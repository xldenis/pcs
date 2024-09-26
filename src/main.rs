#![feature(rustc_private)]

use std::collections::{BTreeMap, BTreeSet};
use std::io::Write;
use std::{cmp::Ordering, fs::File};

use std::cell::RefCell;

use itertools::Itertools;
use mir_state_analysis::visualization::dot_graph::{
    DotEdge, DotGraph, DotLabel, DotNode, EdgeDirection, EdgeOptions,
};
use mir_state_analysis::visualization::dot_graph::{DotStringAttr, DotSubgraph};
use mir_state_analysis::{combined_pcs::BodyWithBorrowckFacts, run_combined_pcs, rustc_interface};
use regex::Regex;
use rustc_interface::{
    borrowck::consumers,
    data_structures::fx::FxHashMap,
    driver::{self, Compilation},
    hir::{self, def_id::LocalDefId},
    interface::{interface::Compiler, Config, Queries},
    middle::{
        mir::{BasicBlock, Location},
        query::{queries::mir_borrowck::ProvidedValue as MirBorrowck, ExternProviders},
        ty::TyCtxt,
        util::Providers,
    },
    session::Session,
};

struct PcsCallbacks;

thread_local! {
    pub static BODIES:
        RefCell<FxHashMap<LocalDefId, BodyWithBorrowckFacts<'static>>> =
        RefCell::new(FxHashMap::default());
}

fn mir_borrowck<'tcx>(tcx: TyCtxt<'tcx>, def_id: LocalDefId) -> MirBorrowck<'tcx> {
    let consumer_opts = consumers::ConsumerOptions::PoloniusOutputFacts;
    let body_with_facts = consumers::get_body_with_borrowck_facts(tcx, def_id, consumer_opts);
    unsafe {
        let body: BodyWithBorrowckFacts<'tcx> = body_with_facts.into();
        let body: BodyWithBorrowckFacts<'static> = std::mem::transmute(body);
        BODIES.with(|state| {
            let mut map = state.borrow_mut();
            assert!(map.insert(def_id, body).is_none());
        });
    }
    let mut providers = Providers::default();
    rustc_interface::borrowck::provide(&mut providers);
    let original_mir_borrowck = providers.mir_borrowck;
    original_mir_borrowck(tcx, def_id)
}

fn run_pcs_on_all_fns<'tcx>(tcx: TyCtxt<'tcx>) {
    let mut item_names = vec![];

    let vis_dir = if std::env::var("PCS_VISUALIZATION").unwrap_or_default() == "true" {
        Some("visualization/data")
    } else {
        None
    };

    if let Some(path) = &vis_dir {
        if std::path::Path::new(path).exists() {
            std::fs::remove_dir_all(path)
                .expect("Failed to delete visualization directory contents");
        }
        std::fs::create_dir_all(path).expect("Failed to create visualization directory");
    }

    for def_id in tcx.hir().body_owners() {
        let kind = tcx.def_kind(def_id);
        match kind {
            hir::def::DefKind::Fn | hir::def::DefKind::AssocFn => {
                let item_name = format!("{}", tcx.item_name(def_id.to_def_id()));
                let body = BODIES.with(|state| {
                    let mut map = state.borrow_mut();
                    unsafe { std::mem::transmute(map.remove(&def_id).unwrap()) }
                });
                run_combined_pcs(
                    &body,
                    tcx,
                    vis_dir.map(|dir| format!("{}/{}", dir, item_name)),
                );
                item_names.push(item_name);
            }
            unsupported_item_kind => {
                eprintln!("unsupported item: {unsupported_item_kind:?}");
            }
        }
    }

    if let Some(dir_path) = &vis_dir {
        let file_path = format!("{}/functions.json", dir_path);

        let json_data = serde_json::to_string(
            &item_names
                .iter()
                .map(|name| (name.clone(), name.clone()))
                .collect::<std::collections::HashMap<_, _>>(),
        )
        .expect("Failed to serialize item names to JSON");
        let mut file = File::create(file_path).expect("Failed to create JSON file");
        file.write_all(json_data.as_bytes())
            .expect("Failed to write item names to JSON file");
    }
}

fn set_mir_borrowck(_session: &Session, providers: &mut Providers) {
    providers.mir_borrowck = mir_borrowck;
}

impl driver::Callbacks for PcsCallbacks {
    fn config(&mut self, config: &mut Config) {
        assert!(config.override_queries.is_none());
        config.override_queries = Some(set_mir_borrowck);
    }
    fn after_analysis<'tcx>(
        &mut self,
        _compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        queries.global_ctxt().unwrap().enter(run_pcs_on_all_fns);
        Compilation::Stop
    }
}



fn main() {
    let mut rustc_args = vec![
        "--cfg=prusti".to_string(),
        "--edition=2018".to_string(),
        "-Zpolonius=next".to_string(),
        "-L".to_string(),
        "dependency=../prusti-dev/target/verify/debug/deps".to_string(),
    ];
    rustc_args.push("-Zcrate-attr=feature(register_tool)".to_owned());
    rustc_args.push("-Zcrate-attr=register_tool(prusti)".to_owned());
    rustc_args.push("-Zcrate-attr=feature(stmt_expr_attributes)".to_owned());

    rustc_args.extend(std::env::args().skip(1));
    let mut callbacks = PcsCallbacks;
    driver::RunCompiler::new(&rustc_args, &mut callbacks)
        .run()
        .unwrap();
}
