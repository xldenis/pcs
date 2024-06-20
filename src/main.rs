#![feature(rustc_private)]

use std::{cell::RefCell, rc::Rc};

use pcs::{prusti_rustc_interface, run_free_pcs};
use prusti_rustc_interface::{
    borrowck::consumers::{self, BodyWithBorrowckFacts},
    data_structures::fx::FxHashMap,
    data_structures::steal::Steal,
    driver::{self, Compilation},
    hir::{self, def::DefKind, def_id::LocalDefId},
    index::IndexVec,
    interface::{interface::Compiler, Config, Queries},
    middle::{
        mir,
        query::{queries::mir_borrowck::ProvidedValue as MirBorrowck, ExternProviders, Providers},
        ty::TyCtxt,
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
        let body: BodyWithBorrowckFacts<'static> = std::mem::transmute(body_with_facts);
        BODIES.with(|state| {
            let mut map = state.borrow_mut();
            assert!(map.insert(def_id, body).is_none());
        });
    }
    let mut providers = Providers::default();
    prusti_rustc_interface::borrowck::provide(&mut providers);
    let original_mir_borrowck = providers.mir_borrowck;
    original_mir_borrowck(tcx, def_id)
}

fn do_stuff<'tcx>(tcx: TyCtxt<'tcx>) {
    let mut item_names = vec![];
    let dir_path = "visualization/data";
    if std::path::Path::new(dir_path).exists() {
        std::fs::remove_dir_all(dir_path).expect("Failed to delete directory contents");
    }
    std::fs::create_dir_all(dir_path).expect("Failed to create directory for JSON file");

    for def_id in tcx.hir().body_owners() {
        let kind = tcx.def_kind(def_id);
        match kind {
            hir::def::DefKind::Fn | hir::def::DefKind::AssocFn => {
                let body = BODIES.with(|state| {
                    let mut map = state.borrow_mut();
                    unsafe { std::mem::transmute(map.remove(&def_id).unwrap()) }
                });
                run_free_pcs(&body, tcx, &dir_path);
                item_names.push(format!("{}", tcx.item_name(body.body.source.def_id())));
            }
            unsupported_item_kind => {
                eprintln!("unsupported item: {unsupported_item_kind:?}");
            }
        }
    }

    use std::{fs::File, io::Write};

    let file_path = format!("{}/functions.json", dir_path);

    let json_data =
        serde_json::to_string(&item_names).expect("Failed to serialize item names to JSON");
    let mut file = File::create(file_path).expect("Failed to create JSON file");
    file.write_all(json_data.as_bytes())
        .expect("Failed to write item names to JSON file");
}

impl driver::Callbacks for PcsCallbacks {
    fn config(&mut self, config: &mut Config) {
        assert!(config.override_queries.is_none());
        config.override_queries = Some(
            |_session: &Session, providers: &mut Providers, _external: &mut ExternProviders| {
                providers.mir_borrowck = mir_borrowck;
            },
        );
    }
    fn after_analysis<'tcx>(
        &mut self,
        compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        queries.global_ctxt().unwrap().enter(do_stuff);
        Compilation::Stop
    }
}

fn main() {
    let mut rustc_args = vec!["-Zpolonius=yes".to_string()];
    rustc_args.extend(std::env::args().skip(1));
    let mut callbacks = PcsCallbacks;
    driver::RunCompiler::new(&rustc_args, &mut callbacks).run();
}
