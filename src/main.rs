#![feature(rustc_private)]

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};
use std::{cell::RefCell, rc::Rc};

use itertools::Itertools;
use pcs::visualization::dot_graph::{
    DotEdge, DotGraph, DotLabel, DotNode, DotSubgraph, EdgeOptions,
};
use pcs::{combined_pcs::BodyWithBorrowckFacts, run_free_pcs, rustc_interface};
use regex::Regex;
use rustc_interface::{
    borrowck::consumers,
    data_structures::fx::FxHashMap,
    data_structures::steal::Steal,
    driver::{self, Compilation},
    hir::{self, def::DefKind, def_id::LocalDefId},
    index::IndexVec,
    interface::{interface::Compiler, Config, Queries},
    middle::{
        mir::{BasicBlock, Location},
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
    let dir_path = "visualization/data";
    if std::path::Path::new(dir_path).exists() {
        std::fs::remove_dir_all(dir_path).expect("Failed to delete directory contents");
    }
    std::fs::create_dir_all(dir_path).expect("Failed to create directory for JSON file");

    for def_id in tcx.hir().body_owners() {
        let kind = tcx.def_kind(def_id);
        match kind {
            hir::def::DefKind::Fn | hir::def::DefKind::AssocFn => {
                let item_name = format!("{}", tcx.item_name(def_id.to_def_id()));
                let body = BODIES.with(|state| {
                    let mut map = state.borrow_mut();
                    unsafe { std::mem::transmute(map.remove(&def_id).unwrap()) }
                });
                run_free_pcs(&body, tcx, Some(format!("{}/{}", dir_path, item_name)));
                item_names.push(item_name);
            }
            unsupported_item_kind => {
                eprintln!("unsupported item: {unsupported_item_kind:?}");
            }
        }
    }

    use std::{fs::File, io::Write};

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
        queries.global_ctxt().unwrap().enter(run_pcs_on_all_fns);
        Compilation::Stop
    }
}

#[derive(Debug, Eq, PartialEq, Clone)]
enum RichLocation {
    Mid(Location),
    Start(Location),
}

impl Ord for RichLocation {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match self.location().cmp(&other.location()) {
            Ordering::Equal => match (self, other) {
                (RichLocation::Mid(_), RichLocation::Start(_)) => Ordering::Greater,
                (RichLocation::Start(_), RichLocation::Mid(_)) => Ordering::Less,
                _ => Ordering::Equal,
            },
            ord => ord,
        }
    }
}

impl PartialOrd for RichLocation {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl RichLocation {
    fn location(&self) -> Location {
        match self {
            RichLocation::Mid(loc) => *loc,
            RichLocation::Start(loc) => *loc,
        }
    }
    fn block(&self) -> BasicBlock {
        match self {
            RichLocation::Mid(loc) => loc.block,
            RichLocation::Start(loc) => loc.block,
        }
    }
}

type Borrow = String;
type Region = String;

#[derive(Debug)]
enum PoloniusFact {
    OriginContainsLoanAt(RichLocation, Region, Borrow),
}

fn parse_location(input: String) -> Location {
    let re = Regex::new(r#"bb([^\[]+)\[([^\]]+)\]"#).unwrap();

    if let Some(captures) = re.captures(&input) {
        let block = *(&captures[1].parse::<usize>().unwrap());
        let statement_index = *(&captures[2].parse::<usize>().unwrap());
        Location {
            block: BasicBlock::from_usize(block),
            statement_index,
        }
    } else {
        unreachable!()
    }
}

fn parse_rich_location(string: String) -> RichLocation {
    let re = Regex::new(r#"(Mid|Start)\(([^)]+)\)"#).unwrap();
    let captures = re.captures(&string).unwrap();
    let location = parse_location(captures[2].to_string());
    match &captures[1] {
        "Mid" => RichLocation::Mid(location),
        "Start" => RichLocation::Start(location),
        _ => unreachable!(),
    }
}

fn unquote(input: &str) -> &str {
    &input[1..input.len() - 1]
}

fn parse_polonius_line(line: &str) -> Option<PoloniusFact> {
    let parts: Vec<&str> = line.split_whitespace().collect();

    match parts[0] {
        "origin_contains_loan_at" => {
            let location = parse_rich_location(unquote(parts[1]).to_string());
            let region = unquote(parts[2]).to_string();
            let borrow = unquote(parts[3]).to_string();
            Some(PoloniusFact::OriginContainsLoanAt(location, region, borrow))
        }
        _ => None,
    }
}

#[derive(Debug)]
struct SubsetBaseFact {
    subset: Region,
    superset: Region,
    location: RichLocation,
}

fn parse_subset_base_fact(line: &str) -> SubsetBaseFact {
    let parts: Vec<&str> = line.split_whitespace().collect();
    let subset = unquote(parts[0]).to_string();
    let superset = unquote(parts[1]).to_string();
    let location = parse_rich_location(unquote(parts[2]).to_string());
    SubsetBaseFact {
        subset,
        superset,
        location,
    }
}

fn main() {
    let mut rustc_args = vec!["-Zpolonius=yes".to_string()];
    rustc_args.extend(std::env::args().skip(1));
    let mut callbacks = PcsCallbacks;
    driver::RunCompiler::new(&rustc_args, &mut callbacks).run();
}
