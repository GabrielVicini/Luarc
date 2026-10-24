//! Definition-file optimizer options must survive imports and function aliases.

use luarc::ast::StatKind;
use luarc::check::{Checker, ModuleUnit};
use luarc::diag::{Diagnostic, SourceMap};
use luarc::native::{adapters::AdapterSet, world::World};
use luarc::parser::parse_module;
use luarc::resolve::{Resolution, Resolver};

fn imported_function_errors(producer_level: u8, caller_level: u8) -> Vec<Diagnostic> {
    let producer = format!("--!optimize {producer_level}\nlocal function run()\n local t={{[\"key\"]=1}}\n local key=\"k\"..\"ey\"\n local alias=key\n next(t,alias)\nend\nreturn run\n");
    let caller = format!("--!optimize {caller_level}\nlocal imported=require(\"./producer\")\nlocal alias=imported\nalias()\n");
    let mut sm = SourceMap::default();
    let mut units = Vec::new();
    let mut next_id = 1;
    for (name, source) in [("producer.luarc", producer), ("caller.luarc", caller)] {
        let file = sm.add(name.into(), name.into(), source.clone());
        let module = parse_module(file, &source, &mut next_id).expect("parse module");
        let pseudo_func = next_id;
        next_id += 1;
        units.push(ModuleUnit { module, pseudo_func, ident: name.into(), requires: Default::default(), rust_requires: Default::default() });
    }
    let StatKind::Local(_, exprs) = &units[1].module.body.stats[0].kind else { panic!("import declaration") };
    let require_id = exprs[0].id;
    units[1].requires.insert(require_id, 0);
    let mut resolution = Resolution::default();
    let mut resolver = Resolver::new(&mut resolution);
    for unit in &units { resolver.module(&unit.module, unit.pseudo_func); }
    resolver.finish();
    assert!(resolver.errors.is_empty(), "{:?}", resolver.errors);
    let world = World::default();
    let adapters = AdapterSet::default();
    let mut checker = Checker::new(&resolution, &sm, &world, &adapters);
    checker.check_program(&units, &[0, 1]);
    checker.errors
}

#[test]
fn imported_aliases_keep_the_producer_files_constant_identity_proof() {
    let errors = imported_function_errors(0, 1);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert_eq!(errors[0].span.file, 0);
    assert!(errors[0].msg.contains("next continuation key has GC-sensitive identity"), "{errors:?}");
    assert!(imported_function_errors(1, 0).is_empty());
    assert!(imported_function_errors(2, 0).is_empty());
}
