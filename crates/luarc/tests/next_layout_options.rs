//! Constructor hints belong to the definition module, including across imports.
use luarc::ast::StatKind;
use luarc::check::{Checker, ModuleUnit};
use luarc::diag::{Diagnostic, SourceMap};
use luarc::native::{adapters::AdapterSet, world::World};
use luarc::parser::parse_module;
use luarc::resolve::{Resolution, Resolver};

fn imported_layout(producer_level: &str, caller_level: &str) -> (Vec<Diagnostic>, (usize, usize)) {
    let producer = format!("--!optimize {producer_level}\nlocal t={{[1]=1,[2]=2,[3]=3}}\nreturn t\n");
    let caller = format!("--!optimize {caller_level}\nlocal t=require(\"./producer\")\nnext(t,4)\n");
    let mut map = SourceMap::default();
    let mut units = Vec::new();
    let mut next_id = 1;
    for (name, source) in [("producer.luarc", producer), ("caller.luarc", caller)] {
        let file = map.add(name.into(), name.into(), source.clone());
        let module = parse_module(file, &source, &mut next_id).expect("parse layout module");
        let pseudo_func = next_id;
        next_id += 1;
        units.push(ModuleUnit { module, pseudo_func, ident: name.into(), requires: Default::default(), rust_requires: Default::default() });
    }
    let StatKind::Local(_, exprs) = &units[0].module.body.stats[0].kind else { panic!("producer constructor") };
    let constructor = exprs[0].id;
    let StatKind::Local(_, exprs) = &units[1].module.body.stats[0].kind else { panic!("import declaration") };
    let require = exprs[0].id;
    units[1].requires.insert(require, 0);
    let mut resolution = Resolution::default();
    let mut resolver = Resolver::new(&mut resolution);
    for unit in &units { resolver.module(&unit.module, unit.pseudo_func); }
    resolver.finish();
    assert!(resolver.errors.is_empty(), "{:?}", resolver.errors);
    let world = World::default();
    let adapters = AdapterSet::default();
    let mut checker = Checker::new(&resolution, &map, &world, &adapters);
    checker.check_program(&units, &[0, 1]);
    (checker.errors, checker.info.table_layouts[&constructor])
}

#[test]
fn imported_tables_retain_the_producers_allocation_mode() {
    for caller in ["0", "1", "2"] {
        for producer in ["0", "1", "2"] {
            let (errors, layout) = imported_layout(producer, caller);
            assert!(errors.is_empty(), "producer {producer}, caller {caller}: {errors:?}");
            assert_eq!(layout, if producer == "0" { (0,3) } else { (3,0) });
        }
    }
}

#[test]
fn unknown_allocation_is_diagnosed_at_the_producer() {
    let (errors, _) = imported_layout("18446744073709551616", "1");
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert_eq!(errors[0].span.file, 0);
    assert!(errors[0].msg.contains("table allocation depends on an unproven Luau optimization directive"));
    assert!(imported_layout("1", "18446744073709551616").0.is_empty());
}
