//! Static checking for general record metadata.

use luarc::check::{Checker, ModuleUnit};
use luarc::diag::{SourceMap, Span};
use luarc::native::{adapters::AdapterSet, world::World};
use luarc::parser::parse_module;
use luarc::resolve::{Resolution, Resolver};
use luarc::types::{Slot, Soft, TKind, TabId, TyNode};

fn checked(src: &str, test: impl FnOnce(&mut Checker<'_>)) {
    let mut next = 1;
    let module = parse_module(0, src, &mut next).expect("parse general metadata fixture");
    let mut res = Resolution::default();
    let mut resolver = Resolver::new(&mut res);
    resolver.module(&module, next);
    resolver.finish();
    assert!(resolver.errors.is_empty(), "{:?}", resolver.errors);
    let units = vec![ModuleUnit {
        module,
        pseudo_func: next,
        ident: "m0".into(),
        requires: Default::default(),
        rust_requires: Default::default(),
    }];
    let mut sm = SourceMap::default();
    sm.add("step2.luarc".into(), "step2.luarc".into(), src.into());
    let world = World::default();
    let adapters = AdapterSet::default();
    let mut checker = Checker::new(&res, &sm, &world, &adapters);
    checker.prepare_general_record_metatables(&units);
    checker.check_program(&units, &[0]);
    test(&mut checker);
}

fn slot(checker: &Checker<'_>, name: &str) -> Slot {
    let sym = checker
        .res
        .syms
        .iter()
        .position(|s| s.name == name)
        .expect("fixture symbol") as u32;
    checker.info.sym_slot[&sym]
}

fn tab(checker: &Checker<'_>, name: &str) -> TabId {
    match checker.st.node(slot(checker, name).ty) {
        TyNode::Table(tab) => checker.st.tab_root(*tab),
        other => panic!("expected table for {name}: {other:?}"),
    }
}

fn good(checker: &Checker<'_>) {
    assert!(checker.errors.is_empty(), "{:?}", checker.errors);
}
fn error(checker: &Checker<'_>, message: &str) {
    assert!(
        checker.errors.iter().any(|e| e.msg == message),
        "{:?}",
        checker.errors
    );
}

#[test]
fn metadata_and_parent_types_are_separate_from_own_storage() {
    checked("local p = {x = 7} local mt = {__index = p} local child = setmetatable({}, mt) print(child.x)", |c| {
        good(c);
        let child = c.st.tab(tab(c, "child"));
        assert_eq!(child.metatable, Some(tab(c, "mt")));
        assert_eq!(child.parent, Some(tab(c, "p")));
        assert!(!child.fields.contains_key("x"));
        assert!(c.info.record_lookups.values().any(|p| p.levels.len() == 2 && p.may_miss));
    });
}

#[test]
fn raw_index_is_not_inherited_from_a_metatables_parent() {
    checked("local p = {x = 1} local mt = setmetatable({}, {__index = {__index = p}}) local child = setmetatable({}, mt) print(mt.__index, child.x)", |c| {
        good(c);
        assert!(c.st.tab(tab(c, "mt")).parent.is_some());
        assert!(c.st.tab(tab(c, "child")).parent.is_none());
        assert!(!c.st.tab(tab(c, "mt")).fields.contains_key("__index"));
    });
}

#[test]
fn aliases_replacement_nil_and_reattachment_keep_compatible_shapes() {
    checked("local p, q = {x = 1}, {x = 2} local mt = {__index = p} local alias = mt local child = setmetatable({}, mt) alias[\"__index\"] = q alias.__index = nil setmetatable(child, {__index = p}) print(child.x)", |c| {
        good(c);
        assert_eq!(tab(c, "p"), tab(c, "q"));
        assert_eq!(tab(c, "mt"), tab(c, "alias"));
        assert!(c.st.is_null(c.st.tab(tab(c, "mt")).fields["__index"].null));
    });
}

#[test]
fn absent_and_nil_only_raw_index_have_no_parent_and_soft_misses() {
    for src in [
        "local child = setmetatable({}, {}) print(child.x)",
        "local child = setmetatable({}, {__index = nil}) print(child.x)",
        "local child = setmetatable({}, {[\"__index\"] = nil}) print(child.x)",
    ] {
        checked(src, |c| {
            good(c);
            assert!(c.st.tab(tab(c, "child")).parent.is_none());
            assert!(c.st.tab(tab(c, "child")).metatable.is_some());
            assert!(c.info.record_lookups.values().all(|p| p.may_miss));
            assert!(c
                .info
                .expr
                .values()
                .any(|e| c.soft(e.soft) && e.soft != Soft::No));
        });
    }
}

#[test]
fn chains_keep_all_reachable_candidates_and_stop_at_present_own_fields() {
    checked("local p = {x = 7, flag = true} local middle = setmetatable({y = 2}, {__index = p}) local child = setmetatable({flag = false}, {__index = middle}) print(child.x, child.y, child.flag) child.x = nil", |c| {
        good(c);
        assert!(c.info.record_lookups.values().any(|p| p.tab == tab(c, "child") && p.levels.len() == 3));
        assert!(c.info.record_lookups.values().any(|p| p.tab == tab(c, "child") && p.levels.len() == 1 && !p.may_miss));
        assert!(!c.st.tab(tab(c, "child")).fields.contains_key("y"));
    });
}

#[test]
fn general_parent_methods_infer_the_original_instance_receiver() {
    checked("local parent = {} function parent:get() return self.x end local middle = setmetatable({}, {__index = parent}) local child = setmetatable({x = 7}, {__index = middle}) print(child:get(), child.get(child))", |c| {
        good(c);
        assert_ne!(tab(c, "parent"), tab(c, "child"));
        let method = c.st.tab(tab(c, "parent")).fields["get"];
        let TyNode::Func(method) = c.st.node(method.ty) else { panic!("method type") };
        let TyNode::Table(receiver) = c.st.node(method.params[0].ty) else { panic!("receiver type") };
        assert_eq!(c.st.tab_root(*receiver), tab(c, "child"));
    });
}

#[test]
fn ordinary_methods_still_infer_self_from_their_owner() {
    checked("local ordinary = {x = 7} function ordinary:get() return self.x end local child = setmetatable({}, {}) print(ordinary:get(), child.x)", |c| good(c));
}

#[test]
fn clone_and_shared_plain_instances_adopt_metadata_types_without_own_field_flattening() {
    checked("local function read(t): number? return t.x end local p = {x = 7} local child = setmetatable({}, {__index = p}) local plain = {} local copy = table.clone(child) print(read(child), read(plain), read(copy))", |c| {
        good(c);
        assert_eq!(tab(c, "child"), tab(c, "plain"));
        assert_eq!(tab(c, "child"), tab(c, "copy"));
        assert!(c.st.tab(tab(c, "plain")).metatable.is_some());
        assert!(!c.st.tab(tab(c, "plain")).fields.contains_key("x"));
    });
}

#[test]
fn closed_annotations_constrain_own_writes_but_allow_chain_reads() {
    checked(
        "local child: {own: number} = setmetatable({own = 1}, {__index = {x = 7}}) print(child.x)",
        |c| good(c),
    );
    checked(
        "local child: {own: number} = setmetatable({own = 1}, {__index = {x = 7}}) child.x = 9",
        |c| {
            assert!(
                c.errors
                    .iter()
                    .any(|e| e.msg == "field 'x' does not exist on record type {own}"),
                "{:?}",
                c.errors
            );
        },
    );
}

#[test]
fn parent_and_metadata_cycles_are_distinct_from_data_self_references() {
    checked(
        "local C = {} C.__index = C local child = setmetatable({}, C) print(child.x)",
        |c| good(c),
    );
    checked(
        "local a, b = {}, {} setmetatable(a, {__index = b}) setmetatable(b, {__index = a})",
        |c| error(c, "cyclic static record parent types are not supported"),
    );
    checked(
        "local a, b = {}, {} setmetatable(a, b) setmetatable(b, a)",
        |c| error(c, "cyclic static metatable type expansion is not supported"),
    );
}

fn chain(depth: usize) -> String {
    let mut src = "local t0 = {x = 1}\n".to_string();
    for i in 1..=depth {
        src.push_str(&format!(
            "local t{i} = setmetatable({{}}, {{__index = t{}}})\n",
            i - 1
        ));
    }
    src.push_str(&format!("print(t{depth}.x)"));
    src
}

#[test]
fn ninety_nine_parent_links_pass_and_one_hundred_are_diagnosed() {
    checked(&chain(99), |c| good(c));
    checked(&chain(100), |c| {
        error(
            c,
            "static record parent chains must have fewer than 100 links",
        )
    });
}

#[test]
fn induced_unions_are_rejected_before_any_table_links_change() {
    checked("local p = {} local child = setmetatable({}, {__index = p}) local a, b = {nested = p}, {nested = child}", |c| {
        good(c);
        let before: Vec<_> = c.st.tabs.iter().map(|t| t.link).collect();
        assert!(!c.unify(slot(c, "a").ty, slot(c, "b").ty, Span::default()));
        assert_eq!(before, c.st.tabs.iter().map(|t| t.link).collect::<Vec<_>>());
        error(c, "cyclic static record parent types are not supported");
    });
}

#[test]
fn late_container_or_native_promotion_is_diagnosed_in_all_roles() {
    for role in ["child", "mt", "p"] {
        for kind in [TKind::Array, TKind::Map, TKind::Record] {
            checked(
                "local p = {x = 7} local mt = {__index = p} local child = setmetatable({}, mt)",
                |c| {
                    good(c);
                    let other = c.st.new_tab(kind, Span::default());
                    if kind == TKind::Record {
                        c.st.tab_mut(other).native = Some(luarc::check_native::NativeRec::Tuple(0));
                    }
                    let ty = c.st.ty(TyNode::Table(other));
                    assert!(!c.unify(slot(c, role).ty, ty, Span::default()));
                    error(
                        c,
                        if kind == TKind::Record {
                            "metatables on native-converted records are not supported in this step"
                        } else {
                            "setmetatable does not support arrays or maps"
                        },
                    );
                },
            );
        }
    }
}

#[test]
fn reserved_index_values_are_checked_even_without_attachment() {
    for src in [
        "local mt = {__index = 3}",
        "local mt = {} function mt.__index() end",
        "local mt = {} local function unused(v) mt.__index = v end",
    ] {
        checked(src, |c| {
            error(
                c,
                "setmetatable __index must have a statically known record type",
            )
        });
    }
}

#[test]
fn unannotated_general_constructors_and_inherited_result_tails_are_inferred() {
    checked("local Parent = {} function Parent.new(x) return setmetatable({x = x}, {__index = Parent}) end function Parent:pair(...: number) return self.x, ... end local child = Parent.new(7) print(child:pair(1, 2)) print(child.pair(child, 3, 4)) print(child:pair())", |c| {
        good(c);
        assert_ne!(tab(c, "Parent"), tab(c, "child"));
        let method = c.st.tab(tab(c, "Parent")).fields["pair"];
        let TyNode::Func(method) = c.st.node(method.ty) else { panic!("method type") };
        assert!(c.st.rets_tail(method.rets).is_some());
        assert_eq!(c.info.pack_calls.len(), 3);
    });
}

#[test]
fn late_metadata_cycles_are_rejected_before_induced_storage_unions() {
    checked("local mt = {} local child = setmetatable({}, mt) local a, b = {nested = mt}, {nested = child}", |c| {
        good(c);
        let before: Vec<_> = c.st.tabs.iter().map(|t| t.link).collect();
        assert!(!c.unify(slot(c, "a").ty, slot(c, "b").ty, Span::default()));
        assert_eq!(before, c.st.tabs.iter().map(|t| t.link).collect::<Vec<_>>());
        error(c, "cyclic static metatable type expansion is not supported");
    });
}

#[test]
fn metadata_and_parent_edges_survive_unions_in_both_directions() {
    for reverse in [false, true] {
        checked("local p = {x = 7} local mt = {__index = p} local child = setmetatable({}, mt) local plain = {own = 1}", |c| {
            good(c);
            let (a, b) = if reverse { ("plain", "child") } else { ("child", "plain") };
            assert!(c.unify(slot(c, a).ty, slot(c, b).ty, Span::default()));
            assert_eq!(tab(c, "child"), tab(c, "plain"));
            let plain = c.st.tab(tab(c, "plain"));
            assert_eq!(plain.parent, Some(tab(c, "p")));
            assert_eq!(plain.metatable, Some(tab(c, "mt")));
        });
    }
}

#[test]
fn reachable_incompatible_candidates_and_alias_replacements_are_diagnosed() {
    for src in [
        "local child = setmetatable({x = 1}, {__index = {x = false}}) child.x = nil print(child.x)",
        "local mt = {__index = {x = 1}} local alias = mt local child = setmetatable({}, mt) alias.__index = {x = false} print(child.x)",
    ] {
        checked(src, |c| assert!(c.errors.iter().any(|e| e.msg.starts_with("type mismatch:")), "{:?}", c.errors));
    }
}

#[test]
fn unresolved_general_method_arity_is_diagnosed_without_guessing() {
    checked("local Parent = {} function Parent:forward(f) return f() end local child = setmetatable({}, {__index = Parent}) print(child:forward(function() return 1, 2 end))", |c| {
        assert!(c.errors.iter().any(|e| e.msg.contains("annotate") && (e.msg.contains("values") || e.msg.contains("returns"))), "{:?}", c.errors);
    });
}

#[test]
fn unresolved_index_type_cannot_link_to_a_parent_cycle() {
    checked(
        "local mt = {__index = nil} local child = setmetatable({}, mt)",
        |c| {
            good(c);
            let index = c.st.tab(tab(c, "mt")).fields["__index"];
            let before_types: Vec<_> = (0..c.st.tys.len()).map(|i| c.st.root(i as u32)).collect();
            let before_tables: Vec<_> = c.st.tabs.iter().map(|t| t.link).collect();
            assert!(!c.unify(index.ty, slot(c, "child").ty, Span::default()));
            assert_eq!(
                before_types,
                (0..c.st.tys.len())
                    .map(|i| c.st.root(i as u32))
                    .collect::<Vec<_>>()
            );
            assert_eq!(
                before_tables,
                c.st.tabs.iter().map(|t| t.link).collect::<Vec<_>>()
            );
            error(c, "cyclic static record parent types are not supported");
        },
    );
}
