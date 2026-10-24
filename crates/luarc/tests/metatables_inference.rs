#[path = "support/metatables.rs"]
mod support;

use luarc::check::{CallKind, Checker};
use luarc::types::{TabId, TyNode};

const CLASS: &str = "local Class = {}\nClass.__index = Class\nfunction Class.new(x) return setmetatable({x = x}, Class) end\nfunction Class:get() return self.x end\n";

fn tab(checker: &Checker<'_>, name: &str) -> TabId {
    let sym = checker.res.syms.iter().position(|s| s.name == name).expect("fixture symbol") as u32;
    match checker.st.node(checker.info.sym_slot[&sym].ty) {
        TyNode::Table(tab) => checker.st.tab_root(*tab),
        other => panic!("expected record for {name}: {other:?}"),
    }
}

#[test]
fn exact_unannotated_class_infers_self_and_constructor_without_merging_class() {
    support::checked(
        &format!("{CLASS}local obj = Class.new(7) print(obj:get(), obj.get(obj))"),
        |checker, _| {
            assert!(checker.errors.is_empty(), "{:?}", checker.errors);
            let class = tab(checker, "Class");
            let instance = tab(checker, "obj");
            assert_ne!(class, instance);
            assert_eq!(tab(checker, "self"), instance);
            assert_eq!(checker.st.tab(instance).parent, Some(class));
            assert!(checker.st.tab(class).parent.is_none());
            assert!(!checker.st.tab(instance).fields.contains_key("get"));
            assert_eq!(checker.info.record_methods.len(), 1);
            assert!(checker.info.calls.values().any(|call| matches!(call, CallKind::RecordParent)));
        },
    );
}

#[test]
fn inherited_method_result_count_comes_from_the_resolved_function() {
    support::checked("local Class = {} Class.__index = Class function Class.new() return setmetatable({x = 7}, Class) end function Class:pair() return self.x, 9 end local obj = Class.new() print(obj:pair()) print(obj.pair(obj))", |checker, _| {
        assert!(checker.errors.is_empty(), "{:?}", checker.errors);
        let class = tab(checker, "Class");
        let slot = checker.st.tab(class).fields["pair"];
        let TyNode::Func(f) = checker.st.node(slot.ty) else { panic!() };
        assert_eq!(checker.st.rets_known(f.rets).expect("known results").len(), 2);
        assert!(checker.info.record_methods.values().all(|v| matches!(checker.st.node(v.ty), TyNode::Func(_))));
    });
}

#[test]
fn inherited_receivers_share_plain_parameter_roots_and_live_method_replacement_types() {
    support::checked(&format!("{CLASS}local obj = Class.new(7) local function read(t) return t.x end local plain = {{x = 9}} local isolated = {{x = 11}} print(read(obj), read(plain), obj:get()) Class.get = function(self) return self.x + 1 end print(obj:get())"), |checker, _| {
        assert!(checker.errors.is_empty(), "{:?}", checker.errors);
        assert_eq!(tab(checker, "obj"), tab(checker, "plain"));
        assert_eq!(tab(checker, "obj"), tab(checker, "t"));
        assert_ne!(tab(checker, "obj"), tab(checker, "isolated"));
        assert_ne!(tab(checker, "obj"), tab(checker, "Class"));
    });
}

#[test]
fn class_alias_method_storage_does_not_bind_its_receiver_to_the_class() {
    support::checked("local Class = {} Class.__index = Class local Alias = Class function Class.new(x) return setmetatable({x = x}, Class) end function Alias:get() return self.x end local obj = Class.new(7) print(obj:get())", |checker, _| {
        assert!(checker.errors.is_empty(), "{:?}", checker.errors);
        assert_ne!(tab(checker, "Class"), tab(checker, "self"));
        assert_eq!(tab(checker, "obj"), tab(checker, "self"));
    });
}

#[test]
fn unknown_inherited_result_count_is_diagnosed() {
    for call in ["obj:missing()", "obj.missing(obj)"] {
        support::checked(&format!("{CLASS}local obj = Class.new(7) print({call})"), |checker, _| {
            assert!(
                checker
                    .errors
                    .iter()
                    .any(|e| e.msg == "cannot determine how many values this call returns here; annotate the function's return type"),
                "{:?}",
                checker.errors
            );
        });
    }
}

#[test]
fn incompatible_inherited_receivers_are_diagnosed() {
    support::checked(
        &format!("{CLASS}local obj = Class.new(7) print(obj:get()) local other = {{x = \"text\"}} print(obj.get(other))"),
        |checker, _| {
            assert!(
                checker.errors.iter().any(|e| e.msg.starts_with("type mismatch:")),
                "{:?}",
                checker.errors
            );
        },
    );
}
