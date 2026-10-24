# Approved step 2 source-test migrations

Each program below is preserved verbatim apart from its obsolete `expect-error`
comment. The module entry uses `.luau` for the pinned oracle require context.
All 26 oracle runs exited 0. `clone_plain` printed `1\t2\n`, `loaded_write`
printed `1\n`; every other program printed nothing. The source harness executes
each fixture in debug and release and rejects generated-code warnings.

| Original compile-fail source | Positive fixture |
|---|---|
| `tests/compile_fail/metatables_anonymous.luarc` | `tests/metatables_step2_source/metatables_anonymous.luarc` |
| `tests/compile_fail/metatables_nonself_index.luarc` | `tests/metatables_step2_source/metatables_nonself_index.luarc` |
| `tests/compile_fail/metatables_class_argument.luarc` | `tests/metatables_step2_source/metatables_class_argument.luarc` |
| `tests/compile_fail/metatables_class_expression.luarc` | `tests/metatables_step2_source/metatables_class_expression.luarc` |
| `tests/compile_fail/metatables_class_parameter.luarc` | `tests/metatables_step2_source/metatables_class_parameter.luarc` |
| `tests/compile_fail/metatables_class_reassigned.luarc` | `tests/metatables_step2_source/metatables_class_reassigned.luarc` |
| `tests/compile_fail/metatables_class_shadow.luarc` | `tests/metatables_step2_source/metatables_class_shadow.luarc` |
| `tests/compile_fail/metatables_chain.luarc` | `tests/metatables_step2_source/metatables_chain.luarc` |
| `tests/compile_fail/metatables_late_chain.luarc` | `tests/metatables_step2_source/metatables_late_chain.luarc` |
| `tests/compile_fail/metatables_clone.luarc` | `tests/metatables_step2_source/metatables_clone.luarc` |
| `tests/compile_fail/metatables_clone_plain.luarc` | `tests/metatables_step2_source/metatables_clone_plain.luarc` |
| `tests/compile_fail/metatables_clone_promotion.luarc` | `tests/metatables_step2_source/metatables_clone_promotion.luarc` |
| `tests/compile_fail/metatables_index_alias.luarc` | `tests/metatables_step2_source/metatables_index_alias.luarc` |
| `tests/compile_fail/metatables_index_block.luarc` | `tests/metatables_step2_source/metatables_index_block.luarc` |
| `tests/compile_fail/metatables_index_bracket.luarc` | `tests/metatables_step2_source/metatables_index_bracket.luarc` |
| `tests/compile_fail/metatables_index_conditional.luarc` | `tests/metatables_step2_source/metatables_index_conditional.luarc` |
| `tests/compile_fail/metatables_index_constructor.luarc` | `tests/metatables_step2_source/metatables_index_constructor.luarc` |
| `tests/compile_fail/metatables_index_early.luarc` | `tests/metatables_step2_source/metatables_index_early.luarc` |
| `tests/compile_fail/metatables_index_embedded.luarc` | `tests/metatables_step2_source/metatables_index_embedded.luarc` |
| `tests/compile_fail/metatables_index_initialization.luarc` | `tests/metatables_step2_source/metatables_index_initialization.luarc` |
| `tests/compile_fail/metatables_index_keyed_constructor.luarc` | `tests/metatables_step2_source/metatables_index_keyed_constructor.luarc` |
| `tests/compile_fail/metatables_index_nested_early.luarc` | `tests/metatables_step2_source/metatables_index_nested_early.luarc` |
| `tests/compile_fail/metatables_index_parallel.luarc` | `tests/metatables_step2_source/metatables_index_parallel.luarc` |
| `tests/compile_fail/metatables_index_replacement.luarc` | `tests/metatables_step2_source/metatables_index_replacement.luarc` |
| `tests/compile_fail/metatables_index_unused.luarc` | `tests/metatables_step2_source/metatables_index_unused.luarc` |
| `tests/compile_fail/metatables_loaded_write.luarc` | `tests/metatables_step2_source/metatables_loaded_write.luau` |
