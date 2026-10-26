# Automated fuzz testing and edge-case discovery
**COPY OF GITHUB #6**

Luarc currently relies heavily on manually written tests, making it easy to miss unusual combinations of otherwise supported language features.

Adding automated fuzz testing could help discover similar compiler bugs before they are encountered by users.

## Proposed approach
* Program mutation: Generate variations of existing working tests by modifying expressions, types, scopes, tables, function calls, and imports.
* Differential testing: Compare behavior against Luau where applicable.
* Compiler validation: Detect crashes, invalid generated Rust, unexpected diagnostics, and runtime inconsistencies.
* Failure minimization: Reduce failing programs to small, reproducible test cases.

## Suggested Impalmentation Plan
Start with a small harness that mutates existing test cases and validates the results. Grammar-aware generation, coverage guidance, and CI integration can be added later if useful. It should first pass an Luau interpter before continuning. 

The goal is to automatically discover edge cases rather than rely entirely on developers anticipating them, without introducing unnecessary complexity into the compiler itself.