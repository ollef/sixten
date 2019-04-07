# Changelog

## 2019

### April
- Added rudimentary support for reporting errors through the language server.
- Improved parse error recovery around top-level definitions.
- Made the language server use incremental compilation, reusing compilation results between changes when it can.
- Made the language server type check on every change, instead of on every save.

### March
- Added pattern exhaustiveness and redundancy checks.
- Added support for forced patterns (sometimes called dot patterns) (#137).
- Started printing spans instead of just the start position of error locations.
- Added support for boxed types (#138).
- Started doing inlining of simple definitions during simplification.
- Improved the generated case trees when pattern matching on literals.
- Started reporting errors on the fly instead of at the end of type checking.

### February
- Added preliminary support for inductive families (#133).
- Refactored the compiler to use explicit contexts and to properly elaborate pattern matching during type checking (#132).
- Added file watching functionality (#129 by Varun Gandhi).

### January
- Implemented type hovering (#128 based on code by Dan Rosén).

## 2018

### December
- Implemented a query-based compiler architecture (#119).
