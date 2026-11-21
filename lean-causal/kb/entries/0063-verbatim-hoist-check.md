---
id: 0063
title: Checking a verbatim hoist: dump the environment before and after
kind: pattern
created: 2026-11-21
---
A hoist (moving declarations between modules under the same full names) is checked by dumping
every constant before and after: module, kind, universe levels, `Expr.hash` of type and value,
binder telescope with macro scopes erased, reducibility. If `lake build --no-build` reports the
package up to date with a clean tree, the "before" dump needs no /tmp copy of HEAD. `Expr.hash`
ignores binder names, so hygienic instance names (which encode the module) give no false
difference; a moved constant must differ in its module only (T-abs-hoist-model-free,
T-abs-hoist-cbg-cores).
