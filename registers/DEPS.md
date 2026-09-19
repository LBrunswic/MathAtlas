# Dependencies register

**lake resolves to exactly ONE mathlib and has no version solver.** Two live dependencies pinned
to different mathlib revisions cannot coexist, and mathlib has no stable API. So: a library is a
**live-dep** only if its `lean-toolchain` matches the pin (`hub.toml`); anything off-pin is a
**vendored-slice** under `lean/deps/ports/<name>/` with a provenance header, or is re-grown in
the scaffold. A ported foreign proof enters the strict library only after `lake build` clean,
the axiom sweep and kernel replay in this tree. General results go upstream to mathlib.
(Policy lifted from `~/LeanAI/deps/README.md`, 2026-07-10.) `tools/deps_register.py` fails when
this table and `lean/lakefile.toml` disagree.

Status: `live-dep · vendored-slice · reference · to-survey · rejected`.

| name | upstream | rev | toolchain | license | used by | status |
|---|---|---|---|---|---|---|
| `mathlib` | https://github.com/leanprover-community/mathlib4 | `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` (tag v4.31.0) | v4.31.0 | Apache-2.0 | all | live-dep |
| `SLT` | https://github.com/YuanheZ/lean-stat-learning-theory | `216e578c9576bab6b0abc3ba6c65762536768e96` | v4.31.0 | to record | DynIso (54 of LeanAI/library's files import it) | to-survey |
| `SemicircleLaw` | https://github.com/FredRaj3/SemicircleLaw | port at `~/LeanAI/library` (from v4.24.0) | v4.31.0 (ported) | MIT | DynIso | to-survey |
| `LeanArchitect` | https://github.com/... (ITP 2026, arXiv 2601.22554) | — | v4.32.0-rc1 | — | paper binding (`@[blueprint]` inverted) | reference |
| `verso-blueprint` | Lean FRO | — | v4.34.0 | — | future blueprint | reference |
