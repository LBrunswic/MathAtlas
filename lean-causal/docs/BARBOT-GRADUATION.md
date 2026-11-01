# Barbot graduation plan (2026-11-01; read-only planner, kb/0015)

Execute ONLY when no workflow is writing or importing `scaffold/CausalScaffold/Flat/*`, `Port/*`,
`Splitting`, `CurvesExtend`, `CompactCauchy` (all agents use those module paths).

## Findings
- **The axiom sweep has never seen a Barbot module**: `scaffold/CausalScaffold.lean` imports only
  the 5 ETT modules. Graduation (imports in `Causal.lean`) and adding the 5 remaining Barbot
  scaffold modules to `CausalScaffold.lean` fix it (kb/0025 to write).
- No declaration name is defined twice across the 73 built `.ilean` (checked).
- `set_option backward.isDefEq.respectTransparency false in` at `Splitting.lean:1214` would be the
  strict library's first `set_option` — disclose in Splitting's SCOPE.
- Only marks: Penrose's 5 b-labels, CauchyComplete's `bprop:project`, `bcor:quoiso`.

## Graduable set (25, dependency order), `CausalScaffold.X` → `Causal.X`
0: Flat.Form, Flat.Bieberbach, Port.UniversalCover, Port.GXBasic, CurvesExtend, CompactCauchy
(proved part: delete the bare lemma K, l.791–805, into a scaffold stub of the same module name
importing `Causal.CompactCauchy`) · 1: Flat.{Isometries, Penrose, IsomCausal, Achronal,
InducedLength}, Port.Developing · 2: Flat.{AchronalDomains, FlatSpacetime, Cosmological,
Developing}, Splitting · 3: Flat.{Externals, Quotient, LipschitzGraph} · 4: Flat.{SecondCountable,
Examples, Develop} · 5: Flat.{TwistedProduct, CauchyComplete}.
Stay in the scaffold: Flat.{Nonloxodromic, Loxodromic, TitsNull, Classification}, the CompactCauchy
stub, and any Flat/Lox/*, Flat/Nonlox/* lemma files still carrying sorries (re-census first).

## Steps (bash, not zsh; nothing else running Lake)
0. Commit the in-flight round (CauchyComplete, SecondCountable, TitsNull, …) after its audits; build.
1. `git mv` each file to `Causal/Flat/`, `Causal/Port/`, `Causal/`; rewrite imports and prose with
   word-bounded sed (`\bCausalScaffold\.Flat\.$m\b` → `Causal.Flat.$m`; `\b` keeps Develop ≠
   Developing, Achronal ≠ AchronalDomains) over `Causal/**`, `scaffold/CausalScaffold/Flat/*.lean`,
   `docs/BARBOT.md`, `../papers/barbot/certificate/curation.toml` (extra_lean_files paths); delete stale oleans `.lake/build/lib/lean/CausalScaffold/{Flat,Port}/<m>.*`;
   assert `! grep -rn '^import CausalScaffold' Causal/ Causal.lean`.
2. Write the CompactCauchy stub (header + l.791–804 from HEAD + `end Causality` / `end Causal`, with
   `variable {C : Causality M}`); fix the strict CompactCauchy docstring (l.44–46, 76–81, 92–94).
3. Root files: append the 25 imports to `Causal.lean` after `import Causal.Model.Massive`; append
   `CompactCauchy, Flat.Nonloxodromic, Flat.Loxodromic, Flat.TitsNull, Flat.Classification` (+ Lox/,
   Nonlox/ files) to `scaffold/CausalScaffold.lean`; README module table; BARBOT.md line.
4. Verify: `taskset -c 0-11 make -C lean-causal check` (strict 0 sorry; sweep clean); ledgers:
   `tools/ledger.py -c papers/barbot/ledger/ledger.toml build && … check`, ETT ledger rebuild must
   change only its git stamp; `tools/papers_check.py`. Commit by pathspec (never lean-gx).
5. Message gx: module renames only (no declaration renamed, no signature changed); list of modules
   still in the scaffold; `secondCountableTopology` is a new global instance; never
   `open Causal GX`.

## Deferred cleanups
minkB/minkQ helper triplication (Isometries public / Penrose, Cosmological private) → consolidate
into Form later; `IsLocalIsometry` ↔ `Port.GXBasic.IsGXMorphism` bridge file; generic Causality
lemmas living in Flat files (IsomCausal `eq_of_agree_on_basis`, Achronal `IsAchronal`, Cosmological
extension lemmas, SecondCountable's general lemmas) → ETT backlog; InducedLength's `hG` on `.smul`
(gx API: announce before dropping). Do now (docstring only): stale "not graduated / not
ClosedUnderRestriction" prose in FlatSpacetime, Flat/Developing, CompactCauchy.
