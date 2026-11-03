# lean-benzecri — the Lean library of Benzécri, *Sur les variétés localement affines et localement projectives*

The formalization of `papers/benzecri`: J.-P. Benzécri's thesis, Bull. SMF 88 (1960) 229–332
(DOI 10.24033/bsmf.1551), formalized systematically as the home of the (singular) Benzécri /
affine suspension (DEC-112, WP-45). A strict library `Benzecri` and a scaffold library
`BenzecriScaffold`, Lean `v4.31.0`, mathlib `fabf563a` (the hub's pin, `hub.toml`).

    python3 ../tools/dropbox_ignore.py               # once, BEFORE any build: .lake must never sync
    taskset -c 0-11 lake build BenzecriScaffold.<Module>   # one module — the iteration loop
    make check                                       # strict build, scaffold build, sorry count, axiom sweep

The paper is external (DEC-112, as Barbot's is under DEC-34): it is formalized, never rewritten.
Its ledger reads a **transcription** of the Numdam scan, `papers/benzecri/legacy/labeled/
benzecri1960_ch1.tex` — Chapter 1 and the results A, B, C of the introduction, in French, with
labels `bzdef:` `bzprop:` `bzthm:` `bzcor:` `bzlem:` `bzrem:`. The transcription is to be checked
by the author; a reading you doubt is checked against the page image of
`papers/benzecri/sources/bsmf-1960-88-229/benzecri1960.pdf`, never against its OCR text layer.

## Layout (DEC-112)

| layer | imports | status |
|---|---|---|
| the classical core (Chapter 1 first, then Ch. 2–5) | **Mathlib only** | wave 0: skeleton |
| the generalisations: gx's singular (G,X) topological setting, ETT causality, functoriality, the sheaf viewpoints (étalé / sheaf of charts; cone ↔ Proj as a graded structure; locally ringed spaces), the Lorentzian / HS specialisations | `GX.*`, `Causal.*`, through a `[[require]]` of `lean-gx` **git-pinned to a gated commit** (as lean-gx pins Causal) | not started |

Neither `lean-gx` nor `lean-causal` ever imports this package. Until the generalisation layers
start, `lakefile.toml` requires Mathlib alone, and a file of the core that wants a gx notion
(`gxGroupoid`, the developing theorem) builds a minimal local version of it, citing its gx
original; the bridge to gx's version is a later module of the generalisation layer, not an import.

## The two libraries

| library | where | rule |
|---|---|---|
| `Benzecri` | `Benzecri/` | strict: `warningAsError`, so a `sorry`, an unused variable or a deprecation fails the build |
| `BenzecriScaffold` | `scaffold/BenzecriScaffold/` | `sorry` permitted and tagged `SORRY(<label>): <obstruction>`; never imported by `Benzecri`. The campaign writes here (`docs/CAMPAIGN.md`); a file graduates by `git mv` |

## Conventions

- Namespace `Benzecri`. Hypotheses are the weakest the proof uses; a hypothesis the paper omits
  but the proof needs is added and recorded as a finding.
- **S(E) is the sphere of rays** `(E ∖ 0)/ℝ₊*`, Benzécri's *sphère projective*, a double cover of
  ℝPⁿ; it is never Mathlib's `Projectivization` (which is ℝPⁿ = `(E ∖ 0)/ℝ*`, his `P(E)`).
  `S(n)` is the sphere of `ℝⁿ⁺¹` (dimension n). See `kb/0001-conventions.md`.
- A locally projective (resp. affine) manifold is a `ChartedSpace` over the model with
  `HasGroupoid` for the groupoid of local restrictions of `GS(n, ℝ)` (resp. `GA(n, ℝ)`) — the
  (G,X) groupoid; the paper's jets-based Definition 12 is proved equivalent, not taken as the
  definition (plan: `campaign/WP-45-plan/CH1-PLAN.md`).
- The knowledge base of `lean-causal/kb/` applies where it is not about causality (0004 names at
  this pin, 0005 build your own module, 0006 docstring contract, 0011 never outrun the paper, 0015
  graduation checklist, 0018 charts and maximal atlases); benzecri-specific entries are in `kb/`.

## Modules

None yet (wave 0: the package root and placeholders `Benzecri.Basic`, `BenzecriScaffold.Basic`).
The proposed Chapter 1 split, sizes and dependency order are in `campaign/WP-45-plan/CH1-PLAN.md`.
