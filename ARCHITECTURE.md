# The target architecture of the hub's Lean (planned; the move is not yet made)

The author's design of 2026-11-23 (DEC-211). It replaces the historical split, where
lean-causal holds ETT plus Barbot's flat geometry plus copies of gx, lean-gx holds the general
theory plus Lorentzian BTZ geometry, and Benzécri copies gx's groupoid. **Nothing has moved yet.**
This file is the plan. The move happens in one window that stops every loop (§5), once its
prerequisites (§4) exist.

## 1. The packages and their dependencies

Seven theory packages, each a Lake package of its own, git-pinned to the packages it depends on.
Sub-packages are separate libraries inside a package, and they keep the same dependency discipline.

```
mathlib ──► ETT ───────────────┬─────────────────────────┐
   │                            │                          │
   ├──────► GX ──► AffineGX ────┼──► Lorentzian ◄──────────┤
   │                │   │       │      │  └─ Lorentzian.D21 (2+1) ◄── BBS.D21 (2+1 particle classification)
   │                │   └─ Riemannian (Bieberbach)                     ▲
   │                └──────────────────────────────────────► BBS ─────┘  (AffineGX + ETT)
   └──────► Wave (functional analysis + ETT) ──┐
                                                ▼
                         Einstein-like (ETT global properties instantiated) ◄── Lorentzian
```

| Package | Depends on | Content |
|---|---|---|
| **ETT** (root) | mathlib | topological causality: the ladder, CBG over abstract geometries, abstract maximal developments, nested causalities, the layer-1 theorems of the programme. Pure causal-topological: no model, no metric. |
| **GX** (root) | mathlib | the general singular (G,X) theory: portly sets, a.e. atlases, spreads, Fox completion, branched coverings and Galois, the developing theorems, tameness, general suspensions. No causality. |
| **Wave** | mathlib, ETT | functional analysis + ETT: local theory of non-linear wave equations (Ringström, Sbierski, Le Floch, ERS's quasilinear layer 3). Smooth Lorentzian manifolds (DEC-147) live here. |
| **AffineGX** | GX | the singular extension of Benzécri: affine, projective and radiant (G,X) models, cones, suspensions over them. Benzécri is its regular case. **Sub-package `Riemannian`**: Bieberbach. |
| **Lorentzian** | ETT, AffineGX | the Lorentzian special case, flat spacetimes and their uniformization theorems: Barbot, Mess, Bonsante, Benedetti, Seppi, Brunswic (BTZ, Alexandrov), Tholozan. **Sub-package `D21`** (2+1): the singular models E_α, E₀; it depends on BBS.D21. |
| **BBS** | AffineGX, ETT | Barbot–Bonsante–Schlenker and the 3+1 programme. **Sub-package `D21`**: the 2+1 particle classification (links, HS-surfaces), which Lorentzian.D21 depends on. |
| **Einstein** | ETT, Wave, Lorentzian | ETT's global properties instantiated for Einstein-like equations and for geometric spacetimes: CBG for vacuum Einstein (Sbierski), ERS, inextendibility (the Sbierski binders' instances). |

**Dependency hazard.** Lorentzian.D21 depends on BBS.D21, and BBS depends on AffineGX and ETT but
not on Lorentzian. The package graph stays acyclic only if BBS.D21 never imports Lorentzian. The
import gate (§4) enforces this.

**Orbiting packages.** These are examples that live where our theories meet theories we do not
cover. Their dependencies are not fully traced, and they rest on foundations outside the hub. They
sit outside the seven-package graph, and the theory packages import them as **named external
inputs**, each one a localisation the theory needs but does not own:

| Orbiting package | Content (today in `Causal/Flat`) |
|---|---|
| `orbit-discrete-groups` | Selberg's lemma; Auslander–Carrière–Dal'bo; Fried–Goldman–Hirsch (Fitting, H¹ vanishing); Gromov's classification on ℍᵈ; the Tits branch |

Bieberbach is self-contained and goes to `AffineGX.Riemannian`, not to an orbit. Other orbiting
packages are named as they appear, for example spectral gaps for EGF.

**Outside the theory:** GFN (`lean/`), EGF, Syracuse and Yamabe stay as they are.

## 2. Where today's code goes (measured 2026-11-23)

| Today | Lines | Goes to |
|---|---:|---|
| `lean-causal/Causal/*` (core), `CBG/`, `Ladder/` | 58k + 14k + 4k | **ETT** |
| `lean-causal/Causal/Model/Quasilinear*`, the planned Lorentzian package (DEC-147) | part of 8k | **Wave** |
| `lean-causal/Causal/Model/{Cone,Massive,EAlphaCauchy,…}`, `SingularFlat`'s models | rest of 8k | **Lorentzian.D21** (the abstract `SingularFlatAxioms` stay in ETT, DEC-197) |
| `lean-causal/Causal/Flat/*` (Barbot), group theory excluded | ~74k | **Lorentzian** |
| `Causal/Flat/{Selberg*,ACD*,AffACD*,MaxUnip*,AffUnip*,Gromov*,TitsNull}` | ~9k | **orbit-discrete-groups** |
| `Causal/Flat/Bieberbach*` | ~2k | **AffineGX.Riemannian** |
| `lean-causal/Causal/Port/*` | 16k | **deleted**: its gx copies are replaced by imports of GX and AffineGX |
| `lean-gx/GX/{Topology,Structure,Spread,Singular,Branched,SingularII}`, general `Suspension` | ~66k | **GX** |
| `lean-gx/GX/Hyperbolic`, `Suspension/Affine`, `Suspension/{Conic,Celestial}`'s affine models | ~6k | **AffineGX** |
| `lean-gx/GX/{BTZ,Lorentz}` | 56k | **Lorentzian** (BTZ models to `D21`) |
| `lean-gx/GX/BBS` | 11k | **BBS** (the HS link classification to `D21`) |
| `lean-benzecri/*` | 35k | **AffineGX** (its copied `gxGroupoid`, `IsGXMorphism` and universal cover become imports of GX) |
| planned `lean-alexandrov` (DEC-209) | — | **Lorentzian** (radiant spacetimes), not a package of its own |

Papers then span packages. Their ledgers need several Lean roots:
- ETT: ETT, plus Lorentzian.D21 for §3–4;
- gx: GX, plus Lorentzian for §4;
- Barbot: Lorentzian, plus the orbit;
- BBS: BBS, plus BBS.D21.

## 3. What the move gains

- **Fewer copies.** `Causal/Port` (16k lines of copied gx) and Benzécri's copied groupoid both
  disappear.
- **"Benzécri is the regular case of gx" becomes a matter of definitions.** AffineGX imports GX
  instead of duplicating it.
- **ETT is the pure causal root** the programme's layer-1 rule asks for, and GX is the pure
  structural root.
- **The four-layer framing becomes the package graph.** Global causal arguments sit in ETT, and the
  localisations come from geometry (Lorentzian), from PDE (Wave), or from orbits.

## 4. Prerequisites: tooling to build before the window

1. **Multi-root ledgers.** `tools/ledger.py` and `ledger.toml` must take several Lean roots per
   paper (§2), and `tools/doubledag.py` and the atlas overlay must follow.
2. **A mechanical rename tool.** It takes a map `old module/namespace → new` and rewrites Lean
   sources, imports, every `curation.toml`, binder, ladder witness, roadmap evidence, kb entry and
   atlas overlay. It also checks that each name still resolves.
3. **A pin-bump tool for seven git-pinned packages.** It bumps a package's pin in every dependent
   and rebuilds in dependency order. This fixes the "ledger predates a pinned commit" failures seen
   in the journals.
4. **An import-graph gate.** A package or sub-package may import only what §1 allows, orbits only
   as declared external inputs, and the graph must be acyclic. It needs a fixture under
   `tools/fixtures/`, as every gate does.
5. **Leases per package and sub-package directory** in `tools/lease.py` and both loop skills.

## 5. The migration window

The trigger is the author's go-ahead, once §4 exists and ETT's gluing refactor (DEC-167) has
landed, since that refactor rewrites the same ETT core.

1. Stop `/atlas-team`, `/ett-programme` and `/egf-programme` (their leases dropped). Open a branch.
2. Create the seven packages and the orbit, and move files with `git mv` (history kept), in
   dependency order: ETT, GX, orbit, AffineGX, BBS.D21, Lorentzian, Wave, Einstein, BBS.
3. Run the rename tool. Delete `Port/` and Benzécri's copies, replacing them with imports. Build
   each package (`make check`) in order.
4. Switch the ledgers to multi-root and rebuild them. Every paper's closure must be unchanged; any
   change is a regression, explained or reverted. Then the atlas, the ladder, the binders and the
   hub `make check`.
5. Merge and push. Re-arm the loops with the new package map (`PACKAGE_OF`, leases, skills).

## 6. Open questions for the author

- **Names.** The packages are `ETT`, `GX`, `Wave`, `AffineGX`, `Lorentzian`, `Einstein`, `BBS`.
  Lean namespaces would become `ETT.*` (today `Causal.*`), `GX.*`, … Rename `Causal` to `ETT`?
- **Where smooth Lorentzian manifolds live.** Wave (the PDE side), or a sub-package of Lorentzian
  that Wave also imports? Wave and Lorentzian are otherwise independent.
- **Sub-package or own package.** Do `Lorentzian.D21` and `BBS.D21` stay sub-packages (libraries
  inside their package), or become packages of their own, given the cross-dependency between them?
- **Further orbits.** Beyond discrete groups: Troyanov's cone metrics (gx), the spectral gaps (EGF),
  and the PDE facts named as hypotheses in ERS (Sogge, O'Neill)?
