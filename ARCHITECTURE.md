# The target architecture of the hub's Lean (planned; the move is not yet made)

The author's design of 2026-11-23 (DEC-211, organised in three tiers by DEC-212). It replaces the historical split, where
lean-causal holds ETT plus Barbot's flat geometry plus copies of gx, lean-gx holds the general
theory plus Lorentzian BTZ geometry, and Benzécri copies gx's groupoid. **Nothing has moved yet.**
This file is the plan. The move happens in one window that stops every loop (§5), once its
prerequisites (§4) exist.

## 1. Three tiers: general, local, global

The author's summary (2026-11-23): **general theory, local theories, global theories.** It is
ETT's own factoring applied to the library. The general tier argues globally from properties, the
local tier proves those properties for a model, and the global tier instantiates the general
arguments with the local proofs to obtain classification and uniformization theorems.

| Tier | What it holds | Packages |
|---|---|---|
| **General** | the abstract frameworks: no model, no metric | **ETT** (causality), **GX** (singular (G,X)-structures) |
| **Local** | the models and their local theory: what the localisation properties are proved from | **Wave** (local non-linear wave equations), **AffineGX** (affine, projective, radiant local models; Riemannian sub-package: Bieberbach), **Lorentzian.Local** (flat Lorentzian models; the 2+1 singular models E_α, E₀), **BBS.Local** (the particle classification: links, HS-surfaces; 2+1 and 3+1) |
| **Global** | the general arguments instantiated by the local theories | **Lorentzian** (uniformization: Barbot, Mess, Bonsante, Benedetti, Seppi, Brunswic for BTZ and Alexandrov, Tholozan), **Einstein** (ETT's global properties for Einstein-like equations and geometric spacetimes), **BBS** (collisions, the 3+1 programme) |

**The import rule** is the whole dependency discipline. Imports go down the tiers, never up:
- general imports mathlib only;
- local imports general and other local libraries;
- global imports anything below it.

No global library is imported by a local one, so the cross-dependency that §1 of the first draft
flagged disappears. The 2+1 singular models (Lorentzian.Local) depend on the 2+1 particle
classification (BBS.Local), and both are local.

```
GENERAL   ETT                        GX
           │  ╲                       │
LOCAL      │   Wave       AffineGX ◄──┘ (+ Riemannian)
           │    │           │    │
           │    │   BBS.Local ◄──┤   (2+1 and 3+1 particle classification)
           │    │      ▲         │
           │    │   Lorentzian.Local ◄┘  (E_α, E₀ need BBS.Local's 2+1 part)
           ▼    ▼      ▼
GLOBAL    Einstein ◄ Lorentzian    BBS      (each imports ETT and the local libraries it instantiates)
```

| Package | Tier | Depends on |
|---|---|---|
| **ETT** | general | mathlib |
| **GX** | general | mathlib |
| **Wave** | local | ETT (the properties it localises); smooth Lorentzian manifolds (DEC-147) |
| **AffineGX** | local | GX |
| **BBS.Local** | local | AffineGX, ETT |
| **Lorentzian.Local** | local | AffineGX, ETT, BBS.Local |
| **Lorentzian** | global | Lorentzian.Local, ETT |
| **BBS** | global | BBS.Local, Lorentzian.Local, ETT |
| **Einstein** | global | Wave, Lorentzian, ETT |

Each of Lorentzian and BBS is still **one package**: two libraries, `Local` and the global one.
The DEC-211 count of seven packages stands. The tier is a property of the library, and the import
gate (§4) checks it.

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
| `lean-causal/Causal/Model/{Cone,Massive,EAlphaCauchy,…}`, `SingularFlat`'s models | rest of 8k | **Lorentzian.Local** (the abstract `SingularFlatAxioms` stay in ETT, DEC-197) |
| `lean-causal/Causal/Flat/*` (Barbot), group theory excluded | ~74k | **Lorentzian** |
| `Causal/Flat/{Selberg*,ACD*,AffACD*,MaxUnip*,AffUnip*,Gromov*,TitsNull}` | ~9k | **orbit-discrete-groups** |
| `Causal/Flat/Bieberbach*` | ~2k | **AffineGX.Riemannian** |
| `lean-causal/Causal/Port/*` | 16k | **deleted**: its gx copies are replaced by imports of GX and AffineGX |
| `lean-gx/GX/{Topology,Structure,Spread,Singular,Branched,SingularII}`, general `Suspension` | ~66k | **GX** |
| `lean-gx/GX/Hyperbolic`, `Suspension/Affine`, `Suspension/{Conic,Celestial}`'s affine models | ~6k | **AffineGX** |
| `lean-gx/GX/{BTZ,Lorentz}` | 56k | **Lorentzian** (the BTZ local models to Lorentzian.Local) |
| `lean-gx/GX/BBS` | 11k | **BBS** (the link and HS classification to BBS.Local) |
| `lean-benzecri/*` | 35k | **AffineGX** (its copied `gxGroupoid`, `IsGXMorphism` and universal cover become imports of GX) |
| planned `lean-alexandrov` (DEC-209) | — | **Lorentzian** (radiant spacetimes), not a package of its own |

Papers then span packages. Their ledgers need several Lean roots:
- ETT: ETT, plus Lorentzian.Local for §3–4;
- gx: GX, plus Lorentzian for §4;
- Barbot: Lorentzian, plus the orbit;
- BBS: BBS, plus BBS.Local.

## 3. What the move gains

- **Fewer copies.** `Causal/Port` (16k lines of copied gx) and Benzécri's copied groupoid both
  disappear.
- **"Benzécri is the regular case of gx" becomes a matter of definitions.** AffineGX imports GX
  instead of duplicating it.
- **The tiers make the four-layer framing visible in the package graph.** General tier = layer 1, local tier = layers 2–3, global tier = the instantiated results and layer 4's classifications.
- **ETT is the pure causal root** the programme's layer-1 rule asks for, and GX is the pure
  structural root.

## 4. Prerequisites: tooling to build before the window

1. **Multi-root ledgers.** `tools/ledger.py` and `ledger.toml` must take several Lean roots per
   paper (§2), and `tools/doubledag.py` and the atlas overlay must follow.
2. **A mechanical rename tool.** It takes a map `old module/namespace → new` and rewrites Lean
   sources, imports, every `curation.toml`, binder, ladder witness, roadmap evidence, kb entry and
   atlas overlay. It also checks that each name still resolves.
3. **A pin-bump tool for seven git-pinned packages.** It bumps a package's pin in every dependent
   and rebuilds in dependency order. This fixes the "ledger predates a pinned commit" failures seen
   in the journals.
4. **An import-graph gate.** Each library declares its tier, imports go only down the tiers, and a library may import only what §1 allows, orbits only
   as declared external inputs, and the graph must be acyclic. It needs a fixture under
   `tools/fixtures/`, as every gate does.
5. **Leases per package and sub-package directory** in `tools/lease.py` and both loop skills.

## 5. The migration window

The trigger is the author's go-ahead, once §4 exists and ETT's gluing refactor (DEC-167) has
landed, since that refactor rewrites the same ETT core.

1. Stop `/atlas-team`, `/ett-programme` and `/egf-programme` (their leases dropped). Open a branch.
2. Create the seven packages and the orbit, and move files with `git mv` (history kept), in
   tier order: general (ETT, GX), the orbit, local (AffineGX, Wave, BBS.Local, Lorentzian.Local),
  global (Lorentzian, BBS, Einstein).
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
- **Where Benzécri's Theorem A sits.** It is a global classification of affine manifolds over a
  local model theory. Does it stay in AffineGX, or go into a global library of its own? The same
  question applies to Bieberbach in AffineGX.Riemannian.
- **Further orbits.** Beyond discrete groups: Troyanov's cone metrics (gx), the spectral gaps (EGF),
  and the PDE facts named as hypotheses in ERS (Sogge, O'Neill)?
