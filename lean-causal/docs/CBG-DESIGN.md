# CBG for flat spacetimes with singular lines — ETT generality, Sbierski's order (design)

Read-only design, 2026-11-01, requested by gx (gx DEC-29: full flat CBG with singular lines,
Sbierski 1309.7591, `papers/gx/sources/1309.7591/`). Home: `lean-causal/scaffold/CausalScaffold/CBG/`.
It overlaps ETT §4 (`theo:CBG` and its lemmas, `scaffold/CausalScaffold/SubExtension.lean`): marking
ETT labels is the ETT campaign's; rows stay partial until the singular instance discharges the model.

## 1. Statement
A geometry 𝔊 (§2) gives admissible spacetimes (T2, connected, a structure and the causality it
generates) and structure morphisms (each an `IsEMorphism`). A **Cauchy development** of `M₀` is
`(N, φ)` with `IsCauchyEmbedding C₀ D φ` and φ a 𝔊-morphism (`S` irrelevant by
`IsEMorphism.isCauchySurface_image`); morphisms `f ∘ φ = φ'` are automatically Cauchy embeddings.
"Maximal" has two readings (ETT §4 never defines it): **ETT/Barbot** (every morphism out is bijective)
and **Sbierski Thm 2.8, universal** (every development maps into it; unique under rigidity).
```
theorem cbg (𝔊) (M₀) (hGH) (hS : C₀.IsCauchySurface S) :
  ∃ M̄ : Dev 𝔊 M₀, ∀ N : Dev 𝔊 M₀, ∃! f, Dev.IsMorphism N M̄ f
```
ETT's form follows (universal ⇒ ETT-maximal; ETT-maximal ⇒ universal; uniqueness up to unique
isomorphism). The universal form is strictly stronger and is what gx's B21 Lemma 2.3 uses.
`rem:CBG_manquant`: (ii) small skeleton → the bound of §3.6; (i) second countability of M̄ → a
geometry hypothesis (proved for regular flat, DEC-49; open with singular charts, R2).
ETT gaps filled: the "inductive limit" (l.2335) → Sbierski's gluing; ppcm's global hyperbolicity
(l.2319–2325) → proved (§3.5).

## 2. Hypotheses; why rigidity and a size bound are essential
**Without rigidity (timelike line):** M₀ = (−∞,0), `kinkIso` (x ↦ x for x ≤ 0, 2x for x > 0) is an
`IsEMorphism` fixing M₀ (`timelikeLine_not_isRigid`): (ℝ,id,id), (ℝ,id,kink) are over-extensions with
no morphism between them; no Hausdorff minimal over-extension exists (so `prop:ppcm_Cauchy` fails);
inequivalent maximal sub-extensions (uniqueness of `prop:Cauchy_pgcd` fails); x ↦ arctan x for x > 0
is a non-surjective Cauchy self-embedding (existence fails — the 1-D DEC-45 arctan finding). Without
T2 carriers the branching line (ETT l.1312) IS a minimal over-extension: `CommonSubExtension` /
`CommonOverExtension` must ask T2. **Without a size bound:** the long ray has no future-inextensible
curves, every set is Cauchy, developments of unbounded cardinality — no universal one; second
countability rules it out. The existing `SubExtension.IsRigid` (over all causal local isomorphisms) is
the WRONG hypothesis: CBG is false for those.

**Level A (what the proof consumes):**
```
structure Geometry where
  Str : (M : Type u) → [TopologicalSpace M] → Type u
  causality : Str M → Causality M                      -- absolutely minimal on every open
  IsMor : Str M → Str N → Opens M → (M → N) → Prop     -- sheaf: mono, local, id, comp, congr
  isEMorphismOn : IsMor s t W f → IsEMorphismOn (causality s) (causality t) W f
  inv : IsMor s t W f → InjOn f W → IsMor t s (f '' W) (invFunOn f W)
  restrict : Str M → (W : Opens M) → Str W
  transport : (e : M ≃ₜ M') → Str M → Str M'
  glue : FamilyGlueData → (compatible) → Str glued
  rigid : IsConnected V → IsMor s t V f → IsMor s t V g → O ≤ V → O.Nonempty → EqOn f g O → EqOn f g V   -- A1
  axioms : SingularFlatAxioms (causality s) (sing s); curvesExtend; sigmaCompact          -- A2
  germExt : …  -- A3, Sbierski Lemma 3.8 / cor:ext_continue, K⁻ AND K⁺ versions (no duality)
  slice : …    -- A4, local spacelike slice through a boundary point, both time directions
```
Hausdorffness of the glued space is a THEOREM (Sbierski Thm 3.13, from A1–A4; topological half:
`Gluing.t2Space_iff_Cdist_eq_empty`, `C_eq_closure`). **Level B (local model, gx discharges):**
model Y (Minkowski ⊕ Σ_α E_α), `G : StructureGroupoid Y`, admissible = `ChartedSpace Y M`,
`HasGroupoid M G`, T2, connected; `IsMor` = `LiftProp (G.IsLocalStructomorphWithinAt)`; (B1) G rigid on
connected opens; (B2) local uniqueness (B21 `prop:isom` + `lem:liouville`); (B3) causal facts on Y;
(B4) slices on Y. `Geometry.ofLocalModel : Level B → Level A`. **No time reversal:** the time
reverse of an E₀-manifold is not one (gx D-12(e)): A3/A4 stated in both directions.

## 3. Sbierski's order on the API
1. Rigidity + connectedness (Cor 3.2, `lem:C_ext_connexe`), re-routed via `CurvesExtend` +
   `inextensible_ordConnectedComponent` (bypassing the possibly-false `exists_mem_image_inf`).
2. Injectivity (Lemma 3.3; ETT ledger gap 1) by lifting causal curves along a local homeomorphism.
3. MCGHD as the union (Thm 3.4, `prop:Cauchy_pgcd`): reuse `IsPgcdCandidate`, `pgcdOpens`, `pgcdMap`,
   with `IsRigidFor IsMor`; new: a Cauchy inclusion into a causal T2 spacetime with CurvesExtend is
   causally convex; union of Cauchy inclusions is a Cauchy inclusion (closes ETT gap 2).
4. No corresponding boundary points (Prop 3.7 = `lem:corresponding_K` with K⁻; Lemma 3.8 = A3;
   Lemma 3.9 via a Geroch time minimised on ∂U ∩ J(Σ, p₀); Thm 3.6 = A4 + A3; T2 of the gluing).
5. Two developments embed in a common one (Thm 2.7, `prop:ppcm_Cauchy`): structure by `glue`,
   causality by `Gluing.causality`/`CompatibleAlong`, GH directly (causal convexity of each ιᵢ(Mᵢ)).
6. Size bound: SC + T0 ↪ `Set ℕ`; `SmallDev M₀ : Type`.
7. Maximal development (Thm 2.8): glue all small developments along pairwise MCGHDs; cocycle from
   maximality + rigidity; T2 from pairs; universality; `ULift` to `Type u`.
Labels this would certify (ETT, partial until the singular instance): `theo:CBG`, `prop:Cauchy_pgcd`,
`prop:ppcm_Cauchy`, `lem:C_ext_connexe`, `lem:corresponding_K`, `cor:ext_continue`,
`cor:model_corresponding`, `prop:C_connexe`, `prop:Cauchy_point_min`, `prop:Cauchy_non_max`,
`def:common_sub/over_extension` (with T2).

## 4. Flat instance; what gx discharges
(Isom, 𝐌)-manifolds: `Str` = ChartedSpace + HasGroupoid; `IsMor` = `IsLocalIsometry`; A1
`IsGXMorphism.eq_of_eqOn` + `isAnalyticAction_isom`; A3 trivial (one g on a connected V); A4
hyperboloid level sets of τ_q(r) = √(−Q(q−r)) in a chart; A2 Minkowski facts, CurvesExtend, DEC-49.
gx for E₀: (i) model + `SingularFlatAxioms`; (ii) B1 a.e. rigidity (`lem:liouville`); (iii) B2 at
BTZ points (`prop:isom`, α = 0); (iv) B4 both directions (spear graphs); (v) K± calculus at BTZ
points; (vi) second countability of E_{≥0}-manifolds; (vii) `sigmaCompact`.

## 5. Packages (`scaffold/CausalScaffold/CBG/`, ~11–13k lines)
| # | file | content | deps | risk |
|---|---|---|---|---|
| 1 | Geometry | Level A/B, `IsRigidFor`, kink/arctan witnesses | — | interface — **gate: review before 4–10** |
| 2 | CausalConvex | Cauchy inclusion ⇒ convex; union; `c_ext_connexe` | — | low |
| 3 | Injective | Lemma 3.3 by curve lifting | — | medium |
| 4 | Pgcd | MCGHD, principal `cauchy_pgcd` | 1,2,3 | low |
| 5 | Corresponding | Prop 3.7 (K±), ext_continue, C open | 1 | BTZ points |
| 6 | NoCorresponding | Lemmas 3.9, 3.11, Thms 3.6, 3.13 | 4,5 | time function |
| 7 | Ppcm | Thm 2.7, GH of the gluing | 2,6 | GH without Geroch |
| 8 | FamilyGluing | family gluing with cocycle, T2 from pairs | — | low |
| 9 | Bound | SC T0 ↪ Set ℕ, SmallDev | 1 | universes |
| 10 | Maximal | Thm 2.8, `cbg`, ETT corollaries | 4,7,8,9 | medium |
| 11 | FromModel | Level B ⇒ Level A | 1 | A3/A4 connectedness |
| 12 | Flat/CBG | flat instance `flat_cbg` | 1,11,10 | A4 hyperboloid |
Parallel start: 1, 2, 3, 8; then 9, 11; then 4, 5; then 6, 7, 10, 12.
Risks: R1 `sigmaCompact` (compactness of J⁺(Σ) ∩ J⁻(p)); R2 SC with singular charts; R3 K⁻ at BTZ
points; R4 no duality; R5 the ruling on "maximal".

## 6. Rulings and review outcomes (2026-11-01)
- DEC-59 maximal = universal; DEC-60 the thesis framework (rigid morphisms of singular (G,X)-manifolds);
  DEC-61 start now; gx DEC-62 X_A-morphisms in the LOCAL form; gx DEC-63 these.tex:3176 quantifies over
  EVERY singular point; DEC-64 fix ETT's `BTZAxioms.Iplus_eq` (false in E₀) → `Iplus_of_lt`.
- gx review (`lean-gx/campaign/WP-28-scope/CBG-REVIEW.md`): C1 corrected BTZ bundle; C2 second
  countability carried (Dev, admissible-M fields, new `secondCountable_of_cauchy`); C3 `curvesExtend`
  for GH M only; C4 strong `localUnique_sing` (B21 `prop:isom_strong`); C5 export the charted-space
  gluing with package 11.
- **A3 at BTZ points stays as stated, without (B)** (gx, `A3-B-INVESTIGATION.md`): (B) = these.tex
  l.6634–6638, the hypothesis of `prop:Cauchy_non_max` ("J_{M₁}(Σ₁,p) ∖ {p} ⊂ j₁(N)"), named only at
  l.6693, is Sbierski Lemma 3.9's conclusion — A4's hypothesis, not A3's; adding it to A3 breaks
  Sbierski's order. Future side at BTZ points: (B) automatic (thesis `lem:passe_pgcd`, l.6541–6554);
  past side: (B) can fail (U = I⁺(0) ∪ {τ+r > 1/2}, Σ = {τ+r = 1}) while A3 still holds. gx owes for
  E₀: the two connectedness arguments, the past-side B2 step outside U, K⁺ injectivity.
- **Findings against the thesis** (author's): the stray "(B)" label (l.6693); the missing `∖{p}` at
  l.6658; the past side is never treated, which E₀'s time asymmetry requires.
- **Risk for package 10 (Maximal), from the Geometry re-audit:** after C2/C3, M̄'s global
  hyperbolicity must be proved before its second countability and without `curvesExtend` /
  `isCompact_*` (which now require GH + SC); §3 step 7 must say how (e.g. GH of each glued piece and
  the causal-convexity argument of step 5, then `secondCountable_of_cauchy`). Also §2's A2 sketch
  ("SingularFlatAxioms; … sigmaCompact") now reads `SingularFlatAxiomsCorr` (C1).
- **Interface round 2 (gx, 2026-11-01), queued until packages 7/10/12 land (they compile against
  Geometry):** (1) ACCEPTED: field `timeFunction` on Geometry (admissible M: T2, connected, SC; GH ⇒
  `HasTimeFunction`) and its LocalModel counterpart — discharged flat by `Flat/GerochFlat`
  (admissible measures → Geroch time), E₀ by SingularGeroch; replaces the disclosed `InjOn` /
  time-function hypothesis of Pgcd, NoCorresponding, Ppcm, Maximal. (2) Past-side B2 at a BTZ point:
  `localUnique_sing_adherent` with the **full wrap-around** largeness clause — U contains
  reg ∩ I⁻_O(r) for some r above y₀ on its line (`causalityY.le O y₀ r`); point contact (cone
  counterexample, WP-36k) and "closure contains a segment of the line" (a boost along Δ conjugates P
  to a non-integral power) are both rejected. gx's E₀ argument: a loop around Δ in reg ∩ I⁻_O(r)
  has holonomy P, f maps it to a loop winding the same way, so the lift normalises ⟨P⟩, and the
  normaliser is Isom(E₀). If FromModel's past-side pieces have another shape, gx adapts the clause.
