import CausalScaffold.Flat.Nonloxodromic
import CausalScaffold.Flat.Loxodromic
import CausalScaffold.CompactCauchy
import CausalScaffold.CurvesExtend

/-!
# `CausalScaffold.Flat.Classification` — Barbot §11: Theorems A and B, absolute maximality

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §11
"Summary of the proof" (`sumup`, `GHFspace.tex` l.3477–3679 of the labelled file
`papers/barbot/legacy/labeled/GHFspace.tex`) and the two theorems it assembles. **No label is
marked**: both rest on tagged `sorry`s (here and upstream) and on named external hypotheses
(DEC-36), so both are partial (SCOPE).

* `bthm:caucomp` — `GHFspace.tex:338` (Theorem A), **stated and assembled** under reading R1
  (DEC-43): `barbot_A`, through the layering G3 `barbot_A₀` (embedding) → [11.i] → `barbot_A`.
* `bthm:cauclo` — `GHFspace.tex:353` (Theorem B), **stated and assembled**: `barbot_B`, with
  "standard" read as Cauchy-compact Cauchy-hyperbolic (G4). G4 is realised in the statement by
  `CauchyCompact` on the torus product (`IsCHTorusProduct M₁ ∧ CauchyCompact M₁`, exactly
  BARBOT-THEOREMS §2), which is equivalent (the torus fibre being compact; not proved here) to
  its Cauchy-hyperbolic base being standard;
  `IsStandard` states G4 for a spacetime and is not used by the statements (the library builds no
  base spacetime of a torus product to apply it to).
* Prose: [11.i] absolute maximality (`maxi`, l.3563–3679): `amgh_of_isTranslationSpacetime`,
  `amgh_of_isMisnerSpacetime` (F1's nonzero boost is in `IsMisnerSpacetime`, G2),
  `amgh_of_isCHCentralExtension`, and G1 + G3 for the unipotent family
  (`exists_absMax_unipotent_ltp`). **Proved, no `sorry`:** the lifting of an isometric embedding
  to the universal covers with rigidity (`exists_lift_of_isQuotientOf`, l.3586–3599), its
  equivariance (`exists_deck_of_lift`: `gΓ₀g⁻¹ ≤ ρ_N(Deck)`), its end for a convex `Ω₀`
  (`surjective_of_lift_of_range_subset`: `𝒟_N(Ñ) ⊆ gΩ₀ ⇒ f` onto) and for `Ω₀ = 𝐌ⁿ`
  (`surjective_of_isQuotientOf_top`, `absMax_of_isTranslationSpacetime`, l.3616–3618:
  translation spacetimes are absolutely maximal among **all** flat targets); **absolute
  maximality of Misner spacetimes** (`surjective_of_isQuotientOf_misner`, both wedges) **and of
  quotients of the regular domains `Ω^±(Λ(Γ))`** (`surjective_of_isQuotientOf_limitOpensPlus`,
  `…Minus`, family (b)) among GH Cauchy-complete targets (l.3620–3626) — these rest only on the
  bridge (`exists_developsCC_of_isCauchyComplete`, CauchyComplete) applied to the target, which is
  how "Theorem A on the target" enters (finding 5); GH of the models in
  the `IsQuotientOf` form (`gh_of_isQuotientOf`, `gh_of_isTranslationSpacetime`,
  `gh_of_isQuotientOf_misnerWedge`); [11.ii] (l.3573–3581): `surjective_of_mgh_cauchyCompact` (G8);
  Rem 2.3 `clomax` corrected (DEC-44, l.571–578): `absMax_of_cauchyCompact_of_mgh`, through lemma K
  (`Causality.isCauchySurface_of_isLocallyCauchyTwoSided`) under its named hypotheses
  (`FlatLemmaKData`); G9 (l.3542–3548): `cauclo_from_embedding`.
* gx exports: **`equality_of_absMax`** (the §11.3 lifting argument, l.3607–3611, `AbsMax P M →
  range 𝒟 = Ω`, `P` parametric) — **proved, no `sorry`**; `range_eq_omegaS_of_absMax`.
* The bridge connection (wave 3, written in parallel): `developsCC_iff_bridge`,
  `exists_developsCC_of_isCauchyComplete'` — CauchyComplete's bridge conclusion is Develop's
  `DevelopsCC`; proved here.

> Up to finite coverings and linear twisted products, every Cauchy-complete globally hyperbolic
> flat spacetime can be tamely embedded in an absolutely maximal globally hyperbolic spacetime
> which is a translation spacetime, a Misner spacetime, a unipotent spacetime, or the twisted
> product of a Cauchy-hyperbolic flat GH spacetime by an euclidean torus. (l.340–347)

> Up to finite coverings, every maximal Cauchy-compact globally hyperbolic flat spacetime is
> isometric to a translation spacetime, a Misner spacetime, or the twisted product of a standart
> spacetime (Cauchy-compact Cauchy-hyperbolic GH spacetime) by an euclidean torus. (l.355–359)

> (i) Translation spacetimes, Misner spacetimes, and twisted products of Cauchy-hyperbolic
> spacetimes by flat torii are absolutely maximal, and any unipotent spacetime can be tamely
> embedded in some absolutely maximal unipotent spacetime. (l.3568–3571)

> (ii) Any maximal Cauchy-compact GH spacetime is not only embedded in a finite quotient of a
> translation spacetime, a Misner spacetime or the twisted product of a standart spacetime by a
> flat torus, it is actually \emph{isometric} to one of them. (l.3573–3576)

> Hence, if the inclusion $\Omega_{0} \subset \Omega_{1}$ is actually surjective, then
> $\Gamma'_{0} = \Gamma_{1}$, and $f$ is a surjective embedding. (l.3609–3611)

> It follows that nontrivial linear twisted products destroy Cauchy-compactness (l.3542–3543)

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; `Minkowski d` has `d` spatial
dimensions: Barbot's `n` is `d + 1`. The Misner and unipotent families live in
`Minkowski (e + 1)` (Examples); `IsMisnerFamily`, `IsUnipotentFamily` extend them by `False` to
`d₁ = 0`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| A: `M` Cauchy-complete GH flat | ✓ carried: `GH M` (ETT's) + `IsCauchyComplete d M` (CauchyComplete's metric notion, DEC-35; Lean ≥ paper) |
| A, B: "any dimension" (l.388, l.411) | ✓ carried: every `d`, `d = 0` (`𝐌¹`) included. The Misner branch, which needs `d = d' + 1`, is unreachable at `d = 0`: nothing is loxodromic there (`not_isHyperbolic_zero`: `IsHyperbolic` asks `minkQ e₁ = 1`, and `minkQ (t, x) = −t²` in `Minkowski 0`) |
| A/B: external group theory (Benoist, Bieberbach, Auslander–Carrière–Dal'bo, Carrière–Dal'bo, cited; Tits, not cited) | ⚠ strengthened: named hypotheses bundled in `BarbotExternals d` (DEC-36): `BenoistNoLox k`, `BieberbachI (ℝᵏ)` (`k ≤ d + 1`), `AuslanderCarriereDalbo k`, `MaxUnipotentSubspace k` for `k ≤ d`, and — **added 2026-11-01, disclosed adaptation** to Nonloxodromic's round-3a statement change of `nonloxodromic`/`exists_timelike_fixed_of_elliptic_of_null` (DEC-27; the printed §9 lemma is false for `d ≥ 5`) — `TitsVirtuallyAbelianNull k` for `k ≤ d` (Tits' alternative + amenability for the branch l.2621–2622 overlooks, null `v₀` fixed and all elliptic; **not cited by Barbot**, witness at `d = 0` `titsVirtuallyAbelianNull_zero`). Theorem A/B's conclusions are unchanged; their hypothesis `BarbotExternals d` is strictly stronger than before by this one component. Non-vacuity: `barbotExternals_zero` (the bundle at `d = 0`, from the components' witnesses), so Theorem A's hypotheses are jointly satisfiable (`barbot_A_hypotheses_zero`: the bundle, GH and Cauchy-completeness of `𝐌¹`). For `d ≥ 1` the bundle is consistent on the cited literature only (Bieberbach in `ℝ^{k ≥ 2}`, Benoist, Auslander–Carrière–Dal'bo, Carrière–Dal'bo); no component is trivially true or false (each has a not-trivially-true witness in `Externals`/`Bieberbach`; `AuslanderCarriereDalbo`'s `DiscreteTopology Γ` is read in `isomTopology`, not in the discrete topology) |
| B: `M` maximal Cauchy-compact GH | ✓ carried: `GH M`, `CauchyCompact M`, `MGH M` |
| B: π₁ finitely generated ⇒ family (a) (DEC-44, Selberg) | ⚠ strengthened: `SelbergLemma (Minkowski d)` (named external) |
| B: "closed spacelike hypersurfaces are Cauchy" (l.3537–3540, asserted) | ⚠ strengthened: lemma K's named data `FlatLemmaKData` on **every** GH flat target of dimension `d` (DEC-44): tarentin, causal arc-connectedness, `J^±(p) ≠ {p}`, `CurvesExtend`, a chronal causal flow, an acausal Cauchy surface. The non-vacuity witness `flatLemmaKData_minkowskiSpace` is **pointwise** (one instance, `𝐌ⁿ`); the universal form `∀ N, GH N → FlatLemmaKData N` is true by standard GH facts (Geroch / Bernal–Sánchez for the acausal Cauchy surface, a complete timelike flow), not certified here |
| Rem 2.3: CGH ⇒ AMGH | ⚠ corrected (DEC-44): GH + Cauchy-compact + **MGH** ⇒ `AbsMax (fun _ => True)` |
| §11.3 equality: `M` absolutely maximal, `M(S)` a GH spacetime of the class | ✓ carried, `P` parametric (DEC-45): `AbsMax P M`, `GH B`, `P B`, `IsQuotientOf B Γ Ω`, `𝒟` injective, `range 𝒟 ⊆ Ω` |
| universes | targets of `AbsMax` are flat spacetimes of the same universe (`FlatSpacetime.{u}`); the models, `M'` and `B` are in `Type` (`FlatSpacetime.{0}`), as upstream. A Type-0 cover, base and model is a stronger conclusion, not a weaker one. The one place the universe matters is `AMGH (CauchyCompleteClass d₁) M₁` at `.{0}`: `AbsMax.{0}` is Barbot's absolute maximality against Type-0 targets; every second-countable flat spacetime has an isometric copy in Type 0 (`Shrink` and transport of structure; not proved here), so for the paper's manifolds nothing is lost |
| the four (A) / three (B) families | `IsTranslationSpacetime` and `IsMisnerSpacetime` have inhabitation witnesses (`isTranslationSpacetime_quotient`, `misner_example`); `IsCHCentralExtension`, `IsCHTorusProduct`, `IsCauchyHyperbolic` have none in the library, and `IsUnipotentSpacetime` only with trivial `Γ` (Examples' SCOPE). An empty disjunct would not make A vacuous, but would make the corresponding upstream case theorem unprovable. Family (b) (`IsCHCentralExtensionOf`, Loxodromic, Def 4.18 l.1212–1214) asks "no global fixed point", not "nonelementary": it admits elementary groups with a loxodromic element (e.g. infinite dihedral), so A's fourth disjunct is slightly broader than BARBOT-THEOREMS §1 (A's conclusion slightly weaker than R1 as drafted); faithful to Def 4.18, and the Misner disjunct covers that case up to finite index |

## SCOPE (disclosed)

* **Readings.** Theorem A is R1 (DEC-43): a finite cover `M'` of `M` tamely embeds in an LTP `B`
  over a model `M₁` of dimension `≤ d`, `M₁` AMGH in its own dimension for Cauchy-complete targets
  (`CauchyCompleteClass`); the fourth family is the central-extension form (b),
  `IsCHCentralExtension` (DEC-44). Theorem B: "standard" is Cauchy-compact Cauchy-hyperbolic (G4);
  its third family is (a), `IsCHTorusProduct ∧ CauchyCompact` (π₁ finitely generated, Selberg),
  where `CauchyCompact` of the product carries G4 (`IsStandard` is stated, unused).
* **Lemma K's data is universal, its witness pointwise.** `barbot_B`,
  `absMax_of_cauchyCompact_of_mgh` and `surjective_of_mgh_cauchyCompact` carry
  `hK : ∀ N, GH N → FlatLemmaKData N`; it cannot be narrowed to the targets used, because absolute
  maximality quantifies over every GH target. `flatLemmaKData_minkowskiSpace` shows one instance
  (`𝐌ⁿ`) only; the universal form rests on standard GH facts (an acausal Cauchy surface,
  Bernal–Sánchez; a complete timelike flow; tarentin and causal arc-connectedness of GH flat
  spacetimes), which the library does not prove for a general flat spacetime (`Splitting.lean`'s
  target 4 is itself a tagged `sorry`).
* **Namespace.** `UniversalCover.exists_deck_apply_eq` is declared in `Causal.Flat` (the campaign's
  namespace rule), so its full name is `Causal.Flat.UniversalCover.exists_deck_apply_eq` and dot
  notation on the ported `Causal.UniversalCover` does not find it; it is called by full name.
* **Assembly, proved here (no `sorry` of their own):** `barbot_A₀` (bridge → developing pair →
  case split loxodromic / not → §9, §10 → the finite cover; at `d = 0` the elementary loxodromic
  branch is refuted by `not_isHyperbolic_zero`), `barbot_A` (A₀ + [11.i] + G1/G3),
  `barbot_B` (A₀ + G9 + Rem 2.3 corrected + [11.ii]), `caseOutput` and its three branches,
  `absMax_of_cauchyCompact_of_mgh` (Rem 2.3 corrected, from lemma K's proved form),
  `surjective_of_mgh_cauchyCompact` ([11.ii], G8), `equality_of_absMax`,
  `range_eq_omegaS_of_absMax`, the bridge connection; and the [11.i] infrastructure
  `exists_lift_of_isQuotientOf`, `exists_deck_of_lift`, `surjective_of_lift_of_range_subset`,
  `surjective_of_isQuotientOf_top`, `absMax_of_isTranslationSpacetime`,
  `surjective_of_isQuotientOf_misner` (with `isLoxodromic_axisBoost`, `linOf_misnerMap`,
  `nullX_mul_nullY_nonpos_of_mem_achronalDomain`, `nullX_mul_nullY_neg_of_isOpen`),
  `surjective_of_isQuotientOf_limitOpensPlus`, `surjective_of_isQuotientOf_limitOpensMinus`
  (with `range_subset_quadrant_of_mem_range`), `gh_of_isQuotientOf`, `gh_of_isTranslationSpacetime`,
  `gh_of_isQuotientOf_misnerWedge`, `globallyHyperbolic_of_isIsometricEmbedding_of_surjective`,
  and the non-vacuity witnesses `barbotExternals_zero`, `barbot_A_hypotheses_zero`.
* **Sorries in this file (each tagged with its obstruction):** `nonloxodromic_parabolic_convex`
  (Nonloxodromic's parabolic export omits the convexity of its `Ω`, which tameness needs: a
  finding for that file), `exists_finiteCover_tameEmbedding` (the intermediate cover
  `ρ⁻¹(Γ'')\M̃` and π₁ of the quotients), `amgh_of_isTranslationSpacetime` (Cauchy-completeness
  of the model only: its GH and absolute maximality are proved), `amgh_of_isMisnerSpacetime`
  (absolute maximality proved, GH proved on the future wedge; the past wedge's GH and
  Cauchy-completeness remain), `amgh_of_isCHCentralExtension` (absolute maximality proved; GH of
  the constructed quotient and Cauchy-completeness remain), `exists_absMax_unipotent_ltp` (G1 + G3),
  `isLocallyCauchyTwoSided_image` (an embedded acausal compact Cauchy surface is locally Cauchy
  and two-sided in the target: lemma K's input), `isCauchyComplete_of_cauchyCompact` (smoothing
  of a topological Cauchy surface), `cauclo_from_embedding` (G9, the passage (b) → (a), finite
  covers of maximal CGH spacetimes).
* **Upstream sorries** reached by `barbot_A` / `barbot_B` (re-derived 2026-11-01 from
  `#print axioms` and the transitive closure of declarations whose own body uses `sorryAx`; the
  other agents of this run are closing some of them, so re-derive at graduation): from
  CauchyComplete `exists_splitting_of_isCauchySurface` (re-derived 2026-11-01, second pass:
  `isCoveringMap_projAlong_comp` and `bcor_quoiso` are no longer reached); from Nonloxodromic
  `nonloxodromic_elliptic` (`exists_timelike_fixed_of_elliptic_of_null` is now proved, under the
  external `TitsVirtuallyAbelianNull`); from Loxodromic `loxo_elementary_misner`,
  `loxo_generic_centralExtension`. The absolute-maximality lemmas
  `surjective_of_isQuotientOf_misner` / `_limitOpensPlus` / `_limitOpensMinus` reach
  `exists_splitting_of_isCauchySurface` only (through the bridge on the target).
* **Not attempted:** the corollary on closed Cauchy hypersurfaces (finitely covered by
  `Tᵏ × closed hyperbolic manifold`, l.383–386): the library has no notion of a closed hyperbolic
  manifold.
* **Findings.** (1) Nonloxodromic's `nonloxodromic_parabolic` should export `Convex ℝ Ω` (true:
  `Ω = π_𝒰⁻¹(Ω_A)`, a slab between null hyperplanes), without which no tame embedding into
  `B = Γ''\Ω` can be derived (π₁(B) is an extension of `Γ''` by π₁(Ω)). (2) Barbot's (ii) "follows
  from (i)" (l.3578) also needs that a finite cover of a maximal CGH spacetime is maximal, which the
  paper does not state (used in `cauclo_from_embedding`). (3) [11.i]'s proof applies Theorem A to the
  target `N` (l.3588–3590): the layering A₀ → (i) → A (G3) is what makes that non-circular; here
  `barbot_A₀` carries the embedding and (i) is stated after it. (4) For translation spacetimes
  [11.i]'s proof does not need Theorem A on the target (l.3586–3590, l.3616–3618): the lift of
  `f ∘ π : 𝐌ⁿ → N` to `Ñ` composed with `𝒟_N` is a global isometry, so its inverse is a global
  section of `𝒟_N`, whose range is clopen; translation spacetimes are absolutely maximal among
  **all** flat targets, GH or not (`absMax_of_isTranslationSpacetime`), and every local isometry
  out of them is onto. (5) For Misner spacetimes and family (b), "Theorem A applied to `N`"
  (l.3588–3590) is needed only through the **bridge** on the target (`𝒟_N` injective with
  `𝒟_N(Ñ) ⊆ Ω(S̃_N)`, Develop's `bprop_danom` under (CC′)), not through the classification of `N`:
  the limit-set comparison `Λ(Γ₀) ⊆ Λ(Γ₂) ⇒ Ω(Λ(Γ₂)) ⊆ Ω(Λ(Γ₀))` (l.3622–3626) is replaced by one
  quadrant argument per loxodromic element of `Γ₀` (`range_subset_quadrant_of_mem_range`, from
  Loxodromic's `omegaS_subset_quadrant`), the sign being fixed because `𝒟_N(Ñ) ⊇ gΩ₀` (Barbot's
  remark "a future `Ω₀` cannot sit in a past `Ω₂`"), and the passage from `Λ₀` to its closure
  `Λ` by openness of `𝒟_N(Ñ)`. For Misner, `Ω₀`'s quadrants are computed directly: the achronal
  domain of `ψ g_{s,w} ψ⁻¹` lies in `ψ{xy ≤ 0}` (an exponential beats a quadratic). (6) The
  absolute maximality of family (b) uses none of `IsCHCentralExtensionOf`'s conditions beyond the
  quotient form `M₁ = Γ\Ω^±(Λ(Γ))`: every quotient of a regular domain of its own limit set is
  absolutely maximal among GH Cauchy-complete targets.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
wave 5, package WP-34e-Classification.
-/

namespace Causal.Flat

open Set Function Filter Topology TopologicalSpace

universe u

variable {d : ℕ}

/-! ## §0 The families in every dimension, the externals, lemma K's data -/

section Families

/-- **The Misner family in dimension `d₁`** (`Examples`' `IsMisnerSpacetime` lives in
`Minkowski (e + 1)`; there is none in `𝐌¹`). -/
def IsMisnerFamily : (d₁ : ℕ) → FlatSpacetime.{u} d₁ → Prop
  | 0, _ => False
  | _ + 1, M => IsMisnerSpacetime M

/-- **The unipotent family in dimension `d₁`** (none in `𝐌¹`). -/
def IsUnipotentFamily : (d₁ : ℕ) → FlatSpacetime.{u} d₁ → Prop
  | 0, _ => False
  | _ + 1, M => IsUnipotentSpacetime M

variable (d) in
/-- **The class of Cauchy-complete targets** (DEC-45 (α)): CauchyComplete's metric notion. -/
def CauchyCompleteClass : FlatSpacetime.{u} d → Prop := fun N => IsCauchyComplete d N

/-- **Theorem A's four model families** (DEC-43, DEC-44): translation, Misner (with a nonzero
boost, F1), unipotent, and the central-extension form (b) of "Cauchy-hyperbolic × torus". -/
def IsModelA {d₁ : ℕ} (M₁ : FlatSpacetime.{u} d₁) : Prop :=
  IsTranslationSpacetime M₁ ∨ IsMisnerFamily d₁ M₁ ∨ IsUnipotentFamily d₁ M₁ ∨
    IsCHCentralExtension M₁

/-- **G4: a standard spacetime** (l.358): a Cauchy-compact Cauchy-hyperbolic spacetime. Stated for
reference: Theorem B carries G4 as `CauchyCompact` of the torus product (`IsModelB`), since the
library constructs no base spacetime of an `IsCHTorusProduct` to which `IsStandard` could apply. -/
def IsStandard (M : FlatSpacetime.{u} d) : Prop := IsCauchyHyperbolic M ∧ CauchyCompact M

/-- **Theorem B's three families**: translation, Misner, and the literal twisted product (a) of a
standard spacetime by a torus — family (a), Cauchy-compact. -/
def IsModelB (M₁ : FlatSpacetime.{u} d) : Prop :=
  IsTranslationSpacetime M₁ ∨ IsMisnerFamily d M₁ ∨ (IsCHTorusProduct M₁ ∧ CauchyCompact M₁)

variable (d) in
/-- **The external group theory of §5, §9, §10** (DEC-36), as named hypotheses in every dimension
`≤ d` (Theorem A's proof of absolute maximality applies Theorem A in the model's dimension):
Benoist's elementarity (Prop 9.1), Bieberbach I (§5), Auslander–Carrière–Dal'bo (5.1),
Carrière–Dal'bo's maximal unipotent subspace (5.2) and — not cited by Barbot, added 2026-11-01 —
Tits' alternative in the form `TitsVirtuallyAbelianNull` (Nonloxodromic, DEC-27). -/
structure BarbotExternals : Prop where
  benoist : ∀ k ≤ d, BenoistNoLox k
  bieberbach : ∀ k ≤ d + 1, BieberbachI (EuclideanSpace ℝ (Fin k))
  auslander : ∀ k ≤ d, AuslanderCarriereDalbo k
  unipotent : ∀ k ≤ d, MaxUnipotentSubspace k
  /-- **Added 2026-11-01** (adaptation to Nonloxodromic's DEC-27 statement change): the external
  `TitsVirtuallyAbelianNull` (Tits' alternative + amenability; not cited by Barbot), which the
  branch l.2621–2622 overlooks (null `v₀` fixed, all elliptic) consumes through the now-proved
  `exists_timelike_fixed_of_elliptic_of_null`. -/
  tits : ∀ k ≤ d, TitsVirtuallyAbelianNull k

theorem BarbotExternals.mono {d₁ : ℕ} (h : BarbotExternals d) (h₁ : d₁ ≤ d) :
    BarbotExternals d₁ :=
  ⟨fun k hk => h.benoist k (hk.trans h₁), fun k hk => h.bieberbach k (by omega),
    fun k hk => h.auslander k (hk.trans h₁), fun k hk => h.unipotent k (hk.trans h₁),
    fun k hk => h.tits k (hk.trans h₁)⟩

/-- **Non-vacuity of the bundle** (kb/0012, DEC-36): in dimension `0` (`𝐌¹`) every component of
`BarbotExternals` holds, from the components' own witnesses in `Externals` and `Bieberbach`. For
`d ≥ 1` the bundle is consistent on the cited literature only (Bieberbach in `ℝ^{k ≥ 2}`, Benoist,
Auslander–Carrière–Dal'bo, Carrière–Dal'bo). -/
theorem barbotExternals_zero : BarbotExternals 0 :=
  ⟨fun k hk => by obtain rfl : k = 0 := by omega
                  exact benoistNoLox_zero,
    fun k hk => bieberbachI_of_finrank_le_one (by simp; omega),
    fun k hk => by obtain rfl : k = 0 := by omega
                   exact auslanderCarriereDalbo_zero,
    fun k hk => by obtain rfl : k = 0 := by omega
                   exact maxUnipotentSubspace_zero,
    fun k hk => by obtain rfl : k = 0 := by omega
                   exact titsVirtuallyAbelianNull_zero⟩

/-- **Lemma K's named data on a flat spacetime** (`CausalScaffold.CompactCauchy`, DEC-44): the
hypotheses of its proved form `isCauchySurface_of_isLocallyCauchyTwoSided` beyond GH, with the
splitting supplied by a chronal causal flow (`Splitting.lean`, target 4, itself a tagged `sorry`
for a general flat spacetime). -/
structure FlatLemmaKData (N : FlatSpacetime.{u} d) : Prop where
  tarentin : (flatCausality d N).Tarentin
  arc : (flatCausality d N).CausallyArcConnected
  jminus : ∀ p : N, (flatCausality d N).Jminus ⊤ {p} ≠ {p}
  jplus : ∀ p : N, (flatCausality d N).Jplus ⊤ {p} ≠ {p}
  curvesExtend : (flatCausality d N).CurvesExtend
  flow : (flatCausality d N).HasChronalCausalFlow
  exists_cauchy : ∃ S : Set N, (flatCausality d N).IsCauchySurface S ∧
    (flatCausality d N).IsAcausal S

/-- **Non-vacuity** (kb/0012): `𝐌ⁿ` carries lemma K's data. -/
theorem flatLemmaKData_minkowskiSpace : FlatLemmaKData (FlatSpacetime.minkowskiSpace d) := by
  have h : flatCausality d (FlatSpacetime.minkowskiSpace d) = minkowski d := flatCausality_self
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h]; exact minkowski_tarentin
  · rw [h]; exact minkowski_causallyArcConnected
  · rw [h]; exact staticCausality.Jminus_ne_singleton
  · rw [h]; exact staticCausality.Jplus_ne_singleton
  · rw [h]; exact minkowski_curvesExtend d
  · exact Flat.flatCausality_self_hasChronalCausalFlow
  · rw [h]
    refine ⟨graph fun _ => (0 : ℝ), isCauchySurface_graph_zero, ?_⟩
    exact isAcausal_graph_iff.2 fun x y hxy => by simpa using norm_pos_iff.2 (sub_ne_zero.2 hxy)

end Families

/-! ## §1 The bridge connected to `DevelopsCC` (wave 3, written in parallel) -/

section Bridge

/-- **CauchyComplete's bridge conclusion is Develop's `DevelopsCC`**: (CC′) is the conjunction of
`IsEntireAcausalGraph` and `NullSaturated`. -/
theorem developsCC_iff_bridge {M : Type*} [TopologicalSpace M] [ChartedSpace (Minkowski d) M]
    [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))] {x₀ : M}
    {D : UniversalCover M x₀ → Minkowski d} {S : Set M} :
    DevelopsCC x₀ D S ↔ (flatCausality d M).IsCauchySurface S ∧
      InjOn D (UniversalCover.proj M x₀ ⁻¹' S) ∧
      IsEntireAcausalGraph (D '' (UniversalCover.proj M x₀ ⁻¹' S)) ∧
      NullSaturated (D '' (UniversalCover.proj M x₀ ⁻¹' S)) :=
  ⟨fun h => ⟨h.cauchy, h.injOn, h.cc.entire, h.cc.nullSat⟩,
    fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, ⟨h3, h4⟩⟩⟩

/-- **The bridge, in Develop's terms** (DEC-35): a GH Cauchy-complete flat spacetime has, for every
developing pair, a Cauchy surface `S` with `DevelopsCC x₀ D S`. -/
theorem exists_developsCC_of_isCauchyComplete' (M : FlatSpacetime.{u} d) (hGH : GH M)
    (hCC : IsCauchyComplete d M) {x₀ : M} {D : UniversalCover M x₀ → Minkowski d}
    {ρ : Deck (UniversalCover.proj M x₀) →* isom d} (hpair : IsDevelopingPair x₀ D ρ) :
    ∃ S : Set M, DevelopsCC x₀ D S := by
  obtain ⟨S, h⟩ := exists_developsCC_of_isCauchyComplete M hGH hCC x₀
  exact ⟨S, developsCC_iff_bridge.2 (h D hpair.gx)⟩

end Bridge

/-! ## §2 The case split: the common output of §9 and §10 -/

section Cases

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Minkowski d) M]
  [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))] {x₀ : M}
  {D : UniversalCover M x₀ → Minkowski d} {ρ : Deck (UniversalCover.proj M x₀) →* isom d}
  {S : Set M}

/-- **The common output of §9 and §10** (DEC-43 R1): a finite-index `Γ'' ≤ Γ = ρ(Deck)`, a
convex open `Γ''`-invariant `Ω ⊇ 𝒟(M̃)`, the quotient `B = Γ''\Ω`, and `B` an LTP over a model
`M₁` of Theorem A's families, of dimension `≤ d`. -/
def CaseOutput (D : UniversalCover M x₀ → Minkowski d)
    (ρ : Deck (UniversalCover.proj M x₀) →* isom d) : Prop :=
  ∃ Γ : Subgroup (isom d), Γ ≤ ρ.range ∧ Γ.relIndex ρ.range ≠ 0 ∧
    ∃ Ω : Opens (Minkowski d), range D ⊆ Ω ∧ Convex ℝ (Ω : Set (Minkowski d)) ∧
      ∃ B : FlatSpacetime.{0} d, IsQuotientOf B Γ Ω ∧
        ∃ d₁ : ℕ, d₁ ≤ d ∧ ∃ M₁ : FlatSpacetime.{0} d₁, IsModelA M₁ ∧ IsLTPOver B M₁

/-- `Ω(S̃)` is convex (Prop 8.10). -/
theorem convex_omegaS_of_developsCC [T2Space M] (hpair : IsDevelopingPair x₀ D ρ)
    (h : DevelopsCC x₀ D S) :
    Convex ℝ ((omegaSOpens ρ.range (D '' (UniversalCover.proj M x₀ ⁻¹' S)) : Opens _) :
      Set (Minkowski d)) :=
  (bprop_ghyp (ccAction_of_developsCC hpair h)).2.1

/-- **[9.P]–[9.A] with the convexity of `Ω`.** Nonloxodromic's `nonloxodromic_parabolic`, with
`Convex ℝ Ω` added to its conclusion (needed for tameness, `exists_finiteCover_tameEmbedding`). -/
theorem nonloxodromic_parabolic_convex [T2Space M]
    (_hBieb : ∀ k : ℕ, k ≤ d + 1 → BieberbachI (EuclideanSpace ℝ (Fin k)))
    (_hpair : IsDevelopingPair x₀ D ρ) (_hcaus : (flatCausality d M).IsCausal)
    (_h : DevelopsCC x₀ D S) {Γ' : Subgroup (isom d)} (_hle : Γ' ≤ ρ.range)
    (_hidx : Γ'.relIndex ρ.range ≠ 0) (_hnl : ∀ γ ∈ ρ.range, ¬IsLoxodromic (linOf γ))
    {v₀ : Minkowski d} (_hv0 : v₀ ≠ 0) (_hv : minkQ v₀ = 0)
    (_hfix : ∀ γ ∈ Γ', linOf γ v₀ = v₀) (_hpar : ∃ γ ∈ Γ', IsParabolic (linOf γ)) :
    ∃ Γ'' : Subgroup (isom d), Γ'' ≤ Γ' ∧ Γ''.relIndex Γ' ≠ 0 ∧
      ∃ Ω : TopologicalSpace.Opens (Minkowski d), range D ⊆ Ω ∧
        Convex ℝ (Ω : Set (Minkowski d)) ∧
        ∃ B : FlatSpacetime.{0} d, IsQuotientOf B Γ'' Ω ∧
          ∃ d₁ : ℕ, d₁ + 1 ≤ d ∧ ∃ M₁ : FlatSpacetime.{0} (d₁ + 1), IsUnipotentSpacetime M₁ ∧
            IsLTPOver B M₁ := by
  sorry -- SORRY([9.P]–[9.A], convexity): `Flat.Nonloxodromic.nonloxodromic_parabolic` (itself a tagged sorry) exports `range D ⊆ Ω ⊆ Ω(S̃)` but not `Convex ℝ Ω`, and its `Ω` is existential, so the convexity cannot be added after the fact. In its construction (its obstruction (7)) `Ω = π_𝒰⁻¹(Ω_A)` with `Ω_A` a component `{α < y < β}` of `Ω(A)` in `𝒰` (`unipDomain`, a slab between two null hyperplanes, convex) and `π_𝒰` affine, so `Ω` is convex; the export should carry it (finding 1)

/-- **The nonloxodromic case in the common form** (§9, `nonloxodromic` with convexity). -/
theorem caseOutput_nonloxodromic [T2Space M] (hB : BenoistNoLox d)
    (hT : TitsVirtuallyAbelianNull d) (hBieb : ∀ k : ℕ, k ≤ d + 1 → BieberbachI (EuclideanSpace ℝ (Fin k)))
    (hpair : IsDevelopingPair x₀ D ρ) (hcaus : (flatCausality d M).IsCausal)
    (h : DevelopsCC x₀ D S) (hnl : ∀ γ ∈ ρ.range, ¬IsLoxodromic (linOf γ)) :
    CaseOutput D ρ := by
  have hD := (bprop_danom hpair hcaus h).2
  have hcv := convex_omegaS_of_developsCC hpair h
  obtain ⟨Γ₁, hle₁, hidx₁, hcase⟩ := bprop_sanloxo hB hnl
  rcases hcase with ⟨v, hv, hfix⟩ | ⟨v₀, hv0, hv, hfix, hpar | hell⟩
  · obtain ⟨Γ₂, hle₂, hidx₂, B, hB', d₁, hd₁, M₁, hM₁, hltp⟩ :=
      nonloxodromic_elliptic hBieb hpair h hle₁ hidx₁ ⟨v, hv, fun γ hγ => (hfix γ hγ).1⟩
    exact ⟨Γ₂, hle₂.trans hle₁, Subgroup.relIndex_ne_zero_trans hidx₂ hidx₁, _, hD, hcv, B, hB',
      d₁, hd₁, M₁, Or.inl hM₁, hltp⟩
  · obtain ⟨Γ₂, hle₂, hidx₂, Ω, hDΩ, hΩ, B, hB', d₁, hd₁, M₁, hM₁, hltp⟩ :=
      nonloxodromic_parabolic_convex hBieb hpair hcaus h hle₁ hidx₁ hnl hv0 hv hfix hpar
    exact ⟨Γ₂, hle₂.trans hle₁, Subgroup.relIndex_ne_zero_trans hidx₂ hidx₁, Ω, hDΩ, hΩ, B, hB',
      d₁ + 1, hd₁, M₁, Or.inr (Or.inr (Or.inl hM₁)), hltp⟩
  · obtain ⟨Γ₂, hle₂, hidx₂, v, hv', hfix'⟩ :=
      exists_timelike_fixed_of_elliptic_of_null hT (discreteTopology_of_developsCC hpair h hle₁)
        hv0 hv hfix hell
    have hidx₂₁ := Subgroup.relIndex_ne_zero_trans hidx₂ hidx₁
    obtain ⟨Γ₃, hle₃, hidx₃, B, hB', d₁, hd₁, M₁, hM₁, hltp⟩ :=
      nonloxodromic_elliptic hBieb hpair h (hle₂.trans hle₁) hidx₂₁ ⟨v, hv', hfix'⟩
    exact ⟨Γ₃, hle₃.trans (hle₂.trans hle₁), Subgroup.relIndex_ne_zero_trans hidx₃ hidx₂₁, _, hD,
      hcv, B, hB', d₁, hd₁, M₁, Or.inl hM₁, hltp⟩

/-- **The nonelementary loxodromic case in the common form** ([10.G], family (b)). -/
theorem caseOutput_generic [T2Space M] (hA : AuslanderCarriereDalbo d)
    (hU : MaxUnipotentSubspace d) (hpair : IsDevelopingPair x₀ D ρ)
    (hcaus : (flatCausality d M).IsCausal) (h : DevelopsCC x₀ D S)
    (hlox : ∃ γ ∈ ρ.range, IsLoxodromic (linOf γ)) (hne : IsNonelementary ρ.range) :
    CaseOutput D ρ := by
  obtain ⟨Γ', hle, hidx, B, hB', d₁, M₁, hd₁, hltp, hM₁⟩ :=
    loxo_generic_centralExtension hpair hcaus h hlox hne hA hU
  exact ⟨Γ', hle, hidx, _, (bprop_danom hpair hcaus h).2, convex_omegaS_of_developsCC hpair h, B,
    hB', d₁, hd₁, M₁, Or.inr (Or.inr (Or.inr hM₁)), hltp⟩

end Cases

/-- **The elementary loxodromic case in the common form** ([10.M], Misner), in `𝐌^{d'+2}`. -/
theorem caseOutput_misner {d' : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (Minkowski (d' + 1)) M]
    [HasGroupoid M (gxGroupoid (isom (d' + 1)) (Minkowski (d' + 1)))] [T2Space M] {x₀ : M}
    {D : UniversalCover M x₀ → Minkowski (d' + 1)}
    {ρ : Deck (UniversalCover.proj M x₀) →* isom (d' + 1)} {S : Set M}
    (hpair : IsDevelopingPair x₀ D ρ) (hcaus : (flatCausality (d' + 1) M).IsCausal)
    (h : DevelopsCC x₀ D S) (hlox : ∃ γ ∈ ρ.range, IsLoxodromic (linOf γ))
    (helem : ¬IsNonelementary ρ.range) : CaseOutput D ρ := by
  obtain ⟨Γ', hle, hidx, B, hB', d₁, M₁, hd₁, hltp, hM₁⟩ :=
    loxo_elementary_misner hpair hcaus h hlox helem
  exact ⟨Γ', hle, hidx, _, (bprop_danom hpair hcaus h).2, convex_omegaS_of_developsCC hpair h, B,
    hB', d₁ + 1, by omega, M₁, Or.inr (Or.inl hM₁), hltp⟩

/-- **Nothing is hyperbolic in `𝐌¹`**: `IsHyperbolic` asks a unit spacelike `e₁`
(`minkQ e₁ = 1`), and in `Minkowski 0` every vector has `minkQ (t, x) = −t² ≤ 0`. -/
theorem not_isHyperbolic_zero (A : Minkowski 0 ≃ₗ[ℝ] Minkowski 0) : ¬IsHyperbolic A := by
  rintro ⟨e₀, e₁, ζ, -, -, h1, -⟩
  have hx : e₁.2 = 0 := Subsingleton.elim _ _
  simp [minkQ, hx] at h1
  nlinarith [sq_nonneg e₁.1]

/-- **The case split** (BARBOT.md's spine, step 1.4): from (CC′) and the externals, loxodromic or
not (Isometries' classes), then elementary or not. -/
theorem caseOutput {M : Type*} [TopologicalSpace M] [ChartedSpace (Minkowski d) M]
    [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))] [T2Space M] {x₀ : M}
    {D : UniversalCover M x₀ → Minkowski d} {ρ : Deck (UniversalCover.proj M x₀) →* isom d}
    {S : Set M} (hE : BarbotExternals d) (hpair : IsDevelopingPair x₀ D ρ)
    (hcaus : (flatCausality d M).IsCausal) (h : DevelopsCC x₀ D S) : CaseOutput D ρ := by
  by_cases hlox : ∃ γ ∈ ρ.range, IsLoxodromic (linOf γ)
  · by_cases hne : IsNonelementary ρ.range
    · exact caseOutput_generic (hE.auslander d le_rfl) (hE.unipotent d le_rfl) hpair hcaus h
        hlox hne
    · cases d with
      | zero => exact absurd hlox (by
          rintro ⟨γ, -, R, H, -, -, -, hH, -⟩
          exact not_isHyperbolic_zero H hH)
      | succ d' => exact caseOutput_misner hpair hcaus h hlox hne
  · push Not at hlox
    exact caseOutput_nonloxodromic (hE.benoist d le_rfl) (hE.tits d le_rfl) hE.bieberbach hpair
      hcaus h hlox

/-! ## §3 The finite cover and the tame embedding -/

/-- **The finite cover `M' = ρ⁻¹(Γ'')\M̃` tamely embeds in `B = Γ''\Ω`** (l.3586–3592; R1's
"finite cover", DEC-43). -/
theorem exists_finiteCover_tameEmbedding (M : FlatSpacetime.{u} d) {x₀ : M}
    {D : UniversalCover M x₀ → Minkowski d} {ρ : Deck (UniversalCover.proj M x₀) →* isom d}
    (_hpair : IsDevelopingPair x₀ D ρ) (_hinj : Injective D) {Γ : Subgroup (isom d)}
    (_hle : Γ ≤ ρ.range) (_hidx : Γ.relIndex ρ.range ≠ 0) {Ω : Opens (Minkowski d)}
    (_hΩ : range D ⊆ Ω) (_hcv : Convex ℝ (Ω : Set (Minkowski d))) {B : FlatSpacetime.{0} d}
    (_hB : IsQuotientOf B Γ Ω) :
    ∃ (M' : FlatSpacetime.{0} d) (p : M' → M), IsFiniteCover d p ∧
      ∃ f : M' → B, IsTameEmbedding d f := by
  sorry -- SORRY(bthm:caucomp, finite cover): `W := range D` is open (`hpair.gx.isOpenMap`), `Γ`-invariant (equivariance, `Γ ≤ ρ.range`) and `D : M̃ ≃ W`; the candidate is `M' := Γ\W` (`FlatQuotient.toFlatSpacetime`, which needs `ProperlyDiscontinuousSMul Γ W` — the deck group's properness `finite_deck_of_isCompact` transported along the open embedding `D` — and `IsCancelSMul`, from freeness of the deck action), `f := FlatQuotient.quotInclusion Γ (W ≤ Ω)` (an isometric embedding, `isIsometricEmbedding_quotInclusion`, after identifying `B` with `Γ\Ω` by `IsQuotientOf.exists_homeomorph`), and `p : Γ\W → M` induced by `proj ∘ D⁻¹`, a covering with fibres `ρ.range/Γ`, finite by `hidx`. Missing: (1) the descent `M ≃ ρ.range\W` (a covering-space quotient of `M̃` by its deck group, not in the port), (2) the finite-fibre covering `Γ\W → ρ.range\W`, (3) tameness: π₁ of `Γ\X` for `X` simply connected (here `W ≅ M̃`, and `Ω` convex, hence contractible) is `Γ`, and `quotInclusion` induces the identity on it — the library has no computation of π₁ of a quotient by a free properly discontinuous action

/-! ## §4 Theorem A₀ — the embedding layer (G3) -/

/-- **The output of the embedding layer** of Theorem A: a finite cover `M'` of `M` tamely embeds in
`B = Γ\Ω` (`Ω` convex), an LTP over a model `M₁` of dimension `≤ d`. -/
def EmbeddingOutput (M : FlatSpacetime.{u} d) : Prop :=
  ∃ (M' : FlatSpacetime.{0} d) (p : M' → M), IsFiniteCover d p ∧
    ∃ (Γ : Subgroup (isom d)) (Ω : Opens (Minkowski d)), Convex ℝ (Ω : Set (Minkowski d)) ∧
      ∃ B : FlatSpacetime.{0} d, IsQuotientOf B Γ Ω ∧ (∃ f : M' → B, IsTameEmbedding d f) ∧
        ∃ d₁ : ℕ, d₁ ≤ d ∧ ∃ M₁ : FlatSpacetime.{0} d₁, IsModelA M₁ ∧ IsLTPOver B M₁

/-- **Theorem A₀ (G3's first layer: the embedding, without absolute maximality).** Under the
externals (`BarbotExternals d`), a Cauchy-complete GH flat spacetime `M` (any `d`) has a finite
cover `M'` which tamely embeds in an LTP `B` over a model `M₁` (translation, Misner, unipotent,
family (b)) of dimension `≤ d`. Proof: the bridge (`exists_developsCC_of_isCauchyComplete'`), the
case split (`caseOutput`), the finite cover (`exists_finiteCover_tameEmbedding`). -/
theorem barbot_A₀ (hE : BarbotExternals d) (M : FlatSpacetime.{u} d) (hGH : GH M)
    (hCC : IsCauchyComplete d M) : EmbeddingOutput M := by
  obtain ⟨x₀⟩ : Nonempty M := inferInstance
  obtain ⟨D, ρ, hpair⟩ := exists_isDevelopingPair (d := d) x₀
  obtain ⟨S, h⟩ := exists_developsCC_of_isCauchyComplete' M hGH hCC hpair
  have hinj := (bprop_danom hpair hGH.1 h).1
  obtain ⟨Γ, hle, hidx, Ω, hDΩ, hcv, B, hB, d₁, hd₁, M₁, hM₁, hltp⟩ :=
    caseOutput hE hpair hGH.1 h
  obtain ⟨M', p, hp, f, hf⟩ :=
    exists_finiteCover_tameEmbedding M hpair hinj hle hidx hDΩ hcv hB
  exact ⟨M', p, hp, Γ, Ω, hcv, B, hB, ⟨f, hf⟩, d₁, hd₁, M₁, hM₁, hltp⟩

/-- **Theorem A's hypotheses are jointly satisfiable** (kb/0012): at `d = 0`, `𝐌¹` carries every
hypothesis of `barbot_A₀` / `barbot_A` (the externals bundle, GH, Cauchy-completeness). -/
theorem barbot_A_hypotheses_zero : BarbotExternals 0 ∧ GH (FlatSpacetime.minkowskiSpace 0) ∧
    IsCauchyComplete 0 (FlatSpacetime.minkowskiSpace 0) :=
  ⟨barbotExternals_zero, gh_minkowskiSpace, isCauchyComplete_minkowskiSpace⟩

/-! ## §4′ Local isometries: cancellation, descent, transport of GH -/

section Equality

variable {X M N : Type*} [TopologicalSpace X] [ChartedSpace (Minkowski d) X]
  [TopologicalSpace M] [ChartedSpace (Minkowski d) M]
  [TopologicalSpace N] [ChartedSpace (Minkowski d) N]

/-- **Cancelling an isometric embedding on the left**: if `h ∘ f` is a local isometry and `h` an
isometric embedding, `f` is a local isometry. -/
theorem IsLocalIsometry.of_comp_left {f : X → M} {h : M → N} (hh : IsIsometricEmbedding d h)
    (hhf : IsLocalIsometry d (h ∘ f)) : IsLocalIsometry d f := by
  have hfc : Continuous f := hh.isOpenEmbedding.isEmbedding.continuous_iff.2 hhf.1
  obtain ⟨-, hhf'⟩ := isLocalIsometry_iff_eventually.1 hhf
  obtain ⟨-, hh'⟩ := isLocalIsometry_iff_eventually.1 hh.1
  refine isLocalIsometry_iff_eventually.2 ⟨hfc, fun x => ?_⟩
  obtain ⟨g₁, hg₁⟩ := hhf' x
  obtain ⟨g₂, hg₂⟩ := hh' (f x)
  refine ⟨g₂⁻¹ * g₁, ?_⟩
  filter_upwards [hg₁, hfc.continuousAt.eventually hg₂] with y h1 h2
  simp only [comp_apply] at h1
  rw [mul_smul, ← h1, h2, inv_smul_smul]

/-- **Descending a local isometry along a surjective local isometry**: if `q` is a surjective
local isometry and `f ∘ q` a local isometry, `f` is a local isometry. -/
theorem IsLocalIsometry.of_comp_right {q : X → M} {f : M → N} (hq : IsLocalIsometry d q)
    (hqs : Surjective q) (hfq : IsLocalIsometry d (f ∘ q)) : IsLocalIsometry d f := by
  have hfc : Continuous f :=
    (hq.isOpenMap.isQuotientMap hq.continuous hqs).continuous_iff.2 hfq.1
  obtain ⟨-, hfq'⟩ := isLocalIsometry_iff_eventually.1 hfq
  obtain ⟨-, hq'⟩ := isLocalIsometry_iff_eventually.1 hq
  refine isLocalIsometry_iff_eventually.2 ⟨hfc, fun x => ?_⟩
  obtain ⟨z, rfl⟩ := hqs x
  obtain ⟨g₁, hg₁⟩ := hfq' z
  obtain ⟨g₂, hg₂⟩ := hq' z
  refine ⟨g₁ * g₂⁻¹, ?_⟩
  have hA : {w | chartAt (Minkowski d) (f (q z)) (f (q w)) =
      (g₁ * g₂⁻¹) • chartAt (Minkowski d) (q z) (q w)} ∈ 𝓝 z := by
    filter_upwards [hg₁, hg₂] with w h1 h2
    simp only [comp_apply] at h1
    rw [h1, h2, mul_smul, inv_smul_smul]
  filter_upwards [hq.isOpenMap.image_mem_nhds hA] with y hy
  obtain ⟨w, hw, rfl⟩ := hy
  exact hw

end Equality

/-- **GH transports along a surjective isometric embedding** (an isometric homeomorphism):
the causal relations correspond (`IsIsometricEmbedding.rel_iff` on `⊤`), so causality and the
compactness of the diamonds `J(f p, f q) = f(J(p, q))` transport. -/
theorem globallyHyperbolic_of_isIsometricEmbedding_of_surjective {M N : Type*} [TopologicalSpace M]
    [ChartedSpace (Minkowski d) M] [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))]
    [TopologicalSpace N] [ChartedSpace (Minkowski d) N]
    [HasGroupoid N (gxGroupoid (isom d) (Minkowski d))] {f : M → N}
    (hf : IsIsometricEmbedding d f) (hs : Surjective f)
    (hM : (flatCausality d M).GloballyHyperbolic) : (flatCausality d N).GloballyHyperbolic := by
  have hrel : ∀ x y : M, (flatCausality d M).le ⊤ x y ↔ (flatCausality d N).le ⊤ (f x) (f y) :=
    fun x y => (hf.rel_iff ⊤ ⊤ (by rw [Opens.coe_top, Opens.coe_top, image_univ, hs.range_eq])
      x y).1
  refine ⟨fun x y hxy hyx => ?_, fun p q => ?_⟩
  · obtain ⟨x, rfl⟩ := hs x
    obtain ⟨y, rfl⟩ := hs y
    exact congrArg f (hM.1 ((hrel x y).2 hxy) ((hrel y x).2 hyx))
  · obtain ⟨p, rfl⟩ := hs p
    obtain ⟨q, rfl⟩ := hs q
    have heq : (flatCausality d N).diamond ⊤ (f p) (f q) =
        f '' (flatCausality d M).diamond ⊤ p q := by
      ext z
      obtain ⟨z, rfl⟩ := hs z
      rw [Causality.mem_diamond]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨z, Causality.mem_diamond.2 ⟨(hrel p z).2 h1, (hrel z q).2 h2⟩, rfl⟩
      · rintro ⟨w, hw, hwz⟩
        obtain ⟨h1, h2⟩ := Causality.mem_diamond.1 hw
        rw [← hwz]
        exact ⟨(hrel p w).1 h1, (hrel w q).1 h2⟩
    rw [heq]
    exact (hM.2 p q).image hf.1.continuous

/-- **GH of a quotient, in the `IsQuotientOf` form.** The homeomorphism `Φ : Γ\Ω ≃ₜ M₁` of
`IsQuotientOf.exists_homeomorph` is a local isometry (it descends `π = Φ ∘ proj`,
`IsLocalIsometry.of_comp_right`), so ETT's GH of the constructed quotient transports. -/
theorem gh_of_isQuotientOf {M₁ : FlatSpacetime.{u} d} {Γ : Subgroup (isom d)}
    {Ω : Opens (Minkowski d)} [FlatQuotient.Invariant Γ Ω] [ProperlyDiscontinuousSMul Γ Ω]
    [IsCancelSMul Γ Ω] (hq : IsQuotientOf M₁ Γ Ω)
    (hGH : (flatCausality d (FlatQuotient Γ Ω)).GloballyHyperbolic) : GH M₁ := by
  obtain ⟨π, -, hπl, Φ, hΦ⟩ := hq.exists_homeomorph
  have hΦπ : Φ ∘ FlatQuotient.proj _ _ = π := funext hΦ
  have hΦl : IsLocalIsometry d Φ :=
    IsLocalIsometry.of_comp_right (FlatQuotient.isLocalIsometry_proj _ _)
      (FlatQuotient.proj_surjective _ _) (by rw [hΦπ]; exact hπl)
  exact globallyHyperbolic_of_isIsometricEmbedding_of_surjective ⟨hΦl, Φ.injective⟩ Φ.surjective
    hGH

/-- **[11.i], (1) for translation spacetimes: GH in the `IsQuotientOf` form** (Examples'
`gh_translation_frame`, through `gh_of_isQuotientOf`). -/
theorem gh_of_isTranslationSpacetime {M₁ : FlatSpacetime.{u} d} (h : IsTranslationSpacetime M₁) :
    GH M₁ := by
  obtain ⟨φ, Λ, hΛ, hq⟩ := h
  exact gh_of_isQuotientOf hq (gh_translation_frame φ Λ)

/-- **[11.i], (1) for Misner spacetimes on the future wedge: GH in the `IsQuotientOf` form**
(Examples' `gh_misner_frame`, through `gh_of_isQuotientOf`). -/
theorem gh_of_isQuotientOf_misnerWedge {e : ℕ} {M₁ : FlatSpacetime.{u} (e + 1)}
    {φ : isom (e + 1)} {L : AddSubgroup (ℝ × EuclideanSpace ℝ (Fin e))} [BallFinite L]
    (hq : IsQuotientOf M₁ (frameConj φ (misnerGroup L)) (isomImage φ (misnerWedge e))) :
    GH M₁ :=
  gh_of_isQuotientOf hq (gh_misner_frame φ)

/-! ## §5 [11.i] Absolute maximality of the models (G1, G2, G3) -/

section AbsMax

/-- **Cancelling a local isometry on the left, for a continuous map**: if `h ∘ f` and `h` are
local isometries and `f` is continuous, `f` is a local isometry. -/
theorem IsLocalIsometry.of_comp_left_of_continuous {X M N : Type*} [TopologicalSpace X]
    [ChartedSpace (Minkowski d) X] [TopologicalSpace M] [ChartedSpace (Minkowski d) M]
    [TopologicalSpace N] [ChartedSpace (Minkowski d) N] {f : X → M} {h : M → N}
    (hh : IsLocalIsometry d h) (hfc : Continuous f) (hhf : IsLocalIsometry d (h ∘ f)) :
    IsLocalIsometry d f := by
  obtain ⟨-, hhf'⟩ := isLocalIsometry_iff_eventually.1 hhf
  obtain ⟨-, hh'⟩ := isLocalIsometry_iff_eventually.1 hh
  refine isLocalIsometry_iff_eventually.2 ⟨hfc, fun x => ?_⟩
  obtain ⟨g₁, hg₁⟩ := hhf' x
  obtain ⟨g₂, hg₂⟩ := hh' (f x)
  refine ⟨g₂⁻¹ * g₁, ?_⟩
  filter_upwards [hg₁, hfc.continuousAt.eventually hg₂] with y h1 h2
  simp only [comp_apply] at h1
  rw [mul_smul, ← h1, h2, inv_smul_smul]

/-- **[11.i], the lifting of an isometric embedding to the universal covers, and rigidity**
(l.3586–3599, the first step of Barbot's argument for every family). Let `M₁ = Γ\Ω` with `Ω`
convex and nonempty, `f : M₁ → N` a local isometry, and `(𝒟, ρ)` a developing pair of `N`. Then
`f ∘ π : Ω → N` lifts to the universal cover `Ñ` as a local isometry `F` (`Ω` simply connected;
mathlib's `existsUnique_continuousMap_lifts`), and `𝒟 ∘ F` is the restriction to `Ω` of one
`g ∈ Isom(𝐌ⁿ)` (rigidity, `Port.Developing`'s `developing_unique_of_preconnected` through
`IsGXMorphism.eq_of_eventuallyEq`). No injectivity of `f` and no hypothesis on `N` is used. -/
theorem exists_lift_of_isQuotientOf {M₁ : Type*} [TopologicalSpace M₁]
    [ChartedSpace (Minkowski d) M₁] {Γ : Subgroup (isom d)} {Ω : Opens (Minkowski d)}
    (hq : IsQuotientOf M₁ Γ Ω) (hcv : Convex ℝ (Ω : Set (Minkowski d)))
    (hne : (Ω : Set (Minkowski d)).Nonempty) (N : FlatSpacetime.{u} d) {f : M₁ → N}
    (hf : IsLocalIsometry d f) {y₀ : N} {D : UniversalCover N y₀ → Minkowski d}
    {ρ : Deck (UniversalCover.proj N y₀) →* isom d} (hpair : IsDevelopingPair y₀ D ρ) :
    ∃ π : Ω → M₁, IsLocalIsometry d π ∧ Surjective π ∧
      (∀ p q : Ω, π p = π q ↔ ∃ γ ∈ Γ, γ • (p : Minkowski d) = q) ∧
      ∃ F : Ω → UniversalCover N y₀,
        (letI := flatCoverChartedSpace d N y₀; IsLocalIsometry d F) ∧
        UniversalCover.proj N y₀ ∘ F = f ∘ π ∧ ∃ g : isom d, ∀ p : Ω, D (F p) = g • (p : Minkowski d) := by
  obtain ⟨π, -, hπl, hπs, hfib⟩ := hq.quot
  refine ⟨π, hπl, hπs, hfib, ?_⟩
  letI := flatCoverChartedSpace d N y₀
  haveI := hasGroupoid_flatCover (d := d) N y₀
  haveI := locPathConnectedSpace_of_flat d N
  haveI : PathConnectedSpace N := pathConnectedSpace_iff_connectedSpace.2 inferInstance
  haveI : Nonempty Ω := hne.to_subtype
  haveI : ContractibleSpace Ω := hcv.contractibleSpace hne
  haveI : LocPathConnectedSpace Ω := locPathConnectedSpace_of_flat d Ω
  haveI : PreconnectedSpace Ω :=
    Subtype.preconnectedSpace hcv.isPreconnected
  have hcov := isCoveringMap_flatCover_proj d N y₀
  have hpl : IsLocalIsometry d (UniversalCover.proj N y₀) := isLocalIsometry_flatCover_proj y₀
  have hDl : IsLocalIsometry d D := isLocalIsometry_iff_eventually.2 ⟨hpair.gx.1, hpair.gx.2⟩
  have hφl : IsLocalIsometry d (f ∘ π) := hf.comp hπl
  obtain ⟨a₀⟩ := (inferInstance : Nonempty Ω)
  obtain ⟨e₀, he₀⟩ := UniversalCover.proj_surjective (y₀ := y₀) (f (π a₀))
  obtain ⟨F, ⟨-, hF⟩, -⟩ := hcov.existsUnique_continuousMap_lifts ⟨f ∘ π, hφl.continuous⟩
    a₀ e₀ he₀
  have hFl : IsLocalIsometry d F :=
    IsLocalIsometry.of_comp_left_of_continuous hpl F.continuous (by rw [hF]; exact hφl)
  have hvl : IsLocalIsometry d (Subtype.val : Ω → Minkowski d) :=
    (isIsometricEmbedding_subtype_val Ω).1
  obtain ⟨g, hg, -⟩ := developing_unique_of_preconnected (G := isom d) (X := Minkowski d)
    (N := Ω) (D := Subtype.val) (D' := D ∘ F)
    (isLocalIsometry_iff_eventually.1 hvl |> fun h' => ⟨h'.1, h'.2⟩)
    (isLocalIsometry_iff_eventually.1 (hDl.comp hFl) |> fun h' => ⟨h'.1, h'.2⟩)
  exact ⟨F, hFl, hF, g, hg⟩

/-- **[11.i] for a quotient of all of `𝐌ⁿ`, the end of the lifting argument** (l.3616–3618:
`Ω₀ = 𝐌ⁿ`). Every local isometry from a quotient `Γ\𝐌ⁿ` into a flat spacetime `N` is onto — no
global hyperbolicity, completeness or injectivity is needed. Proof: by
`exists_lift_of_isQuotientOf`, `f ∘ π` lifts to `F : 𝐌ⁿ → Ñ` with `𝒟_N ∘ F = g`; so
`σ := F ∘ g⁻¹` is a global section of `𝒟_N`, whose range `{z | σ (𝒟_N z) = z}` is closed (`Ñ`
Hausdorff) and open (`F` is open): it is `Ñ`, which is connected. -/
theorem surjective_of_isQuotientOf_top {M₁ : Type*} [TopologicalSpace M₁]
    [ChartedSpace (Minkowski d) M₁] {Γ : Subgroup (isom d)} (hq : IsQuotientOf M₁ Γ ⊤)
    (N : FlatSpacetime.{u} d) {f : M₁ → N} (hf : IsLocalIsometry d f) : Surjective f := by
  obtain ⟨y₀⟩ : Nonempty N := inferInstance
  obtain ⟨D, ρ, hpair⟩ := exists_isDevelopingPair (d := d) y₀
  obtain ⟨π, -, -, -, F, hFl, hF, g, hg⟩ := exists_lift_of_isQuotientOf hq (by simpa using
    convex_univ) (by simp) N hf hpair
  letI := flatCoverChartedSpace d N y₀
  haveI : T2Space (UniversalCover N y₀) := t2Space_universalCover N y₀
  have hDl : IsLocalIsometry d D := isLocalIsometry_iff_eventually.2 ⟨hpair.gx.1, hpair.gx.2⟩
  set σ : Minkowski d → UniversalCover N y₀ := fun x => F ⟨g⁻¹ • x, trivial⟩
  have hσc : Continuous σ :=
    hFl.continuous.comp ((continuous_const_smul _).subtype_mk _)
  have hrange : range F = {z | σ (D z) = z} := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      change F ⟨g⁻¹ • D (F w), trivial⟩ = F w
      congr 1
      exact Subtype.ext (by rw [hg w, inv_smul_smul])
    · intro hz
      exact ⟨_, hz⟩
  have hclopen : IsClopen (range F) :=
    ⟨by rw [hrange]; exact isClosed_eq (hσc.comp hDl.continuous) continuous_id,
      hFl.isOpenMap.isOpen_range⟩
  have huniv := hclopen.eq_univ ⟨F ⟨0, trivial⟩, mem_range_self _⟩
  haveI := locPathConnectedSpace_of_flat d N
  haveI : PathConnectedSpace N := pathConnectedSpace_iff_connectedSpace.2 inferInstance
  intro z
  obtain ⟨yt, rfl⟩ := UniversalCover.proj_surjective (y₀ := y₀) z
  obtain ⟨w, hw⟩ : yt ∈ range F := huniv ▸ mem_univ yt
  exact ⟨π w, by rw [← hw]; exact (congrFun hF w).symm⟩

/-- **[11.i], translation spacetimes are absolutely maximal among all flat targets** (l.3616–3618),
the lifting argument (`surjective_of_isQuotientOf_top`). -/
theorem absMax_of_isTranslationSpacetime (P : FlatSpacetime.{u} d → Prop)
    {M₁ : FlatSpacetime.{u} d} (h : IsTranslationSpacetime M₁) : AbsMax P M₁ := by
  obtain ⟨φ, Λ, hΛ, hq⟩ := h
  exact fun N _ _ f hf => surjective_of_isQuotientOf_top hq N hf.1

/-- **The deck group acts transitively on the fibres** of the universal cover. -/
theorem UniversalCover.exists_deck_apply_eq {Y : Type*} [TopologicalSpace Y] {y₀ : Y}
    (c c' : UniversalCover Y y₀) (h : UniversalCover.proj Y y₀ c = UniversalCover.proj Y y₀ c') :
    ∃ γ : Deck (UniversalCover.proj Y y₀), γ.1 c = c' := by
  obtain ⟨a, ca⟩ := c
  obtain ⟨b, cb⟩ := c'
  change a = b at h
  subst h
  refine ⟨⟨UniversalCover.leftMulHomeomorph (cb.trans ca.symm), rfl⟩, ?_⟩
  change (⟨a, (cb.trans ca.symm).trans ca⟩ : UniversalCover Y y₀) = ⟨a, cb⟩
  rw [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.trans_refl]

/-- **[11.i], the lift is equivariant** (l.3592–3599: the lift `F : Ω₀ → Ñ` of `f ∘ π` conjugates
the action of `Γ₀` into the deck group of `Ñ`). For `γ ∈ Γ`, `p ↦ F (γ p)` and `F` are two lifts of
`f ∘ π` (`π (γ p) = π p`), so they differ by a deck transformation `δ` (transitivity on the fibres,
`UniversalCover.exists_deck_apply_eq`, and uniqueness of lifts on the connected `Ω`); reading
`D ∘ F = g` on `Ω` through `D ∘ δ = ρ(δ) D` gives `ρ(δ) g = g γ` on the open `Ω`, hence
`ρ(δ) = g γ g⁻¹` (rigidity, `Causal.eq_of_eqOn`). So `g Γ g⁻¹ ≤ ρ(Deck)`. -/
theorem exists_deck_of_lift {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace (Minkowski d) M₁]
    {Γ : Subgroup (isom d)} {Ω : Opens (Minkowski d)}
    (hinv : ∀ γ ∈ Γ, (fun p : Minkowski d => γ • p) '' (Ω : Set (Minkowski d)) = Ω)
    (hcv : Convex ℝ (Ω : Set (Minkowski d))) (hne : (Ω : Set (Minkowski d)).Nonempty)
    (N : FlatSpacetime.{u} d) {f : M₁ → N} {y₀ : N} {D : UniversalCover N y₀ → Minkowski d}
    {ρ : Deck (UniversalCover.proj N y₀) →* isom d} (hpair : IsDevelopingPair y₀ D ρ)
    {π : Ω → M₁} (hfib : ∀ p q : Ω, π p = π q ↔ ∃ γ ∈ Γ, γ • (p : Minkowski d) = q)
    {F : Ω → UniversalCover N y₀} (hFc : Continuous F)
    (hF : UniversalCover.proj N y₀ ∘ F = f ∘ π) {g : isom d}
    (hg : ∀ p : Ω, D (F p) = g • (p : Minkowski d)) {γ : isom d} (hγ : γ ∈ Γ) :
    ∃ δ : Deck (UniversalCover.proj N y₀), ρ δ = g * γ * g⁻¹ ∧
      ∀ p q : Ω, (q : Minkowski d) = γ • (p : Minkowski d) → F q = δ.1 (F p) := by
  haveI : PreconnectedSpace Ω := Subtype.preconnectedSpace hcv.isPreconnected
  have hmem : ∀ p : Ω, γ • (p : Minkowski d) ∈ (Ω : Set (Minkowski d)) := fun p => by
    rw [← hinv γ hγ]; exact ⟨p, p.2, rfl⟩
  set A : Ω → Ω := fun p => ⟨γ • (p : Minkowski d), hmem p⟩ with hA
  have hAc : Continuous A :=
    ((continuous_const_smul γ).comp continuous_subtype_val).subtype_mk _
  have hπA : ∀ p, π (A p) = π p := fun p => ((hfib p (A p)).2 ⟨γ, hγ, rfl⟩).symm
  have hlift : ∀ p, UniversalCover.proj N y₀ (F p) = f (π p) := fun p => congrFun hF p
  obtain ⟨p₀, hp₀⟩ := hne
  obtain ⟨δ, hδ⟩ := UniversalCover.exists_deck_apply_eq (F ⟨p₀, hp₀⟩) (F (A ⟨p₀, hp₀⟩))
    (by rw [hlift, hlift, hπA])
  have hcov := isCoveringMap_flatCover_proj d N y₀
  have hcomp : (fun p => δ.1 (F p)) = F ∘ A :=
    hcov.eq_of_comp_eq (δ.1.continuous.comp hFc) (hFc.comp hAc)
      (funext fun p => by
        simp only [comp_apply]
        rw [proj_deck_apply, hlift, hlift, hπA])
      ⟨p₀, hp₀⟩ hδ
  have hg' : ∀ (x : Minkowski d) (hx : x ∈ (Ω : Set (Minkowski d))), D (F ⟨x, hx⟩) = g • x :=
    fun x hx => hg ⟨x, hx⟩
  refine ⟨δ, ?_, fun p q hq => ?_⟩
  · have h : ρ δ * g = g * γ := by
      refine Causal.eq_of_eqOn Ω.isOpen ⟨p₀, hp₀⟩ fun x hx => ?_
      have h1 := congrFun hcomp ⟨x, hx⟩
      simp only [comp_apply] at h1
      calc (ρ δ * g) • x = ρ δ • D (F ⟨x, hx⟩) := by rw [mul_smul, hg' x hx]
        _ = D (δ.1 (F ⟨x, hx⟩)) := (hpair.equiv δ _).symm
        _ = D (F (A ⟨x, hx⟩)) := by rw [h1]
        _ = g • (γ • x) := hg (A ⟨x, hx⟩)
        _ = (g * γ) • x := (mul_smul g γ x).symm
    rw [← h, mul_inv_cancel_right]
  · have h1 := congrFun hcomp p
    simp only [comp_apply] at h1
    rw [show q = A p from Subtype.ext hq, ← h1]

/-- **[11.i], the end of the lifting argument for a convex `Ω`** (l.3599–3611): with the lift
`F : Ω → Ñ` of `f ∘ π` and `𝒟_N ∘ F = g|Ω` (`exists_lift_of_isQuotientOf`), if the developing
image `𝒟_N(Ñ)` lies in `gΩ`, then `f` is onto. As for `Ω = 𝐌ⁿ`
(`surjective_of_isQuotientOf_top`): `σ := F ∘ g⁻¹ ∘ 𝒟_N : Ñ → Ñ` is defined on all of `Ñ`, and
`range F = {z | σ z = z}` is closed (`Ñ` Hausdorff) and open (`F` is open), so it is `Ñ`. No
injectivity of `𝒟_N` is used. -/
theorem surjective_of_lift_of_range_subset {M₁ : Type*} [TopologicalSpace M₁]
    [ChartedSpace (Minkowski d) M₁] {Ω : Opens (Minkowski d)} (N : FlatSpacetime.{u} d)
    {f : M₁ → N} {y₀ : N} {D : UniversalCover N y₀ → Minkowski d}
    {ρ : Deck (UniversalCover.proj N y₀) →* isom d} (hpair : IsDevelopingPair y₀ D ρ)
    {π : Ω → M₁} {F : Ω → UniversalCover N y₀}
    (hFl : letI := flatCoverChartedSpace d N y₀; IsLocalIsometry d F)
    (hF : UniversalCover.proj N y₀ ∘ F = f ∘ π) {g : isom d}
    (hg : ∀ p : Ω, D (F p) = g • (p : Minkowski d))
    (hsub : range D ⊆ (fun p => g • p) '' (Ω : Set (Minkowski d))) : Surjective f := by
  letI := flatCoverChartedSpace d N y₀
  haveI : T2Space (UniversalCover N y₀) := t2Space_universalCover N y₀
  haveI := locPathConnectedSpace_of_flat d N
  haveI : PathConnectedSpace N := pathConnectedSpace_iff_connectedSpace.2 inferInstance
  have hDl : IsLocalIsometry d D := isLocalIsometry_iff_eventually.2 ⟨hpair.gx.1, hpair.gx.2⟩
  have hmem : ∀ z, g⁻¹ • D z ∈ (Ω : Set (Minkowski d)) := fun z => by
    obtain ⟨p, hp, hpz⟩ := hsub (mem_range_self z)
    rw [← hpz, inv_smul_smul]; exact hp
  set σ : UniversalCover N y₀ → UniversalCover N y₀ := fun z => F ⟨g⁻¹ • D z, hmem z⟩
  have hσc : Continuous σ :=
    hFl.continuous.comp (((continuous_const_smul _).comp hDl.continuous).subtype_mk _)
  have hrange : range F = {z | σ z = z} := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      change F ⟨g⁻¹ • D (F w), _⟩ = F w
      congr 1
      apply Subtype.ext
      change g⁻¹ • D (F w) = (w : Minkowski d)
      rw [hg w, inv_smul_smul]
    · intro hz
      exact ⟨_, hz⟩
  have hclopen : IsClopen (range F) :=
    ⟨by rw [hrange]; exact isClosed_eq hσc continuous_id, hFl.isOpenMap.isOpen_range⟩
  obtain ⟨z₀, -⟩ := UniversalCover.proj_surjective (y₀ := y₀) y₀
  have huniv := hclopen.eq_univ ⟨σ z₀, mem_range_self _⟩
  intro z
  obtain ⟨yt, rfl⟩ := UniversalCover.proj_surjective (y₀ := y₀) z
  obtain ⟨w, hw⟩ : yt ∈ range F := huniv ▸ mem_univ yt
  exact ⟨π w, by rw [← hw]; exact (congrFun hF w).symm⟩

/-! ### [11.i] for Misner spacetimes: the developing image of the target lies in the wedge -/

section MisnerAbsMax

variable {e : ℕ}

theorem nullX_sub' (p q : Minkowski (e + 1)) : nullX (p - q) = nullX p - nullX q := by
  simp only [nullX, Prod.fst_sub, Prod.snd_sub, PiLp.sub_apply]; ring

theorem nullY_sub' (p q : Minkowski (e + 1)) : nullY (p - q) = nullY p - nullY q := by
  simp only [nullY, Prod.fst_sub, Prod.snd_sub, PiLp.sub_apply]; ring

theorem nullZ_sub' (p q : Minkowski (e + 1)) : nullZ (p - q) = nullZ p - nullZ q := by
  ext i; simp [nullZ]

theorem nullX_combo (a b : ℝ) (p q : Minkowski (e + 1)) :
    nullX (a • p + b • q) = a * nullX p + b * nullX q := by
  simp only [nullX, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul]; ring

theorem nullY_combo (a b : ℝ) (p q : Minkowski (e + 1)) :
    nullY (a • p + b • q) = a * nullY p + b * nullY q := by
  simp only [nullY, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul]; ring

/-- The two Misner wedges (`c = 1`: future, `c = −1`: past) are convex. -/
theorem convex_of_mem_iff_null {W : Set (Minkowski (e + 1))} {c : ℝ}
    (hW : ∀ p, p ∈ W ↔ 0 < c * nullX p ∧ c * nullY p < 0) : Convex ℝ W := by
  intro p hp q hq a b ha hb hab
  rw [hW] at hp hq ⊢
  rw [nullX_combo, nullY_combo]
  have key : ∀ u v : ℝ, 0 < u → 0 < v → 0 < a * u + b * v := fun u v hu hv => by
    rcases ha.eq_or_lt with rfl | ha'
    · rw [zero_add] at hab; subst hab; simpa using hv
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' hu) (mul_nonneg hb hv.le)
  refine ⟨?_, ?_⟩
  · have := key _ _ hp.1 hq.1; linarith
  · have := key _ _ (neg_pos.2 hp.2) (neg_pos.2 hq.2); linarith

theorem mem_misnerWedge_iff {p : Minkowski (e + 1)} :
    p ∈ misnerWedge e ↔ 0 < (1 : ℝ) * nullX p ∧ (1 : ℝ) * nullY p < 0 := by
  rw [one_mul, one_mul]; exact mem_omegaPlus_misnerΛ

theorem mem_misnerWedgePast_iff {p : Minkowski (e + 1)} :
    p ∈ misnerWedgePast e ↔ 0 < (-1 : ℝ) * nullX p ∧ (-1 : ℝ) * nullY p < 0 := by
  change nullX p < 0 ∧ 0 < nullY p ↔ _
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem linOf_misnerMap (x : ℝ × EuclideanSpace ℝ (Fin e)) :
    linOf (misnerMap x) = axisBoost x.1 := by
  refine LinearEquiv.ext fun v => ?_
  have h := smul_sub_smul (misnerMap x) v 0
  rw [sub_zero] at h
  rw [← h, misnerMap_smul, misnerMap_smul, map_zero]
  abel

/-- **The Misner boost is loxodromic** (`R = id`, `H` the boost of rapidity `s ≠ 0` in the plane
`(t, x₁)`, frame `e₀ = (1, 0)`, `e₁ = (0, e₁)`). -/
theorem isLoxodromic_axisBoost {s : ℝ} (hs : s ≠ 0) : IsLoxodromic (axisBoost (d := e) s) := by
  refine ⟨1, axisBoost s, (lorentz (e + 1)).one_mem, axisBoost_mem_lorentz s, isElliptic_one,
    ⟨((1 : ℝ), 0), ((0 : ℝ), axisVec e), s, hs, ?_, ?_, ?_, ?_, ?_, ?_⟩, (one_mul _).symm,
    by rw [one_mul, mul_one]⟩
  · simp [minkQ]
  · simp [minkQ, axisVec]
  · simp [minkB]
  · refine axisBoostL_ext ?_ ?_ fun i => ?_
    · simp [axisBoost_apply, axisBoostL_fst]
    · simp [axisBoost_apply, axisBoostL_snd_zero]
    · simp [axisBoost_apply, axisBoostL_snd_succ]
  · refine axisBoostL_ext ?_ ?_ fun i => ?_
    · simp [axisBoost_apply, axisBoostL_fst]
    · simp [axisBoost_apply, axisBoostL_snd_zero]
    · simp [axisBoost_apply, axisBoostL_snd_succ]
  · intro w h0 h1
    have hw1 : w.1 = 0 := by simpa [minkB] using h0
    have hw0 : w.2 0 = 0 := by
      simpa [minkB, axisVec, EuclideanSpace.inner_single_left] using h1
    refine axisBoostL_ext ?_ ?_ fun i => ?_
    · simp [axisBoost_apply, axisBoostL_fst, hw1, hw0]
    · simp [axisBoost_apply, axisBoostL_snd_zero, hw1, hw0]
    · simp [axisBoost_apply, axisBoostL_snd_succ]

/-- An exponential beats a quadratic (a copy of Loxodromic's `exists_nat_add_mul_sq_lt`, which the
built `Loxodromic` olean of this run does not carry). -/
theorem exists_nat_add_mul_sq_lt' {A B C r : ℝ} (hC : 0 < C) (hr : 1 < r) :
    ∃ n : ℕ, A + B * (n : ℝ) ^ 2 < C * r ^ n := by
  have h1 := tendsto_pow_const_div_const_pow_of_one_lt 2 hr
  have h2 := tendsto_pow_atTop_atTop_of_one_lt hr
  have e1 := h1.eventually (gt_mem_nhds (show (0 : ℝ) < C / (2 * (|B| + 1)) by positivity))
  have e2 := h2.eventually (eventually_gt_atTop (2 * (|A| + 1) / C))
  obtain ⟨n, hn1, hn2⟩ := (e1.and e2).exists
  refine ⟨n, ?_⟩
  have hrn : 0 < r ^ n := pow_pos (by linarith) n
  rw [div_lt_iff₀ hrn, div_mul_eq_mul_div, lt_div_iff₀ (by positivity)] at hn1
  rw [div_lt_iff₀ hC] at hn2
  have hB1 : B * (n : ℝ) ^ 2 ≤ |B| * (n : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right (le_abs_self B) (by positivity)
  nlinarith [le_abs_self A, abs_nonneg B, sq_nonneg (n : ℝ)]

theorem misnerMap_pow (x : ℝ × EuclideanSpace ℝ (Fin e)) (n : ℕ) :
    misnerMap x ^ n = misnerMap (n • x) := by
  induction n with
  | zero => rw [pow_zero, zero_smul, misnerMap_zero]
  | succ n ih => rw [pow_succ, succ_nsmul, misnerMap_add, ih]

theorem minkQ_misnerMap_smul_sub (y : ℝ × EuclideanSpace ℝ (Fin e)) (p : Minkowski (e + 1)) :
    minkQ (misnerMap y • p - p) =
      2 * ((Real.exp y.1 - 1) * nullX p) * ((Real.exp (-y.1) - 1) * nullY p) + ‖y.2‖ ^ 2 := by
  rw [minkQ_eq_null, nullX_sub', nullY_sub', nullZ_sub', nullX_misner, nullY_misner, nullZ_misner,
    add_sub_cancel_right]
  ring

/-- **Off the Misner wedges, the boost is not achronal** (the computation behind l.3176–3180 for
`g_{s,w}`, `s ≠ 0`): in the frame `ψ`, a point with `xy > 0` is causally related to its image by a
power of `ψ g_{s,w} ψ⁻¹` (`|g^n p − p|² = 2xy(2 − e^{ns} − e^{−ns}) + n²|w|²`, and an exponential
beats a quadratic, `exists_nat_add_mul_sq_lt`). So the achronal domain lies in `{xy ≤ 0}`. -/
theorem nullX_mul_nullY_nonpos_of_mem_achronalDomain {x : ℝ × EuclideanSpace ℝ (Fin e)}
    (hx : x.1 ≠ 0) (ψ : isom (e + 1)) {p : Minkowski (e + 1)}
    (hp : p ∈ achronalDomain (ψ * misnerMap x * ψ⁻¹)) :
    nullX (ψ⁻¹ • p) * nullY (ψ⁻¹ • p) ≤ 0 := by
  by_contra hcon
  push Not at hcon
  set q := ψ⁻¹ • p with hq
  set P := nullX q * nullY q with hP
  obtain ⟨n, hn⟩ := exists_nat_add_mul_sq_lt' (A := 4 * P) (B := ‖x.2‖ ^ 2)
    (show 0 < 2 * P by linarith)
    (by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (abs_pos.2 hx))
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp only [Nat.cast_zero, pow_zero, mul_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, mul_zero, add_zero] at hn
    linarith
  have h := hp (n : ℤ) (by exact_mod_cast hn0)
  have hpq : p = ψ • q := (smul_inv_smul ψ p).symm
  rw [zpow_natCast, conj_pow, hpq, show (ψ * misnerMap x ^ n * ψ⁻¹) • ψ • q = ψ • (misnerMap x ^ n • q)
    by simp [mul_smul], smul_sub_smul, minkQ_isom_linear, misnerMap_pow,
    minkQ_misnerMap_smul_sub] at h
  rw [Prod.smul_fst, Prod.smul_snd, nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℝ, norm_smul,
    Real.norm_natCast] at h
  set s := x.1
  have hE : Real.exp (↑n * s) * Real.exp (-(↑n * s)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hbound : Real.exp |s| ^ n ≤ Real.exp (↑n * s) + Real.exp (-(↑n * s)) := by
    rw [← Real.exp_nat_mul]
    rcases le_or_gt 0 s with hs | hs
    · rw [abs_of_nonneg hs]; linarith [Real.exp_pos (-(↑n * s))]
    · rw [abs_of_neg hs, mul_neg]; linarith [Real.exp_pos (↑n * s)]
  have hval : 2 * ((Real.exp (↑n * s) - 1) * nullX q) * ((Real.exp (-(↑n * s)) - 1) * nullY q) =
      2 * P * (2 - (Real.exp (↑n * s) + Real.exp (-(↑n * s)))) := by
    rw [hP]; linear_combination (2 * nullX q * nullY q) * hE
  rw [hval] at h
  have hP0 : 0 ≤ 2 * P := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hbound hP0]

/-- **An open set in `{xy ≤ 0}` lies in `{xy < 0}`**: near a point with `xy = 0`, moving along
`±(0, e₁)` (which raises `x` and `y` together) produces `xy > 0`. -/
theorem nullX_mul_nullY_neg_of_isOpen {O : Set (Minkowski (e + 1))} (hO : IsOpen O)
    (h : ∀ q ∈ O, nullX q * nullY q ≤ 0) : ∀ q ∈ O, nullX q * nullY q < 0 := by
  intro q hq
  refine lt_of_le_of_ne (h q hq) fun h0 => ?_
  set σ : ℝ := if 0 ≤ nullX q + nullY q then 1 else -1 with hσdef
  have hσ : 0 ≤ σ * (nullX q + nullY q) := by
    rw [hσdef]; split_ifs with hc
    · linarith
    · push Not at hc; linarith
  have hσ2 : σ ^ 2 = 1 := by rw [hσdef]; split_ifs <;> norm_num
  set u : Minkowski (e + 1) := ((0 : ℝ), axisVec e)
  have hc : Continuous fun t : ℝ => q + (σ * t) • u := by fun_prop
  have ht0 := hc.tendsto 0
  simp only [mul_zero, zero_smul, add_zero] at ht0
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), q + (σ * t) • u ∈ O :=
    (ht0.mono_left nhdsWithin_le_nhds).eventually (hO.mem_nhds hq)
  obtain ⟨t, ht, ht0'⟩ := (hev.and self_mem_nhdsWithin).exists
  have hle := h _ ht
  have hs2 : 0 < √2 := by positivity
  have hX : nullX (q + (σ * t) • u) = nullX q + σ * (t / √2) := by
    simp only [nullX, u, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      PiLp.add_apply, PiLp.smul_apply, axisVec_zero, smul_eq_mul]; ring
  have hY : nullY (q + (σ * t) • u) = nullY q + σ * (t / √2) := by
    simp only [nullY, u, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      PiLp.add_apply, PiLp.smul_apply, axisVec_zero, smul_eq_mul]; ring
  rw [hX, hY] at hle
  have hk : 0 < t / √2 := div_pos ht0' hs2
  nlinarith [mul_nonneg hk.le hσ, sq_pos_of_pos hk]

/-- **[11.i] for Misner spacetimes, absolute maximality** (l.3620–3626), for either wedge
(`c = 1` future, `c = −1` past): every local isometry of `M₁ = φΓφ⁻¹\φW` into a GH Cauchy-complete
`N` is onto. Proof: lift (`exists_lift_of_isQuotientOf`) with `𝒟_N ∘ F = g|φW`; equivariance
(`exists_deck_of_lift`) puts `ψ g_{s,w} ψ⁻¹` (`ψ = gφ`, `s ≠ 0`, F1) in `Γ_N = ρ_N(Deck)`; it is
loxodromic, so `𝒟_N(Ñ) ⊆ Ω(S̃_N)` (Develop's `bprop_danom` under (CC′), the bridge) lies in its
achronal domain (Loxodromic's `omegaS_subset_interior_achronalDomain`), which is `ψ{xy ≤ 0}`;
`𝒟_N(Ñ)` is open, so it lies in `ψ{xy < 0}`, connected and meeting `ψW = gφW`, so it lies in
`gφW`; the end of the lifting argument (`surjective_of_lift_of_range_subset`). This replaces
Barbot's limit-set comparison `Λ(Γ₀) ⊆ Λ(Γ₂)` by the single loxodromic element. -/
theorem surjective_of_isQuotientOf_misner {M₁ : Type*} [TopologicalSpace M₁]
    [ChartedSpace (Minkowski (e + 1)) M₁] [Nonempty M₁] {φ : isom (e + 1)}
    {L : AddSubgroup (ℝ × EuclideanSpace ℝ (Fin e))} {x : ℝ × EuclideanSpace ℝ (Fin e)}
    (hxL : x ∈ L) (hx : x.1 ≠ 0) {W : Opens (Minkowski (e + 1))} {c : ℝ} (hc : c ≠ 0)
    (hW : ∀ p, p ∈ W ↔ 0 < c * nullX p ∧ c * nullY p < 0)
    (hq : IsQuotientOf M₁ (frameConj φ (misnerGroup L)) (isomImage φ W))
    (N : FlatSpacetime.{u} (e + 1)) (hN : GH N) (hCC : IsCauchyComplete (e + 1) N)
    {f : M₁ → N} (hf : IsLocalIsometry (e + 1) f) : Surjective f := by
  have hWcv : Convex ℝ (W : Set (Minkowski (e + 1))) := convex_of_mem_iff_null hW
  have hΩcv : Convex ℝ (isomImage φ W : Set (Minkowski (e + 1))) := convex_isomImage hWcv
  obtain ⟨π₀, -, -, hπs₀, -⟩ := hq.quot
  obtain ⟨m₀⟩ := (inferInstance : Nonempty M₁)
  obtain ⟨p₀, -⟩ := hπs₀ m₀
  have hne : (isomImage φ W : Set (Minkowski (e + 1))).Nonempty := ⟨p₀, p₀.2⟩
  obtain ⟨y₀⟩ : Nonempty N := inferInstance
  obtain ⟨D, ρ, hpair⟩ := exists_isDevelopingPair (d := e + 1) y₀
  obtain ⟨S, hS⟩ := exists_developsCC_of_isCauchyComplete' N hN hCC hpair
  have hDΩ := (bprop_danom hpair hN.1 hS).2
  letI := flatCoverChartedSpace (e + 1) N y₀
  obtain ⟨π, -, -, hfib, F, hFl, hF, g, hg⟩ :=
    exists_lift_of_isQuotientOf hq hΩcv hne N hf hpair
  have hγ : φ * misnerMap x * φ⁻¹ ∈ frameConj φ (misnerGroup L) :=
    Subgroup.mem_map.2 ⟨misnerMap x, mem_misnerGroup.2 ⟨x, hxL, rfl⟩, rfl⟩
  obtain ⟨δ, hδ, -⟩ := exists_deck_of_lift hq.inv hΩcv hne N hpair hfib hFl.continuous hF hg hγ
  set ψ : isom (e + 1) := g * φ with hψ
  have hγ' : ψ * misnerMap x * ψ⁻¹ ∈ ρ.range := ⟨δ, by rw [hδ, hψ]; group⟩
  have hlox : IsLoxodromic (linOf (ψ * misnerMap x * ψ⁻¹)) := by
    rw [linOf_mul, linOf_mul, linOf_inv, linOf_misnerMap]
    exact (isLoxodromic_axisBoost hx).conj (linOf_mem ψ)
  have hach : ∀ z, D z ∈ achronalDomain (ψ * misnerMap x * ψ⁻¹) := fun z =>
    interior_subset (omegaS_subset_interior_achronalDomain hγ' hlox (hDΩ (mem_range_self z)))
  have hDl : IsLocalIsometry (e + 1) D :=
    isLocalIsometry_iff_eventually.2 ⟨hpair.gx.1, hpair.gx.2⟩
  set G : UniversalCover N y₀ → Minkowski (e + 1) := fun z => ψ⁻¹ • D z with hG
  have hGc : Continuous G := (continuous_const_smul _).comp hDl.continuous
  have hO : IsOpen (range G) := ((isOpenMap_smul ψ⁻¹).comp hDl.isOpenMap).isOpen_range
  have hlt := nullX_mul_nullY_neg_of_isOpen hO (by
    rintro _ ⟨z, rfl⟩
    exact nullX_mul_nullY_nonpos_of_mem_achronalDomain hx ψ (hach z))
  set U : Set (Minkowski (e + 1)) := {p | 0 < c * nullX p ∧ c * nullY p < 0}
  set V : Set (Minkowski (e + 1)) := {p | 0 < -c * nullX p ∧ -c * nullY p < 0}
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const (continuous_nullX.const_mul c)).inter
      (isOpen_lt (continuous_nullY.const_mul c) continuous_const)
  have hVo : IsOpen V :=
    (isOpen_lt continuous_const (continuous_nullX.const_mul (-c))).inter
      (isOpen_lt (continuous_nullY.const_mul (-c)) continuous_const)
  have hUV : Disjoint U V := Set.disjoint_left.2 fun p hp hp' => by
    have h1 := hp.1; have h2 := hp'.1; linarith
  have hcov : range G ⊆ U ∪ V := by
    intro p hp
    have hxy := hlt p hp
    have hc2 : 0 < c ^ 2 := by positivity
    have hprod : (c * nullX p) * (c * nullY p) < 0 := by
      have : (c * nullX p) * (c * nullY p) = c ^ 2 * (nullX p * nullY p) := by ring
      rw [this]; exact mul_neg_of_pos_of_neg hc2 hxy
    rcases lt_trichotomy (c * nullX p) 0 with h | h | h
    · right
      refine ⟨by linarith, ?_⟩
      by_contra hy; push Not at hy
      nlinarith
    · rw [h, zero_mul] at hprod; exact absurd hprod (lt_irrefl 0)
    · left
      refine ⟨h, ?_⟩
      by_contra hy; push Not at hy
      nlinarith
  have hconn : IsPreconnected (range G) := isPreconnected_range hGc
  have hpU : G (F p₀) ∈ U := by
    obtain ⟨w, hw, hwp⟩ := (coe_isomImage φ W ▸ p₀.2 : (p₀ : Minkowski (e + 1)) ∈
      (fun p => φ • p) '' (W : Set (Minkowski (e + 1))))
    have : G (F p₀) = w := by
      simp only [hG]
      rw [hg p₀, ← hwp]
      simp [hψ, mul_smul]
    rw [this]; exact (hW w).1 hw
  have hsubU : range G ⊆ U := by
    rcases hconn.subset_or_subset hUo hVo hUV hcov with h | h
    · exact h
    · exact absurd (h (mem_range_self (F p₀))) (Set.disjoint_left.1 hUV hpU)
  refine surjective_of_lift_of_range_subset N hpair hFl hF hg ?_
  rintro _ ⟨z, rfl⟩
  have hz : G z ∈ (W : Set (Minkowski (e + 1))) := (hW _).2 (hsubU (mem_range_self z))
  refine ⟨φ • G z, ?_, ?_⟩
  · rw [coe_isomImage]; exact ⟨G z, hz, rfl⟩
  · simp only [hG]
    rw [← mul_smul, ← mul_smul, hψ, mul_inv_rev, ← mul_assoc, mul_assoc g φ, mul_inv_cancel,
      mul_one, mul_inv_cancel, one_smul]

end MisnerAbsMax

/-! ### [11.i] for regular domains `Ω^±(Λ(Γ))` (family (b)): the developing image of the target -/

section RegularAbsMax

/-- An open set on which `⟨n | ·⟩ ≤ s` (`n = (1, u)` null) has `⟨n | ·⟩ < s`: move along `(−1, 0)`,
which raises `⟨n | ·⟩` at unit speed. -/
theorem minkB_nullVec_lt_of_isOpen {O : Set (Minkowski d)} (hO : IsOpen O) (u : PenroseSphere d)
    (s : ℝ) (h : ∀ p ∈ O, minkB (nullVec u) p ≤ s) : ∀ p ∈ O, minkB (nullVec u) p < s := by
  intro p hp
  refine lt_of_le_of_ne (h p hp) fun h0 => ?_
  have hc : Continuous fun t : ℝ => p + t • ((-1 : ℝ), (0 : EuclideanSpace ℝ (Fin d))) := by
    fun_prop
  have ht0 := hc.tendsto 0
  simp only [zero_smul, add_zero] at ht0
  obtain ⟨t, ht, ht0'⟩ :=
    (((ht0.mono_left nhdsWithin_le_nhds).eventually (hO.mem_nhds hp)).and
      (self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)))).exists
  have := h _ ht
  rw [minkB_nullVec] at this h0
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, smul_zero,
    add_zero] at this
  have ht0'' : (0 : ℝ) < t := ht0'
  linarith

/-- The past version: on an open set, `s ≤ ⟨n | ·⟩` gives `s < ⟨n | ·⟩` (move along `(1, 0)`). -/
theorem lt_minkB_nullVec_of_isOpen {O : Set (Minkowski d)} (hO : IsOpen O) (u : PenroseSphere d)
    (s : ℝ) (h : ∀ p ∈ O, s ≤ minkB (nullVec u) p) : ∀ p ∈ O, s < minkB (nullVec u) p := by
  intro p hp
  refine lt_of_le_of_ne (h p hp) fun h0 => ?_
  have hc : Continuous fun t : ℝ => p + t • ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin d))) := by
    fun_prop
  have ht0 := hc.tendsto 0
  simp only [zero_smul, add_zero] at ht0
  obtain ⟨t, ht, ht0'⟩ :=
    (((ht0.mono_left nhdsWithin_le_nhds).eventually (hO.mem_nhds hp)).and
      (self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)))).exists
  have := h _ ht
  rw [minkB_nullVec] at this h0
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, smul_zero,
    add_zero] at this
  have ht0'' : (0 : ℝ) < t := ht0'
  linarith

theorem continuous_minkB_nullVec_fst (p : Minkowski d) :
    Continuous fun w : PenroseSphere d × ℝ => minkB (nullVec w.1) p := by
  simp only [minkB_nullVec]
  exact continuous_const.add ((continuous_subtype_val.comp continuous_fst).inner continuous_const)

/-- **The quadrant of a loxodromic element of the target's holonomy**, pulled back by `g`: if
`g γ g⁻¹ ∈ ρ_N(Deck)` with `γ` loxodromic (repulsive points `w` of `γ`, `w'` of `γ⁻¹`), then
`g⁻¹ 𝒟_N(Ñ)` lies in one of the two quadrants `P^±(w) ∩ P^±(w')` (Loxodromic's
`omegaS_subset_quadrant` for `Ω(S̃_N)`, conjugated by `g`, `IsRepulsiveFixedJ.conj`). -/
theorem range_subset_quadrant_of_mem_range {N : FlatSpacetime.{u} d} (hN : GH N) {y₀ : N}
    {D : UniversalCover N y₀ → Minkowski d} {ρ : Deck (UniversalCover.proj N y₀) →* isom d}
    {S : Set N} (hpair : IsDevelopingPair y₀ D ρ) (hS : DevelopsCC y₀ D S) {g γ : isom d}
    (hγ : g * γ * g⁻¹ ∈ ρ.range) {w w' : PenroseSphere d × ℝ} (hw : IsRepulsiveFixedJ γ w)
    (hw' : IsRepulsiveFixedJ γ⁻¹ w') :
    (∀ z, g⁻¹ • D z ∈ halfPlus w.1 w.2 ∩ halfPlus w'.1 w'.2) ∨
      (∀ z, g⁻¹ • D z ∈ halfMinus w.1 w.2 ∩ halfMinus w'.1 w'.2) := by
  have hDΩ := (bprop_danom hpair hN.1 hS).2
  have hw'' : IsRepulsiveFixedJ (g * γ * g⁻¹)⁻¹ (isomPenrose g w') := by
    rw [show (g * γ * g⁻¹)⁻¹ = g * γ⁻¹ * g⁻¹ by group]; exact hw'.conj g
  have hP : ∀ (v : PenroseSphere d × ℝ) (p : Minkowski d),
      g⁻¹ • p ∈ halfPlus v.1 v.2 ↔ p ∈ halfPlus (isomPenrose g v).1 (isomPenrose g v).2 :=
    fun v p => by rw [smul_mem_halfPlus_iff, inv_inv]
  have hM : ∀ (v : PenroseSphere d × ℝ) (p : Minkowski d),
      g⁻¹ • p ∈ halfMinus v.1 v.2 ↔ p ∈ halfMinus (isomPenrose g v).1 (isomPenrose g v).2 :=
    fun v p => by rw [smul_mem_halfMinus_iff, inv_inv]
  rcases omegaS_subset_quadrant (ccAction_of_developsCC hpair hS) hγ (hw.conj g) hw'' with h | h
  · exact Or.inl fun z => by
      obtain ⟨h1, h2⟩ := h (hDΩ (mem_range_self z))
      exact ⟨(hP w _).2 h1, (hP w' _).2 h2⟩
  · exact Or.inr fun z => by
      obtain ⟨h1, h2⟩ := h (hDΩ (mem_range_self z))
      exact ⟨(hM w _).2 h1, (hM w' _).2 h2⟩

/-- **[11.i] for a quotient of a future regular domain `Ω⁺(Λ(Γ))`, absolute maximality**
(l.3620–3626, family (b), future case): every local isometry of `M₁ = Γ\Ω⁺(Λ(Γ))` into a GH
Cauchy-complete `N` is onto. Proof: lift (`exists_lift_of_isQuotientOf`, `Ω⁺` convex) with
`𝒟_N ∘ F = g|Ω⁺`; for every loxodromic `γ ∈ Γ`, equivariance (`exists_deck_of_lift`) puts
`gγg⁻¹` in `ρ_N(Deck)`, so `g⁻¹𝒟_N(Ñ)` lies in a quadrant of `γ`
(`range_subset_quadrant_of_mem_range`), the future one because it meets `Ω⁺ ⊆ P⁺(w)`; so
`⟨n_w | ·⟩ < s_w` on `g⁻¹𝒟_N(Ñ)` for every repulsive `w ∈ Λ₀(Γ)`, hence `≤` on the closure
`Λ(Γ)`, hence `<` (the set is open): `g⁻¹𝒟_N(Ñ) ⊆ Ω⁺(Λ(Γ))`, and the end of the lifting argument
(`surjective_of_lift_of_range_subset`). This is Barbot's `Λ(Γ₀) ⊆ Λ(Γ₂) ⇒ Ω(Λ(Γ₂)) ⊆ Ω(Λ(Γ₀))`
(l.3622–3626), read on the repulsive points of `Γ₀` directly. No hypothesis on `Γ` beyond the
quotient is used (with no loxodromic element, `Ω⁺(∅) = 𝐌ⁿ`). -/
theorem surjective_of_isQuotientOf_limitOpensPlus {M₁ : Type*} [TopologicalSpace M₁]
    [ChartedSpace (Minkowski d) M₁] [Nonempty M₁] {Γ : Subgroup (isom d)}
    (hq : IsQuotientOf M₁ Γ (limitOpensPlus Γ)) (N : FlatSpacetime.{u} d) (hN : GH N)
    (hCC : IsCauchyComplete d N) {f : M₁ → N} (hf : IsLocalIsometry d f) : Surjective f := by
  have hcv : Convex ℝ (limitOpensPlus Γ : Set (Minkowski d)) := convex_omegaPlus _
  obtain ⟨π₀, -, -, hπs₀, -⟩ := hq.quot
  obtain ⟨m₀⟩ := (inferInstance : Nonempty M₁)
  obtain ⟨p₀, -⟩ := hπs₀ m₀
  have hne : (limitOpensPlus Γ : Set (Minkowski d)).Nonempty := ⟨p₀, p₀.2⟩
  obtain ⟨y₀⟩ : Nonempty N := inferInstance
  obtain ⟨D, ρ, hpair⟩ := exists_isDevelopingPair (d := d) y₀
  obtain ⟨S, hS⟩ := exists_developsCC_of_isCauchyComplete' N hN hCC hpair
  letI := flatCoverChartedSpace d N y₀
  obtain ⟨π, -, -, hfib, F, hFl, hF, g, hg⟩ := exists_lift_of_isQuotientOf hq hcv hne N hf hpair
  have hDl : IsLocalIsometry d D := isLocalIsometry_iff_eventually.2 ⟨hpair.gx.1, hpair.gx.2⟩
  have hp₀ : g⁻¹ • D (F p₀) = p₀ := by rw [hg p₀, inv_smul_smul]
  -- every repulsive point of `Γ` bounds `g⁻¹ 𝒟_N(Ñ)` strictly
  have hrep : ∀ w ∈ loxRepSet Γ, ∀ z, minkB (nullVec w.1) (g⁻¹ • D z) < w.2 := by
    rintro w ⟨γ, hγ, hw⟩ z
    obtain ⟨δ, hδ, -⟩ := exists_deck_of_lift hq.inv hcv hne N hpair hfib hFl.continuous hF hg hγ
    obtain ⟨w', hw'⟩ := exists_isRepulsiveFixedJ (isLoxodromic_linOf_inv hw.1)
    rcases range_subset_quadrant_of_mem_range hN hpair hS ⟨δ, hδ⟩ hw hw' with h | h
    · exact mem_halfPlus.1 (h z).1
    · exfalso
      have h1 := mem_halfMinus.1 (h (F p₀)).1
      rw [hp₀] at h1
      have h2 := mem_omegaPlus.1 p₀.2 w (subset_closure ⟨γ, hγ, hw⟩)
      linarith
  have hO : IsOpen (range fun z => g⁻¹ • D z) :=
    ((isOpenMap_smul g⁻¹).comp hDl.isOpenMap).isOpen_range
  have hlim : ∀ z, g⁻¹ • D z ∈ (limitOpensPlus Γ : Set (Minkowski d)) := fun z => by
    refine mem_omegaPlus.2 fun w hw => ?_
    have hle : ∀ p ∈ range fun z => g⁻¹ • D z, minkB (nullVec w.1) p ≤ w.2 := by
      rintro _ ⟨z', rfl⟩
      exact closure_minimal (s := loxRepSet Γ)
        (t := {v : PenroseSphere d × ℝ | minkB (nullVec v.1) (g⁻¹ • D z') ≤ v.2})
        (fun v hv => (hrep v hv z').le)
        (isClosed_le (continuous_minkB_nullVec_fst _) continuous_snd) hw
    exact minkB_nullVec_lt_of_isOpen hO w.1 w.2 hle _ (mem_range_self z)
  refine surjective_of_lift_of_range_subset N hpair hFl hF hg ?_
  rintro _ ⟨z, rfl⟩
  exact ⟨g⁻¹ • D z, hlim z, smul_inv_smul g (D z)⟩

/-- **[11.i] for a quotient of a past regular domain `Ω⁻(Λ(Γ))`, absolute maximality** — the time
reversal of `surjective_of_isQuotientOf_limitOpensPlus` (family (b), past case). -/
theorem surjective_of_isQuotientOf_limitOpensMinus {M₁ : Type*} [TopologicalSpace M₁]
    [ChartedSpace (Minkowski d) M₁] [Nonempty M₁] {Γ : Subgroup (isom d)}
    (hq : IsQuotientOf M₁ Γ (limitOpensMinus Γ)) (N : FlatSpacetime.{u} d) (hN : GH N)
    (hCC : IsCauchyComplete d N) {f : M₁ → N} (hf : IsLocalIsometry d f) : Surjective f := by
  have hcv : Convex ℝ (limitOpensMinus Γ : Set (Minkowski d)) := convex_omegaMinus _
  obtain ⟨π₀, -, -, hπs₀, -⟩ := hq.quot
  obtain ⟨m₀⟩ := (inferInstance : Nonempty M₁)
  obtain ⟨p₀, -⟩ := hπs₀ m₀
  have hne : (limitOpensMinus Γ : Set (Minkowski d)).Nonempty := ⟨p₀, p₀.2⟩
  obtain ⟨y₀⟩ : Nonempty N := inferInstance
  obtain ⟨D, ρ, hpair⟩ := exists_isDevelopingPair (d := d) y₀
  obtain ⟨S, hS⟩ := exists_developsCC_of_isCauchyComplete' N hN hCC hpair
  letI := flatCoverChartedSpace d N y₀
  obtain ⟨π, -, -, hfib, F, hFl, hF, g, hg⟩ := exists_lift_of_isQuotientOf hq hcv hne N hf hpair
  have hDl : IsLocalIsometry d D := isLocalIsometry_iff_eventually.2 ⟨hpair.gx.1, hpair.gx.2⟩
  have hp₀ : g⁻¹ • D (F p₀) = p₀ := by rw [hg p₀, inv_smul_smul]
  have hrep : ∀ w ∈ loxRepSet Γ, ∀ z, w.2 < minkB (nullVec w.1) (g⁻¹ • D z) := by
    rintro w ⟨γ, hγ, hw⟩ z
    obtain ⟨δ, hδ, -⟩ := exists_deck_of_lift hq.inv hcv hne N hpair hfib hFl.continuous hF hg hγ
    obtain ⟨w', hw'⟩ := exists_isRepulsiveFixedJ (isLoxodromic_linOf_inv hw.1)
    rcases range_subset_quadrant_of_mem_range hN hpair hS ⟨δ, hδ⟩ hw hw' with h | h
    · exfalso
      have h1 := mem_halfPlus.1 (h (F p₀)).1
      rw [hp₀] at h1
      have h2 := mem_omegaMinus.1 p₀.2 w (subset_closure ⟨γ, hγ, hw⟩)
      linarith
    · exact mem_halfMinus.1 (h z).1
  have hO : IsOpen (range fun z => g⁻¹ • D z) :=
    ((isOpenMap_smul g⁻¹).comp hDl.isOpenMap).isOpen_range
  have hlim : ∀ z, g⁻¹ • D z ∈ (limitOpensMinus Γ : Set (Minkowski d)) := fun z => by
    refine mem_omegaMinus.2 fun w hw => ?_
    have hle : ∀ p ∈ range fun z => g⁻¹ • D z, w.2 ≤ minkB (nullVec w.1) p := by
      rintro _ ⟨z', rfl⟩
      exact closure_minimal (s := loxRepSet Γ)
        (t := {v : PenroseSphere d × ℝ | v.2 ≤ minkB (nullVec v.1) (g⁻¹ • D z')})
        (fun v hv => (hrep v hv z').le)
        (isClosed_le continuous_snd (continuous_minkB_nullVec_fst _)) hw
    exact lt_minkB_nullVec_of_isOpen hO w.1 w.2 hle _ (mem_range_self z)
  refine surjective_of_lift_of_range_subset N hpair hFl hF hg ?_
  rintro _ ⟨z, rfl⟩
  exact ⟨g⁻¹ • D z, hlim z, smul_inv_smul g (D z)⟩

end RegularAbsMax

/-- **[11.i], translation spacetimes are AMGH** (l.3616–3618: `Ω₀ = 𝐌ⁿ`): GH
(`gh_of_isTranslationSpacetime`) and absolute maximality (`absMax_of_isTranslationSpacetime`, the
lifting argument, against all targets) are proved; Cauchy-completeness of the model is the one
tagged `sorry`. -/
theorem amgh_of_isTranslationSpacetime {d₁ : ℕ} (_hE : BarbotExternals d₁)
    (M₁ : FlatSpacetime.{0} d₁) (_h : IsTranslationSpacetime M₁) :
    AMGH (CauchyCompleteClass d₁) M₁ := by
  refine ⟨gh_of_isTranslationSpacetime _h, ?_, absMax_of_isTranslationSpacetime _ _h⟩
  sorry -- SORRY([11.i], translation, Cauchy-completeness): `IsCauchyComplete d₁ M₁` asks a Cauchy surface of `M₁ = Γ\𝐌ⁿ` (`Γ = φ(horizGroup Λ)φ⁻¹`), spacelike Lipschitz in charts, whose glued induced length (`InducedLengthSpace`) is complete and induces the subspace topology. The candidate is the image of the slice `φ{t = 0}` (Examples' `isCauchySurface_translation`, for the constructed quotient; transported along `Φ` of `IsQuotientOf.exists_homeomorph`, a local isometry by `IsLocalIsometry.of_comp_right` as in `gh_of_isTranslationSpacetime`). Missing: (1) spacelike-Lipschitzness of a projected slice in the charts of a quotient (charts of `Γ\Ω` are local inverses of `proj`, `c = 0` in them); (2) the induced length of the quotient slice `Λ\ℝᵈ` as the quotient of the Euclidean length of `ℝᵈ` (the length is defined by gluing chart lengths over paths; no descent lemma along a covering of the surface); (3) its completeness (a quotient of a complete length space by a discrete group of isometries; Examples SCOPE: completeness not stated)

/-- **[11.i], Misner spacetimes are AMGH** (l.3620–3626), with F1's nonzero boost (G2), which is a
field of `IsMisnerSpacetime`. Absolute maximality is proved (`surjective_of_isQuotientOf_misner`,
both wedges; it rests on the bridge only), GH on the future wedge
(`gh_of_isQuotientOf_misnerWedge`); the past wedge's GH and Cauchy-completeness are tagged. -/
theorem amgh_of_isMisnerSpacetime {e : ℕ} (_hE : BarbotExternals (e + 1))
    (M₁ : FlatSpacetime.{0} (e + 1)) (_h : IsMisnerSpacetime M₁) :
    AMGH (CauchyCompleteClass (e + 1)) M₁ := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨φ, L, hL, -, hq | hq⟩ := _h
    · exact gh_of_isQuotientOf_misnerWedge hq
    · sorry -- SORRY([11.i], Misner, GH of the past wedge): `gh_of_isQuotientOf` reduces it to ETT's GH of the constructed quotient `φΓφ⁻¹\φ{xy < 0, x < 0}`; Examples proves GH for the future wedge only (`gh_misner_frame`, through `misnerRegular`, a regular-domain presentation of `misnerWedge`), and has no regular-domain (past) presentation of `misnerWedgePast` to feed `gh_frameConj`. As sets `misnerWedgePast = omegaMinus (misnerΛ d)` (checked by hand: `0 < −t ± x₁` iff `nullX < 0 < nullY`), so `PastRegular.globallyHyperbolicOn` (Penrose) would give the GH of the domain; missing are the other inputs of `gh_frameConj` — `ActsAcausally`, the finiteness of `{γ | x ≤ γ y}`, and the instances `ProperlyDiscontinuousSMul`, `IsCancelSMul` on the past wedge — which Examples derives for the future wedge from the cosmological time of a `CosmoRegular` domain (`actsAcausally_of_preservesOmega`, `finite_le_of_preservesOmega`; future-only), or a `dual` (time-reversal) transport of `gh_frameConj`
  · sorry -- SORRY([11.i], Misner, Cauchy-completeness): `IsCauchyComplete` of `M₁`: the level sets of the cosmological time of the wedge descend to acausal Cauchy surfaces (Examples' `isCauchySurface_misner`, constructed quotient), but their spacelike-Lipschitz property in the quotient charts and the completeness of the induced length of the quotient hyperboloid-like slice are not in the library (Examples SCOPE: completeness not stated)
  · intro N hN hCC f hf
    obtain ⟨φ, L, -, ⟨x, hxL, hx⟩, hq | hq⟩ := _h
    · exact surjective_of_isQuotientOf_misner hxL hx one_ne_zero (fun _ => mem_misnerWedge_iff) hq
        N hN hCC hf.1
    · exact surjective_of_isQuotientOf_misner hxL hx (by norm_num)
        (fun _ => mem_misnerWedgePast_iff) hq N hN hCC hf.1

/-- **[11.i], family (b) is AMGH** (l.3620–3626, "twisted products of Cauchy-hyperbolic spacetimes
by flat torii", in the central-extension form, DEC-44). Absolute maximality is proved
(`surjective_of_isQuotientOf_limitOpensPlus`, `…Minus`; it rests on the bridge only); GH and
Cauchy-completeness are tagged. -/
theorem amgh_of_isCHCentralExtension {d₁ : ℕ} (_hE : BarbotExternals d₁)
    (M₁ : FlatSpacetime.{0} d₁) (_h : IsCHCentralExtension M₁) :
    AMGH (CauchyCompleteClass d₁) M₁ := by
  refine ⟨?_, ?_, ?_⟩
  · sorry -- SORRY([11.i], family (b), GH): `gh_of_isQuotientOf` (proved here) reduces GH of `M₁` in the `IsQuotientOf` form to ETT's GH of the constructed quotient `Γ\Ω^±(Λ(Γ))`, which needs Loxodromic's `bcor_loxo_proper` (future case; resting on `loxo_properlyDiscontinuous`) and the instances `ProperlyDiscontinuousSMul Γ Ω`, `IsCancelSMul Γ Ω` for the central-extension domain — not exported by Loxodromic for `IsCHCentralExtension` (its `Γ` need not be the holonomy of a (CC′) action, so `CCAction` is not available either); the past case `Ω⁻` needs the time reversal (`cosmoRegular_negS`)
  · sorry -- SORRY([11.i], family (b), Cauchy-completeness): `IsCauchyComplete` of `M₁ = Γ\Ω^±(Λ(Γ))`: Loxodromic's `loxo_cauchyComplete` (itself a sorry upstream, and stated for a (CC′) action), plus the descent of a level set of the cosmological time to a spacelike Lipschitz Cauchy surface of the quotient with complete induced length (the same infrastructure the translation and Misner cases lack)
  · intro N hN hCC f hf
    obtain ⟨Γ, E, -, -, -, -, -, -, ⟨hq, -⟩ | ⟨hq, -⟩⟩ := _h
    · exact surjective_of_isQuotientOf_limitOpensPlus hq N hN hCC hf.1
    · exact surjective_of_isQuotientOf_limitOpensMinus hq N hN hCC hf.1

/-- **[11.i] for the unipotent family, with G3** (l.3570–3571, l.3629–3679; G1 is the unbounded
case l.3678–3679): an LTP `B` over a unipotent spacetime `M₁`, presented as the quotient of a
convex `Ω`, tamely embeds in an LTP `B₂` over an **absolutely maximal** unipotent spacetime `M₂`. -/
theorem exists_absMax_unipotent_ltp {e : ℕ} (_hE : BarbotExternals d) (_he : e + 1 ≤ d)
    (M₁ : FlatSpacetime.{0} (e + 1)) (_hU : IsUnipotentSpacetime M₁) (B : FlatSpacetime.{0} d)
    (_hB : IsLTPOver B M₁) {Γ : Subgroup (isom d)} {Ω : Opens (Minkowski d)}
    (_hq : IsQuotientOf B Γ Ω) (_hcv : Convex ℝ (Ω : Set (Minkowski d))) :
    ∃ M₂ : FlatSpacetime.{0} (e + 1), IsUnipotentSpacetime M₂ ∧
      AMGH (CauchyCompleteClass (e + 1)) M₂ ∧
      ∃ B₂ : FlatSpacetime.{0} d, IsLTPOver B₂ M₂ ∧ ∃ g : B → B₂, IsTameEmbedding d g := by
  sorry -- SORRY([11.i] unipotent, G1 + G3): proved upstream: Prop 9.3 (`bprop_limites`, both infinite-extremity cases) and Prop 9.5 (`bprop_extension`, bounded and one-sided: G1 at the level of 9.3/9.5). Missing: (1) G1 proper — the maximal interval `]−Y₊, Y₊[` (`Y₊` the inverse operator norm of `T₀`, l.3657–3664) and its one-sided analogues, the abelian group `A` of `T̂` and the component `Ω = π₁⁻¹(]−Y₊, Y₊[)` of `Ω(A)` (`IsUnipComponent`), so `M₁ ↪ M₂ := Γ₀\Ω` tamely (`quotInclusion`, convex domains); (2) `M₂` absolutely maximal (l.3668–3676): the lift to `Ñ` with rigidity (`exists_lift_of_isQuotientOf`), its equivariance `gΓ₀g⁻¹ ≤ ρ_N(Deck)` (`exists_deck_of_lift`) and the end `𝒟_N(Ñ) ⊆ gΩ ⇒ onto` (`surjective_of_lift_of_range_subset`) are proved here, and the bridge on the target gives `𝒟_N(Ñ) ⊆ Ω(S̃_N)` (as in `surjective_of_isQuotientOf_misner`); what remains is the inclusion `𝒟_N(Ñ) ⊆ gΩ`, i.e. 9.3 for `Γ₁ ⊇ gΓ₀g⁻¹` forcing `π₁(Ω₁) ⊆ ]−Y₊, Y₊[` (no loxodromic element: the quadrant argument of the Misner case is unavailable, and `Ω(S̃_N) ⊆ U(Γ_N)` must be read through the null hyperplanes of the parabolic elements, `Ug` of a linear parabolic), its GH (Examples' `barbotGH_unip`; ETT's GH of the quotient not done upstream) and Cauchy-completeness (`unipcomplet`, l.744–753); (3) G3 — the LTP over `M₂`: `B₂ := Γ\(Ω_{M₂} ⊕ U^⊥)` with `Γ` restricting to `Γ_U` on `U` (`IsLTPData.restricts`), `B ↪ B₂` induced by the inclusion `Ω ⊆ Ω_{M₂} ⊕ U^⊥`; this needs the LTP data of `hB` to be the convex presentation `hq` (both are existential; the statement is nevertheless true as written: `hq`'s `Ω` is convex, and IsLTPOver's domain `Ω_{M₁} ⊕ U^⊥` is convex too (a unipotent slab plus a subspace), so both are simply connected developing images of the universal cover of `B` and agree up to an element of `Isom(𝐌ⁿ)` — uniqueness of the developing pair, not derived here)

end AbsMax

/-! ## §6 Theorem A -/

/-- **Theorem A** (`bthm:caucomp`, l.338–347), in reading R1 (DEC-43), the fourth family in the
central-extension form (b) (DEC-44), absolute maximality for Cauchy-complete targets (DEC-45 (α)).
Under the named externals `BarbotExternals d` — `BenoistNoLox`, `BieberbachI`,
`AuslanderCarriereDalbo`, `MaxUnipotentSubspace`, `TitsVirtuallyAbelianNull` (the last not cited
by Barbot, added 2026-11-01) in every dimension `≤ d` (DEC-36) — every GH,
Cauchy-complete (`IsCauchyComplete`, DEC-35) flat spacetime `M`, in any dimension, has a finite cover
`M'` which tamely embeds in a linear twisted product `B` over a model `M₁` of dimension `d₁ ≤ d`,
`M₁` AMGH in its dimension and a translation, Misner, unipotent spacetime or of family (b).
Assembled from `barbot_A₀` (the embedding), [11.i] (`amgh_of_*`) and G1 + G3
(`exists_absMax_unipotent_ltp`); partial (SCOPE). -/
theorem barbot_A (hE : BarbotExternals d) (M : FlatSpacetime.{u} d) (hGH : GH M)
    (hCC : IsCauchyComplete d M) :
    ∃ (M' : FlatSpacetime.{0} d) (p : M' → M), IsFiniteCover d p ∧
      ∃ (d₁ : ℕ) (_ : d₁ ≤ d) (M₁ : FlatSpacetime.{0} d₁) (B : FlatSpacetime.{0} d),
        AMGH (CauchyCompleteClass d₁) M₁ ∧
        (IsTranslationSpacetime M₁ ∨ IsMisnerFamily d₁ M₁ ∨ IsUnipotentFamily d₁ M₁ ∨
          IsCHCentralExtension M₁) ∧
        IsLTPOver B M₁ ∧ ∃ f : M' → B, IsTameEmbedding d f := by
  obtain ⟨M', p, hp, Γ, Ω, hcv, B, hq, ⟨f, hf⟩, d₁, hd₁, M₁, hM₁, hltp⟩ :=
    barbot_A₀ hE M hGH hCC
  have hE₁ := hE.mono hd₁
  rcases hM₁ with hT | hMis | hU | hCH
  · exact ⟨M', p, hp, d₁, hd₁, M₁, B, amgh_of_isTranslationSpacetime hE₁ M₁ hT, Or.inl hT, hltp,
      f, hf⟩
  · cases d₁ with
    | zero => exact (hMis : False).elim
    | succ e =>
      exact ⟨M', p, hp, e + 1, hd₁, M₁, B, amgh_of_isMisnerSpacetime hE₁ M₁ hMis,
        Or.inr (Or.inl hMis), hltp, f, hf⟩
  · cases d₁ with
    | zero => exact (hU : False).elim
    | succ e =>
      obtain ⟨M₂, hU₂, hamgh, B₂, hltp₂, g, hg⟩ :=
        exists_absMax_unipotent_ltp hE hd₁ M₁ hU B hltp hq hcv
      exact ⟨M', p, hp, e + 1, hd₁, M₂, B₂, hamgh, Or.inr (Or.inr (Or.inl hU₂)), hltp₂, g ∘ f,
        hg.comp hf⟩
  · exact ⟨M', p, hp, d₁, hd₁, M₁, B, amgh_of_isCHCentralExtension hE₁ M₁ hCH,
      Or.inr (Or.inr (Or.inr hCH)), hltp, f, hf⟩

/-! ## §7 Rem 2.3 corrected (DEC-44), [11.ii] (G8) -/

section CauchyCompact

/-- **An embedded compact acausal Cauchy surface is locally Cauchy and two-sided in the target**
(the "spacelike hypersurface" input of lemma K, l.576–578, l.3537–3538). -/
theorem isLocallyCauchyTwoSided_image {M N : FlatSpacetime.{u} d} (_hM : GH M) (_hN : GH N)
    {f : M → N} (_hf : IsIsometricEmbedding d f) {S : Set M}
    (_hS : (flatCausality d M).IsCauchySurface S) (_hac : (flatCausality d M).IsAcausal S) :
    (flatCausality d N).IsLocallyCauchyTwoSided (f '' S) := by
  sorry -- SORRY(clomax, lemma K input): for `x = f s`, the neighbourhood is a domain of dependence: in a flat chart of `N` at `x` inside the open `f(M)`, `S` reads as an acausal graph (Achronal's `isAcausal_graph_iff`), and `LipschitzGraph`'s `graph_subset_interior_dependenceDomain` gives a causally convex open `U ∋ x` (a small domain of dependence of a piece of `f(S)`) with `f(S) ∩ U` Cauchy in `U`; two-sidedness from the splitting of `U` by the graph's time function. Missing: the transport of `S`'s Cauchy property along the local isometry `f` into a chart (only causal convexity of `f⁻¹(U)` is immediate), the local graph form of a topological acausal Cauchy surface (S need not be Lipschitz in a chart: it is achronal there, hence 1-Lipschitz, but strict contraction holds only along `S`), and the domain-of-dependence lemmas for a graph defined on a ball rather than on all of `ℝᵈ` (LipschitzGraph's are for entire graphs)

/-- **Rem 2.3 corrected** (`clomax`, l.571–578; DEC-44): a GH, Cauchy-compact, **maximal** flat
spacetime is absolutely maximal among all GH flat targets, under lemma K's named data on every GH
flat spacetime (`FlatLemmaKData`). Proof: the image `f(S)` of a compact acausal Cauchy surface is
compact, connected (`S × ℝ ≃ₜ M` along `S`) and locally Cauchy two-sided
(`isLocallyCauchyTwoSided_image`), hence Cauchy (lemma K,
`Causality.isCauchySurface_of_isLocallyCauchyTwoSided`), so `f` is a flat Cauchy embedding and
maximality makes it onto. The printed form is false (`Examples.not_cauchyCompact_absMax`). -/
theorem absMax_of_cauchyCompact_of_mgh (hK : ∀ N : FlatSpacetime.{u} d, GH N → FlatLemmaKData N)
    (M : FlatSpacetime.{u} d) (hGH : GH M) (hC : CauchyCompact M) (hM : MGH M) :
    AbsMax (fun _ => True) M := by
  intro N hN _ f hf
  obtain ⟨S, hS, hSc, hSac⟩ := hC
  have hKM := hK M hGH
  have hKN := hK N hN
  -- `S` is connected, through the splitting `S × ℝ ≃ₜ M`
  obtain ⟨ψ, hψ⟩ := Flat.flat_exists_isCauchySplitting hKM.flow hGH.1 hS hSac
  have hSconn : IsConnected S := by
    haveI : ConnectedSpace (S × ℝ) := ψ.symm.surjective.connectedSpace ψ.symm.continuous
    haveI : Nonempty S := by
      obtain ⟨m⟩ : Nonempty M := inferInstance
      exact ⟨(ψ.symm m).1⟩
    haveI : ConnectedSpace S := (Prod.fst_surjective (β := ℝ)).connectedSpace continuous_fst
    simpa using isConnected_range (continuous_subtype_val (p := (· ∈ S)))
  -- a splitting of `N`, from its acausal Cauchy surface and flow
  obtain ⟨S₀, hS₀, hac₀⟩ := hKN.exists_cauchy
  obtain ⟨ψN, hψN⟩ := Flat.flat_exists_isCauchySplitting hKN.flow hN.1 hS₀ hac₀
  have himage : (flatCausality d N).IsCauchySurface (f '' S) :=
    Causality.isCauchySurface_of_isLocallyCauchyTwoSided hKN.tarentin hN hKN.arc hKN.jminus
      hKN.jplus hKN.curvesExtend hψN (hSc.image hf.continuous)
      (hSconn.image f hf.continuous.continuousOn)
      (isLocallyCauchyTwoSided_image hGH hN hf hS hSac)
  exact hM.2 N f (isFlatCauchyEmbedding_iff.2 ⟨hf, hGH, hN, S, hS, himage⟩)

/-- **[11.ii] (G8)** (l.3573–3581): a GH, Cauchy-compact, maximal flat spacetime is not only
embedded in a GH flat spacetime — every isometric embedding of it into one is onto (lemma K in
place of Rem `dependance`, G8). -/
theorem surjective_of_mgh_cauchyCompact
    (hK : ∀ N : FlatSpacetime.{u} d, GH N → FlatLemmaKData N) {M B : FlatSpacetime.{u} d}
    (hGH : GH M) (hC : CauchyCompact M) (hM : MGH M) (hB : GH B) {f : M → B}
    (hf : IsIsometricEmbedding d f) : Surjective f :=
  absMax_of_cauchyCompact_of_mgh hK M hGH hC hM B hB trivial f hf

/-- **A Cauchy-compact GH flat spacetime is Cauchy-complete** (compact ⇒ complete), the
input of Theorem A in Theorem B's proof ("Reconsider the proof above when M is assumed
Cauchy-compact", l.3536). -/
theorem isCauchyComplete_of_cauchyCompact (M : FlatSpacetime.{u} d) (_hGH : GH M)
    (_hC : CauchyCompact M) : IsCauchyComplete d M := by
  sorry -- SORRY(bthm:cauclo, compact ⇒ complete): `CauchyCompact` gives a compact acausal TOPOLOGICAL Cauchy surface, while `IsCauchyComplete` asks a spacelike Lipschitz one (`IsSpacelikeLipschitz`, `c < 1` point-locally in charts) with complete induced length and the topology field. Missing: (1) a spacelike Cauchy surface from a topological one (smoothing, Bernal–Sánchez; or the level set of a Cauchy time function made uniformly spacelike in charts) — not in the library; (2) for a compact spacelike Lipschitz `S`, completeness of `InducedLengthSpace d S` (a compact length space whose pseudo-emetric induces the subspace topology — the gluing of `IsSpacelikeLipschitzIn.isHomeomorph_toSubtype` over charts, CauchyComplete SCOPE)

end CauchyCompact

/-! ## §8 Theorem B -/

/-- **G9 and the identification of Theorem B** (l.3536–3548, l.3573–3581): for `M` maximal
Cauchy-compact GH with the embedding data of Theorem A₀, a finite cover of `M` is a maximal
Cauchy-compact GH spacetime of one of Theorem B's families. -/
theorem cauclo_from_embedding (_hSel : SelbergLemma (Minkowski d))
    (_hK : ∀ N : FlatSpacetime.{0} d, GH N → FlatLemmaKData N) (M : FlatSpacetime.{u} d)
    (_hGH : GH M) (_hC : CauchyCompact M) (_hM : MGH M) {M' : FlatSpacetime.{0} d} {p : M' → M}
    (_hp : IsFiniteCover d p) {Γ : Subgroup (isom d)} {Ω : Opens (Minkowski d)}
    (_hcv : Convex ℝ (Ω : Set (Minkowski d))) {B : FlatSpacetime.{0} d} (_hq : IsQuotientOf B Γ Ω)
    {f : M' → B} (_hf : IsTameEmbedding d f) {d₁ : ℕ} (_hd₁ : d₁ ≤ d) {M₁ : FlatSpacetime.{0} d₁}
    (_hM₁ : IsModelA M₁) (_hltp : IsLTPOver B M₁) :
    ∃ (M₁' : FlatSpacetime.{0} d) (q : M₁' → M), IsFiniteCover d q ∧ IsModelB M₁' ∧ GH M₁' ∧
      CauchyCompact M₁' ∧ MGH M₁' := by
  sorry -- SORRY(bthm:cauclo, G9): the chain of l.3536–3548 and (ii). (1) `M'` is GH, Cauchy-compact and maximal: GH and Cauchy-compactness lift along the finite cover `p` (preimage of a compact Cauchy surface; diamonds), maximality of a finite cover of a maximal CGH spacetime is not stated by the paper (finding 2: a Cauchy extension of `M'` should descend, through the uniqueness of the maximal Cauchy development, gx's CBG, DEC-29); (2) `B` is GH (Prop 8.10/Cor 10.3 for the quotient of `Ω`; not exported by the case theorems, and the statement does not receive `GH B`: it waits on GH of `B`, which follows from `B` being an LTP over a family member once the families' GH in the `IsQuotientOf` form is available — `gh_of_isQuotientOf` here, the same infrastructure the `amgh_*` lemmas lack — and GH transfers along LTPs); then [11.ii] (`surjective_of_mgh_cauchyCompact`, proved here) makes `f` onto, so `f` is a bijective local isometry `M' ≃ B` and `p ∘ f⁻¹ : B → M` a finite cover; (3) G9: in a Cauchy-compact `B`, an LTP over `M₁` is trivial (`d₁ = d`, `U = 𝐌ⁿ`: a nontrivial `U^⊥` makes every Cauchy surface non-compact, `Ω + U^⊥ = Ω`, l.3542–3543), and `M₁` is not unipotent (l.744: `Ω` a slab between null hyperplanes, no compact Cauchy surface of the quotient, l.3546–3548); (4) family (b) to (a): `π₁(M)` finitely generated (compact Cauchy surface; not in the library) and Selberg (`hSel`, `exists_finiteIndex_torsionFree_linOf`) give a further finite cover with torsion-free linear part, i.e. `IsCHTorusProduct`; (5) the composition of finite covers (finite fibres; not in mathlib at this pin)

/-- **Theorem B** (`bthm:cauclo`, l.353–359), "standard" read as Cauchy-compact Cauchy-hyperbolic
(G4), the torus product in its literal form (a) (π₁ finitely generated, Selberg, DEC-44). Under the
named externals `BarbotExternals d`, `SelbergLemma (Minkowski d)` and lemma K's data
`FlatLemmaKData` on every GH flat spacetime of dimension `d` (DEC-36, DEC-44), every maximal
Cauchy-compact GH flat spacetime `M` (any `d`) is finitely covered by an AMGH spacetime `M₁` which
is a translation spacetime, a Misner spacetime, or a Cauchy-compact twisted product (a) of a
standard spacetime by a torus. Assembled from `barbot_A₀`, `cauclo_from_embedding` (G9),
`isCauchyComplete_of_cauchyCompact` and Rem 2.3 corrected (`absMax_of_cauchyCompact_of_mgh`);
partial (SCOPE). -/
theorem barbot_B (hE : BarbotExternals d) (hSel : SelbergLemma (Minkowski d))
    (hK : ∀ N : FlatSpacetime.{0} d, GH N → FlatLemmaKData N) (M : FlatSpacetime.{u} d)
    (hGH : GH M) (hC : CauchyCompact M) (hM : MGH M) :
    ∃ (M₁ : FlatSpacetime.{0} d) (p : M₁ → M), IsFiniteCover d p ∧
      AMGH (CauchyCompleteClass d) M₁ ∧
      (IsTranslationSpacetime M₁ ∨ IsMisnerFamily d M₁ ∨
        (IsCHTorusProduct M₁ ∧ CauchyCompact M₁)) := by
  have hCC := isCauchyComplete_of_cauchyCompact M hGH hC
  obtain ⟨M', p, hp, Γ, Ω, hcv, B, hq, ⟨f, hf⟩, d₁, hd₁, M₁, hM₁, hltp⟩ :=
    barbot_A₀ hE M hGH hCC
  obtain ⟨M₁', q, hq', hmod, hGH', hC', hM'⟩ :=
    cauclo_from_embedding hSel hK M hGH hC hM hp hcv hq hf hd₁ hM₁ hltp
  exact ⟨M₁', q, hq', ⟨hGH', isCauchyComplete_of_cauchyCompact M₁' hGH' hC',
    (absMax_of_cauchyCompact_of_mgh hK M₁' hGH' hC' hM').mono fun _ _ => trivial⟩, hmod⟩

/-! ## §9 The gx export: equality (§11.3) -/


/-- **The gx export, equality** (§11.3, l.3607–3611; `docs/BARBOT-THEOREMS.md` §3, the contract
with gx), `P` parametric (DEC-45): let `(𝒟, ρ)` be a developing pair of a flat spacetime `M`, `𝒟`
injective with image in an open `Ω`, and `B = ρ(Deck)\Ω` a GH flat spacetime of class `P`. If `M` is
absolutely maximal in the class `P`, then `𝒟(M̃) = Ω`. Proof: `𝒟` descends to an isometric
embedding `M → B` (equivariance and injectivity of `𝒟`), which `AbsMax P M` makes onto, and
`𝒟(M̃)` is `ρ(Deck)`-invariant. No `sorry`. -/
theorem equality_of_absMax {P : FlatSpacetime.{u} d → Prop} (M : FlatSpacetime.{u} d) {x₀ : M}
    {D : UniversalCover M x₀ → Minkowski d} {ρ : Deck (UniversalCover.proj M x₀) →* isom d}
    (hpair : IsDevelopingPair x₀ D ρ) (hinj : Injective D) {Ω : Opens (Minkowski d)}
    (hΩ : range D ⊆ Ω) (B : FlatSpacetime.{u} d) (hB : IsQuotientOf B ρ.range Ω) (hGHB : GH B)
    (hPB : P B) (hmax : AbsMax P M) : range D = Ω := by
  letI := flatCoverChartedSpace d M x₀
  haveI := locPathConnectedSpace_of_flat d M
  haveI : PathConnectedSpace M := pathConnectedSpace_iff_connectedSpace.2 inferInstance
  have hqs : Surjective (UniversalCover.proj M x₀) := UniversalCover.proj_surjective
  have hql : IsLocalIsometry d (UniversalCover.proj M x₀) := isLocalIsometry_flatCover_proj x₀
  obtain ⟨π, -, hπl, -, hfib⟩ := hB.quot
  -- `𝒟` as a map into `Ω`
  set D' : UniversalCover M x₀ → Ω := fun z => ⟨D z, hΩ (mem_range_self z)⟩
  have hDl : IsLocalIsometry d D := isLocalIsometry_iff_eventually.2 ⟨hpair.gx.1, hpair.gx.2⟩
  have hD'l : IsLocalIsometry d D' :=
    IsLocalIsometry.of_comp_left (isIsometricEmbedding_subtype_val Ω) hDl
  -- the descended map
  set f : M → B := fun x => π (D' (surjInv hqs x))
  have key : ∀ z, f (UniversalCover.proj M x₀ z) = π (D' z) := by
    intro z
    set z' := surjInv hqs (UniversalCover.proj M x₀ z)
    obtain ⟨γ, hγ⟩ := UniversalCover.exists_deck_apply_eq z z'
      (surjInv_eq hqs (UniversalCover.proj M x₀ z)).symm
    refine ((hfib (D' z) (D' z')).2 ⟨ρ γ, ⟨γ, rfl⟩, ?_⟩).symm
    simp only [D']
    rw [← hpair.equiv, hγ]
  have hfq : f ∘ (UniversalCover.proj M x₀) = π ∘ D' := funext key
  have hfl : IsLocalIsometry d f := hql.of_comp_right hqs (hfq ▸ hπl.comp hD'l)
  have hfi : Injective f := by
    intro x x' hxx'
    obtain ⟨z, rfl⟩ := hqs x
    obtain ⟨z', rfl⟩ := hqs x'
    rw [key, key] at hxx'
    obtain ⟨_, ⟨γ, rfl⟩, hγ⟩ := (hfib _ _).1 hxx'
    have h1 : D (γ.1 z) = D z' := by rw [hpair.equiv]; exact hγ
    rw [← hinj h1]
    exact (proj_deck_apply γ z).symm
  have hfs := hmax B hGHB hPB f ⟨hfl, hfi⟩
  refine Subset.antisymm hΩ fun p hp => ?_
  obtain ⟨x, hx⟩ := hfs (π ⟨p, hp⟩)
  obtain ⟨z, rfl⟩ := hqs x
  rw [key] at hx
  obtain ⟨_, ⟨γ, rfl⟩, hγ⟩ := (hfib _ _).1 hx
  exact ⟨γ.1 z, by rw [hpair.equiv]; exact hγ⟩

/-- **Equality for `Ω(S̃)`** (§11.3 with Develop's §8): under (CC′), if `M(S) = Γ\Ω(S̃)` is a GH
flat spacetime of class `P` and `M` is absolutely maximal in `P`, then `𝒟(M̃) = Ω(S̃)`. -/
theorem range_eq_omegaS_of_absMax {P : FlatSpacetime.{u} d → Prop} (M : FlatSpacetime.{u} d)
    {x₀ : M} {D : UniversalCover M x₀ → Minkowski d}
    {ρ : Deck (UniversalCover.proj M x₀) →* isom d} {S : Set M} (hpair : IsDevelopingPair x₀ D ρ)
    (hcaus : (flatCausality d M).IsCausal) (h : DevelopsCC x₀ D S) (B : FlatSpacetime.{u} d)
    (hB : IsQuotientOf B ρ.range (omegaSOpens ρ.range (D '' (UniversalCover.proj M x₀ ⁻¹' S))))
    (hGHB : GH B) (hPB : P B) (hmax : AbsMax P M) :
    range D = omegaS ρ.range (D '' (UniversalCover.proj M x₀ ⁻¹' S)) :=
  equality_of_absMax M hpair (bprop_danom hpair hcaus h).1 (bprop_danom hpair hcaus h).2 B hB
    hGHB hPB hmax

end Causal.Flat
