import Causal.Flat.Nonloxodromic
import Causal.Flat.TitsNull
import Causal.Flat.Loxodromic
import Causal.CompactCauchy
import Causal.CurvesExtend
import Causal.Flat.Cla.LTPConvex
import Causal.Flat.Cla.FiniteCover
import Causal.Flat.Cla.TameNested
import Causal.Flat.Cla.RegularComplete
import Causal.Flat.Cla.UnipEnvelope
import Causal.Flat.Cla.UnipComplete
import Causal.Flat.Cla.LTPEnlarge
import Causal.Flat.Cla.LocallyCauchy
import Causal.Flat.Cla.CompactComplete
import Causal.Flat.Cla.CoverMGH
import Causal.Flat.Cla.G9
import Causal.Flat.Cla.CoverComp

/-!
# `Causal.Flat.Classification` — Barbot §11: Theorems A and B, absolute maximality

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §11
"Summary of the proof" (`sumup`, `GHFspace.tex` l.3477–3679) and the two theorems it assembles.
Labels certified (line in `papers/barbot/legacy/labeled/GHFspace.tex`), **under named external
hypotheses, disclosed** (DEC-72; the paper cites them, DEC-36; checklist below):

* **`bthm:caucomp`** — `GHFspace.tex:338` (Theorem A: `barbot_A`, reading R1, DEC-43, through
  the layering G3 `barbot_A₀` (embedding) → [11.i] → `barbot_A`)
* **`bthm:cauclo`** — `GHFspace.tex:353` (Theorem B: `barbot_B`, "standard" read as Cauchy-compact
  Cauchy-hyperbolic, G4; with lemma K's data `hK` discharged, `barbot_B_geroch` in
  `Flat/GerochFlat.lean`, DEC-65)

**Both are sorry-free** (re-derived 2026-11-02: `#print axioms` of `barbot_A`, `barbot_A₀`,
`barbot_B`, `barbot_B_geroch` gives `[propext, Classical.choice, Quot.sound]`). ⚠ strengthened:
they rest on the named externals `BarbotExternals d` — Benoist (`BenoistNoLox`), Bieberbach I
(`BieberbachI`), Auslander–Carrière–Dal'bo (`AuslanderCarriereDalbo`), Carrière–Dal'bo
(`MaxUnipotentSubspace`) — and, for B, `SelbergLemma (Minkowski d)`, each witnessed at `d = 0`
(`barbot_A_hypotheses_zero`, `barbot_B_hypotheses_satisfiable`, `barbot_B_zero_geroch`). This
file has no `sorry`, and no `sorry` lies beneath A or B (SCOPE, "No sorry leaf"). Two components
of the bundle are now **proved** (2026-11-03): Bieberbach I (`bieberbachI`, `Flat/BieberbachProof`,
DEC-110) and Benoist (`benoistNoLox`, `Flat/GromovProof`, DEC-111, by Gromov's classification on
`ℍᵈ`, no Zariski closure); `Flat/GromovProof`'s `barbot_A_min`, `barbot_B_min`,
`barbot_B_geroch_min` are A and B with only `AuslanderCarriereDalbo` and `MaxUnipotentSubspace`
(`BarbotExternalsMin d`) and, for B, `SelbergLemma` — this file's statements are unchanged;
`docs/BARBOT-DEPENDENCIES.md` (snapshot 2026-11-01 22:05Z, three leaves) predates the closures.

* Prose: [11.i] absolute maximality (`maxi`, l.3563–3679): `amgh_of_isTranslationSpacetime`,
  `amgh_of_isMisnerSpacetime` (F1's nonzero boost is in `IsMisnerSpacetime`, G2),
  `amgh_of_isCHCentralExtension`, and G1 + G3 for the unipotent family
  (`exists_absMax_unipotent_ltp`). **Proved, no `sorry`:** every [11.i] statement —
  translation spacetimes are AMGH (`amgh_of_isTranslationSpacetime`, Cauchy-completeness through
  `isCauchyComplete_of_isQuotientOf_frameHoriz`), **Misner spacetimes and family (b) are AMGH**
  (Cauchy-completeness by plan lemma L4, `Cla.isCauchyComplete_of_isQuotientOf_regular`, both
  time orientations), and **G1 + G3 for the unipotent family** (`exists_absMax_unipotent_ltp`:
  convex LTP data L1, the corrected maximal envelope L5, its GH and Cauchy-completeness L6, the
  enlarged LTP L7, tameness L3); the finite cover and its tame embedding
  (`exists_finiteCover_tameEmbedding`, L2 + L3); the convexity of the parabolic `Ω`
  (`nonloxodromic_parabolic_convex`, L1, no `sorry` of its own); lemma K's input
  (`isLocallyCauchyTwoSided_image`, L8); the lifting of an isometric embedding
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
  `gh_of_isQuotientOf_misnerWedge`, `…_misnerWedgePast`, `gh_of_isQuotientOf_limitOpensPlus`,
  `…Minus`: every family but the unipotent one, both time orientations); [11.ii] (l.3573–3581): `surjective_of_mgh_cauchyCompact` (G8);
  Rem 2.3 `clomax` corrected (DEC-44, l.571–578): `absMax_of_cauchyCompact_of_mgh`, through lemma K
  (`Causality.isCauchySurface_of_isLocallyCauchyTwoSided`) under its named hypotheses
  (`FlatLemmaKData`); G9 (l.3542–3548): `cauclo_from_embedding`, assembled from L10, L11, L12,
  **no `sorry`, none beneath** (GH of `B` over a family-(b) base through Benoist, `hE`, finding
  11).
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
| A/B: external group theory (Benoist, Bieberbach, Auslander–Carrière–Dal'bo, Carrière–Dal'bo, cited; Tits, not cited) | ⚠ strengthened: named externals, bundled in `BarbotExternals d` (DEC-36; the labels are marked under them, DEC-72): `BenoistNoLox k`, `BieberbachI (ℝᵏ)` (`k ≤ d + 1`), `AuslanderCarriereDalbo k`, `MaxUnipotentSubspace k` for `k ≤ d`. **The Bieberbach component is now proved** (DEC-110, 2026-11-03): `bieberbachI` of `Flat/BieberbachProof`, through virtual abelianity; that module states `BarbotExternalsNoBieb d` (the bundle without it, `barbotExternals_iff_noBieb`) and `barbot_A_noBieb`, `barbot_B_noBieb`, `barbot_B_geroch_noBieb` (this file's statements are unchanged). **The Benoist component is now proved** (DEC-111, 2026-11-03): `benoistNoLox d` of `Flat/GromovProof`, every `d`, by Gromov's classification on `ℍᵈ` (bounded orbit ⇒ fixed timelike vector; unbounded ⇒ fixed nonzero null vector), with no discreteness, no finite generation and no Zariski closure, so it discharges both of this file's uses — the possibly indiscrete `L(Γ)` of `caseOutput_nonloxodromic` and the family-(b) loxodromic element of `exists_loxodromic_of_not_hasGlobalFixedPoint` (findings 7, 11); that module states `BarbotExternalsNoBenoist d`, `BarbotExternalsMin d` (Auslander–Carrière–Dal'bo and Carrière–Dal'bo only; `barbotExternals_iff_min`) and `barbot_A_min`, `barbot_B_min`, `barbot_B_geroch_min` (and the `_noBenoist` forms). [10.M] (`loxo_elementary_misner`, Loxodromic) carries `hBieb : ∀ k ≤ d' + 1 + 1, BieberbachI (ℝᵏ)` (2026-11-01: its statement implies Bieberbach I), which `caseOutput` supplies from `BarbotExternals.bieberbach`: no hypothesis beyond the bundle. **Tits (not cited by Barbot) is no longer a hypothesis** (DEC-50, 2026-11-01): the branch l.2621–2622 overlooks (null `v₀` fixed, all elliptic; Nonloxodromic's DEC-27 statement change of `exists_timelike_fixed_of_elliptic_of_null`, the printed §9 lemma being false for `d ≥ 5`) consumes `TitsVirtuallyAbelianNull d`, which is **supplied** by `Flat/TitsNull`'s `titsVirtuallyAbelianNull d` at the one use site (`caseOutput`) — proved there; TitsNull is now sorry-free (`exists_commute_screenRot_of_discrete`, the Auslander/Cartan local step, is closed upstream; re-derived by the integrator pass of 2026-11-01), so Theorems A/B inherit no `sorry` through it. The `tits` field added to `BarbotExternals` earlier on 2026-11-01 is removed, so A/B carry one hypothesis fewer than in that interim version and exactly the Barbot-cited bundle; their conclusions are unchanged. Non-vacuity: `barbotExternals_zero` (the bundle at `d = 0`, from the components' witnesses), so Theorem A's hypotheses are jointly satisfiable (`barbot_A_hypotheses_zero`: the bundle, GH and Cauchy-completeness of `𝐌¹`). For `d ≥ 1` the bundle is consistent on the cited literature only (Bieberbach in `ℝ^{k ≥ 2}`, Benoist, Auslander–Carrière–Dal'bo, Carrière–Dal'bo); no component is trivially true or false (each has a not-trivially-true witness in `Externals`/`Bieberbach`; `AuslanderCarriereDalbo`'s `DiscreteTopology Γ` is read in `isomTopology`, not in the discrete topology) |
| B: `M` maximal Cauchy-compact GH | ✓ carried: `GH M`, `CauchyCompact M`, `MGH M` |
| B: π₁ finitely generated ⇒ family (a) (DEC-44, Selberg) | ⚠ strengthened: named external `SelbergLemma (Minkowski d)`, consumed by G9's step family (b) → (a) (`Cla.exists_modelB_cover_of_isLTPOver_cauchyCompact`, through `cauclo_from_embedding`); discharged at `d = 0` (`selbergLemma_minkowski_zero`, TheoremBInputs) |
| B: "closed spacelike hypersurfaces are Cauchy" (l.3537–3540, asserted) | ✓ **discharged** in `barbot_B_geroch` (`Flat/GerochFlat.lean`, DEC-65). `barbot_B` itself carries lemma K's named data `FlatLemmaKData` on **every** GH flat target of dimension `d` (`hK`, DEC-44): tarentin, causal arc-connectedness, `J^±(p) ≠ {p}`, `CurvesExtend`, a chronal causal flow, an acausal Cauchy surface. Six fields hold on every flat spacetime and `hK` is equivalent to `FlatGerochGH d` (`forall_flatLemmaKData_iff`, TheoremBInputs), which GerochFlat proves sorry-free (`flatGerochGH`: admissible measures on every GH flat spacetime, then ETT's `geroch_i_imp_iii`); `barbot_B_geroch` is `barbot_B` with `hK` so discharged. The flow field is redundant (`Flat.flat_hasChronalCausalFlow`, Splitting, every `FlatSpacetime`, DEC-49) and kept so that `barbot_B`'s statement does not change; `flatLemmaKData_minkowskiSpace` is the pointwise instance on `𝐌ⁿ` |
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
  where `CauchyCompact` of the product carries G4: it is equivalent (the torus fibre being
  compact; not proved here) to the Cauchy-hyperbolic base being standard, exactly
  BARBOT-THEOREMS §2. `IsStandard` states G4 for a spacetime and is not used by the statements
  (the library builds no base spacetime of a torus product to apply it to).
* **Lemma K's data is universal, and discharged.** `barbot_B`,
  `absMax_of_cauchyCompact_of_mgh` and `surjective_of_mgh_cauchyCompact` carry
  `hK : ∀ N, GH N → FlatLemmaKData N`; it cannot be narrowed to the targets used, because absolute
  maximality quantifies over every GH target. The universal form is proved, sorry-free, in
  `Flat/GerochFlat.lean` (DEC-65: `flatGerochGH` through TheoremBInputs'
  `forall_flatLemmaKData_iff`; GerochFlat imports this file, so it cannot be used here), and
  `barbot_B_geroch` is `barbot_B` with `hK` discharged: the certified Theorem B carries
  `BarbotExternals d` and `SelbergLemma (Minkowski d)` only. `FlatLemmaKData.flow` is redundant
  (`Flat.flat_hasChronalCausalFlow`, Splitting's target 4, every `FlatSpacetime`; kept: no
  statement change), and `flatLemmaKData_minkowskiSpace` is the pointwise instance on `𝐌ⁿ`.
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
  and the non-vacuity witnesses `barbotExternals_zero`, `barbot_A_hypotheses_zero`. Closer pass 2
  (2026-11-01): the instances of a presentation (`isCancelSMul_of_isCoveringMap`,
  `properlyDiscontinuousSMul_of_isCoveringMap`, `IsQuotientOf.isCancelSMul`,
  `IsQuotientOf.properlyDiscontinuousSMul`); GH of the past Misner wedge
  (`gh_of_isQuotientOf_misnerWedgePast`: `actsAcausally_misnerPast`, `finite_le_misnerPast`,
  `globallyHyperbolicOn_misnerWedgePast`, by direct computation in null coordinates); the
  Cauchy-completeness of translation spacetimes (`isCauchyComplete_of_isQuotientOf_frameHoriz`:
  `frameSlice`, `sliceProj`, `exists_lift_sliceProj`, `edist_sliceProj_le`,
  `exists_sliceProj_edist_lt`); GH of family (b) (`exists_loxodromic_of_not_hasGlobalFixedPoint`,
  `gh_of_isQuotientOf_limitOpensPlus`, and on the past side, by the time reversal `timeRev` /
  `revConj`, `gh_of_isQuotientOf_limitOpensMinus`).
* **Plan lemmas (integrator pass, 2026-11-01).** Twelve audited modules `Flat/Cla/*` are
  imported and close seven of the eight former `sorry`s of this file, no statement changed (the
  eighth, GH of `B` over family (b) in `cauclo_from_embedding`, is closed by threading Benoist,
  below):
  L1 `Cla.LTPConvex` (convex LTP data; every presentation carrying a preconnected invariant set
  is convex) → `nonloxodromic_parabolic_convex`, `exists_absMax_unipotent_ltp`; L2
  `Cla.FiniteCover` + L3 `Cla.TameNested` → `exists_finiteCover_tameEmbedding`; L4
  `Cla.RegularComplete` (`bcor:level_sets_complete`, Prop 4.14 descended) →
  `amgh_of_isMisnerSpacetime`, `amgh_of_isCHCentralExtension`; L5 `Cla.UnipEnvelope`, L6
  `Cla.UnipComplete`, L7 `Cla.LTPEnlarge` → `exists_absMax_unipotent_ltp`; L8
  `Cla.LocallyCauchy` → `isLocallyCauchyTwoSided_image`; L9 `Cla.CompactComplete` →
  `isCauchyComplete_of_cauchyCompact` (its smoothing step
  `exists_isSpacelikeLipschitz_of_isCompact_cauchy` is now sorry-free: the cap envelope of
  `Cla.SmoothCap` / `Cla.SmoothGlue`, zero sets of cone-increasing functions `Cla.SmoothCone`, a
  connected component `Cla.CCComponent`); L10 `Cla.CoverMGH` (`maximal_of_isFiniteCover`,
  finding 2, now sorry-free: `Cla.CoverMax`'s `cover_maximal_of_isFiniteCover`), L11 `Cla.G9`
  (`false_of_cauchyCompact_of_fixed_pair`, the residual elementary-loxodromic pair case of G9d's
  (NE), to which `fg_and_nonelementary_of_cauchyCompact` reduces, now sorry-free through
  `Cla.G9Pair`, `Cla.G9PairLin`), L12 `Cla.CoverComp` → `cauclo_from_embedding`.
* **No `sorry` is left in this file** (2026-11-01). The last one was `cauclo_from_embedding`'s
  family-(b) branch of `GH B`: GH of `Γ₁\Ω^±(Λ(Γ₁))` needs a loxodromic element of `Γ₁`, which
  Def 4.18's "no global fixed point" yields only through Benoist (`BenoistNoLox d₁`). It is
  closed by threading the externals down from `barbot_B`: the **internal** lemma
  `cauclo_from_embedding` now takes `hE : BarbotExternals d` as its first argument (a signature
  change of an internal lemma; its one call site is `barbot_B`, which already carries `hE`), and
  the branch is `amgh_of_isCHCentralExtension (hE.mono hd₁)`'s GH component, lifted by
  TwistedProduct's `gh_of_isLTPOver`. `barbot_A`'s and `barbot_B`'s statements are unchanged.
* **No sorry leaf** of `barbot_A`, `barbot_A₀`, `barbot_B`, `barbot_B_geroch`,
  `barbot_B_zero_geroch` (re-derived 2026-11-02 by `#print axioms` against the current oleans:
  `[propext, Classical.choice, Quot.sound]` for each; re-derive at graduation). The leaves of the
  2026-11-01 closure walk are closed upstream, no statement of A or B changed:
  `loxo_elementary_misner` ([10.M], Loxodromic; the second null direction `Lox.fix_second_null`,
  `Lox/SecondNullFix`, then the Misner identification `Lox/MisnerFrame`, `MisnerLimitSet`,
  `MisnerBieberbach`, `MisnerRestrict`), `bprop_LU_discrete` (the branch `L_U(Γ_nd) = {1}` of
  [10.G], `Lox/ClosedSubgroupNhds`), the smoothing step
  `Cla.exists_nonempty_isSpacelikeLipschitz_succ` (`Cla.SmoothCap`, `Cla.SmoothGlue`),
  `Cla.maximal_of_isFiniteCover` (`Cla.CoverMax`, no CBG) and
  `Cla.false_of_cauchyCompact_of_fixed_pair` (`Cla.G9Pair`, `Cla.G9PairLin`). Earlier closed:
  Nonloxodromic ([9.U], [9.E], [9.A]; `Nonlox/*`), TitsNull (`titsVirtuallyAbelianNull`), [10.G]
  (`loxo_generic_centralExtension`, `Lox/*`), Develop (`ccAction_of_developsCC`, `bprop_danom`),
  Splitting's target 4 and CauchyComplete's `exists_splitting_of_isCauchySurface`. So A rests on
  Classification, Loxodromic, Nonloxodromic, TitsNull, `Lox/*`, `Nonlox/*` and the `Cla/*` of
  L1–L7; B on the same top-level modules and on L1–L4, L6, L8–L12 with G9Pair/G9PairLin,
  CoverMax and SmoothCap/SmoothGlue/SmoothCone/CCComponent; `barbot_B_geroch` adds GerochFlat,
  TheoremBInputs and `Geroch/*`. **kb/0025:** the
  scaffold root imports no `Flat` module, so the axiom sweep has not seen these; the figures are
  `#print axioms` run by hand.
* **Not attempted:** the corollary on closed Cauchy hypersurfaces (finitely covered by
  `Tᵏ × closed hyperbolic manifold`, l.383–386): the library has no notion of a closed hyperbolic
  manifold.
* **Findings.** (1) Nonloxodromic's `nonloxodromic_parabolic` does not export `Convex ℝ Ω`
  (true: `Ω = π_𝒰⁻¹(Ω_A)`, a slab between null hyperplanes), without which no tame embedding into
  `B = Γ''\Ω` can be derived (π₁(B) is an extension of `Γ''` by π₁(Ω)); it is now recovered after
  the fact (L1, part (2)): a presentation of an LTP over a unipotent spacetime whose `Ω` contains
  the nonempty preconnected `Γ''`-invariant `𝒟(M̃)` is convex. The export would still be the
  simpler interface. (2) Barbot's (ii) "follows
  from (i)" (l.3578) also needs that a finite cover of a maximal CGH spacetime is maximal, which the
  paper does not state (used in `cauclo_from_embedding`). It is true and proved without the
  uniqueness of maximal Cauchy developments (`Cla.CoverMax`, `cover_maximal_of_isFiniteCover`):
  Rem `defdep`'s first claim (l.2517–2521), proved for every maximal GH flat spacetime with (CC′)
  in the DEC-35 reading — `𝒟(M̃) = int D(Σ)`, `cover_range_eq_of_mgh`, Cauchy-compactness unused —
  then the lift of a Cauchy embedding of the cover to the universal covers. Rem `defdep`'s second
  claim, `Ω(S̃) = int D(Σ)` (Rem `dependance`, l.3552–3555), is not proved. (3) [11.i]'s proof applies Theorem A to the
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
  absolutely maximal among GH Cauchy-complete targets. (7) Family (b)'s GH needs a loxodromic
  element of `Γ` (so that `Λ(Γ)` has two directions and `Ω^±(Λ(Γ))` carries a cosmological time).
  Def 4.18's "discrete without global fixed point" yields one only through the classification of
  elementary groups, which Barbot does not invoke here; it is derived from Benoist's theorem
  (`BenoistNoLox`, already in `BarbotExternals`) by averaging a finite orbit
  (`exists_loxodromic_of_not_hasGlobalFixedPoint`) — no new hypothesis. (8) The past sides are
  reached by the time reversal `τ`, which is not in `Isom(𝐌ⁿ)`, while `g ↦ τgτ` is an automorphism
  of it (`revConj`): `τΩ⁻(Λ) = Ω⁺(−Λ)`, so Examples' future-only cosmological-time lemmas serve.
  (9) A presentation `IsQuotientOf M Γ Ω` with `M` Hausdorff already makes the action free and
  properly discontinuous: the instances need not be carried. (10) **G1 is wrong as printed**
  (L5, `Cla.UnipEnvelope`, l.3654–3676): Barbot's slab `π₁⁻¹(]−Y₊, Y₊[)` need not be a component
  of `Ω(A)` nor maximal (witness `Cla.slab_not_maximal_e2` in `𝐌⁴`); the envelope used in
  `exists_absMax_unipotent_ltp` is the corrected one, over a maximal admissible interval, and the
  conclusion of [11.i] for the unipotent family survives unchanged. (11) In Theorem B's proof the
  GH of `B` over a family-(b) base is Benoist's theorem again (the loxodromic element of finding
  7): Theorem B's assembly uses `BenoistNoLox` twice, in Theorem A₀ and in G9 — the second use is
  why `cauclo_from_embedding` takes `hE` (2026-11-01). (12) Cauchy-compact ⇒ Cauchy-complete
  (l.3536, l.560–565) takes the closed Cauchy hypersurface to be smooth spacelike; for a
  topological one a smoothing step is needed and is proved (L9): finitely many past-hyperboloid
  caps whose rims lie strictly below `S` (in `I⁻(S)`) and which lie strictly above `S` near their
  centres, so that the upper part `K ∖ I⁻(K)` of their union is a nonempty compact spacelike
  Lipschitz hypersurface (`Cla.exists_capEnvelope_of_isCompact_cauchy`, SmoothCap; the gluing
  `Cla.isLocallyConeZeroSetAt_of_capData`, SmoothGlue), one component of which is connected
  (CCComponent) and Cauchy by lemma K; only per-point constants, no uniform net. (13) [10.M]
  (Loxodromic's SCOPE, `docs/BARBOT.md` F3, F4): l.3326–3327 "the action on `π_P⁻¹(0)` is free
  and properly discontinuous" is false for `Γ` (true for `Γ₀ = ker a`; Bieberbach is run on
  `Γ₁`'s euclidean model, `Lox.misner_bieberbach`), and l.3264–3269's conjugation formula holds
  only if `α(γ)` fixes the origin of `Q₀` (a screw part breaks the accumulation argument); the
  conclusion is proved another way (`Lox.fix_second_null`, translation lengths being conjugation
  invariant, under Bieberbach I — whence `hBieb`).

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
Carrière–Dal'bo's maximal unipotent subspace (5.2). Tits' alternative in the form
`TitsVirtuallyAbelianNull` (not cited by Barbot; Nonloxodromic, DEC-27) is **not** a component:
it is supplied by `Flat/TitsNull`'s `titsVirtuallyAbelianNull` (DEC-50; sorry-free) where it is
consumed, `caseOutput`. -/
structure BarbotExternals : Prop where
  benoist : ∀ k ≤ d, BenoistNoLox k
  bieberbach : ∀ k ≤ d + 1, BieberbachI (EuclideanSpace ℝ (Fin k))
  auslander : ∀ k ≤ d, AuslanderCarriereDalbo k
  unipotent : ∀ k ≤ d, MaxUnipotentSubspace k

theorem BarbotExternals.mono {d₁ : ℕ} (h : BarbotExternals d) (h₁ : d₁ ≤ d) :
    BarbotExternals d₁ :=
  ⟨fun k hk => h.benoist k (hk.trans h₁), fun k hk => h.bieberbach k (by omega),
    fun k hk => h.auslander k (hk.trans h₁), fun k hk => h.unipotent k (hk.trans h₁)⟩

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
                   exact maxUnipotentSubspace_zero⟩

/-- **Lemma K's named data on a flat spacetime** (`Causal.CompactCauchy`, DEC-44): the
hypotheses of its proved form `isCauchySurface_of_isLocallyCauchyTwoSided` beyond GH, with the
splitting supplied by a chronal causal flow. The `flow` field is redundant since
`Splitting.lean`'s target 4 (`Flat.flat_hasChronalCausalFlow`) is proved for every Hausdorff
second-countable flat manifold, so for every `FlatSpacetime` (DEC-49); kept, so that the
statements carrying `FlatLemmaKData` do not change. -/
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
`Convex ℝ Ω` added to its conclusion (needed for tameness, `exists_finiteCover_tameEmbedding`).
No `sorry` of its own: the convexity is recovered by L1 (`Cla.exists_isLTPData_convex_of_unipotent`,
part (2)) from `𝒟(M̃) ⊆ Ω`, a nonempty preconnected `Γ''`-invariant set; `nonloxodromic_parabolic`
is sorry-free upstream since 2026-11-01, so this is sorry-free (`#print axioms`). -/
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
  obtain ⟨Γ'', hle'', hidx'', Ω, hDΩ, -, B, hq, d₁, hd₁, M₁, hU, hltp⟩ :=
    nonloxodromic_parabolic _hBieb _hpair _hcaus _h _hle _hidx _hnl _hv0 _hv _hfix _hpar
  refine ⟨Γ'', hle'', hidx'', Ω, hDΩ, ?_, B, hq, d₁, hd₁, M₁, hU, hltp⟩
  -- `𝒟(M̃)` is a nonempty preconnected `Γ''`-invariant subset of `Ω` (L1, part (2))
  refine (Cla.exists_isLTPData_convex_of_unipotent hU hltp).2 Γ'' Ω hq (range D) hDΩ
    (isPreconnected_range (by letI := flatCoverChartedSpace d M x₀; exact _hpair.gx.continuous))
    (range_nonempty D) ?_
  rintro γ hγ _ ⟨z, rfl⟩
  obtain ⟨δ, rfl⟩ := _hle (hle'' hγ)
  exact ⟨δ.1 z, _hpair.equiv δ z⟩

/-- **The nonloxodromic case in the common form** (§9, `nonloxodromic` with convexity).
Sorry-free (`#print axioms`, 2026-11-01). -/
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

/-- **The nonelementary loxodromic case in the common form** ([10.G], family (b)). No `sorry`
beneath it: Loxodromic's `bprop_LU_discrete`, which it uses through
`loxo_generic_centralExtension`, is sorry-free (`#print axioms`: `propext`, `Classical.choice`,
`Quot.sound`). -/
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

/-- **The elementary loxodromic case in the common form** ([10.M], Misner), in `𝐌^{d'+2}`.
Sorry-free since 2026-11-01 (`loxo_elementary_misner` closed, under `hBieb`). -/
theorem caseOutput_misner {d' : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (Minkowski (d' + 1)) M]
    [HasGroupoid M (gxGroupoid (isom (d' + 1)) (Minkowski (d' + 1)))] [T2Space M] {x₀ : M}
    {D : UniversalCover M x₀ → Minkowski (d' + 1)}
    {ρ : Deck (UniversalCover.proj M x₀) →* isom (d' + 1)} {S : Set M}
    (hBieb : ∀ k ≤ d' + 1 + 1, BieberbachI (EuclideanSpace ℝ (Fin k)))
    (hpair : IsDevelopingPair x₀ D ρ) (hcaus : (flatCausality (d' + 1) M).IsCausal)
    (h : DevelopsCC x₀ D S) (hlox : ∃ γ ∈ ρ.range, IsLoxodromic (linOf γ))
    (helem : ¬IsNonelementary ρ.range) : CaseOutput D ρ := by
  obtain ⟨Γ', hle, hidx, B, hB', d₁, M₁, hd₁, hltp, hM₁⟩ :=
    loxo_elementary_misner hBieb hpair hcaus h hlox helem
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
not (Isometries' classes), then elementary or not. The nonloxodromic branch's
`TitsVirtuallyAbelianNull d` is discharged here by TitsNull's `titsVirtuallyAbelianNull d`
(DEC-50), not taken from `BarbotExternals`. -/
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
      | succ d' => exact caseOutput_misner hE.bieberbach hpair hcaus h hlox hne
  · push Not at hlox
    exact caseOutput_nonloxodromic (hE.benoist d le_rfl) (titsVirtuallyAbelianNull d)
      hE.bieberbach hpair hcaus h hlox

/-! ## §3 The finite cover and the tame embedding -/

/-- **The finite cover `M' = ρ⁻¹(Γ'')\M̃` tamely embeds in `B = Γ''\Ω`** (l.3586–3592; R1's
"finite cover", DEC-43). Proved, no `sorry`: `M' = Γ''\𝒟(M̃)` finitely covers `M` (L2,
`Cla.exists_finiteCover_quotient_range`) and `[w] ↦ [w]` is tame, `𝒟(M̃)` and the convex `Ω`
being simply connected (L3, `Cla.exists_isTameEmbedding_of_isQuotientOf_le`). -/
theorem exists_finiteCover_tameEmbedding (M : FlatSpacetime.{u} d) {x₀ : M}
    {D : UniversalCover M x₀ → Minkowski d} {ρ : Deck (UniversalCover.proj M x₀) →* isom d}
    (_hpair : IsDevelopingPair x₀ D ρ) (_hinj : Injective D) {Γ : Subgroup (isom d)}
    (_hle : Γ ≤ ρ.range) (_hidx : Γ.relIndex ρ.range ≠ 0) {Ω : Opens (Minkowski d)}
    (_hΩ : range D ⊆ Ω) (_hcv : Convex ℝ (Ω : Set (Minkowski d))) {B : FlatSpacetime.{0} d}
    (_hB : IsQuotientOf B Γ Ω) :
    ∃ (M' : FlatSpacetime.{0} d) (p : M' → M), IsFiniteCover d p ∧
      ∃ f : M' → B, IsTameEmbedding d f := by
  obtain ⟨W, hW, hWsc, M', p, hp, hq'⟩ :=
    Cla.exists_finiteCover_quotient_range M _hpair _hinj _hle _hidx _hΩ _hB
  have hne : (Ω : Set (Minkowski d)).Nonempty := (range_nonempty D).mono _hΩ
  haveI : ContractibleSpace Ω := _hcv.contractibleSpace hne
  have hWΩ : W ≤ Ω := fun x hx => _hΩ (hW ▸ hx)
  exact ⟨M', p, hp, Cla.exists_isTameEmbedding_of_isQuotientOf_le hWΩ hq' _hB hWsc inferInstance⟩

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

/-- A covering map is injective near each point (it is a local homeomorphism). -/
theorem exists_injOn_of_isCoveringMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {π : X → Y} (h : IsCoveringMap π) (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ InjOn π U := by
  obtain ⟨e, hx, he⟩ := h.isLocalHomeomorph x
  exact ⟨e.source, e.open_source, hx, fun a ha b hb hab => by
    rw [he] at hab; exact e.injOn ha hb hab⟩

/-- **A covering presentation acts freely**: if `γ p = p`, `γ` fixes a neighbourhood of `p` (the
covering `π` is injective near `p` and `π (γ q) = π q`), hence `γ = 1` (rigidity,
`Causal.eq_of_eqOn`). Only the covering property and the fibres are used, not the local isometry. -/
theorem isCancelSMul_of_isCoveringMap {X : Type*} [TopologicalSpace X] {Γ : Subgroup (isom d)}
    {Ω : Opens (Minkowski d)} [FlatQuotient.Invariant Γ Ω] {π : Ω → X} (hcov : IsCoveringMap π)
    (hfib : ∀ p q : Ω, π p = π q ↔ ∃ γ ∈ Γ, γ • (p : Minkowski d) = q) : IsCancelSMul Γ Ω := by
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro γ p hp
  obtain ⟨U, hUo, hpU, hinj⟩ := exists_injOn_of_isCoveringMap hcov p
  have hc : Continuous fun q : Ω => γ • q := continuous_const_smul γ
  have hU' : IsOpen (U ∩ (fun q : Ω => γ • q) ⁻¹' U) := hUo.inter (hUo.preimage hc)
  have hfix : ∀ q ∈ U ∩ (fun q : Ω => γ • q) ⁻¹' U, γ • q = q := by
    rintro q ⟨hq1, hq2⟩
    exact hinj hq2 hq1 ((hfib q (γ • q)).2 ⟨γ, γ.2, rfl⟩).symm
  obtain ⟨V, hVo, hV⟩ := isOpen_induced_iff.1 hU'
  have hpU' : p ∈ U ∩ (fun q : Ω => γ • q) ⁻¹' U := ⟨hpU, by simp only [mem_preimage, hp]; exact hpU⟩
  rw [← hV] at hpU'
  have hpV : (p : Minkowski d) ∈ V ∩ Ω := ⟨hpU', p.2⟩
  apply Subtype.ext
  refine Causal.eq_of_eqOn (hVo.inter Ω.isOpen) ⟨_, hpV⟩ fun x hx => ?_
  have hx' : (⟨x, hx.2⟩ : Ω) ∈ U ∩ (fun q : Ω => γ • q) ⁻¹' U := by rw [← hV]; exact hx.1
  have := congrArg Subtype.val (hfix _ hx')
  simpa using this

/-- **A covering presentation acts properly discontinuously** (`X` Hausdorff): if infinitely many
`γₙ` met `γₙ K ∩ L`, extract `kₙ → a`, `γₙ kₙ → b` (compactness); `π a = π b` (`π (γₙ kₙ) = π kₙ`,
`X` Hausdorff), so `b = γ a`; near `b`, `π` is injective and both `γₙ kₙ` and `γ kₙ` lie there with
the same image, so `γₙ = γ` eventually (freeness), against the injectivity of `n ↦ γₙ`. -/
theorem properlyDiscontinuousSMul_of_isCoveringMap {X : Type*} [TopologicalSpace X] [T2Space X]
    {Γ : Subgroup (isom d)} {Ω : Opens (Minkowski d)} [FlatQuotient.Invariant Γ Ω] {π : Ω → X}
    (hcov : IsCoveringMap π)
    (hfib : ∀ p q : Ω, π p = π q ↔ ∃ γ ∈ Γ, γ • (p : Minkowski d) = q) :
    ProperlyDiscontinuousSMul Γ Ω := by
  haveI := isCancelSMul_of_isCoveringMap hcov hfib
  refine ⟨fun {K L} hK hL => ?_⟩
  by_contra hinf
  set T := {γ : Γ | ((γ • ·) '' K ∩ L).Nonempty}
  let e := Set.Infinite.natEmbedding T hinf
  have hmem : ∀ n, ∃ k ∈ K, ((e n : Γ)) • k ∈ L := fun n => by
    obtain ⟨_, ⟨k, hk, rfl⟩, hl⟩ := (e n).2
    exact ⟨k, hk, hl⟩
  choose k hkK hkL using hmem
  obtain ⟨a, -, φ, hφ, ha⟩ := hK.tendsto_subseq hkK
  obtain ⟨b, -, ψ, hψ, hb⟩ := hL.tendsto_subseq (fun n => hkL (φ n))
  set c : ℕ → Ω := fun n => k (φ (ψ n))
  set γn : ℕ → Γ := fun n => (e (φ (ψ n)) : Γ)
  have hc : Tendsto c atTop (𝓝 a) := ha.comp hψ.tendsto_atTop
  have hb' : Tendsto (fun n => γn n • c n) atTop (𝓝 b) := hb
  have hπ : ∀ n, π (γn n • c n) = π (c n) := fun n =>
    ((hfib (c n) (γn n • c n)).2 ⟨_, (γn n).2, rfl⟩).symm
  have h1 : Tendsto (fun n => π (c n)) atTop (𝓝 (π a)) := (hcov.continuous.tendsto a).comp hc
  have h2 : Tendsto (fun n => π (c n)) atTop (𝓝 (π b)) := by
    have := (hcov.continuous.tendsto b).comp hb'
    simpa only [comp_def, hπ] using this
  obtain ⟨γ, hγ, hγab⟩ := (hfib a b).1 (tendsto_nhds_unique h1 h2)
  set g : Γ := ⟨γ, hγ⟩
  have hga : g • a = b := Subtype.ext hγab
  obtain ⟨U, hUo, hbU, hinj⟩ := exists_injOn_of_isCoveringMap hcov b
  have h3 : Tendsto (fun n => g • c n) atTop (𝓝 b) := by
    have := ((continuous_const_smul g).tendsto a).comp hc
    rwa [hga] at this
  have hev : ∀ᶠ n in atTop, γn n = g := by
    filter_upwards [h3.eventually (hUo.mem_nhds hbU), hb'.eventually (hUo.mem_nhds hbU)] with n
      hu1 hu2
    have hπ' : π (γn n • c n) = π (g • c n) := by
      rw [hπ, ((hfib (c n) (g • c n)).2 ⟨_, g.2, rfl⟩)]
    exact IsCancelSMul.right_cancel _ _ _ (hinj hu2 hu1 hπ')
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have hEq : e (φ (ψ N)) = e (φ (ψ (N + 1))) :=
    Subtype.ext ((hN N le_rfl).trans (hN (N + 1) (by omega)).symm)
  have := hψ.injective (hφ.injective (e.injective hEq))
  omega

/-- **The action of an `IsQuotientOf` presentation is free** (`isCancelSMul_of_isCoveringMap`). -/
theorem IsQuotientOf.isCancelSMul {M : Type*} [TopologicalSpace M] [ChartedSpace (Minkowski d) M]
    {Γ : Subgroup (isom d)} {Ω : Opens (Minkowski d)} (hq : IsQuotientOf M Γ Ω)
    [FlatQuotient.Invariant Γ Ω] : IsCancelSMul Γ Ω :=
  let ⟨_, hcov, _, _, hfib⟩ := hq.quot
  isCancelSMul_of_isCoveringMap hcov hfib

/-- **The action of an `IsQuotientOf` presentation is properly discontinuous** (`M` Hausdorff;
`properlyDiscontinuousSMul_of_isCoveringMap`). So the instances `gh_of_isQuotientOf` asks of the
constructed quotient are supplied by the presentation itself. -/
theorem IsQuotientOf.properlyDiscontinuousSMul {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (Minkowski d) M] {Γ : Subgroup (isom d)} {Ω : Opens (Minkowski d)}
    (hq : IsQuotientOf M Γ Ω) [FlatQuotient.Invariant Γ Ω] : ProperlyDiscontinuousSMul Γ Ω :=
  let ⟨_, hcov, _, _, hfib⟩ := hq.quot
  properlyDiscontinuousSMul_of_isCoveringMap hcov hfib

/-- A causal pair of `𝐌ⁿ` has a nonpositive square interval. -/
theorem minkQ_nonpos_of_le_top {p q : Minkowski d} (h : (minkowski d).le ⊤ p q) :
    minkQ (q - p) ≤ 0 := by
  have h' := minkowski_le_top_iff.1 h
  simp only [minkQ, Prod.fst_sub, Prod.snd_sub]
  nlinarith [norm_nonneg (q.2 - p.2)]

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

/-! ### [11.i] GH of Misner spacetimes on the past wedge -/

section MisnerPast

variable {e : ℕ} {L : AddSubgroup (ℝ × EuclideanSpace ℝ (Fin e))}

theorem mem_misnerWedgePast {p : Minkowski (e + 1)} :
    p ∈ misnerWedgePast e ↔ nullX p < 0 ∧ 0 < nullY p := Iff.rfl

/-- `G₀` preserves the past Misner wedge (`eˢ x`, `e⁻ˢ y`). -/
instance instInvariantMisnerPast : FlatQuotient.Invariant (misnerGroup L) (misnerWedgePast e) :=
  ⟨fun γ p hp => by
    obtain ⟨x, -, hx⟩ := mem_misnerGroup.1 γ.2
    rw [← hx, mem_misnerWedgePast, nullX_misner, nullY_misner]
    obtain ⟨h1, h2⟩ := mem_misnerWedgePast.1 hp
    exact ⟨mul_neg_of_pos_of_neg (Real.exp_pos _) h1, mul_pos (Real.exp_pos _) h2⟩⟩

/-- The past Misner wedge is convex and nonempty, hence connected. -/
theorem isConnected_misnerWedgePast :
    IsConnected (misnerWedgePast e : Set (Minkowski (e + 1))) := by
  refine (convex_of_mem_iff_null (c := -1) fun _ => mem_misnerWedgePast_iff).isConnected
    ⟨((-1 : ℝ), 0), ?_⟩
  rw [SetLike.mem_coe, mem_misnerWedgePast]
  have hs : 0 < √2 := by positivity
  simp only [nullX, nullY, PiLp.zero_apply]
  exact ⟨div_neg_of_neg_of_pos (by norm_num) hs, div_pos (by norm_num) hs⟩

/-- The past Misner wedge is the past regular domain `Ω⁻(Λ)`, `Λ = {(±e₁, 0)}`. -/
theorem mem_omegaMinus_misnerΛ {p : Minkowski (e + 1)} :
    p ∈ omegaMinus (misnerΛ e) ↔ nullX p < 0 ∧ 0 < nullY p := by
  rw [mem_omegaMinus]
  simp only [misnerΛ, mem_insert_iff, mem_singleton_iff, forall_eq_or_imp, forall_eq,
    minkB_nullVec, axisSphere, axisSphereNeg]
  have h1 : inner ℝ (axisVec e) p.2 = p.2 0 := by simp [axisVec, EuclideanSpace.inner_single_left]
  have h2 : inner ℝ (-axisVec e) p.2 = -p.2 0 := by rw [inner_neg_left, h1]
  rw [h1, h2]
  have hs : 0 < √2 := by positivity
  simp only [nullX, nullY]
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨div_neg_of_neg_of_pos (by linarith) hs, div_pos (by linarith) hs⟩
  · rintro ⟨ha, hb⟩
    have ha' : p.2 0 + p.1 < 0 := by
      by_contra hc; push Not at hc; exact absurd ha (not_lt.2 (div_nonneg hc hs.le))
    have hb' := (div_pos_iff_of_pos_right hs).1 hb
    constructor <;> linarith

/-- **The past Misner wedge is globally hyperbolic in `𝐌ⁿ`** (`Ω⁻(Λ)` is past-closed). -/
theorem globallyHyperbolicOn_misnerWedgePast :
    (minkowski (e + 1)).GloballyHyperbolicOn (misnerWedgePast e) := by
  have h : ((misnerWedgePast e : Opens (Minkowski (e + 1))) : Set (Minkowski (e + 1))) =
      omegaMinus (misnerΛ e) := Set.ext fun _ => mem_omegaMinus_misnerΛ.symm
  refine globallyHyperbolicOn_of_Jminus_subset ?_
  rw [h]; exact Jminus_omegaMinus_subset _

theorem exp_sub_one_mul_exp_neg_sub_one (s : ℝ) :
    (Real.exp s - 1) * (Real.exp (-s) - 1) = -((Real.exp s - 1) ^ 2 * Real.exp (-s)) := by
  have h : Real.exp s * Real.exp (-s) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  linear_combination (Real.exp s - 1) * h


/-- **`G₀` acts acausally on the past wedge**: `|g p − p|² = −2(eˢ − 1)² e⁻ˢ xy + |w|²` is
positive for `xy < 0` unless `g = 1`. -/
theorem actsAcausally_misnerPast :
    FlatQuotient.ActsAcausally (misnerGroup L) (misnerWedgePast e) := by
  intro γ hne x hle
  have hle' := (minkowski (e + 1)).le_mono le_top ((flat_le_top_subtype_iff _ _ _).1 hle)
  obtain ⟨y, -, hy⟩ := mem_misnerGroup.1 γ.2
  have hQ := minkQ_nonpos_of_le_top hle'
  rw [FlatQuotient.coe_smul, ← hy, minkQ_misnerMap_smul_sub] at hQ
  obtain ⟨hX, hY⟩ := mem_misnerWedgePast.1 x.2
  have hXY : nullX (x : Minkowski (e + 1)) * nullY (x : Minkowski (e + 1)) < 0 :=
    mul_neg_of_neg_of_pos hX hY
  have hA := exp_sub_one_mul_exp_neg_sub_one y.1
  have hrw : 2 * ((Real.exp y.1 - 1) * nullX (x : Minkowski (e + 1))) *
      ((Real.exp (-y.1) - 1) * nullY (x : Minkowski (e + 1))) =
      -(2 * ((Real.exp y.1 - 1) ^ 2 * Real.exp (-y.1)) *
        (nullX (x : Minkowski (e + 1)) * nullY (x : Minkowski (e + 1)))) := by
    rw [← neg_mul, ← neg_mul]; linear_combination
      (2 * nullX (x : Minkowski (e + 1)) * nullY (x : Minkowski (e + 1))) * hA
  rw [hrw] at hQ
  have hE := Real.exp_pos (-y.1)
  have hpos : 0 ≤ (Real.exp y.1 - 1) ^ 2 * Real.exp (-y.1) := by positivity
  have h1 : (Real.exp y.1 - 1) ^ 2 * Real.exp (-y.1) = 0 := by
    by_contra hc
    have : 0 < (Real.exp y.1 - 1) ^ 2 * Real.exp (-y.1) := lt_of_le_of_ne hpos (Ne.symm hc)
    nlinarith [sq_nonneg ‖y.2‖, mul_pos this (neg_pos.2 hXY)]
  have hs : y.1 = 0 := by
    rcases mul_eq_zero.1 h1 with h | h
    · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
      rwa [sub_eq_zero, Real.exp_eq_one_iff] at this
    · exact absurd h hE.ne'
  have hw : y.2 = 0 := by
    rw [h1, mul_zero, zero_mul, neg_zero, zero_add] at hQ
    exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1
      (le_antisymm hQ (sq_nonneg _)))
  apply hne
  apply Subtype.ext
  rw [← hy, show y = 0 from Prod.ext hs hw, misnerMap_zero]
  rfl

theorem norm_le_of_sq_le {a C : ℝ} (ha : 0 ≤ a) (hC : a ^ 2 ≤ C) : a ≤ 1 + C := by
  nlinarith

/-- **Finiteness of `{γ | x ≤ γ y}` on the past wedge** (the input of `gh_frameConj`): `x ≤ g y`
bounds `s` by the logarithms of the ratios of the null coordinates, and then `|z + w − z'|`. -/
theorem finite_le_misnerPast [BallFinite L] (x y : misnerWedgePast e) :
    {γ : misnerGroup L |
      (flatCausality (e + 1) (misnerWedgePast e)).le ⊤ x (γ • y)}.Finite := by
  set X₁ := nullX (x : Minkowski (e + 1))
  set Y₁ := nullY (x : Minkowski (e + 1))
  set X₂ := nullX (y : Minkowski (e + 1))
  set Y₂ := nullY (y : Minkowski (e + 1))
  obtain ⟨hX₁, hY₁⟩ := mem_misnerWedgePast.1 x.2
  obtain ⟨hX₂, hY₂⟩ := mem_misnerWedgePast.1 y.2
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = (|Real.log (X₁ / X₂)| + |Real.log (Y₁ / Y₂)|) +
      (1 + 2 * (-X₁) * Y₁ + ‖nullZ (y : Minkowski (e + 1)) - nullZ (x : Minkowski (e + 1))‖) :=
    ⟨_, rfl⟩
  refine (finite_misner_of_bound (L := L) R).subset ?_
  rintro γ hle
  obtain ⟨w, hwL, hw⟩ := mem_misnerGroup.1 γ.2
  refine ⟨w, hwL, ?_, hw⟩
  have hle' := (minkowski (e + 1)).le_mono le_top ((flat_le_top_subtype_iff _ _ _).1 hle)
  rw [FlatQuotient.coe_smul, ← hw] at hle'
  set q := misnerMap w • (y : Minkowski (e + 1))
  have hq := minkowski_le_top_iff.1 hle'
  have hQ := minkQ_nonpos_of_le_top hle'
  have hs2 : 0 < √2 := by positivity
  have h0 : |(q - (x : Minkowski (e + 1))).2 0| ≤ ‖(q - (x : Minkowski (e + 1))).2‖ := by
    have := PiLp.norm_apply_le (q - (x : Minkowski (e + 1))).2 0
    rwa [Real.norm_eq_abs] at this
  have hab := abs_le.1 (h0.trans hq)
  have hnX : 0 ≤ nullX (q - (x : Minkowski (e + 1))) := by
    simp only [nullX, Prod.fst_sub]; exact div_nonneg (by linarith [hab.1]) hs2.le
  have hnY : nullY (q - (x : Minkowski (e + 1))) ≤ 0 := by
    simp only [nullY, Prod.fst_sub]; exact div_nonpos_of_nonpos_of_nonneg (by linarith [hab.2]) hs2.le
  rw [nullX_sub', nullX_misner] at hnX
  rw [nullY_sub', nullY_misner] at hnY
  rw [minkQ_eq_null, nullX_sub', nullY_sub', nullZ_sub', nullX_misner, nullY_misner,
    nullZ_misner] at hQ
  -- the boost parameter
  have hsup : w.1 ≤ Real.log (X₁ / X₂) := by
    rw [Real.le_log_iff_exp_le (div_pos_of_neg_of_neg hX₁ hX₂), le_div_iff_of_neg hX₂]
    linarith
  have hinf : -w.1 ≤ Real.log (Y₁ / Y₂) := by
    rw [Real.le_log_iff_exp_le (div_pos hY₁ hY₂), le_div_iff₀ hY₂]
    linarith
  have hs : |w.1| ≤ |Real.log (X₁ / X₂)| + |Real.log (Y₁ / Y₂)| := by
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (Real.log (Y₁ / Y₂)), abs_nonneg (Real.log (X₁ / X₂)),
        le_abs_self (Real.log (Y₁ / Y₂))]
    · linarith [le_abs_self (Real.log (X₁ / X₂)), abs_nonneg (Real.log (Y₁ / Y₂))]
  -- the translation part
  have hE1 := Real.exp_pos w.1
  have hE2 := Real.exp_pos (-w.1)
  have hA : Real.exp w.1 * X₂ - X₁ ≤ -X₁ := by nlinarith
  have hB : Y₁ - Real.exp (-w.1) * Y₂ ≤ Y₁ := by nlinarith
  have hab2 : (Real.exp w.1 * X₂ - X₁) * (Y₁ - Real.exp (-w.1) * Y₂) ≤ (-X₁) * Y₁ :=
    mul_le_mul hA hB (by linarith) (by linarith)
  have key : 2 * (Real.exp w.1 * X₂ - X₁) * (Real.exp (-w.1) * Y₂ - Y₁) =
      -(2 * ((Real.exp w.1 * X₂ - X₁) * (Y₁ - Real.exp (-w.1) * Y₂))) := by ring
  have hZ2 : ‖w.2 + nullZ (y : Minkowski (e + 1)) - nullZ (x : Minkowski (e + 1))‖ ^ 2 ≤
      2 * (-X₁) * Y₁ := by
    rw [key] at hQ; linarith
  have hZ := norm_le_of_sq_le (norm_nonneg _) hZ2
  have hw2 : ‖w.2‖ ≤ 1 + 2 * (-X₁) * Y₁ +
      ‖nullZ (y : Minkowski (e + 1)) - nullZ (x : Minkowski (e + 1))‖ := by
    have := norm_sub_le (w.2 + nullZ (y : Minkowski (e + 1)) - nullZ (x : Minkowski (e + 1)))
      (nullZ (y : Minkowski (e + 1)) - nullZ (x : Minkowski (e + 1)))
    rw [show w.2 + nullZ (y : Minkowski (e + 1)) - nullZ (x : Minkowski (e + 1)) -
      (nullZ (y : Minkowski (e + 1)) - nullZ (x : Minkowski (e + 1))) = w.2 by abel] at this
    linarith
  have hP : 0 < (-X₁) * Y₁ := mul_pos (neg_pos.2 hX₁) hY₁
  have hN := norm_nonneg (nullZ (y : Minkowski (e + 1)) - nullZ (x : Minkowski (e + 1)))
  have hL1 := abs_nonneg (Real.log (X₁ / X₂))
  have hL2 := abs_nonneg (Real.log (Y₁ / Y₂))
  rw [Prod.norm_def, Real.norm_eq_abs, hR]
  exact max_le (by linarith) (by linarith)

/-- **[11.i], (1) for Misner spacetimes on the past wedge: GH in the `IsQuotientOf` form**:
`gh_frameConj` on `{x < 0 < y}` (globally hyperbolic in `𝐌ⁿ`, being `Ω⁻(Λ)`; acausal and with
finite `{γ | x ≤ γy}` by direct computation in null coordinates), the instances on the quotient
from `IsQuotientOf` itself, and `gh_of_isQuotientOf`. -/
theorem gh_of_isQuotientOf_misnerWedgePast {M₁ : FlatSpacetime.{u} (e + 1)}
    {φ : isom (e + 1)} [BallFinite L]
    (hq : IsQuotientOf M₁ (frameConj φ (misnerGroup L)) (isomImage φ (misnerWedgePast e))) :
    GH M₁ := by
  haveI := hq.invariant
  haveI := hq.isCancelSMul
  haveI := hq.properlyDiscontinuousSMul
  exact gh_of_isQuotientOf hq (gh_frameConj φ (misnerGroup L) (misnerWedgePast e) _ rfl
    (isConnected_isomImage φ _ isConnected_misnerWedgePast) actsAcausally_misnerPast
    globallyHyperbolicOn_misnerWedgePast finite_le_misnerPast)

end MisnerPast

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

/-! ### [11.i] Cauchy-completeness of translation spacetimes -/

section TranslationComplete

open scoped Pointwise

/-- The chart of an open subset of `𝐌ⁿ` is the inclusion. -/
theorem chartAt_opens_apply (Ω : Opens (Minkowski d)) (x y : Ω) :
    chartAt (Minkowski d) x y = (y : Minkowski d) := by
  rw [TopologicalSpace.Opens.chartAt_eq]; simp [OpenPartialHomeomorph.subtypeRestr]

/-- An element of `φ(horizGroup Λ)φ⁻¹` is `p ↦ φ((0, v) + φ⁻¹p)`, `v ∈ Λ`. -/
theorem mem_frameConj_horizGroup {φ γ : isom d} {Λ : AddSubgroup (EuclideanSpace ℝ (Fin d))}
    (hγ : γ ∈ frameConj φ (horizGroup Λ)) :
    ∃ v ∈ Λ, ∀ p : Minkowski d, γ • p = φ • (((0 : ℝ), v) + φ⁻¹ • p) := by
  obtain ⟨τ, hτ, rfl⟩ := Subgroup.mem_map.1 hγ
  obtain ⟨v, hv, rfl⟩ := mem_horizGroup.1 hτ
  refine ⟨v, hv, fun p => ?_⟩
  simp [MulAut.conj_apply, mul_smul, horizTranslation_smul]

/-- `φ (horizGroup Λ) φ⁻¹` acts acausally on `𝐌ⁿ`: `γ p − p = L(φ)(0, v)` is spacelike. -/
theorem actsAcausally_frameConj_horiz (φ : isom d) (Λ : AddSubgroup (EuclideanSpace ℝ (Fin d))) :
    FlatQuotient.ActsAcausally (frameConj φ (horizGroup Λ)) (⊤ : Opens (Minkowski d)) := by
  rintro ⟨γ, hγ⟩ hne x hle
  obtain ⟨v, -, hv⟩ := mem_frameConj_horizGroup hγ
  have hQ := minkQ_nonpos_of_le_top ((minkowski d).le_mono le_top
    ((flat_le_top_subtype_iff ⊤ _ _).1 hle))
  rw [FlatQuotient.coe_smul, hv, show (x : Minkowski d) = φ • (φ⁻¹ • (x : Minkowski d)) by
    rw [smul_inv_smul], smul_sub_smul, minkQ_isom_linear, inv_smul_smul, add_sub_cancel_right]
    at hQ
  have hv0 : v = 0 := by
    simp only [minkQ] at hQ
    have : ‖v‖ ^ 2 ≤ 0 := by nlinarith
    exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm this (sq_nonneg _)))
  apply hne
  apply Subtype.ext
  change γ = 1
  refine Causal.eq_of_eqOn (X := Minkowski d) isOpen_univ univ_nonempty fun p _ => ?_
  simp only [hv, hv0, Prod.mk_zero_zero, zero_add, smul_inv_smul, one_smul]

variable (φ : isom d)

/-- The slice `φ{t = 0}`, parametrised by `ℝᵈ`, in `Ω = 𝐌ⁿ`. -/
noncomputable def frameSlice (x : EuclideanSpace ℝ (Fin d)) : (⊤ : Opens (Minkowski d)) :=
  ⟨φ • ((0 : ℝ), x), trivial⟩

theorem continuous_frameSlice : Continuous (frameSlice φ) :=
  ((continuous_const_smul φ).comp (continuous_const.prodMk continuous_id)).subtype_mk _

variable {φ} {Λ : AddSubgroup (EuclideanSpace ℝ (Fin d))} {M₁ : Type*} {π : (⊤ : Opens (Minkowski d)) → M₁}

/-- The `Γ`-orbit of the slice is the slice. -/
theorem exists_frameSlice_of_proj_eq
    (hfib : ∀ p q : (⊤ : Opens (Minkowski d)), π p = π q ↔
      ∃ γ ∈ frameConj φ (horizGroup Λ), γ • (p : Minkowski d) = q)
    {x : EuclideanSpace ℝ (Fin d)} {p : (⊤ : Opens (Minkowski d))} (h : π p = π (frameSlice φ x)) :
    ∃ y, p = frameSlice φ y := by
  obtain ⟨γ, hγ, hγp⟩ := (hfib (frameSlice φ x) p).1 h.symm
  obtain ⟨v, -, hv⟩ := mem_frameConj_horizGroup hγ
  refine ⟨v + x, Subtype.ext ?_⟩
  rw [← hγp, hv]
  simp [frameSlice]

variable [TopologicalSpace M₁] [ChartedSpace (Minkowski d) M₁]

variable (π φ) in
/-- The parametrisation `q : ℝᵈ → S` of the projected slice `S = π(φ{t = 0})`. -/
noncomputable def sliceProj (x : EuclideanSpace ℝ (Fin d)) : range (π ∘ frameSlice φ) :=
  ⟨π (frameSlice φ x), x, rfl⟩

omit [ChartedSpace (Minkowski d) M₁] in
theorem continuous_sliceProj (hπ : Continuous π) : Continuous (sliceProj φ π) :=
  (hπ.comp (continuous_frameSlice φ)).subtype_mk _

omit [ChartedSpace (Minkowski d) M₁] in
/-- **Paths of `S` lift to `ℝᵈ`** through `q` (the restriction of the covering `π` to
`π⁻¹(S) = φ{t = 0}`, then `φ⁻¹` and the spatial projection). -/
theorem exists_lift_sliceProj (hcov : IsCoveringMap π)
    (hfib : ∀ p q : (⊤ : Opens (Minkowski d)), π p = π q ↔
      ∃ γ ∈ frameConj φ (horizGroup Λ), γ • (p : Minkowski d) = q)
    {a : EuclideanSpace ℝ (Fin d)} {s : range (π ∘ frameSlice φ)}
    (γ : Path (sliceProj φ π a) s) :
    ∃ (b : EuclideanSpace ℝ (Fin d)) (c : Path a b), sliceProj φ π b = s ∧
      ∀ t, sliceProj φ π (c t) = γ t := by
  set S := range (π ∘ frameSlice φ)
  have cov := hcov.restrictPreimage S
  set r : (π ⁻¹' S) → EuclideanSpace ℝ (Fin d) :=
    fun z => (φ⁻¹ • ((z : (⊤ : Opens (Minkowski d))) : Minkowski d)).2 with hr_def
  have hr : Continuous r := continuous_snd.comp
    ((continuous_const_smul _).comp (continuous_subtype_val.comp continuous_subtype_val))
  have key : ∀ z : π ⁻¹' S, frameSlice φ (r z) = z.1 := by
    rintro ⟨z, x, hx⟩
    obtain ⟨y, rfl⟩ := exists_frameSlice_of_proj_eq hfib hx.symm
    apply Subtype.ext
    simp [frameSlice, r]
  obtain ⟨Γ, hΓ, hΓ0⟩ := cov.exists_path_lifts γ.toContinuousMap ⟨frameSlice φ a, a, rfl⟩
    (by simp only [Path.coe_toContinuousMap, Path.source]; rfl)
  have hΓt : ∀ t, sliceProj φ π (r (Γ t)) = γ t := fun t => by
    apply Subtype.ext
    change π (frameSlice φ (r (Γ t))) = _
    rw [key]
    exact congrArg Subtype.val (congrFun hΓ t)
  refine ⟨r (Γ 1), Path.mk ⟨fun t => r (Γ t), hr.comp Γ.continuous⟩ ?_ rfl,
    by rw [hΓt, γ.target], hΓt⟩
  change r (Γ 0) = a
  rw [hΓ0]
  simp [r, frameSlice]

/-- Near each point, `(0, x')` is the chart of `S` at `q x` read through `q`, up to an isometry. -/
theorem sliceProj_local (hloc : IsLocalIsometry d π) (x : EuclideanSpace ℝ (Fin d)) :
    ∃ g : isom d, ∀ᶠ x' in 𝓝 x, ((0 : ℝ), x') =
      g • chartSys d (range (π ∘ frameSlice φ)) (sliceProj φ π x) (sliceProj φ π x') := by
  obtain ⟨-, h⟩ := isLocalIsometry_iff_eventually.1 hloc
  obtain ⟨g, hg⟩ := h (frameSlice φ x)
  refine ⟨(g * φ)⁻¹, ?_⟩
  filter_upwards [(continuous_frameSlice φ).continuousAt.eventually hg] with x' hx'
  change ((0 : ℝ), x') =
    (g * φ)⁻¹ • chartAt (Minkowski d) (π (frameSlice φ x)) (π (frameSlice φ x'))
  rw [hx', chartAt_opens_apply]
  simp [frameSlice, mul_smul]

/-- **`q : ℝᵈ → S` is `1`-Lipschitz** for the induced length of `S` (paths push down with the same
length, `pathLength_pulled_eq_of_local`). -/
theorem edist_sliceProj_le (hloc : IsLocalIsometry d π) (a b : EuclideanSpace ℝ (Fin d)) :
    edist (InducedLengthSpace.toSubtype.symm (sliceProj φ π a) :
        InducedLengthSpace d (range (π ∘ frameSlice φ)))
      (InducedLengthSpace.toSubtype.symm (sliceProj φ π b)) ≤ edist a b := by
  have hq := continuous_sliceProj (φ := φ) hloc.continuous
  rw [edist_eq_iInf_pathLength_slice a b]
  refine le_iInf fun c => ?_
  rw [pathLength_pulled_eq_of_local (fun z : EuclideanSpace ℝ (Fin d) => ((0 : ℝ), z))
    (chartSys d _) hq (sliceProj_local hloc) c]
  exact iInf_le (fun γ : Path (sliceProj φ π a) (sliceProj φ π b) =>
    pathLength (chartSys d (range (π ∘ frameSlice φ))) γ) (c.map hq)

/-- **Short paths of `S` lift to short segments of `ℝᵈ`.** -/
theorem exists_sliceProj_edist_le (hcov : IsCoveringMap π) (hloc : IsLocalIsometry d π)
    (hfib : ∀ p q : (⊤ : Opens (Minkowski d)), π p = π q ↔
      ∃ γ ∈ frameConj φ (horizGroup Λ), γ • (p : Minkowski d) = q)
    {a : EuclideanSpace ℝ (Fin d)} {s : range (π ∘ frameSlice φ)}
    (γ : Path (sliceProj φ π a) s) :
    ∃ b, sliceProj φ π b = s ∧
      edist a b ≤ pathLength (chartSys d (range (π ∘ frameSlice φ))) γ := by
  obtain ⟨b, c, hb, hc⟩ := exists_lift_sliceProj hcov hfib γ
  have hq := continuous_sliceProj (φ := φ) hloc.continuous
  refine ⟨b, hb, ?_⟩
  rw [pathLength_congr_extend (chartSys d _) γ (c.map hq) (funext fun t => ?_),
    ← pathLength_pulled_eq_of_local (fun z : EuclideanSpace ℝ (Fin d) => ((0 : ℝ), z))
      (chartSys d _) hq (sliceProj_local hloc) c, edist_eq_iInf_pathLength_slice]
  · exact iInf_le _ c
  · simp only [Path.extend, IccExtend, Path.map_coe]
    exact (hc _).symm

/-- **Length balls of `S` are images of Euclidean balls** (`exists_sliceProj_edist_le`, through
the infimum defining the induced length). -/
theorem exists_sliceProj_edist_lt (hcov : IsCoveringMap π) (hloc : IsLocalIsometry d π)
    (hfib : ∀ p q : (⊤ : Opens (Minkowski d)), π p = π q ↔
      ∃ γ ∈ frameConj φ (horizGroup Λ), γ • (p : Minkowski d) = q)
    {a : EuclideanSpace ℝ (Fin d)} {s : InducedLengthSpace d (range (π ∘ frameSlice φ))}
    {r : ENNReal} (h : edist (InducedLengthSpace.toSubtype.symm (sliceProj φ π a)) s < r) :
    ∃ b, InducedLengthSpace.toSubtype.symm (sliceProj φ π b) = s ∧ edist a b < r := by
  obtain ⟨γ, hγ⟩ := iInf_lt_iff.1 h
  obtain ⟨b, hb, hle⟩ := exists_sliceProj_edist_le hcov hloc hfib (s := s) γ
  exact ⟨b, hb, hle.trans_lt hγ⟩

/-- **[11.i], translation spacetimes are Cauchy-complete.** For `M₁ = Γ\𝐌ⁿ`,
`Γ = φ(horizGroup Λ)φ⁻¹`, the projected slice `S = π(φ{t = 0})`: Cauchy (Examples' descent of an
invariant Cauchy surface, transported along `Φ : Γ\𝐌ⁿ ≃ M₁`), spacelike Lipschitz in the charts
of `M₁` (near each point, a chart reads `S` as the isometric image of a piece of `{t = 0}`), and
its induced length is complete with the subspace topology: `q : ℝᵈ → S` is `1`-Lipschitz
(`edist_sliceProj_le`) and lifts short paths to short segments (`exists_sliceProj_edist_lt`), so a
Cauchy sequence of `S` lifts, along a fast subsequence, to a Cauchy sequence of `ℝᵈ`. -/
theorem isCauchyComplete_of_isQuotientOf_frameHoriz {M₁ : FlatSpacetime.{u} d}
    (hq : IsQuotientOf M₁ (frameConj φ (horizGroup Λ)) ⊤) : IsCauchyComplete d M₁ := by
  haveI := hq.isCancelSMul
  haveI := hq.properlyDiscontinuousSMul
  obtain ⟨π, hcov, hloc, Φ, hΦ⟩ := hq.exists_homeomorph
  have hfib : ∀ p q : (⊤ : Opens (Minkowski d)), π p = π q ↔
      ∃ γ ∈ frameConj φ (horizGroup Λ), γ • (p : Minkowski d) = q := fun p q => by
    rw [← hΦ, ← hΦ, Φ.injective.eq_iff, FlatQuotient.proj_eq_proj_iff']
  set S : Set M₁ := range (π ∘ frameSlice φ) with hS
  set Q : EuclideanSpace ℝ (Fin d) → InducedLengthSpace d S :=
    fun x => InducedLengthSpace.toSubtype.symm (sliceProj φ π x) with hQdef
  have hQ : LipschitzWith 1 Q := LipschitzWith.of_edist_le (edist_sliceProj_le hloc)
  have hsurj : ∀ s : InducedLengthSpace d S, ∃ x, Q x = s := by
    rintro ⟨_, x, rfl⟩; exact ⟨x, rfl⟩
  refine ⟨S, ?_, ?_, ?_, ?_⟩
  · -- `S` is a Cauchy surface
    set G0 : Set (Minkowski d) := {q | q.1 = 0} with hG0def
    have hG0 : (minkowski d).IsCauchySurfaceOn ⊤ G0 :=
      (minkowski d).isCauchySurfaceOn_top.2 isCauchySurface_graph_zero
    have h1 := isCauchySurfaceOn_isomImage φ ⊤ (subset_univ _) hG0
    rw [isomImage_top] at h1
    have hinv : ∀ γ ∈ frameConj φ (horizGroup Λ), ∀ p ∈ (fun p => φ • p) '' G0,
        γ • p ∈ (fun p => φ • p) '' G0 := by
      rintro γ hγ _ ⟨p, hp, rfl⟩
      obtain ⟨v, -, hv⟩ := mem_frameConj_horizGroup hγ
      refine ⟨((0 : ℝ), v) + p, ?_, ?_⟩
      · simp only [hG0def, mem_setOf_eq, Prod.fst_add] at hp ⊢; rw [hp]; simp
      · rw [hv, inv_smul_smul]
    have h2 := FlatQuotient.isCauchySurface_image_of_isCauchySurfaceOn _ _
      (actsAcausally_frameConj_horiz φ Λ) (subset_univ _) hinv h1
    have hΦl : IsLocalIsometry d Φ :=
      IsLocalIsometry.of_comp_right (FlatQuotient.isLocalIsometry_proj _ _)
        (FlatQuotient.proj_surjective _ _) (by rw [show Φ ∘ _ = π from funext hΦ]; exact hloc)
    have h3 := ((IsIsometricEmbedding.isEMorphism (d := d) ⟨hΦl, Φ.injective⟩).isCauchySurfaceOn_image_iff
      Φ.injective.injOn le_rfl (V := ⊤) (U := ⊤) (by simp [Φ.surjective.range_eq])
      (subset_univ _)).1 ((flatCausality _ _).isCauchySurfaceOn_top.2 h2)
    rw [(flatCausality _ _).isCauchySurfaceOn_top] at h3
    convert h3 using 1
    ext m
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨FlatQuotient.proj _ _ (frameSlice φ x), ⟨frameSlice φ x, ⟨((0 : ℝ), x), rfl, rfl⟩,
        rfl⟩, hΦ _⟩
    · rintro ⟨_, ⟨y, ⟨p, hp, hpy⟩, rfl⟩, rfl⟩
      refine ⟨p.2, ?_⟩
      change π (frameSlice φ p.2) = Φ (FlatQuotient.proj _ _ y)
      rw [hΦ]
      congr 1
      apply Subtype.ext
      rw [← hpy]
      change φ • ((0 : ℝ), p.2) = φ • p
      congr 1
      exact Prod.ext hp.symm rfl
  · -- `S` is spacelike Lipschitz in the charts of `M₁`
    rintro _ ⟨a, rfl⟩
    set p := frameSlice φ a
    obtain ⟨-, h⟩ := isLocalIsometry_iff_eventually.1 hloc
    obtain ⟨g, hg⟩ := h p
    set e := chartAt (Minkowski d) (π p)
    have hsrc : ∀ᶠ y in 𝓝 p, π y ∈ e.source :=
      hloc.continuous.continuousAt.preimage_mem_nhds
        (e.open_source.mem_nhds (mem_chart_source _ _))
    obtain ⟨W, hWsub, hWo, hpW⟩ := mem_nhds_iff.1 (hg.and hsrc)
    have hWmo : IsOpen (Subtype.val '' W : Set (Minkowski d)) :=
      (⊤ : Opens (Minkowski d)).isOpen.isOpenMap_subtype_val W hWo
    set V : Opens (Minkowski d) := isomImage g ⟨Subtype.val '' W, hWmo⟩ with hVdef
    have hV : ∀ z, z ∈ (V : Set (Minkowski d)) ↔ ∃ y ∈ W, g • (y : Minkowski d) = z := by
      intro z
      rw [hVdef, coe_isomImage]
      constructor
      · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩; exact ⟨y, hy, rfl⟩
      · rintro ⟨y, hy, rfl⟩; exact ⟨y, ⟨y, hy, rfl⟩, rfl⟩
    have hW : ∀ y ∈ W, e (π y) = g • (y : Minkowski d) ∧ π y ∈ e.source := fun y hy => by
      obtain ⟨h1, h2⟩ := hWsub hy
      rw [chartAt_opens_apply] at h1
      exact ⟨h1, h2⟩
    refine ⟨V, (hV _).2 ⟨p, hpW, (hW p hpW).1.symm⟩, fun z hz => ?_, ?_⟩
    · obtain ⟨y, hy, rfl⟩ := (hV z).1 hz
      rw [← (hW y hy).1]
      exact e.map_source (hW y hy).2
    have hset : e '' (S ∩ e.source) ∩ V =
        (g * φ) • graphOver univ (fun _ : EuclideanSpace ℝ (Fin d) => (0 : ℝ)) ∩
          (V : Set (Minkowski d)) := by
      ext z
      constructor
      · rintro ⟨⟨m, ⟨hmS, hmsrc⟩, rfl⟩, hzV⟩
        refine ⟨?_, hzV⟩
        obtain ⟨y, hy, hyz⟩ := (hV _).1 hzV
        have hm : π y = m := e.injOn (hW y hy).2 hmsrc ((hW y hy).1.trans hyz)
        obtain ⟨x', hx'⟩ := hmS
        obtain ⟨y', rfl⟩ := exists_frameSlice_of_proj_eq hfib (hm.trans hx'.symm)
        rw [← hyz]
        exact ⟨((0 : ℝ), y'), ⟨trivial, rfl⟩, by simp [frameSlice, mul_smul]⟩
      · rintro ⟨⟨w, hw, rfl⟩, hzV⟩
        obtain ⟨y, hy, hyz⟩ := (hV _).1 hzV
        have hw' : w = ((0 : ℝ), w.2) := Prod.ext hw.2 rfl
        have hyw : y = frameSlice φ w.2 := by
          apply Subtype.ext
          simp only [mul_smul] at hyz
          rw [(smul_left_cancel_iff g).1 hyz, hw']
          rfl
        subst hyw
        refine ⟨⟨π (frameSlice φ w.2), ⟨⟨w.2, rfl⟩, (hW _ hy).2⟩, ?_⟩, hzV⟩
        rw [(hW _ hy).1, ← hyz]
    change IsSpacelikeLipschitzIn V (e '' (S ∩ e.source) ∩ V)
    rw [hset]
    have h0 := (isSpacelikeLipschitzIn_graphOver (d := d) (c := 0) zero_lt_one
      (LipschitzWith.const (0 : ℝ))).smul isom_strongMorphism (g * φ)
    refine h0.restrict fun z _ => ?_
    rw [← SetLike.mem_coe, coe_smulOpens]
    exact ⟨(g * φ)⁻¹ • z, trivial, smul_inv_smul _ _⟩
  · -- completeness
    refine EMetric.complete_of_convergent_controlled_sequences (fun n => 1 / 2 ^ n)
      (fun n => ENNReal.div_pos_iff.2 ⟨one_ne_zero, ENNReal.pow_ne_top ENNReal.ofNat_ne_top⟩)
      fun u hu => ?_
    obtain ⟨a0, ha0⟩ := hsurj (u 0)
    have step : ∀ n (x : {x : EuclideanSpace ℝ (Fin d) // Q x = u n}),
        ∃ y : {y : EuclideanSpace ℝ (Fin d) // Q y = u (n + 1)},
          edist (x : EuclideanSpace ℝ (Fin d)) y < 1 / 2 ^ n := by
      rintro n ⟨x, hx⟩
      have h := hu n n (n + 1) le_rfl (by omega)
      rw [← hx] at h
      obtain ⟨b, hb, hlt⟩ := exists_sliceProj_edist_lt hcov hloc hfib h
      exact ⟨⟨b, hb⟩, hlt⟩
    choose g hg using step
    let a : (n : ℕ) → {x : EuclideanSpace ℝ (Fin d) // Q x = u n} := fun n =>
      Nat.rec (motive := fun n => {x : EuclideanSpace ℝ (Fin d) // Q x = u n}) ⟨a0, ha0⟩
        (fun n x => g n x) n
    have ha : ∀ n, edist (a n : EuclideanSpace ℝ (Fin d)) (a (n + 1)) ≤ 1 / 2 ^ n :=
      fun n => (hg n (a n)).le
    have hc : CauchySeq fun n => (a n : EuclideanSpace ℝ (Fin d)) :=
      cauchySeq_of_edist_le_geometric_two 1 ENNReal.one_ne_top ha
    obtain ⟨b, hb⟩ := cauchySeq_tendsto_of_complete hc
    exact ⟨Q b, ((hQ.continuous.tendsto b).comp hb).congr fun n => (a n).2⟩
  · -- the length topology is finer than the subspace topology
    rw [continuous_iff_continuousAt]
    intro s
    obtain ⟨x, rfl⟩ := hsurj s
    refine tendsto_nhds.2 fun N hN hxN => ?_
    have hpre : (π ∘ frameSlice φ) ⁻¹' N ∈ 𝓝 x :=
      (hloc.continuous.comp (continuous_frameSlice φ)).continuousAt.preimage_mem_nhds
        (hN.mem_nhds hxN)
    obtain ⟨ε, hε, hball⟩ := EMetric.mem_nhds_iff.1 hpre
    filter_upwards [Metric.eball_mem_nhds (Q x) hε] with y hy
    rw [Metric.mem_eball, edist_comm] at hy
    obtain ⟨b, rfl, hb⟩ := exists_sliceProj_edist_lt hcov hloc hfib hy
    exact hball (by rw [Metric.mem_eball, edist_comm]; exact hb)

end TranslationComplete

/-- **[11.i], translation spacetimes are AMGH** (l.3616–3618: `Ω₀ = 𝐌ⁿ`): GH
(`gh_of_isTranslationSpacetime`), Cauchy-completeness (`isCauchyComplete_of_isQuotientOf_frameHoriz`,
the projected slice `π(φ{t = 0})`) and absolute maximality (`absMax_of_isTranslationSpacetime`, the
lifting argument, against all targets). **Proved, no `sorry`** (`_hE` unused). -/
theorem amgh_of_isTranslationSpacetime {d₁ : ℕ} (_hE : BarbotExternals d₁)
    (M₁ : FlatSpacetime.{0} d₁) (_h : IsTranslationSpacetime M₁) :
    AMGH (CauchyCompleteClass d₁) M₁ := by
  refine ⟨gh_of_isTranslationSpacetime _h, ?_, absMax_of_isTranslationSpacetime _ _h⟩
  obtain ⟨φ, Λ, -, hq⟩ := _h
  exact isCauchyComplete_of_isQuotientOf_frameHoriz hq

/-- **[11.i], Misner spacetimes are AMGH** (l.3620–3626), with F1's nonzero boost (G2), which is a
field of `IsMisnerSpacetime`. Absolute maximality is proved (`surjective_of_isQuotientOf_misner`,
both wedges; it rests on the bridge only), GH on both wedges (`gh_of_isQuotientOf_misnerWedge`,
`gh_of_isQuotientOf_misnerWedgePast`), Cauchy-completeness by L4
(`Cla.isCauchyComplete_of_isQuotientOf_regular`: the wedges are `Ω^±(misnerΛ)`). No `sorry`. -/
theorem amgh_of_isMisnerSpacetime {e : ℕ} (_hE : BarbotExternals (e + 1))
    (M₁ : FlatSpacetime.{0} (e + 1)) (_h : IsMisnerSpacetime M₁) :
    AMGH (CauchyCompleteClass (e + 1)) M₁ := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨φ, L, hL, -, hq | hq⟩ := _h
    · exact gh_of_isQuotientOf_misnerWedge hq
    · exact gh_of_isQuotientOf_misnerWedgePast hq
  · obtain ⟨φ, L, -, -, hq | hq⟩ := _h
    · exact Cla.isCauchyComplete_of_isQuotientOf_regular
        (Or.inl ⟨misnerRegular e, fun _ => Iff.rfl⟩) φ hq
    · refine Cla.isCauchyComplete_of_isQuotientOf_regular (Λ := misnerΛ e)
        (Or.inr ⟨?_, (misnerRegular e).two, fun p => ?_⟩) φ hq
      · refine ⟨⟨((-1 : ℝ), 0), mem_omegaMinus_misnerΛ.2 ⟨?_, ?_⟩⟩, ?_⟩
        · exact div_neg_of_neg_of_pos (by simp) (by positivity)
        · exact div_pos (by simp) (by positivity)
        · have : omegaMinus (misnerΛ e) = (misnerWedgePast e : Set (Minkowski (e + 1))) :=
            Set.ext fun _ => mem_omegaMinus_misnerΛ
          rw [this]; exact (misnerWedgePast e).isOpen
      · exact mem_omegaMinus_misnerΛ.symm
  · intro N hN hCC f hf
    obtain ⟨φ, L, -, ⟨x, hxL, hx⟩, hq | hq⟩ := _h
    · exact surjective_of_isQuotientOf_misner hxL hx one_ne_zero (fun _ => mem_misnerWedge_iff) hq
        N hN hCC hf.1
    · exact surjective_of_isQuotientOf_misner hxL hx (by norm_num)
        (fun _ => mem_misnerWedgePast_iff) hq N hN hCC hf.1

/-! ### [11.i] GH of family (b) -/

/-- **A discrete group without global fixed point has a loxodromic element** (the step of
Def 4.18 / l.1212–1214 that makes `Ω^±(Λ(Γ))` a regular domain): otherwise Benoist's theorem
(`BenoistNoLox`; an external here, proved as `benoistNoLox` in `Flat/GromovProof`, DEC-111) gives
a finite-index `H ≤ L(Γ)` fixing a nonzero future causal `v`; the
sum `w` of the finite orbit `L(Γ) v` is nonzero, future causal and `L(Γ)`-fixed, so either timelike
(a fixed point inside) or null (its direction is a fixed point of `𝒮`). -/
theorem exists_loxodromic_of_not_hasGlobalFixedPoint (hB : BenoistNoLox d)
    {Γ : Subgroup (isom d)} (hfix : ¬HasGlobalFixedPoint (linearImage Γ)) :
    ∃ γ ∈ Γ, IsLoxodromic (linOf γ) := by
  by_contra hno
  push Not at hno
  apply hfix
  set G := linearImage Γ with hGdef
  have hG : ∀ A ∈ G, ¬IsLoxodromic (A : Minkowski d ≃ₗ[ℝ] Minkowski d) := by
    rintro A ⟨γ, hγ, rfl⟩
    exact hno γ hγ
  obtain ⟨H, hHG, hidx, hfixH⟩ := hB G hG
  obtain ⟨v, hvc, hv0, hvH⟩ : ∃ v : Minkowski d, IsFutureCausal v ∧ 0 < v.1 ∧
      ∀ A ∈ H, (A : Minkowski d ≃ₗ[ℝ] Minkowski d) v = v := by
    rcases hfixH with ⟨v, hv, hvH⟩ | ⟨v, hv0, hv, hvH⟩
    · rcases isFutureTimelike_or_neg hv with h | h
      · exact ⟨v, ⟨h.1.le, h.2.le⟩, h.1, hvH⟩
      · exact ⟨-v, ⟨h.1.le, h.2.le⟩, h.1, fun A hA => by rw [map_neg, hvH A hA]⟩
    · have h1 : v.1 ≠ 0 := fun h => hv0 (eq_zero_of_fst_eq_zero h hv.le)
      rcases lt_or_gt_of_ne h1 with h | h
      · exact ⟨-v, ⟨by simp; linarith, by simpa using hv.le⟩, by simp; linarith,
          fun A hA => by rw [map_neg, hvH A hA]⟩
      · exact ⟨v, ⟨h.le, hv.le⟩, h, hvH⟩
  haveI : (H.subgroupOf G).FiniteIndex := ⟨hidx⟩
  letI := Fintype.ofFinite (G ⧸ H.subgroupOf G)
  let f : G ⧸ H.subgroupOf G → Minkowski d :=
    Quotient.lift (fun g : G => (((g : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d)) v) (by
      intro a b hab
      have hab' : a⁻¹ * b ∈ H.subgroupOf G := QuotientGroup.leftRel_apply.1 hab
      rw [Subgroup.mem_subgroupOf] at hab'
      have h := hvH _ hab'
      change ((a : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) v =
        ((b : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) v
      have e : ((b : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) =
          ((a : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) *
            (((a⁻¹ * b : G) : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) := by
        simp
      rw [e, LinearEquiv.mul_apply, h])
  have hf : ∀ g : G, f (g : G ⧸ H.subgroupOf G) =
      (((g : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d)) v := fun _ => rfl
  have hfc : ∀ c, IsFutureCausal (f c) ∧ 0 < (f c).1 := by
    rintro ⟨g⟩
    change IsFutureCausal (f (g : G ⧸ H.subgroupOf G)) ∧ 0 < (f (g : G ⧸ H.subgroupOf G)).1
    rw [hf]
    have hc := lorentz.isFutureCausal_apply (g : lorentz d).2 hvc
    refine ⟨hc, lt_of_le_of_ne hc.1 fun h0 => ?_⟩
    have := eq_zero_of_fst_eq_zero h0.symm hc.2
    rw [LinearEquiv.map_eq_zero_iff] at this
    rw [this] at hv0
    exact lt_irrefl _ hv0
  set w := ∑ c, f c with hwdef
  have hw : IsFutureCausal w := by
    rw [hwdef]
    refine Finset.sum_induction _ IsFutureCausal (fun a b ha hb => isFutureCausal_add ha hb)
      ⟨le_rfl, by simp [minkQ]⟩ fun c _ => (hfc c).1
  have hw1 : 0 < w.1 := by
    rw [hwdef, Prod.fst_sum]
    exact Finset.sum_pos (fun c _ => (hfc c).2) ⟨((1 : G) : G ⧸ H.subgroupOf G), Finset.mem_univ _⟩
  have hfixw : ∀ A ∈ G, (A : Minkowski d ≃ₗ[ℝ] Minkowski d) w = w := by
    intro A hA
    set a : G := ⟨A, hA⟩
    have hperm : ∀ c, (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (f c) = f (a • c) := by
      rintro ⟨g⟩
      change (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (f (g : G ⧸ H.subgroupOf G)) =
        f (a • (g : G ⧸ H.subgroupOf G))
      rw [MulAction.Quotient.smul_mk, hf, hf]
      rfl
    rw [hwdef, map_sum]
    simp only [hperm]
    exact Equiv.sum_comp (MulAction.toPerm a) f
  rcases lt_or_eq_of_le hw.2 with hlt | heq
  · exact Or.inl ⟨w, hlt, hfixw⟩
  · right
    have hn : ‖w.2‖ = w.1 := by
      have h2 : ‖w.2‖ ^ 2 = w.1 ^ 2 := by unfold minkQ at heq; linarith
      exact (sq_eq_sq₀ (norm_nonneg _) hw1.le).1 h2
    let u : PenroseSphere d := ⟨(w.1)⁻¹ • w.2, by
      rw [mem_sphere_zero_iff_norm, norm_smul, hn, norm_inv, Real.norm_eq_abs,
        abs_of_pos hw1, inv_mul_cancel₀ hw1.ne']⟩
    have hnu : nullVec u = (w.1)⁻¹ • w :=
      Prod.ext (by simp [nullVec, hw1.ne']) rfl
    refine ⟨u, fun A hA => ?_⟩
    have hAn : (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u) = nullVec u := by
      rw [hnu, map_smul, hfixw A hA]
    apply Subtype.ext
    simp only [lorentzSphere, lorentzScale, hAn]
    simp [nullVec]


/-- **[11.i], family (b) on the future side: GH in the `IsQuotientOf` form.** `Γ` has a
loxodromic element (`exists_loxodromic_of_not_hasGlobalFixedPoint`), so `Λ(Γ)` is a regular set
with two directions (`cosmoRegular_limitSetJ`) preserved by `Γ` (`preservesOmega_limitSetJ`);
Examples' `gh_quotient_omegaPlus`, with the instances from the presentation, and
`gh_of_isQuotientOf`. -/
theorem gh_of_isQuotientOf_limitOpensPlus {M₁ : FlatSpacetime.{u} d} (hB : BenoistNoLox d)
    {Γ : Subgroup (isom d)} (hnf : ¬HasGlobalFixedPoint (linearImage Γ))
    (hq : IsQuotientOf M₁ Γ (limitOpensPlus Γ)) : GH M₁ := by
  obtain ⟨γ₀, hγ₀, hlox₀⟩ := exists_loxodromic_of_not_hasGlobalFixedPoint hB hnf
  obtain ⟨π₀, -, -, hπs₀, -⟩ := hq.quot
  obtain ⟨m₀⟩ := (inferInstance : Nonempty M₁)
  obtain ⟨p₀, -⟩ := hπs₀ m₀
  have hF : FutureRegular (limitSetJ Γ) :=
    ⟨⟨p₀, p₀.2⟩, isOpen_omegaPlus_of_isClosed (isClosed_limitSetJ Γ)⟩
  have hc := cosmoRegular_limitSetJ hγ₀ hlox₀ hF
  have hq' : IsQuotientOf M₁ Γ hc.regular.opens := hq
  haveI := hq'.invariant
  haveI := hq'.isCancelSMul
  haveI := hq'.properlyDiscontinuousSMul
  exact gh_of_isQuotientOf hq' (gh_quotient_omegaPlus (h := hc) (preservesOmega_limitSetJ Γ))

/-! ### Time reversal, for the past regular domains -/

section TimeReversal

variable (d) in
/-- **Time reversal** `(t, x) ↦ (−t, x)` (not in `Isom(𝐌ⁿ)`: it reverses the time orientation). -/
noncomputable def timeRev : Minkowski d ≃ₗ[ℝ] Minkowski d :=
  (LinearEquiv.neg ℝ).prodCongr (LinearEquiv.refl ℝ _)

@[simp] theorem timeRev_apply (p : Minkowski d) : timeRev d p = (-p.1, p.2) := rfl

@[simp] theorem timeRev_timeRev (p : Minkowski d) : timeRev d (timeRev d p) = p := by
  simp

theorem minkQ_timeRev (v : Minkowski d) : minkQ (timeRev d v) = minkQ v := by
  simp [minkQ]

theorem continuous_timeRev : Continuous (timeRev d) := by
  change Continuous fun p : Minkowski d => (-p.1, p.2); fun_prop

/-- Time reversal reverses the causal relation of `𝐌ⁿ`. -/
theorem le_top_timeRev {p q : Minkowski d} (h : (minkowski d).le ⊤ p q) :
    (minkowski d).le ⊤ (timeRev d q) (timeRev d p) := by
  rw [le_top_iff_minkQ] at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨by simp only [Prod.fst_sub, timeRev_apply] at h1 ⊢; linarith, ?_⟩
  rw [← map_sub, minkQ_timeRev, show p - q = -(q - p) by abel]
  have : minkQ (-(q - p)) = minkQ (q - p) := by
    simp only [minkQ, Prod.fst_neg, Prod.snd_neg, norm_neg, neg_sq]
  rw [this]; exact h2

theorem det_timeRev_mul_self :
    LinearMap.det (timeRev d : Minkowski d →ₗ[ℝ] Minkowski d) *
      LinearMap.det (timeRev d : Minkowski d →ₗ[ℝ] Minkowski d) = 1 := by
  rw [← LinearMap.det_comp]
  have : (timeRev d : Minkowski d →ₗ[ℝ] Minkowski d) ∘ₗ (timeRev d : Minkowski d →ₗ[ℝ] Minkowski d)
      = LinearMap.id := LinearMap.ext fun p => by simp
  rw [this, LinearMap.det_id]

/-- The conjugate `τ g τ` of an isometry by the time reversal is an isometry. -/
theorem revConj_mem (g : isom d) :
    (timeRev d).toAffineEquiv.trans
      ((g : Minkowski d ≃ᵃ[ℝ] Minkowski d).trans (timeRev d).toAffineEquiv) ∈ isom d := by
  rw [mem_isom_iff]
  set A := (g : Minkowski d ≃ᵃ[ℝ] Minkowski d).linear
  have hA : A ∈ lorentz d := g.2
  have hlin : ((timeRev d).toAffineEquiv.trans
      ((g : Minkowski d ≃ᵃ[ℝ] Minkowski d).trans (timeRev d).toAffineEquiv)).linear =
      (timeRev d).trans (A.trans (timeRev d)) := rfl
  rw [hlin]
  have hQ : ∀ v, minkQ ((timeRev d).trans (A.trans (timeRev d)) v) = minkQ v := fun v => by
    simp only [LinearEquiv.trans_apply]
    rw [minkQ_timeRev, lorentz.minkQ_apply hA, minkQ_timeRev]
  set e : Minkowski d := ((1 : ℝ), 0)
  have he : IsFutureTimelike e := ⟨one_pos, by simp [e, minkQ]⟩
  have hAe := lorentz.isFutureTimelike_apply hA he
  refine mem_lorentz_of_future hQ he ?_ ?_
  · have h1 : timeRev d e = -e := Prod.ext (by simp [e]) (by simp [e])
    simp only [LinearEquiv.trans_apply, h1, map_neg, timeRev_apply]
    refine ⟨by simpa using hAe.1, ?_⟩
    have := hAe.2
    simp only [minkQ, Prod.fst_neg, Prod.snd_neg, norm_neg, neg_sq] at this ⊢
    simpa using this
  · rw [LinearEquiv.coe_trans, LinearEquiv.coe_trans, LinearMap.det_comp, LinearMap.det_comp,
      lorentz.det_eq_one hA, mul_one]
    exact det_timeRev_mul_self

variable (d) in
/-- **Conjugation by the time reversal**, `g ↦ τ g τ`, an automorphism of `Isom(𝐌ⁿ)`. -/
noncomputable def revConj : isom d →* isom d where
  toFun g := ⟨_, revConj_mem g⟩
  map_one' := Subtype.ext (AffineEquiv.ext fun p => by
    change timeRev d ((1 : isom d) • timeRev d p) = p
    rw [one_smul, timeRev_timeRev])
  map_mul' g h := Subtype.ext (AffineEquiv.ext fun p => by
    change timeRev d ((g * h) • timeRev d p) =
      timeRev d (g • timeRev d (timeRev d (h • timeRev d p)))
    rw [timeRev_timeRev, mul_smul])

theorem revConj_smul (g : isom d) (p : Minkowski d) :
    revConj d g • p = timeRev d (g • timeRev d p) := rfl

theorem revConj_revConj (g : isom d) : revConj d (revConj d g) = g :=
  Subtype.ext (AffineEquiv.ext fun p => by
    change timeRev d (timeRev d (g • timeRev d (timeRev d p))) = g • p
    rw [timeRev_timeRev, timeRev_timeRev])

theorem revConj_injective : Injective (revConj d) := fun g h e => by
  rw [← revConj_revConj g, e, revConj_revConj]


/-- The antipode of the Penrose sphere. -/
def penroseNeg (u : PenroseSphere d) : PenroseSphere d :=
  ⟨-(u : EuclideanSpace ℝ (Fin d)), by
    rw [mem_sphere_zero_iff_norm, norm_neg]; exact norm_penroseSphere u⟩

/-- **[11.i], family (b) on the past side: GH in the `IsQuotientOf` form**, by time reversal:
`τ = (t, x) ↦ (−t, x)` carries `Ω⁻(Λ(Γ))` onto the future regular domain `Ω⁺(Λ')`, `Λ' = −Λ(Γ)`
(two directions, from a loxodromic element), preserved by `Γ' = τΓτ ≤ Isom(𝐌ⁿ)` (`revConj`), whose
action is free and properly discontinuous through the covering `π ∘ τ`; the acausality and the
finiteness of `{γ | x ≤ γ y}` on `Ω⁻` are those of `Γ'` on `Ω⁺(Λ')` read backwards (Examples'
`actsAcausally_of_preservesOmega`, `finite_le_of_preservesOmega`; `Ω⁺(Λ')` is future complete, so
`≤` of `𝐌ⁿ` is its own), `Ω⁻` is GH in `𝐌ⁿ` (`PastRegular.globallyHyperbolicOn`), and
`gh_toFlatSpacetime`, `gh_of_isQuotientOf`. -/
theorem gh_of_isQuotientOf_limitOpensMinus {M₁ : FlatSpacetime.{u} d} (hB : BenoistNoLox d)
    {Γ : Subgroup (isom d)} (hnf : ¬HasGlobalFixedPoint (linearImage Γ))
    (hq : IsQuotientOf M₁ Γ (limitOpensMinus Γ)) : GH M₁ := by
  obtain ⟨γ₀, hγ₀, hlox₀⟩ := exists_loxodromic_of_not_hasGlobalFixedPoint hB hnf
  obtain ⟨π, hcov, -, hπs, hfib⟩ := hq.quot
  obtain ⟨m₀⟩ := (inferInstance : Nonempty M₁)
  obtain ⟨p₀, -⟩ := hπs m₀
  haveI := hq.invariant
  haveI := isCancelSMul_of_isCoveringMap hcov hfib
  haveI := properlyDiscontinuousSMul_of_isCoveringMap hcov hfib
  have hmem : ∀ γ ∈ Γ, ∀ x, γ • x ∈ ((limitOpensMinus Γ) : Set (Minkowski d)) ↔ x ∈ ((limitOpensMinus Γ) : Set (Minkowski d)) :=
    fun γ hγ x => by
      constructor
      · intro hx
        have := (hq.inv γ⁻¹ (Γ.inv_mem hγ)).subset ⟨_, hx, rfl⟩
        simpa using this
      · intro hx; exact (hq.inv γ hγ).subset ⟨x, hx, rfl⟩
  -- the time-reversed data `Λ' = −Λ`, `Γ' = τΓτ`, `Ω⁺(Λ') = τ Ω⁻(Λ)`
  set Λ' : Set (PenroseSphere d × ℝ) := (fun w => (penroseNeg w.1, -w.2)) '' limitSetJ Γ
  have hΛ' : ∀ p, p ∈ omegaPlus Λ' ↔ timeRev d p ∈ omegaMinus (limitSetJ Γ) := fun p => by
    rw [mem_omegaPlus, mem_omegaMinus]
    constructor
    · intro h w hw
      have := h _ ⟨w, hw, rfl⟩
      simp only [minkB_nullVec, penroseNeg, inner_neg_left, timeRev_apply] at this ⊢
      linarith
    · rintro h _ ⟨w, hw, rfl⟩
      have := h w hw
      simp only [minkB_nullVec, penroseNeg, inner_neg_left, timeRev_apply] at this ⊢
      linarith
  have hF' : FutureRegular Λ' := by
    refine ⟨⟨timeRev d p₀, (hΛ' _).2 (by rw [timeRev_timeRev]; exact p₀.2)⟩, ?_⟩
    rw [show omegaPlus Λ' = timeRev d ⁻¹' omegaMinus (limitSetJ Γ) from Set.ext hΛ']
    exact (isOpen_omegaMinus_of_isClosed (isClosed_limitSetJ Γ)).preimage continuous_timeRev
  obtain ⟨w₁, hw₁, w₂, hw₂, -, -, hne⟩ := exists_two_loxRepSet hγ₀ hlox₀
  have hc' : CosmoRegular Λ' := ⟨hF', _, ⟨w₁, subset_closure hw₁, rfl⟩, _,
    ⟨w₂, subset_closure hw₂, rfl⟩, fun h => hne (Subtype.ext (neg_injective
      (congrArg Subtype.val h)))⟩
  set Γ' := Γ.map (revConj d) with hΓ'
  have hP' : PreservesOmega Λ' Γ' := by
    rintro _ ⟨γ, hγ, rfl⟩
    ext p
    simp only [mem_preimage]
    rw [hΛ', hΛ', revConj_smul, timeRev_timeRev]
    exact hmem γ hγ _
  haveI : FlatQuotient.Invariant Γ' hc'.regular.opens := hP'.invariant (h := hc')
  -- `τ : Ω⁺(Λ') ≃ₜ Ω⁻(Λ)`, and the presentation it induces
  let τh : Minkowski d ≃ₜ Minkowski d :=
    { toFun := timeRev d, invFun := timeRev d, left_inv := timeRev_timeRev,
      right_inv := timeRev_timeRev, continuous_toFun := continuous_timeRev,
      continuous_invFun := continuous_timeRev }
  let ρ : hc'.regular.opens ≃ₜ (limitOpensMinus Γ) := τh.subtype fun p => hΛ' p
  have hρ : ∀ z, (ρ z : Minkowski d) = timeRev d z := fun _ => rfl
  have hcov' : IsCoveringMap (π ∘ ρ) := hcov.comp_homeomorph ρ
  have hfib' : ∀ a b : hc'.regular.opens, (π ∘ ρ) a = (π ∘ ρ) b ↔
      ∃ γ' ∈ Γ', γ' • (a : Minkowski d) = b := by
    intro a b
    rw [comp_apply, comp_apply, hfib]
    constructor
    · rintro ⟨γ, hγ, h⟩
      refine ⟨revConj d γ, ⟨γ, hγ, rfl⟩, ?_⟩
      rw [revConj_smul, ← hρ a, h, hρ, timeRev_timeRev]
    · rintro ⟨_, ⟨γ, hγ, rfl⟩, h⟩
      refine ⟨γ, hγ, ?_⟩
      rw [hρ, hρ, ← h, revConj_smul, timeRev_timeRev]
  haveI := isCancelSMul_of_isCoveringMap hcov' hfib'
  haveI := properlyDiscontinuousSMul_of_isCoveringMap hcov' hfib'
  -- `Ω⁺(Λ')` is future complete, so `≤` of `𝐌ⁿ` between its points is its own
  have hlift : ∀ a b : hc'.regular.opens, (minkowski d).le ⊤ (a : Minkowski d) b →
      (flatCausality d hc'.regular.opens).le ⊤ a b := fun a b h =>
    (flat_le_top_subtype_iff _ _ _).2 (le_of_le_top_of_segment_subset h fun y hy =>
      Jplus_omegaPlus_subset Λ' ⟨a, a.2, (le_top_of_mem_segment h hy).1⟩)
  have hinvConj : ∀ γ : isom d, (revConj d γ)⁻¹ = revConj d γ⁻¹ := fun γ => (map_inv _ γ).symm
  -- acausality of `Γ` on `Ω⁻`, from that of `Γ'` on `Ω⁺(Λ')`
  have hac : FlatQuotient.ActsAcausally Γ (limitOpensMinus Γ) := by
    rintro ⟨γ, hγ⟩ hne x hle
    have h1 := le_top_timeRev ((minkowski d).le_mono le_top ((flat_le_top_subtype_iff _ _ _).1 hle))
    set γ' : Γ' := ⟨revConj d γ, γ, hγ, rfl⟩
    have hne' : γ'⁻¹ ≠ 1 := by
      rw [ne_eq, inv_eq_one]
      intro h
      apply hne
      apply Subtype.ext
      apply revConj_injective
      have h' : revConj d γ = 1 := congrArg Subtype.val h
      simpa using h'
    set y : hc'.regular.opens := ρ.symm ((⟨γ, hγ⟩ : Γ) • x)
    have hy : ((γ'⁻¹ • y : hc'.regular.opens) : Minkowski d) = timeRev d x := by
      rw [FlatQuotient.coe_smul]
      change (revConj d γ)⁻¹ • timeRev d (γ • (x : Minkowski d)) = _
      rw [hinvConj, revConj_smul, timeRev_timeRev, inv_smul_smul]
    refine actsAcausally_of_preservesOmega (h := hc') hP' γ'⁻¹ hne' y (hlift _ _ ?_)
    rw [hy]
    exact h1
  -- finiteness of `{γ | x ≤ γ y}` on `Ω⁻`
  have hfin : ∀ x y : (limitOpensMinus Γ), {γ : Γ | (flatCausality d (limitOpensMinus Γ)).le ⊤ x (γ • y)}.Finite := by
    intro x y
    have hF := finite_le_of_preservesOmega (h := hc') hP' (ρ.symm y) (ρ.symm x)
    refine (hF.preimage (f := fun γ : Γ => (⟨revConj d γ, γ, γ.2, rfl⟩ : Γ')⁻¹)
      fun a _ b _ h => ?_).subset fun γ hγ => ?_
    · have := congrArg Subtype.val (inv_injective h)
      exact Subtype.ext (revConj_injective this)
    · have h1 := le_top_timeRev ((minkowski d).le_mono le_top
        ((flat_le_top_subtype_iff _ _ _).1 hγ))
      refine hlift _ _ ?_
      have h2 := (isom_le_iff (revConj d γ)⁻¹ ⊤ _ _).2 h1
      rw [isomImage_top] at h2
      convert h2 using 1
      · change timeRev d (y : Minkowski d) = _
        rw [FlatQuotient.coe_smul, hinvConj, revConj_smul, timeRev_timeRev, inv_smul_smul]
      · rw [FlatQuotient.coe_smul]; rfl
  have hPR : PastRegular (limitSetJ Γ) :=
    ⟨⟨p₀, p₀.2⟩, isOpen_omegaMinus_of_isClosed (isClosed_limitSetJ Γ)⟩
  have hconn : IsConnected ((limitOpensMinus Γ) : Set (Minkowski d)) := (convex_omegaMinus _).isConnected ⟨p₀, p₀.2⟩
  exact gh_of_isQuotientOf hq (FlatQuotient.gh_toFlatSpacetime Γ (limitOpensMinus Γ) hconn hac
    (globallyHyperbolic_subtype _ hPR.globallyHyperbolicOn) hfin)

end TimeReversal

/-- **[11.i], family (b) is AMGH** (l.3620–3626, "twisted products of Cauchy-hyperbolic spacetimes
by flat torii", in the central-extension form, DEC-44). Absolute maximality is proved
(`surjective_of_isQuotientOf_limitOpensPlus`, `…Minus`; it rests on the bridge only), GH on both
sides (`gh_of_isQuotientOf_limitOpensPlus`, `…Minus`, through Benoist's `_hE.benoist`, which gives
`Γ` a loxodromic element), Cauchy-completeness by L4 (`Cla.isCauchyComplete_of_isQuotientOf_regular`,
`Λ(Γ)` regular through the same loxodromic element). No `sorry`. -/
theorem amgh_of_isCHCentralExtension {d₁ : ℕ} (_hE : BarbotExternals d₁)
    (M₁ : FlatSpacetime.{0} d₁) (_h : IsCHCentralExtension M₁) :
    AMGH (CauchyCompleteClass d₁) M₁ := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨Γ, E, -, -, -, -, -, hnf, ⟨hq, -⟩ | ⟨hq, -⟩⟩ := _h
    · exact gh_of_isQuotientOf_limitOpensPlus (_hE.benoist d₁ le_rfl) hnf hq
    · exact gh_of_isQuotientOf_limitOpensMinus (_hE.benoist d₁ le_rfl) hnf hq
  · obtain ⟨Γ, E, -, -, -, -, -, hnf, ⟨hq, -⟩ | ⟨hq, -⟩⟩ := _h
    · obtain ⟨γ₀, hγ₀, hlox₀⟩ := exists_loxodromic_of_not_hasGlobalFixedPoint
        (_hE.benoist d₁ le_rfl) hnf
      obtain ⟨π₀, -, -, hπs₀, -⟩ := hq.quot
      obtain ⟨m₀⟩ := (inferInstance : Nonempty M₁)
      obtain ⟨p₀, -⟩ := hπs₀ m₀
      have hc := cosmoRegular_limitSetJ hγ₀ hlox₀
        ⟨⟨p₀, p₀.2⟩, isOpen_omegaPlus_of_isClosed (isClosed_limitSetJ Γ)⟩
      have hq' : IsQuotientOf M₁ (frameConj 1 Γ) (isomImage 1 (limitOpensPlus Γ)) := by
        rw [frameConj_one, isomImage_one]; exact hq
      exact Cla.isCauchyComplete_of_isQuotientOf_regular (Or.inl ⟨hc, fun _ => Iff.rfl⟩) 1 hq'
    · obtain ⟨γ₀, hγ₀, hlox₀⟩ := exists_loxodromic_of_not_hasGlobalFixedPoint
        (_hE.benoist d₁ le_rfl) hnf
      obtain ⟨π₀, -, -, hπs₀, -⟩ := hq.quot
      obtain ⟨m₀⟩ := (inferInstance : Nonempty M₁)
      obtain ⟨p₀, -⟩ := hπs₀ m₀
      obtain ⟨w₁, hw₁, w₂, hw₂, -, -, hne⟩ := exists_two_loxRepSet hγ₀ hlox₀
      have hq' : IsQuotientOf M₁ (frameConj 1 Γ) (isomImage 1 (limitOpensMinus Γ)) := by
        rw [frameConj_one, isomImage_one]; exact hq
      exact Cla.isCauchyComplete_of_isQuotientOf_regular
        (Or.inr ⟨⟨⟨p₀, p₀.2⟩, isOpen_omegaMinus_of_isClosed (isClosed_limitSetJ Γ)⟩,
          ⟨w₁, subset_closure hw₁, w₂, subset_closure hw₂, hne⟩, fun _ => Iff.rfl⟩) 1 hq'
  · intro N hN hCC f hf
    obtain ⟨Γ, E, -, -, -, -, -, -, ⟨hq, -⟩ | ⟨hq, -⟩⟩ := _h
    · exact surjective_of_isQuotientOf_limitOpensPlus hq N hN hCC hf.1
    · exact surjective_of_isQuotientOf_limitOpensMinus hq N hN hCC hf.1

/-- **[11.i] for the unipotent family, with G3** (l.3570–3571, l.3629–3679; G1 is the unbounded
case l.3678–3679): an LTP `B` over a unipotent spacetime `M₁`, presented as the quotient of a
convex `Ω`, tamely embeds in an LTP `B₂` over an **absolutely maximal** unipotent spacetime `M₂`.
No `sorry`: convex LTP data (L1), the maximal envelope `M₂` in its corrected form (L5, finding 10),
GH and Cauchy-completeness of `M₂` (L6), its absolute maximality by the lifting glue of this file
(`exists_lift_of_isQuotientOf`, `exists_deck_of_lift`, `surjective_of_lift_of_range_subset`) and
L5's envelope maximality, the enlarged LTP `B₂` (L7), and tameness of `B ↪ B₂` (L3). The
hypotheses `_hq`, `_hcv` are not needed (L1 supplies a convex presentation). -/
theorem exists_absMax_unipotent_ltp {e : ℕ} (_hE : BarbotExternals d) (_he : e + 1 ≤ d)
    (M₁ : FlatSpacetime.{0} (e + 1)) (_hU : IsUnipotentSpacetime M₁) (B : FlatSpacetime.{0} d)
    (_hB : IsLTPOver B M₁) {Γ : Subgroup (isom d)} {Ω : Opens (Minkowski d)}
    (_hq : IsQuotientOf B Γ Ω) (_hcv : Convex ℝ (Ω : Set (Minkowski d))) :
    ∃ M₂ : FlatSpacetime.{0} (e + 1), IsUnipotentSpacetime M₂ ∧
      AMGH (CauchyCompleteClass (e + 1)) M₂ ∧
      ∃ B₂ : FlatSpacetime.{0} d, IsLTPOver B₂ M₂ ∧ ∃ g : B → B₂, IsTameEmbedding d g := by
  -- convex LTP data `(Γ₁, Ω₁, ι)` of `B` (L1), the base presented as `Γ_U\ι⁻¹Ω₁`, convex
  obtain ⟨⟨Γ₁, Ω₁, ι, hd, hcv₁, hcvU⟩, -⟩ := Cla.exists_isLTPData_convex_of_unipotent _hU _hB
  -- G1: the maximal unipotent envelope `M₂ = Γ_U\Ω₂` (L5)
  obtain ⟨Ω₂, hle₂, hcv₂, ⟨M₂, hq₂, hU₂⟩, hmax⟩ :=
    Cla.exists_unipotent_envelope _hU hd.quotient_base hcvU
  -- `M₂` is GH and Cauchy-complete (L6)
  obtain ⟨hGH₂, hCC₂⟩ := Cla.gh_isCauchyComplete_of_isUnipotentSpacetime hU₂
  have hne₂ : (Ω₂ : Set (Minkowski (e + 1))).Nonempty := by
    obtain ⟨π, -, -, hπs, -⟩ := hq₂.quot
    obtain ⟨x⟩ : Nonempty M₂ := inferInstance
    obtain ⟨p, -⟩ := hπs x
    exact ⟨p, p.2⟩
  refine ⟨M₂, hU₂, ⟨hGH₂, hCC₂, ?_⟩, ?_⟩
  · -- absolute maximality of `M₂` (l.3668–3676): lift, equivariance, envelope maximality, end
    intro N hN hCC f hf
    obtain ⟨y₀⟩ : Nonempty N := inferInstance
    obtain ⟨D, ρ, hpair⟩ := exists_isDevelopingPair (d := e + 1) y₀
    obtain ⟨S, hS⟩ := exists_developsCC_of_isCauchyComplete' N hN hCC hpair
    letI := flatCoverChartedSpace (e + 1) N y₀
    obtain ⟨π, -, -, hfib, F, hFl, hF, g, hg⟩ :=
      exists_lift_of_isQuotientOf hq₂ hcv₂ hne₂ N hf.1 hpair
    have hconj : ∀ γ ∈ ι.restrictGroup Γ₁, g * γ * g⁻¹ ∈ ρ.range := fun γ hγ => by
      obtain ⟨δ, hδ, -⟩ :=
        exists_deck_of_lift hq₂.inv hcv₂ hne₂ N hpair hfib hFl.continuous hF hg hγ
      exact ⟨δ, hδ⟩
    have hsub : (fun p => g • p) '' (Ω₂ : Set (Minkowski (e + 1))) ⊆ range D := by
      rintro _ ⟨p, hp, rfl⟩
      exact ⟨F ⟨p, hp⟩, hg ⟨p, hp⟩⟩
    exact surjective_of_lift_of_range_subset N hpair hFl hF hg
      (hmax N hpair hN.1 hS g hconj hsub)
  · -- G3: the LTP `B₂ = Γ₁\(Ω₂ ⊕ U^⊥)` over `M₂` (L7), and `B ↪ B₂` tamely (L3)
    obtain ⟨Ω', hΩ', -, hcv', B₂, hd₂⟩ := Cla.exists_isLTPData_enlarge hd hle₂ hq₂
    have hne₁ : (Ω₁ : Set (Minkowski d)).Nonempty := by
      obtain ⟨π, -, -, hπs, -⟩ := hd.quotient.quot
      obtain ⟨x⟩ : Nonempty B := inferInstance
      obtain ⟨p, -⟩ := hπs x
      exact ⟨p, p.2⟩
    haveI : ContractibleSpace Ω₁ := hcv₁.contractibleSpace hne₁
    haveI : ContractibleSpace Ω' := (hcv' hcv₂).contractibleSpace (hne₁.mono hΩ')
    exact ⟨B₂, ⟨Γ₁, Ω', ι, hd₂⟩, Cla.exists_isTameEmbedding_of_isQuotientOf_le hΩ' hd.quotient
      hd₂.quotient inferInstance inferInstance⟩

end AbsMax

/-! ## §6 Theorem A -/

/-- **Theorem A** (`bthm:caucomp`, l.338–347), in reading R1 (DEC-43), the fourth family in the
central-extension form (b) (DEC-44), absolute maximality for Cauchy-complete targets (DEC-45 (α)).
Under the named externals `BarbotExternals d` — `BenoistNoLox`, `BieberbachI`,
`AuslanderCarriereDalbo`, `MaxUnipotentSubspace` in every dimension `≤ d` (DEC-36; Tits'
`TitsVirtuallyAbelianNull`, not cited by Barbot, is not a hypothesis: TitsNull proves it, DEC-50)
— every GH,
Cauchy-complete (`IsCauchyComplete`, DEC-35) flat spacetime `M`, in any dimension, has a finite cover
`M'` which tamely embeds in a linear twisted product `B` over a model `M₁` of dimension `d₁ ≤ d`,
`M₁` AMGH in its dimension and a translation, Misner, unipotent spacetime or of family (b).
Assembled from `barbot_A₀` (the embedding), [11.i] (`amgh_of_*`) and G1 + G3
(`exists_absMax_unipotent_ltp`); sorry-free under the named externals; marked under DEC-72. -/
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
(the "spacelike hypersurface" input of lemma K, l.576–578, l.3537–3538). No `sorry`: L8,
`Cla.isLocallyCauchyTwoSided_image_of_isIsometricEmbedding`. -/
theorem isLocallyCauchyTwoSided_image {M N : FlatSpacetime.{u} d} (_hM : GH M) (_hN : GH N)
    {f : M → N} (_hf : IsIsometricEmbedding d f) {S : Set M}
    (_hS : (flatCausality d M).IsCauchySurface S) (_hac : (flatCausality d M).IsAcausal S) :
    (flatCausality d N).IsLocallyCauchyTwoSided (f '' S) := by
  exact Cla.isLocallyCauchyTwoSided_image_of_isIsometricEmbedding _hM _hN _hf _hS _hac

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
Cauchy-compact", l.3536). By L9 (`Cla.isCauchyComplete_of_isCompact_cauchy`), sorry-free
(the smoothing step is closed in `Flat/Cla/SmoothCap`, `Flat/Cla/SmoothGlue`). -/
theorem isCauchyComplete_of_cauchyCompact (M : FlatSpacetime.{u} d) (_hGH : GH M)
    (_hC : CauchyCompact M) : IsCauchyComplete d M := by
  obtain ⟨S, hS, hSc, hac⟩ := _hC
  exact Cla.isCauchyComplete_of_isCompact_cauchy M _hGH hS hSc hac

end CauchyCompact

/-! ## §8 Theorem B -/

/-- **G9 and the identification of Theorem B** (l.3536–3548, l.3573–3581): for `M` maximal
Cauchy-compact GH with the embedding data of Theorem A₀, a finite cover of `M` is a maximal
Cauchy-compact GH spacetime of one of Theorem B's families. Assembled from L10
(`Cla.mgh_cauchyCompact_of_isFiniteCover`, with lemma K's proved form under `FlatLemmaKData`),
L11 (`Cla.exists_modelB_cover_of_isLTPOver_cauchyCompact`, G9) and L12
(`Cla.IsFiniteCover.comp`). **No `sorry` of its own**: GH of `B` over a family-(b) base is
Benoist's theorem (`hE`, finding 11; this internal lemma takes `hE` since 2026-11-01). -/
theorem cauclo_from_embedding (hE : BarbotExternals d) (_hSel : SelbergLemma (Minkowski d))
    (_hK : ∀ N : FlatSpacetime.{0} d, GH N → FlatLemmaKData N) (M : FlatSpacetime.{u} d)
    (_hGH : GH M) (_hC : CauchyCompact M) (_hM : MGH M) {M' : FlatSpacetime.{0} d} {p : M' → M}
    (_hp : IsFiniteCover d p) {Γ : Subgroup (isom d)} {Ω : Opens (Minkowski d)}
    (_hcv : Convex ℝ (Ω : Set (Minkowski d))) {B : FlatSpacetime.{0} d} (_hq : IsQuotientOf B Γ Ω)
    {f : M' → B} (_hf : IsTameEmbedding d f) {d₁ : ℕ} (_hd₁ : d₁ ≤ d) {M₁ : FlatSpacetime.{0} d₁}
    (_hM₁ : IsModelA M₁) (_hltp : IsLTPOver B M₁) :
    ∃ (M₁' : FlatSpacetime.{0} d) (q : M₁' → M), IsFiniteCover d q ∧ IsModelB M₁' ∧ GH M₁' ∧
      CauchyCompact M₁' ∧ MGH M₁' := by
  -- lemma K in the form L10 consumes, from its named data on every GH target
  have hK' : ∀ N : FlatSpacetime.{0} d, GH N → ∀ S : Set N, IsCompact S → IsConnected S →
      (flatCausality d N).IsLocallyCauchyTwoSided S → (flatCausality d N).IsCauchySurface S := by
    intro N hN S hSc hSconn hloc
    have hKN := _hK N hN
    obtain ⟨S₀, hS₀, hac₀⟩ := hKN.exists_cauchy
    obtain ⟨ψN, hψN⟩ := Flat.flat_exists_isCauchySplitting hKN.flow hN.1 hS₀ hac₀
    exact Causality.isCauchySurface_of_isLocallyCauchyTwoSided hKN.tarentin hN hKN.arc
      hKN.jminus hKN.jplus hKN.curvesExtend hψN hSc hSconn hloc
  -- steps (1)–(2) (L10): `M'` is maximal Cauchy-compact GH, and an embedding into a GH `B` is
  -- onto a Cauchy-compact `B`
  obtain ⟨-, -, -, hemb⟩ := Cla.mgh_cauchyCompact_of_isFiniteCover hK' _hGH _hC _hM _hp
  obtain ⟨-, hfi, -⟩ := _hf
  -- `B` is GH, through the GH of its base (TwistedProduct's `gh_of_isLTPOver`)
  have hGHB : GH B := by
    rcases _hM₁ with hT | hMis | hU | hCH
    · exact gh_of_isLTPOver _hltp (gh_of_isTranslationSpacetime hT)
    · cases d₁ with
      | zero => exact (hMis : False).elim
      | succ e =>
        obtain ⟨φ, L, hL, -, hq₁ | hq₁⟩ := (hMis : IsMisnerSpacetime M₁)
        · exact gh_of_isLTPOver _hltp (gh_of_isQuotientOf_misnerWedge hq₁)
        · exact gh_of_isLTPOver _hltp (gh_of_isQuotientOf_misnerWedgePast hq₁)
    · cases d₁ with
      | zero => exact (hU : False).elim
      | succ e =>
        exact gh_of_isLTPOver _hltp (Cla.gh_of_isUnipotentSpacetime (hU : IsUnipotentSpacetime M₁))
    · -- family (b): `M₁ = Γ₁\Ω^±(Λ(Γ₁))` is GH through Benoist (`hE.benoist d₁`, finding 11),
      -- `amgh_of_isCHCentralExtension`'s first component
      exact gh_of_isLTPOver _hltp (amgh_of_isCHCentralExtension (hE.mono _hd₁) M₁ hCH).1
  obtain ⟨hfs, hCB⟩ := hemb B f hGHB hfi
  -- steps (3)–(4) (L11): G9, the unipotent base excluded, family (b) → (a) by Selberg
  obtain ⟨M₁', q, hq', hfam⟩ := Cla.exists_modelB_cover_of_isLTPOver_cauchyCompact _hSel hGHB hCB
    hfi hfs (by cases d₁ <;> exact _hM₁) _hltp
  -- step (5) (L12): the composite of finite covers, and the MGH Cauchy-compact properties (L10)
  have hpq : IsFiniteCover d (p ∘ q) := Cla.IsFiniteCover.comp _hp hq'
  obtain ⟨hGH₁, hC₁, hM₁', -⟩ := Cla.mgh_cauchyCompact_of_isFiniteCover hK' _hGH _hC _hM hpq
  refine ⟨M₁', p ∘ q, hpq, ?_, hGH₁, hC₁, hM₁'⟩
  rcases hfam with hT | hMis | hCH
  · exact Or.inl hT
  · exact Or.inr (Or.inl (by cases d <;> exact hMis))
  · exact Or.inr (Or.inr ⟨hCH, hC₁⟩)

/-- **Theorem B** (`bthm:cauclo`, l.353–359), "standard" read as Cauchy-compact Cauchy-hyperbolic
(G4), the torus product in its literal form (a) (π₁ finitely generated, Selberg, DEC-44). Under the
named externals `BarbotExternals d`, `SelbergLemma (Minkowski d)` and lemma K's data
`FlatLemmaKData` on every GH flat spacetime of dimension `d` (DEC-36, DEC-44), every maximal
Cauchy-compact GH flat spacetime `M` (any `d`) is finitely covered by an AMGH spacetime `M₁` which
is a translation spacetime, a Misner spacetime, or a Cauchy-compact twisted product (a) of a
standard spacetime by a torus. Assembled from `barbot_A₀`, `cauclo_from_embedding` (G9),
`isCauchyComplete_of_cauchyCompact` and Rem 2.3 corrected (`absMax_of_cauchyCompact_of_mgh`);
sorry-free; marked under DEC-72, `hK` discharged in `barbot_B_geroch`. -/
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
    cauclo_from_embedding hE hSel hK M hGH hC hM hp hcv hq hf hd₁ hM₁ hltp
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
