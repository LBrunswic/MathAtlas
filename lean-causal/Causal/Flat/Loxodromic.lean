import Causal.Flat.Develop
import Causal.Flat.Externals
import Causal.Flat.Bieberbach
import Causal.Flat.Examples
import Causal.Flat.TwistedProduct
import Causal.Flat.CauchyComplete
import Causal.Flat.Lox.LevelComplete
import Causal.Flat.Lox.QuotientComplete
import Causal.Flat.Lox.CentralFix
import Causal.Flat.Lox.RestrictFix
import Causal.Flat.Lox.LatticeTrivial
import Causal.Flat.Lox.RestrictOrient
import Causal.Flat.Lox.TwoNullNormalForm
import Causal.Flat.Lox.FixLoxodromic
import Causal.Flat.Lox.SelbergMono
import Causal.Flat.Lox.EllipticCommonFix
import Causal.Flat.Lox.CommuteOnFix
import Causal.Flat.Lox.NilpotentFix
import Causal.Flat.Lox.UnipotentCentre
import Causal.Flat.Lox.PerpInvariant
import Causal.Flat.Lox.RestrictLimitSet
import Causal.Flat.Lox.NullLevelFix
import Causal.Flat.Lox.RegularLattice
import Causal.Flat.Lox.FiniteIndexND
import Causal.Flat.Lox.RestrictUnipotent
import Causal.Flat.Lox.ClosedSubgroupNhds
import Causal.Flat.Lox.SecondNullFix
import Causal.Flat.Lox.MisnerFrame
import Causal.Flat.Lox.MisnerLimitSet
import Causal.Flat.Lox.MisnerBieberbach
import Causal.Flat.Lox.MisnerRestrict
import Mathlib.GroupTheory.Schreier

/-!
# `Causal.Flat.Loxodromic` — Barbot §10, the loxodromic case

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §10
"The loxodromic case" (`loxocase`), `GHFspace.tex` l.3133–3456 of the labelled file
`papers/barbot/legacy/labeled/GHFspace.tex`. Seven labels are certified, **under readings and named
external hypotheses, disclosed** (DEC-83, DEC-89, DEC-96, the author's rulings, as DEC-72; checklist
below); the others are partial (SCOPE).

* **`bprop:admlox`** — `GHFspace.tex:1230` (Prop 4.17), marked (DEC-96; 'nonempty' added, the
  evident intent; external `LimitSetMinimal`; **no `sorry`**): `bprop_admlox`.
* **`bdef:definitioncauchyhyp`** — `GHFspace.tex:1277` (Def 4.18), marked (DEC-96; readings):
  `IsCauchyHyperbolic`, `IsAdmissible`, `limitSetJ`.

* **`blem:sanlox`** — `GHFspace.tex:3141` (Lemma 10.1), marked (DEC-83; reading: §8's standing
  hypotheses `CCAction`; **no `sorry`**): `blem_sanlox` as printed, by a proof other than the paper's (whose
  convexity of `Ω_lox(Γ)` fails): the sign of `U_lox(Γ)` is uniform over the loxodromic elements
  (`not_mem_quadrantPlus_quadrantMinus`), so `Ω_lox(Γ) ⊆ Ω^±(Λ(Γ)) ⊆ Ω(Γ)`
  (`subset_UGamma_of_oneSided`, `omegaPlus_limitSetJ_subset_omegaGamma`).
* **`blem:loxregular`** — `GHFspace.tex:3170` (Lemma 10.2), marked (DEC-83; reading: §8's standing
  hypotheses `CCAction`, both time orientations; **no `sorry`**): `blem_loxregular`, `loxregular_sign`, `omegaS_eq_interior`; the
  "reader can easily check" (l.3191–3193) is `exists_line_avoiding`.
* **`bcor:loxo_proper`** — `GHFspace.tex:3214` (Cor 10.3), marked (DEC-89; reading: `CCAction`,
  DEC-35's completeness; both time orientations; **no `sorry`**): `loxo_free`,
  `loxo_properlyDiscontinuous` (equivariant Gauss map), `bcor_loxo_proper`, `loxo_cauchyComplete`
  (future); `Lox.bcor_loxo_proper_past`, `Lox.bcor_loxo_proper_both` (`Flat/Lox/PastProper`).
* **`bprop:U_timelike`** — `GHFspace.tex:3347` (Prop 10.4), marked (DEC-83; externals
  `AuslanderCarriereDalbo`, `MaxUnipotentSubspace`; `CCAction` carried, unused; **no `sorry`**): the lightlike case
  (`not_isNonelementary_of_lightlike`); in the spacelike case the fixed space of `L(Γ_nd)` is
  spacelike (`IsMaxUnipotent.mem_direction_of_linFixed`), and a nilpotent group normalised by
  `L(Γ)` with spacelike common fixed space gives a finite-index subgroup of `L(Γ)` fixing a point
  of `𝒮` (`Flat.Lox.NilpotentFix`, by the upper central series, through `Flat.Lox.EllipticCommonFix`
  and `Flat.Lox.CommuteOnFix`), by a route other than the paper's (Cor 8.4, on which the paper
  relies, is false as printed: finding).
* **`bprop:LU_discrete`** — `GHFspace.tex:3368` (Prop 10.5), marked (DEC-83; external
  `AuslanderCarriereDalbo`; reading: `U` via `RestrictsIn`; **no `sorry`**): l.3372–3380, both branches (`Flat.Lox.UnipotentCentre`; Cartan in local form,
  `Flat.Lox.ClosedSubgroupNhds`), and l.3380–3388 (`Flat.Lox.CentralFix`, `RestrictFix`).
* `bprop:admlox` (marked above, DEC-96) — `bprop_admlox`, from invariance in `𝒥` (`isomPenrose_image_limitSetJ_subset`),
  minimality on `𝒮` (`fst_image_limitSetJ_subset`) and in `𝒥` (`limitSetJ_subset`, through the
  basin of repulsion `tendsto_isomPenrose_inv_pow`).
* `bdef:definitioncauchyhyp` (marked above, DEC-96) — `IsCauchyHyperbolic`,
  `IsFutureAdmissible`, `IsPastAdmissible`, `IsAdmissible`, `IsCauchyHyperbolic.exists_isAdmissible`.
* Prose: [10.M] l.3235–3330 (`loxo_elementary_misner`, for a finite-index `Γ'`, under the cited
  Bieberbach I, **no `sorry`** (`#print axioms`: `propext`, `Classical.choice`, `Quot.sound`); its
  steps `b ≡ 0` and `x(γ) = y(γ) = 0` under `CCAction`, `exists_invariant_nullLevel_of_ccAction`,
  `exists_invariant_nullLevels_of_ccAction`, from `Flat.Lox.NullLevelFix`; the second null
  direction `Δ₁`, l.3260–3299, fixed by **all** of `L(Γ₁)`, by a route other than the paper's,
  `Lox.fix_second_null`, `Flat.Lox.SecondNullFix`; the Misner identification l.3302–3330 through
  `Flat.Lox.MisnerFrame`, `MisnerLimitSet`, `MisnerBieberbach` (finding F3), `MisnerRestrict`
  (finding F1)); [10.G] l.3333–3456
  (`generic_omegaS_eq`, `kerTranslations_spacelike`, `kerTranslations_ballFinite`,
  `linOf_mem_kerTranslations`, `omegaS_add_mem_span`, `span_kerTranslations_spacelike` proved;
  gap G6 `limitOpens_add_perp` (`Flat.Lox.PerpInvariant`), the base domain
  `preimage_omega_limitSetJ` and `limitSetJ_eq_of_relIndex_ne_zero` (`Flat.Lox.RestrictLimitSet`),
  the `𝒩`-conjuncts without `CCAction` `kerTranslations_lattice_of_limitSetJ`
  (`Flat.Lox.RegularLattice`) proved; the reduction to `U` `exists_generic_reduction` and the
  conclusion in `𝐌ⁿ` `generic_isCHCentralExtension` proved (wave 7, `Flat.Lox.FiniteIndexND`,
  `Flat.Lox.RestrictUnipotent`); the conclusion `loxo_generic_centralExtension`, family (b), and
  `loxo_generic_torusProduct`, family (a) under `π₁` finitely generated through Selberg, are
  proved, **no `sorry`** (`#print axioms`: `propext`, `Classical.choice`, `Quot.sound`).
* gx exports (the contract of `docs/BARBOT.md`): `uniformization_injective`,
  `uniformization_image`, `uniformization_properlyDiscontinuous`, and `uniformization`.

> If $\Gamma$ contains loxodromic elements, $\Omega_{lox}(\Gamma) = \Omega(\Gamma)$. (l.3143–3144)

> $\Omega(\widetilde{S})$ is a regular convex domain. (l.3172)

> The action of $\Gamma$ on $\Omega(\widetilde{S})$ is free and properly discontinuous, and the
> quotient space $M(S) = \Gamma \backslash \Omega(\widetilde{S})$ is a Cauchy-complete globally
> hyperbolic spacetime. (l.3215–3218)

> ${\bf U}$ is timelike. (l.3348) — $L_{U}(\Gamma)$ is discrete. (l.3369)

> But the reader can easily check that in all cases, there is always a timelike line avoiding the
> intersection $U^{+}(\gamma_{0}) \cap U^{-}(\gamma_{1})$. (l.3191–3193)

> $L$ might be noninjective! Let $\mathcal N$ be its kernel: its elements are translations, and the
> translation vectors form a lattice in some spacelike linear space $E$. (l.3406–3409)

> \emph{Conclusion:\/} $M(S) = \Gamma\backslash\Omega(\widetilde{S})$ is a twisted product of a
> Cauchy-hyperbolic spacetime by a flat torus. (l.3454–3456)

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; `Minkowski d` has `d` spatial
dimensions: Barbot's `n` is `d + 1` (the Misner branch works in `Minkowski (d' + 1)`).

## Main declarations

* `IsRepulsiveFixedJ γ w` (the repulsive fixed point in `𝒥 ≅ 𝒮 × ℝ` of a loxodromic `γ`: an
  eigenvector `(1,u)` for `λ < 1` and a `γ`-invariant hyperplane, `⟨(1,u)|γp⟩ − s = λ⁻¹(⟨(1,u)|p⟩ − s)`),
  `exists_isRepulsiveFixedJ`, `IsRepulsiveFixedJ.fst_ne`, `.conj`, `eigen_of_funEq`;
  `loxRepSet Γ` (Barbot's `Λ₀`), `limitSetJ Γ` (`Λ(Γ)`, its closure).
* [7.L] in `𝒥`: `quadrants_subset_achronalDomain`, **`interior_achronalDomain_eq_quadrants`**
  (`Int Ω_γ = U⁺(γ) ⊔ U⁻(γ)`, `U^±(γ) = P^±(w) ∩ P^±(w')`, `w`, `w'` the repulsive points of `γ`,
  `γ⁻¹`).
* Classes: `Ug_eq_achronalDomain_of_isLoxodromic`, `achronalDomain_eq_univ_of_isSpacelikeElliptic`,
  `…_of_isTangentParabolic`, the linear parabolic orbit `linearParabolic_orbit_fwd`/`_bwd`,
  `subset_compl_nullHyperplanes_of_oneSided`.
* Lemma 10.1's uniform sign: the transverse part `nullV` of a null frame (`nullV_map`,
  `minkQ_nullV_pow_smul_sub_le`: it grows at most linearly along an orbit), `IsRepulsiveFixedJ.pair`,
  `exists_lt_minkB_pow_smul`, `exists_minkQ_neg_of_sign`, `not_minkQ_neg_of_mem_UGammaLox`,
  `not_mem_quadrantPlus_quadrantMinus`, `blem_sanlox`.
* The regular domains: `smul_mem_omegaPlus_limitSetJ` (and `Minus`), `preservesOmega_limitSetJ`,
  `exists_two_loxRepSet`, `cosmoRegular_limitSetJ`, `limitOpensPlus`/`Minus`.
* Cor 10.3: `ActsFreelyProperlyOn`, `isCancelSMul_of_free`, `properlyDiscontinuousSMul_of_finite`,
  `loxo_free`, `loxo_properlyDiscontinuous`; its engine `finite_of_gaussEquivariant` (the rest-frame
  norm `restNormSq`, `sq_norm_le_restNormSq`, `restNormSq_le`, `norm_linOf_le_of_gauss`), the
  Gauss map equivariant and bounded on compacts (`gaussMap_smul`, `exists_norm_gaussMap_le`), the
  point-reflection conjugate `negConj` (`negConj_smul`, `linOf_negConj`, `cosmoRegular_negS`).
* Prop 10.4: `not_isNonelementary_of_lightlike`, `IsMaxUnipotent.mem_direction_of_linFixed` (every
  vector fixed by `L(N)` lies in the direction of the maximal `N`-unipotent subspace),
  `bprop_U_timelike`.
* [10.G]: `exists_finiteIndex_linOf_eq_on_span_kerTranslations` (a finite-index `Γ'` with
  `L(γ)|_E = id`), `limitSetJ_eq_of_relIndex_ne_zero`, `limitOpens_eq_of_relIndex_ne_zero`,
  `preimage_omega_limitSetJ`, `limitOpens_add_perp`, `kerTranslations_lattice_of_limitSetJ`; the
  reduction to `U` and the conclusion (wave 7): `IsNonelementary.of_relIndex`,
  `exists_loxodromic_of_relIndex`, `omegaSOpens_eq_limitOpens_of_relIndex`, `omegaSOpens_add_perp`,
  `exists_loxodromic_restrictGroup`, `restrict_kerTranslations_lattice`, `exists_generic_reduction`
  (`U` timelike, `Γ₂` of index `≤ 2` restricting to `U` with `Γ₂_nd = Γ_nd`, `L_U(Γ₂)` discrete),
  `exists_finiteIndex_restrict_trivial_on_span`, `generic_isCHCentralExtension`.
* [10.M] under `CCAction`: `exists_invariant_nullLevel_of_ccAction`,
  `exists_invariant_nullLevels_of_ccAction`; the conclusion `loxo_elementary_misner` (§9, placed
  after §11b, whose `generic_omegaS_eq`, `limitSetJ_eq_of_relIndex_ne_zero` and
  `omegaSOpens_add_perp` its proof uses).
* Families: `IsNonelementary`, `IsFutureAdmissible`, `IsPastAdmissible`, `IsAdmissible`,
  `IsCauchyHyperbolic`, `kerTranslations`, `IsSpacelikeSubmodule`, `IsCHCentralExtensionOf`,
  `IsCHCentralExtension` (b), `IsCHTorusProduct` (a, for the same `Γ`).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `bprop:admlox` (**marked**, DEC-96): "contained in any closed `ρ(Γ)`-invariant subset" | ⚠ reading: **nonempty** added (the evident intent, DEC-96: the empty set is closed and invariant — the same for the limit-set fact quoted at l.1248–1251); ⚠ strengthened: the cited dynamics of discrete subgroups on the sphere (l.1246–1254) is the named external `LimitSetMinimal` (DEC-36), not proved by design, used only on a singleton; ⚠ weakened: of admissibility only `L(Γ)` discrete without global fixed point is used (`limitSetJ_subset`); the step l.1254–1267 is proved from the eigenvalue alone (`laoucapulse_repulsive_basin`) |
| `bdef:definitioncauchyhyp` (**marked**, DEC-96) | ⚠ reading (DEC-96): `Λ(ρ)` as in Prop 4.17 (`limitSetJ`, the closure of the repulsive fixed points in `𝒥` of the loxodromic elements); `Ω⁺` for a future admissible and `Ω⁻` for a past admissible `ρ` (`limitOpensPlus`, `limitOpensMinus`); 'admissible' in subgroup form (`Γ ≤ Isom(𝐌ⁿ)`, `L` injective on `Γ`, `L(Γ)` discrete without global fixed point, preserving a regular domain: `IsFutureAdmissible`, `IsPastAdmissible`) |
| `blem:sanlox` (**marked**, DEC-83) | ⚠ reading (DEC-35): §8's standing hypotheses as `CCAction Γ Σ`, Rem 8.9 derived from it (`nini`); no external; proved by a route other than the paper's (finding: `Ω_lox(Γ)` is not convex) |
| `blem:loxregular` (**marked**, DEC-83) | ⚠ reading (DEC-35): `CCAction Γ Σ`; both time orientations kept (`Ω⁺` future regular or `Ω⁻` past regular); Lemma 4.9 without its hypothesis; no external |
| `bprop:U_timelike` (**marked**, DEC-83) | ⚠ strengthened: the named externals `AuslanderCarriereDalbo d` (`bthm:ausl`) and `MaxUnipotentSubspace d` (`bthm:unip`), cited by the paper, not proved by design (DEC-36); `CCAction` carried and unused (⚠ weakened); Cor 8.4 replaced (finding) |
| `bprop:LU_discrete` (**marked**, DEC-83) | ⚠ strengthened: the named external `AuslanderCarriereDalbo d` (`bthm:ausl`, DEC-36), used by the proof; `MaxUnipotentSubspace d` and `CCAction` carried and unused (⚠ weakened); ⚠ reading: `U` an `AffineMinkEmbedding` with `RestrictsIn` (`Flat.TwistedProduct`'s form) |
| §8's setting: `S` complete, `Γ = π₁(S)` acting on `S̃` | ⚠ strengthened (DEC-35 reading, as `Flat.Develop`): `CCAction Γ Σ` in `𝐌ⁿ`; on `M` through `DevelopsCC`, `ccAction_of_developsCC` |
| `Γ` contains a loxodromic element (l.3135) | ✓ carried (`hlox`) |
| Rem 8.9: no nonspacelike elliptic, no transverse parabolic (used in 10.1) | ✓ derived from `CCAction` (`nini`) |
| 10.2: "up to time reversing isometries" (l.3181–3183) | ⚠ reading: both cases kept (`isom d` is `SO₀`-affine); `Ω⁺` or `Ω⁻` |
| 10.2: 4.6, 4.8, 4.9 | ✓ through `omegaPlus_closure_eq_interior` (4.9 with no hypothesis) |
| 10.3: `bprop:agissons` (Γ discrete) | ⚠ replaced: 4.16 is not used; properness on `Ω(S̃)` is derived from `CCAction.proper` (Γ proper on `Σ`) through the `L(Γ)`-equivariant Gauss map into `ℍᵈ` (`finite_of_gaussEquivariant`) |
| 10.3: "`M(S)` is a Cauchy-complete GH spacetime" | ✓ both time orientations: `bcor_loxo_proper` under `Ω(S̃) = Ω⁺(Λ)`, `Lox.bcor_loxo_proper_past` under `Ω(S̃) = Ω⁻(Λ)` (the point reflection `p ↦ −p`, DEC-89), `Lox.bcor_loxo_proper_both` (no case split, Cauchy-completeness included, `Flat/Lox/PastProper`); in this file Cauchy-completeness split off as `loxo_cauchyComplete`, which takes the quotient instances as hypotheses and uses only `CosmoRegular Λ` (⚠ weakened: `h`, `hlox`, `hΛ` unused) |
| gx uniformization: nonelementary, `ker L = 1` | ⚠ weakened: neither is used; only a loxodromic element |
| 10.4: `bthm:ausl`, `bthm:unip`, discreteness, nonelementary | ✓ carried (`AuslanderCarriereDalbo`, `MaxUnipotentSubspace`, `DiscreteTopology Γ`) |
| 10.4: Cor 8.4 (a finite-index subgroup abelian, l.3354–3356) | ⚠ replaced: `L(Γ_nd)` nilpotent (`bthm:ausl`) and `Lox.exists_finiteIndex_fix_of_nilpotent_normal`; Cor 8.4 is false as printed (finding); `CCAction` (`h`) is carried but unused (⚠ weakened) |
| 10.4: `U` nonempty and `Γ`-invariant ("being unique", l.3343–3344) | ✓ derived (`exists_invariant_maxUnipotent` and the uniqueness of `MaxUnipotentSubspace`) |
| [10.M]: "up to finite index" `L(Γ)` fixes `Δ₀` (l.3236–3238) | ⚠ conclusion for a finite-index `Γ' ≤ Γ` (DEC-43's R1): the paper's conclusion for `Γ` itself (l.3326–3330) is false (finding) |
| [10.M]: "an appropriate use of Bieberbach's theorem" (l.3327) | ⚠ strengthened: a cited external, as `BarbotExternals` (`hBieb : ∀ k ≤ d' + 1 + 1, BieberbachI (EuclideanSpace ℝ (Fin k))`, the form of `BarbotExternals.bieberbach` and of `nonloxodromic_*`; added 2026-11-01 by master ruling: the conclusion implies Bieberbach I, finding). Used at `k = d'` by `Lox.fix_second_null` and at `k = d' + 1` by `Lox.misner_bieberbach` (the euclidean model of `Γ₁` on `ℝ × ℝ^{d'}`) |
| [10.M]: "the action on `π_P⁻¹(0)` is free and properly discontinuous" (l.3326–3327), Bieberbach for it (l.3322) | ⚠ replaced: false for `Γ` (finding F3); Bieberbach is applied to `Γ₁`'s euclidean model `(s, z) ↦ (s + a, Az + u)`, discrete by properness on the tube, and `𝒲 ∋ e_s` (`Lox.misner_bieberbach`) |
| [10.M]: the setting `hcaus` (`M` causal) | ⚠ weakened: carried, unused by `loxo_elementary_misner` |
| [10.M]: `α(Γ₀)` discrete, the conjugation argument for `v(γ') = 0` (l.3260–3270) | ⚠ replaced: discreteness of the slice actions of `Γ₀` and translation lengths (`Flat.Lox.SecondNullFix`); the paper's formula omits the screw part of `α(γ)` (finding F4) |
| Def 4.18 / family (b): `L(Γ)` without global fixed point (l.1212–1214) | ⚠ reading: Def 4.18's condition, weaker than `docs/BARBOT-THEOREMS.md` §1's "discrete nonelementary" (an infinite dihedral group with a loxodromic is elementary and has none) |
| Def 4.18: `Ω^±(Λ(ρ))` | ⚠ reading: sign tied to the side of admissibility (`IsFutureAdmissible` ↦ `Ω⁺`, `IsPastAdmissible` ↦ `Ω⁻`) |
| [10.G]: Selberg (DEC-44) for family (a) | ✓ carried (`SelbergLemma`, `ρ.range.FG`) |
| [10.M], [10.G]: `M` a (Hausdorff) manifold | ✓ carried (`[T2Space M]`, added 2026-11-01 as for `Flat.Develop`'s Prop 8.12: Barbot's spacetimes are Hausdorff manifolds; it gives `ccAction_of_developsCC`) |
| [10.G]: the setting `hcaus` (`M` causal) | ⚠ weakened: carried, unused by `loxo_generic_centralExtension` and `loxo_generic_torusProduct` |
| [10.G]: Prop 10.5 for `Γ` (l.3368) | ⚠ applied to the index-`≤ 2` subgroup `Γ₂` restricting to `U` (`Γ` itself need not restrict: orientation of `U`); `Γ₂ ⊇ Γ_nd`, so `Γ₂_nd = Γ_nd` (`Lox.nonDiscretePart_eq_of_le`) |

## SCOPE (disclosed)

* **Sorries (0)**: `loxo_elementary_misner` ([10.M]) is closed (integrator, 2026-11-01): after its
  first three steps (`Γ₁`, `b ≡ 0`, `Δ₁` fixed by all of `L(Γ₁)`, `Lox.fix_second_null`) the Misner
  identification l.3302–3330 is the glue over four lemma modules — the two-null-vector frame and
  the normal form on `Γ₁` (`Lox.misner_frame`), `limitSetJ Γ₁ = {(u₀,s₀),(u₁,s₁)}`
  (`Lox.misner_limitSet`), Bieberbach for the euclidean model `(s, z) ↦ (s + a, Az + u)` of `Γ₁` on
  `ℝ × ℝ^{d'}` (`Lox.misner_bieberbach`, F3), `restrictGroup Γ' = misnerGroup L` with a nonzero
  boost (`Lox.misner_restrict`, F1) — each sorry-free; `#print axioms loxo_elementary_misner`:
  `propext`, `Classical.choice`, `Quot.sound`. The proof runs under `maxHeartbeats 400000`.
  The statement carries Bieberbach I since 2026-11-01 (master ruling: the conclusion implies
  Bieberbach I for torsion-free orientation-preserving crystallographic groups of `ℝ^{d'}`).
  `bprop_LU_discrete` is closed (closer, 2026-11-01): the branch `L_U(Γ_nd) = {1}` by
  `discreteTopology_restrictGroup_of_nonDiscretePart_bot` and `Flat.Lox.ClosedSubgroupNhds`
  (Cartan's closed-subgroup theorem in local form, by von Neumann's elementary argument:
  one-parameter subgroups of `cl L(Γ)` from `exp`, the Trotter step, the inverse function theorem
  for `(H, M) ↦ exp H exp M`), so `loxo_generic_centralExtension` and `loxo_generic_torusProduct`
  ([10.G]) are sorry-free (`#print axioms`: `propext`, `Classical.choice`, `Quot.sound`).
  `loxo_cauchyComplete` is proved
  (`Flat.Lox.LevelComplete`, `Flat.Lox.QuotientComplete`). `blem_sanlox`, `blem_loxregular`,
  `interior_achronalDomain_eq_quadrants`,
  `subset_UGamma_of_oneSided`, `loxo_properlyDiscontinuous`, `bcor_loxo_proper`, `bprop_U_timelike`,
  the proved [10.G]
  lemmas and all of `bprop:admlox`
  (`bprop_admlox`, `isomPenrose_image_limitSetJ_subset`, `fst_image_limitSetJ_subset`,
  `limitSetJ_subset`) use no `sorry`. **Ruled DEC-96:** `bprop:admlox` is marked with 'nonempty'
  (the evident intent) and `LimitSetMinimal` a named external; `bdef:definitioncauchyhyp` under
  the readings of the checklist. Findings kept: Prop 4.17 as printed is false for the empty set;
  the basin of repulsion of `x₀` is all of `𝒥` off the fibre over the attractive point, so the
  closure of `δ(Λ)` is not needed, and the convergence of the `s`-coordinate (l.1255–1266) is not
  argued in the paper.
* **Upstream.** The gx exports and the three [10.M]/[10.G] conclusions go through
  `ccAction_of_developsCC` and `bprop_danom`; `Flat.Develop`'s former two `sorry`s
  (`holonomy_proper`; Prop 8.12 step 1) are closed at 20ea59b (it has no `SORRY(` left), and Cor
  10.3's properness adds none. The three conclusions since 2026-11-01 carry `[T2Space M]` and
  read `CCAction ρ.range Σ` through `ccAction_of_developsCC`. Under a given `CCAction` (in `𝐌ⁿ`) Lemma 10.2 and Cor 10.3 (completeness included) are
  sorry-free.
* **Lemma modules** (`Flat/Lox/`, wave 5): `LevelComplete`, `QuotientComplete` (Cor 10.3's
  completeness), `CentralFix`, `RestrictFix` (Props 10.4/10.5), `LatticeTrivial`
  (`exists_finiteIndex_linOf_eq_on_span_kerTranslations`), `RestrictOrient`, `TwoNullNormalForm`,
  `FixLoxodromic` ([10.M]'s first step), `SelbergMono` (Selberg in dimension `d₁ ≤ d`), and
  (wave 6) `EllipticCommonFix`, `CommuteOnFix`, `NilpotentFix` (Prop 10.4's spacelike case),
  `UnipotentCentre` (Prop 10.5's centre step), `PerpInvariant`, `RestrictLimitSet`,
  `RegularLattice` ([10.G]), `NullLevelFix` ([10.M]), (closer, 2026-11-01) `SecondNullFix` ([10.M]'s
  second null direction, `fix_second_null`, under Bieberbach I), and (wave 7) `FiniteIndexND` (`SO₀(1, d)` a
  topological group; `Γ_nd` unchanged on a finite-index subgroup containing it), `RestrictUnipotent`
  (the restricting subgroup contains `Γ_nd`; loxodromics restrict to loxodromics; the restriction
  hom and pull-backs; the restricted proper action; `d₁ ≤ d`) ([10.G]), and (closer)
  `ClosedSubgroupNhds` (Prop 10.5's Lie-theoretic input, `exists_nhds_subset_connectedComponentIn_closure`),
  and (integrator, 2026-11-01) `MisnerFrame`, `MisnerLimitSet`, `MisnerBieberbach`, `MisnerRestrict`
  ([10.M]'s Misner identification; none imports this file or a sibling of the four).
  Their
  declarations live in `Causal.Flat.Lox` (`completeSpace_inducedLength_cosmoLevel` in
  `Causal.Flat`).
* **Readings.** `Λ₀` is the set of all repulsive fixed points (`IsRepulsiveFixedJ`), not one per
  element; `U^±(γ)` are the two quadrants of `interior_achronalDomain_eq_quadrants`, whatever
  repulsive points are chosen; "nonelementary" is `IsNonelementary` (no finite-index subgroup of
  `L(Γ)` fixing a point of `𝒮`); "admissible" asks `L(Γ)` discrete (Externals' `lorentzTopology`)
  without global fixed point (Def 4.18, l.1212–1214 — weaker than BARBOT-THEOREMS §1's
  "nonelementary"; family (b) uses the same condition), future or past (`IsFutureAdmissible`,
  `IsPastAdmissible`), and Cauchy-hyperbolic takes `Ω⁺` for a future, `Ω⁻` for a past admissible
  group. Family (a) is (b) with `L(Γ)` torsion-free for the same `Γ` (BARBOT-THEOREMS §1), the
  bundle description not written. The Misner and generic conclusions are both stated in DEC-43's
  R1 form: the quotient by a finite-index `Γ' ≤ Γ` is an LTP over the model (for [10.M] the
  statement for `Γ` itself is false: finding below).
* **Cor 10.3's quotient** is stated here in the future case only; the past case and the printed
  statement are in `Flat/Lox/PastProper` (`Lox.bcor_loxo_proper_past`, `Lox.bcor_loxo_proper_both`),
  which imports `Flat.Classification` (for the time reversal `revConj`) and so cannot be imported
  by this file. `Flat.Examples` has the GH theory of `Γ\Ω⁺(Λ)` only.

## Findings (DEC-27)

* **`blem:sanlox`'s proof (l.3157–3165) treats `Ω_lox(Γ)` as convex; it is not** — for `Γ = ⟨γ⟩` it
  is the disjoint union `U⁺(γ) ⊔ U⁻(γ)`. The argument is correct for each `Γ`-invariant convex
  piece on which two null directions are one-sided, which covers `Ω^±(Λ(Γ))`. **The printed
  equality is nevertheless true** (proved here): no point of `U_lox(Γ)` lies in a future quadrant
  `U⁺(γ)` and a past quadrant `U⁻(γ')`, because for the repulsive point `w` of `γ^{±1}` off the
  attractive direction of `γ'` some `γ'ᵐx` crosses the hyperplane of `w`, and then
  `γ^{±n}γ'ᵐx − x` is timelike for `n` large; an element of `Γ` with a timelike displacement is
  loxodromic under Rem 8.9 (a linear parabolic displaces into `J^⊥`, a spacelike elliptic or
  tangent parabolic has `Ω_g = 𝐌ⁿ`). So `Ω_lox(Γ) ⊆ Ω⁺(Λ(Γ)) ∪ Ω⁻(Λ(Γ))`: there are no mixed-sign
  components, and the linear parabolics never need to be examined on them.
* **The "convex hull of the orbit is a complete lightlike line" (l.3159–3163)** is replaced by an
  exact growth argument: along the orbit `⟨n|γᵏx⟩ = ⟨n|c⟩ + ⟨n|Rᵏy⟩ + k⟨n|p(y)⟩`, and `x` must first be
  moved off `ker p` inside the open set (a point of `P(γ₀) ∩ ker p` has a bounded orbit).
* **l.3191–3193 ("easily check") is easy, and is filled** (`exists_line_avoiding`).
* **[10.G] l.3409: "the translation vectors form a lattice in some spacelike linear space `E`" is not
  implied by the vectors being spacelike** (`ℤ(0,0,1) + ℤ(1,1,√2)` in `𝐌³` consists of spacelike
  vectors and spans a degenerate plane); it holds here because `Ω(S̃) = Ω^±(Λ(Γ))` is `E`-invariant
  and `Λ(Γ)` has two null directions (`span_kerTranslations_spacelike`).
* **[10.M]'s conclusion for `Γ` itself (l.3326–3330) is false; it holds up to finite index.** In `𝐌⁴`
  (form `xy + |z|²`, coordinates `(x, z₁, z₂, y)`), `γ₀(x,z,y) = (e⁻¹x, z, e y)` and the glide
  `σ(x,z₁,z₂,y) = (−y, z₁+1, −z₂, −x)` (in `SO₀`, spacelike elliptic, allowed by Rem 8.9) satisfy
  `σγ₀σ⁻¹ = γ₀⁻¹`; `Γ = ⟨γ₀, σ⟩` acts freely and properly on `Ω = {x > 0, y < 0} × ℝ²` and
  `Σ = {xy = −1} ∩ Ω` satisfies (CC′) with `Ω(S̃) = Ω`. `⟨γ₀, σ²⟩` has index 2 and fixes `Δ₀`, so `Γ`
  is elementary; but the direction of `U` contains the `(x, y)`-plane, so `Γ_U` is non-abelian, and
  no presentation as an LTP over a Misner spacetime (an abelian group) exists. `loxo_elementary_misner`
  is stated for a finite-index `Γ'` (DEC-43's R1).
* **[10.M] l.3326–3327: "the action on `π_P^{-1}(0)` is free and properly discontinuous" is false
  for `Γ`** (true for `Γ₀ = ker a`). In `𝐌⁴` (form `xy + |z|²`, `z ∈ ℝ²`) let
  `γ₀(x, z, y) = (e⁻¹x, R_θ z, e y)`, `θ/π` irrational, and `Γ = ⟨γ₀⟩`: `Γ` is elementary (it fixes
  both null axes), loxodromic, acts freely and properly on `Ω = {x > 0, y < 0} × ℝ²` and on the
  (CC′) surface `{xy = −1} ∩ Ω` (as in the finding below for `σ`); yet `γ₀` acts on
  `π_P^{-1}(0) = {x = y = 0} ≅ ℝ²` by the rotation `R_θ`, which fixes `0` and has dense orbits on
  circles. The conclusion of [10.M] still holds there (`U' = {z = 0}`, a Misner spacetime in `𝐌²`):
  the Bieberbach step (l.3322) must be run for `Γ₀`, normalised by `Γ`, not for `Γ`.
* **[10.M] l.3264–3270 (F4): the conjugation formula for `α(γγ'γ⁻¹)` omits the translation part
  of `α(γ)`, and the discreteness argument for `v(γ') = 0` fails as written.** The formula
  `α(γγ'γ⁻¹)(z,y) = (R(γ)R(γ')R(γ)⁻¹(z) + R(γ)(u(γ')) + e^{−a(γ)} v(γ'), y)` holds only if `α(γ)`
  fixes the origin of `Q₀`; the choice of origin (l.3250) fixes `y` only. A loxodromic `γ` with
  a **screw** part — `α(γ)(z, y) = (R z + u, e^{a} y)`, `R u = u ≠ 0`, e.g. a boost times a
  translation along the axis of a rotation of `{x = y = 0}`, `d' ≥ 3` (or `R = 1`, `d' ≥ 2`) —
  fixes no point of `Q₀`, and `γⁿγ'γ⁻ⁿ` has translation part `n Rⁿ (I − R(γ')) u + Rⁿ u(γ')`,
  unbounded as soon as `R(γ')` moves `u`: the elements are not shown to accumulate. The conclusion
  (`Δ₁` is `L(Γ)`-invariant, l.3298–3299) is true, and is proved here for all of `Γ₁` without
  Auslander–Carrière–Dal'bo (`Lox.fix_second_null`): a translation length, unlike a translation
  part, is conjugation invariant; Bieberbach on one slice and finitely generated torsion abelian
  groups being finite do the rest. Also: l.3287's "`L(Γ₀)` is a finite group" holds only after the
  reduction `𝐔 = 𝐌ⁿ` (l.3280–3284), which needs the Carrière–Dal'bo maximal unipotent subspace
  (`MaxUnipotentSubspace`, not carried by `loxo_elementary_misner`): in `𝐌⁵`, `Γ = ⟨γ₀, g⟩`,
  `γ₀` a pure boost of the null plane, `g` = (translation by `e₁`) × (irrational rotation of
  `(e₂, e₃)`) commuting with it, `L(Γ₀) = ⟨R_θ⟩` is infinite.
* **Prop 4.17's proof (l.1255–1266) needs less than it uses**: the basin of repulsion of the
  repulsive point `x₀` of `γ` is all of `𝒥` off the fibre over the attractive point `v₁` of `γ`
  (not only some `δ⁻¹(U)`, `tendsto_isomPenrose_inv_pow`), so no closure of `δ(Λ)` is needed: if
  `Λ ⊆ δ⁻¹(v₁)`, then `{v₁}` is closed, nonempty and `L(Γ)`-invariant and the limit-set
  minimality puts `v₀ ≠ v₁` in it. The `s`-coordinate converges because the elliptic part grows
  linearly against the contraction `λᵏ` (`exists_abs_minkB_pow_smul_sub_le`).
* **Cor 10.3's proper discontinuity (l.3222–3224) needs neither `bprop:agissons` nor the
  Riemannian geometry of the level sets.** The Gauss map `n` of the cosmological time satisfies
  `n(γp) = L(γ)n(p)` and is bounded on compact sets (`T ≥ ε`, `r(K)` in a compact
  `cl Ω ∩ J⁻(q)`); if `γK ∩ K ≠ ∅` then `L(γ)` maps a bounded point of `ℍᵈ` to a bounded point,
  so it is bounded (`SO₀(1, d)` acts properly on `ℍᵈ`), so `γ s₀` is bounded for a fixed `s₀ ∈ Σ`,
  and the properness of `Γ` on `Σ` concludes. The continuity of `n` is not needed.
* **Prop 10.4's folklore is false as printed** (`Flat.Externals`' `not_abelianPairAsPrinted`); its
  lightlike case does not use it.
* **Cor 8.4 (`bcor:abel`) is false as printed**, so Prop 10.4's spacelike case (l.3355–3356) rests
  on a false statement:

  > If $\Gamma$ preserves a spacelike affine subspace ${\bf U}$, then
  > $\Gamma$ contains as a finite index subgroup a free abelian group of finite rank. (l.2295–2296)

  In `𝐌⁴` let `Γ₀ ⊂ SO₀(1, 2)` be a cocompact Fuchsian group acting on `(t, x, y)` and
  `Γ = Γ₀ × ⟨z ↦ z + 1⟩`: `Γ` preserves the spacelike line `{t = x = y = 0}`, acts freely, properly
  and cocompactly on the (CC′) surface `ℍ² × ℝ`, and is `π₁(closed surface) × ℤ`, not virtually
  abelian (`Γ₀` alone, preserving the point `0`, is the `0`-dimensional instance). The failing step
  is "the action of `Γ` on `π(U)` has to be free and properly discontinuous" (`Δ` is not
  `Γ`-invariant, W9). Prop 10.4 itself is not refuted (here `Γ_nd = ℤ` and `U = 𝐌⁴`); its true
  route is through the fixed space of `L(Γ_nd)`, which lies in `U`'s direction
  (`IsMaxUnipotent.mem_direction_of_linFixed`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
wave 5, package WP-34d-Loxodromic.
-/

namespace Causal.Flat

open Set Function TopologicalSpace Topology Filter
open scoped Pointwise

variable {d : ℕ}

/-! ## 0. Loxodromic isometries, their repulsive fixed points in `𝒥`, the limit set -/

section RepulsiveFixed

/-- An element of `SO₀(1, d)` whose inverse is loxodromic is loxodromic (`R⁻¹` elliptic, the boost
`H⁻¹` of rapidity `−ζ`). -/
theorem IsLoxodromic.inv' {A : Minkowski d ≃ₗ[ℝ] Minkowski d} (h : IsLoxodromic A) :
    IsLoxodromic A⁻¹ := by
  obtain ⟨R, H, hR, hH, ⟨E, hEs, hEp, hE⟩, ⟨e₀, e₁, ζ, hζ, h0, h1, h01, hH0, hH1, hW⟩, rfl, hc⟩ := h
  have hinv : ∀ x y, H x = y → H⁻¹ y = x := fun x y hxy => by rw [← hxy]; simp
  refine ⟨R⁻¹, H⁻¹, (lorentz d).inv_mem hR, (lorentz d).inv_mem hH, ⟨E, hEs, hEp, fun v w => ?_⟩,
    ⟨e₀, e₁, -ζ, neg_ne_zero.2 hζ, h0, h1, h01, ?_, ?_, fun w hw0 hw1 => ?_⟩, ?_, ?_⟩
  · have := hE (R⁻¹ v) (R⁻¹ w)
    rw [← this]; simp
  · rw [Real.cosh_neg, Real.sinh_neg]
    refine hinv _ _ ?_
    rw [map_add, map_smul, map_smul, hH0, hH1]
    linear_combination (norm := module) (Real.cosh_sq_sub_sinh_sq ζ) • e₀
  · rw [Real.cosh_neg, Real.sinh_neg]
    refine hinv _ _ ?_
    rw [map_add, map_smul, map_smul, hH0, hH1]
    linear_combination (norm := module) (Real.cosh_sq_sub_sinh_sq ζ) • e₁
  · exact hinv _ _ (hW w hw0 hw1)
  · rw [hc, mul_inv_rev]
  · rw [← mul_inv_rev, ← mul_inv_rev, hc]

theorem isLoxodromic_linOf_inv {γ : isom d} (h : IsLoxodromic (linOf γ)) :
    IsLoxodromic (linOf γ⁻¹) := by
  rw [linOf_inv]; exact h.inv'

/-- A loxodromic isometry is not the identity (`id` is elliptic). -/
theorem ne_one_of_isLoxodromic {γ : isom d} (h : IsLoxodromic (linOf γ)) : γ ≠ 1 := by
  rintro rfl
  exact h.not_isElliptic (by
    have : linOf (1 : isom d) = 1 := by
      have := linOf_mul (1 : isom d) 1; rw [one_mul] at this
      exact LinearEquiv.ext fun v => by
        have h2 := congrArg (fun A : Minkowski d ≃ₗ[ℝ] Minkowski d => (linOf (1 : isom d))⁻¹ (A v)) this
        simpa using h2.symm
    rw [this]; exact isElliptic_one)

/-- **A repulsive fixed point in `𝒥 ≅ 𝒮 × ℝ` of an isometry `γ`** (l.1254–1258, l.3199–3200):
`L(γ)` is loxodromic, the future null vector `(1, u)` is an eigenvector of `L(γ)` for an eigenvalue
`0 < λ < 1`, and the lightlike hyperplane `{⟨(1,u) | ·⟩ = s}` is `γ`-invariant, with
`⟨(1,u) | γ p⟩ − s = λ⁻¹ (⟨(1,u) | p⟩ − s)`: `γ` pushes points away from it. On `𝒮` this is
Externals' `IsRepulsiveFixed` (`IsRepulsiveFixedJ.isRepulsiveFixed`). -/
def IsRepulsiveFixedJ (γ : isom d) (w : PenroseSphere d × ℝ) : Prop :=
  IsLoxodromic (linOf γ) ∧ ∃ l : ℝ, 0 < l ∧ l < 1 ∧ linOf γ (nullVec w.1) = l • nullVec w.1 ∧
    ∀ p : Minkowski d, minkB (nullVec w.1) (γ • p) - w.2 = l⁻¹ * (minkB (nullVec w.1) p - w.2)

/-- **`Λ₀(Γ)`**, the repulsive fixed points in `𝒥` of the loxodromic elements of `Γ`
(l.3199–3200). -/
def loxRepSet (Γ : Subgroup (isom d)) : Set (PenroseSphere d × ℝ) :=
  {w | ∃ γ ∈ Γ, IsRepulsiveFixedJ γ w}

/-- **`Λ(Γ)`, the closure of `Λ₀(Γ)` in `𝒥`** (l.3203–3205; the `Λ(ρ)` of `bprop:admlox` and
`bdef:definitioncauchyhyp`, l.1232–1238, l.1277–1280). -/
def limitSetJ (Γ : Subgroup (isom d)) : Set (PenroseSphere d × ℝ) := closure (loxRepSet Γ)

theorem isClosed_limitSetJ (Γ : Subgroup (isom d)) : IsClosed (limitSetJ Γ) := isClosed_closure

theorem loxRepSet_subset_limitSetJ (Γ : Subgroup (isom d)) : loxRepSet Γ ⊆ limitSetJ Γ :=
  subset_closure

/-- `⟨(1,u) | γ p⟩ = λ⁻¹ ⟨(1,u) | p⟩` along the linear part, from the eigenvector equation. -/
theorem minkB_linOf_of_eigen {γ : isom d} {n : Minkowski d} {l : ℝ} (hl : l ≠ 0)
    (hn : linOf γ n = l • n) (p : Minkowski d) : minkB n (linOf γ p) = l⁻¹ * minkB n p := by
  have h := lorentz.minkB_apply (linOf_mem γ) n p
  rw [hn, minkB_smul_left] at h
  field_simp; linarith

/-- **The functional equation gives the eigenvector equation**: if an affine function
`⟨n | ·⟩ − s` is multiplied by `c⁻¹` under `γ`, then `L(γ) n = c n`. -/
theorem eigen_of_funEq {γ : isom d} {n : Minkowski d} {s c : ℝ} (hc : c ≠ 0)
    (h : ∀ p, minkB n (γ • p) - s = c⁻¹ * (minkB n p - s)) : linOf γ n = c • n := by
  have hlin : ∀ p, minkB n (linOf γ p) = c⁻¹ * minkB n p := fun p => by
    have h1 := h p
    have h0 := h 0
    rw [smul_eq_lin_add] at h1 h0
    rw [map_zero, zero_add, minkB_zero_right] at h0
    rw [minkB_add_right] at h1
    linarith
  have hz : ∀ z, minkB z (linOf γ n - c • n) = 0 := fun z => by
    obtain ⟨p, rfl⟩ := (linOf γ).surjective z
    rw [minkB_sub_right, minkB_smul_right, lorentz.minkB_apply (linOf_mem γ), minkB_comm p n,
      minkB_comm (linOf γ p) n, hlin p]
    field_simp; ring
  exact sub_eq_zero.1 (eq_zero_of_forall_minkB hz)

/-- **Existence of the repulsive fixed point** of a loxodromic isometry. -/
theorem exists_isRepulsiveFixedJ {γ : isom d} (h : IsLoxodromic (linOf γ)) :
    ∃ w, IsRepulsiveFixedJ γ w := by
  obtain ⟨-, u, u', l, -, -, -, hu0, hu0', hq, hq', -, hl, hl1, hAu, hAu', -⟩ := h.frame
  obtain ⟨e, μ, he0, heq, hμ0, hμ1, hAe⟩ : ∃ e : Minkowski d, ∃ μ : ℝ, e ≠ 0 ∧ minkQ e = 0 ∧
      0 < μ ∧ μ < 1 ∧ linOf γ e = μ • e := by
    rcases lt_or_gt_of_ne hl1 with h1 | h1
    · exact ⟨u, l, hu0, hq, hl, h1, hAu⟩
    · exact ⟨u', l⁻¹, hu0', hq', inv_pos.2 hl, inv_lt_one_of_one_lt₀ h1, hAu'⟩
  have he1 : e.1 ≠ 0 := fun h0 => he0 (eq_zero_of_fst_eq_zero h0 heq.le)
  have hnorm : ‖e.2‖ = |e.1| := by
    have h2 : ‖e.2‖ ^ 2 = |e.1| ^ 2 := by
      have := heq; simp only [minkQ] at this; rw [sq_abs]; linarith
    exact (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).1 h2
  set û : PenroseSphere d := ⟨e.1⁻¹ • e.2, by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, Real.norm_eq_abs, hnorm,
      inv_mul_cancel₀ (abs_ne_zero.2 he1)]⟩
  have hn : nullVec û = e.1⁻¹ • e := by
    refine Prod.ext ?_ rfl
    simp [nullVec, inv_mul_cancel₀ he1]
  have hAn : linOf γ (nullVec û) = μ • nullVec û := by
    rw [hn, map_smul, hAe, smul_comm]
  have hμ1' : (1 : ℝ) - μ⁻¹ ≠ 0 := by
    have : 1 < μ⁻¹ := one_lt_inv_iff₀.2 ⟨hμ0, hμ1⟩
    linarith
  refine ⟨(û, minkB (nullVec û) (trOf γ) / (1 - μ⁻¹)), h, μ, hμ0, hμ1, hAn, fun p => ?_⟩
  simp only
  rw [smul_eq_lin_add, minkB_add_right, minkB_linOf_of_eigen hμ0.ne' hAn]
  have hs : minkB (nullVec û) (trOf γ) / (1 - μ⁻¹) * (1 - μ⁻¹) = minkB (nullVec û) (trOf γ) :=
    div_mul_cancel₀ _ hμ1'
  linear_combination -hs

/-- **The repulsive fixed points of `γ` and of `γ⁻¹` have distinct null directions**: their
eigenvalues for `L(γ)` are `λ < 1` and `λ'⁻¹ > 1`. -/
theorem IsRepulsiveFixedJ.fst_ne {γ : isom d} {w w' : PenroseSphere d × ℝ}
    (hw : IsRepulsiveFixedJ γ w) (hw' : IsRepulsiveFixedJ γ⁻¹ w') : w.1 ≠ w'.1 := by
  obtain ⟨-, l, hl0, hl1, hAn, -⟩ := hw
  obtain ⟨-, l', hl0', hl1', hAn', -⟩ := hw'
  intro he
  rw [he] at hAn
  rw [linOf_inv] at hAn'
  have : linOf γ (nullVec w'.1) = l'⁻¹ • nullVec w'.1 := by
    have h2 := congrArg (linOf γ) hAn'
    simp only [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply, map_smul] at h2
    rw [eq_inv_smul_iff₀ hl0'.ne']; exact h2.symm
  rw [this] at hAn
  have hll : l'⁻¹ = l := smul_left_injective ℝ (nullVec_ne_zero w'.1) hAn
  have : 1 < l'⁻¹ := one_lt_inv_iff₀.2 ⟨hl0', hl1'⟩
  linarith

/-- The functional equation along iterates: `f(γⁿ p) = λ⁻ⁿ f(p)`. -/
theorem IsRepulsiveFixedJ.iterate {γ : isom d} {w : PenroseSphere d × ℝ} {l : ℝ}
    (h : ∀ p : Minkowski d, minkB (nullVec w.1) (γ • p) - w.2 = l⁻¹ * (minkB (nullVec w.1) p - w.2))
    (n : ℕ) (p : Minkowski d) :
    minkB (nullVec w.1) ((γ ^ n) • p) - w.2 = (l⁻¹) ^ n * (minkB (nullVec w.1) p - w.2) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', mul_smul, h, ih, pow_succ']; ring

/-- The functional equation of a repulsive point of `γ⁻¹`, read along `γ`: `f(γ p) = λ f(p)`. -/
theorem funEq_of_inv {γ : isom d} {w : PenroseSphere d × ℝ} {l : ℝ} (hl : l ≠ 0)
    (h : ∀ p : Minkowski d,
      minkB (nullVec w.1) (γ⁻¹ • p) - w.2 = l⁻¹ * (minkB (nullVec w.1) p - w.2))
    (p : Minkowski d) :
    minkB (nullVec w.1) (γ • p) - w.2 = l * (minkB (nullVec w.1) p - w.2) := by
  have := h (γ • p)
  rw [inv_smul_smul] at this
  rw [this]; field_simp

end RepulsiveFixed

/-! ## 1. The achronal domain of a loxodromic isometry: two quadrants -/

section Quadrants

/-- A vector with `minkQ ≤ 0` is future causal or past causal. -/
theorem isFutureCausal_or_neg_of_minkQ_nonpos {y : Minkowski d} (h : minkQ y ≤ 0) :
    IsFutureCausal y ∨ IsFutureCausal (-y) := by
  rcases le_total 0 y.1 with h1 | h1
  · exact Or.inl ⟨h1, h⟩
  · exact Or.inr ⟨by simpa using h1, by rw [minkQ_neg]; exact h⟩

/-- **Two future null vectors separating `y`** (`⟨n | y⟩ < 0 < ⟨n' | y⟩`) force `y` spacelike. -/
theorem minkQ_pos_of_minkB_sign {n n' y : Minkowski d} (hn : IsFutureCausal n)
    (hn' : IsFutureCausal n') (h1 : minkB n y < 0) (h2 : 0 < minkB n' y) : 0 < minkQ y := by
  by_contra hle
  rcases isFutureCausal_or_neg_of_minkQ_nonpos (not_lt.1 hle) with hy | hy
  · have := minkB_nonpos_of_isFutureCausal hn' hy; linarith
  · have := minkB_nonpos_of_isFutureCausal hn hy
    rw [minkB_neg_right] at this; linarith

/-- **The two quadrants lie in `Ω_γ`** (the easy half of [7.L], read in `𝒥`): for `w` a
repulsive fixed point of `γ` and `w'` one of `γ⁻¹`, both `P⁺(w) ∩ P⁺(w')` and `P⁻(w) ∩ P⁻(w')`
lie in the achronal domain of `γ`. -/
theorem quadrants_subset_achronalDomain {γ : isom d} {w w' : PenroseSphere d × ℝ}
    (hw : IsRepulsiveFixedJ γ w) (hw' : IsRepulsiveFixedJ γ⁻¹ w') :
    (halfPlus w.1 w.2 ∩ halfPlus w'.1 w'.2) ∪ (halfMinus w.1 w.2 ∩ halfMinus w'.1 w'.2) ⊆
      achronalDomain γ := by
  obtain ⟨-, l, hl0, hl1, -, hf⟩ := hw
  obtain ⟨-, l', hl0', hl1', -, hf'⟩ := hw'
  have hg' := funEq_of_inv hl0'.ne' hf'
  intro x hx
  rw [mem_achronalDomain_iff]
  intro n hn
  set y := (γ ^ n) • x - x
  have hB : minkB (nullVec w.1) y =
      ((l⁻¹) ^ n - 1) * (minkB (nullVec w.1) x - w.2) := by
    simp only [y, minkB_sub_right]
    have := IsRepulsiveFixedJ.iterate hf n x
    linarith
  have hB' : minkB (nullVec w'.1) y = (l' ^ n - 1) * (minkB (nullVec w'.1) x - w'.2) := by
    simp only [y, minkB_sub_right]
    have := IsRepulsiveFixedJ.iterate (l := l'⁻¹) (by simpa using hg') n x
    rw [inv_inv] at this
    linarith
  have hgt : 0 < (l⁻¹) ^ n - 1 := by
    have : 1 < l⁻¹ := one_lt_inv_iff₀.2 ⟨hl0, hl1⟩
    have := one_lt_pow₀ this hn.ne'
    linarith
  have hlt : l' ^ n - 1 < 0 := by
    have := pow_lt_one₀ hl0'.le hl1' hn.ne'
    linarith
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [mem_halfPlus] at h1 h2
    exact minkQ_pos_of_minkB_sign (isFutureCausal_nullVec w.1) (isFutureCausal_nullVec w'.1)
      (by rw [hB]; exact mul_neg_of_pos_of_neg hgt (by linarith))
      (by rw [hB']; exact mul_pos_of_neg_of_neg hlt (by linarith))
  · rw [mem_halfMinus] at h1 h2
    exact minkQ_pos_of_minkB_sign (isFutureCausal_nullVec w'.1) (isFutureCausal_nullVec w.1)
      (by rw [hB']; exact mul_neg_of_neg_of_pos hlt (by linarith))
      (by rw [hB]; exact mul_pos hgt (by linarith))

/-- **A null eigenvector of a loxodromic `L(γ)` lies on one of the two lines of its frame**, with
the frame's eigenvalue. -/
theorem null_eigen_cases {A : Minkowski d ≃ₗ[ℝ] Minkowski d} (hA : A ∈ lorentz d)
    {u u' : Minkowski d} {l : ℝ} (hu0 : u ≠ 0) (hu : minkQ u = 0) (hu'0 : u' ≠ 0)
    (hB : minkB u u' ≠ 0) (hl : 0 < l) (hl1 : l ≠ 1) (hAu : A u = l • u)
    (hAu' : A u' = l⁻¹ • u') {e : Minkowski d} (he0 : e ≠ 0) (he : minkQ e = 0) {μ : ℝ}
    (hAe : A e = μ • e) : (∃ c : ℝ, e = c • u ∧ μ = l) ∨ (∃ c : ℝ, e = c • u' ∧ μ = l⁻¹) := by
  have hQ : ∀ v, minkQ (A v) = minkQ v := lorentz.minkQ_apply hA
  have h1 := lorentz.minkB_apply hA e u
  have h2 := lorentz.minkB_apply hA e u'
  rw [hAe, hAu, minkB_smul_left, minkB_smul_right] at h1
  rw [hAe, hAu', minkB_smul_left, minkB_smul_right] at h2
  have hll : l * l ≠ 1 := fun h => hl1 (by nlinarith)
  have hll' : l⁻¹ * l⁻¹ ≠ 1 := fun h => hl1 (by
    have : l⁻¹ = 1 := by nlinarith [inv_pos.2 hl]
    simpa using this)
  by_cases hb' : minkB e u' = 0
  · by_cases hb : minkB e u = 0
    · exfalso
      obtain ⟨c, rfl⟩ := eq_smul_of_null_orth hu hu0 he (by rw [minkB_comm]; exact hb)
      rw [minkB_smul_left] at hb'
      have hc : c = 0 := (mul_eq_zero.1 hb').resolve_right hB
      exact he0 (by rw [hc, zero_smul])
    · have hμ : μ = l⁻¹ := by
        have : μ * l = 1 := by
          have : (μ * l - 1) * minkB e u = 0 := by linear_combination h1
          exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hb)
        field_simp; linarith
      right
      obtain ⟨c, hc⟩ := eigen_line hQ hll' hu'0 hAu' (w := e) (by rw [hAe, hμ])
      exact ⟨c, hc, hμ⟩
  · have hμ : μ = l := by
      have : μ * l⁻¹ = 1 := by
        have : (μ * l⁻¹ - 1) * minkB e u' = 0 := by linear_combination h2
        exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hb')
      field_simp at this; linarith
    left
    obtain ⟨c, hc⟩ := eigen_line hQ hll hu0 hAu (w := e) (by rw [hAe, hμ])
    exact ⟨c, hc, hμ⟩

theorem nullXY_smul_smul (u u' z : Minkowski d) {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    nullXY (a • u) (b • u') z = nullXY u u' z := by
  simp only [nullXY, minkB_smul_left, minkB_smul_right]
  by_cases h : minkB u u' = 0
  · simp [h]
  · field_simp

theorem nullXY_comm (u u' z : Minkowski d) : nullXY u u' z = nullXY u' u z := by
  simp only [nullXY, minkB_comm u u']; ring

/-- **[7.L] in `𝒥`, exactly**: the interior of the achronal domain of a loxodromic `γ` is the union
of the two quadrants `P⁺(w) ∩ P⁺(w')` (future complete) and `P⁻(w) ∩ P⁻(w')` (past complete),
`w` the repulsive fixed point of `γ` and `w'` that of `γ⁻¹` (any choice of either). These are
Barbot's `U⁺(γ)`, `U⁻(γ)` (l.3176–3178). -/
theorem interior_achronalDomain_eq_quadrants {γ : isom d} {w w' : PenroseSphere d × ℝ}
    (hw : IsRepulsiveFixedJ γ w) (hw' : IsRepulsiveFixedJ γ⁻¹ w') :
    interior (achronalDomain γ) =
      (halfPlus w.1 w.2 ∩ halfPlus w'.1 w'.2) ∪ (halfMinus w.1 w.2 ∩ halfMinus w'.1 w'.2) := by
  have hopen : IsOpen ((halfPlus w.1 w.2 ∩ halfPlus w'.1 w'.2) ∪
      (halfMinus w.1 w.2 ∩ halfMinus w'.1 w'.2)) :=
    ((isOpen_halfPlus _ _).inter (isOpen_halfPlus _ _)).union
      ((isOpen_halfMinus _ _).inter (isOpen_halfMinus _ _))
  refine Subset.antisymm ?_ (interior_maximal (quadrants_subset_achronalDomain hw hw') hopen)
  have hfst := hw.fst_ne hw'
  obtain ⟨hlox, lw, hlw0, hlw1, hAn, hf⟩ := hw
  obtain ⟨-, lw', hlw0', hlw1', -, hf'⟩ := hw'
  have hg' := funEq_of_inv hlw0'.ne' hf'
  have hAn' : linOf γ (nullVec w'.1) = lw'⁻¹ • nullVec w'.1 :=
    eigen_of_funEq (inv_ne_zero hlw0'.ne') (by simpa using hg')
  set n := nullVec w.1
  set n' := nullVec w'.1
  -- the normal form `g' = isomConj v γ`
  obtain ⟨v, hv⟩ := IsLoxodromic.exists_transConj_fixed γ.2 hlox
  set g' := isomConj v γ
  have hτ : linOf g' (trOf g') = trOf g' := by rw [linOf_isomConj]; exact hv
  have htr : trOf g' = v + γ • (-v) := by
    show transPart (transConj v (γ : Minkowski d ≃ᵃ[ℝ] Minkowski d)) = _
    rw [transPart, transConj_apply, add_zero, isom_smul_def]
  have hQ : ∀ x, minkQ (linOf γ x) = minkQ x := lorentz.minkQ_apply (linOf_mem γ)
  have hτ' : linOf γ (trOf g') = trOf g' := by rw [← linOf_isomConj v γ]; exact hτ
  -- the constants vanish in the normal form: `⟨n | v + z⟩ = ⟨n | z⟩ − s`
  have hc : minkB n v + w.2 = 0 := by
    have h0 : minkB (trOf g') n = 0 := minkB_fixed_eigen hQ hlw1.ne hτ' hAn
    rw [htr, minkB_add_left, minkB_comm, minkB_comm (γ • -v)] at h0
    have h1 := hf (-v)
    rw [minkB_neg_right] at h1
    have hl : lw⁻¹ ≠ 1 := by
      have : 1 < lw⁻¹ := one_lt_inv_iff₀.2 ⟨hlw0, hlw1⟩
      exact this.ne'
    have : (minkB n v + w.2) * (1 - lw⁻¹) = 0 := by linear_combination h0 - h1
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hl.symm)
  have hc' : minkB n' v + w'.2 = 0 := by
    have hne : lw'⁻¹ ≠ 1 := by
      have : 1 < lw'⁻¹ := one_lt_inv_iff₀.2 ⟨hlw0', hlw1'⟩
      exact this.ne'
    have h0 : minkB (trOf g') n' = 0 := minkB_fixed_eigen hQ hne hτ' hAn'
    rw [htr, minkB_add_left, minkB_comm, minkB_comm (γ • -v)] at h0
    have h1 := hg' (-v)
    rw [minkB_neg_right] at h1
    have : (minkB n' v + w'.2) * (1 - lw') = 0 := by linear_combination h0 - h1
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hlw1'.ne')
  -- the frame of `L(γ)`, and `nullXY` in terms of `n`, `n'`
  obtain ⟨-, u, u', l, -, -, -, hu0, hu0', hu, hu', hB, hl, hl1, hAu, hAu', -⟩ := hlox.frame
  have hint := interior_achronalDomain_lox (g := g') hu hu' hB hl hl1
    (by rw [linOf_isomConj]; exact hAu) (by rw [linOf_isomConj]; exact hAu') hτ
  have hnn' : minkB n n' < 0 := by
    rw [minkB_nullVec_nullVec]
    have : 0 < ‖((w.1 : PenroseSphere d) : EuclideanSpace ℝ (Fin d)) - w'.1‖ := by
      rw [norm_pos_iff, sub_ne_zero]; exact fun h => hfst (Subtype.ext h)
    have := pow_pos this 2
    linarith
  have hXY : ∀ x, nullXY u u' x = 2 * minkB x n * minkB x n' / minkB n n' := by
    intro x
    have key : ∀ (a b : ℝ) (e e' : Minkowski d), a ≠ 0 → b ≠ 0 → n = a • e → n' = b • e' →
        nullXY e e' x = 2 * minkB x n * minkB x n' / minkB n n' := by
      intro a b e e' ha hb hn hn'
      rw [← nullXY_smul_smul e e' x ha hb, ← hn, ← hn', nullXY]
    rcases null_eigen_cases (linOf_mem γ) hu0 hu hu0' hB hl hl1 hAu hAu'
        (nullVec_ne_zero w.1) (minkQ_nullVec w.1) hAn with ⟨a, ha, hla⟩ | ⟨a, ha, hla⟩ <;>
      rcases null_eigen_cases (linOf_mem γ) hu0 hu hu0' hB hl hl1 hAu hAu'
        (nullVec_ne_zero w'.1) (minkQ_nullVec w'.1) hAn' with ⟨b, hb, hlb⟩ | ⟨b, hb, hlb⟩
    · exfalso
      have : 1 < lw'⁻¹ := one_lt_inv_iff₀.2 ⟨hlw0', hlw1'⟩
      linarith
    · have ha0 : a ≠ 0 := fun h => nullVec_ne_zero w.1 (by rw [ha, h, zero_smul])
      have hb0 : b ≠ 0 := fun h => nullVec_ne_zero w'.1 (by rw [hb, h, zero_smul])
      exact key a b u u' ha0 hb0 ha hb
    · have ha0 : a ≠ 0 := fun h => nullVec_ne_zero w.1 (by rw [ha, h, zero_smul])
      have hb0 : b ≠ 0 := fun h => nullVec_ne_zero w'.1 (by rw [hb, h, zero_smul])
      rw [nullXY_comm]; exact key a b u' u ha0 hb0 ha hb
    · exfalso
      have : 1 < lw'⁻¹ := one_lt_inv_iff₀.2 ⟨hlw0', hlw1'⟩
      have : lw = lw'⁻¹ := by rw [hla, hlb]
      linarith
  -- conclusion
  intro z hz
  have hz' : v + z ∈ interior (achronalDomain g') := by
    have e1 : achronalDomain γ = (Homeomorph.addLeft v) ⁻¹' achronalDomain g' :=
      achronalDomain_eq_preimage_isomConj v γ
    rw [e1, ← Homeomorph.preimage_interior] at hz
    exact hz
  rw [hint, mem_setOf_eq, hXY, div_neg_iff] at hz'
  have hpos : 0 < minkB (v + z) n * minkB (v + z) n' := by
    rcases hz' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · linarith
    · linarith
  have e1 : minkB (v + z) n = minkB n z - w.2 := by
    rw [minkB_comm, minkB_add_right]; linarith
  have e2 : minkB (v + z) n' = minkB n' z - w'.2 := by
    rw [minkB_comm, minkB_add_right]; linarith
  rw [e1, e2] at hpos
  have hne : minkB n z - w.2 ≠ 0 := by
    intro h; rw [h, zero_mul] at hpos; exact lt_irrefl _ hpos
  rcases lt_or_gt_of_ne hne with h1 | h1
  · left
    refine ⟨mem_halfPlus.2 (by linarith), mem_halfPlus.2 ?_⟩
    by_contra h2; push Not at h2
    nlinarith
  · right
    refine ⟨mem_halfMinus.2 (by linarith), mem_halfMinus.2 ?_⟩
    by_contra h2; push Not at h2
    nlinarith

end Quadrants


/-! ## 2. `U(γ)` for the classes of §6, and the regular domains -/

section Classes

open Classical in
theorem Ug_eq_achronalDomain_of_isLoxodromic {g : isom d} (h : IsLoxodromic (linOf g)) :
    Ug g = achronalDomain g := by
  unfold Ug
  rw [if_neg (fun hN => h.not_isElliptic hN.1), if_neg (fun hL => hL.1.not_isLoxodromic h)]

/-- **[7.E] for a spacelike elliptic `g`, in any frame: `U(g) = Ω_g = 𝐌ⁿ`.** -/
theorem achronalDomain_eq_univ_of_isSpacelikeElliptic {g : isom d} (h : IsSpacelikeElliptic g) :
    achronalDomain g = univ := by
  obtain ⟨hE, x, hx1, hx2⟩ := h
  have htr : trOf (isomConj (-x) g) = g • x - x := by
    rw [trOf_isomConj, map_neg, pOf_apply, smul_eq_lin_add]; abel
  rw [achronalDomain_eq_preimage_isomConj (-x) g,
    achronalDomain_elliptic_spacelike (g := isomConj (-x) g) (by rw [linOf_isomConj]; exact hE)
      (by rw [linOf_isomConj, htr]; exact hx1) (by rw [htr]; exact hx2), preimage_univ]

/-- **[7.P] for a tangent parabolic `g`, in any frame: `Ω_g = 𝐌ⁿ`.** -/
theorem achronalDomain_eq_univ_of_isTangentParabolic {g : isom d} (h : IsTangentParabolic g) :
    achronalDomain g = univ := by
  obtain ⟨R, U, ⟨hR, hU, hRe, hn, hU1, hg, hc⟩, hT⟩ := h
  have hrange := parabolic_range_le_minkOrth_nullPart hR hU hRe hn hU1 hc
  obtain ⟨vₙ, v₁, -, h1, -, -, -, -, hq1, -⟩ := unipotent_frame hU.1 hn (pOf_ne_zero hU1)
  obtain ⟨v, hv, -⟩ := parabolic_exists_transConj_normal hR hU hRe hn hU1 hc hg
    (v₁ := v₁) ⟨vₙ, h1⟩ hq1.ne'
  have hT' : IsTangentCase U (transConj v (g : Minkowski d ≃ᵃ[ℝ] Minkowski d)) := by
    refine ⟨?_, fun h' => hT.2 ((isLinearCase_transConj_iff v _).1 h')⟩
    have hr : LinearMap.range (pOf (linOf g)) ≤ minkOrth (nullPart U) := by
      rw [hg]; exact hrange
    rw [transPart_transConj_mem_iff hr v]; exact hT.1
  rw [achronalDomain_eq_preimage_isomConj v g,
    achronalDomain_parabolic_tangent hR hU hRe hn hU1 hc
      (g := isomConj v g) (by rw [linOf_isomConj]; exact hg) hv hT', preimage_univ]

/-- A real `β` with `kβ` bounded above on both sides of `0` (`k ∈ ℕ`) is `0`. -/
theorem eq_zero_of_nat_mul_le {β C : ℝ} (h1 : ∀ k : ℕ, (k : ℝ) * β ≤ C)
    (h2 : ∀ k : ℕ, -((k : ℝ) * β) ≤ C) : β = 0 := by
  by_contra hβ
  rcases lt_or_gt_of_ne hβ with hβ | hβ
  · obtain ⟨k, hk⟩ := exists_nat_gt (C / -β)
    have := h2 k
    rw [div_lt_iff₀ (by linarith)] at hk
    linarith
  · obtain ⟨k, hk⟩ := exists_nat_gt (C / β)
    have := h1 k
    rw [div_lt_iff₀ hβ] at hk
    linarith

section LinearParabolic

variable {γ : isom d} {R U : Minkowski d ≃ₗ[ℝ] Minkowski d} (hp : IsParabolicPair γ R U)
  {c : Minkowski d} (hc : γ • c = c) {y : Minkowski d} (hy : y ∈ minkOrth (nullPart U))
include hp hc hy

/-- **The forward orbit** of `c + y`, `y ∈ J^⊥`: `γᵏ(c + y) = c + Rᵏ y + k p(y)`. -/
theorem linearParabolic_orbit_fwd (k : ℕ) :
    (γ ^ k) • (c + y) = c + ((R ^ k) y + (k : ℝ) • pOf U y) := by
  obtain ⟨hR, hU, hRe, hn, hU1, hg, hcomm⟩ := hp
  have hpy : pOf U y ∈ nullPart U := pOf_mem_nullPart hU.1 hn (pOf_ne_zero hU1) hy
  have hUpy : U (pOf U y) = pOf U y := by
    have := pOf_eq_zero_of_mem_nullPart hU.1 hpy
    rwa [pOf_apply, sub_eq_zero] at this
  have hRpy : R (pOf U y) = pOf U y := parabolic_R_fix_range hR hU hRe hn hU1 hcomm ⟨y, rfl⟩
  have hRk : ∀ k : ℕ, (R ^ k) (pOf U y) = pOf U y := fun k => pow_apply_eq_self hRpy k
  have hγp : ∀ p, γ • p = linOf γ (p - c) + c := fun p => by
    have := smul_sub_smul γ p c; rw [hc] at this; rw [← this]; abel
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_smul, ih, hγp, add_sub_cancel_left, hg, LinearEquiv.mul_apply,
      map_add, map_smul, hUpy, map_add, map_smul, hRpy]
    have hcomm' : U ((R ^ k) y) = (R ^ k) (U y) := by
      rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply,
        ((Commute.pow_left (show Commute R U from hcomm) k).eq).symm]
    rw [hcomm', apply_eq_add_pOf U y, map_add, hRk, map_add, hRpy, ← LinearEquiv.mul_apply,
      ← pow_succ']
    push_cast
    module

/-- **The backward orbit**: `γ⁻ᵏ(c + y) = c + R⁻ᵏ y − k p(y)`. -/
theorem linearParabolic_orbit_bwd (k : ℕ) :
    (γ⁻¹ ^ k) • (c + y) = c + (((R⁻¹) ^ k) y - (k : ℝ) • pOf U y) := by
  obtain ⟨hR, hU, hRe, hn, hU1, hg, hcomm⟩ := hp
  have hpy : pOf U y ∈ nullPart U := pOf_mem_nullPart hU.1 hn (pOf_ne_zero hU1) hy
  have hUpy : U (pOf U y) = pOf U y := by
    have := pOf_eq_zero_of_mem_nullPart hU.1 hpy
    rwa [pOf_apply, sub_eq_zero] at this
  have hRpy : R (pOf U y) = pOf U y := parabolic_R_fix_range hR hU hRe hn hU1 hcomm ⟨y, rfl⟩
  have hRipy : R⁻¹ (pOf U y) = pOf U y := by
    conv_lhs => rw [← hRpy]
    simp
  have hRik : ∀ k : ℕ, ((R⁻¹) ^ k) (pOf U y) = pOf U y := fun k => pow_apply_eq_self hRipy k
  have hUR : ∀ z, U (R⁻¹ z) = R⁻¹ (U z) := fun z => by
    apply R.injective
    have h1 : R (U (R⁻¹ z)) = U (R (R⁻¹ z)) := by
      rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, hcomm]
      simp only [LinearEquiv.mul_apply]
    rw [h1]; simp
  have hURk : ∀ k : ℕ, ∀ z, U (((R⁻¹) ^ k) z) = ((R⁻¹) ^ k) (U z) := by
    intro k; induction k with
    | zero => intro z; simp
    | succ k ih => intro z; rw [pow_succ', LinearEquiv.mul_apply, LinearEquiv.mul_apply, hUR, ih]
  have hci : γ⁻¹ • c = c := by rw [inv_smul_eq_iff, hc]
  have hγp : ∀ p, γ⁻¹ • p = linOf γ⁻¹ (p - c) + c := fun p => by
    have := smul_sub_smul γ⁻¹ p c; rw [hci] at this; rw [← this]; abel
  -- `L(γ)⁻¹ (R⁻ᵏ y) = R⁻ᵏ⁻¹ y − p(y)`
  have hstep : ∀ k : ℕ, linOf γ⁻¹ (((R⁻¹) ^ k) y) = ((R⁻¹) ^ (k + 1)) y - pOf U y := by
    intro k
    rw [linOf_inv]
    have this : linOf γ (((R⁻¹) ^ (k + 1)) y - pOf U y) = ((R⁻¹) ^ k) y := by
      have e1 : U (((R⁻¹) ^ (k + 1)) y) = ((R⁻¹) ^ (k + 1)) y + pOf U y := by
        rw [hURk]
        conv_lhs => rw [apply_eq_add_pOf U y]
        rw [map_add, hRik]
      have e2 : R (((R⁻¹) ^ (k + 1)) y) = ((R⁻¹) ^ k) y := by
        rw [pow_succ', LinearEquiv.mul_apply]; simp
      rw [hg, LinearEquiv.mul_apply, map_sub, e1, hUpy, map_sub, map_add, e2, hRpy]
      abel
    rw [← this]; simp
  have hLpy : linOf γ⁻¹ (pOf U y) = pOf U y := by
    rw [linOf_inv]
    have : linOf γ (pOf U y) = pOf U y := by rw [hg, LinearEquiv.mul_apply, hUpy, hRpy]
    conv_lhs => rw [← this]
    simp
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_smul, ih, hγp, add_sub_cancel_left, map_sub, map_smul, hstep, hLpy]
    push_cast
    module

end LinearParabolic

/-- The iterates of an elliptic `R` (and of `R⁻¹`) keep a vector in a bounded set: they preserve
the euclidean form of `IsElliptic`, which is coercive. -/
theorem IsElliptic.bounded_orbit {R : Minkowski d ≃ₗ[ℝ] Minkowski d} (hRe : IsElliptic R)
    (y : Minkowski d) : ∃ K : ℝ, ∀ k : ℕ, ‖(R ^ k) y‖ ^ 2 ≤ K ∧ ‖((R⁻¹) ^ k) y‖ ^ 2 ≤ K := by
  obtain ⟨E, -, hEp, hE⟩ := hRe
  obtain ⟨m, hm, hcoer⟩ := exists_coercive E hEp
  have hE' : ∀ v w, E (R⁻¹ v) (R⁻¹ w) = E v w := fun v w => by
    rw [← hE (R⁻¹ v) (R⁻¹ w)]; simp
  have h1 : ∀ k : ℕ, E ((R ^ k) y) ((R ^ k) y) = E y y := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', LinearEquiv.mul_apply, hE, ih]
  have h2 : ∀ k : ℕ, E (((R⁻¹) ^ k) y) (((R⁻¹) ^ k) y) = E y y := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', LinearEquiv.mul_apply, hE', ih]
  refine ⟨E y y / m, fun k => ⟨?_, ?_⟩⟩
  · rw [le_div_iff₀ hm]; have := hcoer ((R ^ k) y); rw [h1] at this; linarith
  · rw [le_div_iff₀ hm]; have := hcoer (((R⁻¹) ^ k) y); rw [h2] at this; linarith

/-- `|⟨(1,u) | z⟩| ≤ (1 + 4‖z‖²)/2`, a bound with no square root. -/
theorem abs_minkB_nullVec_le_sq (u : PenroseSphere d) (z : Minkowski d) :
    |minkB (nullVec u) z| ≤ (1 + 4 * ‖z‖ ^ 2) / 2 := by
  have h := abs_minkB_nullVec_le_two_mul_norm u z
  nlinarith [norm_nonneg z, sq_nonneg (2 * ‖z‖ - 1)]


/-- A null function `⟨(1,u) | ·⟩` bounded on one side of a set. -/
def OneSidedOn (Ω : Set (Minkowski d)) (u : PenroseSphere d) : Prop :=
  (∃ M, ∀ p ∈ Ω, minkB (nullVec u) p ≤ M) ∨ ∃ M, ∀ p ∈ Ω, M ≤ minkB (nullVec u) p

/-- **The core of `blem:sanlox`, corrected** (l.3153–3165): an open set `Ω` invariant under a
linear parabolic `γ` and `γ⁻¹`, on which the null functions of two distinct directions are
bounded on one side, misses the null hyperplanes `c + J^⊥` of `γ`. Barbot's argument, made
exact: on the `γ`-orbit of a point `c + y`, `y ∈ J^⊥`, `⟨n | ·⟩` is `⟨n | c⟩ + ⟨n | Rᵏ y⟩ ± k ⟨n | p(y)⟩`
with the middle term bounded, so a one-sided bound forces `⟨n | p(y)⟩ = 0`; `p(y)` spans the null
line `J` once `y` is moved off `ker p` inside `Ω`, and two distinct null directions cannot both be
orthogonal to `J`. -/
theorem subset_compl_nullHyperplanes_of_oneSided {γ : isom d} {Ω : Set (Minkowski d)}
    (hΩ : IsOpen Ω) (hinv : ∀ p ∈ Ω, γ • p ∈ Ω) (hinv' : ∀ p ∈ Ω, γ⁻¹ • p ∈ Ω)
    {u₁ u₂ : PenroseSphere d} (hu : u₁ ≠ u₂) (hb₁ : OneSidedOn Ω u₁) (hb₂ : OneSidedOn Ω u₂) :
    Ω ⊆ (nullHyperplanes γ)ᶜ := by
  rintro x hx ⟨R, U, hp, c, hc, hy⟩
  obtain ⟨hR, hU, hRe, hn, hU1, hg, hcomm⟩ := hp
  have hp' : IsParabolicPair γ R U := ⟨hR, hU, hRe, hn, hU1, hg, hcomm⟩
  have hp0 := pOf_ne_zero hU1
  -- move `y = x − c` off `ker p` inside `Ω`
  obtain ⟨y, hyJ, hyΩ, hpy0⟩ : ∃ y, y ∈ minkOrth (nullPart U) ∧ c + y ∈ Ω ∧ pOf U y ≠ 0 := by
    by_cases h0 : pOf U (x - c) = 0
    · obtain ⟨vₙ, v₁, v₀, h1, h2, hv₀, -⟩ := unipotent_frame hU.1 hn hp0
      have hv₁ : v₁ ∈ minkOrth (nullPart U) := range_le_minkOrth_nullPart U ⟨vₙ, h1⟩
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hΩ x hx
      set ε : ℝ := r / (2 * (‖v₁‖ + 1))
      have hε : 0 < ε := by positivity
      refine ⟨x - c + ε • v₁, add_mem hy (Submodule.smul_mem _ _ hv₁), ?_, ?_⟩
      · refine hball ?_
        rw [Metric.mem_ball, show c + (x - c + ε • v₁) = x + ε • v₁ by abel, dist_eq_norm,
          add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
        have : ε * ‖v₁‖ ≤ r / 2 := by
          simp only [ε]; rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) two_pos]
          nlinarith [norm_nonneg v₁]
        linarith
      · rw [map_add, h0, zero_add, map_smul, h2]
        exact smul_ne_zero hε.ne' hv₀
    · exact ⟨x - c, hy, by rwa [add_sub_cancel], h0⟩
  have hpyN : pOf U y ∈ nullPart U := pOf_mem_nullPart hU.1 hn hp0 hyJ
  have hpyQ : minkQ (pOf U y) = 0 := minkQ_eq_zero_of_mem_nullPart hpyN
  -- the orbit stays in `Ω`
  have hfwd : ∀ k : ℕ, (γ ^ k) • (c + y) ∈ Ω := by
    intro k; induction k with
    | zero => simpa using hyΩ
    | succ k ih => rw [pow_succ', mul_smul]; exact hinv _ ih
  have hbwd : ∀ k : ℕ, (γ⁻¹ ^ k) • (c + y) ∈ Ω := by
    intro k; induction k with
    | zero => simpa using hyΩ
    | succ k ih => rw [pow_succ', mul_smul]; exact hinv' _ ih
  obtain ⟨K, hK⟩ := hRe.bounded_orbit y
  -- a one-sided bound kills `⟨n | p(y)⟩`
  have hkill : ∀ u : PenroseSphere d, OneSidedOn Ω u → minkB (nullVec u) (pOf U y) = 0 := by
    intro u hb
    set β := minkB (nullVec u) (pOf U y)
    have hf : ∀ k : ℕ, minkB (nullVec u) ((γ ^ k) • (c + y)) =
        minkB (nullVec u) c + minkB (nullVec u) ((R ^ k) y) + (k : ℝ) * β := by
      intro k
      rw [linearParabolic_orbit_fwd hp' hc hyJ k, minkB_add_right, minkB_add_right,
        minkB_smul_right]; ring
    have hb' : ∀ k : ℕ, minkB (nullVec u) ((γ⁻¹ ^ k) • (c + y)) =
        minkB (nullVec u) c + minkB (nullVec u) (((R⁻¹) ^ k) y) - (k : ℝ) * β := by
      intro k
      rw [linearParabolic_orbit_bwd hp' hc hyJ k, minkB_add_right, minkB_sub_right,
        minkB_smul_right]; ring
    have hB1 : ∀ k : ℕ, |minkB (nullVec u) ((R ^ k) y)| ≤ (1 + 4 * K) / 2 := fun k =>
      (abs_minkB_nullVec_le_sq u _).trans (by linarith [(hK k).1])
    have hB2 : ∀ k : ℕ, |minkB (nullVec u) (((R⁻¹) ^ k) y)| ≤ (1 + 4 * K) / 2 := fun k =>
      (abs_minkB_nullVec_le_sq u _).trans (by linarith [(hK k).2])
    rcases hb with ⟨M, hM⟩ | ⟨M, hM⟩
    · refine eq_zero_of_nat_mul_le (C := M - minkB (nullVec u) c + (1 + 4 * K) / 2)
        (fun k => ?_) (fun k => ?_)
      · have := hM _ (hfwd k); rw [hf] at this
        linarith [neg_abs_le (minkB (nullVec u) ((R ^ k) y)), hB1 k]
      · have := hM _ (hbwd k); rw [hb'] at this
        linarith [neg_abs_le (minkB (nullVec u) (((R⁻¹) ^ k) y)), hB2 k]
    · refine eq_zero_of_nat_mul_le (C := minkB (nullVec u) c - M + (1 + 4 * K) / 2)
        (fun k => ?_) (fun k => ?_)
      · have := hM _ (hbwd k); rw [hb'] at this
        linarith [le_abs_self (minkB (nullVec u) (((R⁻¹) ^ k) y)), hB2 k]
      · have := hM _ (hfwd k); rw [hf] at this
        linarith [le_abs_self (minkB (nullVec u) ((R ^ k) y)), hB1 k]
  -- two distinct directions orthogonal to the null `p(y)`
  obtain ⟨c₁, hc₁⟩ := eq_smul_of_null_orth hpyQ hpy0 (minkQ_nullVec u₁)
    (by rw [minkB_comm]; exact hkill u₁ hb₁)
  obtain ⟨c₂, hc₂⟩ := eq_smul_of_null_orth hpyQ hpy0 (minkQ_nullVec u₂)
    (by rw [minkB_comm]; exact hkill u₂ hb₂)
  have hc₂0 : c₂ ≠ 0 := fun h => nullVec_ne_zero u₂ (by rw [hc₂, h, zero_smul])
  exact hu (nullVec_injective_smul (c := c₁ / c₂) (by
    rw [hc₁, hc₂, smul_smul, div_mul_cancel₀ _ hc₂0]))

end Classes


/-! ## 3. The limit set is invariant; the two regular domains `Ω^±(Λ(Γ))` -/

section Invariance

/-- **Conjugation carries repulsive fixed points**: `g.w` (the action `isomPenrose` on `𝒥`,
l.829–845) is the repulsive fixed point of `g γ g⁻¹`. -/
theorem IsRepulsiveFixedJ.conj {γ : isom d} {w : PenroseSphere d × ℝ}
    (hw : IsRepulsiveFixedJ γ w) (g : isom d) :
    IsRepulsiveFixedJ (g * γ * g⁻¹) (isomPenrose g w) := by
  obtain ⟨hlox, l, hl0, hl1, -, hf⟩ := hw
  have hfun : ∀ q : Minkowski d, minkB (nullVec (isomPenrose g w).1) ((g * γ * g⁻¹) • q) -
      (isomPenrose g w).2 = l⁻¹ * (minkB (nullVec (isomPenrose g w).1) q - (isomPenrose g w).2) := by
    intro q
    obtain ⟨p, rfl⟩ : ∃ p, q = g • p := ⟨g⁻¹ • q, by rw [smul_inv_smul]⟩
    rw [show (g * γ * g⁻¹) • (g • p) = g • (γ • p) by simp [mul_smul],
      minkB_isomPenrose, minkB_isomPenrose, hf]
    ring
  refine ⟨?_, l, hl0, hl1, eigen_of_funEq hl0.ne' hfun, hfun⟩
  rw [linOf_mul, linOf_mul, linOf_inv]
  exact hlox.conj (linOf_mem g)

variable {Γ : Subgroup (isom d)}

/-- `Λ₀(Γ)` is `Γ`-invariant under the action on `𝒥`. -/
theorem isomPenrose_mem_loxRepSet {η : isom d} (hη : η ∈ Γ) {w : PenroseSphere d × ℝ}
    (hw : w ∈ loxRepSet Γ) : isomPenrose η w ∈ loxRepSet Γ := by
  obtain ⟨γ, hγ, hr⟩ := hw
  exact ⟨_, Γ.mul_mem (Γ.mul_mem hη hγ) (Γ.inv_mem hη), hr.conj η⟩

/-- The pull-back of a null half-space through an isometry. -/
theorem smul_mem_halfPlus_iff (η : isom d) (w : PenroseSphere d × ℝ) (p : Minkowski d) :
    η • p ∈ halfPlus w.1 w.2 ↔ p ∈ halfPlus (isomPenrose η⁻¹ w).1 (isomPenrose η⁻¹ w).2 := by
  rw [← isom_preimage_halfPlus η⁻¹ w, mem_preimage, inv_smul_smul]

theorem smul_mem_halfMinus_iff (η : isom d) (w : PenroseSphere d × ℝ) (p : Minkowski d) :
    η • p ∈ halfMinus w.1 w.2 ↔ p ∈ halfMinus (isomPenrose η⁻¹ w).1 (isomPenrose η⁻¹ w).2 := by
  rw [← isom_preimage_halfMinus η⁻¹ w, mem_preimage, inv_smul_smul]

theorem smul_mem_omegaPlus_loxRepSet {η : isom d} (hη : η ∈ Γ) {p : Minkowski d}
    (hp : p ∈ omegaPlus (loxRepSet Γ)) : η • p ∈ omegaPlus (loxRepSet Γ) :=
  mem_omegaPlus.2 fun w hw => mem_halfPlus.1 ((smul_mem_halfPlus_iff η w p).2
    (mem_halfPlus.2 (mem_omegaPlus.1 hp _ (isomPenrose_mem_loxRepSet (Γ.inv_mem hη) hw))))

theorem smul_mem_omegaMinus_loxRepSet {η : isom d} (hη : η ∈ Γ) {p : Minkowski d}
    (hp : p ∈ omegaMinus (loxRepSet Γ)) : η • p ∈ omegaMinus (loxRepSet Γ) :=
  mem_omegaMinus.2 fun w hw => mem_halfMinus.1 ((smul_mem_halfMinus_iff η w p).2
    (mem_halfMinus.2 (mem_omegaMinus.1 hp _ (isomPenrose_mem_loxRepSet (Γ.inv_mem hη) hw))))

theorem smul_mem_interior_of {η : isom d} {A : Set (Minkowski d)} (hA : ∀ p ∈ A, η • p ∈ A)
    {p : Minkowski d} (hp : p ∈ interior A) : η • p ∈ interior A := by
  have : interior A ⊆ (fun q => η • q) ⁻¹' interior A := by
    rw [← isom.coe_toHomeomorph, Homeomorph.preimage_interior]
    exact interior_mono fun q hq => hA q hq
  exact this hp

/-- **`Ω⁺(Λ(Γ))` is `Γ`-invariant** (`Ω⁺(Λ(Γ)) = Int Ω⁺(Λ₀)`, `blem:fermonsbis`). -/
theorem smul_mem_omegaPlus_limitSetJ {η : isom d} (hη : η ∈ Γ) {p : Minkowski d}
    (hp : p ∈ omegaPlus (limitSetJ Γ)) : η • p ∈ omegaPlus (limitSetJ Γ) := by
  rw [limitSetJ, omegaPlus_closure_eq_interior] at hp ⊢
  exact smul_mem_interior_of (fun q hq => smul_mem_omegaPlus_loxRepSet hη hq) hp

theorem smul_mem_omegaMinus_limitSetJ {η : isom d} (hη : η ∈ Γ) {p : Minkowski d}
    (hp : p ∈ omegaMinus (limitSetJ Γ)) : η • p ∈ omegaMinus (limitSetJ Γ) := by
  rw [limitSetJ, omegaMinus_closure_eq_interior] at hp ⊢
  exact smul_mem_interior_of (fun q hq => smul_mem_omegaMinus_loxRepSet hη hq) hp

/-- `Γ` preserves `Ω⁺(Λ(Γ))`, in `Flat.Examples`' form. -/
theorem preservesOmega_limitSetJ (Γ : Subgroup (isom d)) :
    PreservesOmega (limitSetJ Γ) Γ := fun γ hγ => by
  ext p
  refine ⟨fun hp => ?_, fun hp => smul_mem_omegaPlus_limitSetJ hγ hp⟩
  have := smul_mem_omegaPlus_limitSetJ (Γ.inv_mem hγ) hp
  rwa [inv_smul_smul] at this

/-- The two distinct null directions of `Λ₀(Γ)` given by one loxodromic element. -/
theorem exists_two_loxRepSet {γ : isom d} (hγ : γ ∈ Γ) (hlox : IsLoxodromic (linOf γ)) :
    ∃ w ∈ loxRepSet Γ, ∃ w' ∈ loxRepSet Γ, IsRepulsiveFixedJ γ w ∧ IsRepulsiveFixedJ γ⁻¹ w' ∧
      w.1 ≠ w'.1 := by
  obtain ⟨w, hw⟩ := exists_isRepulsiveFixedJ hlox
  obtain ⟨w', hw'⟩ := exists_isRepulsiveFixedJ (isLoxodromic_linOf_inv hlox)
  exact ⟨w, ⟨γ, hγ, hw⟩, w', ⟨γ⁻¹, Γ.inv_mem hγ, hw'⟩, hw, hw', hw.fst_ne hw'⟩

end Invariance

/-! ## 4. `blem:sanlox` (Lemma 10.1) -/

section Sanlox

variable {Γ : Subgroup (isom d)} {S : Set (Minkowski d)}

/-- **Barbot's `U_lox(Γ)`** (l.3136–3138): the intersection of the `U(γ)` over the loxodromic
elements of `Γ`. -/
def UGammaLox (Γ : Subgroup (isom d)) : Set (Minkowski d) :=
  {x | ∀ γ ∈ Γ, IsLoxodromic (linOf γ) → x ∈ Ug γ}

/-- **Barbot's `Ω_lox(Γ)`** (l.3136–3138): the interior of `U_lox(Γ)`. -/
def omegaLox (Γ : Subgroup (isom d)) : Set (Minkowski d) := interior (UGammaLox Γ)

/-- **`blem:sanlox`, the inclusion "obvious" in the paper** (l.3148): `Ω(Γ) ⊆ Ω_lox(Γ)`. -/
theorem omegaGamma_subset_omegaLox (Γ : Subgroup (isom d)) : omegaGamma Γ ⊆ omegaLox Γ :=
  interior_mono fun _ hx γ hγ hlox => hx γ hγ (ne_one_of_isLoxodromic hlox)

/-- **`blem:sanlox` in its corrected, proved form**: every `Γ`-invariant open set `Ω ⊆ U_lox(Γ)`
on which two distinct null directions are bounded on one side lies in `U(Γ)`, hence in `Ω(Γ)`
(the standing hypotheses of §8, `CCAction`, are what exclude nonspacelike elliptic and
transverse parabolic elements, Rem 8.9). The two regular domains `Ω^±(Λ(Γ))` are such sets
(`omegaPlus_limitSetJ_subset_omegaGamma`). The class analysis is Barbot's (l.3150–3165): tangent
parabolic and spacelike elliptic `γ` have `U(γ) = 𝐌ⁿ`, a linear parabolic one is excluded by
`subset_compl_nullHyperplanes_of_oneSided`. -/
theorem subset_UGamma_of_oneSided (h : CCAction Γ S) {Ω : Set (Minkowski d)} (hΩ : IsOpen Ω)
    (hinv : ∀ η ∈ Γ, ∀ p ∈ Ω, η • p ∈ Ω)
    (hlox : ∀ γ ∈ Γ, IsLoxodromic (linOf γ) → Ω ⊆ achronalDomain γ)
    {u₁ u₂ : PenroseSphere d} (hu : u₁ ≠ u₂) (hb₁ : OneSidedOn Ω u₁) (hb₂ : OneSidedOn Ω u₂) :
    Ω ⊆ UGamma Γ := by
  intro x hx γ hγ h1
  obtain ⟨hN, hT, -⟩ := nini h hγ h1
  classical
  unfold Ug
  rw [if_neg hN]
  by_cases h3 : IsLinearParabolic γ
  · rw [if_pos h3]
    exact subset_compl_nullHyperplanes_of_oneSided hΩ (hinv γ hγ) (hinv γ⁻¹ (Γ.inv_mem hγ)) hu
      hb₁ hb₂ hx
  · rw [if_neg h3]
    rcases classes_of_not lorentzTrichotomy hN h3 with hX | hX | hX | hX
    · exact hlox γ hγ hX hx
    · rw [achronalDomain_eq_univ_of_isSpacelikeElliptic hX]; trivial
    · rw [achronalDomain_eq_univ_of_isTangentParabolic hX]; trivial
    · exact (hT hX).elim

theorem oneSidedOn_omegaPlus {Λ : Set (PenroseSphere d × ℝ)} {w : PenroseSphere d × ℝ}
    (hw : w ∈ Λ) : OneSidedOn (omegaPlus Λ) w.1 :=
  Or.inl ⟨w.2, fun _ hp => (mem_omegaPlus.1 hp w hw).le⟩

theorem oneSidedOn_omegaMinus {Λ : Set (PenroseSphere d × ℝ)} {w : PenroseSphere d × ℝ}
    (hw : w ∈ Λ) : OneSidedOn (omegaMinus Λ) w.1 :=
  Or.inr ⟨w.2, fun _ hp => (mem_omegaMinus.1 hp w hw).le⟩

/-- **`Ω⁺(Λ(Γ)) ⊆ Ω(Γ)`** when `Γ` has a loxodromic element (standing hypotheses of §8). -/
theorem omegaPlus_limitSetJ_subset_omegaGamma (h : CCAction Γ S) {γ₀ : isom d} (hγ₀ : γ₀ ∈ Γ)
    (hlox₀ : IsLoxodromic (linOf γ₀)) : omegaPlus (limitSetJ Γ) ⊆ omegaGamma Γ := by
  obtain ⟨w₁, hw₁, w₂, hw₂, -, -, hne⟩ := exists_two_loxRepSet hγ₀ hlox₀
  refine interior_maximal (subset_UGamma_of_oneSided h (isOpen_omegaPlus_of_isClosed
    (isClosed_limitSetJ Γ)) (fun η hη p hp => smul_mem_omegaPlus_limitSetJ hη hp)
    (fun γ hγ hlox => ?_) hne (oneSidedOn_omegaPlus (subset_closure hw₁))
    (oneSidedOn_omegaPlus (subset_closure hw₂))) (isOpen_omegaPlus_of_isClosed
      (isClosed_limitSetJ Γ))
  obtain ⟨w, hw, w', hw', hr, hr', -⟩ := exists_two_loxRepSet hγ hlox
  exact fun p hp => quadrants_subset_achronalDomain hr hr' (Or.inl
    ⟨mem_halfPlus.2 (mem_omegaPlus.1 hp w (subset_closure hw)),
      mem_halfPlus.2 (mem_omegaPlus.1 hp w' (subset_closure hw'))⟩)

/-- **`Ω⁻(Λ(Γ)) ⊆ Ω(Γ)`**, likewise. -/
theorem omegaMinus_limitSetJ_subset_omegaGamma (h : CCAction Γ S) {γ₀ : isom d} (hγ₀ : γ₀ ∈ Γ)
    (hlox₀ : IsLoxodromic (linOf γ₀)) : omegaMinus (limitSetJ Γ) ⊆ omegaGamma Γ := by
  obtain ⟨w₁, hw₁, w₂, hw₂, -, -, hne⟩ := exists_two_loxRepSet hγ₀ hlox₀
  refine interior_maximal (subset_UGamma_of_oneSided h (isOpen_omegaMinus_of_isClosed
    (isClosed_limitSetJ Γ)) (fun η hη p hp => smul_mem_omegaMinus_limitSetJ hη hp)
    (fun γ hγ hlox => ?_) hne (oneSidedOn_omegaMinus (subset_closure hw₁))
    (oneSidedOn_omegaMinus (subset_closure hw₂))) (isOpen_omegaMinus_of_isClosed
      (isClosed_limitSetJ Γ))
  obtain ⟨w, hw, w', hw', hr, hr', -⟩ := exists_two_loxRepSet hγ hlox
  exact fun p hp => quadrants_subset_achronalDomain hr hr' (Or.inr
    ⟨mem_halfMinus.2 (mem_omegaMinus.1 hp w (subset_closure hw)),
      mem_halfMinus.2 (mem_omegaMinus.1 hp w' (subset_closure hw'))⟩)

/-! ### The sign of `U_lox(Γ)` is uniform: the replacement for l.3157's convexity -/


theorem minkQ_sub_eq (v w : Minkowski d) : minkQ (v - w) = minkQ v - 2 * minkB v w + minkQ w := by
  rw [sub_eq_add_neg, minkQ_add, minkQ_neg, minkB_neg_right]; ring

theorem nullV_add (u u' z z' : Minkowski d) :
    nullV u u' (z + z') = nullV u u' z + nullV u u' z' := by
  simp only [nullV, minkB_add_left, add_div, add_smul]; abel

theorem nullV_sub (u u' z z' : Minkowski d) :
    nullV u u' (z - z') = nullV u u' z - nullV u u' z' := by
  simp only [nullV, minkB_sub_left, sub_div, sub_smul]; abel

theorem nullV_zero (u u' : Minkowski d) : nullV u u' 0 = 0 := by simp [nullV]

/-- The transverse part of a null frame commutes with a Lorentz map that scales the frame by
`l`, `l⁻¹`. -/
theorem nullV_map {A : Minkowski d ≃ₗ[ℝ] Minkowski d} (hA : A ∈ lorentz d) {u u' : Minkowski d}
    {l : ℝ} (hl : l ≠ 0) (hAu : A u = l • u) (hAu' : A u' = l⁻¹ • u') (z : Minkowski d) :
    nullV u u' (A z) = A (nullV u u' z) := by
  have h1 : minkB (A z) u' = l * minkB z u' := by
    have := lorentz.minkB_apply hA z (l • u')
    rwa [map_smul, hAu', smul_smul, mul_inv_cancel₀ hl, one_smul, minkB_smul_right] at this
  have h2 : minkB (A z) u = l⁻¹ * minkB z u := by
    have := lorentz.minkB_apply hA z (l⁻¹ • u)
    rwa [map_smul, hAu, smul_smul, inv_mul_cancel₀ hl, one_smul, minkB_smul_right] at this
  have h3 : minkB (A u) (A u') = minkB u u' := lorentz.minkB_apply hA u u'
  simp only [nullV, map_sub, map_smul, hAu, hAu', h1, h2, smul_smul]
  congr 2 <;> ring_nf

theorem nullV_map_pow {A : Minkowski d ≃ₗ[ℝ] Minkowski d} (hA : A ∈ lorentz d) {u u' : Minkowski d}
    {l : ℝ} (hl : l ≠ 0) (hAu : A u = l • u) (hAu' : A u' = l⁻¹ • u') (n : ℕ) (z : Minkowski d) :
    nullV u u' ((A ^ n) z) = (A ^ n) (nullV u u' z) := by
  induction n generalizing z with
  | zero => simp
  | succ n ih => rw [pow_succ, LinearEquiv.mul_apply, LinearEquiv.mul_apply, ih, nullV_map hA hl hAu hAu']

/-- `⟨z | v⟩ = ⟨v(z) | v(q)⟩` for the transverse part `v(q)` of a null frame. -/
theorem minkB_nullV_eq {u u' : Minkowski d} (hu : minkQ u = 0) (hu' : minkQ u' = 0)
    (hB : minkB u u' ≠ 0) (z q : Minkowski d) :
    minkB z (nullV u u' q) = minkB (nullV u u' z) (nullV u u' q) := by
  conv_lhs => rw [eq_nullV_add (u := u) (u' := u') z]
  rw [minkB_add_left, minkB_add_left, minkB_smul_left, minkB_smul_left,
    minkB_comm u (nullV u u' q), minkB_comm u' (nullV u u' q), minkB_nullV_left hu hB,
    minkB_nullV_right hu' hB]
  ring

/-- On the orthogonal of a null frame, `|⟨v | w⟩| ≤ (|v|² + |w|²)/2`. -/
theorem abs_minkB_le_of_orth_frame {u u' : Minkowski d} (hu : minkQ u = 0) (hu' : minkQ u' = 0)
    (hB : minkB u u' ≠ 0) {v w : Minkowski d} (h1 : minkB v u = 0) (h2 : minkB v u' = 0)
    (h3 : minkB w u = 0) (h4 : minkB w u' = 0) : |minkB v w| ≤ (minkQ v + minkQ w) / 2 := by
  have hs := (minkQ_nonneg_of_orth_frame hu hu' hB (y := v - w)
    (by rw [minkB_sub_left, h1, h3, sub_zero]) (by rw [minkB_sub_left, h2, h4, sub_zero])).1
  have ha := (minkQ_nonneg_of_orth_frame hu hu' hB (y := v + w)
    (by rw [minkB_add_left, h1, h3, add_zero]) (by rw [minkB_add_left, h2, h4, add_zero])).1
  rw [minkQ_sub_eq] at hs
  rw [minkQ_add] at ha
  rw [abs_le]; constructor <;> linarith

/-- **The transverse part of the orbit grows at most linearly**: for an isometry whose linear part
scales the null frame `(u, u')` by `l`, `l⁻¹`, `|v(gⁿp − p)|² ≤ n² |v(gp − p)|²`. -/
theorem minkQ_nullV_pow_smul_sub_le {g : isom d} {u u' : Minkowski d} (hu : minkQ u = 0)
    (hu' : minkQ u' = 0) (hB : minkB u u' ≠ 0) {l : ℝ} (hl : l ≠ 0)
    (hAu : linOf g u = l • u) (hAu' : linOf g u' = l⁻¹ • u') (p : Minkowski d) (n : ℕ) :
    minkQ (nullV u u' ((g ^ n) • p - p)) ≤ (n : ℝ) ^ 2 * minkQ (nullV u u' (g • p - p)) := by
  set q := minkQ (nullV u u' (g • p - p))
  have hstep : ∀ n : ℕ, nullV u u' ((g ^ (n + 1)) • p - p) =
      nullV u u' ((g ^ n) • p - p) + nullV u u' ((linOf g ^ n) (g • p - p)) := by
    intro n
    rw [← nullV_add, pow_succ, mul_smul, ← linOf_pow, ← smul_sub_smul]
    congr 1; abel
  have he : ∀ n : ℕ, minkQ (nullV u u' ((linOf g ^ n) (g • p - p))) = q := fun n => by
    rw [nullV_map_pow (linOf_mem g) hl hAu hAu', minkQ_pow_apply (lorentz.minkQ_apply (linOf_mem g))]
  have key : ∀ n : ℕ, minkQ (nullV u u' ((g ^ n) • p - p)) ≤ (n : ℝ) ^ 2 * q ∧
      ∀ w : Minkowski d, minkB w u = 0 → minkB w u' = 0 → minkQ w = q →
        minkB (nullV u u' ((g ^ n) • p - p)) w ≤ n * q := by
    intro n
    induction n with
    | zero => refine ⟨by simp [nullV_zero], fun w _ _ _ => by simp [nullV_zero]⟩
    | succ n ih =>
      obtain ⟨ih1, ih2⟩ := ih
      set D := nullV u u' ((g ^ n) • p - p)
      set e := nullV u u' ((linOf g ^ n) (g • p - p))
      have hD1 : minkB D u = 0 := minkB_nullV_left hu hB _
      have hD2 : minkB D u' = 0 := minkB_nullV_right hu' hB _
      have he1 : minkB e u = 0 := minkB_nullV_left hu hB _
      have he2 : minkB e u' = 0 := minkB_nullV_right hu' hB _
      rw [hstep n]
      refine ⟨?_, fun w hw1 hw2 hwq => ?_⟩
      · rw [minkQ_add, he n]
        have := ih2 e he1 he2 (he n)
        push_cast; nlinarith
      · rw [minkB_add_left]
        have h1 := ih2 w hw1 hw2 hwq
        have h2 := (abs_le.1 (abs_minkB_le_of_orth_frame hu hu' hB he1 he2 hw1 hw2)).2
        rw [he n, hwq] at h2
        push_cast; linarith
  exact (key n).1

/-- An exponential beats a quadratic. -/
theorem exists_nat_add_mul_sq_lt {A B C r : ℝ} (hC : 0 < C) (hr : 1 < r) :
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


/-- **The two repulsive points of `γ` and `γ⁻¹`, packaged**: one eigenvalue `0 < l < 1` for both
(`L(γ)(1,u) = l(1,u)`, `L(γ)(1,u') = l⁻¹(1,u')`, since `L(γ)` preserves `⟨(1,u) | (1,u')⟩ ≠ 0`),
the two functional equations along the iterates, and `⟨(1,u) | (1,u')⟩ < 0`. -/
theorem IsRepulsiveFixedJ.pair {γ : isom d} {w w' : PenroseSphere d × ℝ}
    (hw : IsRepulsiveFixedJ γ w) (hw' : IsRepulsiveFixedJ γ⁻¹ w') :
    ∃ l : ℝ, 0 < l ∧ l < 1 ∧ linOf γ (nullVec w.1) = l • nullVec w.1 ∧
      linOf γ (nullVec w'.1) = l⁻¹ • nullVec w'.1 ∧
      (∀ (n : ℕ) (p : Minkowski d), minkB (nullVec w.1) ((γ ^ n) • p) - w.2 =
        (l⁻¹) ^ n * (minkB (nullVec w.1) p - w.2)) ∧
      (∀ (n : ℕ) (p : Minkowski d), minkB (nullVec w'.1) ((γ ^ n) • p) - w'.2 =
        l ^ n * (minkB (nullVec w'.1) p - w'.2)) ∧
      minkB (nullVec w.1) (nullVec w'.1) < 0 := by
  have hfst := hw.fst_ne hw'
  obtain ⟨-, l, hl0, hl1, hAn, hf⟩ := hw
  obtain ⟨-, l', hl0', hl1', -, hf'⟩ := hw'
  have hg' := funEq_of_inv hl0'.ne' hf'
  have hAn' : linOf γ (nullVec w'.1) = l'⁻¹ • nullVec w'.1 :=
    eigen_of_funEq (inv_ne_zero hl0'.ne') (by simpa using hg')
  have hκ : minkB (nullVec w.1) (nullVec w'.1) < 0 := by
    rw [minkB_nullVec_nullVec]
    have : 0 < ‖((w.1 : PenroseSphere d) : EuclideanSpace ℝ (Fin d)) - w'.1‖ := by
      rw [norm_pos_iff, sub_ne_zero]; exact fun h => hfst (Subtype.ext h)
    have := pow_pos this 2
    linarith
  have hll : l' = l := by
    have h := lorentz.minkB_apply (linOf_mem γ) (nullVec w.1) (nullVec w'.1)
    rw [hAn, hAn', minkB_smul_left, minkB_smul_right] at h
    have h2 : (l * l'⁻¹ - 1) * minkB (nullVec w.1) (nullVec w'.1) = 0 := by linear_combination h
    have h3 := sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right hκ.ne)
    field_simp at h3; linarith
  subst hll
  refine ⟨l', hl0', hl1', hAn, hAn', fun n p => IsRepulsiveFixedJ.iterate hf n p, fun n p => ?_, hκ⟩
  have := IsRepulsiveFixedJ.iterate (l := l'⁻¹) (by simpa using hg') n p
  rwa [inv_inv] at this

/-- **A causal displacement along `γⁿ`** (the engine of `blem_sanlox`): if `y` lies strictly on the
expanding side of the repulsive hyperplane of `γ` (`⟨(1,u) | y⟩ > s`) and `x` strictly on the past
side of that of `γ⁻¹`, then `γⁿ y − x` is timelike for `n` large: in the null frame of `γ`,
`|γⁿy − x|² = 2 f(γⁿ y − x) g(γⁿ y − x)/⟨(1,u)|(1,u')⟩ + |v|²` with `f ~ λ⁻ⁿ f(y)`, `g → −g(x)`, and
the transverse part `v` growing at most linearly (`minkQ_nullV_pow_smul_sub_le`). -/
theorem exists_minkQ_neg_of_sign {γ : isom d} {w w' : PenroseSphere d × ℝ}
    (hw : IsRepulsiveFixedJ γ w) (hw' : IsRepulsiveFixedJ γ⁻¹ w') {x y : Minkowski d}
    (hy : 0 < minkB (nullVec w.1) y - w.2) (hx : minkB (nullVec w'.1) x - w'.2 < 0) :
    ∃ n : ℕ, minkQ ((γ ^ n) • y - x) < 0 := by
  obtain ⟨l, hl0, hl1, hAn, hAn', hf, hg, hκ⟩ := hw.pair hw'
  have hr : minkQ (nullVec w.1) = 0 := minkQ_nullVec w.1
  have ha : minkQ (nullVec w'.1) = 0 := minkQ_nullVec w'.1
  obtain ⟨r, rfl⟩ : ∃ r, r = nullVec w.1 := ⟨_, rfl⟩
  obtain ⟨a, rfl⟩ : ∃ a, a = nullVec w'.1 := ⟨_, rfl⟩
  obtain ⟨κ, hκd⟩ : ∃ κ, κ = minkB (nullVec w.1) (nullVec w'.1) := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F, F = minkB (nullVec w.1) y - w.2 := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = minkB (nullVec w'.1) y - w'.2 := ⟨_, rfl⟩
  obtain ⟨f₀, hf₀⟩ : ∃ f₀, f₀ = minkB (nullVec w.1) x - w.2 := ⟨_, rfl⟩
  obtain ⟨g₀, hg₀⟩ : ∃ g₀, g₀ = minkB (nullVec w'.1) x - w'.2 := ⟨_, rfl⟩
  obtain ⟨Q₁, hQ₁⟩ : ∃ Q₁, Q₁ = minkQ (nullV (nullVec w.1) (nullVec w'.1) (y - x)) := ⟨_, rfl⟩
  obtain ⟨q, hqd⟩ : ∃ q, q = minkQ (nullV (nullVec w.1) (nullVec w'.1) (γ • x - x)) := ⟨_, rfl⟩
  rw [← hF] at hy
  rw [← hg₀] at hx
  rw [← hκd] at hκ
  have hκ0 : minkB (nullVec w.1) (nullVec w'.1) ≠ 0 := hκd ▸ hκ.ne
  have hq0 : 0 ≤ q := hqd ▸ (minkQ_nonneg_of_orth_frame hr ha hκ0 (minkB_nullV_left hr hκ0 _)
    (minkB_nullV_right ha hκ0 _)).1
  have hc : 0 < 2 * F * g₀ / κ := by
    have : F * g₀ < 0 := mul_neg_of_pos_of_neg hy hx
    rw [mul_assoc]
    exact div_pos_of_neg_of_neg (by linarith) hκ
  have hl1' : 1 < l⁻¹ := one_lt_inv_iff₀.2 ⟨hl0, hl1⟩
  obtain ⟨n, hn⟩ := exists_nat_add_mul_sq_lt (A := 2 * (F * G + f₀ * g₀) / κ + |2 * G * f₀ / κ| +
    2 * Q₁) (B := 2 * q) hc hl1'
  refine ⟨n, ?_⟩
  obtain ⟨t, ht⟩ : ∃ t, t = (l⁻¹) ^ n := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = l ^ n := ⟨_, rfl⟩
  rw [← ht] at hn
  have hts : t * s = 1 := by rw [ht, hs, ← mul_pow, inv_mul_cancel₀ hl0.ne', one_pow]
  have hs0 : 0 < s := hs ▸ pow_pos hl0 n
  have hzr : minkB ((γ ^ n) • y - x) (nullVec w.1) = t * F - f₀ := by
    rw [minkB_comm, minkB_sub_right]; have := hf n y; rw [← ht] at this; subst hF hf₀; linarith
  have hza : minkB ((γ ^ n) • y - x) (nullVec w'.1) = s * G - g₀ := by
    rw [minkB_comm, minkB_sub_right]; have := hg n y; rw [← hs] at this; subst hG hg₀; linarith
  -- the transverse part
  have hv : nullV (nullVec w.1) (nullVec w'.1) ((γ ^ n) • y - x) =
      (linOf γ ^ n) (nullV (nullVec w.1) (nullVec w'.1) (y - x)) +
        nullV (nullVec w.1) (nullVec w'.1) ((γ ^ n) • x - x) := by
    rw [← nullV_map_pow (linOf_mem γ) hl0.ne' hAn hAn', ← nullV_add, ← linOf_pow,
      ← smul_sub_smul]
    congr 1; abel
  have hv1 := minkQ_nullV_pow_smul_sub_le hr ha hκ0 hl0.ne' hAn hAn' x n
  rw [← hqd] at hv1
  have hW : minkQ (nullV (nullVec w.1) (nullVec w'.1) ((γ ^ n) • y - x)) ≤
      2 * Q₁ + 2 * ((n : ℝ) ^ 2 * q) := by
    rw [hv]
    have he : minkQ ((linOf γ ^ n) (nullV (nullVec w.1) (nullVec w'.1) (y - x))) = Q₁ := by
      rw [hQ₁]; exact minkQ_pow_apply (lorentz.minkQ_apply (linOf_mem γ)) n _
    have he1 : minkB ((linOf γ ^ n) (nullV (nullVec w.1) (nullVec w'.1) (y - x))) (nullVec w.1)
        = 0 := by
      rw [← nullV_map_pow (linOf_mem γ) hl0.ne' hAn hAn']; exact minkB_nullV_left hr hκ0 _
    have he2 : minkB ((linOf γ ^ n) (nullV (nullVec w.1) (nullVec w'.1) (y - x))) (nullVec w'.1)
        = 0 := by
      rw [← nullV_map_pow (linOf_mem γ) hl0.ne' hAn hAn']; exact minkB_nullV_right ha hκ0 _
    have hb := (abs_le.1 (abs_minkB_le_of_orth_frame hr ha hκ0 he1 he2
      (minkB_nullV_left hr hκ0 ((γ ^ n) • x - x)) (minkB_nullV_right ha hκ0 _))).2
    rw [minkQ_add]
    linarith
  rw [minkQ_eq_nullXY_add hr ha hκ0 ((γ ^ n) • y - x), nullXY, hzr, hza, ← hκd]
  have h1 : 2 * (t * F - f₀) * (s * G - g₀) =
      2 * (F * G + f₀ * g₀) - s * (2 * G * f₀) - (2 * F * g₀) * t := by
    linear_combination (2 * F * G) * hts
  have hprod : 2 * (t * F - f₀) * (s * G - g₀) / κ =
      2 * (F * G + f₀ * g₀) / κ - s * (2 * G * f₀ / κ) - (2 * F * g₀ / κ) * t := by
    rw [h1]; ring
  have hsb : -|2 * G * f₀ / κ| ≤ s * (2 * G * f₀ / κ) := by
    have hs1 : s ≤ 1 := hs ▸ pow_le_one₀ hl0.le hl1.le
    have := neg_abs_le (2 * G * f₀ / κ)
    have h2 := mul_le_mul_of_nonneg_left this hs0.le
    nlinarith [abs_nonneg (2 * G * f₀ / κ)]
  rw [hprod]
  nlinarith

/-- **The orbit of `γ` crosses every null hyperplane of another direction** (the second engine
of `blem_sanlox`): if `x` lies strictly on the expanding side of the repulsive hyperplane of `γ`
(`⟨(1,v) | x⟩ > s`), then along `γᵐ x` every null function `⟨(1,u) | ·⟩` with `u` not the
attractive direction `v'` of `γ` tends to `+∞`: `γᵐ x − x ≈ λ⁻ᵐ f(x) (1,v')/⟨(1,v)|(1,v')⟩`, and
`⟨(1,u) | (1,v')⟩ < 0`. -/
theorem exists_lt_minkB_pow_smul {γ : isom d} {v v' : PenroseSphere d × ℝ}
    (hv : IsRepulsiveFixedJ γ v) (hv' : IsRepulsiveFixedJ γ⁻¹ v') {x : Minkowski d}
    (hx : 0 < minkB (nullVec v.1) x - v.2) {u : PenroseSphere d} (hu : u ≠ v'.1) (M : ℝ) :
    ∃ m : ℕ, M < minkB (nullVec u) ((γ ^ m) • x) := by
  obtain ⟨l, hl0, hl1, hAn, hAn', hf, hg, hκ⟩ := hv.pair hv'
  have hr : minkQ (nullVec v.1) = 0 := minkQ_nullVec v.1
  have ha : minkQ (nullVec v'.1) = 0 := minkQ_nullVec v'.1
  have hκ0 := hκ.ne
  have hua : minkB (nullVec u) (nullVec v'.1) < 0 := by
    rw [minkB_nullVec_nullVec]
    have : 0 < ‖((u : PenroseSphere d) : EuclideanSpace ℝ (Fin d)) - v'.1‖ := by
      rw [norm_pos_iff, sub_ne_zero]; exact fun h => hu (Subtype.ext h)
    have := pow_pos this 2
    linarith
  obtain ⟨κ, hκd⟩ : ∃ κ, κ = minkB (nullVec v.1) (nullVec v'.1) := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F, F = minkB (nullVec v.1) x - v.2 := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = minkB (nullVec v'.1) x - v'.2 := ⟨_, rfl⟩
  obtain ⟨Q₀, hQ₀⟩ : ∃ Q₀, Q₀ = minkQ (nullV (nullVec v.1) (nullVec v'.1) (nullVec u)) :=
    ⟨_, rfl⟩
  obtain ⟨q, hqd⟩ : ∃ q, q = minkQ (nullV (nullVec v.1) (nullVec v'.1) (γ • x - x)) := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, C = F * minkB (nullVec u) (nullVec v'.1) / κ := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X, X = G * minkB (nullVec u) (nullVec v.1) / κ := ⟨_, rfl⟩
  rw [← hF] at hx
  rw [← hκd] at hκ
  have hC0 : 0 < C := by
    rw [hC, mul_div_assoc]; exact mul_pos hx (div_pos_of_neg_of_neg hua hκ)
  have hl1' : 1 < l⁻¹ := one_lt_inv_iff₀.2 ⟨hl0, hl1⟩
  obtain ⟨m, hm⟩ := exists_nat_add_mul_sq_lt
    (A := M - minkB (nullVec u) x + |X| + C + Q₀ / 2) (B := q / 2) hC0 hl1'
  refine ⟨m, ?_⟩
  obtain ⟨t, ht⟩ : ∃ t, t = (l⁻¹) ^ m := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = l ^ m := ⟨_, rfl⟩
  rw [← ht] at hm
  have hs0 : 0 < s := hs ▸ pow_pos hl0 m
  have hs1 : s ≤ 1 := hs ▸ pow_le_one₀ hl0.le hl1.le
  have hzr : minkB ((γ ^ m) • x - x) (nullVec v.1) = (t - 1) * F := by
    rw [minkB_comm, minkB_sub_right]; have := hf m x; rw [← ht] at this; subst hF; linarith
  have hza : minkB ((γ ^ m) • x - x) (nullVec v'.1) = (s - 1) * G := by
    rw [minkB_comm, minkB_sub_right]; have := hg m x; rw [← hs] at this; subst hG; linarith
  -- `⟨(1,u) | q⟩` in the frame of `γ`
  have hdec := congrArg (minkB (nullVec u))
    (eq_nullV_add (u := nullVec v.1) (u' := nullVec v'.1) ((γ ^ m) • x - x))
  rw [minkB_add_right, minkB_add_right, minkB_smul_right, minkB_smul_right, hzr, hza, ← hκd,
    minkB_nullV_eq hr ha hκ0] at hdec
  have hv1 := minkQ_nullV_pow_smul_sub_le hr ha hκ0 hl0.ne' hAn hAn' x m
  rw [← hqd] at hv1
  have hb := (abs_le.1 (abs_minkB_le_of_orth_frame hr ha hκ0
    (minkB_nullV_left hr hκ0 (nullVec u)) (minkB_nullV_right ha hκ0 _)
    (minkB_nullV_left hr hκ0 ((γ ^ m) • x - x)) (minkB_nullV_right ha hκ0 _))).1
  rw [← hQ₀] at hb
  have e1 : (s - 1) * G / κ * minkB (nullVec u) (nullVec v.1) = (s - 1) * X := by
    rw [hX]; ring
  have e2 : (t - 1) * F / κ * minkB (nullVec u) (nullVec v'.1) = C * t - C := by
    rw [hC]; ring
  rw [e1, e2] at hdec
  have hX1 : -|X| ≤ (s - 1) * X := by
    rcases le_total 0 X with h0 | h0
    · rw [abs_of_nonneg h0]; nlinarith
    · rw [abs_of_nonpos h0]; nlinarith
  have hsub : minkB (nullVec u) ((γ ^ m) • x) =
      minkB (nullVec u) x + minkB (nullVec u) ((γ ^ m) • x - x) := by
    rw [minkB_sub_right]; ring
  rw [hsub, hdec]
  linarith

/-- **A timelike displacement forces a loxodromic element** (Rem 8.9 and the class analysis of
§8): under the standing hypotheses, an element `g ∈ Γ` with `g x − x` timelike is loxodromic — it
is not nonspacelike elliptic nor transverse parabolic (`nini`), a spacelike elliptic or tangent
parabolic one has `Ω_g = 𝐌ⁿ`, and a linear parabolic one has `g x − x = p(x − c) ∈ J^⊥`,
never timelike — so `x ∉ U_lox(Γ)`. -/
theorem not_minkQ_neg_of_mem_UGammaLox (h : CCAction Γ S) {x : Minkowski d}
    (hx : x ∈ UGammaLox Γ) {g : isom d} (hg : g ∈ Γ) : ¬minkQ (g • x - x) < 0 := by
  intro hneg
  have h1 : g ≠ 1 := by rintro rfl; simp at hneg
  obtain ⟨hN, hT, -⟩ := nini h hg h1
  by_cases hL : IsLinearParabolic g
  · obtain ⟨⟨R, U, hR, hU, hRe, hn, hU1, hgRU, hc⟩, c, hcf⟩ := hL
    have he : g • x - x = pOf (R * U) (x - c) := by
      have := smul_sub_smul g x c
      rw [hcf, hgRU] at this
      rw [pOf_apply, ← this]; abel
    have hmem := parabolic_range_le_minkOrth_nullPart hR hU hRe hn hU1 hc ⟨x - c, rfl⟩
    have := (minkQ_nonneg_of_mem_minkOrth_nullPart hU.1 hn (pOf_ne_zero hU1) hmem).1
    rw [← he] at this
    linarith
  · have hA : x ∈ achronalDomain g := by
      rcases classes_of_not lorentzTrichotomy hN hL with hX | hX | hX | hX
      · have := hx g hg hX; rwa [Ug_eq_achronalDomain_of_isLoxodromic hX] at this
      · rw [achronalDomain_eq_univ_of_isSpacelikeElliptic hX]; trivial
      · rw [achronalDomain_eq_univ_of_isTangentParabolic hX]; trivial
      · exact (hT hX).elim
    have := mem_achronalDomain_iff.1 hA 1 one_pos
    rw [pow_one] at this
    linarith

/-- **No point of `U_lox(Γ)` is in a future quadrant of one loxodromic element and a past quadrant
of another** (the missing step of `blem:sanlox`, replacing the convexity of l.3157): if
`x ∈ U⁺(γ) ∩ U⁻(γ')`, then, choosing the repulsive point `w` of `γ^{±1}` off the attractive
direction of `γ'`, some `γ'ᵐ x` lies beyond the hyperplane of `w` (`exists_lt_minkB_pow_smul`),
then `γ^{±n} γ'ᵐ x − x` is timelike for `n` large (`exists_minkQ_neg_of_sign`), and an element of
`Γ` with a timelike displacement at `x` is loxodromic with `x ∉ Ω_g`
(`not_minkQ_neg_of_mem_UGammaLox`). -/
theorem not_mem_quadrantPlus_quadrantMinus (h : CCAction Γ S) {x : Minkowski d}
    (hx : x ∈ UGammaLox Γ) {γ γ' : isom d} (hγ : γ ∈ Γ) (hγ' : γ' ∈ Γ)
    {w w' v v' : PenroseSphere d × ℝ} (hw : IsRepulsiveFixedJ γ w)
    (hw' : IsRepulsiveFixedJ γ⁻¹ w') (hv : IsRepulsiveFixedJ γ' v)
    (hv' : IsRepulsiveFixedJ γ'⁻¹ v') (hp : x ∈ halfPlus w.1 w.2 ∩ halfPlus w'.1 w'.2)
    (hm : x ∈ halfMinus v.1 v.2 ∩ halfMinus v'.1 v'.2) : False := by
  suffices key : ∀ g : isom d, g ∈ Γ → ∀ {a b : PenroseSphere d × ℝ}, IsRepulsiveFixedJ g a →
      IsRepulsiveFixedJ g⁻¹ b → x ∈ halfPlus b.1 b.2 → a.1 ≠ v'.1 → False by
    by_cases hne : w.1 = v'.1
    · have : w'.1 ≠ v'.1 := fun h' => hw.fst_ne hw' (hne.trans h'.symm)
      exact key γ⁻¹ (Γ.inv_mem hγ) hw' (by rwa [inv_inv]) hp.1 this
    · exact key γ hγ hw hw' hp.2 hne
  intro g hg a b ha hb hxb hne
  have hxv := mem_halfMinus.1 hm.1
  obtain ⟨m, hm'⟩ := exists_lt_minkB_pow_smul hv hv' (x := x) (by linarith) hne a.2
  have hxb' := mem_halfPlus.1 hxb
  obtain ⟨n, hn⟩ := exists_minkQ_neg_of_sign ha hb (x := x) (y := (γ' ^ m) • x) (by linarith)
    (by linarith)
  refine not_minkQ_neg_of_mem_UGammaLox h hx (Γ.mul_mem (Γ.pow_mem hg n) (Γ.pow_mem hγ' m)) ?_
  rwa [mul_smul]

/-- **`blem:sanlox` as printed** (l.3143–3144): `Ω_lox(Γ) = Ω(Γ)` when `Γ` contains a loxodromic
element (under the standing hypotheses of §8, read as `CCAction`). Not the paper's proof, which
needs `Ω_lox(Γ)` convex: a point `x ∈ Ω_lox(Γ)` lies in a quadrant of every loxodromic element
(`interior_achronalDomain_eq_quadrants`), with the same sign for all of them
(`not_mem_quadrantPlus_quadrantMinus`); on the open set of points sharing the sign of `x` for one
`γ₀`, every repulsive hyperplane of `Λ₀(Γ)` is one-sided, so `x ∈ Int Ω^±(Λ₀) = Ω^±(Λ(Γ))`
(`omegaPlus_closure_eq_interior`), which lies in `Ω(Γ)` (`omegaPlus_limitSetJ_subset_omegaGamma`). -/
theorem blem_sanlox (h : CCAction Γ S) (hlox : ∃ γ ∈ Γ, IsLoxodromic (linOf γ)) :
    omegaLox Γ = omegaGamma Γ := by
  refine Subset.antisymm ?_ (omegaGamma_subset_omegaLox Γ)
  intro x hx
  obtain ⟨γ₀, hγ₀, hlox₀⟩ := hlox
  obtain ⟨w₀, -, w₀', -, hr₀, hr₀', -⟩ := exists_two_loxRepSet hγ₀ hlox₀
  have hUL : omegaLox Γ ⊆ UGammaLox Γ := interior_subset
  have hquad : ∀ γ ∈ Γ, ∀ {w w' : PenroseSphere d × ℝ}, IsRepulsiveFixedJ γ w →
      IsRepulsiveFixedJ γ⁻¹ w' → ∀ p ∈ omegaLox Γ,
        p ∈ (halfPlus w.1 w.2 ∩ halfPlus w'.1 w'.2) ∪ (halfMinus w.1 w.2 ∩ halfMinus w'.1 w'.2) := by
    intro γ hγ w w' hw hw' p hp
    rw [← interior_achronalDomain_eq_quadrants hw hw']
    refine interior_mono (fun q hq => ?_) hp
    have := hq γ hγ hw.1
    rwa [Ug_eq_achronalDomain_of_isLoxodromic hw.1] at this
  rcases hquad γ₀ hγ₀ hr₀ hr₀' x hx with hxp | hxm
  · have hV : omegaLox Γ ∩ (halfPlus w₀.1 w₀.2 ∩ halfPlus w₀'.1 w₀'.2) ⊆
        omegaPlus (loxRepSet Γ) := by
      rintro p ⟨hp, hp0⟩
      refine mem_omegaPlus.2 fun w ⟨γ, hγ, hw⟩ => ?_
      obtain ⟨w', hw'⟩ := exists_isRepulsiveFixedJ (isLoxodromic_linOf_inv hw.1)
      rcases hquad γ hγ hw hw' p hp with hq | hq
      · exact mem_halfPlus.1 hq.1
      · exact (not_mem_quadrantPlus_quadrantMinus h (hUL hp) hγ₀ hγ hr₀ hr₀' hw hw' hp0 hq).elim
    have hVo : IsOpen (omegaLox Γ ∩ (halfPlus w₀.1 w₀.2 ∩ halfPlus w₀'.1 w₀'.2)) :=
      isOpen_interior.inter ((isOpen_halfPlus _ _).inter (isOpen_halfPlus _ _))
    have : x ∈ omegaPlus (limitSetJ Γ) := by
      rw [limitSetJ, omegaPlus_closure_eq_interior]
      exact interior_maximal hV hVo ⟨hx, hxp⟩
    exact omegaPlus_limitSetJ_subset_omegaGamma h hγ₀ hlox₀ this
  · have hV : omegaLox Γ ∩ (halfMinus w₀.1 w₀.2 ∩ halfMinus w₀'.1 w₀'.2) ⊆
        omegaMinus (loxRepSet Γ) := by
      rintro p ⟨hp, hp0⟩
      refine mem_omegaMinus.2 fun w ⟨γ, hγ, hw⟩ => ?_
      obtain ⟨w', hw'⟩ := exists_isRepulsiveFixedJ (isLoxodromic_linOf_inv hw.1)
      rcases hquad γ hγ hw hw' p hp with hq | hq
      · exact (not_mem_quadrantPlus_quadrantMinus h (hUL hp) hγ hγ₀ hw hw' hr₀ hr₀' hq hp0).elim
      · exact mem_halfMinus.1 hq.1
    have hVo : IsOpen (omegaLox Γ ∩ (halfMinus w₀.1 w₀.2 ∩ halfMinus w₀'.1 w₀'.2)) :=
      isOpen_interior.inter ((isOpen_halfMinus _ _).inter (isOpen_halfMinus _ _))
    have : x ∈ omegaMinus (limitSetJ Γ) := by
      rw [limitSetJ, omegaMinus_closure_eq_interior]
      exact interior_maximal hV hVo ⟨hx, hxm⟩
    exact omegaMinus_limitSetJ_subset_omegaGamma h hγ₀ hlox₀ this

end Sanlox


/-! ## 5. `blem:loxregular` (Lemma 10.2): `Ω(S̃)` is a regular convex domain -/

section Loxregular

variable {Γ : Subgroup (isom d)} {S : Set (Minkowski d)}

theorem isPreconnected_omegaS (h : CCAction Γ S) : IsPreconnected (omegaS Γ S) := by
  obtain ⟨x, hx⟩ := h.nonempty
  rw [omegaS_eq h hx]; exact isPreconnected_connectedComponentIn

theorem omegaS_subset_interior_achronalDomain {γ : isom d} (hγ : γ ∈ Γ)
    (hlox : IsLoxodromic (linOf γ)) : omegaS Γ S ⊆ interior (achronalDomain γ) := by
  have hsub : UGamma Γ ⊆ achronalDomain γ := fun x hx => by
    have := hx γ hγ (ne_one_of_isLoxodromic hlox)
    rwa [Ug_eq_achronalDomain_of_isLoxodromic hlox] at this
  exact (omegaS_subset_omegaGamma Γ S).trans (interior_mono hsub)

/-- **`Ω(S̃)` lies in one of the two components `U^±(γ)`** (l.3176–3180): it is connected and lies
in the interior of the achronal domain of every loxodromic `γ ∈ Γ`. -/
theorem omegaS_subset_quadrant (h : CCAction Γ S) {γ : isom d} (hγ : γ ∈ Γ)
    {w w' : PenroseSphere d × ℝ} (hw : IsRepulsiveFixedJ γ w) (hw' : IsRepulsiveFixedJ γ⁻¹ w') :
    omegaS Γ S ⊆ halfPlus w.1 w.2 ∩ halfPlus w'.1 w'.2 ∨
      omegaS Γ S ⊆ halfMinus w.1 w.2 ∩ halfMinus w'.1 w'.2 := by
  have hsub := omegaS_subset_interior_achronalDomain (S := S) hγ hw.1
  rw [interior_achronalDomain_eq_quadrants hw hw'] at hsub
  exact (isPreconnected_omegaS h).subset_or_subset
    ((isOpen_halfPlus _ _).inter (isOpen_halfPlus _ _))
    ((isOpen_halfMinus _ _).inter (isOpen_halfMinus _ _))
    (Set.disjoint_left.2 fun p hp hq => lt_asymm (mem_halfPlus.1 hp.1) (mem_halfMinus.1 hq.1))
    hsub

theorem minkB_nullVec_vertical (u : PenroseSphere d) :
    minkB (nullVec u) ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin d))) = -1 := by
  simp [minkB_nullVec]

/-- **Barbot's "the reader can easily check" (l.3191–3193), filled**: for two null directions
`a.1 ≠ c.1`, some vertical (timelike) line avoids `P⁻(a) ∩ P⁺(c)`, hence `U⁺(γ₀) ∩ U⁻(γ₁)`: its
point `p` with `⟨(1,a) | p⟩ = s_a`, `⟨(1,c) | p⟩ = s_c` is below `P⁺(c)` and above `P⁻(a)`, and the
line is monotone for both. -/
theorem exists_line_avoiding {a c : PenroseSphere d × ℝ} (hac : a.1 ≠ c.1) :
    ∃ p : Minkowski d, ∀ s : ℝ, p + s • ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin d))) ∉
      halfMinus a.1 a.2 ∩ halfPlus c.1 c.2 := by
  set κ := minkB (nullVec a.1) (nullVec c.1)
  have hκ : κ < 0 := by
    simp only [κ]; rw [minkB_nullVec_nullVec]
    have : 0 < ‖((a.1 : PenroseSphere d) : EuclideanSpace ℝ (Fin d)) - c.1‖ := by
      rw [norm_pos_iff, sub_ne_zero]; exact fun h => hac (Subtype.ext h)
    have := pow_pos this 2
    linarith
  have haa : minkB (nullVec a.1) (nullVec a.1) = 0 := by rw [← minkQ_eq_minkB, minkQ_nullVec]
  have hcc : minkB (nullVec c.1) (nullVec c.1) = 0 := by rw [← minkQ_eq_minkB, minkQ_nullVec]
  set p : Minkowski d := (c.2 / κ) • nullVec a.1 + (a.2 / κ) • nullVec c.1
  have e1 : minkB (nullVec a.1) p = a.2 := by
    simp only [p, minkB_add_right, minkB_smul_right, haa, mul_zero, zero_add]
    exact div_mul_cancel₀ _ hκ.ne
  have e2 : minkB (nullVec c.1) p = c.2 := by
    simp only [p, minkB_add_right, minkB_smul_right, hcc, mul_zero, add_zero]
    rw [minkB_comm]; exact div_mul_cancel₀ _ hκ.ne
  refine ⟨p, fun s ⟨h1, h2⟩ => ?_⟩
  rw [mem_halfMinus, minkB_add_right, minkB_smul_right, minkB_nullVec_vertical, e1] at h1
  rw [mem_halfPlus, minkB_add_right, minkB_smul_right, minkB_nullVec_vertical, e2] at h2
  linarith

/-- **The claim of l.3185–3194**: either `Ω(S̃) ⊆ U⁺(γ)` for every loxodromic `γ ∈ Γ` or
`Ω(S̃) ⊆ U⁻(γ)` for every one — read on the repulsive fixed points: `Ω(S̃)` lies on the future side
of every hyperplane of `Λ₀(Γ)`, or on the past side of every one. Barbot normalises to the
first by a time-reversing isometry (l.3181–3183); `isom d` is `SO₀`-affine, so both are kept. -/
theorem loxregular_sign (h : CCAction Γ S) :
    (∀ w ∈ loxRepSet Γ, omegaS Γ S ⊆ halfPlus w.1 w.2) ∨
      ∀ w ∈ loxRepSet Γ, omegaS Γ S ⊆ halfMinus w.1 w.2 := by
  by_cases hA : ∀ w ∈ loxRepSet Γ, omegaS Γ S ⊆ halfPlus w.1 w.2
  · exact Or.inl hA
  right
  intro w₁ hw₁
  by_contra hn₁
  obtain ⟨w₀, hw₀, hn₀⟩ : ∃ w ∈ loxRepSet Γ, ¬omegaS Γ S ⊆ halfPlus w.1 w.2 := by
    by_contra hc
    exact hA fun w hw => by_contra fun hn => hc ⟨w, hw, hn⟩
  obtain ⟨γ₀, hγ₀, hr₀⟩ := hw₀
  obtain ⟨γ₁, hγ₁, hr₁⟩ := hw₁
  obtain ⟨w₀', hr₀'⟩ := exists_isRepulsiveFixedJ (isLoxodromic_linOf_inv hr₀.1)
  obtain ⟨w₁', hr₁'⟩ := exists_isRepulsiveFixedJ (isLoxodromic_linOf_inv hr₁.1)
  have h0 : omegaS Γ S ⊆ halfMinus w₀.1 w₀.2 ∩ halfMinus w₀'.1 w₀'.2 :=
    (omegaS_subset_quadrant h hγ₀ hr₀ hr₀').resolve_left
      fun h' => hn₀ (h'.trans inter_subset_left)
  have h1 : omegaS Γ S ⊆ halfPlus w₁.1 w₁.2 ∩ halfPlus w₁'.1 w₁'.2 :=
    (omegaS_subset_quadrant h hγ₁ hr₁ hr₁').resolve_right
      fun h' => hn₁ (h'.trans inter_subset_left)
  have hne := hr₀.fst_ne hr₀'
  obtain ⟨b, hbS, hb⟩ : ∃ b : PenroseSphere d × ℝ, omegaS Γ S ⊆ halfMinus b.1 b.2 ∧
      b.1 ≠ w₁.1 := by
    by_cases hc : w₀.1 = w₁.1
    · exact ⟨w₀', h0.trans inter_subset_right, fun e => hne (hc.trans e.symm)⟩
    · exact ⟨w₀, h0.trans inter_subset_left, hc⟩
  obtain ⟨p, hp⟩ := exists_line_avoiding hb
  obtain ⟨s, hs⟩ := h.cc.entire.meets p _ isFutureTimelike_vertical
  exact hp s ⟨hbS (subset_omegaS h hs), (h1.trans inter_subset_left) (subset_omegaS h hs)⟩

/-- `blem:loxregular` (Lemma 10.2, l.3170–3211): `Ω(S̃)` is a regular convex domain — the
future regular domain `Ω⁺(Λ(Γ))` or (time-reversed) the past regular domain `Ω⁻(Λ(Γ))` of the
closure `Λ(Γ)` of the repulsive fixed points (l.3196–3210, with 4.6/4.8/4.9 through
`blem:fermonsbis`). Standing hypotheses of §8 (`CCAction`) and a loxodromic element. -/
theorem blem_loxregular (h : CCAction Γ S) (hlox : ∃ γ ∈ Γ, IsLoxodromic (linOf γ)) :
    (FutureRegular (limitSetJ Γ) ∧ omegaS Γ S = omegaPlus (limitSetJ Γ)) ∨
      (PastRegular (limitSetJ Γ) ∧ omegaS Γ S = omegaMinus (limitSetJ Γ)) := by
  obtain ⟨γ₀, hγ₀, hlox₀⟩ := hlox
  obtain ⟨x₀, hx₀⟩ := h.nonempty
  have hx₀Ω := subset_omegaS h hx₀
  rcases loxregular_sign h with hF | hP
  · have hsub : omegaS Γ S ⊆ omegaPlus (limitSetJ Γ) := by
      rw [limitSetJ, omegaPlus_closure_eq_interior]
      exact interior_maximal (fun p hp => mem_omegaPlus.2 fun w hw => mem_halfPlus.1 (hF w hw hp))
        (isOpen_omegaS Γ S)
    have heq : omegaS Γ S = omegaPlus (limitSetJ Γ) := by
      refine hsub.antisymm ?_
      rw [omegaS_eq h hx₀]
      exact (convex_omegaPlus _).isPreconnected.subset_connectedComponentIn (hsub hx₀Ω)
        (omegaPlus_limitSetJ_subset_omegaGamma h hγ₀ hlox₀)
    exact Or.inl ⟨⟨⟨x₀, hsub hx₀Ω⟩, isOpen_omegaPlus_of_isClosed (isClosed_limitSetJ Γ)⟩, heq⟩
  · have hsub : omegaS Γ S ⊆ omegaMinus (limitSetJ Γ) := by
      rw [limitSetJ, omegaMinus_closure_eq_interior]
      exact interior_maximal
        (fun p hp => mem_omegaMinus.2 fun w hw => mem_halfMinus.1 (hP w hw hp))
        (isOpen_omegaS Γ S)
    have heq : omegaS Γ S = omegaMinus (limitSetJ Γ) := by
      refine hsub.antisymm ?_
      rw [omegaS_eq h hx₀]
      exact (convex_omegaMinus _).isPreconnected.subset_connectedComponentIn (hsub hx₀Ω)
        (omegaMinus_limitSetJ_subset_omegaGamma h hγ₀ hlox₀)
    exact Or.inr ⟨⟨⟨x₀, hsub hx₀Ω⟩, isOpen_omegaMinus_of_isClosed (isClosed_limitSetJ Γ)⟩, heq⟩

/-- Barbot's intermediate form (l.3196–3203): `Ω(S̃)` is the interior of the future (or past)
complete convex domain defined by `Λ₀(Γ)` itself. -/
theorem omegaS_eq_interior (h : CCAction Γ S) (hlox : ∃ γ ∈ Γ, IsLoxodromic (linOf γ)) :
    omegaS Γ S = interior (omegaPlus (loxRepSet Γ)) ∨
      omegaS Γ S = interior (omegaMinus (loxRepSet Γ)) := by
  rcases blem_loxregular h hlox with ⟨-, he⟩ | ⟨-, he⟩
  · exact Or.inl (by rw [he, limitSetJ, omegaPlus_closure_eq_interior])
  · exact Or.inr (by rw [he, limitSetJ, omegaMinus_closure_eq_interior])

/-- **Two null directions in `Λ(Γ)`**: `Ω⁺(Λ(Γ))` is a regular domain in Bonsante's sense
(`Flat.Cosmological`'s `CosmoRegular`) once it is future regular. -/
theorem cosmoRegular_limitSetJ {γ₀ : isom d} (hγ₀ : γ₀ ∈ Γ) (hlox₀ : IsLoxodromic (linOf γ₀))
    (hF : FutureRegular (limitSetJ Γ)) : CosmoRegular (limitSetJ Γ) := by
  obtain ⟨w₁, hw₁, w₂, hw₂, -, -, hne⟩ := exists_two_loxRepSet hγ₀ hlox₀
  exact ⟨hF, w₁, subset_closure hw₁, w₂, subset_closure hw₂, hne⟩

end Loxregular


/-! ## 6a. Proper discontinuity from an equivariant Gauss map (for Cor 10.3)

The mechanism of Barbot's `bprop:agissons` (4.16, l.1176–1180) without the Riemannian metric of the
level sets: the Gauss map `n` of the cosmological time is `L(Γ)`-equivariant into the unit future
hyperboloid `ℍᵈ` and bounded on compact sets, and `SO₀(1, d)` acts properly on `ℍᵈ` — in the
concrete form of the rest-frame norm `restNormSq n x = 2⟨x|n⟩² + |x|²`, which `L` carries from `n`
to `L n` and which is comparable to `‖x‖²` with constants depending on `‖n‖`. Properness on the
Cauchy surface `Σ` then bounds `γ s₀` and gives finiteness. The past case goes through the point
reflection `p ↦ −p` (`negConj`, `omegaMinus_eq_neg`). -/

section GaussProper

/-- The square of the Euclidean norm of `x` in the rest frame of a unit timelike `n`:
`2⟨x|n⟩² + |x|²`. -/
noncomputable def restNormSq (n x : Minkowski d) : ℝ := 2 * minkB x n ^ 2 + minkQ x

theorem restNormSq_linOf (g : isom d) (n x : Minkowski d) :
    restNormSq (linOf g n) (linOf g x) = restNormSq n x := by
  rw [restNormSq, restNormSq, minkB_linOf, lorentz.minkQ_apply (linOf_mem g)]

theorem restNormSq_le {n : Minkowski d} {R : ℝ} (hn : ‖n‖ ≤ R) (x : Minkowski d) :
    restNormSq n x ≤ (8 * R ^ 2 + 1) * ‖x‖ ^ 2 := by
  have h1 : |x.1| ≤ ‖x‖ := by simpa using norm_fst_le x
  have h2 : ‖x.2‖ ≤ ‖x‖ := norm_snd_le x
  have h3 : |n.1| ≤ R := by have := norm_fst_le n; simp at this; linarith
  have h4 : ‖n.2‖ ≤ R := (norm_snd_le n).trans hn
  have hi : |inner ℝ x.2 n.2| ≤ ‖x.2‖ * ‖n.2‖ := abs_real_inner_le_norm _ _
  have hB : |minkB x n| ≤ 2 * ‖x‖ * R := by
    rw [minkB]
    have e1 : |x.1| * |n.1| ≤ ‖x‖ * R :=
      mul_le_mul h1 h3 (abs_nonneg _) (norm_nonneg _)
    have e2 : ‖x.2‖ * ‖n.2‖ ≤ ‖x‖ * R :=
      mul_le_mul h2 h4 (norm_nonneg _) (norm_nonneg _)
    calc |-(x.1 * n.1) + inner ℝ x.2 n.2| ≤ |x.1| * |n.1| + ‖x.2‖ * ‖n.2‖ := by
          refine (abs_add_le _ _).trans (add_le_add ?_ hi); rw [abs_neg, abs_mul]
      _ ≤ 2 * ‖x‖ * R := by linarith
  have hQ : minkQ x ≤ ‖x‖ ^ 2 := by
    rw [minkQ]; nlinarith [norm_nonneg x.2, sq_nonneg x.1]
  have hB2 : minkB x n ^ 2 ≤ (2 * ‖x‖ * R) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hB 2
  rw [restNormSq]; nlinarith

theorem sq_norm_le_restNormSq {n : Minkowski d} (hn : IsFutureTimelike n) (hq : minkQ n = -1)
    (x : Minkowski d) : ‖x‖ ^ 2 ≤ 2 * n.1 ^ 2 * restNormSq n x := by
  set a := minkB x n
  set y := x + a • n with hy
  have hnn : minkB n n = -1 := by rw [← minkQ_eq_minkB]; exact hq
  have hyn : minkB y n = 0 := by
    rw [hy, minkB_add_left, minkB_smul_left, hnn]; ring
  have hQy : minkQ y = minkQ x + a ^ 2 := by
    rw [hy, minkQ_add, minkQ_smul, minkB_smul_right, hq]; ring
  have hN : restNormSq n x = a ^ 2 + minkQ y := by rw [restNormSq, hQy]; ring
  have hn1 : 0 < n.1 := hn.1
  have hn2 : ‖n.2‖ ^ 2 = n.1 ^ 2 - 1 := by
    have := hq; rw [minkQ] at this; linarith
  have hn2le : ‖n.2‖ ≤ n.1 := by
    nlinarith [norm_nonneg n.2]
  have hyi : y.1 * n.1 = inner ℝ y.2 n.2 := by
    have := hyn; rw [minkB] at this; linarith
  have hyi' : (y.1 * n.1) ^ 2 ≤ ‖y.2‖ ^ 2 * ‖n.2‖ ^ 2 := by
    rw [hyi, ← mul_pow, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm _ _) 2
  have hQy' : minkQ y = -y.1 ^ 2 + ‖y.2‖ ^ 2 := rfl
  have hy2 : ‖y.2‖ ^ 2 ≤ n.1 ^ 2 * minkQ y := by
    rw [hQy', hn2] at *; nlinarith
  have hy1 : y.1 ^ 2 ≤ ‖y.2‖ ^ 2 := by
    rw [hn2] at hyi'
    have h0 : 0 < n.1 ^ 2 := by positivity
    nlinarith [sq_nonneg (‖y.2‖), sq_nonneg y.1]
  have hx : x = y - a • n := by rw [hy]; abel
  have hx1 : x.1 = y.1 - a * n.1 := by rw [hx]; simp
  have hx2 : ‖x.2‖ ≤ ‖y.2‖ + |a| * n.1 := by
    rw [hx, Prod.snd_sub, Prod.smul_snd]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hn2le (abs_nonneg _))
  have hNa : restNormSq n x = a ^ 2 + minkQ y := hN
  have hA : |x.1| ^ 2 ≤ 2 * n.1 ^ 2 * restNormSq n x := by
    rw [sq_abs, hx1, hN]
    nlinarith [sq_nonneg (y.1 + a * n.1)]
  have hB : ‖x.2‖ ^ 2 ≤ 2 * n.1 ^ 2 * restNormSq n x := by
    have := pow_le_pow_left₀ (norm_nonneg _) hx2 2
    rw [hN]
    nlinarith [sq_nonneg (‖y.2‖ - |a| * n.1), sq_abs a]
  rw [Prod.norm_def, Real.norm_eq_abs]
  rcases le_total |x.1| ‖x.2‖ with h | h
  · rw [max_eq_right h]; exact hB
  · rw [max_eq_left h]; exact hA


/-- `‖L(γ) x‖ ≤ c ‖x‖` when `L(γ)` maps a unit future timelike `n` of norm `≤ R` to one. -/
theorem norm_linOf_le_of_gauss {g : isom d} {n : Minkowski d} {R : ℝ}
    (hn : IsFutureTimelike n) (hq : minkQ n = -1) (hR : ‖n‖ ≤ R) (hR' : ‖linOf g n‖ ≤ R)
    (x : Minkowski d) :
    ‖linOf g x‖ ≤ (2 * R ^ 2 * (8 * R ^ 2 + 1) + 1) * ‖x‖ := by
  have hn' : IsFutureTimelike (linOf g n) := lorentz.isFutureTimelike_apply (linOf_mem g) hn
  have hq' : minkQ (linOf g n) = -1 := by rw [lorentz.minkQ_apply (linOf_mem g), hq]
  have h1 := sq_norm_le_restNormSq hn' hq' (linOf g x)
  rw [restNormSq_linOf] at h1
  have h2 := restNormSq_le hR x
  have h3 : (linOf g n).1 ^ 2 ≤ R ^ 2 := by
    have : |(linOf g n).1| ≤ R := by have := norm_fst_le (linOf g n); simp at this; linarith
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have hN : 0 ≤ restNormSq n x := by
    have := sq_norm_le_restNormSq hn hq x
    have h0 : 0 < n.1 ^ 2 := by have := hn.1; positivity
    nlinarith [sq_nonneg ‖x‖]
  set c := 2 * R ^ 2 * (8 * R ^ 2 + 1)
  have hc : 0 ≤ c := by positivity
  have h4 : ‖linOf g x‖ ^ 2 ≤ c * ‖x‖ ^ 2 := by
    calc ‖linOf g x‖ ^ 2 ≤ 2 * (linOf g n).1 ^ 2 * restNormSq n x := h1
      _ ≤ 2 * R ^ 2 * restNormSq n x := by gcongr
      _ ≤ 2 * R ^ 2 * ((8 * R ^ 2 + 1) * ‖x‖ ^ 2) := by gcongr
      _ = c * ‖x‖ ^ 2 := by ring
  have hx0 : 0 ≤ (c + 1) * ‖x‖ := by positivity
  refine not_lt.1 fun hlt => ?_
  nlinarith [norm_nonneg x, norm_nonneg (linOf g x), sq_nonneg ‖x‖]

/-- **Proper discontinuity from an equivariant Gauss map** (the mechanism of Barbot's
`bprop:agissons`, l.1176–1180, without the Riemannian metric of `S_t`): if `Γ` acts properly on a
nonempty closed invariant `S`, and a set `Ω` carries a map `ν` to the unit future
hyperboloid, `L(Γ)`-equivariant and bounded on compact subsets, then `Γ` acts properly on `Ω`.
For `γK ∩ K ≠ ∅`, `L(γ)` maps a bounded point `ν(k)` of `ℍᵈ` to a bounded point, so `L(γ)` is bounded
(`norm_linOf_le_of_gauss`, the rest-frame norm `restNormSq`), hence `γ s₀` is bounded for a fixed
`s₀ ∈ S`. -/
theorem finite_of_gaussEquivariant {Γ : Subgroup (isom d)} {S Ω : Set (Minkowski d)}
    (hSc : IsClosed S) (hSne : S.Nonempty) (hinv : ∀ γ ∈ Γ, ∀ x ∈ S, γ • x ∈ S)
    (hprop : ∀ K ⊆ S, IsCompact K → {γ : isom d | γ ∈ Γ ∧ (γ • K ∩ K).Nonempty}.Finite)
    (ν : Minkowski d → Minkowski d)
    (hν : ∀ p ∈ Ω, IsFutureTimelike (ν p) ∧ minkQ (ν p) = -1)
    (heq : ∀ γ ∈ Γ, ∀ p ∈ Ω, ν (γ • p) = linOf γ (ν p))
    (hbd : ∀ K ⊆ Ω, IsCompact K → ∃ R, ∀ p ∈ K, ‖ν p‖ ≤ R) :
    ∀ K ⊆ Ω, IsCompact K → {γ : isom d | γ ∈ Γ ∧ (γ • K ∩ K).Nonempty}.Finite := by
  intro K hKΩ hK
  obtain ⟨R, hR⟩ := hbd K hKΩ hK
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.1 hK.isBounded
  obtain ⟨s₀, hs₀⟩ := hSne
  set c := 2 * R ^ 2 * (8 * R ^ 2 + 1) + 1
  set ρ := ‖s₀‖ + |B| + c * (‖s₀‖ + |B|)
  have hc : 0 ≤ c := by positivity
  have hC : IsCompact (S ∩ Metric.closedBall 0 ρ) := (isCompact_closedBall 0 ρ).inter_left hSc
  refine (hprop _ inter_subset_left hC).subset ?_
  rintro γ ⟨hγ, y, hyK, hy⟩
  obtain ⟨k, hk, rfl⟩ := Set.mem_smul_set.1 hyK
  refine ⟨hγ, γ • s₀, Set.smul_mem_smul_set ⟨hs₀, ?_⟩, hinv γ hγ s₀ hs₀, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right]
    have := abs_nonneg B
    have : 0 ≤ c * (‖s₀‖ + |B|) := by positivity
    linarith
  · rw [Metric.mem_closedBall, dist_zero_right]
    have hkΩ := hKΩ hk
    have hL := norm_linOf_le_of_gauss (g := γ) (hν k hkΩ).1 (hν k hkΩ).2 (hR k hk)
      (by rw [← heq γ hγ k hkΩ]; exact hR _ hy) (s₀ - k)
    have hdec : γ • s₀ = γ • k + linOf γ (s₀ - k) := by
      rw [isom_smul_def, isom_smul_def, ← isom_sub]; abel
    have hk' : ‖k‖ ≤ |B| := (hB k hk).trans (le_abs_self B)
    have hγk : ‖γ • k‖ ≤ |B| := (hB _ hy).trans (le_abs_self B)
    have hsk : ‖s₀ - k‖ ≤ ‖s₀‖ + |B| := (norm_sub_le _ _).trans (by linarith)
    rw [hdec]
    calc ‖γ • k + linOf γ (s₀ - k)‖ ≤ ‖γ • k‖ + ‖linOf γ (s₀ - k)‖ := norm_add_le _ _
      _ ≤ |B| + c * (‖s₀‖ + |B|) := add_le_add hγk (hL.trans (mul_le_mul_of_nonneg_left hsk hc))
      _ ≤ ρ := by linarith [norm_nonneg s₀]

variable {Λ : Set (PenroseSphere d × ℝ)}

/-- **The Gauss map is equivariant**: `n(gp) = L(g) n(p)` for `g` preserving `Ω⁺(Λ)`
(`cosmoTime_smul`, `cosmoRetract_smul`). -/
theorem gaussMap_smul (h : CosmoRegular Λ) {g : isom d}
    (hg : (fun p => g • p) ⁻¹' omegaPlus Λ = omegaPlus Λ) {p : Minkowski d}
    (hp : p ∈ omegaPlus Λ) : gaussMap Λ (g • p) = linOf g (gaussMap Λ p) := by
  rw [gaussMap, gaussMap, cosmoTime_smul hg, cosmoRetract_smul h hg hp, map_smul,
    isom_smul_def, isom_smul_def, isom_sub]

/-- **The Gauss map is bounded on compact subsets of `Ω⁺(Λ)`** (no continuity of `r` needed):
`T ≥ ε > 0` on `K`, and `r(K)` lies in the compact `cl Ω ∩ J⁻(q)` for a `q` above `K`. -/
theorem exists_norm_gaussMap_le (h : CosmoRegular Λ) {K : Set (Minkowski d)}
    (hKΩ : K ⊆ omegaPlus Λ) (hK : IsCompact K) : ∃ R, ∀ p ∈ K, ‖gaussMap Λ p‖ ≤ R := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, fun _ hp => hp.elim⟩
  obtain ⟨p₀, hp₀, hmin⟩ := hK.exists_isMinOn hne ((continuousOn_cosmoTime h).mono hKΩ)
  set ε := cosmoTime Λ p₀
  have hε : 0 < ε := cosmoTime_pos h (hKΩ hp₀)
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.1 hK.isBounded
  set q : Minkowski d := (2 * |B|, 0)
  have hpq : ∀ p ∈ K, (minkowski d).le ⊤ p q := by
    intro p hp
    rw [minkowski_le_top_iff]
    have h1 : |p.1| ≤ |B| := by
      have := norm_fst_le p; simp at this; linarith [hB p hp, le_abs_self B]
    have h2 : ‖p.2‖ ≤ |B| := (norm_snd_le p).trans ((hB p hp).trans (le_abs_self B))
    simp only [q, zero_sub, norm_neg]
    linarith [le_abs_self p.1]
  obtain ⟨B', hB'⟩ := isBounded_iff_forall_norm_le.1 (isCompact_cosmoPast h q).isBounded
  refine ⟨ε⁻¹ * (|B| + B'), fun p hp => ?_⟩
  have hpΩ := hKΩ hp
  obtain ⟨hfr, hle, -⟩ := cosmoRetract_spec h hpΩ
  have hr : ‖cosmoRetract Λ p‖ ≤ B' :=
    hB' _ ⟨frontier_subset_closure hfr, (minkowski d).le_trans hle (hpq p hp)⟩
  have hT : ε ≤ cosmoTime Λ p := hmin hp
  rw [gaussMap, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (cosmoTime_pos h hpΩ)]
  have hnum : ‖p - cosmoRetract Λ p‖ ≤ |B| + B' :=
    (norm_sub_le _ _).trans (add_le_add ((hB p hp).trans (le_abs_self B)) hr)
  calc (cosmoTime Λ p)⁻¹ * ‖p - cosmoRetract Λ p‖ ≤ ε⁻¹ * ‖p - cosmoRetract Λ p‖ := by
        gcongr
    _ ≤ ε⁻¹ * (|B| + B') := by gcongr


/-- The affine map `p ↦ −g(−p)`. -/
noncomputable def negConjAff (g : isom d) : Minkowski d ≃ᵃ[ℝ] Minkowski d :=
  (AffineEquiv.pointReflection ℝ (0 : Minkowski d)).trans
    ((g : Minkowski d ≃ᵃ[ℝ] Minkowski d).trans (AffineEquiv.pointReflection ℝ (0 : Minkowski d)))

theorem negConjAff_apply (g : isom d) (p : Minkowski d) :
    negConjAff g p = -((g : Minkowski d ≃ᵃ[ℝ] Minkowski d) (-p)) := by
  simp [negConjAff, Equiv.pointReflection_apply]

theorem negConjAff_linear (g : isom d) :
    (negConjAff g).linear = (g : Minkowski d ≃ᵃ[ℝ] Minkowski d).linear := by
  ext v : 1
  have e := isom_sub (negConjAff g) 0 v
  rw [sub_zero] at e
  rw [← e, negConjAff_apply, negConjAff_apply, neg_zero]
  have e2 := isom_sub (g : Minkowski d ≃ᵃ[ℝ] Minkowski d) (-v) 0
  rw [zero_sub, neg_neg] at e2
  rw [← e2]; abel

/-- **The point-reflection conjugate** `g̃ = σ g σ`, `σ(p) = −p`: same linear part, opposite
translation. It turns the past statements into future ones (`omegaMinus_eq_neg`). -/
noncomputable def negConj (g : isom d) : isom d :=
  ⟨negConjAff g, by rw [mem_isom_iff, negConjAff_linear]; exact g.2⟩

theorem negConj_smul (g : isom d) (p : Minkowski d) : negConj g • p = -(g • -p) :=
  negConjAff_apply g p

theorem linOf_negConj (g : isom d) : linOf (negConj g) = linOf g := negConjAff_linear g

theorem mem_omegaMinus_iff_neg {p : Minkowski d} :
    p ∈ omegaMinus Λ ↔ -p ∈ omegaPlus (negS d ⁻¹' Λ) := by
  rw [omegaMinus_eq_neg]; rfl

/-- `Ω⁻(Λ)` past regular with two null directions makes `Ω⁺(−Λ)` Bonsante-regular. -/
theorem cosmoRegular_negS (hP : PastRegular Λ) (htwo : ∃ w₁ ∈ Λ, ∃ w₂ ∈ Λ, w₁.1 ≠ w₂.1) :
    CosmoRegular (negS d ⁻¹' Λ) := by
  have hpre : omegaPlus (negS d ⁻¹' Λ) = (fun p : Minkowski d => -p) ⁻¹' omegaMinus Λ := by
    ext p; rw [mem_preimage, mem_omegaMinus_iff_neg, neg_neg]
  obtain ⟨w₁, hw₁, w₂, hw₂, hne⟩ := htwo
  refine ⟨⟨?_, ?_⟩, (w₁.1, -w₁.2), by simpa using hw₁, (w₂.1, -w₂.2), by simpa using hw₂, hne⟩
  · obtain ⟨p, hp⟩ := hP.1
    exact ⟨-p, mem_omegaMinus_iff_neg.1 hp⟩
  · rw [hpre]; exact hP.2.preimage continuous_neg


end GaussProper

/-! ## 6. `bcor:loxo_proper` (Corollary 10.3): `M(S) = Γ\Ω(S̃)` -/

section LoxoProper

variable {Γ : Subgroup (isom d)} {S : Set (Minkowski d)}

/-- **`Γ` acts freely and properly discontinuously on `Ω`** (in `𝐌ⁿ`, with compact subsets of `Ω`;
the form of `CCAction`). -/
def ActsFreelyProperlyOn (Γ : Subgroup (isom d)) (Ω : Set (Minkowski d)) : Prop :=
  (∀ γ ∈ Γ, γ ≠ 1 → ∀ x ∈ Ω, γ • x ≠ x) ∧
    ∀ K ⊆ Ω, IsCompact K → {γ : isom d | γ ∈ Γ ∧ (γ • K ∩ K).Nonempty}.Finite

/-- A free action gives mathlib's `IsCancelSMul` on the subtype. -/
theorem isCancelSMul_of_free {Ω : Opens (Minkowski d)} [FlatQuotient.Invariant Γ Ω]
    (hfree : ∀ γ ∈ Γ, γ ≠ 1 → ∀ x ∈ Ω, γ • x ≠ x) : IsCancelSMul Γ Ω where
  left_cancel' a b c hbc := by
    have := congrArg (fun q : Ω => a⁻¹ • q) hbc
    simpa using this
  right_cancel' a b c habc := by
    by_contra hab
    have hab' : ((b : isom d)⁻¹ * a) ≠ 1 := fun e =>
      hab (Subtype.ext (by rw [inv_mul_eq_one] at e; exact e.symm))
    refine hfree _ (Γ.mul_mem (Γ.inv_mem b.2) a.2) hab' c c.2 ?_
    have := congrArg Subtype.val habc
    simp only [FlatQuotient.coe_smul] at this
    rw [mul_smul, this, inv_smul_smul]

/-- A properly discontinuous action in `𝐌ⁿ`'s form gives mathlib's `ProperlyDiscontinuousSMul` on
the subtype. -/
theorem properlyDiscontinuousSMul_of_finite {Ω : Opens (Minkowski d)} [FlatQuotient.Invariant Γ Ω]
    (hprop : ∀ K ⊆ (Ω : Set (Minkowski d)), IsCompact K →
      {γ : isom d | γ ∈ Γ ∧ (γ • K ∩ K).Nonempty}.Finite) :
    ProperlyDiscontinuousSMul Γ Ω where
  finite_disjoint_inter_image {K L} hK hL := by
    set K' : Set (Minkowski d) := Subtype.val '' (K ∪ L)
    have hK' : IsCompact K' := (hK.union hL).image continuous_subtype_val
    have hsub : K' ⊆ Ω := by rintro _ ⟨x, -, rfl⟩; exact x.2
    refine (Set.Finite.preimage (f := fun γ : Γ => (γ : isom d))
      Subtype.val_injective.injOn (hprop K' hsub hK')).subset ?_
    rintro γ ⟨_, ⟨x, hx, rfl⟩, hxL⟩
    exact ⟨γ.2, (γ : isom d) • (x : Minkowski d),
      Set.smul_mem_smul_set ⟨x, Or.inl hx, rfl⟩, ⟨γ • x, Or.inr hxL, rfl⟩⟩

/-- **Cor 10.3, freeness** (l.3225–3226: "by definition of `Ω(S̃)`"): Prop 8.10. -/
theorem loxo_free (h : CCAction Γ S) : ∀ γ ∈ Γ, γ ≠ 1 → ∀ x ∈ omegaS Γ S, γ • x ≠ x :=
  fun γ hγ h1 x hx => ((bprop_ghyp h).2.2.2.2 γ hγ h1 x hx).1

/-- **Cor 10.3, proper discontinuity** (l.3222–3224, "through `bprop:agissons`"): proved, by the
equivariant Gauss map in place of 4.16's Riemannian level sets (`finite_of_gaussEquivariant`):
`n` of `Ω⁺(Λ(Γ))` in the future case of `blem_loxregular`, `p ↦ n(−p)` of `Ω⁺(−Λ(Γ))` in the past
case, and the properness of `Γ` on `Σ` (`CCAction.proper`). -/
theorem loxo_properlyDiscontinuous (h : CCAction Γ S) (hlox : ∃ γ ∈ Γ, IsLoxodromic (linOf γ)) :
    ∀ K ⊆ omegaS Γ S, IsCompact K → {γ : isom d | γ ∈ Γ ∧ (γ • K ∩ K).Nonempty}.Finite := by
  have hSc : IsClosed S := by
    obtain ⟨g, hg, hS⟩ := isEntireAcausalGraph_iff.1 h.cc.entire
    rw [hS]; exact isClosed_graph hg.lipschitzWith.continuous
  have hfin := fun (Ω : Set (Minkowski d)) => finite_of_gaussEquivariant (Ω := Ω) hSc h.nonempty
    (fun γ hγ x hx => h.smul_mem hγ hx) h.proper
  obtain ⟨γ₀, hγ₀, hlox₀⟩ := hlox
  rcases blem_loxregular h ⟨γ₀, hγ₀, hlox₀⟩ with ⟨hF, he⟩ | ⟨hP, he⟩
  · rw [he]
    have hc := cosmoRegular_limitSetJ hγ₀ hlox₀ hF
    exact hfin _ (gaussMap (limitSetJ Γ))
      (fun p hp => ⟨isFutureTimelike_gaussMap hc hp, minkQ_gaussMap hc hp⟩)
      (fun γ hγ p hp => gaussMap_smul hc (preservesOmega_limitSetJ Γ γ hγ) hp)
      (fun K hK hKc => exists_norm_gaussMap_le hc hK hKc)
  · rw [he]
    obtain ⟨w₁, hw₁, w₂, hw₂, -, -, hne⟩ := exists_two_loxRepSet hγ₀ hlox₀
    have hc := cosmoRegular_negS hP ⟨w₁, subset_closure hw₁, w₂, subset_closure hw₂, hne⟩
    set Λ' := negS d ⁻¹' limitSetJ Γ
    have hmem : ∀ γ ∈ Γ, ∀ x, γ • x ∈ omegaMinus (limitSetJ Γ) ↔ x ∈ omegaMinus (limitSetJ Γ) :=
      fun γ hγ x => ⟨fun hx => by
        have := smul_mem_omegaMinus_limitSetJ (Γ.inv_mem hγ) hx
        rwa [inv_smul_smul] at this, fun hx => smul_mem_omegaMinus_limitSetJ hγ hx⟩
    have hpres : ∀ γ ∈ Γ, (fun p => negConj γ • p) ⁻¹' omegaPlus Λ' = omegaPlus Λ' := by
      intro γ hγ
      ext q
      rw [mem_preimage, negConj_smul, ← neg_neg q, ← mem_omegaMinus_iff_neg, neg_neg,
        ← mem_omegaMinus_iff_neg]
      exact hmem γ hγ _
    have hnΩ : ∀ p ∈ omegaMinus (limitSetJ Γ), -p ∈ omegaPlus Λ' :=
      fun p hp => mem_omegaMinus_iff_neg.1 hp
    refine hfin _ (fun p => gaussMap Λ' (-p))
      (fun p hp => ⟨isFutureTimelike_gaussMap hc (hnΩ p hp), minkQ_gaussMap hc (hnΩ p hp)⟩)
      (fun γ hγ p hp => ?_) (fun K hK hKc => ?_)
    · have : -(γ • p) = negConj γ • (-p) := by rw [negConj_smul, neg_neg]
      show gaussMap Λ' (-(γ • p)) = _
      rw [this, gaussMap_smul hc (hpres γ hγ) (hnΩ p hp), linOf_negConj]
    · obtain ⟨R, hR⟩ := exists_norm_gaussMap_le hc (K := (fun p => -p) '' K)
        (by rintro _ ⟨p, hp, rfl⟩; exact hnΩ p (hK hp)) (hKc.image continuous_neg)
      exact ⟨R, fun p hp => hR _ ⟨p, hp, rfl⟩⟩


/-- `bcor:loxo_proper` (Cor 10.3, l.3213–3228): `Γ` acts freely and properly discontinuously
on `Ω(S̃)`, and — in the future case of `blem_loxregular`, the past one being its time reversal
(l.3181–3183; `Lox.bcor_loxo_proper_past`, `Flat/Lox/PastProper`) — the quotient `M(S) = Γ\Ω(S̃)` is a flat spacetime, globally
hyperbolic in ETT's sense, with an acausal Cauchy surface: the image of a level set of the
cosmological time (`Flat.Examples`' `gh_quotient_omegaPlus`, `isCauchySurface_quotient_cosmoLevel`).
Cauchy-completeness is `loxo_cauchyComplete`. -/
theorem bcor_loxo_proper (h : CCAction Γ S) (hlox : ∃ γ ∈ Γ, IsLoxodromic (linOf γ)) :
    ActsFreelyProperlyOn Γ (omegaS Γ S) ∧
      (omegaS Γ S = omegaPlus (limitSetJ Γ) →
        ∃ M : FlatSpacetime.{0} d, IsQuotientOf M Γ (omegaSOpens Γ S) ∧ GH M ∧
          ∃ Sc : Set M, (flatCausality d M).IsCauchySurface Sc ∧
            (flatCausality d M).IsAcausal Sc) := by
  refine ⟨⟨loxo_free h, loxo_properlyDiscontinuous h hlox⟩, fun heq => ?_⟩
  obtain ⟨γ₀, hγ₀, hlox₀⟩ := hlox
  obtain ⟨x₀, hx₀⟩ := h.nonempty
  have hF : FutureRegular (limitSetJ Γ) :=
    ⟨⟨x₀, heq ▸ subset_omegaS h hx₀⟩, isOpen_omegaPlus_of_isClosed (isClosed_limitSetJ Γ)⟩
  have hc := cosmoRegular_limitSetJ hγ₀ hlox₀ hF
  have hP := preservesOmega_limitSetJ Γ
  haveI : FlatQuotient.Invariant Γ hc.regular.opens := hP.invariant (h := hc)
  have hΩ : ((hc.regular.opens : Opens (Minkowski d)) : Set (Minkowski d)) = omegaS Γ S := heq.symm
  haveI : IsCancelSMul Γ hc.regular.opens :=
    isCancelSMul_of_free fun γ hγ h1 x hx => loxo_free h γ hγ h1 x (hΩ ▸ hx)
  haveI : ProperlyDiscontinuousSMul Γ hc.regular.opens :=
    properlyDiscontinuousSMul_of_finite fun K hK hKc =>
      loxo_properlyDiscontinuous h ⟨γ₀, hγ₀, hlox₀⟩ K (hΩ ▸ hK) hKc
  have hopens : omegaSOpens Γ S = hc.regular.opens := Opens.ext hΩ.symm
  refine ⟨FlatQuotient.toFlatSpacetime Γ hc.regular.opens (isConnected_omegaPlus hc), ?_,
    gh_quotient_omegaPlus (h := hc) hP, _,
    (isCauchySurface_quotient_cosmoLevel (h := hc) hP one_pos).1,
    (isCauchySurface_quotient_cosmoLevel (h := hc) hP one_pos).2⟩
  rw [hopens]
  exact FlatQuotient.isQuotientOf_toFlatSpacetime _ _ _

/-- **Cor 10.3, Cauchy-completeness of `M(S)`** (l.3217–3218, through `bprop:agissons` and
`bprop:regular_cauchy_complete`). -/
theorem loxo_cauchyComplete (h : CCAction Γ S) (hlox : ∃ γ ∈ Γ, IsLoxodromic (linOf γ))
    {Λ : Set (PenroseSphere d × ℝ)} (hc : CosmoRegular Λ) (hΛ : omegaS Γ S = omegaPlus Λ)
    [FlatQuotient.Invariant Γ hc.regular.opens] [ProperlyDiscontinuousSMul Γ hc.regular.opens]
    [IsCancelSMul Γ hc.regular.opens] :
    IsCauchyComplete d (FlatQuotient Γ hc.regular.opens) := by
  -- `h`, `hlox`, `hΛ` are the paper's setting; the proof needs only `CosmoRegular Λ` and the
  -- free, properly discontinuous `Γ`-action on `Ω⁺(Λ)` (⚠ weakened, `Flat.Lox.QuotientComplete`)
  have _setting : CCAction Γ S ∧ (∃ γ ∈ Γ, IsLoxodromic (linOf γ)) ∧ omegaS Γ S = omegaPlus Λ :=
    ⟨h, hlox, hΛ⟩  -- unused (⚠ weakened)
  exact Lox.isCauchyComplete_flatQuotient_cosmo hc (completeSpace_inducedLength_cosmoLevel hc one_pos)

end LoxoProper

/-! ## 7. The gx exports: uniformization (`docs/BARBOT-THEOREMS.md` §3, the contract with gx) -/

section Uniformization

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace (Minkowski d) M]
  [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))] {x₀ : M}
  {D : UniversalCover M x₀ → Minkowski d} {ρ : Deck (UniversalCover.proj M x₀) →* isom d}
  {S : Set M}

/-- **Uniformization, injectivity** (gx): the developing map is injective (Prop 8.12,
`Flat.Develop`'s `bprop_danom`). Holds with no case hypothesis. -/
theorem uniformization_injective (hpair : IsDevelopingPair x₀ D ρ)
    (hcaus : (flatCausality d M).IsCausal) (h : DevelopsCC x₀ D S) : Injective D :=
  (bprop_danom hpair hcaus h).1

/-- **Uniformization, image** (gx): when the holonomy group `Γ = ρ(π₁)` has a loxodromic element,
`𝒟(M̃) ⊆ Ω⁺(Λ(Γ))` with `Λ(Γ)` future regular, or (time reversal) `𝒟(M̃) ⊆ Ω⁻(Λ(Γ))` with `Λ(Γ)` past
regular (Prop 8.12 and Lemma 10.2). Neither nonelementarity nor `ker L = 1` is needed. -/
theorem uniformization_image (hpair : IsDevelopingPair x₀ D ρ)
    (hcaus : (flatCausality d M).IsCausal) (h : DevelopsCC x₀ D S)
    (hlox : ∃ γ ∈ ρ.range, IsLoxodromic (linOf γ)) :
    (FutureRegular (limitSetJ ρ.range) ∧ range D ⊆ omegaPlus (limitSetJ ρ.range)) ∨
      (PastRegular (limitSetJ ρ.range) ∧ range D ⊆ omegaMinus (limitSetJ ρ.range)) := by
  have hD := (bprop_danom hpair hcaus h).2
  rcases blem_loxregular (ccAction_of_developsCC hpair h) hlox with ⟨hF, he⟩ | ⟨hP, he⟩
  · exact Or.inl ⟨hF, he ▸ hD⟩
  · exact Or.inr ⟨hP, he ▸ hD⟩

/-- **Uniformization, the action** (gx): `ρ(Γ)` acts freely and properly discontinuously on
`Ω⁺(Λ(Γ))` (future case) or on `Ω⁻(Λ(Γ))` (past case), which is `Ω(S̃)` (Lemma 10.2, Cor 10.3). -/
theorem uniformization_properlyDiscontinuous (hpair : IsDevelopingPair x₀ D ρ)
    (h : DevelopsCC x₀ D S) (hlox : ∃ γ ∈ ρ.range, IsLoxodromic (linOf γ)) :
    (FutureRegular (limitSetJ ρ.range) ∧
        omegaS ρ.range (D '' (UniversalCover.proj M x₀ ⁻¹' S)) = omegaPlus (limitSetJ ρ.range) ∧
        ActsFreelyProperlyOn ρ.range (omegaPlus (limitSetJ ρ.range))) ∨
      (PastRegular (limitSetJ ρ.range) ∧
        omegaS ρ.range (D '' (UniversalCover.proj M x₀ ⁻¹' S)) = omegaMinus (limitSetJ ρ.range) ∧
        ActsFreelyProperlyOn ρ.range (omegaMinus (limitSetJ ρ.range))) := by
  have hcc := ccAction_of_developsCC hpair h
  have hfp := (bcor_loxo_proper hcc hlox).1
  rcases blem_loxregular hcc hlox with ⟨hF, he⟩ | ⟨hP, he⟩
  · exact Or.inl ⟨hF, he, he ▸ hfp⟩
  · exact Or.inr ⟨hP, he, he ▸ hfp⟩

/-- **Uniformization, the three exports together**, on the same side (future or past). -/
theorem uniformization (hpair : IsDevelopingPair x₀ D ρ) (hcaus : (flatCausality d M).IsCausal)
    (h : DevelopsCC x₀ D S) (hlox : ∃ γ ∈ ρ.range, IsLoxodromic (linOf γ)) :
    Injective D ∧
      ((FutureRegular (limitSetJ ρ.range) ∧ range D ⊆ omegaPlus (limitSetJ ρ.range) ∧
          ActsFreelyProperlyOn ρ.range (omegaPlus (limitSetJ ρ.range))) ∨
        (PastRegular (limitSetJ ρ.range) ∧ range D ⊆ omegaMinus (limitSetJ ρ.range) ∧
          ActsFreelyProperlyOn ρ.range (omegaMinus (limitSetJ ρ.range)))) := by
  have hD := (bprop_danom hpair hcaus h).2
  have hcc := ccAction_of_developsCC hpair h
  have hfp := (bcor_loxo_proper hcc hlox).1
  refine ⟨(bprop_danom hpair hcaus h).1, ?_⟩
  rcases blem_loxregular hcc hlox with ⟨hF, he⟩ | ⟨hP, he⟩
  · exact Or.inl ⟨hF, he ▸ hD, he ▸ hfp⟩
  · exact Or.inr ⟨hP, he ▸ hD, he ▸ hfp⟩

end Uniformization


/-! ## 8. Elementary and nonelementary groups; Def 4.18 and the families (a), (b) -/

section Families

universe u

/-- **Nonelementary** (l.3237–3239, l.3336–3337): no finite-index subgroup of `L(Γ)` preserves an
isotropic direction (a point of `𝒮`, for the conformal action `lorentzSphere`). Its negation is
Barbot's elementary case [10.M]. -/
def IsNonelementary (Γ : Subgroup (isom d)) : Prop :=
  ∀ H : Subgroup (lorentz d), H ≤ linearImage Γ → H.relIndex (linearImage Γ) ≠ 0 →
    ¬∃ u : PenroseSphere d, ∀ A ∈ H, lorentzSphere A u = u

/-- `Ω⁺(Λ(Γ))`, as an open set (`blem:closecool`). -/
def limitOpensPlus (Γ : Subgroup (isom d)) : Opens (Minkowski d) :=
  ⟨omegaPlus (limitSetJ Γ), isOpen_omegaPlus_of_isClosed (isClosed_limitSetJ Γ)⟩

/-- `Ω⁻(Λ(Γ))`, as an open set. -/
def limitOpensMinus (Γ : Subgroup (isom d)) : Opens (Minkowski d) :=
  ⟨omegaMinus (limitSetJ Γ), isOpen_omegaMinus_of_isClosed (isClosed_limitSetJ Γ)⟩

/-- **A future admissible representation** (l.1212–1220), in subgroup form: `Γ ≤ Isom(𝐌ⁿ)` with `L`
injective on `Γ` (so `Γ = ρ(L(Γ))`, `L ∘ ρ = id`), `L(Γ)` discrete in `SO₀(1, d)` without global
fixed point on `𝐇̄ⁿ⁻¹` (l.1212–1214), preserving a future complete regular convex domain. -/
def IsFutureAdmissible (Γ : Subgroup (isom d)) : Prop :=
  Set.InjOn linearPart (Γ : Set (isom d)) ∧ DiscreteTopology (linearImage Γ) ∧
    ¬HasGlobalFixedPoint (linearImage Γ) ∧
    ∃ Λ : Set (PenroseSphere d × ℝ), FutureRegular Λ ∧ PreservesOmega Λ Γ

/-- **A past admissible representation** (l.1216–1220): as `IsFutureAdmissible`, preserving a past
complete regular convex domain. -/
def IsPastAdmissible (Γ : Subgroup (isom d)) : Prop :=
  Set.InjOn linearPart (Γ : Set (isom d)) ∧ DiscreteTopology (linearImage Γ) ∧
    ¬HasGlobalFixedPoint (linearImage Γ) ∧
    ∃ Λ : Set (PenroseSphere d × ℝ), PastRegular Λ ∧
      ∀ γ ∈ Γ, (fun p => γ • p) ⁻¹' omegaMinus Λ = omegaMinus Λ

/-- **An admissible representation** (l.1212–1220): future or past admissible. -/
def IsAdmissible (Γ : Subgroup (isom d)) : Prop :=
  IsFutureAdmissible Γ ∨ IsPastAdmissible Γ

/-- `bdef:definitioncauchyhyp` (Def 4.18, l.1277–1281): a **Cauchy-hyperbolic spacetime** is the
quotient of `Ω^±(Λ(ρ))` by `ρ(Γ)` for an admissible `ρ`, `Λ(ρ)` the closure of the repulsive fixed
points of its loxodromic elements (`bprop:admlox`). Reading of `±`: the sign is tied to the side of
admissibility — `Ω⁺` for a future admissible, `Ω⁻` for a past admissible `ρ`. -/
def IsCauchyHyperbolic (M : FlatSpacetime.{u} d) : Prop :=
  ∃ Γ : Subgroup (isom d),
    (IsFutureAdmissible Γ ∧ IsQuotientOf M Γ (limitOpensPlus Γ)) ∨
      (IsPastAdmissible Γ ∧ IsQuotientOf M Γ (limitOpensMinus Γ))

/-- A Cauchy-hyperbolic spacetime comes from an admissible representation. -/
theorem IsCauchyHyperbolic.exists_isAdmissible {M : FlatSpacetime.{u} d}
    (hM : IsCauchyHyperbolic M) : ∃ Γ : Subgroup (isom d), IsAdmissible Γ ∧
      (IsQuotientOf M Γ (limitOpensPlus Γ) ∨ IsQuotientOf M Γ (limitOpensMinus Γ)) := by
  obtain ⟨Γ, ⟨hF, hq⟩ | ⟨hP, hq⟩⟩ := hM
  · exact ⟨Γ, Or.inl hF, Or.inl hq⟩
  · exact ⟨Γ, Or.inr hP, Or.inr hq⟩

/-- The translation vectors of `ker L ∩ Γ` (Barbot's `𝒩`, l.3407–3409). -/
def kerTranslations (Γ : Subgroup (isom d)) : Set (Minkowski d) :=
  {v | ∃ γ ∈ Γ, linOf γ = 1 ∧ trOf γ = v}

/-- A **spacelike** linear subspace: `minkQ > 0` off `0`. -/
def IsSpacelikeSubmodule (E : Submodule ℝ (Minkowski d)) : Prop :=
  ∀ v ∈ E, v ≠ 0 → 0 < minkQ v

/-- **Family (b) for a given group `Γ`: a central extension over a Cauchy-hyperbolic spacetime**
(`docs/BARBOT-THEOREMS.md` §1, DEC-44; Barbot l.3405–3456): `M = Γ\Ω` with `E` spacelike, the
translation vectors of `ker L ∩ Γ` a lattice of `E` (ball-finite, spanning `E`), `L(γ)|_E = id` for
all `γ ∈ Γ` (the extension `0 → 𝒩 → Γ → L(Γ) → 0` central), `Ω = Ω^±(Λ(Γ))` invariant under `E`, and
`L(Γ)` discrete without global fixed point (its image in `Isom(𝐌ⁿ/E)`, l.3428–3430). Its quotient by
`E` is the Cauchy-hyperbolic `M(L)` when `L(Γ)` acts freely; the fibres are the tori `E/𝒩`.
Reading: "without global fixed point" is Def 4.18's condition (l.1212–1214), not
`docs/BARBOT-THEOREMS.md` §1's "nonelementary" (which is stronger: an infinite dihedral group with a
loxodromic has no global fixed point and is elementary). -/
def IsCHCentralExtensionOf (M : FlatSpacetime.{u} d) (Γ : Subgroup (isom d)) : Prop :=
  ∃ E : Submodule ℝ (Minkowski d),
    IsSpacelikeSubmodule E ∧ Submodule.span ℝ (kerTranslations Γ) = E ∧
    (∀ R : ℝ, (kerTranslations Γ ∩ Metric.closedBall 0 R).Finite) ∧
    (∀ γ ∈ Γ, ∀ v ∈ E, linOf γ v = v) ∧
    DiscreteTopology (linearImage Γ) ∧ ¬HasGlobalFixedPoint (linearImage Γ) ∧
    ((IsQuotientOf M Γ (limitOpensPlus Γ) ∧ ∀ v ∈ E, ∀ p ∈ omegaPlus (limitSetJ Γ),
        p + v ∈ omegaPlus (limitSetJ Γ)) ∨
      (IsQuotientOf M Γ (limitOpensMinus Γ) ∧ ∀ v ∈ E, ∀ p ∈ omegaMinus (limitSetJ Γ),
        p + v ∈ omegaMinus (limitSetJ Γ)))

/-- **Family (b): a central extension over a Cauchy-hyperbolic spacetime** — `IsCHCentralExtensionOf`
for some `Γ`. -/
def IsCHCentralExtension (M : FlatSpacetime.{u} d) : Prop :=
  ∃ Γ : Subgroup (isom d), IsCHCentralExtensionOf M Γ

/-- **Family (a): the literal twisted product "Cauchy-hyperbolic × torus"** (l.3454–3456), in the
form of `docs/BARBOT-THEOREMS.md` §1: family (b) with `L(Γ)` torsion-free, for the same `Γ` —
exactly when the quotient by `E` is a manifold, the Cauchy-hyperbolic base `L(Γ)\Ω(L(Γ))`, and `M`
the bundle over it with fibre the torus `E/𝒩` and translation monodromy ((b) = (a) iff `L(Γ)` is
torsion-free). -/
def IsCHTorusProduct (M : FlatSpacetime.{u} d) : Prop :=
  ∃ Γ : Subgroup (isom d), IsCHCentralExtensionOf M Γ ∧
    ∀ γ ∈ Γ, IsOfFinOrder (linOf γ) → linOf γ = 1

/-- Family (a) is a case of family (b). -/
theorem IsCHTorusProduct.isCHCentralExtension {M : FlatSpacetime.{u} d}
    (hM : IsCHTorusProduct M) : IsCHCentralExtension M :=
  let ⟨Γ, hΓ, _⟩ := hM
  ⟨Γ, hΓ⟩

end Families

/-! ## 10. `bprop:U_timelike` (Prop 10.4), `bprop:LU_discrete` (Prop 10.5) -/

section UTimelike

variable {Γ : Subgroup (isom d)} {S : Set (Minkowski d)}


/-- A nonzero null vector spans the null direction of a point of `𝒮`. -/
theorem exists_nullVec_eq_smul {e : Minkowski d} (he0 : e ≠ 0) (he : minkQ e = 0) :
    ∃ (u : PenroseSphere d) (c : ℝ), c ≠ 0 ∧ nullVec u = c • e := by
  have he1 : e.1 ≠ 0 := fun h0 => he0 (eq_zero_of_fst_eq_zero h0 he.le)
  have hnorm : ‖e.2‖ = |e.1| := by
    have h2 : ‖e.2‖ ^ 2 = |e.1| ^ 2 := by
      have := he; simp only [minkQ] at this; rw [sq_abs]; linarith
    exact (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).1 h2
  refine ⟨⟨e.1⁻¹ • e.2, by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, Real.norm_eq_abs, hnorm,
      inv_mul_cancel₀ (abs_ne_zero.2 he1)]⟩, e.1⁻¹, inv_ne_zero he1, ?_⟩
  refine Prod.ext ?_ rfl
  simp [nullVec, inv_mul_cancel₀ he1]

/-- **Prop 10.4, the lightlike case** (l.3352–3353): a `Γ`-invariant affine subspace whose direction
contains a nonzero null vector and no timelike one has a unique isotropic direction, which `L(Γ)`
preserves: `Γ` is elementary. -/
theorem not_isNonelementary_of_lightlike {U : AffineSubspace ℝ (Minkowski d)}
    (hUne : (U : Set (Minkowski d)).Nonempty)
    (hinv : ∀ γ ∈ Γ, ∀ x : Minkowski d, γ • x ∈ U ↔ x ∈ U) {v₀ : Minkowski d}
    (hv₀ : v₀ ∈ U.direction) (hv0 : v₀ ≠ 0) (hq : minkQ v₀ = 0) (hnt : ¬IsTimelikeSubspace U) :
    ¬IsNonelementary Γ := by
  obtain ⟨p, hp⟩ := hUne
  -- every null vector of the direction is a multiple of `v₀`
  have huniq : ∀ w ∈ U.direction, minkQ w = 0 → ∃ c : ℝ, w = c • v₀ := by
    intro w hw hwq
    refine eq_smul_of_null_orth hq hv0 hwq ?_
    by_contra hB
    set B := minkB v₀ w
    have ht : minkQ (v₀ + (-B) • w) < 0 := by
      rw [minkQ_add, minkQ_smul, hwq, hq, minkB_smul_right]
      nlinarith [sq_pos_of_ne_zero hB]
    exact hnt ⟨_, U.direction.add_mem hv₀ (U.direction.smul_mem _ hw), ht⟩
  -- `L(γ)` preserves the direction
  have hdir : ∀ γ ∈ Γ, ∀ w ∈ U.direction, linOf γ w ∈ U.direction := by
    intro γ hγ w hw
    obtain ⟨p₂, hp₂, rfl⟩ := (AffineSubspace.mem_direction_iff_eq_vsub_right hp w).1 hw
    rw [vsub_eq_sub, ← smul_sub_smul, ← vsub_eq_sub]
    exact AffineSubspace.vsub_mem_direction ((hinv γ hγ p₂).2 hp₂) ((hinv γ hγ p).2 hp)
  obtain ⟨u, c, hc0, hu⟩ := exists_nullVec_eq_smul hv0 hq
  intro hne
  refine hne (linearImage Γ) le_rfl (by rw [Subgroup.relIndex_self]; exact one_ne_zero) ⟨u, ?_⟩
  rintro _ ⟨γ, hγ, rfl⟩
  obtain ⟨a, ha⟩ := huniq _ (hdir γ hγ v₀ hv₀)
    (by rw [lorentz.minkQ_apply (linOf_mem γ), hq])
  refine lorentzSphere_eq_of_eigen (c := a) ?_
  rw [← linOf_eq_linearPart, hu, map_smul, ha, smul_comm]

/-- **The maximal unipotent subspace contains every vector fixed by `L(N)`** (the step of
l.3360–3362, "`v₀` … has to belong to `U`", for any fixed vector): if `L(γ) v = v` for all `γ ∈ N`,
then `U + ℝv` is again `N`-invariant and unipotent, so it is `U` by maximality. The isom analogue of
`Flat.Bieberbach`'s `mem_direction_of_fixed`. -/
theorem IsMaxUnipotent.mem_direction_of_linFixed {N : Subgroup (isom d)}
    {U : AffineSubspace ℝ (Minkowski d)} (hmax : IsMaxUnipotent N U)
    (hUne : (U : Set (Minkowski d)).Nonempty) {v : Minkowski d}
    (hv : ∀ γ ∈ N, linOf γ v = v) : v ∈ U.direction := by
  obtain ⟨p, hp⟩ := hUne
  set D := U.direction ⊔ Submodule.span ℝ {v}
  have hdir : ∀ γ ∈ N, ∀ w ∈ U.direction, linOf γ w ∈ U.direction := by
    intro γ hγ w hw
    obtain ⟨p₂, hp₂, rfl⟩ := (AffineSubspace.mem_direction_iff_eq_vsub_right hp w).1 hw
    rw [vsub_eq_sub, ← smul_sub_smul, ← vsub_eq_sub]
    exact AffineSubspace.vsub_mem_direction ((hmax.1.1 γ hγ p₂).2 hp₂) ((hmax.1.1 γ hγ p).2 hp)
  have hD : ∀ γ ∈ N, ∀ w ∈ D, linOf γ w ∈ D := by
    intro γ hγ w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hb
    rw [map_add, map_smul, hv γ hγ]
    exact Submodule.add_mem_sup (hdir γ hγ a ha)
      (Submodule.smul_mem _ t (Submodule.mem_span_singleton_self v))
  have hfwd : ∀ γ ∈ N, ∀ x, x ∈ AffineSubspace.mk' p D → γ • x ∈ AffineSubspace.mk' p D := by
    intro γ hγ x hx
    rw [AffineSubspace.mem_mk'] at hx ⊢
    have hγp : γ • p -ᵥ p ∈ U.direction :=
      AffineSubspace.vsub_mem_direction ((hmax.1.1 γ hγ p).2 hp) hp
    have : γ • x -ᵥ p = linOf γ (x -ᵥ p) + (γ • p -ᵥ p) := by
      simp only [vsub_eq_sub]; rw [← smul_sub_smul]; abel
    rw [this]
    exact D.add_mem (hD γ hγ _ hx) (Submodule.mem_sup_left hγp)
  have hinv : IsUnipotentInvariant N (AffineSubspace.mk' p D) := by
    refine ⟨fun γ hγ x => ⟨fun hx => ?_, hfwd γ hγ x⟩, fun γ hγ => ?_⟩
    · have := hfwd γ⁻¹ (N.inv_mem hγ) _ hx
      rwa [inv_smul_smul] at this
    · obtain ⟨m, hm⟩ := hmax.1.2 γ hγ
      refine ⟨m + 1, fun w hw => ?_⟩
      rw [AffineSubspace.direction_mk'] at hw
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hw
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hb
      have h1 : pOf (linOf γ) v = 0 := by rw [pOf_apply, hv γ hγ, sub_self]
      have e1 : (pOf (linOf γ) ^ (m + 1)) a = 0 := by
        rw [pow_succ', Module.End.mul_apply, hm a ha, map_zero]
      have e2 : (pOf (linOf γ) ^ (m + 1)) v = 0 := by
        rw [pow_succ, Module.End.mul_apply, h1, map_zero]
      rw [map_add, map_smul, e1, e2, smul_zero, add_zero]
  have hle : U ≤ AffineSubspace.mk' p D := by
    intro x hx
    rw [AffineSubspace.mem_mk']
    exact Submodule.mem_sup_left (AffineSubspace.vsub_mem_direction hx hp)
  have heq := hmax.2 _ hinv hle
  have : v ∈ (AffineSubspace.mk' p D).direction := by
    rw [AffineSubspace.direction_mk']
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)
  rwa [heq] at this

/-- `bprop:U_timelike` (Prop 10.4, l.3346–3362): in the nonelementary case, the maximal
`Γ_nd`-unipotent affine subspace `U` (`bthm:ausl`, `bthm:unip`) is timelike. Its nonemptiness and
`Γ`-invariance ("being unique", l.3343–3344) are derived from the uniqueness in `bthm:unip`
(`exists_invariant_maxUnipotent`), not assumed. -/
theorem bprop_U_timelike (hA : AuslanderCarriereDalbo d) (hU : MaxUnipotentSubspace d)
    (hΓ : DiscreteTopology Γ) (h : CCAction Γ S) (hne : IsNonelementary Γ)
    {U : AffineSubspace ℝ (Minkowski d)} (hmax : IsMaxUnipotent (nonDiscretePart Γ) U) :
    IsTimelikeSubspace U := by
  -- `CCAction` (`h`, §8's standing hypothesis, kept in the statement) is not used by this proof
  -- (finding): the spacelike case goes through the nilpotency of `L(Γ_nd)`
  -- (`Flat.Lox.NilpotentFix`) and `hne` alone, not through Cor 8.4
  have _ := h
  -- "Being unique, `U` is also preserved by `Γ`" (l.3343–3344)
  obtain ⟨U₀, hUne, hmax₀, hinv⟩ := exists_invariant_maxUnipotent hA hU hΓ
  obtain ⟨U₁, -, -, huniq⟩ := hU _ (hA Γ hΓ).2
  obtain rfl : U = U₀ := (huniq U hmax).trans (huniq U₀ hmax₀).symm
  by_contra hnt
  by_cases hnull : ∃ v ∈ U.direction, v ≠ 0 ∧ minkQ v = 0
  · obtain ⟨v, hv, hv0, hq⟩ := hnull
    exact not_isNonelementary_of_lightlike hUne hinv hv hv0 hq hnt hne
  -- The spacelike case: every vector fixed by `L(Γ_nd)` lies in `U`'s direction
  -- (`IsMaxUnipotent.mem_direction_of_linFixed`), so the common fixed space of `L(Γ_nd)` is
  -- spacelike: `L(Γ_nd)` fixes no timelike and no nonzero null vector.
  have hfixsp : ∀ v : Minkowski d, (∀ γ ∈ nonDiscretePart Γ, linOf γ v = v) → v ≠ 0 →
      0 < minkQ v := by
    intro v hv hv0
    have hvU := hmax.mem_direction_of_linFixed hUne hv
    by_contra hle
    rcases (not_lt.1 hle).lt_or_eq with hlt | heq
    · exact hnt ⟨v, hvU, hlt⟩
    · exact hnull ⟨v, hvU, hv0, heq⟩
  -- The spacelike step (`Flat.Lox.NilpotentFix`, in place of Cor 8.4, which is false as printed):
  -- `L(Γ_nd)` is nilpotent (`bthm:ausl`) and normalised by `L(Γ)` (`conj_mem_nonDiscretePart`),
  -- and its nonzero common fixed vectors are spacelike (`hfixsp`), so a finite-index subgroup of
  -- `L(Γ)` fixes a point of `𝒮` (induction along the upper central series of `L(Γ_nd)`:
  -- `Lox.exists_fixed_timelike_of_commuteOn` in the all-elliptic step,
  -- `Lox.exists_finiteIndex_fix_of_commuteOn_nonElliptic` otherwise), against `hne`. This
  -- subsumes the former branch "a central non-elliptic member" (`Flat.Lox.CentralFix`).
  have hnil : Group.IsNilpotent (linearImage (nonDiscretePart Γ)) := by
    haveI := (hA Γ hΓ).2
    have e : (linearPart.comp (nonDiscretePart Γ).subtype).range =
        linearImage (nonDiscretePart Γ) := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← e]
    exact Group.nilpotent_of_surjective _ (MonoidHom.rangeRestrict_surjective _)
  have hnorm : ∀ A ∈ linearImage Γ, ∀ B ∈ linearImage (nonDiscretePart Γ),
      A * B * A⁻¹ ∈ linearImage (nonDiscretePart Γ) := by
    rintro _ ⟨γ, hγ, rfl⟩ _ ⟨η, hη, rfl⟩
    exact ⟨γ * η * γ⁻¹, conj_mem_nonDiscretePart hγ hη, by simp only [map_mul, map_inv]⟩
  obtain ⟨H, hH, hidx, u, hu⟩ := Lox.exists_finiteIndex_fix_of_nilpotent_normal hnorm hnil
    fun v hv hv0 => hfixsp v (fun γ hγ => hv _ ⟨γ, hγ, rfl⟩) hv0
  exact hne H hH hidx ⟨u, hu⟩

/-- `L(γ⁻¹) L(γ) = id`. -/
theorem linOf_inv_apply_linOf (g : isom d) (v : Minkowski d) : linOf g⁻¹ (linOf g v) = v := by
  calc linOf g⁻¹ (linOf g v) = linOf (g⁻¹ * g) v := rfl
    _ = v := by rw [inv_mul_cancel]; rfl

theorem linToCLM_linOf_mul (g h : isom d) :
    linToCLM (linOf (g * h)) = linToCLM (linOf g) * linToCLM (linOf h) :=
  ContinuousLinearMap.ext fun _ => rfl

/-- **A subgroup of `SO₀(1, d)` is discrete as soon as a ball around `1` meets it only in `1`.** -/
theorem discreteTopology_of_dist_lt {H : Subgroup (lorentz d)} {ε : ℝ} (hε : 0 < ε)
    (h : ∀ A ∈ H, dist (linToCLM (A : Minkowski d ≃ₗ[ℝ] Minkowski d)) 1 < ε → A = 1) :
    DiscreteTopology H := by
  haveI := Lox.lorentz_isTopologicalGroup (d := d)
  rw [discreteTopology_iff_isOpen_singleton_one]
  have e : ({1} : Set H) = (fun A : H => linToCLM ((A : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d)) ⁻¹'
      Metric.ball 1 ε := by
    ext A
    simp only [mem_singleton_iff, mem_preimage, Metric.mem_ball]
    constructor
    · rintro rfl
      show dist (linToCLM (1 : Minkowski d ≃ₗ[ℝ] Minkowski d)) 1 < ε
      rw [linToCLM_one, dist_self]; exact hε
    · intro hA; exact Subtype.ext (h _ A.2 hA)
  rw [e]
  exact (continuous_lorentz_linToCLM.comp continuous_subtype_val).isOpen_preimage _ Metric.isOpen_ball

/-- **Prop 10.5, the branch `L_U(Γ_nd) = {1}`** (l.3372–3376): if the restrictions to `U` of the
elements of `Γ_nd` all have trivial linear part, `L_U(Γ)` is discrete. Not through the closure of
`L_U(Γ)` (l.3372–3374) but directly: by Cartan's theorem in its local form
(`Lox.exists_nhds_subset_connectedComponentIn_closure`) an element of `Γ` whose linear part is
close to `1` lies in `Γ_nd`, hence restricts with trivial linear part; and a sequence `hₖ → 1` of
`L_U(Γ)`, `hₖ ≠ 1`, lifts to `γₖ ∈ Γ` whose linear parts are bounded together with their inverses
(they move the unit timelike vector of `U` boundedly, `norm_linOf_le_of_gauss`: the action on
`U^⊥` is euclidean), so a subsequence is Cauchy and `γ_{φN}⁻¹ γ_{φn}` restricts trivially for
`n ≥ N`: `hₖ` is eventually constant, hence `1`. No `RestrictsIn` is needed. -/
theorem discreteTopology_restrictGroup_of_nonDiscretePart_bot {Γ : Subgroup (isom d)} {d₁ : ℕ}
    (ι : AffineMinkEmbedding d₁ d)
    (hnt : linearImage (ι.restrictGroup (nonDiscretePart Γ)) = ⊥) :
    DiscreteTopology (linearImage (ι.restrictGroup Γ)) := by
  -- Cartan (`Lox.exists_nhds_subset_connectedComponentIn_closure`): near `1`, `cl L(Γ) ⊆ G₀`
  obtain ⟨V, hV, hVsub⟩ := Lox.exists_nhds_subset_connectedComponentIn_closure (linearImage Γ)
  obtain ⟨δ, hδ, hδV⟩ : ∃ δ > 0, ∀ A : lorentz d,
      dist (linToCLM (A : Minkowski d ≃ₗ[ℝ] Minkowski d)) 1 < δ → A ∈ V := by
    rw [isEmbedding_lorentz_linToCLM.isInducing.nhds_eq_comap, Filter.mem_comap] at hV
    obtain ⟨t, ht, htV⟩ := hV
    have ht' : t ∈ 𝓝 (1 : Minkowski d →L[ℝ] Minkowski d) := by
      simpa [linToCLM_one] using ht
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 ht'
    exact ⟨δ, hδ, fun A hA => htV (hball hA)⟩
  -- an element of `Γ` whose linear part is `δ`-close to `1` lies in `Γ_nd`: it restricts trivially
  have hkill : ∀ γ ∈ Γ, dist (linToCLM (linOf γ)) 1 < δ → ∀ g : isom d₁, ι.Restricts γ g →
      linearPart g = 1 := by
    intro γ hγ hd g hg
    have hV' : linearPart γ ∈ V := hδV _ (by rwa [← linOf_eq_linearPart])
    have hcl : linearPart γ ∈ closure (linearImage Γ : Set (lorentz d)) :=
      subset_closure ⟨γ, hγ, rfl⟩
    have hG : linearPart γ ∈ linClosureIdentityComponent Γ := hVsub ⟨hV', hcl⟩
    have hnd : γ ∈ nonDiscretePart Γ := Subgroup.mem_inf.2 ⟨hγ, Subgroup.subset_closure hG⟩
    have : linearPart g ∈ linearImage (ι.restrictGroup (nonDiscretePart Γ)) :=
      ⟨g, ⟨γ, hnd, hg⟩, rfl⟩
    rw [hnt] at this
    exact Subgroup.mem_bot.1 this
  -- the unit timelike vector of `U`, made future
  set t₁ : Minkowski d₁ := (1, 0)
  obtain ⟨n₀, σ, hσ, hn₀, hn₀q, hn₀e⟩ : ∃ (n₀ : Minkowski d) (σ : ℝ), |σ| = 1 ∧
      IsFutureTimelike n₀ ∧ minkQ n₀ = -1 ∧ n₀ = σ • ι.lin t₁ := by
    have hq := ι.minkQ_lin_timeVec
    rcases isFutureTimelike_or_neg (v := ι.lin t₁) (by rw [hq]; norm_num) with h | h
    · exact ⟨_, 1, by simp, h, hq, by rw [one_smul]⟩
    · exact ⟨_, -1, by simp, h, by rw [minkQ_neg, hq], by rw [neg_one_smul]⟩
  set Cι := ‖LinearMap.toContinuousLinearMap ι.lin‖
  set R := max ‖n₀‖ (Cι * 2 * ‖t₁‖)
  set c := 2 * R ^ 2 * (8 * R ^ 2 + 1) + 1
  have hc1 : 1 ≤ c := by have : 0 ≤ 2 * R ^ 2 * (8 * R ^ 2 + 1) := by positivity
                         linarith
  have hc0 : 0 < c := by linarith
  -- an element of `Γ` restricting to `g` with `L(g)` `1`-close to `1` has `‖L(γ)^{±1}‖ ≤ c`
  have hbound : ∀ γ : isom d, ∀ g : isom d₁, ι.Restricts γ g → dist (linToCLM (linOf g)) 1 < 1 →
      ‖linToCLM (linOf γ)‖ ≤ c ∧ ‖linToCLM (linOf γ⁻¹)‖ ≤ c := by
    intro γ g hg hd
    have hLg : ‖linToCLM (linOf g)‖ ≤ 2 := by
      have h1 : ‖(1 : Minkowski d₁ →L[ℝ] Minkowski d₁)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
      rw [dist_eq_norm] at hd
      linarith [norm_sub_norm_le (linToCLM (linOf g)) 1]
    have hn : linOf γ n₀ = σ • ι.lin (linOf g t₁) := by
      rw [hn₀e, map_smul, hg.lin]
    have hnR : ‖linOf γ n₀‖ ≤ R := by
      rw [hn, norm_smul, Real.norm_eq_abs, hσ, one_mul]
      refine le_trans ?_ (le_max_right _ _)
      calc ‖ι.lin (linOf g t₁)‖ = ‖LinearMap.toContinuousLinearMap ι.lin (linOf g t₁)‖ := rfl
        _ ≤ Cι * ‖linOf g t₁‖ := ContinuousLinearMap.le_opNorm _ _
        _ = Cι * ‖linToCLM (linOf g) t₁‖ := rfl
        _ ≤ Cι * (‖linToCLM (linOf g)‖ * ‖t₁‖) := by
          gcongr; exact ContinuousLinearMap.le_opNorm _ _
        _ ≤ Cι * (2 * ‖t₁‖) := by gcongr
        _ = Cι * 2 * ‖t₁‖ := by ring
    have hn0R : ‖n₀‖ ≤ R := le_max_left _ _
    refine ⟨ContinuousLinearMap.opNorm_le_bound _ hc0.le fun x =>
      norm_linOf_le_of_gauss hn₀ hn₀q hn0R hnR x, ?_⟩
    have hn' : IsFutureTimelike (linOf γ n₀) := lorentz.isFutureTimelike_apply (linOf_mem γ) hn₀
    have hq' : minkQ (linOf γ n₀) = -1 := by rw [lorentz.minkQ_apply (linOf_mem γ), hn₀q]
    refine ContinuousLinearMap.opNorm_le_bound _ hc0.le fun x =>
      norm_linOf_le_of_gauss (g := γ⁻¹) hn' hq' hnR (by rw [linOf_inv_apply_linOf]; exact hn0R) x
  -- non-discreteness gives `hₖ ∈ L_U(Γ)`, `hₖ ≠ 1`, `hₖ → 1`
  by_contra hnd
  have hcon : ∀ ε > 0, ∃ A ∈ linearImage (ι.restrictGroup Γ),
      dist (linToCLM (A : Minkowski d₁ ≃ₗ[ℝ] Minkowski d₁)) 1 < ε ∧ A ≠ 1 := by
    intro ε hε
    by_contra hc
    push Not at hc
    exact hnd (discreteTopology_of_dist_lt hε hc)
  choose h hH hhd hhne using fun k : ℕ => hcon (1 / ((k : ℝ) + 2)) (by positivity)
  choose g hg hgh using fun k => Subgroup.mem_map.1 (hH k)
  choose γ hγ hγg using fun k => (hg k)
  have hψh : ∀ k, linToCLM ((h k : lorentz d₁) : Minkowski d₁ ≃ₗ[ℝ] Minkowski d₁) =
      linToCLM (linOf (g k)) := fun k => by rw [← hgh k, linOf_eq_linearPart]
  have hk1 : ∀ k, dist (linToCLM (linOf (g k))) 1 < 1 := fun k => by
    rw [← hψh]
    refine (hhd k).trans_le ?_
    rw [div_le_one (by positivity)]; linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
  set a : ℕ → Minkowski d →L[ℝ] Minkowski d := fun k => linToCLM (linOf (γ k))
  have ha : ∀ k, a k ∈ Metric.closedBall 0 c := fun k =>
    mem_closedBall_zero_iff.2 (hbound _ _ (hγg k) (hk1 k)).1
  haveI : ProperSpace (Minkowski d →L[ℝ] Minkowski d) :=
    FiniteDimensional.proper ℝ (Minkowski d →L[ℝ] Minkowski d)
  obtain ⟨T, -, φ, hφ, hT⟩ := (isCompact_closedBall (0 : Minkowski d →L[ℝ] Minkowski d) c).tendsto_subseq ha
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 hT.cauchySeq (δ / c) (div_pos hδ hc0)
  -- for `n ≥ N`, `γ_{φN}⁻¹ γ_{φn}` has linear part `δ`-close to `1`, so `h_{φN} = h_{φn}`
  have hconst : ∀ n ≥ N, h (φ n) = h (φ N) := by
    intro n hn
    set γ' := (γ (φ N))⁻¹ * γ (φ n)
    have hγ' : γ' ∈ Γ := Γ.mul_mem (Γ.inv_mem (hγ _)) (hγ _)
    have hinv1 : linToCLM (linOf (γ (φ N))⁻¹) * a (φ N) = 1 :=
      ContinuousLinearMap.ext fun v => linOf_inv_apply_linOf _ v
    have hdist : dist (linToCLM (linOf γ')) 1 < δ := by
      rw [dist_eq_norm, linToCLM_linOf_mul]
      have e : linToCLM (linOf (γ (φ N))⁻¹) * linToCLM (linOf (γ (φ n))) - 1 =
          linToCLM (linOf (γ (φ N))⁻¹) * (a (φ n) - a (φ N)) := by
        rw [mul_sub, hinv1]
      rw [e]
      calc ‖linToCLM (linOf (γ (φ N))⁻¹) * (a (φ n) - a (φ N))‖
          ≤ ‖linToCLM (linOf (γ (φ N))⁻¹)‖ * ‖a (φ n) - a (φ N)‖ := norm_mul_le _ _
        _ ≤ c * ‖a (φ n) - a (φ N)‖ := by
          gcongr; exact (hbound _ _ (hγg _) (hk1 _)).2
        _ < c * (δ / c) := by
          gcongr; rw [← dist_eq_norm]; exact hN n hn
        _ = δ := by field_simp
    have h1 := hkill γ' hγ' hdist _ ((hγg (φ N)).inv.mul (hγg (φ n)))
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    rw [← hgh, ← hgh, h1]
  -- `h_{φn} → 1`, so the constant `h_{φN}` is `1`
  have hlim : Tendsto (fun n => linToCLM ((h (φ n) : lorentz d₁) : Minkowski d₁ ≃ₗ[ℝ] Minkowski d₁))
      atTop (𝓝 1) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun _ => dist_nonneg) (fun n => (hhd (φ n)).le.trans ?_)
      (tendsto_one_div_add_atTop_nhds_zero_nat)
    have := hφ.id_le n
    gcongr
    · exact_mod_cast this
    · norm_num
  have hlim' : Tendsto (fun n => linToCLM ((h (φ n) : lorentz d₁) : Minkowski d₁ ≃ₗ[ℝ] Minkowski d₁))
      atTop (𝓝 (linToCLM ((h (φ N) : lorentz d₁) : Minkowski d₁ ≃ₗ[ℝ] Minkowski d₁))) :=
    tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun n hn => by
      show _ = linToCLM ((h (φ n) : lorentz d₁) : Minkowski d₁ ≃ₗ[ℝ] Minkowski d₁)
      rw [hconst n hn]⟩)
  have e1 := tendsto_nhds_unique hlim' hlim
  refine hhne (φ N) (Subtype.ext ?_)
  rw [← linToCLM_one] at e1
  exact linToCLM_injective e1

/-- `bprop:LU_discrete` (Prop 10.5, l.3367–3388): `L_U(Γ)`, the linear parts of the restrictions
of `Γ` to the (timelike, Prop 10.4) maximal unipotent subspace `U`, is discrete. `U` is given through
a parametrization `ι : 𝐌^{d₁+1} → 𝐌ⁿ` on which every element of `Γ` restricts to an isometry
(`RestrictsIn`, as in `Flat.TwistedProduct`), and `L_U(Γ)` is the linear image of the restricted
group. -/
theorem bprop_LU_discrete (hA : AuslanderCarriereDalbo d) (hU : MaxUnipotentSubspace d)
    (hΓ : DiscreteTopology Γ) (h : CCAction Γ S) (hne : IsNonelementary Γ)
    {d₁ : ℕ} (ι : AffineMinkEmbedding d₁ d) (hmax : IsMaxUnipotent (nonDiscretePart Γ) ι.range)
    (hres : ι.RestrictsIn Γ) : DiscreteTopology (linearImage (ι.restrictGroup Γ)) := by
  -- `MaxUnipotentSubspace` (`hU`) and `CCAction` (`h`, §8's standing hypothesis) are not used by
  -- this proof (finding): `hmax` is used as given, and the branch `L_U(Γ_nd) = {1}` needs no
  -- hypothesis on `Γ` at all (`discreteTopology_restrictGroup_of_nonDiscretePart_bot`)
  have _ := hU
  have _ := h
  by_contra hnd
  -- the Lie-theoretic input (l.3372–3380): a subgroup `N ≤ SO₀(U)` normalised by `L_U(Γ)` with a
  -- central parabolic or hyperbolic member. On the branch `L_U(Γ_nd) ≠ {1}` it is `N = L_U(Γ_nd)`
  -- itself (`Flat.Lox.UnipotentCentre`: nilpotent by `bthm:ausl`, unipotent by `bthm:unip`,
  -- normal in `L_U(Γ)`, so its centre has a parabolic member).
  obtain ⟨N, hnorm, z, hz, hzc, hzne⟩ : ∃ N : Subgroup (lorentz d₁),
      (∀ A ∈ linearImage (ι.restrictGroup Γ), ∀ B ∈ N, A * B * A⁻¹ ∈ N) ∧
      ∃ z ∈ N, (∀ B ∈ N, B * z = z * B) ∧
        ¬IsElliptic (z : Minkowski d₁ ≃ₗ[ℝ] Minkowski d₁) := by
    by_cases hnt : linearImage (ι.restrictGroup (nonDiscretePart Γ)) = ⊥
    · exfalso
      exact hnd (discreteTopology_restrictGroup_of_nonDiscretePart_bot ι hnt)
    · exact Lox.exists_normal_central_nonElliptic_restrict hA hΓ ι hmax hres hnt
  -- l.3380–3388: `L_U(Γ)` permutes the fixed points of `z` on `𝒮(U)`; the transport to `𝐌ⁿ`
  obtain ⟨H, hH, hidx, u₁, hu₁⟩ :=
    Lox.exists_finiteIndex_fix_of_central_nonElliptic hnorm hz hzc hzne
  obtain ⟨H', hH', hidx', u, hu⟩ := Lox.exists_finiteIndex_fix_of_restrictGroup ι hres hH hidx hu₁
  exact hne H' hH' hidx' ⟨u, hu⟩

end UTimelike

/-! ## 11. [10.G] The nonelementary case -/

section Generic

variable {Γ : Subgroup (isom d)} {S : Set (Minkowski d)}

/-- **[10.G], l.3398–3403: `Ω(S̃)` is Def 4.18's regular domain `Ω^±(Λ(ρ))`** — `blem_loxregular`
restated: the domain of the Cauchy-hyperbolic spacetime of `Γ` (when `Γ` is admissible). -/
theorem generic_omegaS_eq (h : CCAction Γ S) (hlox : ∃ γ ∈ Γ, IsLoxodromic (linOf γ)) :
    (omegaSOpens Γ S = limitOpensPlus Γ ∧ FutureRegular (limitSetJ Γ)) ∨
      (omegaSOpens Γ S = limitOpensMinus Γ ∧ PastRegular (limitSetJ Γ)) := by
  rcases blem_loxregular h hlox with ⟨hF, he⟩ | ⟨hP, he⟩
  · exact Or.inl ⟨Opens.ext he, hF⟩
  · exact Or.inr ⟨Opens.ext he, hP⟩

/-- **[10.G], l.3407–3408: the elements of `𝒩 = ker L` are translations by spacelike vectors.**
A causal translation `x ↦ x + v` would send a point of `Ω(S̃)` into its own causal future,
against Prop 8.10. -/
theorem kerTranslations_spacelike (h : CCAction Γ S) {v : Minkowski d}
    (hv : v ∈ kerTranslations Γ) (hv0 : v ≠ 0) : 0 < minkQ v := by
  obtain ⟨γ, hγ, hL, rfl⟩ := hv
  have hsm : ∀ x, γ • x = x + trOf γ := fun x => by rw [smul_eq_lin_add, hL]; rfl
  have h1 : γ ≠ 1 := fun e => hv0 (by
    have := hsm 0; rw [zero_add] at this; rw [← this, e, one_smul])
  obtain ⟨x, hx⟩ := h.nonempty
  have hxΩ := subset_omegaS h hx
  have hach := (bprop_ghyp h).2.2.2.2
  by_contra hle
  rcases isFutureCausal_or_neg_of_minkQ_nonpos (not_lt.1 hle) with hc | hc
  · exact (hach γ hγ h1 x hxΩ).2 (le_top_iff_minkQ.2 (by rw [hsm, add_sub_cancel_left]; exact hc))
  · have hsm' : γ⁻¹ • x = x + -trOf γ := by
      rw [inv_smul_eq_iff, hsm]; abel
    exact (hach γ⁻¹ (Γ.inv_mem hγ) (inv_ne_one.2 h1) x hxΩ).2
      (le_top_iff_minkQ.2 (by rw [hsm', add_sub_cancel_left]; exact hc))

/-- **[10.G], l.3409: the translation vectors of `𝒩` are discrete** (finitely many in each ball),
from the proper discontinuity of `Γ` on `Σ` (`CCAction.proper`). -/
theorem kerTranslations_ballFinite (h : CCAction Γ S) (R : ℝ) :
    (kerTranslations Γ ∩ Metric.closedBall 0 R).Finite := by
  obtain ⟨x, hx⟩ := h.nonempty
  obtain ⟨f, hf, hfS⟩ := isEntireAcausalGraph_iff.1 h.cc.entire
  have hSc : IsClosed S := by rw [hfS]; exact isClosed_graph hf.lipschitzWith.continuous
  set K := S ∩ Metric.closedBall x R
  have hK : IsCompact K := (isCompact_closedBall x R).inter_left hSc
  refine ((h.proper K inter_subset_left hK).image trOf).subset ?_
  rintro v ⟨⟨γ, hγ, hL, rfl⟩, hvR⟩
  have hsm : γ • x = x + trOf γ := by rw [smul_eq_lin_add, hL]; rfl
  have hR : ‖trOf γ‖ ≤ R := by simpa using hvR
  have hxK : x ∈ K := ⟨hx, Metric.mem_closedBall_self ((norm_nonneg _).trans hR)⟩
  have hγxK : γ • x ∈ K := ⟨h.smul_mem hγ hx, by
    rw [Metric.mem_closedBall, hsm, dist_eq_norm, add_sub_cancel_left]; exact hR⟩
  exact ⟨γ, ⟨hγ, γ • x, Set.smul_mem_smul_set hxK, hγxK⟩, rfl⟩

/-- **[10.G], l.3432–3435: `Ω(S̃)` is invariant under the translations by `E = span 𝒩`** — it is
convex and invariant under the lattice `𝒩`, and a convex set invariant under `±v` is invariant
under `ℝ v`. -/
theorem omegaS_add_mem_span (h : CCAction Γ S) {v : Minkowski d}
    (hv : v ∈ Submodule.span ℝ (kerTranslations Γ)) {p : Minkowski d} (hp : p ∈ omegaS Γ S) :
    p + v ∈ omegaS Γ S := by
  have hconv := (bprop_ghyp h).2.1
  set Ω := omegaS Γ S
  -- the translations preserving `Ω` in both directions form a submodule
  let T : Submodule ℝ (Minkowski d) :=
    { carrier := {v | ∀ p ∈ Ω, p + v ∈ Ω ∧ p - v ∈ Ω}
      add_mem' := by
        intro a b ha hb p hp
        refine ⟨?_, ?_⟩
        · rw [← add_assoc]; exact (hb _ (ha p hp).1).1
        · rw [sub_add_eq_sub_sub]; exact (hb _ (ha p hp).2).2
      zero_mem' := fun p hp => by simpa using hp
      smul_mem' := by
        intro t a ha p hp
        have hnat : ∀ n : ℕ, ∀ q ∈ Ω, q + (n : ℝ) • a ∈ Ω ∧ q - (n : ℝ) • a ∈ Ω := by
          intro n; induction n with
          | zero => intro q hq; simpa using hq
          | succ n ih =>
            intro q hq
            obtain ⟨h1, h2⟩ := ih q hq
            push_cast
            refine ⟨?_, ?_⟩
            · rw [add_smul, one_smul, ← add_assoc]; exact (ha _ h1).1
            · rw [add_smul, one_smul, sub_add_eq_sub_sub]; exact (ha _ h2).2
        have key : ∀ s : ℝ, ∀ q ∈ Ω, q + s • a ∈ Ω := by
          intro s q hq
          obtain ⟨n, hn⟩ := exists_nat_gt |s|
          have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (abs_nonneg s) hn
          rcases le_total 0 s with hs | hs
          · have := hconv.add_smul_mem hq (hnat n q hq).1 (t := s / n)
              ⟨div_nonneg hs hn0.le, (div_le_one hn0).2 (by
                rw [abs_of_nonneg hs] at hn; exact hn.le)⟩
            rwa [smul_smul, div_mul_cancel₀ _ hn0.ne'] at this
          · have h2 : q + (n : ℝ) • (-a) ∈ Ω := by
              rw [smul_neg, ← sub_eq_add_neg]; exact (hnat n q hq).2
            have := hconv.add_smul_mem hq h2 (t := -s / n)
              ⟨div_nonneg (by linarith) hn0.le, (div_le_one hn0).2 (by
                rw [abs_of_nonpos hs] at hn; exact hn.le)⟩
            rwa [smul_smul, div_mul_cancel₀ _ hn0.ne', smul_neg, neg_smul, neg_neg] at this
        exact ⟨key t p hp, by rw [sub_eq_add_neg, ← neg_smul]; exact key (-t) p hp⟩ }
  have hsub : kerTranslations Γ ⊆ T := by
    rintro _ ⟨γ, hγ, hL, rfl⟩ q hq
    have hsm : ∀ x, γ • x = x + trOf γ := fun x => by rw [smul_eq_lin_add, hL]; rfl
    have h1 : γ • q ∈ Ω := (smul_omegaS h hγ).subset (Set.smul_mem_smul_set hq)
    have h2 : γ⁻¹ • q ∈ Ω := (smul_omegaS h (Γ.inv_mem hγ)).subset (Set.smul_mem_smul_set hq)
    refine ⟨by rw [← hsm]; exact h1, ?_⟩
    have : γ⁻¹ • q = q - trOf γ := by rw [inv_smul_eq_iff, hsm]; abel
    rw [← this]; exact h2
  exact ((Submodule.span_le.2 hsub) hv p hp).1

/-- **[10.G]: `E = span 𝒩` is spacelike.** Barbot asserts it (l.3409) without argument, and it does
not follow from the vectors of `𝒩` being spacelike (a lattice in a degenerate plane can consist of
spacelike vectors only). It follows from `blem:loxregular`: `Ω(S̃)` is invariant under `ℝ v` for
`v ∈ E` and lies on one side of every hyperplane of `Λ₀(Γ)`, so `v` is orthogonal to two distinct
null directions — impossible for a nonzero causal `v`. -/
theorem span_kerTranslations_spacelike (h : CCAction Γ S)
    (hlox : ∃ γ ∈ Γ, IsLoxodromic (linOf γ)) :
    IsSpacelikeSubmodule (Submodule.span ℝ (kerTranslations Γ)) := by
  intro v hv hv0
  obtain ⟨γ₀, hγ₀, hlox₀⟩ := hlox
  obtain ⟨w₁, hw₁, w₂, hw₂, -, -, hne⟩ := exists_two_loxRepSet hγ₀ hlox₀
  obtain ⟨x, hx⟩ := h.nonempty
  have hxΩ := subset_omegaS h hx
  have hline : ∀ t : ℝ, x + t • v ∈ omegaS Γ S := fun t =>
    omegaS_add_mem_span h (Submodule.smul_mem _ t hv) hxΩ
  -- `⟨n_w | v⟩ = 0` for `w ∈ Λ₀`
  have hkill : ∀ w ∈ loxRepSet Γ, minkB (nullVec w.1) v = 0 := by
    intro w hw
    by_contra hB
    have hbd : (∀ t : ℝ, minkB (nullVec w.1) (x + t • v) < w.2) ∨
        ∀ t : ℝ, w.2 < minkB (nullVec w.1) (x + t • v) := by
      rcases loxregular_sign h with hF | hP
      · exact Or.inl fun t => mem_halfPlus.1 (hF w hw (hline t))
      · exact Or.inr fun t => mem_halfMinus.1 (hP w hw (hline t))
    have e : ∀ t : ℝ, minkB (nullVec w.1) (x + t • v) =
        minkB (nullVec w.1) x + t * minkB (nullVec w.1) v := fun t => by
      rw [minkB_add_right, minkB_smul_right]
    set β := minkB (nullVec w.1) v
    set a := minkB (nullVec w.1) x
    have ht : a + (w.2 - a) / β * β = w.2 := by rw [div_mul_cancel₀ _ hB]; ring
    rcases hbd with hb | hb
    · have := hb ((w.2 - a) / β); rw [e, ht] at this; exact lt_irrefl _ this
    · have := hb ((w.2 - a) / β); rw [e, ht] at this; exact lt_irrefl _ this
  have h1 := hkill w₁ hw₁
  have h2 := hkill w₂ hw₂
  have key : ∀ u : Minkowski d, u ≠ 0 → IsFutureCausal u → minkB (nullVec w₁.1) u = 0 →
      minkB (nullVec w₂.1) u = 0 → False := by
    intro u hu0 hc hu1 hu2
    rcases lt_or_eq_of_le hc.2 with hq | hq
    · have := minkB_neg_of_isFutureTimelike ⟨lt_of_le_of_ne hc.1 (fun e =>
        hu0 (eq_zero_of_fst_eq_zero e.symm hc.2)), hq⟩ (isFutureCausal_nullVec w₁.1)
        (nullVec_ne_zero w₁.1)
      rw [minkB_comm] at this; linarith
    · obtain ⟨c₁, hc₁⟩ := eq_smul_of_null_orth hq hu0 (minkQ_nullVec w₁.1)
        (by rw [minkB_comm]; exact hu1)
      obtain ⟨c₂, hc₂⟩ := eq_smul_of_null_orth hq hu0 (minkQ_nullVec w₂.1)
        (by rw [minkB_comm]; exact hu2)
      have hc₂0 : c₂ ≠ 0 := fun e => nullVec_ne_zero w₂.1 (by rw [hc₂, e, zero_smul])
      exact hne (nullVec_injective_smul (c := c₁ / c₂) (by
        rw [hc₁, hc₂, smul_smul, div_mul_cancel₀ _ hc₂0]))
  by_contra hle
  rcases isFutureCausal_or_neg_of_minkQ_nonpos (not_lt.1 hle) with hc | hc
  · exact key v hv0 hc h1 h2
  · exact key (-v) (neg_ne_zero.2 hv0) hc (by rw [minkB_neg_right, h1, neg_zero])
      (by rw [minkB_neg_right, h2, neg_zero])


/-- **[10.G], l.3410–3415: conjugation acts on `𝒩` linearly**: `γ t_v γ⁻¹ = t_{L(γ) v}`, so
`L(Γ)` preserves the translation vectors of `𝒩`. -/
theorem linOf_mem_kerTranslations {γ : isom d} (hγ : γ ∈ Γ) {v : Minkowski d}
    (hv : v ∈ kerTranslations Γ) : linOf γ v ∈ kerTranslations Γ := by
  obtain ⟨t, ht, hL, rfl⟩ := hv
  have hsm : ∀ x, t • x = x + trOf t := fun x => by rw [smul_eq_lin_add, hL]; rfl
  have hη : ∀ x, (γ * t * γ⁻¹) • x = x + linOf γ (trOf t) := fun x => by
    rw [mul_smul, mul_smul, hsm, show γ⁻¹ • x + trOf t = γ⁻¹ • x + (1 : ℝ) • trOf t by
      rw [one_smul], isom_smul_add_smul, smul_inv_smul, one_smul]
  refine ⟨γ * t * γ⁻¹, Γ.mul_mem (Γ.mul_mem hγ ht) (Γ.inv_mem hγ), ?_, ?_⟩
  · rw [linOf_mul, linOf_mul, hL, mul_one, linOf_inv, mul_inv_cancel]
  · show (γ * t * γ⁻¹) • (0 : Minkowski d) = _
    rw [hη, zero_add]

/-- **[10.G], l.3410–3417: a finite-index `Γ' ≤ Γ` acts trivially on `E = span 𝒩`** — "the
finite-index subgroup on which `L(Γ)|_E` is trivial": `L(Γ)` permutes the finitely many lattice
vectors of `𝒩` below a bound fixing a basis of `E` (`Lox.exists_finiteIndex_linOf_eq_on_span`, with
`span_kerTranslations_spacelike`, `kerTranslations_ballFinite`, `linOf_mem_kerTranslations`). -/
theorem exists_finiteIndex_linOf_eq_on_span_kerTranslations (h : CCAction Γ S)
    (hlox : ∃ γ ∈ Γ, IsLoxodromic (linOf γ)) :
    ∃ Γ' : Subgroup (isom d), Γ' ≤ Γ ∧ Γ'.relIndex Γ ≠ 0 ∧
      ∀ γ ∈ Γ', ∀ v ∈ Submodule.span ℝ (kerTranslations Γ), linOf γ v = v :=
  Lox.exists_finiteIndex_linOf_eq_on_span (span_kerTranslations_spacelike h hlox)
    (kerTranslations_ballFinite h) fun _ hγ _ hv => linOf_mem_kerTranslations hγ hv

/-- **[10.G], l.3418–3419: `Λ(Γ')` = `Λ(Γ)` for a finite-index `Γ' ≤ Γ`** ("replacing `Γ` by some
finite index subgroup", which therefore does not move `Ω^±(Λ(Γ))`), from
`Lox.repJ_eq_of_relIndex_ne_zero` (`Flat.Lox.RestrictLimitSet`). -/
theorem limitSetJ_eq_of_relIndex_ne_zero {Γ Γ' : Subgroup (isom d)} (hle : Γ' ≤ Γ)
    (hidx : Γ'.relIndex Γ ≠ 0) : limitSetJ Γ' = limitSetJ Γ := by
  unfold limitSetJ
  congr 1
  exact Lox.repJ_eq_of_relIndex_ne_zero hle hidx

/-- The open form of `limitSetJ_eq_of_relIndex_ne_zero`: `Ω^±(Λ(Γ'))` = `Ω^±(Λ(Γ))`. -/
theorem limitOpens_eq_of_relIndex_ne_zero {Γ Γ' : Subgroup (isom d)} (hle : Γ' ≤ Γ)
    (hidx : Γ'.relIndex Γ ≠ 0) :
    limitOpensPlus Γ' = limitOpensPlus Γ ∧ limitOpensMinus Γ' = limitOpensMinus Γ := by
  have e := limitSetJ_eq_of_relIndex_ne_zero hle hidx
  exact ⟨Opens.ext (by simp only [limitOpensPlus, e]),
    Opens.ext (by simp only [limitOpensMinus, e])⟩

/-- **[10.G], l.3391–3403, read on the section `U`**: for an orthochronous parametrisation `ι` of
`U` on which `Γ` restricts, `ι⁻¹ Ω^±(Λ(Γ)) = Ω^±(Λ(Γ_{|U}))` — the base domain of the linear
twisted product of `blem:suspendre` is the regular domain of the restricted group, as family (b)
asks (`Lox.preimage_omega_closure_repJ`, `Flat.Lox.RestrictLimitSet`). -/
theorem preimage_omega_limitSetJ {d₁ : ℕ} (ι : AffineMinkEmbedding d₁ d) (hι : ι.Orthochronous)
    {Γ : Subgroup (isom d)} (hres : ι.RestrictsIn Γ) :
    ι ⁻¹' omegaPlus (limitSetJ Γ) = omegaPlus (limitSetJ (ι.restrictGroup Γ)) ∧
      ι ⁻¹' omegaMinus (limitSetJ Γ) = omegaMinus (limitSetJ (ι.restrictGroup Γ)) :=
  Lox.preimage_omega_closure_repJ ι hι hres

/-- **[10.G], l.3391–3396 (gap G6 for `Ω(S̃)`): `Ω^±(Λ(Γ))` is invariant under `U^⊥`** when `Γ`
restricts to `U = range ι` — the hypothesis `hperp` of `blem:suspendre`
(`TwistedProduct.suspendre`) for `Ω = Ω^±(Λ(Γ))` (`Lox.add_perp_mem_omega_of_preserves`,
`Flat.Lox.PerpInvariant`; the repulsive points of `Γ` are null eigenlines of eigenvalue
`0 < λ < 1`). -/
theorem limitOpens_add_perp {d₁ : ℕ} (ι : AffineMinkEmbedding d₁ d) {Γ : Subgroup (isom d)}
    (hres : ι.RestrictsIn Γ) :
    (∀ w ∈ ι.perp, ∀ p ∈ limitOpensPlus Γ, p + w ∈ limitOpensPlus Γ) ∧
      ∀ w ∈ ι.perp, ∀ p ∈ limitOpensMinus Γ, p + w ∈ limitOpensMinus Γ := by
  have hΛ : limitSetJ Γ ⊆ closure {w : PenroseSphere d × ℝ | ∃ γ ∈ Γ, ∃ l : ℝ, 0 < l ∧ l ≠ 1 ∧
      linOf γ (nullVec w.1) = l • nullVec w.1} :=
    closure_mono fun _ ⟨γ, hγ, _, l, hl0, hl1, hn, _⟩ => ⟨γ, hγ, l, hl0, hl1.ne, hn⟩
  exact ⟨fun w hw p hp =>
      (Lox.add_perp_mem_omega_of_preserves ι hres.preserves hΛ hw).1 p hp,
    fun w hw p hp => (Lox.add_perp_mem_omega_of_preserves ι hres.preserves hΛ hw).2 p hp⟩

/-- **[10.G], l.3406–3417 and l.3432–3435, without `CCAction`**: for any `Γ` with a loxodromic
element acting properly on an open convex nonempty `Γ`-invariant `Ω` on one side of `Λ(Γ)`, the
translation vectors `𝒩` of `ker L ∩ Γ` span a spacelike `E`, are discrete, and `Ω + E = Ω` — the
`𝒩`-conjuncts of family (b) (`IsCHCentralExtensionOf`) for a group with no `CCAction`, such as
the restricted `Γ_{|U}` on `ι⁻¹ Ω(S̃)` (`Lox.kerTranslations_lattice_of_oneSided`,
`Flat.Lox.RegularLattice`). -/
theorem kerTranslations_lattice_of_limitSetJ {Γ : Subgroup (isom d)} {Ω : Set (Minkowski d)}
    (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω) (hΩn : Ω.Nonempty)
    (hinv : ∀ γ ∈ Γ, ∀ p ∈ Ω, γ • p ∈ Ω)
    (hprop : ∀ K ⊆ Ω, IsCompact K → {γ : isom d | γ ∈ Γ ∧ (γ • K ∩ K).Nonempty}.Finite)
    (hside : Ω ⊆ omegaPlus (limitSetJ Γ) ∨ Ω ⊆ omegaMinus (limitSetJ Γ))
    (hlox : ∃ γ ∈ Γ, IsLoxodromic (linOf γ)) :
    IsSpacelikeSubmodule (Submodule.span ℝ (kerTranslations Γ)) ∧
      (∀ R : ℝ, (kerTranslations Γ ∩ Metric.closedBall 0 R).Finite) ∧
      ∀ v ∈ Submodule.span ℝ (kerTranslations Γ), ∀ p ∈ Ω, p + v ∈ Ω := by
  obtain ⟨γ₀, hγ₀, hlox₀⟩ := hlox
  obtain ⟨w₁, hw₁, w₂, hw₂, -, -, hne⟩ := exists_two_loxRepSet hγ₀ hlox₀
  exact Lox.kerTranslations_lattice_of_oneSided hΩo hΩc hΩn hinv hprop hside
    ⟨w₁, loxRepSet_subset_limitSetJ Γ hw₁, w₂, loxRepSet_subset_limitSetJ Γ hw₂, hne⟩

/-- **[10.M], l.3250–3257 (`b ≡ 0`) under `CCAction`**: a subgroup `Γ₁ ≤ Γ` fixing `u₀ ∈ 𝒮` and
containing a loxodromic element preserves a lightlike level `{⟨(1,u₀) | ·⟩ = s₀}`
(`Lox.exists_invariant_nullLevel`, `Flat.Lox.NullLevelFix`; the one-sidedness of `Ω(S̃)` is
`loxregular_sign`). -/
theorem exists_invariant_nullLevel_of_ccAction (h : CCAction Γ S) {Γ₁ : Subgroup (isom d)}
    (hle : Γ₁ ≤ Γ) {u₀ : PenroseSphere d}
    (hfix : ∀ γ ∈ Γ₁, lorentzSphere (linearPart γ) u₀ = u₀)
    (hlox : ∃ γ ∈ Γ₁, IsLoxodromic (linOf γ)) :
    ∃ s₀ : ℝ, ∀ γ ∈ Γ₁, ∀ p : Minkowski d,
      minkB (nullVec u₀) p = s₀ → minkB (nullVec u₀) (γ • p) = s₀ := by
  obtain ⟨x, hx⟩ := h.nonempty
  refine Lox.exists_invariant_nullLevel hfix hlox (Ω := omegaS Γ S) ⟨x, subset_omegaS h hx⟩ ?_
  rcases loxregular_sign h with hF | hP
  · exact Or.inl fun p hp => mem_omegaPlus.2 fun w ⟨γ, hγ, hw⟩ =>
      mem_halfPlus.1 (hF w ⟨γ, hle hγ, hw⟩ hp)
  · exact Or.inr fun p hp => mem_omegaMinus.2 fun w ⟨γ, hγ, hw⟩ =>
      mem_halfMinus.1 (hP w ⟨γ, hle hγ, hw⟩ hp)

/-- **[10.M], l.3306–3319 (`x(γ) = y(γ) = 0`) under `CCAction`**: a subgroup `Γ₁ ≤ Γ` fixing two
points `u₀, u₁` of `𝒮` and containing a loxodromic element preserves the spacelike affine subspace
`{⟨(1,u₀) | ·⟩ = s₀} ∩ {⟨(1,u₁) | ·⟩ = s₁}` (Barbot's `Γ`-invariant `π_P^{-1}(0)`):
`exists_invariant_nullLevel_of_ccAction` at `u₀` and at `u₁`. -/
theorem exists_invariant_nullLevels_of_ccAction (h : CCAction Γ S) {Γ₁ : Subgroup (isom d)}
    (hle : Γ₁ ≤ Γ) {u₀ u₁ : PenroseSphere d}
    (hfix₀ : ∀ γ ∈ Γ₁, lorentzSphere (linearPart γ) u₀ = u₀)
    (hfix₁ : ∀ γ ∈ Γ₁, lorentzSphere (linearPart γ) u₁ = u₁)
    (hlox : ∃ γ ∈ Γ₁, IsLoxodromic (linOf γ)) :
    ∃ s₀ s₁ : ℝ, ∀ γ ∈ Γ₁, ∀ p : Minkowski d,
      minkB (nullVec u₀) p = s₀ → minkB (nullVec u₁) p = s₁ →
        minkB (nullVec u₀) (γ • p) = s₀ ∧ minkB (nullVec u₁) (γ • p) = s₁ := by
  obtain ⟨s₀, hs₀⟩ := exists_invariant_nullLevel_of_ccAction h hle hfix₀ hlox
  obtain ⟨s₁, hs₁⟩ := exists_invariant_nullLevel_of_ccAction h hle hfix₁ hlox
  exact ⟨s₀, s₁, fun γ hγ p h₀ h₁ => ⟨hs₀ γ hγ p h₀, hs₁ γ hγ p h₁⟩⟩

end Generic

/-! ## 11b. [10.G] The reduction to `U` and the family (b) conclusion in `𝐌ⁿ` -/

section GenericReduction

variable {Γ : Subgroup (isom d)} {S : Set (Minkowski d)}

/-- **Nonelementary passes to finite-index subgroups**: a finite-index subgroup of `L(Γ')` has
finite index in `L(Γ)`. -/
theorem IsNonelementary.of_relIndex {Γ Γ' : Subgroup (isom d)} (hne : IsNonelementary Γ)
    (hle : Γ' ≤ Γ) (hidx : Γ'.relIndex Γ ≠ 0) : IsNonelementary Γ' := fun H hH hHi hfix =>
  hne H (hH.trans (Subgroup.map_mono hle))
    (Subgroup.relIndex_ne_zero_trans hHi (Lox.relIndex_map_ne_zero linearPart hidx)) hfix

/-- `𝒩` is monotone in the group. -/
theorem kerTranslations_subset_of_le {Γ Γ' : Subgroup (isom d)} (hle : Γ' ≤ Γ) :
    kerTranslations Γ' ⊆ kerTranslations Γ := fun _ ⟨γ, hγ, h⟩ => ⟨γ, hle hγ, h⟩

/-- **A finite-index subgroup of a group with a loxodromic element has one** (a positive power). -/
theorem exists_loxodromic_of_relIndex {Γ Γ' : Subgroup (isom d)} (hidx : Γ'.relIndex Γ ≠ 0)
    (hlox : ∃ γ ∈ Γ, IsLoxodromic (linOf γ)) : ∃ γ ∈ Γ', IsLoxodromic (linOf γ) := by
  obtain ⟨γ, hγ, hl⟩ := hlox
  obtain ⟨k, hk, -, hmem⟩ := Subgroup.exists_pow_mem_of_relIndex_ne_zero hidx hγ
  refine ⟨γ ^ k, hmem.1, ?_⟩
  have := hl.zpow_linOf (n := (k : ℤ)) (by exact_mod_cast hk.ne')
  rwa [zpow_natCast] at this

/-- **[10.G], l.3398–3403 and l.3418: `Ω(S̃) = Ω^±(Λ(Γ'))` for every finite-index `Γ' ≤ Γ`**
(`generic_omegaS_eq`, `limitOpens_eq_of_relIndex_ne_zero`). -/
theorem omegaSOpens_eq_limitOpens_of_relIndex (h : CCAction Γ S)
    (hlox : ∃ γ ∈ Γ, IsLoxodromic (linOf γ)) {Γ' : Subgroup (isom d)} (hle : Γ' ≤ Γ)
    (hidx : Γ'.relIndex Γ ≠ 0) :
    omegaSOpens Γ S = limitOpensPlus Γ' ∨ omegaSOpens Γ S = limitOpensMinus Γ' := by
  obtain ⟨e₁, e₂⟩ := limitOpens_eq_of_relIndex_ne_zero hle hidx
  rcases generic_omegaS_eq h hlox with ⟨he, -⟩ | ⟨he, -⟩
  · exact Or.inl (he.trans e₁.symm)
  · exact Or.inr (he.trans e₂.symm)

/-- **[10.G], l.3391–3396: `Ω(S̃)` is invariant under `U^⊥`** for a finite-index `Γ' ≤ Γ`
restricting to `U = range ι` (`limitOpens_add_perp` through
`omegaSOpens_eq_limitOpens_of_relIndex`). -/
theorem omegaSOpens_add_perp (h : CCAction Γ S) (hlox : ∃ γ ∈ Γ, IsLoxodromic (linOf γ))
    {d₁ : ℕ} (ι : AffineMinkEmbedding d₁ d) {Γ' : Subgroup (isom d)} (hle : Γ' ≤ Γ)
    (hidx : Γ'.relIndex Γ ≠ 0) (hres : ι.RestrictsIn Γ') :
    ∀ w ∈ ι.perp, ∀ p ∈ omegaSOpens Γ S, p + w ∈ omegaSOpens Γ S := by
  rcases omegaSOpens_eq_limitOpens_of_relIndex h hlox hle hidx with he | he <;> rw [he]
  · exact (limitOpens_add_perp ι hres).1
  · exact (limitOpens_add_perp ι hres).2

/-- **The restricted group has a loxodromic element** (the restriction of a power of a
loxodromic element of `Γ`, `Lox.Restricts.isLoxodromic`). -/
theorem exists_loxodromic_restrictGroup (hlox : ∃ γ ∈ Γ, IsLoxodromic (linOf γ))
    {d₁ : ℕ} {ι : AffineMinkEmbedding d₁ d} {Γ' : Subgroup (isom d)} (hidx : Γ'.relIndex Γ ≠ 0)
    (hres : ι.RestrictsIn Γ') : ∃ g ∈ ι.restrictGroup Γ', IsLoxodromic (linOf g) := by
  obtain ⟨γ, hγ, hl⟩ := exists_loxodromic_of_relIndex hidx hlox
  obtain ⟨g, hg⟩ := hres γ hγ
  exact ⟨g, ⟨γ, hγ, hg⟩, Lox.Restricts.isLoxodromic hg hl⟩

/-- **[10.G], l.3406–3417 and l.3432–3435, for the restricted group** `Γ'_U` acting on
`ι⁻¹ Ω(S̃)`: its translation vectors span a spacelike `E`, are discrete, and `ι⁻¹ Ω(S̃) + E =
ι⁻¹ Ω(S̃)` (`kerTranslations_lattice_of_limitSetJ`, with the restricted proper action
`Lox.proper_restrictGroup` and the base domain `preimage_omega_limitSetJ`). -/
theorem restrict_kerTranslations_lattice (h : CCAction Γ S)
    (hlox : ∃ γ ∈ Γ, IsLoxodromic (linOf γ)) {d₁ : ℕ} (ι : AffineMinkEmbedding d₁ d)
    (hι : ι.Orthochronous) {Γ' : Subgroup (isom d)} (hle : Γ' ≤ Γ) (hidx : Γ'.relIndex Γ ≠ 0)
    (hres : ι.RestrictsIn Γ') :
    IsSpacelikeSubmodule (Submodule.span ℝ (kerTranslations (ι.restrictGroup Γ'))) ∧
      (∀ R : ℝ, (kerTranslations (ι.restrictGroup Γ') ∩ Metric.closedBall 0 R).Finite) ∧
      ∀ v ∈ Submodule.span ℝ (kerTranslations (ι.restrictGroup Γ')),
        ∀ p ∈ ι ⁻¹' omegaS Γ S, p + v ∈ ι ⁻¹' omegaS Γ S := by
  have hgh := bprop_ghyp h
  have hperp := omegaSOpens_add_perp h hlox ι hle hidx hres
  obtain ⟨x, hx⟩ := h.nonempty
  have hxΩ : x ∈ omegaSOpens Γ S := subset_omegaS h hx
  have hne : (ι ⁻¹' omegaS Γ S).Nonempty :=
    ⟨ι.retract x, (ι.mem_iff_retract_mem (Ω := omegaSOpens Γ S) hperp).1 hxΩ⟩
  have hinv : ∀ g ∈ ι.restrictGroup Γ', ∀ p ∈ ι ⁻¹' omegaS Γ S, g • p ∈ ι ⁻¹' omegaS Γ S := by
    rintro g ⟨γ, hγ, hr⟩ p hp
    show ι (g • p) ∈ omegaS Γ S
    rw [hr]
    have := Set.smul_mem_smul_set (a := γ) (show ι p ∈ omegaS Γ S from hp)
    rwa [hgh.2.2.2.1 γ (hle hγ)] at this
  have hprop := Lox.proper_restrictGroup ι (Γ := Γ') (Ω := omegaS Γ S) fun K hK hKc =>
    (loxo_properlyDiscontinuous h hlox K hK hKc).subset fun γ hγ => ⟨hle hγ.1, hγ.2⟩
  have hside : ι ⁻¹' omegaS Γ S ⊆ omegaPlus (limitSetJ (ι.restrictGroup Γ')) ∨
      ι ⁻¹' omegaS Γ S ⊆ omegaMinus (limitSetJ (ι.restrictGroup Γ')) := by
    obtain ⟨e₁, e₂⟩ := preimage_omega_limitSetJ ι hι hres
    rcases omegaSOpens_eq_limitOpens_of_relIndex h hlox hle hidx with he | he
    · left
      have : omegaS Γ S = omegaPlus (limitSetJ Γ') := by
        rw [show omegaS Γ S = (omegaSOpens Γ S : Set (Minkowski d)) from rfl, he]; rfl
      rw [this, e₁]
    · right
      have : omegaS Γ S = omegaMinus (limitSetJ Γ') := by
        rw [show omegaS Γ S = (omegaSOpens Γ S : Set (Minkowski d)) from rfl, he]; rfl
      rw [this, e₂]
  exact kerTranslations_lattice_of_limitSetJ ((isOpen_omegaS Γ S).preimage ι.continuous)
    (hgh.2.1.affine_preimage ι.toAffineMap) hne hinv hprop hside
    (exists_loxodromic_restrictGroup hlox hidx hres)

/-- **[10.G], l.3339–3403: the reduction to the maximal unipotent subspace `U`** — under §8's data
in the nonelementary case, there are an orthochronous `ι : 𝐌^{d₁+1} → 𝐌ⁿ` onto the maximal
`Γ_nd`-unipotent subspace `U` (timelike, `bprop_U_timelike`) and a finite-index `Γ₂ ≤ Γ`
restricting to `U`, with `L_U(Γ₂)` discrete (`bprop_LU_discrete`, applied to `Γ₂`, whose
non-discrete part is `Γ`'s: `Lox.exists_restrictsIn_ge`, `Lox.nonDiscretePart_eq_of_le`). -/
theorem exists_generic_reduction (h : CCAction Γ S) (hne : IsNonelementary Γ)
    (hA : AuslanderCarriereDalbo d) (hU : MaxUnipotentSubspace d) :
    ∃ (d₁ : ℕ) (ι : AffineMinkEmbedding d₁ d) (Γ₂ : Subgroup (isom d)), Γ₂ ≤ Γ ∧
      Γ₂.relIndex Γ ≠ 0 ∧ ι.Orthochronous ∧ ι.RestrictsIn Γ₂ ∧
        DiscreteTopology (linearImage (ι.restrictGroup Γ₂)) := by
  have hdisc := Lox.ccAction_discreteTopology h
  obtain ⟨U, -, hmax, hinv⟩ := exists_invariant_maxUnipotent hA hU hdisc
  have hUt := bprop_U_timelike hA hU hdisc h hne hmax
  obtain ⟨d₁, ι, hι, rfl⟩ := exists_affineMinkEmbedding_of_isTimelike hUt
  have hrange : (ι.range : Set (Minkowski d)) = Set.range ι := by
    rw [AffineMinkEmbedding.range, AffineSubspace.coe_map, AffineSubspace.top_coe, image_univ]
  have hpres : ∀ γ ∈ Γ, (fun p => γ • p) '' Set.range ι = Set.range ι := by
    intro γ hγ
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      rw [← hrange] at hp ⊢
      exact (hinv γ hγ p).2 hp
    · intro hq
      refine ⟨γ⁻¹ • q, ?_, smul_inv_smul γ q⟩
      rw [← hrange] at hq ⊢
      exact (hinv γ hγ _).1 (by rwa [smul_inv_smul])
  obtain ⟨Γ₂, hle, hidx, hres, hnd⟩ := Lox.exists_restrictsIn_ge ι hpres (nonDiscretePart_le Γ)
    fun γ hγ => hmax.1.2 γ hγ
  have hmax₂ : IsMaxUnipotent (nonDiscretePart Γ₂) ι.range := by
    rw [Lox.nonDiscretePart_eq_of_le hle hidx hnd]; exact hmax
  have h₂ := Lox.ccAction_mono h hle
  exact ⟨d₁, ι, Γ₂, hle, hidx, hι, hres, bprop_LU_discrete hA hU (Lox.ccAction_discreteTopology h₂)
    h₂ (hne.of_relIndex hle hidx) ι hmax₂ hres⟩

/-- **[10.G], l.3389–3456: the conclusion, family (b), for a given finite-index `Γ'`** — if `Γ'`
lies in a subgroup `Γ₂` restricting to `U = range ι` with `L_U(Γ₂)` discrete, and `L_U(g)` is
trivial on `E = span 𝒩(Γ'_U)` for `g ∈ Γ'_U` (l.3412–3417), then `B = Γ'\Ω(S̃)` exists and is a
linear twisted product (`blem:suspendre`) over `M₁ = Γ'_U\(ι⁻¹ Ω(S̃))`, which is a central
extension over a Cauchy-hyperbolic spacetime for the group `Γ'_U`. -/
theorem generic_isCHCentralExtension (h : CCAction Γ S)
    (hlox : ∃ γ ∈ Γ, IsLoxodromic (linOf γ)) (hne : IsNonelementary Γ) {d₁ : ℕ}
    (ι : AffineMinkEmbedding d₁ d) (hι : ι.Orthochronous) {Γ₂ Γ' : Subgroup (isom d)}
    (hres : ι.RestrictsIn Γ₂) (hdisc : DiscreteTopology (linearImage (ι.restrictGroup Γ₂)))
    (hle' : Γ' ≤ Γ₂) (hle₂ : Γ₂ ≤ Γ) (hidx : Γ'.relIndex Γ ≠ 0)
    (hE : ∀ g ∈ ι.restrictGroup Γ', ∀ v ∈ Submodule.span ℝ (kerTranslations (ι.restrictGroup Γ')),
      linOf g v = v) :
    ∃ B : FlatSpacetime.{0} d, IsQuotientOf B Γ' (omegaSOpens Γ S) ∧
      ∃ M₁ : FlatSpacetime.{0} d₁, IsLTPOver B M₁ ∧ IsCHCentralExtensionOf M₁ (ι.restrictGroup Γ') := by
  have hle : Γ' ≤ Γ := hle'.trans hle₂
  have hres' : ι.RestrictsIn Γ' := Lox.restrictsIn_mono hres hle'
  have hgh := bprop_ghyp h
  set Ω := omegaSOpens Γ S with hΩ
  haveI : FlatQuotient.Invariant Γ' Ω := ⟨fun γ p hp => by
    have := Set.smul_mem_smul_set (a := (γ : isom d)) (show p ∈ omegaS Γ S from hp)
    rwa [hgh.2.2.2.1 γ (hle γ.2)] at this⟩
  haveI : IsCancelSMul Γ' Ω :=
    isCancelSMul_of_free fun γ hγ h1 x hx => loxo_free h γ (hle hγ) h1 x hx
  haveI : ProperlyDiscontinuousSMul Γ' Ω :=
    properlyDiscontinuousSMul_of_finite fun K hK hKc =>
      (loxo_properlyDiscontinuous h hlox K hK hKc).subset fun γ hγ => ⟨hle hγ.1, hγ.2⟩
  obtain ⟨x, hx⟩ := h.nonempty
  have hconn : IsConnected (Ω : Set (Minkowski d)) :=
    ⟨⟨x, subset_omegaS h hx⟩, hgh.2.1.isPreconnected⟩
  set B := FlatQuotient.toFlatSpacetime Γ' Ω hconn
  have hB : IsQuotientOf B Γ' Ω := FlatQuotient.isQuotientOf_toFlatSpacetime _ _ _
  have hperp := omegaSOpens_add_perp h hlox ι hle hidx hres'
  set M₁ := ι.baseSpacetime B hB hres' hperp
  have hM₁ : IsQuotientOf M₁ (ι.restrictGroup Γ') (ι.preimageOpens Ω) :=
    ι.isQuotientOf_baseSpacetime B hB hres' hperp
  refine ⟨B, hB, M₁, suspendre B hB ι hι hres' hperp, ?_⟩
  -- the conjuncts of family (b) for `H = Γ'_U`
  set H := ι.restrictGroup Γ' with hHdef
  obtain ⟨hsp, hfin, hEinv⟩ := restrict_kerTranslations_lattice h hlox ι hι hle hidx hres'
  obtain ⟨g₀, hg₀, hlox₀⟩ := exists_loxodromic_restrictGroup hlox hidx hres'
  have hdiscH : DiscreteTopology (linearImage H) :=
    DiscreteTopology.of_subset (s := (linearImage (ι.restrictGroup Γ₂) : Set (lorentz d₁)))
      (t := (linearImage H : Set (lorentz d₁))) hdisc
      (Subgroup.map_mono (Lox.restrictGroup_mono ι hle'))
  have hnfix : ¬HasGlobalFixedPoint (linearImage H) := by
    rintro (⟨v, hv, hfix⟩ | ⟨u, hu⟩)
    · have hv0 : v ≠ 0 := fun h0 => by rw [h0] at hv; simp [minkQ] at hv
      have hfv := hfix (linearPart g₀) ⟨g₀, hg₀, rfl⟩
      have hl : IsLoxodromic ((linearPart g₀ : lorentz d₁) : Minkowski d₁ ≃ₗ[ℝ] Minkowski d₁) := by
        rw [← linOf_eq_linearPart]; exact hlox₀
      have := minkQ_pos_of_fixed_pow_loxodromic hl one_ne_zero (by rw [pow_one]; exact hfv) hv0
      linarith
    · obtain ⟨H', hH', hidx', u', hu'⟩ := Lox.exists_finiteIndex_fix_of_restrictGroup ι hres'
        (H := linearImage H) le_rfl (by rw [Subgroup.relIndex_self]; exact one_ne_zero) hu
      exact hne H' (hH'.trans (Subgroup.map_mono hle))
        (Subgroup.relIndex_ne_zero_trans hidx' (Lox.relIndex_map_ne_zero linearPart hidx))
        ⟨u', hu'⟩
  refine ⟨_, hsp, rfl, hfin, hE, hdiscH, hnfix, ?_⟩
  obtain ⟨e₁, e₂⟩ := preimage_omega_limitSetJ ι hι hres'
  rcases omegaSOpens_eq_limitOpens_of_relIndex h hlox hle hidx with he | he
  · have hpre : ι.preimageOpens Ω = limitOpensPlus H := by
      refine Opens.ext ?_
      show ι ⁻¹' (Ω : Set (Minkowski d)) = omegaPlus (limitSetJ H)
      rw [hΩ, he]; exact e₁
    refine Or.inl ⟨hpre ▸ hM₁, fun v hv p hp => ?_⟩
    have hpre' : ι ⁻¹' omegaS Γ S = omegaPlus (limitSetJ H) :=
      congrArg (fun U : Opens _ => (U : Set (Minkowski d₁))) hpre
    rw [← hpre'] at hp ⊢
    exact hEinv v hv p hp
  · have hpre : ι.preimageOpens Ω = limitOpensMinus H := by
      refine Opens.ext ?_
      show ι ⁻¹' (Ω : Set (Minkowski d)) = omegaMinus (limitSetJ H)
      rw [hΩ, he]; exact e₂
    refine Or.inr ⟨hpre ▸ hM₁, fun v hv p hp => ?_⟩
    have hpre' : ι ⁻¹' omegaS Γ S = omegaMinus (limitSetJ H) :=
      congrArg (fun U : Opens _ => (U : Set (Minkowski d₁))) hpre
    rw [← hpre'] at hp ⊢
    exact hEinv v hv p hp

/-- **[10.G], l.3412–3417, after the reduction**: a finite-index `Γ' ≤ Γ₂` on whose restriction
`L_U` is trivial on `E = span 𝒩(Γ'_U)` — `Lox.exists_finiteIndex_linOf_eq_on_span` for the
restricted group `Γ₂_U`, pulled back to `Γ₂` (`Lox.exists_le_restrictGroup_le`). -/
theorem exists_finiteIndex_restrict_trivial_on_span (h : CCAction Γ S)
    (hlox : ∃ γ ∈ Γ, IsLoxodromic (linOf γ)) {d₁ : ℕ} (ι : AffineMinkEmbedding d₁ d)
    (hι : ι.Orthochronous) {Γ₂ : Subgroup (isom d)} (hle₂ : Γ₂ ≤ Γ) (hidx₂ : Γ₂.relIndex Γ ≠ 0)
    (hres : ι.RestrictsIn Γ₂) :
    ∃ Γ' : Subgroup (isom d), Γ' ≤ Γ₂ ∧ Γ'.relIndex Γ₂ ≠ 0 ∧
      ∀ Γ'' : Subgroup (isom d), Γ'' ≤ Γ' →
        ∀ g ∈ ι.restrictGroup Γ'', ∀ v ∈ Submodule.span ℝ (kerTranslations (ι.restrictGroup Γ'')),
          linOf g v = v := by
  obtain ⟨hsp, hfin, -⟩ := restrict_kerTranslations_lattice h hlox ι hι hle₂ hidx₂ hres
  obtain ⟨H₀, -, hH₀i, hH₀E⟩ := Lox.exists_finiteIndex_linOf_eq_on_span hsp hfin
    fun _ hγ _ hv => linOf_mem_kerTranslations hγ hv
  obtain ⟨Γ', hle', hidx', hrG⟩ := Lox.exists_le_restrictGroup_le ι hres hH₀i
  refine ⟨Γ', hle', hidx', fun Γ'' hle'' g hg v hv => hH₀E g (hrG (Lox.restrictGroup_mono ι hle'' hg))
    v (Submodule.span_mono (kerTranslations_subset_of_le
      (Lox.restrictGroup_mono ι (hle''.trans hle'))) hv)⟩

end GenericReduction

/-! ## 9. [10.M] The elementary case: Misner spacetimes

Placed after §11b (out of numerical order): the proof uses `generic_omegaS_eq` (§11),
`limitSetJ_eq_of_relIndex_ne_zero` and `omegaSOpens_add_perp` (§11b). -/

section Misner

-- the glue below exceeds the default 200000 heartbeats
set_option maxHeartbeats 400000 in
/-- **[10.M] (l.3235–3330): the elementary loxodromic case, up to finite index.** If, up to finite
index, `L(Γ)` preserves an isotropic direction and `Γ` has a loxodromic element, then for a
finite-index subgroup `Γ' ≤ Γ` the quotient `B = Γ'\Ω(S̃)` is a linear twisted product over a Misner
spacetime — with an element of nonzero boost parameter (finding F1). This is DEC-43's R1 (a finite
cover of `M(S)`); the paper states the conclusion for `Γ` itself (l.3326–3330), which fails (finding:
in `𝐌⁴` the group generated by a boost `γ₀` and a glide `σ(x,z₁,z₂,y) = (−y, z₁+1, −z₂, −x)` with
`σγ₀σ⁻¹ = γ₀⁻¹` is elementary up to index 2, satisfies `CCAction` on `{x > 0, y < 0} × ℝ²`, and its
restriction to the direction of `U` is non-abelian, while a Misner group is abelian). `d = d' + 1`
(`IsMisnerSpacetime` lives in `Minkowski (d' + 1)`); the Misner base has dimension
`d₁ + 1 ≤ d' + 1`. **⚠ strengthened: a cited external, as `BarbotExternals`**: `hBieb`, Bieberbach I
in every dimension `≤ d' + 2` (master ruling 2026-11-01, DEC-36's named-externals policy: the
conclusion implies Bieberbach I for torsion-free orientation-preserving crystallographic groups of
`ℝ^{d'}`, so it cannot be proved without it); used at `k = d'` (`Lox.fix_second_null`) and
`k = d' + 1` (`Lox.misner_bieberbach`). `hcaus` is carried, unused (⚠ weakened).

**No `sorry` in this proof.** The steps: `Γ₁` of finite index fixing `u₀`
(`Lox.exists_finiteIndex_fix_loxodromic`); `b ≡ 0` (the invariant level `s₀`); `Δ₁ = u₁` fixed by
all of `L(Γ₁)` (`Lox.fix_second_null`, finding F4); then the Misner identification l.3302–3330,
through the four lemma modules `Flat.Lox.Misner*`: the second level `s₁`; the two-null-vector
frame `φ` and the normal form `γ(φ·ofNull x y z) = φ·ofNull (eᵃx) (e⁻ᵃy) (Az + u)` on `Γ₁`
(`Lox.misner_frame`, either order of the two axes); `limitSetJ Γ₁ = {(u₀,s₀),(u₁,s₁)}`
(`Lox.misner_limitSet`), hence for `Γ` by finite index and `Ω(S̃) = Ω^±` of it
(`generic_omegaS_eq`); Bieberbach for the euclidean model `(s, z) ↦ (s + a, Az + u)` of `Γ₁` on
`ℝ^{d'+1}`, discrete by properness on the tube — not for the action on `π_P⁻¹(0)` (finding F3) —
giving `Γ'`, `J`, `z₀` and a boost (`Lox.misner_bieberbach`); `restrictGroup Γ' = misnerGroup L`
with `L` ball-finite and of nonzero boost (`Lox.misner_restrict`, finding F1); then `B = Γ'\Ω(S̃)`,
`omegaSOpens_add_perp`, `suspendre`, and `ι⁻¹Ω(S̃)` is `misnerWedge d₁` or `misnerWedgePast d₁`
(frame `1`). The lemma modules' own `sorry`s, if any, are inherited (none at this writing). -/
theorem loxo_elementary_misner {d' : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (Minkowski (d' + 1)) M]
    [HasGroupoid M (gxGroupoid (isom (d' + 1)) (Minkowski (d' + 1)))] [T2Space M] {x₀ : M}
    {D : UniversalCover M x₀ → Minkowski (d' + 1)}
    {ρ : Deck (UniversalCover.proj M x₀) →* isom (d' + 1)} {S : Set M}
    (hBieb : ∀ k ≤ d' + 1 + 1, BieberbachI (EuclideanSpace ℝ (Fin k)))
    (hpair : IsDevelopingPair x₀ D ρ) (hcaus : (flatCausality (d' + 1) M).IsCausal)
    (h : DevelopsCC x₀ D S) (hlox : ∃ γ ∈ ρ.range, IsLoxodromic (linOf γ))
    (helem : ¬IsNonelementary ρ.range) :
    ∃ Γ' : Subgroup (isom (d' + 1)), Γ' ≤ ρ.range ∧ Γ'.relIndex ρ.range ≠ 0 ∧
      ∃ B : FlatSpacetime.{0} (d' + 1),
        IsQuotientOf B Γ' (omegaSOpens ρ.range (D '' (UniversalCover.proj M x₀ ⁻¹' S))) ∧
        ∃ (d₁ : ℕ) (M₁ : FlatSpacetime.{0} (d₁ + 1)), d₁ ≤ d' ∧ IsLTPOver B M₁ ∧
          IsMisnerSpacetime M₁ := by
  -- l.3237–3240, the first step (`Flat.Lox.FixLoxodromic`): a finite-index `Γ₁ ≤ Γ` containing a
  -- power of the loxodromic `γ₀`, with `L(Γ₁)` fixing the direction `Δ₀ = u₀`, one of the two
  -- distinct fixed points `u₀ ≠ u₁` of `L(γ₀)` on `𝒮`.
  obtain ⟨γ₀, hγ₀, hlox₀⟩ := hlox
  simp only [IsNonelementary, not_forall, not_not] at helem
  obtain ⟨H, hH, hHi, hu⟩ := helem
  obtain ⟨Γ₁, hΓ₁, hΓ₁i, k, hk, hγ₀k, u₀, u₁, hu₀₁, hf₀, hf₁, hfix₀⟩ :=
    Lox.exists_finiteIndex_fix_loxodromic hγ₀ hlox₀ ⟨H, hH, hHi, hu⟩
  -- `hcaus` is §8's setting (carried, unused: ⚠ weakened); `hBieb` is the cited Bieberbach I, spent at
  -- `k = d'` (`Lox.fix_second_null`) and `k = d' + 1` (`Lox.misner_bieberbach`)
  have _ := hcaus
  -- `[T2Space M]` gives §8's data in `𝐌ⁿ` (`ccAction_of_developsCC`)
  have h' := ccAction_of_developsCC hpair h
  -- l.3250–3257, `b ≡ 0` for `Γ₁`: a `Γ₁`-invariant lightlike level `{⟨(1,u₀)|·⟩ = s₀}`
  have hlox₁ : ∃ γ ∈ Γ₁, IsLoxodromic (linOf γ) := ⟨γ₀ ^ k, hγ₀k, by
    have := hlox₀.zpow_linOf (n := (k : ℤ)) (by exact_mod_cast hk.ne')
    rwa [zpow_natCast] at this⟩
  -- (the argument of `exists_invariant_nullLevel_of_ccAction`, below, inlined)
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : ℝ, ∀ γ ∈ Γ₁, ∀ p : Minkowski (d' + 1),
      minkB (nullVec u₀) p = s₀ → minkB (nullVec u₀) (γ • p) = s₀ := by
    obtain ⟨x, hx⟩ := h'.nonempty
    refine Lox.exists_invariant_nullLevel (fun γ hγ => hfix₀ _ ⟨γ, hγ, rfl⟩) hlox₁
      (Ω := omegaS ρ.range _) ⟨x, subset_omegaS h' hx⟩ ?_
    rcases loxregular_sign h' with hF | hP
    · exact Or.inl fun p hp => mem_omegaPlus.2 fun w ⟨γ, hγ, hw⟩ =>
        mem_halfPlus.1 (hF w ⟨γ, hΓ₁ hγ, hw⟩ hp)
    · exact Or.inr fun p hp => mem_omegaMinus.2 fun w ⟨γ, hγ, hw⟩ =>
        mem_halfMinus.1 (hP w ⟨γ, hΓ₁ hγ, hw⟩ hp)
  -- l.3260–3299, the second null direction (`Flat.Lox.SecondNullFix`, proved under Bieberbach I
  -- in `ℝ^{d'}`): ALL of `L(Γ₁)` fixes `u₁`, the second fixed point of `γ₀ᵏ` — not the paper's
  -- route (its conjugation formula l.3264–3265 omits the screw part of `α(γ)`: finding F4)
  have hloxk : IsLoxodromic (linOf (γ₀ ^ k)) := by
    have := hlox₀.zpow_linOf (n := (k : ℤ)) (by exact_mod_cast hk.ne')
    rwa [zpow_natCast] at this
  have hfix₁ : ∀ γ ∈ Γ₁, lorentzSphere (linearPart γ) u₁ = u₁ :=
    Lox.fix_second_null (hBieb d' (by omega)) h' hΓ₁ hγ₀k hloxk hu₀₁
      (fun γ hγ => hfix₀ _ ⟨γ, hγ, rfl⟩) (by rw [map_pow]; exact Lox.lorentzSphere_fix_pow hf₁ k)
      hs₀
  have hfix₀' : ∀ γ ∈ Γ₁, lorentzSphere (linearPart γ) u₀ = u₀ := fun γ hγ => hfix₀ _ ⟨γ, hγ, rfl⟩
  -- (g1) the second invariant level
  obtain ⟨s₁, hs₁⟩ : ∃ s₁ : ℝ, ∀ γ ∈ Γ₁, ∀ p : Minkowski (d' + 1),
      minkB (nullVec u₁) p = s₁ → minkB (nullVec u₁) (γ • p) = s₁ := by
    obtain ⟨x, hx⟩ := h'.nonempty
    refine Lox.exists_invariant_nullLevel hfix₁ hlox₁
      (Ω := omegaS ρ.range _) ⟨x, subset_omegaS h' hx⟩ ?_
    rcases loxregular_sign h' with hF | hP
    · exact Or.inl fun p hp => mem_omegaPlus.2 fun w ⟨γ, hγ, hw⟩ =>
        mem_halfPlus.1 (hF w ⟨γ, hΓ₁ hγ, hw⟩ hp)
    · exact Or.inr fun p hp => mem_omegaMinus.2 fun w ⟨γ, hγ, hw⟩ =>
        mem_halfMinus.1 (hP w ⟨γ, hΓ₁ hγ, hw⟩ hp)
  -- (g2) the frame and the normal form
  obtain ⟨φ, hφP, hφM, hnf⟩ := Lox.misner_frame hu₀₁ hfix₀' hfix₁ hs₀ hs₁
  -- (g3) the limit set and `Ω(S̃)`
  set Sig := D '' (UniversalCover.proj M x₀ ⁻¹' S) with hSig
  have hlox : ∃ γ ∈ ρ.range, IsLoxodromic (linOf γ) := ⟨γ₀, hγ₀, hlox₀⟩
  have hΛ₁ : limitSetJ Γ₁ = ({(u₀, s₀), (u₁, s₁)} : Set (PenroseSphere (d' + 1) × ℝ)) :=
    Lox.misner_limitSet hu₀₁ hfix₀' hfix₁ hs₀ hs₁ hlox₁
  have hΛ : limitSetJ ρ.range = ({(u₀, s₀), (u₁, s₁)} : Set (PenroseSphere (d' + 1) × ℝ)) := by
    rw [← limitSetJ_eq_of_relIndex_ne_zero hΓ₁ hΓ₁i, hΛ₁]
  set Ω := omegaSOpens ρ.range Sig with hΩ
  have hΩside : ((Ω : Set (Minkowski (d' + 1))) =
      omegaPlus ({(u₀, s₀), (u₁, s₁)} : Set (PenroseSphere (d' + 1) × ℝ))) ∨
      ((Ω : Set (Minkowski (d' + 1))) =
      omegaMinus ({(u₀, s₀), (u₁, s₁)} : Set (PenroseSphere (d' + 1) × ℝ))) := by
    rcases generic_omegaS_eq h' hlox with ⟨he, -⟩ | ⟨he, -⟩
    · left; rw [hΩ, he, ← hΛ]; rfl
    · right; rw [hΩ, he, ← hΛ]; rfl
  -- (g4) properness on `Ω` and the tube
  have hprop₁ : ∀ K ⊆ (Ω : Set (Minkowski (d' + 1))), IsCompact K →
      {γ : isom (d' + 1) | γ ∈ Γ₁ ∧ (γ • K ∩ K).Nonempty}.Finite := fun K hK hKc =>
    (loxo_properlyDiscontinuous h' hlox K hK hKc).subset fun γ hγ => ⟨hΓ₁ hγ.1, hγ.2⟩
  obtain ⟨x₁, y₁, htube⟩ : ∃ x₁ y₁ : ℝ, ∀ (b : ℝ) (z : EuclideanSpace ℝ (Fin d')),
      φ • ofNull (Real.exp b * x₁) (Real.exp (-b) * y₁) z ∈ (Ω : Set (Minkowski (d' + 1))) := by
    rcases hΩside with he | he
    · refine ⟨1, -1, fun b z => ?_⟩
      rw [he, hφP]
      exact ⟨by positivity, by nlinarith [Real.exp_pos (-b)]⟩
    · refine ⟨-1, 1, fun b z => ?_⟩
      rw [he, hφM]
      exact ⟨by nlinarith [Real.exp_pos b], by positivity⟩
  -- (g5) Bieberbach through the euclidean model
  obtain ⟨a₀, A₀, v₀, hnf₀, hl₀⟩ := hnf _ hγ₀k
  obtain ⟨Γ', hΓ', hΓ'i, d₁, J, z₀, hd₁, htr, hboost⟩ :=
    Lox.misner_bieberbach (hBieb (d' + 1) (by omega)) φ (fun γ hγ => by
        obtain ⟨a, A, u, h1, -⟩ := hnf γ hγ; exact ⟨a, A, u, h1⟩)
      hprop₁ htube ⟨_, hγ₀k, a₀, hl₀ hloxk, A₀, v₀, hnf₀⟩
  -- (g6) the restriction to `U`
  obtain ⟨ι, L, hιf, hι, hres, hrg, hBF, hLb⟩ :=
    Lox.misner_restrict φ J z₀ htr hboost (fun K hK hKc => (hprop₁ K hK hKc).subset
      fun γ hγ => ⟨hΓ' hγ.1, hγ.2⟩) htube
  -- (g7) `B = Γ'\Ω(S̃)` and `suspendre`
  have hle : Γ' ≤ ρ.range := hΓ'.trans hΓ₁
  have hidx : Γ'.relIndex ρ.range ≠ 0 := Subgroup.relIndex_ne_zero_trans hΓ'i hΓ₁i
  have hgh := bprop_ghyp h'
  haveI : FlatQuotient.Invariant Γ' Ω := ⟨fun γ p hp => by
    have := Set.smul_mem_smul_set (a := (γ : isom (d' + 1))) (show p ∈ omegaS ρ.range Sig from hp)
    rwa [hgh.2.2.2.1 γ (hle γ.2)] at this⟩
  haveI : IsCancelSMul Γ' Ω :=
    isCancelSMul_of_free fun γ hγ h1 x hx => loxo_free h' γ (hle hγ) h1 x hx
  haveI : ProperlyDiscontinuousSMul Γ' Ω :=
    properlyDiscontinuousSMul_of_finite fun K hK hKc =>
      (loxo_properlyDiscontinuous h' hlox K hK hKc).subset fun γ hγ => ⟨hle hγ.1, hγ.2⟩
  obtain ⟨x, hx⟩ := h'.nonempty
  have hconn : IsConnected (Ω : Set (Minkowski (d' + 1))) :=
    ⟨⟨x, subset_omegaS h' hx⟩, hgh.2.1.isPreconnected⟩
  set B := FlatQuotient.toFlatSpacetime Γ' Ω hconn
  have hB : IsQuotientOf B Γ' Ω := FlatQuotient.isQuotientOf_toFlatSpacetime _ _ _
  have hperp := omegaSOpens_add_perp h' hlox ι hle hidx hres
  set M₁ := ι.baseSpacetime B hB hres hperp
  have hM₁ : IsQuotientOf M₁ (ι.restrictGroup Γ') (ι.preimageOpens Ω) :=
    ι.isQuotientOf_baseSpacetime B hB hres hperp
  refine ⟨Γ', hle, hidx, B, hB, d₁, M₁, hd₁, suspendre B hB ι hι hres hperp, ?_⟩
  -- (g8) `M₁` is a Misner spacetime (frame `1`, absorbed in `ι`)
  have hιp : ∀ p : Minkowski (d₁ + 1),
      ι p = φ • ofNull (nullX p) (nullY p) (z₀ + J (nullZ p)) := fun p => by
    conv_lhs => rw [← Nonlox.ULTP.ofNull_null p]
    exact hιf _ _ _
  refine ⟨1, L, hBF, hLb, ?_⟩
  rw [frameConj_one, isomImage_one, isomImage_one, ← hrg]
  rcases hΩside with he | he
  · left
    have hpre : ι.preimageOpens Ω = misnerWedge d₁ := by
      refine Opens.ext (Set.ext fun p => ?_)
      show ι p ∈ (Ω : Set (Minkowski (d' + 1))) ↔ p ∈ omegaPlus (misnerΛ d₁)
      rw [he, hιp, hφP, mem_omegaPlus_misnerΛ]
    exact hpre ▸ hM₁
  · right
    have hpre : ι.preimageOpens Ω = misnerWedgePast d₁ := by
      refine Opens.ext (Set.ext fun p => ?_)
      show ι p ∈ (Ω : Set (Minkowski (d' + 1))) ↔ nullX p < 0 ∧ 0 < nullY p
      rw [he, hιp, hφM]
    exact hpre ▸ hM₁

end Misner

section GenericConclusion

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Minkowski d) M]
  [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))] [T2Space M] {x₀ : M}
  {D : UniversalCover M x₀ → Minkowski d} {ρ : Deck (UniversalCover.proj M x₀) →* isom d}
  {S : Set M}

/-- **[10.G], the conclusion in the central-extension form (b)** (l.3416–3456; DEC-43's R1, DEC-44):
in the nonelementary loxodromic case, a finite-index subgroup `Γ' ≤ Γ` (on which conjugation acts
trivially on `𝒩`) gives `B = Γ'\Ω(S̃)`, a linear twisted product (over the timelike `U` of
Prop 10.4, `blem:suspendre`) over a spacetime of family (b). Proved (wave 7) through
`exists_generic_reduction`, `exists_finiteIndex_restrict_trivial_on_span` and
`generic_isCHCentralExtension`; `[T2Space M]` (added 2026-11-01) gives `ccAction_of_developsCC`.
The family-(b) group of `M₁` is the restriction `Γ'_U`. -/
theorem loxo_generic_centralExtension (hpair : IsDevelopingPair x₀ D ρ)
    (hcaus : (flatCausality d M).IsCausal) (h : DevelopsCC x₀ D S)
    (hlox : ∃ γ ∈ ρ.range, IsLoxodromic (linOf γ)) (hne : IsNonelementary ρ.range)
    (hA : AuslanderCarriereDalbo d) (hU : MaxUnipotentSubspace d) :
    ∃ Γ' : Subgroup (isom d), Γ' ≤ ρ.range ∧ Γ'.relIndex ρ.range ≠ 0 ∧
      ∃ B : FlatSpacetime.{0} d,
        IsQuotientOf B Γ' (omegaSOpens ρ.range (D '' (UniversalCover.proj M x₀ ⁻¹' S))) ∧
        ∃ (d₁ : ℕ) (M₁ : FlatSpacetime.{0} d₁), d₁ ≤ d ∧ IsLTPOver B M₁ ∧
          IsCHCentralExtension M₁ := by
  -- `hcaus` is the setting of §8 (kept in the statement); the proof does not use it (⚠ weakened)
  have _ := hcaus
  have h' := ccAction_of_developsCC hpair h
  -- the reduction to `U` (Props 10.4, 10.5, `blem:suspendre`'s orientation step)
  obtain ⟨d₁, ι, Γ₂, hle₂, hidx₂, hι, hres, hdisc⟩ := exists_generic_reduction h' hne hA hU
  -- l.3412–3417: the finite-index subgroup on which `L_U` is trivial on `E`
  obtain ⟨Γ', hle', hidx', hE⟩ :=
    exists_finiteIndex_restrict_trivial_on_span h' hlox ι hι hle₂ hidx₂ hres
  have hidx : Γ'.relIndex ρ.range ≠ 0 := Subgroup.relIndex_ne_zero_trans hidx' hidx₂
  obtain ⟨B, hB, M₁, hltp, hM₁⟩ :=
    generic_isCHCentralExtension h' hlox hne ι hι hres hdisc hle' hle₂ hidx (hE Γ' le_rfl)
  exact ⟨Γ', hle'.trans hle₂, hidx, B, hB, d₁, M₁, Lox.le_of_affineMinkEmbedding ι, hltp, _, hM₁⟩

/-- **[10.G], family (a) under "`π₁` finitely generated"** (DEC-44, finding F2/gap G5): through
Selberg's lemma (a named external, `Flat.Externals`), a further finite-index subgroup has
torsion-free linear part, and family (b) with `L(Γ)` torsion-free is the literal
"Cauchy-hyperbolic × torus" (a). Proved (wave 7): `Γ'` is cut down by Selberg in dimension `d`
(torsion-free `L(Γ')`) and, after restriction to `U`, by Selberg in dimension `d₁`
(`Lox.selbergLemma_minkowski_of_le`; torsion-freeness does not pass to `L_U`), the restricted group
being finitely generated by Schreier's lemma. -/
theorem loxo_generic_torusProduct (hpair : IsDevelopingPair x₀ D ρ)
    (hcaus : (flatCausality d M).IsCausal) (h : DevelopsCC x₀ D S)
    (hlox : ∃ γ ∈ ρ.range, IsLoxodromic (linOf γ)) (hne : IsNonelementary ρ.range)
    (hA : AuslanderCarriereDalbo d) (hU : MaxUnipotentSubspace d)
    (hS : SelbergLemma (Minkowski d)) (hfg : ρ.range.FG) :
    ∃ Γ' : Subgroup (isom d), Γ' ≤ ρ.range ∧ Γ'.relIndex ρ.range ≠ 0 ∧
      (∀ γ ∈ Γ', IsOfFinOrder (linOf γ) → linOf γ = 1) ∧
      ∃ B : FlatSpacetime.{0} d,
        IsQuotientOf B Γ' (omegaSOpens ρ.range (D '' (UniversalCover.proj M x₀ ⁻¹' S))) ∧
        ∃ (d₁ : ℕ) (M₁ : FlatSpacetime.{0} d₁), d₁ ≤ d ∧ IsLTPOver B M₁ ∧ IsCHTorusProduct M₁ := by
  obtain ⟨Γ₁, hle₁, hidx₁, htf₁⟩ := exists_finiteIndex_torsionFree_linOf hS hfg
  -- Selberg for the base `M₁` of dimension `d₁ ≤ d` (`Flat.Lox.SelbergMono`): torsion-freeness of
  -- `L(Γ)` does not pass to `L_U(Γ)`, so the external is moved down instead
  have hS₁ : ∀ d₁ ≤ d, SelbergLemma (Minkowski d₁) := fun _ hd₁ =>
    Lox.selbergLemma_minkowski_of_le hd₁ hS
  have _ := hcaus
  have h' := ccAction_of_developsCC hpair h
  obtain ⟨d₁, ι, Γ₂, hle₂, hidx₂, hι, hres, hdisc⟩ := exists_generic_reduction h' hne hA hU
  obtain ⟨Γ', hle', hidx', hE⟩ :=
    exists_finiteIndex_restrict_trivial_on_span h' hlox ι hι hle₂ hidx₂ hres
  -- intersect with Selberg's subgroup in dimension `d`
  set Γ'' := Γ' ⊓ Γ₁ with hΓ''
  have hidx'' : Γ''.relIndex ρ.range ≠ 0 :=
    Subgroup.relIndex_inf_ne_zero (Subgroup.relIndex_ne_zero_trans hidx' hidx₂) hidx₁
  have hle'' : Γ'' ≤ Γ₂ := inf_le_left.trans hle'
  have hres'' := Lox.restrictsIn_mono hres hle''
  -- `Γ''` is finitely generated (finite index in the finitely generated `Γ`)
  have hfg'' : Γ''.FG := by
    haveI : Group.FG ρ.range := (Group.fg_iff_subgroup_fg _).2 hfg
    haveI : (Γ''.subgroupOf ρ.range).FiniteIndex := ⟨hidx''⟩
    have h1 : (Γ''.subgroupOf ρ.range).FG := (Group.fg_iff_subgroup_fg _).1 inferInstance
    have h2 := fg_map_of_fg h1 ρ.range.subtype
    rwa [Subgroup.subgroupOf_map_subtype, inf_of_le_left (hle''.trans hle₂)] at h2
  -- so is its restriction to `U`; Selberg in dimension `d₁` there
  have hGfg : (ι.restrictGroup Γ'').FG := by
    rw [← Lox.range_restrictHom ι hres'', MonoidHom.range_eq_map]
    exact fg_map_of_fg (Group.fg_def.1 ((Group.fg_iff_subgroup_fg Γ'').2 hfg'')) _
  obtain ⟨H₁, -, hH₁i, htfH₁⟩ :=
    exists_finiteIndex_torsionFree_linOf (hS₁ d₁ (Lox.le_of_affineMinkEmbedding ι)) hGfg
  obtain ⟨Γ₃, hle₃, hidx₃, hrG⟩ := Lox.exists_le_restrictGroup_le ι hres'' hH₁i
  have hidx3 : Γ₃.relIndex ρ.range ≠ 0 := Subgroup.relIndex_ne_zero_trans hidx₃ hidx''
  obtain ⟨B, hB, M₁, hltp, hM₁⟩ := generic_isCHCentralExtension h' hlox hne ι hι hres hdisc
    (hle₃.trans hle'') hle₂ hidx3 (hE Γ₃ (hle₃.trans inf_le_left))
  exact ⟨Γ₃, (hle₃.trans hle'').trans hle₂, hidx3,
    fun γ hγ hf => htf₁ γ ((hle₃.trans inf_le_right) hγ) hf, B, hB, d₁, M₁,
    Lox.le_of_affineMinkEmbedding ι, hltp, _, hM₁, fun g hg hf => htfH₁ g (hrG hg) hf⟩

end GenericConclusion

/-! ## 12. `bprop:admlox` (Prop 4.17) in `𝒥`: invariance, and the link with `Flat.Externals` -/

section Admlox

variable {Γ : Subgroup (isom d)}

theorem continuous_isomPenrose (g : isom d) : Continuous (isomPenrose g) := by
  have h1 : Continuous fun w : PenroseSphere d × ℝ => lorentzSphere (linearPart g) w.1 :=
    (continuous_lorentzSphere _).comp continuous_fst
  have h2 : Continuous fun w : PenroseSphere d × ℝ => (lorentzScale (linearPart g) w.1)⁻¹ * w.2 :=
    (((continuous_lorentzScale _).comp continuous_fst).inv₀
      fun w => (lorentzScale_pos _ _).ne').mul continuous_snd
  have h3 : Continuous fun w : PenroseSphere d × ℝ =>
      minkB (nullVec (lorentzSphere (linearPart g) w.1)) (g • (0 : Minkowski d)) :=
    (continuous_minkB_nullVec_param (g • (0 : Minkowski d))).comp
      (h1.prodMk (continuous_const (y := (0 : ℝ))))
  exact h1.prodMk (h2.add h3)

/-- **`bprop:admlox`, invariance** (l.1232–1236): `Λ(Γ)` is `Γ`-invariant in `𝒥`. -/
theorem isomPenrose_image_limitSetJ_subset {η : isom d} (hη : η ∈ Γ) :
    isomPenrose η '' limitSetJ Γ ⊆ limitSetJ Γ :=
  (image_closure_subset_closure_image (continuous_isomPenrose η)).trans
    (closure_mono (by rintro _ ⟨w, hw, rfl⟩; exact isomPenrose_mem_loxRepSet hη hw))

/-- On `𝒮`, a repulsive fixed point in `𝒥` is Externals' repulsive fixed point. -/
theorem IsRepulsiveFixedJ.isRepulsiveFixed {γ : isom d} {w : PenroseSphere d × ℝ}
    (hw : IsRepulsiveFixedJ γ w) : IsRepulsiveFixed (linearPart γ) w.1 := by
  obtain ⟨hlox, l, hl0, hl1, hAn, -⟩ := hw
  refine ⟨by rw [← linOf_eq_linearPart]; exact hlox, l, hl0, hl1, ?_⟩
  rw [← linOf_eq_linearPart]; exact hAn

theorem fst_image_loxRepSet_subset (Γ : Subgroup (isom d)) :
    Prod.fst '' loxRepSet Γ ⊆ repulsiveSet (linearImage Γ) := by
  rintro _ ⟨w, ⟨γ, hγ, hw⟩, rfl⟩
  exact ⟨linearPart γ, ⟨γ, hγ, rfl⟩, hw.isRepulsiveFixed⟩

/-- **`bprop:admlox` on `𝒮`** (through `Flat.Externals`' `LimitSetMinimal`): `δ(Λ(Γ))` lies in every
nonempty closed `L(Γ)`-invariant subset of `𝒮`. -/
theorem fst_image_limitSetJ_subset (hL : LimitSetMinimal d) (hΓ : DiscreteTopology (linearImage Γ))
    (hfix : ¬HasGlobalFixedPoint (linearImage Γ)) {F : Set (PenroseSphere d)} (hF : IsClosed F)
    (hne : F.Nonempty) (hinv : IsSphereInvariant (linearImage Γ) F) :
    Prod.fst '' limitSetJ Γ ⊆ F := by
  have h1 : Prod.fst '' limitSetJ Γ ⊆ closure (Prod.fst '' loxRepSet Γ) :=
    image_closure_subset_closure_image continuous_fst
  exact h1.trans (closure_minimal ((fst_image_loxRepSet_subset Γ).trans
    (hL _ hΓ hfix F hF hne hinv)) hF)

/-- `minkQ` is positive semidefinite on the orthogonal of a nonzero null vector `n`
(`minkQ_nonneg_of_null_orth`), so there `|⟨v | z⟩| ≤ (|v|² + |z|²)/2`. -/
theorem abs_minkB_le_of_null_orth {n v z : Minkowski d} (hn : minkQ n = 0) (hn0 : n ≠ 0)
    (hv : minkB n v = 0) (hz : minkB n z = 0) : |minkB v z| ≤ (minkQ v + minkQ z) / 2 := by
  have h1 := (minkQ_nonneg_of_null_orth hn hn0 (w := v + z)
    (by rw [minkB_add_right, hv, hz, add_zero])).1
  have h2 := (minkQ_nonneg_of_null_orth hn hn0 (w := v - z)
    (by rw [minkB_sub_right, hv, hz, sub_zero])).1
  rw [minkQ_eq_minkB] at h1 h2
  rw [minkQ_eq_minkB v, minkQ_eq_minkB z]
  simp only [minkB_add_left, minkB_add_right, minkB_sub_left, minkB_sub_right] at h1 h2
  rw [minkB_comm z v] at h1 h2
  rw [abs_le]; constructor <;> linarith

/-- The functional equation of `w` along `γ` makes `nullVec w.1` an eigenvector of every `L(γᵏ)`. -/
theorem linOf_pow_nullVec_of_funEq {γ : isom d} {w : PenroseSphere d × ℝ} {c : ℝ} (hc : c ≠ 0)
    (h : ∀ p, minkB (nullVec w.1) (γ • p) - w.2 = c⁻¹ * (minkB (nullVec w.1) p - w.2)) (k : ℕ) :
    linOf (γ ^ k) (nullVec w.1) = c ^ k • nullVec w.1 :=
  eigen_of_funEq (pow_ne_zero k hc) fun p => by
    rw [IsRepulsiveFixedJ.iterate h k p, inv_pow]

/-- Differences along `gᵏ` are moved by the linear part `L(gᵏ)`. -/
theorem pow_smul_sub_pow_smul (g : isom d) (k : ℕ) (a b : Minkowski d) :
    (g ^ k) • a - (g ^ k) • b = linOf (g ^ k) (a - b) := by
  rw [smul_eq_lin_add, smul_eq_lin_add, map_sub]; abel

/-- **The elliptic part grows at most linearly**: if `e` is orthogonal to the two null
eigenvectors `nullVec w.1`, `nullVec w'.1` of `L(γ)` (two distinct null directions), then
`⟨e | γᵏ q⟩ − ⟨e | q⟩` is `O(k)`: each step is `⟨e | L(γᵏ) z⟩` with `z ⊥ nullVec w.1`, bounded by
`(|e|² + |z|²)/2` (`abs_minkB_le_of_null_orth`, `L(γᵏ)` preserving `minkQ` and `(nullVec w.1)^⊥`). -/
theorem exists_abs_minkB_pow_smul_sub_le {γ : isom d} {w w' : PenroseSphere d × ℝ} {c c' : ℝ}
    (hc : c ≠ 0) (hc' : c' ≠ 0)
    (h : ∀ p, minkB (nullVec w.1) (γ • p) - w.2 = c⁻¹ * (minkB (nullVec w.1) p - w.2))
    (h' : ∀ p, minkB (nullVec w'.1) (γ • p) - w'.2 = c'⁻¹ * (minkB (nullVec w'.1) p - w'.2))
    (hD : minkB (nullVec w.1) (nullVec w'.1) ≠ 0)
    {e : Minkowski d} (he : minkB (nullVec w.1) e = 0) (he' : minkB (nullVec w'.1) e = 0)
    (q : Minkowski d) :
    ∃ B : ℝ, ∀ k : ℕ, |minkB e ((γ ^ k) • q) - minkB e q| ≤ k * B := by
  obtain ⟨z, β, hv, hz⟩ : ∃ z : Minkowski d, ∃ β : ℝ, γ • q - q = z + β • nullVec w'.1 ∧
      minkB (nullVec w.1) z = 0 := by
    refine ⟨γ • q - q - (minkB (nullVec w.1) (γ • q - q) / minkB (nullVec w.1) (nullVec w'.1)) •
      nullVec w'.1, _, by abel, ?_⟩
    rw [minkB_sub_right, minkB_smul_right, div_mul_cancel₀ _ hD, sub_self]
  refine ⟨(minkQ e + minkQ z) / 2, fun k => ?_⟩
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep : minkB e ((γ ^ (k + 1)) • q) - minkB e ((γ ^ k) • q) =
        minkB e (linOf (γ ^ k) z) := by
      rw [← minkB_sub_right, pow_succ, mul_smul, pow_smul_sub_pow_smul, hv, map_add, map_smul,
        linOf_pow_nullVec_of_funEq hc' h' k, minkB_add_right, minkB_smul_right, minkB_smul_right,
        minkB_comm e (nullVec w'.1), he', mul_zero, mul_zero, add_zero]
    have hLz : minkB (nullVec w.1) (linOf (γ ^ k) z) = 0 := by
      have h1 := lorentz.minkB_apply (linOf_mem (γ ^ k)) (nullVec w.1) z
      rw [linOf_pow_nullVec_of_funEq hc h k, minkB_smul_left, hz] at h1
      exact (mul_eq_zero.1 h1).resolve_left (pow_ne_zero k hc)
    have hb := abs_minkB_le_of_null_orth (minkQ_nullVec w.1) (nullVec_ne_zero w.1) he hLz
    rw [lorentz.minkQ_apply (linOf_mem (γ ^ k))] at hb
    rw [← hstep] at hb
    push_cast
    rw [abs_le] at hb ih ⊢
    constructor <;> nlinarith [hb.1, hb.2, ih.1, ih.2]


/-- **The basin of repulsion in `𝒥`** (l.1255–1264): for a loxodromic `γ` with repulsive point
`w` (and `w'` that of `γ⁻¹`), the negative iterates `γ⁻ᵏ x` of every `x ∈ 𝒥` off the fibre
`δ⁻¹(w'.1)` converge to `w`. Proof: write `nullVec x.1 = a n₀ + b n₁ + e` with `n₀, n₁` the null
eigenvectors and `e ⊥ n₀, n₁`, `a ≠ 0` exactly when `x.1 ≠ w'.1`; along `γᵏ`, the affine function
`⟨nullVec x.1 | ·⟩ − x.2`, rescaled by `λᵏ`, converges to `a (⟨n₀ | ·⟩ − w.2)` (the `n₁` term is
`O((λλ')ᵏ)`, the `e` term `O(kλᵏ)` by `exists_abs_minkB_pow_smul_sub_le`); the affine functions of
`γ⁻ᵏ x` are its positive multiples normalised by `⟨nullVec · | (1,0)⟩ = −1`, so they converge to
`⟨n₀ | ·⟩ − w.2`, which gives both coordinates (`‖u − v₀‖² = −2⟨nullVec u | nullVec v₀⟩`). -/
theorem tendsto_isomPenrose_inv_pow {γ : isom d} {w w' x : PenroseSphere d × ℝ}
    (hw : IsRepulsiveFixedJ γ w) (hw' : IsRepulsiveFixedJ γ⁻¹ w') (hx : x.1 ≠ w'.1) :
    Tendsto (fun k : ℕ => isomPenrose (γ⁻¹ ^ k) x) atTop (𝓝 w) := by
  have hne := hw.fst_ne hw'
  obtain ⟨-, l, hl0, hl1, -, hf⟩ := hw
  obtain ⟨-, l', hl0', hl1', -, hfi⟩ := hw'
  have hf' : ∀ p, minkB (nullVec w'.1) (γ • p) - w'.2 = (l'⁻¹)⁻¹ * (minkB (nullVec w'.1) p - w'.2) :=
    fun p => by rw [inv_inv]; exact funEq_of_inv hl0'.ne' hfi p
  set n₀ := nullVec w.1 with hn₀
  set n₁ := nullVec w'.1 with hn₁
  set n := nullVec x.1 with hn
  have hsub : ∀ {u u' : PenroseSphere d}, u ≠ u' → minkB (nullVec u) (nullVec u') ≠ 0 := by
    intro u u' huu h0
    rw [minkB_nullVec_nullVec] at h0
    have : ‖(u : EuclideanSpace ℝ (Fin d)) - u'‖ = 0 := by
      have : ‖(u : EuclideanSpace ℝ (Fin d)) - u'‖ ^ 2 = 0 := by linarith
      exact pow_eq_zero_iff two_ne_zero |>.1 this
    exact huu (Subtype.ext (sub_eq_zero.1 (norm_eq_zero.1 this)))
  have hD : minkB n₀ n₁ ≠ 0 := hsub hne
  have hxa : minkB n n₁ ≠ 0 := hsub hx
  set a := minkB n n₁ / minkB n₀ n₁ with ha
  set b := minkB n n₀ / minkB n₀ n₁ with hb
  have ha0 : a ≠ 0 := div_ne_zero hxa hD
  set e := n - a • n₀ - b • n₁ with he
  have hq₀ : minkQ n₀ = 0 := minkQ_nullVec _
  have hq₁ : minkQ n₁ = 0 := minkQ_nullVec _
  have he₀ : minkB n₀ e = 0 := by
    rw [he, minkB_sub_right, minkB_sub_right, minkB_smul_right, minkB_smul_right,
      ← minkQ_eq_minkB, hq₀, hb, minkB_comm n₀ n]
    field_simp; ring
  have he₁ : minkB n₁ e = 0 := by
    rw [he, minkB_sub_right, minkB_sub_right, minkB_smul_right, minkB_smul_right,
      ← minkQ_eq_minkB n₁, hq₁, ha, minkB_comm n₁ n, minkB_comm n₁ n₀]
    field_simp; ring
  -- the rescaled affine function along the orbit
  set Φ : ℕ → Minkowski d → ℝ := fun k q => l ^ k * (minkB n ((γ ^ k) • q) - x.2) with hΦ
  have hdec : ∀ k q, Φ k q = a * (minkB n₀ q - w.2) + l ^ k * (a * w.2 + b * w'.2 - x.2) +
      b * (l * l') ^ k * (minkB n₁ q - w'.2) + l ^ k * minkB e ((γ ^ k) • q) := by
    intro k q
    have hA : minkB n₀ ((γ ^ k) • q) = w.2 + (l ^ k)⁻¹ * (minkB n₀ q - w.2) := by
      have := IsRepulsiveFixedJ.iterate hf k q; rw [inv_pow] at this; linarith
    have hB : minkB n₁ ((γ ^ k) • q) = w'.2 + l' ^ k * (minkB n₁ q - w'.2) := by
      have := IsRepulsiveFixedJ.iterate hf' k q; rw [inv_inv] at this; linarith
    have hE : minkB e ((γ ^ k) • q) = minkB n ((γ ^ k) • q) - a * minkB n₀ ((γ ^ k) • q) -
        b * minkB n₁ ((γ ^ k) • q) := by
      rw [he, minkB_sub_left, minkB_sub_left, minkB_smul_left, minkB_smul_left]
    simp only [hΦ]
    rw [hE, hA, hB, mul_pow]
    have : l ^ k ≠ 0 := pow_ne_zero k hl0.ne'
    field_simp; ring
  have hpow : Tendsto (fun k : ℕ => l ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hl0.le hl1
  have hpow' : Tendsto (fun k : ℕ => (l * l') ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (mul_nonneg hl0.le hl0'.le)
      (mul_lt_one_of_nonneg_of_lt_one_left hl0.le hl1 hl1'.le)
  have hlim : ∀ q, Tendsto (fun k => Φ k q) atTop (𝓝 (a * (minkB n₀ q - w.2))) := by
    intro q
    obtain ⟨B, hB⟩ := exists_abs_minkB_pow_smul_sub_le hl0.ne'
      (inv_ne_zero hl0'.ne') hf hf' hD he₀ he₁ q
    have hE : Tendsto (fun k : ℕ => l ^ k * minkB e ((γ ^ k) • q)) atTop (𝓝 0) := by
      refine squeeze_zero_norm (a := fun k : ℕ => l ^ k * |minkB e q| + ((k : ℝ) * l ^ k) * B)
        (fun k => ?_) ?_
      · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hl0 k)]
        have := hB k
        have h2 : |minkB e ((γ ^ k) • q)| ≤ |minkB e q| + k * B := by
          have := abs_sub_abs_le_abs_sub (minkB e ((γ ^ k) • q)) (minkB e q); linarith
        nlinarith [pow_pos hl0 k]
      · have := (hpow.mul_const |minkB e q|).add
          ((tendsto_self_mul_const_pow_of_lt_one hl0.le hl1).mul_const B)
        simpa using this
    have := ((((tendsto_const_nhds (x := a * (minkB n₀ q - w.2))).add
      (hpow.mul_const (a * w.2 + b * w'.2 - x.2))).add
      (((hpow'.const_mul b).mul_const (minkB n₁ q - w'.2)))).add hE)
    simp only [zero_mul, mul_zero, add_zero] at this
    refine this.congr fun k => ?_
    rw [hdec k q]
  -- the normalised affine functions of the iterates converge
  set xk : ℕ → PenroseSphere d × ℝ := fun k => isomPenrose (γ⁻¹ ^ k) x with hxk
  have hrel : ∀ k q, minkB (nullVec (xk k).1) q - (xk k).2 =
      (lorentzScale (linearPart (γ⁻¹ ^ k)) x.1)⁻¹ * (minkB n ((γ ^ k) • q) - x.2) := by
    intro k q
    have hs : (γ⁻¹ ^ k) • ((γ ^ k) • q) = q := by rw [inv_pow, inv_smul_smul]
    have := minkB_isomPenrose (γ⁻¹ ^ k) x ((γ ^ k) • q)
    rw [hs] at this
    exact this
  set r : ℕ → ℝ := fun k => (lorentzScale (linearPart (γ⁻¹ ^ k)) x.1)⁻¹ / l ^ k with hr
  have hrΦ : ∀ k q, minkB (nullVec (xk k).1) q - (xk k).2 = r k * Φ k q := by
    intro k q
    rw [hrel k q]
    simp only [hr, hΦ]
    have : l ^ k ≠ 0 := pow_ne_zero k hl0.ne'
    field_simp
  set et : Minkowski d := ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin d))) with het
  have hmet : ∀ u : PenroseSphere d, minkB (nullVec u) et = -1 := fun u => by
    rw [minkB_nullVec]; simp [het]
  have hnorm : ∀ k, r k = -1 / (Φ k et - Φ k 0) := by
    intro k
    have h1 := hrΦ k et
    have h0 := hrΦ k 0
    rw [hmet] at h1
    rw [minkB_zero_right] at h0
    have hprod : r k * (Φ k et - Φ k 0) = -1 := by rw [mul_sub]; linarith
    have hD0 : Φ k et - Φ k 0 ≠ 0 := fun h => by rw [h, mul_zero] at hprod; norm_num at hprod
    exact eq_div_of_mul_eq hD0 hprod
  have hDlim : a * (minkB n₀ et - w.2) - a * (minkB n₀ 0 - w.2) = -a := by
    rw [hn₀, hmet, minkB_zero_right]; ring
  have hrlim : Tendsto r atTop (𝓝 (-1 / -a)) := by
    have := (tendsto_const_nhds (x := (-1 : ℝ))).div ((hlim et).sub (hlim 0))
      (by rw [hDlim]; exact neg_ne_zero.2 ha0)
    rw [hDlim] at this
    exact this.congr fun k => (hnorm k).symm
  have hφlim : ∀ q, Tendsto (fun k => minkB (nullVec (xk k).1) q - (xk k).2) atTop
      (𝓝 (minkB n₀ q - w.2)) := by
    intro q
    have := hrlim.mul (hlim q)
    rw [show -1 / -a * (a * (minkB n₀ q - w.2)) = minkB n₀ q - w.2 by field_simp] at this
    exact this.congr fun k => (hrΦ k q).symm
  -- the two coordinates
  have h2 : Tendsto (fun k => (xk k).2) atTop (𝓝 w.2) := by
    have := (hφlim 0).neg
    simp only [minkB_zero_right, zero_sub, neg_neg] at this
    exact this
  have h1 : Tendsto (fun k => (xk k).1) atTop (𝓝 w.1) := by
    rw [tendsto_subtype_rng, tendsto_iff_norm_sub_tendsto_zero]
    have hsq : Tendsto (fun k => ‖((xk k).1 : EuclideanSpace ℝ (Fin d)) - w.1‖ ^ 2) atTop
        (𝓝 0) := by
      have := ((hφlim n₀).sub (hφlim 0)).const_mul (-2)
      rw [show (-2) * ((minkB n₀ n₀ - w.2) - (minkB n₀ 0 - w.2)) = 0 by
        rw [← minkQ_eq_minkB, hq₀, minkB_zero_right]; ring] at this
      refine this.congr fun k => ?_
      rw [minkB_zero_right, hn₀, minkB_nullVec_nullVec]; ring
    have := (Real.continuous_sqrt.tendsto 0).comp hsq
    rw [Real.sqrt_zero] at this
    exact this.congr fun k => Real.sqrt_sq (norm_nonneg _)
  exact (Prod.tendsto_iff _ _).2 ⟨h1, h2⟩


/-- **`bprop:admlox`, minimality in `𝒥`** (l.1232–1238): `Λ(Γ)` is contained in every nonempty
closed `Γ`-invariant subset of `𝒥`. -/
theorem limitSetJ_subset (hL : LimitSetMinimal d) (hΓ : DiscreteTopology (linearImage Γ))
    (hfix : ¬HasGlobalFixedPoint (linearImage Γ)) {F : Set (PenroseSphere d × ℝ)}
    (hF : IsClosed F) (hne : F.Nonempty) (hinv : ∀ η ∈ Γ, isomPenrose η '' F ⊆ F) :
    limitSetJ Γ ⊆ F := by
  refine closure_minimal (fun w hw => ?_) hF
  obtain ⟨γ, hγ, hr⟩ := hw
  obtain ⟨w', hr'⟩ := exists_isRepulsiveFixedJ (isLoxodromic_linOf_inv hr.1)
  obtain ⟨x, hxF, hx⟩ : ∃ x ∈ F, x.1 ≠ w'.1 := by
    by_contra hall'
    have hall : ∀ x ∈ F, x.1 = w'.1 := fun x hx => by_contra fun h => hall' ⟨x, hx, h⟩
    have hsph : IsSphereInvariant (linearImage Γ) {w'.1} := by
      rintro A hA u rfl
      obtain ⟨η, hη, rfl⟩ := Subgroup.mem_map.1 hA
      obtain ⟨y, hy⟩ := hne
      have h1 : lorentzSphere (linearPart η) y.1 = w'.1 := hall _ (hinv η hη ⟨y, hy, rfl⟩)
      rw [hall y hy] at h1
      exact h1
    have hw1 := hL _ hΓ hfix {w'.1} isClosed_singleton (singleton_nonempty _) hsph
      (fst_image_loxRepSet_subset Γ ⟨w, ⟨γ, hγ, hr⟩, rfl⟩)
    exact hr.fst_ne hr' hw1
  exact hF.mem_of_tendsto (tendsto_isomPenrose_inv_pow hr hr' hx)
    (Eventually.of_forall fun k => hinv _ (Γ.pow_mem (Γ.inv_mem hγ) k) ⟨x, hxF, rfl⟩)

/-- **`bprop:admlox`** (Prop 4.17, l.1230–1238), the formalization of record (DEC-96): for an
admissible `Γ` (subgroup form, `IsAdmissible`), `Λ(Γ)` is `Γ`-invariant in `𝒥` and contained in
every **nonempty** closed `Γ`-invariant subset of `𝒥` ('nonempty' the evident intent: the empty
set is closed and invariant), the cited limit-set dynamics (l.1246–1254) entering as the named
external `LimitSetMinimal` (DEC-36). -/
theorem bprop_admlox (hL : LimitSetMinimal d) (hΓ : IsAdmissible Γ) :
    (∀ η ∈ Γ, isomPenrose η '' limitSetJ Γ ⊆ limitSetJ Γ) ∧
      ∀ F : Set (PenroseSphere d × ℝ), IsClosed F → F.Nonempty →
        (∀ η ∈ Γ, isomPenrose η '' F ⊆ F) → limitSetJ Γ ⊆ F := by
  obtain ⟨hD, hfix⟩ : DiscreteTopology (linearImage Γ) ∧ ¬HasGlobalFixedPoint (linearImage Γ) := by
    rcases hΓ with h | h
    · exact ⟨h.2.1, h.2.2.1⟩
    · exact ⟨h.2.1, h.2.2.1⟩
  exact ⟨fun η hη => isomPenrose_image_limitSetJ_subset hη,
    fun F hF hne hinv => limitSetJ_subset hL hD hfix hF hne hinv⟩

end Admlox


end Causal.Flat
