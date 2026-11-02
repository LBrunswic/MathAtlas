import Causal.Flat.Quotient
import Causal.Flat.LipschitzGraph
import Causal.Flat.Cosmological

/-!
# `Causal.Flat.Examples` — the elementary models: translation, Misner and unipotent spacetimes; Rem 2.2 completed; Rem 2.3 refuted by the slab

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §2.4 and
§3. **No b-label is certified**: every item here is prose without a ledger environment ([3.T],
[3.M], [3.U]) or a remark (`\rquea`: Rem 2.2, Rem 2.3 `clomax`), which the ledger does not track.
Line numbers are those of the **labelled** `papers/barbot/legacy/labeled/GHFspace.tex`. Status:
Rem 2.2 completed (GH + Cauchy, MGH not proved); Rem 2.3 as printed refuted (DEC-44); [3.T] and
[3.M] partial (every frame `φ`; completeness not stated; the past Misner wedge not treated); [3.U]
partial (`S_f` Cauchy and its descent to an acausal Cauchy surface proved, in every frame
`φ`; Barbot-GH of the quotient in every frame; ETT's GH of the quotient,
completeness and a witness not done). Sorry-free.

> in \mink, let $\Omega$ be a connected component of the negative cone $\{ Q< 0 \}$.
> Then, $S = \Omega \cap \{ Q=-1 \}$ is a Cauchy hypersurface for $\Omega$.
> Observe that $\Omega$ is MGH, but nontrivially embedded in ${\bf M}^{n}$! (l.541–543)

> Cauchy-compact GH spacetimes are automatically absolutely maximal. Indeed, any spacelike
> hypersurface in a given CGH spacetime is a Cauchy hypersurface. (l.576–578)

> they are the quotients of the entire \mink by a group of translations by spacelike
> translation vectors. (l.588–590)

> let $G_{0}$ be the subgroup of $\mbox{Isom}({\bf M}^{n})$ formed by elements with linear parts
> in $\gamma_{0}^{t}$ and translations parts in the subspace $\{ x = y = 0 \}$. […] If $\Gamma$ is
> any discrete subgroup of $G_{0}$, the quotient $\Gamma\backslash\Omega$ is a flat globally
> hyperbolic spacetime, that we call \emph{Misner spacetime.\/} (l.606–612)

> Let $f: I=]y_{j}, y_{j+1}[ \rightarrow {\mathbb R}$ be any
> (strictly) increasing function. (l.676–677)

> We now prove that $S_{f}$ is a Cauchy hypersurface for $\Omega$. […] Hence, any nonspacelike
> geodesic intersect $S_{f}$: this is a criteria proving that $S_{f}$ is indeed a Cauchy
> hypersurface. (l.728–741)

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; `Minkowski d =
ℝ × EuclideanSpace ℝ (Fin d)` has `d` spatial dimensions: Barbot's `n` is `d + 1`. The Misner and
unipotent sections work in `Minkowski (d + 1)` (`n = d + 2 ≥ 2`, `z ∈ ℝ^{n−2} = ℝᵈ`).

## What is proved

* **Open subsets.** `flat_le_top_subtype_iff`, `globallyHyperbolic_subtype`: an open `W ⊆ 𝐌ⁿ`
  globally hyperbolic in `𝐌ⁿ` is GH as a flat spacetime.
* **Rem 2.2, completed** (`rem22_cone`, `0 < d`): the future cone `Ω` is GH, the hyperboloid
  `S = Ω ∩ {Q = −1}` is a Cauchy surface of `Ω` (both readings), `Ω = D(S)` exactly
  (`LipschitzGraph.dependenceDomain_hyperboloid`), and `S` is not Cauchy in `𝐌ⁿ`; through
  `Cosmological` (`S` = the level `T = 1` of the cosmological time of `Ω⁺(𝒮 × {0})`,
  `cosmoLevel_cone_one`), bypassing what was `LipschitzGraph`'s `SORRY(D-cauchy-interior)` (since
  closed there: `isCauchySurfaceOn_interior_dependenceDomain`, no `sorry`).
* **The causal order of `Γ\Ω` lifts** (`exists_lift_le`, through absolute minimality: a chain of
  relations in sheets lifts step by step), hence **`Γ\Ω` is causal under an acausal action**
  (`isCausal_of_actsAcausally`, an item of `Flat.Quotient`'s SCOPE), images of invariant acausal
  sets are acausal (`isAcausal_image`), `diamond_proj`, and **ETT's GH descends**
  (`globallyHyperbolic_quotient`, `gh_toFlatSpacetime`) when only finitely many `γ` have `x ≤ γ y`.
* **Slabs** `{a < t < b}`: GH in `𝐌ⁿ`, and every slice `t = c` is a Cauchy surface of the slab for
  every inextensible causal curve (`isCauchySurfaceOn_timeSlab`, relative extension lemmas).
* **[3.T]**: `horizGroup Λ` (translations by `(0, v)`, `v ∈ Λ`), free, properly discontinuous for
  ball-finite (discrete) `Λ`, acausal, finitely related; `Λ\𝐌ⁿ` is GH (`gh_translation`) with the
  invariant acausal Cauchy surface `{t = 0}` (`isCauchySurface_translation`);
  `IsTranslationSpacetime` (frames `φ`), witnesses `translation_bot` (`Γ = 1`), `ℤᵈ`
  (`isTranslationSpacetime_torusSpace`); Barbot's GH `barbotGH_translation`.
* **Rem 2.3 refuted as printed** (DEC-44): `slabSpace d = ℤᵈ\{0 < t < 1}` is GH and Cauchy-compact,
  `torusSpace d = ℤᵈ\𝐌ⁿ` is a GH Cauchy-compact translation spacetime, the induced map is an
  isometric embedding (`isIsometricEmbedding_quotInclusion`, general) and not onto
  (`slab_embedding`); `not_cauchyCompact_absMax`: no class `CC ⊇ CauchyCompact` makes "GH +
  Cauchy-compact ⇒ `AbsMax CC`" true.
* **Regular-domain quotients** (general): for `CosmoRegular Λ` and a free, properly discontinuous
  `Γ` preserving `Ω⁺(Λ)`, the action is acausal, finitely related, `Γ\Ω⁺(Λ)` is GH
  (`gh_quotient_omegaPlus`) and every level `S_t` descends to an acausal Cauchy surface.
* **[3.M]**: null coordinates `nullX nullY nullZ` (`minkQ_eq_null`: `Q = 2xy + |z|²`), the boost
  `axisBoost s ∈ SO₀(1, d + 1)` (`det_boost` by a conjugation trick), `misnerMap (s, w)`,
  `misnerHom`, `misnerGroup L`; the wedge `{xy < 0, x > 0}` is `Ω⁺(misnerΛ)`
  (`mem_omegaPlus_misnerΛ`, `misnerRegular`); free, properly discontinuous for ball-finite `L`;
  `gh_misner`, `isCauchySurface_misner`, and these Cauchy surfaces are the paper's `η`-slices
  (`cosmoTime_misner`: `T = √(t² − x₁²) = √(−2xy)`, `cosmoLevel_misner`);
  `IsMisnerSpacetime` (with F1's nonzero boost); Barbot's GH `barbotGH_misner`;
  `misner_example` (`Γ = ℤ (s₀, w₀)`, `s₀ ≠ 0`).
* **[3.U]**: `ofNull`, `unipAction` (the action of `A`), `unipDomain α β`, `IsUnipComponent`,
  `unipPhi`, `unipSlice` (`S_f`), `IsUnipotentSpacetime`; `S_f` and `Ω` are `A`-invariant
  (`unipAction_mem_unipSlice`, `unipAction_mem_unipDomain`). **`S_f` is a Cauchy surface of `Ω`
  for every inextensible causal curve** (`isCauchySurfaceOn_unipSlice`, `f` strictly increasing,
  continuous, unbounded at both ends), through the time function `unipTime` `T = x − Φ(y, z)`:
  `A`-invariant (`unipTime_unipAction`), strictly increasing along `≤` (`unipTime_lt`, from the
  three-term decomposition `unipTime_sub`), and a bound on `T` bounds the curve
  (`nullX_sub_le_aux`, `future/pastExtensible_unipDomain`). A free group acting through `A` acts
  acausally (`actsAcausally_unip`), `S_f` descends to an acausal Cauchy surface of `Γ\Ω`
  (`isCauchySurface_unip`), and `Γ\Ω` is GH in Barbot's sense (`barbotGH_unip`).
* **Frame transport** (general): conjugation by `φ ∈ isom` carries `(Γ, Ω)` to `(φΓφ⁻¹, φΩ)`
  (`frameConjEquiv`, `frameHomeomorph`, `frameHomeomorph_smul`, `le_frameHomeomorph_iff`) and
  preserves invariance, freeness, proper discontinuity (instances), acausality, finiteness of
  `{γ | x ≤ γ y}`, `GloballyHyperbolicOn` and Cauchy surfaces (`actsAcausally_frameConj`,
  `finite_le_frameConj`, `globallyHyperbolicOn_isomImage`, `isCauchySurfaceOn_isomImage`), hence
  `gh_frameConj`, `barbotGH_frameConj`. Instances: `gh_translation_frame`,
  `barbotGH_translation_frame`, `isTranslationSpacetime_frame`; `gh_misner_frame`,
  `barbotGH_misner_frame`, `isMisnerSpacetime_frame`; `isCauchySurfaceOn_unipSlice_frame`
  (`φ S_f` Cauchy in `φΩ`), `isCauchySurface_unip_frame` (its acausal Cauchy descent, through
  `isAcausal_unipSlice`), `barbotGH_unip_frame`.

## Hypothesis checklist

| paper | here |
|---|---|
| Rem 2.2: "a connected component" of `{Q < 0}` | ⚠ strengthened: the future one, and `0 < d` (the last clause is false at `d = 0`); the past one by time reversal, not stated |
| Rem 2.2: "`Ω` is MGH" | not proved (GH and the Cauchy surface are) |
| Rem 2.3 as printed | refuted (DEC-44, under DEC-27's rule): `not_cauchyCompact_absMax`; the corrected form (lemma K: GH + Cauchy-compact + **MGH** ⇒ `AbsMax`) is DEC-44's, elsewhere |
| [3.T] translations "by spacelike vectors", discrete group | ⚠ reading: normalised to horizontal vectors `(0, v)` in a frame; discrete read as ball-finite (`BallFinite`) |
| [3.M] `Γ` discrete in `G₀`; `Ω = {xy < 0, ±x > 0}` | ⚠ strengthened (scope): `Γ = misnerGroup L`, `L` ball-finite; theorems for every frame `φ` (`*_frame`) and the sign `x > 0`; F1's nonzero boost is in `IsMisnerSpacetime`, not used by GH/Cauchy |
| [3.U] `λᵢ`, an orthogonal basis, a component, `Γ ⊆ A` discrete | ⚠ standard basis (absorbed in `φ`), `Γ` given acting by `unipAction` through ball-finite `L` |
| [3.U] `f` "any (strictly) increasing" (l.676–677), then `f = ∫ a²` (l.707–711) | ⚠ strengthened over l.676–677, weakened under l.707–711: strictly increasing, continuous, unbounded both ways on `]α, β[` (`isCauchySurfaceOn_unipSlice`); divergence at **every** end (finite poles included) is necessary — counterexample in its docstring (DEC-27 finding) |

## SCOPE (disclosed)

* **Frames.** `IsTranslationSpacetime`, `IsMisnerSpacetime`, `IsUnipotentSpacetime` quantify over a
  frame `φ ∈ isom` (`frameConj`, `isomImage`). The GH/Barbot-GH theorems (and the [3.U] acausal
  Cauchy surface `φ S_f`) hold for every `φ`, for
  the concrete quotient `φΓφ⁻¹\φΩ` (`*_frame`, by transporting the hypotheses, not by an isometry
  `Γ\Ω ≅ φΓφ⁻¹\φΩ`, which is not written). `IsQuotientOf` fixes `M` only up to homeomorphism, so
  "every `IsTranslationSpacetime M` is GH" is still not stated (the homeomorphism is not shown to
  be an isometry).
* **Completeness** of the slices (Cauchy-completeness, DEC-35) is not stated for any family: the
  `InducedLength` layer is not used. Hence no "Cauchy-complete" claim, and no AMGH claim.
* **[3.M]**: the past wedge `{xy < 0, x < 0}` is only defined (its theory is the time reversal of
  the future one, not written).
* **[3.U]**: ETT's `GH` (compact diamonds) of `Γ\Ω` is not proved (`globallyHyperbolic_quotient`
  needs "finitely many `γ` with `x ≤ γ y`", not written for `A`); `barbotGH_unip` takes the
  function `f` as data (the existence of such an `f` for every component is not written);
  completeness of `S_f` (l.712–726), "unipotent spacetimes never have closed Cauchy
  hypersurfaces" (l.746–748) and a non-vacuity witness are not attempted; `unipAction ℓ t` is not
  shown to be an element of `isom` (the groups of `IsUnipotentSpacetime` are carried abstractly).
* **Null coordinates and boosts** are defined here (`nullX/Y/Z`, `axisBoost`), deliberately
  duplicating `Isometries.stdBoost 0` (not imported: it is being edited in this wave);
  `AchronalDomains.nullXY` is a second, frame-relative null-coordinate notion. Graduation: define
  `axisBoost := stdBoost 0` or keep the duplication on record.
* **Names.** The families are `IsTranslationSpacetime`, `IsMisnerSpacetime`, `IsUnipotentSpacetime`
  (BARBOT-THEOREMS §1 says `IsTranslation`/`IsMisner`/`IsUnipotent`; `IsUnipotent` would collide
  with `Isometries.IsUnipotent`).
* `BallFinite` (finite in every ball) is used for discreteness; equivalence with discreteness of a
  subgroup of `ℝᵏ` is not proved.
* The duplicate relative extension lemmas of the interrupted draft were removed in favour of
  `Cosmological`'s `Causality.pastExtensible_of_tendsto_opens`/`futureExtensible_of_tendsto_opens`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
wave 2, package WP-31c-Examples; fixer pass 2026-10-31 (audit findings applied, the [3.U] Cauchy
`sorry` closed); closer pass 2026-11-01 (no tagged `sorry` was left; frame transport added); fixer pass
2026-11-01 (audit polish: docstrings, the [3.U] Cauchy surface exported in every frame).
-/

namespace Causal.Flat

open Set TopologicalSpace Topology Filter Function

variable {d : ℕ}

/-! ### Open subsets of `𝐌ⁿ` as flat spacetimes -/

section Opens

/-- On an open subset `W` of `𝐌ⁿ`, the flat causality of the subtype reads, on the open `⊤`, as
`≤_W` of `𝐌ⁿ`. -/
theorem flat_le_top_subtype_iff (W : Opens (Minkowski d)) (a b : W) :
    (flatCausality d W).le ⊤ a b ↔ (minkowski d).le W a b := by
  have h := ((isIsometricEmbedding_subtype_val (d := d) W).rel_iff ⊤ W
    (by rw [Opens.coe_top, image_univ, Subtype.range_coe]) a b).1
  rwa [flatCausality_self] at h

/-- **An open subset of `𝐌ⁿ` that is globally hyperbolic in `𝐌ⁿ` is GH as a flat spacetime.** -/
theorem globallyHyperbolic_subtype (W : Opens (Minkowski d))
    (h : (minkowski d).GloballyHyperbolicOn W) : (flatCausality d W).GloballyHyperbolic := by
  refine ⟨fun a b hab hba => Subtype.ext (h.1 ((flat_le_top_subtype_iff W a b).1 hab)
    ((flat_le_top_subtype_iff W b a).1 hba)), fun p q => ?_⟩
  have hD : (flatCausality d W).diamond ⊤ p q =
      Subtype.val ⁻¹' (minkowski d).diamond W (p : Minkowski d) q := by
    ext z
    simp only [Causality.mem_diamond, mem_preimage, flat_le_top_subtype_iff]
  rw [hD, Subtype.isCompact_iff, image_preimage_eq_inter_range, Subtype.range_coe,
    inter_eq_left.2 fun z hz => (minkowski d).le_mem_left ((Causality.mem_diamond.1 hz).2)]
  exact h.2 p q

end Opens

/-! ### Rem 2.2: the future cone and the hyperboloid -/

section Rem22

/-- The future cone is the regular domain `Ω⁺(𝒮 × {0})` of `Flat.Cosmological`, as open sets. -/
theorem futureTimelikeCone_eq_opens (hd : 0 < d) :
    futureTimelikeCone d = (cosmoRegular_cone hd).regular.opens :=
  Opens.ext (omegaPlus_cone hd).symm

/-- On the future cone the level set `T = 1` of the cosmological time is the hyperboloid. -/
theorem cosmoLevel_cone_one (hd : 0 < d) :
    cosmoLevel (univ ×ˢ {0} : Set (PenroseSphere d × ℝ)) 1 = graph (hyperboloid d) := by
  rw [graph_hyperboloid]
  ext p
  simp only [cosmoLevel, mem_setOf_eq, omegaPlus_cone hd]
  constructor
  · rintro ⟨hp, hT⟩
    rw [(cosmoTime_cone hd hp).1, Real.sqrt_eq_one] at hT
    exact ⟨by linarith, hp.1⟩
  · rintro ⟨hQ, ht⟩
    have hp : IsFutureTimelike p := ⟨ht, by linarith⟩
    refine ⟨hp, ?_⟩
    rw [(cosmoTime_cone hd hp).1, hQ, neg_neg, Real.sqrt_one]

/-- **Rem 2.2, completed** (l.540–545, `d ≥ 1`, Barbot's `n ≥ 2`): the future component `Ω` of
`{Q < 0}` is globally hyperbolic as a flat spacetime (ETT's GH: causal, compact diamonds), the
hyperboloid `S = Ω ∩ {Q = −1}` is a Cauchy surface of `Ω` (read in `𝐌ⁿ` on the open set `Ω`, and
as a flat spacetime on the subtype), `Ω` is exactly the domain of dependence of `S` in `𝐌ⁿ`, and
`S` is no Cauchy surface of `𝐌ⁿ`, so the inclusion `Ω ⊆ 𝐌ⁿ` is not a Cauchy embedding. -/
theorem rem22_cone (hd : 0 < d) :
    GH (futureTimelikeConeSpace d) ∧
      (minkowski d).IsCauchySurfaceOn (futureTimelikeCone d) (graph (hyperboloid d)) ∧
      (flatCausality d (futureTimelikeCone d)).IsCauchySurface
        (Subtype.val ⁻¹' graph (hyperboloid d)) ∧
      dependenceDomain (minkowski d) ⊤ (graph (hyperboloid d)) =
        (futureTimelikeCone d : Set (Minkowski d)) ∧
      ¬ (minkowski d).IsCauchySurface (graph (hyperboloid d)) := by
  have h := cosmoRegular_cone hd
  have hW := futureTimelikeCone_eq_opens hd
  have hC : (minkowski d).IsCauchySurfaceOn (futureTimelikeCone d) (graph (hyperboloid d)) := by
    rw [hW, ← cosmoLevel_cone_one hd]
    exact isCauchySurfaceOn_cosmoLevel h one_pos
  refine ⟨?_, hC, (FlatQuotient.isCauchySurfaceOn_iff _ ?_).1 hC, dependenceDomain_hyperboloid hd,
    not_isCauchySurface_graph_hyperboloid_of_criterion hd⟩
  · show (flatCausality d (futureTimelikeCone d)).GloballyHyperbolic
    refine globallyHyperbolic_subtype _ ?_
    rw [hW]
    exact h.regular.globallyHyperbolicOn
  · intro p hp
    rw [graph_hyperboloid] at hp
    exact ⟨hp.2, by linarith [hp.1]⟩

end Rem22

/-! ### The causal order of a quotient `Γ\Ω` lifts -/

namespace FlatQuotient

variable (Γ : Subgroup (isom d)) (Ω : Opens (Minkowski d)) [Invariant Γ Ω]
  [ProperlyDiscontinuousSMul Γ Ω] [IsCancelSMul Γ Ω]

omit [ProperlyDiscontinuousSMul Γ Ω] [IsCancelSMul Γ Ω] in
/-- The action of `Γ` preserves the flat causal relation of `Ω` on `⊤`. -/
theorem le_top_smul {a b : Ω} (γ : Γ) (h : (flatCausality d Ω).le ⊤ a b) :
    (flatCausality d Ω).le ⊤ (γ • a) (γ • b) := by
  rw [flat_le_top_subtype_iff] at h ⊢
  have hΩ : isomImage (γ : isom d) Ω = Ω := by
    apply isomImage_eq_of_coe_eq_preimage
    ext p
    refine ⟨fun hp => Invariant.smul_mem γ p hp, fun hp => ?_⟩
    have := Invariant.smul_mem γ⁻¹ _ hp
    simpa using this
  have := (le_iff_le_isomImage (γ : isom d) Ω a b).1 h
  rwa [hΩ] at this

/-- Every point of `Ω` has an open neighbourhood in `Ω` on which the projection is injective. -/
theorem exists_sheet (x : Ω) : ∃ U : Opens Ω, x ∈ U ∧ InjOn (proj Γ Ω) U := by
  obtain ⟨U, hU, hUγ⟩ := exists_nhds_smul_eq_one Γ Ω x x.2
  refine ⟨⟨Subtype.val ⁻¹' interior U, isOpen_interior.preimage continuous_subtype_val⟩,
    mem_interior_iff_mem_nhds.2 hU, fun a ha b hb hab => ?_⟩
  obtain ⟨γ, hγ⟩ := proj_eq_proj_iff.1 hab
  have h1 := hUγ γ b b.2 (interior_subset hb) (by
    have : ((γ • b : Ω) : Minkowski d) = a := congrArg Subtype.val hγ
    rw [← coe_smul, this]; exact interior_subset ha)
  rw [← hγ, h1, one_smul]

/-- **A relation in a sheet lifts**: if the projection is injective on the open `U ⊆ Ω`, a
relation `π a ≤_{π U} π b` of `Γ\Ω` between points of `U` is the image of `a ≤ b` in `Ω`. -/
theorem le_top_of_le_sheet {U : Opens Ω} (hU : InjOn (proj Γ Ω) U) {a b : Ω} (ha : a ∈ U)
    (hb : b ∈ U)
    (h : (flatCausality d (FlatQuotient Γ Ω)).le ⟨proj Γ Ω '' U, isOpenMap_proj Γ Ω _ U.2⟩
      (proj Γ Ω a) (proj Γ Ω b)) :
    (flatCausality d Ω).le ⊤ a b := by
  have hf : IsIsometricEmbedding d (proj Γ Ω ∘ (Subtype.val : U → Ω)) :=
    ⟨(isLocalIsometry_proj Γ Ω).comp (isLocalIsometry_subtype_val U),
      fun u v huv => Subtype.ext (hU u.2 v.2 huv)⟩
  have h1 := ((hf.rel_iff ⊤ ⟨proj Γ Ω '' U, isOpenMap_proj Γ Ω _ U.2⟩ (by
    simp only [Opens.coe_top, image_univ, Opens.coe_mk]
    rw [range_comp, Subtype.range_coe]) ⟨a, ha⟩ ⟨b, hb⟩).1).2 h
  have h2 := (((isIsometricEmbedding_subtype_val (d := d) U).rel_iff ⊤ U
    (by rw [Opens.coe_top, image_univ, Subtype.range_coe]) ⟨a, ha⟩ ⟨b, hb⟩).1).1 h1
  exact (flatCausality d Ω).le_mono le_top h2

/-- The sheets of the projection, as an open cover of `Γ\Ω`. -/
def sheets : Set (Opens (FlatQuotient Γ Ω)) :=
  {O | ∃ U : Opens Ω, InjOn (proj Γ Ω) U ∧ (O : Set (FlatQuotient Γ Ω)) = proj Γ Ω '' U}

/-- One step of a chain in a sheet lifts from any lift of its origin. -/
theorem exists_lift_step {O : Opens (FlatQuotient Γ Ω)} (hO : O ∈ sheets Γ Ω) {q q' : FlatQuotient Γ Ω}
    (h : (flatCausality d (FlatQuotient Γ Ω)).le O q q') {x : Ω} (hx : proj Γ Ω x = q) :
    ∃ y : Ω, proj Γ Ω y = q' ∧ (flatCausality d Ω).le ⊤ x y := by
  obtain ⟨U, hU, hOU⟩ := hO
  have hO' : O = ⟨proj Γ Ω '' U, isOpenMap_proj Γ Ω _ U.2⟩ := Opens.ext hOU
  subst hO'
  obtain ⟨u, hu, rfl⟩ := (flatCausality d (FlatQuotient Γ Ω)).le_mem_left h
  obtain ⟨v, hv, rfl⟩ := (flatCausality d (FlatQuotient Γ Ω)).le_mem_right h
  have huv := le_top_of_le_sheet Γ Ω hU hu hv h
  obtain ⟨γ, hγ⟩ := proj_eq_proj_iff.1 hx
  refine ⟨γ • v, proj_eq_proj_iff.2 ⟨γ, rfl⟩, ?_⟩
  rw [← hγ]
  exact le_top_smul Γ Ω γ huv

/-- **The causal order of `Γ\Ω` lifts**: if `π x ≤ q` in `Γ\Ω`, some lift `y` of `q` has
`x ≤ y` in `Ω`. Through absolute minimality of the flat causality (chains of relations in sheets)
and the local isometry of the projection on each sheet. -/
theorem exists_lift_le {x : Ω} {q : FlatQuotient Γ Ω}
    (h : (flatCausality d (FlatQuotient Γ Ω)).le ⊤ (proj Γ Ω x) q) :
    ∃ y : Ω, proj Γ Ω y = q ∧ (flatCausality d Ω).le ⊤ x y := by
  have hcov : ∀ z ∈ (⊤ : Opens (FlatQuotient Γ Ω)), ∃ O ∈ sheets Γ Ω, z ∈ O := by
    intro z _
    obtain ⟨x', rfl⟩ := proj_surjective Γ Ω z
    obtain ⟨U, hxU, hU⟩ := exists_sheet Γ Ω x'
    exact ⟨⟨proj Γ Ω '' U, isOpenMap_proj Γ Ω _ U.2⟩, ⟨U, hU, rfl⟩, x', hxU, rfl⟩
  have hch := ((Precausality.absolutelyMinimal_iff.1
    (flatCausality_absolutelyMinimal (d := d) (M := FlatQuotient Γ Ω))) (sheets Γ Ω) hcov ⊤ le_rfl
    (proj Γ Ω x) q).1 h
  clear h
  induction hch with
  | single hab =>
    obtain ⟨O, hO, hle⟩ := hab
    exact exists_lift_step Γ Ω hO ((flatCausality d _).le_mono inf_le_right hle) rfl
  | tail _ hbc ih =>
    obtain ⟨y, hy, hxy⟩ := ih
    obtain ⟨O, hO, hle⟩ := hbc
    obtain ⟨z, hz, hyz⟩ := exists_lift_step Γ Ω hO ((flatCausality d _).le_mono inf_le_right hle) hy
    exact ⟨z, hz, (flatCausality d Ω).le_trans hxy hyz⟩

/-- The projection preserves the causal relation on `⊤`. -/
theorem proj_le_proj {a b : Ω} (h : (flatCausality d Ω).le ⊤ a b) :
    (flatCausality d (FlatQuotient Γ Ω)).le ⊤ (proj Γ Ω a) (proj Γ Ω b) :=
  (strongMorphism_proj Γ Ω).le_of_mapsTo (U := ⊤) (V := ⊤) (fun _ _ => trivial) h

/-- The flat causality of `Ω ⊆ 𝐌ⁿ` is causal. -/
theorem isCausal_subtype : (flatCausality d Ω).IsCausal := fun a b hab hba =>
  Subtype.ext (minkowski_isCausal ((minkowski d).le_mono le_top ((flat_le_top_subtype_iff Ω a b).1 hab))
    ((minkowski d).le_mono le_top ((flat_le_top_subtype_iff Ω b a).1 hba)))

/-- **`Γ\Ω` is causal when `Γ` acts acausally** (closes the item of `Flat.Quotient`'s SCOPE). -/
theorem isCausal_of_actsAcausally (hac : ActsAcausally Γ Ω) :
    (flatCausality d (FlatQuotient Γ Ω)).IsCausal := by
  intro q q' h h'
  obtain ⟨x, rfl⟩ := proj_surjective Γ Ω q
  obtain ⟨y, rfl, hxy⟩ := exists_lift_le Γ Ω h
  obtain ⟨x', hx', hyx'⟩ := exists_lift_le Γ Ω h'
  obtain ⟨γ, hγ⟩ := proj_eq_proj_iff.1 hx'
  -- `x' = γ • x`, and `x ≤ γ • x` forces `γ = 1`
  have hxx : (flatCausality d Ω).le ⊤ x (γ • x) := by
    rw [hγ]; exact (flatCausality d Ω).le_trans hxy hyx'
  have hγ1 : γ = 1 := by
    by_contra hne
    exact hac γ hne x hxx
  rw [hγ1, one_smul] at hγ
  rw [← hγ] at hyx'
  rw [isCausal_subtype Ω hxy hyx']

/-- **The image of a `Γ`-invariant acausal set of `Ω` is acausal in `Γ\Ω`.** -/
theorem isAcausal_image {S : Set Ω} (hinv : ∀ γ : Γ, ∀ p ∈ S, γ • p ∈ S)
    (hS : (flatCausality d Ω).IsAcausal S) :
    (flatCausality d (FlatQuotient Γ Ω)).IsAcausal (proj Γ Ω '' S) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ h
  obtain ⟨y, hy, hay⟩ := exists_lift_le Γ Ω h
  obtain ⟨γ, hγ⟩ := proj_eq_proj_iff.1 hy
  have hyS : y ∈ S := hγ ▸ hinv γ b hb
  rw [hS a ha y hyS hay, hy]

/-- **The diamonds of `Γ\Ω` are projections of diamonds of `Ω`**: `J(π x, π y)` is the image of
the union of the `J(x, γ y)` over the `γ` with `x ≤ γ y`. -/
theorem diamond_proj (x y : Ω) :
    (flatCausality d (FlatQuotient Γ Ω)).diamond ⊤ (proj Γ Ω x) (proj Γ Ω y) =
      proj Γ Ω '' ⋃ γ ∈ {γ : Γ | (flatCausality d Ω).le ⊤ x (γ • y)},
        (flatCausality d Ω).diamond ⊤ x (γ • y) := by
  ext z
  constructor
  · intro hz
    rw [Causality.mem_diamond] at hz
    obtain ⟨w, rfl, hxw⟩ := exists_lift_le Γ Ω hz.1
    obtain ⟨y', hy', hwy'⟩ := exists_lift_le Γ Ω hz.2
    obtain ⟨γ, hγ⟩ := proj_eq_proj_iff.1 hy'
    refine ⟨w, mem_iUnion₂.2 ⟨γ, ?_, ?_⟩, rfl⟩
    · show (flatCausality d Ω).le ⊤ x (γ • y)
      rw [hγ]; exact (flatCausality d Ω).le_trans hxw hwy'
    · rw [Causality.mem_diamond, hγ]; exact ⟨hxw, hwy'⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨γ, -, hw⟩ := mem_iUnion₂.1 hw
    rw [Causality.mem_diamond] at hw ⊢
    refine ⟨proj_le_proj Γ Ω hw.1, ?_⟩
    have := proj_le_proj Γ Ω hw.2
    rwa [show proj Γ Ω (γ • y) = proj Γ Ω y from proj_eq_proj_iff.2 ⟨γ, rfl⟩] at this

/-- **Global hyperbolicity descends** (ETT's GH: causal, compact diamonds): under an acausal
action on a GH `Ω`, if for all `x, y` only finitely many `γ` have `x ≤ γ y`. -/
theorem globallyHyperbolic_quotient (hac : ActsAcausally Γ Ω)
    (hGH : (flatCausality d Ω).GloballyHyperbolic)
    (hfin : ∀ x y : Ω, {γ : Γ | (flatCausality d Ω).le ⊤ x (γ • y)}.Finite) :
    (flatCausality d (FlatQuotient Γ Ω)).GloballyHyperbolic := by
  refine ⟨isCausal_of_actsAcausally Γ Ω hac, fun q q' => ?_⟩
  obtain ⟨x, rfl⟩ := proj_surjective Γ Ω q
  obtain ⟨y, rfl⟩ := proj_surjective Γ Ω q'
  rw [diamond_proj]
  exact ((hfin x y).isCompact_biUnion fun γ _ => hGH.2 _ _).image (continuous_proj Γ Ω)

/-- `GH` of the bundled quotient. -/
theorem gh_toFlatSpacetime (hΩ : IsConnected (Ω : Set (Minkowski d))) (hac : ActsAcausally Γ Ω)
    (hGH : (flatCausality d Ω).GloballyHyperbolic)
    (hfin : ∀ x y : Ω, {γ : Γ | (flatCausality d Ω).le ⊤ x (γ • y)}.Finite) :
    GH (toFlatSpacetime Γ Ω hΩ) :=
  globallyHyperbolic_quotient Γ Ω hac hGH hfin

end FlatQuotient

/-! ### Time slabs `{a < t < b}` and their horizontal slices -/

section Slab

/-- The open time slab `{a < t < b}` of `𝐌ⁿ`. -/
def timeSlab (d : ℕ) (a b : ℝ) : Opens (Minkowski d) :=
  ⟨{p | a < p.1 ∧ p.1 < b}, (isOpen_lt continuous_const continuous_fst).inter
    (isOpen_lt continuous_fst continuous_const)⟩

variable {a b c : ℝ}

theorem mem_timeSlab {p : Minkowski d} : p ∈ timeSlab d a b ↔ a < p.1 ∧ p.1 < b := Iff.rfl

theorem convex_timeSlab : Convex ℝ (timeSlab d a b : Set (Minkowski d)) := by
  intro p hp q hq s t hs ht hst
  have h1 : (s • p + t • q).1 = s * p.1 + t * q.1 := rfl
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hq1, hq2⟩ := hq
  refine ⟨?_, ?_⟩ <;> rw [h1]
  · have hm : 0 < min (p.1 - a) (q.1 - a) := lt_min (by linarith) (by linarith)
    have e1 := mul_le_mul_of_nonneg_left (min_le_left (p.1 - a) (q.1 - a)) hs
    have e2 := mul_le_mul_of_nonneg_left (min_le_right (p.1 - a) (q.1 - a)) ht
    have e3 : s * min (p.1 - a) (q.1 - a) + t * min (p.1 - a) (q.1 - a) =
        min (p.1 - a) (q.1 - a) := by rw [← add_mul, hst, one_mul]
    have e4 : a * s + a * t = a := by rw [← mul_add, hst, mul_one]
    nlinarith
  · have hm : 0 < min (b - p.1) (b - q.1) := lt_min (by linarith) (by linarith)
    have e1 := mul_le_mul_of_nonneg_left (min_le_left (b - p.1) (b - q.1)) hs
    have e2 := mul_le_mul_of_nonneg_left (min_le_right (b - p.1) (b - q.1)) ht
    have e3 : s * min (b - p.1) (b - q.1) + t * min (b - p.1) (b - q.1) =
        min (b - p.1) (b - q.1) := by rw [← add_mul, hst, one_mul]
    have e4 : b * s + b * t = b := by rw [← mul_add, hst, mul_one]
    nlinarith

theorem isConnected_timeSlab (hab : a < b) :
    IsConnected (timeSlab d a b : Set (Minkowski d)) :=
  convex_timeSlab.isConnected ⟨(((a + b) / 2 : ℝ), 0), by constructor <;> simp <;> linarith⟩

/-- In `𝐌ⁿ`, `p ≤ q` forces `p.1 ≤ q.1`. -/
theorem fst_le_of_le_top {p q : Minkowski d} (h : (minkowski d).le ⊤ p q) : p.1 ≤ q.1 := by
  have := minkowski_le_top_iff.1 h; linarith [norm_nonneg (q.2 - p.2)]

/-- **A time slab is globally hyperbolic in `𝐌ⁿ`**: it is convex, so its diamonds are those of
`𝐌ⁿ`, which it contains. -/
theorem globallyHyperbolicOn_timeSlab :
    (minkowski d).GloballyHyperbolicOn (timeSlab d a b) := by
  refine ⟨fun x y hxy hyx => minkowski_isCausal ((minkowski d).le_mono le_top hxy)
    ((minkowski d).le_mono le_top hyx), fun p q => ?_⟩
  by_cases hpq : p ∈ timeSlab d a b ∧ q ∈ timeSlab d a b
  · have : (minkowski d).diamond (timeSlab d a b) p q = (minkowski d).diamond ⊤ p q := by
      ext x
      simp only [Causality.mem_diamond, le_iff_of_convex convex_timeSlab]
      constructor
      · rintro ⟨⟨-, -, h1⟩, -, -, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        have hx : x ∈ timeSlab d a b :=
          ⟨hpq.1.1.trans_le (fst_le_of_le_top h1), (fst_le_of_le_top h2).trans_lt hpq.2.2⟩
        exact ⟨⟨hpq.1, hx, h1⟩, hx, hpq.2, h2⟩
    rw [this]
    exact minkowski_globallyHyperbolic.2 p q
  · have : (minkowski d).diamond (timeSlab d a b) p q = ∅ := by
      ext x
      simp only [Causality.mem_diamond, mem_empty_iff_false, iff_false, not_and]
      intro h1 h2
      exact hpq ⟨(minkowski d).le_mem_left h1, (minkowski d).le_mem_right h2⟩
    rw [this]
    exact isCompact_empty

/-- `J⁺(x) ≠ {x}` in a slab. -/
theorem Jplus_timeSlab_ne_singleton {x : Minkowski d} (hx : x ∈ timeSlab d a b) :
    (minkowski d).Jplus (timeSlab d a b) {x} ≠ {x} := by
  intro he
  set ε := (b - x.1) / 2
  have hε : 0 < ε := by have := hx.2; simp only [ε]; linarith
  have hy : x + ((ε, 0) : Minkowski d) ∈ timeSlab d a b := by
    have := hx.2; have := hx.1
    constructor <;> simp only [Prod.fst_add] <;> simp only [ε] <;> linarith
  have hmem : x + ((ε, 0) : Minkowski d) ∈ (minkowski d).Jplus (timeSlab d a b) {x} :=
    ⟨x, rfl, (le_iff_of_convex convex_timeSlab).2 ⟨hx, hy, by
      rw [minkowski_le_top_iff]; simp [hε.le]⟩⟩
  rw [he, mem_singleton_iff] at hmem
  have := congrArg Prod.fst hmem
  simp at this
  linarith

/-- `J⁻(x) ≠ {x}` in a slab. -/
theorem Jminus_timeSlab_ne_singleton {x : Minkowski d} (hx : x ∈ timeSlab d a b) :
    (minkowski d).Jminus (timeSlab d a b) {x} ≠ {x} := by
  intro he
  set ε := (x.1 - a) / 2
  have hε : 0 < ε := by have := hx.1; simp only [ε]; linarith
  have hy : x - ((ε, 0) : Minkowski d) ∈ timeSlab d a b := by
    have := hx.2; have := hx.1
    constructor <;> simp only [Prod.fst_sub] <;> simp only [ε] <;> linarith
  have hmem : x - ((ε, 0) : Minkowski d) ∈ (minkowski d).Jminus (timeSlab d a b) {x} :=
    ⟨x, rfl, (le_iff_of_convex convex_timeSlab).2 ⟨hy, hx, by
      rw [minkowski_le_top_iff]; simp [hε.le]⟩⟩
  rw [he, mem_singleton_iff] at hmem
  have := congrArg Prod.fst hmem
  simp at this
  linarith

/-- **A causal curve of a slab, over a bounded-above interval, along which `t ≤ B < b`, is
extensible in the slab at its future end.** -/
theorem futureExtensible_timeSlab {J : Set ℝ} {γ : ℝ → Minkowski d}
    (hγ : (minkowski d).CausalCurveIn (timeSlab d a b) J γ) (hJ : BddAbove J) {B : ℝ}
    (hBb : B < b) (hB : ∀ u ∈ J, (γ u).1 ≤ B) :
    (minkowski d).FutureExtensible (timeSlab d a b) J γ := by
  by_cases hmax : ∃ m, IsGreatest J m
  · obtain ⟨m, hm⟩ := hmax
    exact Causality.futureExtensible_of_isGreatest minkowski_causallyArcConnected
      minkowski_isCausal hγ hm (Jplus_timeSlab_ne_singleton (hγ.mem hm.1))
  have hlub : IsLUB J (sSup J) := isLUB_csSup hγ.nonempty hJ
  have hβJ : sSup J ∉ J := fun hβ => hmax ⟨_, hβ, hlub.1⟩
  have hlt : ∀ u ∈ J, u < sSup J := fun u hu =>
    lt_of_le_of_ne (hlub.1 hu) fun he => hβJ (he ▸ hu)
  have hle : ∀ u ∈ J, ∀ u' ∈ J, u ≤ u' → (minkowski d).le ⊤ (γ u) (γ u') :=
    fun u hu u' hu' huu' => (minkowski d).le_mono le_top (hγ.le_of_le hu hu' huu')
  obtain ⟨u₀, hu₀⟩ := hγ.nonempty
  obtain ⟨p, hp⟩ := exists_tendsto_of_bddAbove hle hγ.nonempty hγ.ordConnected hlub hβJ
    ⟨B, by rintro _ ⟨u, hu, rfl⟩; exact hB u hu⟩
  have hev : ∀ᶠ u in 𝓝[<] (sSup J), u ∈ J :=
    mem_of_superset (Ioo_mem_nhdsLT (hlt u₀ hu₀)) (Ioo_subset_of_isLUB hγ.ordConnected hlub hu₀)
  have hpΩ : p ∈ timeSlab d a b := by
    have hcl : IsClosed {y : Minkowski d | (minkowski d).le ⊤ (γ u₀) y} := by
      simp only [minkowski_le_top_iff]
      exact isClosed_le (by fun_prop) (by fun_prop)
    have h1 : (minkowski d).le ⊤ (γ u₀) p := by
      refine hcl.mem_of_tendsto hp ?_
      filter_upwards [Ioo_mem_nhdsLT (hlt u₀ hu₀)] with u hu
      exact hle u₀ hu₀ u (Ioo_subset_of_isLUB hγ.ordConnected hlub hu₀ hu) hu.1.le
    have h2 : p.1 ≤ B := by
      have hc : Tendsto (fun u => (γ u).1) (𝓝[<] (sSup J)) (𝓝 p.1) :=
        (continuous_fst.tendsto p).comp hp
      exact le_of_tendsto hc (hev.mono fun u hu => hB u hu)
    exact ⟨(hγ.mem hu₀).1.trans_le (fst_le_of_le_top h1), h2.trans_lt hBb⟩
  exact (Causality.futureExtensible_of_tendsto_opens staticCausality.isClosed_Jplus_top
    minkowski_stronglyCausal minkowski_causallyArcConnected minkowski_isCausal hγ hpΩ hlt
    (ordConnected_insert_of_isLUB hγ.ordConnected hlub) hp (Jplus_timeSlab_ne_singleton hpΩ))

/-- **A causal curve of a slab, over a bounded-below interval, along which `t ≥ A > a`, is
extensible in the slab at its past end.** -/
theorem pastExtensible_timeSlab {J : Set ℝ} {γ : ℝ → Minkowski d}
    (hγ : (minkowski d).CausalCurveIn (timeSlab d a b) J γ) (hJ : BddBelow J) {A : ℝ}
    (hAa : a < A) (hA : ∀ u ∈ J, A ≤ (γ u).1) :
    (minkowski d).PastExtensible (timeSlab d a b) J γ := by
  by_cases hmin : ∃ m, IsLeast J m
  · obtain ⟨m, hm⟩ := hmin
    exact Causality.pastExtensible_of_isLeast minkowski_causallyArcConnected minkowski_isCausal
      hγ hm (Jminus_timeSlab_ne_singleton (hγ.mem hm.1))
  have hglb : IsGLB J (sInf J) := isGLB_csInf hγ.nonempty hJ
  have hαJ : sInf J ∉ J := fun hα => hmin ⟨_, hα, hglb.1⟩
  have hgt : ∀ u ∈ J, sInf J < u := fun u hu =>
    lt_of_le_of_ne (hglb.1 hu) fun he => hαJ (he ▸ hu)
  have hle : ∀ u ∈ J, ∀ u' ∈ J, u ≤ u' → (minkowski d).le ⊤ (γ u) (γ u') :=
    fun u hu u' hu' huu' => (minkowski d).le_mono le_top (hγ.le_of_le hu hu' huu')
  obtain ⟨u₀, hu₀⟩ := hγ.nonempty
  obtain ⟨p, hp⟩ := exists_tendsto_of_bddBelow hle hγ.nonempty hγ.ordConnected hglb hαJ
    ⟨A, by rintro _ ⟨u, hu, rfl⟩; exact hA u hu⟩
  have hev : ∀ᶠ u in 𝓝[>] (sInf J), u ∈ J :=
    mem_of_superset (Ioo_mem_nhdsGT (hgt u₀ hu₀)) (Ioo_subset_of_isGLB hγ.ordConnected hglb hu₀)
  have hpΩ : p ∈ timeSlab d a b := by
    have hcl : IsClosed {y : Minkowski d | (minkowski d).le ⊤ y (γ u₀)} := by
      simp only [minkowski_le_top_iff]
      exact isClosed_le (by fun_prop) (by fun_prop)
    have h1 : (minkowski d).le ⊤ p (γ u₀) := by
      refine hcl.mem_of_tendsto hp ?_
      filter_upwards [Ioo_mem_nhdsGT (hgt u₀ hu₀)] with u hu
      exact hle u (Ioo_subset_of_isGLB hγ.ordConnected hglb hu₀ hu) u₀ hu₀ hu.2.le
    have h2 : A ≤ p.1 := by
      have hc : Tendsto (fun u => (γ u).1) (𝓝[>] (sInf J)) (𝓝 p.1) :=
        (continuous_fst.tendsto p).comp hp
      exact ge_of_tendsto hc (hev.mono fun u hu => hA u hu)
    exact ⟨hAa.trans_le h2, (fst_le_of_le_top h1).trans_lt (hγ.mem hu₀).2⟩
  exact (Causality.pastExtensible_of_tendsto_opens staticCausality.isClosed_Jminus_top
    minkowski_stronglyCausal minkowski_causallyArcConnected minkowski_isCausal hγ hpΩ hgt
    (ordConnected_insert_of_isGLB hγ.ordConnected hglb) hp (Jminus_timeSlab_ne_singleton hpΩ))

/-- **The horizontal slice `t = c` is a Cauchy surface of the slab `{a < t < b}`** (`a < c < b`;
ETT's `IsCauchySurfaceOn`, every inextensible causal curve of the slab). -/
theorem isCauchySurfaceOn_timeSlab (hac : a < c) (hcb : c < b) :
    (minkowski d).IsCauchySurfaceOn (timeSlab d a b) {p | p.1 = c} := by
  intro I γ hγ
  obtain ⟨hpi, hfi⟩ := Causality.inextensible_iff.1 hγ
  have hle : ∀ {s s' : ℝ}, s ∈ I → s' ∈ I → s ≤ s' → (minkowski d).le ⊤ (γ s) (γ s') :=
    fun hs hs' h => (minkowski d).le_mono le_top (hγ.1.le_of_le hs hs' h)
  -- some time is `≥ c`
  have hup : ∃ s ∈ I, c ≤ (γ s).1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hd, hsub, htan, -, hfut⟩ := hfi.1.arctanReparam
    exact hfi.2 (hfut (futureExtensible_timeSlab hd ⟨Real.pi / 2, fun u hu => (hsub hu).2.le⟩
      hcb fun u hu => (hcon _ (htan u hu)).le))
  have hdown : ∃ s ∈ I, (γ s).1 ≤ c := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hd, hsub, htan, hpast, -⟩ := hpi.1.arctanReparam
    exact hpi.2 (hpast (pastExtensible_timeSlab hd ⟨-(Real.pi / 2), fun u hu => (hsub hu).1.le⟩
      hac fun u hu => (hcon _ (htan u hu)).le))
  obtain ⟨s₂, hs₂, h₂⟩ := hup
  obtain ⟨s₁, hs₁, h₁⟩ := hdown
  have huniq : ∀ s ∈ I, ∀ s' ∈ I, (γ s).1 = c → (γ s').1 = c → γ s = γ s' := by
    intro s hs s' hs' h h'
    rcases le_total s s' with hss | hss
    · have := minkowski_le_top_iff.1 (hle hs hs' hss)
      rw [h, h', sub_self] at this
      exact Prod.ext (h.trans h'.symm) (sub_eq_zero.1 (norm_le_zero_iff.1 this)).symm
    · have := minkowski_le_top_iff.1 (hle hs' hs hss)
      rw [h, h', sub_self] at this
      exact Prod.ext (h.trans h'.symm) (sub_eq_zero.1 (norm_le_zero_iff.1 this))
  have hex : ∃ s ∈ I, (γ s).1 = c := by
    rcases le_total s₁ s₂ with h12 | h12
    · have hsub : Icc s₁ s₂ ⊆ I := hγ.1.ordConnected.out hs₁ hs₂
      have hcont : ContinuousOn (fun s => (γ s).1) (Icc s₁ s₂) :=
        continuous_fst.comp_continuousOn (hγ.1.continuousOn_Icc hs₁ hs₂)
      obtain ⟨s, hs, hst⟩ := intermediate_value_Icc h12 hcont ⟨h₁, h₂⟩
      exact ⟨s, hsub hs, hst⟩
    · have := fst_le_of_le_top (hle hs₂ hs₁ h12)
      exact ⟨s₁, hs₁, le_antisymm h₁ (h₂.trans this)⟩
  obtain ⟨s, hs, hsc⟩ := hex
  refine ⟨γ s, ⟨⟨s, hs, rfl⟩, hsc⟩, ?_⟩
  rintro _ ⟨⟨s', hs', rfl⟩, hs'c⟩
  exact huniq s' hs' s hs hs'c hsc

/-- A horizontal slice is acausal in `𝐌ⁿ`. -/
theorem isAcausal_timeSlice (c : ℝ) : (minkowski d).IsAcausal {p : Minkowski d | p.1 = c} := by
  intro x hx y hy hxy
  have := minkowski_le_top_iff.1 hxy
  rw [show y.1 - x.1 = 0 by rw [hx, hy]; ring] at this
  exact Prod.ext (hx.trans hy.symm) (sub_eq_zero.1 (norm_le_zero_iff.1 this)).symm

end Slab

/-! ### [3.T] Translation spacetimes -/

section Translation

variable (d) in
/-- `v ↦` the translation by the horizontal (spacelike) vector `(0, v)`. -/
noncomputable def horizTranslation : Multiplicative (EuclideanSpace ℝ (Fin d)) →* isom d where
  toFun v := ⟨AffineEquiv.constVAdd ℝ (Minkowski d) ((0 : ℝ), Multiplicative.toAdd v),
    constVAdd_mem_isom _⟩
  map_one' := by
    apply Subtype.ext
    ext p
    · simp
    · simp
  map_mul' a b := by
    apply Subtype.ext
    ext p
    · simp
    · simp [add_assoc]

theorem horizTranslation_smul (v : Multiplicative (EuclideanSpace ℝ (Fin d))) (p : Minkowski d) :
    horizTranslation d v • p = ((0 : ℝ), Multiplicative.toAdd v) + p := rfl

@[simp] theorem fst_horizTranslation_smul (v : Multiplicative (EuclideanSpace ℝ (Fin d)))
    (p : Minkowski d) : (horizTranslation d v • p).1 = p.1 := by
  rw [horizTranslation_smul]; simp

@[simp] theorem snd_horizTranslation_smul (v : Multiplicative (EuclideanSpace ℝ (Fin d)))
    (p : Minkowski d) : (horizTranslation d v • p).2 = Multiplicative.toAdd v + p.2 := by
  rw [horizTranslation_smul]; simp

/-- **The group of horizontal translations by the vectors of `Λ`.** -/
noncomputable def horizGroup (Λ : AddSubgroup (EuclideanSpace ℝ (Fin d))) : Subgroup (isom d) :=
  (AddSubgroup.toSubgroup Λ).map (horizTranslation d)

theorem mem_horizGroup {Λ : AddSubgroup (EuclideanSpace ℝ (Fin d))} {γ : isom d} :
    γ ∈ horizGroup Λ ↔ ∃ v ∈ Λ, horizTranslation d (Multiplicative.ofAdd v) = γ := by
  simp only [horizGroup, Subgroup.mem_map]
  constructor
  · rintro ⟨v, hv, rfl⟩; exact ⟨Multiplicative.toAdd v, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩; exact ⟨Multiplicative.ofAdd v, hv, rfl⟩

/-- **Discreteness, in its metric form**: `Λ` meets every ball in a finite set (for a subgroup of
`ℝᵈ`, equivalent to discreteness; the equivalence is not proved here). -/
class BallFinite {V : Type*} [SeminormedAddCommGroup V] (Λ : AddSubgroup V) : Prop where
  finite_ball : ∀ R : ℝ, {v | v ∈ Λ ∧ ‖v‖ ≤ R}.Finite

variable (Λ : AddSubgroup (EuclideanSpace ℝ (Fin d)))

/-- The time slabs are invariant under the horizontal translations. -/
instance instInvariantHorizTimeSlab (a b : ℝ) : FlatQuotient.Invariant (horizGroup Λ) (timeSlab d a b) :=
  ⟨fun γ p hp => by
    obtain ⟨v, -, hv⟩ := mem_horizGroup.1 γ.2
    rw [← hv]
    exact ⟨by rw [fst_horizTranslation_smul]; exact hp.1, by rw [fst_horizTranslation_smul]; exact hp.2⟩⟩

instance instInvariantHorizTop : FlatQuotient.Invariant (horizGroup Λ) (⊤ : Opens (Minkowski d)) :=
  ⟨fun _ _ _ => trivial⟩

variable {Ω : Opens (Minkowski d)} [FlatQuotient.Invariant (horizGroup Λ) Ω]

/-- The horizontal translations act freely. -/
instance instIsCancelSMulHoriz : IsCancelSMul (horizGroup Λ) Ω := by
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  rintro ⟨γ, hγ⟩ x hx
  obtain ⟨v, -, rfl⟩ := mem_horizGroup.1 hγ
  have h := congrArg (fun q : Ω => (q : Minkowski d).2) hx
  simp only [FlatQuotient.coe_smul, snd_horizTranslation_smul, toAdd_ofAdd] at h
  have hv : v = 0 := by simpa using h
  subst hv
  exact Subtype.ext (by simp [ofAdd_zero])

/-- The norm of the displacement of a horizontal translation. -/
theorem norm_le_of_horiz {v : EuclideanSpace ℝ (Fin d)} {p q : Minkowski d}
    (h : horizTranslation d (Multiplicative.ofAdd v) • p = q) : ‖v‖ ≤ ‖q.2‖ + ‖p.2‖ := by
  have h2 := congrArg Prod.snd h
  simp only [snd_horizTranslation_smul, toAdd_ofAdd] at h2
  have : v = q.2 - p.2 := by rw [← h2]; abel
  rw [this]
  exact norm_sub_le _ _

/-- The finite set of group elements carried by a ball of `Λ`. -/
theorem finite_horiz_of_bound [BallFinite Λ] (R : ℝ) :
    {γ : horizGroup Λ | ∃ v, ‖v‖ ≤ R ∧ horizTranslation d (Multiplicative.ofAdd v) = γ}.Finite := by
  refine ((BallFinite.finite_ball (Λ := Λ) R).image fun v =>
    horizTranslation d (Multiplicative.ofAdd v)).preimage
    (Subtype.val_injective.injOn) |>.subset ?_
  rintro ⟨γ, hγ⟩ ⟨v, hvR, hv⟩
  obtain ⟨w, hw, hw'⟩ := mem_horizGroup.1 hγ
  have hvw : v = w := by
    have h1 := congrArg (fun g : isom d => (g • (0 : Minkowski d)).2) (hv.trans hw'.symm)
    simpa using h1
  subst hvw
  exact ⟨v, ⟨hw, hvR⟩, hv⟩

/-- The horizontal translations by a ball-finite `Λ` act properly discontinuously. -/
instance instProperlyDiscontinuousSMulHoriz [BallFinite Λ] :
    ProperlyDiscontinuousSMul (horizGroup Λ) Ω := by
  refine ⟨fun {K L} hK hL => ?_⟩
  have hf : Continuous fun q : Ω => ‖(q : Minkowski d).2‖ :=
    (continuous_snd.comp continuous_subtype_val).norm
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  obtain ⟨R', hR'⟩ := hL.exists_bound_of_continuousOn hf.continuousOn
  refine (finite_horiz_of_bound Λ (R' + R)).subset ?_
  rintro ⟨γ, hγ⟩ ⟨_, ⟨k, hk, rfl⟩, hl⟩
  obtain ⟨v, -, rfl⟩ := mem_horizGroup.1 hγ
  refine ⟨v, ?_, rfl⟩
  have h1 := hR k hk
  have h2 := hR' _ hl
  simp only [Real.norm_eq_abs, abs_norm] at h1 h2
  have := norm_le_of_horiz (p := (k : Minkowski d)) (q := ((⟨_, hγ⟩ : horizGroup Λ) • k : Ω))
    rfl
  linarith

/-- **The horizontal translations act acausally** on every invariant `Ω`. -/
theorem actsAcausally_horiz : FlatQuotient.ActsAcausally (horizGroup Λ) Ω := by
  rintro ⟨γ, hγ⟩ hne x hle
  obtain ⟨v, -, rfl⟩ := mem_horizGroup.1 hγ
  apply hne
  have h := minkowski_le_top_iff.1 ((minkowski d).le_mono le_top
    ((flat_le_top_subtype_iff Ω _ _).1 hle))
  simp only [FlatQuotient.coe_smul, snd_horizTranslation_smul, fst_horizTranslation_smul,
    toAdd_ofAdd, add_sub_cancel_right, sub_self, norm_le_zero_iff] at h
  subst h
  exact Subtype.ext (by simp [ofAdd_zero])

/-- **Only finitely many `γ` have `x ≤ γ y`.** -/
theorem finite_le_horiz [BallFinite Λ] (x y : Ω) :
    {γ : horizGroup Λ | (flatCausality d Ω).le ⊤ x (γ • y)}.Finite := by
  refine (finite_horiz_of_bound Λ (‖(y : Minkowski d).2‖ + ‖(x : Minkowski d).2‖ +
    ((y : Minkowski d).1 - (x : Minkowski d).1))).subset ?_
  rintro ⟨γ, hγ⟩ hle
  obtain ⟨v, -, rfl⟩ := mem_horizGroup.1 hγ
  refine ⟨v, ?_, rfl⟩
  have h := minkowski_le_top_iff.1 ((minkowski d).le_mono le_top
    ((flat_le_top_subtype_iff Ω _ _).1 hle))
  simp only [FlatQuotient.coe_smul, snd_horizTranslation_smul, fst_horizTranslation_smul,
    toAdd_ofAdd] at h
  have : v = (v + (y : Minkowski d).2 - (x : Minkowski d).2) - (y : Minkowski d).2 +
    (x : Minkowski d).2 := by abel
  rw [this]
  linarith [norm_add_le (v + (y : Minkowski d).2 - (x : Minkowski d).2 - (y : Minkowski d).2)
    (x : Minkowski d).2, norm_sub_le (v + (y : Minkowski d).2 - (x : Minkowski d).2)
    (y : Minkowski d).2]

/-- A horizontal slice of an invariant `Ω` is invariant. -/
theorem slice_invariant (c : ℝ) : ∀ γ : horizGroup Λ, ∀ p ∈ (Subtype.val ⁻¹' {q : Minkowski d | q.1 = c} : Set Ω),
    γ • p ∈ (Subtype.val ⁻¹' {q : Minkowski d | q.1 = c} : Set Ω) := by
  rintro ⟨γ, hγ⟩ p hp
  obtain ⟨v, -, rfl⟩ := mem_horizGroup.1 hγ
  simp only [mem_preimage, mem_setOf_eq, FlatQuotient.coe_smul, fst_horizTranslation_smul] at hp ⊢
  exact hp

/-- A horizontal slice, read on the subtype `Ω`, is acausal. -/
theorem isAcausal_slice_subtype (c : ℝ) :
    (flatCausality d Ω).IsAcausal (Subtype.val ⁻¹' {q : Minkowski d | q.1 = c} : Set Ω) :=
  fun x hx y hy h => Subtype.ext (isAcausal_timeSlice c _ hx _ hy
    ((minkowski d).le_mono le_top ((flat_le_top_subtype_iff Ω x y).1 h)))

/-- The slice `t = 0` is a Cauchy surface of `𝐌ⁿ`, read on the subtype `⊤`. -/
theorem isCauchySurface_slice_top' :
    (flatCausality d (⊤ : Opens (Minkowski d))).IsCauchySurface
      (Subtype.val ⁻¹' {q : Minkowski d | q.1 = 0}) := by
  have h := (FlatQuotient.isCauchySurfaceOn_iff (⊤ : Opens (Minkowski d))
    (S := graph fun _ : EuclideanSpace ℝ (Fin d) => (0 : ℝ)) (fun _ _ => trivial)).1
    ((minkowski d).isCauchySurfaceOn_top.2 isCauchySurface_graph_zero)
  convert h using 2
  ext q
  simp [mem_graph]

variable [BallFinite Λ]

/-- **[3.T] The translation spacetime `Λ\𝐌ⁿ` is GH** (ETT's GH), for every ball-finite `Λ`. -/
theorem gh_translation :
    GH (FlatQuotient.toFlatSpacetime (horizGroup Λ) ⊤ FlatQuotient.isConnected_top) :=
  FlatQuotient.gh_toFlatSpacetime _ _ _ (actsAcausally_horiz Λ)
    (globallyHyperbolic_subtype ⊤ ((minkowski d).globallyHyperbolicOn_top.2
      minkowski_globallyHyperbolic)) (finite_le_horiz Λ)

/-- **[3.T] The slice `t = 0` descends to a Cauchy surface of `Λ\𝐌ⁿ`**, which is acausal. -/
theorem isCauchySurface_translation :
    (flatCausality d (FlatQuotient (horizGroup Λ) ⊤)).IsCauchySurface
        (FlatQuotient.proj _ _ '' (Subtype.val ⁻¹' {q : Minkowski d | q.1 = 0})) ∧
      (flatCausality d (FlatQuotient (horizGroup Λ) ⊤)).IsAcausal
        (FlatQuotient.proj _ _ '' (Subtype.val ⁻¹' {q : Minkowski d | q.1 = 0})) :=
  ⟨FlatQuotient.isCauchySurface_image _ _ (actsAcausally_horiz Λ) (slice_invariant Λ 0)
      isCauchySurface_slice_top',
    FlatQuotient.isAcausal_image _ _ (slice_invariant Λ 0) (isAcausal_slice_subtype 0)⟩

/-- **[3.T] `Λ\𝐌ⁿ` is GH in Barbot's sense** (a Cauchy surface: the image of `{t = 0}`). -/
theorem barbotGH_translation :
    BarbotGH (FlatQuotient.toFlatSpacetime (horizGroup Λ) ⊤ FlatQuotient.isConnected_top) :=
  ⟨_, (isCauchySurface_translation Λ).1⟩

end Translation

/-! ### Frames, and the translation family -/

section Family

universe u

/-- **The group `Γ` read in the frame `φ`**: `φ Γ φ⁻¹`. -/
noncomputable def frameConj (φ : isom d) (Γ : Subgroup (isom d)) : Subgroup (isom d) :=
  Γ.map (MulAut.conj φ).toMonoidHom

@[simp] theorem frameConj_one (Γ : Subgroup (isom d)) : frameConj 1 Γ = Γ := by
  rw [frameConj, map_one]
  exact Subgroup.map_id Γ

/-- **[3.T] A translation spacetime** (l.586–593, BARBOT-THEOREMS §1): in some frame `φ`, the
quotient of all of `𝐌ⁿ` by a discrete group of translations by spacelike vectors, here
normalised to horizontal vectors `(0, v)`, `v ∈ Λ` (a spacelike subspace is moved into
`{t = 0}` by a Lorentz transformation; reading disclosed). -/
def IsTranslationSpacetime (M : FlatSpacetime.{u} d) : Prop :=
  ∃ (φ : isom d) (Λ : AddSubgroup (EuclideanSpace ℝ (Fin d))), BallFinite Λ ∧
    IsQuotientOf M (frameConj φ (horizGroup Λ)) ⊤

/-- **Non-vacuity**: the quotient `Λ\𝐌ⁿ` is a translation spacetime. -/
theorem isTranslationSpacetime_quotient (Λ : AddSubgroup (EuclideanSpace ℝ (Fin d)))
    [BallFinite Λ] :
    IsTranslationSpacetime (FlatQuotient.toFlatSpacetime (horizGroup Λ) ⊤
      FlatQuotient.isConnected_top) :=
  ⟨1, Λ, inferInstance, by
    rw [frameConj_one]
    exact FlatQuotient.isQuotientOf_toFlatSpacetime _ _ _⟩

/-- The trivial group is ball-finite. -/
instance instBallFiniteBot : BallFinite (⊥ : AddSubgroup (EuclideanSpace ℝ (Fin d))) :=
  ⟨fun R => (finite_singleton 0).subset fun v hv => by
    exact AddSubgroup.mem_bot.1 hv.1⟩

/-- **Non-vacuity, `Γ = 1`**: `𝐌ⁿ` as the trivial quotient is a GH translation spacetime. -/
theorem translation_bot :
    IsTranslationSpacetime (FlatQuotient.toFlatSpacetime
        (horizGroup (⊥ : AddSubgroup (EuclideanSpace ℝ (Fin d)))) ⊤
      FlatQuotient.isConnected_top) ∧
    GH (FlatQuotient.toFlatSpacetime (horizGroup (⊥ : AddSubgroup (EuclideanSpace ℝ (Fin d)))) ⊤
      FlatQuotient.isConnected_top) :=
  ⟨isTranslationSpacetime_quotient _, gh_translation _⟩

variable (d) in
/-- **The integer lattice `ℤᵈ`** of the horizontal space. -/
def intLattice : AddSubgroup (EuclideanSpace ℝ (Fin d)) where
  carrier := {v | ∀ i, ∃ n : ℤ, v i = n}
  zero_mem' i := ⟨0, by simp⟩
  add_mem' {v w} hv hw i := by
    obtain ⟨n, hn⟩ := hv i
    obtain ⟨m, hm⟩ := hw i
    exact ⟨n + m, by rw [PiLp.add_apply, hn, hm]; push_cast; ring⟩
  neg_mem' {v} hv i := by
    obtain ⟨n, hn⟩ := hv i
    exact ⟨-n, by rw [PiLp.neg_apply, hn]; push_cast; ring⟩

/-- `ℤᵈ` is ball-finite. -/
instance instBallFiniteIntLattice : BallFinite (intLattice d) := by
  refine ⟨fun R => ?_⟩
  set N : ℤ := ⌈R⌉
  refine ((Set.Finite.pi (t := fun _ : Fin d => Icc (-N) N) fun _ => Set.finite_Icc _ _).image
    fun n : Fin d → ℤ => (WithLp.toLp 2 fun i => (n i : ℝ) : EuclideanSpace ℝ (Fin d))).subset ?_
  rintro v ⟨hv, hvR⟩
  choose n hn using hv
  refine ⟨n, fun i _ => ⟨?_, ?_⟩, ?_⟩
  · have h1 := (PiLp.norm_apply_le v i).trans hvR
    rw [hn i, Real.norm_eq_abs] at h1
    have h2 : ((-N : ℤ) : ℝ) ≤ n i := by
      have := Int.le_ceil R; push_cast; linarith [neg_abs_le ((n i : ℤ) : ℝ)]
    show -N ≤ n i
    exact_mod_cast h2
  · have h1 := (PiLp.norm_apply_le v i).trans hvR
    rw [hn i, Real.norm_eq_abs] at h1
    have h2 : ((n i : ℤ) : ℝ) ≤ N := by
      have := Int.le_ceil R; linarith [le_abs_self ((n i : ℤ) : ℝ)]
    show n i ≤ N
    exact_mod_cast h2
  · ext i
    simp [hn i]

end Family

/-! ### The induced map of quotients `Γ\Ω₁ → Γ\Ω₂` for `Ω₁ ⊆ Ω₂` -/

namespace FlatQuotient

variable (Γ : Subgroup (isom d)) {Ω₁ Ω₂ : Opens (Minkowski d)} [Invariant Γ Ω₁] [Invariant Γ Ω₂]
  (h12 : Ω₁ ≤ Ω₂)

/-- The map `Γ\Ω₁ → Γ\Ω₂` induced by the inclusion. -/
noncomputable def quotInclusion : FlatQuotient Γ Ω₁ → FlatQuotient Γ Ω₂ :=
  Quotient.lift (fun x : Ω₁ => proj Γ Ω₂ ⟨x, h12 x.2⟩) fun a b hab => by
    obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 hab)
    exact proj_eq_proj_iff.2 ⟨γ, Subtype.ext
      (show (γ : isom d) • (b : Minkowski d) = a from congrArg Subtype.val hγ)⟩

theorem quotInclusion_proj (x : Ω₁) :
    quotInclusion Γ h12 (proj Γ Ω₁ x) = proj Γ Ω₂ ⟨x, h12 x.2⟩ := rfl

theorem continuous_quotInclusion : Continuous (quotInclusion Γ h12) :=
  ((continuous_proj Γ Ω₂).comp ((continuous_subtype_val).subtype_mk _)).quotient_lift _

theorem quotInclusion_injective : Injective (quotInclusion Γ h12) := by
  intro q q' h
  obtain ⟨x, rfl⟩ := proj_surjective Γ Ω₁ q
  obtain ⟨y, rfl⟩ := proj_surjective Γ Ω₁ q'
  rw [quotInclusion_proj, quotInclusion_proj, proj_eq_proj_iff] at h
  obtain ⟨γ, hγ⟩ := h
  exact proj_eq_proj_iff.2 ⟨γ, Subtype.ext
    (show (γ : isom d) • (y : Minkowski d) = x from congrArg Subtype.val hγ)⟩

variable [ProperlyDiscontinuousSMul Γ Ω₁] [IsCancelSMul Γ Ω₁] [ProperlyDiscontinuousSMul Γ Ω₂]
  [IsCancelSMul Γ Ω₂]

/-- **The induced map of quotients is an isometric embedding.** -/
theorem isIsometricEmbedding_quotInclusion : IsIsometricEmbedding d (quotInclusion Γ h12) := by
  refine ⟨⟨continuous_quotInclusion Γ h12, fun q => ?_⟩, quotInclusion_injective Γ h12⟩
  set e₁ := chartAt (Minkowski d) q
  set e₂ := chartAt (Minkowski d) (quotInclusion Γ h12 q)
  set p₀ := e₁ q
  have hp₀ : p₀ ∈ e₁.target := e₁.map_source (mem_chart_source _ _)
  have hG : ContinuousAt (quotInclusion Γ h12 ∘ e₁.symm) p₀ :=
    (continuous_quotInclusion Γ h12).continuousAt.comp (e₁.continuousAt_symm hp₀)
  have hGp : (quotInclusion Γ h12 ∘ e₁.symm) p₀ = quotInclusion Γ h12 q := by
    simp only [comp_apply, p₀, e₁.left_inv (mem_chart_source _ _)]
  have hF : ContinuousAt (e₂ ∘ quotInclusion Γ h12 ∘ e₁.symm) p₀ := by
    refine ContinuousAt.comp (f := quotInclusion Γ h12 ∘ e₁.symm) ?_ hG
    rw [hGp]
    exact e₂.continuousAt (mem_chart_source _ _)
  obtain ⟨γ, hγ⟩ := eventually_eq_smul (Γ := Γ) (Ω := Ω₂) hF (by
    have hsrc : ∀ᶠ p in 𝓝 p₀, (quotInclusion Γ h12 ∘ e₁.symm) p ∈ e₂.source :=
      hG.eventually_mem (by rw [hGp]; exact e₂.open_source.mem_nhds (mem_chart_source _ _))
    filter_upwards [e₁.open_target.mem_nhds hp₀, hsrc] with p hp hpe
    obtain ⟨hpΩ, hsymm⟩ := symm_apply_of_mem_target Γ Ω₁ (chart_mem_atlas _ _) hp
    simp only [comp_apply] at hpe ⊢
    rw [hsymm, quotInclusion_proj] at hpe ⊢
    obtain ⟨hF, hFproj⟩ := apply_of_mem_source Γ Ω₂ (chart_mem_atlas _ _) hpe
    obtain ⟨γ, hγ, h⟩ := proj_eq_proj_iff'.1 hFproj.symm
    exact ⟨h12 hpΩ, hF, ⟨γ, hγ⟩, h⟩)
  exact ⟨(γ : isom d), hγ⟩

end FlatQuotient

/-! ### Rem 2.3 refuted as printed: the slab in the torus (DEC-44) -/

section Slab23

/-- `Γ = ℤᵈ`, the horizontal integer translations. -/
noncomputable abbrev torusGroup (d : ℕ) : Subgroup (isom d) := horizGroup (intLattice d)

/-- **The slab spacetime** `M = ℤᵈ\{0 < t < 1}`. -/
noncomputable def slabSpace (d : ℕ) : FlatSpacetime.{0} d :=
  FlatQuotient.toFlatSpacetime (torusGroup d) (timeSlab d 0 1) (isConnected_timeSlab one_pos)

/-- **The static torus** `N = ℤᵈ\𝐌ⁿ`, a translation spacetime. -/
noncomputable def torusSpace (d : ℕ) : FlatSpacetime.{0} d :=
  FlatQuotient.toFlatSpacetime (torusGroup d) ⊤ FlatQuotient.isConnected_top

/-- **Cauchy-compactness from a horizontal slice**: if the slice `t = c` lies in the
`ℤᵈ`-invariant `Ω` and is a Cauchy surface of `Ω`, then `ℤᵈ\Ω` is Cauchy-compact, its Cauchy
surface being the torus `ℤᵈ\{t = c}`. -/
theorem cauchyCompact_of_slice {Ω : Opens (Minkowski d)}
    [FlatQuotient.Invariant (torusGroup d) Ω] (hΩ : IsConnected (Ω : Set (Minkowski d))) {c : ℝ}
    (hcΩ : ∀ v : EuclideanSpace ℝ (Fin d), ((c, v) : Minkowski d) ∈ Ω)
    (hS : (flatCausality d Ω).IsCauchySurface (Subtype.val ⁻¹' {q : Minkowski d | q.1 = c})) :
    CauchyCompact (FlatQuotient.toFlatSpacetime (torusGroup d) Ω hΩ) := by
  set S : Set Ω := Subtype.val ⁻¹' {q : Minkowski d | q.1 = c}
  refine ⟨FlatQuotient.proj _ _ '' S, FlatQuotient.isCauchySurface_image _ _
    (actsAcausally_horiz (Ω := Ω) _) (slice_invariant (Ω := Ω) _ c) hS, ?_,
    FlatQuotient.isAcausal_image _ _ (slice_invariant (Ω := Ω) _ c)
      (isAcausal_slice_subtype (Ω := Ω) c)⟩
  -- the unit cube of the slice
  set κ : (Fin d → ℝ) → Minkowski d := fun x => (c, WithLp.toLp 2 x)
  have hκ : Continuous κ := continuous_const.prodMk (PiLp.continuous_toLp 2 _)
  set K : Set Ω := Subtype.val ⁻¹' (κ '' Icc 0 1)
  have hK : IsCompact K := by
    rw [Subtype.isCompact_iff, image_preimage_eq_inter_range, Subtype.range_coe,
      inter_eq_left.2 (by rintro _ ⟨x, -, rfl⟩; exact hcΩ _)]
    exact isCompact_Icc.image hκ
  have heq : FlatQuotient.proj (torusGroup d) Ω '' S = FlatQuotient.proj (torusGroup d) Ω '' K := by
    apply Subset.antisymm
    · rintro _ ⟨p, hp, rfl⟩
      set n : Fin d → ℤ := fun i => ⌊(p : Minkowski d).2 i⌋
      set w : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 fun i => -((n i : ℤ) : ℝ)
      have hw : w ∈ intLattice d := fun i => ⟨-n i, by simp [w]⟩
      set γ : torusGroup d := ⟨horizTranslation d (Multiplicative.ofAdd w),
        mem_horizGroup.2 ⟨w, hw, rfl⟩⟩
      refine ⟨γ • p, ⟨fun i => (p : Minkowski d).2 i - n i, ⟨fun i => ?_, fun i => ?_⟩, ?_⟩, ?_⟩
      · simp only [Pi.zero_apply, sub_nonneg, n]; exact Int.floor_le _
      · simp only [Pi.one_apply, n]; linarith [Int.lt_floor_add_one ((p : Minkowski d).2 i)]
      · simp only [κ, FlatQuotient.coe_smul, γ, horizTranslation_smul, toAdd_ofAdd]
        refine Prod.ext ?_ ?_
        · simp only [Prod.fst_add, zero_add]; exact hp.symm
        · ext i; simp [w, sub_eq_neg_add]
      · exact (FlatQuotient.proj_eq_proj_iff (Γ := torusGroup d) (Ω := Ω)).2 ⟨γ, rfl⟩
    · rintro _ ⟨p, hp, rfl⟩
      obtain ⟨x, -, hx⟩ := hp
      exact ⟨p, show (p : Minkowski d).1 = c by rw [← hx], rfl⟩
  have : IsCompact (FlatQuotient.proj (torusGroup d) Ω '' S) :=
    heq ▸ hK.image (FlatQuotient.continuous_proj _ _)
  exact this

/-- **The slab spacetime is GH.** -/
theorem gh_slabSpace : GH (slabSpace d) :=
  FlatQuotient.gh_toFlatSpacetime _ _ _ (actsAcausally_horiz _)
    (globallyHyperbolic_subtype _ globallyHyperbolicOn_timeSlab) (finite_le_horiz _)

/-- **The slab spacetime is Cauchy-compact**: `ℤᵈ\{t = 1/2}`. -/
theorem cauchyCompact_slabSpace : CauchyCompact (slabSpace d) := by
  have hc : ∀ v : EuclideanSpace ℝ (Fin d), (((1 / 2 : ℝ), v) : Minkowski d) ∈ timeSlab d 0 1 :=
    fun v => ⟨by norm_num, by norm_num⟩
  have hsub : {q : Minkowski d | q.1 = 1 / 2} ⊆ timeSlab d 0 1 := fun q hq =>
    ⟨by rw [hq]; norm_num, by rw [hq]; norm_num⟩
  exact cauchyCompact_of_slice (Ω := timeSlab d 0 1) (isConnected_timeSlab one_pos) hc
    ((FlatQuotient.isCauchySurfaceOn_iff _ hsub).1
      (isCauchySurfaceOn_timeSlab (by norm_num) (by norm_num)))

/-- **The torus is GH.** -/
theorem gh_torusSpace : GH (torusSpace d) := gh_translation _

/-- **The torus is Cauchy-compact**: `ℤᵈ\{t = 0}`. -/
theorem cauchyCompact_torusSpace : CauchyCompact (torusSpace d) :=
  cauchyCompact_of_slice (Ω := ⊤) _ (c := 0) (fun _ => trivial) isCauchySurface_slice_top'

/-- **The torus is a translation spacetime.** -/
theorem isTranslationSpacetime_torusSpace : IsTranslationSpacetime (torusSpace d) :=
  isTranslationSpacetime_quotient _

/-- The inclusion of the slab into `𝐌ⁿ`. -/
theorem timeSlab_le_top : timeSlab d 0 1 ≤ ⊤ := le_top

/-- **The slab embeds isometrically in the torus**, and **not surjectively**: the class of
`(2, 0)` is not reached, as the time coordinate is `ℤᵈ`-invariant. -/
theorem slab_embedding :
    IsIsometricEmbedding d (FlatQuotient.quotInclusion (torusGroup d) (timeSlab_le_top (d := d)) :
      slabSpace d → torusSpace d) ∧
    ¬ Surjective (FlatQuotient.quotInclusion (torusGroup d) (timeSlab_le_top (d := d)) :
      slabSpace d → torusSpace d) := by
  refine ⟨FlatQuotient.isIsometricEmbedding_quotInclusion _ _, fun hs => ?_⟩
  obtain ⟨q, hq⟩ := hs (FlatQuotient.proj (torusGroup d) ⊤ ⟨((2 : ℝ), 0), trivial⟩)
  obtain ⟨x, rfl⟩ := FlatQuotient.proj_surjective _ _ q
  change FlatQuotient.quotInclusion _ _ (FlatQuotient.proj _ _ x) = _ at hq
  rw [FlatQuotient.quotInclusion_proj, FlatQuotient.proj_eq_proj_iff] at hq
  obtain ⟨⟨γ, hγ⟩, h⟩ := hq
  obtain ⟨v, -, rfl⟩ := mem_horizGroup.1 hγ
  have := congrArg (fun r : (⊤ : Opens (Minkowski d)) => (r : Minkowski d).1) h
  simp only [FlatQuotient.coe_smul, fst_horizTranslation_smul] at this
  have hx := x.2.2
  rw [← this] at hx
  norm_num at hx

/-- **Rem 2.3 (`clomax`, l.571–578), as printed, is false** (DEC-44, OQ-22) for every class `CC`
of "Cauchy-complete" targets containing the Cauchy-compact ones: the slab `ℤᵈ\{0 < t < 1}` is GH
and Cauchy-compact and sits non-surjectively, isometrically, in the GH Cauchy-compact translation
spacetime `ℤᵈ\𝐌ⁿ`. -/
theorem not_cauchyCompact_absMax (CC : FlatSpacetime.{0} d → Prop)
    (hCC : ∀ N, CauchyCompact N → CC N) :
    ¬ ∀ M : FlatSpacetime.{0} d, GH M → CauchyCompact M → AbsMax CC M := by
  intro h
  exact slab_embedding.2 (h _ gh_slabSpace cauchyCompact_slabSpace (torusSpace d) gh_torusSpace
    (hCC _ cauchyCompact_torusSpace) _ slab_embedding.1)

end Slab23

/-! ### Null coordinates and boosts (Barbot's `2dxdy + dz²`) -/

section Null

/-- The unit vector `e = e₁` of the first spatial axis of `Minkowski (d + 1)`. -/
noncomputable def axisVec (d : ℕ) : EuclideanSpace ℝ (Fin (d + 1)) := EuclideanSpace.single 0 1

@[simp] theorem axisVec_zero : axisVec d 0 = 1 := by simp [axisVec]
@[simp] theorem axisVec_succ (i : Fin d) : axisVec d i.succ = 0 := by
  simp [axisVec, Fin.succ_ne_zero]

/-- The spatial square norm splits along the first axis: `‖x‖² = x₀² + ∑ᵢ x_{i+1}²`. -/
theorem norm_sq_split (x : EuclideanSpace ℝ (Fin (d + 1))) :
    ‖x‖ ^ 2 = x 0 ^ 2 + ∑ i : Fin d, x i.succ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
  simp [Real.norm_eq_abs, sq_abs]

/-- **The null coordinate `x`** (l.597–599): `x = (p₁ + t)/√2`. -/
noncomputable def nullX (p : Minkowski (d + 1)) : ℝ := (p.2 0 + p.1) / √2

/-- **The null coordinate `y`**: `y = (p₁ − t)/√2`. -/
noncomputable def nullY (p : Minkowski (d + 1)) : ℝ := (p.2 0 - p.1) / √2

/-- **The transverse coordinate `z ∈ ℝ^{n−2}`** (here `ℝᵈ`): the spatial coordinates but the
first. -/
noncomputable def nullZ (p : Minkowski (d + 1)) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun i => p.2 i.succ

theorem two_mul_nullX_mul_nullY (p : Minkowski (d + 1)) :
    2 * nullX p * nullY p = p.2 0 ^ 2 - p.1 ^ 2 := by
  have h : (√2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2 : √2 ≠ 0 := by positivity
  simp only [nullX, nullY]
  field_simp
  rw [h]; ring

/-- **`Q = 2xy + |z|²`** (l.599): the Minkowski form in null coordinates. -/
theorem minkQ_eq_null (p : Minkowski (d + 1)) :
    minkQ p = 2 * nullX p * nullY p + ‖nullZ p‖ ^ 2 := by
  rw [two_mul_nullX_mul_nullY, minkQ, norm_sq_split, EuclideanSpace.norm_sq_eq]
  simp [nullZ, Real.norm_eq_abs, sq_abs]
  ring

theorem continuous_nullX : Continuous (nullX (d := d)) :=
  (((EuclideanSpace.proj (0 : Fin (d + 1))).continuous.comp continuous_snd).add
    continuous_fst).div_const _

theorem continuous_nullZ : Continuous (nullZ (d := d)) :=
  (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i =>
    ((EuclideanSpace.proj i.succ).continuous.comp continuous_snd))

theorem norm_nullZ_le (p : Minkowski (d + 1)) : ‖nullZ p‖ ≤ ‖p.2‖ := by
  have h1 := norm_sq_split p.2
  have h2 : ‖nullZ p‖ ^ 2 = ∑ i : Fin d, p.2 i.succ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]; simp [nullZ, Real.norm_eq_abs, sq_abs]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by rw [h1, h2]; nlinarith [sq_nonneg (p.2 0)])

/-- **The boost of rapidity `s`** in the plane `(t, x₁)`, as a linear map. -/
noncomputable def axisBoostL (s : ℝ) : Minkowski (d + 1) →ₗ[ℝ] Minkowski (d + 1) where
  toFun p := (Real.cosh s * p.1 + Real.sinh s * p.2 0,
    p.2 + (Real.sinh s * p.1 + (Real.cosh s - 1) * p.2 0) • axisVec d)
  map_add' p q := by
    ext
    · simp only [Prod.fst_add, Prod.snd_add, PiLp.add_apply]; ring
    · simp only [Prod.snd_add, Prod.fst_add, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  map_smul' c p := by
    ext
    · simp only [Prod.smul_fst, Prod.smul_snd, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring
    · simp only [Prod.smul_snd, Prod.smul_fst, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
        RingHom.id_apply]; ring

theorem axisBoostL_fst (s : ℝ) (p : Minkowski (d + 1)) :
    (axisBoostL s p).1 = Real.cosh s * p.1 + Real.sinh s * p.2 0 := rfl

theorem axisBoostL_snd_zero (s : ℝ) (p : Minkowski (d + 1)) :
    (axisBoostL s p).2 0 = Real.sinh s * p.1 + Real.cosh s * p.2 0 := by
  show (p.2 + _ • axisVec d) 0 = _
  simp only [PiLp.add_apply, PiLp.smul_apply, axisVec_zero, smul_eq_mul]; ring

theorem axisBoostL_snd_succ (s : ℝ) (p : Minkowski (d + 1)) (i : Fin d) :
    (axisBoostL s p).2 i.succ = p.2 i.succ := by
  show (p.2 + _ • axisVec d) i.succ = _
  simp only [PiLp.add_apply, PiLp.smul_apply, axisVec_succ, smul_eq_mul, mul_zero, add_zero]

theorem axisBoostL_ext {p q : Minkowski (d + 1)} (h1 : p.1 = q.1) (h0 : p.2 0 = q.2 0)
    (hs : ∀ i : Fin d, p.2 i.succ = q.2 i.succ) : p = q := by
  refine Prod.ext h1 ?_
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact h0
  · exact hs j

theorem axisBoostL_add (s s' : ℝ) (p : Minkowski (d + 1)) :
    axisBoostL s (axisBoostL s' p) = axisBoostL (s + s') p := by
  refine axisBoostL_ext ?_ ?_ fun i => by rw [axisBoostL_snd_succ, axisBoostL_snd_succ, axisBoostL_snd_succ]
  · rw [axisBoostL_fst, axisBoostL_fst, axisBoostL_snd_zero, axisBoostL_fst, Real.cosh_add, Real.sinh_add]; ring
  · rw [axisBoostL_snd_zero, axisBoostL_snd_zero, axisBoostL_fst, axisBoostL_snd_zero, Real.cosh_add,
      Real.sinh_add]; ring

theorem axisBoostL_zero (p : Minkowski (d + 1)) : axisBoostL 0 p = p := by
  refine axisBoostL_ext ?_ ?_ fun i => axisBoostL_snd_succ _ _ _
  · rw [axisBoostL_fst]; simp
  · rw [axisBoostL_snd_zero]; simp

/-- **The boost**, as a linear automorphism. -/
noncomputable def axisBoost (s : ℝ) : Minkowski (d + 1) ≃ₗ[ℝ] Minkowski (d + 1) :=
  LinearEquiv.ofLinear (axisBoostL s) (axisBoostL (-s))
    (LinearMap.ext fun p => by
      show axisBoostL s (axisBoostL (-s) p) = p; rw [axisBoostL_add, add_neg_cancel, axisBoostL_zero])
    (LinearMap.ext fun p => by
      show axisBoostL (-s) (axisBoostL s p) = p; rw [axisBoostL_add, neg_add_cancel, axisBoostL_zero])

theorem axisBoost_apply (s : ℝ) (p : Minkowski (d + 1)) : axisBoost s p = axisBoostL s p := rfl

theorem nullX_boost (s : ℝ) (p : Minkowski (d + 1)) : nullX (axisBoost s p) = Real.exp s * nullX p := by
  simp only [nullX, axisBoost_apply, axisBoostL_fst, axisBoostL_snd_zero, ← Real.cosh_add_sinh]; ring

theorem nullY_boost (s : ℝ) (p : Minkowski (d + 1)) :
    nullY (axisBoost s p) = Real.exp (-s) * nullY p := by
  simp only [nullY, axisBoost_apply, axisBoostL_fst, axisBoostL_snd_zero, ← Real.cosh_sub_sinh]; ring

theorem nullZ_boost (s : ℝ) (p : Minkowski (d + 1)) : nullZ (axisBoost s p) = nullZ p := by
  ext i; simp [nullZ, axisBoost_apply, axisBoostL_snd_succ]

theorem minkQ_boost (s : ℝ) (p : Minkowski (d + 1)) : minkQ (axisBoost s p) = minkQ p := by
  rw [minkQ_eq_null, minkQ_eq_null, nullX_boost, nullY_boost, nullZ_boost]
  have : Real.exp s * Real.exp (-s) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  linear_combination (2 * nullX p * nullY p) * this

/-- The reflection `x₁ ↦ −x₁`, which conjugates `axisBoost s` to `axisBoost (−s)`. -/
noncomputable def axisReflL : Minkowski (d + 1) →ₗ[ℝ] Minkowski (d + 1) where
  toFun p := (p.1, p.2 - (2 * p.2 0) • axisVec d)
  map_add' p q := by
    ext
    · rfl
    · simp only [Prod.snd_add, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
  map_smul' c p := by
    ext
    · rfl
    · simp only [Prod.smul_snd, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
      ring

theorem axisReflL_fst (q : Minkowski (d + 1)) : (axisReflL q).1 = q.1 := rfl

theorem axisReflL_snd_zero (q : Minkowski (d + 1)) : (axisReflL q).2 0 = -q.2 0 := by
  show (q.2 - _ • axisVec d) 0 = _
  simp only [PiLp.sub_apply, PiLp.smul_apply, axisVec_zero, smul_eq_mul]; ring

theorem axisReflL_snd_succ (q : Minkowski (d + 1)) (i : Fin d) :
    (axisReflL q).2 i.succ = q.2 i.succ := by
  show (q.2 - _ • axisVec d) i.succ = _; simp

theorem axisReflL_invol (p : Minkowski (d + 1)) : axisReflL (axisReflL p) = p :=
  axisBoostL_ext rfl (by rw [axisReflL_snd_zero, axisReflL_snd_zero, neg_neg])
    fun i => by rw [axisReflL_snd_succ, axisReflL_snd_succ]

noncomputable def axisRefl : Minkowski (d + 1) ≃ₗ[ℝ] Minkowski (d + 1) :=
  LinearEquiv.ofLinear axisReflL axisReflL (LinearMap.ext axisReflL_invol)
    (LinearMap.ext axisReflL_invol)

theorem axisRefl_boost (s : ℝ) (p : Minkowski (d + 1)) :
    axisRefl (axisBoost s (axisRefl p)) = axisBoost (-s) p := by
  have h0 : ∀ q : Minkowski (d + 1), (axisRefl q).2 0 = -q.2 0 := axisReflL_snd_zero
  have hs : ∀ (q : Minkowski (d + 1)) (i : Fin d), (axisRefl q).2 i.succ = q.2 i.succ :=
    axisReflL_snd_succ
  have h1 : ∀ q : Minkowski (d + 1), (axisRefl q).1 = q.1 := fun _ => rfl
  refine axisBoostL_ext ?_ ?_ fun i => ?_
  · rw [h1, axisBoost_apply, axisBoostL_fst, h1, h0, axisBoost_apply, axisBoostL_fst, Real.sinh_neg,
      Real.cosh_neg]; ring
  · rw [h0, axisBoost_apply, axisBoostL_snd_zero, h1, h0, axisBoost_apply, axisBoostL_snd_zero, Real.sinh_neg,
      Real.cosh_neg]; ring
  · rw [hs, axisBoost_apply, axisBoostL_snd_succ, hs, axisBoost_apply, axisBoostL_snd_succ]

/-- **A boost has determinant `1`**: `det(B_s) = det(B_{s/2})² ≥ 0`, `det(B_s) det(B_{−s}) = 1`, and
`B_{−s}` is conjugate to `B_s` by the reflection `x₁ ↦ −x₁`. -/
theorem det_boost (s : ℝ) : LinearMap.det (axisBoost (d := d) s).toLinearMap = 1 := by
  have hmul : ∀ a b : ℝ, (axisBoost (d := d) a).toLinearMap ∘ₗ (axisBoost (d := d) b).toLinearMap =
      (axisBoost (d := d) (a + b)).toLinearMap := fun a b =>
    LinearMap.ext fun p => by
      show axisBoostL a (axisBoostL b p) = axisBoostL (a + b) p; exact axisBoostL_add a b p
  have hconj : (axisBoost (d := d) (-s)).toLinearMap =
      (axisRefl (d := d)).toLinearMap ∘ₗ (axisBoost (d := d) s).toLinearMap ∘ₗ
        (axisRefl (d := d)).symm.toLinearMap := by
    refine LinearMap.ext fun p => ?_
    have : axisRefl.symm p = axisRefl p := rfl
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, comp_apply, this]
    exact (axisRefl_boost s p).symm
  have h1 : LinearMap.det (axisBoost (d := d) (-s)).toLinearMap =
      LinearMap.det (axisBoost (d := d) s).toLinearMap := by
    rw [hconj, LinearMap.det_conj]
  have h2 : LinearMap.det (axisBoost (d := d) s).toLinearMap *
      LinearMap.det (axisBoost (d := d) (-s)).toLinearMap = 1 := by
    rw [← LinearMap.det_comp, hmul, add_neg_cancel]
    have : (axisBoost (d := d) 0).toLinearMap = LinearMap.id :=
      LinearMap.ext fun p => axisBoostL_zero p
    rw [this, LinearMap.det_id]
  have h3 : 0 ≤ LinearMap.det (axisBoost (d := d) s).toLinearMap := by
    rw [show s = s / 2 + s / 2 by ring, ← hmul, LinearMap.det_comp]
    exact mul_self_nonneg _
  rw [h1] at h2
  nlinarith [sq_nonneg (LinearMap.det (axisBoost (d := d) s).toLinearMap - 1)]

/-- A boost preserves the closed future cone. -/
theorem isFutureCausal_boost (s : ℝ) {v : Minkowski (d + 1)} (hv : IsFutureCausal v) :
    IsFutureCausal (axisBoost s v) := by
  refine ⟨?_, by rw [minkQ_boost]; exact hv.2⟩
  rw [axisBoost_apply, axisBoostL_fst]
  have hn : |v.2 0| ≤ v.1 := by
    have h1 : |v.2 0| ≤ ‖v.2‖ := by
      have := PiLp.norm_apply_le v.2 0; rwa [Real.norm_eq_abs] at this
    have h2 : ‖v.2‖ ≤ v.1 := (sq_le_sq₀ (norm_nonneg _) hv.1).1 (minkQ_le_zero_iff.1 hv.2)
    linarith
  have hc : |Real.sinh s| ≤ Real.cosh s := by
    have h := Real.cosh_sq s
    have hp := Real.cosh_pos s
    nlinarith [abs_nonneg (Real.sinh s), sq_abs (Real.sinh s)]
  nlinarith [abs_le.1 hn, abs_le.1 hc, abs_nonneg (Real.sinh s), abs_mul_abs_self (Real.sinh s),
    mul_le_mul hc hn (abs_nonneg _) (Real.cosh_pos s).le, abs_mul (Real.sinh s) (v.2 0),
    neg_abs_le (Real.sinh s * v.2 0)]

/-- **The boost is in `SO₀(1, d + 1)`.** -/
theorem axisBoost_mem_lorentz (s : ℝ) : axisBoost s ∈ lorentz (d + 1) :=
  ⟨minkQ_boost s, fun _ hv => isFutureCausal_boost s hv, det_boost s⟩

end Null

/-! ### Quotients of regular domains `Γ\Ω⁺(Λ)` -/

section CosmoQuotient

variable {Λ : Set (PenroseSphere d × ℝ)} (h : CosmoRegular Λ) (Γ : Subgroup (isom d))

/-- `Ω⁺(Λ)` is connected (convex, non-empty). -/
theorem isConnected_omegaPlus : IsConnected (h.regular.opens : Set (Minkowski d)) :=
  (convex_omegaPlus Λ).isConnected h.regular.1

/-- `Γ` preserves `Ω⁺(Λ)`, in the form of `Flat.Cosmological` (`cosmoTime_smul`). -/
def PreservesOmega (Λ : Set (PenroseSphere d × ℝ)) (Γ : Subgroup (isom d)) : Prop :=
  ∀ γ ∈ Γ, (fun p => γ • p) ⁻¹' omegaPlus Λ = omegaPlus Λ

variable {h Γ}

theorem PreservesOmega.invariant (hΓ : PreservesOmega Λ Γ) :
    FlatQuotient.Invariant Γ h.regular.opens :=
  ⟨fun γ p hp => by
    have hp' : p ∈ omegaPlus Λ := hp
    rw [← hΓ γ γ.2] at hp'
    exact hp'⟩

variable [FlatQuotient.Invariant Γ h.regular.opens]

/-- **A free action preserving `Ω⁺(Λ)` is acausal**: the cosmological time is `Γ`-invariant and
strictly increasing along `≤`. -/
theorem actsAcausally_of_preservesOmega (hΓ : PreservesOmega Λ Γ)
    [IsCancelSMul Γ h.regular.opens] : FlatQuotient.ActsAcausally Γ h.regular.opens := by
  intro γ hne x hle
  have hle' := (minkowski d).le_mono le_top ((flat_le_top_subtype_iff _ _ _).1 hle)
  by_cases hx : (x : Minkowski d) = ((γ • x : h.regular.opens) : Minkowski d)
  · apply hne
    have : γ • x = (1 : Γ) • x := by rw [one_smul]; exact (Subtype.ext hx).symm
    exact IsCancelSMul.right_cancel γ 1 x this
  · have h1 := cosmoTime_lt_of_le h x.2 hle' hx
    rw [FlatQuotient.coe_smul, cosmoTime_smul (hΓ γ γ.2)] at h1
    exact lt_irrefl _ h1

/-- **Only finitely many `γ` have `x ≤ γ y`**, for a properly discontinuous `Γ` preserving
`Ω⁺(Λ)`: all such `γ y` lie in the compact diamond `J(x, x + (2C, 0)) ⊆ Ω`, `C` bounding the time
coordinate on `J⁺(x) ∩ {T ≤ T(y)}`. -/
theorem finite_le_of_preservesOmega (hΓ : PreservesOmega Λ Γ)
    [ProperlyDiscontinuousSMul Γ h.regular.opens] (x y : h.regular.opens) :
    {γ : Γ | (flatCausality d h.regular.opens).le ⊤ x (γ • y)}.Finite := by
  set X : Minkowski d := (x : Minkowski d)
  set κ := (X - cosmoRetract Λ X).1 - ‖(X - cosmoRetract Λ X).2‖
  have hκ : 0 < κ := by
    have hz := isFutureTimelike_iff_norm_lt.1 (cosmoRetract_facts h x.2).1
    simp only [κ]; linarith
  set C : ℝ := cosmoTime Λ y ^ 2 / (2 * κ)
  have hC : 0 ≤ C := by positivity
  set D : Set (Minkowski d) := (minkowski d).diamond ⊤ X (X + ((2 * C : ℝ), 0))
  have hDΩ : D ⊆ (h.regular.opens : Set (Minkowski d)) := fun q hq =>
    Jplus_omegaPlus_subset Λ ⟨X, x.2, (Causality.mem_diamond.1 hq).1⟩
  have hDc : IsCompact (Subtype.val ⁻¹' D : Set h.regular.opens) := by
    rw [Subtype.isCompact_iff, image_preimage_eq_inter_range, Subtype.range_coe,
      inter_eq_left.2 hDΩ]
    exact minkowski_globallyHyperbolic.2 _ _
  refine (ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := Γ) isCompact_singleton
    hDc).subset fun γ hγ => ⟨γ • y, ⟨y, rfl, rfl⟩, ?_⟩
  have hle := (minkowski d).le_mono le_top ((flat_le_top_subtype_iff _ _ _).1 hγ)
  set Y : Minkowski d := ((γ • y : h.regular.opens) : Minkowski d)
  have hT : cosmoTime Λ Y = cosmoTime Λ y := by
    simp only [Y, FlatQuotient.coe_smul]; exact cosmoTime_smul (hΓ γ γ.2) _
  have h1 := two_mul_fst_sub_le_cosmoTime_sq h x.2 hle
  rw [hT] at h1
  have h2 : (Y - X).1 ≤ C := by
    simp only [C]; rw [le_div_iff₀ (by positivity)]; linarith
  have h3 := minkowski_le_top_iff.1 hle
  simp only [Prod.fst_sub] at h2
  refine Causality.mem_diamond.2 ⟨hle, ?_⟩
  rw [minkowski_le_top_iff]
  simp only [Prod.snd_add, Prod.fst_add, add_zero]
  rw [norm_sub_rev]
  linarith

variable [ProperlyDiscontinuousSMul Γ h.regular.opens] [IsCancelSMul Γ h.regular.opens]

/-- **`Γ\Ω⁺(Λ)` is GH** (ETT's GH) for a free, properly discontinuous `Γ` preserving `Ω⁺(Λ)`. -/
theorem gh_quotient_omegaPlus (hΓ : PreservesOmega Λ Γ) :
    GH (FlatQuotient.toFlatSpacetime Γ h.regular.opens (isConnected_omegaPlus h)) :=
  FlatQuotient.gh_toFlatSpacetime _ _ _ (actsAcausally_of_preservesOmega (h := h) hΓ)
    (globallyHyperbolic_subtype _ h.regular.globallyHyperbolicOn)
    (finite_le_of_preservesOmega (h := h) hΓ)

/-- **The level sets `S_t` of the cosmological time descend to acausal Cauchy surfaces of
`Γ\Ω⁺(Λ)`** (l.1204–1208). -/
theorem isCauchySurface_quotient_cosmoLevel (hΓ : PreservesOmega Λ Γ) {t : ℝ} (ht : 0 < t) :
    (flatCausality d (FlatQuotient Γ h.regular.opens)).IsCauchySurface
        (FlatQuotient.proj _ _ '' (Subtype.val ⁻¹' cosmoLevel Λ t)) ∧
      (flatCausality d (FlatQuotient Γ h.regular.opens)).IsAcausal
        (FlatQuotient.proj _ _ '' (Subtype.val ⁻¹' cosmoLevel Λ t)) := by
  have hinv : ∀ γ : Γ, ∀ p ∈ (Subtype.val ⁻¹' cosmoLevel Λ t : Set h.regular.opens),
      γ • p ∈ (Subtype.val ⁻¹' cosmoLevel Λ t : Set h.regular.opens) := by
    intro γ p hp
    refine ⟨(γ • p).2, ?_⟩
    rw [FlatQuotient.coe_smul, cosmoTime_smul (hΓ γ γ.2)]
    exact hp.2
  refine ⟨FlatQuotient.isCauchySurface_image_of_isCauchySurfaceOn Γ h.regular.opens
    (actsAcausally_of_preservesOmega (h := h) hΓ) (cosmoLevel_subset t)
      (fun γ hγ p hp => ⟨?_, ?_⟩)
    (isCauchySurfaceOn_cosmoLevel h ht), FlatQuotient.isAcausal_image _ _ hinv fun a ha b hb hab =>
      Subtype.ext (isAcausal_cosmoLevel h t _ ha _ hb
        ((minkowski d).le_mono le_top ((flat_le_top_subtype_iff _ _ _).1 hab)))⟩
  · have h' : p ∈ omegaPlus Λ := hp.1
    rw [← hΓ γ hγ] at h'
    exact h'
  · rw [cosmoTime_smul (hΓ γ hγ)]; exact hp.2

end CosmoQuotient

/-! ### [3.M] Misner spacetimes -/

section Misner

/-- The transverse directions `{x = y = 0}`: `w ↦ (0, w) ∈ ℝ^{d+1}`. -/
noncomputable def transEmb (w : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin (d + 1)) :=
  WithLp.toLp 2 (Fin.cons 0 fun i => w i)

@[simp] theorem transEmb_zero (w : EuclideanSpace ℝ (Fin d)) : transEmb w 0 = 0 := rfl
@[simp] theorem transEmb_succ (w : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    transEmb w i.succ = w i := rfl

/-- **The Misner isometry** `g_{s,w}`: `(x, y, z) ↦ (eˢ x, e⁻ˢ y, z + w)` (l.600–608): the boost of
rapidity `s` followed by the translation by `w` in `{x = y = 0}`. -/
noncomputable def misnerMap (x : ℝ × EuclideanSpace ℝ (Fin d)) : isom (d + 1) :=
  ⟨(axisBoost x.1).toAffineEquiv.trans
      (AffineEquiv.constVAdd ℝ (Minkowski (d + 1)) ((0 : ℝ), transEmb x.2)), by
    rw [mem_isom_iff]
    convert axisBoost_mem_lorentz (d := d) x.1 using 1
    ext v <;> rfl⟩

theorem misnerMap_smul (x : ℝ × EuclideanSpace ℝ (Fin d)) (p : Minkowski (d + 1)) :
    misnerMap x • p = ((0 : ℝ), transEmb x.2) + axisBoost x.1 p := rfl

theorem misnerMap_fst (x : ℝ × EuclideanSpace ℝ (Fin d)) (p : Minkowski (d + 1)) :
    (misnerMap x • p).1 = (axisBoost x.1 p).1 := by rw [misnerMap_smul]; simp

theorem misnerMap_snd_zero (x : ℝ × EuclideanSpace ℝ (Fin d)) (p : Minkowski (d + 1)) :
    (misnerMap x • p).2 0 = (axisBoost x.1 p).2 0 := by rw [misnerMap_smul]; simp

theorem misnerMap_snd_succ (x : ℝ × EuclideanSpace ℝ (Fin d)) (p : Minkowski (d + 1))
    (i : Fin d) : (misnerMap x • p).2 i.succ = x.2 i + p.2 i.succ := by
  rw [misnerMap_smul]; simp [axisBoost_apply, axisBoostL_snd_succ]

theorem nullX_misner (x : ℝ × EuclideanSpace ℝ (Fin d)) (p : Minkowski (d + 1)) :
    nullX (misnerMap x • p) = Real.exp x.1 * nullX p := by
  rw [← nullX_boost]; simp only [nullX, misnerMap_fst, misnerMap_snd_zero]

theorem nullY_misner (x : ℝ × EuclideanSpace ℝ (Fin d)) (p : Minkowski (d + 1)) :
    nullY (misnerMap x • p) = Real.exp (-x.1) * nullY p := by
  rw [← nullY_boost]; simp only [nullY, misnerMap_fst, misnerMap_snd_zero]

theorem nullZ_misner (x : ℝ × EuclideanSpace ℝ (Fin d)) (p : Minkowski (d + 1)) :
    nullZ (misnerMap x • p) = x.2 + nullZ p := by
  ext i; simp [nullZ, misnerMap_snd_succ]

theorem axisBoost_fst_congr (s : ℝ) {q q' : Minkowski (d + 1)} (h1 : q.1 = q'.1)
    (h0 : q.2 0 = q'.2 0) : (axisBoost s q).1 = (axisBoost s q').1 := by
  rw [axisBoost_apply, axisBoost_apply, axisBoostL_fst, axisBoostL_fst, h1, h0]

theorem axisBoost_snd_zero_congr (s : ℝ) {q q' : Minkowski (d + 1)} (h1 : q.1 = q'.1)
    (h0 : q.2 0 = q'.2 0) : (axisBoost s q).2 0 = (axisBoost s q').2 0 := by
  rw [axisBoost_apply, axisBoost_apply, axisBoostL_snd_zero, axisBoostL_snd_zero, h1, h0]

theorem misnerMap_add (x x' : ℝ × EuclideanSpace ℝ (Fin d)) :
    misnerMap (x + x') = misnerMap x * misnerMap x' := by
  apply Subtype.ext
  apply AffineEquiv.ext
  intro p
  show misnerMap (x + x') • p = misnerMap x • (misnerMap x' • p)
  refine axisBoostL_ext ?_ ?_ fun i => ?_
  · rw [misnerMap_fst, misnerMap_fst, axisBoost_fst_congr x.1 (misnerMap_fst x' p)
      (misnerMap_snd_zero x' p), axisBoost_apply, axisBoost_apply, axisBoost_apply, axisBoostL_add, Prod.fst_add]
  · rw [misnerMap_snd_zero, misnerMap_snd_zero, axisBoost_snd_zero_congr x.1 (misnerMap_fst x' p)
      (misnerMap_snd_zero x' p), axisBoost_apply, axisBoost_apply, axisBoost_apply, axisBoostL_add, Prod.fst_add]
  · rw [misnerMap_snd_succ, misnerMap_snd_succ, misnerMap_snd_succ]
    simp only [Prod.snd_add, PiLp.add_apply]; ring

theorem misnerMap_zero : misnerMap (0 : ℝ × EuclideanSpace ℝ (Fin d)) = 1 := by
  apply Subtype.ext
  apply AffineEquiv.ext
  intro p
  show misnerMap (0 : ℝ × EuclideanSpace ℝ (Fin d)) • p = p
  refine axisBoostL_ext ?_ ?_ fun i => ?_
  · rw [misnerMap_fst, axisBoost_apply, Prod.fst_zero, axisBoostL_zero]
  · rw [misnerMap_snd_zero, axisBoost_apply, Prod.fst_zero, axisBoostL_zero]
  · rw [misnerMap_snd_succ]; simp

variable (d) in
/-- `(s, w) ↦ g_{s,w}`: the group `G₀ ≅ ℝ^{n−1}` (l.605–609), as a homomorphism. -/
noncomputable def misnerHom : Multiplicative (ℝ × EuclideanSpace ℝ (Fin d)) →* isom (d + 1) where
  toFun x := misnerMap (Multiplicative.toAdd x)
  map_one' := misnerMap_zero
  map_mul' a b := by rw [toAdd_mul, misnerMap_add]

/-- **The Misner group `Γ`**, the image of a subgroup `L` of `ℝ × ℝᵈ ≅ G₀`. -/
noncomputable def misnerGroup (L : AddSubgroup (ℝ × EuclideanSpace ℝ (Fin d))) :
    Subgroup (isom (d + 1)) :=
  (AddSubgroup.toSubgroup L).map (misnerHom d)

theorem mem_misnerGroup {L : AddSubgroup (ℝ × EuclideanSpace ℝ (Fin d))} {γ : isom (d + 1)} :
    γ ∈ misnerGroup L ↔ ∃ x ∈ L, misnerMap x = γ := by
  simp only [misnerGroup, Subgroup.mem_map]
  constructor
  · rintro ⟨v, hv, rfl⟩; exact ⟨Multiplicative.toAdd v, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩; exact ⟨Multiplicative.ofAdd v, hv, rfl⟩

/-- The point `e₁` of the Penrose sphere. -/
noncomputable def axisSphere (d : ℕ) : PenroseSphere (d + 1) :=
  ⟨axisVec d, by simp [axisVec]⟩

/-- The point `−e₁` of the Penrose sphere. -/
noncomputable def axisSphereNeg (d : ℕ) : PenroseSphere (d + 1) :=
  ⟨-axisVec d, by simp [axisVec]⟩

variable (d) in
/-- `Λ = {(e₁, 0), (−e₁, 0)}`: two null planes through `{x = y = 0}`. -/
def misnerΛ : Set (PenroseSphere (d + 1) × ℝ) := {(axisSphere d, 0), (axisSphereNeg d, 0)}

/-- **The Misner wedge `{xy < 0, x > 0}` is the regular domain `Ω⁺(Λ)`.** -/
theorem mem_omegaPlus_misnerΛ {p : Minkowski (d + 1)} :
    p ∈ omegaPlus (misnerΛ d) ↔ 0 < nullX p ∧ nullY p < 0 := by
  rw [mem_omegaPlus]
  simp only [misnerΛ, mem_insert_iff, mem_singleton_iff, forall_eq_or_imp, forall_eq,
    minkB_nullVec, axisSphere, axisSphereNeg]
  have h1 : inner ℝ (axisVec d) p.2 = p.2 0 := by simp [axisVec, EuclideanSpace.inner_single_left]
  have h2 : inner ℝ (-axisVec d) p.2 = -p.2 0 := by rw [inner_neg_left, h1]
  rw [h1, h2]
  have hs : 0 < √2 := by positivity
  simp only [nullX, nullY]
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨div_pos (by linarith) hs, div_neg_of_neg_of_pos (by linarith) hs⟩
  · rintro ⟨ha, hb⟩
    have ha' := (div_pos_iff_of_pos_right hs).1 ha
    have hb' := (div_neg_iff.1 hb).elim (fun h => absurd h.2 (not_lt.2 hs.le)) id
    constructor <;> linarith [hb'.1]

theorem isOpen_misnerWedge :
    IsOpen {p : Minkowski (d + 1) | 0 < nullX p ∧ nullY p < 0} :=
  (isOpen_lt continuous_const continuous_nullX).inter
    (isOpen_lt ((((EuclideanSpace.proj (0 : Fin (d + 1))).continuous.comp continuous_snd).sub
      continuous_fst).div_const _) continuous_const)

/-- **The Misner wedge is a regular domain with two directions.** -/
theorem misnerRegular (d : ℕ) : CosmoRegular (misnerΛ d) := by
  have hω : omegaPlus (misnerΛ d) = {p : Minkowski (d + 1) | 0 < nullX p ∧ nullY p < 0} :=
    Set.ext fun _ => mem_omegaPlus_misnerΛ
  refine ⟨⟨⟨((1 : ℝ), 0), mem_omegaPlus_misnerΛ.2 ⟨by simp [nullX],
    div_neg_of_neg_of_pos (by simp) (by positivity)⟩⟩,
    by rw [hω]; exact isOpen_misnerWedge⟩, ⟨_, Or.inl rfl, _, Or.inr rfl, fun he => ?_⟩⟩
  have := congrArg (fun u : PenroseSphere (d + 1) => (u : EuclideanSpace ℝ (Fin (d + 1))) 0) he
  simp [axisSphere, axisSphereNeg] at this
  norm_num at this

/-- The Misner wedge, as an open set. -/
noncomputable abbrev misnerWedge (d : ℕ) : Opens (Minkowski (d + 1)) := (misnerRegular d).regular.opens

/-- The Misner wedge is `{|x₁| < t}`. -/
theorem mem_omegaPlus_misnerΛ' {p : Minkowski (d + 1)} :
    p ∈ omegaPlus (misnerΛ d) ↔ |p.2 0| < p.1 := by
  rw [mem_omegaPlus_misnerΛ, abs_lt]
  have hs : 0 < √2 := by positivity
  simp only [nullX, nullY]
  constructor
  · rintro ⟨h1, h2⟩
    have h1' := (div_pos_iff_of_pos_right hs).1 h1
    have h2' : p.2 0 - p.1 < 0 := by
      by_contra hc; push Not at hc; exact absurd h2 (not_lt.2 (div_nonneg hc hs.le))
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    exact ⟨div_pos (by linarith) hs, div_neg_of_neg_of_pos (by linarith) hs⟩

/-- **The cosmological time of the Misner wedge** is `√(t² − x₁²) = √(−2xy)`; so its level sets
are the paper's slices `η = const` (`x = e^{η+ν}`, `y = −e^{η−ν}`, `−2xy = 2e^{2η}`, l.622–626). -/
theorem cosmoTime_misner {p : Minkowski (d + 1)} (hp : p ∈ omegaPlus (misnerΛ d)) :
    cosmoTime (misnerΛ d) p = √(p.1 ^ 2 - p.2 0 ^ 2) := by
  have h := misnerRegular d
  have hc0 : Continuous fun q : Minkowski (d + 1) => q.2 0 :=
    (EuclideanSpace.proj (0 : Fin (d + 1))).continuous.comp continuous_snd
  have hcl : closure (omegaPlus (misnerΛ d)) ⊆ {q : Minkowski (d + 1) | |q.2 0| ≤ q.1} :=
    closure_minimal (fun q hq => (mem_omegaPlus_misnerΛ'.1 hq).le)
      (isClosed_le (continuous_abs.comp hc0) continuous_fst)
  set q₀ : Minkowski (d + 1) := (0, p.2 - (p.2 0) • axisVec d)
  have hq₀a : q₀.2 0 = 0 := by simp [q₀]
  have hdiff : p - q₀ = (p.1, (p.2 0) • axisVec d) := by
    refine Prod.ext (by simp [q₀]) ?_
    simp only [Prod.snd_sub, q₀]; abel
  have hnorm : ‖(p.2 0) • axisVec d‖ = |p.2 0| := by
    rw [norm_smul, Real.norm_eq_abs]; simp [axisVec]
  have hq₀cl : q₀ ∈ closure (omegaPlus (misnerΛ d)) := by
    have hc : Continuous fun ε : ℝ => q₀ + ((ε, 0) : Minkowski (d + 1)) := by fun_prop
    have ht : Tendsto (fun ε : ℝ => q₀ + ((ε, 0) : Minkowski (d + 1))) (𝓝[>] 0) (𝓝 q₀) := by
      have := hc.tendsto 0; simp only [Prod.mk_zero_zero, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto ht ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    rw [mem_omegaPlus_misnerΛ']
    simp [q₀, hε]
  have hq₀le : (minkowski (d + 1)).le ⊤ q₀ p := by
    rw [minkowski_le_top_iff]
    have : p.2 - q₀.2 = (p.2 0) • axisVec d := by simp only [q₀]; abel
    rw [this, hnorm]
    simp only [q₀, sub_zero]
    exact (mem_omegaPlus_misnerΛ'.1 hp).le
  have hseg0 : segTime q₀ p = √(p.1 ^ 2 - p.2 0 ^ 2) := by
    simp only [segTime, minkQ, hdiff, hnorm, sq_abs]; ring_nf
  have hup : ∀ q ∈ cosmoPast (misnerΛ d) p, segTime q p ≤ √(p.1 ^ 2 - p.2 0 ^ 2) := by
    intro q hq
    have hq1 : |q.2 0| ≤ q.1 := hcl hq.1
    have hq2 := minkowski_le_top_iff.1 hq.2
    have ha : |p.2 0 - q.2 0| ≤ ‖p.2 - q.2‖ := by
      have := PiLp.norm_apply_le (p.2 - q.2) 0
      rwa [Real.norm_eq_abs, PiLp.sub_apply] at this
    apply Real.sqrt_le_sqrt
    simp only [minkQ, Prod.fst_sub, Prod.snd_sub]
    have hq1' := abs_le.1 hq1
    have hd := abs_le.1 (ha.trans hq2)
    have hsq : (p.2 0 - q.2 0) ^ 2 ≤ ‖p.2 - q.2‖ ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) ha 2
    nlinarith [mul_nonneg (by linarith [hq1'.1] : (0 : ℝ) ≤ q.1 + q.2 0)
      (by linarith [hd.2] : (0 : ℝ) ≤ (p.1 - q.1) - (p.2 0 - q.2 0)),
      mul_nonneg (by linarith [hq1'.2] : (0 : ℝ) ≤ q.1 - q.2 0)
      (by linarith [hd.1] : (0 : ℝ) ≤ (p.1 - q.1) + (p.2 0 - q.2 0)),
      mul_nonneg (by linarith [hq1'.1] : (0 : ℝ) ≤ q.1 + q.2 0)
      (by linarith [hq1'.2] : (0 : ℝ) ≤ q.1 - q.2 0)]
  refine le_antisymm ?_ (hseg0 ▸ segTime_le_cosmoTime h hp ⟨hq₀cl, hq₀le⟩)
  rw [cosmoTime_eq_segTime h hp]
  exact hup _ ⟨frontier_subset_closure (cosmoRetract_spec h hp).1, (cosmoRetract_spec h hp).2.1⟩

/-- **The Cauchy surfaces of `isCauchySurface_misner` are the `η`-slices**: for `t > 0`,
`cosmoLevel misnerΛ t = {xy < 0, x > 0, −2xy = t²}`. -/
theorem cosmoLevel_misner {t : ℝ} (ht : 0 < t) :
    cosmoLevel (misnerΛ d) t =
      {p | 0 < nullX p ∧ nullY p < 0 ∧ -(2 * nullX p * nullY p) = t ^ 2} := by
  ext p
  simp only [cosmoLevel, mem_setOf_eq, two_mul_nullX_mul_nullY]
  constructor
  · rintro ⟨hp, hT⟩
    rw [cosmoTime_misner hp] at hT
    have hpos : 0 ≤ p.1 ^ 2 - p.2 0 ^ 2 := by
      have := mem_omegaPlus_misnerΛ'.1 hp
      nlinarith [abs_nonneg (p.2 0), sq_abs (p.2 0)]
    obtain ⟨h1, h2⟩ := mem_omegaPlus_misnerΛ.1 hp
    refine ⟨h1, h2, ?_⟩
    rw [← hT, Real.sq_sqrt hpos]; ring
  · rintro ⟨h1, h2, h3⟩
    have hp : p ∈ omegaPlus (misnerΛ d) := mem_omegaPlus_misnerΛ.2 ⟨h1, h2⟩
    refine ⟨hp, ?_⟩
    rw [cosmoTime_misner hp, show p.1 ^ 2 - p.2 0 ^ 2 = t ^ 2 by linarith, Real.sqrt_sq ht.le]

variable {L : AddSubgroup (ℝ × EuclideanSpace ℝ (Fin d))}

/-- **`G₀` preserves the Misner wedge** (`eˢ x`, `e⁻ˢ y`). -/
theorem preservesOmega_misner : PreservesOmega (misnerΛ d) (misnerGroup L) := by
  intro γ hγ
  obtain ⟨x, -, rfl⟩ := mem_misnerGroup.1 hγ
  ext p
  simp only [mem_preimage, mem_omegaPlus_misnerΛ, nullX_misner, nullY_misner]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨pos_of_mul_pos_right h1 (Real.exp_pos _).le,
      neg_of_mul_neg_right h2 (Real.exp_pos _).le⟩
  · rintro ⟨h1, h2⟩
    exact ⟨mul_pos (Real.exp_pos _) h1, mul_neg_of_pos_of_neg (Real.exp_pos _) h2⟩

instance instInvariantMisner : FlatQuotient.Invariant (misnerGroup L) (misnerWedge d) :=
  preservesOmega_misner.invariant (h := misnerRegular d)

theorem nullX_pos_of_mem {p : Minkowski (d + 1)} (hp : p ∈ misnerWedge d) : 0 < nullX p :=
  (mem_omegaPlus_misnerΛ.1 hp).1

/-- **`G₀` acts freely on the wedge.** -/
instance instIsCancelSMulMisner : IsCancelSMul (misnerGroup L) (misnerWedge d) := by
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  rintro ⟨γ, hγ⟩ p hp
  obtain ⟨x, -, rfl⟩ := mem_misnerGroup.1 hγ
  have hv := congrArg (fun q : misnerWedge d => (q : Minkowski (d + 1))) hp
  simp only [FlatQuotient.coe_smul] at hv
  have hX := congrArg nullX hv
  have hZ := congrArg nullZ hv
  rw [nullX_misner] at hX
  rw [nullZ_misner] at hZ
  have hpos := nullX_pos_of_mem p.2
  have hs : Real.exp x.1 = 1 := by
    have := mul_right_cancel₀ hpos.ne' (hX.trans (one_mul _).symm); exact this
  have hs0 : x.1 = 0 := by rwa [Real.exp_eq_one_iff] at hs
  have hw0 : x.2 = 0 := by simpa using hZ
  have hx0 : x = 0 := Prod.ext hs0 hw0
  subst hx0
  exact Subtype.ext misnerMap_zero

/-- The finite set of elements of `Γ` carried by a ball of `L`. -/
theorem finite_misner_of_bound [BallFinite L] (R : ℝ) :
    {γ : misnerGroup L | ∃ x ∈ L, ‖x‖ ≤ R ∧ misnerMap x = γ}.Finite := by
  refine ((BallFinite.finite_ball (Λ := L) R).image fun x => misnerMap x).preimage
    (Subtype.val_injective.injOn) |>.subset ?_
  rintro ⟨γ, hγ⟩ ⟨x, hx, hxR, hxγ⟩
  exact ⟨x, ⟨hx, hxR⟩, hxγ⟩

/-- **A discrete `Γ ⊆ G₀` acts properly discontinuously on the wedge**: on compact sets,
`log x` and `‖z‖` are bounded, and `g_{s,w}` shifts them by `s` and `w`. -/
instance instProperlyDiscontinuousSMulMisner [BallFinite L] :
    ProperlyDiscontinuousSMul (misnerGroup L) (misnerWedge d) := by
  refine ⟨fun {K K'} hK hK' => ?_⟩
  have hX : Continuous fun q : misnerWedge d => Real.log (nullX (q : Minkowski (d + 1))) :=
    (continuous_nullX.comp continuous_subtype_val).log fun q => (nullX_pos_of_mem q.2).ne'
  have hZ : Continuous fun q : misnerWedge d => ‖nullZ (q : Minkowski (d + 1))‖ :=
    (continuous_nullZ.comp continuous_subtype_val).norm
  obtain ⟨R₁, hR₁⟩ := hK.exists_bound_of_continuousOn hX.continuousOn
  obtain ⟨R₂, hR₂⟩ := hK'.exists_bound_of_continuousOn hX.continuousOn
  obtain ⟨R₃, hR₃⟩ := hK.exists_bound_of_continuousOn hZ.continuousOn
  obtain ⟨R₄, hR₄⟩ := hK'.exists_bound_of_continuousOn hZ.continuousOn
  refine (finite_misner_of_bound (L := L) (max (R₁ + R₂) (R₃ + R₄))).subset ?_
  rintro ⟨γ, hγ⟩ ⟨_, ⟨k, hk, rfl⟩, hl⟩
  obtain ⟨x, hxL, rfl⟩ := mem_misnerGroup.1 hγ
  refine ⟨x, hxL, ?_, rfl⟩
  have h1 := hR₁ k hk
  have h2 := hR₂ _ hl
  have h3 := hR₃ k hk
  have h4 := hR₄ _ hl
  simp only [Real.norm_eq_abs, abs_norm, FlatQuotient.coe_smul] at h1 h2 h3 h4
  rw [nullX_misner, Real.log_mul (Real.exp_pos _).ne' (nullX_pos_of_mem k.2).ne',
    Real.log_exp] at h2
  rw [nullZ_misner] at h4
  rw [Prod.norm_def]
  refine max_le_max ?_ ?_
  · rw [Real.norm_eq_abs]
    have := abs_add_le (x.1 + Real.log (nullX (k : Minkowski (d + 1))))
      (-Real.log (nullX (k : Minkowski (d + 1))))
    rw [abs_neg] at this
    simp only [add_neg_cancel_right] at this
    linarith
  · have := norm_sub_le (x.2 + nullZ (k : Minkowski (d + 1))) (nullZ (k : Minkowski (d + 1)))
    simp only [add_sub_cancel_right] at this
    linarith

variable [BallFinite L]

/-- **[3.M] The Misner quotient `Γ\Ω` is GH** (ETT's GH: causal, compact diamonds; l.610–612
"the quotient `Γ\Ω` is a flat globally hyperbolic spacetime"). -/
theorem gh_misner :
    GH (FlatQuotient.toFlatSpacetime (misnerGroup L) (misnerWedge d)
      (isConnected_omegaPlus (misnerRegular d))) :=
  gh_quotient_omegaPlus (h := misnerRegular d) preservesOmega_misner

/-- **[3.M] Every level set of the cosmological time of the wedge descends to an acausal Cauchy
surface** of the Misner spacetime: the `G₀`-invariant slices (proved Cauchy for every
inextensible causal curve, `Flat.Cosmological`). -/
theorem isCauchySurface_misner {t : ℝ} (ht : 0 < t) :
    (flatCausality d.succ (FlatQuotient (misnerGroup L) (misnerWedge d))).IsCauchySurface
        (FlatQuotient.proj _ _ '' (Subtype.val ⁻¹' cosmoLevel (misnerΛ d) t)) ∧
      (flatCausality d.succ (FlatQuotient (misnerGroup L) (misnerWedge d))).IsAcausal
        (FlatQuotient.proj _ _ '' (Subtype.val ⁻¹' cosmoLevel (misnerΛ d) t)) :=
  isCauchySurface_quotient_cosmoLevel (h := misnerRegular d) preservesOmega_misner ht

/-- **[3.M] The Misner quotient is GH in Barbot's sense** (a Cauchy surface: the slice `η = 0`,
i.e. the level `T = 1` of the cosmological time). -/
theorem barbotGH_misner :
    BarbotGH (FlatQuotient.toFlatSpacetime (misnerGroup L) (misnerWedge d)
      (isConnected_omegaPlus (misnerRegular d))) :=
  ⟨_, (isCauchySurface_misner (L := L) one_pos).1⟩

end Misner

section MisnerFamily

universe u

/-- The past Misner wedge `{xy < 0, x < 0}` (l.616–618, the other sign). -/
def misnerWedgePast (d : ℕ) : Opens (Minkowski (d + 1)) :=
  ⟨{p | nullX p < 0 ∧ 0 < nullY p}, (isOpen_lt continuous_nullX continuous_const).inter
    (isOpen_lt continuous_const ((((EuclideanSpace.proj (0 : Fin (d + 1))).continuous.comp
      continuous_snd).sub continuous_fst).div_const _))⟩

/-- **[3.M] A Misner spacetime** (l.597–629, BARBOT-THEOREMS §1): in a frame `φ`, the quotient of
the wedge `{xy < 0, ±x > 0}` by a discrete subgroup `Γ` of `G₀`, **with an element of nonzero
boost parameter `s`** (finding F1: without one, `Γ` is a group of spacelike translations and [11.i]
fails). -/
def IsMisnerSpacetime (M : FlatSpacetime.{u} (d + 1)) : Prop :=
  ∃ (φ : isom (d + 1)) (L : AddSubgroup (ℝ × EuclideanSpace ℝ (Fin d))), BallFinite L ∧
    (∃ x ∈ L, x.1 ≠ 0) ∧
    (IsQuotientOf M (frameConj φ (misnerGroup L)) (isomImage φ (misnerWedge d)) ∨
      IsQuotientOf M (frameConj φ (misnerGroup L)) (isomImage φ (misnerWedgePast d)))

/-- `ℤ v` is ball-finite for `v ≠ 0`. -/
theorem ballFinite_zmultiples {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {v : V}
    (hv : v ≠ 0) : BallFinite (AddSubgroup.zmultiples v) := by
  refine ⟨fun R => ?_⟩
  have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
  set N : ℤ := ⌈R / ‖v‖⌉
  refine ((Set.finite_Icc (-N) N).image fun n : ℤ => n • v).subset ?_
  rintro x ⟨hx, hxR⟩
  obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hx
  refine ⟨n, ?_, rfl⟩
  rw [norm_zsmul ℝ, Real.norm_eq_abs] at hxR
  have h1 : |(n : ℝ)| ≤ R / ‖v‖ := by rw [le_div_iff₀ hn]; exact hxR
  have h2 : |(n : ℝ)| ≤ N := h1.trans (Int.le_ceil _)
  have h3 : |n| ≤ N := by exact_mod_cast h2
  exact ⟨by linarith [neg_abs_le n], (le_abs_self n).trans h3⟩

/-- **Non-vacuity** (kb/0011): the Misner spacetime `⟨g_{s₀,w₀}⟩\Ω`, `s₀ ≠ 0` (a boost times a
translation in `{x = y = 0}`, `Γ ≅ ℤ`), is a Misner spacetime and is GH. -/
theorem misner_example (w₀ : EuclideanSpace ℝ (Fin d)) {s₀ : ℝ} (hs₀ : s₀ ≠ 0) :
    haveI := ballFinite_zmultiples (V := ℝ × EuclideanSpace ℝ (Fin d)) (v := (s₀, w₀))
      (fun h => hs₀ (congrArg Prod.fst h))
    IsMisnerSpacetime (FlatQuotient.toFlatSpacetime (misnerGroup (AddSubgroup.zmultiples (s₀, w₀)))
        (misnerWedge d) (isConnected_omegaPlus (misnerRegular d))) ∧
      GH (FlatQuotient.toFlatSpacetime (misnerGroup (AddSubgroup.zmultiples (s₀, w₀)))
        (misnerWedge d) (isConnected_omegaPlus (misnerRegular d))) := by
  haveI := ballFinite_zmultiples (V := ℝ × EuclideanSpace ℝ (Fin d)) (v := (s₀, w₀))
    (fun h => hs₀ (congrArg Prod.fst h))
  refine ⟨⟨1, _, inferInstance, ⟨(s₀, w₀), AddSubgroup.mem_zmultiples _, hs₀⟩, Or.inl ?_⟩, gh_misner⟩
  rw [frameConj_one, isomImage_one]
  exact FlatQuotient.isQuotientOf_toFlatSpacetime _ _ _

end MisnerFamily

/-! ### [3.U] Unipotent spacetimes -/

section Unipotent

universe u

/-- **The point with null coordinates `(x, y, z)`**, inverse to `nullX`, `nullY`, `nullZ`. -/
noncomputable def ofNull (x y : ℝ) (z : EuclideanSpace ℝ (Fin d)) : Minkowski (d + 1) :=
  ((x - y) / √2, WithLp.toLp 2 (Fin.cons ((x + y) / √2) fun i => z i))

theorem nullX_ofNull (x y : ℝ) (z : EuclideanSpace ℝ (Fin d)) : nullX (ofNull x y z) = x := by
  have h : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h2 : √2 ≠ 0 := by positivity
  simp only [nullX, ofNull]
  show ((x + y) / √2 + (x - y) / √2) / √2 = x
  field_simp
  linear_combination (-x) * h

theorem nullY_ofNull (x y : ℝ) (z : EuclideanSpace ℝ (Fin d)) : nullY (ofNull x y z) = y := by
  have h : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h2 : √2 ≠ 0 := by positivity
  simp only [nullY, ofNull]
  show ((x + y) / √2 - (x - y) / √2) / √2 = y
  field_simp
  linear_combination (-y) * h

theorem nullZ_ofNull (x y : ℝ) (z : EuclideanSpace ℝ (Fin d)) : nullZ (ofNull x y z) = z := by
  ext i; rfl

/-- **The action of `t = (t₁, …, t_{n−2})` in the abelian group `A`** (l.649–659; the formula is l.659), in null
coordinates, for the eigenvalues `ℓ = (λ₁, …, λ_{n−2})` and the standard basis (the orthonormal
basis `eᵢ` of the paper is absorbed in the frame):
`(x, y, z) ↦ (x − ∑ λᵢtᵢ²/2 − ∑ λᵢzᵢtᵢ − (y/2) ∑ λᵢ²tᵢ², y, z + t(1 + yλ))`. -/
noncomputable def unipAction (ℓ : Fin d → ℝ) (t : EuclideanSpace ℝ (Fin d))
    (p : Minkowski (d + 1)) : Minkowski (d + 1) :=
  ofNull (nullX p - ∑ i, ℓ i / 2 * t i ^ 2 - ∑ i, ℓ i * nullZ p i * t i -
      nullY p / 2 * ∑ i, ℓ i ^ 2 * t i ^ 2) (nullY p)
    (WithLp.toLp 2 fun i => nullZ p i + t i * (1 + nullY p * ℓ i))

/-- The `A`-invariant coordinate `y` (l.643, l.746–748). -/
theorem nullY_unipAction (ℓ : Fin d → ℝ) (t : EuclideanSpace ℝ (Fin d)) (p : Minkowski (d + 1)) :
    nullY (unipAction ℓ t p) = nullY p := nullY_ofNull _ _ _

/-- **A slab between null hyperplanes** `{α < y < β}`, `α, β ∈ [−∞, +∞]`. -/
def unipDomain (α β : EReal) : Opens (Minkowski (d + 1)) :=
  ⟨{p | α < (nullY p : EReal) ∧ (nullY p : EReal) < β},
    (isOpen_lt continuous_const (continuous_coe_real_ereal.comp
      ((((EuclideanSpace.proj (0 : Fin (d + 1))).continuous.comp continuous_snd).sub
        continuous_fst).div_const _))).inter
    (isOpen_lt (continuous_coe_real_ereal.comp
      ((((EuclideanSpace.proj (0 : Fin (d + 1))).continuous.comp continuous_snd).sub
        continuous_fst).div_const _)) continuous_const)⟩

/-- **`]α, β[` is a component of `{y | ∀ i, 1 + yλᵢ ≠ 0}`** (l.663–670, with l.665's
convention `yᵢ = ∞` when `λᵢ = 0`): no pole `yᵢ = −1/λᵢ` inside, and each finite end
is a pole. -/
def IsUnipComponent (ℓ : Fin d → ℝ) (α β : EReal) : Prop :=
  α < β ∧ (∀ y : ℝ, α < y → (y : EReal) < β → ∀ i, 1 + y * ℓ i ≠ 0) ∧
    (α = ⊥ ∨ ∃ i, ℓ i ≠ 0 ∧ α = ((-1 / ℓ i : ℝ) : EReal)) ∧
    (β = ⊤ ∨ ∃ i, ℓ i ≠ 0 ∧ β = ((-1 / ℓ i : ℝ) : EReal))

/-- **`Ω(A)` is invariant**: the action of `A` preserves `y`, hence each component. -/
theorem unipAction_mem_unipDomain (ℓ : Fin d → ℝ) (t : EuclideanSpace ℝ (Fin d)) {α β : EReal}
    {p : Minkowski (d + 1)} (hp : p ∈ unipDomain α β) : unipAction ℓ t p ∈ unipDomain α β := by
  show α < (nullY (unipAction ℓ t p) : EReal) ∧ (nullY (unipAction ℓ t p) : EReal) < β
  rw [nullY_unipAction]; exact hp

/-- **The function `Φ`** of l.687–690, `Φ(y, z) = f(y) + ½ ∑ zᵢ²/(yᵢ − y)`, with
`yᵢ = −1/λᵢ` (`zᵢ²/(yᵢ − y) = −λᵢzᵢ²/(1 + yλᵢ)`, and `0` when `λᵢ = 0`). -/
noncomputable def unipPhi (ℓ : Fin d → ℝ) (f : ℝ → ℝ) (y : ℝ) (z : EuclideanSpace ℝ (Fin d)) : ℝ :=
  f y - (1 / 2) * ∑ i, ℓ i * z i ^ 2 / (1 + y * ℓ i)

/-- **The hypersurface `S_f`** (l.676–691): the graph `x = Φ(y, z)` over the slab. -/
def unipSlice (ℓ : Fin d → ℝ) (f : ℝ → ℝ) (α β : EReal) : Set (Minkowski (d + 1)) :=
  {p | p ∈ unipDomain α β ∧ nullX p = unipPhi ℓ f (nullY p) (nullZ p)}

/-- **[3.U] A unipotent spacetime** (l.632–673 and l.743–745, BARBOT-THEOREMS §1): in a frame `φ`, the quotient
of a component `Ω` of `Ω(A)` by a group `Γ` acting through a ball-finite (discrete) subgroup `L`
of `A ≅ ℝ^{n−2}`. The group is carried as a subgroup of `isom` acting by `unipAction`. -/
def IsUnipotentSpacetime (M : FlatSpacetime.{u} (d + 1)) : Prop :=
  ∃ (φ : isom (d + 1)) (ℓ : Fin d → ℝ) (α β : EReal) (L : AddSubgroup (EuclideanSpace ℝ (Fin d)))
    (Γ : Subgroup (isom (d + 1))), BallFinite L ∧ IsUnipComponent ℓ α β ∧
    (∀ γ ∈ Γ, ∃ t ∈ L, ∀ p, γ • p = unipAction ℓ t p) ∧
    (∀ t ∈ L, ∃ γ ∈ Γ, ∀ p, γ • p = unipAction ℓ t p) ∧
    IsQuotientOf M (frameConj φ Γ) (isomImage φ (unipDomain α β))

/-- **`S_f` is `A`-invariant** (l.678–691: it is the `A`-saturation of the curve `(f(y), y, 0)`). -/
theorem unipAction_mem_unipSlice (ℓ : Fin d → ℝ) (f : ℝ → ℝ) {α β : EReal}
    (hℓ : IsUnipComponent ℓ α β) (t : EuclideanSpace ℝ (Fin d)) {p : Minkowski (d + 1)}
    (hp : p ∈ unipSlice ℓ f α β) : unipAction ℓ t p ∈ unipSlice ℓ f α β := by
  refine ⟨unipAction_mem_unipDomain ℓ t hp.1, ?_⟩
  obtain ⟨⟨hα, hβ⟩, hx⟩ := hp
  set y := nullY p
  set z := nullZ p
  have hc : ∀ i, 1 + y * ℓ i ≠ 0 := hℓ.2.1 y hα hβ
  have key : ∀ i, ℓ i * (z i + t i * (1 + y * ℓ i)) ^ 2 / (1 + y * ℓ i) =
      ℓ i * z i ^ 2 / (1 + y * ℓ i) + 2 * (ℓ i * z i * t i) + 2 * (ℓ i / 2 * t i ^ 2) +
        y * (ℓ i ^ 2 * t i ^ 2) := fun i => by
    have h1 := hc i
    rw [div_add' _ _ _ h1, div_add' _ _ _ h1, div_add' _ _ _ h1, div_left_inj' h1]
    ring
  simp only [unipAction, nullX_ofNull, nullY_ofNull, nullZ_ofNull, unipPhi]
  show _ = f y - 1 / 2 * ∑ i, ℓ i * (z i + t i * (1 + y * ℓ i)) ^ 2 / (1 + y * ℓ i)
  rw [Finset.sum_congr rfl fun i _ => key i, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hx, unipPhi]
  ring

/-! #### `S_f` is a Cauchy surface: the time function `T = x − Φ(y, z)`

The paper's argument (l.728–741) treats causal geodesics only; for a closed, acausal, edgeless
`S` null geodesics would suffice (Cauchy-horizon generators), so the real gap is its separation
claim (l.729–738), false for bounded `f` (counterexample at `isCauchySurfaceOn_unipSlice`). The
repair is a time function:
`T = x − Φ(y, z)` vanishes exactly on `S_f`, and for `p ≤ q` in `Ω` with `u = y(p) − y(q) > 0`

`T(q) − T(p) = (Δx − |Δz|²/(2u)) + (f(y(p)) − f(y(q))) + ½ ∑ᵢ (sᵢzᵢ' − sᵢ'zᵢ)²/(sᵢsᵢ'u)`

(`sᵢ = 1 + y(p)λᵢ`, `sᵢ' = 1 + y(q)λᵢ`, `unipTime_sub`), a sum of three non-negative terms
(the causal cone `|Δz|² ≤ 2Δx·u`, `f` increasing, and `sᵢsᵢ' > 0` because no pole lies between).
So `T` increases strictly along `≤` in `Ω` (`unipTime_lt`), and a bound on `T` bounds `y` (through
the divergence of `f` at both ends) and then `x` (through the third term, `nullX_sub_le_aux`), so an
inextensible causal curve along which `T` keeps one sign would converge in `Ω`. -/

theorem continuous_nullY : Continuous (nullY (d := d)) :=
  (((EuclideanSpace.proj (0 : Fin (d + 1))).continuous.comp continuous_snd).sub
    continuous_fst).div_const _

/-- The time coordinate in null coordinates: `t = (x − y)/√2`. -/
theorem fst_eq_null (p : Minkowski (d + 1)) : p.1 = (nullX p - nullY p) / √2 := by
  have h : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [nullX, nullY, div_sub_div_same, div_div, h]; ring

/-- The first spatial coordinate in null coordinates: `x₁ = (x + y)/√2`. -/
theorem snd_zero_eq_null (p : Minkowski (d + 1)) : p.2 0 = (nullX p + nullY p) / √2 := by
  have h : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [nullX, nullY, ← add_div, div_div, h]; ring

/-- The null coordinates determine the point. -/
theorem eq_of_null {p q : Minkowski (d + 1)} (hx : nullX p = nullX q) (hy : nullY p = nullY q)
    (hz : ∀ i, nullZ p i = nullZ q i) : p = q :=
  axisBoostL_ext (by rw [fst_eq_null, fst_eq_null q, hx, hy])
    (by rw [snd_zero_eq_null, snd_zero_eq_null q, hx, hy]) hz

/-- **The causal cone in null coordinates**: `p ≤ q` in `𝐌ⁿ` gives `y` non-increasing, `x`
non-decreasing and `|Δz|² ≤ 2 Δx (−Δy)`. -/
theorem null_le_of_le_top {p q : Minkowski (d + 1)} (h : (minkowski (d + 1)).le ⊤ p q) :
    nullY q ≤ nullY p ∧ nullX p ≤ nullX q ∧
      ∑ i, (nullZ q i - nullZ p i) ^ 2 ≤ 2 * (nullX q - nullX p) * (nullY p - nullY q) := by
  obtain ⟨h1, h2⟩ := minkowski_le_top_iff_sq.1 h
  rw [norm_sq_split] at h2
  have hs : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 < √2 := by positivity
  have hX : nullX q - nullX p = ((q.2 0 - p.2 0) + (q.1 - p.1)) / √2 := by
    simp only [nullX]; ring
  have hY : nullY p - nullY q = ((q.1 - p.1) - (q.2 0 - p.2 0)) / √2 := by
    simp only [nullY]; ring
  have hZ : ∑ i, (nullZ q i - nullZ p i) ^ 2 = ∑ i : Fin d, (q.2 - p.2) i.succ ^ 2 := rfl
  have ha : (q.2 - p.2) 0 = q.2 0 - p.2 0 := rfl
  rw [ha] at h2
  have hS : 0 ≤ ∑ i : Fin d, (q.2 - p.2) i.succ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hτ : 0 ≤ q.1 - p.1 := by linarith
  have hat : q.2 0 - p.2 0 ≤ q.1 - p.1 := by nlinarith
  have hat' : -(q.1 - p.1) ≤ q.2 0 - p.2 0 := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · have : 0 ≤ nullY p - nullY q := by rw [hY]; exact div_nonneg (by linarith) hs0.le
    linarith
  · have : 0 ≤ nullX q - nullX p := by rw [hX]; exact div_nonneg (by linarith) hs0.le
    linarith
  · rw [hZ, hX, hY, mul_assoc, div_mul_div_comm, hs]
    nlinarith

section UnipCauchy

variable {ℓ : Fin d → ℝ} {f : ℝ → ℝ} {α β : EReal}

/-- **The time function of `S_f`**: `T = x − Φ(y, z)`, so that `S_f = Ω ∩ {T = 0}`. -/
noncomputable def unipTime (ℓ : Fin d → ℝ) (f : ℝ → ℝ) (p : Minkowski (d + 1)) : ℝ :=
  nullX p - unipPhi ℓ f (nullY p) (nullZ p)

theorem mem_unipSlice_iff {p : Minkowski (d + 1)} :
    p ∈ unipSlice ℓ f α β ↔ p ∈ unipDomain α β ∧ unipTime ℓ f p = 0 :=
  and_congr_right fun _ => sub_eq_zero.symm

/-- `Ω = {α < y < β}` is convex (a slab between two null hyperplanes). -/
theorem convex_unipDomain : Convex ℝ (unipDomain (d := d) α β : Set (Minkowski (d + 1))) := by
  intro p hp q hq s t hs ht hst
  have hY : nullY (s • p + t • q) = s * nullY p + t * nullY q := by
    simp only [nullY, Prod.snd_add, Prod.smul_snd, Prod.fst_add, Prod.smul_fst, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul]
    ring
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hq1, hq2⟩ := hq
  have e1 : s * min (nullY p) (nullY q) + t * min (nullY p) (nullY q) = min (nullY p) (nullY q) := by
    rw [← add_mul, hst, one_mul]
  have e2 : s * max (nullY p) (nullY q) + t * max (nullY p) (nullY q) = max (nullY p) (nullY q) := by
    rw [← add_mul, hst, one_mul]
  have hmin : min (nullY p) (nullY q) ≤ s * nullY p + t * nullY q := by
    nlinarith [mul_le_mul_of_nonneg_left (min_le_left (nullY p) (nullY q)) hs,
      mul_le_mul_of_nonneg_left (min_le_right (nullY p) (nullY q)) ht]
  have hmax : s * nullY p + t * nullY q ≤ max (nullY p) (nullY q) := by
    nlinarith [mul_le_mul_of_nonneg_left (le_max_left (nullY p) (nullY q)) hs,
      mul_le_mul_of_nonneg_left (le_max_right (nullY p) (nullY q)) ht]
  show α < ((nullY (s • p + t • q) : ℝ) : EReal) ∧ ((nullY (s • p + t • q) : ℝ) : EReal) < β
  rw [hY]
  refine ⟨?_, ?_⟩
  · refine lt_of_lt_of_le ?_ (EReal.coe_le_coe_iff.2 hmin)
    rcases min_choice (nullY p) (nullY q) with h | h <;> rw [h] <;> assumption
  · refine lt_of_le_of_lt (EReal.coe_le_coe_iff.2 hmax) ?_
    rcases max_choice (nullY p) (nullY q) with h | h <;> rw [h] <;> assumption

/-- **No pole between two points of a component**: `(1 + yλᵢ)(1 + y'λᵢ) > 0`. -/
theorem unip_mul_pos (hℓ : IsUnipComponent ℓ α β) {y y' : ℝ} (hy : α < y) (hy' : (y : EReal) < β)
    (hz : α < y') (hz' : (y' : EReal) < β) (i : Fin d) :
    0 < (1 + y * ℓ i) * (1 + y' * ℓ i) := by
  have key : ∀ {a b : ℝ}, α < a → (a : EReal) < β → α < b → (b : EReal) < β → a ≤ b →
      0 < (1 + a * ℓ i) * (1 + b * ℓ i) := by
    intro a b ha _ _ hb' hab
    have hcont : ContinuousOn (fun c : ℝ => 1 + c * ℓ i) (Icc a b) := by fun_prop
    have hmem : ∀ c ∈ Icc a b, 1 + c * ℓ i ≠ 0 := fun c hc =>
      hℓ.2.1 c (ha.trans_le (EReal.coe_le_coe_iff.2 hc.1))
        ((EReal.coe_le_coe_iff.2 hc.2).trans_lt hb') i
    have h1 := hmem a ⟨le_rfl, hab⟩
    have h2 := hmem b ⟨hab, le_rfl⟩
    by_contra hneg
    push Not at hneg
    rcases le_or_gt (1 + a * ℓ i) 0 with h | h
    · have hb0 : 0 ≤ 1 + b * ℓ i := by
        by_contra hb0
        push Not at hb0
        nlinarith [mul_pos_of_neg_of_neg (lt_of_le_of_ne h h1) hb0]
      obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc hab hcont ⟨h, hb0⟩
      exact hmem c hc hc0
    · have hb0 : 1 + b * ℓ i ≤ 0 := by
        by_contra hb0
        push Not at hb0
        nlinarith [mul_pos h hb0]
      obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' hab hcont ⟨hb0, h.le⟩
      exact hmem c hc hc0
  rcases le_total y y' with h | h
  · exact key hy hy' hz hz' h
  · rw [mul_comm]; exact key hz hz' hy hy' h

/-- The one-coordinate identity behind `unipTime_sub`. -/
theorem unip_sq_identity {l s s' z z' u : ℝ} (hs : s ≠ 0) (hs' : s' ≠ 0) (hu : u ≠ 0)
    (h : s' = s - u * l) :
    l * z' ^ 2 / s' - l * z ^ 2 / s + (z' - z) ^ 2 / u =
      (s * z' - s' * z) ^ 2 / (s * s' * u) := by
  have hl : l = (s - s') / u := by field_simp; linarith
  subst hl
  field_simp
  ring

/-- **The decomposition of `T(q) − T(p)`** into three non-negative terms (see the section
header), for `p ≤ q` in `Ω` with `y(q) < y(p)`. -/
theorem unipTime_sub (hℓ : IsUnipComponent ℓ α β) {p q : Minkowski (d + 1)}
    (hp : p ∈ unipDomain α β) (hq : q ∈ unipDomain α β) (hu : nullY q < nullY p) :
    unipTime ℓ f q - unipTime ℓ f p =
      ((nullX q - nullX p) - (∑ i, (nullZ q i - nullZ p i) ^ 2) / (2 * (nullY p - nullY q))) +
      (f (nullY p) - f (nullY q)) +
      1 / 2 * ∑ i, ((1 + nullY p * ℓ i) * nullZ q i - (1 + nullY q * ℓ i) * nullZ p i) ^ 2 /
        ((1 + nullY p * ℓ i) * (1 + nullY q * ℓ i) * (nullY p - nullY q)) := by
  have hu0 : nullY p - nullY q ≠ 0 := sub_ne_zero.2 hu.ne'
  rw [Finset.sum_congr rfl fun i _ => (unip_sq_identity (l := ℓ i) (u := nullY p - nullY q) (hℓ.2.1 _ hp.1 hp.2 i)
    (hℓ.2.1 _ hq.1 hq.2 i) hu0 (by ring)).symm]
  simp only [unipTime, unipPhi, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div]
  rw [← div_div (∑ i, (nullZ q i - nullZ p i) ^ 2) 2]
  ring

/-- Along `≤` with `y` constant, `z` is constant and `T` grows as `x`. -/
theorem unipTime_sub_of_nullY_eq {p q : Minkowski (d + 1)} (h : (minkowski (d + 1)).le ⊤ p q)
    (hy : nullY q = nullY p) :
    nullZ q = nullZ p ∧ unipTime ℓ f q - unipTime ℓ f p = nullX q - nullX p := by
  obtain ⟨-, -, hZ⟩ := null_le_of_le_top h
  rw [hy, sub_self, mul_zero] at hZ
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (nullZ q i - nullZ p i)).1
    (le_antisymm hZ (Finset.sum_nonneg fun i _ => sq_nonneg _))
  have hz : nullZ q = nullZ p := by
    ext i
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (h0 i (Finset.mem_univ i)))
  refine ⟨hz, ?_⟩
  simp only [unipTime, hy, hz]
  ring

/-- **`f(y(p)) − f(y(q)) ≤ T(q) − T(p)`** for `p ≤ q` in `Ω` (any `f`). -/
theorem unipTime_sub_ge (hℓ : IsUnipComponent ℓ α β) {p q : Minkowski (d + 1)}
    (hp : p ∈ unipDomain α β) (hq : q ∈ unipDomain α β) (h : (minkowski (d + 1)).le ⊤ p q) :
    f (nullY p) - f (nullY q) ≤ unipTime ℓ f q - unipTime ℓ f p := by
  obtain ⟨hY, hX, hZ⟩ := null_le_of_le_top h
  rcases hY.lt_or_eq with hlt | heq
  · rw [unipTime_sub hℓ hp hq hlt]
    have hu : 0 < nullY p - nullY q := sub_pos.2 hlt
    have hA : 0 ≤ (nullX q - nullX p) -
        (∑ i, (nullZ q i - nullZ p i) ^ 2) / (2 * (nullY p - nullY q)) := by
      rw [sub_nonneg, div_le_iff₀ (by positivity)]; linarith
    have hC : 0 ≤ ∑ i, ((1 + nullY p * ℓ i) * nullZ q i - (1 + nullY q * ℓ i) * nullZ p i) ^ 2 /
        ((1 + nullY p * ℓ i) * (1 + nullY q * ℓ i) * (nullY p - nullY q)) :=
      Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _)
        (mul_pos (unip_mul_pos hℓ hp.1 hp.2 hq.1 hq.2 i) hu).le
    linarith
  · rw [(unipTime_sub_of_nullY_eq h heq).2, heq, sub_self]
    linarith

theorem unipTime_le (hℓ : IsUnipComponent ℓ α β)
    (hf : MonotoneOn f {y : ℝ | α < y ∧ (y : EReal) < β}) {p q : Minkowski (d + 1)}
    (hp : p ∈ unipDomain α β) (hq : q ∈ unipDomain α β) (h : (minkowski (d + 1)).le ⊤ p q) :
    unipTime ℓ f p ≤ unipTime ℓ f q := by
  have h1 := unipTime_sub_ge (f := f) hℓ hp hq h
  have h2 : f (nullY q) ≤ f (nullY p) := hf hq hp (null_le_of_le_top h).1
  linarith

/-- **`T` increases strictly along `≤` in `Ω`** (`f` strictly increasing). -/
theorem unipTime_lt (hℓ : IsUnipComponent ℓ α β)
    (hf : StrictMonoOn f {y : ℝ | α < y ∧ (y : EReal) < β}) {p q : Minkowski (d + 1)}
    (hp : p ∈ unipDomain α β) (hq : q ∈ unipDomain α β) (h : (minkowski (d + 1)).le ⊤ p q)
    (hne : p ≠ q) : unipTime ℓ f p < unipTime ℓ f q := by
  obtain ⟨hY, hX, -⟩ := null_le_of_le_top h
  rcases hY.lt_or_eq with hlt | heq
  · have h1 := unipTime_sub_ge (f := f) hℓ hp hq h
    have h2 : f (nullY q) < f (nullY p) := hf hq hp hlt
    linarith
  · obtain ⟨hz, he⟩ := unipTime_sub_of_nullY_eq (f := f) h heq
    have hXlt : nullX p < nullX q := lt_of_le_of_ne hX fun hx =>
      hne (eq_of_null hx heq.symm fun i => by rw [hz])
    linarith

/-- The real-arithmetic step of `nullX_sub_le_aux`. -/
theorem unip_aux_bound {σ l ζ w A u U D P : ℝ} (hσ : σ ≠ 0) (hu : 0 < u) (huU : u ≤ U)
    (hP : 0 < P) (hPle : P ≤ σ ^ 2 + U * |σ * l|) (hA : A ^ 2 / (P * u) ≤ 2 * D)
    (hw : σ * w = A - u * l * ζ) :
    w ^ 2 / (2 * u) ≤ (2 * D * (σ ^ 2 + U * |σ * l|) + U * l ^ 2 * ζ ^ 2) / σ ^ 2 := by
  have hPu : 0 < P * u := mul_pos hP hu
  have hA' : A ^ 2 ≤ 2 * D * (P * u) := (div_le_iff₀ hPu).1 hA
  have hD : 0 ≤ D := by
    have := div_nonneg (sq_nonneg A) hPu.le; linarith
  have hσ2 : 0 < σ ^ 2 := by positivity
  have h1 : σ ^ 2 * w ^ 2 ≤ 2 * A ^ 2 + 2 * (u * l * ζ) ^ 2 := by
    have : σ ^ 2 * w ^ 2 = (A - u * l * ζ) ^ 2 := by rw [← hw]; ring
    rw [this]; nlinarith [sq_nonneg (A + u * l * ζ)]
  have h2 : 2 * A ^ 2 ≤ 4 * D * (σ ^ 2 + U * |σ * l|) * u := by
    nlinarith [mul_nonneg (mul_nonneg hD hu.le) (sub_nonneg.2 hPle)]
  have h3 : 2 * (u * l * ζ) ^ 2 ≤ 2 * U * l ^ 2 * ζ ^ 2 * u := by
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg l) (sq_nonneg ζ))
      (mul_nonneg hu.le (sub_nonneg.2 huU))]
  rw [div_le_div_iff₀ (by positivity) hσ2]
  nlinarith

/-- **A bound on `T` and on the fall of `y` bounds the rise of `x`**, for `p ≤ q` in `Ω`, with
any coefficients `σᵢ ≠ 0`, `ζᵢ` satisfying the two side conditions (instantiated at `p` for the
future end and at `q` for the past end). -/
theorem nullX_sub_le_aux (hℓ : IsUnipComponent ℓ α β)
    (hf : MonotoneOn f {y : ℝ | α < y ∧ (y : EReal) < β}) {p q : Minkowski (d + 1)}
    (hp : p ∈ unipDomain α β) (hq : q ∈ unipDomain α β) (h : (minkowski (d + 1)).le ⊤ p q)
    {D U : ℝ} (hD : unipTime ℓ f q - unipTime ℓ f p ≤ D) (hU : nullY p - nullY q ≤ U)
    (σ ζ : Fin d → ℝ) (hσ : ∀ i, σ i ≠ 0)
    (hP : ∀ i, (1 + nullY p * ℓ i) * (1 + nullY q * ℓ i) ≤ σ i ^ 2 + U * |σ i * ℓ i|)
    (hw : ∀ i, σ i * (nullZ q i - nullZ p i) =
      ((1 + nullY p * ℓ i) * nullZ q i - (1 + nullY q * ℓ i) * nullZ p i) -
        (nullY p - nullY q) * ℓ i * ζ i) :
    nullX q - nullX p ≤
      D + ∑ i, (2 * D * (σ i ^ 2 + U * |σ i * ℓ i|) + U * ℓ i ^ 2 * ζ i ^ 2) / σ i ^ 2 := by
  obtain ⟨hY, hX, hZ⟩ := null_le_of_le_top h
  have hD0 : 0 ≤ D := by linarith [unipTime_le hℓ hf hp hq h]
  have hU0 : 0 ≤ U := by linarith
  have hR : 0 ≤ ∑ i, (2 * D * (σ i ^ 2 + U * |σ i * ℓ i|) + U * ℓ i ^ 2 * ζ i ^ 2) / σ i ^ 2 :=
    Finset.sum_nonneg fun i _ => div_nonneg (add_nonneg (mul_nonneg (mul_nonneg two_pos.le hD0)
      (add_nonneg (sq_nonneg _) (mul_nonneg hU0 (abs_nonneg _))))
      (mul_nonneg (mul_nonneg hU0 (sq_nonneg _)) (sq_nonneg _))) (sq_nonneg _)
  rcases hY.lt_or_eq with hlt | heq
  · have hu : 0 < nullY p - nullY q := sub_pos.2 hlt
    have hdec := unipTime_sub (f := f) hℓ hp hq hlt
    set A := (nullX q - nullX p) -
      (∑ i, (nullZ q i - nullZ p i) ^ 2) / (2 * (nullY p - nullY q)) with hAdef
    set E : Fin d → ℝ := fun i =>
      ((1 + nullY p * ℓ i) * nullZ q i - (1 + nullY q * ℓ i) * nullZ p i) ^ 2 /
        ((1 + nullY p * ℓ i) * (1 + nullY q * ℓ i) * (nullY p - nullY q)) with hEdef
    have hA : 0 ≤ A := by
      rw [hAdef, sub_nonneg, div_le_iff₀ (by positivity)]; linarith
    have hE : ∀ i, 0 ≤ E i := fun i => div_nonneg (sq_nonneg _)
      (mul_pos (unip_mul_pos hℓ hp.1 hp.2 hq.1 hq.2 i) hu).le
    have hB : 0 ≤ f (nullY p) - f (nullY q) := sub_nonneg.2 (hf hq hp hY)
    have hEs : 0 ≤ ∑ i, E i := Finset.sum_nonneg fun i _ => hE i
    have hAD : A ≤ D := by linarith
    have hEi : ∀ i, E i ≤ 2 * D := fun i => by
      have := Finset.single_le_sum (fun j _ => hE j) (Finset.mem_univ i)
      linarith
    have hX' : nullX q - nullX p =
        A + ∑ i, (nullZ q i - nullZ p i) ^ 2 / (2 * (nullY p - nullY q)) := by
      rw [hAdef, ← Finset.sum_div]; ring
    rw [hX']
    have hsum : ∑ i, (nullZ q i - nullZ p i) ^ 2 / (2 * (nullY p - nullY q)) ≤
        ∑ i, (2 * D * (σ i ^ 2 + U * |σ i * ℓ i|) + U * ℓ i ^ 2 * ζ i ^ 2) / σ i ^ 2 :=
      Finset.sum_le_sum fun i _ => unip_aux_bound (hσ i) hu hU
        (unip_mul_pos hℓ hp.1 hp.2 hq.1 hq.2 i) (hP i) (hEi i) (hw i)
    linarith
  · have h1 := (unipTime_sub_of_nullY_eq (ℓ := ℓ) (f := f) h heq).2
    linarith

theorem continuousOn_unipTime (hℓ : IsUnipComponent ℓ α β)
    (hfc : ContinuousOn f {y : ℝ | α < y ∧ (y : EReal) < β}) :
    ContinuousOn (unipTime ℓ f) (unipDomain (d := d) α β : Set (Minkowski (d + 1))) := by
  refine continuous_nullX.continuousOn.sub ((hfc.comp continuous_nullY.continuousOn
    fun p hp => hp).sub (continuousOn_const.mul (continuousOn_finsetSum _ fun i _ => ?_)))
  have hz : Continuous fun p : Minkowski (d + 1) => nullZ p i :=
    (EuclideanSpace.proj i.succ).continuous.comp continuous_snd
  exact ContinuousOn.div (continuousOn_const.mul (hz.continuousOn.pow 2))
    (continuousOn_const.add (continuous_nullY.continuousOn.mul continuousOn_const))
    fun p hp => hℓ.2.1 _ hp.1 hp.2 i

/-- `J⁺(x) ≠ {x}` in `Ω` (move along the null direction `∂ₓ`, which keeps `y`). -/
theorem Jplus_unipDomain_ne_singleton {x : Minkowski (d + 1)} (hx : x ∈ unipDomain α β) :
    (minkowski (d + 1)).Jplus (unipDomain α β) {x} ≠ {x} := by
  intro he
  have hY : nullY (x + ((1 : ℝ), axisVec d)) = nullY x := by
    simp only [nullY, Prod.snd_add, Prod.fst_add, PiLp.add_apply, axisVec_zero]; ring
  have hy : x + ((1 : ℝ), axisVec d) ∈ unipDomain α β := by
    show α < ((nullY (x + ((1 : ℝ), axisVec d)) : ℝ) : EReal) ∧
      ((nullY (x + ((1 : ℝ), axisVec d)) : ℝ) : EReal) < β
    rw [hY]; exact hx
  have hmem : x + ((1 : ℝ), axisVec d) ∈ (minkowski (d + 1)).Jplus (unipDomain α β) {x} :=
    ⟨x, rfl, (le_iff_of_convex convex_unipDomain).2 ⟨hx, hy, by
      rw [minkowski_le_top_iff]; simp [axisVec]⟩⟩
  rw [he, mem_singleton_iff] at hmem
  have := congrArg Prod.fst hmem
  simp at this

/-- `J⁻(x) ≠ {x}` in `Ω`. -/
theorem Jminus_unipDomain_ne_singleton {x : Minkowski (d + 1)} (hx : x ∈ unipDomain α β) :
    (minkowski (d + 1)).Jminus (unipDomain α β) {x} ≠ {x} := by
  intro he
  have hY : nullY (x - ((1 : ℝ), axisVec d)) = nullY x := by
    simp only [nullY, Prod.snd_sub, Prod.fst_sub, PiLp.sub_apply, axisVec_zero]; ring
  have hy : x - ((1 : ℝ), axisVec d) ∈ unipDomain α β := by
    show α < ((nullY (x - ((1 : ℝ), axisVec d)) : ℝ) : EReal) ∧
      ((nullY (x - ((1 : ℝ), axisVec d)) : ℝ) : EReal) < β
    rw [hY]; exact hx
  have hmem : x - ((1 : ℝ), axisVec d) ∈ (minkowski (d + 1)).Jminus (unipDomain α β) {x} :=
    ⟨x, rfl, (le_iff_of_convex convex_unipDomain).2 ⟨hy, hx, by
      rw [minkowski_le_top_iff]; simp [axisVec]⟩⟩
  rw [he, mem_singleton_iff] at hmem
  have := congrArg Prod.fst hmem
  simp at this

/-- **A causal curve of `Ω` over a bounded-above interval with `t` bounded above and
`y ≥ y_K > α` is extensible in `Ω` at its future end.** -/
theorem futureExtensible_unipDomain {J : Set ℝ} {γ : ℝ → Minkowski (d + 1)}
    (hγ : (minkowski (d + 1)).CausalCurveIn (unipDomain α β) J γ) (hJ : BddAbove J) {B yK : ℝ}
    (hyK : α < yK) (hB : ∀ u ∈ J, (γ u).1 ≤ B) (hY : ∀ u ∈ J, yK ≤ nullY (γ u)) :
    (minkowski (d + 1)).FutureExtensible (unipDomain α β) J γ := by
  by_cases hmax : ∃ m, IsGreatest J m
  · obtain ⟨m, hm⟩ := hmax
    exact Causality.futureExtensible_of_isGreatest minkowski_causallyArcConnected
      minkowski_isCausal hγ hm (Jplus_unipDomain_ne_singleton (hγ.mem hm.1))
  have hlub : IsLUB J (sSup J) := isLUB_csSup hγ.nonempty hJ
  have hβJ : sSup J ∉ J := fun hβ => hmax ⟨_, hβ, hlub.1⟩
  have hlt : ∀ u ∈ J, u < sSup J := fun u hu =>
    lt_of_le_of_ne (hlub.1 hu) fun he => hβJ (he ▸ hu)
  have hle : ∀ u ∈ J, ∀ u' ∈ J, u ≤ u' → (minkowski (d + 1)).le ⊤ (γ u) (γ u') :=
    fun u hu u' hu' huu' => (minkowski (d + 1)).le_mono le_top (hγ.le_of_le hu hu' huu')
  obtain ⟨u₀, hu₀⟩ := hγ.nonempty
  obtain ⟨p, hp⟩ := exists_tendsto_of_bddAbove hle hγ.nonempty hγ.ordConnected hlub hβJ
    ⟨B, by rintro _ ⟨u, hu, rfl⟩; exact hB u hu⟩
  have hev : ∀ᶠ u in 𝓝[<] (sSup J), u ∈ J :=
    mem_of_superset (Ioo_mem_nhdsLT (hlt u₀ hu₀)) (Ioo_subset_of_isLUB hγ.ordConnected hlub hu₀)
  have hpΩ : p ∈ unipDomain α β := by
    have hcl : IsClosed {y : Minkowski (d + 1) | (minkowski (d + 1)).le ⊤ (γ u₀) y} := by
      simp only [minkowski_le_top_iff]
      exact isClosed_le (by fun_prop) (by fun_prop)
    have h1 : (minkowski (d + 1)).le ⊤ (γ u₀) p := by
      refine hcl.mem_of_tendsto hp ?_
      filter_upwards [Ioo_mem_nhdsLT (hlt u₀ hu₀)] with u hu
      exact hle u₀ hu₀ u (Ioo_subset_of_isLUB hγ.ordConnected hlub hu₀ hu) hu.1.le
    have h2 : yK ≤ nullY p := by
      have hc : Tendsto (fun u => nullY (γ u)) (𝓝[<] (sSup J)) (𝓝 (nullY p)) :=
        (continuous_nullY.tendsto p).comp hp
      exact ge_of_tendsto hc (hev.mono fun u hu => hY u hu)
    exact ⟨hyK.trans_le (EReal.coe_le_coe_iff.2 h2),
      (EReal.coe_le_coe_iff.2 (null_le_of_le_top h1).1).trans_lt (hγ.mem hu₀).2⟩
  exact (Causality.futureExtensible_of_tendsto_opens staticCausality.isClosed_Jplus_top
    minkowski_stronglyCausal minkowski_causallyArcConnected minkowski_isCausal hγ hpΩ hlt
    (ordConnected_insert_of_isLUB hγ.ordConnected hlub) hp (Jplus_unipDomain_ne_singleton hpΩ))

/-- **A causal curve of `Ω` over a bounded-below interval with `t` bounded below and
`y ≤ y_K < β` is extensible in `Ω` at its past end.** -/
theorem pastExtensible_unipDomain {J : Set ℝ} {γ : ℝ → Minkowski (d + 1)}
    (hγ : (minkowski (d + 1)).CausalCurveIn (unipDomain α β) J γ) (hJ : BddBelow J) {A yK : ℝ}
    (hyK : (yK : EReal) < β) (hA : ∀ u ∈ J, A ≤ (γ u).1) (hY : ∀ u ∈ J, nullY (γ u) ≤ yK) :
    (minkowski (d + 1)).PastExtensible (unipDomain α β) J γ := by
  by_cases hmin : ∃ m, IsLeast J m
  · obtain ⟨m, hm⟩ := hmin
    exact Causality.pastExtensible_of_isLeast minkowski_causallyArcConnected minkowski_isCausal
      hγ hm (Jminus_unipDomain_ne_singleton (hγ.mem hm.1))
  have hglb : IsGLB J (sInf J) := isGLB_csInf hγ.nonempty hJ
  have hαJ : sInf J ∉ J := fun hα => hmin ⟨_, hα, hglb.1⟩
  have hgt : ∀ u ∈ J, sInf J < u := fun u hu =>
    lt_of_le_of_ne (hglb.1 hu) fun he => hαJ (he ▸ hu)
  have hle : ∀ u ∈ J, ∀ u' ∈ J, u ≤ u' → (minkowski (d + 1)).le ⊤ (γ u) (γ u') :=
    fun u hu u' hu' huu' => (minkowski (d + 1)).le_mono le_top (hγ.le_of_le hu hu' huu')
  obtain ⟨u₀, hu₀⟩ := hγ.nonempty
  obtain ⟨p, hp⟩ := exists_tendsto_of_bddBelow hle hγ.nonempty hγ.ordConnected hglb hαJ
    ⟨A, by rintro _ ⟨u, hu, rfl⟩; exact hA u hu⟩
  have hev : ∀ᶠ u in 𝓝[>] (sInf J), u ∈ J :=
    mem_of_superset (Ioo_mem_nhdsGT (hgt u₀ hu₀)) (Ioo_subset_of_isGLB hγ.ordConnected hglb hu₀)
  have hpΩ : p ∈ unipDomain α β := by
    have hcl : IsClosed {y : Minkowski (d + 1) | (minkowski (d + 1)).le ⊤ y (γ u₀)} := by
      simp only [minkowski_le_top_iff]
      exact isClosed_le (by fun_prop) (by fun_prop)
    have h1 : (minkowski (d + 1)).le ⊤ p (γ u₀) := by
      refine hcl.mem_of_tendsto hp ?_
      filter_upwards [Ioo_mem_nhdsGT (hgt u₀ hu₀)] with u hu
      exact hle u (Ioo_subset_of_isGLB hγ.ordConnected hglb hu₀ hu) u₀ hu₀ hu.2.le
    have h2 : nullY p ≤ yK := by
      have hc : Tendsto (fun u => nullY (γ u)) (𝓝[>] (sInf J)) (𝓝 (nullY p)) :=
        (continuous_nullY.tendsto p).comp hp
      exact le_of_tendsto hc (hev.mono fun u hu => hY u hu)
    exact ⟨(hγ.mem hu₀).1.trans_le (EReal.coe_le_coe_iff.2 (null_le_of_le_top h1).1),
      (EReal.coe_le_coe_iff.2 h2).trans_lt hyK⟩
  exact (Causality.pastExtensible_of_tendsto_opens staticCausality.isClosed_Jminus_top
    minkowski_stronglyCausal minkowski_causallyArcConnected minkowski_isCausal hγ hpΩ hgt
    (ordConnected_insert_of_isGLB hγ.ordConnected hglb) hp (Jminus_unipDomain_ne_singleton hpΩ))

end UnipCauchy

/-- **[3.U] `S_f` is a Cauchy surface of `Ω`** (l.728–741), for **every inextensible causal
curve** of `Ω` (the paper argues on causal geodesics, l.731–741), for `f` strictly increasing and
continuous on `]α, β[`, **unbounded below and above** (the paper's `f = ∫ a²`, `a > 1`, with
both integrals of `a` infinite, l.707–711, is such an `f`). The divergence is needed at **every**
end, finite or infinite: l.676–677's "any (strictly) increasing `f`" is too weak (finding; for
`n = 4`, `λ = (−1, 1)`, `Ω = {−1 < y < 1}`, `f(y) = y`, the null line `z₁ = K(1 − y)`, `z₂ = 0`,
`x = 5 + K²(1 − y)/2` crosses both boundary hyperplanes with `T = 5 − y ∈ ]4, 6[`, so it misses
`S_f`). Proof through the time function `unipTime` (section header above). -/
theorem isCauchySurfaceOn_unipSlice (ℓ : Fin d → ℝ) (f : ℝ → ℝ) {α β : EReal}
    (hℓ : IsUnipComponent ℓ α β) (hf : StrictMonoOn f {y : ℝ | α < y ∧ (y : EReal) < β})
    (hfc : ContinuousOn f {y : ℝ | α < y ∧ (y : EReal) < β})
    (hfα : ∀ C : ℝ, ∃ y : ℝ, α < y ∧ (y : EReal) < β ∧ f y < C)
    (hfβ : ∀ C : ℝ, ∃ y : ℝ, α < y ∧ (y : EReal) < β ∧ C < f y) :
    (minkowski (d + 1)).IsCauchySurfaceOn (unipDomain α β) (unipSlice ℓ f α β) := by
  have hfm := hf.monotoneOn
  intro I γ hγ
  obtain ⟨hpi, hfi⟩ := Causality.inextensible_iff.1 hγ
  have hle : ∀ {s s' : ℝ}, s ∈ I → s' ∈ I → s ≤ s' → (minkowski (d + 1)).le ⊤ (γ s) (γ s') :=
    fun hs hs' h => (minkowski (d + 1)).le_mono le_top (hγ.1.le_of_le hs hs' h)
  have hΩ : ∀ {s : ℝ}, s ∈ I → γ s ∈ unipDomain α β := fun hs => hγ.1.mem hs
  -- some time with `T ≥ 0`: otherwise `y` and then `t` stay bounded, and the curve extends
  have hup : ∃ s ∈ I, 0 ≤ unipTime ℓ f (γ s) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hd, hsub, htan, -, hfut⟩ := hfi.1.arctanReparam
    have hT : ∀ u ∈ Real.arctan '' I, unipTime ℓ f ((γ ∘ Real.tan) u) < 0 :=
      fun u hu => hcon _ (htan u hu)
    have hle' : ∀ u ∈ Real.arctan '' I, ∀ u' ∈ Real.arctan '' I, u ≤ u' →
        (minkowski (d + 1)).le ⊤ ((γ ∘ Real.tan) u) ((γ ∘ Real.tan) u') :=
      fun u hu u' hu' h => (minkowski (d + 1)).le_mono le_top (hd.le_of_le hu hu' h)
    obtain ⟨u₀, hu₀⟩ := hd.nonempty
    have hp₀ := hd.mem hu₀
    set p₀ := (γ ∘ Real.tan) u₀
    obtain ⟨yK, hyK1, hyK2, hfyK⟩ := hfα (f (nullY p₀) + unipTime ℓ f p₀)
    have hYf : ∀ u ∈ Real.arctan '' I, u₀ ≤ u → yK ≤ nullY ((γ ∘ Real.tan) u) := by
      intro u hu h
      by_contra hlt
      push Not at hlt
      have hm : f (nullY ((γ ∘ Real.tan) u)) ≤ f yK :=
        hfm ⟨(hd.mem hu).1, (hd.mem hu).2⟩ ⟨hyK1, hyK2⟩ hlt.le
      have := unipTime_sub_ge (f := f) hℓ hp₀ (hd.mem hu) (hle' u₀ hu₀ u hu h)
      have := hT u hu
      linarith
    have hY : ∀ u ∈ Real.arctan '' I, yK ≤ nullY ((γ ∘ Real.tan) u) := by
      intro u hu
      rcases le_total u₀ u with h | h
      · exact hYf u hu h
      · exact (hYf u₀ hu₀ le_rfl).trans (null_le_of_le_top (hle' u hu u₀ hu₀ h)).1
    set U := nullY p₀ - yK
    set R := ∑ i, (2 * (-unipTime ℓ f p₀) * ((1 + nullY p₀ * ℓ i) ^ 2 +
      U * |(1 + nullY p₀ * ℓ i) * ℓ i|) + U * ℓ i ^ 2 * nullZ p₀ i ^ 2) / (1 + nullY p₀ * ℓ i) ^ 2
    have hXf : ∀ u ∈ Real.arctan '' I, u₀ ≤ u →
        nullX ((γ ∘ Real.tan) u) - nullX p₀ ≤ -unipTime ℓ f p₀ + R := by
      intro u hu h
      have hq := hd.mem hu
      have hpq := hle' u₀ hu₀ u hu h
      have hyq := null_le_of_le_top hpq
      refine nullX_sub_le_aux hℓ hfm hp₀ hq hpq (by linarith [hT u hu])
        (by linarith [hY u hu]) _ _ (fun i => hℓ.2.1 _ hp₀.1 hp₀.2 i) (fun i => ?_) (fun i => by ring)
      have hu0 : 0 ≤ nullY p₀ - nullY ((γ ∘ Real.tan) u) := by linarith [hyq.1]
      have huU : nullY p₀ - nullY ((γ ∘ Real.tan) u) ≤ U := by linarith [hY u hu]
      have e : (1 + nullY p₀ * ℓ i) * (1 + nullY ((γ ∘ Real.tan) u) * ℓ i) =
          (1 + nullY p₀ * ℓ i) ^ 2 + (nullY p₀ - nullY ((γ ∘ Real.tan) u)) *
            (-((1 + nullY p₀ * ℓ i) * ℓ i)) := by ring
      rw [e]
      have h1 := mul_le_mul_of_nonneg_left (neg_le_abs ((1 + nullY p₀ * ℓ i) * ℓ i)) hu0
      have h2 := mul_le_mul_of_nonneg_right huU (abs_nonneg ((1 + nullY p₀ * ℓ i) * ℓ i))
      linarith
    have h0R := hXf u₀ hu₀ le_rfl
    have hB : ∀ u ∈ Real.arctan '' I,
        ((γ ∘ Real.tan) u).1 ≤ (nullX p₀ + (-unipTime ℓ f p₀ + R) - yK) / √2 := by
      intro u hu
      rw [fst_eq_null]
      refine div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg 2)
      have hx : nullX ((γ ∘ Real.tan) u) ≤ nullX p₀ + (-unipTime ℓ f p₀ + R) := by
        rcases le_total u₀ u with h | h
        · linarith [hXf u hu h]
        · linarith [(null_le_of_le_top (hle' u hu u₀ hu₀ h)).2.1]
      linarith [hY u hu]
    exact hfi.2 (hfut (futureExtensible_unipDomain hd
      ⟨Real.pi / 2, fun u hu => (hsub hu).2.le⟩ hyK1 hB hY))
  -- some time with `T ≤ 0`
  have hdown : ∃ s ∈ I, unipTime ℓ f (γ s) ≤ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hd, hsub, htan, hpast, -⟩ := hpi.1.arctanReparam
    have hT : ∀ u ∈ Real.arctan '' I, 0 < unipTime ℓ f ((γ ∘ Real.tan) u) :=
      fun u hu => hcon _ (htan u hu)
    have hle' : ∀ u ∈ Real.arctan '' I, ∀ u' ∈ Real.arctan '' I, u ≤ u' →
        (minkowski (d + 1)).le ⊤ ((γ ∘ Real.tan) u) ((γ ∘ Real.tan) u') :=
      fun u hu u' hu' h => (minkowski (d + 1)).le_mono le_top (hd.le_of_le hu hu' h)
    obtain ⟨u₀, hu₀⟩ := hd.nonempty
    have hp₀ := hd.mem hu₀
    set p₀ := (γ ∘ Real.tan) u₀
    obtain ⟨yK, hyK1, hyK2, hfyK⟩ := hfβ (f (nullY p₀) + unipTime ℓ f p₀)
    have hYp : ∀ u ∈ Real.arctan '' I, u ≤ u₀ → nullY ((γ ∘ Real.tan) u) ≤ yK := by
      intro u hu h
      by_contra hlt
      push Not at hlt
      have hm : f yK ≤ f (nullY ((γ ∘ Real.tan) u)) :=
        hfm ⟨hyK1, hyK2⟩ ⟨(hd.mem hu).1, (hd.mem hu).2⟩ hlt.le
      have := unipTime_sub_ge (f := f) hℓ (hd.mem hu) hp₀ (hle' u hu u₀ hu₀ h)
      have := hT u hu
      linarith
    have hY : ∀ u ∈ Real.arctan '' I, nullY ((γ ∘ Real.tan) u) ≤ yK := by
      intro u hu
      rcases le_total u u₀ with h | h
      · exact hYp u hu h
      · exact (null_le_of_le_top (hle' u₀ hu₀ u hu h)).1.trans (hYp u₀ hu₀ le_rfl)
    set U := yK - nullY p₀
    set R := ∑ i, (2 * unipTime ℓ f p₀ * ((1 + nullY p₀ * ℓ i) ^ 2 +
      U * |(1 + nullY p₀ * ℓ i) * ℓ i|) + U * ℓ i ^ 2 * nullZ p₀ i ^ 2) / (1 + nullY p₀ * ℓ i) ^ 2
    have hXp : ∀ u ∈ Real.arctan '' I, u ≤ u₀ →
        nullX p₀ - nullX ((γ ∘ Real.tan) u) ≤ unipTime ℓ f p₀ + R := by
      intro u hu h
      have hq := hd.mem hu
      have hpq := hle' u hu u₀ hu₀ h
      have hyq := null_le_of_le_top hpq
      refine nullX_sub_le_aux hℓ hfm hq hp₀ hpq (by linarith [hT u hu])
        (by linarith [hY u hu]) _ _ (fun i => hℓ.2.1 _ hp₀.1 hp₀.2 i) (fun i => ?_) (fun i => by ring)
      have hu0 : 0 ≤ nullY ((γ ∘ Real.tan) u) - nullY p₀ := by linarith [hyq.1]
      have huU : nullY ((γ ∘ Real.tan) u) - nullY p₀ ≤ U := by linarith [hY u hu]
      have e : (1 + nullY ((γ ∘ Real.tan) u) * ℓ i) * (1 + nullY p₀ * ℓ i) =
          (1 + nullY p₀ * ℓ i) ^ 2 + (nullY ((γ ∘ Real.tan) u) - nullY p₀) *
            ((1 + nullY p₀ * ℓ i) * ℓ i) := by ring
      rw [e]
      have h1 := mul_le_mul_of_nonneg_left (le_abs_self ((1 + nullY p₀ * ℓ i) * ℓ i)) hu0
      have h2 := mul_le_mul_of_nonneg_right huU (abs_nonneg ((1 + nullY p₀ * ℓ i) * ℓ i))
      linarith
    have h0R := hXp u₀ hu₀ le_rfl
    have hA : ∀ u ∈ Real.arctan '' I,
        (nullX p₀ - (unipTime ℓ f p₀ + R) - yK) / √2 ≤ ((γ ∘ Real.tan) u).1 := by
      intro u hu
      rw [fst_eq_null]
      refine div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg 2)
      have hx : nullX p₀ - (unipTime ℓ f p₀ + R) ≤ nullX ((γ ∘ Real.tan) u) := by
        rcases le_total u u₀ with h | h
        · linarith [hXp u hu h]
        · linarith [(null_le_of_le_top (hle' u₀ hu₀ u hu h)).2.1]
      linarith [hY u hu]
    exact hpi.2 (hpast (pastExtensible_unipDomain hd
      ⟨-(Real.pi / 2), fun u hu => (hsub hu).1.le⟩ hyK2 hA hY))
  obtain ⟨s₂, hs₂, h₂⟩ := hup
  obtain ⟨s₁, hs₁, h₁⟩ := hdown
  have huniq : ∀ s ∈ I, ∀ s' ∈ I, unipTime ℓ f (γ s) = 0 → unipTime ℓ f (γ s') = 0 →
      γ s = γ s' := by
    intro s hs s' hs' h h'
    by_contra hne
    rcases le_total s s' with hss | hss
    · have := unipTime_lt hℓ hf (hΩ hs) (hΩ hs') (hle hs hs' hss) hne
      linarith
    · have := unipTime_lt hℓ hf (hΩ hs') (hΩ hs) (hle hs' hs hss) (Ne.symm hne)
      linarith
  have hex : ∃ s ∈ I, unipTime ℓ f (γ s) = 0 := by
    rcases le_total s₁ s₂ with h12 | h12
    · have hsub : Icc s₁ s₂ ⊆ I := hγ.1.ordConnected.out hs₁ hs₂
      have hcont : ContinuousOn (fun s => unipTime ℓ f (γ s)) (Icc s₁ s₂) :=
        (continuousOn_unipTime hℓ hfc).comp (hγ.1.continuousOn_Icc hs₁ hs₂)
          fun s hs => hΩ (hsub hs)
      obtain ⟨s, hs, hst⟩ := intermediate_value_Icc h12 hcont ⟨h₁, h₂⟩
      exact ⟨s, hsub hs, hst⟩
    · have := unipTime_le hℓ hfm (hΩ hs₂) (hΩ hs₁) (hle hs₂ hs₁ h12)
      exact ⟨s₁, hs₁, le_antisymm h₁ (h₂.trans this)⟩
  obtain ⟨s, hs, hsc⟩ := hex
  refine ⟨γ s, ⟨⟨s, hs, rfl⟩, mem_unipSlice_iff.2 ⟨hΩ hs, hsc⟩⟩, ?_⟩
  rintro _ ⟨⟨s', hs', rfl⟩, hs'c⟩
  exact huniq s' hs' s hs (mem_unipSlice_iff.1 hs'c).2 hsc


/-- **`T` is `A`-invariant** (`S_{f+c} = {T = c}` is `A`-invariant for every `c`). -/
theorem unipTime_unipAction (ℓ : Fin d → ℝ) (f : ℝ → ℝ) {α β : EReal}
    (hℓ : IsUnipComponent ℓ α β) (t : EuclideanSpace ℝ (Fin d)) {p : Minkowski (d + 1)}
    (hp : p ∈ unipDomain α β) : unipTime ℓ f (unipAction ℓ t p) = unipTime ℓ f p := by
  obtain ⟨hα, hβ⟩ := hp
  set y := nullY p
  set z := nullZ p
  have hc : ∀ i, 1 + y * ℓ i ≠ 0 := hℓ.2.1 y hα hβ
  have key : ∀ i, ℓ i * (z i + t i * (1 + y * ℓ i)) ^ 2 / (1 + y * ℓ i) =
      ℓ i * z i ^ 2 / (1 + y * ℓ i) + 2 * (ℓ i * z i * t i) + 2 * (ℓ i / 2 * t i ^ 2) +
        y * (ℓ i ^ 2 * t i ^ 2) := fun i => by
    have h1 := hc i
    rw [div_add' _ _ _ h1, div_add' _ _ _ h1, div_add' _ _ _ h1, div_left_inj' h1]
    ring
  simp only [unipTime, unipAction, nullX_ofNull, nullY_ofNull, nullZ_ofNull, unipPhi]
  show nullX p - ∑ i, ℓ i / 2 * t i ^ 2 - ∑ i, ℓ i * z i * t i - y / 2 * ∑ i, ℓ i ^ 2 * t i ^ 2 -
      (f y - 1 / 2 * ∑ i, ℓ i * (z i + t i * (1 + y * ℓ i)) ^ 2 / (1 + y * ℓ i)) =
    nullX p - (f y - 1 / 2 * ∑ i, ℓ i * z i ^ 2 / (1 + y * ℓ i))
  rw [Finset.sum_congr rfl fun i _ => key i, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

theorem isConnected_unipDomain {α β : EReal} (hαβ : α < β) :
    IsConnected (unipDomain (d := d) α β : Set (Minkowski (d + 1))) := by
  obtain ⟨y, hy1, hy2⟩ := EReal.lt_iff_exists_real_btwn.1 hαβ
  refine convex_unipDomain.isConnected ⟨ofNull 0 y 0, ?_⟩
  show α < ((nullY (ofNull 0 y (0 : EuclideanSpace ℝ (Fin d))) : ℝ) : EReal) ∧
    ((nullY (ofNull 0 y (0 : EuclideanSpace ℝ (Fin d))) : ℝ) : EReal) < β
  rw [nullY_ofNull]; exact ⟨hy1, hy2⟩

/-- **`S_f` is acausal in `Ω`** for strictly increasing `f`: `T = x − Φ` is strictly increasing
along `≤` and equals `f(y)` on `S_f`. (Extracted from `isCauchySurface_unip`, for the frame
transport.) -/
theorem isAcausal_unipSlice {ℓ : Fin d → ℝ} {α β : EReal} (hℓ : IsUnipComponent ℓ α β)
    {f : ℝ → ℝ} (hf : StrictMonoOn f {y : ℝ | α < y ∧ (y : EReal) < β}) :
    (flatCausality (d + 1) (unipDomain (d := d) α β)).IsAcausal
      (Subtype.val ⁻¹' unipSlice ℓ f α β) := by
  intro x hx y hy h
  have hle' := (minkowski (d + 1)).le_mono le_top ((flat_le_top_subtype_iff _ _ _).1 h)
  by_contra hne
  have h1 := unipTime_lt hℓ hf x.2 y.2 hle' fun he => hne (Subtype.ext he)
  rw [(mem_unipSlice_iff.1 hx).2, (mem_unipSlice_iff.1 hy).2] at h1
  exact lt_irrefl _ h1

section UnipQuotient

variable {ℓ : Fin d → ℝ} {α β : EReal} (Γ : Subgroup (isom (d + 1)))
  [FlatQuotient.Invariant Γ (unipDomain (d := d) α β)]

/-- **A free group acting through `A` acts acausally on `Ω`**: `T` (for `f = id`) is invariant
and strictly increasing along `≤`. -/
theorem actsAcausally_unip (hℓ : IsUnipComponent ℓ α β)
    (hΓ : ∀ γ ∈ Γ, ∃ t, ∀ p : Minkowski (d + 1), γ • p = unipAction ℓ t p) [IsCancelSMul Γ (unipDomain (d := d) α β)] :
    FlatQuotient.ActsAcausally Γ (unipDomain (d := d) α β) := by
  intro γ hne x hle
  have hle' := (minkowski (d + 1)).le_mono le_top ((flat_le_top_subtype_iff _ _ _).1 hle)
  by_cases hx : (x : Minkowski (d + 1)) = ((γ • x : unipDomain (d := d) α β) : Minkowski (d + 1))
  · apply hne
    have : γ • x = (1 : Γ) • x := by rw [one_smul]; exact (Subtype.ext hx).symm
    exact IsCancelSMul.right_cancel γ 1 x this
  · have h1 := unipTime_lt (f := id) hℓ (strictMono_id.strictMonoOn _) x.2 (γ • x).2 hle' hx
    obtain ⟨t, ht⟩ := hΓ γ γ.2
    rw [FlatQuotient.coe_smul, ht, unipTime_unipAction ℓ id hℓ t x.2] at h1
    exact lt_irrefl _ h1

variable [ProperlyDiscontinuousSMul Γ (unipDomain (d := d) α β)] [IsCancelSMul Γ (unipDomain (d := d) α β)]

/-- **[3.U] `S_f` descends to an acausal Cauchy surface of `Γ\Ω`** (l.743–744: "the quotient of
`Ω` by `Γ` is globally hyperbolic"), for every inextensible causal curve, for any free, properly
discontinuous `Γ` acting through `A` (`IsUnipotentSpacetime`'s groups). -/
theorem isCauchySurface_unip (hℓ : IsUnipComponent ℓ α β)
    (hΓ : ∀ γ ∈ Γ, ∃ t, ∀ p : Minkowski (d + 1), γ • p = unipAction ℓ t p) (f : ℝ → ℝ)
    (hf : StrictMonoOn f {y : ℝ | α < y ∧ (y : EReal) < β})
    (hfc : ContinuousOn f {y : ℝ | α < y ∧ (y : EReal) < β})
    (hfα : ∀ C : ℝ, ∃ y : ℝ, α < y ∧ (y : EReal) < β ∧ f y < C)
    (hfβ : ∀ C : ℝ, ∃ y : ℝ, α < y ∧ (y : EReal) < β ∧ C < f y) :
    (flatCausality (d + 1) (FlatQuotient Γ (unipDomain (d := d) α β))).IsCauchySurface
        (FlatQuotient.proj _ _ '' (Subtype.val ⁻¹' unipSlice ℓ f α β)) ∧
      (flatCausality (d + 1) (FlatQuotient Γ (unipDomain (d := d) α β))).IsAcausal
        (FlatQuotient.proj _ _ '' (Subtype.val ⁻¹' unipSlice ℓ f α β)) := by
  have hinv : ∀ γ ∈ Γ, ∀ p ∈ unipSlice ℓ f α β, γ • p ∈ unipSlice ℓ f α β := by
    intro γ hγ p hp
    obtain ⟨t, ht⟩ := hΓ γ hγ
    rw [ht]; exact unipAction_mem_unipSlice ℓ f hℓ t hp
  refine ⟨FlatQuotient.isCauchySurface_image_of_isCauchySurfaceOn Γ _
    (actsAcausally_unip Γ hℓ hΓ) (fun p hp => hp.1) hinv
    (isCauchySurfaceOn_unipSlice ℓ f hℓ hf hfc hfα hfβ), ?_⟩
  exact FlatQuotient.isAcausal_image _ _ (fun γ p hp => hinv γ γ.2 p hp) (isAcausal_unipSlice hℓ hf)

/-- **[3.U] Unipotent quotients are GH in Barbot's sense** (a Cauchy surface; l.743–744), given
one `f` as in `isCauchySurfaceOn_unipSlice` (the paper's `f = ∫ a²`, l.707–711, is one; the
existence of such an `f` for every component is not written here). -/
theorem barbotGH_unip (hℓ : IsUnipComponent ℓ α β)
    (hΓ : ∀ γ ∈ Γ, ∃ t, ∀ p : Minkowski (d + 1), γ • p = unipAction ℓ t p) (f : ℝ → ℝ)
    (hf : StrictMonoOn f {y : ℝ | α < y ∧ (y : EReal) < β})
    (hfc : ContinuousOn f {y : ℝ | α < y ∧ (y : EReal) < β})
    (hfα : ∀ C : ℝ, ∃ y : ℝ, α < y ∧ (y : EReal) < β ∧ f y < C)
    (hfβ : ∀ C : ℝ, ∃ y : ℝ, α < y ∧ (y : EReal) < β ∧ C < f y) :
    BarbotGH (FlatQuotient.toFlatSpacetime Γ (unipDomain (d := d) α β) (isConnected_unipDomain hℓ.1)) :=
  ⟨_, (isCauchySurface_unip Γ hℓ hΓ f hf hfc hfα hfβ).1⟩

end UnipQuotient

end Unipotent

/-! ### Frame transport: conjugation by `φ ∈ isom` preserves everything

The families `IsTranslationSpacetime`, `IsMisnerSpacetime` quantify over a frame `φ`; the theorems
above are for `φ = 1`. Conjugation by `φ` carries `(Γ, Ω)` to `(φΓφ⁻¹, φΩ)`: `φ` is a homeomorphism
`Ω ≃ₜ φΩ` (`frameHomeomorph`), equivariant along `Γ ≃* φΓφ⁻¹` (`frameConjEquiv`), and an
isomorphism of the causal relations (`le_iff_le_isomImage`). Hence freeness, proper
discontinuity, acausality, the finiteness of `{γ | x ≤ γ y}`, global hyperbolicity of `Ω` and
invariant Cauchy surfaces all transport (`gh_frameConj`, `barbotGH_frameConj`). -/

section FrameTransport

open FlatQuotient

variable (φ : isom d) (Γ : Subgroup (isom d)) (Ω : Opens (Minkowski d))

/-- **`Γ ≃* φΓφ⁻¹`**, conjugation by `φ`. -/
noncomputable def frameConjEquiv : Γ ≃* frameConj φ Γ :=
  Γ.equivMapOfInjective (MulAut.conj φ).toMonoidHom (MulAut.conj φ).injective

@[simp] theorem coe_frameConjEquiv (γ : Γ) :
    ((frameConjEquiv φ Γ γ : frameConj φ Γ) : isom d) = φ * γ * φ⁻¹ := rfl

/-- **The isometry `φ` as a homeomorphism `Ω ≃ₜ φΩ`.** -/
noncomputable def frameHomeomorph : Ω ≃ₜ isomImage φ Ω :=
  (isom.toHomeomorph φ).subtype fun _ => smul_mem_isomImage.symm

@[simp] theorem coe_frameHomeomorph (p : Ω) :
    ((frameHomeomorph φ Ω p : isomImage φ Ω) : Minkowski d) = φ • (p : Minkowski d) := rfl

/-- **`φΩ` is invariant under `φΓφ⁻¹`.** -/
instance instInvariantFrameConj [Invariant Γ Ω] : Invariant (frameConj φ Γ) (isomImage φ Ω) := by
  refine ⟨fun γ' p hp => ?_⟩
  obtain ⟨γ, hγ, hγ'⟩ := Subgroup.mem_map.1 γ'.2
  rw [mem_isomImage] at hp ⊢
  rw [← hγ']
  have := Invariant.smul_mem ⟨γ, hγ⟩ _ hp
  simpa [MulAut.conj_apply, mul_smul] using this

/-- `φ` intertwines the two actions. -/
theorem frameHomeomorph_smul [Invariant Γ Ω] (γ : Γ) (p : Ω) :
    frameHomeomorph φ Ω (γ • p) = frameConjEquiv φ Γ γ • frameHomeomorph φ Ω p := by
  apply Subtype.ext
  simp [mul_smul]

/-- `φ` is an isomorphism of the flat causal relations of `Ω` and `φΩ`. -/
theorem le_frameHomeomorph_iff (a b : Ω) :
    (flatCausality d (isomImage φ Ω)).le ⊤ (frameHomeomorph φ Ω a) (frameHomeomorph φ Ω b) ↔
      (flatCausality d Ω).le ⊤ a b := by
  rw [flat_le_top_subtype_iff, flat_le_top_subtype_iff]
  exact (le_iff_le_isomImage φ Ω a b).symm

/-- **`φΓφ⁻¹` acts freely on `φΩ`** when `Γ` acts freely on `Ω`. -/
instance instIsCancelSMulFrameConj [Invariant Γ Ω] [IsCancelSMul Γ Ω] :
    IsCancelSMul (frameConj φ Γ) (isomImage φ Ω) := by
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro γ' x hx
  obtain ⟨γ, rfl⟩ := (frameConjEquiv φ Γ).surjective γ'
  obtain ⟨y, rfl⟩ := (frameHomeomorph φ Ω).surjective x
  rw [← frameHomeomorph_smul] at hx
  have h1 : γ • y = y := (frameHomeomorph φ Ω).injective hx
  rw [(isCancelSMul_iff_eq_one_of_smul_eq.1 inferInstance) γ y h1, map_one]

/-- **`φΓφ⁻¹` acts properly discontinuously on `φΩ`** when `Γ` does on `Ω`. -/
instance instProperlyDiscontinuousSMulFrameConj [Invariant Γ Ω] [ProperlyDiscontinuousSMul Γ Ω] :
    ProperlyDiscontinuousSMul (frameConj φ Γ) (isomImage φ Ω) := by
  refine ⟨fun {K L} hK hL => ?_⟩
  set e := frameHomeomorph φ Ω
  have hK' : IsCompact (e ⁻¹' K) := e.isCompact_preimage.2 hK
  have hL' : IsCompact (e ⁻¹' L) := e.isCompact_preimage.2 hL
  refine (((ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := Γ) hK' hL').image
    (frameConjEquiv φ Γ))).subset ?_
  rintro γ' ⟨_, ⟨k, hk, rfl⟩, hl⟩
  obtain ⟨γ, rfl⟩ := (frameConjEquiv φ Γ).surjective γ'
  refine ⟨γ, ⟨γ • e.symm k, ⟨e.symm k, by simpa using hk, rfl⟩, ?_⟩, rfl⟩
  show e (γ • e.symm k) ∈ L
  rw [frameHomeomorph_smul, e.apply_symm_apply]
  exact hl

/-- **Acausality transports.** -/
theorem actsAcausally_frameConj [Invariant Γ Ω] (hac : ActsAcausally Γ Ω) :
    ActsAcausally (frameConj φ Γ) (isomImage φ Ω) := by
  intro γ' hne x hle
  obtain ⟨γ, rfl⟩ := (frameConjEquiv φ Γ).surjective γ'
  obtain ⟨y, rfl⟩ := (frameHomeomorph φ Ω).surjective x
  rw [← frameHomeomorph_smul, le_frameHomeomorph_iff] at hle
  exact hac γ (fun h => hne (by rw [h, map_one])) y hle

/-- **The finiteness of `{γ | x ≤ γ y}` transports.** -/
theorem finite_le_frameConj [Invariant Γ Ω]
    (hfin : ∀ x y : Ω, {γ : Γ | (flatCausality d Ω).le ⊤ x (γ • y)}.Finite)
    (x y : isomImage φ Ω) :
    {γ : frameConj φ Γ | (flatCausality d (isomImage φ Ω)).le ⊤ x (γ • y)}.Finite := by
  obtain ⟨x, rfl⟩ := (frameHomeomorph φ Ω).surjective x
  obtain ⟨y, rfl⟩ := (frameHomeomorph φ Ω).surjective y
  refine ((hfin x y).image (frameConjEquiv φ Γ)).subset ?_
  intro γ' hγ'
  obtain ⟨γ, rfl⟩ := (frameConjEquiv φ Γ).surjective γ'
  refine ⟨γ, ?_, rfl⟩
  have hγ'' : (flatCausality d (isomImage φ Ω)).le ⊤ (frameHomeomorph φ Ω x)
      (frameConjEquiv φ Γ γ • frameHomeomorph φ Ω y) := hγ'
  rwa [← frameHomeomorph_smul, le_frameHomeomorph_iff] at hγ''

/-- `≤_{φΩ}` read through `φ⁻¹`. -/
theorem le_isomImage_iff (p q : Minkowski d) :
    (minkowski d).le (isomImage φ Ω) p q ↔ (minkowski d).le Ω (φ⁻¹ • p) (φ⁻¹ • q) := by
  have := le_iff_le_isomImage φ⁻¹ (isomImage φ Ω) p q
  rwa [isomImage_inv_isomImage] at this

/-- **Global hyperbolicity of an open set of `𝐌ⁿ` transports along an isometry.** -/
theorem globallyHyperbolicOn_isomImage (h : (minkowski d).GloballyHyperbolicOn Ω) :
    (minkowski d).GloballyHyperbolicOn (isomImage φ Ω) := by
  refine ⟨fun x y hxy hyx => ?_, fun p q => ?_⟩
  · rw [le_isomImage_iff] at hxy hyx
    exact MulAction.injective φ⁻¹ (h.1 hxy hyx)
  · have hD : (minkowski d).diamond (isomImage φ Ω) p q =
        (isom.toHomeomorph φ⁻¹) ⁻¹' (minkowski d).diamond Ω (φ⁻¹ • p) (φ⁻¹ • q) := by
      ext z
      simp only [Causality.mem_diamond, mem_preimage, le_isomImage_iff, isom.coe_toHomeomorph]
    rw [hD]
    exact (isom.toHomeomorph φ⁻¹).isCompact_preimage.2 (h.2 _ _)

/-- **Cauchy surfaces of an open set of `𝐌ⁿ` transport along an isometry.** -/
theorem isCauchySurfaceOn_isomImage {S : Set (Minkowski d)} (hS : S ⊆ Ω)
    (h : (minkowski d).IsCauchySurfaceOn Ω S) :
    (minkowski d).IsCauchySurfaceOn (isomImage φ Ω) ((fun p => φ • p) '' S) :=
  ((isom_isEMorphism φ).isCauchySurfaceOn_image_iff (MulAction.injective φ).injOn le_top rfl
    hS).1 h

/-- A `Γ`-invariant set goes to a `φΓφ⁻¹`-invariant set. -/
theorem image_invariant_frameConj {S : Set (Minkowski d)} (hinv : ∀ γ ∈ Γ, ∀ p ∈ S, γ • p ∈ S) :
    ∀ γ' ∈ frameConj φ Γ, ∀ p ∈ (fun p => φ • p) '' S, γ' • p ∈ (fun p => φ • p) '' S := by
  rintro γ' hγ' _ ⟨p, hp, rfl⟩
  obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hγ'
  exact ⟨γ • p, hinv γ hγ p hp, by simp [MulAut.conj_apply, mul_smul]⟩

/-- **`φΩ` is connected when `Ω` is.** -/
theorem isConnected_isomImage (hΩ : IsConnected (Ω : Set (Minkowski d))) :
    IsConnected (isomImage φ Ω : Set (Minkowski d)) := by
  rw [coe_isomImage]
  exact hΩ.image _ (continuous_const_smul φ).continuousOn

/-- **ETT's GH of `Γ\Ω` transports to `φΓφ⁻¹\Ω'`**, for any `Ω' = φΩ` (stated with `Ω'` so that
`Ω' = ⊤` needs no rewriting): the hypotheses of `gh_toFlatSpacetime` transport. -/
theorem gh_frameConj [Invariant Γ Ω] (Ω' : Opens (Minkowski d)) (hΩ' : Ω' = isomImage φ Ω)
    [Invariant (frameConj φ Γ) Ω'] [ProperlyDiscontinuousSMul (frameConj φ Γ) Ω']
    [IsCancelSMul (frameConj φ Γ) Ω'] (hΩ'c : IsConnected (Ω' : Set (Minkowski d)))
    (hac : ActsAcausally Γ Ω) (hGH : (minkowski d).GloballyHyperbolicOn Ω)
    (hfin : ∀ x y : Ω, {γ : Γ | (flatCausality d Ω).le ⊤ x (γ • y)}.Finite) :
    GH (toFlatSpacetime (frameConj φ Γ) Ω' hΩ'c) := by
  subst hΩ'
  exact gh_toFlatSpacetime _ _ hΩ'c (actsAcausally_frameConj φ Γ Ω hac)
    (globallyHyperbolic_subtype _ (globallyHyperbolicOn_isomImage φ Ω hGH))
    (finite_le_frameConj φ Γ Ω hfin)

/-- **Barbot's GH of `Γ\Ω` transports to `φΓφ⁻¹\Ω'`**, `Ω' = φΩ`: the image `φS` of a
`Γ`-invariant Cauchy surface `S ⊆ Ω` descends to a Cauchy surface. -/
theorem barbotGH_frameConj [Invariant Γ Ω] (Ω' : Opens (Minkowski d)) (hΩ' : Ω' = isomImage φ Ω)
    [Invariant (frameConj φ Γ) Ω'] [ProperlyDiscontinuousSMul (frameConj φ Γ) Ω']
    [IsCancelSMul (frameConj φ Γ) Ω'] (hΩ'c : IsConnected (Ω' : Set (Minkowski d)))
    (hac : ActsAcausally Γ Ω) {S : Set (Minkowski d)} (hSΩ : S ⊆ Ω)
    (hinv : ∀ γ ∈ Γ, ∀ p ∈ S, γ • p ∈ S) (hS : (minkowski d).IsCauchySurfaceOn Ω S) :
    BarbotGH (toFlatSpacetime (frameConj φ Γ) Ω' hΩ'c) := by
  subst hΩ'
  exact ⟨_, isCauchySurface_image_of_isCauchySurfaceOn _ _ (actsAcausally_frameConj φ Γ Ω hac)
    (image_mono hSΩ) (image_invariant_frameConj φ Γ hinv) (isCauchySurfaceOn_isomImage φ Ω hSΩ hS)⟩

/-- **Freeness transports to `Ω' = φΩ`** (stated with `Ω'` so that `Ω' = ⊤` needs no rewriting). -/
theorem isCancelSMul_frameConj [Invariant Γ Ω] [IsCancelSMul Γ Ω] (Ω' : Opens (Minkowski d))
    (hΩ' : Ω' = isomImage φ Ω) [Invariant (frameConj φ Γ) Ω'] :
    IsCancelSMul (frameConj φ Γ) Ω' := by
  subst hΩ'
  exact instIsCancelSMulFrameConj φ Γ Ω

/-- **Proper discontinuity transports to `Ω' = φΩ`** (stated with `Ω'` so that `Ω' = ⊤` needs
no rewriting). -/
theorem properlyDiscontinuousSMul_frameConj [Invariant Γ Ω] [ProperlyDiscontinuousSMul Γ Ω]
    (Ω' : Opens (Minkowski d)) (hΩ' : Ω' = isomImage φ Ω) [Invariant (frameConj φ Γ) Ω'] :
    ProperlyDiscontinuousSMul (frameConj φ Γ) Ω' := by
  subst hΩ'
  exact instProperlyDiscontinuousSMulFrameConj φ Γ Ω

/-! #### [3.T] in a general frame -/

variable (Λ : AddSubgroup (EuclideanSpace ℝ (Fin d)))

/-- **`𝐌ⁿ` is invariant under `φ (horizGroup Λ) φ⁻¹`.** -/
instance instInvariantFrameConjHorizTop :
    Invariant (frameConj φ (horizGroup Λ)) (⊤ : Opens (Minkowski d)) :=
  ⟨fun _ _ _ => trivial⟩

/-- **`φ (horizGroup Λ) φ⁻¹` acts freely on `𝐌ⁿ`** (`isCancelSMul_frameConj` at `Ω = Ω' = ⊤`). -/
instance instIsCancelSMulFrameConjHorizTop :
    IsCancelSMul (frameConj φ (horizGroup Λ)) (⊤ : Opens (Minkowski d)) :=
  isCancelSMul_frameConj φ _ ⊤ ⊤ (isomImage_top φ).symm

/-- **`φ (horizGroup Λ) φ⁻¹` acts properly discontinuously on `𝐌ⁿ`** for ball-finite `Λ`
(`properlyDiscontinuousSMul_frameConj` at `Ω = Ω' = ⊤`). -/
instance instProperlyDiscontinuousSMulFrameConjHorizTop [BallFinite Λ] :
    ProperlyDiscontinuousSMul (frameConj φ (horizGroup Λ)) (⊤ : Opens (Minkowski d)) :=
  properlyDiscontinuousSMul_frameConj φ _ ⊤ ⊤ (isomImage_top φ).symm

variable [BallFinite Λ]

/-- **[3.T] in the frame `φ`: `φΓφ⁻¹\𝐌ⁿ` is a translation spacetime** (the witness of
`isTranslationSpacetime_quotient` at an arbitrary frame). -/
theorem isTranslationSpacetime_frame :
    IsTranslationSpacetime (FlatQuotient.toFlatSpacetime (frameConj φ (horizGroup Λ)) ⊤
      FlatQuotient.isConnected_top) :=
  ⟨φ, Λ, inferInstance, FlatQuotient.isQuotientOf_toFlatSpacetime _ _ _⟩

/-- **[3.T] in the frame `φ`: the translation spacetime is GH** (ETT's GH). -/
theorem gh_translation_frame :
    GH (FlatQuotient.toFlatSpacetime (frameConj φ (horizGroup Λ)) ⊤
      FlatQuotient.isConnected_top) :=
  gh_frameConj φ (horizGroup Λ) ⊤ ⊤ (isomImage_top φ).symm _ (actsAcausally_horiz Λ)
    ((minkowski d).globallyHyperbolicOn_top.2 minkowski_globallyHyperbolic) (finite_le_horiz Λ)

/-- **[3.T] in the frame `φ`: the translation spacetime is GH in Barbot's sense** (the image of
`φ{t = 0}`). -/
theorem barbotGH_translation_frame :
    BarbotGH (FlatQuotient.toFlatSpacetime (frameConj φ (horizGroup Λ)) ⊤
      FlatQuotient.isConnected_top) := by
  refine barbotGH_frameConj φ (horizGroup Λ) ⊤ ⊤ (isomImage_top φ).symm _ (actsAcausally_horiz Λ)
    (S := graph fun _ : EuclideanSpace ℝ (Fin d) => (0 : ℝ)) (fun _ _ => trivial) ?_
    ((minkowski d).isCauchySurfaceOn_top.2 isCauchySurface_graph_zero)
  intro γ hγ p hp
  obtain ⟨v, -, rfl⟩ := mem_horizGroup.1 hγ
  simp only [mem_graph] at hp ⊢
  rw [fst_horizTranslation_smul]
  exact hp

/-! #### [3.M] in a general frame -/

variable {L : AddSubgroup (ℝ × EuclideanSpace ℝ (Fin d))} [BallFinite L]

/-- **[3.M] in the frame `φ`: `φΓφ⁻¹\φΩ` is GH** (ETT's GH). -/
theorem gh_misner_frame (φ : isom (d + 1)) :
    GH (FlatQuotient.toFlatSpacetime (frameConj φ (misnerGroup L)) (isomImage φ (misnerWedge d))
      (isConnected_isomImage φ _ (isConnected_omegaPlus (misnerRegular d)))) :=
  gh_frameConj φ (misnerGroup L) (misnerWedge d) _ rfl _
    (actsAcausally_of_preservesOmega (h := misnerRegular d) preservesOmega_misner)
    (misnerRegular d).regular.globallyHyperbolicOn
    (finite_le_of_preservesOmega (h := misnerRegular d) preservesOmega_misner)

/-- **[3.M] in the frame `φ`: `φΓφ⁻¹\φΩ` is GH in Barbot's sense** (the image of the `φ`-image
of the level `T = 1` of the cosmological time of the wedge). -/
theorem barbotGH_misner_frame (φ : isom (d + 1)) :
    BarbotGH (FlatQuotient.toFlatSpacetime (frameConj φ (misnerGroup L))
      (isomImage φ (misnerWedge d))
      (isConnected_isomImage φ _ (isConnected_omegaPlus (misnerRegular d)))) := by
  refine barbotGH_frameConj φ (misnerGroup L) (misnerWedge d) _ rfl _
    (actsAcausally_of_preservesOmega (h := misnerRegular d) preservesOmega_misner)
    (cosmoLevel_subset 1) (fun γ hγ p hp => ⟨?_, ?_⟩)
    (isCauchySurfaceOn_cosmoLevel (misnerRegular d) one_pos)
  · have h' : p ∈ omegaPlus (misnerΛ d) := hp.1
    rw [← preservesOmega_misner γ hγ] at h'
    exact h'
  · rw [cosmoTime_smul (preservesOmega_misner γ hγ)]; exact hp.2

/-- **[3.M] in the frame `φ`: the witness.** For `L` with an element of nonzero boost parameter,
`φΓφ⁻¹\φΩ` is a Misner spacetime. -/
theorem isMisnerSpacetime_frame (φ : isom (d + 1)) (hL : ∃ x ∈ L, x.1 ≠ 0) :
    IsMisnerSpacetime (FlatQuotient.toFlatSpacetime (frameConj φ (misnerGroup L))
      (isomImage φ (misnerWedge d))
      (isConnected_isomImage φ _ (isConnected_omegaPlus (misnerRegular d)))) :=
  ⟨φ, L, inferInstance, hL, Or.inl (FlatQuotient.isQuotientOf_toFlatSpacetime _ _ _)⟩

/-! #### [3.U] in a general frame -/

/-- **[3.U] in the frame `φ`: `φΓφ⁻¹\φΩ` is GH in Barbot's sense** (the image of `φ S_f`), under
the hypotheses of `barbotGH_unip`. -/
theorem barbotGH_unip_frame (φ : isom (d + 1)) {ℓ : Fin d → ℝ} {α β : EReal}
    (Γ : Subgroup (isom (d + 1))) [Invariant Γ (unipDomain (d := d) α β)]
    [ProperlyDiscontinuousSMul Γ (unipDomain (d := d) α β)]
    [IsCancelSMul Γ (unipDomain (d := d) α β)] (hℓ : IsUnipComponent ℓ α β)
    (hΓ : ∀ γ ∈ Γ, ∃ t, ∀ p : Minkowski (d + 1), γ • p = unipAction ℓ t p) (f : ℝ → ℝ)
    (hf : StrictMonoOn f {y : ℝ | α < y ∧ (y : EReal) < β})
    (hfc : ContinuousOn f {y : ℝ | α < y ∧ (y : EReal) < β})
    (hfα : ∀ C : ℝ, ∃ y : ℝ, α < y ∧ (y : EReal) < β ∧ f y < C)
    (hfβ : ∀ C : ℝ, ∃ y : ℝ, α < y ∧ (y : EReal) < β ∧ C < f y) :
    BarbotGH (FlatQuotient.toFlatSpacetime (frameConj φ Γ) (isomImage φ (unipDomain (d := d) α β))
      (isConnected_isomImage φ _ (isConnected_unipDomain hℓ.1))) := by
  refine barbotGH_frameConj φ Γ (unipDomain (d := d) α β) _ rfl _ (actsAcausally_unip Γ hℓ hΓ)
    (S := unipSlice ℓ f α β) (fun p hp => hp.1) ?_ (isCauchySurfaceOn_unipSlice ℓ f hℓ hf hfc hfα hfβ)
  intro γ hγ p hp
  obtain ⟨t, ht⟩ := hΓ γ hγ
  rw [ht]; exact unipAction_mem_unipSlice ℓ f hℓ t hp

/-- **[3.U] in the frame `φ`: `φ S_f` is a Cauchy surface of `φΩ`** (every inextensible causal
curve; `isCauchySurfaceOn_unipSlice` transported along `φ`). -/
theorem isCauchySurfaceOn_unipSlice_frame (φ : isom (d + 1)) (ℓ : Fin d → ℝ) (f : ℝ → ℝ)
    {α β : EReal} (hℓ : IsUnipComponent ℓ α β)
    (hf : StrictMonoOn f {y : ℝ | α < y ∧ (y : EReal) < β})
    (hfc : ContinuousOn f {y : ℝ | α < y ∧ (y : EReal) < β})
    (hfα : ∀ C : ℝ, ∃ y : ℝ, α < y ∧ (y : EReal) < β ∧ f y < C)
    (hfβ : ∀ C : ℝ, ∃ y : ℝ, α < y ∧ (y : EReal) < β ∧ C < f y) :
    (minkowski (d + 1)).IsCauchySurfaceOn (isomImage φ (unipDomain (d := d) α β))
      ((fun p => φ • p) '' unipSlice ℓ f α β) :=
  isCauchySurfaceOn_isomImage φ _ (fun _ hp => hp.1)
    (isCauchySurfaceOn_unipSlice ℓ f hℓ hf hfc hfα hfβ)

/-- **[3.U] in the frame `φ`: `φ S_f` descends to an acausal Cauchy surface of `φΓφ⁻¹\φΩ`**
(`isCauchySurface_unip` transported along `φ`, same hypotheses). -/
theorem isCauchySurface_unip_frame (φ : isom (d + 1)) {ℓ : Fin d → ℝ} {α β : EReal}
    (Γ : Subgroup (isom (d + 1))) [Invariant Γ (unipDomain (d := d) α β)]
    [ProperlyDiscontinuousSMul Γ (unipDomain (d := d) α β)]
    [IsCancelSMul Γ (unipDomain (d := d) α β)] (hℓ : IsUnipComponent ℓ α β)
    (hΓ : ∀ γ ∈ Γ, ∃ t, ∀ p : Minkowski (d + 1), γ • p = unipAction ℓ t p) (f : ℝ → ℝ)
    (hf : StrictMonoOn f {y : ℝ | α < y ∧ (y : EReal) < β})
    (hfc : ContinuousOn f {y : ℝ | α < y ∧ (y : EReal) < β})
    (hfα : ∀ C : ℝ, ∃ y : ℝ, α < y ∧ (y : EReal) < β ∧ f y < C)
    (hfβ : ∀ C : ℝ, ∃ y : ℝ, α < y ∧ (y : EReal) < β ∧ C < f y) :
    (flatCausality (d + 1)
        (FlatQuotient (frameConj φ Γ) (isomImage φ (unipDomain (d := d) α β)))).IsCauchySurface
        (FlatQuotient.proj _ _ '' (Subtype.val ⁻¹' ((fun p => φ • p) '' unipSlice ℓ f α β))) ∧
      (flatCausality (d + 1)
        (FlatQuotient (frameConj φ Γ) (isomImage φ (unipDomain (d := d) α β)))).IsAcausal
        (FlatQuotient.proj _ _ '' (Subtype.val ⁻¹' ((fun p => φ • p) '' unipSlice ℓ f α β))) := by
  have hinv : ∀ γ ∈ Γ, ∀ p ∈ unipSlice ℓ f α β, γ • p ∈ unipSlice ℓ f α β := by
    intro γ hγ p hp
    obtain ⟨t, ht⟩ := hΓ γ hγ
    rw [ht]; exact unipAction_mem_unipSlice ℓ f hℓ t hp
  refine ⟨isCauchySurface_image_of_isCauchySurfaceOn _ _
    (actsAcausally_frameConj φ Γ _ (actsAcausally_unip Γ hℓ hΓ)) (image_mono fun _ hp => hp.1)
    (image_invariant_frameConj φ Γ hinv)
    (isCauchySurfaceOn_unipSlice_frame φ ℓ f hℓ hf hfc hfα hfβ), ?_⟩
  refine FlatQuotient.isAcausal_image _ _
    (fun γ p hp => image_invariant_frameConj φ Γ hinv γ γ.2 p hp) ?_
  intro x hx y hy h
  obtain ⟨a, rfl⟩ := (frameHomeomorph φ (unipDomain (d := d) α β)).surjective x
  obtain ⟨b, rfl⟩ := (frameHomeomorph φ (unipDomain (d := d) α β)).surjective y
  rw [le_frameHomeomorph_iff] at h
  have hmem : ∀ c : unipDomain (d := d) α β,
      ((frameHomeomorph φ _ c : isomImage φ _) : Minkowski (d + 1)) ∈
        (fun p => φ • p) '' unipSlice ℓ f α β → (c : Minkowski (d + 1)) ∈ unipSlice ℓ f α β := by
    rintro c ⟨p, hp, hpc⟩
    have hpc' : φ • p = φ • (c : Minkowski (d + 1)) := hpc
    rwa [← MulAction.injective φ hpc']
  rw [isAcausal_unipSlice hℓ hf a (hmem a hx) b (hmem b hy) h]

end FrameTransport

end Causal.Flat
