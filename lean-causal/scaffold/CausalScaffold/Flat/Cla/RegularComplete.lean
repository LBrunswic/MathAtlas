import CausalScaffold.Flat.Nonloxodromic
import CausalScaffold.Flat.TitsNull
import CausalScaffold.Flat.Loxodromic
import CausalScaffold.CompactCauchy
import CausalScaffold.CurvesExtend

/-!
# `CausalScaffold.Flat.Cla.RegularComplete` — quotients of regular domains are Cauchy-complete

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257); line
numbers are those of the labelled `papers/barbot/legacy/labeled/GHFspace.tex`. **No label is
marked**: every statement below is proved with no `sorry`, but each is the paper's statement in
the library's reading (SCOPE), so the rows are `partial` (kb/0011, DEC-27).

* `bcor:level_sets_complete` — `GHFspace.tex:1109` (Cor 4.13): `cosmoLevel_completeSpace_inducedLength`,
  every level `S_t` (`t > 0`) of the cosmological time of `Ω⁺(Λ)` is complete for its induced
  length (`InducedLength`, DEC-35), for `CosmoRegular Λ`.
* `bprop:regular_cauchy_complete` — `GHFspace.tex:1148` (Prop 4.14), Cauchy-completeness, both
  time orientations and descended to every quotient: `isCauchyComplete_of_isQuotientOf_regular`
  (the statement dispatched for Classification's `amgh_of_isMisnerSpacetime` and
  `amgh_of_isCHCentralExtension`, [11.i] l.3568–3571): a spacetime `M₁ = φΓφ⁻¹\φΩ`, `Ω` the future
  regular domain `Ω⁺(Λ)` or the past one `Ω⁻(Λ)` (two null directions), is `IsCauchyComplete`.
* (A), exported for reuse: `isCauchyComplete_of_isQuotientOf_of_invariant` — the descent: a
  `Γ`-invariant Cauchy surface of `Ω`, spacelike Lipschitz, complete for its induced length, with
  the length topology finer than the subspace one, makes an acausal quotient `Γ\Ω` Cauchy-complete.

> The Gauss map $n: S_{t} \rightarrow {\mathbb H}^{n-1}$, where ${\mathbb H}^{n-1}$ is equipped
> with its usual hyperbolic metric is $\frac{1}{t}$-Lipschitz. (l.1075–1077)

> Every $S_{t}$ is complete. (l.1110)

> Since $S_{t}$ is riemannian, completeness notions are all equivalent. Let $s \mapsto p(s)$ be
> an incomplete geodesic in $S_{t}$ defined on $[0, s_{\infty}[$, parametrized by unit length.
> According to proposition \ref{lip}, $s \mapsto n(c(s))$ must converge in ${\mathbb H}^{n-1}$ to
> some limit point $n_{\infty}$. (l.1113–1118)

> Future complete regular convex domains are globally hyperbolic Cauchy-complete, admitting as
> Cauchy hypersurfaces the level sets of the cosmological time function. (l.1149–1151)

> (i) Translation spacetimes, Misner spacetimes, and twisted products of Cauchy-hyperbolic
> spacetimes by flat torii are absolutely maximal (l.3568–3570)

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; `Minkowski d` has `d` spatial
dimensions: Barbot's `n` is `d + 1`, his `ℍⁿ⁻¹` the unit future hyperboloid of `Minkowski d`.

## How `bcor:level_sets_complete` is proved (not Barbot's route)

Barbot follows an incomplete geodesic and the convergence of its Gauss image. Here the estimate
is global and needs neither geodesics nor smoothness of `S_t`. For `p, p' ∈ S_t`,
`−|p' − p|² ≤ 2t ⟨n(p) | p' − p⟩ ≤ 0` (`rC_neg_minkQ_le`: the osculating hyperboloid
`r(p) + tℍ` lies in `{T ≥ t}`; `rC_minkB_gaussMap_le`: the tangent plane supports `{T ≥ t}`), so a
Lipschitz curve `c` of `S_t` has `c' ⊥ n(c)` a.e. (`rC_minkB_deriv_eq_zero`). With
`Y = |c − c(0)|² + 2t²`, Cauchy–Schwarz on `n^⊥` (`rC_minkB_sq_le`) gives `|Y'| ≤ √|c'|² Y/t`, so
`Y ≤ 2t² e^{ℓ/t}`, `ℓ` the length (`rC_gronwall`, FTC for absolutely continuous `log Y`). The
chordal `bprop:lip` (`minkQ_gaussMap_sub_le`) then bounds `−⟨n(c) | n(c 0)⟩ ≤ e^{ℓ/t}`, hence
the time component of `n(c)` (`rC_fst_le_of_unit`), hence the slope, hence `‖c'⃗‖ ≤ A √|c'|²`
(`rC_norm_snd_sq_le`): length-bounded sets are Euclidean-bounded (`rC_norm_sub_le`), and a
Cauchy sequence has a convergent subsequence in the closed `S_t`, convergent for the length
(`IsSpacelikeLipschitzIn.isHomeomorph_toSubtype`).

## The quotient

Future side: `S₁ ⊆ Ω⁺(Λ)` is invariant under every `γ` preserving `Ω` (`smul_mem_cosmoLevel_iff`),
`Γ` is acausal since `T` is `Γ`-invariant and strictly increasing along `≤`; the frame `φ` is
absorbed by `rC_of_frame` (`φ S₁` in `φΩ`, the isometry `φ` of the induced lengths,
`rC_transfer`). Past side: `σ(p) = −p` carries `Ω⁺(−Λ)` (`negS`, `cosmoRegular_negS`) onto
`Ω⁻(Λ)`; it is an isomorphism `(𝐌ⁿ)^dual → 𝐌ⁿ` (`rC_negTransport_eq`, `rC_neg_isEMorphism`), so
it carries Cauchy surfaces (`rC_isCauchySurfaceOn_neg`, with `dual_isCauchySurfaceOn`) and spacelike
Lipschitz hypersurfaces (`rC_isSpacelikeLipschitzIn_neg`, frames `σgσ = negConj g`), preserves the
induced lengths (`minkQ_neg`), and `γ ↦ σγσ` preserves `Ω⁺(−Λ)`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `Ω` future complete regular convex (Def 4.5) | ✓ carried, as `CosmoRegular Λ` (two null directions: the paper's "at least two elements" is too weak, Cosmological's `not_cosmoBoundedAsPrinted`) — ⚠ strengthened in the paper's letter, the strongest true form |
| past regular domains (Barbot: "up to time reversal", l.618) | ✓ carried: `PastRegular Λ` with two null directions |
| `S_t` "riemannian" (l.1113), geodesics | ⚠ weakened: not used; the length is that of Lipschitz curves (`InducedLength`) |
| `Γ` discrete, torsion-free | ⚠ weakened: only `IsQuotientOf` (a covering presentation) is used |

## SCOPE (disclosed)

* "Complete" is `CompleteSpace` of the induced length of DEC-35 (Lipschitz curves, `√|γ'|²`);
  Barbot's Riemannian metric on the `C^{1,1}` hypersurface `S_t` is not built, and the
  equivalence of the two (DEC-31 at the metric level) is not proved (InducedLength's SCOPE).
* The Gauss map is not shown Lipschitz for the induced length and the hyperbolic metric (Barbot's
  `bprop:lip` as printed); only its chordal form is used, which suffices.
* `Λ = misnerΛ`, the family (b) and the frame bookkeeping of Classification are its own.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
Cla prover dispatch (RegularComplete).
-/

namespace Causal.Flat.Cla

open Set TopologicalSpace Topology Filter Function MeasureTheory
open scoped ENNReal NNReal unitInterval Pointwise

universe u

variable {d : ℕ}

/-! ### Pulled lengths under an affine map preserving `minkQ` -/

section Pulled

/-- The derivative of `A ∘ γ + b` is `A` of that of `γ`, everywhere. -/
private theorem rC_deriv_affine (A : Minkowski d ≃L[ℝ] Minkowski d) (b : Minkowski d)
    (γ : ℝ → Minkowski d) (t : ℝ) :
    deriv (fun s => A (γ s) + b) t = A (deriv γ t) := by
  rw [deriv_add_const]
  by_cases hγ : DifferentiableAt ℝ γ t
  · exact ((A : Minkowski d →L[ℝ] Minkowski d).hasFDerivAt.comp_hasDerivAt t hγ.hasDerivAt).deriv
  · have h' : ¬ DifferentiableAt ℝ (fun s => A (γ s)) t := fun h =>
      hγ ((A.comp_differentiableAt_iff (f := γ)).1 h)
    rw [deriv_zero_of_not_differentiableAt h', deriv_zero_of_not_differentiableAt hγ, map_zero]

private theorem rC_lipschitz_affine (A : Minkowski d ≃L[ℝ] Minkowski d) (b : Minkowski d)
    {f : ℝ → Minkowski d} {K : ℝ≥0} (hf : LipschitzWith K f) :
    LipschitzWith (‖(A : Minkowski d →L[ℝ] Minkowski d)‖₊ * K) fun t => A (f t) + b := by
  refine LipschitzWith.of_dist_le_mul fun s t => ?_
  rw [dist_add_right, dist_eq_norm, ← map_sub]
  calc ‖(A : Minkowski d →L[ℝ] Minkowski d) (f s - f t)‖
      ≤ ‖(A : Minkowski d →L[ℝ] Minkowski d)‖ * ‖f s - f t‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖(A : Minkowski d →L[ℝ] Minkowski d)‖ * (K * dist s t) := by
        rw [← dist_eq_norm]; gcongr; exact hf.dist_le_mul s t
    _ = _ := by push_cast; ring

/-- **Transfer of pulled lengths along an affine map preserving `minkQ`**: if `G ∘ e = A ∘ F + b`
with `A` linear preserving `minkQ`, a path and its image have the same pulled length. -/
theorem rC_pathLength_affine {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (F : X → Minkowski d) (G : Y → Minkowski d) {e : X → Y} (he : Continuous e)
    (A : Minkowski d ≃L[ℝ] Minkowski d) (hA : ∀ v, minkQ (A v) = minkQ v) (b : Minkowski d)
    (hFG : ∀ x, G (e x) = A (F x) + b) {x y : X} (γ : Path x y) :
    pathLength (fun _ z => G z) (γ.map he) = pathLength (fun _ z => F z) γ := by
  have hext : (fun t => G ((γ.map he).extend t)) = fun t => A (F (γ.extend t)) + b :=
    funext fun t => hFG (γ.extend t)
  have hiff : IsLocLip (fun _ z => G z) (γ.map he).extend ↔ IsLocLip (fun _ z => F z) γ.extend := by
    rw [isLocLip_pulled_iff, isLocLip_pulled_iff, hext]
    constructor
    · rintro ⟨K, hK⟩
      refine ⟨‖(A.symm : Minkowski d →L[ℝ] Minkowski d)‖₊ * K, ?_⟩
      convert rC_lipschitz_affine A.symm (-A.symm b) hK using 1
      funext t
      simp
    · rintro ⟨K, hK⟩
      exact ⟨_, rC_lipschitz_affine A b hK⟩
  by_cases hL : IsLocLip (fun _ z => F z) γ.extend
  · rw [pathLength_of_isLocLip _ hL, pathLength_of_isLocLip _ (hiff.2 hL), localLength_pulled,
      localLength_pulled, hext]
    unfold lorentzLength
    congr 1
    funext t
    rw [rC_deriv_affine, hA]
  · rw [pathLength_of_not_isLocLip _ hL, pathLength_of_not_isLocLip _ (mt hiff.1 hL)]

/-- **The pulled length spaces of `F` and of `G` are isometric** through a homeomorphism `e` with
`G ∘ e = A ∘ F + b`. -/
theorem rC_edist_affine {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (F : X → Minkowski d) (G : Y → Minkowski d) (e : X ≃ₜ Y)
    (A : Minkowski d ≃L[ℝ] Minkowski d) (hA : ∀ v, minkQ (A v) = minkQ v) (b : Minkowski d)
    (hFG : ∀ x, G (e x) = A (F x) + b) (x y : X) :
    edist (LocalLengthSpace.toSpace.symm (e x) : LocalLengthSpace fun (_ : Y) z => G z)
        (LocalLengthSpace.toSpace.symm (e y)) =
      edist (LocalLengthSpace.toSpace.symm x : LocalLengthSpace fun (_ : X) z => F z)
        (LocalLengthSpace.toSpace.symm y) := by
  rw [LocalLengthSpace.edist_def, LocalLengthSpace.edist_def]
  change (⨅ γ : Path (e x) (e y), pathLength (fun _ z => G z) γ) =
    ⨅ γ : Path x y, pathLength (fun _ z => F z) γ
  apply le_antisymm
  · exact le_iInf fun γ => (iInf_le _ (γ.map e.continuous)).trans_eq
      (rC_pathLength_affine F G e.continuous A hA b hFG γ)
  · refine le_iInf fun γ' => ?_
    set γ := (γ'.map e.symm.continuous).cast (e.symm_apply_apply x).symm (e.symm_apply_apply y).symm
    refine (iInf_le _ γ).trans_eq ?_
    rw [← rC_pathLength_affine F G e.continuous A hA b hFG γ]
    exact pathLength_congr_extend _ _ _ (funext fun t => by
      simp [γ, Path.extend, IccExtend])

end Pulled

/-! ### The chart system of a subset of an open set of `𝐌ⁿ`, and `InducedLength` -/

section OpensLink

/-- The chart of an open subset of `𝐌ⁿ` is the inclusion. -/
private theorem rC_chartAt_opens (Ω : Opens (Minkowski d)) (x y : Ω) :
    chartAt (Minkowski d) x y = (y : Minkowski d) := by
  rw [TopologicalSpace.Opens.chartAt_eq]; simp [OpenPartialHomeomorph.subtypeRestr]

/-- For `Ŝ ⊆ Ω`, the chart system is the inclusion into `𝐌ⁿ`. -/
theorem rC_chartSys_opens (Ω : Opens (Minkowski d)) (T : Set Ω) :
    chartSys d T = fun (_ : T) (z : T) => ((z : Ω) : Minkowski d) := by
  funext x z; exact rC_chartAt_opens Ω _ _

/-- `InducedLength`'s `lengthOn` is the pulled length of the inclusion. -/
theorem rC_lengthOn_eq_pathLength (S : Set (Minkowski d)) (V : Opens (Minkowski d))
    {x y : ↥(S ∩ (V : Set (Minkowski d)))} (γ : Path x y) :
    lengthOn S V γ.toContinuousMap =
      pathLength (fun _ (z : ↥(S ∩ (V : Set (Minkowski d)))) => (z : Minkowski d)) γ := by
  have hext : curveExtend γ.toContinuousMap = fun t => (γ.extend t : Minkowski d) := rfl
  have hiff : IsLipschitzCurve γ.toContinuousMap ↔
      IsLocLip (fun _ (z : ↥(S ∩ (V : Set (Minkowski d)))) => (z : Minkowski d)) γ.extend := by
    rw [isLocLip_pulled_iff]; unfold IsLipschitzCurve; rw [hext]
  by_cases h : IsLipschitzCurve γ.toContinuousMap
  · rw [lengthOn_of_isLipschitzCurve h, pathLength_of_isLocLip _ (hiff.1 h), localLength_pulled,
      hext]
  · rw [lengthOn_of_not_isLipschitzCurve h, pathLength_of_not_isLocLip _ (mt hiff.2 h)]

/-- The homeomorphism `Ω ⊇ Ŝ ≃ S ∩ Ω`. -/
def rC_opensHomeo (Ω : Opens (Minkowski d)) (S : Set (Minkowski d)) :
    (Subtype.val ⁻¹' S : Set Ω) ≃ₜ ↥(S ∩ (Ω : Set (Minkowski d))) where
  toFun z := ⟨((z : Ω) : Minkowski d), z.2, (z : Ω).2⟩
  invFun w := ⟨⟨w, w.2.2⟩, w.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((continuous_subtype_val).subtype_mk _).subtype_mk _

/-- **The glued length of `Ŝ ⊆ Ω` is `InducedLength S Ω`.** -/
theorem rC_edist_opens (Ω : Opens (Minkowski d)) (S : Set (Minkowski d))
    (x y : InducedLengthSpace d (Subtype.val ⁻¹' S : Set Ω)) :
    edist (InducedLength.toSubtype.symm (rC_opensHomeo Ω S (InducedLengthSpace.toSubtype x)) :
        InducedLength S Ω) (InducedLength.toSubtype.symm
          (rC_opensHomeo Ω S (InducedLengthSpace.toSubtype y))) = edist x y := by
  have h := rC_edist_affine (fun z : (Subtype.val ⁻¹' S : Set Ω) => ((z : Ω) : Minkowski d))
    (fun z : ↥(S ∩ (Ω : Set (Minkowski d))) => (z : Minkowski d)) (rC_opensHomeo Ω S)
    (ContinuousLinearEquiv.refl ℝ _) (fun _ => rfl) 0 (fun _ => by simp [rC_opensHomeo])
    (InducedLengthSpace.toSubtype x) (InducedLengthSpace.toSubtype y)
  refine Eq.trans ?_ (h.trans ?_)
  · rw [InducedLength.edist_def, LocalLengthSpace.edist_def]
    exact iInf_congr fun γ => rC_lengthOn_eq_pathLength S Ω γ
  · change _ = ⨅ γ : Path _ _, pathLength (chartSys d (Subtype.val ⁻¹' S : Set Ω)) γ
    rw [rC_chartSys_opens]
    rfl

/-- The isometry `InducedLengthSpace d Ŝ ≃ InducedLength S Ω`. -/
noncomputable def rC_opensIsometry (Ω : Opens (Minkowski d)) (S : Set (Minkowski d)) :
    InducedLengthSpace d (Subtype.val ⁻¹' S : Set Ω) ≃ᵢ InducedLength S Ω where
  toEquiv := InducedLengthSpace.toSubtype.trans ((rC_opensHomeo Ω S).toEquiv.trans
    InducedLength.toSubtype.symm)
  isometry_toFun x y := rC_edist_opens Ω S x y

/-- **Completeness and the topology field transfer from `InducedLength S Ω`.** -/
theorem rC_complete_opens_of_inducedLength {Ω : Opens (Minkowski d)} {S : Set (Minkowski d)}
    (hL : IsSpacelikeLipschitzIn Ω S) (hc : CompleteSpace (InducedLength S Ω)) :
    CompleteSpace (InducedLengthSpace d (Subtype.val ⁻¹' S : Set Ω)) ∧
      Continuous fun x : InducedLengthSpace d (Subtype.val ⁻¹' S : Set Ω) =>
        (InducedLengthSpace.toSubtype x).1 := by
  refine ⟨(rC_opensIsometry Ω S).completeSpace_iff.2 hc, ?_⟩
  have h1 : Continuous fun x : InducedLengthSpace d (Subtype.val ⁻¹' S : Set Ω) =>
      InducedLength.toSubtype (rC_opensIsometry Ω S x) :=
    hL.continuous_toSubtype.comp (rC_opensIsometry Ω S).continuous
  have h2 := (rC_opensHomeo Ω S).symm.continuous.comp h1
  refine (continuous_subtype_val.comp h2).congr fun x => ?_
  rfl

end OpensLink

/-! ### (A) Descent: an invariant complete Cauchy surface of `Ω` gives a Cauchy-complete `Γ\Ω` -/

section Descent

private theorem rC_exists_injOn {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {π : X → Y} (h : IsCoveringMap π) (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ InjOn π U := by
  obtain ⟨e, hx, he⟩ := h.isLocalHomeomorph x
  exact ⟨e.source, e.open_source, hx, fun a ha b hb hab => by
    rw [he] at hab; exact e.injOn ha hb hab⟩

/-- **A covering presentation acts freely**: if `γ p = p`, `γ` fixes a neighbourhood of `p` (the
covering `π` is injective near `p` and `π (γ q) = π q`), hence `γ = 1` (rigidity,
`Causal.eq_of_eqOn`). Only the covering property and the fibres are used, not the local isometry. -/
private theorem rC_isCancelSMul {X : Type*} [TopologicalSpace X] {Γ : Subgroup (isom d)}
    {Ω : Opens (Minkowski d)} [FlatQuotient.Invariant Γ Ω] {π : Ω → X} (hcov : IsCoveringMap π)
    (hfib : ∀ p q : Ω, π p = π q ↔ ∃ γ ∈ Γ, γ • (p : Minkowski d) = q) : IsCancelSMul Γ Ω := by
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro γ p hp
  obtain ⟨U, hUo, hpU, hinj⟩ := rC_exists_injOn hcov p
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
private theorem rC_properlyDiscontinuousSMul {X : Type*} [TopologicalSpace X] [T2Space X]
    {Γ : Subgroup (isom d)} {Ω : Opens (Minkowski d)} [FlatQuotient.Invariant Γ Ω] {π : Ω → X}
    (hcov : IsCoveringMap π)
    (hfib : ∀ p q : Ω, π p = π q ↔ ∃ γ ∈ Γ, γ • (p : Minkowski d) = q) :
    ProperlyDiscontinuousSMul Γ Ω := by
  haveI := rC_isCancelSMul hcov hfib
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
  obtain ⟨U, hUo, hbU, hinj⟩ := rC_exists_injOn hcov b
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


section OfComp
variable {X M N : Type*} [TopologicalSpace X] [ChartedSpace (Minkowski d) X]
  [TopologicalSpace M] [ChartedSpace (Minkowski d) M] [TopologicalSpace N]
  [ChartedSpace (Minkowski d) N]

/-- **Descending a local isometry along a surjective local isometry** (Classification's
`IsLocalIsometry.of_comp_right`, redone here). -/
private theorem rC_isLocalIsometry_of_comp_right {q : X → M} {f : M → N} (hq : IsLocalIsometry d q)
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

end OfComp

/-- **(A) Descent of Cauchy-completeness** (the lifting argument of Classification's
`isCauchyComplete_of_isQuotientOf_frameHoriz`, for an arbitrary invariant surface). If
`M₁ = Γ\Ω`, `Γ` acts acausally, and `S ⊆ Ω` is a `Γ`-invariant Cauchy surface of `Ω`, spacelike
Lipschitz in `Ω`, complete for its induced length, with the length topology finer than the
subspace one, then `M₁` is Cauchy-complete, through `π(S)`: `π|_S` does not increase lengths
(`pathLength_pulled_eq_of_local`) and lifts paths of `π(S)` with their lengths
(`IsCoveringMap.restrictPreimage`), so a Cauchy sequence of `π(S)` lifts along a fast
subsequence. -/
theorem isCauchyComplete_of_isQuotientOf_of_invariant {M₁ : FlatSpacetime.{u} d}
    {Γ : Subgroup (isom d)} {Ω : Opens (Minkowski d)} (hq : IsQuotientOf M₁ Γ Ω)
    [FlatQuotient.Invariant Γ Ω] (hac : FlatQuotient.ActsAcausally Γ Ω)
    {S : Set (Minkowski d)} (hSΩ : S ⊆ Ω) (hinv : ∀ γ ∈ Γ, ∀ p ∈ S, γ • p ∈ S)
    (hC : (minkowski d).IsCauchySurfaceOn Ω S) (hL : IsSpacelikeLipschitzIn Ω S)
    (hcomp : CompleteSpace (InducedLengthSpace d (Subtype.val ⁻¹' S : Set Ω)))
    (htop : Continuous fun x : InducedLengthSpace d (Subtype.val ⁻¹' S : Set Ω) =>
      (InducedLengthSpace.toSubtype x).1) :
    IsCauchyComplete d M₁ := by
  obtain ⟨π₀, hcov₀, -, -, hfib₀⟩ := hq.quot
  haveI : IsCancelSMul Γ Ω := rC_isCancelSMul hcov₀ hfib₀
  haveI : ProperlyDiscontinuousSMul Γ Ω := rC_properlyDiscontinuousSMul hcov₀ hfib₀
  obtain ⟨π, hcov, hloc, Φ, hΦ⟩ := hq.exists_homeomorph
  have hfib : ∀ p q : Ω, π p = π q ↔ ∃ γ ∈ Γ, γ • (p : Minkowski d) = q := fun p q => by
    rw [← hΦ, ← hΦ, Φ.injective.eq_iff, FlatQuotient.proj_eq_proj_iff']
  set Ŝ : Set Ω := Subtype.val ⁻¹' S with hŜ
  set T : Set M₁ := π '' Ŝ with hT
  have hpre : ∀ z : Ω, π z ∈ T → z ∈ Ŝ := by
    rintro z ⟨y, hy, hyz⟩
    obtain ⟨γ, hγ, hγy⟩ := (hfib y z).1 hyz
    change (z : Minkowski d) ∈ S
    rw [← hγy]
    exact hinv γ hγ _ hy
  set q : Ŝ → T := fun z => ⟨π z, z, z.2, rfl⟩ with hqdef
  have hqc : Continuous q := (hcov.continuous.comp continuous_subtype_val).subtype_mk _
  have hlocq : ∀ x : Ŝ, ∃ g : isom d, ∀ᶠ (x' : Ŝ) in 𝓝 x,
      (x'.1 : Minkowski d) = g • chartSys d T (q x) (q x') := by
    intro x
    obtain ⟨-, h⟩ := isLocalIsometry_iff_eventually.1 hloc
    obtain ⟨g, hg⟩ := h (x : Ω)
    refine ⟨g⁻¹, ?_⟩
    filter_upwards [((continuous_subtype_val : Continuous (Subtype.val : Ŝ → Ω)).continuousAt
      (x := x)).eventually hg] with x' hx'
    change _ = g⁻¹ • chartAt (Minkowski d) (π x) (π x')
    rw [hx', rC_chartAt_opens, inv_smul_smul]
  have hlen : ∀ {a b : Ŝ} (c : Path a b),
      pathLength (chartSys d Ŝ) c = pathLength (chartSys d T) (c.map hqc) := fun c => by
    rw [rC_chartSys_opens]
    exact pathLength_pulled_eq_of_local _ (chartSys d T) hqc hlocq c
  set Q : InducedLengthSpace d Ŝ → InducedLengthSpace d T :=
    fun x => InducedLengthSpace.toSubtype.symm (q (InducedLengthSpace.toSubtype x)) with hQdef
  have hQle : ∀ a b : Ŝ, edist (Q (InducedLengthSpace.toSubtype.symm a))
      (Q (InducedLengthSpace.toSubtype.symm b)) ≤
        edist (InducedLengthSpace.toSubtype.symm a : InducedLengthSpace d Ŝ)
          (InducedLengthSpace.toSubtype.symm b) := fun a b => by
    change (⨅ γ : Path (q a) (q b), pathLength (chartSys d T) γ) ≤
      ⨅ γ : Path a b, pathLength (chartSys d Ŝ) γ
    exact le_iInf fun c => (iInf_le _ (c.map hqc)).trans_eq (hlen c).symm
  have hQ : LipschitzWith 1 Q := LipschitzWith.of_edist_le fun a b =>
    hQle (InducedLengthSpace.toSubtype a) (InducedLengthSpace.toSubtype b)
  have hsurj : ∀ s : InducedLengthSpace d T, ∃ x, Q x = s := by
    rintro ⟨_, z, hz, rfl⟩; exact ⟨⟨z, hz⟩, rfl⟩
  have hlift : ∀ {a : Ŝ} {s : T} (γ : Path (q a) s), ∃ (b : Ŝ) (c : Path a b), q b = s ∧
      ∀ t, q (c t) = γ t := by
    intro a s γ
    have cov := hcov.restrictPreimage T
    set r : (π ⁻¹' T) → Ŝ := fun z => ⟨z.1, hpre z.1 z.2⟩ with hr_def
    have hr : Continuous r := (continuous_subtype_val).subtype_mk _
    obtain ⟨Γ', hΓ', hΓ0⟩ := cov.exists_path_lifts γ.toContinuousMap
      ⟨(a : Ω), ⟨a, a.2, rfl⟩⟩ (by simp only [Path.coe_toContinuousMap, Path.source]; rfl)
    have hΓt : ∀ t, q (r (Γ' t)) = γ t := fun t => by
      apply Subtype.ext
      exact congrArg Subtype.val (congrFun hΓ' t)
    refine ⟨r (Γ' 1), Path.mk ⟨fun t => r (Γ' t), hr.comp Γ'.continuous⟩ ?_ rfl,
      by rw [hΓt, γ.target], hΓt⟩
    change r (Γ' 0) = a
    rw [hΓ0]
  have hlift_le : ∀ {a : Ŝ} {s : T} (γ : Path (q a) s), ∃ b, q b = s ∧
      edist (InducedLengthSpace.toSubtype.symm a : InducedLengthSpace d Ŝ)
        (InducedLengthSpace.toSubtype.symm b) ≤ pathLength (chartSys d T) γ := by
    intro a s γ
    obtain ⟨b, c, hb, hc⟩ := hlift γ
    refine ⟨b, hb, ?_⟩
    rw [pathLength_congr_extend (chartSys d T) γ (c.map hqc) (funext fun t => ?_), ← hlen]
    · exact iInf_le _ c
    · simp only [Path.extend, IccExtend, Path.map_coe]
      exact (hc _).symm
  have hlift_lt : ∀ {a : Ŝ} {s : InducedLengthSpace d T} {ε : ENNReal},
      edist (Q (InducedLengthSpace.toSubtype.symm a)) s < ε →
      ∃ b, Q (InducedLengthSpace.toSubtype.symm b) = s ∧
        edist (InducedLengthSpace.toSubtype.symm a : InducedLengthSpace d Ŝ)
          (InducedLengthSpace.toSubtype.symm b) < ε := by
    intro a s ε h
    obtain ⟨γ, hγ⟩ := iInf_lt_iff.1 h
    obtain ⟨b, hb, hle⟩ := hlift_le (s := InducedLengthSpace.toSubtype s) γ
    exact ⟨b, hb, hle.trans_lt hγ⟩
  refine ⟨T, ?_, ?_, ?_, ?_⟩
  · -- `T` is a Cauchy surface
    have h2 := FlatQuotient.isCauchySurface_image_of_isCauchySurfaceOn Γ Ω hac hSΩ hinv hC
    have hΦl : IsLocalIsometry d Φ :=
      rC_isLocalIsometry_of_comp_right (FlatQuotient.isLocalIsometry_proj _ _)
        (FlatQuotient.proj_surjective _ _) (by rw [show Φ ∘ _ = π from funext hΦ]; exact hloc)
    have h3 := ((IsIsometricEmbedding.isEMorphism (d := d)
      ⟨hΦl, Φ.injective⟩).isCauchySurfaceOn_image_iff
      Φ.injective.injOn le_rfl (V := ⊤) (U := ⊤) (by simp [Φ.surjective.range_eq])
      (subset_univ _)).1 ((flatCausality _ _).isCauchySurfaceOn_top.2 h2)
    rw [(flatCausality _ _).isCauchySurfaceOn_top] at h3
    have hTe : Φ '' (FlatQuotient.proj Γ Ω '' Ŝ) = T := by
      rw [image_image]; exact image_congr fun x _ => hΦ x
    rwa [hTe] at h3
  · -- `T` is spacelike Lipschitz in the charts of `M₁`
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨-, h⟩ := isLocalIsometry_iff_eventually.1 hloc
    obtain ⟨g, hg⟩ := h p
    set e := chartAt (Minkowski d) (π p)
    have hsrc : ∀ᶠ y in 𝓝 p, π y ∈ e.source :=
      hloc.continuous.continuousAt.preimage_mem_nhds
        (e.open_source.mem_nhds (mem_chart_source _ _))
    obtain ⟨W, hWsub, hWo, hpW⟩ := mem_nhds_iff.1 (hg.and hsrc)
    have hWmo : IsOpen (Subtype.val '' W : Set (Minkowski d)) :=
      Ω.isOpen.isOpenMap_subtype_val W hWo
    set V : Opens (Minkowski d) := isomImage g ⟨Subtype.val '' W, hWmo⟩ with hVdef
    have hV : ∀ z, z ∈ (V : Set (Minkowski d)) ↔ ∃ y ∈ W, g • (y : Minkowski d) = z := by
      intro z
      rw [hVdef, coe_isomImage]
      constructor
      · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩; exact ⟨y, hy, rfl⟩
      · rintro ⟨y, hy, rfl⟩; exact ⟨y, ⟨y, hy, rfl⟩, rfl⟩
    have hW : ∀ y ∈ W, e (π y) = g • (y : Minkowski d) ∧ π y ∈ e.source := fun y hy => by
      obtain ⟨h1, h2⟩ := hWsub hy
      rw [rC_chartAt_opens] at h1
      exact ⟨h1, h2⟩
    refine ⟨V, (hV _).2 ⟨p, hpW, (hW p hpW).1.symm⟩, fun z hz => ?_, ?_⟩
    · obtain ⟨y, hy, rfl⟩ := (hV z).1 hz
      rw [← (hW y hy).1]
      exact e.map_source (hW y hy).2
    have hset : e '' (T ∩ e.source) ∩ V = g • S ∩ (V : Set (Minkowski d)) := by
      ext z
      constructor
      · rintro ⟨⟨m, ⟨hmT, hmsrc⟩, rfl⟩, hzV⟩
        refine ⟨?_, hzV⟩
        obtain ⟨y, hy, hyz⟩ := (hV _).1 hzV
        have hm : π y = m := e.injOn (hW y hy).2 hmsrc ((hW y hy).1.trans hyz)
        have hyS : y ∈ Ŝ := hpre y (hm ▸ hmT)
        exact ⟨(y : Minkowski d), hyS, hyz⟩
      · rintro ⟨⟨s, hs, rfl⟩, hzV⟩
        obtain ⟨y, hy, hyz⟩ := (hV _).1 hzV
        have hys : (y : Minkowski d) = s := (smul_left_cancel_iff g).1 hyz
        have hyS : y ∈ Ŝ := by change (y : Minkowski d) ∈ S; rw [hys]; exact hs
        refine ⟨⟨π y, ⟨⟨y, hyS, rfl⟩, (hW y hy).2⟩, ?_⟩, hzV⟩
        rw [(hW y hy).1, hyz]
    change IsSpacelikeLipschitzIn V (e '' (T ∩ e.source) ∩ V)
    rw [hset]
    refine (hL.smul isom_strongMorphism g).restrict fun z hz => ?_
    obtain ⟨y, hy, rfl⟩ := (hV z).1 hz
    rw [← SetLike.mem_coe, coe_smulOpens]
    exact ⟨y, y.2, rfl⟩
  · -- completeness
    refine EMetric.complete_of_convergent_controlled_sequences (fun n => 1 / 2 ^ n)
      (fun n => ENNReal.div_pos_iff.2 ⟨one_ne_zero, ENNReal.pow_ne_top ENNReal.ofNat_ne_top⟩)
      fun u hu => ?_
    obtain ⟨a0, ha0⟩ := hsurj (u 0)
    have step : ∀ n (x : {x : InducedLengthSpace d Ŝ // Q x = u n}),
        ∃ y : {y : InducedLengthSpace d Ŝ // Q y = u (n + 1)},
          edist (x : InducedLengthSpace d Ŝ) y < 1 / 2 ^ n := by
      rintro n ⟨x, hx⟩
      have h := hu n n (n + 1) le_rfl (by omega)
      rw [← hx] at h
      obtain ⟨b, hb, hlt⟩ := hlift_lt (a := InducedLengthSpace.toSubtype x) h
      exact ⟨⟨_, hb⟩, hlt⟩
    choose g hg using step
    let a : (n : ℕ) → {x : InducedLengthSpace d Ŝ // Q x = u n} := fun n =>
      Nat.rec (motive := fun n => {x : InducedLengthSpace d Ŝ // Q x = u n}) ⟨a0, ha0⟩
        (fun n x => g n x) n
    have ha : ∀ n, edist (a n : InducedLengthSpace d Ŝ) (a (n + 1)) ≤ 1 / 2 ^ n :=
      fun n => (hg n (a n)).le
    have hc : CauchySeq fun n => (a n : InducedLengthSpace d Ŝ) :=
      cauchySeq_of_edist_le_geometric_two 1 ENNReal.one_ne_top ha
    obtain ⟨b, hb⟩ := cauchySeq_tendsto_of_complete hc
    exact ⟨Q b, ((hQ.continuous.tendsto b).comp hb).congr fun n => (a n).2⟩
  · -- the length topology is finer than the subspace topology
    rw [continuous_iff_continuousAt]
    intro s
    obtain ⟨x, rfl⟩ := hsurj s
    refine tendsto_nhds.2 fun N hN hxN => ?_
    have hpre' : (fun x : InducedLengthSpace d Ŝ => π (InducedLengthSpace.toSubtype x).1) ⁻¹' N
        ∈ 𝓝 x :=
      (hcov.continuous.comp htop).continuousAt.preimage_mem_nhds (hN.mem_nhds hxN)
    obtain ⟨ε, hε, hball⟩ := EMetric.mem_nhds_iff.1 hpre'
    filter_upwards [Metric.eball_mem_nhds (Q x) hε] with y hy
    rw [Metric.mem_eball, edist_comm] at hy
    obtain ⟨b, rfl, hb⟩ := hlift_lt (a := InducedLengthSpace.toSubtype x) hy
    exact hball (by rw [Metric.mem_eball, edist_comm]; exact hb)

end Descent

/-! ### Changing the frame and the transfer of the completeness fields -/

section Frame

/-- **Transfer of the completeness fields** along an affine map `p ↦ A p + b`, `A` preserving
`minkQ`, carrying `Ŝ ⊆ Ω` onto `Ŝ' ⊆ Ω'`. -/
theorem rC_transfer {Ω Ω' : Opens (Minkowski d)} {S S' : Set (Minkowski d)}
    (A : Minkowski d ≃L[ℝ] Minkowski d) (hA : ∀ v, minkQ (A v) = minkQ v) (b : Minkowski d)
    (hmem : ∀ p, (p ∈ Ω ∧ p ∈ S) ↔ (A p + b ∈ Ω' ∧ A p + b ∈ S'))
    (hcomp : CompleteSpace (InducedLengthSpace d (Subtype.val ⁻¹' S : Set Ω)))
    (htop : Continuous fun x : InducedLengthSpace d (Subtype.val ⁻¹' S : Set Ω) =>
      (InducedLengthSpace.toSubtype x).1) :
    CompleteSpace (InducedLengthSpace d (Subtype.val ⁻¹' S' : Set Ω')) ∧
      Continuous fun x : InducedLengthSpace d (Subtype.val ⁻¹' S' : Set Ω') =>
        (InducedLengthSpace.toSubtype x).1 := by
  have hinv : ∀ w, A (A.symm (w - b)) + b = w := fun w => by simp
  have hmem' : ∀ w : (Subtype.val ⁻¹' S' : Set Ω'),
      (A.symm (w.1.1 - b) ∈ Ω ∧ A.symm (w.1.1 - b) ∈ S) :=
    fun w => (hmem _).2 (by rw [hinv]; exact ⟨w.1.2, w.2⟩)
  let e : (Subtype.val ⁻¹' S : Set Ω) ≃ₜ (Subtype.val ⁻¹' S' : Set Ω') :=
    { toFun := fun z => ⟨⟨A z.1.1 + b, ((hmem _).1 ⟨z.1.2, z.2⟩).1⟩, ((hmem _).1 ⟨z.1.2, z.2⟩).2⟩
      invFun := fun w => ⟨⟨A.symm (w.1.1 - b), (hmem' w).1⟩, (hmem' w).2⟩
      left_inv := fun z => by apply Subtype.ext; apply Subtype.ext; simp
      right_inv := fun w => by apply Subtype.ext; apply Subtype.ext; simp
      continuous_toFun := by
        refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
        exact (A.continuous.comp (continuous_subtype_val.comp continuous_subtype_val)).add
          continuous_const
      continuous_invFun := by
        refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
        exact A.symm.continuous.comp
          ((continuous_subtype_val.comp continuous_subtype_val).sub continuous_const) }
  have hiso : ∀ x y : (Subtype.val ⁻¹' S : Set Ω),
      edist (InducedLengthSpace.toSubtype.symm (e x) :
          InducedLengthSpace d (Subtype.val ⁻¹' S' : Set Ω'))
        (InducedLengthSpace.toSubtype.symm (e y)) =
      edist (InducedLengthSpace.toSubtype.symm x : InducedLengthSpace d (Subtype.val ⁻¹' S : Set Ω))
        (InducedLengthSpace.toSubtype.symm y) := by
    intro x y
    have h := rC_edist_affine (fun z : (Subtype.val ⁻¹' S : Set Ω) => ((z : Ω) : Minkowski d))
      (fun z : (Subtype.val ⁻¹' S' : Set Ω') => ((z : Ω') : Minkowski d)) e A hA b
      (fun _ => rfl) x y
    change (⨅ γ : Path (e x) (e y), pathLength
        (chartSys d (Subtype.val ⁻¹' S' : Set Ω')) γ) =
      ⨅ γ : Path x y, pathLength (chartSys d (Subtype.val ⁻¹' S : Set Ω)) γ
    rw [rC_chartSys_opens, rC_chartSys_opens]
    exact h
  let Iso : InducedLengthSpace d (Subtype.val ⁻¹' S : Set Ω) ≃ᵢ
      InducedLengthSpace d (Subtype.val ⁻¹' S' : Set Ω') :=
    { toEquiv := InducedLengthSpace.toSubtype.trans (e.toEquiv.trans
        InducedLengthSpace.toSubtype.symm)
      isometry_toFun := fun x y => hiso _ _ }
  refine ⟨Iso.completeSpace_iff.1 hcomp, ?_⟩
  have h1 : Continuous fun x : InducedLengthSpace d (Subtype.val ⁻¹' S : Set Ω) =>
      (InducedLengthSpace.toSubtype x : (Subtype.val ⁻¹' S : Set Ω)) :=
    htop.subtype_mk fun x => (InducedLengthSpace.toSubtype x).2
  refine (continuous_subtype_val.comp (e.continuous.comp (h1.comp Iso.symm.continuous))).congr
    fun x => ?_
  change ((e (e.symm (InducedLengthSpace.toSubtype x)) : (Subtype.val ⁻¹' S' : Set Ω')) : Ω') = _
  rw [e.apply_symm_apply]

/-- A free action with no point causally related to its image is acausal. -/
private theorem rC_actsAcausally {Γ : Subgroup (isom d)} {Ω : Opens (Minkowski d)}
    [FlatQuotient.Invariant Γ Ω] [IsCancelSMul Γ Ω]
    (h : ∀ γ ∈ Γ, ∀ x ∈ Ω, (minkowski d).le ⊤ x (γ • x) → γ • x = x) :
    FlatQuotient.ActsAcausally Γ Ω := by
  intro γ hne x hle
  have hle' := (minkowski d).le_mono le_top ((flat_le_top_subtype_iff _ _ _).1 hle)
  have hx : (γ : isom d) • (x : Minkowski d) = x := h γ γ.2 x x.2 hle'
  apply hne
  have : γ • x = (1 : Γ) • x := by rw [one_smul]; exact Subtype.ext hx
  exact IsCancelSMul.right_cancel γ 1 x this

/-- The conjugate `φ γ φ⁻¹` acts on `φ p` as `φ (γ p)`. -/
private theorem rC_conj_smul (φ γ : isom d) (p : Minkowski d) :
    (MulAut.conj φ γ) • (φ • p) = φ • (γ • p) := by
  simp [MulAut.conj_apply, mul_smul]

private theorem rC_mem_frameConj {φ γ' : isom d} {Γ : Subgroup (isom d)}
    (h : γ' ∈ frameConj φ Γ) : ∃ γ ∈ Γ, MulAut.conj φ γ = γ' := by
  obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 h
  exact ⟨γ, hγ, rfl⟩

/-- **`Γ` preserves `Ω`** when `φΓφ⁻¹` preserves `φΩ`. -/
theorem rC_smul_mem_iff {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace (Minkowski d) M₁]
    {Γ : Subgroup (isom d)} {Ω : Opens (Minkowski d)} (φ : isom d)
    (hq : IsQuotientOf M₁ (frameConj φ Γ) (isomImage φ Ω)) {γ : isom d} (hγ : γ ∈ Γ)
    (p : Minkowski d) : γ • p ∈ Ω ↔ p ∈ Ω := by
  have key : ∀ g ∈ Γ, ∀ x, x ∈ Ω → g • x ∈ Ω := fun g hg x hx => by
    have h := hq.inv (MulAut.conj φ g) (Subgroup.mem_map_of_mem _ hg)
    have hx' : φ • x ∈ isomImage φ Ω := smul_mem_isomImage.2 hx
    have h2 : (MulAut.conj φ g) • (φ • x) ∈ ((isomImage φ Ω : Opens (Minkowski d)) :
        Set (Minkowski d)) := by
      rw [← h]; exact ⟨_, hx', rfl⟩
    rw [rC_conj_smul] at h2
    exact smul_mem_isomImage.1 h2
  refine ⟨fun h => ?_, key γ hγ p⟩
  have := key γ⁻¹ (Γ.inv_mem hγ) _ h
  rwa [inv_smul_smul] at this

/-- `φ p = L(φ) p + φ 0`. -/
private theorem rC_smul_eq (φ : isom d) (p : Minkowski d) :
    φ • p = (φ : Minkowski d ≃ᵃ[ℝ] Minkowski d).linear.toContinuousLinearEquiv p +
      φ • (0 : Minkowski d) := by
  have := isom_sub (φ : Minkowski d ≃ᵃ[ℝ] Minkowski d) 0 p
  rw [sub_zero] at this
  rw [isom_smul_def, isom_smul_def]
  change _ = (φ : Minkowski d ≃ᵃ[ℝ] Minkowski d).linear p + _
  rw [← this]
  abel

/-- **Absorbing the frame**: data `S ⊆ Ω` for `Γ` gives the Cauchy-completeness of
`M₁ = φΓφ⁻¹\φΩ`, through `φ S` (`isCauchySurfaceOn_isomImage`, `IsSpacelikeLipschitzIn.smul`,
the isometry `φ` of the induced lengths). -/
private theorem rC_of_frame {M₁ : FlatSpacetime.{u} d} {Γ : Subgroup (isom d)}
    {Ω : Opens (Minkowski d)} (φ : isom d)
    (hq : IsQuotientOf M₁ (frameConj φ Γ) (isomImage φ Ω)) {S : Set (Minkowski d)}
    (hSΩ : S ⊆ Ω) (hinv : ∀ γ ∈ Γ, ∀ p ∈ S, γ • p ∈ S)
    (hC : (minkowski d).IsCauchySurfaceOn Ω S) (hL : IsSpacelikeLipschitzIn Ω S)
    (hcomp : CompleteSpace (InducedLengthSpace d (Subtype.val ⁻¹' S : Set Ω)))
    (htop : Continuous fun x : InducedLengthSpace d (Subtype.val ⁻¹' S : Set Ω) =>
      (InducedLengthSpace.toSubtype x).1)
    (hacc : ∀ γ ∈ Γ, ∀ x ∈ Ω, (minkowski d).le ⊤ x (γ • x) → γ • x = x) :
    IsCauchyComplete d M₁ := by
  haveI := hq.invariant
  obtain ⟨π₀, hcov₀, -, -, hfib₀⟩ := hq.quot
  haveI : IsCancelSMul (frameConj φ Γ) (isomImage φ Ω) := rC_isCancelSMul hcov₀ hfib₀
  set A : Minkowski d ≃L[ℝ] Minkowski d :=
    (φ : Minkowski d ≃ᵃ[ℝ] Minkowski d).linear.toContinuousLinearEquiv with hAdef
  have hA : ∀ v, minkQ (A v) = minkQ v := fun v => minkQ_isom_linear φ v
  have hmem : ∀ p, (p ∈ Ω ∧ p ∈ S) ↔
      (A p + φ • (0 : Minkowski d) ∈ isomImage φ Ω ∧
        A p + φ • (0 : Minkowski d) ∈ (fun p => φ • p) '' S) := fun p => by
    rw [← rC_smul_eq, smul_mem_isomImage, (MulAction.injective φ).mem_set_image]
  obtain ⟨hc', ht'⟩ := rC_transfer A hA _ hmem hcomp htop
  have hac' : FlatQuotient.ActsAcausally (frameConj φ Γ) (isomImage φ Ω) := by
    refine rC_actsAcausally fun γ' hγ' x hx hle => ?_
    obtain ⟨γ, hγ, rfl⟩ := rC_mem_frameConj hγ'
    rw [← SetLike.mem_coe, coe_isomImage] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [rC_conj_smul] at hle ⊢
    have h1 := (isom_le_iff φ ⊤ y (γ • y)).1 (by rwa [isomImage_top])
    rw [hacc γ hγ y hy h1]
  refine isCauchyComplete_of_isQuotientOf_of_invariant hq hac' ?_ ?_
    (isCauchySurfaceOn_isomImage φ Ω hSΩ hC) ?_ hc' ht'
  · rintro _ ⟨p, hp, rfl⟩
    exact smul_mem_isomImage.2 (hSΩ hp)
  · rintro γ' hγ' _ ⟨p, hp, rfl⟩
    obtain ⟨γ, hγ, rfl⟩ := rC_mem_frameConj hγ'
    exact ⟨γ • p, hinv γ hγ p hp, (rC_conj_smul φ γ p).symm⟩
  · rw [Set.image_smul]
    exact hL.smul isom_strongMorphism φ

end Frame

/-! ### Time reversal by `p ↦ −p` (it reverses the causal relations of every open set) -/

section Negation

/-- Negation `p ↦ −p`, a chart of `𝐌ⁿ` defined everywhere. -/
noncomputable def rC_negChart : OpenPartialHomeomorph (Minkowski d) (Minkowski d) :=
  (Homeomorph.neg (Minkowski d)).toOpenPartialHomeomorph

/-- `−U`, as an open set. -/
noncomputable def rC_negOpens (U : Opens (Minkowski d)) : Opens (Minkowski d) :=
  chartImage rC_negChart U

theorem rC_mem_negOpens {U : Opens (Minkowski d)} {p : Minkowski d} :
    p ∈ rC_negOpens U ↔ -p ∈ U := by
  change p ∈ rC_negChart '' (rC_negChart.source ∩ (U : Set (Minkowski d))) ↔ _
  constructor
  · rintro ⟨q, ⟨-, hq⟩, rfl⟩
    change -(-q) ∈ U
    rwa [neg_neg]
  · intro h
    exact ⟨-p, ⟨trivial, h⟩, neg_neg p⟩

theorem rC_coe_negOpens (U : Opens (Minkowski d)) :
    (rC_negOpens U : Set (Minkowski d)) = (fun p => -p) '' (U : Set (Minkowski d)) := by
  ext p
  rw [SetLike.mem_coe, rC_mem_negOpens]
  constructor
  · intro h; exact ⟨-p, h, neg_neg p⟩
  · rintro ⟨q, hq, rfl⟩; rwa [neg_neg]

private theorem rC_mem_neg_image {A : Set (Minkowski d)} {p : Minkowski d} :
    p ∈ (fun q => -q) '' A ↔ -p ∈ A := by
  constructor
  · rintro ⟨q, hq, rfl⟩; rwa [neg_neg]
  · intro h; exact ⟨-p, h, neg_neg p⟩

private theorem rC_convex_negOpens {U : Opens (Minkowski d)}
    (hU : Convex ℝ (U : Set (Minkowski d))) : Convex ℝ (rC_negOpens U : Set (Minkowski d)) := by
  have : (rC_negOpens U : Set (Minkowski d)) = -(U : Set (Minkowski d)) := by
    ext p; exact rC_mem_negOpens
  rw [this]; exact hU.neg

/-- Negation reverses `≤` of `𝐌ⁿ`. -/
theorem rC_le_top_neg {p q : Minkowski d} (h : (minkowski d).le ⊤ p q) :
    (minkowski d).le ⊤ (-q) (-p) := by
  rw [minkowski_le_top_iff] at h ⊢
  simp only [Prod.snd_neg, Prod.fst_neg]
  rw [show -p.2 - -q.2 = q.2 - p.2 by abel]
  linarith

/-- Negation reverses `≪` of `𝐌ⁿ`. -/
theorem rC_lt_top_neg {p q : Minkowski d} (h : (minkowski d).lt ⊤ p q) :
    (minkowski d).lt ⊤ (-q) (-p) := by
  rw [minkowski_lt_top_iff] at h ⊢
  simp only [Prod.snd_neg, Prod.fst_neg]
  rw [show -p.2 - -q.2 = q.2 - p.2 by abel]
  linarith

private theorem rC_negTransport_le_iff {O : Opens (Minkowski d)}
    (hO : Convex ℝ (O : Set (Minkowski d))) {p q : Minkowski d} :
    ((minkowski d).chartTransport rC_negChart).le O p q ↔ (minkowski d).dual.le O p q := by
  have hiso := (minkowski d).chartTransport_chartIso rC_negChart
  have hO' := rC_convex_negOpens hO
  constructor
  · intro h
    have hp := ((minkowski d).chartTransport rC_negChart).le_mem_left h
    have hq := ((minkowski d).chartTransport rC_negChart).le_mem_right h
    have h' := ((hiso O (fun _ _ => trivial) p hp q hq).1).1 h
    change (minkowski d).le (rC_negOpens O) (-p) (-q) at h'
    rw [le_iff_of_convex hO'] at h'
    change (minkowski d).le O q p
    rw [le_iff_of_convex hO]
    refine ⟨hq, hp, ?_⟩
    simpa using rC_le_top_neg h'.2.2
  · intro h
    change (minkowski d).le O q p at h
    rw [le_iff_of_convex hO] at h
    obtain ⟨hq, hp, h⟩ := h
    refine ((hiso O (fun _ _ => trivial) p hp q hq).1).2 ?_
    change (minkowski d).le (rC_negOpens O) (-p) (-q)
    rw [le_iff_of_convex hO']
    exact ⟨rC_mem_negOpens.2 (by simpa using hp), rC_mem_negOpens.2 (by simpa using hq),
      rC_le_top_neg h⟩

private theorem rC_negTransport_lt_iff {O : Opens (Minkowski d)}
    (hO : Convex ℝ (O : Set (Minkowski d))) {p q : Minkowski d} :
    ((minkowski d).chartTransport rC_negChart).lt O p q ↔ (minkowski d).dual.lt O p q := by
  have hiso := (minkowski d).chartTransport_chartIso rC_negChart
  have hO' := rC_convex_negOpens hO
  constructor
  · intro h
    have hp := ((minkowski d).chartTransport rC_negChart).lt_mem_left h
    have hq := ((minkowski d).chartTransport rC_negChart).lt_mem_right h
    have h' := ((hiso O (fun _ _ => trivial) p hp q hq).2).1 h
    change (minkowski d).lt (rC_negOpens O) (-p) (-q) at h'
    rw [lt_iff_of_convex hO'] at h'
    change (minkowski d).lt O q p
    rw [lt_iff_of_convex hO]
    refine ⟨hq, hp, ?_⟩
    simpa using rC_lt_top_neg h'.2.2
  · intro h
    change (minkowski d).lt O q p at h
    rw [lt_iff_of_convex hO] at h
    obtain ⟨hq, hp, h⟩ := h
    refine ((hiso O (fun _ _ => trivial) p hp q hq).2).2 ?_
    change (minkowski d).lt (rC_negOpens O) (-p) (-q)
    rw [lt_iff_of_convex hO']
    exact ⟨rC_mem_negOpens.2 (by simpa using hp), rC_mem_negOpens.2 (by simpa using hq),
      rC_lt_top_neg h⟩

/-- **The causality of `𝐌ⁿ` transported along `p ↦ −p` is its time reversal.** -/
theorem rC_negTransport_eq :
    (minkowski d).chartTransport rC_negChart = (minkowski d).dual :=
  Causality.eq_of_agree_on_basis _ exists_convex_opens
    (fun _ => ((minkowski d).chartTransport_chartIso _).absolutelyMinimalOn (fun _ _ => trivial)
      (minkowski_causallyArcConnected.absolutelyMinimalOn_all _))
    (fun W => Precausality.dual_absolutelyMinimalOn.2
      (minkowski_causallyArcConnected.absolutelyMinimalOn_all W))
    fun _ hO _ _ => ⟨rC_negTransport_le_iff hO, rC_negTransport_lt_iff hO⟩

/-- **`p ↦ −p` reverses the relations of every open set**: `q ≤_U p ↔ −p ≤_{−U} −q`. -/
theorem rC_neg_rel (U : Opens (Minkowski d)) (p q : Minkowski d) :
    ((minkowski d).le U q p ↔ (minkowski d).le (rC_negOpens U) (-p) (-q)) ∧
      ((minkowski d).lt U q p ↔ (minkowski d).lt (rC_negOpens U) (-p) (-q)) := by
  have hiso := (minkowski d).chartTransport_chartIso rC_negChart
  rw [rC_negTransport_eq] at hiso
  by_cases hp : p ∈ U
  · by_cases hq : q ∈ U
    · exact hiso U (fun _ _ => trivial) p hp q hq
    · refine ⟨⟨fun h => absurd ((minkowski d).le_mem_left h) hq, fun h => ?_⟩,
        ⟨fun h => absurd ((minkowski d).lt_mem_left h) hq, fun h => ?_⟩⟩
      · exact absurd (by simpa using rC_mem_negOpens.1 ((minkowski d).le_mem_right h)) hq
      · exact absurd (by simpa using rC_mem_negOpens.1 ((minkowski d).lt_mem_right h)) hq
  · refine ⟨⟨fun h => absurd ((minkowski d).le_mem_right h) hp, fun h => ?_⟩,
      ⟨fun h => absurd ((minkowski d).lt_mem_right h) hp, fun h => ?_⟩⟩
    · exact absurd (by simpa using rC_mem_negOpens.1 ((minkowski d).le_mem_left h)) hp
    · exact absurd (by simpa using rC_mem_negOpens.1 ((minkowski d).lt_mem_left h)) hp

/-- `p ↦ −p` is a morphism from the time-reversed `𝐌ⁿ` to `𝐌ⁿ`. -/
theorem rC_neg_isEMorphism :
    IsEMorphism (minkowski d).dual (minkowski d) fun p : Minkowski d => -p := by
  have hU : ∀ (U : Opens (Minkowski d)) (V : Opens (Minkowski d)),
      (V : Set (Minkowski d)) = (fun p : Minkowski d => -p) ⁻¹' U → rC_negOpens V = U :=
    fun U V hV => SetLike.ext fun p => by
      rw [rC_mem_negOpens, ← SetLike.mem_coe, hV, mem_preimage, neg_neg, SetLike.mem_coe]
  refine isEMorphism_iff.2 ⟨⟨continuous_neg, (Homeomorph.neg (Minkowski d)).isOpenMap,
    fun U V hV x y hxy => ?_, fun U V hV x y hxy => ?_⟩,
    ⟨(Homeomorph.neg (Minkowski d)).isLocalHomeomorph, fun x => ⟨⊤, trivial,
      neg_injective.injOn, fun V' _ U hU' y _ z _ => ?_⟩⟩⟩
  · rw [← hU U V hV]; exact (rC_neg_rel V x y).1.1 hxy
  · rw [← hU U V hV]; exact (rC_neg_rel V x y).2.1 hxy
  · have : U = rC_negOpens V' := SetLike.coe_injective (by rw [hU', rC_coe_negOpens])
    subst this
    exact rC_neg_rel V' y z

/-- **`p ↦ −p` carries Cauchy surfaces of `V` to Cauchy surfaces of `−V`.** -/
theorem rC_isCauchySurfaceOn_neg {V : Opens (Minkowski d)} {S : Set (Minkowski d)}
    (hS : S ⊆ V) (h : (minkowski d).IsCauchySurfaceOn V S) :
    (minkowski d).IsCauchySurfaceOn (rC_negOpens V) ((fun p => -p) '' S) :=
  (rC_neg_isEMorphism.isCauchySurfaceOn_image_iff neg_injective.injOn le_top
    (rC_coe_negOpens V) hS).1 (Causality.dual_isCauchySurfaceOn.2 h)

/-- `σ g σ` moves `−A` as `g` moves `A`. -/
private theorem rC_negConj_smul_image (g : isom d) (A : Set (Minkowski d)) :
    negConj g • ((fun p => -p) '' A) = (fun p => -p) '' (g • A) := by
  ext z
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨g • a, ⟨a, ha, rfl⟩, by
      show -(g • a) = negConj g • -a
      rw [negConj_smul, neg_neg]⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨-a, ⟨a, ha, rfl⟩, by
      show negConj g • -a = -(g • a)
      rw [negConj_smul, neg_neg]⟩

private theorem rC_neg_graphOver (U : Set (EuclideanSpace ℝ (Fin d)))
    (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    (fun p => -p) '' graphOver U f = graphOver ((fun x => -x) ⁻¹' U) fun x => -f (-x) := by
  ext q
  rw [rC_mem_neg_image]
  simp only [graphOver, mem_setOf_eq, mem_preimage, Prod.snd_neg, Prod.fst_neg]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [← h2, neg_neg]⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [h2, neg_neg]⟩

/-- **`p ↦ −p` carries spacelike Lipschitz hypersurfaces of `V` to those of `−V`** (frames
`σ g σ`, graphs of `x ↦ −f(−x)`). -/
theorem rC_isSpacelikeLipschitzIn_neg {V : Opens (Minkowski d)} {S : Set (Minkowski d)}
    (h : IsSpacelikeLipschitzIn V S) :
    IsSpacelikeLipschitzIn (rC_negOpens V) ((fun p => -p) '' S) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact rC_mem_negOpens.2 (by simpa using h.subset hp)
  · rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ hpq
    exact h.achronal q hq p hp ((rC_neg_rel V p q).2.2 hpq)
  · rintro _ ⟨p, hp, rfl⟩
    obtain ⟨g, O, U, f, c, hc, hpO, hOV, hU, hf, hgr⟩ := h.locGraph p hp
    refine ⟨negConj g, rC_negOpens O, (fun x => -x) ⁻¹' U, fun x => -f (-x), c, hc,
      rC_mem_negOpens.2 (by simpa using hpO), fun x hx => ?_, hU.preimage continuous_neg,
      fun x hx y hy => ?_, ?_⟩
    · rw [rC_mem_negOpens] at hx ⊢; exact hOV hx
    · have := hf hx hy
      simpa [edist_neg_neg] using this
    · rw [rC_coe_negOpens, ← image_inter neg_injective, rC_negConj_smul_image, hgr,
        image_inter neg_injective, ← rC_negConj_smul_image, rC_neg_graphOver]

end Negation

/-! ### (B′) `bcor:level_sets_complete`: the analytic estimates -/

section LevelAlgebra

private theorem rB_add_right (v p q : Minkowski d) : minkB v (p + q) = minkB v p + minkB v q := by
  simp only [minkB, Prod.fst_add, Prod.snd_add, inner_add_right]; ring

private theorem rB_sub_right (v p q : Minkowski d) : minkB v (p - q) = minkB v p - minkB v q := by
  simp only [minkB, Prod.fst_sub, Prod.snd_sub, inner_sub_right]; ring

private theorem rB_smul_right (v p : Minkowski d) (c : ℝ) : minkB v (c • p) = c * minkB v p := by
  simp only [minkB, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, real_inner_smul_right]; ring

private theorem rB_smul_left (v p : Minkowski d) (c : ℝ) : minkB (c • v) p = c * minkB v p := by
  rw [minkB_comm, rB_smul_right, minkB_comm]

private theorem rQ_add (v w : Minkowski d) :
    minkQ (v + w) = minkQ v + 2 * minkB v w + minkQ w := by
  simp only [minkQ, minkB, Prod.fst_add, Prod.snd_add, norm_add_sq_real]; ring

private theorem rQ_sub (v w : Minkowski d) :
    minkQ (v - w) = minkQ v - 2 * minkB v w + minkQ w := by
  simp only [minkQ, minkB, Prod.fst_sub, Prod.snd_sub, norm_sub_sq_real]; ring

/-- A vector orthogonal to a future timelike one is spacelike or zero. -/
theorem rC_minkQ_nonneg_of_orth {n x : Minkowski d} (hn : IsFutureTimelike n)
    (hx : minkB n x = 0) : 0 ≤ minkQ x := by
  by_contra hneg
  push Not at hneg
  have hx0 : x ≠ 0 := fun h0 => by rw [h0] at hneg; simp [minkQ] at hneg
  rcases le_or_gt 0 x.1 with h1 | h1
  · have := minkB_neg_of_isFutureTimelike hn ⟨h1, hneg.le⟩ hx0
    linarith
  · have hc : IsFutureCausal (-x) := ⟨by simp only [Prod.fst_neg]; linarith, by
      rw [minkQ_neg]; exact hneg.le⟩
    have := minkB_neg_of_isFutureTimelike hn hc (neg_ne_zero.2 hx0)
    have e : minkB n (-x) = -minkB n x := by
      simp only [minkB, Prod.fst_neg, Prod.snd_neg, inner_neg_right]; ring
    rw [e, hx] at this
    linarith

/-- **Cauchy–Schwarz on `n^⊥`**: for `n` unit future timelike and `v ⊥ n`,
`⟨v | w⟩² ≤ |v|² (|w|² + ⟨n | w⟩²)`. -/
theorem rC_minkB_sq_le {n v w : Minkowski d} (hn : IsFutureTimelike n) (hnQ : minkQ n = -1)
    (hv : minkB n v = 0) : minkB v w ^ 2 ≤ minkQ v * (minkQ w + minkB n w ^ 2) := by
  set β := minkB n w
  set w' := w + β • n with hw'
  have hnw' : minkB n w' = 0 := by
    rw [hw', rB_add_right, rB_smul_right, ← minkQ_eq_minkB, hnQ]; ring
  have hQw' : minkQ w' = minkQ w + β ^ 2 := by
    rw [hw', rQ_add, rB_smul_right, minkQ_smul, hnQ, minkB_comm w n]; ring
  have hvw' : minkB v w' = minkB v w := by
    rw [hw', rB_add_right, rB_smul_right, minkB_comm v n, hv]; ring
  set a := minkQ v
  set b := minkB v w
  set c := minkQ w'
  have hpos : ∀ l₁ l₂ : ℝ, 0 ≤ minkQ (l₁ • v + l₂ • w') := fun l₁ l₂ => by
    refine rC_minkQ_nonneg_of_orth hn ?_
    rw [rB_add_right, rB_smul_right, rB_smul_right, hv, hnw']; ring
  have hexp : ∀ l₁ l₂ : ℝ, minkQ (l₁ • v + l₂ • w') =
      l₁ ^ 2 * a + 2 * l₁ * l₂ * b + l₂ ^ 2 * c := fun l₁ l₂ => by
    rw [rQ_add, minkQ_smul, minkQ_smul, rB_smul_left, rB_smul_right, hvw']; ring
  have h1 := hpos c (-b); rw [hexp] at h1
  have h2 := hpos (-b) a; rw [hexp] at h2
  have h3 := hpos 1 (-b); rw [hexp] at h3
  have ha : 0 ≤ a := by have := hpos 1 0; rw [hexp] at this; linarith
  have hc : 0 ≤ c := by have := hpos 0 1; rw [hexp] at this; linarith
  rw [← hQw']
  change b ^ 2 ≤ a * c
  rcases ha.eq_or_lt with ha0 | ha0
  · rcases hc.eq_or_lt with hc0 | hc0
    · rw [← ha0, ← hc0] at h3; nlinarith
    · nlinarith
  · nlinarith

/-- **The time component of a unit future timelike vector is controlled**: for `a, b` unit
future timelike, `a₀ ≤ 2 (−⟨a | b⟩) b₀` (the hyperbolic triangle inequality, coarsely). -/
theorem rC_fst_le_of_unit {a b : Minkowski d} (ha : IsFutureTimelike a) (haQ : minkQ a = -1)
    (hb : IsFutureTimelike b) (hbQ : minkQ b = -1) : a.1 ≤ 2 * (-minkB a b) * b.1 := by
  set x := a.1
  set y := b.1
  have hx : 0 < x := ha.1
  have hy : 0 < y := hb.1
  have hxa : ‖a.2‖ ^ 2 = x ^ 2 - 1 := by unfold minkQ at haQ; linarith
  have hyb : ‖b.2‖ ^ 2 = y ^ 2 - 1 := by unfold minkQ at hbQ; linarith
  have hy1 : 1 ≤ y := by nlinarith [sq_nonneg ‖b.2‖]
  have hx1 : 1 ≤ x := by nlinarith [sq_nonneg ‖a.2‖]
  set s := ‖a.2‖ * ‖b.2‖
  have hs0 : 0 ≤ s := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hs2 : s ^ 2 = (x ^ 2 - 1) * (y ^ 2 - 1) := by rw [mul_pow, hxa, hyb]
  have hsxy : s ≤ x * y := by
    by_contra hc; push Not at hc
    have := mul_self_lt_mul_self (by positivity : 0 ≤ x * y) hc
    nlinarith
  have hinner : inner ℝ a.2 b.2 ≤ s := real_inner_le_norm _ _
  have hD : x * y - s ≤ -minkB a b := by unfold minkB; linarith
  have hkey : (x * y - s) * (x * y + s) = x ^ 2 + y ^ 2 - 1 := by nlinarith
  have hDpos : 0 ≤ x * y - s := by linarith
  have h2 : x ^ 2 ≤ 2 * (x * y - s) * y * x := by nlinarith
  have h3 : x ≤ 2 * (x * y - s) * y := by
    by_contra hc; push Not at hc; nlinarith
  nlinarith

/-- **The slope bound**: for `n` unit future timelike and `v ⊥ n`, `‖v⃗‖² ≤ n₀² |v|²`. -/
theorem rC_norm_snd_sq_le {n v : Minkowski d} (hnQ : minkQ n = -1) (hv : minkB n v = 0) :
    ‖v.2‖ ^ 2 ≤ n.1 ^ 2 * minkQ v := by
  have hn2 : ‖n.2‖ ^ 2 = n.1 ^ 2 - 1 := by unfold minkQ at hnQ; linarith
  have hv' : n.1 * v.1 = inner ℝ n.2 v.2 := by unfold minkB at hv; linarith
  have hcs : |inner ℝ n.2 v.2| ≤ ‖n.2‖ * ‖v.2‖ := abs_real_inner_le_norm _ _
  have hsq : (inner ℝ n.2 v.2) ^ 2 ≤ ‖n.2‖ ^ 2 * ‖v.2‖ ^ 2 := by
    rw [← mul_pow, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hcs 2
  unfold minkQ
  rw [← hv', mul_pow, hn2] at hsq
  nlinarith

/-- The derivative of `|γ|²` along a curve: `2 ⟨γ | γ'⟩`. -/
theorem rC_hasDerivAt_minkQ {γ : ℝ → Minkowski d} {v : Minkowski d} {u : ℝ}
    (hγ : HasDerivAt γ v u) : HasDerivAt (fun x => minkQ (γ x)) (2 * minkB (γ u) v) u := by
  have h1 : HasDerivAt (fun x => (γ x).1) v.1 u :=
    (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin d))).hasFDerivAt.comp_hasDerivAt u hγ
  have h2 : HasDerivAt (fun x => (γ x).2) v.2 u :=
    (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin d))).hasFDerivAt.comp_hasDerivAt u hγ
  have h3 : HasDerivAt (fun x => ‖(γ x).2‖ ^ 2) (2 * inner ℝ (γ u).2 v.2) u := h2.norm_sq
  have h4 := (h1.pow 2).neg.add h3
  refine h4.congr_deriv ?_
  simp only [minkB]
  norm_num
  ring

private theorem rC_abs_minkB_le (x y : Minkowski d) : |minkB x y| ≤ 2 * ‖x‖ * ‖y‖ := by
  have h1 : |x.1 * y.1| ≤ ‖x‖ * ‖y‖ := by
    rw [abs_mul]
    exact mul_le_mul (by simpa using norm_fst_le x) (by simpa using norm_fst_le y)
      (abs_nonneg _) (norm_nonneg _)
  have h2 : |inner ℝ x.2 y.2| ≤ ‖x‖ * ‖y‖ :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul (norm_snd_le x) (norm_snd_le y)
      (norm_nonneg _) (norm_nonneg _))
  unfold minkB
  calc |-(x.1 * y.1) + inner ℝ x.2 y.2| ≤ |-(x.1 * y.1)| + |inner ℝ x.2 y.2| := abs_add_le _ _
    _ ≤ _ := by rw [abs_neg]; linarith

theorem rC_abs_minkQ_sub_le (a b : Minkowski d) :
    |minkQ a - minkQ b| ≤ 2 * ‖a - b‖ * (‖a‖ + ‖b‖) := by
  have e : minkQ a - minkQ b = minkB (a - b) (a + b) := by
    simp only [minkQ, minkB, Prod.fst_sub, Prod.fst_add, Prod.snd_sub, Prod.snd_add,
      inner_sub_left, inner_add_right, real_inner_self_eq_norm_sq, real_inner_comm a.2 b.2]
    ring
  rw [e]
  refine (rC_abs_minkB_le _ _).trans ?_
  have := norm_add_le a b
  have := norm_nonneg (a - b)
  nlinarith

private theorem rC_abs_log_sub_le {m y y' : ℝ} (hm : 0 < m) (hy : m ≤ y) (hy' : m ≤ y') :
    |Real.log y - Real.log y'| ≤ |y - y'| / m := by
  have k : ∀ a b : ℝ, m ≤ a → m ≤ b → Real.log a - Real.log b ≤ |a - b| / m :=
    fun a b ha hb => by
      have hb0 : 0 < b := hm.trans_le hb
      have ha0 : 0 < a := hm.trans_le ha
      rw [← Real.log_div ha0.ne' hb0.ne']
      calc Real.log (a / b) ≤ a / b - 1 := Real.log_le_sub_one_of_pos (div_pos ha0 hb0)
        _ = (a - b) / b := by field_simp
        _ ≤ |a - b| / b := div_le_div_of_nonneg_right (le_abs_self _) hb0.le
        _ ≤ |a - b| / m := div_le_div_of_nonneg_left (abs_nonneg _) hm hb
  rw [abs_le]
  constructor
  · have := k y' y hy' hy
    rw [abs_sub_comm] at this
    linarith
  · exact k y y' hy hy'

end LevelAlgebra

/-! ### (B) The level sets of the cosmological time -/

section Level

variable {Λ : Set (PenroseSphere d × ℝ)}



/-- `p − r(p) = t n(p)` on `S_t`. -/
private theorem rC_sub_retract (h : CosmoRegular Λ) {t : ℝ} {p : Minkowski d}
    (hp : p ∈ cosmoLevel Λ t) : p - cosmoRetract Λ p = t • gaussMap Λ p := by
  rw [← smul_gaussMap h hp.1, hp.2]

/-- **`S_t` lies to the future of its tangent planes**: `⟨n(p) | p' − p⟩ ≤ 0` on `S_t`
(`cosmoTime_mul_le` at `T = t`). -/
theorem rC_minkB_gaussMap_le (h : CosmoRegular Λ) {t : ℝ} (ht : 0 < t) {p p' : Minkowski d}
    (hp : p ∈ cosmoLevel Λ t) (hp' : p' ∈ cosmoLevel Λ t) :
    minkB (gaussMap Λ p) (p' - p) ≤ 0 := by
  have h1 := cosmoTime_mul_le h hp.1 hp'.1
  rw [rC_sub_retract h hp, hp.2, hp'.2, rB_smul_left] at h1
  nlinarith

/-- **`S_t` lies to the past of its osculating hyperboloids**: `−|p' − p|² ≤ 2t ⟨n(p) | p' − p⟩`
on `S_t` (the hyperboloid `r(p) + t ℍ` lies in `{T ≥ t}`). -/
theorem rC_neg_minkQ_le (h : CosmoRegular Λ) {t : ℝ} (ht : 0 < t) {p p' : Minkowski d}
    (hp : p ∈ cosmoLevel Λ t) (hp' : p' ∈ cosmoLevel Λ t) :
    -minkQ (p' - p) ≤ 2 * t * minkB (gaussMap Λ p) (p' - p) := by
  set r := cosmoRetract Λ p
  set n := gaussMap Λ p
  have hrf := (cosmoRetract_spec h hp.1).1
  have hnQ : minkQ n = -1 := minkQ_gaussMap h hp.1
  have key : -minkQ (p' - r) ≤ t ^ 2 := by
    by_cases hle : (minkowski d).le ⊤ r p'
    · have h1 := segTime_le_cosmoTime h hp'.1 ⟨frontier_subset_closure hrf, hle⟩
      rw [hp'.2] at h1
      have hc := (le_top_iff_minkQ.1 hle).2
      have hnn : 0 ≤ -minkQ (p' - r) := by linarith
      unfold segTime at h1
      have := Real.sq_sqrt hnn
      nlinarith [Real.sqrt_nonneg (-minkQ (p' - r))]
    · rw [minkowski_le_top_iff] at hle
      push Not at hle
      rcases le_or_gt (r.1 - p'.1) ‖p'.2 - r.2‖ with h2 | h2
      · have hq : 0 ≤ minkQ (p' - r) := by
          simp only [minkQ, Prod.fst_sub, Prod.snd_sub]
          nlinarith [norm_nonneg (p'.2 - r.2)]
        nlinarith
      · exfalso
        have hle' : (minkowski d).le ⊤ p' r := by
          rw [minkowski_le_top_iff, norm_sub_rev]; exact h2.le
        have hrΩ := Jplus_omegaPlus_subset Λ ⟨p', hp'.1, hle'⟩
        rw [h.regular.2.frontier_eq] at hrf
        exact hrf.2 hrΩ
  have he : p' - r = (p' - p) + t • n := by
    rw [← rC_sub_retract h hp]; abel
  rw [he, rQ_add, rB_smul_right, minkQ_smul, hnQ, minkB_comm] at key
  nlinarith

/-- Two points of `S_t` are spacelike or null separated. -/
theorem rC_minkQ_sub_nonneg (h : CosmoRegular Λ) {t : ℝ} (ht : 0 < t) {p p' : Minkowski d}
    (hp : p ∈ cosmoLevel Λ t) (hp' : p' ∈ cosmoLevel Λ t) : 0 ≤ minkQ (p' - p) := by
  have h1 := rC_minkB_gaussMap_le h ht hp hp'
  have h2 := rC_neg_minkQ_le h ht hp hp'
  nlinarith

/-- **Tangency**: a curve of `S_t` differentiable at `s` has its velocity orthogonal to `n`. -/
theorem rC_minkB_deriv_eq_zero (h : CosmoRegular Λ) {t : ℝ} (ht : 0 < t) {c : ℝ → Minkowski d}
    (hc : ∀ s, c s ∈ cosmoLevel Λ t) {s : ℝ} (hd : DifferentiableAt ℝ c s) :
    minkB (gaussMap Λ (c s)) (deriv c s) = 0 := by
  set n := gaussMap Λ (c s)
  let L : Minkowski d →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (minkBL n)
  have hL : ∀ v, L v = minkB n v := fun v => by
    change minkBL n v = _; rw [minkBL_apply, minkB_comm]
  have hder : HasDerivAt (fun u => L (c u - c s)) (L (deriv c s)) s :=
    L.hasFDerivAt.comp_hasDerivAt s (hd.hasDerivAt.sub_const (c s))
  have hmax : IsLocalMax (fun u => L (c u - c s)) s :=
    Filter.Eventually.of_forall fun u => by
      simp only [hL, sub_self]
      rw [show minkB n 0 = 0 by simp [minkB]]
      exact rC_minkB_gaussMap_le h ht (hc s) (hc u)
  rw [← hL]
  exact hmax.hasDerivAt_eq_zero hder

/-- **The Grönwall estimate** (the step of `bcor:level_sets_complete` that replaces Barbot's
convergence of the Gauss map): along a Lipschitz curve `c` of `S_t`,
`|c(s) − c(0)|² + 2t² ≤ 2t² exp(ℓ/t)`, `ℓ` the length of `c|[0,s]`. With `Y = |c − c(0)|² + 2t²`,
`Y' = 2⟨c − c(0) | c'⟩`, and since `c' ⊥ n(c)` (tangency) and
`0 ≤ ⟨n(c) | c − c(0)⟩ ≤ |c − c(0)|²/2t` (the tangent plane and the osculating hyperboloid),
Cauchy–Schwarz on `n^⊥` gives `|Y'| ≤ √|c'|² Y / t`. -/
theorem rC_gronwall (h : CosmoRegular Λ) {t : ℝ} (ht : 0 < t) {c : ℝ → Minkowski d}
    {K : ℝ≥0} (hcL : LipschitzWith K c) (hc : ∀ s, c s ∈ cosmoLevel Λ t) {s : ℝ}
    (hs : 0 ≤ s) :
    minkQ (c s - c 0) + 2 * t ^ 2 ≤
      2 * t ^ 2 * Real.exp ((∫ u in (0 : ℝ)..s, Real.sqrt (minkQ (deriv c u))) / t) := by
  set Y : ℝ → ℝ := fun u => minkQ (c u - c 0) + 2 * t ^ 2 with hYdef
  have ht2 : 0 < 2 * t ^ 2 := by positivity
  have hYge : ∀ u, 2 * t ^ 2 ≤ Y u := fun u => by
    have := rC_minkQ_sub_nonneg h ht (hc 0) (hc u); simp only [hYdef]; linarith
  have hYpos : ∀ u, 0 < Y u := fun u => ht2.trans_le (hYge u)
  set Z : ℝ → ℝ := fun u => Real.log (Y u) with hZdef
  have hbd : ∀ u ∈ Icc 0 s, ‖c u - c 0‖ ≤ K * s := fun u hu => by
    have := hcL.dist_le_mul u 0
    rw [dist_eq_norm, Real.dist_eq, sub_zero, abs_of_nonneg hu.1] at this
    exact this.trans (mul_le_mul_of_nonneg_left hu.2 K.2)
  have hYL : LipschitzOnWith (Real.toNNReal (4 * K * s * K)) Y (Icc 0 s) := by
    refine LipschitzOnWith.of_dist_le_mul fun u hu v hv => ?_
    rw [Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
    simp only [hYdef, add_sub_add_right_eq_sub]
    refine (rC_abs_minkQ_sub_le _ _).trans ?_
    have h1 : ‖(c u - c 0) - (c v - c 0)‖ ≤ K * dist u v := by
      rw [sub_sub_sub_cancel_right, ← dist_eq_norm]; exact hcL.dist_le_mul u v
    have h2 := hbd u hu
    have h3 := hbd v hv
    calc 2 * ‖(c u - c 0) - (c v - c 0)‖ * (‖c u - c 0‖ + ‖c v - c 0‖)
        ≤ 2 * (K * dist u v) * (K * s + K * s) := by gcongr
      _ = 4 * K * s * K * dist u v := by ring
  have hlog : LipschitzOnWith (Real.toNNReal (1 / (2 * t ^ 2))) Real.log (Ici (2 * t ^ 2)) := by
    refine LipschitzOnWith.of_dist_le_mul fun y hy y' hy' => ?_
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity), one_div_mul_eq_div]
    exact rC_abs_log_sub_le ht2 hy hy'
  have hZL := hlog.comp hYL fun u _ => hYge u
  rw [← uIcc_of_le hs] at hZL
  have hAC := hZL.absolutelyContinuousOnInterval
  have hFTC : ∫ u in (0 : ℝ)..s, deriv Z u = Z s - Z 0 := hAC.integral_deriv_eq_sub
  -- the pointwise bound on `Z'`
  have hpt : ∀ u, DifferentiableAt ℝ c u →
      deriv Z u ≤ Real.sqrt (minkQ (deriv c u)) / t := fun u hd => by
    set v := deriv c u
    set w := c u - c 0
    set n := gaussMap Λ (c u)
    have hγ : HasDerivAt (fun x => c x - c 0) v u := hd.hasDerivAt.sub_const _
    have hY' : HasDerivAt Y (2 * minkB w v) u := (rC_hasDerivAt_minkQ hγ).add_const _
    have hZ' : HasDerivAt Z (2 * minkB w v / Y u) u := hY'.log (hYpos u).ne'
    rw [hZ'.deriv]
    have hn := isFutureTimelike_gaussMap h (hc u).1
    have hnQ := minkQ_gaussMap h (hc u).1
    have htan : minkB n v = 0 := rC_minkB_deriv_eq_zero h ht hc hd
    have hcs := rC_minkB_sq_le hn hnQ htan (w := w)
    have hβ1 := rC_minkB_gaussMap_le h ht (hc u) (hc 0)
    have hβ2 := rC_neg_minkQ_le h ht (hc u) (hc 0)
    have hneg : c 0 - c u = -w := by simp only [w, neg_sub]
    have hBneg : minkB n (-w) = -minkB n w := by
      simp only [minkB, Prod.fst_neg, Prod.snd_neg, inner_neg_right]; ring
    rw [hneg, hBneg] at hβ1 hβ2
    rw [minkQ_neg] at hβ2
    have hQw : 0 ≤ minkQ w := rC_minkQ_sub_nonneg h ht (hc 0) (hc u)
    have hQv : 0 ≤ minkQ v := rC_minkQ_nonneg_of_orth hn htan
    set ρ := Real.sqrt (minkQ v)
    have hρ : ρ ^ 2 = minkQ v := Real.sq_sqrt hQv
    have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
    have hYu : Y u = minkQ w + 2 * t ^ 2 := rfl
    have hb : minkB n w * (2 * t) ≤ minkQ w := by linarith
    have hb0 : 0 ≤ minkB n w := by linarith
    have hb2 : (minkB n w) ^ 2 * (4 * t ^ 2) ≤ (minkQ w) ^ 2 := by
      have := mul_self_le_mul_self (mul_nonneg hb0 (by positivity : (0 : ℝ) ≤ 2 * t)) hb
      nlinarith
    have hsq : (minkB w v) ^ 2 * (4 * t ^ 2) ≤ (ρ * Y u) ^ 2 := by
      rw [minkB_comm, mul_pow, hρ, hYu]
      have := mul_le_mul_of_nonneg_right hcs (by positivity : (0 : ℝ) ≤ 4 * t ^ 2)
      refine this.trans ?_
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hQv
      nlinarith
    have habs : minkB w v * (2 * t) ≤ ρ * Y u := by
      have hM : 0 ≤ ρ * Y u := mul_nonneg hρ0 (hYpos u).le
      by_contra hc'
      push Not at hc'
      nlinarith
    rw [div_le_div_iff₀ (hYpos u) ht]
    nlinarith
  have hintZ := hAC.intervalIntegrable_deriv
  have hintρ : IntervalIntegrable (fun u => Real.sqrt (minkQ (deriv c u)) / t) volume 0 s :=
    intervalIntegrable_of_bound ((Real.continuous_sqrt.measurable.comp
      (continuous_minkQ.measurable.comp (measurable_deriv c))).div_const t) (K / t)
      (fun u => by
        rw [Real.norm_eq_abs]
        change |Real.sqrt (minkQ (deriv c u)) / t| ≤ _
        rw [abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) ht.le)]
        exact div_le_div_of_nonneg_right ((sqrt_minkQ_le _).trans ((norm_snd_le _).trans
          (norm_deriv_le_of_lipschitz hcL))) ht.le) 0 s
  have hint : ∫ u in (0 : ℝ)..s, deriv Z u ≤
      ∫ u in (0 : ℝ)..s, Real.sqrt (minkQ (deriv c u)) / t :=
    intervalIntegral.integral_mono_ae hs hintZ hintρ (by
      filter_upwards [hcL.ae_differentiableAt_real] with u hu
      exact hpt u hu)
  rw [hFTC, intervalIntegral.integral_div] at hint
  have hZ0 : Z 0 = Real.log (2 * t ^ 2) := by simp [hZdef, hYdef, minkQ]
  rw [hZ0] at hint
  have h1 : Real.log (Y s) ≤ Real.log (2 * t ^ 2) +
      (∫ u in (0 : ℝ)..s, Real.sqrt (minkQ (deriv c u))) / t := by
    change Z s ≤ _; linarith
  rw [Real.log_le_iff_le_exp (hYpos s), Real.exp_add, Real.exp_log ht2] at h1
  exact h1

/-- `S_t` as an `IsSpacelikeLipschitzIn` of `Ω⁺(Λ)` (Cosmological's fields, rewrapped, frame `1`). -/
theorem rC_isSpacelikeLipschitzIn_cosmoLevel (h : CosmoRegular Λ) {t : ℝ} (ht : 0 < t) :
    IsSpacelikeLipschitzIn h.regular.opens (cosmoLevel Λ t) := by
  obtain ⟨hsub, hach, hloc⟩ := isSpacelikeLipschitz_cosmoLevel h ht
  refine ⟨hsub, hach, fun p hp => ?_⟩
  obtain ⟨O, U, f, c, hc, hpO, hO, hU, hf, heq⟩ := hloc p hp
  refine ⟨1, O, U, f, c, hc, hpO, hO, hU, hf, ?_⟩
  rw [one_smul, one_smul]
  exact heq

/-- **Bounded length, bounded displacement** (`bcor:level_sets_complete`, l.1112–1125, in the
form "bounded subsets of `S_t` are relatively compact"): a Lipschitz curve of `S_t` over `[0,1]`
of length at most `L` moves by at most `2 e^{L/t} n₀(c 0) L`. Along it
`|c − c(0)|² ≤ 2t²(e^{L/t} − 1)` (`rC_gronwall`), so `−⟨n(c) | n(c 0)⟩ ≤ e^{L/t}` (`bprop:lip`,
chordal form), so the time component of the normal stays below `A = 2 e^{L/t} n₀(c 0)`
(`rC_fst_le_of_unit`), so the slope stays below `√(1 − 1/A²)` and `‖c'⃗‖ ≤ A √|c'|²`. -/
theorem rC_norm_sub_le (h : CosmoRegular Λ) {t : ℝ} (ht : 0 < t) {c : ℝ → Minkowski d}
    {K : ℝ≥0} (hcL : LipschitzWith K c) (hc : ∀ s, c s ∈ cosmoLevel Λ t) {L : ℝ}
    (hL : ∫ u in (0 : ℝ)..1, Real.sqrt (minkQ (deriv c u)) ≤ L) :
    ‖c 1 - c 0‖ ≤ 2 * Real.exp (L / t) * (gaussMap Λ (c 0)).1 * L := by
  set n₀ := gaussMap Λ (c 0)
  have hn₀ := isFutureTimelike_gaussMap h (hc 0).1
  have hn₀Q := minkQ_gaussMap h (hc 0).1
  set A := 2 * Real.exp (L / t) * n₀.1 with hAdef
  have hA0 : 0 ≤ A := by have := hn₀.1; positivity
  have hρint : IntervalIntegrable (fun u => Real.sqrt (minkQ (deriv c u))) volume 0 1 :=
    intervalIntegrable_of_bound (Real.continuous_sqrt.measurable.comp
      (continuous_minkQ.measurable.comp (measurable_deriv c))) K (fun u => by
        rw [Real.norm_eq_abs]
        change |Real.sqrt (minkQ (deriv c u))| ≤ _
        rw [abs_of_nonneg (Real.sqrt_nonneg _)]
        exact (sqrt_minkQ_le _).trans ((norm_snd_le _).trans (norm_deriv_le_of_lipschitz hcL)))
      0 1
  -- the normal is controlled along the curve
  have hnorm : ∀ s ∈ Icc (0 : ℝ) 1, (gaussMap Λ (c s)).1 ≤ A := fun s hs => by
    have hg := rC_gronwall h ht hcL hc hs.1
    have hIs : ∫ u in (0 : ℝ)..s, Real.sqrt (minkQ (deriv c u)) ≤ L :=
      (intervalIntegral.integral_mono_interval le_rfl hs.1 hs.2
        (Filter.Eventually.of_forall fun _ => Real.sqrt_nonneg _) hρint).trans hL
    have hexp : Real.exp ((∫ u in (0 : ℝ)..s, Real.sqrt (minkQ (deriv c u))) / t) ≤
        Real.exp (L / t) :=
      Real.exp_le_exp.2 (div_le_div_of_nonneg_right hIs ht.le)
    have hQ : minkQ (c s - c 0) ≤ 2 * t ^ 2 * (Real.exp (L / t) - 1) := by nlinarith
    have hlip := minkQ_gaussMap_sub_le h ht (hc s) (hc 0)
    set ns := gaussMap Λ (c s)
    have hns := isFutureTimelike_gaussMap h (hc s).1
    have hnsQ := minkQ_gaussMap h (hc s).1
    have hQn : minkQ (ns - n₀) ≤ 2 * (Real.exp (L / t) - 1) := by
      have : t ^ 2 * minkQ (ns - n₀) ≤ t ^ 2 * (2 * (Real.exp (L / t) - 1)) := by nlinarith
      exact le_of_mul_le_mul_left this (by positivity)
    have hB : -minkB ns n₀ ≤ Real.exp (L / t) := by
      rw [rQ_sub, hnsQ, hn₀Q] at hQn; linarith
    have := rC_fst_le_of_unit hns hnsQ hn₀ hn₀Q
    have hn01 := hn₀.1
    calc ns.1 ≤ 2 * (-minkB ns n₀) * n₀.1 := this
      _ ≤ 2 * Real.exp (L / t) * n₀.1 := by gcongr
  -- the spatial speed is controlled
  set X : ℝ → EuclideanSpace ℝ (Fin d) := fun u => (c u).2 with hXdef
  have hXL : LipschitzWith K X := by
    have := LipschitzWith.prod_snd.comp hcL
    rw [one_mul] at this
    exact this
  have hX := norm_sub_le_integral_norm_deriv hXL zero_le_one
  have hspeed : ∫ u in (0 : ℝ)..1, ‖deriv X u‖ ≤
      ∫ u in (0 : ℝ)..1, A * Real.sqrt (minkQ (deriv c u)) := by
    refine intervalIntegral.integral_mono_ae_restrict zero_le_one
      (intervalIntegrable_of_bound (measurable_deriv X).norm K
        (fun u => by rw [norm_norm]; exact norm_deriv_le_of_lipschitz hXL) 0 1)
      (hρint.const_mul A) ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae hcL.ae_differentiableAt_real] with u hu hd
    have htan := rC_minkB_deriv_eq_zero h ht hc hd
    have hsq := rC_norm_snd_sq_le (minkQ_gaussMap h (hc u).1) htan
    have hns := isFutureTimelike_gaussMap h (hc u).1
    have hQv := rC_minkQ_nonneg_of_orth hns htan
    have hnA := hnorm u hu
    rw [← snd_deriv_eq c hd]
    have h1 : ‖(deriv c u).2‖ ^ 2 ≤ (A * Real.sqrt (minkQ (deriv c u))) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hQv]
      refine hsq.trans (mul_le_mul_of_nonneg_right ?_ hQv)
      exact pow_le_pow_left₀ hns.1.le hnA 2
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hA0 (Real.sqrt_nonneg _))
      two_ne_zero).1 h1
  rw [intervalIntegral.integral_const_mul] at hspeed
  have h2 : ‖(c 1 - c 0).2‖ ≤ A * L := by
    have := hX.trans hspeed
    exact this.trans (mul_le_mul_of_nonneg_left hL hA0)
  have h3 : ‖(c 1 - c 0).1‖ ≤ ‖(c 1 - c 0).2‖ := by
    have hQ := rC_minkQ_sub_nonneg h ht (hc 0) (hc 1)
    unfold minkQ at hQ
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt (by linarith)
  rw [Prod.norm_def]
  exact max_le (h3.trans h2) h2

/-- `bcor:level_sets_complete` (l.1109–1125): every level set `S_t` of the cosmological time
is complete for its induced length. A Cauchy sequence is eventually within length `1` of one of
its terms, hence (`rC_norm_sub_le`) in a compact piece of the closed `S_t`
(`isClosed_cosmoLevel`); a subsequence converges in `𝐌ⁿ`, hence for the length
(`IsSpacelikeLipschitzIn.isHomeomorph_toSubtype`), and so does the sequence. -/
theorem cosmoLevel_completeSpace_inducedLength (h : CosmoRegular Λ) {t : ℝ} (ht : 0 < t) :
    CompleteSpace (InducedLength (cosmoLevel Λ t) h.regular.opens) := by
  set S := cosmoLevel Λ t
  set V := h.regular.opens
  have hL := rC_isSpacelikeLipschitzIn_cosmoLevel h ht
  have hhom := hL.isHomeomorph_toSubtype
  -- bounded length, bounded displacement
  have hbound : ∀ (x y : InducedLength S V) (R : ℝ), edist x y < ENNReal.ofReal R →
      ‖((InducedLength.toSubtype y : ↥(S ∩ (V : Set (Minkowski d)))) : Minkowski d) -
        (InducedLength.toSubtype x : ↥(S ∩ (V : Set (Minkowski d))))‖ ≤
        2 * Real.exp (R / t) *
          (gaussMap Λ (InducedLength.toSubtype x : ↥(S ∩ (V : Set (Minkowski d))))).1 * R := by
    intro x y R hxy
    rw [InducedLength.edist_def] at hxy
    obtain ⟨γ, hγ⟩ := iInf_lt_iff.1 hxy
    have hLip : IsLipschitzCurve γ.toContinuousMap := by
      by_contra hn
      rw [lengthOn_of_not_isLipschitzCurve hn] at hγ
      exact absurd hγ (not_lt.2 le_top)
    obtain ⟨K, hK⟩ := hLip
    rw [lengthOn_eq_integral ⟨K, hK⟩] at hγ
    set c := curveExtend γ.toContinuousMap
    have hI0 : 0 ≤ ∫ u in (0 : ℝ)..1, Real.sqrt (minkQ (deriv c u)) :=
      intervalIntegral.integral_nonneg zero_le_one fun _ _ => Real.sqrt_nonneg _
    have hIR := ((ENNReal.ofReal_lt_ofReal_iff'.1 hγ).1).le
    have hc : ∀ s, c s ∈ S := fun s => (γ.toContinuousMap (projIcc 0 1 zero_le_one s)).2.1
    have hc0 : c 0 = (InducedLength.toSubtype x : Minkowski d) := by
      simp only [c, curveExtend, IccExtend_left, Path.coe_toContinuousMap]
      exact congrArg Subtype.val γ.source
    have hc1 : c 1 = (InducedLength.toSubtype y : Minkowski d) := by
      simp only [c, curveExtend, IccExtend_right, Path.coe_toContinuousMap]
      exact congrArg Subtype.val γ.target
    have := rC_norm_sub_le h ht hK hc hIR
    rwa [hc0, hc1] at this
  refine EMetric.complete_of_cauchySeq_tendsto fun u hu => ?_
  obtain ⟨N, hN⟩ := (EMetric.cauchySeq_iff.1 hu) 1 one_pos
  set P : ℕ → Minkowski d := fun k =>
    ((InducedLength.toSubtype (u (N + k)) : ↥(S ∩ (V : Set (Minkowski d)))) : Minkowski d)
  set p₀ := P 0
  set B := 2 * Real.exp (1 / t) *
    (gaussMap Λ (InducedLength.toSubtype (u N) : ↥(S ∩ (V : Set (Minkowski d))))).1 * 1
  have hPB : ∀ k, P k ∈ S ∩ Metric.closedBall p₀ B := fun k => by
    refine ⟨(InducedLength.toSubtype (u (N + k))).2.1, ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    have := hbound (u N) (u (N + k)) 1 (by
      rw [ENNReal.ofReal_one]; exact hN (N + k) (by omega) N le_rfl |>.trans_eq' (edist_comm _ _))
    exact this
  have hK : IsCompact (S ∩ Metric.closedBall p₀ B) :=
    (isCompact_closedBall p₀ B).inter_left (isClosed_cosmoLevel h ht)
  obtain ⟨q, hqK, φ, hφ, hlim⟩ := hK.tendsto_subseq hPB
  have hqV : q ∈ (V : Set (Minkowski d)) := cosmoLevel_subset t hqK.1
  set z : InducedLength S V := InducedLength.toSubtype.symm ⟨q, hqK.1, hqV⟩
  refine ⟨z, tendsto_nhds_of_cauchySeq_of_subseq hu (f := fun k => N + φ k)
    (tendsto_atTop_mono (fun k => Nat.le_add_left (φ k) N) hφ.tendsto_atTop) ?_⟩
  have h1 : Tendsto (fun k => InducedLength.toSubtype (u (N + φ k))) atTop
      (𝓝 (⟨q, hqK.1, hqV⟩ : ↥(S ∩ (V : Set (Minkowski d))))) :=
    tendsto_subtype_rng.2 hlim
  have h2 := ((hhom.homeomorph _).symm.continuous.tendsto _).comp h1
  have hz : (hhom.homeomorph _).symm ⟨q, hqK.1, hqV⟩ = z := by
    apply (hhom.homeomorph _).injective
    rw [Homeomorph.apply_symm_apply]
    rfl
  have hf : (hhom.homeomorph _).symm ∘ (fun k => InducedLength.toSubtype (u (N + φ k))) =
      u ∘ (fun k => N + φ k) :=
    funext fun k => (hhom.homeomorph _).symm_apply_apply (u (N + φ k))
  rw [hz, hf] at h2
  exact h2

/-- **The future data**: for `Ω` with the points of `Ω⁺(Λ)`, `S₁` is a Cauchy surface of `Ω`,
spacelike Lipschitz, complete, with the length topology finer than the subspace one. -/
theorem rC_future_data (h : CosmoRegular Λ) {Ω : Opens (Minkowski d)}
    (hΩ : ∀ p, p ∈ Ω ↔ p ∈ omegaPlus Λ) :
    cosmoLevel Λ 1 ⊆ Ω ∧ (minkowski d).IsCauchySurfaceOn Ω (cosmoLevel Λ 1) ∧
      IsSpacelikeLipschitzIn Ω (cosmoLevel Λ 1) ∧
      CompleteSpace (InducedLengthSpace d (Subtype.val ⁻¹' cosmoLevel Λ 1 : Set Ω)) ∧
      Continuous fun x : InducedLengthSpace d (Subtype.val ⁻¹' cosmoLevel Λ 1 : Set Ω) =>
        (InducedLengthSpace.toSubtype x).1 := by
  obtain rfl : Ω = h.regular.opens := SetLike.ext hΩ
  have hL := rC_isSpacelikeLipschitzIn_cosmoLevel h one_pos
  exact ⟨cosmoLevel_subset 1, isCauchySurfaceOn_cosmoLevel h one_pos, hL,
    rC_complete_opens_of_inducedLength hL (cosmoLevel_completeSpace_inducedLength h one_pos)⟩

end Level

/-! ### The theorem -/

/-- **Quotients of regular domains are Cauchy-complete** (`bprop:regular_cauchy_complete`,
l.1148–1151, descended to the quotient; both time orientations). -/
theorem isCauchyComplete_of_isQuotientOf_regular {M₁ : FlatSpacetime.{u} d}
    {Λ : Set (PenroseSphere d × ℝ)} {Ω : Opens (Minkowski d)}
    (_hΩ : (CosmoRegular Λ ∧ ∀ p, p ∈ Ω ↔ p ∈ omegaPlus Λ) ∨
      (PastRegular Λ ∧ (∃ w₁ ∈ Λ, ∃ w₂ ∈ Λ, w₁.1 ≠ w₂.1) ∧ ∀ p, p ∈ Ω ↔ p ∈ omegaMinus Λ))
    (φ : isom d) {Γ : Subgroup (isom d)} (_hq : IsQuotientOf M₁ (frameConj φ Γ) (isomImage φ Ω)) :
    IsCauchyComplete d M₁ := by
  rcases _hΩ with ⟨h, hΩ⟩ | ⟨hP, htwo, hΩ⟩
  · -- the future side: `S₁ ⊆ Ω⁺(Λ)`
    obtain ⟨hsub, hC, hL, hc, ht⟩ := rC_future_data h hΩ
    have hpre : ∀ γ ∈ Γ, (fun p => γ • p) ⁻¹' omegaPlus Λ = omegaPlus Λ := fun γ hγ => by
      ext p
      rw [mem_preimage, ← hΩ, ← hΩ]
      exact rC_smul_mem_iff φ _hq hγ p
    refine rC_of_frame φ _hq hsub (fun γ hγ p hp => (smul_mem_cosmoLevel_iff (hpre γ hγ)).2 hp)
      hC hL hc ht fun γ hγ x hx hle => ?_
    by_contra hne
    have h1 := cosmoTime_lt_of_le h ((hΩ x).1 hx) hle (Ne.symm hne)
    rw [cosmoTime_smul (hpre γ hγ)] at h1
    exact lt_irrefl _ h1
  · -- the past side: `−S₁(−Λ) ⊆ Ω⁻(Λ)`
    set Λ' := negS d ⁻¹' Λ with hΛ'
    have h' : CosmoRegular Λ' := cosmoRegular_negS hP htwo
    obtain ⟨hsub', hC', hL', hc', ht'⟩ :=
      rC_future_data h' (Ω := h'.regular.opens) (fun _ => Iff.rfl)
    have hΩ' : ∀ p, p ∈ Ω ↔ -p ∈ omegaPlus Λ' := fun p => (hΩ p).trans mem_omegaMinus_iff_neg
    have hΩeq : rC_negOpens h'.regular.opens = Ω := SetLike.ext fun p => by
      rw [rC_mem_negOpens, hΩ']; rfl
    set S : Set (Minkowski d) := (fun p => -p) '' cosmoLevel Λ' 1 with hS
    have hmemS : ∀ q, q ∈ S ↔ -q ∈ cosmoLevel Λ' 1 := fun q => rC_mem_neg_image
    have hsub : S ⊆ Ω := fun q hq => (hΩ' q).2 (cosmoLevel_subset 1 ((hmemS q).1 hq))
    have hC : (minkowski d).IsCauchySurfaceOn Ω S := by
      rw [← hΩeq]; exact rC_isCauchySurfaceOn_neg hsub' hC'
    have hL : IsSpacelikeLipschitzIn Ω S := by
      rw [← hΩeq]; exact rC_isSpacelikeLipschitzIn_neg hL'
    have hmem : ∀ p, (p ∈ h'.regular.opens ∧ p ∈ cosmoLevel Λ' 1) ↔
        ((ContinuousLinearEquiv.neg ℝ : Minkowski d ≃L[ℝ] Minkowski d) p + 0 ∈ Ω ∧
          (ContinuousLinearEquiv.neg ℝ : Minkowski d ≃L[ℝ] Minkowski d) p + 0 ∈ S) := fun p => by
      change _ ↔ (-p + 0 ∈ Ω ∧ -p + 0 ∈ S)
      rw [add_zero, hΩ', hmemS, neg_neg]
      exact Iff.rfl
    obtain ⟨hc, ht⟩ := rC_transfer _ (fun v => minkQ_neg v) 0 hmem hc' ht'
    -- `σγσ` preserves `Ω⁺(Λ')` for `γ ∈ Γ`
    have hpre : ∀ γ ∈ Γ, (fun p => negConj γ • p) ⁻¹' omegaPlus Λ' = omegaPlus Λ' :=
      fun γ hγ => by
        ext p
        rw [mem_preimage, negConj_smul, ← hΩ', ← neg_neg p, ← hΩ', neg_neg]
        exact rC_smul_mem_iff φ _hq hγ (-p)
    refine rC_of_frame φ _hq hsub (fun γ hγ p hp => ?_) hC hL hc ht fun γ hγ x hx hle => ?_
    · rw [hmemS] at hp ⊢
      have : -(γ • p) = negConj γ • -p := by rw [negConj_smul, neg_neg]
      rw [this]
      exact (smul_mem_cosmoLevel_iff (hpre γ hγ)).2 hp
    · by_contra hne
      have hy : -x ∈ omegaPlus Λ' := (hΩ' x).1 hx
      have hle' : (minkowski d).le ⊤ (negConj γ • -x) (-x) := by
        rw [negConj_smul, neg_neg]; exact rC_le_top_neg hle
      have hne' : negConj γ • -x ≠ -x := by
        rw [negConj_smul, neg_neg, Ne, neg_inj]; exact hne
      have hy' : negConj γ • -x ∈ omegaPlus Λ' := by
        rw [← mem_preimage (f := fun p => negConj γ • p), hpre γ hγ]; exact hy
      have h1 := cosmoTime_lt_of_le h' hy' hle' hne'
      rw [cosmoTime_smul (hpre γ hγ)] at h1
      exact lt_irrefl _ h1

end Causal.Flat.Cla
