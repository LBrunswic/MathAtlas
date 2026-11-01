import CausalScaffold.Flat.Nonloxodromic
import CausalScaffold.Flat.TitsNull
import CausalScaffold.Flat.Loxodromic
import CausalScaffold.CompactCauchy
import CausalScaffold.CurvesExtend

/-!
# `CausalScaffold.Flat.Cla.CompactComplete` — a Cauchy-compact GH flat spacetime is Cauchy-complete

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §2.4 and
§11. **No label is marked**: the theorem rests on one tagged `sorry` (the smoothing step, SCOPE).
Cited UNMARKED: `bthm:cauclo` — `GHFspace.tex:353` (Theorem B, l.352–360), whose proof (l.3536)
feeds Theorem A a Cauchy-compact `M`, which must therefore be Cauchy-complete; `[2.4]`
Cauchy-complete — l.551–553 (prose, DEC-35, a reading); Cauchy-compact — l.560–565 (prose,
`FlatSpacetime.CauchyCompact`'s topological reading). Serves
`Classification.isCauchyComplete_of_cauchyCompact` (`Flat/Classification.lean:2429`), which closes
by `obtain ⟨S, hS, hSc, hac⟩ := _hC; exact isCauchyComplete_of_isCompact_cauchy M _hGH hS hSc hac`
(tested at the end of this file).

> A GH spacetime is *Cauchy-complete* if it admits a Cauchy hypersurface where the ambiant
> lorentzian metric restricts as a complete riemanian metric. (l.551–553)

> Among Cauchy-complete spacetimes, there is a remarkable natural family: GH spacetimes with
> *closed* Cauchy hypersurfaces (we know that in general, if a spacetime admits a closed Cauchy
> hypersurface, then all its Cauchy surfaces are closed - indeed, they are homeomorphic one to the
> other). We call such a spacetime *Cauchy-compact* GH spacetime (abbreviation CGH).
> (l.560–565)

> Reconsider the proof above when $M$ is assumed Cauchy-compact. (l.3536)

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; `Minkowski d` has `d` spatial
dimensions, so Barbot's `n` is `d + 1`.

## Main declarations
* `isCauchyComplete_of_isCompact_cauchy` — GH, a compact acausal Cauchy surface ⇒
  `IsCauchyComplete d M`. Assembled (no `sorry` of its own) from:
* `exists_isSpacelikeLipschitz_cauchy_of_isCompact` — **the one `sorry`** of the module
  (`SORRY(bthm:cauclo, compact ⇒ complete, smoothing)`): a compact spacelike Lipschitz Cauchy
  surface from a compact acausal topological one.
* PROVED, for any `S ⊆ M`, `M` charted over `𝐌ⁿ` with the `(Isom(𝐌ⁿ), 𝐌ⁿ)` groupoid — the gluing
  of `IsSpacelikeLipschitzIn.isHomeomorph_toSubtype` over charts that `CauchyComplete`'s SCOPE
  left open:
  - `continuous_inducedLengthSpace_toSubtype_symm` (`IsSpacelikeLipschitz d S`): the subspace
    topology is finer than the glued length topology;
  - `continuous_inducedLengthSpace_toSubtype` (`T2Space M`): the glued length topology is finer
    than the topology of `M` — exactly `IsCauchyComplete`'s topology field — by a first-exit
    argument in the chart at the point;
  - `completeSpace_inducedLengthSpace_of_isCompact`: a COMPACT spacelike Lipschitz `S` is complete
    for its glued length (the length space is a continuous image of the compact `S`).
  - The chart transport they rest on: `localLength_chartSys_eq_lorentzLength` (glued length =
    Lorentzian length in one chart), `exists_lipschitzOnWith_chart` / `isLocLip_of_chart`
    (Lipschitz in charts ⇔ Lipschitz in one chart, on a compact interval), `chartPt`,
    `edist_le_edist_chart` (chart-image paths are paths of `S`, no longer), and
    `edist_chart_le_pathLength` (an initial piece of a path of `S` staying in a chart is a path
    of the chart image, no longer).

## Hypothesis checklist
| paper hypothesis | here |
|---|---|
| `M` GH | ✓ carried (`GH M`, ETT's reading); used only by the smoothing step (the `sorry`) |
| `M` Cauchy-compact ("closed Cauchy hypersurfaces", l.560–565) | ✓ carried in `CauchyCompact`'s topological reading: `S` Cauchy, compact, acausal |
| "the ambiant lorentzian metric restricts as a complete riemanian metric" (l.551–553) | ⚠ read (DEC-35): `IsCauchyComplete` — a spacelike Lipschitz Cauchy surface, `CompleteSpace` of its glued length, and the topology field |
| compact ⇒ complete (implicit, l.560 "Among Cauchy-complete spacetimes") | ✓ proved for a compact spacelike Lipschitz surface, with no second countability and no Hausdorff hypothesis beyond `M`'s |

## SCOPE (disclosed)
* **The smoothing step is not proved** (`exists_isSpacelikeLipschitz_cauchy_of_isCompact`, one
  tagged `sorry`). A topological acausal Cauchy surface is only achronal, i.e. 1-Lipschitz in flat
  charts, with no slope bound `c < 1`; `IsSpacelikeLipschitz` asks one at every point. Bernal–Sánchez
  is avoided in the plan (local mollification over a finite chart cover of the compact `S`, then
  a push to the future), but the library lacks every ingredient: the local graph form of a
  topological Cauchy surface on a chart ball (LipschitzGraph's domain-of-dependence lemmas are for
  entire graphs), the gluing of the mollified pieces across tilted frames, and the Cauchy property
  of the result. The obstruction is stated in full at the `sorry`. Everything downstream of it is
  proved, and the statement of the theorem is the dispatched one, unchanged.
* The compactness of the smoothed surface is part of the `sorry`'d construction (it lies in the
  compact slab between `S` and its push), not derived from "all Cauchy surfaces are homeomorphic"
  (l.562–563, not in the library).
* Completeness is proved through compactness of the length space, not by a Cauchy-sequence
  argument; the topology field through `IsSpacelikeLipschitzIn.continuous_toSubtype` in the chart
  at each point plus a first-exit time, with the chart piece over a closed ball compact, hence
  closed in the Hausdorff `M`.
* Namespace `Causal.Flat.Cla`; no file of `Flat/Lox/` or `Flat/Nonlox/` is imported directly.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Written for the
Barbot campaign (Cla round), as the prover of `Classification`'s `isCauchyComplete_of_cauchyCompact`.
-/

namespace Causal.Flat.Cla

open Set TopologicalSpace Filter Topology MeasureTheory
open scoped ENNReal NNReal unitInterval

universe u

variable {d : ℕ}

section Chart

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Minkowski d) M]
  [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))] {S : Set M}

/-- **The glued length is the Lorentzian length in one chart**, on an interval where the curve
stays in the chart's source (`localDensity_chartSys_eq`, point by point). -/
theorem localLength_chartSys_eq_lorentzLength {c : ℝ → S} (hc : Continuous c)
    {e : OpenPartialHomeomorph M (Minkowski d)} (he : e ∈ atlas (Minkowski d) M) {a b : ℝ}
    (hsrc : ∀ s ∈ Ioc a b, (c s : M) ∈ e.source) :
    localLength (chartSys d S) c a b = lorentzLength (fun s => e (c s : M)) a b :=
  setLIntegral_congr_fun measurableSet_Ioc fun s hs =>
    localDensity_chartSys_eq hc.continuousAt he (hsrc s hs)

/-- **Lipschitz in charts ⇒ Lipschitz in one chart**, on a compact interval mapped into its
source: near each time the chart at the point and `e` differ by an element of `Isom(𝐌ⁿ)`. -/
theorem exists_lipschitzOnWith_chart {c : ℝ → S} (hc : Continuous c)
    (hL : IsLocLip (chartSys d S) c) {e : OpenPartialHomeomorph M (Minkowski d)}
    (he : e ∈ atlas (Minkowski d) M) {a b : ℝ} (hsrc : ∀ s ∈ Icc a b, (c s : M) ∈ e.source) :
    ∃ K : ℝ≥0, LipschitzOnWith K (fun s => e (c s : M)) (Icc a b) := by
  refine LocallyLipschitzOn.exists_lipschitzOnWith_of_compact isCompact_Icc fun t ht => ?_
  obtain ⟨g, O, htO, -, heq⟩ := exists_smul_eq_of_mem_gxGroupoid
    ((gxGroupoid (isom d) (Minkowski d)).compatible (chart_mem_atlas (Minkowski d) (c t : M)) he)
    (mem_chart_source _ (c t : M)) (hsrc t ht)
  obtain ⟨ε, hε, K, hK⟩ := hL t
  have hcont : Continuous fun s => (c s : M) := continuous_subtype_val.comp hc
  obtain ⟨δ, hδ, hδO⟩ := exists_Icc_subset_of_eventually
    (hcont.continuousAt.eventually_mem (O.isOpen.mem_nhds htO))
  obtain ⟨Kg, hKg⟩ := isom_lipschitzWith g
  set η := min ε δ
  have hη : 0 < η := lt_min hε hδ
  have hsub : Icc (t - η) (t + η) ⊆ Icc (t - ε) (t + ε) :=
    Icc_subset_Icc (by linarith [min_le_left ε δ]) (by linarith [min_le_left ε δ])
  have hsubδ : Icc (t - η) (t + η) ⊆ Icc (t - δ) (t + δ) :=
    Icc_subset_Icc (by linarith [min_le_right ε δ]) (by linarith [min_le_right ε δ])
  refine ⟨Kg * K, Icc (t - η) (t + η),
    mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds (by linarith) (by linarith)), ?_⟩
  have h1 := hKg.comp_lipschitzOnWith (hK.mono hsub)
  exact lipschitzOnWith_congr_of_eqOn (fun s hs => (heq _ (hδO s (hsubδ hs))).symm) h1

/-- **Lipschitz in one chart ⇒ Lipschitz in charts.** -/
theorem isLocLip_of_chart {c : ℝ → S} (hc : Continuous c)
    {e : OpenPartialHomeomorph M (Minkowski d)} (he : e ∈ atlas (Minkowski d) M)
    (hsrc : ∀ s, (c s : M) ∈ e.source) {K : ℝ≥0} (hK : LipschitzWith K fun s => e (c s : M)) :
    IsLocLip (chartSys d S) c := by
  intro t
  obtain ⟨g, O, htO, -, heq⟩ := exists_smul_eq_of_mem_gxGroupoid
    ((gxGroupoid (isom d) (Minkowski d)).compatible he (chart_mem_atlas (Minkowski d) (c t : M)))
    (hsrc t) (mem_chart_source _ (c t : M))
  have hcont : Continuous fun s => (c s : M) := continuous_subtype_val.comp hc
  obtain ⟨δ, hδ, hδO⟩ := exists_Icc_subset_of_eventually
    (hcont.continuousAt.eventually_mem (O.isOpen.mem_nhds htO))
  obtain ⟨Kg, hKg⟩ := isom_lipschitzWith g
  exact ⟨δ, hδ, Kg * K, lipschitzOnWith_congr_of_eqOn (fun s hs => (heq _ (hδO s hs)).symm)
    (hKg.comp hK).lipschitzOnWith⟩

/-- A point of `S` in the source of `e`, read in `e`, as a point of the chart image
`T = e(S ∩ e.source) ∩ V` (the set `IsSpacelikeLipschitz` controls), in `T ∩ V`. -/
def chartPt (e : OpenPartialHomeomorph M (Minkowski d)) (V : Opens (Minkowski d)) (y : S)
    (hy : (y : M) ∈ e.source) (hyV : e y ∈ (V : Set (Minkowski d))) :
    ↥((e '' (S ∩ e.source) ∩ (V : Set (Minkowski d))) ∩ (V : Set (Minkowski d))) :=
  ⟨e y, ⟨⟨y, ⟨y.2, hy⟩, rfl⟩, hyV⟩, hyV⟩

/-- **Chart paths are paths of `S`**: the glued distance of two points of `S` read in a chart is
at most their induced distance in the chart image (map a Lipschitz path of the image back by
`e.symm`; its glued length is its Lorentzian length). -/
theorem edist_le_edist_chart {e : OpenPartialHomeomorph M (Minkowski d)}
    (he : e ∈ atlas (Minkowski d) M) {V : Opens (Minkowski d)}
    (hV : (V : Set (Minkowski d)) ⊆ e.target) (y z : S) (hy : (y : M) ∈ e.source)
    (hyV : e y ∈ (V : Set (Minkowski d))) (hz : (z : M) ∈ e.source)
    (hzV : e z ∈ (V : Set (Minkowski d))) :
    edist (InducedLengthSpace.toSubtype.symm y : InducedLengthSpace d S)
        (InducedLengthSpace.toSubtype.symm z) ≤
      edist (InducedLength.toSubtype.symm (chartPt e V y hy hyV) :
          InducedLength (e '' (S ∩ e.source) ∩ (V : Set (Minkowski d))) V)
        (InducedLength.toSubtype.symm (chartPt e V z hz hzV)) := by
  rw [InducedLength.edist_def]
  refine le_iInf fun β => ?_
  by_cases hβ : IsLipschitzCurve β.toContinuousMap
  swap
  · rw [lengthOn_of_not_isLipschitzCurve hβ]; exact le_top
  have hmem : ∀ u, e.symm (β u : Minkowski d) ∈ S := fun u => by
    obtain ⟨⟨w, ⟨hwS, hws⟩, hw⟩, -⟩ := (β u).2.1
    rw [← hw, e.left_inv hws]; exact hwS
  let γ : Path y z :=
    { toFun := fun u => ⟨e.symm (β u : Minkowski d), hmem u⟩
      continuous_toFun := (e.continuousOn_symm.comp_continuous
        (continuous_subtype_val.comp β.continuous) fun u => hV (β u).2.2).subtype_mk _
      source' := Subtype.ext (by
        show e.symm (β 0 : Minkowski d) = y
        rw [β.source]; exact e.left_inv hy)
      target' := Subtype.ext (by
        show e.symm (β 1 : Minkowski d) = z
        rw [β.target]; exact e.left_inv hz) }
  have hsrc : ∀ s, (γ.extend s : M) ∈ e.source := fun s => e.map_target (hV (β _).2.2)
  have hcomp : (fun s => e (γ.extend s : M)) = curveExtend β.toContinuousMap :=
    funext fun s => e.right_inv (hV (β _).2.2)
  obtain ⟨K, hK⟩ := hβ
  have hLoc : IsLocLip (chartSys d S) γ.extend :=
    isLocLip_of_chart γ.continuous_extend he hsrc (K := K) (by rw [hcomp]; exact hK)
  calc edist (InducedLengthSpace.toSubtype.symm y : InducedLengthSpace d S)
        (InducedLengthSpace.toSubtype.symm z)
      ≤ pathLength (chartSys d S) γ := iInf_le (fun γ : Path y z => pathLength (chartSys d S) γ) γ
    _ = localLength (chartSys d S) γ.extend 0 1 := pathLength_of_isLocLip _ hLoc
    _ = lorentzLength (fun s => e (γ.extend s : M)) 0 1 :=
        localLength_chartSys_eq_lorentzLength γ.continuous_extend he fun s _ => hsrc s
    _ = lengthOn _ V β.toContinuousMap := by rw [hcomp, lengthOn_of_isLipschitzCurve ⟨K, hK⟩]

/-- **The subspace topology is finer than the glued length topology**, for a spacelike Lipschitz
`S` (`IsLipschitzHypersurfaceIn.continuous_toSubtype_symm` in the chart at each point, through
`edist_le_edist_chart`). -/
theorem continuous_inducedLengthSpace_toSubtype_symm (hL : IsSpacelikeLipschitz d S) :
    Continuous ⇑(InducedLengthSpace.toSubtype (d := d) (S := S)).symm := by
  refine continuous_iff_continuousAt.2 fun y => ?_
  rw [ContinuousAt, EMetric.tendsto_nhds]
  intro ε hε
  set e := chartAt (Minkowski d) (y : M)
  have he : e ∈ atlas (Minkowski d) M := chart_mem_atlas _ _
  have hy : (y : M) ∈ e.source := mem_chart_source _ _
  obtain ⟨V, hyV, hVt, hT⟩ := hL y y.2
  have hc := hT.toIsLipschitzHypersurfaceIn.continuous_toSubtype_symm
  have h1 := (EMetric.tendsto_nhds.1 (hc.continuousAt (x := chartPt e V y hy hyV))) ε hε
  obtain ⟨u, hu, hus⟩ := (mem_nhds_subtype _ _ _).1 h1
  have hN : (fun z : S => (z : M)) ⁻¹' (e.source ∩ e ⁻¹' ((V : Set (Minkowski d)) ∩ u)) ∈ 𝓝 y :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds
      (inter_mem (e.open_source.mem_nhds hy) ((e.continuousAt hy).preimage_mem_nhds
        (inter_mem (V.isOpen.mem_nhds hyV) hu)))
  filter_upwards [hN] with z ⟨hz, hzV, hzu⟩
  exact (edist_le_edist_chart he hVt z y hz hzV hy hyV).trans_lt
    (hus (show chartPt e V z hz hzV ∈ Subtype.val ⁻¹' u from hzu))

/-- **A short initial piece of a path of `S`, read in a chart, is a short path of the chart
image**: if `γ` stays in `e.source` with `e ∘ γ` in `V` on `[0, t]`, the induced distance in the
chart image from `e(γ 0)` to `e(γ t)` is at most the glued length of `γ`. -/
theorem edist_chart_le_pathLength {e : OpenPartialHomeomorph M (Minkowski d)}
    (he : e ∈ atlas (Minkowski d) M) {V : Opens (Minkowski d)} {y z : S} (γ : Path y z)
    (hLoc : IsLocLip (chartSys d S) γ.extend) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hy : (y : M) ∈ e.source) (hyV : e y ∈ (V : Set (Minkowski d)))
    (hin : ∀ s ∈ Icc 0 t, (γ.extend s : M) ∈ e.source ∧ e (γ.extend s : M) ∈ (V : Set (Minkowski d))) :
    edist (InducedLength.toSubtype.symm (chartPt e V y hy hyV) :
          InducedLength (e '' (S ∩ e.source) ∩ (V : Set (Minkowski d))) V)
        (InducedLength.toSubtype.symm (chartPt e V (γ.extend t)
          (hin t ⟨ht0.le, le_rfl⟩).1 (hin t ⟨ht0.le, le_rfl⟩).2)) ≤
      pathLength (chartSys d S) γ := by
  have hI : ∀ u : I, t * (u : ℝ) ∈ Icc 0 t := fun u =>
    ⟨mul_nonneg ht0.le u.2.1, mul_le_of_le_one_right ht0.le u.2.2⟩
  have hcont : Continuous fun u : I => (γ.extend (t * u) : M) :=
    continuous_subtype_val.comp (γ.continuous_extend.comp (continuous_const.mul continuous_subtype_val))
  let β : Path (InducedLength.toSubtype (InducedLength.toSubtype.symm (chartPt e V y hy hyV) :
        InducedLength (e '' (S ∩ e.source) ∩ (V : Set (Minkowski d))) V))
      (InducedLength.toSubtype (InducedLength.toSubtype.symm (chartPt e V (γ.extend t)
        (hin t ⟨ht0.le, le_rfl⟩).1 (hin t ⟨ht0.le, le_rfl⟩).2) :
        InducedLength (e '' (S ∩ e.source) ∩ (V : Set (Minkowski d))) V)) :=
    { toFun := fun u => chartPt e V (γ.extend (t * u)) (hin _ (hI u)).1 (hin _ (hI u)).2
      continuous_toFun := (e.continuousOn.comp_continuous hcont fun u => (hin _ (hI u)).1).subtype_mk _
      source' := Subtype.ext (by
        show e (γ.extend (t * ((0 : I) : ℝ)) : M) = e y
        simp)
      target' := Subtype.ext (by
        show e (γ.extend (t * ((1 : I) : ℝ)) : M) = e (γ.extend t : M)
        simp) }
  obtain ⟨K, hK⟩ := exists_lipschitzOnWith_chart γ.continuous_extend hLoc he
    (a := 0) (b := t) fun s hs => (hin s hs).1
  set h : ℝ → ℝ := fun u => t * (projIcc (0 : ℝ) 1 zero_le_one u : ℝ)
  have hh : LipschitzWith 1 h := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul, ← mul_sub, abs_mul,
      abs_of_nonneg ht0.le]
    calc t * |(projIcc (0 : ℝ) 1 zero_le_one a : ℝ) - projIcc 0 1 zero_le_one b|
        ≤ 1 * |a - b| := mul_le_mul ht1 (abs_projIcc_sub_projIcc _) (abs_nonneg _) zero_le_one
      _ = |a - b| := one_mul _
  have hmaps : MapsTo h univ (Icc 0 t) := fun r _ => hI (projIcc 0 1 zero_le_one r)
  have hβext : curveExtend β.toContinuousMap = (fun s => e (γ.extend s : M)) ∘ h := rfl
  have hLipβ : IsLipschitzCurve β.toContinuousMap := by
    refine ⟨K * 1, ?_⟩
    have := hK.comp hh.lipschitzOnWith hmaps
    rw [lipschitzOnWith_univ] at this
    rw [hβext]; exact this
  refine (InducedLength.edist_le_lengthOn _ _ β).trans ?_
  rw [lengthOn_of_isLipschitzCurve hLipβ]
  have h1 : lorentzLength (curveExtend β.toContinuousMap) 0 1 =
      lorentzLength (fun r => e (γ.extend (t * r + 0) : M)) 0 1 :=
    lorentzLength_congr fun r hr => by
      rw [hβext]
      simp only [Function.comp_apply, h, add_zero, projIcc_of_mem zero_le_one ⟨hr.1.le, hr.2.le⟩]
  rw [h1, lorentzLength_comp_affine (fun s => e (γ.extend s : M)) ht0 0 0 1, mul_zero, add_zero,
    mul_one, add_zero, ← localLength_chartSys_eq_lorentzLength γ.continuous_extend he
      fun s hs => (hin s ⟨hs.1.le, hs.2⟩).1, pathLength_of_isLocLip _ hLoc]
  exact lintegral_mono_set (Ioc_subset_Ioc_right ht1)

/-- **The glued length topology is finer than the topology of `M`**, for a spacelike Lipschitz
`S` in a Hausdorff `M` (the topology field of `IsCauchyComplete`). A path of glued length `< δ`
from `y` cannot leave the chart piece over the ball `B(e y, r)`: up to its first exit time it is a
short path of the chart image (`edist_chart_le_pathLength`), hence stays in `B(e y, r/2)`
(`IsSpacelikeLipschitzIn.continuous_toSubtype` in the chart), and the piece over the closed ball
is compact, hence closed. -/
theorem continuous_inducedLengthSpace_toSubtype [T2Space M] (hL : IsSpacelikeLipschitz d S) :
    Continuous fun x : InducedLengthSpace d S => (InducedLengthSpace.toSubtype x : M) := by
  refine continuous_iff_continuousAt.2 fun y => ?_
  rw [ContinuousAt, Filter.tendsto_def]
  intro N hN
  set y' : S := InducedLengthSpace.toSubtype y with hy'def
  set e := chartAt (Minkowski d) (y' : M)
  have he : e ∈ atlas (Minkowski d) M := chart_mem_atlas _ _
  have hy : (y' : M) ∈ e.source := mem_chart_source _ _
  obtain ⟨V, hyV, hVt, hT⟩ := hL y' y'.2
  have hN' : (V : Set (Minkowski d)) ∩ (e.target ∩ e.symm ⁻¹' N) ∈ 𝓝 (e y') := by
    refine inter_mem (V.isOpen.mem_nhds hyV) (inter_mem (e.open_target.mem_nhds (e.map_source hy)) ?_)
    have : N ∈ Filter.map e.symm (𝓝 (e y')) := by rw [e.symm_map_nhds_eq hy]; exact hN
    exact this
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hN'
  set p₀ := chartPt e V y' hy hyV
  have hW : {q : ↥((e '' (S ∩ e.source) ∩ (V : Set (Minkowski d))) ∩ (V : Set (Minkowski d))) |
      (q : Minkowski d) ∈ Metric.ball (e y') (r / 2)} ∈ 𝓝 p₀ :=
    (Metric.isOpen_ball.preimage continuous_subtype_val).mem_nhds
      (Metric.mem_ball_self (half_pos hr))
  have hc := hT.continuous_toSubtype.continuousAt (x := InducedLength.toSubtype.symm p₀)
  have hpre := hc.preimage_mem_nhds (by rw [Equiv.apply_symm_apply]; exact hW)
  obtain ⟨δ, hδ, hδW⟩ := EMetric.mem_nhds_iff.1 hpre
  rw [EMetric.mem_nhds_iff]
  refine ⟨δ, hδ, fun z hz => ?_⟩
  have hz' : edist y z < δ := by rw [edist_comm]; exact hz
  obtain ⟨γ, hγ⟩ := iInf_lt_iff.1
    (show (⨅ γ : Path y' (InducedLengthSpace.toSubtype z), pathLength (chartSys d S) γ) < δ
      from hz')
  have hLoc : IsLocLip (chartSys d S) γ.extend := by
    by_contra hn; rw [pathLength_of_not_isLocLip _ hn] at hγ; exact not_top_lt hγ
  set G : Set M := {m | m ∈ e.source ∧ e m ∈ Metric.ball (e y') r}
  set A : Set ℝ := {t | t ∈ Icc (0 : ℝ) 1 ∧ ∀ s ∈ Icc 0 t, (γ.extend s : M) ∈ G}
  have hkey : ∀ t ∈ A, e (γ.extend t : M) ∈ Metric.ball (e y') (r / 2) := by
    intro t ht
    rcases ht.1.1.eq_or_lt with h0 | hpos
    · rw [← h0, Path.extend_zero]; exact Metric.mem_ball_self (half_pos hr)
    · have hin : ∀ s ∈ Icc 0 t, (γ.extend s : M) ∈ e.source ∧
          e (γ.extend s : M) ∈ (V : Set (Minkowski d)) :=
        fun s hs => ⟨(ht.2 s hs).1, (hball (ht.2 s hs).2).1⟩
      have hle := edist_chart_le_pathLength he γ hLoc hpos ht.1.2 hy hyV hin
      exact hδW (show _ ∈ Metric.eball _ δ by
        rw [Metric.mem_eball, edist_comm]; exact hle.trans_lt hγ)
  set Kc : Set M := e.symm '' Metric.closedBall (e y') (r / 2)
  have hcb : Metric.closedBall (e y') (r / 2) ⊆ Metric.ball (e y') r :=
    Metric.closedBall_subset_ball (half_lt_self hr)
  have hKc : IsClosed Kc := ((isCompact_closedBall _ _).image_of_continuousOn
    (e.continuousOn_symm.mono fun w hw => (hball (hcb hw)).2.1)).isClosed
  have hcont : Continuous fun s => (γ.extend s : M) :=
    continuous_subtype_val.comp γ.continuous_extend
  have h0A : (0 : ℝ) ∈ A := ⟨⟨le_rfl, zero_le_one⟩, fun s hs => by
    rw [show s = 0 from le_antisymm hs.2 hs.1, Path.extend_zero]
    exact ⟨hy, Metric.mem_ball_self hr⟩⟩
  have hAne : A.Nonempty := ⟨0, h0A⟩
  have hAbdd : BddAbove A := ⟨1, fun t ht => ht.1.2⟩
  set τ := sSup A
  have hτ0 : 0 ≤ τ := le_csSup hAbdd h0A
  have hτ1 : τ ≤ 1 := csSup_le hAne fun t ht => ht.1.2
  have hdown : ∀ t ∈ A, ∀ s ∈ Icc (0 : ℝ) t, s ∈ A := fun t ht s hs =>
    ⟨⟨hs.1, hs.2.trans ht.1.2⟩, fun s' hs' => ht.2 s' ⟨hs'.1, hs'.2.trans hs.2⟩⟩
  have hB : ∀ s ∈ Ico (0 : ℝ) τ, s ∈ A := fun s hs => by
    obtain ⟨t, ht, hst⟩ := exists_lt_of_lt_csSup hAne hs.2
    exact hdown t ht s ⟨hs.1, hst.le⟩
  have hAK : ∀ s ∈ A, (γ.extend s : M) ∈ Kc := fun s hs =>
    ⟨e (γ.extend s : M), Metric.ball_subset_closedBall (hkey s hs),
      e.left_inv (hs.2 s ⟨hs.1.1, le_rfl⟩).1⟩
  have hC : (γ.extend τ : M) ∈ G := by
    rcases hτ0.eq_or_lt with h0 | hpos
    · rw [← h0, Path.extend_zero]; exact ⟨hy, Metric.mem_ball_self hr⟩
    have hmemK : (γ.extend τ : M) ∈ Kc := by
      have hcl : τ ∈ closure (Ico 0 τ) := by rw [closure_Ico hpos.ne]; exact ⟨hτ0, le_rfl⟩
      have := mem_closure_image (f := fun s => (γ.extend s : M)) hcont.continuousAt hcl
      refine closure_minimal ?_ hKc this
      rintro _ ⟨s, hs, rfl⟩; exact hAK s (hB s hs)
    obtain ⟨w, hw, hwγ⟩ := hmemK
    have hwt : w ∈ e.target := (hball (hcb hw)).2.1
    refine ⟨hwγ ▸ e.map_target hwt, ?_⟩
    rw [← hwγ, e.right_inv hwt]; exact hcb hw
  have hτA : τ ∈ A := ⟨⟨hτ0, hτ1⟩, fun s hs => by
    rcases hs.2.lt_or_eq with hlt | heq
    · exact (hB s ⟨hs.1, hlt⟩).2 s ⟨hs.1, le_rfl⟩
    · rw [heq]; exact hC⟩
  have hGo : IsOpen G := e.isOpen_inter_preimage Metric.isOpen_ball
  have hτeq : τ = 1 := by
    by_contra hne
    have hlt : τ < 1 := lt_of_le_of_ne hτ1 hne
    obtain ⟨η, hη, hηG⟩ := Metric.isOpen_iff.1 (hGo.preimage hcont) τ hC
    set t' := min 1 (τ + η / 2)
    have ht' : t' ∈ A := ⟨⟨hτ0.trans (le_min hτ1 (by linarith)), min_le_left _ _⟩,
      fun s hs => by
        rcases le_or_gt s τ with hsτ | hsτ
        · exact hτA.2 s ⟨hs.1, hsτ⟩
        · refine hηG (Metric.mem_ball.2 ?_)
          rw [Real.dist_eq, abs_of_pos (by linarith)]
          linarith [hs.2.trans (min_le_right _ _)]⟩
    have := le_csSup hAbdd ht'
    have : τ < t' := lt_min hlt (by linarith)
    linarith
  have h1A : (1 : ℝ) ∈ A := hτeq ▸ hτA
  have h1 := hkey 1 h1A
  have hsrc1 : (γ.extend 1 : M) ∈ e.source := (h1A.2 1 ⟨zero_le_one, le_rfl⟩).1
  have hmemN := (hball (Metric.ball_subset_ball (half_le_self hr.le) h1)).2.2
  rw [mem_preimage, e.left_inv hsrc1, Path.extend_one] at hmemN
  exact hmemN

/-- **A compact spacelike Lipschitz hypersurface is complete for its glued length**: the length
space is the continuous image of the compact `S` (`continuous_inducedLengthSpace_toSubtype_symm`),
hence compact, hence complete. -/
theorem completeSpace_inducedLengthSpace_of_isCompact (hSc : IsCompact S)
    (hL : IsSpacelikeLipschitz d S) : CompleteSpace (InducedLengthSpace d S) := by
  haveI : CompactSpace S := isCompact_iff_compactSpace.1 hSc
  haveI : CompactSpace (InducedLengthSpace d S) :=
    Function.Surjective.compactSpace (continuous_inducedLengthSpace_toSubtype_symm hL)
      (InducedLengthSpace.toSubtype (d := d) (S := S)).symm.surjective
  infer_instance

end Chart

/-! ### The spacelike Cauchy surface, and the theorem -/

/-- **A compact spacelike Lipschitz Cauchy surface from a compact acausal topological one** (the
step `CauchyCompact`'s topological reading leaves to `IsCauchyComplete`'s metric one). Carried as a
tagged `sorry`: it is the one assertion of this module that is not proved. -/
theorem exists_isSpacelikeLipschitz_cauchy_of_isCompact (M : FlatSpacetime.{u} d) (_hGH : GH M)
    {S : Set M} (_hS : (flatCausality d M).IsCauchySurface S) (_hSc : IsCompact S)
    (_hac : (flatCausality d M).IsAcausal S) :
    ∃ S' : Set M, (flatCausality d M).IsCauchySurface S' ∧ IsCompact S' ∧
      IsSpacelikeLipschitz d S' := by
  sorry -- SORRY(bthm:cauclo, compact ⇒ complete, smoothing): a compact acausal TOPOLOGICAL Cauchy surface `S` is only achronal, hence 1-Lipschitz in flat charts, with no slope bound `c < 1`; `IsSpacelikeLipschitz` asks one at every point. Missing: (a) the local smoothing — over a finite cover of the compact `S` by flat charts in which `S` is a 1-Lipschitz graph over a ball (achronal ⇒ 1-Lipschitz graph in a chart needs `S` to meet every timelike segment of a chart box exactly once, i.e. the local Cauchy property of `S` in a small domain of dependence; the library has `Achronal.isAchronal_graph_iff` and `LipschitzGraph.graph_subset_interior_dependenceDomain` for ENTIRE graphs only), glue `f_i + ε` mollified with a partition of unity of `S` subordinate to the cover and pushed to the future, and prove that the result is ONE achronal hypersurface (the glued graphs agree on overlaps only after the transition isometries, which tilt the frames, so the partition of unity must be taken on `S`, not on the chart bases); (b) that it is still a Cauchy surface of `M` (every inextensible causal curve crosses the thin slab `J⁺(S) ∩ J⁻(S_ε)` once; needs the closedness of `J^±(S)` and the compact diamonds `J⁺(S) ∩ J⁻(S_ε)` of GH); (c) its compactness, as a closed subset of that compact slab. The global alternative, a level set of a Cauchy time function made uniformly spacelike in charts (Bernal–Sánchez; or Barbot's cosmological time, available only for regular domains of `𝐌ⁿ`, `Flat.Cosmological`), is not in the library either: the splitting `S × ℝ ≃ₜ M` of `CauchyComplete.exists_splitting_of_isCauchySurface` (from the flow of `HasChronalCausalFlow`) has a merely continuous time coordinate, with no spacelike level set

/-- **A Cauchy-compact GH flat spacetime is Cauchy-complete** (the input of Theorem A in Theorem
B's proof, l.3536: "Reconsider the proof above when $M$ is assumed Cauchy-compact"). From a
compact spacelike Lipschitz Cauchy surface `S'` (`exists_isSpacelikeLipschitz_cauchy_of_isCompact`,
the module's one `sorry`): its glued length space is compact, hence complete
(`completeSpace_inducedLengthSpace_of_isCompact`), and its length topology is finer than the
topology of `M` (`continuous_inducedLengthSpace_toSubtype`). -/
theorem isCauchyComplete_of_isCompact_cauchy (M : FlatSpacetime.{u} d) (hGH : GH M)
    {S : Set M} (hS : (flatCausality d M).IsCauchySurface S) (hSc : IsCompact S)
    (hac : (flatCausality d M).IsAcausal S) : IsCauchyComplete d M := by
  obtain ⟨S', hS', hSc', hL⟩ := exists_isSpacelikeLipschitz_cauchy_of_isCompact M hGH hS hSc hac
  exact ⟨S', hS', hL, completeSpace_inducedLengthSpace_of_isCompact hSc' hL,
    continuous_inducedLengthSpace_toSubtype hL⟩

/-- Test of the intended use at `Classification.isCauchyComplete_of_cauchyCompact`. -/
example (M : FlatSpacetime.{u} d) (_hGH : GH M) (_hC : CauchyCompact M) : IsCauchyComplete d M := by
  obtain ⟨S, hS, hSc, hac⟩ := _hC; exact isCauchyComplete_of_isCompact_cauchy M _hGH hS hSc hac

end Causal.Flat.Cla
