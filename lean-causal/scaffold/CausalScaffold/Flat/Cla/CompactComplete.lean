import CausalScaffold.Flat.Nonloxodromic
import CausalScaffold.Flat.TitsNull
import CausalScaffold.Flat.Loxodromic
import CausalScaffold.CompactCauchy
import CausalScaffold.CurvesExtend
import CausalScaffold.Flat.Cla.CCComponent

/-!
# `CausalScaffold.Flat.Cla.CompactComplete` — a Cauchy-compact GH flat spacetime is Cauchy-complete

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §2.4 and
§11. **No label is marked**: the theorem rests on one tagged `sorry` (the smoothing step, SCOPE).
Cited UNMARKED: `bthm:cauclo` — `GHFspace.tex:353` (Theorem B, l.352–360), whose proof (l.3536)
feeds Theorem A a Cauchy-compact `M`, which must therefore be Cauchy-complete; `[2.4]`
Cauchy-complete — l.551–553 (prose, DEC-35, a reading); Cauchy-compact — l.560–565 (prose,
`FlatSpacetime.CauchyCompact`'s topological reading); the "fundamental observation" — l.3537–3540
(prose; lemma K, DEC-44). Line numbers are those of the labelled
`papers/barbot/legacy/labeled/GHFspace.tex`. Serves `Classification.isCauchyComplete_of_cauchyCompact`
(`Flat/Classification.lean:2429`), which closes by
`obtain ⟨S, hS, hSc, hac⟩ := _hC; exact isCauchyComplete_of_isCompact_cauchy M _hGH hS hSc hac`
(tested at the end of this file).

> A GH spacetime is *Cauchy-complete* if it admits a Cauchy hypersurface where the ambiant
> lorentzian metric restricts as a complete riemanian metric. (l.551–553)

> Among Cauchy-complete spacetimes, there is a remarkable natural family: GH spacetimes with
> *closed* Cauchy hypersurfaces (we know that in general, if a spacetime admits a closed Cauchy
> hypersurface, then all its Cauchy surfaces are closed - indeed, they are homeomorphic one to the
> other). We call such a spacetime *Cauchy-compact* GH spacetime (abbreviation CGH).
> (l.560–565)

> Reconsider the proof above when $M$ is assumed Cauchy-compact.
> A fundamental observation is that in a GH spacetime, every
> closed spacelike hypersurface is necessarely a Cauchy surface (l.3536–3538)

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; `Minkowski d` has `d` spatial
dimensions, so Barbot's `n` is `d + 1`.

## Main declarations
* `isCauchyComplete_of_isCompact_cauchy` — GH, a compact acausal Cauchy surface ⇒
  `IsCauchyComplete d M`. Assembled (no `sorry` of its own) from:
* `exists_isSpacelikeLipschitz_of_isCompact_cauchy` — a compact connected spacelike Lipschitz
  hypersurface `H`. **Its Cauchy property is not part of it.** Proved for `d = 0` (a point,
  `Flat/Cla/CCComponent.lean`'s `isSpacelikeLipschitz_singleton_zero`) and, for `d + 1`, from
* `exists_nonempty_isSpacelikeLipschitz_succ` — **the one `sorry`** of the module
  (`SORRY(bthm:cauclo, compact ⇒ complete, smoothing, d ≥ 1)`): a NONEMPTY compact spacelike
  Lipschitz `H`, connectedness being free (`Flat/Cla/CCComponent.lean`'s `exists_isConnected_isSpacelikeLipschitz_subset`:
  a connected component of a spacelike Lipschitz set is spacelike Lipschitz).
* PROVED, `isCauchySurface_of_isSpacelikeLipschitz`: in a GH flat spacetime with an acausal Cauchy
  surface, a compact connected spacelike Lipschitz `H` is a Cauchy surface — Barbot's "closed
  spacelike hypersurfaces are Cauchy" (l.3537–3538) for spacelike Lipschitz `H`: lemma K
  (`Causality.isCauchySurface_of_isLocallyCauchyTwoSided`) along the splitting of `M` given by
  the chronal causal flow of every flat spacetime (`flat_hasChronalCausalFlow`, second countability
  by DEC-49), fed by
* PROVED, `isLocallyCauchyTwoSided_of_isSpacelikeLipschitz` (GH): a spacelike Lipschitz `H` is
  locally Cauchy and two-sided. In the chart and the frame `g` at `x ∈ H`, `H` is the graph of a
  `c`-Lipschitz `f`, `c < 1`, so a strict contraction on a small ball; it is extended to an entire
  strict contraction and its local domain of dependence is pulled back by `g⁻¹` and the chart
  (the construction of `Flat/Cla/LocallyCauchy.lean`, steps 4–7, with the graph read off
  `IsSpacelikeLipschitzIn.locGraph` instead of a splitting).
* PROVED, for any `S ⊆ M`, `M` charted over `𝐌ⁿ` with the `(Isom(𝐌ⁿ), 𝐌ⁿ)` groupoid — the gluing
  of `IsSpacelikeLipschitzIn.isHomeomorph_toSubtype` over charts that `CauchyComplete`'s SCOPE
  left open:
  - `continuous_inducedLengthSpace_toSubtype_symm` (`IsSpacelikeLipschitz d S`): the subspace
    topology is finer than the glued length topology;
  - `continuous_inducedLengthSpace_toSubtype` (`T2Space M`): the glued length topology is finer
    than the topology of `M` — exactly `IsCauchyComplete`'s topology field — by a first-exit
    argument in the chart at the point;
  - `completeSpace_inducedLengthSpace_of_isCompact`: a COMPACT spacelike Lipschitz `S` is complete
    for its glued length (the length space is a continuous image of the compact `S`);
  - the chart transport they rest on: `localLength_chartSys_eq_lorentzLength`,
    `exists_lipschitzOnWith_chart` / `isLocLip_of_chart`, `chartPt`, `edist_le_edist_chart`,
    `edist_chart_le_pathLength`.

## Hypothesis checklist
| paper hypothesis | here |
|---|---|
| `M` GH | ✓ carried (`GH M`, ETT's reading); used by lemma K and strong causality |
| `M` Cauchy-compact ("closed Cauchy hypersurfaces", l.560–565) | ✓ carried in `CauchyCompact`'s topological reading: `S` Cauchy, compact, acausal |
| "the ambiant lorentzian metric restricts as a complete riemanian metric" (l.551–553) | ⚠ read (DEC-35): `IsCauchyComplete` — a spacelike Lipschitz Cauchy surface, `CompleteSpace` of its glued length, and the topology field |
| "closed spacelike hypersurface ⇒ Cauchy" (l.3537–3538) | ✓ proved for compact connected spacelike Lipschitz hypersurfaces (no hypothesis beyond GH and the given acausal Cauchy surface) |
| compact ⇒ complete (implicit, l.560 "Among Cauchy-complete spacetimes") | ✓ proved for a compact spacelike Lipschitz surface, with no second countability and no Hausdorff hypothesis beyond `M`'s |

## SCOPE (disclosed)
* **The smoothing step is not proved for `d ≥ 1`** (`exists_nonempty_isSpacelikeLipschitz_succ`,
  one tagged `sorry`): a NONEMPTY compact spacelike Lipschitz hypersurface. It is not asked to be
  Cauchy (lemma K, proved here, supplies that) nor connected (a component is taken,
  `Flat/Cla/CCComponent.lean`), and `d = 0` is closed by a point. The cosmological-time route
  (level sets of Barbot's cosmological time, spacelike Lipschitz on regular domains) is circular
  here: a regular-domain presentation of a Cauchy-compact `M` is Theorem A's conclusion, whose
  input is the Cauchy-completeness this step feeds. A topological acausal Cauchy surface is only a
  strict contraction in flat charts, with no slope bound `c < 1`: in the flat torus spacetime
  `𝐌¹/⟨(0, 2π)⟩` the graph of `sin` is an acausal compact Cauchy surface whose slope tends to `1`
  at `x = 0` in every frame, so `S` itself cannot be used. The obstruction (no intrinsic envelope
  construction on `M`, its locality, compactness and connectedness) is stated in full at the
  `sorry`. Everything downstream of it is proved, and the statement of the theorem is the
  dispatched one, unchanged.
* The local graph form and local domain of dependence are PRIVATE copies of
  `Flat/Cla/LocallyCauchy.lean` §1–§3 (`ballRetract`, `exists_isStrictContraction_extension`,
  `graphLocalDomain` and its saturation lemmas, `tarentin_flatCausality`,
  `isEMorphismOn_chartSource`, `mem_Jplus_chart_iff`, `mem_Jminus_chart_iff`,
  `isCauchySurfaceOn_inter_opens`) and of `Flat/TheoremBInputs.lean`'s
  `jplus_ne_singleton_of_isCausalFlow` / `jminus_ne_singleton_of_isCausalFlow`: neither module is
  in this file's dispatched import closure. At graduation, import them and delete the copies.
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

/-! ### Private copies (from `Flat/Cla/LocallyCauchy.lean` and `Flat/TheoremBInputs.lean`, neither importable here) -/

section Copies

open Function Metric

/-! ## §1 The retraction onto a closed ball; extending a local strict contraction -/

section Retraction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The radial retraction of `E` onto `closedBall y₀ ρ`. -/
private noncomputable def ballRetract (y₀ : E) (ρ : ℝ) (y : E) : E :=
  if ‖y - y₀‖ ≤ ρ then y else y₀ + (ρ / ‖y - y₀‖) • (y - y₀)

private theorem ballRetract_of_le {y₀ y : E} {ρ : ℝ} (h : ‖y - y₀‖ ≤ ρ) : ballRetract y₀ ρ y = y :=
  if_pos h

private theorem norm_ballRetract_sub_le {y₀ : E} {ρ : ℝ} (hρ : 0 ≤ ρ) (y : E) :
    ‖ballRetract y₀ ρ y - y₀‖ ≤ ρ := by
  unfold ballRetract
  split_ifs with h
  · exact h
  · push Not at h
    have hpos : 0 < ‖y - y₀‖ := hρ.trans_lt h
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hρ hpos.le),
      div_mul_cancel₀ _ hpos.ne']

/-- The variational inequality of the retraction (it is the metric projection). -/
private theorem inner_ballRetract_le {y₀ : E} {ρ : ℝ} (hρ : 0 ≤ ρ) (y w : E) (hw : ‖w - y₀‖ ≤ ρ) :
    inner ℝ (y - ballRetract y₀ ρ y) (w - ballRetract y₀ ρ y) ≤ 0 := by
  unfold ballRetract
  split_ifs with h
  · simp
  · push Not at h
    have ha : 0 < ‖y - y₀‖ := hρ.trans_lt h
    have h1 : y - (y₀ + (ρ / ‖y - y₀‖) • (y - y₀)) = (1 - ρ / ‖y - y₀‖) • (y - y₀) := by
      rw [sub_smul, one_smul]; abel
    have h2 : w - (y₀ + (ρ / ‖y - y₀‖) • (y - y₀)) = (w - y₀) - (ρ / ‖y - y₀‖) • (y - y₀) := by
      abel
    rw [h1, h2, real_inner_smul_left, inner_sub_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    have hi : inner ℝ (y - y₀) (w - y₀) ≤ ‖y - y₀‖ * ρ :=
      (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hw ha.le)
    have hc : 0 ≤ 1 - ρ / ‖y - y₀‖ := by rw [sub_nonneg, div_le_one ha]; exact h.le
    have h3 : ρ / ‖y - y₀‖ * ‖y - y₀‖ ^ 2 = ‖y - y₀‖ * ρ := by field_simp
    rw [h3]
    exact mul_nonpos_of_nonneg_of_nonpos hc (by linarith)

/-- **The retraction is 1-Lipschitz.** -/
private theorem norm_ballRetract_sub_ballRetract_le {y₀ : E} {ρ : ℝ} (hρ : 0 ≤ ρ) (y y' : E) :
    ‖ballRetract y₀ ρ y - ballRetract y₀ ρ y'‖ ≤ ‖y - y'‖ := by
  set p := ballRetract y₀ ρ y
  set q := ballRetract y₀ ρ y'
  have h1 := inner_ballRetract_le hρ y q (norm_ballRetract_sub_le hρ y')
  have h2 := inner_ballRetract_le hρ y' p (norm_ballRetract_sub_le hρ y)
  have key : ‖p - q‖ ^ 2 ≤ inner ℝ (y - y') (p - q) := by
    have : inner ℝ (y - y') (p - q) - ‖p - q‖ ^ 2 =
        -inner ℝ (y - p) (q - p) - inner ℝ (y' - q) (p - q) := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_sub_left, inner_sub_right, real_inner_comm]
      ring
    linarith
  have h3 := real_inner_le_norm (y - y') (p - q)
  rcases (norm_nonneg (p - q)).eq_or_lt with h0 | h0
  · rw [← h0]; exact norm_nonneg _
  · nlinarith

end Retraction

/-- **A strict contraction on a ball extends, near its centre, to an entire bounded strict
contraction**: `g ∘ π`, `π` the retraction onto `closedBall y₀ (δ/2)`. -/
private theorem exists_isStrictContraction_extension {g : EuclideanSpace ℝ (Fin d) → ℝ}
    {y₀ : EuclideanSpace ℝ (Fin d)} {δ : ℝ} (hδ : 0 < δ)
    (hg : ∀ y ∈ ball y₀ δ, ∀ y' ∈ ball y₀ δ, y ≠ y' → |g y - g y'| < ‖y - y'‖) :
    ∃ F : EuclideanSpace ℝ (Fin d) → ℝ, IsStrictContraction F ∧ (∀ y, |F y - g y₀| ≤ δ) ∧
      ∀ y, ‖y - y₀‖ ≤ δ / 2 → F y = g y := by
  have hρ : (0 : ℝ) ≤ δ / 2 := by positivity
  set π := ballRetract y₀ (δ / 2) with hπ
  have hmem : ∀ y, π y ∈ ball y₀ δ := fun y => by
    rw [mem_ball, dist_eq_norm]
    exact (norm_ballRetract_sub_le hρ y).trans_lt (by linarith)
  refine ⟨g ∘ π, fun y y' hne => ?_, fun y => ?_, fun y hy => ?_⟩
  · simp only [comp_apply]
    by_cases he : π y = π y'
    · rw [he, sub_self, abs_zero]; exact norm_pos_iff.2 (sub_ne_zero.2 hne)
    · exact (hg _ (hmem y) _ (hmem y') he).trans_le (norm_ballRetract_sub_ballRetract_le hρ y y')
  · simp only [comp_apply]
    have h0 : π y₀ = y₀ := ballRetract_of_le (by simpa using hρ)
    by_cases he : π y = y₀
    · rw [he, sub_self, abs_zero]; exact hδ.le
    · have := hg _ (hmem y) _ (mem_ball_self hδ) he
      have h2 := norm_ballRetract_sub_le hρ (y₀ := y₀) y
      linarith
  · exact congrArg g (ballRetract_of_le hy)

/-! ## §2 The local domain of dependence of an entire strict contraction, cut to a cylinder -/

section LocalDomain

variable {F : EuclideanSpace ℝ (Fin d) → ℝ}

/-- **The cone step, past side**: around `y₁`, the causal past of a point just above the graph,
down to the graph, stays within `ρ` of `y₁` spatially. -/
private theorem graphCone_past (hF : IsStrictContraction F) (y₁ : EuclideanSpace ℝ (Fin d)) {ρ : ℝ}
    (hρ : 0 < ρ) : ∃ ε > 0, ∀ p : Minkowski d, ‖p.2 - y₁‖ < ε → timeSub F p < ε →
      ∀ p', (minkowski d).le ⊤ p' p → 0 ≤ timeSub F p' → ‖p'.2 - y₁‖ < ρ := by
  have hlip := hF.lipschitzWith
  have hL : ∀ x y, |F x - F y| ≤ ‖x - y‖ := abs_sub_le_norm_of_lipschitzWith_one hlip
  obtain ⟨c₀, hc₀, hc₀ρ, hsph⟩ : ∃ c₀ : ℝ, 0 ≤ c₀ ∧ c₀ < ρ ∧
      ∀ x ∈ sphere y₁ ρ, |F x - F y₁| ≤ c₀ := by
    rcases (sphere y₁ ρ).eq_empty_or_nonempty with h | h
    · exact ⟨0, le_rfl, hρ, fun x hx => by rw [h] at hx; exact absurd hx (notMem_empty x)⟩
    · obtain ⟨x₀, hx₀, hmax⟩ := (isCompact_sphere y₁ ρ).exists_isMaxOn h
        ((continuous_abs.comp (hlip.continuous.sub continuous_const)).continuousOn)
      have hx₀n : ‖x₀ - y₁‖ = ρ := by rw [← dist_eq_norm]; exact hx₀
      refine ⟨|F x₀ - F y₁|, abs_nonneg _, ?_, fun x hx => hmax hx⟩
      rw [← hx₀n]
      exact hF x₀ y₁ fun h => by rw [h, sub_self, norm_zero] at hx₀n; exact hρ.ne hx₀n
  refine ⟨(ρ - c₀) / 4, by linarith, fun p hp hTp p' hle hT' => ?_⟩
  by_contra hcon
  push Not at hcon
  have hd := minkowski_le_top_iff.1 hle
  set φ : ℝ → ℝ := fun l => ‖(p'.2 + l • (p.2 - p'.2)) - y₁‖ with hφ
  have hφc : ContinuousOn φ (Icc 0 1) :=
    ((continuous_const.add (continuous_id.smul continuous_const)).sub
      continuous_const).norm.continuousOn
  have h0 : φ 0 = ‖p'.2 - y₁‖ := by simp [hφ]
  have h1 : φ 1 = ‖p.2 - y₁‖ := by simp [hφ]
  obtain ⟨l, hl, hlρ⟩ := intermediate_value_Icc' zero_le_one hφc
    (show ρ ∈ Icc (φ 1) (φ 0) by rw [h0, h1]; exact ⟨by linarith, hcon⟩)
  set w : Minkowski d := (p'.1 + l * (p.1 - p'.1), p'.2 + l • (p.2 - p'.2)) with hw
  have hw2 : ‖w.2 - y₁‖ = ρ := hlρ
  have hwp' : ‖w.2 - p'.2‖ ≤ w.1 - p'.1 := by
    simp only [hw, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hl.1]
    exact mul_le_mul_of_nonneg_left hd hl.1
  have hpw : ‖p.2 - w.2‖ ≤ p.1 - w.1 := by
    have e1 : p.2 - w.2 = (1 - l) • (p.2 - p'.2) := by simp only [hw, sub_smul, one_smul]; abel
    have e2 : p.1 - w.1 = (1 - l) * (p.1 - p'.1) := by simp only [hw]; ring
    rw [e1, e2, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [hl.2])]
    exact mul_le_mul_of_nonneg_left hd (by linarith [hl.2])
  have hTw : 0 ≤ timeSub F w :=
    hT'.trans (timeSub_le_of_le hlip (minkowski_le_top_iff.2 hwp'))
  have hFw : F y₁ - c₀ ≤ F w.2 := by
    have := hsph w.2 (by rw [mem_sphere, dist_eq_norm]; exact hw2)
    linarith [neg_abs_le (F w.2 - F y₁)]
  have htri : ‖w.2 - y₁‖ ≤ ‖p.2 - w.2‖ + ‖p.2 - y₁‖ := by
    have := norm_sub_le_norm_sub_add_norm_sub w.2 p.2 y₁
    rwa [norm_sub_rev w.2 p.2] at this
  have hFp := hL p.2 y₁
  simp only [timeSub] at hTw hTp
  linarith [le_abs_self (F p.2 - F y₁)]

/-- Time reflection `(t, x) ↦ (−t, x)`. -/
private def timeReflect (p : Minkowski d) : Minkowski d := (-p.1, p.2)

private theorem le_timeReflect_iff {p q : Minkowski d} :
    (minkowski d).le ⊤ (timeReflect q) (timeReflect p) ↔ (minkowski d).le ⊤ p q := by
  simp only [minkowski_le_top_iff, timeReflect]
  rw [norm_sub_rev]; ring_nf

private theorem timeSub_neg_timeReflect (p : Minkowski d) :
    timeSub (fun x => -F x) (timeReflect p) = -timeSub F p := by
  simp [timeSub, timeReflect]; ring

/-- **The cone step, future side**, by time reflection. -/
private theorem graphCone_future (hF : IsStrictContraction F) (y₁ : EuclideanSpace ℝ (Fin d)) {ρ : ℝ}
    (hρ : 0 < ρ) : ∃ ε > 0, ∀ p : Minkowski d, ‖p.2 - y₁‖ < ε → -ε < timeSub F p →
      ∀ p', (minkowski d).le ⊤ p p' → timeSub F p' ≤ 0 → ‖p'.2 - y₁‖ < ρ := by
  obtain ⟨ε, hε, h⟩ := graphCone_past hF.neg y₁ hρ
  refine ⟨ε, hε, fun p hp hTp p' hle hT' => ?_⟩
  have := h (timeReflect p) hp (by rw [timeSub_neg_timeReflect]; linarith) (timeReflect p')
    (le_timeReflect_iff.2 hle) (by rw [timeSub_neg_timeReflect]; linarith)
  exact this

variable (F) in
/-- The set whose interior is the local domain: within `r` of `y₀` spatially, `|T| < r`, and the
causal past (resp. future) of each point, down (resp. up) to the graph, within `r` of `y₀`. -/
private def graphLocalSet (y₀ : EuclideanSpace ℝ (Fin d)) (r : ℝ) : Set (Minkowski d) :=
  {q | ‖q.2 - y₀‖ < r ∧ |timeSub F q| < r ∧
    (0 ≤ timeSub F q → ∀ p, (minkowski d).le ⊤ p q → 0 ≤ timeSub F p → ‖p.2 - y₀‖ < r) ∧
    (timeSub F q ≤ 0 → ∀ p, (minkowski d).le ⊤ q p → timeSub F p ≤ 0 → ‖p.2 - y₀‖ < r)}

variable {y₀ : EuclideanSpace ℝ (Fin d)} {r : ℝ}

private theorem graphLocalSet_past (hF : IsStrictContraction F) {q p : Minkowski d}
    (hq : q ∈ graphLocalSet F y₀ r)
    (hpq : (minkowski d).le ⊤ p q) (hp : 0 ≤ timeSub F p) : p ∈ graphLocalSet F y₀ r := by
  have hlip := hF.lipschitzWith
  obtain ⟨-, hqT, hqp, -⟩ := hq
  have hTpq := timeSub_le_of_le hlip hpq
  have hq0 : 0 ≤ timeSub F q := hp.trans hTpq
  refine ⟨hqp hq0 p hpq hp, ?_, fun _ p' hp' hT' => hqp hq0 p' ((minkowski d).le_trans hp' hpq) hT',
    fun hT p' hp' hT' => ?_⟩
  · rw [abs_of_nonneg hp]; rw [abs_of_nonneg hq0] at hqT; linarith
  · have hp0 : timeSub F p = 0 := le_antisymm hT hp
    have hpp' : p = p' := by
      by_contra hne
      have := timeSub_lt_of_le hF hp' hne
      linarith
    subst hpp'
    exact hqp hq0 p hpq hp

private theorem graphLocalSet_future (hF : IsStrictContraction F) {q p : Minkowski d}
    (hq : q ∈ graphLocalSet F y₀ r) (hqp : (minkowski d).le ⊤ q p) (hp : timeSub F p ≤ 0) :
    p ∈ graphLocalSet F y₀ r := by
  have hlip := hF.lipschitzWith
  obtain ⟨-, hqT, -, hqf⟩ := hq
  have hTqp := timeSub_le_of_le hlip hqp
  have hq0 : timeSub F q ≤ 0 := hTqp.trans hp
  refine ⟨hqf hq0 p hqp hp, ?_, fun hT p' hp' hT' => ?_,
    fun _ p' hp' hT' => hqf hq0 p' ((minkowski d).le_trans hqp hp') hT'⟩
  · rw [abs_of_nonpos hp]; rw [abs_of_nonpos hq0] at hqT; linarith
  · have hp0 : timeSub F p = 0 := le_antisymm hp hT
    have hpp' : p' = p := by
      by_contra hne
      have := timeSub_lt_of_le hF hp' hne
      linarith
    subst hpp'
    exact hqf hq0 p' hqp hp

/-- **A graph point within `r` of `y₀` is interior to the local set** (both cone steps). -/
private theorem mem_interior_graphLocalSet_of_graph (hF : IsStrictContraction F) {q : Minkowski d}
    (hq : timeSub F q = 0) (hqr : ‖q.2 - y₀‖ < r) : q ∈ interior (graphLocalSet F y₀ r) := by
  have hlip := hF.lipschitzWith
  set ρ := r - ‖q.2 - y₀‖ with hρdef
  have hρ : 0 < ρ := by linarith
  have hr : 0 < r := (norm_nonneg _).trans_lt hqr
  obtain ⟨ε₁, hε₁, h₁⟩ := graphCone_past hF q.2 hρ
  obtain ⟨ε₂, hε₂, h₂⟩ := graphCone_future hF q.2 hρ
  set ε := min (min ε₁ ε₂) (min ρ r) with hεdef
  have hε : 0 < ε := lt_min (lt_min hε₁ hε₂) (lt_min hρ hr)
  have hε1 : ε ≤ ε₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hε2 : ε ≤ ε₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hερ : ε ≤ ρ := (min_le_right _ _).trans (min_le_left _ _)
  have hεr : ε ≤ r := (min_le_right _ _).trans (min_le_right _ _)
  set O : Set (Minkowski d) := {p | ‖p.2 - q.2‖ < ε ∧ |timeSub F p| < ε} with hO
  have hOo : IsOpen O :=
    (isOpen_lt ((continuous_snd.sub continuous_const).norm) continuous_const).inter
      (isOpen_lt (continuous_timeSub hlip).abs continuous_const)
  have hqO : q ∈ O := ⟨by simpa using hε, by rw [hq, abs_zero]; exact hε⟩
  have hspace : ∀ p' : Minkowski d, ‖p'.2 - q.2‖ < ρ → ‖p'.2 - y₀‖ < r := fun p' h => by
    have := norm_sub_le_norm_sub_add_norm_sub p'.2 q.2 y₀
    linarith
  refine interior_maximal (fun p hp => ?_) hOo hqO
  obtain ⟨hp1, hp2⟩ := hp
  have hT := abs_lt.1 hp2
  refine ⟨hspace p (hp1.trans_le hερ), hp2.trans_le hεr, fun _ p' hp' hT' => ?_,
    fun _ p' hp' hT' => ?_⟩
  · exact hspace p' (h₁ p (hp1.trans_le hε1) (hT.2.trans_le hε1) p' hp' hT')
  · exact hspace p' (h₂ p (hp1.trans_le hε2) (by linarith) p' hp' hT')

/-- **The interior of the local set is closed under `J⁻` inside `{T ≥ 0}`.** -/
private theorem interior_graphLocalSet_past (hF : IsStrictContraction F) {z q : Minkowski d}
    (hz : z ∈ interior (graphLocalSet F y₀ r)) (hqz : (minkowski d).le ⊤ q z)
    (hq : 0 ≤ timeSub F q) : q ∈ interior (graphLocalSet F y₀ r) := by
  have hlip := hF.lipschitzWith
  rcases hq.lt_or_eq with hq | hq
  · obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior z hz
    set z' : Minkowski d := z + ((ε / 2, 0) : Minkowski d) with hz'def
    have hz' : z' ∈ graphLocalSet F y₀ r := by
      refine interior_subset (hball ?_)
      rw [mem_ball, dist_eq_norm, hz'def, add_sub_cancel_left, Prod.norm_def]
      simp only [norm_zero, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
      rw [max_eq_left (half_pos hε).le]
      exact half_lt_self hε
    have hz'1 : z'.1 = z.1 + ε / 2 := rfl
    have hz'2 : z'.2 = z.2 := by simp [hz'def]
    set U : Set (Minkowski d) := {p | ‖z'.2 - p.2‖ < z'.1 - p.1} ∩ {p | 0 < timeSub F p}
      with hUdef
    have hUo : IsOpen U :=
      (isOpen_lt (continuous_const.sub continuous_snd).norm
        (continuous_const.sub continuous_fst)).inter
        (isOpen_lt continuous_const (continuous_timeSub hlip))
    have hqU : q ∈ U := by
      refine ⟨?_, hq⟩
      have := minkowski_le_top_iff.1 hqz
      show ‖z'.2 - q.2‖ < z'.1 - q.1
      rw [hz'1, hz'2]
      linarith [half_pos hε]
    refine interior_maximal (fun p hp => ?_) hUo hqU
    exact graphLocalSet_past hF hz' (minkowski_le_top_iff.2 hp.1.le) hp.2.le
  · exact mem_interior_graphLocalSet_of_graph hF hq.symm
      (graphLocalSet_past hF (interior_subset hz) hqz (le_of_eq hq)).1

/-- **The interior of the local set is closed under `J⁺` inside `{T ≤ 0}`.** -/
private theorem interior_graphLocalSet_future (hF : IsStrictContraction F) {z q : Minkowski d}
    (hz : z ∈ interior (graphLocalSet F y₀ r)) (hzq : (minkowski d).le ⊤ z q)
    (hq : timeSub F q ≤ 0) : q ∈ interior (graphLocalSet F y₀ r) := by
  have hlip := hF.lipschitzWith
  rcases hq.lt_or_eq with hq | hq
  · obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior z hz
    set z' : Minkowski d := z - ((ε / 2, 0) : Minkowski d) with hz'def
    have hz' : z' ∈ graphLocalSet F y₀ r := by
      refine interior_subset (hball ?_)
      rw [mem_ball, dist_eq_norm, hz'def, sub_sub_cancel_left, norm_neg, Prod.norm_def]
      simp only [norm_zero, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
      rw [max_eq_left (half_pos hε).le]
      exact half_lt_self hε
    have hz'1 : z'.1 = z.1 - ε / 2 := rfl
    have hz'2 : z'.2 = z.2 := by simp [hz'def]
    set U : Set (Minkowski d) := {p | ‖p.2 - z'.2‖ < p.1 - z'.1} ∩ {p | timeSub F p < 0}
      with hUdef
    have hUo : IsOpen U :=
      (isOpen_lt (continuous_snd.sub continuous_const).norm
        (continuous_fst.sub continuous_const)).inter
        (isOpen_lt (continuous_timeSub hlip) continuous_const)
    have hqU : q ∈ U := by
      refine ⟨?_, hq⟩
      have := minkowski_le_top_iff.1 hzq
      show ‖q.2 - z'.2‖ < q.1 - z'.1
      rw [hz'1, hz'2]
      linarith [half_pos hε]
    refine interior_maximal (fun p hp => ?_) hUo hqU
    exact graphLocalSet_future hF hz' (minkowski_le_top_iff.2 hp.1.le) hp.2.le
  · exact mem_interior_graphLocalSet_of_graph hF hq
      (graphLocalSet_future hF (interior_subset hz) hzq (le_of_eq hq)).1

/-- A bounded `F`: every causal line meets its graph. -/
private theorem exists_mem_graph_line_of_bounded {c B : ℝ} (hlip : LipschitzWith 1 F)
    (hB : ∀ y, |F y - c| ≤ B) (z v : Minkowski d) (hv : IsFutureCausal v) (hv0 : v ≠ 0) :
    ∃ s : ℝ, z + s • v ∈ graph F := by
  have hv1 : 0 < v.1 := lt_of_le_of_ne hv.1 fun h => hv0 (eq_zero_of_fst_eq_zero h.symm hv.2)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  set K : ℝ := (|z.1| + |c| + B + 1) / v.1 with hK
  have hK0 : 0 ≤ K := div_nonneg (by positivity) hv1.le
  have hKv : K * v.1 = |z.1| + |c| + B + 1 := by rw [hK]; field_simp
  have hcont : ContinuousOn (fun s : ℝ => timeSub F (z + s • v)) (Icc (-K) K) :=
    ((continuous_timeSub hlip).comp (continuous_const.add
      (continuous_id.smul continuous_const))).continuousOn
  have hlo : timeSub F (z + (-K) • v) ≤ 0 := by
    have := hB (z + (-K) • v).2
    simp only [timeSub, Prod.fst_add, Prod.smul_fst, smul_eq_mul] at this ⊢
    have h1 := abs_le.1 this
    linarith [le_abs_self z.1, neg_abs_le c, le_abs_self c]
  have hhi : 0 ≤ timeSub F (z + K • v) := by
    have := hB (z + K • v).2
    simp only [timeSub, Prod.fst_add, Prod.smul_fst, smul_eq_mul] at this ⊢
    have h1 := abs_le.1 this
    linarith [neg_abs_le z.1, neg_abs_le c, le_abs_self c]
  obtain ⟨s, -, hs⟩ := intermediate_value_Icc (by linarith) hcont ⟨hlo, hhi⟩
  exact ⟨s, mem_graph_iff_timeSub.2 hs⟩

variable (F y₀ r) in
/-- **The local domain** `W = int (graphLocalSet F y₀ r)`, as an open set. -/
private def graphLocalDomain : Opens (Minkowski d) := ⟨interior (graphLocalSet F y₀ r), isOpen_interior⟩

private theorem mem_graphLocalDomain {q : Minkowski d} :
    q ∈ graphLocalDomain F y₀ r ↔ q ∈ interior (graphLocalSet F y₀ r) :=
  Iff.rfl

private theorem graphLocalDomain_subset {q : Minkowski d} (hq : q ∈ graphLocalDomain F y₀ r) :
    ‖q.2 - y₀‖ < r ∧ |timeSub F q| < r :=
  let h := interior_subset hq; ⟨h.1, h.2.1⟩

/-- **The graph is a Cauchy surface of the local domain**, through LipschitzGraph's saturated
criterion `isCauchySurfaceOn_graph_of_saturated`. -/
private theorem isCauchySurfaceOn_graphLocalDomain (hF : IsStrictContraction F) {c B : ℝ}
    (hB : ∀ y, |F y - c| ≤ B) :
    (minkowski d).IsCauchySurfaceOn (graphLocalDomain F y₀ r) (graph F) :=
  isCauchySurfaceOn_graph_of_saturated hF
    (fun z _ v hv hv0 => exists_mem_graph_line_of_bounded hF.lipschitzWith hB z v hv hv0)
    (fun _ hz _ hqz hq => interior_graphLocalSet_past hF hz hqz hq)
    (fun _ hz _ hzq hq => interior_graphLocalSet_future hF hz hzq hq)

/-- **The local domain is causally convex for the cone.** -/
private theorem graphLocalDomain_convex (hF : IsStrictContraction F) {a b c : Minkowski d}
    (ha : a ∈ graphLocalDomain F y₀ r) (hc : c ∈ graphLocalDomain F y₀ r)
    (hab : (minkowski d).le ⊤ a b)
    (hbc : (minkowski d).le ⊤ b c) : b ∈ graphLocalDomain F y₀ r := by
  rcases le_total 0 (timeSub F b) with h | h
  · exact interior_graphLocalSet_past hF hc hbc h
  · exact interior_graphLocalSet_future hF ha hab h

/-- The vertical segment below a point of the local domain above the graph lies in it, so the
point is in the future of the graph inside the local domain. -/
private theorem Jplus_graphLocalDomain (hF : IsStrictContraction F) :
    (minkowski d).Jplus (graphLocalDomain F y₀ r) (graph F ∩ graphLocalDomain F y₀ r) =
      {q | q ∈ graphLocalDomain F y₀ r ∧ 0 ≤ timeSub F q} := by
  have hlip := hF.lipschitzWith
  ext q
  constructor
  · rintro ⟨x, ⟨hxg, -⟩, hxq⟩
    refine ⟨(minkowski d).le_mem_right hxq, ?_⟩
    have := timeSub_le_of_le hlip ((minkowski d).le_mono le_top hxq)
    rw [mem_graph_iff_timeSub.1 hxg] at this
    exact this
  · rintro ⟨hqW, hq⟩
    have hseg : ∀ τ ∈ Icc (F q.2) q.1, ((τ, q.2) : Minkowski d) ∈ graphLocalDomain F y₀ r := by
      intro τ hτ
      refine interior_graphLocalSet_past hF hqW (minkowski_le_top_iff.2 ?_) ?_
      · simp only [sub_self, norm_zero]; linarith [hτ.2]
      · simp only [timeSub]; linarith [hτ.1]
    have hxW := hseg (F q.2) ⟨le_rfl, by simp only [timeSub] at hq; linarith⟩
    refine ⟨(F q.2, q.2), ⟨mk_mem_graph q.2, hxW⟩, ?_⟩
    refine staticCausality.le_iff.2 ⟨by simp only [timeSub] at hq; linarith, fun _ => q.2, rfl,
      rfl, ⟨fun _ _ _ _ => by simp, fun τ hτ => hseg τ hτ⟩⟩

private theorem Jminus_graphLocalDomain (hF : IsStrictContraction F) :
    (minkowski d).Jminus (graphLocalDomain F y₀ r) (graph F ∩ graphLocalDomain F y₀ r) =
      {q | q ∈ graphLocalDomain F y₀ r ∧ timeSub F q ≤ 0} := by
  have hlip := hF.lipschitzWith
  ext q
  constructor
  · rintro ⟨x, ⟨hxg, -⟩, hqx⟩
    refine ⟨(minkowski d).le_mem_left hqx, ?_⟩
    have := timeSub_le_of_le hlip ((minkowski d).le_mono le_top hqx)
    rw [mem_graph_iff_timeSub.1 hxg] at this
    exact this
  · rintro ⟨hqW, hq⟩
    have hseg : ∀ τ ∈ Icc q.1 (F q.2), ((τ, q.2) : Minkowski d) ∈ graphLocalDomain F y₀ r := by
      intro τ hτ
      refine interior_graphLocalSet_future hF hqW (minkowski_le_top_iff.2 ?_) ?_
      · simp only [sub_self, norm_zero]; linarith [hτ.1]
      · simp only [timeSub]; linarith [hτ.2]
    have hxW := hseg (F q.2) ⟨by simp only [timeSub] at hq; linarith, le_rfl⟩
    refine ⟨(F q.2, q.2), ⟨mk_mem_graph q.2, hxW⟩, ?_⟩
    refine staticCausality.le_iff.2 ⟨by simp only [timeSub] at hq; linarith, fun _ => q.2, rfl,
      rfl, ⟨fun _ _ _ _ => by simp, fun τ hτ => hseg τ hτ⟩⟩

end LocalDomain

/-! ## §3 Charts of a flat spacetime -/

section LCChart

variable {X : Type*} [TopologicalSpace X] [ChartedSpace (Minkowski d) X]
  [HasGroupoid X (gxGroupoid (isom d) (Minkowski d))]

/-- Every flat spacetime is tarentin (the proof of `Flat.TheoremBInputs.flatCausality_tarentin`,
not imported here). -/
private theorem tarentin_flatCausality : (flatCausality d X).Tarentin := by
  intro x U hU
  set e := chartAt (Minkowski d) x with he
  have hiso : ChartIso (flatCausality d X) (minkowski d) e := flatCausality_chartIso_chartAt x
  have hxs : x ∈ e.source := mem_chart_source _ x
  let W : Opens X := ⟨interior U ∩ e.source, isOpen_interior.inter e.open_source⟩
  have hxW : x ∈ W := ⟨mem_interior_iff_mem_nhds.2 hU, hxs⟩
  have hWe : W ≤ chartSource e := fun z hz => hz.2
  have hyW : e x ∈ chartImage e W := mem_chartImage_of_mem hxs hxW
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 (chartImage e W).isOpen (e x) hyW
  set y := e x with hy
  set ε := ρ / 4 with hε
  have hε0 : 0 < ε := by positivity
  have key : ∀ w : Minkowski d, dist w y < 3 * ε → w ∈ chartImage e W := fun w hw =>
    hball (by rw [mem_ball]; linarith)
  set p' : Minkowski d := (y.1 - ε, y.2) with hp'
  set q' : Minkowski d := (y.1 + ε, y.2) with hq'
  have hp'y : dist p' y = ε := by
    rw [hp', Prod.dist_eq, dist_self, Real.dist_eq]
    simp only [sub_sub_cancel_left, abs_neg, abs_of_pos hε0]
    exact max_eq_left hε0.le
  have hq'y : dist q' y = ε := by
    rw [hq', Prod.dist_eq, dist_self, Real.dist_eq]
    simp only [add_sub_cancel_left, abs_of_pos hε0]
    exact max_eq_left hε0.le
  obtain ⟨p, -, hpW, hpe, -⟩ := exists_of_mem_chartImage (key p' (by linarith))
  obtain ⟨q, -, hqW, hqe, -⟩ := exists_of_mem_chartImage (key q' (by linarith))
  refine ⟨p, interior_subset hpW.1, q, interior_subset hqW.1, ?_⟩
  have hO : IsOpen ((W : Set X) ∩ (e.source ∩ e ⁻¹' ball y (ε / 2))) :=
    W.isOpen.inter (e.continuousOn.isOpen_inter_preimage e.open_source isOpen_ball)
  refine interior_maximal (fun z hz => ?_) hO ⟨hxW, hxs, mem_ball_self (by linarith)⟩
  obtain ⟨hzW, -, hzb⟩ := hz
  have hzy : dist (e z) y < ε / 2 := hzb
  rw [mem_preimage, mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, abs_lt] at hzb
  obtain ⟨⟨h1, h2⟩, h3⟩ := hzb
  rw [Causality.mem_diamond]
  constructor
  · refine (flatCausality d X).le_mono le_top ((hiso W hWe p hpW z hzW).1.2 ?_)
    rw [hpe]
    refine staticCausality.le_iff.2 (staticLe_of_ball (ρ := 2 * ε) (fun w hw => key w
      ((dist_triangle w p' y).trans_lt (by linarith))) ?_ ?_ ?_)
    · show y.1 - ε ≤ (e z).1
      linarith
    · show dist y.2 (e z).2 ≤ (e z).1 - (y.1 - ε)
      rw [dist_comm]; linarith
    · show (e z).1 - (y.1 - ε) < 2 * ε
      linarith
  · refine (flatCausality d X).le_mono le_top ((hiso W hWe z hzW q hqW).1.2 ?_)
    rw [hqe]
    refine staticCausality.le_iff.2 (staticLe_of_ball (ρ := 2 * ε) (fun w hw => key w
      ((dist_triangle w (e z) y).trans_lt (by linarith))) ?_ ?_ ?_)
    · show (e z).1 ≤ y.1 + ε
      linarith
    · show dist (e z).2 y.2 ≤ y.1 + ε - (e z).1
      linarith
    · show y.1 + ε - (e z).1 < 2 * ε
      linarith

/-- **A chart is an abstract `𝕄≥0`-morphism on its source** (`IsEMorphismOn`), from a chart
isomorphism (`flatCausality_chartIso_chartAt`). -/
private theorem isEMorphismOn_chartSource {e : OpenPartialHomeomorph X (Minkowski d)}
    (hiso : ChartIso (flatCausality d X) (minkowski d) e) :
    IsEMorphismOn (flatCausality d X) (minkowski d) (chartSource e) e := by
  have himg : ∀ V : Opens X, V ≤ chartSource e → ((chartImage e V : Opens _) : Set _) = e '' V :=
    fun V hV => coe_chartImage_of_le hV
  have hsub : ∀ (V : Opens X) (U : Opens (Minkowski d)), V ≤ chartSource e → MapsTo e V U →
      chartImage e V ≤ U := fun V U hV hmaps p hp => by
    rw [← SetLike.mem_coe, himg V hV] at hp
    obtain ⟨z, hz, rfl⟩ := hp
    exact hmaps hz
  exact
  { continuousOn := e.continuousOn
    isOpen_image := fun V hV => by rw [← himg V hV]; exact (chartImage e V).isOpen
    map_le := fun V U hV hmaps y z hyz =>
      (minkowski d).le_mono (hsub V U hV hmaps)
        (((hiso V hV y ((flatCausality d X).le_mem_left hyz) z
          ((flatCausality d X).le_mem_right hyz)).1).1 hyz)
    map_lt := fun V U hV hmaps y z hyz =>
      (minkowski d).lt_mono (hsub V U hV hmaps)
        (((hiso V hV y ((flatCausality d X).lt_mem_left hyz) z
          ((flatCausality d X).lt_mem_right hyz)).2).1 hyz)
    locally := fun z hz => ⟨chartSource e, le_rfl, hz, e.injOn, fun V' hV' U hU y hy w hw => by
      have hU' : chartImage e V' = U := SetLike.coe_injective (by rw [himg V' hV', hU])
      rw [← hU']; exact hiso V' hV' y hy w hw⟩ }

/-- `J⁺` through a chart. -/
private theorem mem_Jplus_chart_iff {e : OpenPartialHomeomorph X (Minkowski d)}
    (hiso : ChartIso (flatCausality d X) (minkowski d) e) {U : Opens X} (hU : U ≤ chartSource e)
    {A : Set X} (hA : A ⊆ U) {n : X} :
    n ∈ (flatCausality d X).Jplus U A ↔
      n ∈ U ∧ e n ∈ (minkowski d).Jplus (chartImage e U) (e '' A) := by
  constructor
  · rintro ⟨a, ha, hle⟩
    have hn := (flatCausality d X).le_mem_right hle
    exact ⟨hn, _, ⟨a, ha, rfl⟩, ((hiso U hU a (hA ha) n hn).1).1 hle⟩
  · rintro ⟨hn, _, ⟨a, ha, rfl⟩, hle⟩
    exact ⟨a, ha, ((hiso U hU a (hA ha) n hn).1).2 hle⟩

/-- `J⁻` through a chart. -/
private theorem mem_Jminus_chart_iff {e : OpenPartialHomeomorph X (Minkowski d)}
    (hiso : ChartIso (flatCausality d X) (minkowski d) e) {U : Opens X} (hU : U ≤ chartSource e)
    {A : Set X} (hA : A ⊆ U) {n : X} :
    n ∈ (flatCausality d X).Jminus U A ↔
      n ∈ U ∧ e n ∈ (minkowski d).Jminus (chartImage e U) (e '' A) := by
  constructor
  · rintro ⟨a, ha, hle⟩
    have hn := (flatCausality d X).le_mem_left hle
    exact ⟨hn, _, ⟨a, ha, rfl⟩, ((hiso U hU n hn a (hA ha)).1).1 hle⟩
  · rintro ⟨hn, _, ⟨a, ha, rfl⟩, hle⟩
    exact ⟨a, ha, ((hiso U hU n hn a (hA ha)).1).2 hle⟩

end LCChart

/-- A Cauchy surface of `W` meets every inextensible curve of `W` inside `W`. -/
private theorem isCauchySurfaceOn_inter_opens {X : Type*} [TopologicalSpace X] {C : Causality X}
    {W : Opens X} {A : Set X} (h : C.IsCauchySurfaceOn W A) : C.IsCauchySurfaceOn W (A ∩ W) := by
  intro J c hc
  obtain ⟨x, ⟨⟨t, ht, rfl⟩, hxA⟩, huniq⟩ := h J c hc
  exact ⟨c t, ⟨⟨t, ht, rfl⟩, hxA, hc.1.mem ht⟩, fun y hy => huniq y ⟨hy.1, hy.2.1⟩⟩


section FlowFields

variable {M : Type*} [TopologicalSpace M] {C : Causality M} {φ : Flow ℝ M}

/-- **A causal flow gives `J⁺(p) ≠ {p}`**: if `J⁺(p) = {p}`, the forward orbit of `p` is
constant, hence (group law) the whole orbit, against `nonstationary`. -/
private theorem jplus_ne_singleton_of_isCausalFlow (hφ : C.IsCausalFlow φ) (p : M) :
    C.Jplus ⊤ {p} ≠ {p} := by
  intro h
  have hfix : ∀ t : ℝ, 0 ≤ t → φ t p = p := fun t ht => by
    have hmem : φ t p ∈ C.Jplus ⊤ {p} :=
      ⟨p, rfl, by simpa [Flow.map_zero_apply] using hφ.le p ht⟩
    rw [h] at hmem
    exact hmem
  obtain ⟨t, ht⟩ := hφ.nonstationary p
  apply ht
  rcases le_total 0 t with h0 | h0
  · exact hfix t h0
  · have h' := hfix (-t) (by linarith)
    calc φ t p = φ t (φ (-t) p) := by rw [h']
      _ = p := by rw [← Flow.map_add, add_neg_cancel, Flow.map_zero_apply]

/-- **A causal flow gives `J⁻(p) ≠ {p}`** (the backward orbit). -/
private theorem jminus_ne_singleton_of_isCausalFlow (hφ : C.IsCausalFlow φ) (p : M) :
    C.Jminus ⊤ {p} ≠ {p} := by
  intro h
  have hfix : ∀ t : ℝ, t ≤ 0 → φ t p = p := fun t ht => by
    have hmem : φ t p ∈ C.Jminus ⊤ {p} :=
      ⟨p, rfl, by simpa [Flow.map_zero_apply] using hφ.le p ht⟩
    rw [h] at hmem
    exact hmem
  obtain ⟨t, ht⟩ := hφ.nonstationary p
  apply ht
  rcases le_total t 0 with h0 | h0
  · exact hfix t h0
  · have h' := hfix (-t) (by linarith)
    calc φ t p = φ t (φ (-t) p) := by rw [h']
      _ = p := by rw [← Flow.map_add, add_neg_cancel, Flow.map_zero_apply]

end FlowFields

end Copies

/-! ### A spacelike Lipschitz hypersurface is locally Cauchy and two-sided -/

section LocCauchy

open Metric
open scoped Pointwise

private theorem mem_image_inv_smul_iff {g : isom d} {A : Set (Minkowski d)} {q : Minkowski d} :
    q ∈ (fun p => g⁻¹ • p) '' A ↔ g • q ∈ A :=
  ⟨by rintro ⟨p, hp, rfl⟩; simpa using hp, fun h => ⟨g • q, h, by simp⟩⟩

private theorem mem_isomImage_inv_iff {g : isom d} {W : Opens (Minkowski d)} {q : Minkowski d} :
    q ∈ isomImage g⁻¹ W ↔ g • q ∈ W := by
  rw [mem_isomImage, inv_inv]

/-- **A spacelike Lipschitz hypersurface of a GH flat spacetime is locally Cauchy and two-sided**
(the "spacelike hypersurface" input of lemma K, `CausalScaffold.CompactCauchy`). At `x ∈ H`, in
the chart at `x` and the frame `g` of `IsSpacelikeLipschitzIn`, `H` is the graph of a `c`-Lipschitz
`f`, `c < 1`, hence of a strict contraction on a small ball; it extends to an entire strict
contraction `F` (`exists_isStrictContraction_extension`), and the chart preimage of the local
domain of `graph F` (`graphLocalDomain`), moved back by `g⁻¹`, is the neighbourhood: causally
convex through a causally convex `Vc ∋ x` of the strongly causal `M`, Cauchy by
`isCauchySurfaceOn_graphLocalDomain` transported along `g⁻¹` and the chart, its two sides
`{timeSub F ∘ g > 0}`, `{timeSub F ∘ g < 0}`. -/
theorem isLocallyCauchyTwoSided_of_isSpacelikeLipschitz {M : FlatSpacetime.{u} d} (hGH : GH M)
    {H : Set M} (hL : IsSpacelikeLipschitz d H) :
    (flatCausality d M).IsLocallyCauchyTwoSided H := by
  classical
  intro x hx
  obtain ⟨V, hxV, hVt, hT⟩ := hL x hx
  set e := chartAt (Minkowski d) x with he_def
  have hiso : ChartIso (flatCausality d M) (minkowski d) e := flatCausality_chartIso_chartAt x
  have hxe : x ∈ e.source := mem_chart_source _ x
  have hEm := isEMorphismOn_chartSource hiso
  obtain ⟨g, O, Ug, f, c, hc, hxO, hOV, hUo, hf, hgr⟩ :=
    hT.locGraph (e x) ⟨⟨x, ⟨hx, hxe⟩, rfl⟩, hxV⟩
  -- (1) the graph in the frame `g`
  have hgraph : ∀ w : Minkowski d, g⁻¹ • w ∈ (O : Set (Minkowski d)) →
      (e.symm (g⁻¹ • w) ∈ H ↔ w ∈ graphOver Ug f) := by
    intro w hwO
    have hwt : g⁻¹ • w ∈ e.target := hVt (hOV hwO)
    have hgw : g • (g⁻¹ • w) = w := smul_inv_smul g w
    constructor
    · intro hH
      have hmem : g⁻¹ • w ∈ (e '' (H ∩ e.source) ∩ (V : Set (Minkowski d))) ∩
          (O : Set (Minkowski d)) :=
        ⟨⟨⟨_, ⟨hH, e.map_target hwt⟩, e.right_inv hwt⟩, hOV hwO⟩, hwO⟩
      have : w ∈ g • ((e '' (H ∩ e.source) ∩ (V : Set (Minkowski d))) ∩
          (O : Set (Minkowski d))) := ⟨_, hmem, hgw⟩
      rw [hgr] at this
      exact this.2
    · intro hw
      have : w ∈ g • (O : Set (Minkowski d)) ∩ graphOver Ug f := ⟨⟨_, hwO, hgw⟩, hw⟩
      rw [← hgr] at this
      obtain ⟨t, ⟨⟨⟨m, ⟨hmH, hms⟩, rfl⟩, -⟩, -⟩, hgt⟩ := this
      have hm : e m = g⁻¹ • w := by rw [← hgt, inv_smul_smul]
      rw [← hm, e.left_inv hms]; exact hmH
  -- (2) strong causality: a causally convex `Vc ∋ x` inside the chart piece over `O`
  have hArc := flatCausality_causallyArcConnected d M
  have hSC := Causality.GloballyHyperbolic.stronglyCausal (tarentin_flatCausality (X := M)) hGH
  let OM : Opens M := ⟨e.source ∩ e ⁻¹' (O : Set (Minkowski d)), e.isOpen_inter_preimage O.isOpen⟩
  have hOMs : OM ≤ chartSource e := fun n hn => hn.1
  have hxOM : x ∈ OM := ⟨hxe, hxO⟩
  obtain ⟨Vc, hVcn, hVcO, hVcc⟩ := hSC x OM (OM.isOpen.mem_nhds hxOM)
  set p₀ : Minkowski d := g • e x with hp₀
  have hopen : IsOpen ((fun w : Minkowski d => g⁻¹ • w) ⁻¹' (e '' (e.source ∩ interior Vc))) :=
    (e.isOpen_image_source_inter isOpen_interior).preimage (continuous_const_smul g⁻¹)
  obtain ⟨β, hβ, hβsub⟩ := Metric.isOpen_iff.1 hopen p₀
    (show g⁻¹ • p₀ ∈ e '' (e.source ∩ interior Vc) by
      rw [hp₀, inv_smul_smul]
      exact ⟨x, ⟨hxe, mem_interior_iff_mem_nhds.2 hVcn⟩, rfl⟩)
  have hball : ∀ w ∈ ball p₀ β, e.symm (g⁻¹ • w) ∈ e.source ∧ e.symm (g⁻¹ • w) ∈ Vc ∧
      e (e.symm (g⁻¹ • w)) = g⁻¹ • w ∧ g⁻¹ • w ∈ (O : Set (Minkowski d)) := by
    intro w hw
    obtain ⟨n, ⟨hns, hnV⟩, hn⟩ := hβsub hw
    have hn : e n = g⁻¹ • w := hn
    have h1 : e.symm (g⁻¹ • w) = n := by rw [← hn, e.left_inv hns]
    have hnV' : n ∈ Vc := interior_subset hnV
    refine ⟨by rw [h1]; exact hns, by rw [h1]; exact hnV', by rw [h1, hn], ?_⟩
    rw [← hn]; exact (hVcO hnV').2
  -- (3) the local graph is a strict contraction on a small ball
  have hp₀g : p₀ ∈ graphOver Ug f := by
    refine (hgraph p₀ (hball p₀ (mem_ball_self hβ)).2.2.2).1 ?_
    rw [hp₀, inv_smul_smul, e.left_inv hxe]; exact hx
  obtain ⟨δ₁, hδ₁, hδ₁U⟩ := Metric.isOpen_iff.1 hUo p₀.2 hp₀g.1
  set δ : ℝ := min δ₁ (β / 4) with hδ
  have hδ0 : 0 < δ := lt_min hδ₁ (by positivity)
  have hδδ₁ : δ ≤ δ₁ := min_le_left _ _
  have hδβ : δ ≤ β / 4 := min_le_right _ _
  have hc1 : (c : ℝ) < 1 := by exact_mod_cast hc
  have hGstrict : ∀ y ∈ ball p₀.2 δ, ∀ y' ∈ ball p₀.2 δ, y ≠ y' → |f y - f y'| < ‖y - y'‖ := by
    intro y hy y' hy' hne
    have hyU : y ∈ Ug := hδ₁U (ball_subset_ball hδδ₁ hy)
    have hyU' : y' ∈ Ug := hδ₁U (ball_subset_ball hδδ₁ hy')
    have h := hf.dist_le_mul y hyU y' hyU'
    rw [Real.dist_eq, dist_eq_norm] at h
    have hpos : 0 < ‖y - y'‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
    calc |f y - f y'| ≤ c * ‖y - y'‖ := h
      _ < 1 * ‖y - y'‖ := mul_lt_mul_of_pos_right hc1 hpos
      _ = ‖y - y'‖ := one_mul _
  -- (4) the entire strict contraction `F`, and the local domain `W₀` of its graph
  obtain ⟨F, hF, hFb, hFG⟩ := exists_isStrictContraction_extension hδ0 hGstrict
  have hlip := hF.lipschitzWith
  set r : ℝ := δ / 4 with hr
  have hr0 : 0 < r := by positivity
  have hFy₀ : F p₀.2 = p₀.1 :=
    (hFG p₀.2 (by rw [sub_self, norm_zero]; positivity)).trans hp₀g.2.symm
  set W₀ : Opens (Minkowski d) := graphLocalDomain F p₀.2 r with hW₀
  have hWsub : ∀ q ∈ W₀, |q.1 - p₀.1| < 2 * r ∧ ‖q.2 - p₀.2‖ < r := by
    intro q hq
    obtain ⟨h1, h2⟩ := graphLocalDomain_subset hq
    have h3 := abs_sub_le_norm_of_lipschitzWith_one hlip q.2 p₀.2
    rw [hFy₀] at h3
    simp only [timeSub] at h2
    refine ⟨?_, h1⟩
    calc |q.1 - p₀.1| = |(q.1 - F q.2) + (F q.2 - p₀.1)| := by ring_nf
      _ ≤ |q.1 - F q.2| + |F q.2 - p₀.1| := abs_add_le _ _
      _ < 2 * r := by linarith
  have hWB : ∀ q ∈ W₀, q ∈ ball p₀ β := fun q hq => by
    rw [mem_ball, Prod.dist_eq, Real.dist_eq, dist_eq_norm]
    exact max_lt (by linarith [(hWsub q hq).1]) (by linarith [(hWsub q hq).2])
  have hgraphW : ∀ q ∈ W₀, (e.symm (g⁻¹ • q) ∈ H ↔ timeSub F q = 0) := by
    intro q hq
    have h2 := (hWsub q hq).2
    have hqU : q.2 ∈ Ug := hδ₁U (by rw [mem_ball, dist_eq_norm]; linarith)
    have hFq : F q.2 = f q.2 := hFG q.2 (by linarith)
    rw [hgraph q (hball q (hWB q hq)).2.2.2, timeSub, sub_eq_zero, hFq]
    exact ⟨fun h => h.2, fun h => ⟨hqU, h⟩⟩
  -- (5) the neighbourhood `U` of `x` in `M`
  let U : Opens M := ⟨e.source ∩ e ⁻¹' (isomImage g⁻¹ W₀ : Set (Minkowski d)),
    e.isOpen_inter_preimage (isomImage g⁻¹ W₀).isOpen⟩
  have hUs : U ≤ chartSource e := fun n hn => hn.1
  have hUfacts : ∀ n ∈ U, g • e n ∈ W₀ ∧ n ∈ Vc ∧ (n ∈ H ↔ timeSub F (g • e n) = 0) := by
    intro n hn
    have hq : g • e n ∈ W₀ := mem_isomImage_inv_iff.1 hn.2
    have hb := hball _ (hWB _ hq)
    have hgr' := hgraphW _ hq
    rw [inv_smul_smul, e.left_inv hn.1] at hb hgr'
    exact ⟨hq, hb.2.1, hgr'⟩
  have hWt : ((isomImage g⁻¹ W₀ : Opens (Minkowski d)) : Set (Minkowski d)) ⊆ e.target := by
    intro q hq
    have hq' : g • q ∈ W₀ := mem_isomImage_inv_iff.1 hq
    have hb := hball _ (hWB _ hq')
    rw [inv_smul_smul] at hb
    rw [← hb.2.2.1]; exact e.map_source hb.1
  have hUimg : ((isomImage g⁻¹ W₀ : Opens (Minkowski d)) : Set (Minkowski d)) = e '' U := by
    ext q
    constructor
    · intro hq
      refine ⟨e.symm q, ⟨e.map_target (hWt hq), ?_⟩, e.right_inv (hWt hq)⟩
      show e (e.symm q) ∈ isomImage g⁻¹ W₀
      rw [e.right_inv (hWt hq)]; exact hq
    · rintro ⟨n, hn, rfl⟩; exact hn.2
  have hchartU : chartImage e U = isomImage g⁻¹ W₀ :=
    SetLike.coe_injective (by rw [coe_chartImage_of_le hUs, ← hUimg])
  have hAimg : e '' (H ∩ U) = (fun p => g⁻¹ • p) '' (graph F ∩ W₀) := by
    ext q
    constructor
    · rintro ⟨n, ⟨hnH, hnU⟩, rfl⟩
      obtain ⟨hW, -, hiff⟩ := hUfacts n hnU
      exact mem_image_inv_smul_iff.2 ⟨mem_graph_iff_timeSub.2 (hiff.1 hnH), hW⟩
    · intro hq
      obtain ⟨hqg, hqW⟩ := mem_image_inv_smul_iff.1 hq
      have hqW' : q ∈ isomImage g⁻¹ W₀ := mem_isomImage_inv_iff.2 hqW
      have hnU : e.symm q ∈ U := ⟨e.map_target (hWt hqW'), by
        show e (e.symm q) ∈ isomImage g⁻¹ W₀
        rw [e.right_inv (hWt hqW')]; exact hqW'⟩
      refine ⟨e.symm q, ⟨(hUfacts _ hnU).2.2.2 ?_, hnU⟩, e.right_inv (hWt hqW')⟩
      rw [e.right_inv (hWt hqW')]; exact mem_graph_iff_timeSub.1 hqg
  have hxU : x ∈ U := ⟨hxe, by
    show e x ∈ isomImage g⁻¹ W₀
    refine mem_isomImage_inv_iff.2 ?_
    rw [← hp₀]
    exact mem_interior_graphLocalSet_of_graph hF (by rw [timeSub, hFy₀, sub_self])
      (by rw [sub_self, norm_zero]; exact hr0)⟩
  have hgle : ∀ a b : Minkowski d, (minkowski d).le ⊤ a b → (minkowski d).le ⊤ (g • a) (g • b) :=
    fun a b hab => by
      have := (le_iff_le_isomImage g ⊤ a b).1 hab
      rwa [isomImage_top] at this
  refine ⟨U, hxU, ⟨fun _ _ => trivial, fun p hp q hq r' hr' => ?_⟩, ?_, ?_, ?_⟩
  · -- causally convex
    obtain ⟨hpr, hrq⟩ := Causality.mem_diamond.1 hr'
    have hpV := (hUfacts p hp).2.1
    have hqV := (hUfacts q hq).2.1
    have hrV : r' ∈ Vc := hVcc.2 p hpV q hqV hr'
    have hrO : r' ∈ OM := hVcO hrV
    have h1 := Causality.le_of_causallyConvexIn hArc hVcc hVcO hpV hrV hpr
    have h2 := Causality.le_of_causallyConvexIn hArc hVcc hVcO hrV hqV hrq
    have h1' := (minkowski d).le_mono le_top (((hiso OM hOMs p (hVcO hpV) r' hrO).1).1 h1)
    have h2' := (minkowski d).le_mono le_top (((hiso OM hOMs r' hrO q (hVcO hqV)).1).1 h2)
    exact ⟨hOMs hrO, mem_isomImage_inv_iff.2 (graphLocalDomain_convex hF (hUfacts p hp).1
      (hUfacts q hq).1 (hgle _ _ h1') (hgle _ _ h2'))⟩
  · -- Cauchy
    have hC := isCauchySurfaceOn_inter_opens
      (isCauchySurfaceOn_graphLocalDomain (y₀ := p₀.2) (r := r) hF hFb)
    have hC' : (minkowski d).IsCauchySurfaceOn (isomImage g⁻¹ W₀)
        ((fun p => g⁻¹ • p) '' (graph F ∩ W₀)) :=
      ((isom_isEMorphism g⁻¹).isCauchySurfaceOn_image_iff (MulAction.injective g⁻¹).injOn le_top
        rfl inter_subset_right).1 hC
    rw [← hAimg] at hC'
    exact (hEm.isCauchySurfaceOn_image_iff e.injOn hUs hUimg inter_subset_right).2 hC'
  · -- the future side
    have heq : (flatCausality d M).Jplus U (H ∩ U) \ H =
        e.source ∩ e ⁻¹' ((fun q : Minkowski d => g • q) ⁻¹'
          ((W₀ : Set (Minkowski d)) ∩ {q | 0 < timeSub F q})) := by
      ext n
      rw [Set.mem_sdiff, mem_Jplus_chart_iff hiso hUs inter_subset_right, hchartU, hAimg,
        Jplus_isomImage, Jplus_graphLocalDomain hF, mem_image_inv_smul_iff]
      constructor
      · rintro ⟨⟨hnU, hnW, hT⟩, hnH⟩
        exact ⟨hnU.1, hnW, lt_of_le_of_ne hT fun h => hnH ((hUfacts n hnU).2.2.2 h.symm)⟩
      · rintro ⟨hns, hnW, hT⟩
        have hnU : n ∈ U := ⟨hns, mem_isomImage_inv_iff.2 hnW⟩
        exact ⟨⟨hnU, hnW, hT.le⟩, fun hnH => hT.ne' ((hUfacts n hnU).2.2.1 hnH)⟩
    rw [heq]
    exact e.isOpen_inter_preimage ((W₀.isOpen.inter
      (isOpen_lt continuous_const (continuous_timeSub hlip))).preimage (continuous_const_smul g))
  · -- the past side
    have heq : (flatCausality d M).Jminus U (H ∩ U) \ H =
        e.source ∩ e ⁻¹' ((fun q : Minkowski d => g • q) ⁻¹'
          ((W₀ : Set (Minkowski d)) ∩ {q | timeSub F q < 0})) := by
      ext n
      rw [Set.mem_sdiff, mem_Jminus_chart_iff hiso hUs inter_subset_right, hchartU, hAimg,
        Jminus_isomImage, Jminus_graphLocalDomain hF, mem_image_inv_smul_iff]
      constructor
      · rintro ⟨⟨hnU, hnW, hT⟩, hnH⟩
        exact ⟨hnU.1, hnW, lt_of_le_of_ne hT fun h => hnH ((hUfacts n hnU).2.2.2 h)⟩
      · rintro ⟨hns, hnW, hT⟩
        have hnU : n ∈ U := ⟨hns, mem_isomImage_inv_iff.2 hnW⟩
        exact ⟨⟨hnU, hnW, hT.le⟩, fun hnH => hT.ne ((hUfacts n hnU).2.2.1 hnH)⟩
    rw [heq]
    exact e.isOpen_inter_preimage ((W₀.isOpen.inter
      (isOpen_lt (continuous_timeSub hlip) continuous_const)).preimage (continuous_const_smul g))

end LocCauchy

/-! ### The smoothing step, lemma K, and the theorem -/

/-- **The smoothing step proper, in dimension `d + 1 ≥ 1`** (Barbot's `n ≥ 2`): a NONEMPTY
COMPACT spacelike Lipschitz `H` (the one assertion of this module that is not proved). Neither
connectedness (`exists_isConnected_isSpacelikeLipschitz_subset` takes a component) nor the Cauchy
property (lemma K, `isCauchySurface_of_isSpacelikeLipschitz`) is part of it, and `d = 0` is closed
by a point (`isSpacelikeLipschitz_singleton_zero`). -/
theorem exists_nonempty_isSpacelikeLipschitz_succ (M : FlatSpacetime.{u} (d + 1)) (_hGH : GH M)
    {S : Set M} (_hS : (flatCausality (d + 1) M).IsCauchySurface S) (_hSc : IsCompact S)
    (_hac : (flatCausality (d + 1) M).IsAcausal S) :
    ∃ H : Set M, H.Nonempty ∧ IsCompact H ∧ IsSpacelikeLipschitz (d + 1) H := by
  sorry -- SORRY(bthm:cauclo, compact ⇒ complete, smoothing, d ≥ 1): a NONEMPTY COMPACT hypersurface that is spacelike Lipschitz (`c < 1` point-locally in charts). Connectedness is NOT asked (`exists_isConnected_isSpacelikeLipschitz_subset`, proved: a component of a spacelike Lipschitz set is spacelike Lipschitz, the set being locally a graph over a ball), nor the Cauchy property (lemma K, proved), and `d = 0` is closed (a point, `isSpacelikeLipschitz_singleton_zero`). `S` itself does not qualify: acausal only makes it strictly contracting in charts, the slope may tend to 1 (in the flat torus spacetime `Minkowski 1 / ⟨(0, 2π)⟩`, Barbot's `𝐌²`, the graph of `sin` is an acausal compact Cauchy surface with no `c < 1` at `x = 0`, in any frame). Routes checked and refused (2026-11-01 closer pass): (A) Barbot's cosmological time (`Flat.Cosmological`, `Lox/LevelComplete`, Cor 4.13 proved) gives spacelike Lipschitz level sets only on a regular domain `Ω` with `M = Γ\Ω`; for a Cauchy-compact `M` that presentation is Theorem A's conclusion, whose input is the Cauchy-completeness this lemma feeds (`Develop.DevelopsCC` — injectivity of `𝒟` on the lift of `S` and (CC′) — is produced only by `exists_developsCC_of_isCauchyComplete'`), so the route is circular; (B) a Γ-invariant max of finitely many hyperboloid graphs over a compact fundamental domain in `𝐌ⁿ` needs the same injectivity of `𝒟` to place the pieces in one copy of `𝐌ⁿ` (circular); done directly in `M` it is the envelope below. Missing: a global smoothing of `S` in `M` — the envelope of the future Lorentzian ε-hyperboloids of the points of `S` (or, frame-free, the future boundary of `⋃ᵢ J⁺(Pᵢ)` for finitely many short hyperboloid caps `Pᵢ`), which in the chart at a point of `S` is the graph of `x ↦ inf_y (G y + √(ε² + ‖x − y‖²))` over `‖x − y‖ ≤ δ` (`G` the local strict contraction), `c`-Lipschitz with `c = δ/√(ε² + δ²) < 1` as soon as the acausality gap `‖x − y‖ − |G x − G y| ≥ η > ε` holds for `‖x − y‖ ≥ δ` (compactness of `S`). The library lacks (i) an intrinsic definition of that envelope on `M` (no Lorentzian time separation on `M`; a transition is one isometry only on a connected overlap, and boosts do not preserve Euclidean smallness, so the hyperboloid pieces must be cut by a Lebesgue number of a finite cover of `S` by charts each inside a larger convex chart), (ii) the locality statement that near a point of the envelope only the hyperboloids of nearby points of `S` contribute (the past of a point just above `S`, down to `S`, is small: `graphCone_past` in one chart, globally the shrinking of `J⁻(p) ∩ J⁺(S)` to `{x}` as `p ↓ x`, from compact diamonds and the closedness of `J^±(S)`), (iii) compactness (a closed subset of the compact slab `J⁺(S) ∩ J⁻(φ_T(S))`). Bernal–Sánchez's smooth spacelike Cauchy surfaces are not in the library either

/-- **A compact connected spacelike Lipschitz hypersurface from a compact acausal topological
Cauchy surface** (the smoothing step). Its Cauchy property is NOT part of the assertion: lemma K
gives it (`isCauchySurface_of_isSpacelikeLipschitz`). Proved for `d = 0` (a point,
`isSpacelikeLipschitz_singleton_zero`); for `d + 1` from the module's one `sorry`,
`exists_nonempty_isSpacelikeLipschitz_succ` (a nonempty compact spacelike Lipschitz `H`), by
taking a connected component (`exists_isConnected_isSpacelikeLipschitz_subset`). -/
theorem exists_isSpacelikeLipschitz_of_isCompact_cauchy (M : FlatSpacetime.{u} d) (_hGH : GH M)
    {S : Set M} (_hS : (flatCausality d M).IsCauchySurface S) (_hSc : IsCompact S)
    (_hac : (flatCausality d M).IsAcausal S) :
    ∃ H : Set M, IsCompact H ∧ IsConnected H ∧ IsSpacelikeLipschitz d H := by
  cases d with
  | zero =>
    obtain ⟨x⟩ := (inferInstance : Nonempty M)
    exact ⟨{x}, isCompact_singleton, isConnected_singleton, isSpacelikeLipschitz_singleton_zero x⟩
  | succ d =>
    obtain ⟨H, hne, hHc, hL⟩ := exists_nonempty_isSpacelikeLipschitz_succ M _hGH _hS _hSc _hac
    obtain ⟨H₀, -, hc, hconn, hL₀⟩ := exists_isConnected_isSpacelikeLipschitz_subset hHc hne hL
    exact ⟨H₀, hc, hconn, hL₀⟩

/-- **Lemma K for spacelike Lipschitz hypersurfaces**: in a GH flat spacetime with an acausal
Cauchy surface `S`, a compact connected spacelike Lipschitz `H` is a Cauchy surface (`Causality.
isCauchySurface_of_isLocallyCauchyTwoSided`, along the splitting of `M` along `S` given by the
chronal causal flow of every flat spacetime, `flat_hasChronalCausalFlow`, and
`isLocallyCauchyTwoSided_of_isSpacelikeLipschitz`). -/
theorem isCauchySurface_of_isSpacelikeLipschitz {M : FlatSpacetime.{u} d} (hGH : GH M)
    {S : Set M} (hS : (flatCausality d M).IsCauchySurface S)
    (hac : (flatCausality d M).IsAcausal S) {H : Set M} (hHc : IsCompact H)
    (hHconn : IsConnected H) (hL : IsSpacelikeLipschitz d H) :
    (flatCausality d M).IsCauchySurface H := by
  have hflow : (flatCausality d M).HasChronalCausalFlow := flat_hasChronalCausalFlow
  obtain ⟨φ, hφ, -⟩ := id hflow
  obtain ⟨ψ, hψ⟩ := flat_exists_isCauchySplitting hflow hGH.1 hS hac
  exact Causality.isCauchySurface_of_isLocallyCauchyTwoSided (tarentin_flatCausality (X := M)) hGH
    (flatCausality_causallyArcConnected d M) (jminus_ne_singleton_of_isCausalFlow hφ)
    (jplus_ne_singleton_of_isCausalFlow hφ) (curvesExtend_of_isCausalFlow hφ) hψ hHc hHconn
    (isLocallyCauchyTwoSided_of_isSpacelikeLipschitz hGH hL)

/-- **A Cauchy-compact GH flat spacetime is Cauchy-complete** (the input of Theorem A in Theorem
B's proof, l.3536: "Reconsider the proof above when $M$ is assumed Cauchy-compact"). From a
compact connected spacelike Lipschitz `H` (`exists_isSpacelikeLipschitz_of_isCompact_cauchy`, which
rests for `d ≥ 1` on the module's one `sorry`): it is a Cauchy surface (lemma K, `isCauchySurface_of_isSpacelikeLipschitz`),
its glued length space is compact, hence complete (`completeSpace_inducedLengthSpace_of_isCompact`),
and its length topology is finer than the topology of `M` (`continuous_inducedLengthSpace_toSubtype`). -/
theorem isCauchyComplete_of_isCompact_cauchy (M : FlatSpacetime.{u} d) (hGH : GH M)
    {S : Set M} (hS : (flatCausality d M).IsCauchySurface S) (hSc : IsCompact S)
    (hac : (flatCausality d M).IsAcausal S) : IsCauchyComplete d M := by
  obtain ⟨H, hHc, hHconn, hL⟩ := exists_isSpacelikeLipschitz_of_isCompact_cauchy M hGH hS hSc hac
  exact ⟨H, isCauchySurface_of_isSpacelikeLipschitz hGH hS hac hHc hHconn hL, hL,
    completeSpace_inducedLengthSpace_of_isCompact hHc hL, continuous_inducedLengthSpace_toSubtype hL⟩

/-- Test of the intended use at `Classification.isCauchyComplete_of_cauchyCompact`. -/
example (M : FlatSpacetime.{u} d) (_hGH : GH M) (_hC : CauchyCompact M) : IsCauchyComplete d M := by
  obtain ⟨S, hS, hSc, hac⟩ := _hC; exact isCauchyComplete_of_isCompact_cauchy M _hGH hS hSc hac

end Causal.Flat.Cla
