import CausalScaffold.Flat.InducedLength
import CausalScaffold.Flat.FlatSpacetime
import CausalScaffold.Flat.LipschitzGraph
import CausalScaffold.Flat.Developing
import CausalScaffold.Splitting

/-!
# `CausalScaffold.Flat.CauchyComplete` — Cauchy-completeness of a flat spacetime, and the bridge to (CC′)

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §2.4 and
§8. Labels certified (no `sorry` beneath, in the DEC-35 reading, hypotheses only ⚠ weakened):
**`bprop:project`** — `GHFspace.tex:2232` (l.2232–2261); **`bcor:quoiso`** — `GHFspace.tex:2277`
(l.2277–2290). Cited UNMARKED: `[2.4]` Cauchy-complete — l.551–558 (prose, DEC-35, a reading);
`[8.G]` the graph remark — l.2307–2309 (prose, proved); `bcor:quo`'s last clause ("intersects
every timelike geodesic") — l.2263–2271 (proved; the rest of `bcor:quo` is not stated). Design:
`docs/BARBOT-WAVE3.md` §3 "The metric notion", "Prop 8.1", "Cor 8.3", "The bridge"; defects W2,
W3, W5, W6; the contract with gx, `docs/BARBOT.md` (a)–(f).

> A GH spacetime is *Cauchy-complete* if it admits a Cauchy hypersurface where the ambiant
> lorentzian metric restricts as a complete riemanian metric. (l.551–553)

> Let $\Delta$ be a timelike direction in ${\bf M}^{n}$. Let $Q(\Delta)$ be the quotient linear
> space ${\bf M}^{n} \slash \Delta$, and $\pi: {\bf M}^{n} \rightarrow Q(\Delta)$ the quotient map.
> Equip $Q(\Delta)$ with the metric for which $\pi$ restricted to every spacelike hyperplane
> orthogonal to $\Delta$ is an isometry. Then, $\pi \circ {\mathcal D} \circ \tilde{f}$ is a
> homeomorphism. (l.2235–2240)

> Let $P_{0}$ be a lightlike affine hyperplane of ${\bf M}^{n}$, with direction the orthogonal of a
> lightlike direction $\Delta_{0}$. Then, either $\widetilde{S}$ does not intersect $P_{0}$, or it
> intersects every affine line with direction $\Delta_{0}$ contained in $P_{0}$. (l.2280–2284)

> As an immediate corollary of proposition \ref{project}, we obtain that $\widetilde{S}$ is the
> graph of a contracting map $\varphi: {\mathbb R}^{n-1} \rightarrow {\mathbb R}$. (l.2307–2309)

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; `Minkowski d` has `d` spatial
dimensions, so Barbot's `n` is `d + 1`, `ℝ^{n−1}` is `EuclideanSpace ℝ (Fin d)`, and
`Q(Δ) ≅ ℝᵈ` is modelled by the hyperplane `Δ^⊥` (`orthSub Δ`).

## Main declarations
* **The gluing** (contract (a)–(e), reusable by gx). A *local developing system* is
  `φ : X → X → 𝐌ⁿ` (`φ x` is the chart at `x`). `localDensity φ c t = √(minkQ (d/ds φ (c t) (c s)))`
  at `s = t` — the chart is taken at the point itself, so no subdivision is chosen;
  `localLength`, `LocLipAt`/`IsLocLip` (Lipschitz in charts), `pathLength`, and
  `LocalLengthSpace φ` with `edist x y = ⨅ γ, pathLength φ γ` (a `PseudoEMetricSpace`, its three laws
  proved: `pathLength_refl`, `pathLength_symm`, `pathLength_trans`).
  - `InducedLengthSpace d S` for `S ⊆ M`, `M` charted over `𝐌ⁿ`: `φ = chartSys d S` (charts `chartAt`).
  - `localDensity_chartSys_eq`: (b)+(c) — the density is the same in EVERY atlas chart (gx groupoid).
  - `localLength_chartSys_minkowski`: (d) — on `𝐌ⁿ` it is `InducedLength.lorentzLength`.
  - **The reuse link with `InducedLength`** (for gx): `isLocLip_pulled_iff` (Lipschitz in charts
    along a path ⇔ a global Lipschitz bound, by compactness of `[0, 1]`); for `S ⊆ 𝐌ⁿ`,
    `isLocLip_chartSys_minkowski_iff` (⇔ `IsLipschitzCurve`), `pathLength_chartSys_minkowski`
    (`pathLength = lengthOn S ⊤`) and `edist_inducedLengthSpace_minkowski` (the two `edist`s agree).
  - `PulledLength F`: `φ = fun _ => F`, the length pulled back along `F : X → 𝐌ⁿ` (`localLength_pulled`).
* `IsSpacelikeLipschitz d S` (contract (f): `c < 1` per point, in the chart at the point) and
  **`IsCauchyComplete d M`**: `∃ S` Cauchy, spacelike Lipschitz, `CompleteSpace (InducedLengthSpace d S)`,
  and the topology-compatibility field (W3).
* `SpacelikeDevelopment F` (Barbot's `𝒟 ∘ f̃`), `projAlong Δ` (`π`), `projAlong_eq_iff`.
* **Non-vacuity** (kb/0011, proved): `completeSpace_pulledLength_slice` (with
  `spacelikeDevelopment_slice`, the hypotheses of 8.1/8.3 are inhabited: the slice `t = 0` of `𝐌ⁿ`,
  pulled length = Euclidean distance, `edist_pulledLength_slice`); `isCauchyComplete_minkowski`
  (`𝐌ⁿ` is Cauchy-complete through that slice, `edist_inducedLengthSpace_slice`,
  `continuous_toSubtype_slice`).
* `isHomeomorph_of_isCoveringMap` (proved): a covering of a simply connected, locally
  path-connected space by a connected one is a homeomorphism.
* **The lifting machinery** (proved, shared by 8.1 and 8.3): `exists_lift_segment_of_mapClusterPt`
  (maximal lifts of a straight segment through a local homeomorphism of a Hausdorff space, given
  cluster points at the ends), `isHomeomorph_of_lift_segment` (segment lifting onto a normed space
  ⇒ homeomorphism, by the radial lift); for a linear `P : 𝐌ⁿ → E`: `edist_lift_le_of_proj` (the
  pulled length of a lift is bounded by the segment), `SpacelikeDevelopment.tendsto_lift_of_proj`
  (completeness gives the endpoint), `SpacelikeDevelopment.continuous_toSpace` (the pulled-length
  topology is finer than `X`'s, by a first-exit argument), `exists_chart` / `exists_chart_of_proj`
  (`P ∘ F` is a local homeomorphism, by the intermediate value theorem along `Δ`-lines,
  `IsSpacelikeLipschitzIn.eventually_exists_add_smul_mem`, `Δ ≠ 0` causal).
* `bprop_project` (8.1): `projAlong Δ ∘ F` is a homeomorphism; from `isCoveringMap_projAlong_comp`
  (PROVED: charts, `π` does not decrease `minkQ`, segment lifting) and the lemma above.
* `isEntireAcausalGraph_range` ([8.G], Cor 8.2's last clause), PROVED from 8.1: `range F` is an
  entire acausal graph — achronal by injectivity of `π`, and null pairs excluded by
  `IsSpacelikeLipschitzIn.not_eventually_add_smul_mem` (no germ of null segment, `c < 1`) through
  `lipschitzWith_one_segment`; also `injective_of_complete`, `exists_graph`.
* `bcor_quoiso` (8.3): `NullSaturated (range F)` (PROVED, W6): lift, through the projection
  `nullProj e` along `(1, e)`, the segments of a level of `P₀`, where `minkQ` is the squared
  Euclidean speed (`minkQ_eq_nullProj`).
* **The bridge** `developsCC_of_isCauchyComplete`: for GH `M`, `S` as in `IsCauchyComplete` and any
  developing map `dev`: `S` Cauchy, `dev` injective on `Ŝ = p⁻¹(S)`, `dev '' Ŝ` an entire acausal
  graph meeting every timelike line, and `NullSaturated`. ASSEMBLED (proved) from 8.1, 8.3, B1, B2,
  B3; `t2Space_universalCover` is proved; its only `sorry` is B1's splitting.
  `exists_developsCC_of_isCauchyComplete`.
  - B2 (`dev|Ŝ` is a spacelike development) PROVED: `spacelikeDevelopment_restrict`, through
    `IsSpacelikeLipschitzIn.restrict`.
  - B3 (completeness lifts to `Ŝ`) PROVED: `completeSpace_pulledLength_restrict`. The pulled length
    of a path of `Ŝ` is the glued length of its projection (`pathLength_pulled_eq_of_local`, from
    `exists_dev_eq_smul_chart` and the pointwise `locLipAt_pulled_iff_of_eventually`), so `proj`
    is `1`-Lipschitz; a path is longer than the distance to each of its points
    (`LocalLengthSpace.edist_le_pathLength`), so by `htop` short paths near the limit stay in an
    evenly covered `U`; the Cauchy tail lies on one sheet (its index is constant along short
    paths), and the sheet's section lifts short paths to the limit.
  - B1 (`Ŝ` connected) REDUCED: `connectedSpace_preimage_cauchy` is proved from
    `connectedSpace_preimage_of_splitting` (proved: a slice `S × {0}` of a homeomorphism
    `S × ℝ ≃ₜ Y` lifts to a connected set of the universal cover) and the tagged
    `exists_splitting_of_isCauchySurface` (a variant of the homeomorphism half of Prop 8.11,
    class E). That lemma is in turn reduced, by the proved
    `exists_splitting_of_hasChronalCausalFlow`, to target 4 (`Flat.flat_hasChronalCausalFlow`,
    `Splitting.lean`, now proved) and acausality of `S`, now proved too
    (`isAcausal_of_isCauchySurface_of_hasChronalCausalFlow`, from
    `flatCausality_causallyArcConnected` — chart transport of curves, `curveOn_chart_symm`,
    `causallyArcConnectedOn_of_chartIso`, then absolute minimality — and
    `curvesExtend_of_isCausalFlow`, through `inextensible_univ_of_not_tendsto` and
    `not_tendsto_of_eventuallyEq_flow`). The one input left is `[SecondCountableTopology M]`,
    which `flat_hasChronalCausalFlow` asks and `FlatSpacetime` does not carry.

## Hypothesis checklist
| paper hypothesis | here |
|---|---|
| `M` GH (l.551) | ✓ carried in the bridge (`GH M`), in ETT's reading (BARBOT-THEOREMS §1, "ETT's is used"); classically implied by `hS` (Barbot's GH is the existence of a Cauchy surface), but in the library Geroch (iii)⇒(i) is itself a `sorry`, so it is carried rather than derived; consumed only by B1 (through `exists_splitting_of_isCauchySurface`). `IsCauchyComplete` alone does not ask it, as `AMGH` composes them |
| a Cauchy hypersurface (l.551) | ✓ carried: ETT's `IsCauchySurface` |
| "the ambiant lorentzian metric restricts as a riemanian metric" | ⚠ weakened (a reading): point-locally spacelike Lipschitz in flat charts (DEC-31/35), not smooth |
| "complete" | ✓ carried: `CompleteSpace` of the glued length pseudo-emetric; plus the topology field (W3: without spacelikeness the length can vanish; for spacelike `S` the field holds locally, `IsSpacelikeLipschitzIn.isHomeomorph_toSubtype`, its gluing is not proved here) |
| 8.1: `f : S → M` isometric immersion of a complete riemannian hypersurface, `S̃`, `𝒟 ∘ f̃` | ⚠ weakened: any connected T2 `X` (not simply connected), `F` a `SpacelikeDevelopment` (Lipschitz), `PulledLength F` complete; the compatibility of the pulled-length topology with `X`'s is DERIVED (`SpacelikeDevelopment.continuous_toSpace`), not assumed |
| 8.1: `Δ` a timelike direction, `Q(Δ) = 𝐌ⁿ/Δ` with its metric | ✓ carried: `minkQ Δ < 0` (both orientations); `Q(Δ)` is modelled TOPOLOGICALLY by `Δ^⊥` (`π` is the identity on `Δ^⊥`). The paper's metric is `minkQ` restricted to `Δ^⊥` (positive definite); the Lean subtype carries the sup-product metric of `ℝ × ℝᵈ`, equivalent to it but not equal — only the topology enters 8.1's homeomorphism |
| 8.3: same set-up | ⚠ weakened, as for 8.1; `ConnectedSpace X` is in the statement but unused (the proof does not go through 8.1) |

## SCOPE (disclosed)
* **One tagged sorry.** In `exists_splitting_of_isCauchySurface` (tag `bridge-B1`: the splitting
  `M ≅ S × ℝ`, class E), and it is now exactly `SecondCountableTopology M` for a flat spacetime
  (Geroch's paracompactness, not formalized): target 4 and `IsAcausal S` are proved, and the
  splitting follows by the proved `exists_splitting_of_hasChronalCausalFlow`. Everything else is proved:
  the whole length structure and its link to `InducedLength`, `π` and its kernel, 8.1 (covering,
  hence homeomorphism), 8.1 ⇒ the entire acausal graph, 8.3, B1 from the splitting, B2, B3, the
  non-vacuity witnesses, the bridge's assembly.
* 8.1 lifts STRAIGHT segments only (W5: the paper's "distance increasing" bound on the lift of an
  arbitrary path needs it rectifiable), and its "local homeomorphism" step, the inverse function
  theorem in Barbot's smooth setting, is an intermediate value argument along `Δ`-lines here.
  8.3 projects along `Δ₀` onto `ℝᵈ` rather than onto `P₀/Δ₀`, and lifts segments inside one
  level of `P₀`; its "completely similar" is literally the 8.1 machinery (W6).
* B3 does not use `IsSpacelikeLipschitz S` (`hL`, kept in the statement): the transfer of lengths
  only needs `dev` and `proj` to be `(Isom, 𝐌ⁿ)`-morphisms; completeness and `htop` do the rest.
* `IsSpacelikeLipschitz` reads the hypersurface in `chartAt x`; any other atlas chart differs by an
  element of `Isom(𝐌ⁿ)` near `x` (`IsSpacelikeLipschitzIn.smul`), not restated here.
* The paths of `InducedLengthSpace d S` are paths of the subspace `S`; a path is charged `⊤` unless
  it is Lipschitz in charts (`IsLocLip`), as `InducedLength.lengthOn` charges non-Lipschitz curves.
* `DevelopsCC` of `Flat/Develop.lean` (written in parallel) is NOT imported: the bridge states its
  conclusion as the explicit conjunction (Cauchy, `InjOn dev Ŝ`, `IsEntireAcausalGraph`,
  `NullSaturated`); the master connects the two.
* Non-vacuity: `spacelikeDevelopment_slice` + `completeSpace_pulledLength_slice` inhabit the
  hypotheses of 8.1 and 8.3; `isCauchyComplete_minkowski` inhabits `IsCauchyComplete` (and, with
  `gh_minkowskiSpace`, the bridge's). The reuse link with `InducedLength` is proved for subsets of
  `𝐌ⁿ` (one chart); for a general `M` the chart-local comparison is `localDensity_chartSys_eq`
  (the density) and is not restated as an `edist` comparison on chart domains.
* `Σ` is written `S` (Lean keyword).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Written by
WP-32g-CauchyComplete (Barbot campaign, wave 3).
-/

namespace Causal.Flat

open Set TopologicalSpace MeasureTheory Filter Topology
open scoped ENNReal NNReal unitInterval Pointwise

variable {d : ℕ}

/-! ### A. Lengths through a local developing system -/

section LocalLength

variable {X : Type*}

/-- The density of a curve `c : ℝ → X` at `t` for the local developing system `φ`. -/
noncomputable def localDensity (φ : X → X → Minkowski d) (c : ℝ → X) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sqrt (minkQ (deriv (fun s => φ (c t) (c s)) t)))

/-- The length of `c` over `(a, b]`. -/
noncomputable def localLength (φ : X → X → Minkowski d) (c : ℝ → X) (a b : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioc a b, localDensity φ c t

/-- `c` is Lipschitz near `t`, read in the chart `φ (c t)`. -/
def LocLipAt (φ : X → X → Minkowski d) (c : ℝ → X) (t : ℝ) : Prop :=
  ∃ ε > (0 : ℝ), ∃ K : ℝ≥0, LipschitzOnWith K (fun s => φ (c t) (c s)) (Icc (t - ε) (t + ε))

/-- `c` is Lipschitz in charts. -/
def IsLocLip (φ : X → X → Minkowski d) (c : ℝ → X) : Prop := ∀ t, LocLipAt φ c t

/-! #### The density under reparametrisation -/

theorem localDensity_comp_affine (φ : X → X → Minkowski d) (c : ℝ → X) {a : ℝ} (ha : 0 < a)
    (e s : ℝ) :
    localDensity φ (fun u => c (a * u + e)) s =
      ENNReal.ofReal a * localDensity φ c (a * s + e) := by
  have hd : deriv (fun u => φ (c (a * s + e)) (c (a * u + e))) s =
      a • deriv (fun y => φ (c (a * s + e)) (c y)) (a * s + e) := by
    have h2 : deriv (fun y => φ (c (a * s + e)) (c (y + e))) (a * s) =
        deriv (fun z => φ (c (a * s + e)) (c z)) (a * s + e) :=
      deriv_comp_add_const (f := fun z => φ (c (a * s + e)) (c z)) e (a * s)
    have := deriv_comp_mul_left a (fun y => φ (c (a * s + e)) (c (y + e))) s
    rw [h2] at this
    exact this
  change ENNReal.ofReal (Real.sqrt (minkQ (deriv (fun u => φ (c (a * s + e)) (c (a * u + e))) s)))
    = _
  rw [hd, sqrt_minkQ_smul, abs_of_pos ha, ENNReal.ofReal_mul ha.le]
  rfl

theorem localDensity_comp_const_sub (φ : X → X → Minkowski d) (c : ℝ → X) (e s : ℝ) :
    localDensity φ (fun u => c (e - u)) s = localDensity φ c (e - s) := by
  have hd : deriv (fun u => φ (c (e - s)) (c (e - u))) s =
      -deriv (fun y => φ (c (e - s)) (c y)) (e - s) :=
    deriv_comp_const_sub (f := fun y => φ (c (e - s)) (c y)) e s
  simp only [localDensity, hd, minkQ_neg]

/-- The density only sees the curve near the point. -/
theorem localDensity_congr (φ : X → X → Minkowski d) {c c' : ℝ → X} {t : ℝ}
    (h : c =ᶠ[𝓝 t] c') : localDensity φ c t = localDensity φ c' t := by
  have ht : c t = c' t := h.eq_of_nhds
  have : (fun s => φ (c t) (c s)) =ᶠ[𝓝 t] fun s => φ (c' t) (c' s) := by
    filter_upwards [h] with s hs; rw [hs, ht]
  simp only [localDensity, this.deriv_eq]

theorem localDensity_const (φ : X → X → Minkowski d) (x : X) (t : ℝ) :
    localDensity φ (fun _ => x) t = 0 := by
  simp [localDensity]

/-! #### The length -/

theorem localLength_eq_Icc (φ : X → X → Minkowski d) (c : ℝ → X) (a b : ℝ) :
    localLength φ c a b = ∫⁻ t in Icc a b, localDensity φ c t :=
  setLIntegral_congr Ioc_ae_eq_Icc

theorem localLength_add (φ : X → X → Minkowski d) (c : ℝ → X) {a b b' : ℝ} (hab : a ≤ b)
    (hbc : b ≤ b') : localLength φ c a b' = localLength φ c a b + localLength φ c b b' := by
  rw [localLength, ← Ioc_union_Ioc_eq_Ioc hab hbc, lintegral_union measurableSet_Ioc]
  · rfl
  · exact Set.disjoint_left.2 fun t ht ht' => (not_lt.2 ht.2) ht'.1

theorem localLength_congr (φ : X → X → Minkowski d) {c c' : ℝ → X} {a b : ℝ}
    (h : EqOn c c' (Ioo a b)) : localLength φ c a b = localLength φ c' a b := by
  unfold localLength
  rw [setLIntegral_congr Ioo_ae_eq_Ioc.symm, setLIntegral_congr Ioo_ae_eq_Ioc.symm]
  exact setLIntegral_congr_fun measurableSet_Ioo fun t ht =>
    localDensity_congr φ (Filter.eventually_of_mem (Ioo_mem_nhds ht.1 ht.2) h)

theorem localLength_const (φ : X → X → Minkowski d) (x : X) (a b : ℝ) :
    localLength φ (fun _ => x) a b = 0 := by
  simp [localLength, localDensity_const]

theorem localLength_comp_affine (φ : X → X → Minkowski d) (c : ℝ → X) {a : ℝ} (ha : 0 < a)
    (e u v : ℝ) :
    localLength φ (fun s => c (a * s + e)) u v = localLength φ c (a * u + e) (a * v + e) := by
  rw [localLength_eq_Icc, localLength_eq_Icc, ← image_affine_Icc' ha e u v,
    lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Icc (f := fun x => a * x + e)
      (f' := fun _ => a)
      (fun s _ => (((hasDerivAt_id' s).const_mul a).add_const e).hasDerivWithinAt.congr_deriv
        (mul_one a))
      ((strictMono_mul_left_of_pos ha).add_const e).injective.injOn]
  refine setLIntegral_congr_fun measurableSet_Icc fun s _ => ?_
  rw [localDensity_comp_affine φ c ha, abs_of_pos ha]

theorem localLength_comp_const_sub (φ : X → X → Minkowski d) (c : ℝ → X) (e u v : ℝ) :
    localLength φ (fun s => c (e - s)) u v = localLength φ c (e - v) (e - u) := by
  rw [localLength_eq_Icc, localLength_eq_Icc, ← image_const_sub_Icc,
    lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Icc (f := fun x => e - x)
      (f' := fun _ => -1)
      (fun s _ => ((hasDerivAt_id' s).const_sub e).hasDerivWithinAt)
      (sub_right_injective).injOn]
  refine setLIntegral_congr_fun measurableSet_Icc fun s _ => ?_
  simp [localDensity_comp_const_sub]

/-! #### Lipschitz in charts -/

theorem lipschitzOnWith_congr_of_eqOn {Y : Type*} [PseudoEMetricSpace Y] {f g : ℝ → Y}
    {K : ℝ≥0} {s : Set ℝ} (h : EqOn f g s) (hf : LipschitzOnWith K f s) :
    LipschitzOnWith K g s := fun x hx y hy => by rw [← h hx, ← h hy]; exact hf hx hy

theorem LocLipAt.congr {φ : X → X → Minkowski d} {c c' : ℝ → X} {t δ : ℝ} (hδ : 0 < δ)
    (h : EqOn c c' (Icc (t - δ) (t + δ))) (hc : LocLipAt φ c t) : LocLipAt φ c' t := by
  obtain ⟨ε, hε, K, hK⟩ := hc
  have ht : c t = c' t := h ⟨by linarith, by linarith⟩
  refine ⟨min ε δ, lt_min hε hδ, K, lipschitzOnWith_congr_of_eqOn (fun s hs => ?_)
    (hK.mono (Icc_subset_Icc (by linarith [min_le_left ε δ]) (by linarith [min_le_left ε δ])))⟩
  have : s ∈ Icc (t - δ) (t + δ) :=
    ⟨by linarith [hs.1, min_le_right ε δ], by linarith [hs.2, min_le_right ε δ]⟩
  simp only [ht, h this]

theorem LocLipAt.comp_affine {φ : X → X → Minkowski d} {c : ℝ → X} {a : ℝ} (ha : 0 < a)
    {e t : ℝ} (hc : LocLipAt φ c (a * t + e)) : LocLipAt φ (fun s => c (a * s + e)) t := by
  obtain ⟨ε, hε, K, hK⟩ := hc
  refine ⟨ε / a, div_pos hε ha, K * ‖a‖₊, ?_⟩
  have hmaps : MapsTo (fun s => a * s + e) (Icc (t - ε / a) (t + ε / a))
      (Icc (a * t + e - ε) (a * t + e + ε)) := fun s hs => by
    have h1 : a * (ε / a) = ε := mul_div_cancel₀ ε ha.ne'
    constructor <;> nlinarith [hs.1, hs.2]
  have := hK.comp ((lipschitzWith_affine a e).lipschitzOnWith) hmaps
  exact this

theorem LocLipAt.comp_const_sub {φ : X → X → Minkowski d} {c : ℝ → X} {e t : ℝ}
    (hc : LocLipAt φ c (e - t)) : LocLipAt φ (fun s => c (e - s)) t := by
  obtain ⟨ε, hε, K, hK⟩ := hc
  refine ⟨ε, hε, K * ‖(-1 : ℝ)‖₊, ?_⟩
  have hmaps : MapsTo (fun s => -1 * s + e) (Icc (t - ε) (t + ε))
      (Icc (e - t - ε) (e - t + ε)) := fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have := hK.comp ((lipschitzWith_affine (-1) e).lipschitzOnWith) hmaps
  convert this using 2 with s
  simp only [Function.comp_apply]; ring_nf

theorem locLipAt_const (φ : X → X → Minkowski d) (x : X) (t : ℝ) :
    LocLipAt φ (fun _ => x) t :=
  ⟨1, one_pos, 0, (LipschitzWith.const _).lipschitzOnWith⟩

variable [TopologicalSpace X]

/-- The length of a path: its `localLength` over `[0, 1]` if it is Lipschitz in charts, `⊤`
otherwise. -/
noncomputable def pathLength (φ : X → X → Minkowski d) {x y : X} (γ : Path x y) : ℝ≥0∞ := by
  classical exact if IsLocLip φ γ.extend then localLength φ γ.extend 0 1 else ⊤

theorem pathLength_of_isLocLip (φ : X → X → Minkowski d) {x y : X} {γ : Path x y}
    (h : IsLocLip φ γ.extend) : pathLength φ γ = localLength φ γ.extend 0 1 := by
  simp [pathLength, h]

theorem pathLength_of_not_isLocLip (φ : X → X → Minkowski d) {x y : X} {γ : Path x y}
    (h : ¬ IsLocLip φ γ.extend) : pathLength φ γ = ⊤ := by
  simp [pathLength, h]

theorem pathLength_refl (φ : X → X → Minkowski d) (x : X) : pathLength φ (Path.refl x) = 0 := by
  have h : ⇑(Path.refl x).extend = fun _ => x := by rw [Path.refl_extend]; rfl
  rw [pathLength_of_isLocLip φ (by rw [h]; exact locLipAt_const φ x), h, localLength_const]

theorem isLocLip_symm (φ : X → X → Minkowski d) {x y : X} {γ : Path x y}
    (h : IsLocLip φ γ.extend) : IsLocLip φ γ.symm.extend := by
  rw [Path.extend_symm]
  exact fun t => (h (1 - t)).comp_const_sub

theorem pathLength_symm (φ : X → X → Minkowski d) {x y : X} (γ : Path x y) :
    pathLength φ γ.symm = pathLength φ γ := by
  by_cases h : IsLocLip φ γ.extend
  · rw [pathLength_of_isLocLip φ h, pathLength_of_isLocLip φ (isLocLip_symm φ h),
      Path.extend_symm, localLength_comp_const_sub]
    norm_num
  · have h' : ¬ IsLocLip φ γ.symm.extend := fun h' => h (by
      simpa using isLocLip_symm φ h')
    rw [pathLength_of_not_isLocLip φ h, pathLength_of_not_isLocLip φ h']

theorem isLocLip_trans (φ : X → X → Minkowski d) {x y z : X} {γ₁ : Path x y} {γ₂ : Path y z}
    (h₁ : IsLocLip φ γ₁.extend) (h₂ : IsLocLip φ γ₂.extend) :
    IsLocLip φ (γ₁.trans γ₂).extend := by
  intro t
  rcases lt_trichotomy t (1 / 2) with ht | rfl | ht
  · have hA : LocLipAt φ (fun s => γ₁.extend (2 * s + 0)) t := (h₁ _).comp_affine two_pos
    refine hA.congr (δ := 1 / 2 - t) (by linarith) fun s hs => ?_
    simp only [add_zero]
    rw [Path.extend_trans_of_le_half _ _ (by linarith [hs.2])]
  · have hA : LocLipAt φ (fun s => γ₁.extend (2 * s + 0)) (1 / 2) :=
      (h₁ _).comp_affine two_pos
    have hB : LocLipAt φ (fun s => γ₂.extend (2 * s + -1)) (1 / 2) :=
      (h₂ _).comp_affine two_pos
    obtain ⟨ε₁, hε₁, K₁, hK₁⟩ := hA
    obtain ⟨ε₂, hε₂, K₂, hK₂⟩ := hB
    have e1 : γ₁.extend (2 * (1 / 2)) = y := by norm_num
    have e2 : γ₂.extend (2 * (1 / 2) + -1) = y := by norm_num
    have e0 : (γ₁.trans γ₂).extend (1 / 2) = y := by
      rw [Path.extend_trans_of_le_half _ _ le_rfl]; norm_num
    set ε := min ε₁ ε₂
    refine ⟨ε, lt_min hε₁ hε₂, max K₁ K₂, ?_⟩
    refine LipschitzOnWith.Icc_union_Icc (b := 1 / 2) ?_ ?_ (by linarith [lt_min hε₁ hε₂])
      (by linarith [lt_min hε₁ hε₂])
    · refine lipschitzOnWith_congr_of_eqOn (fun s hs => ?_)
        ((hK₁.mono (Icc_subset_Icc (by linarith [min_le_left ε₁ ε₂]) (by linarith))).weaken
          (le_max_left K₁ K₂))
      simp only [add_zero, e1, e0]
      rw [Path.extend_trans_of_le_half _ _ hs.2]
    · refine lipschitzOnWith_congr_of_eqOn (fun s hs => ?_)
        ((hK₂.mono (Icc_subset_Icc (by linarith) (by linarith [min_le_right ε₁ ε₂]))).weaken
          (le_max_right K₁ K₂))
      simp only [e2, e0]
      rw [Path.extend_trans_of_half_le _ _ hs.1, ← sub_eq_add_neg]
  · have hA : LocLipAt φ (fun s => γ₂.extend (2 * s + -1)) t := (h₂ _).comp_affine two_pos
    refine hA.congr (δ := t - 1 / 2) (by linarith) fun s hs => ?_
    rw [Path.extend_trans_of_half_le _ _ (by linarith [hs.1]), ← sub_eq_add_neg]

/-- **Additivity under concatenation.** -/
theorem pathLength_trans (φ : X → X → Minkowski d) {x y z : X} {γ₁ : Path x y} {γ₂ : Path y z}
    (h₁ : IsLocLip φ γ₁.extend) (h₂ : IsLocLip φ γ₂.extend) :
    pathLength φ (γ₁.trans γ₂) = pathLength φ γ₁ + pathLength φ γ₂ := by
  rw [pathLength_of_isLocLip φ (isLocLip_trans φ h₁ h₂), pathLength_of_isLocLip φ h₁,
    pathLength_of_isLocLip φ h₂,
    localLength_add φ _ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)]
  congr 1
  · rw [localLength_congr φ (c' := fun s => γ₁.extend (2 * s + 0)) (fun s hs => by
      simp only [add_zero]; exact Path.extend_trans_of_le_half _ _ hs.2.le),
      localLength_comp_affine φ _ two_pos]
    norm_num
  · rw [localLength_congr φ (c' := fun s => γ₂.extend (2 * s + -1)) (fun s hs => by
      show _ = γ₂.extend (2 * s + -1)
      rw [← sub_eq_add_neg]; exact Path.extend_trans_of_half_le _ _ hs.1.le),
      localLength_comp_affine φ _ two_pos]
    norm_num

theorem pathLength_trans_le (φ : X → X → Minkowski d) {x y z : X} (γ₁ : Path x y)
    (γ₂ : Path y z) : pathLength φ (γ₁.trans γ₂) ≤ pathLength φ γ₁ + pathLength φ γ₂ := by
  by_cases h₁ : IsLocLip φ γ₁.extend
  swap; · rw [pathLength_of_not_isLocLip φ h₁, top_add]; exact le_top
  by_cases h₂ : IsLocLip φ γ₂.extend
  swap; · rw [pathLength_of_not_isLocLip φ h₂, add_top]; exact le_top
  exact (pathLength_trans φ h₁ h₂).le

end LocalLength

/-- `X` with the length pseudo-emetric of the local developing system `φ`. -/
def LocalLengthSpace {X : Type*} (_φ : X → X → Minkowski d) : Type _ := X

namespace LocalLengthSpace

variable {X : Type*} {φ : X → X → Minkowski d}

/-- The identity. -/
def toSpace : LocalLengthSpace φ ≃ X := Equiv.refl _

variable [TopologicalSpace X]

noncomputable instance : PseudoEMetricSpace (LocalLengthSpace φ) where
  edist x y := ⨅ γ : Path (toSpace x) (toSpace y), pathLength φ γ
  edist_self x := le_antisymm ((iInf_le _ (Path.refl _)).trans_eq (pathLength_refl φ _)) bot_le
  edist_comm x y := le_antisymm
    (le_iInf fun γ => (iInf_le _ γ.symm).trans_eq (pathLength_symm φ γ))
    (le_iInf fun γ => (iInf_le _ γ.symm).trans_eq (pathLength_symm φ γ))
  edist_triangle x y z := ENNReal.le_iInf_add_iInf fun γ₁ γ₂ =>
    (iInf_le _ (γ₁.trans γ₂)).trans (pathLength_trans_le φ γ₁ γ₂)

theorem edist_def (x y : LocalLengthSpace φ) :
    edist x y = ⨅ γ : Path (toSpace x) (toSpace y), pathLength φ γ := rfl

end LocalLengthSpace

/-! #### Sub-paths: a path is longer than the distance to each of its points -/

section SubPath

/-- An eventual property near `t` holds on a closed interval about `t`. -/
theorem exists_Icc_subset_of_eventually {P : ℝ → Prop} {t : ℝ} (h : ∀ᶠ s in 𝓝 t, P s) :
    ∃ δ > (0 : ℝ), ∀ s ∈ Icc (t - δ) (t + δ), P s := by
  obtain ⟨ε, hε, hP⟩ := Metric.eventually_nhds_iff.1 h
  refine ⟨ε / 2, half_pos hε, fun s hs => hP ?_⟩
  rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hs.1, hs.2]

/-- Lipschitz in charts survives a `1`-Lipschitz reparametrisation. -/
theorem LocLipAt.comp_lipschitz {X : Type*} {φ : X → X → Minkowski d} {c : ℝ → X} {h : ℝ → ℝ}
    (hh : LipschitzWith 1 h) {u : ℝ} (hc : LocLipAt φ c (h u)) : LocLipAt φ (c ∘ h) u := by
  obtain ⟨ε, hε, K, hK⟩ := hc
  refine ⟨ε, hε, K * 1, ?_⟩
  have hmaps : MapsTo h (Icc (u - ε) (u + ε)) (Icc (h u - ε) (h u + ε)) := fun s hs => by
    have := hh.dist_le_mul s u
    rw [NNReal.coe_one, one_mul, Real.dist_eq, Real.dist_eq] at this
    have h2 : |s - u| ≤ ε := abs_le.2 ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have h3 := (abs_le.1 (this.trans h2))
    exact ⟨by linarith [h3.1], by linarith [h3.2]⟩
  exact hK.comp hh.lipschitzOnWith hmaps

/-- `pathLength` only sees the extended curve. -/
theorem pathLength_congr_extend {X : Type*} [TopologicalSpace X] (φ : X → X → Minkowski d)
    {x y x' y' : X} (γ : Path x y) (γ' : Path x' y') (h : ⇑γ.extend = ⇑γ'.extend) :
    pathLength φ γ = pathLength φ γ' := by
  unfold pathLength; rw [h]

/-- **A path is at least as long as the distance to any of its points.** -/
theorem LocalLengthSpace.edist_le_pathLength {X : Type*} [TopologicalSpace X]
    (φ : X → X → Minkowski d) {x y : X} (γ : Path x y) (t : I) :
    edist (LocalLengthSpace.toSpace.symm x : LocalLengthSpace φ)
      (LocalLengthSpace.toSpace.symm (γ t)) ≤ pathLength φ γ := by
  rcases eq_or_lt_of_le t.2.1 with h0 | ht0
  · have : t = 0 := Subtype.ext h0.symm
    rw [this, γ.source, edist_self]; exact bot_le
  by_cases hL : IsLocLip φ γ.extend
  swap; · rw [pathLength_of_not_isLocLip φ hL]; exact le_top
  set τ : ℝ := (t : ℝ) with hτ
  let β : Path x (γ t) :=
    { toFun := fun s => γ.extend (τ * s)
      continuous_toFun := γ.continuous_extend.comp (continuous_const.mul continuous_subtype_val)
      source' := by simp
      target' := by simp [τ] }
  set h : ℝ → ℝ := fun u => τ * (projIcc (0 : ℝ) 1 zero_le_one u : ℝ)
  have hβ : ⇑β.extend = γ.extend ∘ h := rfl
  have hh : LipschitzWith 1 h := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul, ← mul_sub, abs_mul,
      abs_of_nonneg t.2.1]
    calc τ * |(projIcc (0 : ℝ) 1 zero_le_one a : ℝ) - projIcc 0 1 zero_le_one b|
        ≤ 1 * |a - b| := mul_le_mul t.2.2 (abs_projIcc_sub_projIcc _) (abs_nonneg _) zero_le_one
      _ = |a - b| := one_mul _
  have hLβ : IsLocLip φ β.extend := by
    rw [hβ]; exact fun u => (hL (h u)).comp_lipschitz hh
  refine (iInf_le _ β).trans ?_
  change pathLength φ β ≤ _
  rw [pathLength_of_isLocLip φ hLβ, pathLength_of_isLocLip φ hL]
  rw [localLength_congr φ (c' := fun s => γ.extend (τ * s + 0)) (fun s hs => by
    rw [hβ]; simp only [Function.comp_apply, h, add_zero, projIcc_of_mem _ ⟨hs.1.le, hs.2.le⟩]),
    localLength_comp_affine φ _ ht0]
  simp only [mul_zero, add_zero, mul_one]
  exact lintegral_mono_set (Ioc_subset_Ioc_right t.2.2)

end SubPath

/-! ### B. The induced length of a hypersurface of a flat spacetime (the gluing) -/

section Glued

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Minkowski d) M]

variable (d) in
/-- **The chart system of `S ⊆ M`**: a point `y` read in the chart at `x`. -/
noncomputable def chartSys (S : Set M) (x y : S) : Minkowski d :=
  chartAt (Minkowski d) (x : M) (y : M)

variable (d) in
/-- **The induced length space of `S ⊆ M`** (contract (e)). -/
def InducedLengthSpace (S : Set M) : Type _ := LocalLengthSpace (chartSys d S)

noncomputable instance (S : Set M) : PseudoEMetricSpace (InducedLengthSpace d S) :=
  inferInstanceAs (PseudoEMetricSpace (LocalLengthSpace (chartSys d S)))

/-- The identity, from the length space to the subspace `S`. -/
def InducedLengthSpace.toSubtype {S : Set M} : InducedLengthSpace d S ≃ S := Equiv.refl _

variable (d) in
/-- **Point-local spacelike Lipschitz hypersurface** (contract (f)). -/
def IsSpacelikeLipschitz (S : Set M) : Prop :=
  ∀ x ∈ S, ∃ V : Opens (Minkowski d), chartAt (Minkowski d) x x ∈ V ∧
    (V : Set (Minkowski d)) ⊆ (chartAt (Minkowski d) x).target ∧
    IsSpacelikeLipschitzIn V ((chartAt (Minkowski d) x) '' (S ∩ (chartAt (Minkowski d) x).source) ∩
      (V : Set (Minkowski d)))

/-- **(c), gluing on overlaps; (b), `Isom(𝐌ⁿ)`-invariance**: the density of a curve of `S`
can be computed in ANY chart of the atlas containing the point, not only in `chartAt`. The
transition is, near the point, an element `g` of `Isom(𝐌ⁿ)` (`exists_smul_eq_of_mem_gxGroupoid`),
and `g` preserves `minkQ` of velocities (`deriv_isom_comp`). So the chart-local lengths of
`InducedLength` agree on overlaps, and the glued length is independent of the atlas. -/
theorem localDensity_chartSys_eq [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))]
    {S : Set M} {c : ℝ → S} {t : ℝ} (hc : ContinuousAt c t)
    {e : OpenPartialHomeomorph M (Minkowski d)} (he : e ∈ atlas (Minkowski d) M)
    (hct : (c t : M) ∈ e.source) :
    localDensity (chartSys d S) c t =
      ENNReal.ofReal (Real.sqrt (minkQ (deriv (fun s => e (c s : M)) t))) := by
  obtain ⟨g, O, hxO, -, heq⟩ := exists_smul_eq_of_mem_gxGroupoid
    ((gxGroupoid (isom d) (Minkowski d)).compatible (chart_mem_atlas (Minkowski d) (c t : M)) he)
    (mem_chart_source _ (c t : M)) hct
  have hcont : ContinuousAt (fun s => (c s : M)) t := continuous_subtype_val.continuousAt.comp hc
  have hev : ∀ᶠ s in 𝓝 t, (c s : M) ∈ O := hcont.eventually (O.isOpen.mem_nhds hxO)
  have hfun : (fun s => e (c s : M)) =ᶠ[𝓝 t]
      fun s => g • chartAt (Minkowski d) (c t : M) (c s : M) := by
    filter_upwards [hev] with s hs; exact heq _ hs
  rw [hfun.deriv_eq, deriv_isom_comp, show ((g : Minkowski d ≃ᵃ[ℝ] Minkowski d).linear
      (deriv (fun s => chartAt (Minkowski d) (c t : M) (c s : M)) t)) =
      (linearPart g : Minkowski d ≃ₗ[ℝ] Minkowski d)
        (deriv (fun s => chartAt (Minkowski d) (c t : M) (c s : M)) t) from rfl,
    lorentz.minkQ_apply (linearPart g).2]
  rfl

end Glued

/-- **(d), specialisation to `𝐌ⁿ`**: for a subset of `𝐌ⁿ` with its one-chart atlas the glued
length is `InducedLength`'s `lorentzLength`, `∫ √(minkQ γ')` (W2's corrected integrand). -/
theorem localLength_chartSys_minkowski (S : Set (Minkowski d)) (c : ℝ → S) (a b : ℝ) :
    localLength (chartSys d S) c a b = lorentzLength (fun t => (c t : Minkowski d)) a b := by
  simp only [localLength, localDensity, chartSys, chartAt_self_eq,
    OpenPartialHomeomorph.refl_apply, id_eq, lorentzLength]

/-- The pulled-back length is the Lorentzian length of the developed curve. -/
theorem localLength_pulled {X : Type*} (F : X → Minkowski d) (c : ℝ → X) (a b : ℝ) :
    localLength (fun (_ : X) (y : X) => F y) c a b = lorentzLength (fun t => F (c t)) a b := rfl

/-! #### The reuse link: for one developing map, "Lipschitz in charts" is "Lipschitz" -/

/-- **Local ⇒ global Lipschitz along a path**, for a system with one developing map `F`:
`IsLocLip` of `γ.extend` is a global Lipschitz bound on `F ∘ γ.extend` (compactness of `[0, 1]`,
`LocallyLipschitzOn.exists_lipschitzOnWith_of_compact`, and `γ.extend` factors through
`projIcc`, which is `1`-Lipschitz). -/
theorem isLocLip_pulled_iff {X : Type*} [TopologicalSpace X] (F : X → Minkowski d) {x y : X}
    (γ : Path x y) :
    IsLocLip (fun (_ : X) (y : X) => F y) γ.extend ↔
      ∃ K : ℝ≥0, LipschitzWith K fun t => F (γ.extend t) := by
  constructor
  · intro h
    set f : ℝ → Minkowski d := fun t => F (γ.extend t) with hf
    have hloc : LocallyLipschitzOn (Icc (0 : ℝ) 1) f := fun t _ => by
      obtain ⟨ε, hε, K, hK⟩ := h t
      exact ⟨K, Icc (t - ε) (t + ε),
        mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds (by linarith) (by linarith)), hK⟩
    obtain ⟨K, hK⟩ := hloc.exists_lipschitzOnWith_of_compact isCompact_Icc
    have hproj : ∀ u, f u = f (projIcc 0 1 zero_le_one u) := fun u => by
      simp only [hf, Path.extend_extends']; rfl
    refine ⟨K, LipschitzWith.of_dist_le_mul fun s t => ?_⟩
    rw [hproj s, hproj t]
    refine (hK.dist_le_mul _ (projIcc 0 1 zero_le_one s).2 _ (projIcc 0 1 zero_le_one t).2).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ K.2
    have := (LipschitzWith.projIcc (zero_le_one' ℝ)).dist_le_mul s t
    rw [NNReal.coe_one, one_mul, Subtype.dist_eq] at this
    exact this
  · rintro ⟨K, hK⟩ t
    exact ⟨1, one_pos, K, hK.lipschitzOnWith⟩

section MinkowskiLink

variable {S : Set (Minkowski d)}

/-- On `𝐌ⁿ` with its one-chart atlas the chart system is the inclusion. -/
theorem chartSys_minkowski (S : Set (Minkowski d)) :
    chartSys d S = fun (_ : S) (y : S) => (y : Minkowski d) := by
  funext x y; simp [chartSys]

/-- `S` as `S ∩ ⊤`, the carrier `InducedLength S ⊤` is built on. -/
noncomputable def interTopHomeo (S : Set (Minkowski d)) :
    S ≃ₜ ↥(S ∩ ((⊤ : Opens (Minkowski d)) : Set (Minkowski d))) :=
  Homeomorph.setCongr (by simp)

theorem curveExtend_map_interTop {x y : S} (γ : Path x y) :
    curveExtend (γ.map (interTopHomeo S).continuous).toContinuousMap =
      fun t => (γ.extend t : Minkowski d) := rfl

/-- **The reuse link, paths** (`S ⊆ 𝐌ⁿ`): "Lipschitz in charts" is `InducedLength`'s
`IsLipschitzCurve`. -/
theorem isLocLip_chartSys_minkowski_iff {x y : S} (γ : Path x y) :
    IsLocLip (chartSys d S) γ.extend ↔
      IsLipschitzCurve (γ.map (interTopHomeo S).continuous).toContinuousMap := by
  rw [chartSys_minkowski, isLocLip_pulled_iff (fun y : S => (y : Minkowski d)) γ]
  unfold IsLipschitzCurve
  rw [curveExtend_map_interTop]

/-- **The reuse link, lengths** (`S ⊆ 𝐌ⁿ`): the glued `pathLength` is `InducedLength.lengthOn`. -/
theorem pathLength_chartSys_minkowski {x y : S} (γ : Path x y) :
    pathLength (chartSys d S) γ =
      lengthOn S ⊤ (γ.map (interTopHomeo S).continuous).toContinuousMap := by
  by_cases h : IsLocLip (chartSys d S) γ.extend
  · rw [pathLength_of_isLocLip _ h,
      lengthOn_of_isLipschitzCurve ((isLocLip_chartSys_minkowski_iff γ).1 h),
      curveExtend_map_interTop, localLength_chartSys_minkowski]
  · rw [pathLength_of_not_isLocLip _ h,
      lengthOn_of_not_isLipschitzCurve (mt (isLocLip_chartSys_minkowski_iff γ).2 h)]

/-- **The reuse link, distances** (`S ⊆ 𝐌ⁿ`): the glued length space of `S` and
`InducedLength S ⊤` have the same `edist`. -/
theorem edist_inducedLengthSpace_minkowski (x y : S) :
    edist (InducedLengthSpace.toSubtype.symm x : InducedLengthSpace d S)
        (InducedLengthSpace.toSubtype.symm y) =
      edist (InducedLength.toSubtype.symm (interTopHomeo S x) : InducedLength S ⊤)
        (InducedLength.toSubtype.symm (interTopHomeo S y)) := by
  set e := interTopHomeo S
  change (⨅ γ : Path x y, pathLength (chartSys d S) γ) =
    ⨅ γ' : Path (e x) (e y), lengthOn S ⊤ γ'.toContinuousMap
  apply le_antisymm
  · refine le_iInf fun γ' => ?_
    refine (iInf_le _ ((γ'.map e.symm.continuous).cast (e.symm_apply_apply x).symm
      (e.symm_apply_apply y).symm)).trans_eq ?_
    rw [pathLength_chartSys_minkowski]
    exact lengthOn_congr _ _ fun t => rfl
  · exact le_iInf fun γ => (iInf_le _ (γ.map e.continuous)).trans_eq
      (pathLength_chartSys_minkowski γ).symm

end MinkowskiLink

section Complete

variable (d) in
/-- **Cauchy-complete** (Barbot l.551–553, DEC-35). -/
def IsCauchyComplete (M : Type*) [TopologicalSpace M] [ChartedSpace (Minkowski d) M]
    [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))] : Prop :=
  ∃ S : Set M, (flatCausality d M).IsCauchySurface S ∧ IsSpacelikeLipschitz d S ∧
    CompleteSpace (InducedLengthSpace d S) ∧
    Continuous fun x : InducedLengthSpace d S => (InducedLengthSpace.toSubtype x : M)

end Complete

/-! ### C. Spacelike developments, the projection along a timelike direction -/

section Development

variable {X : Type*} [TopologicalSpace X]

/-- **A spacelike development** of `X`. -/
structure SpacelikeDevelopment (F : X → Minkowski d) : Prop where
  continuous : Continuous F
  locally : ∀ x : X, ∃ (U : Opens X) (V : Opens (Minkowski d)), x ∈ U ∧
    IsEmbedding ((U : Set X).restrict F) ∧ IsSpacelikeLipschitzIn V (F '' U)

/-- **The length pulled back along `F`.** -/
def PulledLength (F : X → Minkowski d) : Type _ := LocalLengthSpace fun (_ : X) (y : X) => F y

noncomputable instance (F : X → Minkowski d) : PseudoEMetricSpace (PulledLength F) :=
  inferInstanceAs (PseudoEMetricSpace (LocalLengthSpace fun (_ : X) (y : X) => F y))

/-- **Non-vacuity**: the slice `x ↦ (0, x)` of `𝐌ⁿ` is a spacelike development of `ℝᵈ`. -/
theorem spacelikeDevelopment_slice :
    SpacelikeDevelopment (fun x : EuclideanSpace ℝ (Fin d) => ((0 : ℝ), x)) := by
  have hemb : IsEmbedding (fun x : EuclideanSpace ℝ (Fin d) => ((0 : ℝ), x)) :=
    isEmbedding_prodMkRight (0 : ℝ)
  refine ⟨hemb.continuous, fun x => ⟨⊤, ⊤, trivial, hemb.comp IsEmbedding.subtypeVal, ?_⟩⟩
  have h : (fun x : EuclideanSpace ℝ (Fin d) => ((0 : ℝ), x)) ''
      ((⊤ : Opens (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d))) =
      graphOver univ (fun _ => (0 : ℝ)) := by
    ext p
    simp only [Opens.coe_top, image_univ, mem_range, graphOver, mem_setOf_eq, mem_univ, true_and]
    exact ⟨fun ⟨y, hy⟩ => by rw [← hy], fun hp => ⟨p.2, Prod.ext hp.symm rfl⟩⟩
  rw [h]
  exact isSpacelikeLipschitzIn_graphOver (c := 0) zero_lt_one (LipschitzWith.const _)

/-- The identity, from the pulled length space to `X`. -/
def PulledLength.toSpace (F : X → Minkowski d) : PulledLength F ≃ X := Equiv.refl _

/-- The straight segment `t ↦ a + t (b − a)`. -/
def segmentPath {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a b : E) : Path a b where
  toFun t := a + (t : ℝ) • (b - a)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

/-- **The pulled length of the slice is the Euclidean distance.** Lower bound:
`le_lorentzLength_of_frame` (frame `1`, graph of `0`, `c = 0`); upper bound: the segment. -/
theorem edist_eq_iInf_pathLength_slice (x y : EuclideanSpace ℝ (Fin d)) :
    edist x y = ⨅ γ : Path x y,
      pathLength (fun (_ : EuclideanSpace ℝ (Fin d)) (z : EuclideanSpace ℝ (Fin d)) =>
        ((0 : ℝ), z)) γ := by
  set F : EuclideanSpace ℝ (Fin d) → Minkowski d := fun x => ((0 : ℝ), x) with hF
  apply le_antisymm
  · refine le_iInf fun γ => ?_
    by_cases h : IsLocLip (fun _ z => F z) γ.extend
    swap; · rw [pathLength_of_not_isLocLip _ h]; exact le_top
    obtain ⟨K, hK⟩ := (isLocLip_pulled_iff F γ).1 h
    rw [pathLength_of_isLocLip _ h, localLength_pulled]
    have hfr := le_lorentzLength_of_frame hK zero_le_one (1 : isom d) (c := 0)
      (f := fun _ => (0 : ℝ)) (U := univ) (LipschitzWith.const _).lipschitzOnWith
      (fun s _ => by simp [hF])
    simp only [one_smul, NNReal.coe_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, sub_zero, Real.sqrt_one, one_mul, Path.extend_one, Path.extend_zero, hF] at hfr
    rw [edist_dist, dist_eq_norm, norm_sub_rev]
    exact hfr
  · have hL : LipschitzWith ‖y - x‖₊ fun t => F ((segmentPath x y).extend t) := by
      refine LipschitzWith.of_dist_le_mul fun s t => ?_
      have e : ∀ u, F ((segmentPath x y).extend u) =
          ((0 : ℝ), x + ((projIcc 0 1 zero_le_one u : ℝ)) • (y - x)) := fun u => rfl
      rw [e, e, Prod.dist_eq, dist_self, dist_add_left, dist_eq_norm, ← sub_smul, norm_smul,
        Real.norm_eq_abs, max_eq_right (by positivity), coe_nnnorm, Real.dist_eq, mul_comm]
      exact mul_le_mul_of_nonneg_left (abs_projIcc_sub_projIcc _) (norm_nonneg _)
    refine (iInf_le _ (segmentPath x y)).trans ?_
    rw [pathLength_of_isLocLip _ ((isLocLip_pulled_iff F _).2 ⟨_, hL⟩), localLength_pulled]
    refine (lorentzLength_le_of_lipschitzWith hL 0 1).trans_eq ?_
    rw [edist_dist, dist_eq_norm, norm_sub_rev, coe_nnnorm, sub_zero, mul_one]

/-- The slice's pulled length space is isometric to `ℝᵈ`. -/
theorem edist_pulledLength_slice
    (a b : PulledLength fun x : EuclideanSpace ℝ (Fin d) => ((0 : ℝ), x)) :
    edist (PulledLength.toSpace _ a) (PulledLength.toSpace _ b) = edist a b :=
  edist_eq_iInf_pathLength_slice _ _

/-- **Non-vacuity of 8.1 / 8.3** (kb/0011): the slice `t = 0` of `𝐌ⁿ` is a spacelike development
of `ℝᵈ` (`spacelikeDevelopment_slice`) whose pulled length is complete — it is isometric to
`ℝᵈ`. -/
theorem completeSpace_pulledLength_slice :
    CompleteSpace (PulledLength fun x : EuclideanSpace ℝ (Fin d) => ((0 : ℝ), x)) :=
  (IsometryEquiv.mk (PulledLength.toSpace _) fun a b => edist_pulledLength_slice a b).completeSpace

end Development

/-! #### Non-vacuity of `IsCauchyComplete`: `𝐌ⁿ` and its slice `t = 0` -/

section MinkowskiWitness

/-- **The pulled length of a path only sees the developed curve** `t ↦ F (γ.extend t)`. -/
theorem pathLength_pulled_congr {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (F : X → Minkowski d) (G : Y → Minkowski d) {x y : X} {x' y' : Y} (γ : Path x y)
    (γ' : Path x' y') (h : ∀ t, F (γ.extend t) = G (γ'.extend t)) :
    pathLength (fun (_ : X) (z : X) => F z) γ = pathLength (fun (_ : Y) (z : Y) => G z) γ' := by
  have hf : (fun t => F (γ.extend t)) = fun t => G (γ'.extend t) := funext h
  have hiff : IsLocLip (fun (_ : X) (z : X) => F z) γ.extend ↔
      IsLocLip (fun (_ : Y) (z : Y) => G z) γ'.extend := by
    rw [isLocLip_pulled_iff, isLocLip_pulled_iff, hf]
  by_cases hL : IsLocLip (fun (_ : X) (z : X) => F z) γ.extend
  · rw [pathLength_of_isLocLip _ hL, pathLength_of_isLocLip _ (hiff.1 hL), localLength_pulled,
      localLength_pulled, hf]
  · rw [pathLength_of_not_isLocLip _ hL, pathLength_of_not_isLocLip _ (mt hiff.2 hL)]

/-- The slice `t = 0` of `𝐌ⁿ` is `ℝᵈ`. -/
def sliceHomeo :
    (graph (fun _ : EuclideanSpace ℝ (Fin d) => (0 : ℝ)) : Set (Minkowski d)) ≃ₜ
      EuclideanSpace ℝ (Fin d) where
  toFun p := (p : Minkowski d).2
  invFun x := ⟨((0 : ℝ), x), rfl⟩
  left_inv p := Subtype.ext (Prod.ext p.2.symm rfl)
  right_inv _ := rfl
  continuous_toFun := continuous_snd.comp continuous_subtype_val
  continuous_invFun := (continuous_const.prodMk continuous_id).subtype_mk fun _ => rfl

/-- **The glued length of the slice is the Euclidean distance.** -/
theorem edist_inducedLengthSpace_slice
    (x y : InducedLengthSpace d (graph (fun _ : EuclideanSpace ℝ (Fin d) => (0 : ℝ)))) :
    edist (sliceHomeo (InducedLengthSpace.toSubtype x))
      (sliceHomeo (InducedLengthSpace.toSubtype y)) = edist x y := by
  rw [edist_eq_iInf_pathLength_slice]
  change _ = ⨅ γ : Path (InducedLengthSpace.toSubtype x) (InducedLengthSpace.toSubtype y),
    pathLength (chartSys d (graph (fun _ : EuclideanSpace ℝ (Fin d) => (0 : ℝ)))) γ
  rw [chartSys_minkowski]
  apply le_antisymm
  · exact le_iInf fun γ => (iInf_le _ (γ.map (sliceHomeo (d := d)).continuous)).trans_eq
      (pathLength_pulled_congr _ _ _ _ fun t => Prod.ext (γ.extend t).2.symm rfl)
  · exact le_iInf fun γ' => (iInf_le _ ((γ'.map (sliceHomeo (d := d)).symm.continuous).cast
      ((sliceHomeo (d := d)).symm_apply_apply _).symm
      ((sliceHomeo (d := d)).symm_apply_apply _).symm)).trans_eq
      (pathLength_pulled_congr _ _ _ _ fun _ => rfl)

theorem completeSpace_inducedLengthSpace_slice :
    CompleteSpace (InducedLengthSpace d (graph (fun _ : EuclideanSpace ℝ (Fin d) => (0 : ℝ)))) :=
  (IsometryEquiv.mk (InducedLengthSpace.toSubtype.trans (sliceHomeo (d := d)).toEquiv)
    fun x y => edist_inducedLengthSpace_slice x y).completeSpace

/-- The topology-compatibility field holds on the slice. -/
theorem continuous_toSubtype_slice :
    Continuous fun x : InducedLengthSpace d (graph (fun _ : EuclideanSpace ℝ (Fin d) => (0 : ℝ))) =>
      (InducedLengthSpace.toSubtype x : Minkowski d) := by
  have hi : Isometry fun x : InducedLengthSpace d
      (graph (fun _ : EuclideanSpace ℝ (Fin d) => (0 : ℝ))) =>
      sliceHomeo (InducedLengthSpace.toSubtype x) := fun x y => edist_inducedLengthSpace_slice x y
  have := continuous_subtype_val.comp ((sliceHomeo (d := d)).symm.continuous.comp hi.continuous)
  convert this using 2 with x
  simp

/-- **Non-vacuity of `IsCauchyComplete`** (kb/0011): `𝐌ⁿ` is Cauchy-complete, through its slice
`t = 0` (`isCauchySurface_graph_zero`), whose glued length is Euclidean. So the bridge
`exists_developsCC_of_isCauchyComplete` has an instance (with `gh_minkowskiSpace`). -/
theorem isCauchyComplete_minkowski : IsCauchyComplete d (Minkowski d) := by
  refine ⟨graph fun _ => (0 : ℝ), ?_, fun x _ => ⟨⊤, trivial, by simp, ?_⟩,
    completeSpace_inducedLengthSpace_slice, continuous_toSubtype_slice⟩
  · rw [flatCausality_self]; exact isCauchySurface_graph_zero
  · have h : graph (fun _ : EuclideanSpace ℝ (Fin d) => (0 : ℝ)) =
        graphOver univ (fun _ => (0 : ℝ)) := by
      ext p; simp [graph, graphOver]
    simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_source, inter_univ,
      OpenPartialHomeomorph.refl_apply, id_eq, image_id', Opens.coe_top]
    rw [h]
    exact isSpacelikeLipschitzIn_graphOver (c := 0) zero_lt_one (LipschitzWith.const _)

/-- The same, for the bundled flat spacetime `minkowskiSpace d` the bridge takes. -/
theorem isCauchyComplete_minkowskiSpace : IsCauchyComplete d (FlatSpacetime.minkowskiSpace d) :=
  isCauchyComplete_minkowski

end MinkowskiWitness

/-- `v ↦ ⟨v, Δ⟩`, linear. -/
noncomputable def minkBL (Δ : Minkowski d) : Minkowski d →ₗ[ℝ] ℝ where
  toFun v := minkB v Δ
  map_add' v w := by
    simp only [minkB, Prod.fst_add, Prod.snd_add, inner_add_left]; ring
  map_smul' c v := by
    simp only [minkB, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, real_inner_smul_left,
      RingHom.id_apply]; ring

/-- The hyperplane `Δ^⊥`, a model of `Q(Δ) = 𝐌ⁿ / Δ`. -/
noncomputable def orthSub (Δ : Minkowski d) : Submodule ℝ (Minkowski d) := LinearMap.ker (minkBL Δ)

theorem minkBL_apply (Δ v : Minkowski d) : minkBL Δ v = minkB v Δ := rfl

theorem minkB_self (Δ : Minkowski d) : minkB Δ Δ = minkQ Δ := (minkQ_eq_minkB Δ).symm

theorem mem_orthSub {Δ v : Minkowski d} : v ∈ orthSub Δ ↔ minkB v Δ = 0 := Iff.rfl

/-- The projection along `Δ` onto `Δ^⊥`, as a linear map. -/
noncomputable def projAlongₗ (Δ : Minkowski d) (hΔ : minkQ Δ ≠ 0) :
    Minkowski d →ₗ[ℝ] orthSub Δ :=
  LinearMap.codRestrict (orthSub Δ)
    (LinearMap.id - (minkQ Δ)⁻¹ • (minkBL Δ).smulRight Δ) fun v => by
      change minkBL Δ _ = 0
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
        LinearMap.smulRight_apply, map_sub, map_smul, minkBL_apply, minkB_self, smul_eq_mul]
      field_simp; ring

/-- **The projection `π : 𝐌ⁿ → Q(Δ)` along the timelike direction `Δ`** (Barbot l.2236–2239),
with `Q(Δ)` modelled TOPOLOGICALLY by the hyperplane `Δ^⊥`: `π v = v − (⟨v, Δ⟩ / ⟨Δ, Δ⟩) Δ`. On
`Δ^⊥` it is the identity. The paper's metric on `Q(Δ)` (the one making `π` isometric on the
spacelike hyperplanes orthogonal to `Δ`) is `minkQ` restricted to `Δ^⊥`, positive definite; the
subtype `orthSub Δ` carries instead the sup-product metric of `ℝ × ℝᵈ`, equivalent to it but not
equal. Only the topology enters 8.1's homeomorphism. -/
noncomputable def projAlong (Δ : Minkowski d) (hΔ : minkQ Δ ≠ 0) : Minkowski d →L[ℝ] orthSub Δ :=
  (projAlongₗ Δ hΔ).toContinuousLinearMap

theorem projAlong_coe (Δ : Minkowski d) (hΔ : minkQ Δ ≠ 0) (v : Minkowski d) :
    (projAlong Δ hΔ v : Minkowski d) = v - ((minkQ Δ)⁻¹ * minkB v Δ) • Δ := by
  simp [projAlong, projAlongₗ, minkBL_apply, mul_smul]

/-- `π` identifies exactly the points of one `Δ`-line. -/
theorem projAlong_eq_iff {Δ : Minkowski d} (hΔ : minkQ Δ ≠ 0) {v w : Minkowski d} :
    projAlong Δ hΔ v = projAlong Δ hΔ w ↔ ∃ s : ℝ, v = w + s • Δ := by
  constructor
  · intro h
    have h' := congrArg (Subtype.val) h
    simp only [projAlong_coe] at h'
    refine ⟨(minkQ Δ)⁻¹ * minkB v Δ - (minkQ Δ)⁻¹ * minkB w Δ, ?_⟩
    calc v = (v - ((minkQ Δ)⁻¹ * minkB v Δ) • Δ) + ((minkQ Δ)⁻¹ * minkB v Δ) • Δ := by abel
      _ = (w - ((minkQ Δ)⁻¹ * minkB w Δ) • Δ) + ((minkQ Δ)⁻¹ * minkB v Δ) • Δ := by rw [h']
      _ = _ := by rw [sub_smul]; abel
  · rintro ⟨s, rfl⟩
    rw [map_add, map_smul, add_eq_left]
    ext1
    rw [Submodule.coe_smul, projAlong_coe, ZeroMemClass.coe_zero]
    simp only [minkB_self, inv_mul_cancel₀ hΔ, one_smul, sub_self, smul_zero]

/-- `Q(Δ)` is simply connected and locally path-connected. -/
example (Δ : Minkowski d) : SimplyConnectedSpace (orthSub Δ) := inferInstance
example (Δ : Minkowski d) : LocPathConnectedSpace (orthSub Δ) := inferInstance

/-! ### D. Prop 8.1 -/

theorem isHomeomorph_of_isCoveringMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ConnectedSpace X] [SimplyConnectedSpace Y] [LocPathConnectedSpace Y] {q : X → Y}
    (hq : IsCoveringMap q) : IsHomeomorph q := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  obtain ⟨s, ⟨hs0, hs⟩, -⟩ :=
    hq.existsUnique_continuousMap_lifts (ContinuousMap.id Y) (q x₀) x₀ rfl
  have hsq : (s ∘ q) = id :=
    hq.eq_of_comp_eq (s.continuous.comp hq.continuous) continuous_id
      (by funext x; exact congrFun hs (q x)) x₀ (by simpa using hs0)
  exact (Homeomorph.mk ⟨q, s, fun x => congrFun hsq x, fun y => congrFun hs y⟩ hq.continuous
    s.continuous).isHomeomorph

/-! #### The steps of 8.1, and the lifting machinery shared with 8.3 -/

/-- The linear part of an isometry preserves `minkQ`. -/
theorem minkQ_isom_linear (g : isom d) (v : Minkowski d) :
    minkQ ((g : Minkowski d ≃ᵃ[ℝ] Minkowski d).linear v) = minkQ v := by
  rw [show ((g : Minkowski d ≃ᵃ[ℝ] Minkowski d).linear v) =
      (linearPart g : Minkowski d ≃ₗ[ℝ] Minkowski d) v from rfl,
    lorentz.minkQ_apply (linearPart g).2]

/-- `minkQ (w + s Δ) = minkQ w + s² minkQ Δ` when `w ⊥ Δ`. -/
theorem minkQ_add_smul_of_minkB_eq_zero {w Δ : Minkowski d} (h : minkB w Δ = 0) (s : ℝ) :
    minkQ (w + s • Δ) = minkQ w + s ^ 2 * minkQ Δ := by
  unfold minkB at h
  unfold minkQ
  simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
  rw [norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have : inner ℝ w.2 Δ.2 = w.1 * Δ.1 := by linarith
  rw [this]; ring

/-- `v = π v + κ Δ`. -/
theorem projAlong_decomp (Δ : Minkowski d) (hΔ : minkQ Δ ≠ 0) (v : Minkowski d) :
    v = (projAlong Δ hΔ v : Minkowski d) + ((minkQ Δ)⁻¹ * minkB v Δ) • Δ := by
  rw [projAlong_coe]; abel

theorem minkB_projAlong (Δ : Minkowski d) (hΔ : minkQ Δ ≠ 0) (v : Minkowski d) :
    minkB (projAlong Δ hΔ v : Minkowski d) Δ = 0 := (projAlong Δ hΔ v).2

/-- `minkQ v = minkQ (π v) + κ² minkQ Δ`. -/
theorem minkQ_eq_projAlong (Δ : Minkowski d) (hΔ : minkQ Δ ≠ 0) (v : Minkowski d) :
    minkQ v = minkQ (projAlong Δ hΔ v : Minkowski d) +
      ((minkQ Δ)⁻¹ * minkB v Δ) ^ 2 * minkQ Δ := by
  conv_lhs => rw [projAlong_decomp Δ hΔ v]
  exact minkQ_add_smul_of_minkB_eq_zero (minkB_projAlong Δ hΔ v) _

/-- **`π` does not decrease `minkQ`** along a timelike `Δ`. -/
theorem minkQ_le_minkQ_projAlong {Δ : Minkowski d} (hΔ : minkQ Δ < 0) (v : Minkowski d) :
    minkQ v ≤ minkQ (projAlong Δ hΔ.ne v : Minkowski d) := by
  rw [minkQ_eq_projAlong Δ hΔ.ne v]
  nlinarith [sq_nonneg ((minkQ Δ)⁻¹ * minkB v Δ)]

/-- `π` fixes `Δ^⊥`. -/
theorem projAlong_of_mem {Δ : Minkowski d} (hΔ : minkQ Δ ≠ 0) (w : orthSub Δ) :
    projAlong Δ hΔ (w : Minkowski d) = w := by
  ext1; rw [projAlong_coe, show minkB (w : Minkowski d) Δ = 0 from w.2]; simp

theorem projAlong_smul_self {Δ : Minkowski d} (hΔ : minkQ Δ ≠ 0) (s : ℝ) :
    projAlong Δ hΔ (s • Δ) = 0 := by
  rw [map_smul]
  have : projAlong Δ hΔ Δ = 0 := by
    ext1; rw [projAlong_coe, minkB_self, inv_mul_cancel₀ hΔ, one_smul, sub_self]; rfl
  rw [this, smul_zero]

/-- **The Lipschitz constant of the inverse of `π` on a non-timelike set.** -/
noncomputable def projLipConst (Δ : Minkowski d) : ℝ := 1 + ‖Δ‖ / Real.sqrt (-minkQ Δ)

theorem projLipConst_nonneg (Δ : Minkowski d) : 0 ≤ projLipConst Δ := by
  unfold projLipConst; positivity

/-- **A non-timelike vector is controlled by its projection**: if `0 ≤ minkQ v`,
`‖v‖ ≤ (1 + ‖Δ‖ / √(−minkQ Δ)) ‖π v‖`. -/
theorem norm_le_of_minkQ_nonneg {Δ : Minkowski d} (hΔ : minkQ Δ < 0) {v : Minkowski d}
    (hv : 0 ≤ minkQ v) :
    ‖v‖ ≤ projLipConst Δ * ‖(projAlong Δ hΔ.ne v : Minkowski d)‖ := by
  set w : Minkowski d := (projAlong Δ hΔ.ne v : Minkowski d) with hw
  set κ := (minkQ Δ)⁻¹ * minkB v Δ
  have hdec : v = w + κ • Δ := projAlong_decomp Δ hΔ.ne v
  have hQ := minkQ_eq_projAlong Δ hΔ.ne v
  have hm : 0 < -minkQ Δ := by linarith
  have hsq : 0 < Real.sqrt (-minkQ Δ) := Real.sqrt_pos.2 hm
  have hw2 : minkQ w ≤ ‖w‖ ^ 2 := by
    have h1 := sqrt_minkQ_le w
    have h2 : ‖w.2‖ ≤ ‖w‖ := norm_snd_le w
    by_cases h0 : minkQ w ≤ 0
    · nlinarith [norm_nonneg w]
    · push Not at h0
      have := Real.sq_sqrt h0.le
      nlinarith [Real.sqrt_nonneg (minkQ w), norm_nonneg w.2]
  -- κ² (−minkQ Δ) ≤ ‖w‖²
  have hκ : κ ^ 2 * (-minkQ Δ) ≤ ‖w‖ ^ 2 := by nlinarith
  have hκ' : |κ| * Real.sqrt (-minkQ Δ) ≤ ‖w‖ := by
    rw [← Real.sqrt_sq (abs_nonneg κ), ← Real.sqrt_mul (sq_nonneg _), sq_abs]
    calc Real.sqrt (κ ^ 2 * -minkQ Δ) ≤ Real.sqrt (‖w‖ ^ 2) := Real.sqrt_le_sqrt hκ
      _ = ‖w‖ := Real.sqrt_sq (norm_nonneg _)
  have hκ'' : |κ| ≤ ‖w‖ / Real.sqrt (-minkQ Δ) := by
    rw [le_div_iff₀ hsq]; exact hκ'
  calc ‖v‖ = ‖w + κ • Δ‖ := by rw [← hdec]
    _ ≤ ‖w‖ + |κ| * ‖Δ‖ := by
        refine (norm_add_le _ _).trans ?_; rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖w‖ + ‖w‖ / Real.sqrt (-minkQ Δ) * ‖Δ‖ := by gcongr
    _ = projLipConst Δ * ‖w‖ := by unfold projLipConst; field_simp

/-- **The local pieces of a spacelike Lipschitz hypersurface are non-timelike.** -/
theorem IsSpacelikeLipschitzIn.exists_minkQ_sub_nonneg {V : Opens (Minkowski d)}
    {T : Set (Minkowski d)} (hT : IsSpacelikeLipschitzIn V T) {p : Minkowski d} (hp : p ∈ T) :
    ∃ O : Opens (Minkowski d), p ∈ O ∧
      ∀ z₁ ∈ T ∩ (O : Set (Minkowski d)), ∀ z₂ ∈ T ∩ (O : Set (Minkowski d)),
        0 ≤ minkQ (z₁ - z₂) := by
  obtain ⟨g, O, U, f, c, hc, hpO, -, -, hf, hgr⟩ := hT.locGraph p hp
  refine ⟨O, hpO, fun z₁ h₁ z₂ h₂ => ?_⟩
  obtain ⟨hU₁, he₁⟩ := frame_mem_graphOver hgr h₁.1 h₁.2
  obtain ⟨hU₂, he₂⟩ := frame_mem_graphOver hgr h₂.1 h₂.2
  rw [← isom_minkQ_sub g z₂ z₁, he₁, he₂]
  have hL := hf.dist_le_mul _ hU₁ _ hU₂
  rw [Real.dist_eq, dist_eq_norm] at hL
  have hc1 : (c : ℝ) ≤ 1 := by exact_mod_cast hc.le
  unfold minkQ graphLift
  simp only [Prod.fst_sub, Prod.snd_sub]
  have h0 : |f (g • z₁).2 - f (g • z₂).2| ≤ ‖(g • z₁).2 - (g • z₂).2‖ :=
    hL.trans (mul_le_of_le_one_left (norm_nonneg _) hc1)
  have := sq_le_sq' (abs_le.1 h0).1 (abs_le.1 h0).2
  linarith
theorem isom_smul_add (g : isom d) (w v : Minkowski d) :
    g • (w + v) = g • w + (g : Minkowski d ≃ᵃ[ℝ] Minkowski d).linear v := by
  have := isom_sub (g : Minkowski d ≃ᵃ[ℝ] Minkowski d) w (w + v)
  rw [add_sub_cancel_left] at this
  rw [isom_smul_def, isom_smul_def, ← this]; abel

/-- **Openness of the projection of a spacelike Lipschitz piece** (the intermediate value
theorem along `Δ`-lines, `Δ ≠ 0` causal): every `Δ`-line through a point near `p` meets
`T ∩ O'`. In the frame where `T` is a `c`-Lipschitz graph, `c < 1`, the function
`s ↦ (z + sΔ').1 − f (z + sΔ').2` is strictly monotone, since `c ‖Δ'.2‖ < |Δ'.1|`. -/
theorem IsSpacelikeLipschitzIn.eventually_exists_add_smul_mem {V : Opens (Minkowski d)}
    {T : Set (Minkowski d)} (hT : IsSpacelikeLipschitzIn V T) {p : Minkowski d} (hp : p ∈ T)
    {O' : Set (Minkowski d)} (hO' : IsOpen O') (hpO' : p ∈ O') {Δ : Minkowski d}
    (hΔ : minkQ Δ ≤ 0) (hΔ0 : Δ ≠ 0) : ∀ᶠ w in 𝓝 p, ∃ s : ℝ, w + s • Δ ∈ T ∩ O' := by
  obtain ⟨g, O, U, f, c, hc, hpO, -, hU, hf, hgr⟩ := hT.locGraph p hp
  obtain ⟨hUa, ha⟩ := frame_mem_graphOver hgr hp hpO
  set a := g • p with hadef
  set Δ' := (g : Minkowski d ≃ᵃ[ℝ] Minkowski d).linear Δ with hΔ'
  have hQ' : minkQ Δ' ≤ 0 := by rw [hΔ', minkQ_isom_linear]; exact hΔ
  have hc1 : (c : ℝ) < 1 := by exact_mod_cast hc
  have hc0 : (0 : ℝ) ≤ c := c.2
  have hne : Δ'.1 ≠ 0 := by
    intro h'
    refine hΔ0 ((g : Minkowski d ≃ᵃ[ℝ] Minkowski d).linear.map_eq_zero_iff.1 ?_)
    exact eq_zero_of_fst_eq_zero h' hQ'
  have hle : ‖Δ'.2‖ ≤ |Δ'.1| := by
    have h := minkQ_le_zero_iff.1 hQ'
    rw [← sq_abs Δ'.1] at h
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (abs_nonneg _) two_ne_zero).1 h
  set μ := |Δ'.1| - c * ‖Δ'.2‖ with hμ
  have hμ0 : 0 < μ := by
    have h1 : (c : ℝ) * ‖Δ'.2‖ ≤ c * |Δ'.1| := mul_le_mul_of_nonneg_left hle hc0
    have h2 : (c : ℝ) * |Δ'.1| < |Δ'.1| := mul_lt_of_lt_one_left (abs_pos.2 hne) hc1
    linarith
  set G : Set (Minkowski d) := g • ((O : Set (Minkowski d)) ∩ O') with hG
  have hGo : IsOpen G := (O.isOpen.inter hO').smul g
  have haG : a ∈ G := smul_mem_smul_set ⟨hpO, hpO'⟩
  obtain ⟨r₁, hr₁, hb₁⟩ := Metric.isOpen_iff.1 hGo a haG
  obtain ⟨r₂, hr₂, hb₂⟩ := Metric.isOpen_iff.1 hU a.2 hUa
  set r := min r₁ r₂
  have hr : 0 < r := lt_min hr₁ hr₂
  set s₀ := r / (2 * (‖Δ'‖ + 1)) with hs₀
  have hs₀0 : 0 < s₀ := by positivity
  have hs₀r : s₀ * ‖Δ'‖ < r / 2 := by
    rw [hs₀, div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) two_pos]
    nlinarith [norm_nonneg Δ']
  set δ := min (r / 2) (s₀ * μ / 4)
  have hδ : 0 < δ := lt_min (half_pos hr) (by positivity)
  have hcont : Tendsto (fun w : Minkowski d => g • w) (𝓝 p) (𝓝 a) :=
    (continuous_const_smul g).tendsto p
  filter_upwards [hcont (Metric.ball_mem_nhds a hδ)] with w hw
  set z := g • w with hz
  have hza : ‖z - a‖ < δ := by rw [← dist_eq_norm]; exact hw
  -- the points of the segment stay in `G` and over `U`
  have hseg : ∀ s ∈ Icc (-s₀) s₀, z + s • Δ' ∈ G ∧ (z + s • Δ').2 ∈ U := by
    intro s hs
    have habs : |s| ≤ s₀ := abs_le.2 ⟨hs.1, hs.2⟩
    have hd : ‖z + s • Δ' - a‖ < r := by
      calc ‖z + s • Δ' - a‖ = ‖(z - a) + s • Δ'‖ := by congr 1; abel
        _ ≤ ‖z - a‖ + |s| * ‖Δ'‖ := by
            refine (norm_add_le _ _).trans ?_; rw [norm_smul, Real.norm_eq_abs]
        _ < r / 2 + r / 2 := by
            have : |s| * ‖Δ'‖ ≤ s₀ * ‖Δ'‖ := mul_le_mul_of_nonneg_right habs (norm_nonneg _)
            have : δ ≤ r / 2 := min_le_left _ _
            linarith
        _ = r := by ring
    refine ⟨hb₁ ?_, hb₂ ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm]; exact hd.trans_le (min_le_left _ _)
    · rw [Metric.mem_ball, dist_eq_norm]
      refine lt_of_le_of_lt ?_ (hd.trans_le (min_le_right _ _))
      rw [← Prod.snd_sub]; exact norm_snd_le _
  set h : ℝ → ℝ := fun s => (z + s • Δ').1 - f (z + s • Δ').2 with hh
  have hcon : ContinuousOn h (uIcc (-s₀) s₀) := by
    rw [uIcc_of_le (by linarith)]
    refine (continuous_fst.comp (continuous_const.add
      (continuous_id.smul continuous_const))).continuousOn.sub ?_
    refine hf.continuousOn.comp (continuous_snd.comp (continuous_const.add
      (continuous_id.smul continuous_const))).continuousOn fun s hs => (hseg s hs).2
  have h0 : |h 0| < s₀ * μ := by
    have hz0 : z.2 ∈ U := by simpa using (hseg 0 ⟨by linarith, by linarith⟩).2
    simp only [hh, zero_smul, add_zero]
    have ha1 : a.1 = f a.2 := congrArg Prod.fst ha
    have e1 : |z.1 - a.1| ≤ ‖z - a‖ := by
      rw [← Prod.fst_sub, ← Real.norm_eq_abs]; exact norm_fst_le _
    have e2 : ‖z.2 - a.2‖ ≤ ‖z - a‖ := by rw [← Prod.snd_sub]; exact norm_snd_le _
    have e3 := hf.dist_le_mul _ hz0 _ hUa
    rw [Real.dist_eq, dist_eq_norm] at e3
    have : z.1 - f z.2 = (z.1 - a.1) - (f z.2 - f a.2) := by rw [ha1]; ring
    rw [this]
    have hδ' : δ ≤ s₀ * μ / 4 := min_le_right _ _
    calc |(z.1 - a.1) - (f z.2 - f a.2)| ≤ |z.1 - a.1| + |f z.2 - f a.2| := abs_sub _ _
      _ ≤ ‖z - a‖ + c * ‖z - a‖ := add_le_add e1 (e3.trans (mul_le_mul_of_nonneg_left e2 hc0))
      _ < s₀ * μ := by
          have : (c : ℝ) * ‖z - a‖ ≤ ‖z - a‖ := mul_le_of_le_one_left (norm_nonneg _) hc1.le
          linarith
  have hpm : ∀ u : ℝ, u = s₀ ∨ u = -s₀ →
      |h u - h 0 - u * Δ'.1| ≤ c * (s₀ * ‖Δ'.2‖) := by
    intro u hu
    have hu' : u ∈ Icc (-s₀) s₀ := by rcases hu with rfl | rfl <;> constructor <;> linarith
    have hU1 := (hseg u hu').2
    have hU0 := (hseg 0 ⟨by linarith, by linarith⟩).2
    have e3 := hf.dist_le_mul _ hU1 _ hU0
    simp only [zero_smul, add_zero] at hU0 e3
    rw [Real.dist_eq, dist_eq_norm] at e3
    have : h u - h 0 - u * Δ'.1 = -(f (z + u • Δ').2 - f z.2) := by
      simp only [hh, Prod.fst_add, Prod.smul_fst, smul_eq_mul, zero_smul, add_zero]; ring
    rw [this, abs_neg]
    refine e3.trans (mul_le_mul_of_nonneg_left ?_ hc0)
    simp only [Prod.snd_add, Prod.smul_snd, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    rcases hu with rfl | rfl
    · rw [abs_of_pos hs₀0]
    · rw [abs_neg, abs_of_pos hs₀0]
  have hP := hpm s₀ (Or.inl rfl)
  have hM := hpm (-s₀) (Or.inr rfl)
  have hzero : (0 : ℝ) ∈ uIcc (h (-s₀)) (h s₀) := by
    have hcs : c * (s₀ * ‖Δ'.2‖) = s₀ * (c * ‖Δ'.2‖) := by ring
    rw [mem_uIcc]
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · rw [abs_of_neg hneg] at hμ
      have hsμ : s₀ * μ = -(s₀ * Δ'.1) - s₀ * (c * ‖Δ'.2‖) := by rw [hμ]; ring
      have hP' := abs_le.1 hP
      have hM' := abs_le.1 hM
      have h0' := abs_lt.1 h0
      have e : -s₀ * Δ'.1 = -(s₀ * Δ'.1) := by ring
      rw [e] at hM'
      right
      constructor <;> linarith
    · rw [abs_of_pos hpos] at hμ
      have hsμ : s₀ * μ = s₀ * Δ'.1 - s₀ * (c * ‖Δ'.2‖) := by rw [hμ]; ring
      have hP' := abs_le.1 hP
      have hM' := abs_le.1 hM
      have h0' := abs_lt.1 h0
      have e : -s₀ * Δ'.1 = -(s₀ * Δ'.1) := by ring
      rw [e] at hM'
      left
      constructor <;> linarith
  obtain ⟨s, hs, hs0⟩ := intermediate_value_uIcc hcon hzero
  rw [uIcc_of_le (by linarith)] at hs
  obtain ⟨hsG, hsU⟩ := hseg s hs
  refine ⟨s, ?_⟩
  have hgs : g • (w + s • Δ) = z + s • Δ' := by rw [isom_smul_add, map_smul]
  have hgraph : z + s • Δ' ∈ g • (T ∩ (O : Set (Minkowski d))) := by
    rw [hgr]
    refine ⟨?_, hsU, ?_⟩
    · rw [← hgs, smul_mem_smul_set_iff]
      rw [← hgs, smul_mem_smul_set_iff] at hsG
      exact hsG.1
    · have : h s = 0 := hs0
      simp only [hh] at this; linarith
  rw [← hgs, smul_mem_smul_set_iff] at hgraph hsG
  exact ⟨hgraph.1, hsG.2⟩

/-- **The local charts of `π ∘ F`** (step (i) of 8.1): near each point, `π ∘ F` is an open
embedding, on a source where `F` takes pairwise non-timelike values. -/
theorem SpacelikeDevelopment.exists_chart {X : Type*} [TopologicalSpace X] {F : X → Minkowski d}
    (hF : SpacelikeDevelopment F) {Δ : Minkowski d} (hΔ : minkQ Δ < 0) (x : X) :
    ∃ e : OpenPartialHomeomorph X (orthSub Δ), x ∈ e.source ∧
      ⇑e = projAlong Δ hΔ.ne ∘ F ∧ ∀ a ∈ e.source, ∀ b ∈ e.source, 0 ≤ minkQ (F a - F b) := by
  haveI : Nonempty X := ⟨x⟩
  set π := projAlong Δ hΔ.ne with hπ
  obtain ⟨U, V, hxU, hemb, hT⟩ := hF.locally x
  obtain ⟨O, hxO, hO⟩ := hT.exists_minkQ_sub_nonneg ⟨x, hxU, rfl⟩
  set W : Set X := (U : Set X) ∩ F ⁻¹' O with hWdef
  have hWo : IsOpen W := U.isOpen.inter (O.isOpen.preimage hF.continuous)
  have hxW : x ∈ W := ⟨hxU, hxO⟩
  have hWnn : ∀ a ∈ W, ∀ b ∈ W, 0 ≤ minkQ (F a - F b) := fun a ha b hb =>
    hO (F a) ⟨⟨a, ha.1, rfl⟩, ha.2⟩ (F b) ⟨⟨b, hb.1, rfl⟩, hb.2⟩
  have hFinj : InjOn F U := fun a ha b hb hab => by
    have := hemb.injective (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) hab
    exact congrArg Subtype.val this
  have hinj : InjOn (π ∘ F) W := by
    intro a ha b hb hab
    have h0 : π (F a - F b) = 0 := by
      rw [map_sub]; exact sub_eq_zero.2 hab
    have hQ := minkQ_eq_projAlong Δ hΔ.ne (F a - F b)
    rw [← hπ, h0, ZeroMemClass.coe_zero, minkQ_zero, zero_add] at hQ
    have hnn := hWnn a ha b hb
    set κ := (minkQ Δ)⁻¹ * minkB (F a - F b) Δ
    have hκ : κ = 0 := by
      by_contra hne
      have : 0 < κ ^ 2 := by positivity
      nlinarith
    have hdec := projAlong_decomp Δ hΔ.ne (F a - F b)
    rw [← hπ, h0, ZeroMemClass.coe_zero, zero_add, show (minkQ Δ)⁻¹ * minkB (F a - F b) Δ = κ
      from rfl, hκ, zero_smul] at hdec
    exact hFinj ha.1 hb.1 (sub_eq_zero.1 hdec)
  have hopen : ∀ B ⊆ W, IsOpen B → IsOpen ((π ∘ F) '' B) := by
    intro B hBW hBo
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨b, hb, rfl⟩
    have hbU : b ∈ U := (hBW hb).1
    obtain ⟨O'', hO''o, hO''⟩ := hemb.isInducing.isOpen_iff.1
      (hBo.preimage continuous_subtype_val)
    have key : ∀ z, ∀ hz : z ∈ U, F z ∈ O'' ↔ z ∈ B := fun z hz => by
      have := congrArg (fun s : Set U => (⟨z, hz⟩ : U) ∈ s) hO''
      simpa using this
    have hev := hT.eventually_exists_add_smul_mem ⟨b, hbU, rfl⟩ hO''o ((key b hbU).2 hb) hΔ.le
      (fun h => by rw [h, minkQ_zero] at hΔ; exact lt_irrefl _ hΔ)
    set ι : orthSub Δ → Minkowski d := fun y => (y : Minkowski d) + (F b - (π (F b) : Minkowski d))
    have hιc : Continuous ι := continuous_subtype_val.add continuous_const
    have hιb : ι (π (F b)) = F b := by simp [ι]
    have hten : Tendsto ι (𝓝 ((π ∘ F) b)) (𝓝 (F b)) := by
      have := hιc.tendsto (π (F b)); rwa [hιb] at this
    filter_upwards [hten hev] with y hy
    obtain ⟨s, ⟨z, hzU, hz⟩, hzO⟩ := hy
    refine ⟨z, (key z hzU).1 (by rw [hz]; exact hzO), ?_⟩
    simp only [Function.comp_apply]
    rw [hz]
    simp only [ι, map_add, map_sub, projAlong_of_mem, hπ, projAlong_smul_self, add_zero]
    abel
  have hc : ContinuousOn (π ∘ F) W := (π.continuous.comp hF.continuous).continuousOn
  have ho : IsOpenMap (W.restrict (π ∘ F)) := by
    intro A hA
    rw [show W.restrict (π ∘ F) '' A = (π ∘ F) '' (Subtype.val '' A) by
      rw [← image_comp]; rfl]
    exact hopen _ (Subtype.coe_image_subset _ _) (hWo.isOpenMap_subtype_val A hA)
  refine ⟨OpenPartialHomeomorph.ofContinuousOpenRestrict (hinj.toPartialEquiv (π ∘ F) W) hc ho
    hWo, hxW, rfl, hWnn⟩

/-- **Step (ii) of 8.1: the pulled-length topology is finer than the topology of `X`.** A path of
pulled length `< √(1 − c²) ρ` from `x` cannot leave the piece of `X` over the frame cylinder of
radius `ρ` around `F x` (`le_lorentzLength_of_frame` up to the first exit time; the piece over the
closed cylinder is compact through the embedding `F|U`, hence closed in the Hausdorff `X`). The
argument of `IsSpacelikeLipschitzIn.continuous_toSubtype`, run through `SpacelikeDevelopment`. -/
theorem SpacelikeDevelopment.continuous_toSpace {X : Type*} [TopologicalSpace X] [T2Space X]
    {F : X → Minkowski d} (hF : SpacelikeDevelopment F) :
    Continuous ⇑(PulledLength.toSpace F) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  rw [ContinuousAt, Filter.tendsto_def]
  intro N hN
  set x' : X := PulledLength.toSpace F x with hx'
  obtain ⟨U, V, hxU, hemb, hT⟩ := hF.locally x'
  have hNU : ((↑) : U → X) ⁻¹' N ∈ 𝓝 (⟨x', hxU⟩ : U) :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds hN
  rw [hemb.isInducing.nhds_eq_comap, mem_comap] at hNU
  obtain ⟨M, hM, hMN⟩ := hNU
  obtain ⟨W, hWM, hWo, hPW⟩ := mem_nhds_iff.1 hM
  set P : Minkowski d := F x' with hPdef
  have hPT : P ∈ F '' (U : Set X) := ⟨x', hxU, rfl⟩
  obtain ⟨g, O, U', f, c, hc, hpO, hOV, hU', hf, hgr⟩ := hT.locGraph P hPT
  obtain ⟨hx₀U, hP⟩ := frame_mem_graphOver hgr hPT hpO
  set x₀ := (g • P).2
  have hlift := lipschitzOnWith_graphLift hc.le hf
  have hcont : ContinuousAt (graphLift f) x₀ :=
    hlift.continuousOn.continuousAt (hU'.mem_nhds hx₀U)
  have hOW : g • ((O : Set (Minkowski d)) ∩ W) ∈ 𝓝 (graphLift f x₀) := by
    rw [← hP, smul_mem_nhds_smul_iff]
    exact (O.isOpen.inter hWo).mem_nhds ⟨hpO, hPW⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (inter_mem (hU'.mem_nhds hx₀U)
    (hcont.preimage_mem_nhds hOW))
  set ρ := r / 2
  have hρ : 0 < ρ := half_pos hr
  have hρr : Metric.closedBall x₀ ρ ⊆ Metric.ball x₀ r :=
    Metric.closedBall_subset_ball (half_lt_self hr)
  set k := Real.sqrt (1 - (c : ℝ) ^ 2)
  have hk : 0 < k := Real.sqrt_pos.2 (by
    have : (c : ℝ) < 1 := by exact_mod_cast hc
    nlinarith [NNReal.coe_nonneg c])
  set G : Set (Minkowski d) := {z | z ∈ O ∧ z ∈ W ∧ (g • z).2 ∈ Metric.ball x₀ r}
  have hGo : IsOpen G := O.isOpen.inter (hWo.inter
    (Metric.isOpen_ball.preimage (continuous_snd.comp (continuous_const_smul g))))
  have hPG : P ∈ G := ⟨hpO, hPW, Metric.mem_ball_self hr⟩
  -- the compact piece over the closed frame ball, in `X`
  set Kc := (fun y => g⁻¹ • graphLift f y) '' Metric.closedBall x₀ ρ
  have hKcc : IsCompact Kc := (isCompact_closedBall x₀ ρ).image_of_continuousOn
    ((hlift.continuousOn.mono fun y hy => (hball (hρr hy)).1).const_smul g⁻¹)
  have hKcT : Kc ⊆ range ((U : Set X).restrict F) := by
    rintro _ ⟨y, hy, rfl⟩
    have hyb := hball (hρr hy)
    obtain ⟨z, ⟨hzO, -⟩, hzx⟩ := hyb.2
    have hm := mem_of_frame hgr hyb.1 (by rw [← hzx]; exact smul_mem_smul_set hzO)
    obtain ⟨u, hu, hux⟩ := hm.1
    exact ⟨⟨u, hu⟩, hux⟩
  have hKX : IsCompact (((↑) : U → X) '' ((U : Set X).restrict F ⁻¹' Kc)) :=
    ((hemb.isInducing.isCompact_preimage_iff hKcT).2 hKcc).image continuous_subtype_val
  have hKXc := hKX.isClosed
  have memKX : ∀ z, z ∈ (U : Set X) → F z ∈ Kc →
      z ∈ ((↑) : U → X) '' ((U : Set X).restrict F ⁻¹' Kc) := fun z hz hzK =>
    ⟨⟨z, hz⟩, hzK, rfl⟩
  rw [EMetric.mem_nhds_iff]
  refine ⟨ENNReal.ofReal (k * ρ), ENNReal.ofReal_pos.2 (mul_pos hk hρ), fun q hq => ?_⟩
  rw [Metric.mem_eball, edist_comm] at hq
  change (⨅ γ : Path x' (PulledLength.toSpace F q),
    pathLength (fun (_ : X) (y : X) => F y) γ) < _ at hq
  rw [iInf_lt_iff] at hq
  obtain ⟨γ, hγ⟩ := hq
  have hLip : IsLocLip (fun (_ : X) (y : X) => F y) γ.extend := by
    by_contra hn; rw [pathLength_of_not_isLocLip _ hn] at hγ; exact not_top_lt hγ
  obtain ⟨K, hK⟩ := (isLocLip_pulled_iff F γ).1 hLip
  rw [pathLength_of_isLocLip _ hLip, localLength_pulled] at hγ
  set Γ : ℝ → Minkowski d := fun t => F (γ.extend t) with hΓ
  have hΓc : Continuous Γ := hF.continuous.comp γ.continuous_extend
  have hΓ0 : Γ 0 = P := by simp [Γ, hPdef]
  have hγ0 : γ.extend 0 = x' := by simp
  set Tt : Set ℝ := {t | t ∈ Icc (0 : ℝ) 1 ∧ ∀ s ∈ Icc 0 t, γ.extend s ∈ (U : Set X) ∧ Γ s ∈ G}
  have h0T : (0 : ℝ) ∈ Tt := ⟨⟨le_rfl, zero_le_one⟩, fun s hs => by
    rw [show s = 0 from le_antisymm hs.2 hs.1, hγ0, hΓ0]; exact ⟨hxU, hPG⟩⟩
  have hTne : Tt.Nonempty := ⟨0, h0T⟩
  have hTbdd : BddAbove Tt := ⟨1, fun t ht => ht.1.2⟩
  set τ := sSup Tt
  have hτ0 : 0 ≤ τ := le_csSup hTbdd h0T
  have hτ1 : τ ≤ 1 := csSup_le hTne fun t ht => ht.1.2
  have hΓT : ∀ s, γ.extend s ∈ (U : Set X) → Γ s ∈ F '' (U : Set X) := fun s hs =>
    ⟨_, hs, rfl⟩
  have hA : ∀ t ∈ Tt, ‖(g • Γ t).2 - x₀‖ < ρ := fun t ht => by
    have hle := le_lorentzLength_of_frame hK ht.1.1 g hf fun s hs =>
      frame_mem_graphOver hgr (hΓT s (ht.2 s ⟨hs.1.le, hs.2.le⟩).1)
        (ht.2 s ⟨hs.1.le, hs.2.le⟩).2.1 |>.imp_right fun h' => by rw [h']; rfl
    rw [hΓ0] at hle
    have hlt := hle.trans_lt ((lorentzLength_mono le_rfl ht.1.2).trans_lt hγ)
    rw [ENNReal.ofReal_lt_ofReal_iff (mul_pos hk hρ)] at hlt
    exact lt_of_mul_lt_mul_left hlt hk.le
  have hdown : ∀ t ∈ Tt, ∀ s ∈ Icc (0 : ℝ) t, s ∈ Tt := fun t ht s hs =>
    ⟨⟨hs.1, hs.2.trans ht.1.2⟩, fun s' hs' => ht.2 s' ⟨hs'.1, hs'.2.trans hs.2⟩⟩
  have hB : ∀ s ∈ Ico (0 : ℝ) τ, s ∈ Tt := fun s hs => by
    obtain ⟨t, ht, hst⟩ := exists_lt_of_lt_csSup hTne hs.2
    exact hdown t ht s ⟨hs.1, hst.le⟩
  have hFK : ∀ s ∈ Tt, γ.extend s ∈ ((↑) : U → X) '' ((U : Set X).restrict F ⁻¹' Kc) :=
    fun s hs => by
      have hsU := (hs.2 s ⟨hs.1.1, le_rfl⟩).1
      obtain ⟨-, hFs⟩ := frame_mem_graphOver hgr (hΓT s hsU) (hs.2 s ⟨hs.1.1, le_rfl⟩).2.1
      refine memKX _ hsU ⟨(g • Γ s).2,
        Metric.mem_closedBall.2 ((dist_eq_norm _ _).trans_le (hA s hs).le), ?_⟩
      dsimp only; rw [← hFs, inv_smul_smul]
  have hC : γ.extend τ ∈ (U : Set X) ∧ Γ τ ∈ G := by
    rcases hτ0.eq_or_lt with h0 | hpos
    · rw [← h0, hγ0, show Γ 0 = P from hΓ0]; exact ⟨hxU, hPG⟩
    have hmemK : γ.extend τ ∈ ((↑) : U → X) '' ((U : Set X).restrict F ⁻¹' Kc) := by
      have hcl : τ ∈ closure (Ico 0 τ) := by rw [closure_Ico hpos.ne]; exact ⟨hτ0, le_rfl⟩
      have := mem_closure_image (f := γ.extend) γ.continuous_extend.continuousAt hcl
      refine closure_minimal ?_ hKXc this
      rintro _ ⟨s, hs, rfl⟩; exact hFK s (hB s hs)
    obtain ⟨⟨u, hu⟩, huK, hux⟩ := hmemK
    simp only at hux
    subst hux
    refine ⟨hu, ?_⟩
    obtain ⟨y, hy, hyF⟩ := huK
    obtain ⟨-, hyOW⟩ := hball (hρr hy)
    obtain ⟨z, ⟨hzO, hzW⟩, hzy⟩ := hyOW
    have hz : z = Γ τ := by
      change z = F (γ.extend τ)
      rw [show F (γ.extend τ) = (U : Set X).restrict F ⟨γ.extend τ, hu⟩ from rfl, ← hyF]
      dsimp only; rw [← hzy, inv_smul_smul]
    refine ⟨hz ▸ hzO, hz ▸ hzW, ?_⟩
    rw [← hz, show g • z = graphLift f y from hzy]; exact hρr hy
  have hτT : τ ∈ Tt := ⟨⟨hτ0, hτ1⟩, fun s hs => by
    rcases hs.2.lt_or_eq with hlt | heq
    · exact (hB s ⟨hs.1, hlt⟩).2 s ⟨hs.1, le_rfl⟩
    · rw [heq]; exact hC⟩
  have hτeq : τ = 1 := by
    by_contra hne
    have hlt : τ < 1 := lt_of_le_of_ne hτ1 hne
    have hopen : IsOpen {t : ℝ | γ.extend t ∈ (U : Set X) ∧ Γ t ∈ G} :=
      (U.isOpen.inter (hGo.preimage hF.continuous)).preimage γ.continuous_extend
    obtain ⟨η, hη, hηG⟩ := Metric.isOpen_iff.1 hopen τ hC
    set t' := min 1 (τ + η / 2)
    have ht' : t' ∈ Tt := ⟨⟨hτ0.trans (le_min hτ1 (by linarith)), min_le_left _ _⟩,
      fun s hs => by
        rcases le_or_gt s τ with hsτ | hsτ
        · exact hτT.2 s ⟨hs.1, hsτ⟩
        · refine hηG (Metric.mem_ball.2 ?_)
          rw [Real.dist_eq, abs_of_pos (by linarith)]
          linarith [hs.2.trans (min_le_right _ _)]⟩
    have := le_csSup hTbdd ht'
    have : τ < t' := lt_min hlt (by linarith)
    linarith
  have h1 := hτeq ▸ hC
  have hγ1 : γ.extend 1 = PulledLength.toSpace F q := by simp
  have hU1 : PulledLength.toSpace F q ∈ (U : Set X) := hγ1 ▸ h1.1
  have hW1 : F (PulledLength.toSpace F q) ∈ W := by
    have := h1.2.2.1
    rw [show Γ 1 = F (γ.extend 1) from rfl, hγ1] at this; exact this
  exact hMN (show (⟨_, hU1⟩ : U) ∈ (U : Set X).restrict F ⁻¹' M from hWM hW1)

section SegmentLifting

variable {X E : Type*} [TopologicalSpace X]

/-- **Uniqueness of lifts** through a local homeomorphism of a Hausdorff space, over a
preconnected set of parameters. -/
theorem lift_eqOn_of_isLocalHomeomorph [TopologicalSpace E] [T2Space X] {q : X → E}
    (hq : IsLocalHomeomorph q) {s : Set ℝ} (hs : IsPreconnected s) {l₁ l₂ : ℝ → X}
    (h₁ : ContinuousOn l₁ s) (h₂ : ContinuousOn l₂ s) (he : ∀ t ∈ s, q (l₁ t) = q (l₂ t))
    {t₀ : ℝ} (ht₀ : t₀ ∈ s) (h0 : l₁ t₀ = l₂ t₀) : EqOn l₁ l₂ s :=
  (T2Space.isSeparatedMap q).eqOn_of_comp_eqOn hq.isLocallyInjective hs h₁ h₂
    (fun t ht => he t ht) ht₀ h0

/-- **Gluing a lift with a chart**: a lift on `[0, T₁]` whose endpoint lies in the source of a
chart `e` of `q` extends to `[0, T₂]` as long as the path stays in `e.target`. -/
theorem exists_lift_glue [TopologicalSpace E] {q : X → E} {sg : ℝ → E} (hsg : Continuous sg)
    {l : ℝ → X} {T₁ T₂ : ℝ} (h0 : 0 ≤ T₁) (h12 : T₁ ≤ T₂) (hlc : ContinuousOn l (Icc 0 T₁))
    (hlq : ∀ t ∈ Icc 0 T₁, q (l t) = sg t) (e : OpenPartialHomeomorph X E) (he : ⇑e = q)
    (hle : l T₁ ∈ e.source) (hsge : ∀ t ∈ Icc T₁ T₂, sg t ∈ e.target) :
    ∃ μ : ℝ → X, ContinuousOn μ (Icc 0 T₂) ∧ μ 0 = l 0 ∧ ∀ t ∈ Icc 0 T₂, q (μ t) = sg t := by
  classical
  have hT : e.symm (sg T₁) = l T₁ := by
    rw [← hlq T₁ ⟨h0, le_rfl⟩, ← he]; exact e.left_inv hle
  refine ⟨fun t => if t ≤ T₁ then l t else e.symm (sg t), ?_, by simp [h0], ?_⟩
  · rw [← Icc_union_Icc_eq_Icc h0 h12]
    refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Icc isClosed_Icc
    · exact hlc.congr fun t ht => if_pos ht.2
    · refine (e.continuousOn_symm.comp hsg.continuousOn fun t ht => hsge t ht).congr fun t ht => ?_
      by_cases h : t ≤ T₁
      · have : t = T₁ := le_antisymm h ht.1
        simp only [Function.comp_apply, this, hT, ite_self]
      · simp only [if_neg h, Function.comp_apply]
  · intro t ht
    by_cases h : t ≤ T₁
    · simp only [if_pos h]; exact hlq t ⟨ht.1, h⟩
    · simp only [if_neg h]
      rw [← he]; exact e.right_inv (hsge t ⟨(not_le.1 h).le, ht.2⟩)

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Existence of lifts of segments** (the maximal-lift argument): if every lift of the segment
`t ↦ q x₀ + t v` on `[0, T)` has a cluster point as `t → T⁻` (the place where completeness enters),
the whole segment `[0, 1]` lifts from `x₀`. -/
theorem exists_lift_segment_of_mapClusterPt [T2Space X] {q : X → E} (hq : IsLocalHomeomorph q)
    (x₀ : X) (v : E)
    (hcomp : ∀ T : ℝ, 0 < T → ∀ l : ℝ → X, ContinuousOn l (Ico 0 T) →
      (∀ t ∈ Ico 0 T, q (l t) = q x₀ + t • v) → ∃ x, MapClusterPt x (𝓝[<] T) l) :
    ∃ l : ℝ → X, ContinuousOn l (Icc 0 1) ∧ l 0 = x₀ ∧ ∀ t ∈ Icc 0 1, q (l t) = q x₀ + t • v := by
  set sg : ℝ → E := fun t => q x₀ + t • v with hsgdef
  have hsg : Continuous sg := continuous_const.add (continuous_id.smul continuous_const)
  set A : Set ℝ := {T | 0 ≤ T ∧ T ≤ 1 ∧ ∃ l : ℝ → X, ContinuousOn l (Icc 0 T) ∧ l 0 = x₀ ∧
    ∀ t ∈ Icc 0 T, q (l t) = sg t} with hAdef
  have h0A : (0 : ℝ) ∈ A := ⟨le_rfl, zero_le_one, fun _ => x₀, continuousOn_const, rfl,
    fun t ht => by
      rw [show t = 0 from le_antisymm ht.2 ht.1]; simp [sg]⟩
  have hAne : A.Nonempty := ⟨0, h0A⟩
  have hAbdd : BddAbove A := ⟨1, fun T hT => hT.2.1⟩
  set Ts := sSup A with hTs
  have hTs0 : 0 ≤ Ts := le_csSup hAbdd h0A
  have hTs1 : Ts ≤ 1 := csSup_le hAne fun T hT => hT.2.1
  -- a chart at a point gives a radius on which `sg` stays in its target
  have hrad : ∀ (x : X) (e : OpenPartialHomeomorph X E) (T : ℝ), x ∈ e.source → ⇑e = q →
      q x = sg T → ∃ η > 0, ∀ t, |t - T| < η → sg t ∈ e.target := by
    intro x e T hx he hxT
    have hmem : sg T ∈ e.target := by rw [← hxT, ← he]; exact e.map_source hx
    obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.1 (e.open_target.preimage hsg) T hmem
    exact ⟨η, hη, fun t ht => hball (by rw [Metric.mem_ball, Real.dist_eq]; exact ht)⟩
  -- `Ts > 0`
  have hpos : 0 < Ts := by
    obtain ⟨e, hxe, he⟩ := hq x₀
    obtain ⟨η, hη, hηe⟩ := hrad x₀ e 0 hxe he.symm (by simp [sg])
    obtain ⟨μ, hμc, hμ0, hμq⟩ := exists_lift_glue (q := q) hsg (l := fun _ => x₀) le_rfl
      (le_min zero_le_one (half_pos hη).le) continuousOn_const
      (fun t ht => by rw [show t = 0 from le_antisymm ht.2 ht.1]; simp [sg]) e he.symm hxe
      fun t ht => hηe t (by
        rw [sub_zero, abs_of_nonneg ht.1]
        exact lt_of_le_of_lt (ht.2.trans (min_le_right _ _)) (half_lt_self hη))
    have hmem : min 1 (η / 2) ∈ A :=
      ⟨le_min zero_le_one (half_pos hη).le, min_le_left _ _, μ, hμc, hμ0, hμq⟩
    exact lt_of_lt_of_le (lt_min one_pos (half_pos hη)) (le_csSup hAbdd hmem)
  -- the lifts below `Ts` agree: the glued lift `Λ` on `[0, Ts)`
  have H : ∀ t ∈ Ico 0 Ts, ∃ y : X, ∀ (T : ℝ) (l : ℝ → X), ContinuousOn l (Icc 0 T) →
      l 0 = x₀ → (∀ s ∈ Icc 0 T, q (l s) = sg s) → t ≤ T → l t = y := by
    intro t ht
    obtain ⟨T', hT'A, htT'⟩ := exists_lt_of_lt_csSup hAne ht.2
    obtain ⟨-, -, l', hl'c, hl'0, hl'q⟩ := hT'A
    refine ⟨l' t, fun T l hlc hl0 hlq htT => ?_⟩
    have hsub : ∀ T'', Icc (0 : ℝ) (min T T') ⊆ Icc 0 T'' → True := fun _ _ => trivial
    exact lift_eqOn_of_isLocalHomeomorph hq isPreconnected_Icc
      (hlc.mono (Icc_subset_Icc le_rfl (min_le_left _ _)))
      (hl'c.mono (Icc_subset_Icc le_rfl (min_le_right _ _)))
      (fun s hs => by
        rw [hlq s ⟨hs.1, hs.2.trans (min_le_left _ _)⟩,
          hl'q s ⟨hs.1, hs.2.trans (min_le_right _ _)⟩])
      (⟨le_rfl, le_min (ht.1.trans htT) (ht.1.trans htT'.le)⟩ : (0 : ℝ) ∈ Icc 0 (min T T'))
      (by rw [hl0, hl'0]) ⟨ht.1, le_min htT htT'.le⟩
  haveI : Nonempty X := ⟨x₀⟩
  choose! Λ hΛ using H
  have hΛlift : ∀ t ∈ Ico 0 Ts, ∃ T ∈ A, t < T ∧ ∃ l : ℝ → X, ContinuousOn l (Icc 0 T) ∧
      l 0 = x₀ ∧ (∀ s ∈ Icc 0 T, q (l s) = sg s) ∧ ∀ s ∈ Ico 0 Ts, s ≤ T → l s = Λ s := by
    intro t ht
    obtain ⟨T', hT'A, htT'⟩ := exists_lt_of_lt_csSup hAne ht.2
    obtain ⟨h1, h2, l', hl'c, hl'0, hl'q⟩ := hT'A
    exact ⟨T', ⟨h1, h2, l', hl'c, hl'0, hl'q⟩, htT', l', hl'c, hl'0, hl'q,
      fun s hs hsT => hΛ s hs T' l' hl'c hl'0 hl'q hsT⟩
  have hΛc : ContinuousOn Λ (Ico 0 Ts) := by
    intro t ht
    obtain ⟨T', -, htT', l', hl'c, -, -, hl'Λ⟩ := hΛlift t ht
    have hnhds : Icc 0 T' ∈ 𝓝[Ico 0 Ts] t :=
      mem_nhdsWithin.2 ⟨Iio T', isOpen_Iio, htT', fun s hs => ⟨hs.2.1, hs.1.le⟩⟩
    refine ((hl'c t ⟨ht.1, htT'.le⟩).mono_of_mem_nhdsWithin hnhds).congr_of_eventuallyEq ?_
      (hl'Λ t ht htT'.le).symm
    filter_upwards [inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds
      (Iio_mem_nhds htT'))] with s hs
    exact (hl'Λ s hs.1 (le_of_lt hs.2)).symm
  have hΛq : ∀ t ∈ Ico 0 Ts, q (Λ t) = sg t := fun t ht => by
    obtain ⟨T', -, htT', l', -, -, hl'q, hl'Λ⟩ := hΛlift t ht
    rw [← hl'Λ t ht htT'.le]; exact hl'q t ⟨ht.1, htT'.le⟩
  have hΛ0 : Λ 0 = x₀ := (hΛ 0 ⟨le_rfl, hpos⟩ 0 (fun _ => x₀) continuousOn_const rfl
    (fun s hs => by rw [show s = 0 from le_antisymm hs.2 hs.1]; simp [sg]) le_rfl).symm
  -- completeness: a cluster point at `Ts`
  obtain ⟨xs, hxs⟩ := hcomp Ts hpos Λ hΛc hΛq
  have hev : ∀ᶠ t in 𝓝[<] Ts, t ∈ Ico 0 Ts := by
    filter_upwards [Ioo_mem_nhdsLT hpos] with t ht using ⟨ht.1.le, ht.2⟩
  have hqxs : q xs = sg Ts := by
    by_contra hne
    obtain ⟨N₁, N₂, hN₁, hN₂, hdisj⟩ := t2_separation_nhds hne
    have hfreq := (mapClusterPt_iff_frequently.1 hxs) _
      (hq.continuous.continuousAt.preimage_mem_nhds hN₁)
    have hev2 : ∀ᶠ t in 𝓝[<] Ts, sg t ∈ N₂ :=
      (hsg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hN₂
    obtain ⟨t, ht1, ht2, ht3⟩ := (hfreq.and_eventually (hev2.and hev)).exists
    rw [mem_preimage, hΛq t ht3] at ht1
    exact hdisj.le_bot ⟨ht1, ht2⟩
  obtain ⟨e, hxse, he⟩ := hq xs
  obtain ⟨η, hη, hηe⟩ := hrad xs e Ts hxse he.symm hqxs
  have hfreq := (mapClusterPt_iff_frequently.1 hxs) _ (e.open_source.mem_nhds hxse)
  have hev3 : ∀ᶠ t in 𝓝[<] Ts, Ts - η < t := by
    filter_upwards [Ioo_mem_nhdsLT (show Ts - η < Ts by linarith)] with t ht using ht.1
  obtain ⟨t₁, ht₁e, ht₁η, ht₁I⟩ := (hfreq.and_eventually (hev3.and hev)).exists
  set T₂ := min 1 (Ts + η / 2)
  obtain ⟨μ, hμc, hμ0, hμq⟩ := exists_lift_glue (q := q) hsg (l := Λ) (T₂ := T₂) ht₁I.1
    (le_min (ht₁I.2.le.trans hTs1) (by linarith [ht₁I.2])) (hΛc.mono
      (Icc_subset_Ico_right ht₁I.2)) (fun t ht => hΛq t ⟨ht.1, ht.2.trans_lt ht₁I.2⟩) e
    he.symm ht₁e fun t ht => hηe t (by
      rw [abs_lt]; constructor
      · linarith [ht.1]
      · linarith [ht.2.trans (min_le_right _ _)])
  have hT₂A : T₂ ∈ A := ⟨le_min zero_le_one (by linarith), min_le_left _ _, μ, hμc,
    hμ0.trans hΛ0, hμq⟩
  have hT₂ : T₂ = 1 := by
    have h := le_csSup hAbdd hT₂A
    rcases min_choice 1 (Ts + η / 2) with h' | h'
    · exact h'
    · exfalso; rw [show T₂ = Ts + η / 2 from h'] at h; linarith
  obtain ⟨-, -, l, hlc, hl0, hlq⟩ := hT₂ ▸ hT₂A
  exact ⟨l, hlc, hl0, hlq⟩


/-- **Segment lifting makes a local homeomorphism onto a normed space a homeomorphism**: the
radial lift from a base point is a continuous section (continuity along the segment by a clopen
argument on `[0, 1]`), and a continuous section of a local homeomorphism of a connected Hausdorff
space through one point of each fibre is a two-sided inverse. -/
theorem isHomeomorph_of_lift_segment [T2Space X] [ConnectedSpace X] {q : X → E}
    (hq : IsLocalHomeomorph q)
    (hlift : ∀ (x₀ : X) (v : E), ∃ l : ℝ → X, ContinuousOn l (Icc 0 1) ∧ l 0 = x₀ ∧
      ∀ t ∈ Icc 0 1, q (l t) = q x₀ + t • v) : IsHomeomorph q := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  set y₀ := q x₀ with hy₀
  choose L hLc hL0 hLq0 using fun y : E => hlift x₀ (y - y₀)
  set sg : E → ℝ → E := fun y t => y₀ + t • (y - y₀) with hsg
  have hLq : ∀ y, ∀ t ∈ Icc (0 : ℝ) 1, q (L y t) = sg y t := fun y t ht => hLq0 y t ht
  have hsgc : Continuous fun p : E × ℝ => sg p.1 p.2 :=
    continuous_const.add (continuous_snd.smul (continuous_fst.sub continuous_const))
  -- the δ-lemma
  have hδ : ∀ y : E, ∀ t ∈ Icc (0 : ℝ) 1, ∃ δ > 0, ∀ t₁ ∈ Icc (0 : ℝ) 1, |t₁ - t| < δ →
      ContinuousAt (fun y' => L y' t₁) y →
      ∀ t' ∈ Icc (0 : ℝ) 1, |t' - t| < δ → ContinuousAt (fun y' => L y' t') y := by
    intro y t ht
    obtain ⟨e, hxe, he⟩ := hq (L y t)
    have hmem : sg y t ∈ e.target := by
      rw [show sg y t = q (L y t) from (hLq y t ht).symm, he]; exact e.map_source hxe
    obtain ⟨ε, hε, hεb⟩ := Metric.isOpen_iff.1 (e.open_target.preimage hsgc) (y, t) hmem
    have hε' : ∀ y' t', dist y' y < ε → |t' - t| < ε → sg y' t' ∈ e.target := fun y' t' h1 h2 =>
      hεb (show dist (y', t') (y, t) < ε by
        rw [Prod.dist_eq, max_lt_iff, Real.dist_eq]; exact ⟨h1, h2⟩)
    have hcw := hLc y t ht
    obtain ⟨δ₂, hδ₂, hδ₂b⟩ := Metric.mem_nhdsWithin_iff.1
      (hcw.preimage_mem_nhdsWithin (e.open_source.mem_nhds hxe))
    refine ⟨min ε δ₂, lt_min hε hδ₂, fun t₁ ht₁ ht₁t hP t' ht' ht't => ?_⟩
    have hLt₁ : L y t₁ ∈ e.source := hδ₂b ⟨by
      rw [Metric.mem_ball, Real.dist_eq]; exact ht₁t.trans_le (min_le_right _ _), ht₁⟩
    have hev : ∀ᶠ y' in 𝓝 y, L y' t' = e.symm (sg y' t') := by
      filter_upwards [hP.preimage_mem_nhds (e.open_source.mem_nhds hLt₁),
        Metric.ball_mem_nhds y hε] with y' hy'e hy'b
      have hJ : uIcc t₁ t' ⊆ Icc 0 1 := uIcc_subset_Icc ht₁ ht'
      have hJt : ∀ s ∈ uIcc t₁ t', |s - t| < min ε δ₂ := fun s hs => by
        rw [abs_lt] at ht₁t ht't ⊢
        rcases le_total t₁ t' with h | h
        · rw [uIcc_of_le h] at hs; constructor <;> linarith [hs.1, hs.2]
        · rw [uIcc_of_ge h] at hs; constructor <;> linarith [hs.1, hs.2]
      have htg : ∀ s ∈ uIcc t₁ t', sg y' s ∈ e.target := fun s hs =>
        hε' y' s hy'b ((hJt s hs).trans_le (min_le_left _ _))
      have hEq := lift_eqOn_of_isLocalHomeomorph (l₂ := fun s => e.symm (sg y' s)) hq
        isPreconnected_uIcc ((hLc y').mono hJ) (e.continuousOn_symm.comp
          (hsgc.comp (Continuous.prodMk_right y')).continuousOn fun s hs => htg s hs)
        (fun s hs => by
          rw [hLq y' s (hJ hs), he, e.right_inv (htg s hs)])
        left_mem_uIcc (by
          show L y' t₁ = e.symm (sg y' t₁)
          rw [← hLq y' t₁ ht₁, he]; exact (e.left_inv hy'e).symm)
      exact hEq right_mem_uIcc
    have hc2 : ContinuousAt (fun y' => sg y' t') y :=
      (hsgc.comp (Continuous.prodMk_left t')).continuousAt
    have hct : ContinuousAt (fun y' => e.symm (sg y' t')) y :=
      ContinuousAt.comp (f := fun y' => sg y' t') (g := e.symm)
        (e.continuousAt_symm (hε' y t' (by simpa using hε) (ht't.trans_le (min_le_left _ _)))) hc2
    exact hct.congr (hev.mono fun y' h => h.symm)
  -- continuity of `y ↦ L y t` for every `t`, by connectedness of `[0, 1]`
  have hP : ∀ y : E, ∀ t ∈ Icc (0 : ℝ) 1, ContinuousAt (fun y' => L y' t) y := by
    intro y
    set S : Set I := {t | ContinuousAt (fun y' => L y' (t : ℝ)) y}
    have hS0 : (0 : I) ∈ S := by
      show ContinuousAt (fun y' => L y' 0) y
      simp only [hL0]; exact continuousAt_const
    have hSo : IsOpen S := by
      refine Metric.isOpen_iff.2 fun t ht => ?_
      obtain ⟨δ, hδ0, hδb⟩ := hδ y t t.2
      refine ⟨δ, hδ0, fun t' ht' => ?_⟩
      rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq] at ht'
      exact hδb t t.2 (by simpa using hδ0) ht t' t'.2 ht'
    have hSc : IsClosed S := by
      refine isClosed_of_closure_subset fun t ht => ?_
      obtain ⟨δ, hδ0, hδb⟩ := hδ y t t.2
      obtain ⟨t₁, ht₁S, ht₁d⟩ := Metric.mem_closure_iff.1 ht δ hδ0
      rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm] at ht₁d
      exact hδb t₁ t₁.2 ht₁d ht₁S t t.2 (by simpa using hδ0)
    have := (IsClopen.eq_univ ⟨hSc, hSo⟩ ⟨0, hS0⟩)
    intro t ht
    have : (⟨t, ht⟩ : I) ∈ S := by rw [this]; trivial
    exact this
  set s : E → X := fun y => L y 1 with hsdef
  have hs : Continuous s := continuous_iff_continuousAt.2 fun y => hP y 1 ⟨zero_le_one, le_rfl⟩
  have hqs : ∀ y, q (s y) = y := fun y => by
    rw [hsdef, hLq y 1 ⟨zero_le_one, le_rfl⟩]
    show y₀ + (1 : ℝ) • (y - y₀) = y
    rw [one_smul, add_sub_cancel]
  have hsq0 : s y₀ = x₀ := by
    have := lift_eqOn_of_isLocalHomeomorph hq isPreconnected_Icc (hLc y₀) continuousOn_const
      (fun t ht => by
        rw [hLq y₀ t ht]; show y₀ + t • (y₀ - y₀) = q x₀; rw [sub_self, smul_zero, add_zero])
      (left_mem_Icc.2 zero_le_one)
      (hL0 y₀)
    exact this (right_mem_Icc.2 zero_le_one)
  set Eq' : Set X := {x | s (q x) = x}
  have hEc : IsClosed Eq' := isClosed_eq (hs.comp hq.continuous) continuous_id
  have hEo : IsOpen Eq' := by
    refine isOpen_iff_mem_nhds.2 fun x hx => ?_
    obtain ⟨e, hxe, he⟩ := hq x
    have h1 : ∀ᶠ x' in 𝓝 x, s (q x') ∈ e.source :=
      (hs.comp hq.continuous).continuousAt.preimage_mem_nhds
        (by rw [Function.comp_apply, hx]; exact e.open_source.mem_nhds hxe)
    filter_upwards [h1, e.open_source.mem_nhds hxe] with x' h1' h2'
    exact e.injOn h1' h2' (by rw [← he, hqs])
  have hsq : ∀ x, s (q x) = x := fun x => by
    have := IsClopen.eq_univ ⟨hEc, hEo⟩ ⟨x₀, hsq0⟩
    have hx : x ∈ Eq' := by rw [this]; trivial
    exact hx
  exact (Homeomorph.mk ⟨q, s, hsq, hqs⟩ hq.continuous hs).isHomeomorph

end SegmentLifting

/-- A homeomorphism is a covering map (fibre `PUnit`). -/
theorem isCoveringMap_of_isHomeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {q : X → Y} (hq : IsHomeomorph q) : IsCoveringMap q := by
  intro y
  have h : IsEvenlyCovered q y PUnit.{1} := by
    exact ⟨inferInstance, univ, mem_univ y, isOpen_univ, by simp,
      ((Homeomorph.setCongr (preimage_univ (f := q))).trans ((Homeomorph.Set.univ X).trans
        (hq.homeomorph q))).trans ((Homeomorph.Set.univ Y).symm.trans
          (Homeomorph.prodPUnit (univ : Set Y)).symm), fun x => rfl⟩
  exact h.to_isEvenlyCovered_preimage

/-! #### Lifts through a linear projection: lengths and endpoints -/

section ProjLift

variable {X : Type*} [TopologicalSpace X] {F : X → Minkowski d} {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Along a lift of an affine path through `P ∘ F`, the developed curve `F ∘ l` is locally
Lipschitz, if `F` is locally controlled by `P ∘ F`. -/
theorem locallyLipschitzOn_lift_of_proj (P : Minkowski d →L[ℝ] E)
    (hloc : ∀ x : X, ∃ W ∈ 𝓝 x, ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ W, ∀ b ∈ W,
      ‖F a - F b‖ ≤ C * ‖P (F a) - P (F b)‖)
    {a v : E} {s : Set ℝ} {l : ℝ → X} (hl : ContinuousOn l s)
    (hlq : ∀ t ∈ s, P (F (l t)) = a + t • v) :
    LocallyLipschitzOn s (fun t => F (l t)) := by
  intro t ht
  obtain ⟨W, hW, C, hC, hCW⟩ := hloc (l t)
  refine ⟨Real.toNNReal (C * ‖v‖), s ∩ l ⁻¹' W,
    inter_mem self_mem_nhdsWithin ((hl t ht).preimage_mem_nhdsWithin hW),
    LipschitzOnWith.of_dist_le_mul fun t₁ h₁ t₂ h₂ => ?_⟩
  rw [dist_eq_norm, Real.coe_toNNReal _ (mul_nonneg hC (norm_nonneg _)), Real.dist_eq]
  refine (hCW _ h₁.2 _ h₂.2).trans ?_
  rw [hlq t₁ h₁.1, hlq t₂ h₂.1, add_sub_add_left_eq_sub, ← sub_smul, norm_smul,
    Real.norm_eq_abs]
  exact le_of_eq (by ring)

/-- **The length bound of a lift** (step (iii) of 8.1): if `P w = c v` forces
`minkQ w ≤ c² M`, then between two times of a lift of `t ↦ a + t v` through `P ∘ F` the
pulled distance is at most `(t₂ − t₁) √M`. -/
theorem edist_lift_le_of_proj (P : Minkowski d →L[ℝ] E)
    (hloc : ∀ x : X, ∃ W ∈ 𝓝 x, ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ W, ∀ b ∈ W,
      ‖F a - F b‖ ≤ C * ‖P (F a) - P (F b)‖)
    {a v : E} {M : ℝ} (hden : ∀ (w : Minkowski d) (c : ℝ), P w = c • v → minkQ w ≤ c ^ 2 * M)
    {s : Set ℝ} {l : ℝ → X} (hl : ContinuousOn l s)
    (hlq : ∀ t ∈ s, P (F (l t)) = a + t • v) {t₁ t₂ : ℝ} (h12 : t₁ ≤ t₂)
    (hs : Icc t₁ t₂ ⊆ s) :
    edist ((PulledLength.toSpace F).symm (l t₁)) ((PulledLength.toSpace F).symm (l t₂)) ≤
      ENNReal.ofReal ((t₂ - t₁) * Real.sqrt M) := by
  set h : ℝ → ℝ := fun u => t₁ + (projIcc (0 : ℝ) 1 zero_le_one u : ℝ) * (t₂ - t₁) with hh
  have hhI : ∀ u, h u ∈ Icc t₁ t₂ := fun u => by
    have h0 := (projIcc (0 : ℝ) 1 zero_le_one u).2
    constructor <;> simp only [hh] <;> nlinarith [h0.1, h0.2]
  have hcI : Continuous fun u : I => t₁ + (u : ℝ) * (t₂ - t₁) := by fun_prop
  let β : Path (l t₁) (l t₂) :=
    { toFun := fun u => l (t₁ + (u : ℝ) * (t₂ - t₁))
      continuous_toFun := (hl.mono hs).comp_continuous hcI fun u => by
        constructor <;> nlinarith [u.2.1, u.2.2]
      source' := by simp
      target' := by simp }
  have hβ : ∀ u, β.extend u = l (h u) := fun u => rfl
  obtain ⟨K, hK⟩ := ((locallyLipschitzOn_lift_of_proj P hloc hl hlq).mono
    hs).exists_lipschitzOnWith_of_compact isCompact_Icc
  have hhL : LipschitzWith (Real.toNNReal (t₂ - t₁)) h := by
    refine LipschitzWith.of_dist_le_mul fun u u' => ?_
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by linarith)]
    simp only [hh]
    rw [show t₁ + (projIcc (0 : ℝ) 1 zero_le_one u : ℝ) * (t₂ - t₁) -
        (t₁ + (projIcc (0 : ℝ) 1 zero_le_one u' : ℝ) * (t₂ - t₁)) =
        ((projIcc (0 : ℝ) 1 zero_le_one u : ℝ) - projIcc 0 1 zero_le_one u') * (t₂ - t₁) by ring,
      abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ t₂ - t₁), mul_comm]
    exact mul_le_mul_of_nonneg_left (abs_projIcc_sub_projIcc _) (by linarith)
  have hΓL : LipschitzWith (K * Real.toNNReal (t₂ - t₁)) fun u => F (β.extend u) := by
    have := hK.comp hhL.lipschitzOnWith (s := univ) fun u _ => hhI u
    exact lipschitzOnWith_univ.1 this
  have hLoc : IsLocLip (fun (_ : X) (y : X) => F y) β.extend :=
    (isLocLip_pulled_iff F β).2 ⟨_, hΓL⟩
  refine (iInf_le _ β).trans ?_
  change pathLength (fun (_ : X) (y : X) => F y) β ≤ _
  rw [pathLength_of_isLocLip _ hLoc, localLength_pulled]
  set Γ : ℝ → Minkowski d := fun u => F (β.extend u) with hΓ
  have hpt : ∀ u ∈ Ioo (0 : ℝ) 1, ENNReal.ofReal (Real.sqrt (minkQ (deriv Γ u))) ≤
      ENNReal.ofReal ((t₂ - t₁) * Real.sqrt M) := by
    intro u hu
    refine ENNReal.ofReal_le_ofReal ?_
    by_cases hd : DifferentiableAt ℝ Γ u
    · have h1 : HasDerivAt (fun u => P (Γ u)) (P (deriv Γ u)) u :=
        P.hasFDerivAt.comp_hasDerivAt u hd.hasDerivAt
      have h2 : HasDerivAt (fun u' => a + (t₁ + u' * (t₂ - t₁)) • v) ((t₂ - t₁) • v) u := by
        have := (((hasDerivAt_id u).mul_const (t₂ - t₁)).const_add t₁).smul_const v
        simpa using this.const_add a
      have heq : (fun u => P (Γ u)) =ᶠ[𝓝 u] fun u' => a + (t₁ + u' * (t₂ - t₁)) • v := by
        filter_upwards [Ioo_mem_nhds hu.1 hu.2] with u' hu'
        have hp : (projIcc (0 : ℝ) 1 zero_le_one u' : ℝ) = u' := by
          rw [projIcc_of_mem _ ⟨hu'.1.le, hu'.2.le⟩]
        simp only [hΓ, hβ]
        rw [hlq _ (hs (hhI u'))]
        simp only [hh, hp]
      have hD : P (deriv Γ u) = (t₂ - t₁) • v := h1.unique (h2.congr_of_eventuallyEq heq)
      calc Real.sqrt (minkQ (deriv Γ u)) ≤ Real.sqrt ((t₂ - t₁) ^ 2 * M) :=
            Real.sqrt_le_sqrt (hden _ _ hD)
        _ = (t₂ - t₁) * Real.sqrt M := by
            rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by linarith)]
    · rw [deriv_zero_of_not_differentiableAt hd, minkQ_zero, Real.sqrt_zero]
      exact mul_nonneg (by linarith) (Real.sqrt_nonneg _)
  calc lorentzLength Γ 0 1
        = ∫⁻ u in Ioo (0 : ℝ) 1, ENNReal.ofReal (Real.sqrt (minkQ (deriv Γ u))) :=
        (setLIntegral_congr Ioo_ae_eq_Ioc).symm
    _ ≤ ∫⁻ _u in Ioo (0 : ℝ) 1, ENNReal.ofReal ((t₂ - t₁) * Real.sqrt M) :=
        setLIntegral_mono measurable_const hpt
    _ = _ := by rw [setLIntegral_const, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one, mul_one]

/-- **Completeness gives the endpoint** (steps (ii)+(iii) of 8.1): a lift on `[0, T)` of an
affine path through `P ∘ F` converges in `X` as `t → T⁻`, when the pulled length is complete. -/
theorem SpacelikeDevelopment.tendsto_lift_of_proj [T2Space X] (hF : SpacelikeDevelopment F)
    (hc : CompleteSpace (PulledLength F)) (P : Minkowski d →L[ℝ] E)
    (hloc : ∀ x : X, ∃ W ∈ 𝓝 x, ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ W, ∀ b ∈ W,
      ‖F a - F b‖ ≤ C * ‖P (F a) - P (F b)‖)
    {a v : E} {M : ℝ} (hden : ∀ (w : Minkowski d) (c : ℝ), P w = c • v → minkQ w ≤ c ^ 2 * M)
    {T : ℝ} (hT : 0 < T) {l : ℝ → X} (hl : ContinuousOn l (Ico 0 T))
    (hlq : ∀ t ∈ Ico 0 T, P (F (l t)) = a + t • v) :
    ∃ x, Tendsto l (𝓝[<] T) (𝓝 x) := by
  set Cv := Real.sqrt M
  have hCv : 0 ≤ Cv := Real.sqrt_nonneg _
  set f := map (fun t => (PulledLength.toSpace F).symm (l t)) (𝓝[<] T)
  have hf : Cauchy f := by
    rw [EMetric.cauchy_iff]
    refine ⟨(map_neBot (hf := nhdsLT_neBot T)).ne, fun ε hε => ?_⟩
    have hlim : Tendsto (fun η : ℝ => ENNReal.ofReal (η * Cv)) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun η : ℝ => η * Cv) (𝓝 0) (𝓝 0) := by
        simpa using (continuous_mul_const Cv).tendsto 0
      simpa using (ENNReal.tendsto_ofReal this).mono_left nhdsWithin_le_nhds
    obtain ⟨η, hηε, hη⟩ := ((hlim.eventually (gt_mem_nhds hε)).and self_mem_nhdsWithin).exists
    refine ⟨(fun t => (PulledLength.toSpace F).symm (l t)) '' Ioo (max 0 (T - η)) T,
      image_mem_map (Ioo_mem_nhdsLT (max_lt hT (by linarith [show (0:ℝ) < η from hη]))),
      ?_⟩
    rintro _ ⟨t, ht, rfl⟩ _ ⟨t', ht', rfl⟩
    have hsub : ∀ {u u' : ℝ}, u ∈ Ioo (max 0 (T - η)) T → u' ∈ Ioo (max 0 (T - η)) T →
        Icc u u' ⊆ Ico 0 T := fun hu hu' w hw =>
      ⟨(le_max_left _ _).trans (hu.1.le.trans hw.1), hw.2.trans_lt hu'.2⟩
    have hdist : ∀ {u u' : ℝ}, u ∈ Ioo (max 0 (T - η)) T → u' ∈ Ioo (max 0 (T - η)) T →
        u ≤ u' → u' - u < η := fun hu hu' _ => by
      have := le_max_right 0 (T - η); linarith [hu.1, hu'.2]
    rcases le_total t t' with h | h
    · refine (edist_lift_le_of_proj P hloc hden hl hlq h (hsub ht ht')).trans_lt
        (lt_of_le_of_lt ?_ hηε)
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hdist ht ht' h).le hCv)
    · rw [edist_comm]
      refine (edist_lift_le_of_proj P hloc hden hl hlq h (hsub ht' ht)).trans_lt
        (lt_of_le_of_lt ?_ hηε)
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hdist ht' ht h).le hCv)
  obtain ⟨x, hx⟩ := CompleteSpace.complete hf
  refine ⟨PulledLength.toSpace F x, ?_⟩
  have := (hF.continuous_toSpace.tendsto x).comp hx
  simpa [Function.comp_def] using this

/-- **Segment lifting through `P ∘ F`**, for a direction `v` whose `P`-preimages satisfy the
density bound. -/
theorem SpacelikeDevelopment.exists_lift_of_proj [T2Space X] (hF : SpacelikeDevelopment F)
    (hc : CompleteSpace (PulledLength F)) (P : Minkowski d →L[ℝ] E)
    (hq : IsLocalHomeomorph (P ∘ F))
    (hloc : ∀ x : X, ∃ W ∈ 𝓝 x, ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ W, ∀ b ∈ W,
      ‖F a - F b‖ ≤ C * ‖P (F a) - P (F b)‖)
    (x₀ : X) {v : E} {M : ℝ}
    (hden : ∀ (w : Minkowski d) (c : ℝ), P w = c • v → minkQ w ≤ c ^ 2 * M) :
    ∃ l : ℝ → X, ContinuousOn l (Icc 0 1) ∧ l 0 = x₀ ∧
      ∀ t ∈ Icc 0 1, (P ∘ F) (l t) = (P ∘ F) x₀ + t • v := by
  refine exists_lift_segment_of_mapClusterPt hq x₀ v fun T hT l hl hlq => ?_
  obtain ⟨x, hx⟩ := hF.tendsto_lift_of_proj hc P hloc hden hT hl hlq
  exact ⟨x, hx.mapClusterPt⟩

end ProjLift

/-- **Prop 8.1, the covering** (`GHFspace.tex` l.2243–2261): `π ∘ F` is a covering map — in fact a
homeomorphism. (i) charts: `SpacelikeDevelopment.exists_chart`; (ii) the pulled-length topology
is finer than `X`'s: `SpacelikeDevelopment.continuous_toSpace`; (iii) maximal lifts of straight
segments of `Δ^⊥` (W5: rectifiable paths only) have pulled length at most the segment's
(`edist_lift_le_of_proj`, through `minkQ_le_minkQ_projAlong`), so they converge by completeness
(`SpacelikeDevelopment.tendsto_lift_of_proj`) and extend (`exists_lift_segment_of_mapClusterPt`);
(iv) the radial lift is a continuous inverse (`isHomeomorph_of_lift_segment`). -/
theorem isCoveringMap_projAlong_comp {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    [T2Space X] {F : X → Minkowski d} (hF : SpacelikeDevelopment F)
    (hc : CompleteSpace (PulledLength F)) {Δ : Minkowski d} (hΔ : minkQ Δ < 0) :
    IsCoveringMap (projAlong Δ hΔ.ne ∘ F) := by
  have hq : IsLocalHomeomorph (projAlong Δ hΔ.ne ∘ F) := fun x => by
    obtain ⟨e, hxe, he, -⟩ := hF.exists_chart hΔ x
    exact ⟨e, hxe, he.symm⟩
  have hloc : ∀ x : X, ∃ W ∈ 𝓝 x, ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ W, ∀ b ∈ W,
      ‖F a - F b‖ ≤ C * ‖projAlong Δ hΔ.ne (F a) - projAlong Δ hΔ.ne (F b)‖ := fun x => by
    obtain ⟨e, hxe, -, hnn⟩ := hF.exists_chart hΔ x
    refine ⟨e.source, e.open_source.mem_nhds hxe, projLipConst Δ, projLipConst_nonneg Δ,
      fun a ha b hb => ?_⟩
    rw [← map_sub]; exact norm_le_of_minkQ_nonneg hΔ (hnn a ha b hb)
  refine isCoveringMap_of_isHomeomorph (isHomeomorph_of_lift_segment hq fun x₀ v =>
    hF.exists_lift_of_proj hc _ hq hloc x₀ (M := minkQ (v : Minkowski d)) fun w c hw => ?_)
  calc minkQ w ≤ minkQ (projAlong Δ hΔ.ne w : Minkowski d) := minkQ_le_minkQ_projAlong hΔ w
    _ = c ^ 2 * minkQ (v : Minkowski d) := by rw [hw, Submodule.coe_smul, minkQ_smul]

theorem bprop_project {X : Type*} [TopologicalSpace X] [ConnectedSpace X] [T2Space X]
    {F : X → Minkowski d} (hF : SpacelikeDevelopment F) (hc : CompleteSpace (PulledLength F))
    {Δ : Minkowski d} (hΔ : minkQ Δ < 0) :
    IsHomeomorph (projAlong Δ hΔ.ne ∘ F) :=
  isHomeomorph_of_isCoveringMap (isCoveringMap_projAlong_comp hF hc hΔ)

/-! #### A spacelike Lipschitz hypersurface contains no germ of null segment -/

theorem eventually_add_smul_mem {O : Set (Minkowski d)} (hO : IsOpen O) {p : Minkowski d}
    (hp : p ∈ O) (ℓ : Minkowski d) : ∀ᶠ s in 𝓝 (0 : ℝ), p + s • ℓ ∈ O := by
  have hc : Continuous fun s : ℝ => p + s • ℓ := continuous_const.add (continuous_id.smul continuous_const)
  have : Tendsto (fun s : ℝ => p + s • ℓ) (𝓝 0) (𝓝 p) := by
    simpa using hc.tendsto (0 : ℝ)
  exact this.eventually (hO.mem_nhds hp)

/-- A null vector has `|v.1| = ‖v.2‖`. -/
theorem abs_fst_eq_norm_of_minkQ_eq_zero {v : Minkowski d} (hv : minkQ v = 0) :
    |v.1| = ‖v.2‖ := by
  have h : v.1 ^ 2 = ‖v.2‖ ^ 2 := by unfold minkQ at hv; linarith
  rw [← Real.sqrt_sq_eq_abs, h, Real.sqrt_sq (norm_nonneg _)]

/-- **A spacelike Lipschitz hypersurface contains no germ of null segment**: if `p ∈ T` and
`ℓ ≠ 0` is null, `p + s ℓ ∉ T` for arbitrarily small `s > 0`. In a frame where `T` is a
`c`-Lipschitz graph, `c < 1`, a null displacement has slope exactly `1`. -/
theorem IsSpacelikeLipschitzIn.not_eventually_add_smul_mem {V : Opens (Minkowski d)}
    {T : Set (Minkowski d)} (hT : IsSpacelikeLipschitzIn V T) {p ℓ : Minkowski d} (hp : p ∈ T)
    (hℓ0 : ℓ ≠ 0) (hℓ : minkQ ℓ = 0) : ¬ ∀ᶠ s in 𝓝[>] (0 : ℝ), p + s • ℓ ∈ T := by
  intro h
  obtain ⟨g, O, U', f', c, hc1, hpO, -, -, hf', hgr⟩ := hT.locGraph p hp
  have hO : ∀ᶠ s in 𝓝[>] (0 : ℝ), p + s • ℓ ∈ O :=
    nhdsWithin_le_nhds (eventually_add_smul_mem O.isOpen hpO ℓ)
  have hpos : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s := self_mem_nhdsWithin
  obtain ⟨s, hsT, hsO, hs0⟩ := (h.and (hO.and hpos)).exists
  have h0 := frame_mem_graphOver hgr hp hpO
  have h1 := frame_mem_graphOver hgr hsT hsO
  have f0 : (g • p).1 = f' (g • p).2 := congrArg Prod.fst h0.2
  have f1 : (g • (p + s • ℓ)).1 = f' (g • (p + s • ℓ)).2 := congrArg Prod.fst h1.2
  have hL := hf'.dist_le_mul _ h1.1 _ h0.1
  set w := (g : Minkowski d ≃ᵃ[ℝ] Minkowski d).linear ℓ with hw
  have hdiff : g • (p + s • ℓ) - g • p = s • w := by
    rw [isom_smul_def, isom_smul_def, isom_sub, add_sub_cancel_left, map_smul]
  have hwQ : minkQ w = 0 := by
    rw [hw, show ((g : Minkowski d ≃ᵃ[ℝ] Minkowski d).linear ℓ) =
      (linearPart g : Minkowski d ≃ₗ[ℝ] Minkowski d) ℓ from rfl,
      lorentz.minkQ_apply (linearPart g).2, hℓ]
  have hw0 : w ≠ 0 := by
    rw [hw]; intro h0'
    exact hℓ0 ((g : Minkowski d ≃ᵃ[ℝ] Minkowski d).linear.map_eq_zero_iff.1 h0')
  have hw1 : w.1 ≠ 0 := fun h' => hw0 (eq_zero_of_fst_eq_zero h' hwQ.le)
  have e1 : (g • (p + s • ℓ)).1 - (g • p).1 = s * w.1 := by
    have := congrArg Prod.fst hdiff; simpa using this
  have e2 : (g • (p + s • ℓ)).2 - (g • p).2 = s • w.2 := by
    have := congrArg Prod.snd hdiff; simpa using this
  rw [Real.dist_eq, dist_eq_norm, ← f0, ← f1, e1, e2, norm_smul, abs_mul,
    abs_fst_eq_norm_of_minkQ_eq_zero hwQ, Real.norm_eq_abs] at hL
  have hpos : 0 < |s| * ‖w.2‖ := by
    rw [← abs_fst_eq_norm_of_minkQ_eq_zero hwQ]
    exact mul_pos (abs_pos.2 (ne_of_gt hs0)) (abs_pos.2 hw1)
  have : (1 : ℝ) ≤ c := by
    by_contra hlt
    have hlt' := not_le.1 hlt
    nlinarith
  exact absurd hc1 (not_lt.2 (by exact_mod_cast this))

/-- A `1`-Lipschitz map attaining slope `1` between two points is affine of slope `1` on the
segment. -/
theorem lipschitzWith_one_segment {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : LipschitzWith 1 g)
    {x y : EuclideanSpace ℝ (Fin d)} (hxy : g y - g x = ‖y - x‖) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    g (x + s • (y - x)) = g x + s * ‖y - x‖ := by
  have h1 := abs_sub_le_of_lipschitz (κ := 1) hg (x + s • (y - x)) x
  have h2 := abs_sub_le_of_lipschitz (κ := 1) hg y (x + s • (y - x))
  have n1 : ‖x + s • (y - x) - x‖ = s * ‖y - x‖ := by
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
  have n2 : ‖y - (x + s • (y - x))‖ = (1 - s) * ‖y - x‖ := by
    rw [show y - (x + s • (y - x)) = (1 - s) • (y - x) by
      rw [sub_smul, one_smul]; abel, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [hs.2])]
  rw [n1, NNReal.coe_one, one_mul] at h1
  rw [n2, NNReal.coe_one, one_mul] at h2
  have := (abs_le.1 h1).2
  have := (abs_le.1 h2).2
  linarith

/-! #### The immediate corollary (l.2307–2309): an entire acausal graph -/

section Consequences

variable {X : Type*} [TopologicalSpace X] [ConnectedSpace X] [T2Space X] {F : X → Minkowski d}

/-- `F` is injective. -/
theorem SpacelikeDevelopment.injective_of_complete (hF : SpacelikeDevelopment F)
    (hc : CompleteSpace (PulledLength F)) : Function.Injective F :=
  Function.Injective.of_comp (bprop_project hF hc isFutureTimelike_vertical.2).injective

/-- `range F` meets every timelike line. -/
theorem SpacelikeDevelopment.exists_add_smul_mem_range (hF : SpacelikeDevelopment F)
    (hc : CompleteSpace (PulledLength F)) (p : Minkowski d) {v : Minkowski d} (hv : minkQ v < 0) :
    ∃ s : ℝ, p + s • v ∈ range F := by
  obtain ⟨x, hx⟩ := (bprop_project hF hc hv).surjective (projAlong v hv.ne p)
  obtain ⟨s, hs⟩ := (projAlong_eq_iff hv.ne).1 hx
  exact ⟨s, x, hs⟩

theorem SpacelikeDevelopment.eq_of_projAlong_eq (hF : SpacelikeDevelopment F)
    (hc : CompleteSpace (PulledLength F)) {v : Minkowski d} (hv : minkQ v < 0) {p q : Minkowski d}
    (hp : p ∈ range F) (hq : q ∈ range F) (h : projAlong v hv.ne p = projAlong v hv.ne q) :
    p = q := by
  obtain ⟨a, rfl⟩ := hp
  obtain ⟨b, rfl⟩ := hq
  exact congrArg F ((bprop_project hF hc hv).injective h)

/-- `range F` is achronal. -/
theorem SpacelikeDevelopment.isAchronal_range (hF : SpacelikeDevelopment F)
    (hc : CompleteSpace (PulledLength F)) : (minkowski d).IsAchronal (range F) := by
  refine isAchronal_iff_minkQ.2 fun p hp q hq => ?_
  by_contra hneg
  have hv : minkQ (q - p) < 0 := not_le.1 hneg
  have hpq := hF.eq_of_projAlong_eq hc hv hp hq
    ((projAlong_eq_iff hv.ne).2 ⟨-1, by rw [neg_one_smul]; abel⟩)
  rw [hpq, sub_self, minkQ_zero] at hv
  exact lt_irrefl _ hv

/-- `range F` is the graph of a `1`-Lipschitz map. -/
theorem SpacelikeDevelopment.exists_graph (hF : SpacelikeDevelopment F)
    (hc : CompleteSpace (PulledLength F)) :
    ∃ g : EuclideanSpace ℝ (Fin d) → ℝ, LipschitzWith 1 g ∧ range F = graph g := by
  refine exists_lipschitz_graph_of_isAchronal_of_exists (hF.isAchronal_range hc) fun x => ?_
  obtain ⟨s, hs⟩ := hF.exists_add_smul_mem_range hc ((0 : ℝ), x) isFutureTimelike_vertical.2
  exact ⟨s, by convert hs using 1; ext <;> simp⟩

/-- No two points of `range F` are null-separated. -/
theorem SpacelikeDevelopment.not_null_pair (hF : SpacelikeDevelopment F)
    (hc : CompleteSpace (PulledLength F)) {p q : Minkowski d} (hp : p ∈ range F)
    (hq : q ∈ range F) (hQ : minkQ (q - p) = 0) (h1 : 0 < (q - p).1) : False := by
  set ℓ := q - p with hℓ
  obtain ⟨g, hg, hgr⟩ := hF.exists_graph hc
  have hℓ0 : ℓ ≠ 0 := fun h => by rw [h] at h1; simp at h1
  have hℓ1 : ℓ.1 = ‖ℓ.2‖ := by
    rw [← abs_fst_eq_norm_of_minkQ_eq_zero hQ, abs_of_pos h1]
  have gp : p.1 = g p.2 := by rw [hgr] at hp; exact hp
  have gq : q.1 = g q.2 := by rw [hgr] at hq; exact hq
  have hseg : ∀ s ∈ Icc (0 : ℝ) 1, p + s • ℓ ∈ range F := by
    intro s hs
    rw [hgr]
    show (p + s • ℓ).1 = g (p + s • ℓ).2
    have hq2 : ℓ.2 = q.2 - p.2 := by simp [hℓ]
    have hxy : g q.2 - g p.2 = ‖q.2 - p.2‖ := by
      rw [← gp, ← gq, ← hq2, ← hℓ1]; simp [hℓ]
    simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    rw [hq2, lipschitzWith_one_segment hg hxy hs, ← hq2, ← hℓ1, gp]
  obtain ⟨a, rfl⟩ := hp
  obtain ⟨U, V, haU, -, hT⟩ := hF.locally a
  have hh := bprop_project hF hc isFutureTimelike_vertical.2
  set π := projAlong ((1, 0) : Minkowski d) isFutureTimelike_vertical.2.ne
  have hW : IsOpen (π ⁻¹' ((π ∘ F) '' U)) :=
    (hh.isOpenMap _ U.isOpen).preimage π.continuous
  have hpW : F a ∈ π ⁻¹' ((π ∘ F) '' U) := ⟨a, haU, rfl⟩
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), F a + s • ℓ ∈ F '' U := by
    filter_upwards [nhdsWithin_le_nhds (eventually_add_smul_mem hW hpW ℓ),
      Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with s hsW hs01
    obtain ⟨b, hb⟩ := hseg s ⟨hs01.1.le, hs01.2.le⟩
    obtain ⟨u, hu, hub⟩ := hsW
    have : u = b := hh.injective (by rw [hub]; simp [hb])
    exact ⟨b, this ▸ hu, hb⟩
  exact hT.not_eventually_add_smul_mem ⟨a, haU, rfl⟩ hℓ0 hQ hev

/-- **The immediate corollary of Prop 8.1** (l.2307–2309, and Cor 8.2's last clause, l.2269):
`range F` is an entire acausal graph — the graph of a strictly contracting map of `ℝᵈ`,
meeting every timelike line. -/
theorem isEntireAcausalGraph_range (hF : SpacelikeDevelopment F)
    (hc : CompleteSpace (PulledLength F)) : IsEntireAcausalGraph (range F) := by
  refine ⟨isAcausal_iff_minkQ.2 fun p hp q hq hpq => ?_,
    fun p v hv => hF.exists_add_smul_mem_range hc p hv.2⟩
  have h0 := isAchronal_iff_minkQ.1 (hF.isAchronal_range hc) p hp q hq
  rcases h0.lt_or_eq with h | h
  · exact h
  exfalso
  rcases lt_trichotomy (q - p).1 0 with h1 | h1 | h1
  · refine hF.not_null_pair hc hq hp ?_ ?_
    · rw [show p - q = -(q - p) by abel, minkQ_neg, h]
    · have : (p - q).1 = -(q - p).1 := by simp
      rw [this]; linarith
  · exact hpq (sub_eq_zero.1 (eq_zero_of_fst_eq_zero h1 h.symm.le)).symm
  · exact hF.not_null_pair hc hp hq h.symm h1

end Consequences

/-! #### Cor 8.3: lifting through the projection along a null direction -/

/-- **The local pieces of a spacelike Lipschitz hypersurface are uniformly spacelike**:
`κ ‖z₁ − z₂‖² ≤ minkQ (z₁ − z₂)` on a neighbourhood. -/
theorem IsSpacelikeLipschitzIn.exists_uniform_spacelike {V : Opens (Minkowski d)}
    {T : Set (Minkowski d)} (hT : IsSpacelikeLipschitzIn V T) {p : Minkowski d} (hp : p ∈ T) :
    ∃ O : Opens (Minkowski d), p ∈ O ∧ ∃ κ > (0 : ℝ),
      ∀ z₁ ∈ T ∩ (O : Set (Minkowski d)), ∀ z₂ ∈ T ∩ (O : Set (Minkowski d)),
        κ * ‖z₁ - z₂‖ ^ 2 ≤ minkQ (z₁ - z₂) := by
  obtain ⟨g, O, U, f, c, hc, hpO, -, -, hf, hgr⟩ := hT.locGraph p hp
  obtain ⟨K, hK⟩ := isom_lipschitzWith g⁻¹
  have hc1 : (c : ℝ) < 1 := by exact_mod_cast hc
  have hc0 : (0 : ℝ) ≤ c := c.2
  have hk : 0 < 1 - (c : ℝ) ^ 2 := by nlinarith
  refine ⟨O, hpO, (1 - (c : ℝ) ^ 2) / ((K : ℝ) ^ 2 + 1), div_pos hk (by positivity),
    fun z₁ h₁ z₂ h₂ => ?_⟩
  obtain ⟨hU₁, he₁⟩ := frame_mem_graphOver hgr h₁.1 h₁.2
  obtain ⟨hU₂, he₂⟩ := frame_mem_graphOver hgr h₂.1 h₂.2
  set u := g • z₁ - g • z₂ with hu
  have hL := hf.dist_le_mul _ hU₁ _ hU₂
  rw [Real.dist_eq, dist_eq_norm] at hL
  have hu1 : |u.1| ≤ c * ‖u.2‖ := by
    have e1 : u.1 = f (g • z₁).2 - f (g • z₂).2 := by
      rw [hu, Prod.fst_sub]; rw [he₁, he₂]; rfl
    have e2 : u.2 = (g • z₁).2 - (g • z₂).2 := by rw [hu, Prod.snd_sub]
    rw [e1, e2]; exact hL
  have hu2 : ‖u‖ ≤ ‖u.2‖ := norm_prod_le_iff.2 ⟨by
    rw [Real.norm_eq_abs]; exact hu1.trans (mul_le_of_le_one_left (norm_nonneg _) hc1.le),
    le_rfl⟩
  have hQ : (1 - (c : ℝ) ^ 2) * ‖u.2‖ ^ 2 ≤ minkQ u := by
    unfold minkQ
    have := sq_le_sq' (abs_le.1 hu1).1 (abs_le.1 hu1).2
    nlinarith
  have hz : ‖z₁ - z₂‖ ≤ K * ‖u‖ := by
    have := hK.dist_le_mul (g • z₁) (g • z₂)
    rwa [inv_smul_smul, inv_smul_smul, dist_eq_norm, dist_eq_norm] at this
  rw [← isom_minkQ_sub g z₂ z₁]
  change _ ≤ minkQ u
  have hz2 : ‖z₁ - z₂‖ ^ 2 ≤ (K : ℝ) ^ 2 * ‖u‖ ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hz 2; rwa [mul_pow] at this
  have hu3 : ‖u‖ ^ 2 ≤ ‖u.2‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hu2 2
  have s4 : 0 ≤ minkQ u := le_trans (by positivity) hQ
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  calc (1 - (c : ℝ) ^ 2) * ‖z₁ - z₂‖ ^ 2 ≤ (1 - (c : ℝ) ^ 2) * ((K : ℝ) ^ 2 * ‖u.2‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (hz2.trans (mul_le_mul_of_nonneg_left hu3 (sq_nonneg _)))
          hk.le
    _ = (K : ℝ) ^ 2 * ((1 - (c : ℝ) ^ 2) * ‖u.2‖ ^ 2) := by ring
    _ ≤ (K : ℝ) ^ 2 * minkQ u := mul_le_mul_of_nonneg_left hQ (sq_nonneg _)
    _ ≤ minkQ u * ((K : ℝ) ^ 2 + 1) := by nlinarith

section ChartProj

variable {X : Type*} [TopologicalSpace X] {F : X → Minkowski d} {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The local charts of `P ∘ F`** for a linear projection `P` along a causal direction `Δ ≠ 0`
(kernel `ℝ Δ`, with a linear section `ι`): near each point `P ∘ F` is an open embedding, on a
source where `F` is uniformly spacelike. -/
theorem SpacelikeDevelopment.exists_chart_of_proj (hF : SpacelikeDevelopment F)
    (P : Minkowski d →L[ℝ] E) {Δ : Minkowski d} (hΔ : minkQ Δ ≤ 0) (hΔ0 : Δ ≠ 0)
    (hPΔ : P Δ = 0) (hker : ∀ w, P w = 0 → ∃ s : ℝ, w = s • Δ) (ι : E →L[ℝ] Minkowski d)
    (hι : ∀ y, P (ι y) = y) (x : X) :
    ∃ e : OpenPartialHomeomorph X E, x ∈ e.source ∧ ⇑e = P ∘ F ∧ ∃ κ > (0 : ℝ),
      ∀ a ∈ e.source, ∀ b ∈ e.source, κ * ‖F a - F b‖ ^ 2 ≤ minkQ (F a - F b) := by
  haveI : Nonempty X := ⟨x⟩
  obtain ⟨U, V, hxU, hemb, hT⟩ := hF.locally x
  obtain ⟨O, hxO, κ, hκ, hO⟩ := hT.exists_uniform_spacelike ⟨x, hxU, rfl⟩
  set W : Set X := (U : Set X) ∩ F ⁻¹' O with hWdef
  have hWo : IsOpen W := U.isOpen.inter (O.isOpen.preimage hF.continuous)
  have hxW : x ∈ W := ⟨hxU, hxO⟩
  have hWnn : ∀ a ∈ W, ∀ b ∈ W, κ * ‖F a - F b‖ ^ 2 ≤ minkQ (F a - F b) := fun a ha b hb =>
    hO (F a) ⟨⟨a, ha.1, rfl⟩, ha.2⟩ (F b) ⟨⟨b, hb.1, rfl⟩, hb.2⟩
  have hFinj : InjOn F U := fun a ha b hb hab => by
    have := hemb.injective (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) hab
    exact congrArg Subtype.val this
  have hinj : InjOn (P ∘ F) W := by
    intro a ha b hb hab
    obtain ⟨s, hs⟩ := hker (F a - F b) (by rw [map_sub]; exact sub_eq_zero.2 hab)
    have hnn := hWnn a ha b hb
    rw [hs, minkQ_smul] at hnn
    have h1 : s ^ 2 * minkQ Δ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hΔ
    have h2 : ‖s • Δ‖ ^ 2 = 0 := by
      have := mul_nonneg hκ.le (sq_nonneg ‖s • Δ‖)
      nlinarith
    have : s • Δ = 0 := by
      rw [sq_eq_zero_iff, norm_eq_zero] at h2; exact h2
    rw [this, sub_eq_zero] at hs
    exact hFinj ha.1 hb.1 hs
  have hopen : ∀ B ⊆ W, IsOpen B → IsOpen ((P ∘ F) '' B) := by
    intro B hBW hBo
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨b, hb, rfl⟩
    have hbU : b ∈ U := (hBW hb).1
    obtain ⟨O'', hO''o, hO''⟩ := hemb.isInducing.isOpen_iff.1
      (hBo.preimage continuous_subtype_val)
    have key : ∀ z, ∀ hz : z ∈ U, F z ∈ O'' ↔ z ∈ B := fun z hz => by
      have := congrArg (fun s : Set U => (⟨z, hz⟩ : U) ∈ s) hO''
      simpa using this
    have hev := hT.eventually_exists_add_smul_mem ⟨b, hbU, rfl⟩ hO''o ((key b hbU).2 hb) hΔ hΔ0
    set j : E → Minkowski d := fun y => ι (y - P (F b)) + F b
    have hjc : Continuous j := (ι.continuous.comp (continuous_id.sub continuous_const)).add
      continuous_const
    have hjb : j (P (F b)) = F b := by simp [j]
    have hten : Tendsto j (𝓝 ((P ∘ F) b)) (𝓝 (F b)) := by
      have := hjc.tendsto (P (F b)); rwa [hjb] at this
    filter_upwards [hten hev] with y hy
    obtain ⟨s, ⟨z, hzU, hz⟩, hzO⟩ := hy
    refine ⟨z, (key z hzU).1 (by rw [hz]; exact hzO), ?_⟩
    simp only [Function.comp_apply]
    rw [hz]
    simp only [j, map_add, map_smul, hPΔ, smul_zero, add_zero, hι]
    abel
  have hc : ContinuousOn (P ∘ F) W := (P.continuous.comp hF.continuous).continuousOn
  have ho : IsOpenMap (W.restrict (P ∘ F)) := by
    intro A hA
    rw [show W.restrict (P ∘ F) '' A = (P ∘ F) '' (Subtype.val '' A) by
      rw [← image_comp]; rfl]
    exact hopen _ (Subtype.coe_image_subset _ _) (hWo.isOpenMap_subtype_val A hA)
  exact ⟨OpenPartialHomeomorph.ofContinuousOpenRestrict (hinj.toPartialEquiv (P ∘ F) W) hc ho
    hWo, hxW, rfl, κ, hκ, hWnn⟩

end ChartProj

/-- The projection `w ↦ w.2 − w.1 e` of `𝐌ⁿ` onto `ℝᵈ` along the null direction `(1, e)`. -/
noncomputable def nullProj (e : EuclideanSpace ℝ (Fin d)) :
    Minkowski d →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin d)) -
    (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin d))).smulRight e

theorem nullProj_apply (e : EuclideanSpace ℝ (Fin d)) (w : Minkowski d) :
    nullProj e w = w.2 - w.1 • e := rfl

/-- For a unit `e`, `minkQ w = ‖Ψ w‖² + 2 w₁ ⟨Ψ w, e⟩` with `Ψ = nullProj e`. -/
theorem minkQ_eq_nullProj {e : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) (w : Minkowski d) :
    minkQ w = ‖nullProj e w‖ ^ 2 + 2 * w.1 * inner ℝ (nullProj e w) e := by
  rw [nullProj_apply]
  unfold minkQ
  rw [norm_sub_sq_real, inner_sub_left, norm_smul, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, he, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- For a unit `e`, `minkB w (1, e) = ⟨Ψ w, e⟩`. -/
theorem minkB_nullProj {e : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) (w : Minkowski d) :
    minkB w ((1 : ℝ), e) = inner ℝ (nullProj e w) e := by
  rw [nullProj_apply, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, he]
  unfold minkB; ring

theorem minkB_sub_left' (a b c : Minkowski d) : minkB (a - b) c = minkB a c - minkB b c := by
  unfold minkB; simp only [Prod.fst_sub, Prod.snd_sub, inner_sub_left]; ring

theorem minkB_smul_right' (a c : Minkowski d) (s : ℝ) : minkB a (s • c) = s * minkB a c := by
  unfold minkB; simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, real_inner_smul_right]
  ring

/-- **Cor 8.3** (`GHFspace.tex` l.2277–2290, W6): a lightlike hyperplane `P₀` meeting `range F`
has all its `Δ₀`-lines meeting `range F`. "Completely similar" to 8.1, made literal: normalise
`Δ₀ = ℓ.1 (1, e)`, `‖e‖ = 1`, project along `(1, e)` onto `ℝᵈ` (`nullProj e`, a local
homeomorphism on `F`: `exists_chart_of_proj`), and lift the segment from `Ψ (F x₀)` to `Ψ r`
inside the level `⟨·, e⟩ = const` of `P₀`, where `minkQ` of the developed velocity is exactly
the squared Euclidean speed (`minkQ_eq_nullProj`) — Barbot's "the projection onto `P₀/Δ₀` is an
isometry on `S ∩ P₀`". Neither 8.1 nor `ConnectedSpace X` is used. -/
theorem bcor_quoiso {X : Type*} [TopologicalSpace X] [ConnectedSpace X] [T2Space X]
    {F : X → Minkowski d} (hF : SpacelikeDevelopment F) (hc : CompleteSpace (PulledLength F)) :
    NullSaturated (range F) := by
  rintro p ℓ hℓ0 hℓ ⟨_, ⟨x₀, rfl⟩, hq⟩ r hr
  have h1 : ℓ.1 ≠ 0 := fun h => hℓ0 (eq_zero_of_fst_eq_zero h hℓ.le)
  set e : EuclideanSpace ℝ (Fin d) := ℓ.1⁻¹ • ℓ.2 with hedef
  have he : ‖e‖ = 1 := by
    rw [hedef, norm_smul, norm_inv, Real.norm_eq_abs, ← abs_fst_eq_norm_of_minkQ_eq_zero hℓ,
      inv_mul_cancel₀ (abs_ne_zero.2 h1)]
  set ℓ' : Minkowski d := ((1 : ℝ), e) with hℓ'
  have hℓℓ' : ℓ' = ℓ.1⁻¹ • ℓ := by
    rw [hℓ']; ext
    · simp [inv_mul_cancel₀ h1]
    · simp [hedef]
  set Ψ := nullProj e with hΨ
  have hΨℓ : Ψ ℓ' = 0 := by simp [hΨ, nullProj_apply, hℓ']
  have hker : ∀ w, Ψ w = 0 → ∃ s : ℝ, w = s • ℓ' := fun w hw => by
    refine ⟨w.1, ?_⟩
    rw [hΨ, nullProj_apply, sub_eq_zero] at hw
    ext
    · simp [hℓ']
    · simp [hℓ', hw]
  set ι : EuclideanSpace ℝ (Fin d) →L[ℝ] Minkowski d :=
    ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin d))
  have hι : ∀ y, Ψ (ι y) = y := fun y => by simp [hΨ, nullProj_apply, ι]
  have hℓ'Q : minkQ ℓ' ≤ 0 := by
    rw [hℓ', show minkQ ((1 : ℝ), e) = -1 ^ 2 + ‖e‖ ^ 2 from rfl, he]; norm_num
  have hℓ'0 : ℓ' ≠ 0 := fun h => by
    have := congrArg Prod.fst h; simp [hℓ'] at this
  have hq' : IsLocalHomeomorph (Ψ ∘ F) := fun x => by
    obtain ⟨e', hxe, he', -⟩ := hF.exists_chart_of_proj Ψ hℓ'Q hℓ'0 hΨℓ hker ι hι x
    exact ⟨e', hxe, he'.symm⟩
  have hloc : ∀ x : X, ∃ W ∈ 𝓝 x, ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ W, ∀ b ∈ W,
      ‖F a - F b‖ ≤ C * ‖Ψ (F a) - Ψ (F b)‖ := fun x => by
    obtain ⟨e', hxe, -, κ, hκ, hnn⟩ := hF.exists_chart_of_proj Ψ hℓ'Q hℓ'0 hΨℓ hker ι hι x
    refine ⟨e'.source, e'.open_source.mem_nhds hxe, 1 + 3 / κ, by positivity,
      fun a ha b hb => ?_⟩
    rw [← map_sub]
    set w := F a - F b
    have hQ := minkQ_eq_nullProj he w
    have hb1 : |w.1| ≤ ‖w‖ := by rw [← Real.norm_eq_abs]; exact norm_fst_le w
    have hb2 : |inner ℝ (Ψ w) e| ≤ ‖Ψ w‖ := by
      have := abs_real_inner_le_norm (Ψ w) e; rwa [he, mul_one] at this
    have hcross : 2 * w.1 * inner ℝ (Ψ w) e ≤ 2 * ‖w‖ * ‖Ψ w‖ := by
      have := abs_mul w.1 (inner ℝ (Ψ w) e)
      have h3 : w.1 * inner ℝ (Ψ w) e ≤ ‖w‖ * ‖Ψ w‖ :=
        (le_abs_self _).trans (this ▸ mul_le_mul hb1 hb2 (abs_nonneg _) (norm_nonneg _))
      linarith
    have hmain : κ * ‖w‖ ^ 2 ≤ ‖Ψ w‖ ^ 2 + 2 * ‖w‖ * ‖Ψ w‖ := by
      have := hnn a ha b hb; rw [hQ] at this; linarith
    rcases le_or_gt ‖w‖ ‖Ψ w‖ with h | h
    · have : 0 ≤ 3 / κ * ‖Ψ w‖ := by positivity
      nlinarith
    · have hpos : 0 < ‖w‖ := lt_of_le_of_lt (norm_nonneg _) h
      have h3 : ‖Ψ w‖ ^ 2 ≤ ‖w‖ * ‖Ψ w‖ := by nlinarith [norm_nonneg (Ψ w)]
      have h5 : κ * ‖w‖ * ‖w‖ ≤ 3 * ‖Ψ w‖ * ‖w‖ := by nlinarith
      have h6 : κ * ‖w‖ ≤ 3 * ‖Ψ w‖ := le_of_mul_le_mul_right h5 hpos
      have h4 : ‖w‖ ≤ 3 / κ * ‖Ψ w‖ := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hκ]; linarith
      have : (1 + 3 / κ) * ‖Ψ w‖ = ‖Ψ w‖ + 3 / κ * ‖Ψ w‖ := by ring
      linarith [norm_nonneg (Ψ w)]
  set v := Ψ r - Ψ (F x₀) with hv
  have hve : inner ℝ v e = 0 := by
    rw [hv, ← map_sub, ← minkB_nullProj he, show ((1 : ℝ), e) = ℓ' from rfl, hℓℓ',
      minkB_smul_right', show r - F x₀ = (r - p) - (F x₀ - p) by abel, minkB_sub_left', hr, hq,
      sub_zero, mul_zero]
  obtain ⟨l, -, -, hlq⟩ := hF.exists_lift_of_proj hc Ψ hq' hloc x₀ (v := v) (M := ‖v‖ ^ 2)
    fun w c hw => by
      rw [minkQ_eq_nullProj he w, hw, inner_smul_left, hve, mul_zero, mul_zero, add_zero,
        norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have h1' := hlq 1 ⟨zero_le_one, le_rfl⟩
  simp only [Function.comp_apply, one_smul, hv, add_sub_cancel] at h1'
  obtain ⟨s, hs⟩ := hker (F (l 1) - r) (by rw [map_sub, h1', sub_self])
  refine ⟨s * ℓ.1⁻¹, l 1, ?_⟩
  rw [mul_smul, ← hℓℓ', ← hs]; abel

/-! ### E. The bridge -/

/-- **Restriction to a smaller open** (a step of B2): a spacelike Lipschitz hypersurface of `V`,
cut by an open `V' ≤ V`, is one of `V'` — achronality in `V'` follows from achronality in `V`
(`lt_mono`: fewer curves), and the frame pictures are cut by `V'`. -/
theorem IsSpacelikeLipschitzIn.restrict {V V' : Opens (Minkowski d)} {T : Set (Minkowski d)}
    (h : IsSpacelikeLipschitzIn V T) (hV : V' ≤ V) :
    IsSpacelikeLipschitzIn V' (T ∩ (V' : Set (Minkowski d))) := by
  refine ⟨inter_subset_right, fun p hp q hq hpq =>
    h.achronal p hp.1 q hq.1 ((minkowski d).lt_mono hV hpq), fun p hp => ?_⟩
  obtain ⟨g, O, U, f, c, hc, hpO, -, hU, hf, hgr⟩ := h.locGraph p hp.1
  refine ⟨g, O ⊓ V', U, f, c, hc, ⟨hpO, hp.2⟩, inf_le_right, hU, hf, ?_⟩
  rw [Opens.coe_inf, show T ∩ (V' : Set (Minkowski d)) ∩ ((O : Set (Minkowski d)) ∩ V') =
      (T ∩ O) ∩ V' by ext; simp only [mem_inter_iff]; tauto, smul_set_inter, hgr,
    smul_set_inter]
  ext; simp only [mem_inter_iff]; tauto

/-- A covering space of a Hausdorff space is Hausdorff. -/
theorem t2Space_of_isCoveringMap {E Y : Type*} [TopologicalSpace E] [TopologicalSpace Y]
    [T2Space Y] {p : E → Y} (hp : IsCoveringMap p) : T2Space E :=
  ⟨fun x₁ x₂ hne => by
    by_cases h : p x₁ = p x₂
    · exact hp.isSeparatedMap x₁ x₂ h hne
    · obtain ⟨u, v, hu, hv, hxu, hxv, huv⟩ := t2_separation h
      exact ⟨p ⁻¹' u, p ⁻¹' v, hu.preimage hp.continuous, hv.preimage hp.continuous, hxu, hxv,
        huv.preimage p⟩⟩

/-- **A slice of a product splitting lifts to a connected set** (the topological half of B1): if
`ψ : S × ℝ ≃ₜ Y` with `ψ (x, 0) = x`, then `p⁻¹(S)` is connected in the universal cover. The
homotopy `H (y, u) = ψ (r y, (1 − u) t(y))` retracts `Y` onto `S` rel `S`; a path `α⁻¹ · β` between
two points of `S` is homotopic rel endpoints to its retraction, a path in `S`, whose lift from
`⟨a, [α]⟩` (`UniversalCover.liftFrom`) ends at `⟨b, [β]⟩` and stays over `S`. -/
theorem connectedSpace_preimage_of_splitting {Y : Type*} [TopologicalSpace Y]
    [PathConnectedSpace Y] {S : Set Y} (ψ : S × ℝ ≃ₜ Y) (hψ : ∀ x : S, ψ (x, 0) = x) (y₀ : Y) :
    ConnectedSpace (UniversalCover.proj Y y₀ ⁻¹' S) := by
  let r : Y → S := fun y => (ψ.symm y).1
  have hsymm : ∀ x : S, ψ.symm x = (x, 0) := fun x => by
    rw [← hψ x, Homeomorph.symm_apply_apply]
  have hr : ∀ x : S, r x = x := fun x => by simp only [r, hsymm]
  let H : Y → ℝ → Y := fun y u => ψ ((ψ.symm y).1, (1 - u) * (ψ.symm y).2)
  have H0 : ∀ y, H y 0 = y := fun y => by simp [H]
  have H1 : ∀ y, H y 1 = r y := fun y => by simp [H, r, hψ]
  have HS : ∀ x : S, ∀ u, H x u = x := fun x u => by simp [H, hsymm, hψ]
  have Hc : Continuous fun q : ℝ × Y => H q.2 q.1 := by
    refine ψ.continuous.comp (Continuous.prodMk ?_ ?_)
    · exact continuous_fst.comp (ψ.symm.continuous.comp continuous_snd)
    · exact (continuous_const.sub continuous_fst).mul
        (continuous_snd.comp (ψ.symm.continuous.comp continuous_snd))
  -- two points of `p⁻¹(S)` are joined inside it
  have hj : ∀ a b : UniversalCover Y y₀, a.pt ∈ S → b.pt ∈ S →
      JoinedIn (UniversalCover.proj Y y₀ ⁻¹' S) a b := by
    rintro ⟨ya, ca⟩ ⟨yb, cb⟩ ha hb
    obtain ⟨α, rfl⟩ := Quotient.exists_rep ca
    obtain ⟨β, rfl⟩ := Quotient.exists_rep cb
    let δ : Path ya yb := α.symm.trans β
    let δ' : Path ya yb :=
      { toFun := fun t => (r (δ t) : Y)
        continuous_toFun := continuous_subtype_val.comp
          (continuous_fst.comp (ψ.symm.continuous.comp δ.continuous))
        source' := by
          show ((r (δ 0)) : Y) = ya
          rw [δ.source]; exact congrArg Subtype.val (hr ⟨ya, ha⟩)
        target' := by
          show ((r (δ 1)) : Y) = yb
          rw [δ.target]; exact congrArg Subtype.val (hr ⟨yb, hb⟩) }
    have hδ : Path.Homotopic δ δ' := by
      refine ⟨{ toFun := fun q => H (δ q.2) q.1
                continuous_toFun := Hc.comp ((continuous_subtype_val.comp continuous_fst).prodMk
                  (δ.continuous.comp continuous_snd))
                map_zero_left := fun t => H0 _
                map_one_left := fun t => H1 _
                prop' := ?_ }⟩
      intro u t ht
      rcases ht with rfl | rfl
      · show H (δ 0) u = δ 0
        rw [δ.source]; exact HS ⟨ya, ha⟩ u
      · show H (δ 1) u = δ 1
        rw [δ.target]; exact HS ⟨yb, hb⟩ u
    have hcls : (Path.Homotopic.Quotient.mk α).trans (Path.Homotopic.Quotient.mk δ') =
        Path.Homotopic.Quotient.mk β := by
      rw [← Path.Homotopic.Quotient.eq.2 hδ]
      show (Path.Homotopic.Quotient.mk α).trans
        (Path.Homotopic.Quotient.mk (α.symm.trans β)) = _
      rw [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
        ← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.trans_symm,
        Path.Homotopic.Quotient.refl_trans]
    have e : (⟨yb, (Path.Homotopic.Quotient.mk α).trans (Path.Homotopic.Quotient.mk δ')⟩ :
        UniversalCover Y y₀) = ⟨yb, Path.Homotopic.Quotient.mk β⟩ := by rw [hcls]
    refine ⟨(UniversalCover.liftFrom (Path.Homotopic.Quotient.mk α) δ').cast rfl e.symm,
      fun t => ?_⟩
    show (UniversalCover.liftFrom _ δ' t).pt ∈ S
    rw [UniversalCover.proj_liftFrom]; exact (r (δ t)).2
  have hne : Nonempty S := ⟨(ψ.symm (Classical.arbitrary Y)).1⟩
  obtain ⟨x⟩ := hne
  let a : UniversalCover Y y₀ :=
    ⟨x, Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath y₀ x)⟩
  have hpc : IsPathConnected (UniversalCover.proj Y y₀ ⁻¹' S) :=
    ⟨a, x.2, fun {b} hb => hj a b x.2 hb⟩
  exact isConnected_iff_connectedSpace.1 hpc.isConnected

/-! ### The inputs of B1: causal arc-connectedness, `CurvesExtend` from a flow, acausality

`exists_splitting_of_hasChronalCausalFlow` asks a chronal causal flow and `IsAcausal S`. The flow
is `Flat.flat_hasChronalCausalFlow` (`Splitting.lean`, proved, under `[SecondCountableTopology M]`);
acausality is `IsCauchySurface.isAcausal` (`Causal/CauchyExtension.lean:110`), whose two named
hypotheses are discharged here for a flat spacetime carrying a causal flow:
`flatCausality_causallyArcConnected` (charts + absolute minimality) and
`curvesExtend_of_isCausalFlow` (prolong a causal segment by two orbits). -/

section BridgeInputs

variable {X : Type*} [TopologicalSpace X]

/-- A causal curve over `ℝ` with no limit at either end is inextensible. -/
theorem inextensible_univ_of_not_tendsto {C : Causality X} {γ : ℝ → X}
    (hc : C.CausalCurveIn ⊤ univ γ) (hbot : ∀ p, ¬ Tendsto γ atBot (𝓝 p))
    (htop : ∀ p, ¬ Tendsto γ atTop (𝓝 p)) : C.Inextensible ⊤ univ γ := by
  refine ⟨hc, ?_⟩
  rintro ⟨I', c', hcurve, ⟨ψ, hψ, hψmaps, hψoc, hψeq⟩, ⟨t', ht', hgrow⟩⟩
  have hmono : Monotone ψ := (strictMonoOn_univ.1 hψ).monotone
  by_cases h1 : ∃ s, t' ≤ ψ s
  · by_cases h2 : ∃ s, ψ s ≤ t'
    · obtain ⟨s₁, hs₁⟩ := h1
      obtain ⟨s₂, hs₂⟩ := h2
      obtain ⟨s, -, hs⟩ := hψoc.out (mem_image_of_mem ψ (mem_univ s₂))
        (mem_image_of_mem ψ (mem_univ s₁)) ⟨hs₂, hs₁⟩
      exact hgrow s trivial (by rw [← hs, hψeq s trivial])
    · simp only [not_exists, not_le] at h2
      have hbdd : BddBelow (range ψ) := ⟨t', by rintro _ ⟨s, rfl⟩; exact (h2 s).le⟩
      set sψ := ⨅ s, ψ s
      have hlimψ : Tendsto ψ atBot (𝓝 sψ) := tendsto_atBot_ciInf hmono hbdd
      have hlimψt : t' ≤ sψ := le_ciInf fun s => (h2 s).le
      have hlimψ0 : sψ ≤ ψ 0 := ciInf_le hbdd 0
      have hcont := (hcurve.curve t' ht' (ψ 0) (hψmaps (mem_univ 0))).continuousOn
        C.isRelFamily_le
      have hlimψmem : sψ ∈ Icc t' (ψ 0) := ⟨hlimψt, hlimψ0⟩
      have hev : ∀ᶠ s in atBot, ψ s ∈ Icc t' (ψ 0) :=
        eventually_atBot.2 ⟨0, fun s hs => ⟨(h2 s).le, hmono hs⟩⟩
      refine hbot (c' sψ) ?_
      have := (hcont sψ hlimψmem).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlimψ, hev⟩)
      exact this.congr fun s => by simp only [Function.comp, hψeq s trivial]
  · simp only [not_exists, not_le] at h1
    have hbdd : BddAbove (range ψ) := ⟨t', by rintro _ ⟨s, rfl⟩; exact (h1 s).le⟩
    set sψ := ⨆ s, ψ s
    have hlimψ : Tendsto ψ atTop (𝓝 sψ) := tendsto_atTop_ciSup hmono hbdd
    have hlimψt : sψ ≤ t' := ciSup_le fun s => (h1 s).le
    have hlimψ0 : ψ 0 ≤ sψ := le_ciSup hbdd 0
    have hcont := (hcurve.curve (ψ 0) (hψmaps (mem_univ 0)) t' ht').continuousOn
      C.isRelFamily_le
    have hlimψmem : sψ ∈ Icc (ψ 0) t' := ⟨hlimψ0, hlimψt⟩
    have hev : ∀ᶠ s in atTop, ψ s ∈ Icc (ψ 0) t' :=
      eventually_atTop.2 ⟨0, fun s hs => ⟨hmono hs, (h1 s).le⟩⟩
    refine htop (c' sψ) ?_
    have := (hcont sψ hlimψmem).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlimψ, hev⟩)
    exact this.congr fun s => by simp only [Function.comp, hψeq s trivial]

/-- A curve eventually equal to an orbit of a causal flow has no limit (a limit of an orbit is a
fixed point, `Causality.flow_fixed_of_tendsto`, and a causal flow has none). -/
theorem not_tendsto_of_eventuallyEq_flow [T2Space X] {C : Causality X} {φ : Flow ℝ X}
    (hφ : C.IsCausalFlow φ) {γ : ℝ → X} {y : X} {l : Filter ℝ} [l.NeBot]
    (hl : ∀ τ : ℝ, Tendsto (fun s => τ + s) l l) (heq : γ =ᶠ[l] fun t => φ t y) (p : X) :
    ¬ Tendsto γ l (𝓝 p) := fun h => by
  obtain ⟨t, ht⟩ := hφ.nonstationary p
  exact ht (Causality.flow_fixed_of_tendsto hl (h.congr' heq) t)

/-- **`CurvesExtend` from a causal flow** (`M` Hausdorff): a causal curve `c` over `[a, b]` is
prolonged by the past orbit of `c a` and the future orbit of `c b`; the result is a causal curve
over `ℝ` (two concatenations, `CurveOn.concat`) whose ends are orbits, hence have no limit, hence
it is inextensible (`inextensible_univ_of_not_tendsto`). -/
theorem curvesExtend_of_isCausalFlow [T2Space X] {C : Causality X} {φ : Flow ℝ X}
    (hφ : C.IsCausalFlow φ) : C.CurvesExtend := by
  intro c a b hab hc
  set y₁ := φ (-a) (c a)
  set y₂ := φ (-b) (c b)
  have hy₁ : φ a y₁ = c a := by
    rw [← Flow.map_add, add_neg_cancel, Flow.map_zero_apply]
  have hy₂ : φ b y₂ = c b := by
    rw [← Flow.map_add, add_neg_cancel, Flow.map_zero_apply]
  let g : ℝ → X := fun t => if t ≤ a then φ t y₁ else c t
  let γ : ℝ → X := fun t => if t ≤ b then g t else φ t y₂
  have horb : ∀ y : X, ∀ s t : ℝ, C.CausalCurveOn ⊤ (fun t => φ t y) s t := fun y s t =>
    (hφ.inextensible y).1.curve s trivial t trivial
  have hgb : g b = φ b y₂ := by
    rw [hy₂]
    by_cases h : b ≤ a
    · have hba : b = a := le_antisymm h hab
      simp only [g, h, if_true]; rw [hba, hy₁]
    · simp only [g, h, if_false]
  have hcurve : ∀ A B : ℝ, A ≤ a → b ≤ B → C.CausalCurveOn ⊤ γ A B := fun A B hA hB => by
    have h1 : C.CausalCurveOn ⊤ g A b :=
      CurveOn.concat C.isRelFamily_le (horb y₁ A a) hc hA hab hy₁
    exact CurveOn.concat C.isRelFamily_le h1 (horb y₂ b B) (hA.trans hab) hB hgb
  have hγ : C.CausalCurveIn ⊤ univ γ := by
    refine ⟨⟨0, trivial⟩, ordConnected_univ, fun s _ t _ => ?_⟩
    rcases lt_or_ge t s with hts | hst
    · exact CurveOn.of_lt hts
    · exact (hcurve (min s a) (max t b) (min_le_right _ _) (le_max_right _ _)).restrict
        (min_le_left _ _) (le_max_left _ _) le_rfl fun _ _ => trivial
  have hbot : γ =ᶠ[atBot] fun t => φ t y₁ :=
    eventually_atBot.2 ⟨a, fun t ht => by simp only [γ, g, ht, ht.trans hab, if_true]⟩
  have htop : γ =ᶠ[atTop] fun t => φ t y₂ :=
    eventually_atTop.2 ⟨b + 1, fun t ht => by
      have : ¬ t ≤ b := by linarith
      simp only [γ, this, if_false]⟩
  refine ⟨univ, γ, inextensible_univ_of_not_tendsto hγ
    (not_tendsto_of_eventuallyEq_flow hφ (fun τ => tendsto_atBot_add_const_left _ τ tendsto_id)
      hbot)
    (not_tendsto_of_eventuallyEq_flow hφ (fun τ => tendsto_atTop_add_const_left _ τ tendsto_id)
      htop), ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  refine ⟨t, trivial, ?_⟩
  by_cases h : t ≤ a
  · have hta : t = a := le_antisymm h ht.1
    simp only [γ, g, ht.2, h, if_true]; rw [hta, hy₁]
  · simp only [γ, g, ht.2, h, if_true, if_false]

/-- The inverse of a chart isomorphism carries curves of the image of `U` to curves of `U`, for
any pair of relation families that the chart matches on the open subsets of its source. -/
theorem curveOn_chart_symm {Y : Type*} [TopologicalSpace Y] {e : OpenPartialHomeomorph X Y}
    {rC : Opens X → X → X → Prop} {rD : Opens Y → Y → Y → Prop} (hrD : IsRelFamily rD)
    {U : Opens X} (hU : U ≤ chartSource e)
    (hiso : ∀ N : Opens X, N ≤ chartSource e → ∀ x ∈ N, ∀ y ∈ N,
      (rC N x y ↔ rD (chartImage e N) (e x) (e y)))
    {c : ℝ → Y} {a b : ℝ} (hc : CurveOn rD (chartImage e U) c a b) :
    CurveOn rC U (fun t => e.symm (c t)) a b where
  mem t ht := by
    obtain ⟨z, -, hzU, -, hz⟩ := exists_of_mem_chartImage (hc.mem t ht)
    show e.symm (c t) ∈ U
    rw [hz]; exact hzU
  rel t ht N hN htN := by
    obtain ⟨z, hzs, -, hze, hz⟩ := exists_of_mem_chartImage (hc.mem t ht)
    have hzN : z ∈ N := by rw [← hz]; exact htN
    have hcN : c t ∈ chartImage e N := ⟨z, ⟨hzs, hzN⟩, hze⟩
    obtain ⟨l, u, hl, hu, hrel⟩ := hc.rel t ht (chartImage e N) (chartImage_mono hN) hcN
    refine ⟨l, u, hl, hu, fun s hs s' hs' h1 h2 h3 => ?_⟩
    have hr := hrel s hs s' hs' h1 h2 h3
    obtain ⟨w, -, hwN, hwe, hw⟩ := exists_of_mem_chartImage (hrD.mem_left hr)
    obtain ⟨w', -, hwN', hwe', hw'⟩ := exists_of_mem_chartImage (hrD.mem_right hr)
    show rC N (e.symm (c s)) (e.symm (c s'))
    rw [hw, hw']
    refine (hiso N (hN.trans hU) w hwN w' hwN').2 ?_
    rw [hwe, hwe']; exact hr

/-- **A chart isomorphism onto a causally arc-connected model makes every open subset of its
source causally arc-connected**: a relation of `U` is one of the image, realised there by a curve
(`hD`), carried back by `e.symm` (`curveOn_chart_symm`). -/
theorem causallyArcConnectedOn_of_chartIso {Y : Type*} [TopologicalSpace Y] {C : Causality X}
    {D : Causality Y} {e : OpenPartialHomeomorph X Y} (h : ChartIso C D e)
    (hD : D.CausallyArcConnected) {V : Opens X} (hV : V ≤ chartSource e) :
    C.CausallyArcConnectedOn V := by
  intro U hU p q
  have hUe : U ≤ chartSource e := hU.trans hV
  refine ⟨⟨fun hpq => ?_, ?_⟩, ⟨fun hpq => ?_, ?_⟩⟩
  · have hp := C.le_mem_left hpq
    have hq := C.le_mem_right hpq
    obtain ⟨c, hc, h0, h1⟩ :=
      (hD (chartImage e U) le_top (e p) (e q)).1.1 ((h U hUe p hp q hq).1.1 hpq)
    refine ⟨fun t => e.symm (c t), curveOn_chart_symm D.isRelFamily_le hUe
      (fun N hN x hx y hy => (h N hN x hx y hy).1) hc, ?_, ?_⟩
    · show e.symm (c 0) = p
      rw [h0]; exact e.left_inv (hUe hp)
    · show e.symm (c 1) = q
      rw [h1]; exact e.left_inv (hUe hq)
  · rintro ⟨c, hc, rfl, rfl⟩
    exact hc.le_of_le le_rfl zero_le_one le_rfl
  · have hp := C.lt_mem_left hpq
    have hq := C.lt_mem_right hpq
    obtain ⟨c, hc, h0, h1⟩ :=
      (hD (chartImage e U) le_top (e p) (e q)).2.1 ((h U hUe p hp q hq).2.1 hpq)
    refine ⟨fun t => e.symm (c t), curveOn_chart_symm D.isRelFamily_lt hUe
      (fun N hN x hx y hy => (h N hN x hx y hy).2) hc, ?_, ?_⟩
    · show e.symm (c 0) = p
      rw [h0]; exact e.left_inv (hUe hp)
    · show e.symm (c 1) = q
      rw [h1]; exact e.left_inv (hUe hq)
  · rintro ⟨c, hc, rfl, rfl⟩
    exact hc.lt_of_lt le_rfl zero_lt_one le_rfl

variable [ChartedSpace (Minkowski d) X] [HasGroupoid X (gxGroupoid (isom d) (Minkowski d))]

variable (d X) in
/-- **A flat spacetime is causally arc-connected**: locally through the charts
(`causallyArcConnectedOn_of_chartIso`, `minkowski_causallyArcConnected`), then globally because
`flatCausality` is absolutely minimal (`LocallyCausallyArcConnected.causallyArcConnected`). -/
theorem flatCausality_causallyArcConnected : (flatCausality d X).CausallyArcConnected := by
  refine Causality.LocallyCausallyArcConnected.causallyArcConnected (fun x N hN => ?_)
    flatCausality_absolutelyMinimal
  refine ⟨⟨interior N ∩ (chartAt (Minkowski d) x).source,
      isOpen_interior.inter (chartAt (Minkowski d) x).open_source⟩,
    ⟨mem_interior_iff_mem_nhds.2 hN, mem_chart_source _ x⟩, fun y hy => interior_subset hy.1, ?_⟩
  exact causallyArcConnectedOn_of_chartIso (flatCausality_chartIso_chartAt x)
    minkowski_causallyArcConnected fun y hy => hy.2

/-- **A Cauchy surface of a flat spacetime with a causal flow is acausal**:
`IsCauchySurface.isAcausal` with `flatCausality_causallyArcConnected` and
`curvesExtend_of_isCausalFlow`. -/
theorem isAcausal_of_isCauchySurface_of_hasChronalCausalFlow [T2Space X]
    (hflow : (flatCausality d X).HasChronalCausalFlow) {S : Set X}
    (hS : (flatCausality d X).IsCauchySurface S) : (flatCausality d X).IsAcausal S := by
  obtain ⟨φ, hφ, -⟩ := hflow
  exact hS.isAcausal (flatCausality_causallyArcConnected d X) (curvesExtend_of_isCausalFlow hφ)

end BridgeInputs

section Bridge

variable (M : FlatSpacetime.{u} d)

/-- The universal cover of a flat spacetime is Hausdorff. -/
theorem t2Space_universalCover (x₀ : M) : T2Space (UniversalCover M x₀) :=
  haveI := locPathConnectedSpace_of_flat d M
  t2Space_of_isCoveringMap (UniversalCover.isCoveringMap_proj (y₀ := x₀) (semilocallySimplyConnected_of_flat d M))

/-- The splitting along a Cauchy surface **from a chronal causal flow and acausality** (a proved
reduction of `exists_splitting_of_isCauchySurface`): `Flat.flat_exists_isCauchySplitting`
(`Splitting.lean`) with `IsCausal` taken from `GH` (`GloballyHyperbolic` is `IsCausal ∧ compact
diamonds`) and `ψ (x, 0) = x` read off `IsCauchySplitting.zero`. -/
theorem exists_splitting_of_hasChronalCausalFlow
    (hflow : (flatCausality d M).HasChronalCausalFlow) (hGH : GH M) {S : Set M}
    (hS : (flatCausality d M).IsCauchySurface S) (hac : (flatCausality d M).IsAcausal S) :
    ∃ ψ : S × ℝ ≃ₜ M, ∀ x : S, ψ (x, 0) = x := by
  obtain ⟨ψ, hψ⟩ := Flat.flat_exists_isCauchySplitting hflow hGH.1 hS hac
  exact ⟨ψ, hψ.zero⟩

/-- The splitting `M ≅ S × ℝ` along a Cauchy surface. STATED, tagged `sorry`. This is a variant
of the homeomorphism half of Prop 8.11 (`bprop:splitting`, l.2459–2464; class E in
`docs/BARBOT-WAVE3.md` §3). Here `ψ` restricted to `S × {0}` is the inclusion, as in the flow
construction. The slices' Cauchy property, which Prop 8.11 also states, is not asked. It reduces
by `exists_splitting_of_hasChronalCausalFlow` to two inputs: target 4
(`Flat.flat_hasChronalCausalFlow`) and acausality of `S`. Both are discharged here
(`isAcausal_of_isCauchySurface_of_hasChronalCausalFlow` for the second), except for the
second countability of `M` that target 4 asks: the tagged `sorry` is that instance. -/
theorem exists_splitting_of_isCauchySurface (hGH : GH M) {S : Set M}
    (hS : (flatCausality d M).IsCauchySurface S) :
    ∃ ψ : S × ℝ ≃ₜ M, ∀ x : S, ψ (x, 0) = x := by
  haveI : SecondCountableTopology M := by
    sorry -- SORRY(bridge-B1): second countability of a flat spacetime, the ONLY missing input
    -- of the splitting. Everything else is proved: the chronal causal flow is
    -- `Flat.flat_hasChronalCausalFlow` (`Splitting.lean:1912`, 0 sorry), acausality of `S` is
    -- `isAcausal_of_isCauchySurface_of_hasChronalCausalFlow` (above: causal arc-connectedness from
    -- the charts and absolute minimality, `CurvesExtend` from the flow's orbits), and the
    -- splitting is `exists_splitting_of_hasChronalCausalFlow`. But `flat_hasChronalCausalFlow`
    -- asks `[SecondCountableTopology M]` (it builds the timelike field by a partition of unity,
    -- hence σ-compactness), and `FlatSpacetime` carries only `T2` + connected
    -- (`FlatSpacetime.lean`, SCOPE "No second countability"). Classically true, GH or not: a
    -- connected Hausdorff manifold with an affine connection (here the flat one: the transition
    -- maps lie in `Isom(𝐌ⁿ)`, affine) is paracompact (Geroch 1968), hence second countable
    -- (`ChartedSpace.secondCountable_of_sigmaCompact`). Neither that theorem (connection ⇒
    -- paracompact, via a Riemannian metric on the frame bundle) nor a GH substitute is in the
    -- library or mathlib: compact diamonds are local data, and σ-compactness needs a global
    -- exhaustion; the long line shows charts alone do not give it.
  exact exists_splitting_of_hasChronalCausalFlow M Flat.flat_hasChronalCausalFlow hGH hS
    (isAcausal_of_isCauchySurface_of_hasChronalCausalFlow Flat.flat_hasChronalCausalFlow hS)

/-- (B1) The lift `Ŝ = p⁻¹(S)` of a Cauchy surface to the universal cover is connected: from the
splitting (`exists_splitting_of_isCauchySurface`) and `connectedSpace_preimage_of_splitting`. -/
theorem connectedSpace_preimage_cauchy (hGH : GH M) {S : Set M}
    (hS : (flatCausality d M).IsCauchySurface S) (x₀ : M) :
    ConnectedSpace (UniversalCover.proj M x₀ ⁻¹' S) := by
  haveI := locPathConnectedSpace_of_flat d M
  haveI : PathConnectedSpace M := pathConnectedSpace_iff_connectedSpace.2 inferInstance
  obtain ⟨ψ, hψ⟩ := exists_splitting_of_isCauchySurface M hGH hS
  exact connectedSpace_preimage_of_splitting ψ hψ x₀

/-- (B2) **A developing map restricted to `Ŝ` is a spacelike development.** Near `z ∈ Ŝ`,
`dev = g • ψ ∘ proj` with `ψ` the chart at `proj z` (both are `IsGXMorphism`s, `g = g₁ g₂⁻¹`), and
`proj` is a local homeomorphism `e`; on a small open `W ∋ z`, `dev|Ŝ∩W` is `g • (e.trans ψ)`
restricted (an embedding), and its image is `g • (T ∩ V')` for `T` the chart picture of `hL` and
`V' = (e.trans ψ) '' W`; then `IsSpacelikeLipschitzIn.restrict` and `.smul`. -/
theorem spacelikeDevelopment_restrict {S : Set M} (hL : IsSpacelikeLipschitz d S) (x₀ : M) :
    letI := flatCoverChartedSpace d M x₀
    ∀ dev : UniversalCover M x₀ → Minkowski d, IsGXMorphism (isom d) (Minkowski d) dev →
      SpacelikeDevelopment ((UniversalCover.proj M x₀ ⁻¹' S).restrict dev) := by
  letI := flatCoverChartedSpace d M x₀
  intro dev hdev
  have hp : IsGXMorphism (isom d) (Minkowski d) (UniversalCover.proj M x₀) :=
    isGXMorphism_flatCover_proj M x₀
  set Sh := UniversalCover.proj M x₀ ⁻¹' S with hSh
  refine ⟨hdev.continuous.comp continuous_subtype_val, fun z => ?_⟩
  obtain ⟨V, hxV, -, hT⟩ := hL _ z.2
  set ψ := chartAt (Minkowski d) (UniversalCover.proj M x₀ (z : UniversalCover M x₀)) with hψ
  -- `dev = g • ψ ∘ proj` near `z`
  obtain ⟨g₁, hg₁⟩ := hdev.exists_smul_eq (z : UniversalCover M x₀)
  obtain ⟨g₂, hg₂⟩ := hp.exists_smul_eq (z : UniversalCover M x₀)
  obtain ⟨e, hze, hpe⟩ := hp.isLocalHomeomorph (z : UniversalCover M x₀)
  set g : isom d := g₁ * g₂⁻¹
  set N := {y : UniversalCover M x₀ | dev y = g • ψ (UniversalCover.proj M x₀ y)}
  have hN : N ∈ 𝓝 (z : UniversalCover M x₀) := by
    filter_upwards [hg₁, hg₂] with y h1 h2
    simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_apply, id_eq] at h1
    show dev y = g • ψ _
    rw [h1, h2, smul_smul, mul_assoc, inv_mul_cancel, mul_one]
  set K := e.trans ψ
  have hK : ∀ y, K y = ψ (UniversalCover.proj M x₀ y) := fun y => by
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, hpe]
  set W := interior N ∩ (K.source ∩ K ⁻¹' (V : Set (Minkowski d)))
  have hWo : IsOpen W := isOpen_interior.inter (K.isOpen_inter_preimage V.isOpen)
  have hWK : W ⊆ K.source := fun y hy => hy.2.1
  have hzW : (z : UniversalCover M x₀) ∈ W := by
    refine ⟨mem_interior_iff_mem_nhds.2 hN, ?_, ?_⟩
    · rw [OpenPartialHomeomorph.trans_source]
      exact ⟨hze, by rw [mem_preimage, ← hpe]; exact mem_chart_source _ _⟩
    · rw [mem_preimage, hK]; exact hxV
  let V' : Opens (Minkowski d) := ⟨K '' W, K.isOpen_image_of_subset_source hWo hWK⟩
  have hV'V : V' ≤ V := by
    rintro _ ⟨y, hy, rfl⟩; exact hy.2.2
  let U : Opens Sh := ⟨Subtype.val ⁻¹' W, hWo.preimage continuous_subtype_val⟩
  have hdevK : ∀ y ∈ W, dev y = g • K y := fun y hy => by
    rw [hK]; have := interior_subset hy.1; exact this
  refine ⟨U, smulOpens g V', hzW, ?_, ?_⟩
  · have h1 : IsEmbedding fun u : (U : Set Sh) => ((u : Sh) : UniversalCover M x₀) :=
      IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal
    have h2 := ((isom.toHomeomorph g).isEmbedding.comp K.isOpenEmbedding_restrict.isEmbedding).comp
      (h1.codRestrict K.source fun u => hWK u.2)
    convert h2 using 1
    funext u
    simp only [Set.restrict_apply, Function.comp_apply, isom.coe_toHomeomorph, codRestrict]
    exact hdevK _ u.2
  · have himg : Sh.restrict dev '' (U : Set Sh) =
        g • ((ψ '' (S ∩ ψ.source) ∩ (V : Set (Minkowski d))) ∩ (V' : Set (Minkowski d))) := by
      ext q
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [Set.restrict_apply, hdevK _ hy]
        refine smul_mem_smul_set ⟨⟨⟨_, ⟨y.2, ?_⟩, (hK y).symm⟩, hy.2.2⟩, ⟨_, hy, rfl⟩⟩
        have := hy.2.1
        rw [OpenPartialHomeomorph.trans_source] at this
        rw [← hpe] at this; exact this.2
      · intro hq
        obtain ⟨r, ⟨⟨⟨a, ⟨haS, has⟩, rfl⟩, -⟩, ⟨w, hw, hwr⟩⟩, rfl⟩ := Set.mem_smul_set.1 hq
        have hws : UniversalCover.proj M x₀ w ∈ ψ.source := by
          have := hw.2.1
          rw [OpenPartialHomeomorph.trans_source, ← hpe] at this; exact this.2
        have haw : a = UniversalCover.proj M x₀ w :=
          ψ.injOn has hws (by rw [← hK]; exact hwr.symm)
        refine ⟨⟨w, show UniversalCover.proj M x₀ w ∈ S from haw ▸ haS⟩, hw, ?_⟩
        rw [Set.restrict_apply, hdevK _ hw, hwr]
    rw [himg]
    exact (hT.restrict hV'V).smul isom_strongMorphism g

/-- **Transfer through a local isometry of charts** (pointwise): if near `c t` the developing
map `F` is `g • φ (q (c t)) ∘ q`, then `c` is Lipschitz in the pulled system at `t` iff `q ∘ c` is
in `φ`, with the same density. -/
theorem locLipAt_pulled_iff_of_eventually {X Y : Type*} [TopologicalSpace X]
    (F : X → Minkowski d) (φ : Y → Y → Minkowski d) (q : X → Y) {c : ℝ → X} {t : ℝ}
    (hc : ContinuousAt c t) {g : isom d} (hg : ∀ᶠ x in 𝓝 (c t), F x = g • φ (q (c t)) (q x)) :
    (LocLipAt (fun _ y => F y) c t ↔ LocLipAt φ (q ∘ c) t) ∧
      localDensity (fun _ y => F y) c t = localDensity φ (q ∘ c) t := by
  have hev : ∀ᶠ s in 𝓝 t, F (c s) = g • φ (q (c t)) (q (c s)) := hc.eventually hg
  obtain ⟨δ, hδ, hP⟩ := exists_Icc_subset_of_eventually hev
  refine ⟨⟨fun ⟨ε, hε, K, hK⟩ => ?_, fun ⟨ε, hε, K, hK⟩ => ?_⟩, ?_⟩
  · obtain ⟨K', hK'⟩ := isom_lipschitzWith g⁻¹
    refine ⟨min ε δ, lt_min hε hδ, K' * K, ?_⟩
    have hsub : Icc (t - min ε δ) (t + min ε δ) ⊆ Icc (t - ε) (t + ε) :=
      Icc_subset_Icc (by linarith [min_le_left ε δ]) (by linarith [min_le_left ε δ])
    have h1 := hK'.comp_lipschitzOnWith (hK.mono hsub)
    refine lipschitzOnWith_congr_of_eqOn (fun s hs => ?_) h1
    have : s ∈ Icc (t - δ) (t + δ) :=
      ⟨by linarith [hs.1, min_le_right ε δ], by linarith [hs.2, min_le_right ε δ]⟩
    simp only [Function.comp_apply, hP s this, inv_smul_smul]
  · obtain ⟨K', hK'⟩ := isom_lipschitzWith g
    refine ⟨min ε δ, lt_min hε hδ, K' * K, ?_⟩
    have hsub : Icc (t - min ε δ) (t + min ε δ) ⊆ Icc (t - ε) (t + ε) :=
      Icc_subset_Icc (by linarith [min_le_left ε δ]) (by linarith [min_le_left ε δ])
    have h1 := hK'.comp_lipschitzOnWith (hK.mono hsub)
    refine lipschitzOnWith_congr_of_eqOn (fun s hs => ?_) h1
    have : s ∈ Icc (t - δ) (t + δ) :=
      ⟨by linarith [hs.1, min_le_right ε δ], by linarith [hs.2, min_le_right ε δ]⟩
    simp only [Function.comp_apply, hP s this]
  · have hfun : (fun s => F (c s)) =ᶠ[𝓝 t] fun s => g • φ (q (c t)) (q (c s)) := hev
    change ENNReal.ofReal (Real.sqrt (minkQ (deriv (fun s => F (c s)) t))) =
      ENNReal.ofReal (Real.sqrt (minkQ (deriv (fun s => φ (q (c t)) (q (c s))) t)))
    rw [hfun.deriv_eq, deriv_isom_comp, minkQ_isom_linear]

/-- **Transfer of path lengths**: if `F` is, near every point, an isometry of `𝐌ⁿ` composed with
the chart system `φ` read through `q`, the pulled length of a path is the `φ`-length of its image. -/
theorem pathLength_pulled_eq_of_local {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (F : X → Minkowski d) (φ : Y → Y → Minkowski d) {q : X → Y} (hq : Continuous q)
    (hloc : ∀ x, ∃ g : isom d, ∀ᶠ x' in 𝓝 x, F x' = g • φ (q x) (q x')) {a b : X}
    (γ : Path a b) : pathLength (fun _ y => F y) γ = pathLength φ (γ.map hq) := by
  have hext : ⇑(γ.map hq).extend = q ∘ γ.extend := rfl
  have key : ∀ t, (LocLipAt (fun _ y => F y) γ.extend t ↔ LocLipAt φ (q ∘ γ.extend) t) ∧
      localDensity (fun _ y => F y) γ.extend t = localDensity φ (q ∘ γ.extend) t := fun t => by
    obtain ⟨g, hg⟩ := hloc (γ.extend t)
    exact locLipAt_pulled_iff_of_eventually F φ q γ.continuous_extend.continuousAt hg
  have hiff : IsLocLip (fun _ y => F y) γ.extend ↔ IsLocLip φ (γ.map hq).extend := by
    rw [hext]; exact forall_congr' fun t => (key t).1
  by_cases hL : IsLocLip (fun _ y => F y) γ.extend
  · rw [pathLength_of_isLocLip _ hL, pathLength_of_isLocLip _ (hiff.1 hL), hext]
    exact lintegral_congr fun t => (key t).2
  · rw [pathLength_of_not_isLocLip _ hL, pathLength_of_not_isLocLip _ (mt hiff.2 hL)]

/-- Near every point of the universal cover, a developing map is an isometry of `𝐌ⁿ` composed with
the chart of `M` at the projected point (the step `hN` of B2, isolated). -/
theorem exists_dev_eq_smul_chart (x₀ : M) :
    letI := flatCoverChartedSpace d M x₀
    ∀ dev : UniversalCover M x₀ → Minkowski d, IsGXMorphism (isom d) (Minkowski d) dev →
    ∀ z : UniversalCover M x₀, ∃ g : isom d, ∀ᶠ y in 𝓝 z,
      dev y = g • chartAt (Minkowski d) (UniversalCover.proj M x₀ z)
        (UniversalCover.proj M x₀ y) := by
  letI := flatCoverChartedSpace d M x₀
  intro dev hdev z
  have hp : IsGXMorphism (isom d) (Minkowski d) (UniversalCover.proj M x₀) :=
    isGXMorphism_flatCover_proj M x₀
  obtain ⟨g₁, hg₁⟩ := hdev.exists_smul_eq z
  obtain ⟨g₂, hg₂⟩ := hp.exists_smul_eq z
  refine ⟨g₁ * g₂⁻¹, ?_⟩
  filter_upwards [hg₁, hg₂] with y h1 h2
  simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_apply, id_eq] at h1
  rw [h1, h2, smul_smul, mul_assoc, inv_mul_cancel, mul_one]

/-- (B3) **The pulled-back length on `Ŝ` is complete.** `proj` does not increase lengths
(`pathLength_pulled_eq_of_local`), so a Cauchy sequence of `Ŝ` projects to one of `S`, convergent
by `hc`; by `htop` a length ball about the limit lies in an evenly covered `U`, the tail of the
sequence lies on one sheet, and the sheet's section lifts short paths to the limit. -/
theorem completeSpace_pulledLength_restrict {S : Set M} (hL : IsSpacelikeLipschitz d S)
    (hc : CompleteSpace (InducedLengthSpace d S))
    (htop : Continuous fun x : InducedLengthSpace d S => (InducedLengthSpace.toSubtype x : M))
    (x₀ : M) :
    letI := flatCoverChartedSpace d M x₀
    ∀ dev : UniversalCover M x₀ → Minkowski d, IsGXMorphism (isom d) (Minkowski d) dev →
      CompleteSpace (PulledLength ((UniversalCover.proj M x₀ ⁻¹' S).restrict dev)) := by
  -- `hL` is not needed: the comparison of lengths only uses that `dev` and `proj` are GX maps.
  have _unusedL := hL
  letI := flatCoverChartedSpace d M x₀
  intro dev hdev
  haveI := locPathConnectedSpace_of_flat d M
  set p := UniversalCover.proj M x₀ with hp
  have hcov : IsCoveringMap p :=
    UniversalCover.isCoveringMap_proj (semilocallySimplyConnected_of_flat d M)
  set Sh := p ⁻¹' S with hSh
  set F := Sh.restrict dev with hF
  let q : Sh → S := fun z => ⟨p z, z.2⟩
  have hq : Continuous q := (hcov.continuous.comp continuous_subtype_val).subtype_mk _
  have hloc : ∀ z : Sh, ∃ g : isom d, ∀ᶠ z' in 𝓝 z, F z' = g • chartSys d S (q z) (q z') := by
    intro z
    obtain ⟨g, hg⟩ := exists_dev_eq_smul_chart M x₀ dev hdev z
    exact ⟨g, continuous_subtype_val.continuousAt.eventually hg⟩
  have hlen : ∀ {a b : Sh} (γ : Path a b),
      pathLength (fun _ y => F y) γ = pathLength (chartSys d S) (γ.map hq) :=
    fun γ => pathLength_pulled_eq_of_local F (chartSys d S) hq hloc γ
  -- `q` does not increase distances
  let Q : PulledLength F → InducedLengthSpace d S := q
  have hQ : ∀ a b : PulledLength F, edist (Q a) (Q b) ≤ edist a b := fun a b =>
    le_iInf fun γ => (iInf_le _ (γ.map hq)).trans_eq (hlen γ).symm
  have hQu : UniformContinuous Q :=
    (LipschitzWith.of_edist_le hQ).uniformContinuous
  refine EMetric.complete_of_cauchySeq_tendsto fun u hu => ?_
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete (hQu.comp_cauchySeq hu)
  set ys : S := InducedLengthSpace.toSubtype y with hys
  -- an evenly covered neighbourhood `U` of the limit, and a length ball inside it
  obtain ⟨hdisc, U, hyU, hUo, -, H, hH⟩ := hcov (ys : M)
  have hO : IsOpen {w : InducedLengthSpace d S | ((InducedLengthSpace.toSubtype w : S) : M) ∈ U} :=
    hUo.preimage htop
  obtain ⟨r, hr, hball⟩ := EMetric.isOpen_iff.1 hO y hyU
  have hr2 : (0 : ℝ≥0∞) < r / 2 := ENNReal.half_pos hr.ne'
  -- a short path starting near `y` stays in `U`
  have stay : ∀ {a b : S} (β : Path a b),
      edist y (InducedLengthSpace.toSubtype.symm a) < r / 2 →
      pathLength (chartSys d S) β < r / 2 → ∀ t, ((β t : S) : M) ∈ U := by
    intro a b β ha hβ t
    have h1 : edist (InducedLengthSpace.toSubtype.symm a : InducedLengthSpace d S)
        (InducedLengthSpace.toSubtype.symm (β t)) ≤ pathLength (chartSys d S) β :=
      LocalLengthSpace.edist_le_pathLength (chartSys d S) β t
    have h2 : edist (InducedLengthSpace.toSubtype.symm (β t) : InducedLengthSpace d S) y < r := by
      rw [edist_comm]
      calc edist y (InducedLengthSpace.toSubtype.symm (β t))
          ≤ edist y (InducedLengthSpace.toSubtype.symm a) +
            edist (InducedLengthSpace.toSubtype.symm a : InducedLengthSpace d S)
              (InducedLengthSpace.toSubtype.symm (β t)) := edist_triangle _ _ _
        _ < r / 2 + r / 2 := ENNReal.add_lt_add ha (h1.trans_lt hβ)
        _ = r := ENNReal.add_halves r
    exact hball h2
  let w : ℕ → Sh := fun n => PulledLength.toSpace F (u n)
  obtain ⟨N₁, hN₁⟩ := EMetric.cauchySeq_iff.1 hu (r / 2) hr2
  obtain ⟨N₂, hN₂⟩ := EMetric.tendsto_atTop.1 hy (r / 2) hr2
  set N := max N₁ N₂
  have hnear : ∀ n ≥ N₂, edist y (InducedLengthSpace.toSubtype.symm (q (w n))) < r / 2 :=
    fun n hn => by rw [edist_comm]; exact hN₂ n hn
  have hwU : ∀ n ≥ N₂, p (w n : UniversalCover M x₀) ∈ U := fun n hn =>
    hball (by rw [Metric.mem_eball, edist_comm]; exact (hnear n hn).trans_le ENNReal.half_le_self)
  haveI := hdisc
  -- the sheet of `w N`, and its section `sec` over `U`
  have hNU : p (w N : UniversalCover M x₀) ∈ U := hwU N (le_max_right _ _)
  set i := (H ⟨w N, hNU⟩).2 with hi
  let sec : U → UniversalCover M x₀ := fun v => (H.symm (v, i) : UniversalCover M x₀)
  have hsecc : Continuous sec := continuous_subtype_val.comp (H.symm.continuous.comp
    (continuous_id.prodMk continuous_const))
  have hpsec : ∀ v : U, p (sec v) = v := fun v => by
    have := hH (H.symm (v, i)); rw [Homeomorph.apply_symm_apply] at this; exact this.symm
  have hseccongr : ∀ {a b : M} (ha : a ∈ U) (hb : b ∈ U), a = b → sec ⟨a, ha⟩ = sec ⟨b, hb⟩ := by
    rintro a b ha hb rfl; rfl
  -- every `w n`, `n ≥ N`, lies on that sheet
  have hsheet : ∀ n (hn : n ≥ N), sec ⟨p (w n : UniversalCover M x₀), hwU n (le_of_max_le_right hn)⟩ =
      (w n : UniversalCover M x₀) := by
    intro n hn
    have hnU := hwU n (le_of_max_le_right hn)
    obtain ⟨γ, hγ⟩ := iInf_lt_iff.1 (hN₁ N (le_max_left _ _) n (le_trans (le_max_left _ _) hn))
    have hγ' : pathLength (chartSys d S) (γ.map hq) < r / 2 := (hlen γ) ▸ hγ
    have hst := stay (γ.map hq) (hnear N (le_max_right _ _)) hγ'
    let f : I → p ⁻¹' {(ys : M)} := fun t => (H ⟨(γ t : UniversalCover M x₀), hst t⟩).2
    have hf : Continuous f := continuous_snd.comp (H.continuous.comp
      ((continuous_subtype_val.comp γ.continuous).subtype_mk _))
    have h01 : f 0 = f 1 := PreconnectedSpace.constant inferInstance hf
    have e0 : f 0 = i := by
      simp only [f, hi]; congr 2; exact Subtype.ext (by simp; rfl)
    have e1 : H ⟨w n, hnU⟩ = (⟨p (w n : UniversalCover M x₀), hnU⟩, i) := by
      refine Prod.ext (Subtype.ext (hH _)) ?_
      rw [← e0, h01]; simp only [f]; congr 2; exact Subtype.ext (by simp; rfl)
    have := congrArg (fun v => (H.symm v : UniversalCover M x₀)) e1
    simp only [Homeomorph.symm_apply_apply] at this
    exact this.symm
  -- the limit: the point of the sheet over `y`
  let z : Sh := ⟨sec ⟨ys, hyU⟩, by
    show p (sec ⟨ys, hyU⟩) ∈ S
    rw [hpsec]; exact ys.2⟩
  refine ⟨PulledLength.toSpace F |>.symm z, EMetric.tendsto_atTop.2 fun ε hε => ?_⟩
  have hε' : (0 : ℝ≥0∞) < min ε (r / 2) := lt_min hε hr2
  obtain ⟨N₃, hN₃⟩ := EMetric.tendsto_atTop.1 hy _ hε'
  refine ⟨max N N₃, fun n hn => ?_⟩
  have hnN : n ≥ N := le_trans (le_max_left _ _) hn
  have hn2 : n ≥ N₂ := le_trans (le_max_right _ _) hnN
  obtain ⟨β, hβ⟩ := iInf_lt_iff.1 (hN₃ n (le_trans (le_max_right _ _) hn))
  have hβ2 : pathLength (chartSys d S) β < r / 2 := hβ.trans_le (min_le_right _ _)
  have hst := stay β (hnear n hn2) hβ2
  have hlift : ∀ t, p (sec ⟨(β t : M), hst t⟩) ∈ S := fun t => by rw [hpsec]; exact (β t).2
  let βl : Path (w n) z :=
    { toFun := fun t => ⟨sec ⟨(β t : M), hst t⟩, hlift t⟩
      continuous_toFun := (hsecc.comp ((continuous_subtype_val.comp β.continuous).subtype_mk
        _)).subtype_mk _
      source' := Subtype.ext ((hseccongr _ _ (by rw [β.source]; rfl)).trans (hsheet n hnN))
      target' := Subtype.ext (hseccongr _ _ (by rw [β.target]; rfl)) }
  have hext : ⇑(βl.map hq).extend = ⇑β.extend := by
    funext t; exact Subtype.ext (hpsec _)
  calc edist (u n) (PulledLength.toSpace F |>.symm z) ≤ pathLength (fun _ y => F y) βl :=
        iInf_le _ βl
    _ = pathLength (chartSys d S) β := (hlen βl).trans (pathLength_congr_extend _ _ _ hext)
    _ < min ε (r / 2) := hβ
    _ ≤ ε := min_le_left _ _

/-- **The bridge** (DEC-35, `docs/BARBOT-WAVE3.md` §3): paper's Cauchy-completeness ⇒ (CC′). -/
theorem developsCC_of_isCauchyComplete (hGH : GH M) {S : Set M}
    (hS : (flatCausality d M).IsCauchySurface S) (hL : IsSpacelikeLipschitz d S)
    (hc : CompleteSpace (InducedLengthSpace d S))
    (htop : Continuous fun x : InducedLengthSpace d S => (InducedLengthSpace.toSubtype x : M))
    (x₀ : M) :
    letI := flatCoverChartedSpace d M x₀
    ∀ dev : UniversalCover M x₀ → Minkowski d, IsGXMorphism (isom d) (Minkowski d) dev →
      (flatCausality d M).IsCauchySurface S ∧
      InjOn dev (UniversalCover.proj M x₀ ⁻¹' S) ∧
      IsEntireAcausalGraph (dev '' (UniversalCover.proj M x₀ ⁻¹' S)) ∧
      NullSaturated (dev '' (UniversalCover.proj M x₀ ⁻¹' S)) := by
  letI := flatCoverChartedSpace d M x₀
  intro dev hdev
  haveI := connectedSpace_preimage_cauchy M hGH hS x₀
  haveI := t2Space_universalCover M x₀
  have hF := spacelikeDevelopment_restrict M hL x₀ dev hdev
  have hcF := completeSpace_pulledLength_restrict M hL hc htop x₀ dev hdev
  have hr : range ((UniversalCover.proj M x₀ ⁻¹' S).restrict dev) =
      dev '' (UniversalCover.proj M x₀ ⁻¹' S) := Set.range_restrict _ _
  refine ⟨hS, Set.injOn_iff_injective.2 (hF.injective_of_complete hcF), ?_, ?_⟩
  · rw [← hr]; exact isEntireAcausalGraph_range hF hcF
  · rw [← hr]; exact bcor_quoiso hF hcF

/-- The bridge, from `IsCauchyComplete`: some Cauchy surface develops as (CC′). -/
theorem exists_developsCC_of_isCauchyComplete (hGH : GH M) (hCC : IsCauchyComplete d M)
    (x₀ : M) :
    letI := flatCoverChartedSpace d M x₀
    ∃ S : Set M, ∀ dev : UniversalCover M x₀ → Minkowski d,
      IsGXMorphism (isom d) (Minkowski d) dev →
      (flatCausality d M).IsCauchySurface S ∧
      InjOn dev (UniversalCover.proj M x₀ ⁻¹' S) ∧
      IsEntireAcausalGraph (dev '' (UniversalCover.proj M x₀ ⁻¹' S)) ∧
      NullSaturated (dev '' (UniversalCover.proj M x₀ ⁻¹' S)) := by
  obtain ⟨S, hS, hL, hc, htop⟩ := hCC
  exact ⟨S, developsCC_of_isCauchyComplete M hGH hS hL hc htop x₀⟩

end Bridge

end Causal.Flat
