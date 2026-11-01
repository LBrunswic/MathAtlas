import CausalScaffold.Flat.InducedLength
import CausalScaffold.Flat.FlatSpacetime
import CausalScaffold.Flat.LipschitzGraph
import CausalScaffold.Flat.Developing
import CausalScaffold.Splitting

/-!
# `CausalScaffold.Flat.CauchyComplete` — Cauchy-completeness of a flat spacetime, and the bridge to (CC′)

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §2.4 and
§8. Labels (all UNMARKED: each rests on a tagged `sorry` or is a reading, see SCOPE):
`bprop:project` — `GHFspace.tex` (labelled) l.2232–2261; `bcor:quoiso` — l.2277–2290;
`[2.4]` Cauchy-complete — l.551–558 (prose, DEC-35); `[8.G]` the graph remark — l.2307–2309;
`bcor:quo`'s last clause ("intersects every timelike geodesic") — l.2263–2271. Design:
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
* `bprop_project` (8.1): `projAlong Δ ∘ F` is a homeomorphism; from `isCoveringMap_projAlong_comp`
  (sorry, R1/W5) and the lemma above.
* `isEntireAcausalGraph_range` ([8.G], Cor 8.2's last clause), PROVED from 8.1: `range F` is an
  entire acausal graph — achronal by injectivity of `π`, and null pairs excluded by
  `IsSpacelikeLipschitzIn.not_eventually_add_smul_mem` (no germ of null segment, `c < 1`) through
  `lipschitzWith_one_segment`; also `injective_of_complete`, `exists_graph`.
* `bcor_quoiso` (8.3): `NullSaturated (range F)` (sorry, W6).
* **The bridge** `developsCC_of_isCauchyComplete`: for GH `M`, `S` as in `IsCauchyComplete` and any
  developing map `dev`: `S` Cauchy, `dev` injective on `Ŝ = p⁻¹(S)`, `dev '' Ŝ` an entire acausal
  graph meeting every timelike line, and `NullSaturated`. ASSEMBLED (proved) from 8.1, 8.3, B1, B2,
  B3; `t2Space_universalCover` is proved. `exists_developsCC_of_isCauchyComplete`.
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
    `Splitting.lean`, itself a tagged sorry) and acausality of `S`.

## Hypothesis checklist
| paper hypothesis | here |
|---|---|
| `M` GH (l.551) | ✓ carried in the bridge (`GH M`), in ETT's reading (BARBOT-THEOREMS §1, "ETT's is used"); classically implied by `hS` (Barbot's GH is the existence of a Cauchy surface), but in the library Geroch (iii)⇒(i) is itself a `sorry`, so it is carried rather than derived; consumed only by B1 (through `exists_splitting_of_isCauchySurface`). `IsCauchyComplete` alone does not ask it, as `AMGH` composes them |
| a Cauchy hypersurface (l.551) | ✓ carried: ETT's `IsCauchySurface` |
| "the ambiant lorentzian metric restricts as a riemanian metric" | ⚠ weakened (a reading): point-locally spacelike Lipschitz in flat charts (DEC-31/35), not smooth |
| "complete" | ✓ carried: `CompleteSpace` of the glued length pseudo-emetric; plus the topology field (W3: without spacelikeness the length can vanish; for spacelike `S` the field holds locally, `IsSpacelikeLipschitzIn.isHomeomorph_toSubtype`, its gluing is not proved here) |
| 8.1: `f : S → M` isometric immersion of a complete riemannian hypersurface, `S̃`, `𝒟 ∘ f̃` | ⚠ weakened: any connected T2 `X`, `F` a `SpacelikeDevelopment` (Lipschitz), `PulledLength F` complete |
| 8.1: `Δ` a timelike direction, `Q(Δ) = 𝐌ⁿ/Δ` with its metric | ✓ carried: `minkQ Δ < 0` (both orientations); `Q(Δ)` is modelled TOPOLOGICALLY by `Δ^⊥` (`π` is the identity on `Δ^⊥`). The paper's metric is `minkQ` restricted to `Δ^⊥` (positive definite); the Lean subtype carries the sup-product metric of `ℝ × ℝᵈ`, equivalent to it but not equal — only the topology enters 8.1's homeomorphism |
| 8.3: same set-up | ✓ carried, as for 8.1 |

## SCOPE (disclosed)
* **Three tagged sorries.** `isCoveringMap_projAlong_comp` (the covering of 8.1, R1/W5: the
  design estimated about 500 lines; the closer's breakdown in the obstruction, four steps, puts it
  nearer 1000), `bcor_quoiso` (8.3, W6: its closedness half needs the same topology and
  segment-lifting steps), and `exists_splitting_of_isCauchySurface` (tag `bridge-B1`: the
  splitting `M ≅ S × ℝ`, class E; it reduces to target 4 plus `IsAcausal S` through the proved
  `exists_splitting_of_hasChronalCausalFlow`). Each carries its obstruction. Everything else is proved: the
  whole length structure and its link to `InducedLength`, `π` and its kernel, covering ⇒
  homeomorphism, 8.1 ⇒ the entire acausal graph, B1 from the splitting, B2, B3, the non-vacuity
  witnesses, the bridge's assembly.
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

theorem isCoveringMap_projAlong_comp {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    [T2Space X] {F : X → Minkowski d} (hF : SpacelikeDevelopment F)
    (hc : CompleteSpace (PulledLength F)) {Δ : Minkowski d} (hΔ : minkQ Δ < 0) :
    IsCoveringMap (projAlong Δ hΔ.ne ∘ F) := by
  sorry -- SORRY(bprop:project): R1/W5. Four steps, none in mathlib or the port;
  -- `isHomeomorph_of_isCoveringMap` then finishes 8.1. (i) LOCAL HOMEOMORPHISM: in the frame
  -- `g` of `IsSpacelikeLipschitzIn.locGraph` a piece of `range F` is a `c`-Lipschitz graph over
  -- an open `U`, `c < 1`; `π` is injective on it (distinct points are spacelike separated), and
  -- its image is open by the IVT along `Δ`-lines: `s ↦ (w + sΔ').1 − f((w + sΔ').2)` is strictly
  -- monotone since `c ‖Δ'.2‖ < |Δ'.1|` (`Δ' = g.linear Δ` timelike) — no invariance of
  -- domain is available. (ii) TOPOLOGY: the pulled-length topology is finer than `X`'s, else
  -- `hc`'s limits are not limits in `X` (it is NOT a hypothesis here, unlike `IsCauchyComplete`'s
  -- field): for subsets of `𝐌ⁿ` it is `IsSpacelikeLipschitzIn.continuous_toSubtype`
  -- (`InducedLength.lean:1082`), to be transported through the embeddings of
  -- `SpacelikeDevelopment.locally` by a first-exit argument. (iii) SEGMENT LIFTING (W5): `π` does
  -- not decrease `√minkQ` of spacelike vectors, so a lift of a straight segment of `Δ^⊥` has
  -- pulled length at most the segment's; a maximal lift on `[0, t)` is Cauchy, converges by `hc`
  -- and (ii), and extends by (i); lifts are unique (`T2Space X`, (i), `IsSeparatedMap`).
  -- (iv) ASSEMBLY: radial lifts from the fibre give sections over all of `Δ^⊥`; their continuity
  -- is the Lebesgue-number argument along the compact lifted segment; disjoint open sheets then
  -- give `isEvenlyCovered_of_sheets` (Port/UniversalCover.lean:204). Estimate ~1000 lines.

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

theorem bcor_quoiso {X : Type*} [TopologicalSpace X] [ConnectedSpace X] [T2Space X]
    {F : X → Minkowski d} (hF : SpacelikeDevelopment F) (hc : CompleteSpace (PulledLength F)) :
    NullSaturated (range F) := by
  sorry -- SORRY(bcor:quoiso): W6. Frame `P₀ = {t − x₁ = c}`, `Δ₀ = (1, e₁)`, `range F = graph f`
  -- (`SpacelikeDevelopment.exists_graph`; `f` strictly contracting by `isEntireAcausalGraph_range`
  -- through `isEntireAcausalGraph_iff`). Put
  -- `Y_c = {y ⊥ e₁ | ∃ s, f (y + s e₁) − s = c}`. Open: `s ↦ f (y + s e₁) − s` is strictly
  -- decreasing, so values `c₁ > c > c₂` on both sides persist for `y'` near `y`, and the
  -- intermediate value theorem applies (no completeness). Closed: the only place completeness
  -- enters (the entire-graph structure from 8.1 alone does not bound `s(y)` as `y` moves): the
  -- lift `y ↦ y + s(y) e₁ ∈ range F ∩ P₀` of a segment
  -- of `e₁^⊥` has `minkQ`-length equal to the segment's Euclidean length (the projection
  -- `P₀ → P₀/Δ₀` is isometric on it), so the maximal-lift argument of 8.1 gives the limit point:
  -- the same missing steps (ii) TOPOLOGY and (iii) SEGMENT LIFTING as
  -- `isCoveringMap_projAlong_comp`, run in the `(n − 2)`-dimensional `range F ∩ P₀`. `e₁^⊥` is
  -- connected, so `Y_c` is empty or all of it.

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
(`Flat.flat_hasChronalCausalFlow`) and acausality of `S`. -/
theorem exists_splitting_of_isCauchySurface (hGH : GH M) {S : Set M}
    (hS : (flatCausality d M).IsCauchySurface S) :
    ∃ ψ : S × ℝ ≃ₜ M, ∀ x : S, ψ (x, 0) = x := by
  sorry -- SORRY(bridge-B1): the splitting of a GH flat spacetime along a Cauchy surface. Proved
  -- reduction: `exists_splitting_of_hasChronalCausalFlow` (via `Flat.flat_exists_isCauchySplitting`,
  -- `Splitting.lean:1084`, whose `IsCauchySplitting.zero` is `ψ (x, 0) = x`; `IsCausal` is
  -- `hGH.1`). The two missing inputs. (1) The flow: `Flat.flat_hasChronalCausalFlow`
  -- (`Splitting.lean:1078`) is itself a tagged sorry (SORRY target-4: no global flow of a complete
  -- timelike vector field, `lem:vecteur`), and it also asks `[SecondCountableTopology M]`, which is
  -- not a field of `FlatSpacetime` (paracompactness of a Lorentzian manifold, Geroch, is not
  -- formalized). (2) Acausality `(flatCausality d M).IsAcausal S`: `IsCauchySurface.isAcausal`
  -- needs `CausallyArcConnected` and `CurvesExtend`. The library supplies `CurvesExtend` only
  -- from a time function (`isAcausal_of_timeFunction`) or under `geroch`'s measure/tarentin
  -- hypotheses (`isAcausal_of_globallyHyperbolic`, `CurvesExtend.lean:480`), none proved for
  -- `flatCausality`.

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

/-- The linear part of an isometry preserves `minkQ`. -/
theorem minkQ_isom_linear (g : isom d) (v : Minkowski d) :
    minkQ ((g : Minkowski d ≃ᵃ[ℝ] Minkowski d).linear v) = minkQ v := by
  rw [show ((g : Minkowski d ≃ᵃ[ℝ] Minkowski d).linear v) =
      (linearPart g : Minkowski d ≃ₗ[ℝ] Minkowski d) v from rfl,
    lorentz.minkQ_apply (linearPart g).2]

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
