import Causal.Flat.Form
import Causal.GXStructure
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Topology.Connected.PathConnected

/-!
# `Causal.Flat.InducedLength` — the induced length of achronal Lipschitz hypersurfaces

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257).
Labels (unmarked: both are prose and both are `partial`, see SCOPE):
`[8.L]` — Lipschitz spacelike hypersurfaces and their length (`GHFspace.tex` labelled
l.2307–2319, orig l.2278–2290); `[2.4]` — Cauchy-complete (labelled l.551–557, orig l.549–555;
DEC-35). Neither id is yet in `docs/BARBOT.md`'s label list (the §2 entry is the unnamed
"Cauchy-complete (l.549)"); registering them is the master session's. This module is the chart-local length structure of DEC-35 / DEC-31 and the
interface of the contract with gx (`docs/BARBOT.md`, items (a)–(f)); design
`docs/BARBOT-WAVE3.md` §1E.

> A GH spacetime is *Cauchy-complete* if it admits a Cauchy hypersurface where the ambiant
> lorentzian metric restricts as a complete riemanian metric. (l.551–553)

> it is worth to extend the definition of spacelike hypersurfaces to (local) graphs of contracting
> maps from (euclidean) ${\mathbb R}^{n-1}$ into (euclidean) ${\mathbb R}$. […] This low regularity
> is sufficient to define a (non-riemannian) length metric on the spacelike hypersurface, since
> Lipschitz maps are differentiable almost everywhere: if $c: t \mapsto {\mathbb R}^{n-1}$ is a
> $C^{1}$-curve in ${\mathbb R}^{n-1}$, define the length of $\varphi \circ c$ as the Lebesgue
> integral of $\sqrt{1-\varphi'(c(t))^{2}} \Vert c'(t) \Vert$. (l.2310–2319)

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; `Minkowski d` has `d` spatial
dimensions, so Barbot's `n` is `d + 1`, and his `ℝ^{n−1}` is `EuclideanSpace ℝ (Fin d)`.

* **(a)** `IsLipschitzHypersurfaceIn V Σ`, `IsSpacelikeLipschitzIn V Σ` (`V` open): achronal for
  `≪_V`, and near each point, in some frame `g ∈ isom d`, the graph `graphOver U f` of an
  `f` that is `1`-Lipschitz (resp. `c`-Lipschitz, `c < 1` **depending on the point**, item (f)).
  Inhabitants: `isLipschitzHypersurfaceIn_graphOver`, `isSpacelikeLipschitzIn_graphOver`.
* `lorentzLength γ a b = ∫⁻_{(a,b]} √(minkQ γ')`; `lengthOn Σ V γ` its value on a curve
  `γ : C(I, Σ ∩ V)` if `γ` is Lipschitz, `⊤` otherwise; `InducedLength Σ V`, a type synonym of
  `Σ ∩ V`, with `edist x y = ⨅ γ : Path x y, lengthOn Σ V γ` (`edist_def`), item (e).
* **(b)** `lorentzLength_isom`, `lengthOn_curveSMul`, `InducedLength.edist_smulMap`;
  `IsLipschitzHypersurfaceIn.smul`, `IsSpacelikeLipschitzIn.smul` (into `smulOpens g V`).
* **(c)** `lengthOn_congr` (the length depends only on the points of the curve, not on `Σ, V`),
  `lorentzLength_add`, `lengthOn_trans`, `lorentzLength_congr`, `InducedLength.edist_inclusion_le`.
* **(d)** DEC-31's specialisation: `lengthOn_eq_integral` (every Lipschitz curve) and
  `lengthOn_eq_integral_of_isPiecewiseC1On`: the length is the classical `∫₀¹ √(minkQ γ')`;
  metric level, `≤` only: `InducedLength.edist_le_iInf_piecewiseC1`.
* **(e)** `IsSpacelikeLipschitzIn.isHomeomorph_toSubtype`: the length topology is the subspace
  topology, from `√(1 − c²) ‖Δx‖ ≤ d ≤ ‖Δx‖` (`le_lorentzLength_of_frame`,
  `InducedLength.edist_le_frame`); the half `d ≤ ‖Δx‖` holds for every achronal Lipschitz
  hypersurface (`continuous_toSubtype_symm`). It FAILS without spacelikeness:
  `nullGraph_edist_eq_zero`, `not_continuous_toSubtype_nullGraph` (W3, achronal form).

## Hypothesis checklist
| paper | here |
|---|---|
| `C¹` curve `c` in `ℝ^{n−1}`, length of `φ ∘ c` | ⚠ weakened: every Lipschitz curve of `Σ ∩ V`; for `C¹`/piecewise `C¹` it is the classical integral (d) |
| integrand `√(1 − φ'(c)²) ‖c'‖` | ✓ carried (corrected form, W2 finding): `√(minkQ γ')`, `γ = (φ∘c, c)`; Barbot's form is right only for `n − 1 = 1` and needs `φ'` along `c` |
| "graphs of contracting maps" | ✓ carried (in a reading): locally `c`-Lipschitz, `c < 1` per point (W3); `1`-Lipschitz for the plain predicate |
| isometries of `𝐌ⁿ` | ✓ carried: `isom d`, `MulAction`/`ContinuousConstSMul` untouched |
| "a Cauchy hypersurface where the ambiant lorentzian metric restricts as a complete riemanian metric" (l.551–553) | ⚠ weakened: chart-local length space only (no Cauchy hypersurface, no `CompleteSpace`; gx's) |

## SCOPE (disclosed)
* `IsLipschitzHypersurfaceIn.smul` / `IsSpacelikeLipschitzIn.smul` carry
  `hG : ∀ g, StrongMorphism (minkowski d) (minkowski d) (g • ·)`, which is
  `Causal.Flat.IsomCausal.isom_strongMorphism` (not importable in this wave); it is used for
  the achronality field only. Every other statement is unconditional. When `IsomCausal` is
  imported at graduation `hG` is dropped, so these two signatures (imported by gx) change.
* **DEC-31 at the metric level is not proved.** (d) is curve-level: for a piecewise-smooth
  spacelike `Σ`, `edist` (an inf over Lipschitz paths) equal to the classical inf over piecewise
  `C¹` paths is NOT proved; only `≤` follows, stated as
  `InducedLength.edist_le_iInf_piecewiseC1`. The `≥` direction needs approximating a Lipschitz
  path of `Σ` by piecewise-`C¹` paths of `Σ` with lengths converging, i.e. smoothness of `Σ`.
* `Causal.Flat.Achronal` (`graph f`, `isAchronal_graph_iff`) was outside this wave's
  dispatched imports, so `graphOver univ f` (= `graph f`), `nullGraph e` (= `graph (inner e ·)`)
  and `not_lt_top_of_graphOver` (one direction of `isAchronal_graph_iff`) re-derive it. At
  graduation: import `Achronal` (no cycle), restate via `graph f`, derive the achronality.
* Imports beyond the dispatched `Causal.Flat.Form`: the strict `Causal.GXStructure`
  (`smulOpens`, `StrongMorphism`, `smul_rel_iff`) and mathlib modules only; no other scaffold file.
* The chord-sum limit (mesh → 0) is not stated; nothing downstream reads it. The length is never a
  sup/inf of chord sums.
* W3's acausal counterexample (`f = ∫σ`, `σ = ±1` on sets meeting every interval in positive
  measure) is not formalized; the null hyperplane is the cheaper achronal one.
* The metric is chart-local (contract (a)); gluing along a Cauchy surface and `CompleteSpace` are
  the consumer's (`CauchyComplete`, gx). `Σ` is written `S` (`Σ` is a Lean keyword).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Written by WP-32c
(Barbot campaign, wave 3a).
-/

namespace Causal.Flat

open Set TopologicalSpace MeasureTheory Filter Topology
open scoped ENNReal NNReal unitInterval Pointwise

variable {d : ℕ}

/-! ### Lipschitz hypersurfaces of an open set -/

/-- The graph `{q | q.2 ∈ U ∧ q.1 = f q.2}` of `f : ℝᵈ → ℝ` over `U ⊆ ℝᵈ`, in the frame of
`𝐌ⁿ` (time first). -/
def graphOver (U : Set (EuclideanSpace ℝ (Fin d))) (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    Set (Minkowski d) :=
  {q | q.2 ∈ U ∧ q.1 = f q.2}

/-- **An achronal Lipschitz hypersurface of the open set `V`.** -/
structure IsLipschitzHypersurfaceIn (V : Opens (Minkowski d)) (S : Set (Minkowski d)) : Prop where
  subset : S ⊆ V
  achronal : ∀ p ∈ S, ∀ q ∈ S, ¬ (minkowski d).lt V p q
  locGraph : ∀ p ∈ S, ∃ (g : isom d) (O : Opens (Minkowski d))
    (U : Set (EuclideanSpace ℝ (Fin d))) (f : EuclideanSpace ℝ (Fin d) → ℝ),
    p ∈ O ∧ O ≤ V ∧ IsOpen U ∧ LipschitzOnWith 1 f U ∧
      g • (S ∩ (O : Set (Minkowski d))) = g • (O : Set (Minkowski d)) ∩ graphOver U f

/-- **An achronal spacelike Lipschitz hypersurface of the open set `V`**: the slope bound `c < 1`
depends on the point (contract item (f)). -/
structure IsSpacelikeLipschitzIn (V : Opens (Minkowski d)) (S : Set (Minkowski d)) : Prop where
  subset : S ⊆ V
  achronal : ∀ p ∈ S, ∀ q ∈ S, ¬ (minkowski d).lt V p q
  locGraph : ∀ p ∈ S, ∃ (g : isom d) (O : Opens (Minkowski d))
    (U : Set (EuclideanSpace ℝ (Fin d))) (f : EuclideanSpace ℝ (Fin d) → ℝ) (c : ℝ≥0),
    c < 1 ∧ p ∈ O ∧ O ≤ V ∧ IsOpen U ∧ LipschitzOnWith c f U ∧
      g • (S ∩ (O : Set (Minkowski d))) = g • (O : Set (Minkowski d)) ∩ graphOver U f

theorem IsSpacelikeLipschitzIn.toIsLipschitzHypersurfaceIn {V : Opens (Minkowski d)}
    {S : Set (Minkowski d)} (h : IsSpacelikeLipschitzIn V S) : IsLipschitzHypersurfaceIn V S := by
  refine ⟨h.subset, h.achronal, fun p hp => ?_⟩
  obtain ⟨g, O, U, f, c, hc, hpO, hOV, hU, hf, hgr⟩ := h.locGraph p hp
  exact ⟨g, O, U, f, hpO, hOV, hU, hf.weaken hc.le, hgr⟩

@[simp] theorem coe_smulOpens (g : isom d) (V : Opens (Minkowski d)) :
    (smulOpens g V : Set (Minkowski d)) = g • (V : Set (Minkowski d)) :=
  Set.image_smul

/-- Changing the frame from `g₀` to `g₀ g⁻¹` after moving by `g`. -/
theorem frame_smul (g g₀ : isom d) (A : Set (Minkowski d)) :
    (g₀ * g⁻¹) • (g • A) = g₀ • A := by
  rw [smul_smul, inv_mul_cancel_right]

theorem smul_achronal
    (hG : ∀ g : isom d, StrongMorphism (minkowski d) (minkowski d) fun p => g • p)
    {V : Opens (Minkowski d)} {S : Set (Minkowski d)}
    (h : ∀ p ∈ S, ∀ q ∈ S, ¬ (minkowski d).lt V p q) (g : isom d) :
    ∀ p ∈ g • S, ∀ q ∈ g • S, ¬ (minkowski d).lt (smulOpens g V) p q := by
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ hpq
  exact h p hp q hq ((smul_rel_iff hG g V p q).2.1 hpq)

/-- **(b) Isometries map achronal Lipschitz hypersurfaces of `V` to those of `g V`.** The
hypothesis `hG` is `IsomCausal.isom_strongMorphism` (not importable in this wave); it is used only
for the achronality field. -/
theorem IsLipschitzHypersurfaceIn.smul
    (hG : ∀ g : isom d, StrongMorphism (minkowski d) (minkowski d) fun p => g • p)
    {V : Opens (Minkowski d)} {S : Set (Minkowski d)} (h : IsLipschitzHypersurfaceIn V S)
    (g : isom d) : IsLipschitzHypersurfaceIn (smulOpens g V) (g • S) := by
  refine ⟨?_, smul_achronal hG h.achronal g, ?_⟩
  · rw [coe_smulOpens]; exact Set.smul_set_mono h.subset
  · rintro _ ⟨p, hp, rfl⟩
    obtain ⟨g₀, O, U, f, hpO, hOV, hU, hf, hgr⟩ := h.locGraph p hp
    refine ⟨g₀ * g⁻¹, smulOpens g O, U, f, ⟨p, hpO, rfl⟩,
      fun x hx => by
        rw [← SetLike.mem_coe, coe_smulOpens] at hx ⊢; exact Set.smul_set_mono hOV hx, hU, hf, ?_⟩
    rw [coe_smulOpens, ← smul_set_inter, frame_smul, frame_smul, hgr]

/-- **(b), spacelike form.** -/
theorem IsSpacelikeLipschitzIn.smul
    (hG : ∀ g : isom d, StrongMorphism (minkowski d) (minkowski d) fun p => g • p)
    {V : Opens (Minkowski d)} {S : Set (Minkowski d)} (h : IsSpacelikeLipschitzIn V S)
    (g : isom d) : IsSpacelikeLipschitzIn (smulOpens g V) (g • S) := by
  refine ⟨?_, smul_achronal hG h.achronal g, ?_⟩
  · rw [coe_smulOpens]; exact Set.smul_set_mono h.subset
  · rintro _ ⟨p, hp, rfl⟩
    obtain ⟨g₀, O, U, f, c, hc, hpO, hOV, hU, hf, hgr⟩ := h.locGraph p hp
    refine ⟨g₀ * g⁻¹, smulOpens g O, U, f, c, hc, ⟨p, hpO, rfl⟩,
      fun x hx => by
        rw [← SetLike.mem_coe, coe_smulOpens] at hx ⊢; exact Set.smul_set_mono hOV hx, hU, hf, ?_⟩
    rw [coe_smulOpens, ← smul_set_inter, frame_smul, frame_smul, hgr]

/-! ### The Lorentzian length of a curve -/

/-- **The Lorentzian length** `∫_{(a,b]} √(minkQ γ'(t)) dt` of a curve `γ : ℝ → 𝐌ⁿ`. -/
noncomputable def lorentzLength (γ : ℝ → Minkowski d) (a b : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioc a b, ENNReal.ofReal (Real.sqrt (minkQ (deriv γ t)))

theorem lorentzLength_of_le {γ : ℝ → Minkowski d} {a b : ℝ} (h : b ≤ a) :
    lorentzLength γ a b = 0 := by
  simp [lorentzLength, Ioc_eq_empty (not_lt.2 h)]

theorem lorentzLength_add {γ : ℝ → Minkowski d} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    lorentzLength γ a c = lorentzLength γ a b + lorentzLength γ b c := by
  rw [lorentzLength, ← Ioc_union_Ioc_eq_Ioc hab hbc, lintegral_union measurableSet_Ioc]
  · rfl
  · exact Set.disjoint_left.2 fun t ht ht' => (not_lt.2 ht.2) ht'.1

theorem lorentzLength_mono {γ : ℝ → Minkowski d} {a b a' b' : ℝ} (ha : a ≤ a') (hb : b' ≤ b) :
    lorentzLength γ a' b' ≤ lorentzLength γ a b :=
  lintegral_mono_set (Ioc_subset_Ioc ha hb)

/-- The derivative only sees the curve on an open interval. -/
theorem deriv_eq_of_eqOn_Ioo {γ γ' : ℝ → Minkowski d} {a b t : ℝ} (h : EqOn γ γ' (Ioo a b))
    (ht : t ∈ Ioo a b) : deriv γ t = deriv γ' t :=
  Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem (Ioo_mem_nhds ht.1 ht.2) h)

theorem lorentzLength_congr {γ γ' : ℝ → Minkowski d} {a b : ℝ} (h : EqOn γ γ' (Ioo a b)) :
    lorentzLength γ a b = lorentzLength γ' a b := by
  unfold lorentzLength
  rw [setLIntegral_congr Ioo_ae_eq_Ioc.symm, setLIntegral_congr Ioo_ae_eq_Ioc.symm]
  refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  simp only [deriv_eq_of_eqOn_Ioo h ht]

theorem lorentzLength_const (p : Minkowski d) (a b : ℝ) :
    lorentzLength (fun _ => p) a b = 0 := by
  simp [lorentzLength]

/-- The derivative of `g ∘ γ` is the linear part of `g` applied to that of `γ`, at every point
(both sides vanish where `γ` is not differentiable). -/
theorem deriv_isom_comp (g : isom d) (γ : ℝ → Minkowski d) (t : ℝ) :
    deriv (fun s => g • γ s) t = (g : Minkowski d ≃ᵃ[ℝ] Minkowski d).linear (deriv γ t) := by
  set A := (g : Minkowski d ≃ᵃ[ℝ] Minkowski d)
  set L : Minkowski d ≃L[ℝ] Minkowski d := A.linear.toContinuousLinearEquiv
  have hA : (fun s => g • γ s) = fun s => L (γ s) + A 0 := by
    funext s
    have := congrFun A.toAffineMap.decomp (γ s)
    simpa [isom_smul_def, A, L] using this
  rw [hA, deriv_add_const]
  by_cases hγ : DifferentiableAt ℝ γ t
  · exact (L.hasFDerivAt.comp_hasDerivAt t hγ.hasDerivAt).deriv
  · have h' : ¬ DifferentiableAt ℝ (fun s => L (γ s)) t := fun h =>
      hγ ((L.comp_differentiableAt_iff (f := γ)).1 h)
    rw [deriv_zero_of_not_differentiableAt h', deriv_zero_of_not_differentiableAt hγ, map_zero]

theorem lorentzLength_isom (g : isom d) (γ : ℝ → Minkowski d) (a b : ℝ) :
    lorentzLength (fun t => g • γ t) a b = lorentzLength γ a b := by
  unfold lorentzLength
  congr 1
  funext t
  rw [deriv_isom_comp, show ((g : Minkowski d ≃ᵃ[ℝ] Minkowski d).linear (deriv γ t)) =
    (linearPart g : Minkowski d ≃ₗ[ℝ] Minkowski d) (deriv γ t) from rfl,
    lorentz.minkQ_apply (linearPart g).2]

/-- `√(minkQ (c • v)) = |c| √(minkQ v)`. -/
theorem sqrt_minkQ_smul (c : ℝ) (v : Minkowski d) :
    Real.sqrt (minkQ (c • v)) = |c| * Real.sqrt (minkQ v) := by
  rw [minkQ_smul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

theorem lorentzLength_eq_Icc (γ : ℝ → Minkowski d) (a b : ℝ) :
    lorentzLength γ a b = ∫⁻ t in Icc a b, ENNReal.ofReal (Real.sqrt (minkQ (deriv γ t))) :=
  setLIntegral_congr Ioc_ae_eq_Icc

theorem lorentzLength_comp_affine (γ : ℝ → Minkowski d) {c : ℝ} (hc : 0 < c) (e a b : ℝ) :
    lorentzLength (fun s => γ (c * s + e)) a b = lorentzLength γ (c * a + e) (c * b + e) := by
  rw [lorentzLength_eq_Icc, lorentzLength_eq_Icc, ← image_affine_Icc' hc e a b,
    lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Icc (f := fun x => c * x + e)
      (f' := fun _ => c)
      (fun s _ => (((hasDerivAt_id' s).const_mul c).add_const e).hasDerivWithinAt.congr_deriv
        (mul_one c))
      ((strictMono_mul_left_of_pos hc).add_const e).injective.injOn]
  refine setLIntegral_congr_fun measurableSet_Icc fun s _ => ?_
  have hd : deriv (fun s => γ (c * s + e)) s = c • deriv γ (c * s + e) := by
    have := deriv_comp_mul_left c (fun y => γ (y + e)) s
    simp only [deriv_comp_add_const] at this
    exact this
  simp only [hd, sqrt_minkQ_smul, abs_of_pos hc]
  rw [ENNReal.ofReal_mul hc.le]

theorem lorentzLength_comp_const_sub (γ : ℝ → Minkowski d) (e a b : ℝ) :
    lorentzLength (fun s => γ (e - s)) a b = lorentzLength γ (e - b) (e - a) := by
  rw [lorentzLength_eq_Icc, lorentzLength_eq_Icc, ← image_const_sub_Icc,
    lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Icc (f := fun x => e - x)
      (f' := fun _ => -1)
      (fun s _ => ((hasDerivAt_id' s).const_sub e).hasDerivWithinAt)
      (sub_right_injective).injOn]
  refine setLIntegral_congr_fun measurableSet_Icc fun s _ => ?_
  simp [deriv_comp_const_sub]

/-- `√(minkQ v) ≤ ‖v.2‖`. -/
theorem sqrt_minkQ_le (v : Minkowski d) : Real.sqrt (minkQ v) ≤ ‖v.2‖ := by
  rw [← Real.sqrt_sq (norm_nonneg v.2)]
  exact Real.sqrt_le_sqrt (by unfold minkQ; nlinarith [sq_nonneg v.1])

theorem lorentzLength_le_of_lipschitzWith {γ : ℝ → Minkowski d} {K : ℝ≥0}
    (hγ : LipschitzWith K γ) (a b : ℝ) :
    lorentzLength γ a b ≤ ENNReal.ofReal (K * (b - a)) := by
  rcases le_or_gt b a with hab | hab
  · rw [lorentzLength_of_le hab]; exact bot_le
  calc lorentzLength γ a b ≤ ∫⁻ _ in Ioc a b, ENNReal.ofReal K := by
        refine lintegral_mono fun t => ENNReal.ofReal_le_ofReal ?_
        exact (sqrt_minkQ_le _).trans ((norm_snd_le _).trans (norm_deriv_le_of_lipschitz hγ))
    _ = ENNReal.ofReal (K * (b - a)) := by
        rw [setLIntegral_const, Real.volume_Ioc]
        exact (ENNReal.ofReal_mul (NNReal.coe_nonneg K)).symm

/-! ### Curves in a set, and their length -/

/-- A curve `I → X`, extended constantly to `ℝ`, as a curve of `𝐌ⁿ`. -/
noncomputable def curveExtend {X : Set (Minkowski d)} (γ : C(I, X)) : ℝ → Minkowski d :=
  IccExtend zero_le_one fun t => (γ t : Minkowski d)

/-- A Lipschitz curve. -/
def IsLipschitzCurve {X : Set (Minkowski d)} (γ : C(I, X)) : Prop :=
  ∃ K : ℝ≥0, LipschitzWith K (curveExtend γ)

/-- **The length of a curve of `Σ ∩ V`**: the Lorentzian length of its extension if the curve is
Lipschitz, `⊤` otherwise. The restriction is necessary, not cosmetic: a continuous curve that is
not absolutely continuous (a Cantor-staircase reparametrisation) has derivative `0` a.e., hence
`lorentzLength 0`, between distinct points; and it loses nothing, since every rectifiable curve
has a Lipschitz reparametrisation, so `⊤` never changes an infimum that matters. (That last
sentence is an informal remark, not proved here; nothing downstream depends on it.) -/
noncomputable def lengthOn (S : Set (Minkowski d)) (V : Opens (Minkowski d))
    (γ : C(I, ↥(S ∩ (V : Set (Minkowski d))))) : ℝ≥0∞ := by
  classical exact if IsLipschitzCurve γ then lorentzLength (curveExtend γ) 0 1 else ⊤

theorem curveExtend_eq_of_forall {X X' : Set (Minkowski d)} {γ : C(I, X)} {γ' : C(I, X')}
    (h : ∀ t, (γ t : Minkowski d) = γ' t) : curveExtend γ = curveExtend γ' :=
  funext fun t => by simp only [curveExtend, IccExtend, Function.comp_apply, h]

/-- **(c) The length depends only on the curve**, not on the set it is read in: two curves with
the same points of `𝐌ⁿ` have the same length, whatever `Σ, V` and `Σ', V'` they are read in. -/
theorem lengthOn_congr {S S' : Set (Minkowski d)} {V V' : Opens (Minkowski d)}
    (γ : C(I, ↥(S ∩ (V : Set (Minkowski d))))) (γ' : C(I, ↥(S' ∩ (V' : Set (Minkowski d)))))
    (h : ∀ t, (γ t : Minkowski d) = γ' t) : lengthOn S V γ = lengthOn S' V' γ' := by
  unfold lengthOn IsLipschitzCurve; rw [curveExtend_eq_of_forall h]

theorem lengthOn_of_isLipschitzCurve {S : Set (Minkowski d)} {V : Opens (Minkowski d)}
    {γ : C(I, ↥(S ∩ (V : Set (Minkowski d))))} (hγ : IsLipschitzCurve γ) :
    lengthOn S V γ = lorentzLength (curveExtend γ) 0 1 := by
  simp [lengthOn, hγ]

theorem lengthOn_of_not_isLipschitzCurve {S : Set (Minkowski d)} {V : Opens (Minkowski d)}
    {γ : C(I, ↥(S ∩ (V : Set (Minkowski d))))} (hγ : ¬ IsLipschitzCurve γ) :
    lengthOn S V γ = ⊤ := by
  simp [lengthOn, hγ]

/-- Gluing two `K`-Lipschitz maps of `ℝ` that agree at `b`. -/
theorem lipschitzWith_piecewise_le {X : Type*} [PseudoMetricSpace X] {f g : ℝ → X} {K : ℝ≥0}
    {b : ℝ} (hf : LipschitzWith K f) (hg : LipschitzWith K g) (hb : f b = g b) :
    LipschitzWith K fun t => if t ≤ b then f t else g t := by
  have key : ∀ s t, s ≤ b → b < t → dist (f s) (g t) ≤ K * dist s t := fun s t hs ht => by
    calc dist (f s) (g t) ≤ dist (f s) (f b) + dist (g b) (g t) := by
          rw [hb]; exact dist_triangle _ _ _
      _ ≤ K * dist s b + K * dist b t := add_le_add (hf.dist_le_mul _ _) (hg.dist_le_mul _ _)
      _ = K * dist s t := by
          rw [Real.dist_eq, Real.dist_eq, Real.dist_eq, abs_of_nonpos (by linarith),
            abs_of_neg (by linarith), abs_of_neg (by linarith)]; ring
  refine LipschitzWith.of_dist_le_mul fun s t => ?_
  by_cases hs : s ≤ b <;> by_cases ht : t ≤ b <;> simp only [hs, ht, if_true, if_false]
  · exact hf.dist_le_mul _ _
  · exact key s t hs (not_le.1 ht)
  · rw [dist_comm, dist_comm s]; exact key t s ht (not_le.1 hs)
  · exact hg.dist_le_mul _ _

theorem lipschitzWith_affine (c e : ℝ) : LipschitzWith ‖c‖₊ fun t : ℝ => c * t + e :=
  LipschitzWith.of_dist_le_mul fun s t => by
    rw [Real.dist_eq, Real.dist_eq, coe_nnnorm, Real.norm_eq_abs, ← abs_mul]
    exact le_of_eq (by ring_nf)

/-! ### Paths of `Σ ∩ V`: the constant, the reverse, the concatenation -/

section Paths

variable {S : Set (Minkowski d)} {V : Opens (Minkowski d)} {x y z : ↥(S ∩ (V : Set (Minkowski d)))}

theorem curveExtend_path (γ : Path x y) :
    curveExtend γ.toContinuousMap = fun t => ((γ.extend t : ↥(S ∩ (V : Set (Minkowski d)))) :
      Minkowski d) := rfl

theorem lengthOn_refl (x : ↥(S ∩ (V : Set (Minkowski d)))) :
    lengthOn S V (Path.refl x).toContinuousMap = 0 := by
  have h : curveExtend (Path.refl x).toContinuousMap = fun _ => (x : Minkowski d) := by
    rw [curveExtend_path, Path.refl_extend]; rfl
  rw [lengthOn_of_isLipschitzCurve ⟨0, by rw [h]; exact LipschitzWith.const _⟩, h,
    lorentzLength_const]

theorem curveExtend_symm (γ : Path x y) :
    curveExtend γ.symm.toContinuousMap = fun t => curveExtend γ.toContinuousMap (1 - t) := by
  rw [curveExtend_path, curveExtend_path, Path.extend_symm]

theorem isLipschitzCurve_symm {γ : Path x y} (hγ : IsLipschitzCurve γ.toContinuousMap) :
    IsLipschitzCurve γ.symm.toContinuousMap := by
  obtain ⟨K, hK⟩ := hγ
  refine ⟨K * ‖(-1 : ℝ)‖₊, ?_⟩
  rw [curveExtend_symm]
  have := hK.comp (lipschitzWith_affine (-1) 1)
  convert this using 2 with t
  simp only [Function.comp_apply]; ring_nf

theorem lengthOn_symm (γ : Path x y) :
    lengthOn S V γ.symm.toContinuousMap = lengthOn S V γ.toContinuousMap := by
  by_cases hγ : IsLipschitzCurve γ.toContinuousMap
  · rw [lengthOn_of_isLipschitzCurve hγ, lengthOn_of_isLipschitzCurve (isLipschitzCurve_symm hγ),
      curveExtend_symm, lorentzLength_comp_const_sub]
    norm_num
  · have h' : ¬ IsLipschitzCurve γ.symm.toContinuousMap := fun h =>
      hγ (by simpa using isLipschitzCurve_symm h)
    rw [lengthOn_of_not_isLipschitzCurve hγ, lengthOn_of_not_isLipschitzCurve h']

theorem curveExtend_trans (γ₁ : Path x y) (γ₂ : Path y z) :
    curveExtend (γ₁.trans γ₂).toContinuousMap = fun t => if t ≤ 1 / 2 then
      curveExtend γ₁.toContinuousMap (2 * t + 0) else curveExtend γ₂.toContinuousMap (2 * t + -1) := by
  funext t
  rw [curveExtend_path, curveExtend_path, curveExtend_path]
  dsimp only
  split_ifs with ht
  · rw [Path.extend_trans_of_le_half _ _ ht, add_zero]
  · rw [Path.extend_trans_of_half_le _ _ (not_le.1 ht).le, ← sub_eq_add_neg]

/-- **(c) Additivity under concatenation**: the concatenation of two Lipschitz curves is
Lipschitz, and its length is the sum. -/
theorem lengthOn_trans {γ₁ : Path x y} {γ₂ : Path y z} (h₁ : IsLipschitzCurve γ₁.toContinuousMap)
    (h₂ : IsLipschitzCurve γ₂.toContinuousMap) :
    IsLipschitzCurve (γ₁.trans γ₂).toContinuousMap ∧ lengthOn S V (γ₁.trans γ₂).toContinuousMap =
      lengthOn S V γ₁.toContinuousMap + lengthOn S V γ₂.toContinuousMap := by
  obtain ⟨K₁, hK₁⟩ := h₁
  obtain ⟨K₂, hK₂⟩ := h₂
  have hL₁ := (hK₁.comp (lipschitzWith_affine 2 0)).weaken
    (le_max_left (K₁ * ‖(2 : ℝ)‖₊) (K₂ * ‖(2 : ℝ)‖₊))
  have hL₂ := (hK₂.comp (lipschitzWith_affine 2 (-1))).weaken
    (le_max_right (K₁ * ‖(2 : ℝ)‖₊) (K₂ * ‖(2 : ℝ)‖₊))
  have hb : (curveExtend γ₁.toContinuousMap ∘ fun t => 2 * t + 0) (1 / 2) =
      (curveExtend γ₂.toContinuousMap ∘ fun t => 2 * t + -1) (1 / 2) := by
    simp only [Function.comp_apply, curveExtend_path]; norm_num
  have hT : IsLipschitzCurve (γ₁.trans γ₂).toContinuousMap :=
    ⟨_, by rw [curveExtend_trans]; exact lipschitzWith_piecewise_le hL₁ hL₂ hb⟩
  refine ⟨hT, ?_⟩
  rw [lengthOn_of_isLipschitzCurve hT, lengthOn_of_isLipschitzCurve ⟨K₁, hK₁⟩,
    lengthOn_of_isLipschitzCurve ⟨K₂, hK₂⟩, lorentzLength_add (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 1)]
  congr 1
  · rw [lorentzLength_congr (γ' := fun t => curveExtend γ₁.toContinuousMap (2 * t + 0))
      (fun t ht => by rw [curveExtend_trans]; exact if_pos ht.2.le),
      lorentzLength_comp_affine _ two_pos]
    norm_num
  · rw [lorentzLength_congr (γ' := fun t => curveExtend γ₂.toContinuousMap (2 * t + -1))
      (fun t ht => by rw [curveExtend_trans]; exact if_neg (not_le.2 ht.1)),
      lorentzLength_comp_affine _ two_pos]
    norm_num

theorem lengthOn_trans_le (γ₁ : Path x y) (γ₂ : Path y z) :
    lengthOn S V (γ₁.trans γ₂).toContinuousMap ≤
      lengthOn S V γ₁.toContinuousMap + lengthOn S V γ₂.toContinuousMap := by
  by_cases h₁ : IsLipschitzCurve γ₁.toContinuousMap
  swap; · rw [lengthOn_of_not_isLipschitzCurve h₁, top_add]; exact le_top
  by_cases h₂ : IsLipschitzCurve γ₂.toContinuousMap
  swap; · rw [lengthOn_of_not_isLipschitzCurve h₂, add_top]; exact le_top
  exact (lengthOn_trans h₁ h₂).2.le

end Paths

/-! ### The induced length space -/

/-- **`Σ ∩ V` with its induced length pseudo-metric** (a type synonym: its topology is the one of
the pseudo-metric, not the subspace topology). -/
def InducedLength (S : Set (Minkowski d)) (V : Opens (Minkowski d)) : Type :=
  ↥(S ∩ (V : Set (Minkowski d)))

namespace InducedLength

variable {S : Set (Minkowski d)} {V : Opens (Minkowski d)}

/-- The identity, from the length space to the subspace. -/
def toSubtype : InducedLength S V ≃ ↥(S ∩ (V : Set (Minkowski d))) := Equiv.refl _

/-- The induced (pseudo-)distance: the infimum of the lengths of the paths. -/
noncomputable def lengthDist (x y : ↥(S ∩ (V : Set (Minkowski d)))) : ℝ≥0∞ :=
  ⨅ γ : Path x y, lengthOn S V γ.toContinuousMap

theorem lengthDist_le (x y : ↥(S ∩ (V : Set (Minkowski d)))) (γ : Path x y) :
    lengthDist x y ≤ lengthOn S V γ.toContinuousMap :=
  iInf_le _ γ

end InducedLength

open InducedLength in
/-- **(e) The induced pseudo-emetric**: `edist x y = ⨅ γ, lengthOn Σ V γ` over the paths of
`Σ ∩ V` (subspace topology) from `x` to `y`. -/
noncomputable instance (S : Set (Minkowski d)) (V : Opens (Minkowski d)) :
    PseudoEMetricSpace (InducedLength S V) where
  edist x y := lengthDist (toSubtype x) (toSubtype y)
  edist_self x := le_antisymm ((lengthDist_le _ _ (Path.refl _)).trans_eq (lengthOn_refl _))
    bot_le
  edist_comm x y := le_antisymm
    (le_iInf fun γ => (lengthDist_le _ _ γ.symm).trans_eq (lengthOn_symm γ))
    (le_iInf fun γ => (lengthDist_le _ _ γ.symm).trans_eq (lengthOn_symm γ))
  edist_triangle x y z := ENNReal.le_iInf_add_iInf fun γ₁ γ₂ =>
    (lengthDist_le _ _ (γ₁.trans γ₂)).trans (lengthOn_trans_le γ₁ γ₂)

namespace InducedLength

variable {S : Set (Minkowski d)} {V : Opens (Minkowski d)}

theorem edist_def (x y : InducedLength S V) :
    edist x y = ⨅ γ : Path (toSubtype x) (toSubtype y), lengthOn S V γ.toContinuousMap := rfl

theorem edist_le_lengthOn (x y : InducedLength S V) (γ : Path (toSubtype x) (toSubtype y)) :
    edist x y ≤ lengthOn S V γ.toContinuousMap :=
  lengthDist_le _ _ γ

end InducedLength

/-! ### (b) Isometries preserve lengths; (c) inclusions do not increase distances -/

/-- An isometry is Lipschitz for the norm of `Minkowski d`. -/
theorem isom_lipschitzWith (g : isom d) : ∃ K : ℝ≥0, LipschitzWith K fun z : Minkowski d => g • z := by
  set A := (g : Minkowski d ≃ᵃ[ℝ] Minkowski d)
  set L : Minkowski d ≃L[ℝ] Minkowski d := A.linear.toContinuousLinearEquiv
  refine ⟨‖(L : Minkowski d →L[ℝ] Minkowski d)‖₊, LipschitzWith.of_dist_le_mul fun z w => ?_⟩
  rw [dist_eq_norm, dist_eq_norm, isom_smul_def, isom_smul_def, isom_sub]
  exact (L : Minkowski d →L[ℝ] Minkowski d).le_opNorm (z - w)

/-- The image `g ∘ γ` of a curve, read in any set `Y` containing it. -/
noncomputable def curveSMul (g : isom d) {X Y : Set (Minkowski d)} (γ : C(I, X))
    (h : ∀ t, g • (γ t : Minkowski d) ∈ Y) : C(I, Y) :=
  ⟨fun t => ⟨g • (γ t : Minkowski d), h t⟩,
    ((continuous_subtype_val.comp γ.continuous).const_smul g).subtype_mk _⟩

theorem curveExtend_curveSMul (g : isom d) {X Y : Set (Minkowski d)} (γ : C(I, X))
    (h : ∀ t, g • (γ t : Minkowski d) ∈ Y) :
    curveExtend (curveSMul g γ h) = fun t => g • curveExtend γ t := rfl

theorem isLipschitzCurve_curveSMul_iff (g : isom d) {X Y : Set (Minkowski d)} (γ : C(I, X))
    (h : ∀ t, g • (γ t : Minkowski d) ∈ Y) :
    IsLipschitzCurve (curveSMul g γ h) ↔ IsLipschitzCurve γ := by
  constructor
  · rintro ⟨K, hK⟩
    obtain ⟨K', hK'⟩ := isom_lipschitzWith g⁻¹
    refine ⟨K' * K, ?_⟩
    have := hK'.comp hK
    rw [curveExtend_curveSMul] at this
    simpa [Function.comp_def] using this
  · rintro ⟨K, hK⟩
    obtain ⟨K', hK'⟩ := isom_lipschitzWith g
    exact ⟨K' * K, by rw [curveExtend_curveSMul]; exact hK'.comp hK⟩

/-- **(b) An isometry preserves the length of curves**: the image of a curve of `Σ ∩ V`, read in
any `Σ' ∩ V'` containing it (e.g. `g Σ ∩ g V`), has the same length. -/
theorem lengthOn_curveSMul (g : isom d) {S S' : Set (Minkowski d)} {V V' : Opens (Minkowski d)}
    (γ : C(I, ↥(S ∩ (V : Set (Minkowski d)))))
    (h : ∀ t, g • (γ t : Minkowski d) ∈ S' ∩ (V' : Set (Minkowski d))) :
    lengthOn S' V' (curveSMul g γ h) = lengthOn S V γ := by
  by_cases hγ : IsLipschitzCurve γ
  · rw [lengthOn_of_isLipschitzCurve hγ, lengthOn_of_isLipschitzCurve
      ((isLipschitzCurve_curveSMul_iff g γ h).2 hγ), curveExtend_curveSMul, lorentzLength_isom]
  · rw [lengthOn_of_not_isLipschitzCurve hγ, lengthOn_of_not_isLipschitzCurve
      (mt (isLipschitzCurve_curveSMul_iff g γ h).1 hγ)]

/-- The image of a path under an isometry. -/
noncomputable def pathSMul (g : isom d) {X Y : Set (Minkowski d)} {x y : X} {x' y' : Y}
    (γ : Path x y) (h : ∀ t, g • (γ t : Minkowski d) ∈ Y)
    (hx : g • (x : Minkowski d) = x') (hy : g • (y : Minkowski d) = y') : Path x' y' where
  toContinuousMap := curveSMul g γ.toContinuousMap h
  source' := Subtype.ext (by simp [curveSMul, hx])
  target' := Subtype.ext (by simp [curveSMul, hy])

namespace InducedLength

variable {S : Set (Minkowski d)} {V : Opens (Minkowski d)}

theorem smul_mem (g : isom d) (x : ↥(S ∩ (V : Set (Minkowski d)))) :
    g • (x : Minkowski d) ∈ g • S ∩ (smulOpens g V : Set (Minkowski d)) :=
  ⟨Set.smul_mem_smul_set x.2.1, by rw [coe_smulOpens]; exact Set.smul_mem_smul_set x.2.2⟩

/-- The action of `g` from `Σ ∩ V` to `g Σ ∩ g V`. -/
noncomputable def smulMap (g : isom d) (x : InducedLength S V) :
    InducedLength (g • S) (smulOpens g V) :=
  toSubtype.symm ⟨g • (toSubtype x : Minkowski d), smul_mem g (toSubtype x)⟩

theorem inv_smul_mem (g : isom d) (z : ↥(g • S ∩ (smulOpens g V : Set (Minkowski d)))) :
    g⁻¹ • (z : Minkowski d) ∈ S ∩ (V : Set (Minkowski d)) := by
  obtain ⟨a, ha, haz⟩ := z.2.1
  obtain ⟨b, hb, hbz⟩ : (z : Minkowski d) ∈ (fun p => g • p) '' (V : Set (Minkowski d)) := z.2.2
  refine ⟨?_, ?_⟩
  · rw [← haz, inv_smul_smul]; exact ha
  · rw [← hbz, inv_smul_smul]; exact hb

/-- **(b) An isometry is an isometry of the induced length spaces**,
`Σ ∩ V → g Σ ∩ g V`. -/
theorem edist_smulMap (g : isom d) (x y : InducedLength S V) :
    edist (smulMap g x) (smulMap g y) = edist x y := by
  refine le_antisymm (le_iInf fun γ => ?_) (le_iInf fun δ => ?_)
  · refine (edist_le_lengthOn _ _ (pathSMul g γ (fun t => smul_mem g (γ t)) rfl rfl)).trans_eq ?_
    exact lengthOn_curveSMul g _ _
  · refine (edist_le_lengthOn _ _ (pathSMul g⁻¹ δ (fun t => inv_smul_mem g (δ t))
      (inv_smul_smul g _) (inv_smul_smul g _))).trans_eq ?_
    exact lengthOn_curveSMul g⁻¹ _ _

/-- The inclusion `Σ ∩ V ⊆ Σ' ∩ V'`. -/
def inclusion {S' : Set (Minkowski d)} {V' : Opens (Minkowski d)}
    (h : S ∩ (V : Set (Minkowski d)) ⊆ S' ∩ (V' : Set (Minkowski d))) (x : InducedLength S V) :
    InducedLength S' V' :=
  toSubtype.symm ⟨toSubtype x, h (toSubtype x).2⟩

/-- **(c) Locality, metric form**: distances measured in a larger chart are no larger — the
inclusion `Σ ∩ V ⊆ Σ' ∩ V'` is `1`-Lipschitz for the induced lengths. -/
theorem edist_inclusion_le {S' : Set (Minkowski d)} {V' : Opens (Minkowski d)}
    (h : S ∩ (V : Set (Minkowski d)) ⊆ S' ∩ (V' : Set (Minkowski d))) (x y : InducedLength S V) :
    edist (inclusion h x) (inclusion h y) ≤ edist x y := by
  refine le_iInf fun γ => ?_
  let γ' : Path (toSubtype (inclusion h x)) (toSubtype (inclusion h y)) :=
    { toFun := fun t => ⟨γ t, h (γ t).2⟩
      continuous_toFun := (continuous_subtype_val.comp γ.continuous).subtype_mk _
      source' := Subtype.ext (by simp only [Path.source]; rfl)
      target' := Subtype.ext (by simp only [Path.target]; rfl) }
  exact (edist_le_lengthOn _ _ γ').trans_eq (lengthOn_congr _ _ fun t => rfl)

end InducedLength

/-! ### (d) The specialisation theorem -/

/-- **The Lorentzian length of a Lipschitz curve is the classical integral** `∫ₐᵇ √(minkQ γ')`. -/
theorem lorentzLength_eq_ofReal_integral {γ : ℝ → Minkowski d} {K : ℝ≥0}
    (hγ : LipschitzWith K γ) {a b : ℝ} (hab : a ≤ b) :
    lorentzLength γ a b = ENNReal.ofReal (∫ t in a..b, Real.sqrt (minkQ (deriv γ t))) := by
  rw [intervalIntegral.integral_of_le hab, ofReal_integral_eq_lintegral_ofReal]
  · rfl
  · refine Integrable.mono' (g := fun _ => (K : ℝ)) (integrableOn_const (by simp)) ?_ ?_
    · exact (Real.continuous_sqrt.measurable.comp
        (continuous_minkQ.measurable.comp (measurable_deriv γ))).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun t => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact (sqrt_minkQ_le _).trans ((norm_snd_le _).trans (norm_deriv_le_of_lipschitz hγ))
  · exact Filter.Eventually.of_forall fun t => Real.sqrt_nonneg _

/-- **(d) The specialisation theorem, for every Lipschitz curve of `Σ ∩ V`**: its length is the
classical `∫₀¹ √(minkQ γ'(t)) dt`. -/
theorem lengthOn_eq_integral {S : Set (Minkowski d)} {V : Opens (Minkowski d)}
    {γ : C(I, ↥(S ∩ (V : Set (Minkowski d))))} (hγ : IsLipschitzCurve γ) :
    lengthOn S V γ =
      ENNReal.ofReal (∫ t in (0 : ℝ)..1, Real.sqrt (minkQ (deriv (curveExtend γ) t))) := by
  obtain ⟨K, hK⟩ := hγ
  rw [lengthOn_of_isLipschitzCurve ⟨K, hK⟩, lorentzLength_eq_ofReal_integral hK zero_le_one]

/-- Gluing two `K`-Lipschitz pieces over adjacent closed intervals. -/
theorem LipschitzOnWith.Icc_union_Icc {X : Type*} [PseudoMetricSpace X] {f : ℝ → X} {K : ℝ≥0}
    {a b c : ℝ} (h₁ : LipschitzOnWith K f (Icc a b)) (h₂ : LipschitzOnWith K f (Icc b c))
    (hab : a ≤ b) (hbc : b ≤ c) : LipschitzOnWith K f (Icc a c) := by
  have key : ∀ s ∈ Icc a b, ∀ t ∈ Icc b c, dist (f s) (f t) ≤ K * dist s t := fun s hs t ht => by
    have hb₁ : b ∈ Icc a b := ⟨hab, le_rfl⟩
    have hb₂ : b ∈ Icc b c := ⟨le_rfl, hbc⟩
    calc dist (f s) (f t) ≤ dist (f s) (f b) + dist (f b) (f t) := dist_triangle _ _ _
      _ ≤ K * dist s b + K * dist b t :=
          add_le_add (h₁.dist_le_mul s hs b hb₁) (h₂.dist_le_mul b hb₂ t ht)
      _ = K * dist s t := by
          rw [Real.dist_eq, Real.dist_eq, Real.dist_eq, abs_of_nonpos (by linarith [hs.2]),
            abs_of_nonpos (by linarith [ht.1]), abs_of_nonpos (by linarith [hs.2, ht.1])]; ring
  refine LipschitzOnWith.of_dist_le_mul fun s hs t ht => ?_
  by_cases hsb : s ≤ b <;> by_cases htb : t ≤ b
  · exact h₁.dist_le_mul s ⟨hs.1, hsb⟩ t ⟨ht.1, htb⟩
  · exact key s ⟨hs.1, hsb⟩ t ⟨(not_le.1 htb).le, ht.2⟩
  · rw [dist_comm, dist_comm s]; exact key t ⟨ht.1, htb⟩ s ⟨(not_le.1 hsb).le, hs.2⟩
  · exact h₂.dist_le_mul s ⟨(not_le.1 hsb).le, hs.2⟩ t ⟨(not_le.1 htb).le, ht.2⟩

/-- **A piecewise `C¹` curve on `[a, b]`**: a subdivision `a = τ₀ ≤ τ₁ ≤ ⋯ ≤ τₙ = b` such that
`γ` is `C¹` on each closed piece `[τᵢ, τᵢ₊₁]` (one-sided derivatives at the break points). -/
def IsPiecewiseC1On (γ : ℝ → Minkowski d) (a b : ℝ) : Prop :=
  ∃ (n : ℕ) (τ : ℕ → ℝ), τ 0 = a ∧ τ n = b ∧
    ∀ i < n, τ i ≤ τ (i + 1) ∧ ContDiffOn ℝ 1 γ (Icc (τ i) (τ (i + 1)))

/-- A piecewise `C¹` curve is Lipschitz on its interval. -/
theorem IsPiecewiseC1On.exists_lipschitzOnWith {γ : ℝ → Minkowski d} {a b : ℝ}
    (h : IsPiecewiseC1On γ a b) : ∃ K : ℝ≥0, LipschitzOnWith K γ (Icc a b) := by
  obtain ⟨n, τ, h0, hn, hτ⟩ := h
  suffices ∀ k ≤ n, τ 0 ≤ τ k ∧ ∃ K : ℝ≥0, LipschitzOnWith K γ (Icc (τ 0) (τ k)) by
    obtain ⟨-, K, hK⟩ := this n le_rfl
    exact ⟨K, by rw [← h0, ← hn]; exact hK⟩
  intro k
  induction k with
  | zero =>
    refine fun _ => ⟨le_rfl, 0, LipschitzOnWith.of_dist_le_mul fun s hs t ht => ?_⟩
    rw [show s = t by linarith [hs.1, hs.2, ht.1, ht.2], dist_self, dist_self, mul_zero]
  | succ k ih =>
    intro hk
    obtain ⟨h0k, K, hK⟩ := ih (Nat.le_of_succ_le hk)
    obtain ⟨hle, hC⟩ := hτ k hk
    obtain ⟨K', hK'⟩ := hC.exists_lipschitzOnWith one_ne_zero (convex_Icc _ _) isCompact_Icc
    exact ⟨h0k.trans hle, max K K', LipschitzOnWith.Icc_union_Icc (hK.weaken (le_max_left _ _))
      (hK'.weaken (le_max_right _ _)) h0k hle⟩

/-- A curve whose extension is Lipschitz on `[0, 1]` is a Lipschitz curve. -/
theorem isLipschitzCurve_of_lipschitzOnWith {X : Set (Minkowski d)} {γ : C(I, X)} {K : ℝ≥0}
    (h : LipschitzOnWith K (curveExtend γ) (Icc 0 1)) : IsLipschitzCurve γ := by
  refine ⟨K, LipschitzWith.of_dist_le_mul fun s t => ?_⟩
  have hp : ∀ r : ℝ, curveExtend γ r = curveExtend γ (projIcc 0 1 zero_le_one r) := fun r => by
    simp only [curveExtend, IccExtend_val]; rfl
  rw [hp s, hp t]
  calc dist _ _ ≤ K * dist (projIcc 0 1 zero_le_one s : ℝ) (projIcc 0 1 zero_le_one t) :=
        h.dist_le_mul _ (projIcc 0 1 zero_le_one s).2 _ (projIcc 0 1 zero_le_one t).2
    _ ≤ K * dist s t := by
        gcongr
        exact (LipschitzWith.projIcc zero_le_one).dist_le_mul s t |>.trans_eq (one_mul _)

/-- **(d) The specialisation theorem required by DEC-31**: for a piecewise `C¹` curve of `Σ ∩ V`,
the induced length is the classical `∫₀¹ √(minkQ γ'(t)) dt`. -/
theorem lengthOn_eq_integral_of_isPiecewiseC1On {S : Set (Minkowski d)} {V : Opens (Minkowski d)}
    {γ : C(I, ↥(S ∩ (V : Set (Minkowski d))))} (hγ : IsPiecewiseC1On (curveExtend γ) 0 1) :
    lengthOn S V γ =
      ENNReal.ofReal (∫ t in (0 : ℝ)..1, Real.sqrt (minkQ (deriv (curveExtend γ) t))) := by
  obtain ⟨K, hK⟩ := hγ.exists_lipschitzOnWith
  exact lengthOn_eq_integral (isLipschitzCurve_of_lipschitzOnWith hK)

/-- **(d), metric half of DEC-31 (`≤` only)**: the induced distance is at most the classical
length of every piecewise-`C¹` path of `Σ ∩ V`. The reverse inequality is not proved (SCOPE). -/
theorem InducedLength.edist_le_iInf_piecewiseC1 {S : Set (Minkowski d)} {V : Opens (Minkowski d)}
    (x y : InducedLength S V) :
    edist x y ≤ ⨅ (γ : Path (InducedLength.toSubtype x) (InducedLength.toSubtype y))
      (_ : IsPiecewiseC1On (curveExtend γ.toContinuousMap) 0 1),
      ENNReal.ofReal
        (∫ t in (0 : ℝ)..1, Real.sqrt (minkQ (deriv (curveExtend γ.toContinuousMap) t))) :=
  le_iInf₂ fun γ hγ =>
    (InducedLength.edist_le_lengthOn x y γ).trans_eq (lengthOn_eq_integral_of_isPiecewiseC1On hγ)

/-! ### Inhabitants: entire Lipschitz graphs -/

/-- Achronality of an entire `1`-Lipschitz graph. -/
theorem not_lt_top_of_graphOver {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : LipschitzWith 1 f)
    {p q : Minkowski d} (hp : p ∈ graphOver univ f) (hq : q ∈ graphOver univ f) :
    ¬ (minkowski d).lt ⊤ p q := by
  intro hpq
  rw [lt_top_iff_minkQ] at hpq
  have h2 : |(q - p).1| ≤ ‖(q - p).2‖ := by
    simp only [Prod.fst_sub, Prod.snd_sub]
    rw [hp.2, hq.2, ← Real.dist_eq, ← dist_eq_norm]
    simpa using hf.dist_le_mul q.2 p.2
  have h3 := hpq.2
  rw [minkQ_lt_zero_iff] at h3
  nlinarith [abs_nonneg (q - p).1, sq_abs (q - p).1, norm_nonneg (q - p).2]

/-- **An entire `1`-Lipschitz graph is an achronal Lipschitz hypersurface of `𝐌ⁿ`.** -/
theorem isLipschitzHypersurfaceIn_graphOver {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : LipschitzWith 1 f) : IsLipschitzHypersurfaceIn ⊤ (graphOver univ f) :=
  ⟨fun _ _ => trivial, fun _ hp _ hq => not_lt_top_of_graphOver hf hp hq,
    fun _ _ => ⟨1, ⊤, univ, f, trivial, le_rfl, isOpen_univ, hf.lipschitzOnWith, by simp⟩⟩

/-- **An entire `c`-Lipschitz graph, `c < 1`, is a spacelike Lipschitz hypersurface of `𝐌ⁿ`**
(the non-vacuity witness of `IsSpacelikeLipschitzIn`; `f = 0` is the hyperplane `t = 0`). -/
theorem isSpacelikeLipschitzIn_graphOver {f : EuclideanSpace ℝ (Fin d) → ℝ} {c : ℝ≥0}
    (hc : c < 1) (hf : LipschitzWith c f) : IsSpacelikeLipschitzIn ⊤ (graphOver univ f) :=
  ⟨fun _ _ => trivial, fun _ hp _ hq => not_lt_top_of_graphOver (hf.weaken hc.le) hp hq,
    fun _ _ => ⟨1, ⊤, univ, f, c, hc, trivial, le_rfl, isOpen_univ, hf.lipschitzOnWith, by simp⟩⟩

/-! ### The topology needs spacelikeness: a null hyperplane -/

/-- The null hyperplane `{t = ⟪e, x⟫}` (`‖e‖ = 1`): an achronal, closed, `1`-Lipschitz graph. -/
def nullGraph (e : EuclideanSpace ℝ (Fin d)) : Set (Minkowski d) :=
  {p | p.1 = inner ℝ e p.2}

theorem isLipschitzHypersurfaceIn_nullGraph {e : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) :
    IsLipschitzHypersurfaceIn ⊤ (nullGraph e) := by
  refine ⟨fun _ _ => trivial, fun p hp q hq hpq => ?_, fun p _ => ?_⟩
  · rw [show (⊤ : Opens (Minkowski d)) = ⊤ from rfl, lt_top_iff_minkQ] at hpq
    have h1 : (q - p).1 = inner ℝ e (q - p).2 := by
      simp only [Prod.fst_sub, Prod.snd_sub, inner_sub_right]
      rw [show p.1 = _ from hp, show q.1 = _ from hq]
    have h2 : |(q - p).1| ≤ ‖(q - p).2‖ := by
      rw [h1]; exact (abs_real_inner_le_norm _ _).trans_eq (by rw [he, one_mul])
    have h3 := hpq.2
    rw [minkQ_lt_zero_iff] at h3
    nlinarith [abs_nonneg (q - p).1, sq_abs (q - p).1, norm_nonneg (q - p).2]
  · refine ⟨1, ⊤, univ, fun x => inner ℝ e x, trivial, le_rfl, isOpen_univ,
      LipschitzWith.lipschitzOnWith (LipschitzWith.of_dist_le_mul fun x y => ?_), ?_⟩
    · rw [Real.dist_eq, dist_eq_norm, ← inner_sub_right, NNReal.coe_one, one_mul]
      exact (abs_real_inner_le_norm _ _).trans_eq (by rw [he, one_mul])
    · ext q
      simp [nullGraph, graphOver]

/-- The null vector `(1, e)`. -/
theorem minkQ_one_e {e : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) :
    minkQ ((1, e) : Minkowski d) = 0 := by
  simp [minkQ, he]

/-- **Counterexample (W3, achronal form).** On the null hyperplane the induced pseudo-distance
vanishes along the null generators: `(0, 0)` and `(1, e)` are distinct points at distance `0`. -/
theorem nullGraph_edist_eq_zero {e : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) :
    ∃ x y : InducedLength (nullGraph e) ⊤, x ≠ y ∧ edist x y = 0 := by
  set v : Minkowski d := (1, e)
  have hv : ∀ r : ℝ, r • v ∈ nullGraph e ∩ ((⊤ : Opens (Minkowski d)) : Set _) := fun r =>
    ⟨by simp [v, nullGraph, inner_smul_right, he], trivial⟩
  let x : ↥(nullGraph e ∩ ((⊤ : Opens (Minkowski d)) : Set _)) := ⟨(0 : ℝ) • v, hv 0⟩
  let y : ↥(nullGraph e ∩ ((⊤ : Opens (Minkowski d)) : Set _)) := ⟨(1 : ℝ) • v, hv 1⟩
  let γ : Path x y :=
    { toFun := fun t => ⟨(t : ℝ) • v, hv t⟩
      continuous_toFun := by fun_prop
      source' := rfl
      target' := rfl }
  refine ⟨InducedLength.toSubtype.symm x, InducedLength.toSubtype.symm y, fun h => ?_,
    le_antisymm ((InducedLength.edist_le_lengthOn _ _ γ).trans_eq ?_) bot_le⟩
  · have h' := congrArg
      (fun z : ↥(nullGraph e ∩ ((⊤ : Opens (Minkowski d)) : Set _)) => (z : Minkowski d).1)
      (InducedLength.toSubtype.symm.injective h)
    simp [x, y, v] at h'
  · have hext : curveExtend γ.toContinuousMap =
        fun r => ((projIcc 0 1 zero_le_one r : ℝ)) • v := rfl
    have hL : IsLipschitzCurve γ.toContinuousMap := by
      refine ⟨‖v‖₊, ?_⟩
      rw [hext]
      have h1 : LipschitzWith ‖v‖₊ fun r : ℝ => r • v :=
        LipschitzWith.of_dist_le_mul fun r s => by
          rw [dist_eq_norm, ← sub_smul, norm_smul, Real.dist_eq, coe_nnnorm, mul_comm,
            Real.norm_eq_abs]
      have := h1.comp ((LipschitzWith.subtype_val _).comp (LipschitzWith.projIcc zero_le_one))
      rw [mul_one, mul_one] at this
      exact this
    rw [lengthOn_of_isLipschitzCurve hL, lorentzLength_congr (γ' := fun r => r • v)]
    · have hd : ∀ r, deriv (fun r : ℝ => r • v) r = v := fun r => by
        simpa using ((hasDerivAt_id' r).smul_const v).deriv
      have hv0 : minkQ v = 0 := minkQ_one_e he
      unfold lorentzLength
      simp only [hd, hv0, Real.sqrt_zero, ENNReal.ofReal_zero, lintegral_zero]
    · intro r hr
      rw [hext]; dsimp only; rw [projIcc_of_mem zero_le_one ⟨hr.1.le, hr.2.le⟩]

/-- **The emetric topology of a merely achronal Lipschitz hypersurface need not be the subspace
topology**: on the null hyperplane the identity to the subspace is not continuous. -/
theorem not_continuous_toSubtype_nullGraph {e : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) :
    ¬ Continuous ⇑(InducedLength.toSubtype (S := nullGraph e) (V := ⊤)) := by
  intro hc
  obtain ⟨x, y, hxy, h0⟩ := nullGraph_edist_eq_zero he
  exact hxy ((EMetric.inseparable_iff.2 h0).map hc).eq

/-! ### (e) The topology of the induced length -/

section Topology

variable {S : Set (Minkowski d)} {O : Set (Minkowski d)} {g : isom d}
  {U : Set (EuclideanSpace ℝ (Fin d))} {f : EuclideanSpace ℝ (Fin d) → ℝ}

/-- The lift `x ↦ (f x, x)` of `ℝᵈ` to the graph of `f`. -/
def graphLift (f : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) : Minkowski d :=
  (f x, x)

/-- In a frame, a point of `Σ ∩ O` is a point of the graph. -/
theorem frame_mem_graphOver (hgr : g • (S ∩ O) = g • O ∩ graphOver U f) {z : Minkowski d}
    (hz : z ∈ S) (hzO : z ∈ O) : (g • z).2 ∈ U ∧ g • z = graphLift f (g • z).2 := by
  have : g • z ∈ g • (S ∩ O) := Set.smul_mem_smul_set ⟨hz, hzO⟩
  rw [hgr] at this
  exact ⟨this.2.1, Prod.ext this.2.2 rfl⟩

/-- In a frame, a point of the graph over `U` inside `g • O` comes from `Σ ∩ O`. -/
theorem mem_of_frame (hgr : g • (S ∩ O) = g • O ∩ graphOver U f) {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ U) (hxO : graphLift f x ∈ g • O) : g⁻¹ • graphLift f x ∈ S ∩ O := by
  have : graphLift f x ∈ g • (S ∩ O) := by rw [hgr]; exact ⟨hxO, hx, rfl⟩
  obtain ⟨z, hz, hzx⟩ := this
  rw [← hzx, inv_smul_smul]; exact hz

theorem lipschitzOnWith_graphLift {c : ℝ≥0} (hc : c ≤ 1) (hf : LipschitzOnWith c f U) :
    LipschitzOnWith 1 (graphLift f) U := by
  have := (hf.weaken hc).prodMk (LipschitzWith.id.lipschitzOnWith (s := U))
  unfold graphLift; simpa using this

/-- The spatial part of the derivative is bounded by the derivative of the spatial part. -/
theorem norm_deriv_snd_le (F : ℝ → Minkowski d) (s : ℝ) :
    ‖(deriv F s).2‖ ≤ ‖deriv (fun t => (F t).2) s‖ := by
  by_cases hF : DifferentiableAt ℝ F s
  · have h := ((ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin d))).hasFDerivAt.comp_hasDerivAt
      s hF.hasDerivAt).deriv
    exact le_of_eq (congrArg norm h.symm)
  · rw [deriv_zero_of_not_differentiableAt hF]; simp

theorem snd_deriv_eq (F : ℝ → Minkowski d) {s : ℝ} (hF : DifferentiableAt ℝ F s) :
    (deriv F s).2 = deriv (fun t => (F t).2) s :=
  (((ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin d))).hasFDerivAt.comp_hasDerivAt
      s hF.hasDerivAt).deriv).symm

/-- **The upper half of the comparison** `d ≤ ‖Δx‖`: two points of `Σ ∩ O` whose frame
coordinates `x₀, x₁` lie in a convex `B ⊆ U` over which the graph stays in `g • O` are at induced
distance at most `‖x₁ − x₀‖`. -/
theorem InducedLength.edist_le_frame {V : Opens (Minkowski d)} {O : Opens (Minkowski d)}
    (hOV : O ≤ V) (hf : LipschitzOnWith 1 f U)
    (hgr : g • (S ∩ (O : Set (Minkowski d))) = g • (O : Set (Minkowski d)) ∩ graphOver U f)
    {B : Set (EuclideanSpace ℝ (Fin d))} (hB : Convex ℝ B) (hBU : B ⊆ U)
    (hBO : ∀ x ∈ B, graphLift f x ∈ g • (O : Set (Minkowski d)))
    {x₀ x₁ : EuclideanSpace ℝ (Fin d)} (hx₀ : x₀ ∈ B) (hx₁ : x₁ ∈ B) (p q : InducedLength S V)
    (hp : g • (InducedLength.toSubtype p : Minkowski d) = graphLift f x₀)
    (hq : g • (InducedLength.toSubtype q : Minkowski d) = graphLift f x₁) :
    edist p q ≤ ENNReal.ofReal ‖x₁ - x₀‖ := by
  set seg : ℝ → EuclideanSpace ℝ (Fin d) := fun t => x₀ + t • (x₁ - x₀)
  have hsegB : ∀ t : I, seg t ∈ B := fun t => hB.add_smul_sub_mem hx₀ hx₁ t.2
  have hmem : ∀ t : I, g⁻¹ • graphLift f (seg t) ∈ S ∩ (V : Set (Minkowski d)) := fun t => by
    have h := mem_of_frame hgr (hBU (hsegB t)) (hBO _ (hsegB t))
    exact ⟨h.1, hOV h.2⟩
  have hcont : Continuous fun t : I => graphLift f (seg t) :=
    (lipschitzOnWith_graphLift le_rfl hf).continuousOn.comp_continuous (by fun_prop)
      fun t => hBU (hsegB t)
  let γ : Path (InducedLength.toSubtype p) (InducedLength.toSubtype q) :=
    { toFun := fun t => ⟨g⁻¹ • graphLift f (seg t), hmem t⟩
      continuous_toFun := (hcont.const_smul g⁻¹).subtype_mk _
      source' := Subtype.ext (by simp [seg, ← hp])
      target' := Subtype.ext (by simp [seg, ← hq]) }
  have hext : curveExtend γ.toContinuousMap = fun r =>
      g⁻¹ • graphLift f (seg (projIcc 0 1 zero_le_one r)) := rfl
  -- the curve is Lipschitz
  obtain ⟨K, hK⟩ := isom_lipschitzWith g⁻¹
  have hsegL : LipschitzWith ‖x₁ - x₀‖₊ fun r : ℝ => seg (projIcc 0 1 zero_le_one r) := by
    have h1 : LipschitzWith ‖x₁ - x₀‖₊ seg := LipschitzWith.of_dist_le_mul fun r s => by
      simp only [seg, dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul, coe_nnnorm,
        Real.norm_eq_abs]; rw [mul_comm]
    have := h1.comp ((LipschitzWith.subtype_val _).comp (LipschitzWith.projIcc zero_le_one))
    rw [mul_one, mul_one] at this; exact this
  have hlift : LipschitzWith ‖x₁ - x₀‖₊ fun r : ℝ => graphLift f (seg (projIcc 0 1 zero_le_one r)) := by
    have := (lipschitzOnWith_graphLift le_rfl hf).comp (hsegL.lipschitzOnWith (s := univ))
      (fun r _ => hBU (hsegB _))
    rw [one_mul, lipschitzOnWith_univ] at this; exact this
  have hL : IsLipschitzCurve γ.toContinuousMap := ⟨K * ‖x₁ - x₀‖₊, by rw [hext]; exact hK.comp hlift⟩
  refine (InducedLength.edist_le_lengthOn p q γ).trans ?_
  rw [lengthOn_of_isLipschitzCurve hL, hext, lorentzLength_isom g⁻¹ _ 0 1,
    lorentzLength_congr (γ' := fun r => graphLift f (seg r)) fun r hr => by
      dsimp only; rw [projIcc_of_mem zero_le_one ⟨hr.1.le, hr.2.le⟩]]
  calc lorentzLength (fun r => graphLift f (seg r)) 0 1
      ≤ ∫⁻ _ in Ioc (0 : ℝ) 1, ENNReal.ofReal ‖x₁ - x₀‖ := by
        refine lintegral_mono fun r => ENNReal.ofReal_le_ofReal ?_
        refine (sqrt_minkQ_le _).trans ((norm_deriv_snd_le _ r).trans (le_of_eq ?_))
        have : (fun t => (graphLift f (seg t)).2) = seg := rfl
        rw [this]
        have hd : HasDerivAt seg (x₁ - x₀) r := by
          have := ((hasDerivAt_id' r).smul_const (x₁ - x₀)).const_add x₀
          rw [one_smul] at this; exact this
        rw [hd.deriv]
    _ = ENNReal.ofReal ‖x₁ - x₀‖ := by simp [Real.volume_Ioc]

theorem isOpen_frameBall (O : Opens (Minkowski d)) (g : isom d) (x₀ : EuclideanSpace ℝ (Fin d))
    (r : ℝ) : IsOpen {z : Minkowski d | z ∈ O ∧ (g • z).2 ∈ Metric.ball x₀ r} :=
  O.isOpen.inter (Metric.isOpen_ball.preimage (continuous_snd.comp (continuous_const_smul g)))

/-- **(e), first half: the subspace topology is finer than the length topology**, for every
achronal Lipschitz hypersurface (`c = 1` suffices): the identity from `Σ ∩ V` with the subspace
topology to the induced length space is continuous. -/
theorem IsLipschitzHypersurfaceIn.continuous_toSubtype_symm {V : Opens (Minkowski d)}
    (h : IsLipschitzHypersurfaceIn V S) :
    Continuous ⇑(InducedLength.toSubtype (S := S) (V := V)).symm := by
  refine continuous_iff_continuousAt.2 fun p => ?_
  rw [ContinuousAt, EMetric.tendsto_nhds]
  intro ε hε
  obtain ⟨g, O, U, f, hpO, hOV, hU, hf, hgr⟩ := h.locGraph p p.2.1
  obtain ⟨hx₀U, hP⟩ := frame_mem_graphOver hgr p.2.1 hpO
  set x₀ := (g • (p : Minkowski d)).2
  have hcont : ContinuousAt (graphLift f) x₀ :=
    (lipschitzOnWith_graphLift le_rfl hf).continuousOn.continuousAt (hU.mem_nhds hx₀U)
  have hO' : IsOpen (g • (O : Set (Minkowski d))) := O.isOpen.smul g
  have hmem : graphLift f x₀ ∈ g • (O : Set (Minkowski d)) := hP ▸ smul_mem_smul_set hpO
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (inter_mem (hU.mem_nhds hx₀U)
    (hcont.preimage_mem_nhds (hO'.mem_nhds hmem)))
  obtain ⟨δ, -, hδ0, hδε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  have hδ : 0 < δ := ENNReal.ofReal_pos.1 hδ0
  set ρ := min r δ
  have hρ : 0 < ρ := lt_min hr hδ
  have hsub : Metric.ball x₀ ρ ⊆ Metric.ball x₀ r := Metric.ball_subset_ball (min_le_left _ _)
  have hN : {q : ↥(S ∩ (V : Set (Minkowski d))) | (q : Minkowski d) ∈ O ∧
      (g • (q : Minkowski d)).2 ∈ Metric.ball x₀ ρ} ∈ 𝓝 p :=
    (continuous_subtype_val.isOpen_preimage _ (isOpen_frameBall O g x₀ ρ)).mem_nhds
      ⟨hpO, Metric.mem_ball_self hρ⟩
  filter_upwards [hN] with q ⟨hqO, hqb⟩
  obtain ⟨-, hQ⟩ := frame_mem_graphOver hgr q.2.1 hqO
  rw [edist_comm]
  calc edist (InducedLength.toSubtype.symm p) (InducedLength.toSubtype.symm q)
      ≤ ENNReal.ofReal ‖(g • (q : Minkowski d)).2 - x₀‖ :=
        InducedLength.edist_le_frame hOV hf hgr (convex_ball x₀ ρ)
          (fun x hx => (hball (hsub hx)).1) (fun x hx => (hball (hsub hx)).2)
          (Metric.mem_ball_self hρ) hqb _ _ hP hQ
    _ < ε := by
        refine lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff hδ).2 ?_) hδε.le
        exact (mem_ball_iff_norm.1 hqb).trans_le (min_le_right _ _)

theorem intervalIntegrable_of_bound {φ : ℝ → ℝ} (hφ : Measurable φ) (C : ℝ) (h : ∀ s, ‖φ s‖ ≤ C)
    (a b : ℝ) : IntervalIntegrable φ volume a b :=
  IntervalIntegrable.mono_fun' (g := fun _ => C) intervalIntegrable_const
    hφ.aestronglyMeasurable (Filter.Eventually.of_forall h)

/-- **The fundamental theorem of calculus, as an inequality, for Lipschitz curves of `ℝᵈ`**:
`‖X b − X a‖ ≤ ∫ₐᵇ ‖X'‖`. -/
theorem norm_sub_le_integral_norm_deriv {X : ℝ → EuclideanSpace ℝ (Fin d)} {K : ℝ≥0}
    (hX : LipschitzWith K X) {a b : ℝ} (hab : a ≤ b) :
    ‖X b - X a‖ ≤ ∫ s in a..b, ‖deriv X s‖ := by
  set w := X b - X a
  set u : ℝ → ℝ := fun s => inner ℝ w (X s)
  have h1 : LipschitzWith ‖w‖₊ fun x : EuclideanSpace ℝ (Fin d) => inner ℝ w x :=
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [Real.dist_eq, dist_eq_norm, ← inner_sub_right, coe_nnnorm]
      exact abs_real_inner_le_norm _ _
  have hu : LipschitzWith (‖w‖₊ * K) u := h1.comp hX
  have hFTC : ∫ s in a..b, deriv u s = u b - u a :=
    (hu.lipschitzOnWith.absolutelyContinuousOnInterval).integral_deriv_eq_sub
  have hub : u b - u a = ‖w‖ ^ 2 := by
    simp only [u, ← inner_sub_right, real_inner_self_eq_norm_sq, w]
  have hdu : ∀ᵐ s, deriv u s = inner ℝ w (deriv X s) := by
    filter_upwards [hX.ae_differentiableAt_real] with s hs
    exact ((innerSL ℝ w).hasFDerivAt.comp_hasDerivAt s hs.hasDerivAt).deriv
  have hbd : ∀ s, ‖deriv X s‖ ≤ K := fun s => norm_deriv_le_of_lipschitz hX
  have hint1 : IntervalIntegrable (fun s => inner ℝ w (deriv X s)) volume a b :=
    intervalIntegrable_of_bound ((continuous_const.inner continuous_id).measurable.comp
      (measurable_deriv X)) (‖w‖ * K) (fun s => by
        rw [Real.norm_eq_abs]
        exact (abs_real_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_left (hbd s) (norm_nonneg _))) a b
  have hint2 : IntervalIntegrable (fun s => ‖w‖ * ‖deriv X s‖) volume a b :=
    intervalIntegrable_of_bound (measurable_const.mul (measurable_deriv X).norm) (‖w‖ * K)
      (fun s => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left (hbd s) (norm_nonneg _)) a b
  have hle : ‖w‖ ^ 2 ≤ ‖w‖ * ∫ s in a..b, ‖deriv X s‖ := by
    rw [← hub, ← hFTC, intervalIntegral.integral_congr_ae (hdu.mono fun s hs _ => hs),
      ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_ae hab hint1 hint2
      (Filter.Eventually.of_forall fun s => real_inner_le_norm _ _)
  have hI : 0 ≤ ∫ s in a..b, ‖deriv X s‖ :=
    intervalIntegral.integral_nonneg hab fun _ _ => norm_nonneg _
  rcases (norm_nonneg w).eq_or_lt with h0 | hpos
  · rw [← h0]; exact hI
  · nlinarith

/-- A derivative whose difference quotients obey `|Δt| ≤ c ‖Δx‖` obeys `|t'| ≤ c ‖x'‖`. -/
theorem abs_deriv_fst_le {Γ : ℝ → Minkowski d} {s : ℝ} (hΓ : DifferentiableAt ℝ Γ s) {c : ℝ}
    (h : ∀ᶠ s' in 𝓝 s, |(Γ s').1 - (Γ s).1| ≤ c * ‖(Γ s').2 - (Γ s).2‖) :
    |(deriv Γ s).1| ≤ c * ‖(deriv Γ s).2‖ := by
  have ht := hasDerivAt_iff_tendsto_slope.1 hΓ.hasDerivAt
  have hφ : Continuous fun v : Minkowski d => c * ‖v.2‖ - |v.1| := by fun_prop
  have := ge_of_tendsto (b := 0) ((hφ.tendsto _).comp ht) ((h.filter_mono nhdsWithin_le_nhds).mono fun s' hs' => by
    simp only [Function.comp_apply, slope_def_module, Prod.smul_fst, Prod.smul_snd,
      Prod.fst_sub, Prod.snd_sub, smul_eq_mul, norm_smul, abs_mul, Real.norm_eq_abs]
    rw [sub_nonneg, mul_left_comm]
    exact mul_le_mul_of_nonneg_left hs' (abs_nonneg _))
  linarith

/-- `√(1 − c²) ‖v.2‖ ≤ √(minkQ v)` when `|v.1| ≤ c ‖v.2‖`. -/
theorem le_sqrt_minkQ {v : Minkowski d} {c : ℝ} (h : |v.1| ≤ c * ‖v.2‖) :
    Real.sqrt (1 - c ^ 2) * ‖v.2‖ ≤ Real.sqrt (minkQ v) := by
  rw [← Real.sqrt_sq (norm_nonneg v.2), ← Real.sqrt_mul' _ (sq_nonneg _)]
  refine Real.sqrt_le_sqrt ?_
  have h2 : v.1 ^ 2 ≤ (c * ‖v.2‖) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
  unfold minkQ; nlinarith

/-- **The lower half of the comparison** `√(1−c²) ‖Δx‖ ≤ d`, along a curve: if, on `(0, t)`, the
frame image of the Lipschitz curve `F` stays on the graph of a `c`-Lipschitz `f` over `U`, its
length on `[0, t]` is at least `√(1 − c²)` times the frame displacement. -/
theorem le_lorentzLength_of_frame {F : ℝ → Minkowski d} {K : ℝ≥0} (hF : LipschitzWith K F)
    {t : ℝ} (ht : 0 ≤ t) (g : isom d) {c : ℝ≥0} (hf : LipschitzOnWith c f U)
    (hgraph : ∀ s ∈ Ioo 0 t, (g • F s).2 ∈ U ∧ (g • F s).1 = f (g • F s).2) :
    ENNReal.ofReal (Real.sqrt (1 - (c : ℝ) ^ 2) * ‖(g • F t).2 - (g • F 0).2‖) ≤
      lorentzLength F 0 t := by
  set k := Real.sqrt (1 - (c : ℝ) ^ 2)
  set Γ : ℝ → Minkowski d := fun s => g • F s
  set X : ℝ → EuclideanSpace ℝ (Fin d) := fun s => (Γ s).2
  obtain ⟨Kg, hKg⟩ := isom_lipschitzWith g
  have hΓ : LipschitzWith (Kg * K) Γ := hKg.comp hF
  have hX : LipschitzWith (1 * (Kg * K)) X := LipschitzWith.prod_snd.comp hΓ
  have hbd : ∀ s, ‖deriv X s‖ ≤ 1 * (Kg * K) := fun s => norm_deriv_le_of_lipschitz hX
  have hk : 0 ≤ k := Real.sqrt_nonneg _
  -- the pointwise bound, a.e. on `(0, t)`
  have hpt : ∀ᵐ s ∂(volume.restrict (Ioo 0 t)),
      ENNReal.ofReal (k * ‖deriv X s‖) ≤ ENNReal.ofReal (Real.sqrt (minkQ (deriv Γ s))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae hΓ.ae_differentiableAt_real] with s hs hd
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← snd_deriv_eq Γ hd]
    refine le_sqrt_minkQ (abs_deriv_fst_le hd ?_)
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with s' hs'
    obtain ⟨h1, h2⟩ := hgraph s' hs'
    obtain ⟨h1', h2'⟩ := hgraph s hs
    rw [show (Γ s').1 = _ from h2, show (Γ s).1 = _ from h2', ← Real.dist_eq, ← dist_eq_norm]
    exact hf.dist_le_mul _ h1 _ h1'
  calc ENNReal.ofReal (k * ‖(g • F t).2 - (g • F 0).2‖)
      ≤ ENNReal.ofReal (∫ s in (0 : ℝ)..t, k * ‖deriv X s‖) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [intervalIntegral.integral_const_mul]
        exact mul_le_mul_of_nonneg_left (norm_sub_le_integral_norm_deriv hX ht) hk
    _ = ∫⁻ s in Ioo 0 t, ENNReal.ofReal (k * ‖deriv X s‖) := by
        rw [intervalIntegral.integral_of_le ht, integral_Ioc_eq_integral_Ioo,
          ofReal_integral_eq_lintegral_ofReal]
        · refine Integrable.mono' (g := fun _ => k * (1 * (Kg * K))) (integrableOn_const (by simp))
            (measurable_const.mul (measurable_deriv X).norm).aestronglyMeasurable
            (Filter.Eventually.of_forall fun s => ?_)
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          exact mul_le_mul_of_nonneg_left (hbd s) hk
        · exact Filter.Eventually.of_forall fun s => by positivity
    _ ≤ ∫⁻ s in Ioo 0 t, ENNReal.ofReal (Real.sqrt (minkQ (deriv Γ s))) := lintegral_mono_ae hpt
    _ = lorentzLength F 0 t := by
        rw [← lorentzLength_isom g F 0 t]
        exact setLIntegral_congr Ioo_ae_eq_Ioc

/-- **(e), second half: for a spacelike Lipschitz hypersurface the length topology is finer than
the subspace topology.** A path of length `< √(1 − c²) ρ` from `p` cannot leave the frame
cylinder of radius `ρ` around `p` (`le_lorentzLength_of_frame`, run up to the first exit time). -/
theorem IsSpacelikeLipschitzIn.continuous_toSubtype {V : Opens (Minkowski d)}
    (h : IsSpacelikeLipschitzIn V S) :
    Continuous ⇑(InducedLength.toSubtype (S := S) (V := V)) := by
  refine continuous_iff_continuousAt.2 fun p => ?_
  rw [ContinuousAt, Filter.tendsto_def]
  intro N hN
  obtain ⟨u, hu, huN⟩ := (mem_nhds_subtype _ _ _).1 hN
  obtain ⟨W, hWu, hWo, hPW⟩ := mem_nhds_iff.1 hu
  set p' := InducedLength.toSubtype p
  set P : Minkowski d := (p' : Minkowski d)
  obtain ⟨g, O, U, f, c, hc, hpO, hOV, hU, hf, hgr⟩ := h.locGraph P p'.2.1
  obtain ⟨hx₀U, hP⟩ := frame_mem_graphOver hgr p'.2.1 hpO
  set x₀ := (g • P).2
  have hlift := lipschitzOnWith_graphLift hc.le hf
  have hcont : ContinuousAt (graphLift f) x₀ := hlift.continuousOn.continuousAt (hU.mem_nhds hx₀U)
  have hOW : g • ((O : Set (Minkowski d)) ∩ W) ∈ 𝓝 (graphLift f x₀) := by
    rw [← hP, smul_mem_nhds_smul_iff]
    exact (O.isOpen.inter hWo).mem_nhds ⟨hpO, hPW⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (inter_mem (hU.mem_nhds hx₀U)
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
  rw [EMetric.mem_nhds_iff]
  refine ⟨ENNReal.ofReal (k * ρ), ENNReal.ofReal_pos.2 (mul_pos hk hρ), fun q hq => ?_⟩
  rw [Metric.mem_eball, edist_comm, InducedLength.edist_def, iInf_lt_iff] at hq
  obtain ⟨γ, hγ⟩ := hq
  have hLip : IsLipschitzCurve γ.toContinuousMap := by
    by_contra hn; rw [lengthOn_of_not_isLipschitzCurve hn] at hγ; exact not_top_lt hγ
  obtain ⟨K, hK⟩ := hLip
  rw [lengthOn_of_isLipschitzCurve ⟨K, hK⟩] at hγ
  set F := curveExtend γ.toContinuousMap
  have hFc : Continuous F := continuous_subtype_val.comp γ.extend.continuous
  have hFS : ∀ s, F s ∈ S := fun s => (γ.extend s).2.1
  have hF0 : F 0 = P := by simp [F, curveExtend_path, P, p']
  have hF1 : F 1 = (InducedLength.toSubtype q : Minkowski d) := by simp [F, curveExtend_path]
  -- the set of times up to which the curve stays in `G`
  set T : Set ℝ := {t | t ∈ Icc (0 : ℝ) 1 ∧ ∀ s ∈ Icc 0 t, F s ∈ G}
  have h0T : (0 : ℝ) ∈ T := ⟨⟨le_rfl, zero_le_one⟩, fun s hs => by
    rw [show s = 0 from le_antisymm hs.2 hs.1, hF0]; exact hPG⟩
  have hTne : T.Nonempty := ⟨0, h0T⟩
  have hTbdd : BddAbove T := ⟨1, fun t ht => ht.1.2⟩
  set τ := sSup T
  have hτ0 : 0 ≤ τ := le_csSup hTbdd h0T
  have hτ1 : τ ≤ 1 := csSup_le hTne fun t ht => ht.1.2
  -- inside `G` the frame displacement is controlled by the length
  have hA : ∀ t ∈ T, ‖(g • F t).2 - x₀‖ < ρ := fun t ht => by
    have hle := le_lorentzLength_of_frame hK ht.1.1 g hf fun s hs =>
      frame_mem_graphOver hgr (hFS s) (ht.2 s ⟨hs.1.le, hs.2.le⟩).1 |>.imp_right
        fun h' => by rw [h']; rfl
    rw [hF0] at hle
    have hlt := hle.trans_lt ((lorentzLength_mono le_rfl ht.1.2).trans_lt hγ)
    rw [ENNReal.ofReal_lt_ofReal_iff (mul_pos hk hρ)] at hlt
    exact lt_of_mul_lt_mul_left hlt hk.le
  have hdown : ∀ t ∈ T, ∀ s ∈ Icc (0 : ℝ) t, s ∈ T := fun t ht s hs =>
    ⟨⟨hs.1, hs.2.trans ht.1.2⟩, fun s' hs' => ht.2 s' ⟨hs'.1, hs'.2.trans hs.2⟩⟩
  have hB : ∀ s ∈ Ico (0 : ℝ) τ, s ∈ T := fun s hs => by
    obtain ⟨t, ht, hst⟩ := exists_lt_of_lt_csSup hTne hs.2
    exact hdown t ht s ⟨hs.1, hst.le⟩
  -- the compact piece of `Σ` over the closed frame ball
  set Kc := (fun x => g⁻¹ • graphLift f x) '' Metric.closedBall x₀ ρ
  have hKc : IsClosed Kc := ((isCompact_closedBall x₀ ρ).image_of_continuousOn
    ((hlift.continuousOn.mono fun x hx => (hball (hρr hx)).1).const_smul g⁻¹)).isClosed
  have hFK : ∀ s ∈ T, F s ∈ Kc := fun s hs => by
    obtain ⟨-, hFs⟩ := frame_mem_graphOver hgr (hFS s) (hs.2 s ⟨hs.1.1, le_rfl⟩).1
    refine ⟨(g • F s).2, Metric.mem_closedBall.2 ((dist_eq_norm _ _).trans_le (hA s hs).le), ?_⟩
    dsimp only; rw [← hFs, inv_smul_smul]
  have hC : F τ ∈ G := by
    rcases hτ0.eq_or_lt with h0 | hpos
    · rw [← h0, hF0]; exact hPG
    have hmemK : F τ ∈ Kc := by
      have hcl : τ ∈ closure (Ico 0 τ) := by rw [closure_Ico hpos.ne]; exact ⟨hτ0, le_rfl⟩
      have := mem_closure_image (f := F) hFc.continuousAt hcl
      refine closure_minimal ?_ hKc this
      rintro _ ⟨s, hs, rfl⟩; exact hFK s (hB s hs)
    obtain ⟨x, hx, hxF⟩ := hmemK
    obtain ⟨-, hxOW⟩ := hball (hρr hx)
    obtain ⟨z, ⟨hzO, hzW⟩, hzx⟩ := hxOW
    have hz : z = F τ := by rw [← hxF]; dsimp only; rw [← hzx, inv_smul_smul]
    refine ⟨hz ▸ hzO, hz ▸ hzW, ?_⟩
    rw [← hxF, smul_inv_smul]; exact hρr hx
  have hτT : τ ∈ T := ⟨⟨hτ0, hτ1⟩, fun s hs => by
    rcases hs.2.lt_or_eq with hlt | heq
    · exact (hB s ⟨hs.1, hlt⟩).2 s ⟨hs.1, le_rfl⟩
    · rw [heq]; exact hC⟩
  have hτeq : τ = 1 := by
    by_contra hne
    have hlt : τ < 1 := lt_of_le_of_ne hτ1 hne
    obtain ⟨η, hη, hηG⟩ := Metric.isOpen_iff.1 (hGo.preimage hFc) τ hC
    set t' := min 1 (τ + η / 2)
    have ht' : t' ∈ T := ⟨⟨hτ0.trans (le_min hτ1 (by linarith)), min_le_left _ _⟩,
      fun s hs => by
        rcases le_or_gt s τ with hsτ | hsτ
        · exact hτT.2 s ⟨hs.1, hsτ⟩
        · refine hηG (Metric.mem_ball.2 ?_)
          rw [Real.dist_eq, abs_of_pos (by linarith)]
          linarith [hs.2.trans (min_le_right _ _)]⟩
    have := le_csSup hTbdd ht'
    have : τ < t' := lt_min hlt (by linarith)
    linarith
  have h1G : F 1 ∈ G := by rw [← hτeq]; exact hC
  exact huN (show (InducedLength.toSubtype q : Minkowski d) ∈ u from hWu (hF1 ▸ h1G.2.1))

/-- **(e) For a spacelike Lipschitz hypersurface the emetric topology of the induced length is
the subspace topology** (the identity is a homeomorphism). -/
theorem IsSpacelikeLipschitzIn.isHomeomorph_toSubtype {V : Opens (Minkowski d)}
    (h : IsSpacelikeLipschitzIn V S) :
    IsHomeomorph ⇑(InducedLength.toSubtype (S := S) (V := V)) :=
  Homeomorph.isHomeomorph
    { toEquiv := InducedLength.toSubtype
      continuous_toFun := h.continuous_toSubtype
      continuous_invFun := h.toIsLipschitzHypersurfaceIn.continuous_toSubtype_symm }

/-- **For a spacelike Lipschitz hypersurface the induced length is a genuine (extended) metric**:
distinct points are at positive distance. (False for merely achronal ones:
`nullGraph_edist_eq_zero`.) -/
theorem IsSpacelikeLipschitzIn.eq_of_edist_eq_zero {V : Opens (Minkowski d)}
    (h : IsSpacelikeLipschitzIn V S) {x y : InducedLength S V} (hxy : edist x y = 0) : x = y :=
  InducedLength.toSubtype.injective ((EMetric.inseparable_iff.2 hxy).map h.continuous_toSubtype).eq

end Topology

end Causal.Flat
