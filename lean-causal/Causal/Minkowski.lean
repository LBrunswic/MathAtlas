import Causal.Static
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Minkowski space `ℝ^{1,n}` as a static spacetime

No label of the paper is certified by this file: the paper's model space is `E^{1,2}`
(`defi:causal_Ealpha`, `ETT.tex:1335`), the case `n = 2` of what is proved here, and every
statement is an instance of `Causal.Static`. Three prose findings of earlier waves become
theorems.

> for $\U\subset \mass{\alpha}$ open and $x,y\in \U$, one sets $x\leq_\U y$ (resp.
> $x\ll_\U y$) if and only if there is a future causal (resp. chronological) curve from $x$ to $y$
> in $\U$. (`defi:causal_Ealpha`, `ETT.tex:1335`)

> The flat model spacetimes of Section \ref{subsec:sing_spacetime_defi} are, by contrast,
> strongly causal. (`rem:galileo_spacetime_not_strongly`, `ETT.tex:672`)

> Let $M$ be a topological spacetime. A time function $T$ is a Cauchy time function if for every
> inextensible causal curve $c:\RR\rightarrow M$,
> $-\lim_{-\infty} (T\circ c) = \lim_{+\infty}(T\circ c) = +\infty$.
> (`def:cauchy_time_function`, `ETT.tex:1251`)

> It suffices to take $S=T^{-1}(0)$ as Cauchy hypersurface. (`theo:geroch`, `ETT.tex:1300`)

## What is proved

* `minkowski n` is the causality of `ℝ × EuclideanSpace ℝ (Fin n)` by future causal and
  chronological curves in each open set; globally `p ≤ q ⟺ p.1 ≤ q.1 ∧ ‖q.2 − p.2‖² ≤ (q.1 − p.1)²`
  (`minkowski_le_top_iff_sq`) and `p ≪ q ⟺ ‖q.2 − p.2‖ < q.1 − p.1`.
* It is causal, causally arc-connected, absolutely minimal, has push-up in every open set, is
  tarentin with `Z^± = M`, strongly causal, globally hyperbolic; `Int J^±(p) = I^±(p)`
  (`lem:IJ_calc`'s identity, `Z^∓ = M`) and `J^±(p) = closure(I^±(p))` (`lem:densite_modele`
  (a)(b)), also in every causally convex open subset.
* **(i) DEC-15's counterexample** (`minkowski_dec15`, `minkowski2_dec15`): on `ℝ^{1,n}`, `n ≥ 1`,
  with `e` a unit vector and `g(x) = max(0, min(⟨x, e⟩, 1))` — bounded, 1-Lipschitz, `g(τe) = τ`
  on `[0, 1]` — `T(t, x) = t − g(x)` is a Cauchy time function (DEC-10), is not strictly
  increasing along `≤`, and `T⁻¹(0)` is not a Cauchy surface (DEC-14): the null segment
  `{(τ, τe) : τ ∈ [0,1]}` lies in `T⁻¹(0)`, and the inextensible null line through it meets
  `T⁻¹(0)` at least twice. For `n = 1` this is the 1+1 counterexample of `Causal.Geroch`'s SCOPE.
* **(ii) No maximal chain in `ℝ^{1,n}`, `n ≥ 1`** (`minkowski_not_isMaximalChain`), so
  `def:causally_connected` fails and `def:causally_complete` holds vacuously there
  (`minkowski_not_causallyConnected`, `minkowski_causallyComplete`).
* **(iii) The strongly causal sentence of `rem:galileo_spacetime_not_strongly`** for Minkowski
  space of every dimension (`minkowski_stronglyCausal`).

## Hypothesis checklist

| paper | here |
|---|---|
| `E^{1,2}` | ⚠ weakened: `ℝ^{1,n}` for every `n` (`n ≥ 1` where two points of space are needed) |
| chronological curve | as in `Causal.Static`: the graph of a `c`-Lipschitz map, `c < 1`; same `≪_U` as "speed `< 1` at every point" (Static's SCOPE) |

## SCOPE (disclosed)

* The causality is defined by curves in every open set, as `defi:causal_Ealpha` does; it is not
  produced by a Lorentzian metric (the library has none). `minkowski_le_top_iff_sq` is the bridge
  to the quadratic form `−dt² + ‖dx‖²`.
* `prop:mesure_dieckmann_Lorentz` is not attempted here; see `Causal.MinkowskiMeasure`.
* The counterexamples are built with the **local** causality of curves, not with
  `Causality.ofRelation` (kb/0014, kb/0019): they refute statements about this absolutely
  minimal causality.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Metric

/-- Minkowski space `ℝ^{1,n}`: time and Euclidean space `ℝ^n`. -/
abbrev Minkowski (n : ℕ) : Type := ℝ × EuclideanSpace ℝ (Fin n)

/-- **The causality of Minkowski space** `ℝ^{1,n}`: `x ≤_U y` (resp. `x ≪_U y`) iff a future
causal (resp. chronological) curve joins them in `U` (`defi:causal_Ealpha`). -/
noncomputable abbrev minkowski (n : ℕ) : Causality (Minkowski n) := staticCausality (EuclideanSpace ℝ (Fin n))

variable {n : ℕ} {p q : Minkowski n}

theorem minkowski_le_top_iff : (minkowski n).le ⊤ p q ↔ ‖q.2 - p.2‖ ≤ q.1 - p.1 := by
  rw [staticCausality.le_top_iff, dist_comm, dist_eq_norm]

theorem minkowski_lt_top_iff : (minkowski n).lt ⊤ p q ↔ ‖q.2 - p.2‖ < q.1 - p.1 := by
  rw [staticCausality.lt_top_iff, dist_comm, dist_eq_norm]

/-- The causal relation is the future causal cone of the quadratic form `−dt² + ‖dx‖²`. -/
theorem minkowski_le_top_iff_sq :
    (minkowski n).le ⊤ p q ↔ p.1 ≤ q.1 ∧ ‖q.2 - p.2‖ ^ 2 ≤ (q.1 - p.1) ^ 2 := by
  rw [minkowski_le_top_iff]
  constructor
  · intro h
    have h0 : 0 ≤ q.1 - p.1 := (norm_nonneg _).trans h
    exact ⟨by linarith, pow_le_pow_left₀ (norm_nonneg _) h 2⟩
  · rintro ⟨h1, h2⟩
    exact (sq_le_sq₀ (norm_nonneg _) (by linarith)).1 h2

/-- The chronological relation is the open future timelike cone. -/
theorem minkowski_lt_top_iff_sq :
    (minkowski n).lt ⊤ p q ↔ p.1 < q.1 ∧ ‖q.2 - p.2‖ ^ 2 < (q.1 - p.1) ^ 2 := by
  rw [minkowski_lt_top_iff]
  constructor
  · intro h
    have h0 : 0 < q.1 - p.1 := (norm_nonneg _).trans_lt h
    exact ⟨by linarith, pow_lt_pow_left₀ h (norm_nonneg _) two_ne_zero⟩
  · rintro ⟨h1, h2⟩
    exact (sq_lt_sq₀ (norm_nonneg _) (by linarith)).1 h2

/-! ### The properties, instantiated -/

theorem minkowski_isCausal : (minkowski n).IsCausal := staticCausality.isCausal

theorem minkowski_causallyArcConnected : (minkowski n).CausallyArcConnected :=
  staticCausality.causallyArcConnected

theorem minkowski_absolutelyMinimal : (minkowski n).AbsolutelyMinimal :=
  staticCausality.absolutelyMinimal

/-- `rem:pushup` for Minkowski space: push-up in every open set. -/
theorem minkowski_pushUp : (minkowski n).PushUp := staticCausality.pushUp

theorem minkowski_tarentin : (minkowski n).Tarentin := staticCausality.tarentin

theorem minkowski_Zplus : (minkowski n).Zplus = univ := staticCausality.Zplus_eq

theorem minkowski_Zminus : (minkowski n).Zminus = univ := staticCausality.Zminus_eq

/-- **(iii)** The strongly causal sentence of `rem:galileo_spacetime_not_strongly`, for Minkowski
space of every dimension. -/
theorem minkowski_stronglyCausal : (minkowski n).StronglyCausal :=
  staticCausality.stronglyCausal

theorem minkowski_globallyHyperbolic : (minkowski n).GloballyHyperbolic :=
  staticCausality.globallyHyperbolic

/-- `lem:IJ_calc` for Minkowski space: `Int J^+(p) ∩ Z^- = I^+(p)`. -/
theorem minkowski_IJ_calc (p : Minkowski n) :
    interior ((minkowski n).Jplus ⊤ {p}) ∩ (minkowski n).Zminus = (minkowski n).Iplus ⊤ {p} ∧
      interior ((minkowski n).Jminus ⊤ {p}) ∩ (minkowski n).Zplus =
        (minkowski n).Iminus ⊤ {p} :=
  ⟨staticCausality.interior_Jplus_inter_Zminus p, staticCausality.interior_Jminus_inter_Zplus p⟩

/-- `lem:densite_modele` (a)(b) for Minkowski space. -/
theorem minkowski_densite (p : Minkowski n) :
    closure ((minkowski n).Iplus ⊤ {p}) = (minkowski n).Jplus ⊤ {p} ∧
      closure ((minkowski n).Iminus ⊤ {p}) = (minkowski n).Jminus ⊤ {p} :=
  ⟨staticCausality.closure_Iplus p, staticCausality.closure_Iminus p⟩

/-- `lem:densite_modele`, in a causally convex open subset of Minkowski space. -/
theorem minkowski_densite_of_causallyConvexIn {V : Opens (Minkowski n)}
    (hV : (minkowski n).CausallyConvexIn (V : Set (Minkowski n)) ⊤) (hp : p ∈ V) :
    (minkowski n).Jplus V {p} = closure ((minkowski n).Iplus V {p}) ∩ V ∧
      (minkowski n).Jminus V {p} = closure ((minkowski n).Iminus V {p}) ∩ V :=
  ⟨staticCausality.Jplus_eq_closure_Iplus_of_causallyConvexIn hV hp,
    staticCausality.Jminus_eq_closure_Iminus_of_causallyConvexIn hV hp⟩

/-! ### A unit vector, the null line, the clamped coordinate -/

/-- The first basis vector of `ℝ^n`, `n ≥ 1`. -/
noncomputable def unitVec (n : ℕ) (hn : 0 < n) : EuclideanSpace ℝ (Fin n) :=
  EuclideanSpace.single ⟨0, hn⟩ 1

theorem norm_unitVec (hn : 0 < n) : ‖unitVec n hn‖ = 1 := by simp [unitVec]

theorem inner_smul_unitVec (hn : 0 < n) (τ : ℝ) : inner ℝ (τ • unitVec n hn) (unitVec n hn) = τ := by
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq, norm_unitVec]; ring

/-- The line `τ ↦ τ e` is a unit-speed geodesic line of `ℝ^n`. -/
theorem dist_smul_unitVec (hn : 0 < n) (s s' : ℝ) :
    dist (s • unitVec n hn) (s' • unitVec n hn) = |s - s'| := by
  rw [dist_eq_norm, ← sub_smul, norm_smul, norm_unitVec, Real.norm_eq_abs, mul_one]

/-- The clamped first coordinate `g(x) = max(0, min(⟨x, e⟩, 1))`. -/
noncomputable def clampCoord (n : ℕ) (hn : 0 < n) (v : EuclideanSpace ℝ (Fin n)) : ℝ :=
  max 0 (min (inner ℝ v (unitVec n hn)) 1)

theorem clampCoord_lipschitz (hn : 0 < n) (v w : EuclideanSpace ℝ (Fin n)) :
    |clampCoord n hn v - clampCoord n hn w| ≤ dist v w := by
  unfold clampCoord
  refine (abs_max_sub_max_le_max _ _ _ _).trans ?_
  rw [sub_self, abs_zero]
  refine max_le (dist_nonneg) ((abs_min_sub_min_le_max _ _ _ _).trans ?_)
  rw [sub_self, abs_zero]
  refine max_le ?_ dist_nonneg
  rw [← inner_sub_left, dist_eq_norm]
  exact (abs_real_inner_le_norm _ _).trans (by rw [norm_unitVec, mul_one])

theorem abs_clampCoord_le (hn : 0 < n) (v : EuclideanSpace ℝ (Fin n)) : |clampCoord n hn v| ≤ 1 := by
  unfold clampCoord
  rw [abs_le]
  constructor
  · linarith [le_max_left 0 (min (inner ℝ v (unitVec n hn)) 1)]
  · exact max_le zero_le_one (min_le_right _ _)

theorem clampCoord_smul (hn : 0 < n) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) :
    clampCoord n hn (τ • unitVec n hn) = τ := by
  rw [clampCoord, inner_smul_unitVec, min_eq_left hτ.2, max_eq_right hτ.1]

/-- **Witness.** The null line `τ ↦ (τ, τe)` of `ℝ^{1,n}`, `n ≥ 1`, is an inextensible causal
curve over `ℝ` (the hypothesis of `staticCausality.inextensible_nullLine`, instantiated). -/
theorem minkowski_inextensible_nullLine (hn : 0 < n) :
    (minkowski n).Inextensible ⊤ univ fun τ => (τ, τ • unitVec n hn) :=
  staticCausality.inextensible_nullLine (dist_smul_unitVec hn)

/-- **Witness.** The clamped coordinate is bounded, 1-Lipschitz and the identity along the null
line over `[0, 1]`: the hypotheses of `staticCausality.isCauchyTimeFunction_sub` and of
`staticCausality.not_strict_and_not_isCauchySurface`, instantiated. -/
theorem clampCoord_hypotheses (hn : 0 < n) :
    (∀ v w, |clampCoord n hn v - clampCoord n hn w| ≤ dist v w) ∧
      (∀ v, |clampCoord n hn v| ≤ 1) ∧
      ∀ τ ∈ Icc (0 : ℝ) 1, clampCoord n hn (τ • unitVec n hn) = τ :=
  ⟨clampCoord_lipschitz hn, abs_clampCoord_le hn, fun _ hτ => clampCoord_smul hn hτ⟩

/-- DEC-15's time function: `T(t, x) = t − g(x)`. -/
noncomputable def dec15Time (n : ℕ) (hn : 0 < n) (p : Minkowski n) : ℝ := p.1 - clampCoord n hn p.2

/-! ### (i) DEC-15's counterexample -/

/-- **(i) The counterexample behind DEC-15.** On `ℝ^{1,n}`, `n ≥ 1`, the function
`T(t, x) = t − g(x)`, `g` the clamped coordinate along a unit vector (bounded, 1-Lipschitz,
`g(τe) = τ` on `[0, 1]`), is a Cauchy time function in the sense of DEC-10, is **not** strictly
increasing along `≤`, and `T⁻¹(0)` — which contains the null segment `{(τ, τe) : τ ∈ [0, 1]}` —
is **not** a Cauchy surface (DEC-14). This is a local causality: it is not built with
`Causality.ofRelation`. -/
theorem minkowski_dec15 (hn : 0 < n) :
    (minkowski n).IsCauchyTimeFunction (dec15Time n hn) ∧
      (∀ τ ∈ Icc (0 : ℝ) 1, dec15Time n hn (τ, τ • unitVec n hn) = 0) ∧
      (∃ x y : Minkowski n, (minkowski n).le ⊤ x y ∧ x ≠ y ∧ dec15Time n hn x = dec15Time n hn y) ∧
      ¬ (minkowski n).IsCauchySurface (dec15Time n hn ⁻¹' {0}) := by
  have h := staticCausality.not_strict_and_not_isCauchySurface (dist_smul_unitVec hn)
    (g := clampCoord n hn) (fun τ hτ => clampCoord_smul hn hτ)
  refine ⟨staticCausality.isCauchyTimeFunction_sub (clampCoord n hn) (clampCoord_lipschitz hn)
    (abs_clampCoord_le hn), fun τ hτ => ?_, h.1, h.2⟩
  simp [dec15Time, clampCoord_smul hn hτ]

/-- **(i) on `ℝ^{1,1}`**, the case of `Causal.Geroch`'s SCOPE and `campaign/WP-7`. -/
theorem minkowski2_dec15 :
    (minkowski 1).IsCauchyTimeFunction (dec15Time 1 one_pos) ∧
      (∃ x y : Minkowski 1, (minkowski 1).le ⊤ x y ∧ x ≠ y ∧
        dec15Time 1 one_pos x = dec15Time 1 one_pos y) ∧
      ¬ (minkowski 1).IsCauchySurface (dec15Time 1 one_pos ⁻¹' {0}) :=
  ⟨(minkowski_dec15 one_pos).1, (minkowski_dec15 one_pos).2.2⟩

/-- **Sanity, the other side of DEC-15.** The time coordinate `T(t, x) = t` is a Cauchy time
function strictly increasing along `≤`, so `geroch_ii_imp_iii` applies to it. -/
theorem minkowski_time_strict :
    (minkowski n).IsCauchyTimeFunction (fun p => p.1) ∧
      ∀ x y : Minkowski n, (minkowski n).le ⊤ x y → x ≠ y → x.1 < y.1 := by
  refine ⟨staticCausality.isCauchyTimeFunction_fst, fun x y h hne => ?_⟩
  have h' := minkowski_le_top_iff.1 h
  rcases (le_trans (norm_nonneg _) h').eq_or_lt with he | hlt
  · exfalso
    have : ‖y.2 - x.2‖ = 0 := le_antisymm (by linarith) (norm_nonneg _)
    rw [norm_eq_zero, sub_eq_zero] at this
    exact hne (Prod.ext (by linarith) this.symm)
  · linarith

/-! ### (ii) No maximal chain -/

theorem nontrivial_euclidean (hn : 0 < n) : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
  nontrivial_of_ne (unitVec n hn) 0 fun h => by
    have := norm_unitVec hn
    rw [h, norm_zero] at this
    exact zero_ne_one this

/-- **(ii) No maximal causal chain in `ℝ^{1,n}`, `n ≥ 1`** (`def:maximal_chain` as written,
`Causal.Chains`). -/
theorem minkowski_not_isMaximalChain (hn : 0 < n) (S : Set (Minkowski n)) :
    ¬ (minkowski n).IsMaximalChain S :=
  haveI := nontrivial_euclidean hn
  staticCausality.not_isMaximalChain S

/-- Consequently `def:causally_connected`, as written, fails in `ℝ^{1,n}`, `n ≥ 1`. -/
theorem minkowski_not_causallyConnected (hn : 0 < n) : ¬ (minkowski n).CausallyConnected := by
  intro h
  obtain ⟨S, hS, -⟩ := h (0, 0) (0, 0) ((minkowski n).le_refl trivial)
  exact minkowski_not_isMaximalChain hn S hS

/-- And `def:causally_complete` holds vacuously in `ℝ^{1,n}`, `n ≥ 1`. -/
theorem minkowski_causallyComplete (hn : 0 < n) : (minkowski n).CausallyComplete :=
  fun S hS => absurd hS (minkowski_not_isMaximalChain hn S)

end Causal
