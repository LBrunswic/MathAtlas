import CausalScaffold.Flat.Nonloxodromic
import Mathlib.Analysis.InnerProductSpace.MeanErgodic

/-!
# `CausalScaffold.Flat.TitsNull` — a discrete null-fixing all-elliptic group is virtually abelian in its linear parts

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §9.2–9.3,
the gap of Prop 9.1 at l.2621–2622 of the **labelled** `papers/barbot/legacy/labeled/GHFspace.tex`
(DEC-50: "proved, not carried as a named external"). Package WP-34g-TitsNull.

**No ledger label is certified here.** The statement is not one of Barbot's environments: it is
the `Prop` `TitsVirtuallyAbelianNull d` of `Flat/Nonloxodromic` (not redefined here), which the
§9 assembly `nonloxodromic` carries as a hypothesis for the branch the paper overlooks.

* `titsVirtuallyAbelianNull` (every `d`) — `TitsVirtuallyAbelianNull d`, **proved, no `sorry`**,
  from the reductions below, the deep step `exists_commute_screenRot_of_discrete` (step 4, with
  `ε = 1/64`; proved elementarily — Zassenhaus' halving, the Engel property of near-identity
  rotation parts from discreteness, Frobenius' lemma through the mean ergodic theorem — so
  neither Auslander's theorem nor Tits' alternative is used) and `exists_comm_linOf_of_local`
  (steps 5–6). `titsVirtuallyAbelianNull_of_le_two` (`d ≤ 2`, Barbot's `n ≤ 3`): the cheaper
  special case, where step 4 holds for every `ε` and needs no discreteness
  (`commute_screenRot_of_le_two`, the screen having dimension `≤ 1`; `finrank_nullPlaneSpan`).
* Proved (no `sorry`): the **screen** of `v₀` (`nullPlaneSpan`, `nullScreen`, `screenProj`, a
  concrete section of Barbot's `P̄₀ = v₀^⊥/ℝv₀`, l.2623–2629); the **rotation part**
  `screenRot v₀ A` (Barbot's natural action of `L(Γ)` on `P̄₀`, made a unital endomorphism of
  `𝐌ⁿ`), multiplicative on the stabiliser of `v₀` (`screenRot_mul`, `screenRot_one`) and
  uniformly bounded (`norm_screenRot_le`, from `norm_screenProj_apply_screenProj`: it preserves
  `q̄₀`); **an elliptic Lorentz map fixing `v₀` with trivial rotation part is `id`**
  (`eq_one_of_screenRot_eq_one`); the generic **commutation on a generated subgroup**
  (`commute_of_mem_closure`) and **finite index by compactness** (`relIndex_closure_ne_zero`:
  the elements whose bounded "rotation part" is `ε`-close to `1` generate a subgroup of finite
  index — pigeonhole in a totally bounded ball).

> In this case, up to finite index, $L(\Gamma)$ preserves a isotropic vector $v_{0}$
> and $\Gamma$ contains a parabolic element $\gamma_{1}$. (l.2621–2622)

> Denote by $P_{0}$ the orthogonal $v_{0}^{\perp}$, by $\Delta_{0} = P_{0}^{\perp}$
> the direction containing $v_{0}$, and by $\overline{P}_{0}$ the quotient space
> $P_{0}\slash \Delta_{0}$. The lorentzian quadratic form on \mink induces on
> $\overline{P}_{0}$ an euclidean quadratic form $\bar{q}_{0}$ which is preserved by the
> natural action of $L(\Gamma)$. (l.2623–2629)

> If not, $G_{0}$ admits only elliptic elements. Therefore, $1$-parameter subgroups
> are all compact: it follows that $G_{0}$ is compact, hence, contained in a conjugate of
> $SO(n-1)$. (l.2596–2597)

> Let $\Gamma$ be a discrete subgroup of $\mbox{Aff}(n, {\mathbb R})$.
> Then, the identity component $G_{0}$ of
> the closure of $L(\Gamma)$ in $GL(n, {\mathbb R})$ is nilpotent. (l.1699–1701, Barbot's
> Auslander–Carrière–Dal'bo theorem; **not used** here: step 4 replaces it, see below)

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; `Minkowski d` has `d` spatial
dimensions, so Barbot's `n` is `d + 1`, and the screen `P̄₀` has dimension `n − 2 = d − 1`.

## The proof (sketch first, then the Lean)

Let `Γ ≤ Isom(𝐌ⁿ)` be discrete (`isomTopology`), `v₀ ≠ 0` null, `L(γ) v₀ = v₀` and `L(γ)`
elliptic for every `γ ∈ Γ`.

1. **The screen.** `C = span {v₀, e₀}` (`e₀ = timeUnit d`) contains a timelike vector, so
   `𝐌ⁿ = S ⊕ C` with `S = C^⊥` (`isCompl_minkOrth_of_timelike`); `S ⊆ e₀^⊥` is euclidean
   (`minkQ = ‖·‖²` there, the sup norm being `‖x‖` on `{t = 0}`), and `S ≅ P̄₀` (it is a
   complement of `ℝv₀` in `v₀^⊥`). `π` is the projection on `S` along `C`. Key fact: for
   `A ∈ SO₀(1,d)` fixing `v₀` and `p ∈ S`, `A p − π(A p) ∈ C ∩ v₀^⊥ = ℝ v₀`
   (`sub_screenProj_apply_mem`; `⟨e₀ | v₀⟩ ≠ 0` because a null vector orthogonal to a timelike
   one is `0`).
2. **The rotation part** `ρ(A) = π A π + (1 − π)`. By 1, `π A (B π x) = π A (π B π x)`, hence
   `ρ(AB) = ρ(A) ρ(B)` on the stabiliser of `v₀`, `ρ(1) = 1`; and `‖π A π x‖ = ‖π x‖`
   (`q̄₀` is preserved, l.2627–2629), so `‖ρ(A)‖ ≤ M := ‖π‖ + ‖1 − π‖` for all such `A`.
3. **Trivial rotation part + elliptic ⇒ identity.** If `ρ(A) = 1` then `A w − w ∈ ℝ v₀` for
   every `w ∈ v₀^⊥`. `A` fixes a timelike `u` (elliptic); on `W^⊥`, `W = span {u, v₀}`,
   `A w − w = a v₀` and `0 = ⟨u | A w − w⟩ = a ⟨u | v₀⟩` forces `a = 0`; `A` fixes `W`; and
   `𝐌ⁿ = W ⊕ W^⊥` (`u` timelike). So `A = 1`.
4. **The deep step (Zassenhaus–Bieberbach, elementary; `ε = 1/64`).** Any two elements of
   `ρ(Γ)` within `1/64` of `1` commute (`exists_commute_screenRot_of_discrete`, through
   `commute_screenRot_of_lt_inv64`). `ρ(A)` acts as `(t, y) ↦ (t, R y)` with `R` orthogonal on
   `ℝᵈ` (`fst_screenRot_apply`, `norm_screenRot_apply`: an isometry of the sup norm).
   (a) *Halving* (`norm_commutator_le_half`): in a normed ring, `XYX⁻¹Y⁻¹ − 1 =
   ((X−1)(Y−1) − (Y−1)(X−1))X⁻¹Y⁻¹`, so `‖X^{±1} − 1‖ ≤ 1/32` and `‖Y^{±1} − 1‖ ≤ m ≤ 3` give
   `‖[X,Y]^{±1} − 1‖ ≤ m/2`; iterated, `‖F hₖ − 1‖ ≤ 3·2⁻ᵏ` for `hₖ = [g, hₖ₋₁]`
   (`norm_iterate_commutator_le`).
   (b) *Engel* (`exists_iterate_commutator_eq_one`): `g ∈ Γ` with `‖ρ(g) − 1‖ < 1/64` and any
   `h ∈ Γ` have `hₙ = 1` for some `n`. The affine extensions `ĝ (y, s) = (L(g) y + s τ(g), s)`
   (`affExt`) are block upper triangular in the flag `ℝ v₀ ⊂ v₀^⊥ ⊂ 𝐌ⁿ ⊂ 𝐌ⁿ × ℝ`
   (`flagProj`, `flagProj_affExt_lower`) with diagonal `(1, ρ, 1, 1)` (`flagProj_affExt_diag`);
   conjugating by the scaling `D_K = ∑ Kⁱ Pᵢ` shrinks the upper blocks by `K⁻¹`
   (`norm_scaleBy_conj_sub_le`), so for `K` large `D ĝ^{±1} D⁻¹` is `1/32`-close to `1` and
   `D ĥ^{±1} D⁻¹` is `3`-close (`exists_good_scaling`); by (a) `ĥₖ → 1`, and discreteness
   (`exists_affExt_isolated`) makes `hₖ = 1`. This is Bieberbach's contraction, with the null
   rotations and translations of `G = SO(d − 1) ⋉ N` absorbed by the scaling.
   (c) *Frobenius* (`commute_screenRot_of_commute_conj`): if `ρ(A)` commutes with `ρ(B A B⁻¹)`
   and `‖ρ(B) − 1‖ < 1/2`, then `c = [ρA, ρB]` has `cⁿ = ρ(A)ⁿ ρ(B) ρ(A)⁻ⁿ ρ(B)⁻¹`, all within
   `2‖ρ(B) − 1‖ < 1` of `1`; no small subgroups (`screenRot_eq_one_of_forall_pow`, from von
   Neumann's mean ergodic theorem `eq_self_of_forall_iterate_near`) gives `c = 1`.
   (d) *Backward induction* (`commute_screenRot_of_iterate_eq_one`): from `hₙ = 1`, (c) carries
   "`ρ(g)` commutes with `ρ(hₖ)`" from `k = n` down to `k = 0`.
   No ellipticity is used, and neither Auslander's theorem (Barbot's `bthm:ausl`, l.1696–1703)
   nor Tits' alternative: the Lie-theoretic route recorded in the earlier tag (Auslander +
   Cartan + compact solvable ⇒ torus) is superseded.
5. **Finite index.** Let `Γ' = ⟨γ ∈ Γ : ‖ρ(γ) − 1‖ < ε⟩`. If `ρ(r₁), ρ(r₂)` lie in one ball of
   radius `δ = ε / (2(|M|+1))`, then `ρ(r₁⁻¹ r₂) − 1 = ρ(r₁⁻¹)(ρ(r₂) − ρ(r₁))` has norm `< ε`,
   so `r₁ Γ' = r₂ Γ'`; the ball `B̄(0, M)` of the finite-dimensional `End(𝐌ⁿ)` is covered by
   finitely many `δ`-balls, so `[Γ : Γ'] < ∞` (`relIndex_closure_ne_zero`).
6. **Conclusion.** On `Γ'` the rotation parts commute (they do on the generators, 4, and `ρ` is
   multiplicative: `commute_of_mem_closure`). For `g, h ∈ Γ'`, `c = g h g⁻¹ h⁻¹ ∈ Γ` has
   `ρ(L(c)) = 1` and is elliptic, so `L(c) = 1` by 3: `L(g) L(h) = L(h) L(g)`.

**Checked against the counterexample** (SCOPE finding (7) of `Flat/Nonloxodromic`; `d = 5`,
`P̄₀ = ℝ⁴ ≅ ℍ`, the linear maps with `NolParam`s `(L_a, 0, 0, 0, 0)`, `(L_b, 0, e, 0, 0)`, `a, b` a
free pair of unit quaternions): there `ρ(Γ)` is the free group `⟨L_a, L_b⟩`, dense in a copy of
`SU(2)`, so non-commuting elements of `ρ(Γ)` accumulate at `1` — step 4 fails, and only there:
steps 1–3 and 5–6 use no discreteness. Consistently, that `Γ` is not discrete (its closure
contains the `SO(4)`-elements `z ↦ q z`). Discreteness is spent in step 4 alone, at the single
point (b) where the iterated commutators `hₖ → 1` are forced to equal `1`.

## Hypothesis checklist

Barbot states no hypotheses for this step (he does not state the step at all: it is the gap of
l.2621–2622, DEC-50), so the "paper hypothesis" column lists the hypotheses of the project `Prop`
`TitsVirtuallyAbelianNull` of `Flat/Nonloxodromic`, read off the §9 situation at l.2596–2629.

| paper hypothesis | here |
|---|---|
| `Γ` discrete in `Isom(𝐌ⁿ)` (`isomTopology`) | ✓ carried; spent only in step 4(b) (`exists_affExt_isolated` inside `exists_iterate_commutator_eq_one`); not needed when `d ≤ 2` |
| `v₀ ≠ 0`, `minkQ v₀ = 0` | ✓ carried (the screen and step 3) |
| `L(γ) v₀ = v₀` for `γ ∈ Γ` | ✓ carried (multiplicativity of `ρ`) |
| every `L(γ)` elliptic | ✓ carried; spent only in step 3 (commutators); the deep step (step 4) does not need it |

## SCOPE (disclosed)

* **Sorries (0).** The deep step `exists_commute_screenRot_of_discrete` (previously the one
  tagged `sorry`, `TitsVirtuallyAbelianNull/Auslander`) is proved by the elementary route of
  step 4, so `titsVirtuallyAbelianNull` (every `d`) uses only `propext`, `Classical.choice`,
  `Quot.sound`. No named external is used (DEC-50): in particular not
  `AuslanderCarriereDalbo` (`Flat/Externals`, `bthm:ausl`), which would not have sufficed on its
  own (it makes `(closure L(Γ))⁰` nilpotent, but reaching the elements of `ρ(Γ)` near `1` from
  it needs that identity component open, i.e. Cartan's theorem).
* `ρ` is defined through the screen `S = {v₀, e₀}^⊥`, a section of Barbot's quotient `P̄₀`
  (mathlib quotients by a submodule would also do; the section makes `ρ` an endomorphism of
  `𝐌ⁿ` and gives the norm for free). The choice of `e₀` is immaterial to the statement.
* The deep step is stated with `ε` depending on `Γ` (its original statement, unchanged); the
  proof gives the uniform `ε = 1/64`, independent of `Γ`, `v₀` and `d` (a quantitative
  Zassenhaus neighbourhood; for a finite `ρ(Γ)` it is Frobenius' classical commutation of
  near-identity elements).
* Non-vacuity: `titsVirtuallyAbelianNull_of_le_two` covers `d = 0, 1, 2` (Barbot's `n ≤ 3`);
  `Flat/Nonloxodromic`'s `titsVirtuallyAbelianNull_zero` is the degenerate `d = 0`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
package WP-34g-TitsNull (DEC-50).
-/

namespace Causal.Flat

open Set Function Filter Topology Submodule Module

variable {d : ℕ}

/-! ## §1 Generic group theory: commutation on a generated subgroup, finite index -/

section Generic

variable {G X : Type*} [Group G]

/-- **Commutation propagates to a generated subgroup.** If `f : G → X` is multiplicative on a
subgroup `Γ` with `f 1 = 1`, and the values of `f` on `S ⊆ Γ` pairwise commute, then so do its
values on `closure S`. -/
theorem commute_of_mem_closure [Monoid X] {Γ : Subgroup G} {f : G → X}
    (hmul : ∀ a ∈ Γ, ∀ b ∈ Γ, f (a * b) = f a * f b) (hone : f 1 = 1) {S : Set G}
    (hS : S ⊆ Γ) (hc : ∀ a ∈ S, ∀ b ∈ S, Commute (f a) (f b)) {a b : G}
    (ha : a ∈ Subgroup.closure S) (hb : b ∈ Subgroup.closure S) : Commute (f a) (f b) := by
  have hle : Subgroup.closure S ≤ Γ := (Subgroup.closure_le Γ).2 hS
  have key : ∀ y : X, (∀ s ∈ S, Commute (f s) y) → ∀ g ∈ Subgroup.closure S,
      Commute (f g) y := by
    intro y hy g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact hy x hx
    | one => rw [hone]; exact Commute.one_left y
    | mul x z hx hz ihx ihz => rw [hmul x (hle hx) z (hle hz)]; exact ihx.mul_left ihz
    | inv x hx ihx =>
      have h1 : f x⁻¹ * f x = 1 := by
        rw [← hmul _ (Γ.inv_mem (hle hx)) _ (hle hx), inv_mul_cancel, hone]
      have h2 : f x * f x⁻¹ = 1 := by
        rw [← hmul _ (hle hx) _ (Γ.inv_mem (hle hx)), mul_inv_cancel, hone]
      let u : Xˣ := ⟨f x, f x⁻¹, h2, h1⟩
      exact (show Commute (u : X) y from ihx).units_inv_left
  exact key (f b) (fun s hs => (key (f s) (fun t ht => hc t ht s hs) b hb).symm) a ha

/-- **Finite index by compactness.** If `f : G → X` (a proper normed ring) is multiplicative on
`Γ`, `f 1 = 1`, and bounded on `Γ`, then for every `ε > 0` the elements of `Γ` with
`‖f γ − 1‖ < ε` generate a subgroup of finite index in `Γ`: two representatives whose images lie
in one small ball differ by a generator. -/
theorem relIndex_closure_ne_zero [NormedRing X] [ProperSpace X] {Γ : Subgroup G} {f : G → X}
    (hmul : ∀ a ∈ Γ, ∀ b ∈ Γ, f (a * b) = f a * f b) (hone : f 1 = 1) {M : ℝ}
    (hM : ∀ g ∈ Γ, ‖f g‖ ≤ M) {ε : ℝ} (hε : 0 < ε) :
    (Subgroup.closure {g | g ∈ Γ ∧ ‖f g - 1‖ < ε}).relIndex Γ ≠ 0 := by
  classical
  set H := Subgroup.closure {g | g ∈ Γ ∧ ‖f g - 1‖ < ε} with hH
  set δ := ε / (2 * (|M| + 1)) with hδdef
  have hM1 : 0 < |M| + 1 := by positivity
  have hδ : 0 < δ := by positivity
  obtain ⟨t, htf, hcov⟩ :=
    (Metric.totallyBounded_iff.1 (isCompact_closedBall (0 : X) M).totallyBounded) δ hδ
  have hcov' : ∀ q : Γ ⧸ H.subgroupOf Γ, ∃ y ∈ t, dist (f (q.out : G)) y < δ := by
    intro q
    have hq : f (q.out : G) ∈ Metric.closedBall (0 : X) M := by
      rw [mem_closedBall_zero_iff]; exact hM _ q.out.2
    obtain ⟨y, hyt, hy⟩ := mem_iUnion₂.1 (hcov hq)
    exact ⟨y, hyt, hy⟩
  choose c hct hcd using hcov'
  haveI : Finite t := htf.to_subtype
  haveI : Finite (Γ ⧸ H.subgroupOf Γ) := by
    refine Finite.of_injective (fun q => (⟨c q, hct q⟩ : t)) fun q₁ q₂ h12 => ?_
    have hc12 : c q₁ = c q₂ := congrArg Subtype.val h12
    have hd : ‖f (q₂.out : G) - f (q₁.out : G)‖ < 2 * δ := by
      have h1 := hcd q₁
      have h2 := hcd q₂
      rw [← hc12] at h2
      rw [← dist_eq_norm]
      calc dist (f (q₂.out : G)) (f (q₁.out : G))
          ≤ dist (f (q₂.out : G)) (c q₁) + dist (f (q₁.out : G)) (c q₁) :=
            dist_triangle_right _ _ _
        _ < δ + δ := add_lt_add h2 h1
        _ = 2 * δ := by ring
    have hr₁ := q₁.out.2
    have hr₂ := q₂.out.2
    have hmem : (q₁.out⁻¹ * q₂.out : Γ) ∈ H.subgroupOf Γ := by
      rw [Subgroup.mem_subgroupOf]
      apply Subgroup.subset_closure
      refine ⟨(q₁.out⁻¹ * q₂.out : Γ).2, ?_⟩
      have e : f ((q₁.out⁻¹ * q₂.out : Γ) : G) - 1 =
          f ((q₁.out : G)⁻¹) * (f (q₂.out : G) - f (q₁.out : G)) := by
        rw [mul_sub, ← hmul _ (Γ.inv_mem hr₁) _ hr₂, ← hmul _ (Γ.inv_mem hr₁) _ hr₁,
          inv_mul_cancel, hone]
        rfl
      rw [e]
      have hinvM : ‖f ((q₁.out : G)⁻¹)‖ ≤ |M| + 1 :=
        (hM _ (Γ.inv_mem hr₁)).trans ((le_abs_self M).trans (le_add_of_nonneg_right zero_le_one))
      calc ‖f ((q₁.out : G)⁻¹) * (f (q₂.out : G) - f (q₁.out : G))‖
          ≤ ‖f ((q₁.out : G)⁻¹)‖ * ‖f (q₂.out : G) - f (q₁.out : G)‖ := norm_mul_le _ _
        _ ≤ (|M| + 1) * ‖f (q₂.out : G) - f (q₁.out : G)‖ :=
            mul_le_mul_of_nonneg_right hinvM (norm_nonneg _)
        _ < (|M| + 1) * (2 * δ) := mul_lt_mul_of_pos_left hd hM1
        _ = ε := by rw [hδdef]; field_simp
    rw [← QuotientGroup.out_eq' q₁, ← QuotientGroup.out_eq' q₂]
    exact QuotientGroup.eq.2 hmem
  exact Subgroup.index_ne_zero_of_finite

end Generic

/-! ## §2 The screen of a null vector and the rotation part -/

section Screen

variable (v₀ : Minkowski d)

/-- `C = span {v₀, e₀}`, a Lorentzian plane (it contains the time unit `e₀`). -/
noncomputable def nullPlaneSpan : Submodule ℝ (Minkowski d) := span ℝ {v₀, timeUnit d}

/-- **The screen** `S = {v₀, e₀}^⊥`: a euclidean complement of `ℝ v₀` in `v₀^⊥`, i.e. a section
of Barbot's `P̄₀ = v₀^⊥ / ℝ v₀` (l.2623–2626). -/
noncomputable def nullScreen : Submodule ℝ (Minkowski d) := minkOrth (nullPlaneSpan v₀)

theorem timeUnit_mem_nullPlaneSpan : timeUnit d ∈ nullPlaneSpan v₀ :=
  subset_span (mem_insert_of_mem _ rfl)

theorem self_mem_nullPlaneSpan : v₀ ∈ nullPlaneSpan v₀ := subset_span (mem_insert _ _)

theorem isCompl_nullScreen : IsCompl (nullScreen v₀) (nullPlaneSpan v₀) :=
  (isCompl_minkOrth_of_timelike (timeUnit_mem_nullPlaneSpan v₀)
    (by rw [minkQ_timeUnit]; norm_num)).symm

/-- The projection `π` on the screen along `C`. -/
noncomputable def screenProj : Minkowski d →ₗ[ℝ] Minkowski d :=
  (nullScreen v₀).projection (nullPlaneSpan v₀) (isCompl_nullScreen v₀)

theorem screenProj_mem (x : Minkowski d) : screenProj v₀ x ∈ nullScreen v₀ :=
  projection_apply_mem _ x

theorem screenProj_of_mem {p : Minkowski d} (hp : p ∈ nullScreen v₀) : screenProj v₀ p = p :=
  projection_apply_of_mem_left _ hp

theorem screenProj_of_mem_plane {c : Minkowski d} (hc : c ∈ nullPlaneSpan v₀) :
    screenProj v₀ c = 0 :=
  projection_apply_of_mem_right _ hc

theorem sub_screenProj_mem (x : Minkowski d) : x - screenProj v₀ x ∈ nullPlaneSpan v₀ :=
  sub_projection_mem _ x

theorem screenProj_screenProj (x : Minkowski d) :
    screenProj v₀ (screenProj v₀ x) = screenProj v₀ x :=
  screenProj_of_mem v₀ (screenProj_mem v₀ x)

theorem screenProj_self : screenProj v₀ v₀ = 0 :=
  screenProj_of_mem_plane v₀ (self_mem_nullPlaneSpan v₀)

theorem screenProj_sub_screenProj (x : Minkowski d) :
    screenProj v₀ (x - screenProj v₀ x) = 0 := by
  rw [map_sub, screenProj_screenProj, sub_self]

theorem minkB_self_of_mem_nullScreen {p : Minkowski d} (hp : p ∈ nullScreen v₀) :
    minkB v₀ p = 0 :=
  hp v₀ (self_mem_nullPlaneSpan v₀)

theorem fst_eq_zero_of_mem_nullScreen {p : Minkowski d} (hp : p ∈ nullScreen v₀) : p.1 = 0 := by
  have h : minkB (timeUnit d) p = 0 := hp _ (timeUnit_mem_nullPlaneSpan v₀)
  simp only [minkB, timeUnit, one_mul, inner_zero_left, add_zero, neg_eq_zero] at h
  exact h

/-- On the screen `minkQ` is the square of the norm (`q̄₀` is euclidean, l.2627–2628). -/
theorem minkQ_eq_norm_sq_of_mem_nullScreen {p : Minkowski d} (hp : p ∈ nullScreen v₀) :
    minkQ p = ‖p‖ ^ 2 := by
  have h1 := fst_eq_zero_of_mem_nullScreen v₀ hp
  rw [minkQ, h1, Prod.norm_def, h1, norm_zero, max_eq_right (norm_nonneg _)]
  ring

variable {v₀}

/-- `⟨e₀ | v₀⟩ ≠ 0` for a nonzero null `v₀`. -/
theorem minkB_timeUnit_ne_zero (hv0 : v₀ ≠ 0) (hv : minkQ v₀ = 0) :
    minkB (timeUnit d) v₀ ≠ 0 := fun h =>
  (minkQ_pos_of_orth_timelike (by rw [minkQ_timeUnit]; norm_num) h hv0).ne' hv

/-- **`C ∩ v₀^⊥ = ℝ v₀`.** -/
theorem mem_span_of_mem_nullPlaneSpan (hv0 : v₀ ≠ 0) (hv : minkQ v₀ = 0) {c : Minkowski d}
    (hc : c ∈ nullPlaneSpan v₀) (hcv : minkB c v₀ = 0) : c ∈ ℝ ∙ v₀ := by
  obtain ⟨a, b, rfl⟩ := mem_span_pair.1 hc
  have hb : b = 0 := by
    rw [minkB_add_left, minkB_smul_left, minkB_smul_left, ← minkQ_eq_minkB, hv, mul_zero,
      zero_add] at hcv
    exact (mul_eq_zero.1 hcv).resolve_right (minkB_timeUnit_ne_zero hv0 hv)
  rw [hb, zero_smul, add_zero]
  exact smul_mem _ _ (mem_span_singleton_self v₀)

/-- **Key fact**: for `A ∈ SO₀(1,d)` fixing `v₀` and `p` in the screen, `A p − π(A p) ∈ ℝ v₀`. -/
theorem sub_screenProj_apply_mem (hv0 : v₀ ≠ 0) (hv : minkQ v₀ = 0)
    {A : Minkowski d ≃ₗ[ℝ] Minkowski d} (hA : A ∈ lorentz d) (hfix : A v₀ = v₀)
    {p : Minkowski d} (hp : p ∈ nullScreen v₀) : A p - screenProj v₀ (A p) ∈ ℝ ∙ v₀ := by
  refine mem_span_of_mem_nullPlaneSpan hv0 hv (sub_screenProj_mem v₀ _) ?_
  rw [minkB_sub_left, minkB_comm (screenProj v₀ (A p)),
    minkB_self_of_mem_nullScreen v₀ (screenProj_mem v₀ _), sub_zero]
  conv_lhs => rw [← hfix]
  rw [minkB_map (lorentz.minkQ_apply hA), minkB_comm]
  exact minkB_self_of_mem_nullScreen v₀ hp

/-- `π (A (B p)) = π (A (π (B p)))` for `p` in the screen. -/
theorem screenProj_apply_apply (hv0 : v₀ ≠ 0) (hv : minkQ v₀ = 0)
    {A B : Minkowski d ≃ₗ[ℝ] Minkowski d} (hfA : A v₀ = v₀) (hB : B ∈ lorentz d)
    (hfB : B v₀ = v₀) {p : Minkowski d} (hp : p ∈ nullScreen v₀) :
    screenProj v₀ (A (B p)) = screenProj v₀ (A (screenProj v₀ (B p))) := by
  obtain ⟨a, ha⟩ := mem_span_singleton.1 (sub_screenProj_apply_mem hv0 hv hB hfB hp)
  have e : B p = screenProj v₀ (B p) + a • v₀ := by rw [ha]; abel
  conv_lhs => rw [e]
  rw [map_add, map_smul, hfA, map_add, map_smul, screenProj_self, smul_zero, add_zero]

/-- **The rotation part** `ρ(A) = π A π + (1 − π)`: Barbot's natural action of `L(Γ)` on
`P̄₀` (l.2627–2629), read on the screen, made a unital endomorphism of `𝐌ⁿ`. -/
noncomputable def screenRot (v₀ : Minkowski d) (A : Minkowski d ≃ₗ[ℝ] Minkowski d) :
    Minkowski d →L[ℝ] Minkowski d :=
  LinearMap.toContinuousLinearMap
    (screenProj v₀ ∘ₗ (A : Minkowski d →ₗ[ℝ] Minkowski d) ∘ₗ screenProj v₀ +
      (LinearMap.id - screenProj v₀))

theorem screenRot_apply (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (x : Minkowski d) :
    screenRot v₀ A x = screenProj v₀ (A (screenProj v₀ x)) + (x - screenProj v₀ x) := rfl

theorem screenRot_one : screenRot v₀ (1 : Minkowski d ≃ₗ[ℝ] Minkowski d) = 1 := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [screenRot_apply, show (1 : Minkowski d ≃ₗ[ℝ] Minkowski d) (screenProj v₀ x) =
      screenProj v₀ x from rfl, screenProj_screenProj,
    show (1 : Minkowski d →L[ℝ] Minkowski d) x = x from rfl]
  abel

/-- **`ρ` is multiplicative on the stabiliser of `v₀`.** -/
theorem screenRot_mul (hv0 : v₀ ≠ 0) (hv : minkQ v₀ = 0)
    {A B : Minkowski d ≃ₗ[ℝ] Minkowski d} (hfA : A v₀ = v₀) (hB : B ∈ lorentz d)
    (hfB : B v₀ = v₀) : screenRot v₀ (A * B) = screenRot v₀ A * screenRot v₀ B := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [show (screenRot v₀ A * screenRot v₀ B) x = screenRot v₀ A (screenRot v₀ B x) from rfl,
    screenRot_apply, screenRot_apply, screenRot_apply, LinearEquiv.mul_apply]
  have hy : screenProj v₀ (screenProj v₀ (B (screenProj v₀ x)) + (x - screenProj v₀ x)) =
      screenProj v₀ (B (screenProj v₀ x)) := by
    rw [map_add, screenProj_sub_screenProj, add_zero, screenProj_screenProj]
  rw [hy, screenProj_apply_apply hv0 hv hfA hB hfB (screenProj_mem v₀ x)]
  abel

/-- **`ρ(A)` preserves `q̄₀`**: `‖π (A (π x))‖ = ‖π x‖`. -/
theorem norm_screenProj_apply_screenProj (hv0 : v₀ ≠ 0) (hv : minkQ v₀ = 0)
    {A : Minkowski d ≃ₗ[ℝ] Minkowski d} (hA : A ∈ lorentz d) (hfix : A v₀ = v₀)
    (x : Minkowski d) : ‖screenProj v₀ (A (screenProj v₀ x))‖ = ‖screenProj v₀ x‖ := by
  set p := screenProj v₀ x with hpdef
  have hp : p ∈ nullScreen v₀ := screenProj_mem v₀ x
  set q := screenProj v₀ (A p) with hqdef
  have hq : q ∈ nullScreen v₀ := screenProj_mem v₀ _
  obtain ⟨a, ha⟩ := mem_span_singleton.1 (sub_screenProj_apply_mem hv0 hv hA hfix hp)
  have hqe : q = A p + (-a) • v₀ := by rw [neg_smul, ha]; abel
  have hB0 : minkB (A p) v₀ = 0 := by
    conv_lhs => rw [← hfix]
    rw [minkB_map (lorentz.minkQ_apply hA), minkB_comm]
    exact minkB_self_of_mem_nullScreen v₀ hp
  have hQ : minkQ q = minkQ p := by
    rw [hqe, minkQ_add, minkQ_smul, hv, minkB_smul_right, hB0, lorentz.minkQ_apply hA]
    ring
  rw [minkQ_eq_norm_sq_of_mem_nullScreen v₀ hq, minkQ_eq_norm_sq_of_mem_nullScreen v₀ hp] at hQ
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hQ

/-- The uniform bound `M = ‖π‖ + ‖1 − π‖` on the rotation parts. -/
noncomputable def screenBound (v₀ : Minkowski d) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (screenProj v₀)‖ +
    ‖LinearMap.toContinuousLinearMap (LinearMap.id - screenProj v₀)‖

/-- **The rotation parts are uniformly bounded** on the stabiliser of `v₀`. -/
theorem norm_screenRot_le (hv0 : v₀ ≠ 0) (hv : minkQ v₀ = 0)
    {A : Minkowski d ≃ₗ[ℝ] Minkowski d} (hA : A ∈ lorentz d) (hfix : A v₀ = v₀) :
    ‖screenRot v₀ A‖ ≤ screenBound v₀ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by unfold screenBound; positivity) fun x => ?_
  rw [screenRot_apply]
  have h1 := (LinearMap.toContinuousLinearMap (screenProj v₀)).le_opNorm x
  have h2 := (LinearMap.toContinuousLinearMap (LinearMap.id - screenProj v₀)).le_opNorm x
  rw [LinearMap.coe_toContinuousLinearMap'] at h1 h2
  rw [LinearMap.sub_apply, LinearMap.id_apply] at h2
  calc ‖screenProj v₀ (A (screenProj v₀ x)) + (x - screenProj v₀ x)‖
      ≤ ‖screenProj v₀ (A (screenProj v₀ x))‖ + ‖x - screenProj v₀ x‖ := norm_add_le _ _
    _ = ‖screenProj v₀ x‖ + ‖x - screenProj v₀ x‖ := by
        rw [norm_screenProj_apply_screenProj hv0 hv hA hfix]
    _ ≤ _ := by unfold screenBound; rw [add_mul]; exact add_le_add h1 h2

/-- **An elliptic Lorentz map fixing `v₀` with trivial rotation part is the identity** (step 3):
it moves `v₀^⊥` along `ℝ v₀` only, fixes a timelike `u`, hence fixes `span {u, v₀}` and its
(spacelike) orthogonal. -/
theorem eq_one_of_screenRot_eq_one (hv0 : v₀ ≠ 0) (hv : minkQ v₀ = 0)
    {A : Minkowski d ≃ₗ[ℝ] Minkowski d} (hA : A ∈ lorentz d) (hfix : A v₀ = v₀)
    (hell : IsElliptic A) (h : screenRot v₀ A = 1) : A = 1 := by
  have hscr : ∀ p ∈ nullScreen v₀, A p - p ∈ ℝ ∙ v₀ := by
    intro p hp
    have e := congrArg (fun f : Minkowski d →L[ℝ] Minkowski d => f p) h
    simp only [screenRot_apply, screenProj_of_mem v₀ hp, sub_self, add_zero] at e
    rw [show (1 : Minkowski d →L[ℝ] Minkowski d) p = p from rfl] at e
    have := sub_screenProj_apply_mem hv0 hv hA hfix hp
    rwa [e] at this
  have hperp : ∀ w, minkB v₀ w = 0 → A w - w ∈ ℝ ∙ v₀ := by
    intro w hw
    have hc : w - screenProj v₀ w ∈ ℝ ∙ v₀ := by
      refine mem_span_of_mem_nullPlaneSpan hv0 hv (sub_screenProj_mem v₀ w) ?_
      rw [minkB_sub_left, minkB_comm w, hw, minkB_comm,
        minkB_self_of_mem_nullScreen v₀ (screenProj_mem v₀ w), sub_zero]
    obtain ⟨b, hb⟩ := mem_span_singleton.1 hc
    have hAc : A (w - screenProj v₀ w) = w - screenProj v₀ w := by
      rw [← hb, map_smul, hfix]
    have e : A w - w = A (screenProj v₀ w) - screenProj v₀ w := by
      have : A w = A (w - screenProj v₀ w) + A (screenProj v₀ w) := by
        rw [← map_add, sub_add_cancel]
      rw [this, hAc]; abel
    rw [e]
    exact hscr _ (screenProj_mem v₀ w)
  obtain ⟨u, hu, hAu⟩ := hell.exists_fixed_timelike hA
  have huv : minkB u v₀ ≠ 0 := fun h0 =>
    (minkQ_pos_of_orth_timelike hu.2 h0 hv0).ne' hv
  set W : Submodule ℝ (Minkowski d) := span ℝ {u, v₀} with hWdef
  have huW : u ∈ W := subset_span (mem_insert _ _)
  have hvW : v₀ ∈ W := subset_span (mem_insert_of_mem _ rfl)
  have hc := isCompl_minkOrth_of_timelike huW hu.2
  have hQ := lorentz.minkQ_apply hA
  have hW' : ∀ w ∈ minkOrth W, A w = w := by
    intro w hw
    have hwv : minkB v₀ w = 0 := hw v₀ hvW
    have hwu : minkB u w = 0 := hw u huW
    obtain ⟨a, ha⟩ := mem_span_singleton.1 (hperp w hwv)
    have h1 : minkB u (A w - w) = 0 := by
      rw [minkB_sub_right, hwu, sub_zero]
      conv_lhs => rw [← hAu]
      rw [minkB_map hQ, hwu]
    rw [← ha, minkB_smul_right] at h1
    have ha0 : a = 0 := (mul_eq_zero.1 h1).resolve_right huv
    rw [ha0, zero_smul] at ha
    exact (sub_eq_zero.1 ha.symm)
  have hWfix : ∀ s ∈ W, A s = s := by
    intro s hs
    obtain ⟨a, b, rfl⟩ := mem_span_pair.1 hs
    rw [map_add, map_smul, map_smul, hAu, hfix]
  refine LinearEquiv.ext fun x => ?_
  have hx : x ∈ W ⊔ minkOrth W := by rw [hc.sup_eq_top]; exact mem_top
  obtain ⟨s, hs, w, hw, rfl⟩ := mem_sup.1 hx
  rw [map_add, hWfix s hs, hW' w hw]
  rfl

/-- `v₀` and `e₀` are linearly independent: `C` is a plane. -/
theorem finrank_nullPlaneSpan (hv0 : v₀ ≠ 0) (hv : minkQ v₀ = 0) :
    finrank ℝ (nullPlaneSpan v₀) = 2 := by
  have hli : LinearIndependent ℝ ![v₀, timeUnit d] := by
    refine LinearIndependent.pair_iff.2 fun s t hst => ?_
    have h1 := congrArg (fun w => minkB w v₀) hst
    simp only [minkB_add_left, minkB_smul_left, minkB_zero_left, ← minkQ_eq_minkB, hv,
      mul_zero, zero_add] at h1
    have ht : t = 0 := (mul_eq_zero.1 h1).resolve_right (minkB_timeUnit_ne_zero hv0 hv)
    rw [ht, zero_smul, add_zero] at hst
    exact ⟨(smul_eq_zero.1 hst).resolve_right hv0, ht⟩
  have h2 := finrank_span_eq_card hli
  have hr : Set.range ![v₀, timeUnit d] = {v₀, timeUnit d} := by
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union]
  rw [hr, Fintype.card_fin] at h2
  exact h2

/-- **In `d ≤ 2` (Barbot's `n ≤ 3`) all rotation parts commute**: the screen has dimension
`d − 1 ≤ 1`, where every endomorphism is a scalar (no hypothesis on `A`, `B`). -/
theorem commute_screenRot_of_le_two (hd : d ≤ 2) (hv0 : v₀ ≠ 0) (hv : minkQ v₀ = 0)
    (A B : Minkowski d ≃ₗ[ℝ] Minkowski d) : Commute (screenRot v₀ A) (screenRot v₀ B) := by
  have hrank : finrank ℝ (nullScreen v₀) ≤ 1 := by
    rw [nullScreen, finrank_minkOrth, finrank_nullPlaneSpan hv0 hv]
    omega
  obtain ⟨e, he⟩ := finrank_le_one_iff.1 hrank
  have hsc : ∀ C : Minkowski d ≃ₗ[ℝ] Minkowski d, ∃ a : ℝ,
      screenProj v₀ (C (e : Minkowski d)) = a • (e : Minkowski d) := fun C => by
    obtain ⟨a, ha⟩ := he ⟨screenProj v₀ (C e), screenProj_mem v₀ _⟩
    exact ⟨a, (congrArg Subtype.val ha).symm⟩
  obtain ⟨a, ha⟩ := hsc A
  obtain ⟨b, hb⟩ := hsc B
  have key : ∀ x, screenProj v₀ (A (screenProj v₀ (B (screenProj v₀ x)))) =
      screenProj v₀ (B (screenProj v₀ (A (screenProj v₀ x)))) := by
    intro x
    obtain ⟨c, hc⟩ := he ⟨screenProj v₀ x, screenProj_mem v₀ x⟩
    have hc' : screenProj v₀ x = c • (e : Minkowski d) := (congrArg Subtype.val hc).symm
    simp only [hc', map_smul, ha, hb, smul_smul]
    congr 1
    ring
  have hmul : ∀ C D : Minkowski d ≃ₗ[ℝ] Minkowski d, ∀ x,
      (screenRot v₀ C * screenRot v₀ D) x =
        screenProj v₀ (C (screenProj v₀ (D (screenProj v₀ x)))) + (x - screenProj v₀ x) := by
    intro C D x
    rw [show (screenRot v₀ C * screenRot v₀ D) x = screenRot v₀ C (screenRot v₀ D x) from rfl,
      screenRot_apply, screenRot_apply]
    have hy : screenProj v₀ (screenProj v₀ (D (screenProj v₀ x)) + (x - screenProj v₀ x)) =
        screenProj v₀ (D (screenProj v₀ x)) := by
      rw [map_add, screenProj_sub_screenProj, add_zero, screenProj_screenProj]
    rw [hy]
    abel
  exact ContinuousLinearMap.ext fun x => by rw [hmul, hmul, key]

end Screen

/-! ## §2b The deep step, proved: Zassenhaus–Bieberbach, elementary

Step 4 of the module docstring, in four parts: (4a) the Zassenhaus halving step in a normed ring
(`norm_commutator_le_half`, `norm_iterate_commutator_le`); (4b) no small subgroups on the screen
(`eq_self_of_forall_iterate_near`, the mean ergodic theorem) and Frobenius' lemma for rotation
parts (`commute_screenRot_of_commute_conj`); (4c) the backward induction
(`commute_screenRot_of_iterate_eq_one`); (4d) the Engel property of `g` with `ρ(g)` near `1`
(`exists_iterate_commutator_eq_one`: the affine extension `affExt`, the flag scaling `scaleBy
(flagProj v₀) K`, and discreteness `exists_affExt_isolated`). -/

section NormedRingContract

variable {R : Type*} [NormedRing R]

theorem norm_mul_mul_mul_sub_one_le {X Xi Y Yi : R} (hX : X * Xi = 1) (hY : Y * Yi = 1) :
    ‖X * Y * Xi * Yi - 1‖ ≤ 2 * ‖X - 1‖ * ‖Y - 1‖ * ‖Xi‖ * ‖Yi‖ := by
  have e : X * Y * Xi * Yi - 1 = ((X - 1) * (Y - 1) - (Y - 1) * (X - 1)) * Xi * Yi := by
    have h0 : Y * X * Xi * Yi = 1 := by rw [mul_assoc Y, hX, mul_one, hY]
    calc X * Y * Xi * Yi - 1 = X * Y * Xi * Yi - Y * X * Xi * Yi := by rw [h0]
      _ = _ := by noncomm_ring
  rw [e]
  calc ‖((X - 1) * (Y - 1) - (Y - 1) * (X - 1)) * Xi * Yi‖
      ≤ ‖(X - 1) * (Y - 1) - (Y - 1) * (X - 1)‖ * ‖Xi‖ * ‖Yi‖ := by
        refine (norm_mul_le _ _).trans ?_
        gcongr
        exact norm_mul_le _ _
    _ ≤ (‖X - 1‖ * ‖Y - 1‖ + ‖Y - 1‖ * ‖X - 1‖) * ‖Xi‖ * ‖Yi‖ := by
        gcongr
        exact (norm_sub_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    _ = _ := by ring

theorem norm_conj_mul_sub_one_le {X Xi Y Yi : R} (hX : X * Xi = 1) (hY : Y * Yi = 1) :
    ‖X * Y * Xi * Yi - 1‖ ≤ (‖X‖ * ‖Xi‖ + 1) * ‖Y - 1‖ * ‖Yi‖ := by
  have e : X * Y * Xi * Yi - 1 = (X * (Y - 1) * Xi - (Y - 1)) * Yi := by
    have h1 : X * (Y - 1) * Xi = X * Y * Xi - 1 := by rw [mul_sub, mul_one, sub_mul, hX]
    rw [h1, sub_sub, add_sub_cancel, sub_mul, hY]
  rw [e]
  calc ‖(X * (Y - 1) * Xi - (Y - 1)) * Yi‖ ≤ ‖X * (Y - 1) * Xi - (Y - 1)‖ * ‖Yi‖ := norm_mul_le _ _
    _ ≤ (‖X‖ * ‖Y - 1‖ * ‖Xi‖ + ‖Y - 1‖) * ‖Yi‖ := by
        gcongr
        refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
        exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ = _ := by ring

/-- The arithmetic of the halving step. -/
private theorem halving_arith {a b xi yi δ m : ℝ} (_ha0 : 0 ≤ a) (ha : a ≤ δ) (hδ : δ ≤ 1 / 32)
    (hb0 : 0 ≤ b) (hb : b ≤ m) (hm : m ≤ 3) (hxi0 : 0 ≤ xi) (hxi : xi ≤ 1 + δ) (hyi0 : 0 ≤ yi)
    (hyi : yi ≤ 1 + m) : 2 * a * b * xi * yi ≤ m / 2 := by
  have hm0 : 0 ≤ m := hb0.trans hb
  have h1 : 2 * a * b * xi * yi ≤ 2 * (1 / 32) * m * (1 + 1 / 32) * 4 := by
    have hxi' : xi ≤ 1 + 1 / 32 := hxi.trans (by linarith)
    have hyi' : yi ≤ 4 := hyi.trans (by linarith)
    have := mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left (ha.trans hδ)
      (by norm_num : (0:ℝ) ≤ 2)) hb hb0 (by positivity)) hxi' hxi0 (by positivity)) hyi' hyi0
      (by positivity)
    simpa [mul_assoc] using this
  linarith

/-- **The Zassenhaus halving step** in a normed ring with `‖1‖ ≤ 1`. -/
theorem norm_commutator_le_half (h1 : ‖(1 : R)‖ ≤ 1) {X Xi Y Yi : R} (hX : X * Xi = 1)
    (hY : Y * Yi = 1) {δ m : ℝ} (hXd : ‖X - 1‖ ≤ δ) (hXid : ‖Xi - 1‖ ≤ δ) (hδ : δ ≤ 1 / 32)
    (hYm : ‖Y - 1‖ ≤ m) (hYim : ‖Yi - 1‖ ≤ m) (hm : m ≤ 3) :
    ‖X * Y * Xi * Yi - 1‖ ≤ m / 2 ∧ ‖Y * X * Yi * Xi - 1‖ ≤ m / 2 := by
  have hXi : ‖Xi‖ ≤ 1 + δ := by
    calc ‖Xi‖ = ‖(Xi - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ ‖Xi - 1‖ + ‖(1 : R)‖ := norm_add_le _ _
      _ ≤ 1 + δ := by linarith
  have hYi : ‖Yi‖ ≤ 1 + m := by
    calc ‖Yi‖ = ‖(Yi - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ ‖Yi - 1‖ + ‖(1 : R)‖ := norm_add_le _ _
      _ ≤ 1 + m := by linarith
  refine ⟨(norm_mul_mul_mul_sub_one_le hX hY).trans ?_, (norm_mul_mul_mul_sub_one_le hY hX).trans ?_⟩
  · exact halving_arith (norm_nonneg _) hXd hδ (norm_nonneg _) hYm hm (norm_nonneg _) hXi
      (norm_nonneg _) hYi
  · have := halving_arith (norm_nonneg _) hXd hδ (norm_nonneg _) hYm hm (norm_nonneg _) hXi
      (norm_nonneg _) hYi
    calc 2 * ‖Y - 1‖ * ‖X - 1‖ * ‖Yi‖ * ‖Xi‖ = 2 * ‖X - 1‖ * ‖Y - 1‖ * ‖Xi‖ * ‖Yi‖ := by ring
      _ ≤ m / 2 := this

/-- **Iterated commutators contract**: if `F : G → R` is multiplicative, `F g` and `F g⁻¹` are
`1/32`-close to `1` and `F h`, `F h⁻¹` are `3`-close, the iterated commutators
`h_k = [g, h_{k-1}]` satisfy `‖F h_k − 1‖ ≤ 3 · 2⁻ᵏ`. -/
theorem norm_iterate_commutator_le {G : Type*} [Group G] (h1 : ‖(1 : R)‖ ≤ 1) {F : G → R}
    (hF : ∀ a b, F (a * b) = F a * F b) (hF1 : F 1 = 1) {g h : G} (hg : ‖F g - 1‖ ≤ 1 / 32)
    (hgi : ‖F g⁻¹ - 1‖ ≤ 1 / 32) (hh : ‖F h - 1‖ ≤ 3) (hhi : ‖F h⁻¹ - 1‖ ≤ 3) (k : ℕ) :
    ‖F ((fun x => g * x * g⁻¹ * x⁻¹)^[k] h) - 1‖ ≤ 3 * (1 / 2) ^ k ∧
      ‖F ((fun x => g * x * g⁻¹ * x⁻¹)^[k] h)⁻¹ - 1‖ ≤ 3 * (1 / 2) ^ k := by
  have hinv : ∀ a, F a * F a⁻¹ = 1 := fun a => by rw [← hF, mul_inv_cancel, hF1]
  induction k with
  | zero => simpa using ⟨hh, hhi⟩
  | succ k ih =>
    rw [iterate_succ_apply']
    set x := (fun x => g * x * g⁻¹ * x⁻¹)^[k] h
    have hm : 3 * (1 / 2 : ℝ) ^ k ≤ 3 := by
      have : (1 / 2 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      linarith
    obtain ⟨h1', h2'⟩ := norm_commutator_le_half h1 (hinv g) (hinv x) hg hgi le_rfl ih.1 ih.2 hm
    have e1 : F (g * x * g⁻¹ * x⁻¹) = F g * F x * F g⁻¹ * F x⁻¹ := by simp only [hF]
    have e2 : F (g * x * g⁻¹ * x⁻¹)⁻¹ = F x * F g * F x⁻¹ * F g⁻¹ := by
      rw [show (g * x * g⁻¹ * x⁻¹)⁻¹ = x * g * x⁻¹ * g⁻¹ by group]; simp only [hF]
    rw [e1, e2, pow_succ]
    constructor <;> linarith

end NormedRingContract

section NoSmallSubgroups

/-- **No small subgroups** (through von Neumann's mean ergodic theorem): a contraction `f` of a
Hilbert space all of whose iterates move every `x` by at most `θ ‖x‖`, `θ < 1`, is the identity.
-/
theorem eq_self_of_forall_iterate_near {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E →L[ℝ] E) (hf : ‖f‖ ≤ 1) {θ : ℝ} (hθ : θ < 1)
    (h : ∀ (n : ℕ) (x : E), ‖f^[n] x - x‖ ≤ θ * ‖x‖) (x : E) : f x = x := by
  have hlim := f.tendsto_birkhoffAverage_orthogonalProjection hf x
  set q := (LinearMap.eqLocus (f : E →ₗ[ℝ] E) ((1 : E →L[ℝ] E) : E →ₗ[ℝ] E)).orthogonalProjectionOnto x
    with hq
  set p : E := (q : E) with hp
  have hfp : f p = p := LinearMap.mem_eqLocus.1 q.2
  have hpn : ∀ n, f^[n] p = p := fun n => iterate_fixed hfp n
  have hz : ∀ n, ‖f^[n] x - x‖ ≤ θ * ‖x - p‖ := by
    intro n
    have h' := h n (x - p)
    rw [← ContinuousLinearMap.coe_pow', map_sub, ContinuousLinearMap.coe_pow', hpn] at h'
    rwa [show f^[n] x - p - (x - p) = f^[n] x - x by abel] at h'
  have havg : ∀ N : ℕ, 1 ≤ N → ‖birkhoffAverage ℝ f _root_.id N x - x‖ ≤ θ * ‖x - p‖ := by
    intro N hN
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    have e : birkhoffAverage ℝ f _root_.id N x - x =
        (N : ℝ)⁻¹ • ∑ k ∈ Finset.range N, (f^[k] x - x) := by
      rw [birkhoffAverage, birkhoffSum, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_range, smul_sub, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hN0,
        one_smul]
      rfl
    rw [e, norm_smul, norm_inv, Real.norm_natCast]
    have hs : ‖∑ k ∈ Finset.range N, (f^[k] x - x)‖ ≤ N * (θ * ‖x - p‖) := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ k ∈ Finset.range N, ‖f^[k] x - x‖ ≤ ∑ _k ∈ Finset.range N, θ * ‖x - p‖ :=
            Finset.sum_le_sum fun k _ => hz k
        _ = N * (θ * ‖x - p‖) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    calc (N : ℝ)⁻¹ * ‖∑ k ∈ Finset.range N, (f^[k] x - x)‖ ≤ (N : ℝ)⁻¹ * (N * (θ * ‖x - p‖)) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ = θ * ‖x - p‖ := by field_simp
  have hle : ‖p - x‖ ≤ θ * ‖x - p‖ := by
    have ht : Tendsto (fun N => ‖birkhoffAverage ℝ f _root_.id N x - x‖) atTop (𝓝 ‖p - x‖) :=
      (hlim.sub_const x).norm
    exact le_of_tendsto ht (eventually_atTop.2 ⟨1, havg⟩)
  rw [norm_sub_rev] at hle
  have h0 : ‖x - p‖ = 0 := by
    have := norm_nonneg (x - p)
    nlinarith
  have hxp : x = p := sub_eq_zero.1 (norm_eq_zero.1 h0)
  rw [hxp, hfp]

end NoSmallSubgroups

section ScreenIsometry

variable {v₀ : Minkowski d}

theorem screenProj_eq_screenProj_snd (x : Minkowski d) :
    screenProj v₀ x = screenProj v₀ ((0 : ℝ), x.2) := by
  have e : x = ((0 : ℝ), x.2) + x.1 • timeUnit d := by
    refine Prod.ext ?_ ?_ <;> simp [timeUnit]
  conv_lhs => rw [e]
  rw [map_add, map_smul, screenProj_of_mem_plane v₀ (timeUnit_mem_nullPlaneSpan v₀), smul_zero,
    add_zero]

theorem screenRot_sub_self (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (x : Minkowski d) :
    screenRot v₀ A x - x = screenProj v₀ (A (screenProj v₀ x)) - screenProj v₀ x := by
  rw [screenRot_apply]; abel

/-- The rotation part keeps the time coordinate. -/
theorem fst_screenRot_apply (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (x : Minkowski d) :
    (screenRot v₀ A x).1 = x.1 := by
  rw [screenRot_apply, Prod.fst_add, Prod.fst_sub, fst_eq_zero_of_mem_nullScreen v₀
    (screenProj_mem v₀ _), fst_eq_zero_of_mem_nullScreen v₀ (screenProj_mem v₀ _), zero_add,
    sub_zero]

/-- The rotation part only sees the space coordinate. -/
theorem screenRot_apply_eq_add (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (x : Minkowski d) :
    screenRot v₀ A x = x + (screenRot v₀ A ((0 : ℝ), x.2) - ((0 : ℝ), x.2)) := by
  rw [screenRot_sub_self, ← screenProj_eq_screenProj_snd, ← screenRot_sub_self]; abel

/-- **The rotation part preserves `minkQ`.** -/
theorem minkQ_screenRot_apply (hv0 : v₀ ≠ 0) (hv : minkQ v₀ = 0)
    {A : Minkowski d ≃ₗ[ℝ] Minkowski d} (hA : A ∈ lorentz d) (hfix : A v₀ = v₀)
    (x : Minkowski d) : minkQ (screenRot v₀ A x) = minkQ x := by
  have horth : ∀ q, q ∈ nullScreen v₀ → minkB q (x - screenProj v₀ x) = 0 := fun q hq => by
    rw [minkB_comm]; exact hq _ (sub_screenProj_mem v₀ x)
  have hq : minkQ (screenProj v₀ (A (screenProj v₀ x))) = minkQ (screenProj v₀ x) := by
    rw [minkQ_eq_norm_sq_of_mem_nullScreen v₀ (screenProj_mem v₀ _),
      minkQ_eq_norm_sq_of_mem_nullScreen v₀ (screenProj_mem v₀ _),
      norm_screenProj_apply_screenProj hv0 hv hA hfix]
  have hx : x = screenProj v₀ x + (x - screenProj v₀ x) := by abel
  rw [screenRot_apply, minkQ_add, horth _ (screenProj_mem v₀ _), hq]
  conv_rhs => rw [hx, minkQ_add, horth _ (screenProj_mem v₀ _)]

/-- **The rotation part is an isometry** of the sup norm of `Minkowski d`. -/
theorem norm_screenRot_apply (hv0 : v₀ ≠ 0) (hv : minkQ v₀ = 0)
    {A : Minkowski d ≃ₗ[ℝ] Minkowski d} (hA : A ∈ lorentz d) (hfix : A v₀ = v₀)
    (x : Minkowski d) : ‖screenRot v₀ A x‖ = ‖x‖ := by
  have h1 := fst_screenRot_apply (v₀ := v₀) A x
  have hQ := minkQ_screenRot_apply hv0 hv hA hfix x
  unfold minkQ at hQ
  rw [h1] at hQ
  have h2 : ‖(screenRot v₀ A x).2‖ = ‖x.2‖ :=
    (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (by linarith)
  rw [Prod.norm_def, Prod.norm_def, h1, h2]

theorem norm_screenRot_le_one (hv0 : v₀ ≠ 0) (hv : minkQ v₀ = 0)
    {A : Minkowski d ≃ₗ[ℝ] Minkowski d} (hA : A ∈ lorentz d) (hfix : A v₀ = v₀) :
    ‖screenRot v₀ A‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [norm_screenRot_apply hv0 hv hA hfix, one_mul]

theorem norm_zero_snd (y : EuclideanSpace ℝ (Fin d)) : ‖((0 : ℝ), y)‖ = ‖y‖ := by
  rw [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)]

variable (v₀) in
/-- **The stabiliser of `v₀`** in `SO₀(1, d)`. -/
def nullStab : Subgroup (Minkowski d ≃ₗ[ℝ] Minkowski d) where
  carrier := {A | A ∈ lorentz d ∧ A v₀ = v₀}
  one_mem' := ⟨(lorentz d).one_mem, rfl⟩
  mul_mem' := fun {A B} hA hB => ⟨(lorentz d).mul_mem hA.1 hB.1, by
    rw [LinearEquiv.mul_apply, hB.2, hA.2]⟩
  inv_mem' := fun {A} hA => ⟨(lorentz d).inv_mem hA.1, by
    show A.symm v₀ = v₀
    exact A.symm_apply_eq.2 hA.2.symm⟩

theorem mem_nullStab {A : Minkowski d ≃ₗ[ℝ] Minkowski d} :
    A ∈ nullStab v₀ ↔ A ∈ lorentz d ∧ A v₀ = v₀ := Iff.rfl

/-- The rotation part as a monoid homomorphism on the stabiliser of `v₀`. -/
noncomputable def screenRotHom (hv0 : v₀ ≠ 0) (hv : minkQ v₀ = 0) :
    nullStab v₀ →* (Minkowski d →L[ℝ] Minkowski d) where
  toFun A := screenRot v₀ A
  map_one' := screenRot_one
  map_mul' A B := screenRot_mul hv0 hv A.2.2 B.2.1 B.2.2

theorem screenRotHom_apply (hv0 : v₀ ≠ 0) (hv : minkQ v₀ = 0) (A : nullStab v₀) :
    screenRotHom hv0 hv A = screenRot v₀ A := rfl

/-- **No small subgroups for rotation parts**: if every power of `D` has rotation part within
`θ < 1` of `1`, the rotation part of `D` is `1` (mean ergodic theorem on the screen). -/
theorem screenRot_eq_one_of_forall_pow (hv0 : v₀ ≠ 0) (hv : minkQ v₀ = 0)
    {D : Minkowski d ≃ₗ[ℝ] Minkowski d} (hD : D ∈ nullStab v₀) {θ : ℝ} (hθ : θ < 1)
    (h : ∀ n : ℕ, ‖screenRot v₀ (D ^ n) - 1‖ ≤ θ) : screenRot v₀ D = 1 := by
  set f : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
    (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin d))).comp
    ((screenRot v₀ D).comp (ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin d)))) with hfdef
  have hf : ∀ y : EuclideanSpace ℝ (Fin d), screenRot v₀ D ((0 : ℝ), y) = ((0 : ℝ), f y) := fun y =>
    Prod.ext (by rw [fst_screenRot_apply]) rfl
  have hpow : ∀ n : ℕ, screenRot v₀ (D ^ n) = screenRot v₀ D ^ n := fun n => by
    have := map_pow (screenRotHom hv0 hv) ⟨D, hD⟩ n
    rw [screenRotHom_apply, screenRotHom_apply, SubgroupClass.coe_pow] at this
    exact this
  have hit : ∀ (n : ℕ) (y : EuclideanSpace ℝ (Fin d)), (screenRot v₀ D ^ n) ((0 : ℝ), y) = ((0 : ℝ), f^[n] y) := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih =>
      intro y
      rw [pow_succ, show (screenRot v₀ D ^ n * screenRot v₀ D) ((0 : ℝ), y) =
        (screenRot v₀ D ^ n) (screenRot v₀ D ((0 : ℝ), y)) from rfl, hf, ih, iterate_succ_apply]
  have hfn : ‖f‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => by
    have := norm_screenRot_apply hv0 hv hD.1 hD.2 ((0 : ℝ), y)
    rw [hf, norm_zero_snd, norm_zero_snd] at this
    rw [this, one_mul]
  have hnear : ∀ (n : ℕ) (y : EuclideanSpace ℝ (Fin d)), ‖f^[n] y - y‖ ≤ θ * ‖y‖ := by
    intro n y
    have e : ((0 : ℝ), f^[n] y - y) = (screenRot v₀ (D ^ n) - 1) ((0 : ℝ), y) := by
      rw [show (screenRot v₀ (D ^ n) - 1) ((0 : ℝ), y) =
        screenRot v₀ (D ^ n) ((0 : ℝ), y) - ((0 : ℝ), y) from rfl, hpow, hit]
      exact Prod.ext (by simp) rfl
    calc ‖f^[n] y - y‖ = ‖((0 : ℝ), f^[n] y - y)‖ := (norm_zero_snd _).symm
      _ ≤ ‖screenRot v₀ (D ^ n) - 1‖ * ‖((0 : ℝ), y)‖ := by rw [e]; exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ θ * ‖y‖ := by rw [norm_zero_snd]; exact mul_le_mul_of_nonneg_right (h n) (norm_nonneg _)
  have hid := eq_self_of_forall_iterate_near f hfn hθ hnear
  refine ContinuousLinearMap.ext fun x => ?_
  rw [screenRot_apply_eq_add, hf, hid]
  simp

/-- **Frobenius' lemma for rotation parts**: if the rotation part of `A` commutes with that of
`B A B⁻¹` and the rotation part of `B` is `½`-close to `1`, the rotation parts of `A` and `B`
commute. -/
theorem commute_screenRot_of_commute_conj (hv0 : v₀ ≠ 0) (hv : minkQ v₀ = 0)
    {A B : Minkowski d ≃ₗ[ℝ] Minkowski d} (hA : A ∈ nullStab v₀) (hB : B ∈ nullStab v₀)
    (hB1 : ‖screenRot v₀ B - 1‖ < 1 / 2)
    (hc : Commute (screenRot v₀ A) (screenRot v₀ (B * A * B⁻¹))) :
    Commute (screenRot v₀ A) (screenRot v₀ B) := by
  set ρu := (screenRotHom hv0 hv).toHomUnits
  have hval : ∀ z : nullStab v₀, ((ρu z : (Minkowski d →L[ℝ] Minkowski d)ˣ) :
      Minkowski d →L[ℝ] Minkowski d) = screenRot v₀ z := fun _ => rfl
  have hnorm : ∀ z : nullStab v₀, ‖((ρu z : (Minkowski d →L[ℝ] Minkowski d)ˣ) :
      Minkowski d →L[ℝ] Minkowski d)‖ ≤ 1 := fun z => by
    rw [hval]; exact norm_screenRot_le_one hv0 hv z.2.1 z.2.2
  set A' : nullStab v₀ := ⟨A, hA⟩
  set B' : nullStab v₀ := ⟨B, hB⟩
  set a := ρu A'
  set b := ρu B'
  have hc' : Commute a (b * a * b⁻¹) := by
    have e : b * a * b⁻¹ = ρu (B' * A' * B'⁻¹) := by simp only [map_mul, map_inv, a, b]
    rw [e]
    exact Units.ext hc.eq
  set c := a * b * a⁻¹ * b⁻¹ with hcdef
  have hcn : ∀ n : ℕ, c ^ n = a ^ n * b * a⁻¹ ^ n * b⁻¹ := by
    intro n
    have e1 : c = a * (b * a * b⁻¹)⁻¹ := by rw [hcdef]; group
    have e2 : (b * a * b⁻¹)⁻¹ = b * a⁻¹ * b⁻¹ := by group
    rw [e1, hc'.inv_right.mul_pow, e2, conj_pow]
    group
  have hθ : ∀ n : ℕ, ‖((c ^ n : (Minkowski d →L[ℝ] Minkowski d)ˣ) :
      Minkowski d →L[ℝ] Minkowski d) - 1‖ ≤ 2 * ‖screenRot v₀ B - 1‖ := by
    intro n
    rw [hcn, Units.val_mul, Units.val_mul, Units.val_mul]
    have hX : ((a ^ n : (Minkowski d →L[ℝ] Minkowski d)ˣ) : Minkowski d →L[ℝ] Minkowski d) *
        ((a⁻¹ ^ n : (Minkowski d →L[ℝ] Minkowski d)ˣ) : Minkowski d →L[ℝ] Minkowski d) = 1 := by
      rw [← Units.val_mul, inv_pow, mul_inv_cancel, Units.val_one]
    have hY : ((b : (Minkowski d →L[ℝ] Minkowski d)ˣ) : Minkowski d →L[ℝ] Minkowski d) *
        ((b⁻¹ : (Minkowski d →L[ℝ] Minkowski d)ˣ) : Minkowski d →L[ℝ] Minkowski d) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    refine (norm_conj_mul_sub_one_le hX hY).trans ?_
    have h1 : ‖((a ^ n : (Minkowski d →L[ℝ] Minkowski d)ˣ) : Minkowski d →L[ℝ] Minkowski d)‖ ≤ 1 := by
      rw [show a ^ n = ρu (A' ^ n) by simp only [map_pow, a]]; exact hnorm _
    have h2 : ‖((a⁻¹ ^ n : (Minkowski d →L[ℝ] Minkowski d)ˣ) : Minkowski d →L[ℝ] Minkowski d)‖ ≤ 1 := by
      rw [show a⁻¹ ^ n = ρu (A'⁻¹ ^ n) by simp only [map_pow, map_inv, a]]; exact hnorm _
    have h3 : ‖((b⁻¹ : (Minkowski d →L[ℝ] Minkowski d)ˣ) : Minkowski d →L[ℝ] Minkowski d)‖ ≤ 1 := by
      rw [show b⁻¹ = ρu B'⁻¹ by simp only [map_inv, b]]; exact hnorm _
    have hb : ((b : (Minkowski d →L[ℝ] Minkowski d)ˣ) : Minkowski d →L[ℝ] Minkowski d) =
        screenRot v₀ B := rfl
    rw [hb]
    have h12 : ‖((a ^ n : (Minkowski d →L[ℝ] Minkowski d)ˣ) : Minkowski d →L[ℝ] Minkowski d)‖ *
        ‖((a⁻¹ ^ n : (Minkowski d →L[ℝ] Minkowski d)ˣ) : Minkowski d →L[ℝ] Minkowski d)‖ ≤ 1 :=
      mul_le_one₀ h1 (norm_nonneg _) h2
    calc _ ≤ (1 + 1) * ‖screenRot v₀ B - 1‖ * 1 := by
          gcongr
      _ = 2 * ‖screenRot v₀ B - 1‖ := by ring
  set D : Minkowski d ≃ₗ[ℝ] Minkowski d := A * B * A⁻¹ * B⁻¹
  have hD : D ∈ nullStab v₀ := (A' * B' * A'⁻¹ * B'⁻¹).2
  have hcD : c = ρu ⟨D, hD⟩ := by
    simp only [hcdef, a, b, ← map_inv, ← map_mul]; rfl
  have hDn : ∀ n : ℕ, ‖screenRot v₀ (D ^ n) - 1‖ ≤ 2 * ‖screenRot v₀ B - 1‖ := by
    intro n
    have := hθ n
    rwa [hcD, ← map_pow, hval] at this
  have hD1 := screenRot_eq_one_of_forall_pow hv0 hv hD (by linarith) hDn
  have hc1 : c = 1 := by
    rw [hcD]; exact Units.ext hD1
  have hab : a * b = b * a := by
    rw [hcdef, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hc1
    exact hc1
  exact congrArg Units.val hab

end ScreenIsometry

section Chain

variable {v₀ : Minkowski d}

theorem linOf_one' : linOf (1 : isom d) = 1 := LinearEquiv.ext fun _ => rfl

theorem linOf_mem_nullStab {Γ : Subgroup (isom d)} (hfix : ∀ γ ∈ Γ, linOf γ v₀ = v₀) {γ : isom d}
    (hγ : γ ∈ Γ) : linOf γ ∈ nullStab v₀ := ⟨linOf_mem γ, hfix γ hγ⟩

/-- `‖ρ(A⁻¹) − 1‖ ≤ ‖ρ(A) − 1‖` on the stabiliser. -/
theorem norm_screenRot_inv_sub_one_le (hv0 : v₀ ≠ 0) (hv : minkQ v₀ = 0)
    {A : Minkowski d ≃ₗ[ℝ] Minkowski d} (hA : A ∈ nullStab v₀) :
    ‖screenRot v₀ A⁻¹ - 1‖ ≤ ‖screenRot v₀ A - 1‖ := by
  have hAi : A⁻¹ ∈ nullStab v₀ := (nullStab v₀).inv_mem hA
  have h1 : screenRot v₀ A⁻¹ * screenRot v₀ A = 1 := by
    rw [← screenRot_mul hv0 hv hAi.2 hA.1 hA.2, inv_mul_cancel, screenRot_one]
  have e : screenRot v₀ A⁻¹ - 1 = -(screenRot v₀ A⁻¹ * (screenRot v₀ A - 1)) := by
    rw [mul_sub, h1, mul_one, neg_sub]
  rw [e, norm_neg]
  calc ‖screenRot v₀ A⁻¹ * (screenRot v₀ A - 1)‖ ≤ ‖screenRot v₀ A⁻¹‖ * ‖screenRot v₀ A - 1‖ :=
        norm_mul_le _ _
    _ ≤ 1 * ‖screenRot v₀ A - 1‖ :=
        mul_le_mul_of_nonneg_right (norm_screenRot_le_one hv0 hv hAi.1 hAi.2) (norm_nonneg _)
    _ = _ := one_mul _

theorem norm_screenRot_sub_one_le_two (hv0 : v₀ ≠ 0) (hv : minkQ v₀ = 0)
    {A : Minkowski d ≃ₗ[ℝ] Minkowski d} (hA : A ∈ nullStab v₀) : ‖screenRot v₀ A - 1‖ ≤ 2 := by
  calc ‖screenRot v₀ A - 1‖ ≤ ‖screenRot v₀ A‖ + ‖(1 : Minkowski d →L[ℝ] Minkowski d)‖ :=
        norm_sub_le _ _
    _ ≤ 1 + 1 := add_le_add (norm_screenRot_le_one hv0 hv hA.1 hA.2)
        ContinuousLinearMap.norm_id_le
    _ = 2 := by norm_num

/-- **The backward induction** (Zassenhaus): if `g` has rotation part `½`-close to `1`, `h` has
rotation part `½`-close to `1`, and the iterated commutator `[g, [g, …, [g, h]]]` is trivial,
the rotation parts of `g` and `h` commute (Frobenius' lemma at each step). -/
theorem commute_screenRot_of_iterate_eq_one (hv0 : v₀ ≠ 0) (hv : minkQ v₀ = 0) {g : isom d}
    (hg : linOf g ∈ nullStab v₀) (hgε : ‖screenRot v₀ (linOf g) - 1‖ ≤ 1 / 2) (N : ℕ) :
    ∀ h : isom d, linOf h ∈ nullStab v₀ → ‖screenRot v₀ (linOf h) - 1‖ < 1 / 2 →
      (fun x => g * x * g⁻¹ * x⁻¹)^[N] h = 1 →
        Commute (screenRot v₀ (linOf g)) (screenRot v₀ (linOf h)) := by
  induction N with
  | zero =>
    intro h _ _ hN
    rw [iterate_zero_apply] at hN
    rw [hN, linOf_one', screenRot_one]
    exact Commute.one_right _
  | succ N ih =>
    intro h hh hhε hN
    rw [iterate_succ_apply] at hN
    set ρu := (screenRotHom hv0 hv).toHomUnits
    set G' : nullStab v₀ := ⟨linOf g, hg⟩
    set H' : nullStab v₀ := ⟨linOf h, hh⟩
    have hlin : linOf (g * h * g⁻¹ * h⁻¹) = ((G' * H' * G'⁻¹ * H'⁻¹ : nullStab v₀) :
        Minkowski d ≃ₗ[ℝ] Minkowski d) := by
      simp only [linOf_mul, linOf_inv]; rfl
    have hh' : linOf (g * h * g⁻¹ * h⁻¹) ∈ nullStab v₀ := by
      rw [hlin]; exact (G' * H' * G'⁻¹ * H'⁻¹).2
    have hval : ∀ z : nullStab v₀, ((ρu z : (Minkowski d →L[ℝ] Minkowski d)ˣ) :
        Minkowski d →L[ℝ] Minkowski d) = screenRot v₀ z := fun _ => rfl
    have hρ' : screenRot v₀ (linOf (g * h * g⁻¹ * h⁻¹)) =
        (((ρu G' * ρu H' * (ρu G')⁻¹ * (ρu H')⁻¹ : (Minkowski d →L[ℝ] Minkowski d)ˣ)) :
          Minkowski d →L[ℝ] Minkowski d) := by
      rw [hlin, ← hval]; simp only [map_mul, map_inv]
    have hε' : ‖screenRot v₀ (linOf (g * h * g⁻¹ * h⁻¹)) - 1‖ < 1 / 2 := by
      rw [hρ', Units.val_mul, Units.val_mul, Units.val_mul]
      have hX : ((ρu G' : (Minkowski d →L[ℝ] Minkowski d)ˣ) : Minkowski d →L[ℝ] Minkowski d) *
          (((ρu G')⁻¹ : (Minkowski d →L[ℝ] Minkowski d)ˣ) : Minkowski d →L[ℝ] Minkowski d) = 1 :=
        by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      have hY : ((ρu H' : (Minkowski d →L[ℝ] Minkowski d)ˣ) : Minkowski d →L[ℝ] Minkowski d) *
          (((ρu H')⁻¹ : (Minkowski d →L[ℝ] Minkowski d)ˣ) : Minkowski d →L[ℝ] Minkowski d) = 1 :=
        by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      refine (norm_mul_mul_mul_sub_one_le hX hY).trans_lt ?_
      have hGi : ‖(((ρu G')⁻¹ : (Minkowski d →L[ℝ] Minkowski d)ˣ) :
          Minkowski d →L[ℝ] Minkowski d)‖ ≤ 1 := by
        rw [← map_inv, hval]; exact norm_screenRot_le_one hv0 hv (G'⁻¹).2.1 (G'⁻¹).2.2
      have hHi : ‖(((ρu H')⁻¹ : (Minkowski d →L[ℝ] Minkowski d)ˣ) :
          Minkowski d →L[ℝ] Minkowski d)‖ ≤ 1 := by
        rw [← map_inv, hval]; exact norm_screenRot_le_one hv0 hv (H'⁻¹).2.1 (H'⁻¹).2.2
      rw [hval, hval]
      have h0 : 0 ≤ ‖screenRot v₀ (linOf h) - 1‖ := norm_nonneg _
      calc 2 * ‖screenRot v₀ ↑G' - 1‖ * ‖screenRot v₀ ↑H' - 1‖ *
            ‖(((ρu G')⁻¹ : (Minkowski d →L[ℝ] Minkowski d)ˣ) : Minkowski d →L[ℝ] Minkowski d)‖ *
            ‖(((ρu H')⁻¹ : (Minkowski d →L[ℝ] Minkowski d)ˣ) : Minkowski d →L[ℝ] Minkowski d)‖
          ≤ 2 * (1 / 2) * ‖screenRot v₀ (linOf h) - 1‖ * 1 * 1 := by gcongr
        _ < 1 / 2 := by linarith
    have hc := ih _ hh' hε' hN
    -- from `ρg` commuting with `ρg ρh ρg⁻¹ ρh⁻¹` to `ρg` commuting with `ρ(h g h⁻¹)`
    have hu : Commute (ρu G') (ρu G' * ρu H' * (ρu G')⁻¹ * (ρu H')⁻¹) := by
      refine Units.ext ?_
      have := hc.eq
      rw [hρ'] at this
      exact this
    have hu2 : Commute (ρu G') (ρu H' * ρu G' * (ρu H')⁻¹) := by
      have e : ρu G' * ρu H' * (ρu G')⁻¹ * (ρu H')⁻¹ =
          ρu G' * (ρu H' * ρu G' * (ρu H')⁻¹)⁻¹ := by group
      rw [e] at hu
      have h2 : ρu G' * (ρu G' * (ρu H' * ρu G' * (ρu H')⁻¹)⁻¹) =
          ρu G' * ((ρu H' * ρu G' * (ρu H')⁻¹)⁻¹ * ρu G') := by
        rw [hu.eq, mul_assoc]
      exact (Commute.inv_right_iff.1 (mul_left_cancel h2))
    have hconj : Commute (screenRot v₀ (linOf g))
        (screenRot v₀ (linOf h * linOf g * (linOf h)⁻¹)) := by
      have e : screenRot v₀ (linOf h * linOf g * (linOf h)⁻¹) =
          ((ρu H' * ρu G' * (ρu H')⁻¹ : (Minkowski d →L[ℝ] Minkowski d)ˣ) :
            Minkowski d →L[ℝ] Minkowski d) := by
        rw [← map_inv, ← map_mul, ← map_mul, hval]; rfl
      rw [e]
      exact congrArg Units.val hu2.eq
    exact commute_screenRot_of_commute_conj hv0 hv hg hh hhε hconj

end Chain

section AffExt

/-- **The affine extension** `ĝ (y, s) = (L(g) y + s τ(g), s)` of an isometry, a continuous
linear endomorphism of `𝐌ⁿ × ℝ` (`g ↦ ĝ` is multiplicative). -/
noncomputable def affExt (g : isom d) : Minkowski d × ℝ →L[ℝ] Minkowski d × ℝ :=
  LinearMap.toContinuousLinearMap
    ((((linOf g : Minkowski d →ₗ[ℝ] Minkowski d).comp (LinearMap.fst ℝ (Minkowski d) ℝ)) +
      (LinearMap.snd ℝ (Minkowski d) ℝ).smulRight (trOf g)).prod (LinearMap.snd ℝ (Minkowski d) ℝ))

theorem affExt_apply (g : isom d) (y : Minkowski d) (s : ℝ) :
    affExt g (y, s) = (linOf g y + s • trOf g, s) := rfl

theorem trOf_mul (g h : isom d) : trOf (g * h) = linOf g (trOf h) + trOf g := by
  show transPart ((g : Minkowski d ≃ᵃ[ℝ] Minkowski d) * (h : Minkowski d ≃ᵃ[ℝ] Minkowski d)) = _
  rw [transPart, show ((g : Minkowski d ≃ᵃ[ℝ] Minkowski d) * (h : Minkowski d ≃ᵃ[ℝ] Minkowski d)) 0
    = (g : Minkowski d ≃ᵃ[ℝ] Minkowski d) ((h : Minkowski d ≃ᵃ[ℝ] Minkowski d) 0) from rfl,
    apply_eq_linear_add_transPart]
  rfl

theorem trOf_one : trOf (1 : isom d) = 0 := rfl

theorem affExt_mul (g h : isom d) : affExt (g * h) = affExt g * affExt h := by
  refine ContinuousLinearMap.ext fun ⟨y, s⟩ => ?_
  rw [show (affExt g * affExt h) (y, s) = affExt g (affExt h (y, s)) from rfl, affExt_apply,
    affExt_apply, affExt_apply, linOf_mul, trOf_mul, LinearEquiv.mul_apply, map_add, map_smul,
    smul_add]
  refine Prod.ext ?_ rfl
  show _ + (_ + _) = _ + _ + _
  rw [add_assoc]

theorem affExt_one : affExt (1 : isom d) = 1 := by
  refine ContinuousLinearMap.ext fun ⟨y, s⟩ => ?_
  rw [affExt_apply, linOf_one', trOf_one, smul_zero, add_zero]
  rfl

theorem affExt_sub_one_apply (g : isom d) (y : Minkowski d) (s : ℝ) :
    (affExt g - 1) (y, s) = (linOf g y + s • trOf g - y, 0) := by
  rw [show (affExt g - 1) (y, s) = affExt g (y, s) - (y, s) from rfl, affExt_apply]
  exact Prod.ext rfl (sub_self s)

theorem norm_linToCLM_sub_one_le (g : isom d) :
    ‖linToCLM (linOf g) - 1‖ ≤ ‖affExt g - 1‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun y => ?_
  have h := (affExt g - 1).le_opNorm (y, 0)
  rw [affExt_sub_one_apply, zero_smul, add_zero] at h
  have e1 : ‖((linOf g y - y, (0 : ℝ)) : Minkowski d × ℝ)‖ = ‖linOf g y - y‖ := by
    rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]
  have e2 : ‖((y, (0 : ℝ)) : Minkowski d × ℝ)‖ = ‖y‖ := by
    rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]
  rw [e1, e2] at h
  exact h

theorem norm_trOf_le (g : isom d) : ‖trOf g‖ ≤ ‖affExt g - 1‖ := by
  have h := (affExt g - 1).le_opNorm (0, 1)
  rw [affExt_sub_one_apply, map_zero, one_smul, zero_add, sub_zero] at h
  have e1 : ‖((trOf g, (0 : ℝ)) : Minkowski d × ℝ)‖ = ‖trOf g‖ := by
    rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]
  have e2 : ‖(((0 : Minkowski d), (1 : ℝ)) : Minkowski d × ℝ)‖ = 1 := by
    rw [Prod.norm_def, norm_zero, norm_one, max_eq_right zero_le_one]
  rw [e1, e2, mul_one] at h
  exact h

/-- **Discreteness, quantified**: a discrete `Γ` has a neighbourhood of `1`, read on the affine
extension, containing no other element of `Γ`. -/
theorem exists_affExt_isolated {Γ : Subgroup (isom d)} (hdisc : DiscreteTopology Γ) :
    ∃ η > 0, ∀ x ∈ Γ, ‖affExt x - 1‖ < η → x = 1 := by
  have hop : IsOpen ({1} : Set Γ) := isOpen_discrete _
  obtain ⟨t, ht, htΓ⟩ := isOpen_induced_iff.1 hop
  obtain ⟨t', ht', htt⟩ := isOpen_induced_iff.1 ht
  have h1t : (1 : isom d) ∈ t := by
    have : (1 : Γ) ∈ Subtype.val ⁻¹' t := by rw [htΓ]; rfl
    exact this
  have h1t' : isomPair (1 : isom d) ∈ t' := by rw [← htt] at h1t; exact h1t
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.1 ht' _ h1t'
  refine ⟨η, hη, fun x hx hxη => ?_⟩
  have hpair : isomPair x ∈ t' := by
    apply hball
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    have e1 : (isomPair (1 : isom d)).1 = 1 := linToCLM_one
    have e2 : (isomPair (1 : isom d)).2 = 0 := trOf_one
    rw [e1, e2, dist_eq_norm, dist_eq_norm, sub_zero]
    exact ⟨(norm_linToCLM_sub_one_le x).trans_lt hxη, (norm_trOf_le x).trans_lt hxη⟩
  have hxt : x ∈ t := by rw [← htt]; exact hpair
  have : (⟨x, hx⟩ : Γ) ∈ Subtype.val ⁻¹' t := hxt
  rw [htΓ] at this
  exact congrArg Subtype.val (Set.mem_singleton_iff.1 this)

end AffExt

section Scaling

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : ℕ}

/-- The scaling `D_K = ∑ᵢ Kⁱ Pᵢ` along a decomposition `1 = ∑ᵢ Pᵢ`. -/
noncomputable def scaleBy (P : Fin n → V →L[ℝ] V) (K : ℝ) : V →L[ℝ] V :=
  ∑ i : Fin n, K ^ (i : ℕ) • P i

theorem scaleBy_mul_scaleBy (P : Fin n → V →L[ℝ] V)
    (hP : ∀ i j, P i * P j = if i = j then P i else 0) (hsum : ∑ i, P i = 1) {K : ℝ}
    (hK : K ≠ 0) : scaleBy P K * scaleBy P K⁻¹ = 1 ∧ scaleBy P K⁻¹ * scaleBy P K = 1 := by
  have key : ∀ a b : ℝ, a * b = 1 → scaleBy P a * scaleBy P b = 1 := by
    intro a b hab
    have hab' : ∀ i : ℕ, a ^ i * b ^ i = 1 := fun i => by rw [← mul_pow, hab, one_pow]
    have e : scaleBy P a * scaleBy P b = ∑ i : Fin n, P i := by
      rw [scaleBy, scaleBy, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      simp_rw [smul_mul_assoc, mul_smul_comm, smul_smul, hP, smul_ite, smul_zero]
      rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _), hab', one_smul]
    rw [e, hsum]
  exact ⟨key K K⁻¹ (mul_inv_cancel₀ hK), key K⁻¹ K (inv_mul_cancel₀ hK)⟩

private theorem scale_coef_le {K : ℝ} (hK : 1 ≤ K) {i j : ℕ} (hij : i < j) :
    |K ^ i * K⁻¹ ^ j| ≤ K⁻¹ := by
  have hK0 : 0 < K := by linarith
  have hKi : K⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hK
  have e : K ^ i * K⁻¹ ^ j = K⁻¹ ^ (j - i) := by
    have hj : K⁻¹ ^ j = K⁻¹ ^ i * K⁻¹ ^ (j - i) := by
      rw [← pow_add, Nat.add_sub_cancel' hij.le]
    rw [hj, ← mul_assoc, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hK0.ne'), one_mul]
  rw [e, abs_of_nonneg (by positivity)]
  calc K⁻¹ ^ (j - i) ≤ K⁻¹ ^ 1 := pow_le_pow_of_le_one (by positivity) hKi (by omega)
    _ = K⁻¹ := pow_one _

/-- **Conjugating by a scaling kills the upper part**: for `T` block upper triangular
(`Pᵢ T Pⱼ = 0` for `j < i`), `‖D_K T D_K⁻¹ − ∑ᵢ Pᵢ T Pᵢ‖ ≤ K⁻¹ ∑ᵢⱼ ‖Pᵢ T Pⱼ‖` (`K ≥ 1`). -/
theorem norm_scaleBy_conj_sub_le (P : Fin n → V →L[ℝ] V) (T : V →L[ℝ] V)
    (hT : ∀ i j, j < i → P i * T * P j = 0) {K : ℝ} (hK : 1 ≤ K) :
    ‖scaleBy P K * T * scaleBy P K⁻¹ - ∑ i, P i * T * P i‖ ≤
      K⁻¹ * ∑ i, ∑ j, ‖P i * T * P j‖ := by
  have e : scaleBy P K * T * scaleBy P K⁻¹ - ∑ i, P i * T * P i =
      ∑ i : Fin n, ∑ j : Fin n,
        (K ^ (i : ℕ) * K⁻¹ ^ (j : ℕ) - if i = j then 1 else 0) • (P i * T * P j) := by
    rw [scaleBy, scaleBy, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    simp_rw [sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [e, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  rcases lt_trichotomy i j with hij | rfl | hij
  · rw [if_neg hij.ne, sub_zero]
    exact mul_le_mul_of_nonneg_right (scale_coef_le hK hij) (norm_nonneg _)
  · have hK0 : K ≠ 0 := by linarith
    rw [if_pos rfl, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hK0), sub_self, abs_zero, zero_mul]
    positivity
  · rw [hT i j hij, norm_zero, mul_zero, mul_zero]

/-- The diagonal part: if `Pᵢ T Pᵢ = Pᵢ` except at `k`, `∑ᵢ Pᵢ T Pᵢ − 1 = P_k (T − 1) P_k`. -/
theorem sum_diag_sub_one (P : Fin n → V →L[ℝ] V)
    (hP : ∀ i j, P i * P j = if i = j then P i else 0) (hsum : ∑ i, P i = 1) (T : V →L[ℝ] V)
    (k : Fin n) (hdiag : ∀ i, i ≠ k → P i * T * P i = P i) :
    ∑ i, P i * T * P i - 1 = P k * (T - 1) * P k := by
  have e : ∑ i, P i * T * P i - 1 = ∑ i, (P i * T * P i - P i) := by
    rw [Finset.sum_sub_distrib, hsum]
  rw [e, Finset.sum_eq_single k]
  · rw [mul_sub, sub_mul, mul_one, hP k k, if_pos rfl]
  · intro i _ hi; rw [hdiag i hi, sub_self]
  · intro h; exact absurd (Finset.mem_univ k) h

end Scaling

section Flag

variable (v₀ : Minkowski d)

/-- `φ(x) = ⟨v₀ | x⟩ / ⟨v₀ | e₀⟩`, the `e₀`-coordinate of `x` in `𝐌ⁿ = v₀^⊥ ⊕ ℝ e₀`. -/
noncomputable def nullCoord : Minkowski d →ₗ[ℝ] ℝ := (minkB v₀ (timeUnit d))⁻¹ • minkForm d v₀

theorem nullCoord_apply (x : Minkowski d) :
    nullCoord v₀ x = (minkB v₀ (timeUnit d))⁻¹ * minkB v₀ x := rfl

/-- The projection on `ℝ v₀` along `S ⊕ ℝ e₀`. -/
noncomputable def nullLineProj : Minkowski d →ₗ[ℝ] Minkowski d :=
  LinearMap.id - screenProj v₀ - (nullCoord v₀).smulRight (timeUnit d)

theorem nullLineProj_apply (x : Minkowski d) :
    nullLineProj v₀ x = x - screenProj v₀ x - nullCoord v₀ x • timeUnit d := rfl

/-- A linear endomorphism of `𝐌ⁿ`, acting on the first factor of `𝐌ⁿ × ℝ`. -/
noncomputable def liftV (q : Minkowski d →ₗ[ℝ] Minkowski d) : Minkowski d × ℝ →L[ℝ] Minkowski d × ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.inl ℝ (Minkowski d) ℝ).comp (q.comp (LinearMap.fst ℝ (Minkowski d) ℝ)))

theorem liftV_apply (q : Minkowski d →ₗ[ℝ] Minkowski d) (y : Minkowski d) (s : ℝ) :
    liftV q (y, s) = (q y, 0) := rfl

/-- The projection of `𝐌ⁿ × ℝ` on its last factor. -/
noncomputable def lastV : Minkowski d × ℝ →L[ℝ] Minkowski d × ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.inr ℝ (Minkowski d) ℝ).comp (LinearMap.snd ℝ (Minkowski d) ℝ))

theorem lastV_apply (y : Minkowski d) (s : ℝ) : (lastV (d := d)) (y, s) = (0, s) := rfl

/-- **The flag decomposition** `𝐌ⁿ × ℝ = ℝ v₀ ⊕ S ⊕ ℝ e₀ ⊕ ℝ`: every affine map whose linear
part fixes `v₀` is block upper triangular, with diagonal `(1, ρ, 1, 1)`. -/
noncomputable def flagProj : Fin 4 → (Minkowski d × ℝ →L[ℝ] Minkowski d × ℝ)
  | 0 => liftV (nullLineProj v₀)
  | 1 => liftV (screenProj v₀)
  | 2 => liftV ((nullCoord v₀).smulRight (timeUnit d))
  | 3 => lastV

variable {v₀}

theorem nullCoord_screenProj (y : Minkowski d) : nullCoord v₀ (screenProj v₀ y) = 0 := by
  rw [nullCoord_apply, minkB_self_of_mem_nullScreen v₀ (screenProj_mem v₀ y), mul_zero]

theorem nullCoord_timeUnit (hv0 : v₀ ≠ 0) (hv : minkQ v₀ = 0) : nullCoord v₀ (timeUnit d) = 1 := by
  rw [nullCoord_apply, inv_mul_cancel₀]
  rw [minkB_comm]; exact minkB_timeUnit_ne_zero hv0 hv

theorem screenProj_timeUnit : screenProj v₀ (timeUnit d) = 0 :=
  screenProj_of_mem_plane v₀ (timeUnit_mem_nullPlaneSpan v₀)

theorem screenProj_nullLineProj (y : Minkowski d) : screenProj v₀ (nullLineProj v₀ y) = 0 := by
  rw [nullLineProj_apply, map_sub, map_sub, screenProj_screenProj, map_smul, screenProj_timeUnit,
    smul_zero, sub_self, sub_zero]

theorem nullCoord_nullLineProj (hv0 : v₀ ≠ 0) (hv : minkQ v₀ = 0) (y : Minkowski d) :
    nullCoord v₀ (nullLineProj v₀ y) = 0 := by
  rw [nullLineProj_apply, map_sub, map_sub, nullCoord_screenProj, map_smul,
    nullCoord_timeUnit hv0 hv, smul_eq_mul, mul_one, sub_zero, sub_self]

theorem nullLineProj_mem (hv0 : v₀ ≠ 0) (hv : minkQ v₀ = 0) (y : Minkowski d) :
    nullLineProj v₀ y ∈ ℝ ∙ v₀ := by
  refine mem_span_of_mem_nullPlaneSpan hv0 hv ?_ ?_
  · rw [nullLineProj_apply]
    exact sub_mem (sub_screenProj_mem v₀ y) (smul_mem _ _ (timeUnit_mem_nullPlaneSpan v₀))
  · have h := nullCoord_nullLineProj hv0 hv y
    rw [nullCoord_apply, mul_eq_zero] at h
    rcases h with h | h
    · exact absurd (inv_eq_zero.1 h) (by rw [minkB_comm]; exact minkB_timeUnit_ne_zero hv0 hv)
    · rw [minkB_comm]; exact h

theorem nullCoord_map {L : Minkowski d ≃ₗ[ℝ] Minkowski d} (hL : L ∈ nullStab v₀) (y : Minkowski d) :
    nullCoord v₀ (L y) = nullCoord v₀ y := by
  have h : minkB v₀ (L y) = minkB v₀ y := by
    conv_lhs => rw [← hL.2]
    exact minkB_map (lorentz.minkQ_apply hL.1) _ _
  rw [nullCoord_apply, nullCoord_apply, h]

theorem map_nullLineProj (hv0 : v₀ ≠ 0) (hv : minkQ v₀ = 0) {L : Minkowski d ≃ₗ[ℝ] Minkowski d}
    (hL : L ∈ nullStab v₀) (y : Minkowski d) : L (nullLineProj v₀ y) = nullLineProj v₀ y := by
  obtain ⟨c, hc⟩ := mem_span_singleton.1 (nullLineProj_mem hv0 hv y)
  rw [← hc, map_smul, hL.2]

theorem liftV_mul_liftV (q q' : Minkowski d →ₗ[ℝ] Minkowski d) :
    liftV q * liftV q' = liftV (q.comp q') := by
  refine ContinuousLinearMap.ext fun ⟨y, s⟩ => ?_
  rfl

theorem liftV_mul_lastV (q : Minkowski d →ₗ[ℝ] Minkowski d) : liftV q * lastV = 0 := by
  refine ContinuousLinearMap.ext fun ⟨y, s⟩ => ?_
  show (q 0, (0 : ℝ)) = 0
  rw [map_zero]; rfl

theorem lastV_mul_liftV (q : Minkowski d →ₗ[ℝ] Minkowski d) : lastV * liftV q = 0 := by
  refine ContinuousLinearMap.ext fun ⟨y, s⟩ => ?_
  rfl

theorem lastV_mul_lastV : (lastV (d := d)) * lastV = lastV := by
  refine ContinuousLinearMap.ext fun ⟨y, s⟩ => ?_
  rfl

theorem liftV_eq_zero {q : Minkowski d →ₗ[ℝ] Minkowski d} (hq : ∀ y, q y = 0) : liftV q = 0 := by
  refine ContinuousLinearMap.ext fun ⟨y, s⟩ => ?_
  rw [liftV_apply, hq]; rfl

theorem flagProj_mul (hv0 : v₀ ≠ 0) (hv : minkQ v₀ = 0) (i j : Fin 4) :
    flagProj v₀ i * flagProj v₀ j = if i = j then flagProj v₀ i else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, flagProj, if_true,
      Fin.reduceEq, if_false, liftV_mul_liftV, liftV_mul_lastV, lastV_mul_liftV, lastV_mul_lastV]
  all_goals first
    | (apply liftV_eq_zero; intro y
       simp only [LinearMap.comp_apply, nullLineProj_apply, LinearMap.smulRight_apply,
         screenProj_screenProj, map_smul, map_sub, screenProj_timeUnit, nullCoord_screenProj,
         nullCoord_timeUnit hv0 hv, smul_zero, sub_zero, sub_self, one_smul, zero_smul])
    | (congr 1; refine LinearMap.ext fun y => ?_
       simp only [LinearMap.comp_apply, nullLineProj_apply, LinearMap.smulRight_apply,
         screenProj_screenProj, map_smul, map_sub, screenProj_timeUnit, nullCoord_screenProj,
         nullCoord_timeUnit hv0 hv, smul_zero, sub_zero, sub_self, one_smul, zero_smul])

theorem flagProj_sum : ∑ i, flagProj v₀ i = 1 := by
  rw [Fin.sum_univ_four]
  refine ContinuousLinearMap.ext fun ⟨y, s⟩ => ?_
  show ((nullLineProj v₀ y, (0 : ℝ)) + (screenProj v₀ y, 0) + (nullCoord v₀ y • timeUnit d, 0) +
    (0, s)) = (y, s)
  refine Prod.ext ?_ ?_
  · show nullLineProj v₀ y + screenProj v₀ y + nullCoord v₀ y • timeUnit d + 0 = y
    rw [nullLineProj_apply]; abel
  · show (0 : ℝ) + 0 + 0 + s = s
    ring

theorem liftV_mul_affExt_mul_liftV (q q' : Minkowski d →ₗ[ℝ] Minkowski d) (x : isom d) :
    liftV q' * affExt x * liftV q =
      liftV (q'.comp ((linOf x : Minkowski d →ₗ[ℝ] Minkowski d).comp q)) := by
  refine ContinuousLinearMap.ext fun ⟨y, s⟩ => ?_
  show liftV q' (affExt x (q y, 0)) = _
  rw [affExt_apply, zero_smul, add_zero]
  rfl

theorem lastV_mul_affExt_mul_liftV (q : Minkowski d →ₗ[ℝ] Minkowski d) (x : isom d) :
    lastV * affExt x * liftV q = 0 := by
  refine ContinuousLinearMap.ext fun ⟨y, s⟩ => ?_
  show lastV (affExt x (q y, 0)) = 0
  rw [affExt_apply]; rfl

theorem lastV_mul_affExt_mul_lastV (x : isom d) : lastV * affExt x * lastV = lastV := by
  refine ContinuousLinearMap.ext fun ⟨y, s⟩ => ?_
  show lastV (affExt x (0, s)) = (0, s)
  rw [affExt_apply]; rfl

/-- **`ĝ` is block upper triangular** in the flag decomposition. -/
theorem flagProj_affExt_lower (hv0 : v₀ ≠ 0) (hv : minkQ v₀ = 0) {x : isom d}
    (hx : linOf x ∈ nullStab v₀) (i j : Fin 4) (hji : j < i) :
    flagProj v₀ i * affExt x * flagProj v₀ j = 0 := by
  fin_cases i <;> fin_cases j <;> simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one,
    Fin.reduceFinMk, Fin.reduceLT] at hji ⊢ <;>
    simp only [flagProj, liftV_mul_affExt_mul_liftV, lastV_mul_affExt_mul_liftV] <;>
    apply liftV_eq_zero <;> intro y <;>
    simp only [LinearMap.comp_apply, LinearMap.smulRight_apply, LinearEquiv.coe_coe,
      map_nullLineProj hv0 hv hx, screenProj_nullLineProj, nullCoord_map hx,
      nullCoord_nullLineProj hv0 hv, nullCoord_screenProj, zero_smul]

/-- **The diagonal of `ĝ` is `(1, ρ, 1, 1)`.** -/
theorem flagProj_affExt_diag (hv0 : v₀ ≠ 0) (hv : minkQ v₀ = 0) {x : isom d}
    (hx : linOf x ∈ nullStab v₀) (i : Fin 4) (hi : i ≠ 1) :
    flagProj v₀ i * affExt x * flagProj v₀ i = flagProj v₀ i := by
  fin_cases i <;> simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, ne_eq,
    not_true_eq_false] at hi ⊢ <;>
    simp only [flagProj, liftV_mul_affExt_mul_liftV, lastV_mul_affExt_mul_lastV]
  · congr 1
    refine LinearMap.ext fun y => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, map_nullLineProj hv0 hv hx]
    rw [nullLineProj_apply v₀ (nullLineProj v₀ y), screenProj_nullLineProj,
      nullCoord_nullLineProj hv0 hv, zero_smul, sub_zero, sub_zero]
  · congr 1
    refine LinearMap.ext fun y => ?_
    simp only [LinearMap.comp_apply, LinearMap.smulRight_apply, LinearEquiv.coe_coe, map_smul,
      nullCoord_map hx, nullCoord_timeUnit hv0 hv, one_smul]

/-- **The diagonal block on the screen is the rotation part**. -/
theorem norm_flagProj_one_affExt_le (x : isom d) :
    ‖flagProj v₀ 1 * (affExt x - 1) * flagProj v₀ 1‖ ≤ ‖screenRot v₀ (linOf x) - 1‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun ⟨y, s⟩ => ?_
  have e : (flagProj v₀ 1 * (affExt x - 1) * flagProj v₀ 1) (y, s) =
      ((screenRot v₀ (linOf x) - 1) y, 0) := by
    show liftV (screenProj v₀) ((affExt x - 1) (screenProj v₀ y, 0)) = _
    rw [affExt_sub_one_apply, zero_smul, add_zero, liftV_apply, map_sub, screenProj_screenProj,
      show (screenRot v₀ (linOf x) - 1) y = screenRot v₀ (linOf x) y - y from rfl,
      screenRot_sub_self]
  rw [e]
  have e1 : ‖(((screenRot v₀ (linOf x) - 1) y, (0 : ℝ)) : Minkowski d × ℝ)‖ =
      ‖(screenRot v₀ (linOf x) - 1) y‖ := by
    rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]
  rw [e1]
  calc ‖(screenRot v₀ (linOf x) - 1) y‖ ≤ ‖screenRot v₀ (linOf x) - 1‖ * ‖y‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖screenRot v₀ (linOf x) - 1‖ * ‖((y, s) : Minkowski d × ℝ)‖ :=
        mul_le_mul_of_nonneg_left (norm_fst_le (y, s)) (norm_nonneg _)

end Flag

section Engel

variable {v₀ : Minkowski d}

/-- **The conjugated affine extension is `ρ`-close to `1`**, up to `K⁻¹` times a constant. -/
theorem norm_scale_affExt_sub_one_le (hv0 : v₀ ≠ 0) (hv : minkQ v₀ = 0) {x : isom d}
    (hx : linOf x ∈ nullStab v₀) {K : ℝ} (hK : 1 ≤ K) :
    ‖scaleBy (flagProj v₀) K * affExt x * scaleBy (flagProj v₀) K⁻¹ - 1‖ ≤
      ‖screenRot v₀ (linOf x) - 1‖ +
        K⁻¹ * ∑ i, ∑ j, ‖flagProj v₀ i * affExt x * flagProj v₀ j‖ := by
  have h1 := norm_scaleBy_conj_sub_le (flagProj v₀) (affExt x) (flagProj_affExt_lower hv0 hv hx) hK
  have h2 := sum_diag_sub_one (flagProj v₀) (flagProj_mul hv0 hv) flagProj_sum (affExt x) 1
    (flagProj_affExt_diag hv0 hv hx)
  have h3 := norm_flagProj_one_affExt_le (v₀ := v₀) x
  rw [← h2] at h3
  calc ‖scaleBy (flagProj v₀) K * affExt x * scaleBy (flagProj v₀) K⁻¹ - 1‖
      = ‖(scaleBy (flagProj v₀) K * affExt x * scaleBy (flagProj v₀) K⁻¹ -
          ∑ i, flagProj v₀ i * affExt x * flagProj v₀ i) +
          (∑ i, flagProj v₀ i * affExt x * flagProj v₀ i - 1)‖ := by rw [sub_add_sub_cancel]
    _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add h1 h3
    _ = _ := add_comm _ _

theorem iterate_commutator_mem {G : Type*} [Group G] {Γ : Subgroup G} {g h : G} (hg : g ∈ Γ)
    (hh : h ∈ Γ) (k : ℕ) : (fun x => g * x * g⁻¹ * x⁻¹)^[k] h ∈ Γ := by
  induction k with
  | zero => exact hh
  | succ k ih =>
    rw [iterate_succ_apply']
    exact Γ.mul_mem (Γ.mul_mem (Γ.mul_mem hg ih) (Γ.inv_mem hg)) (Γ.inv_mem ih)

/-- **A good scaling**: for `g, h` with linear parts fixing `v₀` and `ρ(g)` `1/64`-close to `1`,
some flag scaling `S` (inverse `S'`) brings `ĝ^{±1}` within `1/32` of `1` and `ĥ^{±1}` within `3`.
-/
theorem exists_good_scaling (hv0 : v₀ ≠ 0) (hv : minkQ v₀ = 0) {g h : isom d}
    (hg : linOf g ∈ nullStab v₀) (hh : linOf h ∈ nullStab v₀)
    (hgε : ‖screenRot v₀ (linOf g) - 1‖ < 1 / 64) :
    ∃ S S' : Minkowski d × ℝ →L[ℝ] Minkowski d × ℝ, S * S' = 1 ∧ S' * S = 1 ∧
      ‖S * affExt g * S' - 1‖ ≤ 1 / 32 ∧ ‖S * affExt g⁻¹ * S' - 1‖ ≤ 1 / 32 ∧
      ‖S * affExt h * S' - 1‖ ≤ 3 ∧ ‖S * affExt h⁻¹ * S' - 1‖ ≤ 3 := by
  set C : isom d → ℝ := fun x => ∑ i, ∑ j, ‖flagProj v₀ i * affExt x * flagProj v₀ j‖ with hCdef
  have hC0 : ∀ x, 0 ≤ C x := fun x =>
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  have hCg := hC0 g
  have hCgi := hC0 g⁻¹
  have hCh := hC0 h
  have hChi := hC0 h⁻¹
  set K : ℝ := 1 + 64 * (C g + C g⁻¹) + C h + C h⁻¹ with hKdef
  have hK1 : 1 ≤ K := by rw [hKdef]; linarith
  have hK0 : 0 < K := by linarith
  have hsmall : ∀ c : ℝ, 0 ≤ c → 64 * c ≤ K → K⁻¹ * c ≤ 1 / 64 := fun c hc hcK => by
    rw [inv_mul_le_iff₀ hK0]; linarith
  have hbig : ∀ c : ℝ, 0 ≤ c → c ≤ K → K⁻¹ * c ≤ 1 := fun c hc hcK => by
    rw [inv_mul_le_iff₀ hK0]; linarith
  obtain ⟨hSS', hS'S⟩ := scaleBy_mul_scaleBy (flagProj v₀) (flagProj_mul hv0 hv) flagProj_sum
    hK0.ne'
  have hgi : linOf g⁻¹ ∈ nullStab v₀ := by rw [linOf_inv]; exact (nullStab v₀).inv_mem hg
  have hhi : linOf h⁻¹ ∈ nullStab v₀ := by rw [linOf_inv]; exact (nullStab v₀).inv_mem hh
  have hρgi : ‖screenRot v₀ (linOf g⁻¹) - 1‖ < 1 / 64 := by
    rw [linOf_inv]; exact (norm_screenRot_inv_sub_one_le hv0 hv hg).trans_lt hgε
  refine ⟨_, _, hSS', hS'S, ?_, ?_, ?_, ?_⟩
  · have := hsmall (C g) hCg (by rw [hKdef]; linarith)
    linarith [norm_scale_affExt_sub_one_le hv0 hv hg hK1]
  · have := hsmall (C g⁻¹) hCgi (by rw [hKdef]; linarith)
    linarith [norm_scale_affExt_sub_one_le hv0 hv hgi hK1]
  · have := hbig (C h) hCh (by rw [hKdef]; linarith)
    linarith [norm_scale_affExt_sub_one_le hv0 hv hh hK1, norm_screenRot_sub_one_le_two hv0 hv hh]
  · have := hbig (C h⁻¹) hChi (by rw [hKdef]; linarith)
    linarith [norm_scale_affExt_sub_one_le hv0 hv hhi hK1,
      norm_screenRot_sub_one_le_two hv0 hv hhi]

/-- **The iterated commutators of affine extensions tend to `1`** (Zassenhaus contraction in the
scaled norm). -/
theorem norm_affExt_iterate_sub_one_le {g h : isom d}
    {S S' : Minkowski d × ℝ →L[ℝ] Minkowski d × ℝ} (hSS' : S * S' = 1) (hS'S : S' * S = 1)
    (h1 : ‖S * affExt g * S' - 1‖ ≤ 1 / 32) (h2 : ‖S * affExt g⁻¹ * S' - 1‖ ≤ 1 / 32)
    (h3 : ‖S * affExt h * S' - 1‖ ≤ 3) (h4 : ‖S * affExt h⁻¹ * S' - 1‖ ≤ 3) (k : ℕ) :
    ‖affExt ((fun x => g * x * g⁻¹ * x⁻¹)^[k] h) - 1‖ ≤ ‖S'‖ * ‖S‖ * (3 * (1 / 2) ^ k) := by
  have hF : ∀ a b : isom d, S * affExt (a * b) * S' =
      (S * affExt a * S') * (S * affExt b * S') := fun a b => by
    rw [affExt_mul]
    calc S * (affExt a * affExt b) * S' = S * affExt a * (S' * S) * affExt b * S' := by
          rw [hS'S, mul_one]; noncomm_ring
      _ = S * affExt a * S' * (S * affExt b * S') := by noncomm_ring
  have hF1 : S * affExt (1 : isom d) * S' = 1 := by rw [affExt_one, mul_one, hSS']
  have hk1 := (norm_iterate_commutator_le (F := fun x => S * affExt x * S')
    ContinuousLinearMap.norm_id_le hF hF1 h1 h2 h3 h4 k).1
  generalize (fun x => g * x * g⁻¹ * x⁻¹)^[k] h = y at hk1 ⊢
  have e : S' * (S * affExt y * S' - 1) * S = affExt y - 1 := by
    rw [mul_sub, sub_mul, mul_one, hS'S, show S' * (S * affExt y * S') * S =
      (S' * S) * affExt y * (S' * S) by simp only [mul_assoc], hS'S, one_mul, mul_one]
  rw [← e]
  calc ‖S' * (S * affExt y * S' - 1) * S‖ ≤ ‖S'‖ * ‖S * affExt y * S' - 1‖ * ‖S‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ ‖S'‖ * (3 * (1 / 2) ^ k) * ‖S‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk1 (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

/-- **The Engel property (Bieberbach's contraction, made discrete)**: for `Γ` discrete with
linear parts fixing `v₀`, an element `g ∈ Γ` whose rotation part is `1/64`-close to `1` is an
Engel element: every iterated commutator `[g, [g, …, [g, h]]]` (`h ∈ Γ`) is eventually `1`.
Conjugating by the flag scaling `D_K` makes `ĝ`, `ĥ` close to block-diagonal, the halving step
makes the iterates tend to `1`, and discreteness makes them equal to `1`. -/
theorem exists_iterate_commutator_eq_one {Γ : Subgroup (isom d)} (hdisc : DiscreteTopology Γ)
    (hv0 : v₀ ≠ 0) (hv : minkQ v₀ = 0) (hfix : ∀ γ ∈ Γ, linOf γ v₀ = v₀) {g h : isom d}
    (hg : g ∈ Γ) (hh : h ∈ Γ) (hgε : ‖screenRot v₀ (linOf g) - 1‖ < 1 / 64) :
    ∃ N : ℕ, (fun x => g * x * g⁻¹ * x⁻¹)^[N] h = 1 := by
  obtain ⟨η, hη, hiso⟩ := exists_affExt_isolated hdisc
  obtain ⟨S, S', hSS', hS'S, h1, h2, h3, h4⟩ := exists_good_scaling hv0 hv
    (linOf_mem_nullStab hfix hg) (linOf_mem_nullStab hfix hh) hgε
  have hM : 0 < 3 * (‖S'‖ * ‖S‖ + 1) := by positivity
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hη hM) (show (1 / 2 : ℝ) < 1 by norm_num)
  refine ⟨k, hiso _ (iterate_commutator_mem hg hh k) ?_⟩
  refine (norm_affExt_iterate_sub_one_le hSS' hS'S h1 h2 h3 h4 k).trans_lt ?_
  rw [lt_div_iff₀ hM] at hk
  have hp : (0 : ℝ) ≤ (1 / 2) ^ k := by positivity
  nlinarith [norm_nonneg S, norm_nonneg S']

/-- **Step 4 for `ε = 1/64`**: rotation parts of elements of a discrete `Γ` (linear parts fixing
`v₀`) that are `1/64`-close to `1` commute — the Engel property, then the backward induction. -/
theorem commute_screenRot_of_lt_inv64 {Γ : Subgroup (isom d)} (hdisc : DiscreteTopology Γ)
    (hv0 : v₀ ≠ 0) (hv : minkQ v₀ = 0) (hfix : ∀ γ ∈ Γ, linOf γ v₀ = v₀) {g h : isom d}
    (hg : g ∈ Γ) (hh : h ∈ Γ) (hgε : ‖screenRot v₀ (linOf g) - 1‖ < 1 / 64)
    (hhε : ‖screenRot v₀ (linOf h) - 1‖ < 1 / 64) :
    Commute (screenRot v₀ (linOf g)) (screenRot v₀ (linOf h)) := by
  obtain ⟨N, hN⟩ := exists_iterate_commutator_eq_one hdisc hv0 hv hfix hg hh hgε
  exact commute_screenRot_of_iterate_eq_one hv0 hv (linOf_mem_nullStab hfix hg)
    (by linarith) N h (linOf_mem_nullStab hfix hh) (by linarith) hN

end Engel


/-! ## §3 The deep step and the assembly -/

section Assembly

/-- **Steps 5–6, proved**: if the rotation parts of elements of `Γ` that are `ε`-close to `1`
commute, the subgroup they generate has finite index and pairwise commuting linear parts. -/
theorem exists_comm_linOf_of_local {Γ : Subgroup (isom d)} {v₀ : Minkowski d} (hv0 : v₀ ≠ 0)
    (hv : minkQ v₀ = 0) (hfix : ∀ γ ∈ Γ, linOf γ v₀ = v₀)
    (hell : ∀ γ ∈ Γ, IsElliptic (linOf γ)) {ε : ℝ} (hε : 0 < ε)
    (hloc : ∀ g ∈ Γ, ∀ h ∈ Γ, ‖screenRot v₀ (linOf g) - 1‖ < ε →
      ‖screenRot v₀ (linOf h) - 1‖ < ε →
        Commute (screenRot v₀ (linOf g)) (screenRot v₀ (linOf h))) :
    ∃ Γ' : Subgroup (isom d), Γ' ≤ Γ ∧ Γ'.relIndex Γ ≠ 0 ∧
      ∀ g ∈ Γ', ∀ h ∈ Γ', linOf g * linOf h = linOf h * linOf g := by
  set f : isom d → (Minkowski d →L[ℝ] Minkowski d) := fun γ => screenRot v₀ (linOf γ) with hf
  have hmul : ∀ a ∈ Γ, ∀ b ∈ Γ, f (a * b) = f a * f b := fun a ha b hb => by
    simp only [hf, linOf_mul]
    exact screenRot_mul hv0 hv (hfix a ha) (linOf_mem b) (hfix b hb)
  have hone : f 1 = 1 := screenRot_one
  set S : Set (isom d) := {g | g ∈ Γ ∧ ‖f g - 1‖ < ε} with hSdef
  have hS : S ⊆ Γ := fun g hg => hg.1
  have hle : Subgroup.closure S ≤ Γ := (Subgroup.closure_le Γ).2 hS
  refine ⟨Subgroup.closure S, hle,
    relIndex_closure_ne_zero hmul hone (fun g hg => norm_screenRot_le hv0 hv (linOf_mem g)
      (hfix g hg)) hε, ?_⟩
  intro g hg h hh
  have hcomm : Commute (f g) (f h) :=
    commute_of_mem_closure hmul hone hS (fun a ha b hb => hloc a ha.1 b hb.1 ha.2 hb.2) hg hh
  have hgΓ := hle hg
  have hhΓ := hle hh
  have hgi := Γ.inv_mem hgΓ
  have hhi := Γ.inv_mem hhΓ
  have hcΓ : g * h * g⁻¹ * h⁻¹ ∈ Γ := Γ.mul_mem (Γ.mul_mem (Γ.mul_mem hgΓ hhΓ) hgi) hhi
  have hc : f (g * h * g⁻¹ * h⁻¹) = 1 := by
    rw [hmul _ (Γ.mul_mem (Γ.mul_mem hgΓ hhΓ) hgi) _ hhi, hmul _ (Γ.mul_mem hgΓ hhΓ) _ hgi,
      hmul _ hgΓ _ hhΓ, hcomm.eq, mul_assoc (f h), ← hmul _ hgΓ _ hgi, mul_inv_cancel, hone,
      mul_one, ← hmul _ hhΓ _ hhi, mul_inv_cancel, hone]
  have h1 := eq_one_of_screenRot_eq_one hv0 hv (linOf_mem _) (hfix _ hcΓ) (hell _ hcΓ) hc
  rw [linOf_mul, linOf_mul, linOf_mul, linOf_inv, linOf_inv, ← commutatorElement_def] at h1
  exact commutatorElement_eq_one_iff_mul_comm.1 h1

/-- **The Zassenhaus step** (step 4 of the module docstring): for `Γ` discrete whose
linear parts fix a nonzero null `v₀`, elements of `Γ` whose rotation parts are `ε`-close to `1`
have commuting rotation parts, for some `ε > 0`. No ellipticity is needed. **Proved**, with the
uniform `ε = 1/64` (`commute_screenRot_of_lt_inv64`: Engel property from discreteness, then
Frobenius' lemma backwards along the iterated commutators). -/
theorem exists_commute_screenRot_of_discrete {Γ : Subgroup (isom d)} (hdisc : DiscreteTopology Γ)
    {v₀ : Minkowski d} (hv0 : v₀ ≠ 0) (hv : minkQ v₀ = 0) (hfix : ∀ γ ∈ Γ, linOf γ v₀ = v₀) :
    ∃ ε > 0, ∀ g ∈ Γ, ∀ h ∈ Γ, ‖screenRot v₀ (linOf g) - 1‖ < ε →
      ‖screenRot v₀ (linOf h) - 1‖ < ε →
        Commute (screenRot v₀ (linOf g)) (screenRot v₀ (linOf h)) :=
  ⟨1 / 64, by norm_num, fun _ hg _ hh hgε hhε =>
    commute_screenRot_of_lt_inv64 hdisc hv0 hv hfix hg hh hgε hhε⟩

variable (d) in
/-- **`TitsVirtuallyAbelianNull d`** (DEC-50; the gap of l.2621–2622), assembled from the proved
steps 1–3, 5, 6 and the (proved) step 4 `exists_commute_screenRot_of_discrete`; no `sorry`. -/
theorem titsVirtuallyAbelianNull : TitsVirtuallyAbelianNull d := by
  intro Γ hdisc v₀ hv0 hv hfix hell
  obtain ⟨ε, hε, hloc⟩ := exists_commute_screenRot_of_discrete hdisc hv0 hv hfix
  exact exists_comm_linOf_of_local hv0 hv hfix hell hε hloc

variable (d) in
/-- **`TitsVirtuallyAbelianNull d` for `d ≤ 2`** (Barbot's `n ≤ 3`), with **no `sorry`**: the
deep step holds there with any `ε` (`commute_screenRot_of_le_two`); discreteness is not used. -/
theorem titsVirtuallyAbelianNull_of_le_two (hd : d ≤ 2) : TitsVirtuallyAbelianNull d := by
  intro Γ _ v₀ hv0 hv hfix hell
  exact exists_comm_linOf_of_local hv0 hv hfix hell one_pos fun g hg h hh _ _ =>
    commute_screenRot_of_le_two hd hv0 hv (linOf g) (linOf h)

end Assembly

end Causal.Flat
