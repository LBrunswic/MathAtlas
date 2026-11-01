import CausalScaffold.Flat.Nonloxodromic

/-!
# `CausalScaffold.Flat.TitsNull` — a discrete null-fixing all-elliptic group is virtually abelian in its linear parts

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §9.2–9.3,
the gap of Prop 9.1 at l.2621–2622 of the **labelled** `papers/barbot/legacy/labeled/GHFspace.tex`
(DEC-50: "proved, not carried as a named external"). Package WP-34g-TitsNull.

**No ledger label is certified here.** The statement is not one of Barbot's environments: it is
the `Prop` `TitsVirtuallyAbelianNull d` of `Flat/Nonloxodromic` (not redefined here), which the
§9 assembly `nonloxodromic` carries as a hypothesis for the branch the paper overlooks.

* `titsVirtuallyAbelianNull` (every `d`) — `TitsVirtuallyAbelianNull d`, **assembled** from the
  proved reductions below and ONE tagged `sorry`, `exists_commute_screenRot_of_discrete` (the
  Zassenhaus/Auslander step; obstruction in its tag), through the proved
  `exists_comm_linOf_of_local` (steps 5–6 below). `titsVirtuallyAbelianNull_of_le_two`
  (`d ≤ 2`, Barbot's `n ≤ 3`): **no `sorry`** — there the deep step holds for every `ε`
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
4. **The deep step (Zassenhaus/Auslander; the one `sorry`).** There is `ε > 0` such that any
   two elements of `ρ(Γ)` within `ε` of `1` commute. *Derivation.* The affine maps whose
   linear part fixes `v₀` form a Lie group `G = K ⋉ N`, `K ≅ SO(d − 1)` (the rotation part) and
   `N` = null rotations `⋉` translations, closed, connected, nilpotent (unipotent) and normal
   (it is the kernel of `ρ`). *Auslander's theorem* (M. S. Raghunathan, *Discrete subgroups of
   Lie groups*, 1972, Ch. VIII, Thm 8.24 — the number is not checked against an archived
   copy; L. Auslander, Ann. of Math. 71 (1960)): for `Γ`
   discrete in a Lie group and `R` a closed connected solvable normal subgroup, the identity
   component of `closure (Γ R)` is solvable. Its image under `G → G/N ≅ K` (an open map, `K`
   compact) is the identity component `H⁰` of `H = closure ρ(Γ)`, a compact connected solvable
   Lie group, i.e. a torus: abelian. `H` is a compact Lie group (Cartan), so `H⁰` is open in
   `H`, and an `ε`-ball of `1` meets `H` inside `H⁰`. *Connectedness.* Auslander's theorem is
   usually stated for a connected `G`, and `G` need not be (`K` may be disconnected); apply it to
   `Γ ∩ G⁰` instead, which is discrete in `G⁰ = K⁰ ⋉ N` (`N` connected) and of finite index in
   `Γ` (`K` compact has finitely many components), so the closure of its rotation parts has
   finite index in `H` (hence is open in `H`) and the same identity component `H⁰`, which is
   therefore abelian, and the `ε`-ball argument above applies unchanged. (Alternative route, the one the
   `TitsVirtuallyAbelianNull` docstring names: `G` is amenable, so is the discrete `Γ`, so it
   has no free subgroup; Tits' alternative makes `Γ` virtually solvable; a solvable subgroup of
   the compact `K` has a torus as identity component of its closure; same conclusion.)
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
contains the `SO(4)`-elements `z ↦ q z`). Discreteness is spent in step 4 alone.

## Hypothesis checklist

Barbot states no hypotheses for this step (he does not state the step at all: it is the gap of
l.2621–2622, DEC-50), so the "paper hypothesis" column lists the hypotheses of the project `Prop`
`TitsVirtuallyAbelianNull` of `Flat/Nonloxodromic`, read off the §9 situation at l.2596–2629.

| paper hypothesis | here |
|---|---|
| `Γ` discrete in `Isom(𝐌ⁿ)` (`isomTopology`) | ✓ carried; spent only in `exists_commute_screenRot_of_discrete` (the `sorry`); not needed when `d ≤ 2` |
| `v₀ ≠ 0`, `minkQ v₀ = 0` | ✓ carried (the screen and step 3) |
| `L(γ) v₀ = v₀` for `γ ∈ Γ` | ✓ carried (multiplicativity of `ρ`) |
| every `L(γ)` elliptic | ✓ carried; spent only in step 3 (commutators); the deep step does not need it |

## SCOPE (disclosed)

* **Sorries (1)**: `exists_commute_screenRot_of_discrete` — Auslander's theorem on discrete
  subgroups of `K ⋉ N` (step 4). mathlib has no Lie groups, no Cartan closed-subgroup theorem
  and no structure theory of compact groups (tori), so neither Auslander's route nor Tits' is
  formalizable at this pin; the step is stated for its weakest hypotheses (no ellipticity).
  The named external `AuslanderCarriereDalbo d` of `Flat/Externals` (`bthm:ausl`) does not
  discharge it on its own: it makes `G₀ = (closure L(Γ))⁰` nilpotent, but step 4 also needs
  `G₀` OPEN in `closure L(Γ)` (Cartan) to reach the elements of `ρ(Γ)` near `1`, and DEC-50
  asks for a proof rather than a carried external in any case.
  Consequently `titsVirtuallyAbelianNull` (every `d`) rests on that `sorry`, and
  `titsVirtuallyAbelianNull_of_le_two` (`d ≤ 2`) does not.
* `ρ` is defined through the screen `S = {v₀, e₀}^⊥`, a section of Barbot's quotient `P̄₀`
  (mathlib quotients by a submodule would also do; the section makes `ρ` an endomorphism of
  `𝐌ⁿ` and gives the norm for free). The choice of `e₀` is immaterial to the statement.
* The deep step is stated with `ε` depending on `Γ` (the honest form: for a finite non-abelian
  `ρ(Γ)` with elements near `1` no uniform `ε` is claimed).
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

/-- **The Zassenhaus/Auslander step** (step 4 of the module docstring): for `Γ` discrete whose
linear parts fix a nonzero null `v₀`, elements of `Γ` whose rotation parts are `ε`-close to `1`
have commuting rotation parts, for some `ε > 0` (depending on `Γ`). No ellipticity is needed. -/
theorem exists_commute_screenRot_of_discrete {Γ : Subgroup (isom d)} (hdisc : DiscreteTopology Γ)
    {v₀ : Minkowski d} (hv0 : v₀ ≠ 0) (hv : minkQ v₀ = 0) (hfix : ∀ γ ∈ Γ, linOf γ v₀ = v₀) :
    ∃ ε > 0, ∀ g ∈ Γ, ∀ h ∈ Γ, ‖screenRot v₀ (linOf g) - 1‖ < ε →
      ‖screenRot v₀ (linOf h) - 1‖ < ε →
        Commute (screenRot v₀ (linOf g)) (screenRot v₀ (linOf h)) := by
  sorry -- SORRY(TitsVirtuallyAbelianNull/Auslander): the identity component of the closure `H` of the rotation parts `ρ(Γ) ⊆ SO(d − 1)` is abelian and open in `H`. This is Auslander's theorem for the discrete `Γ` in `G = K ⋉ N` (`N` = null rotations ⋉ translations, connected nilpotent normal; Raghunathan, Discrete subgroups of Lie groups, Thm 8.24, number unchecked: `(closure (Γ N))⁰` solvable; applied to `Γ ∩ G⁰`, of finite index, `G⁰ = K⁰ ⋉ N` connected, whose rotation-part closure has the same identity component) plus Cartan's closed-subgroup theorem (`H` a compact Lie group, `H⁰` open) and compact connected solvable ⇒ torus; or Tits' alternative for the amenable `Γ`. None of Lie groups, Cartan's theorem, the structure of compact groups or Tits' alternative is in mathlib at this pin.

variable (d) in
/-- **`TitsVirtuallyAbelianNull d`** (DEC-50; the gap of l.2621–2622), assembled from the proved
steps 1–3, 5, 6 and the step 4 `exists_commute_screenRot_of_discrete`. -/
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
