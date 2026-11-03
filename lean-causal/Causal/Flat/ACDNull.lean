import Causal.Flat.TitsNull

/-!
# `Causal.Flat.ACDNull` — near-identity elements of a nilpotent subgroup of `SO₀(1, d)` fixing a timelike or a null vector commute

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §5,
Theorem 5.1 (`bthm:ausl`, `GHFspace.tex:1696`), carried as the external
`AuslanderCarriereDalbo d` (`Flat/Externals`, DEC-36). **No ledger label is certified here**:
this module is Step 2 ("Lorentz Frobenius lemma, with no discreteness") of the Lorentz
Zassenhaus–Frobenius route of `docs/CARRIERE-DALBO-SURVEY.md` §2.2 T1 (DEC-121), in its two
non-loxodromic cases (the dichotomy `FixesTimelikeOrNull`, `fixesTimelikeOrNull_of_noLox`,
`Flat/GromovProof`); the loxodromic case is `Flat/ACDLoxodromic`.

> Let $\Gamma$ be a discrete subgroup of $\mbox{Aff}(n, {\mathbb R})$.
> Then, the identity component $G_{0}$ of
> the closure of $L(\Gamma)$ in $GL(n, {\mathbb R})$ is nilpotent. (l.1699–1701)

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; `Minkowski d` has `d` spatial
dimensions, so Barbot's `n` is `d + 1`.

## The proof

Let `N ≤ SO₀(1, d)` be nilpotent and `a, b ∈ N` with `‖a − 1‖, ‖b − 1‖ < 1/2` (operator norm on
`Minkowski d`). Nilpotent groups are Engel (`exists_iterate_commutator_eq_one_of_isNilpotent`).

**Null case** (`commute_of_isNilpotent_of_fixNull`): `N` fixes a nonzero null `v₀`.
1. The rotation parts `ρ = screenRot v₀` (`Flat/TitsNull`) satisfy `ρ(A) − 1 = π (A − 1) π`
   with `‖π x‖ ≤ ‖x‖` (`π` is the spatial orthogonal projection off the direction of `v₀`), so
   `‖ρ(A) − 1‖ ≤ ‖A − 1‖` uniformly in `v₀` (`norm_screenRot_sub_one_le`).
2. Frobenius backwards along `[a, [a, …, [a, b]]] = 1`
   (`commute_screenRot_of_iterate_eq_one`, lifted to `isom d` by `Nonlox.nfIsom`): `ρ(a)`,
   `ρ(b)` commute, so `C = [a, b]` has `ρ(C) = 1`: `C` moves `W = v₀^⊥` along `ℓ₀ = ℝ v₀`
   (`sub_mem_span_of_screenRot_eq_one`).
3. **`C = 1`** (`eq_one_of_commutator_null`, the survey's "`z = 0`" step, made coordinate-free):
   fix `n` with `⟨n | v₀⟩ = 1` and set `m_X = X⁻¹ n − n ∈ W`. For `X` moving `W` along `ℓ₀`,
   `(X − 1) u = ⟨u | m_X⟩ v₀` on `W`, and `[A, X]` (`A v₀ = v₀`) is of the same kind with
   `m ≡ (A − 1) m_X` modulo `ℓ₀`. Engel gives `(a − 1)ᵏ m_C ∈ ℓ₀`; on `W` the form is
   semidefinite with radical `ℓ₀`, so `(a − 1) m_C ∈ ℓ₀` (if `(A − 1) x ∈ ℓ₀`, `x = (A − 1) y`,
   then `minkQ x = 0`); likewise for `b`. Then `m_C = b (a − 1) m_b + b a (b⁻¹ − 1) m_a` is
   `⟨·|·⟩`-orthogonal to itself, hence in `ℓ₀`, so `C` is the identity on `W`, hence `C = 1`.

**Timelike case** (`commute_of_isNilpotent_of_fixTimelike`): `N` fixes `w`, `minkQ w = −1`.
Extend each `A` to `Minkowski (d + 1) = 𝐌ⁿ ⊕ ℝ e_{d}` by the identity on the new spacelike axis:
an injective homomorphism into `SO₀(1, d + 1)` with `‖Â − 1‖ ≤ ‖A − 1‖`, whose image fixes the
null vector `ŵ + e_d`. The null case in dimension `d + 1` concludes. (Fallback, if the dimension
shift resists: Frobenius on `w^⊥` with the uniform bound `‖(A − 1)|_{w^⊥}‖_{w^⊥} ≤ ‖A − 1‖`,
from `‖Tᵏ‖ ≤ C ‖A − 1‖ᵏ` and `‖T^{2ʲ}‖ = ‖T‖^{2ʲ}` for the normal `T = (A − 1)|_{w^⊥}`.)

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| (route) `N ≤ SO₀(1, n−1)` nilpotent | ✓ carried: `N : Subgroup (lorentz d)`, `Group.IsNilpotent N` |
| (route) `N` fixes a timelike or nonzero null vector | ✓ carried: `FixesTimelikeOrNull N` (the conclusion of `fixesTimelikeOrNull_of_noLox`) |
| (route) `a`, `b` near `1` | ✓ carried: `‖a − 1‖ < 1/2`, `‖b − 1‖ < 1/2` (operator norm); uniform in `N` |
| `Γ` discrete | ⚠ weakened: not used (Step 2 is discreteness-free) |

## SCOPE (disclosed)

* The non-loxodromic cases of Step 2 only; the loxodromic case is `Flat/ACDLoxodromic`, which
  takes `commute_of_isNilpotent_of_fixNull` and `norm_screenRot_sub_one_le` as hypotheses.
* Proved in full (2026-11-03), no `sorry`, no axiom; the statements of
  `norm_screenRot_sub_one_le`, `commute_of_isNilpotent_of_fixNull` and
  `commute_of_isNilpotent_of_fixesTimelikeOrNull` are those of the planner's skeleton (the
  assembly uses them). In `norm_screenProj_le` the hypotheses `v₀ ≠ 0`, `minkQ v₀ = 0` are unused
  (the contraction holds for every `v₀`) and are named `_hv0`, `_hv`; the type is unchanged.
* Step 3 runs the Engel induction on the invariant itself: `[a,ₖX] = 1` gives `a m_X ≡ m_X`
  modulo `ℓ₀` (`acdn_engel_shear`), each level by the recursion `acdn_m_commutator` and the
  semisimplicity `acdn_semisimple`, so no power `(a − 1)ᵏ` is formed.
* The timelike case is the dimension shift (`acdnSplit`, `acdnLift`, `acdnLiftHom`), with the
  fixed null vector `(w, √(−minkQ w))` (no normalisation of `w`); the Frobenius fallback is not
  needed.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
DEC-121 (`docs/CARRIERE-DALBO-SURVEY.md` §2.2, T1 Step 2, timelike and null cases).
-/

namespace Causal.Flat

open Set Function Topology Module Submodule

open scoped commutatorElement

variable {d : ℕ}

/-- **Nilpotent groups are Engel**: in a nilpotent group, `[a, [a, …, [a, b]]] = 1` (the
iterated commutator `hₖ = [a, hₖ₋₁]` lies in `lowerCentralSeries G k`). -/
theorem exists_iterate_commutator_eq_one_of_isNilpotent {G : Type*} [Group G]
    [Group.IsNilpotent G] (a b : G) : ∃ n : ℕ, (fun x => a * x * a⁻¹ * x⁻¹)^[n] b = 1 := by
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.1 ‹Group.IsNilpotent G›
  refine ⟨n, ?_⟩
  have key : ∀ k, (fun x => a * x * a⁻¹ * x⁻¹)^[k] b ∈ (⊤ : Subgroup G).lowerCentralSeries k := by
    intro k
    induction k with
    | zero => exact Subgroup.mem_top _
    | succ k ih =>
      rw [iterate_succ_apply', Subgroup.lowerCentralSeries_succ]
      have h := Subgroup.commutator_mem_commutator ih (Subgroup.mem_top a)
      have e : a * (fun x => a * x * a⁻¹ * x⁻¹)^[k] b * a⁻¹ *
          ((fun x => a * x * a⁻¹ * x⁻¹)^[k] b)⁻¹ =
          ⁅(fun x => a * x * a⁻¹ * x⁻¹)^[k] b, a⁆⁻¹ := by
        rw [commutatorElement_inv, commutatorElement_def]
      rw [e]
      exact inv_mem h
  have h := key n
  rw [hn] at h
  exact (Subgroup.mem_bot).1 h

/-- The screen projection is a contraction of the sup norm: it is `(t, y) ↦ (0, y − ⟨y, û⟩ û)`,
`û` the unit spatial direction of `v₀`. -/
theorem norm_screenProj_le {v₀ : Minkowski d} (_hv0 : v₀ ≠ 0) (_hv : minkQ v₀ = 0)
    (x : Minkowski d) : ‖screenProj v₀ x‖ ≤ ‖x‖ := by
  set y : Minkowski d := ((0 : ℝ), x.2) with hydef
  set p := screenProj v₀ y with hpdef
  have hpS : p ∈ nullScreen v₀ := screenProj_mem v₀ y
  have hp1 : p.1 = 0 := fst_eq_zero_of_mem_nullScreen v₀ hpS
  set c := y - p with hcdef
  have hcC : c ∈ nullPlaneSpan v₀ := sub_screenProj_mem v₀ y
  have hc1 : c.1 = 0 := by rw [hcdef, Prod.fst_sub, hp1, hydef, sub_zero]
  have hB : minkB p c = 0 := by rw [minkB_comm]; exact hpS c hcC
  have hyq : minkQ y = minkQ p + 2 * minkB p c + minkQ c := by
    rw [← minkQ_add, hcdef, add_sub_cancel]
  have hyQ : minkQ y = ‖x.2‖ ^ 2 := by rw [minkQ, hydef]; ring
  have hcQ : 0 ≤ minkQ c := minkQ_nonneg_of_fst_eq_zero hc1
  rw [hyQ, hB, minkQ_eq_norm_sq_of_mem_nullScreen v₀ hpS] at hyq
  have hle : ‖p‖ ≤ ‖x.2‖ := by
    have h2 : ‖p‖ ^ 2 ≤ ‖x.2‖ ^ 2 := by linarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2
  rw [screenProj_eq_screenProj_snd]
  exact hle.trans (norm_snd_le x)

/-- **Rotation parts are uniformly controlled**: `‖ρ(A) − 1‖ ≤ ‖A − 1‖`, for every `A` and every
nonzero null `v₀` (`ρ(A) − 1 = π (A − 1) π`). -/
theorem norm_screenRot_sub_one_le {v₀ : Minkowski d} (hv0 : v₀ ≠ 0) (hv : minkQ v₀ = 0)
    (A : Minkowski d ≃ₗ[ℝ] Minkowski d) : ‖screenRot v₀ A - 1‖ ≤ ‖linToCLM A - 1‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  have e : (screenRot v₀ A - 1) x =
      screenProj v₀ ((linToCLM A - 1) (screenProj v₀ x)) := by
    change screenRot v₀ A x - x = screenProj v₀ (A (screenProj v₀ x) - screenProj v₀ x)
    rw [screenRot_sub_self, map_sub, screenProj_screenProj]
  rw [e]
  calc ‖screenProj v₀ ((linToCLM A - 1) (screenProj v₀ x))‖
      ≤ ‖(linToCLM A - 1) (screenProj v₀ x)‖ := norm_screenProj_le hv0 hv _
    _ ≤ ‖linToCLM A - 1‖ * ‖screenProj v₀ x‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖linToCLM A - 1‖ * ‖x‖ :=
        mul_le_mul_of_nonneg_left (norm_screenProj_le hv0 hv x) (norm_nonneg _)

/-- **Trivial rotation part**: a Lorentz map fixing `v₀` with `ρ(A) = 1` moves `v₀^⊥` along
`ℝ v₀` (the `hperp` step of `eq_one_of_screenRot_eq_one`, Flat/TitsNull, without ellipticity). -/
theorem sub_mem_span_of_screenRot_eq_one {v₀ : Minkowski d} (hv0 : v₀ ≠ 0) (hv : minkQ v₀ = 0)
    {A : Minkowski d ≃ₗ[ℝ] Minkowski d} (hA : A ∈ lorentz d) (hfix : A v₀ = v₀)
    (h : screenRot v₀ A = 1) (w : Minkowski d) (hw : minkB v₀ w = 0) : A w - w ∈ ℝ ∙ v₀ := by
  have hscr : ∀ p ∈ nullScreen v₀, A p - p ∈ ℝ ∙ v₀ := by
    intro p hp
    have e := congrArg (fun f : Minkowski d →L[ℝ] Minkowski d => f p) h
    simp only [screenRot_apply, screenProj_of_mem v₀ hp, sub_self, add_zero] at e
    rw [show (1 : Minkowski d →L[ℝ] Minkowski d) p = p from rfl] at e
    have := sub_screenProj_apply_mem hv0 hv hA hfix hp
    rwa [e] at this
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


/-! ### The `z = 0` step -/

section ZeroStep

variable {v₀ : Minkowski d}

/-- A map fixing `v₀` preserves the line `ℓ₀ = ℝ v₀`. -/
theorem acdn_map_mem_span {A : Minkowski d ≃ₗ[ℝ] Minkowski d} (hfix : A v₀ = v₀)
    {x : Minkowski d} (hx : x ∈ ℝ ∙ v₀) : A x ∈ ℝ ∙ v₀ := by
  obtain ⟨t, rfl⟩ := mem_span_singleton.1 hx
  rw [map_smul, hfix]
  exact smul_mem _ _ (mem_span_singleton_self v₀)

theorem acdn_inv_apply_self {A : Minkowski d ≃ₗ[ℝ] Minkowski d} (hfix : A v₀ = v₀) :
    A⁻¹ v₀ = v₀ :=
  A.symm_apply_eq.2 hfix.symm

theorem acdn_apply_inv_apply (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (x : Minkowski d) :
    A (A⁻¹ x) = x :=
  A.apply_symm_apply x

theorem acdn_inv_apply_apply (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (x : Minkowski d) :
    A⁻¹ (A x) = x :=
  A.symm_apply_apply x

/-- A Lorentz map fixing `v₀` preserves `v₀^⊥`. -/
theorem acdn_minkB_apply {A : Minkowski d ≃ₗ[ℝ] Minkowski d} (hA : A ∈ lorentz d)
    (hfix : A v₀ = v₀) {w : Minkowski d} (hw : minkB v₀ w = 0) : minkB v₀ (A w) = 0 := by
  conv_lhs => rw [← hfix]
  rw [minkB_map (lorentz.minkQ_apply hA)]
  exact hw

/-- `⟨A x | y⟩ = ⟨x | A⁻¹ y⟩` for a Lorentz map. -/
theorem acdn_minkB_apply_left {A : Minkowski d ≃ₗ[ℝ] Minkowski d} (hA : A ∈ lorentz d)
    (x y : Minkowski d) : minkB (A x) y = minkB x (A⁻¹ y) := by
  have h := minkB_map (lorentz.minkQ_apply hA) x (A⁻¹ y)
  rwa [acdn_apply_inv_apply] at h

/-- **A null vector of `v₀^⊥` is a multiple of `v₀`.** -/
theorem acdn_mem_span_of_null (hv0 : v₀ ≠ 0) (hv : minkQ v₀ = 0) {x : Minkowski d}
    (hx : minkB v₀ x = 0) (hq : minkQ x = 0) : x ∈ ℝ ∙ v₀ := by
  have hc : x - screenProj v₀ x ∈ ℝ ∙ v₀ := by
    refine mem_span_of_mem_nullPlaneSpan hv0 hv (sub_screenProj_mem v₀ x) ?_
    rw [minkB_sub_left, minkB_comm x, hx, minkB_comm,
      minkB_self_of_mem_nullScreen v₀ (screenProj_mem v₀ x), sub_zero]
  obtain ⟨t, ht⟩ := mem_span_singleton.1 hc
  have hpS := screenProj_mem v₀ x
  have hp : screenProj v₀ x = 0 := by
    have e : x = screenProj v₀ x + t • v₀ := by rw [ht]; abel
    have hB : minkB (screenProj v₀ x) (t • v₀) = 0 := by
      rw [minkB_smul_right, minkB_comm, minkB_self_of_mem_nullScreen v₀ hpS, mul_zero]
    have h2 := hq
    rw [e, minkQ_add, minkQ_smul, hv, hB, minkQ_eq_norm_sq_of_mem_nullScreen v₀ hpS] at h2
    have h3 : ‖screenProj v₀ x‖ ^ 2 = 0 := by linarith
    exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h3)
  rw [hp, sub_zero] at hc
  exact hc

/-- For a Lorentz map `X` fixing `v₀` and moving `v₀^⊥` along `ℝ v₀`, and `⟨v₀ | n⟩ = 1`:
`X u − u = ⟨u | X⁻¹ n − n⟩ v₀` on `v₀^⊥`. -/
theorem acdn_shear_apply {n : Minkowski d} (hn : minkB v₀ n = 1)
    {X : Minkowski d ≃ₗ[ℝ] Minkowski d} (hX : X ∈ lorentz d)
    (hXW : ∀ w, minkB v₀ w = 0 → X w - w ∈ ℝ ∙ v₀) {u : Minkowski d} (hu : minkB v₀ u = 0) :
    X u - u = minkB u (X⁻¹ n - n) • v₀ := by
  obtain ⟨t, ht⟩ := mem_span_singleton.1 (hXW u hu)
  have h1 : minkB (X u - u) n = t := by
    rw [← ht, minkB_smul_left, hn, mul_one]
  have h2 : minkB (X u - u) n = minkB u (X⁻¹ n - n) := by
    rw [minkB_sub_left, acdn_minkB_apply_left hX, minkB_sub_right]
  rw [← ht, ← h1, h2]

/-- `X⁻¹ n − n ∈ v₀^⊥` for a Lorentz `X` fixing `v₀`, when `⟨v₀ | n⟩ = 1`. -/
theorem acdn_minkB_m {n : Minkowski d} {X : Minkowski d ≃ₗ[ℝ] Minkowski d}
    (hX : X ∈ lorentz d) (hfix : X v₀ = v₀) : minkB v₀ (X⁻¹ n - n) = 0 := by
  have h := acdn_minkB_apply_left hX v₀ n
  rw [hfix] at h
  rw [minkB_sub_right, ← h, sub_self]

/-- The inverse of a shear is a shear. -/
theorem acdn_shear_inv {X : Minkowski d ≃ₗ[ℝ] Minkowski d} (hfix : X v₀ = v₀)
    (hXW : ∀ w, minkB v₀ w = 0 → X w - w ∈ ℝ ∙ v₀) {w : Minkowski d} (hw : minkB v₀ w = 0) :
    X⁻¹ w - w ∈ ℝ ∙ v₀ := by
  have h := acdn_map_mem_span (acdn_inv_apply_self hfix) (hXW w hw)
  rw [map_sub, acdn_inv_apply_apply] at h
  have e : X⁻¹ w - w = -(w - X⁻¹ w) := by abel
  rw [e]
  exact neg_mem h

/-- `A x − x ∈ ℓ₀` implies `A⁻¹ x − x ∈ ℓ₀`, for `A` fixing `v₀`. -/
theorem acdn_inv_sub_mem {A : Minkowski d ≃ₗ[ℝ] Minkowski d} (hfix : A v₀ = v₀)
    {x : Minkowski d} (h : A x - x ∈ ℝ ∙ v₀) : A⁻¹ x - x ∈ ℝ ∙ v₀ := by
  have h' := acdn_map_mem_span (acdn_inv_apply_self hfix) h
  rw [map_sub, acdn_inv_apply_apply] at h'
  have e : A⁻¹ x - x = -(x - A⁻¹ x) := by abel
  rw [e]
  exact neg_mem h'

/-- **The commutator `[A, X]` of a shear `X` with `A` fixing `v₀` is a shear.** -/
theorem acdn_shear_commutator {A X : Minkowski d ≃ₗ[ℝ] Minkowski d} (hA : A ∈ lorentz d)
    (hAf : A v₀ = v₀) (hXf : X v₀ = v₀) (hXW : ∀ w, minkB v₀ w = 0 → X w - w ∈ ℝ ∙ v₀)
    {w : Minkowski d} (hw : minkB v₀ w = 0) :
    (A * X * A⁻¹ * X⁻¹) w - w ∈ ℝ ∙ v₀ := by
  have hu : minkB v₀ (A⁻¹ w) = 0 :=
    acdn_minkB_apply ((lorentz d).inv_mem hA) (acdn_inv_apply_self hAf) hw
  have e : (A * X * A⁻¹ * X⁻¹) w - w =
      A (X (A⁻¹ (X⁻¹ w - w))) + A (X (A⁻¹ w) - A⁻¹ w) := by
    simp only [LinearEquiv.mul_apply, map_sub, acdn_apply_inv_apply]
    abel
  rw [e]
  refine add_mem ?_ (acdn_map_mem_span hAf (hXW _ hu))
  refine acdn_map_mem_span hAf (acdn_map_mem_span hXf ?_)
  exact acdn_map_mem_span (acdn_inv_apply_self hAf) (acdn_shear_inv hXf hXW hw)

/-- **The recursion** `m_{[A,X]} ≡ (A − 1) m_X` modulo `ℝ v₀`, `m_Z = Z⁻¹ n − n`. -/
theorem acdn_m_commutator {n : Minkowski d} {A X : Minkowski d ≃ₗ[ℝ] Minkowski d}
    (hA : A ∈ lorentz d) (hAf : A v₀ = v₀) (hX : X ∈ lorentz d) (hXf : X v₀ = v₀)
    (hXW : ∀ w, minkB v₀ w = 0 → X w - w ∈ ℝ ∙ v₀) :
    ((A * X * A⁻¹ * X⁻¹)⁻¹ n - n) - (A (X⁻¹ n - n) - (X⁻¹ n - n)) ∈ ℝ ∙ v₀ := by
  have hmA : minkB v₀ (A⁻¹ n - n) = 0 := acdn_minkB_m hA hAf
  have hmX : minkB v₀ (X⁻¹ n - n) = 0 := acdn_minkB_m hX hXf
  have e : ((A * X * A⁻¹ * X⁻¹)⁻¹ n - n) - (A (X⁻¹ n - n) - (X⁻¹ n - n)) =
      X (A (X⁻¹ (A⁻¹ n - n) - (A⁻¹ n - n))) + (X (A (X⁻¹ n - n)) - A (X⁻¹ n - n)) -
        (X (X⁻¹ n - n) - (X⁻¹ n - n)) := by
    simp only [mul_inv_rev, inv_inv, LinearEquiv.mul_apply, map_sub, acdn_apply_inv_apply]
    abel
  rw [e]
  refine sub_mem (add_mem ?_ (hXW _ (acdn_minkB_apply hA hAf hmX))) (hXW _ hmX)
  exact acdn_map_mem_span hXf (acdn_map_mem_span hAf (acdn_shear_inv hXf hXW hmA))

/-- **Semisimplicity on `v₀^⊥ / ℝ v₀`**: if `y ∈ v₀^⊥` and `(A − 1)² y ∈ ℝ v₀`, then
`(A − 1) y ∈ ℝ v₀` (`x = (A − 1) y` is null, since `A⁻¹ x ≡ x`). -/
theorem acdn_semisimple (hv0 : v₀ ≠ 0) (hv : minkQ v₀ = 0) {A : Minkowski d ≃ₗ[ℝ] Minkowski d}
    (hA : A ∈ lorentz d) (hAf : A v₀ = v₀) {y : Minkowski d} (hy : minkB v₀ y = 0)
    (h : A (A y - y) - (A y - y) ∈ ℝ ∙ v₀) : A y - y ∈ ℝ ∙ v₀ := by
  set x := A y - y with hxdef
  have hxW : minkB v₀ x = 0 := by
    rw [hxdef, minkB_sub_right, acdn_minkB_apply hA hAf hy, hy, sub_zero]
  obtain ⟨t, ht⟩ := mem_span_singleton.1 h
  have hAi : A⁻¹ x = x - t • v₀ := by
    have e1 : A x = x + t • v₀ := by rw [ht]; abel
    have e2 : x = A⁻¹ x + t • v₀ := by
      conv_lhs => rw [← acdn_inv_apply_apply A x]
      rw [e1, map_add, map_smul, acdn_inv_apply_self hAf]
    exact eq_sub_of_add_eq e2.symm
  have hq : minkQ x = 0 := by
    have h1 : minkB x (A y) = minkB x y := by
      rw [minkB_comm, acdn_minkB_apply_left hA, minkB_comm, hAi, minkB_sub_left,
        minkB_smul_left, hy, mul_zero, sub_zero]
    rw [minkQ_eq_minkB]
    conv_lhs => rw [show x = A y - y from rfl]
    rw [minkB_sub_right, ← hxdef, h1, sub_self]
  exact acdn_mem_span_of_null hv0 hv hxW hq

/-- `minkB m (X z) = minkB m z` on `v₀^⊥` when `X⁻¹ m ≡ m` modulo `ℝ v₀`. -/
theorem acdn_minkB_apply_right_of {X : Minkowski d ≃ₗ[ℝ] Minkowski d} (hX : X ∈ lorentz d)
    {m z : Minkowski d} (hm : X⁻¹ m - m ∈ ℝ ∙ v₀) (hz : minkB v₀ z = 0) :
    minkB m (X z) = minkB m z := by
  obtain ⟨t, ht⟩ := mem_span_singleton.1 hm
  have e : X⁻¹ m = m + t • v₀ := by rw [ht]; abel
  have h := minkB_map (lorentz.minkQ_apply ((lorentz d).inv_mem hX)) m (X z)
  rw [acdn_inv_apply_apply, e, minkB_add_left, minkB_smul_left, hz, mul_zero, add_zero] at h
  exact h.symm

end ZeroStep

section ZeroStepMain

variable {v₀ : Minkowski d}

/-- **The Engel step on a shear**: if `X` fixes `v₀`, moves `v₀^⊥` along `ℝ v₀`, and
`[a, [a, …, [a, X]]] = 1`, then `a m_X ≡ m_X` modulo `ℝ v₀` (`m_X = X⁻¹ n − n`): by induction,
`m_{[a,X]} ≡ (a − 1) m_X`, then semisimplicity. -/
theorem acdn_engel_shear (hv0 : v₀ ≠ 0) (hv : minkQ v₀ = 0) {n : Minkowski d}
    {a : lorentz d} (haf : (a : Minkowski d ≃ₗ[ℝ] Minkowski d) v₀ = v₀) :
    ∀ (k : ℕ) (X : lorentz d), (X : Minkowski d ≃ₗ[ℝ] Minkowski d) v₀ = v₀ →
      (∀ w, minkB v₀ w = 0 → (X : Minkowski d ≃ₗ[ℝ] Minkowski d) w - w ∈ ℝ ∙ v₀) →
      (fun x => a * x * a⁻¹ * x⁻¹)^[k] X = 1 →
      (a : Minkowski d ≃ₗ[ℝ] Minkowski d) ((X : Minkowski d ≃ₗ[ℝ] Minkowski d)⁻¹ n - n) -
        ((X : Minkowski d ≃ₗ[ℝ] Minkowski d)⁻¹ n - n) ∈ ℝ ∙ v₀ := by
  intro k
  induction k with
  | zero =>
    intro X _ _ hX
    rw [iterate_zero_apply] at hX
    subst hX
    simp
  | succ k ih =>
    intro X hXf hXW hX
    rw [iterate_succ_apply] at hX
    set Y : lorentz d := a * X * a⁻¹ * X⁻¹ with hYdef
    have hYc : (Y : Minkowski d ≃ₗ[ℝ] Minkowski d) = (a : Minkowski d ≃ₗ[ℝ] Minkowski d) *
        X * (a : Minkowski d ≃ₗ[ℝ] Minkowski d)⁻¹ * (X : Minkowski d ≃ₗ[ℝ] Minkowski d)⁻¹ := by
      simp [hYdef]
    have hYf : (Y : Minkowski d ≃ₗ[ℝ] Minkowski d) v₀ = v₀ := by
      rw [hYc]
      simp only [LinearEquiv.mul_apply, acdn_inv_apply_self hXf, acdn_inv_apply_self haf, hXf,
        haf]
    have hYW : ∀ w, minkB v₀ w = 0 → (Y : Minkowski d ≃ₗ[ℝ] Minkowski d) w - w ∈ ℝ ∙ v₀ := by
      intro w hw
      rw [hYc]
      exact acdn_shear_commutator a.2 haf hXf hXW hw
    have ihY := ih Y hYf hYW hX
    have hrec := acdn_m_commutator (n := n) a.2 haf X.2 hXf hXW
    rw [← hYc] at hrec
    set mX := (X : Minkowski d ≃ₗ[ℝ] Minkowski d)⁻¹ n - n with hmXdef
    set mY := (Y : Minkowski d ≃ₗ[ℝ] Minkowski d)⁻¹ n - n with hmYdef
    have hmXW : minkB v₀ mX = 0 := acdn_minkB_m X.2 hXf
    refine acdn_semisimple hv0 hv a.2 haf hmXW ?_
    set x := (a : Minkowski d ≃ₗ[ℝ] Minkowski d) mX - mX with hxdef
    have e : (a : Minkowski d ≃ₗ[ℝ] Minkowski d) x - x =
        ((a : Minkowski d ≃ₗ[ℝ] Minkowski d) mY - mY) -
          ((a : Minkowski d ≃ₗ[ℝ] Minkowski d) (mY - x) - (mY - x)) := by
      rw [map_sub (a : Minkowski d ≃ₗ[ℝ] Minkowski d) mY x]; abel
    rw [e]
    exact sub_mem ihY (sub_mem (acdn_map_mem_span haf hrec) hrec)

/-- **The `z = 0` step**: if `a`, `b` fix the nonzero null `v₀`, their commutator `C` has
trivial rotation part, and `[a, [a, …, C]] = 1 = [b, [b, …, C]]`, then `C = 1`. -/
theorem eq_one_of_commutator_null (hv0 : v₀ ≠ 0) (hv : minkQ v₀ = 0)
    {a b : lorentz d} (ha : (a : Minkowski d ≃ₗ[ℝ] Minkowski d) v₀ = v₀)
    (hb : (b : Minkowski d ≃ₗ[ℝ] Minkowski d) v₀ = v₀)
    (hc : screenRot v₀ ((a * b * a⁻¹ * b⁻¹ : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) = 1)
    (hea : ∃ n : ℕ, (fun x => a * x * a⁻¹ * x⁻¹)^[n] (a * b * a⁻¹ * b⁻¹) = 1)
    (heb : ∃ n : ℕ, (fun x => b * x * b⁻¹ * x⁻¹)^[n] (a * b * a⁻¹ * b⁻¹) = 1) :
    a * b * a⁻¹ * b⁻¹ = 1 := by
  set n : Minkowski d := (minkB v₀ (timeUnit d))⁻¹ • timeUnit d with hndef
  have hn : minkB v₀ n = 1 := by
    rw [hndef, minkB_smul_right, minkB_comm]
    exact inv_mul_cancel₀ (minkB_timeUnit_ne_zero hv0 hv)
  set A : Minkowski d ≃ₗ[ℝ] Minkowski d := ↑a with hAdef
  set B : Minkowski d ≃ₗ[ℝ] Minkowski d := ↑b with hBdef
  have hAL : A ∈ lorentz d := a.2
  have hBL : B ∈ lorentz d := b.2
  set C : lorentz d := a * b * a⁻¹ * b⁻¹ with hCdef
  have hCc : (C : Minkowski d ≃ₗ[ℝ] Minkowski d) = A * B * A⁻¹ * B⁻¹ := by simp [hCdef, A, B]
  have hCf : (C : Minkowski d ≃ₗ[ℝ] Minkowski d) v₀ = v₀ := by
    rw [hCc]
    simp only [LinearEquiv.mul_apply, acdn_inv_apply_self hb, acdn_inv_apply_self ha, ha, hb]
  have hCW := sub_mem_span_of_screenRot_eq_one hv0 hv C.2 hCf hc
  obtain ⟨ka, hka⟩ := hea
  obtain ⟨kb, hkb⟩ := heb
  have hma := acdn_engel_shear hv0 hv (n := n) ha ka C hCf hCW hka
  have hmb := acdn_engel_shear hv0 hv (n := n) hb kb C hCf hCW hkb
  set m := (C : Minkowski d ≃ₗ[ℝ] Minkowski d)⁻¹ n - n with hmdef
  have hmW : minkB v₀ m = 0 := acdn_minkB_m C.2 hCf
  set ma := A⁻¹ n - n with hmadef
  set mb := B⁻¹ n - n with hmbdef
  have hmaW : minkB v₀ ma = 0 := acdn_minkB_m hAL ha
  have hmbW : minkB v₀ mb = 0 := acdn_minkB_m hBL hb
  have hdecomp : m = B (A mb - mb) + B (A (B⁻¹ ma - ma)) := by
    rw [hmdef, hCc, hmadef, hmbdef]
    simp only [mul_inv_rev, inv_inv, LinearEquiv.mul_apply, map_sub, acdn_apply_inv_apply]
    abel
  have hai : A⁻¹ m - m ∈ ℝ ∙ v₀ := acdn_inv_sub_mem ha hma
  have hbi : B⁻¹ m - m ∈ ℝ ∙ v₀ := acdn_inv_sub_mem hb hmb
  have hbb : B⁻¹⁻¹ m - m ∈ ℝ ∙ v₀ := by rw [inv_inv]; exact hmb
  have hz1 : minkB v₀ (A mb - mb) = 0 := by
    rw [minkB_sub_right, acdn_minkB_apply hAL ha hmbW, hmbW, sub_zero]
  have hBi : B⁻¹ ∈ lorentz d := (lorentz d).inv_mem hBL
  have hz2 : minkB v₀ (B⁻¹ ma - ma) = 0 := by
    rw [minkB_sub_right, acdn_minkB_apply hBi (acdn_inv_apply_self hb) hmaW, hmaW, sub_zero]
  have hz2' : minkB v₀ (A (B⁻¹ ma - ma)) = 0 := acdn_minkB_apply hAL ha hz2
  have hq : minkQ m = 0 := by
    rw [minkQ_eq_minkB]
    nth_rewrite 2 [hdecomp]
    rw [minkB_add_right, acdn_minkB_apply_right_of hBL hbi hz1,
      acdn_minkB_apply_right_of hBL hbi hz2', acdn_minkB_apply_right_of hAL hai hz2,
      minkB_sub_right m (A mb) mb, minkB_sub_right m (B⁻¹ ma) ma,
      acdn_minkB_apply_right_of hAL hai hmbW,
      acdn_minkB_apply_right_of hBi hbb hmaW]
    ring
  obtain ⟨s, hs⟩ := mem_span_singleton.1 (acdn_mem_span_of_null hv0 hv hmW hq)
  have hCi : (C : Minkowski d ≃ₗ[ℝ] Minkowski d)⁻¹ ∈ lorentz d := (lorentz d).inv_mem C.2
  have hs0 : s = 0 := by
    have hQ := lorentz.minkQ_apply hCi n
    have e : (C : Minkowski d ≃ₗ[ℝ] Minkowski d)⁻¹ n = n + s • v₀ := by
      rw [hs, hmdef]; abel
    rw [e, minkQ_add, minkQ_smul s v₀, hv, minkB_smul_right, minkB_comm n v₀, hn] at hQ
    linarith
  have hm0 : m = 0 := by rw [← hs, hs0, zero_smul]
  have hCn : (C : Minkowski d ≃ₗ[ℝ] Minkowski d) n = n := by
    have h1 : (C : Minkowski d ≃ₗ[ℝ] Minkowski d)⁻¹ n = n := sub_eq_zero.1 hm0
    calc (C : Minkowski d ≃ₗ[ℝ] Minkowski d) n =
        (C : Minkowski d ≃ₗ[ℝ] Minkowski d) ((C : Minkowski d ≃ₗ[ℝ] Minkowski d)⁻¹ n) := by
          rw [h1]
      _ = n := acdn_apply_inv_apply _ _
  have hCu : ∀ u, minkB v₀ u = 0 → (C : Minkowski d ≃ₗ[ℝ] Minkowski d) u = u := by
    intro u hu
    have h := acdn_shear_apply hn C.2 hCW hu
    rw [← hmdef, hm0, minkB_zero_right, zero_smul] at h
    exact sub_eq_zero.1 h
  refine Subtype.ext (LinearEquiv.ext fun x => ?_)
  have hxW : minkB v₀ (x - minkB v₀ x • n) = 0 := by
    rw [minkB_sub_right, minkB_smul_right, hn, mul_one, sub_self]
  have e : x = (x - minkB v₀ x • n) + minkB v₀ x • n := by abel
  show (C : Minkowski d ≃ₗ[ℝ] Minkowski d) x = x
  conv_lhs => rw [e]
  rw [map_add, map_smul, hCu _ hxW, hCn, ← e]

end ZeroStepMain

/-! ### The null case -/

/-- Iterated commutators commute with group homomorphisms. -/
theorem acdn_map_iterate_commutator {G H : Type*} [Group G] [Group H] (f : G →* H) (a : G)
    (k : ℕ) : ∀ b : G, f ((fun x => a * x * a⁻¹ * x⁻¹)^[k] b) =
      (fun x => f a * x * (f a)⁻¹ * x⁻¹)^[k] (f b) := by
  induction k with
  | zero => intro b; rfl
  | succ k ih =>
    intro b
    rw [iterate_succ_apply, iterate_succ_apply, ih]
    simp only [map_mul, map_inv]

/-- `SO₀(1, d)` inside `Isom(𝐌ⁿ)`, with zero translation part (`Nonlox.nfIsom`). -/
noncomputable def acdnLorentzToIsom : lorentz d →* isom d where
  toFun A := Nonlox.nfIsom A A.2
  map_one' := Subtype.ext (AffineEquiv.ext fun _ => rfl)
  map_mul' _ _ := Subtype.ext (AffineEquiv.ext fun _ => rfl)

theorem linOf_acdnLorentzToIsom (A : lorentz d) :
    linOf (acdnLorentzToIsom A) = (A : Minkowski d ≃ₗ[ℝ] Minkowski d) := rfl

/-- **Step 2, null case**: near-identity elements (in rotation part) of a nilpotent subgroup of
`SO₀(1, d)` fixing a nonzero null vector commute. -/
theorem commute_of_isNilpotent_of_fixNull {N : Subgroup (lorentz d)} (hN : Group.IsNilpotent N)
    {v₀ : Minkowski d} (hv0 : v₀ ≠ 0) (hv : minkQ v₀ = 0)
    (hfix : ∀ A ∈ N, (A : Minkowski d ≃ₗ[ℝ] Minkowski d) v₀ = v₀) {a b : lorentz d}
    (ha : a ∈ N) (hb : b ∈ N)
    (haε : ‖screenRot v₀ (a : Minkowski d ≃ₗ[ℝ] Minkowski d) - 1‖ < 1 / 2)
    (hbε : ‖screenRot v₀ (b : Minkowski d ≃ₗ[ℝ] Minkowski d) - 1‖ < 1 / 2) :
    a * b = b * a := by
  set ψ : N →* isom d := acdnLorentzToIsom.comp N.subtype with hψdef
  set a' : N := ⟨a, ha⟩
  set b' : N := ⟨b, hb⟩
  have hstab : ∀ A ∈ N, linOf (acdnLorentzToIsom A) ∈ nullStab v₀ := fun A hA =>
    ⟨A.2, hfix A hA⟩
  -- Frobenius backwards along `[a, [a, …, [a, b]]] = 1`: the rotation parts commute
  obtain ⟨k, hk⟩ := exists_iterate_commutator_eq_one_of_isNilpotent a' b'
  have hk' : (fun x => ψ a' * x * (ψ a')⁻¹ * x⁻¹)^[k] (ψ b') = 1 := by
    rw [← acdn_map_iterate_commutator, hk, map_one]
  have hcomm := commute_screenRot_of_iterate_eq_one hv0 hv (hstab a ha) haε.le k (ψ b')
    (hstab b hb) hbε hk'
  -- hence `ρ([a, b]) = 1`
  have hc : screenRot v₀ ((a * b * a⁻¹ * b⁻¹ : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) =
      1 := by
    set A' : nullStab v₀ := ⟨a, a.2, hfix a ha⟩
    set B' : nullStab v₀ := ⟨b, b.2, hfix b hb⟩
    have e : ((a * b * a⁻¹ * b⁻¹ : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) =
        ((A' * B' * A'⁻¹ * B'⁻¹ : nullStab v₀) : Minkowski d ≃ₗ[ℝ] Minkowski d) := by
      simp [A', B']
    rw [e, ← screenRotHom_apply hv0 hv]
    set ρu := (screenRotHom hv0 hv).toHomUnits
    have hc' : Commute (ρu A') (ρu B') := Units.ext hcomm.eq
    have h1 : ρu (A' * B' * A'⁻¹ * B'⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hc'.eq]
      group
    have h2 := congrArg Units.val h1
    rw [Units.val_one] at h2
    exact h2
  -- the Engel conditions on `C = [a, b]`, and the `z = 0` step
  set C' : N := a' * b' * a'⁻¹ * b'⁻¹
  have hC : N.subtype C' = a * b * a⁻¹ * b⁻¹ := by simp [C', a', b']
  obtain ⟨ka, hka⟩ := exists_iterate_commutator_eq_one_of_isNilpotent a' C'
  obtain ⟨kb, hkb⟩ := exists_iterate_commutator_eq_one_of_isNilpotent b' C'
  have hea : (fun x => a * x * a⁻¹ * x⁻¹)^[ka] (a * b * a⁻¹ * b⁻¹) = 1 := by
    have h := acdn_map_iterate_commutator N.subtype a' ka C'
    rw [hka, map_one, hC] at h
    exact h.symm
  have heb : (fun x => b * x * b⁻¹ * x⁻¹)^[kb] (a * b * a⁻¹ * b⁻¹) = 1 := by
    have h := acdn_map_iterate_commutator N.subtype b' kb C'
    rw [hkb, map_one, hC] at h
    exact h.symm
  have h := eq_one_of_commutator_null hv0 hv (hfix a ha) (hfix b hb) hc ⟨ka, hea⟩ ⟨kb, heb⟩
  rw [← commutatorElement_def] at h
  exact commutatorElement_eq_one_iff_mul_comm.1 h

/-! ### The timelike case: one dimension up -/

section Shift

noncomputable def acdnSplit : Minkowski (d + 1) ≃ₗ[ℝ] Minkowski d × ℝ where
  toFun p := ((p.1, WithLp.toLp 2 fun i => p.2 (Fin.castSucc i)), p.2 (Fin.last d))
  map_add' p q := by
    refine Prod.ext (Prod.ext rfl ?_) rfl
    ext i; simp
  map_smul' c p := by
    refine Prod.ext (Prod.ext rfl ?_) rfl
    ext i; simp
  invFun q := (q.1.1, WithLp.toLp 2 (Fin.snoc (α := fun _ => ℝ) (fun i => q.1.2 i) q.2))
  left_inv p := by
    refine Prod.ext rfl ?_
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  right_inv q := by
    refine Prod.ext (Prod.ext rfl ?_) ?_
    · ext i; simp
    · simp

theorem acdnSplit_apply (p : Minkowski (d + 1)) : acdnSplit p =
    ((p.1, WithLp.toLp 2 fun i => p.2 (Fin.castSucc i)), p.2 (Fin.last d)) := rfl

theorem acdnSplit_symm_apply (q : Minkowski d × ℝ) : acdnSplit.symm q =
    (q.1.1, WithLp.toLp 2 (Fin.snoc (α := fun _ => ℝ) (fun i => q.1.2 i) q.2)) := rfl

theorem acdn_norm_sq_snoc (y : EuclideanSpace ℝ (Fin d)) (s : ℝ) :
    ‖(WithLp.toLp 2 (Fin.snoc (α := fun _ => ℝ) (fun i => y i) s) : EuclideanSpace ℝ (Fin (d + 1)))‖ ^ 2 =
      ‖y‖ ^ 2 + s ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc]
  simp

theorem minkQ_acdnSplit_symm (q : Minkowski d × ℝ) :
    minkQ (acdnSplit.symm q) = minkQ q.1 + q.2 ^ 2 := by
  rw [acdnSplit_symm_apply, minkQ, minkQ]
  simp only
  rw [acdn_norm_sq_snoc]; ring


theorem acdn_norm_split_symm_zero (r : Minkowski d) : ‖acdnSplit.symm (r, (0 : ℝ))‖ = ‖r‖ := by
  rw [acdnSplit_symm_apply, Prod.norm_def, Prod.norm_def]
  congr 1
  have h := acdn_norm_sq_snoc r.2 0
  rw [zero_pow two_ne_zero, add_zero] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

theorem acdn_norm_split_fst_le (p : Minkowski (d + 1)) : ‖(acdnSplit p).1‖ ≤ ‖p‖ := by
  have h := congrArg (fun q : Minkowski (d + 1) => ‖q.2‖ ^ 2) (acdnSplit.symm_apply_apply p)
  rw [acdnSplit_symm_apply, acdn_norm_sq_snoc] at h
  have h2 : ‖(acdnSplit p).1.2‖ ≤ ‖p.2‖ := by
    have : ‖(acdnSplit p).1.2‖ ^ 2 ≤ ‖p.2‖ ^ 2 := by rw [← h]; nlinarith [sq_nonneg (acdnSplit p).2]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this
  rw [Prod.norm_def, Prod.norm_def]
  exact max_le_max (le_of_eq rfl) h2

/-- `A ⊕ id` on `Minkowski (d + 1) = Minkowski d ⊕ ℝ e_last`. -/
noncomputable def acdnLift (A : Minkowski d ≃ₗ[ℝ] Minkowski d) :
    Minkowski (d + 1) ≃ₗ[ℝ] Minkowski (d + 1) :=
  acdnSplit.trans ((A.prodCongr (LinearEquiv.refl ℝ ℝ)).trans acdnSplit.symm)

theorem acdnLift_apply (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (p : Minkowski (d + 1)) :
    acdnLift A p = acdnSplit.symm (A (acdnSplit p).1, (acdnSplit p).2) := rfl

theorem acdnLift_mem {A : Minkowski d ≃ₗ[ℝ] Minkowski d} (hA : A ∈ lorentz d) :
    acdnLift A ∈ lorentz (d + 1) := by
  refine mem_lorentz_of (fun p => ?_) ?_ ?_
  · rw [acdnLift_apply, minkQ_acdnSplit_symm]
    simp only
    rw [lorentz.minkQ_apply hA]
    conv_rhs => rw [← acdnSplit.symm_apply_apply p]
    rw [minkQ_acdnSplit_symm]
  · have h1 : (acdnSplit (timeUnit (d + 1))).1 = timeUnit d := by
      refine Prod.ext rfl ?_
      ext i; simp [acdnSplit_apply, timeUnit]
    show 0 < (A (acdnSplit (timeUnit (d + 1))).1).1
    rw [h1]
    exact (lorentz.isFutureTimelike_apply hA (v := timeUnit d)
      ⟨by simp [timeUnit], by rw [minkQ_timeUnit]; norm_num⟩).1
  · have e : (acdnLift A : Minkowski (d + 1) →ₗ[ℝ] Minkowski (d + 1)) =
        ((acdnSplit (d := d)).symm : Minkowski d × ℝ →ₗ[ℝ] Minkowski (d + 1)) ∘ₗ
          (LinearMap.prodMap (A : Minkowski d →ₗ[ℝ] Minkowski d) LinearMap.id) ∘ₗ
            ((acdnSplit (d := d)).symm.symm : Minkowski (d + 1) →ₗ[ℝ] Minkowski d × ℝ) := by
      ext p <;> rfl
    rw [e, LinearMap.det_conj, LinearMap.det_prodMap, lorentz.det_eq_one hA, LinearMap.det_id,
      one_mul]

theorem acdnLift_mul (A B : Minkowski d ≃ₗ[ℝ] Minkowski d) :
    acdnLift (A * B) = acdnLift A * acdnLift B :=
  LinearEquiv.ext fun p => by
    simp only [LinearEquiv.mul_apply, acdnLift_apply, LinearEquiv.apply_symm_apply]

theorem acdnLift_one : acdnLift (1 : Minkowski d ≃ₗ[ℝ] Minkowski d) = 1 :=
  LinearEquiv.ext fun p => by
    rw [acdnLift_apply]
    exact acdnSplit.symm_apply_apply p

theorem acdnLift_injective : Function.Injective (acdnLift (d := d)) := fun A B h =>
  LinearEquiv.ext fun x => by
    have h1 := congrArg (fun L : Minkowski (d + 1) ≃ₗ[ℝ] Minkowski (d + 1) =>
      acdnSplit (L (acdnSplit.symm (x, (0 : ℝ))))) h
    simp only [acdnLift_apply, LinearEquiv.apply_symm_apply] at h1
    exact congrArg Prod.fst h1

theorem acdn_norm_lift_sub_one_le (A : Minkowski d ≃ₗ[ℝ] Minkowski d) :
    ‖linToCLM (acdnLift A) - 1‖ ≤ ‖linToCLM A - 1‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun p => ?_
  have e : (linToCLM (acdnLift A) - 1) p =
      acdnSplit.symm ((linToCLM A - 1) (acdnSplit p).1, (0 : ℝ)) := by
    change acdnLift A p - p = acdnSplit.symm (A (acdnSplit p).1 - (acdnSplit p).1, (0 : ℝ))
    conv_lhs => rw [← acdnSplit.symm_apply_apply p]
    rw [acdnLift_apply, LinearEquiv.apply_symm_apply, ← map_sub, Prod.mk_sub_mk, sub_self]
  rw [e, acdn_norm_split_symm_zero]
  calc ‖(linToCLM A - 1) (acdnSplit p).1‖ ≤ ‖linToCLM A - 1‖ * ‖(acdnSplit p).1‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖linToCLM A - 1‖ * ‖p‖ :=
        mul_le_mul_of_nonneg_left (acdn_norm_split_fst_le p) (norm_nonneg _)

/-- The extension `A ↦ A ⊕ id` as a homomorphism `SO₀(1, d) → SO₀(1, d + 1)`. -/
noncomputable def acdnLiftHom : lorentz d →* lorentz (d + 1) where
  toFun A := ⟨acdnLift (A : Minkowski d ≃ₗ[ℝ] Minkowski d), acdnLift_mem A.2⟩
  map_one' := Subtype.ext (by
    show acdnLift (1 : Minkowski d ≃ₗ[ℝ] Minkowski d) = 1
    exact acdnLift_one)
  map_mul' A B := Subtype.ext (by
    show acdnLift ((A : Minkowski d ≃ₗ[ℝ] Minkowski d) * (B : Minkowski d ≃ₗ[ℝ] Minkowski d)) =
      acdnLift (A : Minkowski d ≃ₗ[ℝ] Minkowski d) * acdnLift (B : Minkowski d ≃ₗ[ℝ] Minkowski d)
    exact acdnLift_mul _ _)

theorem acdnLiftHom_injective : Function.Injective (acdnLiftHom (d := d)) := fun _ _ h =>
  Subtype.ext (acdnLift_injective (congrArg Subtype.val h))

end Shift

/-- **Step 2, timelike case**: near-identity elements of a nilpotent subgroup of `SO₀(1, d)`
fixing a timelike vector commute. -/
theorem commute_of_isNilpotent_of_fixTimelike {N : Subgroup (lorentz d)}
    (hN : Group.IsNilpotent N) {w : Minkowski d} (hw : minkQ w < 0)
    (hfix : ∀ A ∈ N, (A : Minkowski d ≃ₗ[ℝ] Minkowski d) w = w) {a b : lorentz d}
    (ha : a ∈ N) (hb : b ∈ N)
    (haε : ‖linToCLM (a : Minkowski d ≃ₗ[ℝ] Minkowski d) - 1‖ < 1 / 2)
    (hbε : ‖linToCLM (b : Minkowski d ≃ₗ[ℝ] Minkowski d) - 1‖ < 1 / 2) :
    a * b = b * a := by
  set E : lorentz d →* lorentz (d + 1) := acdnLiftHom with hEdef
  set c : ℝ := Real.sqrt (-minkQ w) with hcdef
  have hc0 : 0 < c := Real.sqrt_pos.2 (neg_pos.2 hw)
  set v : Minkowski (d + 1) := acdnSplit.symm (w, c) with hvdef
  have hvq : minkQ v = 0 := by
    rw [hvdef, minkQ_acdnSplit_symm]
    simp only
    rw [hcdef, Real.sq_sqrt (neg_nonneg.2 hw.le)]
    ring
  have hv0 : v ≠ 0 := by
    intro h
    have h1 := congrArg (fun p => (acdnSplit p).2) h
    simp only [hvdef, LinearEquiv.apply_symm_apply, map_zero, Prod.snd_zero] at h1
    exact hc0.ne' h1
  have hfixE : ∀ A ∈ N.map E, (A : Minkowski (d + 1) ≃ₗ[ℝ] Minkowski (d + 1)) v = v := by
    rintro _ ⟨A, hA, rfl⟩
    show acdnLift (A : Minkowski d ≃ₗ[ℝ] Minkowski d) v = v
    rw [hvdef, acdnLift_apply, LinearEquiv.apply_symm_apply]
    simp only
    rw [hfix A hA]
  have hNE : Group.IsNilpotent (N.map E) :=
    Group.nilpotent_of_surjective (E.subgroupMap N) (E.subgroupMap_surjective N)
  have hρ : ∀ x : lorentz d, ‖linToCLM (x : Minkowski d ≃ₗ[ℝ] Minkowski d) - 1‖ < 1 / 2 →
      ‖screenRot v ((E x : lorentz (d + 1)) : Minkowski (d + 1) ≃ₗ[ℝ] Minkowski (d + 1)) - 1‖ <
        1 / 2 := fun x hx =>
    (norm_screenRot_sub_one_le hv0 hvq _).trans_lt ((acdn_norm_lift_sub_one_le _).trans_lt hx)
  have h := commute_of_isNilpotent_of_fixNull hNE hv0 hvq hfixE (Subgroup.mem_map_of_mem E ha)
    (Subgroup.mem_map_of_mem E hb) (hρ a haε) (hρ b hbε)
  rw [← map_mul, ← map_mul] at h
  exact acdnLiftHom_injective h

/-- **Step 2 without loxodromic elements**: for a nilpotent `N ≤ SO₀(1, d)` fixing a timelike or a
nonzero null vector, elements `1/2`-close to `1` commute. -/
theorem commute_of_isNilpotent_of_fixesTimelikeOrNull {N : Subgroup (lorentz d)}
    (hN : Group.IsNilpotent N) (hF : FixesTimelikeOrNull N) {a b : lorentz d} (ha : a ∈ N)
    (hb : b ∈ N) (haε : ‖linToCLM (a : Minkowski d ≃ₗ[ℝ] Minkowski d) - 1‖ < 1 / 2)
    (hbε : ‖linToCLM (b : Minkowski d ≃ₗ[ℝ] Minkowski d) - 1‖ < 1 / 2) :
    a * b = b * a := by
  rcases hF with ⟨w, hw, hfix⟩ | ⟨v, hv0, hv, hfix⟩
  · exact commute_of_isNilpotent_of_fixTimelike hN hw hfix ha hb haε hbε
  · exact commute_of_isNilpotent_of_fixNull hN hv0 hv hfix ha hb
      ((norm_screenRot_sub_one_le hv0 hv _).trans_lt haε)
      ((norm_screenRot_sub_one_le hv0 hv _).trans_lt hbε)

end Causal.Flat
