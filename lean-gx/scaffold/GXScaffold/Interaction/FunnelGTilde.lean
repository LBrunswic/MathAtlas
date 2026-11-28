import GX.BBS.RP1Circles
import GX.BBS.GTilde

/-!
# Lemma F's `G̃` half: the rotation lifts, (S), (S′), and (F1)–(F4) from the relation (N)

Research target `T-3p1-funnel-gtilde` (`roadmap/roadmap.toml`): `papers/bbs/NOTES-3+1.md`, N9 §1,
§2 and §4 (`NOTES-3+1.md:738–760`, `:788–803`, `:873–890`). No ledger label. Pseudo-labels below,
**none marked**: the master records research results, and (F1)–(F4) rest on the relation (N),
carried as a hypothesis (`GX.RelationN`) as the dispatch rules. `l.` without a file is
`papers/bbs/legacy/labeled/colI_v1.tex`; `N9 l.` is `NOTES-3+1.md`. 0 `sorry`.

* `N9:R` — `NOTES-3+1.md:795–797` — the rotation lifts `R̃_c(φ)`: `GX.GTilde.rot` (the lift of
  `φ ↦ rot(φ/2) ∈ SL(2,ℝ)` from `1`, `R̃(φ) t = t + φ/2π`), `GX.GTilde.rot_add`,
  `GX.GTilde.rot_two_pi` (`R̃(2π) = δ`), `GX.GTilde.eq_conj_rot_of_lift` (the lift of a conjugated
  one-parameter rotation group is the conjugate), `GX.GTilde.IsRotLift` (`R̃_c(φ)`, any `c`);
  `GX.GTilde.tau_rot`, `GX.GTilde.angle_rot` (`angle R̃(φ) = φ`).
* `N9:S` — `NOTES-3+1.md:798` — `GX.GTilde.rot_S`, `GX.GTilde.IsRotLift.S`; sharp:
  `GX.GTilde.rot_S_iff`. Conjugation (`:802`): `GX.GTilde.lt_conj_apply`,
  `GX.GTilde.conj_apply_lt_delta`.
* `N9:S'` — `NOTES-3+1.md:799` — `GX.GTilde.apply_lt_delta_of_fixed`; the mirror bound
  `GX.GTilde.sub_one_lt_apply_of_fixed`.
* `N9:F1` — `NOTES-3+1.md:749` — `GX.funnel_F1`, `GX.funnel_F1_circle`; the `G̃` lemma
  `GX.funnel_F1_of_forall_lt`; positivity is needed: `GX.funnel_F1_needs_positivity`.
* `N9:F2` — `NOTES-3+1.md:750` — `GX.funnel_F2`, `GX.funnel_F2_circle`: degree `0`, and only `0`
  (`GX.GTilde.HasDegree`), `τ = 0`. The funnel sentence is not stated (out of scope).
* `N9:F3` — `NOTES-3+1.md:753` — `GX.funnel_F3`, `GX.funnel_F3_circle`: degree `0`, hence
  positive (`GX.GTilde.IsParabolic.le_apply`, through `GX.PSL2.IsParabolic.eq_of_smul_eq`: a
  parabolic element of `PSL(2,ℝ)` has one fixed point on `ℝP¹`).
* `N9:F4` — `NOTES-3+1.md:755` — `GX.funnel_F4_tau` (`0 < τ < 1`, normalisation-free),
  `GX.funnel_F4`, `GX.funnel_F4_circle` (`0 < Θ < 2π` with `GX.GTilde.angle`, OQ-113 (a)); in the
  wide reading of « elliptic » (OQ-113 (d), central holonomy included) `GX.funnel_F4_wide` needs
  `a ≥ 1`, and `GX.funnel_F4_wide_fails` is the counterexample at `a = 0` (a finding).
* The checks of (N) (`NOTES-3+1.md:864–866`): `GX.RelationN.eq_delta_of_zero`,
  `GX.relationN_one`, `GX.relationN_two_rot`.

> - **(F1)** if a ≥ 1, hol̃(C)·x < δx for every x ∈ ℝP̃¹;
> - **(F2)** if hol(C) is hyperbolic, C is a hyperbolic ℝP¹-circle **of degree 0** from the
>   hyperbolic side, and the end of H at C is a funnel: a neighbourhood of C in H ∪ C is isometric
>   to a neighbourhood of one end of ℍ²/⟨g⟩, g = hol(C);
> - **(F3)** if hol(C) is parabolic, C is a parabolic ℝP¹-circle of degree 0, hence positive
>   (l.754–756);
> - **(F4)** if hol(C) is elliptic, its angle satisfies 0 < Θ < 2π. (N9 l.749–755)
>
> - **R̃_c(φ)**, for c ∈ ℍ² and φ ∈ ℝ, is the lift of the rotation about c by angle φ along the
>   one-parameter rotation group. [...] Hence R̃_c(2π) = δ, and:
>   - **(S)** for 0 < φ < 2π, x < R̃_c(φ)x < δx for every x ∈ ℝP̃¹;
>   - **(S′)** an element g̃ ∈ G̃ with a fixed point satisfies g̃x < δx for every x.
>     (N9 l.795–799)
>
> **(N)  hol̃(C) = δ^{1−a} · P̃₁′ ⋯ P̃_a′,**
>
> with P̃_j′ a conjugate of R̃(θ_j) at a cone point, and of the parabolic lift with fixed points at
> a cusp. (N9 l.859–862)

## Hypothesis checklist

| N9 | here |
|---|---|
| `Σ`, `H`, `H̄` a disc, `C` its end | ⚠ read: they enter only through (N) and (eq>); `a`, the kinds and the `P̃_j′` are data |
| `p₁ … p_m` of angles `θ_j`, cusps `q₁ … q_n`, `a = m + n` | ✓ `s : Fin a → GX.SingKind` (`cone θ` or `cusp`), in the cyclic order of (N) |
| positivity `0 < θ_j < 2π` (l.1510–1511) | ⚠ weakened: `GX.SingKind.IsPositive` is l.1511's « less that 2π »; `0 < θ_j` is not used |
| `P̃_j′` a conjugate of `R̃(θ_j)`, or the parabolic lift with fixed points | ✓ `GX.SingKind.IsLift`; (F1) needs only `P̃_j′ y < δ y` (`GX.funnel_F1_of_forall_lt`), parabolicity at a cusp is not used |
| the relation (N) (N9 §3, Umlaufsatz) | ⚠ carried as a hypothesis `GX.RelationN` (dispatch) |
| `hol̃(C)`, from the hyperbolic side, for the generator of (eq>) | ✓ `GX.HasLiftedHolonomy L hol` (circle form); « from the hyperbolic side » SCOPE (b) |
| (eq>), `hol̃(C) x > x` on the developed image | ✓ `∃ x, x < hol x` (`G̃` form); from `GX.HasLiftedHolonomy.lt_apply` (circle form) |
| `a ≥ 1` in (F1) | ✓ carried; (F2), (F3) and (F4) hold for every `a` (at `a = 0`, `hol̃(C) = δ` is central); (F4) in the wide reading needs `a ≥ 1` |

## SCOPE (disclosed)

* **(a)** `R̃_c(φ)`. `GX.GTilde.rot φ` lifts `rot(φ/2) ∈ SL(2,ℝ)`, which turns the lines of `ℝ²` by
  `φ/2`, i.e. `ℝP¹ = P(ℝ²)` once around when `φ = 2π`. Through `PSL(2,ℝ) ≅ SO₀(1,2)` (`v ↦ v ⊗ v`)
  it is the hyperbolic rotation of angle `φ` about the point fixed by `SO(2)`: classical, not
  formalized, since `ℍ²` is not connected to `ℝP¹` here. A rotation about another point is a
  conjugate in `PSL(2,ℝ)`, and its lift along its one-parameter group is the conjugate
  `h R̃(φ) h⁻¹` (`GX.GTilde.eq_conj_rot_of_lift`); so `R̃_c(φ)` is `GX.GTilde.IsRotLift φ`.
  Positive `φ` moves `ℝP̃¹` to the right, as in N9 §2.
* **(b)** `L` is any `ℝP¹`-circle. « From the hyperbolic side » (l.1905) is not formalized: it
  needs the HS-surface. Every lifted holonomy of `L` is conjugate to `hol` (gx's
  `GX.HasLiftedHolonomy.conj`), so the circle forms conclude for all of them.
* **(c)** « Degree `k` » (l.696–698) is `GX.GTilde.HasDegree f k`: `f = δᵏ g`, `g` with a fixed
  point; unique (`GX.GTilde.HasDegree.unique`), conjugation-invariant (`GX.GTilde.HasDegree.conj`).
  « Positive » (l.748, l.754–756) is the positive parabolic class: `g x ≥ x` for every `x`.
* **(d)** « Elliptic » is gx's `GX.GTilde.IsElliptic` (`tr² < 4`), under which (F4) holds for every
  `a`. In the wide reading (l.693–694, OQ-113 (d)) it holds for `a ≥ 1` only.
* **(e)** Normalisation (OQ-113 (a)). (S), (S′), (F1)–(F3), `GX.funnel_F4_tau` and `R̃` do not
  depend on it. Only `GX.funnel_F4`, `GX.funnel_F4_circle`, `GX.GTilde.angle_rot` read
  `angle = 2π τ`.
* **(f)** Not stated: the funnel sentence of (F2), and (N) itself (dispatch).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Builds on
`GX.BBS.RP1Circles` (T-bbs-rp1-circles, e3220f0).
The generic `G̃` lemmas above (`R̃`, `τ`, `IsRotLift`, the fixed-point and parabolic lemmas,
`GX.PSL2.trSq_one`) live in `GX.BBS.GTilde` (hoisted by T-bbs-hs-graduate, names
unchanged); this file keeps (S), the conjugation lemmas, (N), the degree and (F1)–(F4).
-/

noncomputable section

open Set Real
open scoped MatrixGroups

namespace GX

set_option linter.unusedSectionVars false

namespace GTilde

/-! ### (S) and (S′) (N9 §2) -/

/-- Conjugation preserves `x < f x` (N9 l.802–803). -/
theorem lt_conj_apply {f : GTilde} (hf : ∀ y, y < f y) (h : GTilde) (x : ℝ) :
    x < (h * f * h⁻¹) x := by
  rw [coe_mul_apply, coe_mul_apply]
  have := GTilde.strictMono h (hf (h⁻¹ x))
  rwa [apply_inv_apply] at this

/-- Conjugation preserves `f x < δ x` (N9 l.802–803). -/
theorem conj_apply_lt_delta {f : GTilde} (hf : ∀ y, f y < delta y) (h : GTilde) (x : ℝ) :
    (h * f * h⁻¹) x < delta x := by
  rw [coe_mul_apply, coe_mul_apply, delta_apply]
  have h1 := hf (h⁻¹ x)
  rw [delta_apply] at h1
  have h2 := GTilde.strictMono h h1
  have h3 : h (h⁻¹ x + 1) = h (h⁻¹ x) + 1 := by
    have := map_add_int h (h⁻¹ x) 1
    rwa [Int.cast_one] at this
  rwa [h3, apply_inv_apply] at h2

/-- **(S)** for `R̃(φ)`. -/
theorem rot_S {φ : ℝ} (h0 : 0 < φ) (h2 : φ < 2 * π) (x : ℝ) :
    x < rot φ x ∧ rot φ x < delta x := by
  rw [rot_apply, delta_apply]
  have h3 : 0 < φ / (2 * π) := by positivity
  have h4 : φ / (2 * π) < 1 := (div_lt_one (by positivity)).2 h2
  constructor <;> linarith

/-- (S) is sharp: it holds exactly for `0 < φ < 2π`. -/
theorem rot_S_iff (φ : ℝ) : (∀ x, x < rot φ x ∧ rot φ x < delta x) ↔ 0 < φ ∧ φ < 2 * π := by
  refine ⟨fun h => ?_, fun h => rot_S h.1 h.2⟩
  have h0 := h 0
  rw [rot_apply, delta_apply, zero_add, zero_add] at h0
  have hπ : (0 : ℝ) < 2 * π := by positivity
  exact ⟨(div_pos_iff_of_pos_right hπ).1 h0.1, (div_lt_one hπ).1 h0.2⟩

/-- **(S)** for every rotation lift `R̃_c(φ)`. -/
theorem IsRotLift.S {φ : ℝ} {f : GTilde} (hf : IsRotLift φ f) (h0 : 0 < φ) (h2 : φ < 2 * π)
    (x : ℝ) : x < f x ∧ f x < delta x := by
  obtain ⟨h, rfl⟩ := hf
  exact ⟨lt_conj_apply (fun y => (rot_S h0 h2 y).1) h x,
    conj_apply_lt_delta (fun y => (rot_S h0 h2 y).2) h x⟩

end GTilde

/-! ### The singularities of `H̄` and the relation (N) (N9 §1, §3.2, §3.4) -/

/-- The kind of a singularity of `H̄` (N9 §1): a time-like singularity (a cone point) of cone
angle `θ`, or a cusp. -/
inductive SingKind : Type
  | cone (θ : ℝ) : SingKind
  | cusp : SingKind

namespace SingKind

/-- `P` is **a lifted local holonomy** at a singularity of kind `s` (N9 §3.2, §3.4): a conjugate
of `R̃(θ)` at a cone point of angle `θ`, a parabolic lift with a fixed point at a cusp. -/
def IsLift : SingKind → GTilde → Prop
  | cone θ, f => GTilde.IsRotLift θ f
  | cusp, f => GTilde.IsParabolic f ∧ ∃ x, f x = x

/-- **Positivity** (l.1510–1511: « all time-like singularities have a cone angle less that
$2\pi$ »): a cone angle is `< 2π`; nothing at a cusp. -/
def IsPositive : SingKind → Prop
  | cone θ => θ < 2 * π
  | cusp => True

/-- **(S) and (S′) at a singularity**: a positive lifted local holonomy `P` has `P y < δ y`. -/
theorem IsLift.apply_lt_delta {s : SingKind} {f : GTilde} (hf : s.IsLift f) (hs : s.IsPositive)
    (y : ℝ) : f y < GTilde.delta y := by
  cases s with
  | cone θ =>
    obtain ⟨h, rfl⟩ := hf
    refine GTilde.conj_apply_lt_delta (fun z => ?_) h y
    rw [GTilde.rot_apply, GTilde.delta_apply]
    have : θ / (2 * π) < 1 := (div_lt_one (by positivity)).2 hs
    linarith
  | cusp => exact GTilde.apply_lt_delta_of_fixed hf.2 y

end SingKind

/-- **The relation (N)** (N9 §3.4, N9 l.859), carried as a hypothesis (it needs tangent lifts and
Hopf's Umlaufsatz, not at this pin): `hol̃(C) = δ^{1−a} P̃₁′ ⋯ P̃ₐ′`. -/
def RelationN {a : ℕ} (hol : GTilde) (P : Fin a → GTilde) : Prop :=
  hol = GTilde.delta ^ (1 - (a : ℤ)) * (List.ofFn P).prod

theorem RelationN.eq_delta_of_zero {hol : GTilde} {P : Fin 0 → GTilde} (hN : RelationN hol P) :
    hol = GTilde.delta := by
  rw [hN]; simp

/-! ### (F1) (N9 §4) -/

/-- A product of elements of `G̃` with `f y < δ y` moves `x` by at most its length. -/
theorem GTilde.list_prod_apply_le (l : List GTilde) (hl : ∀ f ∈ l, ∀ y, f y < GTilde.delta y)
    (x : ℝ) : l.prod x ≤ x + l.length := by
  induction l generalizing x with
  | nil => simp only [List.prod_nil, List.length_nil, CharP.cast_eq_zero, add_zero]; exact le_rfl
  | cons f l ih =>
    rw [List.prod_cons, GTilde.coe_mul_apply, List.length_cons]
    have h1 := hl f List.mem_cons_self (l.prod x)
    have h2 := ih (fun g hg => hl g (List.mem_cons_of_mem _ hg)) x
    rw [GTilde.delta_apply] at h1
    rw [Nat.cast_succ]; linarith

/-- ... and a nonempty one by less than its length (N9 l.876–877: `f(x) < δ^a x`). -/
theorem GTilde.list_prod_apply_lt (l : List GTilde) (hl : ∀ f ∈ l, ∀ y, f y < GTilde.delta y)
    (hne : l ≠ []) (x : ℝ) : l.prod x < x + l.length := by
  obtain ⟨f, l, rfl⟩ := List.exists_cons_of_ne_nil hne
  rw [List.prod_cons, GTilde.coe_mul_apply, List.length_cons]
  have h1 := hl f List.mem_cons_self (l.prod x)
  have h2 := GTilde.list_prod_apply_le l (fun g hg => hl g (List.mem_cons_of_mem _ hg)) x
  rw [GTilde.delta_apply] at h1
  rw [Nat.cast_succ]; linarith

/-- **(F1), the `G̃` lemma** (N9 l.875–878): if every factor satisfies `P y < δ y` and `a ≥ 1`,
then `δ^{1−a} P₁ ⋯ Pₐ x < δ x`. -/
theorem funnel_F1_of_forall_lt {a : ℕ} (ha : 1 ≤ a) {P : Fin a → GTilde}
    (hP : ∀ j y, P j y < GTilde.delta y) {hol : GTilde} (hN : RelationN hol P) (x : ℝ) :
    hol x < GTilde.delta x := by
  rw [hN, GTilde.coe_mul_apply, GTilde.delta_zpow_apply, GTilde.delta_apply]
  have hne : List.ofFn P ≠ [] := by rw [Ne, List.ofFn_eq_nil_iff]; omega
  have := GTilde.list_prod_apply_lt (List.ofFn P) (fun f hf y => by
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hf
    exact hP j y) hne x
  rw [List.length_ofFn] at this
  rw [Int.cast_sub, Int.cast_one, Int.cast_natCast]; linarith

/-- **(F1)** (N9 l.749): with positivity, `a ≥ 1` and the relation (N), `hol̃(C) x < δ x`. -/
theorem funnel_F1 {a : ℕ} (ha : 1 ≤ a) {s : Fin a → SingKind} (hpos : ∀ j, (s j).IsPositive)
    {P : Fin a → GTilde} (hP : ∀ j, (s j).IsLift (P j)) {hol : GTilde} (hN : RelationN hol P)
    (x : ℝ) : hol x < GTilde.delta x :=
  funnel_F1_of_forall_lt ha (fun j y => (hP j).apply_lt_delta (hpos j) y) hN x

/-! ### The degree (l.696–698) -/

namespace GTilde

/-- `f` **has degree `k`** (l.696–698): `f = δᵏ g` with `g` having a fixed point in `ℝP̃¹`. -/
def HasDegree (f : GTilde) (k : ℤ) : Prop := ∃ f₀ : GTilde, (∃ x, f₀ x = x) ∧ f = delta ^ k * f₀

theorem HasDegree.unique {f : GTilde} {k k' : ℤ} (hk : HasDegree f k) (hk' : HasDegree f k') :
    k = k' := by
  obtain ⟨f₀, h₀, rfl⟩ := hk
  obtain ⟨f₀', h₀', hf'⟩ := hk'
  exact delta_zpow_mul_unique h₀ h₀' hf'

theorem hasDegree_zero_iff {f : GTilde} : HasDegree f 0 ↔ ∃ x, f x = x := by
  refine ⟨fun ⟨f₀, h₀, hf⟩ => ?_, fun h => ⟨f, h, by rw [zpow_zero, one_mul]⟩⟩
  rw [hf, zpow_zero, one_mul]; exact h₀

theorem HasDegree.conj {f : GTilde} {k : ℤ} (hk : HasDegree f k) (h : GTilde) :
    HasDegree (h * f * h⁻¹) k := by
  obtain ⟨f₀, ⟨x, hx⟩, rfl⟩ := hk
  refine ⟨h * f₀ * h⁻¹, ⟨h x, by rw [coe_mul_apply, coe_mul_apply, inv_apply_apply, hx]⟩,
    ext' fun y => ?_⟩
  simp only [coe_mul_apply, delta_zpow_apply]
  rw [map_add_int]

theorem exists_hasDegree_of_not_isElliptic {f : GTilde} (hf : ¬ IsElliptic f) :
    ∃ k, HasDegree f k := by
  obtain ⟨k, f₀, h₀, hf'⟩ := exists_delta_zpow_mul_of_not_isElliptic hf
  exact ⟨k, f₀, h₀, hf'⟩

/-- **The degree is `0`** (N9 l.879–883): if `f x < δ x` for every `x` and `x < f x` for some `x`
(eq>), every degree of `f` is `0`. -/
theorem HasDegree.eq_zero {f : GTilde} {k : ℤ} (hk : HasDegree f k)
    (h1 : ∀ x, f x < delta x) (h2 : ∃ x, x < f x) : k = 0 := by
  obtain ⟨f₀, ⟨x₀, hx₀⟩, rfl⟩ := hk
  obtain ⟨x, hx⟩ := h2
  have e : ∀ y, (delta ^ k * f₀) y = f₀ y + k := fun y => by
    rw [coe_mul_apply, delta_zpow_apply]
  -- `k ≥ 1` contradicts (F1) at the fixed point
  have hk1 : (k : ℝ) < 1 := by
    have := h1 x₀
    rw [e, hx₀, delta_apply] at this
    linarith
  -- `k ≤ -1` contradicts (eq>), by (S′)
  have hk2 : (-1 : ℝ) < k := by
    have h3 := apply_lt_delta_of_fixed ⟨x₀, hx₀⟩ x
    rw [e] at hx
    rw [delta_apply] at h3
    linarith
  have : k < 1 := by exact_mod_cast hk1
  have : -1 < k := by exact_mod_cast hk2
  omega

end GTilde


/-! ### (F2), (F3), (F4) for an element of `G̃` (N9 §4) -/

section Funnel

variable {a : ℕ} {s : Fin a → SingKind} {P : Fin a → GTilde} {hol : GTilde}

/-- **The degree of a non-elliptic, non-central `hol̃(C)` is `0`** (N9 l.879–883), for every `a`:
at `a = 0`, (N) makes `hol̃(C) = δ` central. -/
theorem funnel_deg_zero (hpos : ∀ j, (s j).IsPositive) (hP : ∀ j, (s j).IsLift (P j))
    (hN : RelationN hol P) (hgt : ∃ x, x < hol x) (hne : ¬ GTilde.IsElliptic hol)
    (h1 : GTilde.toPSL hol ≠ 1) :
    GTilde.HasDegree hol 0 ∧ (∀ k, GTilde.HasDegree hol k → k = 0) ∧ GTilde.tau hol = 0 := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact absurd (by rw [hN.eq_delta_of_zero, GTilde.toPSL_delta]) h1
  have hF1 := funnel_F1 ha hpos hP hN
  obtain ⟨k, hk⟩ := GTilde.exists_hasDegree_of_not_isElliptic hne
  have hk0 := hk.eq_zero hF1 hgt
  subst hk0
  obtain ⟨x, hx⟩ := GTilde.hasDegree_zero_iff.1 hk
  exact ⟨hk, fun k' hk' => hk'.eq_zero hF1 hgt, GTilde.tau_eq_zero_of_fixed hx⟩

/-- **(F2)**, `G̃` form: a hyperbolic `hol̃(C)` satisfying (N) and (eq>) has degree `0`, and only
degree `0`; its translation number is `0`. -/
theorem funnel_F2 (hpos : ∀ j, (s j).IsPositive) (hP : ∀ j, (s j).IsLift (P j))
    (hN : RelationN hol P) (hgt : ∃ x, x < hol x) (hhyp : GTilde.IsHyperbolic hol) :
    GTilde.HasDegree hol 0 ∧ (∀ k, GTilde.HasDegree hol k → k = 0) ∧ GTilde.tau hol = 0 :=
  funnel_deg_zero hpos hP hN hgt hhyp.not_isElliptic hhyp.toPSL_ne_one

/-- **(F3)**, `G̃` form: a parabolic `hol̃(C)` satisfying (N) and (eq>) has degree `0`, only
degree `0`, and is positive: `x ≤ hol̃(C) x` for every `x`. -/
theorem funnel_F3 (hpos : ∀ j, (s j).IsPositive) (hP : ∀ j, (s j).IsLift (P j))
    (hN : RelationN hol P) (hgt : ∃ x, x < hol x) (hpar : GTilde.IsParabolic hol) :
    GTilde.HasDegree hol 0 ∧ (∀ k, GTilde.HasDegree hol k → k = 0) ∧ GTilde.tau hol = 0 ∧
      ∀ x, x ≤ hol x := by
  obtain ⟨h0, huniq, htau⟩ := funnel_deg_zero hpos hP hN hgt hpar.not_isElliptic hpar.2
  exact ⟨h0, huniq, htau, hpar.le_apply (GTilde.hasDegree_zero_iff.1 h0) hgt⟩

/-- **(F4)**, translation-number form (normalisation-free): an elliptic `hol̃(C)` satisfying (N)
and (eq>) has `0 < τ < 1`. -/
theorem funnel_F4_tau (hpos : ∀ j, (s j).IsPositive) (hP : ∀ j, (s j).IsLift (P j))
    (hN : RelationN hol P) (hgt : ∃ x, x < hol x) (hell : GTilde.IsElliptic hol) :
    0 < GTilde.tau hol ∧ GTilde.tau hol < 1 := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact absurd hell (GTilde.not_isElliptic_of_toPSL_eq_one
      (by rw [hN.eq_delta_of_zero, GTilde.toPSL_delta]))
  have hF1 := funnel_F1 ha hpos hP hN
  obtain ⟨x₀, hx₀⟩ := hgt
  -- (eq>) and freeness: `x < hol x` everywhere, so `τ > 0`
  have hlt : ∀ x, x < hol x := GTilde.lt_apply_of_forall_ne hell.apply_ne hx₀
  refine ⟨?_, ?_⟩
  · exact CircleDeg1Lift.lt_translationNumber_of_forall_add_lt
      ((hol : CircleDeg1Liftˣ) : CircleDeg1Lift) (GTilde.continuous hol) (z := 0)
      fun x => by rw [add_zero]; exact hlt x
  -- (F1): `hol x < x + 1` everywhere, so `τ < 1`
  · exact CircleDeg1Lift.translationNumber_lt_of_forall_lt_add
      ((hol : CircleDeg1Liftˣ) : CircleDeg1Lift) (GTilde.continuous hol) (z := 1)
      fun x => by have := hF1 x; rwa [GTilde.delta_apply] at this

/-- **(F4)**, angle form (`GX.GTilde.angle`, `angle δ = 2π`, OQ-113 (a)): `0 < Θ < 2π`. -/
theorem funnel_F4 (hpos : ∀ j, (s j).IsPositive) (hP : ∀ j, (s j).IsLift (P j))
    (hN : RelationN hol P) (hgt : ∃ x, x < hol x) (hell : GTilde.IsElliptic hol) :
    0 < GTilde.angle hol ∧ GTilde.angle hol < 2 * π := by
  obtain ⟨h0, h1⟩ := funnel_F4_tau hpos hP hN hgt hell
  rw [GTilde.angle_eq_two_pi_mul_tau]
  have hπ : (0 : ℝ) < 2 * π := by positivity
  exact ⟨by positivity, by nlinarith⟩

/-- **(F4) in the wide reading of « elliptic »** (OQ-113 (d): central holonomy counts as
elliptic): true for `a ≥ 1`, where `hol̃(C)` is never central. -/
theorem funnel_F4_wide (ha : 1 ≤ a) (hpos : ∀ j, (s j).IsPositive) (hP : ∀ j, (s j).IsLift (P j))
    (hN : RelationN hol P) (hgt : ∃ x, x < hol x)
    (hell : GTilde.IsElliptic hol ∨ GTilde.toPSL hol = 1) :
    0 < GTilde.tau hol ∧ GTilde.tau hol < 1 ∧ 0 < GTilde.angle hol ∧ GTilde.angle hol < 2 * π := by
  rcases hell with hell | hc
  · exact ⟨(funnel_F4_tau hpos hP hN hgt hell).1, (funnel_F4_tau hpos hP hN hgt hell).2,
      (funnel_F4 hpos hP hN hgt hell).1, (funnel_F4 hpos hP hN hgt hell).2⟩
  -- a central `hol̃(C) = δⁿ` contradicts (F1) and (eq>) together
  exfalso
  have hk : hol ∈ GTilde.toPSL.ker := hc
  rw [GTilde.ker_toPSL, Subgroup.mem_zpowers_iff] at hk
  obtain ⟨n, rfl⟩ := hk
  obtain ⟨x, hx⟩ := hgt
  have h1 := funnel_F1 ha hpos hP hN x
  rw [GTilde.delta_zpow_apply] at hx h1
  rw [GTilde.delta_apply] at h1
  have : (0 : ℝ) < n := by linarith
  have : (n : ℝ) < 1 := by linarith
  have : 0 < n := by exact_mod_cast ‹(0 : ℝ) < n›
  have : n < 1 := by exact_mod_cast ‹(n : ℝ) < 1›
  omega

end Funnel

/-- **(F4) fails at `a = 0` in the wide reading** (a finding): `H̄ = ℍ²` with no singularity, the
relation (N) gives `hol̃(C) = δ`, the holonomy of `ℝP¹` itself, central (elliptic in the reading
of l.693–694), of angle exactly `2π`. -/
theorem funnel_F4_wide_fails :
    RelationN GTilde.delta (Fin.elim0 : Fin 0 → GTilde) ∧ HasLiftedHolonomy RP1 GTilde.delta ∧
      GTilde.toPSL GTilde.delta = 1 ∧ GTilde.angle GTilde.delta = 2 * π ∧
      ¬ GTilde.angle GTilde.delta < 2 * π := by
  refine ⟨by simp [RelationN], hasLiftedHolonomy_rp1, GTilde.toPSL_delta, GTilde.angle_delta, ?_⟩
  rw [GTilde.angle_delta]
  exact lt_irrefl _

/-! ### (F1)–(F4) for an `ℝP¹`-circle (N9 §1) -/

section Circle

variable {L : Type*} [TopologicalSpace L] [ChartedSpace RP1 L]
  [HasGroupoid L (gxGroupoid PSL(2, ℝ) RP1)]
  {a : ℕ} {s : Fin a → SingKind} {P : Fin a → GTilde} {hol : GTilde}

/-- **(F1)** for every lifted holonomy of `L`, when one of them satisfies (N). -/
theorem funnel_F1_circle (ha : 1 ≤ a) (hpos : ∀ j, (s j).IsPositive)
    (hP : ∀ j, (s j).IsLift (P j)) (hf : HasLiftedHolonomy L hol) (hN : RelationN hol P)
    {f : GTilde} (hf' : HasLiftedHolonomy L f) (x : ℝ) : f x < GTilde.delta x := by
  obtain ⟨h, rfl⟩ := hf.conj hf'
  exact GTilde.conj_apply_lt_delta (funnel_F1 ha hpos hP hN) h x

/-- **(F2)**: `L` is a hyperbolic `ℝP¹`-circle of degree `0`: every lifted holonomy of `L` has
degree `0`, and only degree `0`. -/
theorem funnel_F2_circle (hpos : ∀ j, (s j).IsPositive) (hP : ∀ j, (s j).IsLift (P j))
    (hf : HasLiftedHolonomy L hol) (hN : RelationN hol P) (hhyp : GTilde.IsHyperbolic hol)
    {f : GTilde} (hf' : HasLiftedHolonomy L f) :
    GTilde.HasDegree f 0 ∧ ∀ k, GTilde.HasDegree f k → k = 0 := by
  obtain ⟨h, rfl⟩ := hf.conj hf'
  have h0 := (funnel_F2 hpos hP hN hf.lt_apply hhyp).1.conj h
  exact ⟨h0, fun k hk => hk.unique h0⟩

/-- **(F3)**: `L` is a parabolic `ℝP¹`-circle of degree `0`, positive. -/
theorem funnel_F3_circle (hpos : ∀ j, (s j).IsPositive) (hP : ∀ j, (s j).IsLift (P j))
    (hf : HasLiftedHolonomy L hol) (hN : RelationN hol P) (hpar : GTilde.IsParabolic hol)
    {f : GTilde} (hf' : HasLiftedHolonomy L f) :
    GTilde.HasDegree f 0 ∧ (∀ k, GTilde.HasDegree f k → k = 0) ∧ ∀ x, x ≤ f x := by
  obtain ⟨h, rfl⟩ := hf.conj hf'
  obtain ⟨h0, -, -, hle⟩ := funnel_F3 hpos hP hN hf.lt_apply hpar
  exact ⟨h0.conj h, fun k hk => hk.unique (h0.conj h), GTilde.le_conj_apply hle h⟩

/-- **(F4)**: the real angle `Θ` of the elliptic `ℝP¹`-circle `L` satisfies `0 < Θ < 2π`
(`GX.HasRealAngle`, `angle δ = 2π`), and every lifted holonomy has `0 < τ < 1`. -/
theorem funnel_F4_circle (hpos : ∀ j, (s j).IsPositive) (hP : ∀ j, (s j).IsLift (P j))
    (hf : HasLiftedHolonomy L hol) (hN : RelationN hol P) (hell : GTilde.IsElliptic hol) :
    (∀ Θ, HasRealAngle L Θ → 0 < Θ ∧ Θ < 2 * π) ∧
      ∀ f, HasLiftedHolonomy L f → 0 < GTilde.tau f ∧ GTilde.tau f < 1 := by
  refine ⟨fun Θ hΘ => ?_, fun f hf' => ?_⟩
  · rw [hΘ.unique ⟨hol, hf, rfl⟩]
    exact funnel_F4 hpos hP hN hf.lt_apply hell
  · obtain ⟨h, rfl⟩ := hf.conj hf'
    rw [GTilde.tau_conj]
    exact funnel_F4_tau hpos hP hN hf.lt_apply hell

end Circle

/-! ### The checks of N9 §3.4, and the sharpness of positivity -/

/-- `a = 1`: `hol̃(C) = P̃(p₁)`, of angle `θ₁` (N9 l.865). -/
theorem relationN_one (f : GTilde) : RelationN f ![f] := by
  simp [RelationN]

/-- Two cone points pushed together: `δ⁻¹ R̃(θ₁) R̃(θ₂) = R̃(θ₁ + θ₂ − 2π)`, the merged cone
(N9 l.866). -/
theorem relationN_two_rot (θ₁ θ₂ : ℝ) :
    RelationN (GTilde.rot (θ₁ + θ₂ - 2 * π)) ![GTilde.rot θ₁, GTilde.rot θ₂] := by
  refine GTilde.ext' fun x => ?_
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
    Matrix.cons_val_zero, Matrix.cons_val_succ, GTilde.coe_mul_apply, GTilde.delta_zpow_apply,
    GTilde.rot_apply]
  push_cast
  field_simp
  ring

/-- **Positivity is needed in (F1)** (N9 l.877–878): one cone point of angle `2π` gives
`hol̃(C) = R̃(2π) = δ`, and (F1) fails. -/
theorem funnel_F1_needs_positivity :
    (SingKind.cone (2 * π)).IsLift (GTilde.rot (2 * π)) ∧
      RelationN (GTilde.rot (2 * π)) ![GTilde.rot (2 * π)] ∧
      ¬ ∀ x, GTilde.rot (2 * π) x < GTilde.delta x := by
  refine ⟨GTilde.isRotLift_rot _, relationN_one _, fun h => ?_⟩
  have := h 0
  rw [GTilde.rot_two_pi] at this
  exact lt_irrefl _ this

end GX
