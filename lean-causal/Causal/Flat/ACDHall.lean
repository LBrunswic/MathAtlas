import Causal.Flat.TitsNull

/-!
# `Causal.Flat.ACDHall` — two elements of a discrete `Γ` with linear parts near `1` generate a nilpotent group

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §5,
Theorem 5.1 (`bthm:ausl`, `GHFspace.tex:1696`), carried as the external
`AuslanderCarriereDalbo d` (`Flat/Externals`, DEC-36). **No ledger label is certified here**:
this module is Step 1 ("local nilpotency from discreteness") of the Lorentz Zassenhaus–Frobenius
route of `docs/CARRIERE-DALBO-SURVEY.md` §2.2 T1 (DEC-121), the half of the local commutation
lemma (★) that spends discreteness.

> Let $\Gamma$ be a discrete subgroup of $\mbox{Aff}(n, {\mathbb R})$.
> Then, the identity component $G_{0}$ of
> the closure of $L(\Gamma)$ in $GL(n, {\mathbb R})$ is nilpotent. (l.1699–1701)

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; `Minkowski d` has `d` spatial
dimensions, so Barbot's `n` is `d + 1`.

## The proof

1. **Hall's lemma** (`isNilpotent_closure_of_leftCommIter_eq_one`; Robinson, *A Course in the
   Theory of Groups*, 5.1.7): if `G = ⟨X⟩` and every left-normed commutator
   `[x₀, x₁, …, x_k] = [[x₀, x₁], …, x_k]` with letters in `X` is `1`, then `G` is nilpotent.
   With `N_i` the normal closure in `⟨X⟩` of the weight-`i` left-normed commutators,
   `γ_i ≤ N_i` by induction: modulo `N_{i+1}` each weight-`i` commutator commutes with every
   `x ∈ X`, hence is central, so `[N_i, ⟨X⟩] ≤ N_{i+1}`.
2. **Multi-letter halving** (`norm_leftCommIter_le`): for `F` multiplicative into a normed ring,
   `‖F x^{±1} − 1‖ ≤ 1/32` on the letters and `‖F c^{±1} − 1‖ ≤ m ≤ 3` give
   `‖F [c, x₁, …, x_k]^{±1} − 1‖ ≤ m · 2⁻ᵏ` (`norm_commutator_le_half`, `Flat/TitsNull`, at each
   step, with `X = F x`, `Y = F c`).
3. **The scaling** (`exists_affScale`): the affine extension `ĝ (y, s) = (L(g) y + s τ(g), s)`
   (`affExt`) is block upper triangular for `𝐌ⁿ × ℝ = 𝐌ⁿ ⊕ ℝ`, with diagonal `(L(g), 1)`;
   conjugating by `D_K (y, s) = (y, K s)` (`scaleBy`, `norm_scaleBy_conj_sub_le`) divides the
   translation block by `K`, so for `K` large every `ĝ^{±1}`, `g` in a finite set with
   `‖L(g) − 1‖ ≤ 1/64`, is `1/32`-close to `1`. This is the dilation `x ↦ x / K` of the survey.
4. **Discreteness** (`exists_affExt_isolated`): unscaling costs the fixed factor `‖D⁻¹‖ ‖D‖`, so
   all left-normed commutators of weight `k` in `{g, h}` tend to `1` uniformly and are `1` for `k`
   large; Hall's lemma concludes (`isNilpotent_closure_pair_of_near_one`).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `Γ` discrete (l.1699) | ✓ carried: `DiscreteTopology Γ` (`isomTopology`), spent in step 4 only |
| (route) `g`, `h` with linear parts near `1` | ✓ carried: `‖L(g) − 1‖ < 1/128`, `‖L(h) − 1‖ < 1/128` (operator norm on `Minkowski d`) |

## SCOPE (disclosed)

* Step 1 of the route only; Step 2 (`Flat/ACDNull`, `Flat/ACDLoxodromic`) turns the nilpotency
  of `⟨g, h⟩` into the commutation of `L(g)`, `L(h)`, and the assembly concludes `bthm:ausl`.
* The nilpotency class of `⟨g, h⟩` depends on the pair; nothing uniform is claimed.
* Proved in full (prover, 2026-11-03): no `sorry`, no axiom. The skeleton's statements are
  unchanged; `isNilpotent_closure_pair_of_near_one` is the one the assembly uses. Hall's lemma
  is proved for letters in `X` (not `X^{±1}`): a weight-`i` commutator commuting with every
  `x ∈ X` modulo `N_{i+1}` commutes with `⟨X⟩` there.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
DEC-121 (`docs/CARRIERE-DALBO-SURVEY.md` §2.2, T1 Step 1).
-/

namespace Causal.Flat

open Set Function Topology Module

variable {d : ℕ}

section Hall

variable {G : Type*} [Group G]

/-- The left-normed commutator `[c, x₁, …, x_k] = [[c, x₁], …, x_k]`, with `[c, x] = c x c⁻¹ x⁻¹`
(mathlib's `⁅c, x⁆`). -/
def leftCommIter : G → List G → G
  | c, [] => c
  | c, x :: l => leftCommIter (c * x * c⁻¹ * x⁻¹) l

@[simp] theorem leftCommIter_nil (c : G) : leftCommIter c [] = c := rfl

@[simp] theorem leftCommIter_cons (c x : G) (l : List G) :
    leftCommIter c (x :: l) = leftCommIter (c * x * c⁻¹ * x⁻¹) l := rfl

/-- `[c, l₁ ++ l₂] = [[c, l₁], l₂]`. -/
theorem leftCommIter_append (c : G) (l₁ l₂ : List G) :
    leftCommIter c (l₁ ++ l₂) = leftCommIter (leftCommIter c l₁) l₂ := by
  induction l₁ generalizing c with
  | nil => rfl
  | cons x l ih => exact ih _

/-- A group homomorphism maps left-normed commutators to left-normed commutators. -/
theorem map_leftCommIter {H : Type*} [Group H] (f : G →* H) (c : G) (l : List G) :
    f (leftCommIter c l) = leftCommIter (f c) (l.map f) := by
  induction l generalizing c with
  | nil => rfl
  | cons x l ih => simp only [leftCommIter_cons, List.map_cons, ih, map_mul, map_inv]

/-- A subgroup contains the left-normed commutators of its elements. -/
theorem leftCommIter_mem {S : Subgroup G} {c : G} (hc : c ∈ S) {l : List G}
    (hl : ∀ y ∈ l, y ∈ S) : leftCommIter c l ∈ S := by
  induction l generalizing c with
  | nil => exact hc
  | cons x l ih =>
    have hx : x ∈ S := hl x List.mem_cons_self
    exact ih (S.mul_mem (S.mul_mem (S.mul_mem hc hx) (S.inv_mem hc)) (S.inv_mem hx))
      fun y hy => hl y (List.mem_cons_of_mem _ hy)

/-- The left-normed commutators `[x₀, x₁, …, x_n]` of weight `n + 1` with letters in `X`. -/
def leftCommSet (X : Set G) (n : ℕ) : Set G :=
  {c | ∃ x ∈ X, ∃ l : List G, (∀ y ∈ l, y ∈ X) ∧ l.length = n ∧ leftCommIter x l = c}

/-- **The step of Hall's lemma**: when `X` generates `G` and `N` is a normal subgroup containing
the weight-`(n + 2)` commutators, the weight-`(n + 1)` commutators are central modulo `N`, so
`⁅N_{n+1}, G⁆ ≤ N` (`N_{n+1}` their normal closure). -/
theorem commutator_normalClosure_leftCommSet_le {X : Set G} (hX : Subgroup.closure X = ⊤)
    {n : ℕ} {N : Subgroup G} [N.Normal] (hN : leftCommSet X (n + 1) ⊆ N) :
    ⁅Subgroup.normalClosure (leftCommSet X n), ⊤⁆ ≤ N := by
  have hcen : Subgroup.normalClosure (leftCommSet X n) ≤
      (Subgroup.center (G ⧸ N)).comap (QuotientGroup.mk' N) := by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨x, hx, l, hl, hlen, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_center_iff]
    have hcl : Subgroup.closure X ≤ (Subgroup.centralizer
        {QuotientGroup.mk' N (leftCommIter x l)}).comap (QuotientGroup.mk' N) := by
      refine (Subgroup.closure_le _).2 fun y hy => ?_
      rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
      rintro _ rfl
      have hmem : leftCommIter x (l ++ [y]) ∈ N :=
        hN ⟨x, hx, l ++ [y], fun z hz => by
          rcases List.mem_append.1 hz with hz | hz
          · exact hl z hz
          · rw [List.mem_singleton.1 hz]; exact hy, by simp [hlen], rfl⟩
      rw [leftCommIter_append, leftCommIter_cons, leftCommIter_nil, ← QuotientGroup.eq_one_iff,
        ← QuotientGroup.mk'_apply, ← commutatorElement_def, map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hmem
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
    have hg := hcl (hX ▸ Subgroup.mem_top g)
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at hg
    exact (hg _ rfl).symm
  rw [Subgroup.commutator_le]
  intro a ha g _
  have hz := hcen ha
  rw [Subgroup.mem_comap, Subgroup.mem_center_iff] at hz
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
    commutatorElement_eq_one_iff_mul_comm]
  exact (hz _).symm

/-- `γ_{n+1}(G) ≤ N_{n+1}`, the normal closure of the weight-`(n + 1)` left-normed commutators in a
generating set `X`. -/
theorem lowerCentralSeries_le_normalClosure_leftCommSet {X : Set G}
    (hX : Subgroup.closure X = ⊤) (n : ℕ) :
    Subgroup.lowerCentralSeries (⊤ : Subgroup G) n ≤
      Subgroup.normalClosure (leftCommSet X n) := by
  induction n with
  | zero =>
    rw [Subgroup.lowerCentralSeries_zero, ← hX]
    exact (Subgroup.closure_le _).2 fun x hx =>
      Subgroup.subset_normalClosure ⟨x, hx, [], by simp, rfl, rfl⟩
  | succ n ih =>
    rw [Subgroup.lowerCentralSeries_succ]
    exact (Subgroup.commutator_mono ih le_rfl).trans
      (commutator_normalClosure_leftCommSet_le hX Subgroup.subset_normalClosure)

/-- Hall's lemma for a group generated by `X`. -/
theorem isNilpotent_of_closure_eq_top_of_leftCommIter {X : Set G} (hX : Subgroup.closure X = ⊤)
    {k : ℕ} (h : ∀ x ∈ X, ∀ l : List G, (∀ y ∈ l, y ∈ X) → l.length = k → leftCommIter x l = 1) :
    Group.IsNilpotent G := by
  refine Subgroup.nilpotent_iff_lowerCentralSeries.2 ⟨k, le_bot_iff.1 ?_⟩
  refine (lowerCentralSeries_le_normalClosure_leftCommSet hX k).trans
    (Subgroup.normalClosure_le_normal ?_)
  rintro _ ⟨x, hx, l, hl, hlen, rfl⟩
  exact (Subgroup.mem_bot).2 (h x hx l hl hlen)

/-- **Hall's lemma** (Robinson 5.1.7): if every left-normed commutator of weight `k + 1` with
letters in `X` is trivial, the subgroup generated by `X` is nilpotent. -/
theorem isNilpotent_closure_of_leftCommIter_eq_one {X : Set G} {k : ℕ}
    (h : ∀ x ∈ X, ∀ l : List G, (∀ y ∈ l, y ∈ X) → l.length = k → leftCommIter x l = 1) :
    Group.IsNilpotent (Subgroup.closure X) := by
  refine isNilpotent_of_closure_eq_top_of_leftCommIter Subgroup.closure_closure_coe_preimage
    (k := k) fun x hx l hl hlen => Subtype.val_injective ?_
  have e := map_leftCommIter (Subgroup.closure X).subtype x l
  rw [Subgroup.coe_subtype] at e
  rw [Subgroup.coe_one, e]
  exact h _ hx _ (fun y hy => by
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    exact hl z hz) (by rw [List.length_map, hlen])

end Hall

section Halving

variable {R : Type*} [NormedRing R]

/-- **Multi-letter halving**: along a left-normed commutator whose letters are `1/32`-close to
`1` (with their inverses), the distance to `1` halves at each letter. -/
theorem norm_leftCommIter_le {G : Type*} [Group G] (h1 : ‖(1 : R)‖ ≤ 1) {F : G → R}
    (hF : ∀ a b, F (a * b) = F a * F b) (hF1 : F 1 = 1) {X : Set G}
    (hX : ∀ x ∈ X, ‖F x - 1‖ ≤ 1 / 32 ∧ ‖F x⁻¹ - 1‖ ≤ 1 / 32) (l : List G) (hl : ∀ y ∈ l, y ∈ X)
    {c : G} {m : ℝ} (hm : m ≤ 3) (hc : ‖F c - 1‖ ≤ m) (hci : ‖F c⁻¹ - 1‖ ≤ m) :
    ‖F (leftCommIter c l) - 1‖ ≤ m * (1 / 2) ^ l.length ∧
      ‖F (leftCommIter c l)⁻¹ - 1‖ ≤ m * (1 / 2) ^ l.length := by
  have hinv : ∀ a, F a * F a⁻¹ = 1 := fun a => by rw [← hF, mul_inv_cancel, hF1]
  induction l generalizing c m with
  | nil => simpa using ⟨hc, hci⟩
  | cons x l ih =>
    have hx := hX x (hl x List.mem_cons_self)
    obtain ⟨h1', h2'⟩ := norm_commutator_le_half h1 (hinv x) (hinv c) hx.1 hx.2 le_rfl hc hci hm
    have e1 : F (c * x * c⁻¹ * x⁻¹) = F c * F x * F c⁻¹ * F x⁻¹ := by simp only [hF]
    have e2 : F (c * x * c⁻¹ * x⁻¹)⁻¹ = F x * F c * F x⁻¹ * F c⁻¹ := by
      rw [show (c * x * c⁻¹ * x⁻¹)⁻¹ = x * c * x⁻¹ * c⁻¹ by group]; simp only [hF]
    have := ih (fun y hy => hl y (List.mem_cons_of_mem _ hy)) (m := m / 2) (by linarith)
      (by rw [e1]; exact h2') (by rw [e2]; exact h1')
    rw [leftCommIter_cons, List.length_cons, pow_succ]
    constructor <;> linarith [this.1, this.2]

end Halving

/-- Unscaling: `‖A − 1‖ ≤ ‖S'‖ ‖S‖ ‖S A S' − 1‖` when `S' S = 1`. -/
theorem norm_sub_one_le_of_conj {R : Type*} [NormedRing R] {S S' : R} (hS'S : S' * S = 1)
    (A : R) : ‖A - 1‖ ≤ ‖S'‖ * ‖S‖ * ‖S * A * S' - 1‖ := by
  have e : S' * (S * A * S' - 1) * S = A - 1 := by
    rw [mul_sub, sub_mul, mul_one, hS'S, show S' * (S * A * S') * S =
      (S' * S) * A * (S' * S) by simp only [mul_assoc], hS'S, one_mul, mul_one]
  rw [← e]
  calc ‖S' * (S * A * S' - 1) * S‖ ≤ ‖S'‖ * ‖S * A * S' - 1‖ * ‖S‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ = _ := by ring

section Scaling

/-- The two-block decomposition `𝐌ⁿ × ℝ = 𝐌ⁿ ⊕ ℝ`: `P 0 (y, s) = (y, 0)`, `P 1 (y, s) = (0, s)`. -/
noncomputable def affBlockProj : Fin 2 → (Minkowski d × ℝ →L[ℝ] Minkowski d × ℝ)
  | 0 => liftV LinearMap.id
  | 1 => lastV

/-- The two blocks are complementary idempotents. -/
theorem affBlockProj_mul (i j : Fin 2) :
    affBlockProj (d := d) i * affBlockProj j = if i = j then affBlockProj i else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, affBlockProj, if_true, Fin.reduceEq,
      if_false, liftV_mul_liftV, liftV_mul_lastV, lastV_mul_liftV, lastV_mul_lastV,
      LinearMap.id_comp]

/-- The two blocks sum to `1`. -/
theorem affBlockProj_sum : ∑ i, affBlockProj (d := d) i = 1 := by
  rw [Fin.sum_univ_two]
  refine ContinuousLinearMap.ext fun ⟨y, s⟩ => ?_
  show ((y, (0 : ℝ)) + (0, s) : Minkowski d × ℝ) = (y, s)
  exact Prod.ext (add_zero y) (zero_add s)

/-- `ĝ` is block upper triangular for `𝐌ⁿ ⊕ ℝ`. -/
theorem affBlockProj_affExt_lower (x : isom d) (i j : Fin 2) (hji : j < i) :
    affBlockProj i * affExt x * affBlockProj j = 0 := by
  fin_cases i <;> fin_cases j
  all_goals first
    | exact absurd hji (by decide)
    | exact lastV_mul_affExt_mul_liftV _ x

/-- The `ℝ`-diagonal block of `ĝ` is `1`. -/
theorem affBlockProj_affExt_diag (x : isom d) (i : Fin 2) (hi : i ≠ 0) :
    affBlockProj i * affExt x * affBlockProj i = affBlockProj i := by
  fin_cases i
  · exact absurd rfl hi
  · exact lastV_mul_affExt_mul_lastV x

/-- The `𝐌ⁿ`-diagonal block of `ĝ − 1` is `L(g) − 1`. -/
theorem norm_affBlockProj_zero_affExt_le (x : isom d) :
    ‖affBlockProj 0 * (affExt x - 1) * affBlockProj 0‖ ≤ ‖linToCLM (linOf x) - 1‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun ⟨y, s⟩ => ?_
  have e : (affBlockProj 0 * (affExt x - 1) * affBlockProj 0 :
      Minkowski d × ℝ →L[ℝ] Minkowski d × ℝ) (y, s) =
      ((linToCLM (linOf x) - 1) y, 0) := by
    show liftV LinearMap.id ((affExt x - 1) (y, 0)) = _
    rw [affExt_sub_one_apply, zero_smul, add_zero, liftV_apply]
    rfl
  rw [e]
  have e1 : ‖(((linToCLM (linOf x) - 1) y, (0 : ℝ)) : Minkowski d × ℝ)‖ =
      ‖(linToCLM (linOf x) - 1) y‖ := by
    rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]
  rw [e1]
  calc ‖(linToCLM (linOf x) - 1) y‖ ≤ ‖linToCLM (linOf x) - 1‖ * ‖y‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖linToCLM (linOf x) - 1‖ * ‖((y, s) : Minkowski d × ℝ)‖ :=
        mul_le_mul_of_nonneg_left (norm_fst_le (y, s)) (norm_nonneg _)

/-- The scaled affine extension is `‖L(g) − 1‖`-close to `1`, up to `K⁻¹` times a constant. -/
theorem norm_scaleBy_affBlockProj_affExt_sub_one_le (x : isom d) {K : ℝ} (hK : 1 ≤ K) :
    ‖scaleBy affBlockProj K * affExt x * scaleBy affBlockProj K⁻¹ - 1‖ ≤
      ‖linToCLM (linOf x) - 1‖ +
        K⁻¹ * ∑ i, ∑ j, ‖affBlockProj i * affExt x * affBlockProj j‖ := by
  have h1 := norm_scaleBy_conj_sub_le affBlockProj (affExt x) (affBlockProj_affExt_lower x) hK
  have h2 := sum_diag_sub_one affBlockProj affBlockProj_mul affBlockProj_sum (affExt x) 0
    (affBlockProj_affExt_diag x)
  have h3 := norm_affBlockProj_zero_affExt_le x
  rw [← h2] at h3
  calc ‖scaleBy affBlockProj K * affExt x * scaleBy affBlockProj K⁻¹ - 1‖
      = ‖(scaleBy affBlockProj K * affExt x * scaleBy affBlockProj K⁻¹ -
          ∑ i, affBlockProj i * affExt x * affBlockProj i) +
          (∑ i, affBlockProj i * affExt x * affBlockProj i - 1)‖ := by rw [sub_add_sub_cancel]
    _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add h1 h3
    _ = _ := add_comm _ _

/-- **The scaling of the affine extension**: for a finite set `T` of isometries with linear parts
`1/64`-close to `1`, a conjugation `S (·) S'` (`S S' = S' S = 1`; `S = D_K`, `D_K (y, s) = (y, K s)`)
brings every `affExt x`, `x ∈ T`, within `1/32` of `1`. -/
theorem exists_affScale {T : Set (isom d)} (hT : T.Finite)
    (hTε : ∀ x ∈ T, ‖linToCLM (linOf x) - 1‖ ≤ 1 / 64) :
    ∃ S S' : Minkowski d × ℝ →L[ℝ] Minkowski d × ℝ, S * S' = 1 ∧ S' * S = 1 ∧
      ∀ x ∈ T, ‖S * affExt x * S' - 1‖ ≤ 1 / 32 := by
  set C : isom d → ℝ := fun x => ∑ i, ∑ j, ‖affBlockProj i * affExt x * affBlockProj j‖
    with hCdef
  have hC0 : ∀ x, 0 ≤ C x := fun x =>
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  set K : ℝ := 1 + 64 * ∑ x ∈ hT.toFinset, C x with hKdef
  have hsum0 : 0 ≤ ∑ x ∈ hT.toFinset, C x := Finset.sum_nonneg fun x _ => hC0 x
  have hK1 : 1 ≤ K := by rw [hKdef]; linarith
  have hK0 : 0 < K := by linarith
  obtain ⟨hSS', hS'S⟩ := scaleBy_mul_scaleBy affBlockProj affBlockProj_mul affBlockProj_sum
    hK0.ne'
  refine ⟨_, _, hSS', hS'S, fun x hx => ?_⟩
  have hCx : C x ≤ ∑ x ∈ hT.toFinset, C x :=
    Finset.single_le_sum (fun y _ => hC0 y) (hT.mem_toFinset.2 hx)
  have hsmall : K⁻¹ * C x ≤ 1 / 64 := by
    rw [inv_mul_le_iff₀ hK0]; rw [hKdef]; nlinarith [hC0 x]
  linarith [norm_scaleBy_affBlockProj_affExt_sub_one_le x hK1, hTε x hx]

end Scaling

/-- `‖L(g⁻¹) − 1‖ ≤ 2 ‖L(g) − 1‖` when `‖L(g) − 1‖ ≤ 1/2` (Neumann series). -/
theorem norm_linToCLM_inv_sub_one_le {g : isom d} (hg : ‖linToCLM (linOf g) - 1‖ ≤ 1 / 2) :
    ‖linToCLM (linOf g⁻¹) - 1‖ ≤ 2 * ‖linToCLM (linOf g) - 1‖ := by
  set X := linToCLM (linOf g)
  set Y := linToCLM (linOf g⁻¹)
  have hXY : X * Y = 1 := by
    rw [← linToCLM_mul, ← linOf_mul, mul_inv_cancel, linOf_one', linToCLM_one]
  have h1 : ‖(1 : Minkowski d →L[ℝ] Minkowski d)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have eY : 1 - (X - 1) * Y = Y := by rw [sub_mul, hXY, one_mul, sub_sub_cancel]
  have eY1 : Y - 1 = -((X - 1) * Y) := by rw [sub_mul, hXY, one_mul, neg_sub]
  have hXY' : ‖(X - 1) * Y‖ ≤ ‖X - 1‖ * ‖Y‖ := norm_mul_le _ _
  have hYn : ‖Y‖ ≤ 2 := by
    have : ‖Y‖ ≤ 1 + ‖X - 1‖ * ‖Y‖ := by
      calc ‖Y‖ = ‖1 - (X - 1) * Y‖ := by rw [eY]
        _ ≤ ‖(1 : Minkowski d →L[ℝ] Minkowski d)‖ + ‖(X - 1) * Y‖ := norm_sub_le _ _
        _ ≤ 1 + ‖X - 1‖ * ‖Y‖ := add_le_add h1 hXY'
    have : ‖X - 1‖ * ‖Y‖ ≤ 1 / 2 * ‖Y‖ := mul_le_mul_of_nonneg_right hg (norm_nonneg _)
    linarith
  rw [eY1, norm_neg]
  calc ‖(X - 1) * Y‖ ≤ ‖X - 1‖ * ‖Y‖ := hXY'
    _ ≤ ‖X - 1‖ * 2 := mul_le_mul_of_nonneg_left hYn (norm_nonneg _)
    _ = _ := mul_comm _ _

/-- **Step 1 (local nilpotency from discreteness).** Two elements of a discrete `Γ ≤ Isom(𝐌ⁿ)`
whose linear parts are `1/128`-close to `1` generate a nilpotent subgroup. -/
theorem isNilpotent_closure_pair_of_near_one {Γ : Subgroup (isom d)} (hdisc : DiscreteTopology Γ)
    {g h : isom d} (hg : g ∈ Γ) (hh : h ∈ Γ) (hgε : ‖linToCLM (linOf g) - 1‖ < 1 / 128)
    (hhε : ‖linToCLM (linOf h) - 1‖ < 1 / 128) :
    Group.IsNilpotent (Subgroup.closure ({g, h} : Set (isom d))) := by
  have hgi := norm_linToCLM_inv_sub_one_le (g := g) (by linarith)
  have hhi := norm_linToCLM_inv_sub_one_le (g := h) (by linarith)
  have hT : ({g, h, g⁻¹, h⁻¹} : Set (isom d)).Finite := by
    simp only [Set.finite_insert, Set.finite_singleton]
  have hTε : ∀ x ∈ ({g, h, g⁻¹, h⁻¹} : Set (isom d)), ‖linToCLM (linOf x) - 1‖ ≤ 1 / 64 := by
    rintro x (rfl | rfl | rfl | rfl) <;> linarith
  obtain ⟨S, S', hSS', hS'S, hS⟩ := exists_affScale hT hTε
  obtain ⟨η, hη, hiso⟩ := exists_affExt_isolated hdisc
  have hF : ∀ a b : isom d, S * affExt (a * b) * S' =
      (S * affExt a * S') * (S * affExt b * S') := fun a b => by
    rw [affExt_mul]
    calc S * (affExt a * affExt b) * S' = S * affExt a * (S' * S) * affExt b * S' := by
          rw [hS'S, mul_one]; noncomm_ring
      _ = S * affExt a * S' * (S * affExt b * S') := by noncomm_ring
  have hF1 : S * affExt (1 : isom d) * S' = 1 := by rw [affExt_one, mul_one, hSS']
  have hX : ∀ x ∈ ({g, h} : Set (isom d)),
      ‖S * affExt x * S' - 1‖ ≤ 1 / 32 ∧ ‖S * affExt x⁻¹ * S' - 1‖ ≤ 1 / 32 := by
    rintro x (rfl | rfl)
    · exact ⟨hS _ (by simp), hS _ (by simp)⟩
    · exact ⟨hS _ (by simp), hS _ (by simp)⟩
  have hM : 0 < ‖S'‖ * ‖S‖ + 1 := by positivity
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hη hM) (show (1 / 2 : ℝ) < 1 by norm_num)
  refine isNilpotent_closure_of_leftCommIter_eq_one (k := k) fun x hx l hl hlen => ?_
  have hpair : ∀ y ∈ ({g, h} : Set (isom d)), y ∈ Γ := by
    rintro y (rfl | rfl)
    · exact hg
    · exact hh
  refine hiso _ (leftCommIter_mem (hpair x hx) fun y hy => hpair y (hl y hy)) ?_
  have hb := (norm_leftCommIter_le (F := fun x => S * affExt x * S')
    ContinuousLinearMap.norm_id_le hF hF1 hX l hl (by norm_num : (1 / 32 : ℝ) ≤ 3)
    (hX x hx).1 (hX x hx).2).1
  rw [hlen] at hb
  have hp : (0 : ℝ) ≤ (1 / 2) ^ k := by positivity
  rw [lt_div_iff₀ hM] at hk
  calc ‖affExt (leftCommIter x l) - 1‖
      ≤ ‖S'‖ * ‖S‖ * ‖S * affExt (leftCommIter x l) * S' - 1‖ := norm_sub_one_le_of_conj hS'S _
    _ ≤ ‖S'‖ * ‖S‖ * (1 / 32 * (1 / 2) ^ k) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ (1 / 2) ^ k * (‖S'‖ * ‖S‖ + 1) := by nlinarith [norm_nonneg S, norm_nonneg S']
    _ < η := hk

end Causal.Flat
