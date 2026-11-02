import Causal.Flat.Develop
import Causal.Flat.Externals
import Causal.Flat.Bieberbach
import Causal.Flat.TwistedProduct
import Causal.Flat.Examples

/-!
# `Causal.Flat.Nonlox.UnipotentLTP` — the parabolic case in a null frame: `Ω ⊆ Ω(S̃)`, the quotient `B = Γ''\Ω`, and `B` a linear twisted product over a unipotent spacetime

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §9
[9.U]–[9.A] (`GHFspace.tex` l.2904–2907, l.2927–2932, l.3120–3127), Lemma 5.5 (`blem:suspendre`)
and [3.U]. Line numbers are those of the **labelled** `papers/barbot/legacy/labeled/GHFspace.tex`.
Barbot's `𝐌ⁿ` is `Minkowski (d + 1)` here (kb/0024), `𝒰 ≅ 𝐌^{d₁+1}`.

* No b-label is certified. `exists_unipotent_ltp_of_frame` is item (7) of the obstruction of
  `Causal.Flat.nonloxodromic_parabolic` ([9.A], DEC-43 R1), proved with **no `sorry`**: given the
  frame `φ`, the parametrisation `ι` of `𝒰` (`ι (x, y, z) = (x, y + y₀, z₀ + J z)` in the frame),
  every `γ ∈ Γ''` restricting through `ι` to an element of `φ₁ A φ₁⁻¹` (`A` acting by
  `unipAction ℓ t`, `t ∈ L` ball-finite), and `Σ` inside the slab `]α, β[` (a component of
  `Ω(A)`), it builds `Ω`, proves `W ⊆ Ω ⊆ Ω(S̃)`, the quotient `B = Γ''\Ω` and `B` an LTP over a
  unipotent spacetime.

> Thanks to lemma \ref{suspendre}, and since the result we are proving is up to linear twisted
> products, we can assume that ${\mathcal U}$ is the entire Minkowski space (l.2904–2907)

> The causality domain $U(u)$ is then the open set formed by the points $(x, z, y)$ for which
> $u+yA(u) \neq 0$. (l.2927–2929)

> $\widetilde{S}$ is contained in a connected component $\Omega$ of $\Omega(A)$ […] every
> lightlike geodesic contained in $\widetilde{M}$ intersect $\widetilde{S}$ […] It follows that
> ${\mathcal D}(\widetilde{M})$ is contained in $\Omega$, i.e., that $M$ can be embedded in the
> unipotent spacetime $\Gamma\backslash\Omega$. (l.3120–3127)

## Proof

`Ω := {p | α < y(φ p) − y₀ < β}` (convex, open). (a) `W ⊆ Ω`: the null line `p + s v`,
`v = L(φ)⁻¹ v₀`, keeps `y(φ ·)`. (b) For `γ ∈ Γ''`, `φγφ⁻¹` acts on `𝒰 × 𝒰^⊥` by
`(φ₁ a_t φ₁⁻¹, L)`; `𝒰^⊥` has `y = 0`, so `y(φ ·)` is `Γ''`-invariant; `γ ↦ t` is injective
(`φγφ⁻¹ = id` on `𝒰`, which meets `φ Σ`, forces `γ = 1` by freeness). (c) For `γ ≠ 1`,
`|γ p − p|² ≥ |a_t x − x|² = ∑ tᵢ²(1 + yℓᵢ)² > 0` on `Ω`; nonspacelike elliptic is excluded
(`CCAction.not_isNonspacelikeElliptic`); for linear parabolic `γ`, `L(γ) v = v`
(`lin_fix_of_minkB`) and a fixed point on `p + v^⊥` would lie in `Ω`; so `Ω ⊆ U(Γ'') = U(Γ)`
(`UGamma_eq_of_index`) and `Ω ⊆ Ω(S̃)` (`omegaS_eq`, `Ω` connected, `Σ ⊆ Ω`). (d) Properness
from `exists_bound_unipAction` and `BallFinite L`. (e)–(f) `B = toFlatSpacetime Γ'' Ω`,
`ι' = φ⁻¹ ∘ ι`, `suspendre`; `ι'.restrictGroup Γ'' = φ₁ ΓA φ₁⁻¹`, `ι'⁻¹ Ω = φ₁(]α, β[-slab)`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `Σ ⊆ Ω(S̃)`, (CC′), `Γ` free proper on `Σ` (§8) | ✓ carried (`hcc : CCAction Γ St`) |
| `Γ''` of finite index (Rem 8.8) | ✓ carried (`hidx`) |
| `𝒟(M̃)` swept by null lines meeting `S̃` (l.3123–3125) | ✓ carried as `hD` on `W` |
| `Γ` restricted to `𝒰` is a discrete group of `A` (l.2904–2932) | ✓ carried (`hres`, `hH`, `hA`, `hA'`, `hL`) |
| `S̃` in a component of `Ω(A)` (l.3120–3122) | ✓ carried (`hαβ`, `hSt`) |

## SCOPE (disclosed)

* `Ω` is the slab `π_𝒰⁻¹(Ω_A)` read in the frame; that it is `Ω(S̃)` itself is not claimed.
* `set_option maxHeartbeats 1000000` on the main theorem (one long assembly).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal.Flat.Nonlox.ULTP

open Set Function TopologicalSpace Topology Filter

variable {d : ℕ}

theorem nullY_add (p q : Minkowski (d + 1)) : nullY (p + q) = nullY p + nullY q := by
  simp only [nullY, Prod.fst_add, Prod.snd_add, PiLp.add_apply]; ring

theorem nullY_sub (p q : Minkowski (d + 1)) : nullY (p - q) = nullY p - nullY q := by
  simp only [nullY, Prod.fst_sub, Prod.snd_sub, PiLp.sub_apply]; ring

theorem nullY_smul (c : ℝ) (p : Minkowski (d + 1)) : nullY (c • p) = c * nullY p := by
  simp only [nullY, Prod.smul_fst, Prod.smul_snd, PiLp.smul_apply, smul_eq_mul]; ring

theorem nullX_sub (p q : Minkowski (d + 1)) : nullX (p - q) = nullX p - nullX q := by
  simp only [nullX, Prod.fst_sub, Prod.snd_sub, PiLp.sub_apply]; ring

theorem nullZ_sub (p q : Minkowski (d + 1)) (i : Fin d) : nullZ (p - q) i = nullZ p i - nullZ q i := by
  simp [nullZ]

theorem ofNull_null (p : Minkowski (d + 1)) : ofNull (nullX p) (nullY p) (nullZ p) = p :=
  eq_of_null (nullX_ofNull _ _ _) (nullY_ofNull _ _ _) fun i => by rw [nullZ_ofNull]

theorem ofNull_zero : (ofNull 0 0 0 : Minkowski (d + 1)) = 0 :=
  eq_of_null (by rw [nullX_ofNull]; simp [nullX]) (by rw [nullY_ofNull]; simp [nullY])
    fun i => by rw [nullZ_ofNull]; simp [nullZ]

theorem nullY_eq_minkB (p : Minkowski (d + 1)) : nullY p = minkB p (ofNull 1 0 0) := by
  simp [nullY, minkB, ofNull, PiLp.inner_apply, Fin.sum_univ_succ]
  ring

theorem minkQ_ofNull_one : minkQ (ofNull 1 0 0 : Minkowski (d + 1)) = 0 := by
  rw [minkQ_eq_null, nullY_ofNull, nullZ_ofNull]; simp

theorem ofNull_one_ne_zero : (ofNull 1 0 0 : Minkowski (d + 1)) ≠ 0 := fun h => by
  have := nullX_ofNull (d := d) 1 0 0
  rw [h] at this; simp [nullX] at this

theorem minkQ_unipAction_sub {d₁ : ℕ} (ℓ : Fin d₁ → ℝ) (t : EuclideanSpace ℝ (Fin d₁))
    (x : Minkowski (d₁ + 1)) :
    minkQ (unipAction ℓ t x - x) = ∑ i, (t i * (1 + nullY x * ℓ i)) ^ 2 := by
  rw [minkQ_eq_null, nullY_sub, nullY_unipAction, sub_self, mul_zero, zero_add,
    EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.norm_eq_abs, sq_abs, nullZ_sub]
  simp [unipAction, nullZ_ofNull]

theorem nullZ_unipAction {d₁ : ℕ} (ℓ : Fin d₁ → ℝ) (t : EuclideanSpace ℝ (Fin d₁))
    (x : Minkowski (d₁ + 1)) (i : Fin d₁) :
    nullZ (unipAction ℓ t x) i = nullZ x i + t i * (1 + nullY x * ℓ i) := by
  simp [unipAction, nullZ_ofNull]

theorem unipAction_zero {d₁ : ℕ} (ℓ : Fin d₁ → ℝ) (x : Minkowski (d₁ + 1)) :
    unipAction ℓ 0 x = x := by
  conv_rhs => rw [← ofNull_null x]
  simp [unipAction]

theorem minkB_nondeg {e : Minkowski d} (h : ∀ z, minkB z e = 0) : e = 0 := by
  have := h (-e.1, e.2)
  simp only [minkB, real_inner_self_eq_norm_sq] at this
  have h1 : e.1 = 0 := by nlinarith [sq_nonneg e.1, sq_nonneg ‖e.2‖]
  have h2 : ‖e.2‖ = 0 := by nlinarith [sq_nonneg e.1, sq_nonneg ‖e.2‖]
  exact Prod.ext h1 (norm_eq_zero.1 h2)

theorem lin_fix_of_minkB {A : Minkowski d ≃ₗ[ℝ] Minkowski d} (hA : A ∈ lorentz d)
    {v : Minkowski d} (h : ∀ w, minkB (A w) v = minkB w v) : A v = v := by
  have key : ∀ z, minkB z (A v - v) = 0 := fun z => by
    obtain ⟨w, rfl⟩ := A.surjective z
    rw [minkB_sub_right, minkB_map (lorentz.minkQ_apply hA), h, sub_self]
  exact sub_eq_zero.1 (minkB_nondeg key)


theorem sum_sq_mul_pos {n : ℕ} {t : EuclideanSpace ℝ (Fin n)} (ht : t ≠ 0) {c : Fin n → ℝ}
    (hc : ∀ i, c i ≠ 0) : 0 < ∑ i, (t i * c i) ^ 2 := by
  obtain ⟨i, hi⟩ : ∃ i, t i ≠ 0 := by
    by_contra h; push Not at h; exact ht (by ext i; simp [h i])
  have hm := mul_ne_zero hi (hc i)
  exact lt_of_lt_of_le (by positivity)
    (Finset.single_le_sum (f := fun i => (t i * c i) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i))

/-- **The displacement of `a_t` bounds `t`** on a compact set of the slab: if `a_t k ∈ K'` for some
`k ∈ K`, then `‖t‖ ≤ R`, because `Δz = t ⊙ (1 + yℓ)` and `|1 + yℓᵢ|` is bounded below on `K`. -/
theorem exists_bound_unipAction {d₁ : ℕ} {ℓ : Fin d₁ → ℝ} {α β : EReal}
    (hαβ : IsUnipComponent ℓ α β) {K K' : Set (Minkowski (d₁ + 1))} (hK : IsCompact K)
    (hK' : IsCompact K') (hKd : K ⊆ unipDomain (d := d₁) α β) :
    ∃ R : ℝ, ∀ k ∈ K, ∀ t : EuclideanSpace ℝ (Fin d₁), unipAction ℓ t k ∈ K' → ‖t‖ ≤ R := by
  obtain ⟨MK, hMK⟩ := hK.exists_bound_of_continuousOn (continuous_nullZ (d := d₁)).continuousOn
  obtain ⟨ML, hML⟩ := hK'.exists_bound_of_continuousOn (continuous_nullZ (d := d₁)).continuousOn
  have hne : ∀ x ∈ K, ∀ i, 1 + nullY x * ℓ i ≠ 0 := fun x hx i =>
    hαβ.2.1 _ (hKd hx).1 (hKd hx).2 i
  have hC : ∀ i, ∃ C : ℝ, ∀ x ∈ K, ‖(1 + nullY x * ℓ i)⁻¹‖ ≤ C := fun i =>
    hK.exists_bound_of_continuousOn (ContinuousOn.inv₀
      ((continuous_const.add ((continuous_nullY (d := d₁)).mul continuous_const)).continuousOn)
      fun x hx => hne x hx i)
  choose C hC using hC
  refine ⟨√(∑ i, ((ML + MK) * C i) ^ 2), fun k hk t hkt => ?_⟩
  have hti : ∀ i, ‖t i‖ ≤ (ML + MK) * C i := fun i => by
    have e : t i = (nullZ (unipAction ℓ t k) i - nullZ k i) * (1 + nullY k * ℓ i)⁻¹ := by
      rw [nullZ_unipAction, add_sub_cancel_left, mul_assoc, mul_inv_cancel₀ (hne k hk i), mul_one]
    rw [e, norm_mul]
    have h1 : ‖nullZ (unipAction ℓ t k) i - nullZ k i‖ ≤ ML + MK :=
      (norm_sub_le _ _).trans (add_le_add ((PiLp.norm_apply_le _ i).trans (hML _ hkt))
        ((PiLp.norm_apply_le _ i).trans (hMK _ hk)))
    exact mul_le_mul h1 (hC i k hk) (norm_nonneg _) ((norm_nonneg _).trans h1)
  rw [EuclideanSpace.norm_eq]
  exact Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ =>
    pow_le_pow_left₀ (norm_nonneg _) (hti i) 2)

section Embedding

variable {d₁ : ℕ} {J : EuclideanSpace ℝ (Fin d₁) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)}
  {z₀ : EuclideanSpace ℝ (Fin d)} {y₀ : ℝ} {ι : AffineMinkEmbedding (d₁ + 1) (d + 1)}

theorem nullY_apply (hι : ∀ x y z, ι (ofNull x y z) = ofNull x (y + y₀) (z₀ + J z))
    (x : Minkowski (d₁ + 1)) : nullY (ι x) = nullY x + y₀ := by
  have := hι (nullX x) (nullY x) (nullZ x)
  rw [ofNull_null] at this
  rw [this, nullY_ofNull]

theorem lin_ofNull_one (hι : ∀ x y z, ι (ofNull x y z) = ofNull x (y + y₀) (z₀ + J z)) :
    ι.lin (ofNull 1 0 0) = ofNull 1 0 0 := by
  have h0 : ι 0 = ofNull 0 y₀ z₀ := by
    rw [← ofNull_zero, hι]; simp
  have h1 : ι (ofNull 1 0 0) = ofNull 1 y₀ z₀ := by
    rw [hι]; simp
  have e := ι.apply_eq (ofNull 1 0 0)
  rw [h0, h1] at e
  have e' : ι.lin (ofNull 1 0 0) = ofNull 1 y₀ z₀ - ofNull 0 y₀ z₀ := by rw [e]; abel
  rw [e']
  refine eq_of_null ?_ ?_ fun i => ?_
  · rw [nullX_sub]; simp [nullX_ofNull]
  · rw [nullY_sub]; simp [nullY_ofNull]
  · rw [nullZ_sub]; simp [nullZ_ofNull]

theorem nullY_eq_zero_of_mem_perp (hι : ∀ x y z, ι (ofNull x y z) = ofNull x (y + y₀) (z₀ + J z))
    {w : Minkowski (d + 1)} (hw : w ∈ ι.perp) : nullY w = 0 := by
  rw [nullY_eq_minkB, ← lin_ofNull_one hι]; exact hw _

theorem nullY_eq_retract (hι : ∀ x y z, ι (ofNull x y z) = ofNull x (y + y₀) (z₀ + J z))
    (q : Minkowski (d + 1)) : nullY q = nullY (ι.retract q) + y₀ := by
  have e := ι.apply_retract_add q
  conv_lhs => rw [← e]
  rw [nullY_add, nullY_apply hι, nullY_eq_zero_of_mem_perp hι (ι.sub_apply_retract_mem_perp q),
    add_zero]

theorem minkQ_pos_of_restricts (hι : ∀ x y z, ι (ofNull x y z) = ofNull x (y + y₀) (z₀ + J z))
    {G : isom (d + 1)} {φ₁ a : isom (d₁ + 1)} {ℓ : Fin d₁ → ℝ} {t : EuclideanSpace ℝ (Fin d₁)}
    (hR : ι.Restricts G (φ₁ * a * φ₁⁻¹)) (ha : ∀ p, a • p = unipAction ℓ t p)
    (hφ₁ : ∀ x : Minkowski (d₁ + 1), nullY (φ₁⁻¹ • x) = nullY x) (ht : t ≠ 0) (q : Minkowski (d + 1))
    (hc : ∀ i, 1 + (nullY q - y₀) * ℓ i ≠ 0) : 0 < minkQ (G • q - q) := by
  have hw := ι.sub_apply_retract_mem_perp q
  have e := hR.smul_apply_add (ι.retract q) (q - ι (ι.retract q))
  rw [ι.apply_retract_add] at e
  have hdec : G • q - q = ι.lin ((φ₁ * a * φ₁⁻¹) • ι.retract q - ι.retract q) +
      ((G : Minkowski (d + 1) ≃ᵃ[ℝ] Minkowski (d + 1)).linear (q - ι (ι.retract q)) -
        (q - ι (ι.retract q))) := by
    rw [e, ← ι.apply_sub]; abel
  have hw' := ι.sub_mem_perp (hR.linear_mem_perp hw) hw
  rw [hdec, minkQ_add, minkB_comm, hw' _, mul_zero, add_zero, ι.minkQ_lin]
  have hu : minkQ ((φ₁ * a * φ₁⁻¹) • ι.retract q - ι.retract q) =
      ∑ i, (t i * (1 + nullY (φ₁⁻¹ • ι.retract q) * ℓ i)) ^ 2 := by
    rw [mul_smul, mul_smul, ha]
    have := isom_minkQ_sub φ₁ (φ₁⁻¹ • ι.retract q) (unipAction ℓ t (φ₁⁻¹ • ι.retract q))
    rw [smul_inv_smul] at this
    rw [this, minkQ_unipAction_sub]
  have hy : nullY (φ₁⁻¹ • ι.retract q) = nullY q - y₀ := by
    have := nullY_eq_retract hι q
    rw [hφ₁, this]; ring
  rw [hu, hy]
  have := sum_sq_mul_pos ht hc
  linarith [ι.minkQ_nonneg_of_mem_perp hw']

end Embedding

end Causal.Flat.Nonlox.ULTP

namespace Causal.Flat.Nonlox

open Set Function TopologicalSpace Topology Filter
open scoped Pointwise
open ULTP FlatQuotient

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
/-- **[9.A], item (7)** (l.3120–3127, with Lemma 5.5 and l.2904–2932): in the null frame `φ`,
the slab `Ω = {α < y(φ ·) − y₀ < β}` contains `W` (the points swept by the null lines of `Σ`),
lies in `Ω(S̃)`, carries a free properly discontinuous action of `Γ''` with quotient `B`, and `B`
is a linear twisted product over a unipotent spacetime. -/
theorem exists_unipotent_ltp_of_frame {Γ Γ'' : Subgroup (isom (d + 1))}
    {St W : Set (Minkowski (d + 1))} (hcc : CCAction Γ St) (hle : Γ'' ≤ Γ)
    (hidx : Γ''.relIndex Γ ≠ 0) (φ : isom (d + 1))
    (hD : ∀ p ∈ W, ∃ s : ℝ, p + s • (linOf φ).symm (ofNull 1 0 0) ∈ St)
    {d₁ : ℕ} (J : EuclideanSpace ℝ (Fin d₁) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (z₀ : EuclideanSpace ℝ (Fin d)) (y₀ : ℝ) (ι : AffineMinkEmbedding (d₁ + 1) (d + 1))
    (hι : ∀ x y z, ι (ofNull x y z) = ofNull x (y + y₀) (z₀ + J z)) (hιo : ι.Orthochronous)
    (hres : ι.RestrictsIn (frameConj φ Γ''))
    {φ₁ : isom (d₁ + 1)} {ℓ : Fin d₁ → ℝ} {α β : EReal}
    {L : AddSubgroup (EuclideanSpace ℝ (Fin d₁))} {ΓA : Subgroup (isom (d₁ + 1))}
    (hL : BallFinite L) (hαβ : IsUnipComponent ℓ α β)
    (hA : ∀ γ ∈ ΓA, ∃ t ∈ L, ∀ p, γ • p = unipAction ℓ t p)
    (hA' : ∀ t ∈ L, ∃ γ ∈ ΓA, ∀ p, γ • p = unipAction ℓ t p)
    (hH : ι.restrictGroup (frameConj φ Γ'') = frameConj φ₁ ΓA)
    (hφ₁ : ∀ p : Minkowski (d₁ + 1), nullY (φ₁ • p) = nullY p)
    (hSt : ∀ p ∈ St, α < ((nullY (φ • p) - y₀ : ℝ) : EReal) ∧
      ((nullY (φ • p) - y₀ : ℝ) : EReal) < β) :
    ∃ Ω : TopologicalSpace.Opens (Minkowski (d + 1)), W ⊆ Ω ∧
      (Ω : Set (Minkowski (d + 1))) ⊆ omegaS Γ St ∧
      ∃ B : FlatSpacetime.{0} (d + 1), IsQuotientOf B Γ'' Ω ∧
        ∃ M₁ : FlatSpacetime.{0} (d₁ + 1), IsUnipotentSpacetime M₁ ∧ IsLTPOver B M₁ := by
  /- the structure of `Γ''`: each `γ` restricts through `ι` to `φ₁ a φ₁⁻¹`, `a = a_t` -/
  have hconjmem : ∀ γ ∈ Γ'', φ * γ * φ⁻¹ ∈ frameConj φ Γ'' := fun γ hγ =>
    Subgroup.mem_map.2 ⟨γ, hγ, by simp [MulAut.conj_apply]⟩
  have hkey : ∀ γ, γ ∈ Γ'' → ∃ a ∈ ΓA, ∃ t ∈ L, (∀ p, a • p = unipAction ℓ t p) ∧
      ι.Restricts (φ * γ * φ⁻¹) (φ₁ * a * φ₁⁻¹) := by
    intro γ hγ
    obtain ⟨g, hg⟩ := hres _ (hconjmem γ hγ)
    have hgm : g ∈ ι.restrictGroup (frameConj φ Γ'') := ⟨_, hconjmem γ hγ, hg⟩
    rw [hH] at hgm
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hgm
    obtain ⟨t, ht, hat⟩ := hA a ha
    exact ⟨a, ha, t, ht, hat, by simpa [MulAut.conj_apply] using hg⟩
  choose! Aγ hAγ T hT hTact hTres using hkey
  have hφ₁' : ∀ x, nullY (φ₁⁻¹ • x) = nullY x := fun x => by rw [← hφ₁ (φ₁⁻¹ • x), smul_inv_smul]
  have hg_smul : ∀ γ ∈ Γ'', ∀ x, (φ₁ * Aγ γ * φ₁⁻¹) • x = φ₁ • unipAction ℓ (T γ) (φ₁⁻¹ • x) :=
    fun γ hγ x => by rw [mul_smul, mul_smul, hTact γ hγ]
  have hconj_smul : ∀ (γ : isom (d + 1)) (p : Minkowski (d + 1)), (φ * γ * φ⁻¹) • (φ • p) = φ • (γ • p) := by
    intro γ p; rw [mul_smul, mul_smul, inv_smul_smul]
  /- a point of `Σ` on `φ⁻¹ U` -/
  have hU1 : IsFutureTimelike (ι.lin (1, 0)) := ⟨hιo, by rw [ι.minkQ_lin_timeVec]; norm_num⟩
  have hu : IsFutureTimelike ((linOf φ).symm (ι.lin (1, 0))) := by
    rw [← lorentz.isFutureTimelike_apply_iff (linOf_mem φ), linOf_symm_apply]; exact hU1
  obtain ⟨s₀, hs₀⟩ := hcc.cc.entire.meets (φ⁻¹ • ι 0) _ hu
  have hφp₀ : φ • (φ⁻¹ • ι 0 + s₀ • (linOf φ).symm (ι.lin (1, 0))) = ι (s₀ • (1, 0)) := by
    rw [isom_smul_add_smul, smul_inv_smul, linOf_symm_apply, ι.apply_eq (s₀ • (1, 0)), map_smul]
    abel
  /- the restriction `γ ↦ g` is injective -/
  have hinj : ∀ γ ∈ Γ'', (∀ x, (φ * γ * φ⁻¹) • ι x = ι x) → γ = 1 := by
    intro γ hγ hfix
    by_contra h1
    apply hcc.free γ (hle hγ) h1 _ hs₀
    have := hfix (s₀ • (1, 0))
    rw [← hφp₀, hconj_smul] at this
    exact MulAction.injective φ this
  have hT0 : ∀ γ ∈ Γ'', γ ≠ 1 → T γ ≠ 0 := by
    intro γ hγ h1 ht
    apply h1
    refine hinj γ hγ fun x => ?_
    rw [← hTres γ hγ x, hg_smul γ hγ, ht, unipAction_zero, smul_inv_smul]
  have hTinj : ∀ γ ∈ Γ'', ∀ γ' ∈ Γ'', T γ = T γ' → γ = γ' := by
    intro γ hγ γ' hγ' h
    have hg : φ₁ * Aγ γ * φ₁⁻¹ = φ₁ * Aγ γ' * φ₁⁻¹ := Subtype.ext (AffineEquiv.ext fun x => by
      show (φ₁ * Aγ γ * φ₁⁻¹) • x = (φ₁ * Aγ γ' * φ₁⁻¹) • x
      rw [hg_smul γ hγ, hg_smul γ' hγ', h])
    have := hinj (γ⁻¹ * γ') (Γ''.mul_mem (Γ''.inv_mem hγ) hγ') fun x => by
      rw [show φ * (γ⁻¹ * γ') * φ⁻¹ = (φ * γ * φ⁻¹)⁻¹ * (φ * γ' * φ⁻¹) by group, mul_smul,
        ← hTres γ' hγ' x, ← hg, hTres γ hγ x, inv_smul_smul]
    exact (inv_mul_eq_one.1 this)
  have hY1 : ∀ γ ∈ Γ'', ∀ q : Minkowski (d + 1), nullY ((φ * γ * φ⁻¹) • q) = nullY q := by
    intro γ hγ q
    have h1 := nullY_eq_retract hι ((φ * γ * φ⁻¹) • q)
    have h2 := (hTres γ hγ).retract_smul q
    have h3 := hg_smul γ hγ (ι.retract q)
    have h4 := nullY_eq_retract hι q
    rw [h1, h2, h3, h4, hφ₁, nullY_unipAction, hφ₁']
  have hY : ∀ γ ∈ Γ'', ∀ p, nullY (φ • (γ • p)) = nullY (φ • p) := fun γ hγ p => by
    rw [← hconj_smul, hY1 γ hγ]
  /- achronality: `|γ p − p|² > 0` on the slab -/
  have hQ : ∀ γ ∈ Γ'', γ ≠ 1 → ∀ p : Minkowski (d + 1), α < ((nullY (φ • p) - y₀ : ℝ) : EReal) →
      ((nullY (φ • p) - y₀ : ℝ) : EReal) < β → 0 < minkQ (γ • p - p) := by
    intro γ hγ h1 p hpα hpβ
    rw [← isom_minkQ_sub φ p (γ • p), ← hconj_smul γ p]
    exact minkQ_pos_of_restricts hι (hTres γ hγ) (hTact γ hγ) hφ₁' (hT0 γ hγ h1) _
      (hαβ.2.1 _ hpα hpβ)
  /- the open set `Ω`: a null slab of the frame -/
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : Minkowski (d + 1), c₀ = ofNull 0 y₀ (0 : EuclideanSpace ℝ (Fin d)) :=
    ⟨_, rfl⟩
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : isom (d + 1), ψ = isomTrans (-c₀) * φ := ⟨_, rfl⟩
  have hψ : ∀ p : Minkowski (d + 1), nullY (ψ • p) = nullY (φ • p) - y₀ := fun p => by
    have e : ψ • p = -c₀ + φ • p := by rw [hψdef, mul_smul]; rfl
    rw [e, nullY_add, show -c₀ = (-1 : ℝ) • c₀ by simp, nullY_smul, hc₀, nullY_ofNull]; ring
  let Ω : Opens (Minkowski (d + 1)) :=
    ⟨(fun p : Minkowski (d + 1) => ψ • p) ⁻¹' (unipDomain (d := d) α β : Set (Minkowski (d + 1))),
      (unipDomain (d := d) α β).isOpen.preimage (continuous_const_smul ψ)⟩
  have hmemΩ : ∀ p : Minkowski (d + 1), p ∈ Ω ↔ α < ((nullY (φ • p) - y₀ : ℝ) : EReal) ∧
      ((nullY (φ • p) - y₀ : ℝ) : EReal) < β := fun p => by
    show α < ((nullY (ψ • p) : ℝ) : EReal) ∧ ((nullY (ψ • p) : ℝ) : EReal) < β ↔ _
    rw [hψ]
  have hconv : Convex ℝ (Ω : Set (Minkowski (d + 1))) :=
    (convex_unipDomain (d := d) (α := α) (β := β)).affine_preimage
      (ψ : Minkowski (d + 1) ≃ᵃ[ℝ] Minkowski (d + 1)).toAffineMap
  obtain ⟨x₀, hx₀⟩ := hcc.nonempty
  have hx₀Ω : x₀ ∈ Ω := (hmemΩ x₀).2 (hSt x₀ hx₀)
  have hΩc : IsConnected (Ω : Set (Minkowski (d + 1))) := hconv.isConnected ⟨x₀, hx₀Ω⟩
  /- the null direction `v = L(φ)⁻¹ v₀` -/
  obtain ⟨v, hv⟩ : ∃ v : Minkowski (d + 1), v = (linOf φ).symm (ofNull 1 0 0) := ⟨_, rfl⟩
  have hBv : ∀ x y : Minkowski (d + 1), minkB (x - y) v = nullY (φ • x) - nullY (φ • y) := by
    intro x y
    rw [← nullY_sub, smul_sub_smul, nullY_eq_minkB, ← minkB_linOf φ (x - y) v, hv, linOf_symm_apply]
  have hv0 : v ≠ 0 := fun h => ofNull_one_ne_zero (d := d) (by
    rw [← linOf_symm_apply φ (ofNull 1 0 0), ← hv, h, map_zero])
  have hvq : minkQ v = 0 := by rw [hv, minkQ_linOf_symm, minkQ_ofNull_one]
  have hfixv : ∀ γ ∈ Γ'', linOf γ v = v := fun γ hγ => lin_fix_of_minkB (linOf_mem γ) fun w => by
    have h1 := hBv (γ • w) (γ • (0 : Minkowski (d + 1)))
    have h2 := hBv w 0
    rw [hY γ hγ w, hY γ hγ 0, ← h2, smul_sub_smul, sub_zero] at h1
    exact h1
  /- (a) `W ⊆ Ω` -/
  have hWΩ : W ⊆ Ω := by
    intro p hp
    obtain ⟨s, hs⟩ := hD p hp
    rw [← hv] at hs
    have e : nullY (φ • (p + s • v)) = nullY (φ • p) := by
      have := hBv (p + s • v) p
      rw [add_sub_cancel_left, minkB_smul_left, ← minkQ_eq_minkB, hvq, mul_zero] at this
      linarith
    exact (hmemΩ p).2 (by rw [← e]; exact hSt _ hs)
  /- (c) `Ω ⊆ U(Γ'') = U(Γ)`, hence `Ω ⊆ Ω(S̃)` -/
  have hΩU : (Ω : Set (Minkowski (d + 1))) ⊆ UGamma Γ'' := by
    intro p hp γ hγ h1
    obtain ⟨hpα, hpβ⟩ := (hmemΩ p).1 hp
    unfold Ug
    split_ifs with hN hLP
    · exact (hcc.not_isNonspacelikeElliptic (hle hγ) h1 hN).elim
    · intro hmem
      rw [mem_nullHyperplanes_iff hLP.1 hv0 hvq (hfixv γ hγ)] at hmem
      obtain ⟨c, hc, hB⟩ := hmem
      have hcY : nullY (φ • c) = nullY (φ • p) := by have := hBv p c; linarith
      have := hQ γ hγ h1 c (by rw [hcY]; exact hpα) (by rw [hcY]; exact hpβ)
      rw [hc, sub_self, minkQ_zero] at this
      exact lt_irrefl _ this
    · intro q hq
      exact hQ _ (zpow_mem hγ q) (hcc.zpow_ne_one (hle hγ) h1 hq) p hpα hpβ
  have htf : ∀ γ ∈ Γ, γ ≠ 1 → ∀ n : ℕ, 0 < n → γ ^ n ≠ 1 := fun γ hγ h1 n hn =>
    hcc.pow_ne_one hγ h1 hn
  have hΩG : (Ω : Set (Minkowski (d + 1))) ⊆ omegaGamma Γ := by
    rw [omegaGamma, ← UGamma_eq_of_index hle hidx htf]
    exact interior_maximal hΩU Ω.isOpen
  have hΩS : (Ω : Set (Minkowski (d + 1))) ⊆ omegaS Γ St := by
    rw [omegaS_eq hcc hx₀]; exact hΩc.isPreconnected.subset_connectedComponentIn hx₀Ω hΩG
  /- (b) invariance, freeness; (d) proper discontinuity -/
  haveI hinv : Invariant Γ'' Ω :=
    ⟨fun γ p hp => (hmemΩ _).2 (by rw [hY γ γ.2]; exact (hmemΩ p).1 hp)⟩
  haveI hfree : IsCancelSMul Γ'' Ω := by
    rw [isCancelSMul_iff_eq_one_of_smul_eq]
    intro γ x hx
    by_contra h1
    have hx' : (γ : isom (d + 1)) • (x : Minkowski (d + 1)) = x := congrArg Subtype.val hx
    obtain ⟨h2, h3⟩ := (hmemΩ x).1 x.2
    have := hQ γ γ.2 (fun e => h1 (Subtype.ext e)) x h2 h3
    rw [hx', sub_self, minkQ_zero] at this
    exact lt_irrefl _ this
  haveI hprop : ProperlyDiscontinuousSMul Γ'' Ω := by
    refine ⟨fun {K K'} hK hK' => ?_⟩
    obtain ⟨F, hFdef⟩ : ∃ F : Ω → Minkowski (d₁ + 1),
        F = fun p : Ω => φ₁⁻¹ • ι.retract (φ • (p : Minkowski (d + 1))) := ⟨_, rfl⟩
    have hF : Continuous F := by
      rw [hFdef]
      exact (continuous_const_smul _).comp (ι.continuous_retract.comp
        ((continuous_const_smul _).comp continuous_subtype_val))
    have hFY : ∀ p : Ω, nullY (F p) = nullY (φ • (p : Minkowski (d + 1))) - y₀ := fun p => by
      have := nullY_eq_retract hι (φ • (p : Minkowski (d + 1)))
      rw [hFdef]; dsimp only
      rw [hφ₁', this]; ring
    have hFdom : F '' K ⊆ unipDomain (d := d₁) α β := by
      rintro _ ⟨p, -, rfl⟩
      show α < ((nullY (F p) : ℝ) : EReal) ∧ ((nullY (F p) : ℝ) : EReal) < β
      rw [hFY]; exact (hmemΩ p).1 p.2
    obtain ⟨R, hR⟩ := exists_bound_unipAction hαβ (hK.image hF) (hK'.image hF) hFdom
    have hFγ : ∀ (γ : Γ'') (p : Ω), F (γ • p) = unipAction ℓ (T γ) (F p) := by
      intro γ p
      rw [hFdef]; dsimp only
      rw [coe_smul, ← hconj_smul, (hTres γ γ.2).retract_smul, hg_smul γ γ.2, inv_smul_smul]
    refine ((hL.finite_ball R).preimage (f := fun γ : Γ'' => T γ) ?_).subset ?_
    · intro γ _ γ' _ h; exact Subtype.ext (hTinj γ γ.2 γ' γ'.2 h)
    · rintro γ ⟨_, ⟨k, hk, rfl⟩, hl⟩
      refine ⟨hT γ γ.2, hR (F k) ⟨k, hk, rfl⟩ (T γ) ?_⟩
      rw [← hFγ]; exact ⟨_, hl, rfl⟩
  /- (e) the quotient `B = Γ''\Ω` -/
  let B : FlatSpacetime.{0} (d + 1) := FlatQuotient.toFlatSpacetime Γ'' Ω hΩc
  have hB : IsQuotientOf B Γ'' Ω := FlatQuotient.isQuotientOf_toFlatSpacetime Γ'' Ω hΩc
  /- (f) the embedding `ι' = φ⁻¹ ∘ ι` of `𝒰` -/
  let ι' : AffineMinkEmbedding (d₁ + 1) (d + 1) :=
    ⟨((φ⁻¹ : isom (d + 1)) : Minkowski (d + 1) ≃ᵃ[ℝ] Minkowski (d + 1)).toAffineMap.comp
      ι.toAffineMap, fun u => by
        show minkQ (linOf φ⁻¹ (ι.lin u)) = minkQ u
        rw [lorentz.minkQ_apply (linOf_mem _), ι.minkQ_lin]⟩
  have hι' : ∀ x, ι' x = φ⁻¹ • ι x := fun x => rfl
  have hι'lin : ∀ u, ι'.lin u = linOf φ⁻¹ (ι.lin u) := fun u => rfl
  have hι'o : ι'.Orthochronous := by
    show 0 < (ι'.lin (1, 0)).1
    rw [hι'lin]; exact (lorentz.isFutureTimelike_apply (linOf_mem φ⁻¹) hU1).1
  have hres' : ι'.RestrictsIn Γ'' := fun γ hγ => ⟨φ₁ * Aγ γ * φ₁⁻¹, fun x => by
    rw [hι', hι', hTres γ hγ x, mul_smul, mul_smul, inv_smul_smul]⟩
  have hinvv : linOf φ⁻¹ (ofNull 1 0 0) = v := by
    rw [hv]; rfl
  have hperp' : ∀ w ∈ ι'.perp, ∀ p ∈ Ω, p + w ∈ Ω := by
    intro w hw p hp
    have hwv : minkB w v = 0 := by
      have := hw (ofNull 1 0 0)
      rwa [hι'lin, lin_ofNull_one hι, hinvv] at this
    have e : nullY (φ • (p + w)) = nullY (φ • p) := by
      have := hBv (p + w) p
      rw [add_sub_cancel_left, hwv] at this; linarith
    exact (hmemΩ _).2 (by rw [e]; exact (hmemΩ p).1 hp)
  have hrg : ι'.restrictGroup Γ'' = frameConj φ₁ ΓA := by
    rw [← hH]
    ext g
    simp only [AffineMinkEmbedding.mem_restrictGroup]
    constructor
    · rintro ⟨γ, hγ, hR⟩
      refine ⟨φ * γ * φ⁻¹, hconjmem γ hγ, fun x => ?_⟩
      have := congrArg (fun y => φ • y) (hR x)
      simp only [hι', smul_inv_smul] at this
      rw [this, mul_smul, mul_smul]
    · rintro ⟨G, hG, hR⟩
      obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hG
      refine ⟨γ, hγ, fun x => ?_⟩
      rw [hι', hι', hR x]
      simp [MulAut.conj_apply, mul_smul]
  have hpre : ι'.preimageOpens Ω = isomImage φ₁ (unipDomain α β) := by
    ext x
    rw [SetLike.mem_coe, SetLike.mem_coe, AffineMinkEmbedding.mem_preimageOpens, mem_isomImage,
      hmemΩ]
    show _ ↔ α < ((nullY (φ₁⁻¹ • x) : ℝ) : EReal) ∧ ((nullY (φ₁⁻¹ • x) : ℝ) : EReal) < β
    rw [hι', smul_inv_smul, nullY_apply hι, hφ₁', add_sub_cancel_right]
  refine ⟨Ω, hWΩ, hΩS, B, hB, ι'.baseSpacetime B hB hres' hperp', ?_,
    suspendre B hB ι' hι'o hres' hperp'⟩
  refine ⟨φ₁, ℓ, α, β, L, ΓA, hL, hαβ, hA, hA', ?_⟩
  have := ι'.isQuotientOf_baseSpacetime B hB hres' hperp'
  rwa [hrg, hpre] at this

end Causal.Flat.Nonlox
