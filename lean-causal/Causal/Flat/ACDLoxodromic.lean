import Causal.Flat.TitsNull
import Causal.Flat.Lox.TwoNullNormalForm
import Causal.Flat.Lox.FixLoxodromic
import Causal.Flat.Lox.SecondNullFix

/-!
# `Causal.Flat.ACDLoxodromic` — near-identity elements of a nilpotent subgroup of `SO₀(1, d)` containing a loxodromic element commute

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §5,
Theorem 5.1 (`bthm:ausl`, `GHFspace.tex:1696`), carried as the external
`AuslanderCarriereDalbo d` (`Flat/Externals`, DEC-36). **No ledger label is certified here**:
this module is the loxodromic case of Step 2 ("Lorentz Frobenius lemma, with no discreteness")
of the Lorentz Zassenhaus–Frobenius route of `docs/CARRIERE-DALBO-SURVEY.md` §2.2 T1 (DEC-121),
the case the survey flags as argued on paper only. It is reduced here to the null case
(`Flat/ACDNull`'s `commute_of_isNilpotent_of_fixNull`), taken as a hypothesis.

> Let $\Gamma$ be a discrete subgroup of $\mbox{Aff}(n, {\mathbb R})$.
> Then, the identity component $G_{0}$ of
> the closure of $L(\Gamma)$ in $GL(n, {\mathbb R})$ is nilpotent. (l.1699–1701)

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; `Minkowski d` has `d` spatial
dimensions, so Barbot's `n` is `d + 1`, and `𝒮 ≅ S^{d−1}` is `PenroseSphere d`.

## The proof

Let `N ≤ SO₀(1, d)` be nilpotent, `ℓ ∈ N` loxodromic with fixed points `u₀ ≠ u₁ ∈ 𝒮`
(`exists_fixed_pair_of_isLoxodromic`), `F = {u₀, u₁}`, and `a, b ∈ N` with `‖a − 1‖, ‖b − 1‖ < 1/2`.

1. **Every element of `N` preserves `F`** (`preservesPair_of_engel`), from the Engel condition
   `[ℓ, [ℓ, …, [ℓ, g]]] = 1` alone, backwards: if `c = ℓ x ℓ⁻¹ x⁻¹` preserves `F`, then
   `x ℓ⁻¹ x⁻¹ F = ℓ⁻¹ c F = F`, so `ℓ⁻¹ (x⁻¹ F) = x⁻¹ F`: `x⁻¹ F` is an `ℓ`-invariant pair;
   each of its points is fixed by `ℓ²`, hence lies in `F`
   (`minkB_eq_zero_of_fixed_pow_loxodromic`, `eq_or_eq_of_fixed`); so `x F = F`
   (`preservesPair_of_commutator`). No free subgroup, no ping-pong, no dynamics.
2. **A near-identity element does not swap** (`two_le_norm_of_swap`): if `g (1, u₀) = c (1, u₁)`
   and `g (1, u₁) = c' (1, u₀)`, then `c c' = 1` (`⟨(1,u₀) | (1,u₁)⟩ ≠ 0` is preserved) and
   `w = (1, u₀) − c (1, u₁) ≠ 0` has `g w = −w`, so `‖g − 1‖ ≥ 2`. Hence `a`, `b` fix `u₀`, `u₁`.
3. **Normalisation** (`exists_normalize_pairStab`): on the stabiliser `M` of `u₀` and `u₁`, each
   `A` scales `n₀ = (1, u₀)` by `λ(A) = lorentzScale A u₀ > 0` and `n₁ = (1, u₁)` by `λ(A)⁻¹`,
   `λ` is multiplicative, and the boosts
   `B_t x = x + (t − 1) (⟨x|n₀⟩/β) n₁ + (t⁻¹ − 1) (⟨x|n₁⟩/β) n₀` (`β = ⟨n₀|n₁⟩ < 0`, `t > 0`;
   `B_t ∈ SO₀(1, d)` by `mem_lorentz_of_future` at `n₀ + n₁` and `det_eq_one_of_eq_sq` with
   `B_{√t}`, `B_s B_t = B_{st}`) commute with `M`; `A ↦ B_{λ(A)} A` (Barbot's `B_{−α(A)} A` in
   the multiplicative parameter) is a homomorphism `φ` onto a group fixing `v₀ = (1, u₀)` exactly, with
   `ρ(φ A) = ρ(A)` for `ρ = screenRot v₀` (`B_s` moves `v₀^⊥` along `ℝ v₀`, which `π` kills), and
   `φ A`, `φ B` commuting forces `A`, `B` to commute.
4. **Conclusion.** `φ(N ∩ M)` is nilpotent and fixes `v₀`; `‖ρ(φ a) − 1‖ = ‖ρ(a) − 1‖ ≤ ‖a − 1‖ < 1/2`
   (hypothesis `hρ`, `Flat/ACDNull`'s `norm_screenRot_sub_one_le`), likewise for `b`; the null
   case (hypothesis `hNull`) gives `φ a φ b = φ b φ a`, hence `a b = b a`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| (route) `N ≤ SO₀(1, n−1)` nilpotent | ✓ carried: `N : Subgroup (lorentz d)`, `Group.IsNilpotent N` |
| (route) `N` contains a loxodromic element | ✓ carried: `ℓ ∈ N`, `IsLoxodromic ℓ` |
| (route) `a`, `b` near `1` | ✓ carried: `‖a − 1‖ < 1/2`, `‖b − 1‖ < 1/2` (operator norm); uniform in `N` |
| (route) the null case of Step 2 | ✓ carried as hypotheses `hNull`, `hρ`, verbatim the statements of `Flat/ACDNull`'s `commute_of_isNilpotent_of_fixNull` and `norm_screenRot_sub_one_le` |
| `Γ` discrete | ⚠ weakened: not used (Step 2 is discreteness-free) |

## SCOPE (disclosed)

* The loxodromic case of Step 2 only, relative to the null case (`hNull`, `hρ`), which the
  assembly discharges with `Flat/ACDNull`. The survey's sketch ("`N ≤ A × M`, Frobenius on the
  complement of the axis plane") is replaced by the normalisation of step 3, so that the only
  Frobenius argument is the screen one of `Flat/TitsNull`.
* Sorry-free and axiom-free (prover, 2026-11-03; `#print axioms` gives `propext`,
  `Classical.choice`, `Quot.sound` only). The statements of the planner's skeleton are unchanged;
  the boost machinery of step 3 is `private` (`acdlBoost`, `acdlNormalize`), and the Engel lemma
  `lox_exists_iterate_eq_one` is a private copy, so that this module does not import `Flat/ACDNull`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
DEC-121 (`docs/CARRIERE-DALBO-SURVEY.md` §2.2, T1 Step 2, loxodromic case).
-/

namespace Causal.Flat

open Set Function Topology Module Submodule

variable {d : ℕ}

/-- `g` preserves the pair `{u₀, u₁}` of `𝒮`: it fixes both points or swaps them. -/
def PreservesPair (g : lorentz d) (u₀ u₁ : PenroseSphere d) : Prop :=
  (lorentzSphere g u₀ = u₀ ∧ lorentzSphere g u₁ = u₁) ∨
    (lorentzSphere g u₀ = u₁ ∧ lorentzSphere g u₁ = u₀)

/-- Nilpotent groups are Engel (local copy; the public one is `Flat/ACDNull`'s
`exists_iterate_commutator_eq_one_of_isNilpotent`, not imported here). -/
private theorem lox_exists_iterate_eq_one {G : Type*} [Group G] [Group.IsNilpotent G] (a b : G) :
    ∃ n : ℕ, (fun x => a * x * a⁻¹ * x⁻¹)^[n] b = 1 := by
  have key : ∀ n : ℕ, (fun x => a * x * a⁻¹ * x⁻¹)^[n] b ∈ (⊤ : Subgroup G).lowerCentralSeries n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [iterate_succ_apply', Subgroup.lowerCentralSeries_succ]
      have h := Subgroup.commutator_mem_commutator ih (Subgroup.mem_top a)
      have h' := Subgroup.inv_mem _ h
      rw [commutatorElement_inv] at h'
      simpa [commutatorElement_def] using h'
  obtain ⟨n, hn⟩ := (Subgroup.nilpotent_iff_lowerCentralSeries).1 (inferInstance : Group.IsNilpotent G)
  exact ⟨n, by simpa [hn] using key n⟩

/-- A loxodromic element of `SO₀(1, d)` has two distinct fixed points on `𝒮`. -/
theorem exists_fixed_pair_of_isLoxodromic {ℓ : lorentz d}
    (hlox : IsLoxodromic (ℓ : Minkowski d ≃ₗ[ℝ] Minkowski d)) :
    ∃ u₀ u₁ : PenroseSphere d, u₀ ≠ u₁ ∧ lorentzSphere ℓ u₀ = u₀ ∧ lorentzSphere ℓ u₁ = u₁ := by
  obtain ⟨R, e, e', l, -, -, -, he0, he0', hq, hq', hee', -, -, hAe, hAe', -⟩ := hlox.frame
  obtain ⟨u, c, hc, hu⟩ := Lox.exists_nullVec_eq_smul_of_null he0 hq
  have horth : minkB e (nullVec u) = 0 := by
    rw [hu, minkB_smul_right, ← minkQ_eq_minkB, hq, mul_zero]
  obtain ⟨u₁, hne, h0, h1⟩ := Lox.exists_fixed_pair_of_null_orth he0 he0' hq hq' hee' hAe hAe' horth
  exact ⟨u, u₁, hne, h0, h1⟩

private theorem acdl_sphere_one (u : PenroseSphere d) :
    lorentzSphere (1 : lorentz d) u = u :=
  lorentzSphere_eq_of_eigen (c := 1) (by simp)

private theorem acdl_sphere_mul (A B : lorentz d) (u : PenroseSphere d) :
    lorentzSphere (A * B) u = lorentzSphere A (lorentzSphere B u) := by
  have hA := (lorentzScale_pos A (lorentzSphere B u)).ne'
  have hB := (lorentzScale_pos B u).ne'
  have hAB := (lorentzScale_pos (A * B) u).ne'
  refine nullVec_injective_smul
    (c := (lorentzScale (A * B) u)⁻¹ * (lorentzScale A (lorentzSphere B u) * lorentzScale B u)) ?_
  rw [nullVec_lorentzSphere, nullVec_lorentzSphere A, nullVec_lorentzSphere B, map_smul,
    smul_smul, smul_smul, Subgroup.coe_mul, LinearEquiv.mul_apply]
  congr 1
  field_simp

private theorem acdl_sphere_inv_mul (A : lorentz d) (u : PenroseSphere d) :
    lorentzSphere A⁻¹ (lorentzSphere A u) = u := by
  rw [← acdl_sphere_mul, inv_mul_cancel, acdl_sphere_one]

private theorem acdl_sphere_injective (A : lorentz d) :
    Function.Injective (lorentzSphere A) := fun u u' h => by
  have := congrArg (lorentzSphere A⁻¹) h
  rwa [acdl_sphere_inv_mul, acdl_sphere_inv_mul] at this

private theorem acdl_fixed_inv {A : lorentz d} {u : PenroseSphere d}
    (h : lorentzSphere A u = u) : lorentzSphere A⁻¹ u = u := by
  conv_lhs => rw [← h]
  exact acdl_sphere_inv_mul A u

private theorem acdl_eq_of_minkB_eq_zero {u v : PenroseSphere d}
    (h : minkB (nullVec u) (nullVec v) = 0) : u = v := by
  by_contra hne
  exact (Lox.lox_minkB_nullVec_neg hne).ne h

private theorem acdl_preservesPair_one (u₀ u₁ : PenroseSphere d) :
    PreservesPair (1 : lorentz d) u₀ u₁ :=
  Or.inl ⟨acdl_sphere_one u₀, acdl_sphere_one u₁⟩

private theorem acdl_preservesPair_of_mem {g : lorentz d} {u₀ u₁ : PenroseSphere d}
    (hne : u₀ ≠ u₁) (h0 : lorentzSphere g u₀ = u₀ ∨ lorentzSphere g u₀ = u₁)
    (h1 : lorentzSphere g u₁ = u₀ ∨ lorentzSphere g u₁ = u₁) : PreservesPair g u₀ u₁ := by
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
  · exact absurd (acdl_sphere_injective g (h0.trans h1.symm)) hne
  · exact Or.inl ⟨h0, h1⟩
  · exact Or.inr ⟨h0, h1⟩
  · exact absurd (acdl_sphere_injective g (h0.trans h1.symm)) hne

private theorem acdl_preservesPair_mul {g h : lorentz d} {u₀ u₁ : PenroseSphere d}
    (hne : u₀ ≠ u₁) (hg : PreservesPair g u₀ u₁) (hh : PreservesPair h u₀ u₁) :
    PreservesPair (g * h) u₀ u₁ := by
  refine acdl_preservesPair_of_mem hne ?_ ?_ <;> rw [acdl_sphere_mul] <;>
    rcases hg with ⟨g0, g1⟩ | ⟨g0, g1⟩ <;> rcases hh with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;>
    simp only [h0, h1, g0, g1, true_or, or_true]

private theorem acdl_preservesPair_inv {g : lorentz d} {u₀ u₁ : PenroseSphere d}
    (hg : PreservesPair g u₀ u₁) : PreservesPair g⁻¹ u₀ u₁ := by
  rcases hg with ⟨g0, g1⟩ | ⟨g0, g1⟩
  · exact Or.inl ⟨acdl_fixed_inv g0, acdl_fixed_inv g1⟩
  · refine Or.inr ⟨?_, ?_⟩
    · conv_lhs => rw [← g1]
      exact acdl_sphere_inv_mul g u₁
    · conv_lhs => rw [← g0]
      exact acdl_sphere_inv_mul g u₀

private theorem acdl_sq_fix {m : lorentz d} {u₀ u₁ : PenroseSphere d}
    (hm : PreservesPair m u₀ u₁) :
    lorentzSphere (m ^ 2) u₀ = u₀ ∧ lorentzSphere (m ^ 2) u₁ = u₁ := by
  rw [pow_two, acdl_sphere_mul, acdl_sphere_mul]
  rcases hm with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rw [h0, h0, h1, h1]; exact ⟨rfl, rfl⟩
  · exact ⟨by rw [h0, h1], by rw [h1, h0]⟩

/-- A point of `𝒮` fixed by `ℓ²`, `ℓ` loxodromic with fixed points `u₀ ≠ u₁`, is `u₀` or `u₁`. -/
private theorem acdl_mem_pair_of_sq {ℓ : lorentz d}
    (hlox : IsLoxodromic (ℓ : Minkowski d ≃ₗ[ℝ] Minkowski d)) {u₀ u₁ : PenroseSphere d}
    (hne : u₀ ≠ u₁) (h₀ : lorentzSphere ℓ u₀ = u₀) (h₁ : lorentzSphere ℓ u₁ = u₁)
    {p : PenroseSphere d} (hp : lorentzSphere (ℓ ^ 2) p = p) : p = u₀ ∨ p = u₁ := by
  obtain ⟨a, ha₀, ha₁, -, hiff, -⟩ := Lox.lorentz_normalForm_of_fix_two hne h₀ h₁
  have ha : a ≠ 0 := hiff.1 hlox
  have hl1 : Real.exp (-a) ≠ 1 := fun h => ha (by
    have := Real.exp_eq_one_iff (-a) |>.1 h; linarith)
  have ha₁' : (ℓ : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u₁) = (Real.exp (-a))⁻¹ • nullVec u₁ := by
    rw [Real.exp_neg, inv_inv]; exact ha₁
  rcases Lox.minkB_eq_zero_of_fixed_pow_loxodromic (Real.exp_pos _) hl1 ha₀ ha₁' two_pos hp with
    h | h
  · exact Or.inl (acdl_eq_of_minkB_eq_zero h).symm
  · exact Or.inr (acdl_eq_of_minkB_eq_zero h).symm

/-- **The backward step**: if the commutator `ℓ x ℓ⁻¹ x⁻¹` preserves the fixed pair of the
loxodromic `ℓ`, so does `x`. -/
theorem preservesPair_of_commutator {ℓ x : lorentz d}
    (hlox : IsLoxodromic (ℓ : Minkowski d ≃ₗ[ℝ] Minkowski d)) {u₀ u₁ : PenroseSphere d}
    (hne : u₀ ≠ u₁) (h₀ : lorentzSphere ℓ u₀ = u₀) (h₁ : lorentzSphere ℓ u₁ = u₁)
    (hc : PreservesPair (ℓ * x * ℓ⁻¹ * x⁻¹) u₀ u₁) : PreservesPair x u₀ u₁ := by
  set m := ℓ⁻¹ * (ℓ * x * ℓ⁻¹ * x⁻¹) with hmdef
  have hm : PreservesPair m u₀ u₁ :=
    acdl_preservesPair_mul hne (Or.inl ⟨acdl_fixed_inv h₀, acdl_fixed_inv h₁⟩) hc
  have hrel : (ℓ ^ 2)⁻¹ * x⁻¹ = x⁻¹ * m ^ 2 := by rw [hmdef]; simp only [pow_two]; group
  have key : ∀ u, lorentzSphere m (lorentzSphere m u) = u →
      lorentzSphere (ℓ ^ 2) (lorentzSphere x⁻¹ u) = lorentzSphere x⁻¹ u := by
    intro u hu
    have e : lorentzSphere (ℓ ^ 2)⁻¹ (lorentzSphere x⁻¹ u) = lorentzSphere x⁻¹ u := by
      rw [← acdl_sphere_mul, hrel, acdl_sphere_mul, pow_two, acdl_sphere_mul, hu]
    calc lorentzSphere (ℓ ^ 2) (lorentzSphere x⁻¹ u)
        = lorentzSphere (ℓ ^ 2) (lorentzSphere (ℓ ^ 2)⁻¹ (lorentzSphere x⁻¹ u)) := by rw [e]
      _ = lorentzSphere x⁻¹ u := by rw [← acdl_sphere_mul, mul_inv_cancel, acdl_sphere_one]
  obtain ⟨hm0, hm1⟩ := acdl_sq_fix hm
  rw [pow_two, acdl_sphere_mul] at hm0 hm1
  have hy0 := acdl_mem_pair_of_sq hlox hne h₀ h₁ (key u₀ hm0)
  have hy1 := acdl_mem_pair_of_sq hlox hne h₀ h₁ (key u₁ hm1)
  have hy : PreservesPair x⁻¹ u₀ u₁ :=
    acdl_preservesPair_of_mem hne hy0 (hy1.symm.imp id id |>.symm)
  simpa using acdl_preservesPair_inv hy

/-- **Step 1 of the loxodromic case**: an Engel element for `ℓ` preserves the fixed pair of `ℓ`. -/
theorem preservesPair_of_engel {ℓ g : lorentz d}
    (hlox : IsLoxodromic (ℓ : Minkowski d ≃ₗ[ℝ] Minkowski d)) {u₀ u₁ : PenroseSphere d}
    (hne : u₀ ≠ u₁) (h₀ : lorentzSphere ℓ u₀ = u₀) (h₁ : lorentzSphere ℓ u₁ = u₁) {k : ℕ}
    (hk : (fun x => ℓ * x * ℓ⁻¹ * x⁻¹)^[k] g = 1) : PreservesPair g u₀ u₁ := by
  induction k generalizing g with
  | zero => rw [iterate_zero_apply] at hk; rw [hk]; exact acdl_preservesPair_one u₀ u₁
  | succ k ih =>
    rw [iterate_succ_apply] at hk
    exact preservesPair_of_commutator hlox hne h₀ h₁ (ih hk)

/-- **A swap is far from `1`**: an element of `SO₀(1, d)` exchanging two points of `𝒮` has the
eigenvalue `−1`, so `‖g − 1‖ ≥ 2`. -/
theorem two_le_norm_of_swap {g : lorentz d} {u₀ u₁ : PenroseSphere d} (hne : u₀ ≠ u₁)
    (h₀ : lorentzSphere g u₀ = u₁) (h₁ : lorentzSphere g u₁ = u₀) :
    2 ≤ ‖linToCLM (g : Minkowski d ≃ₗ[ℝ] Minkowski d) - 1‖ := by
  set G : Minkowski d ≃ₗ[ℝ] Minkowski d := (g : Minkowski d ≃ₗ[ℝ] Minkowski d) with hG
  set s := lorentzScale g u₀
  set s' := lorentzScale g u₁
  have hs : 0 < s := lorentzScale_pos g u₀
  have hs' : 0 < s' := lorentzScale_pos g u₁
  have e₀ : G (nullVec u₀) = s • nullVec u₁ := by
    have := nullVec_lorentzSphere g u₀
    rw [h₀] at this
    rw [this, smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
  have e₁ : G (nullVec u₁) = s' • nullVec u₀ := by
    have := nullVec_lorentzSphere g u₁
    rw [h₁] at this
    rw [this, smul_smul, mul_inv_cancel₀ hs'.ne', one_smul]
  have hss : s * s' = 1 := by
    have h := lorentz.minkB_apply g.2 (nullVec u₀) (nullVec u₁)
    rw [← hG, e₀, e₁, minkB_smul_left, minkB_smul_right, minkB_comm (nullVec u₁)] at h
    have h0 := (Lox.lox_minkB_nullVec_neg hne).ne
    have : (s * s' - 1) * minkB (nullVec u₀) (nullVec u₁) = 0 := by linear_combination h
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right h0)
  set w := nullVec u₀ - s • nullVec u₁ with hw
  have hw0 : w ≠ 0 := fun h => hne (nullVec_injective_smul (c := s) (sub_eq_zero.1 h))
  have hGw : G w = -w := by
    rw [hw, map_sub, map_smul, e₀, e₁, smul_smul, hss, one_smul]; abel
  have hT : (linToCLM G - 1) w = (-2 : ℝ) • w := by
    change G w - w = _
    rw [hGw]
    module
  have hle := (linToCLM G - 1).le_opNorm w
  rw [hT, norm_smul] at hle
  have hpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
  norm_num at hle
  exact le_of_mul_le_mul_right hle hpos

section Boost

variable (u₀ u₁ : PenroseSphere d)

/-- The bilinear constant `β = ⟨(1,u₀) | (1,u₁)⟩` (negative for `u₀ ≠ u₁`). -/
private noncomputable def acdlβ : ℝ := minkB (nullVec u₀) (nullVec u₁)

/-- The axis boost `B_t x = x + (t − 1) (⟨x|n₀⟩/β) n₁ + (t⁻¹ − 1) (⟨x|n₁⟩/β) n₀`. -/
private noncomputable def acdlBoostLin (t : ℝ) : Minkowski d →ₗ[ℝ] Minkowski d where
  toFun x := x + ((t - 1) * (minkB x (nullVec u₀) / acdlβ u₀ u₁)) • nullVec u₁ +
    ((t⁻¹ - 1) * (minkB x (nullVec u₁) / acdlβ u₀ u₁)) • nullVec u₀
  map_add' x y := by
    simp only [minkB_add_left, add_div, mul_add, add_smul]; abel
  map_smul' c x := by
    simp only [minkB_smul_left, RingHom.id_apply]; module

private theorem acdlBoostLin_apply (t : ℝ) (x : Minkowski d) :
    acdlBoostLin u₀ u₁ t x = x + ((t - 1) * (minkB x (nullVec u₀) / acdlβ u₀ u₁)) • nullVec u₁ +
      ((t⁻¹ - 1) * (minkB x (nullVec u₁) / acdlβ u₀ u₁)) • nullVec u₀ := rfl

variable {u₀ u₁}

private theorem acdlβ_ne (hne : u₀ ≠ u₁) : acdlβ u₀ u₁ ≠ 0 := (Lox.lox_minkB_nullVec_neg hne).ne

private theorem acdl_minkB_boost_n₀ (hne : u₀ ≠ u₁) (t : ℝ) (x : Minkowski d) :
    minkB (acdlBoostLin u₀ u₁ t x) (nullVec u₀) = t * minkB x (nullVec u₀) := by
  have hβ := acdlβ_ne hne
  have h00 : minkB (nullVec u₀) (nullVec u₀) = 0 := by rw [← minkQ_eq_minkB, minkQ_nullVec]
  have h10 : minkB (nullVec u₁) (nullVec u₀) = acdlβ u₀ u₁ := minkB_comm _ _
  rw [acdlBoostLin_apply, minkB_add_left, minkB_add_left, minkB_smul_left, minkB_smul_left, h00,
    h10]
  field_simp; ring

private theorem acdl_minkB_boost_n₁ (hne : u₀ ≠ u₁) (t : ℝ) (x : Minkowski d) :
    minkB (acdlBoostLin u₀ u₁ t x) (nullVec u₁) = t⁻¹ * minkB x (nullVec u₁) := by
  have hβ := acdlβ_ne hne
  have h11 : minkB (nullVec u₁) (nullVec u₁) = 0 := by rw [← minkQ_eq_minkB, minkQ_nullVec]
  rw [acdlBoostLin_apply, minkB_add_left, minkB_add_left, minkB_smul_left, minkB_smul_left, h11]
  change _ + _ * minkB (nullVec u₀) (nullVec u₁) = _
  rw [show minkB (nullVec u₀) (nullVec u₁) = acdlβ u₀ u₁ from rfl]
  field_simp; ring

private theorem acdl_boost_comp (hne : u₀ ≠ u₁) (s t : ℝ) :
    acdlBoostLin u₀ u₁ s ∘ₗ acdlBoostLin u₀ u₁ t = acdlBoostLin u₀ u₁ (s * t) := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, acdlBoostLin_apply u₀ u₁ s, acdl_minkB_boost_n₀ hne,
    acdl_minkB_boost_n₁ hne, acdlBoostLin_apply, acdlBoostLin_apply, mul_inv]
  module

private theorem acdl_boost_one : acdlBoostLin u₀ u₁ 1 = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  rw [acdlBoostLin_apply]; simp

private theorem acdl_boost_n₀ (hne : u₀ ≠ u₁) (t : ℝ) :
    acdlBoostLin u₀ u₁ t (nullVec u₀) = t⁻¹ • nullVec u₀ := by
  have hβ := acdlβ_ne hne
  have h00 : minkB (nullVec u₀) (nullVec u₀) = 0 := by rw [← minkQ_eq_minkB, minkQ_nullVec]
  rw [acdlBoostLin_apply, h00, show minkB (nullVec u₀) (nullVec u₁) = acdlβ u₀ u₁ from rfl,
    div_self hβ]
  module

private theorem acdl_boost_n₁ (hne : u₀ ≠ u₁) (t : ℝ) :
    acdlBoostLin u₀ u₁ t (nullVec u₁) = t • nullVec u₁ := by
  have hβ := acdlβ_ne hne
  have h11 : minkB (nullVec u₁) (nullVec u₁) = 0 := by rw [← minkQ_eq_minkB, minkQ_nullVec]
  rw [acdlBoostLin_apply, h11, minkB_comm, show minkB (nullVec u₀) (nullVec u₁) = acdlβ u₀ u₁ from rfl,
    div_self hβ]
  module

private theorem acdl_boost_minkQ (hne : u₀ ≠ u₁) {t : ℝ} (ht : t ≠ 0) (x : Minkowski d) :
    minkQ (acdlBoostLin u₀ u₁ t x) = minkQ x := by
  have hβ := acdlβ_ne hne
  have e0 := acdl_minkB_boost_n₀ hne t x
  have e1 := acdl_minkB_boost_n₁ hne t x
  set y := acdlBoostLin u₀ u₁ t x with hy
  have hyx : minkB y x = minkQ x + ((t - 1) * (minkB x (nullVec u₀) / acdlβ u₀ u₁)) *
      minkB (nullVec u₁) x + ((t⁻¹ - 1) * (minkB x (nullVec u₁) / acdlβ u₀ u₁)) *
      minkB (nullVec u₀) x := by
    rw [hy, acdlBoostLin_apply, minkB_add_left, minkB_add_left, minkB_smul_left, minkB_smul_left,
      minkQ_eq_minkB]
  have hyy : minkQ y = minkB y x + ((t - 1) * (minkB x (nullVec u₀) / acdlβ u₀ u₁)) *
      minkB y (nullVec u₁) + ((t⁻¹ - 1) * (minkB x (nullVec u₁) / acdlβ u₀ u₁)) *
      minkB y (nullVec u₀) := by
    conv_lhs => rw [minkQ_eq_minkB, hy]
    conv_lhs => arg 2; rw [acdlBoostLin_apply]
    rw [minkB_add_right, minkB_add_right, minkB_smul_right, minkB_smul_right]
  rw [hyy, hyx, e0, e1, minkB_comm (nullVec u₁) x, minkB_comm (nullVec u₀) x]
  field_simp
  ring

/-- The boost `B_t ∈ SO₀(1, d)` (`t > 0`). -/
private noncomputable def acdlBoost (hne : u₀ ≠ u₁) (t : ℝ) (ht : 0 < t) : lorentz d :=
  ⟨LinearEquiv.ofLinear (acdlBoostLin u₀ u₁ t) (acdlBoostLin u₀ u₁ t⁻¹)
    (by rw [acdl_boost_comp hne, mul_inv_cancel₀ ht.ne', acdl_boost_one])
    (by rw [acdl_boost_comp hne, inv_mul_cancel₀ ht.ne', acdl_boost_one]), by
    have hQ : ∀ v, minkQ (acdlBoostLin u₀ u₁ t v) = minkQ v := acdl_boost_minkQ hne ht.ne'
    have hβ := Lox.lox_minkB_nullVec_neg hne
    have he : IsFutureTimelike (nullVec u₀ + nullVec u₁) := by
      refine ⟨by simp [nullVec], ?_⟩
      rw [minkQ_add, minkQ_nullVec, minkQ_nullVec]; linarith
    refine mem_lorentz_of_future hQ he ?_ ?_
    · refine ⟨?_, by rw [LinearEquiv.ofLinear_apply, hQ]; exact he.2⟩
      rw [LinearEquiv.ofLinear_apply, map_add, acdl_boost_n₀ hne, acdl_boost_n₁ hne]
      simp only [Prod.fst_add, Prod.smul_fst, nullVec, smul_eq_mul, mul_one]
      positivity
    · change LinearMap.det (acdlBoostLin u₀ u₁ t) = 1
      refine det_eq_one_of_eq_sq hQ (B := acdlBoostLin u₀ u₁ (Real.sqrt t)) ?_
      rw [acdl_boost_comp hne, Real.mul_self_sqrt ht.le]⟩

private theorem acdlBoost_apply (hne : u₀ ≠ u₁) {t : ℝ} (ht : 0 < t) (x : Minkowski d) :
    ((acdlBoost hne t ht : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) x =
      acdlBoostLin u₀ u₁ t x := rfl

private theorem acdlBoost_congr (hne : u₀ ≠ u₁) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (h : s = t) :
    acdlBoost hne s hs = acdlBoost hne t ht := by subst h; rfl

private theorem acdlBoost_mul (hne : u₀ ≠ u₁) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    acdlBoost hne s hs * acdlBoost hne t ht = acdlBoost hne (s * t) (mul_pos hs ht) := by
  refine Subtype.ext (LinearEquiv.ext fun x => ?_)
  change acdlBoostLin u₀ u₁ s (acdlBoostLin u₀ u₁ t x) = acdlBoostLin u₀ u₁ (s * t) x
  rw [← LinearMap.comp_apply, acdl_boost_comp hne]

private theorem acdlBoost_one (hne : u₀ ≠ u₁) : acdlBoost hne 1 one_pos = 1 := by
  refine Subtype.ext (LinearEquiv.ext fun x => ?_)
  change acdlBoostLin u₀ u₁ 1 x = x
  rw [acdl_boost_one, LinearMap.id_apply]

/-- `⟨A x | n⟩ = c' ⟨x | n⟩` when `A n = c n` and `c c' = 1`. -/
private theorem acdl_minkB_apply_eigen {A : lorentz d} {n : Minkowski d} {c c' : ℝ}
    (hn : (A : Minkowski d ≃ₗ[ℝ] Minkowski d) n = c • n) (hcc : c * c' = 1) (x : Minkowski d) :
    minkB ((A : Minkowski d ≃ₗ[ℝ] Minkowski d) x) n = c' * minkB x n := by
  have h := lorentz.minkB_apply A.2 x n
  rw [hn, minkB_smul_right] at h
  rw [← h, ← mul_assoc, mul_comm c' c, hcc, one_mul]

/-- The boosts commute with every element scaling `n₀` and `n₁` reciprocally. -/
private theorem acdlBoost_commute (hne : u₀ ≠ u₁) {t : ℝ} (ht : 0 < t) {A : lorentz d} {c c' : ℝ}
    (h₀ : (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u₀) = c • nullVec u₀)
    (h₁ : (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u₁) = c' • nullVec u₁)
    (hcc : c * c' = 1) : A * acdlBoost hne t ht = acdlBoost hne t ht * A := by
  have hcc' : c' * c = 1 := by rw [mul_comm]; exact hcc
  refine Subtype.ext (LinearEquiv.ext fun x => ?_)
  change (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (acdlBoostLin u₀ u₁ t x) =
    acdlBoostLin u₀ u₁ t ((A : Minkowski d ≃ₗ[ℝ] Minkowski d) x)
  rw [acdlBoostLin_apply, acdlBoostLin_apply, map_add, map_add, map_smul, map_smul, h₀, h₁,
    acdl_minkB_apply_eigen h₀ hcc, acdl_minkB_apply_eigen h₁ hcc']
  have hc' : c' = c⁻¹ := eq_inv_of_mul_eq_one_right hcc
  subst hc'
  have hc : c ≠ 0 := left_ne_zero_of_mul_eq_one hcc
  rw [smul_smul, smul_smul]
  congr 2 <;> field_simp

/-- The eigenvalue data of an element fixing `u₀` and `u₁`. -/
private theorem acdl_eigen_pair {A : lorentz d} (hne : u₀ ≠ u₁)
    (h₀ : lorentzSphere A u₀ = u₀) (h₁ : lorentzSphere A u₁ = u₁) :
    (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u₀) = lorentzScale A u₀ • nullVec u₀ ∧
      (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u₁) = lorentzScale A u₁ • nullVec u₁ ∧
        lorentzScale A u₀ * lorentzScale A u₁ = 1 := by
  have e₀ := Lox.lox_apply_nullVec_of_fix h₀
  have e₁ := Lox.lox_apply_nullVec_of_fix h₁
  refine ⟨e₀, e₁, ?_⟩
  have h := lorentz.minkB_apply A.2 (nullVec u₀) (nullVec u₁)
  rw [e₀, e₁, minkB_smul_left, minkB_smul_right] at h
  have h0 := (Lox.lox_minkB_nullVec_neg hne).ne
  have : (lorentzScale A u₀ * lorentzScale A u₁ - 1) * minkB (nullVec u₀) (nullVec u₁) = 0 := by
    linear_combination h
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right h0)

private theorem acdl_lorentzScale_mul {A B : lorentz d} {u : PenroseSphere d}
    (hB : lorentzSphere B u = u) :
    lorentzScale (A * B) u = lorentzScale B u * lorentzScale A u := by
  change (((A : Minkowski d ≃ₗ[ℝ] Minkowski d) * (B : Minkowski d ≃ₗ[ℝ] Minkowski d))
    (nullVec u)).1 = _
  rw [LinearEquiv.mul_apply, Lox.lox_apply_nullVec_of_fix hB, map_smul, Prod.smul_fst,
    smul_eq_mul]
  rfl

/-- The normalisation `φ A = B_{λ(A)} A`, `λ(A) = lorentzScale A u₀`. -/
private noncomputable def acdlNormalize (hne : u₀ ≠ u₁) (M : Subgroup (lorentz d))
    (hM : ∀ A ∈ M, lorentzSphere A u₀ = u₀ ∧ lorentzSphere A u₁ = u₁) : M →* lorentz d where
  toFun A := acdlBoost hne (lorentzScale (A : lorentz d) u₀) (lorentzScale_pos _ _) * A
  map_one' := by
    rw [acdlBoost_congr hne _ one_pos (show lorentzScale ((1 : M) : lorentz d) u₀ = 1 from rfl),
      acdlBoost_one, one_mul, OneMemClass.coe_one]
  map_mul' A B := by
    have hA := hM A A.2
    have hB := hM B B.2
    obtain ⟨eA₀, eA₁, hAA⟩ := acdl_eigen_pair hne hA.1 hA.2
    simp only [Subgroup.coe_mul]
    rw [acdlBoost_congr hne _ (mul_pos (lorentzScale_pos (A : lorentz d) u₀)
      (lorentzScale_pos (B : lorentz d) u₀))
      (by rw [acdl_lorentzScale_mul hB.1, mul_comm]), ← acdlBoost_mul hne]
    simp only [mul_assoc]
    rw [← mul_assoc (A : lorentz d), acdlBoost_commute hne _ eA₀ eA₁ hAA, mul_assoc]

/-- **Normalisation on the stabiliser of two points of `𝒮`**: a homomorphism `φ` from any group
`M` of Lorentz maps fixing `u₀` and `u₁` to the stabiliser of `(1, u₀)`, preserving the rotation
part `screenRot (1, u₀)` and reflecting commutation (`φ A = B_{−α(A)} A`, `B_s` the boost of the
axis `span {(1,u₀), (1,u₁)}`). -/
theorem exists_normalize_pairStab {u₀ u₁ : PenroseSphere d} (hne : u₀ ≠ u₁)
    (M : Subgroup (lorentz d))
    (hM : ∀ A ∈ M, lorentzSphere A u₀ = u₀ ∧ lorentzSphere A u₁ = u₁) :
    ∃ φ : M →* lorentz d,
      (∀ A : M, ((φ A : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u₀) = nullVec u₀) ∧
      (∀ A : M, screenRot (nullVec u₀) ((φ A : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) =
        screenRot (nullVec u₀) ((A : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d)) ∧
      ∀ A B : M, φ A * φ B = φ B * φ A → (A : lorentz d) * B = B * A := by
  refine ⟨acdlNormalize hne M hM, fun A => ?_, fun A => ?_, fun A B hAB => ?_⟩
  · have hA := hM A A.2
    obtain ⟨eA₀, -, -⟩ := acdl_eigen_pair hne hA.1 hA.2
    change acdlBoostLin u₀ u₁ _ (((A : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u₀)) = _
    rw [eA₀, map_smul, acdl_boost_n₀ hne, smul_smul,
      mul_inv_cancel₀ (lorentzScale_pos (A : lorentz d) u₀).ne', one_smul]
  · have hA := hM A A.2
    obtain ⟨eA₀, -, hAA⟩ := acdl_eigen_pair hne hA.1 hA.2
    refine ContinuousLinearMap.ext fun x => ?_
    rw [screenRot_apply, screenRot_apply]
    congr 1
    set y := ((A : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) (screenProj (nullVec u₀) x)
    have hy : minkB y (nullVec u₀) = 0 := by
      rw [acdl_minkB_apply_eigen eA₀ hAA, minkB_comm,
        minkB_self_of_mem_nullScreen _ (screenProj_mem _ x), mul_zero]
    change screenProj (nullVec u₀) (acdlBoostLin u₀ u₁ _ y) = screenProj (nullVec u₀) y
    rw [acdlBoostLin_apply, hy, zero_div, mul_zero, zero_smul, add_zero, map_add, map_smul,
      screenProj_self, smul_zero, add_zero]
  · rw [← map_mul, ← map_mul] at hAB
    change acdlBoost hne _ _ * ((A * B : M) : lorentz d) =
      acdlBoost hne _ _ * ((B * A : M) : lorentz d) at hAB
    have hA := hM A A.2
    have hB := hM B B.2
    rw [acdlBoost_congr hne _ (lorentzScale_pos ((B * A : M) : lorentz d) u₀)
      (by simp only [Subgroup.coe_mul]; rw [acdl_lorentzScale_mul hB.1,
        acdl_lorentzScale_mul hA.1, mul_comm])] at hAB
    simpa using mul_left_cancel hAB

end Boost

/-- **Step 2, loxodromic case**: near-identity elements of a nilpotent subgroup of `SO₀(1, d)`
containing a loxodromic element commute — given the null case (`hNull`, `hρ`). -/
theorem commute_of_isNilpotent_of_loxodromic
    (hNull : ∀ N : Subgroup (lorentz d), Group.IsNilpotent N → ∀ v₀ : Minkowski d, v₀ ≠ 0 →
      minkQ v₀ = 0 → (∀ A ∈ N, (A : Minkowski d ≃ₗ[ℝ] Minkowski d) v₀ = v₀) →
      ∀ a ∈ N, ∀ b ∈ N, ‖screenRot v₀ (a : Minkowski d ≃ₗ[ℝ] Minkowski d) - 1‖ < 1 / 2 →
        ‖screenRot v₀ (b : Minkowski d ≃ₗ[ℝ] Minkowski d) - 1‖ < 1 / 2 → a * b = b * a)
    (hρ : ∀ v₀ : Minkowski d, v₀ ≠ 0 → minkQ v₀ = 0 → ∀ A : Minkowski d ≃ₗ[ℝ] Minkowski d,
      ‖screenRot v₀ A - 1‖ ≤ ‖linToCLM A - 1‖)
    {N : Subgroup (lorentz d)} (hN : Group.IsNilpotent N) {ℓ : lorentz d} (hℓ : ℓ ∈ N)
    (hlox : IsLoxodromic (ℓ : Minkowski d ≃ₗ[ℝ] Minkowski d)) {a b : lorentz d} (ha : a ∈ N)
    (hb : b ∈ N) (haε : ‖linToCLM (a : Minkowski d ≃ₗ[ℝ] Minkowski d) - 1‖ < 1 / 2)
    (hbε : ‖linToCLM (b : Minkowski d ≃ₗ[ℝ] Minkowski d) - 1‖ < 1 / 2) :
    a * b = b * a := by
  haveI := hN
  obtain ⟨u₀, u₁, hne, h₀, h₁⟩ := exists_fixed_pair_of_isLoxodromic hlox
  -- every element of `N` preserves `{u₀, u₁}` (Engel in `↥N`, transported to `lorentz d`)
  have hval : ∀ (n : ℕ) (x : N),
      (((fun y => (⟨ℓ, hℓ⟩ : N) * y * (⟨ℓ, hℓ⟩ : N)⁻¹ * y⁻¹)^[n] x : N) : lorentz d) =
        (fun y => ℓ * y * ℓ⁻¹ * y⁻¹)^[n] (x : lorentz d) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih => intro x; rw [iterate_succ_apply, iterate_succ_apply, ih]; rfl
  have hpres : ∀ g ∈ N, PreservesPair g u₀ u₁ := by
    intro g hg
    obtain ⟨k, hk⟩ := lox_exists_iterate_eq_one (⟨ℓ, hℓ⟩ : N) ⟨g, hg⟩
    refine preservesPair_of_engel hlox hne h₀ h₁ (k := k) ?_
    have := congrArg Subtype.val hk
    rwa [hval] at this
  -- a near-identity element of `N` fixes both points
  have hfix : ∀ g ∈ N, ‖linToCLM (g : Minkowski d ≃ₗ[ℝ] Minkowski d) - 1‖ < 1 / 2 →
      lorentzSphere g u₀ = u₀ ∧ lorentzSphere g u₁ = u₁ := by
    intro g hg hε
    rcases hpres g hg with h | ⟨s₀, s₁⟩
    · exact h
    · have := two_le_norm_of_swap hne s₀ s₁
      linarith
  -- the pair stabiliser `M = N ⊓ Stab(u₀) ⊓ Stab(u₁)`
  let S : Subgroup (lorentz d) :=
    { carrier := {A | lorentzSphere A u₀ = u₀ ∧ lorentzSphere A u₁ = u₁}
      mul_mem' := fun {A B} hA hB => by
        refine ⟨?_, ?_⟩ <;> rw [acdl_sphere_mul]
        · rw [hB.1, hA.1]
        · rw [hB.2, hA.2]
      one_mem' := ⟨acdl_sphere_one u₀, acdl_sphere_one u₁⟩
      inv_mem' := fun {A} hA => ⟨acdl_fixed_inv hA.1, acdl_fixed_inv hA.2⟩ }
  let M : Subgroup (lorentz d) := N ⊓ S
  have hM : ∀ A ∈ M, lorentzSphere A u₀ = u₀ ∧ lorentzSphere A u₁ = u₁ := fun A hA => hA.2
  haveI hMnil : Group.IsNilpotent M :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe (inf_le_left : M ≤ N))
  obtain ⟨φ, hφ₀, hφρ, hφc⟩ := exists_normalize_pairStab hne M hM
  -- the null case on `φ(M)`, at `v₀ = (1, u₀)`
  have hnil : Group.IsNilpotent φ.range :=
    Group.nilpotent_of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hfix₀ : ∀ A ∈ φ.range, (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u₀) = nullVec u₀ := by
    rintro _ ⟨m, rfl⟩
    exact hφ₀ m
  let a' : M := ⟨a, ha, hfix a ha haε⟩
  let b' : M := ⟨b, hb, hfix b hb hbε⟩
  have hbound : ∀ x : M, ‖linToCLM ((x : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) - 1‖ < 1 / 2 →
      ‖screenRot (nullVec u₀) ((φ x : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) - 1‖ < 1 / 2 := by
    intro x hx
    rw [hφρ]
    exact lt_of_le_of_lt (hρ _ (nullVec_ne_zero u₀) (minkQ_nullVec u₀) _) hx
  exact hφc a' b' (hNull φ.range hnil (nullVec u₀) (nullVec_ne_zero u₀) (minkQ_nullVec u₀) hfix₀
    (φ a') ⟨a', rfl⟩ (φ b') ⟨b', rfl⟩ (hbound a' haε) (hbound b' hbε))

end Causal.Flat
