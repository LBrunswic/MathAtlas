import Causal.Flat.Externals
import Causal.Flat.Lox.TwoNullNormalForm

/-!
# `Causal.Flat.Lox.MisnerLimitSet` — [10.M]: the limit set is the two invariant null levels

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §10,
subsection "The elementary case", `papers/barbot/legacy/labeled/GHFspace.tex` l.3307–3315.
**No label is marked**: [10.M] is prose; this file is one step of `loxo_elementary_misner`
(`Flat/Loxodromic.lean`, item (4) of its obstruction: `limitSetJ Γ' = {(u₀,s₀),(u₁,s₁)}`).

> Then, since the linear parts of loxodromic elements of
> $\Gamma$ preserve the same isotropic directions than $L(\gamma_{0})$, the achronal
> domain of any loxodromic element $\gamma$ of $\Gamma$ is $\pi_{P}^{-1}(\{ (x-x(\gamma))(y-y(\gamma)) < 0 \})$
> for some real numbers $x(\gamma)$, $y(\gamma)$.
> According to lemma \ref{sanlox}, it follows that $\Omega(\Gamma) = \Omega_{lox}(\gamma)$
> has also the expression $\pi_{P}^{-1}(\{ (x-x_{0})(y-y_{0}) < 0 \})$.
> Finally, since $\Omega(\Gamma)$ is $\gamma_{0}$-invariant, we have $x_{0} = y_{0} = x(\gamma) = y(\gamma) = 0$.
> (l.3309–3315)

`misner_limitSet`: if `L(Γ₁)` fixes `u₀ ≠ u₁ ∈ 𝒮`, `Γ₁` preserves the lightlike levels `s₀` of
`(1,u₀)` and `s₁` of `(1,u₁)`, and `Γ₁` has a loxodromic element, then the closure of the
repulsive fixed points in `𝒥 = 𝒮 × ℝ` of the loxodromic elements of `Γ₁` — `Flat.Loxodromic`'s
`limitSetJ Γ₁`, written out, as in `Lox.preimage_omega_closure_repJ`, because this module may not
import `Flat.Loxodromic` (which imports it) — is the two-point set `{(u₀, s₀), (u₁, s₁)}`. The
set below is `limitSetJ Γ₁` **by definition** (`limitSetJ`, `loxRepSet`, `IsRepulsiveFixedJ`
unfold to it), so the consumer closes with `exact`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `L(Γ)` fixes `Δ₀`, `Δ₁` (l.3309–3310) | ✓ carried, for `Γ₁` (`hfix₀`, `hfix₁`) |
| `x(γ) = y(γ) = 0` (l.3315) | ✓ carried as the invariant levels (`hs₀`, `hs₁`) |
| `γ₀` loxodromic | ✓ carried (`hlox`) |

## SCOPE (disclosed)

* **No `sorry`.** `misner_limitSet` is proved in full, as stated; it is one step of the prose
  [10.M] (no label), so it carries no `**` mark. What l.3309–3315 derives through the achronal
  domains `π_P^{-1}({(x-x(γ))(y-y(γ)) < 0})` and lemma `sanlox` is reached here directly in `𝒥`:
  the invariant levels `x₀ = y₀ = 0` are carried as hypotheses (`hs₀`, `hs₁`), not derived.
* Proof. (⊆) the two-point set is finite, hence closed; for a repulsive `(u,t)` of a `γ ∈ Γ₁`,
  `L(γ)` scales `(1,u₀)`, `(1,u₁)` by `e^{∓a}` (`lorentz_normalForm_of_fix_two`) and preserves
  `minkB`, so `(e^{∓a} l − 1) ⟨(1,uᵢ)|(1,u)⟩ = 0`; both brackets nonzero forces `l² = 1`, absurd,
  and a zero bracket forces `u = uᵢ` (`lox_minkB_nullVec_neg`); then the level point `(−sᵢ, 0)`
  and `hsᵢ` give `(1 − l⁻¹)(sᵢ − t) = 0`, so `t = sᵢ`. (⊇) for the loxodromic `γ` of `hlox`,
  `a ≠ 0` and `γ⁻¹ ∈ Γ₁` has parameter `−a`, hence is loxodromic by the same normal form; whichever
  of `γ`, `γ⁻¹` has eigenvalue `e^{−|a|} < 1` on `(1,uᵢ)` makes `(uᵢ,sᵢ)` repulsive
  (`mls_mem`, the functional equation's constant being `sᵢ` by `hsᵢ`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal.Flat.Lox

open Causal.Flat Set

section mls

variable {d : ℕ}

/-- The level functional of an eigen-null vector: if `L(γ)(1,u) = l (1,u)` with `l ≠ 0`, then
`⟨(1,u) | γ p⟩ = l⁻¹ ⟨(1,u) | p⟩ + ⟨(1,u) | τ(γ)⟩`. -/
private theorem mls_level {γ : isom d} {u : PenroseSphere d} {l : ℝ} (hl : l ≠ 0)
    (hL : linOf γ (nullVec u) = l • nullVec u) (p : Minkowski d) :
    minkB (nullVec u) (γ • p) = l⁻¹ * minkB (nullVec u) p + minkB (nullVec u) (trOf γ) := by
  have h := lorentz.minkB_apply (linOf_mem γ) (nullVec u) p
  rw [hL, minkB_smul_left] at h
  rw [smul_eq_lin_add, minkB_add_right, ← h, ← mul_assoc, inv_mul_cancel₀ hl, one_mul]

/-- A point of level `s` for `(1,u)`: `⟨(1,u) | (-s, 0)⟩ = s`. -/
private theorem mls_minkB_level (u : PenroseSphere d) (s : ℝ) :
    minkB (nullVec u) ((-s, 0) : Minkowski d) = s := by
  simp [minkB, nullVec]

/-- (⊇), one point: a loxodromic `γ ∈ Γ₁` contracting `(1,u)` (`0 < l < 1`) whose `u`-level `s`
is `Γ₁`-invariant has `(u, s)` as a repulsive fixed point in `𝒥`. -/
private theorem mls_mem {Γ₁ : Subgroup (isom d)} {u : PenroseSphere d} {s : ℝ}
    (hs : ∀ γ ∈ Γ₁, ∀ p : Minkowski d,
      minkB (nullVec u) p = s → minkB (nullVec u) (γ • p) = s)
    {γ : isom d} (hγ : γ ∈ Γ₁) (hlox : IsLoxodromic (linOf γ)) {l : ℝ} (hl0 : 0 < l)
    (hl1 : l < 1) (hL : linOf γ (nullVec u) = l • nullVec u) :
    (u, s) ∈ {w : PenroseSphere d × ℝ | ∃ γ ∈ Γ₁, IsLoxodromic (linOf γ) ∧
        ∃ l : ℝ, 0 < l ∧ l < 1 ∧ linOf γ (nullVec w.1) = l • nullVec w.1 ∧
          ∀ p : Minkowski d, minkB (nullVec w.1) (γ • p) - w.2 =
            l⁻¹ * (minkB (nullVec w.1) p - w.2)} := by
  refine ⟨γ, hγ, hlox, l, hl0, hl1, hL, fun p => ?_⟩
  have hc := mls_level hl0.ne' hL ((-s, 0) : Minkowski d)
  rw [hs γ hγ _ (mls_minkB_level u s), mls_minkB_level u s] at hc
  show minkB (nullVec u) (γ • p) - s = l⁻¹ * (minkB (nullVec u) p - s)
  rw [mls_level hl0.ne' hL p]
  linarith [hc]

/-- Two points of `𝒮` whose null vectors are `minkB`-orthogonal coincide. -/
private theorem mls_eq_of_minkB_zero {u u' : PenroseSphere d}
    (h : minkB (nullVec u) (nullVec u') = 0) : u = u' := by
  by_contra hne
  exact (lox_minkB_nullVec_neg hne).ne h

/-- `L(γ) L(γ⁻¹) = id`, pointwise. -/
private theorem mls_linOf_inv_apply (γ : isom d) (v : Minkowski d) :
    linOf γ (linOf γ⁻¹ v) = v := by
  have h : γ • (γ⁻¹ • (0 : Minkowski d)) = 0 := smul_inv_smul γ 0
  have e : γ • (γ⁻¹ • v) = v := smul_inv_smul γ v
  rw [smul_eq_lin_add, smul_eq_lin_add, map_add] at e h
  rw [map_zero, map_zero, zero_add] at h
  rw [add_assoc, h, add_zero] at e
  exact e

end mls

/-- **[10.M] l.3309–3315: `Λ(Γ₁) = {(u₀,s₀),(u₁,s₁)}`.** The closure of the repulsive fixed points
in `𝒥` of the loxodromic elements of `Γ₁` (`limitSetJ Γ₁`, written out) is the pair of invariant
lightlike levels. -/
theorem misner_limitSet {d : ℕ} {Γ₁ : Subgroup (isom d)} {u₀ u₁ : PenroseSphere d}
    (hne : u₀ ≠ u₁)
    (hfix₀ : ∀ γ ∈ Γ₁, lorentzSphere (linearPart γ) u₀ = u₀)
    (hfix₁ : ∀ γ ∈ Γ₁, lorentzSphere (linearPart γ) u₁ = u₁) {s₀ s₁ : ℝ}
    (hs₀ : ∀ γ ∈ Γ₁, ∀ p : Minkowski d,
      minkB (nullVec u₀) p = s₀ → minkB (nullVec u₀) (γ • p) = s₀)
    (hs₁ : ∀ γ ∈ Γ₁, ∀ p : Minkowski d,
      minkB (nullVec u₁) p = s₁ → minkB (nullVec u₁) (γ • p) = s₁)
    (hlox : ∃ γ ∈ Γ₁, IsLoxodromic (linOf γ)) :
    closure {w : PenroseSphere d × ℝ | ∃ γ ∈ Γ₁, IsLoxodromic (linOf γ) ∧
        ∃ l : ℝ, 0 < l ∧ l < 1 ∧ linOf γ (nullVec w.1) = l • nullVec w.1 ∧
          ∀ p : Minkowski d, minkB (nullVec w.1) (γ • p) - w.2 =
            l⁻¹ * (minkB (nullVec w.1) p - w.2)} =
      ({(u₀, s₀), (u₁, s₁)} : Set (PenroseSphere d × ℝ)) := by
  set S := {w : PenroseSphere d × ℝ | ∃ γ ∈ Γ₁, IsLoxodromic (linOf γ) ∧
        ∃ l : ℝ, 0 < l ∧ l < 1 ∧ linOf γ (nullVec w.1) = l • nullVec w.1 ∧
          ∀ p : Minkowski d, minkB (nullVec w.1) (γ • p) - w.2 =
            l⁻¹ * (minkB (nullVec w.1) p - w.2)} with hS
  -- the normal form of any element of `Γ₁`
  have hnf : ∀ γ ∈ Γ₁, ∃ a : ℝ, linOf γ (nullVec u₀) = Real.exp (-a) • nullVec u₀ ∧
      linOf γ (nullVec u₁) = Real.exp a • nullVec u₁ ∧ (IsLoxodromic (linOf γ) ↔ a ≠ 0) := by
    intro γ hγ
    obtain ⟨a, e₀, e₁, -, hl, -⟩ := lorentz_normalForm_of_fix_two hne (hfix₀ γ hγ) (hfix₁ γ hγ)
    rw [← linOf_eq_linearPart] at e₀ e₁ hl
    exact ⟨a, e₀, e₁, hl⟩
  apply Set.Subset.antisymm
  · -- (⊆): `S` lies in the closed two-point set
    have hcl : IsClosed ({(u₀, s₀), (u₁, s₁)} : Set (PenroseSphere d × ℝ)) :=
      (Set.toFinite _).isClosed
    refine (hcl.closure_subset_iff).2 ?_
    rintro ⟨u, t⟩ ⟨γ, hγ, -, l, hl0, hl1, hL, hfun⟩
    simp only at hL hfun
    obtain ⟨a, e₀, e₁, -⟩ := hnf γ hγ
    -- `(e^{∓a} l - 1) ⟨(1,uᵢ)|(1,u)⟩ = 0`
    have key : ∀ (v : PenroseSphere d) (c : ℝ), linOf γ (nullVec v) = c • nullVec v →
        (c * l - 1) * minkB (nullVec v) (nullVec u) = 0 := by
      intro v c hv
      have h := lorentz.minkB_apply (linOf_mem γ) (nullVec v) (nullVec u)
      rw [hv, hL, minkB_smul_left, minkB_smul_right] at h
      linarith
    have k₀ := key u₀ _ e₀
    have k₁ := key u₁ _ e₁
    -- the level `t` is the invariant one
    have hlev : ∀ {v : PenroseSphere d} {s : ℝ}, v = u →
        (∀ γ ∈ Γ₁, ∀ p : Minkowski d,
          minkB (nullVec v) p = s → minkB (nullVec v) (γ • p) = s) → t = s := by
      rintro v s rfl hs
      have h := hfun ((-s, 0) : Minkowski d)
      rw [hs γ hγ _ (mls_minkB_level v s), mls_minkB_level v s] at h
      have hl' : l⁻¹ ≠ 1 := by
        intro h1; rw [inv_eq_one] at h1; linarith
      have : (1 - l⁻¹) * (s - t) = 0 := by linarith
      rcases mul_eq_zero.1 this with h2 | h2
      · exact absurd (by linarith : l⁻¹ = 1) hl'
      · linarith
    by_cases h₀ : minkB (nullVec u₀) (nullVec u) = 0
    · have hu := mls_eq_of_minkB_zero h₀
      exact Or.inl (Prod.ext hu.symm (hlev hu hs₀))
    by_cases h₁ : minkB (nullVec u₁) (nullVec u) = 0
    · have hu := mls_eq_of_minkB_zero h₁
      exact Or.inr (Set.mem_singleton_iff.2 (Prod.ext hu.symm (hlev hu hs₁)))
    exfalso
    have c₀ : Real.exp (-a) * l = 1 := by
      have := (mul_eq_zero.1 k₀).resolve_right h₀; linarith
    have c₁ : Real.exp a * l = 1 := by
      have := (mul_eq_zero.1 k₁).resolve_right h₁; linarith
    have hprod : (Real.exp (-a) * l) * (Real.exp a * l) = 1 := by rw [c₀, c₁, one_mul]
    have hee : Real.exp (-a) * Real.exp a = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have hll : l * l = 1 := by
      have : (Real.exp (-a) * Real.exp a) * (l * l) = 1 := by rw [← hprod]; ring
      rwa [hee, one_mul] at this
    nlinarith
  · -- (⊇): both points are repulsive fixed points, of `γ` and `γ⁻¹`
    obtain ⟨γ, hγ, hγl⟩ := hlox
    obtain ⟨a, e₀, e₁, ha⟩ := hnf γ hγ
    have ha0 : a ≠ 0 := ha.1 hγl
    have hγi : γ⁻¹ ∈ Γ₁ := Γ₁.inv_mem hγ
    obtain ⟨b, f₀, f₁, hb⟩ := hnf γ⁻¹ hγi
    -- `b = -a`
    have hba : b = -a := by
      have h := mls_linOf_inv_apply γ (nullVec u₁)
      rw [f₁, map_smul, e₁, smul_smul] at h
      have h2 : (Real.exp b * Real.exp a - 1) • nullVec u₁ = 0 := by
        rw [sub_smul, h, one_smul, sub_self]
      rcases smul_eq_zero.1 h2 with h3 | h3
      · rw [← Real.exp_add, sub_eq_zero, Real.exp_eq_one_iff] at h3; linarith
      · exact absurd h3 (nullVec_ne_zero u₁)
    subst hba
    have hil : IsLoxodromic (linOf γ⁻¹) := hb.2 (neg_ne_zero.2 ha0)
    have hpos : ∀ x : ℝ, 0 < Real.exp x := Real.exp_pos
    rw [neg_neg] at f₀
    rintro w hw
    apply subset_closure
    rcases hw with rfl | hw
    · rcases lt_or_gt_of_ne ha0 with hneg | hpos'
      · -- `a < 0`: `γ⁻¹` contracts `(1,u₀)` by `e^{a}`
        exact mls_mem hs₀ hγi hil (hpos a) (Real.exp_lt_one_iff.2 hneg) f₀
      · -- `a > 0`: `γ` contracts `(1,u₀)` by `e^{-a}`
        exact mls_mem hs₀ hγ hγl (hpos (-a)) (Real.exp_lt_one_iff.2 (by linarith)) e₀
    · rw [Set.mem_singleton_iff] at hw; subst hw
      rcases lt_or_gt_of_ne ha0 with hneg | hpos'
      · exact mls_mem hs₁ hγ hγl (hpos a) (Real.exp_lt_one_iff.2 hneg) e₁
      · exact mls_mem hs₁ hγi hil (hpos (-a)) (Real.exp_lt_one_iff.2 (by linarith)) f₁

end Causal.Flat.Lox
