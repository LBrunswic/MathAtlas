import CausalScaffold.Flat.Externals

/-!
# `CausalScaffold.Flat.Lox.NullLevelFix` — [10.M]: a group fixing a null direction `Δ₀` and one-sided on its repulsive fixed points preserves one lightlike level `{⟨(1,u₀) | ·⟩ = s₀}`

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §10,
subsection "The elementary case" (`misnerr`). No ledger label is certified here (no `**` mark):
this serves `loxo_elementary_misner` (`Flat/Loxodromic.lean`, [10.M]) for two of its steps, read
in `papers/barbot/legacy/labeled/GHFspace.tex`: `b ≡ 0` (l.3250–3257),

> We choose as origin of $Q_{1}$ the fixed point of $\gamma_{0}$. Then, $b(\gamma_{0})=0$, …
> Since $I = \pi_{1}(\widetilde{S})$, $I'=\pi_{1}(\Omega(\widetilde{S}))$ are
> $\rho(\gamma_{0})$-invariant intervals of ${\mathbb R}$, they are both the interval
> $]-\infty, 0[$ or $]0, +\infty[$ … Moreover, $b(\gamma)=0$ for every $\gamma$ in $\Gamma$.

and `x(γ) = y(γ) = 0` (l.3306–3319),

> the achronal domain of any loxodromic element $\gamma$ of $\Gamma$ is
> $\pi_{P}^{-1}(\{ (x-x(\gamma))(y-y(\gamma)) < 0 \})$ … Finally, since $\Omega(\Gamma)$ is
> $\gamma_{0}$-invariant, we have $x_{0} = y_{0} = x(\gamma) = y(\gamma) = 0$.
> Then $\pi_{P}^{-1}(0)$ is a $\Gamma$-invariant spacelike subspace

`exists_invariant_nullLevel`: if every `γ ∈ Γ` fixes `u₀ ∈ 𝒮`, some `γ ∈ Γ` is loxodromic, and a
nonempty `Ω` lies in `Ω⁺` or in `Ω⁻` of the repulsive fixed points `Λ₀(Γ)` (written out:
`Flat.Loxodromic.loxRepSet`, not importable here), then some level `{⟨(1,u₀) | ·⟩ = s₀}` is
`Γ`-invariant. Applied at `u₀` and at `u₁` once both are fixed, the two levels meet in Barbot's
`Γ`-invariant spacelike `π_P^{-1}(0)`. Barbot's `n` is `d + 1` (kb/0024).

The proof: with `f = ⟨(1,u₀) | ·⟩`, `f(γ p) = c_γ⁻¹ f(p) + f(γ 0)`, `c_γ > 0` the eigenvalue of
`L(γ)` on `(1,u₀)`. An element with `c < 1` fixing the level `σ` makes `(u₀, σ) ∈ Λ₀(Γ)`. If a
loxodromic `k` (`c_k < 1`, level `a`) and a conjugate `h = γ k γ⁻¹` (level `b ≠ a`) existed, the
levels `b + c⁻ⁿ (a − b)` (of `hⁿ k h⁻ⁿ`) and `a + c⁻ⁿ (b − a)` (of `kⁿ h k⁻ⁿ`) would all lie in
`Λ₀(Γ)` and be unbounded on both sides, so no point is on one side of all of them.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `L(Γ)` preserves the isotropic direction `Δ₀` | ✓ carried (`hfix`) |
| `γ₀ ∈ Γ` loxodromic | ✓ carried (`hlox`) |
| `Ω(S̃)` is on one side of the fixed hyperplanes (`I' = ]0,+∞[`) | ✓ carried, as `hside` with `Ω` nonempty |
| `Γ` discrete, `Ω(S̃)` a regular domain, `Γ` acting freely and properly | ⚠ weakened (not used) |

## SCOPE (disclosed)

* The conclusion is the invariance of one lightlike level of `Δ₀` only; the paper's `x = y = 0`
  is this lemma applied at `u₀` and at `u₁`.
* `hside` is the paper's one-sidedness of `Ω(S̃)` relative to every `Λ₀(Γ)` point, which the
  consumer derives from `blem:loxregular` (`Ω(S̃) = Ω^±(Λ)`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Planner's statement
(Barbot campaign, [10.M] integration); the eigenvalue computation repeats
`Flat.Loxodromic.minkB_linOf_of_eigen` (not importable here).
-/

namespace Causal.Flat

open Set

variable {d : ℕ}

namespace Lox

/-- `L(γ δ) = L(γ) ∘ L(δ)`. -/
theorem linOf_mul_apply (γ δ : isom d) (v : Minkowski d) :
    linOf (γ * δ) v = linOf γ (linOf δ v) := rfl

/-- The eigenvalue of `L(γ)` on the null vector `(1, u)` when `(1, u)` is an eigenvector: the
time component of `L(γ)(1, u)` (Penrose's `lorentzScale (linearPart γ) u`). -/
noncomputable def nullLevelScale (u : PenroseSphere d) (γ : isom d) : ℝ := (linOf γ (nullVec u)).1

theorem nullLevelScale_pos (u : PenroseSphere d) (γ : isom d) : 0 < nullLevelScale u γ :=
  lorentzScale_pos (linearPart γ) u

/-- A fixed point `u` of `L(γ)` on `𝒮` makes `(1, u)` an eigenvector, of eigenvalue
`nullLevelScale u γ`. -/
theorem linOf_nullVec_of_lorentzSphere_fix {γ : isom d} {u : PenroseSphere d}
    (h : lorentzSphere (linearPart γ) u = u) :
    linOf γ (nullVec u) = nullLevelScale u γ • nullVec u := by
  have e := nullVec_lorentzSphere (linearPart γ) u
  rw [h] at e
  have hc := (lorentzScale_pos (linearPart γ) u).ne'
  change nullVec u = (nullLevelScale u γ)⁻¹ • linOf γ (nullVec u) at e
  have hc' : nullLevelScale u γ ≠ 0 := hc
  conv_rhs => rw [e]
  rw [smul_smul, mul_inv_cancel₀ hc', one_smul]

/-- Along an eigenvector `n` of `L(γ)` of eigenvalue `c ≠ 0`, `⟨n | γ p⟩ = c⁻¹ ⟨n | p⟩ + ⟨n | γ 0⟩`. -/
theorem minkB_smul_of_eigen {γ : isom d} {n : Minkowski d} {c : ℝ} (hc : c ≠ 0)
    (hn : linOf γ n = c • n) (p : Minkowski d) :
    minkB n (γ • p) = c⁻¹ * minkB n p + minkB n (γ • (0 : Minkowski d)) := by
  have h := lorentz.minkB_apply (linOf_mem γ) n p
  rw [hn, minkB_smul_left] at h
  rw [smul_eq_lin_add γ p, smul_eq_lin_add γ 0, map_zero, zero_add, minkB_add_right]
  have : minkB n (linOf γ p) = c⁻¹ * minkB n p := by
    rw [← h, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  rw [this]

/-- **[10.M], `b ≡ 0` and `x(γ) = y(γ) = 0`** (l.3250–3257, l.3306–3319): a group of isometries
fixing `u₀ ∈ 𝒮`, containing a loxodromic element, with a nonempty `Ω` on one side of all the
repulsive fixed points `Λ₀(Γ)` in `𝒥`, preserves a lightlike level `{⟨(1,u₀) | ·⟩ = s₀}`. -/
theorem exists_invariant_nullLevel {d : ℕ} {Γ : Subgroup (isom d)} {u₀ : PenroseSphere d}
    (hfix : ∀ γ ∈ Γ, lorentzSphere (linearPart γ) u₀ = u₀)
    (hlox : ∃ γ ∈ Γ, IsLoxodromic (linOf γ))
    {Ω : Set (Minkowski d)} (hΩ : Ω.Nonempty)
    (hside :
      Ω ⊆ omegaPlus {w : PenroseSphere d × ℝ | ∃ γ ∈ Γ, IsLoxodromic (linOf γ) ∧
        ∃ l : ℝ, 0 < l ∧ l < 1 ∧ linOf γ (nullVec w.1) = l • nullVec w.1 ∧
          ∀ p : Minkowski d, minkB (nullVec w.1) (γ • p) - w.2 =
            l⁻¹ * (minkB (nullVec w.1) p - w.2)} ∨
      Ω ⊆ omegaMinus {w : PenroseSphere d × ℝ | ∃ γ ∈ Γ, IsLoxodromic (linOf γ) ∧
        ∃ l : ℝ, 0 < l ∧ l < 1 ∧ linOf γ (nullVec w.1) = l • nullVec w.1 ∧
          ∀ p : Minkowski d, minkB (nullVec w.1) (γ • p) - w.2 =
            l⁻¹ * (minkB (nullVec w.1) p - w.2)}) :
    ∃ s₀ : ℝ, ∀ γ ∈ Γ, ∀ p : Minkowski d,
      minkB (nullVec u₀) p = s₀ → minkB (nullVec u₀) (γ • p) = s₀ := by
  set R := {w : PenroseSphere d × ℝ | ∃ γ ∈ Γ, IsLoxodromic (linOf γ) ∧
        ∃ l : ℝ, 0 < l ∧ l < 1 ∧ linOf γ (nullVec w.1) = l • nullVec w.1 ∧
          ∀ p : Minkowski d, minkB (nullVec w.1) (γ • p) - w.2 =
            l⁻¹ * (minkB (nullVec w.1) p - w.2)} with hR
  -- the eigenvalue `c γ` and the affine action `x ↦ c⁻¹ x + β` on the levels of `(1, u₀)`
  have hE : ∀ γ ∈ Γ, linOf γ (nullVec u₀) = nullLevelScale u₀ γ • nullVec u₀ := fun γ hγ =>
    linOf_nullVec_of_lorentzSphere_fix (hfix γ hγ)
  have hpos : ∀ γ : isom d, 0 < nullLevelScale u₀ γ := nullLevelScale_pos u₀
  have hF : ∀ γ ∈ Γ, ∀ p : Minkowski d, minkB (nullVec u₀) (γ • p) =
      (nullLevelScale u₀ γ)⁻¹ * minkB (nullVec u₀) p +
        minkB (nullVec u₀) (γ • (0 : Minkowski d)) := fun γ hγ p =>
    minkB_smul_of_eigen (hpos γ).ne' (hE γ hγ) p
  have hfst : ∀ r : ℝ, (r • nullVec u₀).1 = r := fun r => by simp [nullVec]
  have hmulc : ∀ γ ∈ Γ, ∀ δ ∈ Γ,
      nullLevelScale u₀ (γ * δ) = nullLevelScale u₀ γ * nullLevelScale u₀ δ := by
    intro γ hγ δ hδ
    change (linOf γ (linOf δ (nullVec u₀))).1 = _
    rw [hE δ hδ, map_smul, hE γ hγ, smul_smul, hfst, mul_comm]
  have hone : nullLevelScale u₀ (1 : isom d) = 1 := by
    show (linOf (1 : isom d) (nullVec u₀)).1 = 1
    rfl
  have hinvc : ∀ γ ∈ Γ, nullLevelScale u₀ γ⁻¹ = (nullLevelScale u₀ γ)⁻¹ := by
    intro γ hγ
    have h := hmulc γ⁻¹ (Γ.inv_mem hγ) γ hγ
    rw [inv_mul_cancel, hone] at h
    exact eq_inv_of_mul_eq_one_left h.symm
  -- a level fixed by an element with `c < 1` is a repulsive fixed point
  have hmem : ∀ e ∈ Γ, nullLevelScale u₀ e < 1 → ∀ x : Minkowski d,
      minkB (nullVec u₀) (e • x) = minkB (nullVec u₀) x →
        ((u₀, minkB (nullVec u₀) x) : PenroseSphere d × ℝ) ∈ R := by
    intro e he hc x hx
    refine ⟨e, he, isLoxodromic_of_null_eigen (linOf_mem e) (nullVec_ne_zero u₀)
      (minkQ_nullVec u₀) (hpos e) hc.ne (hE e he), nullLevelScale u₀ e, hpos e, hc, hE e he,
      fun p => ?_⟩
    dsimp only
    have h1 := hF e he p
    have h2 := hF e he x
    linear_combination h1 - h2 + hx
  -- conjugating by `m` moves the fixed level by `m`
  have hconj : ∀ m ∈ Γ, ∀ e ∈ Γ, nullLevelScale u₀ e < 1 → ∀ x : Minkowski d,
      minkB (nullVec u₀) (e • x) = minkB (nullVec u₀) x →
        ((u₀, minkB (nullVec u₀) (m • x)) : PenroseSphere d × ℝ) ∈ R := by
    intro m hm e he hc x hx
    have hm' : m * e * m⁻¹ ∈ Γ := Γ.mul_mem (Γ.mul_mem hm he) (Γ.inv_mem hm)
    have hce : nullLevelScale u₀ (m * e * m⁻¹) = nullLevelScale u₀ e := by
      rw [hmulc _ (Γ.mul_mem hm he) _ (Γ.inv_mem hm), hmulc m hm e he, hinvc m hm]
      field_simp [(hpos m).ne']
    refine hmem _ hm' (hce ▸ hc) (m • x) ?_
    rw [mul_smul, mul_smul, inv_smul_smul, hF m hm (e • x), hF m hm x, hx]
  -- iterates: `hᵏ` multiplies the distance to its fixed level by `c⁻ᵏ`
  have hiter : ∀ e ∈ Γ, ∀ x : Minkowski d,
      minkB (nullVec u₀) (e • x) = minkB (nullVec u₀) x → ∀ (k : ℕ) (y : Minkowski d),
        minkB (nullVec u₀) (e ^ k • y) - minkB (nullVec u₀) x =
          (nullLevelScale u₀ e)⁻¹ ^ k * (minkB (nullVec u₀) y - minkB (nullVec u₀) x) := by
    intro e he x hx k
    induction k with
    | zero => intro y; simp
    | succ k ih =>
      intro y
      rw [pow_succ', mul_smul, hF e he]
      have ih' := ih y
      have h2 := hF e he x
      linear_combination (nullLevelScale u₀ e)⁻¹ * ih' - h2 + hx
  -- every real number is a level
  have hlev : ∀ s : ℝ, ∃ p : Minkowski d, minkB (nullVec u₀) p = s := fun s =>
    ⟨(-s, 0), by simp [minkB_nullVec]⟩
  -- a loxodromic element with `c < 1`
  obtain ⟨g, hg, hglox⟩ := hlox
  have hcg : nullLevelScale u₀ g ≠ 1 := by
    intro h1
    have hA : IsLoxodromic ((linearPart g : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) := by
      rwa [← linOf_eq_linearPart]
    have hv : (((linearPart g) ^ 1 : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u₀) =
        nullVec u₀ := by
      rw [pow_one, linearPart_apply]
      change linOf g (nullVec u₀) = _
      rw [hE g hg, h1, one_smul]
    have := minkQ_pos_of_fixed_pow_loxodromic hA one_ne_zero hv (nullVec_ne_zero u₀)
    rw [minkQ_nullVec] at this
    exact lt_irrefl _ this
  obtain ⟨k, hk, hck⟩ : ∃ k ∈ Γ, nullLevelScale u₀ k < 1 := by
    rcases lt_or_gt_of_ne hcg with h | h
    · exact ⟨g, hg, h⟩
    · exact ⟨g⁻¹, Γ.inv_mem hg, by rw [hinvc g hg]; exact inv_lt_one_of_one_lt₀ h⟩
  set c := nullLevelScale u₀ k with hc
  have hc0 : 0 < c := hpos k
  have hlam : 1 < c⁻¹ := one_lt_inv_iff₀.2 ⟨hc0, hck⟩
  -- the fixed level `a` of `k`
  obtain ⟨p, hp⟩ := hlev (minkB (nullVec u₀) (k • (0 : Minkowski d)) / (1 - c⁻¹))
  have hkp : minkB (nullVec u₀) (k • p) = minkB (nullVec u₀) p := by
    have h1 : (1 : ℝ) - c⁻¹ ≠ 0 := by linarith
    have hs := div_mul_cancel₀ (minkB (nullVec u₀) (k • (0 : Minkowski d))) h1
    rw [hF k hk p, hp, ← hc]
    linear_combination -hs
  refine ⟨minkB (nullVec u₀) p, fun γ hγ q hq => ?_⟩
  have hγq : minkB (nullVec u₀) (γ • q) = minkB (nullVec u₀) (γ • p) := by
    rw [hF γ hγ q, hF γ hγ p, hq]
  rw [hγq]
  by_contra hne
  set a := minkB (nullVec u₀) p with ha
  set b := minkB (nullVec u₀) (γ • p) with hb
  -- the conjugate `h = γ k γ⁻¹`, with the same `c` and the fixed level `b ≠ a`
  have hh : γ * k * γ⁻¹ ∈ Γ := Γ.mul_mem (Γ.mul_mem hγ hk) (Γ.inv_mem hγ)
  have hch : nullLevelScale u₀ (γ * k * γ⁻¹) = c := by
    rw [hmulc _ (Γ.mul_mem hγ hk) _ (Γ.inv_mem hγ), hmulc γ hγ k hk, hinvc γ hγ, hc]
    field_simp [(hpos γ).ne']
  have hhp : minkB (nullVec u₀) ((γ * k * γ⁻¹) • (γ • p)) = b := by
    rw [mul_smul, mul_smul, inv_smul_smul, hF γ hγ (k • p), hkp, hb, hF γ hγ p]
  -- the two families of fixed levels
  have hX : ∀ N : ℕ, ((u₀, minkB (nullVec u₀) ((γ * k * γ⁻¹) ^ N • p)) :
      PenroseSphere d × ℝ) ∈ R := fun N => hconj _ (Γ.pow_mem hh N) k hk hck p hkp
  have hY : ∀ N : ℕ, ((u₀, minkB (nullVec u₀) (k ^ N • (γ • p))) :
      PenroseSphere d × ℝ) ∈ R := fun N =>
    hconj _ (Γ.pow_mem hk N) _ hh (hch ▸ hck) (γ • p) hhp
  have hXv : ∀ N : ℕ, minkB (nullVec u₀) ((γ * k * γ⁻¹) ^ N • p) - b = c⁻¹ ^ N * (a - b) :=
    fun N => by
      have := hiter _ hh (γ • p) hhp N p
      rwa [hch] at this
  have hYv : ∀ N : ℕ, minkB (nullVec u₀) (k ^ N • (γ • p)) - a = c⁻¹ ^ N * (b - a) :=
    fun N => hiter k hk p hkp N (γ • p)
  -- a point of `Ω` and a large `N`
  obtain ⟨p₀, hp₀⟩ := hΩ
  set z := minkB (nullVec u₀) p₀ with hz
  have hab : 0 < |a - b| := abs_pos.2 (sub_ne_zero.2 (Ne.symm hne))
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt ((|z - a| + |z - b|) / |a - b|) hlam
  have hN' : |z - a| + |z - b| < c⁻¹ ^ N * |a - b| := (div_lt_iff₀ hab).1 hN
  have e1 := hXv N
  have e2 := hYv N
  have hsym : c⁻¹ ^ N * (b - a) = -(c⁻¹ ^ N * (a - b)) := by ring
  have k1 := neg_abs_le (z - a)
  have k2 := neg_abs_le (z - b)
  have k3 := le_abs_self (z - a)
  have k4 := le_abs_self (z - b)
  rcases hside with hs | hs
  · have hx := mem_halfPlus.1 (Set.mem_iInter₂.1 (hs hp₀) _ (hX N))
    have hy := mem_halfPlus.1 (Set.mem_iInter₂.1 (hs hp₀) _ (hY N))
    dsimp only at hx hy
    rcases lt_or_gt_of_ne (sub_ne_zero.2 (Ne.symm hne) : a - b ≠ 0) with h | h
    · rw [abs_of_neg h] at hN'
      have : -(a - b) = b - a := by ring
      linarith
    · rw [abs_of_pos h] at hN'
      linarith
  · have hx := mem_halfMinus.1 (Set.mem_iInter₂.1 (hs hp₀) _ (hX N))
    have hy := mem_halfMinus.1 (Set.mem_iInter₂.1 (hs hp₀) _ (hY N))
    dsimp only at hx hy
    rcases lt_or_gt_of_ne (sub_ne_zero.2 (Ne.symm hne) : a - b ≠ 0) with h | h
    · rw [abs_of_neg h] at hN'
      linarith
    · rw [abs_of_pos h] at hN'
      linarith

end Lox

end Causal.Flat
