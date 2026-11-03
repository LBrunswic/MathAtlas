import GX.BTZ.LocalModel
import Causal.Flat.Loxodromic
import Causal.Flat.Nonloxodromic
import Causal.Flat.Classification
import Mathlib.GroupTheory.Commutator.Basic

/-!
# `GX.BTZ.Holonomy` — the holonomy of `Reg M`: faithful, discrete, torsion-free, loxodromic

Package WP-41m (WAVE5-PLAN.md, WP-39m). `papers/gx`, §4.6, the Barbot step of the proof of the
main theorem (`RamcovGX.tex:2378–2380`), and §4.3's uniformization prose (l.2228–2232).
**No ledger label is certified in full here, so nothing is marked.** One label is served in part:

* `theo:globally_hyperbolic_cauchy_complete_cauchy_maximal` — `RamcovGX.tex:2363`, partial (its
  proof's Barbot step, l.2378–2380, for `Reg M`; the theorem itself is WP-39n's):
  `GX.e0RegM_holonomy` — for `Reg M` GH and Cauchy-complete with `π₁(Reg M)` not metabelian,
  and for **every** developing pair `(𝒟, ρ)` of `Reg M` (the given one, not merely some one;
  `GX.e0RegM_exists_holonomy` is the existential corollary): `𝒟|reg` injective, `ρ` faithful (`GX.holonomy_injective`), discrete (`GX.holonomy_discrete`),
  torsion-free (`GX.holonomy_torsionFree`), a **loxodromic element proved** (DEC-75,
  `GX.exists_isLoxodromic_of_not_metabelian`), `𝒟(Reg M̃) ⊆ Ω⁺(Λ) = ⋂_j I⁺(Π_j)`, the
  `Γ`-invariance of the family of lightlike planes of `Λ(Γ)` as a conjunct
  (`GX.omegaPlus_eq_iInter_Iplus`, `GX.limitSetJ_nullPlane_invariant`), `Γ` free and properly
  discontinuous on it.

Proved here, of general use (0 `sorry`, standard axioms only):

* **2+1 elementary groups (DEC-75)**: `GX.lorentz2_noLox_classification` — a subgroup of
  `SO₀(1, 2)` without loxodromic element fixes a timelike or a nonzero null vector and is
  commutative; hence **`GX.benoistNoLox_two : Causal.Flat.BenoistNoLox 2`**, Barbot's external
  Prop 9.1 (Benoist) discharged in 2+1 with finite index `1`. Two ping-pongs:
  `GX.exists_isLoxodromic_pow_mul_of_fix_null` (a null rotation `A ≠ 1`, `B` moving its null line:
  `tr(Aⁿ B) → ∞`) and `GX.isLoxodromic_commutator_of_fix_timelike` (`tr [A, B] − 3 =
  (1 − c)(β − 1)(2(β + 1) − (1 + c)(β − 1)) > 0`), through `GX.isLoxodromic_of_three_lt_trace`
  (`tr > 3` ⇒ loxodromic, from the characteristic polynomial `GX.lorentz2_det_sub_smul`).
* `GX.isMetabelianOn_of_noLox`: `Γ ≤ Isom(𝐌³)` with no loxodromic linear part is metabelian.
* **Finding** `GX.exists_nonabelian_subgroup_noLox`: a non-abelian subgroup of `Isom(𝐌³)` with no
  loxodromic element — "non-abelian" (DEC-76) does not suffice algebraically.
* `GX.e0RegMFlat`: `Reg M` as a `Causal.Flat.FlatSpacetime 2`.
* `GX.holonomy_package_of_isCauchyComplete`: Barbot's uniformization in 2+1 from the paper's
  hypotheses (GH, Cauchy-complete in DEC-31's induced-length sense, `π₁` not metabelian), for an
  arbitrary given developing pair (`GX.exists_holonomy_package_of_isCauchyComplete`: the ∃ form).

> From Theorem 3 of \cite{brunswic2021cauchy}, the regular part of $M$ is globally hyperbolic,
> Cauchy-maximal and Cauchy-complete; therefore, by general result of Barbot
> \cite{barbot_globally_2004}, the restriction $\D_{|\reg(\widetilde M)}$ is injective, $\rho$ is
> faithful, discrete and without torsion and $$ \Omega:=\D(\reg(\widetilde M))
> =\bigcap_{j\in I} I^+(\Pi_j)$$ for some $\Gamma$-invariant family $(\Pi_j)_{j\in J}$ of
> lightlike planes. Furthermore, $\Gamma$ acts totally discontinuously and freely on $\Omega$.
> (`RamcovGX.tex:2378–2380`)

> In this case, there exists a representation $\pi_1(\Sigma)\xrightarrow{~~\rho~~} \GG\ltimes
> \RR^3$ whose linear part is discrete and faithful as well as a $\rho$-invariant convex domain
> $\Omega\subset \E^{1,2}$ such that $M\simeq \rho\backslash \Omega$ and $\widetilde M \simeq
> \Omega$. (l.2230–2231)

## Hypothesis checklist

| paper / dispatch | here |
|---|---|
| `reg(M)` GH, Cauchy-complete (from B21 Thm 3, l.2378) | ⚠ carried as hypotheses `GH (e0RegMFlat M)`, `IsCauchyComplete 2 (e0RegMFlat M)` (DEC-31: induced length); their derivation from `M` is downstream (WP-39j/k) |
| `reg(M)` Cauchy-maximal (l.2378) | ⚠ weakened (assumes less): not used (Barbot's `⊆`; equality needs absolute maximality, SCOPE D-12(b), WP-39k) |
| a loxodromic element (Barbot's Lemma 10.2 needs one; DEC-75) | ✓ **proved** from `π₁(Reg M)` not metabelian (`exists_isLoxodromic_of_not_metabelian`), no external |
| `π₁(Σ∖sing)` non-abelian, `s ≥ 1` (DEC-76) | ⚠ strengthened: `π₁(Reg M)` **not metabelian**; non-abelian alone is refuted algebraically (`exists_nonabelian_subgroup_noLox`); the two agree for `π₁` of a punctured surface (free), not formalized (SCOPE (a)) |
| `ρ` faithful | ✓ `holonomy_injective`: `𝒟` injective (Prop 8.12) and `𝒟 ∘ γ = ρ(γ) ∘ 𝒟` |
| `ρ` discrete | ✓ `holonomy_discrete` (`isomTopology`, Barbot §8) |
| `ρ` without torsion | ✓ `holonomy_torsionFree`: free action on the convex `Ω^±(Λ) ⊇ 𝒟(M̃)`, barycentre of a finite orbit |
| `Ω = ⋂ I⁺(Π_j)`, `Π_j` lightlike planes, `Γ`-invariant | ✓ `Ω⁺(Λ) = ⋂ I⁺(Π_w)` (`omegaPlus_eq_iInter_Iplus`), the invariance as a conjunct of the package (`limitSetJ_nullPlane_invariant`); ⚠ **conclusion weakened (missing assertion, WP-39n)**: `𝒟(Reg M̃) ⊆ Ω` (Barbot Prop 8.12), not `=` |
| "up to time reversal" (dropped by DEC-77 (a)) | ⚠ **conclusion weakened (missing assertion, WP-39n)**: the future/past disjunction is concluded; the selection of the future case from `sing ≠ ∅` is WP-39n's |
| the given developing pair `(D, ρ)` (l.2363–2365, 2378) | ✓ every developing pair is a hypothesis (`hpair`), not an `∃` |
| `Γ` acts totally discontinuously and freely on `Ω` | ✓ `ActsFreelyProperlyOn` (Cor 10.3) |

## SCOPE (disclosed)

* (a) DEC-76's hypothesis is consumed as "`π₁(Reg M)` (the deck group of `Reg M`'s universal cover)
  is not metabelian" (`IsMetabelianGroup`; implied by non-solvable,
  `not_isMetabelianGroup_of_not_isSolvable`). The passage from "`π₁(Σ∖sing)` non-abelian, `s ≥ 1`"
  needs `π₁(Reg M) ≅ π₁(Σ∖sing)` (the splitting `Reg M ≅ Σ* × ℝ`) and that a non-abelian `π₁` of
  a punctured surface is free of rank `≥ 2`; neither is built here. The counterexample shows the
  algebraic step cannot be done from non-abelianness alone.
* (b) The theorem's `𝒟` on `M̃` (BTZ points included) and the future-case selection are WP-39n's.
* (c') **Not proved here**: §4.3's "linear part is discrete and faithful" (l.2230–2231). The file
  proves `ρ` faithful and discrete in `Isom(𝐌³)`, not that `linOf ∘ ρ` is injective or has discrete
  image in `SO₀(1, 2)`; the quote is context for the uniformization, not a certified assertion.
* (c) The 2+1 algebra is proved for all of `SO₀(1, 2)` without discreteness (no Fuchsian theory):
  it is the trace argument of `PSL₂ℝ`, carried out in `SO₀(1, 2)` through null and orthonormal
  frames (`IsNullFrame2`, `IsOrthoFrame2`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; lean-causal `ca2ad78`
(`lake-manifest.json`).
-/

namespace GX

open Set Function

section TwoOneFrame

open Causal.Flat

/-- A null frame of `𝐌³`: `u`, `w` null with `⟨u | w⟩ = −1`, `e` a unit spacelike vector
orthogonal to both. -/
structure IsNullFrame2 (u e w : Causal.Minkowski 2) : Prop where
  uu : minkB u u = 0
  ww : minkB w w = 0
  uw : minkB u w = -1
  ee : minkB e e = 1
  ue : minkB u e = 0
  we : minkB w e = 0

variable {u e w : Causal.Minkowski 2}

theorem IsNullFrame2.wu (F : IsNullFrame2 u e w) : minkB w u = -1 := by rw [minkB_comm]; exact F.uw
theorem IsNullFrame2.eu (F : IsNullFrame2 u e w) : minkB e u = 0 := by rw [minkB_comm]; exact F.ue
theorem IsNullFrame2.ew (F : IsNullFrame2 u e w) : minkB e w = 0 := by rw [minkB_comm]; exact F.we

theorem finrank_minkowski_two : Module.finrank ℝ (Causal.Minkowski 2) = 3 := by
  simp [Causal.Minkowski, Module.finrank_prod]

theorem IsNullFrame2.linearIndependent (F : IsNullFrame2 u e w) :
    LinearIndependent ℝ ![u, e, w] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h0 := congrArg (fun z => minkB z w) hg
  have h1 := congrArg (fun z => minkB z e) hg
  have h2 := congrArg (fun z => minkB z u) hg
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, minkB_add_left, minkB_smul_left,
    minkB_zero_left, F.uu, F.ww, F.uw, F.ee, F.ue, F.we, F.wu, F.eu, F.ew] at h0 h1 h2
  intro i
  fin_cases i <;> simp <;> linarith

/-- The basis of a null frame. -/
noncomputable def IsNullFrame2.basis (F : IsNullFrame2 u e w) : Module.Basis (Fin 3) ℝ (Causal.Minkowski 2) :=
  basisOfLinearIndependentOfCardEqFinrank F.linearIndependent (by simp)

theorem IsNullFrame2.basis_apply (F : IsNullFrame2 u e w) (i : Fin 3) :
    F.basis i = ![u, e, w] i := by
  simp [IsNullFrame2.basis, coe_basisOfLinearIndependentOfCardEqFinrank]


/-- The three frame coordinates: `x = c₀ u + c₁ e + c₂ w`. -/
noncomputable def frameCoord (u e w x : Causal.Minkowski 2) : Fin 3 → ℝ :=
  ![-minkB x w, minkB x e, -minkB x u]

/-- **The frame expansion**: `x = −⟨x|w⟩ u + ⟨x|e⟩ e − ⟨x|u⟩ w`. -/
theorem IsNullFrame2.expand (F : IsNullFrame2 u e w) (x : Causal.Minkowski 2) :
    x = (-minkB x w) • u + minkB x e • e + (-minkB x u) • w := by
  set y := x - ((-minkB x w) • u + minkB x e • e + (-minkB x u) • w) with hy
  suffices hy0 : y = 0 by rw [hy, sub_eq_zero] at hy0; exact hy0
  have hyu : minkB u y = 0 := by
    simp only [hy, minkB_sub_right, minkB_add_right, minkB_smul_right, F.uu, F.ue, F.uw]
    rw [minkB_comm]; ring
  have hye : minkB e y = 0 := by
    simp only [hy, minkB_sub_right, minkB_add_right, minkB_smul_right, F.eu, F.ee, F.ew]
    rw [minkB_comm]; ring
  have hyw : minkB w y = 0 := by
    simp only [hy, minkB_sub_right, minkB_add_right, minkB_smul_right, F.wu, F.we, F.ww]
    rw [minkB_comm]; ring
  apply eq_zero_of_forall_minkB
  intro z
  have hz := F.basis.sum_repr z
  rw [← hz]
  simp only [Fin.sum_univ_three, F.basis_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, minkB_add_left, minkB_smul_left,
    hyu, hye, hyw]
  ring

/-- **The Gram formula in a null frame**. -/
theorem IsNullFrame2.minkB_eq (F : IsNullFrame2 u e w) (x y : Causal.Minkowski 2) :
    minkB x y = -(minkB x w * minkB y u) - minkB x u * minkB y w + minkB x e * minkB y e := by
  conv_lhs => rw [F.expand x, F.expand y]
  simp only [minkB_add_left, minkB_add_right, minkB_smul_left, minkB_smul_right, F.uu, F.ue,
    F.uw, F.eu, F.ee, F.ew, F.wu, F.we, F.ww]
  ring

theorem IsNullFrame2.repr_apply (F : IsNullFrame2 u e w) (x : Causal.Minkowski 2) (i : Fin 3) :
    F.basis.repr x i = frameCoord u e w x i := by
  have hx : x = ∑ j, frameCoord u e w x j • F.basis j := by
    simp only [Fin.sum_univ_three, F.basis_apply, frameCoord, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    exact F.expand x
  conv_lhs => rw [hx]
  rw [F.basis.repr_sum_self]

/-- **The trace in a null frame**: `tr f = −⟨f u|w⟩ + ⟨f e|e⟩ − ⟨f w|u⟩`. -/
theorem IsNullFrame2.trace_eq (F : IsNullFrame2 u e w) (f : Causal.Minkowski 2 →ₗ[ℝ] Causal.Minkowski 2) :
    LinearMap.trace ℝ _ f = -minkB (f u) w + minkB (f e) e - minkB (f w) u := by
  rw [LinearMap.trace_eq_matrix_trace ℝ F.basis, Matrix.trace_fin_three]
  simp only [LinearMap.toMatrix_apply, F.repr_apply, F.basis_apply, frameCoord,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]
  ring

/-- The matrix of `f` in a null frame. -/
theorem IsNullFrame2.toMatrix_apply (F : IsNullFrame2 u e w)
    (f : Causal.Minkowski 2 →ₗ[ℝ] Causal.Minkowski 2) (i j : Fin 3) :
    LinearMap.toMatrix F.basis F.basis f i j = frameCoord u e w (f (![u, e, w] j)) i := by
  rw [LinearMap.toMatrix_apply, F.repr_apply, F.basis_apply]

/-- **Every nonzero null vector of `𝐌³` is the first vector of a null frame.** -/
theorem exists_isNullFrame2 {u : Causal.Minkowski 2} (hu0 : u ≠ 0) (hq : Causal.Flat.minkQ u = 0) :
    ∃ e w, IsNullFrame2 u e w := by
  obtain ⟨t, x⟩ := u
  have ht : t ≠ 0 := fun h => hu0 (eq_zero_of_fst_eq_zero (v := (t, x)) h hq.le)
  have hx : x 0 ^ 2 + x 1 ^ 2 = t ^ 2 := by
    have := hq
    simp only [Causal.Flat.minkQ, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] at this
    linarith
  refine ⟨((0 : ℝ), t⁻¹ • (WithLp.toLp 2 ![-(x 1), x 0] : EuclideanSpace ℝ (Fin 2))),
    (2 * t ^ 2)⁻¹ • ((t, -x) : Causal.Minkowski 2), ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [minkB, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, inner_smul_left,
      inner_smul_right, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial,
      Matrix.cons_val_zero, Matrix.cons_val_one, inner_neg_left, inner_neg_right] <;>
    field_simp <;> nlinarith [hx]

/-- A standard nonzero null vector of `𝐌³`. -/
noncomputable def stdNull2 : Causal.Minkowski 2 := ((1 : ℝ), EuclideanSpace.single 0 1)

theorem stdNull2_ne_zero : stdNull2 ≠ 0 := fun h => by
  have := congrArg Prod.fst h; simp [stdNull2] at this

theorem minkQ_stdNull2 : Causal.Flat.minkQ stdNull2 = 0 := by
  simp [Causal.Flat.minkQ, stdNull2]

/-- A null frame of `𝐌³`. -/
theorem exists_isNullFrame2_std : ∃ e w, IsNullFrame2 stdNull2 e w :=
  exists_isNullFrame2 stdNull2_ne_zero minkQ_stdNull2

variable {A : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2}

/-- `A⁻¹` is the `minkB`-adjoint of `A`. -/
theorem minkB_symm_apply (hA : A ∈ lorentz 2) (x y : Causal.Minkowski 2) :
    minkB (A.symm x) y = minkB x (A y) := by
  rw [← minkB_map hA.1 (A.symm x) y, LinearEquiv.apply_symm_apply]

/-- **`tr A⁻¹ = tr A`** on `SO₀(1, 2)`. -/
theorem lorentz2_trace_symm (hA : A ∈ lorentz 2) :
    LinearMap.trace ℝ _ (A.symm : Causal.Minkowski 2 →ₗ[ℝ] Causal.Minkowski 2) =
      LinearMap.trace ℝ _ (A : Causal.Minkowski 2 →ₗ[ℝ] Causal.Minkowski 2) := by
  obtain ⟨e, w, F⟩ := exists_isNullFrame2_std
  rw [F.trace_eq, F.trace_eq]
  simp only [LinearEquiv.coe_coe, minkB_symm_apply hA]
  rw [minkB_comm stdNull2 (A w), minkB_comm e (A e), minkB_comm w (A stdNull2)]
  ring

/-- **The characteristic polynomial of `A ∈ SO₀(1, 2)`**:
`det (A − l) = −(l − 1)(l² − (tr A − 1) l + 1)`. -/
theorem lorentz2_det_sub_smul (hA : A ∈ lorentz 2) (l : ℝ) :
    LinearMap.det ((A : Causal.Minkowski 2 →ₗ[ℝ] Causal.Minkowski 2) - l • LinearMap.id) =
      -(l - 1) * (l ^ 2 - (LinearMap.trace ℝ _ (A : Causal.Minkowski 2 →ₗ[ℝ] Causal.Minkowski 2) - 1) * l + 1) := by
  obtain ⟨e, w, F⟩ := exists_isNullFrame2_std
  set b := F.basis
  set M := LinearMap.toMatrix b b (A : Causal.Minkowski 2 →ₗ[ℝ] Causal.Minkowski 2) with hM
  set N := LinearMap.toMatrix b b (A.symm : Causal.Minkowski 2 →ₗ[ℝ] Causal.Minkowski 2) with hN
  have hMN : M * N = 1 := by
    rw [hM, hN, ← LinearMap.toMatrix_mul]
    have : (A : Causal.Minkowski 2 →ₗ[ℝ] Causal.Minkowski 2) * (A.symm : Causal.Minkowski 2 →ₗ[ℝ] _) =
        LinearMap.id := LinearMap.ext fun x => A.apply_symm_apply x
    rw [this, LinearMap.toMatrix_id]
  have hdet : M.det = 1 := by rw [hM, LinearMap.det_toMatrix]; exact hA.2.2
  have hadj : M.adjugate = N := by
    calc M.adjugate = M.adjugate * (M * N) := by rw [hMN, Matrix.mul_one]
      _ = (M.adjugate * M) * N := by rw [Matrix.mul_assoc]
      _ = N := by rw [Matrix.adjugate_mul, hdet, one_smul, Matrix.one_mul]
  have htr : N.trace = M.trace := by
    rw [hN, hM, ← LinearMap.trace_eq_matrix_trace, ← LinearMap.trace_eq_matrix_trace]
    exact lorentz2_trace_symm hA
  rw [← hadj] at htr
  rw [LinearMap.trace_eq_matrix_trace ℝ b, ← hM, ← LinearMap.det_toMatrix b, map_sub, map_smul,
    LinearMap.toMatrix_id, ← hM]
  rw [Matrix.adjugate_fin_three] at htr
  rw [Matrix.det_fin_three] at hdet ⊢
  simp [Matrix.trace_fin_three] at htr ⊢
  linear_combination hdet - l * htr

/-- **A trace `> 3` makes `A ∈ SO₀(1, 2)` loxodromic**: the root `l > 1` of
`l² − (tr A − 1) l + 1` is an eigenvalue, and its eigenvectors are null. -/
theorem isLoxodromic_of_three_lt_trace (hA : A ∈ lorentz 2)
    (ht : 3 < LinearMap.trace ℝ _ (A : Causal.Minkowski 2 →ₗ[ℝ] Causal.Minkowski 2)) :
    IsLoxodromic A := by
  set t := LinearMap.trace ℝ _ (A : Causal.Minkowski 2 →ₗ[ℝ] Causal.Minkowski 2)
  set D := (t - 1) ^ 2 - 4 with hD
  have hD0 : 0 ≤ D := by nlinarith
  set s := Real.sqrt D
  have hs : s ^ 2 = D := Real.sq_sqrt hD0
  have hs0 : 0 ≤ s := Real.sqrt_nonneg D
  set l := ((t - 1) + s) / 2
  have hl1 : 1 < l := by simp only [l]; linarith
  have hroot : l ^ 2 - (t - 1) * l + 1 = 0 := by simp only [l]; nlinarith
  have hdet := lorentz2_det_sub_smul hA l
  rw [hroot, mul_zero] at hdet
  obtain ⟨v, hvk, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.bot_lt_ker_of_det_eq_zero hdet).ne'
  have hAv : A v = l • v := by
    have := hvk
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      LinearEquiv.coe_coe, sub_eq_zero] at this
    exact this
  have hq : Causal.Flat.minkQ v = 0 := by
    have h1 := hA.1 v
    rw [hAv, Causal.Flat.minkQ_smul] at h1
    have : (l ^ 2 - 1) * Causal.Flat.minkQ v = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left (by nlinarith)
  exact isLoxodromic_of_null_eigen hA hv0 hq (by linarith) hl1.ne' hAv

/-! ### The stabiliser of a null vector in `SO₀(1, 2)` -/

/-- `A` is the **null rotation of parameter `a`** in the frame `(u, e, w)`:
`u ↦ u`, `e ↦ a u + e`, `w ↦ (a²/2) u + a e + w`. -/
structure IsNullRot2 (u e w : Causal.Minkowski 2) (a : ℝ) (A : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2) : Prop where
  hu : A u = u
  he : A e = a • u + e
  hw : A w = (a ^ 2 / 2) • u + a • e + w

theorem IsNullFrame2.ext (F : IsNullFrame2 u e w) {X Y : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2}
    (hu : X u = Y u) (he : X e = Y e) (hw : X w = Y w) : X = Y := by
  have : (X : Causal.Minkowski 2 →ₗ[ℝ] Causal.Minkowski 2) = Y := by
    refine F.basis.ext fun i => ?_
    fin_cases i <;> simp [F.basis_apply, hu, he, hw]
  exact LinearEquiv.toLinearMap_injective this

/-- **The stabiliser of a null vector in `SO₀(1, 2)` is the group of null rotations**. The
determinant excludes the reflections fixing `u`. -/
theorem IsNullFrame2.isNullRot2_of_fix (F : IsNullFrame2 u e w) (hA : A ∈ lorentz 2)
    (hAu : A u = u) : IsNullRot2 u e w (-minkB (A e) w) A := by
  have hQ := hA.1
  have h1 : minkB (A e) u = 0 := by rw [← hAu, minkB_map hQ]; exact F.eu
  have h2 : minkB (A w) u = -1 := by rw [← hAu, minkB_map hQ]; exact F.wu
  have h3 : minkB (A e) (A e) = 1 := by rw [minkB_map hQ]; exact F.ee
  have h4 : minkB (A e) (A w) = 0 := by rw [minkB_map hQ]; exact F.ew
  have h5 : minkB (A w) (A w) = 0 := by rw [minkB_map hQ]; exact F.ww
  rw [F.minkB_eq, h1] at h3
  rw [F.minkB_eq, h1, h2] at h4
  rw [F.minkB_eq, h2] at h5
  -- the determinant in the frame is `⟨A e | e⟩`
  have hdet : minkB (A e) e = 1 := by
    have h := hA.2.2
    rw [← LinearMap.det_toMatrix F.basis, Matrix.det_fin_three] at h
    simp only [F.toMatrix_apply, frameCoord, LinearEquiv.coe_coe, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, hAu, F.uu,
      F.ue, F.uw, h1, h2] at h
    linarith
  rw [hdet] at h3 h4
  have hβ : minkB (A w) e = -minkB (A e) w := by linarith
  have hα : -minkB (A w) w = (-minkB (A e) w) ^ 2 / 2 := by rw [← hβ]; linarith
  refine ⟨hAu, ?_, ?_⟩
  · conv_lhs => rw [F.expand (A e)]
    rw [hdet, h1, neg_zero, zero_smul, add_zero, one_smul]
  · conv_lhs => rw [F.expand (A w)]
    rw [hα, hβ, h2, neg_neg, one_smul]

theorem IsNullRot2.mul {a b : ℝ} {X Y : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2}
    (hX : IsNullRot2 u e w a X) (hY : IsNullRot2 u e w b Y) : IsNullRot2 u e w (a + b) (X * Y) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [LinearEquiv.mul_apply, hY.hu, hX.hu]
  · rw [LinearEquiv.mul_apply, hY.he, map_add, map_smul, hX.hu, hX.he]; module
  · rw [LinearEquiv.mul_apply, hY.hw, map_add, map_add, map_smul, map_smul, hX.hu, hX.he, hX.hw]
    module

theorem IsNullRot2.one : IsNullRot2 u e w 0 (1 : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2) :=
  ⟨rfl, by simp, by simp⟩

theorem IsNullRot2.pow {a : ℝ} {X : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2}
    (hX : IsNullRot2 u e w a X) (n : ℕ) : IsNullRot2 u e w (n * a) (X ^ n) := by
  induction n with
  | zero => simpa using IsNullRot2.one
  | succ n ih =>
    rw [pow_succ]
    have := ih.mul hX
    convert this using 1; push_cast; ring

theorem IsNullRot2.symm_apply {a : ℝ} {X : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2}
    (hX : IsNullRot2 u e w a X) :
    X.symm u = u ∧ X.symm e = (-a) • u + e ∧ X.symm w = (a ^ 2 / 2) • u + (-a) • e + w := by
  refine ⟨?_, ?_, ?_⟩
  · conv_lhs => rw [← hX.hu]
    exact X.symm_apply_apply u
  · apply X.injective
    rw [X.apply_symm_apply, map_add, map_smul, hX.hu, hX.he]; module
  · apply X.injective
    rw [X.apply_symm_apply, map_add, map_add, map_smul, map_smul, hX.hu, hX.he, hX.hw]; module

theorem IsNullRot2.eq_one {X : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2} (F : IsNullFrame2 u e w)
    (hX : IsNullRot2 u e w 0 X) : X = 1 :=
  F.ext (by rw [hX.hu]; rfl) (by rw [hX.he]; simp) (by rw [hX.hw]; simp)

/-- **The trace of `X B` for a null rotation `X` of parameter `s`**: a quadratic polynomial in `s`
with leading coefficient `−⟨u | B u⟩ / 2`. -/
theorem IsNullRot2.trace_mul (F : IsNullFrame2 u e w) {s : ℝ}
    {X : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2} (hX : IsNullRot2 u e w s X)
    (hXL : X ∈ lorentz 2) (B : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2) :
    LinearMap.trace ℝ _ ((X * B : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2) :
        Causal.Minkowski 2 →ₗ[ℝ] Causal.Minkowski 2) =
      -(minkB u (B u)) / 2 * s ^ 2 + (minkB e (B u) - minkB u (B e)) * s +
        (-minkB w (B u) + minkB e (B e) - minkB u (B w)) := by
  rw [F.trace_eq]
  simp only [LinearEquiv.coe_coe, LinearEquiv.mul_apply]
  have hadj : ∀ y z, minkB (X y) z = minkB (X.symm z) y := fun y z => by
    rw [minkB_symm_apply hXL, minkB_comm]
  obtain ⟨h1, h2, h3⟩ := hX.symm_apply
  rw [hadj, hadj, hadj, h1, h2, h3]
  simp only [minkB_add_left, minkB_smul_left]
  ring

/-- **Two elements of `SO₀(1, 2)` fixing the same nonzero null vector commute.** -/
theorem lorentz2_commute_of_fix_null {u : Causal.Minkowski 2} (hu0 : u ≠ 0)
    (hq : Causal.Flat.minkQ u = 0) {X Y : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2}
    (hX : X ∈ lorentz 2) (hY : Y ∈ lorentz 2) (hXu : X u = u) (hYu : Y u = u) : X * Y = Y * X := by
  obtain ⟨e, w, F⟩ := exists_isNullFrame2 hu0 hq
  have h1 := (F.isNullRot2_of_fix hX hXu).mul (F.isNullRot2_of_fix hY hYu)
  have h2 := (F.isNullRot2_of_fix hY hYu).mul (F.isNullRot2_of_fix hX hXu)
  refine F.ext (by rw [h1.hu, h2.hu]) (by rw [h1.he, h2.he]; module) ?_
  rw [h1.hw, h2.hw]; module

/-- Two null vectors with `⟨x | y⟩ = 0`, `y ≠ 0`, are proportional: `x = c y`. -/
theorem IsNullFrame2.eq_smul_of_null_orth (F : IsNullFrame2 u e w) {x : Causal.Minkowski 2}
    (hxq : Causal.Flat.minkQ x = 0) (hxu : minkB x u = 0) : x = (-minkB x w) • u := by
  have hq : minkB x x = 0 := by rw [← Causal.Flat.minkQ_eq_minkB]; exact hxq
  rw [F.minkB_eq, hxu] at hq
  have he : minkB x e = 0 := by nlinarith
  conv_lhs => rw [F.expand x]
  rw [he, hxu]; simp

/-- **The parabolic ping-pong of `SO₀(1, 2)`**: if `A` fixes the future null `u`, `A ≠ 1`, and `B`
moves `u`, then some `Aⁿ B` (`n ∈ ℕ`) or `B` itself is loxodromic. -/
theorem exists_isLoxodromic_pow_mul_of_fix_null {u : Causal.Minkowski 2} (hu0 : u ≠ 0)
    (huF : IsFutureCausal u) (hq : Causal.Flat.minkQ u = 0)
    {A B : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2} (hA : A ∈ lorentz 2) (hB : B ∈ lorentz 2)
    (hAu : A u = u) (hA1 : A ≠ 1) (hBu : B u ≠ u) :
    IsLoxodromic B ∨ ∃ n : ℕ, IsLoxodromic (A ^ n * B) := by
  obtain ⟨e, w, F⟩ := exists_isNullFrame2 hu0 hq
  set a := -minkB (A e) w
  have hNA := F.isNullRot2_of_fix hA hAu
  have ha : a ≠ 0 := fun h => hA1 (IsNullRot2.eq_one F (h ▸ hNA))
  have hBuF : IsFutureCausal (B u) := lorentz.isFutureCausal_apply hB huF
  have hBuq : Causal.Flat.minkQ (B u) = 0 := by rw [hB.1]; exact hq
  have hBu0 : B u ≠ 0 := fun h => hu0 (B.injective (by rw [h, map_zero]))
  rcases eq_or_ne (minkB (B u) u) 0 with h0 | h0
  · -- `B u ∥ u`: an eigenvalue `≠ 1` on a null vector
    left
    have hBc := F.eq_smul_of_null_orth hBuq h0
    have hc := lorentz.eigen_pos_of_null hB hu0 hq hBc
    refine isLoxodromic_of_null_eigen hB hu0 hq hc ?_ hBc
    intro h1; apply hBu; rw [hBc, h1, one_smul]
  · right
    have hneg : minkB u (B u) < 0 := by
      rw [minkB_comm]
      exact lt_of_le_of_ne (minkB_nonpos_of_future hBuF huF) h0
    set κ := -(minkB u (B u)) / 2 with hκ
    have hκ0 : 0 < κ := by rw [hκ]; linarith
    set β := minkB e (B u) - minkB u (B e)
    set γ := -minkB w (B u) + minkB e (B e) - minkB u (B w)
    set R := (|β| + |γ| + 3) / κ + 1
    obtain ⟨n, hn⟩ := exists_nat_gt (R / |a|)
    have ha' : 0 < |a| := abs_pos.2 ha
    refine ⟨n, isLoxodromic_of_three_lt_trace ?_ ?_⟩
    · exact (lorentz 2).mul_mem ((lorentz 2).pow_mem hA n) hB
    · have hpow := hNA.pow n
      rw [IsNullRot2.trace_mul F hpow ((lorentz 2).pow_mem hA n) B]
      set s := (n : ℝ) * a
      have hs : R < |s| := by
        rw [abs_mul, Nat.abs_cast]
        rw [div_lt_iff₀ ha'] at hn; linarith
      have hR1 : 1 ≤ R := by
        have : 0 ≤ (|β| + |γ| + 3) / κ := div_nonneg (by positivity) hκ0.le
        simp only [R]; linarith
      have hκR : |β| + |γ| + 3 ≤ κ * (R - 1) := by
        simp only [R, add_sub_cancel_right]; rw [mul_div_cancel₀ _ hκ0.ne']
      have hsβ : -(|β| * |s|) ≤ β * s := by
        rw [← abs_mul]; exact neg_abs_le (β * s)
      have hg := neg_abs_le γ
      have hs2 : s ^ 2 = |s| * |s| := by rw [← sq, sq_abs]
      have hX : |γ| + 3 < κ * |s| - |β| := by nlinarith
      have hs1 : 1 < |s| := by linarith
      have hXs : |γ| + 3 < |s| * (κ * |s| - |β|) := by
        have := mul_pos (sub_pos.2 hs1) (show 0 < κ * |s| - |β| by linarith [abs_nonneg γ])
        nlinarith
      show 3 < κ * s ^ 2 + β * s + γ
      rw [hs2]; nlinarith

/-- A future representative of a nonzero null line. -/
theorem exists_future_null_rep {v : Causal.Minkowski 2} (hv0 : v ≠ 0) (hq : Causal.Flat.minkQ v = 0) :
    ∃ uf : Causal.Minkowski 2, uf ≠ 0 ∧ IsFutureCausal uf ∧ Causal.Flat.minkQ uf = 0 ∧
      (uf = v ∨ uf = -v) := by
  have hv1 : v.1 ≠ 0 := fun h => hv0 (eq_zero_of_fst_eq_zero h hq.le)
  rcases lt_or_gt_of_ne hv1 with h | h
  · have hn : Causal.Flat.minkQ (-v) = Causal.Flat.minkQ v := by simp [Causal.Flat.minkQ]
    exact ⟨-v, neg_ne_zero.2 hv0, ⟨by simp; linarith, by rw [hn, hq]⟩, by rw [hn, hq], Or.inr rfl⟩
  · exact ⟨v, hv0, ⟨h.le, hq.le⟩, hq, Or.inl rfl⟩

/-- **A parabolic element fixes a nonzero null vector and is not the identity.** -/
theorem exists_fixed_null_of_isParabolic {A : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2}
    (hA : A ∈ lorentz 2) (h : IsParabolic A) :
    A ≠ 1 ∧ ∃ v : Causal.Minkowski 2, v ≠ 0 ∧ Causal.Flat.minkQ v = 0 ∧ A v = v := by
  obtain ⟨v₁, v₀, hv0, h1, h0⟩ := h.exists_jordan
  refine ⟨fun hA1 => hv0 ?_, v₀, hv0, ?_, h0⟩
  · rw [hA1] at h1; simpa using h1.symm
  · have h2 := minkB_map hA.1 v₁ v₀
    rw [h1, h0, minkB_add_left] at h2
    rw [Causal.Flat.minkQ_eq_minkB]; linarith

/-- **2+1, the subgroup form (DEC-75)**: a subgroup of `SO₀(1, 2)` with no loxodromic element and
a nontrivial element fixing a nonzero null vector `v` fixes `v` pointwise. -/
theorem lorentz2_fix_of_noLox {G : Subgroup (lorentz 2)}
    (hG : ∀ A ∈ G, ¬IsLoxodromic (A : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2))
    {A₀ : lorentz 2} (hA₀ : A₀ ∈ G) (hA₀1 : A₀ ≠ 1) {v : Causal.Minkowski 2} (hv0 : v ≠ 0)
    (hq : Causal.Flat.minkQ v = 0) (hfix : (A₀ : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2) v = v) :
    ∀ B ∈ G, (B : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2) v = v := by
  obtain ⟨uf, huf0, hufF, hufq, hrep⟩ := exists_future_null_rep hv0 hq
  have hA₀1' : (A₀ : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2) ≠ 1 := fun h =>
    hA₀1 (Subtype.ext h)
  have hfixf : (A₀ : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2) uf = uf := by
    rcases hrep with rfl | rfl
    · exact hfix
    · rw [map_neg, hfix]
  intro B hB
  suffices hBf : (B : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2) uf = uf by
    rcases hrep with rfl | rfl
    · exact hBf
    · rw [map_neg, neg_inj] at hBf; exact hBf
  by_contra hBu
  rcases exists_isLoxodromic_pow_mul_of_fix_null huf0 hufF hufq A₀.2 B.2 hfixf hA₀1' hBu with
    hl | ⟨n, hl⟩
  · exact hG B hB hl
  · refine hG (A₀ ^ n * B) (G.mul_mem (G.pow_mem hA₀ n) hB) ?_
    simpa using hl

/-- **2+1, commutativity**: such a subgroup is commutative (the stabiliser of a null vector in
`SO₀(1, 2)` is the abelian group of null rotations). -/
theorem lorentz2_commute_of_noLox {G : Subgroup (lorentz 2)}
    (hG : ∀ A ∈ G, ¬IsLoxodromic (A : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2))
    {A₀ : lorentz 2} (hA₀ : A₀ ∈ G) (hA₀1 : A₀ ≠ 1) {v : Causal.Minkowski 2} (hv0 : v ≠ 0)
    (hq : Causal.Flat.minkQ v = 0) (hfix : (A₀ : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2) v = v) :
    ∀ B ∈ G, ∀ C ∈ G, B * C = C * B := by
  have h := lorentz2_fix_of_noLox hG hA₀ hA₀1 hv0 hq hfix
  intro B hB C hC
  exact Subtype.ext (lorentz2_commute_of_fix_null hv0 hq B.2 C.2 (h B hB) (h C hC))

/-- **`bprop:sanloxo` in 2+1 for a group with a parabolic element, proved** (DEC-75; Barbot's
Prop 9.1 is the external `Causal.Flat.BenoistNoLox`): no loxodromic element and a parabolic one
⇒ the whole group (finite index `1`) fixes a nonzero null vector. -/
theorem fixesTimelikeOrNull_of_noLox_of_parabolic {G : Subgroup (lorentz 2)}
    (hG : ∀ A ∈ G, ¬IsLoxodromic (A : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2))
    (hpar : ∃ A ∈ G, IsParabolic (A : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2)) :
    FixesTimelikeOrNull G := by
  obtain ⟨A₀, hA₀, hP⟩ := hpar
  obtain ⟨hA1, v, hv0, hq, hfix⟩ := exists_fixed_null_of_isParabolic A₀.2 hP
  exact Or.inr ⟨v, hv0, hq, lorentz2_fix_of_noLox hG hA₀ (fun h => hA1 (by rw [h]; rfl)) hv0 hq hfix⟩

/-! ### Orthonormal frames and the stabiliser of a timelike vector -/

/-- An orthonormal frame of `𝐌³`: `a` unit timelike, `e₁`, `e₂` unit spacelike, pairwise
orthogonal. -/
structure IsOrthoFrame2 (a e₁ e₂ : Causal.Minkowski 2) : Prop where
  aa : minkB a a = -1
  e₁e₁ : minkB e₁ e₁ = 1
  e₂e₂ : minkB e₂ e₂ = 1
  ae₁ : minkB a e₁ = 0
  ae₂ : minkB a e₂ = 0
  e₁e₂ : minkB e₁ e₂ = 0

variable {a e₁ e₂ : Causal.Minkowski 2}

theorem IsOrthoFrame2.e₁a (F : IsOrthoFrame2 a e₁ e₂) : minkB e₁ a = 0 := by rw [minkB_comm]; exact F.ae₁
theorem IsOrthoFrame2.e₂a (F : IsOrthoFrame2 a e₁ e₂) : minkB e₂ a = 0 := by rw [minkB_comm]; exact F.ae₂
theorem IsOrthoFrame2.e₂e₁ (F : IsOrthoFrame2 a e₁ e₂) : minkB e₂ e₁ = 0 := by rw [minkB_comm]; exact F.e₁e₂

theorem IsOrthoFrame2.linearIndependent (F : IsOrthoFrame2 a e₁ e₂) :
    LinearIndependent ℝ ![a, e₁, e₂] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h0 := congrArg (fun z => minkB z a) hg
  have h1 := congrArg (fun z => minkB z e₁) hg
  have h2 := congrArg (fun z => minkB z e₂) hg
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, minkB_add_left, minkB_smul_left,
    minkB_zero_left, F.aa, F.e₁e₁, F.e₂e₂, F.ae₁, F.ae₂, F.e₁e₂, F.e₁a, F.e₂a, F.e₂e₁] at h0 h1 h2
  intro i
  fin_cases i <;> simp <;> linarith

/-- The basis of an orthonormal frame. -/
noncomputable def IsOrthoFrame2.basis (F : IsOrthoFrame2 a e₁ e₂) :
    Module.Basis (Fin 3) ℝ (Causal.Minkowski 2) :=
  basisOfLinearIndependentOfCardEqFinrank F.linearIndependent (by simp)

theorem IsOrthoFrame2.basis_apply (F : IsOrthoFrame2 a e₁ e₂) (i : Fin 3) :
    F.basis i = ![a, e₁, e₂] i := by
  simp [IsOrthoFrame2.basis, coe_basisOfLinearIndependentOfCardEqFinrank]

/-- The coordinates in an orthonormal frame. -/
noncomputable def orthoCoord (a e₁ e₂ x : Causal.Minkowski 2) : Fin 3 → ℝ :=
  ![-minkB x a, minkB x e₁, minkB x e₂]

theorem IsOrthoFrame2.expand (F : IsOrthoFrame2 a e₁ e₂) (x : Causal.Minkowski 2) :
    x = (-minkB x a) • a + minkB x e₁ • e₁ + minkB x e₂ • e₂ := by
  set y := x - ((-minkB x a) • a + minkB x e₁ • e₁ + minkB x e₂ • e₂) with hy
  suffices hy0 : y = 0 by rw [hy, sub_eq_zero] at hy0; exact hy0
  have hya : minkB a y = 0 := by
    simp only [hy, minkB_sub_right, minkB_add_right, minkB_smul_right, F.aa, F.ae₁, F.ae₂]
    rw [minkB_comm]; ring
  have hy1 : minkB e₁ y = 0 := by
    simp only [hy, minkB_sub_right, minkB_add_right, minkB_smul_right, F.e₁a, F.e₁e₁, F.e₁e₂]
    rw [minkB_comm]; ring
  have hy2 : minkB e₂ y = 0 := by
    simp only [hy, minkB_sub_right, minkB_add_right, minkB_smul_right, F.e₂a, F.e₂e₁, F.e₂e₂]
    rw [minkB_comm]; ring
  apply eq_zero_of_forall_minkB
  intro z
  have hz := F.basis.sum_repr z
  rw [← hz]
  simp only [Fin.sum_univ_three, F.basis_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, minkB_add_left, minkB_smul_left,
    hya, hy1, hy2]
  ring

theorem IsOrthoFrame2.minkB_eq (F : IsOrthoFrame2 a e₁ e₂) (x y : Causal.Minkowski 2) :
    minkB x y = -(minkB x a * minkB y a) + minkB x e₁ * minkB y e₁ + minkB x e₂ * minkB y e₂ := by
  conv_lhs => rw [F.expand x, F.expand y]
  simp only [minkB_add_left, minkB_add_right, minkB_smul_left, minkB_smul_right, F.aa, F.ae₁,
    F.ae₂, F.e₁a, F.e₁e₁, F.e₁e₂, F.e₂a, F.e₂e₁, F.e₂e₂]
  ring

theorem IsOrthoFrame2.repr_apply (F : IsOrthoFrame2 a e₁ e₂) (x : Causal.Minkowski 2) (i : Fin 3) :
    F.basis.repr x i = orthoCoord a e₁ e₂ x i := by
  have hx : x = ∑ j, orthoCoord a e₁ e₂ x j • F.basis j := by
    simp only [Fin.sum_univ_three, F.basis_apply, orthoCoord, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    exact F.expand x
  conv_lhs => rw [hx]
  rw [F.basis.repr_sum_self]

theorem IsOrthoFrame2.toMatrix_apply (F : IsOrthoFrame2 a e₁ e₂)
    (f : Causal.Minkowski 2 →ₗ[ℝ] Causal.Minkowski 2) (i j : Fin 3) :
    LinearMap.toMatrix F.basis F.basis f i j = orthoCoord a e₁ e₂ (f (![a, e₁, e₂] j)) i := by
  rw [LinearMap.toMatrix_apply, F.repr_apply, F.basis_apply]

theorem IsOrthoFrame2.ext (F : IsOrthoFrame2 a e₁ e₂) {X Y : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2}
    (ha : X a = Y a) (h1 : X e₁ = Y e₁) (h2 : X e₂ = Y e₂) : X = Y := by
  have : (X : Causal.Minkowski 2 →ₗ[ℝ] Causal.Minkowski 2) = Y := by
    refine F.basis.ext fun i => ?_
    fin_cases i <;> simp [F.basis_apply, ha, h1, h2]
  exact LinearEquiv.toLinearMap_injective this

/-- A unit vector of the plane in the direction of `x`. -/
theorem exists_unit_dir (x : EuclideanSpace ℝ (Fin 2)) :
    ∃ ξ : EuclideanSpace ℝ (Fin 2), ξ 0 ^ 2 + ξ 1 ^ 2 = 1 ∧ ∀ i, x i = ‖x‖ * ξ i := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact ⟨EuclideanSpace.single 0 1, by simp, fun i => by simp⟩
  · refine ⟨‖x‖⁻¹ • x, ?_, fun i => ?_⟩
    · have hn : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
      have hn0 : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
      simp only [PiLp.smul_apply, smul_eq_mul]
      field_simp
      linarith
    · simp only [PiLp.smul_apply, smul_eq_mul]
      field_simp [norm_ne_zero_iff.2 hx]

/-- **Every unit future timelike vector of `𝐌³` is the first vector of an orthonormal frame.** -/
theorem exists_isOrthoFrame2 {a : Causal.Minkowski 2} (hq : Causal.Flat.minkQ a = -1) :
    ∃ e₁ e₂, IsOrthoFrame2 a e₁ e₂ := by
  obtain ⟨t, x⟩ := a
  obtain ⟨ξ, hξ, hx⟩ := exists_unit_dir x
  set n := ‖x‖
  have htn : t ^ 2 - n ^ 2 = 1 := by
    have := hq
    simp only [Causal.Flat.minkQ] at this
    linarith
  have hx0 := hx 0
  have hx1 := hx 1
  refine ⟨(n, t • ξ), ((0 : ℝ), (WithLp.toLp 2 ![-(ξ 1), ξ 0] : EuclideanSpace ℝ (Fin 2))),
    ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [minkB, inner_smul_left, inner_smul_right, PiLp.inner_apply, Fin.sum_univ_two,
      RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    (try simp only [hx0, hx1]) <;>
    first | linear_combination (t * n) * hξ | nlinarith [hξ, htn]

/-- `A` is the **rotation `(c, s)` about `a`** in the frame `(a, e₁, e₂)`. -/
structure IsRot2 (a e₁ e₂ : Causal.Minkowski 2) (c s : ℝ)
    (A : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2) : Prop where
  ha : A a = a
  h₁ : A e₁ = c • e₁ + s • e₂
  h₂ : A e₂ = (-s) • e₁ + c • e₂
  hcs : c ^ 2 + s ^ 2 = 1

/-- **The stabiliser of a unit timelike vector in `SO₀(1, 2)` is the rotation group** (the
determinant excludes the reflections). -/
theorem IsOrthoFrame2.isRot2_of_fix (F : IsOrthoFrame2 a e₁ e₂) (hA : A ∈ lorentz 2)
    (hAa : A a = a) : IsRot2 a e₁ e₂ (minkB (A e₁) e₁) (minkB (A e₁) e₂) A := by
  have hQ := hA.1
  have h1 : minkB (A e₁) a = 0 := by rw [← hAa, minkB_map hQ]; exact F.e₁a
  have h2 : minkB (A e₂) a = 0 := by rw [← hAa, minkB_map hQ]; exact F.e₂a
  have h11 : minkB (A e₁) (A e₁) = 1 := by rw [minkB_map hQ]; exact F.e₁e₁
  have h22 : minkB (A e₂) (A e₂) = 1 := by rw [minkB_map hQ]; exact F.e₂e₂
  have h12 : minkB (A e₁) (A e₂) = 0 := by rw [minkB_map hQ]; exact F.e₁e₂
  rw [F.minkB_eq, h1] at h11
  rw [F.minkB_eq, h2] at h22
  rw [F.minkB_eq, h1, h2] at h12
  have hdet : minkB (A e₁) e₁ * minkB (A e₂) e₂ - minkB (A e₂) e₁ * minkB (A e₁) e₂ = 1 := by
    have h := hA.2.2
    rw [← LinearMap.det_toMatrix F.basis, Matrix.det_fin_three] at h
    simp only [F.toMatrix_apply, orthoCoord, LinearEquiv.coe_coe, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, hAa, F.aa,
      F.ae₁, F.ae₂, h1, h2] at h
    linarith
  set c := minkB (A e₁) e₁
  set s := minkB (A e₁) e₂
  have hcs : c ^ 2 + s ^ 2 = 1 := by linarith
  have hc' : minkB (A e₂) e₁ = -s := by
    linear_combination c * h12 - s * hdet - minkB (A e₂) e₁ * hcs
  have hs' : minkB (A e₂) e₂ = c := by
    linear_combination s * h12 + c * hdet - minkB (A e₂) e₂ * hcs
  refine ⟨hAa, ?_, ?_, hcs⟩
  · conv_lhs => rw [F.expand (A e₁)]
    rw [h1, neg_zero, zero_smul, zero_add]
  · conv_lhs => rw [F.expand (A e₂)]
    rw [h2, neg_zero, zero_smul, zero_add, hc', hs']

theorem IsRot2.symm_apply {c s : ℝ} (hR : IsRot2 a e₁ e₂ c s A) :
    A.symm a = a ∧ A.symm e₁ = c • e₁ + (-s) • e₂ ∧ A.symm e₂ = s • e₁ + c • e₂ := by
  refine ⟨?_, ?_, ?_⟩
  · conv_lhs => rw [← hR.ha]
    exact A.symm_apply_apply a
  · apply A.injective
    rw [A.apply_symm_apply, map_add, map_smul, map_smul, hR.h₁, hR.h₂]
    linear_combination (norm := module) (-hR.hcs) • e₁
  · apply A.injective
    rw [A.apply_symm_apply, map_add, map_smul, map_smul, hR.h₁, hR.h₂]
    linear_combination (norm := module) (-hR.hcs) • e₂

/-- **Two elements of `SO₀(1, 2)` fixing the same unit timelike vector commute.** -/
theorem lorentz2_commute_of_fix_timelike {a : Causal.Minkowski 2} (hq : Causal.Flat.minkQ a = -1)
    {X Y : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2} (hX : X ∈ lorentz 2) (hY : Y ∈ lorentz 2)
    (hXa : X a = a) (hYa : Y a = a) : X * Y = Y * X := by
  obtain ⟨e₁, e₂, F⟩ := exists_isOrthoFrame2 hq
  have rX := F.isRot2_of_fix hX hXa
  have rY := F.isRot2_of_fix hY hYa
  have k : ∀ {cX sX cY sY : ℝ} {X Y : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2},
      IsRot2 a e₁ e₂ cX sX X → IsRot2 a e₁ e₂ cY sY Y →
      (X * Y) e₁ = (cX * cY - sX * sY) • e₁ + (sX * cY + cX * sY) • e₂ ∧
      (X * Y) e₂ = (-(sX * cY + cX * sY)) • e₁ + (cX * cY - sX * sY) • e₂ := by
    intro cX sX cY sY X Y rX rY
    constructor
    · rw [LinearEquiv.mul_apply, rY.h₁, map_add, map_smul, map_smul, rX.h₁, rX.h₂]; module
    · rw [LinearEquiv.mul_apply, rY.h₂, map_add, map_smul, map_smul, rX.h₁, rX.h₂]; module
  obtain ⟨k1, k2⟩ := k rX rY
  obtain ⟨k1', k2'⟩ := k rY rX
  refine F.ext ?_ ?_ ?_
  · simp only [LinearEquiv.mul_apply, rX.ha, rY.ha]
  · rw [k1, k1']; congr 2 <;> ring
  · rw [k2, k2']; congr 2 <;> ring

/-- The trace identity behind the elliptic ping-pong (pure algebra on `3 × 3` matrices). -/
theorem trace_rot_commutator_formula (c s : ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ)
    (hR1 : c ^ 2 + s ^ 2 - 1 = 0) (hRp : -M 0 0 ^ 2 + M 0 1 ^ 2 + M 0 2 ^ 2 + 1 = 0)
    (hRq : -M 0 0 ^ 2 + M 1 0 ^ 2 + M 2 0 ^ 2 + 1 = 0)
    (hRK1 : -M 0 1 ^ 2 + M 1 1 ^ 2 + M 2 1 ^ 2 - 1 = 0)
    (hRK2 : -M 0 2 ^ 2 + M 1 2 ^ 2 + M 2 2 ^ 2 - 1 = 0)
    (hRdet : M 1 1 * M 2 2 - M 1 2 * M 2 1 - M 0 0 = 0) :
    Matrix.trace (!![1, 0, 0; 0, c, -s; 0, s, c] * M * !![1, 0, 0; 0, c, s; 0, -s, c] *
      !![M 0 0, -M 1 0, -M 2 0; -M 0 1, M 1 1, M 2 1; -M 0 2, M 1 2, M 2 2]) =
      3 + (1 - c) * (M 0 0 - 1) * (2 * (M 0 0 + 1) - (1 + c) * (M 0 0 - 1)) := by
  simp only [Matrix.trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.vecHead, Matrix.vecTail,
    Function.comp_apply, Fin.succ_zero_eq_one]
  linear_combination 2 * (M 1 1 * M 2 2 - M 1 2 * M 2 1) * hR1 + c * (c - 1) * hRp + (-c) * hRq +
    c ^ 2 * hRK1 + c ^ 2 * hRK2 + (-2 * (c - 1) * (c + 1)) * hRdet

/-- **The elliptic ping-pong of `SO₀(1, 2)`**: if `A ≠ 1` fixes the unit future timelike `a` and
`X` moves `a`, the commutator `A X A⁻¹ X⁻¹` is loxodromic. In an orthonormal frame at `a`,
`tr [A, X] − 3 = (1 − c)(β − 1)(2(β + 1) − (1 + c)(β − 1)) > 0`, `c = cos θ`, `β = −⟨X a | a⟩`. -/
theorem isLoxodromic_commutator_of_fix_timelike {a : Causal.Minkowski 2}
    (hq : Causal.Flat.minkQ a = -1) (haF : 0 < a.1)
    {A X : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2} (hA : A ∈ lorentz 2) (hX : X ∈ lorentz 2)
    (hAa : A a = a) (hA1 : A ≠ 1) (hXa : X a ≠ a) :
    IsLoxodromic (A * X * A.symm * X.symm) := by
  obtain ⟨e₁, e₂, F⟩ := exists_isOrthoFrame2 hq
  have rA := F.isRot2_of_fix hA hAa
  set c := minkB (A e₁) e₁
  set s := minkB (A e₁) e₂
  obtain ⟨hs1, hs2, hs3⟩ := rA.symm_apply
  set b := F.basis
  set M := LinearMap.toMatrix b b (X : Causal.Minkowski 2 →ₗ[ℝ] Causal.Minkowski 2) with hM
  have hMe : ∀ i j, M i j = orthoCoord a e₁ e₂ (X (![a, e₁, e₂] j)) i := fun i j =>
    F.toMatrix_apply _ i j
  have hP : LinearMap.toMatrix b b (A : Causal.Minkowski 2 →ₗ[ℝ] Causal.Minkowski 2) =
      !![1, 0, 0; 0, c, -s; 0, s, c] := by
    ext i j
    rw [F.toMatrix_apply]
    fin_cases i <;> fin_cases j <;>
      simp [orthoCoord, rA.ha, rA.h₁, rA.h₂, minkB_add_left, minkB_smul_left, F.aa, F.ae₁,
        F.ae₂, F.e₁a, F.e₁e₁, F.e₁e₂, F.e₂a, F.e₂e₁, F.e₂e₂]
  have hP' : LinearMap.toMatrix b b (A.symm : Causal.Minkowski 2 →ₗ[ℝ] Causal.Minkowski 2) =
      !![1, 0, 0; 0, c, s; 0, -s, c] := by
    ext i j
    rw [F.toMatrix_apply]
    fin_cases i <;> fin_cases j <;>
      simp [orthoCoord, hs1, hs2, hs3, minkB_add_left, minkB_smul_left, F.aa, F.ae₁,
        F.ae₂, F.e₁a, F.e₁e₁, F.e₁e₂, F.e₂a, F.e₂e₁, F.e₂e₂]
  have hN : LinearMap.toMatrix b b (X.symm : Causal.Minkowski 2 →ₗ[ℝ] Causal.Minkowski 2) =
      !![M 0 0, -M 1 0, -M 2 0; -M 0 1, M 1 1, M 2 1; -M 0 2, M 1 2, M 2 2] := by
    ext i j
    rw [F.toMatrix_apply]
    fin_cases i <;> fin_cases j <;>
      simp [orthoCoord, hMe, minkB_symm_apply hX, minkB_comm a, minkB_comm e₁, minkB_comm e₂]
  -- the relations
  have hRq : -M 0 0 ^ 2 + M 1 0 ^ 2 + M 2 0 ^ 2 + 1 = 0 := by
    have h := minkB_map hX.1 a a
    rw [F.aa, F.minkB_eq] at h
    simp only [hMe, orthoCoord, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons]
    linarith
  have hRK1 : -M 0 1 ^ 2 + M 1 1 ^ 2 + M 2 1 ^ 2 - 1 = 0 := by
    have h := minkB_map hX.1 e₁ e₁
    rw [F.e₁e₁, F.minkB_eq] at h
    simp only [hMe, orthoCoord, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons]
    linarith
  have hRK2 : -M 0 2 ^ 2 + M 1 2 ^ 2 + M 2 2 ^ 2 - 1 = 0 := by
    have h := minkB_map hX.1 e₂ e₂
    rw [F.e₂e₂, F.minkB_eq] at h
    simp only [hMe, orthoCoord, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons]
    linarith
  have hRp : -M 0 0 ^ 2 + M 0 1 ^ 2 + M 0 2 ^ 2 + 1 = 0 := by
    have hXs : X.symm ∈ lorentz 2 := (lorentz 2).inv_mem hX
    have h := minkB_map hXs.1 a a
    rw [F.aa, F.minkB_eq] at h
    simp only [minkB_symm_apply hX] at h
    simp only [hMe, orthoCoord, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons]
    rw [minkB_comm a (X a), minkB_comm a (X e₁), minkB_comm a (X e₂)] at h
    linear_combination h
  have hMN : M * LinearMap.toMatrix b b (X.symm : Causal.Minkowski 2 →ₗ[ℝ] Causal.Minkowski 2) = 1 := by
    rw [hM, ← LinearMap.toMatrix_mul]
    have : (X : Causal.Minkowski 2 →ₗ[ℝ] Causal.Minkowski 2) * (X.symm : Causal.Minkowski 2 →ₗ[ℝ] _) =
        LinearMap.id := LinearMap.ext fun x => X.apply_symm_apply x
    rw [this, LinearMap.toMatrix_id]
  have hdet : M.det = 1 := by rw [hM, LinearMap.det_toMatrix]; exact hX.2.2
  have hadj : M.adjugate = LinearMap.toMatrix b b (X.symm : Causal.Minkowski 2 →ₗ[ℝ] Causal.Minkowski 2) := by
    calc M.adjugate = M.adjugate * (M * LinearMap.toMatrix b b (X.symm : _ →ₗ[ℝ] _)) := by
          rw [hMN, Matrix.mul_one]
      _ = (M.adjugate * M) * LinearMap.toMatrix b b (X.symm : _ →ₗ[ℝ] _) := by rw [Matrix.mul_assoc]
      _ = _ := by rw [Matrix.adjugate_mul, hdet, one_smul, Matrix.one_mul]
  have hRdet : M 1 1 * M 2 2 - M 1 2 * M 2 1 - M 0 0 = 0 := by
    have h := congrFun (congrFun hadj 0) 0
    rw [hN, Matrix.adjugate_fin_three] at h
    simp at h
    linarith
  have hR1 : c ^ 2 + s ^ 2 - 1 = 0 := by linarith [rA.hcs]
  -- the trace of the commutator
  have hcoe : ((A * X * A.symm * X.symm : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2) :
      Causal.Minkowski 2 →ₗ[ℝ] Causal.Minkowski 2) = (A : _ →ₗ[ℝ] _) * (X : _ →ₗ[ℝ] _) *
        (A.symm : _ →ₗ[ℝ] _) * (X.symm : _ →ₗ[ℝ] _) := LinearMap.ext fun x => rfl
  set β := M 0 0
  have hT : LinearMap.trace ℝ _ ((A * X * A.symm * X.symm : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2) :
      Causal.Minkowski 2 →ₗ[ℝ] Causal.Minkowski 2) =
      3 + (1 - c) * (β - 1) * (2 * (β + 1) - (1 + c) * (β - 1)) := by
    rw [hcoe, LinearMap.trace_eq_matrix_trace ℝ b, LinearMap.toMatrix_mul, LinearMap.toMatrix_mul,
      LinearMap.toMatrix_mul, hP, hP', hN, ← hM]
    exact trace_rot_commutator_formula c s M hR1 hRp hRq hRK1 hRK2 hRdet
  -- positivity
  have haT : IsFutureTimelike a := ⟨haF, by rw [hq]; norm_num⟩
  have hXaT : IsFutureTimelike (X a) := lorentz.isFutureTimelike_apply hX haT
  have hβpos : 0 < β := by
    have h := minkB_neg_of_future ⟨hXaT.1.le, hXaT.2.le⟩
      (fun h0 => by rw [h0] at hXaT; exact lt_irrefl _ hXaT.1) haT
    simp only [β, hMe, orthoCoord, Matrix.cons_val_zero]
    linarith
  have hβ1 : 1 < β := by
    have hsq : 1 ≤ β ^ 2 := by linarith [sq_nonneg (M 1 0), sq_nonneg (M 2 0)]
    have hge : 1 ≤ β := by
      by_contra h; push Not at h; nlinarith only [hsq, hβpos, h]
    refine lt_of_le_of_ne hge fun h1 => hXa ?_
    rw [← h1] at hRq
    have h10 : M 1 0 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1
      (by linarith [sq_nonneg (M 1 0), sq_nonneg (M 2 0)])
    have h20 : M 2 0 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1
      (by linarith [sq_nonneg (M 1 0), sq_nonneg (M 2 0)])
    simp only [β, hMe, orthoCoord, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h1 h10 h20
    rw [F.expand (X a), ← h1, h10, h20]; simp
  have hcs := rA.hcs
  have hc1 : c < 1 := by
    have hle : c ≤ 1 := by
      by_contra h; push Not at h; nlinarith only [hcs, sq_nonneg s, h]
    refine lt_of_le_of_ne hle fun h1 => hA1 ?_
    have hs0 : s = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (by rw [h1] at hcs; linarith)
    refine F.ext ?_ ?_ ?_
    · rw [rA.ha]; rfl
    · rw [rA.h₁, h1, hs0]; simp
    · rw [rA.h₂, h1, hs0]; simp
  have hcm : -1 ≤ c := by
    by_contra h; push Not at h; nlinarith only [hcs, sq_nonneg s, h]
  refine isLoxodromic_of_three_lt_trace ?_ ?_
  · exact (lorentz 2).mul_mem ((lorentz 2).mul_mem ((lorentz 2).mul_mem hA hX)
      ((lorentz 2).inv_mem hA)) ((lorentz 2).inv_mem hX)
  · rw [hT]
    have h4 : 0 < 2 * (β + 1) - (1 + c) * (β - 1) := by
      nlinarith only [hc1, hcm, hβ1]
    have := mul_pos (mul_pos (sub_pos.2 hc1) (sub_pos.2 hβ1)) h4
    linarith

/-- A future timelike vector fixed by `A` gives a fixed unit future timelike vector. -/
theorem exists_unit_fixed_of_fixed_timelike {A : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2}
    {v : Causal.Minkowski 2} (hv : IsFutureTimelike v) (hAv : A v = v) :
    ∃ a : Causal.Minkowski 2, Causal.Flat.minkQ a = -1 ∧ 0 < a.1 ∧ A a = a := by
  set k := Real.sqrt (-Causal.Flat.minkQ v)
  have hk0 : 0 < -Causal.Flat.minkQ v := by linarith [hv.2]
  have hk : 0 < k := Real.sqrt_pos.2 hk0
  have hk2 : k ^ 2 = -Causal.Flat.minkQ v := Real.sq_sqrt hk0.le
  refine ⟨k⁻¹ • v, ?_, ?_, by rw [map_smul, hAv]⟩
  · rw [Causal.Flat.minkQ_smul, inv_pow, hk2, inv_neg, neg_mul, inv_mul_cancel₀ (by linarith : Causal.Flat.minkQ v ≠ 0)]
  · simp only [Prod.smul_fst, smul_eq_mul]; exact mul_pos (inv_pos.2 hk) hv.1

/-- **2+1, the classification (DEC-75), proved**: a subgroup of `SO₀(1, 2)` with no loxodromic
element fixes a timelike or a nonzero null vector, and is commutative. This is Barbot's
`bprop:sanloxo` (Prop 9.1, an external there through Benoist) in dimension 2+1, with finite
index `1`: by the parabolic ping-pong (some `Aⁿ B` has trace `> 3`) and the elliptic ping-pong
(`[A, B]` has trace `> 3`). -/
theorem lorentz2_noLox_classification {G : Subgroup (lorentz 2)}
    (hG : ∀ A ∈ G, ¬IsLoxodromic (A : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2)) :
    FixesTimelikeOrNull G ∧ ∀ B ∈ G, ∀ C ∈ G, B * C = C * B := by
  by_cases htriv : ∀ A ∈ G, A = 1
  · refine ⟨Or.inl ⟨timeUnit 2, by simp, fun A hA => by rw [htriv A hA]; rfl⟩, ?_⟩
    intro B hB C hC; rw [htriv B hB, htriv C hC]
  push Not at htriv
  obtain ⟨A₀, hA₀, hA₀1⟩ := htriv
  have hA₀1' : (A₀ : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2) ≠ 1 := fun h =>
    hA₀1 (Subtype.ext h)
  rcases lorentz_trichotomy A₀.2 with hE | hL | hP
  · obtain ⟨v, hv, hAv⟩ := hE.exists_fixed_timelike A₀.2
    obtain ⟨a, hq, haF, hAa⟩ := exists_unit_fixed_of_fixed_timelike hv hAv
    have hfix : ∀ B ∈ G, (B : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2) a = a := by
      intro B hB
      by_contra hBa
      have hl := isLoxodromic_commutator_of_fix_timelike hq haF A₀.2 B.2 hAa hA₀1' hBa
      exact hG (A₀ * B * A₀⁻¹ * B⁻¹)
        (G.mul_mem (G.mul_mem (G.mul_mem hA₀ hB) (G.inv_mem hA₀)) (G.inv_mem hB)) hl
    refine ⟨Or.inl ⟨a, by rw [hq]; norm_num, hfix⟩, ?_⟩
    intro B hB C hC
    exact Subtype.ext (lorentz2_commute_of_fix_timelike hq B.2 C.2 (hfix B hB) (hfix C hC))
  · exact absurd hL (hG A₀ hA₀)
  · obtain ⟨-, v, hv0, hq, hfix⟩ := exists_fixed_null_of_isParabolic A₀.2 hP
    exact ⟨fixesTimelikeOrNull_of_noLox_of_parabolic hG ⟨A₀, hA₀, hP⟩,
      lorentz2_commute_of_noLox hG hA₀ hA₀1 hv0 hq hfix⟩

/-- **`Causal.Flat.BenoistNoLox 2`, proved** (DEC-75): Barbot's external Prop 9.1 holds in
2+1 with no external input, the finite-index subgroup being the whole group. -/
theorem benoistNoLox_two : BenoistNoLox 2 := fun G hG =>
  ⟨G, le_rfl, by rw [Subgroup.relIndex_self]; exact one_ne_zero,
    (lorentz2_noLox_classification hG).1⟩

end TwoOneFrame


/-! ## The isometry groups of `𝐌³` without loxodromic elements -/

section IsomTwoOne

open Causal.Flat
open scoped commutatorElement

/-- **Isometries with trivial linear part (translations) commute.** -/
theorem isom_commute_of_linOf_eq_one {g h : isom 2} (hg : linOf g = 1) (hh : linOf h = 1) :
    g * h = h * g := by
  have key : ∀ k : isom 2, linOf k = 1 → ∀ x,
      (k : Causal.Minkowski 2 ≃ᵃ[ℝ] Causal.Minkowski 2) x = x + trOf k := by
    intro k hk x
    rw [apply_eq_linear_add_transPart]
    show linOf k x + _ = _
    rw [hk]; rfl
  refine Subtype.ext (AffineEquiv.ext fun x => ?_)
  simp only [Subgroup.coe_mul, AffineEquiv.coe_mul, Function.comp_apply, key g hg, key h hh]
  abel

/-- The linear part of a commutator of isometries with commuting linear parts is trivial. -/
theorem linOf_commutator_eq_one {a b : isom 2} (h : linOf a * linOf b = linOf b * linOf a) :
    linOf ⁅a, b⁆ = 1 := by
  rw [commutatorElement_def, linOf_mul, linOf_mul, linOf_mul, linOf_inv, linOf_inv, h]
  group

/-- **Metabelian**: every two commutators commute (`⁅⁅a, b⁆, ⁅c, e⁆⁆ = 1`). -/
def IsMetabelianOn (Γ : Subgroup (isom 2)) : Prop :=
  ∀ a ∈ Γ, ∀ b ∈ Γ, ∀ c ∈ Γ, ∀ e ∈ Γ, ⁅⁅a, b⁆, ⁅c, e⁆⁆ = 1

/-- **The linear parts of `Γ ≤ Isom(𝐌³)` commute** when `Γ` has no loxodromic linear part and
some linear part is parabolic (DEC-75, 2+1). -/
theorem linOf_commute_of_noLox_of_parabolic {Γ : Subgroup (isom 2)}
    (hnl : ∀ γ ∈ Γ, ¬IsLoxodromic (linOf γ)) (hpar : ∃ γ ∈ Γ, IsParabolic (linOf γ)) :
    ∀ a ∈ Γ, ∀ b ∈ Γ, linOf a * linOf b = linOf b * linOf a := by
  set G := Γ.map linearPart
  have hG : ∀ A ∈ G, ¬IsLoxodromic (A : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2) := by
    rintro _ ⟨γ, hγ, rfl⟩
    rw [← linOf_eq_linearPart]; exact hnl γ hγ
  obtain ⟨γ₀, hγ₀, hP⟩ := hpar
  obtain ⟨hA1, v, hv0, hq, hfix⟩ := exists_fixed_null_of_isParabolic (linOf_mem γ₀) hP
  have hmem : linearPart γ₀ ∈ G := ⟨γ₀, hγ₀, rfl⟩
  have hne : linearPart γ₀ ≠ 1 := fun h => hA1 (by rw [linOf_eq_linearPart, h]; rfl)
  have hfix' : (linearPart γ₀ : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2) v = v := by
    rw [← linOf_eq_linearPart]; exact hfix
  have hc := lorentz2_commute_of_noLox hG hmem hne hv0 hq hfix'
  intro a ha b hb
  have := congrArg (fun A : lorentz 2 => (A : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2))
    (hc _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩)
  simpa [← linOf_eq_linearPart] using this

/-- **No loxodromic element and a parabolic one ⇒ metabelian** (2+1): the commutators are
translations. -/
theorem isMetabelianOn_of_noLox_of_parabolic {Γ : Subgroup (isom 2)}
    (hnl : ∀ γ ∈ Γ, ¬IsLoxodromic (linOf γ)) (hpar : ∃ γ ∈ Γ, IsParabolic (linOf γ)) :
    IsMetabelianOn Γ := by
  have hc := linOf_commute_of_noLox_of_parabolic hnl hpar
  intro a ha b hb c hc' e he
  rw [commutatorElement_eq_one_iff_mul_comm]
  exact isom_commute_of_linOf_eq_one (linOf_commutator_eq_one (hc a ha b hb))
    (linOf_commutator_eq_one (hc c hc' e he))

/-- **DEC-75, the loxodromic element (2+1)**: a subgroup of `Isom(𝐌³)` with a parabolic linear
part which is not metabelian contains an element with loxodromic linear part. -/
theorem exists_isLoxodromic_of_parabolic_of_not_metabelian {Γ : Subgroup (isom 2)}
    (hpar : ∃ γ ∈ Γ, IsParabolic (linOf γ)) (hnm : ¬IsMetabelianOn Γ) :
    ∃ γ ∈ Γ, IsLoxodromic (linOf γ) := by
  by_contra h
  push Not at h
  exact hnm (isMetabelianOn_of_noLox_of_parabolic h hpar)

/-- **The linear parts of `Γ ≤ Isom(𝐌³)` commute** when `Γ` has no loxodromic linear part
(2+1, `lorentz2_noLox_classification`). -/
theorem linOf_commute_of_noLox {Γ : Subgroup (isom 2)} (hnl : ∀ γ ∈ Γ, ¬IsLoxodromic (linOf γ)) :
    ∀ a ∈ Γ, ∀ b ∈ Γ, linOf a * linOf b = linOf b * linOf a := by
  have hG : ∀ A ∈ Γ.map linearPart,
      ¬IsLoxodromic (A : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2) := by
    rintro _ ⟨γ, hγ, rfl⟩
    rw [← linOf_eq_linearPart]; exact hnl γ hγ
  have hc := (lorentz2_noLox_classification hG).2
  intro a ha b hb
  have := congrArg (fun A : lorentz 2 => (A : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2))
    (hc _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩)
  simpa [← linOf_eq_linearPart] using this

/-- **No loxodromic element ⇒ metabelian** (2+1): the commutators are translations. -/
theorem isMetabelianOn_of_noLox {Γ : Subgroup (isom 2)} (hnl : ∀ γ ∈ Γ, ¬IsLoxodromic (linOf γ)) :
    IsMetabelianOn Γ := by
  have hc := linOf_commute_of_noLox hnl
  intro a ha b hb c hc' e he
  rw [commutatorElement_eq_one_iff_mul_comm]
  exact isom_commute_of_linOf_eq_one (linOf_commutator_eq_one (hc a ha b hb))
    (linOf_commutator_eq_one (hc c hc' e he))

/-- **DEC-75, the loxodromic element (2+1), proved**: a subgroup of `Isom(𝐌³)` which is not
metabelian contains an element with loxodromic linear part. -/
theorem exists_isLoxodromic_of_not_metabelian {Γ : Subgroup (isom 2)} (hnm : ¬IsMetabelianOn Γ) :
    ∃ γ ∈ Γ, IsLoxodromic (linOf γ) := by
  by_contra h
  push Not at h
  exact hnm (isMetabelianOn_of_noLox h)

/-- The isometries of `𝐌³` whose linear part fixes `u`. -/
noncomputable def isomFixing (u : Causal.Minkowski 2) : Subgroup (isom 2) where
  carrier := {g | linOf g u = u}
  mul_mem' {a b} ha hb := by
    show linOf (a * b) u = u
    rw [linOf_mul, LinearEquiv.mul_apply, hb, ha]
  one_mem' := rfl
  inv_mem' {a} ha := by
    show linOf a⁻¹ u = u
    rw [linOf_inv]
    conv_lhs => rw [← ha]
    exact (linOf a).symm_apply_apply u

/-- **Counterexample (finding on the dispatch's reading of DEC-76)**: "non-abelian" does not force
a loxodromic element. The isometries of `𝐌³` whose linear part fixes a null vector form a
**non-abelian** group with **no** loxodromic element (a null rotation and a translation do not
commute). So the algebraic step of DEC-75 needs more than non-abelianness — here: not metabelian
(`exists_isLoxodromic_of_not_metabelian`), which `π₁` of a punctured surface of non-abelian `π₁`
(a free group of rank `≥ 2`) satisfies. -/
theorem exists_nonabelian_subgroup_noLox :
    ∃ Γ : Subgroup (isom 2), (∃ a ∈ Γ, ∃ b ∈ Γ, a * b ≠ b * a) ∧
      ∀ γ ∈ Γ, ¬IsLoxodromic (linOf γ) := by
  have hij : (0 : Fin 2) ≠ 1 := by decide
  set L := stdNullRot hij (1 : ℝ)
  have hL := stdNullRot_mem_lorentz hij (1 : ℝ)
  obtain ⟨hL1, u, hu0, hq, hLu⟩ :=
    exists_fixed_null_of_isParabolic hL (stdNullRot_isParabolic hij one_ne_zero)
  obtain ⟨v, hv⟩ : ∃ v, L v ≠ v := by
    by_contra h; push Not at h; exact hL1 (LinearEquiv.ext h)
  set g₀ : isom 2 := ⟨L.toAffineEquiv, mem_isom_iff.2 hL⟩
  set τ : isom 2 := ⟨AffineEquiv.constVAdd ℝ (Causal.Minkowski 2) v, constVAdd_mem_isom v⟩
  refine ⟨isomFixing u, ⟨g₀, hLu, τ, rfl, fun h => hv ?_⟩, ?_⟩
  · have h0 : g₀ • (τ • (0 : Causal.Minkowski 2)) = τ • (g₀ • 0) := by
      rw [← mul_smul, ← mul_smul, h]
    rw [isom_smul_def, isom_smul_def, isom_smul_def, isom_smul_def] at h0
    change L.toAffineEquiv (AffineEquiv.constVAdd ℝ _ v 0) =
      AffineEquiv.constVAdd ℝ _ v (L.toAffineEquiv 0) at h0
    simpa using h0
  · intro γ hγ hl
    have hfix : ((linearPart γ ^ 1 : lorentz 2) : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2) u = u := by
      rw [pow_one, ← linOf_eq_linearPart]; exact hγ
    have := minkQ_pos_of_fixed_pow_loxodromic (by rw [← linOf_eq_linearPart]; exact hl)
      one_ne_zero hfix hu0
    rw [hq] at this; exact lt_irrefl 0 this

end IsomTwoOne


/-! ## Null half-spaces as chronological futures of lightlike planes -/

section NullPlanes

open Causal.Flat

variable {d : ℕ}

/-- The **lightlike plane** `Π(u, s) = {p | ⟨(1, u) | p⟩ = s}` of `w = (u, s) ∈ 𝒮 × ℝ`. -/
def nullPlane (w : PenroseSphere d × ℝ) : Set (Causal.Minkowski d) :=
  {p | minkB (nullVec w.1) p = w.2}

/-- **`P⁺(u, s) = I⁺(Π(u, s))`**: Barbot's future null half-space is the chronological future,
in `𝐌ⁿ`, of the lightlike plane bounding it. -/
theorem halfPlus_eq_Iplus_nullPlane (w : PenroseSphere d × ℝ) :
    halfPlus w.1 w.2 = (Causal.minkowski d).Iplus ⊤ (nullPlane w) := by
  ext p
  rw [mem_halfPlus, Causal.Precausality.mem_Iplus]
  constructor
  · intro hp
    set t := w.2 - minkB (nullVec w.1) p with ht
    have ht0 : 0 < t := by rw [ht]; linarith
    refine ⟨p - t • timeUnit d, ?_, ?_⟩
    · show minkB (nullVec w.1) (p - t • timeUnit d) = w.2
      rw [minkB_sub_right, minkB_smul_right]
      have : minkB (nullVec w.1) (timeUnit d) = -1 := by simp [minkB, nullVec, timeUnit]
      rw [this, ht]; ring
    · rw [lt_top_iff_minkQ, sub_sub_cancel]
      refine ⟨by simp [timeUnit, ht0], ?_⟩
      rw [minkQ_smul, minkQ_timeUnit]; nlinarith
  · rintro ⟨q, hq, hqp⟩
    rw [lt_top_iff_minkQ] at hqp
    have h := minkB_neg_of_future (isFutureCausal_nullVec w.1) (nullVec_ne_zero w.1) hqp
    rw [minkB_sub_right] at h
    have hq' : minkB (nullVec w.1) q = w.2 := hq
    linarith

/-- **`Ω⁺(Λ) = ⋂_{w ∈ Λ} I⁺(Π_w)`** (Barbot Def 4.4 read with gx's `I⁺`). -/
theorem omegaPlus_eq_iInter_Iplus (Λ : Set (PenroseSphere d × ℝ)) :
    omegaPlus Λ = ⋂ w ∈ Λ, (Causal.minkowski d).Iplus ⊤ (nullPlane w) := by
  simp only [omegaPlus, halfPlus_eq_Iplus_nullPlane]

/-- `P⁻(u, s) = I⁻(Π(u, s))`. -/
theorem halfMinus_eq_Iminus_nullPlane (w : PenroseSphere d × ℝ) :
    halfMinus w.1 w.2 = (Causal.minkowski d).Iminus ⊤ (nullPlane w) := by
  ext p
  rw [mem_halfMinus, Causal.Precausality.mem_Iminus]
  constructor
  · intro hp
    set t := minkB (nullVec w.1) p - w.2 with ht
    have ht0 : 0 < t := by rw [ht]; linarith
    refine ⟨p + t • timeUnit d, ?_, ?_⟩
    · show minkB (nullVec w.1) (p + t • timeUnit d) = w.2
      rw [minkB_add_right, minkB_smul_right]
      have : minkB (nullVec w.1) (timeUnit d) = -1 := by simp [minkB, nullVec, timeUnit]
      rw [this, ht]; ring
    · rw [lt_top_iff_minkQ, add_sub_cancel_left]
      refine ⟨by simp [timeUnit, ht0], ?_⟩
      rw [minkQ_smul, minkQ_timeUnit]; nlinarith
  · rintro ⟨q, hq, hpq⟩
    rw [lt_top_iff_minkQ] at hpq
    have h := minkB_neg_of_future (isFutureCausal_nullVec w.1) (nullVec_ne_zero w.1) hpq
    rw [minkB_sub_right] at h
    have hq' : minkB (nullVec w.1) q = w.2 := hq
    linarith

/-- `Ω⁻(Λ) = ⋂_{w ∈ Λ} I⁻(Π_w)`. -/
theorem omegaMinus_eq_iInter_Iminus (Λ : Set (PenroseSphere d × ℝ)) :
    omegaMinus Λ = ⋂ w ∈ Λ, (Causal.minkowski d).Iminus ⊤ (nullPlane w) := by
  simp only [omegaMinus, halfMinus_eq_Iminus_nullPlane]

/-- **The family of lightlike planes is `Isom`-equivariant**: `g` maps `Π_w` onto `Π_{g·w}`. -/
theorem smul_mem_nullPlane_iff (g : isom d) (w : PenroseSphere d × ℝ) (p : Causal.Minkowski d) :
    g • p ∈ nullPlane (isomPenrose g w) ↔ p ∈ nullPlane w := by
  have h := minkB_isomPenrose g w p
  have ha := (inv_pos.2 (lorentzScale_pos (linearPart g) w.1)).ne'
  simp only [nullPlane, Set.mem_setOf_eq]
  constructor
  · intro h1
    rw [h1, sub_self] at h
    have := (mul_eq_zero.1 h.symm).resolve_left ha
    linarith
  · intro h1
    rw [h1, sub_self, mul_zero, sub_eq_zero] at h
    exact h

/-- **The planes of `Λ(Γ)` form a `Γ`-invariant family** (`bprop:admlox`'s invariance). -/
theorem limitSetJ_nullPlane_invariant {Γ : Subgroup (isom d)} {γ : isom d} (hγ : γ ∈ Γ)
    {w : PenroseSphere d × ℝ} (hw : w ∈ limitSetJ Γ) :
    isomPenrose γ w ∈ limitSetJ Γ ∧ (fun p => γ • p) '' nullPlane w = nullPlane (isomPenrose γ w) := by
  refine ⟨isomPenrose_image_limitSetJ_subset hγ ⟨w, hw, rfl⟩, ?_⟩
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩; exact (smul_mem_nullPlane_iff γ w p).2 hp
  · intro hq
    refine ⟨γ⁻¹ • q, (smul_mem_nullPlane_iff γ w _).1 ?_, smul_inv_smul γ q⟩
    rw [smul_inv_smul]; exact hq

end NullPlanes

/-! ## The holonomy of a flat `(Isom 𝐌³, 𝐌³)`-spacetime (Barbot's uniformization, read in 2+1) -/

section FlatHolonomy

open Causal.Flat
open scoped commutatorElement

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace (Causal.Minkowski 2) M]
  [HasGroupoid M (Causal.gxGroupoid (isom 2) (Causal.Minkowski 2))] {x₀ : M}
  {D : Causal.UniversalCover M x₀ → Causal.Minkowski 2}
  {ρ : Causal.Deck (Causal.UniversalCover.proj M x₀) →* isom 2} {S : Set M}

/-- **`ρ` is faithful**: `𝒟` is injective (Prop 8.12) and `𝒟 ∘ γ = ρ(γ) ∘ 𝒟`. -/
theorem holonomy_injective (hpair : IsDevelopingPair x₀ D ρ)
    (hcaus : (flatCausality 2 M).IsCausal) (h : DevelopsCC x₀ D S) : Function.Injective ρ := by
  have hD := Causal.Flat.uniformization_injective hpair hcaus h
  rw [injective_iff_map_eq_one]
  intro γ hγ
  refine Subtype.ext (Homeomorph.ext fun z => hD ?_)
  rw [hpair.equiv, hγ, one_smul]; rfl

/-- **`ρ(π₁)` is discrete** (`isomTopology`; Barbot's §8 data). -/
theorem holonomy_discrete (hpair : IsDevelopingPair x₀ D ρ) (h : DevelopsCC x₀ D S) :
    DiscreteTopology ρ.range :=
  Causal.Flat.discreteTopology_of_developsCC hpair h le_rfl

/-- **Torsion-freeness from a free action on a convex invariant set**: if `Γ` acts freely on `Ω`,
`Ω` is convex and contains a `Γ`-orbit, then `Γ` is torsion-free (the barycentre of a finite
orbit is fixed). -/
theorem isTorsionFree_of_free_convex {Γ : Subgroup (isom 2)} {Ω : Set (Causal.Minkowski 2)}
    (hfree : ∀ γ ∈ Γ, γ ≠ 1 → ∀ x ∈ Ω, γ • x ≠ x) (hconv : Convex ℝ Ω)
    (horb : ∀ γ ∈ Γ, ∀ n : ℕ, ∃ x ∈ Ω, ∀ k < n, (γ ^ k) • x ∈ Ω) :
    IsTorsionFreeSubgroup Γ := by
  intro γ hγ hfin
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 hfin
  obtain ⟨x, hx, hk⟩ := horb γ hγ n
  by_contra h1
  set b : Causal.Minkowski 2 := ∑ k ∈ Finset.range n, ((n : ℝ)⁻¹) • ((γ ^ k) • x) with hb
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hbΩ : b ∈ Ω := by
    refine hconv.sum_mem (fun _ _ => inv_nonneg.2 hn'.le) ?_ fun k hk' => hk k (Finset.mem_range.1 hk')
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_inv_cancel₀ hn'.ne']
  apply hfree γ hγ h1 b hbΩ
  have hlin : ∀ y, γ • y = linOf γ y + trOf γ := smul_eq_lin_add γ
  rw [hb, hlin, map_sum]
  simp only [map_smul]
  have hsum1 : ∑ k ∈ Finset.range n, ((n : ℝ)⁻¹) • trOf γ = trOf γ := by
    rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
      mul_inv_cancel₀ hn'.ne', one_smul]
  conv_lhs => rw [← hsum1]
  rw [← Finset.sum_add_distrib]
  have hstep : ∀ k, ((n : ℝ)⁻¹) • linOf γ ((γ ^ k) • x) + ((n : ℝ)⁻¹) • trOf γ =
      ((n : ℝ)⁻¹) • ((γ ^ (k + 1)) • x) := fun k => by
    rw [← smul_add, ← hlin, pow_succ', mul_smul]
  simp only [hstep]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Finset.sum_range_succ, Finset.sum_range_succ' _ m, hpow, pow_zero, one_smul]

/-- **`ρ(π₁)` is torsion-free**, with a loxodromic element: it acts freely on the convex
`Ω^±(Λ(Γ)) ⊇ 𝒟(M̃)` (Cor 10.3), which contains every orbit `ρ(γ)ᵏ 𝒟(z) = 𝒟(γᵏ z)`. -/
theorem holonomy_torsionFree (hpair : IsDevelopingPair x₀ D ρ)
    (hcaus : (flatCausality 2 M).IsCausal) (h : DevelopsCC x₀ D S)
    (hlox : ∃ γ ∈ ρ.range, IsLoxodromic (linOf γ)) [Nonempty M] :
    IsTorsionFreeSubgroup ρ.range := by
  obtain ⟨z⟩ : Nonempty (Causal.UniversalCover M x₀) := ⟨Causal.UniversalCover.base x₀⟩
  have horb : ∀ Ω : Set (Causal.Minkowski 2), Set.range D ⊆ Ω →
      ∀ γ ∈ ρ.range, ∀ n : ℕ, ∃ x ∈ Ω, ∀ k < n, (γ ^ k) • x ∈ Ω := by
    rintro Ω hΩ _ ⟨δ, rfl⟩ n
    refine ⟨D z, hΩ ⟨z, rfl⟩, fun k _ => hΩ ⟨(δ ^ k).1 z, ?_⟩⟩
    rw [hpair.equiv, map_pow]
  rcases (Causal.Flat.uniformization hpair hcaus h hlox).2 with ⟨-, hD, hfp⟩ | ⟨-, hD, hfp⟩
  · exact isTorsionFree_of_free_convex hfp.1 (convex_omegaPlus _) (horb _ hD)
  · exact isTorsionFree_of_free_convex hfp.1 (convex_omegaMinus _) (horb _ hD)

/-- **The holonomy package** (gx §4, the input of `theo:globally_hyperbolic_cauchy_complete_cauchy_maximal`
from Barbot, in 2+1): for a Hausdorff flat `(Isom 𝐌³, 𝐌³)`-manifold, causal, with a Cauchy surface
developing as in (CC′), whose holonomy group is not metabelian: `𝒟` is injective; `ρ` is faithful,
discrete and torsion-free; `ρ(π₁)` contains a loxodromic element (proved, DEC-75); and
`𝒟(M̃) ⊆ Ω⁺(Λ) = ⋂_{w ∈ Λ} I⁺(Π_w)` with `Λ = Λ(Γ)` future regular, a `Γ`-invariant family of
lightlike planes, `Γ` acting freely and properly discontinuously on it — or the time-reversed
statement. -/
theorem holonomy_package (hpair : IsDevelopingPair x₀ D ρ)
    (hcaus : (flatCausality 2 M).IsCausal) (h : DevelopsCC x₀ D S)
    (hnm : ¬IsMetabelianOn ρ.range) [Nonempty M] :
    (∃ γ ∈ ρ.range, IsLoxodromic (linOf γ)) ∧ Function.Injective D ∧ Function.Injective ρ ∧
      DiscreteTopology ρ.range ∧ IsTorsionFreeSubgroup ρ.range ∧
      (∀ γ ∈ ρ.range, ∀ w ∈ limitSetJ ρ.range, isomPenrose γ w ∈ limitSetJ ρ.range ∧
        (fun p => γ • p) '' nullPlane w = nullPlane (isomPenrose γ w)) ∧
      ((FutureRegular (limitSetJ ρ.range) ∧ Set.range D ⊆ omegaPlus (limitSetJ ρ.range) ∧
          ActsFreelyProperlyOn ρ.range (omegaPlus (limitSetJ ρ.range)) ∧
          omegaPlus (limitSetJ ρ.range) =
            ⋂ w ∈ limitSetJ ρ.range, (Causal.minkowski 2).Iplus ⊤ (nullPlane w)) ∨
        (PastRegular (limitSetJ ρ.range) ∧ Set.range D ⊆ omegaMinus (limitSetJ ρ.range) ∧
          ActsFreelyProperlyOn ρ.range (omegaMinus (limitSetJ ρ.range)) ∧
          omegaMinus (limitSetJ ρ.range) =
            ⋂ w ∈ limitSetJ ρ.range, (Causal.minkowski 2).Iminus ⊤ (nullPlane w))) := by
  have hlox := exists_isLoxodromic_of_not_metabelian hnm
  obtain ⟨hD, hcase⟩ := Causal.Flat.uniformization hpair hcaus h hlox
  refine ⟨hlox, hD, holonomy_injective hpair hcaus h, holonomy_discrete hpair h,
    holonomy_torsionFree hpair hcaus h hlox,
    fun γ hγ w hw => limitSetJ_nullPlane_invariant hγ hw, ?_⟩
  rcases hcase with ⟨hF, hDΩ, hfp⟩ | ⟨hP, hDΩ, hfp⟩
  · exact Or.inl ⟨hF, hDΩ, hfp, omegaPlus_eq_iInter_Iplus _⟩
  · exact Or.inr ⟨hP, hDΩ, hfp, omegaMinus_eq_iInter_Iminus _⟩

end FlatHolonomy


/-! ## The holonomy of a Cauchy-complete globally hyperbolic flat spacetime, from the paper's data -/

section CauchyCompleteHolonomy

open Causal.Flat
open scoped commutatorElement

/-- A group is **metabelian** when any two commutators commute. -/
def IsMetabelianGroup (G : Type*) [Group G] : Prop :=
  ∀ a b c e : G, ⁅⁅a, b⁆, ⁅c, e⁆⁆ = 1

/-- A faithful representation transports non-metabelianity to the image. -/
theorem not_isMetabelianOn_range {G : Type*} [Group G] {ρ : G →* isom 2}
    (hρ : Function.Injective ρ) (hG : ¬IsMetabelianGroup G) : ¬IsMetabelianOn ρ.range := by
  intro h
  apply hG
  intro a b c e
  apply hρ
  rw [map_one, map_commutatorElement, map_commutatorElement, map_commutatorElement]
  exact h _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ _ ⟨c, rfl⟩ _ ⟨e, rfl⟩

/-- A metabelian group is solvable (`derivedSeries G 2 = ⊥`). -/
theorem IsMetabelianGroup.isSolvable {G : Type*} [Group G] (h : IsMetabelianGroup G) :
    IsSolvable G := by
  rw [isSolvable_def]
  refine ⟨2, ?_⟩
  have h1 : derivedSeries G 1 = commutator G := derivedSeries_one G
  have hcomm : ∀ x ∈ derivedSeries G 1, ∀ y ∈ derivedSeries G 1, x * y = y * x := by
    rw [h1, commutator_def, Subgroup.commutator_def]
    intro x hx y hy
    have hS : ∀ u ∈ {g : G | ∃ g₁ ∈ (⊤ : Subgroup G), ∃ g₂ ∈ (⊤ : Subgroup G), ⁅g₁, g₂⁆ = g},
        ∀ v ∈ {g : G | ∃ g₁ ∈ (⊤ : Subgroup G), ∃ g₂ ∈ (⊤ : Subgroup G), ⁅g₁, g₂⁆ = g},
        u * v = v * u := by
      rintro _ ⟨a, -, b, -, rfl⟩ _ ⟨c, -, e, -, rfl⟩
      exact (commutatorElement_eq_one_iff_mul_comm).1 (h a b c e)
    have hc := Subgroup.isMulCommutative_closure hS
    exact Subtype.ext_iff.1 (hc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  show ⁅derivedSeries G 1, derivedSeries G 1⁆ = ⊥
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx y hy
  exact (hcomm y hy x hx)

/-- A non-solvable group is not metabelian. -/
theorem not_isMetabelianGroup_of_not_isSolvable {G : Type*} [Group G] (h : ¬IsSolvable G) :
    ¬IsMetabelianGroup G := fun hm => h hm.isSolvable

/-- **Barbot's uniformization in 2+1, from the paper's hypotheses** (gx §4, DEC-31, DEC-75): let
`M` be a globally hyperbolic Cauchy-complete flat spacetime of dimension 2+1 whose fundamental
group (the deck group of its universal cover) is not metabelian. Then **for the given developing
pair** `(𝒟, ρ)` (any one): `𝒟` is injective, `ρ` faithful, discrete and torsion-free, `ρ(π₁)`
contains a loxodromic element, the lightlike planes `Π_w` (`w ∈ Λ = Λ(ρ(π₁))`) form a
`ρ(π₁)`-invariant family, and `𝒟(M̃) ⊆ Ω⁺(Λ) = ⋂_{w ∈ Λ} I⁺(Π_w)` (`Λ` future regular, a free
and properly discontinuous action), or the time-reversed statement. -/
theorem holonomy_package_of_isCauchyComplete (M : FlatSpacetime.{u} 2) (hGH : GH M)
    (hCC : IsCauchyComplete 2 M) (x₀ : M)
    (hnm : ¬IsMetabelianGroup (Causal.Deck (Causal.UniversalCover.proj M x₀)))
    (D : Causal.UniversalCover M x₀ → Causal.Minkowski 2)
    (ρ : Causal.Deck (Causal.UniversalCover.proj M x₀) →* isom 2)
    (hpair : IsDevelopingPair x₀ D ρ) :
      (∃ γ ∈ ρ.range, IsLoxodromic (linOf γ)) ∧ Function.Injective D ∧ Function.Injective ρ ∧
      DiscreteTopology ρ.range ∧ IsTorsionFreeSubgroup ρ.range ∧
      (∀ γ ∈ ρ.range, ∀ w ∈ limitSetJ ρ.range, isomPenrose γ w ∈ limitSetJ ρ.range ∧
        (fun p => γ • p) '' nullPlane w = nullPlane (isomPenrose γ w)) ∧
      ((FutureRegular (limitSetJ ρ.range) ∧ Set.range D ⊆ omegaPlus (limitSetJ ρ.range) ∧
          ActsFreelyProperlyOn ρ.range (omegaPlus (limitSetJ ρ.range)) ∧
          omegaPlus (limitSetJ ρ.range) =
            ⋂ w ∈ limitSetJ ρ.range, (Causal.minkowski 2).Iplus ⊤ (nullPlane w)) ∨
        (PastRegular (limitSetJ ρ.range) ∧ Set.range D ⊆ omegaMinus (limitSetJ ρ.range) ∧
          ActsFreelyProperlyOn ρ.range (omegaMinus (limitSetJ ρ.range)) ∧
          omegaMinus (limitSetJ ρ.range) =
            ⋂ w ∈ limitSetJ ρ.range, (Causal.minkowski 2).Iminus ⊤ (nullPlane w))) := by
  obtain ⟨S, hS⟩ := exists_developsCC_of_isCauchyComplete M hGH hCC x₀
  obtain ⟨h1, h2, h3, h4⟩ := hS D hpair.gx
  have h : DevelopsCC x₀ D S := ⟨h1, h2, ⟨h3, h4⟩⟩
  have hcaus : (flatCausality 2 M).IsCausal := hGH.1
  have hnm' := not_isMetabelianOn_range (holonomy_injective hpair hcaus h) hnm
  exact holonomy_package hpair hcaus h hnm'

/-- The existential corollary of `holonomy_package_of_isCauchyComplete`: a developing pair exists
(`Causal.Flat.exists_isDevelopingPair`), and it has the package's properties. -/
theorem exists_holonomy_package_of_isCauchyComplete (M : FlatSpacetime.{u} 2) (hGH : GH M)
    (hCC : IsCauchyComplete 2 M) (x₀ : M)
    (hnm : ¬IsMetabelianGroup (Causal.Deck (Causal.UniversalCover.proj M x₀))) :
    ∃ (D : Causal.UniversalCover M x₀ → Causal.Minkowski 2)
      (ρ : Causal.Deck (Causal.UniversalCover.proj M x₀) →* isom 2), IsDevelopingPair x₀ D ρ ∧
      (∃ γ ∈ ρ.range, IsLoxodromic (linOf γ)) ∧ Function.Injective D ∧ Function.Injective ρ ∧
      DiscreteTopology ρ.range ∧ IsTorsionFreeSubgroup ρ.range ∧
      (∀ γ ∈ ρ.range, ∀ w ∈ limitSetJ ρ.range, isomPenrose γ w ∈ limitSetJ ρ.range ∧
        (fun p => γ • p) '' nullPlane w = nullPlane (isomPenrose γ w)) ∧
      ((FutureRegular (limitSetJ ρ.range) ∧ Set.range D ⊆ omegaPlus (limitSetJ ρ.range) ∧
          ActsFreelyProperlyOn ρ.range (omegaPlus (limitSetJ ρ.range)) ∧
          omegaPlus (limitSetJ ρ.range) =
            ⋂ w ∈ limitSetJ ρ.range, (Causal.minkowski 2).Iplus ⊤ (nullPlane w)) ∨
        (PastRegular (limitSetJ ρ.range) ∧ Set.range D ⊆ omegaMinus (limitSetJ ρ.range) ∧
          ActsFreelyProperlyOn ρ.range (omegaMinus (limitSetJ ρ.range)) ∧
          omegaMinus (limitSetJ ρ.range) =
            ⋂ w ∈ limitSetJ ρ.range, (Causal.minkowski 2).Iminus ⊤ (nullPlane w))) := by
  obtain ⟨D, ρ, hpair⟩ := exists_isDevelopingPair (d := 2) (M := M) x₀
  exact ⟨D, ρ, hpair, holonomy_package_of_isCauchyComplete M hGH hCC x₀ hnm D ρ hpair⟩

end CauchyCompleteHolonomy

/-! ## `Reg M` of an `𝔼₀`-manifold as a flat spacetime -/

section RegM

open scoped Causal.Flat

variable (M : Type) [TopologicalSpace M] [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]

/-- `Reg M` of a Hausdorff connected `𝔼₀`-manifold is connected (`E0LM.isPreconnected_e0RegM`,
non-empty by density). -/
theorem e0RegM_connectedSpace [ConnectedSpace M] : ConnectedSpace (E0LM.e0RegM M) := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty M)
  obtain ⟨z, -, hz⟩ := (E0LM.dense_e0RegM (M := M)).inter_open_nonempty Set.univ isOpen_univ
    ⟨x₀, trivial⟩
  haveI : PreconnectedSpace (E0LM.e0RegM M) :=
    Subtype.preconnectedSpace E0LM.isPreconnected_e0RegM
  exact { toNonempty := ⟨⟨z, hz⟩⟩ }

/-- **`Reg M` as a `Causal.Flat.FlatSpacetime`** (WP-39m): for a Hausdorff connected
`𝔼₀`-manifold `M`, its regular part with the flat charts `E0LM.e0RegM_chartedSpace` and the
`Isom(𝐌³)`-transitions `E0LM.e0RegM_hasGroupoid`. -/
noncomputable def e0RegMFlat [T2Space M] [ConnectedSpace M] : Causal.Flat.FlatSpacetime.{0} 2 :=
  haveI := e0RegM_connectedSpace M
  Causal.Flat.FlatSpacetime.of (E0LM.e0RegM M)

theorem e0RegMFlat_carrier [T2Space M] [ConnectedSpace M] :
    (e0RegMFlat M : Type) = E0LM.e0RegM M := rfl

/-- **The holonomy of `Reg M`** (WP-39m; gx §4, the Barbot input of
`theo:globally_hyperbolic_cauchy_complete_cauchy_maximal`, l.2377–2381): if `Reg M` is globally
hyperbolic and Cauchy-complete (`brunswic2021cauchy` Thm 3 / Prop 4.9, supplied downstream) and
`π₁(Reg M)` is not metabelian, then **every** developing pair `(𝒟, ρ)` of `Reg M` (in particular
the restriction of `D_BTZ` to `reg M̃`, which WP-39n holds) has `𝒟` injective, `ρ` faithful,
discrete and torsion-free, a loxodromic element in `ρ(π₁ Reg M)` (proved in 2+1, DEC-75), a
`Γ`-invariant family of lightlike planes `(Π_w)_{w ∈ Λ(Γ)}`, and
`𝒟(Reg M̃) ⊆ Ω⁺(Λ) = ⋂ I⁺(Π_w)` (or the time-reversed statement). -/
theorem e0RegM_holonomy [T2Space M] [ConnectedSpace M] (hGH : Causal.Flat.GH (e0RegMFlat M))
    (hCC : Causal.Flat.IsCauchyComplete 2 (e0RegMFlat M)) (x₀ : e0RegMFlat M)
    (hnm : ¬IsMetabelianGroup (Causal.Deck (Causal.UniversalCover.proj (e0RegMFlat M) x₀)))
    (D : Causal.UniversalCover (e0RegMFlat M) x₀ → Causal.Minkowski 2)
    (ρ : Causal.Deck (Causal.UniversalCover.proj (e0RegMFlat M) x₀) →* Causal.Flat.isom 2)
    (hpair : Causal.Flat.IsDevelopingPair x₀ D ρ) :
      (∃ γ ∈ ρ.range, Causal.Flat.IsLoxodromic (Causal.Flat.linOf γ)) ∧ Function.Injective D ∧
      Function.Injective ρ ∧ DiscreteTopology ρ.range ∧ Causal.Flat.IsTorsionFreeSubgroup ρ.range ∧
      (∀ γ ∈ ρ.range, ∀ w ∈ Causal.Flat.limitSetJ ρ.range,
        Causal.Flat.isomPenrose γ w ∈ Causal.Flat.limitSetJ ρ.range ∧
          (fun p => γ • p) '' nullPlane w = nullPlane (Causal.Flat.isomPenrose γ w)) ∧
      ((Causal.Flat.FutureRegular (Causal.Flat.limitSetJ ρ.range) ∧
          Set.range D ⊆ Causal.Flat.omegaPlus (Causal.Flat.limitSetJ ρ.range) ∧
          Causal.Flat.ActsFreelyProperlyOn ρ.range (Causal.Flat.omegaPlus (Causal.Flat.limitSetJ ρ.range)) ∧
          Causal.Flat.omegaPlus (Causal.Flat.limitSetJ ρ.range) =
            ⋂ w ∈ Causal.Flat.limitSetJ ρ.range, (Causal.minkowski 2).Iplus ⊤ (nullPlane w)) ∨
        (Causal.Flat.PastRegular (Causal.Flat.limitSetJ ρ.range) ∧
          Set.range D ⊆ Causal.Flat.omegaMinus (Causal.Flat.limitSetJ ρ.range) ∧
          Causal.Flat.ActsFreelyProperlyOn ρ.range (Causal.Flat.omegaMinus (Causal.Flat.limitSetJ ρ.range)) ∧
          Causal.Flat.omegaMinus (Causal.Flat.limitSetJ ρ.range) =
            ⋂ w ∈ Causal.Flat.limitSetJ ρ.range, (Causal.minkowski 2).Iminus ⊤ (nullPlane w))) :=
  holonomy_package_of_isCauchyComplete (e0RegMFlat M) hGH hCC x₀ hnm D ρ hpair

/-- The existential corollary of `e0RegM_holonomy`: `Reg M` has a developing pair with the
package's properties. -/
theorem e0RegM_exists_holonomy [T2Space M] [ConnectedSpace M] (hGH : Causal.Flat.GH (e0RegMFlat M))
    (hCC : Causal.Flat.IsCauchyComplete 2 (e0RegMFlat M)) (x₀ : e0RegMFlat M)
    (hnm : ¬IsMetabelianGroup (Causal.Deck (Causal.UniversalCover.proj (e0RegMFlat M) x₀))) :
    ∃ (D : Causal.UniversalCover (e0RegMFlat M) x₀ → Causal.Minkowski 2)
      (ρ : Causal.Deck (Causal.UniversalCover.proj (e0RegMFlat M) x₀) →* Causal.Flat.isom 2),
      Causal.Flat.IsDevelopingPair x₀ D ρ ∧
      (∃ γ ∈ ρ.range, Causal.Flat.IsLoxodromic (Causal.Flat.linOf γ)) ∧ Function.Injective D ∧
      Function.Injective ρ ∧ DiscreteTopology ρ.range ∧ Causal.Flat.IsTorsionFreeSubgroup ρ.range ∧
      (∀ γ ∈ ρ.range, ∀ w ∈ Causal.Flat.limitSetJ ρ.range,
        Causal.Flat.isomPenrose γ w ∈ Causal.Flat.limitSetJ ρ.range ∧
          (fun p => γ • p) '' nullPlane w = nullPlane (Causal.Flat.isomPenrose γ w)) ∧
      ((Causal.Flat.FutureRegular (Causal.Flat.limitSetJ ρ.range) ∧
          Set.range D ⊆ Causal.Flat.omegaPlus (Causal.Flat.limitSetJ ρ.range) ∧
          Causal.Flat.ActsFreelyProperlyOn ρ.range (Causal.Flat.omegaPlus (Causal.Flat.limitSetJ ρ.range)) ∧
          Causal.Flat.omegaPlus (Causal.Flat.limitSetJ ρ.range) =
            ⋂ w ∈ Causal.Flat.limitSetJ ρ.range, (Causal.minkowski 2).Iplus ⊤ (nullPlane w)) ∨
        (Causal.Flat.PastRegular (Causal.Flat.limitSetJ ρ.range) ∧
          Set.range D ⊆ Causal.Flat.omegaMinus (Causal.Flat.limitSetJ ρ.range) ∧
          Causal.Flat.ActsFreelyProperlyOn ρ.range (Causal.Flat.omegaMinus (Causal.Flat.limitSetJ ρ.range)) ∧
          Causal.Flat.omegaMinus (Causal.Flat.limitSetJ ρ.range) =
            ⋂ w ∈ Causal.Flat.limitSetJ ρ.range, (Causal.minkowski 2).Iminus ⊤ (nullPlane w))) :=
  exists_holonomy_package_of_isCauchyComplete (e0RegMFlat M) hGH hCC x₀ hnm

end RegM

end GX
