import Yamabe.Quotient

/-!
# Stability of the trace-Sobolev quotient under comparable metrics, over the abstract model

Label (abstract layer only, NOT marked: partial by design, the Riemannian anchoring waits on
T-yamabe-scope):

* `lem:stability` — `Yamabegap.tex:697` (statement l.697–704, proof l.705–713).

> Let $\g,\g'$ be metrics on $\Sigma$ with $(1+\varepsilon)^{-1}\g\le\g'\le(1+\varepsilon)\g$ as
> quadratic forms, $\varepsilon\ge0$. Then for every $u\in W^{1,2}(\Sigma)\setminus\{0\}$ and all
> $\beta_j\ge0$,
> $(1+\varepsilon)^{-N}\ \le\ \frac{\Fq^{(\beta)}_{\g'}(u)}{\Fq^{(\beta)}_{\g}(u)}\ \le\ (1+\varepsilon)^{N}$ ,
> Consequently $\inf\Fq^{(\beta)}_{\g'}\to\inf\Fq^{(\beta)}_\g$ when $\g'\to\g$ uniformly. (l.699–703)

> Pointwise, $|\nabla u|^2_{\g'}\le(1+\varepsilon)|\nabla u|^2_\g$,
> $(1+\varepsilon)^{-N/2}\vol_\g\le\vol_{\g'}\le(1+\varepsilon)^{N/2}\vol_\g$ and
> $\bvol_{\g'}\le(1+\varepsilon)^{(N-1)/2}\bvol_\g$. Hence
> $\|\nabla u\|^2_{L^2(\g')}\le(1+\varepsilon)^{1+N/2}\,\|\nabla u\|^2_{L^2(\g)}$ ,
> $\|u\|^2_{L^{\psharp}(B_j,\g')}\le(1+\varepsilon)^{(N-1)/\psharp}\,\|u\|^2_{L^{\psharp}(B_j,\g)}$ ,
> $\|u\|^2_{L^{\pstar}(\g')}\ge(1+\varepsilon)^{-N/\pstar}\,\|u\|^2_{L^{\pstar}(\g)}$ ,
> with $(N-1)/\psharp=N/\pstar=(N-2)/2$. The quotient is therefore at most
> $(1+\varepsilon)^{1+N/2+(N-2)/2}=(1+\varepsilon)^N$ times $\Fq^{(\beta)}_\g(u)$; the lower bound
> is symmetric. (l.706–712)

## What is proved

* The pointwise comparisons (l.706) are linear algebra at a point, for Gram matrices comparable
  as quadratic forms (`QFormComparable`): dual norms (`dual_le`), determinants (`det_le`, through
  the spectrum of `R⁻ᵀ B R⁻¹` where `A = Rᵀ R`), `sqrt_det_le`, `sqrt_det_ge`, and the
  restriction to the boundary frame (`QFormComparable.congr`); on the model of
  `Yamabe.Quotient` they give `gradSq_le`, `volDensity_le`, `volDensity_ge`,
  `bvolDensity_le`, and the measure dominations `vol_le`, `bvol_le`.
* The integrated step holds over any measured data carrying these dominations
  (`traceSobolevQuot_le_of_densities`); on the model, with the paper's exponents, `dirichlet_le`
  (l.708), `normSq_bvol_le` (l.709), `normSq_vol_ge` (l.710).
* `stability` (both inequalities, product form, every `u`), `stability_ratio` (the printed ratio),
  `adm_iff`, `infF_le`, `le_infF`, and the "consequently": `tendsto_infF` (comparability constants
  `→ 0`) and `tendsto_infF_of_uniformlyClose` (`g' → g` uniformly).
* Witness: `toy_comparable`, `toy_stability` (the toy metric and its rescaling by `1 + ε`);
  `toy_F_zero_one` (the printed ratio is `0/0` at `β = 0`, `u = 1`).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `g, g'` metrics on `Σ` | ⚠ two `FrameMetric`s on one `MeasuredModel` (a reading, see SCOPE) |
| `(1+ε)^{-1} g ≤ g' ≤ (1+ε) g` as quadratic forms | ✓ carried (`Comparable ε g g'`, at every point) |
| `ε ≥ 0` | ✓ carried |
| `u ∈ W^{1,2}(Σ) ∖ {0}` | ⚠ weakened: any `u : D` (product form); the ratio form assumes `F^(β)_g(u) ≠ 0` |
| `β_j ≥ 0` | ✓ carried |
| `N ≥ 3` (l.605) | ✓ carried |
| "`g' → g` uniformly" | ⚠ read as `sup_x ‖g' - g‖_g → 0` (`UniformlyClose`), or directly as comparability with `ε → 0` |

## SCOPE (disclosed)

* Abstract layer only (T-yamabe-quotient, DEC-139): `vol_g = √det G · μ` and
  `bvol_g = √det (Pᵀ G P) · μb` are the model's definitions, the Riemannian volume read in a
  measurable frame. The passage from a Riemannian manifold to the model waits on T-yamabe-scope,
  hence the label is not marked.
* The printed statement is a ratio; it is `0/0` when `F^(β)_g(u) = 0` (e.g. every `β_j = 0` and
  `u` constant). The product form `stability` holds for every `u`; `stability_ratio` assumes
  `F^(β)_g(u) ≠ 0`.
* "`g' → g` uniformly" is read in the norm of `g` itself (`UniformlyClose η g g'`:
  `|g'(v,v) - g(v,v)| ≤ η g(v,v)` everywhere), which on a compact manifold is uniform `C⁰`
  convergence; `tendsto_infF` takes the comparability constants directly.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open MeasureTheory Filter Topology Matrix
open scoped ENNReal NNReal Matrix MatrixOrder

noncomputable section

namespace Yamabe

/-! ## Pointwise linear algebra (l.706) -/

section Pointwise

variable {m : Type*} [Fintype m]

/-- `c⁻¹ A ≤ B ≤ c A` as quadratic forms. -/
def QFormComparable (c : ℝ) (A B : Matrix m m ℝ) : Prop :=
  ∀ v : m → ℝ, c⁻¹ * (v ⬝ᵥ (A *ᵥ v)) ≤ v ⬝ᵥ (B *ᵥ v) ∧ v ⬝ᵥ (B *ᵥ v) ≤ c * (v ⬝ᵥ (A *ᵥ v))

variable {c : ℝ} {A B : Matrix m m ℝ}

/-- The comparison is symmetric. -/
lemma QFormComparable.symm (hc : 0 < c) (h : QFormComparable c A B) : QFormComparable c B A := by
  intro v
  obtain ⟨h1, h2⟩ := h v
  exact ⟨(inv_mul_le_iff₀ hc).mpr h2, (inv_mul_le_iff₀ hc).mp h1⟩

/-- `v ⬝ (Pᵀ A P) v = (P v) ⬝ A (P v)`. -/
lemma dotProduct_transpose_mul_mul_mulVec {k : Type*} [Fintype k] (A : Matrix m m ℝ)
    (P : Matrix m k ℝ) (v : k → ℝ) :
    v ⬝ᵥ ((Pᵀ * A * P) *ᵥ v) = (P *ᵥ v) ⬝ᵥ (A *ᵥ (P *ᵥ v)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

/-- The restriction to a subspace (here the boundary frame `P`) keeps the comparison. -/
lemma QFormComparable.congr {k : Type*} [Fintype k] (h : QFormComparable c A B)
    (P : Matrix m k ℝ) : QFormComparable c (Pᵀ * A * P) (Pᵀ * B * P) := by
  intro v
  rw [dotProduct_transpose_mul_mul_mulVec, dotProduct_transpose_mul_mul_mulVec]
  exact h (P *ᵥ v)

omit [Fintype m] in
/-- A real positive definite matrix is symmetric. -/
lemma transpose_eq_of_posDef {A : Matrix m m ℝ} (hA : A.PosDef) : Aᵀ = A := by
  have := hA.isHermitian
  rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this

/-- A symmetric bilinear form is symmetric. -/
lemma dotProduct_mulVec_symm {A : Matrix m m ℝ} (hA : Aᵀ = A) (x y : m → ℝ) :
    x ⬝ᵥ (A *ᵥ y) = y ⬝ᵥ (A *ᵥ x) := by
  have : x ᵥ* A = A *ᵥ x := by
    calc x ᵥ* A = x ᵥ* Aᵀ := by rw [hA]
      _ = A *ᵥ x := vecMul_transpose A x
  rw [dotProduct_mulVec, this, dotProduct_comm]

/-- `A (A⁻¹ ξ) = ξ`. -/
lemma mulVec_inv_mulVec [DecidableEq m] {A : Matrix m m ℝ} (hA : A.PosDef) (ξ : m → ℝ) :
    A *ᵥ (A⁻¹ *ᵥ ξ) = ξ := by
  rw [mulVec_mulVec, mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA.det_pos.ne'), one_mulVec]

/-- `v ⬝ A v ≥ 0`. -/
lemma dotProduct_mulVec_nonneg_of_posDef {A : Matrix m m ℝ} (hA : A.PosDef) (v : m → ℝ) :
    0 ≤ v ⬝ᵥ (A *ᵥ v) := by
  simpa using hA.posSemidef.dotProduct_mulVec_nonneg v

/-- Dual norms: `|ξ|²_{B} ≤ c |ξ|²_{A}` (l.706, `|∇u|²_{g'} ≤ (1+ε)|∇u|²_g`). -/
theorem dual_le [DecidableEq m] (hc : 0 < c) (hA : A.PosDef) (hB : B.PosDef) (h : QFormComparable c A B)
    (ξ : m → ℝ) : ξ ⬝ᵥ (B⁻¹ *ᵥ ξ) ≤ c * (ξ ⬝ᵥ (A⁻¹ *ᵥ ξ)) := by
  set y := A⁻¹ *ᵥ ξ with hy
  set w := B⁻¹ *ᵥ ξ with hw
  have hAy : A *ᵥ y = ξ := mulVec_inv_mulVec hA ξ
  have hBw : B *ᵥ w = ξ := mulVec_inv_mulVec hB ξ
  have hAs := transpose_eq_of_posDef hA
  have hBs := transpose_eq_of_posDef hB
  -- a = ξ ⬝ y = y ⬝ A y ; b = ξ ⬝ w = w ⬝ B w ; y ⬝ A w = b
  have ha : y ⬝ᵥ (A *ᵥ y) = ξ ⬝ᵥ y := by rw [hAy, dotProduct_comm]
  have hb : w ⬝ᵥ (B *ᵥ w) = ξ ⬝ᵥ w := by rw [hBw, dotProduct_comm]
  have hyw : y ⬝ᵥ (A *ᵥ w) = ξ ⬝ᵥ w := by
    rw [dotProduct_mulVec_symm hAs, hAy, dotProduct_comm]
  have hwA : w ⬝ᵥ (A *ᵥ w) ≤ c * (ξ ⬝ᵥ w) := by
    have := (h w).1
    rw [hb] at this
    exact (inv_mul_le_iff₀ hc).mp this
  have hpos := dotProduct_mulVec_nonneg_of_posDef hA (c • y - w)
  have hexp : (c • y - w) ⬝ᵥ (A *ᵥ (c • y - w)) =
      c ^ 2 * (y ⬝ᵥ (A *ᵥ y)) - 2 * c * (y ⬝ᵥ (A *ᵥ w)) + w ⬝ᵥ (A *ᵥ w) := by
    have hsym : w ⬝ᵥ (A *ᵥ y) = y ⬝ᵥ (A *ᵥ w) := dotProduct_mulVec_symm hAs w y
    simp only [mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, hsym]
    ring
  rw [hexp, ha, hyw] at hpos
  -- 0 ≤ c² a - 2 c b + wAw ≤ c² a - c b
  have : c * (ξ ⬝ᵥ w) ≤ c * (c * (ξ ⬝ᵥ y)) := by nlinarith
  exact le_of_mul_le_mul_left this hc

/-- Determinants: `det B ≤ c^k det A`, `k = dim` (only `B ≤ c A` is used). -/
theorem det_le [DecidableEq m] (hA : A.PosDef) (hB : B.PosDef) (h : QFormComparable c A B) :
    B.det ≤ c ^ Fintype.card m * A.det := by
  obtain ⟨R, hR⟩ : ∃ R : Matrix m m ℝ, A = star R * R :=
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.posSemidef.nonneg
  rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at hR
  have hdetA : A.det = R.det ^ 2 := by rw [hR, det_mul, det_transpose]; ring
  have hRdet : R.det ≠ 0 := by
    intro h0; have := hA.det_pos; rw [hdetA, h0] at this; simp at this
  set S := R⁻¹ with hS
  have hRS : R * S = 1 := mul_nonsing_inv R (isUnit_iff_ne_zero.mpr hRdet)
  have hSinj : Function.Injective S.mulVec := by
    intro v w hvw
    have := congrArg (fun z => R *ᵥ z) hvw
    simpa [mulVec_mulVec, hRS] using this
  set C := Sᵀ * B * S with hC
  have hCpos : C.PosDef := by
    have := hB.conjTranspose_mul_mul_same hSinj
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  have hAdot : ∀ v, (S *ᵥ v) ⬝ᵥ (A *ᵥ (S *ᵥ v)) = v ⬝ᵥ v := by
    intro v
    rw [hR, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, mulVec_mulVec, hRS,
      one_mulVec]
  have hev : ∀ i, hCpos.isHermitian.eigenvalues i ≤ c := by
    intro i
    set w : m → ℝ := ⇑(hCpos.isHermitian.eigenvectorBasis i) with hwdef
    have hw : w ≠ 0 :=
      (WithLp.ofLp_eq_zero 2).ne.2 <| hCpos.isHermitian.eigenvectorBasis.orthonormal.ne_zero i
    have h1 : w ⬝ᵥ (C *ᵥ w) = hCpos.isHermitian.eigenvalues i * (w ⬝ᵥ w) := by
      rw [hwdef, hCpos.isHermitian.mulVec_eigenvectorBasis, dotProduct_smul, smul_eq_mul]
    have h2 : w ⬝ᵥ (C *ᵥ w) ≤ c * (w ⬝ᵥ w) := by
      rw [hC, dotProduct_transpose_mul_mul_mulVec, ← hAdot w]
      exact (h (S *ᵥ w)).2
    have hww : 0 < w ⬝ᵥ w := by
      have := (PosDef.one (n := m) (R := ℝ)).dotProduct_mulVec_pos hw
      simpa using this
    rw [h1] at h2
    exact le_of_mul_le_mul_right h2 hww
  have hdetC : C.det = B.det / A.det := by
    rw [hC, det_mul, det_mul, det_transpose, hS, det_nonsing_inv, Ring.inverse_eq_inv', hdetA]
    field_simp
  have hprod : C.det ≤ c ^ Fintype.card m := by
    rw [hCpos.isHermitian.det_eq_prod_eigenvalues]
    simp only [RCLike.ofReal_real_eq_id, id]
    calc ∏ i, hCpos.isHermitian.eigenvalues i ≤ ∏ _i : m, c :=
          Finset.prod_le_prod (fun i _ => (hCpos.eigenvalues_pos i).le) (fun i _ => hev i)
      _ = c ^ Fintype.card m := by simp
  rw [hdetC, div_le_iff₀ hA.det_pos] at hprod
  linarith

/-- Volume densities: `√det B ≤ c^{k/2} √det A` (l.706, `vol_{g'} ≤ (1+ε)^{N/2} vol_g`). -/
theorem sqrt_det_le [DecidableEq m] (hc : 0 < c) (hA : A.PosDef) (hB : B.PosDef) (h : QFormComparable c A B) :
    Real.sqrt B.det ≤ c ^ ((Fintype.card m : ℝ) / 2) * Real.sqrt A.det := by
  have h1 := Real.sqrt_le_sqrt (det_le hA hB h)
  rw [Real.sqrt_mul (pow_nonneg hc.le _)] at h1
  have h2 : Real.sqrt (c ^ Fintype.card m) = c ^ ((Fintype.card m : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hc.le]
    ring_nf
  rwa [h2] at h1

/-- Volume densities, lower bound: `c^{-k/2} √det A ≤ √det B` (l.706). -/
theorem sqrt_det_ge [DecidableEq m] (hc : 0 < c) (hA : A.PosDef) (hB : B.PosDef) (h : QFormComparable c A B) :
    c ^ (-((Fintype.card m : ℝ) / 2)) * Real.sqrt A.det ≤ Real.sqrt B.det := by
  have h1 := sqrt_det_le hc hB hA (h.symm hc)
  rw [Real.rpow_neg hc.le]
  exact (inv_mul_le_iff₀ (Real.rpow_pos_of_pos hc _)).mpr h1

end Pointwise

/-! ## The integrated step, over any measured data carrying the densities -/

section Integrated

variable {X : Type*} [MeasurableSpace X] {n N : ℕ}

/-- `a ≤ C b` and `b ≤ C' a` in `ℝ≥0∞` give `a.toReal ≤ C b.toReal` (both infinite together). -/
lemma toReal_le_of_le_mul {a b : ℝ≥0∞} {C C' : ℝ} (hC : 0 ≤ C) (h : a ≤ ENNReal.ofReal C * b)
    (h' : b ≤ ENNReal.ofReal C' * a) : a.toReal ≤ C * b.toReal := by
  rcases eq_or_ne b ∞ with hb | hb
  · have ha : a = ∞ := by
      by_contra ha
      have hlt : ENNReal.ofReal C' * a < ∞ :=
        ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr ha)
      rw [hb] at h'
      exact absurd (lt_of_le_of_lt h' hlt) (lt_irrefl _)
    simp [ha, hb]
  · have hfin : ENNReal.ofReal C * b ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb
    have := ENNReal.toReal_mono hfin h
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] at this

/-- Energy under domination of the measure and of the density. -/
lemma lintegral_le_of_le_smul {μ μ' : Measure X} {f f' : X → ℝ≥0∞} {a b : ℝ} (ha : 0 ≤ a)
    (hμ : μ' ≤ ENNReal.ofReal b • μ) (hf : ∀ x, f' x ≤ ENNReal.ofReal a * f x) :
    ∫⁻ x, f' x ∂μ' ≤ ENNReal.ofReal (a * b) * ∫⁻ x, f x ∂μ := by
  calc ∫⁻ x, f' x ∂μ' ≤ ∫⁻ x, ENNReal.ofReal a * f x ∂μ' := lintegral_mono hf
    _ = ENNReal.ofReal a * ∫⁻ x, f x ∂μ' := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal a * ∫⁻ x, f x ∂(ENNReal.ofReal b • μ) := by
        gcongr
    _ = ENNReal.ofReal (a * b) * ∫⁻ x, f x ∂μ := by
        rw [lintegral_smul_measure, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul ha]

/-- Squared norms under a measure domination `ν' ≤ A ν` (both ways, so that infinite norms are
infinite together): `‖f‖²_{L^q(ν')} ≤ A^{2/q} ‖f‖²_{L^q(ν)}`. -/
theorem normSq_le_of_le_smul {q : ℝ} (hq : 0 < q) {ν ν' : Measure X} {a a' : ℝ} (ha : 0 ≤ a)
    (ha' : 0 ≤ a') (h : ν' ≤ ENNReal.ofReal a • ν) (h' : ν ≤ ENNReal.ofReal a' • ν') (f : X → ℝ) :
    normSq ν' q f ≤ a ^ (2 / q) * normSq ν q f := by
  have key : ∀ {μ μ' : Measure X} {b : ℝ}, 0 ≤ b → μ' ≤ ENNReal.ofReal b • μ →
      eLpNorm f (ENNReal.ofReal q) μ' ≤
        ENNReal.ofReal (b ^ (1 / q)) * eLpNorm f (ENNReal.ofReal q) μ := by
    intro μ μ' b hb hμ
    calc eLpNorm f (ENNReal.ofReal q) μ' ≤ eLpNorm f (ENNReal.ofReal q) (ENNReal.ofReal b • μ) :=
          eLpNorm_mono_measure f hμ
      _ = ENNReal.ofReal b ^ (1 / ENNReal.ofReal q).toReal • eLpNorm f (ENNReal.ofReal q) μ :=
          eLpNorm_smul_measure_of_ne_top ENNReal.ofReal_ne_top f _
      _ = ENNReal.ofReal (b ^ (1 / q)) * eLpNorm f (ENNReal.ofReal q) μ := by
          rw [smul_eq_mul, ENNReal.ofReal_rpow_of_nonneg hb (by positivity)]
          congr 2
          rw [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofReal hq.le, one_div]
  have h3 := toReal_le_of_le_mul (Real.rpow_nonneg ha _) (key ha h) (key ha' h')
  unfold normSq
  calc (eLpNorm f (ENNReal.ofReal q) ν').toReal ^ 2
      ≤ (a ^ (1 / q) * (eLpNorm f (ENNReal.ofReal q) ν).toReal) ^ 2 :=
        pow_le_pow_left₀ ENNReal.toReal_nonneg h3 2
    _ = a ^ (2 / q) * (eLpNorm f (ENNReal.ofReal q) ν).toReal ^ 2 := by
        rw [mul_pow, ← Real.rpow_natCast (a ^ (1 / q)), ← Real.rpow_mul ha]
        congr 2
        push_cast
        ring

/-- The integrated step of lem:stability over any measured data carrying the pointwise
comparisons of l.706 (as measure and energy-density dominations): the quotient grows by at most
`c^N`, `c = 1 + ε`. -/
theorem traceSobolevQuot_le_of_densities (hN : 3 ≤ N) {β : Fin n → ℝ} (hβ : ∀ j, 0 ≤ β j)
    {c : ℝ} (hc : 1 ≤ c) {vol vol' : Measure X} {bvol bvol' : Fin n → Measure X}
    (hvol : vol' ≤ ENNReal.ofReal (c ^ ((N : ℝ) / 2)) • vol)
    (hvol' : vol ≤ ENNReal.ofReal (c ^ ((N : ℝ) / 2)) • vol')
    (hbvol : ∀ j, bvol' j ≤ ENNReal.ofReal (c ^ (((N : ℝ) - 1) / 2)) • bvol j)
    (hbvol' : ∀ j, bvol j ≤ ENNReal.ofReal (c ^ (((N : ℝ) - 1) / 2)) • bvol' j)
    {e e' : X → ℝ≥0∞} (he : ∀ x, e' x ≤ ENNReal.ofReal c * e x)
    (he' : ∀ x, e x ≤ ENNReal.ofReal c * e' x) (v t : X → ℝ) :
    traceSobolevQuot N vol' bvol' β (∫⁻ x, e' x ∂vol').toReal v t ≤
      c ^ (N : ℝ) * traceSobolevQuot N vol bvol β (∫⁻ x, e x ∂vol).toReal v t := by
  have hN' : (3 : ℝ) ≤ N := three_le_cast hN
  have hc0 : 0 < c := by linarith
  -- the three integrated comparisons (l.708–710)
  have hE : (∫⁻ x, e' x ∂vol').toReal ≤ c ^ (1 + (N : ℝ) / 2) * (∫⁻ x, e x ∂vol).toReal := by
    have h1 := lintegral_le_of_le_smul hc0.le hvol he
    have h2 := lintegral_le_of_le_smul hc0.le hvol' he'
    have hpow : c * c ^ ((N : ℝ) / 2) = c ^ (1 + (N : ℝ) / 2) := by
      rw [Real.rpow_add hc0, Real.rpow_one]
    rw [hpow] at h1 h2
    exact toReal_le_of_le_mul (by positivity) h1 h2
  have hB : ∀ j, normSq (bvol' j) (pSharp N) t ≤
      c ^ (((N : ℝ) - 2) / 2) * normSq (bvol j) (pSharp N) t := by
    intro j
    have := normSq_le_of_le_smul (pSharp_pos hN) (by positivity) (by positivity)
      (hbvol j) (hbvol' j) t
    rwa [← Real.rpow_mul hc0.le, show ((N : ℝ) - 1) / 2 * (2 / pSharp N) = ((N : ℝ) - 1) / pSharp N by
      ring, sub_one_div_pSharp hN] at this
  have hDle : ∀ {μ μ' : Measure X}, μ' ≤ ENNReal.ofReal (c ^ ((N : ℝ) / 2)) • μ →
      μ ≤ ENNReal.ofReal (c ^ ((N : ℝ) / 2)) • μ' →
      normSq μ' (pStar N) v ≤ c ^ (((N : ℝ) - 2) / 2) * normSq μ (pStar N) v := by
    intro μ μ' h1 h2
    have := normSq_le_of_le_smul (pStar_pos hN) (by positivity) (by positivity) h1 h2 v
    rwa [← Real.rpow_mul hc0.le, show (N : ℝ) / 2 * (2 / pStar N) = (N : ℝ) / pStar N by ring,
      natCast_div_pStar hN] at this
  have hD := hDle hvol' hvol
  have hD' := hDle hvol hvol'
  -- the quotient
  unfold traceSobolevQuot
  set E := (∫⁻ x, e x ∂vol).toReal
  set E' := (∫⁻ x, e' x ∂vol').toReal
  set D := normSq vol (pStar N) v
  set D' := normSq vol' (pStar N) v
  set S := ∑ j, β j * normSq (bvol j) (pSharp N) t
  set S' := ∑ j, β j * normSq (bvol' j) (pSharp N) t
  have hE0 : 0 ≤ E := ENNReal.toReal_nonneg
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => mul_nonneg (hβ j) (normSq_nonneg _ _ _)
  have hS : S' ≤ c ^ (((N : ℝ) - 2) / 2) * S := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => by
      rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left (hB j) (hβ j)
  have hcpow : c ^ (((N : ℝ) - 2) / 2) ≤ c ^ (1 + (N : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hc (by linarith)
  have ha := (aN_pos hN).le
  have hnum0 : 0 ≤ aN N * E + S := add_nonneg (mul_nonneg ha hE0) hS0
  have hnum : aN N * E' + S' ≤ c ^ (1 + (N : ℝ) / 2) * (aN N * E + S) := by
    have h1 := mul_le_mul_of_nonneg_left hE ha
    have h2 := mul_le_mul_of_nonneg_right hcpow hS0
    nlinarith
  have hk : c ^ (N : ℝ) = c ^ (1 + (N : ℝ) / 2) * c ^ (((N : ℝ) - 2) / 2) := by
    rw [← Real.rpow_add hc0]; congr 1; ring
  rcases (show 0 ≤ D' from normSq_nonneg _ _ _).eq_or_lt with hD'0 | hD'pos
  · rw [← hD'0, div_zero]
    exact mul_nonneg (by positivity) (div_nonneg hnum0 (normSq_nonneg _ _ _))
  have hDpos : 0 < D := by
    by_contra hD0
    have : D = 0 := le_antisymm (not_lt.mp hD0) (normSq_nonneg _ _ _)
    rw [this, mul_zero] at hD'
    linarith
  rw [div_le_iff₀ hD'pos]
  calc aN N * E' + S' ≤ c ^ (1 + (N : ℝ) / 2) * (aN N * E + S) := hnum
    _ = c ^ (1 + (N : ℝ) / 2) * ((aN N * E + S) / D) * D := by field_simp
    _ ≤ c ^ (1 + (N : ℝ) / 2) * ((aN N * E + S) / D) * (c ^ (((N : ℝ) - 2) / 2) * D') := by
        gcongr
    _ = c ^ (N : ℝ) * ((aN N * E + S) / D) * D' := by rw [hk]; ring

end Integrated

/-! ## lem:stability on the model -/

namespace MeasuredModel

variable {X D : Type*} [MeasurableSpace X] [AddCommGroup D] [Module ℝ D] {N n : ℕ}
variable (M : MeasuredModel X D N n)

/-- The hypothesis of lem:stability: `(1+ε)^{-1} g ≤ g' ≤ (1+ε) g` as quadratic forms, at every
point. -/
def Comparable (ε : ℝ) (g g' : FrameMetric X N) : Prop :=
  ∀ x, QFormComparable (1 + ε) (g.G x) (g'.G x)

variable {M} {g g' : FrameMetric X N} {ε : ℝ}

omit [MeasurableSpace X] in
/-- The hypothesis of lem:stability is symmetric in `g, g'`. -/
lemma Comparable.symm (hε : 0 ≤ ε) (h : Comparable ε g g') : Comparable ε g' g :=
  fun x => (h x).symm (by linarith)

/-- Pointwise (l.706): `|∇u|²_{g'} ≤ (1+ε) |∇u|²_g`. -/
theorem gradSq_le (hε : 0 ≤ ε) (h : Comparable ε g g') (u : D) (x : X) :
    M.gradSq g' u x ≤ (1 + ε) * M.gradSq g u x :=
  dual_le (by linarith) (g.posDef x) (g'.posDef x) (h x) (M.d u x)

omit [MeasurableSpace X] in
/-- Pointwise (l.706): `vol_{g'} ≤ (1+ε)^{N/2} vol_g`. -/
theorem volDensity_le (hε : 0 ≤ ε) (h : Comparable ε g g') (x : X) :
    Real.sqrt (g'.G x).det ≤ (1 + ε) ^ ((N : ℝ) / 2) * Real.sqrt (g.G x).det := by
  simpa using sqrt_det_le (by linarith) (g.posDef x) (g'.posDef x) (h x)

omit [MeasurableSpace X] in
/-- Pointwise (l.706): `(1+ε)^{-N/2} vol_g ≤ vol_{g'}`. -/
theorem volDensity_ge (hε : 0 ≤ ε) (h : Comparable ε g g') (x : X) :
    (1 + ε) ^ (-((N : ℝ) / 2)) * Real.sqrt (g.G x).det ≤ Real.sqrt (g'.G x).det := by
  simpa using sqrt_det_ge (by linarith) (g.posDef x) (g'.posDef x) (h x)

/-- Pointwise (l.706): `bvol_{g'} ≤ (1+ε)^{(N-1)/2} bvol_g`. -/
theorem bvolDensity_le (hN : 1 ≤ N) (hε : 0 ≤ ε) (h : Comparable ε g g') (x : X) :
    Real.sqrt ((M.P x)ᵀ * g'.G x * M.P x).det ≤
      (1 + ε) ^ (((N : ℝ) - 1) / 2) * Real.sqrt ((M.P x)ᵀ * g.G x * M.P x).det := by
  have hA := (g.posDef x).conjTranspose_mul_mul_same (M.P_injective x)
  have hB := (g'.posDef x).conjTranspose_mul_mul_same (M.P_injective x)
  rw [conjTranspose_eq_transpose_of_trivial] at hA hB
  have := sqrt_det_le (by linarith) hA hB ((h x).congr (M.P x))
  rwa [Fintype.card_fin, Nat.cast_sub hN, Nat.cast_one] at this

/-- `vol_{g'} ≤ (1+ε)^{N/2} vol_g` as measures. -/
theorem vol_le (hε : 0 ≤ ε) (h : Comparable ε g g') :
    M.vol g' ≤ ENNReal.ofReal ((1 + ε) ^ ((N : ℝ) / 2)) • M.vol g := by
  unfold MeasuredModel.vol
  rw [← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  refine withDensity_mono (ae_of_all _ fun x => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (volDensity_le hε h x)

/-- `bvol_{g'} ≤ (1+ε)^{(N-1)/2} bvol_g` as measures. -/
theorem bvol_le (hN : 1 ≤ N) (hε : 0 ≤ ε) (h : Comparable ε g g') (j : Fin n) :
    M.bvol g' j ≤ ENNReal.ofReal ((1 + ε) ^ (((N : ℝ) - 1) / 2)) • M.bvol g j := by
  unfold MeasuredModel.bvol
  rw [← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  refine withDensity_mono (ae_of_all _ fun x => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (M.bvolDensity_le hN hε h x)

/-- l.708: `‖∇u‖²_{L²(g')} ≤ (1+ε)^{1+N/2} ‖∇u‖²_{L²(g)}`. -/
theorem dirichlet_le (hε : 0 ≤ ε) (h : Comparable ε g g') (u : D) :
    M.dirichlet g' u ≤ (1 + ε) ^ (1 + (N : ℝ) / 2) * M.dirichlet g u := by
  have hc : (0 : ℝ) ≤ 1 + ε := by linarith
  have he : ∀ {g g' : FrameMetric X N}, Comparable ε g g' → ∀ x,
      ENNReal.ofReal (M.gradSq g' u x) ≤ ENNReal.ofReal (1 + ε) * ENNReal.ofReal (M.gradSq g u x) :=
    fun h x => by rw [← ENNReal.ofReal_mul hc]; exact ENNReal.ofReal_le_ofReal (M.gradSq_le hε h u x)
  have h1 := lintegral_le_of_le_smul hc (M.vol_le hε h) (he h)
  have h2 := lintegral_le_of_le_smul hc (M.vol_le hε (h.symm hε)) (he (h.symm hε))
  have hpow : (1 + ε) * (1 + ε) ^ ((N : ℝ) / 2) = (1 + ε) ^ (1 + (N : ℝ) / 2) := by
    rw [Real.rpow_add (by linarith), Real.rpow_one]
  rw [hpow] at h1 h2
  exact toReal_le_of_le_mul (by positivity) h1 h2

/-- l.709: `‖u‖²_{L^{p♯}(B_j,g')} ≤ (1+ε)^{(N-1)/p♯} ‖u‖²_{L^{p♯}(B_j,g)}`. -/
theorem normSq_bvol_le (hN : 3 ≤ N) (hε : 0 ≤ ε) (h : Comparable ε g g') (j : Fin n) (u : D) :
    normSq (M.bvol g' j) (pSharp N) (M.tr u) ≤
      (1 + ε) ^ (((N : ℝ) - 1) / pSharp N) * normSq (M.bvol g j) (pSharp N) (M.tr u) := by
  have hc : (0 : ℝ) < 1 + ε := by linarith
  have := normSq_le_of_le_smul (pSharp_pos hN) (by positivity) (by positivity)
    (M.bvol_le (by omega) hε h j) (M.bvol_le (by omega) hε (h.symm hε) j) (M.tr u)
  rwa [← Real.rpow_mul hc.le, show ((N : ℝ) - 1) / 2 * (2 / pSharp N) = ((N : ℝ) - 1) / pSharp N by
    ring] at this

/-- l.710: `‖u‖²_{L^{p*}(g')} ≥ (1+ε)^{-N/p*} ‖u‖²_{L^{p*}(g)}`. -/
theorem normSq_vol_ge (hN : 3 ≤ N) (hε : 0 ≤ ε) (h : Comparable ε g g') (u : D) :
    (1 + ε) ^ (-((N : ℝ) / pStar N)) * normSq (M.vol g) (pStar N) (M.val u) ≤
      normSq (M.vol g') (pStar N) (M.val u) := by
  have hc : (0 : ℝ) < 1 + ε := by linarith
  have := normSq_le_of_le_smul (pStar_pos hN) (by positivity) (by positivity)
    (M.vol_le hε (h.symm hε)) (M.vol_le hε h) (M.val u)
  rw [← Real.rpow_mul hc.le, show (N : ℝ) / 2 * (2 / pStar N) = (N : ℝ) / pStar N by ring] at this
  rw [Real.rpow_neg hc.le]
  exact (inv_mul_le_iff₀ (by positivity)).mpr this

/-- lem:stability, product form, both inequalities, every `u` (l.701). -/
theorem stability (hN : 3 ≤ N) (hε : 0 ≤ ε) (h : Comparable ε g g') {β : Fin n → ℝ}
    (hβ : ∀ j, 0 ≤ β j) (u : D) :
    (1 + ε) ^ (-(N : ℝ)) * M.F g β u ≤ M.F g' β u ∧
      M.F g' β u ≤ (1 + ε) ^ (N : ℝ) * M.F g β u := by
  have hc : (1 : ℝ) ≤ 1 + ε := by linarith
  have up : ∀ {g g' : FrameMetric X N}, Comparable ε g g' →
      M.F g' β u ≤ (1 + ε) ^ (N : ℝ) * M.F g β u := by
    intro g g' h
    have he : ∀ {g g' : FrameMetric X N}, Comparable ε g g' → ∀ x,
        ENNReal.ofReal (M.gradSq g' u x) ≤
          ENNReal.ofReal (1 + ε) * ENNReal.ofReal (M.gradSq g u x) :=
      fun h x => by
        rw [← ENNReal.ofReal_mul (by linarith)]
        exact ENNReal.ofReal_le_ofReal (M.gradSq_le hε h u x)
    exact traceSobolevQuot_le_of_densities hN hβ hc (M.vol_le hε h) (M.vol_le hε (h.symm hε))
      (fun j => M.bvol_le (by omega) hε h j) (fun j => M.bvol_le (by omega) hε (h.symm hε) j)
      (he h) (he (h.symm hε)) (M.val u) (M.tr u)
  refine ⟨?_, up h⟩
  rw [Real.rpow_neg (by linarith)]
  exact (inv_mul_le_iff₀ (by positivity)).mpr (up (h.symm hε))

/-- lem:stability, the printed ratio form (l.701), when `F^(β)_g(u) ≠ 0`. -/
theorem stability_ratio (hN : 3 ≤ N) (hε : 0 ≤ ε) (h : Comparable ε g g') {β : Fin n → ℝ}
    (hβ : ∀ j, 0 ≤ β j) (u : D) (hF : M.F g β u ≠ 0) :
    (1 + ε) ^ (-(N : ℝ)) ≤ M.F g' β u / M.F g β u ∧
      M.F g' β u / M.F g β u ≤ (1 + ε) ^ (N : ℝ) := by
  have hpos : 0 < M.F g β u := lt_of_le_of_ne (M.F_nonneg g hN hβ u) (Ne.symm hF)
  obtain ⟨h1, h2⟩ := M.stability hN hε h hβ u
  exact ⟨(le_div_iff₀ hpos).mpr h1, (div_le_iff₀ hpos).mpr h2⟩

/-- Competitors are the same for comparable metrics. -/
theorem adm_iff (hN : 3 ≤ N) (hε : 0 ≤ ε) (h : Comparable ε g g') (u : D) :
    M.Adm g' u ↔ M.Adm g u := by
  have hc : (0 : ℝ) < 1 + ε := by linarith
  have h1 := normSq_le_of_le_smul (pStar_pos hN) (by positivity) (by positivity)
    (M.vol_le hε h) (M.vol_le hε (h.symm hε)) (M.val u)
  have h2 := normSq_le_of_le_smul (pStar_pos hN) (by positivity) (by positivity)
    (M.vol_le hε (h.symm hε)) (M.vol_le hε h) (M.val u)
  have hk : 0 < ((1 + ε) ^ ((N : ℝ) / 2)) ^ (2 / pStar N) := by positivity
  have n1 := normSq_nonneg (M.vol g) (pStar N) (M.val u)
  have n2 := normSq_nonneg (M.vol g') (pStar N) (M.val u)
  unfold Adm
  constructor
  · intro hp
    by_contra hn
    have h0 : normSq (M.vol g) (pStar N) (M.val u) = 0 := le_antisymm (not_lt.mp hn) n1
    rw [h0, mul_zero] at h1
    linarith
  · intro hp
    by_contra hn
    have h0 : normSq (M.vol g') (pStar N) (M.val u) = 0 := le_antisymm (not_lt.mp hn) n2
    rw [h0, mul_zero] at h2
    linarith

/-- `inf F^(β)_{g'} ≤ (1+ε)^N inf F^(β)_g`. -/
theorem infF_le (hN : 3 ≤ N) (hε : 0 ≤ ε) (h : Comparable ε g g') {β : Fin n → ℝ}
    (hβ : ∀ j, 0 ≤ β j) : M.infF g' β ≤ (1 + ε) ^ (N : ℝ) * M.infF g β := by
  have hcN : 0 < (1 + ε) ^ (N : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hbdd : ∀ g'' : FrameMetric X N, BddBelow (M.F g'' β '' {u | M.Adm g'' u}) :=
    fun g'' => ⟨0, by rintro _ ⟨u, _, rfl⟩; exact M.F_nonneg g'' hN hβ u⟩
  have hset : {u | M.Adm g' u} = {u | M.Adm g u} := by
    ext u; exact M.adm_iff hN hε h u
  unfold infF
  rcases Set.eq_empty_or_nonempty {u | M.Adm g u} with he | hne
  · rw [hset, he, Set.image_empty, Set.image_empty, Real.sInf_empty, mul_zero]
  · rw [← div_le_iff₀' hcN]
    refine le_csInf (hne.image _) ?_
    rintro _ ⟨u, hu, rfl⟩
    rw [div_le_iff₀' hcN]
    have hu' : u ∈ {u | M.Adm g' u} := by rw [hset]; exact hu
    exact (csInf_le (hbdd g') ⟨u, hu', rfl⟩).trans (M.stability hN hε h hβ u).2

/-- `(1+ε)^{-N} inf F^(β)_g ≤ inf F^(β)_{g'}`. -/
theorem le_infF (hN : 3 ≤ N) (hε : 0 ≤ ε) (h : Comparable ε g g') {β : Fin n → ℝ}
    (hβ : ∀ j, 0 ≤ β j) : (1 + ε) ^ (-(N : ℝ)) * M.infF g β ≤ M.infF g' β := by
  have := M.infF_le hN hε (h.symm hε) hβ
  rw [Real.rpow_neg (by linarith)]
  exact (inv_mul_le_iff₀ (Real.rpow_pos_of_pos (by linarith) _)).mpr this

/-- lem:stability, "consequently": `inf F^(β)_{g_i} → inf F^(β)_g` along any family whose
comparability constants tend to `0`. -/
theorem tendsto_infF (hN : 3 ≤ N) {β : Fin n → ℝ} (hβ : ∀ j, 0 ≤ β j) {ι : Type*}
    {l : Filter ι} (gs : ι → FrameMetric X N) (εs : ι → ℝ) (hε : ∀ᶠ i in l, 0 ≤ εs i)
    (hεt : Tendsto εs l (𝓝 0)) (h : ∀ᶠ i in l, Comparable (εs i) g (gs i)) :
    Tendsto (fun i => M.infF (gs i) β) l (𝓝 (M.infF g β)) := by
  have hbase : Tendsto (fun i => 1 + εs i) l (𝓝 1) := by simpa using hεt.const_add 1
  have hup : Tendsto (fun i => (1 + εs i) ^ (N : ℝ) * M.infF g β) l (𝓝 (M.infF g β)) := by
    have := (hbase.rpow_const (p := (N : ℝ)) (Or.inl one_ne_zero)).mul_const (M.infF g β)
    rwa [Real.one_rpow, one_mul] at this
  have hlo : Tendsto (fun i => (1 + εs i) ^ (-(N : ℝ)) * M.infF g β) l (𝓝 (M.infF g β)) := by
    have := (hbase.rpow_const (p := -(N : ℝ)) (Or.inl one_ne_zero)).mul_const (M.infF g β)
    rwa [Real.one_rpow, one_mul] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup ?_ ?_
  · filter_upwards [hε, h] with i hi hci
    exact M.le_infF hN hi hci hβ
  · filter_upwards [hε, h] with i hi hci
    exact M.infF_le hN hi hci hβ

/-- Uniform closeness measured by `g`: `|g'(v,v) - g(v,v)| ≤ η g(v,v)` at every point. -/
def UniformlyClose (η : ℝ) (g g' : FrameMetric X N) : Prop :=
  ∀ x (v : Fin N → ℝ), |v ⬝ᵥ (g'.G x *ᵥ v) - v ⬝ᵥ (g.G x *ᵥ v)| ≤ η * (v ⬝ᵥ (g.G x *ᵥ v))

omit [MeasurableSpace X] in
/-- Uniform closeness gives comparability, with `ε = η/(1-η)`. -/
theorem comparable_of_uniformlyClose {η : ℝ} (hη : 0 ≤ η) (hη1 : η < 1)
    (h : UniformlyClose η g g') : Comparable (η / (1 - η)) g g' := by
  intro x v
  have ha : 0 ≤ v ⬝ᵥ (g.G x *ᵥ v) := dotProduct_mulVec_nonneg_of_posDef (g.posDef x) v
  obtain ⟨h1, h2⟩ := abs_le.mp (h x v)
  have h1η : 0 < 1 - η := by linarith
  have e : 1 + η / (1 - η) = (1 - η)⁻¹ := by field_simp; ring
  rw [e, inv_inv]
  constructor
  · nlinarith
  · rw [le_inv_mul_iff₀ h1η]
    nlinarith

/-- lem:stability, "consequently `inf F^(β)_{g'} → inf F^(β)_g` when `g' → g` uniformly". -/
theorem tendsto_infF_of_uniformlyClose (hN : 3 ≤ N) {β : Fin n → ℝ} (hβ : ∀ j, 0 ≤ β j)
    {ι : Type*} {l : Filter ι} (gs : ι → FrameMetric X N) (η : ι → ℝ) (hη : ∀ i, 0 ≤ η i)
    (hηt : Tendsto η l (𝓝 0)) (h : ∀ i, UniformlyClose (η i) g (gs i)) :
    Tendsto (fun i => M.infF (gs i) β) l (𝓝 (M.infF g β)) := by
  have hεt : Tendsto (fun i => η i / (1 - η i)) l (𝓝 0) := by
    have := hηt.div (tendsto_const_nhds.sub hηt) (by norm_num : (1 : ℝ) - 0 ≠ 0)
    rw [sub_zero, div_one] at this
    exact this
  have hsmall : ∀ᶠ i in l, η i < 1 := hηt.eventually (gt_mem_nhds zero_lt_one)
  refine M.tendsto_infF hN hβ gs _ ?_ hεt ?_
  · filter_upwards [hsmall] with i hi
    exact div_nonneg (hη i) (by linarith)
  · filter_upwards [hsmall] with i hi
    exact comparable_of_uniformlyClose (hη i) hi (h i)

end MeasuredModel

/-! ## A witness -/

/-- The toy metric rescaled by `s > 0`. -/
def toyMetricScaled (s : ℝ) (hs : 0 < s) : FrameMetric Bool 3 where
  G := fun _ => s • (1 : Matrix (Fin 3) (Fin 3) ℝ)
  posDef := fun _ => Matrix.PosDef.one.smul hs

/-- The hypotheses of `stability` are satisfiable: the toy metric and its rescaling by `1 + ε`
are comparable. -/
theorem toy_comparable {ε : ℝ} (hε : 0 ≤ ε) :
    MeasuredModel.Comparable ε toyMetric (toyMetricScaled (1 + ε) (by linarith)) := by
  intro x v
  simp only [toyMetric, toyMetricScaled, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
    smul_eq_mul]
  have hv : 0 ≤ v ⬝ᵥ v := by
    simpa using dotProduct_mulVec_nonneg_of_posDef (Matrix.PosDef.one (n := Fin 3) (R := ℝ)) v
  have hc : 0 < 1 + ε := by linarith
  refine ⟨?_, le_rfl⟩
  rw [inv_mul_le_iff₀ hc]
  nlinarith [mul_nonneg hε hv, mul_nonneg (mul_nonneg hε hε) hv]

/-- lem:stability on the toy model: rescaling the metric by `1 + ε` moves `F^(β)` by at most
`(1+ε)^{±3}`. -/
theorem toy_stability {ε : ℝ} (hε : 0 ≤ ε) {β : Fin 1 → ℝ} (hβ : ∀ j, 0 ≤ β j) (u : Bool → ℝ) :
    (1 + ε) ^ (-(3 : ℝ)) * toyModel.F toyMetric β u ≤
        toyModel.F (toyMetricScaled (1 + ε) (by linarith)) β u ∧
      toyModel.F (toyMetricScaled (1 + ε) (by linarith)) β u ≤
        (1 + ε) ^ (3 : ℝ) * toyModel.F toyMetric β u := by
  exact_mod_cast toyModel.stability (le_refl 3) hε (toy_comparable hε) hβ u

/-- The printed ratio of lem:stability is `0/0` at `β = 0`, `u = 1` (allowed by "all
`β_j ≥ 0`", l.699): on the toy model `F^(0)_g(1) = 0`, so the hypothesis `F^(β)_g(u) ≠ 0` of
`stability_ratio` cannot be dropped, while `stability` holds for every `u`. -/
theorem toy_F_zero_one : toyModel.F toyMetric 0 toyModel.one = 0 := by
  rw [toyModel.F_one toyMetric (le_refl 3)]
  simp

end Yamabe
