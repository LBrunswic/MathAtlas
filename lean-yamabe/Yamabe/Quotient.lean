import Mathlib

/-!
# The trace-Sobolev quotient `F^(β)` over an abstract measured model of `(Σ, ⊔ B_j)`

Labels (the abstract layer, the formalization of record: DEC-186 accepts OQ-44's readings):

* **`rem:sign`** — `Yamabegap.tex:507` (statement l.507–510; its proof l.731–742, "First variation
  at u = 1"), with the value on constants `eq:F1-torus` (l.466–474);
* the quotient `eq:trace-sobolev` (l.486–491), the Hölder inequalities `eq:hoelder` (l.605–610)
  and the quotient `F^(β)` of l.611, used by `lem:stability` (`Yamabe.Stability`).

> For a nonzero function $u\in W^{1,2}(\Sigma)$ define the \emph{trace-Sobolev quotient}
> $\Fq_{\g}(u):=\frac{\aN\|\nabla u\|^2_{L^2(\Sigma,\g)}+\cN\sum_{j=1}^n\|u\|^2_{L^{\psharp}(B_j,\g)}}{\|u\|^2_{L^{\pstar}(\Sigma,\g)}}$,
> where the boundary norms are those of the trace of $u$ [...] (l.486–491)

> $\|u\|^2_{L^2(\Sigma)}\le\Vol(\Sigma)^{2/N}\|u\|^2_{L^{\pstar}(\Sigma)}$ ,
> $\|u\|^2_{L^2(B_j)}\le\Vol(B_j)^{2/(N-1)}\|u\|^2_{L^{\psharp}(B_j)}$ . (l.606–610)

> $\Fq_\g(1)=\cN\,\frac{\sum_{j}\Vol(B_j,\g)^{(N-2)/(N-1)}}{\Vol(\Sigma,\g)^{(N-2)/N}}
> =\frac{2(N-1)\,\omega_{N-1}\sum_j r_j^{N-2}}{\Vol(\Sigma,\g)^{(N-2)/N}}
> =\frac{2(N-1)\,M}{\Vol(\Sigma,\g)^{(N-2)/N}}$ (l.470–472)

> On the constant function, \eqref{eq:F1-torus} gives $\Fq_\g(1)=2(N-1)M/\Vol(\Sigma,\g)^{(N-2)/N}$.
> The first variation of $\Fq_\g$ at $u=1$ in a direction $\varphi$ with $\int_\Sigma\varphi\,\vol=0$
> and $\varphi\le0$, $\varphi\not\equiv0$ on $\partial\Sigma$ is strictly negative
> (Appendix~\ref{app:proofs}), so that $\inf\Fq_\g<\Fq_\g(1)$: the constant function is never
> optimal, and any bound of the form $\inf\Fq_\g\ge\kappa\Fq_\g(1)$ must have $\kappa<1$. [...]
> (l.509)

> $\frac{\rd}{\rd\epsilon}\Big|_{\epsilon=0}\|u_\epsilon\|^2_{L^q(B)}=2\Vol(B)^{2/q-1}\int_B\varphi$
> [...] $=\frac{2\cN}{\Vol(\Sigma)^{(N-2)/N}}\sum_j\Vol(B_j)^{-1/(N-1)}\int_{B_j}\varphi\,\bvol$
> [...] Such $\varphi$ exist (take $\varphi=-1$ near $\partial\Sigma$ and positive in the interior
> with zero mean), so $\inf\Fq_\g<\Fq_\g(1)$. (l.734–741)

## The model

`MeasuredModel X D N n` reads `(Σ, ⊔_{j<n} B_j)` in a measurable frame `e_1, …, e_N` of `TΣ`:
`μ` is the frame measure `|e¹ ∧ ⋯ ∧ eᴺ|`, `μb j` the frame measure of `B_j` (carried by `X`),
`P x` the boundary frame in the ambient frame, `D` the admissible functions with their values
`val`, trace `tr` and differential `d`; `one` has value and trace `1` and differential `0`.
A `FrameMetric` is the Gram matrix `G x`, positive definite. As on a Riemannian manifold,
`vol_g = √(det G) μ`, `bvol_g = √(det (Pᵀ G P)) μb j`, `|∇u|²_g = du ⬝ G⁻¹ du`.

## What is proved

`F_one`, `Fq_one_round`, `Fq_one_round_three` (eq:F1-torus); `hoelder_interior`,
`hoelder_boundary` (eq:hoelder, corrected), `hoelder_boundary_printed_false`,
`hoelder_boundary_printed_false_of_lt_one`;
`hasDerivAt_normSq_one_add` (l.734); `hasDerivAt_F_one_add` (l.738–740), `firstVariation_neg`,
`exists_F_lt_F_one`, `infF_lt_F_one`, `exists_direction`, `infF_lt_Fq_one`, `kappa_lt_one`;
the assembly `rem_sign`; the witness `toyModel`, `toyMetric`, `toy_infF_lt_Fq_one`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `N ≥ 3` (l.605) | ✓ carried |
| `(Σ, g)` compact Riemannian with boundary `⊔ B_j` | ⚠ read in the abstract model (SCOPE) |
| `u ∈ W^{1,2}(Σ) ∖ {0}` | ✓ `u : D`; `u ≠ 0` read `0 < ‖u‖²_{L^{p*}} < ∞` (`Adm`) |
| `B_j` round of radius `r_j` (eq:F1-torus) | ⚠ weakened: only `Vol(B_j) = ω_{N-1} r_j^{N-1}` |
| `g` of constant scalar curvature (Schwarzschild-like, l.467) | ⚠ weakened: not used |
| `∂Σ` minimal, `H_g ≡ 0` (Schwarzschild-like, l.467) | ⚠ weakened: not used |
| `φ` smooth (l.732) | ⚠ weakened: bounded, a.e.-strongly measurable |
| compactness | ✓ carried as `IsFiniteMeasure (vol_g)`, `IsFiniteMeasure (bvol_g)` where used |
| `Σ`, `∂Σ` nonempty | ✓ carried as `vol_g ≠ 0`, `∃ j, bvol_g j ≠ 0` where used |
| "such φ exist" | ⚠ from a cutoff `χ ∈ D`, `tr χ = 1` on `∂Σ`, `∫ χ < Vol(Σ)` (`exists_direction`) |

## SCOPE (disclosed)

* Abstract layer only (DEC-139): the model (measurable frames, `vol_g = √det G · μ`, the trace, a smooth
  collar cutoff `χ`) is the formalization of record (DEC-186, OQ-44); the passage from `(Σ, g)` to
  it is the scaffold's bridge `Yamabe.Mfd.Reads`.
* **Finding (eq:hoelder, l.609; same constant l.720).** On any `B_j` with `Vol(B_j) < 1` the
  constant `u = 1` violates the printed boundary line (`hoelder_boundary_printed_false_of_lt_one`;
  a point mass in `hoelder_boundary_printed_false`): the exponent is `1/(N-1)`, not `2/(N-1)`
  (`hoelder_boundary`, sharp by `hoelder_boundary_eq_one`). Of the two citations of eq:hoelder at
  l.720 only the second, `‖u_k‖_{L²(B_j)} ≤ Vol(B_j)^{1/(N-1)} ‖u_k‖_{L^{p♯}(B_j)}`, uses the
  boundary line; its factor should be `Vol(B_j)^{1/(2(N-1))}`, and the step survives since only
  `→ 0` is used. The first ("bounded in `W^{1,2}`") and l.627 use the interior line, which is
  correct (`hoelder_interior`).
* `normSq ν q f = (eLpNorm f q ν).toReal ^ 2` is `0` when the norm is infinite; `F` is a real
  quotient (`x / 0 = 0`). `inf F` is over `Adm`.
* `dirichlet` is also `0` when the Dirichlet energy is infinite. The Riemannian instance
  (T-yamabe-scope) must therefore take `D` among finite-energy, finite-norm functions (`C^∞(Σ)`,
  or `W^{1,2}(Σ)` by density), where `F` and `inf F` are the paper's; an abstract `D` containing a
  function of infinite energy or boundary norm would give a Lean `inf F` below the paper's.
* `ω_{N-1}` (`sphereArea`) is the mass of Mathlib's `volume.toSphere` (`= N · |B^N|`);
  `sphereArea_three : ω_2 = 4π`. `M` is its round-sphere value `ω_{N-1} Σ r_j^{N-2}` (l.467).
* "Theorem thm:upper-bound therefore yields δ > 0 but no size" is commentary, not formalized.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal Matrix

noncomputable section

namespace Yamabe

/-! ## Exponents and constants -/

section Constants

/-- `a_N = 4(N-1)/(N-2)` (l.180, l.605). -/
def aN (N : ℕ) : ℝ := 4 * ((N : ℝ) - 1) / ((N : ℝ) - 2)

/-- The critical Sobolev exponent `p* = 2N/(N-2)` (l.180, l.605). -/
def pStar (N : ℕ) : ℝ := 2 * (N : ℝ) / ((N : ℝ) - 2)

/-- The critical trace exponent `p♯ = 2(N-1)/(N-2)` (l.329, l.605). -/
def pSharp (N : ℕ) : ℝ := 2 * ((N : ℝ) - 1) / ((N : ℝ) - 2)

/-- `ω_{N-1}`, the area of the unit round `(N-1)`-sphere (l.340): the total mass of Mathlib's
sphere measure on the unit sphere of `ℝ^N` (`= N · |B^N|`, `toSphere_apply_univ`). -/
def sphereArea (N : ℕ) : ℝ :=
  ((volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere Set.univ).toReal

/-- `c_N = 2(N-1) ω_{N-1}^{1/(N-1)}` (eq:cN, l.338). -/
def cN (N : ℕ) : ℝ := 2 * ((N : ℝ) - 1) * sphereArea N ^ (1 / ((N : ℝ) - 1))

/-- The mass of round punctures, `M = ω_{N-1} Σ_j r_j^{N-2}` (l.467). -/
def roundMass (N : ℕ) {n : ℕ} (r : Fin n → ℝ) : ℝ := sphereArea N * ∑ j, r j ^ (N - 2)

variable {N : ℕ}

lemma three_le_cast (hN : 3 ≤ N) : (3 : ℝ) ≤ N := by exact_mod_cast hN

lemma aN_pos (hN : 3 ≤ N) : 0 < aN N := by
  have := three_le_cast hN
  unfold aN; apply div_pos <;> linarith

lemma pStar_pos (hN : 3 ≤ N) : 0 < pStar N := by
  have := three_le_cast hN
  unfold pStar; apply div_pos <;> linarith

lemma pSharp_pos (hN : 3 ≤ N) : 0 < pSharp N := by
  have := three_le_cast hN
  unfold pSharp; apply div_pos <;> linarith

lemma two_le_pStar (hN : 3 ≤ N) : 2 ≤ pStar N := by
  have := three_le_cast hN
  unfold pStar; rw [le_div_iff₀ (by linarith)]; linarith

lemma two_le_pSharp (hN : 3 ≤ N) : 2 ≤ pSharp N := by
  have := three_le_cast hN
  unfold pSharp; rw [le_div_iff₀ (by linarith)]; linarith

lemma two_div_pStar (hN : 3 ≤ N) : 2 / pStar N = ((N : ℝ) - 2) / N := by
  have := three_le_cast hN
  unfold pStar; field_simp

lemma two_div_pSharp (hN : 3 ≤ N) : 2 / pSharp N = ((N : ℝ) - 2) / ((N : ℝ) - 1) := by
  have := three_le_cast hN
  have h1 : (N:ℝ) - 1 ≠ 0 := by linarith
  have h2 : (N:ℝ) - 2 ≠ 0 := by linarith
  unfold pSharp; field_simp

/-- `N / p* = (N-2)/2` (l.712). -/
lemma natCast_div_pStar (hN : 3 ≤ N) : (N : ℝ) / pStar N = ((N : ℝ) - 2) / 2 := by
  have := three_le_cast hN
  have h2 : (N:ℝ) - 2 ≠ 0 := by linarith
  have h3 : (N:ℝ) ≠ 0 := by linarith
  unfold pStar; field_simp

/-- `(N-1) / p♯ = (N-2)/2` (l.712). -/
lemma sub_one_div_pSharp (hN : 3 ≤ N) : ((N : ℝ) - 1) / pSharp N = ((N : ℝ) - 2) / 2 := by
  have := three_le_cast hN
  have h1 : (N:ℝ) - 1 ≠ 0 := by linarith
  have h2 : (N:ℝ) - 2 ≠ 0 := by linarith
  unfold pSharp; field_simp

lemma sphereArea_eq (N : ℕ) :
    sphereArea N = N * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1)).toReal := by
  unfold sphereArea
  rw [Measure.toSphere_apply_univ, ENNReal.toReal_mul]
  simp

lemma sphereArea_pos (hN : 1 ≤ N) : 0 < sphereArea N := by
  rw [sphereArea_eq]
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  apply mul_pos (by exact_mod_cast hN)
  apply ENNReal.toReal_pos
  · exact (Metric.measure_ball_pos _ _ one_pos).ne'
  · exact measure_ball_lt_top.ne

lemma cN_pos (hN : 2 ≤ N) : 0 < cN N := by
  have h2 : (2:ℝ) ≤ N := by exact_mod_cast hN
  unfold cN
  apply mul_pos (by linarith)
  exact Real.rpow_pos_of_pos (sphereArea_pos (by omega)) _

/-- `ω_2 = 4π`. -/
lemma sphereArea_three : sphereArea 3 = 4 * Real.pi := by
  rw [sphereArea_eq, EuclideanSpace.volume_ball]
  simp only [Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul]
  rw [ENNReal.toReal_ofReal (by positivity)]
  have hG : Real.Gamma ((3:ℕ) / 2 + 1) = 3 / 4 * Real.sqrt Real.pi := by
    have e : ((3:ℕ):ℝ) / 2 + 1 = (1/2 + 1) + 1 := by norm_num
    rw [e, Real.Gamma_add_one (by norm_num), Real.Gamma_add_one (by norm_num),
      Real.Gamma_one_half_eq]
    ring
  rw [hG]
  have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hs : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  field_simp
  push_cast
  nlinarith [hs]

/-- `c_3 = 4 √(4π)` (eq:cN, l.338). -/
lemma cN_three : cN 3 = 4 * Real.sqrt (4 * Real.pi) := by
  unfold cN
  rw [sphereArea_three, Real.sqrt_eq_rpow]
  norm_num

end Constants

/-! ## Squared `L^q` norms and the Hölder inequalities `eq:hoelder` -/

section Norms

variable {X : Type*} [MeasurableSpace X]

/-- `‖f‖²_{L^q(ν)}`, through Mathlib's `eLpNorm` (`0` when the norm is infinite). -/
def normSq (ν : Measure X) (q : ℝ) (f : X → ℝ) : ℝ :=
  (eLpNorm f (ENNReal.ofReal q) ν).toReal ^ 2

lemma normSq_nonneg (ν : Measure X) (q : ℝ) (f : X → ℝ) : 0 ≤ normSq ν q f := by
  unfold normSq; positivity

/-- The squared norm of the constant `1`: `‖1‖²_{L^q(ν)} = ν(X)^{2/q}`. -/
lemma normSq_one (ν : Measure X) {q : ℝ} (hq : 0 < q) :
    normSq ν q (fun _ => 1) = (ν Set.univ).toReal ^ (2 / q) := by
  unfold normSq
  rw [eLpNorm_const' _ (by simpa using hq) ENNReal.ofReal_ne_top]
  simp only [enorm_one, one_mul, ENNReal.toReal_ofReal hq.le]
  rw [← ENNReal.toReal_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ENNReal.toReal_nonneg]
  congr 1; push_cast; ring

/-- Hölder, in `ℝ≥0∞` (no finiteness): `‖f‖²_{L²} ≤ ν(X)^{1-2/q} ‖f‖²_{L^q}` for `q ≥ 2`. -/
theorem eLpNorm_two_sq_le {ν : Measure X} {q : ℝ} (hq : 2 ≤ q) {f : X → ℝ}
    (hf : AEStronglyMeasurable f ν) :
    eLpNorm f 2 ν ^ 2 ≤ ν Set.univ ^ (1 - 2 / q) * eLpNorm f (ENNReal.ofReal q) ν ^ 2 := by
  have h2q : (2 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_ofNat]; exact ENNReal.ofReal_le_ofReal hq
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ h2q hf
  have hq0 : 0 ≤ q := by linarith
  rw [ENNReal.toReal_ofReal hq0] at h
  calc eLpNorm f 2 ν ^ 2 ≤ (eLpNorm f (ENNReal.ofReal q) ν * ν Set.univ ^ (1 / (2:ℝ≥0∞).toReal - 1 / q)) ^ 2 := by
        gcongr
    _ = ν Set.univ ^ (1 - 2 / q) * eLpNorm f (ENNReal.ofReal q) ν ^ 2 := by
        rw [mul_pow, mul_comm, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        congr 2
        simp; ring

/-- Hölder, real form. -/
theorem normSq_two_le {ν : Measure X} [IsFiniteMeasure ν] {q : ℝ} (hq : 2 ≤ q) {f : X → ℝ}
    (hf : MemLp f (ENNReal.ofReal q) ν) :
    normSq ν 2 f ≤ (ν Set.univ).toReal ^ (1 - 2 / q) * normSq ν q f := by
  have h := eLpNorm_two_sq_le hq hf.aestronglyMeasurable
  have hfin : ν Set.univ ^ (1 - 2 / q) * eLpNorm f (ENNReal.ofReal q) ν ^ 2 ≠ ∞ := by
    have h1 : 0 ≤ 1 - 2 / q := by
      rw [sub_nonneg, div_le_one (by linarith)]; exact hq
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg h1 (measure_ne_top _ _))
      (ENNReal.pow_ne_top hf.eLpNorm_ne_top)
  have := ENNReal.toReal_mono hfin h
  unfold normSq
  rw [ENNReal.ofReal_ofNat]
  simpa [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_rpow] using this

variable {N : ℕ}

/-- `eq:hoelder`, first line (l.607), as printed. -/
theorem hoelder_interior (hN : 3 ≤ N) {ν : Measure X} [IsFiniteMeasure ν] {f : X → ℝ}
    (hf : MemLp f (ENNReal.ofReal (pStar N)) ν) :
    normSq ν 2 f ≤ (ν Set.univ).toReal ^ (2 / (N : ℝ)) * normSq ν (pStar N) f := by
  have h := normSq_two_le (two_le_pStar hN) hf
  have hN' := three_le_cast hN
  have e : 1 - 2 / pStar N = 2 / (N : ℝ) := by
    rw [two_div_pStar hN]; field_simp; ring
  rwa [e] at h

/-- `eq:hoelder`, second line (l.609), with the corrected exponent `1/(N-1)`. -/
theorem hoelder_boundary (hN : 3 ≤ N) {ν : Measure X} [IsFiniteMeasure ν] {f : X → ℝ}
    (hf : MemLp f (ENNReal.ofReal (pSharp N)) ν) :
    normSq ν 2 f ≤ (ν Set.univ).toReal ^ (1 / ((N : ℝ) - 1)) * normSq ν (pSharp N) f := by
  have h := normSq_two_le (two_le_pSharp hN) hf
  have hN' := three_le_cast hN
  have e : 1 - 2 / pSharp N = 1 / ((N : ℝ) - 1) := by
    have : (N:ℝ) - 1 ≠ 0 := by linarith
    rw [two_div_pSharp hN]; field_simp; ring
  rwa [e] at h

/-- The exponent `1/(N-1)` is sharp: equality on constants, for every mass. -/
theorem hoelder_boundary_eq_one (hN : 3 ≤ N) (ν : Measure X) :
    normSq ν 2 (fun _ => 1) =
      (ν Set.univ).toReal ^ (1 / ((N : ℝ) - 1)) * normSq ν (pSharp N) (fun _ => 1) := by
  have hN' := three_le_cast hN
  rw [normSq_one ν two_pos, normSq_one ν (pSharp_pos hN), ← Real.rpow_add' ENNReal.toReal_nonneg,
    two_div_pSharp hN]
  · congr 1
    have : (N:ℝ) - 1 ≠ 0 := by linarith
    field_simp; ring
  · rw [two_div_pSharp hN]
    exact (add_pos (div_pos one_pos (by linarith)) (div_pos (by linarith) (by linarith))).ne'

/-- **Finding.** `eq:hoelder`, second line, is false as printed (exponent `2/(N-1)`), for every
`N ≥ 3`: one point of mass `1/2`, `u = 1`. -/
theorem hoelder_boundary_printed_false (hN : 3 ≤ N) :
    ¬ ∀ (ν : Measure Unit) (_ : IsFiniteMeasure ν) (f : Unit → ℝ),
        MemLp f (ENNReal.ofReal (pSharp N)) ν →
        normSq ν 2 f ≤ (ν Set.univ).toReal ^ (2 / ((N : ℝ) - 1)) * normSq ν (pSharp N) f := by
  intro h
  have hN' := three_le_cast hN
  set ν : Measure Unit := (2⁻¹ : ℝ≥0∞) • Measure.dirac () with hν
  have hfin : IsFiniteMeasure ν := ⟨by simp [hν]⟩
  have h1 := h ν hfin (fun _ => 1) (memLp_const 1)
  have hV : (ν Set.univ).toReal = 1 / 2 := by
    rw [hν]; simp
  rw [normSq_one ν two_pos, normSq_one ν (pSharp_pos hN), ← Real.rpow_add' ENNReal.toReal_nonneg,
    two_div_pSharp hN, hV] at h1
  · have e : 2 / ((N : ℝ) - 1) + ((N : ℝ) - 2) / ((N : ℝ) - 1) = (N : ℝ) / ((N : ℝ) - 1) := by
      have : (N:ℝ) - 1 ≠ 0 := by linarith
      field_simp; ring
    rw [e, div_self two_ne_zero, Real.rpow_one] at h1
    have hlt : (1 / 2 : ℝ) ^ ((N : ℝ) / ((N : ℝ) - 1)) < (1 / 2) ^ (1 : ℝ) := by
      apply Real.rpow_lt_rpow_of_exponent_gt (by norm_num) (by norm_num)
      rw [one_lt_div (by linarith)]; linarith
    rw [Real.rpow_one] at hlt
    linarith
  · rw [two_div_pSharp hN]
    exact (add_pos (div_pos two_pos (by linarith)) (div_pos (by linarith) (by linarith))).ne'

/-- **Finding**, for every mass in `(0, 1)`: on any finite measure `ν` with `0 < ν(X) < 1` (any
`B_j` with `Vol(B_j) < 1`, e.g. a round `B_j` of radius `r_j < ω_{N-1}^{-1/(N-1)}`), the constant
`u = 1` violates the printed `eq:hoelder` (l.609). -/
theorem hoelder_boundary_printed_false_of_lt_one (hN : 3 ≤ N) (ν : Measure X)
    (h0 : 0 < (ν Set.univ).toReal) (h1 : (ν Set.univ).toReal < 1) :
    (ν Set.univ).toReal ^ (2 / ((N : ℝ) - 1)) * normSq ν (pSharp N) (fun _ => 1) <
      normSq ν 2 (fun _ => 1) := by
  have hN' := three_le_cast hN
  have hN1 : (N : ℝ) - 1 ≠ 0 := by linarith
  rw [normSq_one ν two_pos, normSq_one ν (pSharp_pos hN), ← Real.rpow_add h0, two_div_pSharp hN,
    div_self two_ne_zero]
  have e : 2 / ((N : ℝ) - 1) + ((N : ℝ) - 2) / ((N : ℝ) - 1) = (N : ℝ) / ((N : ℝ) - 1) := by
    field_simp; ring
  rw [e]
  exact Real.rpow_lt_rpow_of_exponent_gt h0 h1 (by rw [one_lt_div (by linarith)]; linarith)

lemma rpow_le_bound {y q : ℝ} (hy1 : 1 / 2 ≤ y) (hy2 : y ≤ 3 / 2) :
    y ^ (q - 1) ≤ (1 / 2 : ℝ) ^ (q - 1) + (3 / 2 : ℝ) ^ (q - 1) := by
  have h1 : 0 ≤ (1 / 2 : ℝ) ^ (q - 1) := by positivity
  have h2 : 0 ≤ (3 / 2 : ℝ) ^ (q - 1) := by positivity
  rcases le_or_gt 0 (q - 1) with h | h
  · have := Real.rpow_le_rpow (by linarith) hy2 h
    linarith
  · have := Real.rpow_le_rpow_of_nonpos (by norm_num) hy1 h.le
    linarith

lemma normSq_one_add_eq {ν : Measure X} [IsFiniteMeasure ν] {q : ℝ} (hq : 0 < q)
    {f : X → ℝ} (hf : AEStronglyMeasurable f ν) {ε : ℝ} (hpos : ∀ x, 0 < 1 + ε * f x)
    {C : ℝ} (hC : ∀ x, |1 + ε * f x| ≤ C) :
    normSq ν q (fun x => 1 + ε * f x) = (∫ x, (1 + ε * f x) ^ q ∂ν) ^ (2 / q) := by
  have hm : AEStronglyMeasurable (fun x => 1 + ε * f x) ν :=
    aestronglyMeasurable_const.add (hf.const_mul ε)
  have hL : MemLp (fun x => 1 + ε * f x) (ENNReal.ofReal q) ν :=
    MemLp.of_bound hm C (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hC x)
  unfold normSq
  rw [hL.eLpNorm_eq_integral_rpow_norm (by simpa using hq) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hq.le]
  have hI : ∫ x, ‖1 + ε * f x‖ ^ q ∂ν = ∫ x, (1 + ε * f x) ^ q ∂ν := by
    congr 1; funext x; rw [Real.norm_eq_abs, abs_of_pos (hpos x)]
  rw [hI]
  have h0 : 0 ≤ ∫ x, (1 + ε * f x) ^ q ∂ν :=
    integral_nonneg fun x => Real.rpow_nonneg (hpos x).le _
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg h0 _), ← Real.rpow_natCast, ← Real.rpow_mul h0]
  congr 1; push_cast; field_simp

/-- The first variation of a squared norm at `1` (l.734):
`d/dε|₀ ‖1 + εφ‖²_{L^q(ν)} = 2 ν(X)^{2/q-1} ∫ φ dν`, for any finite measure, `q > 0`, `φ` bounded. -/
theorem hasDerivAt_normSq_one_add {ν : Measure X} [IsFiniteMeasure ν] {q : ℝ} (hq : 0 < q)
    {f : X → ℝ} (hf : AEStronglyMeasurable f ν) {K : ℝ} (hK : ∀ x, |f x| ≤ K) :
    HasDerivAt (fun ε : ℝ => normSq ν q (fun x => 1 + ε * f x))
      (2 * (ν Set.univ).toReal ^ (2 / q - 1) * ∫ x, f x ∂ν) 0 := by
  rcases eq_or_ne ν 0 with rfl | hν
  · simp only [normSq, eLpNorm_measure_zero, ENNReal.toReal_zero, integral_zero_measure, mul_zero]
    simpa using hasDerivAt_const (0 : ℝ) (0 : ℝ)
  set K' : ℝ := |K| + 1 with hK'
  have hK'pos : 0 < K' := by positivity
  have hfK : ∀ x, |f x| ≤ K' := fun x => (hK x).trans ((le_abs_self K).trans (by linarith))
  set δ : ℝ := 1 / (2 * K') with hδ
  have hδpos : 0 < δ := by positivity
  -- on the ball of radius δ, 1 + ε f ∈ [1/2, 3/2]
  have hsmall : ∀ ε ∈ Metric.ball (0 : ℝ) δ, ∀ x, |ε * f x| ≤ 1 / 2 := by
    intro ε hε x
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hε
    rw [abs_mul]
    calc |ε| * |f x| ≤ δ * K' := mul_le_mul hε.le (hfK x) (abs_nonneg _) hδpos.le
      _ = 1 / 2 := by rw [hδ]; field_simp
  have hlo : ∀ ε ∈ Metric.ball (0 : ℝ) δ, ∀ x, 1 / 2 ≤ 1 + ε * f x := by
    intro ε hε x; have := (abs_le.mp (hsmall ε hε x)).1; linarith
  have hhi : ∀ ε ∈ Metric.ball (0 : ℝ) δ, ∀ x, 1 + ε * f x ≤ 3 / 2 := by
    intro ε hε x; have := (abs_le.mp (hsmall ε hε x)).2; linarith
  set B : ℝ := (1 / 2 : ℝ) ^ (q - 1) + (3 / 2 : ℝ) ^ (q - 1) with hB
  have hball : Metric.ball (0 : ℝ) δ ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds 0 hδpos
  -- derivative of the integral
  have hI : HasDerivAt (fun ε : ℝ => ∫ x, (1 + ε * f x) ^ q ∂ν)
      (∫ x, f x * q * (1 + 0 * f x) ^ (q - 1) ∂ν) 0 := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (bound := fun _ => K' * q * B)
      (F := fun (ε : ℝ) (x : X) => (1 + ε * f x) ^ q)
      (F' := fun (ε : ℝ) (x : X) => f x * q * (1 + ε * f x) ^ (q - 1))
      hball ?_ ?_ ?_ ?_ (integrable_const (μ := ν) (K' * q * B)) ?_).2
    · exact Eventually.of_forall fun ε =>
        (Real.continuous_rpow_const hq.le).comp_aestronglyMeasurable
          (aestronglyMeasurable_const.add (hf.const_mul ε))
    · simp only [zero_mul, add_zero, Real.one_rpow]; exact integrable_const _
    · simp only [zero_mul, add_zero, Real.one_rpow, mul_one]
      exact hf.mul_const q
    · refine ae_of_all _ fun x ε hε => ?_
      have h1 := hlo ε hε x
      have h2 := hhi ε hε x
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hq,
        abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
      have hb := rpow_le_bound (q := q) h1 h2
      have hB0 : 0 ≤ (1 + ε * f x) ^ (q - 1) := Real.rpow_nonneg (by linarith) _
      calc |f x| * q * (1 + ε * f x) ^ (q - 1) ≤ K' * q * (1 + ε * f x) ^ (q - 1) := by
            gcongr; exact hfK x
        _ ≤ K' * q * B := by gcongr
    · refine ae_of_all _ fun x ε hε => ?_
      have h1 := hlo ε hε x
      have hd : HasDerivAt (fun ε : ℝ => 1 + ε * f x) (f x) ε := by
        simpa using ((hasDerivAt_id ε).mul_const (f x)).const_add 1
      exact hd.rpow_const (Or.inl (by linarith))
  have hI0 : ∫ x, (1 + 0 * f x) ^ q ∂ν = (ν Set.univ).toReal := by
    simp [measureReal_def]
  have hVpos : 0 < (ν Set.univ).toReal :=
    ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hν) (measure_ne_top _ _)
  have hJ := hI.rpow_const (p := 2 / q) (Or.inl (by rw [hI0]; exact hVpos.ne'))
  rw [hI0] at hJ
  have hval : (∫ x, f x * q * (1 + 0 * f x) ^ (q - 1) ∂ν) * (2 / q) *
      (ν Set.univ).toReal ^ (2 / q - 1) = 2 * (ν Set.univ).toReal ^ (2 / q - 1) * ∫ x, f x ∂ν := by
    simp only [zero_mul, add_zero, Real.one_rpow, mul_one]
    rw [integral_mul_const]
    field_simp
  rw [hval] at hJ
  refine hJ.congr_of_eventuallyEq ?_
  filter_upwards [hball] with ε hε
  exact normSq_one_add_eq hq hf (fun x => by linarith [hlo ε hε x])
    (C := 3 / 2) (fun x => by rw [abs_of_pos (by linarith [hlo ε hε x])]; exact hhi ε hε x)

end Norms

/-! ## The quotient over raw data -/

section Raw

variable {X : Type*} [MeasurableSpace X] {n : ℕ}

/-- `F^(β)` over raw data (eq:trace-sobolev, l.489, and l.611): the Dirichlet energy `E`, the
volume measure, the boundary measures, the interior values `v` and the trace `t`. -/
def traceSobolevQuot (N : ℕ) (vol : Measure X) (bvol : Fin n → Measure X) (β : Fin n → ℝ)
    (E : ℝ) (v t : X → ℝ) : ℝ :=
  (aN N * E + ∑ j, β j * normSq (bvol j) (pSharp N) t) / normSq vol (pStar N) v

end Raw

/-! ## The abstract measured model -/

/-- An abstract measured model of a compact `N`-manifold `Σ` with boundary `⊔_{j<n} B_j`, read in
a measurable frame (see the module docstring). -/
structure MeasuredModel (X D : Type*) [MeasurableSpace X] [AddCommGroup D] [Module ℝ D]
    (N n : ℕ) where
  /-- the frame measure `|e¹ ∧ ⋯ ∧ eᴺ|` of `Σ` -/
  μ : Measure X
  /-- the frame measure of `B_j`, a measure on `X` carried by `B_j` -/
  μb : Fin n → Measure X
  /-- the boundary frame `f_1, …, f_{N-1}`, written in the ambient frame -/
  P : X → Matrix (Fin N) (Fin (N - 1)) ℝ
  /-- the boundary frame is a frame -/
  P_injective : ∀ x, Function.Injective (P x).mulVec
  /-- interior values -/
  val : D →ₗ[ℝ] X → ℝ
  /-- the trace on `∂Σ` -/
  tr : D →ₗ[ℝ] X → ℝ
  /-- the differential, in the coframe -/
  d : D →ₗ[ℝ] X → Fin N → ℝ
  /-- the constant function `1` -/
  one : D
  val_one : val one = fun _ => 1
  tr_one : tr one = fun _ => 1
  d_one : d one = 0

/-- A metric on the model: its Gram matrix in the frame, positive definite at every point. -/
structure FrameMetric (X : Type*) (N : ℕ) where
  /-- `G x = (g(e_a, e_b))_{a b}` -/
  G : X → Matrix (Fin N) (Fin N) ℝ
  posDef : ∀ x, (G x).PosDef

namespace MeasuredModel

variable {X D : Type*} [MeasurableSpace X] [AddCommGroup D] [Module ℝ D] {N n : ℕ}
variable (M : MeasuredModel X D N n) (g : FrameMetric X N)

/-- `vol_g = √(det G) μ`. -/
def vol : Measure X :=
  M.μ.withDensity fun x => ENNReal.ofReal (Real.sqrt (g.G x).det)

/-- `bvol_g` on `B_j`: `√(det (Pᵀ G P)) μb j`. -/
def bvol (j : Fin n) : Measure X :=
  (M.μb j).withDensity fun x => ENNReal.ofReal (Real.sqrt ((M.P x)ᵀ * g.G x * M.P x).det)

/-- `|∇u|²_g = du ⬝ G⁻¹ du`. -/
def gradSq (u : D) (x : X) : ℝ :=
  M.d u x ⬝ᵥ ((g.G x)⁻¹ *ᵥ M.d u x)

/-- `‖∇u‖²_{L²(Σ,g)}` (`0` when infinite). -/
def dirichlet (u : D) : ℝ :=
  (∫⁻ x, ENNReal.ofReal (M.gradSq g u x) ∂(M.vol g)).toReal

/-- The quotient `F^(β)_g(u)` (l.611). -/
def F (β : Fin n → ℝ) (u : D) : ℝ :=
  traceSobolevQuot N (M.vol g) (M.bvol g) β (M.dirichlet g u) (M.val u) (M.tr u)

/-- The trace-Sobolev quotient `F_g = F^(c_N)_g` (eq:trace-sobolev, l.489). -/
def Fq (u : D) : ℝ := M.F g (fun _ => cN N) u

/-- `u` is a competitor: `0 < ‖u‖²_{L^{p*}(Σ,g)}` (finite and nonzero). -/
def Adm (u : D) : Prop := 0 < normSq (M.vol g) (pStar N) (M.val u)

/-- `inf_{u ≠ 0} F^(β)_g(u)`. -/
def infF (β : Fin n → ℝ) : ℝ := sInf (M.F g β '' {u | M.Adm g u})

/-! ### Basic facts -/

lemma gradSq_nonneg (u : D) (x : X) : 0 ≤ M.gradSq g u x := by
  have h := ((g.posDef x).inv.posSemidef).dotProduct_mulVec_nonneg (M.d u x)
  simpa [gradSq] using h

lemma gradSq_smul (c : ℝ) (u : D) (x : X) : M.gradSq g (c • u) x = c ^ 2 * M.gradSq g u x := by
  simp only [gradSq, map_smul, Pi.smul_apply, Matrix.mulVec_smul, smul_dotProduct,
    dotProduct_smul, smul_eq_mul]
  ring

lemma dirichlet_nonneg (u : D) : 0 ≤ M.dirichlet g u := ENNReal.toReal_nonneg

lemma dirichlet_one : M.dirichlet g M.one = 0 := by
  simp [dirichlet, gradSq, M.d_one]

lemma dirichlet_one_add_smul (ε : ℝ) (φ : D) :
    M.dirichlet g (M.one + ε • φ) = ε ^ 2 * M.dirichlet g φ := by
  have h : ∀ x, M.gradSq g (M.one + ε • φ) x = ε ^ 2 * M.gradSq g φ x := by
    intro x
    rw [← gradSq_smul]
    simp [gradSq, map_add, M.d_one]
  simp only [dirichlet, h]
  have : ∀ x, ENNReal.ofReal (ε ^ 2 * M.gradSq g φ x) =
      ENNReal.ofReal (ε ^ 2) * ENNReal.ofReal (M.gradSq g φ x) :=
    fun x => ENNReal.ofReal_mul (sq_nonneg ε)
  simp only [this]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sq_nonneg ε)]

lemma F_nonneg (hN : 3 ≤ N) {β : Fin n → ℝ} (hβ : ∀ j, 0 ≤ β j) (u : D) : 0 ≤ M.F g β u := by
  unfold F traceSobolevQuot
  apply div_nonneg _ (normSq_nonneg _ _ _)
  exact add_nonneg (mul_nonneg (aN_pos hN).le (M.dirichlet_nonneg g u))
    (Finset.sum_nonneg fun j _ => mul_nonneg (hβ j) (normSq_nonneg _ _ _))

/-! ### The value on constants (eq:F1-torus) -/

/-- `F^(β)_g(1) = Σ_j β_j Vol(B_j)^{(N-2)/(N-1)} / Vol(Σ)^{(N-2)/N}` (eq:F1-torus, first line,
with `β`). No finiteness is needed. -/
theorem F_one (hN : 3 ≤ N) (β : Fin n → ℝ) :
    M.F g β M.one =
      (∑ j, β j * (M.bvol g j Set.univ).toReal ^ (((N : ℝ) - 2) / ((N : ℝ) - 1))) /
        (M.vol g Set.univ).toReal ^ (((N : ℝ) - 2) / N) := by
  unfold F traceSobolevQuot
  rw [dirichlet_one, M.val_one, M.tr_one, mul_zero, zero_add, normSq_one _ (pStar_pos hN),
    two_div_pStar hN]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [normSq_one _ (pSharp_pos hN), two_div_pSharp hN]

/-- eq:F1-torus, second and third lines: if each `B_j` has the area of a round sphere of radius
`r_j`, then `F_g(1) = 2(N-1) M / Vol(Σ)^{(N-2)/N}`. -/
theorem Fq_one_round (hN : 3 ≤ N) (r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j)
    (hB : ∀ j, (M.bvol g j Set.univ).toReal = sphereArea N * r j ^ (N - 1)) :
    M.Fq g M.one = 2 * ((N : ℝ) - 1) * roundMass N r / (M.vol g Set.univ).toReal ^ (((N : ℝ) - 2) / N) := by
  have hN' := three_le_cast hN
  have hω := sphereArea_pos (N := N) (by omega)
  have h1 : (N : ℝ) - 1 ≠ 0 := by linarith
  unfold Fq
  rw [F_one M g hN]
  congr 1
  unfold roundMass
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hB j, Real.mul_rpow hω.le (pow_nonneg (hr j) _), ← Real.rpow_natCast (r j),
    ← Real.rpow_mul (hr j)]
  have e1 : (((N - 1 : ℕ) : ℝ) * (((N : ℝ) - 2) / ((N : ℝ) - 1))) = ((N - 2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    field_simp
  rw [e1, Real.rpow_natCast]
  unfold cN
  have e2 : sphereArea N ^ (1 / ((N : ℝ) - 1)) * sphereArea N ^ (((N : ℝ) - 2) / ((N : ℝ) - 1)) =
      sphereArea N := by
    rw [← Real.rpow_add hω]
    have : 1 / ((N : ℝ) - 1) + ((N : ℝ) - 2) / ((N : ℝ) - 1) = 1 := by field_simp; ring
    rw [this, Real.rpow_one]
  calc 2 * ((N : ℝ) - 1) * sphereArea N ^ (1 / ((N : ℝ) - 1)) *
        (sphereArea N ^ (((N : ℝ) - 2) / ((N : ℝ) - 1)) * r j ^ (N - 2))
      = 2 * ((N : ℝ) - 1) * (sphereArea N ^ (1 / ((N : ℝ) - 1)) *
        sphereArea N ^ (((N : ℝ) - 2) / ((N : ℝ) - 1))) * r j ^ (N - 2) := by ring
    _ = 2 * ((N : ℝ) - 1) * (sphereArea N * r j ^ (N - 2)) := by rw [e2]; ring

/-- eq:F1-torus for `N = 3` (l.474): `F_g(1) = 4M / Vol(Σ)^{1/3}` with `M = Σ_j 4π r_j`. -/
theorem Fq_one_round_three (M : MeasuredModel X D 3 n) (g : FrameMetric X 3) (r : Fin n → ℝ)
    (hr : ∀ j, 0 ≤ r j)
    (hB : ∀ j, (M.bvol g j Set.univ).toReal = 4 * Real.pi * r j ^ 2) :
    M.Fq g M.one = 4 * (∑ j, 4 * Real.pi * r j) / (M.vol g Set.univ).toReal ^ ((1 : ℝ) / 3) := by
  have h := Fq_one_round M g (le_refl 3) r hr (fun j => by rw [hB j, sphereArea_three])
  rw [h, roundMass, sphereArea_three]
  congr 1
  · rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    norm_num
  · norm_num

lemma val_one_add_smul (ε : ℝ) (φ : D) :
    M.val (M.one + ε • φ) = fun x => 1 + ε * M.val φ x := by
  rw [map_add, map_smul, M.val_one]; funext x; simp

lemma tr_one_add_smul (ε : ℝ) (φ : D) :
    M.tr (M.one + ε • φ) = fun x => 1 + ε * M.tr φ x := by
  rw [map_add, map_smul, M.tr_one]; funext x; simp

/-- `F^(β)_g(1 + εφ)`, unfolded. -/
lemma F_one_add_smul (β : Fin n → ℝ) (φ : D) (ε : ℝ) :
    M.F g β (M.one + ε • φ) =
      (aN N * (ε ^ 2 * M.dirichlet g φ) +
          ∑ j, β j * normSq (M.bvol g j) (pSharp N) (fun x => 1 + ε * M.tr φ x)) /
        normSq (M.vol g) (pStar N) (fun x => 1 + ε * M.val φ x) := by
  simp only [F, traceSobolevQuot, dirichlet_one_add_smul, val_one_add_smul, tr_one_add_smul]

/-! ### The first variation at `u = 1` (proof of rem:sign, l.731–742) -/

/-- The first-variation formula (l.738–740), for `F^(β)` and a bounded direction `φ` with
`∫_Σ φ vol = 0`. -/
theorem hasDerivAt_F_one_add (hN : 3 ≤ N) (β : Fin n → ℝ)
    [IsFiniteMeasure (M.vol g)] [∀ j, IsFiniteMeasure (M.bvol g j)] (hV : M.vol g ≠ 0)
    (φ : D) (hφv : AEStronglyMeasurable (M.val φ) (M.vol g))
    (hφt : ∀ j, AEStronglyMeasurable (M.tr φ) (M.bvol g j)) (K : ℝ)
    (hKv : ∀ x, |M.val φ x| ≤ K) (hKt : ∀ x, |M.tr φ x| ≤ K)
    (hmean : ∫ x, M.val φ x ∂(M.vol g) = 0) :
    HasDerivAt (fun ε : ℝ => M.F g β (M.one + ε • φ))
      (2 / (M.vol g Set.univ).toReal ^ (((N : ℝ) - 2) / N) *
        ∑ j, β j * (M.bvol g j Set.univ).toReal ^ (-(1 / ((N : ℝ) - 1))) *
          ∫ x, M.tr φ x ∂(M.bvol g j)) 0 := by
  have hN' := three_le_cast hN
  have h1 : (N : ℝ) - 1 ≠ 0 := by linarith
  have hfun : (fun ε : ℝ => M.F g β (M.one + ε • φ)) = fun ε : ℝ =>
      (aN N * (ε ^ 2 * M.dirichlet g φ) +
          ∑ j, β j * normSq (M.bvol g j) (pSharp N) (fun x => 1 + ε * M.tr φ x)) /
        normSq (M.vol g) (pStar N) (fun x => 1 + ε * M.val φ x) :=
    funext fun ε => M.F_one_add_smul g β φ ε
  rw [hfun]
  have hE : HasDerivAt (fun ε : ℝ => aN N * (ε ^ 2 * M.dirichlet g φ)) 0 0 := by
    simpa using ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (M.dirichlet g φ)).const_mul (aN N)
  have hS : HasDerivAt (fun ε : ℝ =>
      ∑ j, β j * normSq (M.bvol g j) (pSharp N) (fun x => 1 + ε * M.tr φ x))
      (∑ j, β j * (2 * (M.bvol g j Set.univ).toReal ^ (2 / pSharp N - 1) *
        ∫ x, M.tr φ x ∂(M.bvol g j))) 0 :=
    HasDerivAt.fun_sum fun j _ =>
      (hasDerivAt_normSq_one_add (pSharp_pos hN) (hφt j) hKt).const_mul (β j)
  have hD := hasDerivAt_normSq_one_add (pStar_pos hN) hφv hKv
  rw [hmean, mul_zero] at hD
  have hD0 : normSq (M.vol g) (pStar N) (fun x => 1 + 0 * M.val φ x) =
      (M.vol g Set.univ).toReal ^ (((N : ℝ) - 2) / N) := by
    simp only [zero_mul, add_zero]
    rw [normSq_one _ (pStar_pos hN), two_div_pStar hN]
  have hVpos : 0 < (M.vol g Set.univ).toReal :=
    ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hV) (measure_ne_top _ _)
  have hD0pos : 0 < (M.vol g Set.univ).toReal ^ (((N : ℝ) - 2) / N) :=
    Real.rpow_pos_of_pos hVpos _
  have hQ := (hE.add hS).div hD (by rw [hD0]; exact hD0pos.ne')
  refine hQ.congr_deriv ?_
  rw [hD0, two_div_pSharp hN]
  have e : ((N : ℝ) - 2) / ((N : ℝ) - 1) - 1 = -(1 / ((N : ℝ) - 1)) := by field_simp; ring
  rw [e, Finset.mul_sum, mul_zero, sub_zero, zero_add]
  field_simp
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  field_simp

/-- The first variation is strictly negative when `β_j > 0`, `φ ≤ 0` on `∂Σ` and `φ ≢ 0` on
`∂Σ` (l.741). -/
theorem firstVariation_neg {β : Fin n → ℝ} (hβ : ∀ j, 0 < β j)
    [IsFiniteMeasure (M.vol g)] [∀ j, IsFiniteMeasure (M.bvol g j)] (hV : M.vol g ≠ 0)
    (φ : D) (hφt : ∀ j, AEStronglyMeasurable (M.tr φ) (M.bvol g j)) (K : ℝ)
    (hKt : ∀ x, |M.tr φ x| ≤ K)
    (hle : ∀ j, ∀ᵐ x ∂(M.bvol g j), M.tr φ x ≤ 0)
    (hne : ∃ j, ¬ (M.tr φ =ᵐ[M.bvol g j] 0)) :
    2 / (M.vol g Set.univ).toReal ^ (((N : ℝ) - 2) / N) *
        ∑ j, β j * (M.bvol g j Set.univ).toReal ^ (-(1 / ((N : ℝ) - 1))) *
          ∫ x, M.tr φ x ∂(M.bvol g j) < 0 := by
  have hVpos : 0 < (M.vol g Set.univ).toReal :=
    ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hV) (measure_ne_top _ _)
  refine mul_neg_of_pos_of_neg (div_pos two_pos (Real.rpow_pos_of_pos hVpos _)) ?_
  have hint : ∀ j, Integrable (M.tr φ) (M.bvol g j) := fun j =>
    (integrable_const K).mono' (hφt j) (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hKt x)
  have hterm : ∀ j, β j * (M.bvol g j Set.univ).toReal ^ (-(1 / ((N : ℝ) - 1))) *
      ∫ x, M.tr φ x ∂(M.bvol g j) ≤ 0 := fun j =>
    mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (hβ j).le (Real.rpow_nonneg ENNReal.toReal_nonneg _))
      (integral_nonpos_of_ae (hle j))
  obtain ⟨j₀, hj₀⟩ := hne
  have hB0 : M.bvol g j₀ ≠ 0 := by
    rintro h0; apply hj₀; rw [h0]; exact ae_zero.le (by simp)
  have hVj : 0 < (M.bvol g j₀ Set.univ).toReal :=
    ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hB0) (measure_ne_top _ _)
  have hneg : ∫ x, M.tr φ x ∂(M.bvol g j₀) < 0 := by
    have hpos : 0 < ∫ x, (-M.tr φ) x ∂(M.bvol g j₀) := by
      rw [integral_pos_iff_support_of_nonneg_ae
        ((hle j₀).mono fun x hx => by simpa using hx) (hint j₀).neg]
      have hsupp : Function.support (-M.tr φ) = {x | ¬ M.tr φ x = (0 : X → ℝ) x} := by
        ext x; simp [Function.mem_support]
      rw [hsupp]
      rw [Filter.EventuallyEq, ae_iff] at hj₀
      exact pos_iff_ne_zero.mpr hj₀
    simp only [Pi.neg_apply, integral_neg] at hpos
    linarith
  have hlt : β j₀ * (M.bvol g j₀ Set.univ).toReal ^ (-(1 / ((N : ℝ) - 1))) *
      ∫ x, M.tr φ x ∂(M.bvol g j₀) < 0 :=
    mul_neg_of_pos_of_neg (mul_pos (hβ j₀) (Real.rpow_pos_of_pos hVj _)) hneg
  calc ∑ j, β j * (M.bvol g j Set.univ).toReal ^ (-(1 / ((N : ℝ) - 1))) *
        ∫ x, M.tr φ x ∂(M.bvol g j) < ∑ _j : Fin n, (0 : ℝ) :=
        Finset.sum_lt_sum (fun j _ => hterm j) ⟨j₀, Finset.mem_univ _, hlt⟩
    _ = 0 := by simp

/-- rem:sign: in a direction as in l.509 the quotient drops below its value at `1` along
`1 + εφ`, at a competitor. -/
theorem exists_F_lt_F_one (hN : 3 ≤ N) {β : Fin n → ℝ} (hβ : ∀ j, 0 < β j)
    [IsFiniteMeasure (M.vol g)] [∀ j, IsFiniteMeasure (M.bvol g j)] (hV : M.vol g ≠ 0)
    (φ : D) (hφv : AEStronglyMeasurable (M.val φ) (M.vol g))
    (hφt : ∀ j, AEStronglyMeasurable (M.tr φ) (M.bvol g j)) (K : ℝ)
    (hKv : ∀ x, |M.val φ x| ≤ K) (hKt : ∀ x, |M.tr φ x| ≤ K)
    (hmean : ∫ x, M.val φ x ∂(M.vol g) = 0)
    (hle : ∀ j, ∀ᵐ x ∂(M.bvol g j), M.tr φ x ≤ 0)
    (hne : ∃ j, ¬ (M.tr φ =ᵐ[M.bvol g j] 0)) :
    ∃ ε : ℝ, M.Adm g (M.one + ε • φ) ∧ M.F g β (M.one + ε • φ) < M.F g β M.one := by
  have hd := M.hasDerivAt_F_one_add g hN β hV φ hφv hφt K hKv hKt hmean
  have hneg := M.firstVariation_neg g hβ hV φ hφt K hKt hle hne
  -- the quotient drops below its value at `0` arbitrarily close to `0`
  have hfreq : ∃ᶠ ε in 𝓝 (0 : ℝ), M.F g β (M.one + ε • φ) < M.F g β (M.one + (0 : ℝ) • φ) := by
    by_contra hcon
    rw [Filter.not_frequently] at hcon
    have hmin : IsLocalMin (fun ε : ℝ => M.F g β (M.one + ε • φ)) 0 :=
      hcon.mono fun ε hε => not_lt.mp hε
    exact hneg.ne (hmin.hasDerivAt_eq_zero hd)
  -- and `1 + εφ` is a competitor near `0`
  have hD := hasDerivAt_normSq_one_add (pStar_pos hN) hφv hKv
  have hVpos : 0 < (M.vol g Set.univ).toReal :=
    ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hV) (measure_ne_top _ _)
  have hD0 : 0 < normSq (M.vol g) (pStar N) (fun x => 1 + (0 : ℝ) * M.val φ x) := by
    simp only [zero_mul, add_zero]
    rw [normSq_one _ (pStar_pos hN)]
    exact Real.rpow_pos_of_pos hVpos _
  have hadm : ∀ᶠ ε in 𝓝 (0 : ℝ), M.Adm g (M.one + ε • φ) := by
    have := hD.continuousAt.eventually_const_lt hD0
    refine this.mono fun ε hε => ?_
    simpa [Adm, val_one_add_smul] using hε
  obtain ⟨ε, hlt, hε⟩ := (hfreq.and_eventually hadm).exists
  refine ⟨ε, hε, ?_⟩
  simpa using hlt

/-- rem:sign: `inf F^(β)_g < F^(β)_g(1)`. -/
theorem infF_lt_F_one (hN : 3 ≤ N) {β : Fin n → ℝ} (hβ : ∀ j, 0 < β j)
    [IsFiniteMeasure (M.vol g)] [∀ j, IsFiniteMeasure (M.bvol g j)] (hV : M.vol g ≠ 0)
    (φ : D) (hφv : AEStronglyMeasurable (M.val φ) (M.vol g))
    (hφt : ∀ j, AEStronglyMeasurable (M.tr φ) (M.bvol g j)) (K : ℝ)
    (hKv : ∀ x, |M.val φ x| ≤ K) (hKt : ∀ x, |M.tr φ x| ≤ K)
    (hmean : ∫ x, M.val φ x ∂(M.vol g) = 0)
    (hle : ∀ j, ∀ᵐ x ∂(M.bvol g j), M.tr φ x ≤ 0)
    (hne : ∃ j, ¬ (M.tr φ =ᵐ[M.bvol g j] 0)) :
    M.infF g β < M.F g β M.one := by
  obtain ⟨ε, hadm, hlt⟩ := M.exists_F_lt_F_one g hN hβ hV φ hφv hφt K hKv hKt hmean hle hne
  refine lt_of_le_of_lt ?_ hlt
  refine csInf_le ⟨0, ?_⟩ ⟨M.one + ε • φ, hadm, rfl⟩
  rintro _ ⟨u, _, rfl⟩
  exact M.F_nonneg g hN (fun j => (hβ j).le) u

/-- "Such φ exist" (l.741): from a cutoff `χ ∈ D` equal to `1` on `∂Σ` with `∫ χ < Vol(Σ)`,
`φ := (∫χ / Vol(Σ)) · 1 - χ` has zero mean and is `< 0` on `∂Σ`. -/
theorem exists_direction
    [IsFiniteMeasure (M.vol g)] [∀ j, IsFiniteMeasure (M.bvol g j)] (hV : M.vol g ≠ 0)
    (χ : D) (hχv : AEStronglyMeasurable (M.val χ) (M.vol g))
    (hχt : ∀ j, AEStronglyMeasurable (M.tr χ) (M.bvol g j)) (K : ℝ)
    (hKv : ∀ x, |M.val χ x| ≤ K) (hKt : ∀ x, |M.tr χ x| ≤ K)
    (hχ1 : ∀ j, ∀ᵐ x ∂(M.bvol g j), M.tr χ x = 1)
    (hχint : ∫ x, M.val χ x ∂(M.vol g) < (M.vol g Set.univ).toReal)
    (hB : ∃ j, M.bvol g j ≠ 0) :
    ∃ φ : D, AEStronglyMeasurable (M.val φ) (M.vol g) ∧
      (∀ j, AEStronglyMeasurable (M.tr φ) (M.bvol g j)) ∧
      (∃ K' : ℝ, (∀ x, |M.val φ x| ≤ K') ∧ ∀ x, |M.tr φ x| ≤ K') ∧
      ∫ x, M.val φ x ∂(M.vol g) = 0 ∧
      (∀ j, ∀ᵐ x ∂(M.bvol g j), M.tr φ x ≤ 0) ∧
      ∃ j, ¬ (M.tr φ =ᵐ[M.bvol g j] 0) := by
  have hVpos : 0 < (M.vol g Set.univ).toReal :=
    ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hV) (measure_ne_top _ _)
  set t : ℝ := (∫ x, M.val χ x ∂(M.vol g)) / (M.vol g Set.univ).toReal with ht
  have ht1 : t < 1 := by rw [ht, div_lt_one hVpos]; exact hχint
  refine ⟨t • M.one - χ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [map_sub, map_smul, M.val_one, M.tr_one]
  · exact aestronglyMeasurable_const.sub hχv
  · exact fun j => aestronglyMeasurable_const.sub (hχt j)
  · refine ⟨|t| + K, fun x => ?_, fun x => ?_⟩
    · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_one]
      exact (abs_sub _ _).trans (by linarith [hKv x])
    · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_one]
      exact (abs_sub _ _).trans (by linarith [hKt x])
  · have hint : Integrable (M.val χ) (M.vol g) :=
      (integrable_const K).mono' hχv (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hKv x)
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_one]
    rw [integral_sub (integrable_const t) hint, integral_const, smul_eq_mul, measureReal_def, ht]
    field_simp
    ring
  · intro j
    filter_upwards [hχ1 j] with x hx
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_one, hx]
    linarith
  · obtain ⟨j, hj⟩ := hB
    refine ⟨j, fun hae => hj ?_⟩
    have hfalse : ∀ᵐ x ∂(M.bvol g j), False := by
      filter_upwards [hae, hχ1 j] with x hx h1
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_one, h1, Pi.zero_apply] at hx
      linarith
    simpa using hfalse

/-- rem:sign for `F_g` (`β = c_N`): `inf F_g < F_g(1)`, given a boundary cutoff `χ`. -/
theorem infF_lt_Fq_one (hN : 3 ≤ N)
    [IsFiniteMeasure (M.vol g)] [∀ j, IsFiniteMeasure (M.bvol g j)] (hV : M.vol g ≠ 0)
    (χ : D) (hχv : AEStronglyMeasurable (M.val χ) (M.vol g))
    (hχt : ∀ j, AEStronglyMeasurable (M.tr χ) (M.bvol g j)) (K : ℝ)
    (hKv : ∀ x, |M.val χ x| ≤ K) (hKt : ∀ x, |M.tr χ x| ≤ K)
    (hχ1 : ∀ j, ∀ᵐ x ∂(M.bvol g j), M.tr χ x = 1)
    (hχint : ∫ x, M.val χ x ∂(M.vol g) < (M.vol g Set.univ).toReal)
    (hB : ∃ j, M.bvol g j ≠ 0) :
    M.infF g (fun _ => cN N) < M.Fq g M.one := by
  obtain ⟨φ, hφv, hφt, ⟨K', hKv', hKt'⟩, hmean, hle, hne⟩ :=
    M.exists_direction g hV χ hχv hχt K hKv hKt hχ1 hχint hB
  exact M.infF_lt_F_one g hN (fun _ => cN_pos (by omega)) hV φ hφv hφt K' hKv' hKt' hmean hle hne

/-- `F_g(1) > 0` once some boundary component has positive area. -/
theorem Fq_one_pos (hN : 3 ≤ N)
    [IsFiniteMeasure (M.vol g)] [∀ j, IsFiniteMeasure (M.bvol g j)] (hV : M.vol g ≠ 0)
    (hB : ∃ j, M.bvol g j ≠ 0) : 0 < M.Fq g M.one := by
  have hVpos : 0 < (M.vol g Set.univ).toReal :=
    ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hV) (measure_ne_top _ _)
  unfold Fq
  rw [F_one M g hN]
  refine div_pos ?_ (Real.rpow_pos_of_pos hVpos _)
  obtain ⟨j₀, hj₀⟩ := hB
  have hVj : 0 < (M.bvol g j₀ Set.univ).toReal :=
    ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hj₀) (measure_ne_top _ _)
  exact Finset.sum_pos' (fun j _ => mul_nonneg (cN_pos (by omega)).le
      (Real.rpow_nonneg ENNReal.toReal_nonneg _))
    ⟨j₀, Finset.mem_univ _, mul_pos (cN_pos (by omega)) (Real.rpow_pos_of_pos hVj _)⟩

/-- rem:sign: "any bound of the form `inf F_g ≥ κ F_g(1)` must have `κ < 1`". -/
theorem kappa_lt_one (hN : 3 ≤ N)
    [IsFiniteMeasure (M.vol g)] [∀ j, IsFiniteMeasure (M.bvol g j)] (hV : M.vol g ≠ 0)
    (χ : D) (hχv : AEStronglyMeasurable (M.val χ) (M.vol g))
    (hχt : ∀ j, AEStronglyMeasurable (M.tr χ) (M.bvol g j)) (K : ℝ)
    (hKv : ∀ x, |M.val χ x| ≤ K) (hKt : ∀ x, |M.tr χ x| ≤ K)
    (hχ1 : ∀ j, ∀ᵐ x ∂(M.bvol g j), M.tr χ x = 1)
    (hχint : ∫ x, M.val χ x ∂(M.vol g) < (M.vol g Set.univ).toReal)
    (hB : ∃ j, M.bvol g j ≠ 0) {κ : ℝ} (hκ : κ * M.Fq g M.one ≤ M.infF g (fun _ => cN N)) :
    κ < 1 := by
  have hlt := M.infF_lt_Fq_one g hN hV χ hχv hχt K hKv hKt hχ1 hχint hB
  have hpos := M.Fq_one_pos g hN hV hB
  have : κ * M.Fq g M.one < 1 * M.Fq g M.one := by linarith
  exact lt_of_mul_lt_mul_right this hpos.le


/-- Assembly of rem:sign over the model (l.509, with its proof l.731–742): if the boundary
components have the areas of round spheres of radii `r_j` and `∂Σ` carries a cutoff `χ`, then
(i) `F_g(1) = 2(N-1) M / Vol(Σ)^{(N-2)/N}` (eq:F1-torus);
(ii) along every bounded direction `φ` with `∫_Σ φ = 0`, `φ ≤ 0` and `φ ≢ 0` on `∂Σ`, the
first variation of `F_g` at `1` exists, equals the formula of l.739 and is strictly negative;
(iii) `inf F_g < F_g(1)`; (iv) every `κ` with `inf F_g ≥ κ F_g(1)` has `κ < 1`. -/
theorem rem_sign (hN : 3 ≤ N)
    [IsFiniteMeasure (M.vol g)] [∀ j, IsFiniteMeasure (M.bvol g j)] (hV : M.vol g ≠ 0)
    (r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j)
    (hround : ∀ j, (M.bvol g j Set.univ).toReal = sphereArea N * r j ^ (N - 1))
    (χ : D) (hχv : AEStronglyMeasurable (M.val χ) (M.vol g))
    (hχt : ∀ j, AEStronglyMeasurable (M.tr χ) (M.bvol g j)) (K : ℝ)
    (hKv : ∀ x, |M.val χ x| ≤ K) (hKt : ∀ x, |M.tr χ x| ≤ K)
    (hχ1 : ∀ j, ∀ᵐ x ∂(M.bvol g j), M.tr χ x = 1)
    (hχint : ∫ x, M.val χ x ∂(M.vol g) < (M.vol g Set.univ).toReal)
    (hB : ∃ j, M.bvol g j ≠ 0) :
    M.Fq g M.one =
        2 * ((N : ℝ) - 1) * roundMass N r / (M.vol g Set.univ).toReal ^ (((N : ℝ) - 2) / N) ∧
      (∀ φ : D, AEStronglyMeasurable (M.val φ) (M.vol g) →
        (∀ j, AEStronglyMeasurable (M.tr φ) (M.bvol g j)) →
        ∀ K' : ℝ, (∀ x, |M.val φ x| ≤ K') → (∀ x, |M.tr φ x| ≤ K') →
        ∫ x, M.val φ x ∂(M.vol g) = 0 →
        (∀ j, ∀ᵐ x ∂(M.bvol g j), M.tr φ x ≤ 0) →
        (∃ j, ¬ (M.tr φ =ᵐ[M.bvol g j] 0)) →
        HasDerivAt (fun ε : ℝ => M.Fq g (M.one + ε • φ))
            (2 * cN N / (M.vol g Set.univ).toReal ^ (((N : ℝ) - 2) / N) *
              ∑ j, (M.bvol g j Set.univ).toReal ^ (-(1 / ((N : ℝ) - 1))) *
                ∫ x, M.tr φ x ∂(M.bvol g j)) 0 ∧
          2 * cN N / (M.vol g Set.univ).toReal ^ (((N : ℝ) - 2) / N) *
              ∑ j, (M.bvol g j Set.univ).toReal ^ (-(1 / ((N : ℝ) - 1))) *
                ∫ x, M.tr φ x ∂(M.bvol g j) < 0) ∧
      M.infF g (fun _ => cN N) < M.Fq g M.one ∧
      ∀ κ : ℝ, κ * M.Fq g M.one ≤ M.infF g (fun _ => cN N) → κ < 1 := by
  have hc : 0 < cN N := cN_pos (by omega)
  have hform : ∀ φ : D, 2 / (M.vol g Set.univ).toReal ^ (((N : ℝ) - 2) / N) *
      ∑ j, (fun _ => cN N) j * (M.bvol g j Set.univ).toReal ^ (-(1 / ((N : ℝ) - 1))) *
        ∫ x, M.tr φ x ∂(M.bvol g j) =
      2 * cN N / (M.vol g Set.univ).toReal ^ (((N : ℝ) - 2) / N) *
        ∑ j, (M.bvol g j Set.univ).toReal ^ (-(1 / ((N : ℝ) - 1))) *
          ∫ x, M.tr φ x ∂(M.bvol g j) := by
    intro φ
    simp only [mul_assoc, ← Finset.mul_sum]
    ring
  refine ⟨M.Fq_one_round g hN r hr hround, ?_, M.infF_lt_Fq_one g hN hV χ hχv hχt K hKv hKt hχ1
    hχint hB, fun κ hκ => M.kappa_lt_one g hN hV χ hχv hχt K hKv hKt hχ1 hχint hB hκ⟩
  intro φ hφv hφt K' hKv' hKt' hmean hle hne
  refine ⟨?_, ?_⟩
  · rw [← hform]
    exact M.hasDerivAt_F_one_add g hN (fun _ => cN N) hV φ hφv hφt K' hKv' hKt' hmean
  · rw [← hform]
    exact M.firstVariation_neg g (fun _ => hc) hV φ hφt K' hKt' hle hne


end MeasuredModel

/-! ## A witness: the model is not vacuous -/

section Toy

/-- The boundary frame of the toy model: the first two vectors of the ambient frame. -/
def toyP : Matrix (Fin 3) (Fin (3 - 1)) ℝ := Matrix.of fun a b => if (a : ℕ) = b then 1 else 0

lemma toyP_transpose_mul : toyPᵀ * toyP = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toyP, Matrix.mul_apply, Fin.sum_univ_succ]

lemma toyP_injective : Function.Injective toyP.mulVec := by
  intro v w h
  have h' := congrArg (fun z => toyPᵀ *ᵥ z) h
  simp only [Matrix.mulVec_mulVec, toyP_transpose_mul, Matrix.one_mulVec] at h'
  exact h'

/-- The discrete differential of the toy model: `du = (u(true) - u(false), 0, 0)`. -/
def toyD : (Bool → ℝ) →ₗ[ℝ] Bool → Fin 3 → ℝ where
  toFun u := fun _ a => if a = 0 then u true - u false else 0
  map_add' u v := by
    funext x a
    by_cases h : a = 0
    · simp only [h, if_true, Pi.add_apply]; ring
    · simp [h]
  map_smul' c u := by
    funext x a
    by_cases h : a = 0
    · simp only [h, if_true, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring
    · simp [h]

/-- A two-point model of `(Σ, B_0)`, `N = 3`: `false` is the boundary, `true` the interior, the
frame measure is the counting measure, the differential is the edge difference. -/
def toyModel : MeasuredModel Bool (Bool → ℝ) 3 1 where
  μ := Measure.count
  μb := fun _ => Measure.dirac false
  P := fun _ => toyP
  P_injective := fun _ => toyP_injective
  val := LinearMap.id
  tr := LinearMap.id
  d := toyD
  one := fun _ => 1
  val_one := rfl
  tr_one := rfl
  d_one := by
    funext x a
    simp [toyD]

/-- The flat metric of the toy model, `G = 1`. -/
def toyMetric : FrameMetric Bool 3 where
  G := fun _ => 1
  posDef := fun _ => Matrix.PosDef.one

/-- Every hypothesis of `infF_lt_Fq_one` holds on the toy model, with `χ` the indicator of the
boundary point: the hypotheses are jointly satisfiable. -/
lemma toy_vol : toyModel.vol toyMetric = Measure.count := by
  simp [MeasuredModel.vol, toyModel, toyMetric]

lemma toy_bvol (j : Fin 1) : toyModel.bvol toyMetric j = Measure.dirac false := by
  simp only [MeasuredModel.bvol, toyModel, toyMetric, Matrix.mul_one]
  rw [toyP_transpose_mul]
  simp

theorem toy_infF_lt_Fq_one :
    toyModel.infF toyMetric (fun _ => cN 3) < toyModel.Fq toyMetric toyModel.one := by
  haveI : IsFiniteMeasure (toyModel.vol toyMetric) := by rw [toy_vol]; infer_instance
  haveI : ∀ j, IsFiniteMeasure (toyModel.bvol toyMetric j) := fun j => by
    rw [toy_bvol]; infer_instance
  have hcount : Measure.count {true} ≠ 0 := by simp
  refine toyModel.infF_lt_Fq_one toyMetric (le_refl 3) ?_ (fun b => if b then 0 else 1)
    ?_ ?_ 1 ?_ ?_ ?_ ?_ ⟨0, ?_⟩
  · rw [toy_vol]; intro h; apply hcount; rw [h]; rfl
  · exact (Measurable.of_discrete).aestronglyMeasurable
  · exact fun j => (Measurable.of_discrete).aestronglyMeasurable
  · intro b; cases b <;> simp [toyModel]
  · intro b; cases b <;> simp [toyModel]
  · intro j; rw [toy_bvol]; simp [toyModel]
  · rw [toy_vol, integral_fintype]
    simp [toyModel, Measure.count_apply_finite]
    norm_num
  · rw [toy_bvol]; exact Measure.dirac_ne_zero

end Toy

end Yamabe
