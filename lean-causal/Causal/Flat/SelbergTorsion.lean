import Causal.Flat.SelbergBase
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Algebra.Ring.GeomSum

/-!
# `Causal.Flat.SelbergTorsion` — congruence kernels have finite index, and two of them meet torsion-free

Steps 3–4 of the proof of Selberg's lemma by congruence subgroups (DEC-115). **No label is
marked**: Selberg's lemma has no paper environment (Barbot cites it, [10.G]).

* `congrKer_index_ne_zero` — `Γ(φ) = ker (GL_n(R) → GL_n(F))` has finite index when `F` is finite.
* `eq_one_of_mem_congrKer_of_pow_eq_one` — `g ∈ Γ(φ)`, `g ^ N = 1`, `(N : F) ≠ 0` (`R` a domain,
  `F` a field) force `g = 1`.
* `orderOf_eq_ringChar_pow_of_mem_congrKer` — a finite-order element of `Γ(φ)` has order a power
  of `ringChar F`.
* `congrStatement` — `CongrStatement` (`Flat/SelbergBase`).

> torsion in the congruence kernel Γ(m) has p-power order (…); G ∩ Γ(m) ∩ Γ(m′) is torsion-free of
> finite index (DEC-115, the author's route)

The torsion step does **not** use Krull's intersection theorem (the route of DEC-115): with
`S := ∑_{k<N} gᵏ`, `(g - 1) S = gᴺ - 1 = 0`, and `φ(S) = N • 1`, so `φ(det S) = Nⁿ ≠ 0`; then
`det S ≠ 0` in the domain `R` and `det S • (g - 1) = (g - 1) S adj S = 0` gives `g = 1`.

## Hypothesis checklist
| paper hypothesis | here |
|---|---|
| `R` a finitely generated subring of `ℝ`, `m` maximal | ⚠ weakened: any domain `R`, any morphisms to finite fields |

## SCOPE (disclosed)
* All four statements are proved, **no `sorry`** (the four `SORRY(selberg-congr-…)` prover tasks of
  the DEC-115 skeleton are discharged). Route note against DEC-115's text ("Krull intersection +
  binomial expansion"): neither is used — the torsion step is the geometric-sum/adjugate argument
  above, and the index step is `Subgroup.index_ker` into the finite `GL_n(F)`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. DEC-115.
-/

namespace Causal.Flat

/-- **Step 3**: a congruence kernel to a finite ring has finite index. -/
theorem congrKer_index_ne_zero (n : ℕ) {R F : Type*} [CommRing R] [CommRing F] [Finite F]
    (φ : R →+* F) : (congrKer n φ).index ≠ 0 := by
  rw [congrKer, Subgroup.index_ker]
  exact Nat.card_pos.ne'

/-- **Step 4, the core**: in the congruence kernel of `φ : R → F` (`R` a domain, `F` a field),
`gᴺ = 1` with `N` invertible in `F` forces `g = 1`. -/
theorem eq_one_of_mem_congrKer_of_pow_eq_one (n : ℕ) {R F : Type*} [CommRing R] [IsDomain R]
    [Field F] (φ : R →+* F) {g : Matrix.GeneralLinearGroup (Fin n) R} (hg : g ∈ congrKer n φ)
    {N : ℕ} (hN : g ^ N = 1) (hNF : (N : F) ≠ 0) : g = 1 := by
  classical
  set A : Matrix (Fin n) (Fin n) R := (g : Matrix (Fin n) (Fin n) R) with hAdef
  set S : Matrix (Fin n) (Fin n) R := ∑ k ∈ Finset.range N, A ^ k with hSdef
  have hAN : A ^ N = 1 := by
    rw [hAdef, ← Units.val_pow_eq_pow_val, hN, Units.val_one]
  have hS : S * (A - 1) = 0 := by
    rw [hSdef, geom_sum_mul, hAN, sub_self]
  have hφA : φ.mapMatrix A = 1 := by
    have h1 : Matrix.GeneralLinearGroup.map (n := Fin n) φ g = 1 := hg
    have h2 := congrArg
      (fun u : Matrix.GeneralLinearGroup (Fin n) F => (u : Matrix (Fin n) (Fin n) F)) h1
    simpa [hAdef] using h2
  have hφS : φ.mapMatrix S = ((N : F) • (1 : Matrix (Fin n) (Fin n) F)) := by
    rw [hSdef, map_sum]
    simp only [map_pow, hφA, one_pow, Finset.sum_const, Finset.card_range]
    rw [Nat.cast_smul_eq_nsmul]
  have hdet : φ S.det = (N : F) ^ n := by
    rw [RingHom.map_det, hφS, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have hdet0 : S.det ≠ 0 := by
    intro h
    rw [h, map_zero] at hdet
    exact pow_ne_zero n hNF hdet.symm
  have hsmul : S.det • (A - 1) = 0 := by
    rw [← one_mul (A - 1), ← smul_mul_assoc, ← Matrix.adjugate_mul, mul_assoc, hS, mul_zero]
  have hA1 : A - 1 = 0 := (smul_eq_zero.mp hsmul).resolve_left hdet0
  exact Units.ext (sub_eq_zero.mp hA1)

/-- **Step 4**: a finite-order element of the congruence kernel to a finite field has order a power
of the characteristic. -/
theorem orderOf_eq_ringChar_pow_of_mem_congrKer (n : ℕ) {R F : Type*} [CommRing R] [IsDomain R]
    [Field F] [Finite F] (φ : R →+* F) {g : Matrix.GeneralLinearGroup (Fin n) R}
    (hg : g ∈ congrKer n φ) (hfin : IsOfFinOrder g) : ∃ c : ℕ, orderOf g = ringChar F ^ c := by
  classical
  have hp : (ringChar F).Prime := CharP.char_is_prime F (ringChar F)
  obtain ⟨a, m, hm, hdecomp⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hfin.orderOf_pos.ne' (ringChar F) hp.ne_one
  have hmem : g ^ ringChar F ^ a ∈ congrKer n φ := Subgroup.pow_mem _ hg _
  have hpow : (g ^ ringChar F ^ a) ^ m = 1 := by
    rw [← pow_mul, ← hdecomp, pow_orderOf_eq_one]
  have hmF : (m : F) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff F (ringChar F)]
    exact hm
  have h1 : g ^ ringChar F ^ a = 1 := eq_one_of_mem_congrKer_of_pow_eq_one n φ hmem hpow hmF
  obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one h1)
  exact ⟨c, hc⟩

/-- **Steps 3–4 together**: `CongrStatement`. -/
theorem congrStatement : CongrStatement := by
  intro n R _ _ F₁ F₂ _ _ _ _ φ₁ φ₂ hpq
  refine ⟨Subgroup.index_inf_ne_zero (congrKer_index_ne_zero n φ₁) (congrKer_index_ne_zero n φ₂),
    fun g hg hfin => ?_⟩
  have hp : (ringChar F₁).Prime := CharP.char_is_prime F₁ (ringChar F₁)
  have hq : (ringChar F₂).Prime := CharP.char_is_prime F₂ (ringChar F₂)
  obtain ⟨c, hc⟩ := orderOf_eq_ringChar_pow_of_mem_congrKer n φ₁ hg.1 hfin
  refine eq_one_of_mem_congrKer_of_pow_eq_one n φ₂ hg.2 (pow_orderOf_eq_one g) ?_
  rw [hc, Nat.cast_pow]
  refine pow_ne_zero c ?_
  rw [Ne, CharP.cast_eq_zero_iff F₂ (ringChar F₂)]
  intro hdvd
  exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp hdvd).symm

end Causal.Flat
