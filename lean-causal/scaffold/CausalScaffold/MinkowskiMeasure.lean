import Causal.Minkowski
import Causal.Measure
import Causal.Flat.GerochFlat
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Admissible measures on Minkowski space

`prop:mesure_dieckmann_Lorentz` — `ETT.tex:1054`, for Minkowski space only (the library has no
Lorentzian manifolds). Sorry-free since 2026-11-20: the measure-theoretic fact it was reduced to
is `Causal.Flat.minkowski_frontier_null_measure` (the Barbot campaign's offer, DEC-65). Kept in the
scaffold until the ETT campaign graduates it; the instance-only scope below is why the row stays
partial.

> Let $M$ be a strongly causal Lorentzian manifold. Then $M$ admits a measure which is admissible
> both in the past and in the future.

> Since $M$ is strongly causal and Lorentzian, the Alexandrov topology is the manifold topology of
> $M$ and diamonds always have non-empty interior. One then checks easily that conditions $3.$ and
> $4.$ hold for a measure admissible in the sense of Dieckmann.

## What is proved

* **The reduction** (`minkowski_mesure_dieckmann_of`): a finite regular measure, positive on
  non-empty open sets, which does not charge the frontier of any open past set `I^-(A)` or future
  set `I^+(A)`, is admissible in the past and in the future. Property 3. holds because
  `J^-(q) \ J^-(p)` contains a non-empty open set (`exists_isOpen_subset_Jminus_diff`), property
  4. because `K^±(A) = I^±(A)` and `J^±(A) \ I^±(A) ⊂ ∂I^±(A)`
  (`Jminus_diff_Kminus_subset_frontier`): "checks easily" made explicit.
* `prop:mesure_dieckmann_Lorentz` for `ℝ^{1,n}` (`minkowski_mesure_dieckmann`), from the measure
  of `minkowski_exists_measure`, which is `Causal.Flat.minkowski_frontier_null_measure`.

## SCOPE (disclosed)

* **The former `sorry`** (`minkowski_exists_measure`, closed 2026-11-20 by
  `Causal.Flat.minkowski_frontier_null_measure`): a measure as above exists, e.g. a Gaussian on
  `ℝ^{1+n}`. Finiteness, regularity and positivity are standard; what is missing is the
  nullity of `∂I^±(A)` for an **arbitrary** `A`: `I^-(A) = {(t, x) : t < f(x)}` with
  `f(x) = sup_{a ∈ A} (a.1 − ‖x − a.2‖)` 1-Lipschitz (or `±∞`), so `∂I^-(A)` lies in the graph
  of `f`, which is Lebesgue-null by Fubini; `Causal/Flat/GerochFlat.lean` proves it. The
  statement is true for every `n`, `n = 0` included, so the `sorry` is not vacuous.
* **What the paper's "checks easily" rests on.** Condition 4 for an arbitrary `A` is the
  classical theorem that an achronal boundary is a Lipschitz hypersurface (Hawking–Ellis,
  Prop. 6.3.1), hence null for a measure absolutely continuous with respect to Lebesgue; the
  paper's sentence stands once that fact is cited. Condition 3 is elementary here.
* **Instance only**: the row is `prop:mesure_dieckmann_Lorentz` *stated on Minkowski space*;
  the paper's hypothesis "strongly causal Lorentzian manifold" is strengthened to `ℝ^{1,n}`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set MeasureTheory

variable {n : ℕ}

/-- **The reduction of `prop:mesure_dieckmann_Lorentz` for Minkowski space** to a measure which
is finite, regular, positive on non-empty open sets and null on the frontiers of open past and
future sets. -/
theorem minkowski_mesure_dieckmann_of {μ : Measure (Minkowski n)} (hreg : μ.Regular)
    (hfin : μ univ < ⊤) (hpos : ∀ O : Set (Minkowski n), IsOpen O → O.Nonempty → 0 < μ O)
    (hnull : ∀ A : Set (Minkowski n), μ (frontier ((minkowski n).Iminus ⊤ A)) = 0 ∧
      μ (frontier ((minkowski n).Iplus ⊤ A)) = 0) :
    (minkowski n).AdmissiblePast μ ∧ (minkowski n).AdmissibleFuture μ := by
  refine ⟨⟨hreg, hfin, fun p q hpq hne => ?_, fun A => ?_⟩,
    ⟨hreg, hfin, fun p q hpq hne => ?_, fun A => ?_⟩⟩
  · obtain ⟨O, hO, hne', hsub⟩ := staticCausality.exists_isOpen_subset_Jminus_diff hpq hne
    exact (hpos O hO hne').trans_le (measure_mono hsub)
  · exact measure_mono_null (staticCausality.Jminus_diff_Kminus_subset_frontier A) (hnull A).1
  · obtain ⟨O, hO, hne', hsub⟩ := staticCausality.exists_isOpen_subset_Jplus_diff hpq hne
    exact (hpos O hO hne').trans_le (measure_mono hsub)
  · exact measure_mono_null (staticCausality.Jplus_diff_Kplus_subset_frontier A) (hnull A).2

/-- A finite regular measure on `ℝ^{1+n}`, positive on non-empty open sets, which charges the
frontier of no open past set and of no open future set. -/
theorem minkowski_exists_measure (n : ℕ) :
    ∃ μ : Measure (Minkowski n), μ.Regular ∧ μ univ < ⊤ ∧
      (∀ O : Set (Minkowski n), IsOpen O → O.Nonempty → 0 < μ O) ∧
      ∀ A : Set (Minkowski n), μ (frontier ((minkowski n).Iminus ⊤ A)) = 0 ∧
        μ (frontier ((minkowski n).Iplus ⊤ A)) = 0 :=
  Causal.Flat.minkowski_frontier_null_measure n

/-- `prop:mesure_dieckmann_Lorentz` for Minkowski space `ℝ^{1,n}`: a measure admissible both in
the past and in the future. Rests on `minkowski_exists_measure`. -/
theorem minkowski_mesure_dieckmann (n : ℕ) :
    ∃ μ : Measure (Minkowski n), (minkowski n).AdmissiblePast μ ∧
      (minkowski n).AdmissibleFuture μ := by
  obtain ⟨μ, hreg, hfin, hpos, hnull⟩ := minkowski_exists_measure n
  exact ⟨μ, minkowski_mesure_dieckmann_of hreg hfin hpos hnull⟩

end Causal
