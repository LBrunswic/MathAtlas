import Causal.GlobalHyperbolicity
import Causal.Reachable
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Sequences

/-!
# Admissible measures, and the continuity of `p ↦ μ(J^±(p))`

**`defi:mesure_dieckmann`** — `ETT.tex:1032`. **`rem:mesure_bord`** — `ETT.tex:1042`.
**`prop:cont_ext_cont`** — `ETT.tex:1219`.

> A measure $\mu$ on $M$ is admissible \emph{in the past} (resp. \emph{in the future}) if it
> satisfies the following properties: 1. $\mu$ is a regular Borel measure on $M$;
> 2. $\mu(M)<+\infty$; 3. for all $p,q\in M$, if $p<q$ then
> $\mu(J^-(q)\setminus J^-(p))>0$ (resp. $\mu(J^+(p)\setminus J^+(q))>0$); 4. for every
> $A \subset M$, $\mu(J^-(A)\setminus K^-(A))=0$ (resp. $\mu(J^+(A)\setminus K^+(A))=0$).

> Let $M$ be a topological spacetime. If $M$ is tarentin and globally hyperbolic and if $\mu$ is
> a measure admissible in the past (resp. in the future) on $M$, then $p\mapsto \mu(J^-(p))$
> (resp. $p\mapsto \mu(J^+(p))$) is continuous.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `defi:mesure_dieckmann` 1. regular Borel measure | ✓ carried: `BorelSpace M`, `μ.Regular` |
| — 2. `μ(M) < +∞` | ✓ carried |
| — 3. `p < q` | ✓ carried: `p ≤ q` and `p ≠ q` |
| — 4., read for the outer measure (`rem:mesure_bord`) | ✓ carried: mathlib's `μ s` is the outer measure of `s` |
| `prop:cont_ext_cont`: tarentin, globally hyperbolic, admissible measure | ✓ carried |
| — Hausdorff | ✓ carried: `T2Space M` |
| — second countable | ⚠ weakened: `FirstCountableTopology M` |

## SCOPE (disclosed)

* **`prop:cont_ext_cont` is proved without the measurability of `K^-(p)`.** The paper applies
  inner regularity to `K^-(p)` (and `rem:K_borelien` explains why it is Borel). Here property 4.
  gives a measurable null set `Z ⊃ J^-(p) ∖ K^-(p)`, and inner regularity is applied to the
  measurable set `J^-(p) ∖ Z ⊂ K^-(p)`, which has the measure of `J^-(p)`.
* Property 4. is used for `A = {p}` only.
* `AdmissiblePast.lt_of_le_of_ne` is the monotonicity used in the sketch of proof of
  `theo:geroch`, (i)⇒(ii): `x < y` implies `μ(J^-(x)) < μ(J^-(y))`. The theorem itself is not
  stated in this file.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter MeasureTheory

open scoped ENNReal

universe u

variable {M : Type u} [TopologicalSpace M]

section openHull

variable {A S T : Set M}

/-- The largest open set whose trace on `A` is contained in `S`. -/
def openHull (A S : Set M) : Set M := ⋃₀ {O | IsOpen O ∧ O ∩ A ⊆ S}

theorem isOpen_openHull : IsOpen (openHull A S) := isOpen_sUnion fun _ hO => hO.1

/-- The relative interior is the trace of an open set. -/
theorem interiorWithin_eq : interiorWithin A S = A ∩ openHull A S := by
  ext x
  constructor
  · rintro ⟨hxA, hS⟩
    obtain ⟨O, hO, hxO, hsub⟩ := mem_nhdsWithin.1 hS
    exact ⟨hxA, mem_sUnion.2 ⟨O, ⟨hO, hsub⟩, hxO⟩⟩
  · rintro ⟨hxA, hx⟩
    obtain ⟨O, ⟨hO, hsub⟩, hxO⟩ := mem_sUnion.1 hx
    exact ⟨hxA, mem_nhdsWithin.2 ⟨O, hO, hxO, hsub⟩⟩

theorem openHull_mono (h : S ⊆ T) : openHull A S ⊆ openHull A T :=
  sUnion_subset_sUnion fun _ hO => ⟨hO.1, hO.2.trans h⟩

end openHull

variable [MeasurableSpace M]

namespace Causality

variable (C : Causality M)

/-- **`defi:mesure_dieckmann`**, past. Property 4. is read for the outer measure, as
**`rem:mesure_bord`** asks: `μ s` is defined for every set `s`. -/
structure AdmissiblePast (μ : Measure M) : Prop where
  /-- 1. -/
  regular : μ.Regular
  /-- 2. -/
  finite : μ univ < ∞
  /-- 3. -/
  pos : ∀ ⦃p q : M⦄, C.le ⊤ p q → p ≠ q → 0 < μ (C.Jminus ⊤ {q} \ C.Jminus ⊤ {p})
  /-- 4. -/
  null : ∀ A : Set M, μ (C.Jminus ⊤ A \ C.Kminus ⊤ A) = 0

/-- **`defi:mesure_dieckmann`**, future. -/
structure AdmissibleFuture (μ : Measure M) : Prop where
  /-- 1. -/
  regular : μ.Regular
  /-- 2. -/
  finite : μ univ < ∞
  /-- 3. -/
  pos : ∀ ⦃p q : M⦄, C.le ⊤ p q → p ≠ q → 0 < μ (C.Jplus ⊤ {p} \ C.Jplus ⊤ {q})
  /-- 4. -/
  null : ∀ A : Set M, μ (C.Jplus ⊤ A \ C.Kplus ⊤ A) = 0

variable {C} {μ : Measure M}

theorem dual_admissiblePast : C.dual.AdmissiblePast μ ↔ C.AdmissibleFuture μ :=
  ⟨fun h => ⟨h.regular, h.finite, fun _ _ hpq hne => h.pos hpq (Ne.symm hne), h.null⟩,
    fun h => ⟨h.regular, h.finite, fun _ _ hpq hne => h.pos hpq (Ne.symm hne), h.null⟩⟩

theorem dual_admissibleFuture : C.dual.AdmissibleFuture μ ↔ C.AdmissiblePast μ :=
  ⟨fun h => ⟨h.regular, h.finite, fun _ _ hpq hne => h.pos hpq (Ne.symm hne), h.null⟩,
    fun h => ⟨h.regular, h.finite, fun _ _ hpq hne => h.pos hpq (Ne.symm hne), h.null⟩⟩

/-- **`prop:cont_ext_cont`**, past. -/
theorem AdmissiblePast.continuous_measure_Jminus [T2Space M] [FirstCountableTopology M]
    [BorelSpace M] (hμ : C.AdmissiblePast μ) (hT : C.Tarentin) (hG : C.GloballyHyperbolic) :
    Continuous fun p => μ (C.Jminus ⊤ {p}) := by
  haveI := hμ.regular
  haveI : IsFiniteMeasure μ := ⟨hμ.finite⟩
  rw [continuous_iff_seqContinuous]
  intro q p hq
  show Tendsto (fun n => μ (C.Jminus ⊤ {q n})) atTop (𝓝 (μ (C.Jminus ⊤ {p})))
  rw [ENNReal.tendsto_nhds (measure_ne_top μ _)]
  intro ε hε
  have hε0 : ε ≠ 0 := hε.ne'
  have hJclosed : ∀ x, IsClosed (C.Jminus ⊤ {x}) := hG.isClosed_Jminus_singleton hT
  -- from below: a compact subset of `K^-(p)` carrying almost all the measure of `J^-(p)`
  have hlow : ∀ᶠ n in atTop, μ (C.Jminus ⊤ {p}) ≤ μ (C.Jminus ⊤ {q n}) + ε := by
    obtain ⟨Z, hZsub, hZmeas, hZnull⟩ := exists_measurable_superset_of_null (hμ.null {p})
    have hEmeas : MeasurableSet (C.Jminus ⊤ {p} \ Z) := (hJclosed p).measurableSet.diff hZmeas
    have hEK : C.Jminus ⊤ {p} \ Z ⊆ C.Kminus ⊤ {p} := by
      rintro x ⟨hxJ, hxZ⟩
      by_contra hxK
      exact hxZ (hZsub ⟨hxJ, hxK⟩)
    have hμE : μ (C.Jminus ⊤ {p} \ Z) = μ (C.Jminus ⊤ {p}) := measure_sdiff_null hZnull
    obtain ⟨K, hKE, hKc, hKlt⟩ := hEmeas.exists_isCompact_lt_add (measure_ne_top μ _) hε0
    let S : ℕ → Set M := fun N => C.Jminus ⊤ {p} ∩ ⋂ n ≥ N, C.Jminus ⊤ {q n}
    have hScover : K ⊆ ⋃ N, openHull (C.Jminus ⊤ {p}) (S N) := by
      intro x hx
      obtain ⟨N, hN⟩ := mem_Kminus_singleton.1 (hEK (hKE hx)) q hq
      rw [interiorWithin_eq] at hN
      exact mem_iUnion.2 ⟨N, hN.2⟩
    have hSmono : ∀ N N', N ≤ N' → S N ⊆ S N' := by
      intro N N' hNN' x hx
      refine ⟨hx.1, ?_⟩
      have hx2 := hx.2
      simp only [mem_iInter] at hx2 ⊢
      exact fun n hn => hx2 n (hNN'.trans hn)
    have hdir : Directed (· ⊆ ·) fun N => openHull (C.Jminus ⊤ {p}) (S N) := fun N N' =>
      ⟨max N N', openHull_mono (hSmono _ _ (le_max_left _ _)),
        openHull_mono (hSmono _ _ (le_max_right _ _))⟩
    obtain ⟨N, hN⟩ := hKc.elim_directed_cover _ (fun _ => isOpen_openHull) hScover hdir
    refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
    have hKsub : K ⊆ C.Jminus ⊤ {q n} := by
      intro x hx
      have hxint : x ∈ interiorWithin (C.Jminus ⊤ {p}) (S N) := by
        rw [interiorWithin_eq]
        exact ⟨(hKE hx).1, hN hx⟩
      have hxS := (interiorWithin_subset hxint).2
      simp only [mem_iInter] at hxS
      exact hxS n hn
    calc μ (C.Jminus ⊤ {p}) = μ (C.Jminus ⊤ {p} \ Z) := hμE.symm
      _ ≤ μ K + ε := hKlt.le
      _ ≤ μ (C.Jminus ⊤ {q n}) + ε := add_le_add_left (measure_mono hKsub) ε
  -- from above: a compact subset of the complement of `J^-(p)`, whose causal future is closed
  have hup : ∀ᶠ n in atTop, μ (C.Jminus ⊤ {q n}) ≤ μ (C.Jminus ⊤ {p}) + ε := by
    have hFmeas : MeasurableSet (C.Jminus ⊤ {p})ᶜ := (hJclosed p).measurableSet.compl
    obtain ⟨K, hKF, hKc, hKlt⟩ := hFmeas.exists_isCompact_lt_add (measure_ne_top μ _) hε0
    have hJK : IsClosed (C.Jplus ⊤ K) := isClosed_Jplus_of_isCompact (hG.isClosed_le hT) hKc
    have hp : p ∉ C.Jplus ⊤ K := by
      rintro ⟨c, hc, hcp⟩
      exact hKF hc (by simpa using hcp)
    have hev : ∀ᶠ n in atTop, q n ∈ (C.Jplus ⊤ K)ᶜ :=
      hq.eventually (hJK.isOpen_compl.mem_nhds hp)
    refine hev.mono fun n hn => ?_
    have hdisj : Disjoint (C.Jminus ⊤ {q n}) K := by
      rw [Set.disjoint_left]
      intro c hcJ hcK
      exact hn ⟨c, hcK, by simpa using hcJ⟩
    have h1 : μ (C.Jminus ⊤ {q n}) + μ K ≤ μ univ := by
      rw [← measure_union hdisj hKc.measurableSet]
      exact measure_mono (subset_univ _)
    have h2 : μ univ = μ (C.Jminus ⊤ {p}) + μ (C.Jminus ⊤ {p})ᶜ :=
      (measure_add_measure_compl (hJclosed p).measurableSet).symm
    have h3 : μ (C.Jminus ⊤ {q n}) + μ K ≤ μ (C.Jminus ⊤ {p}) + ε + μ K := by
      calc μ (C.Jminus ⊤ {q n}) + μ K ≤ μ univ := h1
        _ = μ (C.Jminus ⊤ {p}) + μ (C.Jminus ⊤ {p})ᶜ := h2
        _ ≤ μ (C.Jminus ⊤ {p}) + (μ K + ε) := add_le_add_right hKlt.le _
        _ = μ (C.Jminus ⊤ {p}) + ε + μ K := by ring
    exact ENNReal.le_of_add_le_add_right (measure_ne_top μ K) h3
  filter_upwards [hlow, hup] with n h1 h2
  exact ⟨tsub_le_iff_right.2 h1, h2⟩

/-- **`prop:cont_ext_cont`**, future. -/
theorem AdmissibleFuture.continuous_measure_Jplus [T2Space M] [FirstCountableTopology M]
    [BorelSpace M] (hμ : C.AdmissibleFuture μ) (hT : C.Tarentin) (hG : C.GloballyHyperbolic) :
    Continuous fun p => μ (C.Jplus ⊤ {p}) :=
  AdmissiblePast.continuous_measure_Jminus (C := C.dual) (dual_admissiblePast.2 hμ)
    (dual_tarentin.2 hT) (dual_globallyHyperbolic.2 hG)

/-- `theo:geroch`, (i)⇒(ii), the monotonicity of `t^-`: if `x < y` then
`μ(J^-(x)) < μ(J^-(y))`. -/
theorem AdmissiblePast.lt_of_le_of_ne [T2Space M] [BorelSpace M] (hμ : C.AdmissiblePast μ)
    (hT : C.Tarentin) (hG : C.GloballyHyperbolic) {x y : M} (hxy : C.le ⊤ x y) (hne : x ≠ y) :
    μ (C.Jminus ⊤ {x}) < μ (C.Jminus ⊤ {y}) := by
  haveI : IsFiniteMeasure μ := ⟨hμ.finite⟩
  have hmeas : MeasurableSet (C.Jminus ⊤ {x}) :=
    (hG.isClosed_Jminus_singleton hT x).measurableSet
  have hsub : C.Jminus ⊤ {x} ⊆ C.Jminus ⊤ {y} := Precausality.Jminus_singleton_subset hxy
  have hsplit : μ (C.Jminus ⊤ {y}) =
      μ (C.Jminus ⊤ {x}) + μ (C.Jminus ⊤ {y} \ C.Jminus ⊤ {x}) := by
    rw [← measure_union disjoint_sdiff_right (by
      exact (hG.isClosed_Jminus_singleton hT y).measurableSet.diff hmeas)]
    rw [union_sdiff_cancel hsub]
  rw [hsplit]
  exact ENNReal.lt_add_right (measure_ne_top μ _) (hμ.pos hxy hne).ne'

/-- `theo:geroch`, (i)⇒(ii), the monotonicity of `t^+`: if `x < y` then
`μ(J^+(y)) < μ(J^+(x))`. -/
theorem AdmissibleFuture.lt_of_le_of_ne [T2Space M] [BorelSpace M] (hμ : C.AdmissibleFuture μ)
    (hT : C.Tarentin) (hG : C.GloballyHyperbolic) {x y : M} (hxy : C.le ⊤ x y) (hne : x ≠ y) :
    μ (C.Jplus ⊤ {y}) < μ (C.Jplus ⊤ {x}) :=
  AdmissiblePast.lt_of_le_of_ne (C := C.dual) (dual_admissiblePast.2 hμ) (dual_tarentin.2 hT)
    (dual_globallyHyperbolic.2 hG) (x := y) (y := x) hxy (Ne.symm hne)

end Causality

end Causal
