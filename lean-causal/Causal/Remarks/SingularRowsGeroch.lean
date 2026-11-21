import Causal.Port.SFAManifolds
import Causal.Remarks.BTZPoints
import Causal.MeasureRemarks
import Causal.SingularGeroch
import Causal.Geroch
import Causal.Port.MeasuresE0
import Causal.Model.MeasuresEAlpha

/-!
# The two senses of admissibility, and Geroch's theorem, at every `E_{≥0}`-manifold

Target `T-ett-singular-rows-geroch`. Cited, unmarked (SCOPE): `rem:mesure_unilaterale` —
`ETT.tex:1713`; `rem:mesure_unilaterale_ptr` — `ETT.tex:1045`; `theo:geroch_sing` —
`ETT.tex:1771`. For a singular `(Isom(𝐌³), 𝐌³)`-manifold `M` (DEC-25) and every absolutely minimal
causality `C` with an isomorphic chart at each point over the family `E_{≥0}`
(`IsoChartsCoverDEC25 … massAModelCausality`; the natural causality is one), the three rows are
stated at `M` itself, not under the abstraction `SingularFlatAxioms`: at a Hausdorff `M` with a BTZ
point no measure is admissible in the past and in the future at once; the obstruction of
`rem:mesure_unilaterale_ptr` holds at every `M` with its hypothesis `K⁺(p) ⊆ I⁺(p)` discharged;
`theo:geroch_sing`'s (i)⇒(ii) and (i)⇒(iii) hold at every Hausdorff, second countable, globally
hyperbolic `M` with no hypothesis left, and (ii)⇒(iii) at every strongly causal one (DEC-18). The
equivalence itself is stated at genuine `E_{≥0}`-manifolds in the scaffold remainder
`CausalScaffold.SingularRowsGerochEquiv` (same full names), where it rests on one tagged `sorry`,
its (iii)⇒(i).

> As soon as a spacetime carries the analogue of a BTZ line --- a causal chain along which
> chronological pasts are empty --- no measure on it is admissible in the past and in the future
> at once, property $4$ being the obstruction. (`rem:mesure_unilaterale_ptr`, `ETT.tex:1046–1048`)

> Let $M$ be a causal $\mass{\geq0}$-manifold and let $p<q$ be two BTZ points of one singular line
> $\Delta$. By Definition \ref{defi:causal_E0} the set $J^-(q)\setminus J^-(p)$ is the segment
> $]p,q]$ of $\Delta$, so property $3$ in the past forces $\mu(]p,q])>0$. But every
> $r\in\,]p,q]$ is a BTZ point, hence $I^-(r)=\emptyset$ and therefore $r\notin I^+(p)=K^+(p)$ by
> Proposition \ref{prop:K_calcul}; thus $]p,q]\subset J^+(p)\setminus K^+(p)$ and property $4$ in
> the future forces $\mu(]p,q])=0$. No measure on $M$ is therefore admissible in the past and in
> the future at once. (`rem:mesure_unilaterale`, `ETT.tex:1716–1723`)

> Let $M$ be a singular flat spacetime. The following are equivalent: (i) $M$ is globally
> hyperbolic; (ii) $M$ admits a Cauchy time function; (iii) $M$ admits a Cauchy hypersurface.
> Moreover, if $\Sigma$ is a Cauchy surface of $M$, then $M$ is homeomorphic to $\Sigma\times \RR$.
> (`theo:geroch_sing`, `ETT.tex:1772–1778`)

## What is proved

* **Model-free** (`isCausal_of_admissiblePast`, `isCausal_of_admissibleFuture`): a causality
  carrying a measure admissible in the past (or in the future) is causal. Property 3. with
  `p ≤ q ≤ p`, `p ≠ q` asks `μ ∅ > 0`.
* `rem:mesure_unilaterale_ptr` (unmarked) **at every `E_{≥0}`-manifold** (no Hausdorff,
  countability or causality): `K⁺(p) = I⁺(p)` at every point (`Kplus_eq_Iplus`,
  `SFABTZ.K_calcul` (a), (b)), so the strict obstruction
  `Causality.not_admissiblePast_and_admissibleFuture` holds with no added hypothesis
  (`not_admissible_both_of_chain`). A point has empty chronological past iff it is a
  BTZ point (`Iminus_eq_empty_iff`), so such a chain lies in `sing₀(M)` (`chain_subset_sing`).
* `rem:mesure_unilaterale` (unmarked) **at every Hausdorff `E_{≥0}`-manifold**, the remark's
  computation at `M`: for `q` BTZ and `p ≤ q`, `J⁻(q) ∖ J⁻(p)` is the segment `γ(]t₀, 0])` of the
  BTZ line through `q` (`Jminus_diff_eq_segment`, `M` causal), inside `(J⁺(p) ∖ K⁺(p)) ∩ sing₀(M)`
  (`segment_subset`); hence no measure is admissible both ways (`not_admissible_both_of_le`;
  `mesure_unilaterale` from `sing₀(M) ≠ ∅`; the natural causality,
  `mesure_unilaterale_of_isAtlasCausalityDEC25`). With strong causality each one-sided notion is
  inhabited (`mesure_unilaterale_sharp`, through `SFAManifolds.mesure_admissible`).
* **The strict `_of_pushUp` obstruction is witnessed** (`pushUp_obstruction_hypotheses`,
  `exists_pushUp_obstruction`, `nonvacuous_e0_chain`): its hypotheses hold at every causal
  Hausdorff `M` with a BTZ point, `E₀` among them.
* `theo:geroch_sing` (unmarked), **the proved directions**: `geroch_sing_i_imp_ii`,
  `geroch_sing_i_imp_iii` (strong causality from `GloballyHyperbolic.stronglyCausal` and
  `SFALocal.tarentin`, `ModelMeasures` from `MeasuresManifolds.massA_modelMeasures`,
  `SingularFlatAxioms` from `SFAManifolds.singularFlatAxioms`), `geroch_sing_ii_imp_iii` (strongly
  causal), their natural forms; the splitting `geroch_sing_split` (connected, causal, the flow of
  `lem:vecteur` as the named hypothesis `VecteurFlow`).
* **Witnesses**, each conclusion out of this file's theorems: `E₀` (`nonvacuous_e0_unilaterale`,
  `nonvacuous_e0_chain`, `nonvacuous_e0_geroch`, `nonvacuous_e0_natural`); `E_π`, globally
  hyperbolic with a massive line (`nonvacuous_epi_geroch`), and carrying a measure admissible both
  ways (`epi_admissible_both`: the BTZ point cannot be dropped).
* **The equivalence, stated** (`geroch_sing`, `geroch_sing_of_isAtlasCausalityDEC25`): in the
  scaffold remainder `CausalScaffold.SingularRowsGerochEquiv`, resting on `geroch_sing_iii_imp_i`,
  a tagged `sorry`; this module is sorry-free.

## Hypothesis checklist

| paper | here |
|---|---|
| « an `E_{≥0}`-manifold », « a singular flat spacetime » | ⚠ read (DEC-25, OQ-18): `[SingularGXStructure (Flat.isom 2) (Minkowski 2) M]`, `C` absolutely minimal with `IsoChartsCoverDEC25` (the natural causality: the `_of_isAtlasCausalityDEC25` forms) |
| Hausdorff, second countable (`ETT.tex:255`) | ✓ carried where used: `T2Space` (the BTZ line, `SFALine.line`); `SecondCountableTopology` for Geroch only; ⚠ weakened: neither in `not_admissible_both_of_chain`, no second countability in the measure rows |
| `rem:mesure_unilaterale`: `M` causal | ⚠ weakened: not assumed by `not_admissible_both_of_le`, `mesure_unilaterale` (`isCausal_of_admissiblePast`); assumed by the segment computation |
| — `p < q` two BTZ points of one singular line | ⚠ weakened: `q` BTZ, `p ≤ q`, `p ≠ q` (`p` is then BTZ, on the line of `q`: `SFABTZ.mem_sing_zero_of_le`, `Jminus_subset_component`); or `sing₀(M) ≠ ∅` |
| — « a measure on `M` » | ✓ `[MeasurableSpace M]`; property 1. is the field `regular` |
| `rem:mesure_unilaterale_ptr`: « a causal chain along which chronological pasts are empty » | ✓ carried at `E_{≥0}`-manifolds: `p ≤ q`, `p ≠ q`, `J⁻(q) ∖ J⁻(p) ⊆ J⁺(p)`, `I⁻(r) = ∅` on it; « a spacetime »: false in general (the lightlike line, `Causal.MeasureRemarks`) |
| — `K⁺(p) ⊆ I⁺(p)` (the strict obstruction's added hypothesis) | discharged: `Kplus_eq_Iplus` |
| `theo:geroch_sing`: connected | ✓ carried by `geroch_sing`, `geroch_sing_iii_imp_i`, `geroch_sing_split`; ⚠ weakened: not used by the proved directions |
| — strongly causal (DEC-18) | ✓ carried by `geroch_sing`, `geroch_sing_ii_imp_iii`; ⚠ weakened: not assumed by (i)⇒(ii), (i)⇒(iii); causal only in `geroch_sing_split` |
| — the measures, `ModelMeasures` | discharged (`MeasuresManifolds.massA_modelMeasures`); no `MeasurableSpace` in the statements (Borel inside the proofs) |
| — (ii) a Cauchy time function; (iii) a Cauchy hypersurface | ⚠ reading: strictly increasing along `≤` (DEC-15); `IsCauchySurface` (DEC-14) |
| — « homeomorphic to `Σ × ℝ` » | ⚠ strengthened: `VecteurFlow C` (`lem:vecteur`, kb/0022) |
| `E₀` (l.1330), `Isom(𝔼^{1,2})` | ⚠ read: `Causal.E0` (OQ-34, OQ-35), `Flat.isom 2` (OQ-82) |

## SCOPE (disclosed)

* **Why unmarked.** The rows rest on the readings DEC-25, OQ-18, OQ-34/OQ-35 and OQ-82; the
  equivalence of `theo:geroch_sing` (scaffold remainder) rests on one `sorry` (OQ-32) and its splitting on
  `VecteurFlow`.
* **The one `sorry`** (in the scaffold remainder `CausalScaffold.SingularRowsGerochEquiv`),
  `geroch_sing_iii_imp_i`: (iii)⇒(i) at a strongly causal, connected,
  Hausdorff, second countable `E_{≥0}`-manifold. The paper's route is `theo:geroch`'s cited
  (iii)⇒(i), false for topological spacetimes (OQ-32, `CausalScaffold.GerochCauchy`). OQ-33's
  witness against the abstract form, chronological Minkowski space, has an isomorphic chart at no
  point, for any singular structure (by hand: a chart isomorphism carries `≤` and `≪` of an open
  set onto a model's, and every open set of a model contains `x ≤ y`, `x ≠ y`, not `x ≪ y`, which
  the reflexive chronological causality excludes; not formalized, `CausalScaffold.GerochCauchy`
  being a scaffold module), so the statement here is not refuted. Its proof needs
  O'Neill's quasi-limits of causal curves with the local closedness of the models' relations
  (`lem:densite_modele`); the library has neither.
* **`sing₀(M)`** is `SFALocal.sing M 0` (brunswic2021cauchy Cor. 1.5). The `E₀`-manifold forms
  follow through `SFALocal.isoChartsCoverDEC25_of_e0` and `SFALocal.sing_eq_of_e0Covered`, not
  stated.
* **Witnesses.** `E₀` has BTZ points only, `E_π` massive points only. `VecteurFlow` has no witness
  at `E₀`; the timelike line's (`Causal.SingularGeroch`) stands.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Imports the strict
`Causal.Port.SFAManifolds`, `Causal.Remarks.BTZPoints`, `Causal.MeasureRemarks`,
`Causal.SingularGeroch`, `Causal.Geroch`, `Causal.Port.MeasuresE0`, `Causal.Model.MeasuresEAlpha`.
-/

namespace Causal

open Set Filter Topology TopologicalSpace MeasureTheory

universe u

namespace SingularRowsGeroch

/-! ### Model-free: a measure admissible on one side makes the causality causal -/

section ModelFree

variable {M : Type u} [TopologicalSpace M] [MeasurableSpace M] {C : Causality M} {μ : Measure M}

/-- **A causality carrying a measure admissible in the past is causal**: for `x ≤ y ≤ x`,
`x ≠ y`, property 3. asks `μ (J⁻(y) ∖ J⁻(x)) > 0`, and `J⁻(y) ⊆ J⁻(x)`. -/
theorem isCausal_of_admissiblePast (hμ : C.AdmissiblePast μ) : C.IsCausal := by
  intro x y hxy hyx
  by_contra hne
  have hsub : C.Jminus ⊤ {y} \ C.Jminus ⊤ {x} = ∅ := by
    refine sdiff_eq_empty.2 fun r hr => ?_
    have hr' : C.le ⊤ r y := by simpa using hr
    simpa using C.le_trans hr' hyx
  have h := hμ.pos hxy hne
  rw [hsub, measure_empty] at h
  exact lt_irrefl 0 h

/-- **A causality carrying a measure admissible in the future is causal.** -/
theorem isCausal_of_admissibleFuture (hμ : C.AdmissibleFuture μ) : C.IsCausal := by
  intro x y hxy hyx
  by_contra hne
  have hsub : C.Jplus ⊤ {x} \ C.Jplus ⊤ {y} = ∅ := by
    refine sdiff_eq_empty.2 fun r hr => ?_
    have hr' : C.le ⊤ x r := by simpa using hr
    simpa using C.le_trans hyx hr'
  have h := hμ.pos hxy hne
  rw [hsub, measure_empty] at h
  exact lt_irrefl 0 h

end ModelFree

/-! ### `rem:mesure_unilaterale_ptr` at every `E_{≥0}`-manifold: `K⁺ = I⁺`, empty pasts -/

section Chains

variable {M : Type u} [TopologicalSpace M] [SingularGXStructure (Flat.isom 2) (Minkowski 2) M]
  {C : Causality M} {p q : M}

/-- **`K⁺(p) = I⁺(p)` at every point of every `E_{≥0}`-manifold**: `prop:K_calcul` (a) off
`sing₀(M)`, (b) on it (`SFABTZ.K_calcul`). The hypothesis the strict obstruction adds. -/
theorem Kplus_eq_Iplus (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) (p : M) :
    C.Kplus ⊤ {p} = C.Iplus ⊤ {p} := by
  by_cases hp : p ∈ SFALocal.sing M 0
  · exact (SFABTZ.K_calcul hmin hC).2.1 p hp
  · exact ((SFABTZ.K_calcul hmin hC).1 p hp).1

/-- A point with empty chronological past is a BTZ point (off `sing₀(M)` every point lies in
`Z⁻`). -/
theorem mem_sing_zero_of_Iminus_eq_empty
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) {r : M}
    (hr : C.Iminus ⊤ {r} = ∅) : r ∈ SFALocal.sing M 0 := by
  by_contra h
  obtain ⟨z, hz⟩ := Causality.Iminus_nonempty_of_mem_Zminus (SFALocal.mem_Zminus_of_notMem hC h)
  rw [hr] at hz
  exact hz

/-- **The chronological past of a point is empty iff it is a BTZ point.** -/
theorem Iminus_eq_empty_iff (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) (r : M) :
    C.Iminus ⊤ {r} = ∅ ↔ r ∈ SFALocal.sing M 0 := by
  exact ⟨mem_sing_zero_of_Iminus_eq_empty hC, SFALocal.Iminus_eq_empty hmin hC r⟩

/-- `rem:mesure_unilaterale_ptr` (unmarked) **at every `E_{≥0}`-manifold**: a causal chain `p ≤ q`,
`p ≠ q`, with `J⁻(q) ∖ J⁻(p) ⊆ J⁺(p)` and empty chronological pasts along it, forbids any
measure admissible in the past and in the future at once. The strict
`Causality.not_admissiblePast_and_admissibleFuture` with its hypothesis `K⁺(p) ⊆ I⁺(p)`
discharged; no Hausdorff, countability or causality hypothesis. -/
theorem not_admissible_both_of_chain [MeasurableSpace M] (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    {μ : Measure M} (hpq : C.le ⊤ p q) (hne : p ≠ q)
    (hline : C.Jminus ⊤ {q} \ C.Jminus ⊤ {p} ⊆ C.Jplus ⊤ {p})
    (hempty : ∀ r ∈ C.Jminus ⊤ {q} \ C.Jminus ⊤ {p}, C.Iminus ⊤ {r} = ∅) :
    ¬ (C.AdmissiblePast μ ∧ C.AdmissibleFuture μ) := by
  exact Causality.not_admissiblePast_and_admissibleFuture hpq hne hline hempty
    (Kplus_eq_Iplus hmin hC p).subset

/-- At an `E_{≥0}`-manifold « the analogue of a BTZ line » is one: a chain along which
chronological pasts are empty lies in `sing₀(M)`. -/
theorem chain_subset_sing
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hempty : ∀ r ∈ C.Jminus ⊤ {q} \ C.Jminus ⊤ {p}, C.Iminus ⊤ {r} = ∅) :
    C.Jminus ⊤ {q} \ C.Jminus ⊤ {p} ⊆ SFALocal.sing M 0 := by
  exact fun r hr => mem_sing_zero_of_Iminus_eq_empty hC (hempty r hr)

end Chains

/-! ### `rem:mesure_unilaterale` at every Hausdorff `E_{≥0}`-manifold -/

section Unilaterale

variable {M : Type u} [TopologicalSpace M] [SingularGXStructure (Flat.isom 2) (Minkowski 2) M]
  {C : Causality M} {p q : M}

/-- Above every BTZ point of a causal Hausdorff `E_{≥0}`-manifold there is another, on its line. -/
theorem exists_le_ne_of_mem_sing [T2Space M]
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hc : C.IsCausal) (hp : p ∈ SFALocal.sing M 0) :
    ∃ q ∈ SFALocal.sing M 0, C.le ⊤ p q ∧ p ≠ q := by
  obtain ⟨γ, hγ0, hγ, hγi, hγr⟩ := SFALine.line hC p hp
  have hemb := hγ hc
  have h1 : γ 1 ∈ SFALocal.sing M 0 := by
    have hmem : γ 1 ∈ range γ := mem_range_self 1
    rw [hγr] at hmem
    exact connectedComponentIn_subset _ _ hmem
  have hle : C.le ⊤ p (γ 1) := by
    have h01 := hγi.1.le_of_le trivial trivial zero_le_one
    rwa [hγ0] at h01
  refine ⟨γ 1, h1, hle, fun heq => ?_⟩
  rw [← hγ0] at heq
  exact zero_ne_one (hemb.injective heq)

/-- **The segment** (`rem:mesure_unilaterale`, « by Definition `defi:causal_E0` »): at a causal
Hausdorff `E_{≥0}`-manifold, for a BTZ point `q` and `p ≤ q`, `J⁻(q) ∖ J⁻(p)` is the segment
`γ(]t₀, 0]) = ]p, q]` of the BTZ line `γ` through `q` (`γ 0 = q`, `γ t₀ = p`). -/
theorem Jminus_diff_eq_segment [T2Space M] (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hc : C.IsCausal) (hq : q ∈ SFALocal.sing M 0) (hpq : C.le ⊤ p q) :
    ∃ γ : ℝ → M, ∃ t₀ : ℝ, γ 0 = q ∧ γ t₀ = p ∧ t₀ ≤ 0 ∧ IsClosedEmbedding γ ∧
      C.CausalCurveIn ⊤ univ γ ∧ range γ = connectedComponentIn (SFALocal.sing M 0) q ∧
      C.Jminus ⊤ {q} \ C.Jminus ⊤ {p} = γ '' Ioc t₀ 0 := by
  obtain ⟨γ, hγ0, hemb, hγi, hγr, hJq⟩ := SFALine.Jminus_eq_image hmin hC hc hq
  have hγc : C.CausalCurveIn ⊤ univ γ := hγi.1
  have hpJ : p ∈ C.Jminus ⊤ {q} := by simpa using hpq
  rw [hJq] at hpJ
  obtain ⟨t₀, ht₀, rfl⟩ := hpJ
  refine ⟨γ, t₀, hγ0, rfl, ht₀, hemb, hγc, hγr, ?_⟩
  rw [hJq]
  ext r
  constructor
  · rintro ⟨⟨s, hs, rfl⟩, hns⟩
    refine ⟨s, ⟨?_, hs⟩, rfl⟩
    by_contra hst
    exact hns (by simpa using hγc.le_of_le trivial trivial (not_lt.1 hst))
  · rintro ⟨s, ⟨hts, hs0⟩, rfl⟩
    refine ⟨⟨s, hs0, rfl⟩, fun hle => ?_⟩
    have h1 : C.le ⊤ (γ s) (γ t₀) := by simpa using hle
    have h2 : C.le ⊤ (γ t₀) (γ s) := hγc.le_of_le trivial trivial hts.le
    exact hts.ne' (hemb.injective (hc h1 h2))

/-- **The remark's computation**: the segment `J⁻(q) ∖ J⁻(p)` consists of BTZ points (so their
chronological pasts are empty) and lies in `J⁺(p) ∖ K⁺(p)`, since `K⁺(p) = I⁺(p)`. -/
theorem segment_subset [T2Space M] (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hc : C.IsCausal) (hq : q ∈ SFALocal.sing M 0) (hpq : C.le ⊤ p q) :
    C.Jminus ⊤ {q} \ C.Jminus ⊤ {p} ⊆ (C.Jplus ⊤ {p} \ C.Kplus ⊤ {p}) ∩ SFALocal.sing M 0 := by
  obtain ⟨γ, t₀, -, hγt, -, -, hγc, -, hseg⟩ := Jminus_diff_eq_segment hmin hC hc hq hpq
  intro r hr
  have hsing : r ∈ SFALocal.sing M 0 :=
    SFABTZ.mem_sing_zero_of_le hmin hC hq (by simpa using hr.1)
  have hpr : C.le ⊤ p r := by
    rw [hseg] at hr
    obtain ⟨s, ⟨hts, -⟩, rfl⟩ := hr
    rw [← hγt]
    exact hγc.le_of_le trivial trivial hts.le
  refine ⟨⟨by simpa using hpr, fun hrK => ?_⟩, hsing⟩
  rw [Kplus_eq_Iplus hmin hC p] at hrK
  have hpr' : p ∈ C.Iminus ⊤ {r} := by simpa using hrK
  rw [SFALocal.Iminus_eq_empty hmin hC r hsing] at hpr'
  exact hpr'

/-- `rem:mesure_unilaterale` (unmarked) **at every Hausdorff `E_{≥0}`-manifold, for `p ≤ q`,
`p ≠ q`, `q` BTZ**: property 3. in the past forces `μ (J⁻(q) ∖ J⁻(p)) > 0`, property 4. in the
future `μ (J⁺(p) ∖ K⁺(p)) = 0`. `M` causal is not assumed: otherwise no measure is admissible in the
past (`isCausal_of_admissiblePast`). -/
theorem not_admissible_both_of_le [T2Space M] [MeasurableSpace M] (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    {μ : Measure M} (hq : q ∈ SFALocal.sing M 0) (hpq : C.le ⊤ p q) (hne : p ≠ q) :
    ¬ (C.AdmissiblePast μ ∧ C.AdmissibleFuture μ) := by
  rintro ⟨h1, h2⟩
  have hsub :=
    (segment_subset hmin hC (isCausal_of_admissiblePast h1) hq hpq).trans inter_subset_left
  exact (h1.pos hpq hne).ne' (measure_mono_null hsub (h2.null {p}))

/-- `rem:mesure_unilaterale` (unmarked) **at every Hausdorff `E_{≥0}`-manifold with a BTZ
point**: no measure is admissible in the past and in the future at once. -/
theorem mesure_unilaterale [T2Space M] [MeasurableSpace M] (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hS : (SFALocal.sing M 0).Nonempty) (μ : Measure M) :
    ¬ (C.AdmissiblePast μ ∧ C.AdmissibleFuture μ) := by
  rintro ⟨h1, h2⟩
  obtain ⟨p, hp⟩ := hS
  obtain ⟨q, hq, hpq, hne⟩ := exists_le_ne_of_mem_sing hC (isCausal_of_admissiblePast h1) hp
  exact not_admissible_both_of_le hmin hC hq hpq hne ⟨h1, h2⟩

/-- `rem:mesure_unilaterale` (unmarked) **for the natural causality** of a Hausdorff
`E_{≥0}`-manifold with a BTZ point. -/
theorem mesure_unilaterale_of_isAtlasCausalityDEC25 [T2Space M] [MeasurableSpace M]
    (hcov : SFALocal.MassACovered M)
    (hC : IsAtlasCausalityDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hS : (SFALocal.sing M 0).Nonempty) (μ : Measure M) :
    ¬ (C.AdmissiblePast μ ∧ C.AdmissibleFuture μ) := by
  exact mesure_unilaterale (SFALocal.of_isAtlasCausalityDEC25 hcov hC).1
    (SFALocal.of_isAtlasCausalityDEC25 hcov hC).2 hS μ

/-- `rem:mesure_unilaterale` (unmarked), **sharp**: at a strongly causal, Hausdorff, second
countable `E_{≥0}`-manifold with a BTZ point, each one-sided notion is inhabited
(`prop:mesure_admissible`, `SFAManifolds.mesure_admissible`) and no measure has both. -/
theorem mesure_unilaterale_sharp [T2Space M] [SecondCountableTopology M] [MeasurableSpace M]
    [BorelSpace M] (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hSC : C.StronglyCausal) (hS : (SFALocal.sing M 0).Nonempty) :
    (∃ μ : Measure M, C.AdmissiblePast μ) ∧ (∃ μ : Measure M, C.AdmissibleFuture μ) ∧
      ∀ μ : Measure M, ¬ (C.AdmissiblePast μ ∧ C.AdmissibleFuture μ) := by
  obtain ⟨h1, h2⟩ := SFAManifolds.mesure_admissible hmin hC hSC
  exact ⟨h1, h2, mesure_unilaterale hmin hC hS⟩

/-- **The hypotheses of the strict obstructions hold at every BTZ segment** of a causal Hausdorff
`E_{≥0}`-manifold: those of `Causality.not_admissiblePast_and_admissibleFuture_of_pushUp`
(push-up, `p ∈ Z⁺`, the chain, the empty pasts) and `K⁺(p) ⊆ I⁺(p)`. -/
theorem pushUp_obstruction_hypotheses [T2Space M] (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hc : C.IsCausal) (hq : q ∈ SFALocal.sing M 0) (hpq : C.le ⊤ p q) :
    C.PushUp ∧ p ∈ C.Zplus ∧ C.Jminus ⊤ {q} \ C.Jminus ⊤ {p} ⊆ C.Jplus ⊤ {p} ∧
      (∀ r ∈ C.Jminus ⊤ {q} \ C.Jminus ⊤ {p}, C.Iminus ⊤ {r} = ∅) ∧
      C.Kplus ⊤ {p} ⊆ C.Iplus ⊤ {p} := by
  have hsub := segment_subset hmin hC hc hq hpq
  exact ⟨SFALocal.pushUp hmin hC, SFALocal.mem_Zplus hC p, fun r hr => (hsub hr).1.1,
    fun r hr => SFALocal.Iminus_eq_empty hmin hC r (hsub hr).2, (Kplus_eq_Iplus hmin hC p).subset⟩

/-- At a causal Hausdorff `E_{≥0}`-manifold with a BTZ point, the hypotheses of
`Causality.not_admissiblePast_and_admissibleFuture_of_pushUp` hold at some pair `p ≤ q`,
`p ≠ q`. -/
theorem exists_pushUp_obstruction [T2Space M] (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hc : C.IsCausal) (hS : (SFALocal.sing M 0).Nonempty) :
    ∃ p q : M, q ∈ SFALocal.sing M 0 ∧ C.le ⊤ p q ∧ p ≠ q ∧ C.PushUp ∧ p ∈ C.Zplus ∧
      C.Jminus ⊤ {q} \ C.Jminus ⊤ {p} ⊆ C.Jplus ⊤ {p} ∧
      (∀ r ∈ C.Jminus ⊤ {q} \ C.Jminus ⊤ {p}, C.Iminus ⊤ {r} = ∅) := by
  obtain ⟨p, hp⟩ := hS
  obtain ⟨q, hq, hpq, hne⟩ := exists_le_ne_of_mem_sing hC hc hp
  obtain ⟨hP, hZ, hline, hempty, -⟩ := pushUp_obstruction_hypotheses hmin hC hc hq hpq
  exact ⟨p, q, hq, hpq, hne, hP, hZ, hline, hempty⟩

end Unilaterale

/-! ### `theo:geroch_sing` at every `E_{≥0}`-manifold: the proved directions -/

section Geroch

variable {M : Type u} [TopologicalSpace M] [SingularGXStructure (Flat.isom 2) (Minkowski 2) M]
  {C : Causality M}

/-- A globally hyperbolic Hausdorff `E_{≥0}`-manifold is strongly causal
(`prop:GH_fortement_causal`; tarentin by `SFALocal.tarentin`). -/
theorem stronglyCausal_of_globallyHyperbolic [T2Space M]
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hG : C.GloballyHyperbolic) : C.StronglyCausal := by
  exact hG.stronglyCausal (SFALocal.tarentin hC)

/-- `theo:geroch_sing` (unmarked), **(i)⇒(ii), at every Hausdorff, second countable
`E_{≥0}`-manifold**: no hypothesis left. -/
theorem geroch_sing_i_imp_ii [T2Space M] [SecondCountableTopology M] (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hG : C.GloballyHyperbolic) :
    ∃ T : M → ℝ, C.IsCauchyTimeFunction T ∧ ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y := by
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  exact (SFAManifolds.singularFlatAxioms hmin hC).geroch_sing_i_imp_ii
    (MeasuresManifolds.massA_modelMeasures hmin hC (stronglyCausal_of_globallyHyperbolic hC hG)) hG

/-- `theo:geroch_sing` (unmarked), **(i)⇒(iii), at every Hausdorff, second countable
`E_{≥0}`-manifold**: no hypothesis left. -/
theorem geroch_sing_i_imp_iii [T2Space M] [SecondCountableTopology M] (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hG : C.GloballyHyperbolic) : ∃ S : Set M, C.IsCauchySurface S := by
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  exact (SFAManifolds.singularFlatAxioms hmin hC).geroch_sing_i_imp_iii
    (MeasuresManifolds.massA_modelMeasures hmin hC (stronglyCausal_of_globallyHyperbolic hC hG)) hG

/-- `theo:geroch_sing` (unmarked), **(ii)⇒(iii), at every strongly causal (DEC-18), Hausdorff,
second countable `E_{≥0}`-manifold** (`Causality.geroch_ii_imp_iii`). -/
theorem geroch_sing_ii_imp_iii [T2Space M] [SecondCountableTopology M]
    (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hSC : C.StronglyCausal)
    (h : ∃ T : M → ℝ, C.IsCauchyTimeFunction T ∧ ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y) :
    ∃ S : Set M, C.IsCauchySurface S := by
  have hSFA := SFAManifolds.singularFlatAxioms hmin hC
  exact Causality.geroch_ii_imp_iii hSFA.causallyArcConnected hSC hSFA.Jminus_ne_singleton
    hSFA.Jplus_ne_singleton h

/-- `theo:geroch_sing` (unmarked), **« Moreover », at every connected, causal, Hausdorff, second
countable `E_{≥0}`-manifold**: a Cauchy surface `Σ` gives `Σ × ℝ ≃ₜ M`, from the flow of
`lem:vecteur` (⚠ the named hypothesis `VecteurFlow C`, `Causal.SingularGeroch`). -/
theorem geroch_sing_split [T2Space M] [SecondCountableTopology M] [ConnectedSpace M]
    (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hc : C.IsCausal) (F : C.VecteurFlow) {S : Set M} (hS : C.IsCauchySurface S) :
    Nonempty (S × ℝ ≃ₜ M) := by
  exact Causality.SingularFlatAxioms.geroch_sing_split (SFAManifolds.singularFlatSpacetime hmin hC)
    hc F hS

/-- `theo:geroch_sing`, (i)⇒(ii), for the natural causality. -/
theorem geroch_sing_i_imp_ii_of_isAtlasCausalityDEC25 [T2Space M] [SecondCountableTopology M]
    (hcov : SFALocal.MassACovered M)
    (hC : IsAtlasCausalityDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hG : C.GloballyHyperbolic) :
    ∃ T : M → ℝ, C.IsCauchyTimeFunction T ∧ ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y := by
  exact geroch_sing_i_imp_ii (SFALocal.of_isAtlasCausalityDEC25 hcov hC).1
    (SFALocal.of_isAtlasCausalityDEC25 hcov hC).2 hG

/-- `theo:geroch_sing`, (i)⇒(iii), for the natural causality. -/
theorem geroch_sing_i_imp_iii_of_isAtlasCausalityDEC25 [T2Space M] [SecondCountableTopology M]
    (hcov : SFALocal.MassACovered M)
    (hC : IsAtlasCausalityDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hG : C.GloballyHyperbolic) : ∃ S : Set M, C.IsCauchySurface S := by
  exact geroch_sing_i_imp_iii (SFALocal.of_isAtlasCausalityDEC25 hcov hC).1
    (SFALocal.of_isAtlasCausalityDEC25 hcov hC).2 hG

end Geroch

/-! ### Witnesses (kb/0011): `E₀` and `E_π` -/

section WitnessE0

attribute [local instance] E0GX.singularGX

/-- **Non-vacuity of `rem:mesure_unilaterale` at `E₀`** (`sing₀ = axis ≠ ∅`): the hypotheses
hold, the one-sided measures exist and no measure has both, out of `mesure_unilaterale_sharp`. -/
theorem nonvacuous_e0_unilaterale :
    E0.causality.AbsolutelyMinimal ∧
      IsoChartsCoverDEC25 (Flat.isom 2) E0.causality (minkowski 2) massAModelCausality ∧
      E0.causality.StronglyCausal ∧ (SFALocal.sing E0 0).Nonempty ∧
      (∃ μ : Measure E0, E0.causality.AdmissiblePast μ) ∧
      (∃ μ : Measure E0, E0.causality.AdmissibleFuture μ) ∧
      ∀ μ : Measure E0, ¬ (E0.causality.AdmissiblePast μ ∧ E0.causality.AdmissibleFuture μ) := by
  obtain ⟨hmin, hC, -, hne⟩ := SFALocal.nonvacuous_e0
  obtain ⟨h1, h2, h3⟩ := mesure_unilaterale_sharp hmin hC E0.stronglyCausal hne
  exact ⟨hmin, hC, E0.stronglyCausal, hne, h1, h2, h3⟩

/-- **Non-vacuity of `rem:mesure_unilaterale_ptr` at `E₀`**: a pair `p ≤ q`, `p ≠ q` satisfying
every hypothesis of the strict `Causality.not_admissiblePast_and_admissibleFuture_of_pushUp`
(which had no witness) and of `not_admissible_both_of_chain`, with both conclusions. -/
theorem nonvacuous_e0_chain :
    ∃ p q : E0, E0.causality.PushUp ∧ p ∈ E0.causality.Zplus ∧ E0.causality.le ⊤ p q ∧ p ≠ q ∧
      E0.causality.Jminus ⊤ {q} \ E0.causality.Jminus ⊤ {p} ⊆ E0.causality.Jplus ⊤ {p} ∧
      (∀ r ∈ E0.causality.Jminus ⊤ {q} \ E0.causality.Jminus ⊤ {p},
        E0.causality.Iminus ⊤ {r} = ∅) ∧
      (∀ μ : Measure E0, ¬ (E0.causality.AdmissiblePast μ ∧ E0.causality.AdmissibleFuture μ)) ∧
      ∀ μ : Measure E0, ¬ (E0.causality.AdmissiblePast μ ∧ E0.causality.AdmissibleFuture μ) := by
  obtain ⟨hmin, hC, -, hne⟩ := SFALocal.nonvacuous_e0
  obtain ⟨p, q, -, hpq, hpq', hP, hZ, hline, hempty⟩ :=
    exists_pushUp_obstruction hmin hC E0.isCausal hne
  exact ⟨p, q, hP, hZ, hpq, hpq', hline, hempty,
    fun _ => Causality.not_admissiblePast_and_admissibleFuture_of_pushUp hP hZ hpq hpq' hline
      hempty,
    fun _ => not_admissible_both_of_chain hmin hC hpq hpq' hline hempty⟩

/-- **Non-vacuity of `theo:geroch_sing`'s directions at `E₀`**: globally hyperbolic, connected,
with every hypothesis of `geroch_sing`; (ii) out of `geroch_sing_i_imp_ii`, (iii) out of
`geroch_sing_ii_imp_iii`, strong causality out of `stronglyCausal_of_globallyHyperbolic`. -/
theorem nonvacuous_e0_geroch :
    E0.causality.AbsolutelyMinimal ∧
      IsoChartsCoverDEC25 (Flat.isom 2) E0.causality (minkowski 2) massAModelCausality ∧
      ConnectedSpace E0 ∧ E0.causality.GloballyHyperbolic ∧ E0.causality.StronglyCausal ∧
      (∃ T : E0 → ℝ, E0.causality.IsCauchyTimeFunction T ∧
        ∀ x y, E0.causality.le ⊤ x y → x ≠ y → T x < T y) ∧
      ∃ S : Set E0, E0.causality.IsCauchySurface S := by
  obtain ⟨hmin, hC, -, -⟩ := SFALocal.nonvacuous_e0
  have hSC := stronglyCausal_of_globallyHyperbolic hC E0.globallyHyperbolic
  have hii := geroch_sing_i_imp_ii hmin hC E0.globallyHyperbolic
  exact ⟨hmin, hC, inferInstance, E0.globallyHyperbolic, hSC, hii,
    geroch_sing_ii_imp_iii hmin hC hSC hii⟩

/-- **Non-vacuity of the natural forms at `E₀`**: `E₀` is an `E_{≥0}`-manifold whose natural
causality is `E0.causality`; the conclusions out of `mesure_unilaterale_of_isAtlasCausalityDEC25`,
`geroch_sing_i_imp_ii_of_isAtlasCausalityDEC25` and
`geroch_sing_i_imp_iii_of_isAtlasCausalityDEC25`. -/
theorem nonvacuous_e0_natural :
    SFALocal.MassACovered E0 ∧
      IsAtlasCausalityDEC25 (Flat.isom 2) E0.causality (minkowski 2) massAModelCausality ∧
      (SFALocal.sing E0 0).Nonempty ∧
      (∀ μ : Measure E0, ¬ (E0.causality.AdmissiblePast μ ∧ E0.causality.AdmissibleFuture μ)) ∧
      (∃ T : E0 → ℝ, E0.causality.IsCauchyTimeFunction T ∧
        ∀ x y, E0.causality.le ⊤ x y → x ≠ y → T x < T y) ∧
      ∃ S : Set E0, E0.causality.IsCauchySurface S := by
  obtain ⟨-, hcov, hC, -⟩ := EModelsBPrime.massA_dec25_models_e0_sing
  obtain ⟨-, -, -, hne⟩ := SFALocal.nonvacuous_e0
  exact ⟨hcov, hC, hne, mesure_unilaterale_of_isAtlasCausalityDEC25 hcov hC hne,
    geroch_sing_i_imp_ii_of_isAtlasCausalityDEC25 hcov hC E0.globallyHyperbolic,
    geroch_sing_i_imp_iii_of_isAtlasCausalityDEC25 hcov hC E0.globallyHyperbolic⟩

end WitnessE0

section WitnessEPi

attribute [local instance] EAlphaGX.singularGX EAlphaGX.fact_pi_pos

/-- **The BTZ point cannot be dropped from `rem:mesure_unilaterale`**: `E_π` has no BTZ point
and carries a measure admissible in the past and in the future at once
(`MeasuresEAlpha.exists_admissible_past_future`). -/
theorem epi_admissible_both :
    SFALocal.sing (Massive Real.pi) 0 = ∅ ∧
      ∃ μ : Measure (Massive Real.pi),
        (massive Real.pi).AdmissiblePast μ ∧ (massive Real.pi).AdmissibleFuture μ := by
  obtain ⟨-, -, -, -, h0⟩ := SFALocal.nonvacuous_epi
  exact ⟨h0, MeasuresEAlpha.exists_admissible_past_future⟩

/-- **Non-vacuity of `theo:geroch_sing`'s directions at `E_π`** (a massive line): (ii), (iii)
out of `geroch_sing_i_imp_ii`, `geroch_sing_i_imp_iii`. -/
theorem nonvacuous_epi_geroch :
    (massive Real.pi).AbsolutelyMinimal ∧
      IsoChartsCoverDEC25 (Flat.isom 2) (massive Real.pi) (minkowski 2) massAModelCausality ∧
      ConnectedSpace (Massive Real.pi) ∧ (massive Real.pi).GloballyHyperbolic ∧
      (∃ T : Massive Real.pi → ℝ, (massive Real.pi).IsCauchyTimeFunction T ∧
        ∀ x y, (massive Real.pi).le ⊤ x y → x ≠ y → T x < T y) ∧
      ∃ S : Set (Massive Real.pi), (massive Real.pi).IsCauchySurface S := by
  obtain ⟨hmin, hC, -⟩ := SFALocal.nonvacuous_epi
  exact ⟨hmin, hC, SFAManifolds.massive_connectedSpace Real.pi, massive_globallyHyperbolic,
    geroch_sing_i_imp_ii hmin hC massive_globallyHyperbolic,
    geroch_sing_i_imp_iii hmin hC massive_globallyHyperbolic⟩

end WitnessEPi

end SingularRowsGeroch

end Causal
