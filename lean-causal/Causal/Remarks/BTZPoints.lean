import Causal.SingularFlat
import Causal.MeasureRemarks
import Causal.Flat.Achronal

/-!
# Remarks on BTZ points: `≪` not reflexive, causal plainness, strongly tarentin points, and the
two senses of admissibility

Target `T-ett-unanchored` (2026-11-20). No label is marked: each remark speaks of BTZ points of
`E^{1,2}_{≥0}`-manifolds, read under DEC-25 over the model `E₀` (`Causal.E0`; OQ-18, OQ-34,
OQ-35, OQ-82), or of Lorentzian manifolds, which the library does not have. The BTZ facts enter through the fields of
`SingularFlatAxioms` / `BTZAxioms` (`Causal.SingularFlat`, kb/0012); Minkowski space stands for the
Lorentzian side where an instance is meant. Cited, unmarked:
`rem:relation_not_assumed_reflexive` — `ETT.tex:235`, `rem:pas_plat` — `ETT.tex:289`,
`rem:lorentz_tarentin` — `ETT.tex:783`, `rem:mesure_unilaterale` — `ETT.tex:1713`.

> The relation $\tlleq$ is \emph{not} assumed reflexive: no point of Minkowski space lies in its
> own chronological future, and a BTZ point has empty chronological past (Definition
> \ref{defi:causal_E0}). (`ETT.tex:235`)

> This is the \emph{push-up} property, and it fails in the two families of spacetimes this work
> exists to cover. [...] (i) \emph{Low regularity.} [...] a \emph{causal bubble} is by definition
> a non-empty open subset of $J^+(p)$ disjoint from $I^+(p)$ --- an explicit violation of
> Definition \ref{defi:causalement_plat}. [...] (ii) \emph{Singularities.} At a BTZ point $p$ of a
> $\mass{\geq0}$-manifold, $I^-(p)=\emptyset$ while $J^-(p)$ is the singular half-line below $p$
> (Definition \ref{defi:causal_E0}). This is the degenerate case of the same defect: causal past without chronological past.
> (`ETT.tex:290–295`)

> Every point of a Lorentzian manifold is strongly tarentin in the future and in the past. The
> notion only becomes discriminating on singular or low-regularity spacetimes: on a
> $\mass{\geq0}$-manifold the points which fail to be strongly tarentin in the past are exactly
> the BTZ points. (`ETT.tex:784–787`)

> Let $M$ be a causal $\mass{\geq0}$-manifold and let $p<q$ be two BTZ points of one singular line
> $\Delta$. By Definition \ref{defi:causal_E0} the set $J^-(q)\setminus J^-(p)$ is the segment
> $]p,q]$ of $\Delta$ [...] No measure on $M$ is therefore admissible in the past and in the
> future at once. (`ETT.tex:1716–1723`)

## What is proved (no `sorry` in this file)

* `rem:relation_not_assumed_reflexive`: `Flat.minkowski_not_lt_self` (`Causal.Flat.Achronal`,
  reused, every dimension), `BTZAxioms.not_lt_self`; assembly `relation_not_assumed_reflexive`.
* `rem:pas_plat`: (i) `IsCausalBubble.not_causallyPlain` (past: `…_past`), witnessed on the
  lightlike line (`lightlikeLine_isCausalBubble`); (ii) `SingularFlatAxioms.btz_past` (`I^-(p) = ∅`
  and `J^-(p)` the half-line `γ(]-∞,0])` of the BTZ line through `p`). **Finding**:
  `SingularFlatAxioms.interior_Jminus_eq_empty`, `.btz_causallyPlain_past` — at BTZ points the
  inclusion of `defi:causalement_plat` holds, trivially (SCOPE).
* `rem:lorentz_tarentin`: `Zplus_Zminus_eq_univ` (absolutely minimal, every `I^±(p) ≠ ∅`),
  `minkowski_Z_eq_univ`, `SingularFlatAxioms.Z_eq`; assembly `lorentz_tarentin`.
* `rem:mesure_unilaterale`: `SingularFlatAxioms.Jminus_diff_eq_segment` (`J^-(q) ∖ J^-(p)` is the
  segment `γ(]t₀,0]) = ]p,q]`), `.not_admissible_both_of_le` (any `p ≤ q`, `p ≠ q`, `q` BTZ),
  `.mesure_unilaterale` (`sing_0 ≠ ∅` suffices).

## Hypothesis checklist

| paper | here |
|---|---|
| Minkowski space | ✓ `minkowski n`, every `n` |
| BTZ point, `E_{≥0}`-manifold (`defi:causal_E0`) | ⚠ strengthened: `BTZAxioms C S₀` / `SingularFlatAxioms C sing` (named model facts; at `E₀`, `Causal.E0.singularFlatAxioms`; at every Hausdorff, second countable `E_{≥0}`-manifold, `Causal.SFAManifolds.singularFlatAxioms`) |
| `rem:pas_plat` (ii): `M` causal | ⚠ strengthened: `btz_past` asks `IsCausal` (the BTZ line a closed embedding, so `J^-(p)` is the image of `]-∞,0]`); the finding `interior_Jminus_eq_empty` does not |
| Lorentzian manifold (`rem:lorentz_tarentin`) | ⚠ strengthened: an absolutely minimal T1 spacetime with `I^±(p) ≠ ∅` everywhere; instance: `minkowski n` |
| `rem:mesure_unilaterale`: `M` causal | ✓ carried |
| — `p < q` two BTZ points of one singular line | ⚠ weakened: `p ≤ q`, `p ≠ q`, `q` BTZ (then `p` is BTZ and on the line of `q`); or only `sing_0 ≠ ∅` |

## SCOPE (disclosed)

* **Finding on `rem:pas_plat` (ii).** A BTZ point does not violate `defi:causalement_plat`.
  `J^-(p) ⊂ sing_0` (`lem:past_BTZ`) and `sing_0` has empty interior (`prop:GX_sing_dec`), so
  `Int J^-(p) = ∅ ⊂ closure I^-(p)`; more generally `Int J^-_U(A) = ∅` for every `A ⊂ sing_0` and
  every open `U` (`interior_Jminus_eq_empty`). "Causal past without chronological past" at a BTZ
  point is a set without interior, about which causal plainness is silent — as
  `rem:deux_pushup` (`ETT.tex:318–320`) itself says. Whether an `E_{≥0}`-manifold is causally plain
  at all is not established in the paper (OQ-16), so the sentence "it fails in the two families"
  (`ETT.tex:290`) is supported for (i) only. The remark's first words, "This is the push-up
  property", name `defi:causalement_plat`; the relational push-up of `defi:pushup` *does* hold on
  `E_{≥0}`-manifolds (`cor:pushup_sing`; the field `pushUp`).
* `rem:pas_plat` (i): the causal bubbles of Chruściel–Grant and Sämann (continuous metrics) are not
  built; what is proved is the sentence "a causal bubble is an explicit violation of
  `defi:causalement_plat`", for any open `U` and any `A` (`IsCausalBubble`). The last sentence of
  the remark (`K^±` agrees with `I^±` where push-up holds) is `PushUp.Kminus_eq_Iminus`
  (`Causal.PushUp`), not restated.
* `rem:lorentz_tarentin`: Lorentzian manifolds are not in the library; the first sentence is proved
  for every absolutely minimal T1 spacetime whose chronological futures and pasts are non-empty
  (`rem:absolutely_minimal_topological_spacetime` does the work), and for Minkowski space. "Only
  becomes discriminating" is prose.
* `rem:mesure_unilaterale`: the paper's "`r ∉ I^+(p) = K^+(p)` by `prop:K_calcul`" is used in the
  form `K^+(p) = I^+(p)` from push-up and `p ∈ Z^+` (`PushUp.Kplus_eq_Iplus`, `prop:K_calcul` (b));
  the segment is computed from the field `line` (`lem:past_BTZ` (a)) and causality. The full
  `SingularFlatAxioms` with `sing_0 ≠ ∅` has the witness `E₀`, where these two theorems are
  instantiated with a BTZ point (`Causal.E0.mesure_unilaterale`, through
  `SingularFlatAxioms.mesure_unilaterale`); the general obstruction
  `not_admissiblePast_and_admissibleFuture` is (`pointedLineMR_not_admissible`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter MeasureTheory

universe u

/-! ### `rem:relation_not_assumed_reflexive` -/

namespace Causality

variable {M : Type u} [TopologicalSpace M] {C : Causality M} {p q : M}

/-- A BTZ point is not in its own chronological past: `I^-(p) = ∅`. -/
theorem BTZAxioms.not_lt_self {S₀ : Set M} (h : C.BTZAxioms S₀) (hp : p ∈ S₀) :
    ¬ C.lt ⊤ p p := by
  intro hpp
  have hmem : p ∈ C.Iminus ⊤ {p} := by simpa using hpp
  rw [h.Iminus_eq_empty p hp] at hmem
  exact hmem

end Causality

/-- `rem:relation_not_assumed_reflexive`, assembled: `≪` is not reflexive on Minkowski space
(every dimension), and a BTZ point has empty chronological past, hence is not `≪` itself. The BTZ
half is the field `Iminus_eq_empty` of `BTZAxioms` (kb/0012). -/
theorem relation_not_assumed_reflexive :
    (∀ (n : ℕ) (p : Minkowski n), ¬ (minkowski n).lt ⊤ p p) ∧
    (∀ {M : Type u} [TopologicalSpace M] (C : Causality M) (S₀ : Set M), C.BTZAxioms S₀ →
      ∀ p ∈ S₀, C.Iminus ⊤ {p} = ∅ ∧ ¬ C.lt ⊤ p p) :=
  ⟨fun _ p => Flat.minkowski_not_lt_self p, fun _ _ h p hp => ⟨h.Iminus_eq_empty p hp, h.not_lt_self hp⟩⟩

/-! ### `rem:pas_plat` -/

namespace Causality

variable {M : Type u} [TopologicalSpace M] {C : Causality M} {p q : M}

/-- A **causal bubble** of `J^+_U(A)` (`ETT.tex:293`, with `U = M`, `A = {p}`): a non-empty open
subset of `J^+_U(A)` disjoint from `I^+_U(A)`. -/
def IsCausalBubble (C : Causality M) (U : Opens M) (A B : Set M) : Prop :=
  IsOpen B ∧ B.Nonempty ∧ B ⊆ C.Jplus U A ∧ Disjoint B (C.Iplus U A)

/-- `rem:pas_plat` (i): a causal bubble is a violation of `defi:causalement_plat`. -/
theorem IsCausalBubble.not_causallyPlain {U : Opens M} {A B : Set M}
    (h : C.IsCausalBubble U A B) : ¬ C.CausallyPlain := by
  intro hP
  obtain ⟨hB, ⟨x, hx⟩, hBJ, hdisj⟩ := h
  have hxint : x ∈ interior (C.Jplus U A) := interior_maximal hBJ hB hx
  have hxcl := (hP U A).1 hxint
  obtain ⟨y, hyB, hyI⟩ := mem_closure_iff.1 hxcl B hB hx
  exact Set.disjoint_left.1 hdisj hyB hyI

/-- `rem:pas_plat` (i), in the past: a bubble of `J^-_U(A)` (a bubble of the time-reversed
causality) is a violation of `defi:causalement_plat`. -/
theorem IsCausalBubble.not_causallyPlain_past {U : Opens M} {A B : Set M}
    (h : C.dual.IsCausalBubble U A B) : ¬ C.CausallyPlain := fun hP =>
  h.not_causallyPlain (dual_causallyPlain.2 hP)

variable {sing : ℝ → Set M}

/-- `rem:pas_plat` (ii): at a BTZ point of a causal `E_{≥0}`-manifold, `I^-(p) = ∅` and `J^-(p)` is
the half-line below `p` of the BTZ line through `p`. -/
theorem SingularFlatAxioms.btz_past (h : C.SingularFlatAxioms sing) (hc : C.IsCausal)
    (hp : p ∈ sing 0) :
    C.Iminus ⊤ {p} = ∅ ∧ ∃ γ : ℝ → M, γ 0 = p ∧ IsClosedEmbedding γ ∧ range γ ⊆ sing 0 ∧
      C.Jminus ⊤ {p} = γ '' Iic 0 := by
  obtain ⟨γ, hγ0, hγ, hγi, hγr⟩ := h.line p hp
  refine ⟨h.Iminus_eq_empty p hp, γ, hγ0, hγ hc, ?_, h.Jminus_eq_image hc hp hγ0 (hγ hc) hγi.1 hγr⟩
  rw [hγr]
  exact connectedComponentIn_subset _ _

/-- **Finding on `rem:pas_plat` (ii).** The causal past, in any open set, of a set of BTZ points
has empty interior: it lies in `sing_0`, which has none. -/
theorem SingularFlatAxioms.interior_Jminus_eq_empty (h : C.SingularFlatAxioms sing)
    {U : Opens M} {A : Set M} (hA : A ⊆ sing 0) : interior (C.Jminus U A) = ∅ := by
  have hsub : C.Jminus U A ⊆ sing 0 := by
    rintro y ⟨x, hxA, hyx⟩
    exact h.mem_sing_zero_of_le (hA hxA) (C.le_mono le_top hyx)
  exact subset_empty_iff.1 ((interior_mono hsub).trans (h.interior_sing 0 le_rfl).subset)

/-- **Finding on `rem:pas_plat` (ii).** At BTZ points the past inclusion of
`defi:causalement_plat` holds: `Int J^-_U(A) ⊂ closure I^-_U(A)` for every `A ⊂ sing_0`. The BTZ
defect "causal past without chronological past" is not a violation of causal plainness. -/
theorem SingularFlatAxioms.btz_causallyPlain_past (h : C.SingularFlatAxioms sing)
    {U : Opens M} {A : Set M} (hA : A ⊆ sing 0) :
    interior (C.Jminus U A) ⊆ closure (C.Iminus U A) := by
  rw [h.interior_Jminus_eq_empty hA]
  exact empty_subset _

end Causality

/-- **Witness of `IsCausalBubble`**: `]0, +∞[` is a causal bubble of `J^+(0)` on the lightlike
line (`ex:causalities_lines`, item 2). -/
theorem lightlikeLine_isCausalBubble : lightlikeLine.IsCausalBubble ⊤ {0} (Ioi 0) := by
  refine ⟨isOpen_Ioi, ⟨1, mem_Ioi.2 one_pos⟩, ?_, ?_⟩
  · intro z hz
    have hz' : (0 : ℝ) ≤ z := le_of_lt hz
    simp [hz']
  · rw [lightlikeLine_interior_Jplus_zero.2]
    exact disjoint_empty _

/-! ### `rem:lorentz_tarentin` -/

namespace Causality

variable {M : Type u} [TopologicalSpace M] {C : Causality M} {p q : M}

/-- `rem:lorentz_tarentin`, first sentence, abstractly: in an absolutely minimal T1 spacetime in
which every point has a non-empty chronological future and past, every point is strongly
tarentin in the future and in the past. -/
theorem Zplus_Zminus_eq_univ [T1Space M] (hA : C.AbsolutelyMinimal)
    (hI : ∀ p, (C.Iplus ⊤ {p}).Nonempty ∧ (C.Iminus ⊤ {p}).Nonempty) :
    C.Zplus = univ ∧ C.Zminus = univ :=
  ⟨eq_univ_of_forall fun p => (AbsolutelyMinimal.mem_Zplus_iff hA).2 (hI p).1,
    eq_univ_of_forall fun p => (AbsolutelyMinimal.mem_Zminus_iff hA).2 (hI p).2⟩

/-- `rem:lorentz_tarentin`, second sentence, for the structure: every point is strongly tarentin
in the future, and the points not strongly tarentin in the past are the BTZ points (the fields
`mem_Zplus`, `mem_Zminus_iff`, i.e. `rem:btz_pas_tarentin`). -/
theorem SingularFlatAxioms.Z_eq {sing : ℝ → Set M} (h : C.SingularFlatAxioms sing) :
    C.Zplus = univ ∧ C.Zminus = (sing 0)ᶜ :=
  ⟨eq_univ_of_forall h.mem_Zplus, Set.ext h.mem_Zminus_iff⟩

end Causality

/-- `rem:lorentz_tarentin` on Minkowski space: every point is strongly tarentin both ways, by the
abstract form (`Zplus_Zminus_eq_univ`). -/
theorem minkowski_Z_eq_univ (n : ℕ) :
    (minkowski n).Zplus = univ ∧ (minkowski n).Zminus = univ := by
  refine Causality.Zplus_Zminus_eq_univ minkowski_absolutelyMinimal fun p => ⟨?_, ?_⟩
  · exact ⟨(p.1 + 1, p.2), by rw [Precausality.mem_Iplus_singleton, minkowski_lt_top_iff]; simp⟩
  · exact ⟨(p.1 - 1, p.2), by rw [Precausality.mem_Iminus_singleton, minkowski_lt_top_iff]; simp⟩

/-- `rem:lorentz_tarentin`, assembled: Minkowski space (every dimension) has `Z^± = M`; on an
`E_{≥0}`-manifold (the structure) `Z^+ = M` and `Z^- = M ∖ sing_0`. -/
theorem lorentz_tarentin :
    (∀ n : ℕ, (minkowski n).Zplus = univ ∧ (minkowski n).Zminus = univ) ∧
    (∀ {M : Type u} [TopologicalSpace M] (C : Causality M) (sing : ℝ → Set M),
      C.SingularFlatAxioms sing → C.Zplus = univ ∧ C.Zminus = (sing 0)ᶜ) :=
  ⟨minkowski_Z_eq_univ, fun _ _ h => h.Z_eq⟩

/-! ### `rem:mesure_unilaterale` -/

namespace Causality

variable {M : Type u} [TopologicalSpace M] {C : Causality M} {p q : M} {sing : ℝ → Set M}

namespace SingularFlatAxioms

/-- `rem:mesure_unilaterale`, first step: in a causal `E_{≥0}`-manifold, for a BTZ point `q` and
`p ≤ q`, `J^-(q) ∖ J^-(p)` is the segment `]p, q]` of the BTZ line `γ` through `q`
(`γ 0 = q`, `γ t₀ = p`). -/
theorem Jminus_diff_eq_segment (h : C.SingularFlatAxioms sing) (hc : C.IsCausal)
    (hq : q ∈ sing 0) (hpq : C.le ⊤ p q) :
    ∃ γ : ℝ → M, ∃ t₀ : ℝ, γ 0 = q ∧ γ t₀ = p ∧ t₀ ≤ 0 ∧ IsClosedEmbedding γ ∧
      C.CausalCurveIn ⊤ univ γ ∧ range γ ⊆ sing 0 ∧
      C.Jminus ⊤ {q} \ C.Jminus ⊤ {p} = γ '' Ioc t₀ 0 := by
  obtain ⟨γ, hγ0, hγ, hγi, hγr⟩ := h.line q hq
  have hemb := hγ hc
  have hγc : C.CausalCurveIn ⊤ univ γ := hγi.1
  have hJq := h.Jminus_eq_image hc hq hγ0 hemb hγc hγr
  have hpJ : p ∈ C.Jminus ⊤ {q} := by simpa using hpq
  rw [hJq] at hpJ
  obtain ⟨t₀, ht₀, rfl⟩ := hpJ
  have hrange : range γ ⊆ sing 0 := by
    rw [hγr]
    exact connectedComponentIn_subset _ _
  refine ⟨γ, t₀, hγ0, rfl, ht₀, hemb, hγc, hrange, ?_⟩
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

/-- `rem:mesure_unilaterale`: in a causal `E_{≥0}`-manifold, a BTZ point `q` and a point `p ≤ q`,
`p ≠ q`, forbid any measure admissible in the past and in the future at once. -/
theorem not_admissible_both_of_le [MeasurableSpace M] (h : C.SingularFlatAxioms sing)
    (hc : C.IsCausal) {μ : Measure M} (hq : q ∈ sing 0) (hpq : C.le ⊤ p q) (hne : p ≠ q) :
    ¬ (C.AdmissiblePast μ ∧ C.AdmissibleFuture μ) := by
  haveI := h.secondCountable
  obtain ⟨γ, t₀, -, hγt, -, -, hγc, -, hseg⟩ := h.Jminus_diff_eq_segment hc hq hpq
  refine not_admissiblePast_and_admissibleFuture_of_pushUp h.pushUp (h.mem_Zplus p) hpq hne
    ?_ ?_
  · rw [hseg]
    rintro _ ⟨s, ⟨hts, -⟩, rfl⟩
    have hle := hγc.le_of_le trivial trivial hts.le
    rw [hγt] at hle
    simpa using hle
  · intro r hr
    exact h.Iminus_eq_empty r (h.mem_sing_zero_of_le hq (by simpa using hr.1))

/-- `rem:mesure_unilaterale`: a causal `E_{≥0}`-manifold with a BTZ point carries no measure
admissible in the past and in the future at once. -/
theorem mesure_unilaterale [MeasurableSpace M] (h : C.SingularFlatAxioms sing) (hc : C.IsCausal)
    (hS : (sing 0).Nonempty) (μ : Measure M) :
    ¬ (C.AdmissiblePast μ ∧ C.AdmissibleFuture μ) := by
  obtain ⟨p, hp⟩ := hS
  obtain ⟨γ, hγ0, hγ, hγi, hγr⟩ := h.line p hp
  have hemb := hγ hc
  have h1 : γ 1 ∈ sing 0 := by
    have hmem : γ 1 ∈ range γ := mem_range_self 1
    rw [hγr] at hmem
    exact connectedComponentIn_subset _ _ hmem
  have hle : C.le ⊤ p (γ 1) := by
    have h01 := hγi.1.le_of_le trivial trivial zero_le_one
    rwa [hγ0] at h01
  have hne : p ≠ γ 1 := by
    intro heq
    rw [← hγ0] at heq
    exact zero_ne_one (hemb.injective heq)
  exact h.not_admissible_both_of_le hc h1 hle hne

end SingularFlatAxioms

end Causality

end Causal
