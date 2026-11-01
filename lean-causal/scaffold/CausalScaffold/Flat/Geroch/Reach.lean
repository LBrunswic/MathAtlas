import CausalScaffold.Flat.CauchyComplete
import Causal.PushUp
import Causal.LinesReachable
import Causal.GlobalHyperbolicity

/-!
# `CausalScaffold.Flat.Geroch.Reach` — `K^± = I^±` on every flat spacetime, and the two sets an admissible measure must see

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257);
infrastructure for `FlatAdmissibleMeasures` (`Flat/TheoremBInputs.lean`, ruling DEC-65). **No label
is marked.** This is the flat-spacetime version of what `Causal/Static.lean` proves for `𝐌ⁿ`
(`staticCausality.Kminus_eq_Iminus`, `Jminus_diff_Kminus_subset_frontier`,
`exists_isOpen_subset_Jminus_diff`): the "checks easily" of `prop:mesure_dieckmann_Lorentz`
(ETT.tex:1054) made explicit for `flatCausality`.

> Since $M$ is strongly causal and Lorentzian, the Alexandrov topology is the manifold topology of
> $M$ and diamonds always have non-empty interior. One then checks easily that conditions $3.$ and
> $4.$ hold for a measure admissible in the sense of Dieckmann. (ETT.tex, proof of
> `prop:mesure_dieckmann_Lorentz`)

* `flatCausality_pushUp`: push-up (`defi:pushup`) on every flat spacetime — locally through the
  charts (Minkowski push-up, `staticCausality.pushUpOn`, carried by `ChartIso`), then globally by
  `CausallyArcConnected.pushUp` (`lem:pushup_local`) over the cover by chart sources.
* `flatCausality_mem_Zminus`, `flatCausality_mem_Zplus`: every point is strongly tarentin
  (`AbsolutelyMinimal.mem_Zminus_iff` and a chronological past point in a chart).
* `flatCausality_Kminus_eq_Iminus`, `flatCausality_Kplus_eq_Iplus`: `K^±(A) = I^±(A)` for **every**
  `A` (`PushUp.Kminus_eq_Iminus` pointwise, `Kminus_eq_biUnion`).
* `flatCausality_Jminus_subset_closure_Iminus`, `…_Jplus_subset_closure_Iplus`:
  `J^±(A) ⊆ closure I^±(A)` (`Jminus_subset_closure_Iminus_of_pushUp` pointwise).
* `flatCausality_Jminus_diff_Kminus_subset_frontier`, `…_Jplus_diff_Kplus_…`: property 4.'s set
  lies in the frontier of the open set `I^±(A)`.
* `flatCausality_exists_isOpen_subset_Jminus_diff`, `…_Jplus_diff`: under GH (and tarentin,
  carried — it is `flatCausality_tarentin`, proved in `TheoremBInputs`, not importable here),
  property 3.'s set contains a non-empty open set.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `M` strongly causal Lorentzian | ⚠ replaced: `M` a flat spacetime (`FlatSpacetime d`); GH only for property 3. |
| "diamonds have non-empty interior" (property 3.) | ✓ carried as: `J^-(p)` closed (GH + tarentin), `q ∈ closure I^-(q)`, causality |
| tarentin | ✓ carried as a hypothesis `hT` (it holds: `flatCausality_tarentin`) |

## SCOPE (disclosed)

* Model-free inputs (push-up, `Z^± = M`, first countability) are proved here for `flatCausality`;
  nothing about measures is in this file.
* `A` is arbitrary: `A = ∅` gives `∅ ⊆ …`; `A = univ` gives `I^-(univ) = univ` (every point has a
  chronological future point), frontier `∅`, and `J^-(univ) ∖ K^-(univ) = ∅`, consistently.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
DEC-65.
-/

namespace Causal.Flat

open Set TopologicalSpace Topology Filter Causality

universe u

variable {d : ℕ}

section Reach

variable {N : FlatSpacetime.{u} d}

/-- **Push-up on every flat spacetime** (`defi:pushup`): in a chart it is Minkowski push-up, and
`lem:pushup_local` globalises it over the cover by chart sources. -/
theorem flatCausality_pushUp : (flatCausality d N).PushUp := by
  refine Causality.CausallyArcConnected.pushUp (flatCausality_causallyArcConnected d N)
    (O := fun x : N => chartSource (chartAt (Minkowski d) x))
    (fun x => ⟨x, mem_chart_source _ x⟩) (fun x => ?_)
  have hiso : ChartIso (flatCausality d N) (minkowski d) (chartAt (Minkowski d) x) :=
    flatCausality_chartIso_chartAt x
  intro U hU a b c
  have hM := staticCausality.pushUpOn (X := EuclideanSpace ℝ (Fin d))
    (chartImage (chartAt (Minkowski d) x) U) (chartImage (chartAt (Minkowski d) x) U) le_rfl
  constructor
  · intro h₁ h₂
    have ha := (flatCausality d N).lt_mem_left h₁
    have hb := (flatCausality d N).lt_mem_right h₁
    have hc := (flatCausality d N).le_mem_right h₂
    exact (hiso U hU a ha c hc).2.2
      (hM.1 ((hiso U hU a ha b hb).2.1 h₁) ((hiso U hU b hb c hc).1.1 h₂))
  · intro h₁ h₂
    have ha := (flatCausality d N).le_mem_left h₁
    have hb := (flatCausality d N).le_mem_right h₁
    have hc := (flatCausality d N).lt_mem_right h₂
    exact (hiso U hU a ha c hc).2.2
      (hM.2 ((hiso U hU a ha b hb).1.1 h₁) ((hiso U hU b hb c hc).2.1 h₂))

/-- **Every point of a flat spacetime is strongly tarentin in the past** (`p ∈ Z^-`). -/
theorem flatCausality_mem_Zminus (p : N) : p ∈ (flatCausality d N).Zminus := by
  rw [Causality.AbsolutelyMinimal.mem_Zminus_iff flatCausality_absolutelyMinimal]
  set e := chartAt (Minkowski d) p with he
  have hiso : ChartIso (flatCausality d N) (minkowski d) e := flatCausality_chartIso_chartAt p
  have hps : p ∈ e.source := mem_chart_source _ p
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 e.open_target (e p) (e.map_source hps)
  let U : Opens N := ⟨e.source ∩ e ⁻¹' Metric.ball (e p) ε,
    e.continuousOn.isOpen_inter_preimage e.open_source Metric.isOpen_ball⟩
  have hU : U ≤ chartSource e := fun z hz => hz.1
  have himg : ∀ w : Minkowski d, w ∈ chartImage e U ↔ w ∈ Metric.ball (e p) ε := by
    intro w
    constructor
    · rintro ⟨z, ⟨-, -, hz⟩, rfl⟩
      exact hz
    · intro hw
      refine ⟨e.symm w, ⟨e.map_target (hball hw), e.map_target (hball hw), ?_⟩,
        e.right_inv (hball hw)⟩
      show e (e.symm w) ∈ Metric.ball (e p) ε
      rwa [e.right_inv (hball hw)]
  have hconv : Convex ℝ (chartImage e U : Set (Minkowski d)) := by
    have : (chartImage e U : Set (Minkowski d)) = Metric.ball (e p) ε := Set.ext himg
    rw [this]; exact convex_ball _ _
  set w : Minkowski d := ((e p).1 - ε / 2, (e p).2) with hw
  have hwb : w ∈ Metric.ball (e p) ε := by
    rw [Metric.mem_ball, hw, Prod.dist_eq, dist_self, Real.dist_eq]
    have : |(e p).1 - ε / 2 - (e p).1| = ε / 2 := by
      rw [show (e p).1 - ε / 2 - (e p).1 = -(ε / 2) by ring]
      rw [abs_neg]; exact abs_of_pos (by linarith)
    rw [this, max_eq_left (by linarith)]; linarith
  have hwt : w ∈ e.target := hball hwb
  have hpU : p ∈ U := ⟨hps, Metric.mem_ball_self hε⟩
  have hzU : e.symm w ∈ U := (himg w).2 hwb |> fun h => by
    obtain ⟨z, ⟨hz, hzU⟩, hzw⟩ := h
    rw [← hzw, e.left_inv hz]; exact hzU
  have hlt : (minkowski d).lt (chartImage e U) w (e p) := by
    refine (lt_iff_of_convex hconv).2 ⟨?_, ?_, minkowski_lt_top_iff.2 ?_⟩
    all_goals first
      | exact (himg _).2 hwb
      | exact (himg _).2 (Metric.mem_ball_self hε)
      | (rw [hw]; simp only [sub_self, norm_zero]; linarith)
  have hlt' := (hiso U hU (e.symm w) hzU p hpU).2.2
    (by rwa [e.right_inv hwt])
  exact ⟨e.symm w, p, rfl, (flatCausality d N).lt_mono le_top hlt'⟩

/-- **Every point of a flat spacetime is strongly tarentin in the future** (`p ∈ Z^+`). -/
theorem flatCausality_mem_Zplus (p : N) : p ∈ (flatCausality d N).Zplus := by
  rw [Causality.AbsolutelyMinimal.mem_Zplus_iff flatCausality_absolutelyMinimal]
  set e := chartAt (Minkowski d) p with he
  have hiso : ChartIso (flatCausality d N) (minkowski d) e := flatCausality_chartIso_chartAt p
  have hps : p ∈ e.source := mem_chart_source _ p
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 e.open_target (e p) (e.map_source hps)
  let U : Opens N := ⟨e.source ∩ e ⁻¹' Metric.ball (e p) ε,
    e.continuousOn.isOpen_inter_preimage e.open_source Metric.isOpen_ball⟩
  have hU : U ≤ chartSource e := fun z hz => hz.1
  have himg : ∀ w : Minkowski d, w ∈ chartImage e U ↔ w ∈ Metric.ball (e p) ε := by
    intro w
    constructor
    · rintro ⟨z, ⟨-, -, hz⟩, rfl⟩
      exact hz
    · intro hw
      refine ⟨e.symm w, ⟨e.map_target (hball hw), e.map_target (hball hw), ?_⟩,
        e.right_inv (hball hw)⟩
      show e (e.symm w) ∈ Metric.ball (e p) ε
      rwa [e.right_inv (hball hw)]
  have hconv : Convex ℝ (chartImage e U : Set (Minkowski d)) := by
    have : (chartImage e U : Set (Minkowski d)) = Metric.ball (e p) ε := Set.ext himg
    rw [this]; exact convex_ball _ _
  set w : Minkowski d := ((e p).1 + ε / 2, (e p).2) with hw
  have hwb : w ∈ Metric.ball (e p) ε := by
    rw [Metric.mem_ball, hw, Prod.dist_eq, dist_self, Real.dist_eq]
    have : |(e p).1 + ε / 2 - (e p).1| = ε / 2 := by
      rw [show (e p).1 + ε / 2 - (e p).1 = (ε / 2) by ring]
      exact abs_of_pos (by linarith)
    rw [this, max_eq_left (by linarith)]; linarith
  have hwt : w ∈ e.target := hball hwb
  have hpU : p ∈ U := ⟨hps, Metric.mem_ball_self hε⟩
  have hzU : e.symm w ∈ U := (himg w).2 hwb |> fun h => by
    obtain ⟨z, ⟨hz, hzU⟩, hzw⟩ := h
    rw [← hzw, e.left_inv hz]; exact hzU
  have hlt : (minkowski d).lt (chartImage e U) (e p) w := by
    refine (lt_iff_of_convex hconv).2 ⟨?_, ?_, minkowski_lt_top_iff.2 ?_⟩
    all_goals first
      | exact (himg _).2 hwb
      | exact (himg _).2 (Metric.mem_ball_self hε)
      | (rw [hw]; simp only [sub_self, norm_zero]; linarith)
  have hlt' := (hiso U hU p hpU (e.symm w) hzU).2.2
    (by rwa [e.right_inv hwt])
  exact ⟨e.symm w, p, rfl, (flatCausality d N).lt_mono le_top hlt'⟩

/-- **`K^-(A) = I^-(A)` for every `A`** on a flat spacetime. -/
theorem flatCausality_Kminus_eq_Iminus (A : Set N) :
    (flatCausality d N).Kminus ⊤ A = (flatCausality d N).Iminus ⊤ A := by
  rw [Causality.Kminus_eq_biUnion, Precausality.Iminus_eq_biUnion]
  refine iUnion₂_congr fun p _ => ?_
  exact Causality.PushUp.Kminus_eq_Iminus flatCausality_pushUp (flatCausality_mem_Zminus p)

/-- **`K^+(A) = I^+(A)` for every `A`** on a flat spacetime. -/
theorem flatCausality_Kplus_eq_Iplus (A : Set N) :
    (flatCausality d N).Kplus ⊤ A = (flatCausality d N).Iplus ⊤ A := by
  rw [Causality.Kplus_eq_biUnion, Precausality.Iplus_eq_biUnion]
  refine iUnion₂_congr fun p _ => ?_
  exact Causality.PushUp.Kplus_eq_Iplus flatCausality_pushUp (flatCausality_mem_Zplus p)

/-- **`J^-(A) ⊆ closure I^-(A)`** on a flat spacetime. -/
theorem flatCausality_Jminus_subset_closure_Iminus (A : Set N) :
    (flatCausality d N).Jminus ⊤ A ⊆ closure ((flatCausality d N).Iminus ⊤ A) := by
  rintro x ⟨a, ha, hxa⟩
  have : x ∈ closure ((flatCausality d N).Iminus ⊤ {a}) :=
    Causality.Jminus_subset_closure_Iminus_of_pushUp flatCausality_pushUp
      (fun z _ => flatCausality_mem_Zminus z) (by simpa using hxa)
  exact closure_mono (Precausality.Iminus_mono (singleton_subset_iff.2 ha)) this

/-- **`J^+(A) ⊆ closure I^+(A)`** on a flat spacetime. -/
theorem flatCausality_Jplus_subset_closure_Iplus (A : Set N) :
    (flatCausality d N).Jplus ⊤ A ⊆ closure ((flatCausality d N).Iplus ⊤ A) := by
  rintro x ⟨a, ha, hxa⟩
  have : x ∈ closure ((flatCausality d N).Iplus ⊤ {a}) :=
    Causality.Jplus_subset_closure_Iplus_of_pushUp flatCausality_pushUp
      (fun z _ => flatCausality_mem_Zplus z) (by simpa using hxa)
  exact closure_mono (Precausality.Iplus_mono (singleton_subset_iff.2 ha)) this

/-- **Property 4.'s set, past**: `J^-(A) ∖ K^-(A)` lies in the frontier of the open set `I^-(A)`. -/
theorem flatCausality_Jminus_diff_Kminus_subset_frontier (A : Set N) :
    (flatCausality d N).Jminus ⊤ A \ (flatCausality d N).Kminus ⊤ A ⊆
      frontier ((flatCausality d N).Iminus ⊤ A) := by
  rintro x ⟨hxJ, hxK⟩
  rw [flatCausality_Kminus_eq_Iminus] at hxK
  exact ⟨flatCausality_Jminus_subset_closure_Iminus A hxJ,
    by rwa [Causality.isOpen_Iminus.interior_eq]⟩

/-- **Property 4.'s set, future**: `J^+(A) ∖ K^+(A)` lies in the frontier of the open set `I^+(A)`. -/
theorem flatCausality_Jplus_diff_Kplus_subset_frontier (A : Set N) :
    (flatCausality d N).Jplus ⊤ A \ (flatCausality d N).Kplus ⊤ A ⊆
      frontier ((flatCausality d N).Iplus ⊤ A) := by
  rintro x ⟨hxJ, hxK⟩
  rw [flatCausality_Kplus_eq_Iplus] at hxK
  exact ⟨flatCausality_Jplus_subset_closure_Iplus A hxJ,
    by rwa [Causality.isOpen_Iplus.interior_eq]⟩

/-- **Property 3.'s set, past**: on a GH flat spacetime, for `p ≤ q`, `p ≠ q`, the set
`J^-(q) ∖ J^-(p)` contains a non-empty open set. -/
theorem flatCausality_exists_isOpen_subset_Jminus_diff (hT : (flatCausality d N).Tarentin)
    (hG : GH N) {p q : N} (hpq : (flatCausality d N).le ⊤ p q) (hne : p ≠ q) :
    ∃ O : Set N, IsOpen O ∧ O.Nonempty ∧
      O ⊆ (flatCausality d N).Jminus ⊤ {q} \ (flatCausality d N).Jminus ⊤ {p} := by
  have hGH : (flatCausality d N).GloballyHyperbolic := hG
  have hq : q ∉ (flatCausality d N).Jminus ⊤ {p} := fun h =>
    hne (hGH.1 hpq (by simpa using h))
  have hJ : IsClosed ((flatCausality d N).Jminus ⊤ {p}) :=
    Causality.GloballyHyperbolic.isClosed_Jminus_singleton hT hGH p
  have hcl : q ∈ closure ((flatCausality d N).Iminus ⊤ {q}) :=
    flatCausality_Jminus_subset_closure_Iminus {q}
      (by simpa using (flatCausality d N).le_refl (U := ⊤) trivial)
  obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.1 hcl _ hJ.isOpen_compl hq
  exact ⟨_, Causality.isOpen_Iminus.inter hJ.isOpen_compl, ⟨z, hz2, hz1⟩,
    fun w hw => ⟨Causality.Iminus_subset_Jminus hw.1, hw.2⟩⟩

/-- **Property 3.'s set, future**: on a GH flat spacetime, for `p ≤ q`, `p ≠ q`, the set
`J^+(p) ∖ J^+(q)` contains a non-empty open set. -/
theorem flatCausality_exists_isOpen_subset_Jplus_diff (hT : (flatCausality d N).Tarentin)
    (hG : GH N) {p q : N} (hpq : (flatCausality d N).le ⊤ p q) (hne : p ≠ q) :
    ∃ O : Set N, IsOpen O ∧ O.Nonempty ∧
      O ⊆ (flatCausality d N).Jplus ⊤ {p} \ (flatCausality d N).Jplus ⊤ {q} := by
  have hGH : (flatCausality d N).GloballyHyperbolic := hG
  have hp : p ∉ (flatCausality d N).Jplus ⊤ {q} := fun h =>
    hne (hGH.1 hpq (by simpa using h))
  have hJ : IsClosed ((flatCausality d N).Jplus ⊤ {q}) :=
    Causality.GloballyHyperbolic.isClosed_Jplus_singleton hT hGH q
  have hcl : p ∈ closure ((flatCausality d N).Iplus ⊤ {p}) :=
    flatCausality_Jplus_subset_closure_Iplus {p}
      (by simpa using (flatCausality d N).le_refl (U := ⊤) trivial)
  obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.1 hcl _ hJ.isOpen_compl hp
  exact ⟨_, Causality.isOpen_Iplus.inter hJ.isOpen_compl, ⟨z, hz2, hz1⟩,
    fun w hw => ⟨Causality.Iplus_subset_Jplus hw.1, hw.2⟩⟩

end Reach

end Causal.Flat
