import Causal.Static
import Causal.Measure
import Causal.CurvesExtend
import Causal.Flat.CBGCompact

/-!
# Limits of a causal curve at an open end, and inextensible curves, without global hyperbolicity

No label is certified by this file: it is infrastructure for `theo:geroch` (`ETT.tex:1256`),
(iii)⇒(i) (`ETT.tex:1301–1306`), target `T-ett-geroch-iii-i`, used by
`CausalScaffold.GerochCauchy`. Sorry-free.

> If $I=]0,1]$ then $c$ is extensible by setting $c(0)=p$. (`ETT.tex:1291`)

> We use Proposition \ref{prop:cont_ext_cont} to show that the functions
> $t^+:x\mapsto \mu_+(J^+(x))$ and $t^-:x\mapsto -\mu_-(J^-(x))$ are time functions (hence
> continuous). (`ETT.tex:1273–1274`)

## What is proved

* **Adjoining a limit without closed pasts.** The library adjoins the limit `p` of a causal curve
  at an open end (`causalCurveIn_insert`, `extensible_of_tendsto`,
  `Inextensible.not_tendsto_atBot`) when every `J^-(x)` is closed, and uses closedness only to
  know `p ≤ c t` for all `t` (`le_of_tendsto`). Here that fact is the hypothesis:
  `causalCurveIn_insert_of_le`, `extensible_of_tendsto_of_le`,
  `Inextensible.not_tendsto_atBot_of_le`, `Inextensible.not_tendsto_atTop_of_le`. This is what
  decides the Cauchy surfaces of chronological Minkowski space, whose pasts are not closed
  (`CausalScaffold.GerochCauchy`).
* **A closed causal relation gives a continuous function strictly increasing along `≤`, without
  global hyperbolicity** (not shown to be a time function in the sense of DEC-10, a strong
  morphism).
  `AdmissiblePast.continuous_measure_Jminus_of_isClosed_le` (`prop:cont_ext_cont`, past, with
  "tarentin and globally hyperbolic" replaced by "`≤` closed", the one property its proof uses),
  `AdmissiblePast.lt_of_le_of_ne_of_isClosed_le`,
  `AdmissiblePast.exists_strict_continuous_of_isClosed_le`; hence every point lies on an
  inextensible causal curve (`exists_inextensible_mem_of_isClosed_le`, Zorn on time graphs), and a
  Cauchy surface is acausal and met by the past or future of every point
  (`IsCauchySurface.isAcausal_of_isClosed_le`, `IsCauchySurface.exists_le_or_le_of_isClosed_le`):
  with `≤` closed, the vacuous Cauchy surface `GerochEquiv`'s SCOPE worried about cannot occur.

## Hypothesis checklist

| library lemma's hypothesis | here |
|---|---|
| `∀ x, IsClosed (C.Jminus ⊤ {x})` (adjoining a limit) | ⚠ weakened: replaced by its one consequence used, `∀ t, C.le ⊤ p (c t)` |
| strongly causal, causally arc-connected, causal, `J^-(p) ≠ {p}` | ✓ carried |
| `prop:cont_ext_cont`: tarentin, globally hyperbolic | ⚠ weakened: the causal relation closed |

## SCOPE (disclosed)

* No quasi-limit of a *sequence* of causal curves (O'Neill, Def. 7) is constructed: a limit here is
  the limit of one curve at an end of its parameter interval.
* The function is `x ↦ μ₋(J^-(x))` alone, continuous and strictly increasing along `≤`; it is
  **not** shown to be a time function (DEC-10: a strong morphism to the timelike line, in
  particular an open map), and the Geroch time `log(−t⁻/t⁺)` and its Cauchy property are not
  claimed without global hyperbolicity.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter

namespace Causality

variable {M : Type*} [TopologicalSpace M] {C : Causality M} {I : Set ℝ} {c : ℝ → M} {a : ℝ}

/-! ### Adjoining a limit at an open end -/

/-- **A limit at an open end can be adjoined** when it lies in the causal past of the whole
curve: the library's `causalCurveIn_insert` with its closedness hypothesis replaced by the one
fact it is used for. -/
theorem causalCurveIn_insert_of_le (hSC : C.StronglyCausal) (hC : C.CausallyArcConnected)
    (hc : C.CausalCurveIn ⊤ I c) {p : M} (haI : ∀ t ∈ I, a < t)
    (hins : (insert a I).OrdConnected) (hlim : Tendsto c (𝓝[>] a) (𝓝 p))
    (hle : ∀ t ∈ I, C.le ⊤ p (c t)) :
    C.CausalCurveIn ⊤ (insert a I) (fun t => if t ≤ a then p else c t) := by
  set c₀ : ℝ → M := fun t => if t ≤ a then p else c t with hc₀
  have hc₀a : c₀ a = p := by simp [hc₀]
  have hc₀gt : ∀ {t}, a < t → c₀ t = c t := fun h => by simp [hc₀, not_le.2 h]
  refine ⟨⟨a, mem_insert a I⟩, hins, fun s hs s' hs' => ?_⟩
  rcases le_or_gt s s' with hss' | hss'
  swap
  · exact CurveOn.of_lt hss'
  rcases lt_or_ge a s with has | has
  · have hsI : s ∈ I := mem_of_insert hins hs has le_rfl
    have hs'I : s' ∈ I := mem_of_insert hins hs' (has.trans_le hss') le_rfl
    exact (hc.curve s hsI s' hs'I).congr fun t ht => (hc₀gt (has.trans_le ht.1)).symm
  have hsa : s = a := by
    rcases hs with h | h
    · exact h
    · exact absurd (haI s h) (not_lt.2 has)
  subst hsa
  refine ⟨fun _ _ => trivial, fun t ht N _ htN => ?_⟩
  rcases eq_or_lt_of_le ht.1 with hts | hts
  · subst hts
    have hpN : p ∈ N := by rw [← hc₀a]; exact htN
    obtain ⟨V, hV, hVN, hVc⟩ := hSC p N (N.isOpen.mem_nhds hpN)
    obtain ⟨δ, hδ, hδV⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (hlim hV)
    refine ⟨s - 1, δ, by linarith, hδ, fun σ hσ σ' hσ' h1 h2 h3 => ?_⟩
    have hσ'a : s < σ' := hσ.1.trans_lt h2
    have hσ'I : σ' ∈ I := mem_of_insert hins hs' hσ'a hσ'.2
    have hσ'V : c σ' ∈ V := hδV ⟨hσ'a, h3⟩
    rw [hc₀gt hσ'a]
    rcases eq_or_lt_of_le hσ.1 with hσs | hσs
    · subst hσs
      rw [hc₀a]
      exact le_of_causallyConvexIn hC hVc hVN (mem_of_mem_nhds hV) hσ'V (hle σ' hσ'I)
    · have hσI : σ ∈ I := mem_of_insert hins hs' hσs hσ.2
      rw [hc₀gt hσs]
      exact le_of_causallyConvexIn hC hVc hVN (hδV ⟨hσs, h2.trans h3⟩) hσ'V
        (hc.le_of_le hσI hσ'I h2.le)
  · set ε := (s + t) / 2 with hε
    have hsε : s < ε := by rw [hε]; linarith
    have hεt : ε < t := by rw [hε]; linarith
    have hεI : ε ∈ I := mem_of_insert hins hs' hsε (hεt.le.trans ht.2)
    have hs'I : s' ∈ I := mem_of_insert hins hs' (hts.trans_le ht.2) le_rfl
    have hctN : c t ∈ N := by rw [← hc₀gt hts]; exact htN
    obtain ⟨l, u, hl, hu, hrel⟩ :=
      (hc.curve ε hεI s' hs'I).rel t ⟨hεt.le, ht.2⟩ N le_top hctN
    refine ⟨max l ε, u, max_lt hl hεt, hu, fun σ hσ σ' hσ' h1 h2 h3 => ?_⟩
    have hεσ : ε < σ := (le_max_right _ _).trans_lt h1
    rw [hc₀gt (hsε.trans hεσ), hc₀gt (hsε.trans (hεσ.trans h2))]
    exact hrel σ ⟨hεσ.le, hσ.2⟩ σ' ⟨(hεσ.trans h2).le, hσ'.2⟩
      ((le_max_left _ _).trans_lt h1) h2 h3

/-- **A curve with a limit `p` at an open lower end is extensible** when `p ≤ c t` for all `t`:
adjoin `p`, then prepend a curve from a point of `J^-(p) ∖ {p}`. -/
theorem extensible_of_tendsto_of_le (hSC : C.StronglyCausal) (hC : C.CausallyArcConnected)
    (hcaus : C.IsCausal) (hc : C.CausalCurveIn ⊤ I c) {p : M} (haI : ∀ t ∈ I, a < t)
    (hins : (insert a I).OrdConnected) (hlim : Tendsto c (𝓝[>] a) (𝓝 p))
    (hle : ∀ t ∈ I, C.le ⊤ p (c t)) (hp : C.Jminus ⊤ {p} ≠ {p}) : C.Extensible ⊤ I c := by
  have h₀ := causalCurveIn_insert_of_le hSC hC hc haI hins hlim hle
  obtain ⟨q, hqJ, hqne⟩ := exists_ne_of_ne_singleton
    (by simpa using C.le_refl (show p ∈ (⊤ : Opens M) from trivial) : p ∈ C.Jminus ⊤ {p}) hp
  have hq : C.le ⊤ q p := by simpa using hqJ
  have hleast : IsLeast (insert a I) a := ⟨mem_insert a I, fun t ht => by
    rcases ht with h | h
    · exact h.ge
    · exact (haI t h).le⟩
  obtain ⟨c', hc', heq, h0⟩ := exists_prepend hC h₀ hleast (q := q) (by simpa using hq)
  have hcI : ∀ t ∈ I, c' t = c t := fun t ht => by
    rw [heq t (mem_insert_of_mem a ht)]
    simp [not_le.2 (haI t ht)]
  refine ⟨_, c', hc', ⟨id, strictMonoOn_id, fun t ht => Or.inr (mem_insert_of_mem a ht), by
    rw [image_id]; exact hc.ordConnected, hcI⟩,
    ⟨a - 1, Or.inl ⟨le_rfl, by linarith⟩, fun t ht hqt => ?_⟩⟩
  rw [h0] at hqt
  subst hqt
  exact hqne (hcaus hq (hle t ht))

/-- **An inextensible curve over `ℝ` has no limit at its past end lying in the causal past of
the whole curve.** -/
theorem Inextensible.not_tendsto_atBot_of_le (hSC : C.StronglyCausal)
    (hC : C.CausallyArcConnected) (hcaus : C.IsCausal) {P : M} (hP : C.Jminus ⊤ {P} ≠ {P})
    (hc : C.Inextensible ⊤ univ c) (hle : ∀ t, C.le ⊤ P (c t)) : ¬ Tendsto c atBot (𝓝 P) := by
  intro hlim
  apply hc.2
  have hd : C.CausalCurveIn ⊤ (Ioi 0) (c ∘ Real.log) :=
    hc.1.comp ⟨1, mem_Ioi.2 one_pos⟩ ordConnected_Ioi Real.strictMonoOn_log
      (Real.continuousOn_log.mono fun x hx => ne_of_gt hx) fun _ _ => trivial
  have hins : (insert (0 : ℝ) (Ioi 0)).OrdConnected := by
    have : insert (0 : ℝ) (Ioi 0) = Ici 0 := by
      ext x
      simp only [mem_insert_iff, mem_Ioi, mem_Ici]
      constructor
      · rintro (rfl | h)
        exacts [le_rfl, h.le]
      · intro h
        rcases h.eq_or_lt with h | h
        exacts [Or.inl h.symm, Or.inr h]
    rw [this]; exact ordConnected_Ici
  have hext := extensible_of_tendsto_of_le hSC hC hcaus hd (a := 0) (fun _ ht => ht) hins
    (hlim.comp Real.tendsto_log_nhdsGT_zero) (fun t _ => hle (Real.log t)) hP
  refine hext.of_comp (ψ := Real.exp) (Real.exp_strictMono.strictMonoOn univ)
    (fun t _ => Real.exp_pos t) (fun y hy => ⟨Real.log y, trivial, Real.exp_log hy⟩)
    (fun t _ => by simp)

/-- **An inextensible curve over `ℝ` has no limit at its future end lying in the causal future
of the whole curve**, by time reversal. -/
theorem Inextensible.not_tendsto_atTop_of_le (hSC : C.StronglyCausal)
    (hC : C.CausallyArcConnected) (hcaus : C.IsCausal) {P : M} (hP : C.Jplus ⊤ {P} ≠ {P})
    (hc : C.Inextensible ⊤ univ c) (hle : ∀ t, C.le ⊤ (c t) P) : ¬ Tendsto c atTop (𝓝 P) := by
  intro hlim
  have hc' := hc.dual_reverse
  rw [Set.neg_univ] at hc'
  exact Inextensible.not_tendsto_atBot_of_le (C := C.dual) (dual_stronglyCausal.2 hSC)
    (dual_causallyArcConnectedOn.2 hC) (dual_isCausal.2 hcaus) hP hc' (fun t => hle (-t))
    (hlim.comp tendsto_neg_atBot_atTop)

/-! ### A closed causal relation: a continuous function strictly increasing along `≤` -/

section ClosedRelation

open MeasureTheory

variable [MeasurableSpace M] {μ : Measure M}

/-- **`prop:cont_ext_cont`, past, without global hyperbolicity**: `p ↦ μ(J^-(p))` is continuous
for a measure admissible in the past as soon as the causal relation is closed. The library's
`AdmissiblePast.continuous_measure_Jminus` asks `M` tarentin and globally hyperbolic and uses them
only for the closedness of `J^-(p)` and of `J^+(K)`, `K` compact, which a closed relation gives. -/
theorem AdmissiblePast.continuous_measure_Jminus_of_isClosed_le [T2Space M]
    [FirstCountableTopology M] [BorelSpace M] (hμ : C.AdmissiblePast μ)
    (hle : IsClosed {z : M × M | C.le ⊤ z.1 z.2}) :
    Continuous fun p => μ (C.Jminus ⊤ {p}) := by
  haveI := hμ.regular
  haveI : IsFiniteMeasure μ := ⟨hμ.finite⟩
  rw [continuous_iff_seqContinuous]
  intro q p hq
  show Tendsto (fun n => μ (C.Jminus ⊤ {q n})) atTop (𝓝 (μ (C.Jminus ⊤ {p})))
  rw [ENNReal.tendsto_nhds (measure_ne_top μ _)]
  intro ε hε
  have hε0 : ε ≠ 0 := hε.ne'
  have hJclosed : ∀ x, IsClosed (C.Jminus ⊤ {x}) := isClosed_Jminus_singleton_of_isClosed_le hle
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
  have hup : ∀ᶠ n in atTop, μ (C.Jminus ⊤ {q n}) ≤ μ (C.Jminus ⊤ {p}) + ε := by
    have hFmeas : MeasurableSet (C.Jminus ⊤ {p})ᶜ := (hJclosed p).measurableSet.compl
    obtain ⟨K, hKF, hKc, hKlt⟩ := hFmeas.exists_isCompact_lt_add (measure_ne_top μ _) hε0
    have hJK : IsClosed (C.Jplus ⊤ K) := isClosed_Jplus_of_isCompact hle hKc
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

/-- `μ(J^-(x)) < μ(J^-(y))` for `x ≤ y`, `x ≠ y`, when the causal relation is closed. -/
theorem AdmissiblePast.lt_of_le_of_ne_of_isClosed_le [BorelSpace M] (hμ : C.AdmissiblePast μ)
    (hle : IsClosed {z : M × M | C.le ⊤ z.1 z.2}) {x y : M} (hxy : C.le ⊤ x y) (hne : x ≠ y) :
    μ (C.Jminus ⊤ {x}) < μ (C.Jminus ⊤ {y}) := by
  haveI : IsFiniteMeasure μ := ⟨hμ.finite⟩
  have hJclosed : ∀ x, IsClosed (C.Jminus ⊤ {x}) := isClosed_Jminus_singleton_of_isClosed_le hle
  have hmeas : MeasurableSet (C.Jminus ⊤ {x}) := (hJclosed x).measurableSet
  have hsub : C.Jminus ⊤ {x} ⊆ C.Jminus ⊤ {y} := Precausality.Jminus_singleton_subset hxy
  have hsplit : μ (C.Jminus ⊤ {y}) =
      μ (C.Jminus ⊤ {x}) + μ (C.Jminus ⊤ {y} \ C.Jminus ⊤ {x}) := by
    rw [← measure_union disjoint_sdiff_right ((hJclosed y).measurableSet.diff hmeas)]
    rw [union_sdiff_cancel hsub]
  rw [hsplit]
  exact ENNReal.lt_add_right (measure_ne_top μ _) (hμ.pos hxy hne).ne'

/-- **A continuous function strictly increasing along `≤`, without global hyperbolicity**:
`x ↦ μ(J^-(x))` for a measure admissible in the past, when the causal relation is closed. It is
not shown to be a time function in the sense of DEC-10 (a strong morphism). -/
theorem AdmissiblePast.exists_strict_continuous_of_isClosed_le [T2Space M]
    [FirstCountableTopology M] [BorelSpace M] (hμ : C.AdmissiblePast μ)
    (hle : IsClosed {z : M × M | C.le ⊤ z.1 z.2}) :
    ∃ T : M → ℝ, Continuous T ∧ ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y := by
  haveI : IsFiniteMeasure μ := ⟨hμ.finite⟩
  refine ⟨fun x => (μ (C.Jminus ⊤ {x})).toReal, ?_, fun x y hxy hne => ?_⟩
  · exact ENNReal.continuousOn_toReal.comp_continuous
      (hμ.continuous_measure_Jminus_of_isClosed_le hle) fun x => measure_ne_top μ _
  · exact (ENNReal.toReal_lt_toReal (measure_ne_top μ _) (measure_ne_top μ _)).2
      (hμ.lt_of_le_of_ne_of_isClosed_le hle hxy hne)

/-- **Every point lies on an inextensible causal curve** when the causal relation is closed and
`M` carries a measure admissible in the past (Zorn on time graphs, `Causal.CurvesExtend`). -/
theorem exists_inextensible_mem_of_isClosed_le [T2Space M] [FirstCountableTopology M]
    [BorelSpace M] (hμ : C.AdmissiblePast μ) (hle : IsClosed {z : M × M | C.le ⊤ z.1 z.2})
    (x : M) : ∃ (J : Set ℝ) (γ : ℝ → M), C.Inextensible ⊤ J γ ∧ x ∈ γ '' J := by
  obtain ⟨T, hTc, hT⟩ := hμ.exists_strict_continuous_of_isClosed_le hle
  have hc : C.CausalCurveIn ⊤ (Icc 0 0) (fun _ : ℝ => x) :=
    CausalCurveOn.causalCurveIn_Icc (causalCurveOn_const (show x ∈ (⊤ : Opens M) from trivial))
      le_rfl
  obtain ⟨J, γ, hγ, hsub, -⟩ := exists_inextensible_of_timeFunction hTc hT hc
  exact ⟨J, γ, hγ, hsub ⟨0, ⟨le_rfl, le_rfl⟩, rfl⟩⟩

/-- **A Cauchy surface is not vacuous** when the causal relation is closed: every point is in
its causal past or its causal future. -/
theorem IsCauchySurface.exists_le_or_le_of_isClosed_le [T2Space M] [FirstCountableTopology M]
    [BorelSpace M] (hμ : C.AdmissiblePast μ) (hle : IsClosed {z : M × M | C.le ⊤ z.1 z.2})
    {S : Set M} (hS : C.IsCauchySurface S) (x : M) :
    ∃ σ ∈ S, C.le ⊤ x σ ∨ C.le ⊤ σ x := by
  obtain ⟨J, γ, hγ, ⟨t, ht, rfl⟩⟩ := exists_inextensible_mem_of_isClosed_le hμ hle x
  obtain ⟨σ, ⟨⟨s, hs, rfl⟩, hσS⟩, -⟩ := hS J γ hγ
  refine ⟨γ s, hσS, ?_⟩
  rcases le_total t s with h | h
  · exact Or.inl (hγ.1.le_of_le ht hs h)
  · exact Or.inr (hγ.1.le_of_le hs ht h)

/-- **A Cauchy surface is acausal** when the causal relation is closed and `M` is causally
arc-connected with a measure admissible in the past. -/
theorem IsCauchySurface.isAcausal_of_isClosed_le [T2Space M] [FirstCountableTopology M]
    [BorelSpace M] (hμ : C.AdmissiblePast μ) (hle : IsClosed {z : M × M | C.le ⊤ z.1 z.2})
    (hC : C.CausallyArcConnected) {S : Set M} (hS : C.IsCauchySurface S) : C.IsAcausal S := by
  obtain ⟨T, hTc, hT⟩ := hμ.exists_strict_continuous_of_isClosed_le hle
  exact hS.isAcausal_of_timeFunction hC hTc hT

end ClosedRelation

end Causality

end Causal
