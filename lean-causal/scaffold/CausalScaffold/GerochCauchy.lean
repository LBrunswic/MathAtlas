import Causal.LimitCurves
import Causal.Minkowski
import Causal.Flat.GerochFlat
import Causal.SingularGeroch
import Causal.MeasureLocal

/-!
# `theo:geroch` (iii)⇒(i) is false as printed: a counterexample, and a conjectured repair

`theo:geroch` — `ETT.tex:1256`, step (iii)⇒(i) at `ETT.tex:1301–1306`; through it
`theo:geroch_sing` — `ETT.tex:1771` (proof `ETT.tex:1781–1785`). **Neither label is marked**: the
step is false as printed (a sorry-free counterexample), and the conjectured repair rests on one
`sorry` whose truth in this setting is open.

> Let $M$ be a metrizable, locally compact topological spacetime. Assume moreover that $M$ is
> tarentin, causally arc-connected and locally causally convex, and that $J^\pm(p)\neq \{p\}$ for
> every $p\in M$. If $M$ admits a pair $(\mu_+,\mu_-)$ of measures admissible respectively in the
> future and in the past, then the following are equivalent: (i) $M$ is globally hyperbolic;
> (ii) $M$ admits a Cauchy time function; (iii) $M$ admits a Cauchy hypersurface.

> \underline{$(iii)\Rightarrow(i)$} This step is technical and uses the notion of quasi-limit of a
> sequence of causal curves (Definition 7, p.~407 of \cite{oneil}). The proof is the object of
> Proposition 8 and of Theorem 35, p.~415 of \cite{oneil}. That proof carries over verbatim under
> the hypotheses of metrizability and local compactness.

## The finding (sorry-free)

**Chronological Minkowski space** `chronoMinkowski n`: `ℝ^{1,n}` with `x ≤_U y` iff `x = y ∈ U`
or `x ≪_U y`, and `≪_U` that of Minkowski space (`Causality.reflChrono`): the null directions are
removed from the causal relation. For `n ≥ 1` (`chronoMinkowski_counterexample`) it is metrizable,
locally compact (second countable, Hausdorff), tarentin, causally arc-connected, strongly causal in
both readings (DEC-7 and open neighbourhoods), `J^±(p) ≠ {p}`, and carries one measure admissible in
the past and in the future; the time `t` is a Cauchy time function strictly increasing along `≤`
(ii), `{t = 0}` is a Cauchy surface (iii) — not a vacuous one, every inextensible curve crosses it;
but it is **not globally hyperbolic** (i): `J((0,x),(2L,x))` is `I⁺ ∩ I⁻` plus its two vertices,
not closed. It is moreover causally plain, causally open, has push-up and is absolutely minimal
(`chronoMinkowski_robust`). So the statements of `CausalScaffold.GerochEquiv`'s
`geroch_iii_imp_i` and `geroch`, and of `CausalScaffold.SingularGeroch`'s
`geroch_sing_of_stronglyCausal` (with an empty singular locus, `chronoMinkowski_singularFlatAxioms`,
`chronoMinkowski_modelMeasures`), are false: `not_gerochIIIImpIAsPrinted`, `not_geroch_tfae`,
`not_geroch_sing_of_stronglyCausal`. O'Neill's quasi-limit is a causal curve because a Lorentzian
causal relation is closed near every point; a topological spacetime's need not be.

## A conjectured repair (one `sorry`, truth open)

With the causal relation **closed** — which (i) implies for a tarentin `M` (`prop:GH_Jferme`,
`ETT.tex:1178`, through `prop:relation_fermee`; `GloballyHyperbolic.isClosed_le`) and the
counterexample violates: `globallyHyperbolic_of_isCauchySurface` and `geroch_of_isClosed_le`
(TFAE of (i), (ii) ∧ closed, (iii) ∧ closed). These are a **conjecture**, not a proved repair:
they rest on `isCompact_Jminus_inter_Jplus_of_isCauchySurface` (`J⁻(q) ∩ J⁺(S)` compact), the
analogue under these hypotheses of O'Neill's compactness lemma for Lorentzian manifolds, which is
**not known to hold in this topological generality**, even with `≤` closed; more closedness (local
causal closedness, `J^±(S)` closed) may be needed. What is proved: `J(p,q)` is closed and lies in
`(J⁻(q) ∩ J⁺(S)) ∪ (J⁺(p) ∩ J⁻(S))`, every point being related to `S`
(`Causal.LimitCurves`).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| metrizable, locally compact | ✓ carried; the counterexample is moreover second countable |
| tarentin, causally arc-connected, `J^±(p) ≠ {p}` | ✓ carried |
| locally causally convex | ✓ `StronglyCausal` (DEC-7); the counterexample also satisfies the open reading |
| a pair `(μ₊, μ₋)` | ✓ carried |
| (iii) a Cauchy surface (DEC-14) | ✓ carried |
| (conjectured repair only) | ⚠ strengthened: the causal relation is closed |

## SCOPE (disclosed)

* The counterexample is a **local** causality (absolutely minimal, kb/0014): not an artefact of
  the missing gluing axiom. It satisfies the paper's definition of a topological spacetime
  (`ETT.tex:254–255`) and every hypothesis of `theo:geroch` in both readings of local causal
  convexity.
* The repaired form is a **conjecture offered for the author's ruling**, not the paper's
  statement and not a proved theorem: its `sorry` is the analogue of O'Neill's compactness lemma,
  whose truth here is open. Whether global closedness of `≤` suffices for it, or a *local* causal
  closedness is needed (O'Neill's use; what `theo:geroch_sing` would need, the models satisfying
  `lem:densite_modele`), is open.
* `theo:geroch_sing` as printed is **not** refuted: a genuine singular flat spacetime has the
  models' locally closed relations; `SingularFlatAxioms` does not carry that model fact.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter MeasureTheory

/-! ### The reflexive chronological causality -/

namespace Causality

variable {M : Type*} [TopologicalSpace M]

/-- The **reflexive chronological causality** of `C`: `x ≤_U y` iff `x = y ∈ U` or `x ≪_U y`;
`≪_U` is that of `C`. -/
def reflChrono (C : Causality M) : Causality M where
  le U x y := (x = y ∧ x ∈ U) ∨ C.lt U x y
  lt U x y := C.lt U x y
  le_mem_left := by
    rintro U x y (⟨rfl, h⟩ | h)
    exacts [h, C.lt_mem_left h]
  le_mem_right := by
    rintro U x y (⟨rfl, h⟩ | h)
    exacts [h, C.lt_mem_right h]
  lt_mem_left h := C.lt_mem_left h
  lt_mem_right h := C.lt_mem_right h
  le_refl hx := Or.inl ⟨rfl, hx⟩
  le_trans := by
    rintro U x y z (⟨rfl, -⟩ | h₁) h₂
    · exact h₂
    · rcases h₂ with ⟨rfl, -⟩ | h₂
      · exact Or.inr h₁
      · exact Or.inr (C.lt_trans h₁ h₂)
  lt_trans h₁ h₂ := C.lt_trans h₁ h₂
  le_mono := by
    rintro U V hVU x y (⟨rfl, h⟩ | h)
    · exact Or.inl ⟨rfl, hVU h⟩
    · exact Or.inr (C.lt_mono hVU h)
  lt_mono hVU _ _ h := C.lt_mono hVU h
  le_of_lt h := Or.inr h
  isOpen_lt_right := C.isOpen_lt_right
  isOpen_lt_left := C.isOpen_lt_left

variable {C : Causality M} {U W : Opens M} {A : Set M} {I : Set ℝ} {c : ℝ → M} {x y p q : M}

theorem reflChrono_le : C.reflChrono.le U x y ↔ (x = y ∧ x ∈ U) ∨ C.lt U x y := Iff.rfl

theorem reflChrono_lt : C.reflChrono.lt U x y ↔ C.lt U x y := Iff.rfl

theorem reflChrono_le_le (h : C.reflChrono.le U x y) : C.le U x y := by
  rcases h with ⟨rfl, hx⟩ | h
  · exact C.le_refl hx
  · exact C.le_of_lt h

theorem reflChrono_lt_of_le_of_ne (h : C.reflChrono.le U x y) (hne : x ≠ y) : C.lt U x y := by
  rcases h with ⟨h, -⟩ | h
  · exact absurd h hne
  · exact h

theorem reflChrono_diamond_subset : C.reflChrono.diamond U p q ⊆ C.diamond U p q := by
  intro z hz
  rw [mem_diamond] at hz ⊢
  exact ⟨reflChrono_le_le hz.1, reflChrono_le_le hz.2⟩

/-- A curve of a relation is a curve of every larger relation. -/
theorem _root_.Causal.CurveOn.mono_rel {r r' : Opens M → M → M → Prop}
    (h : ∀ N x y, r N x y → r' N x y) {a b : ℝ} (hc : CurveOn r W c a b) :
    CurveOn r' W c a b := by
  refine ⟨hc.mem, fun t ht N hN htN => ?_⟩
  obtain ⟨l, u, hl, hu, hrel⟩ := hc.rel t ht N hN htN
  exact ⟨l, u, hl, hu, fun s hs s' hs' h1 h2 h3 => h _ _ _ (hrel s hs s' hs' h1 h2 h3)⟩

theorem CausalCurveIn.of_reflChrono (h : C.reflChrono.CausalCurveIn W I c) :
    C.CausalCurveIn W I c :=
  ⟨h.nonempty, h.ordConnected, fun a ha b hb =>
    CurveOn.mono_rel (fun _ _ _ h => reflChrono_le_le h) (h.curve a ha b hb)⟩

theorem reflChrono_causallyArcConnected (hC : C.CausallyArcConnected) :
    C.reflChrono.CausallyArcConnected := by
  rw [CausallyArcConnected, causallyArcConnectedOn_iff]
  intro U hU p q
  refine ⟨?_, fun h => (hC U hU p q).2.1 h⟩
  rintro (⟨rfl, hp⟩ | h)
  · exact ⟨fun _ => p, causalCurveOn_const hp, rfl, rfl⟩
  · obtain ⟨c, hc, h0, h1⟩ := (hC U hU p q).2.1 h
    exact ⟨c, ChronalCurveOn.causalCurveOn (C := C.reflChrono) hc, h0, h1⟩

theorem reflChrono_stronglyCausal (h : C.StronglyCausal) : C.reflChrono.StronglyCausal := by
  intro p N hN
  obtain ⟨V, hV, hVN, hVc⟩ := h p N hN
  exact ⟨V, hV, hVN, hVc.1, fun a ha b hb => reflChrono_diamond_subset.trans (hVc.2 a ha b hb)⟩

theorem reflChrono_stronglyCausalOpen (h : C.StronglyCausalOpen) :
    C.reflChrono.StronglyCausalOpen := by
  intro p N hN
  obtain ⟨V, hpV, hVN, hVc⟩ := h p N hN
  exact ⟨V, hpV, hVN, hVc.1, fun a ha b hb => reflChrono_diamond_subset.trans (hVc.2 a ha b hb)⟩

/-- Strong causality with open causally convex neighbourhoods, from strong causality, push-up and
`Z^± = M`: the chronological diamond `I^+(a) ∩ I^-(b)` inside a causally convex neighbourhood. -/
theorem stronglyCausalOpen_of_pushUp (hSC : C.StronglyCausal) (hpu : C.PushUp)
    (hZp : ∀ x, x ∈ C.Zplus) (hZm : ∀ x, x ∈ C.Zminus) : C.StronglyCausalOpen := by
  intro p N hN
  obtain ⟨V, hV, hVN, hVc⟩ := hSC p N hN
  obtain ⟨a, ha, haV⟩ := hZm p V hV
  obtain ⟨b, hb, hbV⟩ := hZp p V hV
  rw [Precausality.mem_Iminus_singleton] at ha
  rw [Precausality.mem_Iplus_singleton] at hb
  refine ⟨⟨{z | C.lt ⊤ a z} ∩ {z | C.lt ⊤ z b},
    (C.isOpen_lt_right ⊤ a).inter (C.isOpen_lt_left ⊤ b)⟩, ⟨ha, hb⟩, fun z hz => ?_,
    fun _ _ => trivial, fun z₁ hz₁ z₂ hz₂ w hw => ?_⟩
  · exact hVN (hVc.2 a haV b hbV (mem_diamond.2 ⟨C.le_of_lt hz.1, C.le_of_lt hz.2⟩))
  · rw [mem_diamond] at hw
    exact ⟨(pushUp_iff.1 hpu ⊤).1 hz₁.1 hw.1, (pushUp_iff.1 hpu ⊤).2 hw.2 hz₂.2⟩

theorem reflChrono_tarentin (hZp : ∀ x, x ∈ C.Zplus) (hZm : ∀ x, x ∈ C.Zminus) :
    C.reflChrono.Tarentin := by
  intro x N hN
  obtain ⟨p, hp, hpN⟩ := hZm x N hN
  obtain ⟨q, hq, hqN⟩ := hZp x N hN
  rw [Precausality.mem_Iminus_singleton] at hp
  rw [Precausality.mem_Iplus_singleton] at hq
  refine ⟨p, hpN, q, hqN, ?_⟩
  have hsub : {z | C.lt ⊤ p z} ∩ {z | C.lt ⊤ z q} ⊆ C.reflChrono.diamond ⊤ p q :=
    fun z hz => mem_diamond.2 ⟨Or.inr hz.1, Or.inr hz.2⟩
  exact interior_maximal hsub ((C.isOpen_lt_right ⊤ p).inter (C.isOpen_lt_left ⊤ q)) ⟨hp, hq⟩

theorem reflChrono_pushUp : C.reflChrono.PushUp := by
  rw [pushUp_iff]
  intro U x y z
  refine ⟨fun hxy hyz => ?_, fun hxy hyz => ?_⟩
  · rcases hyz with ⟨rfl, -⟩ | hyz
    · exact hxy
    · exact C.lt_trans hxy hyz
  · rcases hxy with ⟨rfl, -⟩ | hxy
    · exact hyz
    · exact C.lt_trans hxy hyz

/-- **Causal openness** (`def:causally_open_spacetime_open`, DEC-8) always holds for the reflexive
chronological causality: `J^±_U(V) = V ∪ I^±_U(V)`. -/
theorem reflChrono_causallyOpen : C.reflChrono.CausallyOpen := by
  refine ⟨fun U V hVU => ?_, fun U V hVU => ?_⟩
  · have : C.reflChrono.Jplus U V = (V : Set M) ∪ C.Iplus U V := by
      ext y
      constructor
      · rintro ⟨x, hx, ⟨rfl, -⟩ | h⟩
        exacts [Or.inl hx, Or.inr ⟨x, hx, h⟩]
      · rintro (hy | ⟨x, hx, h⟩)
        exacts [⟨y, hy, Or.inl ⟨rfl, hVU hy⟩⟩, ⟨x, hx, Or.inr h⟩]
    rw [this]
    exact V.isOpen.union isOpen_Iplus
  · have : C.reflChrono.Jminus U V = (V : Set M) ∪ C.Iminus U V := by
      ext y
      constructor
      · rintro ⟨x, hx, ⟨rfl, -⟩ | h⟩
        exacts [Or.inl hx, Or.inr ⟨x, hx, h⟩]
      · rintro (hy | ⟨x, hx, h⟩)
        exacts [⟨y, hy, Or.inl ⟨rfl, hVU hy⟩⟩, ⟨x, hx, Or.inr h⟩]
    rw [this]
    exact V.isOpen.union isOpen_Iminus

/-- **Causal plainness** (`defi:causalement_plat`) of the reflexive chronological causality, when
every point of every open `U` is a limit of its chronological future and past in `U`; even
`J^±_U(A) ⊂ closure(I^±_U(A))` holds. -/
theorem reflChrono_causallyPlain
    (h : ∀ (U : Opens M) (x : M), x ∈ U →
      x ∈ closure (C.Iplus U {x}) ∧ x ∈ closure (C.Iminus U {x})) :
    C.reflChrono.CausallyPlain := by
  intro U A
  refine ⟨interior_subset.trans ?_, interior_subset.trans ?_⟩
  · rintro y ⟨x, hx, ⟨rfl, hxU⟩ | hxy⟩
    · exact closure_mono (Precausality.Iplus_mono (singleton_subset_iff.2 hx)) (h U _ hxU).1
    · exact subset_closure ⟨x, hx, hxy⟩
  · rintro y ⟨x, hx, ⟨rfl, hxU⟩ | hxy⟩
    · exact closure_mono (Precausality.Iminus_mono (singleton_subset_iff.2 hx)) (h U _ hxU).2
    · exact subset_closure ⟨x, hx, hxy⟩

/-- `I^-(A) ⊂ K^-(A)` for the reflexive chronological causality, when every point is strongly
tarentin in the future for `C`. -/
theorem Iminus_subset_reflChrono_Kminus (hZp : ∀ x, x ∈ C.Zplus) (A : Set M) :
    C.Iminus ⊤ A ⊆ C.reflChrono.Kminus ⊤ A := by
  rintro y ⟨p, hpA, hyp⟩
  rw [mem_Kminus]
  refine ⟨p, hpA, fun u hu => ?_⟩
  obtain ⟨y', hy'I, hy'p⟩ := hZp y {z | C.lt ⊤ z p} ((C.isOpen_lt_left ⊤ p).mem_nhds hyp)
  rw [Precausality.mem_Iplus_singleton] at hy'I
  have hy'p' : C.lt ⊤ y' p := hy'p
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hu ((C.isOpen_lt_right ⊤ y').mem_nhds hy'p'))
  refine ⟨N, mem_interiorWithin_of_mem_nhds (Precausality.mem_Jminus_singleton.2 (Or.inr hyp))
    (mem_of_superset ((C.isOpen_lt_left ⊤ y').mem_nhds hy'I) fun z hz => ?_)⟩
  have hz' : C.lt ⊤ z y' := hz
  refine ⟨Precausality.mem_Jminus_singleton.2 (Or.inr (C.lt_trans hz' hy'p')), ?_⟩
  simp only [mem_iInter]
  intro n hn
  exact Precausality.mem_Jminus_singleton.2 (Or.inr (C.lt_trans hz' (hN n hn)))

theorem Iplus_subset_reflChrono_Kplus (hZm : ∀ x, x ∈ C.Zminus) (A : Set M) :
    C.Iplus ⊤ A ⊆ C.reflChrono.Kplus ⊤ A := by
  rintro y ⟨p, hpA, hpy⟩
  rw [mem_Kplus]
  refine ⟨p, hpA, fun u hu => ?_⟩
  obtain ⟨y', hy'I, hy'p⟩ := hZm y {z | C.lt ⊤ p z} ((C.isOpen_lt_right ⊤ p).mem_nhds hpy)
  rw [Precausality.mem_Iminus_singleton] at hy'I
  have hy'p' : C.lt ⊤ p y' := hy'p
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hu ((C.isOpen_lt_left ⊤ y').mem_nhds hy'p'))
  refine ⟨N, mem_interiorWithin_of_mem_nhds (Precausality.mem_Jplus_singleton.2 (Or.inr hpy))
    (mem_of_superset ((C.isOpen_lt_right ⊤ y').mem_nhds hy'I) fun z hz => ?_)⟩
  have hz' : C.lt ⊤ y' z := hz
  refine ⟨Precausality.mem_Jplus_singleton.2 (Or.inr (C.lt_trans hy'p' hz')), ?_⟩
  simp only [mem_iInter]
  intro n hn
  exact Precausality.mem_Jplus_singleton.2 (Or.inr (C.lt_trans (hN n hn) hz'))

/-- A time function of `C` is a time function of its reflexive chronological causality. -/
theorem IsTimeFunction.reflChrono {T : M → ℝ} (h : C.IsTimeFunction T) :
    C.reflChrono.IsTimeFunction T := by
  refine ⟨StrongMorphism.continuous h, StrongMorphism.isOpenMap h, ?_, ?_⟩
  · intro U V hV x y hxy
    rcases hxy with ⟨rfl, hx⟩ | hxy
    · have hxU : T x ∈ U := by
        have : x ∈ T ⁻¹' U := by rw [← hV]; exact hx
        exact this
      exact timelikeLine.le_refl hxU
    · exact h.map_le U V hV (C.le_of_lt hxy)
  · intro U V hV x y hxy
    exact h.map_lt U V hV hxy

/-- At the future end of a curve of the reflexive chronological causality, the limit is in the
future of every point of the curve, when the causal futures of `C` are closed and `C` has
push-up at `⊤`. -/
theorem reflChrono_le_of_tendsto_atTop [T2Space M] (hJ : ∀ x, IsClosed (C.Jplus ⊤ {x}))
    (hpu : ∀ ⦃x y z : M⦄, C.lt ⊤ x y → C.le ⊤ y z → C.lt ⊤ x z)
    (hc : C.reflChrono.CausalCurveIn ⊤ univ c) {P : M} (hlim : Tendsto c atTop (𝓝 P)) (t : ℝ) :
    C.reflChrono.le ⊤ (c t) P := by
  by_cases h : ∃ s, t ≤ s ∧ c s ≠ c t
  · obtain ⟨s, hts, hne⟩ := h
    have h1 : C.lt ⊤ (c t) (c s) :=
      reflChrono_lt_of_le_of_ne (hc.le_of_le trivial trivial hts) (Ne.symm hne)
    have h2 : C.le ⊤ (c s) P := by
      have hmem : P ∈ C.Jplus ⊤ {c s} := (hJ (c s)).mem_of_tendsto hlim
        (eventually_atTop.2 ⟨s, fun u hu => Precausality.mem_Jplus_singleton.2
          (reflChrono_le_le (hc.le_of_le trivial trivial hu))⟩)
      exact Precausality.mem_Jplus_singleton.1 hmem
    exact Or.inr (hpu h1 h2)
  · push Not at h
    have hconst : Tendsto c atTop (𝓝 (c t)) :=
      tendsto_nhds_of_eventually_eq (eventually_atTop.2 ⟨t, fun s hs => h s hs⟩)
    rw [tendsto_nhds_unique hlim hconst]
    exact Or.inl ⟨rfl, trivial⟩

theorem reflChrono_le_of_tendsto_atBot [T2Space M] (hJ : ∀ x, IsClosed (C.Jminus ⊤ {x}))
    (hpu : ∀ ⦃x y z : M⦄, C.le ⊤ x y → C.lt ⊤ y z → C.lt ⊤ x z)
    (hc : C.reflChrono.CausalCurveIn ⊤ univ c) {P : M} (hlim : Tendsto c atBot (𝓝 P)) (t : ℝ) :
    C.reflChrono.le ⊤ P (c t) := by
  by_cases h : ∃ s, s ≤ t ∧ c s ≠ c t
  · obtain ⟨s, hst, hne⟩ := h
    have h1 : C.lt ⊤ (c s) (c t) :=
      reflChrono_lt_of_le_of_ne (hc.le_of_le trivial trivial hst) hne
    have h2 : C.le ⊤ P (c s) := by
      have hmem : P ∈ C.Jminus ⊤ {c s} := (hJ (c s)).mem_of_tendsto hlim
        (eventually_atBot.2 ⟨s, fun u hu => Precausality.mem_Jminus_singleton.2
          (reflChrono_le_le (hc.le_of_le trivial trivial hu))⟩)
      exact Precausality.mem_Jminus_singleton.1 hmem
    exact Or.inr (hpu h2 h1)
  · push Not at h
    have hconst : Tendsto c atBot (𝓝 (c t)) :=
      tendsto_nhds_of_eventually_eq (eventually_atBot.2 ⟨t, fun s hs => h s hs⟩)
    rw [tendsto_nhds_unique hlim hconst]
    exact Or.inl ⟨rfl, trivial⟩

end Causality

/-! ### The reflexive chronological static spacetime -/

namespace staticCausality

variable {X : Type*} [MetricSpace X] [GeodesicSpace X] {c : ℝ → ℝ × X}

theorem reflChrono_tarentin : (staticCausality X).reflChrono.Tarentin :=
  Causality.reflChrono_tarentin mem_Zplus mem_Zminus

theorem reflChrono_causallyArcConnected : (staticCausality X).reflChrono.CausallyArcConnected :=
  Causality.reflChrono_causallyArcConnected causallyArcConnected

theorem reflChrono_stronglyCausal : (staticCausality X).reflChrono.StronglyCausal :=
  Causality.reflChrono_stronglyCausal stronglyCausal

theorem reflChrono_isCausal : (staticCausality X).reflChrono.IsCausal :=
  reflChrono_stronglyCausal.isCausal

theorem reflChrono_stronglyCausalOpen : (staticCausality X).reflChrono.StronglyCausalOpen :=
  Causality.stronglyCausalOpen_of_pushUp reflChrono_stronglyCausal Causality.reflChrono_pushUp
    mem_Zplus mem_Zminus

/-- Every point of an open `U` is a limit of its chronological future and past in `U`. -/
theorem mem_closure_Iplus_Iminus (U : Opens (ℝ × X)) (x : ℝ × X) (hx : x ∈ U) :
    x ∈ closure ((staticCausality X).Iplus U {x}) ∧
      x ∈ closure ((staticCausality X).Iminus U {x}) := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 U.isOpen x hx
  have hpt : ∀ ε : ℝ, 0 < ε → ε < ρ / 2 →
      ((x.1 + ε, x.2) : ℝ × X) ∈ (staticCausality X).Iplus U {x} ∧
        ((x.1 - ε, x.2) : ℝ × X) ∈ (staticCausality X).Iminus U {x} ∧
        dist x (x.1 + ε, x.2) < ρ / 2 ∧ dist x (x.1 - ε, x.2) < ρ / 2 := by
    intro ε hε hερ
    have hd1 : dist x ((x.1 + ε, x.2) : ℝ × X) = ε := by
      rw [Prod.dist_eq, dist_self, Real.dist_eq]
      rw [show x.1 - (x.1 + ε) = -ε by ring, abs_neg, abs_of_pos hε, max_eq_left hε.le]
    have hd2 : dist x ((x.1 - ε, x.2) : ℝ × X) = ε := by
      rw [Prod.dist_eq, dist_self, Real.dist_eq]
      rw [show x.1 - (x.1 - ε) = ε by ring, abs_of_pos hε, max_eq_left hε.le]
    refine ⟨Precausality.mem_Iplus_singleton.2 ?_, Precausality.mem_Iminus_singleton.2 ?_,
      by rw [hd1]; exact hερ, by rw [hd2]; exact hερ⟩
    · refine staticLt_of_ball (ρ := ρ) (fun z hz => hball (Metric.mem_ball.2 hz)) ?_ ?_
      · simp only [dist_self]; linarith
      · simp only; linarith
    · have hb : ∀ z : ℝ × X, dist z (x.1 - ε, x.2) < ρ / 2 → z ∈ (U : Set (ℝ × X)) := by
        intro z hz
        refine hball (Metric.mem_ball.2 ?_)
        calc dist z x ≤ dist z (x.1 - ε, x.2) + dist ((x.1 - ε, x.2) : ℝ × X) x :=
              dist_triangle _ _ _
          _ < ρ / 2 + ρ / 2 := by rw [dist_comm _ x, hd2]; linarith
          _ = ρ := by ring
      refine staticLt_of_ball (ρ := ρ / 2) hb ?_ ?_
      · simp only [dist_self]; linarith
      · simp only; linarith
  constructor
  · refine Metric.mem_closure_iff.2 fun δ hδ => ?_
    set ε := min δ (ρ / 2) / 2 with hε
    have hε0 : 0 < ε := by rw [hε]; positivity
    have hεδ : ε < δ := by rw [hε]; linarith [min_le_left δ (ρ / 2)]
    have hερ : ε < ρ / 2 := by rw [hε]; linarith [min_le_right δ (ρ / 2)]
    obtain ⟨h1, -, h3, -⟩ := hpt ε hε0 hερ
    refine ⟨_, h1, ?_⟩
    have : dist x ((x.1 + ε, x.2) : ℝ × X) = ε := by
      rw [Prod.dist_eq, dist_self, Real.dist_eq]
      rw [show x.1 - (x.1 + ε) = -ε by ring, abs_neg, abs_of_pos hε0, max_eq_left hε0.le]
    rw [this]; exact hεδ
  · refine Metric.mem_closure_iff.2 fun δ hδ => ?_
    set ε := min δ (ρ / 2) / 2 with hε
    have hε0 : 0 < ε := by rw [hε]; positivity
    have hεδ : ε < δ := by rw [hε]; linarith [min_le_left δ (ρ / 2)]
    have hερ : ε < ρ / 2 := by rw [hε]; linarith [min_le_right δ (ρ / 2)]
    obtain ⟨-, h2, -, -⟩ := hpt ε hε0 hερ
    refine ⟨_, h2, ?_⟩
    have : dist x ((x.1 - ε, x.2) : ℝ × X) = ε := by
      rw [Prod.dist_eq, dist_self, Real.dist_eq]
      rw [show x.1 - (x.1 - ε) = ε by ring, abs_of_pos hε0, max_eq_left hε0.le]
    rw [this]; exact hεδ

theorem reflChrono_causallyPlain : (staticCausality X).reflChrono.CausallyPlain :=
  Causality.reflChrono_causallyPlain mem_closure_Iplus_Iminus

theorem reflChrono_Jplus_ne_singleton (p : ℝ × X) :
    (staticCausality X).reflChrono.Jplus ⊤ {p} ≠ {p} := by
  intro h
  have : ((p.1 + 1, p.2) : ℝ × X) ∈ (staticCausality X).reflChrono.Jplus ⊤ {p} := by
    refine Precausality.mem_Jplus_singleton.2 (Or.inr ?_)
    rw [lt_top_iff]; simp
  rw [h, mem_singleton_iff, Prod.ext_iff] at this
  linarith [this.1]

theorem reflChrono_Jminus_ne_singleton (p : ℝ × X) :
    (staticCausality X).reflChrono.Jminus ⊤ {p} ≠ {p} := by
  intro h
  have : ((p.1 - 1, p.2) : ℝ × X) ∈ (staticCausality X).reflChrono.Jminus ⊤ {p} := by
    refine Precausality.mem_Jminus_singleton.2 (Or.inr ?_)
    rw [lt_top_iff]; simp
  rw [h, mem_singleton_iff, Prod.ext_iff] at this
  linarith [this.1]

theorem reflChrono_tendsto_time_atTop [CompleteSpace X]
    (hc : (staticCausality X).reflChrono.Inextensible ⊤ univ c) :
    Tendsto (fun s => (c s).1) atTop atTop := by
  have hcC : (staticCausality X).CausalCurveIn ⊤ univ c :=
    Causality.CausalCurveIn.of_reflChrono hc.1
  have hmono := CausalCurveIn.monotone_time hcC
  by_cases h : ∀ b, ∃ a, b ≤ (c a).1
  · exact tendsto_atTop_atTop_of_monotone hmono h
  exfalso
  simp only [not_forall, not_exists, not_le] at h
  obtain ⟨b, hb⟩ := h
  have hbdd : BddAbove (range fun s => (c s).1) := ⟨b, by rintro _ ⟨a, rfl⟩; exact (hb a).le⟩
  have hf := tendsto_atTop_ciSup hmono hbdd
  have hcauchy : CauchySeq fun s => (c s).2 := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := exists_lt_of_lt_ciSup (f := fun s => (c s).1)
      (show (⨆ s, (c s).1) - ε < ⨆ s, (c s).1 by linarith)
    refine ⟨N, fun n hn => ?_⟩
    have h1 := CausalCurveIn.dist_le hcC hn
    have h2 : (c n).1 ≤ ⨆ s, (c s).1 := le_ciSup hbdd n
    rw [dist_comm]
    linarith
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hlim : Tendsto c atTop (𝓝 ((⨆ s, (c s).1), y)) := hf.prodMk_nhds hy
  exact Causality.Inextensible.not_tendsto_atTop_of_le reflChrono_stronglyCausal
    reflChrono_causallyArcConnected reflChrono_isCausal (reflChrono_Jplus_ne_singleton _) hc
    (Causality.reflChrono_le_of_tendsto_atTop isClosed_Jplus_top
      (fun _ _ _ hxy hyz => (Causality.pushUp_iff.1 pushUp ⊤).1 hxy hyz) hc.1 hlim) hlim

theorem reflChrono_tendsto_time_atBot [CompleteSpace X]
    (hc : (staticCausality X).reflChrono.Inextensible ⊤ univ c) :
    Tendsto (fun s => (c s).1) atBot atBot := by
  have hcC : (staticCausality X).CausalCurveIn ⊤ univ c :=
    Causality.CausalCurveIn.of_reflChrono hc.1
  have hmono := CausalCurveIn.monotone_time hcC
  by_cases h : ∀ b, ∃ a, (c a).1 ≤ b
  · exact tendsto_atBot_atBot_of_monotone hmono h
  exfalso
  simp only [not_forall, not_exists, not_le] at h
  obtain ⟨b, hb⟩ := h
  have hanti : Antitone fun s => (c (-s)).1 := fun _ _ h => hmono (neg_le_neg h)
  have hbdd : BddBelow (range fun s => (c (-s)).1) := ⟨b, by rintro _ ⟨a, rfl⟩; exact (hb _).le⟩
  have hf := tendsto_atTop_ciInf hanti hbdd
  have hcauchy : CauchySeq fun s => (c (-s)).2 := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := exists_lt_of_ciInf_lt (f := fun s => (c (-s)).1)
      (show (⨅ s, (c (-s)).1) < (⨅ s, (c (-s)).1) + ε by linarith)
    refine ⟨N, fun n hn => ?_⟩
    have h1 := CausalCurveIn.dist_le hcC (neg_le_neg hn)
    have h2 : ⨅ s, (c (-s)).1 ≤ (c (-n)).1 := ciInf_le hbdd n
    linarith
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hlim : Tendsto c atBot (𝓝 ((⨅ s, (c (-s)).1), y)) := by
    have := (hf.prodMk_nhds hy).comp tendsto_neg_atBot_atTop
    refine this.congr fun s => ?_
    simp
  exact Causality.Inextensible.not_tendsto_atBot_of_le reflChrono_stronglyCausal
    reflChrono_causallyArcConnected reflChrono_isCausal (reflChrono_Jminus_ne_singleton _) hc
    (Causality.reflChrono_le_of_tendsto_atBot isClosed_Jminus_top
      (fun _ _ _ hxy hyz => (Causality.pushUp_iff.1 pushUp ⊤).2 hxy hyz) hc.1 hlim) hlim

/-- **(ii) holds**: the time coordinate is a Cauchy time function of the reflexive chronological
static spacetime over a complete `X`, strictly increasing along `≤`. -/
theorem reflChrono_isCauchyTimeFunction_fst [CompleteSpace X] :
    (staticCausality X).reflChrono.IsCauchyTimeFunction (fun p => p.1) ∧
      ∀ x y, (staticCausality X).reflChrono.le ⊤ x y → x ≠ y → x.1 < y.1 := by
  refine ⟨⟨(isCauchyTimeFunction_fst (X := X)).1.reflChrono, fun c hc =>
    ⟨reflChrono_tendsto_time_atBot hc, reflChrono_tendsto_time_atTop hc⟩⟩, fun x y hxy hne => ?_⟩
  have := lt_top_iff.1 (Causality.reflChrono_lt_of_le_of_ne hxy hne)
  linarith [dist_nonneg (x := x.2) (y := y.2)]

/-- **(iii) holds**: the slice `t = 0` is a Cauchy surface. -/
theorem reflChrono_isCauchySurface [CompleteSpace X] :
    (staticCausality X).reflChrono.IsCauchySurface {p | p.1 = 0} := by
  have h := reflChrono_isCauchyTimeFunction_fst (X := X)
  exact h.1.isCauchySurface reflChrono_causallyArcConnected reflChrono_stronglyCausal
    reflChrono_Jminus_ne_singleton reflChrono_Jplus_ne_singleton h.2

/-- **(i) fails**: as soon as `X` has two points, some diamond is not closed, hence not compact. -/
theorem reflChrono_not_globallyHyperbolic [Nontrivial X] :
    ¬ (staticCausality X).reflChrono.GloballyHyperbolic := by
  rintro ⟨-, hcpt⟩
  obtain ⟨x, y₀, hxy⟩ := exists_pair_ne X
  set L := dist x y₀ with hL
  have hLpos : 0 < L := dist_pos.2 hxy
  obtain ⟨g, hg0, hg1, hg⟩ := GeodesicSpace.exists_geodesic x y₀
  have hclosed : IsClosed ((staticCausality X).reflChrono.diamond ⊤ ((0 : ℝ), x) (2 * L, x)) :=
    (hcpt _ _).isClosed
  have hmem : ∀ s ∈ Ico (0 : ℝ) 1,
      ((L, g s) : ℝ × X) ∈ (staticCausality X).reflChrono.diamond ⊤ ((0 : ℝ), x) (2 * L, x) := by
    intro s hs
    have hd : dist x (g s) = s * L := by
      have := hg 0 ⟨le_rfl, zero_le_one⟩ s ⟨hs.1, hs.2.le⟩
      rw [hg0, zero_sub, abs_neg, abs_of_nonneg hs.1] at this
      exact this
    rw [Causality.mem_diamond]
    refine ⟨Or.inr ?_, Or.inr ?_⟩
    · rw [lt_top_iff]
      simp only
      rw [hd]; nlinarith [hs.2]
    · rw [lt_top_iff]
      simp only
      rw [dist_comm, hd]; nlinarith [hs.2]
  have hg' : Tendsto g (𝓝[<] 1) (𝓝 y₀) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hev : ∀ᶠ s in 𝓝[<] (1 : ℝ), dist (g s) y₀ = |s - 1| * L := by
      filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with s hs
      rw [← hg1]
      exact hg s ⟨hs.1.le, hs.2.le⟩ 1 ⟨zero_le_one, le_rfl⟩
    have h0 : Tendsto (fun s : ℝ => |s - 1| * L) (𝓝[<] 1) (𝓝 0) := by
      have : Tendsto (fun s : ℝ => |s - 1| * L) (𝓝 1) (𝓝 (|1 - 1| * L)) :=
        ((continuous_abs.comp (continuous_id.sub continuous_const)).mul
          continuous_const).tendsto 1
      simpa using this.mono_left nhdsWithin_le_nhds
    exact (tendsto_congr' hev).2 h0
  have hlim : Tendsto (fun s => ((L, g s) : ℝ × X)) (𝓝[<] 1) (𝓝 (L, y₀)) :=
    tendsto_const_nhds.prodMk_nhds hg'
  have hr := hclosed.mem_of_tendsto hlim (by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with s hs
    exact hmem s ⟨hs.1.le, hs.2⟩)
  rw [Causality.mem_diamond] at hr
  rcases hr.1 with ⟨h, -⟩ | h
  · have := congrArg Prod.fst h
    simp only at this
    linarith
  · rw [lt_top_iff] at h
    simp only at h
    linarith

/-- **The measures**: a finite regular measure on `ℝ × X`, positive on non-empty open sets and
null on the frontiers of the open sets `I^±(A)`, is admissible in the past and in the future for
the reflexive chronological causality. -/
theorem reflChrono_admissible_of [MeasurableSpace (ℝ × X)] {μ : Measure (ℝ × X)}
    (hreg : μ.Regular) (hfin : μ univ < ⊤)
    (hpos : ∀ O : Set (ℝ × X), IsOpen O → O.Nonempty → 0 < μ O)
    (hnull : ∀ A : Set (ℝ × X), μ (frontier ((staticCausality X).Iminus ⊤ A)) = 0 ∧
      μ (frontier ((staticCausality X).Iplus ⊤ A)) = 0) :
    (staticCausality X).reflChrono.AdmissiblePast μ ∧
      (staticCausality X).reflChrono.AdmissibleFuture μ := by
  refine ⟨⟨hreg, hfin, fun p q hpq hne => ?_, fun A => ?_⟩,
    ⟨hreg, hfin, fun p q hpq hne => ?_, fun A => ?_⟩⟩
  · have hlt := Causality.reflChrono_lt_of_le_of_ne hpq hne
    have hq : q ∉ (staticCausality X).Jminus ⊤ {p} := fun h =>
      hne (isCausal ((staticCausality X).le_of_lt hlt) (by simpa using h))
    have hcl : q ∈ closure ((staticCausality X).Iminus ⊤ {q}) := by
      rw [closure_Iminus]; simpa using (staticCausality X).le_refl (U := ⊤) trivial
    obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.1 hcl _ (isClosed_Jminus_top p).isOpen_compl hq
    refine (hpos _ (Causality.isOpen_Iminus.inter (isClosed_Jminus_top p).isOpen_compl)
      ⟨z, hz2, hz1⟩).trans_le (measure_mono ?_)
    rintro w ⟨hw1, hw2⟩
    rw [Precausality.mem_Iminus_singleton] at hw1
    refine ⟨Precausality.mem_Jminus_singleton.2 (Or.inr hw1), fun hw => hw2 ?_⟩
    exact Precausality.mem_Jminus_singleton.2
      (Causality.reflChrono_le_le (Precausality.mem_Jminus_singleton.1 hw))
  · refine measure_mono_null (fun x hx => Jminus_diff_Kminus_subset_frontier A ?_) (hnull A).1
    obtain ⟨⟨a, ha, hxa⟩, hxK⟩ := hx
    refine ⟨⟨a, ha, Causality.reflChrono_le_le hxa⟩, fun hK => hxK ?_⟩
    rw [Kminus_eq_Iminus] at hK
    exact Causality.Iminus_subset_reflChrono_Kminus mem_Zplus A hK
  · have hlt := Causality.reflChrono_lt_of_le_of_ne hpq hne
    have hp : p ∉ (staticCausality X).Jplus ⊤ {q} := fun h =>
      hne (isCausal ((staticCausality X).le_of_lt hlt) (by simpa using h))
    have hcl : p ∈ closure ((staticCausality X).Iplus ⊤ {p}) := by
      rw [closure_Iplus]; simpa using (staticCausality X).le_refl (U := ⊤) trivial
    obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.1 hcl _ (isClosed_Jplus_top q).isOpen_compl hp
    refine (hpos _ (Causality.isOpen_Iplus.inter (isClosed_Jplus_top q).isOpen_compl)
      ⟨z, hz2, hz1⟩).trans_le (measure_mono ?_)
    rintro w ⟨hw1, hw2⟩
    rw [Precausality.mem_Iplus_singleton] at hw1
    refine ⟨Precausality.mem_Jplus_singleton.2 (Or.inr hw1), fun hw => hw2 ?_⟩
    exact Precausality.mem_Jplus_singleton.2
      (Causality.reflChrono_le_le (Precausality.mem_Jplus_singleton.1 hw))
  · refine measure_mono_null (fun x hx => Jplus_diff_Kplus_subset_frontier A ?_) (hnull A).2
    obtain ⟨⟨a, ha, hax⟩, hxK⟩ := hx
    refine ⟨⟨a, ha, Causality.reflChrono_le_le hax⟩, fun hK => hxK ?_⟩
    rw [Kplus_eq_Iplus] at hK
    exact Causality.Iplus_subset_reflChrono_Kplus mem_Zminus A hK

end staticCausality

/-! ### Chronological Minkowski space -/

/-- **Chronological Minkowski space** `ℝ^{1,n}`: the reflexive chronological causality of
Minkowski space, `x ≤ y` iff `x = y` or `x ≪ y`. -/
noncomputable abbrev chronoMinkowski (n : ℕ) : Causality (Minkowski n) :=
  (minkowski n).reflChrono

/-- Chronological Minkowski space carries a measure admissible in the past and in the future. -/
theorem chronoMinkowski_admissible (n : ℕ) :
    ∃ μ : Measure (Minkowski n), (chronoMinkowski n).AdmissiblePast μ ∧
      (chronoMinkowski n).AdmissibleFuture μ := by
  obtain ⟨μ, hreg, hfin, hpos, hnull⟩ := Causal.Flat.minkowski_frontier_null_measure n
  exact ⟨μ, staticCausality.reflChrono_admissible_of hreg hfin hpos hnull⟩

/-- **Every hypothesis of `theo:geroch` holds on chronological Minkowski space `ℝ^{1,n}`,
`n ≥ 1`, together with (ii) and (iii), and (i) fails.** -/
theorem chronoMinkowski_counterexample {n : ℕ} (hn : 0 < n) :
    (chronoMinkowski n).Tarentin ∧ (chronoMinkowski n).CausallyArcConnected ∧
      (chronoMinkowski n).StronglyCausal ∧ (chronoMinkowski n).StronglyCausalOpen ∧
      (∀ p, (chronoMinkowski n).Jminus ⊤ {p} ≠ {p}) ∧
      (∀ p, (chronoMinkowski n).Jplus ⊤ {p} ≠ {p}) ∧
      (∃ μ : Measure (Minkowski n), (chronoMinkowski n).AdmissiblePast μ ∧
        (chronoMinkowski n).AdmissibleFuture μ) ∧
      (∃ T : Minkowski n → ℝ, (chronoMinkowski n).IsCauchyTimeFunction T ∧
        ∀ x y, (chronoMinkowski n).le ⊤ x y → x ≠ y → T x < T y) ∧
      (chronoMinkowski n).IsCauchySurface {p | p.1 = 0} ∧
      ¬ (chronoMinkowski n).GloballyHyperbolic := by
  haveI := nontrivial_euclidean hn
  exact ⟨staticCausality.reflChrono_tarentin, staticCausality.reflChrono_causallyArcConnected,
    staticCausality.reflChrono_stronglyCausal, staticCausality.reflChrono_stronglyCausalOpen,
    staticCausality.reflChrono_Jminus_ne_singleton, staticCausality.reflChrono_Jplus_ne_singleton,
    chronoMinkowski_admissible n,
    ⟨fun p => p.1, staticCausality.reflChrono_isCauchyTimeFunction_fst⟩,
    staticCausality.reflChrono_isCauchySurface,
    staticCausality.reflChrono_not_globallyHyperbolic⟩

/-- **Robustness of the counterexample**: chronological Minkowski space is moreover causally
plain, causally open (DEC-8), has push-up and is absolutely minimal (a local causality, kb/0014),
so none of these properties of the paper's spacetimes rescues (iii)⇒(i). -/
theorem chronoMinkowski_robust (n : ℕ) :
    (chronoMinkowski n).CausallyPlain ∧ (chronoMinkowski n).CausallyOpen ∧
      (chronoMinkowski n).PushUp ∧ (chronoMinkowski n).AbsolutelyMinimal ∧
      (chronoMinkowski n).IsCausal :=
  ⟨staticCausality.reflChrono_causallyPlain, Causality.reflChrono_causallyOpen,
    Causality.reflChrono_pushUp, staticCausality.reflChrono_causallyArcConnected.absolutelyMinimal,
    staticCausality.reflChrono_isCausal⟩

/-- Chronological Minkowski space with an empty singular locus satisfies `SingularFlatAxioms`
(`Causal.SingularFlat`): the model facts of the BTZ points are vacuous, the others hold. -/
theorem chronoMinkowski_singularFlatAxioms (n : ℕ) :
    (chronoMinkowski n).SingularFlatAxioms (fun _ => ∅) where
  singularPastAt _ h := h.elim
  Iminus_eq_empty _ h := h.elim
  Iplus_of_lt _ h := h.elim
  past_local _ h := h.elim
  line _ h := h.elim
  pushUp := Causality.reflChrono_pushUp
  absolutelyMinimal := staticCausality.reflChrono_causallyArcConnected.absolutelyMinimal
  causallyArcConnected := staticCausality.reflChrono_causallyArcConnected
  tarentin := staticCausality.reflChrono_tarentin
  mem_Zplus := staticCausality.mem_Zplus
  mem_Zminus_iff p := ⟨fun _ => notMem_empty p, fun _ => staticCausality.mem_Zminus p⟩
  t2 := inferInstance
  secondCountable := inferInstance
  metrizable := inferInstance
  locallyCompact := inferInstance
  noIsolated _ := inferInstance
  isClosed_sing _ _ := isClosed_empty
  interior_sing _ _ := interior_empty
  massive_line _ _ _ h := h.elim

/-- Chronological Minkowski space carries `ModelMeasures` (`Causal.SingularGeroch`): the whole
space is a causally convex open set carrying an admissible pair. -/
theorem chronoMinkowski_modelMeasures (n : ℕ) : (chronoMinkowski n).ModelMeasures := by
  obtain ⟨μ, hμm, hμp⟩ := chronoMinkowski_admissible n
  have hconv : (chronoMinkowski n).CausallyConvexIn ((⊤ : Opens (Minkowski n)) : Set _) ⊤ :=
    ⟨fun _ h => h, fun _ _ _ _ _ _ => trivial⟩
  exact ⟨fun _ => ⟨⊤, trivial, hconv, μ, Causality.admissiblePastOn_top.2 hμm⟩,
    fun _ => ⟨⊤, trivial, hconv, μ, Causality.admissibleFutureOn_top.2 hμp⟩⟩

/-! ### The printed statements, refuted -/

/-- `theo:geroch` (iii)⇒(i) **as printed** (`ETT.tex:1256–1267`, `1301–1306`), in the library's
reading: the statement of `CausalScaffold.GerochEquiv`'s `geroch_iii_imp_i` at universe `0`.
Kept as a `Prop` for the finding (kb/0022). -/
def GerochIIIImpIAsPrinted : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [MetrizableSpace M] [LocallyCompactSpace M]
    [MeasurableSpace M] [BorelSpace M] (C : Causality M) (μp μm : Measure M),
    C.Tarentin → C.CausallyArcConnected → C.StronglyCausal →
    (∀ p : M, C.Jminus ⊤ {p} ≠ {p}) → (∀ p : M, C.Jplus ⊤ {p} ≠ {p}) →
    C.AdmissibleFuture μp → C.AdmissiblePast μm → (∃ S : Set M, C.IsCauchySurface S) →
    C.GloballyHyperbolic

/-- **Finding: `theo:geroch` (iii)⇒(i) is false as printed**, witnessed by chronological
Minkowski space `ℝ^{1,1}`. -/
theorem not_gerochIIIImpIAsPrinted : ¬ GerochIIIImpIAsPrinted := by
  intro h
  obtain ⟨hT, hC, hSC, -, hJm, hJp, ⟨μ, hμm, hμp⟩, -, hS, hnot⟩ :=
    chronoMinkowski_counterexample (n := 1) one_pos
  exact hnot (h (Minkowski 1) (chronoMinkowski 1) μ μ hT hC hSC hJm hJp hμp hμm ⟨_, hS⟩)

/-- **Finding: the equivalence `theo:geroch` is false as printed** (the statement of
`CausalScaffold.GerochEquiv`'s `geroch`, at universe `0`): (ii) and (iii) hold on chronological
Minkowski space, (i) does not. -/
theorem not_geroch_tfae :
    ¬ ∀ (M : Type) [TopologicalSpace M] [MetrizableSpace M] [LocallyCompactSpace M]
      [MeasurableSpace M] [BorelSpace M] (C : Causality M) (μp μm : Measure M),
      C.Tarentin → C.CausallyArcConnected → C.StronglyCausal →
      (∀ p : M, C.Jminus ⊤ {p} ≠ {p}) → (∀ p : M, C.Jplus ⊤ {p} ≠ {p}) →
      C.AdmissibleFuture μp → C.AdmissiblePast μm →
      List.TFAE [C.GloballyHyperbolic,
        ∃ T : M → ℝ, C.IsCauchyTimeFunction T ∧ ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y,
        ∃ S : Set M, C.IsCauchySurface S] := by
  intro h
  obtain ⟨hT, hC, hSC, -, hJm, hJp, ⟨μ, hμm, hμp⟩, -, hS, hnot⟩ :=
    chronoMinkowski_counterexample (n := 1) one_pos
  have hS' : ∃ S : Set (Minkowski 1), (chronoMinkowski 1).IsCauchySurface S := ⟨_, hS⟩
  exact hnot (((h (Minkowski 1) (chronoMinkowski 1) μ μ hT hC hSC hJm hJp hμp hμm).out 2 0).1
    hS')

/-- **Finding: `SingularFlatAxioms` with strong causality and `ModelMeasures` does not give
`theo:geroch_sing`'s equivalence** (the statement of `CausalScaffold.SingularGeroch`'s
`geroch_sing_of_stronglyCausal`, at universe `0`): chronological Minkowski space with an empty
singular locus satisfies all of them. -/
theorem not_geroch_sing_of_stronglyCausal :
    ¬ ∀ (M : Type) [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] (C : Causality M)
      (sing : ℝ → Set M), C.SingularFlatAxioms sing → C.StronglyCausal → C.ModelMeasures →
      List.TFAE [C.GloballyHyperbolic,
        ∃ T : M → ℝ, C.IsCauchyTimeFunction T ∧ ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y,
        ∃ S : Set M, C.IsCauchySurface S] := by
  intro h
  obtain ⟨-, -, hSC, -, -, -, -, -, hS, hnot⟩ := chronoMinkowski_counterexample (n := 1) one_pos
  have hS' : ∃ S : Set (Minkowski 1), (chronoMinkowski 1).IsCauchySurface S := ⟨_, hS⟩
  exact hnot (((h (Minkowski 1) (chronoMinkowski 1) (fun _ => ∅)
    (chronoMinkowski_singularFlatAxioms 1) hSC (chronoMinkowski_modelMeasures 1)).out 2 0).1
    hS')

/-! ### A conjectured repair (rests on one `sorry`, truth open) -/

namespace Causality

variable {M : Type*} [TopologicalSpace M] [MetrizableSpace M] [LocallyCompactSpace M]
  [MeasurableSpace M] [BorelSpace M] {C : Causality M} {μp μm : Measure M}

/-- **Conjecture: the analogue, under these hypotheses, of O'Neill's compactness lemma**
(classical for Lorentzian manifolds: O'Neill 14.40ff, Hawking–Ellis §6.6, as
`Causal.Flat.CBGCompact` cites them): with the causal relation closed, `J^-(q) ∩ J^+(S)` is
compact for a Cauchy surface `S`. **Not known to hold in this topological generality**; more
closedness may be needed. -/
theorem isCompact_Jminus_inter_Jplus_of_isCauchySurface (hT : C.Tarentin)
    (hC : C.CausallyArcConnected) (hSC : C.StronglyCausal) (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p})
    (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) (hμp : C.AdmissibleFuture μp)
    (hμm : C.AdmissiblePast μm) (hle : IsClosed {z : M × M | C.le ⊤ z.1 z.2}) {S : Set M}
    (hS : C.IsCauchySurface S) (q : M) : IsCompact (C.Jminus ⊤ {q} ∩ C.Jplus ⊤ S) := by
  sorry -- SORRY(theo:geroch): conjectural, truth open in this topological setting even with ≤ closed (more closedness may be needed); J⁻(q) ∩ J⁺(S) compact for a Cauchy surface S needs a limit of a sequence of causal curves (O'Neill Def. 7, Prop. 8, Thm 35) or a Zorn substitute; the library has neither in this generality: Causal.Flat.CBGCompact's substitute (PastNoncompactAt) proves only J⁻(q) ∩ S compact, and only when J⁻ of every open set is open (what makes the non-compact points a future set) and J^±(S) are closed, which the library does not derive from these hypotheses

/-- The past form, by time reversal (kb/0002). -/
theorem isCompact_Jplus_inter_Jminus_of_isCauchySurface (hT : C.Tarentin)
    (hC : C.CausallyArcConnected) (hSC : C.StronglyCausal) (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p})
    (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) (hμp : C.AdmissibleFuture μp)
    (hμm : C.AdmissiblePast μm) (hle : IsClosed {z : M × M | C.le ⊤ z.1 z.2}) {S : Set M}
    (hS : C.IsCauchySurface S) (p : M) : IsCompact (C.Jplus ⊤ {p} ∩ C.Jminus ⊤ S) :=
  isCompact_Jminus_inter_Jplus_of_isCauchySurface (C := C.dual) (dual_tarentin.2 hT)
    (dual_causallyArcConnectedOn.2 hC) (dual_stronglyCausal.2 hSC) hJp hJm
    (dual_admissibleFuture.2 hμm) (dual_admissiblePast.2 hμp)
    (hle.preimage (continuous_snd.prodMk continuous_fst)) (dual_isCauchySurfaceOn.2 hS) p

/-- **`theo:geroch` (iii)⇒(i) with the causal relation closed, conjectured** (offered for the
author's ruling): the diamonds are compact. `J(p, q)` is closed, and every point of `M` is in
`J^+(S)` or `J^-(S)` (`IsCauchySurface.exists_le_or_le_of_isClosed_le`), so
`J(p, q) ⊆ (J^-(q) ∩ J^+(S)) ∪ (J^+(p) ∩ J^-(S))`; this reduction is proved, and the theorem rests
on `isCompact_Jminus_inter_Jplus_of_isCauchySurface`, whose truth here is open. -/
theorem isCompact_diamond_of_isCauchySurface (hT : C.Tarentin) (hC : C.CausallyArcConnected)
    (hSC : C.StronglyCausal) (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p})
    (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) (hμp : C.AdmissibleFuture μp)
    (hμm : C.AdmissiblePast μm) (hle : IsClosed {z : M × M | C.le ⊤ z.1 z.2})
    (h : ∃ S : Set M, C.IsCauchySurface S) (p q : M) : IsCompact (C.diamond ⊤ p q) := by
  obtain ⟨S, hS⟩ := h
  have hle' : IsClosed {z : M × M | C.dual.le ⊤ z.1 z.2} :=
    hle.preimage (continuous_snd.prodMk continuous_fst)
  have hclosed : IsClosed (C.diamond ⊤ p q) :=
    (isClosed_Jminus_singleton_of_isClosed_le hle q).inter
      (isClosed_Jminus_singleton_of_isClosed_le (C := C.dual) hle' p)
  refine ((isCompact_Jminus_inter_Jplus_of_isCauchySurface hT hC hSC hJm hJp hμp hμm hle hS
    q).union (isCompact_Jplus_inter_Jminus_of_isCauchySurface hT hC hSC hJm hJp hμp hμm hle hS
    p)).of_isClosed_subset hclosed fun x hx => ?_
  obtain ⟨σ, hσS, h | h⟩ := IsCauchySurface.exists_le_or_le_of_isClosed_le hμm hle hS x
  · exact Or.inr ⟨hx.2, σ, hσS, h⟩
  · exact Or.inl ⟨hx.1, σ, hσS, h⟩

/-- **`theo:geroch` (iii)⇒(i), conjectured repair**: with the causal relation closed. Rests on
`isCompact_Jminus_inter_Jplus_of_isCauchySurface`, whose truth in this setting is open. -/
theorem globallyHyperbolic_of_isCauchySurface (hT : C.Tarentin) (hC : C.CausallyArcConnected)
    (hSC : C.StronglyCausal) (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p})
    (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) (hμp : C.AdmissibleFuture μp)
    (hμm : C.AdmissiblePast μm) (hle : IsClosed {z : M × M | C.le ⊤ z.1 z.2})
    (h : ∃ S : Set M, C.IsCauchySurface S) : C.GloballyHyperbolic :=
  ⟨hSC.isCausal, isCompact_diamond_of_isCauchySurface hT hC hSC hJm hJp hμp hμm hle h⟩

/-- **`theo:geroch`, conjectured repair**: `M` is globally hyperbolic iff it admits a strict
Cauchy time function and its causal relation is closed, iff it admits a Cauchy surface and its
causal relation is closed. (i)⇒(ii) and (ii)⇒(iii) are proved (with `prop:GH_Jferme` for the
closedness); (iii)⇒(i) rests on `isCompact_Jminus_inter_Jplus_of_isCauchySurface`, whose truth in
this setting is open. -/
theorem geroch_of_isClosed_le (hT : C.Tarentin) (hC : C.CausallyArcConnected)
    (hSC : C.StronglyCausal) (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p})
    (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) (hμp : C.AdmissibleFuture μp)
    (hμm : C.AdmissiblePast μm) :
    List.TFAE [C.GloballyHyperbolic,
      (∃ T : M → ℝ, C.IsCauchyTimeFunction T ∧ ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y) ∧
        IsClosed {z : M × M | C.le ⊤ z.1 z.2},
      (∃ S : Set M, C.IsCauchySurface S) ∧ IsClosed {z : M × M | C.le ⊤ z.1 z.2}] := by
  tfae_have 1 → 2 := fun hG =>
    ⟨geroch_i_imp_ii hμp hμm hT hC hJm hJp hG, hG.isClosed_le hT⟩
  tfae_have 2 → 3 := fun ⟨h, hle⟩ => ⟨geroch_ii_imp_iii hC hSC hJm hJp h, hle⟩
  tfae_have 3 → 1 := fun ⟨h, hle⟩ =>
    globallyHyperbolic_of_isCauchySurface hT hC hSC hJm hJp hμp hμm hle h
  tfae_finish

end Causality

end Causal
