import Causal.Lines
import Causal.Reachable
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# `K^±` on lines and on the punctured null plane: the hypotheses that cannot be dropped

`rem:K_neq_I` — `ETT.tex:871`. `rem:K_plongement_hypotheses` — `ETT.tex:951`.

> Causal plainness cannot be dropped from Proposition \ref{prop:tarentin_fort_K}. If $B$ is a
> causal bubble of $J^+(p)$ --- a non-empty open set contained in $J^+(p)$ and disjoint from
> $I^+(p)$ […] --- then $B$ meets $K^+(p)$ while $B\cap I^+(p)=\emptyset$, so
> $K^+(p)\neq I^+(p)$. The same separation occurs, in degenerate form, at a BTZ point, where
> $I^-(p)=\emptyset$ while $K^-(p)=J^-(p)\setminus\{p\}\neq \emptyset$ (Proposition
> \ref{prop:K_calcul}).

> Neither hypothesis can be dispensed with. Without $(a)$ one only gets
> $x\in \overline{J^-(y)}$; global hyperbolicity supplies $(a)$ through Proposition
> \ref{prop:GH_Jferme}. Hypothesis $(b)$ is where push-up enters: at a point which is strongly
> tarentin in the past and around which $M$ is causally plain, $K^-(x)=I^-(x)$ (Proposition
> \ref{prop:tarentin_fort_K}) and $(b)$ reads $J^-(x)\subset\overline{I^-(x)}$, the classical
> density of the chronological past in the causal past. Proposition \ref{prop:K_densite_sing}
> establishes $(b)$ for singular flat spacetimes --- including at BTZ points, where $I^-(x)$ is
> empty and only $K^-(x)$ can be dense.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `rem:K_neq_I`: the other hypotheses of `prop:tarentin_fort_K` (absolutely minimal, tarentin, second countable Hausdorff, `p ∈ Z^-`) | ✓ carried by the witness `halfChronoLine` |
| — "if `B` is a causal bubble of `J^+(p)` then `B` meets `K^+(p)`" | fails in general (`pointedLine`), but `pointedLine` does not meet the hypotheses of `prop:tarentin_fort_K`; under them the claim is **open** |
| `rem:K_plongement_hypotheses`: `M` causal, the other hypothesis of `prop:K_plongement_ordre` | ✓ carried by both witnesses |
| — "around which `M` is causally plain" | **⚠ strengthened: `M` causally plain** (`prop:tarentin_fort_K` is proved for a causally plain `M`) |
| — `prop:GH_Jferme`: tarentin, globally hyperbolic, Hausdorff | ✓ carried |
| — `prop:tarentin_fort_K` (used in `Jminus_subset_closure_Kminus_iff`): second countable | ⚠ weakened: `FirstCountableTopology M` |

## SCOPE (disclosed)

* **`rem:K_neq_I` — content taken: "causal plainness cannot be dropped from
  `prop:tarentin_fort_K`".** Certified by `halfChronoLine`, the line whose causal relation is the
  timelike one and whose chronological relation starts at `-1`: it is tarentin, absolutely
  minimal, causal, `0 ∈ Z^-`, it is not causally plain, `]-∞,-1[` is a causal bubble of `J^-(0)`,
  and `K^-(0) ⊋ I^-(0)` (`causallyPlain_cannot_be_dropped`); its dual gives the `K^+` form. The
  remark's **mechanism** — every bubble meets `K^+(p)` — fails in general: on `pointedLine`
  (only `0` has a future, `J^+(0) = [0,+∞[`) the bubble `]0,+∞[` misses `K^+(0) = ∅`
  (`bubble_need_not_meet_Kplus`). `pointedLine` does not satisfy the hypotheses of
  `prop:tarentin_fort_K` (it is not tarentin — `J^+(p) = {p}` for `p ≠ 0`, so near `5` every
  diamond has empty interior — and `0 ∉ Z^+`, `I^+` being empty), so under those hypotheses the
  mechanism is **open**: neither proved nor refuted here. The BTZ sentence needs `prop:K_calcul` and the model space
  `E_0`, which the library does not have; it is not stated. Not marked.
* **`rem:K_plongement_hypotheses` — content taken: each of (a), (b) is needed for the first
  conclusion of `prop:K_plongement_ordre`, plus the four side assertions.** (a) is needed: on the
  punctured null plane (`ℝ² ∖ {0}` with the product order, the null rays through the puncture
  blocked) `M` is causal, (b) holds at every point for both signs, `J^-((1,0))` is not closed,
  and `K^-((-1,0)) ⊂ K^-((1,0))`, `K^+((1,0)) ⊂ K^+((-1,0))` while `(-1,0) ≰ (1,0)`
  (`hypothesis_a_needed`). (b) is needed: on the spacelike line `M` is causal, (a) holds,
  `K^± ≡ ∅`, and the conclusion and injectivity fail (`hypothesis_b_needed`). Side assertions:
  "one only gets `x ∈ cl J^-(y)`" (`mem_closure_Jminus_of_Kminus_subset`); GH supplies (a)
  (`GloballyHyperbolic.hypothesis_a`, `K_order_embedding_of_globallyHyperbolic`); at a point of
  `Z^-` of a causally plain spacetime (b) reads `J^- ⊂ cl I^-`
  (`Jminus_subset_closure_Kminus_iff`); push-up gives that density at a point whose causal past
  lies in `Z^-` (`Jminus_subset_closure_Iminus_of_pushUp`). The paper's "push-up" is imprecise:
  `ETT.tex:290` calls causal plainness "the push-up property", `defi:pushup` defines a
  relational one. With `defi:pushup` the density needs `J^-(x) ⊂ Z^-`: the spacelike line has
  that push-up (vacuously) and fails (b) everywhere (`pushUp_does_not_give_hypothesis_b`). At
  `ETT.tex:953` the sentence reasons through `prop:tarentin_fort_K`, so its "push-up" is causal
  plainness, which the spacelike line lacks: the sentence is not contradicted. `prop:K_densite_sing` belongs to the
  singular model spaces and is not stated. Not marked.
* **The punctured null plane is a causality in the library's sense whose relation on an open
  `U` is the restriction to `U` of the global one** (`Causality.ofRelation`), not the causality
  of Minkowski space minus a point seen as a Lorentzian manifold. Everything in
  `prop:K_plongement_ordre` reads the relations of `M` only, so the counterexample is one; the
  two causalities agree on `U = M`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Relation

universe u

/-! ### General facts about `K^±` -/

namespace Causality

variable {M : Type u} [TopologicalSpace M] {C : Causality M} {p x y : M}

/-- If the chronological relation of `M` is open in `M × M`, then `I^-(p) ⊂ K^-(p)`. -/
theorem Iminus_subset_Kminus (hO : IsOpen {z : M × M | C.lt ⊤ z.1 z.2}) :
    C.Iminus ⊤ {p} ⊆ C.Kminus ⊤ {p} := by
  intro w hw
  have hwp : C.lt ⊤ w p := by simpa using hw
  obtain ⟨O, hO', Q, hQ, hOQ⟩ := mem_nhds_prod_iff.1 (hO.mem_nhds (show (w, p) ∈ _ from hwp))
  rw [mem_Kminus_singleton]
  intro v hv
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hv.eventually hQ)
  refine ⟨N, mem_interiorWithin_of_mem_nhds (by simpa using C.le_of_lt hwp) ?_⟩
  refine mem_of_superset hO' fun a ha => ⟨?_, ?_⟩
  · have : C.lt ⊤ a p := hOQ (show (a, p) ∈ O ×ˢ Q from ⟨ha, mem_of_mem_nhds hQ⟩)
    simpa using C.le_of_lt this
  · simp only [mem_iInter]
    intro n hn
    have : C.lt ⊤ a (v n) := hOQ (show (a, v n) ∈ O ×ˢ Q from ⟨ha, hN n hn⟩)
    simpa using C.le_of_lt this

/-- If the chronological relation of `M` is open in `M × M`, then `I^+(p) ⊂ K^+(p)`. -/
theorem Iplus_subset_Kplus (hO : IsOpen {z : M × M | C.lt ⊤ z.1 z.2}) :
    C.Iplus ⊤ {p} ⊆ C.Kplus ⊤ {p} :=
  Iminus_subset_Kminus (C := C.dual) (hO.preimage continuous_swap)

/-- `rem:K_plongement_hypotheses`: "without (a) one only gets `x ∈ cl J^-(y)`". -/
theorem mem_closure_Jminus_of_Kminus_subset (hK : C.Jminus ⊤ {x} ⊆ closure (C.Kminus ⊤ {x}))
    (h : C.Kminus ⊤ {x} ⊆ C.Kminus ⊤ {y}) : x ∈ closure (C.Jminus ⊤ {y}) := by
  have hx : x ∈ C.Jminus ⊤ {x} := by simpa using C.le_refl (U := ⊤) (x := x) trivial
  exact closure_mono (h.trans Kminus_subset_Jminus) (hK hx)

/-- `rem:K_plongement_hypotheses`, the `K^+` form: one only gets `y ∈ cl J^+(x)`. -/
theorem mem_closure_Jplus_of_Kplus_subset (hK : C.Jplus ⊤ {y} ⊆ closure (C.Kplus ⊤ {y}))
    (h : C.Kplus ⊤ {y} ⊆ C.Kplus ⊤ {x}) : y ∈ closure (C.Jplus ⊤ {x}) :=
  mem_closure_Jminus_of_Kminus_subset (C := C.dual) hK h

/-- `rem:K_plongement_hypotheses`: global hyperbolicity supplies hypothesis (a) of
`prop:K_plongement_ordre`, through `prop:GH_Jferme`. -/
theorem GloballyHyperbolic.hypothesis_a [T2Space M] (hT : C.Tarentin)
    (hG : C.GloballyHyperbolic) :
    (∀ x, IsClosed (C.Jplus ⊤ {x})) ∧ ∀ x, IsClosed (C.Jminus ⊤ {x}) :=
  ⟨hG.isClosed_Jplus_singleton hT, hG.isClosed_Jminus_singleton hT⟩

/-- `prop:K_plongement_ordre` with (a) supplied by global hyperbolicity. -/
theorem K_order_embedding_of_globallyHyperbolic [T2Space M] (hT : C.Tarentin)
    (hG : C.GloballyHyperbolic) (hKp : ∀ x, C.Jplus ⊤ {x} ⊆ closure (C.Kplus ⊤ {x}))
    (hKm : ∀ x, C.Jminus ⊤ {x} ⊆ closure (C.Kminus ⊤ {x})) :
    (∀ x y, C.Kminus ⊤ {x} ⊆ C.Kminus ⊤ {y} → C.le ⊤ x y) ∧
    (∀ x y, C.Kplus ⊤ {y} ⊆ C.Kplus ⊤ {x} → C.le ⊤ x y) ∧
    Function.Injective (fun x => C.Kminus ⊤ {x}) ∧
      Function.Injective (fun x => C.Kplus ⊤ {x}) := by
  obtain ⟨h1, h2, h3, -⟩ := K_order_embedding (hG.hypothesis_a hT).1 (hG.hypothesis_a hT).2 hKp hKm
  exact ⟨h1, h2, h3 hG.1⟩

/-- `rem:K_plongement_hypotheses`: at a point strongly tarentin in the past of a causally plain
spacetime, (b) reads `J^-(x) ⊂ cl I^-(x)`. -/
theorem Jminus_subset_closure_Kminus_iff [FirstCountableTopology M] (hP : C.CausallyPlain)
    (hx : x ∈ C.Zminus) :
    C.Jminus ⊤ {x} ⊆ closure (C.Kminus ⊤ {x}) ↔ C.Jminus ⊤ {x} ⊆ closure (C.Iminus ⊤ {x}) := by
  rw [Kminus_eq_Iminus_of_mem_Zminus hP hx]

theorem Jplus_subset_closure_Kplus_iff [FirstCountableTopology M] (hP : C.CausallyPlain)
    (hx : x ∈ C.Zplus) :
    C.Jplus ⊤ {x} ⊆ closure (C.Kplus ⊤ {x}) ↔ C.Jplus ⊤ {x} ⊆ closure (C.Iplus ⊤ {x}) := by
  rw [Kplus_eq_Iplus_of_mem_Zplus hP hx]

/-- `rem:K_plongement_hypotheses`, "(b) is where push-up enters": with push-up, `I^-(x)` is dense
in `J^-(x)` as soon as every point of `J^-(x)` is strongly tarentin in the past. -/
theorem Jminus_subset_closure_Iminus_of_pushUp (hU : C.PushUp)
    (hZ : C.Jminus ⊤ {x} ⊆ C.Zminus) : C.Jminus ⊤ {x} ⊆ closure (C.Iminus ⊤ {x}) := by
  intro z hz
  have hzx : C.le ⊤ z x := by simpa using hz
  rw [mem_closure_iff_nhds]
  intro N hN
  obtain ⟨w, hw, hwN⟩ := hZ hz N hN
  have hwz : C.lt ⊤ w z := by simpa using hw
  exact ⟨w, hwN, by simpa using ((pushUp_iff.1 hU) ⊤).1 hwz hzx⟩

theorem Jplus_subset_closure_Iplus_of_pushUp (hU : C.PushUp)
    (hZ : C.Jplus ⊤ {x} ⊆ C.Zplus) : C.Jplus ⊤ {x} ⊆ closure (C.Iplus ⊤ {x}) := by
  have hU' : C.dual.PushUp := by
    rw [pushUp_iff] at hU ⊢
    intro U a b c
    exact ⟨fun h₁ h₂ => (hU U).2 h₂ h₁, fun h₁ h₂ => (hU U).1 h₂ h₁⟩
  exact Jminus_subset_closure_Iminus_of_pushUp (C := C.dual) hU' hZ

end Causality

/-! ### A causality from one global relation -/

section OfRelation

variable {M : Type u} [TopologicalSpace M]

/-- The causality whose relations on an open `U` are the restrictions to `U` of a global
preorder `R` and of a global transitive relation `S ⊂ R` with open sections. -/
def Causality.ofRelation (R S : M → M → Prop) (hrefl : ∀ x, R x x)
    (htrans : ∀ x y z, R x y → R y z → R x z) (hStrans : ∀ x y z, S x y → S y z → S x z)
    (hSR : ∀ x y, S x y → R x y) (hright : ∀ x, IsOpen {y | S x y})
    (hleft : ∀ y, IsOpen {x | S x y}) : Causality M where
  le U x y := x ∈ U ∧ y ∈ U ∧ R x y
  lt U x y := x ∈ U ∧ y ∈ U ∧ S x y
  le_mem_left h := h.1
  le_mem_right h := h.2.1
  lt_mem_left h := h.1
  lt_mem_right h := h.2.1
  le_refl hx := ⟨hx, hx, hrefl _⟩
  le_trans h₁ h₂ := ⟨h₁.1, h₂.2.1, htrans _ _ _ h₁.2.2 h₂.2.2⟩
  lt_trans h₁ h₂ := ⟨h₁.1, h₂.2.1, hStrans _ _ _ h₁.2.2 h₂.2.2⟩
  le_mono h _ _ h' := ⟨h h'.1, h h'.2.1, h'.2.2⟩
  lt_mono h _ _ h' := ⟨h h'.1, h h'.2.1, h'.2.2⟩
  le_of_lt h := ⟨h.1, h.2.1, hSR _ _ h.2.2⟩
  isOpen_lt_right U x := by
    by_cases hx : x ∈ U
    · have : {y | x ∈ U ∧ y ∈ U ∧ S x y} = (U : Set M) ∩ {y | S x y} := by
        ext y; simp [hx]
      rw [this]; exact U.isOpen.inter (hright x)
    · have : {y | x ∈ U ∧ y ∈ U ∧ S x y} = ∅ := by ext y; simp [hx]
      rw [this]; exact isOpen_empty
  isOpen_lt_left U y := by
    by_cases hy : y ∈ U
    · have : {x | x ∈ U ∧ y ∈ U ∧ S x y} = (U : Set M) ∩ {x | S x y} := by
        ext x; simp [hy]
      rw [this]; exact U.isOpen.inter (hleft y)
    · have : {x | x ∈ U ∧ y ∈ U ∧ S x y} = ∅ := by ext x; simp [hy]
      rw [this]; exact isOpen_empty

end OfRelation

/-! ### `rem:K_neq_I`: the half-chronological line -/

/-- The chronological future of the half-chronological line is open. -/
theorem isOpen_halfChrono_right (U : Opens ℝ) (x : ℝ) :
    IsOpen {y : ℝ | -1 < x ∧ x < y ∧ Icc x y ⊆ (U : Set ℝ)} := by
  by_cases hx : -1 < x
  · simpa [hx] using isOpen_setOf_lt_and_Icc_subset_right U x
  · simp [hx]

theorem isOpen_halfChrono_left (U : Opens ℝ) (y : ℝ) :
    IsOpen {x : ℝ | -1 < x ∧ x < y ∧ Icc x y ⊆ (U : Set ℝ)} := by
  have : {x : ℝ | -1 < x ∧ x < y ∧ Icc x y ⊆ (U : Set ℝ)} =
      Ioi (-1) ∩ {x : ℝ | x < y ∧ Icc x y ⊆ (U : Set ℝ)} := by
    ext x; simp
  rw [this]
  exact isOpen_Ioi.inter (isOpen_setOf_lt_and_Icc_subset_left U y)

/-- The **half-chronological line**: the causal relation of the timelike line, and the
chronological relation of the timelike line restricted to the points after `-1`. -/
def halfChronoLine : Causality ℝ where
  le U x y := x ≤ y ∧ Icc x y ⊆ (U : Set ℝ)
  lt U x y := -1 < x ∧ x < y ∧ Icc x y ⊆ (U : Set ℝ)
  le_mem_left h := h.2 (left_mem_Icc.2 h.1)
  le_mem_right h := h.2 (right_mem_Icc.2 h.1)
  lt_mem_left h := h.2.2 (left_mem_Icc.2 h.2.1.le)
  lt_mem_right h := h.2.2 (right_mem_Icc.2 h.2.1.le)
  le_refl hx := ⟨le_rfl, by simpa using hx⟩
  le_trans h₁ h₂ := ⟨h₁.1.trans h₂.1, Icc_subset_Icc_union_Icc.trans (union_subset h₁.2 h₂.2)⟩
  lt_trans h₁ h₂ := ⟨h₁.1, h₁.2.1.trans h₂.2.1,
    Icc_subset_Icc_union_Icc.trans (union_subset h₁.2.2 h₂.2.2)⟩
  le_mono h _ _ h' := ⟨h'.1, fun _ hz => h (h'.2 hz)⟩
  lt_mono h _ _ h' := ⟨h'.1, h'.2.1, fun _ hz => h (h'.2.2 hz)⟩
  le_of_lt h := ⟨h.2.1.le, h.2.2⟩
  isOpen_lt_right := isOpen_halfChrono_right
  isOpen_lt_left := isOpen_halfChrono_left

section HalfChrono

variable {U : Opens ℝ} {x y : ℝ}

@[simp] theorem halfChronoLine_le : halfChronoLine.le U x y ↔ x ≤ y ∧ Icc x y ⊆ (U : Set ℝ) :=
  Iff.rfl

@[simp] theorem halfChronoLine_lt :
    halfChronoLine.lt U x y ↔ -1 < x ∧ x < y ∧ Icc x y ⊆ (U : Set ℝ) := Iff.rfl

theorem halfChronoLine_tarentin : halfChronoLine.Tarentin := timelikeLine_tarentin

theorem halfChronoLine_isCausal : halfChronoLine.IsCausal := timelikeLine_isCausal

theorem halfChronoLine_absolutelyMinimal : halfChronoLine.AbsolutelyMinimal := by
  rw [Precausality.absolutelyMinimal_iff]
  intro S hS V hV x y
  refine ⟨fun h => ((timelikeLine_absolutelyMinimalOn ⊤) S hS V hV x y).1 h, ?_⟩
  rintro ⟨hx, hxy, hsub⟩
  have hc := ((timelikeLine_absolutelyMinimalOn ⊤) S hS V hV x y).2 ⟨hxy, hsub⟩
  -- every point of a chronological chain from `x` lies after `x`, hence after `-1`
  have key : ∀ b, TransGen (fun a b => ∃ O ∈ S, timelikeLine.lt (V ⊓ O) a b) x b →
      TransGen (fun a b => ∃ O ∈ S, halfChronoLine.lt (V ⊓ O) a b) x b ∧ x < b := by
    intro b hb
    induction hb with
    | single hl =>
      obtain ⟨O, hO, hl⟩ := hl
      exact ⟨TransGen.single ⟨O, hO, hx, hl⟩, hl.1⟩
    | tail _ hl ih =>
      obtain ⟨O, hO, hl⟩ := hl
      exact ⟨ih.1.tail ⟨O, hO, hx.trans ih.2, hl⟩, ih.2.trans hl.1⟩
  exact (key y hc).1

theorem halfChronoLine_Jminus_zero : halfChronoLine.Jminus ⊤ {0} = Iic 0 := by
  ext z; simp

theorem halfChronoLine_Iminus_zero : halfChronoLine.Iminus ⊤ {0} = Ioo (-1) 0 := by
  ext z; simp [and_comm]

theorem halfChronoLine_not_causallyPlain : ¬ halfChronoLine.CausallyPlain := by
  intro h
  have h1 : (-2 : ℝ) ∈ interior (halfChronoLine.Jminus ⊤ {0}) := by
    rw [halfChronoLine_Jminus_zero, interior_Iic]
    norm_num
  have h2 := (h ⊤ {0}).2 h1
  rw [halfChronoLine_Iminus_zero, closure_Ioo (by norm_num : (-1 : ℝ) ≠ 0)] at h2
  norm_num at h2

theorem halfChronoLine_mem_Zminus : (0 : ℝ) ∈ halfChronoLine.Zminus := by
  intro N hN
  obtain ⟨l, r, ⟨hl, hr⟩, hlr⟩ := mem_nhds_iff_exists_Ioo_subset.1 hN
  refine ⟨max l (-1) / 2, ?_, hlr ⟨?_, ?_⟩⟩
  · have : max l (-1) < 0 := max_lt hl (by norm_num)
    have h1 : -1 ≤ max l (-1) := le_max_right _ _
    rw [Precausality.mem_Iminus_singleton, halfChronoLine_lt]
    exact ⟨by linarith, by linarith, fun _ _ => trivial⟩
  · have := le_max_left l (-1); have : max l (-1) < 0 := max_lt hl (by norm_num); linarith
  · have : max l (-1) < 0 := max_lt hl (by norm_num); linarith

/-- `]-∞,-1[` is a causal bubble of `J^-(0)`, and it meets `K^-(0)`. -/
theorem halfChronoLine_neg_two_mem_Kminus : (-2 : ℝ) ∈ halfChronoLine.Kminus ⊤ {0} := by
  set u : ℕ → ℝ := fun n => -(1 / ((n : ℝ) + 1)) with hu
  have hut : Tendsto u atTop (𝓝 0) := by
    rw [hu]; simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
  have hu1 : ∀ n, -1 ≤ u n := fun n => by
    have : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    simp only [hu]; linarith
  have hu0 : ∀ n, u n < 0 := fun n => by
    simp only [hu]; have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hp : ∀ n, (0 : ℝ) ∈ interior (halfChronoLine.Jplus ⊤ {u n}) := fun n => by
    have hsub : Ioi (u n) ⊆ halfChronoLine.Jplus ⊤ {u n} := by
      intro z hz
      simp only [Precausality.mem_Jplus_singleton, halfChronoLine_le]
      exact ⟨le_of_lt hz, fun _ _ => trivial⟩
    exact interior_maximal hsub isOpen_Ioi (hu0 n)
  rw [Causality.Kminus_eq_of_tendsto hut hp]
  refine mem_iUnion.2 ⟨0, mem_interiorWithin_of_mem_nhds ?_ ?_⟩
  · simp
  · refine mem_of_superset (Iio_mem_nhds (show (-2 : ℝ) < -1 by norm_num)) fun z hz => ?_
    simp only [mem_iInter, Precausality.mem_Jminus_singleton, halfChronoLine_le]
    exact fun n _ => ⟨(le_of_lt hz).trans (hu1 n), fun _ _ => trivial⟩

/-- **`rem:K_neq_I`, content.** Causal plainness cannot be dropped from `prop:tarentin_fort_K`:
the half-chronological line is tarentin, absolutely minimal and causal, `0` is strongly
tarentin in the past, it is not causally plain, and `K^-(0) ≠ I^-(0)`. -/
theorem causallyPlain_cannot_be_dropped :
    halfChronoLine.Tarentin ∧ halfChronoLine.AbsolutelyMinimal ∧ halfChronoLine.IsCausal ∧
      (0 : ℝ) ∈ halfChronoLine.Zminus ∧ ¬ halfChronoLine.CausallyPlain ∧
      halfChronoLine.Kminus ⊤ {0} ≠ halfChronoLine.Iminus ⊤ {0} := by
  refine ⟨halfChronoLine_tarentin, halfChronoLine_absolutelyMinimal, halfChronoLine_isCausal,
    halfChronoLine_mem_Zminus, halfChronoLine_not_causallyPlain, fun h => ?_⟩
  have := halfChronoLine_neg_two_mem_Kminus
  rw [h, halfChronoLine_Iminus_zero] at this
  norm_num at this

/-- `rem:K_neq_I`, the `K^+` form, on the time-reversed half-chronological line. -/
theorem causallyPlain_cannot_be_dropped_plus :
    halfChronoLine.dual.Tarentin ∧ halfChronoLine.dual.AbsolutelyMinimal ∧
      halfChronoLine.dual.IsCausal ∧ (0 : ℝ) ∈ halfChronoLine.dual.Zplus ∧
      ¬ halfChronoLine.dual.CausallyPlain ∧
      halfChronoLine.dual.Kplus ⊤ {0} ≠ halfChronoLine.dual.Iplus ⊤ {0} := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := causallyPlain_cannot_be_dropped
  exact ⟨Causality.dual_tarentin.2 h1, Causality.dual_absolutelyMinimal.2 h2,
    Causality.dual_isCausal.2 h3, h4, fun h => h5 (Causality.dual_causallyPlain.1 h), h6⟩

end HalfChrono

/-! ### `rem:K_neq_I`: a bubble need not meet `K^+` -/

/-- The **pointed line**: only `0` has a future, `0 ≤_U y` for `y ≥ 0` with `[0,y] ⊂ U`; no
chronology. -/
def pointedLine : Causality ℝ where
  le U x y := (x = y ∧ x ∈ U) ∨ (x = 0 ∧ 0 < y ∧ Icc 0 y ⊆ (U : Set ℝ))
  lt _ _ _ := False
  le_mem_left h := h.elim (fun h => h.2) fun h => by
    rw [h.1]; exact h.2.2 (left_mem_Icc.2 h.2.1.le)
  le_mem_right h := h.elim (fun h => h.1 ▸ h.2) fun h => h.2.2 (right_mem_Icc.2 h.2.1.le)
  lt_mem_left h := h.elim
  lt_mem_right h := h.elim
  le_refl hx := Or.inl ⟨rfl, hx⟩
  le_trans h₁ h₂ := by
    rcases h₁ with ⟨rfl, -⟩ | h₁
    · exact h₂
    · rcases h₂ with ⟨rfl, -⟩ | ⟨rfl, h, -⟩
      · exact Or.inr h₁
      · exact absurd h₁.2.1 (lt_irrefl 0)
  lt_trans h _ := h
  le_mono h _ _ h' := h'.elim (fun h' => Or.inl ⟨h'.1, h h'.2⟩)
    fun h' => Or.inr ⟨h'.1, h'.2.1, fun _ hz => h (h'.2.2 hz)⟩
  lt_mono _ _ _ h' := h'
  le_of_lt h := h.elim
  isOpen_lt_right _ _ := by simp
  isOpen_lt_left _ _ := by simp

theorem pointedLine_Kplus_zero : pointedLine.Kplus ⊤ {0} = ∅ := by
  refine eq_empty_of_forall_notMem fun y hy => ?_
  set u : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hu
  have hut : Tendsto u atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨N, hN⟩ := Causality.mem_Kplus_singleton.1 hy u hut
  have hmem := interiorWithin_subset hN
  simp only [mem_inter_iff, mem_iInter] at hmem
  have hpos : ∀ n, u n ≠ 0 := fun n => by simp only [hu]; positivity
  have key : ∀ n ≥ N, u n = y := fun n hn => by
    have := hmem.2 n hn
    simp only [Precausality.mem_Jplus_singleton] at this
    rcases this with ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h (hpos n)
  have h1 := key N le_rfl
  have h2 := key (N + 1) (Nat.le_succ N)
  have : u N = u (N + 1) := h1.trans h2.symm
  simp only [hu, Nat.cast_add, Nat.cast_one] at this
  have hN0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  rw [div_eq_div_iff hN0.ne' (by positivity)] at this
  linarith

/-- `rem:K_neq_I`: the remark's mechanism fails in general. On the pointed line `]0,+∞[` is a
causal bubble of `J^+(0)` — non-empty, open, contained in `J^+(0)`, disjoint from `I^+(0)` —
and it does not meet `K^+(0)`. The pointed line is not tarentin and `0 ∉ Z^+`, so this says
nothing under the hypotheses of `prop:tarentin_fort_K`, where the mechanism is open. -/
theorem bubble_need_not_meet_Kplus :
    let B : Set ℝ := Ioi 0
    B.Nonempty ∧ IsOpen B ∧ B ⊆ pointedLine.Jplus ⊤ {0} ∧ B ∩ pointedLine.Iplus ⊤ {0} = ∅ ∧
      B ∩ pointedLine.Kplus ⊤ {0} = ∅ := by
  refine ⟨nonempty_Ioi, isOpen_Ioi, fun y hy => ?_, ?_, ?_⟩
  · simp only [Precausality.mem_Jplus_singleton]
    exact Or.inr ⟨rfl, hy, fun _ _ => trivial⟩
  · ext z; simp [pointedLine, Precausality.mem_Iplus]
  · rw [pointedLine_Kplus_zero, inter_empty]

/-! ### `rem:K_plongement_hypotheses`: (b) cannot be dispensed with — the spacelike line -/

theorem spacelikeLine_Kminus (x : ℝ) : spacelikeLine.Kminus ⊤ {x} = ∅ := by
  refine eq_empty_of_forall_notMem fun y hy => ?_
  set u : ℕ → ℝ := fun n => x + 1 / ((n : ℝ) + 1) with hu
  have hut : Tendsto u atTop (𝓝 x) := by
    rw [hu]; simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add x
  obtain ⟨N, hN⟩ := Causality.mem_Kminus_singleton.1 hy u hut
  have hmem := interiorWithin_subset hN
  simp only [mem_inter_iff, mem_iInter, Precausality.mem_Jminus_singleton,
    spacelikeLine_le] at hmem
  have h1 := (hmem.2 N le_rfl).1
  have h2 := (hmem.2 (N + 1) (Nat.le_succ N)).1
  have : u N = u (N + 1) := h1.symm.trans h2
  simp only [hu, Nat.cast_add, Nat.cast_one, add_right_inj] at this
  have hN0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  rw [div_eq_div_iff hN0.ne' (by positivity)] at this
  linarith

theorem spacelikeLine_Kplus (x : ℝ) : spacelikeLine.Kplus ⊤ {x} = ∅ := by
  refine eq_empty_of_forall_notMem fun y hy => ?_
  set u : ℕ → ℝ := fun n => x + 1 / ((n : ℝ) + 1) with hu
  have hut : Tendsto u atTop (𝓝 x) := by
    rw [hu]; simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add x
  obtain ⟨N, hN⟩ := Causality.mem_Kplus_singleton.1 hy u hut
  have hmem := interiorWithin_subset hN
  simp only [mem_inter_iff, mem_iInter, Precausality.mem_Jplus_singleton,
    spacelikeLine_le] at hmem
  have h1 := (hmem.2 N le_rfl).1
  have h2 := (hmem.2 (N + 1) (Nat.le_succ N)).1
  have : u N = u (N + 1) := h1.trans h2.symm
  simp only [hu, Nat.cast_add, Nat.cast_one, add_right_inj] at this
  have hN0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  rw [div_eq_div_iff hN0.ne' (by positivity)] at this
  linarith

theorem spacelikeLine_isCausal : spacelikeLine.IsCausal := fun _ _ h _ => h.1

/-- The spacelike line has the push-up property, vacuously. -/
theorem spacelikeLine_pushUp : spacelikeLine.PushUp := by
  rw [Causality.pushUp_iff]
  intro U x y z
  exact ⟨fun h _ => h.elim, fun _ h => h.elim⟩

/-- `rem:K_plongement_hypotheses`, "(b) is where push-up enters": the push-up of `defi:pushup`
alone gives neither (b) nor the density of `I^-(x)` in `J^-(x)`; the density needs
`J^-(x) ⊂ Z^-` as well (`Jminus_subset_closure_Iminus_of_pushUp`). The spacelike line has
`defi:pushup` (vacuously) and (b) fails at every point; it is not causally plain, which is the
"push-up" of `ETT.tex:290` the sentence of `ETT.tex:953` reasons with. -/
theorem pushUp_does_not_give_hypothesis_b :
    spacelikeLine.PushUp ∧ ∀ x : ℝ,
      ¬ spacelikeLine.Jminus ⊤ {x} ⊆ closure (spacelikeLine.Kminus ⊤ {x}) ∧
      ¬ spacelikeLine.Jminus ⊤ {x} ⊆ closure (spacelikeLine.Iminus ⊤ {x}) := by
  refine ⟨spacelikeLine_pushUp, fun x => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [spacelikeLine_Kminus, closure_empty] at h
    exact h (show x ∈ spacelikeLine.Jminus ⊤ {x} by simp)
  · have hI : spacelikeLine.Iminus ⊤ {x} = ∅ := by ext z; simp
    rw [hI, closure_empty] at h
    exact h (show x ∈ spacelikeLine.Jminus ⊤ {x} by simp)

/-- **`rem:K_plongement_hypotheses`, (b) is needed.** The spacelike line is causal and has
closed causal pasts and futures (hypothesis (a)), hypothesis (b) fails at every point, and so
do the conclusions of `prop:K_plongement_ordre`: `K^-(0) ⊂ K^-(1)` while `0 ≰ 1`, and
`x ↦ K^±(x)` is not injective. -/
theorem hypothesis_b_needed :
    spacelikeLine.IsCausal ∧
      (∀ x, IsClosed (spacelikeLine.Jplus ⊤ {x})) ∧ (∀ x, IsClosed (spacelikeLine.Jminus ⊤ {x})) ∧
      (∀ x, ¬ spacelikeLine.Jminus ⊤ {x} ⊆ closure (spacelikeLine.Kminus ⊤ {x})) ∧
      (∀ x, ¬ spacelikeLine.Jplus ⊤ {x} ⊆ closure (spacelikeLine.Kplus ⊤ {x})) ∧
      spacelikeLine.Kminus ⊤ {0} ⊆ spacelikeLine.Kminus ⊤ {1} ∧ ¬ spacelikeLine.le ⊤ 0 1 ∧
      ¬ Function.Injective (fun x => spacelikeLine.Kminus ⊤ {x}) ∧
      ¬ Function.Injective (fun x => spacelikeLine.Kplus ⊤ {x}) := by
  have hJp : ∀ x, spacelikeLine.Jplus ⊤ {x} = {x} := fun x => by
    ext z; simp [eq_comm]
  have hJm : ∀ x, spacelikeLine.Jminus ⊤ {x} = {x} := fun x => by
    ext z; simp
  refine ⟨spacelikeLine_isCausal, fun x => by rw [hJp]; exact isClosed_singleton,
    fun x => by rw [hJm]; exact isClosed_singleton, fun x h => ?_, fun x h => ?_, ?_, ?_, ?_, ?_⟩
  · rw [hJm, spacelikeLine_Kminus, closure_empty] at h
    exact h rfl
  · rw [hJp, spacelikeLine_Kplus, closure_empty] at h
    exact h rfl
  · rw [spacelikeLine_Kminus]; exact empty_subset _
  · simp
  · intro h
    have : (0 : ℝ) = 1 := h (by simp only [spacelikeLine_Kminus])
    norm_num at this
  · intro h
    have : (0 : ℝ) = 1 := h (by simp only [spacelikeLine_Kplus])
    norm_num at this

/-! ### `rem:K_plongement_hypotheses`: (a) cannot be dispensed with — the punctured null plane -/

/-- The plane minus the origin, coordinates read as null coordinates `(u, v)`. -/
abbrev PuncturedPlane : Type := {p : ℝ × ℝ // p ≠ 0}

namespace PuncturedPlane

/-- The causal relation of the punctured null plane: the product order, except along a null ray
through the puncture. -/
def R (p q : PuncturedPlane) : Prop :=
  p.1.1 ≤ q.1.1 ∧ p.1.2 ≤ q.1.2 ∧ ¬ (p.1.2 = 0 ∧ q.1.2 = 0 ∧ p.1.1 < 0 ∧ 0 < q.1.1) ∧
    ¬ (p.1.1 = 0 ∧ q.1.1 = 0 ∧ p.1.2 < 0 ∧ 0 < q.1.2)

/-- The chronological relation: strictly later in both null coordinates. -/
def S (p q : PuncturedPlane) : Prop := p.1.1 < q.1.1 ∧ p.1.2 < q.1.2

theorem not_both_zero (p : PuncturedPlane) : ¬ (p.1.1 = 0 ∧ p.1.2 = 0) := by
  rintro ⟨h1, h2⟩
  exact p.2 (Prod.ext h1 h2)

theorem R_refl (p : PuncturedPlane) : R p p :=
  ⟨le_rfl, le_rfl, fun h => lt_asymm h.2.2.1 h.2.2.2, fun h => lt_asymm h.2.2.1 h.2.2.2⟩

theorem R_trans (p q r : PuncturedPlane) (h₁ : R p q) (h₂ : R q r) : R p r := by
  obtain ⟨a1, a2, a3, a4⟩ := h₁
  obtain ⟨b1, b2, b3, b4⟩ := h₂
  refine ⟨a1.trans b1, a2.trans b2, ?_, ?_⟩
  · rintro ⟨hp, hr, hp1, hr1⟩
    have hq : q.1.2 = 0 := le_antisymm (hr ▸ b2) (hp ▸ a2)
    rcases lt_trichotomy q.1.1 0 with hq1 | hq1 | hq1
    · exact b3 ⟨hq, hr, hq1, hr1⟩
    · exact not_both_zero q ⟨hq1, hq⟩
    · exact a3 ⟨hp, hq, hp1, hq1⟩
  · rintro ⟨hp, hr, hp1, hr1⟩
    have hq : q.1.1 = 0 := le_antisymm (hr ▸ b1) (hp ▸ a1)
    rcases lt_trichotomy q.1.2 0 with hq1 | hq1 | hq1
    · exact b4 ⟨hq, hr, hq1, hr1⟩
    · exact not_both_zero q ⟨hq, hq1⟩
    · exact a4 ⟨hp, hq, hp1, hq1⟩

theorem S_trans (p q r : PuncturedPlane) (h₁ : S p q) (h₂ : S q r) : S p r :=
  ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

theorem S_R (p q : PuncturedPlane) (h : S p q) : R p q :=
  ⟨h.1.le, h.2.le, fun h' => by linarith [h.2, h'.1, h'.2.1],
    fun h' => by linarith [h.1, h'.1, h'.2.1]⟩

theorem isOpen_S : IsOpen {z : PuncturedPlane × PuncturedPlane | S z.1 z.2} := by
  have hc1 : Continuous fun z : PuncturedPlane × PuncturedPlane => z.1.1.1 :=
    continuous_fst.comp (continuous_subtype_val.comp continuous_fst)
  have hc2 : Continuous fun z : PuncturedPlane × PuncturedPlane => z.2.1.1 :=
    continuous_fst.comp (continuous_subtype_val.comp continuous_snd)
  have hc3 : Continuous fun z : PuncturedPlane × PuncturedPlane => z.1.1.2 :=
    continuous_snd.comp (continuous_subtype_val.comp continuous_fst)
  have hc4 : Continuous fun z : PuncturedPlane × PuncturedPlane => z.2.1.2 :=
    continuous_snd.comp (continuous_subtype_val.comp continuous_snd)
  exact (isOpen_lt hc1 hc2).inter (isOpen_lt hc3 hc4)

theorem isOpen_S_right (p : PuncturedPlane) : IsOpen {q | S p q} :=
  isOpen_S.preimage (Continuous.prodMk_right p)

theorem isOpen_S_left (q : PuncturedPlane) : IsOpen {p | S p q} :=
  isOpen_S.preimage (Continuous.prodMk_left q)

end PuncturedPlane

open PuncturedPlane in
/-- The **punctured null plane** as a causality. -/
def puncturedPlane : Causality PuncturedPlane :=
  Causality.ofRelation R S R_refl R_trans S_trans S_R isOpen_S_right isOpen_S_left

namespace PuncturedPlane

variable {p q : PuncturedPlane}

@[simp] theorem le_top_iff : puncturedPlane.le ⊤ p q ↔ R p q := by
  simp [puncturedPlane, Causality.ofRelation]

@[simp] theorem lt_top_iff : puncturedPlane.lt ⊤ p q ↔ S p q := by
  simp [puncturedPlane, Causality.ofRelation]

theorem isOpen_lt : IsOpen {z : PuncturedPlane × PuncturedPlane | puncturedPlane.lt ⊤ z.1 z.2} := by
  simpa using isOpen_S

/-- A neighbourhood of `z` contains a point `z + s(δ, δ)`, `δ > 0`, for `s = ±1`. -/
theorem exists_shift (z : PuncturedPlane) {N : Set PuncturedPlane} (hN : N ∈ 𝓝 z) {s : ℝ}
    (hs : s = 1 ∨ s = -1) :
    ∃ v ∈ N, ∃ δ > 0, v.1.1 = z.1.1 + s * δ ∧ v.1.2 = z.1.2 + s * δ := by
  obtain ⟨t, ht, htN⟩ := (mem_nhds_subtype _ z N).1 hN
  obtain ⟨t1, ht1, t2, ht2, ht12⟩ := mem_nhds_prod_iff.1 (show t ∈ 𝓝 (z.1.1, z.1.2) from ht)
  obtain ⟨l1, r1, ⟨hl1, hr1⟩, hlr1⟩ := mem_nhds_iff_exists_Ioo_subset.1 ht1
  obtain ⟨l2, r2, ⟨hl2, hr2⟩, hlr2⟩ := mem_nhds_iff_exists_Ioo_subset.1 ht2
  set d := min (min (z.1.1 - l1) (r1 - z.1.1)) (min (z.1.2 - l2) (r2 - z.1.2)) with hd
  have hd0 : 0 < d := lt_min (lt_min (by linarith) (by linarith)) (lt_min (by linarith) (by linarith))
  have hd1 : d ≤ z.1.1 - l1 := (min_le_left _ _).trans (min_le_left _ _)
  have hd2 : d ≤ r1 - z.1.1 := (min_le_left _ _).trans (min_le_right _ _)
  have hd3 : d ≤ z.1.2 - l2 := (min_le_right _ _).trans (min_le_left _ _)
  have hd4 : d ≤ r2 - z.1.2 := (min_le_right _ _).trans (min_le_right _ _)
  -- the point `z + s δ (1,1)`, for `0 < δ < d`, lies in `t`
  have hin : ∀ δ, 0 < δ → δ < d → (z.1.1 + s * δ, z.1.2 + s * δ) ∈ t := by
    intro δ h0 hδ
    refine ht12 ⟨hlr1 ⟨?_, ?_⟩, hlr2 ⟨?_, ?_⟩⟩ <;> rcases hs with rfl | rfl <;> simp <;> linarith
  by_cases h : (z.1.1 + s * (d / 2), z.1.2 + s * (d / 2)) = 0
  · have h' : (z.1.1 + s * (d / 4), z.1.2 + s * (d / 4)) ≠ 0 := by
      intro h'
      have e1 := congrArg Prod.fst h
      have e2 := congrArg Prod.fst h'
      simp only [Prod.fst_zero] at e1 e2
      rcases hs with rfl | rfl <;> linarith
    exact ⟨⟨_, h'⟩, htN (hin _ (by positivity) (by linarith)), d / 4, by positivity, rfl, rfl⟩
  · exact ⟨⟨_, h⟩, htN (hin _ (by positivity) (by linarith)), d / 2, by positivity, rfl, rfl⟩

/-- Every point of the punctured null plane is strongly tarentin in the past. -/
theorem mem_Zminus (z : PuncturedPlane) : z ∈ puncturedPlane.Zminus := by
  intro N hN
  obtain ⟨v, hvN, δ, hδ, h1, h2⟩ := exists_shift z hN (Or.inr rfl)
  refine ⟨v, ?_, hvN⟩
  rw [Precausality.mem_Iminus_singleton, lt_top_iff]
  exact ⟨by rw [h1]; linarith, by rw [h2]; linarith⟩

/-- Every point of the punctured null plane is strongly tarentin in the future. -/
theorem mem_Zplus (z : PuncturedPlane) : z ∈ puncturedPlane.Zplus := by
  intro N hN
  obtain ⟨v, hvN, δ, hδ, h1, h2⟩ := exists_shift z hN (Or.inl rfl)
  refine ⟨v, ?_, hvN⟩
  rw [Precausality.mem_Iplus_singleton, lt_top_iff]
  exact ⟨by rw [h1]; linarith, by rw [h2]; linarith⟩

theorem pushUp : puncturedPlane.PushUp := by
  rw [Causality.pushUp_iff]
  intro U a b c
  refine ⟨fun h₁ h₂ => ⟨h₁.1, h₂.2.1, ?_⟩, fun h₁ h₂ => ⟨h₁.1, h₂.2.1, ?_⟩⟩
  · exact ⟨h₁.2.2.1.trans_le h₂.2.2.1, h₁.2.2.2.trans_le h₂.2.2.2.1⟩
  · exact ⟨h₁.2.2.1.trans_lt h₂.2.2.1, h₁.2.2.2.1.trans_lt h₂.2.2.2⟩

theorem isCausal : puncturedPlane.IsCausal := by
  intro p q hpq hqp
  rw [le_top_iff] at hpq hqp
  exact Subtype.ext (Prod.ext (le_antisymm hpq.1 hqp.1) (le_antisymm hpq.2.1 hqp.2.1))

/-- Hypothesis (b) of `prop:K_plongement_ordre` holds at every point, for the past. -/
theorem hypothesis_b_minus (x : PuncturedPlane) :
    puncturedPlane.Jminus ⊤ {x} ⊆ closure (puncturedPlane.Kminus ⊤ {x}) :=
  (Causality.Jminus_subset_closure_Iminus_of_pushUp pushUp fun z _ => mem_Zminus z).trans
    (closure_mono (Causality.Iminus_subset_Kminus isOpen_lt))

/-- Hypothesis (b) of `prop:K_plongement_ordre` holds at every point, for the future. -/
theorem hypothesis_b_plus (x : PuncturedPlane) :
    puncturedPlane.Jplus ⊤ {x} ⊆ closure (puncturedPlane.Kplus ⊤ {x}) :=
  (Causality.Jplus_subset_closure_Iplus_of_pushUp pushUp fun z _ => mem_Zplus z).trans
    (closure_mono (Causality.Iplus_subset_Kplus isOpen_lt))

/-- The point `(-1, 0)`. -/
def xm : PuncturedPlane := ⟨(-1, 0), by simp⟩

/-- The point `(1, 0)`. -/
def xp : PuncturedPlane := ⟨(1, 0), by simp⟩

theorem not_le_xm_xp : ¬ puncturedPlane.le ⊤ xm xp := by
  rw [le_top_iff]
  rintro ⟨-, -, h, -⟩
  exact h ⟨rfl, rfl, by norm_num [xm], by norm_num [xp]⟩

theorem tendsto_shift (a b : ℝ) (σ : ℝ)
    (hne : ∀ n : ℕ, (a + σ * (1 / ((n : ℝ) + 1)), b + σ * (1 / ((n : ℝ) + 1))) ≠ 0)
    (hab : (a, b) ≠ 0) :
    Tendsto (fun n : ℕ => (⟨_, hne n⟩ : PuncturedPlane)) atTop (𝓝 ⟨(a, b), hab⟩) := by
  rw [tendsto_subtype_rng]
  have h0 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul σ
  rw [mul_zero] at h0
  have h1 := h0.const_add a
  have h2 := h0.const_add b
  rw [add_zero] at h1 h2
  exact h1.prodMk_nhds h2

theorem Kminus_xm_subset : puncturedPlane.Kminus ⊤ {xm} ⊆ puncturedPlane.Kminus ⊤ {xp} := by
  intro z hz
  have hne : ∀ n : ℕ, ((-1 : ℝ) + (-1) * (1 / ((n : ℝ) + 1)), (0 : ℝ) + (-1) * (1 / ((n : ℝ) + 1)))
      ≠ 0 := fun n h => by
    have := congrArg Prod.snd h
    simp only [Prod.snd_zero, zero_add, neg_mul, one_mul, neg_eq_zero] at this
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  obtain ⟨N, hN⟩ := Causality.mem_Kminus_singleton.1 hz _
    (tendsto_shift (-1) 0 (-1) hne xm.2)
  have hmem := interiorWithin_subset hN
  simp only [mem_inter_iff, mem_iInter] at hmem
  have hzq := hmem.2 N le_rfl
  rw [Precausality.mem_Jminus_singleton, le_top_iff] at hzq
  have hε : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
  obtain ⟨h1, h2, -, -⟩ := hzq
  refine Causality.Iminus_subset_Kminus isOpen_lt ?_
  rw [Precausality.mem_Iminus_singleton, lt_top_iff]
  refine ⟨?_, ?_⟩
  · show z.1.1 < 1
    have : z.1.1 ≤ -1 + -1 * (1 / ((N : ℝ) + 1)) := h1
    linarith
  · show z.1.2 < 0
    have : z.1.2 ≤ 0 + -1 * (1 / ((N : ℝ) + 1)) := h2
    linarith

theorem Kplus_xp_subset : puncturedPlane.Kplus ⊤ {xp} ⊆ puncturedPlane.Kplus ⊤ {xm} := by
  intro z hz
  have hne : ∀ n : ℕ, ((1 : ℝ) + 1 * (1 / ((n : ℝ) + 1)), (0 : ℝ) + 1 * (1 / ((n : ℝ) + 1)))
      ≠ 0 := fun n h => by
    have := congrArg Prod.snd h
    simp only [Prod.snd_zero, zero_add, one_mul] at this
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  obtain ⟨N, hN⟩ := Causality.mem_Kplus_singleton.1 hz _
    (tendsto_shift 1 0 1 hne xp.2)
  have hmem := interiorWithin_subset hN
  simp only [mem_inter_iff, mem_iInter] at hmem
  have hzq := hmem.2 N le_rfl
  rw [Precausality.mem_Jplus_singleton, le_top_iff] at hzq
  have hε : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
  obtain ⟨h1, h2, -, -⟩ := hzq
  refine Causality.Iplus_subset_Kplus isOpen_lt ?_
  rw [Precausality.mem_Iplus_singleton, lt_top_iff]
  refine ⟨?_, ?_⟩
  · show (-1 : ℝ) < z.1.1
    have : 1 + 1 * (1 / ((N : ℝ) + 1)) ≤ z.1.1 := h1
    linarith
  · show (0 : ℝ) < z.1.2
    have : 0 + 1 * (1 / ((N : ℝ) + 1)) ≤ z.1.2 := h2
    linarith

end PuncturedPlane

open PuncturedPlane in
/-- **`rem:K_plongement_hypotheses`, (a) is needed.** The punctured null plane is causal,
hypothesis (b) of `prop:K_plongement_ordre` holds at every point for both signs, the causal past
of `(1,0)` is not closed (it misses `(-1,0)`, which is in its closure), and both implications of
`prop:K_plongement_ordre` fail at the pair `(-1,0)`, `(1,0)`. -/
theorem hypothesis_a_needed :
    puncturedPlane.IsCausal ∧
      (∀ x, puncturedPlane.Jplus ⊤ {x} ⊆ closure (puncturedPlane.Kplus ⊤ {x})) ∧
      (∀ x, puncturedPlane.Jminus ⊤ {x} ⊆ closure (puncturedPlane.Kminus ⊤ {x})) ∧
      xm ∈ closure (puncturedPlane.Jminus ⊤ {xp}) ∧ xm ∉ puncturedPlane.Jminus ⊤ {xp} ∧
      ¬ IsClosed (puncturedPlane.Jminus ⊤ {xp}) ∧
      puncturedPlane.Kminus ⊤ {xm} ⊆ puncturedPlane.Kminus ⊤ {xp} ∧
      puncturedPlane.Kplus ⊤ {xp} ⊆ puncturedPlane.Kplus ⊤ {xm} ∧
      ¬ puncturedPlane.le ⊤ xm xp := by
  have hcl : xm ∈ closure (puncturedPlane.Jminus ⊤ {xp}) :=
    Causality.mem_closure_Jminus_of_Kminus_subset (hypothesis_b_minus xm) Kminus_xm_subset
  have hnot : xm ∉ puncturedPlane.Jminus ⊤ {xp} := by
    rw [Precausality.mem_Jminus_singleton]; exact not_le_xm_xp
  refine ⟨isCausal, hypothesis_b_plus, hypothesis_b_minus, hcl, hnot, fun h => ?_,
    Kminus_xm_subset, Kplus_xp_subset, not_le_xm_xp⟩
  rw [h.closure_eq] at hcl
  exact hnot hcl

end Causal
