import Causal.KBorelien
import Causal.LinesReachable

/-!
# `rem:K_neq_I`'s bubble sentence is false under the other hypotheses of `prop:tarentin_fort_K`

`rem:K_neq_I` — `ETT.tex:871`. Cited, not marked: this module refutes the remark's bubble
sentence (`ETT.tex:872–875`) under every hypothesis of `prop:tarentin_fort_K` but causal
plainness; the remark's first sentence (`halfChronoLine`, `Causal.LinesReachable`) and its BTZ
sentence (`ETT.tex:875–877`, waiting on OQ-34) are untouched. `prop:tarentin_fort_K` —
`ETT.tex:850`, cited for its hypotheses only.

> Causal plainness cannot be dropped from Proposition \ref{prop:tarentin_fort_K}. If $B$ is a
> causal bubble of $J^+(p)$ --- a non-empty open set contained in $J^+(p)$ and disjoint from
> $I^+(p)$, as occurs below Lipschitz regularity
> \cite{MR2949547,MR3500220,samann2024nonregular} --- then $B$ meets $K^+(p)$ while
> $B\cap I^+(p)=\emptyset$, so $K^+(p)\neq I^+(p)$. (`ETT.tex:872–875`)

> Let $M$ be a causally plain, absolutely minimal, tarentin topological spacetime and let
> $p\in M$. If $p$ is strongly tarentin in the past, then $K^-(p) = I^-(p)$.
> (`ETT.tex:851–852`)

## The finding (sorry-free)

**Minkowski space with one spoke.** On `ℝ × ℝ`, `spokesCausality (Ioi 0)` (`Causal.KBorelien`):
`≪` is Minkowski's, and `≤` adds the spacelike steps `(0, x) ≤ (0, c x)`, `x > 0`, `c ∈ [0, 1]`,
of the slice `t = 0` towards the origin `o = (0, 0)`. It is tarentin, absolutely minimal and
causal, every point is in `Z^-` and `Z^+`, and `ℝ × ℝ` is Hausdorff and second countable: every
hypothesis of `prop:tarentin_fort_K` but causal plainness. At `o`:

* `B = {(t, x) : t < 0, -t < x}` is a causal bubble of `J^-(o)`: open, non-empty, in `J^-(o)`
  (`(t, x) ≪ (0, x)`, then the spoke) and disjoint from `I^-(o) = {|x| < -t}`
  (`spokesBubble_Ioi`, `spokes_bubble_witness`).
* `u_n = (-1/(n+1), 0) → o`, and `J^-(u_n) ⊆ {u_n} ∪ I^-(u_n)`: a spoke step ends on `t = 0`,
  above `u_n` (`spokes_eq_or_lt_of_le`). So `B ∩ J^-(u_n) = ∅` (`spokesBubble_inter_Jminus_approx`)
  and `B ∩ K^-(o) = ∅` (`spokesBubble_inter_Kminus`).
* The same computation gives `K^-(o) ⊆ I^-(o)`, and `I^-(o) ⊆ K^-(o)` holds as `≪` is open in
  `M × M`: `K^-(o) = I^-(o)` (`spokes_Kminus_origin_eq_Iminus`).
* Push-up fails at `o` itself, in both of the paper's senses: `Int J^-(o) ⊄ cl I^-(o)`
  (`spokes_not_plain_at_origin`) and `I^-(J^-(o)) ⊄ I^-(o)` (`spokes_not_pushUp_at_origin`).

So both the mechanism (`B` meets `K`) and the conclusion (`K ≠ I`) fail: the printed forms
`BubbleKminusAsPrinted`, `BubbleKplusAsPrinted` are false (`not_bubbleKminusAsPrinted`,
`not_bubbleKplusAsPrinted`; the `K^+` form, the one the remark prints, by time reversal), and so
are their conclusions alone, `BubbleKminusNeAsPrinted`, `BubbleKplusNeAsPrinted`
(`not_bubbleKminusNeAsPrinted`, `not_bubbleKplusNeAsPrinted`). The same holds on `ℝ × E` for
every open cone `A` (stable under positive dilations) with a non-zero point
(`spokes_bubble_witness`, `spokes_bubble_witness_future`), for `E` separable (e.g.
finite-dimensional), so that `ℝ × E` is second countable, e.g. on `ℝ × ℂ` with `A = ℂ ∖ {0}`
(`spokes_bubble_witness_complex`); there, by hand and not formalized, `J^-(o)` is the whole
closed lower half-space `t ≤ 0` while `K^-(o) = I^-(o)` is the open past cone.

**The true form** (`Causality.inter_Kminus_nonempty_iff`, from `lem:K_facile`): for `u_n → p`
with `p ∈ Int J^+(u_n)`, an open `B ⊆ J^-(p)` meets `K^-(p)` iff a non-empty open subset of `B`
lies in `J^-(u_n)` for all large `n`; such a sequence exists at every point of `Z^-` of a first
countable spacetime (`Causality.exists_seq_inter_Kminus_nonempty_iff`). When it does, a bubble
separates `K^-(p)` from `I^-(p)` (`Causality.Kminus_ne_Iminus_of_bubble`). It does on
`halfChronoLine` (`halfChronoLine_bubble_inter_Kminus`), not with the spoke. `K^+` forms by
time reversal.

## Hypothesis checklist (the witness against the printed bubble sentence)

| paper hypothesis | here |
|---|---|
| `M` a topological spacetime (`ETT.tex:254`): second countable, Hausdorff, `≪` open | ✓ carried by the witness (`ℝ × ℝ`, Minkowski's `≪`) |
| absolutely minimal (`ETT.tex:851`) | ✓ carried (`spokes_absolutelyMinimal`, `Ioi 0` a cone) |
| tarentin (`ETT.tex:851`) | ✓ carried (`spokes_tarentin`) |
| `p` strongly tarentin in the past (`ETT.tex:852`); `Z^+` for the `K^+` form | ✓ carried: `o ∈ Z^- ∩ Z^+` |
| causally plain (`ETT.tex:851`) | dropped, as the remark drops it; the witness is not causally plain |
| (not in the remark) causal | ✓ the witness is causal (`spokes_isCausal`) |
| "then `B` meets `K^+(p)` …, so `K^+(p) ≠ I^+(p)`" | ✗ refuted: `B ∩ K = ∅` and `K = I` |
| the true form (`inter_Kminus_nonempty_iff`): tarentin, absolute minimality, Hausdorff | ⚠ weakened: not used; a sequence `u_n → p`, `p ∈ Int J^+(u_n)`, or `p ∈ Z^-` and first countable |

## SCOPE (disclosed)

* Not marked. The bubble sentence is false as printed; its rewording is the author's. The BTZ
  sentence waits on OQ-34; the first sentence is certified elsewhere (`halfChronoLine`).
* The causal bubble is written out as the remark defines it (non-empty, open, in `J^±(p)`,
  disjoint from `I^±(p)`); up to the order of the conjuncts and `Disjoint` for `∩ = ∅`, it is
  `C.IsCausalBubble ⊤ {p} B` (future) or `C.dual.IsCausalBubble ⊤ {p} B` (past) of
  `Causal.Remarks.BTZPoints`, which this module does not import.
* The printed `Prop`s quantify over every library causality on a type of universe `0`; that the
  refutation holds for a local causal spacetime rests on the companion theorems
  (`spokes_bubble_witness`: absolutely minimal and causal, kb/0014, kb/0019).
* The `K^+` form is read with `p ∈ Z^+` (the hypothesis of the `K^+` analogue,
  `rem:comparable_property_obviously_holds`, `ETT.tex:868–869`); the witness has `o ∈ Z^-` as
  well, so the refutation does not depend on the reading.
* Nothing is claimed about the `C^0` metrics of Chruściel–Grant and Sämann that the remark
  cites: they are not in the library.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter

universe u

/-! ### The true form: when a bubble meets `K^±(p)` -/

namespace Causality

variable {M : Type u} [TopologicalSpace M] {C : Causality M} {U : Opens M} {p : M} {B : Set M}

/-- **When an open subset of `J^-_U(p)` meets `K^-_U(p)`** (`lem:K_facile`): for a sequence
`u n → p` with `p ∈ Int J^+_U(u n)`, an open `B ⊆ J^-_U(p)` meets `K^-_U(p)` iff a non-empty
open subset of `B` lies in `J^-_U(u n)` for every large `n`. -/
theorem inter_Kminus_nonempty_iff {u : ℕ → M} (hu : Tendsto u atTop (𝓝 p))
    (hp : ∀ n, p ∈ interior (C.Jplus U {u n})) (hB : IsOpen B) (hBJ : B ⊆ C.Jminus U {p}) :
    (B ∩ C.Kminus U {p}).Nonempty ↔
      ∃ N : ℕ, ∃ W : Set M, IsOpen W ∧ W.Nonempty ∧ W ⊆ B ∧ W ⊆ ⋂ n ≥ N, C.Jminus U {u n} := by
  rw [Kminus_eq_of_tendsto hu hp]
  constructor
  · rintro ⟨y, hyB, hyK⟩
    obtain ⟨N, hN⟩ := mem_iUnion.1 hyK
    obtain ⟨V, hVo, hyV, hVsub⟩ := mem_nhdsWithin.1 hN.2
    exact ⟨N, V ∩ B, hVo.inter hB, ⟨y, hyV, hyB⟩, inter_subset_right,
      fun z hz => hVsub ⟨hz.1, hBJ hz.2⟩⟩
  · rintro ⟨N, W, hWo, ⟨y, hyW⟩, hWB, hWsub⟩
    exact ⟨y, hWB hyW, mem_iUnion.2 ⟨N, mem_interiorWithin_of_mem_nhds (hBJ (hWB hyW))
      (mem_of_superset (hWo.mem_nhds hyW) hWsub)⟩⟩

/-- The `K^+` form of `inter_Kminus_nonempty_iff`, by time reversal. -/
theorem inter_Kplus_nonempty_iff {u : ℕ → M} (hu : Tendsto u atTop (𝓝 p))
    (hp : ∀ n, p ∈ interior (C.Jminus U {u n})) (hB : IsOpen B) (hBJ : B ⊆ C.Jplus U {p}) :
    (B ∩ C.Kplus U {p}).Nonempty ↔
      ∃ N : ℕ, ∃ W : Set M, IsOpen W ∧ W.Nonempty ∧ W ⊆ B ∧ W ⊆ ⋂ n ≥ N, C.Jplus U {u n} :=
  inter_Kminus_nonempty_iff (C := C.dual) hu hp hB hBJ

/-- A set disjoint from `I^-_U(p)` that meets `K^-_U(p)` separates them. -/
theorem Kminus_ne_Iminus_of_bubble (hBI : B ∩ C.Iminus U {p} = ∅)
    (h : (B ∩ C.Kminus U {p}).Nonempty) : C.Kminus U {p} ≠ C.Iminus U {p} := by
  intro hKI
  obtain ⟨y, hyB, hyK⟩ := h
  rw [hKI] at hyK
  exact notMem_empty y (hBI.subset ⟨hyB, hyK⟩)

/-- A set disjoint from `I^+_U(p)` that meets `K^+_U(p)` separates them. -/
theorem Kplus_ne_Iplus_of_bubble (hBI : B ∩ C.Iplus U {p} = ∅)
    (h : (B ∩ C.Kplus U {p}).Nonempty) : C.Kplus U {p} ≠ C.Iplus U {p} :=
  Kminus_ne_Iminus_of_bubble (C := C.dual) hBI h

/-- **At a point of `Z^-`**, under the hypotheses of `prop:tarentin_fort_K` that its proof
uses but plainness (a countable basis of neighbourhoods at `p`): there is a sequence
`u n ≪ p`, `u n → p`, such that an open `B ⊆ J^-(p)` meets `K^-(p)` iff a non-empty open subset
of `B` lies in `J^-(u n)` for every large `n`. -/
theorem exists_seq_inter_Kminus_nonempty_iff [FirstCountableTopology M] (hp : p ∈ C.Zminus) :
    ∃ u : ℕ → M, Tendsto u atTop (𝓝 p) ∧ (∀ n, C.lt ⊤ (u n) p) ∧
      ∀ B : Set M, IsOpen B → B ⊆ C.Jminus ⊤ {p} →
        ((B ∩ C.Kminus ⊤ {p}).Nonempty ↔
          ∃ N : ℕ, ∃ W : Set M, IsOpen W ∧ W.Nonempty ∧ W ⊆ B ∧
            W ⊆ ⋂ n ≥ N, C.Jminus ⊤ {u n}) := by
  obtain ⟨q, hq⟩ := Iminus_nonempty_of_mem_Zminus hp
  have hqp : C.lt ⊤ q p := by simpa using hq
  obtain ⟨u, -, -, hup, hu⟩ := exists_seq_lt_tendsto_of_mem_Zminus hp hqp
  refine ⟨u, hu, hup, fun B hB hBJ => inter_Kminus_nonempty_iff hu (fun n => ?_) hB hBJ⟩
  exact Iplus_subset_interior_Jplus (by simpa using hup n)

/-- The `K^+` form of `exists_seq_inter_Kminus_nonempty_iff`, at a point of `Z^+`. -/
theorem exists_seq_inter_Kplus_nonempty_iff [FirstCountableTopology M] (hp : p ∈ C.Zplus) :
    ∃ u : ℕ → M, Tendsto u atTop (𝓝 p) ∧ (∀ n, C.lt ⊤ p (u n)) ∧
      ∀ B : Set M, IsOpen B → B ⊆ C.Jplus ⊤ {p} →
        ((B ∩ C.Kplus ⊤ {p}).Nonempty ↔
          ∃ N : ℕ, ∃ W : Set M, IsOpen W ∧ W.Nonempty ∧ W ⊆ B ∧
            W ⊆ ⋂ n ≥ N, C.Jplus ⊤ {u n}) :=
  exists_seq_inter_Kminus_nonempty_iff (C := C.dual) hp

end Causality

/-- On `halfChronoLine` (`rem:K_neq_I`'s first sentence), the bubble `]-∞, -1[` of `J^-(0)`
meets `K^-(0)`: there the bubble sentence's mechanism does occur. -/
theorem halfChronoLine_bubble_inter_Kminus :
    (Iio (-1 : ℝ)).Nonempty ∧ IsOpen (Iio (-1 : ℝ)) ∧
      Iio (-1 : ℝ) ⊆ halfChronoLine.Jminus ⊤ {0} ∧
      Iio (-1 : ℝ) ∩ halfChronoLine.Iminus ⊤ {0} = ∅ ∧
      (Iio (-1 : ℝ) ∩ halfChronoLine.Kminus ⊤ {0}).Nonempty := by
  refine ⟨⟨-2, by norm_num⟩, isOpen_Iio, fun z hz => ?_, ?_, ⟨-2, by norm_num,
    halfChronoLine_neg_two_mem_Kminus⟩⟩
  · rw [halfChronoLine_Jminus_zero]
    exact (mem_Iio.1 hz).le.trans (by norm_num)
  · rw [halfChronoLine_Iminus_zero]
    refine eq_empty_of_forall_notMem fun z hz => ?_
    exact lt_asymm (mem_Iio.1 hz.1) (mem_Ioo.1 hz.2).1

/-! ### Minkowski space with spokes: a bubble that misses `K^-(o)` -/

section Bubble

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {A : Set E}

/-- The bubble `{(t, x) : t < 0, -t < ‖x‖, x ∈ A}`: the points of the open lower half-space
outside the past light cone of the origin, over the spokes. -/
def spokesBubble (A : Set E) : Set (ℝ × E) := {y | y.1 < 0 ∧ -y.1 < ‖y.2‖ ∧ y.2 ∈ A}

variable (E) in
/-- The sequence `u n = (-1/(n+1), 0)`, converging to the origin from its chronological past. -/
noncomputable def spokesApprox (n : ℕ) : ℝ × E := (-(1 / ((n : ℝ) + 1)), 0)

/-- Every point of `spokesCausality A` is strongly tarentin in the future: `≪` is that of
Minkowski space. -/
theorem spokes_mem_Zplus (x : ℝ × E) : x ∈ (spokesCausality A).Zplus :=
  staticCausality.mem_Zplus x

/-- **Below the slice `t = 0` a spoke cannot be used**: if `y.1 < 0`, then `x ≤ y` means `x = y`
or `x ≪ y`. -/
theorem spokes_eq_or_lt_of_le {x y : ℝ × E} (hy : y.1 < 0)
    (h : (spokesCausality A).le ⊤ x y) : x = y ∨ (spokesCausality A).lt ⊤ x y := by
  rw [spokesCausality.le_top_iff] at h
  rcases h with (⟨rfl, -⟩ | h) | ⟨a, b, -, hab, hby⟩
  · exact Or.inl rfl
  · exact Or.inr h
  · have := hby.fst_le
    rw [hab.2.1] at this
    linarith

/-- `I^-(o) = {(t, x) : ‖x‖ < -t}`. -/
theorem spokes_mem_Iminus_origin {y : ℝ × E} :
    y ∈ (spokesCausality A).Iminus ⊤ {((0 : ℝ), (0 : E))} ↔ ‖y.2‖ < -y.1 := by
  rw [Precausality.mem_Iminus_singleton, spokesCausality.lt_top_iff]
  simp

/-- **The bubble lies in `J^-(o)`**: `(t, x) ≪ (0, x)`, then the spoke from `(0, x)` to `o`. -/
theorem spokesBubble_subset_Jminus :
    spokesBubble A ⊆ (spokesCausality A).Jminus ⊤ {((0 : ℝ), (0 : E))} := by
  rintro ⟨t, x⟩ ⟨ht, -, hx⟩
  rw [Precausality.mem_Jminus_singleton]
  refine (spokesCausality A).le_trans ((spokesCausality A).le_of_lt ?_) (spokes_le_origin hx)
  rw [spokesCausality.lt_top_iff]
  simpa using ht

/-- **The bubble is disjoint from `I^-(o)`.** -/
theorem spokesBubble_inter_Iminus :
    spokesBubble A ∩ (spokesCausality A).Iminus ⊤ {((0 : ℝ), (0 : E))} = ∅ := by
  refine eq_empty_of_forall_notMem ?_
  rintro y ⟨⟨-, hy, -⟩, hI⟩
  rw [spokes_mem_Iminus_origin] at hI
  linarith

omit [NormedSpace ℝ E] in
theorem isOpen_spokesBubble (hA : IsOpen A) : IsOpen (spokesBubble A) := by
  exact (isOpen_lt continuous_fst continuous_const).inter
    ((isOpen_lt continuous_fst.neg continuous_snd.norm).inter (hA.preimage continuous_snd))

omit [NormedSpace ℝ E] in
theorem spokesBubble_nonempty {z : E} (hz : z ∈ A) (hz0 : z ≠ 0) :
    (spokesBubble A).Nonempty := by
  have h0 : 0 < ‖z‖ := norm_pos_iff.2 hz0
  refine ⟨(-(‖z‖ / 2), z), ?_, ?_, hz⟩
  · show -(‖z‖ / 2) < 0
    linarith
  · show -(-(‖z‖ / 2)) < ‖z‖
    linarith

omit [NormedSpace ℝ E] in
theorem tendsto_spokesApprox : Tendsto (spokesApprox E) atTop (𝓝 ((0 : ℝ), (0 : E))) := by
  have h : Tendsto (fun n : ℕ => -(1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
  exact h.prodMk_nhds tendsto_const_nhds

theorem spokesApprox_lt_origin (n : ℕ) :
    (spokesCausality A).lt ⊤ (spokesApprox E n) ((0 : ℝ), (0 : E)) := by
  rw [spokesCausality.lt_top_iff]
  simp only [spokesApprox, sub_self, norm_zero, zero_sub, neg_neg]
  positivity

/-- `J^-(u n) = {u n} ∪ I^-(u n) ⊆ I^-(o)`. -/
theorem spokes_Jminus_approx_subset (n : ℕ) :
    (spokesCausality A).Jminus ⊤ {spokesApprox E n} ⊆
      (spokesCausality A).Iminus ⊤ {((0 : ℝ), (0 : E))} := by
  intro y hy
  rw [Precausality.mem_Jminus_singleton] at hy
  rw [Precausality.mem_Iminus_singleton]
  have hn : (spokesApprox E n).1 < 0 := by
    show -(1 / ((n : ℝ) + 1)) < 0
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  rcases spokes_eq_or_lt_of_le hn hy with rfl | h
  · exact spokesApprox_lt_origin n
  · exact (spokesCausality A).lt_trans h (spokesApprox_lt_origin n)

/-- **The bubble misses every `J^-(u n)`.** -/
theorem spokesBubble_inter_Jminus_approx (n : ℕ) :
    spokesBubble A ∩ (spokesCausality A).Jminus ⊤ {spokesApprox E n} = ∅ := by
  exact subset_empty_iff.1 ((inter_subset_inter_right _ (spokes_Jminus_approx_subset n)).trans
    spokesBubble_inter_Iminus.subset)

theorem spokes_Kminus_origin_subset_Iminus :
    (spokesCausality A).Kminus ⊤ {((0 : ℝ), (0 : E))} ⊆
      (spokesCausality A).Iminus ⊤ {((0 : ℝ), (0 : E))} := by
  intro y hy
  obtain ⟨N, hN⟩ := Causality.mem_Kminus_singleton.1 hy _ tendsto_spokesApprox
  have hyN := interiorWithin_subset hN
  simp only [mem_inter_iff, mem_iInter] at hyN
  exact spokes_Jminus_approx_subset N (hyN.2 N le_rfl)

/-- `≪` is open in `M × M`. -/
theorem spokes_isOpen_lt :
    IsOpen {z : (ℝ × E) × (ℝ × E) | (spokesCausality A).lt ⊤ z.1 z.2} := by
  have : {z : (ℝ × E) × (ℝ × E) | (spokesCausality A).lt ⊤ z.1 z.2} =
      {z | ‖z.2.2 - z.1.2‖ < z.2.1 - z.1.1} := by
    ext z
    exact spokesCausality.lt_top_iff (A := A)
  rw [this]
  exact isOpen_lt (continuous_snd.snd.sub continuous_fst.snd).norm
    (continuous_snd.fst.sub continuous_fst.fst)

/-- `K^-(o) = I^-(o)`, with no causal plainness. -/
theorem spokes_Kminus_origin_eq_Iminus :
    (spokesCausality A).Kminus ⊤ {((0 : ℝ), (0 : E))} =
      (spokesCausality A).Iminus ⊤ {((0 : ℝ), (0 : E))} := by
  exact Subset.antisymm spokes_Kminus_origin_subset_Iminus
    (Causality.Iminus_subset_Kminus spokes_isOpen_lt)

/-- **The bubble misses `K^-(o)`.** -/
theorem spokesBubble_inter_Kminus :
    spokesBubble A ∩ (spokesCausality A).Kminus ⊤ {((0 : ℝ), (0 : E))} = ∅ := by
  rw [spokes_Kminus_origin_eq_Iminus]
  exact spokesBubble_inter_Iminus

/-- The bubble lies in `I^-(J^-(o))`: `(t, x) ≪ (0, x) ≤ o`. -/
theorem spokesBubble_subset_Iminus_Jminus :
    spokesBubble A ⊆
      (spokesCausality A).Iminus ⊤ ((spokesCausality A).Jminus ⊤ {((0 : ℝ), (0 : E))}) := by
  rintro ⟨t, x⟩ ⟨ht, -, hx⟩
  refine ⟨((0 : ℝ), x), Precausality.mem_Jminus_singleton.2 (spokes_le_origin hx), ?_⟩
  rw [spokesCausality.lt_top_iff]
  simpa using ht

/-- **Causal plainness fails at `o` itself** (`defi:causalement_plat` with `U = M`, `A = {o}`):
the bubble lies in `Int J^-(o)` and misses `cl I^-(o)`. -/
theorem spokes_not_plain_at_origin (hA : IsOpen A) {z : E} (hz : z ∈ A) (hz0 : z ≠ 0) :
    ¬ interior ((spokesCausality A).Jminus ⊤ {((0 : ℝ), (0 : E))}) ⊆
      closure ((spokesCausality A).Iminus ⊤ {((0 : ℝ), (0 : E))}) := by
  intro hP
  have hB := isOpen_spokesBubble hA
  obtain ⟨y, hy⟩ := spokesBubble_nonempty hz hz0
  have hint : y ∈ interior ((spokesCausality A).Jminus ⊤ {((0 : ℝ), (0 : E))}) :=
    interior_maximal spokesBubble_subset_Jminus hB hy
  obtain ⟨w, hwB, hwI⟩ := mem_closure_iff.1 (hP hint) _ hB hy
  exact notMem_empty w (spokesBubble_inter_Iminus.subset ⟨hwB, hwI⟩)

/-- **The push-up of `defi:pushup` fails at `o`** too: `I^-(J^-(o)) ⊄ I^-(o)`. -/
theorem spokes_not_pushUp_at_origin {z : E} (hz : z ∈ A) (hz0 : z ≠ 0) :
    ¬ (spokesCausality A).Iminus ⊤ ((spokesCausality A).Jminus ⊤ {((0 : ℝ), (0 : E))}) ⊆
      (spokesCausality A).Iminus ⊤ {((0 : ℝ), (0 : E))} := by
  intro h
  obtain ⟨y, hy⟩ := spokesBubble_nonempty hz hz0
  exact notMem_empty y (spokesBubble_inter_Iminus.subset
    ⟨hy, h (spokesBubble_subset_Iminus_Jminus hy)⟩)

/-- **The witness**, on `ℝ × E` for an open cone `A` with a non-zero point: at `o`, every
hypothesis of `prop:tarentin_fort_K` but causal plainness (second countability of `ℝ × E`
only for `E` separable, e.g. finite-dimensional: this theorem states no topological fact), and
causal; the bubble `spokesBubble A` of
`J^-(o)` misses every `J^-(u n)` and `K^-(o)`; `K^-(o) = I^-(o)`; not causally plain. -/
theorem spokes_bubble_witness (hAo : IsOpen A) (hAc : ∀ z ∈ A, ∀ c : ℝ, 0 < c → c • z ∈ A)
    {z : E} (hz : z ∈ A) (hz0 : z ≠ 0) :
    (spokesCausality A).Tarentin ∧ (spokesCausality A).AbsolutelyMinimal ∧
      (spokesCausality A).IsCausal ∧
      ((0 : ℝ), (0 : E)) ∈ (spokesCausality A).Zminus ∧
      ((0 : ℝ), (0 : E)) ∈ (spokesCausality A).Zplus ∧
      (spokesBubble A).Nonempty ∧ IsOpen (spokesBubble A) ∧
      spokesBubble A ⊆ (spokesCausality A).Jminus ⊤ {((0 : ℝ), (0 : E))} ∧
      spokesBubble A ∩ (spokesCausality A).Iminus ⊤ {((0 : ℝ), (0 : E))} = ∅ ∧
      (∀ n, spokesBubble A ∩ (spokesCausality A).Jminus ⊤ {spokesApprox E n} = ∅) ∧
      spokesBubble A ∩ (spokesCausality A).Kminus ⊤ {((0 : ℝ), (0 : E))} = ∅ ∧
      (spokesCausality A).Kminus ⊤ {((0 : ℝ), (0 : E))} =
        (spokesCausality A).Iminus ⊤ {((0 : ℝ), (0 : E))} ∧
      ¬ interior ((spokesCausality A).Jminus ⊤ {((0 : ℝ), (0 : E))}) ⊆
        closure ((spokesCausality A).Iminus ⊤ {((0 : ℝ), (0 : E))}) ∧
      ¬ (spokesCausality A).Iminus ⊤ ((spokesCausality A).Jminus ⊤ {((0 : ℝ), (0 : E))}) ⊆
        (spokesCausality A).Iminus ⊤ {((0 : ℝ), (0 : E))} ∧
      ¬ (spokesCausality A).CausallyPlain ∧ ¬ (spokesCausality A).PushUp := by
  have hpl := spokes_not_plain_at_origin hAo hz hz0
  have hpu := spokes_not_pushUp_at_origin hz hz0
  exact ⟨spokes_tarentin, spokes_absolutelyMinimal hAc, spokes_isCausal, spokes_mem_Zminus _,
    spokes_mem_Zplus _, spokesBubble_nonempty hz hz0, isOpen_spokesBubble hAo,
    spokesBubble_subset_Jminus, spokesBubble_inter_Iminus, spokesBubble_inter_Jminus_approx,
    spokesBubble_inter_Kminus, spokes_Kminus_origin_eq_Iminus, hpl, hpu,
    fun hP => hpl (hP ⊤ {((0 : ℝ), (0 : E))}).2,
    fun hP => hpu ((hP ⊤ ((0 : ℝ), (0 : E))).2.2)⟩

/-- **The witness, future form**: the time-reversed causality, with the same bubble, now a
bubble of `J^+(o)` that misses `K^+(o) = I^+(o)`. -/
theorem spokes_bubble_witness_future (hAo : IsOpen A)
    (hAc : ∀ z ∈ A, ∀ c : ℝ, 0 < c → c • z ∈ A) {z : E} (hz : z ∈ A) (hz0 : z ≠ 0) :
    (spokesCausality A).dual.Tarentin ∧ (spokesCausality A).dual.AbsolutelyMinimal ∧
      (spokesCausality A).dual.IsCausal ∧
      ((0 : ℝ), (0 : E)) ∈ (spokesCausality A).dual.Zplus ∧
      ((0 : ℝ), (0 : E)) ∈ (spokesCausality A).dual.Zminus ∧
      (spokesBubble A).Nonempty ∧ IsOpen (spokesBubble A) ∧
      spokesBubble A ⊆ (spokesCausality A).dual.Jplus ⊤ {((0 : ℝ), (0 : E))} ∧
      spokesBubble A ∩ (spokesCausality A).dual.Iplus ⊤ {((0 : ℝ), (0 : E))} = ∅ ∧
      spokesBubble A ∩ (spokesCausality A).dual.Kplus ⊤ {((0 : ℝ), (0 : E))} = ∅ ∧
      (spokesCausality A).dual.Kplus ⊤ {((0 : ℝ), (0 : E))} =
        (spokesCausality A).dual.Iplus ⊤ {((0 : ℝ), (0 : E))} ∧
      ¬ (spokesCausality A).dual.CausallyPlain := by
  obtain ⟨hT, hM, hC, hZm, hZp, hne, hB, hBJ, hBI, -, hBK, hKI, -, -, hP, -⟩ :=
    spokes_bubble_witness hAo hAc hz hz0
  exact ⟨Causality.dual_tarentin.2 hT, Causality.dual_absolutelyMinimal.2 hM,
    Causality.dual_isCausal.2 hC, hZm, hZp, hne, hB, hBJ, hBI, hBK, hKI,
    fun h => hP (Causality.dual_causallyPlain.1 h)⟩

end Bubble

/-! ### The planner's witness, `E = ℝ`, `A = ]0, +∞[`, and the `ℝ × ℂ` one -/

/-- On `ℝ × ℝ` with `A = ]0, +∞[` the bubble is `{(t, x) : t < 0, -t < x}`. -/
theorem spokesBubble_Ioi :
    spokesBubble (Ioi (0 : ℝ)) = {y : ℝ × ℝ | y.1 < 0 ∧ -y.1 < y.2} := by
  ext ⟨t, x⟩
  simp only [spokesBubble, mem_setOf_eq, mem_Ioi, Real.norm_eq_abs]
  constructor
  · rintro ⟨ht, hx, hx0⟩
    exact ⟨ht, by rwa [abs_of_pos hx0] at hx⟩
  · rintro ⟨ht, hx⟩
    have hx0 : 0 < x := by linarith
    exact ⟨ht, by rwa [abs_of_pos hx0], hx0⟩

/-- **Minkowski space `ℝ × ℝ` with one spoke** (`A = ]0, +∞[`): the witness. -/
theorem spokes_bubble_witness_real :
    (spokesCausality (Ioi (0 : ℝ))).Tarentin ∧ (spokesCausality (Ioi (0 : ℝ))).AbsolutelyMinimal ∧
      (spokesCausality (Ioi (0 : ℝ))).IsCausal ∧
      ((0 : ℝ), (0 : ℝ)) ∈ (spokesCausality (Ioi (0 : ℝ))).Zminus ∧
      ((0 : ℝ), (0 : ℝ)) ∈ (spokesCausality (Ioi (0 : ℝ))).Zplus ∧
      (spokesBubble (Ioi (0 : ℝ))).Nonempty ∧ IsOpen (spokesBubble (Ioi (0 : ℝ))) ∧
      spokesBubble (Ioi (0 : ℝ)) ⊆ (spokesCausality (Ioi (0 : ℝ))).Jminus ⊤ {((0 : ℝ), (0 : ℝ))} ∧
      spokesBubble (Ioi (0 : ℝ)) ∩ (spokesCausality (Ioi (0 : ℝ))).Iminus ⊤ {((0 : ℝ), (0 : ℝ))} =
        ∅ ∧
      (∀ n, spokesBubble (Ioi (0 : ℝ)) ∩
        (spokesCausality (Ioi (0 : ℝ))).Jminus ⊤ {spokesApprox ℝ n} = ∅) ∧
      spokesBubble (Ioi (0 : ℝ)) ∩ (spokesCausality (Ioi (0 : ℝ))).Kminus ⊤ {((0 : ℝ), (0 : ℝ))} =
        ∅ ∧
      (spokesCausality (Ioi (0 : ℝ))).Kminus ⊤ {((0 : ℝ), (0 : ℝ))} =
        (spokesCausality (Ioi (0 : ℝ))).Iminus ⊤ {((0 : ℝ), (0 : ℝ))} ∧
      ¬ (spokesCausality (Ioi (0 : ℝ))).CausallyPlain ∧
      ¬ (spokesCausality (Ioi (0 : ℝ))).PushUp := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, -, -, h13, h14⟩ :=
    spokes_bubble_witness (A := Ioi (0 : ℝ)) isOpen_Ioi
      (fun z hz c hc => by rw [mem_Ioi, smul_eq_mul]; exact mul_pos hc hz)
      (mem_Ioi.2 one_pos) one_ne_zero
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

/-- **The `ℝ × ℂ` witness** (`A = ℂ ∖ {0}`, spokes in every direction): the same conclusions. -/
theorem spokes_bubble_witness_complex :
    (spokesCausality ({0}ᶜ : Set ℂ)).Tarentin ∧
      (spokesCausality ({0}ᶜ : Set ℂ)).AbsolutelyMinimal ∧
      (spokesCausality ({0}ᶜ : Set ℂ)).IsCausal ∧
      ((0 : ℝ), (0 : ℂ)) ∈ (spokesCausality ({0}ᶜ : Set ℂ)).Zminus ∧
      (spokesBubble ({0}ᶜ : Set ℂ)).Nonempty ∧ IsOpen (spokesBubble ({0}ᶜ : Set ℂ)) ∧
      spokesBubble ({0}ᶜ : Set ℂ) ⊆
        (spokesCausality ({0}ᶜ : Set ℂ)).Jminus ⊤ {((0 : ℝ), (0 : ℂ))} ∧
      spokesBubble ({0}ᶜ : Set ℂ) ∩
        (spokesCausality ({0}ᶜ : Set ℂ)).Iminus ⊤ {((0 : ℝ), (0 : ℂ))} = ∅ ∧
      spokesBubble ({0}ᶜ : Set ℂ) ∩
        (spokesCausality ({0}ᶜ : Set ℂ)).Kminus ⊤ {((0 : ℝ), (0 : ℂ))} = ∅ ∧
      (spokesCausality ({0}ᶜ : Set ℂ)).Kminus ⊤ {((0 : ℝ), (0 : ℂ))} =
        (spokesCausality ({0}ᶜ : Set ℂ)).Iminus ⊤ {((0 : ℝ), (0 : ℂ))} := by
  obtain ⟨hT, hM, hC, hZm, -, hne, hB, hBJ, hBI, -, hBK, hKI, -⟩ :=
    spokes_bubble_witness (A := ({0}ᶜ : Set ℂ)) isOpen_compl_singleton
      (fun z hz c hc => smul_ne_zero hc.ne' hz) (z := 1) one_ne_zero one_ne_zero
  exact ⟨hT, hM, hC, hZm, hne, hB, hBJ, hBI, hBK, hKI⟩

/-! ### The printed bubble sentence, refuted -/

/-- `rem:K_neq_I`'s bubble sentence **as printed** (`ETT.tex:872–875`), in the past form of
`prop:tarentin_fort_K` and over its hypotheses without causal plainness (`ETT.tex:851–852`): on
an absolutely minimal, tarentin topological spacetime, at a point strongly tarentin in the past,
every causal bubble `B` of `J^-(p)` (non-empty, open, in `J^-(p)`, disjoint from `I^-(p)`) meets
`K^-(p)`, so `K^-(p) ≠ I^-(p)`. At universe `0`. Kept as a `Prop` for the finding (kb/0022). -/
def BubbleKminusAsPrinted : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [SecondCountableTopology M] [T2Space M] (C : Causality M),
    C.AbsolutelyMinimal → C.Tarentin → ∀ p ∈ C.Zminus, ∀ B : Set M,
      B.Nonempty → IsOpen B → B ⊆ C.Jminus ⊤ {p} → B ∩ C.Iminus ⊤ {p} = ∅ →
        (B ∩ C.Kminus ⊤ {p}).Nonempty ∧ C.Kminus ⊤ {p} ≠ C.Iminus ⊤ {p}

/-- `rem:K_neq_I`'s bubble sentence **as printed**, in the `K^+` form the remark prints
(`ETT.tex:872–875`), over the hypotheses of the `K^+` analogue of `prop:tarentin_fort_K`
(`rem:comparable_property_obviously_holds`) without causal plainness: every causal bubble `B` of
`J^+(p)` meets `K^+(p)`, so `K^+(p) ≠ I^+(p)`. At universe `0`. -/
def BubbleKplusAsPrinted : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [SecondCountableTopology M] [T2Space M] (C : Causality M),
    C.AbsolutelyMinimal → C.Tarentin → ∀ p ∈ C.Zplus, ∀ B : Set M,
      B.Nonempty → IsOpen B → B ⊆ C.Jplus ⊤ {p} → B ∩ C.Iplus ⊤ {p} = ∅ →
        (B ∩ C.Kplus ⊤ {p}).Nonempty ∧ C.Kplus ⊤ {p} ≠ C.Iplus ⊤ {p}

/-- The bubble sentence's conclusion alone (`ETT.tex:875`, « so `K^-(p) ≠ I^-(p)` »), past form:
under the same hypotheses, a causal bubble of `J^-(p)` separates `K^-(p)` from `I^-(p)`. Weaker
than `BubbleKminusAsPrinted`; kept to show that the conclusion fails too. At universe `0`. -/
def BubbleKminusNeAsPrinted : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [SecondCountableTopology M] [T2Space M] (C : Causality M),
    C.AbsolutelyMinimal → C.Tarentin → ∀ p ∈ C.Zminus, ∀ B : Set M,
      B.Nonempty → IsOpen B → B ⊆ C.Jminus ⊤ {p} → B ∩ C.Iminus ⊤ {p} = ∅ →
        C.Kminus ⊤ {p} ≠ C.Iminus ⊤ {p}

/-- The bubble sentence's conclusion alone, in the `K^+` form the remark prints. -/
def BubbleKplusNeAsPrinted : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [SecondCountableTopology M] [T2Space M] (C : Causality M),
    C.AbsolutelyMinimal → C.Tarentin → ∀ p ∈ C.Zplus, ∀ B : Set M,
      B.Nonempty → IsOpen B → B ⊆ C.Jplus ⊤ {p} → B ∩ C.Iplus ⊤ {p} = ∅ →
        C.Kplus ⊤ {p} ≠ C.Iplus ⊤ {p}

/-- **Finding: the bubble sentence is false as printed** (past form): Minkowski space `ℝ × ℝ`
with one spoke. -/
theorem not_bubbleKminusAsPrinted : ¬ BubbleKminusAsPrinted := by
  intro h
  obtain ⟨hT, hM, -, hZ, -, hne, hB, hBJ, hBI, -, hBK, -⟩ := spokes_bubble_witness_real
  obtain ⟨⟨y, hy⟩, -⟩ := h (ℝ × ℝ) (spokesCausality (Ioi (0 : ℝ))) hM hT _ hZ _ hne hB hBJ hBI
  exact notMem_empty y (hBK.subset hy)

/-- **Finding: the bubble sentence is false as printed** (the `K^+` form the remark prints), by
time reversal. -/
theorem not_bubbleKplusAsPrinted : ¬ BubbleKplusAsPrinted := by
  intro h
  obtain ⟨hT, hM, -, hZ, -, hne, hB, hBJ, hBI, hBK, -⟩ :=
    spokes_bubble_witness_future (A := Ioi (0 : ℝ)) isOpen_Ioi
      (fun z hz c hc => by rw [mem_Ioi, smul_eq_mul]; exact mul_pos hc hz)
      (mem_Ioi.2 one_pos) one_ne_zero
  obtain ⟨⟨y, hy⟩, -⟩ :=
    h (ℝ × ℝ) (spokesCausality (Ioi (0 : ℝ))).dual hM hT _ hZ _ hne hB hBJ hBI
  exact notMem_empty y (hBK.subset hy)

/-- **Finding: the bubble sentence's conclusion is false too** (past form): `K^-(o) = I^-(o)` at
the witness, which has a causal bubble of `J^-(o)`. -/
theorem not_bubbleKminusNeAsPrinted : ¬ BubbleKminusNeAsPrinted := by
  intro h
  obtain ⟨hT, hM, -, hZ, -, hne, hB, hBJ, hBI, -, -, hKI, -⟩ := spokes_bubble_witness_real
  exact h (ℝ × ℝ) (spokesCausality (Ioi (0 : ℝ))) hM hT _ hZ _ hne hB hBJ hBI hKI

/-- **Finding: the bubble sentence's conclusion is false too** (the `K^+` form), by time
reversal. -/
theorem not_bubbleKplusNeAsPrinted : ¬ BubbleKplusNeAsPrinted := by
  intro h
  obtain ⟨hT, hM, -, hZ, -, hne, hB, hBJ, hBI, -, hKI, -⟩ :=
    spokes_bubble_witness_future (A := Ioi (0 : ℝ)) isOpen_Ioi
      (fun z hz c hc => by rw [mem_Ioi, smul_eq_mul]; exact mul_pos hc hz)
      (mem_Ioi.2 one_pos) one_ne_zero
  exact h (ℝ × ℝ) (spokesCausality (Ioi (0 : ℝ))).dual hM hT _ hZ _ hne hB hBJ hBI hKI

end Causal
