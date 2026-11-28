import Causal.RationalLineExtras
import Causal.GluingModels.Minimal
import Causal.CExtConnexeCauchy.SubArc

/-!
# Inextensible nesting does not give ≤-nesting: the rational line in the spacelike line

No label of `ETT.tex` is certified here: the file is the programme target
`T-abs-inextensible-not-le-nested` (layer 1, `programme/roadmap.toml`), a ladder witness. It
settles the pair-sort `[[open]]` entry `inextensible_nested → le_nested`
(`programme/ladder.toml`, the last pair-sort `[[open]]`), argued there on the pointed line, which
is not absolutely minimal (`Causal.GluingModels.pointedLine_not_minimal`); the rational line has
the same mechanism and glues on `M` and on every open set.

* **The model-free lemma** (namespace `Causality`, any causality on any topological space, no
  instance argument): if every `C`-causal curve of `W` over a segment is constant, then
  `C.Inextensible W I c ↔ C.CausalCurveIn W I c`
  (`Causality.inextensible_iff_of_causalCurveOn_eq`; the implication alone,
  `Causality.inextensible_of_causalCurveOn_eq`). A strict extension is a causal curve, hence
  constant on its interval, and it takes the old values on the reparametrised `I`, which is
  non-empty, so its new point (`StrictlyExtends.grows`) is not new
  (`Causality.not_extensible_of_causalCurveOn_eq`).
* The nesting it gives: curve nesting into a causality whose causal curves of `W` are constant is
  inextensible nesting on `W` (`Causality.CurveNestedOn.inextensibleNestedOn_of_causalCurveOn_eq`);
  a causality whose causal curves of `W` are constant is curve-nested in every causality on `W`
  (`Causality.curveNestedOn_of_causalCurveOn_eq`); so two causalities whose causal curves of `W`
  are constant are inextensibly nested in each other on `W`
  (`Causality.inextensibleNestedOn_of_causalCurveOn_eq`).
* What the converse needs: on a T1, second countable space, inextensible nesting at `M` gives
  ≤-nesting when the narrower causality is causally arc-connected
  (`Causality.InextensibleNestedOn.leNested_of_causallyArcConnected`; on the opens of an open `W`,
  `Causality.InextensibleNestedOn.le_of_causallyArcConnectedOn`), through the library's
  `inextensible_nested ⇒ curve_nested` and the converse at `curve_nested`. So a counterexample on
  such a space has a narrower causality that is not causally arc-connected: the rational line is
  not (`rationalLine_not_causallyArcConnected`).
* **The witness** `rationalLine_separates_inextensibleNested`: the rational line is inextensibly
  nested in the spacelike line on every open set and not ≤-nested in it (`0 ≤ 1` in the first
  only); the rational line is causal, absolutely minimal, and absolutely minimal on every open
  set; the spacelike line is causal, causally arc-connected, absolutely minimal, and absolutely
  minimal on every open set. Both forms of DEC-167's gluing hold for both causalities, so the
  separation stands whichever form OQ-95 rules.
* Beside it: the spacelike line's causal curves are constant (`spacelikeLine_causalCurveOn_eq`),
  the nesting holds the other way too (`spacelikeLine_inextensibleNestedOn_rationalLine`), and the
  spacelike line is ≤-nested in the rational line (`spacelikeLine_leNested_rationalLine`): the two
  lines have the same inextensible curves on every open set and are ≤-nested one way only. The
  bare refutation: `not_leNested_of_inextensibleNestedOn_bare`.

> False, argued: the pointed line in the spacelike line (Causal.pointedLine, Causal.spacelikeLine).
> Both have the constant curves of W as their causal curves of W […], and no causal curve of either
> is extensible: a strict extension is a causal curve, hence constant, and takes the old value, so
> its new point (StrictlyExtends.grows) is not new; so the two have the same inextensible curves of
> every W and the pair is inextensibly nested on every open, while it is not ≤-nested
> (`programme/ladder.toml`, `[[open]] from = "inextensible_nested"`, `to = "le_nested"`)

## Hypothesis checklist

| ladder entry | here |
|---|---|
| `from = "inextensible_nested"`: `Causality.InextensibleNestedOn C C' W`, `C` narrower, `W = M` unless named | ✓ on every open `W`, `C = rationalLine`, `C' = spacelikeLine` |
| `to = "le_nested"`: `Causality.LeNested C C'` | ✓ refuted: `rationalLine.le ⊤ 0 1`, not `spacelikeLine.le ⊤ 0 1` |
| space (none: `ℝ` is Hausdorff and second countable) | ✓ `ℝ`, no instance argument |
| gluing (DEC-167, both forms of OQ-95) | ✓ `AbsolutelyMinimal` and `∀ W, AbsolutelyMinimalOn W`, for both causalities |
| the model-free lemma: "every causal curve of `W` constant" | ✓ carried as written, an inline `∀` over segment curves (no ladder node says it) |
| the converse (beyond the target): `C` causally arc-connected | ✓ a ladder node of `C`; `T1Space`, `SecondCountableTopology`, the standing of `InextensibleNestedOn.curveNestedOn_of_t1_secondCountable`; nothing of `C'` |

## SCOPE (disclosed)

* Nothing of `ETT.tex` is marked. The file assembles strict-library results
  (`Causal.NestedConverse`, `Causal.RationalLineExtras`, `Causal.NestedTransfer`,
  `Causal.GluingModels.Minimal`, `Causal.CExtConnexeCauchy.SubArc`) and proves the model-free lemma and the constancy of the
  spacelike line's causal curves. In the witness, `causal_ladder` gives three conjuncts through
  the ladder's edges: both lines causal from their time functions (`time_function ⇒ is_causal`),
  the spacelike line absolutely minimal from its causal arc-connectedness
  (`causally_arc_connected ⇒ absolutely_minimal`). It cannot give the others: the nestings are of
  the pair sort, which it does not read, and `AbsolutelyMinimalOn W` is no node.
* Imports: `Causal.RationalLineExtras` (which imports `Causal.Ladder.Rules`),
  `Causal.GluingModels.Minimal` and `Causal.CExtConnexeCauchy.SubArc`, all ETT layer. The file is a leaf: no module of the library may
  import it while it uses `causal_ladder` (kb/0221).
* The model-free lemma's hypothesis is not a ladder property: it is the statement's own
  ("every causal curve of `W` is constant"), written inline, not as a new definition.
* Not the pointed line: it is not absolutely minimal, so under DEC-167 it is no causality, and its
  separation would be a no-gluing witness.
* Curve nesting is not a conjunct: the rational line is curve-nested in every causality of `ℝ`
  (`rationalLine_curveNestedOn`), and the ladder's closure gives it on a T1, second countable `M`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace

universe u

namespace Causality

variable {M : Type u} [TopologicalSpace M] {C C' : Causality M} {W : Opens M} {I : Set ℝ}
  {c : ℝ → M}

/-! ## 1. Constant causal curves: every causal curve is inextensible -/

/-- A causal curve over an interval is constant on it when every causal curve of `W` over a
segment is constant on its segment. -/
theorem CausalCurveIn.eq_of_causalCurveOn_eq
    (hC : ∀ ⦃d : ℝ → M⦄ ⦃a b : ℝ⦄, C.CausalCurveOn W d a b →
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, d s = d t)
    (hc : C.CausalCurveIn W I c) {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) : c s = c t := by
  rcases le_total s t with hst | hst
  · exact hC (hc.curve s hs t ht) s (left_mem_Icc.2 hst) t (right_mem_Icc.2 hst)
  · exact hC (hc.curve t ht s hs) s (right_mem_Icc.2 hst) t (left_mem_Icc.2 hst)

/-- **No causal curve is extensible** when every causal curve of `W` is constant: the new point of
a strict extension takes the old value. -/
theorem not_extensible_of_causalCurveOn_eq
    (hC : ∀ ⦃d : ℝ → M⦄ ⦃a b : ℝ⦄, C.CausalCurveOn W d a b →
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, d s = d t)
    (hI : I.Nonempty) : ¬ C.Extensible W I c := by
  rintro ⟨I', c', hc', ⟨φ, -, hmaps, -, heq⟩, ⟨t', ht', hgrow⟩⟩
  obtain ⟨t, ht⟩ := hI
  exact hgrow t ht ((hc'.eq_of_causalCurveOn_eq hC ht' (hmaps ht)).trans (heq t ht))

/-- **The model-free lemma**: if every causal curve of `W` over a segment is constant, a curve of
`W` over `I` is inextensible iff it is a causal curve. -/
theorem inextensible_iff_of_causalCurveOn_eq
    (hC : ∀ ⦃d : ℝ → M⦄ ⦃a b : ℝ⦄, C.CausalCurveOn W d a b →
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, d s = d t) :
    C.Inextensible W I c ↔ C.CausalCurveIn W I c :=
  ⟨fun h => h.1, fun hc => ⟨hc, not_extensible_of_causalCurveOn_eq hC hc.nonempty⟩⟩

/-- If every causal curve of `W` is constant, every causal curve of `W` is inextensible. -/
theorem inextensible_of_causalCurveOn_eq
    (hC : ∀ ⦃d : ℝ → M⦄ ⦃a b : ℝ⦄, C.CausalCurveOn W d a b →
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, d s = d t)
    (hc : C.CausalCurveIn W I c) : C.Inextensible W I c :=
  (inextensible_iff_of_causalCurveOn_eq hC).2 hc

/-! ## 2. The nestings it gives -/

/-- A causality whose causal curves of `W` are constant is curve-nested in every causality on
`W` (a constant curve is causal in every causality). -/
theorem curveNestedOn_of_causalCurveOn_eq
    (hC : ∀ ⦃d : ℝ → M⦄ ⦃a b : ℝ⦄, C.CausalCurveOn W d a b →
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, d s = d t) (C' : Causality M) :
    CurveNestedOn C C' W :=
  fun _ _ _ hc => causalCurveOn_of_forall_eq hc.mem (hC hc)

/-- Curve nesting on `W` into a causality whose causal curves of `W` are constant is inextensible
nesting on `W`. -/
theorem CurveNestedOn.inextensibleNestedOn_of_causalCurveOn_eq (h : CurveNestedOn C C' W)
    (hC' : ∀ ⦃d : ℝ → M⦄ ⦃a b : ℝ⦄, C'.CausalCurveOn W d a b →
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, d s = d t) :
    InextensibleNestedOn C C' W :=
  fun _ _ hinext => inextensible_of_causalCurveOn_eq hC' (h.causalCurveIn hinext.1)

/-- **Two causalities whose causal curves of `W` are constant are inextensibly nested on `W`.** -/
theorem inextensibleNestedOn_of_causalCurveOn_eq
    (hC : ∀ ⦃d : ℝ → M⦄ ⦃a b : ℝ⦄, C.CausalCurveOn W d a b →
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, d s = d t)
    (hC' : ∀ ⦃d : ℝ → M⦄ ⦃a b : ℝ⦄, C'.CausalCurveOn W d a b →
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, d s = d t) :
    InextensibleNestedOn C C' W :=
  (curveNestedOn_of_causalCurveOn_eq hC C').inextensibleNestedOn_of_causalCurveOn_eq hC'

/-! ## 3. What the converse needs: the narrower causality causally arc-connected -/

/-- **Inextensible nesting on `W` gives ≤-nesting on the opens of `W` when the narrower causality
is causally arc-connected on `W`**, on a T1, second countable space: inextensible nesting gives
curve nesting (`InextensibleNestedOn.curveNestedOn_of_t1_secondCountable`), which gives ≤-nesting
under causal arc-connectedness (`CurveNestedOn.le_of_causallyArcConnectedOn`). Nothing is asked of
`C'`. -/
theorem InextensibleNestedOn.le_of_causallyArcConnectedOn [T1Space M]
    [SecondCountableTopology M] (h : InextensibleNestedOn C C' W)
    (hC : C.CausallyArcConnectedOn W) {U : Opens M} (hU : U ≤ W) {x y : M} (hxy : C.le U x y) :
    C'.le U x y :=
  h.curveNestedOn_of_t1_secondCountable.le_of_causallyArcConnectedOn hC hU hxy

/-- **Inextensible nesting at `M` gives ≤-nesting when the narrower causality is causally
arc-connected**, on a T1, second countable space. The rational line is not causally
arc-connected (`rationalLine_not_causallyArcConnected`). -/
theorem InextensibleNestedOn.leNested_of_causallyArcConnected [T1Space M]
    [SecondCountableTopology M] (h : InextensibleNestedOn C C' ⊤) (hC : C.CausallyArcConnected) :
    LeNested C C' :=
  h.curveNestedOn_of_t1_secondCountable.leNested_of_causallyArcConnected hC

end Causality

/-! ## 4. The rational line and the spacelike line -/

/-- **A causal curve of the spacelike line is constant** on its segment (`≤_U` is equality). -/
theorem spacelikeLine_causalCurveOn_eq {W : Opens ℝ} {c : ℝ → ℝ} {a b : ℝ}
    (hc : spacelikeLine.CausalCurveOn W c a b) {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    c s = c t := by
  rcases le_total s t with hst | hst
  · exact (spacelikeLine_le.1 (hc.le_of_le hs.1 hst ht.2)).1
  · exact (spacelikeLine_le.1 (hc.le_of_le ht.1 hst hs.2)).1.symm

/-- The rational line is inextensibly nested in the spacelike line, on every open set. -/
theorem rationalLine_inextensibleNestedOn_spacelikeLine (W : Opens ℝ) :
    rationalLine.InextensibleNestedOn spacelikeLine W :=
  Causality.inextensibleNestedOn_of_causalCurveOn_eq
    (fun _ _ _ hc _ hs _ ht => rationalLine_causalCurveOn_eq hc hs ht)
    (fun _ _ _ hc _ hs _ ht => spacelikeLine_causalCurveOn_eq hc hs ht)

/-- The spacelike line is inextensibly nested in the rational line, on every open set: the two
lines have the same inextensible curves. -/
theorem spacelikeLine_inextensibleNestedOn_rationalLine (W : Opens ℝ) :
    spacelikeLine.InextensibleNestedOn rationalLine W :=
  Causality.inextensibleNestedOn_of_causalCurveOn_eq
    (fun _ _ _ hc _ hs _ ht => spacelikeLine_causalCurveOn_eq hc hs ht)
    (fun _ _ _ hc _ hs _ ht => rationalLine_causalCurveOn_eq hc hs ht)

/-- The spacelike line is ≤-nested in the rational line (its `≤_U` is the diagonal of `U`). -/
theorem spacelikeLine_leNested_rationalLine : spacelikeLine.LeNested rationalLine :=
  fun _ _ _ h => Or.inl h

/-- **Inextensible nesting at `M` does not give ≤-nesting.** -/
theorem not_leNested_of_inextensibleNestedOn_bare :
    ¬ ∀ C C' : Causality ℝ, C.InextensibleNestedOn C' ⊤ → C.LeNested C' :=
  fun h => rationalLine_not_leNested_spacelikeLine
    (h _ _ (rationalLine_inextensibleNestedOn_spacelikeLine ⊤))

/-- **The witness for `inextensible_nested ⇏ le_nested`** (`programme/ladder.toml`, pair sort,
`from = "inextensible_nested"`, `to = "le_nested"`): the rational line is inextensibly nested in
the spacelike line on every open set and not ≤-nested in it; the rational line is causal and glues
on `M` and on every open set; the spacelike line is causal, causally arc-connected, and glues on
`M` and on every open set (DEC-167, either form of OQ-95). -/
theorem rationalLine_separates_inextensibleNested :
    (∀ W : Opens ℝ, rationalLine.InextensibleNestedOn spacelikeLine W) ∧
      ¬ rationalLine.LeNested spacelikeLine ∧ rationalLine.IsCausal ∧
      rationalLine.AbsolutelyMinimal ∧ (∀ W : Opens ℝ, rationalLine.AbsolutelyMinimalOn W) ∧
      spacelikeLine.IsCausal ∧ spacelikeLine.CausallyArcConnected ∧
      spacelikeLine.AbsolutelyMinimal ∧ ∀ W : Opens ℝ, spacelikeLine.AbsolutelyMinimalOn W := by
  -- the ladder's edges give causality from a time function and absolute minimality from causal
  -- arc-connectedness
  have hrt := rationalLine_hasTimeFunction
  have hst := spacelikeLine_hasTimeFunction
  have hsa := spacelikeLine_causallyArcConnected
  have hrc : rationalLine.IsCausal := by causal_ladder
  have hsc : spacelikeLine.IsCausal := by causal_ladder
  have hsm : spacelikeLine.AbsolutelyMinimal := by causal_ladder
  exact ⟨rationalLine_inextensibleNestedOn_spacelikeLine, rationalLine_not_leNested_spacelikeLine,
    hrc, rationalLine_absolutelyMinimal, rationalLine_absolutelyMinimalOn, hsc, hsa, hsm,
    GluingModels.spacelikeLine_hereditary⟩

end Causal
