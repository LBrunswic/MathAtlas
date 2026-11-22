import Causal.GluingGeneric.Basic
import Causal.Chains

/-!
# Gluing in its hereditary form, generic constructions (5): the causality of a linear order

No label of `ETT.tex` is marked by this file (target `T-abs-gluing-generic`, DEC-167 step 1a).
Cited, unmarked: `def:causal_chain` — `ETT.tex:329`.

> A causal chain is an embedding $c:(X,\leq) \rightarrow M$ where $(X,\leq)$ is linearly ordered and
> endowed with the order topology, and where $c$ is a causal morphism. (`ETT.tex:331`)

`linearCausality X` (`Causal.Chains`, `def:causal_chain` (1), reading (a)) is the causality of a
linearly ordered space: `x ≤_W y` iff `x ≤ y` and `[x, y] ⊆ W`; no chronology. On `ℝ` it is the
lightlike line (`linearCausality_real`).

## What is proved (no `sorry` in this file)

* `linearCausality_absolutelyMinimalOn_all`: in the order topology, if every closed interval is
  preconnected, `linearCausality X` is absolutely minimal on every open set (hereditary form);
  `linearCausality_absolutelyMinimalOn_all_of_dense` for a densely ordered conditionally complete
  linear order (e.g. `ℝ`). The step is `GluingGeneric.reflTransGen_union` (a relation chaining the
  ordered pairs of two intervals sharing a point chains those of their union) with mathlib's
  `IsPreconnected.induction₂'`.
* **The hypothesis cannot be dropped**: `linearCausality ℤ` is not absolutely minimal
  (`linearCausality_int_not_absolutelyMinimal`; M-only form, so neither form), by the jump lemma.
  The library already has the same for `ℚ` (`Causal.rat_not_absolutelyMinimal`,
  `Causal.ChainsCurves`).

## Hypothesis checklist

| the construction | here |
|---|---|
| `X` linearly ordered, with the order topology | ✓ carried (`OrderTopology X`) |
| — | ⚠ added for the positive half: every `Icc a b` preconnected (the counterexample `ℤ` shows it is needed) |

## SCOPE (disclosed)

* The other `Causal.Chains` constructions (`bowtie`, `fan`, `totalLine`, `diagonalCausality`) are
  `Causality.ofRelation` sites, treated in `Causal.GluingGeneric.OfRelation`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Relation Filter

universe v

namespace GluingGeneric

/-- A relation chaining every ordered pair of `I` and every ordered pair of `J`, two order-connected
sets sharing a point, chains every ordered pair of `I ∪ J`. -/
theorem reflTransGen_union {X : Type v} [LinearOrder X] {r : X → X → Prop} {I J : Set X}
    (hI : I.OrdConnected) (hJ : J.OrdConnected) {b : X} (hbI : b ∈ I) (hbJ : b ∈ J)
    (h₁ : ∀ u ∈ I, ∀ v ∈ I, u ≤ v → ReflTransGen r u v)
    (h₂ : ∀ u ∈ J, ∀ v ∈ J, u ≤ v → ReflTransGen r u v) :
    ∀ u ∈ I ∪ J, ∀ v ∈ I ∪ J, u ≤ v → ReflTransGen r u v := by
  intro u hu v hv huv
  rcases lt_or_ge b u with hbu | hub
  · rcases hv with hvI | hvJ
    · exact h₁ u (hI.out hbI hvI ⟨hbu.le, huv⟩) v hvI huv
    · exact h₂ u (hJ.out hbJ hvJ ⟨hbu.le, huv⟩) v hvJ huv
  · rcases lt_or_ge v b with hvb | hbv
    · rcases hu with huI | huJ
      · exact h₁ u huI v (hI.out huI hbI ⟨huv, hvb.le⟩) huv
      · exact h₂ u huJ v (hJ.out huJ hbJ ⟨huv, hvb.le⟩) huv
    · have h1 : ReflTransGen r u b := by
        rcases hu with huI | huJ
        · exact h₁ u huI b hbI hub
        · exact h₂ u huJ b hbJ hub
      have h2 : ReflTransGen r b v := by
        rcases hv with hvI | hvJ
        · exact h₁ b hbI v hvI hbv
        · exact h₂ b hbJ v hvJ hbv
      exact h1.trans h2

end GluingGeneric

variable {X : Type v} [LinearOrder X] [TopologicalSpace X]

/-- **The causality of a linear order, hereditary form**: in the order topology, with preconnected
closed intervals, `linearCausality X` is absolutely minimal on every open set. -/
theorem linearCausality_absolutelyMinimalOn_all [OrderTopology X]
    (hIcc : ∀ a b : X, IsPreconnected (Icc a b)) (W : Opens X) :
    (linearCausality X).AbsolutelyMinimalOn W := by
  intro S hS V hV x y
  refine ⟨fun hxy => ?_, fun hxy => False.elim hxy⟩
  obtain ⟨hxy, hsub⟩ := hxy
  have hP : ∀ u ∈ uIcc x y, ∀ v ∈ uIcc x y, u ≤ v →
      ReflTransGen (fun a b => ∃ O ∈ S, (linearCausality X).le (V ⊓ O) a b) u v := by
    refine (hIcc x y).induction₂' (fun a b => ∀ u ∈ uIcc a b, ∀ v ∈ uIcc a b, u ≤ v →
      ReflTransGen (fun a b => ∃ O ∈ S, (linearCausality X).le (V ⊓ O) a b) u v) ?_ ?_
      (left_mem_Icc.2 hxy) (right_mem_Icc.2 hxy)
    · intro a ha
      obtain ⟨O, hO, haO⟩ := hS a (hV (hsub ha))
      have hN : ((V ⊓ O : Opens X) : Set X) ∈ 𝓝 a := (V ⊓ O).isOpen.mem_nhds ⟨hsub ha, haO⟩
      obtain ⟨b, c, habc, hbc, hbcN⟩ := exists_Icc_mem_subset_of_mem_nhds hN
      have hloc : ∀ b' ∈ Icc b c, ∀ u ∈ uIcc a b', ∀ v ∈ uIcc a b', u ≤ v →
          ReflTransGen (fun a b => ∃ O ∈ S, (linearCausality X).le (V ⊓ O) a b) u v := by
        intro b' hb' u hu v hv huv
        have hsubbc : uIcc a b' ⊆ Icc b c := uIcc_subset_Icc habc hb'
        exact ReflTransGen.single
          ⟨O, hO, huv, (Icc_subset_Icc (hsubbc hu).1 (hsubbc hv).2).trans hbcN⟩
      filter_upwards [mem_nhdsWithin_of_mem_nhds hbc] with b' hb'
      exact ⟨hloc b' hb', by rw [uIcc_comm]; exact hloc b' hb'⟩
    · intro a b c _ _ _ hab hbc u hu v hv huv
      exact GluingGeneric.reflTransGen_union ordConnected_uIcc ordConnected_uIcc right_mem_uIcc
        left_mem_uIcc hab hbc u (uIcc_subset_uIcc_union_uIcc hu) v
        (uIcc_subset_uIcc_union_uIcc hv) huv
  rcases reflTransGen_iff_eq_or_transGen.1 (hP x left_mem_uIcc y right_mem_uIcc hxy) with h | h
  · rw [h]
    have hx : x ∈ V := hsub (left_mem_Icc.2 hxy)
    obtain ⟨O, hO, hxO⟩ := hS x (hV hx)
    refine TransGen.single ⟨O, hO, le_rfl, fun z hz => ?_⟩
    rw [Icc_self, mem_singleton_iff] at hz
    subst hz
    exact ⟨hx, hxO⟩
  · exact h

theorem linearCausality_absolutelyMinimalOn_all_of_dense {X : Type v}
    [ConditionallyCompleteLinearOrder X] [DenselyOrdered X] [TopologicalSpace X] [OrderTopology X]
    (W : Opens X) : (linearCausality X).AbsolutelyMinimalOn W :=
  linearCausality_absolutelyMinimalOn_all (fun _ _ => isPreconnected_Icc) W

/-- **Without connected intervals the causality of a linear order does not glue**: on `ℤ`
(discrete), `0 ≤ 1` with `[0, 1] = {0, 1}`, and no chain of steps inside `{0}` or `{1}` joins
them. -/
theorem linearCausality_int_not_absolutelyMinimal : ¬ (linearCausality ℤ).AbsolutelyMinimal := by
  intro h
  rw [Precausality.absolutelyMinimal_iff] at h
  let A : Opens ℤ := ⟨{0}, isOpen_discrete _⟩
  let B : Opens ℤ := ⟨{1}, isOpen_discrete _⟩
  have hcl : ∀ z ∈ (⊤ : Opens ℤ), z ∉ closure (A : Set ℤ) ∨ z ∉ closure (B : Set ℤ) := by
    intro z _
    have hA : closure (A : Set ℤ) = {0} := closure_discrete _
    have hB : closure (B : Set ℤ) = {1} := closure_discrete _
    rw [hA, hB]
    by_cases hz : z = 0
    · right; rw [hz]; simp
    · left; simpa using hz
  have hle : (linearCausality ℤ).le (A ⊔ B) 0 1 := by
    refine ⟨zero_le_one, fun z hz => ?_⟩
    have : z = 0 ∨ z = 1 := by
      obtain ⟨h0, h1⟩ := hz
      omega
    rcases this with rfl | rfl
    · exact Opens.mem_sup.2 (Or.inl rfl)
    · exact Opens.mem_sup.2 (Or.inr rfl)
  have h1 : (1 : ℤ) ∈ A := (h.mem_of_le_sup le_top le_top hcl (show (0 : ℤ) ∈ A from rfl)).1 hle
  exact absurd (show (1 : ℤ) = 0 from h1) (by norm_num)

end Causal
