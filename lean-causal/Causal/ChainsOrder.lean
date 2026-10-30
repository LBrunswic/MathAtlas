import Causal.ChainsCurves
import Mathlib.Order.Zorn
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Causal completeness by maximal chains of the causal order (DEC-21, DEC-22)

**`def:causally_complete`** — `ETT.tex:353`, as ruled by DEC-21.
**`rem:causal_completeness_slightly_weaker`** — `ETT.tex:356`, under the hypotheses of DEC-22.

> $M$ is causally complete if every maximal causal chain is Dedekind-complete \cite{MR1631533}.

> Causal completeness is slightly weaker than causal compactness.

DEC-21 (the author): "My mindset was Dedekind construction of real numbers: its not a matter or
curves but a matter of maximal totally ordered subsets having sections (totally ordered subsets
that are locally maximal in the sense that if a point of the ambient space cut the section in two
pieces those above those below, then the point is in the section) all sections have a lower/upper
bound". DEC-22: the remark carries T2, tarentin, causal, causally arc-connected, `J^±(p) ≠ {p}`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| maximal causal chain | ✓ DEC-21: `IsMaxChain (C.le ⊤) S`, a totally ordered `S` containing every point comparable to all of `S` |
| Dedekind-complete | ✓ every cut of `S` has its bound in `S` (`dedekindComplete_iff_cuts`), i.e. `DedekindComplete` of `Causal.Chains` |
| remark, compact ⇒ complete: T2, tarentin, causal (DEC-22) | ✓ carried (`causallyCompleteOrder_of_causallyCompact`) |
| — causally arc-connected, `J^±(p) ≠ {p}` (DEC-22) | ⚠ weakened: not used |
| remark, not conversely, under DEC-22 | ✓ local witness `ℝ × C([0,1], ℝ)`: second countable, absolutely minimal, **not locally compact** (`not_causallyCompleteOrder_imp_causallyCompact`) |
| second countable Hausdorff (`ETT.tex:255`) | ✓ in the witness; ⚠ weakened (not used) for compact ⇒ complete |

## SCOPE (disclosed)

* **(a) The definition.** `CausallyCompleteOrder`: every maximal chain `S` of the preorder
  `(M, ≤_M)` (mathlib `IsMaxChain`) is Dedekind-complete: every non-empty part bounded above in
  `S` has a least upper bound in `S`, equivalently every cut `S = L ⊔ U` (`L`, `U` non-empty,
  `L ≤ U`) has a greatest element of `L` or a least of `U` (`dedekindComplete_iff_cuts`). Maximal
  chains exist through every chain (Zorn, `IsChain.exists_maxChain`), and, unlike the maximal
  chains of `Causal.Chains`, are not dense: the definition is not vacuous. `IsMaxChain` is
  DEC-21's "every point comparable to all of `S` lies in `S`" (`isMaxChain_iff_comparableClosed`);
  for a causal `C` the author's literal notion — only points cutting `S` into two non-empty pieces
  are asked to lie in `S` — gives the same completeness (`causallyCompleteOrder_iff_author`). For a
  non-causal `C`, `≤_M` is only a preorder and an `IsMaxChain` is total for it, not "totally
  ordered" in the author's sense.
* **(b) The proof of the remark.** A non-empty chain bounded above has a least upper bound in `M`
  (`HasChainSups`) when the diamonds are compact and `J^±(x)` closed (finite intersections in the
  compact `J(a₀, u)`); such a bound is comparable to all of a maximal chain, hence on it
  (`HasChainSups.causallyCompleteOrder`). A static spacetime over a complete geodesic space has
  `HasChainSups` (the spatial parts form a Cauchy sequence), proper or not; over `C([0,1], ℝ)`,
  separable, it is second countable and not causally compact (not locally compact either). The
  earlier witness `ℕ →ᵇ ℝ` is not second countable.
* **(c) Sanity.** The timelike line and Minkowski `ℝ^{1,n}` (every `n`) are causally complete:
  every maximal chain of `(ℝ^{1,n}, ≤)` is Dedekind-complete.
* **(d) Negative examples.** Local: the half-plane `ℝ × ]0,∞[` (an open subset of 1+1 Minkowski,
  its causality of curves); the two null rays `t + x = 1` and `t − x = 1` form a maximal chain of
  `(M, ≤)` whose cut at the missing corner `(1, 0)` has no bound (`halfPlane_not_causallyCompleteOrder`).
  Non-local (kb/0019): `ℚ` with its order (`rat_not_causallyCompleteOrder`; not absolutely
  minimal, not causally arc-connected: `rat_not_absolutelyMinimal`, `rat_not_causallyArcConnected`), which is causally
  complete for curves (`rat_causallyCompleteCurves`): reading (b) of `Causal.ChainsCurves`
  does not imply this notion. Whether this notion implies reading (b), or does under the
  hypotheses of DEC-22, is open; both follow from causal compactness under them, both fail on the
  half-plane.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter

open scoped BoundedContinuousFunction

universe u

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable (C : Causality M)

/-- **`def:causally_complete`, DEC-21.** Every maximal chain of the preorder `(M, ≤_M)` is
Dedekind-complete. -/
def CausallyCompleteOrder : Prop :=
  ∀ S : Set M, IsMaxChain (C.le ⊤) S → C.DedekindComplete S

/-- Every non-empty chain bounded above has a least upper bound in `M`. -/
def HasChainSups : Prop :=
  ∀ A : Set M, IsChain (C.le ⊤) A → A.Nonempty → (∃ b, ∀ a ∈ A, C.le ⊤ a b) →
    ∃ p, (∀ a ∈ A, C.le ⊤ a p) ∧ ∀ v, (∀ a ∈ A, C.le ⊤ a v) → C.le ⊤ p v

variable {C}

theorem dual_isMaxChain_le {S : Set M} : IsMaxChain (C.dual.le ⊤) S ↔ IsMaxChain (C.le ⊤) S :=
  ⟨fun h => h.symm, fun h => h.symm⟩

theorem dual_causallyCompleteOrder : C.dual.CausallyCompleteOrder ↔ C.CausallyCompleteOrder :=
  ⟨fun h S hS => dual_dedekindComplete.1 (h S (dual_isMaxChain_le.2 hS)),
    fun h S hS => dual_dedekindComplete.2 (h S (dual_isMaxChain_le.1 hS))⟩

/-! ### Dedekind completeness: suprema, and cuts -/

/-- `DedekindComplete`, with parts of `S` as sets of `M`. -/
theorem dedekindComplete_iff_isLUBOn {S : Set M} : C.DedekindComplete S ↔
    ∀ A ⊆ S, A.Nonempty → (∃ b ∈ S, ∀ a ∈ A, C.le ⊤ a b) → ∃ s, C.IsLUBOn S A s := by
  refine ⟨fun h A hA hne hb => ?_, dedekindComplete_of_isLUBOn⟩
  obtain ⟨a, ha⟩ := hne
  obtain ⟨b, hbS, hb⟩ := hb
  obtain ⟨s, hs1, hs2⟩ := dedekindComplete_iff.1 h {x : S | x.1 ∈ A} ⟨⟨a, hA ha⟩, ha⟩
    ⟨⟨b, hbS⟩, fun x hx => hb _ hx⟩
  exact ⟨s.1, s.2, fun a' ha' => hs1 ⟨a', hA ha'⟩ ha',
    fun s' hs' hub => hs2 ⟨s', hs'⟩ fun x hx => hub _ hx⟩

/-- **Dedekind completeness of a chain is the cut form of DEC-21**: every partition of `S` into a
non-empty lower part `L` and a non-empty upper part `U` has a greatest element of `L` or a least
element of `U`. -/
theorem dedekindComplete_iff_cuts {S : Set M} (hS : IsChain (C.le ⊤) S) : C.DedekindComplete S ↔
    ∀ L U : Set M, L ∪ U = S → Disjoint L U → L.Nonempty → U.Nonempty →
      (∀ l ∈ L, ∀ u ∈ U, C.le ⊤ l u) →
      (∃ l ∈ L, ∀ l' ∈ L, C.le ⊤ l' l) ∨ (∃ u ∈ U, ∀ u' ∈ U, C.le ⊤ u u') := by
  rw [dedekindComplete_iff_isLUBOn]
  constructor
  · intro h L U hLU _ hL ⟨u₀, hu₀⟩ hlu
    have hLS : L ⊆ S := hLU ▸ subset_union_left
    have hUS : U ⊆ S := hLU ▸ subset_union_right
    obtain ⟨s, hsS, hs1, hs2⟩ := h L hLS hL ⟨u₀, hUS hu₀, fun l hl => hlu l hl u₀ hu₀⟩
    rw [← hLU] at hsS
    rcases hsS with hsL | hsU
    · exact Or.inl ⟨s, hsL, hs1⟩
    · exact Or.inr ⟨s, hsU, fun u' hu' => hs2 u' (hUS hu') fun l hl => hlu l hl u' hu'⟩
  · intro h A hA ⟨a₀, ha₀⟩ ⟨b, hbS, hb⟩
    have key : ∀ a ∈ A, (∀ a' ∈ A, C.le ⊤ a' a) → ∃ s, C.IsLUBOn S A s :=
      fun a ha hub => ⟨a, hA ha, hub, fun _ _ hs' => hs' a ha⟩
    set U : Set M := {x | x ∈ S ∧ ∀ a ∈ A, C.le ⊤ a x} with hU
    set L : Set M := S \ U with hL
    have hbelow : ∀ l ∈ L, ∃ a ∈ A, C.le ⊤ l a ∧ ¬ C.le ⊤ a l := by
      intro l hl
      have : ¬ ∀ a ∈ A, C.le ⊤ a l := fun h' => hl.2 ⟨hl.1, h'⟩
      push Not at this
      obtain ⟨a, ha, hal⟩ := this
      have hne : l ≠ a := fun h' => hal (h' ▸ C.le_refl trivial)
      rcases hS hl.1 (hA ha) hne with h' | h'
      · exact ⟨a, ha, h', hal⟩
      · exact absurd h' hal
    by_cases hLe : L.Nonempty
    · have hlu : ∀ l ∈ L, ∀ u ∈ U, C.le ⊤ l u := fun l hl u hu => by
        obtain ⟨a, ha, hla, -⟩ := hbelow l hl
        exact C.le_trans hla (hu.2 a ha)
      have hcut := h L U (sdiff_union_of_subset fun x hx => hx.1) disjoint_sdiff_left hLe
        ⟨b, hbS, hb⟩ hlu
      rcases hcut with ⟨l, hlL, hmax⟩ | ⟨u, huU, hmin⟩
      · obtain ⟨a, ha, -, hal⟩ := hbelow l hlL
        by_cases haU : a ∈ U
        · exact key a ha haU.2
        · exact absurd (hmax a ⟨hA ha, haU⟩) hal
      · exact ⟨u, huU.1, huU.2, fun s' hs'S hs' => hmin s' ⟨hs'S, hs'⟩⟩
    · have ha₀U : a₀ ∈ U := by
        by_contra h'
        exact hLe ⟨a₀, hA ha₀, h'⟩
      exact key a₀ ha₀ ha₀U.2

/-! ### The reading of DEC-21 -/

variable (C) in
/-- DEC-21's sentence: `S` is totally ordered, and every point comparable to all of `S` lies in
`S`. -/
def IsComparableClosedChain (S : Set M) : Prop :=
  IsChain (C.le ⊤) S ∧ ∀ p, (∀ s ∈ S, C.le ⊤ s p ∨ C.le ⊤ p s) → p ∈ S

/-- **`IsMaxChain` is DEC-21's notion.** -/
theorem isMaxChain_iff_comparableClosed (S : Set M) :
    IsMaxChain (C.le ⊤) S ↔ C.IsComparableClosedChain S := by
  constructor
  · intro h
    refine ⟨h.1, fun p hp => ?_⟩
    have hch : IsChain (C.le ⊤) (insert p S) := h.1.insert fun s hs _ => (hp s hs).symm
    have := h.2 hch (subset_insert p S)
    rw [this]; exact mem_insert p S
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun T hT hST => subset_antisymm hST fun t ht => h2 t fun s hs => ?_⟩
    by_cases hst : s = t
    · subst hst; exact Or.inl (C.le_refl trivial)
    · exact hT (hST hs) ht hst

variable (C) in
/-- The author's literal sentence: `S` is totally ordered, and a point of `M` **cutting `S` into
two non-empty pieces**, those strictly below and those strictly above it, lies in `S`. -/
def IsAuthorChain (S : Set M) : Prop :=
  IsChain (C.le ⊤) S ∧ ∀ p, (∀ s ∈ S, C.le ⊤ s p ∨ C.le ⊤ p s) →
    (∃ s ∈ S, C.le ⊤ s p ∧ ¬ C.le ⊤ p s) → (∃ s ∈ S, C.le ⊤ p s ∧ ¬ C.le ⊤ s p) → p ∈ S

/-- **The two readings agree on causal spacetimes**: requiring every author-chain to be
Dedekind-complete is `CausallyCompleteOrder`. (Due to the WP-6b audit.) -/
theorem causallyCompleteOrder_iff_author (hc : C.IsCausal) :
    (∀ S, C.IsAuthorChain S → C.DedekindComplete S) ↔ C.CausallyCompleteOrder := by
  constructor
  · intro h S hS
    exact h S ⟨hS.1, fun p hp _ _ => ((isMaxChain_iff_comparableClosed S).1 hS).2 p hp⟩
  · intro h S hS
    obtain ⟨S', hS', hSS'⟩ := hS.1.exists_maxChain
    have hDC := h S' hS'
    rw [dedekindComplete_iff_cuts hS.1]
    intro L U hLU hdisj hL hU hlu
    have hLS : L ⊆ S := hLU ▸ subset_union_left
    have hUS : U ⊆ S := hLU ▸ subset_union_right
    set L' : Set M := {x | x ∈ S' ∧ ∃ l ∈ L, C.le ⊤ x l}
    set U' : Set M := S' \ L'
    rw [dedekindComplete_iff_cuts hS'.1] at hDC
    obtain ⟨u₀, hu₀⟩ := hU
    obtain ⟨l₀, hl₀⟩ := hL
    have hu₀U' : u₀ ∈ U' := by
      refine ⟨hSS' (hUS hu₀), fun ⟨_, l, hl, hul⟩ => ?_⟩
      have := hc hul (hlu l hl u₀ hu₀)
      subst this
      exact Set.disjoint_left.1 hdisj hl hu₀
    have hcomp : ∀ x ∈ S', ∀ y ∈ S', C.le ⊤ x y ∨ C.le ⊤ y x := fun x hx y hy => by
      by_cases hxy : x = y
      · subst hxy; exact Or.inl (C.le_refl trivial)
      · exact hS'.1 hx hy hxy
    have hL'U' : ∀ x ∈ L', ∀ y ∈ U', C.le ⊤ x y := by
      rintro x ⟨hx, l, hl, hxl⟩ y ⟨hy, hyL'⟩
      rcases hcomp x hx y hy with h' | h'
      · exact h'
      · exact absurd ⟨hy, l, hl, C.le_trans h' hxl⟩ hyL'
    rcases hDC L' U' (union_sdiff_cancel fun x hx => hx.1) disjoint_sdiff_right
      ⟨l₀, hSS' (hLS hl₀), l₀, hl₀, C.le_refl trivial⟩ ⟨u₀, hu₀U'⟩ hL'U' with
      ⟨p, ⟨hpS', l, hl, hpl⟩, hmax⟩ | ⟨p, ⟨hpS', hpL'⟩, hmin⟩
    · exact Or.inl ⟨l, hl, fun l' hl' =>
        C.le_trans (hmax l' ⟨hSS' (hLS hl'), l', hl', C.le_refl trivial⟩) hpl⟩
    · have hpl : ∀ l ∈ L, C.le ⊤ l p ∧ ¬ C.le ⊤ p l := fun l hl => by
        have hnot : ¬ C.le ⊤ p l := fun h' => hpL' ⟨hpS', l, hl, h'⟩
        rcases hcomp p hpS' l (hSS' (hLS hl)) with h' | h'
        · exact absurd h' hnot
        · exact ⟨h', hnot⟩
      have hpu : ∀ u ∈ U, C.le ⊤ p u := fun u hu =>
        hmin u ⟨hSS' (hUS hu), fun ⟨_, l, hl, hul⟩ => by
          have := hc hul (hlu l hl u hu); subst this
          exact Set.disjoint_left.1 hdisj hl hu⟩
      have hpS : p ∈ S := by
        by_cases hup : ∃ u ∈ U, C.le ⊤ u p
        · obtain ⟨u, hu, hup⟩ := hup
          rw [hc (hpu u hu) hup]; exact hUS hu
        · push Not at hup
          exact hS.2 p (fun s hs => by
              rw [← hLU] at hs
              rcases hs with hs | hs
              · exact Or.inl (hpl s hs).1
              · exact Or.inr (hpu s hs))
            ⟨l₀, hLS hl₀, hpl l₀ hl₀⟩
            ⟨u₀, hUS hu₀, hpu u₀ hu₀, hup u₀ hu₀⟩
      rw [← hLU] at hpS
      rcases hpS with hpL | hpU
      · exact absurd (hpl p hpL).1 (hpl p hpL).2
      · exact Or.inr ⟨p, hpU, hpu⟩

/-! ### Least upper bounds of chains give completeness -/

/-- If every non-empty chain bounded above has a least upper bound in `M`, every maximal chain is
Dedekind-complete: the bound is comparable to every point of the chain, hence on it. -/
theorem HasChainSups.causallyCompleteOrder (h : C.HasChainSups) : C.CausallyCompleteOrder := by
  intro S hS
  rw [dedekindComplete_iff_isLUBOn]
  rintro A hA hne ⟨b, -, hb⟩
  obtain ⟨p, hp1, hp2⟩ := h A (hS.1.mono hA) hne ⟨b, hb⟩
  have hcomp : ∀ s ∈ S, C.le ⊤ s p ∨ C.le ⊤ p s := by
    intro s hs
    by_cases hub : ∀ a ∈ A, C.le ⊤ a s
    · exact Or.inr (hp2 s hub)
    · push Not at hub
      obtain ⟨a, ha, has⟩ := hub
      have hne' : s ≠ a := fun h' => has (h' ▸ C.le_refl trivial)
      rcases hS.1 hs (hA ha) hne' with h' | h'
      · exact Or.inl (C.le_trans h' (hp1 a ha))
      · exact absurd h' has
  have hpS : p ∈ S := by
    have hch : IsChain (C.le ⊤) (insert p S) := hS.1.insert fun s hs _ => (hcomp s hs).symm
    have heq := hS.2 hch (subset_insert p S)
    rw [heq]
    exact mem_insert p S
  exact ⟨p, hpS, hp1, fun s' _ hs' => hp2 s' hs'⟩

/-- **Causally compact ⇒ chains have suprema**, when the causal futures and pasts of points are
closed, in a `T2` space: the supremum is a point of the compact `J(a₀, u)` above the chain and
below all its upper bounds, found by a directed intersection. -/
theorem hasChainSups_of_causallyCompact [T2Space M] (hJm : ∀ x, IsClosed (C.Jminus ⊤ {x}))
    (hJp : ∀ x, IsClosed (C.Jplus ⊤ {x})) (hK : C.CausallyCompact) : C.HasChainSups := by
  intro A hA ⟨a₀, ha₀⟩ ⟨u, hu⟩
  have hlarger : ∀ a ∈ A, ∀ a' ∈ A, ∃ m ∈ A, C.le ⊤ a m ∧ C.le ⊤ a' m := by
    intro a ha a' ha'
    by_cases h : a = a'
    · exact ⟨a, ha, C.le_refl trivial, h ▸ C.le_refl trivial⟩
    · rcases hA ha ha' h with h' | h'
      · exact ⟨a', ha', h', C.le_refl trivial⟩
      · exact ⟨a, ha, C.le_refl trivial, h'⟩
  set V : Set M := {v | ∀ a ∈ A, C.le ⊤ a v} with hV
  set K : Set M := C.diamond ⊤ a₀ u with hKdef
  set t : A → Set M := fun a => K ∩ (C.Jplus ⊤ {a.1} ∩ ⋂ v ∈ V, C.Jminus ⊤ {v}) with ht
  have hclosed : ∀ a : A, IsClosed (C.Jplus ⊤ {a.1} ∩ ⋂ v ∈ V, C.Jminus ⊤ {v}) := fun a =>
    (hJp _).inter (isClosed_biInter fun v _ => hJm v)
  have hmemt : ∀ a : A, ∀ m ∈ A, C.le ⊤ a₀ m → C.le ⊤ a.1 m → m ∈ t a := by
    intro a m hm h0 h1
    refine ⟨mem_diamond.2 ⟨h0, hu m hm⟩, Precausality.mem_Jplus_singleton.2 h1, ?_⟩
    exact mem_iInter₂.2 fun v hv => Precausality.mem_Jminus_singleton.2 (hv m hm)
  haveI : Nonempty A := ⟨⟨a₀, ha₀⟩⟩
  obtain ⟨p, hp⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t
    (fun a a' => by
      obtain ⟨m, hm, ham, ha'm⟩ := hlarger a.1 a.2 a'.1 a'.2
      refine ⟨⟨m, hm⟩, fun x hx => ⟨hx.1, Precausality.mem_Jplus_singleton.2 (C.le_trans ham
        (Precausality.mem_Jplus_singleton.1 hx.2.1)), hx.2.2⟩, fun x hx => ⟨hx.1,
        Precausality.mem_Jplus_singleton.2 (C.le_trans ha'm
        (Precausality.mem_Jplus_singleton.1 hx.2.1)), hx.2.2⟩⟩)
    (fun a => by
      obtain ⟨m, hm, h0, h1⟩ := hlarger a₀ ha₀ a.1 a.2
      exact ⟨m, hmemt a m hm h0 h1⟩)
    (fun a => (hK a₀ u).inter_right (hclosed a))
    (fun a => (hK a₀ u).isClosed.inter (hclosed a))
  have hp' := mem_iInter.1 hp
  refine ⟨p, fun a ha => Precausality.mem_Jplus_singleton.1 (hp' ⟨a, ha⟩).2.1, fun v hv => ?_⟩
  exact Precausality.mem_Jminus_singleton.1 (mem_iInter₂.1 (hp' ⟨a₀, ha₀⟩).2.2 v hv)

/-- **`rem:causal_completeness_slightly_weaker`, first half (DEC-21, DEC-22)**: a causally compact
`T2` tarentin causal spacetime is causally complete. Causal arc-connectedness and
`J^±(p) ≠ {p}` (DEC-22) are not used. -/
theorem causallyCompleteOrder_of_causallyCompact [T2Space M] (hT : C.Tarentin)
    (hcaus : C.IsCausal) (hK : C.CausallyCompact) : C.CausallyCompleteOrder :=
  have hG : C.GloballyHyperbolic := ⟨hcaus, hK⟩
  (hasChainSups_of_causallyCompact (hG.isClosed_Jminus_singleton hT)
    (hG.isClosed_Jplus_singleton hT) hK).causallyCompleteOrder

end Causality

/-! ### Static spacetimes over a complete space -/

namespace staticCausality

variable {X : Type u} [MetricSpace X] [GeodesicSpace X]

/-- **Over a complete `X`, chains bounded above have suprema**: the times of the chain increase to
`T`, the spatial parts of points chosen with time `> T − 1/(n+1)` form a Cauchy sequence, and its
limit `x` gives the supremum `(T, x)`. -/
theorem hasChainSups [CompleteSpace X] : (staticCausality X).HasChainSups := by
  intro A hA ⟨a₀, ha₀⟩ ⟨b, hb⟩
  have htime : ∀ x y : ℝ × X, (staticCausality X).le ⊤ x y → x.1 ≤ y.1 := fun x y h => by
    have := le_top_iff.1 h; linarith [dist_nonneg (x := x.2) (y := y.2)]
  have hbdd : BddAbove (Prod.fst '' A) := ⟨b.1, by rintro _ ⟨a, ha, rfl⟩; exact htime _ _ (hb a ha)⟩
  set T := sSup (Prod.fst '' A) with hT
  have hTa : ∀ a ∈ A, a.1 ≤ T := fun a ha => le_csSup hbdd ⟨a, ha, rfl⟩
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hex : ∀ n : ℕ, ∃ a ∈ A, T - 1 / ((n : ℝ) + 1) < a.1 := fun n => by
    obtain ⟨_, ⟨a, ha, rfl⟩, h⟩ := exists_lt_of_lt_csSup
      (⟨a₀.1, a₀, ha₀, rfl⟩ : (Prod.fst '' A).Nonempty)
      (show T - 1 / ((n : ℝ) + 1) < T by linarith [hpos n])
    exact ⟨a, ha, h⟩
  choose s hsA hsT using hex
  have hdist : ∀ a ∈ A, ∀ n : ℕ, dist a.2 (s n).2 ≤ T - a.1 + 1 / ((n : ℝ) + 1) := by
    intro a ha n
    have hcmp : (staticCausality X).le ⊤ a (s n) ∨ (staticCausality X).le ⊤ (s n) a := by
      by_cases h : a = s n
      · exact Or.inl (h ▸ (staticCausality X).le_refl trivial)
      · exact hA ha (hsA n) h
    rcases hcmp with h | h
    · have h1 := le_top_iff.1 h
      have h2 := hTa _ (hsA n)
      linarith [hpos n]
    · have h1 := le_top_iff.1 h
      rw [dist_comm] at h1
      have h2 := hTa a ha
      have h3 := hsT n
      linarith
  have hcauchy : CauchySeq fun n => (s n).2 := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt (half_pos hε)
    refine ⟨N, fun n hn => ?_⟩
    have h1 := hdist _ (hsA n) N
    have h2 := hsT n
    have h3 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hn)
    linarith
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hlim0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨(T, x), fun a ha => ?_, fun v hv => ?_⟩
  · rw [le_top_iff]
    have hl : Tendsto (fun n : ℕ => T - a.1 + 1 / ((n : ℝ) + 1)) atTop (𝓝 (T - a.1)) := by
      have := (tendsto_const_nhds (x := T - a.1)).add hlim0
      rwa [add_zero] at this
    exact le_of_tendsto_of_tendsto' (tendsto_const_nhds.dist hx) hl (hdist a ha)
  · rw [le_top_iff]
    have hl : Tendsto (fun n : ℕ => v.1 - T + 1 / ((n : ℝ) + 1)) atTop (𝓝 (v.1 - T)) := by
      have := (tendsto_const_nhds (x := v.1 - T)).add hlim0
      rwa [add_zero] at this
    refine le_of_tendsto_of_tendsto' (hx.dist tendsto_const_nhds) hl fun n => ?_
    have h1 := le_top_iff.1 (hv _ (hsA n))
    have h2 := hsT n
    show dist (s n).2 v.2 ≤ v.1 - T + 1 / ((n : ℝ) + 1)
    linarith

/-- **A static spacetime over a complete geodesic space is causally complete** (DEC-21), proper or
not. -/
theorem causallyCompleteOrder [CompleteSpace X] : (staticCausality X).CausallyCompleteOrder :=
  hasChainSups.causallyCompleteOrder

end staticCausality

/-! ### The remark, not conversely -/

/-- **`rem:causal_completeness_slightly_weaker`, "not conversely", under DEC-22, with a local
witness**: the static spacetime over `C([0, 1], ℝ)` is second countable, `T2`, tarentin, causal,
causally arc-connected, with `J^±(p) ≠ {p}`, absolutely minimal and strongly causal, causally
complete, and not causally compact. It is not locally compact. -/
theorem not_causallyCompleteOrder_imp_causallyCompact :
    ¬ ∀ (N : Type) [TopologicalSpace N] [T2Space N] [SecondCountableTopology N] (D : Causality N),
      D.Tarentin → D.IsCausal →
      D.CausallyArcConnected → (∀ p, D.Jminus ⊤ {p} ≠ {p}) → (∀ p, D.Jplus ⊤ {p} ≠ {p}) →
      D.AbsolutelyMinimal → D.StronglyCausal → D.CausallyCompleteOrder → D.CausallyCompact :=
  fun h => tentStatic_not_causallyCompact (h (ℝ × C(Icc (0 : ℝ) 1, ℝ)) (staticCausality _)
    staticCausality.tarentin staticCausality.isCausal staticCausality.causallyArcConnected
    staticCausality.Jminus_ne_singleton staticCausality.Jplus_ne_singleton
    staticCausality.absolutelyMinimal staticCausality.stronglyCausal
    staticCausality.causallyCompleteOrder)

/-! ### Sanity -/

/-- The timelike line is causally complete (DEC-21). -/
theorem timelikeLine_causallyCompleteOrder : timelikeLine.CausallyCompleteOrder :=
  Causality.causallyCompleteOrder_of_causallyCompact timelikeLine_tarentin timelikeLine_isCausal
    timelikeLine_globallyHyperbolic.2

/-- **Minkowski space is causally complete** (DEC-21): every maximal chain of `(ℝ^{1,n}, ≤)` is
Dedekind-complete. -/
theorem minkowski_causallyCompleteOrder {n : ℕ} : (minkowski n).CausallyCompleteOrder :=
  Causality.causallyCompleteOrder_of_causallyCompact minkowski_tarentin minkowski_isCausal
    minkowski_globallyHyperbolic.2

/-- Maximal chains of `(M, ≤)` exist through every chain (Zorn): the definition is not vacuous. -/
theorem exists_isMaxChain_le (C : Causality M) {A : Set M} (hA : IsChain (C.le ⊤) A) :
    ∃ S, IsMaxChain (C.le ⊤) S ∧ A ⊆ S :=
  hA.exists_maxChain

/-! ### A local negative example: the half-plane -/

section HalfPlane

local notation "H" => ℝ × Ioi (0 : ℝ)

/-- The causal relation of the half-plane in null coordinates `t + x`, `t − x`. -/
theorem halfPlane_le_iff {p q : H} : (staticCausality (Ioi (0 : ℝ))).le ⊤ p q ↔
    (p.1 + p.2 ≤ q.1 + q.2 ∧ p.1 - p.2 ≤ q.1 - q.2) := by
  rw [staticCausality.le_top_iff, Subtype.dist_eq, Real.dist_eq, abs_le]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- The two null rays `t + x = 1` and `t − x = 1` of the half-plane, meeting at the missing
corner `(1, 0)`. -/
def halfPlaneWedge : Set H := {p | p.1 + p.2 = 1 ∨ p.1 - p.2 = 1}

theorem halfPlaneWedge_isChain :
    IsChain ((staticCausality (Ioi (0 : ℝ))).le ⊤) halfPlaneWedge := by
  intro p hp q hq _
  simp only [halfPlane_le_iff]
  have hp0 : (0 : ℝ) < p.2 := p.2.2
  have hq0 : (0 : ℝ) < q.2 := q.2.2
  rcases hp with hp | hp <;> rcases hq with hq | hq
  · rcases le_total (q.1 : ℝ) p.1 with h | h
    · right; constructor <;> linarith
    · left; constructor <;> linarith
  · left; constructor <;> linarith
  · right; constructor <;> linarith
  · rcases le_total (q.1 : ℝ) p.1 with h | h
    · right; constructor <;> linarith
    · left; constructor <;> linarith

/-- A point of the half-plane. -/
def hpt (t x : ℝ) (hx : 0 < x) : H := (t, ⟨x, hx⟩)

/-- Every point comparable to all of the wedge is on it. -/
theorem mem_halfPlaneWedge_of_comparable {q : H}
    (hq : ∀ p ∈ halfPlaneWedge, (staticCausality (Ioi (0 : ℝ))).le ⊤ p q ∨
      (staticCausality (Ioi (0 : ℝ))).le ⊤ q p) : q ∈ halfPlaneWedge := by
  have hx : (0 : ℝ) < q.2 := q.2.2
  set t := q.1
  set x : ℝ := (q.2 : ℝ)
  by_contra hnot
  simp only [halfPlaneWedge, mem_setOf_eq, not_or] at hnot
  obtain ⟨hv, hw⟩ := hnot
  rcases lt_or_gt_of_ne hw with hw | hw
  · rcases lt_or_gt_of_ne hv with hv | hv
    · -- below the first ray: a point of it far in the past is incomparable
      set τ := (t - x - 1) / 2 - 1 with hτ
      have hpos : 0 < 1 - τ := by rw [hτ]; linarith
      have := hq (hpt τ (1 - τ) hpos) (Or.inl (by simp [hpt]))
      simp only [halfPlane_le_iff, hpt] at this
      rcases this with h | h <;> linarith [h.1, h.2]
    · -- between the rays: a point of the first ray close to the corner is incomparable
      set τ := ((t - x + 1) / 2 + 1) / 2 with hτ
      have hpos : 0 < 1 - τ := by rw [hτ]; linarith
      have := hq (hpt τ (1 - τ) hpos) (Or.inl (by simp [hpt]))
      simp only [halfPlane_le_iff, hpt] at this
      rcases this with h | h <;> linarith [h.1, h.2]
  · -- beyond the second ray: a point of it far in the future is incomparable
    have hpos : 0 < t + x := by linarith
    have := hq (hpt (1 + (t + x)) (t + x) hpos) (Or.inr (by simp [hpt]))
    simp only [halfPlane_le_iff, hpt] at this
    rcases this with h | h <;> linarith [h.1, h.2]

theorem halfPlaneWedge_isMaxChain :
    IsMaxChain ((staticCausality (Ioi (0 : ℝ))).le ⊤) halfPlaneWedge := by
  refine ⟨halfPlaneWedge_isChain, fun T hT hsub => subset_antisymm hsub fun q hqT => ?_⟩
  refine mem_halfPlaneWedge_of_comparable fun p hp => ?_
  by_cases h : p = q
  · exact Or.inl (h ▸ (staticCausality (Ioi (0 : ℝ))).le_refl trivial)
  · exact hT (hsub hp) hqT h

/-- **A local negative example** (DEC-21): the half-plane `ℝ × ]0,∞[` — causal, tarentin, strongly
causal, causally arc-connected, absolutely minimal — is not causally complete. Its maximal chain
`halfPlaneWedge` is cut at the missing corner: the first ray has upper bounds on the second, and
no least one. -/
theorem halfPlane_not_causallyCompleteOrder :
    ¬ (staticCausality (Ioi (0 : ℝ))).CausallyCompleteOrder := by
  intro h
  have hc := Causality.dedekindComplete_iff_isLUBOn.1 (h _ halfPlaneWedge_isMaxChain)
  obtain ⟨s, hsW, hs1, hs2⟩ := hc {p | p.1 + p.2 = 1} (fun p hp => Or.inl hp)
    ⟨hpt 0 1 one_pos, by simp [hpt]⟩
    ⟨hpt 2 1 one_pos, Or.inr (by simp [hpt]; norm_num), fun p hp => by
      have hp0 : (0 : ℝ) < p.2 := p.2.2
      simp only [mem_setOf_eq] at hp
      rw [halfPlane_le_iff]; simp only [hpt]; constructor <;> linarith⟩
  have hs0 : (0 : ℝ) < s.2 := s.2.2
  rcases hsW with hsv | hsw
  · -- `s` on the first ray: a later point of it is not below `s`
    have hpos : (0 : ℝ) < s.2 / 2 := by linarith
    have := hs1 (hpt (1 - s.2 / 2) (s.2 / 2) hpos) (by simp [hpt])
    rw [halfPlane_le_iff] at this
    simp only [hpt] at this
    linarith [this.1, this.2]
  · -- `s` on the second ray: a lower point of it is an upper bound not above `s`
    have hpos : (0 : ℝ) < s.2 / 2 := by linarith
    have := hs2 (hpt (1 + s.2 / 2) (s.2 / 2) hpos) (Or.inr (by simp [hpt])) fun p hp => by
      have hp0 : (0 : ℝ) < p.2 := p.2.2
      simp only [mem_setOf_eq] at hp
      rw [halfPlane_le_iff]; simp only [hpt]; constructor <;> linarith
    rw [halfPlane_le_iff] at this
    simp only [hpt] at this
    linarith [this.1, this.2]

end HalfPlane

/-! ### A non-local example: the rationals -/

/-- `ℚ` with the causality of its order (non-local, kb/0019) is not causally complete: its only
maximal chain is `ℚ`, cut at `√2`. -/
theorem rat_not_causallyCompleteOrder : ¬ (linearCausality ℚ).CausallyCompleteOrder := by
  intro h
  have hchain : IsChain ((linearCausality ℚ).le ⊤) univ := fun x _ y _ _ => by
    rcases le_total x y with hxy | hxy
    · exact Or.inl ⟨hxy, fun _ _ => trivial⟩
    · exact Or.inr ⟨hxy, fun _ _ => trivial⟩
  have hmax : IsMaxChain ((linearCausality ℚ).le ⊤) univ :=
    ⟨hchain, fun T _ hsub => subset_antisymm hsub (subset_univ T)⟩
  have hc := Causality.dedekindComplete_iff_isLUBOn.1 (h _ hmax)
  obtain ⟨s, -, hs1, hs2⟩ := hc {x : ℚ | (x : ℝ) < √2} (subset_univ _)
    ⟨0, by simp⟩ ⟨2, trivial, fun a ha => ⟨by
      have : (a : ℝ) < 2 := ha.trans (by
        rw [Real.sqrt_lt' (by norm_num)]; norm_num)
      exact_mod_cast this.le, fun _ _ => trivial⟩⟩
  have hirr := irrational_sqrt_two
  rcases lt_or_gt_of_ne (hirr.ne_rat s).symm with hlt | hgt
  · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
    have := (hs1 q hq2).1
    have : (q : ℝ) ≤ s := by exact_mod_cast this
    linarith
  · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hgt
    have := (hs2 q trivial fun a ha => ⟨by
      have : (a : ℝ) < q := ha.trans hq1
      exact_mod_cast this.le, fun _ _ => trivial⟩).1
    have : (s : ℝ) ≤ q := by exact_mod_cast this
    linarith

/-- On `ℚ` every inextensible causal curve is constant, so reading (b) holds:
`CausallyCompleteCurves` does not imply `CausallyCompleteOrder` (non-local witness). -/
theorem rat_causallyCompleteCurves : (linearCausality ℚ).CausallyCompleteCurves := by
  intro I c hc
  have hsub := rat_causalCurveIn_subsingleton hc.1
  have key : ∀ (D : Causality ℚ), D.SupCompleteIn (c '' I) := by
    intro D A hA ⟨a, ha⟩ _
    refine ⟨a, hA ha, fun a' ha' => ?_, fun s' hs' _ => ?_⟩
    · rw [hsub (hA ha') (hA ha)]; exact D.le_refl trivial
    · rw [hsub (hA ha) hs']; exact D.le_refl trivial
  exact ⟨key _, key _⟩

end Causal
