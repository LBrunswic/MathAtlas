import Causal.Morphism
import Causal.LinesReachable
import Mathlib.Topology.Order.T5

/-!
# Causal chains, maximal chains, causal connectedness and causal completeness

`def:causal_chain` — `ETT.tex:329`. `def:maximal_chain` — `ETT.tex:334`.
`def:causally_connected` — `ETT.tex:337`. `def:causally_complete` — `ETT.tex:353`.
`rem:causal_completeness_slightly_weaker` — `ETT.tex:356`.
None is marked: each definition rests on a reading (SCOPE (a)–(d)). Of the remark ("compact ⇒
complete, and not conversely"), the strictness half is confirmed (`fan`); the implication is
refuted only for non-local causalities (`bowtie`) and is open for local ones.

> A causal chain is an embedding $c:(X,\leq) \rightarrow M$ where $(X,\leq)$ is linearly ordered
> and endowed with the order topology, and where $c$ is a causal morphism. A subset $S\subset M$
> is a causal chain of $M$ if for every $x\in S$ and every neighbourhood $\U$ of $x$ there exists
> a neighbourhood $\V\subset \U$ of $x$ such that $S\cap \V$ is totally ordered for $\leq_\V$.

> A causal chain of $M$ is maximal if it is maximal for the inclusion among causal chains of $M$.

> $M$ is causally connected if for all $p,q\in M$ such that $p\leq_M q$ there exists a connected
> maximal causal chain from $p$ to $q$.

> $M$ is causally complete if every maximal causal chain is Dedekind-complete.

> Causal completeness is slightly weaker than causal compactness.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| (1) `c` an embedding | ✓ carried (`IsEmbedding`); DEC-6 drops injectivity for curves only |
| (1) `c` a causal morphism | ⚠ reading (a), OQ-12: `WeakMorphism` from `linearCausality X`, whose `≪` is empty and whose `≤_W` asks `Icc x y ⊆ W` |
| (1) ⇒ (2): the image of a chain map is a subset chain | ⚠ strengthened: `X` conditionally complete, densely ordered (`isCausalChain_range`) |
| (2) ⇒ (1) | ⚠ strengthened: `S = range e`, `e` an embedding of a linear order reflected by `≤_M` (`isCausalChainMap_of_isCausalChain`) |
| the remark, "compact ⇒ complete" | ✗ refuted for a NON-LOCAL causality only: `not_causallyCompact_imp_causallyComplete` (`bowtie`, `ofRelation`, kb/0014; causal, `T2`, second countable, not absolutely minimal); open for local ones |
| the remark, "not conversely" (strictness) | ✓ confirmed: `not_causallyComplete_imp_causallyCompact` (`fan`, causal, `T2`, second countable; also non-local) |

## SCOPE (disclosed)

* **(a)** `(X, ≤)` carries `linearCausality X`: `x ≤_W y` iff `x ≤ y` and `[x, y] ⊆ W`, `≪`
  empty; on `ℝ` it is the lightlike line (`linearCausality_real`), so a chain map from `ℝ` is an
  injective DEC-6 causal curve (`isCausalChainMap_real_iff`).
* **(b)** In (2) the neighbourhood `V` is read *open* (`≤_V` is indexed by open sets), `U` any
  neighbourhood. "Totally ordered" is read: any two points comparable for `≤_V`; antisymmetry
  is not asked (it is automatic in a causal spacetime, `≤_V ⊂ ≤_M`).
* **(c)** "A chain from `p` to `q`" is read: containing `p` and `q`.
* **(d)** "Dedekind-complete" is read for the preorder `≤_M` induced on `S` (`chainPreorder`):
  every non-empty subset bounded above has an `IsLUB`; the `IsGLB` half follows
  (`DedekindComplete.exists_isGLB`).
* **Findings.** In a `T1` space a maximal chain is dense (`IsMaximalChain.dense`), so there is
  none where every point has a neighbourhood `U` with two unrelated open sets for `≤_U` in each
  open subset (`not_isMaximalChain_of_hasUnrelatedOpensIn`): the spacelike line, and Lorentzian
  manifolds of dimension ≥ 2 (prose; for Minkowski space `ℝ^{1,n}`, `n ≥ 1`, it is the theorem
  `minkowski_not_isMaximalChain` of `Causal.Minkowski`). Their causal completeness is vacuous.
* **The remark's witnesses are non-local.** `bowtie` and `fan` are discrete, built with
  `Causality.ofRelation` (kb/0014). On a discrete space an absolutely minimal causality has
  `≤` the diagonal and `≪` inside it (not necessarily empty: `diagonalCausality_lt`), hence is
  causally compact and complete (`AbsolutelyMinimalOn.causallyComplete_of_discrete`). A local
  witness — the two null lines through the origin of 1+1 Minkowski space — is described in the
  report and NOT formalized (not cheap).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology

universe u v

/-! ### The causality of a linearly ordered space -/

/-- `def:causal_chain` (1), reading (a): the causality carried by a linearly ordered space
`(X, ≤)`: `x ≤_W y` iff `x ≤ y` and `[x, y] ⊆ W`; no chronological relation. -/
def linearCausality (X : Type v) [LinearOrder X] [TopologicalSpace X] : Causality X where
  le W x y := x ≤ y ∧ Icc x y ⊆ (W : Set X)
  lt _ _ _ := False
  le_mem_left h := h.2 (left_mem_Icc.2 h.1)
  le_mem_right h := h.2 (right_mem_Icc.2 h.1)
  lt_mem_left h := h.elim
  lt_mem_right h := h.elim
  le_refl hx := ⟨le_rfl, by simpa using hx⟩
  le_trans h₁ h₂ := ⟨h₁.1.trans h₂.1, Icc_subset_Icc_union_Icc.trans (union_subset h₁.2 h₂.2)⟩
  lt_trans h _ := h
  le_mono h _ _ h' := ⟨h'.1, fun _ hz => h (h'.2 hz)⟩
  lt_mono _ _ _ h' := h'
  le_of_lt h := h.elim
  isOpen_lt_right _ _ := by simp
  isOpen_lt_left _ _ := by simp

@[simp] theorem linearCausality_le {X : Type v} [LinearOrder X] [TopologicalSpace X]
    {W : Opens X} {x y : X} :
    (linearCausality X).le W x y ↔ x ≤ y ∧ Icc x y ⊆ (W : Set X) := Iff.rfl

/-- On `ℝ` the causality of the order is the lightlike line. -/
theorem linearCausality_real : linearCausality ℝ = lightlikeLine := rfl

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable (C : Causality M)

/-! ### The definitions -/

/-- `def:causal_chain` (1): an embedding `c : X → M`, `X` linearly ordered with the order
topology, which is a causal morphism, read as a weak morphism from `linearCausality X`. -/
structure IsCausalChainMap {X : Type v} [LinearOrder X] [TopologicalSpace X] [OrderTopology X]
    (c : X → M) : Prop where
  isEmbedding : IsEmbedding c
  weakMorphism : WeakMorphism (linearCausality X) C c

/-- `def:causal_chain` (2): "for every `x ∈ S` and every neighbourhood `U` of `x` there exists a
neighbourhood `V ⊂ U` of `x` such that `S ∩ V` is totally ordered for `≤_V`." `V` is open. -/
def IsCausalChain (S : Set M) : Prop :=
  ∀ x ∈ S, ∀ U ∈ 𝓝 x, ∃ V : Opens M, x ∈ V ∧ (V : Set M) ⊆ U ∧
    ∀ y ∈ S ∩ V, ∀ z ∈ S ∩ V, C.le V y z ∨ C.le V z y

/-- `def:maximal_chain`: maximal for the inclusion among causal chains. -/
def IsMaximalChain (S : Set M) : Prop := Maximal C.IsCausalChain S

/-- `def:causally_connected`, reading (c): for `p ≤_M q`, a connected maximal causal chain
containing `p` and `q`. -/
def CausallyConnected : Prop :=
  ∀ p q : M, C.le ⊤ p q → ∃ S : Set M, C.IsMaximalChain S ∧ IsConnected S ∧ p ∈ S ∧ q ∈ S

/-- The preorder `≤_M` induced on a subset `S`, reading (d). -/
@[reducible] def chainPreorder (S : Set M) : Preorder S where
  le a b := C.le ⊤ a b
  le_refl a := C.le_refl (show (a : M) ∈ (⊤ : Opens M) from trivial)
  le_trans _ _ _ := C.le_trans

/-- Reading (d) of "Dedekind-complete" (`MR1631533`): for the preorder `≤_M` induced on `S`,
every non-empty subset bounded above has a least upper bound. -/
def DedekindComplete (S : Set M) : Prop :=
  letI := C.chainPreorder S
  ∀ A : Set S, A.Nonempty → BddAbove A → ∃ s, IsLUB A s

/-- `def:causally_complete`: every maximal causal chain is Dedekind-complete. -/
def CausallyComplete : Prop := ∀ S : Set M, C.IsMaximalChain S → C.DedekindComplete S

variable {C}

/-- `DedekindComplete`, unfolded. -/
theorem dedekindComplete_iff {S : Set M} :
    C.DedekindComplete S ↔ ∀ A : Set S, A.Nonempty → (∃ b : S, ∀ a ∈ A, C.le ⊤ a b) →
      ∃ s : S, (∀ a ∈ A, C.le ⊤ a s) ∧ ∀ b : S, (∀ a ∈ A, C.le ⊤ a b) → C.le ⊤ s b :=
  Iff.rfl

/-- The other half of Dedekind completeness: a non-empty subset bounded below has a greatest
lower bound, the least upper bound of its lower bounds. Stated as the completeness of the
time-reversed preorder. -/
theorem DedekindComplete.dual {S : Set M} (h : C.DedekindComplete S) :
    C.dual.DedekindComplete S := by
  rw [dedekindComplete_iff] at h ⊢
  intro A hA hbdd
  obtain ⟨a₀, ha₀⟩ := hA
  obtain ⟨s, hs₁, hs₂⟩ := h {l | ∀ a ∈ A, C.le ⊤ l a} hbdd ⟨a₀, fun l hl => hl a₀ ha₀⟩
  exact ⟨s, fun a ha => hs₂ a fun l hl => hl a ha, fun b hb => hs₁ b hb⟩

/-- `DedekindComplete.exists_isGLB`, in mathlib's vocabulary. -/
theorem DedekindComplete.exists_isGLB {S : Set M} (h : C.DedekindComplete S) :
    letI := C.chainPreorder S
    ∀ A : Set S, A.Nonempty → BddBelow A → ∃ s, IsGLB A s :=
  h.dual

theorem dual_dedekindComplete {S : Set M} : C.dual.DedekindComplete S ↔ C.DedekindComplete S :=
  ⟨fun h => h.dual, fun h => h.dual⟩

theorem dual_isCausalChain {S : Set M} : C.dual.IsCausalChain S ↔ C.IsCausalChain S := by
  refine ⟨fun h x hx U hU => ?_, fun h x hx U hU => ?_⟩ <;>
  · obtain ⟨V, hxV, hVU, htot⟩ := h x hx U hU
    exact ⟨V, hxV, hVU, fun y hy z hz => (htot y hy z hz).symm⟩

theorem dual_isMaximalChain {S : Set M} : C.dual.IsMaximalChain S ↔ C.IsMaximalChain S := by
  have : C.dual.IsCausalChain = C.IsCausalChain := funext fun _ => propext dual_isCausalChain
  simp only [IsMaximalChain, this]

theorem dual_causallyConnected : C.dual.CausallyConnected ↔ C.CausallyConnected := by
  refine ⟨fun h p q hpq => ?_, fun h p q hpq => ?_⟩
  · obtain ⟨S, hS, hc, hq, hp⟩ := h q p hpq
    exact ⟨S, dual_isMaximalChain.1 hS, hc, hp, hq⟩
  · obtain ⟨S, hS, hc, hq, hp⟩ := h q p hpq
    exact ⟨S, dual_isMaximalChain.2 hS, hc, hp, hq⟩

theorem dual_causallyComplete : C.dual.CausallyComplete ↔ C.CausallyComplete :=
  ⟨fun h S hS => dual_dedekindComplete.1 (h S (dual_isMaximalChain.2 hS)),
    fun h S hS => dual_dedekindComplete.2 (h S (dual_isMaximalChain.1 hS))⟩

/-! ### First facts on subset chains -/

theorem isCausalChain_empty : C.IsCausalChain ∅ := fun _ h => h.elim

/-- A point is a causal chain. -/
theorem isCausalChain_singleton (x : M) : C.IsCausalChain {x} := by
  rintro y rfl U hU
  refine ⟨⟨interior U, isOpen_interior⟩, mem_interior_iff_mem_nhds.2 hU, interior_subset, ?_⟩
  rintro a ⟨rfl, -⟩ b ⟨rfl, hb⟩
  exact Or.inl (C.le_refl hb)

/-- A subset of a causal chain is a causal chain. -/
theorem IsCausalChain.mono {S T : Set M} (hS : C.IsCausalChain S) (hT : T ⊆ S) :
    C.IsCausalChain T := by
  intro x hx U hU
  obtain ⟨V, hxV, hVU, htot⟩ := hS x (hT hx) U hU
  exact ⟨V, hxV, hVU, fun y hy z hz => htot y ⟨hT hy.1, hy.2⟩ z ⟨hT hz.1, hz.2⟩⟩

/-- In a `T1` space a point outside the closure of a chain can be added to it. -/
theorem IsCausalChain.insert_of_notMem_closure [T1Space M] {S : Set M}
    (hS : C.IsCausalChain S) {z : M}
    (hz : z ∉ closure S) : C.IsCausalChain (insert z S) := by
  rintro x (rfl | hx) U hU
  · let V : Opens M :=
      ⟨interior U ∩ (closure S)ᶜ, isOpen_interior.inter isClosed_closure.isOpen_compl⟩
    refine ⟨V, ⟨mem_interior_iff_mem_nhds.2 hU, hz⟩, fun y hy => interior_subset hy.1, ?_⟩
    have key : ∀ y ∈ insert x S ∩ V, y = x := by
      rintro y ⟨rfl | hy, hyV⟩
      · rfl
      · exact absurd (subset_closure hy) hyV.2
    rintro y hy w hw
    rw [key y hy, key w hw]
    exact Or.inl (C.le_refl (show x ∈ V from ⟨mem_interior_iff_mem_nhds.2 hU, hz⟩))
  · have hxz : x ≠ z := fun h => hz (h ▸ subset_closure hx)
    obtain ⟨V, hxV, hVU, htot⟩ :=
      hS x hx (U ∩ {z}ᶜ) (Filter.inter_mem hU (isOpen_compl_singleton.mem_nhds hxz))
    refine ⟨V, hxV, fun y hy => (hVU hy).1, ?_⟩
    have key : ∀ y ∈ insert z S ∩ V, y ∈ S ∩ V := by
      rintro y ⟨rfl | hy, hyV⟩
      · exact absurd rfl (hVU hyV).2
      · exact ⟨hy, hyV⟩
    exact fun y hy w hw => htot y (key y hy) w (key w hw)

/-- **Finding.** In a `T1` space a maximal causal chain is dense. -/
theorem IsMaximalChain.dense [T1Space M] {S : Set M} (h : C.IsMaximalChain S) : Dense S := by
  intro z
  by_contra hz
  exact hz (subset_closure
    (h.2 (h.1.insert_of_notMem_closure hz) (subset_insert z S) (mem_insert z S)))

variable (C) in
/-- Every non-empty open subset of the open `U` contains two non-empty open sets with no `≤_U`
relation between their points. -/
def HasUnrelatedOpensIn (U : Opens M) : Prop :=
  ∀ O : Set M, IsOpen O → O.Nonempty → O ⊆ U → ∃ O₁ O₂ : Set M, IsOpen O₁ ∧ IsOpen O₂ ∧
    O₁.Nonempty ∧ O₂.Nonempty ∧ O₁ ⊆ O ∧ O₂ ⊆ O ∧
      ∀ a ∈ O₁, ∀ b ∈ O₂, ¬ C.le U a b ∧ ¬ C.le U b a

/-- **Finding.** If every point has an open neighbourhood `U` with `HasUnrelatedOpensIn U`, a
`T1` spacetime has no maximal causal chain: a maximal chain is dense, so it meets two unrelated
open sets inside the neighbourhood `V ⊂ U` where it is totally ordered, and `≤_V ⊂ ≤_U`. The
neighbourhoods are local, so no causality condition (no absence of loops) is used. -/
theorem not_isMaximalChain_of_hasUnrelatedOpensIn [T1Space M] [Nonempty M]
    (h : ∀ x : M, ∃ U : Opens M, x ∈ U ∧ C.HasUnrelatedOpensIn U) (S : Set M) :
    ¬ C.IsMaximalChain S := by
  intro hS
  obtain ⟨s, hs⟩ := hS.dense.nonempty
  obtain ⟨U, hsU, hU⟩ := h s
  obtain ⟨V, hsV, hVU, htot⟩ := hS.1 s hs U (U.isOpen.mem_nhds hsU)
  obtain ⟨O₁, O₂, hO₁, hO₂, hne₁, hne₂, h₁, h₂, hun⟩ := hU V V.isOpen ⟨s, hsV⟩ hVU
  obtain ⟨a, ha, haS⟩ := hS.dense.inter_open_nonempty O₁ hO₁ hne₁
  obtain ⟨b, hb, hbS⟩ := hS.dense.inter_open_nonempty O₂ hO₂ hne₂
  have hVU' : V ≤ U := hVU
  rcases htot a ⟨haS, h₁ ha⟩ b ⟨hbS, h₂ hb⟩ with h' | h'
  · exact (hun a ha b hb).1 (C.le_mono hVU' h')
  · exact (hun a ha b hb).2 (C.le_mono hVU' h')

/-- The global form: two unrelated open sets for `≤_M` in every non-empty open set. -/
theorem not_isMaximalChain_of_hasUnrelatedOpensIn_top [T1Space M] [Nonempty M]
    (h : C.HasUnrelatedOpensIn ⊤) (S : Set M) : ¬ C.IsMaximalChain S :=
  not_isMaximalChain_of_hasUnrelatedOpensIn (fun _ => ⟨⊤, trivial, h⟩) S

/-! ### Chain maps and subset chains -/

section ChainMaps

variable {X : Type v} [TopologicalSpace X]

/-- The core of (1) ⇒ (2): along a weak morphism from a conditionally complete, densely ordered
`X`, two points whose segment is mapped into the open set `V` are related by `≤_V`. The
generalisation of `CurveOn.rel_of_lt` from `ℝ` to `X`, by a supremum argument. -/
theorem _root_.Causal.WeakMorphism.le_of_Icc_subset [ConditionallyCompleteLinearOrder X]
    [DenselyOrdered X]
    [OrderTopology X] {c : X → M} (hc : WeakMorphism (linearCausality X) C c) {V : Opens M}
    {y z : X} (hyz : y ≤ z) (hV : ∀ s ∈ Icc y z, c s ∈ V) : C.le V (c y) (c z) := by
  set T : Set X := {s | s ∈ Icc y z ∧ ∀ s' ∈ Icc y s, C.le V (c y) (c s')} with hT
  have hyT : y ∈ T := ⟨⟨le_rfl, hyz⟩, fun s' hs' => by
    have : s' = y := le_antisymm hs'.2 hs'.1
    subst this; exact C.le_refl (hV _ ⟨le_rfl, hyz⟩)⟩
  have hTne : T.Nonempty := ⟨y, hyT⟩
  have hTbdd : BddAbove T := ⟨z, fun s hs => hs.1.2⟩
  have hym : y ≤ sSup T := le_csSup hTbdd hyT
  have hmz : sSup T ≤ z := csSup_le hTne fun s hs => hs.1.2
  obtain ⟨N, hmN, -, hle, -⟩ := hc.local_mono (sSup T) V (hV _ ⟨hym, hmz⟩)
  have hN : (N : Set X) ∈ 𝓝 (sSup T) := N.isOpen.mem_nhds hmN
  obtain ⟨p, hpT, hpN⟩ : ∃ p ∈ T, Icc p (sSup T) ⊆ N := by
    rcases hym.eq_or_lt with h | h
    · refine ⟨y, hyT, ?_⟩
      rw [← h, Icc_self]
      exact singleton_subset_iff.2 (h ▸ hmN)
    · obtain ⟨l, hlm, hl⟩ := exists_Ioc_subset_of_mem_nhds hN ⟨y, h⟩
      obtain ⟨p, hpT, hlp⟩ := exists_lt_of_lt_csSup hTne hlm
      exact ⟨p, hpT, fun s hs => hl ⟨hlp.trans_le hs.1, hs.2⟩⟩
  have key : ∀ q, sSup T ≤ q → q ≤ z → Icc p q ⊆ N → q ∈ T := by
    intro q hmq hqz hpq
    refine ⟨⟨hym.trans hmq, hqz⟩, fun s' hs' => ?_⟩
    by_cases hs'p : s' ≤ p
    · exact hpT.2 s' ⟨hs'.1, hs'p⟩
    · have hps' : p ≤ s' := (not_le.1 hs'p).le
      have h1 : C.le V (c y) (c p) := hpT.2 p ⟨hpT.1.1, le_rfl⟩
      have h2 : C.le V (c p) (c s') := hle ⟨hps', (Icc_subset_Icc_right hs'.2).trans hpq⟩
      exact C.le_trans h1 h2
  have hmT : sSup T ∈ T := key _ le_rfl hmz hpN
  rcases hmz.eq_or_lt with h | h
  · have := hmT.2 (sSup T) ⟨hym, le_rfl⟩
    rwa [h] at this
  · exfalso
    obtain ⟨u, hmu, hu⟩ := exists_Ico_subset_of_mem_nhds hN ⟨z, h⟩
    obtain ⟨q, hmq, hq⟩ := exists_between (lt_min hmu h)
    have hpq : Icc p q ⊆ N := by
      intro s hs
      by_cases hsm : s ≤ sSup T
      · exact hpN ⟨hs.1, hsm⟩
      · exact hu ⟨(not_le.1 hsm).le, hs.2.trans_lt (hq.trans_le (min_le_left _ _))⟩
    have hqT : q ∈ T := key q hmq.le (hq.trans_le (min_le_right _ _)).le hpq
    exact absurd (le_csSup hTbdd hqT) (not_le.2 hmq)

/-- `def:causal_chain`, (1) ⇒ (2): the image of a chain map from a conditionally complete,
densely ordered `X` (an interval of `ℝ`, say) is a subset chain. -/
theorem IsCausalChainMap.isCausalChain_range [ConditionallyCompleteLinearOrder X]
    [DenselyOrdered X] [OrderTopology X] {c : X → M} (hc : C.IsCausalChainMap c) :
    C.IsCausalChain (range c) := by
  rintro _ ⟨t, rfl⟩ U hU
  let U₀ : Opens M := ⟨interior U, isOpen_interior⟩
  have htU₀ : c t ∈ U₀ := mem_interior_iff_mem_nhds.2 hU
  have hs : IsOpen (c ⁻¹' (U₀ : Set M)) := U₀.isOpen.preimage hc.isEmbedding.continuous
  have hWopen : IsOpen (ordConnectedComponent (c ⁻¹' (U₀ : Set M)) t) := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    rw [ordConnectedComponent_eq (mem_ordConnectedComponent.1 hx)]
    exact ordConnectedComponent_mem_nhds.2 (hs.mem_nhds (ordConnectedComponent_subset hx))
  obtain ⟨O, hO, hOW⟩ := hc.isEmbedding.isInducing.isOpen_iff.1 hWopen
  have hmemW : ∀ {r}, r ∈ ordConnectedComponent (c ⁻¹' (U₀ : Set M)) t ↔ c r ∈ O := by
    intro r; rw [← hOW]; rfl
  let V : Opens M := ⟨O, hO⟩ ⊓ U₀
  have htW : t ∈ ordConnectedComponent (c ⁻¹' (U₀ : Set M)) t :=
    self_mem_ordConnectedComponent.2 htU₀
  refine ⟨V, ⟨hmemW.1 htW, htU₀⟩, fun x hx => interior_subset hx.2, ?_⟩
  have hsub : ∀ {a b}, c a ∈ V → c b ∈ V → ∀ r ∈ Icc a b, c r ∈ V := by
    intro a b ha hb r hr
    have hrW : r ∈ ordConnectedComponent (c ⁻¹' (U₀ : Set M)) t :=
      (inferInstance : OrdConnected (ordConnectedComponent (c ⁻¹' (U₀ : Set M)) t)).out
        (hmemW.2 ha.1) (hmemW.2 hb.1) hr
    exact ⟨hmemW.1 hrW, (ordConnectedComponent_subset hrW : r ∈ c ⁻¹' (U₀ : Set M))⟩
  rintro _ ⟨⟨y, rfl⟩, hyV⟩ _ ⟨⟨z, rfl⟩, hzV⟩
  rcases le_total y z with h | h
  · exact Or.inl (hc.weakMorphism.le_of_Icc_subset h (hsub hyV hzV))
  · exact Or.inr (hc.weakMorphism.le_of_Icc_subset h (hsub hzV hyV))

/-- `def:causal_chain`, (2) ⇒ (1): a subset chain `S = range e`, where `e : X → M` is an
embedding of a linearly ordered space with the order topology whose order is reflected by `≤_M`,
is the image of a chain map: `e` is one. -/
theorem isCausalChainMap_of_isCausalChain [LinearOrder X] [OrderTopology X] {e : X → M}
    (he : IsEmbedding e) (hS : C.IsCausalChain (range e))
    (hrefl : ∀ x y, C.le ⊤ (e x) (e y) → x ≤ y) : C.IsCausalChainMap e := by
  refine ⟨he, he.continuous, fun x U hxU => ?_⟩
  obtain ⟨V, hxV, hVU, htot⟩ := hS (e x) ⟨x, rfl⟩ U (U.isOpen.mem_nhds hxU)
  refine ⟨⟨e ⁻¹' V, V.isOpen.preimage he.continuous⟩, hxV, fun y hy => hVU hy, ?_,
    fun _ _ h => h.elim⟩
  rintro y z ⟨hyz, hsub⟩
  have hy : e y ∈ V := hsub (left_mem_Icc.2 hyz)
  have hz : e z ∈ V := hsub (right_mem_Icc.2 hyz)
  rcases htot _ ⟨⟨y, rfl⟩, hy⟩ _ ⟨⟨z, rfl⟩, hz⟩ with h | h
  · exact C.le_mono (show V ≤ U from hVU) h
  · have hzy : z ≤ y := hrefl z y (C.le_mono le_top h)
    have : y = z := le_antisymm hyz hzy
    subst this
    exact C.le_refl (hVU hy)

end ChainMaps

/-- Chain maps from `ℝ` are the injective DEC-6 causal curves: embeddings which are future causal
curves of `M` over every segment. -/
theorem isCausalChainMap_real_iff {c : ℝ → M} :
    C.IsCausalChainMap c ↔ IsEmbedding c ∧ ∀ a b, C.CausalCurveOn ⊤ c a b :=
  ⟨fun h => ⟨h.isEmbedding, weakMorphism_lightlikeLine_iff.1 h.weakMorphism⟩,
    fun h => ⟨h.1, weakMorphism_lightlikeLine_iff.2 h.2⟩⟩

end Causality

/-! ### The lines: the definitions are not empty, and not trivial -/

open Causality

/-- The identity of `ℝ` is a chain map into the timelike line. -/
theorem timelikeLine_isCausalChainMap_id : timelikeLine.IsCausalChainMap (id : ℝ → ℝ) := by
  exact ⟨IsEmbedding.id, continuous_id, fun x U hx =>
    ⟨U, hx, mapsTo_id _, fun _ _ h => h, fun _ _ h => h.elim⟩⟩

/-- The identity of `ℝ` is not a chain map into the spacelike line. -/
theorem spacelikeLine_not_isCausalChainMap_id : ¬ spacelikeLine.IsCausalChainMap (id : ℝ → ℝ) := by
  intro h
  obtain ⟨V, h0V, -, hle, -⟩ := h.weakMorphism.local_mono 0 ⊤ trivial
  obtain ⟨l, u, hl, hu, hlu⟩ := exists_Ioo_subset_opens h0V
  have h' : spacelikeLine.le ⊤ 0 (u / 2) :=
    hle ⟨by linarith, fun r hr => hlu ⟨by linarith [hr.1], by linarith [hr.2]⟩⟩
  have := h'.1
  linarith

/-- Every subset of the timelike line is a causal chain. -/
theorem timelikeLine_isCausalChain (S : Set ℝ) : timelikeLine.IsCausalChain S := by
  intro x _ U hU
  obtain ⟨l, u, ⟨hl, hu⟩, hlu⟩ := mem_nhds_iff_exists_Ioo_subset.1 hU
  refine ⟨⟨Ioo l u, isOpen_Ioo⟩, ⟨hl, hu⟩, hlu, fun y hy z hz => ?_⟩
  rcases le_total y z with h | h
  · exact Or.inl ⟨h, Icc_subset_Ioo hy.2.1 hz.2.2⟩
  · exact Or.inr ⟨h, Icc_subset_Ioo hz.2.1 hy.2.2⟩

/-- The spacelike line is not a causal chain of itself (a point is, `isCausalChain_singleton`). -/
theorem spacelikeLine_not_isCausalChain_univ : ¬ spacelikeLine.IsCausalChain (univ : Set ℝ) := by
  intro h
  obtain ⟨V, h0V, -, htot⟩ := h 0 trivial univ Filter.univ_mem
  obtain ⟨l, u, hl, hu, hlu⟩ := exists_Ioo_subset_opens h0V
  have hu2 : u / 2 ∈ (V : Set ℝ) := hlu ⟨by linarith, by linarith⟩
  rcases htot 0 ⟨trivial, h0V⟩ (u / 2) ⟨trivial, hu2⟩ with h' | h'
  · linarith [h'.1]
  · linarith [h'.1]

/-- The timelike line has exactly one maximal chain, the line. -/
theorem timelikeLine_isMaximalChain_iff {S : Set ℝ} :
    timelikeLine.IsMaximalChain S ↔ S = univ := by
  refine ⟨fun h => eq_univ_of_univ_subset (h.2 (timelikeLine_isCausalChain univ) (subset_univ S)),
    ?_⟩
  rintro rfl
  exact ⟨timelikeLine_isCausalChain univ, fun T _ _ => subset_univ T⟩

/-- **Finding.** The spacelike line has no maximal causal chain. -/
theorem spacelikeLine_not_isMaximalChain (S : Set ℝ) : ¬ spacelikeLine.IsMaximalChain S := by
  intro h
  obtain ⟨s, hs⟩ := h.dense.nonempty
  obtain ⟨V, hsV, -, htot⟩ := h.1 s hs univ Filter.univ_mem
  obtain ⟨l, u, hl, hu, hlu⟩ := exists_Ioo_subset_opens hsV
  obtain ⟨y, hy, hyS⟩ := h.dense.inter_open_nonempty (Ioo s u) isOpen_Ioo ⟨(s + u) / 2,
    by linarith, by linarith⟩
  have hyV : y ∈ (V : Set ℝ) := hlu ⟨hl.trans hy.1, hy.2⟩
  rcases htot s ⟨hs, hsV⟩ y ⟨hyS, hyV⟩ with h' | h'
  · linarith [h'.1, hy.1]
  · linarith [h'.1, hy.1]

theorem timelikeLine_causallyConnected : timelikeLine.CausallyConnected := by
  exact fun _ _ _ => ⟨univ, timelikeLine_isMaximalChain_iff.2 rfl,
    ⟨univ_nonempty, PreconnectedSpace.isPreconnected_univ⟩, trivial,
    trivial⟩

theorem spacelikeLine_not_causallyConnected : ¬ spacelikeLine.CausallyConnected := by
  intro h
  obtain ⟨S, hS, -⟩ := h 0 0 ⟨rfl, trivial⟩
  exact spacelikeLine_not_isMaximalChain S hS

theorem timelikeLine_causallyComplete : timelikeLine.CausallyComplete := by
  intro S hS
  obtain rfl := timelikeLine_isMaximalChain_iff.1 hS
  rw [dedekindComplete_iff]
  rintro A ⟨a₀, ha₀⟩ ⟨b, hb⟩
  have hne : (Subtype.val '' A).Nonempty := ⟨a₀.1, a₀, ha₀, rfl⟩
  have hbdd : BddAbove (Subtype.val '' A) := ⟨b.1, by rintro _ ⟨a, ha, rfl⟩; exact (hb a ha).1⟩
  refine ⟨⟨sSup (Subtype.val '' A), trivial⟩, fun a ha => ⟨le_csSup hbdd ⟨a, ha, rfl⟩,
    fun _ _ => trivial⟩, fun b' hb' => ⟨csSup_le hne ?_, fun _ _ => trivial⟩⟩
  rintro _ ⟨a, ha, rfl⟩
  exact (hb' a ha).1

/-- The spacelike line has unrelated open sets everywhere, so
`not_isMaximalChain_of_hasUnrelatedOpensIn_top` gives `spacelikeLine_not_isMaximalChain` again. -/
theorem spacelikeLine_hasUnrelatedOpensIn_top : spacelikeLine.HasUnrelatedOpensIn ⊤ := by
  rintro O hO ⟨x, hx⟩ -
  obtain ⟨l, u, ⟨hl, hu⟩, hlu⟩ := mem_nhds_iff_exists_Ioo_subset.1 (hO.mem_nhds hx)
  refine ⟨Ioo l x, Ioo x u, isOpen_Ioo, isOpen_Ioo, ⟨(l + x) / 2, by linarith, by linarith⟩,
    ⟨(x + u) / 2, by linarith, by linarith⟩, fun z hz => hlu ⟨hz.1, hz.2.trans hu⟩,
    fun z hz => hlu ⟨hl.trans hz.1, hz.2⟩, fun a ha b hb => ⟨fun h => ?_, fun h => ?_⟩⟩
  · linarith [h.1, ha.2, hb.1]
  · linarith [h.1, ha.2, hb.1]

/-- The spacelike line is causally complete, vacuously. -/
theorem spacelikeLine_causallyComplete : spacelikeLine.CausallyComplete :=
  fun S hS => absurd hS (spacelikeLine_not_isMaximalChain S)

/-! ### `rem:causal_completeness_slightly_weaker`: refuted as read -/

/-- Four events: two in the past, `a₁, a₂`, two in the future, `b₁, b₂`. -/
inductive Bowtie
  | a₁ | a₂ | b₁ | b₂
  deriving DecidableEq

namespace Bowtie

instance : TopologicalSpace Bowtie := ⊥

instance : DiscreteTopology Bowtie := ⟨rfl⟩

/-- An enumeration. -/
def toFin : Bowtie → Fin 4
  | a₁ => 0 | a₂ => 1 | b₁ => 2 | b₂ => 3

instance : Finite Bowtie :=
  Finite.of_injective toFin fun x y h => by cases x <;> cases y <;> first | rfl | cases h

instance : SecondCountableTopology Bowtie := inferInstance

/-- A past event. -/
def IsPast : Bowtie → Prop
  | a₁ | a₂ => True
  | b₁ | b₂ => False

/-- The causal order: each past event precedes each future event. -/
def R (x y : Bowtie) : Prop := x = y ∨ (IsPast x ∧ ¬ IsPast y)

end Bowtie

/-- The bowtie, with the restrictions of `Bowtie.R`; no chronological relation. -/
def bowtie : Causality Bowtie :=
  Causality.ofRelation Bowtie.R (fun _ _ => False) (fun _ => Or.inl rfl)
    (fun x y z h₁ h₂ => by
      cases x <;> cases y <;> cases z <;> simp_all [Bowtie.R, Bowtie.IsPast])
    (fun _ _ _ h _ => h) (fun _ _ h => h.elim) (fun _ => by simp) (fun _ => by simp)

@[simp] theorem bowtie_le {U : Opens Bowtie} {x y : Bowtie} :
    bowtie.le U x y ↔ x ∈ U ∧ y ∈ U ∧ Bowtie.R x y := Iff.rfl

/-- Every subset of the bowtie is a causal chain: the topology is discrete. -/
theorem bowtie_isCausalChain (S : Set Bowtie) : bowtie.IsCausalChain S := by
  intro x _ U hU
  refine ⟨⟨{x}, isOpen_discrete _⟩, rfl, singleton_subset_iff.2 (mem_of_mem_nhds hU), ?_⟩
  rintro y ⟨-, hy⟩ z ⟨-, hz⟩
  have hy' : y = x := hy
  have hz' : z = x := hz
  subst hy' hz'
  exact Or.inl (bowtie.le_refl rfl)

theorem bowtie_isMaximalChain_univ : bowtie.IsMaximalChain univ :=
  ⟨bowtie_isCausalChain univ, fun T _ _ => subset_univ T⟩

theorem bowtie_isCausal : bowtie.IsCausal := by
  intro x y h₁ h₂
  cases x <;> cases y <;> simp_all [Bowtie.R, Bowtie.IsPast]

theorem bowtie_causallyCompact : bowtie.CausallyCompact := by
  exact fun _ _ => (Set.toFinite _).isCompact

theorem bowtie_not_causallyComplete : ¬ bowtie.CausallyComplete := by
  intro h
  have hc := dedekindComplete_iff.1 (h univ bowtie_isMaximalChain_univ)
  let A : Set (univ : Set Bowtie) := {p | p.1 = Bowtie.a₁ ∨ p.1 = Bowtie.a₂}
  have hb : ∀ y : Bowtie, ¬ Bowtie.IsPast y → ∀ a ∈ A, bowtie.le ⊤ a.1 y := by
    rintro y hy a (ha | ha) <;>
      exact ⟨trivial, trivial, Or.inr ⟨by rw [ha]; trivial, hy⟩⟩
  obtain ⟨⟨s, hsu⟩, hs₁, hs₂⟩ := hc A ⟨⟨Bowtie.a₁, trivial⟩, Or.inl rfl⟩
    ⟨⟨Bowtie.b₁, trivial⟩, hb Bowtie.b₁ id⟩
  have h₁ := (hs₁ ⟨Bowtie.a₁, trivial⟩ (Or.inl rfl)).2.2
  have h₂ := (hs₁ ⟨Bowtie.a₂, trivial⟩ (Or.inr rfl)).2.2
  have h₃ := (hs₂ ⟨Bowtie.b₁, trivial⟩ (hb Bowtie.b₁ id)).2.2
  have h₄ := (hs₂ ⟨Bowtie.b₂, trivial⟩ (hb Bowtie.b₂ id)).2.2
  cases s <;> simp_all [Bowtie.R, Bowtie.IsPast]

/-- `rem:causal_completeness_slightly_weaker`, its first half "causally compact ⇒ causally
complete", is false **for a non-local causality**: the bowtie (`Causality.ofRelation`, kb/0014)
is causal, Hausdorff, second countable, causally compact and not causally complete. A local
(absolutely minimal) causality on a discrete space is trivial and both causally compact and
causally complete (`AbsolutelyMinimalOn.causallyComplete_of_discrete`), so this witness says
nothing about local causalities. -/
theorem not_causallyCompact_imp_causallyComplete :
    ¬ ∀ (N : Type) [TopologicalSpace N] [T2Space N] [SecondCountableTopology N]
      (D : Causality N), D.IsCausal → D.CausallyCompact → D.CausallyComplete :=
  fun h => bowtie_not_causallyComplete (h Bowtie bowtie bowtie_isCausal bowtie_causallyCompact)

/-! ### Why the bowtie is non-local: a local causality on a discrete space is trivial -/

section Discrete

variable {M : Type u} [TopologicalSpace M] {C : Causality M}

omit [TopologicalSpace M] in
/-- A chain of steps each of which is an equality is an equality. -/
theorem eq_of_transGen_eq {r : M → M → Prop} (hr : ∀ a b, r a b → a = b) {x y : M}
    (h : Relation.TransGen r x y) : x = y := by
  induction h with
  | single h => exact hr _ _ h
  | tail _ h ih => exact ih.trans (hr _ _ h)

/-- On a discrete space an absolutely minimal causality is trivial: `≤_U` is the diagonal of `U`
and `≪_U` is contained in it (the cover by points). `≪` need not be empty:
`diagonalCausality_lt`. -/
theorem AbsolutelyMinimalOn.eq_of_discrete [DiscreteTopology M]
    (h : C.AbsolutelyMinimalOn ⊤) {U : Opens M} {x y : M} :
    (C.le U x y → x = y) ∧ (C.lt U x y → x = y) := by
  let S : Set (Opens M) := range fun z : M => (⟨{z}, isOpen_discrete _⟩ : Opens M)
  have hS : ∀ z ∈ (⊤ : Opens M), ∃ O ∈ S, z ∈ O := fun z _ => ⟨_, ⟨z, rfl⟩, rfl⟩
  have key : ∀ (r : Opens M → M → M → Prop), (∀ {N : Opens M} {a b : M}, r N a b → a ∈ N) →
      (∀ {N : Opens M} {a b : M}, r N a b → b ∈ N) →
      ∀ a b, (∃ O ∈ S, r (U ⊓ O) a b) → a = b := by
    rintro r hl hr a b ⟨_, ⟨z, rfl⟩, hab⟩
    have ha : a = z := (hl hab).2
    have hb : b = z := (hr hab).2
    rw [ha, hb]
  obtain ⟨hle, hlt⟩ := h S hS U le_top x y
  exact ⟨fun hxy => eq_of_transGen_eq (key _ C.le_mem_left C.le_mem_right) (hle hxy),
    fun hxy => eq_of_transGen_eq (key _ C.lt_mem_left C.lt_mem_right) (hlt hxy)⟩

/-- A causality whose relation `≤_M` is contained in the diagonal is causally compact. -/
theorem causallyCompact_of_le_top_eq (h : ∀ x y, C.le ⊤ x y → x = y) : C.CausallyCompact := by
  intro p q
  have hsub : C.diamond ⊤ p q ⊆ {p} := fun z hz => (h p z (mem_diamond.1 hz).1).symm
  exact (subsingleton_singleton.anti hsub).isCompact

/-- A causality whose relation `≤_M` is contained in the diagonal is causally complete. -/
theorem causallyComplete_of_le_top_eq (h : ∀ x y, C.le ⊤ x y → x = y) : C.CausallyComplete := by
  intro S _
  rw [dedekindComplete_iff]
  rintro A ⟨a₀, ha₀⟩ ⟨b, hb⟩
  refine ⟨b, hb, fun b' hb' => ?_⟩
  have h₁ : (a₀ : M) = b := h _ _ (hb a₀ ha₀)
  have h₂ : (a₀ : M) = b' := h _ _ (hb' a₀ ha₀)
  rw [← h₁, ← h₂]
  exact C.le_refl trivial

theorem AbsolutelyMinimalOn.causallyCompact_of_discrete [DiscreteTopology M]
    (h : C.AbsolutelyMinimalOn ⊤) : C.CausallyCompact :=
  causallyCompact_of_le_top_eq fun _ _ hxy => (AbsolutelyMinimalOn.eq_of_discrete h).1 hxy

theorem AbsolutelyMinimalOn.causallyComplete_of_discrete [DiscreteTopology M]
    (h : C.AbsolutelyMinimalOn ⊤) : C.CausallyComplete :=
  causallyComplete_of_le_top_eq fun _ _ hxy => (AbsolutelyMinimalOn.eq_of_discrete h).1 hxy

end Discrete

/-- On a discrete space, the causality whose two relations are the diagonal. -/
def diagonalCausality (M : Type u) [TopologicalSpace M] [DiscreteTopology M] : Causality M :=
  Causality.ofRelation (· = ·) (· = ·) (fun _ => rfl) (fun _ _ _ h₁ h₂ => h₁.trans h₂)
    (fun _ _ _ h₁ h₂ => h₁.trans h₂) (fun _ _ h => h) (fun _ => isOpen_discrete _)
    (fun _ => isOpen_discrete _)

/-- `diagonalCausality` is absolutely minimal. -/
theorem diagonalCausality_absolutelyMinimalOn (M : Type u) [TopologicalSpace M]
    [DiscreteTopology M] : (diagonalCausality M).AbsolutelyMinimalOn ⊤ := by
  intro S hS V _ x y
  refine ⟨fun hxy => ?_, fun hxy => ?_⟩ <;>
  · obtain ⟨hx, -, rfl⟩ := hxy
    obtain ⟨O, hO, hxO⟩ := hS x trivial
    exact Relation.TransGen.single ⟨O, hO, ⟨hx, hxO⟩, ⟨hx, hxO⟩, rfl⟩

/-- In `diagonalCausality` every point is chronologically related to itself: on a discrete space
an absolutely minimal `≪` is contained in the diagonal, not necessarily empty. -/
theorem diagonalCausality_lt (M : Type u) [TopologicalSpace M] [DiscreteTopology M] (x : M) :
    (diagonalCausality M).lt ⊤ x x :=
  ⟨trivial, trivial, rfl⟩

/-- A non-causal sanity example (kb/0014): the line on which any two points are related, with
`Causality.ofRelation`. It is causally complete and not causally compact; `fan` is the causal
witness of the same. -/
def totalLine : Causality ℝ :=
  Causality.ofRelation (fun _ _ => True) (fun _ _ => False) (fun _ => trivial)
    (fun _ _ _ _ _ => trivial) (fun _ _ _ h _ => h) (fun _ _ h => h.elim) (fun _ => by simp)
    (fun _ => by simp)

@[simp] theorem totalLine_le {U : Opens ℝ} {x y : ℝ} :
    totalLine.le U x y ↔ x ∈ U ∧ y ∈ U ∧ True := Iff.rfl

/-- Every subset of `totalLine` is a chain, and the line is its unique maximal chain. -/
theorem totalLine_isCausalChain (S : Set ℝ) : totalLine.IsCausalChain S := by
  intro x _ U hU
  refine ⟨⟨interior U, isOpen_interior⟩, mem_interior_iff_mem_nhds.2 hU, interior_subset, ?_⟩
  exact fun y hy z hz => Or.inl ⟨hy.2, hz.2, trivial⟩

theorem totalLine_causallyComplete : totalLine.CausallyComplete := by
  intro S _
  rw [dedekindComplete_iff]
  rintro A ⟨a, -⟩ -
  exact ⟨a, fun _ _ => ⟨trivial, trivial, trivial⟩, fun _ _ => ⟨trivial, trivial, trivial⟩⟩

theorem totalLine_not_causallyCompact : ¬ totalLine.CausallyCompact := by
  intro h
  have heq : totalLine.diamond ⊤ 0 0 = univ :=
    eq_univ_of_forall fun _ =>
      mem_diamond.2 ⟨⟨trivial, trivial, trivial⟩, ⟨trivial, trivial, trivial⟩⟩
  exact noncompact_univ ℝ (heq ▸ h 0 0)

/-! A causal witness for the converse: the fan on `ℕ`, discrete, where `0` precedes and `1`
follows every event, the others being pairwise unrelated. -/

/-- The order of the fan. -/
def fanRel (x y : ℕ) : Prop := x = y ∨ x = 0 ∨ y = 1

/-- The fan: `ℕ` discrete, with the restrictions of `fanRel`; no chronological relation. -/
def fan : Causality ℕ :=
  Causality.ofRelation fanRel (fun _ _ => False) (fun _ => Or.inl rfl)
    (fun x y z h₁ h₂ => by unfold fanRel at *; omega)
    (fun _ _ _ h _ => h) (fun _ _ h => h.elim) (fun _ => by simp) (fun _ => by simp)

@[simp] theorem fan_le {U : Opens ℕ} {x y : ℕ} :
    fan.le U x y ↔ x ∈ U ∧ y ∈ U ∧ fanRel x y := Iff.rfl

theorem fan_isCausal : fan.IsCausal := by
  intro x y h₁ h₂
  have := h₁.2.2
  have := h₂.2.2
  unfold fanRel at *
  omega

theorem fan_isCausalChain (S : Set ℕ) : fan.IsCausalChain S := by
  intro x _ U hU
  refine ⟨⟨{x}, isOpen_discrete _⟩, rfl, singleton_subset_iff.2 (mem_of_mem_nhds hU), ?_⟩
  rintro y ⟨-, hy⟩ z ⟨-, hz⟩
  have hy' : y = x := hy
  have hz' : z = x := hz
  subst hy' hz'
  exact Or.inl (fan.le_refl rfl)

theorem fan_not_causallyCompact : ¬ fan.CausallyCompact := by
  intro h
  have heq : fan.diamond ⊤ 0 1 = univ :=
    eq_univ_of_forall fun _ => mem_diamond.2 ⟨⟨trivial, trivial, Or.inr (Or.inl rfl)⟩,
      ⟨trivial, trivial, Or.inr (Or.inr rfl)⟩⟩
  have := h 0 1
  rw [heq, isCompact_iff_finite] at this
  exact Set.infinite_univ this

theorem fan_causallyComplete : fan.CausallyComplete := by
  intro S hS
  have hSu : S = univ := eq_univ_of_univ_subset (hS.2 (fan_isCausalChain univ) (subset_univ S))
  subst hSu
  rw [dedekindComplete_iff]
  rintro A ⟨a₀, ha₀⟩ -
  by_cases h₂ : ∃ a ∈ A, ∃ b ∈ A, a.1 ≠ b.1 ∧ a.1 ≠ 0 ∧ b.1 ≠ 0
  · obtain ⟨a, ha, b, hb, hab, ha0, hb0⟩ := h₂
    refine ⟨⟨1, trivial⟩, fun x _ => ⟨trivial, trivial, Or.inr (Or.inr rfl)⟩, fun c hc => ?_⟩
    have h₁ := (hc a ha).2.2
    have h₂ := (hc b hb).2.2
    refine ⟨trivial, trivial, ?_⟩
    unfold fanRel at *
    omega
  · push Not at h₂
    by_cases h₁ : ∃ a ∈ A, a.1 ≠ 0
    · obtain ⟨a, ha, ha0⟩ := h₁
      refine ⟨a, fun x hx => ⟨trivial, trivial, ?_⟩, fun c hc => hc a ha⟩
      by_cases hxa : x.1 = a.1
      · exact Or.inl hxa
      · by_cases hx0 : x.1 = 0
        · exact Or.inr (Or.inl hx0)
        · exact absurd (h₂ x hx a ha hxa hx0) ha0
    · push Not at h₁
      refine ⟨a₀, fun x hx => ⟨trivial, trivial, ?_⟩, fun c _ =>
        ⟨trivial, trivial, Or.inr (Or.inl (h₁ a₀ ha₀))⟩⟩
      exact Or.inl ((h₁ x hx).trans (h₁ a₀ ha₀).symm)

/-- `rem:causal_completeness_slightly_weaker`, strictness half, confirmed: a causal, Hausdorff,
second countable spacetime is causally complete and not causally compact. The witness `fan` is
non-local (`Causality.ofRelation`, kb/0014). -/
theorem not_causallyComplete_imp_causallyCompact :
    ¬ ∀ (N : Type) [TopologicalSpace N] [T2Space N] [SecondCountableTopology N]
      (D : Causality N), D.IsCausal → D.CausallyComplete → D.CausallyCompact :=
  fun h => fan_not_causallyCompact (h ℕ fan fan_isCausal fan_causallyComplete)

end Causal
