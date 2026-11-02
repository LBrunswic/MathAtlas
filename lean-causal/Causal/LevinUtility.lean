import Causal.LemmaKSC
import Causal.CurvesExtend

/-!
# A continuous time function from second countability (Levin's theorem), hence `CurvesExtend`

No label is marked. This module discharges the named model fact `Causality.CurvesExtend`
(`Causal/CauchyExtension.lean:82`) in every **second countable** tarentin globally hyperbolic
Hausdorff spacetime, with no measure: the time function `curvesExtend_of_timeFunction`
(`Causal/CurvesExtend.lean`) asks for is produced by Levin's theorem for closed preorders, proved
here from mathlib's Urysohn machinery. Second countability is part of ETT's own definition of a
spacetime, so nothing is added to the paper:

> A topological spacetime is a second countable Hausdorff topological space endowed with a
> causality. (`def:category_topological_spacetimes`, `ETT.tex:255`)

It closes the gap `Causal.LemmaKSC` (SCOPE, route (a)) and `Causal.CurvesExtend` (SCOPE: "whether
`CurvesExtend` holds in every second countable … spacetime is open here") left open, for globally
hyperbolic spacetimes.

## What is proved

* **Order normality** (`Levin.exists_cover`): on a locally compact σ-compact normal space with a
  closed preorder `r`, a closed up-set `A` and a closed down-set `B` that are disjoint are covered
  by a closed up-set `A'` missing `B` and a closed down-set `B'` missing `A` (`A' ∪ B' = univ`);
  equivalently they have disjoint open up/down neighbourhoods `B'ᶜ ⊇ A`, `A'ᶜ ⊇ B`. The proof is
  an induction along a compact exhaustion `K₀ ⊆ K₁ ⊆ …` (`Levin.step`): at stage `n` the
  covering sets are hulls `↑P`, `↓Q` of compact sets (closed, because `r` is closed), chosen by
  ordinary normality with a margin, and never changing on `K_{n-1}` — so the unions are locally
  finite unions of closed sets.
* **Order Urysohn** (`Levin.exists_monotone_sep`): if `¬ r y x` there is a continuous
  `u : X → [0, 1]`, monotone along `r`, with `u x = 0`, `u y = 1`. It is mathlib's own
  `Urysohns.CU` construction run with the predicate "the open set is a down-set, and a closed
  down-set sits between": every `U` of the dyadic tree is a down-set, so every approximation, and
  the limit, is monotone.
* **Levin's theorem** (`Levin.exists_utility`): with second countability moreover, there is a
  continuous `T : X → ℝ`, monotone along `r` and strictly increasing on `r x y ∧ ¬ r y x`:
  `T = ∑ 2^{-n} u_n` over a countable family of separating functions (Lindelöf on `X × X`).
* **In ETT** (`Causality.exists_timeFunction_of_secondCountable`): every second countable
  tarentin globally hyperbolic Hausdorff spacetime carries a continuous `τ`, monotone along `≤_M`
  and strictly increasing on `x ≤ y`, `x ≠ y`; hence `CurvesExtend`
  (`Causality.curvesExtend_of_secondCountable`) and, for every open `W` and every interval, the
  relative form (`Causality.exists_inextensible_of_secondCountable`).
* **Lemma K's characterisations without the named hypothesis**: `Causal.LemmaKSC`'s
  `isCauchySurface_iff_local` and `isCauchySurface_iff_isOpen_strictJplus` with `hext` discharged
  under second countability (`…_of_secondCountable`).

## Hypothesis checklist

| hypothesis | here |
|---|---|
| second countable, Hausdorff (`ETT.tex:255`) | ✓ carried: `[SecondCountableTopology M] [T2Space M]` |
| `C.Tarentin`, `C.GloballyHyperbolic` | ✓ carried: they give local compactness, σ-compactness, normality and the closedness of `≤_M` (`prop:GH_Jferme`) |
| connectedness, causal arc-connectedness, `J^±(p) ≠ {p}` | ⚠ weakened: not used for the time function and `CurvesExtend`; carried in the Lemma K corollaries only, where `Causal.LemmaKSC` needs them |
| admissible measures (`geroch_i_imp_ii`) | ⚠ weakened: not used — the time function is Levin's, not Geroch's |
| "time function" | ⚠ reading: a continuous `τ`, monotone along `≤_M`, strictly increasing on `x ≤ y`, `x ≠ y` (what `curvesExtend_of_timeFunction` asks); not Cauchy, not claimed to have spacelike level sets |

## SCOPE (disclosed)

* **Lemma K is not settled by this module.** Where curves extend, the bare (second countable)
  Lemma K is still equivalent to the two local conditions (1′)+(2′) of
  `Causality.isCauchySurface_iff_local`; this module only removes `CurvesExtend` from the
  equivalence (`isCauchySurface_iff_local_of_secondCountable`). The tagged `sorry` of
  `CausalScaffold.LemmaKSCOpen` stays.
* The time function produced is not a Cauchy time function: Barbot's form
  `exists_inextensible_univ_of_isCauchyTimeFunction` (`J = ℝ`) is not reached from it.
* The abstract theorems (`Levin.*`) are stated for any relation `r` that is reflexive,
  transitive and closed in `X × X`, on a normal, weakly locally compact, σ-compact (and for
  `exists_utility`, second countable) space; no antisymmetry is used except in the ETT
  corollary, where it is causality (`hG.1`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Function

universe u

namespace Levin

variable {X : Type*} [TopologicalSpace X] (r : X → X → Prop)

/-- The up-hull `↑S = {y | ∃ x ∈ S, r x y}`. The down-hull is `upHull (flip r) S`. -/
def upHull (S : Set X) : Set X := {y | ∃ x ∈ S, r x y}

/-- `S` is an up-set for `r`. A down-set is an up-set for `flip r`. -/
def IsUp (S : Set X) : Prop := ∀ ⦃x y : X⦄, r x y → x ∈ S → y ∈ S

variable {r}

omit [TopologicalSpace X] in
theorem isUp_upHull (htrans : ∀ x y z, r x y → r y z → r x z) (S : Set X) :
    IsUp r (upHull r S) := fun _ _ hxy ⟨w, hw, hwx⟩ => ⟨w, hw, htrans _ _ _ hwx hxy⟩

omit [TopologicalSpace X] in
theorem subset_upHull (hrefl : ∀ x, r x x) (S : Set X) : S ⊆ upHull r S :=
  fun x hx => ⟨x, hx, hrefl x⟩

omit [TopologicalSpace X] in
/-- The complement of an up-set is a down-set. -/
theorem IsUp.compl {S : Set X} (h : IsUp r S) : IsUp (flip r) Sᶜ :=
  fun _ _ hxy hx hy => hx (h hxy hy)

/-- If the relation is closed, the up-hull of a compact set is closed. -/
theorem isClosed_upHull (hr : IsClosed {p : X × X | r p.1 p.2}) {K : Set X} (hK : IsCompact K) :
    IsClosed (upHull r K) := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hcont : Continuous fun z : K × X => ((z.1 : X), z.2) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hR : IsClosed ((fun z : K × X => ((z.1 : X), z.2)) ⁻¹' {p : X × X | r p.1 p.2}) :=
    hr.preimage hcont
  have himg : upHull r K =
      Prod.snd '' ((fun z : K × X => ((z.1 : X), z.2)) ⁻¹' {p : X × X | r p.1 p.2}) := by
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      exact ⟨(⟨x, hx⟩, y), hxy, rfl⟩
    · rintro ⟨⟨⟨x, hx⟩, y'⟩, hxy, rfl⟩
      exact ⟨x, hx, hxy⟩
  rw [himg]
  exact isClosedMap_snd_of_compactSpace _ hR

theorem isClosed_flip (hr : IsClosed {p : X × X | r p.1 p.2}) :
    IsClosed {p : X × X | flip r p.1 p.2} :=
  hr.preimage continuous_swap

/-! ### Order normality, by induction along a compact exhaustion -/

/-- The invariant of the induction, relative to a compact `K`: `a` a closed up-set missing `B`,
`b` a closed down-set missing `A`, their interiors cover `K`, and no point of `K` off the interior
of `b` lies below a point of `K` off the interior of `a`. -/
structure Good (r : X → X → Prop) (A B K a b : Set X) : Prop where
  closed_a : IsClosed a
  closed_b : IsClosed b
  up_a : IsUp r a
  down_b : IsUp (flip r) b
  disj_a : Disjoint a B
  disj_b : Disjoint b A
  cover : K ⊆ interior a ∪ interior b
  sep : ∀ z' ∈ K, ∀ z ∈ K, z' ∉ interior b → z ∉ interior a → ¬ r z' z

theorem good_empty (A B : Set X) : Good r A B ∅ ∅ ∅ where
  closed_a := isClosed_empty
  closed_b := isClosed_empty
  up_a := fun _ _ _ h => h
  down_b := fun _ _ _ h => h
  disj_a := Set.empty_disjoint _
  disj_b := Set.empty_disjoint _
  cover := empty_subset _
  sep := fun _ h => absurd h (notMem_empty _)

/-- **One step of the induction.** From a good pair for `Kp`, a good pair for `Kn`, larger, and
unchanged on `Kp`. -/
theorem step [NormalSpace X] [WeaklyLocallyCompactSpace X] (hrefl : ∀ x, r x x)
    (htrans : ∀ x y z, r x y → r y z → r x z) (hr : IsClosed {p : X × X | r p.1 p.2})
    {A B : Set X} (hA : IsClosed A) (hAu : IsUp r A) (hB : IsClosed B) (hBd : IsUp (flip r) B)
    (hAB : Disjoint A B) {Kp Kn : Set X} (hKp : IsCompact Kp) (hKn : IsCompact Kn) {a b : Set X}
    (h : Good r A B Kp a b) :
    ∃ a' b', Good r A B Kn a' b' ∧ a ⊆ a' ∧ b ⊆ b' ∧ a' ∩ Kp ⊆ a ∧ b' ∩ Kp ⊆ b := by
  have hrf := isClosed_flip hr
  have hreflf : ∀ x, flip r x x := hrefl
  set Z := Kp \ interior a with hZdef
  set Z' := Kp \ interior b with hZ'def
  have hZ : IsCompact Z := hKp.diff isOpen_interior
  have hZ' : IsCompact Z' := hKp.diff isOpen_interior
  set FP := B ∪ upHull (flip r) Z with hFPdef
  set FQ := A ∪ upHull r Z' with hFQdef
  have hFP : IsClosed FP := hB.union (isClosed_upHull hrf hZ)
  have hFQ : IsClosed FQ := hA.union (isClosed_upHull hr hZ')
  have hFQu : IsUp r FQ := by
    rintro x y hxy (hx | ⟨z, hz, hzx⟩)
    · exact Or.inl (hAu hxy hx)
    · exact Or.inr ⟨z, hz, htrans _ _ _ hzx hxy⟩
  have hdisj : FP ⊆ FQᶜ := by
    rintro w (hwB | ⟨z, hz, hzw⟩) (hwA | ⟨z', hz', hz'w⟩)
    · exact Set.disjoint_left.1 hAB hwA hwB
    · have hz'B : z' ∈ B := hBd hz'w hwB
      have : z' ∈ interior a := (h.cover hz'.1).resolve_right hz'.2
      exact Set.disjoint_left.1 h.disj_a (interior_subset this) hz'B
    · have hzA : z ∈ A := hAu hzw hwA
      have : z ∈ interior b := (h.cover hz.1).resolve_left hz.2
      exact Set.disjoint_left.1 h.disj_b (interior_subset this) hzA
    · exact h.sep z' hz'.1 z hz.1 hz'.2 hz.2 (htrans _ _ _ hz'w hzw)
  obtain ⟨U₁, hU₁o, hFPU₁, hU₁c⟩ := normal_exists_closure_subset hFP hFQ.isOpen_compl hdisj
  set S₂ := closure U₁ ∪ upHull (flip r) (closure U₁ ∩ Kn) with hS₂def
  have hS₂ : IsClosed S₂ :=
    isClosed_closure.union (isClosed_upHull hrf (hKn.inter_left isClosed_closure))
  have hS₂Q : S₂ ⊆ FQᶜ := by
    rintro w (hw | ⟨z, hz, hzw⟩) hwQ
    · exact hU₁c hw hwQ
    · exact hU₁c hz.1 (hFQu hzw hwQ)
  obtain ⟨U₂, hU₂o, hS₂U₂, hU₂c⟩ := normal_exists_closure_subset hS₂ hFQ.isOpen_compl hS₂Q
  obtain ⟨L, hL, hKnL⟩ := exists_compact_superset hKn
  have hP : IsCompact (L \ U₁) := hL.diff hU₁o
  have hQ : IsCompact (L ∩ closure U₂) := hL.inter_right isClosed_closure
  set a' := a ∪ upHull r (L \ U₁) with ha'def
  set b' := b ∪ upHull (flip r) (L ∩ closure U₂) with hb'def
  have hPint : ∀ x ∈ Kn, x ∉ closure U₁ → x ∈ interior a' := by
    intro x hx hxc
    refine interior_maximal (t := interior L ∩ (closure U₁)ᶜ) ?_
      (isOpen_interior.inter isClosed_closure.isOpen_compl) ⟨hKnL hx, hxc⟩
    rintro y ⟨hyL, hyc⟩
    exact Or.inr (subset_upHull hrefl _ ⟨interior_subset hyL, fun hy => hyc (subset_closure hy)⟩)
  have hQint : ∀ x ∈ Kn, x ∈ U₂ → x ∈ interior b' := by
    intro x hx hxU
    refine interior_maximal (t := interior L ∩ U₂) ?_ (isOpen_interior.inter hU₂o)
      ⟨hKnL hx, hxU⟩
    rintro y ⟨hyL, hyU⟩
    exact Or.inr (subset_upHull hreflf _ ⟨interior_subset hyL, subset_closure hyU⟩)
  refine ⟨a', b', ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, subset_union_left, subset_union_left, ?_, ?_⟩
  · exact h.closed_a.union (isClosed_upHull hr hP)
  · exact h.closed_b.union (isClosed_upHull hrf hQ)
  · rintro x y hxy (hx | ⟨p, hp, hpx⟩)
    · exact Or.inl (h.up_a hxy hx)
    · exact Or.inr ⟨p, hp, htrans _ _ _ hpx hxy⟩
  · rintro x y hxy (hx | ⟨q, hq, hqx⟩)
    · exact Or.inl (h.down_b hxy hx)
    · exact Or.inr ⟨q, hq, htrans _ _ _ hxy hqx⟩
  · refine Set.disjoint_left.2 ?_
    rintro y (hy | ⟨p, hp, hpy⟩) hyB
    · exact Set.disjoint_left.1 h.disj_a hy hyB
    · exact hp.2 (hFPU₁ (Or.inl (hBd hpy hyB)))
  · refine Set.disjoint_left.2 ?_
    rintro y (hy | ⟨q, hq, hqy⟩) hyA
    · exact Set.disjoint_left.1 h.disj_b hy hyA
    · exact hU₂c hq.2 (Or.inl (hAu hqy hyA))
  · intro x hx
    by_cases hxc : x ∈ closure U₁
    · exact Or.inr (hQint x hx (hS₂U₂ (Or.inl hxc)))
    · exact Or.inl (hPint x hx hxc)
  · intro z' hz' z hz hz'b hza hrz
    have hzc : z ∈ closure U₁ := by
      by_contra hzc
      exact hza (hPint z hz hzc)
    exact hz'b (hQint z' hz' (hS₂U₂ (Or.inr ⟨z, ⟨hzc, hz⟩, hrz⟩)))
  · rintro y ⟨hy | ⟨p, hp, hpy⟩, hyK⟩
    · exact hy
    · by_contra hya
      have hyZ : y ∈ Z := ⟨hyK, fun hi => hya (interior_subset hi)⟩
      exact hp.2 (hFPU₁ (Or.inr ⟨y, hyZ, hpy⟩))
  · rintro y ⟨hy | ⟨q, hq, hqy⟩, hyK⟩
    · exact hy
    · by_contra hyb
      have hyZ : y ∈ Z' := ⟨hyK, fun hi => hyb (interior_subset hi)⟩
      exact hU₂c hq.2 (Or.inr ⟨y, hyZ, hqy⟩)

/-- **Gluing along a compact exhaustion.** An increasing sequence of closed sets which does not
change on `K n` after stage `n` has a closed union, equal to `S m` on `K m`. -/
theorem glue (K : CompactExhaustion X) (S : ℕ → Set X) (hS : ∀ n, IsClosed (S n))
    (hmono : ∀ n, S n ⊆ S (n + 1)) (hstab : ∀ n, S (n + 1) ∩ K n ⊆ S n) :
    IsClosed (⋃ n, S n) ∧ ∀ m, (⋃ n, S n) ∩ K m ⊆ S m := by
  have hk : ∀ m k, S (m + k) ∩ K m ⊆ S m := by
    intro m k
    induction k with
    | zero => exact inter_subset_left
    | succ k ih =>
      rintro y ⟨hy, hyK⟩
      exact ih ⟨hstab (m + k) ⟨hy, K.subset (Nat.le_add_right m k) hyK⟩, hyK⟩
  have hsm : Monotone S := monotone_nat_of_le_succ hmono
  have hst : ∀ m, (⋃ n, S n) ∩ K m ⊆ S m := by
    rintro m y ⟨hy, hyK⟩
    obtain ⟨n, hn⟩ := mem_iUnion.1 hy
    rcases le_total n m with hnm | hmn
    · exact hsm hnm hn
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      exact hk m k ⟨hn, hyK⟩
  refine ⟨?_, hst⟩
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨m, hm⟩ := K.exists_mem x
  refine ⟨interior (K (m + 1)) ∩ (S (m + 1))ᶜ, ?_, isOpen_interior.inter (hS _).isOpen_compl,
    K.subset_interior_succ m hm, fun h => hx (mem_iUnion.2 ⟨_, h⟩)⟩
  rintro y ⟨hyK, hyS⟩ hy
  exact hyS (hst (m + 1) ⟨hy, interior_subset hyK⟩)

/-- **Order normality** (Nachbin; Minguzzi for locally compact σ-compact spaces). A closed
up-set `A` and a closed down-set `B`, disjoint, are covered by a closed up-set missing `B` and a
closed down-set missing `A`. -/
theorem exists_cover [NormalSpace X] [WeaklyLocallyCompactSpace X] [SigmaCompactSpace X]
    (hrefl : ∀ x, r x x) (htrans : ∀ x y z, r x y → r y z → r x z)
    (hr : IsClosed {p : X × X | r p.1 p.2})
    {A B : Set X} (hA : IsClosed A) (hAu : IsUp r A) (hB : IsClosed B) (hBd : IsUp (flip r) B)
    (hAB : Disjoint A B) :
    ∃ A' B' : Set X, IsClosed A' ∧ IsUp r A' ∧ IsClosed B' ∧ IsUp (flip r) B' ∧
      Disjoint A' B ∧ Disjoint B' A ∧ A' ∪ B' = univ := by
  set K := CompactExhaustion.choice X
  have hstep : ∀ Kp Kn : Set X, IsCompact Kp → IsCompact Kn → ∀ p : Set X × Set X,
      Good r A B Kp p.1 p.2 → ∃ q : Set X × Set X, Good r A B Kn q.1 q.2 ∧ p.1 ⊆ q.1 ∧
        p.2 ⊆ q.2 ∧ q.1 ∩ Kp ⊆ p.1 ∧ q.2 ∩ Kp ⊆ p.2 := by
    intro Kp Kn hKp hKn p hp
    obtain ⟨a', b', h⟩ := step hrefl htrans hr hA hAu hB hBd hAB hKp hKn hp
    exact ⟨(a', b'), h⟩
  choose! F hF using hstep
  obtain ⟨s, hs0, hsS⟩ : ∃ s : ℕ → Set X × Set X, s 0 = F ∅ (K 0) (∅, ∅) ∧
      ∀ n, s (n + 1) = F (K n) (K (n + 1)) (s n) :=
    ⟨fun n => Nat.rec (F ∅ (K 0) (∅, ∅)) (fun n p => F (K n) (K (n + 1)) p) n, rfl,
      fun _ => rfl⟩
  have hgood : ∀ n, Good r A B (K n) (s n).1 (s n).2 := by
    intro n
    induction n with
    | zero => rw [hs0]; exact (hF ∅ (K 0) isCompact_empty (K.isCompact 0) (∅, ∅)
        (good_empty A B)).1
    | succ n ih => rw [hsS]; exact (hF _ _ (K.isCompact n) (K.isCompact (n + 1)) _ ih).1
  have hnext : ∀ n, (s n).1 ⊆ (s (n + 1)).1 ∧ (s n).2 ⊆ (s (n + 1)).2 ∧
      (s (n + 1)).1 ∩ K n ⊆ (s n).1 ∧ (s (n + 1)).2 ∩ K n ⊆ (s n).2 := by
    intro n
    rw [hsS]
    exact (hF _ _ (K.isCompact n) (K.isCompact (n + 1)) _ (hgood n)).2
  obtain ⟨hAc, -⟩ := glue K (fun n => (s n).1) (fun n => (hgood n).closed_a)
    (fun n => (hnext n).1) (fun n => (hnext n).2.2.1)
  obtain ⟨hBc, -⟩ := glue K (fun n => (s n).2) (fun n => (hgood n).closed_b)
    (fun n => (hnext n).2.1) (fun n => (hnext n).2.2.2)
  refine ⟨⋃ n, (s n).1, ⋃ n, (s n).2, hAc, ?_, hBc, ?_, ?_, ?_, ?_⟩
  · intro x y hxy hx
    obtain ⟨n, hn⟩ := mem_iUnion.1 hx
    exact mem_iUnion.2 ⟨n, (hgood n).up_a hxy hn⟩
  · intro x y hxy hx
    obtain ⟨n, hn⟩ := mem_iUnion.1 hx
    exact mem_iUnion.2 ⟨n, (hgood n).down_b hxy hn⟩
  · exact Set.disjoint_iUnion_left.2 fun n => (hgood n).disj_a
  · exact Set.disjoint_iUnion_left.2 fun n => (hgood n).disj_b
  · refine eq_univ_of_forall fun x => ?_
    obtain ⟨n, hn⟩ := K.exists_mem x
    rcases (hgood n).cover hn with h | h
    · exact Or.inl (mem_iUnion.2 ⟨n, interior_subset h⟩)
    · exact Or.inr (mem_iUnion.2 ⟨n, interior_subset h⟩)

/-! ### Order Urysohn, through mathlib's `Urysohns.CU` -/

/-- The predicate carried by the Urysohn tree: the open set `u` is a down-set, and a closed
down-set sits between `c` and `u`. -/
def PDown (r : X → X → Prop) (c u : Set X) : Prop :=
  IsUp (flip r) u ∧ ∃ D, IsClosed D ∧ IsUp (flip r) D ∧ c ⊆ D ∧ D ⊆ u

theorem pDown_split [NormalSpace X] [WeaklyLocallyCompactSpace X] [SigmaCompactSpace X]
    (hrefl : ∀ x, r x x) (htrans : ∀ x y z, r x y → r y z → r x z)
    (hr : IsClosed {p : X × X | r p.1 p.2}) {c u : Set X} (_hc : IsClosed c)
    (hcu : PDown r c u) (hu : IsOpen u) (_hsub : c ⊆ u) :
    ∃ v : Set X, IsOpen v ∧ c ⊆ v ∧ closure v ⊆ u ∧ PDown r c v ∧ PDown r (closure v) u := by
  obtain ⟨hud, D, hD, hDd, hcD, hDu⟩ := hcu
  have hAu : IsUp r uᶜ := fun x y hxy hx hy => hx (hud hxy hy)
  have hAB : Disjoint uᶜ D := Set.disjoint_left.2 fun x hx hxD => hx (hDu hxD)
  obtain ⟨A', B', hA', hA'u, hB', hB'd, hA'D, hB'u, hcov⟩ :=
    exists_cover hrefl htrans hr hu.isClosed_compl hAu hD hDd hAB
  have hvB : A'ᶜ ⊆ B' := fun x hx => ((Set.ext_iff.1 hcov x).2 trivial).resolve_left hx
  have hB'sub : B' ⊆ u := fun x hx => by
    by_contra hxu
    exact Set.disjoint_left.1 hB'u hx hxu
  have hDv : D ⊆ A'ᶜ := fun x hxD hxA => Set.disjoint_left.1 hA'D hxA hxD
  have hcl : closure A'ᶜ ⊆ B' := closure_minimal hvB hB'
  exact ⟨A'ᶜ, hA'.isOpen_compl, hcD.trans hDv, hcl.trans hB'sub,
    ⟨hA'u.compl, D, hD, hDd, hcD, hDv⟩, ⟨hud, B', hB', hB'd, hcl, hB'sub⟩⟩

theorem approx_mono_rel (c : Urysohns.CU (PDown r)) (n : ℕ) :
    ∀ ⦃x y : X⦄, r x y → c.approx n x ≤ c.approx n y := by
  induction n generalizing c with
  | zero =>
    intro x y hxy
    simp only [Urysohns.CU.approx]
    by_cases hy : y ∈ c.U
    · have hx : x ∈ c.U := c.P_C_U.1 hxy hy
      simp [hx, hy]
    · by_cases hx : x ∈ c.U <;> simp [hx, hy]
  | succ n ih =>
    intro x y hxy
    simp only [Urysohns.CU.approx]
    exact midpoint_le_midpoint (ih c.left hxy) (ih c.right hxy)

theorem lim_mono_rel (c : Urysohns.CU (PDown r)) ⦃x y : X⦄ (hxy : r x y) :
    c.lim x ≤ c.lim y :=
  ciSup_mono (c.bddAbove_range_approx y) fun n => approx_mono_rel c n hxy

/-- **Order Urysohn.** On a locally compact σ-compact normal space with a closed preorder, if
`¬ r y x` there is a continuous `u : X → [0, 1]`, monotone along `r`, with `u x = 0`, `u y = 1`. -/
theorem exists_monotone_sep [T1Space X] [NormalSpace X] [WeaklyLocallyCompactSpace X]
    [SigmaCompactSpace X] (hrefl : ∀ x, r x x) (htrans : ∀ x y z, r x y → r y z → r x z)
    (hr : IsClosed {p : X × X | r p.1 p.2}) {x y : X} (hyx : ¬ r y x) :
    ∃ u : X → ℝ, Continuous u ∧ (∀ ⦃a b : X⦄, r a b → u a ≤ u b) ∧
      (∀ z, u z ∈ Icc (0 : ℝ) 1) ∧ u x = 0 ∧ u y = 1 := by
  have hrf := isClosed_flip hr
  have hreflf : ∀ x, flip r x x := hrefl
  have htransf : ∀ a b c, flip r a b → flip r b c → flip r a c :=
    fun a b c hab hbc => htrans c b a hbc hab
  let c : Urysohns.CU (PDown r) :=
    { C := {x}
      U := (upHull r {y})ᶜ
      P_C_U := ⟨(isUp_upHull htrans {y}).compl, upHull (flip r) {x},
        isClosed_upHull hrf isCompact_singleton, isUp_upHull htransf {x},
        subset_upHull hreflf {x}, by
          rintro z ⟨x', hx', hzx⟩ ⟨y', hy', hyz⟩
          rw [mem_singleton_iff] at hx' hy'
          subst hx' hy'
          exact hyx (htrans _ _ _ hyz hzx)⟩
      closed_C := isClosed_singleton
      open_U := (isClosed_upHull hr isCompact_singleton).isOpen_compl
      subset := by
        rintro z hz ⟨y', hy', hyz⟩
        rw [mem_singleton_iff] at hz hy'
        subst hz hy'
        exact hyx hyz
      hP := fun hc hcu hu hsub => pDown_split hrefl htrans hr hc hcu hu hsub }
  exact ⟨c.lim, c.continuous_lim, fun a b hab => lim_mono_rel c hab, c.lim_mem_Icc,
    c.lim_of_mem_C x rfl, c.lim_of_notMem_U y fun h => h (subset_upHull hrefl {y} rfl)⟩

/-- **Levin's theorem.** On a second countable, locally compact, σ-compact normal space with a
closed preorder there is a continuous `T`, monotone along `r` and strictly increasing on
`r x y ∧ ¬ r y x`. -/
theorem exists_utility [T1Space X] [NormalSpace X] [WeaklyLocallyCompactSpace X]
    [SigmaCompactSpace X] [SecondCountableTopology X] (hrefl : ∀ x, r x x)
    (htrans : ∀ x y z, r x y → r y z → r x z) (hr : IsClosed {p : X × X | r p.1 p.2}) :
    ∃ T : X → ℝ, Continuous T ∧ (∀ ⦃x y : X⦄, r x y → T x ≤ T y) ∧
      ∀ ⦃x y : X⦄, r x y → ¬ r y x → T x < T y := by
  have hsep : ∀ p : X × X, ∃ u : X → ℝ, Continuous u ∧ (∀ ⦃a b : X⦄, r a b → u a ≤ u b) ∧
      (∀ z, u z ∈ Icc (0 : ℝ) 1) ∧ (¬ r p.2 p.1 → u p.1 < u p.2) := by
    intro p
    by_cases h : r p.2 p.1
    · exact ⟨fun _ => 0, continuous_const, fun _ _ _ => le_rfl,
        fun _ => ⟨le_rfl, zero_le_one⟩, fun h' => absurd h h'⟩
    · obtain ⟨u, hu, hm, hI, h0, h1⟩ := exists_monotone_sep hrefl htrans hr h
      exact ⟨u, hu, hm, hI, fun _ => by rw [h0, h1]; exact zero_lt_one⟩
  choose U hUc hUm hUI hUs using hsep
  set N : X × X → Set (X × X) := fun p => {q | U p q.1 < U p q.2} with hNdef
  have hN : ∀ p, IsOpen (N p) := fun p =>
    isOpen_lt ((hUc p).comp continuous_fst) ((hUc p).comp continuous_snd)
  obtain ⟨S, hSc, hSU⟩ := isOpen_iUnion_countable N hN
  obtain ⟨f, hf⟩ := Set.countable_iff_exists_injective.1 hSc
  set w : S → ℝ := fun p => (1 / 2 : ℝ) ^ (f p) with hwdef
  have hw : Summable w := summable_geometric_two.comp_injective hf
  have hw0 : ∀ p, 0 < w p := fun p => pow_pos (by norm_num) _
  have hle : ∀ (p : S) z, w p * U p z ≤ w p := fun p z =>
    mul_le_of_le_one_right (hw0 p).le (hUI p z).2
  have hnn : ∀ (p : S) z, 0 ≤ w p * U p z := fun p z => mul_nonneg (hw0 p).le (hUI p z).1
  have hsum : ∀ z, Summable fun p : S => w p * U p z := fun z =>
    Summable.of_nonneg_of_le (fun p => hnn p z) (fun p => hle p z) hw
  refine ⟨fun z => ∑' p : S, w p * U p z, ?_, ?_, ?_⟩
  · refine continuous_tsum (fun p => continuous_const.mul (hUc p)) hw fun p z => ?_
    rw [Real.norm_of_nonneg (hnn p z)]
    exact hle p z
  · intro x y hxy
    exact Summable.tsum_le_tsum (fun p => mul_le_mul_of_nonneg_left (hUm p hxy) (hw0 p).le)
      (hsum x) (hsum y)
  · intro x y hxy hyx
    have hmem : (x, y) ∈ ⋃ p ∈ S, N p := by
      rw [hSU]
      exact mem_iUnion.2 ⟨(x, y), hUs (x, y) hyx⟩
    obtain ⟨p, hpS, hp⟩ := mem_iUnion₂.1 hmem
    have hp' : U p x < U p y := hp
    exact Summable.tsum_lt_tsum (i := ⟨p, hpS⟩)
      (fun q => mul_le_mul_of_nonneg_left (hUm q hxy) (hw0 q).le)
      (mul_lt_mul_of_pos_left hp' (hw0 _)) (hsum x) (hsum y)

end Levin

/-! ### In ETT: a time function, hence `CurvesExtend` -/

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable {C : Causality M}

/-- **A continuous time function in every second countable tarentin globally hyperbolic Hausdorff
spacetime** (Levin's theorem): monotone along `≤_M` and strictly increasing on `x ≤ y`, `x ≠ y`.
No measure is used. -/
theorem exists_timeFunction_of_secondCountable [T2Space M] [SecondCountableTopology M]
    (hT : C.Tarentin) (hG : C.GloballyHyperbolic) :
    ∃ τ : M → ℝ, Continuous τ ∧ (∀ x y, C.le ⊤ x y → τ x ≤ τ y) ∧
      ∀ x y, C.le ⊤ x y → x ≠ y → τ x < τ y := by
  haveI := locallyCompactSpace_of_globallyHyperbolic hT hG
  haveI := sigmaCompactSpace_of_globallyHyperbolic hT hG
  obtain ⟨τ, hτ, hmono, hstrict⟩ := Levin.exists_utility (r := fun x y => C.le ⊤ x y)
    (fun x => C.le_refl (by simp)) (fun _ _ _ => C.le_trans) (hG.isClosed_le hT)
  exact ⟨τ, hτ, fun x y h => hmono h, fun x y h hne => hstrict h fun h' => hne (hG.1 h h')⟩

/-- **`CurvesExtend` in every second countable tarentin globally hyperbolic Hausdorff
spacetime.** -/
theorem curvesExtend_of_secondCountable [T2Space M] [SecondCountableTopology M]
    (hT : C.Tarentin) (hG : C.GloballyHyperbolic) : C.CurvesExtend := by
  obtain ⟨τ, hτ, -, hs⟩ := exists_timeFunction_of_secondCountable hT hG
  exact curvesExtend_of_timeFunction hτ hs

/-- The relative form: every future causal curve of any open `W` over any interval lies on an
inextensible causal curve of `W`, parametrised by the time function. -/
theorem exists_inextensible_of_secondCountable [T2Space M] [SecondCountableTopology M]
    (hT : C.Tarentin) (hG : C.GloballyHyperbolic) {W : Opens M} {I : Set ℝ} {c : ℝ → M}
    (hc : C.CausalCurveIn W I c) :
    ∃ (τ : M → ℝ) (J : Set ℝ) (γ : ℝ → M), Continuous τ ∧ C.Inextensible W J γ ∧
      c '' I ⊆ γ '' J ∧ ∀ t ∈ J, τ (γ t) = t := by
  obtain ⟨τ, hτ, -, hs⟩ := exists_timeFunction_of_secondCountable hT hG
  obtain ⟨J, γ, h1, h2, h3⟩ := exists_inextensible_of_timeFunction hτ hs hc
  exact ⟨τ, J, γ, hτ, h1, h2, h3⟩

/-- **Lemma K's local characterisation, second countable, without `CurvesExtend`**
(`isCauchySurface_iff_local` with `hext` discharged). -/
theorem isCauchySurface_iff_local_of_secondCountable [T2Space M] [SecondCountableTopology M]
    [ConnectedSpace M] (hT : C.Tarentin) (hG : C.GloballyHyperbolic)
    (hC : C.CausallyArcConnected) (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p})
    (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) {S : Set M} (hSc : IsCompact S)
    (hSconn : IsConnected S) (hloc : C.IsLocallyCauchy S) :
    C.IsCauchySurface S ↔
      (∀ w ∈ S ∩ C.strictJplus S, ∃ N ∈ 𝓝 w, S ∩ N ⊆ C.strictJplus S) ∧
      (∀ q ∈ C.Jplus ⊤ S ∪ C.Jminus ⊤ S, q ∉ S → C.Jplus ⊤ S ∪ C.Jminus ⊤ S ∈ 𝓝 q) :=
  isCauchySurface_iff_local hT hG hC hJm hJp (curvesExtend_of_secondCountable hT hG) hSc hSconn
    hloc

/-- **Lemma K, second countable, without `CurvesExtend`**: a compact connected locally Cauchy set
is a Cauchy surface iff its strict causal future and past are open
(`isCauchySurface_iff_isOpen_strictJplus` with `hext` discharged). -/
theorem isCauchySurface_iff_isOpen_strictJplus_of_secondCountable [T2Space M]
    [SecondCountableTopology M] [ConnectedSpace M] (hT : C.Tarentin) (hG : C.GloballyHyperbolic)
    (hC : C.CausallyArcConnected) (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p})
    (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) {S : Set M} (hSc : IsCompact S)
    (hSconn : IsConnected S) (hloc : C.IsLocallyCauchy S) :
    C.IsCauchySurface S ↔ IsOpen (C.strictJplus S) ∧ IsOpen (C.dual.strictJplus S) :=
  isCauchySurface_iff_isOpen_strictJplus hT hG hC hJm hJp
    (curvesExtend_of_secondCountable hT hG) hSc hSconn hloc

end Causality

end Causal
