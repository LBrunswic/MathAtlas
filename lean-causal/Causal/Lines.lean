import Causal.Minimal
import Causal.GlobalHyperbolicity
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Connected.Basic

/-!
# Causalities on the real line

**`rem:droites_pas_plates`** — `ETT.tex:299`.

> Items $2$ and $3$ are not causally plain: for the lightlike line,
> $\mathrm{Int}\left(J^+(0)\right)=]0,+\infty[$ whereas $I^+(0)=\emptyset$.

The three lines of `ex:causalities_lines` (`ETT.tex:265`) are constructed here; items 4
(Galileo's spacetime) and 5 (Minkowski spacetime, Lorentzian manifolds) are not, so that label
is not claimed. The first half of `rem:deux_pushup` (`ETT.tex:314`) is proved: the lightlike
line has the push-up property and is not causally plain.

> **The timelike line** $(\RR,\leq,\leq)$ is $\RR$ endowed with the family of binary relations
> $(\leq_\U,\ll_\U)_{\U}$ given by: $x\leq_\U y$ (resp. $x\ll_\U y$) if and only if $x\leq y$
> (resp. $x< y$) and $x,y$ lie in the same connected component of $\U$.

## Why this file exists

A theorem about a structure is worth what the structure's inhabitants are worth. The timelike
line is shown to be a causality which is causally plain, absolutely minimal, tarentin, causal and
globally hyperbolic, and to have the push-up property: the hypotheses of the theorems of this
library are jointly satisfiable, and `GloballyHyperbolic.stronglyCausal` applies to it.

## SCOPE (disclosed)

* "`x, y` lie in the same connected component of `U`" is carried as `Icc x y ⊆ U`;
  `timelikeLine_le_iff` proves that the two say the same.
* **The spacelike line is `(ℝ, =, ∅)`.** The paper writes `(ℝ, ∅, ∅)`; axiom (a) of
  `defi:causalite` asks `≤_U` reflexive, so the causal relation carried is the diagonal.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Relation

/-! ### Openness of the chronological relation of the line -/

theorem isOpen_setOf_lt_and_Icc_subset_right (U : Opens ℝ) (x : ℝ) :
    IsOpen {y : ℝ | x < y ∧ Icc x y ⊆ (U : Set ℝ)} := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨hxy, hsub⟩
  have hyU : y ∈ (U : Set ℝ) := hsub (right_mem_Icc.2 hxy.le)
  obtain ⟨l, u, ⟨hl, hu⟩, hlu⟩ := mem_nhds_iff_exists_Ioo_subset.1 (U.isOpen.mem_nhds hyU)
  refine Filter.mem_of_superset (Ioo_mem_nhds (max_lt hxy hl) hu) ?_
  rintro y' ⟨hy'1, hy'2⟩
  refine ⟨(le_max_left _ _).trans_lt hy'1, ?_⟩
  rintro z ⟨hz1, hz2⟩
  by_cases hzy : z ≤ y
  · exact hsub ⟨hz1, hzy⟩
  · exact hlu ⟨hl.trans (not_le.1 hzy), hz2.trans_lt hy'2⟩

theorem isOpen_setOf_lt_and_Icc_subset_left (U : Opens ℝ) (y : ℝ) :
    IsOpen {x : ℝ | x < y ∧ Icc x y ⊆ (U : Set ℝ)} := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨hxy, hsub⟩
  have hxU : x ∈ (U : Set ℝ) := hsub (left_mem_Icc.2 hxy.le)
  obtain ⟨l, u, ⟨hl, hu⟩, hlu⟩ := mem_nhds_iff_exists_Ioo_subset.1 (U.isOpen.mem_nhds hxU)
  refine Filter.mem_of_superset (Ioo_mem_nhds hl (lt_min hxy hu)) ?_
  rintro x' ⟨hx'1, hx'2⟩
  refine ⟨hx'2.trans_le (min_le_left _ _), ?_⟩
  rintro z ⟨hz1, hz2⟩
  by_cases hxz : x ≤ z
  · exact hsub ⟨hxz, hz2⟩
  · exact hlu ⟨hx'1.trans_le hz1, (not_le.1 hxz).trans hu⟩

/-! ### The three lines -/

/-- `ex:causalities_lines`, item 1: **the timelike line** `(ℝ, ≤, <)`. -/
def timelikeLine : Causality ℝ where
  le U x y := x ≤ y ∧ Icc x y ⊆ (U : Set ℝ)
  lt U x y := x < y ∧ Icc x y ⊆ (U : Set ℝ)
  le_mem_left h := h.2 (left_mem_Icc.2 h.1)
  le_mem_right h := h.2 (right_mem_Icc.2 h.1)
  lt_mem_left h := h.2 (left_mem_Icc.2 h.1.le)
  lt_mem_right h := h.2 (right_mem_Icc.2 h.1.le)
  le_refl hx := ⟨le_rfl, by simpa using hx⟩
  le_trans h₁ h₂ := ⟨h₁.1.trans h₂.1, Icc_subset_Icc_union_Icc.trans (union_subset h₁.2 h₂.2)⟩
  lt_trans h₁ h₂ := ⟨h₁.1.trans h₂.1, Icc_subset_Icc_union_Icc.trans (union_subset h₁.2 h₂.2)⟩
  le_mono h _ _ h' := ⟨h'.1, fun _ hz => h (h'.2 hz)⟩
  lt_mono h _ _ h' := ⟨h'.1, fun _ hz => h (h'.2 hz)⟩
  le_of_lt h := ⟨h.1.le, h.2⟩
  isOpen_lt_right := isOpen_setOf_lt_and_Icc_subset_right
  isOpen_lt_left := isOpen_setOf_lt_and_Icc_subset_left

/-- `ex:causalities_lines`, item 2: **the lightlike line** `(ℝ, ≤, ∅)`. -/
def lightlikeLine : Causality ℝ where
  le U x y := x ≤ y ∧ Icc x y ⊆ (U : Set ℝ)
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

/-- `ex:causalities_lines`, item 3: **the spacelike line**, the causal relation being the
diagonal. -/
def spacelikeLine : Causality ℝ where
  le U x y := x = y ∧ x ∈ U
  lt _ _ _ := False
  le_mem_left h := h.2
  le_mem_right h := h.1 ▸ h.2
  lt_mem_left h := h.elim
  lt_mem_right h := h.elim
  le_refl hx := ⟨rfl, hx⟩
  le_trans h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2⟩
  lt_trans h _ := h
  le_mono h _ _ h' := ⟨h'.1, h h'.2⟩
  lt_mono _ _ _ h' := h'
  le_of_lt h := h.elim
  isOpen_lt_right _ _ := by simp
  isOpen_lt_left _ _ := by simp

variable {U : Opens ℝ} {x y : ℝ}

@[simp] theorem timelikeLine_le : timelikeLine.le U x y ↔ x ≤ y ∧ Icc x y ⊆ (U : Set ℝ) :=
  Iff.rfl

@[simp] theorem timelikeLine_lt : timelikeLine.lt U x y ↔ x < y ∧ Icc x y ⊆ (U : Set ℝ) :=
  Iff.rfl

@[simp] theorem lightlikeLine_le : lightlikeLine.le U x y ↔ x ≤ y ∧ Icc x y ⊆ (U : Set ℝ) :=
  Iff.rfl

@[simp] theorem lightlikeLine_lt : lightlikeLine.lt U x y ↔ False := Iff.rfl

@[simp] theorem spacelikeLine_le : spacelikeLine.le U x y ↔ x = y ∧ x ∈ U := Iff.rfl

@[simp] theorem spacelikeLine_lt : spacelikeLine.lt U x y ↔ False := Iff.rfl

/-- The relation of the timelike line is the paper's: `x ≤ y` and `x, y` lie in the same
connected component of `U`. -/
theorem timelikeLine_le_iff :
    timelikeLine.le U x y ↔ x ≤ y ∧ x ∈ U ∧ y ∈ connectedComponentIn (U : Set ℝ) x := by
  rw [timelikeLine_le]
  constructor
  · rintro ⟨hxy, hsub⟩
    have hx : x ∈ Icc x y := left_mem_Icc.2 hxy
    exact ⟨hxy, hsub hx,
      isPreconnected_Icc.subset_connectedComponentIn hx hsub (right_mem_Icc.2 hxy)⟩
  · rintro ⟨hxy, hx, hy⟩
    refine ⟨hxy, ?_⟩
    have hK : IsPreconnected (connectedComponentIn (U : Set ℝ) x) :=
      isPreconnected_connectedComponentIn
    exact (hK.Icc_subset (mem_connectedComponentIn hx) hy).trans
      (connectedComponentIn_subset _ _)

/-! ### The timelike line satisfies the hypotheses of the theory -/

theorem timelikeLine_diamond_top (p q : ℝ) : timelikeLine.diamond ⊤ p q = Icc p q := by
  ext z
  simp [Causality.mem_diamond]

theorem timelikeLine_isCausal : timelikeLine.IsCausal :=
  fun _ _ hxy hyx => le_antisymm hxy.1 hyx.1

theorem timelikeLine_globallyHyperbolic : timelikeLine.GloballyHyperbolic :=
  ⟨timelikeLine_isCausal, fun p q => by
    rw [timelikeLine_diamond_top]
    exact isCompact_Icc⟩

theorem timelikeLine_tarentin : timelikeLine.Tarentin := by
  intro x N hN
  obtain ⟨l, u, ⟨hl, hu⟩, hlu⟩ := mem_nhds_iff_exists_Ioo_subset.1 hN
  refine ⟨(l + x) / 2, hlu ⟨by linarith, by linarith⟩, (x + u) / 2,
    hlu ⟨by linarith, by linarith⟩, ?_⟩
  rw [Causality.openDiamond, timelikeLine_diamond_top]
  exact interior_maximal Ioo_subset_Icc_self isOpen_Ioo ⟨by linarith, by linarith⟩

theorem timelikeLine_pushUp : timelikeLine.PushUp := by
  rw [Causality.pushUp_iff]
  intro U x y z
  exact ⟨fun h₁ h₂ => ⟨h₁.1.trans_le h₂.1,
      Icc_subset_Icc_union_Icc.trans (union_subset h₁.2 h₂.2)⟩,
    fun h₁ h₂ => ⟨h₁.1.trans_lt h₂.1,
      Icc_subset_Icc_union_Icc.trans (union_subset h₁.2 h₂.2)⟩⟩

theorem timelikeLine_causallyPlain : timelikeLine.CausallyPlain := by
  intro U A
  constructor
  · refine interior_subset.trans ?_
    rintro y ⟨a, ha, hay, hsub⟩
    rw [mem_closure_iff_nhds]
    intro N hN
    have hyU : y ∈ (U : Set ℝ) := hsub (right_mem_Icc.2 hay)
    obtain ⟨l, u, ⟨hl, hu⟩, hlu⟩ :=
      mem_nhds_iff_exists_Ioo_subset.1 (Filter.inter_mem hN (U.isOpen.mem_nhds hyU))
    have hmem : (y + u) / 2 ∈ Ioo l u := ⟨by linarith, by linarith⟩
    refine ⟨(y + u) / 2, (hlu hmem).1, a, ha, by linarith, ?_⟩
    rintro z ⟨hz1, hz2⟩
    by_cases hzy : z ≤ y
    · exact hsub ⟨hz1, hzy⟩
    · exact (hlu ⟨hl.trans (not_le.1 hzy), by linarith⟩).2
  · refine interior_subset.trans ?_
    rintro y ⟨a, ha, hya, hsub⟩
    rw [mem_closure_iff_nhds]
    intro N hN
    have hyU : y ∈ (U : Set ℝ) := hsub (left_mem_Icc.2 hya)
    obtain ⟨l, u, ⟨hl, hu⟩, hlu⟩ :=
      mem_nhds_iff_exists_Ioo_subset.1 (Filter.inter_mem hN (U.isOpen.mem_nhds hyU))
    have hmem : (l + y) / 2 ∈ Ioo l u := ⟨by linarith, by linarith⟩
    refine ⟨(l + y) / 2, (hlu hmem).1, a, ha, by linarith, ?_⟩
    rintro z ⟨hz1, hz2⟩
    by_cases hyz : y ≤ z
    · exact hsub ⟨hyz, hz2⟩
    · exact (hlu ⟨by linarith, (not_le.1 hyz).trans hu⟩).2

/-- A segment contained in `V` is subdivided into segments each contained in `V` and in a member
of a cover. -/
theorem exists_subdivision {S : Set (Opens ℝ)} {W V : Opens ℝ}
    (hS : ∀ x ∈ W, ∃ O ∈ S, x ∈ O) (hV : V ≤ W) (hxy : x ≤ y)
    (hsub : Icc x y ⊆ (V : Set ℝ)) :
    ∃ t : ℕ → ℝ, t 0 = x ∧ Monotone t ∧ (∃ m, ∀ n ≥ m, t n = y) ∧
      ∀ n, ∃ O ∈ S, Icc (t n) (t (n + 1)) ⊆ ((V ⊓ O : Opens ℝ) : Set ℝ) := by
  let c : S → Set (Icc x y) := fun O => Subtype.val ⁻¹' ((V ⊓ O.1 : Opens ℝ) : Set ℝ)
  have hc₁ : ∀ O, IsOpen (c O) := fun O => (V ⊓ O.1).isOpen.preimage continuous_subtype_val
  have hc₂ : univ ⊆ ⋃ O, c O := by
    rintro ⟨z, hz⟩ -
    obtain ⟨O, hO, hzO⟩ := hS z (hV (hsub hz))
    exact mem_iUnion.2 ⟨⟨O, hO⟩, ⟨hsub hz, hzO⟩⟩
  obtain ⟨t, ht0, hmono, ⟨m, hm⟩, ht⟩ := exists_monotone_Icc_subset_open_cover_Icc hxy hc₁ hc₂
  refine ⟨fun n => (t n : ℝ), ht0, fun a b hab => hmono hab, ⟨m, hm⟩, fun n => ?_⟩
  obtain ⟨O, hO⟩ := ht n
  refine ⟨O.1, O.2, ?_⟩
  rintro z ⟨hz1, hz2⟩
  have hz : z ∈ Icc x y := ⟨(t n).2.1.trans hz1, hz2.trans (t (n + 1)).2.2⟩
  exact hO (show (⟨z, hz⟩ : Icc x y) ∈ Icc (t n) (t (n + 1)) from ⟨hz1, hz2⟩)

/-- The timelike line is absolutely minimal on each of its open subsets. -/
theorem timelikeLine_absolutelyMinimalOn (W : Opens ℝ) :
    timelikeLine.AbsolutelyMinimalOn W := by
  intro S hS V hV x y
  constructor
  · rintro ⟨hxy, hsub⟩
    obtain ⟨t, ht0, hmono, ⟨m, hm⟩, ht⟩ := exists_subdivision hS hV hxy hsub
    have hchain : ∀ n, ReflTransGen
        (fun a b => ∃ O ∈ S, timelikeLine.le (V ⊓ O) a b) x (t n) := by
      intro n
      induction n with
      | zero => rw [ht0]
      | succ n ih =>
        obtain ⟨O, hO, hsubO⟩ := ht n
        exact ih.tail ⟨O, hO, hmono (Nat.le_succ n), hsubO⟩
    have hy := hchain m
    rw [hm m le_rfl] at hy
    -- a last, reflexive, step
    obtain ⟨O, hO, hyO⟩ := hS y (hV (hsub (right_mem_Icc.2 hxy)))
    have hyV : y ∈ V := hsub (right_mem_Icc.2 hxy)
    exact TransGen.tail' hy ⟨O, hO, timelikeLine.le_refl ⟨hyV, hyO⟩⟩
  · rintro ⟨hxy, hsub⟩
    obtain ⟨t, ht0, hmono, ⟨m, hm⟩, ht⟩ := exists_subdivision hS hV hxy.le hsub
    have hchain : ∀ n, ReflTransGen
        (fun a b => ∃ O ∈ S, timelikeLine.lt (V ⊓ O) a b) x (t n) := by
      intro n
      induction n with
      | zero => rw [ht0]
      | succ n ih =>
        rcases (hmono (Nat.le_succ n)).eq_or_lt with h | h
        · rw [← h]; exact ih
        · obtain ⟨O, hO, hsubO⟩ := ht n
          exact ih.tail ⟨O, hO, h, hsubO⟩
    have hy := hchain m
    rw [hm m le_rfl] at hy
    rcases reflTransGen_iff_eq_or_transGen.1 hy with h | h
    · exact absurd h hxy.ne'
    · exact h

theorem timelikeLine_absolutelyMinimal : timelikeLine.AbsolutelyMinimal :=
  Precausality.absolutelyMinimal_iff.2 (timelikeLine_absolutelyMinimalOn ⊤)

/-- The generalised statement `prop:GH_fortement_causal` applies to the timelike line. -/
theorem timelikeLine_stronglyCausal : timelikeLine.StronglyCausal :=
  timelikeLine_globallyHyperbolic.stronglyCausal timelikeLine_tarentin

/-! ### The lightlike and the spacelike lines are not causally plain -/

/-- `rem:droites_pas_plates`, lightlike line: `Int(J^+(0)) = ]0,+∞[` whereas `I^+(0) = ∅`. -/
theorem lightlikeLine_interior_Jplus_zero :
    interior (lightlikeLine.Jplus ⊤ {0}) = Ioi 0 ∧ lightlikeLine.Iplus ⊤ {0} = ∅ := by
  constructor
  · have : lightlikeLine.Jplus ⊤ {0} = Ici 0 := by
      ext z
      simp
    rw [this, interior_Ici]
  · ext z
    simp

theorem lightlikeLine_not_causallyPlain : ¬ lightlikeLine.CausallyPlain := by
  intro h
  have h1 : (1 : ℝ) ∈ interior (lightlikeLine.Jplus ⊤ {0}) := by
    rw [lightlikeLine_interior_Jplus_zero.1]
    exact mem_Ioi.2 one_pos
  have h2 := (h ⊤ {0}).1 h1
  rw [lightlikeLine_interior_Jplus_zero.2, closure_empty] at h2
  exact h2

theorem spacelikeLine_not_causallyPlain : ¬ spacelikeLine.CausallyPlain := by
  intro h
  have hJ : spacelikeLine.Jplus ⊤ univ = univ := by
    ext z
    simp [Precausality.mem_Jplus]
  have hI : spacelikeLine.Iplus ⊤ univ = ∅ := by
    ext z
    simp [Precausality.mem_Iplus]
  have h0 : (0 : ℝ) ∈ interior (spacelikeLine.Jplus ⊤ univ) := by
    rw [hJ, interior_univ]
    trivial
  have h2 := (h ⊤ univ).1 h0
  rw [hI, closure_empty] at h2
  exact h2

/-- **`rem:droites_pas_plates`.** The lightlike and the spacelike lines are not causally
plain. -/
theorem lines_not_causallyPlain :
    ¬ lightlikeLine.CausallyPlain ∧ ¬ spacelikeLine.CausallyPlain :=
  ⟨lightlikeLine_not_causallyPlain, spacelikeLine_not_causallyPlain⟩

/-- `rem:deux_pushup`, first half: the lightlike line has the push-up property, vacuously, and
is not causally plain. -/
theorem lightlikeLine_pushUp : lightlikeLine.PushUp := by
  rw [Causality.pushUp_iff]
  intro U x y z
  exact ⟨fun h _ => h.elim, fun _ h => h.elim⟩

end Causal
