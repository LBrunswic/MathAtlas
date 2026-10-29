import Causal.Curves
import Causal.Generated
import Causal.Reachable

/-!
# Causal arc-connectedness

**`def:causal_arc_connectedness`** — `ETT.tex:403`.
**`def:local_causal_arc_connectedness`** — `ETT.tex:411`. **`rem:cac_local`** — `ETT.tex:415`.
**`prop:cac_engendre`** — `ETT.tex:421`. **`cor:causalement_connexe_minimal`** — `ETT.tex:458`.
**`lem:precausalite_restriction_minimale`** — `ETT.tex:491`.
**`lem:pushup_local`** — `ETT.tex:557`. **`lem:restriction_convexe`** — `ETT.tex:1063`.

All of them with the causal curves of `Causal.Curves`, whose definition the author ruled on
2026-09-27 (DEC-6).

> $M$ is causally arc-connected if for every open subset $\U$ and all $p,q\in \U$ the following
> are equivalent: (i) $p\leq_\U q$ (resp. $p\ll_\U q$); (ii) there exists a future causal (resp.
> future chronal) curve $c:[0,1]\rightarrow \U$ with $c(0)=p$ and $c(1)=q$.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `prop:cac_engendre`: a cover by causally arc-connected open subsets | ✓ carried |
| — `M` locally causally arc-connected | ⚠ weakened: not used (it follows from the cover and `rem:cac_local`) |
| `cor:causalement_connexe_minimal`: causally arc-connected | ✓ carried; proved for every open subset (`CausallyArcConnectedOn.absolutelyMinimalOn`) |
| `lem:precausalite_restriction_minimale`: locally causally arc-connected, absolutely minimal | ✓ carried |
| `lem:pushup_local`: causally arc-connected; a cover by open subsets having push-up | ✓ carried |
| `lem:restriction_convexe`: causally arc-connected; `U` open, causally convex in `M` | ✓ carried |
| second countable, Hausdorff | ⚠ weakened: not used |

## SCOPE (disclosed)

* With the curves of `Causal.Curves` the implication (ii)⇒(i) of
  `def:causal_arc_connectedness` holds in every topological spacetime
  (`CausalCurveOn.le_of_le`, `ChronalCurveOn.lt_of_lt`): causal arc-connectedness is the
  existence of curves.
* `lem:restriction_convexe` is proved for points and for subsets, for `J^±`, `I^±` and `K^±`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Relation Filter

universe u v

variable {M : Type u} [TopologicalSpace M]

namespace CurveOn

variable {r : Opens M → M → M → Prop} {W V : Opens M} {c c₁ c₂ : ℝ → M} {a b : ℝ}

/-- Along a curve of `V`, two points are joined by a chain of relations localised in the members
of a cover: the Lebesgue-number step of `prop:cac_engendre`. -/
theorem transGen_link (hc : CurveOn r V c a b) (S : Set (Opens M))
    (hS : ∀ t ∈ Icc a b, ∃ O ∈ S, c t ∈ O) {s s' : ℝ} (hs : a ≤ s) (hss' : s < s')
    (hs' : s' ≤ b) : TransGen (fun x y => ∃ O ∈ S, r (V ⊓ O) x y) (c s) (c s') := by
  have hloc : ∀ τ : Icc s s', ∃ O ∈ S, ∃ l u, l < τ.1 ∧ τ.1 < u ∧ ∀ x ∈ Icc a b,
      ∀ y ∈ Icc a b, l < x → x < y → y < u → r (V ⊓ O) (c x) (c y) := fun τ => by
    have hτ : τ.1 ∈ Icc a b := ⟨hs.trans τ.2.1, τ.2.2.trans hs'⟩
    obtain ⟨O, hO, hcO⟩ := hS τ.1 hτ
    exact ⟨O, hO, hc.rel τ.1 hτ (V ⊓ O) inf_le_left ⟨hc.mem τ.1 hτ, hcO⟩⟩
  choose O hO l u hl hu hrel using hloc
  obtain ⟨t, ht0, hmono, ⟨m, hm⟩, htmem, ht⟩ :=
    exists_subdivision_Icc hss'.le (O := fun τ : Icc s s' => Ioo (l τ) (u τ))
      (fun _ => isOpen_Ioo)
      (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hl ⟨x, hx⟩, hu ⟨x, hx⟩⟩)
  have hchain : ∀ n, t n = s ∨
      TransGen (fun x y => ∃ O ∈ S, r (V ⊓ O) x y) (c s) (c (t n)) := by
    intro n
    induction n with
    | zero => exact Or.inl ht0
    | succ n ih =>
      rcases (hmono (Nat.le_succ n)).eq_or_lt with h | h
      · rw [← h]; exact ih
      · obtain ⟨τ, hτ⟩ := ht n
        have h1 : t n ∈ Icc a b := ⟨hs.trans (htmem n).1, (htmem n).2.trans hs'⟩
        have h2 : t (n + 1) ∈ Icc a b :=
          ⟨hs.trans (htmem (n + 1)).1, (htmem (n + 1)).2.trans hs'⟩
        have hstep : ∃ O' ∈ S, r (V ⊓ O') (c (t n)) (c (t (n + 1))) :=
          ⟨O τ, hO τ, hrel τ _ h1 _ h2 (hτ (left_mem_Icc.2 h.le)).1 h
            (hτ (right_mem_Icc.2 h.le)).2⟩
        rcases ih with h0 | h0
        · rw [h0] at hstep; exact Or.inr (TransGen.single hstep)
        · exact Or.inr (h0.tail hstep)
  have hend := hchain m
  rw [hm m le_rfl] at hend
  rcases hend with h | h
  · exact absurd h hss'.ne'
  · exact h

/-- Two curves over `[0, 1]` with a common endpoint concatenate into a curve over `[0, 1]`. -/
theorem exists_concat (hr : IsRelFamily r) (h₁ : CurveOn r W c₁ 0 1) (h₂ : CurveOn r W c₂ 0 1)
    (h : c₁ 1 = c₂ 0) : ∃ c, CurveOn r W c 0 1 ∧ c 0 = c₁ 0 ∧ c 1 = c₂ 1 := by
  -- `c₂` moved over `[1, 2]`
  have h₂' : CurveOn r W (fun t => c₂ (1 * t + (-1))) 1 2 :=
    comp_affine one_pos (by norm_num; exact h₂)
  have hglue := concat hr h₁ h₂' zero_le_one one_le_two (by simpa using h)
  -- back over `[0, 1]`
  have hfin := comp_affine (k := 2) (m := 0) (a' := 0) (b' := 1) two_pos
    (by norm_num; exact hglue)
  refine ⟨_, hfin, ?_, ?_⟩
  · simp
  · norm_num

/-- Reversing the parameter of a curve gives a curve for the reversed relations. -/
theorem reverse (hc : CurveOn r W c a b) :
    CurveOn (fun N x y => r N y x) W (fun t => c (a + b - t)) a b where
  mem t ht := hc.mem _ ⟨by linarith [ht.2], by linarith [ht.1]⟩
  rel t ht N hN htN := by
    obtain ⟨l, u, hl, hu, hrel⟩ :=
      hc.rel (a + b - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩ N hN htN
    refine ⟨a + b - u, a + b - l, by linarith, by linarith, fun s hs s' hs' h1 h2 h3 => ?_⟩
    exact hrel (a + b - s') ⟨by linarith [hs'.2], by linarith [hs'.1]⟩ (a + b - s)
      ⟨by linarith [hs.2], by linarith [hs.1]⟩ (by linarith) (by linarith) (by linarith)

end CurveOn

namespace Causality

variable (C : Causality M)

/-- `def:causal_arc_connectedness`, for the open subset `W` seen as a spacetime. -/
def CausallyArcConnectedOn (W : Opens M) : Prop :=
  ∀ U : Opens M, U ≤ W → ∀ p q : M,
    (C.le U p q ↔ ∃ c : ℝ → M, C.CausalCurveOn U c 0 1 ∧ c 0 = p ∧ c 1 = q) ∧
    (C.lt U p q ↔ ∃ c : ℝ → M, C.ChronalCurveOn U c 0 1 ∧ c 0 = p ∧ c 1 = q)

/-- `def:causal_arc_connectedness`. -/
def CausallyArcConnected : Prop := C.CausallyArcConnectedOn ⊤

/-- `def:local_causal_arc_connectedness`. -/
def LocallyCausallyArcConnected : Prop :=
  ∀ (x : M), ∀ N ∈ 𝓝 x, ∃ V : Opens M, x ∈ V ∧ (V : Set M) ⊆ N ∧ C.CausallyArcConnectedOn V

/-- `defi:pushup`, for the open subset `W` seen as a spacetime, in relational form. -/
def PushUpOn (W : Opens M) : Prop :=
  ∀ U : Opens M, U ≤ W → ∀ ⦃x y z : M⦄,
    (C.lt U x y → C.le U y z → C.lt U x z) ∧ (C.le U x y → C.lt U y z → C.lt U x z)

variable {C} {W W' U V : Opens M} {p q x y z : M}

theorem pushUpOn_top : C.PushUpOn ⊤ ↔ C.PushUp := by
  rw [pushUp_iff]
  exact ⟨fun h U => h U le_top, fun h U _ => h U⟩

theorem dual_pushUpOn : C.dual.PushUpOn W ↔ C.PushUpOn W :=
  ⟨fun h U hU _ _ _ => ⟨fun h₁ h₂ => (h U hU).2 h₂ h₁, fun h₁ h₂ => (h U hU).1 h₂ h₁⟩,
    fun h U hU _ _ _ => ⟨fun h₁ h₂ => (h U hU).2 h₂ h₁, fun h₁ h₂ => (h U hU).1 h₂ h₁⟩⟩

/-- Causal arc-connectedness is the existence of curves: the converse implications hold in every
topological spacetime. -/
theorem causallyArcConnectedOn_iff : C.CausallyArcConnectedOn W ↔
    ∀ U : Opens M, U ≤ W → ∀ p q : M,
      (C.le U p q → ∃ c : ℝ → M, C.CausalCurveOn U c 0 1 ∧ c 0 = p ∧ c 1 = q) ∧
      (C.lt U p q → ∃ c : ℝ → M, C.ChronalCurveOn U c 0 1 ∧ c 0 = p ∧ c 1 = q) := by
  constructor
  · intro h U hU p q
    exact ⟨(h U hU p q).1.1, (h U hU p q).2.1⟩
  · intro h U hU p q
    refine ⟨⟨(h U hU p q).1, ?_⟩, ⟨(h U hU p q).2, ?_⟩⟩
    · rintro ⟨c, hc, rfl, rfl⟩
      exact hc.le_of_le le_rfl zero_le_one le_rfl
    · rintro ⟨c, hc, rfl, rfl⟩
      exact hc.lt_of_lt le_rfl zero_lt_one le_rfl

/-- `rem:cac_local`: "every open subset of a causally arc-connected topological spacetime is
itself causally arc-connected". -/
theorem CausallyArcConnectedOn.mono (h : C.CausallyArcConnectedOn W) (hW : W' ≤ W) :
    C.CausallyArcConnectedOn W' := fun U hU => h U (hU.trans hW)

/-- `rem:cac_local`: "a causally arc-connected topological spacetime is in particular locally
causally arc-connected". -/
theorem CausallyArcConnected.locallyCausallyArcConnected (h : C.CausallyArcConnected) :
    C.LocallyCausallyArcConnected := fun _ N hN =>
  ⟨⟨interior N, isOpen_interior⟩, mem_interior_iff_mem_nhds.2 hN, interior_subset,
    CausallyArcConnectedOn.mono h le_top⟩

theorem dual_causallyArcConnectedOn :
    C.dual.CausallyArcConnectedOn W ↔ C.CausallyArcConnectedOn W := by
  have key : ∀ D : Causality M, D.CausallyArcConnectedOn W → D.dual.CausallyArcConnectedOn W := by
    intro D h
    rw [causallyArcConnectedOn_iff]
    intro U hU p q
    refine ⟨fun hpq => ?_, fun hpq => ?_⟩
    · obtain ⟨c, hc, h0, h1⟩ := (h U hU q p).1.1 hpq
      refine ⟨fun t => c (0 + 1 - t), CurveOn.reverse hc, ?_, ?_⟩
      · simpa using h1
      · simpa using h0
    · obtain ⟨c, hc, h0, h1⟩ := (h U hU q p).2.1 hpq
      refine ⟨fun t => c (0 + 1 - t), CurveOn.reverse hc, ?_, ?_⟩
      · simpa using h1
      · simpa using h0
  exact ⟨fun h => by simpa using key _ h, key C⟩

/-! ### `cor:causalement_connexe_minimal`, `prop:cac_engendre` -/

/-- `cor:causalement_connexe_minimal`, for every open subset: a causally arc-connected open
subset is absolutely minimal. -/
theorem CausallyArcConnectedOn.absolutelyMinimalOn (h : C.CausallyArcConnectedOn W) :
    C.AbsolutelyMinimalOn W := by
  intro S hS V hV x y
  refine ⟨fun hxy => ?_, fun hxy => ?_⟩
  · obtain ⟨c, hc, rfl, rfl⟩ := (h V hV x y).1.1 hxy
    exact CurveOn.transGen_link hc S
      (fun t ht => hS _ (hV (hc.mem t ht))) le_rfl zero_lt_one le_rfl
  · obtain ⟨c, hc, rfl, rfl⟩ := (h V hV x y).2.1 hxy
    exact CurveOn.transGen_link hc S
      (fun t ht => hS _ (hV (hc.mem t ht))) le_rfl zero_lt_one le_rfl

/-- `cor:causalement_connexe_minimal`. "If `M` is causally arc-connected, then the causality of
`M` is absolutely minimal." -/
theorem CausallyArcConnected.absolutelyMinimal (h : C.CausallyArcConnected) :
    C.AbsolutelyMinimal :=
  Precausality.absolutelyMinimal_iff.2 (CausallyArcConnectedOn.absolutelyMinimalOn h)

variable {ι : Type v} {O : ι → Opens M}

/-- `prop:cac_engendre`, (i)⇒(ii): a chain of relations localised in causally arc-connected open
subsets is realised by a curve. -/
theorem exists_causalCurveOn_of_transGen (hO : ∀ i, C.CausallyArcConnectedOn (O i))
    (h : TransGen (Precausality.LinkLe O (fun _ => C.toPrecausality) V) p q) :
    ∃ c : ℝ → M, C.CausalCurveOn V c 0 1 ∧ c 0 = p ∧ c 1 = q := by
  have link : ∀ a b, Precausality.LinkLe O (fun _ => C.toPrecausality) V a b →
      ∃ c : ℝ → M, C.CausalCurveOn V c 0 1 ∧ c 0 = a ∧ c 1 = b := by
    rintro a b ⟨i, hi⟩
    obtain ⟨c, hc, h0, h1⟩ := ((hO i) (V ⊓ O i) inf_le_right a b).1.1 hi
    exact ⟨c, CurveOn.mono_opens C.isRelFamily_le hc inf_le_left, h0, h1⟩
  induction h with
  | single hl => exact link _ _ hl
  | tail _ hl ih =>
    obtain ⟨c₁, hc₁, h0, h1⟩ := ih
    obtain ⟨c₂, hc₂, h0', h1'⟩ := link _ _ hl
    obtain ⟨c, hc, hc0, hc1⟩ :=
      CurveOn.exists_concat C.isRelFamily_le hc₁ hc₂ (h1.trans h0'.symm)
    exact ⟨c, hc, hc0.trans h0, hc1.trans h1'⟩

theorem exists_chronalCurveOn_of_transGen (hO : ∀ i, C.CausallyArcConnectedOn (O i))
    (h : TransGen (Precausality.LinkLt O (fun _ => C.toPrecausality) V) p q) :
    ∃ c : ℝ → M, C.ChronalCurveOn V c 0 1 ∧ c 0 = p ∧ c 1 = q := by
  have link : ∀ a b, Precausality.LinkLt O (fun _ => C.toPrecausality) V a b →
      ∃ c : ℝ → M, C.ChronalCurveOn V c 0 1 ∧ c 0 = a ∧ c 1 = b := by
    rintro a b ⟨i, hi⟩
    obtain ⟨c, hc, h0, h1⟩ := ((hO i) (V ⊓ O i) inf_le_right a b).2.1 hi
    exact ⟨c, CurveOn.mono_opens C.isRelFamily_lt hc inf_le_left, h0, h1⟩
  induction h with
  | single hl => exact link _ _ hl
  | tail _ hl ih =>
    obtain ⟨c₁, hc₁, h0, h1⟩ := ih
    obtain ⟨c₂, hc₂, h0', h1'⟩ := link _ _ hl
    obtain ⟨c, hc, hc0, hc1⟩ :=
      CurveOn.exists_concat C.isRelFamily_lt hc₁ hc₂ (h1.trans h0'.symm)
    exact ⟨c, hc, hc0.trans h0, hc1.trans h1'⟩

/-- `prop:cac_engendre`. For a cover of `M` by causally arc-connected open subsets: the
causality of `M` is the causality generated by the family if and only if `M` is causally
arc-connected. -/
theorem generated_eq_iff_causallyArcConnected (hcover : ∀ x : M, ∃ i, x ∈ O i)
    (hO : ∀ i, C.CausallyArcConnectedOn (O i)) :
    Causality.generated O hcover (fun _ => C) = C ↔ C.CausallyArcConnected := by
  constructor
  · intro h
    rw [CausallyArcConnected, causallyArcConnectedOn_iff]
    intro V _ p q
    refine ⟨fun hpq => ?_, fun hpq => ?_⟩
    · have hpq' : (Causality.generated O hcover (fun _ => C)).le V p q := by rw [h]; exact hpq
      exact exists_causalCurveOn_of_transGen hO hpq'
    · have hpq' : (Causality.generated O hcover (fun _ => C)).lt V p q := by rw [h]; exact hpq
      exact exists_chronalCurveOn_of_transGen hO hpq'
  · intro h
    have hmin := CausallyArcConnectedOn.absolutelyMinimalOn h
    ext V p q
    · exact ⟨Precausality.generated_le_imp (hU := hcover) C.toPrecausality
          (fun _ _ _ _ _ hab => hab),
        fun hpq => hmin.linkLe_of_family O (fun x _ => hcover x) le_top hpq⟩
    · exact ⟨Precausality.generated_lt_imp (hU := hcover) C.toPrecausality
          (fun _ _ _ _ _ hab => hab),
        fun hpq => hmin.linkLt_of_family O (fun x _ => hcover x) le_top hpq⟩

/-- `lem:precausalite_restriction_minimale`. A locally causally arc-connected spacetime whose
causality is absolutely minimal is causally arc-connected. -/
theorem LocallyCausallyArcConnected.causallyArcConnected (hloc : C.LocallyCausallyArcConnected)
    (hmin : C.AbsolutelyMinimal) : C.CausallyArcConnected := by
  have hex : ∀ x : M, ∃ V : Opens M, x ∈ V ∧ C.CausallyArcConnectedOn V := fun x => by
    obtain ⟨V, hxV, -, hV⟩ := hloc x univ univ_mem
    exact ⟨V, hxV, hV⟩
  choose O hxO hO using hex
  have hcover : ∀ x : M, ∃ i, x ∈ O i := fun x => ⟨x, hxO x⟩
  refine (generated_eq_iff_causallyArcConnected hcover hO).1 ?_
  have hmin' := Precausality.absolutelyMinimal_iff.1 hmin
  ext V p q
  · exact ⟨Precausality.generated_le_imp (hU := hcover) C.toPrecausality
        (fun _ _ _ _ _ hab => hab),
      fun hpq => hmin'.linkLe_of_family O (fun x _ => hcover x) le_top hpq⟩
  · exact ⟨Precausality.generated_lt_imp (hU := hcover) C.toPrecausality
        (fun _ _ _ _ _ hab => hab),
      fun hpq => hmin'.linkLt_of_family O (fun x _ => hcover x) le_top hpq⟩

/-- `lem:precausalite_restriction_minimale`. "Then the restriction of the causality of `M` to
`U` is absolutely minimal, for every open subset `U` of `M`." -/
theorem LocallyCausallyArcConnected.absolutelyMinimalOn (hloc : C.LocallyCausallyArcConnected)
    (hmin : C.AbsolutelyMinimal) (U : Opens M) : C.AbsolutelyMinimalOn U :=
  CausallyArcConnectedOn.absolutelyMinimalOn
    (CausallyArcConnectedOn.mono (hloc.causallyArcConnected hmin) le_top)

/-! ### `lem:pushup_local` -/

/-- `lem:pushup_local`, the one-step claim followed by concatenation, for the first form of
push-up: `y ≪ z` and `z ≤ x` imply `y ≪ x`. -/
theorem lt_of_lt_of_le_of_cover (h : C.CausallyArcConnected) (hcover : ∀ x : M, ∃ i, x ∈ O i)
    (hO : ∀ i, C.PushUpOn (O i)) (hyz : C.lt V y z) (hzx : C.le V z x) : C.lt V y x := by
  -- one step
  have step : ∀ (w z : M), C.lt V y z → (∃ O' ∈ range O, C.le (V ⊓ O') z w) → C.lt V y w := by
    rintro w z hyz ⟨_, ⟨i, rfl⟩, hzw⟩
    obtain ⟨γ, hγ, rfl, rfl⟩ := (h V le_top y z).2.1 hyz
    have hzN : γ 1 ∈ V ⊓ O i := C.le_mem_left hzw
    obtain ⟨l, u, hl, hu, hrel⟩ := hγ.rel 1 ⟨zero_le_one, le_rfl⟩ (V ⊓ O i) inf_le_left hzN
    -- a parameter `s` with `max l 0 < s < 1`
    have hmax : max l 0 < 1 := max_lt hl zero_lt_one
    obtain ⟨s, hs1, hs2⟩ := exists_between hmax
    have hl_s : l < s := (le_max_left _ _).trans_lt hs1
    have h0_s : 0 < s := (le_max_right _ _).trans_lt hs1
    have hz' : C.lt (V ⊓ O i) (γ s) (γ 1) :=
      hrel s ⟨h0_s.le, hs2.le⟩ 1 ⟨zero_le_one, le_rfl⟩ hl_s hs2 hu
    have hz'w : C.lt (V ⊓ O i) (γ s) w := ((hO i) (V ⊓ O i) inf_le_right).1 hz' hzw
    have hyz' : C.lt V (γ 0) (γ s) := hγ.lt_of_lt le_rfl h0_s hs2.le
    exact C.lt_trans hyz' (C.lt_mono inf_le_left hz'w)
  -- concatenation along a chain from `z` to `x`
  have hchain := ((CausallyArcConnectedOn.absolutelyMinimalOn h) (range O)
    (fun x _ => by obtain ⟨i, hi⟩ := hcover x; exact ⟨O i, mem_range_self i, hi⟩)
    V le_top z x).1 hzx
  clear hzx
  induction hchain with
  | single hl => exact step _ _ hyz hl
  | tail _ hl ih => exact step _ _ ih hl

/-- `lem:pushup_local`. "Let `M` be a causally arc-connected topological spacetime and let
`(U_i)` be a cover of `M` by open subsets each having the push-up property. Then `M` has the
push-up property." -/
theorem CausallyArcConnected.pushUp (h : C.CausallyArcConnected)
    (hcover : ∀ x : M, ∃ i, x ∈ O i) (hO : ∀ i, C.PushUpOn (O i)) : C.PushUp := by
  rw [pushUp_iff]
  intro V x y z
  refine ⟨fun h₁ h₂ => lt_of_lt_of_le_of_cover h hcover hO h₁ h₂, fun h₁ h₂ => ?_⟩
  have h' : C.dual.CausallyArcConnected := dual_causallyArcConnectedOn.2 h
  have hO' : ∀ i, C.dual.PushUpOn (O i) := fun i => dual_pushUpOn.2 (hO i)
  exact lt_of_lt_of_le_of_cover (C := C.dual) h' hcover hO' h₂ h₁

/-! ### `lem:restriction_convexe` -/

/-- `lem:restriction_convexe`, causal relation: in a causally convex open subset of a causally
arc-connected spacetime, the causal relation of `U` is the trace of that of `M`. -/
theorem le_iff_of_causallyConvexIn (h : C.CausallyArcConnected)
    (hU : C.CausallyConvexIn (U : Set M) ⊤) (hx : x ∈ U) (hy : y ∈ U) :
    C.le U y x ↔ C.le ⊤ y x := by
  refine ⟨C.le_mono le_top, fun hyx => ?_⟩
  obtain ⟨c, hc, rfl, rfl⟩ := (h ⊤ le_rfl y x).1.1 hyx
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, c t ∈ U := fun t ht =>
    hU.2 _ hy _ hx (mem_diamond.2
      ⟨hc.le_of_le le_rfl ht.1 ht.2, hc.le_of_le ht.1 ht.2 le_rfl⟩)
  have hcU : C.CausalCurveOn U c 0 1 := CurveOn.restrict hc le_rfl le_rfl le_top hmem
  exact hcU.le_of_le le_rfl zero_le_one le_rfl

/-- `lem:restriction_convexe`, chronological relation. -/
theorem lt_iff_of_causallyConvexIn (h : C.CausallyArcConnected)
    (hU : C.CausallyConvexIn (U : Set M) ⊤) (hx : x ∈ U) (hy : y ∈ U) :
    C.lt U y x ↔ C.lt ⊤ y x := by
  refine ⟨C.lt_mono le_top, fun hyx => ?_⟩
  obtain ⟨c, hc, rfl, rfl⟩ := (h ⊤ le_rfl y x).2.1 hyx
  have hc' := hc.causalCurveOn
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, c t ∈ U := fun t ht =>
    hU.2 _ hy _ hx (mem_diamond.2
      ⟨hc'.le_of_le le_rfl ht.1 ht.2, hc'.le_of_le ht.1 ht.2 le_rfl⟩)
  have hcU : C.ChronalCurveOn U c 0 1 := CurveOn.restrict hc le_rfl le_rfl le_top hmem
  exact hcU.lt_of_lt le_rfl zero_lt_one le_rfl

/-- `lem:restriction_convexe`: `J^-_U(A) = J^-(A) ∩ U` for `A ⊂ U`. -/
theorem Jminus_eq_inter_of_causallyConvexIn (h : C.CausallyArcConnected)
    (hU : C.CausallyConvexIn (U : Set M) ⊤) {A : Set M} (hA : A ⊆ U) :
    C.Jminus U A = C.Jminus ⊤ A ∩ U := by
  ext y
  constructor
  · rintro ⟨a, ha, hya⟩
    exact ⟨⟨a, ha, C.le_mono le_top hya⟩, C.le_mem_left hya⟩
  · rintro ⟨⟨a, ha, hya⟩, hy⟩
    exact ⟨a, ha, (le_iff_of_causallyConvexIn h hU (hA ha) hy).2 hya⟩

/-- `lem:restriction_convexe`: `I^-_U(A) = I^-(A) ∩ U` for `A ⊂ U`. -/
theorem Iminus_eq_inter_of_causallyConvexIn (h : C.CausallyArcConnected)
    (hU : C.CausallyConvexIn (U : Set M) ⊤) {A : Set M} (hA : A ⊆ U) :
    C.Iminus U A = C.Iminus ⊤ A ∩ U := by
  ext y
  constructor
  · rintro ⟨a, ha, hya⟩
    exact ⟨⟨a, ha, C.lt_mono le_top hya⟩, C.lt_mem_left hya⟩
  · rintro ⟨⟨a, ha, hya⟩, hy⟩
    exact ⟨a, ha, (lt_iff_of_causallyConvexIn h hU (hA ha) hy).2 hya⟩

/-- `lem:restriction_convexe`: `K^-_U(x) = K^-(x) ∩ U` for `x ∈ U`. -/
theorem Kminus_singleton_eq_inter_of_causallyConvexIn (h : C.CausallyArcConnected)
    (hU : C.CausallyConvexIn (U : Set M) ⊤) (hx : x ∈ U) :
    C.Kminus U {x} = C.Kminus ⊤ {x} ∩ U := by
  have hJx : C.Jminus U {x} = C.Jminus ⊤ {x} ∩ U :=
    Jminus_eq_inter_of_causallyConvexIn h hU (singleton_subset_iff.2 hx)
  -- within `J^-(x)`, neighbourhoods at a point of `U` do not see the intersection with `U`
  have hnhds : ∀ y ∈ (U : Set M), 𝓝[C.Jminus ⊤ {x} ∩ U] y = 𝓝[C.Jminus ⊤ {x}] y := fun y hy =>
    nhdsWithin_inter_of_mem' (mem_nhdsWithin_of_mem_nhds (U.isOpen.mem_nhds hy))
  ext y
  constructor
  · intro hy
    have hyU : y ∈ U := Precausality.Jminus_subset_carrier (Kminus_subset_Jminus hy)
    refine ⟨?_, hyU⟩
    rw [mem_Kminus_singleton] at hy ⊢
    intro u hu
    obtain ⟨N, hyJ, hN⟩ := hy u hu
    refine ⟨N, Precausality.Jminus_mono_opens le_top hyJ, ?_⟩
    rw [hJx, hnhds y hyU] at hN
    refine mem_of_superset hN ?_
    rintro w ⟨hw, hw'⟩
    refine ⟨hw.1, ?_⟩
    simp only [mem_iInter] at hw' ⊢
    exact fun n hn => Precausality.Jminus_mono_opens le_top (hw' n hn)
  · rintro ⟨hy, hyU⟩
    rw [mem_Kminus_singleton] at hy ⊢
    intro u hu
    obtain ⟨N, hyJ, hN⟩ := hy u hu
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hu.eventually (U.isOpen.mem_nhds hx))
    refine ⟨max N N₀, by rw [hJx]; exact ⟨hyJ, hyU⟩, ?_⟩
    rw [hJx, hnhds y hyU]
    have hUmem : (U : Set M) ∈ 𝓝[C.Jminus ⊤ {x}] y :=
      mem_nhdsWithin_of_mem_nhds (U.isOpen.mem_nhds hyU)
    refine mem_of_superset (inter_mem hN hUmem) ?_
    rintro w ⟨⟨hwJ, hw⟩, hwU⟩
    refine ⟨⟨hwJ, hwU⟩, ?_⟩
    simp only [mem_iInter] at hw ⊢
    intro n hn
    have hn₀ : u n ∈ U := hN₀ n ((le_max_right _ _).trans hn)
    have hwn := hw n ((le_max_left _ _).trans hn)
    rw [Jminus_eq_inter_of_causallyConvexIn h hU (singleton_subset_iff.2 hn₀)]
    exact ⟨hwn, hwU⟩

/-- `lem:restriction_convexe`: `K^-_U(A) = K^-(A) ∩ U` for `A ⊂ U`. -/
theorem Kminus_eq_inter_of_causallyConvexIn (h : C.CausallyArcConnected)
    (hU : C.CausallyConvexIn (U : Set M) ⊤) {A : Set M} (hA : A ⊆ U) :
    C.Kminus U A = C.Kminus ⊤ A ∩ U := by
  rw [Kminus_eq_biUnion, Kminus_eq_biUnion (U := ⊤), iUnion₂_inter]
  refine iUnion₂_congr fun a ha => ?_
  exact Kminus_singleton_eq_inter_of_causallyConvexIn h hU (hA ha)

/-- `lem:restriction_convexe`, in the past: for a causally arc-connected spacetime and an open
subset `U` causally convex in `M`, `J^-_U(A) = J^-(A) ∩ U`, `I^-_U(A) = I^-(A) ∩ U` and
`K^-_U(A) = K^-(A) ∩ U` for every `A ⊂ U`. -/
theorem restriction_convexe_past (h : C.CausallyArcConnected)
    (hU : C.CausallyConvexIn (U : Set M) ⊤) {A : Set M} (hA : A ⊆ U) :
    C.Jminus U A = C.Jminus ⊤ A ∩ U ∧ C.Iminus U A = C.Iminus ⊤ A ∩ U ∧
      C.Kminus U A = C.Kminus ⊤ A ∩ U :=
  ⟨Jminus_eq_inter_of_causallyConvexIn h hU hA, Iminus_eq_inter_of_causallyConvexIn h hU hA,
    Kminus_eq_inter_of_causallyConvexIn h hU hA⟩

/-- `lem:restriction_convexe`, in the future. -/
theorem restriction_convexe_future (h : C.CausallyArcConnected)
    (hU : C.CausallyConvexIn (U : Set M) ⊤) {A : Set M} (hA : A ⊆ U) :
    C.Jplus U A = C.Jplus ⊤ A ∩ U ∧ C.Iplus U A = C.Iplus ⊤ A ∩ U ∧
      C.Kplus U A = C.Kplus ⊤ A ∩ U :=
  restriction_convexe_past (C := C.dual) (dual_causallyArcConnectedOn.2 h)
    (dual_causallyConvexIn.2 hU) hA

end Causality

end Causal
