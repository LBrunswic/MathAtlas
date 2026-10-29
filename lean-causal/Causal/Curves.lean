import Causal.Properties
import Causal.Subdivision

/-!
# Causal and chronal curves

**`def:causal_chronological_curve`** — `ETT.tex:360`.

> A causal chain is an embedding $c:(X,\leq) \rightarrow M$ where $(X,\leq)$ is linearly ordered
> and endowed with the order topology, and where $c$ is a causal morphism.

> Let $I$ be an interval of $\RR$. A causal curve $c:I\rightarrow M$ is a connected causal chain.

## The reading, as ruled

DEC-6 (2026-09-27): "injectivity is not an hypothesis for causal curves."

A **future causal curve of the open set `W`** over `[a, b]` is a map `c` with values in `W` on
`[a, b]` which is locally non-decreasing at every scale: for every `t ∈ [a, b]` and every open
`N ⊂ W` containing `c t`, there is an interval around `t` on which `s < s'` implies
`c s ≤_N c s'`. A **future chronal curve** is the same with `≪_N`. This is the *weak morphism*
of `def:category_topological_spacetimes`, from the segment with the causality of the timelike
line.

| what the paper says | here |
|---|---|
| `c` is a causal morphism | ✓ carried, read as the weak morphism of `def:category_topological_spacetimes` |
| `c` is continuous | ✓ a consequence (`CurveOn.continuousOn`), not an axiom |
| `c` is an embedding | ⚠ weakened, by the author's ruling (DEC-6): injectivity is not asked. A constant map is a causal curve (`causalCurveOn_const`); the proofs of `lem:pushup_local` and `lem:restriction_convexe` use a causal curve from a point to itself |
| `I` an interval | the segment `[a, b]`; the curves of the statements of Section 2 are over `[0, 1]` |

## SCOPE (disclosed)

* "Causal morphism" is read as the weak morphism; DEC-6 rules on injectivity and does not
  address this.
* `def:causal_chain` (the subsets which are causal chains), `def:maximal_chain`,
  `def:causally_connected`, `def:causally_complete` are not carried.
* Curves over a non-compact interval and inextensible curves (`def:cauchy_time_function`,
  `def:cauchy_surface`) are not carried.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology

universe u

variable {M : Type u} [TopologicalSpace M]

/-- What is used of a family of relations `r N`, `N` open: they hold between points of `N`, are
transitive, and are monotone in `N`. Both relations of a precausality are such families. -/
structure IsRelFamily (r : Opens M → M → M → Prop) : Prop where
  mem_left : ∀ {N : Opens M} {x y : M}, r N x y → x ∈ N
  mem_right : ∀ {N : Opens M} {x y : M}, r N x y → y ∈ N
  trans : ∀ {N : Opens M} {x y z : M}, r N x y → r N y z → r N x z
  mono : ∀ {N N' : Opens M}, N' ≤ N → ∀ {x y : M}, r N' x y → r N x y

theorem Precausality.isRelFamily_le (P : Precausality M) : IsRelFamily P.le :=
  ⟨P.le_mem_left, P.le_mem_right, P.le_trans, fun h _ _ h' => P.le_mono h h'⟩

theorem Precausality.isRelFamily_lt (P : Precausality M) : IsRelFamily P.lt :=
  ⟨P.lt_mem_left, P.lt_mem_right, P.lt_trans, fun h _ _ h' => P.lt_mono h h'⟩

/-- A curve of the open set `W` over `[a, b]`, locally increasing for the relations `r N`. -/
structure CurveOn (r : Opens M → M → M → Prop) (W : Opens M) (c : ℝ → M) (a b : ℝ) : Prop where
  mem : ∀ t ∈ Icc a b, c t ∈ W
  rel : ∀ t ∈ Icc a b, ∀ N : Opens M, N ≤ W → c t ∈ N →
    ∃ l u, l < t ∧ t < u ∧ ∀ s ∈ Icc a b, ∀ s' ∈ Icc a b, l < s → s < s' → s' < u →
      r N (c s) (c s')

namespace CurveOn

variable {r : Opens M → M → M → Prop} {W W' : Opens M} {c c' : ℝ → M} {a b d : ℝ}

/-- Along a curve of `W`, the relation of `W` holds between any two points in the order of the
parameters. No hypothesis of arc-connectedness is used. -/
theorem rel_of_lt (hr : IsRelFamily r) (hc : CurveOn r W c a b) {s s' : ℝ} (hs : a ≤ s)
    (hss' : s < s') (hs' : s' ≤ b) : r W (c s) (c s') := by
  have hloc : ∀ τ : Icc s s', ∃ l u, l < τ.1 ∧ τ.1 < u ∧ ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
      l < x → x < y → y < u → r W (c x) (c y) := fun τ =>
    have hτ : τ.1 ∈ Icc a b := ⟨hs.trans τ.2.1, τ.2.2.trans hs'⟩
    hc.rel τ.1 hτ W le_rfl (hc.mem τ.1 hτ)
  choose l u hl hu hrel using hloc
  obtain ⟨t, ht0, hmono, ⟨m, hm⟩, htmem, ht⟩ :=
    exists_subdivision_Icc hss'.le (O := fun τ : Icc s s' => Ioo (l τ) (u τ))
      (fun _ => isOpen_Ioo)
      (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hl ⟨x, hx⟩, hu ⟨x, hx⟩⟩)
  have hchain : ∀ n, t n = s ∨ r W (c s) (c (t n)) := by
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
        have hstep : r W (c (t n)) (c (t (n + 1))) :=
          hrel τ _ h1 _ h2 (hτ (left_mem_Icc.2 h.le)).1 h (hτ (right_mem_Icc.2 h.le)).2
        rcases ih with h0 | h0
        · rw [h0] at hstep; exact Or.inr hstep
        · exact Or.inr (hr.trans h0 hstep)
  have hend := hchain m
  rw [hm m le_rfl] at hend
  rcases hend with h | h
  · exact absurd h hss'.ne'
  · exact h

/-- A curve is continuous: continuity is a consequence of the definition. -/
theorem continuousOn (hr : IsRelFamily r) (hc : CurveOn r W c a b) :
    ContinuousOn c (Icc a b) := by
  intro t ht
  rw [ContinuousWithinAt, tendsto_nhds]
  intro O hO htO
  let N : Opens M := ⟨O, hO⟩ ⊓ W
  have htN : c t ∈ N := ⟨htO, hc.mem t ht⟩
  obtain ⟨l, u, hl, hu, hrel⟩ := hc.rel t ht N inf_le_right htN
  have hmem : Ioo l u ∩ Icc a b ∈ 𝓝[Icc a b] t :=
    Filter.inter_mem (mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds hl hu)) self_mem_nhdsWithin
  refine Filter.mem_of_superset hmem ?_
  rintro s ⟨⟨hls, hsu⟩, hs⟩
  show c s ∈ O
  rcases lt_trichotomy s t with h | h | h
  · exact (hr.mem_left (hrel s hs t ht hls h hu)).1
  · rw [h]; exact htO
  · exact (hr.mem_right (hrel t ht s hs hl h hsu)).1

/-- A curve of `W` is a curve of every larger open set. -/
theorem mono_opens (hr : IsRelFamily r) (hc : CurveOn r W c a b) (hW : W ≤ W') :
    CurveOn r W' c a b where
  mem t ht := hW (hc.mem t ht)
  rel t ht N _ htN := by
    obtain ⟨l, u, hl, hu, hrel⟩ := hc.rel t ht (N ⊓ W) inf_le_right ⟨htN, hc.mem t ht⟩
    exact ⟨l, u, hl, hu, fun s hs s' hs' h1 h2 h3 =>
      hr.mono inf_le_left (hrel s hs s' hs' h1 h2 h3)⟩

/-- The restriction of a curve to a sub-segment is a curve of every open subset of `W`
containing its image. -/
theorem restrict (hc : CurveOn r W c a b) {a' b' : ℝ} (ha : a ≤ a') (hb : b' ≤ b)
    (hW : W' ≤ W) (hmem : ∀ t ∈ Icc a' b', c t ∈ W') : CurveOn r W' c a' b' where
  mem := hmem
  rel t ht N hN htN := by
    have ht' : t ∈ Icc a b := ⟨ha.trans ht.1, ht.2.trans hb⟩
    obtain ⟨l, u, hl, hu, hrel⟩ := hc.rel t ht' N (hN.trans hW) htN
    exact ⟨l, u, hl, hu, fun s hs s' hs' h1 h2 h3 =>
      hrel s ⟨ha.trans hs.1, hs.2.trans hb⟩ s' ⟨ha.trans hs'.1, hs'.2.trans hb⟩ h1 h2 h3⟩

/-- Concatenation of two curves. -/
theorem concat (hr : IsRelFamily r) (hc : CurveOn r W c a b) (hc' : CurveOn r W c' b d)
    (hab : a ≤ b) (hbd : b ≤ d) (hcc' : c b = c' b) :
    CurveOn r W (fun t => if t ≤ b then c t else c' t) a d where
  mem t ht := by
    by_cases h : t ≤ b
    · simp only [h, if_true]
      exact hc.mem t ⟨ht.1, h⟩
    · simp only [h, if_false]
      exact hc'.mem t ⟨(not_le.1 h).le, ht.2⟩
  rel t ht N hN htN := by
    rcases lt_trichotomy t b with h | h | h
    · -- before the junction
      have htN' : c t ∈ N := by simpa [h.le] using htN
      obtain ⟨l, u, hl, hu, hrel⟩ := hc.rel t ⟨ht.1, h.le⟩ N hN htN'
      refine ⟨l, min u b, hl, lt_min hu h, fun s hs s' hs' h1 h2 h3 => ?_⟩
      have hs'b : s' < b := h3.trans_le (min_le_right _ _)
      have hsb : s < b := h2.trans hs'b
      simp only [hsb.le, hs'b.le, if_true]
      exact hrel s ⟨hs.1, hsb.le⟩ s' ⟨hs'.1, hs'b.le⟩ h1 h2 (h3.trans_le (min_le_left _ _))
    · -- at the junction
      subst h
      have htN₁ : c t ∈ N := by simpa using htN
      have htN₂ : c' t ∈ N := hcc' ▸ htN₁
      obtain ⟨l₁, u₁, hl₁, hu₁, hrel₁⟩ := hc.rel t ⟨hab, le_rfl⟩ N hN htN₁
      obtain ⟨l₂, u₂, hl₂, hu₂, hrel₂⟩ := hc'.rel t ⟨le_rfl, hbd⟩ N hN htN₂
      refine ⟨l₁, u₂, hl₁, hu₂, fun s hs s' hs' h1 h2 h3 => ?_⟩
      by_cases hs't : s' ≤ t
      · have hst : s ≤ t := h2.le.trans hs't
        simp only [hst, hs't, if_true]
        exact hrel₁ s ⟨hs.1, hst⟩ s' ⟨hs'.1, hs't⟩ h1 h2 (hs't.trans_lt hu₁)
      · have hts' : t < s' := not_le.1 hs't
        by_cases hst : s ≤ t
        · simp only [hst, hs't, if_true, if_false]
          have h2' : r N (c' t) (c' s') :=
            hrel₂ t ⟨le_rfl, hbd⟩ s' ⟨hts'.le, hs'.2⟩ hl₂ hts' h3
          rcases hst.eq_or_lt with h | h
          · rw [h, hcc']; exact h2'
          · have h1' : r N (c s) (c t) :=
              hrel₁ s ⟨hs.1, hst⟩ t ⟨hab, le_rfl⟩ h1 h hu₁
            rw [hcc'] at h1'
            exact hr.trans h1' h2'
        · have hts : t < s := not_le.1 hst
          simp only [hst, hs't, if_false]
          exact hrel₂ s ⟨hts.le, hs.2⟩ s' ⟨hts'.le, hs'.2⟩ (hl₂.trans hts) h2 h3
    · -- after the junction
      have htb : ¬ t ≤ b := not_le.2 h
      have htN' : c' t ∈ N := by simpa [htb] using htN
      obtain ⟨l, u, hl, hu, hrel⟩ := hc'.rel t ⟨h.le, ht.2⟩ N hN htN'
      refine ⟨max l b, u, max_lt hl h, hu, fun s hs s' hs' h1 h2 h3 => ?_⟩
      have hbs : b < s := (le_max_right _ _).trans_lt h1
      have hbs' : b < s' := hbs.trans h2
      simp only [not_le.2 hbs, not_le.2 hbs', if_false]
      exact hrel s ⟨hbs.le, hs.2⟩ s' ⟨hbs'.le, hs'.2⟩ ((le_max_left _ _).trans_lt h1) h2 h3

/-- Reparametrisation by an increasing affine map. -/
theorem comp_affine {k m a' b' : ℝ} (hk : 0 < k) (hc : CurveOn r W c (k * a' + m) (k * b' + m)) :
    CurveOn r W (fun t => c (k * t + m)) a' b' where
  mem t ht := hc.mem _ ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
  rel t ht N hN htN := by
    have ht' : k * t + m ∈ Icc (k * a' + m) (k * b' + m) :=
      ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
    obtain ⟨l, u, hl, hu, hrel⟩ := hc.rel _ ht' N hN htN
    refine ⟨(l - m) / k, (u - m) / k, ?_, ?_, fun s hs s' hs' h1 h2 h3 => ?_⟩
    · rw [div_lt_iff₀ hk]; linarith
    · rw [lt_div_iff₀ hk]; linarith
    · refine hrel _ ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩ _
        ⟨by nlinarith [hs'.1], by nlinarith [hs'.2]⟩ ?_ (by nlinarith) ?_
      · rw [div_lt_iff₀ hk] at h1; linarith
      · rw [lt_div_iff₀ hk] at h3; linarith

end CurveOn

namespace Causality

variable (C : Causality M)

/-- A future causal curve of the open set `W` over `[a, b]`. -/
def CausalCurveOn (W : Opens M) (c : ℝ → M) (a b : ℝ) : Prop := CurveOn C.le W c a b

/-- A future chronal curve of the open set `W` over `[a, b]`. -/
def ChronalCurveOn (W : Opens M) (c : ℝ → M) (a b : ℝ) : Prop := CurveOn C.lt W c a b

variable {C} {W : Opens M} {c : ℝ → M} {a b : ℝ} {p : M}

/-- A constant map is a future causal curve. -/
theorem causalCurveOn_const (hp : p ∈ W) : C.CausalCurveOn W (fun _ => p) a b where
  mem _ _ := hp
  rel t _ N _ htN := ⟨t - 1, t + 1, by linarith, by linarith, fun _ _ _ _ _ _ _ => C.le_refl htN⟩

/-- A future chronal curve is a future causal curve. -/
theorem ChronalCurveOn.causalCurveOn (hc : C.ChronalCurveOn W c a b) :
    C.CausalCurveOn W c a b where
  mem := hc.mem
  rel t ht N hN htN := by
    obtain ⟨l, u, hl, hu, hrel⟩ := hc.rel t ht N hN htN
    exact ⟨l, u, hl, hu, fun s hs s' hs' h1 h2 h3 => C.le_of_lt (hrel s hs s' hs' h1 h2 h3)⟩

/-- Along a future causal curve of `W` the causal relation of `W` holds in the order of the
parameters. -/
theorem CausalCurveOn.le_of_le (hc : C.CausalCurveOn W c a b) {s s' : ℝ} (hs : a ≤ s)
    (hss' : s ≤ s') (hs' : s' ≤ b) : C.le W (c s) (c s') := by
  rcases hss'.eq_or_lt with h | h
  · subst h
    exact C.le_refl (hc.mem s ⟨hs, hs'⟩)
  · exact CurveOn.rel_of_lt C.isRelFamily_le hc hs h hs'

/-- Along a future chronal curve of `W` the chronological relation of `W` holds in the strict
order of the parameters. -/
theorem ChronalCurveOn.lt_of_lt (hc : C.ChronalCurveOn W c a b) {s s' : ℝ} (hs : a ≤ s)
    (hss' : s < s') (hs' : s' ≤ b) : C.lt W (c s) (c s') :=
  CurveOn.rel_of_lt C.isRelFamily_lt hc hs hss' hs'

end Causality

end Causal
