import Causal.NestedCausalities
import Causal.LinesReachable
import Mathlib.NumberTheory.Real.Irrational

/-!
# Curve nesting gives ≤-nesting when the narrower causality is causally arc-connected, and not without; curve nesting is transitive

Programme target `T-abs-nested-converse` (`programme/roadmap.toml`; layer 1, no label of
`ETT.tex`). Imports: `Causal.NestedCausalities`, `Causal.LinesReachable` (ETT layer, no model) and
`Mathlib.NumberTheory.Real.Irrational` (an irrational between two reals). Sources: the ladder's
`[[open]]` entry `curve_nested → le_nested` (`programme/ladder.toml:1206`) and
Eperon–Reall–Sbierski 1802.03020 Remark 4.74
(`papers/ers-predictability/legacy/labeled/ghd_02_19.tex:993`).

* **`T-abs-nested-converse/1-converse`** — `Causality.CurveNestedOn.leNested_of_causallyArcConnected`
  (`CurveNestedOn C C' ⊤` and `C` causally arc-connected give `LeNested C C'`), its open-set form
  `Causality.CurveNestedOn.le_of_causallyArcConnectedOn`, the equivalences
  `Causality.leNested_iff_curveNestedOn_top`, `Causality.curveNestedOn_iff_of_causallyArcConnectedOn`.
  Nothing is asked of the wider `C'`.
* **`T-abs-nested-converse/2-bare`** — `not_leNested_of_curveNested_bare`: the pointed line is
  curve-nested in the spacelike line and `0 ≤ 1` holds in the first only. A causal curve of the
  pointed line is constant (`pointedLine_causalCurveOn_eq`), so it is curve-nested in every
  causality of `ℝ` (`pointedLine_curveNestedOn`); witness `pointedLine_separates_curveNested`. The
  hypothesis cannot be moved to the wider causality: the spacelike line is causally arc-connected
  (`spacelikeLine_causallyArcConnected`), whence `not_leNested_of_curveNested_wider_bare`.
* **`T-abs-nested-converse/3-trans`** — `Causality.CurveNestedOn.trans`, with `.refl`, the mixed
  forms `Causality.LeNested.trans_curveNestedOn`, `Causality.CurveNestedOn.trans_leNested`, and
  time reversal `Causality.CurveNestedOn.dual`, `Causality.dual_curveNestedOn_iff`.
* **`T-abs-nested-converse/4-absolutely-minimal`** — the hypothesis cannot be weakened to absolute
  minimality of `C` (`not_leNested_of_curveNested_absolutelyMinimal_bare`): the rational line
  `rationalLine` is absolutely minimal (`rationalLine_absolutelyMinimal`) and its causal curves are
  constant (`rationalLine_causalCurveOn_eq`); witness `rationalLine_separates_curveNested`. It is
  moreover causal, with push-up, and not causally open in the future
  (`rationalLine_not_causallyOpenFuture`): causality-sort witness
  `rationalLine_separates_absolutelyMinimal`.

> Pair sort, at M (so on every open). False in general, argued, not in Lean: the pointed line
> (Causal.pointedLine, 0 ≤ y for y > 0) and the spacelike line (Causal.spacelikeLine, ≤ the
> diagonal) have only constant causal curves, so the first is curve-nested in the second, while
> 0 ≤ 1 holds in the first only. True when C is causally arc-connected (x ≤_U y of C lies on a
> C-causal curve of U, which is C'-causal by curve nesting on U, so x ≤_U y for C'), not in Lean
> either. (`programme/ladder.toml:1209`)

> Let us remark that better bounds on the light cones of $g^{\mu \nu}(u, du)$ translate into an
> improvement of the uniqueness results. Above, we have only made use of the trivial Minkowski
> bound on the light cones for subluminal equations. (ERS Remark 4.74, `ghd_02_19.tex:993`)

## Hypothesis checklist

| source hypothesis | here |
|---|---|
| 1-converse: `C` causally arc-connected | ✓ carried (`CausallyArcConnected`, a ladder node); only its `≤` half (a `C`-causal curve of `U` through each `x ≤_U y`) is used; it cannot be weakened to absolute minimality (`rationalLine`) |
| 1-converse: curve nesting at `M` | ✓ carried; the open-set form asks it on `W` only, with `C` arc-connected on `W` |
| 1-converse: `C'` causally arc-connected (the target's fallback) | not needed: a `C'`-causal curve of `U` from `x` to `y` gives `x ≤_U y` for `C'` in every causality (`CausalCurveOn.le_of_le`); nor sufficient in place of the hypothesis on `C` (`spacelikeLine`) |
| 2-bare: the pointed line, the spacelike line | ✓ `Causal.pointedLine`, `Causal.spacelikeLine` of the library |
| 3-trans: a chain `C_g ≤ C_b ≤ C_m` of cone bounds | ✓ curve nesting on one open `W` at each step |
| 4-absolutely-minimal: (beyond the target, no source hypothesis) | a new line, `rationalLine`, defined here |

## SCOPE (disclosed)

* The converse is exact: under causal arc-connectedness of `C` on `W`, curve nesting on `W` is
  ≤-nesting on the opens of `W` (`curveNestedOn_iff_of_causallyArcConnectedOn`).
* The `≪` relation is not treated: curve nesting carries causal curves to causal curves, never to
  chronal ones, so no `LtNested` form is claimed.
* The pointed line and the rational line are causal, have push-up (vacuously) and are not
  causally arc-connected (`pointedLine_not_causallyArcConnected`,
  `rationalLine_not_causallyArcConnected`), as the converse forces; the rational line is moreover
  absolutely minimal (`rationalLine_absolutelyMinimal`: equal rational steps below a Lebesgue
  number of the cover, the metric of `ℝ` used inside that proof only). Its causal curves are
  constant because a non-constant one takes an irrational value (`rationalLine_causalCurveOn_eq`),
  and `J⁺((0, 1))` contains `1` but no irrational number above it
  (`rationalLine_not_causallyOpenFuture`).
* `rationalLine` is a new causality of `ℝ`, defined here: `x ≤_U y` iff `x = y ∈ U` or `x < y`
  both rational with `[x, y] ⊆ U`; `≪` empty.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology

universe u

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable {C C' C'' : Causality M} {U W : Opens M} {x y : M} {c : ℝ → M} {a b : ℝ}

/-! ## 0. A curve constant on its segment -/

/-- A curve constant on its segment is a future causal curve of every causality. -/
theorem causalCurveOn_of_forall_eq (hmem : ∀ t ∈ Icc a b, c t ∈ W)
    (hc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, c s = c t) : C.CausalCurveOn W c a b where
  mem := hmem
  rel t ht N _ htN := ⟨t - 1, t + 1, by linarith, by linarith, fun s hs s' hs' _ _ _ => by
    rw [hc s hs t ht, hc s' hs' t ht]; exact C.le_refl htN⟩

/-! ## 1. Transitivity and time reversal of curve nesting -/

theorem CurveNestedOn.refl (C : Causality M) (W : Opens M) : CurveNestedOn C C W :=
  fun _ _ _ hc => hc

/-- **Curve nesting is transitive** (ERS Remark 4.74: a better a-priori cone bound
`C_g ≤ C_b ≤ C_m`). -/
theorem CurveNestedOn.trans (h : CurveNestedOn C C' W) (h' : CurveNestedOn C' C'' W) :
    CurveNestedOn C C'' W :=
  fun _ _ _ hc => h' (h hc)

theorem LeNested.trans_curveNestedOn (h : LeNested C C') (h' : CurveNestedOn C' C'' W) :
    CurveNestedOn C C'' W :=
  (h.curveNestedOn W).trans h'

theorem CurveNestedOn.trans_leNested (h : CurveNestedOn C C' W) (h' : LeNested C' C'') :
    CurveNestedOn C C'' W :=
  h.trans (h'.curveNestedOn W)

theorem CurveNestedOn.dual (h : CurveNestedOn C C' W) : CurveNestedOn C.dual C'.dual W := by
  intro c a b hc
  have h1 : C.CausalCurveOn W (fun t => c (a + b - t)) a b := CurveOn.reverse hc
  have h2 : CurveOn (fun N x y => C'.le N y x) W (fun t => c (a + b - (a + b - t))) a b :=
    CurveOn.reverse (h h1)
  have he : (fun t => c (a + b - (a + b - t))) = c := funext fun t => by rw [sub_sub_cancel]
  rw [he] at h2
  exact h2

theorem dual_curveNestedOn_iff : CurveNestedOn C.dual C'.dual W ↔ CurveNestedOn C C' W :=
  ⟨fun h => h.dual, fun h => h.dual⟩

/-! ## 2. The converse under causal arc-connectedness -/

/-- **Curve nesting gives ≤-nesting, on an open `W`**, when the narrower causality is causally
arc-connected on `W`: `x ≤_U y` for `C` lies on a `C`-causal curve of `U`, which is `C'`-causal. -/
theorem CurveNestedOn.le_of_causallyArcConnectedOn (h : CurveNestedOn C C' W)
    (hC : C.CausallyArcConnectedOn W) (hU : U ≤ W) (hxy : C.le U x y) : C'.le U x y := by
  obtain ⟨c, hc, rfl, rfl⟩ := (hC U hU x y).1.1 hxy
  exact CausalCurveOn.le_of_le (h.mono hU hc) le_rfl zero_le_one le_rfl

/-- **Curve nesting at `M` gives ≤-nesting when `C` is causally arc-connected.** -/
theorem CurveNestedOn.leNested_of_causallyArcConnected (h : CurveNestedOn C C' ⊤)
    (hC : C.CausallyArcConnected) : LeNested C C' :=
  fun _ _ _ hxy => h.le_of_causallyArcConnectedOn hC le_top hxy

/-- For a causally arc-connected `C`, ≤-nesting and curve nesting at `M` are the same. -/
theorem leNested_iff_curveNestedOn_top (hC : C.CausallyArcConnected) :
    LeNested C C' ↔ CurveNestedOn C C' ⊤ :=
  ⟨fun h => h.curveNestedOn ⊤, fun h => h.leNested_of_causallyArcConnected hC⟩

/-- The open-set form: for `C` causally arc-connected on `W`, curve nesting on `W` is ≤-nesting on
the opens of `W`. -/
theorem curveNestedOn_iff_of_causallyArcConnectedOn (hC : C.CausallyArcConnectedOn W) :
    CurveNestedOn C C' W ↔ ∀ U : Opens M, U ≤ W → ∀ x y, C.le U x y → C'.le U x y :=
  ⟨fun h _ hU _ _ hxy => h.le_of_causallyArcConnectedOn hC hU hxy,
    fun h _ _ _ hc => curveOn_of_rel_imp (fun N hN x y hxy => h N hN x y hxy) hc⟩

end Causality

/-! ## 3. The bare converse fails: the pointed line in the spacelike line -/

theorem pointedLine_le {U : Opens ℝ} {x y : ℝ} :
    pointedLine.le U x y ↔ (x = y ∧ x ∈ U) ∨ (x = 0 ∧ 0 < y ∧ Icc 0 y ⊆ (U : Set ℝ)) :=
  Iff.rfl

/-- **A causal curve of the pointed line is constant** on its segment. -/
theorem pointedLine_causalCurveOn_eq {W : Opens ℝ} {c : ℝ → ℝ} {a b : ℝ}
    (hc : pointedLine.CausalCurveOn W c a b) {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    c s = c t := by
  wlog hst : s ≤ t generalizing s t
  · exact (this ht hs (le_of_not_ge hst)).symm
  have hcont : ContinuousOn c (Icc s t) :=
    (CurveOn.continuousOn pointedLine.isRelFamily_le hc).mono (Icc_subset_Icc hs.1 ht.2)
  rcases pointedLine_le.1 (hc.le_of_le hs.1 hst ht.2) with ⟨heq, -⟩ | ⟨h0, hpos, -⟩
  · exact heq
  · -- `c s = 0 < c t`: the curve takes the value `c t / 2` on `[s, t]`, which is neither
    -- `0` nor `c t`
    obtain ⟨r, hr, hcr⟩ := intermediate_value_Icc hst hcont
      (show c t / 2 ∈ Icc (c s) (c t) from ⟨by rw [h0]; linarith, by linarith⟩)
    rcases pointedLine_le.1 (hc.le_of_le (hs.1.trans hr.1) hr.2 ht.2) with ⟨h, -⟩ | ⟨h, -, -⟩
    · rw [hcr] at h; linarith
    · rw [hcr] at h; linarith

/-- The pointed line is curve-nested in every causality of `ℝ`, on every open set. -/
theorem pointedLine_curveNestedOn (C' : Causality ℝ) (W : Opens ℝ) :
    Causality.CurveNestedOn pointedLine C' W :=
  fun _ _ _ hc => Causality.causalCurveOn_of_forall_eq hc.mem fun _ hs _ ht =>
    pointedLine_causalCurveOn_eq hc hs ht

theorem pointedLine_le_zero_one : pointedLine.le ⊤ 0 1 :=
  Or.inr ⟨rfl, one_pos, fun _ _ => trivial⟩

theorem pointedLine_not_leNested_spacelikeLine : ¬ pointedLine.LeNested spacelikeLine := fun h =>
  zero_ne_one (h pointedLine_le_zero_one).1

theorem pointedLine_not_causallyArcConnected : ¬ pointedLine.CausallyArcConnected := fun h =>
  pointedLine_not_leNested_spacelikeLine
    ((pointedLine_curveNestedOn spacelikeLine ⊤).leNested_of_causallyArcConnected h)

theorem pointedLine_isCausal : pointedLine.IsCausal := by
  intro x y hxy hyx
  rcases pointedLine_le.1 hxy with ⟨h, -⟩ | ⟨rfl, hy, -⟩
  · exact h
  · rcases pointedLine_le.1 hyx with ⟨h, -⟩ | ⟨rfl, -, -⟩
    · exact h.symm
    · exact absurd hy (lt_irrefl 0)

/-- The pointed line has the push-up property, vacuously. -/
theorem pointedLine_pushUp : pointedLine.PushUp := by
  rw [Causality.pushUp_iff]
  intro U x y z
  exact ⟨fun h _ => h.elim, fun _ h => h.elim⟩

/-- **The spacelike line is causally arc-connected**: `≤` is the diagonal, realised by constant
curves, and `≪` is empty, as are its chronal curves. -/
theorem spacelikeLine_causallyArcConnected : spacelikeLine.CausallyArcConnected := by
  rw [Causality.CausallyArcConnected, Causality.causallyArcConnectedOn_iff]
  intro U _ p q
  refine ⟨fun h => ?_, fun h => False.elim h⟩
  obtain ⟨rfl, hp⟩ := h
  exact ⟨fun _ => p, Causality.causalCurveOn_const hp, rfl, rfl⟩

/-- **The bare converse is false**: curve nesting at `M` does not give ≤-nesting. -/
theorem not_leNested_of_curveNested_bare :
    ¬ ∀ C C' : Causality ℝ, Causality.CurveNestedOn C C' ⊤ → C.LeNested C' := fun h =>
  pointedLine_not_leNested_spacelikeLine (h _ _ (pointedLine_curveNestedOn spacelikeLine ⊤))

/-- **Nor with the wider causality causally arc-connected**: the hypothesis is on the narrower. -/
theorem not_leNested_of_curveNested_wider_bare :
    ¬ ∀ C C' : Causality ℝ, C'.CausallyArcConnected → Causality.CurveNestedOn C C' ⊤ →
      C.LeNested C' := fun h =>
  pointedLine_not_leNested_spacelikeLine
    (h _ _ spacelikeLine_causallyArcConnected (pointedLine_curveNestedOn spacelikeLine ⊤))

/-- The conjoined witness: the pointed line is curve-nested in the spacelike line on every open,
not ≤-nested in it, not causally arc-connected, causal and with push-up; the spacelike line is
causally arc-connected. -/
theorem pointedLine_separates_curveNested :
    (∀ W : Opens ℝ, Causality.CurveNestedOn pointedLine spacelikeLine W) ∧
      ¬ pointedLine.LeNested spacelikeLine ∧ ¬ pointedLine.CausallyArcConnected ∧
      pointedLine.IsCausal ∧ pointedLine.PushUp ∧ spacelikeLine.CausallyArcConnected :=
  ⟨pointedLine_curveNestedOn spacelikeLine, pointedLine_not_leNested_spacelikeLine,
    pointedLine_not_causallyArcConnected, pointedLine_isCausal, pointedLine_pushUp,
    spacelikeLine_causallyArcConnected⟩

/-! ## 4. Absolute minimality of the narrower causality does not suffice: the rational line -/

/-- **The rational line**: `x ≤_U y` iff `x = y ∈ U`, or `x < y` are both rational and
`[x, y] ⊆ U`; no chronology. Absolutely minimal (a rational segment is cut into rational
segments as short as wished), yet its causal curves are constant. -/
def rationalLine : Causality ℝ where
  le U x y := (x = y ∧ x ∈ U) ∨
    (x < y ∧ x ∈ range ((↑) : ℚ → ℝ) ∧ y ∈ range ((↑) : ℚ → ℝ) ∧ Icc x y ⊆ (U : Set ℝ))
  lt _ _ _ := False
  le_mem_left h := h.elim (fun h => h.2) fun h => h.2.2.2 (left_mem_Icc.2 h.1.le)
  le_mem_right h := h.elim (fun h => h.1 ▸ h.2) fun h => h.2.2.2 (right_mem_Icc.2 h.1.le)
  lt_mem_left h := h.elim
  lt_mem_right h := h.elim
  le_refl hx := Or.inl ⟨rfl, hx⟩
  le_trans h₁ h₂ := by
    rcases h₁ with ⟨rfl, -⟩ | ⟨h1, hx, hy, h3⟩
    · exact h₂
    rcases h₂ with ⟨rfl, -⟩ | ⟨h1', -, hz, h3'⟩
    · exact Or.inr ⟨h1, hx, hy, h3⟩
    · exact Or.inr ⟨h1.trans h1', hx, hz, Icc_subset_Icc_union_Icc.trans (union_subset h3 h3')⟩
  lt_trans h _ := h
  le_mono h _ _ h' := h'.elim (fun h' => Or.inl ⟨h'.1, h h'.2⟩)
    fun h' => Or.inr ⟨h'.1, h'.2.1, h'.2.2.1, fun _ hz => h (h'.2.2.2 hz)⟩
  lt_mono _ _ _ h' := h'
  le_of_lt h := h.elim
  isOpen_lt_right _ _ := by simp
  isOpen_lt_left _ _ := by simp

theorem rationalLine_le {U : Opens ℝ} {x y : ℝ} :
    rationalLine.le U x y ↔ (x = y ∧ x ∈ U) ∨
      (x < y ∧ x ∈ range ((↑) : ℚ → ℝ) ∧ y ∈ range ((↑) : ℚ → ℝ) ∧ Icc x y ⊆ (U : Set ℝ)) :=
  Iff.rfl

/-- **A causal curve of the rational line is constant** on its segment. -/
theorem rationalLine_causalCurveOn_eq {W : Opens ℝ} {c : ℝ → ℝ} {a b : ℝ}
    (hc : rationalLine.CausalCurveOn W c a b) {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    c s = c t := by
  wlog hst : s ≤ t generalizing s t
  · exact (this ht hs (le_of_not_ge hst)).symm
  have hcont : ContinuousOn c (Icc s t) :=
    (CurveOn.continuousOn rationalLine.isRelFamily_le hc).mono (Icc_subset_Icc hs.1 ht.2)
  rcases rationalLine_le.1 (hc.le_of_le hs.1 hst ht.2) with ⟨heq, -⟩ | ⟨hlt, hrat, -, -⟩
  · exact heq
  · -- an irrational value `v` between `c s < c t` is taken at some `r`, and `c s ≤ c r = v`
    -- holds neither by equality nor between rationals
    obtain ⟨v, hvirr, hv1, hv2⟩ := exists_irrational_btwn hlt
    obtain ⟨r, hr, hcr⟩ := intermediate_value_Icc hst hcont ⟨hv1.le, hv2.le⟩
    rcases rationalLine_le.1 (hc.le_of_le hs.1 hr.1 (hr.2.trans ht.2)) with ⟨h, -⟩ | ⟨-, -, h, -⟩
    · rw [hcr] at h; linarith
    · exact absurd (hcr ▸ h) hvirr

/-- The rational line is curve-nested in every causality of `ℝ`, on every open set. -/
theorem rationalLine_curveNestedOn (C' : Causality ℝ) (W : Opens ℝ) :
    Causality.CurveNestedOn rationalLine C' W :=
  fun _ _ _ hc => Causality.causalCurveOn_of_forall_eq hc.mem fun _ hs _ ht =>
    rationalLine_causalCurveOn_eq hc hs ht

/-- **The rational line is absolutely minimal.** -/
theorem rationalLine_absolutelyMinimal : rationalLine.AbsolutelyMinimal := by
  refine Precausality.absolutelyMinimal_iff.2 fun S hS V _ x y =>
    ⟨fun hxy => ?_, fun hxy => False.elim hxy⟩
  rcases rationalLine_le.1 hxy with ⟨rfl, hx⟩ | ⟨hlt, ⟨q, rfl⟩, ⟨q', rfl⟩, hsub⟩
  · obtain ⟨O, hO, hxO⟩ := hS x trivial
    exact Relation.TransGen.single ⟨O, hO, rationalLine.le_refl ⟨hx, hxO⟩⟩
  -- a Lebesgue number `δ` of the cover `V ⊓ O` of `[q, q']`, and `n` equal rational steps `< δ`
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric (isCompact_Icc (a := (q : ℝ)) (b := q'))
    (c := fun O : S => ((V ⊓ (O : Opens ℝ) : Opens ℝ) : Set ℝ)) (fun _ => Opens.isOpen _)
    (fun z hz => by
      obtain ⟨O, hO, hzO⟩ := hS z trivial
      exact mem_iUnion.2 ⟨⟨O, hO⟩, hsub hz, hzO⟩)
  have hd0 : (0 : ℝ) < (q' : ℝ) - q := sub_pos.2 hlt
  obtain ⟨n, hn⟩ := exists_nat_gt (((q' : ℝ) - q) / δ)
  have hn0 : (0 : ℝ) < n := (div_pos hd0 hδ).trans hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := Nat.exists_eq_succ_of_ne_zero (by exact_mod_cast hn0.ne')
  set d : ℝ := ((q' : ℝ) - q) / ((m + 1 : ℕ) : ℝ) with hd
  have hdpos : 0 < d := div_pos hd0 hn0
  have hdδ : d < δ := by
    rw [hd, div_lt_iff₀ hn0]; rw [div_lt_iff₀ hδ] at hn; linarith
  have hnd : ((m + 1 : ℕ) : ℝ) * d = (q' : ℝ) - q := by rw [hd]; field_simp
  let p : ℕ → ℝ := fun k => (q : ℝ) + k * d
  have hprat : ∀ k : ℕ, p k ∈ range ((↑) : ℚ → ℝ) := fun k =>
    ⟨q + k * ((q' - q) / ((m + 1 : ℕ) : ℚ)), by simp only [p, hd]; push_cast; ring⟩
  have hstep : ∀ k : ℕ, k < m + 1 → ∃ O ∈ S, rationalLine.le (V ⊓ O) (p k) (p (k + 1)) := by
    intro k hk
    have hkn : (k : ℝ) + 1 ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast hk
    have hk0 : (0 : ℝ) ≤ k := k.cast_nonneg
    have hpk : p k ∈ Icc (q : ℝ) q' := ⟨by simp only [p]; nlinarith, by simp only [p]; nlinarith⟩
    obtain ⟨⟨O, hO⟩, hOb⟩ := hball (p k) hpk
    refine ⟨O, hO, Or.inr ⟨by simp only [p]; push_cast; linarith, hprat k, hprat (k + 1),
      fun z hz => hOb ?_⟩⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    simp only [p] at hz; push_cast at hz
    constructor <;> linarith [hz.1, hz.2]
  have hchain : ∀ k : ℕ, k < m + 1 →
      Relation.TransGen (fun a b => ∃ O ∈ S, rationalLine.le (V ⊓ O) a b) (p 0) (p (k + 1)) := by
    intro k
    induction k with
    | zero => intro h0; exact Relation.TransGen.single (hstep 0 h0)
    | succ k ih => intro hk; exact (ih (Nat.lt_of_succ_lt hk)).tail (hstep (k + 1) hk)
  have h0 : p 0 = q := by simp [p]
  have hN : p (m + 1) = q' := by simp only [p]; rw [hnd]; ring
  rw [← h0, ← hN]
  exact hchain m (Nat.lt_succ_self m)

theorem rationalLine_not_leNested_spacelikeLine : ¬ rationalLine.LeNested spacelikeLine := fun h =>
  zero_ne_one (h (show rationalLine.le ⊤ 0 1 from
    Or.inr ⟨one_pos, ⟨0, Rat.cast_zero⟩, ⟨1, Rat.cast_one⟩, fun _ _ => trivial⟩)).1

theorem rationalLine_not_causallyArcConnected : ¬ rationalLine.CausallyArcConnected := fun h =>
  rationalLine_not_leNested_spacelikeLine
    ((rationalLine_curveNestedOn spacelikeLine ⊤).leNested_of_causallyArcConnected h)

theorem rationalLine_isCausal : rationalLine.IsCausal := by
  intro x y hxy hyx
  rcases rationalLine_le.1 hxy with ⟨h, -⟩ | ⟨h, -⟩
  · exact h
  · rcases rationalLine_le.1 hyx with ⟨h', -⟩ | ⟨h', -⟩
    · exact h'.symm
    · exact absurd (h.trans h') (lt_irrefl x)

/-- The rational line has the push-up property, vacuously. -/
theorem rationalLine_pushUp : rationalLine.PushUp := by
  rw [Causality.pushUp_iff]
  intro U x y z
  exact ⟨fun h _ => h.elim, fun _ h => h.elim⟩

/-- **The rational line is not causally open in the future**: `J⁺((0, 1))` contains `1` (from
`1/2`) and no irrational number above `1`. -/
theorem rationalLine_not_causallyOpenFuture : ¬ rationalLine.CausallyOpenFuture := by
  intro h
  let V : Opens ℝ := ⟨Ioo 0 1, isOpen_Ioo⟩
  have h1 : (1 : ℝ) ∈ rationalLine.Jplus ⊤ V := by
    rw [Precausality.mem_Jplus]
    refine ⟨1 / 2, show (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 by norm_num, Or.inr ⟨by norm_num,
      ⟨1 / 2, by push_cast; ring⟩, ⟨1, Rat.cast_one⟩, fun _ _ => trivial⟩⟩
  obtain ⟨l, u, ⟨hl, hu⟩, hlu⟩ :=
    mem_nhds_iff_exists_Ioo_subset.1 ((h ⊤ V le_top).mem_nhds h1)
  obtain ⟨v, hvirr, hv1, hv2⟩ := exists_irrational_btwn hu
  obtain ⟨x, hx, hxv⟩ := Precausality.mem_Jplus.1 (hlu ⟨hl.trans hv1, hv2⟩)
  have hx' : x ∈ Ioo (0 : ℝ) 1 := hx
  rcases rationalLine_le.1 hxv with ⟨rfl, -⟩ | ⟨-, -, hv, -⟩
  · linarith [hx'.2]
  · exact hvirr hv

theorem rationalLine_not_causallyOpen : ¬ rationalLine.CausallyOpen := fun h =>
  rationalLine_not_causallyOpenFuture h.1

/-- The causality-sort witness: the rational line is absolutely minimal, causal and has push-up,
and it is neither causally arc-connected nor causally open in the future (nor causally open). -/
theorem rationalLine_separates_absolutelyMinimal :
    rationalLine.AbsolutelyMinimal ∧ rationalLine.IsCausal ∧ rationalLine.PushUp ∧
      ¬ rationalLine.CausallyArcConnected ∧ ¬ rationalLine.CausallyOpenFuture ∧
      ¬ rationalLine.CausallyOpen :=
  ⟨rationalLine_absolutelyMinimal, rationalLine_isCausal, rationalLine_pushUp,
    rationalLine_not_causallyArcConnected, rationalLine_not_causallyOpenFuture,
    rationalLine_not_causallyOpen⟩

/-- **Absolute minimality of the narrower causality does not give the converse**: causal
arc-connectedness cannot be weakened to its consequence `cor:causalement_connexe_minimal`. -/
theorem not_leNested_of_curveNested_absolutelyMinimal_bare :
    ¬ ∀ C C' : Causality ℝ, C.AbsolutelyMinimal → Causality.CurveNestedOn C C' ⊤ →
      C.LeNested C' := fun h =>
  rationalLine_not_leNested_spacelikeLine
    (h _ _ rationalLine_absolutelyMinimal (rationalLine_curveNestedOn spacelikeLine ⊤))

/-- The conjoined witness: the rational line is absolutely minimal, causal, with push-up, not
causally arc-connected, curve-nested in the (causally arc-connected) spacelike line on every
open and not ≤-nested in it. -/
theorem rationalLine_separates_curveNested :
    (∀ W : Opens ℝ, Causality.CurveNestedOn rationalLine spacelikeLine W) ∧
      ¬ rationalLine.LeNested spacelikeLine ∧ rationalLine.AbsolutelyMinimal ∧
      ¬ rationalLine.CausallyArcConnected ∧ rationalLine.IsCausal ∧ rationalLine.PushUp ∧
      spacelikeLine.CausallyArcConnected :=
  ⟨rationalLine_curveNestedOn spacelikeLine, rationalLine_not_leNested_spacelikeLine,
    rationalLine_absolutelyMinimal, rationalLine_not_causallyArcConnected, rationalLine_isCausal,
    rationalLine_pushUp, spacelikeLine_causallyArcConnected⟩

end Causal
