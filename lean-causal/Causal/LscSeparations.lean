import Causal.FutureOneConnectedVacuous
import Causal.GHWithoutTarentin
import Causal.DiamondConfinement
import Causal.Ladder.Rules

/-!
# Local strong causality separated: the symmetric rational line lacks it at every point, the loop fan has it without strong causality

No label of `ETT.tex` is certified here (no `**` mark). The file is the programme target
`T-abs-lsc-separations` (layer 1, `programme/roadmap.toml`). The ladder node is
`locally_strongly_causal`, `Causal.Causality.LocallyStronglyCausal`: every point has an open `W`
with `StronglyCausalOn W` (`Causal.DiamondConfinement`). Seven of its `[[open]]` pairs were
"False, argued" on two models already in Lean, and the ladder named the arguments:

> A: locally strongly causal at no point p: for an open W ∋ p with (p − ε, p + ε) ⊆ W and
> U = (p − ε/2, p + ε/2), every V ∈ 𝓝 p inside U holds a rational r, and J_W(r, r) holds every
> rational r' of (p + ε/2, p + ε) (uIcc r r' ⊆ W, so r ≤_W r' ≤_W r), which V misses.

> A: locally strongly causal: the ball W of radius 1/2 about a meets each tent in two arcs near
> its feet, its top (height > 1) outside W, so ≤_W relates points of one such arc only, along which
> both coordinates are monotone; the boxes {|x| < δ, y < δ} about a are then causally convex in W,
> and every other point of W has a neighbourhood meeting one arc only (the tents accumulate on the
> vertical through a only).

(`programme/ladder.toml`, the comment of the `[[open]]` section `locally_strongly_causal`, the
symmetric rational line's and the loop fan's bullets, 2026-11-27; anchored by their text, since the
file is edited often.)

* **`symmRationalLine_separates_locallyStronglyCausal`**: the 22 conjuncts of
  `symmRationalLine_separates_futureOneConnected`, then `¬ LocallyStronglyCausal`, then the strong
  form: no open `W` holding a point is strongly causal as a spacetime
  (`symmRationalLine_not_stronglyCausalOn`, the first argument, with `(l, u) ⊆ W` for
  `(p − ε, p + ε)`). It settles `absolutely_minimal`, `push_up`, `locally_push_up`,
  `curves_extend`, `future_one_connected → locally_strongly_causal`.
* **`loopFan_separates_locallyStronglyCausal`**: the 15 conjuncts of `loopFan_separates`, with
  `∀ W, AbsolutelyMinimalOn W` after `AbsolutelyMinimal`, then `FutureOneConnected`,
  `∀ W, FutureOneConnectedOn W` (`≪` empty) and `LocallyStronglyCausal`; after the four negations,
  `¬ CausallyPlain` and `¬ HasChronalNeighbourEverywhere` (`≪` empty). It settles
  `locally_strongly_causal → strongly_causal, strongly_causal_open`.
* **The loop fan's local strong causality** (`loopFan_locallyStronglyCausal`) takes three kinds of
  open set, each strongly causal as a spacetime because small centred boxes are causally convex in
  it (`loopFan_stronglyCausalOn_of_boxes`). A box is causally convex in `W` once every tent whose
  top lies in `W`, and which meets the box on both sides of that top, has the top below the box's
  ceiling (`loopFan_causallyConvexIn_box`): `x` decreases along a tent and the height is
  monotone on each side of the top. At `a`: `loopLow`, the heights below `1`, holding no top
  (`loopFan_stronglyCausalOn_low`; the ball of radius `1/2` about `a` lies in it). Off the
  vertical through `a`: `loopSide`, `x ≠ 0`, holding no top. At the top of `γ_n`: `loopCap n`, a
  band of heights holding no other top (`loopPeak_mem_cap_iff`). No "one arc only" neighbourhood
  is needed. `loopFan_stronglyCausalOn_low_not_at`: `loopLow ∋ a` is strongly causal as a
  spacetime, while in `M` no neighbourhood of `a` inside a fixed one is causally convex.
* **Coherent arcs in an open set** (general): `ArcCoherent.mem_diamond_on`, the diamond of `U` is
  a piece of one arc inside `U`; `ArcCoherent.causallyConvexIn_on`, convexity along the pieces
  inside `U` is causal convexity in `U`. They are the `U`-forms of `ArcCoherent.mem_diamond` and
  `ArcCoherent.causallyConvexIn`.

## Hypothesis checklist

| target's assertion | here |
|---|---|
| every conjunct of `symmRationalLine_separates_futureOneConnected`, with `¬ LocallyStronglyCausal` | ✓ conjuncts 1–22 in order, 23 |
| "no point has a strongly causal open neighbourhood" | ✓ conjunct 24, `∀ W p, p ∈ W → ¬ StronglyCausalOn W` |
| every conjunct of `loopFan_separates`, with `LocallyStronglyCausal` | ✓ its 15 in their order, at positions 1–3, 5–12, 16–19; `LocallyStronglyCausal` at 15 |
| future one-connectedness and `AbsolutelyMinimalOn W` for every `W` "may join" | ✓ conjuncts 4, 13, 14 |
| layer 1, no metric in a statement | ✓ coordinates and ladder properties only; balls inside proofs only |
| instance arguments | none: every statement is closed, on `ℝ` or on `loopSet` |

## SCOPE (disclosed)

* **Layer 1.** The imports reach no module of the model layer: `tools/ladder.py`'s `model_path`
  is `None` for each, checked in memory (kb/0247). `Causal.FutureOneConnectedVacuous` and
  `Causal.GHWithoutTarentin` import `Causal.Ladder.Rules`, so this module stays a leaf: nothing in
  the import closure of `Causal.Ladder.Rules` may import it (kb/0221).
* **The loop fan's open sets differ from the ladder's.** The ladder's ball of radius `1/2` is
  replaced by `loopLow` at `a` (the ball lies in it, so heredity gives the ball). The other points
  take `loopSide` or `loopCap n`. The node is an existential over `W`, so the statement is the same.
* **Not decided for the loop fan:** the four causally open forms. Argued open: every point of a
  tent has a neighbourhood meeting that tent only, so `J^±_U(V)` is open. Not stated; no pair of
  the ladder moves with them (the report's simulation).
* **Either reading** of `defi:causalite` for both: `∀ W, AbsolutelyMinimalOn W` is a conjunct.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Relation Filter

universe u v

/-! ## Coherent arcs: diamonds and causal convexity in an open set -/

section Arcs

variable {M : Type u} [TopologicalSpace M] {ι : Type v} {γ : ι → ℝ → M} {U : Opens M}
  {p q z : M}

/-- **The diamond of an open `U` for coherent arcs** (the `U`-form of `ArcCoherent.mem_diamond`):
the first point, or a point of the piece of one arc between the two ends, the piece inside `U`. -/
theorem ArcCoherent.mem_diamond_on (hc : ArcCoherent γ)
    (hz : z ∈ (arcCausality γ).diamond U p q) :
    z = p ∨ ∃ i s r t, 0 ≤ s ∧ s ≤ r ∧ r ≤ t ∧ t ≤ 1 ∧ γ i s = p ∧ γ i r = z ∧ γ i t = q ∧
      ∀ ρ ∈ Icc s t, γ i ρ ∈ U := by
  obtain ⟨hpz, hzq⟩ := Causality.mem_diamond.1 hz
  rcases hc.le_iff.1 hpz with ⟨-, h⟩ | ⟨i, s, r, hs, hsr, hr, rfl, rfl, hU₁⟩
  · exact Or.inl h.symm
  rcases hc.le_iff.1 hzq with ⟨-, h⟩ | ⟨j, s', t, hs', hs't, ht, hz', rfl, hU₂⟩
  · exact Or.inr ⟨i, s, r, r, hs, hsr, le_rfl, hr, rfl, rfl, h, hU₁⟩
  · obtain ⟨e, hagree⟩ := hc i j r s' ⟨hs.trans hsr, hr⟩ ⟨hs', hs't.trans ht⟩ hz'.symm
    subst e
    refine Or.inr ⟨j, s, r, t, hs, hsr, hs't, ht, (hagree s ⟨hs, hsr⟩).symm,
      (hagree r ⟨hs.trans hsr, le_rfl⟩).symm, rfl, fun ρ hρ => ?_⟩
    rcases le_total ρ r with hρr | hρr
    · rw [← hagree ρ ⟨hs.trans hρ.1, hρr⟩]; exact hU₁ ρ ⟨hρ.1, hρr⟩
    · exact hU₂ ρ ⟨hρr, hρ.2⟩

/-- **A subset of `U` convex along every piece of arc inside `U` is causally convex in `U`**
(`defi:convexite_causale`; the `U`-form of `ArcCoherent.causallyConvexIn`). -/
theorem ArcCoherent.causallyConvexIn_on (hc : ArcCoherent γ) {V : Set M} (hVU : V ⊆ U)
    (hV : ∀ i s r t, 0 ≤ s → s ≤ r → r ≤ t → t ≤ 1 → (∀ ρ ∈ Icc s t, γ i ρ ∈ U) →
      γ i s ∈ V → γ i t ∈ V → γ i r ∈ V) :
    (arcCausality γ).CausallyConvexIn V U := by
  refine ⟨hVU, fun p hp q hq z hz => ?_⟩
  rcases hc.mem_diamond_on hz with rfl | ⟨i, s, r, t, hs, hsr, hrt, ht, rfl, rfl, rfl, hU⟩
  · exact hp
  · exact hV i s r t hs hsr hrt ht hU hp hq

end Arcs

/-! ## The symmetric rational line is locally strongly causal at no point -/

/-- **No open set holding a point of the symmetric rational line is strongly causal as a
spacetime.** With `(l, u) ⊆ W` about `p` and `m` the midpoint of `p` and `u`, a neighbourhood `V`
of `p` inside `(l, m)` holds a rational `r`, and a rational `r'` of `(m, u)` has `r ≤_W r' ≤_W r`
(`uIcc r r' ⊆ W`): `r' ∈ J_W(r, r)`, outside `V`. -/
theorem symmRationalLine_not_stronglyCausalOn {W : Opens ℝ} {p : ℝ} (hp : p ∈ W) :
    ¬ symmRationalLine.StronglyCausalOn W := by
  intro h
  obtain ⟨l, u, ⟨hl, hu⟩, hlu⟩ := mem_nhds_iff_exists_Ioo_subset.1 (W.isOpen.mem_nhds hp)
  set m := (p + u) / 2 with hm
  obtain ⟨V, hV, hVU, hconv⟩ := h p hp (Ioo l m) (Ioo_mem_nhds hl (by linarith))
  obtain ⟨a, b, ⟨ha, hb⟩, hab⟩ := mem_nhds_iff_exists_Ioo_subset.1 hV
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (ha.trans hb)
  obtain ⟨r', hr'1, hr'2⟩ := exists_rat_btwn (show m < u by linarith)
  have hrV : (r : ℝ) ∈ V := hab ⟨hr1, hr2⟩
  have hrU := hVU hrV
  have hsub : uIcc (r : ℝ) r' ⊆ (W : Set ℝ) := by
    rw [uIcc_of_le (by linarith [hrU.2])]
    exact fun x hx => hlu ⟨by linarith [hrU.1, hx.1], by linarith [hx.2]⟩
  have hsub' : uIcc (r' : ℝ) r ⊆ (W : Set ℝ) := uIcc_comm (r : ℝ) r' ▸ hsub
  have hd : (r' : ℝ) ∈ symmRationalLine.diamond W r r :=
    Causality.mem_diamond.2 ⟨Or.inr ⟨⟨r, rfl⟩, ⟨r', rfl⟩, hsub⟩, Or.inr ⟨⟨r', rfl⟩, ⟨r, rfl⟩, hsub'⟩⟩
  have := hVU (hconv.2 _ hrV _ hrV hd)
  linarith [this.2]

/-- **The symmetric rational line is not locally strongly causal** (at `0`, and at every point). -/
theorem symmRationalLine_not_locallyStronglyCausal : ¬ symmRationalLine.LocallyStronglyCausal :=
  fun h => let ⟨_, hpW, hW⟩ := h 0; symmRationalLine_not_stronglyCausalOn hpW hW

/-- **The symmetric rational line's full form, with local strong causality** (either reading:
absolutely minimal on every open set for every cover). The 22 conjuncts of
`symmRationalLine_separates_futureOneConnected`, in its order: future one-connected (on every open
set), absolutely minimal (on every open set), push-up, locally push-up, curves extend; not causal,
strongly causal in neither form, not globally hyperbolic, no time function, not causally compact,
not causally arc-connected, causally open in no form, not tarentin, not causally plain, no chronal
neighbours, no chronal neighbour at some point. Then: not locally strongly causal, and no open set
holding a point is strongly causal as a spacetime. -/
theorem symmRationalLine_separates_locallyStronglyCausal :
    symmRationalLine.FutureOneConnected ∧
      (∀ W : Opens ℝ, symmRationalLine.FutureOneConnectedOn W) ∧
      symmRationalLine.AbsolutelyMinimal ∧
      (∀ W : Opens ℝ, symmRationalLine.AbsolutelyMinimalOn W) ∧
      symmRationalLine.PushUp ∧ symmRationalLine.LocallyPushUp ∧ symmRationalLine.CurvesExtend ∧
      ¬ symmRationalLine.IsCausal ∧ ¬ symmRationalLine.StronglyCausal ∧
      ¬ symmRationalLine.StronglyCausalOpen ∧ ¬ symmRationalLine.GloballyHyperbolic ∧
      ¬ symmRationalLine.HasTimeFunction ∧ ¬ symmRationalLine.CausallyCompact ∧
      ¬ symmRationalLine.CausallyArcConnected ∧ ¬ symmRationalLine.CausallyOpenFuture ∧
      ¬ symmRationalLine.CausallyOpen ∧ ¬ symmRationalLine.LocallyCausallyOpenFuture ∧
      ¬ symmRationalLine.LocallyCausallyOpen ∧ ¬ symmRationalLine.Tarentin ∧
      ¬ symmRationalLine.CausallyPlain ∧ ¬ symmRationalLine.ChronalNeighbours ∧
      ¬ symmRationalLine.HasChronalNeighbourEverywhere ∧
      ¬ symmRationalLine.LocallyStronglyCausal ∧
      (∀ (W : Opens ℝ) (p : ℝ), p ∈ W → ¬ symmRationalLine.StronglyCausalOn W) :=
  let ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇, h₁₈, h₁₉,
    h₂₀, h₂₁, h₂₂⟩ := symmRationalLine_separates_futureOneConnected
  ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇, h₁₈, h₁₉, h₂₀, h₂₁,
    h₂₂, symmRationalLine_not_locallyStronglyCausal,
    fun _ _ hp => symmRationalLine_not_stronglyCausalOn hp⟩

/-! ## The loop fan is locally strongly causal -/

/-- An open box of the loop fan: the points with coordinates in `(a, b) × (c, d)`. -/
def loopBox (a b c d : ℝ) : Set loopSet := {z | z.val.1 ∈ Ioo a b ∧ z.val.2 ∈ Ioo c d}

theorem isOpen_loopBox (a b c d : ℝ) : IsOpen (loopBox a b c d) :=
  (isOpen_Ioo.preimage (continuous_fst.comp continuous_subtype_val)).inter
    (isOpen_Ioo.preimage (continuous_snd.comp continuous_subtype_val))

/-- The coordinates along the tent `γ_n`: `x = ε_n (1 − 2t)` and height
`1 + ε_n − (n + 2) ε_n |1 − 2t|`. -/
theorem loopγ_val_of_mem {n : ℕ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (loopγ n t).val = (combEps n * (1 - 2 * t),
      1 + combEps n - ((n : ℝ) + 2) * (combEps n * |1 - 2 * t|)) := by
  show loopArc n t = _
  rw [loopArc_of_mem ht, abs_mul, abs_of_pos (combEps_pos n)]

/-- The height along a tent decreases with `|1 − 2t|`. -/
theorem loopHeight_le {n : ℕ} {r t : ℝ} (h : |1 - 2 * t| ≤ |1 - 2 * r|) :
    1 + combEps n - ((n : ℝ) + 2) * (combEps n * |1 - 2 * r|) ≤
      1 + combEps n - ((n : ℝ) + 2) * (combEps n * |1 - 2 * t|) := by
  have := combEps_pos n
  gcongr

/-- No point of a tent is above its top. -/
theorem loopHeight_le_top {n : ℕ} {r : ℝ} :
    1 + combEps n - ((n : ℝ) + 2) * (combEps n * |1 - 2 * r|) ≤ 1 + combEps n := by
  have := combEps_pos n
  have : 0 ≤ ((n : ℝ) + 2) * (combEps n * |1 - 2 * r|) := by positivity
  linarith

/-- **A box is causally convex in `W`** once every tent whose top lies in `W`, and which meets
the box on both sides of its top, has that top below the box's ceiling (the hypothesis asks the
top in `W`, not the whole piece between). Along a tent `x` decreases, and the height increases up
to the top and decreases after it. -/
theorem loopFan_causallyConvexIn_box {W : Opens loopSet} {a b c d : ℝ}
    (hBW : loopBox a b c d ⊆ W)
    (hcross : ∀ n s t, 0 ≤ s → s < 1 / 2 → 1 / 2 < t → t ≤ 1 → loopγ n (1 / 2) ∈ W →
      loopγ n s ∈ loopBox a b c d → loopγ n t ∈ loopBox a b c d → 1 + combEps n < d) :
    loopFan.CausallyConvexIn (loopBox a b c d) W := by
  refine loopγ_coherent.causallyConvexIn_on hBW fun n s r t hs hsr hrt ht hW hsB htB => ?_
  have hε := combEps_pos n
  have hs1 : s ∈ Icc (0 : ℝ) 1 := ⟨hs, by linarith⟩
  have hr1 : r ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have ht1 : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith, ht⟩
  have hsB' := hsB
  have htB' := htB
  obtain ⟨⟨hsa, hsb⟩, hsc, hsd⟩ := hsB
  obtain ⟨⟨hta, htb⟩, htc, htd⟩ := htB
  rw [loopγ_val_of_mem hs1] at hsa hsb hsc hsd
  rw [loopγ_val_of_mem ht1] at hta htb htc htd
  show (loopγ n r).val.1 ∈ Ioo a b ∧ (loopγ n r).val.2 ∈ Ioo c d
  rw [loopγ_val_of_mem hr1]
  dsimp only at hsa hsb hsc hsd hta htb htc htd ⊢
  refine ⟨⟨by nlinarith, by nlinarith⟩, ?_, ?_⟩
  · -- the height is at least the smaller of the two ends'
    rcases le_total r (1 / 2) with hr | hr
    · refine lt_of_lt_of_le hsc (loopHeight_le ?_)
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
    · refine lt_of_lt_of_le htc (loopHeight_le ?_)
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
  · -- on one side of the top the height is monotone; across it, the top is below the ceiling
    by_cases ht2 : t ≤ 1 / 2
    · refine lt_of_le_of_lt (loopHeight_le ?_) htd
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
    by_cases hs2 : 1 / 2 ≤ s
    · refine lt_of_le_of_lt (loopHeight_le ?_) hsd
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
    rw [not_le] at ht2 hs2
    exact lt_of_le_of_lt loopHeight_le_top
      (hcross n s t hs hs2 ht2 ht (hW (1 / 2) ⟨hs2.le, ht2.le⟩) hsB' htB')

/-- An open `W` of the loop fan is strongly causal as a spacetime once, about each of its points,
the small centred boxes are causally convex in `W` (a ball of the plane holds a centred box). -/
theorem loopFan_stronglyCausalOn_of_boxes {W : Opens loopSet}
    (h : ∀ q ∈ W, ∃ κ > 0, ∀ δ, 0 < δ → δ ≤ κ →
      loopFan.CausallyConvexIn (loopBox (q.val.1 - δ) (q.val.1 + δ) (q.val.2 - δ) (q.val.2 + δ)) W) :
    loopFan.StronglyCausalOn W := by
  intro q hq U hU
  obtain ⟨κ, hκ, hconv⟩ := h q hq
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hU
  have hδ' : 0 < min δ κ := lt_min hδ hκ
  have hle := min_le_left δ κ
  refine ⟨loopBox (q.val.1 - min δ κ) (q.val.1 + min δ κ) (q.val.2 - min δ κ)
    (q.val.2 + min δ κ), (isOpen_loopBox _ _ _ _).mem_nhds
      ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, fun z hz => hball ?_,
    hconv _ hδ' (min_le_right _ _)⟩
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz
  rw [Metric.mem_ball, Subtype.dist_eq, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq,
    abs_sub_lt_iff, abs_sub_lt_iff]
  exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-- The points of the loop fan below height `1`: no tent's top (height `1 + ε_n`). -/
def loopLow : Opens loopSet :=
  ⟨{z | z.val.2 < 1}, isOpen_lt (continuous_snd.comp continuous_subtype_val) continuous_const⟩

/-- The points of the loop fan off the vertical through `a`: no tent's top. -/
def loopSide : Opens loopSet :=
  ⟨{z | z.val.1 ≠ 0}, isOpen_ne_fun (continuous_fst.comp continuous_subtype_val) continuous_const⟩

/-- The band of heights `(1 + ε_{n+1}, 1 + 2ε_n − ε_{n+1})` about the top of `γ_n`: no other
tent's top (`loopPeak_mem_cap_iff`). -/
def loopCap (n : ℕ) : Opens loopSet :=
  ⟨{z | 1 + combEps (n + 1) < z.val.2 ∧ z.val.2 < 1 + 2 * combEps n - combEps (n + 1)},
    (isOpen_lt continuous_const (continuous_snd.comp continuous_subtype_val)).inter
      (isOpen_lt (continuous_snd.comp continuous_subtype_val) continuous_const)⟩

theorem loopA_mem_loopLow : loopA ∈ loopLow := by
  show loopA.val.2 < 1
  rw [loopA_val]
  norm_num

/-- A point of the loop fan is `a`, or a point of a tent at a parameter of `[0, 1]`. -/
theorem loopSet_cases (z : loopSet) : z = loopA ∨ ∃ n, ∃ t ∈ Icc (0 : ℝ) 1, z = loopγ n t := by
  obtain ⟨v, hv⟩ := z
  rcases (mem_insert_iff.1 hv) with rfl | hv
  · exact Or.inl rfl
  obtain ⟨n, t, rfl⟩ := mem_iUnion.1 hv
  have hc : clampUnit t ∈ Icc (0 : ℝ) 1 :=
    ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
  refine Or.inr ⟨n, clampUnit t, hc, Subtype.ext ?_⟩
  show loopArc n t = loopArc n (clampUnit t)
  simp only [loopArc, clampUnit_of_mem hc]

/-- A point of a tent on the vertical through `a` is its top. -/
theorem eq_half_of_loopγ_fst {n : ℕ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (h : (loopγ n t).val.1 = 0) : t = 1 / 2 := by
  rw [loopγ_val_of_mem ht] at h
  have := (mul_eq_zero.1 h).resolve_left (combEps_pos n).ne'
  linarith

/-- The tops of the taller tents are above the band `loopCap n`: `2ε_n − ε_{n+1} ≤ ε_m` for
`m < n`. -/
theorem combEps_two_mul_sub_le {m n : ℕ} (h : m < n) :
    2 * combEps n - combEps (n + 1) ≤ combEps m := by
  have hm : (m : ℝ) + 1 ≤ n := by exact_mod_cast h
  unfold combEps
  push_cast
  rw [show 2 * (1 / ((n : ℝ) + 1)) - 1 / ((n : ℝ) + 1 + 1) =
      ((n : ℝ) + 3) / (((n : ℝ) + 1) * ((n : ℝ) + 2)) by field_simp; ring,
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- **The band `loopCap n` holds the top of `γ_n` and no other top.** -/
theorem loopPeak_mem_cap_iff {m n : ℕ} : loopγ m (1 / 2) ∈ loopCap n ↔ m = n := by
  show 1 + combEps (n + 1) < (loopγ m (1 / 2)).val.2 ∧
    (loopγ m (1 / 2)).val.2 < 1 + 2 * combEps n - combEps (n + 1) ↔ m = n
  rw [loopPeak_val]
  dsimp only
  constructor
  · rintro ⟨h1, h2⟩
    have hmn : m < n + 1 := (StrictAnti.lt_iff_gt combEps_strictAnti).1 (by linarith)
    rcases Nat.lt_succ_iff_lt_or_eq.1 hmn with hlt | heq
    · have := combEps_two_mul_sub_le hlt
      linarith
    · exact heq
  · rintro rfl
    have := combEps_strictAnti (Nat.lt_succ_self m)
    exact ⟨by linarith, by linarith⟩

/-- **Below height `1` the loop fan is strongly causal as a spacetime**: no piece of a tent inside
`loopLow` passes a top, so every box with ceiling at most `1` is causally convex in it. -/
theorem loopFan_stronglyCausalOn_low : loopFan.StronglyCausalOn loopLow := by
  refine loopFan_stronglyCausalOn_of_boxes fun q hq => ⟨1 - q.val.2, sub_pos.2 hq,
    fun δ hδ hδκ => loopFan_causallyConvexIn_box (fun z hz => ?_) ?_⟩
  · show z.val.2 < 1
    linarith [hz.2.2]
  · intro n s t _ _ _ _ hpeak _ _
    have h : (loopγ n (1 / 2)).val.2 < 1 := hpeak
    rw [loopPeak_val] at h
    linarith [combEps_pos n]

/-- **Off the vertical through `a` the loop fan is strongly causal as a spacetime**: no piece of a
tent inside `loopSide` passes a top. -/
theorem loopFan_stronglyCausalOn_side : loopFan.StronglyCausalOn loopSide := by
  refine loopFan_stronglyCausalOn_of_boxes fun q hq => ⟨|q.val.1|, abs_pos.2 hq,
    fun δ hδ hδκ => loopFan_causallyConvexIn_box (fun z hz => ?_) ?_⟩
  · show z.val.1 ≠ 0
    obtain ⟨⟨h1, h2⟩, -⟩ := hz
    rcases lt_or_gt_of_ne (show q.val.1 ≠ 0 from hq) with hneg | hpos
    · rw [abs_of_neg hneg] at hδκ; linarith
    · rw [abs_of_pos hpos] at hδκ; linarith
  · intro n s t _ _ _ _ hpeak _ _
    have h : (loopγ n (1 / 2)).val.1 ≠ 0 := hpeak
    rw [loopPeak_val] at h
    exact absurd rfl h

/-- **About the top of `γ_n` the loop fan is strongly causal as a spacetime**: a piece of a tent
inside `loopCap n` passing a top passes the top of `γ_n`. A box about the top is above it; a box
about another point of the band, narrower than its distance to the vertical, holds no two points
on either side of a top. -/
theorem loopFan_stronglyCausalOn_cap (n : ℕ) : loopFan.StronglyCausalOn (loopCap n) := by
  refine loopFan_stronglyCausalOn_of_boxes fun q hq => ?_
  obtain ⟨hq1, hq2⟩ := hq
  set κ₀ := min (q.val.2 - (1 + combEps (n + 1))) (1 + 2 * combEps n - combEps (n + 1) - q.val.2)
  have hκ₀ : 0 < κ₀ := lt_min (by linarith) (by linarith)
  have hBW : ∀ δ, δ ≤ κ₀ → loopBox (q.val.1 - δ) (q.val.1 + δ) (q.val.2 - δ) (q.val.2 + δ) ⊆
      loopCap n := fun δ hδ z hz => by
    have h1 := min_le_left (q.val.2 - (1 + combEps (n + 1)))
      (1 + 2 * combEps n - combEps (n + 1) - q.val.2)
    have h2 := min_le_right (q.val.2 - (1 + combEps (n + 1)))
      (1 + 2 * combEps n - combEps (n + 1) - q.val.2)
    obtain ⟨-, h3, h4⟩ := hz
    exact ⟨by linarith, by linarith⟩
  by_cases hx : q.val.1 = 0
  · -- `q` is the top of `γ_n`
    have hqn : q = loopγ n (1 / 2) := by
      rcases loopSet_cases q with rfl | ⟨m, t, ht, rfl⟩
      · rw [loopA_val] at hq1
        linarith [combEps_pos (n + 1)]
      · obtain rfl := eq_half_of_loopγ_fst ht hx
        rw [loopPeak_mem_cap_iff.1 ⟨hq1, hq2⟩]
    refine ⟨κ₀, hκ₀, fun δ hδ hδκ => loopFan_causallyConvexIn_box (hBW δ hδκ) ?_⟩
    intro m s t _ _ _ _ hpeak _ _
    rw [loopPeak_mem_cap_iff.1 hpeak, hqn, loopPeak_val]
    dsimp only
    linarith
  · refine ⟨min |q.val.1| κ₀, lt_min (abs_pos.2 hx) hκ₀, fun δ hδ hδκ =>
      loopFan_causallyConvexIn_box (hBW δ (hδκ.trans (min_le_right _ _))) ?_⟩
    have hδx := hδκ.trans (min_le_left _ _)
    intro m s t hs hs2 ht2 ht hpeak hsB htB
    exfalso
    have hsx := hsB.1
    have htx := htB.1
    rw [loopγ_val_of_mem ⟨hs, by linarith⟩] at hsx
    rw [loopγ_val_of_mem ⟨by linarith, ht⟩] at htx
    dsimp only at hsx htx
    have hε := combEps_pos m
    have hs0 : 0 < combEps m * (1 - 2 * s) := mul_pos hε (by linarith)
    have ht0 : combEps m * (1 - 2 * t) < 0 := mul_neg_of_pos_of_neg hε (by linarith)
    rcases lt_or_gt_of_ne hx with hneg | hpos
    · rw [abs_of_neg hneg] at hδx; linarith [hsx.2]
    · rw [abs_of_pos hpos] at hδx; linarith [htx.1]

/-- **The loop fan is locally strongly causal** (the ladder's `locally_strongly_causal`): `a` lies
in `loopLow`, a point off the vertical through `a` in `loopSide`, and the top of `γ_n` in
`loopCap n`. -/
theorem loopFan_locallyStronglyCausal : loopFan.LocallyStronglyCausal := by
  intro p
  by_cases hx : p.val.1 = 0
  · rcases loopSet_cases p with rfl | ⟨n, t, ht, rfl⟩
    · exact ⟨loopLow, loopA_mem_loopLow, loopFan_stronglyCausalOn_low⟩
    · obtain rfl := eq_half_of_loopγ_fst ht hx
      exact ⟨loopCap n, loopPeak_mem_cap_iff.2 rfl, loopFan_stronglyCausalOn_cap n⟩
  · exact ⟨loopSide, hx, loopFan_stronglyCausalOn_side⟩

/-- **Strongly causal about `a` as a spacetime, though not at `a` in `M`**: the open `loopLow ∋ a`
is strongly causal as a spacetime, while some neighbourhood of `a` contains no neighbourhood of
`a` causally convex in `M` (`loopFan_not_stronglyCausalAt`). -/
theorem loopFan_stronglyCausalOn_low_not_at :
    loopA ∈ loopLow ∧ loopFan.StronglyCausalOn loopLow ∧
      ∃ U ∈ 𝓝 loopA, ∀ V ∈ 𝓝 loopA, V ⊆ U → ¬ loopFan.CausallyConvexIn V ⊤ :=
  ⟨loopA_mem_loopLow, loopFan_stronglyCausalOn_low, loopFan_not_stronglyCausalAt⟩

/-- **The loop fan's full form, with local strong causality** (either reading: absolutely minimal
on every open set for every cover). The 15 conjuncts of `loopFan_separates`, in its order:
Hausdorff, second countable, absolutely minimal (and on every open set, inserted), causally
arc-connected, push-up, locally push-up, causal, causally compact, globally hyperbolic, a time
function, curves extend; then future one-connected (on every open set, `≪` being empty) and
locally strongly causal; strongly causal in neither form, not tarentin, no chronal neighbours;
then not causally plain and no chronal neighbour at some point (`≪` empty). -/
theorem loopFan_separates_locallyStronglyCausal :
    T2Space loopSet ∧ SecondCountableTopology loopSet ∧
      loopFan.AbsolutelyMinimal ∧ (∀ W : Opens loopSet, loopFan.AbsolutelyMinimalOn W) ∧
      loopFan.CausallyArcConnected ∧ loopFan.PushUp ∧ loopFan.LocallyPushUp ∧
      loopFan.IsCausal ∧ loopFan.CausallyCompact ∧ loopFan.GloballyHyperbolic ∧
      loopFan.HasTimeFunction ∧ loopFan.CurvesExtend ∧
      loopFan.FutureOneConnected ∧ (∀ W : Opens loopSet, loopFan.FutureOneConnectedOn W) ∧
      loopFan.LocallyStronglyCausal ∧
      ¬ loopFan.StronglyCausal ∧ ¬ loopFan.StronglyCausalOpen ∧ ¬ loopFan.Tarentin ∧
      ¬ loopFan.ChronalNeighbours ∧ ¬ loopFan.CausallyPlain ∧
      ¬ loopFan.HasChronalNeighbourEverywhere := by
  obtain ⟨hT2, hSC2, hAM, hAC, hPU, hLPU, hC, hCC, hGH, hTF, hCE, hNSC, hNSCO, hNT, hNCN⟩ :=
    loopFan_separates
  have hlt : ∀ (U : Opens loopSet) (x y : loopSet), ¬ loopFan.lt U x y := fun _ _ _ h => h
  haveI : Nonempty loopSet := ⟨loopA⟩
  exact ⟨hT2, hSC2, hAM, loopFan_absolutelyMinimalOn, hAC, hPU, hLPU, hC, hCC, hGH, hTF, hCE,
    Causality.futureOneConnectedOn_of_forall_not_lt (hlt ⊤),
    fun W => Causality.futureOneConnectedOn_of_forall_not_lt (hlt W),
    loopFan_locallyStronglyCausal, hNSC, hNSCO, hNT, hNCN,
    Causality.not_causallyPlain_of_forall_not_lt (hlt ⊤),
    Causality.not_hasChronalNeighbourEverywhere_of_forall_not_lt (hlt ⊤)⟩

end Causal
