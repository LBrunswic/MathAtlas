import Causal.LscSeparations

/-!
# The loop fan at every scale: globally hyperbolic and causally compact, not locally strongly causal

No label of `ETT.tex` is certified here (no `**` mark). The file is the programme target
`T-abs-loop-fan-every-scale` (layer 1, `programme/roadmap.toml`), a ladder witness for the node
`locally_strongly_causal` (`Causal.Causality.LocallyStronglyCausal`: every point has an open `W`
with `StronglyCausalOn W`). Imports: `Causal.LscSeparations` only (ETT layer: it imports
`Causal.FutureOneConnectedVacuous`, `Causal.GHWithoutTarentin`, `Causal.DiamondConfinement` and
`Causal.Ladder.Rules`; no model, transitively), so this module is a leaf.

> The loop fan at every scale: for each k ∈ ℕ a copy of the loop fan scaled by 2⁻ᵏ, the copies'
> arcs pairwise disjoint and accumulating at one point a (in distinct vertical planes through a in
> ℝ³, or an equivalent carrier the closer reports), with the arc causality of all the arcs. One
> conjoined theorem: T2, second countable, absolutely minimal on every open, causally
> arc-connected, push-up, causal, causally compact, globally hyperbolic, a time function, curves
> extend, future one-connected (vacuously), and ¬ LocallyStronglyCausal (at a), with ¬ Tarentin
> and ¬ ChronalNeighbours
(the target's title, `programme/roadmap.toml`)

> Not locally strongly causal at a: an open W ∋ a holds a ball B(a, r); for U = B(a, ρ),
> ρ < r/4, a level k with 2⁻ᵏ ∈ (ρ, r/4] has its loops of large index inside B(a, r) ⊆ W with
> both feet in any V ∈ 𝓝 a inside U, and J_W of the two feet holds the loop's top, at height > ρ,
> outside U.
(`programme/ladder.toml`, the `[[open]]` section `locally_strongly_causal`, the bullet "the loop
fan at every scale (not in Lean)"; anchored by its text, since the file is edited often.)

* **The carrier** `scaledFanSet ⊆ ℝ × ℝ × ℝ`: `a = (0, 0, 0)` (`scaledFanA`) and the arcs
  `scaledFanγ (k, n)`, the loop fan's tent `γ_n` (`Causal.loopArc n`) carried into the vertical
  plane `Y = ε_k X` by `levelEmbed k : (x, y) ↦ 2⁻ᵏ (x, ε_k x, y)` (`ε_k = combEps k = 1/(k+1)`,
  distinct slopes; `fanScale k = 2⁻ᵏ`). With the arc causality `scaledFan := arcCausality
  scaledFanγ` (`≪` empty).
* **The arcs are coherent** (`scaledFanγ_coherent`): two levels meet nowhere
  (`scaledFanArc_level_eq`: off the vertical the slopes differ; on it an arc has its top only, at
  height `2⁻ᵏ (1 + ε_n) ∈ (2⁻ᵏ, 2¹⁻ᵏ]`, disjoint intervals, `fanScale_two_mul_le`), and within a
  level `levelEmbed k` is injective, so `Causal.loopγ_coherent` applies.
* **Not strongly causal about `a`** (`scaledFan_not_stronglyCausalOn`): no open `W ∋ a` is
  `StronglyCausalOn W`, hence `scaledFan_not_locallyStronglyCausal`. With `B(a, r) ⊆ W`, a level
  `k` with `2 · 2⁻ᵏ < r` lies in `W` (`scaledFanγ_coord_le`); for `U = {Z < 2⁻ᵏ}`, any `V ∈ 𝓝 a`
  inside `U` holds both feet of a loop of level `k` (`tendsto_scaledFanP`, `tendsto_scaledFanQ`),
  and `J_W` of the feet holds the loop's top, at height `2⁻ᵏ (1 + ε_n)`, outside `U`.
* **A time function** (`scaledFan_hasTimeFunction`): `−X`, strictly increasing along every arc.
* **Causally open in no form** (beyond the target; `scaledFan_not_causallyOpenFutureOn`,
  `scaledFan_not_locallyCausallyOpenFuture`): the top `(0, 0, 1)` of the tent `(1, 0)` is the
  limit of the tops of level `0`. Every open `W` holding it has `J⁺_W(V)`, `V = W ∩ {Y < X}`
  (`scaledFanBelow`), holding that top (reached along its own tent from below the diagonal) and no
  point of level `0` (which lies in `Y = X`, `scaledFanγ_zero_snd`), so `J⁺_W(V)` is not open.
* **`scaledFan_separates`**: the conjoined witness, 26 conjuncts, deciding all 21 causality nodes
  of the ladder (10 held, 11 lacked); either reading of DEC-167 (`∀ W, AbsolutelyMinimalOn W`).
  It is the witness of `globally_hyperbolic`, `causally_compact ⇏ locally_strongly_causal`.
* **`not_locallyStronglyCausal_of_globallyHyperbolic_bare`**: `prop:GH_fortement_causal` is sharp
  in tarentin even for local strong causality (the loop fan's bare form,
  `not_stronglyCausal_of_globallyHyperbolic_bare`, with `LocallyStronglyCausal`).

## Hypothesis checklist

| target's assertion | here |
|---|---|
| a copy of the loop fan scaled by `2⁻ᵏ` for each `k`, in distinct vertical planes through `a` | ✓ `levelEmbed k`, the plane `Y = ε_k X` (a linear copy: SCOPE) |
| the copies' arcs pairwise disjoint, accumulating at `a` | ✓ across levels `scaledFanArc_level_eq`; within a level as in the loop fan (inside `loopγ_coherent`'s proof; `ArcCoherent` itself states no disjointness); the arcs coherent, `scaledFanγ_coherent`; the feet of every level tend to `a` |
| the arc causality of all the arcs | ✓ `scaledFan := arcCausality scaledFanγ` |
| T2, second countable | ✓ conjuncts 1–2 (a subspace of `ℝ³`) |
| absolutely minimal on every open, causally arc-connected, push-up | ✓ conjuncts 3–7 (and locally push-up) |
| causal, causally compact, globally hyperbolic, a time function, curves extend | ✓ conjuncts 8–12 |
| future one-connected (vacuously) | ✓ conjuncts 13–14 (on every open set; `≪` empty) |
| ¬ LocallyStronglyCausal (at `a`) | ✓ conjuncts 15–16 (16: no open `W ∋ a` is `StronglyCausalOn W`) |
| ¬ Tarentin, ¬ ChronalNeighbours | ✓ conjuncts 19–20 |
| (the ladder's closure) ¬ StronglyCausal (both forms), ¬ CausallyPlain, ¬ HasChronalNeighbourEverywhere | ✓ conjuncts 17–18, 21–22 |
| (beyond) causally open in no form | ✓ conjuncts 23–26 |
| layer 1, no metric in a statement | ✓ coordinates of `ℝ³` only; `Metric.mem_nhds_iff` and `dist` inside one proof |

## SCOPE (disclosed)

* **A linear copy, not a similarity.** Level `k` is `(x, y) ↦ 2⁻ᵏ (x, ε_k x, y)`: height and the
  `X`-coordinate are scaled by `2⁻ᵏ`, the plane's own horizontal direction by `2⁻ᵏ √(1 + ε_k²)`
  (the slope `ε_k` in place of an angle `θ_k = arctan ε_k ∈ (0, π/4]`, to keep trigonometry out).
  Same incidences, limits and local picture as the target's copy; homeomorphic, argued.
* **Either reading** of `defi:causalite` (DEC-167): conjunct 4.
* **The carrier** is a subspace of `ℝ × ℝ × ℝ` with its product (sup) metric, used inside the
  proof of `scaledFan_not_stronglyCausalOn` only. The ladder's Euclidean ball is replaced by the sup
  ball; the level is chosen first (`2 · 2⁻ᵏ < r`) and `U = {Z < 2⁻ᵏ}`, in place of `U = B(a, ρ)`.
* Not decided: whether some open set strongly causal as a spacetime holds a given point other than
  `a`. The loop fan's argument (`Causal.loopFan_locallyStronglyCausal`) does not transfer
  verbatim, since the tops of level `0` accumulate at the top `(0, 0, 1)` of the tent `(1, 0)`.
  Not stated either: the failure of the causally open forms in the past (`C.dual`). No ladder pair
  needs these.
* Names checked unique against `lean-causal/Causal`, the scaffold, `lean-gx`, `lean-benzecri`,
  `lean` and `lean-egf`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Relation Filter

/-! ## Coordinates -/

/-- The scale of level `k`: `2⁻ᵏ`. -/
noncomputable def fanScale (k : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ k

theorem fanScale_pos (k : ℕ) : 0 < fanScale k := by unfold fanScale; positivity

/-- A deeper level is at most half as tall: `2 · 2⁻ᵏ' ≤ 2⁻ᵏ` for `k < k'`. -/
theorem fanScale_two_mul_le {k k' : ℕ} (h : k < k') : 2 * fanScale k' ≤ fanScale k := by
  unfold fanScale
  have : (2 : ℝ)⁻¹ ^ k' ≤ (2 : ℝ)⁻¹ ^ (k + 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) h
  rw [pow_succ] at this
  linarith

theorem fanScale_zero : fanScale 0 = 1 := pow_zero _

theorem fanScale_one : fanScale 1 = 1 / 2 := by unfold fanScale; norm_num

theorem combEps_zero : combEps 0 = 1 := by unfold combEps; norm_num

theorem combEps_one : combEps 1 = 1 / 2 := by unfold combEps; norm_num

/-- Level `k`'s plane: `(x, y) ↦ 2⁻ᵏ (x, ε_k x, y)`, the vertical plane `Y = ε_k X` through
`a = (0, 0, 0)`, scaled by `2⁻ᵏ`. -/
noncomputable def levelEmbed (k : ℕ) (v : ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (fanScale k * v.1, fanScale k * combEps k * v.1, fanScale k * v.2)

theorem continuous_levelEmbed (k : ℕ) : Continuous (levelEmbed k) :=
  (continuous_const.mul continuous_fst).prodMk
    ((continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd))

theorem levelEmbed_injective (k : ℕ) : Function.Injective (levelEmbed k) := by
  intro v w h
  simp only [levelEmbed, Prod.mk.injEq] at h
  obtain ⟨h1, -, h3⟩ := h
  have hs := (fanScale_pos k).ne'
  exact Prod.ext (mul_left_cancel₀ hs h1) (mul_left_cancel₀ hs h3)

/-! ## The loop fan at every scale -/

/-- The arcs of the loop fan at every scale: the tent `γ_n` of the loop fan (`loopArc n`, from
`p_n = (ε_n, 0)` through `(0, 1 + ε_n)` to `q_n = (−ε_n, 0)`) in level `k`'s plane, scaled by
`2⁻ᵏ`. -/
noncomputable def scaledFanArc (i : ℕ × ℕ) (t : ℝ) : ℝ × ℝ × ℝ := levelEmbed i.1 (loopArc i.2 t)

/-- **The loop fan at every scale**, a subspace of `ℝ³`: `a = (0, 0, 0)` and the arcs. -/
def scaledFanSet : Set (ℝ × ℝ × ℝ) :=
  insert ((0 : ℝ), (0 : ℝ), (0 : ℝ)) (⋃ i, range (scaledFanArc i))

/-- The arcs, as maps into the carrier. -/
noncomputable def scaledFanγ (i : ℕ × ℕ) (t : ℝ) : scaledFanSet :=
  ⟨scaledFanArc i t, mem_insert_of_mem _ (mem_iUnion.2 ⟨i, mem_range_self t⟩)⟩

/-- The point `a = (0, 0, 0)`, on no arc. -/
def scaledFanA : scaledFanSet := ⟨((0 : ℝ), (0 : ℝ), (0 : ℝ)), mem_insert _ _⟩

/-- **The causality of the loop fan at every scale**: `≤_U` along the oriented arcs inside `U`,
`≪` empty. -/
noncomputable def scaledFan : Causality scaledFanSet := arcCausality scaledFanγ

theorem continuous_scaledFanγ (i : ℕ × ℕ) : Continuous (scaledFanγ i) :=
  ((continuous_levelEmbed i.1).comp (continuous_loopArc i.2)).subtype_mk _

theorem scaledFanγ_val (i : ℕ × ℕ) (t : ℝ) :
    (scaledFanγ i t).val = levelEmbed i.1 (loopArc i.2 t) :=
  rfl

/-- Level `k` lies in the vertical plane `Y = ε_k X` through `a`. -/
theorem scaledFanγ_plane (k n : ℕ) (t : ℝ) :
    (scaledFanγ (k, n) t).val.2.1 = combEps k * (scaledFanγ (k, n) t).val.1 := by
  rw [scaledFanγ_val]
  simp only [levelEmbed]
  ring

/-- On the vertical through `a` a tent has its top only, at height `1 + ε_n`. -/
theorem loopArc_snd_of_fst_eq_zero {n : ℕ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (h : (loopArc n t).1 = 0) : (loopArc n t).2 = 1 + combEps n := by
  obtain rfl := eq_half_of_loopγ_fst ht h
  exact congrArg Prod.snd (loopPeak_val n)

/-- **Two levels meet nowhere**: off the vertical through `a` their planes differ (the slopes
`ε_k` are distinct); on it an arc has its top only, and the tops of level `k` have heights in
`(2⁻ᵏ, 2¹⁻ᵏ]`, disjoint intervals. -/
theorem scaledFanArc_level_eq {k k' n m : ℕ} {s s' : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hs' : s' ∈ Icc (0 : ℝ) 1) (h : scaledFanArc (k, n) s = scaledFanArc (k', m) s') :
    k = k' := by
  simp only [scaledFanArc, levelEmbed, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hsk := fanScale_pos k
  have hsk' := fanScale_pos k'
  by_cases hx : (loopArc n s).1 = 0
  · have hx' : (loopArc m s').1 = 0 := by
      rw [hx, mul_zero] at h1
      exact (mul_eq_zero.1 h1.symm).resolve_left hsk'.ne'
    rw [loopArc_snd_of_fst_eq_zero hs hx, loopArc_snd_of_fst_eq_zero hs' hx'] at h3
    have hn := combEps_pos n
    have hm := combEps_pos m
    have hn1 := combEps_le_one n
    have hm1 := combEps_le_one m
    rcases lt_trichotomy k k' with hlt | heq | hgt
    · have := fanScale_two_mul_le hlt
      nlinarith [mul_pos hsk hn, mul_le_mul_of_nonneg_left hm1 hsk'.le]
    · exact heq
    · have := fanScale_two_mul_le hgt
      nlinarith [mul_pos hsk' hm, mul_le_mul_of_nonneg_left hn1 hsk.le]
  · have hne : fanScale k * (loopArc n s).1 ≠ 0 := mul_ne_zero hsk.ne' hx
    have e : (combEps k - combEps k') * (fanScale k * (loopArc n s).1) = 0 := by
      have h2' : fanScale k * combEps k * (loopArc n s).1 =
          combEps k' * (fanScale k * (loopArc n s).1) := by
        rw [h1, h2]; ring
      linear_combination h2'
    exact combEps_strictAnti.injective (sub_eq_zero.1 ((mul_eq_zero.1 e).resolve_right hne))

/-- **The arcs of the loop fan at every scale are coherent**: two levels meet nowhere
(`scaledFanArc_level_eq`), and within a level `levelEmbed k` is injective, so the loop fan's
coherence (`loopγ_coherent`) applies. -/
theorem scaledFanγ_coherent : ArcCoherent scaledFanγ := by
  rintro ⟨k, n⟩ ⟨k', m⟩ s s' hs hs' h
  have h' : scaledFanArc (k, n) s = scaledFanArc (k', m) s' := congrArg Subtype.val h
  obtain rfl := scaledFanArc_level_eq hs hs' h'
  have hl : loopArc n s = loopArc m s' := levelEmbed_injective k h'
  obtain ⟨e, hagree⟩ := loopγ_coherent n m s s' hs hs' (Subtype.ext hl)
  refine ⟨e, fun r hr => Subtype.ext ?_⟩
  show levelEmbed k (loopArc n r) = levelEmbed k (loopArc m r)
  rw [show loopArc n r = loopArc m r from congrArg Subtype.val (hagree r hr)]

/-- `≤_U` of the loop fan at every scale, as the planner states it: `x = y ∈ U`, or `y` follows
`x` along one arc whose piece between them lies in `U`. -/
theorem scaledFan_le_iff {U : Opens scaledFanSet} {x y : scaledFanSet} :
    scaledFan.le U x y ↔ (x ∈ U ∧ x = y) ∨ arcStep scaledFanγ U x y :=
  scaledFanγ_coherent.le_iff

/-! ## Feet, tops, and the size of a level -/

/-- The start `2⁻ᵏ (ε_n, ε_k ε_n, 0)` of the arc `(k, n)`. -/
theorem scaledFanP_val (k n : ℕ) :
    (scaledFanγ (k, n) 0).val =
      (fanScale k * combEps n, fanScale k * combEps k * combEps n, 0) := by
  rw [scaledFanγ_val, show loopArc n 0 = (combEps n, 0) from loopP_val n]
  simp [levelEmbed]

/-- The end `2⁻ᵏ (−ε_n, −ε_k ε_n, 0)` of the arc `(k, n)`. -/
theorem scaledFanQ_val (k n : ℕ) :
    (scaledFanγ (k, n) 1).val =
      (fanScale k * -combEps n, fanScale k * combEps k * -combEps n, 0) := by
  rw [scaledFanγ_val, show loopArc n 1 = (-combEps n, 0) from loopQ_val n]
  simp [levelEmbed]

/-- The top `(0, 0, 2⁻ᵏ (1 + ε_n))` of the arc `(k, n)`, on the vertical through `a`. -/
theorem scaledFanPeak_val (k n : ℕ) :
    (scaledFanγ (k, n) (1 / 2)).val = (0, 0, fanScale k * (1 + combEps n)) := by
  rw [scaledFanγ_val, show loopArc n (1 / 2) = (0, 1 + combEps n) from loopPeak_val n]
  simp [levelEmbed]

theorem scaledFanA_val : scaledFanA.val = ((0 : ℝ), (0 : ℝ), (0 : ℝ)) := rfl

/-- The starts of level `k` tend to `a`. -/
theorem tendsto_scaledFanP (k : ℕ) :
    Tendsto (fun n => scaledFanγ (k, n) 0) atTop (𝓝 scaledFanA) := by
  rw [tendsto_subtype_rng, scaledFanA_val]
  simp only [scaledFanP_val]
  have h1 : Tendsto (fun n => fanScale k * combEps n) atTop (𝓝 0) := by
    simpa using tendsto_combEps.const_mul (fanScale k)
  have h2 : Tendsto (fun n => fanScale k * combEps k * combEps n) atTop (𝓝 0) := by
    simpa using tendsto_combEps.const_mul (fanScale k * combEps k)
  exact h1.prodMk_nhds (h2.prodMk_nhds tendsto_const_nhds)

/-- The ends of level `k` tend to `a`. -/
theorem tendsto_scaledFanQ (k : ℕ) :
    Tendsto (fun n => scaledFanγ (k, n) 1) atTop (𝓝 scaledFanA) := by
  rw [tendsto_subtype_rng, scaledFanA_val]
  simp only [scaledFanQ_val]
  have h : Tendsto (fun n => -combEps n) atTop (𝓝 0) := by simpa using tendsto_combEps.neg
  have h1 : Tendsto (fun n => fanScale k * -combEps n) atTop (𝓝 0) := by
    simpa using h.const_mul (fanScale k)
  have h2 : Tendsto (fun n => fanScale k * combEps k * -combEps n) atTop (𝓝 0) := by
    simpa using h.const_mul (fanScale k * combEps k)
  exact h1.prodMk_nhds (h2.prodMk_nhds tendsto_const_nhds)

theorem abs_loopArc_fst_le {n : ℕ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |(loopArc n t).1| ≤ 1 := by
  rw [loopArc_of_mem ht, abs_mul, abs_of_pos (combEps_pos n)]
  have h1 : |1 - 2 * t| ≤ 1 := abs_le.2 ⟨by linarith [ht.2], by linarith [ht.1]⟩
  calc combEps n * |1 - 2 * t| ≤ 1 * 1 :=
        mul_le_mul (combEps_le_one n) h1 (abs_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem loopArc_snd_mem {n : ℕ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ (loopArc n t).2 ∧ (loopArc n t).2 ≤ 2 := by
  have e : loopArc n t = (loopγ n t).val := rfl
  rw [e, loopγ_val_of_mem ht]
  dsimp only
  have hε := combEps_pos n
  have hε1 := combEps_le_one n
  have h1 : |1 - 2 * t| ≤ 1 := abs_le.2 ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hmul := combEps_mul n
  have h0 : 0 ≤ |1 - 2 * t| := abs_nonneg _
  have hn : (0 : ℝ) ≤ n := n.cast_nonneg
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ ((n : ℝ) + 2) * combEps n)]
  · nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ ((n : ℝ) + 2)) (mul_nonneg hε.le h0)]

/-- **The size of a level**: along a level-`k` arc, `|X| ≤ 2⁻ᵏ`, `|Y| ≤ 2⁻ᵏ` and
`0 ≤ Z ≤ 2 · 2⁻ᵏ`. -/
theorem scaledFanγ_coord_le {k n : ℕ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |(scaledFanγ (k, n) t).val.1| ≤ fanScale k ∧ |(scaledFanγ (k, n) t).val.2.1| ≤ fanScale k ∧
      0 ≤ (scaledFanγ (k, n) t).val.2.2 ∧ (scaledFanγ (k, n) t).val.2.2 ≤ 2 * fanScale k := by
  have hs := fanScale_pos k
  have hx := abs_loopArc_fst_le (n := n) ht
  obtain ⟨hy0, hy2⟩ := loopArc_snd_mem (n := n) ht
  have hc := combEps_pos k
  have hc1 := combEps_le_one k
  rw [scaledFanγ_val]
  simp only [levelEmbed]
  refine ⟨?_, ?_, mul_nonneg hs.le hy0, by nlinarith⟩
  · rw [abs_mul, abs_of_pos hs]; nlinarith
  · rw [abs_mul, abs_mul, abs_of_pos hs, abs_of_pos hc]
    nlinarith [mul_le_mul hc1 hx (abs_nonneg _) zero_le_one]

/-! ## Not locally strongly causal at `a` -/

/-- **No open set holding `a` is strongly causal as a spacetime.** With `B(a, r) ⊆ W` take a
level `k` with `2 · 2⁻ᵏ < r`: its arcs lie in `W`. For `U = {Z < 2⁻ᵏ}`, a neighbourhood `V ⊆ U` of
`a` holds both feet of some loop of level `k`, and `J_W` of the two feet holds the loop's top, at
height `2⁻ᵏ (1 + ε_n) > 2⁻ᵏ`, outside `U`. -/
theorem scaledFan_not_stronglyCausalOn {W : Opens scaledFanSet} (ha : scaledFanA ∈ W) :
    ¬ scaledFan.StronglyCausalOn W := by
  intro hW
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (W.isOpen.mem_nhds ha)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (half_pos hr) (by norm_num : (2 : ℝ)⁻¹ < 1)
  have hk' : 2 * fanScale k < r := by unfold fanScale; linarith
  have hU : {z : scaledFanSet | z.val.2.2 < fanScale k} ∈ 𝓝 scaledFanA :=
    (isOpen_lt (continuous_snd.comp (continuous_snd.comp continuous_subtype_val))
      continuous_const).mem_nhds (show (0 : ℝ) < fanScale k from fanScale_pos k)
  obtain ⟨V, hV, hVU, hconv⟩ := hW scaledFanA ha _ hU
  obtain ⟨n, hpn, hqn⟩ :=
    (((tendsto_scaledFanP k).eventually hV).and ((tendsto_scaledFanQ k).eventually hV)).exists
  have hin : ∀ t ∈ Icc (0 : ℝ) 1, scaledFanγ (k, n) t ∈ W := fun t ht => by
    -- the sup distance of `ℝ³` to `a` is at most `2 · 2⁻ᵏ < r`
    obtain ⟨hX, hY, hZ0, hZ⟩ := scaledFanγ_coord_le (n := n) ht
    refine hball (Metric.mem_ball.2 ?_)
    rw [Subtype.dist_eq, scaledFanA_val, Prod.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq,
      Real.dist_eq]
    simp only [sub_zero]
    rw [abs_of_nonneg hZ0]
    have := fanScale_pos k
    exact max_lt (by linarith) (max_lt (by linarith) (by linarith))
  have hpeak : scaledFanγ (k, n) (1 / 2) ∈
      scaledFan.diamond W (scaledFanγ (k, n) 0) (scaledFanγ (k, n) 1) :=
    Causality.mem_diamond.2
      ⟨arcStep.le ⟨(k, n), 0, 1 / 2, le_rfl, by norm_num, by norm_num, rfl, rfl,
        fun t ht => hin t ⟨ht.1, ht.2.trans (by norm_num)⟩⟩,
      arcStep.le ⟨(k, n), 1 / 2, 1, by norm_num, by norm_num, le_rfl, rfl, rfl,
        fun t ht => hin t ⟨by linarith [ht.1], ht.2⟩⟩⟩
  have h1 : (scaledFanγ (k, n) (1 / 2)).val.2.2 < fanScale k := hVU (hconv.2 _ hpn _ hqn hpeak)
  rw [scaledFanPeak_val] at h1
  dsimp only at h1
  nlinarith [mul_pos (fanScale_pos k) (combEps_pos n)]

/-- **The loop fan at every scale is not locally strongly causal** (at `a`). -/
theorem scaledFan_not_locallyStronglyCausal : ¬ scaledFan.LocallyStronglyCausal := fun h =>
  let ⟨_, haW, hW⟩ := h scaledFanA
  scaledFan_not_stronglyCausalOn haW hW

/-! ## A time function -/

/-- **A time function** (the ladder's `time_function`): `−X`, continuous and strictly increasing
along each arc (`X = 2⁻ᵏ ε_n (1 − 2t)` along the arc `(k, n)`). -/
theorem scaledFan_hasTimeFunction : scaledFan.HasTimeFunction := by
  refine scaledFanγ_coherent.hasTimeFunction (T := fun z => -z.val.1)
    (continuous_fst.comp continuous_subtype_val).neg fun i s hs t ht hst => ?_
  show -(levelEmbed i.1 (loopArc i.2 s)).1 < -(levelEmbed i.1 (loopArc i.2 t)).1
  simp only [levelEmbed]
  rw [loopArc_of_mem hs, loopArc_of_mem ht]
  dsimp only
  nlinarith [mul_pos (mul_pos (fanScale_pos i.1) (combEps_pos i.2)) (sub_pos.2 hst)]

/-! ## Causally open in no form -/

/-- The points of level `0` lie in the plane `Y = X` (slope `ε₀ = 1`, scale `1`). -/
theorem scaledFanγ_zero_snd (m : ℕ) (t : ℝ) :
    (scaledFanγ (0, m) t).val.2.1 = (scaledFanγ (0, m) t).val.1 := by
  rw [scaledFanγ_val]
  simp only [levelEmbed, fanScale_zero, combEps_zero, one_mul]

/-- The points with `Y < X`: an open set missing level `0` and `a`. -/
def scaledFanBelow : Opens scaledFanSet :=
  ⟨{z | z.val.2.1 < z.val.1},
    isOpen_lt (continuous_fst.comp (continuous_snd.comp continuous_subtype_val))
      (continuous_fst.comp continuous_subtype_val)⟩

/-- **No open set holding the top `(0, 0, 1)` of the tent `(1, 0)` is causally open in the future
as a spacetime.** That top is the limit of the tops of level `0`. For `V = W ∩ {Y < X}`, `J⁺_W(V)`
holds it (along its own tent, from a point of its rising leg in `W`, where `Y = X/2 < X`) and no
point of level `0`, which lies in `Y = X` and is reached along level `0` only. -/
theorem scaledFan_not_causallyOpenFutureOn {W : Opens scaledFanSet}
    (hy : scaledFanγ (1, 0) (1 / 2) ∈ W) : ¬ scaledFan.CausallyOpenFutureOn W := by
  intro hW
  have hJ := hW W (W ⊓ scaledFanBelow) le_rfl inf_le_left
  obtain ⟨l, u, ⟨hl, hu⟩, hlu⟩ := mem_nhds_iff_exists_Ioo_subset.1
    ((continuous_scaledFanγ (1, 0)).continuousAt.preimage_mem_nhds (W.isOpen.mem_nhds hy))
  set s₀ := max ((l + 1 / 2) / 2) (1 / 4) with hs₀
  have hs₀l : l < s₀ := lt_max_of_lt_left (by linarith)
  have hs₀h : s₀ < 1 / 2 := max_lt (by linarith) (by norm_num)
  have hs₀0 : 1 / 4 ≤ s₀ := le_max_right _ _
  have hpiece : ∀ r ∈ Icc s₀ (1 / 2), scaledFanγ (1, 0) r ∈ W := fun r hr =>
    hlu ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hbelow : scaledFanγ (1, 0) s₀ ∈ W ⊓ scaledFanBelow := by
    refine ⟨hpiece s₀ ⟨le_rfl, hs₀h.le⟩, ?_⟩
    show (scaledFanγ (1, 0) s₀).val.2.1 < (scaledFanγ (1, 0) s₀).val.1
    rw [scaledFanγ_val]
    simp only [levelEmbed, fanScale_one, combEps_one]
    rw [loopArc_of_mem ⟨by linarith, by linarith⟩, combEps_zero]
    dsimp only
    nlinarith
  have hyJ : scaledFanγ (1, 0) (1 / 2) ∈ scaledFan.Jplus W (W ⊓ scaledFanBelow) :=
    ⟨_, hbelow, arcStep.le ⟨(1, 0), s₀, 1 / 2, by linarith, hs₀h.le, by norm_num, rfl, rfl,
      hpiece⟩⟩
  have htend : Tendsto (fun m => scaledFanγ (0, m) (1 / 2)) atTop
      (𝓝 (scaledFanγ (1, 0) (1 / 2))) := by
    rw [tendsto_subtype_rng]
    simp only [scaledFanPeak_val, fanScale_zero, fanScale_one, combEps_zero, one_mul]
    refine tendsto_const_nhds.prodMk_nhds (tendsto_const_nhds.prodMk_nhds ?_)
    have : (1 / 2 : ℝ) * (1 + 1) = 1 + 0 := by norm_num
    rw [this]
    exact tendsto_const_nhds.add tendsto_combEps
  obtain ⟨m, x, hxV, hxle⟩ := (htend.eventually (hJ.mem_nhds hyJ)).exists
  have hxdiag : ¬ x.val.2.1 < x.val.1 := by
    rcases scaledFanγ_coherent.le_iff.1 hxle with ⟨-, rfl⟩ |
        ⟨j, s', t', hs', hst', ht', rfl, hz, -⟩
    · rw [scaledFanγ_zero_snd]; exact lt_irrefl _
    · obtain ⟨-, hagree⟩ := scaledFanγ_coherent j (0, m) t' (1 / 2) ⟨hs'.trans hst', ht'⟩
        ⟨by norm_num, by norm_num⟩ hz
      rw [hagree s' ⟨hs', hst'⟩, scaledFanγ_zero_snd]; exact lt_irrefl _
  exact hxdiag hxV.2

/-- **Not locally causally open in the future** (at the top `(0, 0, 1)` of the tent `(1, 0)`). -/
theorem scaledFan_not_locallyCausallyOpenFuture : ¬ scaledFan.LocallyCausallyOpenFuture :=
  fun h => let ⟨_, hyW, hW⟩ := h (scaledFanγ (1, 0) (1 / 2))
    scaledFan_not_causallyOpenFutureOn hyW hW

/-! ## The separation -/

/-- **The loop fan at every scale, full form** (either reading: absolutely minimal on every open
set for every cover). Hausdorff, second countable, absolutely minimal (and on every open set),
causally arc-connected, push-up, locally push-up, causal, causally compact, globally hyperbolic, a
time function, curves extend, future one-connected (on every open set, `≪` being empty); not
locally strongly causal, and no open set holding `a` strongly causal as a spacetime; strongly
causal in neither form, not tarentin (`globally_hyperbolic ∧ tarentin ⇒ strongly_causal ⇒
locally_strongly_causal` read backwards, T2), no chronal neighbours, not causally plain, no
chronal neighbour at some point; causally open in no form. It decides all 21 causality nodes. -/
theorem scaledFan_separates :
    T2Space scaledFanSet ∧ SecondCountableTopology scaledFanSet ∧
      scaledFan.AbsolutelyMinimal ∧ (∀ W : Opens scaledFanSet, scaledFan.AbsolutelyMinimalOn W) ∧
      scaledFan.CausallyArcConnected ∧ scaledFan.PushUp ∧ scaledFan.LocallyPushUp ∧
      scaledFan.IsCausal ∧ scaledFan.CausallyCompact ∧ scaledFan.GloballyHyperbolic ∧
      scaledFan.HasTimeFunction ∧ scaledFan.CurvesExtend ∧
      scaledFan.FutureOneConnected ∧ (∀ W : Opens scaledFanSet, scaledFan.FutureOneConnectedOn W) ∧
      ¬ scaledFan.LocallyStronglyCausal ∧
      (∀ W : Opens scaledFanSet, scaledFanA ∈ W → ¬ scaledFan.StronglyCausalOn W) ∧
      ¬ scaledFan.StronglyCausal ∧ ¬ scaledFan.StronglyCausalOpen ∧ ¬ scaledFan.Tarentin ∧
      ¬ scaledFan.ChronalNeighbours ∧ ¬ scaledFan.CausallyPlain ∧
      ¬ scaledFan.HasChronalNeighbourEverywhere ∧
      ¬ scaledFan.CausallyOpenFuture ∧ ¬ scaledFan.CausallyOpen ∧
      ¬ scaledFan.LocallyCausallyOpenFuture ∧ ¬ scaledFan.LocallyCausallyOpen := by
  have hAC : scaledFan.CausallyArcConnected :=
    arcCausality_causallyArcConnected continuous_scaledFanγ
  have hAM : scaledFan.AbsolutelyMinimal := hAC.absolutelyMinimal
  have hPU : scaledFan.PushUp := arcCausality_pushUp
  have hGH : scaledFan.GloballyHyperbolic :=
    scaledFanγ_coherent.globallyHyperbolic continuous_scaledFanγ
  have hTF : scaledFan.HasTimeFunction := scaledFan_hasTimeFunction
  have hNLSC : ¬ scaledFan.LocallyStronglyCausal := scaledFan_not_locallyStronglyCausal
  have hNLCOF : ¬ scaledFan.LocallyCausallyOpenFuture := scaledFan_not_locallyCausallyOpenFuture
  have hlt : ∀ (U : Opens scaledFanSet) (x y : scaledFanSet), ¬ scaledFan.lt U x y :=
    fun _ _ _ h => h
  haveI : Nonempty scaledFanSet := ⟨scaledFanA⟩
  -- the ladder steps (`causal_ladder`): push_up ⇒ locally_push_up, globally_hyperbolic ⇒
  -- is_causal, causally_compact, time_function ⇒ curves_extend; read backwards,
  -- strongly_causal ⇒ locally_strongly_causal, strongly_causal_open ⇒ strongly_causal,
  -- globally_hyperbolic ∧ tarentin ⇒ strongly_causal (T2), causally_open_future ⇒
  -- locally_causally_open_future, causally_open ⇒ causally_open_future, locally_causally_open ⇒
  -- locally_causally_open_future
  exact ⟨inferInstance, inferInstance, hAM,
    fun W => arcCausality_absolutelyMinimalOn continuous_scaledFanγ W, hAC, hPU,
    by causal_ladder, by causal_ladder, by causal_ladder, hGH, hTF, by causal_ladder,
    Causality.futureOneConnectedOn_of_forall_not_lt (hlt ⊤),
    fun W => Causality.futureOneConnectedOn_of_forall_not_lt (hlt W), hNLSC,
    fun _ ha => scaledFan_not_stronglyCausalOn ha,
    fun _ => hNLSC (by causal_ladder), fun _ => hNLSC (by causal_ladder),
    fun _ => hNLSC (by causal_ladder), arcCausality_not_chronalNeighbours,
    Causality.not_causallyPlain_of_forall_not_lt (hlt ⊤),
    Causality.not_hasChronalNeighbourEverywhere_of_forall_not_lt (hlt ⊤),
    fun _ => hNLCOF (by causal_ladder), fun _ => hNLCOF (by causal_ladder), hNLCOF,
    fun _ => hNLCOF (by causal_ladder)⟩

/-- **`prop:GH_fortement_causal` is sharp in tarentin, even for local strong causality**: on a
Hausdorff, second countable space, a globally hyperbolic, causally arc-connected causality with a
time function need not be locally strongly causal (the loop fan at every scale). The loop fan
alone is locally strongly causal (`Causal.loopFan_locallyStronglyCausal`): the failure needs loops
at every scale. -/
theorem not_locallyStronglyCausal_of_globallyHyperbolic_bare :
    ¬ ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
      (C : Causality M), C.GloballyHyperbolic → C.HasTimeFunction → C.CausallyArcConnected →
        C.LocallyStronglyCausal := fun h =>
  scaledFan_not_locallyStronglyCausal
    (h scaledFanSet scaledFan (scaledFanγ_coherent.globallyHyperbolic continuous_scaledFanγ)
      scaledFan_hasTimeFunction (arcCausality_causallyArcConnected continuous_scaledFanγ))

end Causal
