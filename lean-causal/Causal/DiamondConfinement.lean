import Causal.TimelikeHomotopy

/-!
# Homotopy confinement and diamond identification in ETT (Sbierski 1507.00601, Thm 3.1 Step 3)

Programme target `T-abs-diamond-confinement` (`programme/roadmap.toml`; layer 1, stream abstract,
ETT-layer imports only, no model, no metric). Source: J. Sbierski, *The C⁰-inextendibility of the
Schwarzschild spacetime and the spacelike diameter in Lorentzian geometry*, arXiv 1507.00601 v2,
`papers/sbierski-schwarzschild/legacy/labeled/InexSchwarzschild2.tex`. **No label is marked**:
the rows concerned (`schwthm:MinkInex`, `schwthm:Exterior`, `schwthm:Inex`, `schwthm:MainThm`)
are statements about `C⁰` Lorentzian manifolds, of which this file gives the causal step (3) of
the binder's scheme for any causality (layer 1).

* (i) **Confinement** — `schwthm:MinkInex` Step 3 (`:619–621`), `schwthm:Inex` (`:1623`), §1
  (`:158`): `ChronalHomotopyOn.mapsTo_of_closure_subset` (a chronal homotopy with fixed endpoints
  `x, y` in any open `W` whose first curve lies in the open `Ũ` stays in `Ũ` once
  `closure (I⁺(x, Ũ) ∩ I⁻(y, Ũ)) ⊆ Ũ`); `.inf_of_closure_subset` (it is a homotopy of `W ⊓ Ũ`);
  `.mem_Iplus_inter_Iminus_of_closure_subset` (the interior points of its curves lie in
  `I⁺(x, W ⊓ Ũ) ∩ I⁻(y, W ⊓ Ũ)`); `.mapsTo_of_closure_subset_of_lt` (Step 3 as printed, the
  diamond up to `y'` with `y ≪_Ũ y'`).
* (ii) **Identification**, (1.2)'s `⊇` (`:153–158`), the `⊇` of `schwthm:Inex`'s
  (FuturePastPreserving) (`:1623`): `FutureOneConnectedOn.chronalCurveOn_inf_of_closure_subset`
  (every chronal curve of a future one-connected `W` from `x` to `y` lies in `Ũ`; no
  arc-connectedness);
  `Iplus_inter_Iminus_subset_inf_of_futureOneConnectedOn`,
  `Iplus_inter_Iminus_eq_inf_of_futureOneConnectedOn` (`I⁺(x, W) ∩ I⁻(y, W) =
  I⁺(x, W ⊓ Ũ) ∩ I⁻(y, W ⊓ Ũ)`), `Iplus_inter_Iminus_subset_of_futureOneConnectedOn`
  (`⊆ I⁺(x, Ũ) ∩ I⁻(y, Ũ)`, the target's form), for `W` causally arc-connected and future
  one-connected; `Iplus_inter_Iminus_subset_of_futureOneConnectedOn_of_lt` ((1.2) as printed,
  through `closure_Iplus_inter_Iminus_subset_of_lt`); `Iplus_inter_Iminus_eq_of_futureOneConnected`
  (`W = M`).
* (iii) **The localisation** `StronglyCausalOn W` (`W` strongly causal as a spacetime) and
  `LocallyStronglyCausal`; `StronglyCausal.locallyStronglyCausal`, `stronglyCausalOn_top`,
  `StronglyCausalOn.mono`, `dual_stronglyCausalOn`, `dual_locallyStronglyCausal`,
  `locallyStronglyCausal_iff_nhds`; the closure hypothesis of (i) near every point:
  `StronglyCausalOn.exists_closure_subset` (`[RegularSpace M]`),
  `StronglyCausalOn.exists_isCompact_closure`, `LocallyStronglyCausal.exists_isCompact_closure`
  (`[LocallyCompactSpace M] [R1Space M]`, so every locally compact Hausdorff `M`); the assembly
  `LocallyStronglyCausal.exists_diamond_identification`. Sufficient, not necessary:
  `exists_confining_not_locallyStronglyCausal`.
* Witnesses (kb/0011), the timelike line: `timelikeLine_confinement`,
  `timelikeLine_diamond_identification`, `timelikeLine_locallyStronglyCausal`,
  `timelikeLine_exists_isCompact_closure`.

> We claim that ι ∘ Γ actually maps into Ũ. This is seen as follows: Let I ⊂ [0,1] denote the
> set of all t ∈ [0,1] such that ι ∘ Γ(t, ·) is a timelike curve in Ũ. Clearly, I is non-empty,
> since ι ∘ Γ(0, ·) = γ̃|[−s₀,−s₁](·) (modulo parametrisation). Moreover, the openness of Ũ
> implies the openness of I, and since we have chosen s₀ ∈ (0, ε) such that the closure of
> I⁻(γ̃(0), Ũ) ∩ I⁺(γ̃(−s₀), Ũ) in M̃ is contained in Ũ, it also follows that I is closed in
> [0,1]. This yields I = [0,1] and hence proves the claim. (`InexSchwarzschild2.tex:621`)

> Ideally, we would like to have the following identification for all s₀ < s < 0:
> I⁺(γ̃(s₀), Ũ) ∩ I⁻(γ̃(s), Ũ) = I⁺(γ̃(s₀), M_max) ∩ I⁻(γ̃(s), M_max). (1.2) […] Here, however,
> we exploit that the exterior of the Schwarzschild black hole is future one-connected […]. Since
> the closure of I⁺(γ̃(s₀), Ũ) ∩ I⁻(γ̃(0), Ũ) in M̃ is contained in Ũ, a homotopy as above cannot
> escape I⁺(γ̃(s₀), Ũ) ∩ I⁻(γ̃(0), Ũ). This yields the relation "⊇" in (1.2).
> (`InexSchwarzschild2.tex:153–158`)

> We need to show that (ι ∘ σ)(·) = (ι ∘ Γ)(1, ·) maps into Õ. We argue by continuity, i.e., we
> show that the interval J := {t ∈ [0,1] | ι ∘ Γ(t, [y₀⁻, s]) ⊆ Õ} is non-empty, open and closed
> in [0,1]. […] the closedness follows since I⁻(γ̃(s), Õ) ∩ I⁺(γ̃(y₀⁻), Õ) is precompact in Õ,
> i.e., in particular its closure in M̃ is contained in Õ. (`InexSchwarzschild2.tex:1625`)

> It now follows from (3.2) that we can choose s₀ ∈ (0, ε) such that the closure of
> I⁻(0, (−ε, ε)^{d+1}) ∩ I⁺((−s₀, 0, …, 0), (−ε, ε)^{d+1}) in (−ε, ε)^{d+1} is compact.
> (`InexSchwarzschild2.tex:528–532`)
-/

/-!
## The reading

* **Timelike curves are future chronal curves** (`Causal.Curves`, DEC-6), over `[0, 1]`, and a
  timelike homotopy with fixed endpoints is `Causality.ChronalHomotopyOn`
  (`Causal.TimelikeHomotopy`, Def 2.13). Thm 4.11's homotopy over `[0, 1] × [y₀⁻, s]` is the
  `[0, 1]` notion after an affine change of the curve parameter (that module's SCOPE).
* **Sbierski's `M̃` is `M`, his `ι(N)` the open `W`, his chart domain `Ũ` (or `Õ`) any open set
  of `M`** (kb/0001, Rem 2.3 `:248`): `I^±(·, Ũ)` are the relations of the open `Ũ`, not of `M`.
  "A timelike curve in `Ũ`" is a chronal curve of `Ũ`; a chronal curve of `W` with values in `Ũ`
  is one of `W ⊓ Ũ` (`CurveOn.restrict`), hence of `Ũ` (`CurveOn.mono_opens`). The conclusions
  are stated for `W ⊓ Ũ`, which is stronger than for `Ũ`.
* **"For all x, y near every point"** in (iii): there is a neighbourhood `V` of the point with the
  closure hypothesis for all `x, y ∈ V`. The open `Ũ` can be taken inside any given neighbourhood
  of the point.
* **"Strongly causal as a spacetime"** for an open `W` is `def:strongly_causal_spacetime`
  (`Causality.StronglyCausal`, DEC-7: the convex neighbourhood need not be open) with the
  relations of `W`: `StronglyCausalOn W` asks, at every `p ∈ W`, arbitrarily small neighbourhoods
  causally convex in `W` (`CausallyConvexIn V W`). It is hereditary (`StronglyCausalOn.mono`), so
  `LocallyStronglyCausal` gives such opens inside every neighbourhood
  (`locallyStronglyCausal_iff_nhds`).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| (i): `M̃` a `C⁰` Lorentzian manifold, `Γ` a timelike homotopy with fixed endpoints in `ι(M)` | ⚠ weakened: any causality on a topological space, `Γ` a chronal homotopy of any open `W` (the `C0` layer 3 compares the curves) |
| (i): `Γ(0, ·)` in `Ũ`, `Ũ` open | ✓ carried |
| (i): closure in `M̃` of `I⁺(x, Ũ) ∩ I⁻(y, Ũ)` in `Ũ` | ✓ carried, with the homotopy's own endpoints `x, y`; Step 3's printed form, the diamond up to `y' = γ̃(0)` with `y ≪_Ũ y'`, is a corollary (`mapsTo_of_closure_subset_of_lt`) |
| (i): compactness of `[0, 1]`, joint continuity of `Γ` | ✓ used (the openness of `I`, `:621`, is the tube lemma); no separation axiom on `M` |
| (ii): `ι(M)` future one-connected | ✓ carried: `FutureOneConnectedOn W` |
| (ii): `≪` of `ι(M)` realised by timelike curves (Def 2.2) | ✓ carried: `CausallyArcConnectedOn W`; not needed in the curve form `FutureOneConnectedOn.chronalCurveOn_inf_of_closure_subset` |
| (iii): the chart diamonds precompact (the upper cone estimates (3.2), `UpperBoundEstimatesOnPastAndFuture`, `C⁰`; the two-sided sandwich is Thm 4.11's, `:1585`) | ⚠ replaced by the localisation `StronglyCausalOn W` of a neighbourhood, from which it follows; that Lemma 2.4's chart is strongly causal as a spacetime is the `C0` layer 3 |
| (iii): `M̃` Hausdorff and locally compact (a manifold) | ⚠ weakened: `[RegularSpace M]` for `closure ⊆ Ũ`; `[LocallyCompactSpace M] [R1Space M]` for compact closures (`T2Space` gives `R1Space`) |

## SCOPE (disclosed)

* Nothing is marked: the Sbierski rows are about `C⁰` metrics; their layer 3 (that a `C⁰` metric's
  curve relation is a causality whose chronal curves contain the timelike curves, and that Lemma
  2.4's chart is strongly causal as a spacetime) is `T-loc-c0-metric-causality`'s and
  `T-loc-c0-chart-diameter`'s. The metric steps (timelike and spacelike diameters) have no
  layer-1 statement.
* `LocallyStronglyCausal` is the definition proposed for the ladder node `locally_strongly_causal`
  (`T-lad-c0-extension-nodes`); the keeper chooses its form. No space locally strongly causal and
  not strongly causal is in this file: the candidates (the loop fan of `Causal.GHWithoutTarentin`,
  the flat time cylinder of `Causal.Model.FlatTimeCylinder`) live in modules this one must not
  import (the first reaches `Causal.Ladder.Rules`, kb/0221; the second is a model).
* `LocallyStronglyCausal` is a sufficient condition for the confinement hypothesis of (i), not a
  necessary one: on `ℝ`, the causality with `≤_U` relating any two points of `U` and `≪` empty
  has empty chronological diamonds and is not locally strongly causal
  (`exists_confining_not_locallyStronglyCausal`; not absolutely minimal, so a remark on the
  hypothesis, not a ladder separation). The weakest localisation for (i)–(ii) is the closure
  property itself, which `LocallyStronglyCausal.exists_isCompact_closure` states.
* `CurveOn.exists_concat_mid` (the concatenation passes through the junction at `1 / 2`) belongs
  beside `CurveOn.exists_concat` in `Causal.ArcConnected`; it is here because that module is
  strict upstream.
* The assembly of steps (1)–(3) (the leaving curve, its chart, the identification) is
  `T-abs-c0-extension-skeleton`'s.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Function

universe u

variable {M : Type u} [TopologicalSpace M]

/-- Two curves over `[0, 1]` with a common endpoint concatenate into a curve over `[0, 1]`
passing through the junction at `1 / 2` (`CurveOn.exists_concat`, with the midpoint). -/
theorem CurveOn.exists_concat_mid {r : Opens M → M → M → Prop} {W : Opens M} {c₁ c₂ : ℝ → M}
    (hr : IsRelFamily r) (h₁ : CurveOn r W c₁ 0 1) (h₂ : CurveOn r W c₂ 0 1) (h : c₁ 1 = c₂ 0) :
    ∃ c, CurveOn r W c 0 1 ∧ c 0 = c₁ 0 ∧ c 1 = c₂ 1 ∧ c (1 / 2) = c₁ 1 := by
  have h₂' : CurveOn r W (fun t => c₂ (1 * t + (-1))) 1 2 :=
    CurveOn.comp_affine one_pos (by norm_num; exact h₂)
  have hglue := CurveOn.concat hr h₁ h₂' zero_le_one one_le_two (by simpa using h)
  have hfin := CurveOn.comp_affine (k := 2) (m := 0) (a' := 0) (b' := 1) two_pos
    (by norm_num; exact hglue)
  refine ⟨_, hfin, ?_, ?_, ?_⟩
  · simp
  · norm_num
  · norm_num

namespace Causality

variable {C : Causality M} {W W' Ũ : Opens M} {Γ : ℝ → ℝ → M} {γ γ₀ γ₁ σ : ℝ → M} {x y y' : M}

/-! ### (i) A homotopy cannot escape a diamond whose closure is in `Ũ` -/

/-- **Sbierski Thm 3.1 Step 3** (`:619–621`; Thm 4.11 at `:1623`): a chronal homotopy with fixed
endpoints `x, y` in the open `W`, whose first curve lies in the open `Ũ`, stays in `Ũ` once the
closure of `I⁺(x, Ũ) ∩ I⁻(y, Ũ)` lies in `Ũ`. The parameters whose curve lies in `Ũ` form an open
set (the tube lemma, `[0, 1]` compact) containing `0`, whose closure in `[0, 1]` it contains (a
limit curve has its interior points in the closure of the diamond); `[0, 1]` is connected. No
ladder property, no separation axiom. -/
theorem ChronalHomotopyOn.mapsTo_of_closure_subset (h : C.ChronalHomotopyOn W Γ γ₀ γ₁)
    (hx : γ₀ 0 = x) (hy : γ₀ 1 = y) (h₀ : MapsTo γ₀ (Icc 0 1) Ũ)
    (hcl : closure (C.Iplus Ũ {x} ∩ C.Iminus Ũ {y}) ⊆ Ũ) :
    MapsTo (uncurry Γ) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) Ũ := by
  -- the clamp `ℝ → [0, 1]`, which makes `Γ` continuous on `ℝ²`
  set cl : ℝ → ℝ := fun t => max 0 (min 1 t)
  have hcl_mem : ∀ t, cl t ∈ Icc (0 : ℝ) 1 := fun t =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hcl_eq : ∀ t ∈ Icc (0 : ℝ) 1, cl t = t := fun t ht => by
    simp only [cl, min_eq_right ht.2, max_eq_right ht.1]
  have hcl_cont : Continuous cl := continuous_const.max (continuous_const.min continuous_id)
  have hG : Continuous (fun q : ℝ × ℝ => Γ (cl q.1) (cl q.2)) :=
    h.continuousOn.comp_continuous ((hcl_cont.comp continuous_fst).prodMk
      (hcl_cont.comp continuous_snd)) (fun q => ⟨hcl_mem _, hcl_mem _⟩)
  -- a curve of the homotopy lying in `Ũ` has its interior points in the diamond
  have hslice : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (Γ t) (Icc 0 1) Ũ → ∀ s ∈ Ioo (0 : ℝ) 1,
      Γ t s ∈ C.Iplus Ũ {x} ∩ C.Iminus Ũ {y} := by
    intro t ht hmaps s hs
    have hc : C.ChronalCurveOn (W ⊓ Ũ) (Γ t) 0 1 :=
      CurveOn.restrict (h.chronalCurveOn t ht) le_rfl le_rfl inf_le_left
        (fun s hs => ⟨(h.chronalCurveOn t ht).mem s hs, hmaps hs⟩)
    have h1 := hc.lt_of_lt le_rfl hs.1 hs.2.le
    have h2 := hc.lt_of_lt hs.1.le hs.2 le_rfl
    rw [h.fix_zero t ht, hx] at h1
    rw [h.fix_one t ht, hy] at h2
    exact ⟨Precausality.mem_Iplus_singleton.2 (C.lt_mono inf_le_right h1),
      Precausality.mem_Iminus_singleton.2 (C.lt_mono inf_le_right h2)⟩
  -- the parameters whose curve lies in `Ũ`
  let S : Set ℝ := {t | MapsTo (Γ (cl t)) (Icc 0 1) Ũ}
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    have hev := isCompact_Icc.eventually_forall_of_forall_eventually (x₀ := t)
      (P := fun t' s => Γ (cl t') (cl s) ∈ Ũ) (fun s hs => by
        have hmem : Γ (cl t) (cl s) ∈ Ũ := by rw [hcl_eq s hs]; exact ht hs
        exact hG.continuousAt.preimage_mem_nhds (Ũ.isOpen.mem_nhds hmem))
    filter_upwards [hev] with t' ht' s hs
    have := ht' s hs
    rwa [hcl_eq s hs] at this
  have h0S : (0 : ℝ) ∈ S := by
    intro s hs
    show Γ (cl 0) s ∈ Ũ
    rw [hcl_eq 0 ⟨le_rfl, zero_le_one⟩, h.eqOn_zero hs]
    exact h₀ hs
  have hsub : Icc (0 : ℝ) 1 ⊆ S := by
    refine isPreconnected_Icc.subset_of_closure_inter_subset hSopen
      ⟨0, ⟨le_rfl, zero_le_one⟩, h0S⟩ ?_
    rintro t ⟨htc, htI⟩ s hs
    show Γ (cl t) s ∈ Ũ
    rw [hcl_eq t htI]
    rcases hs.1.eq_or_lt with h0 | h0
    · rw [← h0, h.fix_zero t htI]
      exact h₀ ⟨le_rfl, zero_le_one⟩
    rcases hs.2.eq_or_lt with h1 | h1
    · rw [h1, h.fix_one t htI]
      exact h₀ ⟨zero_le_one, le_rfl⟩
    have hcont : Continuous (fun t' => Γ (cl t') s) := by
      have := hG.comp (continuous_id.prodMk continuous_const : Continuous fun t' : ℝ => (t', s))
      simpa [comp_def, hcl_eq s hs] using this
    have hS : S ⊆ (fun t' => Γ (cl t') s) ⁻¹' closure (C.Iplus Ũ {x} ∩ C.Iminus Ũ {y}) :=
      fun t' ht' => subset_closure (hslice (cl t') (hcl_mem t') ht' s ⟨h0, h1⟩)
    have := closure_minimal hS (isClosed_closure.preimage hcont) htc
    simp only [mem_preimage, hcl_eq t htI] at this
    exact hcl this
  rintro ⟨t, s⟩ ⟨ht, hs⟩
  have := hsub ht hs
  simpa [hcl_eq t ht] using this

/-- (i): the homotopy is one of `W ⊓ Ũ`; every curve of it is a chronal curve of `W ⊓ Ũ`
("a timelike curve in `Ũ`", `:621`). -/
theorem ChronalHomotopyOn.inf_of_closure_subset (h : C.ChronalHomotopyOn W Γ γ₀ γ₁)
    (hx : γ₀ 0 = x) (hy : γ₀ 1 = y) (h₀ : MapsTo γ₀ (Icc 0 1) Ũ)
    (hcl : closure (C.Iplus Ũ {x} ∩ C.Iminus Ũ {y}) ⊆ Ũ) :
    C.ChronalHomotopyOn (W ⊓ Ũ) Γ γ₀ γ₁ :=
  h.restrict inf_le_left fun _ hq => ⟨h.mapsTo hq, h.mapsTo_of_closure_subset hx hy h₀ hcl hq⟩

/-- (i), §1's "a homotopy as above cannot escape `I⁺(γ̃(s₀), Ũ) ∩ I⁻(γ̃(0), Ũ)`" (`:158`): the
interior points of every curve of the homotopy lie in `I⁺(x, W ⊓ Ũ) ∩ I⁻(y, W ⊓ Ũ)`. -/
theorem ChronalHomotopyOn.mem_Iplus_inter_Iminus_of_closure_subset
    (h : C.ChronalHomotopyOn W Γ γ₀ γ₁) (hx : γ₀ 0 = x) (hy : γ₀ 1 = y)
    (h₀ : MapsTo γ₀ (Icc 0 1) Ũ) (hcl : closure (C.Iplus Ũ {x} ∩ C.Iminus Ũ {y}) ⊆ Ũ) {t s : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Ioo (0 : ℝ) 1) :
    Γ t s ∈ C.Iplus (W ⊓ Ũ) {x} ∩ C.Iminus (W ⊓ Ũ) {y} := by
  have hc := (h.inf_of_closure_subset hx hy h₀ hcl).chronalCurveOn t ht
  have h1 := hc.lt_of_lt le_rfl hs.1 hs.2.le
  have h2 := hc.lt_of_lt hs.1.le hs.2 le_rfl
  rw [h.fix_zero t ht, hx] at h1
  rw [h.fix_one t ht, hy] at h2
  exact ⟨Precausality.mem_Iplus_singleton.2 h1, Precausality.mem_Iminus_singleton.2 h2⟩

/-- The closure hypothesis passes to a nearer second vertex: if `y ≪_Ũ y'`, the diamond from `x`
to `y` lies in the diamond from `x` to `y'`. This is how Sbierski's hypotheses, stated with
`y' = γ̃(0)` (`:158`, `:621`), give the ones of this file for `y = γ̃(s)`, `s < 0`. -/
theorem closure_Iplus_inter_Iminus_subset_of_lt (hyy' : C.lt Ũ y y')
    (hcl : closure (C.Iplus Ũ {x} ∩ C.Iminus Ũ {y'}) ⊆ Ũ) :
    closure (C.Iplus Ũ {x} ∩ C.Iminus Ũ {y}) ⊆ Ũ := by
  refine (closure_mono ?_).trans hcl
  rintro z ⟨hxz, hzy⟩
  exact ⟨hxz, Precausality.mem_Iminus_singleton.2
    (C.lt_trans (Precausality.mem_Iminus_singleton.1 hzy) hyy')⟩

/-- (i), **Step 3 as printed** (`:621`): the homotopy runs from `x = γ̃(−s₀)` to `y = γ̃(−s₁)`
and the closure hypothesis is on the diamond from `x` to `y' = γ̃(0)`, with `y ≪_Ũ y'`. -/
theorem ChronalHomotopyOn.mapsTo_of_closure_subset_of_lt (h : C.ChronalHomotopyOn W Γ γ₀ γ₁)
    (hx : γ₀ 0 = x) (hy : γ₀ 1 = y) (h₀ : MapsTo γ₀ (Icc 0 1) Ũ) (hyy' : C.lt Ũ y y')
    (hcl : closure (C.Iplus Ũ {x} ∩ C.Iminus Ũ {y'}) ⊆ Ũ) :
    MapsTo (uncurry Γ) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) Ũ :=
  h.mapsTo_of_closure_subset hx hy h₀ (closure_Iplus_inter_Iminus_subset_of_lt hyy' hcl)


/-! ### (ii) The diamond identification, (1.2)'s `⊇` -/

/-- (ii), the curve form (Thm 4.11, `:1623`: "we need to show that `ι ∘ σ` maps into `Õ`"):
in a future one-connected `W`, every chronal curve `σ` from `x` to `y` is a chronal curve of
`W ⊓ Ũ`, as soon as one chronal curve `γ` of `W` from `x` to `y` lies in `Ũ` and the closure of
`I⁺(x, Ũ) ∩ I⁻(y, Ũ)` lies in `Ũ`. No arc-connectedness is used. -/
theorem FutureOneConnectedOn.chronalCurveOn_inf_of_closure_subset
    (hfoc : C.FutureOneConnectedOn W) (hγ : C.ChronalCurveOn W γ 0 1) (hx : γ 0 = x)
    (hy : γ 1 = y) (hγŨ : MapsTo γ (Icc 0 1) Ũ)
    (hcl : closure (C.Iplus Ũ {x} ∩ C.Iminus Ũ {y}) ⊆ Ũ)
    (hσ : C.ChronalCurveOn W σ 0 1) (hσx : σ 0 = x) (hσy : σ 1 = y) :
    C.ChronalCurveOn (W ⊓ Ũ) σ 0 1 := by
  obtain ⟨Γ, hΓ⟩ := hfoc x y γ σ hγ hx hy hσ hσx hσy
  exact (hΓ.inf_of_closure_subset hx hy hγŨ hcl).chronalCurveOn_right

/-- (ii), **the identification**, (1.2)'s `⊇` (`:153–158`): for `W` causally arc-connected and
future one-connected, `I⁺(x, W) ∩ I⁻(y, W) ⊆ I⁺(x, W ⊓ Ũ) ∩ I⁻(y, W ⊓ Ũ)` as soon as one chronal
curve of `W` from `x` to `y` lies in `Ũ` and the closure of `I⁺(x, Ũ) ∩ I⁻(y, Ũ)` lies in `Ũ`.
A point `z` of the diamond of `W` lies on a chronal curve of `W` from `x` to `y` (two curves
concatenated through `z`), which future one-connectedness and (i) put in `W ⊓ Ũ`. -/
theorem Iplus_inter_Iminus_subset_inf_of_futureOneConnectedOn (hcac : C.CausallyArcConnectedOn W)
    (hfoc : C.FutureOneConnectedOn W) (hγ : C.ChronalCurveOn W γ 0 1) (hx : γ 0 = x)
    (hy : γ 1 = y) (hγŨ : MapsTo γ (Icc 0 1) Ũ)
    (hcl : closure (C.Iplus Ũ {x} ∩ C.Iminus Ũ {y}) ⊆ Ũ) :
    C.Iplus W {x} ∩ C.Iminus W {y} ⊆ C.Iplus (W ⊓ Ũ) {x} ∩ C.Iminus (W ⊓ Ũ) {y} := by
  rintro z ⟨hxz, hzy⟩
  rw [Precausality.mem_Iplus_singleton] at hxz
  rw [Precausality.mem_Iminus_singleton] at hzy
  obtain ⟨c₁, hc₁, hc₁0, hc₁1⟩ := (hcac W le_rfl x z).2.1 hxz
  obtain ⟨c₂, hc₂, hc₂0, hc₂1⟩ := (hcac W le_rfl z y).2.1 hzy
  obtain ⟨c, hc, hc0, hc1, hcm⟩ :=
    CurveOn.exists_concat_mid C.isRelFamily_lt hc₁ hc₂ (hc₁1.trans hc₂0.symm)
  have hc' : C.ChronalCurveOn (W ⊓ Ũ) c 0 1 :=
    hfoc.chronalCurveOn_inf_of_closure_subset hγ hx hy hγŨ hcl hc (hc0.trans hc₁0)
      (hc1.trans hc₂1)
  have h1 := hc'.lt_of_lt le_rfl (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  have h2 := hc'.lt_of_lt (by norm_num) (by norm_num : (1 / 2 : ℝ) < 1) le_rfl
  rw [hc0, hc₁0, hcm, hc₁1] at h1
  rw [hc1, hc₂1, hcm, hc₁1] at h2
  exact ⟨Precausality.mem_Iplus_singleton.2 h1, Precausality.mem_Iminus_singleton.2 h2⟩

/-- (ii), with equality: the diamond of `W` from `x` to `y` is that of `W ⊓ Ũ`. -/
theorem Iplus_inter_Iminus_eq_inf_of_futureOneConnectedOn (hcac : C.CausallyArcConnectedOn W)
    (hfoc : C.FutureOneConnectedOn W) (hγ : C.ChronalCurveOn W γ 0 1) (hx : γ 0 = x)
    (hy : γ 1 = y) (hγŨ : MapsTo γ (Icc 0 1) Ũ)
    (hcl : closure (C.Iplus Ũ {x} ∩ C.Iminus Ũ {y}) ⊆ Ũ) :
    C.Iplus W {x} ∩ C.Iminus W {y} = C.Iplus (W ⊓ Ũ) {x} ∩ C.Iminus (W ⊓ Ũ) {y} := by
  refine (Iplus_inter_Iminus_subset_inf_of_futureOneConnectedOn hcac hfoc hγ hx hy hγŨ
    hcl).antisymm ?_
  rintro z ⟨hxz, hzy⟩
  exact ⟨Precausality.mem_Iplus_singleton.2
      (C.lt_mono inf_le_left (Precausality.mem_Iplus_singleton.1 hxz)),
    Precausality.mem_Iminus_singleton.2
      (C.lt_mono inf_le_left (Precausality.mem_Iminus_singleton.1 hzy))⟩

/-- (ii), **the target's form**: `I⁺(x, W) ∩ I⁻(y, W) ⊆ I⁺(x, Ũ) ∩ I⁻(y, Ũ)`. -/
theorem Iplus_inter_Iminus_subset_of_futureOneConnectedOn (hcac : C.CausallyArcConnectedOn W)
    (hfoc : C.FutureOneConnectedOn W) (hγ : C.ChronalCurveOn W γ 0 1) (hx : γ 0 = x)
    (hy : γ 1 = y) (hγŨ : MapsTo γ (Icc 0 1) Ũ)
    (hcl : closure (C.Iplus Ũ {x} ∩ C.Iminus Ũ {y}) ⊆ Ũ) :
    C.Iplus W {x} ∩ C.Iminus W {y} ⊆ C.Iplus Ũ {x} ∩ C.Iminus Ũ {y} := by
  intro z hz
  obtain ⟨hxz, hzy⟩ :=
    Iplus_inter_Iminus_subset_inf_of_futureOneConnectedOn hcac hfoc hγ hx hy hγŨ hcl hz
  exact ⟨Precausality.mem_Iplus_singleton.2
      (C.lt_mono inf_le_right (Precausality.mem_Iplus_singleton.1 hxz)),
    Precausality.mem_Iminus_singleton.2
      (C.lt_mono inf_le_right (Precausality.mem_Iminus_singleton.1 hzy))⟩

/-- (ii), **(1.2)'s `⊇` as printed** (`:153–158`): the closure hypothesis on the diamond from
`x = γ̃(s₀)` to `y' = γ̃(0)`, the inclusion for every `y = γ̃(s)` with `y ≪_Ũ y'`. -/
theorem Iplus_inter_Iminus_subset_of_futureOneConnectedOn_of_lt
    (hcac : C.CausallyArcConnectedOn W) (hfoc : C.FutureOneConnectedOn W)
    (hγ : C.ChronalCurveOn W γ 0 1) (hx : γ 0 = x) (hy : γ 1 = y) (hγŨ : MapsTo γ (Icc 0 1) Ũ)
    (hyy' : C.lt Ũ y y') (hcl : closure (C.Iplus Ũ {x} ∩ C.Iminus Ũ {y'}) ⊆ Ũ) :
    C.Iplus W {x} ∩ C.Iminus W {y} ⊆ C.Iplus Ũ {x} ∩ C.Iminus Ũ {y} :=
  Iplus_inter_Iminus_subset_of_futureOneConnectedOn hcac hfoc hγ hx hy hγŨ
    (closure_Iplus_inter_Iminus_subset_of_lt hyy' hcl)

/-- (ii) for the spacetime itself (`W = M`), the consequence at `[future_one_connected,
causally_arc_connected]`: `I⁺(x) ∩ I⁻(y) = I⁺(x, Ũ) ∩ I⁻(y, Ũ)`, (1.2) with equality. -/
theorem Iplus_inter_Iminus_eq_of_futureOneConnected (hcac : C.CausallyArcConnected)
    (hfoc : C.FutureOneConnected) (hγ : C.ChronalCurveOn ⊤ γ 0 1) (hx : γ 0 = x)
    (hy : γ 1 = y) (hγŨ : MapsTo γ (Icc 0 1) Ũ)
    (hcl : closure (C.Iplus Ũ {x} ∩ C.Iminus Ũ {y}) ⊆ Ũ) :
    C.Iplus ⊤ {x} ∩ C.Iminus ⊤ {y} = C.Iplus Ũ {x} ∩ C.Iminus Ũ {y} := by
  have := Iplus_inter_Iminus_eq_inf_of_futureOneConnectedOn hcac hfoc hγ hx hy hγŨ hcl
  rwa [top_inf_eq] at this

/-! ### (iii) Local strong causality -/

variable (C) in
/-- `def:strongly_causal_spacetime` for the open `W` seen as a spacetime (kb/0001): every
neighbourhood of every point of `W` contains a neighbourhood, not necessarily open (DEC-7),
causally convex in `W`. -/
def StronglyCausalOn (W : Opens M) : Prop :=
  ∀ p ∈ W, ∀ U ∈ 𝓝 p, ∃ V ∈ 𝓝 p, V ⊆ U ∧ C.CausallyConvexIn V W

variable (C) in
/-- **Local strong causality**: every point has an open neighbourhood which is strongly causal as
a spacetime. The confinement hypothesis of Sbierski's Thm 3.1 Step 1.2 (`:528`) as a property of
the extension `M̃`, which need not be strongly causal. -/
def LocallyStronglyCausal : Prop := ∀ p : M, ∃ W : Opens M, p ∈ W ∧ C.StronglyCausalOn W

theorem stronglyCausalOn_top : C.StronglyCausalOn ⊤ ↔ C.StronglyCausal :=
  ⟨fun h p => h p trivial, fun h p _ => h p⟩

/-- `StronglyCausalOn` is hereditary: a set causally convex in `W` meets a smaller open `W'` in a
set causally convex in `W'`, since `J_{W'}(p, q) ⊆ J_W(p, q) ∩ W'`. -/
theorem StronglyCausalOn.mono (h : C.StronglyCausalOn W) (hW : W' ≤ W) :
    C.StronglyCausalOn W' := by
  intro p hp U hU
  obtain ⟨V, hV, hVU, hVc⟩ := h p (hW hp) U hU
  refine ⟨V ∩ W', inter_mem hV (W'.isOpen.mem_nhds hp), inter_subset_left.trans hVU,
    inter_subset_right, ?_⟩
  rintro a ⟨haV, -⟩ b ⟨hbV, -⟩ z hz
  rw [mem_diamond] at hz
  exact ⟨hVc.2 a haV b hbV (mem_diamond.2 ⟨C.le_mono hW hz.1, C.le_mono hW hz.2⟩),
    C.le_mem_right hz.1⟩

theorem dual_stronglyCausalOn : C.dual.StronglyCausalOn W ↔ C.StronglyCausalOn W := by
  simp only [StronglyCausalOn, dual_causallyConvexIn]

/-- Local strong causality is two-sided. -/
theorem dual_locallyStronglyCausal : C.dual.LocallyStronglyCausal ↔ C.LocallyStronglyCausal := by
  simp only [LocallyStronglyCausal, dual_stronglyCausalOn]

/-- **The edge `strongly_causal ⇒ locally_strongly_causal`** (`W = M`). -/
theorem StronglyCausal.locallyStronglyCausal (h : C.StronglyCausal) : C.LocallyStronglyCausal :=
  fun _ => ⟨⊤, trivial, stronglyCausalOn_top.2 h⟩

/-- The strongly causal open neighbourhood can be taken inside any neighbourhood (heredity). -/
theorem locallyStronglyCausal_iff_nhds : C.LocallyStronglyCausal ↔
    ∀ p : M, ∀ N ∈ 𝓝 p, ∃ W : Opens M, p ∈ W ∧ (W : Set M) ⊆ N ∧ C.StronglyCausalOn W := by
  refine ⟨fun h p N hN => ?_, fun h p => ?_⟩
  · obtain ⟨W, hpW, hW⟩ := h p
    exact ⟨W ⊓ ⟨interior N, isOpen_interior⟩, ⟨hpW, mem_interior_iff_mem_nhds.2 hN⟩,
      fun z hz => interior_subset hz.2, hW.mono inf_le_left⟩
  · obtain ⟨W, hpW, -, hW⟩ := h p univ univ_mem
    exact ⟨W, hpW, hW⟩

/-- The causal diamond of an open `Ũ ≤ W` between two points of a set causally convex in `W` lies
in that set (`≤_Ũ ⊆ ≤_W`), and contains the chronological diamond (`≪_Ũ ⊆ ≤_Ũ`). -/
theorem diamond_subset_of_causallyConvexIn {V : Set M} (hVc : C.CausallyConvexIn V W)
    (hŨW : Ũ ≤ W) (hx : x ∈ V) (hy : y ∈ V) :
    C.diamond Ũ x y ⊆ V ∧ C.Iplus Ũ {x} ∩ C.Iminus Ũ {y} ⊆ C.diamond Ũ x y := by
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · rw [mem_diamond] at hz
    exact hVc.2 x hx y hy (mem_diamond.2 ⟨C.le_mono hŨW hz.1, C.le_mono hŨW hz.2⟩)
  · exact mem_diamond.2 ⟨C.le_of_lt (Precausality.mem_Iplus_singleton.1 hz.1),
      C.le_of_lt (Precausality.mem_Iminus_singleton.1 hz.2)⟩

/-- (iii), the closure hypothesis of (i) near a point of a strongly causal `W`, on a regular
space: there are an open `Ũ ∋ p` inside `W ∩ N` and a neighbourhood `V` of `p` such that, for all
`x, y ∈ V`, the causal diamond `J_Ũ(x, y)` lies in `V`, and its closure, hence that of
`I⁺(x, Ũ) ∩ I⁻(y, Ũ)`, lies in `Ũ`. -/
theorem StronglyCausalOn.exists_closure_subset [RegularSpace M] (h : C.StronglyCausalOn W)
    {p : M} (hp : p ∈ W) {N : Set M} (hN : N ∈ 𝓝 p) :
    ∃ Ũ : Opens M, p ∈ Ũ ∧ Ũ ≤ W ∧ (Ũ : Set M) ⊆ N ∧ ∃ V ∈ 𝓝 p, ∀ x ∈ V, ∀ y ∈ V,
      C.diamond Ũ x y ⊆ V ∧ closure (C.diamond Ũ x y) ⊆ Ũ ∧
        closure (C.Iplus Ũ {x} ∩ C.Iminus Ũ {y}) ⊆ Ũ := by
  let Ũ : Opens M := W ⊓ ⟨interior N, isOpen_interior⟩
  have hpŨ : p ∈ Ũ := ⟨hp, mem_interior_iff_mem_nhds.2 hN⟩
  obtain ⟨K, ⟨hK, hKc⟩, hKŨ⟩ := (closed_nhds_basis p).mem_iff.1 (Ũ.isOpen.mem_nhds hpŨ)
  obtain ⟨V, hV, hVK, hVc⟩ := h p hp K hK
  refine ⟨Ũ, hpŨ, inf_le_left, fun z hz => interior_subset hz.2, V, hV, fun x hx y hy => ?_⟩
  obtain ⟨hD, hI⟩ := diamond_subset_of_causallyConvexIn hVc inf_le_left hx hy
  have hDcl : closure (C.diamond Ũ x y) ⊆ Ũ := (closure_minimal (hD.trans hVK) hKc).trans hKŨ
  exact ⟨hD, hDcl, (closure_mono hI).trans hDcl⟩

/-- (iii), with compact closures, on a locally compact `R₁` (e.g. Hausdorff) space: Sbierski's
chart diamond with compact closure (Step 1.2, `:528`, paraphrased) and "its closure in `M̃` is
contained in `Õ`" (`:1625`). -/
theorem StronglyCausalOn.exists_isCompact_closure [LocallyCompactSpace M] [R1Space M]
    (h : C.StronglyCausalOn W) {p : M} (hp : p ∈ W) {N : Set M} (hN : N ∈ 𝓝 p) :
    ∃ Ũ : Opens M, p ∈ Ũ ∧ Ũ ≤ W ∧ (Ũ : Set M) ⊆ N ∧ ∃ V ∈ 𝓝 p, ∀ x ∈ V, ∀ y ∈ V,
      C.diamond Ũ x y ⊆ V ∧
        IsCompact (closure (C.diamond Ũ x y)) ∧ closure (C.diamond Ũ x y) ⊆ Ũ ∧
        IsCompact (closure (C.Iplus Ũ {x} ∩ C.Iminus Ũ {y})) ∧
        closure (C.Iplus Ũ {x} ∩ C.Iminus Ũ {y}) ⊆ Ũ := by
  let Ũ : Opens M := W ⊓ ⟨interior N, isOpen_interior⟩
  have hpŨ : p ∈ Ũ := ⟨hp, mem_interior_iff_mem_nhds.2 hN⟩
  obtain ⟨K, hK, hKŨ, hKc⟩ := local_compact_nhds (Ũ.isOpen.mem_nhds hpŨ)
  obtain ⟨V, hV, hVK, hVc⟩ := h p hp K hK
  refine ⟨Ũ, hpŨ, inf_le_left, fun z hz => interior_subset hz.2, V, hV, fun x hx y hy => ?_⟩
  obtain ⟨hD, hI⟩ := diamond_subset_of_causallyConvexIn hVc inf_le_left hx hy
  have hclK : closure K ⊆ Ũ := hKc.closure_subset_of_isOpen Ũ.isOpen hKŨ
  exact ⟨hD, hKc.closure_of_subset (hD.trans hVK), (closure_mono (hD.trans hVK)).trans hclK,
    hKc.closure_of_subset (hI.trans (hD.trans hVK)),
    (closure_mono (hI.trans (hD.trans hVK))).trans hclK⟩

/-- (iii), **the target's form**: on a locally compact `R₁` (e.g. Hausdorff) space, a locally
strongly causal causality has, at every point `p` and inside every neighbourhood `N` of `p`, an
open `Ũ ∋ p`, strongly causal as a spacetime, and a neighbourhood `V` of `p` such that for all
`x, y ∈ V` the closure of `I⁺(x, Ũ) ∩ I⁻(y, Ũ)` is compact and lies in `Ũ`. -/
theorem LocallyStronglyCausal.exists_isCompact_closure [LocallyCompactSpace M] [R1Space M]
    (h : C.LocallyStronglyCausal) (p : M) {N : Set M} (hN : N ∈ 𝓝 p) :
    ∃ Ũ : Opens M, p ∈ Ũ ∧ (Ũ : Set M) ⊆ N ∧ C.StronglyCausalOn Ũ ∧ ∃ V ∈ 𝓝 p,
      ∀ x ∈ V, ∀ y ∈ V, IsCompact (closure (C.Iplus Ũ {x} ∩ C.Iminus Ũ {y})) ∧
        closure (C.Iplus Ũ {x} ∩ C.Iminus Ũ {y}) ⊆ Ũ := by
  obtain ⟨W, hpW, hW⟩ := h p
  obtain ⟨Ũ, hpŨ, hŨW, hŨN, V, hV, hV'⟩ := hW.exists_isCompact_closure hpW hN
  exact ⟨Ũ, hpŨ, hŨN, hW.mono hŨW, V, hV, fun x hx y hy =>
    ⟨(hV' x hx y hy).2.2.2.1, (hV' x hx y hy).2.2.2.2⟩⟩

/-- **The assembly of (i)–(iii)**: on a locally compact `R₁` (e.g. Hausdorff) space with a locally
strongly causal causality, every point `p` has, inside any neighbourhood `N`, an open `Ũ ∋ p` and
a neighbourhood `V` of `p` such that for all `x, y ∈ V` the closure of `I⁺(x, Ũ) ∩ I⁻(y, Ũ)` is
compact and in `Ũ`, and, for every causally arc-connected, future one-connected open `W` and
every chronal curve of `W` from `x` to `y` lying in `Ũ`, the diamonds of `W` and of `W ⊓ Ũ`
from `x` to `y` are equal. -/
theorem LocallyStronglyCausal.exists_diamond_identification [LocallyCompactSpace M] [R1Space M]
    (h : C.LocallyStronglyCausal) (p : M) {N : Set M} (hN : N ∈ 𝓝 p) :
    ∃ Ũ : Opens M, p ∈ Ũ ∧ (Ũ : Set M) ⊆ N ∧ ∃ V ∈ 𝓝 p, ∀ x ∈ V, ∀ y ∈ V,
      IsCompact (closure (C.Iplus Ũ {x} ∩ C.Iminus Ũ {y})) ∧
        closure (C.Iplus Ũ {x} ∩ C.Iminus Ũ {y}) ⊆ Ũ ∧
        ∀ W : Opens M, C.CausallyArcConnectedOn W → C.FutureOneConnectedOn W →
          ∀ γ : ℝ → M, C.ChronalCurveOn W γ 0 1 → γ 0 = x → γ 1 = y → MapsTo γ (Icc 0 1) Ũ →
            C.Iplus W {x} ∩ C.Iminus W {y} = C.Iplus (W ⊓ Ũ) {x} ∩ C.Iminus (W ⊓ Ũ) {y} := by
  obtain ⟨Ũ, hpŨ, hŨN, -, V, hV, hV'⟩ := h.exists_isCompact_closure p hN
  refine ⟨Ũ, hpŨ, hŨN, V, hV, fun x hx y hy => ⟨(hV' x hx y hy).1, (hV' x hx y hy).2,
    fun W hcac hfoc γ hγ hγx hγy hγŨ => ?_⟩⟩
  exact Iplus_inter_Iminus_eq_inf_of_futureOneConnectedOn hcac hfoc hγ hγx hγy hγŨ
    (hV' x hx y hy).2

end Causality

/-! ### Witnesses on the timelike line (kb/0011) -/

/-- (i) on the timelike line: the closure of `I⁺(0, (−1, 2)) ∩ I⁻(1, (−1, 2))` lies in `(−1, 2)`,
and the homotopy between `s ↦ s` and `s ↦ s²` that future one-connectedness gives stays in
`(−1, 2)`. -/
theorem timelikeLine_confinement :
    closure (timelikeLine.Iplus ⟨Ioo (-1) 2, isOpen_Ioo⟩ {0} ∩
        timelikeLine.Iminus ⟨Ioo (-1) 2, isOpen_Ioo⟩ {1}) ⊆ Ioo (-1 : ℝ) 2 ∧
      ∃ Γ : ℝ → ℝ → ℝ, timelikeLine.ChronalHomotopyOn ⊤ Γ id (fun s => s ^ 2) ∧
        MapsTo (uncurry Γ) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) (Ioo (-1 : ℝ) 2) := by
  have hcl : closure (timelikeLine.Iplus ⟨Ioo (-1) 2, isOpen_Ioo⟩ {0} ∩
      timelikeLine.Iminus ⟨Ioo (-1) 2, isOpen_Ioo⟩ {1}) ⊆ Ioo (-1 : ℝ) 2 := by
    refine (closure_minimal (fun z hz => ?_) isClosed_Icc).trans
      (fun z hz => ⟨by linarith [hz.1], by linarith [hz.2]⟩ : Icc (0 : ℝ) 1 ⊆ Ioo (-1) 2)
    obtain ⟨h1, h2⟩ := hz
    rw [Precausality.mem_Iplus_singleton, timelikeLine_lt] at h1
    rw [Precausality.mem_Iminus_singleton, timelikeLine_lt] at h2
    exact ⟨h1.1.le, h2.1.le⟩
  obtain ⟨Γ, hΓ⟩ := timelikeLine_chronallyHomotopicOn_sq.1
  exact ⟨hcl, Γ, hΓ, hΓ.mapsTo_of_closure_subset (Ũ := ⟨Ioo (-1) 2, isOpen_Ioo⟩) rfl rfl
    (fun s hs => ⟨by show (-1 : ℝ) < s; linarith [hs.1], by show s < 2; linarith [hs.2]⟩) hcl⟩

/-- (ii) on the timelike line, which is causally arc-connected and future one-connected, with
`W = ℝ`, `Ũ = (−1, 2)`, `x = 0`, `y = 1` and `γ = id`; the diamond is not empty. -/
theorem timelikeLine_diamond_identification :
    timelikeLine.Iplus ⊤ {0} ∩ timelikeLine.Iminus ⊤ {1} ⊆
        timelikeLine.Iplus ⟨Ioo (-1) 2, isOpen_Ioo⟩ {0} ∩
          timelikeLine.Iminus ⟨Ioo (-1) 2, isOpen_Ioo⟩ {1} ∧
      (1 / 2 : ℝ) ∈ timelikeLine.Iplus ⊤ {0} ∩ timelikeLine.Iminus ⊤ {1} := by
  have hid : timelikeLine.ChronalCurveOn ⊤ id 0 1 :=
    timelikeLine_chronalCurveOn_iff.2 ⟨strictMonoOn_id, continuousOn_id, fun _ _ => trivial⟩
  refine ⟨Causality.Iplus_inter_Iminus_subset_of_futureOneConnectedOn
    timelikeLine_causallyArcConnected (timelikeLine_futureOneConnectedOn ⊤) hid rfl rfl
    (fun s hs => ⟨by show (-1 : ℝ) < s; linarith [hs.1], by show s < 2; linarith [hs.2]⟩)
    timelikeLine_confinement.1, ?_, ?_⟩
  · rw [Precausality.mem_Iplus_singleton, timelikeLine_lt]
    exact ⟨by norm_num, fun _ _ => trivial⟩
  · rw [Precausality.mem_Iminus_singleton, timelikeLine_lt]
    exact ⟨by norm_num, fun _ _ => trivial⟩

/-- The timelike line is locally strongly causal. -/
theorem timelikeLine_locallyStronglyCausal : timelikeLine.LocallyStronglyCausal :=
  Causality.StronglyCausal.locallyStronglyCausal timelikeLine_stronglyCausal

/-- (iii) on the timelike line, at `0`: an open `Ũ ∋ 0`, strongly causal as a spacetime, and a
neighbourhood `V` of `0` whose chronological diamonds in `Ũ` have compact closures in `Ũ`. -/
theorem timelikeLine_exists_isCompact_closure :
    ∃ Ũ : Opens ℝ, (0 : ℝ) ∈ Ũ ∧ timelikeLine.StronglyCausalOn Ũ ∧ ∃ V ∈ 𝓝 (0 : ℝ),
      ∀ x ∈ V, ∀ y ∈ V,
        IsCompact (closure (timelikeLine.Iplus Ũ {x} ∩ timelikeLine.Iminus Ũ {y})) ∧
          closure (timelikeLine.Iplus Ũ {x} ∩ timelikeLine.Iminus Ũ {y}) ⊆ Ũ := by
  obtain ⟨Ũ, h0, -, hsc, V, hV, hV'⟩ :=
    Causality.LocallyStronglyCausal.exists_isCompact_closure timelikeLine_locallyStronglyCausal 0
      univ_mem
  exact ⟨Ũ, h0, hsc, V, hV, hV'⟩

/-! ### The confinement hypothesis is weaker than local strong causality -/

/-- **Local strong causality is sufficient, not necessary, for the confinement hypothesis of
(i)**: on `ℝ`, the causality relating any two points of `U` causally and none chronologically has
compact chronological diamonds (empty ones) inside every open `Ũ`, near every point, and is not
locally strongly causal (`J_W(0, 0) = W` for every open `W ∋ 0`). It is not absolutely minimal:
a remark on the hypothesis, not a ladder separation. -/
theorem exists_confining_not_locallyStronglyCausal :
    ∃ C : Causality ℝ, (∀ p : ℝ, ∀ N ∈ 𝓝 p, ∃ Ũ : Opens ℝ, p ∈ Ũ ∧ (Ũ : Set ℝ) ⊆ N ∧
      ∃ V ∈ 𝓝 p, ∀ x ∈ V, ∀ y ∈ V, IsCompact (closure (C.Iplus Ũ {x} ∩ C.Iminus Ũ {y})) ∧
        closure (C.Iplus Ũ {x} ∩ C.Iminus Ũ {y}) ⊆ Ũ) ∧ ¬ C.LocallyStronglyCausal := by
  let C : Causality ℝ :=
    { le := fun U x y => x ∈ U ∧ y ∈ U
      lt := fun _ _ _ => False
      le_mem_left := fun h => h.1
      le_mem_right := fun h => h.2
      lt_mem_left := fun h => h.elim
      lt_mem_right := fun h => h.elim
      le_refl := fun hx => ⟨hx, hx⟩
      le_trans := fun h₁ h₂ => ⟨h₁.1, h₂.2⟩
      lt_trans := fun h _ => h
      le_mono := fun h _ _ h' => ⟨h h'.1, h h'.2⟩
      lt_mono := fun _ _ _ h' => h'
      le_of_lt := fun h => h.elim
      isOpen_lt_right := fun _ _ => by simp
      isOpen_lt_left := fun _ _ => by simp }
  have hI : ∀ (U : Opens ℝ) (x y : ℝ), C.Iplus U {x} ∩ C.Iminus U {y} = ∅ := by
    intro U x y
    ext z
    simp only [mem_inter_iff, Precausality.mem_Iplus_singleton, mem_empty_iff_false, iff_false]
    exact fun h => h.1
  refine ⟨C, fun p N hN => ⟨⟨interior N, isOpen_interior⟩, mem_interior_iff_mem_nhds.2 hN,
    interior_subset, univ, univ_mem, fun x _ y _ => ?_⟩, fun h => ?_⟩
  · rw [hI, closure_empty]
    exact ⟨isCompact_empty, empty_subset _⟩
  · obtain ⟨W, h0W, hW⟩ := h 0
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 W.isOpen 0 h0W
    obtain ⟨V, hV, hVU, hVc⟩ := hW 0 h0W (Ioo (-(δ / 2)) (δ / 2))
      (Ioo_mem_nhds (by linarith) (by linarith))
    have hmem : 3 * δ / 4 ∈ W := hball (by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
      linarith)
    have h0V : (0 : ℝ) ∈ V := mem_of_mem_nhds hV
    have hz : 3 * δ / 4 ∈ C.diamond W 0 0 :=
      Causality.mem_diamond.2 ⟨⟨h0W, hmem⟩, ⟨hmem, h0W⟩⟩
    have := (hVU (hVc.2 0 h0V 0 h0V hz)).2
    linarith

end Causal
