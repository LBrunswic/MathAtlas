import Causal.DiamondConfinement
import Causal.Flat.Form

/-!
# Minkowski space is future one-connected (Sbierski 1507.00601, Thm 3.1 Step 2.1)

Programme target `T-loc-minkowski-future-one-connected` (`programme/roadmap.toml`; layer 3,
stream localisation, model `minkowski`, `provides = []` until `future_one_connected` is a ladder
node). Source: J. Sbierski, *The C⁰-inextendibility of the Schwarzschild spacetime and the
spacelike diameter in Lorentzian geometry*, arXiv 1507.00601 v2,
`papers/sbierski-schwarzschild/legacy/labeled/InexSchwarzschild2.tex`. **No label is marked**: no
label of `ETT.tex` is concerned, and Step 2.1 is a step inside the proof of the Sbierski row
`schwthm:MinkInex` (`:475`), a statement about `C⁰` extensions whose timelike curves are read as
chronal curves (`Causal.TimelikeHomotopy`'s reading). A model module: a layer-1 module never
imports it.

* **The ETT definition, instantiated** (the layer-3 rule): `minkowski_futureOneConnected` is
  `Causality.FutureOneConnected (minkowski n)`, every `n` (`ℝ^{1,n}`); on every convex open set,
  `minkowski_futureOneConnectedOn` (a slab, a ball, a cube `(−ε, ε)^{n+1}`); time-reversed,
  `minkowski_dual_futureOneConnected(On)`.
* **Step 2.1 as printed** (`:567`): every future chronal curve `λ` of a convex open `W` over
  `[0, 1]` is chronally homotopic in `W`, with fixed endpoints, to the straight segment from
  `λ(0)` to `λ(1)` (`minkowski_chronallyHomotopicOn_segment`), by route (a), the convex
  combination `(1 − t)γ₀ + tγ₁` (`minkowski_chronalHomotopyOn_convexCombination`).
* **Sbierski's homotopy, corrected** (route (b)): the split at `s = t`,
  `Γ(t, s) = λ(0) + (s/t)(λ(t) − λ(0))` for `s ≤ t` and `λ(s)` for `s ≥ t`
  (`sbierskiSplitHomotopy`), is a chronal homotopy from `λ` to the segment in every convex open
  (`minkowski_chronalHomotopyOn_sbierskiSplit`), jointly continuous at the corner `(0, 0)`
  (`continuousOn_sbierskiSplitHomotopy`).
* **Sbierski's homotopy as printed** (`:577`) is not one, in any dimension and any open set: its
  slice at `t = 0` (with `λ(0) = 0`, `:575`) and its slice at `t = 1` pause, so they are not
  chronal curves (`minkowski_not_chronalCurveOn_sbierskiPrinted_zero`, `_one`,
  `minkowski_not_chronalHomotopyOn_sbierskiPrinted`).
* **The local condition** (`ChronalCurveOn` asks `≪_N` in small opens `N`): in Minkowski space it
  is the global cone condition, `minkowski_chronalCurveOn_iff` (continuous, in `W`, and
  `c s ≪ c s'` for `s < s'`), in every open `W`, through a ball, convex, on which `≪_N` is
  the restriction of `≪` (`Causal.Flat.lt_iff_of_convex`).
* **Witness** (kb/0011): the abstract identification applies without restatement,
  `minkowski_Iplus_inter_Iminus_eq_of_Jdiamond_subset` (through
  `Causality.Iplus_inter_Iminus_eq_of_futureOneConnected`: `I⁺(x) ∩ I⁻(y)` is the diamond of
  every open containing `J⁺(x) ∩ J⁻(y)`), and its On form for a convex open `W`
  (`minkowski_Iplus_inter_Iminus_eq_inf_of_convex`).

> **Step 2.1:** Any future directed timelike curve $\lambda : [0,1] \to \Mmink$ is timelike
> homotopic with fixed endpoints to the unique Lorentzian length maximising timelike geodesic from
> $\lambda(0)$ to $\lambda(1)$. (`InexSchwarzschild2.tex:567`)

> Recall that for $p, q \in \Mmink$ with $p \ll q $, the unique Lorentzian length maximising
> timelike geodesic from $p$ to $q$ is given by the straight line connecting $p$ with $q$.
> (`:570`)

> Without loss of generality we can assume that $\lambda(0) =0$. For $X \in T_0\Mmink \approx
> \Mmink$, we denote with $\sigma_X : [0,1] \to \Mmink$ the geodesic given by
> $\sigma_X (s) = s \cdot X$. A timelike homotopy $\Gamma : [0,1] \times [0,1] \to \Mmink$ with
> fixed endpoints between $\lambda$ and the Lorentzian length maximising geodesic
> $\sigma_{\lambda(1)}$ is given by
> $$\Gamma(t,s) = \big( \sigma_{\lambda(t)} * \lambda|_{[t,1]}\big) (s) \;,$$ where
> $\lambda|_{[t,1]}$ is understood to be reparametrised to the interval $[0,1]$ (for example by a
> linear rescaling). (`:575–579`)

> Note that the proof of Step 2.1 for the Minkowskian case shows, in particular, that the
> Minkowski spacetime is future one-connected. (`:835`)
-/

/-!
## The reading

* **Timelike curves are future chronal curves**, timelike homotopies are
  `Causality.ChronalHomotopyOn`, future one-connectedness is `Causality.FutureOneConnected`
  (`Causal.TimelikeHomotopy`, Sbierski Def 2.13, `:380–386`): its reading, not a new one.
* **`𝕄` is `Causal.minkowski n`** (`Causal/Minkowski.lean:76`), the static causality of
  `ℝ × EuclideanSpace ℝ (Fin n)`, `≪` globally `‖Δx‖ < Δt` (`minkowski_lt_top_iff`).
* **"The unique Lorentzian length maximising timelike geodesic" is the straight segment**
  `s ↦ λ(0) + s • (λ(1) − λ(0))`, as `:570` recalls; that it maximises the Lorentzian length is
  metric (`T-loc-minkowski-timelike-diameter`, DEC-147's package), not stated here.
* **`λ|_{[t,1]}` reparametrised linearly** (`:579`) is `u ↦ λ(t + u(1 − t))`, so
  `sbierskiPrintedHomotopy λ t s` is `(2s)·λ(t)` for `s ≤ 1/2` and `λ(t + (2s − 1)(1 − t))`
  for `s > 1/2`, with Sbierski's normalisation `λ(0) = 0` where it is used (the slice `t = 0`).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `(𝕄, m)`, `d + 1 ≥ 2` (`:228`, `:477`) | ⚠ weakened: `ℝ^{1,n}` for every `n`, `n = 0` included |
| `λ` a future directed timelike curve `[0, 1] → 𝕄` | ⚠ the reading: a future chronal curve of `W` over `[0, 1]` (`Causal.TimelikeHomotopy`) |
| the homotopy in `𝕄` | ⚠ weakened: in every convex open `W` (`W = ⊤` is `𝕄`) |
| `λ(0) = 0` (without loss of generality, `:575`) | not used: the segment and the split homotopy start at `λ(0)`; used only to refute the printed formula, which is written for it |
| the target, the length maximising geodesic | the straight segment (`:570`); maximality not stated (metric) |

## SCOPE (disclosed)

* **Not marked**: `schwthm:MinkInex` is a theorem about `C⁰` extensions; Step 2.1 is one step
  of its proof, and the comparison of Sbierski's piecewise smooth timelike curves with chronal
  curves is the `C0` layer 3 (`Causal.TimelikeHomotopy`'s SCOPE). The convex combination of two
  piecewise smooth timelike curves is piecewise smooth and timelike (the future timelike cone is
  convex), so route (a) also proves Sbierski's form; that is argued, not in Lean (no smooth
  curves here).
* **Non-convex open sets are not treated.** Future one-connectedness is not hereditary, and some
  open sets of Minkowski space lack it: `ℝ^{1,2}` minus the time axis carries two timelike curves
  between the same points whose spatial projections wind differently around the origin, so no
  homotopy, chronal or not, joins them in it (argued, not in Lean; the same winding argument is in
  Lean for the flat cylinder ℤe₁\𝐌^{1+1}, `Causal.Flat.windCurve_not_chronallyHomotopicOn`).
* **The printed homotopy's interior slices** (`0 < t < 1`) are chronal and the map is jointly
  continuous; only the two end slices fail. That is argued, not in Lean: what is in Lean is that
  the end slices fail, which refutes the printed `Γ` as a timelike homotopy.
* Sbierski uses Step 2.1 for `γ|[−s₀, −s₁]` (`:606`), a curve over another segment: the `[0, 1]`
  notion after an affine change of parameter (`Causal.TimelikeHomotopy`'s SCOPE).
* `minkowski_chronalCurveOn_iff` is the Minkowski cousin of `timelikeLine_chronalCurveOn_iff`
  (`Causal.TimelikeHomotopy`), and is of general use for building chronal curves of
  `ℝ^{1,n}`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Function Metric

variable {n : ℕ}

/-! ### Chronal curves of Minkowski space -/

/-- **The future timelike cone is convex**: a convex combination of two chronologically related
pairs is chronologically related. -/
theorem minkowski_lt_top_convexCombination {x₀ y₀ x₁ y₁ : Minkowski n}
    (h₀ : (minkowski n).lt ⊤ x₀ y₀) (h₁ : (minkowski n).lt ⊤ x₁ y₁) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    (minkowski n).lt ⊤ ((1 - t) • x₀ + t • x₁) ((1 - t) • y₀ + t • y₁) := by
  rw [minkowski_lt_top_iff] at h₀ h₁ ⊢
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  have hv : (1 - t) • y₀.2 + t • y₁.2 - ((1 - t) • x₀.2 + t • x₁.2) =
      (1 - t) • (y₀.2 - x₀.2) + t • (y₁.2 - x₁.2) := by
    simp only [smul_sub]; abel
  have h1t : 0 ≤ 1 - t := by linarith [ht.2]
  rw [hv]
  calc ‖(1 - t) • (y₀.2 - x₀.2) + t • (y₁.2 - x₁.2)‖
        ≤ (1 - t) * ‖y₀.2 - x₀.2‖ + t * ‖y₁.2 - x₁.2‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, norm_smul, Real.norm_of_nonneg h1t, Real.norm_of_nonneg ht.1]
    _ < (1 - t) * y₀.1 + t * y₁.1 - ((1 - t) * x₀.1 + t * x₁.1) := by
          rcases ht.2.lt_or_eq with h | h
          · have := mul_lt_mul_of_pos_left h₀ (by linarith : (0 : ℝ) < 1 - t)
            nlinarith [mul_le_mul_of_nonneg_left h₁.le ht.1]
          · subst h; simp only [sub_self, zero_mul, one_mul, zero_add]; exact h₁

/-- Along the straight line through `p ≪ q`, a later parameter is in the chronological future. -/
theorem minkowski_lt_top_segment {p q : Minkowski n} (hpq : (minkowski n).lt ⊤ p q) {s s' : ℝ}
    (hss' : s < s') : (minkowski n).lt ⊤ (p + s • (q - p)) (p + s' • (q - p)) := by
  rw [minkowski_lt_top_iff] at hpq ⊢
  have hk : 0 < s' - s := sub_pos.2 hss'
  have h2 : (p + s' • (q - p)).2 - (p + s • (q - p)).2 = (s' - s) • (q.2 - p.2) := by
    simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, sub_smul]; abel
  have h1 : (p + s' • (q - p)).1 - (p + s • (q - p)).1 = (s' - s) * (q.1 - p.1) := by
    simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]; ring
  rw [h1, h2, norm_smul, Real.norm_of_nonneg hk.le]
  exact mul_lt_mul_of_pos_left hpq hk

/-- **The chronal curves of Minkowski space**, in every open `W`: the continuous maps of `[a, b]`
into `W` along which `c s ≪ c s'` for `s < s'`. The local condition of `ChronalCurveOn` (`≪_N`
in every small open `N`) is met on a ball, convex, where `≪_N` is the restriction of `≪`
(`Causal.Flat.lt_iff_of_convex`). -/
theorem minkowski_chronalCurveOn_iff {W : Opens (Minkowski n)} {c : ℝ → Minkowski n} {a b : ℝ} :
    (minkowski n).ChronalCurveOn W c a b ↔
      ContinuousOn c (Icc a b) ∧ MapsTo c (Icc a b) W ∧
        ∀ s ∈ Icc a b, ∀ s' ∈ Icc a b, s < s' → (minkowski n).lt ⊤ (c s) (c s') := by
  constructor
  · intro hc
    exact ⟨CurveOn.continuousOn (minkowski n).isRelFamily_lt hc, fun s hs => hc.mem s hs,
      fun s hs s' hs' h => (minkowski n).lt_mono le_top (hc.lt_of_lt hs.1 h hs'.2)⟩
  · rintro ⟨hcont, hmaps, hlt⟩
    refine ⟨fun t ht => hmaps ht, fun t ht N _ htN => ?_⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 N.isOpen (c t) htN
    let B : Opens (Minkowski n) := ⟨ball (c t) ε, isOpen_ball⟩
    obtain ⟨δ, hδ, hδc⟩ := Metric.continuousWithinAt_iff.1 (hcont t ht) ε hε
    refine ⟨t - δ, t + δ, by linarith, by linarith, fun s hs s' hs' h1 h2 h3 => ?_⟩
    have hd1 : dist s t < δ := by rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    have hd2 : dist s' t < δ := by rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    have hB : (minkowski n).lt B (c s) (c s') :=
      (Flat.lt_iff_of_convex (V := B) (convex_ball (c t) ε)).2
        ⟨hδc hs hd1, hδc hs' hd2, hlt s hs s' hs' h2⟩
    exact (minkowski n).lt_mono (fun z hz => hball hz) hB

/-- **The straight segment** from `p` to `q`, `p ≪ q`, is a future chronal curve over `[0, 1]` of
every convex open set containing `p` and `q`. -/
theorem minkowski_chronalCurveOn_segment {W : Opens (Minkowski n)}
    (hW : Convex ℝ (W : Set (Minkowski n))) {p q : Minkowski n} (hp : p ∈ W) (hq : q ∈ W)
    (hpq : (minkowski n).lt ⊤ p q) :
    (minkowski n).ChronalCurveOn W (fun s => p + s • (q - p)) 0 1 := by
  refine minkowski_chronalCurveOn_iff.2 ⟨?_, fun s hs => hW.add_smul_sub_mem hp hq hs,
    fun s _ s' _ h => minkowski_lt_top_segment hpq h⟩
  exact (continuous_const.add (continuous_id.smul continuous_const)).continuousOn

/-! ### The homotopy -/

/-- **Route (a): the convex combination** `(1 − t)γ₀ + tγ₁` of two future chronal curves of a
convex open `W` with the same endpoints is a chronal homotopy with fixed endpoints in `W`. -/
theorem minkowski_chronalHomotopyOn_convexCombination {W : Opens (Minkowski n)}
    (hW : Convex ℝ (W : Set (Minkowski n))) {γ₀ γ₁ : ℝ → Minkowski n}
    (h₀ : (minkowski n).ChronalCurveOn W γ₀ 0 1) (h₁ : (minkowski n).ChronalCurveOn W γ₁ 0 1)
    (hp : γ₁ 0 = γ₀ 0) (hq : γ₁ 1 = γ₀ 1) :
    (minkowski n).ChronalHomotopyOn W (fun t s => (1 - t) • γ₀ s + t • γ₁ s) γ₀ γ₁ := by
  obtain ⟨c₀, -, l₀⟩ := minkowski_chronalCurveOn_iff.1 h₀
  obtain ⟨c₁, -, l₁⟩ := minkowski_chronalCurveOn_iff.1 h₁
  refine ⟨?_, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun s hs => ?_, fun s hs => ?_⟩
  · have hc : ContinuousOn (fun x : ℝ × ℝ => (1 - x.1) • γ₀ x.2 + x.1 • γ₁ x.2)
        (Icc 0 1 ×ˢ Icc 0 1) :=
      ((continuousOn_const.sub continuousOn_fst).smul
        (c₀.comp continuousOn_snd fun x hx => hx.2)).add
        (continuousOn_fst.smul (c₁.comp continuousOn_snd fun x hx => hx.2))
    exact hc
  · have h1t : 0 ≤ 1 - t := by linarith [ht.2]
    refine minkowski_chronalCurveOn_iff.2 ⟨(continuousOn_const.smul c₀).add
      (continuousOn_const.smul c₁), fun s hs => ?_, fun s hs s' hs' h => ?_⟩
    · exact hW (h₀.mem s hs) (h₁.mem s hs) h1t ht.1 (by ring)
    · exact minkowski_lt_top_convexCombination (l₀ s hs s' hs' h) (l₁ s hs s' hs' h) ht
  · show (1 - t) • γ₀ 0 + t • γ₁ 0 = γ₀ 0
    rw [hp, ← add_smul, sub_add_cancel, one_smul]
  · show (1 - t) • γ₀ 1 + t • γ₁ 1 = γ₀ 1
    rw [hq, ← add_smul, sub_add_cancel, one_smul]
  · show (1 - 0) • γ₀ s + (0 : ℝ) • γ₁ s = γ₀ s
    simp
  · show (1 - 1) • γ₀ s + (1 : ℝ) • γ₁ s = γ₁ s
    simp

/-- **Every convex open set of Minkowski space is future one-connected**
(`Causality.FutureOneConnectedOn`). -/
theorem minkowski_futureOneConnectedOn {W : Opens (Minkowski n)}
    (hW : Convex ℝ (W : Set (Minkowski n))) : (minkowski n).FutureOneConnectedOn W := by
  intro p q γ₀ γ₁ h₀ hp₀ hq₀ h₁ hp₁ hq₁
  exact ⟨_, minkowski_chronalHomotopyOn_convexCombination hW h₀ h₁ (hp₁.trans hp₀.symm)
    (hq₁.trans hq₀.symm)⟩

/-- **Minkowski space is future one-connected** (Sbierski `:835`): the ETT definition
`Causality.FutureOneConnected` for the model `minkowski n`, every `n`. -/
theorem minkowski_futureOneConnected : (minkowski n).FutureOneConnected := by
  refine minkowski_futureOneConnectedOn ?_
  rw [Opens.coe_top]
  exact convex_univ

/-- The time-reversed Minkowski causality is future one-connected on every convex open set. -/
theorem minkowski_dual_futureOneConnectedOn {W : Opens (Minkowski n)}
    (hW : Convex ℝ (W : Set (Minkowski n))) : (minkowski n).dual.FutureOneConnectedOn W := by
  exact Causality.dual_futureOneConnectedOn.2 (minkowski_futureOneConnectedOn hW)

/-- The time-reversed Minkowski causality is future one-connected. -/
theorem minkowski_dual_futureOneConnected : (minkowski n).dual.FutureOneConnected := by
  exact Causality.dual_futureOneConnected.2 minkowski_futureOneConnected

/-- **Sbierski Thm 3.1 Step 2.1** (`:567`): every future chronal curve `λ` of a convex open `W`
over `[0, 1]` is chronally homotopic in `W`, with fixed endpoints, to the straight segment from
`λ(0)` to `λ(1)` (the length maximising geodesic of `:570`; `W = ⊤` is Sbierski's `𝕄`). -/
theorem minkowski_chronallyHomotopicOn_segment {W : Opens (Minkowski n)}
    (hW : Convex ℝ (W : Set (Minkowski n))) {lam : ℝ → Minkowski n}
    (hlam : (minkowski n).ChronalCurveOn W lam 0 1) :
    (minkowski n).ChronallyHomotopicOn W lam (fun s => lam 0 + s • (lam 1 - lam 0)) := by
  have h01 : (minkowski n).lt ⊤ (lam 0) (lam 1) :=
    (minkowski n).lt_mono le_top (hlam.lt_of_lt le_rfl zero_lt_one le_rfl)
  have hσ := minkowski_chronalCurveOn_segment hW (hlam.mem 0 ⟨le_rfl, zero_le_one⟩)
    (hlam.mem 1 ⟨zero_le_one, le_rfl⟩) h01
  exact minkowski_futureOneConnectedOn hW (lam 0) (lam 1) lam _ hlam rfl rfl hσ
    (by simp) (by simp)

/-! ### Sbierski's printed homotopy -/

/-- **Sbierski's printed homotopy** (`:577`), `Γ(t, s) = (σ_{λ(t)} * λ|_{[t,1]})(s)` with
`σ_X(s) = s·X` and `λ|_{[t,1]}` rescaled linearly to `[0, 1]` (`:579`): `(2s)·λ(t)` for
`s ≤ 1/2`, `λ(t + (2s − 1)(1 − t))` for `s > 1/2`. -/
noncomputable def sbierskiPrintedHomotopy (lam : ℝ → Minkowski n) (t s : ℝ) : Minkowski n :=
  if s ≤ 1 / 2 then (2 * s) • lam t else lam (t + (2 * s - 1) * (1 - t))

/-- **The printed slice at `t = 0` is not a chronal curve**: with `λ(0) = 0` (`:575`) it is `0` on
`[0, 1/2]`, and a chronal curve of Minkowski space never pauses (`ChronalCurveOn.injOn`). Any
open set, any dimension. -/
theorem minkowski_not_chronalCurveOn_sbierskiPrinted_zero (lam : ℝ → Minkowski n)
    (hlam : lam 0 = 0) (W : Opens (Minkowski n)) :
    ¬ (minkowski n).ChronalCurveOn W (sbierskiPrintedHomotopy lam 0) 0 1 := by
  intro hc
  have hinj := hc.injOn fun x hx => by
    have := minkowski_lt_top_iff.1 ((minkowski n).lt_mono le_top hx)
    simp at this
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h12 : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have := hinj h0 h12 (by norm_num [sbierskiPrintedHomotopy, hlam])
  norm_num at this

/-- **The printed slice at `t = 1` is not a chronal curve**: it is `λ(1)` on `[1/2, 1]`. No
hypothesis on `λ`. -/
theorem minkowski_not_chronalCurveOn_sbierskiPrinted_one (lam : ℝ → Minkowski n)
    (W : Opens (Minkowski n)) :
    ¬ (minkowski n).ChronalCurveOn W (sbierskiPrintedHomotopy lam 1) 0 1 := by
  intro hc
  have hinj := hc.injOn fun x hx => by
    have := minkowski_lt_top_iff.1 ((minkowski n).lt_mono le_top hx)
    simp at this
  have h12 : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have := hinj h12 h1 (by norm_num [sbierskiPrintedHomotopy])
  norm_num at this

/-- **The printed homotopy is not a chronal homotopy**, in any open set of `ℝ^{1,n}`, between any
two curves, for every `λ` (its slice at `t = 1` pauses). -/
theorem minkowski_not_chronalHomotopyOn_sbierskiPrinted (lam : ℝ → Minkowski n)
    (W : Opens (Minkowski n)) (γ₀ γ₁ : ℝ → Minkowski n) :
    ¬ (minkowski n).ChronalHomotopyOn W (sbierskiPrintedHomotopy lam) γ₀ γ₁ := by
  intro h
  exact minkowski_not_chronalCurveOn_sbierskiPrinted_one lam W
    (h.chronalCurveOn 1 ⟨zero_le_one, le_rfl⟩)

/-! ### The corrected homotopy: split at `s = t` -/

/-- **Route (b), Sbierski's homotopy corrected**: split at `s = t` instead of `s = 1/2`,
`Γ(t, s) = λ(0) + (s/t)(λ(t) − λ(0))` for `s ≤ t` (the segment from `λ(0)` to `λ(t)`) and
`λ(s)` for `s > t`. At `t = 0` only `s = 0` is in the first piece, where `0/0 = 0` gives
`λ(0)`. -/
noncomputable def sbierskiSplitHomotopy (lam : ℝ → Minkowski n) (t s : ℝ) : Minkowski n :=
  if s ≤ t then lam 0 + (s / t) • (lam t - lam 0) else lam s

/-- Below the diagonal, the segment piece. -/
theorem sbierskiSplitHomotopy_of_le {lam : ℝ → Minkowski n} {t s : ℝ} (h : s ≤ t) :
    sbierskiSplitHomotopy lam t s = lam 0 + (s / t) • (lam t - lam 0) := if_pos h

/-- Strictly above the diagonal, the curve. -/
theorem sbierskiSplitHomotopy_of_lt {lam : ℝ → Minkowski n} {t s : ℝ} (h : t < s) :
    sbierskiSplitHomotopy lam t s = lam s := if_neg (not_le.2 h)

/-- On the diagonal the two pieces agree: `Γ(t, t) = λ(t)`. -/
theorem sbierskiSplitHomotopy_self (lam : ℝ → Minkowski n) (t : ℝ) :
    sbierskiSplitHomotopy lam t t = lam t := by
  rw [sbierskiSplitHomotopy_of_le le_rfl]
  rcases eq_or_ne t 0 with h | h
  · subst h; simp
  · rw [div_self h, one_smul, add_sub_cancel]

/-- Above the diagonal, `Γ(t, s) = λ(s)`, the diagonal included. -/
theorem sbierskiSplitHomotopy_of_ge {lam : ℝ → Minkowski n} {t s : ℝ} (h : t ≤ s) :
    sbierskiSplitHomotopy lam t s = lam s := by
  rcases h.eq_or_lt with h | h
  · subst h; exact sbierskiSplitHomotopy_self lam t
  · exact sbierskiSplitHomotopy_of_lt h

/-- **The split homotopy is jointly continuous on `[0, 1]²`**: `λ(s)` on `{t ≤ s}`; the segment
piece on `{s ≤ t}`, continuous where `t > 0`, and at the corner `(0, 0)` because
`‖(s/t)(λ(t) − λ(0))‖ ≤ ‖λ(t) − λ(0)‖`. -/
theorem continuousOn_sbierskiSplitHomotopy {lam : ℝ → Minkowski n}
    (hc : ContinuousOn lam (Icc 0 1)) :
    ContinuousOn (uncurry (sbierskiSplitHomotopy lam)) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := by
  let A : Set (ℝ × ℝ) := (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∩ {x | x.2 ≤ x.1}
  let B : Set (ℝ × ℝ) := (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∩ {x | x.1 ≤ x.2}
  have hAc : IsClosed A := (isClosed_Icc.prod isClosed_Icc).inter
    (isClosed_le continuous_snd continuous_fst)
  have hBc : IsClosed B := (isClosed_Icc.prod isClosed_Icc).inter
    (isClosed_le continuous_fst continuous_snd)
  have hsq : Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 ⊆ A ∪ B := fun x hx => by
    rcases le_total x.2 x.1 with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩
  have hB : ContinuousOn (uncurry (sbierskiSplitHomotopy lam)) B := by
    refine (hc.comp continuousOn_snd fun x hx => hx.1.2).congr fun x hx => ?_
    exact sbierskiSplitHomotopy_of_ge hx.2
  have hA : ContinuousOn (uncurry (sbierskiSplitHomotopy lam)) A := by
    intro x hx
    have hfst : ContinuousWithinAt (fun y : ℝ × ℝ => lam y.1) A x :=
      (hc x.1 hx.1.1).comp continuousWithinAt_fst fun y hy => hy.1.1
    rcases hx.1.1.1.lt_or_eq with h0 | h0
    · -- off the corner, `t > 0`
      have hdiv : ContinuousWithinAt (fun y : ℝ × ℝ => y.2 / y.1) A x :=
        (continuous_snd.continuousAt.div continuous_fst.continuousAt h0.ne').continuousWithinAt
      refine ((continuousWithinAt_const.add (hdiv.smul (hfst.sub continuousWithinAt_const))).congr
        (fun y hy => sbierskiSplitHomotopy_of_le hy.2) (sbierskiSplitHomotopy_of_le hx.2))
    · -- the corner `(0, 0)`
      have hx2 : x.2 = 0 := le_antisymm (h0 ▸ hx.2) hx.1.2.1
      have hx0 : x = (0, 0) := Prod.ext h0.symm hx2
      subst hx0
      have hv : uncurry (sbierskiSplitHomotopy lam) (0, 0) = lam 0 := sbierskiSplitHomotopy_self lam 0
      rw [ContinuousWithinAt, hv, Metric.tendsto_nhdsWithin_nhds]
      intro ε hε
      obtain ⟨δ, hδ, hδc⟩ := Metric.continuousWithinAt_iff.1 (hc 0 ⟨le_rfl, zero_le_one⟩) ε hε
      refine ⟨δ, hδ, fun y hy hyd => ?_⟩
      have ht : dist y.1 0 < δ := by
        have h' : dist y ((0 : ℝ), (0 : ℝ)) = max (dist y.1 0) (dist y.2 0) := Prod.dist_eq
        exact (le_max_left _ _).trans_lt (h' ▸ hyd)
      have hl := hδc hy.1.1 ht
      show dist (sbierskiSplitHomotopy lam y.1 y.2) (lam 0) < ε
      rw [sbierskiSplitHomotopy_of_le hy.2, dist_eq_norm, add_sub_cancel_left, norm_smul]
      rw [dist_eq_norm] at hl
      have hq : ‖y.2 / y.1‖ ≤ 1 := by
        rcases hy.1.1.1.lt_or_eq with h | h
        · rw [Real.norm_of_nonneg (div_nonneg hy.1.2.1 h.le), div_le_one h]; exact hy.2
        · rw [← h, div_zero, norm_zero]; exact zero_le_one
      calc ‖y.2 / y.1‖ * ‖lam y.1 - lam 0‖ ≤ 1 * ‖lam y.1 - lam 0‖ :=
            mul_le_mul_of_nonneg_right hq (norm_nonneg _)
        _ < ε := by rw [one_mul]; exact hl
  exact (hA.union_of_isClosed hB hAc hBc).mono hsq

/-- **Step 2.1 by Sbierski's own construction, corrected**: the split homotopy is a chronal
homotopy with fixed endpoints in every convex open `W`, from `λ` to the straight segment from
`λ(0)` to `λ(1)`. Each slice is the segment from `λ(0)` to `λ(t)`, then `λ`. -/
theorem minkowski_chronalHomotopyOn_sbierskiSplit {W : Opens (Minkowski n)}
    (hW : Convex ℝ (W : Set (Minkowski n))) {lam : ℝ → Minkowski n}
    (hlam : (minkowski n).ChronalCurveOn W lam 0 1) :
    (minkowski n).ChronalHomotopyOn W (sbierskiSplitHomotopy lam) lam
      (fun s => lam 0 + s • (lam 1 - lam 0)) := by
  obtain ⟨hc, hm, hl⟩ := minkowski_chronalCurveOn_iff.1 hlam
  have hΓ := continuousOn_sbierskiSplitHomotopy hc
  have hI0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  refine ⟨hΓ, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun s hs => ?_, fun s hs => ?_⟩
  · refine minkowski_chronalCurveOn_iff.2 ⟨?_, fun s hs => ?_, fun s hs s' hs' h => ?_⟩
    · exact hΓ.comp (continuousOn_const.prodMk continuousOn_id) fun s hs => ⟨ht, hs⟩
    · rcases le_or_gt s t with h | h
      · rw [sbierskiSplitHomotopy_of_le h]
        have hq : s / t ∈ Icc (0 : ℝ) 1 := by
          rcases ht.1.lt_or_eq with h0 | h0
          · exact ⟨div_nonneg hs.1 h0.le, (div_le_one h0).2 h⟩
          · rw [← h0, div_zero]; exact ⟨le_rfl, zero_le_one⟩
        exact hW.add_smul_sub_mem (hm hI0) (hm ht) hq
      · rw [sbierskiSplitHomotopy_of_lt h]; exact hm hs
    · rcases le_or_gt s' t with h' | h'
      · have ht0 : 0 < t := lt_of_le_of_lt hs.1 (h.trans_le h')
        rw [sbierskiSplitHomotopy_of_le (h.le.trans h'), sbierskiSplitHomotopy_of_le h']
        exact minkowski_lt_top_segment (hl 0 hI0 t ht ht0) ((div_lt_div_iff_of_pos_right ht0).2 h)
      · rw [sbierskiSplitHomotopy_of_lt h']
        have hlt : (minkowski n).lt ⊤ (lam t) (lam s') := hl t ht s' hs' h'
        rcases le_or_gt s t with h'' | h''
        · rcases h''.eq_or_lt with he | he
          · rw [he, sbierskiSplitHomotopy_self]; exact hlt
          · have ht0 : 0 < t := lt_of_le_of_lt hs.1 he
            rw [sbierskiSplitHomotopy_of_le h'']
            have := minkowski_lt_top_segment (hl 0 hI0 t ht ht0)
              (show s / t < 1 from (div_lt_one ht0).2 he)
            rw [one_smul, add_sub_cancel] at this
            exact (minkowski n).lt_trans this hlt
        · rw [sbierskiSplitHomotopy_of_lt h'']; exact hl s hs s' hs' h
  · show sbierskiSplitHomotopy lam t 0 = lam 0
    rw [sbierskiSplitHomotopy_of_le ht.1]; simp
  · exact sbierskiSplitHomotopy_of_ge ht.2
  · exact sbierskiSplitHomotopy_of_ge hs.1
  · show sbierskiSplitHomotopy lam 1 s = lam 0 + s • (lam 1 - lam 0)
    rw [sbierskiSplitHomotopy_of_le hs.2, div_one]

/-! ### The witness: Sbierski's identification applies to Minkowski space -/

/-- **Witness: the abstract identification applies to Minkowski space without restatement**
(`Causality.Iplus_inter_Iminus_eq_of_futureOneConnected`, Sbierski (1.2) with equality): for
`x ≪ y`, `I⁺(x) ∩ I⁻(y)` is the chronological diamond of every open `Ũ` containing
`J⁺(x) ∩ J⁻(y)`. The curve is the straight segment; the closure hypothesis holds because the
closed diamond is closed. -/
theorem minkowski_Iplus_inter_Iminus_eq_of_Jdiamond_subset {x y : Minkowski n}
    {Ũ : Opens (Minkowski n)} (hxy : (minkowski n).lt ⊤ x y)
    (hJ : (minkowski n).Jplus ⊤ {x} ∩ (minkowski n).Jminus ⊤ {y} ⊆ Ũ) :
    (minkowski n).Iplus ⊤ {x} ∩ (minkowski n).Iminus ⊤ {y} =
      (minkowski n).Iplus Ũ {x} ∩ (minkowski n).Iminus Ũ {y} := by
  have hU : Convex ℝ ((⊤ : Opens (Minkowski n)) : Set (Minkowski n)) := by
    rw [Opens.coe_top]; exact convex_univ
  have hγ := minkowski_chronalCurveOn_segment hU trivial trivial hxy
  refine Causality.Iplus_inter_Iminus_eq_of_futureOneConnected minkowski_causallyArcConnected
    minkowski_futureOneConnected hγ (by simp) (by simp) (fun s hs => hJ ⟨?_, ?_⟩) ?_
  · have := hγ.causalCurveOn.le_of_le le_rfl hs.1 hs.2
    simp only [zero_smul, add_zero] at this
    exact Precausality.mem_Jplus_singleton.2 this
  · have := hγ.causalCurveOn.le_of_le hs.1 hs.2 le_rfl
    simp only [one_smul, add_sub_cancel] at this
    exact Precausality.mem_Jminus_singleton.2 this
  · refine (((staticCausality.isClosed_Jplus_top x).inter
      (staticCausality.isClosed_Jminus_top y)).closure_subset_iff.2 ?_).trans hJ
    exact inter_subset_inter
      (((minkowski n).Iplus_mono_opens le_top).trans (minkowski n).Iplus_subset_Jplus)
      (((minkowski n).Iminus_mono_opens le_top).trans (minkowski n).Iminus_subset_Jminus)

/-- **Witness, the On form**: a convex open `W` of Minkowski space in the role of Sbierski's
embedded spacetime `ι(M)`, any open `Ũ` in the role of the chart domain. The diamond of `W` from
`x` to `y` is that of `W ⊓ Ũ` as soon as one chronal curve of `W` from `x` to `y` lies in `Ũ` and
the closure of the `Ũ`-diamond lies in `Ũ`
(`Causality.Iplus_inter_Iminus_eq_inf_of_futureOneConnectedOn`, no restatement). -/
theorem minkowski_Iplus_inter_Iminus_eq_inf_of_convex {W Ũ : Opens (Minkowski n)}
    (hW : Convex ℝ (W : Set (Minkowski n))) {γ : ℝ → Minkowski n} {x y : Minkowski n}
    (hγ : (minkowski n).ChronalCurveOn W γ 0 1) (hx : γ 0 = x) (hy : γ 1 = y)
    (hγŨ : MapsTo γ (Icc 0 1) Ũ)
    (hcl : closure ((minkowski n).Iplus Ũ {x} ∩ (minkowski n).Iminus Ũ {y}) ⊆ Ũ) :
    (minkowski n).Iplus W {x} ∩ (minkowski n).Iminus W {y} =
      (minkowski n).Iplus (W ⊓ Ũ) {x} ∩ (minkowski n).Iminus (W ⊓ Ũ) {y} :=
  Causality.Iplus_inter_Iminus_eq_inf_of_futureOneConnectedOn
    (minkowski_causallyArcConnected.mono le_top) (minkowski_futureOneConnectedOn hW) hγ hx hy hγŨ
    hcl

end Causal
