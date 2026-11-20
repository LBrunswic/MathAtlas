import Causal.Port.E0Model
import Causal.ArcConnected

/-!
# The causality of `E₀` from causal curves: the local relations, the curve causality, its calculus

Target `T-ett-port-e0` (DEC-134), the second of three modules. **No label is marked here.**
Cited, unmarked: `defi:causal_E0` — `ETT.tex:1344` (assembled and scoped in
`Causal.Port.E0Axioms`); the curve-defined causality is the one of `defi:causal_Ealpha`
— `ETT.tex:1336`, read at `α = 0`.

> The causal and chronological orders of $\mass{\alpha}$ give rise to a sheaf with values in
> $\mathbf{C}$: for $\U\subset \mass{\alpha}$ open and $x,y\in \U$, one sets $x\leq_\U y$ (resp.
> $x\ll_\U y$) if and only if there is a future causal (resp. chronological) curve from $x$ to $y$
> in $\U$. [...] and $I^\pm(x)$ is always an open --- possibly empty --- subset of $M$.
> (`ETT.tex:1336–1341`)

> For $\alpha=0$ the singular line is lightlike: locally causal, but not locally chronal. More
> precisely \cite[Section~1.2]{brunswic2021cauchy}, for a singular point $p\in \sing(\mass{0})$,
> $$I^-(p)=\emptyset \qquad\text{and}\qquad J^-(p)=\{\r=0,~\tau\leq \tau(p)\},$$
> that is, the causal past of $p$ is exactly the singular half-line below $p$. (`ETT.tex:1345–1348`)

**Ported from `lean-gx/GX/BTZ/Causality.lean` at commit `c48aa45`** (gx package WP-41e):
every declaration `GX.E0.x` of gx's l.359–457 (the local relations `Le`, `Lt` and their
transitivity), l.472–507 (`Lt.of_polar`, `Le.of_polar`), l.648–702 (`relOn`, segments as curves),
l.710–833 (constants, concatenation; `CLe`, `CLt`), l.871–882, l.889–966 and l.973–1102
(openness of `I^±_U`), l.1104–1286 (the causality, its calculus, the cones at a BTZ point) is `Causal.E0.x`
here, with gx's statement and proof character for character. The only changes: the import of
`Causal.Port.E0Model` (the rest of gx's range) in place of gx's; the two `variable`
lines gx declares earlier in its file are repeated; and two **new** theorems,
`le_iff_btzPaperDev`, `lt_iff_btzPaperDev` (the local relations are those of `𝐌³` on the
developments, through `E0Model`'s bridge).

## Contents

* **The local relations** `E0.Le`, `E0.Lt`: some developments of `x` and `y` (angles `θ₁`, `θ₂`,
  winding free) are causally (chronologically) related in `𝐌³` (`le_iff_btzPaperDev`); closed
  form `le_iff_closed`; transitive, push-up (`Lt.trans_le`, `Le.trans_lt`).
* **The causality** `E0.causality : Causality E0`: `x ≤_U y` (`x ≪_U y`) iff a future causal
  (chronological) curve joins them in `U` (`CLe`, `CLt`, curves of `Causal.Curves` for the local
  relations); `I^±_U(x)` open in every `U` (`isOpen_CLt_right`, `isOpen_CLt_left`, BTZ points
  included); globally `≤ = Le`, `≪ = Lt` (`le_top_iff`, `lt_top_iff`).
* **The calculus** `0 ≤ Δr ≤ 2Δτ`, `τ, r, f, h` non-decreasing along `≤_U` (`calculus_le`),
  strictly along `≪_U` (`calculus_lt`).
* **At a BTZ point `p`**: `J^+(p) = {f ≥ τ_p}` (`Jplus_axis`), `I^+(p) = {r > 0, f > τ_p}`
  (`Iplus_axis`, and in every ball `Iplus_ball_axis`), `J^-(p) = {r = 0, τ ≤ τ_p}`
  (`Jminus_axis`), `I^-_U(p) = ∅` for every open `U` (`Iminus_axis`), `J^-_U(p) ⊂ sing₀`
  (`Jminus_axis_subset`).

## Hypothesis checklist

| paper | here |
|---|---|
| `≤_U`, `≪_U` by future causal / chronological curves in `U` (l.1336–1339) | ⚠ read: `CLe`, `CLt`, `Causal.CurveOn` for the local relations (DEC-33, as gx reads it; SCOPE (a)), a question |
| "future causal curve" of `E₀` (not defined by the paper) | ⚠ read: locally `Le`-increasing (some developments causally related in `𝐌³`), DEC-6's curves (SCOPE (a)), a question |
| `I^±(x)` open | ✓ in every open `U`, BTZ points included |
| `I^-(p) = ∅`, `J^-(p) = {r = 0, τ ≤ τ(p)}` (l.1347) | ✓ `Iminus_axis` (every `U`), `Jminus_axis` (`U = E₀`) |

## SCOPE (disclosed)

* **(a) Reading of "future causal curve" in `E₀`** (gx's, DEC-33): the paper defines the
  causality of the model spaces by curves (l.1336–1339) without saying which curves are causal in
  `E₀`. A curve is causal when it is `Causal.CurveOn` for the local relation `Le`: near every
  parameter, later points have developments in the closed future cone of earlier ones in `𝐌³`
  (with the winding free, `𝔼₀ = ⟨P⟩\J⁺(Δ)` in gx's terms). This is the causal-curve notion of
  the `(G,X)`-structure (charts are developments, `E0Model`'s `btzPaperDev`), extended over the
  axis by continuity; it is not derived from a Lorentzian metric (there is none here).
* **(b) Globally `≤ = Le`** (`le_top_iff`): a causal pair of developments is realised by a
  straight segment of `𝐌³`, which never crosses the axis transversally; inside a smaller open
  `U` the curve must stay in `U`, and that is the content of `CLe U`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Ported from
`lean-gx/GX/BTZ/Causality.lean` at `c48aa45` (target `T-ett-port-e0`, DEC-134).
-/

namespace Causal

open Set Filter Topology Function Complex
open scoped Real

namespace E0

variable {x y z : E0} {θ θ' θ₁ θ₂ θ₃ : ℝ}

/-- **`x ≼ y` in `𝔼₀`**: some developments of `x` and `y` (angles `θ₁`, `θ₂`) are causally related
in `𝐌³`; the winding `θ₂ − θ₁` is free (`𝔼₀ = ⟨P⟩\J⁺(Δ)`). -/
def Le (x y : E0) : Prop :=
  ∃ θ₁ θ₂, Polar x θ₁ ∧ Polar y θ₂ ∧ NullCone (lift y θ₂ - lift x θ₁)

/-- **`x ≺ y` in `𝔼₀`**: some developments are chronologically related. -/
def Lt (x y : E0) : Prop :=
  ∃ θ₁ θ₂, Polar x θ₁ ∧ Polar y θ₂ ∧ NullConeLt (lift y θ₂ - lift x θ₁)

/-- **`x ≼ y` iff some developments of `x` and `y` are causally related in `𝐌³`** (new): the
paper's developing map `D = btzPaperDev` at angles `θ₁`, `θ₂` of `x`, `y`, and the causality
`Causal.minkowski 2`. -/
theorem le_iff_btzPaperDev : Le x y ↔ ∃ θ₁ θ₂, Polar x θ₁ ∧ Polar y θ₂ ∧
    (minkowski 2).le ⊤ (btzPaperDev (x.1, rad x, θ₁)) (btzPaperDev (y.1, rad y, θ₂)) := by
  simp only [Le, btzPaperDev_eq_nullToMink, ← nullCone_sub_iff_le, lift]

/-- **`x ≺ y` iff some developments of `x` and `y` are chronologically related in `𝐌³`** (new). -/
theorem lt_iff_btzPaperDev : Lt x y ↔ ∃ θ₁ θ₂, Polar x θ₁ ∧ Polar y θ₂ ∧
    (minkowski 2).lt ⊤ (btzPaperDev (x.1, rad x, θ₁)) (btzPaperDev (y.1, rad y, θ₂)) := by
  simp only [Lt, btzPaperDev_eq_nullToMink, ← nullConeLt_sub_iff_lt, lift]


theorem le_iff_closed : Le x y ↔
    ∃ θ₁ θ₂, Polar x θ₁ ∧ Polar y θ₂ ∧ ClosedLe x.1 (rad x) y.1 (rad y) (θ₂ - θ₁) := by
  simp only [Le, nullCone_lift_iff]

theorem lt_iff_closed : Lt x y ↔
    ∃ θ₁ θ₂, Polar x θ₁ ∧ Polar y θ₂ ∧ ClosedLt x.1 (rad x) y.1 (rad y) (θ₂ - θ₁) := by
  simp only [Lt, nullConeLt_lift_iff]

theorem Lt.le (h : Lt x y) : Le x y := by
  obtain ⟨θ₁, θ₂, h₁, h₂, h⟩ := h
  exact ⟨θ₁, θ₂, h₁, h₂, h.nullCone⟩

theorem le_refl' (x : E0) : Le x x :=
  ⟨arg x.2, arg x.2, polar_arg x, polar_arg x, by rw [sub_self]; exact nullCone_zero⟩

theorem Le.closed (h : Le x y) :
    x.1 ≤ y.1 ∧ rad x ≤ rad y ∧ 0 ≤ (rad y - rad x) * (2 * (y.1 - x.1) - (rad y - rad x)) := by
  obtain ⟨θ₁, θ₂, -, -, h⟩ := le_iff_closed.1 h
  have : 0 ≤ rad x * rad y * (θ₂ - θ₁) ^ 2 := by
    have := rad_nonneg x; have := rad_nonneg y; positivity
  exact ⟨h.1, h.2.1, this.trans h.2.2⟩

theorem Lt.closed (h : Lt x y) :
    rad x < rad y ∧ 0 < (rad y - rad x) * (2 * (y.1 - x.1) - (rad y - rad x)) := by
  obtain ⟨θ₁, θ₂, -, -, h⟩ := lt_iff_closed.1 h
  have : 0 ≤ rad x * rad y * (θ₂ - θ₁) ^ 2 := by
    have := rad_nonneg x; have := rad_nonneg y; positivity
  exact ⟨h.1, this.trans_lt h.2⟩

/-- Re-choosing the angle of the source: `Le y z` holds with any prescribed angle of `y` when `y`
is off the axis. -/
theorem Le.realign (h : Le y z) (hy : Polar y θ) (hr : 0 < rad y) :
    ∃ θ', Polar z θ' ∧ NullCone (lift z θ' - lift y θ) := by
  obtain ⟨θ₂, θ₃, h₂, h₃, h⟩ := h
  obtain ⟨k, hk⟩ := h₂.eq_add_int hy hr
  refine ⟨θ₃ + 2 * π * k, h₃.add_int k, ?_⟩
  rw [nullCone_lift_iff] at h ⊢
  rwa [hk, show θ₃ + 2 * π * k - (θ₂ + 2 * π * k) = θ₃ - θ₂ by ring]

theorem Lt.realign (h : Lt y z) (hy : Polar y θ) (hr : 0 < rad y) :
    ∃ θ', Polar z θ' ∧ NullConeLt (lift z θ' - lift y θ) := by
  obtain ⟨θ₂, θ₃, h₂, h₃, h⟩ := h
  obtain ⟨k, hk⟩ := h₂.eq_add_int hy hr
  refine ⟨θ₃ + 2 * π * k, h₃.add_int k, ?_⟩
  rw [nullConeLt_lift_iff] at h ⊢
  rwa [hk, show θ₃ + 2 * π * k - (θ₂ + 2 * π * k) = θ₃ - θ₂ by ring]

theorem lift_sub_add (x y z : E0) (θ₁ θ₂ θ₃ : ℝ) :
    lift z θ₃ - lift x θ₁ = (lift z θ₃ - lift y θ₂) + (lift y θ₂ - lift x θ₁) := by abel

theorem Le.trans (h₁ : Le x y) (h₂ : Le y z) : Le x z := by
  obtain ⟨θ₁, θ₂, hx, hy, h⟩ := h₁
  rcases (rad_nonneg y).lt_or_eq with hr | hr
  · obtain ⟨θ₃, hz, h'⟩ := h₂.realign hy hr
    exact ⟨θ₁, θ₃, hx, hz, lift_sub_add x y z θ₁ θ₂ θ₃ ▸ h'.add h⟩
  · have hc := Le.closed ⟨θ₁, θ₂, hx, hy, h⟩
    obtain ⟨θ₂', θ₃, -, hz, h''⟩ := le_iff_closed.1 h₂
    have hx0 : rad x = 0 := le_antisymm (hr ▸ hc.2.1) (rad_nonneg x)
    refine le_iff_closed.2 ⟨θ₁, θ₃, hx, hz, ?_⟩
    obtain ⟨hτ, hrz, hq⟩ := h''
    rw [← hr] at hq hrz
    rw [hx0]
    refine ⟨hc.1.trans hτ, rad_nonneg z, ?_⟩
    have := rad_nonneg z
    simp only [zero_mul, sub_zero] at hq ⊢
    nlinarith [hc.1]

theorem Lt.trans_le (h₁ : Lt x y) (h₂ : Le y z) : Lt x z := by
  obtain ⟨θ₁, θ₂, hx, hy, h⟩ := h₁
  have hr : 0 < rad y := (rad_nonneg x).trans_lt (Lt.closed ⟨θ₁, θ₂, hx, hy, h⟩).1
  obtain ⟨θ₃, hz, h'⟩ := h₂.realign hy hr
  exact ⟨θ₁, θ₃, hx, hz, lift_sub_add x y z θ₁ θ₂ θ₃ ▸ h'.add_nullConeLt h⟩

theorem Le.trans_lt (h₁ : Le x y) (h₂ : Lt y z) : Lt x z := by
  obtain ⟨θ₁, θ₂, hx, hy, h⟩ := h₁
  rcases (rad_nonneg y).lt_or_eq with hr | hr
  · obtain ⟨θ₃, hz, h'⟩ := h₂.realign hy hr
    exact ⟨θ₁, θ₃, hx, hz, lift_sub_add x y z θ₁ θ₂ θ₃ ▸ h'.add_nullCone h⟩
  · have hc := Le.closed ⟨θ₁, θ₂, hx, hy, h⟩
    obtain ⟨θ₂', θ₃, -, hz, h''⟩ := lt_iff_closed.1 h₂
    have hx0 : rad x = 0 := le_antisymm (hr ▸ hc.2.1) (rad_nonneg x)
    refine lt_iff_closed.2 ⟨θ₁, θ₃, hx, hz, ?_⟩
    obtain ⟨hrz, hq⟩ := h''
    rw [← hr] at hq hrz
    rw [hx0]
    refine ⟨hrz, ?_⟩
    simp only [zero_mul, sub_zero] at hq ⊢
    nlinarith [hc.1]

theorem Lt.trans (h₁ : Lt x y) (h₂ : Lt y z) : Lt x z := h₁.trans_le h₂.le

/-- With angles less than `π` apart, the relation `Lt` is read on those very angles. -/
theorem Lt.of_polar (h : Lt x y) (hx : Polar x θ₁) (hy : Polar y θ₂) (hθ : |θ₂ - θ₁| ≤ π) :
    NullConeLt (lift y θ₂ - lift x θ₁) := by
  obtain ⟨θ₁', θ₂', hx', hy', h⟩ := h
  rw [nullConeLt_lift_iff] at h ⊢
  obtain ⟨hr, hq⟩ := h
  refine ⟨hr, lt_of_le_of_lt ?_ hq⟩
  rcases (rad_nonneg x).lt_or_eq with hx0 | hx0
  · obtain ⟨k₁, hk₁⟩ := hx.eq_add_int hx' hx0
    obtain ⟨k₂, hk₂⟩ := hy.eq_add_int hy' (hx0.trans hr)
    have hd : θ₂' - θ₁' = (θ₂ - θ₁) + 2 * π * ((k₂ - k₁ : ℤ) : ℝ) := by
      rw [hk₁, hk₂]; push_cast; ring
    have habs := abs_le_abs_add_two_pi_mul hθ (k₂ - k₁)
    rw [← hd] at habs
    have : (θ₂ - θ₁) ^ 2 ≤ (θ₂' - θ₁') ^ 2 := sq_le_sq.2 habs
    have : 0 ≤ rad x * rad y := mul_nonneg (rad_nonneg x) (rad_nonneg y)
    exact mul_le_mul_of_nonneg_left (by assumption) this
  · rw [← hx0]; simp

theorem Le.of_polar (h : Le x y) (hx : Polar x θ₁) (hy : Polar y θ₂) (hθ : |θ₂ - θ₁| ≤ π) :
    NullCone (lift y θ₂ - lift x θ₁) := by
  obtain ⟨θ₁', θ₂', hx', hy', h⟩ := h
  rw [nullCone_lift_iff] at h ⊢
  obtain ⟨hτ, hr, hq⟩ := h
  refine ⟨hτ, hr, le_trans ?_ hq⟩
  rcases (rad_nonneg x).lt_or_eq with hx0 | hx0
  · obtain ⟨k₁, hk₁⟩ := hx.eq_add_int hx' hx0
    obtain ⟨k₂, hk₂⟩ := hy.eq_add_int hy' (hx0.trans_le hr)
    have hd : θ₂' - θ₁' = (θ₂ - θ₁) + 2 * π * ((k₂ - k₁ : ℤ) : ℝ) := by
      rw [hk₁, hk₂]; push_cast; ring
    have habs := abs_le_abs_add_two_pi_mul hθ (k₂ - k₁)
    rw [← hd] at habs
    have : (θ₂ - θ₁) ^ 2 ≤ (θ₂' - θ₁') ^ 2 := sq_le_sq.2 habs
    have : 0 ≤ rad x * rad y := mul_nonneg (rad_nonneg x) (rad_nonneg y)
    exact mul_le_mul_of_nonneg_left (by assumption) this
  · rw [← hx0]; simp

variable {P Q R : ℝ × ℝ × ℝ}

/-- The relation `R` restricted to the open set `N` (the family the curves of `Causal.Curves` are
taken for). -/
def relOn (R : E0 → E0 → Prop) (N : TopologicalSpace.Opens E0) (x y : E0) : Prop :=
  x ∈ N ∧ y ∈ N ∧ R x y

theorem isRelFamily_relOn {R : E0 → E0 → Prop} (hR : ∀ {x y z}, R x y → R y z → R x z) :
    Causal.IsRelFamily (relOn R) where
  mem_left h := h.1
  mem_right h := h.2.1
  trans h₁ h₂ := ⟨h₁.1, h₂.2.1, hR h₁.2.2 h₂.2.2⟩
  mono hN _ _ h := ⟨hN h.1, hN h.2.1, h.2.2⟩

/-- A continuous curve, `R`-increasing on `[a, b]`, is a curve of every open set containing it. -/
theorem curveOn_of_continuousOn {R : E0 → E0 → Prop} {W : TopologicalSpace.Opens E0}
    {c : ℝ → E0} {a b : ℝ} (hc : ContinuousOn c (Icc a b)) (hmem : ∀ t ∈ Icc a b, c t ∈ W)
    (hR : ∀ s ∈ Icc a b, ∀ s' ∈ Icc a b, s < s' → R (c s) (c s')) :
    Causal.CurveOn (relOn R) W c a b where
  mem := hmem
  rel t ht N _ htN := by
    have hN : c ⁻¹' N ∈ 𝓝[Icc a b] t := hc t ht (N.isOpen.mem_nhds htN)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hN
    refine ⟨t - ε, t + ε, by linarith, by linarith, fun s hs s' hs' h1 h2 h3 => ?_⟩
    have hsb : s ∈ Metric.ball t ε := by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith
    have hs'b : s' ∈ Metric.ball t ε := by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith
    exact ⟨hball ⟨hsb, hs⟩, hball ⟨hs'b, hs'⟩, hR s hs s' hs' h2⟩

theorem le_unlift_seg (hP : Adm P) (hPQ : NullCone (Q - P)) {s s' : ℝ} (hs : 0 ≤ s)
    (hss' : s ≤ s') : Le (unlift (seg P Q s)) (unlift (seg P Q s')) := by
  have h₁ := adm_seg hP hPQ hs
  have h₂ := adm_seg hP hPQ (hs.trans hss')
  refine ⟨_, _, polar_unlift h₁.nonneg, polar_unlift h₂.nonneg, ?_⟩
  rw [lift_unlift h₁, lift_unlift h₂, seg_sub]
  exact hPQ.smul (sub_nonneg.2 hss')

theorem lt_unlift_seg (hP : Adm P) (hPQ : NullConeLt (Q - P)) {s s' : ℝ} (hs : 0 ≤ s)
    (hss' : s < s') : Lt (unlift (seg P Q s)) (unlift (seg P Q s')) := by
  have h₁ := adm_seg hP hPQ.nullCone hs
  have h₂ := adm_seg hP hPQ.nullCone (hs.trans hss'.le)
  refine ⟨_, _, polar_unlift h₁.nonneg, polar_unlift h₂.nonneg, ?_⟩
  rw [lift_unlift h₁, lift_unlift h₂, seg_sub]
  exact hPQ.smul (sub_pos.2 hss')

/-- **A straight causal segment of `𝐌³` is a future causal curve of `𝔼₀`.** -/
theorem curveOn_unlift_seg (hP : Adm P) (hPQ : NullCone (Q - P)) {W : TopologicalSpace.Opens E0}
    (hW : ∀ s ∈ Icc (0 : ℝ) 1, unlift (seg P Q s) ∈ W) :
    Causal.CurveOn (relOn Le) W (fun s => unlift (seg P Q s)) 0 1 :=
  curveOn_of_continuousOn (continuousOn_unlift_seg hP hPQ) hW
    fun _ hs _ _ h => le_unlift_seg hP hPQ hs.1 h.le

/-- **A straight chronological segment of `𝐌³` is a future chronological curve of `𝔼₀`.** -/
theorem curveOn_unlift_seg_lt (hP : Adm P) (hPQ : NullConeLt (Q - P))
    {W : TopologicalSpace.Opens E0} (hW : ∀ s ∈ Icc (0 : ℝ) 1, unlift (seg P Q s) ∈ W) :
    Causal.CurveOn (relOn Lt) W (fun s => unlift (seg P Q s)) 0 1 :=
  curveOn_of_continuousOn (continuousOn_unlift_seg hP hPQ.nullCone) hW
    fun _ hs _ _ h => lt_unlift_seg hP hPQ hs.1 h

/-! ### Curves: constants, concatenation -/

section Curves

open TopologicalSpace

variable {r r' : Opens E0 → E0 → E0 → Prop} {U W : Opens E0} {c c' : ℝ → E0} {a b a' b' : ℝ}

theorem curveOn_const (hx : x ∈ U) : Causal.CurveOn r U (fun _ => x) 0 0 where
  mem _ _ := hx
  rel t _ _ _ _ := ⟨t - 1, t + 1, by linarith, by linarith, fun s hs s' hs' _ h _ => by
    have : s = s' := by rw [hs.1.antisymm' hs.2, hs'.1.antisymm' hs'.2]
    exact absurd this h.ne⟩

theorem curveOn_mono_rel (h : ∀ N x y, r N x y → r' N x y) (hc : Causal.CurveOn r W c a b) :
    Causal.CurveOn r' W c a b where
  mem := hc.mem
  rel t ht N hN htN := by
    obtain ⟨l, u, hl, hu, h'⟩ := hc.rel t ht N hN htN
    exact ⟨l, u, hl, hu, fun s hs s' hs' h1 h2 h3 => h _ _ _ (h' s hs s' hs' h1 h2 h3)⟩

/-- Concatenation of two curves, the second translated to start where the first ends. -/
theorem curve_append (hr : Causal.IsRelFamily r) (hc : Causal.CurveOn r U c a b) (hc' : Causal.CurveOn r U c' a' b')
    (hab : a ≤ b) (hab' : a' ≤ b') (h : c b = c' a') :
    ∃ d : ℝ → E0, Causal.CurveOn r U d a (b + (b' - a')) ∧ d a = c a ∧ d (b + (b' - a')) = c' b' := by
  have e1 : 1 * b + (a' - b) = a' := by ring
  have e2 : 1 * (b + (b' - a')) + (a' - b) = b' := by ring
  have hc'' : Causal.CurveOn r U (fun t => c' (1 * t + (a' - b))) b (b + (b' - a')) :=
    Causal.CurveOn.comp_affine (k := 1) (m := a' - b) one_pos (by rw [e1, e2]; exact hc')
  have hj : c b = (fun t => c' (1 * t + (a' - b))) b := by simp only; rw [e1]; exact h
  refine ⟨_, Causal.CurveOn.concat hr hc hc'' hab (by linarith) hj, by simp [hab], ?_⟩
  by_cases hb : b + (b' - a') ≤ b
  · have : b' = a' := le_antisymm (by linarith) hab'
    subst this
    simp only [sub_self, add_zero, le_refl, if_true]
    exact h
  · simp only [hb, if_false]; rw [e2]

end Curves

/-! ### The causality of `𝔼₀` -/

section Causal.Causality

open TopologicalSpace

/-- `x ≤_U y` (`defi:causal_Ealpha`, `RamcovGX.tex:2215`, DEC-33): a future causal curve of `U` from
`x` to `y` — a continuous curve along which the developed points are causally related, the
local relation being `Le` (some development of the two points is causally related in `𝐌³`). -/
def CLe (U : Opens E0) (x y : E0) : Prop :=
  ∃ a b : ℝ, a ≤ b ∧ ∃ c : ℝ → E0, Causal.CurveOn (relOn Le) U c a b ∧ c a = x ∧ c b = y

/-- `x ≪_U y`: a future chronological curve of `U` over a non-trivial segment. -/
def CLt (U : Opens E0) (x y : E0) : Prop :=
  ∃ a b : ℝ, a < b ∧ ∃ c : ℝ → E0, Causal.CurveOn (relOn Lt) U c a b ∧ c a = x ∧ c b = y

theorem isRelFamily_le : Causal.IsRelFamily (relOn Le) := isRelFamily_relOn Le.trans

theorem isRelFamily_lt : Causal.IsRelFamily (relOn Lt) := isRelFamily_relOn Lt.trans

variable {U V : Opens E0}

theorem CLe.le (h : CLe U x y) : Le x y := by
  obtain ⟨a, b, hab, c, hc, rfl, rfl⟩ := h
  rcases hab.lt_or_eq with hab | hab
  · exact (hc.rel_of_lt isRelFamily_le le_rfl hab le_rfl).2.2
  · rw [hab]; exact le_refl' _

theorem CLt.lt (h : CLt U x y) : Lt x y := by
  obtain ⟨a, b, hab, c, hc, rfl, rfl⟩ := h
  exact (hc.rel_of_lt isRelFamily_lt le_rfl hab le_rfl).2.2

theorem CLe.mem_left (h : CLe U x y) : x ∈ U := by
  obtain ⟨a, b, hab, c, hc, rfl, -⟩ := h; exact hc.mem a ⟨le_rfl, hab⟩

theorem CLe.mem_right (h : CLe U x y) : y ∈ U := by
  obtain ⟨a, b, hab, c, hc, -, rfl⟩ := h; exact hc.mem b ⟨hab, le_rfl⟩

theorem CLt.cle (h : CLt U x y) : CLe U x y := by
  obtain ⟨a, b, hab, c, hc, h1, h2⟩ := h
  exact ⟨a, b, hab.le, c, curveOn_mono_rel (fun _ _ _ h => ⟨h.1, h.2.1, h.2.2.le⟩) hc, h1, h2⟩

theorem CLe.refl (hx : x ∈ U) : CLe U x x := ⟨0, 0, le_rfl, _, curveOn_const hx, rfl, rfl⟩

theorem CLe.trans (h₁ : CLe U x y) (h₂ : CLe U y z) : CLe U x z := by
  obtain ⟨a, b, hab, c, hc, rfl, rfl⟩ := h₁
  obtain ⟨a', b', hab', c', hc', h1, rfl⟩ := h₂
  obtain ⟨d, hd, hda, hdb⟩ := curve_append isRelFamily_le hc hc' hab hab' h1.symm
  exact ⟨a, _, by linarith, d, hd, hda, hdb⟩

theorem CLt.trans (h₁ : CLt U x y) (h₂ : CLt U y z) : CLt U x z := by
  obtain ⟨a, b, hab, c, hc, rfl, rfl⟩ := h₁
  obtain ⟨a', b', hab', c', hc', h1, rfl⟩ := h₂
  obtain ⟨d, hd, hda, hdb⟩ := curve_append isRelFamily_lt hc hc' hab.le hab'.le h1.symm
  exact ⟨a, _, by linarith, d, hd, hda, hdb⟩

theorem CLe.mono (hVU : V ≤ U) (h : CLe V x y) : CLe U x y := by
  obtain ⟨a, b, hab, c, hc, h1, h2⟩ := h
  exact ⟨a, b, hab, c, hc.mono_opens isRelFamily_le hVU, h1, h2⟩

theorem CLt.mono (hVU : V ≤ U) (h : CLt V x y) : CLt U x y := by
  obtain ⟨a, b, hab, c, hc, h1, h2⟩ := h
  exact ⟨a, b, hab, c, hc.mono_opens isRelFamily_lt hVU, h1, h2⟩

/-- The straight segment between two developments, as a causal curve from `x` to `y`. -/
theorem cle_of_seg (hx : Polar x θ₁) (hy : Polar y θ₂) (h : NullCone (lift y θ₂ - lift x θ₁))
    (hU : ∀ s ∈ Icc (0 : ℝ) 1, unlift (seg (lift x θ₁) (lift y θ₂) s) ∈ U) : CLe U x y :=
  ⟨0, 1, zero_le_one, _, curveOn_unlift_seg (adm_lift x θ₁) h hU,
    by simp only [seg_zero, unlift_lift hx], by simp only [seg_one, unlift_lift hy]⟩

theorem clt_of_seg (hx : Polar x θ₁) (hy : Polar y θ₂) (h : NullConeLt (lift y θ₂ - lift x θ₁))
    (hU : ∀ s ∈ Icc (0 : ℝ) 1, unlift (seg (lift x θ₁) (lift y θ₂) s) ∈ U) : CLt U x y :=
  ⟨0, 1, zero_lt_one, _, curveOn_unlift_seg_lt (adm_lift x θ₁) h hU,
    by simp only [seg_zero, unlift_lift hx], by simp only [seg_one, unlift_lift hy]⟩

/-- **Globally, `x ≤ y ⟺ Le x y`**: a causal relation of developments is realised by a straight
segment. -/
theorem cle_top_iff : CLe ⊤ x y ↔ Le x y := by
  refine ⟨CLe.le, fun ⟨θ₁, θ₂, hx, hy, h⟩ => cle_of_seg hx hy h fun _ _ => trivial⟩

theorem clt_top_iff : CLt ⊤ x y ↔ Lt x y := by
  refine ⟨CLt.lt, fun ⟨θ₁, θ₂, hx, hy, h⟩ => clt_of_seg hx hy h fun _ _ => trivial⟩

end Causal.Causality

/-! ### Openness of the chronological relation -/

section Open

open TopologicalSpace


/-- **Balls centred on the axis are order-convex**: `w₁ ≼ w ≼ w₂` with `w₁, w₂` in the ball puts
`w` in it (`τ` and `r` are monotone, and the ball is `{|τ − τ_x| < δ, r < δ}`). -/
theorem mem_ball_of_le_of_le {δ : ℝ} {w₁ w w₂ : E0} (hx : x ∈ axis) (h₁ : Le w₁ w) (h₂ : Le w w₂)
    (hw₁ : w₁ ∈ Metric.ball x δ) (hw₂ : w₂ ∈ Metric.ball x δ) : w ∈ Metric.ball x δ := by
  have hx0 : x.2 = 0 := hx
  have c₁ := h₁.closed
  have c₂ := h₂.closed
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff] at hw₁ hw₂ ⊢
  rw [Real.dist_eq, abs_lt] at hw₁ hw₂ ⊢
  simp only [hx0, dist_zero_right] at hw₁ hw₂ ⊢
  have : ‖w.2‖ ≤ ‖w₂.2‖ := c₂.2.1
  exact ⟨⟨by linarith [c₁.1], by linarith [c₂.1]⟩, this.trans_lt hw₂.2⟩

/-- A point of a segment, read in `𝔼₀`, lies between its ends. -/
theorem le_seg_ends (hP : Adm P) (hPQ : NullCone (Q - P)) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    Le (unlift P) (unlift (seg P Q s)) ∧ Le (unlift (seg P Q s)) (unlift Q) := by
  have h0 := le_unlift_seg hP hPQ le_rfl hs.1
  have h1 := le_unlift_seg hP hPQ hs.1 hs.2
  rw [seg_zero] at h0
  rw [seg_one] at h1
  exact ⟨h0, h1⟩

/-- **`I⁺_U(x)` is open.** -/
theorem isOpen_CLt_right (U : Opens E0) (x : E0) : IsOpen {y | CLt U x y} := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨a, b, hab, c, hc, rfl, rfl⟩
  have hLt : Lt (c a) (c b) := (hc.rel_of_lt isRelFamily_lt le_rfl hab le_rfl).2.2
  have hry : 0 < rad (c b) := (rad_nonneg _).trans_lt hLt.closed.1
  have hy0 : (c b).2 ≠ 0 := norm_pos_iff.1 hry
  set Q := lift (c b) (arg (c b).2) with hQdef
  have hQy : unlift Q = c b := unlift_lift (polar_arg _)
  have hQb : 0 < Q.2.1 := hry
  -- a ball around `Q` read inside `U`, off the axis
  have hUQ : unlift ⁻¹' U ∩ {R | 0 < R.2.1} ∈ 𝓝 Q := by
    refine Filter.inter_mem ((continuousAt_unlift hQb.ne').preimage_mem_nhds ?_)
      ((isOpen_lt continuous_const continuous_snd.fst).mem_nhds hQb)
    rw [hQy]; exact U.isOpen.mem_nhds (hc.mem b ⟨hab.le, le_rfl⟩)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hUQ
  -- a point `z = c s₀` of the curve just before `b`, with `locLift z` near `Q`
  have hφ := continuousAt_locLift (c b) hy0
  rw [ContinuousAt, locLift_self _ hy0] at hφ
  have hpre : c ⁻¹' (locLift (c b) ⁻¹' Metric.ball Q (ε / 2)) ∈ 𝓝[Icc a b] b :=
    (hc.continuousOn isRelFamily_lt) b ⟨hab.le, le_rfl⟩ (hφ (Metric.ball_mem_nhds Q (by linarith)))
  obtain ⟨δ₁, hδ₁, hδball⟩ := Metric.mem_nhdsWithin_iff.1 hpre
  obtain ⟨l, u, hl, hu, hrel⟩ := hc.rel b ⟨hab.le, le_rfl⟩ U le_rfl (hc.mem b ⟨hab.le, le_rfl⟩)
  set s₀ := (max (max a l) (b - δ₁) + b) / 2 with hs₀
  have hs₀b : s₀ < b := by
    have : max (max a l) (b - δ₁) < b := max_lt (max_lt hab hl) (by linarith)
    rw [hs₀]; linarith
  have hs₀a : a ≤ s₀ := by
    have : a ≤ max (max a l) (b - δ₁) := (le_max_left _ _).trans (le_max_left _ _)
    rw [hs₀]; linarith
  have hs₀l : l < s₀ := by
    have : l ≤ max (max a l) (b - δ₁) := (le_max_right _ _).trans (le_max_left _ _)
    rw [hs₀]; linarith
  have hs₀δ : b - δ₁ < s₀ := by
    have : b - δ₁ ≤ max (max a l) (b - δ₁) := le_max_right _ _
    rw [hs₀]; linarith
  have hs₀mem : s₀ ∈ Icc a b := ⟨hs₀a, hs₀b.le⟩
  have hzy : Lt (c s₀) (c b) := (hrel s₀ hs₀mem b ⟨hab.le, le_rfl⟩ hs₀l hs₀b hu).2.2
  set P := locLift (c b) (c s₀) with hPdef
  have hPball : P ∈ Metric.ball Q (ε / 2) := by
    refine hδball ⟨?_, hs₀mem⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith
  have hPz : unlift P = c s₀ := unlift_lift (polar_add_arg_div _ _ hy0)
  have hcone : NullConeLt (Q - P) := by
    refine hzy.of_polar (polar_add_arg_div _ _ hy0) (polar_arg _) ?_
    rw [show arg (c b).2 - (arg (c b).2 + arg ((c s₀).2 / (c b).2)) =
      -arg ((c s₀).2 / (c b).2) by ring, abs_neg]
    exact Complex.abs_arg_le_pi _
  -- the neighbourhood
  have hS : IsOpen (Metric.ball Q (ε / 2) ∩ {Q' | NullConeLt (Q' - P)}) :=
    Metric.isOpen_ball.inter (isOpen_nullConeLt.preimage (continuous_id.sub continuous_const))
  have hφ' := continuousAt_locLift (c b) hy0
  refine Filter.mem_of_superset (hφ'.preimage_mem_nhds (hS.mem_nhds ?_)) ?_
  · rw [locLift_self _ hy0]; exact ⟨Metric.mem_ball_self (by linarith), hcone⟩
  · rintro y' ⟨hy'b, hy'c⟩
    set Q' := locLift (c b) y'
    have hQ'y : unlift Q' = y' := unlift_lift (polar_add_arg_div _ _ hy0)
    have hsegU : ∀ s ∈ Icc (0 : ℝ) 1, unlift (seg P Q' s) ∈ U := fun s hs => by
      have := seg_mem_of_convex (convex_ball Q (ε / 2)) hPball hy'b hs
      exact (hball (Metric.ball_subset_ball (by linarith) this)).1
    have hPadm : Adm P := Or.inl (hball (Metric.ball_subset_ball (by linarith) hPball)).2
    have hseg := curveOn_unlift_seg_lt hPadm hy'c hsegU
    have hres : Causal.CurveOn (relOn Lt) U c a s₀ :=
      hc.restrict le_rfl hs₀b.le le_rfl fun t ht => hc.mem t ⟨ht.1, ht.2.trans hs₀b.le⟩
    obtain ⟨d, hd, hda, hdb⟩ := curve_append isRelFamily_lt hres hseg hs₀a zero_le_one
      (by simp only [seg_zero, hPz])
    refine ⟨a, _, by linarith, d, hd, hda, ?_⟩
    rw [hdb, seg_one, hQ'y]


/-- **`I⁻_U(y)` is open**, BTZ points included. -/
theorem isOpen_CLt_left (U : Opens E0) (y : E0) : IsOpen {x | CLt U x y} := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨a, b, hab, c, hc, rfl, hcb⟩
  have haU : c a ∈ U := hc.mem a ⟨le_rfl, hab.le⟩
  obtain ⟨l, u, hl, hu, hrel⟩ := hc.rel a ⟨le_rfl, hab.le⟩ U le_rfl haU
  -- the tail of the curve from `c s₀` to `y`
  have htail : ∀ s₀ ∈ Ioo a b, ∀ x' : E0, ∀ d : ℝ → E0, Causal.CurveOn (relOn Lt) U d 0 1 →
      d 0 = x' → d 1 = c s₀ → CLt U x' y := by
    intro s₀ hs₀ x' d hd hd0 hd1
    have hres : Causal.CurveOn (relOn Lt) U c s₀ b :=
      hc.restrict hs₀.1.le le_rfl le_rfl fun t ht => hc.mem t ⟨hs₀.1.le.trans ht.1, ht.2⟩
    obtain ⟨e, he, hea, heb⟩ := curve_append isRelFamily_lt hd hres zero_le_one hs₀.2.le hd1
    exact ⟨0, _, by linarith [hs₀.2], e, he, hea.trans hd0, heb.trans hcb⟩
  rcases (rad_nonneg (c a)).lt_or_eq with hrx | hrx
  · -- off the axis: the local lift at `x`
    have hx0 : (c a).2 ≠ 0 := norm_pos_iff.1 hrx
    set P := lift (c a) (arg (c a).2) with hPdef
    have hPx : unlift P = c a := unlift_lift (polar_arg _)
    have hPb : 0 < P.2.1 := hrx
    have hUP : unlift ⁻¹' U ∩ {R | 0 < R.2.1} ∈ 𝓝 P := by
      refine Filter.inter_mem ((continuousAt_unlift hPb.ne').preimage_mem_nhds ?_)
        ((isOpen_lt continuous_const continuous_snd.fst).mem_nhds hPb)
      rw [hPx]; exact U.isOpen.mem_nhds haU
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hUP
    have hφ := continuousAt_locLift (c a) hx0
    rw [ContinuousAt, locLift_self _ hx0] at hφ
    have hpre : c ⁻¹' (locLift (c a) ⁻¹' Metric.ball P (ε / 2)) ∈ 𝓝[Icc a b] a :=
      (hc.continuousOn isRelFamily_lt) a ⟨le_rfl, hab.le⟩
        (hφ (Metric.ball_mem_nhds P (by linarith)))
    obtain ⟨δ₁, hδ₁, hδball⟩ := Metric.mem_nhdsWithin_iff.1 hpre
    set s₀ := (a + min (min b u) (a + δ₁)) / 2 with hs₀
    have hm : a < min (min b u) (a + δ₁) := lt_min (lt_min hab hu) (by linarith)
    have hs₀a : a < s₀ := by rw [hs₀]; linarith
    have hs₀b : s₀ < b := by
      have : min (min b u) (a + δ₁) ≤ b := (min_le_left _ _).trans (min_le_left _ _)
      rw [hs₀]; linarith
    have hs₀u : s₀ < u := by
      have : min (min b u) (a + δ₁) ≤ u := (min_le_left _ _).trans (min_le_right _ _)
      rw [hs₀]; linarith
    have hs₀δ : s₀ < a + δ₁ := by
      have : min (min b u) (a + δ₁) ≤ a + δ₁ := min_le_right _ _
      rw [hs₀]; linarith
    have hs₀mem : s₀ ∈ Icc a b := ⟨hs₀a.le, hs₀b.le⟩
    have hxz : Lt (c a) (c s₀) := (hrel a ⟨le_rfl, hab.le⟩ s₀ hs₀mem hl hs₀a hs₀u).2.2
    set Q := locLift (c a) (c s₀) with hQdef
    have hQball : Q ∈ Metric.ball P (ε / 2) := by
      refine hδball ⟨?_, hs₀mem⟩
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith
    have hQz : unlift Q = c s₀ := unlift_lift (polar_add_arg_div _ _ hx0)
    have hcone : NullConeLt (Q - P) := by
      refine hxz.of_polar (polar_arg _) (polar_add_arg_div _ _ hx0) ?_
      rw [show arg (c a).2 + arg ((c s₀).2 / (c a).2) - arg (c a).2 =
        arg ((c s₀).2 / (c a).2) by ring]
      exact Complex.abs_arg_le_pi _
    have hS : IsOpen (Metric.ball P (ε / 2) ∩ {P' | NullConeLt (Q - P')}) :=
      Metric.isOpen_ball.inter (isOpen_nullConeLt.preimage (continuous_const.sub continuous_id))
    have hφ' := continuousAt_locLift (c a) hx0
    refine Filter.mem_of_superset (hφ'.preimage_mem_nhds (hS.mem_nhds ?_)) ?_
    · rw [locLift_self _ hx0]; exact ⟨Metric.mem_ball_self (by linarith), hcone⟩
    · rintro x' ⟨hx'b, hx'c⟩
      set P' := locLift (c a) x'
      have hP'x : unlift P' = x' := unlift_lift (polar_add_arg_div _ _ hx0)
      have hsegU : ∀ s ∈ Icc (0 : ℝ) 1, unlift (seg P' Q s) ∈ U := fun s hs => by
        have := seg_mem_of_convex (convex_ball P (ε / 2)) hx'b hQball hs
        exact (hball (Metric.ball_subset_ball (by linarith) this)).1
      have hP'adm : Adm P' := Or.inl (hball (Metric.ball_subset_ball (by linarith) hx'b)).2
      exact htail s₀ ⟨hs₀a, hs₀b⟩ x' _ (curveOn_unlift_seg_lt hP'adm hx'c hsegU)
        (by simp only [seg_zero, hP'x]) (by simp only [seg_one, hQz])
  · -- on the axis: a ball, order-convex, and the cone condition uniform in the angles
    have hxax : c a ∈ axis := rad_eq_zero.1 hrx.symm
    obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.1 U.isOpen (c a) haU
    have hpre : c ⁻¹' Metric.ball (c a) δ ∈ 𝓝[Icc a b] a :=
      (hc.continuousOn isRelFamily_lt) a ⟨le_rfl, hab.le⟩ (Metric.ball_mem_nhds _ hδ)
    obtain ⟨δ₁, hδ₁, hδball⟩ := Metric.mem_nhdsWithin_iff.1 hpre
    set s₀ := (a + min (min b u) (a + δ₁)) / 2 with hs₀
    have hm : a < min (min b u) (a + δ₁) := lt_min (lt_min hab hu) (by linarith)
    have hs₀a : a < s₀ := by rw [hs₀]; linarith
    have hs₀b : s₀ < b := by
      have : min (min b u) (a + δ₁) ≤ b := (min_le_left _ _).trans (min_le_left _ _)
      rw [hs₀]; linarith
    have hs₀u : s₀ < u := by
      have : min (min b u) (a + δ₁) ≤ u := (min_le_left _ _).trans (min_le_right _ _)
      rw [hs₀]; linarith
    have hs₀δ : s₀ < a + δ₁ := by
      have : min (min b u) (a + δ₁) ≤ a + δ₁ := min_le_right _ _
      rw [hs₀]; linarith
    have hs₀mem : s₀ ∈ Icc a b := ⟨hs₀a.le, hs₀b.le⟩
    have hxz : Lt (c a) (c s₀) := (hrel a ⟨le_rfl, hab.le⟩ s₀ hs₀mem hl hs₀a hs₀u).2.2
    have hzball : c s₀ ∈ Metric.ball (c a) δ := by
      refine hδball ⟨?_, hs₀mem⟩
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith
    set z := c s₀
    have hzc := hxz.closed
    rw [← hrx, sub_zero] at hzc
    set G : E0 → ℝ := fun x' => (rad z - rad x') * (2 * (z.1 - x'.1) - (rad z - rad x')) -
      4 * π ^ 2 * (rad x' * rad z) with hG
    have hGc : Continuous G := by
      have := continuous_rad
      rw [hG]; fun_prop
    have hV : IsOpen (Metric.ball (c a) δ ∩ {x' | rad x' < rad z} ∩ {x' | 0 < G x'}) :=
      (Metric.isOpen_ball.inter (isOpen_lt continuous_rad continuous_const)).inter
        (isOpen_lt continuous_const hGc)
    refine Filter.mem_of_superset (hV.mem_nhds ⟨⟨Metric.mem_ball_self hδ, ?_⟩, ?_⟩) ?_
    · show rad (c a) < rad z
      rw [← hrx]; exact hzc.1
    · show 0 < G (c a)
      simp only [hG, ← hrx, zero_mul, mul_zero, sub_zero]; exact hzc.2
    · rintro x' ⟨⟨hx'b, hx'r⟩, hx'G⟩
      have hcone : NullConeLt (lift z (arg z.2) - lift x' (arg x'.2)) := by
        rw [nullConeLt_lift_iff]
        refine ⟨hx'r, ?_⟩
        have h2π : (arg z.2 - arg x'.2) ^ 2 ≤ (2 * π) ^ 2 :=
          sq_le_sq' (abs_le.1 (abs_arg_sub_arg_le _ _)).1 (abs_le.1 (abs_arg_sub_arg_le _ _)).2
        have hrr : 0 ≤ rad x' * rad z := mul_nonneg (rad_nonneg _) (rad_nonneg _)
        have : rad x' * rad z * (arg z.2 - arg x'.2) ^ 2 ≤ 4 * π ^ 2 * (rad x' * rad z) := by
          nlinarith
        have hx'G' : 0 < G x' := hx'G
        simp only [hG] at hx'G'
        linarith
      have hsegU : ∀ s ∈ Icc (0 : ℝ) 1,
          unlift (seg (lift x' (arg x'.2)) (lift z (arg z.2)) s) ∈ U := fun s hs => by
        have hends := le_seg_ends (adm_lift x' _) hcone.nullCone hs
        rw [unlift_lift (polar_arg _), unlift_lift (polar_arg _)] at hends
        exact hδU (mem_ball_of_le_of_le hxax hends.1 hends.2 hx'b hzball)
      exact htail s₀ ⟨hs₀a, hs₀b⟩ x' _ (curveOn_unlift_seg_lt (adm_lift x' _) hcone hsegU)
        (by simp only [seg_zero, unlift_lift (polar_arg _)])
        (by simp only [seg_one, unlift_lift (polar_arg _)]; rfl)

end Open

/-! ### The causality of `𝔼₀`, and its calculus -/

section Calculus

open TopologicalSpace

/-- **The causality of `𝔼₀`** (`defi:causal_Ealpha` / `defi:causal_E0` read by DEC-33): `x ≤_U y`
(resp. `x ≪_U y`) iff a future causal (resp. chronological) curve joins them in `U`
(`CLe`, `CLe`); the relations are those of `Causal.Curves` for the local relations `Le`, `Lt` of
developments in `𝐌³`. -/
noncomputable def causality : Causal.Causality E0 where
  le := CLe
  lt := CLt
  le_mem_left h := h.mem_left
  le_mem_right h := h.mem_right
  lt_mem_left h := h.cle.mem_left
  lt_mem_right h := h.cle.mem_right
  le_refl hx := CLe.refl hx
  le_trans := CLe.trans
  lt_trans := CLt.trans
  le_mono hVU _ _ h := h.mono hVU
  lt_mono hVU _ _ h := h.mono hVU
  le_of_lt h := h.cle
  isOpen_lt_right := isOpen_CLt_right
  isOpen_lt_left := isOpen_CLt_left

variable {U : Opens E0} {p : E0}

@[simp] theorem causality_le : causality.le U x y ↔ CLe U x y := Iff.rfl

@[simp] theorem causality_lt : causality.lt U x y ↔ CLt U x y := Iff.rfl

/-- **Globally, `x ≤ y` iff some developments are causally related in `𝐌³`.** -/
theorem le_top_iff : causality.le ⊤ x y ↔ Le x y := cle_top_iff

theorem lt_top_iff : causality.lt ⊤ x y ↔ Lt x y := clt_top_iff

theorem le_of_le (h : causality.le U x y) : Le x y := CLe.le h

theorem nonneg_of_mul_nonneg' {B X : ℝ} (hB : 0 < B) (h : 0 ≤ B * X) : 0 ≤ X := by
  by_contra hX
  have : B * X < 0 := mul_neg_of_pos_of_neg hB (not_le.1 hX)
  linarith

theorem pos_of_mul_pos' {B X : ℝ} (hB : 0 ≤ B) (h : 0 < B * X) : 0 < X := by
  by_contra hX
  have : B * X ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hB (not_lt.1 hX)
  linarith

theorem lt_of_lt (h : causality.lt U x y) : Lt x y := CLt.lt h

/-- **The calculus along future causal curves** (`B16 lem:BTZ_causal_curve` (i), `BTZ_HAL_1.tex:515`,
integrated): `0 ≤ Δr ≤ 2Δτ`, so `τ`, `r`, `f = τ − r/2` and `h = τ + r` are non-decreasing. -/
theorem calculus_le (h : causality.le U x y) :
    0 ≤ rad y - rad x ∧ rad y - rad x ≤ 2 * (y.1 - x.1) ∧ x.1 ≤ y.1 ∧ rad x ≤ rad y ∧
      fcoord x ≤ fcoord y ∧ hcoord x ≤ hcoord y := by
  obtain ⟨hτ, hr, hq⟩ := (le_of_le h).closed
  have hd : rad y - rad x ≤ 2 * (y.1 - x.1) := by
    rcases (sub_nonneg.2 hr).lt_or_eq with h' | h'
    · have := nonneg_of_mul_nonneg' h' hq
      linarith
    · rw [← h']; linarith
  refine ⟨by linarith, hd, hτ, hr, ?_, ?_⟩ <;> simp only [fcoord, hcoord] <;> linarith

/-- **Along future chronological curves `r`, `τ`, `f` and `h` increase strictly.** -/
theorem calculus_lt (h : causality.lt U x y) :
    rad x < rad y ∧ rad y - rad x < 2 * (y.1 - x.1) ∧ x.1 < y.1 ∧ fcoord x < fcoord y ∧
      hcoord x < hcoord y := by
  obtain ⟨hr, hq⟩ := (lt_of_lt h).closed
  have h2 : 0 < 2 * (y.1 - x.1) - (rad y - rad x) := by
    by_contra h'
    have : 2 * (y.1 - x.1) - (rad y - rad x) ≤ 0 := not_lt.1 h'
    nlinarith [sub_pos.2 hr]
  refine ⟨hr, by linarith, by linarith, ?_, ?_⟩ <;> simp only [fcoord, hcoord] <;> linarith

/-- Two points of the axis, `τ`-ordered, are causally related. -/
theorem le_axis (hx : x ∈ axis) (hy : y ∈ axis) (h : x.1 ≤ y.1) : Le x y := by
  refine le_iff_closed.2 ⟨0, 0, Polar.of_axis hx 0, Polar.of_axis hy 0, ?_⟩
  rw [rad_eq_zero.2 hx, rad_eq_zero.2 hy]
  exact ⟨h, le_rfl, by simp⟩

theorem fcoord_of_axis (hx : x ∈ axis) : fcoord x = x.1 := by
  simp [fcoord, rad_eq_zero.2 hx]

/-- **The causal future of a BTZ point is `{f ≥ τ_p}`**: below, the future light cone of `p` is
the level set `f = τ_p`. -/
theorem le_axis_iff (hp : p ∈ axis) : Le p y ↔ p.1 ≤ fcoord y := by
  rw [le_iff_closed]
  have hp0 := rad_eq_zero.2 hp
  constructor
  · rintro ⟨θ₁, θ₂, -, -, hτ, hr, hq⟩
    rw [hp0] at hq hr
    simp only [zero_mul, sub_zero] at hq
    simp only [fcoord]
    rcases (rad_nonneg y).lt_or_eq with h' | h'
    · have := nonneg_of_mul_nonneg' h' hq
      linarith
    · rw [← h']; linarith
  · intro h
    have hr := rad_nonneg y
    refine ⟨0, arg y.2, Polar.of_axis hp 0, polar_arg y, ?_, ?_, ?_⟩
    · simp only [fcoord] at h; linarith
    · rw [hp0]; exact hr
    · rw [hp0]; simp only [zero_mul, sub_zero]; simp only [fcoord] at h
      exact mul_nonneg hr (by linarith)

/-- **The chronological future of a BTZ point is `{r > 0, f > τ_p}`.** -/
theorem lt_axis_iff (hp : p ∈ axis) : Lt p y ↔ 0 < rad y ∧ p.1 < fcoord y := by
  rw [lt_iff_closed]
  have hp0 := rad_eq_zero.2 hp
  constructor
  · rintro ⟨θ₁, θ₂, -, -, hr, hq⟩
    rw [hp0] at hq hr
    simp only [zero_mul, sub_zero] at hq
    refine ⟨hr, ?_⟩
    simp only [fcoord]
    have := pos_of_mul_pos' hr.le hq
    linarith
  · rintro ⟨hr, h⟩
    refine ⟨0, arg y.2, Polar.of_axis hp 0, polar_arg y, ?_, ?_⟩
    · rw [hp0]; exact hr
    · rw [hp0]; simp only [zero_mul, sub_zero]; simp only [fcoord] at h
      exact mul_pos hr (by linarith)

/-- **The causal past of a BTZ point is the singular half-line below it**
(`defi:causal_E0`, `ETT.tex:1344`; B21 §1.2). -/
theorem le_axis_iff' (hp : p ∈ axis) : Le x p ↔ x ∈ axis ∧ x.1 ≤ p.1 := by
  constructor
  · intro h
    obtain ⟨hτ, hr, -⟩ := h.closed
    rw [rad_eq_zero.2 hp] at hr
    exact ⟨rad_eq_zero.1 (le_antisymm hr (rad_nonneg x)), hτ⟩
  · rintro ⟨hx, h⟩; exact le_axis hx hp h

theorem Jplus_axis (hp : p ∈ axis) : causality.Jplus ⊤ {p} = {y | p.1 ≤ fcoord y} := by
  ext y; rw [Causal.Precausality.mem_Jplus_singleton, le_top_iff, le_axis_iff hp]; rfl

theorem Iplus_axis (hp : p ∈ axis) :
    causality.Iplus ⊤ {p} = {y | 0 < rad y ∧ p.1 < fcoord y} := by
  ext y; rw [Causal.Precausality.mem_Iplus_singleton, lt_top_iff, lt_axis_iff hp]; rfl

theorem Jminus_axis (hp : p ∈ axis) :
    causality.Jminus ⊤ {p} = {x | x ∈ axis ∧ x.1 ≤ p.1} := by
  ext x; rw [Causal.Precausality.mem_Jminus_singleton, le_top_iff, le_axis_iff' hp]; rfl

/-- **`I⁻_U(p) = ∅` at a BTZ point**, in every open set. -/
theorem Iminus_axis (hp : p ∈ axis) (U : Opens E0) : causality.Iminus U {p} = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
  have h := Causal.Precausality.mem_Iminus_singleton.1 hx
  have := (calculus_lt h).1
  rw [rad_eq_zero.2 hp] at this
  exact absurd this (not_lt.2 (rad_nonneg x))

/-- **`J⁻_U(p) ⊂ sing₀` at a BTZ point**, in every open set (`past_local`). -/
theorem Jminus_axis_subset (hp : p ∈ axis) (U : Opens E0) : causality.Jminus U {p} ⊆ axis :=
  fun _ hx => ((le_axis_iff' hp).1 (le_of_le (Causal.Precausality.mem_Jminus_singleton.1 hx))).1

/-- **Locally `I⁺(p) = {r > 0, f > τ_p}` at a BTZ point**: in every ball `B` centred at `p`,
`I⁺_B(p) = B ∩ {r > 0, f > τ_p}`. -/
theorem Iplus_ball_axis (hp : p ∈ axis) {δ : ℝ} :
    causality.Iplus ⟨Metric.ball p δ, Metric.isOpen_ball⟩ {p} =
      Metric.ball p δ ∩ {y | 0 < rad y ∧ p.1 < fcoord y} := by
  refine Set.ext fun y => ?_
  rw [Causal.Precausality.mem_Iplus_singleton]
  constructor
  · intro h
    exact ⟨causality.lt_mem_right h, (lt_axis_iff hp).1 (lt_of_lt h)⟩
  · rintro ⟨hy, hy'⟩
    have hlt := (lt_axis_iff hp).2 hy'
    obtain ⟨θ₁, θ₂, h₁, h₂, hc⟩ := hlt
    refine clt_of_seg h₁ h₂ hc fun s hs => ?_
    have hends := le_seg_ends (adm_lift p θ₁) hc.nullCone hs
    rw [unlift_lift h₁, unlift_lift h₂] at hends
    have hpb : p ∈ Metric.ball p δ := Metric.mem_ball_self ((Metric.pos_of_mem_ball hy))
    exact mem_ball_of_le_of_le hp hends.1 hends.2 hpb hy

/-- `I⁺_U(p) ⊂ U ∩ {r > 0, f > τ_p}` for every open `U`, and equality in every ball inside `U`. -/
theorem Iplus_axis_subset (hp : p ∈ axis) (U : Opens E0) :
    causality.Iplus U {p} ⊆ U ∩ {y | 0 < rad y ∧ p.1 < fcoord y} := fun _ hy =>
  ⟨causality.lt_mem_right (Causal.Precausality.mem_Iplus_singleton.1 hy),
    (lt_axis_iff hp).1 (lt_of_lt (Causal.Precausality.mem_Iplus_singleton.1 hy))⟩

end Calculus

end E0

end Causal
