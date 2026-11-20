import Causal.Port.E0Causality
import Causal.SingularFlat
import Causal.Static

/-!
# `E₀`: absolute minimality, strong tarentinity, `BTZAxioms`, and `defi:causal_E0` at the model

Target `T-ett-port-e0` (DEC-134), the third of three modules. Cited, **unmarked** (SCOPE (a)):
`defi:causal_E0` — `ETT.tex:1344`, assembled in `Causal.E0.causal_E0`.

> For $\alpha=0$ the singular line is lightlike: locally causal, but not locally chronal. More
> precisely \cite[Section~1.2]{brunswic2021cauchy}, for a singular point $p\in \sing(\mass{0})$,
> $$I^-(p)=\emptyset \qquad\text{and}\qquad J^-(p)=\{\r=0,~\tau\leq \tau(p)\},$$
> that is, the causal past of $p$ is exactly the singular half-line below $p$. In particular a BTZ
> point is strongly tarentin in the future but not in the past, and a $\mass{\geq0}$-manifold with at
> least one extreme BTZ white hole is not past distinguishing.
>
> Dually, the chronological future of a BTZ point $p$ is
> $$I^+(p)=\reg\left(J^+(p)\right)=J^+(p)\setminus \sing_0\left(\mass{0}\right):$$
> every non-BTZ point of the causal future of $p$ lies in its chronological future.
> (`ETT.tex:1344–1356`; l.1352, in the source: "quoted from \cite{thesis}, where it is asserted
> without proof -- verify")

**Ported from `lean-gx/GX/BTZ/Causality.lean` at commit `c48aa45`** (gx package WP-41e): every
declaration `GX.E0.x` of gx's l.1288–1645 (causal arc-connectedness and absolute minimality,
strong tarentinity, the BTZ axioms, `Iplus_ne_Jplus_diff`, `J^±(V)` open) is `Causal.E0.x` here,
with gx's statement and proof character for character; the only changes are the import of
`Causal.Port.E0Causality` in place of gx's, the `variable` line repeated, and the
docstring of `btzAxioms`, whose gx sentence "the first instance in the library with a non-empty
BTZ locus" (gx l.1518–1519) is false — `Causal.lightlikeLine_btzAxioms`
(`Causal/SingularFlat.lean`) has the whole line as its BTZ locus — and is corrected (AUDIT-1).
The section `defi:causal_E0` at the end is **new**.

## What is proved (no `sorry` in this file)

* `causallyArcConnected`, `absolutelyMinimalOn` (every open set; `cor:model_minimal` for `κ = 0`).
* `mem_Zplus` (`Z^+ = E₀`), `mem_Zminus_iff` (`Z^- = E₀ ∖ sing₀`), `tarentin`.
* **`btzAxioms : causality.BTZAxioms axis`** — the library's `Causal.Causality.BTZAxioms` with
  DEC-64's `Iplus_of_lt`, at the paper's model `E₀`: the first instance on a 3-dimensional model
  of the paper, whose BTZ points have a non-empty chronological future (the lightlike line,
  `Causal.lightlikeLine_btzAxioms`, already has a non-empty BTZ locus, with `I^+ = ∅`);
  `isOpen_Jplus`, `isOpen_Jminus` (`J^±(V)` open, BTZ points included).
* At the model, `defi:causal_E0` (new): the singular line is locally causal
  (`axis_causalCurveOn`) but not locally chronal (`not_chronalCurveOn_axisLine`,
  `not_lt_of_mem_axis`); `I^-_U(p) = ∅` for every open `U`; `J^-(p) = {r = 0, τ ≤ τ(p)}`;
  `p ∈ Z^+ ∖ Z^-`; `E₀` is not past distinguishing (`not_pastDistinguishing`), and neither is any
  causality with `SingularFlatAxioms` and `sing₀ ≠ ∅`
  (`Causality.SingularFlatAxioms.not_pastDistinguishing`; no inhabitant with a BTZ point in
  `lean-causal` yet, SCOPE (c)). **The last sentence is false**:
  `I^+(p) ≠ J^+(p) ∖ sing₀` at every BTZ point (`Iplus_ne_Jplus_diff`, gx's;
  `not_btzIplusAsPrinted`); its strongest true form is
  `I^+(p) = Int(J^+(p)) ∖ sing₀` (`Iplus_axis_eq_interior_diff`), with
  `J^+(p) = {f ≥ τ_p}`, `Int J^+(p) = {f > τ_p}`, and DEC-64's `Iplus_of_lt`. Assembly:
  `causal_E0`.

## Hypothesis checklist

| paper | here |
|---|---|
| `E₀`, the extreme BTZ model (l.1330) | ⚠ read: `Causal.E0` with gx's metric `−2dτdr + dr² + r²dθ²` through `D` (`E0Model` SCOPE (a)), a question |
| its causality from curves (`defi:causal_Ealpha`) | ⚠ read: `E0.causality`, the causal curves of `E₀` as gx reads DEC-33 (`E0Causality` SCOPE (a)), a question |
| "locally causal, but not locally chronal" (l.1345) | ⚠ read: every segment of the axis in an open `W` is a causal curve of `W`, none is chronal (SCOPE (a)), a question |
| `I^-(p) = ∅`, `J^-(p) = {r = 0, τ ≤ τ(p)}` | ✓ (`I^-_U(p) = ∅` in every open `U`) |
| strongly tarentin in the future, not in the past | ✓ `Z^+`, `Z^-` of `def:strongly_tarentin_point` |
| "past distinguishing" (undefined in ETT) | ⚠ read: `I^-(x) = I^-(y) ⇒ x = y` (`Causality.PastDistinguishing`), a question |
| "`E_{≥0}`-manifold with an extreme BTZ white hole" | ⚠ `E₀` itself; abstractly `SingularFlatAxioms` with `sing₀ ≠ ∅` (read: a white hole is a BTZ point), a question |
| `I^+(p) = J^+(p) ∖ sing₀` (l.1353–1355) | ✗ **false** (`not_btzIplusAsPrinted`); strongest true form `I^+(p) = Int J^+(p) ∖ sing₀` |

## SCOPE (disclosed)

* **(a) Why `defi:causal_E0` is not marked.** Its last sentence (l.1353–1355) is false in `E₀`
  (DEC-64's finding, now a theorem: the radial null ray `t ↦ (τ_p + t/2, t e^{iθ})` is in
  `J^+(p) ∖ sing₀` and not in `I^+(p)`, since `f = τ − r/2` is constant along it and strictly
  increasing along chronological curves). DEC-64 replaced the corresponding field of
  `BTZAxioms` by `Iplus_of_lt`, but did not rule on the label's statement; the label stays
  `partial`. Two phrases are read (checklist): "past distinguishing" and "extreme BTZ white
  hole"; "lightlike" is read causally (a causal, nowhere chronal curve: there is no metric here).
* **(b) Global versus local.** The paper's `I^±(p)`, `J^±(p)` are read globally (`U = E₀`), as
  `BTZAxioms` reads them, except `I^-_U(p) = ∅`, proved in every open `U`. The local forms gx
  proves are kept (`Iplus_ball_axis`, `Jminus_axis_subset`, `E0Causality`).
* **(c) Not here.** Push-up in every open set and `SingularFlatAxioms` for `E₀` (gx's l.1814–3347
  and `GX.E0LM.e0_pushUp`) are target `T-ett-port-e0-sfa`; `def:singular_spacetime` is not
  touched. The two general definitions introduced (`Causality.PastDistinguishing`,
  `Causality.BTZIplusAsPrinted`) are stated for any causality. **The abstract
  `Causality.SingularFlatAxioms.not_pastDistinguishing` has no inhabitant in `lean-causal` yet**:
  `SingularFlatAxioms` with `sing 0 ≠ ∅` has no witness in the library (`Causal.SingularFlat`,
  SCOPE); the `E₀` instance comes with `T-ett-port-e0-sfa` (gx has it, through
  `GX.E0.singularFlatAxioms_of_pushUp` and `GX.E0LM.e0_pushUp`). Until then the evidence for the
  sentence of l.1349–1350 is the model case `E0.not_pastDistinguishing`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Ported from
`lean-gx/GX/BTZ/Causality.lean` at `c48aa45` (target `T-ett-port-e0`, DEC-134).
-/

namespace Causal

open Set Filter Topology Function Complex
open scoped Real

namespace E0

variable {x y z : E0}

/-! ### Causal arc-connectedness and absolute minimality -/

section ArcConnected

open TopologicalSpace

variable {W : Opens E0} {c : ℝ → E0} {a b : ℝ}

/-- A curve for the local relation `Le` is a future causal curve of `causality` in the sense of
`Causal.Curves` (locally `≤_N`-increasing for every open `N`). -/
theorem causalCurveOn_of_curveOn (hc : Causal.CurveOn (relOn Le) W c a b) :
    causality.CausalCurveOn W c a b where
  mem := hc.mem
  rel t ht N hN htN := by
    have hpre : c ⁻¹' N ∈ 𝓝[Icc a b] t :=
      (hc.continuousOn isRelFamily_le) t ht (N.isOpen.mem_nhds htN)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hpre
    refine ⟨t - ε, t + ε, by linarith, by linarith, fun s hs s' hs' h1 h2 h3 => ?_⟩
    have hmem : ∀ τ ∈ Icc s s', c τ ∈ N := fun τ hτ => hball
      ⟨by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hτ.1, hτ.2],
        ⟨hs.1.trans hτ.1, hτ.2.trans hs'.2⟩⟩
    exact ⟨s, s', h2.le, c, hc.restrict hs.1 hs'.2 hN hmem, rfl, rfl⟩

theorem chronalCurveOn_of_curveOn (hc : Causal.CurveOn (relOn Lt) W c a b) :
    causality.ChronalCurveOn W c a b where
  mem := hc.mem
  rel t ht N hN htN := by
    have hpre : c ⁻¹' N ∈ 𝓝[Icc a b] t :=
      (hc.continuousOn isRelFamily_lt) t ht (N.isOpen.mem_nhds htN)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hpre
    refine ⟨t - ε, t + ε, by linarith, by linarith, fun s hs s' hs' h1 h2 h3 => ?_⟩
    have hmem : ∀ τ ∈ Icc s s', c τ ∈ N := fun τ hτ => hball
      ⟨by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hτ.1, hτ.2],
        ⟨hs.1.trans hτ.1, hτ.2.trans hs'.2⟩⟩
    exact ⟨s, s', h2, c, hc.restrict hs.1 hs'.2 hN hmem, rfl, rfl⟩

/-- Reparametrisation of a curve over `[a, b]`, `a < b`, to `[0, 1]`. -/
theorem curveOn_reparam {r : Opens E0 → E0 → E0 → Prop} (hc : Causal.CurveOn r W c a b) (hab : a < b) :
    Causal.CurveOn r W (fun t => c ((b - a) * t + a)) 0 1 :=
  Causal.CurveOn.comp_affine (k := b - a) (m := a) (sub_pos.2 hab)
    (by rw [mul_zero, zero_add, mul_one, sub_add_cancel]; exact hc)

/-- **`𝔼₀` is causally arc-connected** (`def:causal_arc_connectedness`): `≤_U` and `≪_U` are
realised by causal and chronal curves of `U` in the sense of `Causal.Curves`. -/
theorem causallyArcConnected : causality.CausallyArcConnected := by
  rw [Causal.Causality.CausallyArcConnected, Causal.Causality.causallyArcConnectedOn_iff]
  intro U _ p q
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨a, b, hab, c, hc, rfl, rfl⟩ := h
    rcases hab.lt_or_eq with hab | hab
    · refine ⟨_, causalCurveOn_of_curveOn (curveOn_reparam hc hab), by simp, by simp⟩
    · refine ⟨fun _ => c a, causalCurveOn_of_curveOn (curveOn_of_continuousOn
        continuousOn_const (fun _ _ => hc.mem a ⟨le_rfl, hab.le⟩) fun _ _ _ _ _ => le_refl' _),
        rfl, by rw [hab]⟩
  · obtain ⟨a, b, hab, c, hc, rfl, rfl⟩ := h
    exact ⟨_, chronalCurveOn_of_curveOn (curveOn_reparam hc hab), by simp, by simp⟩

/-- **The causality of `𝔼₀` is absolutely minimal on every open set** (`cor:model_minimal`,
`ETT.tex:1380`, for `κ = 0`, through `cor:causalement_connexe_minimal`). -/
theorem absolutelyMinimalOn (W : Opens E0) : causality.AbsolutelyMinimalOn W :=
  Causal.Causality.CausallyArcConnectedOn.absolutelyMinimalOn (causallyArcConnected.mono le_top)

end ArcConnected

/-! ### Strong tarentinity: `Z⁺ = 𝔼₀`, `Z⁻ = 𝔼₀ ∖ sing₀` -/

section Tarentin

open TopologicalSpace

variable {p : E0}

/-- A fixed future timelike vector of `(ℝ³, nullQ)`. -/
def timelikeT (k : ℝ) : ℝ × ℝ × ℝ := (k, k, 0)

theorem nullConeLt_timelikeT {k : ℝ} (hk : 0 < k) : NullConeLt (timelikeT k) := by
  refine ⟨hk, ?_⟩; simp only [timelikeT]; nlinarith

/-- **Every point has chronological future in each of its neighbourhoods** (`rem:btz_pas_tarentin`:
`Z⁺ = 𝔼₀`). -/
theorem exists_lt_mem (p : E0) {V : Set E0} (hV : V ∈ 𝓝 p) : ∃ q ∈ V, Lt p q := by
  set P := lift p (arg p.2)
  set Q := P + timelikeT 1
  have hPQ : NullConeLt (Q - P) := by
    rw [show Q - P = timelikeT 1 by simp [Q]]; exact nullConeLt_timelikeT one_pos
  have hcont := continuousOn_unlift_seg (adm_lift p (arg p.2)) hPQ.nullCone
  have h0 : unlift (seg P Q 0) = p := by rw [seg_zero]; exact unlift_lift (polar_arg p)
  have hpre : (fun s => unlift (seg P Q s)) ⁻¹' V ∈ 𝓝[Icc 0 1] 0 :=
    hcont 0 ⟨le_rfl, zero_le_one⟩ (by beta_reduce; rw [h0]; exact hV)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hpre
  set s := min (ε / 2) 1
  have hs0 : 0 < s := lt_min (by linarith) one_pos
  have hs : s ∈ Icc (0 : ℝ) 1 := ⟨hs0.le, min_le_right _ _⟩
  refine ⟨unlift (seg P Q s), hball ⟨?_, hs⟩, ?_⟩
  · rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hs0]
    exact (min_le_left _ _).trans_lt (by linarith)
  · have := lt_unlift_seg (adm_lift p (arg p.2)) hPQ le_rfl hs0
    rwa [h0] at this

/-- **A point off the axis has chronological past in each of its neighbourhoods**
(`rem:btz_pas_tarentin`: `Z⁻ ⊇ 𝔼₀ ∖ sing₀`). -/
theorem exists_lt_mem' (hp : p ∉ axis) {V : Set E0} (hV : V ∈ 𝓝 p) : ∃ q ∈ V, Lt q p := by
  have hr := rad_pos.2 hp
  set Q := lift p (arg p.2)
  set P := Q - timelikeT (rad p / 2)
  have hPQ : NullConeLt (Q - P) := by
    rw [show Q - P = timelikeT (rad p / 2) by simp [P]]; exact nullConeLt_timelikeT (by linarith)
  have hP : Adm P := by
    left
    have : P.2.1 = rad p - rad p / 2 := rfl
    rw [this]; linarith
  have hcont := continuousOn_unlift_seg hP hPQ.nullCone
  have h1 : unlift (seg P Q 1) = p := by rw [seg_one]; exact unlift_lift (polar_arg p)
  have hpre : (fun s => unlift (seg P Q s)) ⁻¹' V ∈ 𝓝[Icc 0 1] 1 :=
    hcont 1 ⟨zero_le_one, le_rfl⟩ (by beta_reduce; rw [h1]; exact hV)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hpre
  set s := max (1 - ε / 2) 0
  have hs1 : s < 1 := max_lt (by linarith) one_pos
  have hs : s ∈ Icc (0 : ℝ) 1 := ⟨le_max_right _ _, hs1.le⟩
  refine ⟨unlift (seg P Q s), hball ⟨?_, hs⟩, ?_⟩
  · rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor
    · have : 1 - ε / 2 ≤ s := le_max_left _ _
      linarith
    · linarith
  · have := lt_unlift_seg hP hPQ hs.1 hs1
    rwa [h1] at this

theorem mem_Zplus (p : E0) : p ∈ causality.Zplus := fun U hU => by
  obtain ⟨q, hq, h⟩ := exists_lt_mem p hU
  exact ⟨q, Causal.Precausality.mem_Iplus_singleton.2 (lt_top_iff.2 h), hq⟩

theorem mem_Zminus_iff (p : E0) : p ∈ causality.Zminus ↔ p ∉ axis := by
  constructor
  · intro h hp
    obtain ⟨q, hq, -⟩ := h univ univ_mem
    rw [Iminus_axis hp] at hq
    exact hq
  · intro hp U hU
    obtain ⟨q, hq, h⟩ := exists_lt_mem' hp hU
    exact ⟨q, Causal.Precausality.mem_Iminus_singleton.2 (lt_top_iff.2 h), hq⟩

theorem isOpen_fcoord_gt (c : ℝ) : IsOpen {y : E0 | c < fcoord y} :=
  isOpen_lt continuous_const continuous_fcoord

/-- Points of the axis just below `p` lie in every neighbourhood of `p`. -/
theorem exists_axis_below (hp : p ∈ axis) {V : Set E0} (hV : V ∈ 𝓝 p) :
    ∃ ε > 0, ((p.1 - ε, 0) : E0) ∈ V := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hV
  refine ⟨δ / 2, by linarith, hball ?_⟩
  have hp0 : p.2 = 0 := hp
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, hp0, dist_self]
  refine ⟨?_, hδ⟩
  rw [show p.1 - δ / 2 - p.1 = -(δ / 2) by ring, abs_neg, abs_of_pos (by linarith)]
  linarith

/-- **`𝔼₀` is tarentin** (`rem:sing_tarentin`, `ETT.tex:1364`, for the model): every point lies in
the interior of a causal diamond with vertices in any prescribed neighbourhood. -/
theorem tarentin : causality.Tarentin := by
  intro x U hU
  obtain ⟨q, hqU, hxq⟩ := exists_lt_mem x hU
  have hIq : IsOpen (causality.Iminus ⊤ {q}) := causality.isOpen_Iminus
  have hxIq : x ∈ causality.Iminus ⊤ {q} :=
    Causal.Precausality.mem_Iminus_singleton.2 (lt_top_iff.2 hxq)
  by_cases hx : x ∈ axis
  · obtain ⟨ε, hε, hpU⟩ := exists_axis_below hx hU
    set p : E0 := (x.1 - ε, 0)
    have hpax : p ∈ axis := rfl
    refine ⟨p, hpU, q, hqU, ?_⟩
    have hsub : causality.Iminus ⊤ {q} ∩ {y | p.1 < fcoord y} ⊆ causality.diamond ⊤ p q := by
      rintro y ⟨hy1, hy2⟩
      refine (causality.mem_diamond).2 ⟨?_, causality.le_of_lt (Causal.Precausality.mem_Iminus_singleton.1 hy1)⟩
      exact le_top_iff.2 ((le_axis_iff hpax).2 hy2.le)
    refine interior_maximal hsub (hIq.inter (isOpen_fcoord_gt _)) ⟨hxIq, ?_⟩
    show x.1 - ε < fcoord x
    rw [fcoord_of_axis hx]; linarith
  · obtain ⟨p, hpU, hpx⟩ := exists_lt_mem' hx hU
    refine ⟨p, hpU, q, hqU, ?_⟩
    have hsub : causality.Iminus ⊤ {q} ∩ causality.Iplus ⊤ {p} ⊆ causality.diamond ⊤ p q := by
      rintro y ⟨hy1, hy2⟩
      exact (causality.mem_diamond).2 ⟨causality.le_of_lt (Causal.Precausality.mem_Iplus_singleton.1 hy2),
        causality.le_of_lt (Causal.Precausality.mem_Iminus_singleton.1 hy1)⟩
    exact interior_maximal hsub (hIq.inter causality.isOpen_Iplus)
      ⟨hxIq, Causal.Precausality.mem_Iplus_singleton.2 (lt_top_iff.2 hpx)⟩

end Tarentin

/-! ### The BTZ axioms of `𝔼₀` and the openness of `J^±(V)` -/

section BTZ

open TopologicalSpace

variable {p : E0}

theorem axis_eq_of_fst_eq (hx : x ∈ axis) (hy : y ∈ axis) (h : x.1 = y.1) : x = y :=
  Prod.ext h (hx.trans hy.symm)

/-- `t ↦ (τ_p + t, 0)`, the BTZ line through `p`. -/
def axisLine (p : E0) (t : ℝ) : E0 := (p.1 + t, 0)

theorem axisLine_mem (p : E0) (t : ℝ) : axisLine p t ∈ axis := rfl

theorem isometry_axisLine (p : E0) : Isometry (axisLine p) := by
  refine Isometry.of_dist_eq fun t t' => ?_
  simp only [axisLine, Prod.dist_eq, dist_self, Real.dist_eq]
  rw [max_eq_left (abs_nonneg _)]
  congr 1; ring

theorem range_axisLine (p : E0) : range (axisLine p) = axis := by
  ext y
  refine ⟨fun ⟨t, ht⟩ => ht ▸ axisLine_mem p t, fun hy => ⟨y.1 - p.1, ?_⟩⟩
  exact Prod.ext (by simp [axisLine]) (by simp only [axisLine]; exact hy.symm)

theorem curveOn_axisLine (p : E0) (W : Opens E0) (a b : ℝ) :
    Causal.CurveOn (relOn Le) W (axisLine p) a b ∨ ¬ ∀ t ∈ Icc a b, axisLine p t ∈ W := by
  by_cases h : ∀ t ∈ Icc a b, axisLine p t ∈ W
  · exact Or.inl (curveOn_of_continuousOn (isometry_axisLine p).continuous.continuousOn h
      fun s _ s' _ hss' => le_axis (axisLine_mem p s) (axisLine_mem p s')
        (by simp only [axisLine]; linarith))
  · exact Or.inr h

theorem causalCurveIn_axisLine (p : E0) : causality.CausalCurveIn ⊤ univ (axisLine p) where
  nonempty := univ_nonempty
  ordConnected := ordConnected_univ
  curve a _ b _ := by
    rcases curveOn_axisLine p ⊤ a b with h | h
    · exact causalCurveOn_of_curveOn h
    · exact absurd (fun _ _ => trivial) h

/-- **The BTZ axioms of the model `𝔼₀`** (`Causal.Causality.BTZAxioms`, DEC-64's corrected form
with `Iplus_of_lt`): the first instance at the paper's model `E₀`, whose BTZ points have a
non-empty chronological future (corrected from gx, whose docstring calls it the first instance
with a non-empty BTZ locus; `Causal.lightlikeLine_btzAxioms` is one, on the lightlike line). -/
theorem btzAxioms : causality.BTZAxioms axis where
  singularPastAt p hp := by
    have hp0 : p.2 = 0 := hp
    refine ⟨⟨fun n => (p.1 - 1 / ((n : ℝ) + 1), 0), ?_, fun n => ⟨?_, ?_⟩⟩, ?_⟩
    · have h1 : Tendsto (fun n : ℕ => p.1 - 1 / ((n : ℝ) + 1)) atTop (𝓝 p.1) := by
        have := (tendsto_const_nhds (x := p.1)).sub
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
        rwa [sub_zero] at this
      have := h1.prodMk_nhds (tendsto_const_nhds (x := (0 : ℂ)))
      rwa [show ((p.1, (0 : ℂ)) : E0) = p from Prod.ext rfl hp0.symm] at this
    · have : 0 < 1 / ((n : ℝ) + 1) := Nat.one_div_pos_of_nat
      exact le_top_iff.2 (le_axis rfl hp (by simp only; linarith))
    · intro h
      have := congrArg Prod.fst h
      simp only at this
      have : 0 < 1 / ((n : ℝ) + 1) := Nat.one_div_pos_of_nat
      linarith
    · intro x hxp hne
      obtain ⟨hx, hτ⟩ := (le_axis_iff' hp).1 (le_top_iff.1 hxp)
      have hlt : x.1 < p.1 := lt_of_le_of_ne hτ fun h => hne (axis_eq_of_fst_eq hx hp h)
      set d := p.1 - x.1 with hd
      have hd0 : 0 < d := by rw [hd]; linarith
      set u : ℕ → E0 := fun n => (p.1 - d / (2 * ((n : ℝ) + 1)), 0) with hu
      have hpos : ∀ n : ℕ, 0 < 2 * ((n : ℝ) + 1) := fun n => by positivity
      refine ⟨u, ?_, ?_, ?_, ?_⟩
      · have h1 : Tendsto (fun n : ℕ => d / (2 * ((n : ℝ) + 1))) atTop (𝓝 0) := by
          have : Tendsto (fun n : ℕ => (d / 2) * (1 / ((n : ℝ) + 1))) atTop (𝓝 ((d / 2) * 0)) :=
            tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat
          rw [mul_zero] at this
          refine this.congr fun n => ?_
          field_simp
        have h2 := (tendsto_const_nhds (x := p.1)).sub h1
        rw [sub_zero] at h2
        have := h2.prodMk_nhds (tendsto_const_nhds (x := (0 : ℂ)))
        rwa [show ((p.1, (0 : ℂ)) : E0) = p from Prod.ext rfl hp0.symm] at this
      · intro m n hmn
        refine le_top_iff.2 (le_axis rfl rfl ?_)
        simp only [hu]
        have : d / (2 * ((n : ℝ) + 1)) ≤ d / (2 * ((m : ℝ) + 1)) := by
          apply div_le_div_of_nonneg_left hd0.le (hpos m)
          have : (m : ℝ) ≤ n := by exact_mod_cast hmn
          linarith
        linarith
      · intro n
        have hax : u n ∈ axis := rfl
        rw [Jplus_axis hax]
        refine interior_maximal (t := {y | (u n).1 < fcoord y})
          (fun y (hy : (u n).1 < fcoord y) => hy.le) (isOpen_fcoord_gt _) ?_
        show (u n).1 < fcoord p
        rw [fcoord_of_axis hp]
        simp only [hu]
        have : 0 < d / (2 * ((n : ℝ) + 1)) := div_pos hd0 (hpos n)
        linarith
      · rw [Jminus_axis hp, Jminus_axis rfl]
        refine ⟨⟨hx, hτ⟩, mem_nhdsWithin.2 ⟨{w | w.1 < p.1 - d / 2}, isOpen_lt continuous_fst
          continuous_const, ?_, fun w ⟨hw1, hw2, _⟩ => ⟨hw2, ?_⟩⟩⟩
        · show x.1 < p.1 - d / 2
          rw [hd]; linarith
        · simp only [hu]
          have : (2 * (((0 : ℕ) : ℝ) + 1)) = 2 := by norm_num
          rw [this]
          exact hw1.le
  Iminus_eq_empty p hp := Iminus_axis hp ⊤
  Iplus_of_lt p hp p' hp' hle hne y hy := by
    obtain ⟨hy1, hy2⟩ := hy
    have hτ := (calculus_le hle).2.2.1
    have hlt : p.1 < p'.1 := lt_of_le_of_ne hτ fun h => hne (axis_eq_of_fst_eq hp hp' h)
    have hfy := (le_axis_iff hp').1 (le_top_iff.1 (Causal.Precausality.mem_Jplus_singleton.1 hy1))
    exact Causal.Precausality.mem_Iplus_singleton.2 (lt_top_iff.2 ((lt_axis_iff hp).2
      ⟨rad_pos.2 hy2, by linarith⟩))
  past_local p hp := ⟨⊤, trivial, fun q hq => ((le_axis_iff' hp).1 (le_of_le hq)).1⟩
  line p hp := by
    refine ⟨fun t => axisLine p t, Prod.ext (add_zero _) (show (0 : ℂ) = p.2 from (hp : p.2 = 0).symm), fun _ =>
      (isometry_axisLine p).isClosedEmbedding, ?_, ?_⟩
    · exact Causal.Causality.inextensible_of_unbounded (f := Prod.fst)
        (fun x y h => (calculus_le h).2.2.1) (causalCurveIn_axisLine p)
        (fun b => ⟨b - p.1 + 1, by simp only [axisLine]; linarith⟩)
        (fun b => ⟨b - p.1 - 1, by simp only [axisLine]; linarith⟩)
    · have hconn : IsPreconnected axis := by
        rw [← range_axisLine p]; exact isPreconnected_range (isometry_axisLine p).continuous
      rw [show (fun t => axisLine p t) = axisLine p from rfl, range_axisLine p,
        hconn.connectedComponentIn hp]

/-- **DEC-64's finding, a witness in `𝔼₀`**: the former `BTZAxioms.Iplus_eq`
(`I⁺(p) = J⁺(p) ∖ sing₀`, ETT l.1351) fails at every BTZ point: the point `(τ_p + 1/2, 1)` of the
radial null ray (`f = τ_p`) is in `J⁺(p) ∖ sing₀` and not in `I⁺(p)`. -/
theorem Iplus_ne_Jplus_diff (hp : p ∈ axis) :
    causality.Iplus ⊤ {p} ≠ causality.Jplus ⊤ {p} \ axis := by
  intro h
  set q : E0 := (p.1 + 1 / 2, 1)
  have hrq : rad q = 1 := by simp [rad, q]
  have hfq : fcoord q = p.1 := by simp only [fcoord, hrq, q]; ring
  have hq : q ∈ causality.Jplus ⊤ {p} \ axis := by
    refine ⟨?_, fun h' => by simp [axis, q] at h'⟩
    rw [Jplus_axis hp]; exact hfq.ge
  rw [← h, Iplus_axis hp] at hq
  exact absurd hq.2 (by rw [hfq]; exact lt_irrefl _)

/-- **`J⁺(V)` is open for every open `V`, BTZ points included** (lemma K's future-side obligation,
`BARBOT-INTERFACE.md`): at a BTZ point `p ∈ V`, `J⁺(p) ⊂ {f > τ_p − ε} ⊂ J⁺(p − ε)` with
`p − ε ∈ V` on the line; off the axis, `J⁺(v) ⊂ I⁺(v′)` for some `v′ ≪ v` in `V` (`Z⁻`). -/
theorem isOpen_Jplus {V : Set E0} (hV : IsOpen V) : IsOpen (causality.Jplus ⊤ V) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨v, hv, hvy⟩
  have hvy' := le_top_iff.1 hvy
  by_cases hax : v ∈ axis
  · obtain ⟨ε, hε, hmem⟩ := exists_axis_below hax (hV.mem_nhds hv)
    have hfy := (le_axis_iff hax).1 hvy'
    refine Filter.mem_of_superset ((isOpen_fcoord_gt (v.1 - ε)).mem_nhds (by
      show v.1 - ε < fcoord y; linarith)) fun w hw => ⟨_, hmem, le_top_iff.2 ((le_axis_iff rfl).2 ?_)⟩
    exact (le_of_lt hw : v.1 - ε ≤ fcoord w)
  · obtain ⟨v', hv', hlt⟩ := exists_lt_mem' hax (hV.mem_nhds hv)
    have hy : causality.lt ⊤ v' y := lt_top_iff.2 (hlt.trans_le hvy')
    refine Filter.mem_of_superset ((isOpen_CLt_right ⊤ v').mem_nhds hy) fun w hw =>
      ⟨v', hv', causality.le_of_lt hw⟩

/-- **`J⁻(V)` is open for every open `V`** (every point is in `Z⁺`). -/
theorem isOpen_Jminus {V : Set E0} (hV : IsOpen V) : IsOpen (causality.Jminus ⊤ V) := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨v, hv, hxv⟩
  obtain ⟨v', hv', hlt⟩ := exists_lt_mem v (hV.mem_nhds hv)
  have hx : causality.lt ⊤ x v' := lt_top_iff.2 ((le_top_iff.1 hxv).trans_lt hlt)
  exact Filter.mem_of_superset ((isOpen_CLt_left ⊤ v').mem_nhds hx) fun w hw =>
    ⟨v', hv', causality.le_of_lt hw⟩

end BTZ

/-! ### `defi:causal_E0` at the model (new)

The sentences of `defi:causal_E0` (`ETT.tex:1344–1356`), each at the model `E₀`: the singular
line is locally causal and not locally chronal, the past of a BTZ point, strong tarentinity at a
BTZ point, past distinguishing, and the chronological future of a BTZ point — false as printed,
with its strongest true form. -/

section Label

open TopologicalSpace

variable {p : E0}

/-- **The singular line is locally causal** (`ETT.tex:1345`): every segment of the axis lying
in an open set `W` is a future causal curve of `W`. -/
theorem axis_causalCurveOn (p : E0) (W : Opens E0) {a b : ℝ}
    (h : ∀ t ∈ Icc a b, axisLine p t ∈ W) : causality.CausalCurveOn W (axisLine p) a b := by
  rcases curveOn_axisLine p W a b with hc | hc
  · exact causalCurveOn_of_curveOn hc
  · exact absurd h hc

/-- **Nothing is chronologically below a BTZ point**, in any open set (`I^-_U(p) = ∅`). -/
theorem not_lt_of_mem_axis (hy : y ∈ axis) (U : Opens E0) (x : E0) : ¬ causality.lt U x y := by
  intro h
  have hx : x ∈ causality.Iminus U {y} := Causal.Precausality.mem_Iminus_singleton.2 h
  rw [Iminus_axis hy U] at hx
  exact hx

/-- **The singular line is not locally chronal** (`ETT.tex:1345`): no non-degenerate segment of
the axis is a future chronal curve of any open set. -/
theorem not_chronalCurveOn_axisLine (p : E0) (W : Opens E0) {a b : ℝ} (hab : a < b) :
    ¬ causality.ChronalCurveOn W (axisLine p) a b := fun hc =>
  not_lt_of_mem_axis (axisLine_mem p b) W _ (hc.lt_of_lt le_rfl hab le_rfl)

/-- **A BTZ point is strongly tarentin in the future but not in the past** (`ETT.tex:1348–1349`). -/
theorem mem_Zplus_not_mem_Zminus (hp : p ∈ axis) :
    p ∈ causality.Zplus ∧ p ∉ causality.Zminus :=
  ⟨mem_Zplus p, fun h => (mem_Zminus_iff p).1 h hp⟩

/-- The interior of the causal future of a BTZ point: `Int J^+(p) = {f > τ_p}`. -/
theorem interior_Jplus_axis (hp : p ∈ axis) :
    interior (causality.Jplus ⊤ {p}) = {y | p.1 < fcoord y} := by
  rw [Jplus_axis hp]
  refine Subset.antisymm (fun y hy => ?_)
    (interior_maximal (fun y (hy : p.1 < fcoord y) => show p.1 ≤ fcoord y from hy.le)
      (isOpen_fcoord_gt _))
  by_contra hlt
  have hle : fcoord y ≤ p.1 := not_lt.1 hlt
  have hmem : interior {y : E0 | p.1 ≤ fcoord y} ∈ 𝓝 y := isOpen_interior.mem_nhds hy
  have hcont : Continuous fun t : ℝ => ((y.1 - t, y.2) : E0) := by fun_prop
  have hT : Tendsto (fun t : ℝ => ((y.1 - t, y.2) : E0)) (𝓝[>] 0) (𝓝 y) := by
    have := hcont.tendsto 0
    simp only [sub_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  obtain ⟨t, hty, ht0⟩ := ((hT.eventually hmem).and self_mem_nhdsWithin).exists
  have h' := interior_subset hty
  simp only [mem_setOf_eq, fcoord, rad] at h' hle
  have ht0' : (0 : ℝ) < t := ht0
  linarith

/-- **The strongest true form of `I^+(p) = J^+(p) ∖ sing₀`** (`ETT.tex:1353–1355`): at a BTZ
point, `I^+(p) = Int(J^+(p)) ∖ sing₀` — the printed identity holds once `J^+(p)` is replaced by
its interior, i.e. once the null cone `{f = τ_p}` of `p` is removed. -/
theorem Iplus_axis_eq_interior_diff (hp : p ∈ axis) :
    causality.Iplus ⊤ {p} = interior (causality.Jplus ⊤ {p}) \ axis := by
  rw [Iplus_axis hp, interior_Jplus_axis hp]
  ext y
  simp only [mem_setOf_eq, Set.mem_sdiff, rad_pos]
  exact and_comm

/-- The half of the printed identity which holds: `I^+(p) ⊂ J^+(p) ∖ sing₀`. -/
theorem Iplus_axis_subset_diff (hp : p ∈ axis) :
    causality.Iplus ⊤ {p} ⊆ causality.Jplus ⊤ {p} \ axis := by
  rw [Iplus_axis_eq_interior_diff hp]
  exact sdiff_subset_sdiff_left interior_subset

end Label

end E0

namespace Causality

variable {M : Type*} [TopologicalSpace M]

/-- **Past distinguishing**, in its usual sense (ETT uses the phrase at `ETT.tex:1350` without
defining it; the reading is a question to the author): distinct points have distinct
chronological pasts. -/
def PastDistinguishing (C : Causality M) : Prop :=
  ∀ x y : M, C.Iminus ⊤ {x} = C.Iminus ⊤ {y} → x = y

/-- **The printed identity of `defi:causal_E0`** (`ETT.tex:1353–1355`), for a set `S₀` standing
for `sing₀`: `I^+(p) = J^+(p) ∖ S₀` at every point of `S₀`. It is false in `E₀`
(`E0.not_btzIplusAsPrinted`); kept as a `Prop`, never asserted (kb/0022). -/
def BTZIplusAsPrinted (C : Causality M) (S₀ : Set M) : Prop :=
  ∀ p ∈ S₀, C.Iplus ⊤ {p} = C.Jplus ⊤ {p} \ S₀

/-- **A causality with `SingularFlatAxioms` and a BTZ point is not past distinguishing**
(`ETT.tex:1349–1350`, abstractly: the `E_{≥0}`-manifold is read as the named model facts,
kb/0012): the BTZ point `p` and a point below it on its line (`singularPastAt`, in `sing₀` by
`mem_sing_zero_of_le`) both have empty chronological past. No causality in `lean-causal` yet
satisfies these hypotheses with a BTZ point (the `E₀` instance is `T-ett-port-e0-sfa`'s); the model
case is `E0.not_pastDistinguishing`. -/
theorem SingularFlatAxioms.not_pastDistinguishing {C : Causality M} {sing : ℝ → Set M}
    (h : C.SingularFlatAxioms sing) (hne : (sing 0).Nonempty) : ¬ C.PastDistinguishing := by
  intro hd
  obtain ⟨p, hp⟩ := hne
  obtain ⟨u, -, hu⟩ := (h.singularPastAt p hp).1
  have hu0 : u 0 ∈ sing 0 := h.mem_sing_zero_of_le hp (hu 0).1
  exact (hu 0).2 (hd _ _ (by rw [h.Iminus_eq_empty _ hu0, h.Iminus_eq_empty _ hp]))

end Causality

namespace E0

open TopologicalSpace

/-- **`E₀` is not past distinguishing** (`ETT.tex:1349–1350`, at the model, which is itself an
`E_{≥0}`-manifold with a BTZ line): two points of the axis have empty chronological pasts. -/
theorem not_pastDistinguishing : ¬ causality.PastDistinguishing := by
  intro h
  have h01 := h ((0 : ℝ), (0 : ℂ)) ((1 : ℝ), (0 : ℂ))
    (by rw [Iminus_axis (show ((0 : ℝ), (0 : ℂ)) ∈ axis from rfl) ⊤,
      Iminus_axis (show ((1 : ℝ), (0 : ℂ)) ∈ axis from rfl) ⊤])
  have := congrArg Prod.fst h01
  norm_num at this

/-- **The last sentence of `defi:causal_E0` is false** (`ETT.tex:1353–1355`; DEC-64): in `E₀`,
`I^+(p) = J^+(p) ∖ sing₀` fails at every BTZ point (`Iplus_ne_Jplus_diff`, the radial null ray). -/
theorem not_btzIplusAsPrinted : ¬ causality.BTZIplusAsPrinted axis := fun h =>
  Iplus_ne_Jplus_diff (show ((0 : ℝ), (0 : ℂ)) ∈ axis from rfl) (h _ rfl)

/-- **`defi:causal_E0` at the model `E₀`, assembled** (`ETT.tex:1344–1356`): the singular line is
locally causal and not locally chronal; at a BTZ point `p`, `I^-_U(p) = ∅` in every open `U` and
`J^-(p) = {r = 0, τ ≤ τ(p)}`; `p` is strongly tarentin in the future and not in the past; `E₀` is
not past distinguishing; `BTZAxioms` hold in DEC-64's form; and the printed
`I^+(p) = J^+(p) ∖ sing₀` is **false** at every BTZ point, its strongest true form being
`I^+(p) = Int(J^+(p)) ∖ sing₀`. -/
theorem causal_E0 :
    (∀ p ∈ axis, ∀ (W : Opens E0) (a b : ℝ), (∀ t ∈ Icc a b, axisLine p t ∈ W) →
      causality.CausalCurveOn W (axisLine p) a b) ∧
    (∀ p ∈ axis, ∀ (W : Opens E0) (a b : ℝ), a < b →
      ¬ causality.ChronalCurveOn W (axisLine p) a b) ∧
    (∀ p ∈ axis, ∀ U : Opens E0, causality.Iminus U {p} = ∅) ∧
    (∀ p ∈ axis, causality.Jminus ⊤ {p} = {x | x ∈ axis ∧ x.1 ≤ p.1}) ∧
    (∀ p ∈ axis, p ∈ causality.Zplus ∧ p ∉ causality.Zminus) ∧
    ¬ causality.PastDistinguishing ∧
    causality.BTZAxioms axis ∧
    (∀ p ∈ axis, causality.Iplus ⊤ {p} = interior (causality.Jplus ⊤ {p}) \ axis) ∧
    (∀ p ∈ axis, causality.Iplus ⊤ {p} ≠ causality.Jplus ⊤ {p} \ axis) :=
  ⟨fun p _ W _ _ h => axis_causalCurveOn p W h,
    fun p _ W _ _ hab => not_chronalCurveOn_axisLine p W hab,
    fun _ hp U => Iminus_axis hp U, fun _ hp => Jminus_axis hp,
    fun _ hp => mem_Zplus_not_mem_Zminus hp, not_pastDistinguishing, btzAxioms,
    fun _ hp => Iplus_axis_eq_interior_diff hp, fun _ hp => Iplus_ne_Jplus_diff hp⟩

end E0

end Causal
