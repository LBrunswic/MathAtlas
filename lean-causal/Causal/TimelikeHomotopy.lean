import Causal.CausalIsoInvariance
import Causal.GXStructure
import Causal.LinesCurves
import Causal.Inextensible
import Mathlib.Topology.Homotopy.Basic

/-!
# Chronal homotopies with fixed endpoints and future one-connectedness in ETT

Programme target `T-abs-timelike-homotopy` (`programme/roadmap.toml`; layer 1, stream abstract,
ETT-layer imports only, no model, no metric, no ladder hypothesis). Source: J. Sbierski, *The
C⁰-inextendibility of the Schwarzschild spacetime and the spacelike diameter in Lorentzian
geometry*, arXiv 1507.00601 v2, Def 2.13,
`papers/sbierski-schwarzschild/sources/1507.00601/eprint/InexSchwarzschild2.tex:380–386`.
**No label is marked**: no label of `ETT.tex` is concerned, and the Sbierski row
`schwdef:timelike_homotopic_fixed_endpoints` is a definition about Lorentzian manifolds with a
continuous metric, of which this file gives the ETT form for any causality (layer 1); that
Sbierski's timelike curves are chronal curves of the `C⁰` causality is the `C0` model's layer 3.

* `schwdef:timelike_homotopic_fixed_endpoints` (1) — `InexSchwarzschild2.tex:383`:
  `Causality.ChronalHomotopyOn W Γ γ₀ γ₁` (`Γ` continuous on `[0, 1]²`, every `Γ t` a future
  chronal curve of the open `W` over `[0, 1]` from `γ₀ 0` to `γ₀ 1`, `Γ 0 = γ₀`, `Γ 1 = γ₁` on
  `[0, 1]`) and the relation `Causality.ChronallyHomotopicOn W γ₀ γ₁` (some such `Γ`).
* `schwdef:timelike_homotopic_fixed_endpoints` (2) — `InexSchwarzschild2.tex:384`:
  `Causality.FutureOneConnectedOn W` (for all `p, q`, any two future chronal curves of `W` over
  `[0, 1]` from `p` to `q` are so homotopic) and `Causality.FutureOneConnected` (`W = ⊤`).
* The relation is an equivalence on the chronal curves of `W` over `[0, 1]`
  (`ChronallyHomotopicOn.refl`, `.symm`, `.trans`, `chronallyHomotopicOn_equivalence`): the
  transitivity glues two homotopies in `t`.
* Time reversal: `ChronalHomotopyOn.dual` (`C.dual`, the curve parameter reversed),
  `dual_chronallyHomotopicOn_iff`, `dual_futureOneConnectedOn` (future one-connectedness of
  `C.dual` is that of `C`). Causal isomorphisms: `IsCausalIso.chronalHomotopyOn`,
  `IsCausalIso.futureOneConnectedOn_iff`, `IsCausalIso.futureOneConnected_iff`. Charts which are
  isomorphisms: `ChartIso.chronalHomotopyOn`, `ChartIso.chronalHomotopyOn_symm`,
  `ChartIso.futureOneConnectedOn_iff`. The relation reads `≪` only
  (`futureOneConnectedOn_congr_lt`), which is the layer-1 content of the conformal invariance
  Sbierski notes (`:845`).
* Witness (kb/0011): the timelike line is future one-connected on every open set
  (`timelikeLine_futureOneConnectedOn`), by the convex combination of two strictly increasing
  maps (`timelikeLine_chronalCurveOn_iff`); it relates distinct curves
  (`timelikeLine_chronallyHomotopicOn_sq`).

> Definition. Let $(M,g)$ be a time-oriented Lorentzian manifold with a continuous metric.
> 1. Two future directed timelike curves $\gamma_i : [0,1] \to M$, $i = 0,1$, with
> $\gamma_0(0) = \gamma_1(0)$ and $\gamma_0(1) = \gamma_1(1)$ are called *timelike homotopic with
> fixed endpoints* if, and only if, there exists a continuous map
> $\Gamma : [0,1] \times [0,1] \to M$ such that $\Gamma(t, \cdot)$ is a future directed timelike
> curve from $\gamma_0(0)$ to $\gamma_0(1)$ for all $t \in [0,1]$ and, moreover,
> $\Gamma(0, \cdot) = \gamma_0(\cdot)$ and $\Gamma(1,\cdot) = \gamma_1(\cdot)$. The map $\Gamma$ is
> also called a *timelike homotopy with fixed endpoints between $\gamma_0$ and $\gamma_1$*.
> 2. We say that $(M,g)$ is *future one-connected* if, and only if, for all $p, q \in M$, any two
> future directed timelike curves from $p$ to $q$ are timelike homotopic with fixed endpoints.
> (`InexSchwarzschild2.tex:380–386`)

> We first note that whether a Lorentzian manifold is future one-connected or not depends only
> on the conformal class of the metric. (`InexSchwarzschild2.tex:845`)
-/

/-!
## The reading

* **"Future directed timelike curve" is a future chronal curve of `C`** (`Causal.Curves`,
  DEC-6: a continuous map locally increasing for `≪_N` on every small open `N`, injectivity not
  asked), over `[0, 1]`, in the open `W`. Def 2.13 says "future directed" explicitly, so only `C`
  is used, not `C.dual` (unlike Def 2.14's `ChronallySeparatedOn`, which reads "timelike" with no
  direction). Sbierski's timelike curves are piecewise smooth (Def 2.1, `:235`); under the `C0`
  model each of them is a chronal curve, not conversely, so the ETT notion quantifies over more
  curves and admits more homotopies: the comparison is layer 3 (question in the report).
* **Continuity of `Γ` is joint, on `[0, 1]²`** (`ContinuousOn (uncurry Γ) (Icc 0 1 ×ˢ Icc 0 1)`),
  as printed ("a continuous map Γ : [0,1] × [0,1] → M"), not the continuity of each slice (which
  every chronal curve has, `CurveOn.continuousOn`). Values of `Γ` and of the curves outside
  `[0, 1]` are irrelevant: every condition is asked on `[0, 1]` only.
* **The open set `W`** (kb/0001): `W = ⊤` is Sbierski's `M`; the `On` form is for the embedded
  spacetime `ι(N)`, an open set of the extension (Rem 2.3, `:248`). A chronal curve of `W` reads
  only the relations `≪_U`, `U ≤ W`, so `FutureOneConnectedOn W` is a property of `W` seen as a
  spacetime; it does not quantify over the smaller open sets, because Sbierski's notion is not
  hereditary.
* **The premise of (1)** ("two future directed timelike curves with the same endpoints") is a
  consequence of the existence of `Γ` (`ChronalHomotopyOn.chronalCurveOn_left`, `_right`,
  `right_zero`, `right_one`), so `ChronallyHomotopicOn` is `∃ Γ`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `(M, g)` time-oriented, continuous metric | ⚠ weakened: any causality `C` on a topological space (a `C⁰` metric's is one, the `C0` layer 3) |
| future directed timelike curves `[0, 1] → M` | ⚠ a reading: future chronal curves of `C` over `[0, 1]` in the open `W` (an incomparable class under `C0`, see SCOPE) |
| `Γ : [0,1] × [0,1] → M` continuous | ✓ carried: joint continuity on the square |
| fixed endpoints, `Γ(0, ·) = γ₀`, `Γ(1, ·) = γ₁` | ✓ carried, on `[0, 1]` |
| equivalence, time reversal, isomorphism invariance | not in the paper: the target's; no hypothesis beyond the curves |

## SCOPE (disclosed)

* **The curves are a reading, not a weakening**: future chronal curves of `C`, not Sbierski's
  piecewise smooth timelike curves. Under the `C0` model the ETT class contains his, so the ETT
  notion asks more homotopies of more curves; neither notion implies the other without a
  layer-3 comparison (see "The reading" above).
* Sbierski's Step 2.1 (`:567–579`, Minkowski) and Props 4.12, 6.5 (the Schwarzschild exterior
  and interior) are model facts (`T-loc-minkowski-future-one-connected` and the Schwarzschild
  model): no statement here. The printed homotopy of Step 2.1 has degenerate end slices (constant
  on half of `[0, 1]` at `t = 0` and at `t = 1`; the interior slices are fine), which no chronal
  curve of a chronological open set has (`ChronalCurveOn.injOn`); Lean witnesses the `t = 0`
  slice on the timelike line only (`timelikeLine_not_chronalCurveOn_pause`), while Sbierski's
  dimension is `d + 1 ≥ 2` (`:228`): a finding in the report (against Defs 2.1, 2.13), with the
  corrected formula.
* `ChartIso.chronalCurveOn_image`, `ChartIso.chronalCurveOn_symm_image` and
  `chartImage_subset_target`, written here first, are in `Causal.GXStructure` with the same full
  names (T-abs-hoist-stranded-homes, kb/0047), beside `ChartIso.curveOn_symm`, of which the `symm`
  form is now the `C.lt` case.
* Homotopies over a segment other than `[0, 1]` (Thm 4.11 uses `[0,1] × [y₀⁻, s]`, `:1623`) are
  the `[0, 1]` notion after an affine change of the curve parameter: not stated here.
* Spaces that are not future one-connected: the flat cylinder ℤe₁\𝐌^{1+1}
  (`Causal.Flat.spaceCylinder_separates`, by winding; T-abs-not-future-one-connected).
* **Moved in** (T-abs-sc-open-hoist): `Causality.ChronalHomotopyOn.homotopicRel`, a chronal
  homotopy is a homotopy of paths rel `{0, 1}` (`ContinuousMap.HomotopicRel`), from
  `Causal.Model.FlatSpaceCylinder`, byte for byte under the same full name; it reads only the
  joint continuity on `[0, 1]²` and the fixed endpoints. For it this module imports
  `Mathlib.Topology.Homotopy.Basic`, and no other new module.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Function

universe u v

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable (C : Causality M)

/-- **Sbierski Def 2.13 (1), the homotopy**: `Γ` is a *chronal homotopy with fixed endpoints* in
the open `W` between `γ₀` and `γ₁`. It is continuous on `[0, 1]²`, every `Γ t`, `t ∈ [0, 1]`, is
a future chronal curve of `W` over `[0, 1]` from `γ₀ 0` to `γ₀ 1`, and `Γ 0 = γ₀`, `Γ 1 = γ₁`
on `[0, 1]`. -/
structure ChronalHomotopyOn (W : Opens M) (Γ : ℝ → ℝ → M) (γ₀ γ₁ : ℝ → M) : Prop where
  continuousOn : ContinuousOn (uncurry Γ) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
  chronalCurveOn : ∀ t ∈ Icc (0 : ℝ) 1, C.ChronalCurveOn W (Γ t) 0 1
  fix_zero : ∀ t ∈ Icc (0 : ℝ) 1, Γ t 0 = γ₀ 0
  fix_one : ∀ t ∈ Icc (0 : ℝ) 1, Γ t 1 = γ₀ 1
  eqOn_zero : EqOn (Γ 0) γ₀ (Icc 0 1)
  eqOn_one : EqOn (Γ 1) γ₁ (Icc 0 1)

/-- **Sbierski Def 2.13 (1), the relation**: `γ₀` and `γ₁` are *chronally homotopic with fixed
endpoints* in `W`. The premise of the definition (two future chronal curves with the same
endpoints) follows (`ChronalHomotopyOn.chronalCurveOn_left`, `right_zero`, …). -/
def ChronallyHomotopicOn (W : Opens M) (γ₀ γ₁ : ℝ → M) : Prop :=
  ∃ Γ : ℝ → ℝ → M, C.ChronalHomotopyOn W Γ γ₀ γ₁

/-- **Sbierski Def 2.13 (2)**, for the open `W` seen as a spacetime: for all `p, q`, any two
future chronal curves of `W` over `[0, 1]` from `p` to `q` are chronally homotopic with fixed
endpoints in `W`. -/
def FutureOneConnectedOn (W : Opens M) : Prop :=
  ∀ p q : M, ∀ γ₀ γ₁ : ℝ → M,
    C.ChronalCurveOn W γ₀ 0 1 → γ₀ 0 = p → γ₀ 1 = q →
    C.ChronalCurveOn W γ₁ 0 1 → γ₁ 0 = p → γ₁ 1 = q →
    C.ChronallyHomotopicOn W γ₀ γ₁

/-- **Sbierski Def 2.13 (2)**: the spacetime is future one-connected. -/
def FutureOneConnected : Prop := C.FutureOneConnectedOn ⊤

variable {C} {W W' : Opens M} {Γ Γ' : ℝ → ℝ → M} {γ γ' γ₀ γ₀' γ₁ γ₁' γ₂ : ℝ → M}
  {c : ℝ → M} {a b : ℝ}

/-! ### Chronal curves of a chronological open set are injective -/

/-- A future chronal curve of `W` which takes one value twice gives a point `x ≪_W x`. -/
theorem ChronalCurveOn.lt_self_of_eq (hc : C.ChronalCurveOn W c a b) {s s' : ℝ} (hs : a ≤ s)
    (hss' : s < s') (hs' : s' ≤ b) (heq : c s = c s') : C.lt W (c s) (c s) := by
  have h := hc.lt_of_lt hs hss' hs'
  rw [← heq] at h
  exact h

/-- In an open set with no `x ≪_W x`, a future chronal curve is injective on its segment. -/
theorem ChronalCurveOn.injOn (hc : C.ChronalCurveOn W c a b) (hirr : ∀ x, ¬ C.lt W x x) :
    InjOn c (Icc a b) := by
  intro s hs s' hs' heq
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact hirr _ (hc.lt_self_of_eq hs.1 h hs'.2 heq)
  · exact hirr _ (hc.lt_self_of_eq hs'.1 h hs.2 heq.symm)

/-! ### The basic API of a homotopy -/

namespace ChronalHomotopyOn

theorem mapsTo (h : C.ChronalHomotopyOn W Γ γ₀ γ₁) :
    MapsTo (uncurry Γ) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) W := by
  exact fun p hp => (h.chronalCurveOn p.1 hp.1).mem p.2 hp.2

theorem chronalCurveOn_left (h : C.ChronalHomotopyOn W Γ γ₀ γ₁) : C.ChronalCurveOn W γ₀ 0 1 := by
  exact CurveOn.congr (h.chronalCurveOn 0 ⟨le_rfl, zero_le_one⟩) h.eqOn_zero

theorem chronalCurveOn_right (h : C.ChronalHomotopyOn W Γ γ₀ γ₁) :
    C.ChronalCurveOn W γ₁ 0 1 := by
  exact CurveOn.congr (h.chronalCurveOn 1 ⟨zero_le_one, le_rfl⟩) h.eqOn_one

theorem right_zero (h : C.ChronalHomotopyOn W Γ γ₀ γ₁) : γ₁ 0 = γ₀ 0 := by
  rw [← h.eqOn_one ⟨le_rfl, zero_le_one⟩, h.fix_zero 1 ⟨zero_le_one, le_rfl⟩]

theorem right_one (h : C.ChronalHomotopyOn W Γ γ₀ γ₁) : γ₁ 1 = γ₀ 1 := by
  rw [← h.eqOn_one ⟨zero_le_one, le_rfl⟩, h.fix_one 1 ⟨zero_le_one, le_rfl⟩]

theorem congr_left (h : C.ChronalHomotopyOn W Γ γ₀ γ₁) (h' : EqOn γ₀ γ₀' (Icc 0 1)) :
    C.ChronalHomotopyOn W Γ γ₀' γ₁ := by
  refine ⟨h.continuousOn, h.chronalCurveOn, fun t ht => ?_, fun t ht => ?_,
    fun s hs => (h.eqOn_zero hs).trans (h' hs), h.eqOn_one⟩
  · rw [h.fix_zero t ht, h' ⟨le_rfl, zero_le_one⟩]
  · rw [h.fix_one t ht, h' ⟨zero_le_one, le_rfl⟩]

theorem congr_right (h : C.ChronalHomotopyOn W Γ γ₀ γ₁) (h' : EqOn γ₁ γ₁' (Icc 0 1)) :
    C.ChronalHomotopyOn W Γ γ₀ γ₁' := by
  exact ⟨h.continuousOn, h.chronalCurveOn, h.fix_zero, h.fix_one, h.eqOn_zero,
    fun s hs => (h.eqOn_one hs).trans (h' hs)⟩

/-- A homotopy of `W` is a homotopy of every larger open set. -/
theorem mono_opens (h : C.ChronalHomotopyOn W Γ γ₀ γ₁) (hW : W ≤ W') :
    C.ChronalHomotopyOn W' Γ γ₀ γ₁ := by
  exact ⟨h.continuousOn, fun t ht => CurveOn.mono_opens C.isRelFamily_lt (h.chronalCurveOn t ht) hW,
    h.fix_zero, h.fix_one, h.eqOn_zero, h.eqOn_one⟩

/-- A homotopy of `W'` with values in the smaller open `W` on the square is a homotopy of `W`. -/
theorem restrict (h : C.ChronalHomotopyOn W' Γ γ₀ γ₁) (hW : W ≤ W')
    (hmem : MapsTo (uncurry Γ) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) W) :
    C.ChronalHomotopyOn W Γ γ₀ γ₁ := by
  exact ⟨h.continuousOn, fun t ht => CurveOn.restrict (h.chronalCurveOn t ht) le_rfl le_rfl hW
    (fun s hs => hmem (x := (t, s)) ⟨ht, hs⟩), h.fix_zero, h.fix_one, h.eqOn_zero, h.eqOn_one⟩

/-- The constant homotopy of a future chronal curve. -/
protected theorem refl (hγ : C.ChronalCurveOn W γ 0 1) : C.ChronalHomotopyOn W (fun _ => γ) γ γ := by
  exact ⟨(CurveOn.continuousOn C.isRelFamily_lt hγ).comp continuousOn_snd (fun _ hp => hp.2),
    fun _ _ => hγ, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- A homotopy run backwards in `t`. -/
protected theorem symm (h : C.ChronalHomotopyOn W Γ γ₀ γ₁) :
    C.ChronalHomotopyOn W (fun t => Γ (1 - t)) γ₁ γ₀ := by
  have hmaps : MapsTo (fun p : ℝ × ℝ => (1 - p.1, p.2)) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := fun p hp =>
    ⟨⟨by linarith [hp.1.2], by linarith [hp.1.1]⟩, hp.2⟩
  have hI : ∀ t ∈ Icc (0 : ℝ) 1, 1 - t ∈ Icc (0 : ℝ) 1 := fun t ht =>
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  refine ⟨h.continuousOn.comp ((continuous_const.sub continuous_fst).prodMk
      continuous_snd).continuousOn hmaps, fun t ht => h.chronalCurveOn _ (hI t ht),
    fun t ht => ?_, fun t ht => ?_, fun s hs => ?_, fun s hs => ?_⟩
  · rw [h.fix_zero _ (hI t ht), h.right_zero]
  · rw [h.fix_one _ (hI t ht), h.right_one]
  · show Γ (1 - 0) s = γ₁ s
    rw [sub_zero]; exact h.eqOn_one hs
  · show Γ (1 - 1) s = γ₀ s
    rw [sub_self]; exact h.eqOn_zero hs

/-- Two homotopies glued in `t`, each at double speed. -/
protected theorem trans (h : C.ChronalHomotopyOn W Γ γ₀ γ₁) (h' : C.ChronalHomotopyOn W Γ' γ₁ γ₂) :
    C.ChronalHomotopyOn W (fun t => if t ≤ 1 / 2 then Γ (2 * t) else Γ' (2 * t - 1)) γ₀ γ₂ := by
  have hI1 : ∀ t ∈ Icc (0 : ℝ) 1, t ≤ 1 / 2 → 2 * t ∈ Icc (0 : ℝ) 1 := fun t ht h1 =>
    ⟨by linarith [ht.1], by linarith⟩
  have hI2 : ∀ t ∈ Icc (0 : ℝ) 1, ¬ t ≤ 1 / 2 → 2 * t - 1 ∈ Icc (0 : ℝ) 1 := fun t ht h1 =>
    ⟨by linarith [not_le.1 h1], by linarith [ht.2]⟩
  have hsq : Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 ⊆
      (Icc 0 (1 / 2) ×ˢ Icc 0 1) ∪ (Icc (1 / 2) 1 ×ˢ Icc 0 1) := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    by_cases h1 : t ≤ 1 / 2
    · exact Or.inl ⟨⟨ht.1, h1⟩, hs⟩
    · exact Or.inr ⟨⟨(not_le.1 h1).le, ht.2⟩, hs⟩
  have hA : ContinuousOn (uncurry fun t => if t ≤ 1 / 2 then Γ (2 * t) else Γ' (2 * t - 1))
      (Icc 0 (1 / 2) ×ˢ Icc 0 1) := by
    have hc : ContinuousOn (fun p : ℝ × ℝ => uncurry Γ (2 * p.1, p.2)) (Icc 0 (1 / 2) ×ˢ Icc 0 1) :=
      h.continuousOn.comp ((continuous_const.mul continuous_fst).prodMk continuous_snd).continuousOn
        (fun p hp => ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩, hp.2⟩)
    refine hc.congr (fun p hp => ?_)
    show (if p.1 ≤ 1 / 2 then Γ (2 * p.1) else Γ' (2 * p.1 - 1)) p.2 = Γ (2 * p.1) p.2
    rw [if_pos hp.1.2]
  have hB : ContinuousOn (uncurry fun t => if t ≤ 1 / 2 then Γ (2 * t) else Γ' (2 * t - 1))
      (Icc (1 / 2) 1 ×ˢ Icc 0 1) := by
    have hc : ContinuousOn (fun p : ℝ × ℝ => uncurry Γ' (2 * p.1 - 1, p.2))
        (Icc (1 / 2) 1 ×ˢ Icc 0 1) :=
      h'.continuousOn.comp
        (((continuous_const.mul continuous_fst).sub continuous_const).prodMk
          continuous_snd).continuousOn
        (fun p hp => ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩, hp.2⟩)
    refine hc.congr (fun p hp => ?_)
    show (if p.1 ≤ 1 / 2 then Γ (2 * p.1) else Γ' (2 * p.1 - 1)) p.2 = Γ' (2 * p.1 - 1) p.2
    by_cases hp1 : p.1 ≤ 1 / 2
    · have hpe : p.1 = 1 / 2 := le_antisymm hp1 hp.1.1
      rw [if_pos hp1, hpe, show (2 : ℝ) * (1 / 2) = 1 by norm_num,
        show (1 : ℝ) - 1 = 0 by norm_num, h.eqOn_one hp.2, h'.eqOn_zero hp.2]
    · rw [if_neg hp1]
  refine ⟨(hA.union_of_isClosed hB (isClosed_Icc.prod isClosed_Icc)
      (isClosed_Icc.prod isClosed_Icc)).mono hsq, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_,
    fun s hs => ?_, fun s hs => ?_⟩
  · show C.ChronalCurveOn W (if t ≤ 1 / 2 then Γ (2 * t) else Γ' (2 * t - 1)) 0 1
    by_cases h1 : t ≤ 1 / 2
    · rw [if_pos h1]; exact h.chronalCurveOn _ (hI1 t ht h1)
    · rw [if_neg h1]; exact h'.chronalCurveOn _ (hI2 t ht h1)
  · show (if t ≤ 1 / 2 then Γ (2 * t) else Γ' (2 * t - 1)) 0 = γ₀ 0
    by_cases h1 : t ≤ 1 / 2
    · rw [if_pos h1]; exact h.fix_zero _ (hI1 t ht h1)
    · rw [if_neg h1, h'.fix_zero _ (hI2 t ht h1), h.right_zero]
  · show (if t ≤ 1 / 2 then Γ (2 * t) else Γ' (2 * t - 1)) 1 = γ₀ 1
    by_cases h1 : t ≤ 1 / 2
    · rw [if_pos h1]; exact h.fix_one _ (hI1 t ht h1)
    · rw [if_neg h1, h'.fix_one _ (hI2 t ht h1), h.right_one]
  · show (if (0 : ℝ) ≤ 1 / 2 then Γ (2 * 0) else Γ' (2 * 0 - 1)) s = γ₀ s
    rw [if_pos (by norm_num), mul_zero]
    exact h.eqOn_zero hs
  · show (if (1 : ℝ) ≤ 1 / 2 then Γ (2 * 1) else Γ' (2 * 1 - 1)) s = γ₂ s
    rw [if_neg (by norm_num), show (2 : ℝ) * 1 - 1 = 1 by norm_num]
    exact h'.eqOn_one hs

/-- **Time reversal**: reversing the curve parameter makes a homotopy of `C` a homotopy of
`C.dual` between the reversed curves. -/
protected theorem dual (h : C.ChronalHomotopyOn W Γ γ₀ γ₁) :
    C.dual.ChronalHomotopyOn W (fun t s => Γ t (1 - s)) (fun s => γ₀ (1 - s))
      (fun s => γ₁ (1 - s)) := by
  have hI : ∀ s ∈ Icc (0 : ℝ) 1, 1 - s ∈ Icc (0 : ℝ) 1 := fun s hs =>
    ⟨by linarith [hs.2], by linarith [hs.1]⟩
  refine ⟨h.continuousOn.comp (continuous_fst.prodMk
      (continuous_const.sub continuous_snd)).continuousOn (fun p hp => ⟨hp.1, hI _ hp.2⟩),
    fun t ht => ?_, fun t ht => ?_, fun t ht => ?_,
    fun s hs => h.eqOn_zero (hI s hs), fun s hs => h.eqOn_one (hI s hs)⟩
  · exact (CurveOn.reverse (h.chronalCurveOn t ht)).congr (fun s _ => by simp only [zero_add])
  · show Γ t (1 - 0) = γ₀ (1 - 0)
    rw [sub_zero]; exact h.fix_one t ht
  · show Γ t (1 - 1) = γ₀ (1 - 1)
    rw [sub_self]; exact h.fix_zero t ht

/-- **Time reversal on both parameters**: the curve parameter and the homotopy parameter. -/
theorem dual_symm (h : C.ChronalHomotopyOn W Γ γ₀ γ₁) :
    C.dual.ChronalHomotopyOn W (fun t s => Γ (1 - t) (1 - s)) (fun s => γ₁ (1 - s))
      (fun s => γ₀ (1 - s)) := by
  exact h.dual.symm

/-- A homotopy reads only the chronological relation. -/
theorem congr_lt {D : Causality M} (hCD : ∀ (U : Opens M) (x y : M), C.lt U x y ↔ D.lt U x y)
    (h : C.ChronalHomotopyOn W Γ γ₀ γ₁) : D.ChronalHomotopyOn W Γ γ₀ γ₁ := by
  have hlt : C.lt = D.lt := by funext U x y; exact propext (hCD U x y)
  refine ⟨h.continuousOn, fun t ht => ?_, h.fix_zero, h.fix_one, h.eqOn_zero, h.eqOn_one⟩
  show CurveOn D.lt W (Γ t) 0 1
  rw [← hlt]
  exact h.chronalCurveOn t ht

/-- **A chronal homotopy is a homotopy of paths relative to the endpoints**: for continuous maps
`f₀, f₁ : [0, 1] → M` agreeing with `γ₀, γ₁` on `[0, 1]`, a chronal homotopy with fixed endpoints
from `γ₀` to `γ₁` is a homotopy rel `{0, 1}` from `f₀` to `f₁`. Only the joint continuity on
`[0, 1]²` and the fixed endpoints are read. -/
theorem homotopicRel {M : Type*} [TopologicalSpace M]
    {C : Causality M} {W : Opens M} {Γ : ℝ → ℝ → M} {γ₀ γ₁ : ℝ → M}
    (h : C.ChronalHomotopyOn W Γ γ₀ γ₁) (f₀ f₁ : C(unitInterval, M))
    (hf₀ : ∀ s : unitInterval, f₀ s = γ₀ s) (hf₁ : ∀ s : unitInterval, f₁ s = γ₁ s) :
    f₀.HomotopicRel f₁ {0, 1} := by
  have hcont : Continuous fun x : unitInterval × unitInterval => Γ x.1 x.2 :=
    h.continuousOn.comp_continuous (f := fun x : unitInterval × unitInterval =>
      ((x.1 : ℝ), (x.2 : ℝ))) (by fun_prop) fun x => ⟨x.1.2, x.2.2⟩
  let F : ContinuousMap.HomotopyRel f₀ f₁ {0, 1} :=
    { toFun := fun x => Γ x.1 x.2
      continuous_toFun := hcont
      map_zero_left := fun s => by
        show Γ 0 s = f₀ s
        rw [hf₀]; exact h.eqOn_zero s.2
      map_one_left := fun s => by
        show Γ 1 s = f₁ s
        rw [hf₁]; exact h.eqOn_one s.2
      prop' := fun t s hs => by
        rcases hs with rfl | hs
        · show Γ t 0 = f₀ 0
          rw [hf₀]; exact h.fix_zero t t.2
        · rw [Set.mem_singleton_iff] at hs
          subst hs
          show Γ t 1 = f₀ 1
          rw [hf₀]; exact h.fix_one t t.2 }
  exact ⟨F⟩

end ChronalHomotopyOn

/-! ### The relation is an equivalence on the chronal curves -/

namespace ChronallyHomotopicOn

theorem chronalCurveOn_left (h : C.ChronallyHomotopicOn W γ₀ γ₁) : C.ChronalCurveOn W γ₀ 0 1 := by
  obtain ⟨_, hΓ⟩ := h
  exact hΓ.chronalCurveOn_left

theorem chronalCurveOn_right (h : C.ChronallyHomotopicOn W γ₀ γ₁) :
    C.ChronalCurveOn W γ₁ 0 1 := by
  obtain ⟨_, hΓ⟩ := h
  exact hΓ.chronalCurveOn_right

theorem right_zero (h : C.ChronallyHomotopicOn W γ₀ γ₁) : γ₁ 0 = γ₀ 0 := by
  obtain ⟨_, hΓ⟩ := h
  exact hΓ.right_zero

theorem right_one (h : C.ChronallyHomotopicOn W γ₀ γ₁) : γ₁ 1 = γ₀ 1 := by
  obtain ⟨_, hΓ⟩ := h
  exact hΓ.right_one

protected theorem refl (hγ : C.ChronalCurveOn W γ 0 1) : C.ChronallyHomotopicOn W γ γ := by
  exact ⟨_, ChronalHomotopyOn.refl hγ⟩

protected theorem symm (h : C.ChronallyHomotopicOn W γ₀ γ₁) : C.ChronallyHomotopicOn W γ₁ γ₀ := by
  obtain ⟨_, hΓ⟩ := h
  exact ⟨_, hΓ.symm⟩

protected theorem trans (h : C.ChronallyHomotopicOn W γ₀ γ₁) (h' : C.ChronallyHomotopicOn W γ₁ γ₂) :
    C.ChronallyHomotopicOn W γ₀ γ₂ := by
  obtain ⟨_, hΓ⟩ := h
  obtain ⟨_, hΓ'⟩ := h'
  exact ⟨_, hΓ.trans hΓ'⟩

/-- A chronal curve is homotopic to every map which agrees with it on `[0, 1]`. -/
theorem of_eqOn (hγ : C.ChronalCurveOn W γ 0 1) (h : EqOn γ γ' (Icc 0 1)) :
    C.ChronallyHomotopicOn W γ γ' := by
  exact ⟨_, (ChronalHomotopyOn.refl hγ).congr_right h⟩

theorem mono_opens (h : C.ChronallyHomotopicOn W γ₀ γ₁) (hW : W ≤ W') :
    C.ChronallyHomotopicOn W' γ₀ γ₁ := by
  obtain ⟨_, hΓ⟩ := h
  exact ⟨_, hΓ.mono_opens hW⟩

protected theorem dual (h : C.ChronallyHomotopicOn W γ₀ γ₁) :
    C.dual.ChronallyHomotopicOn W (fun s => γ₀ (1 - s)) (fun s => γ₁ (1 - s)) := by
  obtain ⟨_, hΓ⟩ := h
  exact ⟨_, hΓ.dual⟩

/-- A future chronal curve is homotopic to its reparametrisations by a continuous strictly
increasing map of `[0, 1]` onto itself (Sbierski's "modulo parametrisation", `:621`). -/
theorem comp_reparam (hγ : C.ChronalCurveOn W γ 0 1) {ψ : ℝ → ℝ} (hψ : StrictMonoOn ψ (Icc 0 1))
    (hψc : ContinuousOn ψ (Icc 0 1)) (hψ0 : ψ 0 = 0) (hψ1 : ψ 1 = 1) :
    C.ChronallyHomotopicOn W γ (γ ∘ ψ) := by
  have hψI : ∀ s ∈ Icc (0 : ℝ) 1, ψ s ∈ Icc (0 : ℝ) 1 := fun s hs =>
    ⟨hψ0 ▸ hψ.monotoneOn ⟨le_rfl, zero_le_one⟩ hs hs.1,
      hψ1 ▸ hψ.monotoneOn hs ⟨zero_le_one, le_rfl⟩ hs.2⟩
  have hφI : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, (1 - t) * s + t * ψ s ∈ Icc (0 : ℝ) 1 := by
    intro t ht s hs
    have := hψI s hs
    constructor <;> nlinarith [ht.1, ht.2, hs.1, hs.2, this.1, this.2]
  refine ⟨fun t s => γ ((1 - t) * s + t * ψ s), ⟨?_, fun t ht => ?_, fun t ht => ?_,
    fun t ht => ?_, fun s hs => ?_, fun s hs => ?_⟩⟩
  · have hinner : ContinuousOn (fun p : ℝ × ℝ => (1 - p.1) * p.2 + p.1 * ψ p.2)
        (Icc 0 1 ×ˢ Icc 0 1) :=
      (((continuous_const.sub continuous_fst).mul continuous_snd).continuousOn).add
        (continuousOn_fst.mul (hψc.comp continuousOn_snd (fun p hp => hp.2)))
    exact (CurveOn.continuousOn C.isRelFamily_lt hγ).comp hinner
      (fun p hp => hφI p.1 hp.1 p.2 hp.2)
  · have hmono : StrictMonoOn (fun s => (1 - t) * s + t * ψ s) (Icc 0 1) := by
      intro s hs s' hs' hss'
      have := hψ hs hs' hss'
      rcases ht.2.lt_or_eq with h1 | h1
      · nlinarith [ht.1]
      · rw [h1]; linarith
    have hcont : ContinuousOn (fun s => (1 - t) * s + t * ψ s) (Icc 0 1) :=
      (continuousOn_const.mul continuousOn_id).add (continuousOn_const.mul hψc)
    have h0 : (1 - t) * 0 + t * ψ 0 = 0 := by rw [hψ0]; ring
    have h1 : (1 - t) * 1 + t * ψ 1 = 1 := by rw [hψ1]; ring
    have hγ' : C.ChronalCurveOn W γ ((fun s => (1 - t) * s + t * ψ s) 0)
        ((fun s => (1 - t) * s + t * ψ s) 1) := by
      simp only [h0, h1]; exact hγ
    exact CurveOn.comp_strictMonoOn hγ' hmono hcont
  · show γ ((1 - t) * 0 + t * ψ 0) = γ 0
    rw [hψ0]; congr 1; ring
  · show γ ((1 - t) * 1 + t * ψ 1) = γ 1
    rw [hψ1]; congr 1; ring
  · show γ ((1 - 0) * s + 0 * ψ s) = γ s
    congr 1; ring
  · show γ ((1 - 1) * s + 1 * ψ s) = γ (ψ s)
    congr 1; ring

end ChronallyHomotopicOn

variable (C W) in
/-- **The homotopy relation is an equivalence** on the future chronal curves of `W` over
`[0, 1]`. -/
theorem chronallyHomotopicOn_equivalence :
    Equivalence (fun γ γ' : {γ : ℝ → M // C.ChronalCurveOn W γ 0 1} =>
      C.ChronallyHomotopicOn W γ.1 γ'.1) := by
  exact ⟨fun γ => ChronallyHomotopicOn.refl γ.2, fun h => h.symm, fun h h' => h.trans h'⟩

variable (C W) in
/-- The chronal homotopy classes with fixed endpoints of the future chronal curves of `W`. -/
def chronalHomotopySetoid : Setoid {γ : ℝ → M // C.ChronalCurveOn W γ 0 1} :=
  ⟨_, chronallyHomotopicOn_equivalence C W⟩

/-! ### Time reversal -/

theorem dual_chronallyHomotopicOn_iff :
    C.dual.ChronallyHomotopicOn W (fun s => γ₀ (1 - s)) (fun s => γ₁ (1 - s)) ↔
      C.ChronallyHomotopicOn W γ₀ γ₁ := by
  refine ⟨fun h => ?_, fun h => h.dual⟩
  obtain ⟨Γ, hΓ⟩ := h
  have hΓ' : C.ChronalHomotopyOn W (fun t s => Γ t (1 - s)) (fun s => γ₀ (1 - (1 - s)))
      (fun s => γ₁ (1 - (1 - s))) := ChronalHomotopyOn.dual (C := C.dual) hΓ
  exact ⟨_, (hΓ'.congr_left (fun s _ => by simp only [sub_sub_cancel])).congr_right
    (fun s _ => by simp only [sub_sub_cancel])⟩

theorem FutureOneConnectedOn.dual (h : C.FutureOneConnectedOn W) : C.dual.FutureOneConnectedOn W := by
  intro p q δ₀ δ₁ hδ₀ hp₀ hq₀ hδ₁ hp₁ hq₁
  have hr : ∀ δ : ℝ → M, C.dual.ChronalCurveOn W δ 0 1 →
      C.ChronalCurveOn W (fun s => δ (1 - s)) 0 1 :=
    fun δ hδ => (CurveOn.reverse hδ).congr (fun s _ => by simp only [zero_add])
  have hH := h q p _ _ (hr δ₀ hδ₀) (by simp [hq₀]) (by simp [hp₀]) (hr δ₁ hδ₁) (by simp [hq₁])
    (by simp [hp₁])
  have := hH.dual
  simpa only [sub_sub_cancel] using this

/-- **Future one-connectedness is invariant under time reversal.** -/
theorem dual_futureOneConnectedOn : C.dual.FutureOneConnectedOn W ↔ C.FutureOneConnectedOn W := by
  exact ⟨fun h => FutureOneConnectedOn.dual (C := C.dual) h, FutureOneConnectedOn.dual⟩

theorem dual_futureOneConnected : C.dual.FutureOneConnected ↔ C.FutureOneConnected :=
  dual_futureOneConnectedOn

/-- **Future one-connectedness reads only `≪`**: two causalities with the same chronological
relations are future one-connected together. This is the layer-1 content of Sbierski's remark that
the notion depends only on the conformal class (`:845`). -/
theorem futureOneConnectedOn_congr_lt {D : Causality M}
    (hCD : ∀ (U : Opens M) (x y : M), C.lt U x y ↔ D.lt U x y) :
    C.FutureOneConnectedOn W ↔ D.FutureOneConnectedOn W := by
  have key : ∀ {C D : Causality M}, (∀ (U : Opens M) (x y : M), C.lt U x y ↔ D.lt U x y) →
      C.FutureOneConnectedOn W → D.FutureOneConnectedOn W := by
    intro C D hCD h p q γ₀ γ₁ h₀ hp₀ hq₀ h₁ hp₁ hq₁
    have hlt : C.lt = D.lt := by funext U x y; exact propext (hCD U x y)
    have hback : ∀ c : ℝ → M, D.ChronalCurveOn W c 0 1 → C.ChronalCurveOn W c 0 1 := by
      intro c hc
      show CurveOn C.lt W c 0 1
      rw [hlt]; exact hc
    obtain ⟨Γ, hΓ⟩ := h p q γ₀ γ₁ (hback _ h₀) hp₀ hq₀ (hback _ h₁) hp₁ hq₁
    exact ⟨Γ, hΓ.congr_lt hCD⟩
  exact ⟨key hCD, key fun U x y => (hCD U x y).symm⟩

end Causality

/-! ### Causal isomorphisms -/

namespace IsCausalIso

variable {N : Type v} [TopologicalSpace N] {C : Causality M} {D : Causality N} {e : M ≃ₜ N}
  {W : Opens M} {Γ : ℝ → ℝ → M} {γ₀ γ₁ : ℝ → M}

/-- A causal isomorphism carries chronal homotopies. -/
theorem chronalHomotopyOn (h : IsCausalIso C D e) (hΓ : C.ChronalHomotopyOn W Γ γ₀ γ₁) :
    D.ChronalHomotopyOn (e.opensCongr W) (fun t s => e (Γ t s)) (e ∘ γ₀) (e ∘ γ₁) := by
  refine ⟨e.continuous.comp_continuousOn hΓ.continuousOn,
    fun t ht => h.chronalCurveOn_iff.1 (hΓ.chronalCurveOn t ht), fun t ht => ?_, fun t ht => ?_,
    fun s hs => ?_, fun s hs => ?_⟩
  · show e (Γ t 0) = e (γ₀ 0); rw [hΓ.fix_zero t ht]
  · show e (Γ t 1) = e (γ₀ 1); rw [hΓ.fix_one t ht]
  · show e (Γ 0 s) = e (γ₀ s); rw [hΓ.eqOn_zero hs]
  · show e (Γ 1 s) = e (γ₁ s); rw [hΓ.eqOn_one hs]

theorem chronallyHomotopicOn_iff (h : IsCausalIso C D e) :
    C.ChronallyHomotopicOn W γ₀ γ₁ ↔ D.ChronallyHomotopicOn (e.opensCongr W) (e ∘ γ₀) (e ∘ γ₁) := by
  refine ⟨fun ⟨_, hΓ⟩ => ⟨_, h.chronalHomotopyOn hΓ⟩, fun ⟨Δ, hΔ⟩ => ?_⟩
  have := h.symm.chronalHomotopyOn hΔ
  rw [symm_opensCongr_opensCongr] at this
  have hc : ∀ γ : ℝ → M, e.symm ∘ (e ∘ γ) = γ := fun γ => funext fun t => e.symm_apply_apply (γ t)
  rw [hc, hc] at this
  exact ⟨_, this⟩

theorem futureOneConnectedOn (h : IsCausalIso C D e) (hC : C.FutureOneConnectedOn W) :
    D.FutureOneConnectedOn (e.opensCongr W) := by
  intro p q δ₀ δ₁ h₀ hp₀ hq₀ h₁ hp₁ hq₁
  have hback : ∀ δ : ℝ → N, D.ChronalCurveOn (e.opensCongr W) δ 0 1 →
      C.ChronalCurveOn W (e.symm ∘ δ) 0 1 := by
    intro δ hδ
    have := h.symm.chronalCurveOn_iff.1 hδ
    rwa [symm_opensCongr_opensCongr] at this
  have hee : ∀ δ : ℝ → N, e ∘ (e.symm ∘ δ) = δ := fun δ => funext fun t => e.apply_symm_apply (δ t)
  obtain ⟨Γ, hΓ⟩ := hC (e.symm p) (e.symm q) _ _ (hback δ₀ h₀) (by simp [hp₀]) (by simp [hq₀])
    (hback δ₁ h₁) (by simp [hp₁]) (by simp [hq₁])
  have := h.chronalHomotopyOn hΓ
  rw [hee, hee] at this
  exact ⟨_, this⟩

/-- **Future one-connectedness is invariant under causal isomorphisms.** -/
theorem futureOneConnectedOn_iff (h : IsCausalIso C D e) :
    C.FutureOneConnectedOn W ↔ D.FutureOneConnectedOn (e.opensCongr W) := by
  refine ⟨h.futureOneConnectedOn, fun hD => ?_⟩
  have := h.symm.futureOneConnectedOn hD
  rwa [symm_opensCongr_opensCongr] at this

theorem futureOneConnected_iff (h : IsCausalIso C D e) :
    C.FutureOneConnected ↔ D.FutureOneConnected := by
  show C.FutureOneConnectedOn ⊤ ↔ D.FutureOneConnectedOn ⊤
  rw [h.futureOneConnectedOn_iff, opensCongr_top]

end IsCausalIso

/-! ### Charts which are isomorphisms

The curve transport `ChartIso.chronalCurveOn_image`, `ChartIso.chronalCurveOn_symm_image` and
`chartImage_subset_target` are in `Causal.GXStructure` (moved by T-abs-hoist-stranded-homes). -/

namespace ChartIso

variable {X : Type v} [TopologicalSpace X] {C : Causality M} {D : Causality X}
  {e : OpenPartialHomeomorph M X} {W : Opens M} {Γ : ℝ → ℝ → M} {Δ : ℝ → ℝ → X}
  {γ₀ γ₁ c : ℝ → M} {δ₀ δ₁ d : ℝ → X} {a b : ℝ}

theorem chronalHomotopyOn (h : ChartIso C D e) (hW : W ≤ chartSource e)
    (hΓ : C.ChronalHomotopyOn W Γ γ₀ γ₁) :
    D.ChronalHomotopyOn (chartImage e W) (fun t s => e (Γ t s)) (e ∘ γ₀) (e ∘ γ₁) := by
  refine ⟨e.continuousOn.comp hΓ.continuousOn (fun p hp => hW (hΓ.mapsTo hp)),
    fun t ht => h.chronalCurveOn_image hW (hΓ.chronalCurveOn t ht), fun t ht => ?_, fun t ht => ?_,
    fun s hs => ?_, fun s hs => ?_⟩
  · show e (Γ t 0) = e (γ₀ 0); rw [hΓ.fix_zero t ht]
  · show e (Γ t 1) = e (γ₀ 1); rw [hΓ.fix_one t ht]
  · show e (Γ 0 s) = e (γ₀ s); rw [hΓ.eqOn_zero hs]
  · show e (Γ 1 s) = e (γ₁ s); rw [hΓ.eqOn_one hs]

theorem chronalHomotopyOn_symm (h : ChartIso C D e) (hW : W ≤ chartSource e)
    (hΔ : D.ChronalHomotopyOn (chartImage e W) Δ δ₀ δ₁) :
    C.ChronalHomotopyOn W (fun t s => e.symm (Δ t s)) (e.symm ∘ δ₀) (e.symm ∘ δ₁) := by
  refine ⟨e.continuousOn_symm.comp hΔ.continuousOn
      (fun p hp => chartImage_subset_target W (hΔ.mapsTo hp)),
    fun t ht => h.chronalCurveOn_symm_image hW (hΔ.chronalCurveOn t ht), fun t ht => ?_,
    fun t ht => ?_, fun s hs => ?_, fun s hs => ?_⟩
  · show e.symm (Δ t 0) = e.symm (δ₀ 0); rw [hΔ.fix_zero t ht]
  · show e.symm (Δ t 1) = e.symm (δ₀ 1); rw [hΔ.fix_one t ht]
  · show e.symm (Δ 0 s) = e.symm (δ₀ s); rw [hΔ.eqOn_zero hs]
  · show e.symm (Δ 1 s) = e.symm (δ₁ s); rw [hΔ.eqOn_one hs]

theorem chronallyHomotopicOn_iff (h : ChartIso C D e) (hW : W ≤ chartSource e)
    (h₀ : MapsTo γ₀ (Icc 0 1) W) (h₁ : MapsTo γ₁ (Icc 0 1) W) :
    C.ChronallyHomotopicOn W γ₀ γ₁ ↔
      D.ChronallyHomotopicOn (chartImage e W) (e ∘ γ₀) (e ∘ γ₁) := by
  have hl : ∀ γ : ℝ → M, MapsTo γ (Icc 0 1) W → EqOn (e.symm ∘ (e ∘ γ)) γ (Icc 0 1) :=
    fun γ hγ _ hs => e.left_inv (hW (hγ hs))
  refine ⟨fun ⟨_, hΓ⟩ => ⟨_, h.chronalHomotopyOn hW hΓ⟩, fun ⟨_, hΔ⟩ => ?_⟩
  exact ⟨_, ((h.chronalHomotopyOn_symm hW hΔ).congr_left (hl γ₀ h₀)).congr_right (hl γ₁ h₁)⟩

/-- **Future one-connectedness passes through a chart which is an isomorphism**, both ways. -/
theorem futureOneConnectedOn_iff (h : ChartIso C D e) (hW : W ≤ chartSource e) :
    C.FutureOneConnectedOn W ↔ D.FutureOneConnectedOn (chartImage e W) := by
  have hl : ∀ γ : ℝ → M, MapsTo γ (Icc 0 1) W → EqOn (e.symm ∘ (e ∘ γ)) γ (Icc 0 1) :=
    fun γ hγ _ hs => e.left_inv (hW (hγ hs))
  have hr : ∀ δ : ℝ → X, MapsTo δ (Icc 0 1) (chartImage e W) →
      EqOn (e ∘ (e.symm ∘ δ)) δ (Icc 0 1) :=
    fun δ hδ _ hs => e.right_inv (chartImage_subset_target W (hδ hs))
  constructor
  · intro hC p q δ₀ δ₁ h₀ hp₀ hq₀ h₁ hp₁ hq₁
    obtain ⟨Γ, hΓ⟩ := hC (e.symm p) (e.symm q) _ _ (h.chronalCurveOn_symm_image hW h₀)
      (by simp [hp₀]) (by simp [hq₀]) (h.chronalCurveOn_symm_image hW h₁) (by simp [hp₁])
      (by simp [hq₁])
    exact ⟨_, ((h.chronalHomotopyOn hW hΓ).congr_left (hr δ₀ fun t ht => h₀.mem t ht)).congr_right
      (hr δ₁ fun t ht => h₁.mem t ht)⟩
  · intro hD p q γ₀ γ₁ h₀ hp₀ hq₀ h₁ hp₁ hq₁
    obtain ⟨Δ, hΔ⟩ := hD (e p) (e q) _ _ (h.chronalCurveOn_image hW h₀) (by simp [hp₀])
      (by simp [hq₀]) (h.chronalCurveOn_image hW h₁) (by simp [hp₁]) (by simp [hq₁])
    exact ⟨_, ((h.chronalHomotopyOn_symm hW hΔ).congr_left
      (hl γ₀ fun t ht => h₀.mem t ht)).congr_right (hl γ₁ fun t ht => h₁.mem t ht)⟩

end ChartIso

/-! ### The witness: the timelike line -/

/-- On the timelike line, the future chronal curves of `U` over `[a, b]` are the continuous
strictly increasing maps of `[a, b]` into `U`. -/
theorem timelikeLine_chronalCurveOn_iff {U : Opens ℝ} {c : ℝ → ℝ} {a b : ℝ} :
    timelikeLine.ChronalCurveOn U c a b ↔
      StrictMonoOn c (Icc a b) ∧ ContinuousOn c (Icc a b) ∧ MapsTo c (Icc a b) U := by
  constructor
  · intro hc
    refine ⟨fun s hs s' hs' hss' => ?_, CurveOn.continuousOn timelikeLine.isRelFamily_lt hc,
      fun s hs => hc.mem s hs⟩
    exact (timelikeLine_lt.1 (hc.lt_of_lt hs.1 hss' hs'.2)).1
  · rintro ⟨hmono, hcont, hmaps⟩
    refine ⟨fun t ht => hmaps ht, fun t ht N _ htN => ?_⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 N.isOpen (c t) htN
    obtain ⟨δ, hδ, hδc⟩ := Metric.continuousWithinAt_iff.1 (hcont t ht) ε hε
    refine ⟨t - δ, t + δ, by linarith, by linarith, fun s hs s' hs' h1 h2 h3 => ?_⟩
    have hd1 : dist s t < δ := by rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    have hd2 : dist s' t < δ := by rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    have hc1 := hδc hs hd1
    have hc2 := hδc hs' hd2
    rw [Real.dist_eq, abs_lt] at hc1 hc2
    refine timelikeLine_lt.2 ⟨hmono hs hs' h2, fun z hz => hball ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hz.1, hz.2]

/-- **The timelike line is future one-connected on every open set**: two future chronal curves
with the same endpoints are homotopic through their convex combinations. -/
theorem timelikeLine_futureOneConnectedOn (W : Opens ℝ) : timelikeLine.FutureOneConnectedOn W := by
  intro p q γ₀ γ₁ h₀ hp₀ hq₀ h₁ hp₁ hq₁
  obtain ⟨m₀, c₀, -⟩ := timelikeLine_chronalCurveOn_iff.1 h₀
  obtain ⟨m₁, c₁, -⟩ := timelikeLine_chronalCurveOn_iff.1 h₁
  have hsub : Icc p q ⊆ (W : Set ℝ) := by
    have := (timelikeLine_lt.1 (h₀.lt_of_lt le_rfl zero_lt_one le_rfl)).2
    rwa [hp₀, hq₀] at this
  have hI0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hI1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hbd : ∀ γ : ℝ → ℝ, StrictMonoOn γ (Icc 0 1) → γ 0 = p → γ 1 = q →
      ∀ s ∈ Icc (0 : ℝ) 1, γ s ∈ Icc p q := fun γ hm h0 h1 s hs =>
    ⟨h0 ▸ hm.monotoneOn hI0 hs hs.1, h1 ▸ hm.monotoneOn hs hI1 hs.2⟩
  refine ⟨fun t s => (1 - t) * γ₀ s + t * γ₁ s, ⟨?_, fun t ht => ?_, fun t ht => ?_,
    fun t ht => ?_, fun s hs => ?_, fun s hs => ?_⟩⟩
  · have hc : ContinuousOn (fun x : ℝ × ℝ => (1 - x.1) * γ₀ x.2 + x.1 * γ₁ x.2)
        (Icc 0 1 ×ˢ Icc 0 1) :=
      ((continuousOn_const.sub continuousOn_fst).mul
        (c₀.comp continuousOn_snd fun x hx => hx.2)).add
        (continuousOn_fst.mul (c₁.comp continuousOn_snd fun x hx => hx.2))
    exact hc
  · refine timelikeLine_chronalCurveOn_iff.2 ⟨fun s hs s' hs' hss' => ?_,
      (continuousOn_const.mul c₀).add (continuousOn_const.mul c₁), fun s hs => hsub ?_⟩
    · have a0 := m₀ hs hs' hss'
      have a1 := m₁ hs hs' hss'
      show (1 - t) * γ₀ s + t * γ₁ s < (1 - t) * γ₀ s' + t * γ₁ s'
      rcases ht.2.lt_or_eq with h | h
      · nlinarith [ht.1]
      · rw [h]; linarith
    · have b0 := hbd γ₀ m₀ hp₀ hq₀ s hs
      have b1 := hbd γ₁ m₁ hp₁ hq₁ s hs
      show (1 - t) * γ₀ s + t * γ₁ s ∈ Icc p q
      constructor <;> nlinarith [ht.1, ht.2, b0.1, b0.2, b1.1, b1.2]
  · show (1 - t) * γ₀ 0 + t * γ₁ 0 = γ₀ 0
    rw [hp₁, hp₀]; ring
  · show (1 - t) * γ₀ 1 + t * γ₁ 1 = γ₀ 1
    rw [hq₁, hq₀]; ring
  · show (1 - 0) * γ₀ s + 0 * γ₁ s = γ₀ s
    ring
  · show (1 - 1) * γ₀ s + 1 * γ₁ s = γ₁ s
    ring

theorem timelikeLine_futureOneConnected : timelikeLine.FutureOneConnected :=
  timelikeLine_futureOneConnectedOn ⊤

/-- The time-reversed timelike line is future one-connected. -/
theorem timelikeLine_dual_futureOneConnected : timelikeLine.dual.FutureOneConnected :=
  Causality.dual_futureOneConnected.2 timelikeLine_futureOneConnected

/-- The relation is not the identity: `s ↦ s` and `s ↦ s²` are distinct chronal curves of the
timelike line over `[0, 1]`, and are homotopic. -/
theorem timelikeLine_chronallyHomotopicOn_sq :
    timelikeLine.ChronallyHomotopicOn ⊤ id (fun s => s ^ 2) ∧ id ≠ (fun s : ℝ => s ^ 2) := by
  have hid : timelikeLine.ChronalCurveOn ⊤ id 0 1 :=
    timelikeLine_chronalCurveOn_iff.2 ⟨strictMonoOn_id, continuousOn_id, fun _ _ => trivial⟩
  have hsq : timelikeLine.ChronalCurveOn ⊤ (fun s : ℝ => s ^ 2) 0 1 :=
    timelikeLine_chronalCurveOn_iff.2 ⟨fun s hs s' _ h => by nlinarith [hs.1],
      (continuous_pow 2).continuousOn, fun _ _ => trivial⟩
  refine ⟨timelikeLine_futureOneConnected 0 1 id _ hid rfl rfl hsq (by norm_num) (by norm_num),
    fun h => ?_⟩
  have := congrFun h (1 / 2)
  norm_num at this

/-- **Sbierski's Step 2.1 slice at `t = 0`** (`InexSchwarzschild2.tex:572–579`, `λ(0) = 0`):
`Γ(0, s) = (σ_{λ(0)} * λ)(s)` is `0` on `[0, 1/2]`, so it is not a future chronal curve of the
timelike line (the `1 + 0`-dimensional Minkowski space), whatever `λ` and the open set. -/
theorem timelikeLine_not_chronalCurveOn_pause (lam : ℝ → ℝ) (hlam : lam 0 = 0) (W : Opens ℝ) :
    ¬ timelikeLine.ChronalCurveOn W
      (fun s => if s ≤ 1 / 2 then (2 * s) * lam 0 else lam (2 * s - 1)) 0 1 := by
  intro hc
  have hinj := hc.injOn (fun x hx => lt_irrefl x (timelikeLine_lt.1 hx).1)
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h12 : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have := hinj h0 h12 (by norm_num [hlam])
  norm_num at this

end Causal
