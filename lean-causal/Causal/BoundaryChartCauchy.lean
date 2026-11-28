import Causal.PastInextensibleMeetsCauchy
import Causal.SchwCausalLemmas
import Causal.ErsUniqueness

/-!
# The inside of a boundary chart is future-closed: Sbierski 2312.07443 (2.4) in ETT

Programme target `T-abs-boundary-chart-cauchy` (`programme/roadmap.toml`; layer 1: it imports
`Causal.PastInextensibleMeetsCauchy`, `Causal.SchwCausalLemmas` and, for the witness,
`Causal.ErsUniqueness`, all ETT-layer; no model; no metric, curve length or geodesic in a
statement). There is no statement of `ETT.tex` behind it, so **no label is marked**. It is the
step (2.4) of Sbierski 2312.07443 Prop 2.1, read for the past boundary chart, and as printed:

> any past directed causal curve in Ũ starting below the graph of f remains below the graph of f .
> (2.4) Otherwise, if it were to cross the graph of f , it would give rise, via ι−1 , to a past
> directed past inextendible causal curve in M which starts in I + (Σ, M ) but does not intersect
> Σ – which contradicts Σ being a Cauchy hypersurface.
> (`references/sbierski/text/sbierski2023c.txt:352–358`)

## What is proved (no `sorry`)

1. **The curve form** (`Causality.mapsTo_inside_of_boundaryChart`, the past boundary chart): on a
   T2, second countable space, let `S` be a Cauchy surface of a causally arc-connected open `W`
   with `≤_W` antisymmetric, `Ũ` open, `V ≤ W` open with `V ⊆ J⁻(S, W)`, and no point of
   `(Ũ ∩ closure V) ∖ V` in `W`. Then every future causal curve of `Ũ` starting in `V` stays in
   `V`. `V` disjoint from `S` (the target's hypothesis) is **not needed**: after the curve meets
   `S` it is constant (`S` acausal, `≤_W` antisymmetric), so it cannot reach the frontier. Over
   any interval: `mapsTo_inside_of_boundaryChart_of_causalCurveIn`. Sbierski's (2.2) shape
   `V ⊆ I⁻(S, W)`: `mapsTo_inside_of_boundaryChart_of_Iminus`, no irreflexivity of `≪_W` asked.
2. **The relation forms** (T-abs-flrw-type's field (iii)): if `Ũ` is causally arc-connected and
   `V ≤ Ũ`, then `I⁺(x, Ũ) ⊆ I⁺(x, V)` and `J⁺(x, Ũ) ⊆ J⁺(x, V)` for `x ∈ V`
   (`Iplus_subset_inside_of_boundaryChart`, `Jplus_subset_inside_of_boundaryChart`), through a
   general step (`Iplus_subset_Iplus_of_forall_mapsTo`, `Jplus_subset_Jplus_of_forall_mapsTo`).
3. **The time reversal, (2.4) as printed** (the future boundary chart, `V ⊆ J⁺(S, W)`): every
   past-directed causal curve of `Ũ` (a future causal curve of `C.dual`) starting in `V` stays in
   `V` (`mapsTo_inside_of_futureBoundaryChart`; with (2.2) as printed, `V ⊆ I⁺(S, W)`:
   `…_of_Iplus`); every future causal curve of `Ũ` ending in `V` lies in `V`
   (`…_of_end_mem`); `I⁻(x, Ũ) ⊆ I⁻(x, V)`, `J⁻(x, Ũ) ⊆ J⁻(x, V)`
   (`Iminus_subset_inside_of_futureBoundaryChart`, `Jminus_subset_inside_of_futureBoundaryChart`).
4. **Witnesses** (kb/0011), on the timelike line. `W = ]0, ∞[`, `S = {1}` (Cauchy:
   `timelikeLine_isCauchySurfaceOn_Ioi_zero_one`, the range of `exp`), `Ũ = ]-1, 1[`, `V = ]0, 1[`:
   all hypotheses jointly, the theorem applied, the past direction failing
   (`timelikeLine_boundaryChart_witness`). Its time reversal, `W = ]-∞, 0[`, `S = {-1}`,
   `V = ]-1, 0[` (`timelikeLine_futureBoundaryChart_witness`). The two hypotheses that carry the
   argument cannot be dropped (`timelikeLine_boundaryChart_needs_frontier`,
   `timelikeLine_boundaryChart_needs_Jminus`).

## Hypothesis checklist

| Sbierski (2.4), past chart / the target | here |
|---|---|
| `M̃` a manifold; target: T2, 2nd countable | ✓ `[T2Space M] [SecondCountableTopology M]` |
| `Σ` a Cauchy hypersurface of `(M, g)` | ✓ `C.IsCauchySurfaceOn W S` (DEC-14), `W = ι(M)` |
| `(M, g)` globally hyperbolic | ⚠ weakened: two consequences, `W` arc-connected, `≤_W` antisym. |
| `Ũ` the chart domain | ✓ `U : Opens M` |
| `Ũ_>` open, in `ι(M) ∩ Ũ` ((2.2) reversed; the printed future chart has `Ũ_<`) | ⚠ weakened: `V ≤ W`; `V ≤ Ũ` for the relation forms only |
| (2.2) reversed: `Ũ_> ⊆ ι(I⁻(Σ, M))` (printed: `Ũ_< ⊆ ι(I⁺(Σ, M))`) | ⚠ weakened: `V ⊆ J⁻(S, W)` (`J⁺` for the future chart); the `I` form a corollary |
| the target: `V` disjoint from `S` | ⚠ weakened: not assumed |
| (2.3) reversed: graph of `f` in `∂⁻ι(M)` (printed: `∂⁺`) | ✓ as the frontier: `(Ũ ∩ closure V) ∖ V` misses `W` (`f`'s continuity turns (2.3) into this) |
| the graph achronal; `f` Lipschitz beyond continuity; `δ`, the cone sandwich | ⚠ weakened: not used |
| relation forms: `Ũ` causally arc-connected (a hypothesis the target adds; implicit for a chart domain) | ✓ `C.CausallyArcConnectedOn U` |

## SCOPE (disclosed)

* **Nothing marked**: 2312.07443 is not ledgered and has no binder.
* **The reading** (as for `Causal.C0ExtensionSkeleton`, OQ-154): Sbierski's `M̃` is `M` with the
  causality `C`, `ι(M)` is the open `W`, his relations in `Ũ` and in `M` are those of the opens
  `Ũ` and `W`; the chart's product structure enters only through the frontier hypothesis (the
  graph of `f` is the frontier of `Ũ_<` in `Ũ`, and (2.3) puts it in `∂ι(M)`, which misses `W`).
  Proving that a `C⁰` boundary chart satisfies these hypotheses is layer 3
  (T-loc-c0-past-boundary-chart).
* **The Cauchy and orientation readings** (the REPORT's questions 1–2): "Cauchy hypersurface" is
  DEC-14's `IsCauchySurfaceOn` (every inextensible causal curve of `W` meets `S` exactly once). A
  Lorentzian Cauchy hypersurface defined by timelike curves and containing a null segment is not
  DEC-14 Cauchy: the theorems then apply after `Σ` is replaced by an acausal Cauchy `S` with
  `V ⊆ J^∓(S, W)`. The time orientation of `Ũ` is the one `C` gives (OQ-115), not decided here.
* `causal_ladder` is not used: no statement concludes a ladder property.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter

universe u

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable {C : Causality M} {W U V : Opens M} {S : Set M}

/-- **Sbierski 2312.07443 (2.4) in ETT, for the past boundary chart.** On a T2, second countable
space, let `S` be a Cauchy surface of a causally arc-connected open `W` on which `≤_W` is
antisymmetric, `U` (Sbierski's `Ũ`) open and `V ≤ W` open with `V ⊆ J⁻(S, W)` and no point of
`(U ∩ closure V) ∖ V` in `W`. Then every future causal curve of `U` starting in `V` stays in `V`.
No disjointness of `V` and `S` is assumed. -/
theorem mapsTo_inside_of_boundaryChart [T2Space M] [SecondCountableTopology M]
    (hS : C.IsCauchySurfaceOn W S) (hC : C.CausallyArcConnectedOn W)
    (hcaus : ∀ ⦃x y : M⦄, C.le W x y → C.le W y x → x = y) (hVW : V ≤ W)
    (hVJ : (V : Set M) ⊆ C.Jminus W S)
    (hfr : ∀ x ∈ ((U : Set M) ∩ closure (V : Set M)) \ V, x ∉ W)
    {c : ℝ → M} {a b : ℝ} (hc : C.CausalCurveOn U c a b) (hca : c a ∈ V) :
    MapsTo c (Icc a b) V := by
  intro t₁ ht₁
  by_contra ht₁V
  -- the first exit time `τ`
  have hcont : ContinuousOn c (Icc a b) := CurveOn.continuousOn C.isRelFamily_le hc
  set T : Set ℝ := Icc a b ∩ c ⁻¹' (V : Set M)ᶜ with hT
  have hTcl : IsClosed T :=
    hcont.preimage_isClosed_of_isClosed isClosed_Icc V.isOpen.isClosed_compl
  have hTbdd : BddBelow T := ⟨a, fun t ht => ht.1.1⟩
  have hτT : sInf T ∈ T := hTcl.csInf_mem ⟨t₁, ht₁, ht₁V⟩ hTbdd
  set τ := sInf T with hτ
  have hτb : τ ≤ b := hτT.1.2
  have hbefore : ∀ t ∈ Ico a τ, c t ∈ V := fun t ht => by
    by_contra h
    exact absurd (csInf_le hTbdd ⟨⟨ht.1, ht.2.le.trans hτb⟩, h⟩) (not_le.2 ht.2)
  have haτ : a < τ := by
    rcases hτT.1.1.eq_or_lt with h | h
    · exact absurd (h ▸ hca) hτT.2
    · exact h
  -- `c τ` is a frontier point of `V` in `U`, hence not in `W`
  have hτU : c τ ∈ U := hc.mem τ hτT.1
  have hcw : ∀ t₀ ∈ Ico a τ, ContinuousWithinAt c (Ico t₀ τ) τ := fun t₀ ht₀ =>
    (hcont τ hτT.1).mono fun t ht => ⟨ht₀.1.trans ht.1, ht.2.le.trans hτb⟩
  have hτcl : c τ ∈ closure (V : Set M) :=
    (hcw a ⟨le_rfl, haτ⟩).mem_closure (by rw [closure_Ico haτ.ne]; exact ⟨haτ.le, le_rfl⟩)
      hbefore
  have hτW : c τ ∉ W := hfr (c τ) ⟨⟨hτU, hτcl⟩, hτT.2⟩
  -- over `[a, τ)` the curve is a future-inextensible causal curve of `W`
  have hcurve : C.CausalCurveOn (W ⊔ U) c a τ :=
    CurveOn.mono_opens C.isRelFamily_le
      (CurveOn.restrict hc le_rfl hτb le_rfl fun t ht => hc.mem t ⟨ht.1, ht.2.trans hτb⟩)
      le_sup_right
  have hinex : C.FutureInextensible W (Ico a τ) c :=
    futureInextensible_of_leaving hcurve haτ le_sup_left (fun t ht => hVW (hbefore t ht)) hτW
  -- so it meets `S`, at `t₀`
  obtain ⟨t₀, ht₀, ht₀S⟩ :=
    hinex.exists_mem_of_mem_Jminus hS hC hcaus ⟨a, ⟨le_rfl, haτ⟩, hVJ hca⟩
  -- after `t₀` it is constant: `S` is acausal and `≤_W` antisymmetric
  have hconst : MapsTo c (Ico t₀ τ) {c t₀} := fun t ht => by
    have htI : t ∈ Ico a τ := ⟨ht₀.1.trans ht.1, ht.2⟩
    have hle : C.le W (c t₀) (c t) := hinex.1.le_of_le ht₀ htI ht.1
    obtain ⟨s, hs, hts⟩ := hVJ (hbefore t htI)
    have heq : c t₀ = s :=
      hS.eq_of_le_of_t1_secondCountable hC ht₀S hs (C.le_trans hle hts)
    exact hcaus (by rw [heq]; exact hts) hle
  -- so `c τ = c t₀ ∈ W`
  have hτ₀ : c τ ∈ closure ({c t₀} : Set M) :=
    (hcw t₀ ht₀).mem_closure (by rw [closure_Ico ht₀.2.ne]; exact ⟨ht₀.2.le, le_rfl⟩) hconst
  rw [closure_singleton, mem_singleton_iff] at hτ₀
  exact hτW (hτ₀ ▸ hVW (hbefore t₀ ht₀))

/-- Sbierski's (2.2) shape, `V ⊆ I⁻(S, W)`: a corollary, with no irreflexivity of `≪_W` asked. -/
theorem mapsTo_inside_of_boundaryChart_of_Iminus [T2Space M] [SecondCountableTopology M]
    (hS : C.IsCauchySurfaceOn W S) (hC : C.CausallyArcConnectedOn W)
    (hcaus : ∀ ⦃x y : M⦄, C.le W x y → C.le W y x → x = y) (hVW : V ≤ W)
    (hVI : (V : Set M) ⊆ C.Iminus W S)
    (hfr : ∀ x ∈ ((U : Set M) ∩ closure (V : Set M)) \ V, x ∉ W)
    {c : ℝ → M} {a b : ℝ} (hc : C.CausalCurveOn U c a b) (hca : c a ∈ V) :
    MapsTo c (Icc a b) V := by
  exact mapsTo_inside_of_boundaryChart hS hC hcaus hVW
    (fun _ hx => Iminus_subset_Jminus (hVI hx)) hfr hc hca

/-- The curve form over any interval: a future causal curve of `U` over the interval `I`
(`CausalCurveIn`, any of the four kinds of ends) with a point `c t₀ ∈ V` stays in `V` after `t₀`. -/
theorem mapsTo_inside_of_boundaryChart_of_causalCurveIn [T2Space M]
    [SecondCountableTopology M] (hS : C.IsCauchySurfaceOn W S) (hC : C.CausallyArcConnectedOn W)
    (hcaus : ∀ ⦃x y : M⦄, C.le W x y → C.le W y x → x = y) (hVW : V ≤ W)
    (hVJ : (V : Set M) ⊆ C.Jminus W S)
    (hfr : ∀ x ∈ ((U : Set M) ∩ closure (V : Set M)) \ V, x ∉ W)
    {I : Set ℝ} {c : ℝ → M} {t₀ : ℝ} (hc : C.CausalCurveIn U I c) (ht₀ : t₀ ∈ I)
    (hca : c t₀ ∈ V) : ∀ t ∈ I, t₀ ≤ t → c t ∈ V := fun t ht h =>
  mapsTo_inside_of_boundaryChart hS hC hcaus hVW hVJ hfr (hc.curve t₀ ht₀ t ht) hca ⟨h, le_rfl⟩

/-- **From curves to the chronological relation**: if `U` is causally arc-connected, `V ≤ U`, and
every future causal curve of `U` over `[0, 1]` starting in `V` stays in `V`, then
`I⁺(x, U) ⊆ I⁺(x, V)` for every `x ∈ V`. -/
theorem Iplus_subset_Iplus_of_forall_mapsTo (hU : C.CausallyArcConnectedOn U) (hVU : V ≤ U)
    (hstay : ∀ c : ℝ → M, C.CausalCurveOn U c 0 1 → c 0 ∈ V → MapsTo c (Icc 0 1) V) :
    ∀ x ∈ V, C.Iplus U {x} ⊆ C.Iplus V {x} := by
  rintro x hx y ⟨x', hx', hxy⟩
  rw [mem_singleton_iff] at hx'
  subst hx'
  obtain ⟨c, hc, h0, h1⟩ := (hU U le_rfl x' y).2.1 hxy
  have hmaps := hstay c hc.causalCurveOn (h0 ▸ hx)
  have hcV : C.ChronalCurveOn V c 0 1 := CurveOn.restrict hc le_rfl le_rfl hVU hmaps
  refine ⟨x', rfl, ?_⟩
  have h := hcV.lt_of_lt le_rfl zero_lt_one le_rfl
  rwa [h0, h1] at h

/-- The causal form: `J⁺(x, U) ⊆ J⁺(x, V)` for every `x ∈ V`. -/
theorem Jplus_subset_Jplus_of_forall_mapsTo (hU : C.CausallyArcConnectedOn U) (hVU : V ≤ U)
    (hstay : ∀ c : ℝ → M, C.CausalCurveOn U c 0 1 → c 0 ∈ V → MapsTo c (Icc 0 1) V) :
    ∀ x ∈ V, C.Jplus U {x} ⊆ C.Jplus V {x} := by
  rintro x hx y ⟨x', hx', hxy⟩
  rw [mem_singleton_iff] at hx'
  subst hx'
  obtain ⟨c, hc, h0, h1⟩ := (hU U le_rfl x' y).1.1 hxy
  have hmaps := hstay c hc (h0 ▸ hx)
  have hcV : C.CausalCurveOn V c 0 1 := CurveOn.restrict hc le_rfl le_rfl hVU hmaps
  refine ⟨x', rfl, ?_⟩
  have h := hcV.le_of_le le_rfl zero_le_one le_rfl
  rwa [h0, h1] at h

/-- **T-abs-flrw-type's field (iii)**: the inside of a past boundary chart is future-closed in a
causally arc-connected `U`, `I⁺(x, U) ⊆ I⁺(x, V)` for `x ∈ V`. -/
theorem Iplus_subset_inside_of_boundaryChart [T2Space M] [SecondCountableTopology M]
    (hS : C.IsCauchySurfaceOn W S) (hC : C.CausallyArcConnectedOn W)
    (hcaus : ∀ ⦃x y : M⦄, C.le W x y → C.le W y x → x = y) (hVW : V ≤ W) (hVU : V ≤ U)
    (hVJ : (V : Set M) ⊆ C.Jminus W S)
    (hfr : ∀ x ∈ ((U : Set M) ∩ closure (V : Set M)) \ V, x ∉ W)
    (hU : C.CausallyArcConnectedOn U) : ∀ x ∈ V, C.Iplus U {x} ⊆ C.Iplus V {x} := by
  exact Iplus_subset_Iplus_of_forall_mapsTo hU hVU fun _ hc h0 =>
    mapsTo_inside_of_boundaryChart hS hC hcaus hVW hVJ hfr hc h0

/-- The causal form of field (iii): `J⁺(x, U) ⊆ J⁺(x, V)` for `x ∈ V`. -/
theorem Jplus_subset_inside_of_boundaryChart [T2Space M] [SecondCountableTopology M]
    (hS : C.IsCauchySurfaceOn W S) (hC : C.CausallyArcConnectedOn W)
    (hcaus : ∀ ⦃x y : M⦄, C.le W x y → C.le W y x → x = y) (hVW : V ≤ W) (hVU : V ≤ U)
    (hVJ : (V : Set M) ⊆ C.Jminus W S)
    (hfr : ∀ x ∈ ((U : Set M) ∩ closure (V : Set M)) \ V, x ∉ W)
    (hU : C.CausallyArcConnectedOn U) : ∀ x ∈ V, C.Jplus U {x} ⊆ C.Jplus V {x} := by
  exact Jplus_subset_Jplus_of_forall_mapsTo hU hVU fun _ hc h0 =>
    mapsTo_inside_of_boundaryChart hS hC hcaus hVW hVJ hfr hc h0

/-- **Sbierski 2312.07443 (2.4) as printed, the future boundary chart**: `V ⊆ J⁺(S, W)`, and every
past-directed causal curve of `U` (a future causal curve of `C.dual`) starting in `V` stays in
`V`. -/
theorem mapsTo_inside_of_futureBoundaryChart [T2Space M] [SecondCountableTopology M]
    (hS : C.IsCauchySurfaceOn W S) (hC : C.CausallyArcConnectedOn W)
    (hcaus : ∀ ⦃x y : M⦄, C.le W x y → C.le W y x → x = y) (hVW : V ≤ W)
    (hVJ : (V : Set M) ⊆ C.Jplus W S)
    (hfr : ∀ x ∈ ((U : Set M) ∩ closure (V : Set M)) \ V, x ∉ W)
    {c : ℝ → M} {a b : ℝ} (hc : C.dual.CausalCurveOn U c a b) (hca : c a ∈ V) :
    MapsTo c (Icc a b) V := by
  exact mapsTo_inside_of_boundaryChart (C := C.dual) (dual_isCauchySurfaceOn.2 hS)
    (dual_causallyArcConnectedOn.2 hC) (fun _ _ h₁ h₂ => hcaus h₂ h₁) hVW hVJ hfr hc hca

/-- (2.4) as printed, with (2.2) as printed: `V ⊆ I⁺(S, W)`. -/
theorem mapsTo_inside_of_futureBoundaryChart_of_Iplus [T2Space M] [SecondCountableTopology M]
    (hS : C.IsCauchySurfaceOn W S) (hC : C.CausallyArcConnectedOn W)
    (hcaus : ∀ ⦃x y : M⦄, C.le W x y → C.le W y x → x = y) (hVW : V ≤ W)
    (hVI : (V : Set M) ⊆ C.Iplus W S)
    (hfr : ∀ x ∈ ((U : Set M) ∩ closure (V : Set M)) \ V, x ∉ W)
    {c : ℝ → M} {a b : ℝ} (hc : C.dual.CausalCurveOn U c a b) (hca : c a ∈ V) :
    MapsTo c (Icc a b) V := by
  exact mapsTo_inside_of_futureBoundaryChart hS hC hcaus hVW
    (fun _ hx => Iplus_subset_Jplus (hVI hx)) hfr hc hca

/-- (2.4) for future-directed parameters: a future causal curve of `U` ending in `V` lies in
`V`. -/
theorem mapsTo_inside_of_futureBoundaryChart_of_end_mem [T2Space M]
    [SecondCountableTopology M] (hS : C.IsCauchySurfaceOn W S) (hC : C.CausallyArcConnectedOn W)
    (hcaus : ∀ ⦃x y : M⦄, C.le W x y → C.le W y x → x = y) (hVW : V ≤ W)
    (hVJ : (V : Set M) ⊆ C.Jplus W S)
    (hfr : ∀ x ∈ ((U : Set M) ∩ closure (V : Set M)) \ V, x ∉ W)
    {c : ℝ → M} {a b : ℝ} (hc : C.CausalCurveOn U c a b) (hcb : c b ∈ V) :
    MapsTo c (Icc a b) V := by
  have hrev : C.dual.CausalCurveOn U (fun t => c (a + b - t)) a b := CurveOn.reverse hc
  have hmaps := mapsTo_inside_of_futureBoundaryChart hS hC hcaus hVW hVJ hfr hrev
    (by simpa using hcb)
  intro t ht
  have h := @hmaps (a + b - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
  simpa using h

/-- The relation form of the future boundary chart: `I⁻(x, U) ⊆ I⁻(x, V)` for `x ∈ V`. -/
theorem Iminus_subset_inside_of_futureBoundaryChart [T2Space M] [SecondCountableTopology M]
    (hS : C.IsCauchySurfaceOn W S) (hC : C.CausallyArcConnectedOn W)
    (hcaus : ∀ ⦃x y : M⦄, C.le W x y → C.le W y x → x = y) (hVW : V ≤ W) (hVU : V ≤ U)
    (hVJ : (V : Set M) ⊆ C.Jplus W S)
    (hfr : ∀ x ∈ ((U : Set M) ∩ closure (V : Set M)) \ V, x ∉ W)
    (hU : C.CausallyArcConnectedOn U) : ∀ x ∈ V, C.Iminus U {x} ⊆ C.Iminus V {x} := by
  exact Iplus_subset_Iplus_of_forall_mapsTo (C := C.dual) (dual_causallyArcConnectedOn.2 hU) hVU
    fun _ hc h0 => mapsTo_inside_of_futureBoundaryChart hS hC hcaus hVW hVJ hfr hc h0

/-- The causal relation form of the future boundary chart: `J⁻(x, U) ⊆ J⁻(x, V)` for `x ∈ V`. -/
theorem Jminus_subset_inside_of_futureBoundaryChart [T2Space M] [SecondCountableTopology M]
    (hS : C.IsCauchySurfaceOn W S) (hC : C.CausallyArcConnectedOn W)
    (hcaus : ∀ ⦃x y : M⦄, C.le W x y → C.le W y x → x = y) (hVW : V ≤ W) (hVU : V ≤ U)
    (hVJ : (V : Set M) ⊆ C.Jplus W S)
    (hfr : ∀ x ∈ ((U : Set M) ∩ closure (V : Set M)) \ V, x ∉ W)
    (hU : C.CausallyArcConnectedOn U) : ∀ x ∈ V, C.Jminus U {x} ⊆ C.Jminus V {x} := by
  exact Jplus_subset_Jplus_of_forall_mapsTo (C := C.dual) (dual_causallyArcConnectedOn.2 hU) hVU
    fun _ hc h0 => mapsTo_inside_of_futureBoundaryChart hS hC hcaus hVW hVJ hfr hc h0

end Causality

open Causality

/-- On the timelike line, `{1}` is a Cauchy surface of `]0, ∞[`, the range of `exp`. -/
theorem timelikeLine_isCauchySurfaceOn_Ioi_zero_one :
    timelikeLine.IsCauchySurfaceOn (⟨Ioi 0, isOpen_Ioi⟩ : Opens ℝ) {1} := by
  have h := timelikeLine_isCauchySurfaceOn_range Real.exp_strictMono Real.continuous_exp
    Real.isOpenEmbedding_exp.isOpenMap (U := (⟨Ioi 0, isOpen_Ioi⟩ : Opens ℝ))
    Real.range_exp.symm
  rwa [Real.exp_zero] at h

/-- **The witness** (kb/0011): on the timelike line, `W = ]0, ∞[`, `S = {1}`, `U = ]-1, 1[`,
`V = ]0, 1[` satisfy every hypothesis jointly; the frontier of `V` in `U` is `{0}`, the past
boundary point of `W`. The theorem applied: every future causal curve of `U` starting in `V` stays
in `V`, and `I⁺(x, U) ⊆ I⁺(x, V)`, `J⁺(x, U) ⊆ J⁺(x, V)` for `x ∈ V`. The past direction fails:
`-1/2 ∈ I⁻(1/2, U) ∖ I⁻(1/2, V)`. -/
theorem timelikeLine_boundaryChart_witness :
    (timelikeLine.IsCauchySurfaceOn (⟨Ioi 0, isOpen_Ioi⟩ : Opens ℝ) {1} ∧
      timelikeLine.CausallyArcConnectedOn (⟨Ioi 0, isOpen_Ioi⟩ : Opens ℝ) ∧
      (∀ ⦃x y : ℝ⦄, timelikeLine.le (⟨Ioi 0, isOpen_Ioi⟩ : Opens ℝ) x y →
        timelikeLine.le (⟨Ioi 0, isOpen_Ioi⟩ : Opens ℝ) y x → x = y) ∧
      (⟨Ioo 0 1, isOpen_Ioo⟩ : Opens ℝ) ≤ (⟨Ioi 0, isOpen_Ioi⟩ : Opens ℝ) ∧
      (⟨Ioo 0 1, isOpen_Ioo⟩ : Opens ℝ) ≤ (⟨Ioo (-1) 1, isOpen_Ioo⟩ : Opens ℝ) ∧
      Ioo (0 : ℝ) 1 ⊆ timelikeLine.Jminus (⟨Ioi 0, isOpen_Ioi⟩ : Opens ℝ) {1} ∧
      (Ioo (-1 : ℝ) 1 ∩ closure (Ioo 0 1)) \ Ioo 0 1 = {0} ∧ (0 : ℝ) ∉ Ioi 0 ∧
      timelikeLine.CausallyArcConnectedOn (⟨Ioo (-1) 1, isOpen_Ioo⟩ : Opens ℝ)) ∧
    (∀ (c : ℝ → ℝ) (a b : ℝ),
      timelikeLine.CausalCurveOn (⟨Ioo (-1) 1, isOpen_Ioo⟩ : Opens ℝ) c a b →
        c a ∈ Ioo (0 : ℝ) 1 → MapsTo c (Icc a b) (Ioo 0 1)) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, timelikeLine.Iplus (⟨Ioo (-1) 1, isOpen_Ioo⟩ : Opens ℝ) {x} ⊆
      timelikeLine.Iplus (⟨Ioo 0 1, isOpen_Ioo⟩ : Opens ℝ) {x}) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, timelikeLine.Jplus (⟨Ioo (-1) 1, isOpen_Ioo⟩ : Opens ℝ) {x} ⊆
      timelikeLine.Jplus (⟨Ioo 0 1, isOpen_Ioo⟩ : Opens ℝ) {x}) ∧
    ¬ timelikeLine.Iminus (⟨Ioo (-1) 1, isOpen_Ioo⟩ : Opens ℝ) {1 / 2} ⊆
      timelikeLine.Iminus (⟨Ioo 0 1, isOpen_Ioo⟩ : Opens ℝ) {1 / 2} := by
  have hS := timelikeLine_isCauchySurfaceOn_Ioi_zero_one
  have hCW : timelikeLine.CausallyArcConnectedOn (⟨Ioi 0, isOpen_Ioi⟩ : Opens ℝ) :=
    CausallyArcConnectedOn.mono timelikeLine_causallyArcConnected le_top
  have hCU : timelikeLine.CausallyArcConnectedOn (⟨Ioo (-1) 1, isOpen_Ioo⟩ : Opens ℝ) :=
    CausallyArcConnectedOn.mono timelikeLine_causallyArcConnected le_top
  have hcaus : ∀ ⦃x y : ℝ⦄, timelikeLine.le (⟨Ioi 0, isOpen_Ioi⟩ : Opens ℝ) x y →
      timelikeLine.le (⟨Ioi 0, isOpen_Ioi⟩ : Opens ℝ) y x → x = y := fun _ _ h₁ h₂ =>
    le_antisymm (timelikeLine_le.1 h₁).1 (timelikeLine_le.1 h₂).1
  have hVW : (⟨Ioo 0 1, isOpen_Ioo⟩ : Opens ℝ) ≤ (⟨Ioi 0, isOpen_Ioi⟩ : Opens ℝ) :=
    fun x hx => show x ∈ Ioi (0 : ℝ) from (show x ∈ Ioo (0 : ℝ) 1 from hx).1
  have hVU : (⟨Ioo 0 1, isOpen_Ioo⟩ : Opens ℝ) ≤ (⟨Ioo (-1) 1, isOpen_Ioo⟩ : Opens ℝ) :=
    fun x hx => by
      have hx' : x ∈ Ioo (0 : ℝ) 1 := hx
      exact show x ∈ Ioo (-1 : ℝ) 1 from ⟨by linarith [hx'.1], hx'.2⟩
  have hVJ : Ioo (0 : ℝ) 1 ⊆ timelikeLine.Jminus (⟨Ioi 0, isOpen_Ioi⟩ : Opens ℝ) {1} :=
    fun x hx => ⟨1, mem_singleton _, timelikeLine_le.2 ⟨hx.2.le, fun z hz =>
      show z ∈ Ioi (0 : ℝ) from lt_of_lt_of_le hx.1 hz.1⟩⟩
  have hfrEq : (Ioo (-1 : ℝ) 1 ∩ closure (Ioo 0 1)) \ Ioo 0 1 = {0} := by
    rw [closure_Ioo zero_ne_one]
    ext x
    simp only [Set.mem_sdiff, mem_inter_iff, mem_Ioo, mem_Icc, mem_singleton_iff]
    constructor
    · rintro ⟨⟨⟨-, h2⟩, h3, -⟩, h5⟩
      by_contra hx0
      exact h5 ⟨lt_of_le_of_ne h3 (Ne.symm hx0), h2⟩
    · rintro rfl
      norm_num
  have h0 : (0 : ℝ) ∉ Ioi 0 := fun h => lt_irrefl (0 : ℝ) (mem_Ioi.1 h)
  have hfr : ∀ x ∈ (((⟨Ioo (-1) 1, isOpen_Ioo⟩ : Opens ℝ) : Set ℝ) ∩
      closure ((⟨Ioo 0 1, isOpen_Ioo⟩ : Opens ℝ) : Set ℝ)) \ (⟨Ioo 0 1, isOpen_Ioo⟩ : Opens ℝ),
      x ∉ (⟨Ioi 0, isOpen_Ioi⟩ : Opens ℝ) := fun x hx => by
    have hx' : x ∈ (Ioo (-1 : ℝ) 1 ∩ closure (Ioo 0 1)) \ Ioo 0 1 := hx
    rw [hfrEq, mem_singleton_iff] at hx'
    subst hx'
    exact h0
  refine ⟨⟨hS, hCW, hcaus, hVW, hVU, hVJ, hfrEq, h0, hCU⟩,
    fun c a b hc hca => mapsTo_inside_of_boundaryChart hS hCW hcaus hVW hVJ hfr hc hca,
    Iplus_subset_inside_of_boundaryChart hS hCW hcaus hVW hVU hVJ hfr hCU,
    Jplus_subset_inside_of_boundaryChart hS hCW hcaus hVW hVU hVJ hfr hCU, fun h => ?_⟩
  have hmem : (-1 / 2 : ℝ) ∈ timelikeLine.Iminus (⟨Ioo (-1) 1, isOpen_Ioo⟩ : Opens ℝ) {1 / 2} :=
    ⟨1 / 2, mem_singleton _, timelikeLine_lt.2 ⟨by norm_num, fun z hz =>
      show z ∈ Ioo (-1 : ℝ) 1 from ⟨by linarith [hz.1], by linarith [hz.2]⟩⟩⟩
  obtain ⟨y, hy, hlt⟩ := h hmem
  rw [mem_singleton_iff] at hy
  subst hy
  have h' : (-1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 :=
    (timelikeLine_lt.1 hlt).2 ⟨le_rfl, by norm_num⟩
  norm_num at h'

/-- On the timelike line, `{-1}` is a Cauchy surface of `]-∞, 0[`, the range of `x ↦ -exp (-x)`. -/
theorem timelikeLine_isCauchySurfaceOn_Iio_zero_neg_one :
    timelikeLine.IsCauchySurfaceOn (⟨Iio 0, isOpen_Iio⟩ : Opens ℝ) {-1} := by
  have hgm : StrictMono (fun x : ℝ => -Real.exp (-x)) := fun _ _ h =>
    neg_lt_neg (Real.exp_lt_exp.2 (neg_lt_neg h))
  have hgc : Continuous (fun x : ℝ => -Real.exp (-x)) :=
    (Real.continuous_exp.comp continuous_neg).neg
  have hgo : IsOpenMap (fun x : ℝ => -Real.exp (-x)) :=
    (isOpenMap_neg ℝ).comp (Real.isOpenEmbedding_exp.isOpenMap.comp (isOpenMap_neg ℝ))
  have hr : ((⟨Iio 0, isOpen_Iio⟩ : Opens ℝ) : Set ℝ) = range (fun x : ℝ => -Real.exp (-x)) := by
    ext y
    refine ⟨fun hy => ⟨-Real.log (-y), ?_⟩, ?_⟩
    · have hy' : 0 < -y := neg_pos.2 hy
      simp only [neg_neg, Real.exp_log hy']
    · rintro ⟨x, rfl⟩
      exact show -Real.exp (-x) < 0 from neg_neg_of_pos (Real.exp_pos _)
  have h := timelikeLine_isCauchySurfaceOn_range hgm hgc hgo hr
  simpa using h

/-- **The time-reversed witness**, (2.4) as printed: on the timelike line, `W = ]-∞, 0[`,
`S = {-1}`, `U = ]-1, 1[`, `V = ]-1, 0[ ⊆ J⁺(S, W)`; the frontier of `V` in `U` is `{0}`, the
future boundary point of `W`. Every past-directed causal curve of `U` starting in `V` stays in `V`,
and `I⁻(x, U) ⊆ I⁻(x, V)`, `J⁻(x, U) ⊆ J⁻(x, V)` for `x ∈ V`. -/
theorem timelikeLine_futureBoundaryChart_witness :
    (timelikeLine.IsCauchySurfaceOn (⟨Iio 0, isOpen_Iio⟩ : Opens ℝ) {-1} ∧
      timelikeLine.CausallyArcConnectedOn (⟨Iio 0, isOpen_Iio⟩ : Opens ℝ) ∧
      (∀ ⦃x y : ℝ⦄, timelikeLine.le (⟨Iio 0, isOpen_Iio⟩ : Opens ℝ) x y →
        timelikeLine.le (⟨Iio 0, isOpen_Iio⟩ : Opens ℝ) y x → x = y) ∧
      (⟨Ioo (-1) 0, isOpen_Ioo⟩ : Opens ℝ) ≤ (⟨Iio 0, isOpen_Iio⟩ : Opens ℝ) ∧
      (⟨Ioo (-1) 0, isOpen_Ioo⟩ : Opens ℝ) ≤ (⟨Ioo (-1) 1, isOpen_Ioo⟩ : Opens ℝ) ∧
      Ioo (-1 : ℝ) 0 ⊆ timelikeLine.Jplus (⟨Iio 0, isOpen_Iio⟩ : Opens ℝ) {-1} ∧
      (Ioo (-1 : ℝ) 1 ∩ closure (Ioo (-1) 0)) \ Ioo (-1) 0 = {0} ∧ (0 : ℝ) ∉ Iio 0 ∧
      timelikeLine.CausallyArcConnectedOn (⟨Ioo (-1) 1, isOpen_Ioo⟩ : Opens ℝ)) ∧
    (∀ (c : ℝ → ℝ) (a b : ℝ),
      timelikeLine.dual.CausalCurveOn (⟨Ioo (-1) 1, isOpen_Ioo⟩ : Opens ℝ) c a b →
        c a ∈ Ioo (-1 : ℝ) 0 → MapsTo c (Icc a b) (Ioo (-1) 0)) ∧
    (∀ x ∈ Ioo (-1 : ℝ) 0, timelikeLine.Iminus (⟨Ioo (-1) 1, isOpen_Ioo⟩ : Opens ℝ) {x} ⊆
      timelikeLine.Iminus (⟨Ioo (-1) 0, isOpen_Ioo⟩ : Opens ℝ) {x}) ∧
    (∀ x ∈ Ioo (-1 : ℝ) 0, timelikeLine.Jminus (⟨Ioo (-1) 1, isOpen_Ioo⟩ : Opens ℝ) {x} ⊆
      timelikeLine.Jminus (⟨Ioo (-1) 0, isOpen_Ioo⟩ : Opens ℝ) {x}) := by
  have hS := timelikeLine_isCauchySurfaceOn_Iio_zero_neg_one
  have hCW : timelikeLine.CausallyArcConnectedOn (⟨Iio 0, isOpen_Iio⟩ : Opens ℝ) :=
    CausallyArcConnectedOn.mono timelikeLine_causallyArcConnected le_top
  have hCU : timelikeLine.CausallyArcConnectedOn (⟨Ioo (-1) 1, isOpen_Ioo⟩ : Opens ℝ) :=
    CausallyArcConnectedOn.mono timelikeLine_causallyArcConnected le_top
  have hcaus : ∀ ⦃x y : ℝ⦄, timelikeLine.le (⟨Iio 0, isOpen_Iio⟩ : Opens ℝ) x y →
      timelikeLine.le (⟨Iio 0, isOpen_Iio⟩ : Opens ℝ) y x → x = y := fun _ _ h₁ h₂ =>
    le_antisymm (timelikeLine_le.1 h₁).1 (timelikeLine_le.1 h₂).1
  have hVW : (⟨Ioo (-1) 0, isOpen_Ioo⟩ : Opens ℝ) ≤ (⟨Iio 0, isOpen_Iio⟩ : Opens ℝ) :=
    fun x hx => show x ∈ Iio (0 : ℝ) from (show x ∈ Ioo (-1 : ℝ) 0 from hx).2
  have hVU : (⟨Ioo (-1) 0, isOpen_Ioo⟩ : Opens ℝ) ≤ (⟨Ioo (-1) 1, isOpen_Ioo⟩ : Opens ℝ) :=
    fun x hx => by
      have hx' : x ∈ Ioo (-1 : ℝ) 0 := hx
      exact show x ∈ Ioo (-1 : ℝ) 1 from ⟨hx'.1, by linarith [hx'.2]⟩
  have hVJ : Ioo (-1 : ℝ) 0 ⊆ timelikeLine.Jplus (⟨Iio 0, isOpen_Iio⟩ : Opens ℝ) {-1} :=
    fun x hx => ⟨-1, mem_singleton _, timelikeLine_le.2 ⟨hx.1.le, fun z hz =>
      show z ∈ Iio (0 : ℝ) from lt_of_le_of_lt hz.2 hx.2⟩⟩
  have hfrEq : (Ioo (-1 : ℝ) 1 ∩ closure (Ioo (-1) 0)) \ Ioo (-1) 0 = {0} := by
    rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 0)]
    ext x
    simp only [Set.mem_sdiff, mem_inter_iff, mem_Ioo, mem_Icc, mem_singleton_iff]
    constructor
    · rintro ⟨⟨⟨h1, -⟩, -, h4⟩, h5⟩
      by_contra hx0
      exact h5 ⟨h1, lt_of_le_of_ne h4 hx0⟩
    · rintro rfl
      norm_num
  have h0 : (0 : ℝ) ∉ Iio 0 := fun h => lt_irrefl (0 : ℝ) (mem_Iio.1 h)
  have hfr : ∀ x ∈ (((⟨Ioo (-1) 1, isOpen_Ioo⟩ : Opens ℝ) : Set ℝ) ∩
      closure ((⟨Ioo (-1) 0, isOpen_Ioo⟩ : Opens ℝ) : Set ℝ)) \
        (⟨Ioo (-1) 0, isOpen_Ioo⟩ : Opens ℝ), x ∉ (⟨Iio 0, isOpen_Iio⟩ : Opens ℝ) := fun x hx => by
    have hx' : x ∈ (Ioo (-1 : ℝ) 1 ∩ closure (Ioo (-1) 0)) \ Ioo (-1) 0 := hx
    rw [hfrEq, mem_singleton_iff] at hx'
    subst hx'
    exact h0
  exact ⟨⟨hS, hCW, hcaus, hVW, hVU, hVJ, hfrEq, h0, hCU⟩,
    fun c a b hc hca => mapsTo_inside_of_futureBoundaryChart hS hCW hcaus hVW hVJ hfr hc hca,
    Iminus_subset_inside_of_futureBoundaryChart hS hCW hcaus hVW hVU hVJ hfr hCU,
    Jminus_subset_inside_of_futureBoundaryChart hS hCW hcaus hVW hVU hVJ hfr hCU⟩

/-- **The frontier hypothesis cannot be dropped**: with `U = ]-1, 2[` and the rest as in the
witness, `V ⊆ J⁻(S, W)` holds but the frontier point `1` of `V` in `U` lies in `W`, and `id` over
`[1/2, 3/2]`, a future causal curve of `U` starting in `V`, leaves `V`. -/
theorem timelikeLine_boundaryChart_needs_frontier :
    (timelikeLine.IsCauchySurfaceOn (⟨Ioi 0, isOpen_Ioi⟩ : Opens ℝ) {1} ∧
      timelikeLine.CausallyArcConnectedOn (⟨Ioi 0, isOpen_Ioi⟩ : Opens ℝ) ∧
      (∀ ⦃x y : ℝ⦄, timelikeLine.le (⟨Ioi 0, isOpen_Ioi⟩ : Opens ℝ) x y →
        timelikeLine.le (⟨Ioi 0, isOpen_Ioi⟩ : Opens ℝ) y x → x = y) ∧
      (⟨Ioo 0 1, isOpen_Ioo⟩ : Opens ℝ) ≤ (⟨Ioi 0, isOpen_Ioi⟩ : Opens ℝ) ∧
      Ioo (0 : ℝ) 1 ⊆ timelikeLine.Jminus (⟨Ioi 0, isOpen_Ioi⟩ : Opens ℝ) {1} ∧
      (1 : ℝ) ∈ (Ioo (-1 : ℝ) 2 ∩ closure (Ioo 0 1)) \ Ioo 0 1 ∧ (1 : ℝ) ∈ Ioi 0) ∧
    timelikeLine.CausalCurveOn (⟨Ioo (-1) 2, isOpen_Ioo⟩ : Opens ℝ) id (1 / 2) (3 / 2) ∧
    id (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 ∧ ¬ MapsTo id (Icc (1 / 2 : ℝ) (3 / 2)) (Ioo 0 1) := by
  have hS := timelikeLine_isCauchySurfaceOn_Ioi_zero_one
  have hCW : timelikeLine.CausallyArcConnectedOn (⟨Ioi 0, isOpen_Ioi⟩ : Opens ℝ) :=
    CausallyArcConnectedOn.mono timelikeLine_causallyArcConnected le_top
  have hcaus : ∀ ⦃x y : ℝ⦄, timelikeLine.le (⟨Ioi 0, isOpen_Ioi⟩ : Opens ℝ) x y →
      timelikeLine.le (⟨Ioi 0, isOpen_Ioi⟩ : Opens ℝ) y x → x = y := fun _ _ h₁ h₂ =>
    le_antisymm (timelikeLine_le.1 h₁).1 (timelikeLine_le.1 h₂).1
  have hVW : (⟨Ioo 0 1, isOpen_Ioo⟩ : Opens ℝ) ≤ (⟨Ioi 0, isOpen_Ioi⟩ : Opens ℝ) :=
    fun x hx => show x ∈ Ioi (0 : ℝ) from (show x ∈ Ioo (0 : ℝ) 1 from hx).1
  have hVJ : Ioo (0 : ℝ) 1 ⊆ timelikeLine.Jminus (⟨Ioi 0, isOpen_Ioi⟩ : Opens ℝ) {1} :=
    fun x hx => ⟨1, mem_singleton _, timelikeLine_le.2 ⟨hx.2.le, fun z hz =>
      show z ∈ Ioi (0 : ℝ) from lt_of_lt_of_le hx.1 hz.1⟩⟩
  have h1 : (1 : ℝ) ∈ (Ioo (-1 : ℝ) 2 ∩ closure (Ioo 0 1)) \ Ioo 0 1 := by
    rw [closure_Ioo zero_ne_one]
    exact ⟨⟨⟨by norm_num, by norm_num⟩, ⟨zero_le_one, le_rfl⟩⟩, fun h => lt_irrefl _ h.2⟩
  refine ⟨⟨hS, hCW, hcaus, hVW, hVJ, h1, mem_Ioi.2 one_pos⟩, ?_, by norm_num, fun h => ?_⟩
  · exact CurveOn.restrict (timelikeLine_causalCurveOn_id (1 / 2) (3 / 2)) le_rfl le_rfl le_top
      fun t ht => show t ∈ Ioo (-1 : ℝ) 2 from ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · have h' := @h 1 ⟨by norm_num, by norm_num⟩
    simp at h'

/-- **`V ⊆ J⁻(S, W)` cannot be dropped**: on the timelike line, `W = V = ]-1, 1[`, `S = {0}`,
`U = ]-2, 2[`; the frontier `{-1, 1}` of `V` in `U` misses `W`, but `1/2 ∈ V ∖ J⁻(S, W)`, and
`id` over `[1/2, 3/2]`, a future causal curve of `U` starting in `V`, leaves `V`. -/
theorem timelikeLine_boundaryChart_needs_Jminus :
    (timelikeLine.IsCauchySurfaceOn (⟨Ioo (-1) 1, isOpen_Ioo⟩ : Opens ℝ) {0} ∧
      timelikeLine.CausallyArcConnectedOn (⟨Ioo (-1) 1, isOpen_Ioo⟩ : Opens ℝ) ∧
      (∀ ⦃x y : ℝ⦄, timelikeLine.le (⟨Ioo (-1) 1, isOpen_Ioo⟩ : Opens ℝ) x y →
        timelikeLine.le (⟨Ioo (-1) 1, isOpen_Ioo⟩ : Opens ℝ) y x → x = y) ∧
      (∀ x ∈ (Ioo (-2 : ℝ) 2 ∩ closure (Ioo (-1) 1)) \ Ioo (-1) 1, x ∉ Ioo (-1 : ℝ) 1) ∧
      (1 / 2 : ℝ) ∉ timelikeLine.Jminus (⟨Ioo (-1) 1, isOpen_Ioo⟩ : Opens ℝ) {0}) ∧
    timelikeLine.CausalCurveOn (⟨Ioo (-2) 2, isOpen_Ioo⟩ : Opens ℝ) id (1 / 2) (3 / 2) ∧
    id (1 / 2 : ℝ) ∈ Ioo (-1 : ℝ) 1 ∧ ¬ MapsTo id (Icc (1 / 2 : ℝ) (3 / 2)) (Ioo (-1) 1) := by
  have hS : timelikeLine.IsCauchySurfaceOn (⟨Ioo (-1) 1, isOpen_Ioo⟩ : Opens ℝ) {0} :=
    timelikeLine_isCauchySurfaceOn_Ioo one_pos rfl
  have hCW : timelikeLine.CausallyArcConnectedOn (⟨Ioo (-1) 1, isOpen_Ioo⟩ : Opens ℝ) :=
    CausallyArcConnectedOn.mono timelikeLine_causallyArcConnected le_top
  have hcaus : ∀ ⦃x y : ℝ⦄, timelikeLine.le (⟨Ioo (-1) 1, isOpen_Ioo⟩ : Opens ℝ) x y →
      timelikeLine.le (⟨Ioo (-1) 1, isOpen_Ioo⟩ : Opens ℝ) y x → x = y := fun _ _ h₁ h₂ =>
    le_antisymm (timelikeLine_le.1 h₁).1 (timelikeLine_le.1 h₂).1
  have hJ : (1 / 2 : ℝ) ∉ timelikeLine.Jminus (⟨Ioo (-1) 1, isOpen_Ioo⟩ : Opens ℝ) {0} := by
    rintro ⟨y, hy, hle⟩
    rw [mem_singleton_iff] at hy
    subst hy
    have h' := (timelikeLine_le.1 hle).1
    norm_num at h'
  refine ⟨⟨hS, hCW, hcaus, fun x hx => hx.2, hJ⟩, ?_, by norm_num, fun h => ?_⟩
  · exact CurveOn.restrict (timelikeLine_causalCurveOn_id (1 / 2) (3 / 2)) le_rfl le_rfl le_top
      fun t ht => show t ∈ Ioo (-2 : ℝ) 2 from ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · have h' := @h 1 ⟨by norm_num, by norm_num⟩
    simp at h'

end Causal
