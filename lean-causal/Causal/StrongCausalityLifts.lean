import Causal.StrongCausality
import Causal.Morphism
import Causal.LinesCurves
import Causal.RationalLineExtras
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.NumberTheory.Real.Irrational

/-!
# Strong causality lifts along causal maps to strongly causal spacetimes

No label of `ETT.tex` is certified here, and none is marked. ETT programme, layer 1, target
`T-abs-strong-causality-lifts` (`programme/roadmap.toml:1944`), proposed by the author in the
session of 2026-11-24. The target, as recorded (`programme/roadmap.toml:1945`, `:1953`):

> Strong causality lifts along a causal map to a strongly causal space: if p : M̃ → M and
> D : M̃ → X send causal curves to causal curves, M and X are strongly causal, and every point
> x̃ has a neighbourhood basis of sets C(W) ∩ D⁻¹(V) (C(W) the component of p⁻¹(W) containing x̃
> in the coarser topology, W ∋ p x̃, V ∋ D x̃ open), then M̃ is strongly causal; with tarentin,
> its topology is its Alexandrov topology

> Proof (author's session 2026-11-24): take W causally convex in M and V causally convex in X.
> A causal curve with ends in C(W) ∩ D⁻¹(V) projects to a causal curve of M with ends in W, so
> it stays in W; being connected, it stays in C(W). Its development is a causal curve of X with
> ends in V, so it stays in V. These sets are causally convex and form a basis, so M̃ is
> strongly causal.

`M̃` is `N` here. Its topology is the instance; the coarser one is an explicit
`τc : TopologicalSpace N` with `‹TopologicalSpace N› ≤ τc` (mathlib's order: finer is smaller).
`C(W)` is `@connectedComponentIn N τc (p ⁻¹' W) x`, and the basis is `(𝓝 x).HasBasis` indexed
by ALL the pairs `(W, V)` of open sets with `p x ∈ W`, `D x ∈ V` (the weaker reading, "some
sets of this form make a basis", is not treated; the refutation below is unaffected).

## What is proved

* `Causality.stronglyCausal_lift`: the target's form, with `N` **causally arc-connected added**
  (the finding below). `alexandrovTopology_eq_lift` adds tarentin and concludes
  `C.alexandrovTopology = ‹TopologicalSpace N›` through `StronglyCausal.alexandrovTopology_eq`.
  `stronglyCausalOpen_lift` is the open form: `M`, `X` strongly causal with open neighbourhoods
  give the same for `N`, with nothing added beyond the same causal arc-connectedness, because the
basis sets with `W`, `V` open are open
  (`isOpen_connectedComponentIn_inter_preimage`). `stronglyCausal_lift_of_weakMorphism` is the
  form for the library's weak morphisms, `stronglyCausal_lift_self` the form with the components
  in the topology of `N`.
* `Causality.stronglyCausal_of_lift`, `stronglyCausalOpen_of_lift`: the general form, of which
  the target's is a corollary. Its hypotheses are: `p`, `D` non-decreasing at `M`
  (`≤_N ⇒ ≤_M`, `≤_X`); and `hdiam`, which says every diamond `J_N(a, z)` has a
  `τc`-preconnected subset through `a` and `z`. Neither `τ ≤ τc` nor any curve is asked. Its
  core is `causallyConvexIn_connectedComponentIn_inter_preimage`, the convexity step of the
  author's proof, read on diamonds. The bridges are:
  - `mem_connectedComponentIn_diamond_of_curves`: if `≤_N` is realised by causal curves at `M`,
    `τ ≤ τc` gives `hdiam`;
  - `le_top_map_of_curves`: maps that send causal curves to causal curves are then monotone;
  - `WeakMorphism.causalCurveOn_comp`: weak morphisms send causal curves to causal curves;
  - `WeakMorphism.le_top_of_absolutelyMinimal` and `stronglyCausal_of_lift_of_weakMorphism`: on
    an absolutely minimal `N`, weak morphisms are monotone, and `hdiam` is the one hypothesis
    left.

## Finding: the printed form is false

"Send causal curves to causal curves" constrains `≤_N` only where `≤_N` is realised by causal
curves, and the proof's first step assumes that it is. `not_stronglyCausal_lift_of_curves`
refutes the printed form in either reading of the gluing of `defi:causalite` (DEC-167). The
witness is `symmRationalLine`: on `ℝ`, two rationals are related, both ways, when the segment
between them lies in the open set. It is absolutely minimal on every open set. Its causal curves
are constant, so `id` into the timelike line sends every causal curve to one. The basis holds
with the components taken in `ℝ`. Yet `J(0, 0) ⊇ ℚ`, so it is not strongly causal, and it is not
causally arc-connected (`symmRationalLine_separates_lift`). The witness is not causal and not
tarentin.

Without gluing, the same is true with weak morphisms and tarentin, for both conclusions:
`not_alexandrovTopology_eq_lift_of_weakMorphism`, on `timelikeLineTop` (kb/0014: not causal,
not absolutely minimal, `timelikeLineTop_separates_lift`).

## Hypothesis checklist

| target hypothesis | here |
|---|---|
| `p`, `D` send causal curves to causal curves | ✓ carried, weakest form: a causal curve of `N` over `[0, 1]` goes to a causal curve of `M` (of `X`) over `[0, 1]`. Every reading implies it, weak morphisms included (`WeakMorphism.causalCurveOn_comp`). ⚠ weakened in the general form to monotonicity at `M` |
| `M`, `X` strongly causal | ✓ carried: `StronglyCausal` (DEC-7); the open form takes `StronglyCausalOpen` |
| the basis `C(W) ∩ D⁻¹(V)`, `W ∋ p x̃`, `V ∋ D x̃` open | ✓ carried: `HasBasis` |
| `C(W)` taken in the coarser topology | ✓ carried: any `τc` with `τ ≤ τc`, `τc = τ` allowed. The general form takes any `τc` with `hdiam` |
| — | ⚠ strengthened: `N` causally arc-connected (the finding) |
| tarentin (second conclusion) | ✓ carried |
| separation, countability, continuity of `p`, `D` | not asked by the target; not used |

## SCOPE (disclosed)

* **The coarser topology** is a second topology on `N`, bound *before* the instance, so that
  instance synthesis finds the topology of `N` wherever the causality is used. `τc` enters only
  through `@connectedComponentIn N τc`. The intended instance has `M̃` the maximal branched
  covering, `τ = T_D = natural ∨ D*τ_X`, which in mathlib is `natural ⊓ induced D τ_X`, and
  `τc` the natural topology. Then `hτ` is `inf_le_left`, `C` is ETT's causality from curves on
  `(M̃, T_D)` (DEC-33), and `p`, `D` are its projection and developing map. Its causal
  arc-connectedness, or at least the realisation of `≤_{M̃}` by curves that
  `mem_connectedComponentIn_diamond_of_curves` takes, is owed by
  T-loc-btz-tamifying-initial and T-loc-ealpha-tamifying-alexandrov.
* **Causal arc-connectedness** (`CausallyArcConnected`, a ladder node) is the added hypothesis.
  The general form needs only its consequence `hdiam`. The rational line meets `hdiam` with the
  indiscrete `τc` and is not causally arc-connected (`rationalLine_strongCausalityLift_top`).
  Whether gluing (DEC-167) together with weak morphisms makes `hdiam` unnecessary is **open**.
* Non-vacuity (kb/0011): the timelike line over itself, `p = D = id`, meets every hypothesis
  of the target's form, tarentin included (`timelikeLine_strongCausalityLift`). Its open form
  comes from `causal_ladder`. The general form is witnessed off arc-connectedness by
  `rationalLine_strongCausalityLift_top`.
* ETT layer: the imports reach no model module (`tools/ladder.py` `model_path`, kb/0247).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter

universe u v w

section Lift

variable {M : Type v} {X : Type w} [TopologicalSpace M] [TopologicalSpace X]

/-! ### Weak morphisms send causal curves to causal curves -/

/-- A weak morphism sends a future causal curve of `V` to a future causal curve of every open
`U ⊇ φ(V)`. -/
theorem WeakMorphism.causalCurveOn_comp {N : Type u} [TopologicalSpace N] {C : Causality N}
    {D : Causality M} {φ : N → M} (h : WeakMorphism C D φ) {V : Opens N} {U : Opens M}
    (hVU : MapsTo φ V U) {c : ℝ → N} {a b : ℝ} (hc : C.CausalCurveOn V c a b) :
    D.CausalCurveOn U (φ ∘ c) a b := by
  refine ⟨fun t ht => hVU (hc.mem t ht), fun t ht N' _ hN't => ?_⟩
  obtain ⟨O, hxO, -, hle, -⟩ := h.local_mono (c t) N' hN't
  obtain ⟨l, u, hl, hu, hrel⟩ := hc.rel t ht (O ⊓ V) inf_le_right ⟨hxO, hc.mem t ht⟩
  exact ⟨l, u, hl, hu, fun s hs s' hs' h1 h2 h3 =>
    hle (C.le_mono inf_le_left (hrel s hs s' hs' h1 h2 h3))⟩

/-- **On an absolutely minimal source a weak morphism is non-decreasing at `M`**: `≤_N` is
generated by the relations of the open sets on which the morphism is non-decreasing. -/
theorem WeakMorphism.le_top_of_absolutelyMinimal {N : Type u} [TopologicalSpace N]
    {C : Causality N} {D : Causality M} {φ : N → M} (h : WeakMorphism C D φ)
    (hC : C.AbsolutelyMinimal) {a b : N} (hab : C.le ⊤ a b) : D.le ⊤ (φ a) (φ b) := by
  let S : Set (Opens N) := {O | ∀ ⦃u w : N⦄, C.le O u w → D.le ⊤ (φ u) (φ w)}
  have hS : ∀ x ∈ (⊤ : Opens N), ∃ O ∈ S, x ∈ O := fun x _ => by
    obtain ⟨V, hxV, -, hle, -⟩ := h.local_mono x ⊤ trivial
    exact ⟨V, fun u w huw => hle huw, hxV⟩
  have hchain := ((Precausality.absolutelyMinimal_iff.1 hC) S hS ⊤ le_rfl a b).1 hab
  clear hab
  induction hchain with
  | single hl =>
    obtain ⟨O, hO, hl⟩ := hl
    exact hO (C.le_mono inf_le_right hl)
  | tail _ hl ih =>
    obtain ⟨O, hO, hl⟩ := hl
    exact D.le_trans ih (hO (C.le_mono inf_le_right hl))

namespace Causality

variable {CM : Causality M} {CX : Causality X}

/-! ### The core: the sets `C(W) ∩ D⁻¹(V)` are causally convex

The coarse topology `τc` is bound **before** the topology of `N`, so that instance synthesis
finds the topology of `N` (the most recent local instance) wherever `C` is used, and `τc` only
where it is passed by `@`. -/

/-- **The convexity step.** `τc` is any topology on `N` (the coarser one of the target) in which
every diamond `J_N(a, z)` contains a preconnected set through `a` and `z`. If `p` and `D` are
non-decreasing for `≤_N`, `≤_M`, `≤_X`, then for `W` causally convex in `M` and `V` causally
convex in `X`, the set `C(W) ∩ D⁻¹(V)` is causally convex in `N`, where `C(W)` is the
`τc`-component of `p⁻¹(W)` through any point `x`. -/
theorem causallyConvexIn_connectedComponentIn_inter_preimage {N : Type u}
    (τc : TopologicalSpace N) [TopologicalSpace N] {C : Causality N} {p : N → M} {D : N → X}
    (hdiam : ∀ a z : N, C.le ⊤ a z → z ∈ @connectedComponentIn N τc (C.diamond ⊤ a z) a)
    (hp : ∀ a b : N, C.le ⊤ a b → CM.le ⊤ (p a) (p b))
    (hD : ∀ a b : N, C.le ⊤ a b → CX.le ⊤ (D a) (D b))
    {W : Set M} {V : Set X} (hW : CM.CausallyConvexIn W ⊤) (hV : CX.CausallyConvexIn V ⊤)
    (x : N) :
    C.CausallyConvexIn (@connectedComponentIn N τc (p ⁻¹' W) x ∩ D ⁻¹' V) ⊤ := by
  refine ⟨fun _ _ => trivial, ?_⟩
  rintro a ⟨haW, haV⟩ b ⟨hbW, hbV⟩ z hz
  obtain ⟨haz, hzb⟩ := mem_diamond.1 hz
  -- the `τc`-component of `J(a, z)` through `a`: preconnected, through `a` and `z`
  have hKpre : @IsPreconnected N τc (@connectedComponentIn N τc (C.diamond ⊤ a z) a) :=
    @isPreconnected_connectedComponentIn N τc _ _
  have haK : a ∈ @connectedComponentIn N τc (C.diamond ⊤ a z) a :=
    @mem_connectedComponentIn N τc _ _ (mem_diamond.2 ⟨C.le_refl trivial, haz⟩)
  have hpa : p a ∈ W := @connectedComponentIn_subset N τc _ _ _ haW
  have hpb : p b ∈ W := @connectedComponentIn_subset N τc _ _ _ hbW
  -- it lies in `p⁻¹(W)`: its points lie in `J(a, b)`, and `W` is causally convex
  have hKW : @connectedComponentIn N τc (C.diamond ⊤ a z) a ⊆ p ⁻¹' W := fun k hk => by
    obtain ⟨hak, hkz⟩ := mem_diamond.1 (@connectedComponentIn_subset N τc _ _ _ hk)
    exact hW.2 _ hpa _ hpb (mem_diamond.2 ⟨hp _ _ hak, hp _ _ (C.le_trans hkz hzb)⟩)
  have hcomp : @connectedComponentIn N τc (p ⁻¹' W) x =
      @connectedComponentIn N τc (p ⁻¹' W) a :=
    @connectedComponentIn_eq N τc _ _ _ haW
  refine ⟨?_, hV.2 _ haV _ hbV (mem_diamond.2 ⟨hD _ _ haz, hD _ _ hzb⟩)⟩
  rw [hcomp]
  exact (@IsPreconnected.subset_connectedComponentIn N τc _ _ _ hKpre haK hKW) (hdiam a z haz)

/-- Under the basis hypothesis, `C(W) ∩ D⁻¹(V)` is open for `W`, `V` open: it is the basis set
of each of its points. -/
theorem isOpen_connectedComponentIn_inter_preimage {N : Type u}
    (τc : TopologicalSpace N) [TopologicalSpace N] {p : N → M} {D : N → X}
    (hB : ∀ x : N, (𝓝 x).HasBasis
      (fun WV : Set M × Set X => IsOpen WV.1 ∧ p x ∈ WV.1 ∧ IsOpen WV.2 ∧ D x ∈ WV.2)
      (fun WV => @connectedComponentIn N τc (p ⁻¹' WV.1) x ∩ D ⁻¹' WV.2))
    {W : Set M} {V : Set X} (hW : IsOpen W) (hV : IsOpen V) (x : N) :
    IsOpen (@connectedComponentIn N τc (p ⁻¹' W) x ∩ D ⁻¹' V) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨hyC, hyV⟩
  have hpy : p y ∈ W := @connectedComponentIn_subset N τc _ _ _ hyC
  have hcomp : @connectedComponentIn N τc (p ⁻¹' W) x =
      @connectedComponentIn N τc (p ⁻¹' W) y :=
    @connectedComponentIn_eq N τc _ _ _ hyC
  rw [hcomp]
  exact (hB y).mem_of_mem (i := (W, V)) ⟨hW, hpy, hV, hyV⟩

/-- **Strong causality lifts, the general form.** `p`, `D` are non-decreasing at `M`, and
`hdiam` holds for `τc` (no comparison of `τc` with the topology of `N` is asked). `M` and `X`
are strongly causal, and the sets `C(W) ∩ D⁻¹(V)` form a neighbourhood basis at every point.
Then `N` is strongly causal: given a neighbourhood `U` of `x`, take a basis set
`C(W) ∩ D⁻¹(V) ⊆ U`, and causally convex neighbourhoods `W' ⊆ W` and `V' ⊆ V`. Then
`C(W') ∩ D⁻¹(V')` is causally convex, inside `U`, and contains the basis set of the interiors
of `W'` and `V'`. -/
theorem stronglyCausal_of_lift {N : Type u}
    (τc : TopologicalSpace N) [TopologicalSpace N] {C : Causality N} {p : N → M} {D : N → X}
    (hdiam : ∀ a z : N, C.le ⊤ a z → z ∈ @connectedComponentIn N τc (C.diamond ⊤ a z) a)
    (hp : ∀ a b : N, C.le ⊤ a b → CM.le ⊤ (p a) (p b))
    (hD : ∀ a b : N, C.le ⊤ a b → CX.le ⊤ (D a) (D b))
    (hM : CM.StronglyCausal) (hX : CX.StronglyCausal)
    (hB : ∀ x : N, (𝓝 x).HasBasis
      (fun WV : Set M × Set X => IsOpen WV.1 ∧ p x ∈ WV.1 ∧ IsOpen WV.2 ∧ D x ∈ WV.2)
      (fun WV => @connectedComponentIn N τc (p ⁻¹' WV.1) x ∩ D ⁻¹' WV.2)) :
    C.StronglyCausal := by
  intro x U hU
  obtain ⟨⟨W, V⟩, ⟨hWo, hxW, hVo, hxV⟩, hsub⟩ := (hB x).mem_iff.1 hU
  obtain ⟨W', hW'n, hW'W, hW'c⟩ := hM (p x) W (hWo.mem_nhds hxW)
  obtain ⟨V', hV'n, hV'V, hV'c⟩ := hX (D x) V (hVo.mem_nhds hxV)
  refine ⟨@connectedComponentIn N τc (p ⁻¹' W') x ∩ D ⁻¹' V', ?_, ?_,
    causallyConvexIn_connectedComponentIn_inter_preimage τc hdiam hp hD hW'c hV'c x⟩
  · -- a neighbourhood: it contains the basis set of the interiors
    obtain ⟨W'', hW''sub, hW''o, hxW''⟩ := mem_nhds_iff.1 hW'n
    obtain ⟨V'', hV''sub, hV''o, hxV''⟩ := mem_nhds_iff.1 hV'n
    refine Filter.mem_of_superset ((hB x).mem_of_mem (i := (W'', V''))
      ⟨hW''o, hxW'', hV''o, hxV''⟩) ?_
    exact inter_subset_inter (@connectedComponentIn_mono N τc x _ _ (preimage_mono hW''sub))
      (preimage_mono hV''sub)
  · exact (inter_subset_inter (@connectedComponentIn_mono N τc x _ _ (preimage_mono hW'W))
      (preimage_mono hV'V)).trans hsub

/-- **Strong causality lifts, the general open form.** With `M` and `X` strongly causal by
open sets, so is `N`: the convex set `C(W') ∩ D⁻¹(V')` with `W'` and `V'` open is open
(`isOpen_connectedComponentIn_inter_preimage`). -/
theorem stronglyCausalOpen_of_lift {N : Type u}
    (τc : TopologicalSpace N) [TopologicalSpace N] {C : Causality N} {p : N → M} {D : N → X}
    (hdiam : ∀ a z : N, C.le ⊤ a z → z ∈ @connectedComponentIn N τc (C.diamond ⊤ a z) a)
    (hp : ∀ a b : N, C.le ⊤ a b → CM.le ⊤ (p a) (p b))
    (hD : ∀ a b : N, C.le ⊤ a b → CX.le ⊤ (D a) (D b))
    (hM : CM.StronglyCausalOpen) (hX : CX.StronglyCausalOpen)
    (hB : ∀ x : N, (𝓝 x).HasBasis
      (fun WV : Set M × Set X => IsOpen WV.1 ∧ p x ∈ WV.1 ∧ IsOpen WV.2 ∧ D x ∈ WV.2)
      (fun WV => @connectedComponentIn N τc (p ⁻¹' WV.1) x ∩ D ⁻¹' WV.2)) :
    C.StronglyCausalOpen := by
  intro x U hU
  obtain ⟨⟨W, V⟩, ⟨hWo, hxW, hVo, hxV⟩, hsub⟩ := (hB x).mem_iff.1 hU
  obtain ⟨W', hxW', hW'W, hW'c⟩ := hM (p x) W (hWo.mem_nhds hxW)
  obtain ⟨V', hxV', hV'V, hV'c⟩ := hX (D x) V (hVo.mem_nhds hxV)
  refine ⟨⟨@connectedComponentIn N τc (p ⁻¹' W') x ∩ D ⁻¹' V',
    isOpen_connectedComponentIn_inter_preimage τc hB W'.isOpen V'.isOpen x⟩,
    ⟨@mem_connectedComponentIn N τc _ _ hxW', hxV'⟩, ?_,
    causallyConvexIn_connectedComponentIn_inter_preimage τc hdiam hp hD hW'c hV'c x⟩
  exact (inter_subset_inter (@connectedComponentIn_mono N τc x _ _ (preimage_mono hW'W))
    (preimage_mono hV'V)).trans hsub

/-! ### From causal curves -/

/-- Causal arc-connectedness at `M` for `≤`: two causally related points are joined by a causal
curve of `M`. -/
theorem CausallyArcConnected.exists_causalCurveOn_top {N : Type u} [TopologicalSpace N]
    {C : Causality N} (hC : C.CausallyArcConnected) :
    ∀ a z : N, C.le ⊤ a z → ∃ c : ℝ → N, C.CausalCurveOn ⊤ c 0 1 ∧ c 0 = a ∧ c 1 = z := by
  intro a z h
  exact (hC ⊤ le_rfl a z).1.1 h

/-- If `≤_N` is realised by causal curves and `τc` is coarser than the topology of `N`, every
diamond `J_N(a, z)` contains a `τc`-preconnected set through `a` and `z`: the curve. -/
theorem mem_connectedComponentIn_diamond_of_curves {N : Type u}
    (τc : TopologicalSpace N) [TopologicalSpace N] {C : Causality N}
    (hτ : ‹TopologicalSpace N› ≤ τc)
    (harc : ∀ a z : N, C.le ⊤ a z → ∃ c : ℝ → N, C.CausalCurveOn ⊤ c 0 1 ∧ c 0 = a ∧ c 1 = z) :
    ∀ a z : N, C.le ⊤ a z → z ∈ @connectedComponentIn N τc (C.diamond ⊤ a z) a := by
  intro a z haz
  obtain ⟨c, hc, rfl, rfl⟩ := harc a z haz
  have hcont : @ContinuousOn ℝ N _ τc c (Icc 0 1) :=
    ContinuousOn.mono_rng hτ (CurveOn.continuousOn C.isRelFamily_le hc)
  have himage : @IsPreconnected N τc (c '' Icc 0 1) :=
    @IsPreconnected.image ℝ N _ τc (Icc 0 1) isPreconnected_Icc c hcont
  have hsub : c '' Icc 0 1 ⊆ C.diamond ⊤ (c 0) (c 1) := by
    rintro _ ⟨t, ht, rfl⟩
    exact mem_diamond.2 ⟨hc.le_of_le le_rfl ht.1 ht.2, hc.le_of_le ht.1 ht.2 le_rfl⟩
  exact (@IsPreconnected.subset_connectedComponentIn N τc _ _ _ himage
    ⟨0, left_mem_Icc.2 zero_le_one, rfl⟩ hsub) ⟨1, right_mem_Icc.2 zero_le_one, rfl⟩

/-- If `≤_N` is realised by causal curves and `p` sends causal curves to causal curves, `p` is
non-decreasing for `≤_N` and `≤_M`. -/
theorem le_top_map_of_curves {N : Type u} [TopologicalSpace N] {C : Causality N} {p : N → M}
    (harc : ∀ a z : N, C.le ⊤ a z → ∃ c : ℝ → N, C.CausalCurveOn ⊤ c 0 1 ∧ c 0 = a ∧ c 1 = z)
    (hp : ∀ c : ℝ → N, C.CausalCurveOn ⊤ c 0 1 → CM.CausalCurveOn ⊤ (p ∘ c) 0 1) :
    ∀ a b : N, C.le ⊤ a b → CM.le ⊤ (p a) (p b) := by
  intro a b hab
  obtain ⟨c, hc, rfl, rfl⟩ := harc a b hab
  exact (hp c hc).le_of_le le_rfl zero_le_one le_rfl

/-- **The general form with weak morphisms, under gluing.** If `N` is absolutely minimal (every
ETT causality is, DEC-167), weak morphisms `p`, `D` are non-decreasing at `M`, and the one
hypothesis left beside strong causality and the basis is `hdiam`. -/
theorem stronglyCausal_of_lift_of_weakMorphism {N : Type u}
    (τc : TopologicalSpace N) [TopologicalSpace N] {C : Causality N} {p : N → M} {D : N → X}
    (hdiam : ∀ a z : N, C.le ⊤ a z → z ∈ @connectedComponentIn N τc (C.diamond ⊤ a z) a)
    (hC : C.AbsolutelyMinimal) (hp : WeakMorphism C CM p) (hD : WeakMorphism C CX D)
    (hM : CM.StronglyCausal) (hX : CX.StronglyCausal)
    (hB : ∀ x : N, (𝓝 x).HasBasis
      (fun WV : Set M × Set X => IsOpen WV.1 ∧ p x ∈ WV.1 ∧ IsOpen WV.2 ∧ D x ∈ WV.2)
      (fun WV => @connectedComponentIn N τc (p ⁻¹' WV.1) x ∩ D ⁻¹' WV.2)) :
    C.StronglyCausal :=
  stronglyCausal_of_lift τc hdiam (fun _ _ h => hp.le_top_of_absolutelyMinimal hC h)
    (fun _ _ h => hD.le_top_of_absolutelyMinimal hC h) hM hX hB

/-! ### The target's form -/

/-- **Strong causality lifts** (`T-abs-strong-causality-lifts`), with `N` causally
arc-connected added. `p : N → M` and `D : N → X` send the causal curves of `N` to causal curves
of `M` and `X`. `M` and `X` are strongly causal. `τc` is coarser than the topology of `N`, and
every `x` has the neighbourhood basis `C(W) ∩ D⁻¹(V)`, where `W ∋ p x` and `V ∋ D x` are open
and `C(W)` is the `τc`-component of `p⁻¹(W)` through `x`. Then `N` is strongly causal. Without
causal arc-connectedness this is false (`not_stronglyCausal_lift_of_curves`). -/
theorem stronglyCausal_lift {N : Type u}
    (τc : TopologicalSpace N) [TopologicalSpace N] {C : Causality N} {p : N → M} {D : N → X}
    (hτ : ‹TopologicalSpace N› ≤ τc) (hC : C.CausallyArcConnected)
    (hp : ∀ c : ℝ → N, C.CausalCurveOn ⊤ c 0 1 → CM.CausalCurveOn ⊤ (p ∘ c) 0 1)
    (hD : ∀ c : ℝ → N, C.CausalCurveOn ⊤ c 0 1 → CX.CausalCurveOn ⊤ (D ∘ c) 0 1)
    (hM : CM.StronglyCausal) (hX : CX.StronglyCausal)
    (hB : ∀ x : N, (𝓝 x).HasBasis
      (fun WV : Set M × Set X => IsOpen WV.1 ∧ p x ∈ WV.1 ∧ IsOpen WV.2 ∧ D x ∈ WV.2)
      (fun WV => @connectedComponentIn N τc (p ⁻¹' WV.1) x ∩ D ⁻¹' WV.2)) :
    C.StronglyCausal := by
  have harc := CausallyArcConnected.exists_causalCurveOn_top hC
  exact stronglyCausal_of_lift τc (mem_connectedComponentIn_diamond_of_curves τc hτ harc)
    (le_top_map_of_curves harc hp) (le_top_map_of_curves harc hD) hM hX hB

/-- **With tarentin, the topology of `N` is its Alexandrov topology.** -/
theorem alexandrovTopology_eq_lift {N : Type u}
    (τc : TopologicalSpace N) [TopologicalSpace N] {C : Causality N} {p : N → M} {D : N → X}
    (hτ : ‹TopologicalSpace N› ≤ τc) (hC : C.CausallyArcConnected) (hT : C.Tarentin)
    (hp : ∀ c : ℝ → N, C.CausalCurveOn ⊤ c 0 1 → CM.CausalCurveOn ⊤ (p ∘ c) 0 1)
    (hD : ∀ c : ℝ → N, C.CausalCurveOn ⊤ c 0 1 → CX.CausalCurveOn ⊤ (D ∘ c) 0 1)
    (hM : CM.StronglyCausal) (hX : CX.StronglyCausal)
    (hB : ∀ x : N, (𝓝 x).HasBasis
      (fun WV : Set M × Set X => IsOpen WV.1 ∧ p x ∈ WV.1 ∧ IsOpen WV.2 ∧ D x ∈ WV.2)
      (fun WV => @connectedComponentIn N τc (p ⁻¹' WV.1) x ∩ D ⁻¹' WV.2)) :
    C.alexandrovTopology = ‹TopologicalSpace N› := by
  exact (stronglyCausal_lift τc hτ hC hp hD hM hX hB).alexandrovTopology_eq hT

/-- The open form of the lift. -/
theorem stronglyCausalOpen_lift {N : Type u}
    (τc : TopologicalSpace N) [TopologicalSpace N] {C : Causality N} {p : N → M} {D : N → X}
    (hτ : ‹TopologicalSpace N› ≤ τc) (hC : C.CausallyArcConnected)
    (hp : ∀ c : ℝ → N, C.CausalCurveOn ⊤ c 0 1 → CM.CausalCurveOn ⊤ (p ∘ c) 0 1)
    (hD : ∀ c : ℝ → N, C.CausalCurveOn ⊤ c 0 1 → CX.CausalCurveOn ⊤ (D ∘ c) 0 1)
    (hM : CM.StronglyCausalOpen) (hX : CX.StronglyCausalOpen)
    (hB : ∀ x : N, (𝓝 x).HasBasis
      (fun WV : Set M × Set X => IsOpen WV.1 ∧ p x ∈ WV.1 ∧ IsOpen WV.2 ∧ D x ∈ WV.2)
      (fun WV => @connectedComponentIn N τc (p ⁻¹' WV.1) x ∩ D ⁻¹' WV.2)) :
    C.StronglyCausalOpen := by
  have harc := CausallyArcConnected.exists_causalCurveOn_top hC
  exact stronglyCausalOpen_of_lift τc (mem_connectedComponentIn_diamond_of_curves τc hτ harc)
    (le_top_map_of_curves harc hp) (le_top_map_of_curves harc hD) hM hX hB

/-- The lift for weak morphisms `p`, `D` (the library's morphisms). -/
theorem stronglyCausal_lift_of_weakMorphism {N : Type u}
    (τc : TopologicalSpace N) [TopologicalSpace N] {C : Causality N} {p : N → M} {D : N → X}
    (hτ : ‹TopologicalSpace N› ≤ τc) (hC : C.CausallyArcConnected)
    (hp : WeakMorphism C CM p) (hD : WeakMorphism C CX D)
    (hM : CM.StronglyCausal) (hX : CX.StronglyCausal)
    (hB : ∀ x : N, (𝓝 x).HasBasis
      (fun WV : Set M × Set X => IsOpen WV.1 ∧ p x ∈ WV.1 ∧ IsOpen WV.2 ∧ D x ∈ WV.2)
      (fun WV => @connectedComponentIn N τc (p ⁻¹' WV.1) x ∩ D ⁻¹' WV.2)) :
    C.StronglyCausal := by
  exact stronglyCausal_lift τc hτ hC
    (fun _ hc => hp.causalCurveOn_comp (V := ⊤) (U := ⊤) (fun _ _ => trivial) hc)
    (fun _ hc => hD.causalCurveOn_comp (V := ⊤) (U := ⊤) (fun _ _ => trivial) hc) hM hX hB

/-- The lift with the components taken in the topology of `N` itself (`τc` the topology of
`N`). -/
theorem stronglyCausal_lift_self {N : Type u} [TopologicalSpace N] {C : Causality N}
    {p : N → M} {D : N → X} (hC : C.CausallyArcConnected)
    (hp : ∀ c : ℝ → N, C.CausalCurveOn ⊤ c 0 1 → CM.CausalCurveOn ⊤ (p ∘ c) 0 1)
    (hD : ∀ c : ℝ → N, C.CausalCurveOn ⊤ c 0 1 → CX.CausalCurveOn ⊤ (D ∘ c) 0 1)
    (hM : CM.StronglyCausal) (hX : CX.StronglyCausal)
    (hB : ∀ x : N, (𝓝 x).HasBasis
      (fun WV : Set M × Set X => IsOpen WV.1 ∧ p x ∈ WV.1 ∧ IsOpen WV.2 ∧ D x ∈ WV.2)
      (fun WV => connectedComponentIn (p ⁻¹' WV.1) x ∩ D ⁻¹' WV.2)) :
    C.StronglyCausal := by
  exact stronglyCausal_lift ‹TopologicalSpace N› le_rfl hC hp hD hM hX hB

end Causality

end Lift

/-! ### Non-vacuity: the timelike line over itself -/

/-- The basis hypothesis for `p = D = id` on `ℝ`, components in the topology of `ℝ`. -/
theorem real_hasBasis_connectedComponentIn_inter (x : ℝ) :
    (𝓝 x).HasBasis
      (fun WV : Set ℝ × Set ℝ => IsOpen WV.1 ∧ id x ∈ WV.1 ∧ IsOpen WV.2 ∧ id x ∈ WV.2)
      (fun WV => connectedComponentIn (id ⁻¹' WV.1) x ∩ id ⁻¹' WV.2) := by
  refine ⟨fun U => ⟨fun hU => ?_, ?_⟩⟩
  · obtain ⟨O, hOU, hOo, hxO⟩ := mem_nhds_iff.1 hU
    exact ⟨(O, O), ⟨hOo, hxO, hOo, hxO⟩, inter_subset_right.trans hOU⟩
  · rintro ⟨⟨W, V⟩, ⟨hWo, hxW, hVo, hxV⟩, hsub⟩
    refine Filter.mem_of_superset (inter_mem ?_ (hVo.mem_nhds hxV)) hsub
    exact (IsOpen.connectedComponentIn (x := x) hWo).mem_nhds (mem_connectedComponentIn hxW)

/-- **Non-vacuity (kb/0011).** The timelike line over itself, `p = D = id`, `τc` the topology of
`ℝ`, meets every hypothesis of `stronglyCausal_lift` and of `alexandrovTopology_eq_lift`. -/
theorem timelikeLine_strongCausalityLift :
    timelikeLine.CausallyArcConnected ∧ timelikeLine.Tarentin ∧
      (∀ c : ℝ → ℝ, timelikeLine.CausalCurveOn ⊤ c 0 1 →
        timelikeLine.CausalCurveOn ⊤ (id ∘ c) 0 1) ∧
      timelikeLine.StronglyCausal ∧ timelikeLine.StronglyCausalOpen ∧
      (∀ x : ℝ, (𝓝 x).HasBasis
        (fun WV : Set ℝ × Set ℝ => IsOpen WV.1 ∧ id x ∈ WV.1 ∧ IsOpen WV.2 ∧ id x ∈ WV.2)
        (fun WV => connectedComponentIn (id ⁻¹' WV.1) x ∩ id ⁻¹' WV.2)) ∧
      timelikeLine.StronglyCausal ∧ timelikeLine.alexandrovTopology = (inferInstance : TopologicalSpace ℝ) := by
  have hsc : timelikeLine.StronglyCausal := timelikeLine_stronglyCausal
  have hco : timelikeLine.CausallyOpen := timelikeLine_causallyOpen_of_chronalNeighbours
  have hsco : timelikeLine.StronglyCausalOpen := by causal_ladder
  refine ⟨timelikeLine_causallyArcConnected, timelikeLine_tarentin, fun _ hc => hc, hsc, hsco,
    real_hasBasis_connectedComponentIn_inter, ?_, ?_⟩
  · exact Causality.stronglyCausal_lift_self timelikeLine_causallyArcConnected (fun _ hc => hc)
      (fun _ hc => hc) hsc hsc real_hasBasis_connectedComponentIn_inter
  · exact Causality.alexandrovTopology_eq_lift _ le_rfl timelikeLine_causallyArcConnected
      timelikeLine_tarentin (fun _ hc => hc) (fun _ hc => hc) hsc hsc
      real_hasBasis_connectedComponentIn_inter

/-! ### The general form reaches beyond arc-connectedness: the rational line, `τc` indiscrete -/

/-- In the indiscrete topology every set is preconnected. -/
theorem isPreconnected_top {α : Type*} (s : Set α) : @IsPreconnected α ⊤ s := by
  intro u v hu hv _ hsu hsv
  rcases (TopologicalSpace.isOpen_top_iff u).1 hu with rfl | rfl
  · obtain ⟨_, _, h⟩ := hsu
    exact h.elim
  rcases (TopologicalSpace.isOpen_top_iff v).1 hv with rfl | rfl
  · obtain ⟨_, _, h⟩ := hsv
    exact h.elim
  simpa using hsu

/-- In the indiscrete topology the component of `F` through a point of `F` is `F`. -/
theorem connectedComponentIn_top {α : Type*} {F : Set α} {x : α} (hx : x ∈ F) :
    @connectedComponentIn α ⊤ F x = F :=
  (@connectedComponentIn_subset α ⊤ F x).antisymm
    (@IsPreconnected.subset_connectedComponentIn α ⊤ F x F (isPreconnected_top F) hx
      subset_rfl)

/-- The basis hypothesis for `p = D = id` on `ℝ`, components in the indiscrete topology: the
sets are `W ∩ V`. -/
theorem real_hasBasis_connectedComponentIn_top_inter (x : ℝ) :
    (𝓝 x).HasBasis
      (fun WV : Set ℝ × Set ℝ => IsOpen WV.1 ∧ id x ∈ WV.1 ∧ IsOpen WV.2 ∧ id x ∈ WV.2)
      (fun WV => @connectedComponentIn ℝ ⊤ (id ⁻¹' WV.1) x ∩ id ⁻¹' WV.2) := by
  refine ⟨fun U => ⟨fun hU => ?_, ?_⟩⟩
  · obtain ⟨O, hOU, hOo, hxO⟩ := mem_nhds_iff.1 hU
    refine ⟨(O, O), ⟨hOo, hxO, hOo, hxO⟩, ?_⟩
    exact inter_subset_right.trans hOU
  · rintro ⟨⟨W, V⟩, ⟨hWo, hxW, hVo, hxV⟩, hsub⟩
    refine Filter.mem_of_superset (inter_mem ?_ (hVo.mem_nhds hxV)) hsub
    rw [connectedComponentIn_top (show x ∈ id ⁻¹' W from hxW)]
    exact hWo.mem_nhds hxW

/-- **The general form applies where the target's form does not.** The rational line (no causal
curve but constants, `rationalLine_not_causallyArcConnected`), with `τc` the indiscrete
topology, coarser than that of `ℝ`, and `p = D = id` into the timelike line, meets every
hypothesis of `stronglyCausal_of_lift` and `stronglyCausalOpen_of_lift`, which give its strong
causality in both forms. -/
theorem rationalLine_strongCausalityLift_top :
    (inferInstance : TopologicalSpace ℝ) ≤ ⊤ ∧ ¬ rationalLine.CausallyArcConnected ∧
      (∀ a z : ℝ, rationalLine.le ⊤ a z →
        z ∈ @connectedComponentIn ℝ ⊤ (rationalLine.diamond ⊤ a z) a) ∧
      (∀ a b : ℝ, rationalLine.le ⊤ a b → timelikeLine.le ⊤ (id a) (id b)) ∧
      (∀ x : ℝ, (𝓝 x).HasBasis
        (fun WV : Set ℝ × Set ℝ => IsOpen WV.1 ∧ id x ∈ WV.1 ∧ IsOpen WV.2 ∧ id x ∈ WV.2)
        (fun WV => @connectedComponentIn ℝ ⊤ (id ⁻¹' WV.1) x ∩ id ⁻¹' WV.2)) ∧
      rationalLine.StronglyCausal ∧ rationalLine.StronglyCausalOpen := by
  have hdiam : ∀ a z : ℝ, rationalLine.le ⊤ a z →
      z ∈ @connectedComponentIn ℝ ⊤ (rationalLine.diamond ⊤ a z) a := fun a z haz => by
    have ha : a ∈ rationalLine.diamond ⊤ a z :=
      Causality.mem_diamond.2 ⟨rationalLine.le_refl trivial, haz⟩
    rw [connectedComponentIn_top ha]
    exact Causality.mem_diamond.2 ⟨haz, rationalLine.le_refl trivial⟩
  have hp : ∀ a b : ℝ, rationalLine.le ⊤ a b → timelikeLine.le ⊤ (id a) (id b) :=
    fun _ _ hab => ⟨rationalLine_le_real hab, fun _ _ => trivial⟩
  have hsc : timelikeLine.StronglyCausal := timelikeLine_stronglyCausal
  have hco : timelikeLine.CausallyOpen := timelikeLine_causallyOpen_of_chronalNeighbours
  have hsco : timelikeLine.StronglyCausalOpen := by causal_ladder
  exact ⟨le_top, rationalLine_not_causallyArcConnected, hdiam, hp,
    real_hasBasis_connectedComponentIn_top_inter,
    Causality.stronglyCausal_of_lift ⊤ hdiam hp hp hsc hsc
      real_hasBasis_connectedComponentIn_top_inter,
    Causality.stronglyCausalOpen_of_lift ⊤ hdiam hp hp hsco hsco
      real_hasBasis_connectedComponentIn_top_inter⟩

/-! ### The printed form is false without curves realising `≤_N`, in either reading of gluing -/

/-- **The symmetric rational line**: `x ≤_U y` iff `x = y ∈ U`, or `x`, `y` are rational and the
segment between them lies in `U`; no chronology. -/
def symmRationalLine : Causality ℝ where
  le U x y := (x = y ∧ x ∈ U) ∨
    (x ∈ range ((↑) : ℚ → ℝ) ∧ y ∈ range ((↑) : ℚ → ℝ) ∧ uIcc x y ⊆ (U : Set ℝ))
  lt _ _ _ := False
  le_mem_left h := h.elim (fun h => h.2) fun h => h.2.2 left_mem_uIcc
  le_mem_right h := h.elim (fun h => h.1 ▸ h.2) fun h => h.2.2 right_mem_uIcc
  lt_mem_left h := h.elim
  lt_mem_right h := h.elim
  le_refl hx := Or.inl ⟨rfl, hx⟩
  le_trans h₁ h₂ := by
    rcases h₁ with ⟨rfl, -⟩ | ⟨hx, hy, h3⟩
    · exact h₂
    rcases h₂ with ⟨rfl, -⟩ | ⟨-, hz, h3'⟩
    · exact Or.inr ⟨hx, hy, h3⟩
    · exact Or.inr ⟨hx, hz, uIcc_subset_uIcc_union_uIcc.trans (union_subset h3 h3')⟩
  lt_trans h _ := h
  le_mono h _ _ h' := h'.elim (fun h' => Or.inl ⟨h'.1, h h'.2⟩)
    fun h' => Or.inr ⟨h'.1, h'.2.1, fun _ hz => h (h'.2.2 hz)⟩
  lt_mono _ _ _ h' := h'
  le_of_lt h := h.elim
  isOpen_lt_right _ _ := by simp
  isOpen_lt_left _ _ := by simp

theorem symmRationalLine_le {U : Opens ℝ} {x y : ℝ} :
    symmRationalLine.le U x y ↔ (x = y ∧ x ∈ U) ∨
      (x ∈ range ((↑) : ℚ → ℝ) ∧ y ∈ range ((↑) : ℚ → ℝ) ∧ uIcc x y ⊆ (U : Set ℝ)) :=
  Iff.rfl

/-- The symmetric rational line is absolutely minimal on every open set, for every cover. -/
theorem symmRationalLine_absolutelyMinimalOn (W : Opens ℝ) :
    symmRationalLine.AbsolutelyMinimalOn W := by
  intro S hS V hVW x y
  refine ⟨fun hxy => ?_, fun hxy => False.elim hxy⟩
  -- a link of the rational line, either way round, is a link of the symmetric one
  have hlink : ∀ a b, (∃ O ∈ S, rationalLine.le (V ⊓ O) a b) →
      ∃ O ∈ S, symmRationalLine.le (V ⊓ O) a b := by
    rintro a b ⟨O, hO, h⟩
    refine ⟨O, hO, ?_⟩
    rcases rationalLine_le.1 h with ⟨rfl, ha⟩ | ⟨hlt, ha, hb, hs⟩
    · exact Or.inl ⟨rfl, ha⟩
    · exact Or.inr ⟨ha, hb, by rwa [uIcc_of_le hlt.le]⟩
  have hlink' : ∀ a b, Function.swap (fun a b => ∃ O ∈ S, rationalLine.le (V ⊓ O) a b) a b →
      ∃ O ∈ S, symmRationalLine.le (V ⊓ O) a b := by
    rintro a b ⟨O, hO, h⟩
    refine ⟨O, hO, ?_⟩
    rcases rationalLine_le.1 h with ⟨rfl, ha⟩ | ⟨hlt, hb, ha, hs⟩
    · exact Or.inl ⟨rfl, ha⟩
    · exact Or.inr ⟨ha, hb, by rwa [uIcc_of_ge hlt.le]⟩
  rcases symmRationalLine_le.1 hxy with ⟨rfl, hx⟩ | ⟨hx, hy, hsub⟩
  · obtain ⟨O, hO, hxO⟩ := hS x (hVW hx)
    exact Relation.TransGen.single ⟨O, hO, symmRationalLine.le_refl ⟨hx, hxO⟩⟩
  rcases lt_trichotomy x y with hlt | rfl | hgt
  · have h := ((rationalLine_absolutelyMinimalOn W) S hS V hVW x y).1
      (rationalLine_le.2 (Or.inr ⟨hlt, hx, hy, by rwa [uIcc_of_le hlt.le] at hsub⟩))
    exact h.mono hlink
  · have hxV : x ∈ V := hsub left_mem_uIcc
    obtain ⟨O, hO, hxO⟩ := hS x (hVW hxV)
    exact Relation.TransGen.single ⟨O, hO, symmRationalLine.le_refl ⟨hxV, hxO⟩⟩
  · have h := ((rationalLine_absolutelyMinimalOn W) S hS V hVW y x).1
      (rationalLine_le.2 (Or.inr ⟨hgt, hy, hx, by rwa [uIcc_of_ge hgt.le] at hsub⟩))
    exact h.swap.mono hlink'

/-- A causal curve of the symmetric rational line is constant on its segment. -/
theorem symmRationalLine_causalCurveOn_eq {W : Opens ℝ} {c : ℝ → ℝ} {a b : ℝ}
    (hc : symmRationalLine.CausalCurveOn W c a b) {s t : ℝ} (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) : c s = c t := by
  wlog hst : s ≤ t generalizing s t
  · exact (this ht hs (le_of_not_ge hst)).symm
  have hcont : ContinuousOn c (Icc s t) :=
    (CurveOn.continuousOn symmRationalLine.isRelFamily_le hc).mono (Icc_subset_Icc hs.1 ht.2)
  -- `c s ≤ c r` for `r ∈ [s, t]`: `c r = c s` or `c r` is rational
  have hrel : ∀ r ∈ Icc s t, c s = c r ∨ c r ∈ range ((↑) : ℚ → ℝ) := fun r hr =>
    (symmRationalLine_le.1 (hc.le_of_le hs.1 hr.1 (hr.2.trans ht.2))).imp (fun h => h.1)
      fun h => h.2.1
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨v, hvirr, hv1, hv2⟩ := exists_irrational_btwn hlt
    obtain ⟨r, hr, hcr⟩ := intermediate_value_Icc hst hcont ⟨hv1.le, hv2.le⟩
    rcases hrel r hr with h | ⟨q, hq⟩
    · rw [hcr] at h; linarith
    · exact hvirr ⟨q, hq.trans hcr⟩
  · obtain ⟨v, hvirr, hv1, hv2⟩ := exists_irrational_btwn hgt
    obtain ⟨r, hr, hcr⟩ := intermediate_value_Icc' hst hcont ⟨hv1.le, hv2.le⟩
    rcases hrel r hr with h | ⟨q, hq⟩
    · rw [hcr] at h; linarith
    · exact hvirr ⟨q, hq.trans hcr⟩

/-- The symmetric rational line is not strongly causal: `J(0, 0)` is every rational. -/
theorem symmRationalLine_not_stronglyCausal : ¬ symmRationalLine.StronglyCausal := by
  intro h
  obtain ⟨V, hV, hVU, hconv⟩ := h 0 (Ioo (-1) 1) (Ioo_mem_nhds (by norm_num) (by norm_num))
  have h0 : (0 : ℝ) ∈ V := mem_of_mem_nhds hV
  have h2 : (2 : ℝ) ∈ symmRationalLine.diamond ⊤ 0 0 := by
    rw [Causality.mem_diamond]
    exact ⟨Or.inr ⟨⟨0, by simp⟩, ⟨2, by simp⟩, fun _ _ => trivial⟩,
      Or.inr ⟨⟨2, by simp⟩, ⟨0, by simp⟩, fun _ _ => trivial⟩⟩
  have := hVU (hconv.2 0 h0 0 h0 h2)
  norm_num at this

/-- The symmetric rational line is not causally arc-connected: `0 ≤ 1`, and its causal curves
are constant. -/
theorem symmRationalLine_not_causallyArcConnected : ¬ symmRationalLine.CausallyArcConnected := by
  intro h
  have h01 : symmRationalLine.le ⊤ 0 1 :=
    Or.inr ⟨⟨0, by simp⟩, ⟨1, by simp⟩, fun _ _ => trivial⟩
  obtain ⟨c, hc, h0, h1⟩ := (h ⊤ le_rfl 0 1).1.1 h01
  have := symmRationalLine_causalCurveOn_eq hc (left_mem_Icc.2 zero_le_one)
    (right_mem_Icc.2 zero_le_one)
  rw [h0, h1] at this
  norm_num at this

/-- **The conjoined witness against the printed form.** The symmetric rational line is absolutely
minimal on every open set (the gluing reading of `defi:causalite`, DEC-167, holds), the identity
sends each of its causal curves of any open `U` to a causal curve of the timelike line in every
open `U' ⊇ U`, the timelike line is strongly causal, the basis hypothesis holds with the
components in the topology of `ℝ`; and the symmetric rational line is neither strongly causal nor
causally arc-connected. -/
theorem symmRationalLine_separates_lift :
    (∀ W : Opens ℝ, symmRationalLine.AbsolutelyMinimalOn W) ∧
      (∀ (U U' : Opens ℝ), MapsTo (id : ℝ → ℝ) U U' → ∀ (c : ℝ → ℝ) (a b : ℝ),
        symmRationalLine.CausalCurveOn U c a b → timelikeLine.CausalCurveOn U' (id ∘ c) a b) ∧
      timelikeLine.StronglyCausal ∧
      (∀ x : ℝ, (𝓝 x).HasBasis
        (fun WV : Set ℝ × Set ℝ => IsOpen WV.1 ∧ id x ∈ WV.1 ∧ IsOpen WV.2 ∧ id x ∈ WV.2)
        (fun WV => connectedComponentIn (id ⁻¹' WV.1) x ∩ id ⁻¹' WV.2)) ∧
      ¬ symmRationalLine.StronglyCausal ∧ ¬ symmRationalLine.CausallyArcConnected := by
  refine ⟨symmRationalLine_absolutelyMinimalOn, ?_, timelikeLine_stronglyCausal,
    real_hasBasis_connectedComponentIn_inter, symmRationalLine_not_stronglyCausal,
    symmRationalLine_not_causallyArcConnected⟩
  intro U U' hUU' c a b hc
  refine Causality.causalCurveOn_of_forall_eq (fun t ht => hUU' (hc.mem t ht)) ?_
  intro s hs t ht
  exact congrArg id (symmRationalLine_causalCurveOn_eq hc hs ht)

/-- **The printed form is false (either reading of gluing).** -/
theorem not_stronglyCausal_lift_of_curves :
    ¬ ∀ (N M X : Type) (τc : TopologicalSpace N) [TopologicalSpace N] [TopologicalSpace M]
      [TopologicalSpace X] (C : Causality N) (CM : Causality M) (CX : Causality X) (p : N → M)
      (D : N → X), ‹TopologicalSpace N› ≤ τc →
      (∀ (U : Opens N) (U' : Opens M), MapsTo p U U' → ∀ (c : ℝ → N) (a b : ℝ),
        C.CausalCurveOn U c a b → CM.CausalCurveOn U' (p ∘ c) a b) →
      (∀ (U : Opens N) (U' : Opens X), MapsTo D U U' → ∀ (c : ℝ → N) (a b : ℝ),
        C.CausalCurveOn U c a b → CX.CausalCurveOn U' (D ∘ c) a b) →
      CM.StronglyCausal → CX.StronglyCausal →
      (∀ x : N, (𝓝 x).HasBasis
        (fun WV : Set M × Set X => IsOpen WV.1 ∧ p x ∈ WV.1 ∧ IsOpen WV.2 ∧ D x ∈ WV.2)
        (fun WV => @connectedComponentIn N τc (p ⁻¹' WV.1) x ∩ D ⁻¹' WV.2)) →
      C.StronglyCausal := by
  intro h
  have hcurve : ∀ (U U' : Opens ℝ), MapsTo (id : ℝ → ℝ) U U' → ∀ (c : ℝ → ℝ) (a b : ℝ),
      symmRationalLine.CausalCurveOn U c a b → timelikeLine.CausalCurveOn U' (id ∘ c) a b := by
    intro U U' hUU' c a b hc
    refine Causality.causalCurveOn_of_forall_eq (fun t ht => hUU' (hc.mem t ht)) ?_
    intro s hs t ht
    exact congrArg id (symmRationalLine_causalCurveOn_eq hc hs ht)
  exact symmRationalLine_not_stronglyCausal (h ℝ ℝ ℝ _ symmRationalLine timelikeLine timelikeLine
    id id le_rfl hcurve hcurve timelikeLine_stronglyCausal timelikeLine_stronglyCausal
    real_hasBasis_connectedComponentIn_inter)

/-! ### With weak morphisms and no gluing: `timelikeLineTop` -/

/-- The identity from `timelikeLineTop` to the timelike line is a weak morphism. -/
theorem weakMorphism_timelikeLineTop_id : WeakMorphism timelikeLineTop timelikeLine id := by
  refine ⟨continuous_id, fun x U hxU => ?_⟩
  let O : Opens ℝ := U ⊓ ⟨Ioo (x - 1) (x + 1), isOpen_Ioo⟩
  have hO : O ≠ ⊤ := by
    intro h
    have hmem : x + 1 ∈ O := h ▸ (trivial : x + 1 ∈ (⊤ : Opens ℝ))
    exact lt_irrefl _ hmem.2.2
  refine ⟨O, ⟨hxU, by linarith, by linarith⟩, fun _ hy => hy.1, fun y z hyz => ?_,
    fun y z hyz => timelikeLine.lt_mono inf_le_left hyz⟩
  rcases hyz with h | h
  · exact absurd h hO
  · exact timelikeLine.le_mono inf_le_left h

theorem timelikeLineTop_not_stronglyCausal : ¬ timelikeLineTop.StronglyCausal := by
  intro h
  obtain ⟨V, hV, hVU, hconv⟩ := h 0 (Ioo (-1) 1) (Ioo_mem_nhds (by norm_num) (by norm_num))
  have h0 : (0 : ℝ) ∈ V := mem_of_mem_nhds hV
  have h2 : (2 : ℝ) ∈ timelikeLineTop.diamond ⊤ 0 0 :=
    Causality.mem_diamond.2 ⟨Or.inl rfl, Or.inl rfl⟩
  have := hVU (hconv.2 0 h0 0 h0 h2)
  norm_num at this

theorem timelikeLineTop_tarentin : timelikeLineTop.Tarentin := by
  intro x U hU
  have hdiam : timelikeLineTop.diamond ⊤ x x = univ :=
    eq_univ_of_forall fun _ => Causality.mem_diamond.2 ⟨Or.inl rfl, Or.inl rfl⟩
  refine ⟨x, mem_of_mem_nhds hU, x, mem_of_mem_nhds hU, ?_⟩
  rw [Causality.openDiamond, hdiam, interior_univ]
  trivial

theorem timelikeLineTop_alexandrovTopology_ne :
    timelikeLineTop.alexandrovTopology ≠ (inferInstance : TopologicalSpace ℝ) := by
  intro h
  have htop : (⊤ : TopologicalSpace ℝ) ≤ timelikeLineTop.alexandrovTopology := by
    refine le_generateFrom ?_
    rintro S ⟨p, q, rfl⟩
    have hdiam : timelikeLineTop.diamond ⊤ p q = univ :=
      eq_univ_of_forall fun _ => Causality.mem_diamond.2 ⟨Or.inl rfl, Or.inl rfl⟩
    rw [Causality.openDiamond, hdiam, interior_univ]
    exact @isOpen_univ ℝ ⊤
  rw [h] at htop
  have hopen : IsOpen[⊤] (Ioi (0 : ℝ)) := TopologicalSpace.le_def.1 htop _ isOpen_Ioi
  rcases (TopologicalSpace.isOpen_top_iff _).1 hopen with h0 | h0
  · have : (1 : ℝ) ∈ Ioi (0 : ℝ) := by norm_num
    rw [h0] at this; exact this
  · have : (-1 : ℝ) ∈ Ioi (0 : ℝ) := by rw [h0]; trivial
    norm_num at this

/-- **Without gluing, weak morphisms and tarentin do not help either.** -/
theorem not_alexandrovTopology_eq_lift_of_weakMorphism :
    ¬ ∀ (N M X : Type) (τc : TopologicalSpace N) [TopologicalSpace N] [TopologicalSpace M]
      [TopologicalSpace X] (C : Causality N) (CM : Causality M) (CX : Causality X) (p : N → M)
      (D : N → X), ‹TopologicalSpace N› ≤ τc →
      WeakMorphism C CM p → WeakMorphism C CX D → C.Tarentin →
      CM.StronglyCausal → CX.StronglyCausal →
      (∀ x : N, (𝓝 x).HasBasis
        (fun WV : Set M × Set X => IsOpen WV.1 ∧ p x ∈ WV.1 ∧ IsOpen WV.2 ∧ D x ∈ WV.2)
        (fun WV => @connectedComponentIn N τc (p ⁻¹' WV.1) x ∩ D ⁻¹' WV.2)) →
      C.StronglyCausal ∨ C.alexandrovTopology = ‹TopologicalSpace N› := by
  intro h
  rcases h ℝ ℝ ℝ _ timelikeLineTop timelikeLine timelikeLine id id le_rfl
    weakMorphism_timelikeLineTop_id weakMorphism_timelikeLineTop_id timelikeLineTop_tarentin
    timelikeLine_stronglyCausal timelikeLine_stronglyCausal
    real_hasBasis_connectedComponentIn_inter with h | h
  · exact timelikeLineTop_not_stronglyCausal h
  · exact timelikeLineTop_alexandrovTopology_ne h

/-- **The conjoined witness without gluing.** The identity from `timelikeLineTop` to the timelike
line is a weak morphism; `timelikeLineTop` is tarentin; the basis hypothesis holds; and
`timelikeLineTop` is neither strongly causal nor Alexandrov, nor causal, nor absolutely minimal
(it is a causality only because `Causality` carries no gluing axiom, kb/0014). -/
theorem timelikeLineTop_separates_lift :
    WeakMorphism timelikeLineTop timelikeLine id ∧ timelikeLineTop.Tarentin ∧
      timelikeLine.StronglyCausal ∧
      (∀ x : ℝ, (𝓝 x).HasBasis
        (fun WV : Set ℝ × Set ℝ => IsOpen WV.1 ∧ id x ∈ WV.1 ∧ IsOpen WV.2 ∧ id x ∈ WV.2)
        (fun WV => connectedComponentIn (id ⁻¹' WV.1) x ∩ id ⁻¹' WV.2)) ∧
      ¬ timelikeLineTop.StronglyCausal ∧
      timelikeLineTop.alexandrovTopology ≠ (inferInstance : TopologicalSpace ℝ) ∧
      ¬ timelikeLineTop.IsCausal ∧ ¬ timelikeLineTop.AbsolutelyMinimal :=
  ⟨weakMorphism_timelikeLineTop_id, timelikeLineTop_tarentin, timelikeLine_stronglyCausal,
    real_hasBasis_connectedComponentIn_inter, timelikeLineTop_not_stronglyCausal,
    timelikeLineTop_alexandrovTopology_ne, timelikeLineTop_not_isCausal,
    timelikeLineTop_not_absolutelyMinimal⟩

end Causal
