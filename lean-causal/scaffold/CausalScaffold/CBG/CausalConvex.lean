import CausalScaffold.SubExtension
import CausalScaffold.CurvesExtend
import CausalScaffold.CompactCauchy
import Mathlib.Order.Interval.Set.IsoIoo

/-!
# Cauchy inclusions are causally convex; unions of Cauchy inclusions; `lem:C_ext_connexe` re-routed

No label is marked (package WP-36b-CBGCausalConvex, design `docs/CBG-DESIGN.md` §3 steps 1 and 3,
package 2). Numbering is the design's: **§3 step 1** is `lem:C_ext_connexe` (re-routed), **§3 step
3** is `prop:Cauchy_pgcd`'s two new ingredients — *convexity* (a Cauchy inclusion is causally
convex) and *the union* (a union of Cauchy inclusions is a Cauchy inclusion). The ETT labels
this file serves — `lem:C_ext_connexe` (`ETT.tex:1932`), `prop:Cauchy_pgcd` (`ETT.tex:1945`),
`def:cauchy_embedding_cauchy_extension` (`ETT.tex:1858`) — are the ETT campaign's to mark, and stay
unmarked here (DEC-60: CBG is proved in the framework of rigid morphisms of singular
`(G,X)`-manifolds; this file is the model-free causal part of it). Everything is in ETT generality:
a causality on a topological space, open sets as spacetimes (kb/0001), `CurvesExtend` as a named
model fact (kb/0012).

> **Lemma** (`lem:C_ext_connexe`). Let $M$ be a connected globally hyperbolic singular flat
> spacetime and let $\phi:M\rightarrow N$ be a Cauchy extension. If $A$ and $B$ are open subsets of
> $N$ containing $\phi(M)$ and such that the inclusions $\phi(M)\rightarrow A$ and
> $\phi(M)\rightarrow B$ are Cauchy embeddings, then $A\cap B$ is connected.
> *Proof.* […] The map $M\rightarrow A\cap B$ is a Cauchy embedding, so $\phi(\Sigma)$ is a Cauchy
> surface of $A\cap B$ and every point of $A\cap B$ lies on an inextensible causal curve meeting
> $\phi(\Sigma)$. Hence $A\cap B$ is arcwise connected. (`ETT.tex:1932–1943`)

> On remarque que $M\xrightarrow{\phi} A\cap B$ est un plongement de Cauchy et que tout point de
> $A\cap B$ est relié à $\phi(\Sigma)$ par une courbe causale. (`these.tex:6388–6389`)

> 2. $U$ is globally hyperbolic with Cauchy surface $\iota(M)$: Let $\gamma$ be an inextendible
> timelike curve in $U$. Take a point on $\gamma$; it lies in some $U_\alpha$ and the corresponding
> curve segment in $U_\alpha$ can be considered to be an inextendible timelike curve in $U_\alpha$
> and thus has to meet $\iota(M)$. Note that $\gamma$ cannot meet $\iota(M)$ more than once, since
> $\gamma$ is also a segment of an inextendible timelike curve in $M$ - and $M$ is globally
> hyperbolic. (Sbierski 1309.7591, proof of Thm 3.4)

## What is proved (no `sorry` in this file)

1. **Relative components** (`inextensible_ordConnectedComponent_of_le`): the component, in an
   open `W ≤ U`, of an inextensible curve **of `U`** is inextensible in `W`. The strict library has
   it for `U = ⊤` only; the relative form is obtained by reading `U` as a spacetime through
   `Causality.relativeTo U` (`Causal/Local.lean`'s `restrict`, then `extend`), and needs only `≤_U`
   antisymmetric and `M` Hausdorff.
2. **§3 step 3 (convexity): a Cauchy inclusion is causally convex**
   (`causallyConvexIn_of_isCauchySurfaceOn`, `IsCauchyInclusion.causallyConvexIn`): `A ≤ B` open,
   `S ⊆ A` a Cauchy surface of `A` and of `B`, `M` Hausdorff, `≤_B` antisymmetric, `B` causally
   arc-connected with `CurvesExtendOn B` ⟹ `A` is causally convex in `B`. For `B = ⊤`: a Cauchy
   inclusion into a causal T2 spacetime with `CurvesExtend` **and causal arc-connectedness** is
   causally convex.
   **The last hypothesis cannot be dropped for non-absolutely-minimal (non-local) causalities;
   whether it can be dropped under Level A (absolutely minimal on every open) is OPEN.**
   Witness (`gateLine_cauchyInclusion_not_causallyConvex`, whose statement conjoins
   `¬ AbsolutelyMinimalOn gateLine ⊤`): on the *gated line* (the timelike line plus an isolated
   point `⋆`, with `a ≤ ⋆` for `a ≤ 10` in every open set containing `a`, `⋆` and the gate `5`),
   `A = ]-1, 1[ ∪ {⋆}` is Cauchy-included in the whole space — causal, Hausdorff, globally
   hyperbolic, with a continuous time function, so curves extend — and is not causally convex
   (`g 0 ≤ 5 ≤ ⋆`, `5 ∉ A`). The gated line is not absolutely minimal (the relation `0 ≤ ⋆` is
   realised by no chain of localised relations), so it lies outside the design's Level A, which
   is the setting the design's claim concerns. Flat instances discharge the hypothesis anyway
   (`flatCausality_causallyArcConnected`, `SingularFlatAxioms.causallyArcConnected`).
3. **§3 step 3 (the union)** (`isCauchyInclusion_iSup`, `isCauchyInclusion_iSup_of_common`,
   `Causality.isCauchySurfaceOn_iSup`): inside an open `B` (curves extending, `≤_B`
   antisymmetric), the union of open sets `W i ≤ B` with a common Cauchy surface `S` of every
   `W i` and of `B` has `S` as a Cauchy surface (Cauchy property by components, as Sbierski;
   uniqueness because a segment of the curve lies on an inextensible curve of `B` — Sbierski's
   "`γ` is also a segment of an inextendible curve in `M`" — **no causal arc-connectedness**);
   with `B` causally arc-connected it is moreover causally convex in `B` and, `B` globally
   hyperbolic, is globally hyperbolic (`GloballyHyperbolicOn.of_causallyConvexIn`) — no directedness
   or compatibility is needed, the members being open sets of one space. In the form of a family of
   Cauchy inclusions `A → W i` with `A → B`, no common Cauchy surface is assumed: one is produced
   (`IsCauchySurfaceOn.of_le`, the relative `lem:Cauchy_plongement_toutes`). Also:
   `IsCauchyInclusion.trans`, `IsCauchyInclusion.of_le` (`A → W`, `A → B` ⟹ `W → B`).
4. **§3 step 1: `lem:C_ext_connexe` re-routed, strongest form** (`inf_component_meets`,
   `exists_inextensible_inf_meeting_of_subsingleton`, `isPreconnected_inf_of_subset`,
   `IsCauchyEmbedding.isPreconnected_inf_of_preconnectedSpace`,
   `IsCauchyEmbedding.c_ext_connexe_of_connectedSpace`): **`M` connected ⟹ `A ∩ B` connected**,
   with exactly the paper's topological hypothesis — no splitting of `M`, no connected Cauchy
   surface (the connected set used is `φ(M)` itself), no causal arc-connectedness, no `hthrough`,
   no `exists_mem_image_inf`; `N` Hausdorff with curves extending (kb/0012). Generic core: if `T`
   is a Cauchy surface of `A` and of `B` meeting every inextensible curve of `M` at most once (a
   Cauchy surface of `M`, or an acausal set), every point of `A ∩ B` lies on an inextensible causal
   curve of `A ∩ B` meeting `T` — the paper's last sentence — and `A ∩ B` is preconnected as soon
   as some preconnected `P` with `T ⊆ P ⊆ A ∩ B` exists.
5. **The middle step reduced to its existence half** (`inter_subsingleton_of_curvesExtend`,
   `isCauchySurfaceOn_iff_of_curvesExtend`, `IsCauchyEmbedding.isCauchySurfaceOn_inf_iff`): every
   causal curve of every open set meets `φ(Σ)` at most once, so `φ(Σ)` is a Cauchy surface of
   `A ∩ B` iff every inextensible curve of `A ∩ B` meets it.

## Hypothesis checklist

| hypothesis | here |
|---|---|
| singular flat spacetimes, `𝕄≥0`-morphisms | ⚠ weakened: any causality; `IsCauchyEmbedding` (DEC-17) |
| (C_ext_connexe) `M` connected, GH | ✓ carried: `[ConnectedSpace M]` (`c_ext_connexe_of_connectedSpace`); ⚠ weakened to `PreconnectedSpace M` for preconnectedness; no splitting |
| (C_ext_connexe) curves of `N` extend | ⚠ named: `D.CurvesExtend` (kb/0012; discharged by a time function, `CurvesExtend.lean`) |
| (C_ext_connexe) `N` causally arc-connected, `hthrough`, `φ(Σ)` Cauchy in `A ∩ B` | ⚠ weakened: not used (all three were hypotheses or a `sorry` of `SubExtension.c_ext_connexe`) |
| (§3 step 3, convexity) `B` causal T2, `CurvesExtend` | ✓ carried as `≤_B` antisymmetric, `[T2Space M]`; ⚠ named: `CurvesExtendOn B`; ⚠ strengthened by `CausallyArcConnectedOn B` — necessary among non-local causalities (gated line, not absolutely minimal: `gateLine_cauchyInclusion_not_causallyConvex`), **open** for absolutely minimal ones (Level A); discharged on flat instances |
| (§3 step 3, convexity) GH of `A`, `B` | ⚠ weakened: not used |
| (§3 step 3, union) common Cauchy surface; directed / compatible family | ⚠ weakened: produced, not assumed (`isCauchyInclusion_iSup`), or assumed (`isCauchyInclusion_iSup_of_common`); no family condition |
| (§3 step 3, union) ambient `B` with `A → B` a Cauchy inclusion, `≤_B` antisymmetric | ⚠ strengthened: the union is taken inside an ambient open `B` into which `A` (or `S`) is Cauchy-included (the design's `M₁`) |
| (§3 step 3, union) curves of `B` extend | ⚠ named: `CurvesExtendOn B` (the only hypothesis the Cauchy property of the union uses beyond the above: `isCauchySurfaceOn_iSup`) |
| (§3 step 3, union) `B` causally arc-connected | ⚠ strengthened, inherited from convexity: used only for convexity of the union, hence its GH and `IsCauchyInclusion` (`isCauchyInclusion_iSup`, `_of_common`); not used for its Cauchy surface (`isCauchySurfaceOn_iSup`) |

## SCOPE (disclosed)

* "`φ(Σ)` is a Cauchy surface of `A ∩ B`" (the paper's middle sentence, `exists_mem_image_inf`'s
  existence half) is **not** proved: the re-routed proof does not need it. Its uniqueness half is
  proved (`IsCauchyEmbedding.isCauchySurfaceOn_inf_iff`). The existence half needs an inextensible
  curve **of `A ∩ B`** (over an open interval, not a segment) to lie, with a reparametrisation, on
  an inextensible curve of `N`; `CurvesExtend` extends segments only, and the time-function
  extension (`exists_inextensible_of_timeFunction`) controls images, not reparametrisations of a
  curve with stationary stretches. What is proved instead: every point of `A ∩ B` lies on an
  inextensible curve of `A ∩ B` meeting `φ(Σ)`, and `A ∩ B` is causally convex in `N` and
  globally hyperbolic (`IsCauchyEmbedding.inf_causallyConvexIn`, `N` causally arc-connected).
* `CurvesExtendOn W` is the relative form of the named `CurvesExtend`; it is a theorem under a
  time function (`curvesExtendOn_of_timeFunction`), for every open `W`.
* The gated-line witness is disconnected and not absolutely minimal, so the necessity of
  `CausallyArcConnectedOn B` for convexity (§3 step 3) is established **only among non-local
  causalities**; under Level A (absolutely minimal on every open) it is open — neither a proof
  nor a connected, absolutely minimal counterexample is known.
* Witnesses (kb/0011): on the timelike line, `timelikeLine_causalConvex_hypotheses` (the
  hypotheses of all three steps are jointly satisfiable, with `A = B = ⊤`) and
  `timelikeLine_causalConvex_proper` (convexity and union with `A = ]-1, 1[` a **proper** open
  subset of `B = ℝ`, where convexity is not trivial); on the gated line, the necessity of
  arc-connectedness among non-absolutely-minimal causalities.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Function

open scoped Interval

universe u v

namespace Causality

section Relative

variable {M : Type u} [TopologicalSpace M]

/-! ### Curves read in two causalities agreeing below an open set -/

/-- A curve of `V` for a relation family is one for any family implying it on the opens of `V`. -/
theorem curveOn_of_rel_imp {r r' : Opens M → M → M → Prop} {V : Opens M} {c : ℝ → M} {a b : ℝ}
    (h : ∀ N : Opens M, N ≤ V → ∀ x y, r N x y → r' N x y) (hc : CurveOn r V c a b) :
    CurveOn r' V c a b where
  mem := hc.mem
  rel t ht N hN htN := by
    obtain ⟨l, u, hl, hu, hrel⟩ := hc.rel t ht N hN htN
    exact ⟨l, u, hl, hu, fun s hs s' hs' h1 h2 h3 => h N hN _ _ (hrel s hs s' hs' h1 h2 h3)⟩

variable {C₁ C₂ : Causality M} {V : Opens M} {I : Set ℝ} {c : ℝ → M}

theorem causalCurveIn_congr_causality
    (h : ∀ N : Opens M, N ≤ V → ∀ x y, C₁.le N x y ↔ C₂.le N x y) :
    C₁.CausalCurveIn V I c ↔ C₂.CausalCurveIn V I c :=
  ⟨fun hc => ⟨hc.nonempty, hc.ordConnected, fun a ha b hb =>
      curveOn_of_rel_imp (fun N hN x y => (h N hN x y).1) (hc.curve a ha b hb)⟩,
    fun hc => ⟨hc.nonempty, hc.ordConnected, fun a ha b hb =>
      curveOn_of_rel_imp (fun N hN x y => (h N hN x y).2) (hc.curve a ha b hb)⟩⟩

theorem extensible_congr_causality
    (h : ∀ N : Opens M, N ≤ V → ∀ x y, C₁.le N x y ↔ C₂.le N x y) :
    C₁.Extensible V I c ↔ C₂.Extensible V I c := by
  constructor
  · rintro ⟨I', c', hcurve, hrep, hgrow⟩
    exact ⟨I', c', (causalCurveIn_congr_causality h).1 hcurve, hrep, hgrow⟩
  · rintro ⟨I', c', hcurve, hrep, hgrow⟩
    exact ⟨I', c', (causalCurveIn_congr_causality h).2 hcurve, hrep, hgrow⟩

/-- Inextensibility in `V` reads only the relations of the open subsets of `V`. -/
theorem inextensible_congr_causality
    (h : ∀ N : Opens M, N ≤ V → ∀ x y, C₁.le N x y ↔ C₂.le N x y) :
    C₁.Inextensible V I c ↔ C₂.Inextensible V I c :=
  and_congr (causalCurveIn_congr_causality h) (not_congr (extensible_congr_causality h))

/-! ### The open set `U` read as a spacetime -/

/-- **The causality of the open set `U`, carried by `M`**: the restriction of `C` to the open
subsets of `U` (`Causality.restrict`), extended to `M` by the diagonal (`LocalCausality.extend`).
Its relations on the opens of `U` are those of `C`; on `M` it relates `x` to `y` iff `x = y` or
`x ≤_U y`. -/
def relativeTo (C : Causality M) (U : Opens M) : Causality M := (C.restrict U).extend

variable {C : Causality M} {U : Opens M}

theorem relativeTo_le_iff {N : Opens M} (hN : N ≤ U) {x y : M} :
    (C.relativeTo U).le N x y ↔ C.le N x y :=
  LocalCausality.extend_le_iff hN

theorem relativeTo_le_top {x y : M} (h : (C.relativeTo U).le ⊤ x y) : x = y ∨ C.le U x y := by
  have h' : (x = y ∧ x ∈ (⊤ : Opens M)) ∨ C.le (⊤ ⊓ U) x y := h
  rcases h' with ⟨rfl, -⟩ | h'
  · exact Or.inl rfl
  · rw [top_inf_eq] at h'
    exact Or.inr h'

/-- `U` read as a spacetime is causal when `≤_U` is antisymmetric. -/
theorem relativeTo_isCausal (hanti : ∀ ⦃x y : M⦄, C.le U x y → C.le U y x → x = y) :
    (C.relativeTo U).IsCausal := by
  intro x y hxy hyx
  rcases relativeTo_le_top hxy with h | h
  · exact h
  rcases relativeTo_le_top hyx with h' | h'
  · exact h'.symm
  exact hanti h h'

/-- A curve of `M` for `U`'s causality passing through `U` stays in `U`. -/
theorem relativeTo_mem {I : Set ℝ} {c : ℝ → M} (hc : (C.relativeTo U).CausalCurveIn ⊤ I c)
    {t : ℝ} (ht : t ∈ I) (hU : c t ∈ U) {s : ℝ} (hs : s ∈ I) : c s ∈ U := by
  rcases le_total t s with h | h
  · rcases relativeTo_le_top (hc.le_of_le ht hs h) with h' | h'
    · rw [← h']; exact hU
    · exact C.le_mem_right h'
  · rcases relativeTo_le_top (hc.le_of_le hs ht h) with h' | h'
    · rw [h']; exact hU
    · exact C.le_mem_left h'

theorem relativeTo_causalCurveIn {I : Set ℝ} {c : ℝ → M}
    (hc : (C.relativeTo U).CausalCurveIn ⊤ I c) {t : ℝ} (ht : t ∈ I) (hU : c t ∈ U) :
    C.CausalCurveIn U I c := by
  have hc' : (C.relativeTo U).CausalCurveIn U I c :=
    ⟨hc.nonempty, hc.ordConnected, fun a ha b hb => CurveOn.restrict (hc.curve a ha b hb) le_rfl
      le_rfl le_top fun s hs => relativeTo_mem hc ht hU (hc.ordConnected.out ha hb hs)⟩
  exact (causalCurveIn_congr_causality fun N hN x y => relativeTo_le_iff hN).1 hc'

/-- An inextensible curve of `U` is an inextensible curve of `M` for `U`'s causality. -/
theorem relativeTo_inextensible_top {I : Set ℝ} {c : ℝ → M} (hc : C.Inextensible U I c) :
    (C.relativeTo U).Inextensible ⊤ I c := by
  have hcongr : ∀ N : Opens M, N ≤ U → ∀ x y, (C.relativeTo U).le N x y ↔ C.le N x y :=
    fun N hN x y => relativeTo_le_iff hN
  refine ⟨((causalCurveIn_congr_causality hcongr).2 hc.1).mono_opens le_top, ?_⟩
  rintro ⟨I', c', hcurve, ⟨φ, h1, h2, h3, h4⟩, hgrow⟩
  obtain ⟨t₀, ht₀⟩ := hc.1.nonempty
  have hmem : c' (φ t₀) ∈ U := by rw [h4 t₀ ht₀]; exact hc.1.mem ht₀
  exact hc.2 ⟨I', c', relativeTo_causalCurveIn hcurve (h2 ht₀) hmem, ⟨φ, h1, h2, h3, h4⟩, hgrow⟩

/-- **The component of an inextensible curve of `U` in an open `W ≤ U`, through a parameter whose
point lies in `W`, is an inextensible curve of `W`** (`M` Hausdorff, `≤_U` antisymmetric). The
relative form of `inextensible_ordConnectedComponent`, which is its case `U = ⊤`. -/
theorem inextensible_ordConnectedComponent_of_le [T2Space M] {W : Opens M}
    (hanti : ∀ ⦃x y : M⦄, C.le U x y → C.le U y x → x = y) (hWU : W ≤ U) {I : Set ℝ}
    {c : ℝ → M} (hc : C.Inextensible U I c) {t₀ : ℝ} (ht₀ : t₀ ∈ I) (hW : c t₀ ∈ W) :
    C.Inextensible W (ordConnectedComponent (I ∩ c ⁻¹' W) t₀) c :=
  (inextensible_congr_causality fun _ hN _ _ => relativeTo_le_iff (hN.trans hWU)).1
    (inextensible_ordConnectedComponent (relativeTo_isCausal hanti)
      (relativeTo_inextensible_top hc) ht₀ hW)

end Relative

section Convex

variable {M : Type u} [TopologicalSpace M] {C : Causality M}

/-! ### Curves extend in an open set -/

variable (C) in
/-- **`CurvesExtend` relative to the open set `W`** (a named model fact, kb/0012): every future
causal curve of `W` over a segment lies on an inextensible causal curve of `W`. For `W = ⊤` it is
`CurvesExtend` (`curvesExtendOn_top`). -/
def CurvesExtendOn (W : Opens M) : Prop :=
  ∀ (c : ℝ → M) (a b : ℝ), a ≤ b → C.CausalCurveOn W c a b →
    ∃ (I : Set ℝ) (c' : ℝ → M), C.Inextensible W I c' ∧ c '' Icc a b ⊆ c' '' I

theorem curvesExtendOn_top : C.CurvesExtendOn ⊤ ↔ C.CurvesExtend := Iff.rfl

/-- **`CurvesExtendOn W` holds for every open `W`** in a causality with a continuous function
strictly increasing along `≤_M` (`exists_inextensible_of_timeFunction`, `CurvesExtend.lean`). -/
theorem curvesExtendOn_of_timeFunction {T : M → ℝ} (hTc : Continuous T)
    (hT : ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y) (W : Opens M) : C.CurvesExtendOn W :=
  fun _ _ _ hab hc => by
    obtain ⟨J, γ, h1, h2, -⟩ :=
      exists_inextensible_of_timeFunction hTc hT (hc.causalCurveIn_Icc hab)
    exact ⟨J, γ, h1, h2⟩

/-! ### A Cauchy surface of an open set is acausal in it -/

/-- **A Cauchy surface of `B` is acausal for `≤_B`** when `B` is causally arc-connected and curves
of `B` extend: two `≤_B`-related points of `S` lie on one inextensible curve of `B`. The relative
form of `IsCauchySurface.isAcausal`. -/
theorem IsCauchySurfaceOn.eq_of_le {B : Opens M} {S : Set M} (hS : C.IsCauchySurfaceOn B S)
    (hC : C.CausallyArcConnectedOn B) (hext : C.CurvesExtendOn B) {x y : M} (hx : x ∈ S)
    (hy : y ∈ S) (hxy : C.le B x y) : x = y := by
  obtain ⟨γ, hγ, hγ0, hγ1⟩ := (hC B le_rfl x y).1.1 hxy
  obtain ⟨I, c, hc, hsub⟩ := hext γ 0 1 zero_le_one hγ
  obtain ⟨z, -, hz⟩ := hS I c hc
  have h0 : γ 0 ∈ c '' I := hsub ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
  have h1 : γ 1 ∈ c '' I := hsub ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩
  rw [hγ0] at h0; rw [hγ1] at h1
  exact (hz x ⟨h0, hx⟩).trans (hz y ⟨h1, hy⟩).symm

/-! ### Design §3 step 3 (convexity): a Cauchy inclusion is causally convex -/

/-- Along an inextensible curve of `B` through `c t ∈ A` and `c u ∉ A`, the component of the curve
in `A` through `t` meets a Cauchy surface `S` of `A` at a parameter `τ` strictly on `t`'s side of
`u`. -/
theorem exists_mem_cauchy_side [T2Space M] {A B : Opens M}
    (hanti : ∀ ⦃x y : M⦄, C.le B x y → C.le B y x → x = y) (hAB : A ≤ B) {S : Set M}
    (hSA : C.IsCauchySurfaceOn A S) {I : Set ℝ} {c : ℝ → M} (hc : C.Inextensible B I c)
    {t u : ℝ} (ht : t ∈ I) (htA : c t ∈ A) (huA : c u ∉ A) :
    ∃ τ ∈ I, c τ ∈ S ∧ (t ≤ u → τ < u) ∧ (u ≤ t → u < τ) := by
  have hJ := inextensible_ordConnectedComponent_of_le hanti hAB hc ht htA
  obtain ⟨_, ⟨⟨τ, hτ, rfl⟩, hτS⟩, -⟩ := hSA _ c hJ
  have hoc : (ordConnectedComponent (I ∩ c ⁻¹' A) t).OrdConnected := inferInstance
  have htJ : t ∈ ordConnectedComponent (I ∩ c ⁻¹' A) t :=
    self_mem_ordConnectedComponent.2 ⟨ht, htA⟩
  have huJ : u ∉ ordConnectedComponent (I ∩ c ⁻¹' A) t := fun h =>
    huA (ordConnectedComponent_subset h).2
  refine ⟨τ, (ordConnectedComponent_subset hτ).1, hτS, fun htu => lt_of_not_ge fun h => huJ ?_,
    fun hut => lt_of_not_ge fun h => huJ ?_⟩
  · exact hoc.out htJ hτ ⟨htu, h⟩
  · exact hoc.out hτ htJ ⟨h, hut⟩

/-- **Design §3 step 3 (convexity): a Cauchy inclusion is causally convex.** Let `A ≤ B` be open and
`S ⊆ A` a Cauchy surface of `A` and of `B`; let `M` be Hausdorff, `≤_B` antisymmetric, `B`
causally arc-connected with curves extending in `B`. Then `A` is causally convex in `B`.
Proof: if `p ≤_B r ≤_B q` with `p, q ∈ A`, `r ∉ A`, the inextensible curve of `B` through `p` and
`r` leaves `A` before `r`, after meeting `S` at `s₁ ≤_B r`; the one through `r` and `q` meets `S`
at `s₂ ≥_B r`; `S` is acausal in `B`, so `s₁ = s₂ = r ∈ A`. -/
theorem causallyConvexIn_of_isCauchySurfaceOn [T2Space M] {A B : Opens M}
    (hanti : ∀ ⦃x y : M⦄, C.le B x y → C.le B y x → x = y) (hC : C.CausallyArcConnectedOn B)
    (hext : C.CurvesExtendOn B) (hAB : A ≤ B) {S : Set M} (hSA : S ⊆ A)
    (hA : C.IsCauchySurfaceOn A S) (hB : C.IsCauchySurfaceOn B S) :
    C.CausallyConvexIn (A : Set M) B := by
  refine ⟨hAB, fun p hp q hq r hr => ?_⟩
  obtain ⟨hpr, hrq⟩ := mem_diamond.1 hr
  by_contra hrA
  -- the future side: `p ≤_B r`
  obtain ⟨γ₁, hγ₁, hγ₁0, hγ₁1⟩ := (hC B le_rfl p r).1.1 hpr
  obtain ⟨I₁, c₁, hc₁, hsub₁⟩ := hext γ₁ 0 1 zero_le_one hγ₁
  have hp₁ : γ₁ 0 ∈ c₁ '' I₁ := hsub₁ ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
  have hr₁ : γ₁ 1 ∈ c₁ '' I₁ := hsub₁ ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩
  rw [hγ₁0] at hp₁; rw [hγ₁1] at hr₁
  obtain ⟨tp, htp, hctp⟩ := hp₁
  obtain ⟨tr, htr, hctr⟩ := hr₁
  have hptr : tp ≤ tr := le_of_not_gt fun h => hrA (by
    have h' := hc₁.1.le_of_le htr htp h.le
    rw [hctp, hctr] at h'
    rw [← hanti hpr h']; exact hp)
  obtain ⟨τ₁, hτ₁, hτ₁S, h₁, -⟩ := exists_mem_cauchy_side hanti hAB hA hc₁ htp
    (by rw [hctp]; exact hp) (by rw [hctr]; exact hrA)
  have hs₁r : C.le B (c₁ τ₁) r := by
    rw [← hctr]; exact hc₁.1.le_of_le hτ₁ htr (h₁ hptr).le
  -- the past side: `r ≤_B q`
  obtain ⟨γ₂, hγ₂, hγ₂0, hγ₂1⟩ := (hC B le_rfl r q).1.1 hrq
  obtain ⟨I₂, c₂, hc₂, hsub₂⟩ := hext γ₂ 0 1 zero_le_one hγ₂
  have hr₂ : γ₂ 0 ∈ c₂ '' I₂ := hsub₂ ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
  have hq₂ : γ₂ 1 ∈ c₂ '' I₂ := hsub₂ ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩
  rw [hγ₂0] at hr₂; rw [hγ₂1] at hq₂
  obtain ⟨tr', htr', hctr'⟩ := hr₂
  obtain ⟨tq, htq, hctq⟩ := hq₂
  have hrtq : tr' ≤ tq := le_of_not_gt fun h => hrA (by
    have h' := hc₂.1.le_of_le htq htr' h.le
    rw [hctq, hctr'] at h'
    rw [hanti hrq h']; exact hq)
  obtain ⟨τ₂, hτ₂, hτ₂S, -, h₂⟩ := exists_mem_cauchy_side hanti hAB hA hc₂ htq
    (by rw [hctq]; exact hq) (by rw [hctr']; exact hrA)
  have hrs₂ : C.le B r (c₂ τ₂) := by
    rw [← hctr']; exact hc₂.1.le_of_le htr' hτ₂ (h₂ hrtq).le
  -- `S` is acausal in `B`
  have heq : c₁ τ₁ = c₂ τ₂ := hB.eq_of_le hC hext hτ₁S hτ₂S (C.le_trans hs₁r hrs₂)
  rw [← heq] at hrs₂
  have hr : r = c₁ τ₁ := hanti hrs₂ hs₁r
  exact hrA (hr ▸ hSA hτ₁S)

/-! ### Global hyperbolicity from causal convexity -/

/-- In an open `B` causally arc-connected, two `≤_B`-related points of a set `V` causally convex
in `B` are related in every open `N ≤ B` containing `V`: the relative `le_of_causallyConvexIn`. -/
theorem le_of_causallyConvexIn_of_le {B N : Opens M} (hC : C.CausallyArcConnectedOn B)
    {V : Set M} (hV : C.CausallyConvexIn V B) (hVN : V ⊆ N) (hNB : N ≤ B) {x y : M}
    (hx : x ∈ V) (hy : y ∈ V) (hxy : C.le B x y) : C.le N x y := by
  obtain ⟨γ, hγ, rfl, rfl⟩ := (hC B le_rfl x y).1.1 hxy
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ N := fun t ht =>
    hVN (hV.2 _ hx _ hy (mem_diamond.2
      ⟨hγ.le_of_le le_rfl ht.1 ht.2, hγ.le_of_le ht.1 ht.2 le_rfl⟩))
  have hγN : C.CausalCurveOn N γ 0 1 := CurveOn.restrict hγ le_rfl le_rfl hNB hmem
  exact hγN.le_of_le le_rfl zero_le_one le_rfl

/-- **An open set causally convex in a globally hyperbolic open `B`, causally arc-connected, is
globally hyperbolic**: its diamonds are those of `B`. -/
theorem GloballyHyperbolicOn.of_causallyConvexIn {U B : Opens M}
    (hC : C.CausallyArcConnectedOn B) (hB : C.GloballyHyperbolicOn B)
    (hU : C.CausallyConvexIn (U : Set M) B) : C.GloballyHyperbolicOn U := by
  have hUB : U ≤ B := hU.1
  refine ⟨fun x y hxy hyx => hB.1 (C.le_mono hUB hxy) (C.le_mono hUB hyx), fun p q => ?_⟩
  by_cases hp : p ∈ U
  · by_cases hq : q ∈ U
    · have heq : C.diamond U p q = C.diamond B p q := by
        ext z
        rw [mem_diamond, mem_diamond]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨C.le_mono hUB h1, C.le_mono hUB h2⟩
        · rintro ⟨h1, h2⟩
          have hz : z ∈ U := hU.2 p hp q hq (mem_diamond.2 ⟨h1, h2⟩)
          exact ⟨le_of_causallyConvexIn_of_le hC hU subset_rfl hUB hp hz h1,
            le_of_causallyConvexIn_of_le hC hU subset_rfl hUB hz hq h2⟩
      rw [heq]; exact hB.2 p q
    · have heq : C.diamond U p q = ∅ := eq_empty_of_forall_notMem fun z hz =>
        hq (C.le_mem_right (mem_diamond.1 hz).2)
      rw [heq]; exact isCompact_empty
  · have heq : C.diamond U p q = ∅ := eq_empty_of_forall_notMem fun z hz =>
      hp (C.le_mem_left (mem_diamond.1 hz).1)
    rw [heq]; exact isCompact_empty

/-! ### The relative `lem:Cauchy_plongement_toutes` -/

/-- **The relative core of `lem:Cauchy_plongement_toutes`**: `U ≤ B` open, `S₁, S₂ ⊆ U` Cauchy
surfaces of `U`; if `S₁` is a Cauchy surface of `B`, so is `S₂` (`M` Hausdorff, `≤_B`
antisymmetric). The case `B = ⊤` is `IsCauchySurfaceOn.isCauchySurface_of_open`. -/
theorem IsCauchySurfaceOn.of_le [T2Space M] {U B : Opens M}
    (hanti : ∀ ⦃x y : M⦄, C.le B x y → C.le B y x → x = y) (hUB : U ≤ B) {S₁ S₂ : Set M}
    (hS₁ : S₁ ⊆ U) (hS₂ : S₂ ⊆ U) (h₁U : C.IsCauchySurfaceOn U S₁)
    (h₂U : C.IsCauchySurfaceOn U S₂) (h₁ : C.IsCauchySurfaceOn B S₁) :
    C.IsCauchySurfaceOn B S₂ := by
  intro I c hc
  obtain ⟨_, ⟨⟨t₁, ht₁, rfl⟩, hy⟩, huniq₁⟩ := h₁ I c hc
  obtain ⟨_, ⟨⟨t₂, ht₂, rfl⟩, hz⟩, huniq₂⟩ :=
    h₂U _ c (inextensible_ordConnectedComponent_of_le hanti hUB hc ht₁ (hS₁ hy))
  refine ⟨c t₂, ⟨⟨t₂, (ordConnectedComponent_subset ht₂).1, rfl⟩, hz⟩, ?_⟩
  rintro _ ⟨⟨t₃, ht₃, rfl⟩, hz'⟩
  obtain ⟨_, ⟨⟨t₄, ht₄, rfl⟩, hx⟩, -⟩ :=
    h₁U _ c (inextensible_ordConnectedComponent_of_le hanti hUB hc ht₃ (hS₂ hz'))
  have ht₄I : t₄ ∈ I := (ordConnectedComponent_subset ht₄).1
  have h41 : c t₄ = c t₁ := huniq₁ _ ⟨⟨t₄, ht₄I, rfl⟩, hx⟩
  have hseg : [[t₁, t₄]] ⊆ I ∩ c ⁻¹' U := by
    intro b hb
    have hbI : b ∈ I := hc.1.ordConnected.uIcc_subset ht₁ ht₄I hb
    refine ⟨hbI, ?_⟩
    have hcb : c b = c t₁ := by
      rcases mem_uIcc.1 hb with h | h
      · have h1 := hc.1.le_of_le ht₁ hbI h.1
        have h2 := hc.1.le_of_le hbI ht₄I h.2
        rw [h41] at h2
        exact hanti h2 h1
      · have h1 := hc.1.le_of_le ht₄I hbI h.1
        have h2 := hc.1.le_of_le hbI ht₁ h.2
        rw [h41] at h1
        exact hanti h2 h1
    rw [mem_preimage, hcb]; exact hS₁ hy
  have ht₃J : t₃ ∈ ordConnectedComponent (I ∩ c ⁻¹' U) t₁ :=
    mem_ordConnectedComponent.2 fun b hb => by
      rcases uIcc_subset_uIcc_union_uIcc hb with hb | hb
      · exact hseg hb
      · exact mem_ordConnectedComponent.1 ht₄ (uIcc_comm t₄ t₃ ▸ hb)
  exact huniq₂ _ ⟨⟨t₃, ht₃J, rfl⟩, hz'⟩

/-! ### `lem:C_ext_connexe`, the curve step, re-routed -/

/-- **The core of the curve step**: along an inextensible curve `c` of `M` through a point of
`A ∩ B`, the component of `c` in `A ∩ B` meets `T`, when `T` is a Cauchy surface of `A` and of
`B` and meets every inextensible curve of `M` at most once (e.g. `T` a Cauchy surface of `M`, or
`T` acausal in `M`). The components of `c` in `A` and in `B` meet `T`, at the one point where
`c` meets `T`; the nearer of the two meeting parameters bounds a segment inside `A ∩ B`, and if
they lie on opposite sides, the point itself is the meeting point (`M` causal). -/
theorem inf_component_meets [T2Space M] (hcaus : C.IsCausal) {A B : Opens M} {T : Set M}
    (hT : ∀ (I : Set ℝ) (c : ℝ → M), C.Inextensible ⊤ I c → (c '' I ∩ T).Subsingleton)
    (hTA : C.IsCauchySurfaceOn A T) (hTB : C.IsCauchySurfaceOn B T) {I : Set ℝ} {c : ℝ → M}
    (hc : C.Inextensible ⊤ I c) {t₀ : ℝ} (ht₀ : t₀ ∈ I) (hx₀ : c t₀ ∈ A ⊓ B) :
    (c '' ordConnectedComponent (I ∩ c ⁻¹' (A ⊓ B : Opens M)) t₀ ∩ T).Nonempty := by
  have hx₀A : c t₀ ∈ A := (inf_le_left : A ⊓ B ≤ A) hx₀
  have hx₀B : c t₀ ∈ B := (inf_le_right : A ⊓ B ≤ B) hx₀
  have ht₀J : t₀ ∈ ordConnectedComponent (I ∩ c ⁻¹' (A ⊓ B : Opens M)) t₀ :=
    self_mem_ordConnectedComponent.2 ⟨ht₀, hx₀⟩
  obtain ⟨_, ⟨⟨tA, htA, rfl⟩, hTA'⟩, -⟩ :=
    hTA _ c (inextensible_ordConnectedComponent hcaus hc ht₀ hx₀A)
  obtain ⟨_, ⟨⟨tB, htB, rfl⟩, hTB'⟩, -⟩ :=
    hTB _ c (inextensible_ordConnectedComponent hcaus hc ht₀ hx₀B)
  have htAI : tA ∈ I := (ordConnectedComponent_subset htA).1
  have htBI : tB ∈ I := (ordConnectedComponent_subset htB).1
  have hAB : c tA = c tB := hT I c hc ⟨⟨tA, htAI, rfl⟩, hTA'⟩ ⟨⟨tB, htBI, rfl⟩, hTB'⟩
  -- the segments from `t₀` to `tA`, `tB` lie in `A`, `B`
  have hsegA : [[t₀, tA]] ⊆ I ∩ c ⁻¹' A := fun s hs =>
    ordConnectedComponent_subset ((inferInstance : (ordConnectedComponent
      (I ∩ c ⁻¹' A) t₀).OrdConnected).uIcc_subset
      (self_mem_ordConnectedComponent.2 ⟨ht₀, hx₀A⟩) htA hs)
  have hsegB : [[t₀, tB]] ⊆ I ∩ c ⁻¹' B := fun s hs =>
    ordConnectedComponent_subset ((inferInstance : (ordConnectedComponent
      (I ∩ c ⁻¹' B) t₀).OrdConnected).uIcc_subset
      (self_mem_ordConnectedComponent.2 ⟨ht₀, hx₀B⟩) htB hs)
  have hfin : ∀ τ, [[t₀, τ]] ⊆ I ∩ c ⁻¹' A → [[t₀, τ]] ⊆ I ∩ c ⁻¹' B → c τ ∈ T →
      (c '' ordConnectedComponent (I ∩ c ⁻¹' (A ⊓ B : Opens M)) t₀ ∩ T).Nonempty :=
    fun τ hτA hτB hτT => ⟨c τ, ⟨τ, mem_ordConnectedComponent.2 fun s hs =>
      ⟨(hτA hs).1, show c s ∈ A ⊓ B from ⟨(hτA hs).2, (hτB hs).2⟩⟩, rfl⟩, hτT⟩
  have hcase : ∀ τ ∈ [[t₀, tB]], τ ∈ [[t₀, tA]] → [[t₀, τ]] ⊆ [[t₀, tA]] ∧ [[t₀, τ]] ⊆ [[t₀, tB]] :=
    fun τ hτB hτA => ⟨uIcc_subset_uIcc left_mem_uIcc hτA, uIcc_subset_uIcc left_mem_uIcc hτB⟩
  rcases le_total t₀ tA with h0A | hA0 <;> rcases le_total t₀ tB with h0B | hB0
  · rcases le_total tA tB with hAB' | hBA'
    · have h := hcase tA (mem_uIcc.2 (Or.inl ⟨h0A, hAB'⟩)) right_mem_uIcc
      exact hfin tA (h.1.trans hsegA) (h.2.trans hsegB) hTA'
    · have h := hcase tB right_mem_uIcc (mem_uIcc.2 (Or.inl ⟨h0B, hBA'⟩))
      exact hfin tB (h.1.trans hsegA) (h.2.trans hsegB) hTB'
  · -- `tB ≤ t₀ ≤ tA`: `c t₀` is the meeting point
    have h1 := hc.1.le_of_le htBI ht₀ hB0
    have h2 := hc.1.le_of_le ht₀ htAI h0A
    rw [hAB] at h2
    have hx' : c tB = c t₀ := hcaus h1 h2
    exact ⟨c t₀, ⟨t₀, ht₀J, rfl⟩, hx' ▸ hTB'⟩
  · -- `tA ≤ t₀ ≤ tB`
    have h1 := hc.1.le_of_le htAI ht₀ hA0
    have h2 := hc.1.le_of_le ht₀ htBI h0B
    rw [← hAB] at h2
    have hx' : c tA = c t₀ := hcaus h1 h2
    exact ⟨c t₀, ⟨t₀, ht₀J, rfl⟩, hx' ▸ hTA'⟩
  · rcases le_total tA tB with hAB' | hBA'
    · have h := hcase tB right_mem_uIcc (mem_uIcc.2 (Or.inr ⟨hAB', hB0⟩))
      exact hfin tB (h.1.trans hsegA) (h.2.trans hsegB) hTB'
    · have h := hcase tA (mem_uIcc.2 (Or.inr ⟨hBA', hA0⟩)) right_mem_uIcc
      exact hfin tA (h.1.trans hsegA) (h.2.trans hsegB) hTA'

/-- A Cauchy surface of `M` meets every inextensible curve of `M` at most once. -/
theorem IsCauchySurface.inter_subsingleton {T : Set M} (hT : C.IsCauchySurface T) (I : Set ℝ)
    (c : ℝ → M) (hc : C.Inextensible ⊤ I c) : (c '' I ∩ T).Subsingleton :=
  fun _ hx _ hy => (hT I c hc).unique hx hy

/-- An acausal set meets every causal curve of every open set at most once. -/
theorem IsAcausal.inter_subsingleton {T : Set M} (hT : C.IsAcausal T) {W : Opens M} {I : Set ℝ}
    {c : ℝ → M} (hc : C.CausalCurveIn W I c) : (c '' I ∩ T).Subsingleton := by
  rintro _ ⟨⟨s, hs, rfl⟩, hsT⟩ _ ⟨⟨s', hs', rfl⟩, hs'T⟩
  rcases le_total s s' with h | h
  · exact hT _ hsT _ hs'T (C.le_mono le_top (hc.le_of_le hs hs' h))
  · exact (hT _ hs'T _ hsT (C.le_mono le_top (hc.le_of_le hs' hs h))).symm

/-- **A set meeting every inextensible curve of `M` at most once meets every causal curve of every
open set at most once**, when curves extend (`CurvesExtend`): the segment between two meeting
parameters lies on an inextensible curve of `M`. -/
theorem inter_subsingleton_of_curvesExtend (hext : C.CurvesExtend) {T : Set M}
    (hT : ∀ (I : Set ℝ) (c : ℝ → M), C.Inextensible ⊤ I c → (c '' I ∩ T).Subsingleton)
    {W : Opens M} {I : Set ℝ} {c : ℝ → M} (hc : C.CausalCurveIn W I c) :
    (c '' I ∩ T).Subsingleton := by
  have key : ∀ s ∈ I, ∀ s' ∈ I, s ≤ s' → c s ∈ T → c s' ∈ T → c s = c s' := by
    intro s hs s' hs' h hsT hs'T
    obtain ⟨J, c', hc', hsub⟩ := hext c s s' h
      (CurveOn.mono_opens C.isRelFamily_le (hc.curve s hs s' hs') le_top)
    exact hT J c' hc' ⟨hsub ⟨s, ⟨le_rfl, h⟩, rfl⟩, hsT⟩ ⟨hsub ⟨s', ⟨h, le_rfl⟩, rfl⟩, hs'T⟩
  rintro _ ⟨⟨s, hs, rfl⟩, hsT⟩ _ ⟨⟨s', hs', rfl⟩, hs'T⟩
  rcases le_total s s' with h | h
  · exact key s hs s' hs' h hsT hs'T
  · exact (key s' hs' s hs h hs'T hsT).symm

/-- **Being a Cauchy surface of an open set reduces to the existence half**, for a set meeting
every inextensible curve of `M` at most once, when curves extend: uniqueness is automatic. -/
theorem isCauchySurfaceOn_iff_of_curvesExtend (hext : C.CurvesExtend) {T : Set M}
    (hT : ∀ (I : Set ℝ) (c : ℝ → M), C.Inextensible ⊤ I c → (c '' I ∩ T).Subsingleton)
    (W : Opens M) :
    C.IsCauchySurfaceOn W T ↔
      ∀ (I : Set ℝ) (c : ℝ → M), C.Inextensible W I c → (c '' I ∩ T).Nonempty := by
  refine ⟨fun h I c hc => (h I c hc).exists, fun h I c hc => ?_⟩
  obtain ⟨x, hx⟩ := h I c hc
  exact ⟨x, hx, fun y hy => inter_subsingleton_of_curvesExtend hext hT hc.1 hy hx⟩

/-- **Every point of `A ∩ B` lies on an inextensible causal curve of `A ∩ B` meeting `T`**, when
`T` is a Cauchy surface of `A` and of `B` meeting every inextensible curve of `M` at most once
(the last sentence of `lem:C_ext_connexe`'s proof, `ETT.tex:1941–1942`): the constant curve at
`x` lies on an inextensible curve of `M` (`CurvesExtend`), whose component in `A ∩ B` meets `T`
(`inf_component_meets`). -/
theorem exists_inextensible_inf_meeting_of_subsingleton [T2Space M] (hcaus : C.IsCausal)
    (hext : C.CurvesExtend) {A B : Opens M} {T : Set M}
    (hT : ∀ (I : Set ℝ) (c : ℝ → M), C.Inextensible ⊤ I c → (c '' I ∩ T).Subsingleton)
    (hTA : C.IsCauchySurfaceOn A T) (hTB : C.IsCauchySurfaceOn B T) {x : M} (hx : x ∈ A ⊓ B) :
    ∃ (I : Set ℝ) (c : ℝ → M), C.Inextensible (A ⊓ B) I c ∧ x ∈ c '' I ∧ (c '' I ∩ T).Nonempty := by
  obtain ⟨I, c, hc, hsub⟩ := hext (fun _ => x) 0 0 le_rfl
    (causalCurveOn_const (show x ∈ (⊤ : Opens M) from trivial))
  obtain ⟨t₀, ht₀, hct₀⟩ : x ∈ c '' I := hsub ⟨0, ⟨le_rfl, le_rfl⟩, rfl⟩
  have hx₀ : c t₀ ∈ A ⊓ B := by rw [hct₀]; exact hx
  exact ⟨_, c, inextensible_ordConnectedComponent hcaus hc ht₀ hx₀,
    ⟨t₀, self_mem_ordConnectedComponent.2 ⟨ht₀, hx₀⟩, hct₀⟩,
    inf_component_meets hcaus hT hTA hTB hc ht₀ hx₀⟩

/-- `exists_inextensible_inf_meeting_of_subsingleton` for `T` a Cauchy surface of `M`. -/
theorem exists_inextensible_inf_meeting [T2Space M] (hcaus : C.IsCausal) (hext : C.CurvesExtend)
    {A B : Opens M} {T : Set M} (hT : C.IsCauchySurface T) (hTA : C.IsCauchySurfaceOn A T)
    (hTB : C.IsCauchySurfaceOn B T) {x : M} (hx : x ∈ A ⊓ B) :
    ∃ (I : Set ℝ) (c : ℝ → M), C.Inextensible (A ⊓ B) I c ∧ x ∈ c '' I ∧ (c '' I ∩ T).Nonempty :=
  exists_inextensible_inf_meeting_of_subsingleton hcaus hext hT.inter_subsingleton hTA hTB hx

/-- **Every connected component of `A ∩ B` meets `T`**: each point of `A ∩ B` is joined inside
`A ∩ B` to a point of `T` by a causal curve (`these.tex:6388–6389`). -/
theorem mem_connectedComponentIn_inf_of_subsingleton [T2Space M] (hcaus : C.IsCausal)
    (hext : C.CurvesExtend) {A B : Opens M} {T : Set M}
    (hT : ∀ (I : Set ℝ) (c : ℝ → M), C.Inextensible ⊤ I c → (c '' I ∩ T).Subsingleton)
    (hTA : C.IsCauchySurfaceOn A T) (hTB : C.IsCauchySurfaceOn B T) {x : M} (hx : x ∈ A ⊓ B) :
    ∃ y ∈ T, y ∈ connectedComponentIn ((A ⊓ B : Opens M) : Set M) x := by
  obtain ⟨I, c, hc, ⟨t₁, ht₁, rfl⟩, ⟨_, ⟨t₂, ht₂, rfl⟩, hT₂⟩⟩ :=
    exists_inextensible_inf_meeting_of_subsingleton hcaus hext hT hTA hTB hx
  have hsub : [[t₁, t₂]] ⊆ I := hc.1.ordConnected.uIcc_subset ht₁ ht₂
  have hcont : ContinuousOn c [[t₁, t₂]] := by
    rw [uIcc]
    exact hc.1.continuousOn_Icc (hsub (by simp [uIcc])) (hsub (by simp [uIcc]))
  have hpre : IsPreconnected (c '' [[t₁, t₂]]) := isPreconnected_uIcc.image c hcont
  have hsubF : c '' [[t₁, t₂]] ⊆ ((A ⊓ B : Opens M) : Set M) := by
    rintro _ ⟨t, ht, rfl⟩; exact hc.1.mem (hsub ht)
  exact ⟨c t₂, hT₂, hpre.subset_connectedComponentIn ⟨t₁, left_mem_uIcc, rfl⟩ hsubF
    ⟨t₂, right_mem_uIcc, rfl⟩⟩

/-- `mem_connectedComponentIn_inf_of_subsingleton` for `T` a Cauchy surface of `M`. -/
theorem mem_connectedComponentIn_inf [T2Space M] (hcaus : C.IsCausal) (hext : C.CurvesExtend)
    {A B : Opens M} {T : Set M} (hT : C.IsCauchySurface T) (hTA : C.IsCauchySurfaceOn A T)
    (hTB : C.IsCauchySurfaceOn B T) {x : M} (hx : x ∈ A ⊓ B) :
    ∃ y ∈ T, y ∈ connectedComponentIn ((A ⊓ B : Opens M) : Set M) x :=
  mem_connectedComponentIn_inf_of_subsingleton hcaus hext hT.inter_subsingleton hTA hTB hx

/-- **`lem:C_ext_connexe`, its strongest topological form**: if `T` is a Cauchy surface of `A` and
of `B` meeting every inextensible curve of `M` at most once, and `T ⊆ P ⊆ A ∩ B` with `P`
preconnected, then `A ∩ B` is preconnected (`M` causal, Hausdorff, curves extending). No causal
arc-connectedness, no connectedness of `T` (only of some `P` between `T` and `A ∩ B` — in
`lem:C_ext_connexe`, `P = φ(M)`), and no claim that `T` is a Cauchy surface of `A ∩ B`. -/
theorem isPreconnected_inf_of_subset [T2Space M] (hcaus : C.IsCausal) (hext : C.CurvesExtend)
    {A B : Opens M} {T P : Set M}
    (hT : ∀ (I : Set ℝ) (c : ℝ → M), C.Inextensible ⊤ I c → (c '' I ∩ T).Subsingleton)
    (hTA : C.IsCauchySurfaceOn A T) (hTB : C.IsCauchySurfaceOn B T) (hTP : T ⊆ P)
    (hPsub : P ⊆ ((A ⊓ B : Opens M) : Set M)) (hP : IsPreconnected P) :
    IsPreconnected ((A ⊓ B : Opens M) : Set M) := by
  rcases P.eq_empty_or_nonempty with hPe | ⟨y₀, hy₀⟩
  · have : ((A ⊓ B : Opens M) : Set M) = ∅ := eq_empty_of_forall_notMem fun x hx => by
      obtain ⟨y, hy, -⟩ := mem_connectedComponentIn_inf_of_subsingleton hcaus hext hT hTA hTB hx
      have := hTP hy; rw [hPe] at this; exact this
    rw [this]; exact isPreconnected_empty
  refine isPreconnected_of_forall y₀ fun x hx => ?_
  obtain ⟨y, hy, hyx⟩ := mem_connectedComponentIn_inf_of_subsingleton hcaus hext hT hTA hTB hx
  refine ⟨connectedComponentIn ((A ⊓ B : Opens M) : Set M) x ∪ P,
    union_subset (connectedComponentIn_subset _ _) hPsub, Or.inr hy₀,
    Or.inl (mem_connectedComponentIn hx), ?_⟩
  exact (isPreconnected_connectedComponentIn).union y hyx (hTP hy) hP

/-- `isPreconnected_inf_of_subset` with `P = T`, `T` a Cauchy surface of `M`. -/
theorem isPreconnected_inf [T2Space M] (hcaus : C.IsCausal) (hext : C.CurvesExtend)
    {A B : Opens M} {T : Set M} (hT : C.IsCauchySurface T) (hTA : C.IsCauchySurfaceOn A T)
    (hTB : C.IsCauchySurfaceOn B T) (hTsub : T ⊆ ((A ⊓ B : Opens M) : Set M))
    (hTc : IsPreconnected T) : IsPreconnected ((A ⊓ B : Opens M) : Set M) :=
  isPreconnected_inf_of_subset hcaus hext hT.inter_subsingleton hTA hTB subset_rfl hTsub hTc

end Convex

end Causality

/-! ### Cauchy inclusions -/

section Inclusion

variable {M : Type u} [TopologicalSpace M] {C : Causality M}

/-- **Design §3 step 3 (convexity): a Cauchy inclusion `A → B` is causally convex in `B`**, `M`
Hausdorff, `B` causally arc-connected with curves extending in `B`; the antisymmetry of `≤_B` is the
global hyperbolicity of `B`. For `B = ⊤`: a Cauchy inclusion into a causal T2 spacetime with
`CurvesExtend` and causal arc-connectedness is causally convex. (Arc-connectedness cannot be dropped
for non-local causalities, `gateLine_cauchyInclusion_not_causallyConvex`; open under Level A.) -/
theorem IsCauchyInclusion.causallyConvexIn [T2Space M] {A B : Opens M}
    (h : IsCauchyInclusion C A B) (hC : C.CausallyArcConnectedOn B) (hext : C.CurvesExtendOn B) :
    C.CausallyConvexIn (A : Set M) B := by
  obtain ⟨hAB, -, ⟨hanti, -⟩, S, hSA, hA, hB⟩ := h
  exact Causality.causallyConvexIn_of_isCauchySurfaceOn hanti hC hext hAB hSA hA hB

/-- Cauchy inclusions compose (`M` Hausdorff). -/
theorem IsCauchyInclusion.trans [T2Space M] {A W B : Opens M} (h₁ : IsCauchyInclusion C A W)
    (h₂ : IsCauchyInclusion C W B) : IsCauchyInclusion C A B := by
  obtain ⟨hAW, hGA, -, S, hSA, hSA', hSW⟩ := h₁
  obtain ⟨hWB, -, hGB, S', hS'W, hS'W', hS'B⟩ := h₂
  exact ⟨hAW.trans hWB, hGA, hGB, S, hSA, hSA',
    Causality.IsCauchySurfaceOn.of_le hGB.1 hWB hS'W (fun _ hx => hAW (hSA hx)) hS'W' hSW hS'B⟩

/-- **If `A` is Cauchy-included in `W` and in `B ⊇ W`, then `W` is Cauchy-included in `B`**
(`M` Hausdorff): the form in which an element of `ℰ` (`IsPgcdCandidate`) sits in `M₁`. -/
theorem IsCauchyInclusion.of_le [T2Space M] {A W B : Opens M} (hW : IsCauchyInclusion C A W)
    (hB : IsCauchyInclusion C A B) (hWB : W ≤ B) : IsCauchyInclusion C W B := by
  obtain ⟨hAW, -, hGW, S', hS'A, hS'A', hS'W⟩ := hW
  obtain ⟨-, -, hGB, S, hSA, hSA', hSB⟩ := hB
  exact ⟨hWB, hGW, hGB, S, fun _ hx => hAW (hSA hx),
    Causality.IsCauchySurfaceOn.of_le hGW.1 hAW hS'A hSA hS'A' hSA' hS'W, hSB⟩

/-- **The union of open sets with a common Cauchy surface `S`, inside an open `B` of which `S` is
a Cauchy surface, has `S` as a Cauchy surface** (curves extending in `B`, `≤_B` antisymmetric,
`M` Hausdorff; **no causal arc-connectedness**). Existence by the component of the curve in one
member (Sbierski, Thm 3.4, step 2); uniqueness because the segment of the curve between two
parameters meeting `S` lies on an inextensible curve of `B` (`CurvesExtendOn B`), which meets the
Cauchy surface `S` of `B` once — Sbierski's "`γ` is also a segment of an inextendible timelike
curve in `M`". No family condition (directed, compatible) is needed: the members are open sets of
one space. -/
theorem Causality.isCauchySurfaceOn_iSup [T2Space M] {ι : Sort*} {B : Opens M} {W : ι → Opens M}
    {S : Set M} (hanti : ∀ ⦃x y : M⦄, C.le B x y → C.le B y x → x = y)
    (hext : C.CurvesExtendOn B) (hWB : ∀ i, W i ≤ B)
    (hSW : ∀ i, C.IsCauchySurfaceOn (W i) S) (hSB : C.IsCauchySurfaceOn B S) :
    C.IsCauchySurfaceOn (⨆ i, W i) S := by
  have hUB : (⨆ i, W i) ≤ B := iSup_le hWB
  have hantiU : ∀ ⦃x y : M⦄, C.le (⨆ i, W i) x y → C.le (⨆ i, W i) y x → x = y :=
    fun x y h h' => hanti (C.le_mono hUB h) (C.le_mono hUB h')
  intro I c hc
  obtain ⟨t₀, ht₀⟩ := hc.1.nonempty
  obtain ⟨i, hi⟩ : ∃ i, c t₀ ∈ W i := Opens.mem_iSup.1 (hc.1.mem ht₀)
  obtain ⟨_, ⟨⟨τ, hτ, rfl⟩, hτS⟩, -⟩ := hSW i _ c
    (Causality.inextensible_ordConnectedComponent_of_le hantiU (le_iSup W i) hc ht₀ hi)
  have hτI : τ ∈ I := (ordConnectedComponent_subset hτ).1
  refine ⟨c τ, ⟨⟨τ, hτI, rfl⟩, hτS⟩, ?_⟩
  rintro _ ⟨⟨σ, hσ, rfl⟩, hσS⟩
  -- the segment `[s, s']` of `c` is a causal curve of `B`; it lies on an inextensible curve of `B`
  have key : ∀ s ∈ I, ∀ s' ∈ I, s ≤ s' → c s ∈ S → c s' ∈ S → c s = c s' := by
    intro s hs s' hs' h hsS hs'S
    obtain ⟨J, c', hc', hsub⟩ := hext c s s' h
      (CurveOn.mono_opens C.isRelFamily_le (hc.1.curve s hs s' hs') hUB)
    exact (hSB J c' hc').unique ⟨hsub ⟨s, ⟨le_rfl, h⟩, rfl⟩, hsS⟩
      ⟨hsub ⟨s', ⟨h, le_rfl⟩, rfl⟩, hs'S⟩
  rcases le_total σ τ with h | h
  · exact key σ hσ τ hτI h hσS hτS
  · exact (key τ hτI σ hσ h hτS hσS).symm

/-- **Design §3 step 3 (the union), with a common Cauchy surface**: a non-empty family of open
sets `W i ≤ B` containing a common Cauchy surface `S` of every `W i` and of the globally hyperbolic
`B` (causally arc-connected, curves extending, `M` Hausdorff) has union `U` with `U → B` a Cauchy
inclusion (Cauchy surface `S`) and `U` causally convex in `B`. Arc-connectedness is used only for
the convexity, hence the GH of `U`; the Cauchy surface alone needs none
(`isCauchySurfaceOn_iSup`). -/
theorem isCauchyInclusion_iSup_of_common [T2Space M] {ι : Sort*} [Nonempty ι] {B : Opens M}
    {W : ι → Opens M} {S : Set M} (hC : C.CausallyArcConnectedOn B) (hext : C.CurvesExtendOn B)
    (hGB : C.GloballyHyperbolicOn B) (hWB : ∀ i, W i ≤ B) (hSsub : ∀ i, S ⊆ W i)
    (hSW : ∀ i, C.IsCauchySurfaceOn (W i) S) (hSB : C.IsCauchySurfaceOn B S) :
    IsCauchyInclusion C (⨆ i, W i) B ∧ C.CausallyConvexIn ((⨆ i, W i : Opens M) : Set M) B ∧
      C.IsCauchySurfaceOn (⨆ i, W i) S := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hUB : (⨆ i, W i) ≤ B := iSup_le hWB
  have hSU := Causality.isCauchySurfaceOn_iSup hGB.1 hext hWB hSW hSB
  have hSU' : S ⊆ ((⨆ i, W i : Opens M) : Set M) := fun _ hx => le_iSup W i₀ (hSsub i₀ hx)
  have hconv : C.CausallyConvexIn ((⨆ i, W i : Opens M) : Set M) B :=
    Causality.causallyConvexIn_of_isCauchySurfaceOn hGB.1 hC hext hUB hSU' hSU hSB
  exact ⟨⟨hUB, Causality.GloballyHyperbolicOn.of_causallyConvexIn hC hGB hconv, hGB, S, hSU', hSU,
    hSB⟩, hconv, hSU⟩

/-- **Design §3 step 3 (the union): the union of Cauchy inclusions is a Cauchy inclusion.**
Inside an open `B` causally arc-connected with curves extending, into which `A` is Cauchy-included,
a non-empty family of Cauchy inclusions `A → W i` (`W i ≤ B`) has union `U` with `A → U` a Cauchy
inclusion, and `U` is causally convex in `B` (arc-connectedness of `B` is used for this convexity
and the GH of `U` only). The Cauchy surfaces of the family are not assumed common: the one of
`A → B` is a Cauchy surface of every `W i` (`IsCauchySurfaceOn.of_le`). An inextensible curve of
`U` meets it by its component in a `W i`, at most once because a segment of it lies on an
inextensible curve of `B` (Sbierski, Thm 3.4, step 2); `U` is then causally convex in `B`
(convexity), hence globally hyperbolic (`GloballyHyperbolicOn.of_causallyConvexIn`). -/
theorem isCauchyInclusion_iSup [T2Space M] {ι : Sort*} [Nonempty ι] {A B : Opens M}
    {W : ι → Opens M} (hC : C.CausallyArcConnectedOn B) (hext : C.CurvesExtendOn B)
    (hB : IsCauchyInclusion C A B) (hW : ∀ i, IsCauchyInclusion C A (W i)) (hWB : ∀ i, W i ≤ B) :
    IsCauchyInclusion C A (⨆ i, W i) ∧ C.CausallyConvexIn ((⨆ i, W i : Opens M) : Set M) B := by
  obtain ⟨-, hGA, hGB, S, hSA, hSA', hSB⟩ := hB
  have hUB : (⨆ i, W i) ≤ B := iSup_le hWB
  have hSW : ∀ i, C.IsCauchySurfaceOn (W i) S := fun i => by
    obtain ⟨hAW, -, hGW, S', hS'A, hS'A', hS'W⟩ := hW i
    exact Causality.IsCauchySurfaceOn.of_le hGW.1 hAW hS'A hSA hS'A' hSA' hS'W
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hAU : A ≤ ⨆ i, W i := (hW i₀).1.trans (le_iSup W i₀)
  have hSU : C.IsCauchySurfaceOn (⨆ i, W i) S :=
    Causality.isCauchySurfaceOn_iSup hGB.1 hext hWB hSW hSB
  have hconv : C.CausallyConvexIn ((⨆ i, W i : Opens M) : Set M) B :=
    Causality.causallyConvexIn_of_isCauchySurfaceOn hGB.1 hC hext hUB
      (fun _ hx => hAU (hSA hx)) hSU hSB
  exact ⟨⟨hAU, hGA, Causality.GloballyHyperbolicOn.of_causallyConvexIn hC hGB hconv, S, hSA,
    hSA', hSU⟩, hconv⟩

/-- The union of a set of Cauchy inclusions, as `sSup`. -/
theorem isCauchyInclusion_sSup [T2Space M] {A B : Opens M} {𝒲 : Set (Opens M)}
    (hne : 𝒲.Nonempty) (hC : C.CausallyArcConnectedOn B) (hext : C.CurvesExtendOn B)
    (hB : IsCauchyInclusion C A B) (hW : ∀ W ∈ 𝒲, IsCauchyInclusion C A W)
    (hWB : ∀ W ∈ 𝒲, W ≤ B) :
    IsCauchyInclusion C A (sSup 𝒲) ∧ C.CausallyConvexIn ((sSup 𝒲 : Opens M) : Set M) B := by
  haveI : Nonempty 𝒲 := hne.to_subtype
  rw [sSup_eq_iSup']
  exact isCauchyInclusion_iSup hC hext hB (fun W => hW W.1 W.2) fun W => hWB W.1 W.2

end Inclusion

/-! ### `lem:C_ext_connexe` for a Cauchy extension -/

section CExtConnexe

variable {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
  {C : Causality M} {D : Causality N} {φ : M → N}

/-- In the setting of `lem:C_ext_connexe`, `φ(Σ)` is a Cauchy surface of `A` for every Cauchy
surface `Σ` of `M` (the relative `lem:Cauchy_plongement_toutes` inside `A`). -/
theorem IsCauchyEmbedding.isCauchySurfaceOn_of_isCauchyInclusion [T2Space N]
    (hφ : IsCauchyEmbedding C D φ) {A : Opens N} (hA : IsCauchyInclusion D hφ.rangeOpens A)
    {S : Set M} (hS : C.IsCauchySurface S) : D.IsCauchySurfaceOn A (φ '' S) := by
  obtain ⟨hRA, -, hGA, S', hS'R, hS'R', hS'A⟩ := hA
  have hTR : φ '' S ⊆ (hφ.rangeOpens : Set N) := by
    rw [IsCauchyEmbedding.coe_rangeOpens]; exact image_subset_range φ S
  exact Causality.IsCauchySurfaceOn.of_le hGA.1 hRA hS'R hTR hS'R'
    ((hφ.isEMorphism.isCauchySurface_iff hφ.injective S).1 hS) hS'A

/-- **`lem:C_ext_connexe`, the curve step** (`ETT.tex:1941–1942`): every point of `A ∩ B` lies on
an inextensible causal curve of `A ∩ B` meeting `φ(Σ)`. Hypotheses: `N` Hausdorff, curves of `N`
extend; no causal arc-connectedness, no Cauchy property of `φ(Σ)` in `A ∩ B`. -/
theorem IsCauchyEmbedding.exists_inextensible_inf [T2Space N] (hφ : IsCauchyEmbedding C D φ)
    {A B : Opens N} (hA : IsCauchyInclusion D hφ.rangeOpens A)
    (hB : IsCauchyInclusion D hφ.rangeOpens B) {S : Set M} (hS : C.IsCauchySurface S)
    (hDext : D.CurvesExtend) {x : N} (hx : x ∈ A ⊓ B) :
    ∃ (I : Set ℝ) (c : ℝ → N), D.Inextensible (A ⊓ B) I c ∧ x ∈ c '' I ∧
      (c '' I ∩ φ '' S).Nonempty :=
  Causality.exists_inextensible_inf_meeting hφ.globallyHyperbolic_target.1 hDext
    (hφ.isCauchySurface_image hS) (hφ.isCauchySurfaceOn_of_isCauchyInclusion hA hS)
    (hφ.isCauchySurfaceOn_of_isCauchyInclusion hB hS) hx

theorem IsCauchyEmbedding.image_subset_inf (hφ : IsCauchyEmbedding C D φ) {A B : Opens N}
    (hA : IsCauchyInclusion D hφ.rangeOpens A) (hB : IsCauchyInclusion D hφ.rangeOpens B)
    (S : Set M) : φ '' S ⊆ ((A ⊓ B : Opens N) : Set N) := by
  rintro _ ⟨x, -, rfl⟩
  have hx : φ x ∈ hφ.rangeOpens := by
    show φ x ∈ (hφ.rangeOpens : Set N); rw [IsCauchyEmbedding.coe_rangeOpens]; exact ⟨x, rfl⟩
  exact ⟨hA.1 hx, hB.1 hx⟩

/-- **`lem:C_ext_connexe`, preconnected form**: `Σ` preconnected ⟹ `A ∩ B` preconnected. -/
theorem IsCauchyEmbedding.isPreconnected_inf [T2Space N] (hφ : IsCauchyEmbedding C D φ)
    {A B : Opens N} (hA : IsCauchyInclusion D hφ.rangeOpens A)
    (hB : IsCauchyInclusion D hφ.rangeOpens B) {S : Set M} (hS : C.IsCauchySurface S)
    (hSc : IsPreconnected S) (hDext : D.CurvesExtend) :
    IsPreconnected ((A ⊓ B : Opens N) : Set N) := by
  have hφc : Continuous φ := by
    have := hφ.isEMorphism.continuousOn; rw [Opens.coe_top, continuousOn_univ] at this
    exact this
  exact Causality.isPreconnected_inf hφ.globallyHyperbolic_target.1 hDext
    (hφ.isCauchySurface_image hS) (hφ.isCauchySurfaceOn_of_isCauchyInclusion hA hS)
    (hφ.isCauchySurfaceOn_of_isCauchyInclusion hB hS) (hφ.image_subset_inf hA hB S)
    (hSc.image φ hφc.continuousOn)

/-- **`lem:C_ext_connexe`, with `Σ` connected**: `A ∩ B` is connected. -/
theorem IsCauchyEmbedding.c_ext_connexe_of_isConnected [T2Space N]
    (hφ : IsCauchyEmbedding C D φ) {A B : Opens N} (hA : IsCauchyInclusion D hφ.rangeOpens A)
    (hB : IsCauchyInclusion D hφ.rangeOpens B) {S : Set M} (hS : C.IsCauchySurface S)
    (hSc : IsConnected S) (hDext : D.CurvesExtend) :
    IsConnected ((A ⊓ B : Opens N) : Set N) := by
  obtain ⟨x, hx⟩ := hSc.nonempty
  exact ⟨⟨φ x, hφ.image_subset_inf hA hB S ⟨x, hx, rfl⟩⟩,
    hφ.isPreconnected_inf hA hB hS hSc.isPreconnected hDext⟩

/-- **`lem:C_ext_connexe`, re-routed** (`ETT.tex:1932`), with the hypotheses of
`SubExtension.c_ext_connexe` less three: `N`'s causal arc-connectedness, the model fact
`hthrough`, and the `sorry`'d `exists_mem_image_inf` it rests on. `M` connected with the
splitting `ψ` of `theo:geroch_sing` (for the connectedness of `Σ`), `φ` a Cauchy extension, `A, B`
open with `φ(M) → A`, `φ(M) → B` Cauchy inclusions, `N` Hausdorff with curves extending: `A ∩ B`
is connected. No `sorry`. -/
theorem IsCauchyEmbedding.c_ext_connexe' [T2Space N] [ConnectedSpace M]
    (hφ : IsCauchyEmbedding C D φ) {A B : Opens N} (hA : IsCauchyInclusion D hφ.rangeOpens A)
    (hB : IsCauchyInclusion D hφ.rangeOpens B) {S : Set M} (hS : C.IsCauchySurface S)
    (ψ : S × ℝ ≃ₜ M) (hDext : D.CurvesExtend) : IsConnected ((A ⊓ B : Opens N) : Set N) :=
  hφ.c_ext_connexe_of_isConnected hA hB hS (isConnected_of_homeomorph ψ) hDext

/-- **`lem:C_ext_connexe`, preconnected form, from `M` alone**: `M` preconnected ⟹ `A ∩ B`
preconnected. No Cauchy surface is required connected and no splitting is used: every point of
`A ∩ B` is joined inside `A ∩ B` to `φ(Σ) ⊆ φ(M)`, and `φ(M) ⊆ A ∩ B` is preconnected. -/
theorem IsCauchyEmbedding.isPreconnected_inf_of_preconnectedSpace [T2Space N]
    [PreconnectedSpace M] (hφ : IsCauchyEmbedding C D φ) {A B : Opens N}
    (hA : IsCauchyInclusion D hφ.rangeOpens A) (hB : IsCauchyInclusion D hφ.rangeOpens B)
    (hDext : D.CurvesExtend) : IsPreconnected ((A ⊓ B : Opens N) : Set N) := by
  have hφc : Continuous φ := by
    have := hφ.isEMorphism.continuousOn; rw [Opens.coe_top, continuousOn_univ] at this
    exact this
  obtain ⟨S, hS, -⟩ := hφ.exists_cauchy
  have hR : range φ ⊆ ((A ⊓ B : Opens N) : Set N) := by
    rw [← image_univ]; exact hφ.image_subset_inf hA hB univ
  exact Causality.isPreconnected_inf_of_subset hφ.globallyHyperbolic_target.1 hDext
    (hφ.isCauchySurface_image hS).inter_subsingleton
    (hφ.isCauchySurfaceOn_of_isCauchyInclusion hA hS)
    (hφ.isCauchySurfaceOn_of_isCauchyInclusion hB hS) (image_subset_range φ S) hR
    (isPreconnected_range hφc)

/-- **`lem:C_ext_connexe`, re-routed, with exactly the paper's topological hypothesis** (`M`
connected; `ETT.tex:1932`): `φ` a Cauchy extension, `A, B` open with `φ(M) → A`, `φ(M) → B`
Cauchy inclusions, `N` Hausdorff with curves extending (kb/0012) ⟹ `A ∩ B` is connected. No
splitting of `M`, no connected Cauchy surface, no causal arc-connectedness, no `hthrough`, and
not the `sorry`'d `exists_mem_image_inf` of `SubExtension.c_ext_connexe`. -/
theorem IsCauchyEmbedding.c_ext_connexe_of_connectedSpace [T2Space N] [ConnectedSpace M]
    (hφ : IsCauchyEmbedding C D φ) {A B : Opens N} (hA : IsCauchyInclusion D hφ.rangeOpens A)
    (hB : IsCauchyInclusion D hφ.rangeOpens B) (hDext : D.CurvesExtend) :
    IsConnected ((A ⊓ B : Opens N) : Set N) := by
  obtain ⟨x⟩ := (inferInstance : Nonempty M)
  have hR : range φ ⊆ ((A ⊓ B : Opens N) : Set N) := by
    rw [← image_univ]; exact hφ.image_subset_inf hA hB univ
  exact ⟨⟨φ x, hR ⟨x, rfl⟩⟩, hφ.isPreconnected_inf_of_preconnectedSpace hA hB hDext⟩

/-- **The middle step of `lem:C_ext_connexe` reduced to its existence half**: `φ(Σ)` is a Cauchy
surface of `A ∩ B` iff every inextensible curve of `A ∩ B` meets it; that it meets each one at
most once is proved (`inter_subsingleton_of_curvesExtend`; `N` with curves extending). -/
theorem IsCauchyEmbedding.isCauchySurfaceOn_inf_iff [T2Space N] (hφ : IsCauchyEmbedding C D φ)
    {A B : Opens N} {S : Set M} (hS : C.IsCauchySurface S) (hDext : D.CurvesExtend) :
    D.IsCauchySurfaceOn (A ⊓ B) (φ '' S) ↔
      ∀ (I : Set ℝ) (c : ℝ → N), D.Inextensible (A ⊓ B) I c → (c '' I ∩ φ '' S).Nonempty :=
  Causality.isCauchySurfaceOn_iff_of_curvesExtend hDext
    (hφ.isCauchySurface_image hS).inter_subsingleton _

/-- **`A ∩ B` is causally convex in `N`, hence globally hyperbolic**, in the setting of
`lem:C_ext_connexe` with `N` causally arc-connected: `A` and `B` are Cauchy-included in `N`
(`IsCauchyInclusion.of_le`), hence causally convex (§3 step 3, convexity). With
`exists_inextensible_inf`, the one assertion of "`M → A ∩ B` is a Cauchy embedding" this file leaves
open is that every inextensible curve of `A ∩ B` meets `φ(Σ)`. -/
theorem IsCauchyEmbedding.inf_causallyConvexIn [T2Space N] (hφ : IsCauchyEmbedding C D φ)
    {A B : Opens N} (hA : IsCauchyInclusion D hφ.rangeOpens A)
    (hB : IsCauchyInclusion D hφ.rangeOpens B) (hDac : D.CausallyArcConnected)
    (hDext : D.CurvesExtend) :
    D.CausallyConvexIn ((A ⊓ B : Opens N) : Set N) ⊤ ∧ D.GloballyHyperbolicOn (A ⊓ B) := by
  have hRtop : IsCauchyInclusion D hφ.rangeOpens ⊤ := by
    obtain ⟨S, hS, hS'⟩ := hφ.exists_cauchy
    refine ⟨le_top, hA.2.1, hφ.globallyHyperbolic_target, φ '' S, ?_,
      (hφ.isEMorphism.isCauchySurface_iff hφ.injective S).1 hS, hS'⟩
    rw [IsCauchyEmbedding.coe_rangeOpens]; exact image_subset_range φ S
  have hAc := (hA.of_le hRtop le_top).causallyConvexIn hDac hDext
  have hBc := (hB.of_le hRtop le_top).causallyConvexIn hDac hDext
  have hconv : D.CausallyConvexIn ((A ⊓ B : Opens N) : Set N) ⊤ :=
    ⟨fun _ _ => trivial, fun p hp q hq z hz =>
      ⟨hAc.2 p hp.1 q hq.1 hz, hBc.2 p hp.2 q hq.2 hz⟩⟩
  exact ⟨hconv, Causality.GloballyHyperbolicOn.of_causallyConvexIn hDac
    hφ.globallyHyperbolic_target hconv⟩

end CExtConnexe

/-! ### Witnesses on the timelike line (kb/0011) -/

/-- Curves of every open set of the timelike line extend (the time function `id`). -/
theorem timelikeLine_curvesExtendOn (W : Opens ℝ) : timelikeLine.CurvesExtendOn W :=
  Causality.curvesExtendOn_of_timeFunction continuous_id
    (fun _ _ h hne => lt_of_le_of_ne (timelikeLine_le.1 h).1 hne) W

/-- **The hypotheses of §3 step 3 (convexity, union) and of §3 step 1 (the re-routed
`lem:C_ext_connexe`) are jointly satisfiable**: on the timelike line, `ℝ` is Cauchy-included in
itself, causally arc-connected with curves extending in every open set, Hausdorff and causal, `{0}`
connected and Cauchy; the conclusions follow (the union of the constant family `ℝ`, the
connectedness of `ℝ ∩ ℝ`). -/
theorem timelikeLine_causalConvex_hypotheses :
    IsCauchyInclusion timelikeLine ⊤ ⊤ ∧ timelikeLine.CausallyArcConnected ∧
      (∀ W : Opens ℝ, timelikeLine.CurvesExtendOn W) ∧ timelikeLine.IsCausal ∧
      IsConnected ({0} : Set ℝ) ∧ timelikeLine.IsCauchySurface {0} ∧
      timelikeLine.CausallyConvexIn ((⊤ : Opens ℝ) : Set ℝ) ⊤ ∧
      IsCauchyInclusion timelikeLine ⊤ (⨆ _ : Unit, ⊤) ∧
      IsConnected (((⊤ : Opens ℝ) ⊓ ⊤ : Opens ℝ) : Set ℝ) := by
  have h₁ := timelikeLine_isCauchyInclusion_top
  have hRtop : timelikeLine_isCauchyEmbedding_id.rangeOpens = ⊤ := timelikeLine_rangeOpens_id
  refine ⟨h₁, timelikeLine_causallyArcConnected, timelikeLine_curvesExtendOn, timelikeLine_isCausal,
    isConnected_singleton, timelikeLine_isCauchySurface_zero,
    h₁.causallyConvexIn timelikeLine_causallyArcConnected (timelikeLine_curvesExtendOn ⊤),
    (isCauchyInclusion_iSup timelikeLine_causallyArcConnected (timelikeLine_curvesExtendOn ⊤) h₁
      (fun _ => h₁) fun _ => le_rfl).1, ?_⟩
  have hA : IsCauchyInclusion timelikeLine timelikeLine_isCauchyEmbedding_id.rangeOpens ⊤ := by
    rw [hRtop]; exact h₁
  exact timelikeLine_isCauchyEmbedding_id.c_ext_connexe_of_isConnected hA hA
    timelikeLine_isCauchySurface_zero isConnected_singleton timelikeLine_curvesExtend


/-! ### Witness: causal arc-connectedness is needed for convexity among non-local causalities
(kb/0011, kb/0019) -/

section GateLine

open Sum

/-- The gated line. -/
def gateLine : Causality (ℝ ⊕ Unit) where
  le U x y := match x, y with
    | inl a, inl b => a ≤ b ∧ Icc a b ⊆ inl ⁻¹' (U : Set (ℝ ⊕ Unit))
    | inr _, inr _ => (inr () : ℝ ⊕ Unit) ∈ U
    | inl a, inr _ => a ≤ 10 ∧ (inl a : ℝ ⊕ Unit) ∈ U ∧ (inr () : ℝ ⊕ Unit) ∈ U ∧
        (inl 5 : ℝ ⊕ Unit) ∈ U
    | inr _, inl _ => False
  lt U x y := match x, y with
    | inl a, inl b => a < b ∧ Icc a b ⊆ inl ⁻¹' (U : Set (ℝ ⊕ Unit))
    | _, _ => False
  le_mem_left := by
    intro U x y h
    rcases x with a | ⟨⟩ <;> rcases y with b | ⟨⟩
    · exact h.2 (left_mem_Icc.2 h.1)
    · exact h.2.1
    · exact h.elim
    · exact h
  le_mem_right := by
    intro U x y h
    rcases x with a | ⟨⟩ <;> rcases y with b | ⟨⟩
    · exact h.2 (right_mem_Icc.2 h.1)
    · exact h.2.2.1
    · exact h.elim
    · exact h
  lt_mem_left := by
    intro U x y h
    rcases x with a | ⟨⟩ <;> rcases y with b | ⟨⟩
    · exact h.2 (left_mem_Icc.2 h.1.le)
    all_goals exact h.elim
  lt_mem_right := by
    intro U x y h
    rcases x with a | ⟨⟩ <;> rcases y with b | ⟨⟩
    · exact h.2 (right_mem_Icc.2 h.1.le)
    all_goals exact h.elim
  le_refl := by
    intro U x hx
    rcases x with a | ⟨⟩
    · exact ⟨le_rfl, fun z hz => by rw [Icc_self] at hz; rw [mem_singleton_iff.1 hz]; exact hx⟩
    · exact hx
  le_trans := by
    intro U x y z h₁ h₂
    rcases x with a | ⟨⟩ <;> rcases y with b | ⟨⟩ <;> rcases z with c | ⟨⟩
    · exact ⟨h₁.1.trans h₂.1, fun w hw => by
        rcases le_total w b with h | h
        · exact h₁.2 ⟨hw.1, h⟩
        · exact h₂.2 ⟨h, hw.2⟩⟩
    · exact ⟨h₁.1.trans h₂.1, h₁.2 (left_mem_Icc.2 h₁.1), h₂.2.2.1, h₂.2.2.2⟩
    · exact h₂.elim
    · exact h₁
    · exact h₁.elim
    · exact h₁.elim
    · exact h₂.elim
    · exact h₁
  lt_trans := by
    intro U x y z h₁ h₂
    rcases x with a | ⟨⟩ <;> rcases y with b | ⟨⟩ <;> rcases z with c | ⟨⟩
    · exact ⟨h₁.1.trans h₂.1, fun w hw => by
        rcases le_total w b with h | h
        · exact h₁.2 ⟨hw.1, h⟩
        · exact h₂.2 ⟨h, hw.2⟩⟩
    all_goals first | exact h₁.elim | exact h₂.elim
  le_mono := by
    intro U V hVU x y h
    rcases x with a | ⟨⟩ <;> rcases y with b | ⟨⟩
    · exact ⟨h.1, fun z hz => hVU (h.2 hz)⟩
    · exact ⟨h.1, hVU h.2.1, hVU h.2.2.1, hVU h.2.2.2⟩
    · exact h.elim
    · exact hVU h
  lt_mono := by
    intro U V hVU x y h
    rcases x with a | ⟨⟩ <;> rcases y with b | ⟨⟩
    · exact ⟨h.1, fun z hz => hVU (h.2 hz)⟩
    all_goals exact h.elim
  le_of_lt := by
    intro U x y h
    rcases x with a | ⟨⟩ <;> rcases y with b | ⟨⟩
    · exact ⟨h.1.le, h.2⟩
    all_goals exact h.elim
  isOpen_lt_right := by
    intro U x
    rw [isOpen_sum_iff]
    rcases x with a | ⟨⟩
    · refine ⟨isOpen_setOf_lt_and_Icc_subset_right
        ⟨inl ⁻¹' (U : Set (ℝ ⊕ Unit)), U.isOpen.preimage continuous_inl⟩ a, ?_⟩
      convert isOpen_empty
      ext ⟨⟩; simp
    · constructor
      · convert isOpen_empty; ext b; simp
      · convert isOpen_empty; ext ⟨⟩; simp
  isOpen_lt_left := by
    intro U x
    rw [isOpen_sum_iff]
    rcases x with a | ⟨⟩
    · refine ⟨isOpen_setOf_lt_and_Icc_subset_left
        ⟨inl ⁻¹' (U : Set (ℝ ⊕ Unit)), U.isOpen.preimage continuous_inl⟩ a, ?_⟩
      convert isOpen_empty
      ext ⟨⟩; simp
    · constructor
      · convert isOpen_empty; ext b; simp
      · convert isOpen_empty; ext ⟨⟩; simp

variable {U : Opens (ℝ ⊕ Unit)} {a b : ℝ} {u v : Unit}

@[simp] theorem gateLine_le_inl_inl :
    gateLine.le U (inl a) (inl b) ↔ a ≤ b ∧ Icc a b ⊆ inl ⁻¹' (U : Set (ℝ ⊕ Unit)) := Iff.rfl

@[simp] theorem gateLine_le_inl_inr :
    gateLine.le U (inl a) (inr u) ↔ a ≤ 10 ∧ (inl a : ℝ ⊕ Unit) ∈ U ∧ (inr () : ℝ ⊕ Unit) ∈ U ∧
      (inl 5 : ℝ ⊕ Unit) ∈ U := Iff.rfl

@[simp] theorem gateLine_le_inr_inl : ¬ gateLine.le U (inr u) (inl b) := id

@[simp] theorem gateLine_le_inr_inr :
    gateLine.le U (inr u) (inr v) ↔ (inr () : ℝ ⊕ Unit) ∈ U := Iff.rfl

/-- `≤_U` is antisymmetric on every open set of the gated line. -/
theorem gateLine_le_antisymm {x y : ℝ ⊕ Unit} (h₁ : gateLine.le U x y) (h₂ : gateLine.le U y x) :
    x = y := by
  rcases x with a | ⟨⟩ <;> rcases y with b | ⟨⟩
  · exact congrArg inl (le_antisymm h₁.1 h₂.1)
  · exact h₂.elim
  · exact h₁.elim
  · rfl

/-- The gated line is causal. -/
theorem gateLine_isCausal : gateLine.IsCausal := fun _ _ h₁ h₂ => gateLine_le_antisymm h₁ h₂

/-- A diamond of `U` between two points of the line is the segment between them. -/
theorem gateLine_diamond_inl_inl (h : gateLine.le U (inl a) (inl b)) :
    gateLine.diamond U (inl a) (inl b) = inl '' Icc a b := by
  ext z
  rw [Causality.mem_diamond]
  rcases z with c | ⟨⟩
  · simp only [gateLine_le_inl_inl, mem_image, inl.injEq, exists_eq_right, mem_Icc]
    constructor
    · rintro ⟨⟨h1, -⟩, h2, -⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, fun w hw => h.2 ⟨hw.1, hw.2.trans h2⟩⟩, h2, fun w hw => h.2 ⟨h1.trans hw.1, hw.2⟩⟩
  · simp

/-- **The gated line is globally hyperbolic on `⊤` and on every open set missing the gate.** -/
theorem gateLine_globallyHyperbolicOn (hU : U = ⊤ ∨ (inl 5 : ℝ ⊕ Unit) ∉ U) :
    gateLine.GloballyHyperbolicOn U := by
  refine ⟨fun x y h₁ h₂ => gateLine_le_antisymm h₁ h₂, fun p q => ?_⟩
  by_cases hpq : gateLine.le U p q
  swap
  · have : gateLine.diamond U p q = ∅ := eq_empty_of_forall_notMem fun z hz =>
      hpq (gateLine.le_trans (Causality.mem_diamond.1 hz).1 (Causality.mem_diamond.1 hz).2)
    rw [this]; exact isCompact_empty
  rcases p with a | ⟨⟩ <;> rcases q with b | ⟨⟩
  · rw [gateLine_diamond_inl_inl hpq]; exact isCompact_Icc.image continuous_inl
  · have hU' : U = ⊤ := hU.resolve_right fun h => h hpq.2.2.2
    subst hU'
    have : gateLine.diamond ⊤ (inl a) (inr ()) = inl '' Icc a 10 ∪ {inr ()} := by
      ext z
      rw [Causality.mem_diamond]
      rcases z with c | ⟨⟩
      · simp [Opens.coe_top]
      · simp only [mem_union, mem_image, reduceCtorEq, and_false, exists_false,
          mem_singleton_iff, or_true, iff_true]
        exact ⟨by simpa using hpq, by simp⟩
    rw [this]; exact (isCompact_Icc.image continuous_inl).union isCompact_singleton
  · exact hpq.elim
  · have : gateLine.diamond U (inr ()) (inr ()) = {inr ()} := by
      ext z
      rw [Causality.mem_diamond]
      rcases z with c | ⟨⟩
      · simp
      · simp only [gateLine_le_inr_inr, mem_singleton_iff, and_self, iff_true]; exact hpq
    rw [this]; exact isCompact_singleton

/-- Curves extend on the gated line: `inl a ↦ a`, `⋆ ↦ 11` is a continuous time function. -/
theorem gateLine_curvesExtend : gateLine.CurvesExtend := by
  rw [← Causality.curvesExtendOn_top (C := gateLine)]
  refine Causality.curvesExtendOn_of_timeFunction (T := Sum.elim id fun _ => (11 : ℝ))
    (continuous_id.sumElim continuous_const) (fun x y h hne => ?_) ⊤
  rcases x with a | ⟨⟩ <;> rcases y with b | ⟨⟩
  · exact lt_of_le_of_ne h.1 fun h' => hne (congrArg inl h')
  · simp only [elim_inl, id_eq, elim_inr]; linarith [h.1]
  · exact h.elim
  · exact (hne rfl).elim


/-- A causal curve of the gated line stays on the line or at `⋆`: `Sum.isLeft ∘ c` is continuous
on every segment of the (preconnected) interval, into the discrete `Bool`. -/
theorem gateLine_curve_cases {W : Opens (ℝ ⊕ Unit)} {I : Set ℝ} {c : ℝ → ℝ ⊕ Unit}
    (hc : gateLine.CausalCurveIn W I c) :
    (∀ t ∈ I, (c t).isLeft = true) ∨ ∀ t ∈ I, c t = inr () := by
  obtain ⟨t₀, ht₀⟩ := hc.nonempty
  have hsame : ∀ t ∈ I, (c t).isLeft = (c t₀).isLeft := by
    intro t ht
    have hsub : [[t₀, t]] ⊆ I := hc.ordConnected.uIcc_subset ht₀ ht
    have hcont : ContinuousOn c [[t₀, t]] := by
      rw [uIcc]
      exact hc.continuousOn_Icc (hsub (by simp [uIcc])) (hsub (by simp [uIcc]))
    have hpre : IsPreconnected ((isLeft ∘ c) '' [[t₀, t]]) :=
      isPreconnected_uIcc.image _ (continuous_isLeft.comp_continuousOn hcont)
    exact hpre.subsingleton ⟨t, right_mem_uIcc, rfl⟩ ⟨t₀, left_mem_uIcc, rfl⟩
  cases h₀ : (c t₀).isLeft
  · refine Or.inr fun t ht => ?_
    have h := hsame t ht
    rw [h₀] at h
    rcases hct : c t with a | ⟨⟩
    · rw [hct] at h; exact absurd h (by simp)
    · rfl
  · exact Or.inl fun t ht => (hsame t ht).trans h₀

/-- **An inextensible curve of `W` inside an open `W' ≤ W` is inextensible in `W'`** (any
causality): its strict extensions in `W'` are strict extensions in `W`. -/
theorem Causality.inextensible_of_le_of_mem {M : Type u} [TopologicalSpace M] {C : Causality M}
    {W W' : Opens M} {I : Set ℝ} {c : ℝ → M} (hW : W' ≤ W) (hc : C.Inextensible W I c)
    (hmem : ∀ t ∈ I, c t ∈ W') : C.Inextensible W' I c := by
  refine ⟨⟨hc.1.nonempty, hc.1.ordConnected, fun a ha b hb => CurveOn.restrict
    (hc.1.curve a ha b hb) le_rfl le_rfl hW fun t ht => hmem t (hc.1.ordConnected.out ha hb ht)⟩,
    fun ⟨I', c', hS⟩ => hc.2 ⟨I', c', ⟨⟨hS.curve.nonempty, hS.curve.ordConnected,
      fun a ha b hb => CurveOn.mono_opens C.isRelFamily_le (hS.curve.curve a ha b hb) hW⟩,
      hS.reparam, hS.grows⟩⟩⟩

/-- **`inl ∘ g` is an abstract morphism from the timelike line to the gated line**, for `g`
strictly increasing, continuous and open. -/
theorem gateLine_isEMorphism_inl_comp {g : ℝ → ℝ} (hgm : StrictMono g) (hgc : Continuous g)
    (hgo : IsOpenMap g) : IsEMorphism timelikeLine gateLine (inl ∘ g) := by
  have himg : ∀ {x y : ℝ}, x ≤ y → g '' Icc x y = Icc (g x) (g y) := fun {x y} hxy =>
    Subset.antisymm (image_subset_iff.2 fun w hw => ⟨hgm.monotone hw.1, hgm.monotone hw.2⟩)
      (intermediate_value_Icc hxy hgc.continuousOn)
  refine
    { continuousOn := (continuous_inl.comp hgc).continuousOn
      isOpen_image := fun V _ => (isOpenMap_inl.comp hgo) _ V.isOpen
      map_le := fun V U _ hmaps x y hxy => ?_
      map_lt := fun V U _ hmaps x y hxy => ?_
      locally := fun x _ => ⟨⊤, le_rfl, trivial, (inl_injective.comp hgm.injective).injOn,
        fun V' _ U hU y _ z _ => ?_⟩ }
  · obtain ⟨hxy, hsub⟩ := timelikeLine_le.1 hxy
    refine ⟨hgm.monotone hxy, ?_⟩
    rw [← himg hxy]
    rintro _ ⟨w, hw, rfl⟩
    exact hmaps (hsub hw)
  · obtain ⟨hxy, hsub⟩ := timelikeLine_lt.1 hxy
    refine ⟨hgm hxy, ?_⟩
    rw [← himg hxy.le]
    rintro _ ⟨w, hw, rfl⟩
    exact hmaps (hsub hw)
  · have hpre : inl ⁻¹' (U : Set (ℝ ⊕ Unit)) = g '' V' := by
      rw [hU, image_comp, preimage_image_eq _ inl_injective]
    have hsub : y ≤ z → (Icc y z ⊆ (V' : Set ℝ) ↔ Icc (g y) (g z) ⊆ inl ⁻¹' (U : Set (ℝ ⊕ Unit))) :=
      fun h => by rw [hpre, ← himg h, image_subset_image_iff hgm.injective]
    constructor
    · show (y ≤ z ∧ Icc y z ⊆ (V' : Set ℝ)) ↔ (g y ≤ g z ∧ _)
      rw [hgm.le_iff_le]
      exact and_congr_right hsub
    · show (y < z ∧ Icc y z ⊆ (V' : Set ℝ)) ↔ (g y < g z ∧ _)
      rw [hgm.lt_iff_lt]
      exact and_congr_right fun h => hsub h.le

/-- The part of the gated line over the image of an open map `g : ℝ → ℝ`, as an open set. -/
def gateLineOpens {g : ℝ → ℝ} (hgo : IsOpenMap g) : Opens (ℝ ⊕ Unit) :=
  ⟨(inl ∘ g) '' univ, (isOpenMap_inl.comp hgo) _ isOpen_univ⟩

/-- The isolated point `⋆` of the gated line, as an open set. -/
def gateStar : Opens (ℝ ⊕ Unit) := ⟨range inr, isOpenMap_inr.isOpen_range⟩

/-- **Cauchy surfaces of the line transported to the gated line**: `{inl (g s)}` is a Cauchy
surface of the part of the line over `g(ℝ)` when `{s}` is one of the timelike line. -/
theorem gateLine_isCauchySurfaceOn_lineOpens {g : ℝ → ℝ} (hgm : StrictMono g) (hgc : Continuous g)
    (hgo : IsOpenMap g) {s : ℝ} (hs : timelikeLine.IsCauchySurface {s}) :
    gateLine.IsCauchySurfaceOn (gateLineOpens hgo) {inl (g s)} := by
  have h := IsEMorphismOn.isCauchySurfaceOn_image_iff (gateLine_isEMorphism_inl_comp hgm hgc hgo)
    (inl_injective.comp hgm.injective).injOn (V := ⊤) le_rfl (U := gateLineOpens hgo)
    (by simp [gateLineOpens]) (S := {s}) (subset_univ _)
  rw [image_singleton] at h
  exact h.1 hs

/-- **A Cauchy surface of the gated line, component by component**: if the line part `L` of an
open `O` has the Cauchy surface `{p}`, then `{p, ⋆}` is a Cauchy surface of `O`. -/
theorem gateLine_isCauchySurfaceOn_of_line {O L : Opens (ℝ ⊕ Unit)}
    (hL : (L : Set (ℝ ⊕ Unit)) = (O : Set (ℝ ⊕ Unit)) ∩ range inl) {p : ℝ ⊕ Unit}
    (hLC : gateLine.IsCauchySurfaceOn L {p}) :
    gateLine.IsCauchySurfaceOn O {p, inr ()} := by
  have hLO : L ≤ O := fun x hx => by
    have h : x ∈ (L : Set (ℝ ⊕ Unit)) := hx
    rw [hL] at h; exact h.1
  intro I c hc
  rcases gateLine_curve_cases hc.1 with hl | hr
  · have hmem : ∀ t ∈ I, c t ∈ L := fun t ht => by
      show c t ∈ (L : Set (ℝ ⊕ Unit))
      rw [hL]
      refine ⟨hc.1.mem ht, ?_⟩
      have h := hl t ht
      rcases hct : c t with a | ⟨⟩
      · exact ⟨a, rfl⟩
      · rw [hct] at h; exact absurd h (by simp)
    obtain ⟨x, ⟨hx1, hx2⟩, huniq⟩ := hLC I c (Causality.inextensible_of_le_of_mem hLO hc hmem)
    refine ⟨x, ⟨hx1, Or.inl hx2⟩, fun y hy => ?_⟩
    obtain ⟨hy1, hy2⟩ := hy
    rcases hy2 with hy2 | hy2
    · exact huniq y ⟨hy1, hy2⟩
    · obtain ⟨t, ht, rfl⟩ := hy1
      have h := hl t ht
      rw [mem_singleton_iff.1 hy2] at h
      exact absurd h (by simp)
  · obtain ⟨t₀, ht₀⟩ := hc.1.nonempty
    refine ⟨inr (), ⟨⟨t₀, ht₀, hr t₀ ht₀⟩, Or.inr rfl⟩, ?_⟩
    rintro _ ⟨⟨t, ht, rfl⟩, -⟩
    exact hr t ht

/-- The order isomorphism `ℝ ≃ ]-1, 1[` of mathlib, as a map `ℝ → ℝ`. -/
noncomputable def gateArc (x : ℝ) : ℝ := (orderIsoIooNegOneOne ℝ x : ℝ)

theorem gateArc_strictMono : StrictMono gateArc := fun _ _ h =>
  Subtype.coe_lt_coe.2 ((orderIsoIooNegOneOne ℝ).strictMono h)

theorem gateArc_continuous : Continuous gateArc :=
  continuous_subtype_val.comp (orderIsoIooNegOneOne ℝ).continuous

theorem gateArc_isOpenMap : IsOpenMap gateArc :=
  isOpen_Ioo.isOpenMap_subtype_val.comp (orderIsoIooNegOneOne ℝ).toHomeomorph.isOpenMap

theorem gateArc_lt_one (x : ℝ) : gateArc x < 1 := (orderIsoIooNegOneOne ℝ x).2.2

/-- **The open set `A` of the witness**: the arc `]-1, 1[` of the line, and `⋆`. It misses the
gate `5`. -/
noncomputable def gateA : Opens (ℝ ⊕ Unit) := gateLineOpens gateArc_isOpenMap ⊔ gateStar

theorem gate_notMem_gateA : (inl 5 : ℝ ⊕ Unit) ∉ gateA := by
  rintro (⟨w, -, hw⟩ | ⟨u, hu⟩)
  · have h : gateArc w = 5 := inl_injective hw
    linarith [gateArc_lt_one w]
  · exact inr_ne_inl hu

/-- **The gated line lies outside the CBG framework's Level A**: it is not absolutely minimal (on
`⊤`), i.e. it is a non-local causality. Over the cover `{line, ⋆}`, a chain of localised relations
starting on the line stays on the line, so `0 ≤ ⋆` is not generated. Whether absolute minimality
(the design's standing assumption on `Geometry.causality`) can replace causal arc-connectedness in
§3 step 3 (convexity) is left open. -/
theorem gateLine_not_absolutelyMinimalOn :
    ¬ Precausality.AbsolutelyMinimalOn gateLine.toPrecausality ⊤ := by
  intro h
  have hcov : ∀ x ∈ (⊤ : Opens (ℝ ⊕ Unit)),
      ∃ O ∈ ({gateLineOpens IsOpenMap.id, gateStar} : Set (Opens (ℝ ⊕ Unit))), x ∈ O := by
    rintro (a | ⟨⟩) -
    · exact ⟨_, Or.inl rfl, ⟨a, trivial, rfl⟩⟩
    · exact ⟨_, Or.inr rfl, ⟨(), rfl⟩⟩
  have hrel : gateLine.le ⊤ (inl 0 : ℝ ⊕ Unit) (inr ()) :=
    ⟨by norm_num, trivial, trivial, trivial⟩
  have hgen := ((h _ hcov ⊤ le_rfl (inl 0) (inr ())).1 hrel)
  -- a localised step from a point of the line lands on the line
  have hstep : ∀ a b : ℝ ⊕ Unit, (∃ O ∈ ({gateLineOpens IsOpenMap.id, gateStar} :
      Set (Opens (ℝ ⊕ Unit))), gateLine.le (⊤ ⊓ O) a b) → a.isLeft = true → b.isLeft = true := by
    rintro a b ⟨O, hO, hab⟩ ha
    have haO : a ∈ O := ((inf_le_right : ⊤ ⊓ O ≤ O) (gateLine.le_mem_left hab))
    have hbO : b ∈ O := ((inf_le_right : ⊤ ⊓ O ≤ O) (gateLine.le_mem_right hab))
    rcases hO with rfl | rfl
    · obtain ⟨w, -, rfl⟩ := hbO; rfl
    · obtain ⟨u, rfl⟩ := haO; exact absurd ha (by simp)
  have hend : ∀ b, Relation.TransGen (fun a b => ∃ O ∈ ({gateLineOpens IsOpenMap.id, gateStar} :
      Set (Opens (ℝ ⊕ Unit))), gateLine.le (⊤ ⊓ O) a b) (inl 0) b → b.isLeft = true := by
    intro b hb
    induction hb with
    | single h => exact hstep _ _ h rfl
    | tail _ h ih => exact hstep _ _ h ih
  exact absurd (hend _ hgen) (by simp)

/-- **Witness (kb/0011, kb/0019): among non-local causalities, causal arc-connectedness cannot be
dropped from §3 step 3 (convexity).** On the gated line — the timelike line plus an isolated
point `⋆`, with `a ≤ ⋆` for `a ≤ 10` in every open set containing `a`, `⋆` and the gate `5` — the
open set `A = ]-1, 1[ ∪ {⋆}` is Cauchy-included in the whole space with the common Cauchy surface
`{g 0, ⋆}`; the space is causal, Hausdorff, with curves extending (a continuous time function),
and globally hyperbolic; yet `A` is **not** causally convex: `g 0 ≤ 5 ≤ ⋆` with `5 ∉ A`. The
relation `5 ≤ ⋆` is realised by no causal curve, so the gated line is not causally
arc-connected; and `0 ≤ ⋆` is realised by no chain of localised relations, so it is **not
absolutely minimal** (last conjunct, `gateLine_not_absolutelyMinimalOn`). **Scope**: "a Cauchy
inclusion into a causal T2 spacetime with `CurvesExtend` is causally convex" (design §3 step 3)
is false without arc-connectedness **for non-absolutely-minimal (non-local) causalities**; under
Level A (absolutely minimal on every open), the setting the design concerns, it is **open**. -/
theorem gateLine_cauchyInclusion_not_causallyConvex :
    gateLine.IsCausal ∧ gateLine.CurvesExtend ∧ IsCauchyInclusion gateLine gateA ⊤ ∧
      ¬ gateLine.CausallyConvexIn (gateA : Set (ℝ ⊕ Unit)) ⊤ ∧
      ¬ gateLine.CausallyArcConnected ∧
      ¬ Precausality.AbsolutelyMinimalOn gateLine.toPrecausality ⊤ := by
  have hstarA : (inr () : ℝ ⊕ Unit) ∈ gateA := Or.inr ⟨(), rfl⟩
  have hpA : (inl (gateArc 0) : ℝ ⊕ Unit) ∈ gateA := Or.inl ⟨0, trivial, rfl⟩
  have hLA : (gateLineOpens gateArc_isOpenMap : Set (ℝ ⊕ Unit)) =
      (gateA : Set (ℝ ⊕ Unit)) ∩ range inl := by
    ext x
    constructor
    · rintro ⟨w, -, rfl⟩; exact ⟨Or.inl ⟨w, trivial, rfl⟩, ⟨_, rfl⟩⟩
    · rintro ⟨hx | ⟨u, hu⟩, ⟨a, ha⟩⟩
      · exact hx
      · exact absurd (ha.trans hu.symm) inl_ne_inr
  have hLtop : (gateLineOpens IsOpenMap.id : Set (ℝ ⊕ Unit)) =
      ((⊤ : Opens (ℝ ⊕ Unit)) : Set (ℝ ⊕ Unit)) ∩ range inl := by
    ext x
    simp only [gateLineOpens, Opens.coe_mk, Opens.coe_top, univ_inter, image_univ, comp_id]
  have hCA : gateLine.IsCauchySurfaceOn gateA {inl (gateArc 0), inr ()} :=
    gateLine_isCauchySurfaceOn_of_line hLA
      (gateLine_isCauchySurfaceOn_lineOpens gateArc_strictMono gateArc_continuous gateArc_isOpenMap
        timelikeLine_isCauchySurface_zero)
  have hCtop : gateLine.IsCauchySurfaceOn ⊤ {inl (gateArc 0), inr ()} :=
    gateLine_isCauchySurfaceOn_of_line hLtop
      (gateLine_isCauchySurfaceOn_lineOpens strictMono_id continuous_id IsOpenMap.id
        (timelikeLine_isCauchySurface_singleton (gateArc 0)))
  have hincl : IsCauchyInclusion gateLine gateA ⊤ :=
    ⟨le_top, gateLine_globallyHyperbolicOn (Or.inr gate_notMem_gateA),
      gateLine_globallyHyperbolicOn (Or.inl rfl), _,
      insert_subset hpA (singleton_subset_iff.2 hstarA), hCA, hCtop⟩
  have hnc : ¬ gateLine.CausallyConvexIn (gateA : Set (ℝ ⊕ Unit)) ⊤ := fun h =>
    gate_notMem_gateA (h.2 _ hpA _ hstarA (Causality.mem_diamond.2
      ⟨⟨by linarith [gateArc_lt_one 0], fun _ _ => trivial⟩,
        ⟨by norm_num, trivial, trivial, trivial⟩⟩))
  refine ⟨gateLine_isCausal, gateLine_curvesExtend, hincl, hnc, fun hac => hnc ?_,
    gateLine_not_absolutelyMinimalOn⟩
  exact hincl.causallyConvexIn hac ((Causality.curvesExtendOn_top (C := gateLine)).2
    gateLine_curvesExtend)

end GateLine

/-! ### Witness: the hypotheses with `A` a proper open subset of `B` (kb/0011) -/

/-- Every open set of the timelike line is globally hyperbolic. -/
theorem timelikeLine_globallyHyperbolicOn (U : Opens ℝ) : timelikeLine.GloballyHyperbolicOn U := by
  refine ⟨fun x y h₁ h₂ => le_antisymm h₁.1 h₂.1, fun p q => ?_⟩
  by_cases hpq : timelikeLine.le U p q
  · have : timelikeLine.diamond U p q = Icc p q := by
      ext z
      simp only [Causality.mem_diamond, timelikeLine_le]
      constructor
      · rintro ⟨⟨h1, -⟩, h2, -⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, (Icc_subset_Icc_right h2).trans hpq.2⟩, h2,
          (Icc_subset_Icc_left h1).trans hpq.2⟩
    rw [this]; exact isCompact_Icc
  · have : timelikeLine.diamond U p q = ∅ := eq_empty_of_forall_notMem fun z hz =>
      hpq (timelikeLine.le_trans (Causality.mem_diamond.1 hz).1 (Causality.mem_diamond.1 hz).2)
    rw [this]; exact isCompact_empty

/-- `gateArc : ℝ ≃ ]-1, 1[` is an abstract morphism of the timelike line into itself. -/
theorem timelikeLine_isEMorphism_gateArc : IsEMorphism timelikeLine timelikeLine gateArc := by
  have hgm := gateArc_strictMono
  have himg : ∀ {x y : ℝ}, x ≤ y → gateArc '' Icc x y = Icc (gateArc x) (gateArc y) :=
    fun {x y} hxy =>
    Subset.antisymm (image_subset_iff.2 fun w hw => ⟨hgm.monotone hw.1, hgm.monotone hw.2⟩)
      (intermediate_value_Icc hxy gateArc_continuous.continuousOn)
  refine
    { continuousOn := gateArc_continuous.continuousOn
      isOpen_image := fun V _ => gateArc_isOpenMap _ V.isOpen
      map_le := fun V U _ hmaps x y hxy => ?_
      map_lt := fun V U _ hmaps x y hxy => ?_
      locally := fun x _ => ⟨⊤, le_rfl, trivial, hgm.injective.injOn,
        fun V' _ U hU y _ z _ => ?_⟩ }
  · obtain ⟨hxy, hsub⟩ := timelikeLine_le.1 hxy
    refine timelikeLine_le.2 ⟨hgm.monotone hxy, ?_⟩
    rw [← himg hxy]
    rintro _ ⟨w, hw, rfl⟩
    exact hmaps (hsub hw)
  · obtain ⟨hxy, hsub⟩ := timelikeLine_lt.1 hxy
    refine timelikeLine_lt.2 ⟨hgm hxy, ?_⟩
    rw [← himg hxy.le]
    rintro _ ⟨w, hw, rfl⟩
    exact hmaps (hsub hw)
  · have hsub : y ≤ z →
        (Icc y z ⊆ (V' : Set ℝ) ↔ Icc (gateArc y) (gateArc z) ⊆ (U : Set ℝ)) :=
      fun h => by rw [hU, ← himg h, image_subset_image_iff hgm.injective]
    constructor
    · rw [timelikeLine_le, timelikeLine_le, hgm.le_iff_le]
      exact and_congr_right hsub
    · rw [timelikeLine_lt, timelikeLine_lt, hgm.lt_iff_lt]
      exact and_congr_right fun h => hsub h.le

/-- The arc `]-1, 1[` of the timelike line, as an open set (the image of `gateArc`). -/
noncomputable def timelikeArcOpens : Opens ℝ := ⟨gateArc '' univ, gateArc_isOpenMap _ isOpen_univ⟩

/-- **The hypotheses of §3 step 3 (convexity, union) with `A` a proper open subset of `B`**: on
the timelike line, `A = ]-1, 1[ ≠ ℝ = B` is Cauchy-included in `B` (common Cauchy surface
`{g 0}`), `B` is causally arc-connected with curves extending; `A` is causally convex in `B`, and
the union of the family `{A, B}` of Cauchy inclusions of `A` is one. -/
theorem timelikeLine_causalConvex_proper :
    timelikeArcOpens ≠ ⊤ ∧ IsCauchyInclusion timelikeLine timelikeArcOpens ⊤ ∧
      timelikeLine.CausallyArcConnectedOn ⊤ ∧ timelikeLine.CurvesExtendOn ⊤ ∧
      timelikeLine.CausallyConvexIn (timelikeArcOpens : Set ℝ) ⊤ ∧
      IsCauchyInclusion timelikeLine timelikeArcOpens
        (⨆ b : Bool, if b then ⊤ else timelikeArcOpens) := by
  have hne : timelikeArcOpens ≠ ⊤ := fun h => by
    have h1 : (1 : ℝ) ∈ timelikeArcOpens := by rw [h]; trivial
    obtain ⟨w, -, hw⟩ := h1
    exact (gateArc_lt_one w).ne hw
  have h0A : gateArc 0 ∈ timelikeArcOpens := ⟨0, trivial, rfl⟩
  have hCA : timelikeLine.IsCauchySurfaceOn timelikeArcOpens {gateArc 0} := by
    have h := IsEMorphismOn.isCauchySurfaceOn_image_iff timelikeLine_isEMorphism_gateArc
      gateArc_strictMono.injective.injOn (V := ⊤) le_rfl (U := timelikeArcOpens)
      (by simp [timelikeArcOpens]) (S := {0}) (subset_univ _)
    rw [image_singleton] at h
    exact h.1 timelikeLine_isCauchySurface_zero
  have hCtop : timelikeLine.IsCauchySurfaceOn ⊤ {gateArc 0} :=
    timelikeLine_isCauchySurface_singleton (gateArc 0)
  have hsub : ({gateArc 0} : Set ℝ) ⊆ timelikeArcOpens := singleton_subset_iff.2 h0A
  have hAtop : IsCauchyInclusion timelikeLine timelikeArcOpens ⊤ :=
    ⟨le_top, timelikeLine_globallyHyperbolicOn _, timelikeLine_globallyHyperbolicOn _, _, hsub,
      hCA, hCtop⟩
  have hAA : IsCauchyInclusion timelikeLine timelikeArcOpens timelikeArcOpens :=
    ⟨le_rfl, timelikeLine_globallyHyperbolicOn _, timelikeLine_globallyHyperbolicOn _, _, hsub,
      hCA, hCA⟩
  have hac : timelikeLine.CausallyArcConnectedOn ⊤ := timelikeLine_causallyArcConnected
  refine ⟨hne, hAtop, hac, timelikeLine_curvesExtendOn ⊤,
    hAtop.causallyConvexIn hac (timelikeLine_curvesExtendOn ⊤),
    (isCauchyInclusion_iSup hac (timelikeLine_curvesExtendOn ⊤) hAtop
      (fun b => ?_) fun b => ?_).1⟩
  · cases b
    · exact hAA
    · exact hAtop
  · cases b
    · exact le_top
    · exact le_rfl

end Causal
