import Causal.NestedCausalities
import Causal.LadderLocal

/-!
# ERS19 Theorem 4.64 on a fixed background: two developments agree on a connected overlap

Programme target `T-abs-ers-thm-4-64` (`programme/roadmap.toml`; layer 1, ETT-layer imports only,
no model, no metric). Source: Eperon–Reall–Sbierski, arXiv 1802.03020, `papers/ers-predictability`
(`legacy/labeled/ghd_02_19.tex`; text `references/sbierski/text/eperon2018predictability.txt`).
Causal-topological skeletons whose analytic inputs are named hypotheses; **no label is marked**:

* `ersthm:ThmUnique` — `ghd_02_19.tex:858` (proof 865–912): `ers_theorem_4_64`,
  `ers_theorem_4_64_maxCommonDevelopment`; Step 1 `isCommonDevelopment_maxCommonDevelopment`,
  Step 2 `exists_isSpacelikeBoundaryPoint` (through `exists_spacelike_boundary_point`).
* `ersrem:RemTime` — `ghd_02_19.tex:914`: `ers_remark_4_67` (maximal common development),
  `ers_remark_4_67_future`, `ers_remark_4_67_past` (the time orientations agree).
* `erscor:CorDisCon` — `ghd_02_19.tex:921`: `ers_corollary_4_68`, `ers_corollary_4_68_eqOn`.
* `erscor:globally_defined_globally_hyperbolic` — `ghd_02_19.tex:926`: `ers_corollary_4_69`.
* `erscor:CorSupLum` — `ghd_02_19.tex:959`: `ers_corollary_4_71` (with `ers_lemma_4_70`).
* `erscor:CorUniqueSub` — `ghd_02_19.tex:988`: `ers_corollary_4_73` (with `ers_lemma_4_72`).
* `ersthm:ThmNotBlocking` — `ghd_02_19.tex:1100`: restatements only of the strict
  `ers_theorem_4_82`: `ers_theorem_4_82_of_sliceRestart`,
  `ers_theorem_4_82_of_globallyHyperbolicOn`.

> Theorem 4.64. Let u1 : U1 → R and u2 : U2 → R be two globally hyperbolic developments of
> (4.61) arising from the same initial data given on a connected hypersurface S ⊆ R^{d+1}.
> Assume that U1 ∩ U2 is connected. Then u1 and u2 agree on U1 ∩ U2.

> Remark 4.67. […] the proof in particular shows that under the assumptions of Theorem 4.64 the
> intersection U1 ∩ U2 is the maximal common globally hyperbolic development of u1 and u2. If we
> fix a choice of normal of the initial data hypersurface S and stipulate that it is future
> directed in U1 as well as in U2, then it follows in particular that a point x ∈ U1 ∩ U2, which
> lies to the future of S in U1, also lies to the future of S in U2. Similarly for the past.

> Corollary 4.68. […] If there exists an x ∈ U1 ∩ U2 with u1(x) ≠ u2(x), then U1 ∩ U2 is not
> connected. — Corollary 4.69. Let u1 : R^{d+1} → R be a globally defined globally hyperbolic
> development […]. Let u2 : U2 → R be another globally hyperbolic development […] of the same
> initial data. Then u1|U2 = u2. — Corollary 4.71. […] we then have u1(x) = u2(x) for all
> x ∈ U1 ∩ U2. — Corollary 4.73. […] Assume, moreover, that u1 : U1 → R is a m-GHD. Then
> u1 = u2 on U1 ∩ U2.

## The reading

* **One space, one causality.** `M` is the fixed background; `C` is the causality of the first
  development (`g(u₁, du₁)` on `U₁`), in which ERS run Steps 2–3. The second development's
  causality never enters the layer-1 argument: only the named hypotheses (and Remark 4.67, where
  it is `C₂`, and the lemmas 4.70/4.72) see it. On a fixed causality (the target's reading)
  take `C₂ = C`; ERS's own, where `g(u₂, du₂)` differs from `g(u₁, du₁)` off the agreement
  region, is covered too.
* **The solutions** are an agreement predicate `agree : Opens M → Prop` ("`u₁ = u₂` on `V`") that
  glues (`AgreementGlues`); for two functions it is `EqOn u₁ u₂` (`agreementGlues_eqOn`).
* **A common development** (`IsCommonDevelopment`) is an open `V ⊆ U₁ ∩ U₂` containing `S`, on
  which the solutions agree, of which `S` is a Cauchy surface; `V₀` (`maxCommonDevelopment`) is
  the union of all of them.
* **Readings of OQ-41**: `S` acausal (in `U₁`, `IsAcausalOn`); domains of dependence two-sided
  (none appears in layer 1: they are inside `SliceRestart`'s supplier).

## Hypothesis checklist

| paper | here |
|---|---|
| `u₁` a GHD | ✓ `GloballyHyperbolicOn U₁` (ladder `globally_hyperbolic`, read on `U₁`, kb/0001); `S` Cauchy in `U₁` ⚠ named through what it gives: `SplitBy U₁ S` (`splitBy_of_inextensibleThrough`), `CompactSlabs U₁ S`, `IsAcausalOn U₁ S` (OQ-41) |
| (not printed) `U₁` tarentin | ⚠ named: `TarentinOn U₁` (ladder `tarentin`, read on `U₁`), supplied by the smooth Lorentzian model; with GH it gives `J^∓_{U₁}(x)` closed |
| `u₂` a GHD | ⚠ weakened: not used in layer 1; consumed by the suppliers of `hlocal`, `hstay`, `hstep` |
| same initial data | ⚠ abstract: `agree` with `AgreementGlues`; Prop 4.63 named (`hlocal`) |
| `S` a connected hypersurface | ⚠ weakened: not used by 4.64 (non-emptiness comes from `SplitBy`); `IsPreconnected S` in 4.69, 4.71, 4.73 |
| `U₁ ∩ U₂` connected | ⚠ weakened: `IsPreconnected` |
| Step 1: `V₀` a CGHD, "immediate" | ✓ proved: `S` Cauchy in `V₀` (GH of `V₀` not concluded, SCOPE) |
| Step 2: `p` with (4.65) | ✓ proved, `exists_spacelike_boundary_point` in `U₁`; closedness of `J^∓_{U₁}(x)` derived from GH and tarentin of `U₁` |
| Step 2: `γ([0,1]) ⊆ U₂` | ⚠ named: `FrontierStaysIn` (`hstay`) |
| Steps 3–5 + Prop 4.63 | ⚠ named: `SliceRestart` (`hstep`), the shape of 4.82's `hstep` (SCOPE) |
| 4.67: normal of `S` future in both | ⚠ named: `FollowsSolution C C₂ agree (U₁ ⊓ U₂)`, `InextensibleThrough U₁` |
| 4.69: `U₁ = ℝ^{d+1}` | ✓ `U₁ = ⊤`: ladder `GloballyHyperbolic`, `Tarentin` of `C`; `U₂` connected derived (`isPreconnected_of_inextensibleThrough`) |
| 4.71, 4.73: Lemmas 4.70, 4.72 | ✓ composed with `ers_lemma_4_70`, `ers_lemma_4_72`, their named hypotheses kept |

## SCOPE (disclosed)

* **No label is marked.** Each statement rests on named hypotheses carrying the PDE and smooth
  Lorentzian inputs (layer 3); each docstring names its supplier. No `sorry` in this file.
* **A common development has `S` as Cauchy surface; global hyperbolicity is not asked**, so
  Remark 4.67's "maximal common GHD" is read "greatest common development with Cauchy surface
  `S`" (`ers_remark_4_67`). Concluding GH of a union is Geroch's (iii)⇒(i), unproved in the
  library (`CausalScaffold.GerochEquiv`), as in `ers_theorem_4_77`; the layer-1 argument never
  needs it, and `SliceRestart`'s premise is accordingly wider (Lorentzian: a Cauchy surface makes
  an open set GH, so its supplier is unchanged).
* **The restart and 4.82's `hstep`.** `SliceRestart C W S R L Q` is "at every frontier point `p`
  of `R` in `L` at which the frontier is spacelike in `W` (`IsSpacelikeBoundaryPoint`), `Q p`".
  4.82's `hstep` is `SliceRestart (cau i) (dom i) S Aᵢ (dom i) Qᵢ` definitionally
  (`ers_theorem_4_82_of_sliceRestart`); 4.64's is `SliceRestart C U₁ S V (U₁ ∩ U₂) Q` for every
  common development `V`. The shapes differ in `L` and `Q` only: in 4.64 the restart enlarges
  the common development whose frontier `p` is on (`Q = ∃ V', V < V'`), at a point of both
  developments; in 4.82 it enlarges the MGHD `dom i₁` across a point of `dom i ∖ dom i₁`, using
  `uᵢ` beyond it, which is why `Q` there also asks the one-sided neighbourhood of (4.83).
  With the relative ladder properties, 4.82's `hcaus`, `hJm`, `hJp` are derived from each
  development being GH and tarentin (`ers_theorem_4_82_of_globallyHyperbolicOn`).
* **Prop 4.63 is used twice by ERS**: Step 1 (some CGHD exists: `hlocal`) and Step 5 (agreement
  near `Σ_W`: inside `SliceRestart`). The first is not a restart (there is no boundary point), so
  it stays a separate hypothesis, the proposed ladder id `local_uniqueness`.
* **Step 2's `U₂` half is named, not proved.** `exists_spacelike_boundary_point` gives a minimal
  point `p` of the compact `J⁻_{U₁}(q) ∩ J⁺_{U₁}(S) ∩ ∂V₀`, in `U₁`; ERS put it in `U₂` because
  the null geodesic from `q` to `p` lies in `∂V₀`, where `g(u₁) = g(u₂)` by continuity, so it is
  `g(u₂)`-causal and cannot leave `U₂` before `S`. ETT has no relation on the closed set `∂V₀`
  (two causalities agreeing on the open `V₀` need not agree on curves in its frontier), and on one
  causality the argument needs the past-inextensible part of a curve in `U₂` to extend to an
  inextensible one, which the library has only for segments (`CurvesExtend`). Without it the
  restart's location `U₁ ∩ U₂` cannot be reached, and a restart located in `U₁` alone could not
  be supplied: when `U₁ ∩ U₂` is itself a common development with a spacelike frontier point in
  `U₁ ∖ U₂` (`U₂` a slab of `U₁ = ℝ^{d+1}`), no common development is larger.
* **Non-vacuity** (kb/0011), on the timelike line with `S = {0}`, `C₂ = C`. The proper instance
  `timelikeLine_ers_theorem_4_64_Ioo`: `U₁ = ℝ`, `U₂ = ]-1, 1[`, `u₁ = id`, `u₂` the clamp to
  `[-1, 1]` (they agree on no open set leaving `[-1, 1]`); `hlocal` by `]-1/2, 1/2[`,
  `FrontierStaysIn` because `J⁻(q) ∩ J⁺(0) = [0, q] ⊆ ]-1, 1[`, `SliceRestart` with
  `V' = ]-1, 1[`, which contains the frontier point `p` while `V` does not; the Cauchy property of
  the intervals is transported from `ℝ` along `x ↦ c·arctan x`
  (`timelikeLine_isCauchySurfaceOn_Ioo`).
  The degenerate instance `timelikeLine_ers_theorem_4_64` (`U₁ = U₂ = ℝ`, `hlocal` by `U₁ ∩ U₂`
  itself, `FrontierStaysIn` trivial) is kept. Every instance has `U₁ ∩ U₂` a common development
  (that is Remark 4.67).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Function

open scoped Interval

universe u v

variable {M : Type u} [TopologicalSpace M]

/-! ## 0. The solutions: an agreement predicate that glues -/

/-- **Agreement is local and glues**: two solutions which agree on each open set of a family agree
on its union (ERS Step 1: "`v₀(x) = v_α(x)` for `x ∈ V_α` … is well-defined"). For two
functions this is `agreementGlues_eqOn`. -/
def AgreementGlues (agree : Opens M → Prop) : Prop :=
  ∀ 𝒱 : Set (Opens M), (∀ V ∈ 𝒱, agree V) → agree (sSup 𝒱)

/-- Two functions: agreement on open sets glues. -/
theorem agreementGlues_eqOn {β : Type v} (u₁ u₂ : M → β) :
    AgreementGlues (fun V : Opens M => EqOn u₁ u₂ V) := by
  intro 𝒱 h x hx
  obtain ⟨V, hV, hxV⟩ := Opens.mem_sSup.1 hx
  exact h V hV hxV

namespace Causality

/-! ## 1. Definitions -/

section Defs

variable (C : Causality M)

/-- `def:tarentin_spacetime` for the open set `W` seen as a spacetime (kb/0001): every
neighbourhood of every `x ∈ W` contains `p, q` with `x` in the interior of `J_W(p, q)`
(`tarentinOn_top`). Supplier for a development of a quasilinear equation: a smooth Lorentzian
metric is tarentin (T-loc-quasilinear-causal-ladder). -/
def TarentinOn (W : Opens M) : Prop :=
  ∀ x ∈ W, ∀ N ∈ 𝓝 x, ∃ p ∈ N, ∃ q ∈ N, x ∈ C.openDiamond W p q

/-- `S` is **acausal in the open set `W`**: no two distinct points of `S` are related by `≤_W`
(`IsAcausal` is the case `W = ⊤`). The OQ-41 reading of ERS's initial hypersurface. Supplier: a
spacelike Cauchy hypersurface of a GH development is acausal (T-loc-quasilinear-causal-ladder);
in ETT, at `M`, from `CurvesExtend` and causal arc-connectedness (`IsCauchySurface.isAcausal`). -/
def IsAcausalOn (W : Opens M) (S : Set M) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, C.le W x y → x = y

/-- **The surface splits `W`**: every point of `W` is in `J⁺_W(S) ∪ J⁻_W(S)`. The `hsplit` of
`ers_theorem_4_82`. Supplier: a Cauchy hypersurface of a GH development splits it (every point
lies on an inextendible timelike curve, the integral curve of a timelike vector field;
T-loc-quasilinear-causal-ladder); in ETT, from `InextensibleThrough` and the Cauchy property
(`splitBy_of_inextensibleThrough`). -/
def SplitBy (W : Opens M) (S : Set M) : Prop :=
  ∀ q ∈ W, q ∈ C.Jplus W S ∪ C.Jminus W S

/-- **The slabs between `S` and a point are compact** in `W`: `J⁻_W(q) ∩ J⁺_W(S)` and
`J⁺_W(q) ∩ J⁻_W(S)` for every `q`. The `hKm`, `hKp` of `ers_theorem_4_82`. Supplier: O'Neill
Ch. 14 (a GH spacetime with Cauchy hypersurface `S`), ERS Step 3 ("By the global hyperbolicity
of `U₁` we know that `J⁻(q₀, U₁) ∩ J⁺(S, U₁)` is compact"); T-loc-quasilinear-causal-ladder. In
ETT the implication from a Cauchy surface is open (`CausalScaffold.GerochCauchy`,
`isCompact_Jminus_inter_Jplus_of_isCauchySurface`). -/
def CompactSlabs (W : Opens M) (S : Set M) : Prop :=
  ∀ q, IsCompact (C.Jminus W {q} ∩ C.Jplus W S) ∧ IsCompact (C.Jplus W {q} ∩ C.Jminus W S)

/-- **Through every point of `W` an inextensible causal curve of `W`.** Supplier: the integral
curve of a timelike vector field, maximally extended in `W` (T-loc-quasilinear-causal-ladder);
the `hthrough` of `ers_lemma_4_72`, there for points of `U₁ ∩ U₂`. -/
def InextensibleThrough (W : Opens M) : Prop :=
  ∀ x ∈ W, ∃ (I : Set ℝ) (c : ℝ → M), C.Inextensible W I c ∧ x ∈ c '' I

/-- **A spacelike point of `B`**: `p` is one relative to `S`, in `W` (ERS (4.65)/(4.85), the
conclusion of `exists_spacelike_boundary_point`): `J⁻_W(p) ∩ B ∩ J⁺_W(S) = {p}`, or the past
form `J⁺_W(p) ∩ B ∩ J⁻_W(S) = {p}`. -/
def IsSpacelikeBoundaryPoint (W : Opens M) (S B : Set M) (p : M) : Prop :=
  C.Jminus W {p} ∩ B ∩ C.Jplus W S = {p} ∨ C.Jplus W {p} ∩ B ∩ C.Jminus W S = {p}

/-- **The slice restart** (ERS Thm 4.64, Steps 3–5 with Prop 4.63; the shape of the `hstep` of
`ers_theorem_4_82`, which is `SliceRestart` definitionally, `ers_theorem_4_82_of_sliceRestart`):
at every point `p` of the frontier of the region `R` lying in `L`, at which that frontier is
spacelike in `W` relative to `S`, the conclusion `Q p` holds.

Supplier (layer 3, T-loc-quasilinear-slice), for `R` a common development, `W = U₁`,
`L = U₁ ∩ U₂`, `Q = "a strictly larger common development"`: Step 3 (a point `q ∈ I⁺(p)` with
`J⁻(q) ∩ (U₁ ∖ V) ∩ J⁺(S)` inside a given neighbourhood, by compactness and closedness of `≤`;
Sbierski's Lemma 3.11, causal), Step 4 (the time separation `τ_q` in a convex neighbourhood, its
level set `Σ` spacelike, O'Neill Ch. 5 Cor. 3, meeting `∂V`, inside `closure V`), Step 5 (`Σ_W`
acausal, O'Neill 14.46; its domains of dependence in `U₁` and `U₂`; local uniqueness, Prop 4.63;
`V ∪ O` has `S` as Cauchy surface). -/
def SliceRestart (W : Opens M) (S R L : Set M) (Q : M → Prop) : Prop :=
  ∀ p ∈ frontier R ∩ L, C.IsSpacelikeBoundaryPoint W S (frontier R) p → Q p

/-- **The frontier below a point of `L` stays in `L`** (ERS Thm 4.64, Step 2: "`γ([0,1]) ⊆ U₂`,
since `γ(0) ∈ U₂` and by the smoothness of `u₂`, `γ` is also a past directed null geodesic in the
globally hyperbolic `U₂` — hence, it cannot leave `U₂` without first crossing `S`"): for every
frontier point `q` of `R` in `L` lying in `J⁺_W(S)`, the frontier points of `R` in
`J⁻_W(q) ∩ J⁺_W(S)` lie in `L`; and the past form.

Supplier (layer 3; no roadmap row owns it yet, T-loc-quasilinear-slice is the natural one), for
`R` a common development, `W = U₁`, `L = U₁ ∩ U₂`: `∂R ∩ J⁺(S, U₁)` is achronal (`≪` open, `S`
Cauchy in `R`), so `J⁻(q, U₁) ∩ ∂R` is swept by null geodesics inside `∂R`; there
`g(u₁) = g(u₂)` (the solutions and their derivatives agree on `closure R ∩ U₁ ∩ U₂` by
continuity), so they are `g(u₂)`-causal, and `S ⊆ R` is never crossed. Not layer 1: see the
module's SCOPE. -/
def FrontierStaysIn (W : Opens M) (S R L : Set M) : Prop :=
  ∀ q ∈ frontier R ∩ L,
    (q ∈ C.Jplus W S → C.Jminus W {q} ∩ C.Jplus W S ∩ frontier R ⊆ L) ∧
    (q ∈ C.Jminus W S → C.Jplus W {q} ∩ C.Jminus W S ∩ frontier R ⊆ L)

/-- A **common development** of `U₁` and `U₂` (ERS's CGHD, read on open sets): an open
`V ⊆ U₁ ∩ U₂` containing `S`, on which the two solutions agree, of which `S` is a Cauchy surface
(for `C`, the causality of `g(u₁)`, which is that of `g(v)` on `V`). Global hyperbolicity is not
asked (module SCOPE). -/
structure IsCommonDevelopment (S : Set M) (U₁ U₂ : Opens M) (agree : Opens M → Prop)
    (V : Opens M) : Prop where
  le : V ≤ U₁ ⊓ U₂
  subset : S ⊆ V
  agree : agree V
  cauchy : C.IsCauchySurfaceOn V S

/-- ERS's **maximal common development** `V₀` (Step 1 of Thm 4.64): the union of the common
developments (`isCommonDevelopment_maxCommonDevelopment`). -/
def maxCommonDevelopment (S : Set M) (U₁ U₂ : Opens M) (agree : Opens M → Prop) : Opens M :=
  sSup {V | C.IsCommonDevelopment S U₁ U₂ agree V}

end Defs

/-- **The causality follows the solution on `W`** (Remark 4.67, used at `W = U₁ ∩ U₂` only): if
the solutions agree on `W`, the causal relation `≤_W` of `C` (of `g(u₁)`) is contained in that of
`C₂` (of `g(u₂)`). Supplier at `W = U₁ ∩ U₂`, after Theorem 4.64: `g(u, du)` depends on `u` and
`du` only, so `u₁ = u₂` on `W` gives `g(u₁) = g(u₂)` on `W`; the two time orientations, both
continuous on `W`, agree near `S` (ERS's stipulation: the normal of `S` future directed in both),
hence on the connected `W` containing `S`; T-loc-quasilinear-causal-ladder. Nothing is asked on
other opens (an agreement set away from `S`, or outside `U₁ ∩ U₂`). On one causality it is
`FollowsSolution.refl`. -/
def FollowsSolution (C C₂ : Causality M) (agree : Opens M → Prop) (W : Opens M) : Prop :=
  agree W → ∀ ⦃x y : M⦄, C.le W x y → C₂.le W x y

theorem FollowsSolution.refl (C : Causality M) (agree : Opens M → Prop) (W : Opens M) :
    FollowsSolution C C agree W :=
  fun _ _ _ h => h

variable {C : Causality M} {W W' : Opens M} {S : Set M}

/-! ### Relative tarentin and acausal -/

theorem tarentinOn_top : C.TarentinOn ⊤ ↔ C.Tarentin :=
  ⟨fun h x N hN => h x trivial N hN, fun h x _ N hN => h x N hN⟩

theorem dual_tarentinOn : C.dual.TarentinOn W ↔ C.TarentinOn W := by
  constructor
  · intro h x hx N hN
    obtain ⟨p, hp, q, hq, hpq⟩ := h x hx N hN
    rw [dual_openDiamond] at hpq
    exact ⟨q, hq, p, hp, hpq⟩
  · intro h x hx N hN
    obtain ⟨p, hp, q, hq, hpq⟩ := h x hx N hN
    exact ⟨q, hq, p, hp, by rw [dual_openDiamond]; exact hpq⟩

theorem isAcausalOn_top : C.IsAcausalOn ⊤ S ↔ C.IsAcausal S := Iff.rfl

theorem IsAcausal.isAcausalOn (h : C.IsAcausal S) (W : Opens M) : C.IsAcausalOn W S :=
  fun x hx y hy hxy => h x hx y hy (C.le_mono le_top hxy)

theorem IsAcausalOn.mono (h : C.IsAcausalOn W S) (hW : W' ≤ W) : C.IsAcausalOn W' S :=
  fun x hx y hy hxy => h x hx y hy (C.le_mono hW hxy)

/-! ### Closed causal futures and pasts in a globally hyperbolic tarentin open set -/

/-- `prop:GH_Jferme`'s first step in the open set `W`: the causal past of a point is closed in
`W` when `W` is globally hyperbolic and tarentin (`M` Hausdorff). The relative form of
`GloballyHyperbolic.isClosed_Jminus_singleton`, the same proof. -/
theorem GloballyHyperbolicOn.closure_Jminus_inter_subset [T2Space M]
    (hG : C.GloballyHyperbolicOn W) (hT : C.TarentinOn W) :
    ∀ x ∈ W, closure (C.Jminus W {x}) ∩ W ⊆ C.Jminus W {x} := by
  intro x _ q ⟨hq, hqW⟩
  obtain ⟨a, -, b, -, hqab⟩ := hT q hqW univ univ_mem
  have hclosed : IsClosed (C.diamond W a x) := (hG.2 a x).isClosed
  have hqd : q ∈ closure (C.diamond W a x) := by
    rw [mem_closure_iff_nhds]
    intro N hN
    have hN' : N ∩ C.openDiamond W a b ∈ 𝓝 q :=
      inter_mem hN (isOpen_openDiamond.mem_nhds hqab)
    obtain ⟨q', ⟨hq'N, hq'D⟩, hq'J⟩ := mem_closure_iff_nhds.1 hq _ hN'
    refine ⟨q', hq'N, ?_⟩
    rw [mem_diamond]
    exact ⟨(mem_diamond.1 (openDiamond_subset_diamond hq'D)).1, by simpa using hq'J⟩
  rw [hclosed.closure_eq] at hqd
  exact diamond_subset_Jminus hqd

/-- The future form (kb/0002). -/
theorem GloballyHyperbolicOn.closure_Jplus_inter_subset [T2Space M]
    (hG : C.GloballyHyperbolicOn W) (hT : C.TarentinOn W) :
    ∀ x ∈ W, closure (C.Jplus W {x}) ∩ W ⊆ C.Jplus W {x} :=
  GloballyHyperbolicOn.closure_Jminus_inter_subset (C := C.dual)
    (dual_globallyHyperbolicOn.2 hG) (dual_tarentinOn.2 hT)

/-! ### Inextensible curves through every point -/

/-- **A Cauchy surface splits its development** when every point lies on an inextensible causal
curve. -/
theorem splitBy_of_inextensibleThrough (hS : C.IsCauchySurfaceOn W S)
    (hthrough : C.InextensibleThrough W) : C.SplitBy W S := by
  intro q hq
  obtain ⟨I, c, hc, t, ht, rfl⟩ := hthrough q hq
  obtain ⟨_, ⟨⟨s, hs, rfl⟩, hsS⟩, -⟩ := hS I c hc
  rcases le_total s t with h | h
  · exact Or.inl ⟨c s, hsS, hc.1.le_of_le hs ht h⟩
  · exact Or.inr ⟨c s, hsS, hc.1.le_of_le ht hs h⟩

/-- Through every point of an open `W' ≤ W` runs an inextensible curve of `W'` when one of `W`
runs through it: its component (`inextensible_ordConnectedComponent_of_le`; `≤_W` antisymmetric,
`M` Hausdorff). -/
theorem InextensibleThrough.of_le [T2Space M] (h : C.InextensibleThrough W)
    (hanti : ∀ ⦃x y : M⦄, C.le W x y → C.le W y x → x = y) (hW : W' ≤ W) :
    C.InextensibleThrough W' := by
  intro x hx
  obtain ⟨I, c, hc, t₀, ht₀, rfl⟩ := h x (hW hx)
  exact ⟨_, c, inextensible_ordConnectedComponent_of_le hanti hW hc ht₀ hx, t₀,
    self_mem_ordConnectedComponent.2 ⟨ht₀, hx⟩, rfl⟩

/-- **A development is preconnected** when `S` is, and every point lies on an inextensible causal
curve of it meeting `S` (any causality). -/
theorem isPreconnected_of_inextensibleThrough {D : Causality M} (hS : IsPreconnected S)
    (hSW : S ⊆ W) (hC : D.IsCauchySurfaceOn W S) (hthrough : D.InextensibleThrough W) :
    IsPreconnected (W : Set M) := by
  refine isPreconnected_of_segments hS hSW fun x hx => ?_
  obtain ⟨I, γ, hγ, t₀, ht₀, rfl⟩ := hthrough x hx
  obtain ⟨_, ⟨⟨s, hs, rfl⟩, hsS⟩, -⟩ := hC I γ hγ
  refine ⟨γ, t₀, s, hγ.1.continuousOn_uIcc ht₀ hs, rfl, hsS, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  exact hγ.1.mem (hγ.1.ordConnected.uIcc_subset ht₀ hs hu)

/-! ## 2. Step 1: the maximal common development -/

/-- **ERS Thm 4.64, Step 1**: the union `V₀` of the common developments is a common development,
when one exists (Prop 4.63), agreement glues, `≤_{U₁}` is antisymmetric, `S` is acausal in `U₁`,
and `M` is Hausdorff. An inextensible curve of `V₀` meets `S` through its component in a common
development containing one of its points; twice it cannot, `S` being acausal in `U₁ ⊇ V₀`. -/
theorem isCommonDevelopment_maxCommonDevelopment [T2Space M] {U₁ U₂ : Opens M}
    {agree : Opens M → Prop} (hglue : AgreementGlues agree)
    (hanti : ∀ ⦃x y : M⦄, C.le U₁ x y → C.le U₁ y x → x = y) (hacausal : C.IsAcausalOn U₁ S)
    (hlocal : ∃ V, C.IsCommonDevelopment S U₁ U₂ agree V) :
    C.IsCommonDevelopment S U₁ U₂ agree (C.maxCommonDevelopment S U₁ U₂ agree) := by
  obtain ⟨V₁, hV₁⟩ := hlocal
  have hle : C.maxCommonDevelopment S U₁ U₂ agree ≤ U₁ ⊓ U₂ := sSup_le fun V hV => hV.le
  have hle₁ : C.maxCommonDevelopment S U₁ U₂ agree ≤ U₁ := hle.trans inf_le_left
  have hantiW : ∀ ⦃x y : M⦄, C.le (C.maxCommonDevelopment S U₁ U₂ agree) x y →
      C.le (C.maxCommonDevelopment S U₁ U₂ agree) y x → x = y := fun _ _ h₁ h₂ =>
    hanti (C.le_mono hle₁ h₁) (C.le_mono hle₁ h₂)
  refine ⟨hle, hV₁.subset.trans (le_sSup hV₁ : V₁ ≤ _), hglue _ fun V hV => hV.agree, ?_⟩
  intro I c hc
  obtain ⟨t₀, ht₀⟩ := hc.1.nonempty
  obtain ⟨V, hV, hcV⟩ := Opens.mem_sSup.1 (hc.1.mem ht₀)
  have hJ := inextensible_ordConnectedComponent_of_le hantiW (le_sSup hV) hc ht₀ hcV
  obtain ⟨_, ⟨⟨s, hs, rfl⟩, hsS⟩, -⟩ :=
    (show C.IsCommonDevelopment S U₁ U₂ agree V from hV).cauchy _ c hJ
  have hsI : s ∈ I := (ordConnectedComponent_subset hs).1
  refine ⟨c s, ⟨⟨s, hsI, rfl⟩, hsS⟩, ?_⟩
  rintro _ ⟨⟨s', hs', rfl⟩, hs'S⟩
  rcases le_total s s' with h | h
  · exact (hacausal _ hsS _ hs'S (C.le_mono hle₁ (hc.1.le_of_le hsI hs' h))).symm
  · exact hacausal _ hs'S _ hsS (C.le_mono hle₁ (hc.1.le_of_le hs' hsI h))

/-! ## 3. Step 2: a spacelike boundary point in `U₁ ∩ U₂` -/

/-- A proper open subset `V` of a preconnected set `L`, meeting it, has a frontier point in `L`
("Since we assume that `U₁ ∩ U₂` is connected, there exists then a point `q ∈ ∂V₀ ∩ U₁ ∩ U₂`"). -/
theorem exists_mem_frontier_inter {L V : Set M} (hL : IsPreconnected L) (hV : IsOpen V)
    (hLV : (L ∩ V).Nonempty) (hnot : ¬ L ⊆ V) : (frontier V ∩ L).Nonempty := by
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  refine hnot (hL.subset_of_closure_inter_subset hV hLV fun x ⟨hxc, hxL⟩ => ?_)
  by_contra hxV
  have : x ∈ frontier V ∩ L := ⟨by rw [hV.frontier_eq]; exact ⟨hxc, hxV⟩, hxL⟩
  rw [hne] at this
  exact this

/-- **ERS Thm 4.64, Step 2**: from a frontier point `q` of `R` in `L ⊆ W`, a frontier point `p` of
`R` in `L` at which the frontier is spacelike in `W`: the minimal point of the compact
`J^∓_W(q) ∩ J^±_W(S) ∩ ∂R` (`exists_spacelike_boundary_point`, whose closedness hypothesis is
derived from GH and tarentin of `W`), kept in `L` by `FrontierStaysIn`. No null geodesic. -/
theorem exists_isSpacelikeBoundaryPoint [T2Space M] (hG : C.GloballyHyperbolicOn W)
    (hT : C.TarentinOn W) (hsplit : C.SplitBy W S) (hK : C.CompactSlabs W S) {R L : Set M}
    (hLW : L ⊆ W) (hstay : C.FrontierStaysIn W S R L) {q : M} (hq : q ∈ frontier R ∩ L) :
    ∃ p ∈ frontier R ∩ L, C.IsSpacelikeBoundaryPoint W S (frontier R) p := by
  rcases hsplit q (hLW hq.2) with hqp | hqm
  · obtain ⟨p, hpK, hp⟩ := exists_spacelike_boundary_point hG.1
      (hG.closure_Jminus_inter_subset hT) isClosed_frontier ⟨hqp, hq.1⟩ (hK q).1
    exact ⟨p, ⟨hpK.2, (hstay q hq).1 hqp hpK⟩, Or.inl hp⟩
  · obtain ⟨p, hpK, hp⟩ := exists_spacelike_boundary_point (C := C.dual)
      (fun _ _ h₁ h₂ => hG.1 h₂ h₁)
      ((dual_globallyHyperbolicOn.2 hG).closure_Jminus_inter_subset (dual_tarentinOn.2 hT))
      isClosed_frontier ⟨hqm, hq.1⟩ (hK q).2
    exact ⟨p, ⟨hpK.2, (hstay q hq).2 hqm hpK⟩, Or.inr hp⟩

/-! ## 4. Theorem 4.64 -/

/-- **ERS19 Theorem 4.64, causal-topological skeleton: the maximal common development is
`U₁ ∩ U₂`** (`ersthm:ThmUnique`, unmarked). Step 1: `V₀` is a common development; if
`V₀ ≠ U₁ ∩ U₂`, connectedness gives `q ∈ ∂V₀ ∩ U₁ ∩ U₂`; Step 2 a spacelike `p ∈ ∂V₀ ∩ U₁ ∩ U₂`;
the restart a strictly larger common development, against maximality.

Hypotheses and suppliers: `hglue` — the solutions are functions (`agreementGlues_eqOn`); `hG`,
`hT` — `U₁` is GH and tarentin for `g(u₁)` (ladder `globally_hyperbolic`, `tarentin` on `U₁`;
T-loc-quasilinear-causal-ladder); `hacausal` — `S` acausal in `U₁` (OQ-41); `hsplit`, `hK` —
`S` a Cauchy hypersurface of the GH `U₁` (`SplitBy`, `CompactSlabs`); `hconn` — ERS's
connectedness of `U₁ ∩ U₂`; `hlocal` — Prop 4.63 (proposed ladder id `local_uniqueness`;
T-loc-quasilinear-slice, the union of the `DS_p` in T-abs-ers-unions); `hstay` — Step 2's
`γ([0,1]) ⊆ U₂` (`FrontierStaysIn`); `hstep` — Steps 3–5 with Prop 4.63 (`SliceRestart`;
T-loc-quasilinear-slice). -/
theorem ers_theorem_4_64_maxCommonDevelopment [T2Space M] {U₁ U₂ : Opens M}
    {agree : Opens M → Prop} (hglue : AgreementGlues agree)
    (hG : C.GloballyHyperbolicOn U₁) (hT : C.TarentinOn U₁) (hacausal : C.IsAcausalOn U₁ S)
    (hsplit : C.SplitBy U₁ S) (hK : C.CompactSlabs U₁ S)
    (hconn : IsPreconnected ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hlocal : ∃ V, C.IsCommonDevelopment S U₁ U₂ agree V)
    (hstay : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.FrontierStaysIn U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hstep : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.SliceRestart U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M)
        (fun _ => ∃ V', C.IsCommonDevelopment S U₁ U₂ agree V' ∧ V < V')) :
    C.maxCommonDevelopment S U₁ U₂ agree = U₁ ⊓ U₂ := by
  have hV₀ := isCommonDevelopment_maxCommonDevelopment hglue hG.1 hacausal hlocal
  refine le_antisymm hV₀.le ?_
  by_contra hnot
  -- `V₀` meets `U₁ ∩ U₂` along `S`, which `U₁ ∩ U₂` reaches (`hsplit`) as soon as it is not `⊆ V₀`
  obtain ⟨x, hx, -⟩ := SetLike.not_le_iff_exists.1 hnot
  have hne : (((U₁ ⊓ U₂ : Opens M) : Set M) ∩ C.maxCommonDevelopment S U₁ U₂ agree).Nonempty := by
    obtain ⟨s, hsS, -⟩ | ⟨s, hsS, -⟩ := hsplit x hx.1 <;>
      exact ⟨s, hV₀.le (hV₀.subset hsS), hV₀.subset hsS⟩
  -- a frontier point `q` of `V₀` in `U₁ ∩ U₂` (`U₁ ∩ U₂` connected)
  obtain ⟨q, hq⟩ := exists_mem_frontier_inter hconn (C.maxCommonDevelopment S U₁ U₂ agree).isOpen
    hne fun h => hnot h
  -- Step 2: a spacelike frontier point `p` in `U₁ ∩ U₂`
  obtain ⟨p, hp, hsp⟩ := exists_isSpacelikeBoundaryPoint hG hT hsplit hK
    (fun x hx => hx.1) (hstay _ hV₀) hq
  -- Steps 3–5 (the restart): a strictly larger common development, against maximality
  obtain ⟨V', hV', hlt⟩ := hstep _ hV₀ p hp hsp
  exact lt_irrefl _ (hlt.trans_le (le_sSup hV'))

/-- **ERS19 Theorem 4.64, causal-topological skeleton** (`ersthm:ThmUnique`, unmarked): two
developments of the same data, with `U₁ ∩ U₂` connected, agree on `U₁ ∩ U₂`. Hypotheses and
suppliers as in `ers_theorem_4_64_maxCommonDevelopment`. -/
theorem ers_theorem_4_64 [T2Space M] {U₁ U₂ : Opens M}
    {agree : Opens M → Prop} (hglue : AgreementGlues agree)
    (hG : C.GloballyHyperbolicOn U₁) (hT : C.TarentinOn U₁) (hacausal : C.IsAcausalOn U₁ S)
    (hsplit : C.SplitBy U₁ S) (hK : C.CompactSlabs U₁ S)
    (hconn : IsPreconnected ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hlocal : ∃ V, C.IsCommonDevelopment S U₁ U₂ agree V)
    (hstay : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.FrontierStaysIn U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hstep : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.SliceRestart U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M)
        (fun _ => ∃ V', C.IsCommonDevelopment S U₁ U₂ agree V' ∧ V < V')) :
    agree (U₁ ⊓ U₂) := by
  rw [← ers_theorem_4_64_maxCommonDevelopment hglue hG hT hacausal hsplit hK hconn hlocal
    hstay hstep]
  exact (isCommonDevelopment_maxCommonDevelopment hglue hG.1 hacausal hlocal).agree

/-! ## 5. Remark 4.67 -/

/-- **ERS19 Remark 4.67, first sentence** (`ersrem:RemTime`, unmarked): under the hypotheses of
Theorem 4.64, `U₁ ∩ U₂` is the greatest common development. -/
theorem ers_remark_4_67 [T2Space M] {U₁ U₂ : Opens M}
    {agree : Opens M → Prop} (hglue : AgreementGlues agree)
    (hG : C.GloballyHyperbolicOn U₁) (hT : C.TarentinOn U₁) (hacausal : C.IsAcausalOn U₁ S)
    (hsplit : C.SplitBy U₁ S) (hK : C.CompactSlabs U₁ S)
    (hconn : IsPreconnected ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hlocal : ∃ V, C.IsCommonDevelopment S U₁ U₂ agree V)
    (hstay : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.FrontierStaysIn U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hstep : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.SliceRestart U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M)
        (fun _ => ∃ V', C.IsCommonDevelopment S U₁ U₂ agree V' ∧ V < V')) :
    IsGreatest {V | C.IsCommonDevelopment S U₁ U₂ agree V} (U₁ ⊓ U₂) := by
  have h := isCommonDevelopment_maxCommonDevelopment hglue hG.1 hacausal hlocal
  rw [ers_theorem_4_64_maxCommonDevelopment hglue hG hT hacausal hsplit hK hconn hlocal hstay
    hstep] at h
  exact ⟨h, fun V hV => hV.le⟩

/-- **The time orientations agree on a Cauchy development** (the core of Remark 4.67): if `S` is
a Cauchy surface of an open `V ≤ U`, acausal in `U`, `≤_U` antisymmetric and every point of `U`
on an inextensible curve of `U`, a point of `V` in `J⁺_U(S)` is in `J⁺_V(S)`. -/
theorem Jplus_inter_subset_of_isCauchySurfaceOn [T2Space M] {U V : Opens M} (hVU : V ≤ U)
    (hanti : ∀ ⦃x y : M⦄, C.le U x y → C.le U y x → x = y) (hacausal : C.IsAcausalOn U S)
    (hthrough : C.InextensibleThrough U) (hV : C.IsCauchySurfaceOn V S) :
    C.Jplus U S ∩ V ⊆ C.Jplus V S := by
  rintro x ⟨⟨σ, hσS, hσx⟩, hxV⟩
  rcases splitBy_of_inextensibleThrough hV (hthrough.of_le hanti hVU) x hxV with h | h
  · exact h
  · obtain ⟨σ', hσ'S, hxσ'⟩ := h
    have hxσ'U : C.le U x σ' := C.le_mono hVU hxσ'
    have hσσ' : σ = σ' := hacausal σ hσS σ' hσ'S (C.le_trans hσx hxσ'U)
    subst hσσ'
    have hxσ : x = σ := hanti hxσ'U hσx
    subst hxσ
    exact ⟨x, hσS, C.le_refl hxV⟩

/-- The past form. -/
theorem Jminus_inter_subset_of_isCauchySurfaceOn [T2Space M] {U V : Opens M} (hVU : V ≤ U)
    (hanti : ∀ ⦃x y : M⦄, C.le U x y → C.le U y x → x = y) (hacausal : C.IsAcausalOn U S)
    (hthrough : C.InextensibleThrough U) (hV : C.IsCauchySurfaceOn V S) :
    C.Jminus U S ∩ V ⊆ C.Jminus V S := by
  rintro x ⟨⟨σ, hσS, hxσ⟩, hxV⟩
  rcases splitBy_of_inextensibleThrough hV (hthrough.of_le hanti hVU) x hxV with h | h
  · obtain ⟨σ', hσ'S, hσ'x⟩ := h
    have hσ'xU : C.le U σ' x := C.le_mono hVU hσ'x
    have hσσ' : σ' = σ := hacausal σ' hσ'S σ hσS (C.le_trans hσ'xU hxσ)
    subst hσσ'
    have hxσ : x = σ' := hanti hxσ hσ'xU
    subst hxσ
    exact ⟨x, hσ'S, C.le_refl hxV⟩
  · exact h

/-- **ERS19 Remark 4.67, second sentence** (`ersrem:RemTime`, unmarked): a point of `U₁ ∩ U₂` to
the future of `S` in `U₁` (for `C`, the causality of `g(u₁)`) is to the future of `S` in `U₂`
(for `C₂`, that of `g(u₂)`). Hypotheses of Theorem 4.64 (with `hsplit` from `hC₁`, `hthrough`);
`hthrough` — through every point of `U₁` an inextendible causal curve
(T-loc-quasilinear-causal-ladder); `hfollow` — the causality follows the solution on `U₁ ∩ U₂`,
with the normal of `S` future directed in both (`FollowsSolution … (U₁ ⊓ U₂)`, ERS's
stipulation). -/
theorem ers_remark_4_67_future [T2Space M] {C₂ : Causality M} {U₁ U₂ : Opens M}
    {agree : Opens M → Prop} (hglue : AgreementGlues agree)
    (hG : C.GloballyHyperbolicOn U₁) (hT : C.TarentinOn U₁) (hacausal : C.IsAcausalOn U₁ S)
    (hC₁ : C.IsCauchySurfaceOn U₁ S) (hthrough : C.InextensibleThrough U₁)
    (hK : C.CompactSlabs U₁ S)
    (hconn : IsPreconnected ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hlocal : ∃ V, C.IsCommonDevelopment S U₁ U₂ agree V)
    (hstay : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.FrontierStaysIn U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hstep : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.SliceRestart U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M)
        (fun _ => ∃ V', C.IsCommonDevelopment S U₁ U₂ agree V' ∧ V < V'))
    (hfollow : FollowsSolution C C₂ agree (U₁ ⊓ U₂)) :
    ∀ x ∈ U₁ ⊓ U₂, x ∈ C.Jplus U₁ S → x ∈ C₂.Jplus U₂ S := by
  intro x hx hxS
  have hcd := (ers_remark_4_67 hglue hG hT hacausal (splitBy_of_inextensibleThrough hC₁ hthrough)
    hK hconn hlocal hstay hstep).1
  obtain ⟨σ, hσS, hσx⟩ :=
    Jplus_inter_subset_of_isCauchySurfaceOn inf_le_left hG.1 hacausal hthrough hcd.cauchy
      ⟨hxS, hx⟩
  exact ⟨σ, hσS, C₂.le_mono inf_le_right (hfollow hcd.agree hσx)⟩

/-- **ERS19 Remark 4.67, "Similarly for the past"** (`ersrem:RemTime`, unmarked). -/
theorem ers_remark_4_67_past [T2Space M] {C₂ : Causality M} {U₁ U₂ : Opens M}
    {agree : Opens M → Prop} (hglue : AgreementGlues agree)
    (hG : C.GloballyHyperbolicOn U₁) (hT : C.TarentinOn U₁) (hacausal : C.IsAcausalOn U₁ S)
    (hC₁ : C.IsCauchySurfaceOn U₁ S) (hthrough : C.InextensibleThrough U₁)
    (hK : C.CompactSlabs U₁ S)
    (hconn : IsPreconnected ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hlocal : ∃ V, C.IsCommonDevelopment S U₁ U₂ agree V)
    (hstay : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.FrontierStaysIn U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hstep : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.SliceRestart U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M)
        (fun _ => ∃ V', C.IsCommonDevelopment S U₁ U₂ agree V' ∧ V < V'))
    (hfollow : FollowsSolution C C₂ agree (U₁ ⊓ U₂)) :
    ∀ x ∈ U₁ ⊓ U₂, x ∈ C.Jminus U₁ S → x ∈ C₂.Jminus U₂ S := by
  intro x hx hxS
  have hcd := (ers_remark_4_67 hglue hG hT hacausal (splitBy_of_inextensibleThrough hC₁ hthrough)
    hK hconn hlocal hstay hstep).1
  obtain ⟨σ, hσS, hxσ⟩ :=
    Jminus_inter_subset_of_isCauchySurfaceOn inf_le_left hG.1 hacausal hthrough hcd.cauchy
      ⟨hxS, hx⟩
  exact ⟨σ, hσS, C₂.le_mono inf_le_right (hfollow hcd.agree hxσ)⟩

/-! ## 6. Corollaries 4.68 and 4.69 -/

/-- **ERS19 Corollary 4.68** (`erscor:CorDisCon`, unmarked), abstract form: if the solutions do
not agree on `U₁ ∩ U₂`, then `U₁ ∩ U₂` is not (pre)connected. The contrapositive of
`ers_theorem_4_64`; hypotheses and suppliers as there. -/
theorem ers_corollary_4_68 [T2Space M] {U₁ U₂ : Opens M}
    {agree : Opens M → Prop} (hglue : AgreementGlues agree)
    (hG : C.GloballyHyperbolicOn U₁) (hT : C.TarentinOn U₁) (hacausal : C.IsAcausalOn U₁ S)
    (hsplit : C.SplitBy U₁ S) (hK : C.CompactSlabs U₁ S)
    (hlocal : ∃ V, C.IsCommonDevelopment S U₁ U₂ agree V)
    (hstay : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.FrontierStaysIn U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hstep : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.SliceRestart U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M)
        (fun _ => ∃ V', C.IsCommonDevelopment S U₁ U₂ agree V' ∧ V < V'))
    (hdis : ¬ agree (U₁ ⊓ U₂)) :
    ¬ IsPreconnected ((U₁ ⊓ U₂ : Opens M) : Set M) := fun hconn =>
  hdis (ers_theorem_4_64 hglue hG hT hacausal hsplit hK hconn hlocal hstay hstep)

/-- **ERS19 Corollary 4.68** (`erscor:CorDisCon`, unmarked), for two functions as printed: if
`u₁ x ≠ u₂ x` at some `x ∈ U₁ ∩ U₂`, then `U₁ ∩ U₂` is not connected (not even preconnected). -/
theorem ers_corollary_4_68_eqOn [T2Space M] {β : Type v} {u₁ u₂ : M → β} {U₁ U₂ : Opens M}
    (hG : C.GloballyHyperbolicOn U₁) (hT : C.TarentinOn U₁) (hacausal : C.IsAcausalOn U₁ S)
    (hsplit : C.SplitBy U₁ S) (hK : C.CompactSlabs U₁ S)
    (hlocal : ∃ V, C.IsCommonDevelopment S U₁ U₂ (fun V => EqOn u₁ u₂ V) V)
    (hstay : ∀ V, C.IsCommonDevelopment S U₁ U₂ (fun V => EqOn u₁ u₂ V) V →
      C.FrontierStaysIn U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hstep : ∀ V, C.IsCommonDevelopment S U₁ U₂ (fun V => EqOn u₁ u₂ V) V →
      C.SliceRestart U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M)
        (fun _ => ∃ V', C.IsCommonDevelopment S U₁ U₂ (fun V => EqOn u₁ u₂ V) V' ∧ V < V'))
    (hx : ∃ x ∈ U₁ ⊓ U₂, u₁ x ≠ u₂ x) :
    ¬ IsPreconnected ((U₁ ⊓ U₂ : Opens M) : Set M) := by
  refine ers_corollary_4_68 (agreementGlues_eqOn u₁ u₂) hG hT hacausal hsplit hK hlocal hstay
    hstep fun h => ?_
  obtain ⟨x, hxU, hne⟩ := hx
  exact hne (h hxU)

/-- **ERS19 Corollary 4.69** (`erscor:globally_defined_globally_hyperbolic`, unmarked): a
development defined on all of `M` agrees on `U₂` with every other development `U₂`. `U₁ = ⊤`:
the hypotheses on `U₁` are the ladder nodes `globally_hyperbolic` and `tarentin` of `C`; `U₂` is
connected because `S` is and every point of `U₂` lies on an inextensible causal curve of `U₂`
(for any causality `C₂`, that of `g(u₂)`) meeting `S` (`isPreconnected_of_inextensibleThrough`).
Suppliers as in `ers_theorem_4_64`; `hthrough₂` — integral curves of a `g(u₂)`-timelike vector
field (T-loc-quasilinear-causal-ladder). -/
theorem ers_corollary_4_69 [T2Space M] {C₂ : Causality M} {U₂ : Opens M}
    {agree : Opens M → Prop} (hglue : AgreementGlues agree)
    (hG : C.GloballyHyperbolic) (hT : C.Tarentin) (hacausal : C.IsAcausal S)
    (hsplit : C.SplitBy ⊤ S) (hK : C.CompactSlabs ⊤ S)
    (hS : IsPreconnected S) (hC₂ : C₂.IsCauchySurfaceOn U₂ S)
    (hthrough₂ : C₂.InextensibleThrough U₂)
    (hlocal : ∃ V, C.IsCommonDevelopment S ⊤ U₂ agree V)
    (hstay : ∀ V, C.IsCommonDevelopment S ⊤ U₂ agree V → C.FrontierStaysIn ⊤ S V U₂)
    (hstep : ∀ V, C.IsCommonDevelopment S ⊤ U₂ agree V →
      C.SliceRestart ⊤ S V U₂ (fun _ => ∃ V', C.IsCommonDevelopment S ⊤ U₂ agree V' ∧ V < V')) :
    agree U₂ := by
  have hSU₂ : S ⊆ U₂ := by
    obtain ⟨V, hV⟩ := hlocal
    exact fun s hs => (hV.le (hV.subset hs)).2
  have hconn : IsPreconnected (((⊤ : Opens M) ⊓ U₂ : Opens M) : Set M) := by
    rw [top_inf_eq]
    exact isPreconnected_of_inextensibleThrough hS hSU₂ hC₂ hthrough₂
  have h := ers_theorem_4_64 (U₁ := ⊤) hglue hG (tarentinOn_top.2 hT)
    (hacausal.isAcausalOn ⊤) hsplit hK hconn hlocal
    (by rw [top_inf_eq]; exact hstay) (by rw [top_inf_eq]; exact hstep)
  rwa [top_inf_eq] at h

/-! ## 7. Corollaries 4.71 and 4.73: Theorem 4.64 composed with Lemmas 4.70 and 4.72 -/

/-- **ERS19 Corollary 4.71** (`erscor:CorSupLum`, unmarked): superluminal equations — under (4.62)
and "every maximal integral curve of `T` meets `S` at most once", two developments agree on
`U₁ ∩ U₂`. `ers_lemma_4_70` (connectedness, with its named hypotheses: `Cτ` the causality of the
integral curves of `T`, `hn₁`, `hn₂` the nesting (4.62), `hthroughτ`, `honce`, `hτ`) composed
with `ers_theorem_4_64` (for `C`, the causality of `g(u₁)`; `C₂` that of `g(u₂)`). -/
theorem ers_corollary_4_71 [T2Space M] {Cτ C₂ : Causality M} {U₁ U₂ : Opens M}
    {agree : Opens M → Prop} (hglue : AgreementGlues agree)
    (hG : C.GloballyHyperbolicOn U₁) (hT : C.TarentinOn U₁) (hacausal : C.IsAcausalOn U₁ S)
    (hsplit : C.SplitBy U₁ S) (hK : C.CompactSlabs U₁ S)
    (hS : IsPreconnected S) (hC₁ : C.IsCauchySurfaceOn U₁ S) (hC₂ : C₂.IsCauchySurfaceOn U₂ S)
    (hτ : Cτ.IsCausal)
    (hthroughτ : ∀ x ∈ U₁ ⊓ U₂, ∃ (I : Set ℝ) (γ : ℝ → M), Cτ.Inextensible ⊤ I γ ∧ x ∈ γ '' I)
    (honce : ∀ (I : Set ℝ) (γ : ℝ → M), Cτ.Inextensible ⊤ I γ →
      ∀ y ∈ γ '' I ∩ S, ∀ z ∈ γ '' I ∩ S, y = z)
    (hn₁ : InextensibleNestedOn Cτ C U₁) (hn₂ : InextensibleNestedOn Cτ C₂ U₂)
    (hlocal : ∃ V, C.IsCommonDevelopment S U₁ U₂ agree V)
    (hstay : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.FrontierStaysIn U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hstep : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.SliceRestart U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M)
        (fun _ => ∃ V', C.IsCommonDevelopment S U₁ U₂ agree V' ∧ V < V')) :
    agree (U₁ ⊓ U₂) := by
  have hSU : S ⊆ U₁ ⊓ U₂ := by
    obtain ⟨V, hV⟩ := hlocal
    exact fun s hs => hV.le (hV.subset hs)
  exact ers_theorem_4_64 hglue hG hT hacausal hsplit hK
    (ers_lemma_4_70 hS (fun s hs => (hSU hs).1) (fun s hs => (hSU hs).2) hC₁ hC₂ hτ hthroughτ
      honce hn₁ hn₂) hlocal hstay hstep

/-- **ERS19 Corollary 4.73** (`erscor:CorUniqueSub`, unmarked): subluminal equations — if `u₁` is
moreover an m-GHD, two developments agree on `U₁ ∩ U₂`. `ers_lemma_4_72` (connectedness, with its
named hypotheses: `Cm` Minkowski's causality, causal, curves extending, `S` m-acausal (OQ-41 (c)),
`U₁` m-Cauchy, `hnest` subluminality, `hthrough₂`) composed with `ers_theorem_4_64` (for `C`, the
causality of `g(u₁)`). -/
theorem ers_corollary_4_73 [T2Space M] {Cm C₂ : Causality M} {U₁ U₂ : Opens M}
    {agree : Opens M → Prop} (hglue : AgreementGlues agree)
    (hG : C.GloballyHyperbolicOn U₁) (hT : C.TarentinOn U₁) (hacausal : C.IsAcausalOn U₁ S)
    (hsplit : C.SplitBy U₁ S) (hK : C.CompactSlabs U₁ S)
    (hS : IsPreconnected S) (hm : Cm.IsCausal) (hmext : Cm.CurvesExtend)
    (hmacausal : Cm.IsAcausal S) (hmU₁ : Cm.IsCauchySurfaceOn U₁ S)
    (hC₂ : C₂.IsCauchySurfaceOn U₂ S)
    (hthrough₂ : ∀ x ∈ U₁ ⊓ U₂, ∃ (I : Set ℝ) (γ : ℝ → M), C₂.Inextensible U₂ I γ ∧ x ∈ γ '' I)
    (hnest : CurveNestedOn C₂ Cm U₂)
    (hlocal : ∃ V, C.IsCommonDevelopment S U₁ U₂ agree V)
    (hstay : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.FrontierStaysIn U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hstep : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.SliceRestart U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M)
        (fun _ => ∃ V', C.IsCommonDevelopment S U₁ U₂ agree V' ∧ V < V')) :
    agree (U₁ ⊓ U₂) := by
  have hSU : S ⊆ U₁ ⊓ U₂ := by
    obtain ⟨V, hV⟩ := hlocal
    exact fun s hs => hV.le (hV.subset hs)
  exact ers_theorem_4_64 hglue hG hT hacausal hsplit hK
    (ers_lemma_4_72 hS (fun s hs => (hSU hs).1) (fun s hs => (hSU hs).2) hm hmext hmacausal hmU₁
      hC₂ hthrough₂ hnest) hlocal hstay hstep

/-! ## 8. Theorem 4.82's `hstep` is a `SliceRestart` -/

/-- **Theorem 4.82 with its `hstep` written as a `SliceRestart`** (`ers_theorem_4_82`,
definitionally the same hypothesis): the restart of Theorem 4.82 is
`SliceRestart (cau i) (dom i) S Aᵢ (dom i) Qᵢ`, `Aᵢ` the component of `dom i₁ ∩ dom i` through
`s₀`, `Qᵢ p` "a one-sided neighbourhood of `p` gives a strictly larger development". The other
hypotheses are `ers_theorem_4_82`'s, `hsplit` and `hKm`, `hKp` written `SplitBy`, `CompactSlabs`.
-/
theorem ers_theorem_4_82_of_sliceRestart [T2Space M] [LocallyConnectedSpace M] {ι : Type*}
    (dom : ι → Opens M) (cau : ι → Causality M) {s₀ : M} (hs₀ : s₀ ∈ S) (i₁ : ι)
    (hSU : ∀ i, S ⊆ dom i)
    (hmax : ∀ i, dom i₁ ≤ dom i → dom i = dom i₁)
    (hconn : ∀ i, IsPreconnected (dom i : Set M))
    (hcaus : ∀ i ⦃x y : M⦄, (cau i).le (dom i) x y → (cau i).le (dom i) y x → x = y)
    (hsplit : ∀ i, (cau i).SplitBy (dom i) S)
    (hJm : ∀ i, ∀ x ∈ dom i, closure ((cau i).Jminus (dom i) {x}) ∩ dom i ⊆
      (cau i).Jminus (dom i) {x})
    (hJp : ∀ i, ∀ x ∈ dom i, closure ((cau i).Jplus (dom i) {x}) ∩ dom i ⊆
      (cau i).Jplus (dom i) {x})
    (hK : ∀ i, (cau i).CompactSlabs (dom i) S)
    (hSclosed : ∀ i, closure S ∩ dom i ⊆ S)
    (honesided : OneSidedBoundary (dom i₁) (closure S))
    (hstep : ∀ i, (cau i).SliceRestart (dom i) S
      (connectedComponentIn ((dom i₁ : Set M) ∩ dom i) s₀) (dom i)
      (fun p => (∃ V ∈ 𝓝 p, V ⊆ dom i ∧
        V ∩ dom i₁ ⊆ connectedComponentIn ((dom i₁ : Set M) ∩ dom i) s₀) →
        ∃ j, dom i₁ < dom j)) :
    ∀ i, dom i ≤ dom i₁ :=
  ers_theorem_4_82_of_oneSidedBoundary dom cau hs₀ i₁ hSU hmax hconn hcaus hsplit hJm hJp
    (fun i q => (hK i q).1) (fun i q => (hK i q).2) hSclosed honesided hstep

/-- **Theorem 4.82 with `hcaus`, `hJm`, `hJp` from ladder properties of each development**: each
`dom i` globally hyperbolic and tarentin for `cau i` (ladder `globally_hyperbolic`, `tarentin`,
read on `dom i`; T-loc-quasilinear-causal-ladder), through
`GloballyHyperbolicOn.closure_Jminus_inter_subset`. Otherwise `ers_theorem_4_82_of_sliceRestart`. -/
theorem ers_theorem_4_82_of_globallyHyperbolicOn [T2Space M] [LocallyConnectedSpace M] {ι : Type*}
    (dom : ι → Opens M) (cau : ι → Causality M) {s₀ : M} (hs₀ : s₀ ∈ S) (i₁ : ι)
    (hSU : ∀ i, S ⊆ dom i)
    (hmax : ∀ i, dom i₁ ≤ dom i → dom i = dom i₁)
    (hconn : ∀ i, IsPreconnected (dom i : Set M))
    (hG : ∀ i, (cau i).GloballyHyperbolicOn (dom i)) (hT : ∀ i, (cau i).TarentinOn (dom i))
    (hsplit : ∀ i, (cau i).SplitBy (dom i) S)
    (hK : ∀ i, (cau i).CompactSlabs (dom i) S)
    (hSclosed : ∀ i, closure S ∩ dom i ⊆ S)
    (honesided : OneSidedBoundary (dom i₁) (closure S))
    (hstep : ∀ i, (cau i).SliceRestart (dom i) S
      (connectedComponentIn ((dom i₁ : Set M) ∩ dom i) s₀) (dom i)
      (fun p => (∃ V ∈ 𝓝 p, V ⊆ dom i ∧
        V ∩ dom i₁ ⊆ connectedComponentIn ((dom i₁ : Set M) ∩ dom i) s₀) →
        ∃ j, dom i₁ < dom j)) :
    ∀ i, dom i ≤ dom i₁ :=
  ers_theorem_4_82_of_sliceRestart dom cau hs₀ i₁ hSU hmax hconn (fun i => (hG i).1) hsplit
    (fun i => (hG i).closure_Jminus_inter_subset (hT i))
    (fun i => (hG i).closure_Jplus_inter_subset (hT i)) hK hSclosed honesided hstep

end Causality

/-! ## 9. Witness: the hypotheses are jointly satisfiable (kb/0011) -/

/-- **The degenerate instance**: on the timelike line, `U₁ = U₂ = ℝ`, `S = {0}`,
`agree = EqOn id id`, every hypothesis of `ers_theorem_4_64` holds, but trivially: `hlocal` is
witnessed by `U₁ ∩ U₂` itself, `FrontierStaysIn` holds because `L = ℝ`, `hstep` with `V' = ℝ`.
The proper instance is `timelikeLine_ers_theorem_4_64_Ioo`. -/
theorem timelikeLine_ers_theorem_4_64 :
    EqOn (id : ℝ → ℝ) id (((⊤ : Opens ℝ) ⊓ ⊤ : Opens ℝ) : Set ℝ) := by
  have hcd : timelikeLine.IsCommonDevelopment ({0} : Set ℝ) ⊤ ⊤
      (fun V : Opens ℝ => EqOn (id : ℝ → ℝ) id V) ⊤ :=
    ⟨le_inf le_rfl le_rfl, fun _ _ => trivial, fun _ _ => rfl,
      timelikeLine_isCauchySurface_zero⟩
  refine Causality.ers_theorem_4_64 (agreementGlues_eqOn id id) timelikeLine_globallyHyperbolic
    (Causality.tarentinOn_top.2 timelikeLine_tarentin) ?_ ?_ ?_ ?_ ⟨⊤, hcd⟩ ?_ ?_
  · intro x hx y hy _
    rw [mem_singleton_iff] at hx hy
    rw [hx, hy]
  · intro q _
    rcases le_total 0 q with h | h
    · exact Or.inl ⟨0, rfl, timelikeLine_le_top.2 h⟩
    · exact Or.inr ⟨0, rfl, timelikeLine_le_top.2 h⟩
  · intro q
    have h1 : timelikeLine.Jminus ⊤ {q} ∩ timelikeLine.Jplus ⊤ ({0} : Set ℝ) = Icc 0 q := by
      ext z
      simp only [mem_inter_iff, Precausality.mem_Jminus_singleton, Precausality.mem_Jplus,
        mem_singleton_iff, exists_eq_left, timelikeLine_le_top, mem_Icc]
      tauto
    have h2 : timelikeLine.Jplus ⊤ {q} ∩ timelikeLine.Jminus ⊤ ({0} : Set ℝ) = Icc q 0 := by
      ext z
      simp only [mem_inter_iff, Precausality.mem_Jplus_singleton, Precausality.mem_Jminus,
        mem_singleton_iff, exists_eq_left, timelikeLine_le_top, mem_Icc]
    exact ⟨h1 ▸ isCompact_Icc, h2 ▸ isCompact_Icc⟩
  · rw [inf_idem, Opens.coe_top]
    exact isPreconnected_univ
  · intro V _ q _
    exact ⟨fun _ _ _ => ⟨trivial, trivial⟩, fun _ _ _ => ⟨trivial, trivial⟩⟩
  · intro V _ p hp _
    refine ⟨⊤, hcd, lt_top_iff_ne_top.2 fun hV => ?_⟩
    have : frontier ((V : Opens ℝ) : Set ℝ) = ∅ := by rw [hV, Opens.coe_top, frontier_univ]
    rw [this] at hp
    exact hp.1

/-- A strictly increasing, continuous, open map `g : ℝ → ℝ` is an abstract morphism of the
timelike line into itself (the proof of `Causal.timelikeLine_isEMorphism_gateArc` of
`Causal.CBG.CausalConvex`, a model-importing module, for any such `g`). -/
theorem timelikeLine_isEMorphism_of_strictMono {g : ℝ → ℝ} (hgm : StrictMono g)
    (hgc : Continuous g) (hgo : IsOpenMap g) : IsEMorphism timelikeLine timelikeLine g := by
  have himg : ∀ {x y : ℝ}, x ≤ y → g '' Icc x y = Icc (g x) (g y) :=
    fun {x y} hxy =>
    Subset.antisymm (image_subset_iff.2 fun w hw => ⟨hgm.monotone hw.1, hgm.monotone hw.2⟩)
      (intermediate_value_Icc hxy hgc.continuousOn)
  refine
    { continuousOn := hgc.continuousOn
      isOpen_image := fun V _ => hgo _ V.isOpen
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
        (Icc y z ⊆ (V' : Set ℝ) ↔ Icc (g y) (g z) ⊆ (U : Set ℝ)) :=
      fun h => by rw [hU, ← himg h, image_subset_image_iff hgm.injective]
    constructor
    · rw [timelikeLine_le, timelikeLine_le, hgm.le_iff_le]
      exact and_congr_right hsub
    · rw [timelikeLine_lt, timelikeLine_lt, hgm.lt_iff_lt]
      exact and_congr_right fun h => hsub h.le

/-- On the timelike line, `{g 0}` is a Cauchy surface of the range of a strictly increasing,
continuous, open `g`: `{0}` is one of `ℝ`, transported along `g`
(`IsEMorphismOn.isCauchySurfaceOn_image_iff`). -/
theorem timelikeLine_isCauchySurfaceOn_range {g : ℝ → ℝ} (hgm : StrictMono g)
    (hgc : Continuous g) (hgo : IsOpenMap g) {U : Opens ℝ} (hU : (U : Set ℝ) = range g) :
    timelikeLine.IsCauchySurfaceOn U {g 0} := by
  have h := IsEMorphismOn.isCauchySurfaceOn_image_iff
    (timelikeLine_isEMorphism_of_strictMono hgm hgc hgo) hgm.injective.injOn (V := ⊤) le_rfl
    (U := U) (by rw [hU, Opens.coe_top, image_univ]) (S := {0}) (subset_univ _)
  rw [image_singleton] at h
  exact h.1 timelikeLine_isCauchySurface_zero

/-- On the timelike line, `{0}` is a Cauchy surface of `]-r, r[` (`r > 0`): the range of
`x ↦ c·arctan x`, `c = r/(π/2)`. -/
theorem timelikeLine_isCauchySurfaceOn_Ioo {r : ℝ} (hr : 0 < r) {U : Opens ℝ}
    (hU : (U : Set ℝ) = Ioo (-r) r) : timelikeLine.IsCauchySurfaceOn U {0} := by
  have hπ : 0 < Real.pi / 2 := by positivity
  set c := r / (Real.pi / 2) with hc_def
  have hc : 0 < c := div_pos hr hπ
  have harctan : IsOpenMap Real.arctan :=
    isOpen_Ioo.isOpenMap_subtype_val.comp Real.tanOrderIso.symm.toHomeomorph.isOpenMap
  have hgo : IsOpenMap (fun x => c * Real.arctan x) :=
    (Homeomorph.mulLeft₀ c hc.ne').isOpenMap.comp harctan
  have hrange : range (fun x => c * Real.arctan x) = Ioo (-r) r := by
    rw [range_comp' (c * ·) Real.arctan, Real.range_arctan, image_mul_left_Ioo hc]
    have : c * (Real.pi / 2) = r := by rw [hc_def]; field_simp
    rw [mul_neg, this]
  have h := timelikeLine_isCauchySurfaceOn_range (Real.arctan_strictMono.const_mul hc)
    (continuous_const.mul Real.continuous_arctan) hgo (hU.trans hrange.symm)
  simpa [Real.arctan_zero] using h

/-- **A proper instance of `ers_theorem_4_64`**: on the timelike line, `U₁ = ℝ`, `U₂ = ]-1, 1[`,
`S = {0}`, `u₁ = id`, `u₂ = ` the clamp to `[-1, 1]` (they agree on an open set iff it lies in
`[-1, 1]`). Every hypothesis holds through the geometry of the line: `hlocal` by the common
development `]-1/2, 1/2[`; `FrontierStaysIn` because `J⁻(q) ∩ J⁺(0) = [0, q]` and
`J⁺(q) ∩ J⁻(0) = [q, 0]` lie in `]-1, 1[` for `q ∈ ]-1, 1[`; `SliceRestart` with
`V' = ]-1, 1[`, which contains the frontier point `p` of `V` while the open `V` does not. -/
theorem timelikeLine_ers_theorem_4_64_Ioo :
    EqOn (id : ℝ → ℝ) (fun x => max (-1) (min x 1))
      (((⊤ : Opens ℝ) ⊓ ⟨Ioo (-1) 1, isOpen_Ioo⟩ : Opens ℝ) : Set ℝ) := by
  set U₂ : Opens ℝ := ⟨Ioo (-1) 1, isOpen_Ioo⟩ with hU₂
  set agree : Opens ℝ → Prop := fun V => EqOn (id : ℝ → ℝ) (fun x => max (-1) (min x 1)) V
  have hinter : (((⊤ : Opens ℝ) ⊓ U₂ : Opens ℝ) : Set ℝ) = Ioo (-1) 1 := by
    rw [Opens.coe_inf, Opens.coe_top, univ_inter]; rfl
  have hagree : ∀ V : Opens ℝ, (V : Set ℝ) ⊆ Ioo (-1) 1 → agree V := fun V hV x hx => by
    obtain ⟨h1, h2⟩ := hV hx
    simp [min_eq_left h2.le, max_eq_right h1.le]
  have hcdI : ∀ (r : ℝ), 0 < r → r ≤ 1 → ∀ V : Opens ℝ, (V : Set ℝ) = Ioo (-r) r →
      timelikeLine.IsCommonDevelopment ({0} : Set ℝ) ⊤ U₂ agree V := by
    intro r hr hr1 V hV
    have hsub : (V : Set ℝ) ⊆ Ioo (-1) 1 := by
      rw [hV]; exact Ioo_subset_Ioo (by linarith) hr1
    refine ⟨fun x hx => ?_, ?_, hagree V hsub, timelikeLine_isCauchySurfaceOn_Ioo hr hV⟩
    · rw [← SetLike.mem_coe, hinter]; exact hsub hx
    · rw [singleton_subset_iff, hV]; exact ⟨by linarith, hr⟩
  have hcd : timelikeLine.IsCommonDevelopment ({0} : Set ℝ) ⊤ U₂ agree (⊤ ⊓ U₂) :=
    hcdI 1 one_pos le_rfl _ hinter
  refine Causality.ers_theorem_4_64 (agreementGlues_eqOn _ _) timelikeLine_globallyHyperbolic
    (Causality.tarentinOn_top.2 timelikeLine_tarentin) ?_ ?_ ?_ ?_
    ⟨⟨Ioo (-(1 / 2)) (1 / 2), isOpen_Ioo⟩, hcdI (1 / 2) one_half_pos one_half_lt_one.le _ rfl⟩
    ?_ ?_
  · intro x hx y hy _
    rw [mem_singleton_iff] at hx hy
    rw [hx, hy]
  · intro q _
    rcases le_total 0 q with h | h
    · exact Or.inl ⟨0, rfl, timelikeLine_le_top.2 h⟩
    · exact Or.inr ⟨0, rfl, timelikeLine_le_top.2 h⟩
  · intro q
    have h1 : timelikeLine.Jminus ⊤ {q} ∩ timelikeLine.Jplus ⊤ ({0} : Set ℝ) = Icc 0 q := by
      ext z
      simp only [mem_inter_iff, Precausality.mem_Jminus_singleton, Precausality.mem_Jplus,
        mem_singleton_iff, exists_eq_left, timelikeLine_le_top, mem_Icc]
      tauto
    have h2 : timelikeLine.Jplus ⊤ {q} ∩ timelikeLine.Jminus ⊤ ({0} : Set ℝ) = Icc q 0 := by
      ext z
      simp only [mem_inter_iff, Precausality.mem_Jplus_singleton, Precausality.mem_Jminus,
        mem_singleton_iff, exists_eq_left, timelikeLine_le_top, mem_Icc]
    exact ⟨h1 ▸ isCompact_Icc, h2 ▸ isCompact_Icc⟩
  · rw [hinter]; exact isPreconnected_Ioo
  · -- `FrontierStaysIn`: `J⁻(q) ∩ J⁺(0) = [0, q] ⊆ ]-1, 1[`, and the past form
    intro V _ q hq
    rw [hinter] at hq ⊢
    refine ⟨fun _ z hz => ?_, fun _ z hz => ?_⟩
    · obtain ⟨⟨hzq, ⟨_, rfl, h0z⟩⟩, -⟩ := hz
      rw [Precausality.mem_Jminus_singleton, timelikeLine_le_top] at hzq
      rw [timelikeLine_le_top] at h0z
      exact ⟨by linarith, hzq.trans_lt hq.2.2⟩
    · obtain ⟨⟨hqz, ⟨_, rfl, hz0⟩⟩, -⟩ := hz
      rw [Precausality.mem_Jplus_singleton, timelikeLine_le_top] at hqz
      rw [timelikeLine_le_top] at hz0
      exact ⟨hq.2.1.trans_le hqz, by linarith⟩
  · -- `SliceRestart`: `V' = ]-1, 1[`; the frontier point `p ∈ ]-1, 1[` is not in `V`
    intro V hV p hp _
    refine ⟨⊤ ⊓ U₂, hcd, lt_of_le_of_ne hV.le fun hVeq => ?_⟩
    have hpV : p ∈ (V : Set ℝ) := by rw [hVeq]; exact hp.2
    have := hp.1
    rw [V.isOpen.frontier_eq] at this
    exact this.2 hpV

end Causal
