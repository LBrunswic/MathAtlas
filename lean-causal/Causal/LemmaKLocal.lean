import Causal.LemmaKSC

/-!
# Lemma K, the local conditions: two-sidedness is automatic, and the residue is one causal openness

No label is marked. Lemma K is DEC-44's abstraction of a sentence Barbot asserts twice and never
proves (Rem 2.3 `clomax`, `GHFspace.tex:572`, the sentence at l.576–578; §11, l.3537–3540); it
carries no paper label. Its bare form is `isCauchySurface_of_isLocallyCauchy`
(`CausalScaffold.CompactCauchy`), its second countable form
`isCauchySurface_of_isLocallyCauchy_of_secondCountable` (`CausalScaffold.LemmaKSCOpen`), both
tagged `sorry`s; DEC-92 asks it to be settled. This is round 3, track B: the local conditions
(1′)+(2′) of `isCauchySurface_iff_local` under `CurvesExtend`.

> Cauchy-compact GH spacetimes are automatically absolutely maximal. Indeed, any spacelike
> hypersurface in a given CGH spacetime is a Cauchy hypersurface. (Barbot, Rem 2.3, l.576–578)

**Verdict: not settled.** No proof of (1′)/(2′) from the bare hypotheses, no counterexample. What
is proved removes one of the two named data of every earlier proved form, and narrows the
residue to the openness of the causal future (and past) of one explicit open set.

## What is proved

* **Two-sidedness is automatic where curves extend**
  (`IsLocallyCauchy.isLocallyCauchyTwoSided`, `isLocallyCauchyTwoSided_iff`): in a Hausdorff
  tarentin globally hyperbolic causally arc-connected spacetime with `CurvesExtend`, a closed
  locally Cauchy `Σ` is two-sided in the same charts — `J^±_U(Σ ∩ U) ∖ Σ` is open
  (`isOpen_Jplus_diff_of_isCauchySurfaceOn`, `isOpen_Jminus_diff_of_isCauchySurfaceOn`). The key
  is `exists_nhds_subset_Jplus_of_isCauchySurfaceOn`: a point `y ∈ U ∖ Σ` above `Σ ∩ U` has a
  whole neighbourhood in `J^+(s)` for ONE `s ∈ Σ ∩ U` — tarentin gives `y ∈ Int J(p, q)` inside a
  causally convex neighbourhood missing `Σ`, and the inextensible curve of `U` through a curve
  from `p` to `y` meets `Σ` before `p`. **Only `≤` is used**: no push-up, no `Z^±`, no `≪`, so it
  holds at lightlike configurations and at BTZ points. CompactCauchy's SCOPE called two-sidedness
  "what spacelike means here", a datum the chart had to supply: it is a consequence.
* **Consequences** (two named data removed): Lemma K under `CurvesExtend` and causal openness of
  `⊤` (`J^±(V)` open for `V` open) — `isCauchySurface_of_isLocallyCauchy_of_isOpen_Jplus`; the gx
  shape without two-sidedness — `isCauchySurface_of_isLocallyCauchy_of_pushUp_of_isOpen_Jplus`;
  `CompactCauchy`'s proved form without two-sidedness (splitting + `CurvesExtend` only) —
  `isCauchySurface_of_isLocallyCauchy_of_splitting`; and **(1′) and (2′) themselves** under
  `CurvesExtend` and causal openness — `local_conditions_of_isOpen_Jplus`.
* **The residue, sharp** (`strictJplus_eq_Jplus_chartFutureSide`,
  `isCauchySurface_iff_isOpen_Jplus_chartFutureSide`): the strict causal future of `Σ` IS the
  causal future `J^+(O^+)` of the open **chart future side** `O^+ = ⋃_U (J^+_U(Σ ∩ U) ∖ Σ)`
  (`chartFutureSide`). So, where curves extend, `Σ` is a Cauchy surface **iff** `J^+(O^+)` and
  `J^-(O^-)` are open — causal openness at two specific open sets, a property of `≤` alone.

## Hypothesis checklist

| DEC-44 hypothesis | here |
|---|---|
| `C` a causality on `M`, `M` connected, `T2Space` | ✓ carried |
| `Tarentin`, `GloballyHyperbolic`, `CausallyArcConnected`, `J^±(p) ≠ {p}` | ✓ carried |
| `Σ` compact, connected, `IsLocallyCauchy` | ✓ carried (two-sidedness: closed `Σ` only) |
| second countability (`ETT.tex:255`) | ⚠ weakened: not used — it bears on nothing proved here |
| — | ⚠ strengthened, named (kb/0012): `C.CurvesExtend` (track A's datum) |
| — | ⚠ strengthened in the consequences: causal openness of `J^±(V)`, `V` open; or the sharp form, openness of `J^+(O^+)`, `J^-(O^-)` |

## SCOPE (disclosed)

* **Verdict on DEC-92, track B: not settled.** (1′)+(2′) are proved under causal openness, not
  from the bare hypotheses. Where curves extend, a counterexample to Lemma K must be a
  spacetime in which the causal future (or past) of the open chart side `O^±` of a compact
  connected locally Cauchy `Σ` is not open: a property of `≤` that tarentin, global
  hyperbolicity and causal arc-connectedness do not visibly imply (a point of `J^+(O^+)` on a
  "null" curve from `O^+` need not be interior; propagation `J^+(Int J^+(A)) ⊆ Int J^+(A)` is the
  missing step). Causal openness holds on the timelike and lightlike lines, Minkowski space,
  every static spacetime and wherever push-up and `Z^∓ = M` hold (`isOpen_Jplus_of_pushUp`);
  no causality satisfying the bare hypotheses and failing it was found or built.
* (2′) is NOT shown to follow from (1′) alone: given acausality, the points of `J^+(Σ) ∖ Σ` near
  `Σ` are interior (two-sidedness), but carrying interiority along a causal curve to a far point
  is again causal openness. Round 2's obstruction stands: no proof may use `≪`.
* Imported by `Causal.lean` (the strict root) since the round-3 integration (kb/0025); with
  second countability `CurvesExtend` is discharged in `Causal.LemmaKSCLocal`.
* Non-vacuity: on the timelike line (`timelikeLine_isCauchySurface_zero_of_lemmaKLocal`,
  `timelikeLine_isLocallyCauchyTwoSided_zero_of_lemmaKLocal`) the hypotheses hold jointly and
  the theorems apply.
* gx contract (a)–(f): not applicable; no length, metric or Lipschitz graph is defined here.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Function

universe u

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable {C : Causality M}

/-! ### Two-sidedness from the chart alone -/

/-- **In a chart, a point just above `Σ` has a whole neighbourhood above one point of `Σ`.**
Let `U` be causally convex, `S ∩ U` a Cauchy surface of `U`, `S` closed, `z ∈ S ∩ U`, `y ∈ U ∖ S`,
`z ≤ y`. Then for some `s ∈ S ∩ U` a neighbourhood of `y`, contained in `U ∖ S`, lies in `J^+(s)`.
The neighbourhood is the interior of a diamond `J(p, q)` from tarentin, inside a causally convex
neighbourhood of `y` missing `S` (strong causality); the inextensible curve of `U` through a curve
from `p` to `y` meets `S` once, and neither between `p` and `y` (that point would lie in the
convex neighbourhood) nor after `y` (`S ∩ U` is acausal and `y ∉ S`): so before `p`. No push-up,
no `Z^±`, no chronology. -/
theorem exists_nhds_subset_Jplus_of_isCauchySurfaceOn [T2Space M] (hT : C.Tarentin)
    (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected) (hext : C.CurvesExtend)
    {U : Opens M} (hU : C.CausallyConvexIn (U : Set M) ⊤) {S : Set M} (hSc : IsClosed S)
    (hSU : C.IsCauchySurfaceOn U (S ∩ U)) {z y : M} (hz : z ∈ S ∩ U) (hy : y ∈ U)
    (hyS : y ∉ S) (hzy : C.le ⊤ z y) :
    ∃ s ∈ S ∩ U, ∃ N ∈ 𝓝 y, N ⊆ (U : Set M) ∩ Sᶜ ∧ ∀ y' ∈ N, C.le ⊤ s y' := by
  have hcaus := hG.1
  have hN : (U : Set M) ∩ Sᶜ ∈ 𝓝 y :=
    inter_mem (U.isOpen.mem_nhds hy) (hSc.isOpen_compl.mem_nhds hyS)
  obtain ⟨V, hV, hVN, hVc⟩ := hG.stronglyCausal hT y _ hN
  obtain ⟨p, hpV, q, -, hyD⟩ := hT y V hV
  have hyD' : y ∈ interior (C.diamond ⊤ p q) := hyD
  have hpy : C.le ⊤ p y := (mem_diamond.1 (interior_subset hyD')).1
  obtain ⟨γ, hγ, hγ0, hγ1⟩ := (hC ⊤ le_rfl p y).1.1 hpy
  obtain ⟨I, c, hc, hsub⟩ := hext γ 0 1 zero_le_one hγ
  obtain ⟨tp, htp, hctp⟩ : p ∈ c '' I := hsub ⟨0, ⟨le_rfl, zero_le_one⟩, hγ0⟩
  obtain ⟨ty, hty, hcty⟩ : y ∈ c '' I := hsub ⟨1, ⟨zero_le_one, le_rfl⟩, hγ1⟩
  have hUy : c ty ∈ U := by rw [hcty]; exact hy
  have hJ := inextensible_ordConnectedComponent hcaus hc hty hUy
  obtain ⟨_, ⟨⟨t, htJ, rfl⟩, hS⟩, -⟩ := hSU _ c hJ
  have htI : t ∈ I := (ordConnectedComponent_subset htJ).1
  rcases le_total ty t with h | h
  · exfalso
    have hyt : C.le ⊤ y (c t) := by rw [← hcty]; exact hc.1.le_of_le hty htI h
    have he := eq_of_le_of_isCauchySurfaceOn hcaus hC hext hU hSU hz hS (C.le_trans hzy hyt)
    rw [← he] at hyt
    exact hyS (hcaus hyt hzy ▸ hz.1)
  · rcases le_total t tp with h' | h'
    · have hle : C.le ⊤ (c t) p := by rw [← hctp]; exact hc.1.le_of_le htI htp h'
      refine ⟨c t, hS, interior (C.diamond ⊤ p q) ∩ V,
        inter_mem (isOpen_interior.mem_nhds hyD') hV, fun x hx => hVN hx.2, fun y' hy' => ?_⟩
      exact C.le_trans hle (mem_diamond.1 (interior_subset hy'.1)).1
    · exfalso
      have h1 : C.le ⊤ p (c t) := by rw [← hctp]; exact hc.1.le_of_le htp htI h'
      have h2 : C.le ⊤ (c t) y := by rw [← hcty]; exact hc.1.le_of_le htI hty h
      have hmem : c t ∈ V := hVc.2 p hpV y (mem_of_mem_nhds hV) (mem_diamond.2 ⟨h1, h2⟩)
      exact (hVN hmem).2 hS.1

/-- **The future side of a chart is open**: `J^+_U(S ∩ U) ∖ S` is open when `U` is causally convex,
`S ∩ U` is a Cauchy surface of `U`, `S` is closed and curves extend. -/
theorem isOpen_Jplus_diff_of_isCauchySurfaceOn [T2Space M] (hT : C.Tarentin)
    (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected) (hext : C.CurvesExtend)
    {U : Opens M} (hU : C.CausallyConvexIn (U : Set M) ⊤) {S : Set M} (hSc : IsClosed S)
    (hSU : C.IsCauchySurfaceOn U (S ∩ U)) : IsOpen (C.Jplus U (S ∩ U) \ S) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨⟨z, hz, hzy⟩, hyS⟩
  have hy : y ∈ U := C.le_mem_right hzy
  obtain ⟨s, hs, N, hN, hNsub, hNle⟩ := exists_nhds_subset_Jplus_of_isCauchySurfaceOn hT hG hC
    hext hU hSc hSU hz hy hyS (C.le_mono le_top hzy)
  refine mem_of_superset hN fun y' hy' => ⟨⟨s, hs, ?_⟩, (hNsub hy').2⟩
  exact le_of_mem_causallyConvexIn hC hU hs.2 (hNsub hy').1 (hNle y' hy')

/-- **The past side of a chart is open**: the dual of `isOpen_Jplus_diff_of_isCauchySurfaceOn`. -/
theorem isOpen_Jminus_diff_of_isCauchySurfaceOn [T2Space M] (hT : C.Tarentin)
    (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected) (hext : C.CurvesExtend)
    {U : Opens M} (hU : C.CausallyConvexIn (U : Set M) ⊤) {S : Set M} (hSc : IsClosed S)
    (hSU : C.IsCauchySurfaceOn U (S ∩ U)) : IsOpen (C.Jminus U (S ∩ U) \ S) :=
  isOpen_Jplus_diff_of_isCauchySurfaceOn (C := C.dual) (dual_tarentin.2 hT)
    (dual_globallyHyperbolic.2 hG) (dual_causallyArcConnectedOn.2 hC) hext.dual
    (dual_causallyConvexIn.2 hU) hSc (dual_isCauchySurfaceOn.2 hSU)

/-- **Two-sidedness is automatic where curves extend.** A closed locally Cauchy set of a Hausdorff
tarentin globally hyperbolic causally arc-connected spacetime in which curves extend is locally
Cauchy and two-sided, in the same charts. -/
theorem IsLocallyCauchy.isLocallyCauchyTwoSided [T2Space M] (hT : C.Tarentin)
    (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected) (hext : C.CurvesExtend)
    {S : Set M} (hSc : IsClosed S) (hloc : C.IsLocallyCauchy S) :
    C.IsLocallyCauchyTwoSided S := fun x hx => by
  obtain ⟨U, hxU, hU, hSU⟩ := hloc x hx
  exact ⟨U, hxU, hU, hSU, isOpen_Jplus_diff_of_isCauchySurfaceOn hT hG hC hext hU hSc hSU,
    isOpen_Jminus_diff_of_isCauchySurfaceOn hT hG hC hext hU hSc hSU⟩

/-- Under the same hypotheses, two-sidedness and local Cauchyness coincide. -/
theorem isLocallyCauchyTwoSided_iff [T2Space M] (hT : C.Tarentin)
    (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected) (hext : C.CurvesExtend)
    {S : Set M} (hSc : IsClosed S) :
    C.IsLocallyCauchyTwoSided S ↔ C.IsLocallyCauchy S :=
  ⟨IsLocallyCauchyTwoSided.isLocallyCauchy,
    IsLocallyCauchy.isLocallyCauchyTwoSided hT hG hC hext hSc⟩

/-! ### Lemma K under causal openness, without two-sidedness -/

/-- **Lemma K where curves extend and causal futures and pasts of open sets are open.** The exact
hypotheses of the bare form, plus `CurvesExtend`, plus causal openness of `⊤`
(`J^±(V)` open for `V` open). No splitting, no two-sidedness, no push-up, no `Z^±`, no
chronology. -/
theorem isCauchySurface_of_isLocallyCauchy_of_isOpen_Jplus [T2Space M] [ConnectedSpace M]
    (hT : C.Tarentin) (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected)
    (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p})
    (hext : C.CurvesExtend) (hOp : ∀ V : Opens M, IsOpen (C.Jplus ⊤ V))
    (hOm : ∀ V : Opens M, IsOpen (C.Jminus ⊤ V)) {S : Set M} (hSc : IsCompact S)
    (hSconn : IsConnected S) (hloc : C.IsLocallyCauchy S) : C.IsCauchySurface S :=
  isCauchySurface_of_isLocallyCauchyTwoSided_of_isOpen_Jplus hT hG hC hJm hJp hext hOp hOm hSc
    hSconn (hloc.isLocallyCauchyTwoSided hT hG hC hext hSc.isClosed)

/-- **Lemma K in the shape gx needs, without two-sidedness**: the past side from push-up and
`Z^+ = M`, the future side from "the causal future of an open set is open". -/
theorem isCauchySurface_of_isLocallyCauchy_of_pushUp_of_isOpen_Jplus [T2Space M]
    [ConnectedSpace M] (hT : C.Tarentin) (hG : C.GloballyHyperbolic)
    (hC : C.CausallyArcConnected) (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p})
    (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) (hext : C.CurvesExtend) (hpush : C.PushUp)
    (hZp : ∀ p : M, p ∈ C.Zplus) (hOp : ∀ V : Opens M, IsOpen (C.Jplus ⊤ V)) {S : Set M}
    (hSc : IsCompact S) (hSconn : IsConnected S) (hloc : C.IsLocallyCauchy S) :
    C.IsCauchySurface S :=
  isCauchySurface_of_isLocallyCauchyTwoSided_of_pushUp hT hG hC hJm hJp hext hpush hZp hOp hSc
    hSconn (hloc.isLocallyCauchyTwoSided hT hG hC hext hSc.isClosed)

/-- **`CompactCauchy`'s proved form without two-sidedness**: a splitting and `CurvesExtend`
suffice. -/
theorem isCauchySurface_of_isLocallyCauchy_of_splitting [T2Space M] [ConnectedSpace M]
    {S₀ : Set M} {ψ : S₀ × ℝ ≃ₜ M} (hT : C.Tarentin) (hG : C.GloballyHyperbolic)
    (hC : C.CausallyArcConnected) (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p})
    (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) (hext : C.CurvesExtend)
    (hψ : C.IsCauchySplitting S₀ ψ) {S : Set M} (hSc : IsCompact S) (hSconn : IsConnected S)
    (hloc : C.IsLocallyCauchy S) : C.IsCauchySurface S :=
  isCauchySurface_of_isLocallyCauchyTwoSided hT hG hC hJm hJp hext hψ hSc hSconn
    (hloc.isLocallyCauchyTwoSided hT hG hC hext hSc.isClosed)

/-! ### The residue: the causal future of one open set -/

variable (C) in
/-- The **chart future side** of `S`: the union, over the causally convex open `U` in which
`S ∩ U` is a Cauchy surface of `U`, of the future sides `J^+_U(S ∩ U) ∖ S`. For `C.dual` it is the
chart past side. -/
def chartFutureSide (S : Set M) : Set M :=
  ⋃ (U : Opens M) (_ : C.CausallyConvexIn (U : Set M) ⊤ ∧ C.IsCauchySurfaceOn U (S ∩ U)),
    C.Jplus U (S ∩ U) \ S

/-- The chart future side is open (two-sidedness). -/
theorem isOpen_chartFutureSide [T2Space M] (hT : C.Tarentin) (hG : C.GloballyHyperbolic)
    (hC : C.CausallyArcConnected) (hext : C.CurvesExtend) {S : Set M} (hSc : IsClosed S) :
    IsOpen (C.chartFutureSide S) :=
  isOpen_iUnion fun _ => isOpen_iUnion fun h =>
    isOpen_Jplus_diff_of_isCauchySurfaceOn hT hG hC hext h.1 hSc h.2

/-- **The strict causal future of `Σ` is the causal future of its chart future side**, an open
set: so the openness of the strict causal future (the residue of Lemma K) is the causal openness
of `J^+` at ONE open set. -/
theorem strictJplus_eq_Jplus_chartFutureSide [T2Space M] (hcaus : C.IsCausal)
    (hC : C.CausallyArcConnected) (hext : C.CurvesExtend) {S : Set M}
    (hloc : C.IsLocallyCauchy S) : C.strictJplus S = C.Jplus ⊤ (C.chartFutureSide S) := by
  ext x
  constructor
  · rintro ⟨z, hz, hzx, hne⟩
    obtain ⟨U, hzU, hU, hSU⟩ := hloc z hz
    obtain ⟨y, hyU, hyz, hzy, hyx⟩ := exists_le_le_mem_ne_of_le hC U.isOpen hzU hzx hne
    have hyS : y ∉ S := fun h =>
      hyz (eq_of_le_of_isCauchySurfaceOn hcaus hC hext hU hSU ⟨hz, hzU⟩ ⟨h, hyU⟩ hzy).symm
    refine ⟨y, mem_iUnion₂.2 ⟨U, ⟨hU, hSU⟩, ⟨z, ⟨hz, hzU⟩, ?_⟩, hyS⟩, hyx⟩
    exact le_of_mem_causallyConvexIn hC hU hzU hyU hzy
  · rintro ⟨o, ho, hox⟩
    obtain ⟨U, -, ⟨z, hz, hzo⟩, hoS⟩ := mem_iUnion₂.1 ho
    have hzo' : C.le ⊤ z o := C.le_mono le_top hzo
    refine ⟨z, hz.1, C.le_trans hzo' hox, fun h => ?_⟩
    subst h
    exact hoS (hcaus hox hzo' ▸ hz.1)

/-- **The residue of Lemma K, sharp.** Where curves extend, a compact connected locally Cauchy
`Σ` is a Cauchy surface iff the causal future of its chart future side and the causal past of its
chart past side — two specific open sets — are open. -/
theorem isCauchySurface_iff_isOpen_Jplus_chartFutureSide [T2Space M] [ConnectedSpace M]
    (hT : C.Tarentin) (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected)
    (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p})
    (hext : C.CurvesExtend) {S : Set M} (hSc : IsCompact S) (hSconn : IsConnected S)
    (hloc : C.IsLocallyCauchy S) :
    C.IsCauchySurface S ↔ IsOpen (C.Jplus ⊤ (C.chartFutureSide S)) ∧
      IsOpen (C.Jminus ⊤ (C.dual.chartFutureSide S)) := by
  rw [isCauchySurface_iff_isOpen_strictJplus hT hG hC hJm hJp hext hSc hSconn hloc,
    strictJplus_eq_Jplus_chartFutureSide hG.1 hC hext hloc,
    strictJplus_eq_Jplus_chartFutureSide (C := C.dual) (dual_isCausal.2 hG.1)
      (dual_causallyArcConnectedOn.2 hC) hext.dual hloc.dual]
  rfl

/-! ### The local conditions (1′) and (2′) -/

/-- **(1′) and (2′) hold where curves extend and the causal future and past of open sets are
open** — the two local conditions of `isCauchySurface_iff_local`, for every compact connected
locally Cauchy `Σ`. -/
theorem local_conditions_of_isOpen_Jplus [T2Space M] [ConnectedSpace M]
    (hT : C.Tarentin) (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected)
    (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p})
    (hext : C.CurvesExtend) (hOp : ∀ V : Opens M, IsOpen (C.Jplus ⊤ V))
    (hOm : ∀ V : Opens M, IsOpen (C.Jminus ⊤ V)) {S : Set M} (hSc : IsCompact S)
    (hSconn : IsConnected S) (hloc : C.IsLocallyCauchy S) :
    (∀ w ∈ S ∩ C.strictJplus S, ∃ N ∈ 𝓝 w, S ∩ N ⊆ C.strictJplus S) ∧
      (∀ q ∈ C.Jplus ⊤ S ∪ C.Jminus ⊤ S, q ∉ S → C.Jplus ⊤ S ∪ C.Jminus ⊤ S ∈ 𝓝 q) :=
  (isCauchySurface_iff_local hT hG hC hJm hJp hext hSc hSconn hloc).1
    (isCauchySurface_of_isLocallyCauchy_of_isOpen_Jplus hT hG hC hJm hJp hext hOp hOm hSc hSconn
      hloc)

/-- **Lemma K from the openness of `J^+(O^+)` and `J^-(O^-)`** (the sharp residue, one direction):
the causal future of the chart future side and the causal past of the chart past side open
suffice; neither (1′) nor (2′) is assumed. -/
theorem isCauchySurface_of_isOpen_Jplus_chartFutureSide [T2Space M] [ConnectedSpace M]
    (hT : C.Tarentin) (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected)
    (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p})
    (hext : C.CurvesExtend) {S : Set M} (hSc : IsCompact S) (hSconn : IsConnected S)
    (hloc : C.IsLocallyCauchy S) (hp : IsOpen (C.Jplus ⊤ (C.chartFutureSide S)))
    (hm : IsOpen (C.Jminus ⊤ (C.dual.chartFutureSide S))) : C.IsCauchySurface S :=
  (isCauchySurface_iff_isOpen_Jplus_chartFutureSide hT hG hC hJm hJp hext hSc hSconn hloc).2
    ⟨hp, hm⟩

end Causality

/-! ### Non-vacuity: the timelike line -/

/-- On the timelike line every hypothesis of `isCauchySurface_of_isLocallyCauchy_of_isOpen_Jplus`
holds with `Σ = {0}`, and it applies. -/
theorem timelikeLine_isCauchySurface_zero_of_lemmaKLocal :
    timelikeLine.IsCauchySurface ({0} : Set ℝ) := by
  obtain ⟨hT, hG, hC, hJm, hJp, hext, -, hSc, hSconn, hloc⟩ := timelikeLine_lemmaK_hypotheses
  exact Causality.isCauchySurface_of_isLocallyCauchy_of_isOpen_Jplus hT hG hC hJm hJp hext
    timelikeLine_isOpen_Jplus timelikeLine_isOpen_Jminus hSc hSconn hloc.isLocallyCauchy

/-- On the timelike line the two-sidedness lemma applies to the locally Cauchy `{0}`. -/
theorem timelikeLine_isLocallyCauchyTwoSided_zero_of_lemmaKLocal :
    timelikeLine.IsLocallyCauchyTwoSided ({0} : Set ℝ) := by
  obtain ⟨hT, hG, hC, -, -, hext, -, hSc, -, hloc⟩ := timelikeLine_lemmaK_hypotheses
  exact hloc.isLocallyCauchy.isLocallyCauchyTwoSided hT hG hC hext hSc.isClosed

end Causal
