import Causal.Port.SFALine
import Causal.Remarks.BTZPoints
import Causal.Remarks.Tarentin

/-!
# The singular-flat rows at every `E_{≥0}`-manifold: `Int J^± ∩ Z^∓ = I^±`, the cup-cap formula,
tarentin and strongly tarentin points, and the past of a BTZ point

Target `T-ett-singular-rows-local`. Cited, **unmarked** (SCOPE): `lem:J_int` — `ETT.tex:1800`,
`lem:cup_cap_sing` — `ETT.tex:1812`, `rem:tarentin_exemples` — `ETT.tex:688`,
`rem:lorentz_tarentin` — `ETT.tex:783`, `rem:pas_plat` — `ETT.tex:289`. For a singular
`(Isom(𝐌³), 𝐌³)`-manifold `M` (DEC-25) and every absolutely minimal causality `C` with an
isomorphic chart at each point over the family `E_{≥0}` (`IsoChartsCoverDEC25 … massAModelCausality`,
the hypotheses of `Causal.SFALocal`; the natural causality is one, `SFALocal.of_isAtlasCausalityDEC25`),
the assertions these five rows make about `E_{≥0}`-manifolds, read at `M` with `sing₀(M)` the
BTZ points of `Causal.SFALocal`. Everything comes from the chartwise, BTZ and line layers
(`Causal.SFALocal`, `Causal.SFABTZ`, `Causal.SFALine`) and the abstract cores
(`Causal.PushUp`, `Causal.Remarks.Tarentin`, `Causal.Remarks.BTZPoints`): no `SingularFlatAxioms`,
no field `massive_line`, no second countability.

> Let $M$ be a strongly causal singular flat spacetime. For every $p\in M$,
> $$\ring J^\pm(p)\cap Z^\mp(M)=I^\pm(p).$$ (`lem:J_int`, `ETT.tex:1801–1804`)

> Let $M$ be a globally hyperbolic singular flat spacetime, let $p\in M$ and let
> $(p_n)_{n\in \N}$ be a sequence of $M$ converging to $p$. Then
> $$I^{\pm}(p)=\mathrm{Int}\left(\bigcup_{N\in \N}\bigcap_{n\geq N} I^\pm(p_n)\right).$$
> (`lem:cup_cap_sing`, `ETT.tex:1813–1817`)

> Lorentzian manifolds are tarentin, and so is every $\mass{\geq0}$-manifold (Remark
> \ref{rem:sing_tarentin}). (`rem:tarentin_exemples`, `ETT.tex:689–690`)

> [...] on a $\mass{\geq0}$-manifold the points which fail to be strongly tarentin in the past
> are exactly the BTZ points (Remark \ref{rem:btz_pas_tarentin}). (`rem:lorentz_tarentin`,
> `ETT.tex:785–787`)

> \emph{Singularities.} At a BTZ point $p$ of a $\mass{\geq0}$-manifold, $I^-(p)=\emptyset$ while
> $J^-(p)$ is the singular half-line below $p$ (Definition \ref{defi:causal_E0}). This is the
> degenerate case of the same defect: causal past without chronological past.
> (`rem:pas_plat` (ii), `ETT.tex:294–295`)

## What is proved (no `sorry` in this file)

* **`Z^±` at `M`** (`Zplus_eq`, `Zminus_eq`, `compl_Zminus_eq`): `Z⁺(M) = M` (chart fact) and
  `Z⁻(M) = M ∖ sing₀(M)` (absolute minimality for the BTZ half, kb/0135).
* `lem:J_int` (unmarked): `J_int`, both signs as printed; `J_int_sing`, read at `M`:
  `Int J⁺(p) ∖ sing₀(M) = I⁺(p)` and `Int J⁻(p) = I⁻(p)`; from `Causality.J_int` with T1
  (`SFABTZ.t1Space_of_isoChartsCover`) and push-up (`SFALocal.pushUp`).
* `lem:cup_cap_sing` (unmarked): `cup_cap_sing`, `M` Hausdorff and globally hyperbolic, from
  `Causality.cup_cap_sing` with tarentin (`SFALocal.tarentin`); each sign with `J^∓(x)` closed only
  (`Iminus_eq_interior_iUnion_iInter`, `Iplus_eq_interior_iUnion_iInter`), no T2, no GH.
* `rem:tarentin_exemples` (unmarked), its `E_{≥0}` sentence: `tarentin` (no absolute minimality);
  assembled with the row's other halves in `tarentin_exemples_local`.
* `rem:lorentz_tarentin` (unmarked), its `E_{≥0}` sentence: `compl_Zminus_eq`; assembled in
  `lorentz_tarentin_local`.
* `rem:pas_plat` (ii) (unmarked): `Iminus_eq_empty` (every BTZ point, `M` causal or not),
  `btz_past` (`M` causal and Hausdorff: `J⁻(p) = γ(]-∞, 0])`, `γ` a closed embedding onto the
  component of `sing₀(M)` through `p`), `btz_past_bounds` (no causality:
  `γ(]-∞, 0]) ⊆ J⁻(p) ⊆ range γ`), `Jminus_subset_sing`. The row's findings at `M`:
  `interior_Jminus_eq_empty`, `btz_causallyPlain_past`, and `causallyPlain` (`M` is causally plain,
  `SFALocal.causallyPlain`). Assembled: `pas_plat_ii`.
* **The natural causality** (`IsAtlasCausalityDEC25`): the five rows at once,
  `rows_of_isAtlasCausalityDEC25`, through `SFALocal.of_isAtlasCausalityDEC25`.
* **Witnesses** (kb/0011), every conclusion out of this file's theorems: `nonvacuous_e0` (`E₀`,
  `sing₀ = axis ≠ ∅`, causal, globally hyperbolic), `nonvacuous_e0_natural` (`E₀` with its natural
  causality over the family, `MassAModelsInstance.isAtlasCausalityDEC25_e0`), `nonvacuous_epi`
  (`E_π`, `sing₀ = ∅`, `sing_π ≠ ∅`, globally hyperbolic).

## Hypothesis checklist

| paper | here |
|---|---|
| singular flat spacetime (`def:singular_spacetime`, l.1500–1505), `E_{≥0}`-manifold | ⚠ read (DEC-25, OQ-18): `[SingularGXStructure (Flat.isom 2) (Minkowski 2) M]`, `C` absolutely minimal with `IsoChartsCoverDEC25`; `tarentin`, `Zplus_eq` take no minimality |
| — connected (l.1502) | ⚠ weakened: not used |
| — Hausdorff, second countable (`ETT.tex:254`) | ⚠ weakened: T1 from the charts; ✓ Hausdorff carried by `cup_cap_sing`, `btz_past`, `btz_past_bounds`, `pas_plat_ii` (DEC-25's « manifold ») |
| `lem:J_int`: strongly causal | ⚠ weakened: not used |
| `lem:cup_cap_sing`: globally hyperbolic | ✓ carried (`cup_cap_sing`); ⚠ weakened to `J^∓(x)` closed per sign |
| « BTZ points », `sing₀(M)` | ⚠ read: `SFALocal.sing M 0` (`X_A`-charts into `E₀` sending the point to the axis) |
| `rem:pas_plat` (ii): « `J⁻(p)` is the singular half-line below `p` » | ⚠ strengthened: `M` causal (`btz_past`); without it only `btz_past_bounds` (a finding, SCOPE) |
| `E₀`, `Isom(E^{1,2})` | ⚠ read: `Causal.E0` (OQ-34, OQ-35), `Flat.isom 2` (OQ-82) |

## SCOPE (disclosed)

* **Why unmarked.** The readings OQ-18 (the causality), OQ-34/OQ-35 (`E₀`), OQ-82 (the group)
  remain; `rem:tarentin_exemples` and `rem:lorentz_tarentin` also speak of Lorentzian manifolds,
  which the library does not have (their Minkowski halves are the strict `Causal.tarentin_exemples`,
  `Causal.lorentz_tarentin`); `rem:pas_plat` (i) speaks of the `C⁰` causal bubbles of
  Chruściel–Grant and Sämann, not built.
* `rem:pas_plat` (ii) **needs `M` causal** for the half-line: in a non-causal `M` a component of
  `sing₀(M)` may be compact (by hand, not formalized: `E₀` modulo a translation along the axis),
  and `J⁻(p)` is then the whole circle. `btz_past_bounds` is what holds with no causality (that
  the set equation `J⁻(p) = γ(]-∞, 0])` holds there too, the circle included, is argued by hand
  from the chart time along the line and not proved here). The remark's « causal past without chronological past » is no failure of causal plainness: `M` is
  causally plain (`causallyPlain`), so l.290's « it fails in the two families » is refuted for the
  singular family in these readings.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Imports the strict
`Causal.Port.SFALine`, `Causal.Remarks.BTZPoints`, `Causal.Remarks.Tarentin` only.
-/

namespace Causal

open Set Filter Topology TopologicalSpace

universe u

namespace SingularRowsLocal

section Manifold

variable {M : Type u} [TopologicalSpace M] [SingularGXStructure (Flat.isom 2) (Minkowski 2) M]
  {C : Causality M}

/-! ### `Z^±` at an `E_{≥0}`-manifold -/

/-- `Z⁺(M) = M`: a chart fact (`SFALocal.mem_Zplus`). -/
theorem Zplus_eq (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) :
    C.Zplus = univ :=
  eq_univ_of_forall (SFALocal.mem_Zplus hC)

/-- `Z⁻(M) = M ∖ sing₀(M)` (`SFALocal.mem_Zminus_iff`). -/
theorem Zminus_eq (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) :
    C.Zminus = (SFALocal.sing M 0)ᶜ :=
  Set.ext (SFALocal.mem_Zminus_iff hmin hC)

/-- **`rem:lorentz_tarentin`, its `E_{≥0}` sentence, at `M`** (unmarked): the points which fail
to be strongly tarentin in the past are exactly the BTZ points. -/
theorem compl_Zminus_eq (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) :
    C.Zminusᶜ = SFALocal.sing M 0 := by
  rw [Zminus_eq hmin hC, compl_compl]

/-! ### `lem:J_int` -/

/-- **`lem:J_int` at every `E_{≥0}`-manifold** (unmarked), both signs as printed: from
`Causality.J_int`, with T1 from the charts and push-up. Strong causality is not used. -/
theorem J_int (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) (p : M) :
    interior (C.Jplus ⊤ {p}) ∩ C.Zminus = C.Iplus ⊤ {p} ∧
      interior (C.Jminus ⊤ {p}) ∩ C.Zplus = C.Iminus ⊤ {p} := by
  haveI := SFABTZ.t1Space_of_isoChartsCover hC
  exact Causality.J_int hmin (SFALocal.pushUp hmin hC) p

/-- `lem:J_int`, `+`, read at `M`: `Int J⁺(p) ∖ sing₀(M) = I⁺(p)`. -/
theorem interior_Jplus_diff_sing (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) (p : M) :
    interior (C.Jplus ⊤ {p}) \ SFALocal.sing M 0 = C.Iplus ⊤ {p} := by
  rw [Set.sdiff_eq, ← Zminus_eq hmin hC]
  exact (J_int hmin hC p).1

/-- `lem:J_int`, `-`, read at `M`: `Int J⁻(p) = I⁻(p)`. -/
theorem interior_Jminus_eq (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) (p : M) :
    interior (C.Jminus ⊤ {p}) = C.Iminus ⊤ {p} := by
  have h := (J_int hmin hC p).2
  rwa [Zplus_eq hC, inter_univ] at h

/-- **`lem:J_int` read at `M`** (unmarked): `Int J⁺(p) ∖ sing₀(M) = I⁺(p)` and
`Int J⁻(p) = I⁻(p)`. -/
theorem J_int_sing (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) (p : M) :
    interior (C.Jplus ⊤ {p}) \ SFALocal.sing M 0 = C.Iplus ⊤ {p} ∧
      interior (C.Jminus ⊤ {p}) = C.Iminus ⊤ {p} :=
  ⟨interior_Jplus_diff_sing hmin hC p, interior_Jminus_eq hmin hC p⟩

/-! ### `lem:cup_cap_sing` -/

/-- `lem:cup_cap_sing`, `-`, at every `E_{≥0}`-manifold whose `J⁺(x)` are closed. -/
theorem Iminus_eq_interior_iUnion_iInter (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) {p : M}
    {u : ℕ → M} (hu : Tendsto u atTop (𝓝 p)) (hJ : ∀ x, IsClosed (C.Jplus ⊤ {x})) :
    C.Iminus ⊤ {p} = interior (⋃ N : ℕ, ⋂ n ≥ N, C.Iminus ⊤ {u n}) := by
  haveI := SFABTZ.t1Space_of_isoChartsCover hC
  exact Causality.Iminus_eq_interior_iUnion_iInter hmin (SFALocal.pushUp hmin hC) hu hJ

/-- `lem:cup_cap_sing`, `+`, at every `E_{≥0}`-manifold whose `J⁻(x)` are closed. -/
theorem Iplus_eq_interior_iUnion_iInter (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) {p : M}
    {u : ℕ → M} (hu : Tendsto u atTop (𝓝 p)) (hJ : ∀ x, IsClosed (C.Jminus ⊤ {x})) :
    C.Iplus ⊤ {p} = interior (⋃ N : ℕ, ⋂ n ≥ N, C.Iplus ⊤ {u n}) := by
  haveI := SFABTZ.t1Space_of_isoChartsCover hC
  exact Causality.Iplus_eq_interior_iUnion_iInter hmin (SFALocal.pushUp hmin hC) hu hJ

/-- **`lem:cup_cap_sing` at every Hausdorff, globally hyperbolic `E_{≥0}`-manifold** (unmarked),
both signs: from `Causality.cup_cap_sing`, with push-up and tarentin from the charts. -/
theorem cup_cap_sing [T2Space M] (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hG : C.GloballyHyperbolic) {p : M} {u : ℕ → M} (hu : Tendsto u atTop (𝓝 p)) :
    C.Iminus ⊤ {p} = interior (⋃ N : ℕ, ⋂ n ≥ N, C.Iminus ⊤ {u n}) ∧
      C.Iplus ⊤ {p} = interior (⋃ N : ℕ, ⋂ n ≥ N, C.Iplus ⊤ {u n}) :=
  Causality.cup_cap_sing hmin (SFALocal.pushUp hmin hC) (SFALocal.tarentin hC) hG hu

/-! ### `rem:tarentin_exemples` -/

/-- **`rem:tarentin_exemples`, its `E_{≥0}` sentence** (unmarked): every `E_{≥0}`-manifold is
tarentin; a chart fact, no absolute minimality (`SFALocal.tarentin`). -/
theorem tarentin (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) :
    C.Tarentin :=
  SFALocal.tarentin hC

end Manifold

/-- **`rem:tarentin_exemples`, assembled at `E_{≥0}`-manifolds** (unmarked): Minkowski space
(every dimension) and `E_α`, `α > 0`, are tarentin; every `E_{≥0}`-manifold is tarentin (in place
of the field `tarentin` of `SingularFlatAxioms` in `Causal.tarentin_exemples`); and the mechanism
of `cexemple:misner_tarentin`. -/
theorem tarentin_exemples_local :
    (∀ n : ℕ, (minkowski n).Tarentin) ∧ (∀ (α : ℝ) [Fact (0 < α)], (massive α).Tarentin) ∧
    (∀ {M : Type u} [TopologicalSpace M] [SingularGXStructure (Flat.isom 2) (Minkowski 2) M]
      (C : Causality M),
      IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality → C.Tarentin) ∧
    (∀ {M : Type u} [TopologicalSpace M] (C : Causality M) (x : M),
      C.Jminus ⊤ {x} = {x} → C.Jplus ⊤ {x} ∉ 𝓝 x → ¬ C.Tarentin) :=
  ⟨tarentin_exemples.{u}.1, tarentin_exemples.{u}.2.1, fun _ hC => tarentin hC,
    tarentin_exemples.{u}.2.2.2⟩

/-- **`rem:lorentz_tarentin`, assembled at `E_{≥0}`-manifolds** (unmarked): Minkowski space
(every dimension) has `Z^± = M`; at every `E_{≥0}`-manifold `Z⁺ = M` and the points not strongly
tarentin in the past are exactly `sing₀(M)` (in place of `SingularFlatAxioms.Z_eq`). -/
theorem lorentz_tarentin_local :
    (∀ n : ℕ, (minkowski n).Zplus = univ ∧ (minkowski n).Zminus = univ) ∧
    (∀ {M : Type u} [TopologicalSpace M] [SingularGXStructure (Flat.isom 2) (Minkowski 2) M]
      (C : Causality M), C.AbsolutelyMinimal →
      IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality →
      C.Zplus = univ ∧ C.Zminusᶜ = SFALocal.sing M 0) :=
  ⟨minkowski_Z_eq_univ, fun _ hmin hC => ⟨Zplus_eq hC, compl_Zminus_eq hmin hC⟩⟩

section Manifold

variable {M : Type u} [TopologicalSpace M] [SingularGXStructure (Flat.isom 2) (Minkowski 2) M]
  {C : Causality M}

/-! ### `rem:pas_plat` (ii) -/

/-- `rem:pas_plat` (ii), first half, at every BTZ point of every `E_{≥0}`-manifold, causal or not:
`I⁻(p) = ∅`. -/
theorem Iminus_eq_empty (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) {p : M}
    (hp : p ∈ SFALocal.sing M 0) : C.Iminus ⊤ {p} = ∅ :=
  SFALocal.Iminus_eq_empty hmin hC p hp

/-- At a BTZ point, `J⁻(p) ⊆ sing₀(M)` (`SFABTZ.mem_sing_zero_of_le`). -/
theorem Jminus_subset_sing (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) {p : M}
    (hp : p ∈ SFALocal.sing M 0) : C.Jminus ⊤ {p} ⊆ SFALocal.sing M 0 :=
  fun _ hq => SFABTZ.mem_sing_zero_of_le hmin hC hp (Precausality.mem_Jminus_singleton.1 hq)

/-- **`rem:pas_plat` (ii) at every causal Hausdorff `E_{≥0}`-manifold** (unmarked): at a BTZ point
`p`, `I⁻(p) = ∅` and `J⁻(p) = γ(]-∞, 0])` for the BTZ line `γ` through `p`, a closed embedding
onto the component of `sing₀(M)` through `p`. -/
theorem btz_past [T2Space M] (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hc : C.IsCausal) {p : M} (hp : p ∈ SFALocal.sing M 0) :
    C.Iminus ⊤ {p} = ∅ ∧ ∃ γ : ℝ → M, γ 0 = p ∧ IsClosedEmbedding γ ∧
      C.Inextensible ⊤ univ γ ∧ range γ = connectedComponentIn (SFALocal.sing M 0) p ∧
      C.Jminus ⊤ {p} = γ '' Iic 0 := by
  obtain ⟨γ, hγ0, hγ, hγi, hγr, hJ⟩ := SFALine.Jminus_eq_image hmin hC hc hp
  exact ⟨Iminus_eq_empty hmin hC hp, γ, hγ0, hγ, hγi, hγr, hJ⟩

/-- `rem:pas_plat` (ii) with no causality: `I⁻(p) = ∅`, and `J⁻(p)` lies between the part
`γ(]-∞, 0])` of the BTZ line through `p` and the whole component. -/
theorem btz_past_bounds [T2Space M] (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    {p : M} (hp : p ∈ SFALocal.sing M 0) :
    C.Iminus ⊤ {p} = ∅ ∧ ∃ γ : ℝ → M, γ 0 = p ∧ C.Inextensible ⊤ univ γ ∧
      range γ = connectedComponentIn (SFALocal.sing M 0) p ∧
      γ '' Iic 0 ⊆ C.Jminus ⊤ {p} ∧ C.Jminus ⊤ {p} ⊆ range γ := by
  obtain ⟨γ, hγ0, -, hγi, hγr⟩ := SFALine.line hC p hp
  refine ⟨Iminus_eq_empty hmin hC hp, γ, hγ0, hγi, hγr, ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    have h := hγi.1.le_of_le trivial trivial (show t ≤ 0 from ht)
    rw [hγ0] at h
    exact Precausality.mem_Jminus_singleton.2 h
  · intro q hq
    rw [hγr]
    exact SFABTZ.Jminus_subset_component hmin hC hp (Precausality.mem_Jminus_singleton.1 hq)

/-- **Finding on `rem:pas_plat` (ii), at `M`**: the causal past, in any open set, of a set of BTZ
points has empty interior. -/
theorem interior_Jminus_eq_empty (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    {U : Opens M} {A : Set M} (hA : A ⊆ SFALocal.sing M 0) : interior (C.Jminus U A) = ∅ := by
  have hsub : C.Jminus U A ⊆ SFALocal.sing M 0 := by
    rintro y ⟨x, hxA, hyx⟩
    exact SFABTZ.mem_sing_zero_of_le hmin hC (hA hxA) (C.le_mono le_top hyx)
  exact subset_empty_iff.1
    ((interior_mono hsub).trans (SFALocal.interior_sing (M := M) 0 le_rfl).subset)

/-- **Finding on `rem:pas_plat` (ii), at `M`**: at BTZ points the past inclusion of
`defi:causalement_plat` holds. -/
theorem btz_causallyPlain_past (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    {U : Opens M} {A : Set M} (hA : A ⊆ SFALocal.sing M 0) :
    interior (C.Jminus U A) ⊆ closure (C.Iminus U A) := by
  rw [interior_Jminus_eq_empty hmin hC hA]
  exact empty_subset _

/-- **Finding on `rem:pas_plat`, at `M`**: every `E_{≥0}`-manifold is causally plain
(`SFALocal.causallyPlain`). -/
theorem causallyPlain (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) :
    C.CausallyPlain :=
  SFALocal.causallyPlain hmin hC

/-- **`rem:pas_plat` (ii), assembled at every Hausdorff `E_{≥0}`-manifold** (unmarked): `I⁻(p) = ∅`
at every BTZ point; at a causal `M`, `J⁻(p)` is the half-line of the BTZ line below `p`; and the
findings: `Int J⁻_U(A) = ∅` for `A ⊆ sing₀(M)`, and `M` is causally plain. -/
theorem pas_plat_ii [T2Space M] (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) :
    (∀ p ∈ SFALocal.sing M 0, C.Iminus ⊤ {p} = ∅) ∧
      (C.IsCausal → ∀ p ∈ SFALocal.sing M 0, ∃ γ : ℝ → M, γ 0 = p ∧ IsClosedEmbedding γ ∧
        range γ = connectedComponentIn (SFALocal.sing M 0) p ∧ C.Jminus ⊤ {p} = γ '' Iic 0) ∧
      (∀ (U : Opens M) (A : Set M), A ⊆ SFALocal.sing M 0 → interior (C.Jminus U A) = ∅) ∧
      C.CausallyPlain := by
  refine ⟨fun p hp => Iminus_eq_empty hmin hC hp, fun hc p hp => ?_,
    fun U A hA => interior_Jminus_eq_empty hmin hC hA, causallyPlain hmin hC⟩
  obtain ⟨-, γ, hγ0, hγ, -, hγr, hJ⟩ := btz_past hmin hC hc hp
  exact ⟨γ, hγ0, hγ, hγr, hJ⟩

/-! ### The natural causality -/

/-- **The five rows at every `E_{≥0}`-manifold with its natural causality** (`IsAtlasCausalityDEC25`,
OQ-18's reading of « the causality generated by its `X_A`-atlas », through
`SFALocal.of_isAtlasCausalityDEC25`; unmarked): `lem:J_int` as printed; `lem:cup_cap_sing` when
`M` is Hausdorff and globally hyperbolic; tarentin; `Z⁺ = M` and `Z⁻ᶜ = sing₀(M)`; `I⁻(p) = ∅` at
the BTZ points, `J⁻(p)` the half-line below `p` when `M` is Hausdorff and causal; causal
plainness. -/
theorem rows_of_isAtlasCausalityDEC25 (hcov : SFALocal.MassACovered M)
    (hC : IsAtlasCausalityDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) :
    (∀ p : M, interior (C.Jplus ⊤ {p}) ∩ C.Zminus = C.Iplus ⊤ {p} ∧
      interior (C.Jminus ⊤ {p}) ∩ C.Zplus = C.Iminus ⊤ {p}) ∧
    (T2Space M → C.GloballyHyperbolic → ∀ (p : M) (u : ℕ → M), Tendsto u atTop (𝓝 p) →
      C.Iminus ⊤ {p} = interior (⋃ N : ℕ, ⋂ n ≥ N, C.Iminus ⊤ {u n}) ∧
      C.Iplus ⊤ {p} = interior (⋃ N : ℕ, ⋂ n ≥ N, C.Iplus ⊤ {u n})) ∧
    C.Tarentin ∧ C.Zplus = univ ∧ C.Zminusᶜ = SFALocal.sing M 0 ∧
    (∀ p ∈ SFALocal.sing M 0, C.Iminus ⊤ {p} = ∅) ∧
    (T2Space M → C.IsCausal → ∀ p ∈ SFALocal.sing M 0, ∃ γ : ℝ → M, γ 0 = p ∧
      IsClosedEmbedding γ ∧ range γ = connectedComponentIn (SFALocal.sing M 0) p ∧
      C.Jminus ⊤ {p} = γ '' Iic 0) ∧
    C.CausallyPlain := by
  obtain ⟨hmin, hC'⟩ := SFALocal.of_isAtlasCausalityDEC25 hcov hC
  refine ⟨J_int hmin hC', fun hT2 hG p u hu => ?_, tarentin hC', Zplus_eq hC',
    compl_Zminus_eq hmin hC', fun p hp => Iminus_eq_empty hmin hC' hp, fun hT2 hc p hp => ?_,
    causallyPlain hmin hC'⟩
  · haveI := hT2
    exact cup_cap_sing hmin hC' hG hu
  · haveI := hT2
    exact (pas_plat_ii hmin hC').2.1 hc p hp

end Manifold

/-! ### Witnesses -/

section WitnessE0

attribute [local instance] E0GX.singularGX

/-- **Non-vacuity at `E₀`** (kb/0011): `sing₀(E₀)` is the axis, non-empty, and at every axis point
the conclusions of `J_int_sing`, `cup_cap_sing`, `btz_past` hold, with `E₀` tarentin and
`Z⁻(E₀)ᶜ` the axis, each out of this file's theorems. -/
theorem nonvacuous_e0 :
    SFALocal.sing E0 0 = E0.axis ∧ (SFALocal.sing E0 0).Nonempty ∧ E0.causality.Tarentin ∧
      E0.causality.Zminusᶜ = E0.axis ∧ E0.causality.CausallyPlain ∧
      ∀ p ∈ E0.axis,
        interior (E0.causality.Jplus ⊤ {p}) \ E0.axis = E0.causality.Iplus ⊤ {p} ∧
        interior (E0.causality.Jminus ⊤ {p}) = ∅ ∧
        (∀ u : ℕ → E0, Tendsto u atTop (𝓝 p) →
          E0.causality.Iminus ⊤ {p} = interior (⋃ N : ℕ, ⋂ n ≥ N, E0.causality.Iminus ⊤ {u n}) ∧
          E0.causality.Iplus ⊤ {p} = interior (⋃ N : ℕ, ⋂ n ≥ N, E0.causality.Iplus ⊤ {u n})) ∧
        E0.causality.Iminus ⊤ {p} = ∅ ∧
        ∃ γ : ℝ → E0, γ 0 = p ∧ IsClosedEmbedding γ ∧ range γ = E0.axis ∧
          E0.causality.Jminus ⊤ {p} = γ '' Iic 0 := by
  obtain ⟨hmin, hC, h0, hne⟩ := SFALocal.nonvacuous_e0
  refine ⟨h0, hne, tarentin hC, ?_, causallyPlain hmin hC, fun p hp => ?_⟩
  · rw [compl_Zminus_eq hmin hC, h0]
  have hp' : p ∈ SFALocal.sing E0 0 := h0 ▸ hp
  obtain ⟨hI, γ, hγ0, hγ, -, hγr, hJ⟩ := btz_past hmin hC E0.isCausal hp'
  refine ⟨?_, ?_, fun u hu => cup_cap_sing hmin hC E0.globallyHyperbolic hu, hI, γ, hγ0, hγ, ?_,
    hJ⟩
  · rw [← h0]
    exact interior_Jplus_diff_sing hmin hC p
  · rw [interior_Jminus_eq hmin hC p, hI]
  · have hconn : IsPreconnected E0.axis := by
      rw [← E0.range_axisLine p]
      exact isPreconnected_range (E0.isometry_axisLine p).continuous
    rw [hγr, h0]
    exact hconn.connectedComponentIn hp

/-- **Non-vacuity of `rows_of_isAtlasCausalityDEC25` at `E₀`** (kb/0011): `E₀` is an
`E_{≥0}`-manifold whose natural causality over the family is `E0.causality`
(`MassAModelsInstance.isAtlasCausalityDEC25_e0`), with a BTZ point, Hausdorff, causal and globally
hyperbolic; the assembly's conclusions out of it. -/
theorem nonvacuous_e0_natural :
    SFALocal.MassACovered E0 ∧
      IsAtlasCausalityDEC25 (Flat.isom 2) E0.causality (minkowski 2) massAModelCausality ∧
      (SFALocal.sing E0 0).Nonempty ∧ E0.causality.Zminusᶜ = SFALocal.sing E0 0 ∧
      (∀ p ∈ SFALocal.sing E0 0, E0.causality.Iminus ⊤ {p} = ∅ ∧
        ∃ γ : ℝ → E0, γ 0 = p ∧ IsClosedEmbedding γ ∧
          range γ = connectedComponentIn (SFALocal.sing E0 0) p ∧
          E0.causality.Jminus ⊤ {p} = γ '' Iic 0) ∧
      ∀ (p : E0) (u : ℕ → E0), Tendsto u atTop (𝓝 p) →
        E0.causality.Iminus ⊤ {p} = interior (⋃ N : ℕ, ⋂ n ≥ N, E0.causality.Iminus ⊤ {u n}) ∧
        E0.causality.Iplus ⊤ {p} = interior (⋃ N : ℕ, ⋂ n ≥ N, E0.causality.Iplus ⊤ {u n}) := by
  have hcov : SFALocal.MassACovered E0 := fun x _ =>
    ⟨none, OpenPartialHomeomorph.refl E0, isAEChart_refl, mem_univ x⟩
  have hC := MassAModelsInstance.isAtlasCausalityDEC25_e0
  obtain ⟨-, hcc, -, -, hZ, hI, hJ, -⟩ := rows_of_isAtlasCausalityDEC25 hcov hC
  exact ⟨hcov, hC, SFALocal.nonvacuous_e0.2.2.2, hZ, fun p hp => ⟨hI p hp,
    hJ inferInstance E0.isCausal p hp⟩, hcc inferInstance E0.globallyHyperbolic⟩

end WitnessE0

section WitnessEPi

attribute [local instance] EAlphaGX.singularGX EAlphaGX.fact_pi_pos

/-- **Non-vacuity at `E_π`** (kb/0011): `sing₀(E_π) = ∅` and `sing_π(E_π) ≠ ∅`; `Z⁻(E_π) = E_π`,
`Int J^±(p) = I^±(p)` at every point, the cup-cap formula (`E_π` is globally hyperbolic) and
tarentin, each out of the theorems of this file. -/
theorem nonvacuous_epi :
    SFALocal.sing (Massive Real.pi) 0 = ∅ ∧ (SFALocal.sing (Massive Real.pi) Real.pi).Nonempty ∧
      (massive Real.pi).Tarentin ∧ (massive Real.pi).Zminus = univ ∧
      ∀ p : Massive Real.pi,
        interior ((massive Real.pi).Jplus ⊤ {p}) = (massive Real.pi).Iplus ⊤ {p} ∧
        interior ((massive Real.pi).Jminus ⊤ {p}) = (massive Real.pi).Iminus ⊤ {p} ∧
        ∀ u : ℕ → Massive Real.pi, Tendsto u atTop (𝓝 p) →
          (massive Real.pi).Iminus ⊤ {p} =
            interior (⋃ N : ℕ, ⋂ n ≥ N, (massive Real.pi).Iminus ⊤ {u n}) ∧
          (massive Real.pi).Iplus ⊤ {p} =
            interior (⋃ N : ℕ, ⋂ n ≥ N, (massive Real.pi).Iplus ⊤ {u n}) := by
  obtain ⟨hmin, hC, -, hne, h0⟩ := SFALocal.nonvacuous_epi
  refine ⟨h0, hne, tarentin hC, ?_, fun p => ⟨?_, interior_Jminus_eq hmin hC p,
    fun u hu => cup_cap_sing hmin hC massive_globallyHyperbolic hu⟩⟩
  · rw [Zminus_eq hmin hC, h0, compl_empty]
  · have h := interior_Jplus_diff_sing hmin hC p
    rwa [h0, Set.sdiff_empty] at h

end WitnessEPi

end SingularRowsLocal

end Causal
