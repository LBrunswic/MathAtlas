import Causal.Port.SFALocalE0
import Causal.Remarks.MassAModelsInstance
import Causal.Model.BPrimeEAlpha

/-!
# `SingularFlatAxioms`' chartwise fields at every `E_{≥0}`-manifold

Target `T-ett-sfa-local`. Cited, **unmarked** (SCOPE): `rem:btz_pas_tarentin` — `ETT.tex:1358`,
`rem:sing_tarentin` — `ETT.tex:1364`. For a singular `(Isom(𝐌³), 𝐌³)`-manifold `M` (DEC-25) and
**every absolutely minimal causality `C` with an isomorphic chart at each point** over the whole
family `E_{≥0}` (`IsoChartsCoverDEC25 … massAModelCausality`: a chart of the maximal a.e. atlas
onto `𝐌³`, or an `X_A`-chart onto `E₀` or onto an `E_κ`, `κ > 0`), the fields of
`Causal.Causality.SingularFlatAxioms` that are read in a chart, with `sing_α(M)` defined through
the `X_A`-charts. The instance at the family of the model-free transfer `Causal.SFATransfer`; the
`E₀`-manifold case `Causal.Port.SFALocalE0` is a special case (`sing_eq_of_e0Covered`,
`isoChartsCoverDEC25_of_e0`). No existence half is used.

> Every point of a $\mass{\geq 0}$-manifold is strongly tarentin in the future, and the points
> which fail to be strongly tarentin in the past are exactly the BTZ points: this is immediate
> from Definitions \ref{defi:causal_Ealpha} and \ref{defi:causal_E0} read in a chart.
> (`rem:btz_pas_tarentin`, `ETT.tex:1358–1362`)

> Every $\mass{\geq0}$-manifold is a tarentin topological spacetime. (`rem:sing_tarentin`,
> `ETT.tex:1364–1366`)

> Let $M$ be a $\mass{\geq 0}$-manifold and let $x\in \sing(M)$. There exists exactly one
> $\alpha\geq 0$ such that $x$ is locally modeled on $\mass{\alpha}$.
> (`brunswic2021cauchy`, Cor. 1.5, `papers/gx/sources/2108.12631/src/BTZ_1.tex:388–389`)

## What is proved (no `sorry` in this file)

* **`E_κ`'s model facts in local form** (`κ > 0`): `massive_locZplus`, `massive_locZminus`
  (off `∅`), `massive_locTarentin` (from `massive_causallyArcConnected`, `massive_stronglyCausal`),
  `massive_nhdsNE_neBot`; over the family: `massAModel_locZplus`, `massAModel_locZminus` (off
  `modelBTZ`: the axis of `E₀`, nothing in `E_κ`), `massAModel_locTarentin`,
  `massAModel_locallyCompactSpace`, `massAModel_nhdsNE_neBot`.
* **`sing_α(M)`** (`sing`): the points an `X_A`-chart into the model of angle `α` (`angle`: `0` at
  `E₀`, `κ` at `E_κ`) sends to that model's singular locus. Read: `sing_zero_eq` (`sing₀(M)` = the
  points some `X_A`-chart into `E₀` sends to the axis), `sing_pos_eq` (`κ > 0`, `κ ≠ 2π`: to the
  line of `E_κ`), `sing_two_pi` (`= ∅`), `sing_of_neg`. **Type invariance** (BTZ_1 Cor. 1.5, l.388–389):
  `eq_of_mem_singAt` (one model per singular point: cross-type by
  `MassAModelsInstance.source_subset_reg_of_isAEChart_e0_massive`/`_massive_e0`, `κ′ = κ` by
  `BPrimeEAlpha.eq_of_isAEChart`), so the `sing_α(M)` are disjoint (`disjoint_sing`), read in any
  `X_A`-chart (`mem_sing_iff_of_mem_source`), cover `Sing(M)` (`mem_sing_iff`), each open in
  `Sing(M)` (`exists_isOpen_sing_eq_inter`), and a BTZ point lies in no chart into an `E_κ`
  (`eq_none_of_mem_sing_zero`).
* **Chart facts, no absolute minimality**: `Z⁺ = M` (`mem_Zplus`, `locZplus`), tarentin
  (`tarentin`, `locTarentin`), `M ∖ sing₀(M) ⊆ Z⁻` (`mem_Zminus_of_notMem`, `locZminus`),
  `past_local` (`pastLocal`, through `exists_chartIso_e0`).
* **The BTZ half, absolute minimality**: `I⁻(p) = ∅` at every BTZ point (`Iminus_eq_empty`), hence
  `p ∈ Z⁻ ↔ p ∉ sing₀(M)` (`mem_Zminus_iff`); assembled: `btz_pas_tarentin`.
* **Topology** (from the `X_A`-charts, `MassACovered M`, which the cover implies:
  `massACovered_of_isoChartsCover`): `locallyCompactSpace`, `nhdsNE_neBot`, `metrizableSpace`
  (with the carried T2, second countable), `isClosed_sing`, `interior_sing`.
* **More**: `pushUp`, `causallyArcConnected` (DEC-25 corollaries), `causallyPlain`;
  `singularFlatAxioms_iff`: for `M` T2 and second countable, `C.SingularFlatAxioms (sing M)` iff the
  four line fields not proved here (`singularPastAt`, `Iplus_of_lt`, `line`, `massive_line`);
  `of_isAtlasCausalityDEC25`: the natural causality satisfies the hypotheses.
* **Witnesses** (kb/0011): `nonvacuous_e0` (`E₀`, `sing₀ = axis ≠ ∅`; `sing_e0`,
  `e0_singularFlatAxioms`), `nonvacuous_epi` (`E_π`, `sing_π = line ≠ ∅`, `sing₀ = ∅`);
  `sing_model` computes `sing` at every model.

## Hypothesis checklist

| paper | here |
|---|---|
| `E_{≥0}`-manifold | ⚠ read (DEC-25): `[SingularGXStructure (Flat.isom 2) (Minkowski 2) M]`, its singular points in `X_A`-charts into the family (`MassACovered M`, implied by the next row) |
| its causality (`defi:causal_Ealpha`, l.1339–1340) | ⚠ read (OQ-18): any absolutely minimal `C` with an isomorphic chart at each point (`IsoChartsCoverDEC25`); the natural one is one (`of_isAtlasCausalityDEC25`) and, when it exists, the only one (`massA_causalite_unique_dec25`); minimality is used by the BTZ half only |
| « BTZ points », `sing_α(M)` | ⚠ read: `sing M α` through the `X_A`-charts (brunswic2021cauchy Cor. 1.5); `sing_{2π}(M) = ∅`, settled by DEC-25's computed `Sing` (`EAlphaGX.sing_eq_empty_two_pi`) and DEC-74 (`E_{2π}` is regular) |
| « topological spacetime »: Hausdorff, second countable (`ETT.tex:254`) | ✓ carried by `metrizableSpace` and `singularFlatAxioms_iff` only, as part of « manifold » (`RamcovGX.tex:474`, the definition DEC-25 adopts); `tarentin`, `mem_Zplus`, `mem_Zminus_iff` take neither |
| `E₀` (l.1330), `Isom(E^{1,2})` | ⚠ read: `Causal.E0` (OQ-34, OQ-35), `Flat.isom 2 = SO₀(1,2) ⋉ ℝ³` (OQ-82) |

## SCOPE (disclosed)

* **Why unmarked.** OQ-18 (« its causality », and the BTZ half uses absolute minimality),
  OQ-34/OQ-35 (`E₀`), OQ-82 (the group); Hausdorff and second countable are carried.
* **What each half uses.** `Z⁺`, tarentin, `Z⁻` off `sing₀(M)` are chart facts; `past_local` takes no
  minimality but uses the cross-type invariance (`exists_chartIso_e0`).
  `I⁻(p) = ∅` at a BTZ point uses absolute minimality (kb/0135, `SFALocalE0.e0_topTotal_separates`)
  **and** the cross-type invariance: the members of the cover through `p` must be sources of charts
  into `E₀`, and no `X_A`-chart into an `E_κ` reaches `p` (`eq_none_of_mem_sing_zero`). Under the every-chart
  reading (`IsAtlasCausalityDEC25`) the exclusion follows from the local model facts in two charts;
  `eq_none_of_mem_sing_zero` is needed because the hypothesis here is one isomorphic chart at each point.
* **`sing_α(M)`** is not defined in `ETT.tex`; it is read from `brunswic2021cauchy` (Cor. 1.5, BTZ_1
  l.388–389, « locally modeled on `E_α` ») as the points an `X_A`-chart sends to the singular locus of a
  model of angle `α`, with `Sing(E_{2π}) = ∅`. Read with the line `{r = 0}` of `E_{2π}` instead,
  `sing_{2π}(M)` would contain regular points (through charts composed with translations), and with
  the convention « `α = 2π` if `p` is regular » (`ETT.tex:2185`, OQ-25's subject) it would contain
  `Reg(M)`, a non-empty open set; both contradict `interior_sing` and `prop:GX_sing_dec` (l.1437).
  Not open: DEC-25's computed `Sing`, `EAlphaGX.sing_eq_empty_two_pi` and DEC-74 settle `∅`.
* **Not proved here**: the line fields `singularPastAt`, `Iplus_of_lt`, `line`, `massive_line`
  (`singularFlatAxioms_iff` shows they are all that is missing); the existence of the natural
  causality (T-ett-e-models-bprime). No witness has points of both kinds (no disjoint union of
  singular structures in the library); `E₀` and `E_π` witness each kind.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Template
`Causal.Port.SFALocalE0` (T-ett-sfa-local-e0), imported.
-/

namespace Causal

open Set Filter Topology TopologicalSpace

universe u

namespace SFALocal

open SFATransfer MassAModelsInstance

/-! ### The local model facts of `E_κ`, `κ > 0` -/

section Massive

variable {α : ℝ} [Fact (0 < α)]

theorem massive_locZplus : E0LM.LocZplus (massive α) := by
  refine E0LM.locZplus_of massive_causallyArcConnected massive_stronglyCausal fun y => ?_
  rw [massive_Zplus]
  exact mem_univ y

theorem massive_locZminus : E0LM.LocZminus (massive α) ∅ := by
  refine E0LM.locZminus_of massive_causallyArcConnected massive_stronglyCausal fun y _ => ?_
  rw [massive_Zminus]
  exact mem_univ y

theorem massive_locTarentin : E0LM.LocTarentin (massive α) := by
  exact E0LM.locTarentin_of massive_causallyArcConnected massive_stronglyCausal massive_tarentin

omit [Fact (0 < α)] in
/-- No point of `ℝ × X` is isolated (move along the time factor). -/
theorem massive_nhdsNE_neBot (y : Massive α) : (𝓝[≠] y).NeBot := by
  have h : Tendsto (fun s : ℝ => ((s, y.2) : Massive α)) (𝓝[≠] y.1) (𝓝[≠] y) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hc : Continuous fun s : ℝ => ((s, y.2) : Massive α) :=
        continuous_id.prodMk continuous_const
      exact (hc.tendsto y.1).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact fun h => hs (congrArg Prod.fst h)
  exact h.neBot

end Massive

/-! ### The family `E_{≥0}` -/

/-- The cone angle of a model: `0` at `E₀`, `κ` at `E_κ`. -/
def angle : Option {κ : ℝ // 0 < κ} → ℝ
  | none => 0
  | some κ => κ.1

theorem angle_injective : Function.Injective angle := by
  rintro (_ | ⟨κ, hκ⟩) (_ | ⟨κ', hκ'⟩) h
  · rfl
  · exact absurd h.symm (ne_of_gt hκ')
  · exact absurd h (ne_of_gt hκ)
  · have h' : κ = κ' := h
    subst h'
    rfl

theorem angle_nonneg : ∀ o, 0 ≤ angle o
  | none => le_rfl
  | some κ => κ.2.le

/-- The set of a model that is not strongly tarentin in the past: the axis of `E₀`, nothing in
`E_κ`. -/
def modelBTZ : ∀ o, Set (MassAModel o)
  | none => E0.axis
  | some _ => ∅

theorem massAModel_locZplus : ∀ o, E0LM.LocZplus (massAModelCausality o)
  | none => E0LM.e0_locZplus
  | some κ => @massive_locZplus κ.1 ⟨κ.2⟩

theorem massAModel_locZminus : ∀ o, E0LM.LocZminus (massAModelCausality o) (modelBTZ o)
  | none => E0LM.e0_locZminus
  | some κ => @massive_locZminus κ.1 ⟨κ.2⟩

theorem massAModel_locTarentin : ∀ o, E0LM.LocTarentin (massAModelCausality o)
  | none => E0LM.e0_locTarentin
  | some κ => @massive_locTarentin κ.1 ⟨κ.2⟩

theorem massAModel_locallyCompactSpace : ∀ o, LocallyCompactSpace (MassAModel o)
  | none => inferInstanceAs (LocallyCompactSpace E0)
  | some κ => haveI : Fact (0 < κ.1) := ⟨κ.2⟩; inferInstanceAs (LocallyCompactSpace (Massive κ.1))

theorem massAModel_nhdsNE_neBot : ∀ o (y : MassAModel o), (𝓝[≠] y).NeBot
  | none, y => inferInstanceAs ((𝓝[≠] (y : E0)).NeBot)
  | some κ, y => massive_nhdsNE_neBot (α := κ.1) y

section ModelSing

attribute [local instance] E0GX.singularGX

/-- `Sing(E₀)` is the axis, as a membership. -/
theorem mem_sing_e0_iff (y : E0) : y ∈ Sing (Flat.isom 2) (Minkowski 2) E0 ↔ y ∈ E0.axis := by
  rw [E0GX.sing_eq]

end ModelSing

section ModelSingMassive

attribute [local instance] EAlphaGX.singularGX

/-- A singular point of `E_κ` is on its line, and then `κ ≠ 2π`. -/
theorem massive_mem_sing {κ : ℝ} [Fact (0 < κ)] {y : Massive κ}
    (hy : y ∈ Sing (Flat.isom 2) (Minkowski 2) (Massive κ)) : κ ≠ 2 * Real.pi ∧ y ∈ singLine κ := by
  rcases EAlphaGX.reg_sing_cases (α := κ) with ⟨hκ, -, hS⟩ | ⟨-, -, hS⟩
  · rw [hS] at hy
    exact ⟨hκ, hy⟩
  · rw [hS] at hy
    exact absurd hy (notMem_empty _)

end ModelSingMassive

/-! ### `E_{≥0}`-manifolds and `sing_α(M)` -/

section Manifold

variable {M : Type u} [TopologicalSpace M] [SingularGXStructure (Flat.isom 2) (Minkowski 2) M]

variable (M) in
/-- **An `E_{≥0}`-manifold** (DEC-25): its singular points lie in a.e. isomorphism charts into
models of the family (the `hcov` of `massA_singular_models`). -/
def MassACovered : Prop :=
  ∀ x ∈ Sing (Flat.isom 2) (Minkowski 2) M, ∃ o, ∃ e : OpenPartialHomeomorph M (MassAModel o),
    IsAEChart (Flat.isom 2) (Minkowski 2) e ∧ x ∈ e.source

variable (M) in
/-- The points an `X_A`-chart into the model `o` sends to the model's singular locus. -/
def singAt (o : Option {κ : ℝ // 0 < κ}) : Set M :=
  {x | ∃ e : OpenPartialHomeomorph M (MassAModel o), IsAEChart (Flat.isom 2) (Minkowski 2) e ∧
    x ∈ e.source ∧ e x ∈ Sing (Flat.isom 2) (Minkowski 2) (MassAModel o)}

variable (M) in
/-- **`sing_α(M)`**: the points an `X_A`-chart into the model of angle `α` sends to its singular
locus (the axis of `E₀` at `α = 0`, the line of `E_α` for `α > 0`, `α ≠ 2π`; empty otherwise). -/
def sing (α : ℝ) : Set M := {x | ∃ o, angle o = α ∧ x ∈ singAt M o}

theorem singAt_subset_sing (o : Option {κ : ℝ // 0 < κ}) :
    singAt M o ⊆ Sing (Flat.isom 2) (Minkowski 2) M := by
  rintro x ⟨e, he, hx, hxs⟩
  show x ∉ Reg (Flat.isom 2) (Minkowski 2) M
  exact fun hxr => hxs ((he.mem_reg_iff hx).1 hxr)

theorem mem_singAt_of_mem_source {o : Option {κ : ℝ // 0 < κ}}
    {e : OpenPartialHomeomorph M (MassAModel o)} (he : IsAEChart (Flat.isom 2) (Minkowski 2) e)
    {x : M} (hx : x ∈ e.source) (hxs : x ∈ Sing (Flat.isom 2) (Minkowski 2) M) :
    x ∈ singAt M o :=
  ⟨e, he, hx, fun h => hxs ((he.mem_reg_iff hx).2 h)⟩

/-- **Type invariance**: a singular point is read in one model only. -/
theorem eq_of_mem_singAt {o o' : Option {κ : ℝ // 0 < κ}} {x : M} (h : x ∈ singAt M o)
    (h' : x ∈ singAt M o') : o = o' := by
  obtain ⟨e, he, hx, hxs⟩ := h
  obtain ⟨e', he', hx', hxs'⟩ := h'
  have hχ := he.symm.trans he'
  have hmem : e x ∈ (e.symm.trans e').source := by
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨e.map_source hx, ?_⟩
    show e.symm (e x) ∈ e'.source
    rw [e.left_inv hx]
    exact hx'
  rcases o with _ | κ <;> rcases o' with _ | κ'
  · rfl
  · exact absurd (source_subset_reg_of_isAEChart_e0_massive (κ := κ') hχ hmem) hxs
  · exact absurd (source_subset_reg_of_isAEChart_massive_e0 (κ := κ) hχ hmem) hxs
  · haveI : Fact (0 < κ.1) := ⟨κ.2⟩
    haveI : Fact (0 < κ'.1) := ⟨κ'.2⟩
    obtain ⟨hκ, hline⟩ := massive_mem_sing (κ := κ.1) hxs
    have h := BPrimeEAlpha.eq_of_isAEChart hκ hχ hmem hline
    exact congrArg some (Subtype.ext h.symm)

theorem sing_subset (α : ℝ) : sing M α ⊆ Sing (Flat.isom 2) (Minkowski 2) M := by
  rintro x ⟨o, -, hx⟩
  exact singAt_subset_sing o hx

theorem sing_zero : sing M 0 = singAt M none := by
  ext x
  constructor
  · rintro ⟨o, ho, hx⟩
    obtain rfl : o = none := angle_injective (ho.trans rfl)
    exact hx
  · exact fun hx => ⟨none, rfl, hx⟩

theorem sing_pos (κ : {κ : ℝ // 0 < κ}) : sing M κ.1 = singAt M (some κ) := by
  ext x
  constructor
  · rintro ⟨o, ho, hx⟩
    obtain rfl : o = some κ := angle_injective (ho.trans rfl)
    exact hx
  · exact fun hx => ⟨some κ, rfl, hx⟩

theorem sing_of_neg {α : ℝ} (hα : α < 0) : sing M α = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun x hx => ?_
  obtain ⟨o, ho, -⟩ := hx
  linarith [angle_nonneg o]

/-- **The `sing_α(M)` are pairwise disjoint** (type invariance). -/
theorem disjoint_sing {α β : ℝ} (h : α ≠ β) : Disjoint (sing M α) (sing M β) := by
  rw [Set.disjoint_left]
  rintro x ⟨o, rfl, hx⟩ ⟨o', rfl, hx'⟩
  exact h (congrArg angle (eq_of_mem_singAt hx hx'))

/-- **`sing_α(M)` read in any `X_A`-chart**: a singular point in the source of an `X_A`-chart into
the model `o` is in `sing_α(M)` iff `α` is the angle of `o`. -/
theorem mem_sing_iff_of_mem_source {o : Option {κ : ℝ // 0 < κ}}
    {e : OpenPartialHomeomorph M (MassAModel o)} (he : IsAEChart (Flat.isom 2) (Minkowski 2) e)
    {x : M} (hx : x ∈ e.source) (hxs : x ∈ Sing (Flat.isom 2) (Minkowski 2) M) (α : ℝ) :
    x ∈ sing M α ↔ angle o = α := by
  constructor
  · rintro ⟨o', rfl, hx'⟩
    rw [eq_of_mem_singAt (mem_singAt_of_mem_source he hx hxs) hx']
  · rintro rfl
    exact ⟨o, rfl, mem_singAt_of_mem_source he hx hxs⟩

/-- **`sing_α(M)` is open in `Sing(M)`**: the trace on `Sing(M)` of the union of the sources of
the `X_A`-charts into the model of angle `α`. -/
theorem exists_isOpen_sing_eq_inter (α : ℝ) :
    ∃ V : Set M, IsOpen V ∧ sing M α = V ∩ Sing (Flat.isom 2) (Minkowski 2) M := by
  refine ⟨⋃ (o : Option {κ : ℝ // 0 < κ}) (_ : angle o = α)
    (e : OpenPartialHomeomorph M (MassAModel o)) (_ : IsAEChart (Flat.isom 2) (Minkowski 2) e),
      e.source, ?_, ?_⟩
  · exact isOpen_iUnion fun o => isOpen_iUnion fun _ => isOpen_iUnion fun e =>
      isOpen_iUnion fun _ => e.open_source
  · ext x
    simp only [mem_inter_iff, mem_iUnion]
    constructor
    · rintro ⟨o, ho, e, he, hx, hxs⟩
      exact ⟨⟨o, ho, e, he, hx⟩, singAt_subset_sing o ⟨e, he, hx, hxs⟩⟩
    · rintro ⟨⟨o, ho, e, he, hx⟩, hxs⟩
      exact ⟨o, ho, mem_singAt_of_mem_source he hx hxs⟩

/-- **`Sing(M)` is the union of the `sing_α(M)`, `α ≥ 0`**, at an `E_{≥0}`-manifold. -/
theorem mem_sing_iff (hcov : MassACovered M) (x : M) :
    x ∈ Sing (Flat.isom 2) (Minkowski 2) M ↔ ∃ α, 0 ≤ α ∧ x ∈ sing M α := by
  constructor
  · intro hx
    obtain ⟨o, e, he, hxe⟩ := hcov x hx
    exact ⟨angle o, angle_nonneg o, o, rfl, mem_singAt_of_mem_source he hxe hx⟩
  · rintro ⟨α, -, hx⟩
    exact sing_subset α hx

section ReadE0

attribute [local instance] E0GX.singularGX

/-- **`sing₀(M)` is the set of BTZ points**: the points some `X_A`-chart into `E₀` sends to the
axis. -/
theorem sing_zero_eq :
    sing M 0 = {x | ∃ e : OpenPartialHomeomorph M E0, IsAEChart (Flat.isom 2) (Minkowski 2) e ∧
      x ∈ e.source ∧ e x ∈ E0.axis} := by
  rw [sing_zero]
  ext x
  constructor
  · rintro ⟨e, he, hx, hxs⟩
    exact ⟨e, he, hx, (mem_sing_e0_iff _).1 hxs⟩
  · rintro ⟨e, he, hx, hxa⟩
    exact ⟨e, he, hx, (mem_sing_e0_iff _).2 hxa⟩

end ReadE0

section ReadEAlpha

attribute [local instance] EAlphaGX.singularGX

/-- **`sing_κ(M)`, `κ > 0`, `κ ≠ 2π`**: the points some `X_A`-chart into `E_κ` sends to its
singular line. -/
theorem sing_pos_eq {κ : ℝ} [Fact (0 < κ)] (hκ : κ ≠ 2 * Real.pi) :
    sing M κ = {x | ∃ e : OpenPartialHomeomorph M (Massive κ),
      IsAEChart (Flat.isom 2) (Minkowski 2) e ∧ x ∈ e.source ∧ e x ∈ singLine κ} := by
  have h := sing_pos (M := M) ⟨κ, Fact.out⟩
  simp only at h
  rw [h]
  ext x
  constructor
  · rintro ⟨e, he, hx, hxs⟩
    exact ⟨e, he, hx, (massive_mem_sing hxs).2⟩
  · rintro ⟨e, he, hx, hxl⟩
    refine ⟨e, he, hx, ?_⟩
    show e x ∈ Sing (Flat.isom 2) (Minkowski 2) (Massive κ)
    rw [EAlphaGX.sing_eq hκ]
    exact hxl

end ReadEAlpha

/-- `sing_{2π}(M) = ∅`: `E_{2π}` has no singular point. -/
theorem sing_two_pi : sing M (2 * Real.pi) = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun x hx => ?_
  obtain ⟨o, ho, e, -, -, hxs⟩ := hx
  rcases o with _ | κ
  · exact absurd ho (by simp [angle, Real.pi_pos.ne'])
  · haveI : Fact (0 < κ.1) := ⟨κ.2⟩
    exact (massive_mem_sing (κ := κ.1) hxs).1 ho

/-- **A BTZ point lies in no `X_A`-chart into an `E_κ`**, `κ > 0` (cross-type invariance,
`MassAModelsInstance.source_subset_reg_of_isAEChart_e0_massive`). -/
theorem eq_none_of_mem_sing_zero {o : Option {κ : ℝ // 0 < κ}}
    {e : OpenPartialHomeomorph M (MassAModel o)}
    (he : IsAEChart (Flat.isom 2) (Minkowski 2) e) {p : M} (hp : p ∈ sing M 0)
    (hpe : p ∈ e.source) : o = none := by
  rw [sing_zero] at hp
  exact eq_of_mem_singAt (mem_singAt_of_mem_source he hpe (singAt_subset_sing none hp)) hp

/-- **A causality with an isomorphic chart at each point makes `M` an `E_{≥0}`-manifold**: the
charts of the maximal a.e. atlas have regular sources, so the singular points lie in
`X_A`-charts. -/
theorem massACovered_of_isoChartsCover {C : Causality M}
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) :
    MassACovered M := by
  intro x hx
  rcases hC x with ⟨e, he, hxe, -⟩ | ⟨o, e, he, hxe, -⟩
  · exact absurd (mem_support.2 ⟨e, he, hxe⟩) hx
  · exact ⟨o, e, he, hxe⟩

/-! ### The chart facts: no absolute minimality -/

variable {C : Causality M}

theorem locZplus (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) :
    E0LM.LocZplus C := by
  exact IsoChartsCover.locZplus (SFALocalE0.isoChartsCover_of_dec25 hC)
    (SFALocalE0.minkowski_locZplus 2) massAModel_locZplus

/-- `rem:btz_pas_tarentin`, first half (unmarked): every point is strongly tarentin in the
future. -/
theorem mem_Zplus (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (p : M) : p ∈ C.Zplus := by
  exact IsoChartsCover.mem_Zplus (SFALocalE0.isoChartsCover_of_dec25 hC)
    (SFALocalE0.minkowski_locZplus 2) massAModel_locZplus p

theorem locTarentin
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) :
    E0LM.LocTarentin C := by
  exact IsoChartsCover.locTarentin (SFALocalE0.isoChartsCover_of_dec25 hC)
    (SFALocalE0.minkowski_locTarentin 2) massAModel_locTarentin

/-- `rem:sing_tarentin` (unmarked): tarentin. -/
theorem tarentin (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) :
    C.Tarentin := by
  exact IsoChartsCover.tarentin (SFALocalE0.isoChartsCover_of_dec25 hC)
    (SFALocalE0.minkowski_locTarentin 2) massAModel_locTarentin

theorem locZminus (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) :
    E0LM.LocZminus C (sing M 0) := by
  refine locZminus_of_charts (SX := ∅) (SY := modelBTZ) (fun x hx => ?_)
    (SFALocalE0.minkowski_locZminus 2) massAModel_locZminus
  rcases hC x with ⟨e, -, hxe, he⟩ | ⟨o, e, hea, hxe, he⟩
  · exact Or.inl ⟨e, hxe, he, notMem_empty _⟩
  · refine Or.inr ⟨o, e, hxe, he, ?_⟩
    rcases o with _ | κ
    · intro hax
      apply hx
      rw [sing_zero]
      exact ⟨e, hea, hxe, (mem_sing_e0_iff _).2 hax⟩
    · exact notMem_empty _

/-- **`M ∖ sing₀(M) ⊆ Z⁻`**. -/
theorem mem_Zminus_of_notMem
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) {p : M}
    (hp : p ∉ sing M 0) : p ∈ C.Zminus := by
  intro U hU
  obtain ⟨z, hzU, hz⟩ := locZminus hC ⊤ p trivial hp U hU
  exact ⟨z, Precausality.mem_Iminus_singleton.2 hz, hzU⟩

section E0Chart

attribute [local instance] E0GX.singularGX

/-- At a BTZ point the isomorphic charts go into `E₀`. -/
theorem exists_chartIso_e0
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) {p : M}
    (hp : p ∈ sing M 0) :
    ∃ e : OpenPartialHomeomorph M E0, IsAEChart (Flat.isom 2) (Minkowski 2) e ∧
      p ∈ e.source ∧ ChartIso C E0.causality e := by
  rcases hC p with ⟨e, he, hpe, -⟩ | ⟨o, e, hea, hpe, he⟩
  · exact absurd (mem_support.2 ⟨e, he, hpe⟩) (sing_subset 0 hp)
  · obtain rfl := eq_none_of_mem_sing_zero hea hp hpe
    exact ⟨e, hea, hpe, he⟩

/-- **`past_local`**. -/
theorem pastLocal (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) :
    ∀ p ∈ sing M 0, ∃ U : Opens M, p ∈ U ∧ ∀ q, C.le U q p → q ∈ sing M 0 := by
  intro p hp
  obtain ⟨e, he, hpe, hiso⟩ := exists_chartIso_e0 hC hp
  refine ChartIso.pastLocal hiso E0LM.e0_locPastIn (fun q hq hqa => ?_) hpe
    ((SFALocalE0.mem_axis_iff he hpe).2 (sing_subset 0 hp))
  rw [sing_zero_eq]
  exact ⟨e, he, hq, hqa⟩

/-! ### The BTZ half: absolute minimality -/

/-- **`I⁻(p) = ∅` at every BTZ point.** -/
theorem Iminus_eq_empty (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) :
    ∀ p ∈ sing M 0, C.Iminus ⊤ {p} = ∅ := by
  intro p hp
  refine Iminus_eq_empty_of_cover hmin
    (S := {O | (∃ e ∈ aeAtlas (Flat.isom 2) (Minkowski 2) M, O = chartSource e) ∨
      ∃ o, ∃ e : OpenPartialHomeomorph M (MassAModel o),
        IsAEChart (Flat.isom 2) (Minkowski 2) e ∧ ChartIso C (massAModelCausality o) e ∧
          O = chartSource e}) (fun y => ?_) ?_
  · rcases hC y with ⟨e, he, hye, -⟩ | ⟨o, e, hea, hye, he⟩
    · exact ⟨chartSource e, Or.inl ⟨e, he, rfl⟩, hye⟩
    · exact ⟨chartSource e, Or.inr ⟨o, e, hea, he, rfl⟩, hye⟩
  · rintro O (⟨e, he, rfl⟩ | ⟨o, e, hea, he, rfl⟩) hpO z
    · exact absurd (mem_support.2 ⟨e, he, hpO⟩) (sing_subset 0 hp)
    · obtain rfl := eq_none_of_mem_sing_zero hea hp hpO
      exact ChartIso.not_lt_left he E0LM.e0_locNoPast
        ((SFALocalE0.mem_axis_iff hea hpO).2 (sing_subset 0 hp)) le_rfl z

/-- **The `E₀`-manifolds of `Causal.SFALocalE0` are a special case**: their `sing` is this
file's. -/
theorem sing_eq_of_e0Covered (hcov : SFALocalE0.E0Covered M) : sing M = SFALocalE0.sing M := by
  funext α
  by_cases hα : α = 0
  · subst hα
    exact sing_zero_eq.trans (SFALocalE0.sing_eq_btzPoints hcov).symm
  · rw [SFALocalE0.sing_of_ne hα]
    refine eq_empty_iff_forall_notMem.2 fun x hx => ?_
    have hxs := sing_subset α hx
    obtain ⟨e, he, hxe⟩ := hcov x hxs
    have h0 : x ∈ sing M 0 :=
      (mem_sing_iff_of_mem_source (o := none) (e := e) he hxe hxs 0).2 rfl
    exact Set.disjoint_left.1 (disjoint_sing (M := M) (Ne.symm hα)) h0 hx

/-- **The natural causality of an `E₀`-manifold has an isomorphic chart at each point over the
whole family.** -/
theorem isoChartsCoverDEC25_of_e0 (hcov : SFALocalE0.E0Covered M)
    (hC : SFALocalE0.IsE0Natural C) :
    IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality := by
  intro x
  rcases SFALocalE0.isoChartsCoverDEC25 hcov hC x with h | ⟨_, e, he, hxe, hiso⟩
  · exact Or.inl h
  · exact Or.inr ⟨none, e, he, hxe, hiso⟩

end E0Chart

/-- `rem:btz_pas_tarentin`, second half (unmarked). -/
theorem mem_Zminus_iff (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) (p : M) :
    p ∈ C.Zminus ↔ p ∉ sing M 0 := by
  exact ⟨fun h hp => notMem_Zminus_of_Iminus_eq_empty (Iminus_eq_empty hmin hC p hp) h,
    mem_Zminus_of_notMem hC⟩

/-- **`rem:btz_pas_tarentin` at every `E_{≥0}`-manifold** (unmarked, SCOPE): every point is
strongly tarentin in the future, and the points not strongly tarentin in the past are exactly the
BTZ points `sing₀(M)`. The first half and `M ∖ sing₀(M) ⊆ Z⁻` are chart facts; `sing₀(M) ∩ Z⁻ = ∅`
uses absolute minimality. -/
theorem btz_pas_tarentin (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) :
    (∀ p, p ∈ C.Zplus) ∧ ∀ p, p ∈ C.Zminus ↔ p ∉ sing M 0 :=
  ⟨mem_Zplus hC, mem_Zminus_iff hmin hC⟩

/-! ### Topology -/

theorem locallyCompactSpace (hcov : MassACovered M) : LocallyCompactSpace M := by
  refine ⟨fun x n hn => ?_⟩
  by_cases hx : x ∈ Reg (Flat.isom 2) (Minkowski 2) M
  · obtain ⟨e, -, hxe⟩ := mem_support.1 hx
    exact exists_isCompact_nhds_of_chart e hxe hn
  · obtain ⟨o, e, -, hxe⟩ := hcov x hx
    haveI := massAModel_locallyCompactSpace o
    exact exists_isCompact_nhds_of_chart e hxe hn

theorem nhdsNE_neBot (hcov : MassACovered M) (p : M) : (𝓝[≠] p).NeBot := by
  by_cases hp : p ∈ Reg (Flat.isom 2) (Minkowski 2) M
  · obtain ⟨e, -, hpe⟩ := mem_support.1 hp
    exact nhdsNE_neBot_of_chart e hpe inferInstance
  · obtain ⟨o, e, -, hpe⟩ := hcov p hp
    exact nhdsNE_neBot_of_chart e hpe (massAModel_nhdsNE_neBot o _)

theorem metrizableSpace [T2Space M] [SecondCountableTopology M] (hcov : MassACovered M) :
    MetrizableSpace M := by
  haveI := locallyCompactSpace hcov
  exact metrizableSpace_of_locallyCompact

/-- `sing_α(M)` is closed. -/
theorem isClosed_sing (hcov : MassACovered M) : ∀ α : ℝ, 0 ≤ α → IsClosed (sing M α) := by
  intro α _
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  by_cases hxr : x ∈ Reg (Flat.isom 2) (Minkowski 2) M
  · exact Filter.mem_of_superset ((isOpen_reg (Flat.isom 2) (Minkowski 2) M).mem_nhds hxr)
      fun y hy hys => sing_subset α hys hy
  · obtain ⟨o, e, he, hxe⟩ := hcov x hxr
    have hne : angle o ≠ α := fun h =>
      hx ((mem_sing_iff_of_mem_source he hxe hxr α).2 h)
    exact Filter.mem_of_superset (e.open_source.mem_nhds hxe) fun y hy hys =>
      hne ((mem_sing_iff_of_mem_source he hy (sing_subset α hys) α).1 hys)

/-- `sing_α(M)` has empty interior. -/
theorem interior_sing : ∀ α : ℝ, 0 ≤ α → interior (sing M α) = ∅ := by
  intro α _
  exact eq_empty_of_subset_empty ((interior_mono (sing_subset α)).trans
    (isSkeletal_sing (Flat.isom 2) (Minkowski 2) M).interior_eq_empty.subset)

/-! ### The DEC-25 corollaries and causal plainness -/

theorem pushUp (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) : C.PushUp := by
  exact (massA_dec25_models_of_isoChartsCover hmin hC).2

theorem causallyArcConnected (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) :
    C.CausallyArcConnected := by
  exact (massA_dec25_models_of_isoChartsCover hmin hC).1

theorem causallyPlain (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) :
    C.CausallyPlain := by
  exact Causality.causallyPlain_of_locZ (pushUp hmin hC) (locZplus hC) (locZminus hC)
    (interior_sing 0 le_rfl)

/-- **`SingularFlatAxioms` at a Hausdorff, second countable `E_{≥0}`-manifold is exactly the four
line fields not proved here.** -/
theorem singularFlatAxioms_iff [T2Space M] [SecondCountableTopology M]
    (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) :
    C.SingularFlatAxioms (sing M) ↔
      (∀ p ∈ sing M 0, C.SingularPastAt p) ∧
      (∀ p ∈ sing M 0, ∀ p' ∈ sing M 0, C.le ⊤ p p' → p ≠ p' →
        C.Jplus ⊤ {p'} \ sing M 0 ⊆ C.Iplus ⊤ {p}) ∧
      (∀ p ∈ sing M 0, ∃ γ : ℝ → M, γ 0 = p ∧ (C.IsCausal → IsClosedEmbedding γ) ∧
        C.Inextensible ⊤ univ γ ∧ range γ = connectedComponentIn (sing M 0) p) ∧
      (∀ α : ℝ, 0 < α → ∀ p ∈ sing M α, ∃ γ : ℝ → M, γ 0 = p ∧
        (C.IsCausal → IsClosedEmbedding γ) ∧
        C.Inextensible ⊤ univ γ ∧ (∀ a b, C.ChronalCurveOn ⊤ γ a b) ∧
        range γ = connectedComponentIn (sing M α) p) := by
  have hcov := massACovered_of_isoChartsCover hC
  constructor
  · intro h
    exact ⟨h.singularPastAt, h.Iplus_of_lt, h.line, h.massive_line⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact
      { singularPastAt := h1
        Iminus_eq_empty := Iminus_eq_empty hmin hC
        Iplus_of_lt := h2
        past_local := pastLocal hC
        line := h3
        pushUp := pushUp hmin hC
        absolutelyMinimal := hmin
        causallyArcConnected := causallyArcConnected hmin hC
        tarentin := tarentin hC
        mem_Zplus := mem_Zplus hC
        mem_Zminus_iff := mem_Zminus_iff hmin hC
        t2 := inferInstance
        secondCountable := inferInstance
        metrizable := metrizableSpace hcov
        locallyCompact := locallyCompactSpace hcov
        noIsolated := nhdsNE_neBot hcov
        isClosed_sing := isClosed_sing hcov
        interior_sing := interior_sing
        massive_line := h4 }

/-- The natural causality (`IsAtlasCausalityDEC25`) of an `E_{≥0}`-manifold satisfies the
hypotheses of this file. -/
theorem of_isAtlasCausalityDEC25 (hcov : MassACovered M)
    (hC : IsAtlasCausalityDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) :
    C.AbsolutelyMinimal ∧ IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality :=
  ⟨hC.2.2, hC.isoChartsCover hcov⟩

end Manifold

/-! ### Witnesses: `E₀` and `E_π` -/

/-- **`sing_α` of a model of the family**, as a manifold with its own structure: its singular
locus at its own angle, empty elsewhere (the identity is an `X_A`-chart). -/
theorem sing_model (o₀ : Option {κ : ℝ // 0 < κ}) (α : ℝ) :
    sing (MassAModel o₀) α =
      if angle o₀ = α then Sing (Flat.isom 2) (Minkowski 2) (MassAModel o₀) else ∅ := by
  ext x
  split_ifs with h
  · constructor
    · exact fun hx => sing_subset α hx
    · intro hx
      exact (mem_sing_iff_of_mem_source (e := OpenPartialHomeomorph.refl _) isAEChart_refl
        (mem_univ x) hx α).2 h
  · constructor
    · intro hx
      exact absurd ((mem_sing_iff_of_mem_source (e := OpenPartialHomeomorph.refl _)
        isAEChart_refl (mem_univ x) (sing_subset α hx) α).1 hx) h
    · intro hx
      exact absurd hx (notMem_empty x)

section WitnessE0

attribute [local instance] E0GX.singularGX

/-- `E₀`'s `sing` is `Causal.E0.singE0`. -/
theorem sing_e0 : sing E0 = E0.singE0 := by
  funext α
  have h := sing_model none α
  by_cases hα : α = 0
  · subst hα
    have h0 : sing E0 0 = Sing (Flat.isom 2) (Minkowski 2) E0 := h.trans (if_pos rfl)
    rw [E0.singE0_zero, h0, E0GX.sing_eq]
  · rw [E0.singE0_of_ne hα]
    exact h.trans (if_neg fun h' => hα h'.symm)

/-- **Non-vacuity at `E₀`**: `E0.causality` is absolutely minimal with an isomorphic chart at each
point over the family, and `sing₀(E₀)` is the axis, non-empty. -/
theorem nonvacuous_e0 :
    E0.causality.AbsolutelyMinimal ∧
      IsoChartsCoverDEC25 (Flat.isom 2) E0.causality (minkowski 2) massAModelCausality ∧
      sing E0 0 = E0.axis ∧ (sing E0 0).Nonempty := by
  have h0 : sing E0 0 = E0.axis := by rw [sing_e0, E0.singE0_zero]
  refine ⟨E0.causallyArcConnected.absolutelyMinimal, e0_witness.2.1, h0, ?_⟩
  rw [h0]
  exact ⟨((0 : ℝ), (0 : ℂ)), rfl⟩

/-- `E0.causality` is `SingularFlatAxioms (sing E0)`: both sides of `singularFlatAxioms_iff` hold
at `E₀`. -/
theorem e0_singularFlatAxioms : E0.causality.SingularFlatAxioms (sing E0) := by
  rw [sing_e0]
  exact E0.singularFlatAxioms

end WitnessE0

section WitnessEPi

attribute [local instance] EAlphaGX.singularGX EAlphaGX.fact_pi_pos

/-- **Non-vacuity at `E_π`**: `massive π` is absolutely minimal with an isomorphic chart at each
point over the family, `sing_π(E_π)` is the line, non-empty, and `sing₀(E_π) = ∅`. -/
theorem nonvacuous_epi :
    (massive Real.pi).AbsolutelyMinimal ∧
      IsoChartsCoverDEC25 (Flat.isom 2) (massive Real.pi) (minkowski 2) massAModelCausality ∧
      sing (Massive Real.pi) Real.pi = singLine Real.pi ∧
      (sing (Massive Real.pi) Real.pi).Nonempty ∧ sing (Massive Real.pi) 0 = ∅ := by
  have hπ : Real.pi ≠ 2 * Real.pi := by linarith [Real.pi_pos]
  have h1 := sing_model (some ⟨Real.pi, Real.pi_pos⟩) Real.pi
  have h0 := sing_model (some ⟨Real.pi, Real.pi_pos⟩) 0
  have hl : sing (Massive Real.pi) Real.pi = singLine Real.pi := by
    have h : sing (Massive Real.pi) Real.pi = Sing (Flat.isom 2) (Minkowski 2) (Massive Real.pi) :=
      h1.trans (if_pos rfl)
    rw [h, EAlphaGX.sing_eq hπ]
  refine ⟨massive_absolutelyMinimal, epi_witness.2.1, hl, ?_, ?_⟩
  · rw [hl]
    exact ⟨((0 : ℝ), Cone.apex), rfl⟩
  · exact h0.trans (if_neg fun h => Real.pi_pos.ne' h)

end WitnessEPi

end SFALocal

end Causal
