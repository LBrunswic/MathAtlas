import Causal.Remarks.SingularRowsCauchyExt

/-!
# Second countability from a second countable Cauchy surface at every Hausdorff, connected `E_{≥0}`-manifold

Target `T-ett-sc-cauchy-e0`. Cited, unmarked (SCOPE): `theo:CBG` — `ETT.tex:1884`, of which this
is an input of the `E₀` instance (A2's last field, `secondCountable_of_cauchy`), not a certificate.

For a singular `(Isom(𝐌³), 𝐌³)`-manifold `M` (DEC-25), Hausdorff and connected, and every causality
`C` with an isomorphic chart at each point over the family `E_{≥0}` (`IsoChartsCoverDEC25 …
massAModelCausality`; the natural causality is one), if some Cauchy surface `S` is second
countable then `M` is second countable. No countability is asked of `M`; neither global
hyperbolicity nor absolute minimality is used. This is the conclusion of the field
`secondCountable_of_cauchy` of `Causal.CBG.Geometry` (l.339; `LocalModel`'s at l.625).

> Let $M_0$ be a globally hyperbolic singular flat spacetime. Then $M_0$ admits a maximal Cauchy
> extension, and that extension is unique up to isomorphism.
> (`theo:CBG`, `ETT.tex:1885–1886`)

> The inductive limit $\overline{M_0}$ is Hausdorff and carries a $\mass{\geq0}$-structure, but
> we have not checked that it is \emph{second countable}, hence that it is a topological spacetime in
> the sense of Definition \ref{defi:causalite}. The proof should follow Geroch's argument for
> Lorentzian manifolds, in the appendix of \cite{MR0234703}; this is exactly the point left open in
> \cite[Section~3.4]{thesis}. (`rem:CBG_manquant` (i), `ETT.tex:2346–2350`)

## What is proved (no `sorry` in this file)

* **The models** are second countable: `secondCountableTopology_massAModel` (`E₀ = ℝ × ℂ`;
  `E_κ = ℝ × C_κ`, `C_κ` proper).
* **(a)** `secondCountableTopology_reg`: `Reg(M)` is second countable at every connected, Hausdorff
  singular `(Isom(𝐌³), 𝐌³)`-manifold, no chart cover asked. It is portly, hence connected
  (`IsPortly.isConnected`), and an `(Isom(𝐌³), 𝐌³)`-manifold for its pulled-back maximal a.e.
  atlas (`opensSingularGXStructure`, `reg_opensSingular`, `chartedSpaceOfAtlas`,
  `hasGroupoid_chartedSpaceOfAtlas`), so `Flat.flat_secondCountableTopology` (DEC-49) applies.
* **(b)** `sing_eq_iUnion`: `Sing(M) = ⋃_{α ≥ 0} sing_α(M)`.
* **(c)** `exists_line_development`: the component of `sing_α(M)` through `p` is the continuous
  image of `ℝ` and a neighbourhood of `p` in `sing_α(M)` (`IsLineDevelopment.local_onto`);
  `exists_isOpen_inter_sing_subset`: it is open in `Sing(M)`.
* **(d)** `isLindelof_component`; `existsUnique_mem_component_inter`: each component meets every
  Cauchy surface in exactly one point, being the range of an inextensible causal curve over `ℝ`
  (`SFALine.line`, `SFAMassiveLine.massive_line`).
* **(e)** `countable_sing_inter`: `Sing(M) ∩ S` is a discrete subspace of `S`, hence countable
  when `S` is second countable; `countable_components`: there are countably many singular
  components; `sing_eq_sUnion_components`, `isLindelof_sing`.
* **(f)** `exists_isOpen_secondCountable` (a chart source around each point);
  `secondCountableTopology_of_isCauchySurface`: `M = Reg(M) ∪ Sing(M)` is Lindelöf, and a countable
  subcover by chart sources gives `secondCountableTopology_of_countable_cover`. The field's form
  `secondCountable_of_cauchy`, and the natural causality's
  `secondCountable_of_cauchy_of_isAtlasCausalityDEC25`.
* **Witnesses** (kb/0011), each conclusion out of the `M`-level theorem: `nonvacuous_e0` (`E₀`,
  `S = T⁻¹(0)` for a Cauchy time function `T`, a BTZ point on `S`), `nonvacuous_e0_natural`,
  `nonvacuous_sublevel` (`{T < 1}` of `Causal.Remarks.SingularRowsCauchyExt`, with
  `S = i⁻¹(T⁻¹(0))` and a BTZ point on it).

## Hypothesis checklist

| the field `secondCountable_of_cauchy` (`Causal/CBG/Geometry.lean:339`) | here |
|---|---|
| an admissible spacetime of the geometry, an `E_{≥0}`-manifold | ⚠ read (DEC-25, OQ-18): `[SingularGXStructure (Flat.isom 2) (Minkowski 2) M]`, `C` with `IsoChartsCoverDEC25` over `massAModelCausality`; the natural causality in `…_of_isAtlasCausalityDEC25` |
| `[T2Space M]` | ✓ carried: the line developments and the flat theorem on `Reg(M)` use it |
| `[ConnectedSpace M]` | ✓ carried: `Reg(M)` connected, for the flat theorem |
| no `SecondCountableTopology M` | ✓ none asked |
| `C` globally hyperbolic | ⚠ weakened: not used (taken and dropped by `secondCountable_of_cauchy`) |
| `S` a Cauchy surface (DEC-14), `SecondCountableTopology S` | ✓ carried |
| `C` absolutely minimal | — asked neither by the field nor here |
| `E₀`, `Isom(E^{1,2})` | ⚠ read: `Causal.E0` (OQ-34, OQ-35), `Flat.isom 2` (OQ-82) |

## SCOPE (disclosed)

* **Why unmarked.** `theo:CBG` is named because this is an input of the `E₀` instance of its
  geometry (T-ett-cbg-e0); no statement of the paper asserts it, and `rem:CBG_manquant` (i) lists
  it as unchecked for the limit. Every theorem at `M` rests on DEC-25 and the readings OQ-18,
  OQ-34/OQ-35, OQ-82.
* **Exactly the field's form.** `secondCountable_of_cauchy` concludes
  `C.GloballyHyperbolic → ∀ S, C.IsCauchySurface S → SecondCountableTopology S →
  SecondCountableTopology M` under `[T2Space M] [ConnectedSpace M]`: the field's statement, with
  `C` for `causality s` and the structure `s : Str M` read as the DEC-25 structure with `hC`.
  `LocalModel`'s field (l.625) has the same conclusion over a `ChartedSpace Y M`; it is not
  instantiated here.
* **The route** is the planner's Lindelöf bookkeeping: no splitting, and gx's future-volume step
  (O4) is not needed. The only causal input is that each singular component is the range of an
  inextensible causal curve over `ℝ`, which meets `S` exactly once (DEC-14); hence global
  hyperbolicity is not used. Each `x ∈ Sing(M) ∩ S` is the only point of `S` on its component,
  which is open in `Sing(M)`, so `Sing(M) ∩ S` is discrete.
* **Hypotheses of the lemmas.** (c) and (d) are topological in substance, but stated with `hC`:
  the translation atlases of `SFALine` and `SFAMassiveLine` are indexed by chart isomorphisms.
  (b), `sing_eq_sUnion_components` and `exists_isOpen_secondCountable` ask only
  `SFALocal.MassACovered M`. `T2Space` enters through `LineDevelopment.exists_development` and
  through the flat theorem; whether it can be dropped is not examined.
* **Subtypes in statements** (kb/0001 set aside): the field's own hypothesis is about the subspace
  `S`, and (a) is about the subspace `Reg(M)`.
* **The witnesses are known second countable**: `E₀` by instance, `{T < 1}` as a subspace of `E₀`,
  and `SecondCountableTopology S` is discharged through that instance; neither is a manifold not
  already known second countable. They show the hypotheses met with a BTZ point on `S`, at `E₀`
  and off the identity at `{T < 1}`, not the depth of the proof.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Imports
`Causal.Remarks.SingularRowsCauchyExt` (through it `Causal.Flat.SecondCountable`,
`Causal.Port.SFALine`, `Causal.Port.SFAMassiveLine`, `Causal.Remarks.SingularRowsSplitting`).
-/

namespace Causal

open Set Filter Topology TopologicalSpace Function

universe u

namespace SingularRowsSecondCountable

/-! ### The models are second countable -/

/-- **Every model of the family `E_{≥0}` is second countable**: `E₀ = ℝ × ℂ`, and
`E_κ = ℝ × C_κ` with `C_κ` proper. -/
theorem secondCountableTopology_massAModel :
    ∀ o, SecondCountableTopology (MassAModel o)
  | none => inferInstanceAs (SecondCountableTopology (ℝ × ℂ))
  | some κ => by
    haveI : Fact (0 < κ.1) := ⟨κ.2⟩
    exact inferInstanceAs (SecondCountableTopology (ℝ × Cone κ.1))

section Manifold

variable {M : Type u} [TopologicalSpace M] [SingularGXStructure (Flat.isom 2) (Minkowski 2) M]
  {C : Causality M}

/-! ### (a) The regular part -/

/-- **(a) `Reg(M)` is second countable**, at every connected, Hausdorff singular
`(Isom(𝐌³), 𝐌³)`-manifold, with no countability asked of `M`: `Reg(M)` is open and portly, hence
connected, and the maximal a.e. atlas makes it an `(Isom(𝐌³), 𝐌³)`-manifold, which is second
countable by the flat theorem (DEC-49). -/
theorem secondCountableTopology_reg [T2Space M] [ConnectedSpace M] :
    SecondCountableTopology (Reg (Flat.isom 2) (Minkowski 2) M) := by
  let U : Opens M := ⟨Reg (Flat.isom 2) (Minkowski 2) M, isOpen_reg _ _ _⟩
  have hsupp : ∀ x : U, ∃ e ∈ aeAtlas (Flat.isom 2) (Minkowski 2) U, x ∈ e.source := by
    intro x
    have hx : x ∈ Reg (Flat.isom 2) (Minkowski 2) U := by
      rw [reg_opensSingular]
      exact x.2
    exact mem_support.1 hx
  letI : ChartedSpace (Minkowski 2) U := chartedSpaceOfAtlas _ hsupp
  haveI : HasGroupoid U (gxGroupoid (Flat.isom 2) (Minkowski 2)) :=
    hasGroupoid_chartedSpaceOfAtlas
      (isMaximalAEAtlas_aeAtlas (Flat.isom 2) (Minkowski 2) U).1.1 hsupp
  haveI : ConnectedSpace U :=
    isConnected_iff_connectedSpace.1 (isPortly_reg (Flat.isom 2) (Minkowski 2) M).isConnected
  exact Flat.flat_secondCountableTopology (d := 2) U

/-! ### (b) The singular part is the union of the `sing_α(M)` -/

/-- **(b) `Sing(M) = ⋃_{α ≥ 0} sing_α(M)`** at every `E_{≥0}`-manifold. -/
theorem sing_eq_iUnion (hcov : SFALocal.MassACovered M) :
    Sing (Flat.isom 2) (Minkowski 2) M = ⋃ (α : ℝ) (_ : 0 ≤ α), SFALocal.sing M α := by
  ext x
  rw [SFALocal.mem_sing_iff hcov x]
  simp only [mem_iUnion, exists_prop]

/-- A point of `sing_α(M)` has `α ≥ 0`. -/
theorem nonneg_of_mem_sing {α : ℝ} {p : M} (hp : p ∈ SFALocal.sing M α) : 0 ≤ α := by
  obtain ⟨o, rfl, -⟩ := hp
  exact SFALocal.angle_nonneg o

/-! ### (c), (d) The singular components -/

/-- **The component of `sing_α(M)` through `p` is the continuous image of `ℝ`, and a
neighbourhood of `p` in `sing_α(M)`** (the line development of `Causal.LineDevelopment`, through
`SFALine.exists_isLineDevelopment` at `α = 0` and `SFAMassiveLine.isTranslationAtlas` at
`α > 0`). -/
theorem exists_line_development [T2Space M]
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) {α : ℝ} {p : M}
    (hp : p ∈ SFALocal.sing M α) :
    (∃ γ : ℝ → M, Continuous γ ∧ range γ = connectedComponentIn (SFALocal.sing M α) p) ∧
      ∃ W : Set M, IsOpen W ∧ p ∈ W ∧
        SFALocal.sing M α ∩ W ⊆ connectedComponentIn (SFALocal.sing M α) p := by
  have key : ∀ {ι : Type u} {V : ι → Set M} {σ : ι → ℝ → M} {J : ι → Set ℝ} {γ : ℝ → M},
      LineDevelopment.IsLineDevelopment (SFALocal.sing M α) V σ J p γ →
      (∃ γ : ℝ → M, Continuous γ ∧ range γ = connectedComponentIn (SFALocal.sing M α) p) ∧
        ∃ W : Set M, IsOpen W ∧ p ∈ W ∧
          SFALocal.sing M α ∩ W ⊆ connectedComponentIn (SFALocal.sing M α) p := by
    intro ι V σ J γ hγ
    refine ⟨⟨γ, hγ.continuous, hγ.range_eq⟩, ?_⟩
    obtain ⟨W, hW, h0W, hsub⟩ := hγ.local_onto 0 1 one_pos
    refine ⟨W, hW, hγ.zero ▸ h0W, fun y hy => ?_⟩
    rw [← hγ.range_eq]
    obtain ⟨s, -, hs⟩ := hsub hy
    exact ⟨s, hs⟩
  rcases (nonneg_of_mem_sing hp).eq_or_lt with h0 | hpos
  · subst h0
    obtain ⟨γ, hγ, -⟩ := SFALine.exists_isLineDevelopment hC hp
    exact key hγ
  · by_cases h2 : α = 2 * Real.pi
    · subst h2
      rw [SFALocal.sing_two_pi] at hp
      exact absurd hp (notMem_empty p)
    · haveI : Fact (0 < α) := ⟨hpos⟩
      obtain ⟨γ, hγ⟩ := LineDevelopment.exists_development
        (SFALocal.isClosed_sing (SFALocal.massACovered_of_isoChartsCover hC) α hpos.le)
        (SFAMassiveLine.isTranslationAtlas hC h2) hp
      exact key hγ

/-- **(c) Each component of `sing_α(M)` is open in `Sing(M)`**: some open `W ∋ p` meets `Sing(M)`
inside the component of `sing_α(M)` through `p`. -/
theorem exists_isOpen_inter_sing_subset [T2Space M]
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) {α : ℝ} {p : M}
    (hp : p ∈ SFALocal.sing M α) :
    ∃ W : Set M, IsOpen W ∧ p ∈ W ∧
      W ∩ Sing (Flat.isom 2) (Minkowski 2) M ⊆ connectedComponentIn (SFALocal.sing M α) p := by
  obtain ⟨V, hV, hVeq⟩ := SFALocal.exists_isOpen_sing_eq_inter (M := M) α
  obtain ⟨-, W, hW, hpW, hsub⟩ := exists_line_development hC hp
  have hpV : p ∈ V := (hVeq ▸ hp).1
  refine ⟨V ∩ W, hV.inter hW, ⟨hpV, hpW⟩, fun y hy => hsub ⟨?_, hy.1.2⟩⟩
  rw [hVeq]
  exact ⟨hy.1.1, hy.2⟩

/-- **(d) Each component of `sing_α(M)` is Lindelöf**, the continuous image of `ℝ`. -/
theorem isLindelof_component [T2Space M]
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) {α : ℝ} {p : M}
    (hp : p ∈ SFALocal.sing M α) :
    IsLindelof (connectedComponentIn (SFALocal.sing M α) p) := by
  obtain ⟨⟨γ, hγc, hγr⟩, -⟩ := exists_line_development hC hp
  rw [← hγr]
  exact isLindelof_range hγc

/-- **(d) Each component of `sing_α(M)` meets every Cauchy surface in exactly one point**: it is
the range of an inextensible causal curve over `ℝ` (`SFALine.line`,
`SFAMassiveLine.massive_line`). -/
theorem existsUnique_mem_component_inter [T2Space M]
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) {S : Set M}
    (hS : C.IsCauchySurface S) {α : ℝ} {p : M} (hp : p ∈ SFALocal.sing M α) :
    ∃! x, x ∈ connectedComponentIn (SFALocal.sing M α) p ∩ S := by
  have key : ∀ γ : ℝ → M, C.Inextensible ⊤ univ γ →
      range γ = connectedComponentIn (SFALocal.sing M α) p →
      ∃! x, x ∈ connectedComponentIn (SFALocal.sing M α) p ∩ S := by
    intro γ hγi hγr
    have h := hS univ γ hγi
    rwa [image_univ, hγr] at h
  rcases (nonneg_of_mem_sing hp).eq_or_lt with h0 | hpos
  · subst h0
    obtain ⟨γ, -, -, hγi, hγr⟩ := SFALine.line hC p hp
    exact key γ hγi hγr
  · obtain ⟨γ, -, -, hγi, -, hγr⟩ := SFAMassiveLine.massive_line hC α hpos p hp
    exact key γ hγi hγr

/-! ### (e) Countably many singular components -/

/-- **The set `Sing(M) ∩ S` is countable** for every second countable Cauchy surface `S`: it is a
discrete subspace of `S`, each of its points being the only point of `S` on its component, which
is open in `Sing(M)`. -/
theorem countable_sing_inter [T2Space M]
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) {S : Set M}
    (hS : C.IsCauchySurface S) (hSc : SecondCountableTopology S) :
    (Sing (Flat.isom 2) (Minkowski 2) M ∩ S).Countable := by
  set D : Set S := Subtype.val ⁻¹' Sing (Flat.isom 2) (Minkowski 2) M with hD
  have hdisc : DiscreteTopology D := by
    refine discreteTopology_iff_isOpen_singleton.2 fun d => ?_
    obtain ⟨α, -, hα⟩ := (SFALocal.mem_sing_iff (SFALocal.massACovered_of_isoChartsCover hC)
      (d : S).1).1 d.2
    obtain ⟨W, hW, hdW, hsub⟩ := exists_isOpen_inter_sing_subset hC hα
    have hcont : Continuous fun y : D => ((y : S) : M) :=
      continuous_subtype_val.comp continuous_subtype_val
    convert hW.preimage hcont using 1
    ext y
    simp only [mem_singleton_iff, mem_preimage]
    constructor
    · rintro rfl
      exact hdW
    · intro hy
      have h1 : ((y : S) : M) ∈ connectedComponentIn (SFALocal.sing M α) (d : S).1 ∩ S :=
        ⟨hsub ⟨hy, y.2⟩, (y : S).2⟩
      have h2 : ((d : S) : M) ∈ connectedComponentIn (SFALocal.sing M α) (d : S).1 ∩ S :=
        ⟨mem_connectedComponentIn hα, (d : S).2⟩
      exact Subtype.ext (Subtype.ext ((existsUnique_mem_component_inter hC hS hα).unique h1 h2))
  haveI : Countable D := separableSpace_iff_countable.1 inferInstance
  have hDc : D.Countable := countable_coe_iff.1 inferInstance
  have himg : Sing (Flat.isom 2) (Minkowski 2) M ∩ S = Subtype.val '' D := by
    rw [hD, Subtype.image_preimage_coe, inter_comm]
  rw [himg]
  exact hDc.image _

/-- `Sing(M)` is the union of the singular components. -/
theorem sing_eq_sUnion_components (hcov : SFALocal.MassACovered M) :
    Sing (Flat.isom 2) (Minkowski 2) M = ⋃₀ {K : Set M | ∃ α : ℝ, ∃ p ∈ SFALocal.sing M α,
      K = connectedComponentIn (SFALocal.sing M α) p} := by
  ext x
  constructor
  · intro hx
    obtain ⟨α, -, hα⟩ := (SFALocal.mem_sing_iff hcov x).1 hx
    exact ⟨_, ⟨α, x, hα, rfl⟩, mem_connectedComponentIn hα⟩
  · rintro ⟨K, ⟨α, p, -, rfl⟩, hxK⟩
    exact SFALocal.sing_subset α (connectedComponentIn_subset _ _ hxK)

/-- **(e) There are countably many singular components** once some Cauchy surface is second
countable: each meets it, at a point of the countable `Sing(M) ∩ S`. -/
theorem countable_components [T2Space M]
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) {S : Set M}
    (hS : C.IsCauchySurface S) (hSc : SecondCountableTopology S) :
    {K : Set M | ∃ α : ℝ, ∃ p ∈ SFALocal.sing M α,
      K = connectedComponentIn (SFALocal.sing M α) p}.Countable := by
  have hcov := SFALocal.massACovered_of_isoChartsCover hC
  choose! β hβ using fun x (hx : x ∈ Sing (Flat.isom 2) (Minkowski 2) M) =>
    (SFALocal.mem_sing_iff hcov x).1 hx
  refine ((countable_sing_inter hC hS hSc).image
    fun x => connectedComponentIn (SFALocal.sing M (β x)) x).mono ?_
  rintro K ⟨α, p, hp, rfl⟩
  obtain ⟨x, ⟨hxK, hxS⟩, -⟩ := existsUnique_mem_component_inter hC hS hp
  have hxα : x ∈ SFALocal.sing M α := connectedComponentIn_subset _ _ hxK
  have hxs : x ∈ Sing (Flat.isom 2) (Minkowski 2) M := SFALocal.sing_subset α hxα
  have hβx : β x = α := by
    by_contra hne
    exact Set.disjoint_left.1 (SFALocal.disjoint_sing hne) (hβ x hxs).2 hxα
  refine ⟨x, ⟨hxs, hxS⟩, ?_⟩
  simp only
  rw [hβx, connectedComponentIn_eq hxK]

/-- **The singular locus `Sing(M)` is Lindelöf** once some Cauchy surface is second countable: a
countable union of singular components, each Lindelöf. -/
theorem isLindelof_sing [T2Space M]
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) {S : Set M}
    (hS : C.IsCauchySurface S) (hSc : SecondCountableTopology S) :
    IsLindelof (Sing (Flat.isom 2) (Minkowski 2) M) := by
  rw [sing_eq_sUnion_components (SFALocal.massACovered_of_isoChartsCover hC)]
  refine (countable_components hC hS hSc).isLindelof_sUnion ?_
  rintro K ⟨α, p, hp, rfl⟩
  exact isLindelof_component hC hp

/-! ### (f) The theorem -/

/-- **Every point of an `E_{≥0}`-manifold has a second countable open neighbourhood**: the source
of a chart of the maximal a.e. atlas at a regular point, of an `X_A`-chart at a singular one. -/
theorem exists_isOpen_secondCountable (hcov : SFALocal.MassACovered M) (x : M) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ SecondCountableTopology U := by
  by_cases hx : x ∈ Reg (Flat.isom 2) (Minkowski 2) M
  · obtain ⟨e, -, hxe⟩ := mem_support.1 hx
    exact ⟨e.source, e.open_source, hxe, e.toHomeomorphSourceTarget.secondCountableTopology⟩
  · obtain ⟨o, e, -, hxe⟩ := hcov x hx
    haveI := secondCountableTopology_massAModel o
    exact ⟨e.source, e.open_source, hxe, e.toHomeomorphSourceTarget.secondCountableTopology⟩

/-- **A connected, Hausdorff `E_{≥0}`-manifold with a second countable Cauchy surface is second
countable**, with no countability asked of `M` and no global hyperbolicity. -/
theorem secondCountableTopology_of_isCauchySurface [T2Space M] [ConnectedSpace M]
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) {S : Set M}
    (hS : C.IsCauchySurface S) (hSc : SecondCountableTopology S) :
    SecondCountableTopology M := by
  haveI := secondCountableTopology_reg (M := M)
  have hreg : IsLindelof (Reg (Flat.isom 2) (Minkowski 2) M) :=
    isLindelof_iff_lindelofSpace.2 inferInstance
  have huniv : IsLindelof (univ : Set M) :=
    (hreg.union (isLindelof_sing hC hS hSc)).of_isClosed_subset isClosed_univ fun x _ =>
      em (x ∈ Reg (Flat.isom 2) (Minkowski 2) M)
  choose U hUo hxU hUs using
    exists_isOpen_secondCountable (SFALocal.massACovered_of_isoChartsCover hC)
  obtain ⟨r, hr, hcov⟩ := huniv.elim_countable_subcover U hUo fun x _ => mem_iUnion.2 ⟨x, hxU x⟩
  haveI : Countable r := hr.to_subtype
  haveI : ∀ i : r, SecondCountableTopology (U i) := fun i => hUs i
  refine secondCountableTopology_of_countable_cover (U := fun i : r => U i) (fun i => hUo i) ?_
  refine eq_univ_of_forall fun x => ?_
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 (hcov (mem_univ x))
  exact mem_iUnion.2 ⟨⟨i, hi⟩, hxi⟩

/-- **A2's field `secondCountable_of_cauchy`** (`Causal/CBG/Geometry.lean:339`, `LocalModel`'s at
`:625`) at every Hausdorff, connected `E_{≥0}`-manifold: its conclusion verbatim, with `C` for
`causality s`. Global hyperbolicity is taken and not used. -/
theorem secondCountable_of_cauchy [T2Space M] [ConnectedSpace M]
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) :
    C.GloballyHyperbolic → ∀ S : Set M, C.IsCauchySurface S →
      SecondCountableTopology S → SecondCountableTopology M :=
  fun _ _ hS hSc => secondCountableTopology_of_isCauchySurface hC hS hSc

/-- **The field for the natural causality** (`IsAtlasCausalityDEC25`). -/
theorem secondCountable_of_cauchy_of_isAtlasCausalityDEC25 [T2Space M] [ConnectedSpace M]
    (hcov : SFALocal.MassACovered M)
    (hCM : IsAtlasCausalityDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) :
    C.GloballyHyperbolic → ∀ S : Set M, C.IsCauchySurface S →
      SecondCountableTopology S → SecondCountableTopology M :=
  secondCountable_of_cauchy (SFALocal.of_isAtlasCausalityDEC25 hcov hCM).2

end Manifold

/-! ### Witnesses (kb/0011) -/

section WitnessE0

attribute [local instance] E0GX.singularGX

/-- **Non-vacuity at `E₀`**, out of this file's `M`-level theorems: for the Cauchy time function
`T` of `SingularRowsCauchyExt.exists_cauchyTimeFunction`, `S = T⁻¹(0)` is a second countable
Cauchy surface carrying a BTZ point (the axis meets it), `Sing(E₀) ∩ S` is countable, the singular
components are countably many, `Reg(E₀)` is second countable, and so is `E₀`. `E₀` and `S` are
known second countable by instance (SCOPE). -/
theorem nonvacuous_e0 :
    IsoChartsCoverDEC25 (Flat.isom 2) E0.causality (minkowski 2) massAModelCausality ∧
      ∃ S : Set E0, E0.causality.IsCauchySurface S ∧ SecondCountableTopology S ∧
        (SFALocal.sing E0 0 ∩ S).Nonempty ∧
        (Sing (Flat.isom 2) (Minkowski 2) E0 ∩ S).Countable ∧
        {K : Set E0 | ∃ α : ℝ, ∃ p ∈ SFALocal.sing E0 α,
          K = connectedComponentIn (SFALocal.sing E0 α) p}.Countable ∧
        SecondCountableTopology (Reg (Flat.isom 2) (Minkowski 2) E0) ∧
        SecondCountableTopology E0 := by
  obtain ⟨-, hC, hsing, -⟩ := SFALocal.nonvacuous_e0
  obtain ⟨T, hT, hTs⟩ := SingularRowsCauchyExt.exists_cauchyTimeFunction
  have hS := SingularRowsCauchyExt.isCauchySurface_level hT hTs 0
  have hSc : SecondCountableTopology (T ⁻¹' {(0 : ℝ)}) := inferInstance
  obtain ⟨t, ht⟩ := SingularRowsCauchyExt.exists_tauFlow_level hT hTs ((0 : ℝ), (0 : ℂ)) 0
  have hx₀ : ((0 : ℝ), (0 : ℂ)) ∈ E0.axis := rfl
  have hbtz : SingularRowsSplitting.tauFlow t ((0 : ℝ), (0 : ℂ)) ∈
      SFALocal.sing E0 0 ∩ T ⁻¹' {0} := by
    refine ⟨?_, ht⟩
    rw [hsing]
    exact SingularRowsSplitting.tauFlow_mem_axis.2 hx₀
  exact ⟨hC, T ⁻¹' {0}, hS, hSc, ⟨_, hbtz⟩, countable_sing_inter hC hS hSc,
    countable_components hC hS hSc, secondCountableTopology_reg,
    secondCountableTopology_of_isCauchySurface hC hS hSc⟩

/-- **Non-vacuity of the natural form at `E₀`** (`EModelsBPrime.massA_dec25_models_e0_sing`): the
conclusion out of `secondCountable_of_cauchy_of_isAtlasCausalityDEC25`, at the Cauchy surface
`T⁻¹(0)`, which carries a BTZ point. -/
theorem nonvacuous_e0_natural :
    SFALocal.MassACovered E0 ∧
      IsAtlasCausalityDEC25 (Flat.isom 2) E0.causality (minkowski 2) massAModelCausality ∧
      E0.causality.GloballyHyperbolic ∧
      ∃ S : Set E0, E0.causality.IsCauchySurface S ∧ SecondCountableTopology S ∧
        (SFALocal.sing E0 0 ∩ S).Nonempty ∧ SecondCountableTopology E0 := by
  obtain ⟨-, hcov, hCM, -⟩ := EModelsBPrime.massA_dec25_models_e0_sing
  obtain ⟨-, -, hsing, -⟩ := SFALocal.nonvacuous_e0
  obtain ⟨T, hT, hTs⟩ := SingularRowsCauchyExt.exists_cauchyTimeFunction
  have hS := SingularRowsCauchyExt.isCauchySurface_level hT hTs 0
  have hSc : SecondCountableTopology (T ⁻¹' {(0 : ℝ)}) := inferInstance
  obtain ⟨t, ht⟩ := SingularRowsCauchyExt.exists_tauFlow_level hT hTs ((0 : ℝ), (0 : ℂ)) 0
  have hx₀ : ((0 : ℝ), (0 : ℂ)) ∈ E0.axis := rfl
  have hbtz : SingularRowsSplitting.tauFlow t ((0 : ℝ), (0 : ℂ)) ∈
      SFALocal.sing E0 0 ∩ T ⁻¹' {0} := by
    refine ⟨?_, ht⟩
    rw [hsing]
    exact SingularRowsSplitting.tauFlow_mem_axis.2 hx₀
  exact ⟨hcov, hCM, E0.globallyHyperbolic, T ⁻¹' {0}, hS, hSc, ⟨_, hbtz⟩,
    secondCountable_of_cauchy_of_isAtlasCausalityDEC25 hcov hCM E0.globallyHyperbolic _ hS hSc⟩

/-- **Non-vacuity at `{T < 1}`**, a Cauchy extension of `E₀` that is not onto
(`SingularRowsCauchyExt.cauchyExtension`): with its natural causality `C`, `{T < 1}` is a
connected, Hausdorff `E_{≥0}`-manifold, globally hyperbolic, `S = i⁻¹(T⁻¹(0))` is a second
countable Cauchy surface carrying a BTZ point (the τ-orbit of the axis), and `{T < 1}` is second
countable out of `secondCountableTopology_of_isCauchySurface`. It is known second countable as a
subspace of `E₀` (SCOPE). -/
theorem nonvacuous_sublevel :
    ∃ (T : E0 → ℝ) (hT : E0.causality.IsCauchyTimeFunction T),
      ∃ C : Causality (SingularRowsCauchyExt.sublevel hT.1.continuous 1),
        SFALocalE0.IsE0Natural C ∧
        IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality ∧
        C.GloballyHyperbolic ∧
        ¬ Surjective (Subtype.val : SingularRowsCauchyExt.sublevel hT.1.continuous 1 → E0) ∧
        C.IsCauchySurface (Subtype.val ⁻¹' (T ⁻¹' {0})) ∧
        SecondCountableTopology (Subtype.val ⁻¹' (T ⁻¹' {(0 : ℝ)}) :
          Set (SingularRowsCauchyExt.sublevel hT.1.continuous 1)) ∧
        (SFALocal.sing (SingularRowsCauchyExt.sublevel hT.1.continuous 1) 0 ∩
          Subtype.val ⁻¹' (T ⁻¹' {0})).Nonempty ∧
        SecondCountableTopology (SingularRowsCauchyExt.sublevel hT.1.continuous 1) := by
  obtain ⟨T, hT, hTs⟩ := SingularRowsCauchyExt.exists_cauchyTimeFunction
  obtain ⟨he0, ⟨C, hCn, -⟩, h⟩ := SingularRowsCauchyExt.cauchyExtension hT hTs 1
  obtain ⟨-, hC, -, hG, hcs, -, hns⟩ := h C hCn
  haveI := SingularRowsCauchyExt.connectedSpace_sublevel hT hTs 1
  have hS := hcs 0 zero_lt_one
  have hSc : SecondCountableTopology (Subtype.val ⁻¹' (T ⁻¹' {(0 : ℝ)}) :
      Set (SingularRowsCauchyExt.sublevel hT.1.continuous 1)) := inferInstance
  obtain ⟨t, ht⟩ := SingularRowsCauchyExt.exists_tauFlow_level hT hTs ((0 : ℝ), (0 : ℂ)) 0
  have hxU : SingularRowsSplitting.tauFlow t ((0 : ℝ), (0 : ℂ)) ∈
      SingularRowsCauchyExt.sublevel hT.1.continuous 1 :=
    show T _ < 1 by rw [ht]; exact zero_lt_one
  have hbtz : (⟨_, hxU⟩ : SingularRowsCauchyExt.sublevel hT.1.continuous 1) ∈
      SFALocal.sing (SingularRowsCauchyExt.sublevel hT.1.continuous 1) 0 := by
    rw [SFALocal.sing_eq_of_e0Covered he0, SFALocalE0.sing_zero, sing_opensSingular]
    exact (SFALocal.mem_sing_e0_iff _).2 (SingularRowsSplitting.tauFlow_mem_axis.2 rfl)
  exact ⟨T, hT, C, hCn, hC, hG, hns, hS, hSc, ⟨_, hbtz, ht⟩,
    secondCountableTopology_of_isCauchySurface hC hS hSc⟩

end WitnessE0

end SingularRowsSecondCountable

end Causal
