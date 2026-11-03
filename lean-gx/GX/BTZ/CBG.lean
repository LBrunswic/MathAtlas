import GX.BTZ.LocalModel
import Causal.CBG.Maximal

/-!
# `GX.BTZ.CBG` — the BTZ residuals of `Geometry.ofLocalModelOfBTZ`, and CBG for `𝔼₀`-manifolds

L. Brunswic, *On branched coverings of singular (G,X)-manifolds*, §4 (`papers/gx`), with the
thesis (`papers/gx/sources/thesis/these.tex`) and Sbierski (`papers/gx/sources/1309.7591`).
Package WP-41g (WAVE5-PLAN.md, WP-39g; DEC-29, DEC-59). **No ledger label is marked**: this file
discharges three CBG-interface obligations (lean-causal `ca2ad78`, `Causal/CBG/FromModel.lean`),
which are not rows of the gx ledger. Thesis labels used, unmarked: `lem:passe_pgcd`
(`these.tex:6541`), `cor:K_injectif` (`these.tex:5838`, replaced, see SCOPE).

> Soit $M$ un espace-temps plat singulier globalement hyperbolique de surface de Cauchy $\Sigma$,
> soit $M\xrightarrow{i} N$ une extension de Cauchy de $M$ et soit
> $p\in \partial i(M)\cap J^+(i(\Sigma))$. […] si $p\in \sing_{0}(M)$ alors
> $$J_{N}(i(\Sigma),p)\setminus\{p\}\subset i(M).$$ (`lem:passe_pgcd`, `these.tex:6541–6550`)

> Lemma 3.8. Let U be a CGHD of M and M′ with isometric embedding ψ : U ⊆ M → M′. Then the set C
> is open in ∂U and the isometric embedding ψ : U → M′ extends smoothly to ψ : U ∪ C → M′.
> (Sbierski, p. 16)

## What is proved (0 `sorry`; `#print axioms`: propext, Classical.choice, Quot.sound)

* The three residuals, stated on the `𝔼₀` data (`Y = 𝕄 ⊕ 𝔼₀`, `G = e0Groupoid`, the model
  causality `E0LM.D`; `E0SliceFutureBTZ`, `E0GermExtFutureBTZ`, `E0GermExtPastBTZ`):
  - `e0_sliceFutureBTZ` (A4 future at BTZ points; Sbierski Thm 3.6): unconditional;
  - `e0_germExtFutureBTZ` (A3 future at BTZ points; Lemma 3.8, `lem:passe_pgcd`): unconditional;
  - `e0_germExtPastBTZ_of` (A3 past at BTZ points): **partial**, added hypothesis `hLine` (the
    `line` field of `SingularFlatAxioms`, WP-41f's (O2)); the proof uses the SFA fields
    `mem_Zplus`, `K_densite_sing`, `Iminus_eq_empty`, `pushUp` (on `M` and `N`) and
    `E0LM.sfa_isCompact_Jplus_inter_Jminus`, all through `hLine`.
  Bridges to lean-causal's predicates for `E0LM.e0LocalModelOf hLine hSC hTA` (`sliceFutureBTZ_of`,
  `germExtFutureBTZ_of`, `germExtPastBTZ_of`) and to the port's for `e0TLocalModel hLine hSC`
  (`e0TLocalModel_*`), by definitional unfolding.
* §3c, **the port** `TLocalModel` (lean-causal's `Causal.CBG.LocalModel` and the model-dependent
  part of `Causal/CBG/FromModel.lean`, verbatim, with `typeAgreement` in **convergence** form;
  the section docstring lists every change). `e0TLocalModel hLine hSC`: the `𝔼₀` local model, its
  `typeAgreement` the proved `E0LM.e0_typeAgreementTendsto`.
* `e0Geometry hLine hSC` (a `Causal.CBG.Geometry`, its structures the `𝔼₀`-atlases,
  `e0Geometry_Str`/`_causality`/`_isMor`) and **CBG for `𝔼₀`-manifolds** (DEC-29): `e0_cbg`
  (universal, DEC-59), `e0_cbg_isETTMaximal` (DEC-77(c)), `e0_cbg_ett` (existence and uniqueness
  up to unique isomorphism), from `Causal.CBG.cbg`. **Conditional on `hLine` (O2) and `hSC` (O4)**,
  true statements left open in WP-41f (`E0LM.e0_globalBTZ`, `E0LM.e0_secondCountable_of_cauchy`,
  one tagged `sorry` each): not vacuous (`campaign/WP-41g/Axioms.lean` instantiates it).

## Hypothesis checklist

| interface / paper | here |
|---|---|
| `GermExtFutureBTZ` (all its hypotheses) | ✓ carried; `GH(U)`, `GH(ψ U)`, `ψ S` Cauchy unused |
| `GermExtPastBTZ` | ⚠ strengthened: `hLine` (O2) added — a parameter of the model already |
| `SliceFutureBTZ` | ✓ carried; the corner condition and `GH(U)` unused |
| `LocalModel.typeAgreement` | ⚠ replaced (port): `Tendsto` for `MapClusterPt`; the latter is refuted for `𝔼₀` |
| CBG for `𝔼₀` (DEC-29) | ⚠ conditional on (O2), (O4) |

## SCOPE (disclosed)

* **Why a port.** `hTA : E0TypeAgreement E0LM.D` (lean-causal's field) is refuted
  (`E0LM.e0_not_typeAgreement`, re-exported `e0Geometry_hTA_refuted`), so
  `Geometry.ofLocalModelOfBTZ` cannot be instantiated for `𝔼₀`. Its only consumer
  (`germ_ext_nonBTZ`, `FromModel.lean:1951`) has `Tendsto ψ (𝓝[A] p) (𝓝 q)` in scope, so the
  convergence form suffices; the port proves it, and is to be deleted once lean-causal restates
  the field (then `e0Geometry := Geometry.ofLocalModelOfBTZ …` with the same bridges).
* Past side (against A3-B-INVESTIGATION.md §3): the corresponding point is the limit `q*` of `ψ`
  along a chronal curve from `p` (a monotone family in a compact diamond, unique cluster point),
  not `cor:K_injectif`; `q*` is BTZ by the convergence form of type agreement applied to `ψ⁻¹`.
* Future side: `p`'s line below `p` lies in `U` (`exists_axis_below_mem`); the limit of `ψ` along
  it replaces "an endpoint `q′`". A4 future: the slice is the level `{h = τ_z}` of
  `E0.sliceDom` through a line point `z ∈ U` below `p` (the corner condition is not needed).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; lean-causal `ca2ad78`
(`lake-manifest.json`).
-/

namespace GX

open Set Filter Topology Function TopologicalSpace
open scoped Real

namespace E0CBG

/-! ### §0 The causality and the BTZ locus of an `𝔼₀`-manifold -/

/-- The causality of an `𝔼₀`-manifold (`Causal.CBG.chartedCausality` of the model causality). -/
noncomputable abbrev CE (M : Type) [TopologicalSpace M] [ChartedSpace E0Y M] :
    Causal.Causality M :=
  Causal.CBG.chartedCausality E0LM.D M

/-- The BTZ locus `sing₀(M)` of an `𝔼₀`-manifold. -/
abbrev S0 (M : Type) [TopologicalSpace M] [ChartedSpace E0Y M] : Set M :=
  Causal.CBG.chartedSing e0SingY M 0

/-! ### §1 The three BTZ residuals, stated on the `𝔼₀` data -/

/-- **A4 future at BTZ points, for `𝔼₀`-manifolds** (the body of
`Causal.CBG.LocalModel.SliceFutureBTZ` for `Y = 𝕄 ⊕ 𝔼₀`, `G = e0Groupoid`, read on the data). -/
def E0SliceFutureBTZ : Prop :=
  ∀ {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [SecondCountableTopology M]
    [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid] (U : Opens M) (S : Set M),
    (CE M).GloballyHyperbolic → (CE M).GloballyHyperbolicOn U → S ⊆ U →
    (CE M).IsCauchySurface S → (CE M).IsCauchySurfaceOn U S → ∀ p : M,
    p ∈ frontier (U : Set M) → p ∈ (CE M).Jplus ⊤ S →
    (CE M).Jminus ⊤ {p} ∩ frontier (U : Set M) ∩ (CE M).Jplus ⊤ S = {p} →
    ∀ O : Opens M, p ∈ O → p ∈ S0 M → ∃ U' : Opens M, U < U' ∧ (U' : Set M) ⊆ U ∪ O ∧
      (CE M).GloballyHyperbolicOn U' ∧ (CE M).IsCauchySurfaceOn U' S

/-- **A3 future at BTZ points, for `𝔼₀`-manifolds** (the body of
`Causal.CBG.LocalModel.GermExtFutureBTZ`, read on the data). -/
def E0GermExtFutureBTZ : Prop :=
  ∀ {M N : Type} [TopologicalSpace M] [TopologicalSpace N] [T2Space M]
    [ConnectedSpace M] [SecondCountableTopology M] [T2Space N] [ConnectedSpace N]
    [SecondCountableTopology N] [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]
    [ChartedSpace E0Y N] [HasGroupoid N e0Groupoid] (U : Opens M) (ψ : M → N) (S : Set M)
    (h : ChartedSpace.LiftPropOn e0Groupoid.IsLocalStructomorphWithinAt ψ U), InjOn ψ U →
    (CE M).GloballyHyperbolic → (CE N).GloballyHyperbolic → (CE M).GloballyHyperbolicOn U →
    (CE N).GloballyHyperbolicOn ((Causal.CBG.isEMorphismOn_of_liftPropOn
      E0.chartIso_mem_e0Groupoid E0.absolutelyMinimalOn_YBTZ h).imageOpens U le_rfl) →
    S ⊆ U → (CE M).IsCauchySurface S → (CE M).IsCauchySurfaceOn U S →
    (CE N).IsCauchySurface (ψ '' S) →
    (CE N).IsCauchySurfaceOn ((Causal.CBG.isEMorphismOn_of_liftPropOn
      E0.chartIso_mem_e0Groupoid E0.absolutelyMinimalOn_YBTZ h).imageOpens U le_rfl) (ψ '' S) →
    ∀ p : M, ∀ q : N, p ∈ frontier (U : Set M) → p ∈ (CE M).Jplus ⊤ S →
      MapClusterPt q (𝓝[(U : Set M)] p) ψ → p ∈ S0 M →
      ∃ (O : Opens M) (φ : M → N), p ∈ O ∧
        ChartedSpace.LiftPropOn e0Groupoid.IsLocalStructomorphWithinAt φ O ∧ φ p = q ∧
        EqOn φ ψ (O ⊓ U : Opens M)

/-- **A3 past at BTZ points, for `𝔼₀`-manifolds** (the body of
`Causal.CBG.LocalModel.GermExtPastBTZ`, read on the data). -/
def E0GermExtPastBTZ : Prop :=
  ∀ {M N : Type} [TopologicalSpace M] [TopologicalSpace N] [T2Space M]
    [ConnectedSpace M] [SecondCountableTopology M] [T2Space N] [ConnectedSpace N]
    [SecondCountableTopology N] [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]
    [ChartedSpace E0Y N] [HasGroupoid N e0Groupoid] (U : Opens M) (ψ : M → N) (S : Set M)
    (h : ChartedSpace.LiftPropOn e0Groupoid.IsLocalStructomorphWithinAt ψ U), InjOn ψ U →
    (CE M).GloballyHyperbolic → (CE N).GloballyHyperbolic → (CE M).GloballyHyperbolicOn U →
    (CE N).GloballyHyperbolicOn ((Causal.CBG.isEMorphismOn_of_liftPropOn
      E0.chartIso_mem_e0Groupoid E0.absolutelyMinimalOn_YBTZ h).imageOpens U le_rfl) →
    S ⊆ U → (CE M).IsCauchySurface S → (CE M).IsCauchySurfaceOn U S →
    (CE N).IsCauchySurface (ψ '' S) →
    (CE N).IsCauchySurfaceOn ((Causal.CBG.isEMorphismOn_of_liftPropOn
      E0.chartIso_mem_e0Groupoid E0.absolutelyMinimalOn_YBTZ h).imageOpens U le_rfl) (ψ '' S) →
    ∀ p : M, ∀ q : N, p ∈ frontier (U : Set M) → p ∈ (CE M).Jminus ⊤ S →
      MapClusterPt q (𝓝[(U : Set M)] p) ψ → p ∈ S0 M →
      ∃ (O : Opens M) (φ : M → N), p ∈ O ∧
        ChartedSpace.LiftPropOn e0Groupoid.IsLocalStructomorphWithinAt φ O ∧ φ p = q ∧
        EqOn φ ψ (O ⊓ U : Opens M)

/-! ### §2 The bridges to the `LocalModel` predicates -/

section Bridge

variable
  (hLine : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [SecondCountableTopology M] [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid],
    E0LM.E0GlobalBTZ (Causal.CBG.chartedCausality E0LM.D M) (Causal.CBG.chartedSing e0SingY M 0))
  (hSC : ∀ {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [ChartedSpace E0Y M]
    [HasGroupoid M e0Groupoid], (Causal.CBG.chartedCausality E0LM.D M).GloballyHyperbolic →
    ∀ S : Set M, (Causal.CBG.chartedCausality E0LM.D M).IsCauchySurface S →
    SecondCountableTopology S → SecondCountableTopology M)
  (hTA : E0TypeAgreement E0LM.D)

theorem sliceFutureBTZ_of (h : E0SliceFutureBTZ) :
    (E0LM.e0LocalModelOf hLine hSC hTA).SliceFutureBTZ := by
  intro M _ _ _ _ s U S hGH hGHU hSU hS hSU' p hp hpS hc O hpO hp0
  obtain ⟨cs, hg⟩ := s
  exact @h M _ _ _ _ cs hg U S hGH hGHU hSU hS hSU' p hp hpS hc O hpO hp0

theorem germExtFutureBTZ_of (h : E0GermExtFutureBTZ) :
    (E0LM.e0LocalModelOf hLine hSC hTA).GermExtFutureBTZ := by
  intro M N _ _ _ _ _ _ _ _ s t U ψ S hψ hinj hGM hGN hGU hGV hSU hS hSU' hψS hψSV p q hp hpS
    hcl hp0
  obtain ⟨cs, hgs⟩ := s
  obtain ⟨ct, hgt⟩ := t
  exact @h M N _ _ _ _ _ _ _ _ cs hgs ct hgt U ψ S hψ hinj hGM hGN hGU hGV hSU hS hSU' hψS hψSV
    p q hp hpS hcl hp0

theorem germExtPastBTZ_of (h : E0GermExtPastBTZ) :
    (E0LM.e0LocalModelOf hLine hSC hTA).GermExtPastBTZ := by
  intro M N _ _ _ _ _ _ _ _ s t U ψ S hψ hinj hGM hGN hGU hGV hSU hS hSU' hψS hψSV p q hp hpS
    hcl hp0
  obtain ⟨cs, hgs⟩ := s
  obtain ⟨ct, hgt⟩ := t
  exact @h M N _ _ _ _ _ _ _ _ cs hgs ct hgt U ψ S hψ hinj hGM hGN hGU hGV hSU hS hSU' hψS hψSV
    p q hp hpS hcl hp0

end Bridge

/-! ### §3a Generic: a chart isomorphism is a morphism; the slice assembly through it -/

section ChartSlice

variable {M X : Type*} [TopologicalSpace M] [TopologicalSpace X] {C : Causal.Causality M}
  {DX : Causal.Causality X}

/-- **A chart isomorphism is an abstract morphism on its source** (`Causal.CBG.LocalModel.chart_isEMorphismOn`,
for any chart isomorphism, no local model). -/
theorem isEMorphismOn_of_chartIso {e : OpenPartialHomeomorph M X}
    (hiso : Causal.ChartIso C DX e) : Causal.IsEMorphismOn C DX (Causal.chartSource e) e := by
  have himg : ∀ V : Opens M, V ≤ Causal.chartSource e →
      ((Causal.chartImage e V : Opens X) : Set X) = e '' V :=
    fun V hV => Causal.coe_chartImage_of_le hV
  have hsub : ∀ (V : Opens M) (U : Opens X), V ≤ Causal.chartSource e → MapsTo e V U →
      Causal.chartImage e V ≤ U := fun V U hV hmaps p hp => by
    rw [← SetLike.mem_coe, himg V hV] at hp
    obtain ⟨z, hz, rfl⟩ := hp
    exact hmaps hz
  exact
  { continuousOn := e.continuousOn
    isOpen_image := fun V hV => by rw [← himg V hV]; exact (Causal.chartImage e V).isOpen
    map_le := fun V U hV hmaps y z hyz =>
      DX.le_mono (hsub V U hV hmaps)
        (((hiso V hV y (C.le_mem_left hyz) z (C.le_mem_right hyz)).1).1 hyz)
    map_lt := fun V U hV hmaps y z hyz =>
      DX.lt_mono (hsub V U hV hmaps)
        (((hiso V hV y (C.lt_mem_left hyz) z (C.lt_mem_right hyz)).2).1 hyz)
    locally := fun z hz => ⟨Causal.chartSource e, le_rfl, hz, e.injOn,
      fun V' hV' U hU y hy w hw => by
        have hU' : Causal.chartImage e V' = U := SetLike.coe_injective (by rw [himg V' hV', hU])
        rw [← hU']; exact hiso V' hV' y hy w hw⟩ }

/-- **The assembly of A4 through any chart isomorphism** (`Causal.CBG.LocalModel.slice_assemble`
with the preferred chart replaced by a chart isomorphism `e : M ⇀ X`): an open `N ∋ e p` inside
`e(W₀)` with a Cauchy surface `Γ ⊆ N` inside `e(W₀ ∩ U)` gives, read back in `M`, an open
neighbourhood of `p` with a Cauchy surface inside `U`, and `Causal.CBG.extend_of_cauchy_nbhd`
concludes. -/
theorem slice_assemble_of_chartIso [T2Space M] {e : OpenPartialHomeomorph M X}
    (hiso : Causal.ChartIso C DX e) {p : M} {U O W₀ : Opens M} {S : Set M}
    (hGH : C.GloballyHyperbolic) (harc : C.CausallyArcConnected) (hext : C.CurvesExtend)
    (hSU : S ⊆ U) (hS : C.IsCauchySurface S) (hSU' : C.IsCauchySurfaceOn U S) (hpU : p ∉ U)
    (hpe : p ∈ e.source) (hW₀e : W₀ ≤ Causal.chartSource e)
    {N : Opens X} {Γ : Set X} (hNO : N ≤ Causal.chartImage e W₀) (hyN : e p ∈ N) (hΓN : Γ ⊆ N)
    (hΓG : Γ ⊆ e '' ((W₀ : Set M) ∩ U)) (hNΓ : DX.IsCauchySurfaceOn N Γ)
    (hW₀O : (W₀ : Set M) ⊆ O) :
    ∃ U' : Opens M, U < U' ∧ (U' : Set M) ⊆ U ∪ O ∧ C.GloballyHyperbolicOn U' ∧
      C.IsCauchySurfaceOn U' S := by
  let NM : Opens M := ⟨e.source ∩ e ⁻¹' N, e.isOpen_inter_preimage N.isOpen⟩
  set ΓM : Set M := e.source ∩ e ⁻¹' Γ with hΓMdef
  have hNM : (N : Set X) = e '' NM := by
    ext y
    constructor
    · intro hy
      obtain ⟨w, hws, -, rfl, -⟩ := Causal.exists_of_mem_chartImage (hNO hy)
      exact ⟨w, ⟨hws, hy⟩, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact hw.2
  have hΓM : e '' ΓM = Γ := by
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw.2
    · intro hy
      obtain ⟨w, hws, -, rfl, -⟩ := Causal.exists_of_mem_chartImage (hNO (hΓN hy))
      exact ⟨w, ⟨hws, hy⟩, rfl⟩
  have hΓMN : ΓM ⊆ NM := fun w hw => ⟨hw.1, hΓN hw.2⟩
  have hNMcy : C.IsCauchySurfaceOn NM ΓM := by
    refine ((isEMorphismOn_of_chartIso hiso).isCauchySurfaceOn_image_iff e.injOn
      (show NM ≤ Causal.chartSource e from fun _ hw => hw.1) hNM hΓMN).2 ?_
    rw [hΓM]
    exact hNΓ
  have hΓMU : ΓM ⊆ U := by
    intro w hw
    obtain ⟨w', hw', hw'e⟩ := hΓG hw.2
    rw [← e.injOn (hW₀e hw'.1) hw.1 hw'e]
    exact hw'.2
  have hpNM : p ∈ NM := ⟨hpe, hyN⟩
  have hNMO : (NM : Set M) ⊆ O := by
    intro w hw
    obtain ⟨w', hw's, hw'W, hw'e, -⟩ := Causal.exists_of_mem_chartImage (hNO hw.2)
    rw [← e.injOn hw's hw.1 hw'e]
    exact hW₀O hw'W
  exact Causal.CBG.extend_of_cauchy_nbhd hGH harc hext hSU hS hSU' hNMcy hΓMU hpNM hpU hNMO

end ChartSlice

/-! ### §3b The chart at a BTZ point, in the paper's coordinates -/

section PaperChart

variable {M : Type} [TopologicalSpace M] [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]

/-- The preferred chart of `M` at `x` followed by `E0.paperOfY` (the `𝔼₀` component of `Y`, in
the paper's coordinates `(τ, z)`). -/
noncomputable def paperChart (x : M) : OpenPartialHomeomorph M E0 :=
  (chartAt E0Y x).trans E0.paperOfY

/-- `paperChart x` is a chart isomorphism onto `𝔼₀` with its causality. -/
theorem chartIso_paperChart (x : M) : Causal.ChartIso (CE M) E0.causality (paperChart x) :=
  E0.chartIso_trans (Causal.CBG.chartedCausality_chartIso (M := M) E0.chartIso_mem_e0Groupoid
    E0.absolutelyMinimalOn_YBTZ x) E0.chartIso_paperOfY

omit [HasGroupoid M e0Groupoid] in
/-- At a BTZ point `p`, `p` is in the source of `paperChart p` and is sent to the axis. -/
theorem paperChart_of_mem_S0 {p : M} (hp0 : p ∈ S0 M) :
    p ∈ (paperChart p).source ∧ paperChart p p ∈ E0.axis := by
  have h : chartAt E0Y p p ∈ e0SingY 0 := hp0
  rw [E0LM.e0SingY_zero] at h
  obtain ⟨a, ha, he⟩ := h
  rcases hx : chartAt E0Y p p with m | x
  · rw [hx] at he
    exact absurd he (show ¬ (Sum.inr a : E0.ModelY) = Sum.inl m from Sum.inr_ne_inl)
  · rw [hx] at he
    have hax : E0.toPaper x = a := by
      have : (Sum.inr a : E0.ModelY) = Sum.inr (E0.toPaper x) := he
      exact (Sum.inr_injective this).symm
    refine ⟨⟨mem_chart_source E0Y p, ?_⟩, ?_⟩
    · show chartAt E0Y p p ∈ E0.paperOfY.source
      rw [E0.paperOfY_source, hx]; exact mem_range_self x
    · show E0.paperOfY (chartAt E0Y p p) ∈ E0.axis
      rw [hx, E0.paperOfY_inr, hax]; exact ha

end PaperChart

/-! ### §3c A4 future at BTZ points (`SliceFutureBTZ`) -/

/-- **A point of `p`'s line, strictly below `p`, close to `p`, lies in `U`** (`lem:passe_pgcd`'s
first step, `these.tex:6541`; A3-B-INVESTIGATION.md §2). For a BTZ boundary point `p` of a
causally convex `U` with `p ∈ J⁺(S)`, `S ⊆ U`, and a ball `B(κ p, δ)` inside the chart image of an
open `W ∋ p` (`κ` = `paperChart p`): there is `z ∈ U ∩ W` with `κ z` on the axis, at height in
`]τ_p − δ/2, τ_p[`. The causal curve from `σ ∈ S` to `p` ends on the line (the causal past of a
BTZ point in a ball is the line below it, `E0.le_axis_iff'`), so its last points before reaching
`p` are line points `z` with `σ ≤ z`; and `J⁺(z) = {f ≥ τ_z}` is a neighbourhood of `p`, which
meets `U`, so `z ∈ U` by causal convexity. -/
theorem exists_axis_below_mem {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace E0Y M]
    [HasGroupoid M e0Groupoid] {U : Opens M} {S : Set M}
    (hconv : (CE M).CausallyConvexIn (U : Set M) ⊤) (hSU : S ⊆ U) {p : M}
    (hpU : p ∉ U) (hpcl : p ∈ closure (U : Set M)) (hpS : p ∈ (CE M).Jplus ⊤ S)
    (hpκ : p ∈ (paperChart p).source) (hp₀ : paperChart p p ∈ E0.axis) {W : Opens M}
    {δ : ℝ} (hδ : 0 < δ)
    (hball : Metric.ball (paperChart p p) δ ⊆ Causal.chartImage (paperChart p) W) :
    ∃ z ∈ (U : Set M) ∩ W, paperChart p z ∈ E0.axis ∧
      (paperChart p p).1 - δ / 2 < (paperChart p z).1 ∧ (paperChart p z).1 < (paperChart p p).1 := by
  set κ := paperChart p with hκdef
  set C := CE M with hCdef
  set p₀ := κ p with hp₀def
  have harc : C.CausallyArcConnected := E0LM.e0_causallyArcConnected
  have hiso : Causal.ChartIso C E0.causality κ := chartIso_paperChart p
  -- the ball, read in `M`
  let Wb : Opens M := ⟨κ.source ∩ κ ⁻¹' Metric.ball p₀ δ,
    κ.isOpen_inter_preimage Metric.isOpen_ball⟩
  have hWbκ : Wb ≤ Causal.chartSource κ := fun x hx => hx.1
  have hWbW : (Wb : Set M) ⊆ W := by
    intro x hx
    obtain ⟨w, hws, hwW, hwe, -⟩ := Causal.exists_of_mem_chartImage (hball hx.2)
    rw [← κ.injOn hws hx.1 hwe]; exact hwW
  have hballWb : Metric.ball p₀ δ ⊆ Causal.chartImage κ Wb := by
    intro y hy
    obtain ⟨w, hws, -, rfl, -⟩ := Causal.exists_of_mem_chartImage (hball hy)
    exact Causal.mem_chartImage_of_mem hws ⟨hws, hy⟩
  have hpWb : p ∈ Wb := ⟨hpκ, Metric.mem_ball_self hδ⟩
  -- the causal curve from `σ` to `p`
  obtain ⟨σ, hσS, hσp⟩ := hpS
  have hσU : σ ∈ U := hSU hσS
  have hσne : σ ≠ p := fun h => hpU (h ▸ hσU)
  obtain ⟨γ, hγ, hγ0, hγ1⟩ := ((harc ⊤ le_rfl σ p).1).1 hσp
  have hγc : ContinuousOn γ (Icc 0 1) := Causal.CurveOn.continuousOn C.isRelFamily_le hγ
  set A : Set ℝ := Icc 0 1 ∩ γ ⁻¹' {p} with hAdef
  have hAc : IsClosed A := hγc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hA1 : (1 : ℝ) ∈ A := ⟨⟨zero_le_one, le_rfl⟩, hγ1⟩
  have hAb : BddBelow A := ⟨0, fun t ht => ht.1.1⟩
  set t₀ := sInf A with ht₀def
  have ht₀A : t₀ ∈ A := hAc.csInf_mem ⟨1, hA1⟩ hAb
  have ht₀pos : 0 < t₀ := by
    rcases ht₀A.1.1.lt_or_eq with h | h
    · exact h
    · exfalso; apply hσne
      rw [← hγ0, h]; exact ht₀A.2
  -- continuity of `γ` at `t₀` puts a final segment of the curve into `κ⁻¹ B(p₀, δ/2)`
  have hV : κ.source ∩ κ ⁻¹' Metric.ball p₀ (δ / 2) ∈ 𝓝 p :=
    (κ.isOpen_inter_preimage Metric.isOpen_ball).mem_nhds ⟨hpκ, Metric.mem_ball_self (by linarith)⟩
  have hcw : ContinuousWithinAt γ (Icc 0 1) t₀ := hγc t₀ ht₀A.1
  have hγt₀ : γ t₀ = p := ht₀A.2
  rw [ContinuousWithinAt, hγt₀] at hcw
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhdsWithin_iff.1 (hcw hV)
  set t := max (t₀ - ε / 2) (t₀ / 2) with htdef
  have ht0 : 0 ≤ t := le_max_of_le_right (by linarith)
  have htt₀ : t < t₀ := max_lt (by linarith) (by linarith)
  have ht₀1 : t₀ ≤ 1 := ht₀A.1.2
  have hseg : ∀ s ∈ Icc t t₀, γ s ∈ κ.source ∩ κ ⁻¹' Metric.ball p₀ (δ / 2) := by
    intro s hs
    refine hεV ⟨?_, ⟨ht0.trans hs.1, hs.2.trans ht₀1⟩⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    have : t₀ - ε / 2 ≤ t := le_max_left _ _
    constructor <;> linarith [hs.1, hs.2]
  have hsegWb : ∀ s ∈ Icc t t₀, γ s ∈ Wb := fun s hs =>
    ⟨(hseg s hs).1, Metric.ball_subset_ball (by linarith) (hseg s hs).2⟩
  set z := γ t with hzdef
  have hzseg := hseg t ⟨le_rfl, htt₀.le⟩
  have hzWb : z ∈ Wb := hsegWb t ⟨le_rfl, htt₀.le⟩
  have hzne : z ≠ p := by
    intro h
    have : t ∈ A := ⟨⟨ht0, htt₀.le.trans ht₀1⟩, h⟩
    exact absurd (csInf_le hAb this) (not_le.2 htt₀)
  have hσz : C.le ⊤ σ z := by
    have := hγ.le_of_le le_rfl ht0 (htt₀.le.trans ht₀1)
    rwa [hγ0] at this
  -- `z ≤ p` inside the ball: `z` is on the axis, below `p₀`
  have hzpWb : C.le Wb z p := by
    have hc : C.CausalCurveOn Wb γ t t₀ := Causal.CurveOn.restrict hγ ht0 ht₀1 le_top hsegWb
    have := hc.le_of_le le_rfl htt₀.le le_rfl
    rwa [hγt₀] at this
  have hLe : E0.Le (κ z) p₀ :=
    E0.le_of_le (((hiso Wb hWbκ z hzWb p hpWb).1).1 hzpWb)
  obtain ⟨hzax, hzle⟩ := (E0.le_axis_iff' hp₀).1 hLe
  have hzlt : (κ z).1 < p₀.1 := by
    refine lt_of_le_of_ne hzle fun h => hzne ?_
    exact κ.injOn hzWb.1 hpκ (E0.axis_eq_of_fst_eq hzax hp₀ h)
  have hzd : dist (κ z) p₀ < δ / 2 := hzseg.2
  have hzlow : p₀.1 - δ / 2 < (κ z).1 := by
    have h1 := E0.abs_fst_sub_le_dist (κ z) p₀
    have h2 := (abs_lt.1 (lt_of_le_of_lt h1 hzd)).1
    linarith
  -- `z ∈ U`: `J⁺(z)` is a neighbourhood of `p`, which meets `U`
  set c := (κ z).1 with hcdef
  have hQo : IsOpen (κ.source ∩ κ ⁻¹' (Metric.ball (κ z) (δ / 2) ∩ {y | c < E0.fcoord y})) :=
    κ.isOpen_inter_preimage (Metric.isOpen_ball.inter (E0.isOpen_fcoord_gt c))
  have hpQ : p ∈ κ.source ∩ κ ⁻¹' (Metric.ball (κ z) (δ / 2) ∩ {y | c < E0.fcoord y}) := by
    refine ⟨hpκ, ?_, ?_⟩
    · rw [Metric.mem_ball, dist_comm]; exact hzd
    · show c < E0.fcoord p₀
      rw [E0.fcoord_of_axis hp₀]; exact hzlt
  obtain ⟨u, ⟨huκ, hub, huf⟩, huU⟩ := mem_closure_iff.1 hpcl _ hQo hpQ
  have hball' : Metric.ball (κ z) (δ / 2) ⊆ Metric.ball p₀ δ := by
    intro y hy
    rw [Metric.mem_ball] at hy ⊢
    linarith [dist_triangle y (κ z) p₀]
  have huWb : u ∈ Wb := ⟨huκ, hball' hub⟩
  have hLe' : E0.Le (κ z) (κ u) := (E0.le_axis_iff hzax).2 (le_of_lt huf)
  have hzu' : E0.causality.le (Causal.chartImage κ Wb) (κ z) (κ u) :=
    E0.cle_ball_of_le_axis hzax hub hLe' (hball'.trans hballWb)
  have hzu : C.le ⊤ z u :=
    C.le_mono le_top (((hiso Wb hWbκ z hzWb u huWb).1).2 hzu')
  have hzU : z ∈ U := hconv.2 σ hσU u huU (Causal.Causality.mem_diamond.2 ⟨hσz, hzu⟩)
  exact ⟨z, ⟨hzU, hWbW hzWb⟩, hzax, hzlow, hzlt⟩

/-- **`SliceFutureBTZ` for `𝔼₀`-manifolds** (A4 future at BTZ boundary points; Sbierski Thm 3.6's
geometric half). At a BTZ point `p ∈ ∂U ∩ J⁺(S)`, in the paper chart `κ` at `p`: a point `z` of
`p`'s line strictly below `p` lies in `U` (`exists_axis_below_mem`); the level `{h = τ_z}` of the
domain `N = sliceDom (τ_z − η) (τ_p + δ/4) τ_z` is a Cauchy surface of `N`
(`E0.isCauchySurfaceOn_sliceDom`), `N` contains `κ p` (the BTZ point is above the level, in the
domain of dependence), lies in the chart image of `O`, and its level lies in the ball `B(κ z, η)`
inside `κ(U)`; `slice_assemble_of_chartIso` concludes. The corner condition is not used: the slice
is placed through a line point of `U` instead of on the punctured past cone (which at a BTZ point
is the line itself). -/
theorem e0_sliceFutureBTZ : E0SliceFutureBTZ := by
  intro M _ _ _ _ _ _ U S hGH _hGHU hSU hS hSU' p hp hpS _hc O hpO hp0
  set C := CE M with hCdef
  have harc : C.CausallyArcConnected := E0LM.e0_causallyArcConnected
  have hext : C.CurvesExtend := E0LM.e0_curvesExtend hGH
  have hconv : C.CausallyConvexIn (U : Set M) ⊤ :=
    Causal.Causality.causallyConvexIn_of_isCauchySurfaceOn hGH.1 harc hext le_top hSU hSU' hS
  have hpU : p ∉ U := fun h => hp.2 (by rwa [U.isOpen.interior_eq])
  have hpcl : p ∈ closure (U : Set M) := hp.1
  obtain ⟨hpκ, hp₀⟩ := paperChart_of_mem_S0 hp0
  set κ := paperChart p with hκdef
  set p₀ := κ p with hp₀def
  have hiso : Causal.ChartIso C E0.causality κ := chartIso_paperChart p
  let W₀ : Opens M := O ⊓ Causal.chartSource κ
  have hW₀κ : W₀ ≤ Causal.chartSource κ := inf_le_right
  have hpW₀ : p ∈ W₀ := ⟨hpO, hpκ⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (Causal.chartImage κ W₀).isOpen p₀
    (Causal.mem_chartImage_of_mem hpκ hpW₀)
  obtain ⟨z, ⟨hzU, hzW⟩, hzax, hzlow, hzlt⟩ :=
    exists_axis_below_mem hconv hSU hpU hpcl hpS hpκ hp₀ hδ hball
  -- the open `κ(W₀ ∩ U)` around `κ z`
  set G : Set E0 := κ '' ((W₀ : Set M) ∩ U) with hGdef
  have hGo : IsOpen G :=
    κ.isOpen_image_of_subset_source (W₀.isOpen.inter U.isOpen) fun x hx => hW₀κ hx.1
  obtain ⟨η₀, hη₀, hη₀G⟩ := Metric.isOpen_iff.1 hGo (κ z) ⟨z, ⟨hzW, hzU⟩, rfl⟩
  set η := min η₀ (δ / 4) with hηdef
  have hη : 0 < η := lt_min hη₀ (by linarith)
  have hηη₀ : η ≤ η₀ := min_le_left _ _
  have hηδ : η ≤ δ / 4 := min_le_right _ _
  set c := (κ z).1 with hcdef
  set a := c - η with hadef
  set b := p₀.1 + δ / 4 with hbdef
  have hcb : c < b := by rw [hbdef]; linarith
  have hrp : E0.rad p₀ = 0 := E0.rad_eq_zero.2 hp₀
  have hrz : E0.rad (κ z) = 0 := E0.rad_eq_zero.2 hzax
  refine slice_assemble_of_chartIso hiso hGH harc hext hSU hS hSU' hpU hpκ hW₀κ
    (N := E0.sliceDom a b c) (Γ := {y | E0.hcoord y = c} ∩ E0.sliceDom a b c) ?_ ?_
    inter_subset_right ?_ (E0.isCauchySurfaceOn_sliceDom hcb) inf_le_left
  · -- `N ⊆ B(p₀, δ) ⊆ κ(W₀)`
    intro y hy
    obtain ⟨h1, h2, h3⟩ := E0.mem_sliceDom.1 hy
    have hr := E0.rad_nonneg y
    simp only [E0.fcoord, E0.hcoord] at h1 h2
    refine hball ?_
    rw [Metric.mem_ball, E0.dist_axis hp₀, max_lt_iff, abs_lt]
    refine ⟨⟨by linarith, by linarith⟩, by linarith⟩
  · -- `κ p ∈ N`
    refine E0.mem_sliceDom.2 ⟨?_, ?_, ?_⟩
    · rw [E0.fcoord_of_axis hp₀]; linarith
    · simp only [E0.hcoord]; linarith
    · rw [hrp]; linarith
  · -- the level lies in `B(κ z, η) ⊆ κ(W₀ ∩ U)`
    rintro y ⟨hyc, hyN⟩
    obtain ⟨h1, -, -⟩ := E0.mem_sliceDom.1 hyN
    have hyc' : E0.hcoord y = c := hyc
    have hr := E0.rad_nonneg y
    simp only [E0.fcoord, E0.hcoord] at h1 hyc'
    refine hη₀G ?_
    rw [Metric.mem_ball, E0.dist_axis hzax, max_lt_iff, abs_lt]
    refine ⟨⟨by linarith, by linarith⟩, by linarith⟩

/-! ### §3d A3 at BTZ points: model and chart lemmas -/

section A3Helpers

/-- The regular part of `Y = 𝕄 ⊕ 𝔼₀`. -/
abbrev regE : Set E0Y := {y : E0Y | ∀ α : ℝ, 0 ≤ α → y ∉ e0SingY α}

/-- The `𝔼₀` component of `Y`: the component of a point of `BTZE0` is `range Sum.inr`. -/
theorem connectedComponent_inr (x : BTZE0) :
    connectedComponent (Sum.inr x : E0Y) = range Sum.inr := by
  refine Subset.antisymm (isClopen_range_inr.connectedComponent_subset (mem_range_self x)) ?_
  have hc : IsPreconnected (range (Sum.inr : BTZE0 → E0Y)) := by
    have h1 : range (Sum.inr : BTZE0 → E0Y) = range ((Sum.inr : BTZE0 → E0Y) ∘ E0.toPaper.symm) := by
      rw [range_comp, E0.toPaper.symm.range_coe, image_univ]
    rw [h1]
    exact isPreconnected_range (continuous_inr.comp E0.toPaper.symm.continuous)
  exact hc.subset_connectedComponent (mem_range_self x)

/-- A BTZ point of `Y` lies in the `𝔼₀` component. -/
theorem mem_range_inr_of_mem_e0SingY {y : E0Y} (hy : y ∈ e0SingY 0) : y ∈ range Sum.inr := by
  rw [E0LM.e0SingY_zero] at hy
  obtain ⟨a, -, he⟩ := hy
  rcases y with m | x
  · exact absurd he (show ¬ (Sum.inr a : E0.ModelY) = Sum.inl m from Sum.inr_ne_inl)
  · exact mem_range_self x

/-- A point of `Y` sent to the axis by `paperOfY` is a BTZ point. -/
theorem mem_e0SingY_of_paper {y : E0Y} (hy : y ∈ E0.paperOfY.source)
    (hax : E0.paperOfY y ∈ E0.axis) : y ∈ e0SingY 0 := by
  rw [E0.paperOfY_source] at hy
  obtain ⟨x, rfl⟩ := hy
  rw [E0.paperOfY_inr] at hax
  rw [E0LM.e0SingY_zero]
  exact ⟨E0.toPaper x, hax, rfl⟩

/-- The type of a point read in any chart of the atlas (B3 `sing_mem` on the transition;
`Causal.CBG.LocalModel.chartAt_mem_singY_iff`). -/
theorem chartAt_mem_e0SingY_iff {N : Type} [TopologicalSpace N] [ChartedSpace E0Y N]
    [HasGroupoid N e0Groupoid] {x w : N} (hw : w ∈ (chartAt E0Y x).source) {α : ℝ} (hα : 0 ≤ α) :
    chartAt E0Y x w ∈ e0SingY α ↔ chartAt E0Y w w ∈ e0SingY α := by
  have he : (chartAt E0Y x).symm.trans (chartAt E0Y w) ∈ e0Groupoid :=
    e0Groupoid.compatible (chart_mem_atlas _ x) (chart_mem_atlas _ w)
  have hmem : chartAt E0Y x w ∈ ((chartAt E0Y x).symm.trans (chartAt E0Y w)).source := by
    simp only [OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage,
      OpenPartialHomeomorph.symm_source]
    exact ⟨(chartAt _ x).map_source hw, by rw [(chartAt _ x).left_inv hw]; exact mem_chart_source _ w⟩
  have h := e0_sing_mem _ he _ hmem α hα
  have h2 : ((chartAt E0Y x).symm.trans (chartAt E0Y w)) (chartAt E0Y x w) = chartAt E0Y w w := by
    simp [(chartAt E0Y x).left_inv hw]
  rwa [h2] at h

/-- **B2 at a singular point, in charts, for `𝔼₀`** (`Causal.CBG.LocalModel.exists_eqOn_of_connected_sing`
with `e0_localUnique_sing`; no local model is needed). -/
theorem e0_exists_eqOn_of_connected_sing {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace E0Y M] [ChartedSpace E0Y N] [HasGroupoid M e0Groupoid] [HasGroupoid N e0Groupoid]
    {κ : OpenPartialHomeomorph M E0Y} {κ' : OpenPartialHomeomorph N E0Y}
    (hκ : κ ∈ e0Groupoid.maximalAtlas M) (hκ' : κ' ∈ e0Groupoid.maximalAtlas N) {ψ : M → N}
    {B : Set M} (hBo : IsOpen B) (hBc : IsPreconnected B) (hB : B ⊆ κ.source) {b₀ : M}
    (hb₀ : b₀ ∈ B) {α₀ : ℝ} (hα₀ : 0 ≤ α₀) (hsing : κ b₀ ∈ e0SingY α₀)
    (hAψ : MapsTo ψ (B ∩ κ ⁻¹' regE) κ'.source)
    (hψ : ChartedSpace.LiftPropOn e0Groupoid.IsLocalStructomorphWithinAt ψ (B ∩ κ ⁻¹' regE))
    (hinj : InjOn ψ (B ∩ κ ⁻¹' regE))
    (hcomp : ∀ z ∈ B ∩ κ ⁻¹' regE, κ' (ψ z) ∈ connectedComponent (κ b₀)) :
    ∃ e ∈ e0Groupoid, connectedComponent (κ b₀) ⊆ e.source ∧
      ∀ z ∈ B ∩ κ ⁻¹' regE, κ' (ψ z) = e (κ z) := by
  have hG := StructureGroupoid.isLocalStructomorphWithinAt_localInvariantProp e0Groupoid
  set A := B ∩ κ ⁻¹' regE
  have hA : A ⊆ κ.source := fun z hz => hB hz.1
  set U := κ '' B
  have hUo : IsOpen U := κ.isOpen_image_of_subset_source hBo hB
  have hUc : IsConnected U := ⟨⟨_, b₀, hb₀, rfl⟩, hBc.image _ (κ.continuousOn.mono hB)⟩
  have hreg : U ∩ regE = κ '' A := by
    ext y
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hy⟩; exact ⟨z, ⟨hz, hy⟩, rfl⟩
    · rintro ⟨z, hz, rfl⟩; exact ⟨⟨z, hz.1, rfl⟩, hz.2⟩
  set f : E0Y → E0Y := κ' ∘ ψ ∘ κ.symm
  have hfA : ∀ z ∈ A, f (κ z) = κ' (ψ z) := fun z hz => by
    simp only [f, comp_apply, κ.left_inv (hA hz)]
  have hloc : ∀ y ∈ U ∩ regE, e0Groupoid.IsLocalStructomorphWithinAt f (U ∩ regE) y := by
    rw [hreg]
    rintro _ ⟨z, hz, rfl⟩
    have hP := hG.liftPropOn_indep_chart hκ hκ' hψ
      (y := κ z) ⟨κ.map_source (hA hz), by
        simp only [mem_preimage, κ.left_inv (hA hz)]; exact ⟨hz, hAψ hz⟩⟩
    intro hy
    obtain ⟨e, he, hef, hex⟩ := hP (by simp only [mem_preimage, κ.left_inv (hA hz)]; exact hz)
    refine ⟨e, he, fun y hy => hef ⟨?_, hy.2⟩, hex⟩
    obtain ⟨w, hw, rfl⟩ := hy.1
    simp only [mem_preimage, κ.left_inv (hA hw)]; exact hw
  have hinjf : InjOn f (U ∩ regE) := by
    rw [hreg]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    rw [hfA a ha, hfA b hb] at hab
    rw [hinj ha hb (κ'.injOn (hAψ ha) (hAψ hb) hab)]
  have hmaps : MapsTo f (U ∩ regE) (connectedComponent (κ b₀)) := by
    rw [hreg]
    rintro _ ⟨z, hz, rfl⟩
    rw [hfA z hz]; exact hcomp z hz
  obtain ⟨e, he, hsrc, heq⟩ := e0_localUnique_sing U hUo hUc (κ b₀) ⟨b₀, hb₀, rfl⟩ α₀ hα₀ hsing
    f hloc hinjf hmaps
  refine ⟨e, he, hsrc, fun z hz => ?_⟩
  rw [← hfA z hz]
  have hmem : κ z ∈ U ∩ regE := by rw [hreg]; exact ⟨z, hz, rfl⟩
  exact heq hmem

/-- **The extension from one element of `G`** (`Causal.CBG.LocalModel.exists_extension_of_eqOn`
for `e0Groupoid`). -/
theorem e0_exists_extension_of_eqOn {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace E0Y M] [ChartedSpace E0Y N] [HasGroupoid M e0Groupoid] [HasGroupoid N e0Groupoid]
    {κ : OpenPartialHomeomorph M E0Y} {κ' : OpenPartialHomeomorph N E0Y}
    (hκ : κ ∈ e0Groupoid.maximalAtlas M) (hκ' : κ' ∈ e0Groupoid.maximalAtlas N)
    {e : OpenPartialHomeomorph E0Y E0Y} (he : e ∈ e0Groupoid) {ψ : M → N} {A : Set M}
    (hAψ : MapsTo ψ A κ'.source) (heq : ∀ z ∈ A, κ' (ψ z) = e (κ z)) :
    ∃ O : Set M, IsOpen O ∧ O = κ.source ∩ κ ⁻¹' (e.source ∩ e ⁻¹' κ'.target) ∧
      ChartedSpace.LiftPropOn e0Groupoid.IsLocalStructomorphWithinAt (κ'.symm ∘ e ∘ κ) O ∧
      EqOn (κ'.symm ∘ e ∘ κ) ψ (O ∩ A) := by
  have hO : IsOpen (κ.source ∩ κ ⁻¹' (e.source ∩ e ⁻¹' κ'.target)) :=
    κ.isOpen_inter_preimage (e.isOpen_inter_preimage κ'.open_target)
  refine ⟨_, hO, rfl, ?_, ?_⟩
  · refine Causal.CBG.liftPropOn_of_maximalAtlas_rep hκ hκ' hO (fun z hz => hz.1) ?_ ?_ he
      (fun z hz => hz.2.1) ?_
    · intro z hz; exact κ'.map_target hz.2.2
    · refine κ'.continuousOn_symm.comp
        (e.continuousOn.comp (κ.continuousOn.mono fun z hz => hz.1) ?_) ?_
      · intro z hz; exact hz.2.1
      · intro z hz; exact hz.2.2
    · intro z hz
      simp only [comp_apply]
      exact κ'.right_inv hz.2.2
  · intro z hz
    simp only [comp_apply]
    rw [← heq z hz.2, κ'.left_inv (hAψ hz.2)]

/-- A relation of `𝔼₀` from an axis point, inside a ball in a chart image, read in `M` (`⊤`). -/
theorem le_top_of_axis_ball {M : Type} [TopologicalSpace M] [ChartedSpace E0Y M]
    {κ : OpenPartialHomeomorph M E0} (hiso : Causal.ChartIso (CE M) E0.causality κ) {V : Opens M}
    (hV : V ≤ Causal.chartSource κ) {x y : M} (hx : x ∈ V) (hy : y ∈ V) (hax : κ x ∈ E0.axis)
    {r : ℝ} (hyr : κ y ∈ Metric.ball (κ x) r) (hball : Metric.ball (κ x) r ⊆ Causal.chartImage κ V)
    (hle : E0.Le (κ x) (κ y)) : (CE M).le ⊤ x y :=
  (CE M).le_mono le_top (((hiso V hV x hx y hy).1).2 (E0.cle_ball_of_le_axis hax hyr hle hball))

/-- **A morphism preserves the causal relation of `⊤` between points of a causally convex open
set** (the first half of `Causal.CBG.isCorrPair_of_cghd`, for `𝔼₀`). -/
theorem map_le_top_of_causallyConvex {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace E0Y M] [ChartedSpace E0Y N] [HasGroupoid M e0Groupoid] [HasGroupoid N e0Groupoid]
    {U : Opens M} {ψ : M → N}
    (hψ : ChartedSpace.LiftPropOn e0Groupoid.IsLocalStructomorphWithinAt ψ U)
    (hconv : (CE M).CausallyConvexIn (U : Set M) ⊤) {x y : M} (hx : x ∈ U) (hy : y ∈ U)
    (hxy : (CE M).le ⊤ x y) : (CE N).le ⊤ (ψ x) (ψ y) := by
  have hE := Causal.CBG.isEMorphismOn_of_liftPropOn E0.chartIso_mem_e0Groupoid
    E0.absolutelyMinimalOn_YBTZ hψ
  have h1 : (CE M).le U x y := Causal.Causality.le_of_causallyConvexIn_of_le
    E0LM.e0_causallyArcConnected hconv subset_rfl le_top hx hy hxy
  exact hE.map_le U ⊤ le_rfl (fun _ _ => trivial) h1

/-- **A morphism preserves the chronological relation of `⊤` between points of a causally convex
open set**. -/
theorem map_lt_top_of_causallyConvex {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace E0Y M] [ChartedSpace E0Y N] [HasGroupoid M e0Groupoid] [HasGroupoid N e0Groupoid]
    {U : Opens M} {ψ : M → N}
    (hψ : ChartedSpace.LiftPropOn e0Groupoid.IsLocalStructomorphWithinAt ψ U)
    (hconv : (CE M).CausallyConvexIn (U : Set M) ⊤) {x y : M} (hx : x ∈ U) (hy : y ∈ U)
    (hxy : (CE M).lt ⊤ x y) : (CE N).lt ⊤ (ψ x) (ψ y) := by
  have hE := Causal.CBG.isEMorphismOn_of_liftPropOn E0.chartIso_mem_e0Groupoid
    E0.absolutelyMinimalOn_YBTZ hψ
  have h1 : (CE M).lt U x y := Causal.Causality.lt_of_causallyConvexIn
    E0LM.e0_causallyArcConnected hconv hx hy hxy
  exact hE.map_lt U ⊤ le_rfl (fun _ _ => trivial) h1

/-- The chronology of `⊤` between two points of a causally convex `K ⊆ W` is the chronology of
`W` (the chronal curve stays in the diamond, so in `K`). -/
theorem lt_of_causallyConvex_subset {X : Type*} [TopologicalSpace X] {C : Causal.Causality X}
    (harc : C.CausallyArcConnected) {K : Set X} {W : Opens X} (hKW : K ⊆ W)
    (hKcv : C.CausallyConvexIn K ⊤) {x y : X} (hx : x ∈ K) (hy : y ∈ K) (hxy : C.lt ⊤ x y) :
    C.lt W x y := by
  obtain ⟨c, hc, hc0, hc1⟩ := ((harc ⊤ le_rfl x y).2).1 hxy
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, c t ∈ W := fun t ht => by
    have h1 : C.le ⊤ (c 0) (c t) := hc.causalCurveOn.le_of_le le_rfl ht.1 ht.2
    have h2 : C.le ⊤ (c t) (c 1) := hc.causalCurveOn.le_of_le ht.1 ht.2 le_rfl
    rw [hc0] at h1
    rw [hc1] at h2
    exact hKW (hKcv.2 x hx y hy (Causal.Causality.mem_diamond.2 ⟨h1, h2⟩))
  exact ((harc W le_top x y).2).2 ⟨c, Causal.CurveOn.restrict hc le_rfl le_rfl le_top hmem, hc0, hc1⟩

end A3Helpers

/-! ### §3e A3 at BTZ points -/

/-- **`GermExtFutureBTZ` for `𝔼₀`-manifolds** (A3 future at BTZ boundary points; Sbierski
Lemma 3.8 at a BTZ point, thesis `lem:passe_pgcd` `these.tex:6541`, A3-B-INVESTIGATION.md §3).
In the paper chart `κ` at `p` (`κ p = (τ, 0)` on the axis):
1. the line points `x_c = κ⁻¹(c, 0)`, `c ∈ [c₀, τ[`, lie in `U` (`exists_axis_below_mem` gives
   `x_{c₀} ∈ U`; then `x_{c₀} ≤ x_c ≤ u` for `u ∈ U` near `p`, causal convexity) and form an
   increasing causal family;
2. `ψ(x_c) ≤ q` (`J⁺(x_c)` is a neighbourhood of `p`, `ψ` preserves `≤` on `U`, `q` is a cluster
   point and `J⁺(ψ x_c)` is closed), so `ψ(x_c)` stays in the compact diamond
   `J⁺(ψ x_{c₀}) ∩ J⁻(q)`, where its cluster points are all equal (each lies above every
   `ψ(x_c)` and below every other, `J^±` closed, `N` causal): `ψ(x_c) → q*`;
3. B2 at a singular point (`e0_localUnique_sing`) on the connected piece of
   `U ∩ κ.source ∩ ψ⁻¹(chart at q*)` through the segment `x_{[c₁, τ[}` gives one `e ∈ G`, extended
   to the whole piece by density of the regular part; `e(κ p) = κ*(q*)` by continuity along the
   segment, so `φ = κ*⁻¹ ∘ e ∘ κ` is a morphism near `p` with `φ p = q*`;
4. `φ = ψ` on `O ∩ U` for a small open `O ∋ p` (B1 rigidity on the component of `O₀ ∩ U` through
   a line point `z'`: every `y ∈ O ∩ U` is joined to `z'` by a causal curve inside a causally
   convex neighbourhood of `p` and inside `U`); hence `ψ → q*` along `U` at `p`, and the cluster
   point `q` is `q*`. -/
theorem e0_germExtFutureBTZ : E0GermExtFutureBTZ := by
  intro M N _ _ _ _ _ _ _ _ _ _ _ _ U ψ S hψ hinj hGM hGN _hGU _hGV hSU hS hSU' _hψS _hψSV p q hp
    hpS hcl hp0
  haveI : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace E0Y M
  set CM := CE M with hCMdef
  set CN := CE N with hCNdef
  have harcM : CM.CausallyArcConnected := E0LM.e0_causallyArcConnected
  have hextM : CM.CurvesExtend := E0LM.e0_curvesExtend hGM
  have hconv : CM.CausallyConvexIn (U : Set M) ⊤ :=
    Causal.Causality.causallyConvexIn_of_isCauchySurfaceOn hGM.1 harcM hextM le_top hSU hSU' hS
  have hpU : p ∉ U := fun h => hp.2 (by rwa [U.isOpen.interior_eq])
  have hpcl : p ∈ closure (U : Set M) := hp.1
  have hTM : CM.Tarentin := E0LM.e0_tarentin
  have hTN : CN.Tarentin := E0LM.e0_tarentin
  have hSCM : CM.StronglyCausal := hGM.stronglyCausal hTM
  have hclN : ∀ y, IsClosed (CN.Jplus ⊤ {y}) := hGN.isClosed_Jplus_singleton hTN
  have hclN' : ∀ y, IsClosed (CN.Jminus ⊤ {y}) := hGN.isClosed_Jminus_singleton hTN
  have hψc : ContinuousOn ψ U := fun y hy => (hψ y hy).continuousWithinAt
  obtain ⟨hpκ, hp₀⟩ := paperChart_of_mem_S0 hp0
  set κ := paperChart p with hκdef
  set p₀ := κ p with hp₀def
  have hiso : Causal.ChartIso CM E0.causality κ := chartIso_paperChart p
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (Causal.chartImage κ (Causal.chartSource κ)).isOpen
    p₀ (Causal.mem_chartImage_of_mem hpκ hpκ)
  obtain ⟨z, ⟨hzU, hzκ⟩, hzax, hzlow, hzlt⟩ :=
    exists_axis_below_mem hconv hSU hpU hpcl hpS hpκ hp₀ hδ hball
  -- the ball around `p₀`, read in `M`
  let Wb : Opens M := ⟨κ.source ∩ κ ⁻¹' Metric.ball p₀ δ,
    κ.isOpen_inter_preimage Metric.isOpen_ball⟩
  have hWbκ : Wb ≤ Causal.chartSource κ := fun x hx => hx.1
  have hballWb : Metric.ball p₀ δ ⊆ Causal.chartImage κ Wb := by
    intro y hy
    obtain ⟨w, hws, -, rfl, -⟩ := Causal.exists_of_mem_chartImage (hball hy)
    exact Causal.mem_chartImage_of_mem hws ⟨hws, hy⟩
  set τ := p₀.1 with hτdef
  set c₀ := (κ z).1 with hc₀def
  -- the line points `x_c = κ⁻¹(c, 0)`
  set xl : ℝ → M := fun c => κ.symm (c, 0) with hxldef
  have hmemball : ∀ c, |c - τ| < δ → ((c, 0) : E0) ∈ Metric.ball p₀ δ := by
    intro c hc
    rw [Metric.mem_ball, E0.dist_axis hp₀, max_lt_iff]
    refine ⟨hc, ?_⟩
    show ‖(0 : ℂ)‖ < δ
    rw [norm_zero]; exact hδ
  have hxl : ∀ c, |c - τ| < δ → xl c ∈ Wb ∧ κ (xl c) = (c, 0) := by
    intro c hc
    obtain ⟨w, -, hwW, hwe, hwsymm⟩ := Causal.exists_of_mem_chartImage (hballWb (hmemball c hc))
    have : xl c = w := hwsymm
    rw [this]
    exact ⟨hwW, hwe⟩
  have hrange : ∀ c, c₀ ≤ c → c ≤ τ → |c - τ| < δ := by
    intro c h1 h2
    rw [abs_lt]; constructor <;> linarith
  have hκz : κ z = (c₀, 0) := Prod.ext rfl hzax
  have hzxl : xl c₀ = z := by
    show κ.symm (c₀, 0) = z
    rw [← hκz]; exact κ.left_inv hzκ
  have hpxl : xl τ = p := by
    show κ.symm (τ, 0) = p
    have : ((τ, 0) : E0) = p₀ := Prod.ext rfl hp₀.symm
    rw [this]; exact κ.left_inv hpκ
  have haxis : ∀ c : ℝ, ((c, 0) : E0) ∈ E0.axis := fun c => rfl
  have hdist : ∀ c, |c - τ| ≤ δ / 2 → dist ((c, 0) : E0) p₀ ≤ δ / 2 := by
    intro c hc
    rw [E0.dist_axis hp₀, max_le_iff]
    refine ⟨hc, ?_⟩
    show ‖(0 : ℂ)‖ ≤ δ / 2
    rw [norm_zero]; linarith
  -- the line is increasing
  have hle_line : ∀ c c', c₀ ≤ c → c ≤ c' → c' ≤ τ → CM.le ⊤ (xl c) (xl c') := by
    intro c c' h1 h2 h3
    obtain ⟨hcW, hcκ⟩ := hxl c (hrange c h1 (h2.trans h3))
    obtain ⟨hc'W, hc'κ⟩ := hxl c' (hrange c' (h1.trans h2) h3)
    refine le_top_of_axis_ball hiso hWbκ hcW hc'W (by rw [hcκ]; exact haxis c) (r := δ / 2) ?_ ?_ ?_
    · rw [hcκ, hc'κ, Metric.mem_ball, E0.dist_axis (haxis c), max_lt_iff]
      refine ⟨?_, ?_⟩
      · show |c' - c| < δ / 2
        rw [abs_lt]; constructor <;> linarith
      · show ‖(0 : ℂ)‖ < δ / 2
        rw [norm_zero]; linarith
    · rw [hcκ]
      refine (Metric.ball_subset_ball' ?_).trans hballWb
      have := hdist c (by rw [abs_le]; constructor <;> linarith)
      linarith
    · rw [hcκ, hc'κ]; exact E0.le_axis (haxis c) (haxis c') h2
  -- `J⁺(x_c)` is a neighbourhood of `p`
  have hJ : ∀ c, c₀ ≤ c → c < τ → ∃ Q ∈ 𝓝 p, ∀ u ∈ Q, CM.le ⊤ (xl c) u := by
    intro c h1 h2
    obtain ⟨hcW, hcκ⟩ := hxl c (hrange c h1 h2.le)
    have hsub : Metric.ball ((c, 0) : E0) (δ / 2) ⊆ Metric.ball p₀ δ := by
      refine Metric.ball_subset_ball' ?_
      have := hdist c (by rw [abs_le]; constructor <;> linarith)
      linarith
    refine ⟨κ.source ∩ κ ⁻¹' (Metric.ball ((c, 0) : E0) (δ / 2) ∩ {y | c < E0.fcoord y}),
      (κ.isOpen_inter_preimage (Metric.isOpen_ball.inter (E0.isOpen_fcoord_gt c))).mem_nhds
        ⟨hpκ, ?_, ?_⟩, ?_⟩
    · rw [Metric.mem_ball, E0.dist_axis (haxis c), max_lt_iff]
      refine ⟨?_, ?_⟩
      · show |τ - c| < δ / 2
        rw [abs_lt]; constructor <;> linarith
      · rw [E0.rad_eq_zero.2 hp₀]; linarith
    · show c < E0.fcoord p₀
      rw [E0.fcoord_of_axis hp₀]; exact h2
    · rintro u ⟨huκ, hub, huf⟩
      have huW : u ∈ Wb := ⟨huκ, hsub hub⟩
      refine le_top_of_axis_ball hiso hWbκ hcW huW (by rw [hcκ]; exact haxis c) (r := δ / 2)
        (by rw [hcκ]; exact hub) (by rw [hcκ]; exact hsub.trans hballWb) ?_
      rw [hcκ]
      exact (E0.le_axis_iff (haxis c)).2 (le_of_lt huf)
  -- the line below `p` lies in `U`
  have hlineU : ∀ c, c₀ ≤ c → c < τ → xl c ∈ U := by
    intro c h1 h2
    obtain ⟨Q, hQ, hQle⟩ := hJ c h1 h2
    obtain ⟨u, huQ, huU⟩ := mem_closure_iff_nhds.1 hpcl Q hQ
    have hzc : CM.le ⊤ z (xl c) := by
      have := hle_line c₀ c le_rfl h1 h2.le
      rwa [hzxl] at this
    exact hconv.2 z hzU u huU (Causal.Causality.mem_diamond.2 ⟨hzc, hQle u huQ⟩)
  -- `ψ(x_c) ≤ q`
  have hψq : ∀ c, c₀ ≤ c → c < τ → CN.le ⊤ (ψ (xl c)) q := by
    intro c h1 h2
    obtain ⟨Q, hQ, hQle⟩ := hJ c h1 h2
    have hF : CN.Jplus ⊤ {ψ (xl c)} ∈ map ψ (𝓝[(U : Set M)] p) := by
      rw [Filter.mem_map]
      refine mem_nhdsWithin_iff_exists_mem_nhds_inter.2 ⟨Q, hQ, fun u hu => ?_⟩
      rw [mem_preimage, Causal.Precausality.mem_Jplus_singleton]
      exact map_le_top_of_causallyConvex hψ hconv (hlineU c h1 h2) hu.2 (hQle u hu.1)
    have hq := ClusterPt.mem_closure_of_mem hcl _ hF
    rw [(hclN _).closure_eq, Causal.Precausality.mem_Jplus_singleton] at hq
    exact hq
  -- the family `ψ(x_c)` converges, as `c ↑ τ`, in the compact diamond `J⁺(ψ z) ∩ J⁻(q)`
  set g : ℝ → N := ψ ∘ xl with hgdef
  set l : Filter ℝ := 𝓝[<] τ with hldef
  have hc₀τ : c₀ < τ := hzlt
  have hev : ∀ᶠ c in l, c ∈ Ioo c₀ τ := Ioo_mem_nhdsLT hc₀τ
  set K := CN.diamond ⊤ (ψ z) q with hKdef
  have hK : IsCompact K := hGN.2 (ψ z) q
  have hgK : ∀ᶠ c in l, g c ∈ K := hev.mono fun c hc => by
    refine Causal.Causality.mem_diamond.2 ⟨?_, hψq c hc.1.le hc.2⟩
    have := map_le_top_of_causallyConvex hψ hconv hzU (hlineU c hc.1.le hc.2)
      (by have h := hle_line c₀ c le_rfl hc.1.le hc.2.le; rwa [hzxl] at h)
    exact this
  have hup : ∀ y, MapClusterPt y l g → ∀ c, c₀ ≤ c → c < τ → CN.le ⊤ (g c) y := by
    intro y hy c h1 h2
    have hF : CN.Jplus ⊤ {g c} ∈ map g l := by
      rw [Filter.mem_map]
      filter_upwards [Ioo_mem_nhdsLT h2] with c' hc'
      rw [mem_preimage, Causal.Precausality.mem_Jplus_singleton]
      exact map_le_top_of_causallyConvex hψ hconv (hlineU c h1 h2)
        (hlineU c' (h1.trans hc'.1.le) hc'.2) (hle_line c c' h1 hc'.1.le hc'.2.le)
    have h := ClusterPt.mem_closure_of_mem hy _ hF
    rw [(hclN _).closure_eq, Causal.Precausality.mem_Jplus_singleton] at h
    exact h
  have huniq : ∀ y₁ y₂, MapClusterPt y₁ l g → MapClusterPt y₂ l g → CN.le ⊤ y₁ y₂ := by
    intro y₁ y₂ h₁ h₂
    have hF : CN.Jminus ⊤ {y₂} ∈ map g l := by
      rw [Filter.mem_map]
      filter_upwards [hev] with c hc
      rw [mem_preimage, Causal.Precausality.mem_Jminus_singleton]
      exact hup y₂ h₂ c hc.1.le hc.2
    have h := ClusterPt.mem_closure_of_mem h₁ _ hF
    rw [(hclN' _).closure_eq, Causal.Precausality.mem_Jminus_singleton] at h
    exact h
  obtain ⟨q', -, hq'cl⟩ := hK.exists_mapClusterPt (f := l) (u := g)
    (tendsto_principal.2 hgK)
  have hT : Tendsto g l (𝓝 q') := hK.tendsto_nhds_of_unique_mapClusterPt hgK
    fun y _ hy => hGN.1 (huniq y q' hy hq'cl) (huniq q' y hq'cl hy)
  -- the chart at `q*`, and a final segment of the line mapped into it
  set κs := chartAt E0Y q' with hκsdef
  have hevs : ∀ᶠ c in l, g c ∈ κs.source :=
    hT.eventually (κs.open_source.mem_nhds (mem_chart_source E0Y q'))
  obtain ⟨l₁, hl₁, hl₁sub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 (hevs.and hev)
  set c₁ := max l₁ c₀ + (τ - max l₁ c₀) / 2 with hc₁def
  have hmaxlt : max l₁ c₀ < τ := max_lt hl₁ hc₀τ
  have hc₁τ : c₁ < τ := by rw [hc₁def]; linarith
  have hc₀c₁ : c₀ < c₁ := by rw [hc₁def]; linarith [le_max_right l₁ c₀]
  have hIco : ∀ c ∈ Ico c₁ τ, g c ∈ κs.source ∧ c₀ < c ∧ c < τ := by
    intro c hc
    have hl : l₁ < c := by
      have : l₁ ≤ max l₁ c₀ := le_max_left _ _
      rw [hc₁def] at hc; linarith [hc.1]
    have := hl₁sub ⟨hl, hc.2⟩
    exact ⟨this.1, this.2.1, this.2.2⟩
  -- the preferred chart at `p`
  set κY := chartAt E0Y p with hκYdef
  have hκYmax : κY ∈ e0Groupoid.maximalAtlas M := e0Groupoid.chart_mem_maximalAtlas p
  have hκsmax : κs ∈ e0Groupoid.maximalAtlas N := e0Groupoid.chart_mem_maximalAtlas q'
  have hκsrc : ∀ x, x ∈ κ.source → x ∈ κY.source ∧ κY x ∈ E0.paperOfY.source := fun x hx => hx
  have hκapp : ∀ x, κ x = E0.paperOfY (κY x) := fun x => rfl
  -- the piece: the component of `κY.source ∩ U ∩ ψ⁻¹ κs.source` through the final segment
  set Bset : Set M := κY.source ∩ ((U : Set M) ∩ ψ ⁻¹' κs.source) with hBsetdef
  have hBseto : IsOpen Bset :=
    κY.open_source.inter (hψc.isOpen_inter_preimage U.isOpen κs.open_source)
  set b₀ := xl c₁ with hb₀def
  have hxlI : ∀ c ∈ Ico c₁ τ, xl c ∈ Bset := by
    intro c hc
    obtain ⟨hgs, h1, h2⟩ := hIco c hc
    exact ⟨(hκsrc _ (hxl c (hrange c h1.le h2.le)).1.1).1, hlineU c h1.le h2, hgs⟩
  have hb₀B' : b₀ ∈ Bset := hxlI c₁ ⟨le_rfl, hc₁τ⟩
  set B := connectedComponentIn Bset b₀ with hBdef
  have hBo : IsOpen B := hBseto.connectedComponentIn
  have hBc : IsPreconnected B := isPreconnected_connectedComponentIn
  have hBsub : B ⊆ Bset := connectedComponentIn_subset _ _
  have hb₀B : b₀ ∈ B := mem_connectedComponentIn hb₀B'
  have hxlc : ContinuousOn xl (Ico c₁ τ) := by
    refine κ.continuousOn_symm.comp (continuous_id.prodMk continuous_const).continuousOn ?_
    intro c hc
    obtain ⟨-, h1, h2⟩ := hIco c hc
    obtain ⟨hcW, hcκ⟩ := hxl c (hrange c h1.le h2.le)
    have := κ.map_source hcW.1
    rw [hcκ] at this
    exact this
  have hSegB : xl '' Ico c₁ τ ⊆ B :=
    (isPreconnected_Ico.image xl hxlc).subset_connectedComponentIn
      ⟨c₁, ⟨le_rfl, hc₁τ⟩, rfl⟩ (by rintro _ ⟨c, hc, rfl⟩; exact hxlI c hc)
  have hBκY : B ⊆ κY.source := fun w hw => (hBsub hw).1
  have hBU : B ⊆ U := fun w hw => (hBsub hw).2.1
  have hBψ : MapsTo ψ B κs.source := fun w hw => (hBsub hw).2.2
  -- `b₀` is a BTZ point, so is `ψ b₀`; the piece lands in the `𝔼₀` component on both sides
  obtain ⟨hb₀W, hb₀κ⟩ := hxl c₁ (hrange c₁ hc₀c₁.le hc₁τ.le)
  have hb₀sing : κY b₀ ∈ e0SingY 0 :=
    mem_e0SingY_of_paper (hκsrc _ hb₀W.1).2 (by rw [← hκapp, hb₀κ]; exact haxis c₁)
  have hb₀S0 : b₀ ∈ S0 M := (chartAt_mem_e0SingY_iff (hBκY hb₀B) le_rfl).1 hb₀sing
  have hψb₀ : ψ b₀ ∈ S0 N :=
    (Causal.CBG.mem_chartedSing_iff_of_liftPropOn e0_sing_mem U.isOpen hψ (hBU hb₀B) le_rfl).1
      hb₀S0
  have hψb₀sing : κs (ψ b₀) ∈ e0SingY 0 := (chartAt_mem_e0SingY_iff (hBψ hb₀B) le_rfl).2 hψb₀
  obtain ⟨xb, hxb⟩ := mem_range_inr_of_mem_e0SingY hb₀sing
  have hcc : connectedComponent (κY b₀) = range Sum.inr := by
    rw [← hxb]; exact connectedComponent_inr xb
  have hψcB : ContinuousOn ψ B := hψc.mono hBU
  have himgN : κs ∘ ψ '' B ⊆ range Sum.inr :=
    (hBc.image _ (κs.continuousOn.comp hψcB hBψ)).subset_isClopen isClopen_range_inr
      ⟨κs (ψ b₀), ⟨b₀, hb₀B, rfl⟩, mem_range_inr_of_mem_e0SingY hψb₀sing⟩
  have himgM : κY '' B ⊆ range Sum.inr :=
    (hBc.image _ (κY.continuousOn.mono hBκY)).subset_isClopen isClopen_range_inr
      ⟨κY b₀, ⟨b₀, hb₀B, rfl⟩, mem_range_inr_of_mem_e0SingY hb₀sing⟩
  -- B2 at the singular point `b₀`, on the regular part of the piece
  have hBro : IsOpen (B ∩ κY ⁻¹' regE) := by
    have h := hBo.inter (κY.isOpen_inter_preimage e0_isOpen_regY)
    convert h using 1
    ext w
    exact ⟨fun hw => ⟨hw.1, hBκY hw.1, hw.2⟩, fun hw => ⟨hw.1, hw.2.2⟩⟩
  obtain ⟨e, he, hsrc, heqr⟩ := e0_exists_eqOn_of_connected_sing hκYmax hκsmax hBo hBc hBκY
    hb₀B le_rfl hb₀sing (hBψ.mono_left inter_subset_left)
    (Causal.CBG.liftPropOn_mono_of_le U.isOpen hBro hψ fun w hw => hBU hw.1)
    (hinj.mono fun w hw => hBU hw.1)
    (fun w hw => by rw [hcc]; exact himgN ⟨w, hw.1, rfl⟩)
  have hAe : MapsTo κY B e.source := fun w hw => hsrc (by rw [hcc]; exact himgM ⟨w, hw, rfl⟩)
  -- the regular part of the piece is dense in it, so the agreement extends to the piece
  have hdense : B ⊆ closure (B ∩ κY ⁻¹' regE) := by
    intro w hw
    rw [mem_closure_iff_nhds]
    intro t ht
    have hto : IsOpen (interior t ∩ B) := isOpen_interior.inter hBo
    have hne : (κY '' (interior t ∩ B)).Nonempty :=
      ⟨κY w, w, ⟨mem_interior_iff_mem_nhds.2 ht, hw⟩, rfl⟩
    obtain ⟨_, ⟨w', hw', rfl⟩, hw'reg⟩ := e0_dense_regY.inter_open_nonempty _
      (κY.isOpen_image_of_subset_source hto fun x hx => hBκY hx.2) hne
    exact ⟨w', interior_subset hw'.1, hw'.2, hw'reg⟩
  have heq : ∀ w ∈ B, κs (ψ w) = e (κY w) := by
    have h := Set.EqOn.of_subset_closure (f := fun w => κs (ψ w)) (g := fun w => e (κY w))
      (s := B ∩ κY ⁻¹' regE) (t := B) (fun w hw => heqr w hw)
      (κs.continuousOn.comp hψcB hBψ) (e.continuousOn.comp (κY.continuousOn.mono hBκY) hAe)
      inter_subset_left hdense
    exact fun w hw => h hw
  -- `e(κY p) = κs(q*)`, by continuity along the segment
  have hκpe : κY p ∈ e.source := by
    refine hsrc ?_
    rw [hcc]
    have hx : κY p ∈ E0.paperOfY.source := (hκsrc p hpκ).2
    rw [E0.paperOfY_source] at hx
    exact hx
  have hxlT : Tendsto xl l (𝓝 p) := by
    have hc : ContinuousAt xl τ := by
      refine (κ.continuousAt_symm ?_).comp (continuous_id.prodMk continuous_const).continuousAt
      have : ((τ, 0) : E0) = p₀ := Prod.ext rfl hp₀.symm
      show ((τ, 0) : E0) ∈ κ.target
      rw [this]; exact κ.map_source hpκ
    have := hc.tendsto
    rw [hpxl] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hep : e (κY p) = κs q' := by
    have h1 : Tendsto (fun c => e (κY (xl c))) l (𝓝 (e (κY p))) :=
      ((e.continuousAt hκpe).comp (κY.continuousAt (mem_chart_source E0Y p))).tendsto.comp hxlT
    have h2 : Tendsto (fun c => e (κY (xl c))) l (𝓝 (κs q')) := by
      refine ((κs.continuousAt (mem_chart_source E0Y q')).tendsto.comp hT).congr' ?_
      filter_upwards [Ico_mem_nhdsLT hc₁τ] with c hc
      exact heq _ (hSegB ⟨c, hc, rfl⟩)
    exact tendsto_nhds_unique h1 h2
  -- the extension `φ = κs⁻¹ ∘ e ∘ κY`
  obtain ⟨O₀, hO₀o, hO₀, hφ, hφeq⟩ := e0_exists_extension_of_eqOn hκYmax hκsmax he hBψ heq
  have hpO₀ : p ∈ O₀ := by
    rw [hO₀]
    refine ⟨mem_chart_source E0Y p, hκpe, ?_⟩
    show e (κY p) ∈ κs.target
    rw [hep]; exact κs.map_source (mem_chart_source E0Y q')
  set φ : M → N := κs.symm ∘ e ∘ κY with hφdef
  have hφp : φ p = q' := by
    simp only [hφdef, comp_apply, hep, κs.left_inv (mem_chart_source E0Y q')]
  -- strong causality at `p` inside `O₀`, and a line point `z'` of the segment in it
  obtain ⟨Kc, hKc, hKcO₀, hKcv⟩ := hSCM p O₀ (hO₀o.mem_nhds hpO₀)
  have hev2 : ∀ᶠ c in l, xl c ∈ interior Kc := hxlT.eventually (interior_mem_nhds.2 hKc)
  obtain ⟨c₂, hc₂K, hc₂I⟩ := (hev2.and (Ico_mem_nhdsLT hc₁τ)).exists
  set z' := xl c₂ with hz'def
  have hc₀c₂ : c₀ ≤ c₂ := hc₀c₁.le.trans hc₂I.1
  have hz'U : z' ∈ U := hlineU c₂ hc₀c₂ hc₂I.2
  have hz'B : z' ∈ B := hSegB ⟨c₂, hc₂I, rfl⟩
  have hz'O₀ : z' ∈ O₀ := hKcO₀ (interior_subset hc₂K)
  obtain ⟨Q, hQ, hQle⟩ := hJ c₂ hc₀c₂ hc₂I.2
  -- B1 rigidity on the component of `O₀ ∩ U` through `z'`
  set Ω := connectedComponentIn (O₀ ∩ (U : Set M)) z' with hΩdef
  have hΩo : IsOpen Ω := (hO₀o.inter U.isOpen).connectedComponentIn
  have hΩsub : Ω ⊆ O₀ ∩ U := connectedComponentIn_subset _ _
  have hz'Ω : z' ∈ Ω := mem_connectedComponentIn ⟨hz'O₀, hz'U⟩
  have hEq : EqOn φ ψ Ω := Causal.CBG.eqOn_of_liftPropOn e0_rigid hΩo
    isPreconnected_connectedComponentIn
    (Causal.CBG.liftPropOn_mono_of_le hO₀o hΩo hφ fun w hw => (hΩsub hw).1)
    (Causal.CBG.liftPropOn_mono_of_le U.isOpen hΩo hψ fun w hw => (hΩsub hw).2)
    (hΩo.inter hBo) inter_subset_left ⟨z', hz'Ω, hz'B⟩
    (fun w hw => hφeq ⟨(hΩsub hw.1).1, hw.2⟩)
  -- every point of `U` near `p` is in that component
  set O : Set M := interior Kc ∩ interior Q with hOdef
  have hOo : IsOpen O := isOpen_interior.inter isOpen_interior
  have hpO : p ∈ O := ⟨mem_interior_iff_mem_nhds.2 hKc, mem_interior_iff_mem_nhds.2 hQ⟩
  have hOO₀ : O ⊆ O₀ := fun w hw => hKcO₀ (interior_subset hw.1)
  have hOΩ : ∀ y ∈ O ∩ (U : Set M), y ∈ Ω := by
    rintro y ⟨⟨hyK, hyQ⟩, hyU⟩
    have hz'y : CM.le ⊤ z' y := hQle y (interior_subset hyQ)
    obtain ⟨P, hP, hz'P, hyP, hPb⟩ := Causal.CBG.germ_isPreconnected_between harcM hz'y
    refine hP.subset_connectedComponentIn (F := O₀ ∩ (U : Set M)) hz'P
      (fun w hw => ⟨?_, ?_⟩) hyP
    · exact hKcO₀ (hKcv.2 z' (interior_subset hc₂K) y (interior_subset hyK)
        (Causal.Causality.mem_diamond.2 (hPb w hw)))
    · exact hconv.2 z' hz'U y hyU (Causal.Causality.mem_diamond.2 (hPb w hw))
  -- `ψ → q*` along `U` at `p`, so the cluster point `q` is `q*`
  have hφc : ContinuousAt φ p :=
    (hφ p hpO₀).continuousWithinAt.continuousAt (hO₀o.mem_nhds hpO₀)
  have hTψ : Tendsto ψ (𝓝[(U : Set M)] p) (𝓝 q') := by
    rw [← hφp]
    refine (hφc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [inter_mem_nhdsWithin (U : Set M) (hOo.mem_nhds hpO),
      self_mem_nhdsWithin] with y hy hyU
    exact hEq (hOΩ y ⟨hy.2, hyU⟩)
  have hqq' : q = q' := by
    have h : ClusterPt q (𝓝 q') := (show ClusterPt q (map ψ (𝓝[(U : Set M)] p)) from hcl).mono hTψ
    exact eq_of_nhds_neBot h
  refine ⟨⟨O, hOo⟩, φ, hpO, Causal.CBG.liftPropOn_mono_of_le hO₀o hOo hφ hOO₀,
    by rw [hφp, hqq'], ?_⟩
  rintro y ⟨hyO, hyU⟩
  exact hEq (hOΩ y ⟨hyO, hyU⟩)

/-- **`GermExtPastBTZ` for `𝔼₀`-manifolds, given the BTZ-line field** (A3 past at BTZ boundary
points; A3-B-INVESTIGATION.md §3, past side). `hLine` (the `line` field of `SingularFlatAxioms`,
a parameter of `E0LM.e0LocalModelOf` and of `e0TLocalModel` already) is an **added hypothesis** of
this standalone theorem: through `SingularFlatAxioms` on `M` and `N` it supplies `mem_Zplus`,
`K_densite_sing`, `Iminus_eq_empty`, `pushUp` and the compactness of `J⁺(S) ∩ J⁻(x)`
(`E0LM.sfa_isCompact_Jplus_inter_Jminus`, used for `lem:Sigma_separe`). The argument:
1. a chronal curve `γ` from `p` into `I⁺(p) ∩ J⁻(S)`; `γ(s) ∈ U` for `s > 0`
   (`I⁺(p) ∩ J⁻(S) ⊆ U`, causal convexity), and `ψ(γ s) ≥ q`; the decreasing family `ψ(γ s)`
   converges in the compact diamond `J⁺(q) ∩ J⁻(ψ γ 1)` to some `q*` (unique cluster point);
2. `q*` is a BTZ point (`past_limit_mem_S0`);
3. the regular piece `A` (the component of `I⁺(p) ∩ I⁻(r)` through a lower tip `r₂`) contains the
   chronological diamond `I⁺(p) ∩ I⁻(r₂)`, which is the round-3 diamond clause in the chart, and
   `ψ` clusters at `q*` along it: B2 past side (`E0LM.e0_localUniqueSingAdherent`) gives `e ∈ G`;
4. extension `κ*⁻¹ ∘ e ∘ κ`, B1 rigidity on the component of `O₀ ∩ U` through `γ s₃` (every
   `y ∈ U` near `p` is `≪ γ s₃` and joined to it inside a causally convex neighbourhood), and
   `q = q*`. -/
theorem e0_germExtPastBTZ_of
    (hLine : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
      [SecondCountableTopology M] [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid],
      E0LM.E0GlobalBTZ (Causal.CBG.chartedCausality E0LM.D M)
        (Causal.CBG.chartedSing e0SingY M 0)) : E0GermExtPastBTZ := by
  intro M N _ _ _ _ _ _ _ _ _ _ _ _ U ψ S hψ hinj hGM hGN _hGU hGV hSU hS hSU' hψS hψSV p q hp
    hpS hcl hp0
  haveI : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace E0Y M
  set CM := CE M with hCMdef
  set CN := CE N with hCNdef
  have harcM : CM.CausallyArcConnected := E0LM.e0_causallyArcConnected
  have hextM : CM.CurvesExtend := E0LM.e0_curvesExtend hGM
  have hconv : CM.CausallyConvexIn (U : Set M) ⊤ :=
    Causal.Causality.causallyConvexIn_of_isCauchySurfaceOn hGM.1 harcM hextM le_top hSU hSU' hS
  have hpU : p ∉ U := fun h => hp.2 (by rwa [U.isOpen.interior_eq])
  have hpcl : p ∈ closure (U : Set M) := hp.1
  have hTM : CM.Tarentin := E0LM.e0_tarentin
  have hTN : CN.Tarentin := E0LM.e0_tarentin
  have hSCM : CM.StronglyCausal := hGM.stronglyCausal hTM
  have hclN : ∀ y, IsClosed (CN.Jplus ⊤ {y}) := hGN.isClosed_Jplus_singleton hTN
  have hclN' : ∀ y, IsClosed (CN.Jminus ⊤ {y}) := hGN.isClosed_Jminus_singleton hTN
  have hψc : ContinuousOn ψ U := fun y hy => (hψ y hy).continuousWithinAt
  have hAx : CM.SingularFlatAxioms (Causal.CBG.chartedSing e0SingY M) :=
    E0LM.e0_singularFlatAxioms_of E0.chartIso_mem_e0Groupoid (hLine M)
  have hAxN : CN.SingularFlatAxioms (Causal.CBG.chartedSing e0SingY N) :=
    E0LM.e0_singularFlatAxioms_of E0.chartIso_mem_e0Groupoid (hLine N)
  -- `lem:Sigma_separe`: `J⁻(S)` is a neighbourhood of `p`
  obtain ⟨T, hTc, hT⟩ := E0LM.e0_timeFunction hGM
  have hJ : CM.Jminus ⊤ S ∈ 𝓝 p :=
    Causal.Causality.Jminus_mem_nhds_of_isCauchySurface hGM.1 harcM hextM hS
      (fun x => (hAx.K_densite_sing x).1)
      (fun x => E0LM.sfa_isCompact_Jplus_inter_Jminus hAx hGM hTc hT hS x)
      ⟨hpS, fun h => hpU (hSU h)⟩
  -- a chronal curve from `p` into `I⁺(p) ∩ J⁻(S)`
  obtain ⟨y₁, hy₁I, hy₁J⟩ := hAx.mem_Zplus p _ hJ
  have hpy₁ : CM.lt ⊤ p y₁ := Causal.Precausality.mem_Iplus_singleton.1 hy₁I
  obtain ⟨γ, hγ, hγ0, hγ1⟩ := ((harcM ⊤ le_rfl p y₁).2).1 hpy₁
  have hγc : ContinuousOn γ (Icc 0 1) := Causal.CurveOn.continuousOn CM.isRelFamily_lt hγ
  have hγlt : ∀ s t, 0 ≤ s → s < t → t ≤ 1 → CM.lt ⊤ (γ s) (γ t) := fun s t h1 h2 h3 =>
    hγ.lt_of_lt h1 h2 h3
  have hγle : ∀ s t, 0 ≤ s → s ≤ t → t ≤ 1 → CM.le ⊤ (γ s) (γ t) := fun s t h1 h2 h3 =>
    hγ.causalCurveOn.le_of_le h1 h2 h3
  have hpγ : ∀ s, 0 < s → s ≤ 1 → CM.lt ⊤ p (γ s) := fun s h1 h2 => by
    have := hγlt 0 s le_rfl h1 h2; rwa [hγ0] at this
  have hγJ : ∀ s, 0 ≤ s → s ≤ 1 → γ s ∈ CM.Jminus ⊤ S := fun s h1 h2 => by
    obtain ⟨σ, hσ, hy₁σ⟩ := hy₁J
    refine ⟨σ, hσ, CM.le_trans ?_ hy₁σ⟩
    have := hγle s 1 h1 h2 le_rfl; rwa [hγ1] at this
  have hDU : ∀ x, CM.lt ⊤ p x → x ∈ CM.Jminus ⊤ S → x ∈ U := fun x h1 h2 =>
    Causal.CBG.mem_of_gt_of_mem_closure hconv hSU hpcl h2 h1
  have hγU : ∀ s, 0 < s → s ≤ 1 → γ s ∈ U := fun s h1 h2 =>
    hDU _ (hpγ s h1 h2) (hγJ s h1.le h2)
  set l : Filter ℝ := 𝓝[>] (0 : ℝ) with hldef
  have hev : ∀ᶠ s in l, s ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT zero_lt_one
  have hγT : Tendsto γ l (𝓝 p) := by
    have h := ((hγc 0 ⟨le_rfl, zero_le_one⟩).mono (Ioc_subset_Icc_self)).tendsto
    rw [nhdsWithin_Ioc_eq_nhdsGT zero_lt_one, hγ0] at h
    exact h
  -- `ψ(γ s) ≥ q`, and the family converges
  set g : ℝ → N := ψ ∘ γ with hgdef
  have hqle : ∀ s, 0 < s → s ≤ 1 → CN.le ⊤ q (g s) := by
    intro s h1 h2
    have hF : CN.Jminus ⊤ {g s} ∈ map ψ (𝓝[(U : Set M)] p) := by
      rw [Filter.mem_map]
      refine mem_nhdsWithin_iff_exists_mem_nhds_inter.2 ⟨CM.Iminus ⊤ {γ s},
        CM.isOpen_Iminus.mem_nhds (Causal.Precausality.mem_Iminus_singleton.2 (hpγ s h1 h2)),
        fun u hu => ?_⟩
      rw [mem_preimage, Causal.Precausality.mem_Jminus_singleton]
      exact map_le_top_of_causallyConvex hψ hconv hu.2 (hγU s h1 h2)
        (CM.le_of_lt (Causal.Precausality.mem_Iminus_singleton.1 hu.1))
    have h := ClusterPt.mem_closure_of_mem hcl _ hF
    rw [(hclN' _).closure_eq, Causal.Precausality.mem_Jminus_singleton] at h
    exact h
  set Kd := CN.diamond ⊤ q (g 1) with hKddef
  have hKd : IsCompact Kd := hGN.2 q (g 1)
  have hgK : ∀ᶠ s in l, g s ∈ Kd := hev.mono fun s hs => by
    refine Causal.Causality.mem_diamond.2 ⟨hqle s hs.1 hs.2.le, ?_⟩
    exact map_le_top_of_causallyConvex hψ hconv (hγU s hs.1 hs.2.le) (hγU 1 one_pos le_rfl)
      (hγle s 1 hs.1.le hs.2.le le_rfl)
  have hdown : ∀ y, MapClusterPt y l g → ∀ s, 0 < s → s ≤ 1 → CN.le ⊤ y (g s) := by
    intro y hy s h1 h2
    have hF : CN.Jminus ⊤ {g s} ∈ map g l := by
      rw [Filter.mem_map]
      filter_upwards [Ioo_mem_nhdsGT h1] with t ht
      rw [mem_preimage, Causal.Precausality.mem_Jminus_singleton]
      exact map_le_top_of_causallyConvex hψ hconv (hγU t ht.1 (ht.2.le.trans h2))
        (hγU s h1 h2) (hγle t s ht.1.le ht.2.le h2)
    have h := ClusterPt.mem_closure_of_mem hy _ hF
    rw [(hclN' _).closure_eq, Causal.Precausality.mem_Jminus_singleton] at h
    exact h
  have huniq : ∀ y₁ y₂, MapClusterPt y₁ l g → MapClusterPt y₂ l g → CN.le ⊤ y₂ y₁ := by
    intro y₁ y₂ h₁ h₂
    have hF : CN.Jplus ⊤ {y₂} ∈ map g l := by
      rw [Filter.mem_map]
      filter_upwards [hev] with s hs
      rw [mem_preimage, Causal.Precausality.mem_Jplus_singleton]
      exact hdown y₂ h₂ s hs.1 hs.2.le
    have h := ClusterPt.mem_closure_of_mem h₁ _ hF
    rw [(hclN _).closure_eq, Causal.Precausality.mem_Jplus_singleton] at h
    exact h
  obtain ⟨q', -, hq'cl⟩ := hKd.exists_mapClusterPt (f := l) (u := g) (tendsto_principal.2 hgK)
  have hgT : Tendsto g l (𝓝 q') := hKd.tendsto_nhds_of_unique_mapClusterPt hgK
    fun y _ hy => hGN.1 (huniq q' y hq'cl hy) (huniq y q' hy hq'cl)
  have hq'g : ∀ s, 0 < s → s ≤ 1 → CN.le ⊤ q' (g s) := hdown q' hq'cl
  -- (2) `q*` is a BTZ point
  have hq'S0 : q' ∈ S0 N := by
    haveI : Nonempty M := ⟨p⟩
    have harcN : CN.CausallyArcConnected := E0LM.e0_causallyArcConnected
    have hextN : CN.CurvesExtend := E0LM.e0_curvesExtend hGN
    have hSCN : CN.StronglyCausal := hGN.stronglyCausal hTN
    set V := (Causal.CBG.isEMorphismOn_of_liftPropOn E0.chartIso_mem_e0Groupoid
      E0.absolutelyMinimalOn_YBTZ hψ).imageOpens U le_rfl with hVdef
    have hconvV : CN.CausallyConvexIn (V : Set N) ⊤ :=
      Causal.Causality.causallyConvexIn_of_isCauchySurfaceOn hGN.1 harcN hextN le_top
        (image_mono hSU) hψSV hψS
    set ginv := invFunOn ψ (U : Set M) with hginvdef
    have hginv : ChartedSpace.LiftPropOn e0Groupoid.IsLocalStructomorphWithinAt ginv V :=
      Causal.CBG.liftPropOn_invFunOn U.isOpen hψ hinj
    have hleft : ∀ x ∈ (U : Set M), ginv (ψ x) = x := fun x hx => hinj.leftInvOn_invFunOn hx
    have hright : ∀ v ∈ (V : Set N), ψ (ginv v) = v := fun v hv => invFunOn_eq hv
    have hgV : ∀ s, 0 < s → s ≤ 1 → g s ∈ (V : Set N) := fun s h1 h2 => ⟨γ s, hγU s h1 h2, rfl⟩
    have hglt : ∀ s t, 0 < s → s < t → t ≤ 1 → CN.lt ⊤ (g s) (g t) := fun s t h1 h2 h3 =>
      map_lt_top_of_causallyConvex hψ hconv (hγU s h1 (h2.le.trans h3)) (hγU t (h1.trans h2) h3)
        (hγlt s t h1.le h2 h3)
    have hq'lt : ∀ t, 0 < t → t ≤ 1 → CN.lt ⊤ q' (g t) := fun t h1 h2 =>
      hAxN.pushUp.lt_of_le_of_lt (hq'g (t / 2) (by linarith) (by linarith))
        (hglt (t / 2) t (by linarith) (by linarith) h2)
    have hginvlt : ∀ v w, v ∈ (V : Set N) → w ∈ (V : Set N) → CN.lt ⊤ v w →
        CM.lt ⊤ (ginv v) (ginv w) := fun v w hv hw hvw =>
      map_lt_top_of_causallyConvex (U := V) hginv hconvV hv hw hvw
    set κs := chartAt E0Y q' with hκsdef
    set κY := chartAt E0Y p with hκYdef
    have hκsmax : κs ∈ e0Groupoid.maximalAtlas N := e0Groupoid.chart_mem_maximalAtlas q'
    have hκYmax : κY ∈ e0Groupoid.maximalAtlas M := e0Groupoid.chart_mem_maximalAtlas p
    have hisos : Causal.ChartIso CN E0LM.D κs :=
      Causal.CBG.chartedCausality_chartIso (M := N) E0.chartIso_mem_e0Groupoid
        E0.absolutelyMinimalOn_YBTZ q'
    obtain ⟨K₂, hK₂, hK₂sub, hK₂cv⟩ :=
      hSCN q' κs.source (κs.open_source.mem_nhds (mem_chart_source E0Y q'))
    obtain ⟨K₁, hK₁, hK₁sub, hK₁cv⟩ :=
      hSCM p κY.source (κY.open_source.mem_nhds (mem_chart_source E0Y p))
    have hpK₁ : p ∈ K₁ := mem_of_mem_nhds hK₁
    have hq'K₂ : q' ∈ K₂ := mem_of_mem_nhds hK₂
    obtain ⟨s₄, ⟨hs₄K₁, hs₄K₂⟩, hs₄I⟩ :=
      (((hγT.eventually hK₁).and (hgT.eventually hK₂)).and hev).exists
    obtain ⟨s₅, hs₅K₂, hs₅I⟩ := ((hgT.eventually hK₂).and (Ioo_mem_nhdsGT hs₄I.1)).exists
    have hs₅1 : s₅ ≤ 1 := hs₅I.2.le.trans hs₄I.2.le
    set R := g s₄ with hRdef
    set R₂ := g s₅ with hR₂def
    -- the diamond `D' = I⁺(q*) ∩ I⁻(R)` lies in `ψ(U)`, and `ψ⁻¹` of it near `p`
    set D' := CN.Iplus ⊤ {q'} ∩ CN.Iminus ⊤ {R} with hD'def
    have hD'o : IsOpen D' := CN.isOpen_Iplus.inter CN.isOpen_Iminus
    have hD'rel : ∀ v ∈ D', CN.lt ⊤ q' v ∧ CN.lt ⊤ v R := fun v hv =>
      ⟨Causal.Precausality.mem_Iplus_singleton.1 hv.1,
        Causal.Precausality.mem_Iminus_singleton.1 hv.2⟩
    have hbelow : ∀ v, CN.lt ⊤ q' v → ∃ t ∈ Ioo (0 : ℝ) 1, CN.lt ⊤ (g t) v := by
      intro v hv
      obtain ⟨t, ht, htI⟩ := ((hgT.eventually (CN.isOpen_Iminus.mem_nhds
        (Causal.Precausality.mem_Iminus_singleton.2 hv))).and hev).exists
      exact ⟨t, htI, Causal.Precausality.mem_Iminus_singleton.1 ht⟩
    have hD'V : ∀ v ∈ D', v ∈ (V : Set N) := by
      intro v hv
      obtain ⟨t, htI, htv⟩ := hbelow v (hD'rel v hv).1
      exact hconvV.2 (g t) (hgV t htI.1 htI.2.le) R (hgV s₄ hs₄I.1 hs₄I.2.le)
        (Causal.Causality.mem_diamond.2 ⟨CN.le_of_lt htv, CN.le_of_lt (hD'rel v hv).2⟩)
    have hD'K : ∀ v ∈ D', v ∈ K₂ := fun v hv =>
      hK₂cv.2 q' hq'K₂ R hs₄K₂ (Causal.Causality.mem_diamond.2
        ⟨CN.le_of_lt (hD'rel v hv).1, CN.le_of_lt (hD'rel v hv).2⟩)
    have hpginv : ∀ v ∈ D', CM.le ⊤ p (ginv v) := by
      intro v hv
      obtain ⟨t, htI, htv⟩ := hbelow v (hD'rel v hv).1
      have h := hginvlt (g t) v (hgV t htI.1 htI.2.le) (hD'V v hv) htv
      rw [show ginv (g t) = γ t from hleft _ (hγU t htI.1 htI.2.le)] at h
      exact CM.le_trans (CM.le_of_lt (hpγ t htI.1 htI.2.le)) (CM.le_of_lt h)
    have hR₂D' : R₂ ∈ D' := ⟨Causal.Precausality.mem_Iplus_singleton.2 (hq'lt s₅ hs₅I.1 hs₅1),
      Causal.Precausality.mem_Iminus_singleton.2 (hglt s₅ s₄ hs₅I.1 hs₅I.2 hs₄I.2.le)⟩
    set A'' := connectedComponentIn D' R₂ with hA''def
    have hA''o : IsOpen A'' := by
      haveI : LocallyConnectedSpace N := ChartedSpace.locallyConnectedSpace E0Y N
      exact hD'o.connectedComponentIn
    have hA''c : IsPreconnected A'' := isPreconnected_connectedComponentIn
    have hA''D : A'' ⊆ D' := connectedComponentIn_subset _ _
    have hR₂A : R₂ ∈ A'' := mem_connectedComponentIn hR₂D'
    have hD₂A : ∀ v, CN.lt ⊤ q' v → CN.lt ⊤ v R₂ → v ∈ A'' := by
      intro v h1 h2
      obtain ⟨P, hP, hvP, hR₂P, hPb⟩ :=
        Causal.CBG.germ_isPreconnected_between harcN (CN.le_of_lt h2)
      refine hP.subset_connectedComponentIn (F := D') hR₂P (fun w hw => ⟨?_, ?_⟩) hvP
      · exact Causal.Precausality.mem_Iplus_singleton.2
          (hAxN.pushUp.lt_of_lt_of_le h1 (hPb w hw).1)
      · exact Causal.Precausality.mem_Iminus_singleton.2 (hAxN.pushUp.lt_of_le_of_lt (hPb w hw).2
          (hglt s₅ s₄ hs₅I.1 hs₅I.2 hs₄I.2.le))
    have hA''κs : A'' ⊆ κs.source := fun v hv => hK₂sub (hD'K v (hA''D hv))
    have hA''V : A'' ⊆ (V : Set N) := fun v hv => hD'V v (hA''D hv)
    have hginvA : MapsTo ginv A'' κY.source := by
      intro v hv
      have hvD := hA''D hv
      have h := hginvlt v R (hD'V v hvD) (hgV s₄ hs₄I.1 hs₄I.2.le) (hD'rel v hvD).2
      rw [show ginv R = γ s₄ from hleft _ (hγU s₄ hs₄I.1 hs₄I.2.le)] at h
      exact hK₁sub (hK₁cv.2 p hpK₁ (γ s₄) hs₄K₁
        (Causal.Causality.mem_diamond.2 ⟨hpginv v hvD, CM.le_of_lt h⟩))
    -- `ψ⁻¹ → p` along the diamond at `q*`
    have hTg : Tendsto ginv (𝓝[A''] q') (𝓝 p) := by
      intro W hW
      obtain ⟨KW, hKW, hKWsub, hKWcv⟩ := hSCM p W hW
      obtain ⟨t, htK, htI⟩ := ((hγT.eventually hKW).and hev).exists
      rw [Filter.mem_map]
      filter_upwards [inter_mem_nhdsWithin A'' (CN.isOpen_Iminus.mem_nhds
        (Causal.Precausality.mem_Iminus_singleton.2 (hq'lt t htI.1 htI.2.le))),
        self_mem_nhdsWithin] with v hv hvA
      have hvD := hA''D hvA
      have h := hginvlt v (g t) (hD'V v hvD) (hgV t htI.1 htI.2.le)
        (Causal.Precausality.mem_Iminus_singleton.1 hv.2)
      rw [show ginv (g t) = γ t from hleft _ (hγU t htI.1 htI.2.le)] at h
      exact hKWsub (hKWcv.2 p (mem_of_mem_nhds hKW) (γ t) htK
        (Causal.Causality.mem_diamond.2 ⟨hpginv v hvD, CM.le_of_lt h⟩))
    -- the chart side, and type agreement (convergence form) at the corresponding point `κs q*`
    by_contra hns
    have hy₀ : κs q' ∉ e0SingY 0 := hns
    have hG := StructureGroupoid.isLocalStructomorphWithinAt_localInvariantProp e0Groupoid
    set U'' := κs '' A'' with hU''def
    have hU''o : IsOpen U'' := κs.isOpen_image_of_subset_source hA''o hA''κs
    have hU''c : IsConnected U'' :=
      ⟨⟨κs R₂, R₂, hR₂A, rfl⟩, hA''c.image _ (κs.continuousOn.mono hA''κs)⟩
    have hq'S' : q' ∈ Causal.chartSource κs := mem_chart_source E0Y q'
    have hR₂S : R₂ ∈ Causal.chartSource κs := hA''κs hR₂A
    have hclause : ∃ O : Opens E0Y, κs q' ∈ O ∧ ∃ r ∈ O,
        (E0LM.D.lt O r (κs q') ∧ E0LM.D.Iplus O {r} ∩ E0LM.D.Iminus O {κs q'} ⊆ U'') ∨
        (E0LM.D.lt O (κs q') r ∧ E0LM.D.Iplus O {κs q'} ∩ E0LM.D.Iminus O {r} ⊆ U'') := by
      refine ⟨Causal.chartImage κs (Causal.chartSource κs),
        Causal.mem_chartImage_of_mem hq'S' hq'S', κs R₂,
        Causal.mem_chartImage_of_mem hR₂S hR₂S, Or.inr ⟨?_, ?_⟩⟩
      · exact ((hisos _ le_rfl q' hq'S' R₂ hR₂S).2).1
          (lt_of_causallyConvex_subset harcN hK₂sub hK₂cv hq'K₂ (hD'K R₂ hR₂D')
            (hq'lt s₅ hs₅I.1 hs₅1))
      · rintro y ⟨hy1, hy2⟩
        have hy1' := Causal.Precausality.mem_Iplus_singleton.1 hy1
        have hy2' := Causal.Precausality.mem_Iminus_singleton.1 hy2
        obtain ⟨v, hvs, hvW, rfl, -⟩ := Causal.exists_of_mem_chartImage
          (E0LM.D.lt_mem_right hy1')
        have h1 : CN.lt ⊤ q' v :=
          CN.lt_mono le_top (((hisos _ le_rfl q' hq'S' v hvW).2).2 hy1')
        have h2 : CN.lt ⊤ v R₂ :=
          CN.lt_mono le_top (((hisos _ le_rfl v hvW R₂ hR₂S).2).2 hy2')
        exact ⟨v, hD₂A v h1 h2, rfl⟩
    set f : E0Y → E0Y := κY ∘ ginv ∘ κs.symm with hfdef
    have hfA : ∀ v ∈ A'', f (κs v) = κY (ginv v) := fun v hv => by
      simp only [f, comp_apply, κs.left_inv (hA''κs hv)]
    have hginvA'' : ChartedSpace.LiftPropOn e0Groupoid.IsLocalStructomorphWithinAt ginv A'' :=
      Causal.CBG.liftPropOn_mono_of_le V.isOpen hA''o hginv hA''V
    have hloc : ∀ y ∈ U'', e0Groupoid.IsLocalStructomorphWithinAt f U'' y := by
      rintro _ ⟨z, hz, rfl⟩
      have hP := hG.liftPropOn_indep_chart hκsmax hκYmax hginvA''
        (y := κs z) ⟨κs.map_source (hA''κs hz), by
          simp only [mem_preimage, κs.left_inv (hA''κs hz)]; exact ⟨hz, hginvA hz⟩⟩
      intro hy
      obtain ⟨e, he, hef, hex⟩ := hP (by simp only [mem_preimage, κs.left_inv (hA''κs hz)]; exact hz)
      refine ⟨e, he, fun y hy => hef ⟨?_, hy.2⟩, hex⟩
      obtain ⟨w, hw, rfl⟩ := hy.1
      simp only [mem_preimage, κs.left_inv (hA''κs hw)]; exact hw
    have hinjf : InjOn f U'' := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
      rw [hfA a ha, hfA b hb] at hab
      have h := κY.injOn (hginvA ha) (hginvA hb) hab
      rw [← hright a (hA''V ha), ← hright b (hA''V hb), h]
    have hTf : Tendsto f (𝓝[U''] (κs q')) (𝓝 (κY p)) := by
      have h1 : Tendsto κs.symm (𝓝[U''] (κs q')) (𝓝[A''] q') := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
        · have := (κs.continuousAt_symm (κs.map_source hq'S')).tendsto
          rw [κs.left_inv hq'S'] at this
          exact this.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with y hy
          obtain ⟨v, hv, rfl⟩ := hy
          rw [κs.left_inv (hA''κs hv)]; exact hv
      exact (κY.continuousAt (mem_chart_source E0Y p)).tendsto.comp (hTg.comp h1)
    obtain ⟨hty, -⟩ := E0LM.e0_typeAgreementTendsto U'' hU''o hU''c (κs q') hy₀ hclause (κY p) f
      hloc hinjf hTf
    exact hy₀ ((hty 0 le_rfl).2 hp0)
  -- the charts at `p` and `q*`, and causally convex neighbourhoods inside them
  set κY := chartAt E0Y p with hκYdef
  set κs := chartAt E0Y q' with hκsdef
  have hκYmax : κY ∈ e0Groupoid.maximalAtlas M := e0Groupoid.chart_mem_maximalAtlas p
  have hκsmax : κs ∈ e0Groupoid.maximalAtlas N := e0Groupoid.chart_mem_maximalAtlas q'
  have hisoY : Causal.ChartIso CM E0LM.D κY :=
    Causal.CBG.chartedCausality_chartIso (M := M) E0.chartIso_mem_e0Groupoid
      E0.absolutelyMinimalOn_YBTZ p
  obtain ⟨K₁, hK₁, hK₁sub, hK₁cv⟩ :=
    hSCM p κY.source (κY.open_source.mem_nhds (mem_chart_source E0Y p))
  have hSCN : CN.StronglyCausal := hGN.stronglyCausal hTN
  obtain ⟨K₂, hK₂, hK₂sub, hK₂cv⟩ :=
    hSCN q' κs.source (κs.open_source.mem_nhds (mem_chart_source E0Y q'))
  have hpK₁ : p ∈ K₁ := mem_of_mem_nhds hK₁
  have hq'K₂ : q' ∈ K₂ := mem_of_mem_nhds hK₂
  have hev1 : ∀ᶠ s in l, γ s ∈ K₁ := hγT.eventually hK₁
  have hev2 : ∀ᶠ s in l, g s ∈ K₂ := hgT.eventually hK₂
  obtain ⟨s₁, ⟨hs₁K, hs₁K₂⟩, hs₁I⟩ := ((hev1.and hev2).and hev).exists
  obtain ⟨s₂, hs₂K, hs₂I⟩ := (hev1.and (Ioo_mem_nhdsGT hs₁I.1)).exists
  have hs₂1 : s₂ ≤ 1 := hs₂I.2.le.trans hs₁I.2.le
  set r := γ s₁ with hrdef
  set r₂ := γ s₂ with hr₂def
  -- chronology between points of `K₁`, read in the chart domain
  have hltW : ∀ x y, x ∈ K₁ → y ∈ K₁ → CM.lt ⊤ x y → CM.lt (Causal.chartSource κY) x y := by
    intro x y hx hy hxy
    obtain ⟨c, hc, hc0, hc1⟩ := ((harcM ⊤ le_rfl x y).2).1 hxy
    have hmem : ∀ t ∈ Icc (0 : ℝ) 1, c t ∈ Causal.chartSource κY := fun t ht => by
      have h1 : CM.le ⊤ (c 0) (c t) := hc.causalCurveOn.le_of_le le_rfl ht.1 ht.2
      have h2 : CM.le ⊤ (c t) (c 1) := hc.causalCurveOn.le_of_le ht.1 ht.2 le_rfl
      rw [hc0] at h1
      rw [hc1] at h2
      exact hK₁sub (hK₁cv.2 x hx y hy (Causal.Causality.mem_diamond.2 ⟨h1, h2⟩))
    exact ((harcM (Causal.chartSource κY) le_top x y).2).2
      ⟨c, Causal.CurveOn.restrict hc le_rfl le_rfl le_top hmem, hc0, hc1⟩
  -- the diamond `D = I⁺(p) ∩ I⁻(r)` and the piece `A`
  set D := CM.Iplus ⊤ {p} ∩ CM.Iminus ⊤ {r} with hDdef
  have hDo : IsOpen D := CM.isOpen_Iplus.inter CM.isOpen_Iminus
  have hDrel : ∀ x ∈ D, CM.lt ⊤ p x ∧ CM.lt ⊤ x r := fun x hx =>
    ⟨Causal.Precausality.mem_Iplus_singleton.1 hx.1, Causal.Precausality.mem_Iminus_singleton.1 hx.2⟩
  have hDU : ∀ x ∈ D, x ∈ U := by
    intro x hx
    obtain ⟨h1, h2⟩ := hDrel x hx
    refine hDU _ h1 ?_
    obtain ⟨σ, hσ, hrσ⟩ := hγJ s₁ hs₁I.1.le hs₁I.2.le
    exact ⟨σ, hσ, CM.le_trans (CM.le_of_lt h2) hrσ⟩
  have hDK : ∀ x ∈ D, x ∈ K₁ := fun x hx =>
    hK₁cv.2 p hpK₁ r hs₁K (Causal.Causality.mem_diamond.2
      ⟨CM.le_of_lt (hDrel x hx).1, CM.le_of_lt (hDrel x hx).2⟩)
  have hDreg : ∀ x ∈ D, x ∉ S0 M := by
    intro x hx hxS
    have h := hAx.Iminus_eq_empty x hxS
    have : p ∈ CM.Iminus ⊤ {x} := Causal.Precausality.mem_Iminus_singleton.2 (hDrel x hx).1
    rw [h] at this; exact this
  have hDψ : ∀ x ∈ D, ψ x ∈ K₂ := by
    intro x hx
    obtain ⟨h1, h2⟩ := hDrel x hx
    have hxr : CN.le ⊤ (ψ x) (g s₁) :=
      CN.le_of_lt (map_lt_top_of_causallyConvex hψ hconv (hDU x hx) (hγU s₁ hs₁I.1 hs₁I.2.le) h2)
    obtain ⟨t, ht, htI⟩ := ((hγT.eventually (CM.isOpen_Iminus.mem_nhds
      (Causal.Precausality.mem_Iminus_singleton.2 h1))).and hev).exists
    have htx : CM.lt ⊤ (γ t) x := Causal.Precausality.mem_Iminus_singleton.1 ht
    have hq'x : CN.le ⊤ q' (ψ x) := CN.le_trans (hq'g t htI.1 htI.2.le)
      (map_le_top_of_causallyConvex hψ hconv (hγU t htI.1 htI.2.le) (hDU x hx) (CM.le_of_lt htx))
    exact hK₂cv.2 q' hq'K₂ (g s₁) hs₁K₂ (Causal.Causality.mem_diamond.2 ⟨hq'x, hxr⟩)
  have hr₂D : r₂ ∈ D := ⟨Causal.Precausality.mem_Iplus_singleton.2 (hpγ s₂ hs₂I.1 hs₂1),
    Causal.Precausality.mem_Iminus_singleton.2 (hγlt s₂ s₁ hs₂I.1.le hs₂I.2 hs₁I.2.le)⟩
  set A := connectedComponentIn D r₂ with hAdef
  have hAo : IsOpen A := hDo.connectedComponentIn
  have hAc : IsPreconnected A := isPreconnected_connectedComponentIn
  have hAD : A ⊆ D := connectedComponentIn_subset _ _
  have hr₂A : r₂ ∈ A := mem_connectedComponentIn hr₂D
  have hD₂A : ∀ x, CM.lt ⊤ p x → CM.lt ⊤ x r₂ → x ∈ A := by
    intro x h1 h2
    obtain ⟨P, hP, hxP, hr₂P, hPb⟩ :=
      Causal.CBG.germ_isPreconnected_between harcM (CM.le_of_lt h2)
    refine hP.subset_connectedComponentIn (F := D) hr₂P (fun w hw => ⟨?_, ?_⟩) hxP
    · exact Causal.Precausality.mem_Iplus_singleton.2 (hAx.pushUp.lt_of_lt_of_le h1 (hPb w hw).1)
    · exact Causal.Precausality.mem_Iminus_singleton.2 (hAx.pushUp.lt_of_le_of_lt (hPb w hw).2
        (hγlt s₂ s₁ hs₂I.1.le hs₂I.2 hs₁I.2.le))
  have hAκ : A ⊆ κY.source := fun x hx => hK₁sub (hDK x (hAD hx))
  have hAU : A ⊆ U := fun x hx => hDU x (hAD hx)
  have hAψ : MapsTo ψ A κs.source := fun x hx => hK₂sub (hDψ x (hAD hx))
  have hγA : ∀ s, 0 < s → s < s₂ → γ s ∈ A := fun s h1 h2 =>
    hD₂A _ (hpγ s h1 (h2.le.trans hs₂1)) (hγlt s s₂ h1.le h2 hs₂1)
  have hevA : ∀ᶠ s in l, γ s ∈ A := by
    filter_upwards [Ioo_mem_nhdsGT hs₂I.1] with s hs
    exact hγA s hs.1 hs.2
  -- B2 past side, read in the charts
  have hG := StructureGroupoid.isLocalStructomorphWithinAt_localInvariantProp e0Groupoid
  set U' := κY '' A with hU'def
  have hU'o : IsOpen U' := κY.isOpen_image_of_subset_source hAo hAκ
  have hU'c : IsConnected U' := ⟨⟨κY r₂, r₂, hr₂A, rfl⟩, hAc.image _ (κY.continuousOn.mono hAκ)⟩
  have hreg_of : ∀ x ∈ A, κY x ∈ regE := by
    intro x hx α hα hxα
    rcases eq_or_ne α 0 with rfl | hne
    · exact hDreg x (hAD hx) ((chartAt_mem_e0SingY_iff (hAκ hx) le_rfl).1 hxα)
    · rw [E0LM.e0SingY_of_ne hne] at hxα; exact hxα
  have hU'reg : U' ⊆ regE := by rintro _ ⟨x, hx, rfl⟩; exact hreg_of x hx
  have hclause : ∃ O : Opens E0Y, κY p ∈ O ∧ ∃ r' ∈ O, r' ∈ regE ∧ E0LM.D.lt O (κY p) r' ∧
      regE ∩ E0LM.D.Iplus O {κY p} ∩ E0LM.D.Iminus O {r'} ⊆ U' := by
    have hpS' : p ∈ Causal.chartSource κY := mem_chart_source E0Y p
    have hr₂S : r₂ ∈ Causal.chartSource κY := hAκ hr₂A
    refine ⟨Causal.chartImage κY (Causal.chartSource κY), Causal.mem_chartImage_of_mem hpS' hpS',
      κY r₂, Causal.mem_chartImage_of_mem hr₂S hr₂S, hreg_of r₂ hr₂A, ?_, ?_⟩
    · exact ((hisoY _ le_rfl p hpS' r₂ hr₂S).2).1
        (hltW p r₂ hpK₁ (hDK r₂ hr₂D) (hpγ s₂ hs₂I.1 hs₂1))
    · rintro y ⟨⟨-, hy1⟩, hy2⟩
      have hy1' := Causal.Precausality.mem_Iplus_singleton.1 hy1
      have hy2' := Causal.Precausality.mem_Iminus_singleton.1 hy2
      obtain ⟨x, hxs, hxW, rfl, -⟩ := Causal.exists_of_mem_chartImage
        (E0LM.D.lt_mem_right hy1')
      have h1 : CM.lt ⊤ p x :=
        CM.lt_mono le_top (((hisoY _ le_rfl p hpS' x hxW).2).2 hy1')
      have h2 : CM.lt ⊤ x r₂ :=
        CM.lt_mono le_top (((hisoY _ le_rfl x hxW r₂ hr₂S).2).2 hy2')
      exact ⟨x, hD₂A x h1 h2, rfl⟩
  have hz₀ : κs q' ∈ e0SingY 0 := hq'S0
  set f : E0Y → E0Y := κs ∘ ψ ∘ κY.symm with hfdef
  have hfA : ∀ z ∈ A, f (κY z) = κs (ψ z) := fun z hz => by
    simp only [f, comp_apply, κY.left_inv (hAκ hz)]
  have hψA : ChartedSpace.LiftPropOn e0Groupoid.IsLocalStructomorphWithinAt ψ A :=
    Causal.CBG.liftPropOn_mono_of_le U.isOpen hAo hψ hAU
  have hloc : ∀ y ∈ U', e0Groupoid.IsLocalStructomorphWithinAt f U' y := by
    rintro _ ⟨z, hz, rfl⟩
    have hP := hG.liftPropOn_indep_chart hκYmax hκsmax hψA
      (y := κY z) ⟨κY.map_source (hAκ hz), by
        simp only [mem_preimage, κY.left_inv (hAκ hz)]; exact ⟨hz, hAψ hz⟩⟩
    intro hy
    obtain ⟨e, he, hef, hex⟩ := hP (by simp only [mem_preimage, κY.left_inv (hAκ hz)]; exact hz)
    refine ⟨e, he, fun y hy => hef ⟨?_, hy.2⟩, hex⟩
    obtain ⟨w, hw, rfl⟩ := hy.1
    simp only [mem_preimage, κY.left_inv (hAκ hw)]; exact hw
  have hinjf : InjOn f U' := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    rw [hfA a ha, hfA b hb] at hab
    rw [hinj (hAU ha) (hAU hb) (κs.injOn (hAψ ha) (hAψ hb) hab)]
  have hκsg : Tendsto (fun s => κs (g s)) l (𝓝 (κs q')) :=
    (κs.continuousAt (mem_chart_source E0Y q')).tendsto.comp hgT
  obtain ⟨xp, hxp⟩ := mem_range_inr_of_mem_e0SingY (show κY p ∈ e0SingY 0 from hp0)
  have hcc : connectedComponent (κY p) = range Sum.inr := by
    rw [← hxp]; exact connectedComponent_inr xp
  have hmaps : MapsTo f U' (connectedComponent (κY p)) := by
    rw [hcc]
    have hψcA : ContinuousOn ψ A := hψc.mono hAU
    have hpre : IsPreconnected (closure ((κs ∘ ψ) '' A)) :=
      (hAc.image _ (κs.continuousOn.comp hψcA hAψ)).closure
    have hmemcl : κs q' ∈ closure ((κs ∘ ψ) '' A) :=
      mem_closure_of_tendsto hκsg (hevA.mono fun s hs => ⟨γ s, hs, rfl⟩)
    have hsub := hpre.subset_isClopen isClopen_range_inr
      ⟨κs q', hmemcl, mem_range_inr_of_mem_e0SingY hz₀⟩
    rintro _ ⟨z, hz, rfl⟩
    rw [hfA z hz]
    exact hsub (subset_closure ⟨z, hz, rfl⟩)
  have hNeBot : l.NeBot := inferInstance
  have hclus : MapClusterPt (κs q') (𝓝[U'] (κY p)) f := by
    refine MapClusterPt.of_comp (φ := fun s => κY (γ s)) (p := l) ?_ ?_
    · refine tendsto_nhdsWithin_iff.2 ⟨((κY.continuousAt (mem_chart_source E0Y p)).tendsto.comp
        hγT), hevA.mono fun s hs => ⟨γ s, hs, rfl⟩⟩
    · refine Filter.Tendsto.mapClusterPt (hκsg.congr' ?_)
      filter_upwards [hevA] with s hs
      exact (hfA _ hs).symm
  obtain ⟨e, he, hsrc, heqU'⟩ := E0LM.e0_localUniqueSingAdherent U' hU'o hU'c hU'reg (κY p) 0
    le_rfl hp0 hclause (κs q') hz₀ f hloc hinjf hmaps hclus
  have heq : ∀ w ∈ A, κs (ψ w) = e (κY w) := fun w hw => by
    rw [← hfA w hw]; exact heqU' ⟨w, hw, rfl⟩
  have hκpe : κY p ∈ e.source := hsrc mem_connectedComponent
  have hep : e (κY p) = κs q' := by
    have h1 : Tendsto (fun s => e (κY (γ s))) l (𝓝 (e (κY p))) :=
      ((e.continuousAt hκpe).comp (κY.continuousAt (mem_chart_source E0Y p))).tendsto.comp hγT
    have h2 : Tendsto (fun s => e (κY (γ s))) l (𝓝 (κs q')) := by
      refine hκsg.congr' ?_
      filter_upwards [hevA] with s hs
      exact heq _ hs
    exact tendsto_nhds_unique h1 h2
  -- the extension `φ = κs⁻¹ ∘ e ∘ κY`
  obtain ⟨O₀, hO₀o, hO₀, hφ, hφeq⟩ := e0_exists_extension_of_eqOn hκYmax hκsmax he hAψ heq
  have hpO₀ : p ∈ O₀ := by
    rw [hO₀]
    refine ⟨mem_chart_source E0Y p, hκpe, ?_⟩
    show e (κY p) ∈ κs.target
    rw [hep]; exact κs.map_source (mem_chart_source E0Y q')
  set φ : M → N := κs.symm ∘ e ∘ κY with hφdef
  have hφp : φ p = q' := by
    simp only [hφdef, comp_apply, hep, κs.left_inv (mem_chart_source E0Y q')]
  -- B1 rigidity on the component of `O₀ ∩ U` through a point `γ s₃` of the piece
  obtain ⟨K₃, hK₃, hK₃O₀, hK₃cv⟩ := hSCM p O₀ (hO₀o.mem_nhds hpO₀)
  obtain ⟨s₃, hs₃K, hs₃I⟩ := ((hγT.eventually hK₃).and (Ioo_mem_nhdsGT hs₂I.1)).exists
  set r₃ := γ s₃ with hr₃def
  have hs₃1 : s₃ ≤ 1 := hs₃I.2.le.trans hs₂1
  have hr₃A : r₃ ∈ A := hγA s₃ hs₃I.1 hs₃I.2
  have hr₃U : r₃ ∈ U := hAU hr₃A
  have hr₃O₀ : r₃ ∈ O₀ := hK₃O₀ hs₃K
  set Ω := connectedComponentIn (O₀ ∩ (U : Set M)) r₃ with hΩdef
  have hΩo : IsOpen Ω := (hO₀o.inter U.isOpen).connectedComponentIn
  have hΩsub : Ω ⊆ O₀ ∩ U := connectedComponentIn_subset _ _
  have hr₃Ω : r₃ ∈ Ω := mem_connectedComponentIn ⟨hr₃O₀, hr₃U⟩
  have hEq : EqOn φ ψ Ω := Causal.CBG.eqOn_of_liftPropOn e0_rigid hΩo
    isPreconnected_connectedComponentIn
    (Causal.CBG.liftPropOn_mono_of_le hO₀o hΩo hφ fun w hw => (hΩsub hw).1)
    (Causal.CBG.liftPropOn_mono_of_le U.isOpen hΩo hψ fun w hw => (hΩsub hw).2)
    (hΩo.inter hAo) inter_subset_left ⟨r₃, hr₃Ω, hr₃A⟩
    (fun w hw => hφeq ⟨(hΩsub hw.1).1, hw.2⟩)
  set O : Set M := interior K₃ ∩ CM.Iminus ⊤ {r₃} with hOdef
  have hOo : IsOpen O := isOpen_interior.inter CM.isOpen_Iminus
  have hpO : p ∈ O := ⟨mem_interior_iff_mem_nhds.2 hK₃,
    Causal.Precausality.mem_Iminus_singleton.2 (hpγ s₃ hs₃I.1 hs₃1)⟩
  have hOO₀ : O ⊆ O₀ := fun w hw => hK₃O₀ (interior_subset hw.1)
  have hOΩ : ∀ y ∈ O ∩ (U : Set M), y ∈ Ω := by
    rintro y ⟨⟨hyK, hyI⟩, hyU⟩
    have hyr : CM.le ⊤ y r₃ := CM.le_of_lt (Causal.Precausality.mem_Iminus_singleton.1 hyI)
    obtain ⟨P, hP, hyP, hr₃P, hPb⟩ := Causal.CBG.germ_isPreconnected_between harcM hyr
    refine hP.subset_connectedComponentIn (F := O₀ ∩ (U : Set M)) hr₃P
      (fun w hw => ⟨?_, ?_⟩) hyP
    · exact hK₃O₀ (hK₃cv.2 y (interior_subset hyK) r₃ hs₃K
        (Causal.Causality.mem_diamond.2 (hPb w hw)))
    · exact hconv.2 y hyU r₃ hr₃U (Causal.Causality.mem_diamond.2 (hPb w hw))
  -- `ψ → q*` along `U` at `p`, so the cluster point `q` is `q*`
  have hφc : ContinuousAt φ p :=
    (hφ p hpO₀).continuousWithinAt.continuousAt (hO₀o.mem_nhds hpO₀)
  have hTψ : Tendsto ψ (𝓝[(U : Set M)] p) (𝓝 q') := by
    rw [← hφp]
    refine (hφc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [inter_mem_nhdsWithin (U : Set M) (hOo.mem_nhds hpO),
      self_mem_nhdsWithin] with y hy hyU
    exact hEq (hOΩ y ⟨hy.2, hyU⟩)
  have hqq' : q = q' := by
    have h : ClusterPt q (𝓝 q') := (show ClusterPt q (map ψ (𝓝[(U : Set M)] p)) from hcl).mono hTψ
    exact eq_of_nhds_neBot h
  refine ⟨⟨O, hOo⟩, φ, hpO, Causal.CBG.liftPropOn_mono_of_le hO₀o hOo hφ hOO₀,
    by rw [hφp, hqq'], ?_⟩
  rintro y ⟨hyO, hyU⟩
  exact hEq (hOΩ y ⟨hyO, hyU⟩)

/-! ### §3c The port: `Causal.CBG.LocalModel` with `typeAgreement` in convergence form

lean-causal's `Causal.CBG.LocalModel` cannot be instantiated for `𝔼₀`: its field `typeAgreement`
(`MapClusterPt` form, `Causal/CBG/Geometry.lean:660`) is refuted (`E0LM.e0_not_typeAgreement`).
Its only consumer, `germ_ext_nonBTZ` (`Causal/CBG/FromModel.lean:1951`), has
`hT : Tendsto ψ (𝓝[A] p) (𝓝 q)` in scope. This section is a **port** of lean-causal `ca2ad78`:
`Causal/CBG/Geometry.lean:432–738` (the structure, `regY`, `Str`, `causality`, `IsMor`, `sing`,
`toPreGeometry`) and the model-dependent declarations of `Causal/CBG/FromModel.lean`
(`restrictStr` … `ofLocalModelOfGermSlice`, l.1019–1205; the B2 step, l.1207–1426; `ModelStep`
and `Assembly`, l.1736–2221, without the two model-free lemmas; the cone-slice A4, l.2384–2603;
`AssemblyNonBTZ`, l.2605–2791; the BTZ residual predicates and `ofLocalModelOfBTZ`,
l.2793–2944). Text verbatim except:

1. `LocalModel` → `TLocalModel`, namespace `Geometry` → `TGeometry`, `Causal.*` names qualified
   (DEC-33: no `open Causal`; `Causal.CBG` is opened in this section only);
2. the field `typeAgreement` takes `Tendsto f (𝓝[U] y₀) (𝓝 z₀)` in place of
   `MapClusterPt z₀ (𝓝[U] y₀) f` (see `TLocalModel.typeAgreement`);
3. `germ_ext_nonBTZ` feeds it `tendsto_chart … hT` (new, the convergence form of
   `mapClusterPt_chart`) in place of `hclus`;
4. the `singY 0 = ∅` corollaries and `ofLocalModelNoBTZ` are omitted.

Model-free lemmas are not copied: they are `Causal.CBG`'s (opened here). The port is to be deleted
when lean-causal restates the field (finding, REPORT.json). -/

section Port

open Set Topology Filter Function TopologicalSpace ChartedSpace StructureGroupoid
open Causal.CBG

universe u

set_option autoImplicit false

/-- **Level B: a local model** (design §2; the thesis's `(G, X, X_A)`, `these.tex:3027–3070`).
The model space `Y` (for gx: `𝕄 ⊕ Σ_α 𝔼_α`; flat: `Minkowski d`), the groupoid `G` of the
`X_A`-morphisms between open subsets of `Y` — near a singular point the restrictions of the model
automorphisms `G_α = Aut(X_α)` (`these.tex:3053`), on the regular part the `(G,X)`-morphisms (the
atlas transitions of `these.tex:3048–3050`) — the causality and singular loci of `Y`; the admissible
spacetimes are `ChartedSpace Y M`, `HasGroupoid M G`, Hausdorff, connected, second
countable (`Dev`; gx review C2). Morphisms are
`LiftPropOn G.IsLocalStructomorphWithinAt` (`TLocalModel.IsMor`), the thesis's `X_A`-morphisms
(`these.tex:3173`). -/
structure TLocalModel where
  /-- The model space. -/
  Y : Type u
  [topY : TopologicalSpace Y]
  /-- The groupoid of `X_A`-morphisms between open subsets of `Y` (the transitions of an
  `X_A`-atlas, `these.tex:3048–3050`). -/
  G : StructureGroupoid Y
  /-- `G` is closed under restriction: open subsets inherit the structure (`restrict`), and
  `IsLocalStructomorphWithinAt` is a local invariant property. §3.3. -/
  [closedUnderRestriction : ClosedUnderRestriction G]
  /-- The causality of the model (`defi:causal_Ealpha`, `defi:causal_E0`). -/
  causalityY : Causal.Causality Y
  /-- The singular loci of the model, `sing_α(Y)` (`these.tex:3149`). -/
  singY : ℝ → Set Y
  /-- `Y` is locally connected (Minkowski space, the `𝔼_α`). The open–closed argument deriving A1
  from B1 needs connected chart neighbourhoods; so does A3 (one element of `G` on a connected
  piece of `U` near `p`). §3.1, §3.4. -/
  [locallyConnected : LocallyConnectedSpace Y]
  /-- **Round 4 (1), gx-agreed 2026-11-02: the model is Hausdorff** (Minkowski space and gx's
  `𝕄 ⊕ Σ_α 𝔼_α` are metric). Used by A3 (`CBG/FromModel`, `germ_ext_reg`, `germ_ext_nonBTZ`):
  the element `e ∈ G` that B2 gives on a connected piece and the chart at `q` both carry `ψ`'s
  germ to a limit at the chart image of `p`, so `e (κ p) = κ' q` is uniqueness of limits in `Y`;
  and the extension of an agreement from the regular part of a piece to the whole piece. -/
  [t2Y : T2Space Y]
  /-- **B1, rigidity of `G`** (analyticity of `(G,X)`, `these.tex:1185–1192`: « deux éléments
  $g_1,g_2$ de $G$ sont égaux si et seulement si les restrictions […] à $\U$ sont égales »):
  elements of `G` agreeing on a non-empty open subset of a connected open set agree on it. Gives
  A1 (`prop:GX_liouville`, `these.tex:1476`) with `locallyConnected`. -/
  rigid : ∀ e ∈ G, ∀ e' ∈ G, ∀ U : Set Y, IsOpen U → IsPreconnected U → U ⊆ e.source →
    U ⊆ e'.source → ∀ O ⊆ U, IsOpen O → O.Nonempty → EqOn e e' O → EqOn e e' U
  /-- **B2 at a singular point: the model family is analytic** (`def:analytique`,
  `these.tex:3335–3340`: « pour tout ouvert connexe $\U$ voisinage d'un point singulier, tout
  $(G,X)$-morphisme $f:\reg(\U)\rightarrow\reg(Y)$ est la restriction d'un automorphisme de
  $Y$ »; for `𝔼≥0`, `prop:isom`, `these.tex:4332`, with the injectivity « nécessaire »,
  `these.tex:4426`). `U` is a connected open set meeting `sing_{α₀}` at `y₀`; `f` is an injective
  local `G`-structomorphism on `reg(U)` **into the same model** — `MapsTo f reg(U)` the connected
  component of `y₀`, the thesis's $\reg(Y)$ with $Y$ the model of `y₀` (in gx's
  `Y = 𝕄 ⊕ Σ_α 𝔼_α`, the component `𝔼_{α₀}`). Conclusion: `f` is the restriction of one element of
  `G` **defined on that whole component** (« un automorphisme de $Y$ », not a germ: A3 extends `ψ`
  from `U ∩ O` to a neighbourhood of `p ∉ U`). The same-model hypothesis is what the thesis's
  definition says; a map from `reg(U)` into a *different* model is excluded there by
  `def:incompatibles` / famille analytique (b) (`these.tex:3328–3332`, `3346–3353`), here by the
  hypothesis (package 11 derives it at a BTZ boundary point from `sing_mem` and the chart at `q`).
  Gives A3 at singular points.

  **Kept in this strong form** (gx review C4). For `E₀` it is B21 `prop:isom_strong` at
  `α = β = 0` (arXiv 2108.12631, `papers/gx/sources/2108.12631/src/BTZ_1.tex:468–475`: « let
  $\phi:\reg(\U)\rightarrow \E^{1,2}_\beta$ be a $\mass{}$-morphism. If $\phi$ is a injective
  then $\alpha=\beta$ and $\phi$ is the restriction of an element of $\isom(\E^{1,2}_\alpha)$ »),
  i.e. the thesis's `prop:isom` with the injectivity it calls necessary. The weaker form (`f`
  defined on all of `U`, B21 `prop:isom`, `BTZ_1.tex:378`) does **not** suffice, by gx's past-side
  example: `U = M ∖ (line below a)` is a CGHD, every `p < a` on the line is a corresponding point,
  and `U ∩ O = reg(O)` contains no singular point; Sbierski's **Lemma 3.9** (1309.7591) walks
  along such points with Lemma 3.8 (A3), which needs the extension from `reg(U)` alone. gx's
  route avoids invariance of domain (absent from mathlib): lift to `E₀,∞`, `g ∘ D = D ∘ φ̃`, `g`
  stabilises `Δ` and normalises `⟨P⟩`, the explicit list, injectivity forcing `ℓ = 1`. -/
  localUnique_sing : ∀ U : Set Y, IsOpen U → IsConnected U → ∀ y₀ ∈ U, ∀ α₀ : ℝ, 0 ≤ α₀ →
    y₀ ∈ singY α₀ → ∀ f : Y → Y,
    (∀ y ∈ U ∩ {y | ∀ α : ℝ, 0 ≤ α → y ∉ singY α},
      G.IsLocalStructomorphWithinAt f (U ∩ {y | ∀ α : ℝ, 0 ≤ α → y ∉ singY α}) y) →
    InjOn f (U ∩ {y | ∀ α : ℝ, 0 ≤ α → y ∉ singY α}) →
    MapsTo f (U ∩ {y | ∀ α : ℝ, 0 ≤ α → y ∉ singY α}) (connectedComponent y₀) →
    ∃ e ∈ G, connectedComponent y₀ ⊆ e.source ∧
      EqOn f e (U ∩ {y | ∀ α : ℝ, 0 ≤ α → y ∉ singY α})
  /-- **B2 at a singular point, past side: a regular piece adherent to `y₀`** (design §6,
  interface round 2 (2), gx 2026-11-01; **largeness clause amended in interface round 3**, gx
  2026-11-02, the **diamond form with a regular tip**). `U` is a connected open set of **regular**
  points (not a neighbourhood of `y₀`); the largeness clause: for some open `O ∋ y₀` and some
  **regular** `r ∈ O` with `y₀ ≪_O r`, `U ⊇ reg ∩ I⁺_O(y₀) ∩ I⁻_O(r)` (the regular part of the
  chronological diamond of `y₀` and `r` in `O`). `f` is an injective local `G`-structomorphism on
  `U` into the component of `y₀` (the same model, as in `localUnique_sing`), converging along `U`
  at `y₀` to a point `z₀` of the same singular locus `sing_{α₀}` (`MapClusterPt z₀ (𝓝[U] y₀) f`,
  Sbierski Def 3.5). Conclusion: `f` is the restriction of one element of `G` defined on the whole
  component of `y₀`. Needed by A3 in the past of `Σ` at a BTZ boundary point, where the connected
  piece `U ∩ I⁻_W(r)` is regular and adherent to `p` but need not be `reg` of a neighbourhood of
  `p` (gx `A3-B-INVESTIGATION.md`: (B) can fail on the past side); that piece contains the diamond
  `I⁺_W(p) ∩ I⁻_W(r)` (`Causal.Causality.CausallyConvexIn.Iplus_inter_Iminus_subset`, `CBG/FromModel`),
  which is exactly this clause read in a chart.

  **gx's justification in `E₀`** (2026-11-02, by hand): `r ∈ I⁺_O(y₀)`, an open set, so there is
  a point `q` of `y₀`'s line with `y₀ < q ≪ r`; `I⁻_O(r) ∋ q` contains a basic piece near `q`
  holding every regular point of small radius, for every angle `θ`, and so does `I⁺_O(y₀)` (by
  `Iplus_of_lt`, `q` lying strictly above `y₀` on the line); so the regular part of the diamond
  contains a full `θ`-loop around `Δ`, whose holonomy is the parabolic `P`; `f` maps it to a loop
  winding the same way, so the lift of `f` normalises `⟨P⟩`, and the normaliser is `Isom(E₀)`.

  **The round-2 clause it replaces was vacuous** (finding, `CBG/FromModel`,
  `Causal.Causality.BTZAxioms.exists_le_inter_Iminus_subset`): `∃ r ∈ O, y₀ ≤_O r ∧
  reg ∩ I⁻_O(r) ⊆ U` holds for every `U` at a BTZ point (`r := y₀`: BTZ points have empty
  chronological past, `Iminus_eq_empty`), so it was the point-contact form, which the cone
  counterexample refutes in `E₀`. Here `r ∈ regY` excludes `r := y₀` and every `r` on the line,
  and `y₀ ≪_O r` makes the diamond non-empty. Rejected (design §6): point contact and "the
  closure of `U` contains a segment of the line" (a boost along `Δ` conjugates `P` to a
  non-integral power). Vacuous for the flat instance (`singY = ∅`). -/
  localUnique_sing_adherent : ∀ U : Set Y, IsOpen U → IsConnected U →
    U ⊆ {y | ∀ α : ℝ, 0 ≤ α → y ∉ singY α} → ∀ y₀ : Y, ∀ α₀ : ℝ, 0 ≤ α₀ → y₀ ∈ singY α₀ →
    (∃ O : Opens Y, y₀ ∈ O ∧ ∃ r ∈ O, r ∈ {y | ∀ α : ℝ, 0 ≤ α → y ∉ singY α} ∧
      causalityY.lt O y₀ r ∧
      {y | ∀ α : ℝ, 0 ≤ α → y ∉ singY α} ∩ causalityY.Iplus O {y₀} ∩ causalityY.Iminus O {r} ⊆ U) →
    ∀ z₀ ∈ singY α₀, ∀ f : Y → Y, (∀ y ∈ U, G.IsLocalStructomorphWithinAt f U y) → InjOn f U →
    MapsTo f U (connectedComponent y₀) → MapClusterPt z₀ (𝓝[U] y₀) f →
    ∃ e ∈ G, connectedComponent y₀ ⊆ e.source ∧ EqOn f e U
  /-- **B2 on a regular component** (Liouville for `(G,X)` analytic, `prop:GX_liouville`,
  `these.tex:1476`; **not** the thesis's `def:analytique`, which only covers neighbourhoods of
  singular points — this branch is this file's own, and its hypotheses are chosen so that it holds
  for gx's model): an injective local `G`-structomorphism on a connected open `U` lying in a
  component of `Y` without singular points, **with values in a component without singular points**
  (`MapsTo`), is the restriction of one element of `G` defined on the whole component of `U`. The
  `MapsTo` hypothesis is necessary: without it, `f := e₀.symm` for an `e₀ ∈ G` given by
  `regularChart` at a regular point of `𝔼_α` would force an element of `G` sending all of `𝕄` into
  `reg(𝔼_α)`, which the developing map rules out. Flat instance (`singY = ∅`): Liouville, the
  affine extension. Gives A3 at regular points, with `regularChart` applied on both sides. -/
  localUnique_reg : ∀ U : Set Y, IsOpen U → IsConnected U →
    (∀ y ∈ U, ∀ z ∈ connectedComponent y, ∀ α : ℝ, 0 ≤ α → z ∉ singY α) →
    ∀ f : Y → Y, (∀ y ∈ U, G.IsLocalStructomorphWithinAt f U y) → InjOn f U →
    MapsTo f U {z | ∀ w ∈ connectedComponent z, ∀ α : ℝ, 0 ≤ α → w ∉ singY α} →
    ∃ e ∈ G, (∀ y ∈ U, connectedComponent y ⊆ e.source) ∧ EqOn f e U
  /-- **B2, regular charts** (`these.tex:3043`: $Y_i\in\{X_\alpha\}\cup\{X\}$; a regular point has
  a chart in `X`): a regular point of `Y` is moved by an element of `G` into a component of `Y`
  without singular points. A3 at a regular boundary point `p` (corresponding to `q`): compose the
  charts of `M` at `p` and of `N` at `q` with the elements this field gives, so that both sides
  land in fully regular components; the transported `ψ` then satisfies the `MapsTo` hypothesis of
  `localUnique_reg`. For a model without singular locus, `e = refl`. -/
  regularChart : ∀ y : Y, (∀ α : ℝ, 0 ≤ α → y ∉ singY α) → ∃ e ∈ G, y ∈ e.source ∧
    ∀ z ∈ connectedComponent (e y), ∀ α : ℝ, 0 ≤ α → z ∉ singY α
  /-- **B3**: the model causality is absolutely minimal on every open set (`cor:massA_causalite`).
  Gives `Geometry.absolutelyMinimalOn`. -/
  absolutelyMinimalOn_Y : ∀ W : Opens Y, causalityY.AbsolutelyMinimalOn W
  /-- **B3**: elements of `G` are isomorphisms of the model causality on their source
  (`Causal.ChartIso`, kb/0018). The chart transports then agree on overlaps. -/
  chartIso_mem : ∀ e ∈ G, Causal.ChartIso causalityY causalityY e
  /-- **B3**: elements of `G` preserve the type of a point (`prop:GX_sing_dec`). Gives
  `Geometry.isMor_sing`, and makes `chartedSing` chart-independent. -/
  sing_mem : ∀ e ∈ G, ∀ y ∈ e.source, ∀ α : ℝ, 0 ≤ α → (y ∈ singY α ↔ e y ∈ singY α)
  /-- **B3, the global causal facts of `𝔼≥0`-manifolds** (gx §4 (i): the **corrected** bundle
  `SingularFlatAxioms`, gx review C1, DEC-64 — the former `Iplus_eq` is false in `E₀`, radial null
  ray; not local, so not derivable from `Y`). Second countability is a hypothesis (C2; gx §4 (vi)
  is now `secondCountable_of_cauchy`). Gives A2. -/
  singularFlatAxioms : ∀ {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [SecondCountableTopology M] [ChartedSpace Y M] [HasGroupoid M G],
    (chartedCausality causalityY M).SingularFlatAxioms (chartedSing singY M)
  /-- **B3**: `CurvesExtend` on **globally hyperbolic** `M` (gx review C3). For gx:
  `curvesExtend_of_timeFunction` (`CurvesExtend.lean:409`) with the Geroch time of
  `SingularGeroch` (its `K_monotone` input: `SingularFlatAxioms.K_monotone`, DEC-64), or
  `GloballyHyperbolic.curvesExtend` (`CurvesExtend.lean:447`) from admissible measures. Flat
  instance, existing proofs: `curvesExtend_of_isCausalFlow` (`Flat/CauchyComplete.lean:2467`,
  from a causal flow, so for every GH flat `M` with one, DEC-49), and on opens
  `curvesExtendOn_of_timeFunction` (`CBG/CausalConvex.lean:273`). Gives A2. -/
  curvesExtend : ∀ {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [SecondCountableTopology M] [ChartedSpace Y M] [HasGroupoid M G],
    (chartedCausality causalityY M).GloballyHyperbolic →
    (chartedCausality causalityY M).CurvesExtend
  /-- **B3, time functions** (design §6, interface round 2 (1), the counterpart of
  `Geometry.timeFunction`, which `Geometry.ofLocalModelOfGermSlice` fills from it): every globally hyperbolic
  admissible `M` carries a continuous `T : M → ℝ` strictly increasing along `≤` (the body of
  `Causal.Causality.HasTimeFunction`, `CBG/Pgcd`, verbatim). Flat instance: the Geroch time of admissible
  measures (`Flat/GerochFlat`; `Flat/CBG` already proves the statement for `flatCausality`); `E₀`:
  `SingularGeroch` (gx). Gives A2 (`timeFunction`). -/
  timeFunction : ∀ {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [SecondCountableTopology M] [ChartedSpace Y M] [HasGroupoid M G],
    (chartedCausality causalityY M).GloballyHyperbolic →
    ∃ T : M → ℝ, Continuous T ∧
      ∀ x y, (chartedCausality causalityY M).le ⊤ x y → x ≠ y → T x < T y
  /-- **B3**: `J⁺(Σ) ∩ J⁻(p)` compact (gx §4 (vii), R1). Gives A2. -/
  isCompact_Jplus_inter_Jminus : ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ConnectedSpace M] [SecondCountableTopology M] [ChartedSpace Y M] [HasGroupoid M G],
    (chartedCausality causalityY M).GloballyHyperbolic → ∀ S : Set M,
    (chartedCausality causalityY M).IsCauchySurface S → ∀ p : M,
      IsCompact ((chartedCausality causalityY M).Jplus ⊤ S ∩
        (chartedCausality causalityY M).Jminus ⊤ {p})
  /-- **B3**, time-reversed (no duality). -/
  isCompact_Jminus_inter_Jplus : ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ConnectedSpace M] [SecondCountableTopology M] [ChartedSpace Y M] [HasGroupoid M G],
    (chartedCausality causalityY M).GloballyHyperbolic → ∀ S : Set M,
    (chartedCausality causalityY M).IsCauchySurface S → ∀ p : M,
      IsCompact ((chartedCausality causalityY M).Jminus ⊤ S ∩
        (chartedCausality causalityY M).Jplus ⊤ {p})
  /-- **B3, second countability from a Cauchy surface** (gx review C2; gx §4 (vi)): a globally
  hyperbolic admissible `M` with a second-countable Cauchy surface is second countable. gx
  discharges it by the splitting `M ≅ S × ℝ` (`IsCausalFlow.exists_isCauchySplitting`,
  `Splitting.lean:298`, or `geroch_sing_split`, `SingularGeroch.lean:277`; flat instance:
  `flat_exists_isCauchySplitting`, `Splitting.lean:1934`). Gives A2 (`secondCountable_of_cauchy`),
  used by package 10 for `M̄`. -/
  secondCountable_of_cauchy : ∀ {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [ChartedSpace Y M] [HasGroupoid M G], (chartedCausality causalityY M).GloballyHyperbolic →
    ∀ S : Set M, (chartedCausality causalityY M).IsCauchySurface S →
    SecondCountableTopology S → SecondCountableTopology M
  /-- **Round 4 (4), gx-agreed 2026-11-02: the regular part of the model is open**, i.e. the
  singular loci `⋃_{α ≥ 0} sing_α(Y)` form a closed set (in gx's `𝕄 ⊕ Σ_α 𝔼_α` each `sing_α` is a
  line of `𝔼_α`; flat: `singY = ∅`). Consumed by `CBG/FromModel`'s `germ_ext_nonBTZ` (massive
  case): the regular part `A ∩ κ⁻¹ reg(Y)` of A3's piece is open, so `ψ` restricts to a morphism
  on it, where B2 at a singular point (`localUnique_sing`) is applied; the agreement is then
  extended to `A` by `dense_regY` and `T2Space Y`. -/
  isOpen_regY : IsOpen {y | ∀ α : ℝ, 0 ≤ α → y ∉ singY α}
  /-- **Round 4, added by the round-4 author, accepted by gx (2026-11-02; every stratum closed with
  empty interior, countably many strata): the regular part of the model is dense.** Needed by A3 at a massive boundary point (`α > 0`,
  `CBG/FromModel`'s `germ_ext_nonBTZ`): B2 at a singular point (`localUnique_sing`) gives one
  `e ∈ G` agreeing with `ψ` (read in charts) on the **regular** part of the connected piece `A`
  only; to get `e (κ p) = κ' q` and agreement on `A` the regular part must accumulate at every
  point of `A`. Neither `isOpen_regY` nor the B3 facts give it: `interior_sing` is per `α`, and an
  open set can be covered by uncountably many loci `sing_α` (a foliation by timelike lines, each
  of its own `α`), each closed with empty interior, with `⋃_α sing_α` closed. True in gx's model
  (the singular loci are lines in 3-manifolds) and for the flat model (`singY = ∅`). -/
  dense_regY : Dense {y | ∀ α : ℝ, 0 ≤ α → y ∉ singY α}
  /-- **Round 4 (3), gx-agreed 2026-11-02 ("type agreement, stated on `Y`"): the type of a
  corresponding point, and its component.** `U` is a connected open set of `Y` containing a
  chronological diamond with tip `y₀` — below `y₀` (`r ≪_O y₀`, `I⁺_O(r) ∩ I⁻_O(y₀) ⊆ U`, the
  future-side piece of A3) or above it (`y₀ ≪_O r`, `I⁺_O(y₀) ∩ I⁻_O(r) ⊆ U`, the past-side piece);
  `y₀` is not a BTZ point; `f` is an injective local `G`-structomorphism on `U` (at its singular
  points too) clustering at `z₀` along `U` at `y₀` (`MapClusterPt z₀ (𝓝[U] y₀) f`, Sbierski
  Def 3.5 read in charts). Conclusion: `y₀` and `z₀` have the same type
  (`cor:model_corresponding`, `ETT.tex:2158`, read on `Y`), and if `y₀` is singular, `z₀` lies in
  the component of `y₀` (in gx's model each type `α > 0` lies in the one component `𝔼_α`). This
  is exactly what `CBG/FromModel` consumes (`germ_ext_nonBTZ`): with `y₀ = κ p`, `z₀ = κ' q`,
  `f = κ' ∘ ψ ∘ κ⁻¹` on the chart image of A3's piece; the type equality decides the case (both
  regular: `localUnique_reg` via `regularChart`; both singular: `localUnique_sing`), the component
  is `localUnique_sing`'s `MapsTo … (connectedComponent y₀)` hypothesis. Only `α ≥ 0` is asked
  (`sing_α` is unconstrained for `α < 0`), and BTZ `y₀` are excluded (those cases are the
  explicit hypotheses of `Geometry.ofLocalModelOfBTZ`). Vacuous for the flat model.
  **Port change (WP-41g):** `f` *converges* to `z₀` along `U` at `y₀`
  (`Tendsto f (𝓝[U] y₀) (𝓝 z₀)`) in place of `MapClusterPt z₀ (𝓝[U] y₀) f`, which is false for
  `𝔼₀` (`E0LM.e0_not_typeAgreement`); the convergence is what `germ_ext_nonBTZ` has in scope. -/
  typeAgreement : ∀ U : Set Y, IsOpen U → IsConnected U → ∀ y₀ : Y, y₀ ∉ singY 0 →
    (∃ O : Opens Y, y₀ ∈ O ∧ ∃ r ∈ O,
      (causalityY.lt O r y₀ ∧ causalityY.Iplus O {r} ∩ causalityY.Iminus O {y₀} ⊆ U) ∨
      (causalityY.lt O y₀ r ∧ causalityY.Iplus O {y₀} ∩ causalityY.Iminus O {r} ⊆ U)) →
    ∀ z₀ : Y, ∀ f : Y → Y, (∀ y ∈ U, G.IsLocalStructomorphWithinAt f U y) → InjOn f U →
    Tendsto f (𝓝[U] y₀) (𝓝 z₀) →
    (∀ α : ℝ, 0 ≤ α → (y₀ ∈ singY α ↔ z₀ ∈ singY α)) ∧
      ((∃ α : ℝ, 0 ≤ α ∧ y₀ ∈ singY α) → z₀ ∈ connectedComponent y₀)
  /-- **B4, future side, in cone-slice form** (round 4 (2), gx-agreed 2026-11-02: replaces the
  level-set B4 `slice_future` of rounds 1–3; statement verbatim `CBG/FromModel`'s round-3
  `ConeSliceFuture`). At every point `y` off the BTZ locus and in every open `O ∋ y`, a set
  `K ⊆ O` of points of the punctured causal past `J⁻_O(y) ∖ {y}`, off the BTZ locus, such that
  **every open `V ⊇ K` contains a Cauchy surface `Γ` of some open `N ∋ y`, `N ⊆ O`** (`Γ ⊆ N`).
  Flat (`Flat/CBGSlice`, `minkowski_coneSlice`): `K` the closed slice ball
  `{t = t(y) − δ, ‖x − x(y)‖ ≤ δ}` on the past cone of `y`, `N` the diamond over a slightly larger
  slice ball, which an open `V ⊇ K` contains by compactness. Gives A4 future at every boundary
  point off the BTZ locus (`CBG/FromModel`, `slice_future_of_cone`). Asked only off the BTZ locus:
  near a BTZ point the punctured past is a segment of the line (`past_local`), so no cone slice
  exists there. -/
  coneSliceFuture : ∀ y : Y, y ∉ singY 0 → ∀ O : Opens Y, y ∈ O → ∃ K : Set Y, K ⊆ O ∧
    (∀ z ∈ K, z ∉ singY 0 ∧ z ≠ y ∧ causalityY.le O z y) ∧
    ∀ V : Set Y, IsOpen V → K ⊆ V → ∃ (N : Opens Y) (Γ : Set Y), y ∈ N ∧ N ≤ O ∧
      Γ ⊆ N ∧ Γ ⊆ V ∧ causalityY.IsCauchySurfaceOn N Γ
  /-- **B4, past side, in cone-slice form** (round 4 (2), gx-agreed: replaces `slice_past`;
  statement verbatim `CBG/FromModel`'s round-3 `ConeSlicePast`): as `coneSliceFuture` with `K` in
  the punctured causal future `J⁺_O(y) ∖ {y}`, **at every point** (every point is in `Z⁺`,
  `mem_Zplus`; at a BTZ `y` of `E₀` the future cone is large, `Iplus_of_lt`). No time reversal
  (gx D-12(e)). Gives A4 past everywhere (`slice_past_of_cone`). -/
  coneSlicePast : ∀ y : Y, ∀ O : Opens Y, y ∈ O → ∃ K : Set Y, K ⊆ O ∧
    (∀ z ∈ K, z ≠ y ∧ causalityY.le O y z) ∧
    ∀ V : Set Y, IsOpen V → K ⊆ V → ∃ (N : Opens Y) (Γ : Set Y), y ∈ N ∧ N ≤ O ∧
      Γ ⊆ N ∧ Γ ⊆ V ∧ causalityY.IsCauchySurfaceOn N Γ

namespace TLocalModel

variable (𝔐 : TLocalModel.{u})

attribute [instance] TLocalModel.topY TLocalModel.closedUnderRestriction TLocalModel.locallyConnected
  TLocalModel.t2Y

/-- The regular part of the model, `reg(Y)`. -/
def regY : Set 𝔐.Y := {y | ∀ α : ℝ, 0 ≤ α → y ∉ 𝔐.singY α}

/-- A point of `Y` that is not regular lies in some `sing_α`, `α ≥ 0`. -/
theorem exists_mem_singY_of_not_mem_regY {y : 𝔐.Y} (h : y ∉ 𝔐.regY) :
    ∃ α : ℝ, 0 ≤ α ∧ y ∈ 𝔐.singY α := by
  by_contra hcon
  exact h fun α hα hy => hcon ⟨α, hα, hy⟩

/-- A Level-B structure on `M`: an atlas modelled on `Y` with transitions in `G`
(`these.tex:3133`, read through `HasGroupoid`). -/
def Str (M : Type u) [TopologicalSpace M] : Type u :=
  Σ' cs : ChartedSpace 𝔐.Y M, @HasGroupoid 𝔐.Y _ M _ cs 𝔐.G

variable {𝔐}

/-- The causality generated by a Level-B structure. -/
noncomputable def causality {M : Type u} [TopologicalSpace M] (s : 𝔐.Str M) : Causal.Causality M :=
  letI := s.1; chartedCausality 𝔐.causalityY M

/-- **Level-B morphisms** (`these.tex:3173`): `LiftPropOn G.IsLocalStructomorphWithinAt`. -/
def IsMor {M N : Type u} [TopologicalSpace M] [TopologicalSpace N] (s : 𝔐.Str M)
    (t : 𝔐.Str N) (W : Opens M) (f : M → N) : Prop :=
  letI := s.1; letI := t.1; ChartedSpace.LiftPropOn 𝔐.G.IsLocalStructomorphWithinAt f W

/-- `sing_α` of a Level-B structure. -/
def sing {M : Type u} [TopologicalSpace M] (s : 𝔐.Str M) (α : ℝ) : Set M :=
  letI := s.1; chartedSing 𝔐.singY M α

variable (𝔐)

/-- The pre-geometry of a local model. `Geometry.ofLocalModelOfBTZ` (package 11, `CBG/FromModel`)
completes it to Level A, the BTZ-point cases of A3/A4 as explicit hypotheses. -/
noncomputable def toPreGeometry : Causal.CBG.PreGeometry.{u} where
  Str := 𝔐.Str
  causality := causality
  IsMor := IsMor

end TLocalModel
/-! ### Level B ⇒ Level A: the structural fields -/

namespace TLocalModel

variable (𝔐 : TLocalModel.{u})

/-- The structure induced on an open subset (mathlib's `Opens` charted space; `HasGroupoid` by
`ClosedUnderRestriction`). -/
noncomputable def restrictStr {M : Type u} [TopologicalSpace M] (s : 𝔐.Str M) (W : Opens M) :
    𝔐.Str W :=
  letI := s.1; haveI := s.2; ⟨inferInstance, inferInstance⟩

/-- The structure transported along a homeomorphism. -/
noncomputable def transportStr {M M' : Type u} [TopologicalSpace M] [TopologicalSpace M']
    (e : M ≃ₜ M') (s : 𝔐.Str M) : 𝔐.Str M' :=
  letI := s.1; haveI := s.2; ⟨Causal.CBG.transportChartedSpace 𝔐.Y e, transport_hasGroupoid e⟩

variable {𝔐}

/-- Level-B morphisms are abstract `𝕄≥0`-morphisms (from B3 `chartIso_mem`,
`absolutelyMinimalOn_Y`). -/
theorem isEMorphismOn_of_isMor {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    {s : 𝔐.Str M} {t : 𝔐.Str N} {W : Opens M} {f : M → N} (h : IsMor s t W f) :
    Causal.IsEMorphismOn (causality s) (causality t) W f := by
  letI := s.1; haveI := s.2; letI := t.1; haveI := t.2
  exact isEMorphismOn_of_liftPropOn 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y h

variable (𝔐)

/-- **A3 future, for a local model** (the statement of `Geometry.germExt_future`). -/
def GermExtFuture : Prop :=
  ∀ {M N : Type u} [TopologicalSpace M] [TopologicalSpace N] [T2Space M]
    [ConnectedSpace M] [SecondCountableTopology M] [T2Space N] [ConnectedSpace N]
    [SecondCountableTopology N] (s : 𝔐.Str M) (t : 𝔐.Str N) (U : Opens M)
    (ψ : M → N) (S : Set M) (h : IsMor s t U ψ), InjOn ψ U →
    (causality s).GloballyHyperbolic → (causality t).GloballyHyperbolic →
    (causality s).GloballyHyperbolicOn U →
    (causality t).GloballyHyperbolicOn ((isEMorphismOn_of_isMor h).imageOpens U le_rfl) →
    S ⊆ U → (causality s).IsCauchySurface S → (causality s).IsCauchySurfaceOn U S →
    (causality t).IsCauchySurface (ψ '' S) →
    (causality t).IsCauchySurfaceOn ((isEMorphismOn_of_isMor h).imageOpens U le_rfl) (ψ '' S) →
    ∀ p : M, ∀ q : N, p ∈ frontier (U : Set M) → p ∈ (causality s).Jplus ⊤ S →
      MapClusterPt q (𝓝[(U : Set M)] p) ψ →
      ∃ (O : Opens M) (φ : M → N), p ∈ O ∧ IsMor s t O φ ∧ φ p = q ∧ EqOn φ ψ (O ⊓ U : Opens M)

/-- **A3 past, for a local model** (the statement of `Geometry.germExt_past`). -/
def GermExtPast : Prop :=
  ∀ {M N : Type u} [TopologicalSpace M] [TopologicalSpace N] [T2Space M]
    [ConnectedSpace M] [SecondCountableTopology M] [T2Space N] [ConnectedSpace N]
    [SecondCountableTopology N] (s : 𝔐.Str M) (t : 𝔐.Str N) (U : Opens M)
    (ψ : M → N) (S : Set M) (h : IsMor s t U ψ), InjOn ψ U →
    (causality s).GloballyHyperbolic → (causality t).GloballyHyperbolic →
    (causality s).GloballyHyperbolicOn U →
    (causality t).GloballyHyperbolicOn ((isEMorphismOn_of_isMor h).imageOpens U le_rfl) →
    S ⊆ U → (causality s).IsCauchySurface S → (causality s).IsCauchySurfaceOn U S →
    (causality t).IsCauchySurface (ψ '' S) →
    (causality t).IsCauchySurfaceOn ((isEMorphismOn_of_isMor h).imageOpens U le_rfl) (ψ '' S) →
    ∀ p : M, ∀ q : N, p ∈ frontier (U : Set M) → p ∈ (causality s).Jminus ⊤ S →
      MapClusterPt q (𝓝[(U : Set M)] p) ψ →
      ∃ (O : Opens M) (φ : M → N), p ∈ O ∧ IsMor s t O φ ∧ φ p = q ∧ EqOn φ ψ (O ⊓ U : Opens M)

/-- **A4 future, for a local model** (the statement of `Geometry.slice_future`). -/
def SliceFuture : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [SecondCountableTopology M] (s : 𝔐.Str M) (U : Opens M) (S : Set M),
    (causality s).GloballyHyperbolic →
    (causality s).GloballyHyperbolicOn U → S ⊆ U → (causality s).IsCauchySurface S →
    (causality s).IsCauchySurfaceOn U S → ∀ p : M, p ∈ frontier (U : Set M) →
    p ∈ (causality s).Jplus ⊤ S →
    (causality s).Jminus ⊤ {p} ∩ frontier (U : Set M) ∩ (causality s).Jplus ⊤ S = {p} →
    ∀ O : Opens M, p ∈ O → ∃ U' : Opens M, U < U' ∧ (U' : Set M) ⊆ U ∪ O ∧
      (causality s).GloballyHyperbolicOn U' ∧ (causality s).IsCauchySurfaceOn U' S

/-- **A4 past, for a local model** (the statement of `Geometry.slice_past`). -/
def SlicePast : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [SecondCountableTopology M] (s : 𝔐.Str M) (U : Opens M) (S : Set M),
    (causality s).GloballyHyperbolic →
    (causality s).GloballyHyperbolicOn U → S ⊆ U → (causality s).IsCauchySurface S →
    (causality s).IsCauchySurfaceOn U S → ∀ p : M, p ∈ frontier (U : Set M) →
    p ∈ (causality s).Jminus ⊤ S →
    (causality s).Jplus ⊤ {p} ∩ frontier (U : Set M) ∩ (causality s).Jminus ⊤ S = {p} →
    ∀ O : Opens M, p ∈ O → ∃ U' : Opens M, U < U' ∧ (U' : Set M) ⊆ U ∪ O ∧
      (causality s).GloballyHyperbolicOn U' ∧ (causality s).IsCauchySurfaceOn U' S

end TLocalModel

namespace TGeometry

/-- **Level B ⇒ Level A, modulo A3/A4** (design §2 `Geometry.ofLocalModel`; the round-4 sorry-free
form with A3/A4 derived is `ofLocalModelOfBTZ`): every field of
`Geometry` except the germ extensions (A3) and the slices (A4) is derived from the local model;
those four are taken as hypotheses, so that an instance proving them (e.g. the flat one,
package 12) gets a sorry-free `Geometry`. -/
noncomputable def ofLocalModelOfGermSlice (𝔐 : TLocalModel.{u}) (hA3f : 𝔐.GermExtFuture)
    (hA3p : 𝔐.GermExtPast) (hA4f : 𝔐.SliceFuture) (hA4p : 𝔐.SlicePast) : Causal.CBG.Geometry.{u} where
  toPreGeometry := 𝔐.toPreGeometry
  isMor_mono {M N} _ _ {s t W W' f} h hle := by
    letI := s.1; letI := t.1
    exact liftPropOn_mono_of_le W.isOpen W'.isOpen h hle
  isMor_of_locally {M N} _ _ {s t W f} h := by
    letI := s.1; letI := t.1
    refine liftPropOn_of_locally W.isOpen fun x hx => ?_
    obtain ⟨V, hVW, hxV, hV⟩ := h x hx
    exact ⟨V, V.isOpen, hVW, hxV, hV⟩
  isMor_id {M} _ s W := by
    letI := s.1
    exact liftPropOn_id W.isOpen
  isMor_comp {M N P} _ _ _ {s t r W V f g} hg hf hmaps := by
    letI := s.1; letI := t.1; letI := r.1
    exact liftPropOn_comp W.isOpen V.isOpen hg hf hmaps
  isMor_congr {M N} _ _ {s t W f g} h hfg := by
    letI := s.1; letI := t.1
    exact liftPropOn_congr_of_eqOn W.isOpen h hfg
  isEMorphismOn_of_isMor h := TLocalModel.isEMorphismOn_of_isMor h
  absolutelyMinimalOn {M} _ s W := by
    letI := s.1; haveI := s.2
    exact chartedCausality_absolutelyMinimalOn 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y W
  isMor_inv {M N} _ _ _ {s t W f} h hinj := by
    letI := s.1; letI := t.1
    exact liftPropOn_invFunOn W.isOpen h hinj
  restrict s W := 𝔐.restrictStr s W
  isMor_corestrict_iff {M N} _ _ s W t V g := by
    letI := s.1; haveI := s.2; letI := t.1
    exact forall₂_congr fun x _ => (liftPropWithinAt_subtypeVal_comp_iff g (V : Set N) x).symm
  transport e s := 𝔐.transportStr e s
  isMor_transport {M M'} _ _ e s := by
    letI := s.1; haveI := s.2
    exact Causal.CBG.liftPropOn_transport e
  glue {Z} _ {ι} M _ s e he hcov htrans := by
    let ι' := {i : ι // Nonempty (M i)}
    let M' : ι' → Type u := fun i => M i.1
    letI : ∀ i : ι', Nonempty (M' i) := fun i => i.2
    letI : ∀ i : ι', ChartedSpace 𝔐.Y (M' i) := fun i => (s i.1).1
    haveI : ∀ i : ι', HasGroupoid (M' i) 𝔐.G := fun i => (s i.1).2
    let e' : ∀ i : ι', M' i → Z := fun i => e i.1
    have he' : ∀ i, IsOpenEmbedding (e' i) := fun i => he i.1
    have hcov' : ∀ z, ∃ i, z ∈ range (e' i) := fun z => by
      obtain ⟨i, x, hx⟩ := hcov z
      exact ⟨⟨i, ⟨x⟩⟩, x, hx⟩
    have htrans' : ∀ i j : ι', LiftPropOn 𝔐.G.IsLocalStructomorphWithinAt
        (glueTransition he' i j) (e' i ⁻¹' range (e' j)) := by
      intro i j
      obtain ⟨φ, hφ, hφe⟩ := htrans i.1 j.1
      refine liftPropOn_congr_of_eqOn ((he j.1).isOpen_range.preimage (he i.1).continuous) hφ ?_
      intro x hx
      show φ x = (glueEmb he' j).symm (e i.1 x)
      rw [← hφe x hx]
      exact (glueEmb_symm_apply he' j (φ x)).symm
    refine ⟨⟨gluedChartedSpace 𝔐.Y he' hcov', gluedChartedSpace_hasGroupoid he' hcov' htrans'⟩,
      fun i => ?_⟩
    by_cases hi : Nonempty (M i)
    · exact liftPropOn_glue he' hcov' htrans' ⟨i, hi⟩
    · intro x
      exact absurd ⟨x⟩ hi
  rigid {M N} _ _ _ s t := by
    letI := s.1; letI := t.1
    intro V hV f g hf hg O hOV hOne hfg
    exact eqOn_of_liftPropOn 𝔐.rigid V.isOpen hV.isPreconnected hf hg O.isOpen hOV hOne hfg
  sing s α := TLocalModel.sing s α
  isMor_sing {M N} _ _ {s t W f} h {x} hx {α} hα := by
    letI := s.1; letI := t.1
    exact mem_chartedSing_iff_of_liftPropOn 𝔐.sing_mem W.isOpen h hx hα
  singularFlatAxioms {M} _ _ _ _ s := by
    letI := s.1; haveI := s.2
    exact 𝔐.singularFlatAxioms
  curvesExtend {M} _ _ _ _ s hGH := by
    letI := s.1; haveI := s.2
    exact 𝔐.curvesExtend hGH
  timeFunction {M} _ _ _ _ s hGH := by
    letI := s.1; haveI := s.2
    exact 𝔐.timeFunction hGH
  isCompact_Jplus_inter_Jminus {M} _ _ _ _ s hGH S hS p := by
    letI := s.1; haveI := s.2
    exact 𝔐.isCompact_Jplus_inter_Jminus hGH S hS p
  isCompact_Jminus_inter_Jplus {M} _ _ _ _ s hGH S hS p := by
    letI := s.1; haveI := s.2
    exact 𝔐.isCompact_Jminus_inter_Jplus hGH S hS p
  secondCountable_of_cauchy {M} _ _ _ s hGH S hS hSc := by
    letI := s.1; haveI := s.2
    exact 𝔐.secondCountable_of_cauchy hGH S hS hSc
  germExt_future := hA3f
  germExt_past := hA3p
  slice_future := hA4f
  slice_past := hA4p

end TGeometry
/-! ### The B2 step of A3, with the connectedness made a hypothesis

What A3 needs from Level B, isolated: on a **connected** piece `A` of `U` adherent to `p`, B2
gives one element of `G`, hence an extension of `ψ` to a neighbourhood of `p`. Supplying the
connected piece (and putting `ψ(A)` into a chart at `q`) is the causal part of Sbierski Lemma 3.8
(Prop 3.7, causal convexity), which is not Level B. -/

namespace TLocalModel

variable {𝔐 : TLocalModel.{u}} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace 𝔐.Y M] [ChartedSpace 𝔐.Y N] [HasGroupoid M 𝔐.G] [HasGroupoid N 𝔐.G]

/-- **The extension from one element of `G`.** If `κ' ∘ ψ = e ∘ κ` on `A`, the map
`κ'.symm ∘ e ∘ κ` is a morphism on the open set where it is defined and agrees with `ψ` on `A`
there. -/
theorem exists_extension_of_eqOn {κ : OpenPartialHomeomorph M 𝔐.Y}
    {κ' : OpenPartialHomeomorph N 𝔐.Y} (hκ : κ ∈ 𝔐.G.maximalAtlas M)
    (hκ' : κ' ∈ 𝔐.G.maximalAtlas N) {e : OpenPartialHomeomorph 𝔐.Y 𝔐.Y} (he : e ∈ 𝔐.G)
    {ψ : M → N} {A : Set M} (hAψ : MapsTo ψ A κ'.source)
    (heq : ∀ z ∈ A, κ' (ψ z) = e (κ z)) :
    ∃ O : Set M, IsOpen O ∧ O = κ.source ∩ κ ⁻¹' (e.source ∩ e ⁻¹' κ'.target) ∧
      LiftPropOn 𝔐.G.IsLocalStructomorphWithinAt (κ'.symm ∘ e ∘ κ) O ∧
      EqOn (κ'.symm ∘ e ∘ κ) ψ (O ∩ A) := by
  have hO : IsOpen (κ.source ∩ κ ⁻¹' (e.source ∩ e ⁻¹' κ'.target)) :=
    κ.isOpen_inter_preimage (e.isOpen_inter_preimage κ'.open_target)
  refine ⟨_, hO, rfl, ?_, ?_⟩
  · refine liftPropOn_of_maximalAtlas_rep hκ hκ' hO (fun z hz => hz.1) ?_ ?_ he
      (fun z hz => hz.2.1) ?_
    · intro z hz; exact κ'.map_target hz.2.2
    · refine κ'.continuousOn_symm.comp (e.continuousOn.comp (κ.continuousOn.mono fun z hz => hz.1) ?_) ?_
      · intro z hz; exact hz.2.1
      · intro z hz; exact hz.2.2
    · intro z hz
      simp only [comp_apply]
      exact κ'.right_inv hz.2.2
  · intro z hz
    simp only [comp_apply]
    rw [← heq z hz.2, κ'.left_inv (hAψ hz.2)]

omit [HasGroupoid M 𝔐.G] [HasGroupoid N 𝔐.G] in
/-- **B2 at a regular point** (`localUnique_reg`, chart-independent form): an injective morphism
`ψ` on a **preconnected** non-empty open `A`, read in charts `κ`, `κ'` of the maximal atlases
landing in fully regular components (as `regularChart` provides), is one element `e` of `G`
there, defined on the components of `κ(A)`. -/
theorem exists_eqOn_of_connected_reg {κ : OpenPartialHomeomorph M 𝔐.Y}
    {κ' : OpenPartialHomeomorph N 𝔐.Y} (hκ : κ ∈ 𝔐.G.maximalAtlas M)
    (hκ' : κ' ∈ 𝔐.G.maximalAtlas N) {ψ : M → N} {A : Set M} (hAo : IsOpen A)
    (hAc : IsPreconnected A) (hAne : A.Nonempty) (hA : A ⊆ κ.source) (hAψ : MapsTo ψ A κ'.source)
    (hψ : LiftPropOn 𝔐.G.IsLocalStructomorphWithinAt ψ A) (hinj : InjOn ψ A)
    (hreg : ∀ z ∈ A, ∀ w ∈ connectedComponent (κ z), w ∈ 𝔐.regY)
    (hreg' : ∀ z ∈ A, ∀ w ∈ connectedComponent (κ' (ψ z)), w ∈ 𝔐.regY) :
    ∃ e ∈ 𝔐.G, (∀ z ∈ A, connectedComponent (κ z) ⊆ e.source) ∧
      ∀ z ∈ A, κ' (ψ z) = e (κ z) := by
  have hG := isLocalStructomorphWithinAt_localInvariantProp 𝔐.G
  set U := κ '' A
  have hUo : IsOpen U := κ.isOpen_image_of_subset_source hAo hA
  have hUc : IsConnected U := ⟨hAne.image _, hAc.image _ (κ.continuousOn.mono hA)⟩
  set f : 𝔐.Y → 𝔐.Y := κ' ∘ ψ ∘ κ.symm
  have hfA : ∀ z ∈ A, f (κ z) = κ' (ψ z) := fun z hz => by
    simp only [f, comp_apply, κ.left_inv (hA hz)]
  have hloc : ∀ y ∈ U, 𝔐.G.IsLocalStructomorphWithinAt f U y := by
    rintro _ ⟨z, hz, rfl⟩
    have hP := hG.liftPropOn_indep_chart hκ hκ' hψ
      (y := κ z) ⟨κ.map_source (hA hz), by
        simp only [mem_preimage, κ.left_inv (hA hz)]; exact ⟨hz, hAψ hz⟩⟩
    intro hy
    obtain ⟨e, he, hef, hex⟩ := hP (by simp only [mem_preimage, κ.left_inv (hA hz)]; exact hz)
    refine ⟨e, he, fun y hy => hef ⟨?_, hy.2⟩, hex⟩
    obtain ⟨w, hw, rfl⟩ := hy.1
    simp only [mem_preimage, κ.left_inv (hA hw)]; exact hw
  have hinjf : InjOn f U := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    rw [hfA a ha, hfA b hb] at hab
    rw [hinj ha hb (κ'.injOn (hAψ ha) (hAψ hb) hab)]
  have hmaps : MapsTo f U {z | ∀ w ∈ connectedComponent z, ∀ α : ℝ, 0 ≤ α → w ∉ 𝔐.singY α} := by
    rintro _ ⟨z, hz, rfl⟩ w hw
    rw [hfA z hz] at hw
    exact hreg' z hz w hw
  obtain ⟨e, he, hsrc, heq⟩ := 𝔐.localUnique_reg U hUo hUc
    (by rintro _ ⟨z, hz, rfl⟩ w hw; exact hreg z hz w hw) f hloc hinjf hmaps
  refine ⟨e, he, fun z hz => hsrc _ ⟨z, hz, rfl⟩, fun z hz => ?_⟩
  rw [← hfA z hz]
  exact heq ⟨z, hz, rfl⟩

omit [HasGroupoid M 𝔐.G] [HasGroupoid N 𝔐.G] in
/-- **B2 at a singular point** (`localUnique_sing`, chart-independent form): an injective
morphism `ψ` on the regular part `Bʳ = B ∩ κ⁻¹ reg(Y)` of a preconnected open `B ⊆ κ.source`
containing a point `b₀` with `κ b₀` singular, read in charts `κ`, `κ'`, with values in the
component of `κ b₀` (the same model), is one element `e` of `G` on `Bʳ`, defined on that whole
component. This is the form gx's past-side example needs (`U ∩ O = reg(O)`); it does **not**
cover a connected regular piece of `U` adherent to `p` that is not the whole of `reg(O)`. -/
theorem exists_eqOn_of_connected_sing {κ : OpenPartialHomeomorph M 𝔐.Y}
    {κ' : OpenPartialHomeomorph N 𝔐.Y} (hκ : κ ∈ 𝔐.G.maximalAtlas M)
    (hκ' : κ' ∈ 𝔐.G.maximalAtlas N) {ψ : M → N} {B : Set M} (hBo : IsOpen B)
    (hBc : IsPreconnected B) (hB : B ⊆ κ.source) {b₀ : M} (hb₀ : b₀ ∈ B) {α₀ : ℝ} (hα₀ : 0 ≤ α₀)
    (hsing : κ b₀ ∈ 𝔐.singY α₀)
    (hAψ : MapsTo ψ (B ∩ κ ⁻¹' 𝔐.regY) κ'.source)
    (hψ : LiftPropOn 𝔐.G.IsLocalStructomorphWithinAt ψ (B ∩ κ ⁻¹' 𝔐.regY))
    (hinj : InjOn ψ (B ∩ κ ⁻¹' 𝔐.regY))
    (hcomp : ∀ z ∈ B ∩ κ ⁻¹' 𝔐.regY, κ' (ψ z) ∈ connectedComponent (κ b₀)) :
    ∃ e ∈ 𝔐.G, connectedComponent (κ b₀) ⊆ e.source ∧
      ∀ z ∈ B ∩ κ ⁻¹' 𝔐.regY, κ' (ψ z) = e (κ z) := by
  have hG := isLocalStructomorphWithinAt_localInvariantProp 𝔐.G
  set A := B ∩ κ ⁻¹' 𝔐.regY
  have hA : A ⊆ κ.source := fun z hz => hB hz.1
  set U := κ '' B
  have hUo : IsOpen U := κ.isOpen_image_of_subset_source hBo hB
  have hUc : IsConnected U := ⟨⟨_, b₀, hb₀, rfl⟩, hBc.image _ (κ.continuousOn.mono hB)⟩
  have hreg : U ∩ 𝔐.regY = κ '' A := by
    ext y
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hy⟩; exact ⟨z, ⟨hz, hy⟩, rfl⟩
    · rintro ⟨z, hz, rfl⟩; exact ⟨⟨z, hz.1, rfl⟩, hz.2⟩
  set f : 𝔐.Y → 𝔐.Y := κ' ∘ ψ ∘ κ.symm
  have hfA : ∀ z ∈ A, f (κ z) = κ' (ψ z) := fun z hz => by
    simp only [f, comp_apply, κ.left_inv (hA hz)]
  have hloc : ∀ y ∈ U ∩ 𝔐.regY, 𝔐.G.IsLocalStructomorphWithinAt f (U ∩ 𝔐.regY) y := by
    rw [hreg]
    rintro _ ⟨z, hz, rfl⟩
    have hP := hG.liftPropOn_indep_chart hκ hκ' hψ
      (y := κ z) ⟨κ.map_source (hA hz), by
        simp only [mem_preimage, κ.left_inv (hA hz)]; exact ⟨hz, hAψ hz⟩⟩
    intro hy
    obtain ⟨e, he, hef, hex⟩ := hP (by simp only [mem_preimage, κ.left_inv (hA hz)]; exact hz)
    refine ⟨e, he, fun y hy => hef ⟨?_, hy.2⟩, hex⟩
    obtain ⟨w, hw, rfl⟩ := hy.1
    simp only [mem_preimage, κ.left_inv (hA hw)]; exact hw
  have hinjf : InjOn f (U ∩ 𝔐.regY) := by
    rw [hreg]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    rw [hfA a ha, hfA b hb] at hab
    rw [hinj ha hb (κ'.injOn (hAψ ha) (hAψ hb) hab)]
  have hmaps : MapsTo f (U ∩ 𝔐.regY) (connectedComponent (κ b₀)) := by
    rw [hreg]
    rintro _ ⟨z, hz, rfl⟩
    rw [hfA z hz]; exact hcomp z hz
  obtain ⟨e, he, hsrc, heq⟩ := 𝔐.localUnique_sing U hUo hUc (κ b₀) ⟨b₀, hb₀, rfl⟩ α₀ hα₀ hsing
    f hloc hinjf hmaps
  refine ⟨e, he, hsrc, fun z hz => ?_⟩
  rw [← hfA z hz]
  have hmem : κ z ∈ U ∩ 𝔐.regY := by rw [hreg]; exact ⟨z, hz, rfl⟩
  exact heq hmem

omit [ChartedSpace 𝔐.Y M] [ChartedSpace 𝔐.Y N] [HasGroupoid M 𝔐.G] [HasGroupoid N 𝔐.G] in
/-- **Sbierski Def 3.5 read in charts**: if `q` is a cluster point of `ψ` along `A` at `p`, then
`κ' q` is a cluster point of `κ' ∘ ψ ∘ κ.symm` along `κ '' A` at `κ p` (the cluster hypothesis
of `localUnique_sing_adherent`, from A3's `MapClusterPt q (𝓝[U] p) ψ`). -/
theorem mapClusterPt_chart {κ : OpenPartialHomeomorph M 𝔐.Y} {κ' : OpenPartialHomeomorph N 𝔐.Y}
    {ψ : M → N} {A : Set M} (hA : A ⊆ κ.source) {p : M} (hp : p ∈ κ.source) {q : N}
    (hq : q ∈ κ'.source) (h : MapClusterPt q (𝓝[A] p) ψ) :
    MapClusterPt (κ' q) (𝓝[κ '' A] (κ p)) (κ' ∘ ψ ∘ κ.symm) := by
  have h1 : 𝓝[κ '' A] (κ p) = map κ (𝓝[A] p) := by
    rw [κ.map_nhdsWithin_eq hp, inter_eq_right.2 hA]
  rw [h1, ← mapClusterPt_comp]
  have h2 : (κ' ∘ ψ ∘ κ.symm) ∘ κ =ᶠ[𝓝[A] p] κ' ∘ ψ :=
    eventually_nhdsWithin_of_forall fun z hz => by simp [κ.left_inv (hA hz)]
  rw [h2.mapClusterPt_iff]
  exact h.continuousAt_comp (κ'.continuousAt hq)

omit [ChartedSpace 𝔐.Y M] [ChartedSpace 𝔐.Y N] [HasGroupoid M 𝔐.G] [HasGroupoid N 𝔐.G] in
/-- **The convergence form of `mapClusterPt_chart`** (new in the port): if `ψ → q` along `A` at
`p`, then `κ' ∘ ψ ∘ κ.symm → κ' q` along `κ '' A` at `κ p`. Feeds the convergence form of
`typeAgreement` in `germ_ext_nonBTZ`. -/
theorem tendsto_chart {κ : OpenPartialHomeomorph M 𝔐.Y} {κ' : OpenPartialHomeomorph N 𝔐.Y}
    {ψ : M → N} {A : Set M} (hA : A ⊆ κ.source) {p : M} (hp : p ∈ κ.source) {q : N}
    (hq : q ∈ κ'.source) (h : Tendsto ψ (𝓝[A] p) (𝓝 q)) :
    Tendsto (κ' ∘ ψ ∘ κ.symm) (𝓝[κ '' A] (κ p)) (𝓝 (κ' q)) := by
  have h1 : 𝓝[κ '' A] (κ p) = map κ (𝓝[A] p) := by
    rw [κ.map_nhdsWithin_eq hp, inter_eq_right.2 hA]
  rw [h1, tendsto_map'_iff]
  have h2 : (κ' ∘ ψ ∘ κ.symm) ∘ κ =ᶠ[𝓝[A] p] κ' ∘ ψ :=
    eventually_nhdsWithin_of_forall fun z hz => by simp [κ.left_inv (hA hz)]
  exact (((κ'.continuousAt hq).tendsto).comp h).congr' h2.symm

omit [HasGroupoid M 𝔐.G] [HasGroupoid N 𝔐.G] in
/-- **B2 at a singular point, past side, in charts** (`localUnique_sing_adherent`, interface
round 2 (2), chart-independent form): an injective morphism `ψ` on a preconnected non-empty open
`A ⊆ κ.source` of points with **regular** chart image, read in charts `κ`, `κ'` of the maximal
atlases, with values in the component of a singular `y₀ ∈ sing_{α₀}`, clustering at `z₀ ∈ sing_{α₀}`
along `κ '' A` at `y₀`, and with `κ '' A` satisfying the field's largeness clause **verbatim**
(`hlarge`), is one element `e` of `G` on `A`, defined on the whole component of `y₀`.

The largeness clause is passed through as a hypothesis: since interface round 3 it is the
**diamond form with a regular tip** (`r ∈ reg`, `y₀ ≪_O r`, `reg ∩ I⁺_O(y₀) ∩ I⁻_O(r) ⊆ κ(A)`),
no longer the vacuous round-2 form (`Causal.Causality.BTZAxioms.exists_le_inter_Iminus_subset`).
What A3-past produces meets it: `diamond_clause_of_piece` (from
`Causal.Causality.CausallyConvexIn.Iplus_inter_Iminus_subset`, `chartedCausality_image_Iplus_inter_Iminus`).
A3 past at a BTZ point does not close through this lemma alone, for the model facts listed in
`TLocalModel.GermExtPastBTZ` (round 4: an explicit hypothesis of `Geometry.ofLocalModelOfBTZ`). -/
theorem exists_eqOn_of_connected_sing_adherent {κ : OpenPartialHomeomorph M 𝔐.Y}
    {κ' : OpenPartialHomeomorph N 𝔐.Y} (hκ : κ ∈ 𝔐.G.maximalAtlas M)
    (hκ' : κ' ∈ 𝔐.G.maximalAtlas N) {ψ : M → N} {A : Set M} (hAo : IsOpen A)
    (hAc : IsPreconnected A) (hAne : A.Nonempty) (hA : A ⊆ κ.source)
    (hAreg : ∀ z ∈ A, κ z ∈ 𝔐.regY) {y₀ : 𝔐.Y} {α₀ : ℝ} (hα₀ : 0 ≤ α₀)
    (hsing : y₀ ∈ 𝔐.singY α₀)
    (hlarge : ∃ O : Opens 𝔐.Y, y₀ ∈ O ∧ ∃ r ∈ O, r ∈ 𝔐.regY ∧ 𝔐.causalityY.lt O y₀ r ∧
      𝔐.regY ∩ 𝔐.causalityY.Iplus O {y₀} ∩ 𝔐.causalityY.Iminus O {r} ⊆ κ '' A)
    {z₀ : 𝔐.Y} (hz₀ : z₀ ∈ 𝔐.singY α₀) (hAψ : MapsTo ψ A κ'.source)
    (hψ : LiftPropOn 𝔐.G.IsLocalStructomorphWithinAt ψ A) (hinj : InjOn ψ A)
    (hcomp : ∀ z ∈ A, κ' (ψ z) ∈ connectedComponent y₀)
    (hclus : MapClusterPt z₀ (𝓝[κ '' A] y₀) (κ' ∘ ψ ∘ κ.symm)) :
    ∃ e ∈ 𝔐.G, connectedComponent y₀ ⊆ e.source ∧ ∀ z ∈ A, κ' (ψ z) = e (κ z) := by
  have hG := isLocalStructomorphWithinAt_localInvariantProp 𝔐.G
  set U := κ '' A
  have hUo : IsOpen U := κ.isOpen_image_of_subset_source hAo hA
  have hUc : IsConnected U := ⟨hAne.image _, hAc.image _ (κ.continuousOn.mono hA)⟩
  have hUreg : U ⊆ {y | ∀ α : ℝ, 0 ≤ α → y ∉ 𝔐.singY α} := by
    rintro _ ⟨z, hz, rfl⟩; exact hAreg z hz
  set f : 𝔐.Y → 𝔐.Y := κ' ∘ ψ ∘ κ.symm
  have hfA : ∀ z ∈ A, f (κ z) = κ' (ψ z) := fun z hz => by
    simp only [f, comp_apply, κ.left_inv (hA hz)]
  have hloc : ∀ y ∈ U, 𝔐.G.IsLocalStructomorphWithinAt f U y := by
    rintro _ ⟨z, hz, rfl⟩
    have hP := hG.liftPropOn_indep_chart hκ hκ' hψ
      (y := κ z) ⟨κ.map_source (hA hz), by
        simp only [mem_preimage, κ.left_inv (hA hz)]; exact ⟨hz, hAψ hz⟩⟩
    intro hy
    obtain ⟨e, he, hef, hex⟩ := hP (by simp only [mem_preimage, κ.left_inv (hA hz)]; exact hz)
    refine ⟨e, he, fun y hy => hef ⟨?_, hy.2⟩, hex⟩
    obtain ⟨w, hw, rfl⟩ := hy.1
    simp only [mem_preimage, κ.left_inv (hA hw)]; exact hw
  have hinjf : InjOn f U := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    rw [hfA a ha, hfA b hb] at hab
    rw [hinj ha hb (κ'.injOn (hAψ ha) (hAψ hb) hab)]
  have hmaps : MapsTo f U (connectedComponent y₀) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [hfA z hz]; exact hcomp z hz
  obtain ⟨e, he, hsrc, heq⟩ := 𝔐.localUnique_sing_adherent U hUo hUc hUreg y₀ α₀ hα₀ hsing
    hlarge z₀ hz₀ f hloc hinjf hmaps hclus
  refine ⟨e, he, hsrc, fun z hz => ?_⟩
  rw [← hfA z hz]
  exact heq ⟨z, hz, rfl⟩

end TLocalModel
section ModelStep


variable {𝔐 : TLocalModel.{u}} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace 𝔐.Y M] [ChartedSpace 𝔐.Y N] [HasGroupoid M 𝔐.G] [HasGroupoid N 𝔐.G]

theorem exists_regularChart_mem_maximalAtlas (x : M) (hx : chartAt 𝔐.Y x x ∈ 𝔐.regY) :
    ∃ κ ∈ 𝔐.G.maximalAtlas M, x ∈ κ.source ∧ ∀ w ∈ connectedComponent (κ x), w ∈ 𝔐.regY := by
  obtain ⟨e, he, hxe, hreg⟩ := 𝔐.regularChart _ hx
  exact ⟨(chartAt 𝔐.Y x).trans e,
    trans_mem_maximalAtlas_of_mem (𝔐.G.chart_mem_maximalAtlas x) he,
    ⟨mem_chart_source _ x, hxe⟩, fun w hw => hreg w hw⟩

theorem germ_ext_reg [T2Space N]
    {C' : Causal.Causality M} {D' : Causal.Causality N} (U : Opens M) {V : Opens N} {ψ : M → N} {g : N → M}
    (hψ : LiftPropOn 𝔐.G.IsLocalStructomorphWithinAt ψ U) (hinj : InjOn ψ U)
    (hcorr : IsCorrPair C' D' U V ψ g) (hcvU : C'.CausallyConvexIn (U : Set M) ⊤)
    (hcvV : D'.CausallyConvexIn (V : Set N) ⊤) (hGN : D'.GloballyHyperbolic) (hTN : D'.Tarentin)
    (hSC : C'.StronglyCausal) (harc : C'.CausallyArcConnected) {p : M} {q : N}
    (hZp : p ∈ C'.Zminus) (hZq : q ∈ D'.Zminus) (hPM : C'.PushUp) (hPN : D'.PushUp)
    (hclM : ∀ x, IsClosed (C'.Jplus ⊤ {x})) (hclN : ∀ y, IsClosed (D'.Jplus ⊤ {y}))
    {T : Set N} (hTV : T ⊆ V) (hsepN : D'.Jplus ⊤ T ∈ 𝓝 q) (hc : Corresponds (U : Set M) ψ p q)
    (hpreg : chartAt 𝔐.Y p p ∈ 𝔐.regY) (hqreg : chartAt 𝔐.Y q q ∈ 𝔐.regY) :
    ∃ (O : Opens M) (φ : M → N), p ∈ O ∧ LiftPropOn 𝔐.G.IsLocalStructomorphWithinAt φ O ∧
      φ p = q ∧ EqOn φ ψ (O ⊓ U : Opens M) := by
  haveI : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace 𝔐.Y M
  obtain ⟨κ, hκ, hpκ, hκreg⟩ := exists_regularChart_mem_maximalAtlas (𝔐 := 𝔐) p hpreg
  obtain ⟨κ', hκ', hqκ', hκ'reg⟩ := exists_regularChart_mem_maximalAtlas (𝔐 := 𝔐) q hqreg
  obtain ⟨a, haU, hap, A, hAo, hAc, hdiam, hAsub⟩ := germ_exists_piece hcorr hcvU hcvV hGN hTN hSC
    harc hZp hZq hPM hPN hclM hclN hTV hsepN hc (κ.open_source.mem_nhds hpκ)
    (κ'.open_source.mem_nhds hqκ')
  have hAU : A ⊆ U := fun z hz => (hAsub hz).1.1.1
  have hAκ : A ⊆ κ.source := fun z hz => (hAsub hz).1.1.2
  have hAψ : MapsTo ψ A κ'.source := fun z hz => (hAsub hz).1.2
  have hpcl : p ∈ closure A := by
    rw [mem_closure_iff_nhds]
    intro t ht
    obtain ⟨y, hyp, hyt, hya⟩ := hZp _ (inter_mem ht
      (C'.isOpen_Iplus.mem_nhds (show p ∈ C'.Iplus ⊤ {a} by simpa using hap)))
    exact ⟨y, hyt, hdiam ⟨hya, hyp⟩⟩
  have hAne : A.Nonempty := by
    obtain ⟨y, -, hy⟩ := mem_closure_iff_nhds.1 hpcl univ univ_mem
    exact ⟨y, hy⟩
  haveI hNe : (𝓝[A] p).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hpcl
  have hT : Tendsto ψ (𝓝[A] p) (𝓝 q) :=
    (germ_tendsto_of_corresponds hcorr hcvU hcvV hGN hTN hZp hZq hPM hPN hclM hclN hTV hsepN
      hc).mono_left (nhdsWithin_mono _ fun z hz => ⟨hAU hz, (hAsub hz).2⟩)
  have hψA : LiftPropOn 𝔐.G.IsLocalStructomorphWithinAt ψ A :=
    liftPropOn_mono_of_le U.isOpen hAo hψ hAU
  have hψc : ContinuousOn ψ A := fun y hy => (hψA y hy).continuousWithinAt
  have hcompκ : ∀ z ∈ A, κ z ∈ connectedComponent (κ p) :=
    mem_connectedComponent_of_mem_closure hAc (κ.continuousOn.mono hAκ)
      (κ.continuousAt hpκ).continuousWithinAt hpcl
  have hqcl : q ∈ closure (ψ '' A) :=
    mem_closure_of_tendsto hT (eventually_mem_nhdsWithin.mono fun z hz => mem_image_of_mem ψ hz)
  have hcompκ' : ∀ z ∈ A, κ' (ψ z) ∈ connectedComponent (κ' q) := fun z hz =>
    mem_connectedComponent_of_mem_closure (hAc.image ψ hψc)
      (κ'.continuousOn.mono (image_subset_iff.2 hAψ)) (κ'.continuousAt hqκ').continuousWithinAt
      hqcl _ (mem_image_of_mem ψ hz)
  have hreg : ∀ z ∈ A, ∀ w ∈ connectedComponent (κ z), w ∈ 𝔐.regY := fun z hz w hw =>
    hκreg w (by rw [connectedComponent_eq (hcompκ z hz)]; exact hw)
  have hreg' : ∀ z ∈ A, ∀ w ∈ connectedComponent (κ' (ψ z)), w ∈ 𝔐.regY := fun z hz w hw =>
    hκ'reg w (by rw [connectedComponent_eq (hcompκ' z hz)]; exact hw)
  obtain ⟨e, he, hsrc, heq⟩ := TLocalModel.exists_eqOn_of_connected_reg hκ hκ' hAo hAc hAne hAκ
    hAψ hψA (hinj.mono hAU) hreg hreg'
  obtain ⟨z₀, hz₀⟩ := hAne
  have hκpe : κ p ∈ e.source := hsrc z₀ hz₀
    (by rw [← connectedComponent_eq (hcompκ z₀ hz₀)]; exact mem_connectedComponent)
  have hep : e (κ p) = κ' q := by
    have h1 : Tendsto (fun z => e (κ z)) (𝓝[A] p) (𝓝 (e (κ p))) :=
      ((e.continuousAt hκpe).comp (κ.continuousAt hpκ)).tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun z => e (κ z)) (𝓝[A] p) (𝓝 (κ' q)) :=
      ((κ'.continuousAt hqκ').tendsto.comp hT).congr'
        (eventually_nhdsWithin_of_forall fun z hz => heq z hz)
    exact tendsto_nhds_unique h1 h2
  obtain ⟨O₀, hO₀o, hO₀, hφ, hφeq⟩ := TLocalModel.exists_extension_of_eqOn hκ hκ' he hAψ heq
  have hpO₀ : p ∈ O₀ := by
    rw [hO₀]
    refine ⟨hpκ, hκpe, ?_⟩
    show e (κ p) ∈ κ'.target
    rw [hep]; exact κ'.map_source hqκ'
  have hφp : (κ'.symm ∘ e ∘ κ) p = q := by
    simp only [comp_apply, hep, κ'.left_inv hqκ']
  obtain ⟨x₃, hx₃O₀, hax₃, hx₃p, O, hOo, hpO, hO⟩ := germ_exists_open_subset_connectedComponentIn
    hSC harc hcvU hZp (mem_closure_of_corresponds hc) haU hap hO₀o hpO₀
  have hx₃A : x₃ ∈ A := hdiam ⟨by simpa using hax₃, by simpa using hx₃p⟩
  set Ω := connectedComponentIn (O₀ ∩ (U : Set M)) x₃ with hΩdef
  have hΩo : IsOpen Ω := (hO₀o.inter U.isOpen).connectedComponentIn
  have hΩsub : Ω ⊆ O₀ ∩ U := connectedComponentIn_subset _ _
  have hx₃Ω : x₃ ∈ Ω := mem_connectedComponentIn ⟨hx₃O₀, hAU hx₃A⟩
  have hEq : EqOn (κ'.symm ∘ e ∘ κ) ψ Ω := eqOn_of_liftPropOn 𝔐.rigid hΩo
    isPreconnected_connectedComponentIn
    (liftPropOn_mono_of_le hO₀o hΩo hφ fun z hz => (hΩsub hz).1)
    (liftPropOn_mono_of_le U.isOpen hΩo hψ fun z hz => (hΩsub hz).2)
    (hΩo.inter hAo) inter_subset_left ⟨x₃, hx₃Ω, hx₃A⟩
    (fun z hz => hφeq ⟨(hΩsub hz.1).1, hz.2⟩)
  refine ⟨⟨O ∩ O₀, hOo.inter hO₀o⟩, κ'.symm ∘ e ∘ κ, ⟨hpO, hpO₀⟩,
    liftPropOn_mono_of_le hO₀o (hOo.inter hO₀o) hφ inter_subset_right, hφp, ?_⟩
  rintro y ⟨⟨hyO, -⟩, hyU⟩
  exact hEq (hO y ⟨hyO, hyU⟩)

/-- **A3's core at a non-BTZ boundary point, generic `Y`** (round 4). As `germ_ext_reg`, with the
regularity of `p`, `q` replaced by: `p` is not BTZ (`hp0`); the piece's diamond read in the
preferred chart at `p` (`hread`: the largeness clause of `TLocalModel.typeAgreement`); and the
singular points accumulating at `p` from below (`hline`: for a massive `p`, its line). The piece
`A` is built in the preferred charts `κ` at `p`, `κ'` at `q` (`germ_exists_piece_lt`), and B2 is
chosen by `TLocalModel.typeAgreement` on `κ(A)`: both regular ⇒ `germ_ext_reg`; both singular ⇒
`localUnique_sing` on the regular part of `A` (through a singular point `b ∈ A` of `p`'s line, and
`κ' q` in the component of `κ p`), extended to all of `A` by `dense_regY` and `T2Space Y`
(`Set.EqOn.of_subset_closure`), then the extension and the B1 rigidity step of `germ_ext_reg`. -/
theorem germ_ext_nonBTZ [T2Space N]
    {C' : Causal.Causality M} {D' : Causal.Causality N} (U : Opens M) {V : Opens N} {ψ : M → N} {g : N → M}
    (hψ : LiftPropOn 𝔐.G.IsLocalStructomorphWithinAt ψ U) (hinj : InjOn ψ U)
    (hcorr : IsCorrPair C' D' U V ψ g) (hcvU : C'.CausallyConvexIn (U : Set M) ⊤)
    (hcvV : D'.CausallyConvexIn (V : Set N) ⊤) (hGN : D'.GloballyHyperbolic) (hTN : D'.Tarentin)
    (hSC : C'.StronglyCausal) (harc : C'.CausallyArcConnected) {p : M} {q : N}
    (hZp : p ∈ C'.Zminus) (hZq : q ∈ D'.Zminus) (hPM : C'.PushUp) (hPN : D'.PushUp)
    (hclM : ∀ x, IsClosed (C'.Jplus ⊤ {x})) (hclN : ∀ y, IsClosed (D'.Jplus ⊤ {y}))
    {T : Set N} (hTV : T ⊆ V) (hsepN : D'.Jplus ⊤ T ∈ 𝓝 q) (hc : Corresponds (U : Set M) ψ p q)
    (hp0 : chartAt 𝔐.Y p p ∉ 𝔐.singY 0)
    (hread : ∀ (a : M) (A : Set M), C'.lt (Causal.chartSource (chartAt 𝔐.Y p)) a p →
      C'.Iplus (Causal.chartSource (chartAt 𝔐.Y p)) {a} ∩ C'.Iminus (Causal.chartSource (chartAt 𝔐.Y p)) {p} ⊆
        A →
      ∃ O : Opens 𝔐.Y, chartAt 𝔐.Y p p ∈ O ∧ ∃ r ∈ O,
        (𝔐.causalityY.lt O r (chartAt 𝔐.Y p p) ∧ 𝔐.causalityY.Iplus O {r} ∩
          𝔐.causalityY.Iminus O {chartAt 𝔐.Y p p} ⊆ chartAt 𝔐.Y p '' A) ∨
        (𝔐.causalityY.lt O (chartAt 𝔐.Y p p) r ∧ 𝔐.causalityY.Iplus O {chartAt 𝔐.Y p p} ∩
          𝔐.causalityY.Iminus O {r} ⊆ chartAt 𝔐.Y p '' A))
    (hline : chartAt 𝔐.Y p p ∉ 𝔐.regY → ∀ W ∈ 𝓝 p, ∃ b ∈ W, C'.lt ⊤ b p ∧
      chartAt 𝔐.Y p b ∉ 𝔐.regY) :
    ∃ (O : Opens M) (φ : M → N), p ∈ O ∧ LiftPropOn 𝔐.G.IsLocalStructomorphWithinAt φ O ∧
      φ p = q ∧ EqOn φ ψ (O ⊓ U : Opens M) := by
  haveI : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace 𝔐.Y M
  set κ := chartAt 𝔐.Y p with hκdef
  set κ' := chartAt 𝔐.Y q with hκ'def
  have hκ : κ ∈ 𝔐.G.maximalAtlas M := 𝔐.G.chart_mem_maximalAtlas p
  have hκ' : κ' ∈ 𝔐.G.maximalAtlas N := 𝔐.G.chart_mem_maximalAtlas q
  have hpκ : p ∈ κ.source := mem_chart_source _ p
  have hqκ' : q ∈ κ'.source := mem_chart_source _ q
  obtain ⟨a, haU, hap, hapW, A, hAo, hAc, hdiam, hAsub⟩ := germ_exists_piece_lt hcorr hcvU hcvV
    hGN hTN hSC harc hZp hZq hPM hPN hclM hclN hTV hsepN hc (κ.open_source.mem_nhds hpκ)
    (κ'.open_source.mem_nhds hqκ')
  have hAU : A ⊆ U := fun z hz => (hAsub hz).1.1.1
  have hAκ : A ⊆ κ.source := fun z hz => (hAsub hz).1.1.2
  have hAψ : MapsTo ψ A κ'.source := fun z hz => (hAsub hz).1.2
  have hpcl : p ∈ closure A := by
    rw [mem_closure_iff_nhds]
    intro t ht
    obtain ⟨y, hyp, hyt, hya⟩ := hZp _ (inter_mem ht
      (C'.isOpen_Iplus.mem_nhds (show p ∈ C'.Iplus ⊤ {a} by simpa using hap)))
    exact ⟨y, hyt, hdiam ⟨hya, hyp⟩⟩
  have hAne : A.Nonempty := by
    obtain ⟨y, -, hy⟩ := mem_closure_iff_nhds.1 hpcl univ univ_mem
    exact ⟨y, hy⟩
  haveI hNe : (𝓝[A] p).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hpcl
  have hT : Tendsto ψ (𝓝[A] p) (𝓝 q) :=
    (germ_tendsto_of_corresponds hcorr hcvU hcvV hGN hTN hZp hZq hPM hPN hclM hclN hTV hsepN
      hc).mono_left (nhdsWithin_mono _ fun z hz => ⟨hAU hz, (hAsub hz).2⟩)
  have hψA : LiftPropOn 𝔐.G.IsLocalStructomorphWithinAt ψ A :=
    liftPropOn_mono_of_le U.isOpen hAo hψ hAU
  have hψc : ContinuousOn ψ A := fun y hy => (hψA y hy).continuousWithinAt
  have hcompκ : ∀ z ∈ A, κ z ∈ connectedComponent (κ p) :=
    mem_connectedComponent_of_mem_closure hAc (κ.continuousOn.mono hAκ)
      (κ.continuousAt hpκ).continuousWithinAt hpcl
  have hqcl : q ∈ closure (ψ '' A) :=
    mem_closure_of_tendsto hT (eventually_mem_nhdsWithin.mono fun z hz => mem_image_of_mem ψ hz)
  have hcompκ' : ∀ z ∈ A, κ' (ψ z) ∈ connectedComponent (κ' q) := fun z hz =>
    mem_connectedComponent_of_mem_closure (hAc.image ψ hψc)
      (κ'.continuousOn.mono (image_subset_iff.2 hAψ)) (κ'.continuousAt hqκ').continuousWithinAt
      hqcl _ (mem_image_of_mem ψ hz)
  -- **type agreement**, read on `Y` (round 4 (3)), for `f = κ' ∘ ψ ∘ κ⁻¹` on `κ(A)`
  have hG := isLocalStructomorphWithinAt_localInvariantProp 𝔐.G
  set B := κ '' A with hBdef
  have hBo : IsOpen B := κ.isOpen_image_of_subset_source hAo hAκ
  have hBc : IsConnected B := ⟨hAne.image _, hAc.image _ (κ.continuousOn.mono hAκ)⟩
  set f : 𝔐.Y → 𝔐.Y := κ' ∘ ψ ∘ κ.symm with hfdef
  have hfA : ∀ z ∈ A, f (κ z) = κ' (ψ z) := fun z hz => by
    simp only [f, comp_apply, κ.left_inv (hAκ hz)]
  have hloc : ∀ y ∈ B, 𝔐.G.IsLocalStructomorphWithinAt f B y := by
    rintro _ ⟨z, hz, rfl⟩
    have hP := hG.liftPropOn_indep_chart hκ hκ' hψA
      (y := κ z) ⟨κ.map_source (hAκ hz), by
        simp only [mem_preimage, κ.left_inv (hAκ hz)]; exact ⟨hz, hAψ hz⟩⟩
    intro hy
    obtain ⟨e, he, hef, hex⟩ := hP (by simp only [mem_preimage, κ.left_inv (hAκ hz)]; exact hz)
    refine ⟨e, he, fun y hy => hef ⟨?_, hy.2⟩, hex⟩
    obtain ⟨w, hw, rfl⟩ := hy.1
    simp only [mem_preimage, κ.left_inv (hAκ hw)]; exact hw
  have hinjf : InjOn f B := by
    rintro _ ⟨a', ha', rfl⟩ _ ⟨b', hb', rfl⟩ hab
    rw [hfA a' ha', hfA b' hb'] at hab
    rw [hinj (hAU ha') (hAU hb') (κ'.injOn (hAψ ha') (hAψ hb') hab)]
  have hclus : MapClusterPt (κ' q) (𝓝[B] (κ p)) f :=
    TLocalModel.mapClusterPt_chart (𝔐 := 𝔐) hAκ hpκ hqκ' hT.mapClusterPt
  have hlocdiam : C'.Iplus (Causal.chartSource κ) {a} ∩ C'.Iminus (Causal.chartSource κ) {p} ⊆ A :=
    fun z hz => hdiam ⟨C'.Iplus_mono_opens le_top hz.1, C'.Iminus_mono_opens le_top hz.2⟩
  obtain ⟨hty, hcc⟩ := 𝔐.typeAgreement B hBo hBc (κ p) hp0 (hread a A (hapW _ subset_rfl) hlocdiam)
    (κ' q) f hloc hinjf (TLocalModel.tendsto_chart (𝔐 := 𝔐) hAκ hpκ hqκ' hT)
  by_cases hpreg : κ p ∈ 𝔐.regY
  · -- both regular: `germ_ext_reg`
    have hqreg : κ' q ∈ 𝔐.regY := fun α hα hq => hpreg α hα ((hty α hα).2 hq)
    exact germ_ext_reg U hψ hinj hcorr hcvU hcvV hGN hTN hSC harc hZp hZq hPM hPN hclM hclN hTV
      hsepN hc hpreg hqreg
  -- both singular: B2 at a singular point on the regular part of `A`
  have hα : ∃ α : ℝ, 0 ≤ α ∧ κ p ∈ 𝔐.singY α := 𝔐.exists_mem_singY_of_not_mem_regY hpreg
  have hqcc : κ' q ∈ connectedComponent (κ p) := hcc hα
  obtain ⟨b, ⟨hbκ, hba⟩, hbp, hbreg⟩ := hline hpreg _ (inter_mem (κ.open_source.mem_nhds hpκ)
    (C'.isOpen_Iplus.mem_nhds (show p ∈ C'.Iplus ⊤ {a} by simpa using hap)))
  have hbA : b ∈ A := hdiam ⟨hba, by simpa using hbp⟩
  obtain ⟨α₁, hα₁, hb1⟩ := 𝔐.exists_mem_singY_of_not_mem_regY hbreg
  have hccb : connectedComponent (κ b) = connectedComponent (κ p) :=
    (connectedComponent_eq (hcompκ b hbA)).symm
  have hccq : connectedComponent (κ' q) = connectedComponent (κ p) :=
    (connectedComponent_eq hqcc).symm
  have hcomp : ∀ z ∈ A ∩ κ ⁻¹' 𝔐.regY, κ' (ψ z) ∈ connectedComponent (κ b) := fun z hz => by
    rw [hccb, ← hccq]; exact hcompκ' z hz.1
  have hAro : IsOpen (A ∩ κ ⁻¹' 𝔐.regY) := by
    have h := hAo.inter (κ.isOpen_inter_preimage 𝔐.isOpen_regY)
    convert h using 1
    ext z
    exact ⟨fun hz => ⟨hz.1, hAκ hz.1, hz.2⟩, fun hz => ⟨hz.1, hz.2.2⟩⟩
  obtain ⟨e, he, hsrc, heqr⟩ := TLocalModel.exists_eqOn_of_connected_sing hκ hκ' hAo hAc hAκ hbA
    hα₁ hb1 (hAψ.mono_left inter_subset_left)
    (liftPropOn_mono_of_le hAo hAro hψA inter_subset_left)
    ((hinj.mono hAU).mono inter_subset_left) hcomp
  have hκpe : κ p ∈ e.source := hsrc (by rw [hccb]; exact mem_connectedComponent)
  have hAe : MapsTo κ A e.source := fun z hz => hsrc (by rw [hccb]; exact hcompκ z hz)
  -- the regular part of `A` is dense in `A` (`dense_regY`), so the agreement extends to `A`
  have hdense : A ⊆ closure (A ∩ κ ⁻¹' 𝔐.regY) := by
    intro z hz
    rw [mem_closure_iff_nhds]
    intro t ht
    have hto : IsOpen (interior t ∩ A) := isOpen_interior.inter hAo
    have hne : (κ '' (interior t ∩ A)).Nonempty :=
      ⟨κ z, z, ⟨mem_interior_iff_mem_nhds.2 ht, hz⟩, rfl⟩
    obtain ⟨_, ⟨w, hw, rfl⟩, hwreg⟩ := 𝔐.dense_regY.inter_open_nonempty _
      (κ.isOpen_image_of_subset_source hto fun x hx => hAκ hx.2) hne
    exact ⟨w, interior_subset hw.1, hw.2, hwreg⟩
  have heq : ∀ z ∈ A, κ' (ψ z) = e (κ z) := by
    have h := Set.EqOn.of_subset_closure (f := fun z => κ' (ψ z)) (g := fun z => e (κ z))
      (s := A ∩ κ ⁻¹' 𝔐.regY) (t := A) (fun z hz => heqr z hz)
      (κ'.continuousOn.comp hψc hAψ) (e.continuousOn.comp (κ.continuousOn.mono hAκ) hAe)
      inter_subset_left hdense
    exact fun z hz => h hz
  -- the extension and the rigidity step, as in `germ_ext_reg`
  have hep : e (κ p) = κ' q := by
    have h1 : Tendsto (fun z => e (κ z)) (𝓝[A] p) (𝓝 (e (κ p))) :=
      ((e.continuousAt hκpe).comp (κ.continuousAt hpκ)).tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun z => e (κ z)) (𝓝[A] p) (𝓝 (κ' q)) :=
      ((κ'.continuousAt hqκ').tendsto.comp hT).congr'
        (eventually_nhdsWithin_of_forall fun z hz => heq z hz)
    exact tendsto_nhds_unique h1 h2
  obtain ⟨O₀, hO₀o, hO₀, hφ, hφeq⟩ := TLocalModel.exists_extension_of_eqOn hκ hκ' he hAψ heq
  have hpO₀ : p ∈ O₀ := by
    rw [hO₀]
    refine ⟨hpκ, hκpe, ?_⟩
    show e (κ p) ∈ κ'.target
    rw [hep]; exact κ'.map_source hqκ'
  have hφp : (κ'.symm ∘ e ∘ κ) p = q := by
    simp only [comp_apply, hep, κ'.left_inv hqκ']
  obtain ⟨x₃, hx₃O₀, hax₃, hx₃p, O, hOo, hpO, hO⟩ := germ_exists_open_subset_connectedComponentIn
    hSC harc hcvU hZp (mem_closure_of_corresponds hc) haU hap hO₀o hpO₀
  have hx₃A : x₃ ∈ A := hdiam ⟨by simpa using hax₃, by simpa using hx₃p⟩
  set Ω := connectedComponentIn (O₀ ∩ (U : Set M)) x₃ with hΩdef
  have hΩo : IsOpen Ω := (hO₀o.inter U.isOpen).connectedComponentIn
  have hΩsub : Ω ⊆ O₀ ∩ U := connectedComponentIn_subset _ _
  have hx₃Ω : x₃ ∈ Ω := mem_connectedComponentIn ⟨hx₃O₀, hAU hx₃A⟩
  have hEq : EqOn (κ'.symm ∘ e ∘ κ) ψ Ω := eqOn_of_liftPropOn 𝔐.rigid hΩo
    isPreconnected_connectedComponentIn
    (liftPropOn_mono_of_le hO₀o hΩo hφ fun z hz => (hΩsub hz).1)
    (liftPropOn_mono_of_le U.isOpen hΩo hψ fun z hz => (hΩsub hz).2)
    (hΩo.inter hAo) inter_subset_left ⟨x₃, hx₃Ω, hx₃A⟩
    (fun z hz => hφeq ⟨(hΩsub hz.1).1, hz.2⟩)
  refine ⟨⟨O ∩ O₀, hOo.inter hO₀o⟩, κ'.symm ∘ e ∘ κ, ⟨hpO, hpO₀⟩,
    liftPropOn_mono_of_le hO₀o (hOo.inter hO₀o) hφ inter_subset_right, hφp, ?_⟩
  rintro y ⟨⟨hyO, -⟩, hyU⟩
  exact hEq (hO y ⟨hyO, hyU⟩)

end ModelStep
section Assembly


variable {𝔐 : TLocalModel.{u}} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace 𝔐.Y M] [ChartedSpace 𝔐.Y N] [HasGroupoid M 𝔐.G] [HasGroupoid N 𝔐.G]

theorem isCorrPair_of_cghd [T2Space M] [T2Space N] [Nonempty M]
    (hCM : (chartedCausality 𝔐.causalityY M).CausallyArcConnected)
    (hCN : (chartedCausality 𝔐.causalityY N).CausallyArcConnected)
    (hextM : (chartedCausality 𝔐.causalityY M).CurvesExtend)
    (hextN : (chartedCausality 𝔐.causalityY N).CurvesExtend)
    (U : Opens M) {ψ : M → N} {S : Set M} (hψ : LiftPropOn 𝔐.G.IsLocalStructomorphWithinAt ψ U)
    (hinj : InjOn ψ U) (hGM : (chartedCausality 𝔐.causalityY M).GloballyHyperbolic)
    (hGN : (chartedCausality 𝔐.causalityY N).GloballyHyperbolic)
    (hGU : (chartedCausality 𝔐.causalityY M).GloballyHyperbolicOn U)
    (hGV : (chartedCausality 𝔐.causalityY N).GloballyHyperbolicOn
      ((isEMorphismOn_of_liftPropOn 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y hψ).imageOpens U
        le_rfl))
    (hSU : S ⊆ U) (hS : (chartedCausality 𝔐.causalityY M).IsCauchySurface S)
    (hSU' : (chartedCausality 𝔐.causalityY M).IsCauchySurfaceOn U S)
    (hψS : (chartedCausality 𝔐.causalityY N).IsCauchySurface (ψ '' S))
    (hψSV : (chartedCausality 𝔐.causalityY N).IsCauchySurfaceOn
      ((isEMorphismOn_of_liftPropOn 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y hψ).imageOpens U
        le_rfl) (ψ '' S)) :
    (chartedCausality 𝔐.causalityY M).CausallyConvexIn (U : Set M) ⊤ ∧
      (chartedCausality 𝔐.causalityY N).CausallyConvexIn
        ((isEMorphismOn_of_liftPropOn 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y hψ).imageOpens U
          le_rfl : Set N) ⊤ ∧
      IsCorrPair (chartedCausality 𝔐.causalityY M) (chartedCausality 𝔐.causalityY N) U
        ((isEMorphismOn_of_liftPropOn 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y hψ).imageOpens U
          le_rfl) ψ (invFunOn ψ U) := by
  set C := chartedCausality 𝔐.causalityY M
  set D := chartedCausality 𝔐.causalityY N
  have hE := isEMorphismOn_of_liftPropOn 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y hψ
  set V := hE.imageOpens U le_rfl with hVdef
  have hE' : Causal.IsEMorphismOn D C V (invFunOn ψ U) :=
    isEMorphismOn_of_liftPropOn 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y (W := V)
      (liftPropOn_invFunOn U.isOpen hψ hinj)
  have hcvU : C.CausallyConvexIn (U : Set M) ⊤ :=
    Causal.IsCauchyInclusion.causallyConvexIn ⟨le_top, hGU, hGM, S, hSU, hSU', hS⟩ hCM
      (Causal.Causality.curvesExtendOn_top.2 hextM)
  have hcvV : D.CausallyConvexIn (V : Set N) ⊤ :=
    Causal.IsCauchyInclusion.causallyConvexIn ⟨le_top, hGV, hGN, ψ '' S, image_mono hSU, hψSV, hψS⟩ hCN
      (Causal.Causality.curvesExtendOn_top.2 hextN)
  have hl := hinj.leftInvOn_invFunOn
  have hmaps : MapsTo ψ U V := fun z hz => ⟨z, hz, rfl⟩
  refine ⟨hcvU, hcvV,
    { mapsTo := hmaps
      mapsTo_inv := fun y hy => invFunOn_mem hy
      leftInvOn := hl
      rightInvOn := fun y hy => invFunOn_eq hy
      continuousOn := hE.continuousOn
      continuousOn_inv := hE'.continuousOn
      le_iff := fun x hx y hy => ⟨fun hxy => ?_, fun hxy => ?_⟩
      lt_iff := fun x hx y hy => ⟨fun hxy => ?_, fun hxy => ?_⟩ }⟩
  · exact D.le_mono le_top (hE.map_le U V le_rfl hmaps
      (Causal.Causality.le_of_causallyConvexIn_of_le hCM hcvU subset_rfl le_top hx hy hxy))
  · have hV' := Causal.Causality.le_of_causallyConvexIn_of_le hCN hcvV subset_rfl le_top (hmaps hx)
      (hmaps hy) hxy
    have := hE'.map_le V ⊤ le_rfl (fun _ _ => trivial) hV'
    rwa [hl hx, hl hy] at this
  · exact D.lt_mono le_top (hE.map_lt U V le_rfl hmaps
      (Causal.Causality.lt_of_causallyConvexIn hCM hcvU hx hy hxy))
  · have hV' := Causal.Causality.lt_of_causallyConvexIn hCN hcvV (hmaps hx) (hmaps hy) hxy
    have := hE'.map_lt V ⊤ le_rfl (fun _ _ => trivial) hV'
    rwa [hl hx, hl hy] at this

variable [T2Space M] [ConnectedSpace M] [SecondCountableTopology M]
  [T2Space N] [ConnectedSpace N] [SecondCountableTopology N]

theorem germ_future_reg (U : Opens M) (ψ : M → N) (S : Set M)
    (hψ : LiftPropOn 𝔐.G.IsLocalStructomorphWithinAt ψ U)
    (hinj : InjOn ψ U) (hGM : (chartedCausality 𝔐.causalityY M).GloballyHyperbolic)
    (hGN : (chartedCausality 𝔐.causalityY N).GloballyHyperbolic)
    (hGU : (chartedCausality 𝔐.causalityY M).GloballyHyperbolicOn U)
    (hGV : (chartedCausality 𝔐.causalityY N).GloballyHyperbolicOn
      ((isEMorphismOn_of_liftPropOn 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y hψ).imageOpens U
        le_rfl))
    (hSU : S ⊆ U) (hS : (chartedCausality 𝔐.causalityY M).IsCauchySurface S)
    (hSU' : (chartedCausality 𝔐.causalityY M).IsCauchySurfaceOn U S)
    (hψS : (chartedCausality 𝔐.causalityY N).IsCauchySurface (ψ '' S))
    (hψSV : (chartedCausality 𝔐.causalityY N).IsCauchySurfaceOn
      ((isEMorphismOn_of_liftPropOn 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y hψ).imageOpens U
        le_rfl) (ψ '' S))
    (p : M) (q : N) (hp : p ∈ frontier (U : Set M))
    (hpS : p ∈ (chartedCausality 𝔐.causalityY M).Jplus ⊤ S)
    (hcl : MapClusterPt q (𝓝[(U : Set M)] p) ψ)
    (hpreg : chartAt 𝔐.Y p p ∈ 𝔐.regY) (hqreg : chartAt 𝔐.Y q q ∈ 𝔐.regY) :
    ∃ (O : Opens M) (φ : M → N), p ∈ O ∧ LiftPropOn 𝔐.G.IsLocalStructomorphWithinAt φ O ∧
      φ p = q ∧ EqOn φ ψ (O ⊓ U : Opens M) := by
  set C := chartedCausality 𝔐.causalityY M
  set D := chartedCausality 𝔐.causalityY N
  have hAxM : C.SingularFlatAxioms (chartedSing 𝔐.singY M) := 𝔐.singularFlatAxioms
  have hAxN : D.SingularFlatAxioms (chartedSing 𝔐.singY N) := 𝔐.singularFlatAxioms
  have hextM : C.CurvesExtend := 𝔐.curvesExtend hGM
  have hextN : D.CurvesExtend := 𝔐.curvesExtend hGN
  haveI : Nonempty M := ⟨p⟩
  obtain ⟨hcvU, hcvV, hcorr⟩ := isCorrPair_of_cghd hAxM.causallyArcConnected
    hAxN.causallyArcConnected hextM hextN U hψ hinj hGM hGN hGU hGV hSU hS hSU' hψS hψSV
  set V := (isEMorphismOn_of_liftPropOn 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y hψ).imageOpens U
    le_rfl with hVdef
  have hc : Corresponds (U : Set M) ψ p q := corresponds_iff_mapClusterPt.2 hcl
  have hZp : p ∈ C.Zminus := (hAxM.mem_Zminus_iff p).2 (hpreg 0 le_rfl)
  have hZq : q ∈ D.Zminus := (hAxN.mem_Zminus_iff q).2 (hqreg 0 le_rfl)
  have hclM := hGM.isClosed_Jplus_singleton hAxM.tarentin
  have hclN := hGN.isClosed_Jplus_singleton hAxN.tarentin
  have hpU : p ∉ (U : Set M) := by rw [U.isOpen.frontier_eq] at hp; exact hp.2
  have hsepM : C.Jplus ⊤ S ∈ 𝓝 p :=
    Causal.Causality.Jplus_mem_nhds_of_isCauchySurface hGM.1 hAxM.causallyArcConnected hextM hS
      (fun x => (hAxM.K_densite_sing x).2) (𝔐.isCompact_Jminus_inter_Jplus hGM S hS)
      ⟨hpS, fun h => hpU (hSU h)⟩
  have hqfr := hcorr.mem_frontier_of_corresponds hp hc
  have hqV : q ∉ (V : Set N) := by rw [V.isOpen.frontier_eq] at hqfr; exact hqfr.2
  have hqS := hcorr.mem_Jplus_of_corresponds hcvU hZp hAxN.pushUp hclN hc hqV hGM.1 hGN.1
    (hS.isAcausal hAxM.causallyArcConnected hextM) hSU hsepM
    (Causal.Causality.mem_Jplus_union_Jminus_of_isCauchySurface hextN hψS q)
  have hsepN : D.Jplus ⊤ (ψ '' S) ∈ 𝓝 q :=
    Causal.Causality.Jplus_mem_nhds_of_isCauchySurface hGN.1 hAxN.causallyArcConnected hextN hψS
      (fun x => (hAxN.K_densite_sing x).2) (𝔐.isCompact_Jminus_inter_Jplus hGN _ hψS)
      ⟨hqS, fun h => hqV ((hcorr.mapsTo.mono_left hSU).image_subset h)⟩
  exact germ_ext_reg U hψ hinj hcorr hcvU hcvV hGN hAxN.tarentin
    (hGM.stronglyCausal hAxM.tarentin) hAxM.causallyArcConnected hZp hZq hAxM.pushUp
    hAxN.pushUp hclM hclN ((hcorr.mapsTo.mono_left hSU).image_subset) hsepN hc hpreg hqreg

theorem germ_past_reg (U : Opens M) (ψ : M → N) (S : Set M)
    (hψ : LiftPropOn 𝔐.G.IsLocalStructomorphWithinAt ψ U)
    (hinj : InjOn ψ U) (hGM : (chartedCausality 𝔐.causalityY M).GloballyHyperbolic)
    (hGN : (chartedCausality 𝔐.causalityY N).GloballyHyperbolic)
    (hGU : (chartedCausality 𝔐.causalityY M).GloballyHyperbolicOn U)
    (hGV : (chartedCausality 𝔐.causalityY N).GloballyHyperbolicOn
      ((isEMorphismOn_of_liftPropOn 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y hψ).imageOpens U
        le_rfl))
    (hSU : S ⊆ U) (hS : (chartedCausality 𝔐.causalityY M).IsCauchySurface S)
    (hSU' : (chartedCausality 𝔐.causalityY M).IsCauchySurfaceOn U S)
    (hψS : (chartedCausality 𝔐.causalityY N).IsCauchySurface (ψ '' S))
    (hψSV : (chartedCausality 𝔐.causalityY N).IsCauchySurfaceOn
      ((isEMorphismOn_of_liftPropOn 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y hψ).imageOpens U
        le_rfl) (ψ '' S))
    (p : M) (q : N) (hp : p ∈ frontier (U : Set M))
    (hpS : p ∈ (chartedCausality 𝔐.causalityY M).Jminus ⊤ S)
    (hcl : MapClusterPt q (𝓝[(U : Set M)] p) ψ)
    (hpreg : chartAt 𝔐.Y p p ∈ 𝔐.regY) (hqreg : chartAt 𝔐.Y q q ∈ 𝔐.regY) :
    ∃ (O : Opens M) (φ : M → N), p ∈ O ∧ LiftPropOn 𝔐.G.IsLocalStructomorphWithinAt φ O ∧
      φ p = q ∧ EqOn φ ψ (O ⊓ U : Opens M) := by
  set C := chartedCausality 𝔐.causalityY M
  set D := chartedCausality 𝔐.causalityY N
  have hAxM : C.SingularFlatAxioms (chartedSing 𝔐.singY M) := 𝔐.singularFlatAxioms
  have hAxN : D.SingularFlatAxioms (chartedSing 𝔐.singY N) := 𝔐.singularFlatAxioms
  have hextM : C.CurvesExtend := 𝔐.curvesExtend hGM
  have hextN : D.CurvesExtend := 𝔐.curvesExtend hGN
  haveI : Nonempty M := ⟨p⟩
  obtain ⟨hcvU, hcvV, hcorr⟩ := isCorrPair_of_cghd hAxM.causallyArcConnected
    hAxN.causallyArcConnected hextM hextN U hψ hinj hGM hGN hGU hGV hSU hS hSU' hψS hψSV
  set V := (isEMorphismOn_of_liftPropOn 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y hψ).imageOpens U
    le_rfl with hVdef
  have hc : Corresponds (U : Set M) ψ p q := corresponds_iff_mapClusterPt.2 hcl
  have hcorr' := hcorr.dual
  have hcvU' : C.dual.CausallyConvexIn (U : Set M) ⊤ := Causal.Causality.dual_causallyConvexIn.2 hcvU
  have hcvV' : D.dual.CausallyConvexIn (V : Set N) ⊤ := Causal.Causality.dual_causallyConvexIn.2 hcvV
  have hZM : ∀ x, x ∈ C.dual.Zminus := fun x => hAxM.mem_Zplus x
  have hZN : ∀ y, y ∈ D.dual.Zminus := fun y => hAxN.mem_Zplus y
  have hPM : C.dual.PushUp := Causal.Causality.dual_pushUp.2 hAxM.pushUp
  have hPN : D.dual.PushUp := Causal.Causality.dual_pushUp.2 hAxN.pushUp
  have hclM : ∀ x, IsClosed (C.dual.Jplus ⊤ {x}) := hGM.isClosed_Jminus_singleton hAxM.tarentin
  have hclN : ∀ y, IsClosed (D.dual.Jplus ⊤ {y}) := hGN.isClosed_Jminus_singleton hAxN.tarentin
  have hpU : p ∉ (U : Set M) := by rw [U.isOpen.frontier_eq] at hp; exact hp.2
  have hsepM : C.dual.Jplus ⊤ S ∈ 𝓝 p :=
    Causal.Causality.Jminus_mem_nhds_of_isCauchySurface hGM.1 hAxM.causallyArcConnected hextM hS
      (fun x => (hAxM.K_densite_sing x).1) (𝔐.isCompact_Jplus_inter_Jminus hGM S hS)
      ⟨hpS, fun h => hpU (hSU h)⟩
  have hqfr := hcorr.mem_frontier_of_corresponds hp hc
  have hqV : q ∉ (V : Set N) := by rw [V.isOpen.frontier_eq] at hqfr; exact hqfr.2
  have hqS : q ∈ D.dual.Jplus ⊤ (ψ '' S) := hcorr'.mem_Jplus_of_corresponds hcvU' (hZM p) hPN
    hclN hc hqV (Causal.Causality.dual_isCausal.2 hGM.1) (Causal.Causality.dual_isCausal.2 hGN.1)
    (Causal.Causality.dual_isAcausal.2 (hS.isAcausal hAxM.causallyArcConnected hextM)) hSU hsepM
    (Causal.Causality.mem_Jplus_union_Jminus_of_isCauchySurface hextN hψS q).symm
  have hsepN : D.dual.Jplus ⊤ (ψ '' S) ∈ 𝓝 q :=
    Causal.Causality.Jminus_mem_nhds_of_isCauchySurface hGN.1 hAxN.causallyArcConnected hextN hψS
      (fun x => (hAxN.K_densite_sing x).1) (𝔐.isCompact_Jplus_inter_Jminus hGN _ hψS)
      ⟨hqS, fun h => hqV ((hcorr.mapsTo.mono_left hSU).image_subset h)⟩
  exact germ_ext_reg U hψ hinj hcorr' hcvU' hcvV'
    (Causal.Causality.dual_globallyHyperbolic.2 hGN) (Causal.Causality.dual_tarentin.2 hAxN.tarentin)
    (Causal.Causality.dual_stronglyCausal.2 (hGM.stronglyCausal hAxM.tarentin))
    (Causal.Causality.dual_causallyArcConnectedOn.2 hAxM.causallyArcConnected) (hZM p) (hZN q) hPM hPN
    hclM hclN ((hcorr.mapsTo.mono_left hSU).image_subset) hsepN hc hpreg hqreg

end Assembly
/-! ### A4 from a cone-slice form of B4 (interface round 3) -/

namespace TLocalModel

variable (𝔐 : TLocalModel.{u})

/-! The cone-slice B4 (`ConeSliceFuture`/`ConeSlicePast` of round 3) are the `TLocalModel` fields
`coneSliceFuture`/`coneSlicePast` since round 4 (gx-agreed 2026-11-02), statements verbatim. -/

variable {𝔐} {M : Type u} [TopologicalSpace M] [ChartedSpace 𝔐.Y M] [HasGroupoid M 𝔐.G]

/-- A preferred chart is an abstract morphism on its source (`Flat/CBGSlice`'s
`flatChart_isEMorphismOn`, for any local model). -/
theorem chart_isEMorphismOn (x : M) :
    Causal.IsEMorphismOn (chartedCausality 𝔐.causalityY M) 𝔐.causalityY (Causal.chartSource (chartAt 𝔐.Y x))
      (chartAt 𝔐.Y x) := by
  set e := chartAt 𝔐.Y x
  have hiso : Causal.ChartIso (chartedCausality 𝔐.causalityY M) 𝔐.causalityY e :=
    chartedCausality_chartIso 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y x
  have himg : ∀ V : Opens M, V ≤ Causal.chartSource e → ((Causal.chartImage e V : Opens _) : Set _) = e '' V :=
    fun V hV => Causal.coe_chartImage_of_le hV
  have hsub : ∀ (V : Opens M) (U : Opens 𝔐.Y), V ≤ Causal.chartSource e → MapsTo e V U →
      Causal.chartImage e V ≤ U := fun V U hV hmaps p hp => by
    rw [← SetLike.mem_coe, himg V hV] at hp
    obtain ⟨z, hz, rfl⟩ := hp
    exact hmaps hz
  exact
  { continuousOn := e.continuousOn
    isOpen_image := fun V hV => by rw [← himg V hV]; exact (Causal.chartImage e V).isOpen
    map_le := fun V U hV hmaps y z hyz =>
      𝔐.causalityY.le_mono (hsub V U hV hmaps)
        (((hiso V hV y ((chartedCausality 𝔐.causalityY M).le_mem_left hyz) z
          ((chartedCausality 𝔐.causalityY M).le_mem_right hyz)).1).1 hyz)
    map_lt := fun V U hV hmaps y z hyz =>
      𝔐.causalityY.lt_mono (hsub V U hV hmaps)
        (((hiso V hV y ((chartedCausality 𝔐.causalityY M).lt_mem_left hyz) z
          ((chartedCausality 𝔐.causalityY M).lt_mem_right hyz)).2).1 hyz)
    locally := fun z hz => ⟨Causal.chartSource e, le_rfl, hz, e.injOn, fun V' hV' U hU y hy w hw => by
      have hU' : Causal.chartImage e V' = U := SetLike.coe_injective (by rw [himg V' hV', hU])
      rw [← hU']; exact hiso V' hV' y hy w hw⟩ }

/-- `sing_α` read in any chart of the atlas equals `sing_α` read in the preferred chart at the
point (B3 `sing_mem` on the transition). -/
theorem chartAt_mem_singY_iff {x w : M} (hw : w ∈ (chartAt 𝔐.Y x).source) {α : ℝ} (hα : 0 ≤ α) :
    chartAt 𝔐.Y x w ∈ 𝔐.singY α ↔ chartAt 𝔐.Y w w ∈ 𝔐.singY α := by
  have he : (chartAt 𝔐.Y x).symm.trans (chartAt 𝔐.Y w) ∈ 𝔐.G :=
    𝔐.G.compatible (chart_mem_atlas _ x) (chart_mem_atlas _ w)
  have hmem : chartAt 𝔐.Y x w ∈ ((chartAt 𝔐.Y x).symm.trans (chartAt 𝔐.Y w)).source := by
    simp only [OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage,
      OpenPartialHomeomorph.symm_source]
    exact ⟨(chartAt _ x).map_source hw, by rw [(chartAt _ x).left_inv hw]; exact mem_chart_source _ w⟩
  have h := 𝔐.sing_mem _ he _ hmem α hα
  have h2 : ((chartAt 𝔐.Y x).symm.trans (chartAt 𝔐.Y w)) (chartAt 𝔐.Y x w) = chartAt 𝔐.Y w w := by
    simp [(chartAt 𝔐.Y x).left_inv hw]
  rwa [h2] at h


/-- **The assembly of A4 through a chart** (generic `Flat/CBGSlice` §3 end): an open `N ∋ κ p` of
`Y` inside `κ(W₀)` with a Cauchy surface `Γ ⊆ N` inside `κ(W₀ ∩ U)` gives, read back in `M`, an
open `N_M ∋ p` with Cauchy surface `Γ_M ⊆ U` (`Causal.IsEMorphismOn.isCauchySurfaceOn_image_iff` along
`chart_isEMorphismOn`), and `extend_of_cauchy_nbhd` concludes. -/
theorem slice_assemble [T2Space M] {x p : M} {U O W₀ : Opens M} {S : Set M}
    (hGH : (chartedCausality 𝔐.causalityY M).GloballyHyperbolic)
    (harc : (chartedCausality 𝔐.causalityY M).CausallyArcConnected)
    (hext : (chartedCausality 𝔐.causalityY M).CurvesExtend) (hSU : S ⊆ U)
    (hS : (chartedCausality 𝔐.causalityY M).IsCauchySurface S)
    (hSU' : (chartedCausality 𝔐.causalityY M).IsCauchySurfaceOn U S) (hpU : p ∉ U)
    (hpκ : p ∈ (chartAt 𝔐.Y x).source) (hW₀κ : W₀ ≤ Causal.chartSource (chartAt 𝔐.Y x))
    {N : Opens 𝔐.Y} {Γ : Set 𝔐.Y} (hNO : N ≤ Causal.chartImage (chartAt 𝔐.Y x) W₀)
    (hyN : chartAt 𝔐.Y x p ∈ N) (hΓN : Γ ⊆ N)
    (hΓG : Γ ⊆ chartAt 𝔐.Y x '' ((W₀ : Set M) ∩ U))
    (hNΓ : 𝔐.causalityY.IsCauchySurfaceOn N Γ) (hW₀O : (W₀ : Set M) ⊆ O) :
    ∃ U' : Opens M, U < U' ∧ (U' : Set M) ⊆ U ∪ O ∧
      (chartedCausality 𝔐.causalityY M).GloballyHyperbolicOn U' ∧
      (chartedCausality 𝔐.causalityY M).IsCauchySurfaceOn U' S := by
  set κ := chartAt 𝔐.Y x with hκ
  set C := chartedCausality 𝔐.causalityY M
  let NM : Opens M := ⟨κ.source ∩ κ ⁻¹' N, κ.isOpen_inter_preimage N.isOpen⟩
  set ΓM : Set M := κ.source ∩ κ ⁻¹' Γ with hΓMdef
  have hNM : (N : Set 𝔐.Y) = κ '' NM := by
    ext y
    constructor
    · intro hy
      obtain ⟨w, hws, -, rfl, -⟩ := Causal.exists_of_mem_chartImage (hNO hy)
      exact ⟨w, ⟨hws, hy⟩, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact hw.2
  have hΓM : κ '' ΓM = Γ := by
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw.2
    · intro hy
      obtain ⟨w, hws, -, rfl, -⟩ := Causal.exists_of_mem_chartImage (hNO (hΓN hy))
      exact ⟨w, ⟨hws, hy⟩, rfl⟩
  have hΓMN : ΓM ⊆ NM := fun w hw => ⟨hw.1, hΓN hw.2⟩
  have hNMcy : C.IsCauchySurfaceOn NM ΓM := by
    refine ((chart_isEMorphismOn x).isCauchySurfaceOn_image_iff κ.injOn
      (show NM ≤ Causal.chartSource κ from fun _ hw => hw.1) hNM hΓMN).2 ?_
    rw [hΓM]
    exact hNΓ
  have hΓMU : ΓM ⊆ U := by
    intro w hw
    obtain ⟨w', hw', hw'e⟩ := hΓG hw.2
    rw [← κ.injOn (hW₀κ hw'.1) hw.1 hw'e]
    exact hw'.2
  have hpNM : p ∈ NM := ⟨hpκ, hyN⟩
  have hNMO : (NM : Set M) ⊆ O := by
    intro w hw
    obtain ⟨w', hw's, hw'W, hw'e, -⟩ := Causal.exists_of_mem_chartImage (hNO hw.2)
    rw [← κ.injOn hw's hw.1 hw'e]
    exact hW₀O hw'W
  exact extend_of_cauchy_nbhd hGH harc hext hSU hS hSU' hNMcy hΓMU hpNM hpU hNMO

variable [T2Space M] [ConnectedSpace M] [SecondCountableTopology M]

/-- **A4 future from the cone-slice B4 (`coneSliceFuture`), off the BTZ locus** (Sbierski Thm 3.6, geometric half; the
construction of `Flat/CBGSlice`, generic): the corner condition puts the punctured past cone of `p`
near `p` into `U` (`mem_of_le_of_mem_interior_Jplus_of_mem_Zminus`), so the cone-slice `K` read in
the chart at `p` lies in the chart image of `U`, an open set, which therefore contains a Cauchy
surface `Γ` of an open `N ∋ p`; then `extend_of_cauchy_nbhd`. Uses neither R1 for `U` nor the
global hyperbolicity of `U`. -/
theorem slice_future_of_cone (U : Opens M) (S : Set M)
    (hGH : (chartedCausality 𝔐.causalityY M).GloballyHyperbolic) (hSU : S ⊆ U)
    (hS : (chartedCausality 𝔐.causalityY M).IsCauchySurface S)
    (hSU' : (chartedCausality 𝔐.causalityY M).IsCauchySurfaceOn U S)
    (p : M) (hp : p ∈ frontier (U : Set M))
    (hpS : p ∈ (chartedCausality 𝔐.causalityY M).Jplus ⊤ S)
    (hcorner : (chartedCausality 𝔐.causalityY M).Jminus ⊤ {p} ∩ frontier (U : Set M) ∩
      (chartedCausality 𝔐.causalityY M).Jplus ⊤ S = {p})
    (O : Opens M) (hpO : p ∈ O) (hp0 : chartAt 𝔐.Y p p ∉ 𝔐.singY 0) :
    ∃ U' : Opens M, U < U' ∧ (U' : Set M) ⊆ U ∪ O ∧
      (chartedCausality 𝔐.causalityY M).GloballyHyperbolicOn U' ∧
      (chartedCausality 𝔐.causalityY M).IsCauchySurfaceOn U' S := by
  set C := chartedCausality 𝔐.causalityY M
  have hAx : C.SingularFlatAxioms (chartedSing 𝔐.singY M) := 𝔐.singularFlatAxioms
  have harc := hAx.causallyArcConnected
  have hext : C.CurvesExtend := 𝔐.curvesExtend hGH
  have hconv : C.CausallyConvexIn (U : Set M) ⊤ :=
    Causal.Causality.causallyConvexIn_of_isCauchySurfaceOn hGH.1 harc hext le_top hSU hSU' hS
  have hpU : p ∉ U := fun h => hp.2 (by rwa [U.isOpen.interior_eq])
  have hpcl : p ∈ closure (U : Set M) := hp.1
  have hJ : C.Jplus ⊤ S ∈ 𝓝 p :=
    Causal.Causality.Jplus_mem_nhds_of_isCauchySurface hGH.1 harc hext hS
      (fun x => (hAx.K_densite_sing x).2) (𝔐.isCompact_Jminus_inter_Jplus hGH S hS)
      ⟨hpS, fun h => hpU (hSU h)⟩
  set κ := chartAt 𝔐.Y p with hκ
  have hpκ : p ∈ κ.source := mem_chart_source _ p
  let W₀ : Opens M := ⟨interior (C.Jplus ⊤ S) ∩ O ∩ κ.source,
    (isOpen_interior.inter O.isOpen).inter κ.open_source⟩
  have hpW₀ : p ∈ W₀ := ⟨⟨mem_interior_iff_mem_nhds.2 hJ, hpO⟩, hpκ⟩
  have hW₀κ : W₀ ≤ Causal.chartSource κ := fun z hz => hz.2
  have hiso := chartedCausality_chartIso (M := M) 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y p
  obtain ⟨K, hKO, hKrel, hGam⟩ := 𝔐.coneSliceFuture (κ p) hp0 (Causal.chartImage κ W₀) (Causal.mem_chartImage_of_mem hpκ hpW₀)
  have hKU : K ⊆ κ '' ((W₀ : Set M) ∩ U) := by
    intro z hz
    obtain ⟨hz0, hzne, hzle⟩ := hKrel z hz
    obtain ⟨w, hws, hwW, rfl, -⟩ := Causal.exists_of_mem_chartImage (hKO hz)
    refine ⟨w, ⟨hwW, ?_⟩, rfl⟩
    have hwp : C.le W₀ w p := ((hiso W₀ hW₀κ w hwW p hpW₀).1).2 hzle
    have hwZ : w ∈ C.Zminus :=
      (hAx.mem_Zminus_iff w).2 fun h => hz0 ((chartAt_mem_singY_iff hws le_rfl).2 h)
    exact mem_of_le_of_mem_interior_Jplus_of_mem_Zminus hconv hSU hpcl hAx.pushUp
      hcorner hwZ hwW.1.1 (C.le_mono le_top hwp) fun h => hzne (by rw [h])
  have hGo : IsOpen (κ '' ((W₀ : Set M) ∩ U)) :=
    κ.isOpen_image_of_subset_source (W₀.isOpen.inter U.isOpen) fun z hz => hz.1.2
  obtain ⟨N, Γ, hyN, hNO, hΓN, hΓG, hNΓ⟩ := hGam _ hGo hKU
  exact slice_assemble hGH harc hext hSU hS hSU' hpU hpκ hW₀κ hNO hyN hΓN hΓG hNΓ
    fun w hw => hw.1.2

/-- **A4 past from the cone-slice B4 (`coneSlicePast`), at every boundary point** (no time reversal of the model;
the slice is taken above `p`, inside the punctured future cone, which the corner condition puts
into `U` near `p`: `mem_of_ge_of_mem_interior_Jminus`, every point being in `Z⁺`). -/
theorem slice_past_of_cone (U : Opens M) (S : Set M)
    (hGH : (chartedCausality 𝔐.causalityY M).GloballyHyperbolic) (hSU : S ⊆ U)
    (hS : (chartedCausality 𝔐.causalityY M).IsCauchySurface S)
    (hSU' : (chartedCausality 𝔐.causalityY M).IsCauchySurfaceOn U S)
    (p : M) (hp : p ∈ frontier (U : Set M))
    (hpS : p ∈ (chartedCausality 𝔐.causalityY M).Jminus ⊤ S)
    (hcorner : (chartedCausality 𝔐.causalityY M).Jplus ⊤ {p} ∩ frontier (U : Set M) ∩
      (chartedCausality 𝔐.causalityY M).Jminus ⊤ S = {p})
    (O : Opens M) (hpO : p ∈ O) :
    ∃ U' : Opens M, U < U' ∧ (U' : Set M) ⊆ U ∪ O ∧
      (chartedCausality 𝔐.causalityY M).GloballyHyperbolicOn U' ∧
      (chartedCausality 𝔐.causalityY M).IsCauchySurfaceOn U' S := by
  set C := chartedCausality 𝔐.causalityY M
  have hAx : C.SingularFlatAxioms (chartedSing 𝔐.singY M) := 𝔐.singularFlatAxioms
  have harc := hAx.causallyArcConnected
  have hext : C.CurvesExtend := 𝔐.curvesExtend hGH
  have hconv : C.CausallyConvexIn (U : Set M) ⊤ :=
    Causal.Causality.causallyConvexIn_of_isCauchySurfaceOn hGH.1 harc hext le_top hSU hSU' hS
  have hpU : p ∉ U := fun h => hp.2 (by rwa [U.isOpen.interior_eq])
  have hpcl : p ∈ closure (U : Set M) := hp.1
  have hJ : C.Jminus ⊤ S ∈ 𝓝 p :=
    Causal.Causality.Jminus_mem_nhds_of_isCauchySurface hGH.1 harc hext hS
      (fun x => (hAx.K_densite_sing x).1) (𝔐.isCompact_Jplus_inter_Jminus hGH S hS)
      ⟨hpS, fun h => hpU (hSU h)⟩
  set κ := chartAt 𝔐.Y p with hκ
  have hpκ : p ∈ κ.source := mem_chart_source _ p
  let W₀ : Opens M := ⟨interior (C.Jminus ⊤ S) ∩ O ∩ κ.source,
    (isOpen_interior.inter O.isOpen).inter κ.open_source⟩
  have hpW₀ : p ∈ W₀ := ⟨⟨mem_interior_iff_mem_nhds.2 hJ, hpO⟩, hpκ⟩
  have hW₀κ : W₀ ≤ Causal.chartSource κ := fun z hz => hz.2
  have hiso := chartedCausality_chartIso (M := M) 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y p
  obtain ⟨K, hKO, hKrel, hGam⟩ := 𝔐.coneSlicePast (κ p) (Causal.chartImage κ W₀) (Causal.mem_chartImage_of_mem hpκ hpW₀)
  have hKU : K ⊆ κ '' ((W₀ : Set M) ∩ U) := by
    intro z hz
    obtain ⟨hzne, hzle⟩ := hKrel z hz
    obtain ⟨w, hws, hwW, rfl, -⟩ := Causal.exists_of_mem_chartImage (hKO hz)
    refine ⟨w, ⟨hwW, ?_⟩, rfl⟩
    have hpw : C.le W₀ p w := ((hiso W₀ hW₀κ p hpW₀ w hwW).1).2 hzle
    exact mem_of_ge_of_mem_interior_Jminus hconv hSU hpcl hAx.pushUp hAx.mem_Zplus hcorner
      hwW.1.1 (C.le_mono le_top hpw) fun h => hzne (by rw [h])
  have hGo : IsOpen (κ '' ((W₀ : Set M) ∩ U)) :=
    κ.isOpen_image_of_subset_source (W₀.isOpen.inter U.isOpen) fun z hz => hz.1.2
  obtain ⟨N, Γ, hyN, hNO, hΓN, hΓG, hNΓ⟩ := hGam _ hGo hKU
  exact slice_assemble hGH harc hext hSU hS hSU' hpU hpκ hW₀κ hNO hyN hΓN hΓG hNΓ
    fun w hw => hw.1.2

end TLocalModel
/-! ### A3 at non-BTZ boundary points (interface round 4) -/

section AssemblyNonBTZ

variable {𝔐 : TLocalModel.{u}} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace 𝔐.Y M] [ChartedSpace 𝔐.Y N] [HasGroupoid M 𝔐.G] [HasGroupoid N 𝔐.G]
  [T2Space M] [ConnectedSpace M] [SecondCountableTopology M]
  [T2Space N] [ConnectedSpace N] [SecondCountableTopology N]

/-- **A3 future at a non-BTZ boundary point, any local model** (round 4; Sbierski Lemma 3.8,
`cor:ext_continue`): the conclusion of `GermExtFuture` at every boundary point `p` off the BTZ
locus, regular or massive, from the Level-B fields only (`T2Space Y`, `typeAgreement`,
`dense_regY`, `isOpen_regY`, B1, B2, B3). The corresponding `q` is not BTZ either, model-free
(Prop 3.7: some `x ∈ U` with `x ≪ p` gives `ψ x ≪ q`, and a BTZ point has empty chronological
past). The diamond of the piece is read in the preferred chart at `p` (first disjunct of
`typeAgreement`'s largeness clause); a massive `p` contributes the points of its line below it
(`exists_massive_near`). -/
theorem germ_future_nonBTZ (U : Opens M) (ψ : M → N) (S : Set M)
    (hψ : LiftPropOn 𝔐.G.IsLocalStructomorphWithinAt ψ U)
    (hinj : InjOn ψ U) (hGM : (chartedCausality 𝔐.causalityY M).GloballyHyperbolic)
    (hGN : (chartedCausality 𝔐.causalityY N).GloballyHyperbolic)
    (hGU : (chartedCausality 𝔐.causalityY M).GloballyHyperbolicOn U)
    (hGV : (chartedCausality 𝔐.causalityY N).GloballyHyperbolicOn
      ((isEMorphismOn_of_liftPropOn 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y hψ).imageOpens U
        le_rfl))
    (hSU : S ⊆ U) (hS : (chartedCausality 𝔐.causalityY M).IsCauchySurface S)
    (hSU' : (chartedCausality 𝔐.causalityY M).IsCauchySurfaceOn U S)
    (hψS : (chartedCausality 𝔐.causalityY N).IsCauchySurface (ψ '' S))
    (hψSV : (chartedCausality 𝔐.causalityY N).IsCauchySurfaceOn
      ((isEMorphismOn_of_liftPropOn 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y hψ).imageOpens U
        le_rfl) (ψ '' S))
    (p : M) (q : N) (hp : p ∈ frontier (U : Set M))
    (hpS : p ∈ (chartedCausality 𝔐.causalityY M).Jplus ⊤ S)
    (hcl : MapClusterPt q (𝓝[(U : Set M)] p) ψ)
    (hp0 : chartAt 𝔐.Y p p ∉ 𝔐.singY 0) :
    ∃ (O : Opens M) (φ : M → N), p ∈ O ∧ LiftPropOn 𝔐.G.IsLocalStructomorphWithinAt φ O ∧
      φ p = q ∧ EqOn φ ψ (O ⊓ U : Opens M) := by
  set C := chartedCausality 𝔐.causalityY M
  set D := chartedCausality 𝔐.causalityY N
  have hAxM : C.SingularFlatAxioms (chartedSing 𝔐.singY M) := 𝔐.singularFlatAxioms
  have hAxN : D.SingularFlatAxioms (chartedSing 𝔐.singY N) := 𝔐.singularFlatAxioms
  have hextM : C.CurvesExtend := 𝔐.curvesExtend hGM
  have hextN : D.CurvesExtend := 𝔐.curvesExtend hGN
  haveI : Nonempty M := ⟨p⟩
  obtain ⟨hcvU, hcvV, hcorr⟩ := isCorrPair_of_cghd hAxM.causallyArcConnected
    hAxN.causallyArcConnected hextM hextN U hψ hinj hGM hGN hGU hGV hSU hS hSU' hψS hψSV
  set V := (isEMorphismOn_of_liftPropOn 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y hψ).imageOpens U
    le_rfl with hVdef
  have hc : Corresponds (U : Set M) ψ p q := corresponds_iff_mapClusterPt.2 hcl
  have hZp : p ∈ C.Zminus := (hAxM.mem_Zminus_iff p).2 hp0
  have hclM := hGM.isClosed_Jplus_singleton hAxM.tarentin
  have hclN := hGN.isClosed_Jplus_singleton hAxN.tarentin
  have hpU : p ∉ (U : Set M) := by rw [U.isOpen.frontier_eq] at hp; exact hp.2
  have hsepM : C.Jplus ⊤ S ∈ 𝓝 p :=
    Causal.Causality.Jplus_mem_nhds_of_isCauchySurface hGM.1 hAxM.causallyArcConnected hextM hS
      (fun x => (hAxM.K_densite_sing x).2) (𝔐.isCompact_Jminus_inter_Jplus hGM S hS)
      ⟨hpS, fun h => hpU (hSU h)⟩
  -- `q` is not BTZ: `ψ x ≪ q` for some `x ∈ U`, and `I⁻` of a BTZ point is empty
  have hq0 : chartAt 𝔐.Y q q ∉ 𝔐.singY 0 := by
    intro hq0
    obtain ⟨x, hxI, hxJ⟩ := hZp _ hsepM
    have hxp : C.lt ⊤ x p := by simpa using hxI
    have hxU := mem_of_mem_Jplus_of_lt hcvU hSU (mem_closure_of_corresponds hc) hxJ hxp
    have hxq := hcorr.lt_of_lt_of_corresponds hcvU hZp hAxN.pushUp hclN hc hxU hxp
    have hmem : ψ x ∈ D.Iminus ⊤ {q} := by simpa using hxq
    rw [hAxN.Iminus_eq_empty q hq0] at hmem
    exact hmem
  have hZq : q ∈ D.Zminus := (hAxN.mem_Zminus_iff q).2 hq0
  have hqfr := hcorr.mem_frontier_of_corresponds hp hc
  have hqV : q ∉ (V : Set N) := by rw [V.isOpen.frontier_eq] at hqfr; exact hqfr.2
  have hqS := hcorr.mem_Jplus_of_corresponds hcvU hZp hAxN.pushUp hclN hc hqV hGM.1 hGN.1
    (hS.isAcausal hAxM.causallyArcConnected hextM) hSU hsepM
    (Causal.Causality.mem_Jplus_union_Jminus_of_isCauchySurface hextN hψS q)
  have hsepN : D.Jplus ⊤ (ψ '' S) ∈ 𝓝 q :=
    Causal.Causality.Jplus_mem_nhds_of_isCauchySurface hGN.1 hAxN.causallyArcConnected hextN hψS
      (fun x => (hAxN.K_densite_sing x).2) (𝔐.isCompact_Jminus_inter_Jplus hGN _ hψS)
      ⟨hqS, fun h => hqV ((hcorr.mapsTo.mono_left hSU).image_subset h)⟩
  have hiso := chartedCausality_chartIso (M := M) 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y p
  have hpW : p ∈ Causal.chartSource (chartAt 𝔐.Y p) := mem_chart_source _ p
  refine germ_ext_nonBTZ U hψ hinj hcorr hcvU hcvV hGN hAxN.tarentin
    (hGM.stronglyCausal hAxM.tarentin) hAxM.causallyArcConnected hZp hZq hAxM.pushUp
    hAxN.pushUp hclM hclN ((hcorr.mapsTo.mono_left hSU).image_subset) hsepN hc hp0 ?_ ?_
  · -- the piece's diamond `I⁺_W(a) ∩ I⁻_W(p)` read in the chart: below the tip `κ p`
    intro a A hlt hsub
    have haW : a ∈ Causal.chartSource (chartAt 𝔐.Y p) := C.lt_mem_left hlt
    refine ⟨Causal.chartImage (chartAt 𝔐.Y p) (Causal.chartSource (chartAt 𝔐.Y p)),
      Causal.mem_chartImage_of_mem hpW hpW, chartAt 𝔐.Y p a, Causal.mem_chartImage_of_mem haW haW,
      Or.inl ⟨((hiso _ le_rfl a haW p hpW).2).1 hlt, ?_⟩⟩
    rw [← chartedCausality_image_Iplus_inter_Iminus 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y p
      le_rfl haW hpW]
    exact image_mono hsub
  · -- a massive `p`: the points of its line below it
    intro hpreg W hW
    obtain ⟨α, hα0, hpα⟩ := 𝔐.exists_mem_singY_of_not_mem_regY hpreg
    have hαpos : 0 < α := lt_of_le_of_ne hα0 (by rintro rfl; exact hp0 hpα)
    obtain ⟨⟨b, hbW, hbα, hbp⟩, -⟩ := exists_massive_near hAxM hαpos (p := p) hpα
      (inter_mem hW ((chartAt 𝔐.Y p).open_source.mem_nhds (mem_chart_source _ p)))
    exact ⟨b, hbW.1, hbp, fun hreg => hreg α hα0 ((TLocalModel.chartAt_mem_singY_iff hbW.2 hα0).2 hbα)⟩

/-- **A3 past at a non-BTZ boundary point, any local model** (round 4; the `K⁺` side): as
`germ_future_nonBTZ` for `C.dual` (every point is in `Z⁺`, `mem_Zplus`); the piece's diamond
`I⁺_W(p) ∩ I⁻_W(a)` lies above the tip `κ p` (second disjunct of `typeAgreement`'s largeness
clause); a massive `p` contributes the points of its line above it. Here `q` may a priori be BTZ;
`typeAgreement` excludes it. -/
theorem germ_past_nonBTZ (U : Opens M) (ψ : M → N) (S : Set M)
    (hψ : LiftPropOn 𝔐.G.IsLocalStructomorphWithinAt ψ U)
    (hinj : InjOn ψ U) (hGM : (chartedCausality 𝔐.causalityY M).GloballyHyperbolic)
    (hGN : (chartedCausality 𝔐.causalityY N).GloballyHyperbolic)
    (hGU : (chartedCausality 𝔐.causalityY M).GloballyHyperbolicOn U)
    (hGV : (chartedCausality 𝔐.causalityY N).GloballyHyperbolicOn
      ((isEMorphismOn_of_liftPropOn 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y hψ).imageOpens U
        le_rfl))
    (hSU : S ⊆ U) (hS : (chartedCausality 𝔐.causalityY M).IsCauchySurface S)
    (hSU' : (chartedCausality 𝔐.causalityY M).IsCauchySurfaceOn U S)
    (hψS : (chartedCausality 𝔐.causalityY N).IsCauchySurface (ψ '' S))
    (hψSV : (chartedCausality 𝔐.causalityY N).IsCauchySurfaceOn
      ((isEMorphismOn_of_liftPropOn 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y hψ).imageOpens U
        le_rfl) (ψ '' S))
    (p : M) (q : N) (hp : p ∈ frontier (U : Set M))
    (hpS : p ∈ (chartedCausality 𝔐.causalityY M).Jminus ⊤ S)
    (hcl : MapClusterPt q (𝓝[(U : Set M)] p) ψ)
    (hp0 : chartAt 𝔐.Y p p ∉ 𝔐.singY 0) :
    ∃ (O : Opens M) (φ : M → N), p ∈ O ∧ LiftPropOn 𝔐.G.IsLocalStructomorphWithinAt φ O ∧
      φ p = q ∧ EqOn φ ψ (O ⊓ U : Opens M) := by
  set C := chartedCausality 𝔐.causalityY M
  set D := chartedCausality 𝔐.causalityY N
  have hAxM : C.SingularFlatAxioms (chartedSing 𝔐.singY M) := 𝔐.singularFlatAxioms
  have hAxN : D.SingularFlatAxioms (chartedSing 𝔐.singY N) := 𝔐.singularFlatAxioms
  have hextM : C.CurvesExtend := 𝔐.curvesExtend hGM
  have hextN : D.CurvesExtend := 𝔐.curvesExtend hGN
  haveI : Nonempty M := ⟨p⟩
  obtain ⟨hcvU, hcvV, hcorr⟩ := isCorrPair_of_cghd hAxM.causallyArcConnected
    hAxN.causallyArcConnected hextM hextN U hψ hinj hGM hGN hGU hGV hSU hS hSU' hψS hψSV
  set V := (isEMorphismOn_of_liftPropOn 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y hψ).imageOpens U
    le_rfl with hVdef
  have hc : Corresponds (U : Set M) ψ p q := corresponds_iff_mapClusterPt.2 hcl
  have hcorr' := hcorr.dual
  have hcvU' : C.dual.CausallyConvexIn (U : Set M) ⊤ := Causal.Causality.dual_causallyConvexIn.2 hcvU
  have hcvV' : D.dual.CausallyConvexIn (V : Set N) ⊤ := Causal.Causality.dual_causallyConvexIn.2 hcvV
  have hZM : ∀ x, x ∈ C.dual.Zminus := fun x => hAxM.mem_Zplus x
  have hZN : ∀ y, y ∈ D.dual.Zminus := fun y => hAxN.mem_Zplus y
  have hPM : C.dual.PushUp := Causal.Causality.dual_pushUp.2 hAxM.pushUp
  have hPN : D.dual.PushUp := Causal.Causality.dual_pushUp.2 hAxN.pushUp
  have hclM : ∀ x, IsClosed (C.dual.Jplus ⊤ {x}) := hGM.isClosed_Jminus_singleton hAxM.tarentin
  have hclN : ∀ y, IsClosed (D.dual.Jplus ⊤ {y}) := hGN.isClosed_Jminus_singleton hAxN.tarentin
  have hpU : p ∉ (U : Set M) := by rw [U.isOpen.frontier_eq] at hp; exact hp.2
  have hsepM : C.dual.Jplus ⊤ S ∈ 𝓝 p :=
    Causal.Causality.Jminus_mem_nhds_of_isCauchySurface hGM.1 hAxM.causallyArcConnected hextM hS
      (fun x => (hAxM.K_densite_sing x).1) (𝔐.isCompact_Jplus_inter_Jminus hGM S hS)
      ⟨hpS, fun h => hpU (hSU h)⟩
  have hqfr := hcorr.mem_frontier_of_corresponds hp hc
  have hqV : q ∉ (V : Set N) := by rw [V.isOpen.frontier_eq] at hqfr; exact hqfr.2
  have hqS : q ∈ D.dual.Jplus ⊤ (ψ '' S) := hcorr'.mem_Jplus_of_corresponds hcvU' (hZM p) hPN
    hclN hc hqV (Causal.Causality.dual_isCausal.2 hGM.1) (Causal.Causality.dual_isCausal.2 hGN.1)
    (Causal.Causality.dual_isAcausal.2 (hS.isAcausal hAxM.causallyArcConnected hextM)) hSU hsepM
    (Causal.Causality.mem_Jplus_union_Jminus_of_isCauchySurface hextN hψS q).symm
  have hsepN : D.dual.Jplus ⊤ (ψ '' S) ∈ 𝓝 q :=
    Causal.Causality.Jminus_mem_nhds_of_isCauchySurface hGN.1 hAxN.causallyArcConnected hextN hψS
      (fun x => (hAxN.K_densite_sing x).1) (𝔐.isCompact_Jplus_inter_Jminus hGN _ hψS)
      ⟨hqS, fun h => hqV ((hcorr.mapsTo.mono_left hSU).image_subset h)⟩
  have hiso := chartedCausality_chartIso (M := M) 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y p
  have hpW : p ∈ Causal.chartSource (chartAt 𝔐.Y p) := mem_chart_source _ p
  refine germ_ext_nonBTZ U hψ hinj hcorr' hcvU' hcvV'
    (Causal.Causality.dual_globallyHyperbolic.2 hGN) (Causal.Causality.dual_tarentin.2 hAxN.tarentin)
    (Causal.Causality.dual_stronglyCausal.2 (hGM.stronglyCausal hAxM.tarentin))
    (Causal.Causality.dual_causallyArcConnectedOn.2 hAxM.causallyArcConnected) (hZM p) (hZN q) hPM hPN
    hclM hclN ((hcorr.mapsTo.mono_left hSU).image_subset) hsepN hc hp0 ?_ ?_
  · -- the piece's diamond `I⁺_W(p) ∩ I⁻_W(a)` read in the chart: above the tip `κ p`
    intro a A hlt hsub
    have hlt' : C.lt (Causal.chartSource (chartAt 𝔐.Y p)) p a := hlt
    have haW : a ∈ Causal.chartSource (chartAt 𝔐.Y p) := C.lt_mem_right hlt'
    refine ⟨Causal.chartImage (chartAt 𝔐.Y p) (Causal.chartSource (chartAt 𝔐.Y p)),
      Causal.mem_chartImage_of_mem hpW hpW, chartAt 𝔐.Y p a, Causal.mem_chartImage_of_mem haW haW,
      Or.inr ⟨((hiso _ le_rfl p hpW a haW).2).1 hlt', ?_⟩⟩
    rw [← chartedCausality_image_Iplus_inter_Iminus 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y p
      le_rfl hpW haW]
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨z, hsub ⟨hz.2, hz.1⟩, rfl⟩
  · -- a massive `p`: the points of its line above it
    intro hpreg W hW
    obtain ⟨α, hα0, hpα⟩ := 𝔐.exists_mem_singY_of_not_mem_regY hpreg
    have hαpos : 0 < α := lt_of_le_of_ne hα0 (by rintro rfl; exact hp0 hpα)
    obtain ⟨-, ⟨b, hbW, hbα, hpb⟩⟩ := exists_massive_near hAxM hαpos (p := p) hpα
      (inter_mem hW ((chartAt 𝔐.Y p).open_source.mem_nhds (mem_chart_source _ p)))
    exact ⟨b, hbW.1, hpb, fun hreg => hreg α hα0 ((TLocalModel.chartAt_mem_singY_iff hbW.2 hα0).2 hbα)⟩

end AssemblyNonBTZ
/-! ### A3 and A4 for a local model: derived, the BTZ cases as explicit hypotheses (round 4) -/

namespace TLocalModel

variable (𝔐 : TLocalModel.{u})

/-- **The residual of A3 future: BTZ boundary points** (round 4; the hypothesis `hA3f` of
`Geometry.ofLocalModelOfBTZ`). The statement of `GermExtFuture` at boundary points `p` of the BTZ
locus (`p ∈ sing s 0`, last hypothesis). Not derived here: at a BTZ `p`, `I⁻(p) = ∅`, so `p ∉ Z⁻`
and Sbierski's past piece of `U` near `p` is empty. **Owed by gx for `E₀`**: thesis
`lem:passe_pgcd` (`these.tex:6541–6554`) — a point of `p`'s line below `p` lies in `U` — then B2 at
a singular point of `U` (`localUnique_sing`), as in the massive case (`germ_ext_nonBTZ`).
Vacuous for a model without BTZ points (`germExtFutureBTZ_of_singY_zero`). -/
def GermExtFutureBTZ : Prop :=
  ∀ {M N : Type u} [TopologicalSpace M] [TopologicalSpace N] [T2Space M]
    [ConnectedSpace M] [SecondCountableTopology M] [T2Space N] [ConnectedSpace N]
    [SecondCountableTopology N] (s : 𝔐.Str M) (t : 𝔐.Str N) (U : Opens M)
    (ψ : M → N) (S : Set M) (h : IsMor s t U ψ), InjOn ψ U →
    (causality s).GloballyHyperbolic → (causality t).GloballyHyperbolic →
    (causality s).GloballyHyperbolicOn U →
    (causality t).GloballyHyperbolicOn ((isEMorphismOn_of_isMor h).imageOpens U le_rfl) →
    S ⊆ U → (causality s).IsCauchySurface S → (causality s).IsCauchySurfaceOn U S →
    (causality t).IsCauchySurface (ψ '' S) →
    (causality t).IsCauchySurfaceOn ((isEMorphismOn_of_isMor h).imageOpens U le_rfl) (ψ '' S) →
    ∀ p : M, ∀ q : N, p ∈ frontier (U : Set M) → p ∈ (causality s).Jplus ⊤ S →
      MapClusterPt q (𝓝[(U : Set M)] p) ψ → p ∈ sing s 0 →
      ∃ (O : Opens M) (φ : M → N), p ∈ O ∧ IsMor s t O φ ∧ φ p = q ∧ EqOn φ ψ (O ⊓ U : Opens M)

/-- **The residual of A3 past: BTZ boundary points** (round 4; the hypothesis `hA3p` of
`Geometry.ofLocalModelOfBTZ`). The statement of `GermExtPast` at boundary points `p` of the BTZ
locus. Not derived here. The route is mapped: `germ_exists_piece` for `C.dual` gives a connected
open `A ⊆ U ∩ I⁺(p)` with `I⁺(p) ∩ I⁻(a) ⊆ A` and `ψ → q` along `A`, whose chart image meets the
round-3 diamond clause of `localUnique_sing_adherent` (`diamond_clause_of_piece`, proved).
**Owed by gx for `E₀`**: a **regular** `a ∈ U ∩ I⁺(p)` (density of `reg` in `I⁺(p)`), `I⁺(p)`
**regular near `p`** (so the piece is a regular set, as `localUnique_sing_adherent` asks), and the
corresponding `q` BTZ with its chart in the component of `κ p` (type agreement at a BTZ point,
which `typeAgreement` does not ask). Vacuous without BTZ points. -/
def GermExtPastBTZ : Prop :=
  ∀ {M N : Type u} [TopologicalSpace M] [TopologicalSpace N] [T2Space M]
    [ConnectedSpace M] [SecondCountableTopology M] [T2Space N] [ConnectedSpace N]
    [SecondCountableTopology N] (s : 𝔐.Str M) (t : 𝔐.Str N) (U : Opens M)
    (ψ : M → N) (S : Set M) (h : IsMor s t U ψ), InjOn ψ U →
    (causality s).GloballyHyperbolic → (causality t).GloballyHyperbolic →
    (causality s).GloballyHyperbolicOn U →
    (causality t).GloballyHyperbolicOn ((isEMorphismOn_of_isMor h).imageOpens U le_rfl) →
    S ⊆ U → (causality s).IsCauchySurface S → (causality s).IsCauchySurfaceOn U S →
    (causality t).IsCauchySurface (ψ '' S) →
    (causality t).IsCauchySurfaceOn ((isEMorphismOn_of_isMor h).imageOpens U le_rfl) (ψ '' S) →
    ∀ p : M, ∀ q : N, p ∈ frontier (U : Set M) → p ∈ (causality s).Jminus ⊤ S →
      MapClusterPt q (𝓝[(U : Set M)] p) ψ → p ∈ sing s 0 →
      ∃ (O : Opens M) (φ : M → N), p ∈ O ∧ IsMor s t O φ ∧ φ p = q ∧ EqOn φ ψ (O ⊓ U : Opens M)

/-- **The residual of A4 future: BTZ boundary points** (round 4; the hypothesis `hA4f` of
`Geometry.ofLocalModelOfBTZ`). The statement of `SliceFuture` at boundary points `p` of the BTZ
locus. Not derived here: near a BTZ `p` the punctured causal past `J⁻(p) ∖ {p}` is a segment of
`p`'s line (`past_local`), so no cone slice exists (`coneSliceFuture` is asked off `sing₀`), and
the cone lemma's `Z⁻` step fails on the line (`I⁻ = ∅`). **Owed by gx for `E₀`**: a slice off the
cone — Sbierski's `τ_q`, `q ∈ I⁺(p)`, with Lemma 3.11 (the maximum of `τ_q` on the compact
`J⁻(q) ∩ Uᶜ ∩ J⁺(Σ)`), or an `E₀`-specific slice, with what the corner condition gives on the line
below `p`. Vacuous without BTZ points. -/
def SliceFutureBTZ : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [SecondCountableTopology M] (s : 𝔐.Str M) (U : Opens M) (S : Set M),
    (causality s).GloballyHyperbolic →
    (causality s).GloballyHyperbolicOn U → S ⊆ U → (causality s).IsCauchySurface S →
    (causality s).IsCauchySurfaceOn U S → ∀ p : M, p ∈ frontier (U : Set M) →
    p ∈ (causality s).Jplus ⊤ S →
    (causality s).Jminus ⊤ {p} ∩ frontier (U : Set M) ∩ (causality s).Jplus ⊤ S = {p} →
    ∀ O : Opens M, p ∈ O → p ∈ sing s 0 → ∃ U' : Opens M, U < U' ∧ (U' : Set M) ⊆ U ∪ O ∧
      (causality s).GloballyHyperbolicOn U' ∧ (causality s).IsCauchySurfaceOn U' S

variable {𝔐}

/-- **A3 future from Level B, BTZ points as a hypothesis** (Sbierski Lemma 3.8;
`cor:ext_continue`): off the BTZ locus `germ_future_nonBTZ` (regular and massive `p`), at BTZ
points `hB`. -/
theorem germExtFuture_of (hB : 𝔐.GermExtFutureBTZ) : 𝔐.GermExtFuture := by
  intro M N _ _ _ _ _ _ _ _ s t U ψ S h hinj hGM hGN hGU hGV hSU hS hSU' hψS hψSV p q hp hpS hcl
  by_cases hp0 : p ∈ sing s 0
  · exact hB s t U ψ S h hinj hGM hGN hGU hGV hSU hS hSU' hψS hψSV p q hp hpS hcl hp0
  obtain ⟨cs, hgs⟩ := s
  obtain ⟨ct, hgt⟩ := t
  exact germ_future_nonBTZ U ψ S h hinj hGM hGN hGU hGV hSU hS hSU' hψS hψSV p q hp hpS hcl hp0

/-- **A3 past from Level B, BTZ points as a hypothesis** (Sbierski Lemma 3.8, the `K⁺` side):
off the BTZ locus `germ_past_nonBTZ`, at BTZ points `hB`. -/
theorem germExtPast_of (hB : 𝔐.GermExtPastBTZ) : 𝔐.GermExtPast := by
  intro M N _ _ _ _ _ _ _ _ s t U ψ S h hinj hGM hGN hGU hGV hSU hS hSU' hψS hψSV p q hp hpS hcl
  by_cases hp0 : p ∈ sing s 0
  · exact hB s t U ψ S h hinj hGM hGN hGU hGV hSU hS hSU' hψS hψSV p q hp hpS hcl hp0
  obtain ⟨cs, hgs⟩ := s
  obtain ⟨ct, hgt⟩ := t
  exact germ_past_nonBTZ U ψ S h hinj hGM hGN hGU hGV hSU hS hSU' hψS hψSV p q hp hpS hcl hp0

/-- **A4 future from Level B, BTZ points as a hypothesis** (Sbierski Thm 3.6, geometric half):
off the BTZ locus `slice_future_of_cone` (from the field `coneSliceFuture`), at BTZ points
`hB`. -/
theorem sliceFuture_of (hB : 𝔐.SliceFutureBTZ) : 𝔐.SliceFuture := by
  intro M _ _ _ _ s U S hGH hGHU hSU hS hSU' p hp hpS hc O hpO
  by_cases hp0 : p ∈ sing s 0
  · exact hB s U S hGH hGHU hSU hS hSU' p hp hpS hc O hpO hp0
  obtain ⟨cs, hgs⟩ := s
  exact slice_future_of_cone U S hGH hSU hS hSU' p hp hpS hc O hpO hp0

variable (𝔐) in
/-- **A4 past from Level B, proved** (no time reversal, gx D-12(e)): `slice_past_of_cone`, from the
field `coneSlicePast`, at every boundary point, BTZ included (every point is in `Z⁺`). -/
theorem slicePast : 𝔐.SlicePast := by
  intro M _ _ _ _ s U S hGH _hGHU hSU hS hSU' p hp hpS hc O hpO
  obtain ⟨cs, hgs⟩ := s
  exact slice_past_of_cone U S hGH hSU hS hSU' p hp hpS hc O hpO

end TLocalModel
namespace TGeometry

/-- **Level B ⇒ Level A, the BTZ cases as explicit hypotheses** (design §2, interface round 4):
every field of `Geometry` is derived from the local model (`ofLocalModelOfGermSlice`, with A3 by
`germExtFuture_of`/`germExtPast_of`, A4 by `sliceFuture_of`/`slicePast`), except the three
BTZ-point residuals `hA3f : 𝔐.GermExtFutureBTZ`, `hA3p : 𝔐.GermExtPastBTZ`,
`hA4f : 𝔐.SliceFutureBTZ` (A3 future / past and A4 future at boundary points of the BTZ locus;
A4 past has none). Replaces the sorried `Geometry.ofLocalModel` (deleted 2026-11-02). -/
noncomputable def ofLocalModelOfBTZ (𝔐 : TLocalModel.{u}) (hA3f : 𝔐.GermExtFutureBTZ)
    (hA3p : 𝔐.GermExtPastBTZ) (hA4f : 𝔐.SliceFutureBTZ) : Causal.CBG.Geometry.{u} :=
  ofLocalModelOfGermSlice 𝔐 (TLocalModel.germExtFuture_of hA3f) (TLocalModel.germExtPast_of hA3p)
    (TLocalModel.sliceFuture_of hA4f) (TLocalModel.slicePast 𝔐)

@[simp] theorem ofLocalModelOfBTZ_toPreGeometry (𝔐 : TLocalModel.{u}) (hA3f : 𝔐.GermExtFutureBTZ)
    (hA3p : 𝔐.GermExtPastBTZ) (hA4f : 𝔐.SliceFutureBTZ) :
    (ofLocalModelOfBTZ 𝔐 hA3f hA3p hA4f).toPreGeometry = 𝔐.toPreGeometry := rfl

end TGeometry


end Port

/-! ### §3d The `𝔼₀` local model of the port: `typeAgreement` in its proved convergence form -/

section E0Model

variable
  (hLine : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [SecondCountableTopology M] [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid],
    E0LM.E0GlobalBTZ (Causal.CBG.chartedCausality E0LM.D M) (Causal.CBG.chartedSing e0SingY M 0))
  (hSC : ∀ {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [ChartedSpace E0Y M]
    [HasGroupoid M e0Groupoid], (Causal.CBG.chartedCausality E0LM.D M).GloballyHyperbolic →
    ∀ S : Set M, (Causal.CBG.chartedCausality E0LM.D M).IsCauchySurface S →
    SecondCountableTopology S → SecondCountableTopology M)

/-- **The local model `𝔐E₀` of the port** (`Y = 𝕄 ⊕ 𝔼₀`, `G = e0Groupoid`, causality `E0LM.D`,
`singY = e0SingY`): every field as in `E0LM.e0LocalModelOf`, except `typeAgreement`, which is the
convergence form, **proved** (`E0LM.e0_typeAgreementTendsto`). Parameters: `hLine` (WP-41f's (O2))
and `hSC` (WP-41f's (O4), reduced there to (O4′)) only. -/
noncomputable def e0TLocalModel : TLocalModel.{0} where
  Y := E0Y
  G := e0Groupoid
  causalityY := E0LM.D
  singY := e0SingY
  rigid := e0_rigid
  localUnique_sing := e0_localUnique_sing
  localUnique_sing_adherent := E0LM.e0_localUniqueSingAdherent
  localUnique_reg := e0_localUnique_reg
  regularChart := e0_regularChart
  absolutelyMinimalOn_Y := E0.absolutelyMinimalOn_YBTZ
  chartIso_mem := E0.chartIso_mem_e0Groupoid
  sing_mem := e0_sing_mem
  singularFlatAxioms := fun {M} _ _ _ _ _ _ =>
    E0LM.e0_singularFlatAxioms_of E0.chartIso_mem_e0Groupoid (hLine M)
  curvesExtend := fun {M} _ _ _ _ _ _ hGH => E0LM.e0_curvesExtend hGH
  timeFunction := fun {M} _ _ _ _ _ _ hGH => E0LM.e0_timeFunction hGH
  isCompact_Jplus_inter_Jminus := fun {M} _ _ _ _ _ _ hGH S hS p => by
    have h := E0LM.e0_singularFlatAxioms_of E0.chartIso_mem_e0Groupoid (hLine M)
    obtain ⟨T, hTc, hT⟩ := E0LM.e0_timeFunction hGH
    exact E0LM.sfa_isCompact_Jplus_inter_Jminus h hGH hTc hT hS p
  isCompact_Jminus_inter_Jplus := fun {M} _ _ _ _ _ _ hGH S hS p => by
    have h := E0LM.e0_singularFlatAxioms_of E0.chartIso_mem_e0Groupoid (hLine M)
    obtain ⟨T, hTc, hT⟩ := E0LM.e0_timeFunction hGH
    exact E0LM.sfa_isCompact_Jminus_inter_Jplus h hGH hTc hT hS p
  secondCountable_of_cauchy := hSC
  isOpen_regY := e0_isOpen_regY
  dense_regY := e0_dense_regY
  typeAgreement := E0LM.e0_typeAgreementTendsto
  coneSliceFuture := by
    rw [E0LM.e0SingY_zero]
    exact E0.coneSliceFuture_YBTZ
  coneSlicePast := E0.coneSlicePast_YBTZ

theorem e0TLocalModel_sliceFutureBTZ : (e0TLocalModel hLine hSC).SliceFutureBTZ := by
  intro M _ _ _ _ s U S hGH hGHU hSU hS hSU' p hp hpS hc O hpO hp0
  obtain ⟨cs, hg⟩ := s
  exact @e0_sliceFutureBTZ M _ _ _ _ cs hg U S hGH hGHU hSU hS hSU' p hp hpS hc O hpO hp0

theorem e0TLocalModel_germExtFutureBTZ : (e0TLocalModel hLine hSC).GermExtFutureBTZ := by
  intro M N _ _ _ _ _ _ _ _ s t U ψ S hψ hinj hGM hGN hGU hGV hSU hS hSU' hψS hψSV p q hp hpS
    hcl hp0
  obtain ⟨cs, hgs⟩ := s
  obtain ⟨ct, hgt⟩ := t
  exact @e0_germExtFutureBTZ M N _ _ _ _ _ _ _ _ cs hgs ct hgt U ψ S hψ hinj hGM hGN hGU hGV hSU
    hS hSU' hψS hψSV p q hp hpS hcl hp0

theorem e0TLocalModel_germExtPastBTZ : (e0TLocalModel hLine hSC).GermExtPastBTZ := by
  intro M N _ _ _ _ _ _ _ _ s t U ψ S hψ hinj hGM hGN hGU hGV hSU hS hSU' hψS hψSV p q hp hpS
    hcl hp0
  obtain ⟨cs, hgs⟩ := s
  obtain ⟨ct, hgt⟩ := t
  have h : E0GermExtPastBTZ := e0_germExtPastBTZ_of hLine
  exact @h M N _ _ _ _ _ _ _ _ cs hgs ct hgt U ψ S hψ hinj hGM hGN hGU hGV hSU hS hSU' hψS hψSV
    p q hp hpS hcl hp0

end E0Model

/-! ### §4 The `𝔼₀` geometry and CBG -/

section Geometry

variable
  (hLine : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [SecondCountableTopology M] [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid],
    E0LM.E0GlobalBTZ (Causal.CBG.chartedCausality E0LM.D M) (Causal.CBG.chartedSing e0SingY M 0))
  (hSC : ∀ {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [ChartedSpace E0Y M]
    [HasGroupoid M e0Groupoid], (Causal.CBG.chartedCausality E0LM.D M).GloballyHyperbolic →
    ∀ S : Set M, (Causal.CBG.chartedCausality E0LM.D M).IsCauchySurface S →
    SecondCountableTopology S → SecondCountableTopology M)

/-- **The CBG geometry of `𝔼₀`-manifolds** (a `Causal.CBG.Geometry`): the port's
`TGeometry.ofLocalModelOfBTZ` on `e0TLocalModel`, the three BTZ residuals discharged here
(`e0_germExtFutureBTZ`, `e0_germExtPastBTZ_of hLine`, `e0_sliceFutureBTZ`). Parameters: `hLine`
(O2) and `hSC` (O4) only, both true statements, WP-41f's open obligations. -/
noncomputable def e0Geometry : Causal.CBG.Geometry.{0} :=
  TGeometry.ofLocalModelOfBTZ (e0TLocalModel hLine hSC)
    (e0TLocalModel_germExtFutureBTZ hLine hSC) (e0TLocalModel_germExtPastBTZ hLine hSC)
    (e0TLocalModel_sliceFutureBTZ hLine hSC)

/-- **Why the port**: lean-causal's own route, `Geometry.ofLocalModelOfBTZ` on
`E0LM.e0LocalModelOf hLine hSC hTA`, needs `hTA : E0TypeAgreement E0LM.D`, which is refuted
(`E0LM.e0_not_typeAgreement`, WP-41c's counterexample). Recorded here. -/
theorem e0Geometry_hTA_refuted : ¬ E0TypeAgreement E0LM.D := E0LM.e0_not_typeAgreement

/-- The `𝔼₀` structure of an `𝔼₀`-manifold, as a structure of `e0Geometry`. -/
def e0Str (M₀ : Type) [TopologicalSpace M₀] [ChartedSpace E0Y M₀]
    [HasGroupoid M₀ e0Groupoid] : (e0Geometry hLine hSC).Str M₀ :=
  show Σ' cs : ChartedSpace E0Y M₀, @HasGroupoid E0Y _ M₀ _ cs e0Groupoid from
    ⟨inferInstance, inferInstance⟩

/-- The structures of `e0Geometry` on `M` are exactly the `𝔼₀`-atlases of `M`. -/
theorem e0Geometry_Str (M : Type) [TopologicalSpace M] :
    (e0Geometry hLine hSC).Str M =
      Σ' cs : ChartedSpace E0Y M, @HasGroupoid E0Y _ M _ cs e0Groupoid := rfl

/-- The causality of `e0Geometry` on an `𝔼₀`-manifold is its charted `𝔼₀` causality. -/
theorem e0Geometry_causality (M₀ : Type) [TopologicalSpace M₀] [ChartedSpace E0Y M₀]
    [HasGroupoid M₀ e0Groupoid] :
    (e0Geometry hLine hSC).causality (e0Str hLine hSC M₀) = CE M₀ := rfl

/-- The morphisms of `e0Geometry` are the `e0Groupoid`-morphisms. -/
theorem e0Geometry_isMor {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid] [ChartedSpace E0Y N]
    [HasGroupoid N e0Groupoid] (W : Opens M) (f : M → N) :
    (e0Geometry hLine hSC).IsMor (e0Str hLine hSC M) (e0Str hLine hSC N) W f ↔
      ChartedSpace.LiftPropOn e0Groupoid.IsLocalStructomorphWithinAt f W := Iff.rfl

variable {M₀ : Type} [TopologicalSpace M₀] [T2Space M₀] [ConnectedSpace M₀]
  [SecondCountableTopology M₀] [ChartedSpace E0Y M₀] [HasGroupoid M₀ e0Groupoid]

/-- **CBG for `𝔼₀`-manifolds, universal form** (`Causal.CBG.cbg`; DEC-29, DEC-59). -/
theorem e0_cbg (hGH : (CE M₀).GloballyHyperbolic) {S : Set M₀} (hS : (CE M₀).IsCauchySurface S) :
    ∃ Mbar : Causal.CBG.Dev (e0Geometry hLine hSC).toPreGeometry (e0Str hLine hSC M₀),
      Mbar.IsUniversal :=
  Causal.CBG.cbg (e0Str hLine hSC M₀) hGH hS

/-- **CBG for `𝔼₀`-manifolds, existence of a maximal development** (`Causal.CBG.cbg_isETTMaximal`;
DEC-77(c): Cauchy-maximal is `Dev.IsETTMaximal` among `𝔼₀`-manifolds). -/
theorem e0_cbg_isETTMaximal (hGH : (CE M₀).GloballyHyperbolic) {S : Set M₀}
    (hS : (CE M₀).IsCauchySurface S) :
    ∃ Mbar : Causal.CBG.Dev (e0Geometry hLine hSC).toPreGeometry (e0Str hLine hSC M₀),
      Mbar.IsETTMaximal :=
  Causal.CBG.cbg_isETTMaximal (e0Str hLine hSC M₀) hGH hS

/-- **CBG for `𝔼₀`-manifolds, existence and uniqueness** (`Causal.CBG.cbg_ett`): a maximal
Cauchy development exists, and every maximal one is isomorphic to it by a unique isomorphism. -/
theorem e0_cbg_ett (hGH : (CE M₀).GloballyHyperbolic) {S : Set M₀}
    (hS : (CE M₀).IsCauchySurface S) :
    ∃ Mbar : Causal.CBG.Dev (e0Geometry hLine hSC).toPreGeometry (e0Str hLine hSC M₀),
      Mbar.IsETTMaximal ∧
      ∀ M : Causal.CBG.Dev (e0Geometry hLine hSC).toPreGeometry (e0Str hLine hSC M₀),
        M.IsETTMaximal → ∃! f : Mbar.carrier → M.carrier, Mbar.IsMorphism M f ∧
          ∃ g : M.carrier → Mbar.carrier, M.IsMorphism Mbar g ∧ g ∘ f = id ∧ f ∘ g = id :=
  Causal.CBG.cbg_ett (e0Str hLine hSC M₀) hGH hS

end Geometry

end E0CBG

end GX
