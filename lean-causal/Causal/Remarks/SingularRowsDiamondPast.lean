import Causal.Remarks.SingularRowsDiamond

/-!
# `J⁺` of open sets is open, and the time-reversed diamond `J⁻(Σ) ∩ J⁺(p)` is compact, at every `E_{≥0}`-manifold

Target `T-ett-diamant-past`. Cited, unmarked (SCOPE): `theo:CBG` — `ETT.tex:1884`, of which
this is an input of the `E₀` instance (A2's time-reversed compactness field), not a certificate.

For a singular `(Isom(𝐌³), 𝐌³)`-manifold `M` (DEC-25) and every absolutely minimal causality `C`
with an isomorphic chart at each point over the family `E_{≥0}` (`IsoChartsCoverDEC25 …
massAModelCausality`; the natural causality is one), `J⁺(W)` is open for every open `W`, BTZ
points included, and, `M` globally hyperbolic, Hausdorff and second countable, `J⁻(Σ) ∩ J⁺(p)`
is compact for every Cauchy surface `Σ` and every `p`: the field `isCompact_Jminus_inter_Jplus`
of `Causal.CBG.Geometry` (« A2, time-reversed form (no duality) »).

> Let $M_0$ be a globally hyperbolic singular flat spacetime. Then $M_0$ admits a maximal Cauchy
> extension, and that extension is unique up to isomorphism.
> (`theo:CBG`, `ETT.tex:1885–1886`)

## What is proved (no `sorry` in this file)

* **Openness of `J⁺` of open sets** (model-free): `Causality.isOpen_Jplus_of_singularPastAt`, from
  push-up, `Z⁻` off a set `S₀`, and `SingularPastAt` and `Iplus_of_lt` on `S₀`. Its three local
  cases are `Jplus_mem_nhds_of_singularPastAt` (`x ∈ S₀`), `Jplus_mem_nhds_of_mem_Zminus`
  (`w ∉ S₀`) and `Jplus_mem_nhds_of_Iplus_of_lt` (`x ∉ S₀`, `w ∈ S₀`). Hence
  `SingularFlatAxioms.isOpen_Jplus`, with no causality asked.
* **Compactness of `J⁺(p) ∩ Σ` and `J⁻(Σ) ∩ J⁺(p)`**, for every Cauchy surface `Σ` and every `p`:
  `SingularFlatAxioms.isCompact_Jplus_inter_of_isCauchySurface` and
  `SingularFlatAxioms.isCompact_Jminus_inter_Jplus` (globally hyperbolic, `τ` a hypothesis),
  `…_of_modelMeasures`.
* **At `M`**: `SingularRowsDiamondPast.isOpen_Jplus` and `isOpen_Jminus` at every
  `E_{≥0}`-manifold (no Hausdorff, no countability, no causality); `isCompact_Jplus_inter`,
  `isCompact_Jminus_inter_Jplus` at every globally hyperbolic, Hausdorff, second countable one,
  with no hypothesis left; the natural-causality forms `…_of_isAtlasCausalityDEC25`.
* A BTZ point below every Cauchy surface: `SingularFlatAxioms.exists_mem_sing_zero_Jminus_diff`,
  at `M` `exists_btz_Jminus_diff`, with a BTZ point `x ∈ Σ` above it (`p ≤ x`, `p ≠ x`).
* **Witnesses** (kb/0011), each conclusion out of the `M`-level theorems: `nonvacuous_e0` (`E₀`,
  a Cauchy surface `S`, a BTZ point `p ∈ J⁻(S) ∖ S` with `I⁻(p) = ∅`, `J⁻(S) ∩ J⁺(p)` compact,
  and the BTZ point `x ∈ S` above `p`, with `I⁻(x) = ∅`, where `J⁺(W)` is a neighbourhood of `x`
  for every open `W ∋ p`, `x ∉ W` allowed: case (2) of the openness); `nonvacuous_e0_natural`.

## Hypothesis checklist

| A2's field (`Causal/CBG/Geometry.lean:329`) | here |
|---|---|
| an admissible spacetime of the geometry: a singular flat spacetime, `E_{≥0}`-manifold | ⚠ read (DEC-25, OQ-18): `[SingularGXStructure (Flat.isom 2) (Minkowski 2) M]`, `C` absolutely minimal with `IsoChartsCoverDEC25` over `massAModelCausality`; the natural causality in `…_of_isAtlasCausalityDEC25` |
| Hausdorff, second countable (« manifold », `ETT.tex:254`) | ✓ carried for the compactness; ⚠ weakened for the openness: not used |
| connected (the field's `[ConnectedSpace M]`, l.1502) | ⚠ weakened: not used |
| globally hyperbolic, `Σ` a Cauchy surface (DEC-14), every `p` | ✓ carried |
| `C` causal (the target's (ii) for the openness) | ⚠ weakened: not used |
| `E₀`, `Isom(E^{1,2})` | ⚠ read: `Causal.E0` (OQ-34, OQ-35), `Flat.isom 2` (OQ-82) |

## SCOPE (disclosed)

* **Why unmarked.** `theo:CBG` is named because the time-reversed compactness is an input of the
  `E₀` instance of its geometry (T-ett-cbg-e0); this file certifies no row of the paper, whose text
  does not state `J⁻(Σ) ∩ J⁺(p)` compact. Every theorem at `M` rests on DEC-25 and the readings
  OQ-18, OQ-34/OQ-35 and OQ-82.
* **The openness of `J⁺(W)`** is not the dual of `Causality.isOpen_Jminus_of_pushUp`, which would
  need `Z⁻ = M` and that fails at a BTZ point (`mem_Zminus_iff`). For `w ∈ W`, `w ≤ x`: if `x = w`,
  `W` is a neighbourhood; if `x ∈ S₀`, `SingularPastAt x` at `w` gives `u` with `w ≤ u 0` and
  `x ∈ Int J⁺(u 0)`; if `w ∉ S₀`, some `v ≪ w` lies in `W` and push-up gives `x ∈ I⁺(v)`; if
  `x ∉ S₀` and `w ∈ S₀`, the sequence `u n → w`, `u n ≤ w`, `u n ≠ w` of `SingularPastAt w` enters
  `W`, and either `u n ∈ S₀`, where `Iplus_of_lt` gives `x ∈ I⁺(u n)`, or `u n ∉ S₀` and the
  previous case applies at `u n`. The last case uses this sequence, not the BTZ line of the
  planner's route: no closed embedding, hence no causality. Openness « at `⊤` » only: DEC-8's
  causal openness asks it in every open `U` and is not attempted.
* **The compactness** is `Causal.Flat.CBGCompact`'s Zorn on time graphs in its past form
  (`GloballyHyperbolic.isCompact_Jplus_inter_of_isCauchySurface`) with the openness above, `Σ`
  acausal, `J^±(Σ)` closed (`SingularFlatAxioms.sigma_separe`) and the Geroch time `τ`
  (`SingularRowsGeroch.geroch_sing_i_imp_ii`), then `CBG.isCompact_Jminus_inter_Jplus_of_isCompact`.
* `Causal.Remarks.SingularRowsDiamond`'s SCOPE sentence on the time-reversed form (l.79–82) is
  answered here and is not edited.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Imports
`Causal.Remarks.SingularRowsDiamond` (through it `Causal.Flat.CBG`, `Causal.Flat.CBGCompact`,
`Causal.Remarks.SingularRowsCauchy`, `Causal.Remarks.SingularRowsGeroch`, `Causal.Port.SFABTZ`).
-/

namespace Causal

open Set Filter Topology TopologicalSpace Function

universe u

namespace Causality

section General

variable {M : Type u} [TopologicalSpace M] {C : Causality M}

/-- **Case `w ∉ S₀`**: if `w ∈ W` is strongly tarentin in the past and `w ≤ x`, then `J⁺(W)` is a
neighbourhood of `x` (push-up). -/
theorem Jplus_mem_nhds_of_mem_Zminus (hP : C.PushUp) {W : Set M} (hW : IsOpen W) {w x : M}
    (hw : w ∈ W) (hwZ : w ∈ C.Zminus) (hwx : C.le ⊤ w x) : C.Jplus ⊤ W ∈ 𝓝 x := by
  obtain ⟨v, hvI, hvW⟩ := hwZ W (hW.mem_nhds hw)
  have hvw : C.lt ⊤ v w := Precausality.mem_Iminus_singleton.1 hvI
  have hx : x ∈ C.Iplus ⊤ {v} :=
    (hP ⊤ v).1.1 ⟨w, Precausality.mem_Iplus_singleton.2 hvw, hwx⟩
  exact Filter.mem_of_superset (C.isOpen_Iplus.mem_nhds hx) fun y hy =>
    ⟨v, hvW, C.le_of_lt (Precausality.mem_Iplus_singleton.1 hy)⟩

/-- **Case `x ∈ S₀`**: if `SingularPastAt x` and `w ∈ W`, `w ≤ x`, `w ≠ x`, then `J⁺(W)` is a
neighbourhood of `x`. Nothing is asked of `w`, nor of `W`. -/
theorem Jplus_mem_nhds_of_singularPastAt {W : Set M} {w x : M} (hw : w ∈ W)
    (hx : C.SingularPastAt x) (hwx : C.le ⊤ w x) (hne : w ≠ x) : C.Jplus ⊤ W ∈ 𝓝 x := by
  obtain ⟨u, -, -, hint, hw0⟩ := hx.2 w hwx hne
  have hwu : C.le ⊤ w (u 0) := Precausality.mem_Jminus_singleton.1 (interiorWithin_subset hw0)
  exact Filter.mem_of_superset (mem_interior_iff_mem_nhds.1 (hint 0)) fun y hy =>
    ⟨w, hw, C.le_trans hwu (Precausality.mem_Jplus_singleton.1 hy)⟩

/-- **Case `x ∉ S₀`, `w ∈ S₀`**: with push-up, `Z⁻` off `S₀` and `Iplus_of_lt` on `S₀`, if
`SingularPastAt w`, `w ∈ W ∩ S₀`, `w ≤ x` and `x ∉ S₀`, then `J⁺(W)` is a neighbourhood of `x`. -/
theorem Jplus_mem_nhds_of_Iplus_of_lt (hP : C.PushUp) {S₀ : Set M}
    (hZ : ∀ p ∉ S₀, p ∈ C.Zminus)
    (hlt : ∀ p ∈ S₀, ∀ p' ∈ S₀, C.le ⊤ p p' → p ≠ p' → C.Jplus ⊤ {p'} \ S₀ ⊆ C.Iplus ⊤ {p})
    {W : Set M} (hW : IsOpen W) {w x : M} (hwW : w ∈ W) (hw0 : w ∈ S₀)
    (hw : C.SingularPastAt w) (hwx : C.le ⊤ w x) (hx0 : x ∉ S₀) : C.Jplus ⊤ W ∈ 𝓝 x := by
  obtain ⟨⟨u, hu, hup⟩, -⟩ := hw
  obtain ⟨n, hn⟩ := (hu.eventually (hW.mem_nhds hwW)).exists
  by_cases hn0 : u n ∈ S₀
  · have hx : x ∈ C.Iplus ⊤ {u n} :=
      hlt (u n) hn0 w hw0 (hup n).1 (hup n).2 ⟨Precausality.mem_Jplus_singleton.2 hwx, hx0⟩
    exact Filter.mem_of_superset (C.isOpen_Iplus.mem_nhds hx) fun y hy =>
      ⟨u n, hn, C.le_of_lt (Precausality.mem_Iplus_singleton.1 hy)⟩
  · exact Jplus_mem_nhds_of_mem_Zminus hP hW hn (hZ _ hn0) (C.le_trans (hup n).1 hwx)

/-- **Openness of `J⁺(W)` for every open `W`** in a spacetime with push-up whose points off `S₀` are
strongly tarentin in the past, and at whose points of `S₀` the past is a BTZ half-line
(`SingularPastAt`) with `Iplus_of_lt`. -/
theorem isOpen_Jplus_of_singularPastAt (hP : C.PushUp) {S₀ : Set M}
    (hZ : ∀ p ∉ S₀, p ∈ C.Zminus) (hS : ∀ p ∈ S₀, C.SingularPastAt p)
    (hlt : ∀ p ∈ S₀, ∀ p' ∈ S₀, C.le ⊤ p p' → p ≠ p' → C.Jplus ⊤ {p'} \ S₀ ⊆ C.Iplus ⊤ {p})
    {W : Set M} (hW : IsOpen W) : IsOpen (C.Jplus ⊤ W) := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨w, hwW, hwx⟩
  by_cases hxw : w = x
  · subst hxw
    exact Filter.mem_of_superset (hW.mem_nhds hwW) (C.subset_Jplus fun _ _ => trivial)
  by_cases hx0 : x ∈ S₀
  · exact Jplus_mem_nhds_of_singularPastAt hwW (hS x hx0) hwx hxw
  by_cases hw0 : w ∈ S₀
  · exact Jplus_mem_nhds_of_Iplus_of_lt hP hZ hlt hW hwW hw0 (hS w hw0) hwx hx0
  · exact Jplus_mem_nhds_of_mem_Zminus hP hW hwW (hZ w hw0) hwx

end General

section SFA

variable {M : Type u} [TopologicalSpace M] {C : Causality M} {sing : ℝ → Set M}

/-- Under `SingularFlatAxioms`, **openness of `J⁺(W)` for every open `W`**, BTZ points included, with
no causality asked. -/
theorem SingularFlatAxioms.isOpen_Jplus (h : C.SingularFlatAxioms sing) {W : Set M}
    (hW : IsOpen W) : IsOpen (C.Jplus ⊤ W) :=
  isOpen_Jplus_of_singularPastAt h.pushUp (fun p hp => (h.mem_Zminus_iff p).2 hp)
    h.singularPastAt h.Iplus_of_lt hW

/-- `J⁺(p) ∩ S` is compact for a Cauchy surface `S` of a globally hyperbolic `SingularFlatAxioms`
spacetime with a continuous `τ` strictly increasing along `≤`. -/
theorem SingularFlatAxioms.isCompact_Jplus_inter_of_isCauchySurface
    (h : C.SingularFlatAxioms sing) (hG : C.GloballyHyperbolic) {τ : M → ℝ} (hτc : Continuous τ)
    (hτ : ∀ x y, C.le ⊤ x y → x ≠ y → τ x < τ y) {S : Set M} (hS : C.IsCauchySurface S)
    (p : M) : IsCompact (C.Jplus ⊤ {p} ∩ S) := by
  haveI := h.t2
  haveI := h.secondCountable
  haveI := h.locallyCompact
  obtain ⟨h1, h2, -, -⟩ := h.sigma_separe hG hS
  exact GloballyHyperbolic.isCompact_Jplus_inter_of_isCauchySurface h.tarentin hG
    h.causallyArcConnected hτc hτ (fun _ hW => h.isOpen_Jplus hW) hS
    (hS.isAcausal_of_t1_secondCountable h.causallyArcConnected) h1 h2 p

/-- **Compactness of `J⁻(S) ∩ J⁺(p)`** for a Cauchy surface `S` of a globally hyperbolic
`SingularFlatAxioms` spacetime with a continuous `τ` strictly increasing along `≤`. -/
theorem SingularFlatAxioms.isCompact_Jminus_inter_Jplus (h : C.SingularFlatAxioms sing)
    (hG : C.GloballyHyperbolic) {τ : M → ℝ} (hτc : Continuous τ)
    (hτ : ∀ x y, C.le ⊤ x y → x ≠ y → τ x < τ y) {S : Set M} (hS : C.IsCauchySurface S)
    (p : M) : IsCompact (C.Jminus ⊤ S ∩ C.Jplus ⊤ {p}) := by
  haveI := h.t2
  exact CBG.isCompact_Jminus_inter_Jplus_of_isCompact h.tarentin hG (h.sigma_separe hG hS).2.1
    (h.isCompact_Jplus_inter_of_isCauchySurface hG hτc hτ hS p)

/-- The same, with `τ` out of the model measures (`SingularFlatAxioms.geroch_sing_i_imp_ii`). -/
theorem SingularFlatAxioms.isCompact_Jminus_inter_Jplus_of_modelMeasures [MeasurableSpace M]
    [BorelSpace M] (h : C.SingularFlatAxioms sing) (hM : C.ModelMeasures)
    (hG : C.GloballyHyperbolic) {S : Set M} (hS : C.IsCauchySurface S) (p : M) :
    IsCompact (C.Jminus ⊤ S ∩ C.Jplus ⊤ {p}) := by
  obtain ⟨T, hT, hTs⟩ := h.geroch_sing_i_imp_ii hM hG
  exact h.isCompact_Jminus_inter_Jplus hG hT.1.continuous hTs hS p

/-- A BTZ point `p` in `J⁻(S) ∖ S`, with a BTZ point `x ∈ S` above it (`p ≤ x`, `p ≠ x`). The proof
takes them on one BTZ line, which meets `S` once, but the statement does not say so. -/
theorem SingularFlatAxioms.exists_mem_sing_zero_Jminus_diff (h : C.SingularFlatAxioms sing)
    (hc : C.IsCausal) {S : Set M} (hS : C.IsCauchySurface S) (hne : (sing 0).Nonempty) :
    ∃ p ∈ sing 0, p ∈ C.Jminus ⊤ S \ S ∧ ∃ x ∈ sing 0 ∩ S, C.le ⊤ p x ∧ p ≠ x := by
  obtain ⟨q, hq0⟩ := hne
  obtain ⟨γ, -, hγe, hγi, hγr⟩ := h.line q hq0
  have hγe' := hγe hc
  obtain ⟨σ, ⟨⟨s₀, -, rfl⟩, hσS⟩, huniq⟩ := hS univ γ hγi
  have hmem : ∀ t, γ t ∈ sing 0 := fun t => by
    have hr : γ t ∈ range γ := ⟨t, rfl⟩
    rw [hγr] at hr
    exact connectedComponentIn_subset _ _ hr
  have hle : C.le ⊤ (γ (s₀ - 1)) (γ s₀) := hγi.1.le_of_le trivial trivial (by linarith)
  have hne' : γ (s₀ - 1) ≠ γ s₀ := fun heq => by
    have := hγe'.injective heq
    linarith
  refine ⟨γ (s₀ - 1), hmem _, ⟨⟨γ s₀, hσS, hle⟩, fun hS1 => hne' ?_⟩, γ s₀, ⟨hmem _, hσS⟩,
    hle, hne'⟩
  exact huniq _ ⟨⟨s₀ - 1, trivial, rfl⟩, hS1⟩

end SFA

end Causality

namespace SingularRowsDiamondPast

section Manifold

variable {M : Type u} [TopologicalSpace M] [SingularGXStructure (Flat.isom 2) (Minkowski 2) M]
  {C : Causality M}

/-- **Openness of `J⁺(W)` for every open `W`** at every `E_{≥0}`-manifold, BTZ points included: no
Hausdorff, no countability, no causality. -/
theorem isOpen_Jplus (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) {W : Set M}
    (hW : IsOpen W) : IsOpen (C.Jplus ⊤ W) :=
  Causality.isOpen_Jplus_of_singularPastAt (SFALocal.pushUp hmin hC)
    (fun _ hp => SFALocal.mem_Zminus_of_notMem hC hp) (SFABTZ.singularPastAt hmin hC)
    (SFABTZ.Iplus_of_lt hmin hC) hW

/-- **Openness of `J⁻(W)` for every open `W`** at every `E_{≥0}`-manifold (push-up and `Z⁺ = M`). -/
theorem isOpen_Jminus (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) {W : Set M}
    (hW : IsOpen W) : IsOpen (C.Jminus ⊤ W) :=
  Causality.isOpen_Jminus_of_pushUp (SFALocal.pushUp hmin hC) (SFALocal.mem_Zplus hC) hW

/-- `J⁺(p) ∩ S` is compact at every globally hyperbolic, Hausdorff, second countable
`E_{≥0}`-manifold, for every Cauchy surface `S` and every `p`. -/
theorem isCompact_Jplus_inter [T2Space M] [SecondCountableTopology M]
    (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hG : C.GloballyHyperbolic) {S : Set M} (hS : C.IsCauchySurface S) (p : M) :
    IsCompact (C.Jplus ⊤ {p} ∩ S) := by
  obtain ⟨T, hT, hTs⟩ := SingularRowsGeroch.geroch_sing_i_imp_ii hmin hC hG
  exact (SFAManifolds.singularFlatAxioms hmin hC).isCompact_Jplus_inter_of_isCauchySurface hG
    hT.1.continuous hTs hS p

/-- **Compactness of `J⁻(S) ∩ J⁺(p)`** at every globally hyperbolic, Hausdorff, second countable
`E_{≥0}`-manifold, for every Cauchy surface `S` and every `p`: A2's time-reversed field. -/
theorem isCompact_Jminus_inter_Jplus [T2Space M] [SecondCountableTopology M]
    (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hG : C.GloballyHyperbolic) {S : Set M} (hS : C.IsCauchySurface S) (p : M) :
    IsCompact (C.Jminus ⊤ S ∩ C.Jplus ⊤ {p}) := by
  obtain ⟨T, hT, hTs⟩ := SingularRowsGeroch.geroch_sing_i_imp_ii hmin hC hG
  exact (SFAManifolds.singularFlatAxioms hmin hC).isCompact_Jminus_inter_Jplus hG
    hT.1.continuous hTs hS p

/-- A BTZ point in `J⁻(S) ∖ S`, with the BTZ point of `S` above it. -/
theorem exists_btz_Jminus_diff [T2Space M] [SecondCountableTopology M]
    (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hc : C.IsCausal) {S : Set M} (hS : C.IsCauchySurface S)
    (hne : (SFALocal.sing M 0).Nonempty) :
    ∃ p ∈ SFALocal.sing M 0, p ∈ C.Jminus ⊤ S \ S ∧
      ∃ x ∈ SFALocal.sing M 0 ∩ S, C.le ⊤ p x ∧ p ≠ x :=
  (SFAManifolds.singularFlatAxioms hmin hC).exists_mem_sing_zero_Jminus_diff hc hS hne

/-! ### The natural causality -/

/-- `J^±(W)` open for every open `W`, for the natural causality. -/
theorem isOpen_Jplus_Jminus_of_isAtlasCausalityDEC25 (hcov : SFALocal.MassACovered M)
    (hCM : IsAtlasCausalityDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) {W : Set M}
    (hW : IsOpen W) : IsOpen (C.Jplus ⊤ W) ∧ IsOpen (C.Jminus ⊤ W) := by
  obtain ⟨hmin, hC⟩ := SFALocal.of_isAtlasCausalityDEC25 hcov hCM
  exact ⟨isOpen_Jplus hmin hC hW, isOpen_Jminus hmin hC hW⟩

/-- The compactness of `J⁻(S) ∩ J⁺(p)` for the natural causality of a globally hyperbolic `M`. -/
theorem isCompact_Jminus_inter_Jplus_of_isAtlasCausalityDEC25 [T2Space M]
    [SecondCountableTopology M] (hcov : SFALocal.MassACovered M)
    (hCM : IsAtlasCausalityDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hG : C.GloballyHyperbolic) {S : Set M} (hS : C.IsCauchySurface S) (p : M) :
    IsCompact (C.Jminus ⊤ S ∩ C.Jplus ⊤ {p}) := by
  obtain ⟨hmin, hC⟩ := SFALocal.of_isAtlasCausalityDEC25 hcov hCM
  exact isCompact_Jminus_inter_Jplus hmin hC hG hS p

end Manifold

/-! ### Witnesses (kb/0011) -/

section WitnessE0

attribute [local instance] E0GX.singularGX

/-- **Non-vacuity at `E₀`**, out of this file's `M`-level theorems: `J^±` of open sets open; a
Cauchy surface `S` and a BTZ point `p ∈ J⁻(S) ∖ S` with `I⁻(p) = ∅`, where `J⁺(p) ∩ S` and
`J⁻(S) ∩ J⁺(p)` are compact; and the BTZ point `x ∈ S` above `p`, with `I⁻(x) = ∅`, at which
`J⁺(W)` is a neighbourhood for every open `W ∋ p`, some such `W` missing `x`. As `x` is in no
`I⁺(v)`, that neighbourhood is case (2) of the openness (`Jplus_mem_nhds_of_singularPastAt`). -/
theorem nonvacuous_e0 :
    (∀ W : Set E0, IsOpen W → IsOpen (E0.causality.Jplus ⊤ W)) ∧
      (∀ W : Set E0, IsOpen W → IsOpen (E0.causality.Jminus ⊤ W)) ∧
      ∃ S : Set E0, E0.causality.IsCauchySurface S ∧
        ∃ p ∈ SFALocal.sing E0 0, p ∈ E0.causality.Jminus ⊤ S \ S ∧
          E0.causality.Iminus ⊤ {p} = ∅ ∧
          IsCompact (E0.causality.Jplus ⊤ {p} ∩ S) ∧
          IsCompact (E0.causality.Jminus ⊤ S ∩ E0.causality.Jplus ⊤ {p}) ∧
          ∃ x ∈ SFALocal.sing E0 0 ∩ S, E0.causality.le ⊤ p x ∧ p ≠ x ∧
            E0.causality.Iminus ⊤ {x} = ∅ ∧
            (∃ W : Set E0, IsOpen W ∧ p ∈ W ∧ x ∉ W) ∧
            ∀ W : Set E0, IsOpen W → p ∈ W → E0.causality.Jplus ⊤ W ∈ 𝓝 x := by
  obtain ⟨hmin, hC, -, hG, -, -, S, hS⟩ := SingularRowsGeroch.nonvacuous_e0_geroch
  obtain ⟨-, -, -, hne⟩ := SFALocal.nonvacuous_e0
  obtain ⟨p, hp0, hp, x, ⟨hx0, hxS⟩, hpx, hne'⟩ := exists_btz_Jminus_diff hmin hC hG.1 hS hne
  exact ⟨fun _ hW => isOpen_Jplus hmin hC hW, fun _ hW => isOpen_Jminus hmin hC hW, S, hS, p,
    hp0, hp, SFALocal.Iminus_eq_empty hmin hC p hp0, isCompact_Jplus_inter hmin hC hG hS p,
    isCompact_Jminus_inter_Jplus hmin hC hG hS p, x, ⟨hx0, hxS⟩, hpx, hne',
    SFALocal.Iminus_eq_empty hmin hC x hx0, ⟨{x}ᶜ, isOpen_compl_singleton, hne', fun h => h rfl⟩,
    fun _ hW hpW => (isOpen_Jplus hmin hC hW).mem_nhds ⟨p, hpW, hpx⟩⟩

/-- **Non-vacuity of the natural forms at `E₀`** (`EModelsBPrime.massA_dec25_models_e0_sing`): a
Cauchy surface out of `SingularRowsGeroch.geroch_sing_i_imp_iii_of_isAtlasCausalityDEC25`, and
the openness and the time-reversed compactness out of the natural-causality theorems. -/
theorem nonvacuous_e0_natural :
    SFALocal.MassACovered E0 ∧
      IsAtlasCausalityDEC25 (Flat.isom 2) E0.causality (minkowski 2) massAModelCausality ∧
      (∀ W : Set E0, IsOpen W →
        IsOpen (E0.causality.Jplus ⊤ W) ∧ IsOpen (E0.causality.Jminus ⊤ W)) ∧
      ∃ S : Set E0, E0.causality.IsCauchySurface S ∧
        ∀ p, IsCompact (E0.causality.Jminus ⊤ S ∩ E0.causality.Jplus ⊤ {p}) := by
  obtain ⟨-, hcov, hC, -⟩ := EModelsBPrime.massA_dec25_models_e0_sing
  obtain ⟨S, hS⟩ := SingularRowsGeroch.geroch_sing_i_imp_iii_of_isAtlasCausalityDEC25 hcov hC
    E0.globallyHyperbolic
  exact ⟨hcov, hC, fun _ hW => isOpen_Jplus_Jminus_of_isAtlasCausalityDEC25 hcov hC hW, S, hS,
    fun p => isCompact_Jminus_inter_Jplus_of_isAtlasCausalityDEC25 hcov hC E0.globallyHyperbolic
      hS p⟩

end WitnessE0

end SingularRowsDiamondPast

end Causal
