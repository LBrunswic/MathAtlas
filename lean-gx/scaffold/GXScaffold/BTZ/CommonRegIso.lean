import GXScaffold.BTZ.CommonReg

/-!
# btz § 5.3: `btzcor:common_reg` when « reg(M) ≃ reg(N) » is an isometry of flat spacetimes

Target `T-btz-common-reg-iso` (`roadmap/roadmap.toml`). `papers/btz/legacy/labeled/BTZ_1.tex`.
The row is not marked: the inputs and the hypotheses are those of `GX.BTZCommonReg.common_reg`
(`𝔼₀` only, T-btz-scope; `M`, `N` connected added, OQ-150 (b)), and OQ-152 (a) is open.

* `btzcor:common_reg` — `BTZ_1.tex:1274` (proof l.1277–1279) —
  `GX.BTZCommonRegIso.common_reg_of_isometry` (the corollary when `reg(M) ≃ reg(N)` is a
  surjective isometric embedding `e0RegMFlat M → e0RegMFlat N` of the flat spacetimes) and
  `GX.BTZCommonRegIso.common_reg_either` (the corollary under either reading of OQ-152 (a), as a
  disjunction of the two hypotheses). The bridge is
  `GX.BTZCommonRegIso.isE0Mor_of_isIsometricEmbedding` (an isometric embedding of the regular parts
  is an `𝔼₀`-morphism of the regular open sets), built on `GX.E0AbsMax.isE0Mor_regExt` and
  `GX.BTZCommonRegIso.isE0Mor_flatE0Val` (the `𝔼₀`-structure of `FlatE0 (e0RegMFlat N)` is that of
  the open set `E0LM.e0RegM N ⊆ N`; `GX.BTZCommonRegIso.isE0Mor_toFlatE0` is the converse).

> Let $M,N$ be globally hyperbolic Cauchy-maximal Cauchy-compact $\mass{0}$-manifolds:
> $$\reg(M)\simeq \reg(N) \quad \Rightarrow{} \quad M\simeq N.$$ (l.1274–1276)

## Hypothesis checklist (`common_reg_of_isometry`)

| paper hypothesis | here |
|---|---|
| `M`, `N` `𝔼₀`-manifolds (Hausdorff, second countable, l.261) | ✓ carried |
| (none) | ⚠ strengthened: `M`, `N` connected (as in `common_reg`, OQ-150 (b), DEC-125 (e)) |
| globally hyperbolic | ✓ carried |
| Cauchy-maximal | ✓ carried (`IsE0CauchyMaximal`) |
| Cauchy-compact | ✓ carried (`E0CauchyCompact`) |
| `reg(M) ≃ reg(N)` | reading: a surjective `Causal.Flat.IsIsometricEmbedding 2` between the flat spacetimes `e0RegMFlat M`, `e0RegMFlat N` (an isometry), OQ-152 (a) |
| conclusion `M ≃ N` | ✓ carried, strengthened: a homeomorphism, `𝔼₀`-morphism both ways, extending the given isometry |

## SCOPE (disclosed)

* **Both readings of OQ-152 (a).** `GX.BTZCommonReg.common_reg` (read-only here) takes a
  bijective `𝔼₀`-morphism of the regular open sets; `common_reg_of_isometry` takes an isometry of
  the flat spacetimes; `common_reg_either` takes either. Which is the formalization of record is
  the author's ruling, not decided here.
* **One direction of the bridge.** Isometry ⇒ `𝔼₀`-morphism is proved here; the converse
  (`𝔼₀`-morphism ⇒ isometry) is T-btz-cauchy-easy's and is not used.
* `𝔼₀` only, and no `RichardsInput`, as in `common_reg`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; lean-causal as pinned
in `lake-manifest.json`.
-/

namespace GX

open Set Function TopologicalSpace Filter Topology
open E0CBG E0Spear

namespace BTZCommonRegIso

section Bridge

variable {N : Type} [TopologicalSpace N] [T2Space N] [ConnectedSpace N]
  [ChartedSpace E0Y N] [HasGroupoid N e0Groupoid]

/-- **The `𝔼₀`-structure of `FlatE0 (e0RegMFlat N)` is that of `Reg N ⊆ N`** (one half): the
identity of `Reg N`, read from `FlatE0 (e0RegMFlat N)` into `N`, is an `𝔼₀`-morphism. -/
theorem isE0Mor_flatE0Val :
    IsE0Mor (fun y : E0AbsMax.FlatE0 (e0RegMFlat N) => ((show E0LM.e0RegM N from y) : N)) univ := by
  intro y _
  set y' : E0LM.e0RegM N := y with hy'
  set κ := chartAt E0Y (y' : N) with hκ
  set ρ := E0LM.regAtlasChart y' with hρ
  set C := E0LM.regChartM y' with hC
  set Cs : OpenPartialHomeomorph (E0LM.e0RegM N) (Causal.Minkowski 2) := C.subtypeRestr ⟨y'⟩
    with hCs
  have hy0 : chartAt E0Y y y = Sum.inl (ρ (κ y')) := rfl
  have htgt : ∀ z ∈ (chartAt E0Y y).target, e0Inl.symm z ∈ Cs.target := fun z hz => hz.2
  have hsymm : ∀ z ∈ (chartAt E0Y y).target,
      (((show E0LM.e0RegM N from (chartAt E0Y y).symm z)) : N) = κ.symm (ρ.symm (e0Inl.symm z)) := by
    intro z hz
    exact C.subtypeRestr_symm_apply ⟨y'⟩ (htgt z hz)
  have hCt : ∀ w ∈ Cs.target, ρ.symm w ∈ κ.target := fun w hw =>
    (C.subtypeRestr_target_subset ⟨y'⟩ hw).2
  refine ⟨?_, ?_⟩
  · exact (continuous_subtype_val (p := (· ∈ E0LM.e0RegM N))).continuousWithinAt
  · refine E0AbsMax.isLocalStructomorphWithinAt_of_eventually e0Inl_symm_mem_e0Atlas
      (E0LM.regAtlasChart_mem y') 1 ?_ ?_ ?_
    · rw [hy0, e0Inl_symm_source]; exact ⟨_, rfl⟩
    · rw [hy0, e0Inl_symm_inl, one_smul]
      exact ρ.map_source (E0LM.mem_regAtlasChart_source y')
    · filter_upwards [(chartAt E0Y y).open_target.mem_nhds
        ((chartAt E0Y y).map_source (mem_chart_source E0Y y))] with z hz _
      rw [one_smul]
      show κ (((show E0LM.e0RegM N from (chartAt E0Y y).symm z)) : N) = _
      rw [hsymm z hz, κ.right_inv (hCt _ (htgt z hz))]

/-- The other half: the identity of `Reg N`, read from the open set `E0LM.e0RegM N` into
`FlatE0 (e0RegMFlat N)`, is an `𝔼₀`-morphism. -/
theorem isE0Mor_toFlatE0 :
    IsE0Mor (fun y : E0LM.e0RegM N => (show E0AbsMax.FlatE0 (e0RegMFlat N) from y)) univ := by
  intro y _
  set κ := chartAt E0Y (y : N) with hκ
  set ρ := E0LM.regAtlasChart y with hρ
  have hy0 : chartAt E0Y y y = κ y := rfl
  have hsymm : ∀ z ∈ (chartAt E0Y y).target,
      (((chartAt E0Y y).symm z : E0LM.e0RegM N) : N) = κ.symm z := fun z hz =>
    κ.subtypeRestr_symm_apply ⟨y⟩ hz
  have htgt : ∀ z ∈ (chartAt E0Y y).target, z ∈ κ.target := fun z hz =>
    κ.subtypeRestr_target_subset ⟨y⟩ hz
  refine ⟨continuous_id.continuousWithinAt, ?_⟩
  refine E0AbsMax.isLocalStructomorphWithinAt_of_eventually (E0LM.regAtlasChart_mem y)
    e0Inl_symm_mem_e0Atlas 1 ?_ ?_ ?_
  · rw [hy0]; exact E0LM.mem_regAtlasChart_source y
  · rw [OpenPartialHomeomorph.symm_target, e0Inl_source]; exact mem_univ _
  · filter_upwards [(chartAt E0Y y).open_target.mem_nhds
      ((chartAt E0Y y).map_source (mem_chart_source E0Y y))] with z hz _
    rw [one_smul, OpenPartialHomeomorph.symm_symm]
    show e0Inl (ρ (κ (((chartAt E0Y y).symm z : E0LM.e0RegM N) : N))) = e0Inl (ρ z)
    rw [hsymm z hz, κ.right_inv (htgt z hz)]

end Bridge

section Main

variable {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [SecondCountableTopology M]
  [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]
variable {N : Type} [TopologicalSpace N] [T2Space N] [ConnectedSpace N] [SecondCountableTopology N]
  [ChartedSpace E0Y N] [HasGroupoid N e0Groupoid]

/-- An isometric embedding of the flat spacetimes `Reg M → Reg N`, read on the open sets. -/
def regMap (f : e0RegMFlat M → e0RegMFlat N) : E0LM.e0RegM M → E0LM.e0RegM N :=
  fun x => show E0LM.e0RegM N from f x

omit [SecondCountableTopology M] [SecondCountableTopology N] in
/-- **Isometry ⇒ `𝔼₀`-morphism**: an isometric embedding `e0RegMFlat M → e0RegMFlat N` is an
`𝔼₀`-morphism of the regular open sets `E0LM.e0RegM M → E0LM.e0RegM N`. -/
theorem isE0Mor_of_isIsometricEmbedding {f : e0RegMFlat M → e0RegMFlat N}
    (hf : Causal.Flat.IsIsometricEmbedding 2 f) : IsE0Mor (regMap f) univ := by
  obtain ⟨x₀⟩ : Nonempty (e0RegMFlat M) := inferInstance
  have h1 := E0AbsMax.isE0Mor_regExt hf (f x₀)
  have h2 := Causal.CBG.liftPropOn_comp (E0LM.e0RegM M).isOpen isOpen_univ
    (isE0Mor_flatE0Val (N := N)) h1 (mapsTo_univ _ _)
  have h3 := Causal.CBG.liftPropOn_comp isOpen_univ (E0LM.e0RegM M).isOpen h2
    (isE0Mor_val (E0LM.e0RegM M)) (fun x _ => x.2)
  have h4 : IsE0Mor (Subtype.val ∘ regMap f) univ := by
    refine Causal.CBG.liftPropOn_congr_of_eqOn isOpen_univ h3 fun x _ => ?_
    show ((show E0LM.e0RegM N from E0AbsMax.regExt f (f x₀) x) : N) = ((regMap f x : _) : N)
    rw [E0AbsMax.regExt_apply f (f x₀) x x.2]
    rfl
  exact (isE0Mor_corestrict_iff _ univ).1 h4

/-- **`btzcor:common_reg`, isometry reading** (unmarked; OQ-152 (a)) (`BTZ_1.tex:1274–1276`):
two globally hyperbolic Cauchy-maximal Cauchy-compact `𝔼₀`-manifolds whose regular parts are
isometric flat spacetimes are isomorphic, by a homeomorphism which is an `𝔼₀`-morphism both ways
and extends the given isometry. -/
theorem common_reg_of_isometry (hGM : (CE M).GloballyHyperbolic) (hGN : (CE N).GloballyHyperbolic)
    (hCM : IsE0CauchyMaximal M) (hCN : IsE0CauchyMaximal N)
    (hKM : E0AbsMax.E0CauchyCompact M) (hKN : E0AbsMax.E0CauchyCompact N)
    (f : e0RegMFlat M → e0RegMFlat N) (hf : Causal.Flat.IsIsometricEmbedding 2 f)
    (hfs : Surjective f) :
    ∃ F : M ≃ₜ N, IsE0Mor F univ ∧ IsE0Mor F.symm univ ∧
      (F : M → N) ∘ Subtype.val = Subtype.val ∘ regMap f := by
  refine BTZCommonReg.common_reg hGM hGN hCM hCN hKM hKN (regMap f)
    (isE0Mor_of_isIsometricEmbedding hf) ⟨fun a b hab => hf.2 hab, fun b => ?_⟩
  obtain ⟨a, ha⟩ := hfs b
  exact ⟨a, ha⟩

/-- **`btzcor:common_reg` under either reading of OQ-152 (a)**: if the regular parts are
isomorphic as `𝔼₀`-manifolds (a bijective `𝔼₀`-morphism of the open sets) **or** as flat
spacetimes (a surjective isometric embedding), then `M ≃ N`. -/
theorem common_reg_either (hGM : (CE M).GloballyHyperbolic) (hGN : (CE N).GloballyHyperbolic)
    (hCM : IsE0CauchyMaximal M) (hCN : IsE0CauchyMaximal N)
    (hKM : E0AbsMax.E0CauchyCompact M) (hKN : E0AbsMax.E0CauchyCompact N)
    (h : (∃ φ : E0LM.e0RegM M → E0LM.e0RegM N, IsE0Mor φ univ ∧ Bijective φ) ∨
      ∃ f : e0RegMFlat M → e0RegMFlat N, Causal.Flat.IsIsometricEmbedding 2 f ∧ Surjective f) :
    ∃ F : M ≃ₜ N, IsE0Mor F univ ∧ IsE0Mor F.symm univ := by
  rcases h with ⟨φ, hφ, hφb⟩ | ⟨f, hf, hfs⟩
  · obtain ⟨F, hF, hF', -⟩ := BTZCommonReg.common_reg hGM hGN hCM hCN hKM hKN φ hφ hφb
    exact ⟨F, hF, hF'⟩
  · obtain ⟨F, hF, hF', -⟩ := common_reg_of_isometry hGM hGN hCM hCN hKM hKN f hf hfs
    exact ⟨F, hF, hF'⟩

end Main

end BTZCommonRegIso

end GX
