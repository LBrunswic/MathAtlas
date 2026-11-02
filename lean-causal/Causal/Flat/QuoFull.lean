import Causal.Flat.Develop
import Causal.Flat.CauchyComplete

/-!
# `Causal.Flat.QuoFull` — Cor 8.2 in full: the embeddings and `π₁(S) ↪ π₁(M)`, from completeness

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §8,
`GHFspace.tex` l.2263–2271 (labelled file).

* **`bcor:quo`** — `GHFspace.tex:2264` (Cor 8.2, l.2263–2271; DEC-105)
  (`bcor_quo_of_isCauchyComplete`, `bcor_quo_of_isCauchyComplete'`): every clause, from the
  paper's Cauchy-completeness — (CC′) obtained from completeness through the bridge (DEC-35;
  Prop 8.1 / Cor 8.3, `developsCC_of_isCauchyComplete`, glued by
  `developsCC_of_isCauchyComplete_of_isDevelopingPair`), so `𝒟` injective on `S̃` is proved,
  not assumed; M connected implicit (in "spacetime", `FlatSpacetime`; Hausdorff in "manifold",
  DEC-90); f = inclusion of S ⊆ M (disclosed); `M` GH and `S` a Cauchy surface, the DEC-35
  reading of the paper's complete hypersurface (checklist, SCOPE).
  > The maps $f$ and ${\mathcal D} \circ \tilde{f}$ are embeddings. The natural morphism
  > $\Gamma \subset \pi_{1}(M)$ and the morphism $\rho$ are injective. Moreover,
  > ${\mathcal D} \circ \tilde{f}(\widetilde{S})$ intersects every timelike geodesic.

The set-up it rests on (l.2215–2223):

> an isometric immersion $f: S \rightarrow M$ of a \emph{complete} riemannian hypersurface. Let
> $\widetilde{M}$ be the universal covering of $M$, ${\mathcal D}: \widetilde{M} \rightarrow
> {\bf M}^{n}$ the developping map, $\Gamma$ the fundamental group of $S$, and
> $\tilde{f}: \widetilde{S} \rightarrow \widetilde{M}$ a lifting of $f$.

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; `Minkowski d` has `d` spatial
dimensions: Barbot's `n` is `d + 1`.

## Main declarations

* `bcor_quo_of_isCauchyComplete` — **the principal theorem** (DEC-105): `M : FlatSpacetime`, GH,
  `S` a Cauchy surface complete for its induced length (the fields of `IsCauchyComplete`), any
  developing pair; every clause of Cor 8.2. `bcor_quo_of_isCauchyComplete'` — from
  `IsCauchyComplete d M`: some Cauchy surface satisfies them for every developing pair.
* `developsCC_of_isCauchyComplete_of_isDevelopingPair` — the glue: the bridge's conjunction is
  `DevelopsCC` (no normalisation of the pair or base point needed: the bridge takes any `dev`
  that is a `(G,X)`-morphism of the universal cover at any `x₀`, `IsDevelopingPair.gx`).
* `bcor_quo_full`, `bcor_quo_full_of_connected` — every clause from `DevelopsCC` (relative form,
  kept: `DevelopsCC.injOn` a hypothesis there).
* `graphHomeomorph`, `isEmbedding_develop_liftSet`, `contractibleSpace_liftSet` (`S̃ ≅ Σ ≅ ℝᵈ`),
  `injective_pathQuotient_map_val_of_preimage`, `injective_fundamentalGroup_map_val`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `S` a complete Riemannian hypersurface (l.2215–2216) | ✓ carried in the DEC-35 reading of completeness (DEC-105): `IsSpacelikeLipschitz d S` (⚠ weakened: Lipschitz in flat charts, not smooth), `CompleteSpace (InducedLengthSpace d S)`, the topology field (W3) — the fields of `IsCauchyComplete` |
| `M` a flat spacetime; `S` a Cauchy surface, `M` GH | ⚠ strengthened (DEC-35/DEC-105 reading: the paper's "Cauchy-complete", l.551): §8 does not ask `S` Cauchy; `GH M` is used only for `S̃` connected (B1) |
| `f` an isometric immersion; `f̃` a lifting | ✓ in the reading: f = inclusion of S ⊆ M (disclosed), `S̃ := p⁻¹(S)`, `f̃` its inclusion |
| "`𝒟 ∘ f̃` is an embedding": its injectivity (Prop 8.1) | ✓ proved through the bridge (DEC-35) in `bcor_quo_of_isCauchyComplete`; assumed (`DevelopsCC.injOn`) only in the relative `bcor_quo_full` |
| `Γ = π₁(S)`, "the natural morphism `Γ ⊂ π₁(M)`" | ✓ `FundamentalGroup.map` of the inclusion at every `s ∈ S` |
| (implicit) `M` Hausdorff and connected (manifold, spacetime) | ✓ carried by `FlatSpacetime` (T2 as DEC-90; connected implicit in "spacetime", DEC-105) |
| "timelike geodesic" | ✓ the timelike affine lines `p + ℝ v`, `v` future timelike (as in `bcor_quo`) |

## SCOPE (disclosed)

* **Reading.** DEC-35/DEC-105: the paper's immersed complete hypersurface is a Cauchy surface of
  a GH `M` complete for its induced length; "`f` is an embedding" is then the subspace inclusion
  (`IsEmbedding.subtypeVal`), not the paper's claim that an isometric immersion of a complete
  hypersurface is injective and proper. The immersion form is not formalized: the library has no
  immersed hypersurfaces.
* **(CC′) from completeness.** In `bcor_quo_of_isCauchyComplete` the injectivity of `𝒟` on `S̃`
  (hence the embedding, the contractibility of `S̃`, the `π₁` clause, `ρ` injective and `ρ(Γ)`
  free on `Σ`) rests on the proved bridge (Prop 8.1, `[8.G]`, Cor 8.3, B1–B3 of
  `Flat/CauchyComplete`), not on a hypothesis. `bcor_quo_full` keeps the relative form.
* **`Γ ⊂ π₁(M)`.** Proved directly, without the splitting `M ≅ S × ℝ` (Prop 8.11): a loop of `S`
  null-homotopic in `M` lifts to a loop of `S̃`, contractible because `𝒟` embeds it onto the
  entire graph `Σ ≅ ℝᵈ`. In the relative `bcor_quo_full` (`M` not assumed connected) the clause
  asks `s ∈ range p`.
* **Sorries: none.** No axiom beyond Lean's three.
* **Mark.** `bcor:quo` marked on `bcor_quo_of_isCauchyComplete` by DEC-105 (2026-11-02).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
`bcor:quo` completion pass; ruling L (DEC-105).
-/

namespace Causal.Flat

open Set Function Topology
open scoped Pointwise

variable {d : ℕ}

/-- The graph of a continuous `g : ℝᵈ → ℝ` is homeomorphic to `ℝᵈ` by the spatial projection. -/
def graphHomeomorph {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : Continuous g) :
    (graph g : Set (Minkowski d)) ≃ₜ EuclideanSpace ℝ (Fin d) where
  toFun p := (p : Minkowski d).2
  invFun x := ⟨(g x, x), rfl⟩
  left_inv p := Subtype.ext (Prod.ext p.2.symm rfl)
  right_inv _ := rfl
  continuous_toFun := continuous_snd.comp continuous_subtype_val
  continuous_invFun := (hg.prodMk continuous_id).subtype_mk fun _ => rfl

/-- **Paths in `S` are detected in `X` when `p⁻¹(S)` is simply connected.** For a covering
`p : E → X`, `S ⊆ X` with `p⁻¹(S)` simply connected, and `x` with a point `e` of `p⁻¹(S)` over
it, two paths of `S` from `x` to `y` homotopic in `X` are homotopic in `S`. -/
theorem injective_pathQuotient_map_val_of_preimage {E X : Type*} [TopologicalSpace E]
    [TopologicalSpace X] {p : E → X} (hp : IsCoveringMap p) {S : Set X}
    [SimplyConnectedSpace (p ⁻¹' S)] {x y : S} {e : E} (he : p e = x) :
    Injective fun γ : Path.Homotopic.Quotient x y =>
      γ.map ⟨Subtype.val, continuous_subtype_val⟩ := by
  refine Quotient.ind₂ fun c₀ c₁ hc => ?_
  dsimp only at hc
  simp only [Path.Homotopic.Quotient.mk''_eq_mk] at hc ⊢
  rw [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_map,
    Path.Homotopic.Quotient.eq] at hc
  rw [Path.Homotopic.Quotient.eq]
  set δ₀ : Path (x : X) y := c₀.map continuous_subtype_val
  set δ₁ : Path (x : X) y := c₁.map continuous_subtype_val
  have h₀ : δ₀ 0 = p e := δ₀.source.trans he.symm
  have h₁ : δ₁ 0 = p e := δ₁.source.trans he.symm
  set Γ₀ := hp.liftPath δ₀ e h₀
  set Γ₁ := hp.liftPath δ₁ e h₁
  have hl₀ : ∀ t, p (Γ₀ t) = c₀ t := fun t => congrFun (hp.liftPath_lifts δ₀ e h₀) t
  have hl₁ : ∀ t, p (Γ₁ t) = c₁ t := fun t => congrFun (hp.liftPath_lifts δ₁ e h₁) t
  have hend : Γ₀ 1 = Γ₁ 1 := hp.liftPath_apply_one_eq_of_homotopicRel hc e h₀ h₁
  have hm₀ : ∀ t, Γ₀ t ∈ p ⁻¹' S := fun t => by rw [mem_preimage, hl₀]; exact (c₀ t).2
  have hm₁ : ∀ t, Γ₁ t ∈ p ⁻¹' S := fun t => by rw [mem_preimage, hl₁]; exact (c₁ t).2
  have he₀ : Γ₀ 0 = e := hp.liftPath_zero δ₀ e h₀
  have he₁ : Γ₁ 0 = e := hp.liftPath_zero δ₁ e h₁
  let a : p ⁻¹' S := ⟨e, he₀ ▸ hm₀ 0⟩
  let b : p ⁻¹' S := ⟨Γ₀ 1, hm₀ 1⟩
  let L₀ : Path a b :=
    { toFun := fun t => ⟨Γ₀ t, hm₀ t⟩
      continuous_toFun := Γ₀.continuous.subtype_mk _
      source' := Subtype.ext he₀
      target' := rfl }
  let L₁ : Path a b :=
    { toFun := fun t => ⟨Γ₁ t, hm₁ t⟩
      continuous_toFun := Γ₁.continuous.subtype_mk _
      source' := Subtype.ext he₁
      target' := Subtype.ext hend.symm }
  have hL : L₀.toContinuousMap.HomotopicRel L₁.toContinuousMap {0, 1} :=
    SimplyConnectedSpace.paths_homotopic L₀ L₁
  let q : C(p ⁻¹' S, S) :=
    ⟨fun z => ⟨p z, z.2⟩, (hp.continuous.comp continuous_subtype_val).subtype_mk _⟩
  have hq₀ : q.comp L₀.toContinuousMap = c₀.toContinuousMap := by
    ext t; exact hl₀ t
  have hq₁ : q.comp L₁.toContinuousMap = c₁.toContinuousMap := by
    ext t; exact hl₁ t
  have := hL.comp_continuousMap q
  rw [hq₀, hq₁] at this
  exact this

section QuoFull

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Minkowski d) M]
  [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))] {x₀ : M}
  {D : UniversalCover M x₀ → Minkowski d} {ρ : Deck (UniversalCover.proj M x₀) →* isom d}
  {S : Set M}

/-- **Cor 8.2, "`𝒟 ∘ f̃` is an embedding"** (l.2264), for a Hausdorff `M`: the restriction of the
open embedding `𝒟` (`isOpenEmbedding_of_developsCC`) to `S̃ = p⁻¹(S)`. -/
theorem isEmbedding_develop_liftSet [T2Space M] (hpair : IsDevelopingPair x₀ D ρ)
    (h : DevelopsCC x₀ D S) :
    IsEmbedding fun z : UniversalCover.proj M x₀ ⁻¹' S => D z :=
  (isOpenEmbedding_of_developsCC hpair h).isEmbedding.comp IsEmbedding.subtypeVal

/-- **`S̃ = p⁻¹(S)` is contractible**, for a Hausdorff `M`: `𝒟` maps it homeomorphically onto the
entire graph `Σ = graph g` (`isEmbedding_develop_liftSet`), and `graph g ≅ ℝᵈ`. -/
theorem contractibleSpace_liftSet [T2Space M] (hpair : IsDevelopingPair x₀ D ρ)
    (h : DevelopsCC x₀ D S) : ContractibleSpace (UniversalCover.proj M x₀ ⁻¹' S) := by
  obtain ⟨g, hg, hgr⟩ := isEntireAcausalGraph_iff.1 h.cc.entire
  have hr : range (fun z : UniversalCover.proj M x₀ ⁻¹' S => D z) = graph g := by
    rw [← hgr, image_eq_range]
  exact (((isEmbedding_develop_liftSet hpair h).toHomeomorph.trans
    (Homeomorph.setCongr hr)).trans (graphHomeomorph hg.lipschitzWith.continuous)).contractibleSpace

/-- **Cor 8.2, "the natural morphism `Γ ⊂ π₁(M)` is injective"** (l.2264–2265), for a Hausdorff
`M`: `π₁(S, s) → π₁(M, s)`, induced by the inclusion, is injective at every `s ∈ S` of the
component of `x₀` (`s ∈ range p`). A loop of `S` null-homotopic in `M` lifts to a loop of the
contractible `S̃` (`contractibleSpace_liftSet`, `injective_pathQuotient_map_val_of_preimage`). -/
theorem injective_fundamentalGroup_map_val [T2Space M] (hpair : IsDevelopingPair x₀ D ρ)
    (h : DevelopsCC x₀ D S) (s : S) (hs : (s : M) ∈ range (UniversalCover.proj M x₀)) :
    Injective (FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ s) := by
  haveI := contractibleSpace_liftSet hpair h
  obtain ⟨e, he⟩ := hs
  exact injective_pathQuotient_map_val_of_preimage (isCoveringMap_flatCover_proj d M x₀) he

/-- **Cor 8.2** (`bcor:quo`, l.2263–2271), every clause, in the DEC-35 reading, for a Hausdorff
`M`: `f : S → M` is an embedding (the inclusion), `𝒟 ∘ f̃ : S̃ → 𝐌ⁿ` is an embedding, the
natural morphism `π₁(S) → π₁(M)` is injective (at the base points of the component of `x₀`),
`ρ` is injective, and — with `bcor_quo` — `ρ(Γ)` preserves `Σ = 𝒟(S̃)`, acts freely on it, and
`Σ` meets every timelike line. -/
theorem bcor_quo_full [T2Space M] (hpair : IsDevelopingPair x₀ D ρ) (h : DevelopsCC x₀ D S) :
    IsEmbedding (Subtype.val : S → M) ∧
      IsEmbedding (fun z : UniversalCover.proj M x₀ ⁻¹' S => D z) ∧
      (∀ s : S, (s : M) ∈ range (UniversalCover.proj M x₀) →
        Injective (FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ s)) ∧
      Injective ρ ∧ (∀ γ ∈ ρ.range, γ • (D '' (UniversalCover.proj M x₀ ⁻¹' S)) =
        D '' (UniversalCover.proj M x₀ ⁻¹' S)) ∧
      (∀ γ ∈ ρ.range, γ ≠ 1 → ∀ x ∈ D '' (UniversalCover.proj M x₀ ⁻¹' S), γ • x ≠ x) ∧
      ∀ p v : Minkowski d, IsFutureTimelike v →
        ∃ s : ℝ, p + s • v ∈ D '' (UniversalCover.proj M x₀ ⁻¹' S) :=
  ⟨IsEmbedding.subtypeVal, isEmbedding_develop_liftSet hpair h,
    injective_fundamentalGroup_map_val hpair h, bcor_quo hpair h⟩

/-- **Cor 8.2 for a connected `M`** (a spacetime): the `π₁` clause at every base point of `S`. -/
theorem bcor_quo_full_of_connected [T2Space M] [ConnectedSpace M]
    (hpair : IsDevelopingPair x₀ D ρ) (h : DevelopsCC x₀ D S) :
    IsEmbedding (Subtype.val : S → M) ∧
      IsEmbedding (fun z : UniversalCover.proj M x₀ ⁻¹' S => D z) ∧
      (∀ s : S, Injective (FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ s)) ∧
      Injective ρ ∧ (∀ γ ∈ ρ.range, γ • (D '' (UniversalCover.proj M x₀ ⁻¹' S)) =
        D '' (UniversalCover.proj M x₀ ⁻¹' S)) ∧
      (∀ γ ∈ ρ.range, γ ≠ 1 → ∀ x ∈ D '' (UniversalCover.proj M x₀ ⁻¹' S), γ • x ≠ x) ∧
      ∀ p v : Minkowski d, IsFutureTimelike v →
        ∃ s : ℝ, p + s • v ∈ D '' (UniversalCover.proj M x₀ ⁻¹' S) := by
  haveI := locPathConnectedSpace_of_flat d M
  haveI : PathConnectedSpace M := pathConnectedSpace_iff_connectedSpace.2 ‹_›
  obtain ⟨h1, h2, h3, h4⟩ := bcor_quo_full hpair h
  exact ⟨h1, h2, fun s => h3 s (UniversalCover.proj_surjective _), h4⟩

end QuoFull

/-! ### Cor 8.2 from the paper's Cauchy-completeness (DEC-105, through the DEC-35 bridge) -/

section FromComplete

universe u

/-- **The glue** between the DEC-35 bridge and `DevelopsCC`: for a globally hyperbolic flat
spacetime `M` and a Cauchy surface `S` that is Cauchy-complete in the paper's sense (spacelike
Lipschitz, complete for its induced length, topology field), every developing pair develops `S`
as (CC′) — `injOn`, `IsEntireAcausalGraph` and `NullSaturated` from
`developsCC_of_isCauchyComplete` (Prop 8.1, `[8.G]`, Cor 8.3). -/
theorem developsCC_of_isCauchyComplete_of_isDevelopingPair (M : FlatSpacetime.{u} d) (hGH : GH M)
    {S : Set M} (hS : (flatCausality d M).IsCauchySurface S) (hL : IsSpacelikeLipschitz d S)
    (hc : CompleteSpace (InducedLengthSpace d S))
    (htop : Continuous fun x : InducedLengthSpace d S => (InducedLengthSpace.toSubtype x : M))
    {x₀ : M} {D : UniversalCover M x₀ → Minkowski d} {ρ : Deck (UniversalCover.proj M x₀) →* isom d}
    (hpair : IsDevelopingPair x₀ D ρ) : DevelopsCC x₀ D S := by
  obtain ⟨hS', hinj, hent, hnull⟩ :=
    developsCC_of_isCauchyComplete M hGH hS hL hc htop x₀ D hpair.gx
  exact ⟨hS', hinj, ⟨hent, hnull⟩⟩

/-- **Cor 8.2** (`bcor:quo`, l.2263–2271), every clause, **from the paper's hypothesis** (DEC-105):
`M` a flat spacetime (connected and Hausdorff, implicit in "spacetime"/"manifold"), globally
hyperbolic, `S` a Cauchy surface of `M` complete for its induced length (the paper's
Cauchy-completeness in the DEC-35 reading: `IsSpacelikeLipschitz`, `CompleteSpace` of
`InducedLengthSpace`, the topology field — exactly the fields of `IsCauchyComplete`), `f` the
inclusion `S ⊆ M`, `(𝒟, ρ)` any developing pair. The injectivity of `𝒟` on `S̃ = p⁻¹(S)` is no
longer assumed: (CC′) is obtained from completeness through the proved bridge
(`developsCC_of_isCauchyComplete_of_isDevelopingPair`). Clauses: `f` is an embedding, `𝒟 ∘ f̃` is
an embedding, `π₁(S, s) → π₁(M, s)` is injective at every `s ∈ S`, `ρ` is injective, `ρ(Γ)`
preserves `Σ = 𝒟(S̃)` and acts freely on it, and `Σ` meets every timelike line. -/
theorem bcor_quo_of_isCauchyComplete (M : FlatSpacetime.{u} d) (hGH : GH M) {S : Set M}
    (hS : (flatCausality d M).IsCauchySurface S) (hL : IsSpacelikeLipschitz d S)
    (hc : CompleteSpace (InducedLengthSpace d S))
    (htop : Continuous fun x : InducedLengthSpace d S => (InducedLengthSpace.toSubtype x : M))
    {x₀ : M} {D : UniversalCover M x₀ → Minkowski d} {ρ : Deck (UniversalCover.proj M x₀) →* isom d}
    (hpair : IsDevelopingPair x₀ D ρ) :
    IsEmbedding (Subtype.val : S → M) ∧
      IsEmbedding (fun z : UniversalCover.proj M x₀ ⁻¹' S => D z) ∧
      (∀ s : S, Injective (FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ s)) ∧
      Injective ρ ∧ (∀ γ ∈ ρ.range, γ • (D '' (UniversalCover.proj M x₀ ⁻¹' S)) =
        D '' (UniversalCover.proj M x₀ ⁻¹' S)) ∧
      (∀ γ ∈ ρ.range, γ ≠ 1 → ∀ x ∈ D '' (UniversalCover.proj M x₀ ⁻¹' S), γ • x ≠ x) ∧
      ∀ p v : Minkowski d, IsFutureTimelike v →
        ∃ s : ℝ, p + s • v ∈ D '' (UniversalCover.proj M x₀ ⁻¹' S) :=
  bcor_quo_full_of_connected hpair
    (developsCC_of_isCauchyComplete_of_isDevelopingPair M hGH hS hL hc htop hpair)

/-- **Cor 8.2 from `IsCauchyComplete d M`** (DEC-105): a globally hyperbolic Cauchy-complete flat
spacetime has a Cauchy surface `S` such that, for every base point and every developing pair, all
the clauses of `bcor_quo_of_isCauchyComplete` hold. -/
theorem bcor_quo_of_isCauchyComplete' (M : FlatSpacetime.{u} d) (hGH : GH M)
    (hCC : IsCauchyComplete d M) :
    ∃ S : Set M, (flatCausality d M).IsCauchySurface S ∧
      ∀ (x₀ : M) (D : UniversalCover M x₀ → Minkowski d)
        (ρ : Deck (UniversalCover.proj M x₀) →* isom d), IsDevelopingPair x₀ D ρ →
      IsEmbedding (Subtype.val : S → M) ∧
      IsEmbedding (fun z : UniversalCover.proj M x₀ ⁻¹' S => D z) ∧
      (∀ s : S, Injective (FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ s)) ∧
      Injective ρ ∧ (∀ γ ∈ ρ.range, γ • (D '' (UniversalCover.proj M x₀ ⁻¹' S)) =
        D '' (UniversalCover.proj M x₀ ⁻¹' S)) ∧
      (∀ γ ∈ ρ.range, γ ≠ 1 → ∀ x ∈ D '' (UniversalCover.proj M x₀ ⁻¹' S), γ • x ≠ x) ∧
      ∀ p v : Minkowski d, IsFutureTimelike v →
        ∃ s : ℝ, p + s • v ∈ D '' (UniversalCover.proj M x₀ ⁻¹' S) := by
  obtain ⟨S, hS, hL, hc, htop⟩ := hCC
  exact ⟨S, hS, fun _ _ _ hpair => bcor_quo_of_isCauchyComplete M hGH hS hL hc htop hpair⟩

end FromComplete

/-! ### Non-vacuity (kb/0011): `𝐌ⁿ` itself, `Σ = {t = 0}` -/

example (x₀ : Minkowski d) :=
  bcor_quo_full_of_connected (isDevelopingPair_minkowski x₀) (developsCC_minkowski x₀)

/-- Non-vacuity of the hypothesis of `bcor_quo_of_isCauchyComplete'` (kb/0011): `𝐌ⁿ` is a
globally hyperbolic Cauchy-complete flat spacetime. -/
example :=
  bcor_quo_of_isCauchyComplete' (FlatSpacetime.minkowskiSpace d) gh_minkowskiSpace
    isCauchyComplete_minkowskiSpace

end Causal.Flat
