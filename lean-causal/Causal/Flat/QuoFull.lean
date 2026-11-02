import Causal.Flat.Develop

/-!
# `Causal.Flat.QuoFull` — Cor 8.2 in full (DEC-35 reading): the embeddings and `π₁(S) ↪ π₁(M)`

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §8,
`GHFspace.tex` l.2263–2271 (labelled file).

* `bcor:quo` — `GHFspace.tex:2264` (Cor 8.2, l.2263–2271), every clause stated and proved in
  the DEC-35 reading **from the hypothesis `DevelopsCC.injOn`** (`𝒟` injective on `S̃`, which is
  the injective half of "`𝒟 ∘ f̃` is an embedding" and is assumed, not proved — checklist, SCOPE),
  `M` Hausdorff (T2 implicit in "manifold", as DEC-90 rules for `bprop:danom`), the `π₁` clause
  at base points of the component of `x₀` (connected `M`: every base point);
  **unmarked, no ruling yet** (SCOPE) — `bcor_quo_full`, `bcor_quo_full_of_connected`,
  `injective_fundamentalGroup_map_val`, `contractibleSpace_liftSet`, `isEmbedding_develop_liftSet`:
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

* `graphHomeomorph` — the graph of a continuous `g : ℝᵈ → ℝ` is homeomorphic to `ℝᵈ`.
* `isEmbedding_develop_liftSet` — `𝒟 ∘ f̃ : S̃ → 𝐌ⁿ` is an embedding (T2).
* `contractibleSpace_liftSet` — `S̃ = p⁻¹(S)` is contractible: `𝒟` maps it homeomorphically onto
  the entire graph `Σ`, and `Σ ≅ ℝᵈ` (T2).
* `injective_pathQuotient_map_val_of_preimage` — for a covering `p : E → X` and `S ⊆ X` with
  `p⁻¹(S)` simply connected, `S ↪ X` is injective on homotopy classes of paths between points of
  `S` over which `p⁻¹(S)` has a point (lift both paths from one point; homotopic below, so they
  end at one point; homotopic in the simply connected `p⁻¹(S)`; project back to `S`).
* `injective_fundamentalGroup_map_val` — `π₁(S, s) → π₁(M, s)` is injective for `s ∈ S` in the
  component of `x₀`.
* `bcor_quo_full` — every clause of Cor 8.2; `bcor_quo_full_of_connected` — `M` connected.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `S` a complete Riemannian hypersurface, `f` an isometric immersion (l.2215–2216) | ⚠ strengthened (DEC-35 reading, as in `Flat/Develop`): `S` a Cauchy surface of `M` with `DevelopsCC`; `f` is the inclusion `S ⊆ M`, `S̃ := p⁻¹(S) ⊆ M̃`, `f̃` its inclusion |
| "`𝒟 ∘ f̃` is an embedding": its injectivity (in the paper a consequence of completeness, Prop 8.1) | ⚠ strengthened: carried as the hypothesis `DevelopsCC.injOn` (`𝒟` injective on `S̃ = p⁻¹(S)`; DEC-35 bridge, `Flat/Develop`); only the topological half of the embedding is proved — `𝒟` a local homeomorphism, the injectivity extended from `S̃` to `M̃` (`injective_of_developsCC`), hence `isOpenEmbedding_of_developsCC` and `isEmbedding_develop_liftSet` |
| `Γ = π₁(S)`, "the natural morphism `Γ ⊂ π₁(M)`" | ✓ `FundamentalGroup.map` of the inclusion `S → M` at `s ∈ S`; at every `s` for `M` connected, at the `s` of the component of `x₀` otherwise (SCOPE) |
| (implicit) `M` a manifold: Hausdorff | ✓ carried: `[T2Space M]`, implicit in "manifold" as DEC-90 rules |
| (implicit) `M` connected (a spacetime) | ✓ carried only in `bcor_quo_full_of_connected`; `bcor_quo_full` restricts the base point instead |
| "timelike geodesic" | ✓ the timelike affine lines `p + ℝ v`, `v` future timelike (as in `bcor_quo`) |

## SCOPE (disclosed)

* **Reading.** DEC-35: the paper's immersed complete hypersurface is replaced by a Cauchy surface
  with (CC′) for its lift; under it "`f` is an embedding" is the subspace inclusion
  (`IsEmbedding.subtypeVal`), not the paper's claim that an isometric immersion of a complete
  hypersurface is injective and proper. The immersion form (blocker of the curation row) is not
  formalized: the library has no immersed hypersurfaces.
* **`DevelopsCC.injOn` is assumed.** The injectivity of `𝒟` on `S̃` — the injective half of
  "`𝒟 ∘ f̃` is an embedding", which the paper derives from completeness (Prop 8.1) — is a field
  of `DevelopsCC` (`Flat/Develop`, DEC-35 bridge), not a theorem. Downstream of it, and so proved
  only relative to it: the embedding `isEmbedding_develop_liftSet` (through
  `injective_of_developsCC`), the contractibility of `S̃` (`contractibleSpace_liftSet`), hence the
  `π₁` clause (`injective_fundamentalGroup_map_val`), and the injectivity of `ρ` and freeness of
  `ρ(Γ)` on `Σ` (`bcor_quo`, via `eq_one_of_holonomy_fix`). Only "`f` is an embedding", the
  invariance of `Σ` under `ρ(Γ)` and "`Σ` meets every timelike line" do not use it. So the
  printed statement is proved in the DEC-35 reading, not unconditionally: the hypothesis
  replacing completeness carries the injectivity half of the embedding clause.
* **`Γ ⊂ π₁(M)`.** Proved directly, without the splitting `M ≅ S × ℝ` (Prop 8.11): a loop of `S`
  null-homotopic in `M` lifts to a loop of `S̃`, contractible because `𝒟` embeds it onto the
  entire graph `Σ ≅ ℝᵈ`. The paper's `Γ` is `π₁` of the connected `S`; in the reading `S` may
  meet several components of a disconnected `M`, and only the part over the component of `x₀`
  is developed, so `bcor_quo_full` asks `s ∈ range p`; for connected `M` this is automatic.
  Corollary: `S ∩ range p` is path connected, and the restricted `p : S̃ → S` is, at the level
  of `π₁`, the universal covering of the paper's set-up (finding of the curation row, l.2215–2223,
  answered in the reading).
* **Sorries: none.** No axiom beyond Lean's three.
* **Mark.** None: the label's curation row waits on the master's ruling on the DEC-35 reading.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
`bcor:quo` completion pass.
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

/-! ### Non-vacuity (kb/0011): `𝐌ⁿ` itself, `Σ = {t = 0}` -/

example (x₀ : Minkowski d) :=
  bcor_quo_full_of_connected (isDevelopingPair_minkowski x₀) (developsCC_minkowski x₀)

end Causal.Flat
