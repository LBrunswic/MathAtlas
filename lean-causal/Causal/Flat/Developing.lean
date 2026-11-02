import CausalScaffold.Flat.Form
import CausalScaffold.Port.Developing
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# `CausalScaffold.Flat.Developing` — the developing map and the holonomy of a flat spacetime

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §2.3
"Flat spacetimes as geometric manifolds" (`GHFspace.tex` l.482–492), and the set-up of §8
(l.2190–2201), where the developing map `𝒟` and the holonomy `ρ` are introduced.

> Truely speaking, every spacetimes considered in this work are flat, i.e., locally modeled on
> the Minkowski space. In other words, in the language of geometric structures (see e.g.
> \cite{gold}), they are $(G,X)$-manifolds with $X = {\bf M}^{n}$ and
> $G = \mbox{Isom}(M^{n})$.
>
> We will need only few facts on geometric structures: the existence of the developping map and
> the holonomy morphism (see \S \ref{spapa}). (l.482–492)

> Let $\widetilde{M}$ be the universal covering of $M$, ${\mathcal D}: \widetilde{M} \rightarrow
> {\bf M}^{n}$ the developping map […]. Let $\rho$ be the holonomy morphism of $M$ […]: it is a
> morphism $\rho: \Gamma \rightarrow \mbox{Isom}({\bf M}^{n})$. (l.2190–2201)

§2.3 is prose: **no ledger label**, so nothing is marked. This module makes the two "facts on
geometric structures" available for every flat spacetime, as consequences of the classical
developing theorem ported from gx (`CausalScaffold.Port.Developing`).

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; the library's `Minkowski d =
ℝ × EuclideanSpace ℝ (Fin d)` has `d` spatial dimensions, so Barbot's `n` is `d + 1`.

## Main declarations

* `Causal.Flat.isAnalyticAction_isom` (instance) — `Isom(𝐌ⁿ)` acts analytically on `𝐌ⁿ`:
  faithfully, and rigidly (an affine map is determined by its restriction to a nonempty open set,
  which affinely spans `𝐌ⁿ`); `Causal.Flat.analyticStructure_isom` — `(Isom(𝐌ⁿ), 𝐌ⁿ)` is an
  analytical structure in gx's sense (connected, locally connected, Hausdorff, by homeomorphisms).
* `Causal.semilocallySimplyConnected_of_chartedSpace` — a space with an atlas over a real normed
  space is semilocally simply connected (charts onto convex balls);
  `Causal.Flat.locPathConnectedSpace_of_flat`, `Causal.Flat.semilocallySimplyConnected_of_flat`.
* `Causal.Flat.flatCoverChartedSpace M x₀` — the flat structure of the universal cover
  `M̃ = UniversalCover M x₀`, pulled back along `proj`.
* `Causal.Flat.flat_developing_theorem` — **Barbot's `𝒟` and `ρ`**: `dev : M̃ → 𝐌ⁿ` an
  `(Isom(𝐌ⁿ), 𝐌ⁿ)`-morphism, hence a local homeomorphism, and `hol : Deck(M̃ → M) →* Isom(𝐌ⁿ)`
  with `dev ∘ γ = hol γ • dev`; `Causal.Flat.flat_developing_theorem_fundamentalGroup` — the
  holonomy on `π₁(M, x₀)`; `Causal.Flat.flat_developing_unique` — unique up to a unique element
  of `Isom(𝐌ⁿ)` (`dev' = g • dev`, `hol' = g hol g⁻¹`); `Causal.Flat.flat_developing_descends`
  — trivial holonomy, then `dev` factors through `M` (`M` connected).
* `Causal.Flat.flat_developing_minkowski` — an inhabitant: `𝐌ⁿ` itself, with developing map `id`;
  the four developing theorems are applied to it in `example`s below.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `M` a flat spacetime: an `(Isom(𝐌ⁿ), 𝐌ⁿ)`-manifold | ✓ carried: `[ChartedSpace (Minkowski d) M] [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))]` (DEC-16) |
| `M` connected, Hausdorff, second countable (a manifold) | ⚠ weakened: not used for `𝒟`, `ρ` or their uniqueness; `ConnectedSpace M` only for the descent |
| `M` time-oriented (a spacetime) | ⚠ weakened: not used; it is encoded in `isom d` (linear parts in `SO₀(1, d)`) |
| the universal cover exists | ✓ proved: `M` is locally path-connected and semilocally simply connected because its charts land in the normed space `𝐌ⁿ` |

## SCOPE (disclosed)

* **(a)** "Developing map" is read as in the port (its SCOPE (a)): a `(G,X)`-morphism
  `M̃ → 𝐌ⁿ` for the pulled-back structure, i.e. near every point a translate by `Isom(𝐌ⁿ)` of a
  chart. Its being a local homeomorphism is stated alongside.
* **(b)** `ρ` lives on the deck group `Deck(M̃ → M)` (`flat_developing_theorem`) or on
  `π₁(M, x₀)` through `UniversalCover.deckHom` (`flat_developing_theorem_fundamentalGroup`), with
  the port's sign convention. Barbot's restriction of `ρ` to `Γ = π₁(S)` (l.2199) is §8's, not
  this module's.
* **(c)** Quotients `Γ\Ω` of open subsets of `𝐌ⁿ` (and their developing maps) are wave 2
  (`Flat/Quotient`), not here.
  Noted for wave 2: no instance `HasGroupoid (U : Opens 𝐌ⁿ) (gxGroupoid (isom d) (Minkowski d))`
  is synthesized (`gxGroupoid` is not yet shown `ClosedUnderRestriction`), so these theorems do
  not yet apply to an open `Ω ⊆ 𝐌ⁿ` with its subspace atlas.
* **(d)** `Causal.semilocallySimplyConnected_of_chartedSpace` holds over any real normed model
  space and is not about flat spacetimes; it lives here (namespace `Causal`, not `Causal.Flat`)
  only because the port files are not this package's to edit. Its natural home at graduation is
  beside `SemilocallySimplyConnected` in `CausalScaffold.Port.UniversalCover`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. The developing theorem
is `Causal.developing_theorem` of `CausalScaffold.Port.Developing`, ported from
`lean-gx/GX/Structure/Developing.lean` at `e5a1d46` (WP-24) by WP-32a; the universal cover is
`CausalScaffold.Port.UniversalCover`, ported from `lean-gx/GX/Topology/UniversalCover.lean`.
Written by WP-32b-Developing.
-/

namespace Causal

open Set Filter Topology

/-! ### Charted spaces over a normed space are semilocally simply connected -/

/-- **A space with an atlas over a real normed space is semilocally simply connected**: a loop
at `y` inside the preimage of a ball of the chart target is contracted in the ball, which is
convex, hence simply connected. -/
theorem semilocallySimplyConnected_of_chartedSpace {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (M : Type*) [TopologicalSpace M] [ChartedSpace E M] :
    SemilocallySimplyConnected M := by
  intro y
  set e := chartAt E y
  obtain ⟨r, hr, hrt⟩ := Metric.isOpen_iff.1 e.open_target (e y) (mem_chart_target E y)
  set B := Metric.ball (e y) r
  refine ⟨e.source ∩ e ⁻¹' B, ?_, fun γ hγ => ?_⟩
  · exact e.continuousAt (mem_chart_source E y) |>.preimage_mem_nhds
      (Metric.ball_mem_nhds _ hr) |> inter_mem (e.open_source.mem_nhds (mem_chart_source E y))
  have hc : e y ∈ B := Metric.mem_ball_self hr
  haveI : ContractibleSpace B := (convex_ball (e y) r).contractibleSpace ⟨_, hc⟩
  -- the loop read in the chart, as a loop in the ball
  let pB : Path (⟨e y, hc⟩ : B) ⟨e y, hc⟩ :=
    { toFun := fun t => ⟨e (γ t), (hγ t).2⟩
      continuous_toFun := (e.continuousOn.comp_continuous γ.continuous
        fun t => (hγ t).1).subtype_mk _
      source' := Subtype.ext (by simp)
      target' := Subtype.ext (by simp) }
  have hpB : pB.Homotopic (Path.refl _) := SimplyConnectedSpace.paths_homotopic _ _
  let g : C(B, M) := ⟨fun b => e.symm b,
    e.continuousOn_symm.comp_continuous continuous_subtype_val fun b => hrt b.2⟩
  have hgy : g ⟨e y, hc⟩ = y := e.left_inv (mem_chart_source E y)
  have h := (hpB.map g).pathCast hgy.symm hgy.symm
  convert h using 1
  · ext t
    exact (e.left_inv (hγ t).1).symm
  · ext t
    exact hgy.symm

end Causal

namespace Causal.Flat

open Set Filter Topology

variable {d : ℕ}

/-! ### `Isom(𝐌ⁿ)` acts analytically on `𝐌ⁿ` -/

/-- **`Isom(𝐌ⁿ)` acts analytically on `𝐌ⁿ`**: faithfully, since an isometry is its affine map;
rigidly, since two affine maps agreeing on a nonempty open set agree on its affine span, which is
all of `𝐌ⁿ` (`IsOpen.affineSpan_eq_top`). -/
instance isAnalyticAction_isom : IsAnalyticAction (isom d) (Minkowski d) where
  eq_of_smul_eq_smul {g h} hgh := Subtype.ext (AffineEquiv.ext hgh)
  smul_eq_of_eqOn {g h U} hU hne heq p := by
    have : (g : Minkowski d ≃ᵃ[ℝ] Minkowski d) = h :=
      AffineEquiv.ext_on (hU.affineSpan_eq_top hne) _ _ heq
    rw [isom_smul_def, isom_smul_def, this]

/-- **`(Isom(𝐌ⁿ), 𝐌ⁿ)` is an analytical structure** in gx's sense (`AnalyticStructure`):
`𝐌ⁿ` is connected, locally connected and Hausdorff, and `Isom(𝐌ⁿ)` acts faithfully and rigidly
by homeomorphisms. -/
theorem analyticStructure_isom : AnalyticStructure (isom d) (Minkowski d) where
  connectedSpace := inferInstance
  locallyConnectedSpace := inferInstance
  t2Space := inferInstance
  continuousConstSMul := inferInstance
  isAnalyticAction := inferInstance

/-! ### A flat spacetime has a universal cover -/

section Cover

/-- A space with an atlas over `𝐌ⁿ` is locally path-connected. -/
theorem locPathConnectedSpace_of_flat (d : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (Minkowski d) M] : LocPathConnectedSpace M :=
  ChartedSpace.locPathConnectedSpace (Minkowski d) M

/-- A space with an atlas over `𝐌ⁿ` is semilocally simply connected. -/
theorem semilocallySimplyConnected_of_flat (d : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (Minkowski d) M] : SemilocallySimplyConnected M :=
  semilocallySimplyConnected_of_chartedSpace (E := Minkowski d) M

/-- **The flat structure of the universal cover** `M̃ = UniversalCover M x₀`: the atlas of `M`
pulled back along the covering map `proj` (`Causal.coverChartedSpace`). -/
@[reducible] noncomputable def flatCoverChartedSpace (d : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (Minkowski d) M] (x₀ : M) :
    ChartedSpace (Minkowski d) (UniversalCover M x₀) :=
  haveI := locPathConnectedSpace_of_flat d M
  coverChartedSpace (Minkowski d) (semilocallySimplyConnected_of_flat d M) x₀

variable (M : Type*) [TopologicalSpace M] [ChartedSpace (Minkowski d) M]
  [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))]

/-- The pulled-back structure on `M̃` is flat. -/
theorem hasGroupoid_flatCover (x₀ : M) :
    letI := flatCoverChartedSpace d M x₀
    HasGroupoid (UniversalCover M x₀) (gxGroupoid (isom d) (Minkowski d)) :=
  haveI := locPathConnectedSpace_of_flat d M
  hasGroupoid_cover (G := isom d) (semilocallySimplyConnected_of_flat d M) x₀

omit [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))] in
/-- For it, `proj : M̃ → M` is an `(Isom(𝐌ⁿ), 𝐌ⁿ)`-morphism. -/
theorem isGXMorphism_flatCover_proj (x₀ : M) :
    letI := flatCoverChartedSpace d M x₀
    IsGXMorphism (isom d) (Minkowski d) (UniversalCover.proj M x₀) :=
  haveI := locPathConnectedSpace_of_flat d M
  isGXMorphism_cover_proj (G := isom d) (semilocallySimplyConnected_of_flat d M) x₀

/-! ### The developing map and the holonomy -/

/-- **The developing map `𝒟` and the holonomy `ρ` of a flat spacetime** (Barbot §2.3,
l.482–492; used from §8 on, l.2190–2201). For every `(Isom(𝐌ⁿ), 𝐌ⁿ)`-manifold `M` and base
point `x₀`, the universal cover `M̃` carries a developing map `dev : M̃ → 𝐌ⁿ`, an
`(Isom(𝐌ⁿ), 𝐌ⁿ)`-morphism and so a local homeomorphism, and a holonomy morphism
`hol : Deck(M̃ → M) →* Isom(𝐌ⁿ)` for which `dev` is equivariant: `dev ∘ γ = hol γ • dev`. -/
theorem flat_developing_theorem (x₀ : M) :
    letI := flatCoverChartedSpace d M x₀
    ∃ (dev : UniversalCover M x₀ → Minkowski d)
      (hol : Deck (UniversalCover.proj M x₀) →* isom d),
      IsGXMorphism (isom d) (Minkowski d) dev ∧ IsLocalHomeomorph dev ∧
        ∀ (γ : Deck (UniversalCover.proj M x₀)) (z : UniversalCover M x₀),
          dev (γ.1 z) = hol γ • dev z :=
  haveI := locPathConnectedSpace_of_flat d M
  developing_theorem (G := isom d) (X := Minkowski d) (semilocallySimplyConnected_of_flat d M) x₀

/-- **The holonomy on the fundamental group**: `ρ : π₁(M, x₀) →* Isom(𝐌ⁿ)`, acting on `M̃`
through `UniversalCover.deckHom`, with `dev` equivariant. -/
theorem flat_developing_theorem_fundamentalGroup (x₀ : M) :
    letI := flatCoverChartedSpace d M x₀
    ∃ (dev : UniversalCover M x₀ → Minkowski d) (ρ : FundamentalGroup M x₀ →* isom d),
      IsGXMorphism (isom d) (Minkowski d) dev ∧
        ∀ (a : FundamentalGroup M x₀) (z : UniversalCover M x₀),
          dev ((UniversalCover.deckHom a).1 z) = ρ a • dev z :=
  haveI := locPathConnectedSpace_of_flat d M
  developing_theorem_fundamentalGroup (G := isom d) (X := Minkowski d)
    (semilocallySimplyConnected_of_flat d M) x₀

/-- **Uniqueness of `(𝒟, ρ)`**: two developing pairs of a flat spacetime differ by a unique
isometry `g`: `dev' = g • dev` and `hol' = g hol g⁻¹`. -/
theorem flat_developing_unique (x₀ : M) :
    letI := flatCoverChartedSpace d M x₀
    ∀ {dev dev' : UniversalCover M x₀ → Minkowski d}
      {hol hol' : Deck (UniversalCover.proj M x₀) →* isom d},
      IsGXMorphism (isom d) (Minkowski d) dev → (∀ γ z, dev (γ.1 z) = hol γ • dev z) →
      IsGXMorphism (isom d) (Minkowski d) dev' → (∀ γ z, dev' (γ.1 z) = hol' γ • dev' z) →
      ∃! g : isom d, (∀ z, dev' z = g • dev z) ∧ ∀ γ, hol' γ = g * hol γ * g⁻¹ :=
  haveI := locPathConnectedSpace_of_flat d M
  developing_unique (G := isom d) (X := Minkowski d) (semilocallySimplyConnected_of_flat d M) x₀

omit [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))] in
/-- **Descent**: for a connected flat spacetime, a developing pair with trivial holonomy has
`dev = D ∘ proj` for an `(Isom(𝐌ⁿ), 𝐌ⁿ)`-morphism `D : M → 𝐌ⁿ`. -/
theorem flat_developing_descends [ConnectedSpace M] (x₀ : M) :
    letI := flatCoverChartedSpace d M x₀
    ∀ {dev : UniversalCover M x₀ → Minkowski d} {hol : Deck (UniversalCover.proj M x₀) →* isom d},
      IsGXMorphism (isom d) (Minkowski d) dev → (∀ γ z, dev (γ.1 z) = hol γ • dev z) →
      (∀ γ, hol γ = 1) →
      ∃ D : M → Minkowski d, IsGXMorphism (isom d) (Minkowski d) D ∧
        dev = D ∘ UniversalCover.proj M x₀ :=
  haveI := locPathConnectedSpace_of_flat d M
  developing_descends (G := isom d) (X := Minkowski d) (semilocallySimplyConnected_of_flat d M) x₀

end Cover

/-! ### An inhabitant -/

/-- The hypotheses are inhabited: `𝐌ⁿ` itself, with its one-chart atlas, is a flat spacetime,
and the identity is a developing map of it. -/
theorem flat_developing_minkowski :
    HasGroupoid (Minkowski d) (gxGroupoid (isom d) (Minkowski d)) ∧
      IsGXMorphism (isom d) (Minkowski d) (id : Minkowski d → Minkowski d) :=
  ⟨inferInstance, isGXMorphism_id⟩

/-- The developing theorems apply to `𝐌ⁿ` itself (the hypotheses are not vacuous):
`flat_developing_theorem`, its `π₁` form, uniqueness and descent all elaborate at `M := 𝐌ⁿ`. -/
example (x₀ : Minkowski d) :
    letI := flatCoverChartedSpace d (Minkowski d) x₀
    ∃ (dev : UniversalCover (Minkowski d) x₀ → Minkowski d)
      (hol : Deck (UniversalCover.proj (Minkowski d) x₀) →* isom d),
      IsGXMorphism (isom d) (Minkowski d) dev ∧ IsLocalHomeomorph dev ∧
        ∀ (γ : Deck (UniversalCover.proj (Minkowski d) x₀)) (z : UniversalCover (Minkowski d) x₀),
          dev (γ.1 z) = hol γ • dev z :=
  flat_developing_theorem (d := d) (Minkowski d) x₀

example (x₀ : Minkowski d) := flat_developing_theorem_fundamentalGroup (d := d) (Minkowski d) x₀
example (x₀ : Minkowski d) := @flat_developing_unique d (Minkowski d) _ _ _ x₀
example (x₀ : Minkowski d) := @flat_developing_descends d (Minkowski d) _ _ _ x₀

end Causal.Flat
