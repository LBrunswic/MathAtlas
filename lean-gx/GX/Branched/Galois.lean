import GX.Branched.Paths

/-!
# Galoisian branched coverings and the Galois correspondence (§3.4, l.1417–1559)

Packages WP-26f, WP-27e, WP-35b. `papers/gx`, `RamcovGX.tex:1417–1559`. Reworked to DEC-55,
DEC-57 (2026-11-01) and DEC-70 (2026-11-02): "almost trivial" is the **literal** compact-open
notion `GX.AlmostTrivialCC` of `GX.Branched.Paths`, and semi-local simple connectedness is stated with it
(`GX.IsSLSCAtCC`, `GX.IsSLSCInCC`); quasi-Galoisian is the completion of a Galoisian covering over
a portly `O`; `prop:Galoisian_fiber` uses a basis of open connected neighbourhoods;
`rem:simple_cases` reads a codimension-`≥ 2` submanifold as locally flat and a simplicial complex
as a locally finite geometric one, facets = closed faces. (The names `GX.IsSLSCAt`, `GX.IsSLSCIn`
keep the HOMOTOPY form, which `GXScaffold.Branched.GaloisExamples` consumes; the paper's notions
are the `…CC` declarations.)

* **`def:automorphisms_spread`** — `RamcovGX.tex:1420`: `Γ(X/Y)` is `GX.deckGroup` (strict
  library); `GX.deckStab` (`Γ_x`), `GX.deckSetStab` (`Γ_U`); automorphisms in `Spread`
  `GX.deckToSpreadIso`, `GX.Spread.Iso.homeoX_mem_deckGroup`.
* **`def:branched_covering_galoisian_group`** — `RamcovGX.tex:1426` (DEC-57, SCOPE (a)):
  `GX.IsGaloisian`, `GX.IsQuasiGaloisian` (`GX.IsDeckTransitive`), equivalent to the completion
  form: `GX.isQuasiGaloisian_of_isSpreadCompletion`, `GX.IsQuasiGaloisian.exists_isSpreadCompletion`.
* **`rem:galois_quotient`** — `RamcovGX.tex:1431`: `GX.galois_quotient` (`GX.HomeoQuotient`).
* **`lem:branched_covering_group_automorphisms`** — `RamcovGX.tex:1435`:
  `GX.deckRestrictEquiv`, `GX.branched_covering_group_automorphisms`.
* **`cor:branched_covering`** — `RamcovGX.tex:1441`: `GX.deckOrdEquiv`.
* **`def:semi_locally_simple_connectedness`** — `RamcovGX.tex:1451` (DEC-55, SCOPE (b)):
  `GX.IsSLSCAtCC`, `GX.IsSLSCInCC`; the homotopy form `GX.IsSLSCAt`, `GX.IsSLSCIn` implies it
  (`GX.IsSLSCIn.isSLSCInCC`) and agrees with it for `U` open semilocally simply connected
  (`GX.isSLSCInCC_iff`).
* `rem:definition_semi_locally_simply_connected` — `RamcovGX.tex:1455` (partial, corrected: one
  direction only, SCOPE (e)): `GX.isSLSCInCC_univ_of_semilocallySimplyConnected`; the converse
  fails, `GX.harmonicArchipelago_counterexample` (`GX.HarmonicArchipelago`).
* **`rem:simple_cases`** — `RamcovGX.tex:1459` (DEC-55, DEC-57, SCOPE (f)): first item
  `GX.isSLSCInCC_of_locally_linear` (locally flat; linear model `GX.isSLSCInCC_compl_submodule`,
  `GX.isSLSCInCC_univ_of_normedSpace`), `GX.isSLSCInCC_compl_faces_of_locallyFinite`,
  `GX.isSLSCInCC_compl_faces` (simplicial; `GX.isSLSCAtCC_of_radial_contraction`); second item
  `GX.isSLSCInCC_of_local_nhds` (any neighbourhoods, `X` locally connected) and
  `GX.isSLSCInCC_of_local` (open neighbourhoods, no hypothesis) (`GX.AlmostTrivialCC.map`,
  `GX.isSLSCAtCC_of_subtype`). Homotopy forms: `GX.isSLSCIn_compl_submodule`,
  `GX.isSLSCIn_of_locally_linear`, `GX.isSLSCIn_compl_faces_of_locallyFinite`, `GX.isSLSCIn_of_local`.
* **`lem:dense_orbits`** — `RamcovGX.tex:1469` (DEC-57): `GX.dense_orbits`.
* **`prop:Galoisian_fiber`** — `RamcovGX.tex:1478` (DEC-57, SCOPE (c)):
  `GX.galoisian_fiber` (`GX.GaloisThread`).
* **`lem:alternative_countable`** — `RamcovGX.tex:1492` (DEC-57): `GX.alternative_countable`.
* **`prop:Galoisian_semilocal`** — `RamcovGX.tex:1514` (DEC-55): `GX.galoisian_semilocal_cc`;
  (ii) ⇒ (i) without second countability `GX.maxBranched_isGaloisian_cc`; homotopy form
  `GX.galoisian_semilocal`, `GX.maxBranched_isGaloisian`.
* **`theo:Galois_cor`** — `RamcovGX.tex:1550` (DEC-70: `Y ∖ S` slsc carried; DEC-55):
  `GX.galois_correspondence_cc`; homotopy form `GX.galois_correspondence`
  (`GX.maxBranched_isGaloisian`, `GX.galois_cor_quotient`, `GX.galois_cor_normal`).

> Let $X\xrightarrow{p} Y$ be a spread, an automorphisms of $p$ is an homeomorphism $\varphi$ of
> $X$ such that $p\circ \varphi = p$. […] A branched covering $X\xrightarrow{p} Y$ is Galoisian if
> the group $\Gamma(X/Y)$ of automorphism of $p$ acts transitively on the fibers of $p$. It is
> called quasi-Galoisian if $p$ is the completion of a Galoisian covering.
>
> We say that an open subset $\U$ is semi-locally simply connected at $x \in \overline \U$ if
> there exists a connected open neighborhood $\V$ of $x$ such that every loop $\gamma$ of
> $\Omega(x,x,\V\cap \U)$ seen as an element of $\Omega(x,x,\U)$ is almost trivial.
>
> Let $Y$ be a connected, locally path-connected Hausdorff topological space and let $S\subset Y$
> skeletal. Assume $Y\setminus S$ is semi-locally simply connected in $Y$. Then the maximal
> covering $\widetilde Y^S$ possibly branched over $S$ is Galoisian. Furthermore, every covering
> $X$ of $Y$ possibly branched over $S$ is isomorphic to the quotient of $\widetilde{Y}^S$ by a
> subgroup of $\Gamma(\widetilde{Y}^S/Y)$. Finally, this subgroup is normal if and only if $X$ is
> Galoisian.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| §3 standing: Hausdorff, locally path-connected, first countable | ⚠ weakened: each theorem carries what its proof uses |
| `lem:branched_covering_group_automorphisms`, `cor:…` | ✓ `X`, `Y` T2, `Y` locally connected (completion functoriality) |
| `rem:galois_quotient` | ✓ `Y` T1, LPC, first countable (`p` open); nothing on `X` |
| `lem:dense_orbits`, `prop:Galoisian_fiber`, `lem:alternative_countable` | ✓ `X`, `Y` T2, `Y` LPC, first countable; "possibly branched over `S`" not used |
| `lem:alternative_countable`: `Γ(X/Y)` countable | ✓ carried; no finiteness or surjectivity hypothesis needed (Baire, SCOPE (d)) |
| `prop:Galoisian_semilocal`: `Y` connected, LPC, second countable, T2; `S` skeletal; `Y ∖ S` slsc | ✓ carried; (ii) ⇒ (i) without second countability |
| `theo:Galois_cor`: `Y` connected, LPC, T2 (first countable, §3 standing) | ✓ carried |
| `theo:Galois_cor`: (absent) `Y ∖ S` semi-locally simply connected | ✓ carried (DEC-70; the omission is a finding): `\widetilde Y^S` exists only under it (`prop:universality`), and slsc in `Y` does not imply it (`GX.harmonicArchipelago_compl_empty`) |
| `theo:Galois_cor`: second countability (used by the cited `prop:Galoisian_semilocal`) | ⚠ weakened: not needed (finding) |
| `theo:Galois_cor`: coverings `X` | ✓ T2, LPC, first countable (§3 standing, as `prop:universality`) |
| `def:semi_locally_simple_connectedness`: `X` Hausdorff, connected, LPC; `U` open; `x ∈ closure U` | ⚠ weakened: not used by the definition (defined for every set `U` and point `x`; `IsSLSCInCC` asks `U` dense, so every `x` is in `closure U`) |
| `prop:Galoisian_semilocal`, `theo:Galois_cor`: (ii) / the hypothesis "`Y ∖ S` slsc in `Y`" | ✓ literal `GX.IsSLSCInCC` (DEC-55); the homotopy proofs apply through `GX.isSLSCInCC_iff` (`Y ∖ S` open, slsc, `Y` LPC) |
| `rem:simple_cases`: codimension `≥ 2` | ⚠ weakened: not needed for the linear or simplicial model (finding) |
| `rem:simple_cases`: simplicial `X`, `U` dense and locally connected | ⚠ weakened: local connectedness and dimension not used; `U` dense |
| `rem:simple_cases`: simplicial `X` | ✓ DEC-57: a LOCALLY FINITE geometric complex in a real normed space, subspace topology; facets = closed faces |
| `rem:simple_cases`: codimension-`≥ 2` submanifold | ✓ DEC-57: LOCALLY FLAT (flat charts at points of `X ∖ U`, ordinary charts inside `U`), in any real normed model space |
| `rem:simple_cases`: a basis of neighbourhoods `V` | ⚠ weakened: one neighbourhood `V` per point (`GX.isSLSCInCC_of_local_nhds`, `X` locally connected as the standing LPC gives; with open `V` no hypothesis, `GX.isSLSCInCC_of_local`) |

## SCOPE (disclosed)

(a) DEC-57: `def:branched_covering_galoisian_group`'s "Galoisian covering" is a deck-transitive
connected surjective covering of a portly `O ⊆ Y` (the setting of `rem:one_could_sum_up`); `p` is
quasi-Galoisian (`GX.IsQuasiGaloisian`: `p⁻¹(O) → O` deck-transitive for some portly
`O ⊆ ord(Y)`) iff it is the completion of such a covering (both directions proved,
`GX.isQuasiGaloisian_of_isSpreadCompletion`, `GX.IsQuasiGaloisian.exists_isSpreadCompletion`).
`lem:dense_orbits`, `prop:Galoisian_fiber` and `lem:alternative_countable` take
`GX.IsQuasiGaloisian` as hypothesis. (b) DEC-55: "almost trivial" is the literal compact-open
notion `GX.AlmostTrivialCC`, and `def:semi_locally_simple_connectedness` is `GX.IsSLSCAtCC`,
`GX.IsSLSCInCC` (defined at every `x`; the paper: `x ∈ closure U`, which `IsSLSCInCC` makes all
`x` by density). The homotopy forms `GX.IsSLSCAt`, `GX.IsSLSCIn` (built on `GX.AlmostTrivial`)
always imply them (`GX.IsSLSCIn.isSLSCInCC`) and are equivalent to them for `U` open and
semilocally simply connected in a locally path-connected space (`GX.isSLSCInCC_iff`, from
`GX.almostTrivialCC_iff`) — the situation `U = Y ∖ S` of `prop:Galoisian_semilocal` and
`theo:Galois_cor`, whose homotopy arguments (the paper's own) are run on the homotopy form.
(c) DEC-57: `prop:Galoisian_fiber`'s basis is of OPEN connected neighbourhoods (as in
`prop:spread_fiber`), `≃` is a homeomorphism onto the projective limit `GX.GaloisThread` of the
discrete `Γ/Γ_{Û_U}`. (d) `lem:alternative_countable`: the paper's branching-number dichotomy is
replaced by Baire's theorem on the completely metrizable fibre
(`GX.isCompletelyMetrizableSpace_fiber`): a countable fibre has an isolated point, and dense orbits
of homeomorphisms make every point isolated. (e) `rem:definition_semi_locally_simply_connected`:
only "slsc ⇒ slsc in itself" holds (`GX.isSLSCInCC_univ_of_semilocallySimplyConnected`, the
corrected statement); the converse fails for the harmonic archipelago `GX.HarmonicArchipelago`
(a Hausdorff, path-connected, locally path-connected, metrizable — NOT compact — subspace of
`ℂ × ℝ = ℝ³`): every loop is homotopic into every neighbourhood of the base point, so its loops
are almost trivial in the homotopy form and a fortiori in the literal one
(`GX.harmonicArchipelago_isSLSCInCC`), but the small loops `GX.archLoop` are not null-homotopic
(`GX.archLoop_not_homotopic`, `GX.harmonicArchipelago_not_semilocallySimplyConnected`); the
printed "iff" is refuted as a statement, `GX.not_semilocallySimplyConnected_of_isSLSCInCC_univ`. (f) `rem:simple_cases` (DEC-57): proved for complements of closed proper linear
subspaces of a real normed space, transported to closed sets `X ∖ U` which are locally flat: every
point of `X` has an open chart `V ≃ₜ E` which is either contained in `U` or carries `V ∖ U` onto
a closed proper linear subspace (`GX.isSLSCInCC_of_locally_linear`; points of `U` far from `X ∖ U`
use the first alternative, via `GX.isSLSCIn_univ_of_normedSpace`, and `X ∖ U = ∅` is allowed).
Simplicial case (`GX.isSLSCInCC_compl_faces_of_locallyFinite`, finite case
`GX.isSLSCInCC_compl_faces`): `X = |K|` for a LOCALLY FINITE geometric simplicial complex `K` of a
real normed space (mathlib's `Geometry.SimplicialComplex`, closed faces locally finite in `E`,
subspace topology), `X ∖ U` a union of closed faces of `K` (DEC-57: facets = closed faces; maximal
faces would make `U` non-dense in a pure complex), `U` dense; no dimension condition is needed
(radial contraction in the closed star, `GX.isSLSCAt_of_radial_contraction`). The second item
(`GX.isSLSCInCC_of_local_nhds`) is proved directly in the literal form: `g ↦ f ∘ g` is continuous
for the compact-open topologies, so almost triviality pushes forward along the inclusion
`V ↪ X` (`GX.AlmostTrivialCC.map`), and the connected open neighbourhood in `X` is a component of
`O ∩ int V` (`X` locally connected). The first item's proofs produce homotopies and pass to the
literal form by `GX.IsSLSCIn.isSLSCInCC`. Outside the rulings, NOT stated: complexes which are not
locally finite, or carry the weak topology, and codimension-`≥ 2` topological submanifolds which
are not locally flat (e.g. wild arcs in `ℝ³`). (g) `theo:Galois_cor`: the normality equivalence
is proved for EVERY `H` with `H\widetilde Y^S ≃ X` over `Y`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Filter Topology Function unitInterval

namespace GX

attribute [local instance] Classical.propDecidable

set_option linter.unusedSectionVars false

universe u v

section General

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-! ### `def:automorphisms_spread` -/

section Defs

variable (p : X → Y)

/-- `def:automorphisms_spread`. The stabilizer `Γ_x` of `x` in `Γ(X/Y) = Deck p`. -/
def deckStab (x : X) : Subgroup (Deck p) where
  carrier := {φ | (φ : X ≃ₜ X) x = x}
  mul_mem' {φ ψ} hφ hψ := by
    simp only [mem_setOf_eq, Subgroup.coe_mul, Homeomorph.mul_apply] at *
    rw [hψ, hφ]
  one_mem' := rfl
  inv_mem' {φ} hφ := by
    simp only [mem_setOf_eq, InvMemClass.coe_inv, Homeomorph.inv_apply] at *
    rw [Homeomorph.symm_apply_eq, hφ]

/-- `def:automorphisms_spread`. The set-wise stabilizer `Γ_U` of `U ⊆ X` in `Γ(X/Y)`. -/
def deckSetStab (U : Set X) : Subgroup (Deck p) where
  carrier := {φ | (φ : X ≃ₜ X) '' U = U}
  mul_mem' {φ ψ} hφ hψ := by
    simp only [mem_setOf_eq, Subgroup.coe_mul] at *
    rw [show ⇑((φ : X ≃ₜ X) * (ψ : X ≃ₜ X)) = (φ : X ≃ₜ X) ∘ (ψ : X ≃ₜ X) from rfl, image_comp,
      hψ, hφ]
  one_mem' := image_id _
  inv_mem' {φ} hφ := by
    simp only [mem_setOf_eq, InvMemClass.coe_inv] at *
    conv_lhs => rw [← hφ]
    exact (φ : X ≃ₜ X).toEquiv.symm_image_image U

/-- A deck transformation lies over `Y`. -/
theorem deck_apply {φ : X ≃ₜ X} (hφ : φ ∈ deckGroup p) (x : X) : p (φ x) = p x :=
  congrFun hφ x

/-- A deck transformation preserves every `p⁻¹(U)`. -/
theorem deck_image_preimage {φ : X ≃ₜ X} (hφ : φ ∈ deckGroup p) (U : Set Y) :
    φ '' (p ⁻¹' U) = p ⁻¹' U := by
  ext z
  refine ⟨?_, fun hz => ⟨φ.symm z, ?_, φ.apply_symm_apply z⟩⟩
  · rintro ⟨w, hw, rfl⟩
    show p (φ w) ∈ U
    rw [deck_apply p hφ]; exact hw
  · show p (φ.symm z) ∈ U
    have := deck_apply p (inv_mem hφ) z
    rw [Homeomorph.inv_apply] at this
    rw [this]; exact hz

/-- A deck transformation maps the component of `x` in `p⁻¹(U)` onto that of `φ x`. -/
theorem deck_image_connectedComponentIn {φ : X ≃ₜ X} (hφ : φ ∈ deckGroup p) {U : Set Y}
    {x : X} (hx : p x ∈ U) :
    φ '' connectedComponentIn (p ⁻¹' U) x = connectedComponentIn (p ⁻¹' U) (φ x) := by
  rw [φ.image_connectedComponentIn (show x ∈ p ⁻¹' U from hx), deck_image_preimage p hφ]

/-- A deck transformation preserves the fibres. -/
theorem deck_mem_fiber {φ : X ≃ₜ X} (hφ : φ ∈ deckGroup p) {b : Y} {x : X}
    (hx : x ∈ p ⁻¹' {b}) : φ x ∈ p ⁻¹' {b} := by
  show p (φ x) = b
  rw [deck_apply p hφ]; exact hx

end Defs

/-- `def:automorphisms_spread`, "a spread automorphism is just an automorphism in `Spread`":
an automorphism `φ` of `p` is the automorphism `(id_Y, φ)` of the object `p` of `Spread`. -/
def deckToSpreadIso (S : Spread.{u}) (φ : Deck S.p) : CategoryTheory.Iso S S where
  hom := ⟨⟨φ.1, φ.1.continuous⟩, ContinuousMap.id _, fun x => deck_apply S.p φ.2 x⟩
  inv := ⟨⟨φ.1.symm, φ.1.symm.continuous⟩, ContinuousMap.id _, fun x => by
    have := deck_apply S.p (inv_mem φ.2) x
    rw [Homeomorph.inv_apply] at this
    exact this⟩
  hom_inv_id := Spread.Hom.ext (ContinuousMap.ext fun x => φ.1.symm_apply_apply x) rfl
  inv_hom_id := Spread.Hom.ext (ContinuousMap.ext fun x => φ.1.apply_symm_apply x) rfl

theorem deckToSpreadIso_hom_f (S : Spread.{u}) (φ : Deck S.p) :
    (deckToSpreadIso S φ).hom.f = ContinuousMap.id _ := rfl

theorem deckToSpreadIso_hom_g (S : Spread.{u}) (φ : Deck S.p) (x : S.X) :
    (deckToSpreadIso S φ).hom.g x = (φ : S.X ≃ₜ S.X) x := rfl

/-- Conversely, an automorphism of `S` in `Spread` over `id_Y` is a spread automorphism. -/
theorem Spread.Iso.homeoX_mem_deckGroup {S : Spread.{u}} (e : CategoryTheory.Iso S S)
    (he : e.hom.f = ContinuousMap.id _) : Spread.Iso.homeoX e ∈ deckGroup S.p := by
  funext x
  have := e.hom.comm x
  rw [he] at this
  exact this

/-! ### `def:branched_covering_galoisian_group` -/

/-- The automorphisms of `p` act transitively on its fibres. -/
def IsDeckTransitive (p : X → Y) : Prop :=
  ∀ x x', p x = p x' → ∃ φ ∈ deckGroup p, φ x = x'

/-- `def:branched_covering_galoisian_group`. A branched covering is *Galoisian* if its group
of automorphisms acts transitively on its fibres. -/
def IsGaloisian (p : X → Y) : Prop :=
  IsBranchedCovering p ∧ IsDeckTransitive p

/-- **`def:branched_covering_galoisian_group`** (DEC-57). A branched covering is *quasi-Galoisian* if it is
the completion of a Galoisian covering: over some portly `O ⊆ ord(Y)` its restriction
`p⁻¹(O) → O` (a covering of which `p` is the completion, `GX.IsBranchedCovering.restrict_isCoveringMap`)
has a group of automorphisms acting transitively on its fibres. -/
def IsQuasiGaloisian (p : X → Y) : Prop :=
  IsBranchedCovering p ∧
    ∃ O : Set Y, IsPortly O ∧ O ⊆ ordY p ∧ IsDeckTransitive (O.restrictPreimage p)

/-! ### Maps over `Y` agreeing at one ordinary point -/

/-- Two continuous maps over `Y` from a branched covering `q` to a branched covering `p` agreeing
at one point over a portly `O ⊆ ord_p(Y)` are equal (`X` Hausdorff). -/
theorem eq_of_comp_eq_of_mem_portly [T2Space X] {Z : Type*} [TopologicalSpace Z] {q : Z → Y}
    {p : X → Y} (hq : IsBranchedCovering q) (hp : IsBranchedCovering p) {O : Set Y}
    (hO : IsPortly O) (hOp : O ⊆ ordY p) {F₁ F₂ : Z → X} (h₁ : Continuous F₁)
    (h₂ : Continuous F₂) (hc₁ : ∀ z, p (F₁ z) = q z) (hc₂ : ∀ z, p (F₂ z) = q z) {z₀ : Z}
    (hz₀ : q z₀ ∈ O) (h : F₁ z₀ = F₂ z₀) : F₁ = F₂ := by
  haveI := hp.isSpread.locallyConnectedSpace
  haveI := hq.connectedSpace_source
  have hA := hq.isPortly_preimage hO
  haveI : PreconnectedSpace (q ⁻¹' O) := isPreconnected_iff_preconnectedSpace.1 hA.isPreconnected
  have cov : IsCoveringMap (O.restrictPreimage p) :=
    ((isCoveringMapOn_ordY hp.isSpread.continuous).mono hOp).isCoveringMap_restrictPreimage
  let g₁ : q ⁻¹' O → p ⁻¹' O := fun a => ⟨F₁ a, by show p (F₁ a) ∈ O; rw [hc₁]; exact a.2⟩
  let g₂ : q ⁻¹' O → p ⁻¹' O := fun a => ⟨F₂ a, by show p (F₂ a) ∈ O; rw [hc₂]; exact a.2⟩
  have hg₁ : Continuous g₁ := (h₁.comp continuous_subtype_val).subtype_mk _
  have hg₂ : Continuous g₂ := (h₂.comp continuous_subtype_val).subtype_mk _
  have he : O.restrictPreimage p ∘ g₁ = O.restrictPreimage p ∘ g₂ := by
    funext a
    apply Subtype.ext
    show p (F₁ a) = p (F₂ a)
    rw [hc₁, hc₂]
  have heq := cov.eq_of_comp_eq hg₁ hg₂ he ⟨z₀, hz₀⟩ (Subtype.ext h)
  refine Continuous.ext_on hA.dense h₁ h₂ fun z hz => ?_
  exact congrArg Subtype.val (congrFun heq ⟨z, hz⟩)

/-- Two automorphisms of a branched covering agreeing at one ordinary point are equal. -/
theorem deck_eq_of_apply_eq [T2Space X] {p : X → Y} (hp : IsBranchedCovering p)
    {φ ψ : X ≃ₜ X} (hφ : φ ∈ deckGroup p) (hψ : ψ ∈ deckGroup p) {x₀ : X}
    (hx₀ : p x₀ ∈ ordY p) (h : φ x₀ = ψ x₀) : φ = ψ := by
  have := eq_of_comp_eq_of_mem_portly hp hp hp.isPortly_ordY subset_rfl φ.continuous ψ.continuous
    (deck_apply p hφ) (deck_apply p hψ) hx₀ h
  exact Homeomorph.ext (congrFun this)

/-! ### `lem:branched_covering_group_automorphisms`, `cor:branched_covering` -/

section Restrict

variable (p : X → Y) (U : Set Y)

/-- The restriction of an automorphism of `p` to an automorphism of `p⁻¹(U) → U`. -/
def deckRestrict : Deck p →* Deck (U.restrictPreimage p) where
  toFun φ := ⟨(φ : X ≃ₜ X).subtype (p := (· ∈ p ⁻¹' U)) (q := (· ∈ p ⁻¹' U)) fun x => by
      simp only [mem_preimage, deck_apply p φ.2], by
    funext z
    apply Subtype.ext
    show p ((φ : X ≃ₜ X) z) = p z
    exact deck_apply p φ.2 z⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem deckRestrict_apply (φ : Deck p) (z : p ⁻¹' U) :
    (((deckRestrict p U φ : Deck (U.restrictPreimage p)) : p ⁻¹' U ≃ₜ p ⁻¹' U) z : X) =
      (φ : X ≃ₜ X) z := rfl

end Restrict

variable {p : X → Y}

/-- Extension of an automorphism of `p⁻¹(U) → U` to `X`, `U` portly (functoriality of the
completion). -/
theorem exists_deck_extend [T2Space X] [T2Space Y] [LocallyConnectedSpace Y]
    (hp : IsBranchedCovering p) {U : Set Y} (hU : IsPortly U) (ψ : Deck (U.restrictPreimage p)) :
    ∃ φ : Deck p, deckRestrict p U φ = ψ := by
  have h := (hp.isSpreadCompletion_preimage hU).toIsFoxCompletion
  have hcomm : ∀ (θ : Deck (U.restrictPreimage p)) (z : p ⁻¹' U),
      (p ∘ ((↑) : p ⁻¹' U → X)) ((θ : p ⁻¹' U ≃ₜ p ⁻¹' U) z) =
        id ((p ∘ ((↑) : p ⁻¹' U → X)) z) := fun θ z =>
    congrArg Subtype.val (congrFun θ.2 z)
  obtain ⟨G, ⟨hGc, hGp, hGι⟩, -⟩ := h.existsUnique_extend h continuous_id
    (ψ : p ⁻¹' U ≃ₜ p ⁻¹' U).continuous (hcomm ψ)
  obtain ⟨G', ⟨hG'c, hG'p, hG'ι⟩, -⟩ := h.existsUnique_extend h continuous_id
    ((ψ⁻¹ : Deck (U.restrictPreimage p)) : p ⁻¹' U ≃ₜ p ⁻¹' U).continuous (hcomm ψ⁻¹)
  obtain ⟨G₀, -, huniq⟩ := h.existsUnique_extend h continuous_id (g := id) continuous_id
    (fun z => rfl)
  have hGG' : G ∘ G' = id := by
    have e1 := huniq (G ∘ G') ⟨hGc.comp hG'c, fun x => by simp [hGp, hG'p], fun z => by
      simp only [comp_apply, hG'ι, hGι, id]
      congr 1
      show (ψ : p ⁻¹' U ≃ₜ p ⁻¹' U) ((ψ : p ⁻¹' U ≃ₜ p ⁻¹' U).symm z) = z
      exact Homeomorph.apply_symm_apply _ _⟩
    have e2 := huniq id ⟨continuous_id, fun x => rfl, fun z => rfl⟩
    rw [e1, e2]
  have hG'G : G' ∘ G = id := by
    have e1 := huniq (G' ∘ G) ⟨hG'c.comp hGc, fun x => by simp [hGp, hG'p], fun z => by
      simp only [comp_apply, hG'ι, hGι, id]
      congr 1
      show (ψ : p ⁻¹' U ≃ₜ p ⁻¹' U).symm ((ψ : p ⁻¹' U ≃ₜ p ⁻¹' U) z) = z
      exact Homeomorph.symm_apply_apply _ _⟩
    have e2 := huniq id ⟨continuous_id, fun x => rfl, fun z => rfl⟩
    rw [e1, e2]
  let Φ : X ≃ₜ X :=
    { toFun := G
      invFun := G'
      left_inv := congrFun hG'G
      right_inv := congrFun hGG'
      continuous_toFun := hGc
      continuous_invFun := hG'c }
  refine ⟨⟨Φ, funext fun x => hGp x⟩, Subtype.ext (Homeomorph.ext fun z => Subtype.ext ?_)⟩
  exact hGι z

/-- **`lem:branched_covering_group_automorphisms`** (`RamcovGX.tex:1435`). For `U` portly in `Y`,
restriction is an isomorphism `Γ(X/Y) ≃* Γ(p⁻¹(U)/U)`. -/
def deckRestrictEquiv [T2Space X] [T2Space Y] [LocallyConnectedSpace Y]
    (hp : IsBranchedCovering p) {U : Set Y} (hU : IsPortly U) :
    Deck p ≃* Deck (U.restrictPreimage p) :=
  MulEquiv.ofBijective (deckRestrict p U) ⟨fun φ ψ h => by
    have hd := (hp.isPortly_preimage hU).dense
    refine Subtype.ext (Homeomorph.ext fun x => ?_)
    have := Continuous.ext_on hd (φ : X ≃ₜ X).continuous (ψ : X ≃ₜ X).continuous fun z hz => by
      have := congrArg (fun θ : Deck (U.restrictPreimage p) =>
        ((θ : p ⁻¹' U ≃ₜ p ⁻¹' U) ⟨z, hz⟩ : X)) h
      exact this
    exact congrFun this x, fun ψ => exists_deck_extend hp hU ψ⟩

theorem deckRestrictEquiv_apply [T2Space X] [T2Space Y] [LocallyConnectedSpace Y]
    (hp : IsBranchedCovering p) {U : Set Y} (hU : IsPortly U) (φ : Deck p) (z : p ⁻¹' U) :
    (((deckRestrictEquiv hp hU φ : Deck (U.restrictPreimage p)) : p ⁻¹' U ≃ₜ p ⁻¹' U) z : X) =
      (φ : X ≃ₜ X) z := rfl

/-- **`lem:branched_covering_group_automorphisms`**, the paper's equality: every automorphism of
`p` preserves `p⁻¹(U)` and restricts to one of `p⁻¹(U) → U` (`GX.deckRestrict`); every
automorphism of `p⁻¹(U) → U` is the restriction of exactly one automorphism of `p`. -/
theorem branched_covering_group_automorphisms [T2Space X] [T2Space Y] [LocallyConnectedSpace Y]
    (hp : IsBranchedCovering p) {U : Set Y} (hU : IsPortly U) :
    (∀ φ ∈ deckGroup p, φ '' (p ⁻¹' U) = p ⁻¹' U) ∧
      ∀ ψ : Deck (U.restrictPreimage p), ∃! φ : Deck p, deckRestrict p U φ = ψ :=
  ⟨fun _ hφ => deck_image_preimage p hφ U, fun ψ =>
    (deckRestrictEquiv hp hU).bijective.existsUnique ψ⟩

/-- **`cor:branched_covering`** (`RamcovGX.tex:1441`): `Γ(X/Y) = Γ(ord(X)/ord(Y))`. -/
def deckOrdEquiv [T2Space X] [T2Space Y] [LocallyConnectedSpace Y]
    (hp : IsBranchedCovering p) : Deck p ≃* Deck ((ordY p).restrictPreimage p) :=
  deckRestrictEquiv hp hp.isPortly_ordY

/-- `Γ(X/Y)` acts transitively over `O` iff `Γ(p⁻¹(O)/O)` does (`O` portly). -/
theorem isDeckTransitive_restrict_iff [T2Space X] [T2Space Y] [LocallyConnectedSpace Y]
    (hp : IsBranchedCovering p) {O : Set Y} (hO : IsPortly O) :
    IsDeckTransitive (O.restrictPreimage p) ↔
      ∀ x x', p x = p x' → p x ∈ O → ∃ φ ∈ deckGroup p, φ x = x' := by
  constructor
  · intro h x x' hxx hx
    obtain ⟨ψ, hψ, hψx⟩ := h ⟨x, hx⟩ ⟨x', show p x' ∈ O from hxx ▸ hx⟩ (Subtype.ext hxx)
    obtain ⟨φ, hφ⟩ := exists_deck_extend hp hO ⟨ψ, hψ⟩
    refine ⟨φ.1, φ.2, ?_⟩
    have := congrArg (fun θ : Deck (O.restrictPreimage p) =>
      ((θ : p ⁻¹' O ≃ₜ p ⁻¹' O) ⟨x, hx⟩ : X)) hφ
    exact this.trans (congrArg Subtype.val hψx)
  · intro h z z' hzz
    obtain ⟨φ, hφ, hφz⟩ := h z z' (congrArg Subtype.val hzz) z.2
    refine ⟨(deckRestrict p O ⟨φ, hφ⟩).1, (deckRestrict p O ⟨φ, hφ⟩).2, Subtype.ext ?_⟩
    exact hφz

/-- A quasi-Galoisian branched covering: `Γ(X/Y)` acts transitively on the fibres over a portly
subset of `ord(Y)`. -/
theorem IsQuasiGaloisian.exists_transitive [T2Space X] [T2Space Y] [LocallyConnectedSpace Y]
    (hp : IsQuasiGaloisian p) :
    ∃ O : Set Y, IsPortly O ∧ O ⊆ ordY p ∧
      ∀ x x', p x = p x' → p x ∈ O → ∃ φ ∈ deckGroup p, φ x = x' := by
  obtain ⟨hbc, O, hO, hOp, htr⟩ := hp
  exact ⟨O, hO, hOp, (isDeckTransitive_restrict_iff hbc hO).1 htr⟩

/-- Characterisation of quasi-Galoisian coverings by `Γ(X/Y)` itself. -/
theorem isQuasiGaloisian_iff [T2Space X] [T2Space Y] [LocallyConnectedSpace Y] :
    IsQuasiGaloisian p ↔ IsBranchedCovering p ∧ ∃ O : Set Y, IsPortly O ∧ O ⊆ ordY p ∧
      ∀ x x', p x = p x' → p x ∈ O → ∃ φ ∈ deckGroup p, φ x = x' :=
  ⟨fun h => ⟨h.1, h.exists_transitive⟩, fun ⟨hbc, O, hO, hOp, htr⟩ =>
    ⟨hbc, O, hO, hOp, (isDeckTransitive_restrict_iff hbc hO).2 htr⟩⟩

/-- `def:branched_covering_galoisian_group`, "the completion of a Galoisian covering" read
literally: the completion `(p, ι)` of a deck-transitive connected covering `π : E → O` of a portly
`O ⊆ Y` is quasi-Galoisian. -/
theorem isQuasiGaloisian_of_isSpreadCompletion [T2Space X] [LocPathConnectedSpace X] [T2Space Y]
    [LocPathConnectedSpace Y] [FirstCountableTopology Y] {O : Set Y} (hO : IsPortly O)
    {E : Type*} [TopologicalSpace E] [ConnectedSpace E] {π : E → O} (hπ : IsCoveringMap π)
    (hπs : Surjective π) (hπG : IsDeckTransitive π) {ι : E → X}
    (h : IsSpreadCompletion (fun e => (π e : Y)) p ι) : IsQuasiGaloisian p := by
  obtain ⟨hbc, hpb, hpre⟩ := isBranchedCovering_of_isSpreadCompletion hO hπ hπs h
  have hOp : O ⊆ ordY p := fun y hy => by
    by_contra h'
    exact hpb h' hy
  set ιO : E ≃ₜ p ⁻¹' O := h.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hpre.symm)
  have hιO : ∀ e, (ιO e : X) = ι e := fun e => rfl
  refine ⟨hbc, O, hO, hOp, fun z z' hzz => ?_⟩
  obtain ⟨e, rfl⟩ := ιO.surjective z
  obtain ⟨e', rfl⟩ := ιO.surjective z'
  have hee : π e = π e' := Subtype.ext (by
    have := congrArg Subtype.val hzz
    simp only [Set.restrictPreimage_coe, hιO, h.comm] at this
    exact this)
  obtain ⟨ψ, hψ, hψe⟩ := hπG e e' hee
  refine ⟨ιO.symm.trans (ψ.trans ιO), funext fun w => ?_, ?_⟩
  · obtain ⟨e₁, rfl⟩ := ιO.surjective w
    apply Subtype.ext
    simp only [comp_apply, Homeomorph.trans_apply, Homeomorph.symm_apply_apply,
      Set.restrictPreimage_coe, hιO, h.comm]
    exact congrArg Subtype.val (deck_apply π hψ e₁)
  · simp only [Homeomorph.trans_apply, Homeomorph.symm_apply_apply, hψe]

/-- Conversely, a quasi-Galoisian branched covering is the completion of a deck-transitive
connected covering of a portly `O` (its restriction `p⁻¹(O) → O`). -/
theorem IsQuasiGaloisian.exists_isSpreadCompletion (hp : IsQuasiGaloisian p) :
    ∃ O : Set Y, IsPortly O ∧ IsCoveringMap (O.restrictPreimage p) ∧
      Surjective (O.restrictPreimage p) ∧ ConnectedSpace (p ⁻¹' O) ∧
      IsDeckTransitive (O.restrictPreimage p) ∧
      IsSpreadCompletion (fun e => (O.restrictPreimage p e : Y)) p ((↑) : p ⁻¹' O → X) := by
  obtain ⟨hbc, O, hO, hOp, htr⟩ := hp
  obtain ⟨h1, h2, h3, h4⟩ := hbc.restrict_isCoveringMap hO hOp
  exact ⟨O, hO, h1, h2, h3, htr, h4⟩

/-- A Galoisian branched covering is quasi-Galoisian. -/
theorem IsGaloisian.isQuasiGaloisian [T2Space X] [T2Space Y] [LocallyConnectedSpace Y]
    (hp : IsGaloisian p) : IsQuasiGaloisian p :=
  isQuasiGaloisian_iff.2 ⟨hp.1, ordY p, hp.1.isPortly_ordY, subset_rfl,
    fun x x' h _ => hp.2 x x' h⟩

/-! ### `rem:galois_quotient`: quotients by groups of homeomorphisms -/

/-- The orbit relation of a group `H` of homeomorphisms of `X`. -/
def subgroupOrbitSetoid (H : Subgroup (X ≃ₜ X)) : Setoid X where
  r x x' := ∃ φ ∈ H, φ x = x'
  iseqv := ⟨fun _ => ⟨1, H.one_mem, rfl⟩, fun ⟨φ, hφ, h⟩ => ⟨φ⁻¹, H.inv_mem hφ, by
    rw [← h, Homeomorph.inv_apply, Homeomorph.symm_apply_apply]⟩,
    fun ⟨φ, hφ, h⟩ ⟨ψ, hψ, h'⟩ => ⟨ψ * φ, H.mul_mem hψ hφ, by
      rw [Homeomorph.mul_apply, h, h']⟩⟩

/-- The quotient `H\X` of `X` by a group `H` of homeomorphisms, with the quotient topology. -/
abbrev HomeoQuotient (H : Subgroup (X ≃ₜ X)) : Type _ := Quotient (subgroupOrbitSetoid H)

/-- The projection `X → H\X`. -/
abbrev homeoQuotientMk (H : Subgroup (X ≃ₜ X)) (x : X) : HomeoQuotient H :=
  Quotient.mk (subgroupOrbitSetoid H) x

/-- A continuous open surjection whose fibres are the `H`-orbits induces a homeomorphism
`H\X ≃ₜ Y`. -/
theorem exists_homeomorph_homeoQuotient {H : Subgroup (X ≃ₜ X)} {q : X → Y} (hc : Continuous q)
    (ho : IsOpenMap q) (hs : Surjective q) (hfib : ∀ x x', q x = q x' ↔ ∃ φ ∈ H, φ x = x') :
    ∃ h : HomeoQuotient H ≃ₜ Y, ∀ x, h (homeoQuotientMk H x) = q x := by
  let f : HomeoQuotient H → Y := Quotient.lift q fun a b hab => (hfib a b).2 hab
  have hf : Bijective f := by
    refine ⟨fun a b hab => ?_, fun y => ?_⟩
    · induction a using Quotient.inductionOn with | h a => ?_
      induction b using Quotient.inductionOn with | h b => ?_
      exact Quotient.sound ((hfib a b).1 hab)
    · obtain ⟨x, rfl⟩ := hs y
      exact ⟨homeoQuotientMk H x, rfl⟩
  have hfc : Continuous f := hc.quotient_lift _
  have hfo : IsOpenMap f := by
    intro W hW
    have hW' : IsOpen (homeoQuotientMk H ⁻¹' W) := hW.preimage continuous_quotient_mk'
    have : f '' W = q '' (homeoQuotientMk H ⁻¹' W) := by
      ext y
      constructor
      · rintro ⟨a, ha, rfl⟩
        induction a using Quotient.inductionOn with | h a => exact ⟨a, ha, rfl⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨_, ha, rfl⟩
    rw [this]; exact ho _ hW'
  exact ⟨(Equiv.ofBijective f hf).toHomeomorphOfContinuousOpen hfc hfo, fun _ => rfl⟩

/-- **`rem:galois_quotient`** (`RamcovGX.tex:1431`). A Galoisian branched covering induces a
homeomorphism `Γ(X/Y)\X → Y`. -/
theorem galois_quotient [T1Space Y] [LocPathConnectedSpace Y] [FirstCountableTopology Y]
    (hp : IsGaloisian p) :
    ∃ h : HomeoQuotient (deckGroup p) ≃ₜ Y, ∀ x, h (homeoQuotientMk _ x) = p x :=
  exists_homeomorph_homeoQuotient hp.1.isSpread.continuous (spread_connected_image hp.1).1
    hp.1.surjective fun x x' => ⟨fun h => hp.2 x x' h, fun ⟨φ, hφ, h⟩ => by
      rw [← h, deck_apply p hφ]⟩

/-! ### `lem:dense_orbits` -/

/-- A group `G` of automorphisms of a branched covering `q`, transitive on the fibres over a dense
`D`, acts on every fibre with dense orbits (neighbourhood form). -/
theorem exists_mem_nhds_of_transitive {Z B : Type*} [TopologicalSpace Z] [TopologicalSpace B]
    [T1Space B] [LocPathConnectedSpace B] [FirstCountableTopology B] {q : Z → B}
    (hq : IsBranchedCovering q) {G : Subgroup (Z ≃ₜ Z)} (hG : G ≤ deckGroup q) {D : Set B}
    (hD : Dense D) (htr : ∀ z z', q z = q z' → q z ∈ D → ∃ g ∈ G, g z = z') {z z' : Z}
    (hzz : q z = q z') {N : Set Z} (hN : N ∈ 𝓝 z') : ∃ g ∈ G, g z ∈ N := by
  obtain ⟨O, hON, hO, hz'O⟩ := mem_nhds_iff.1 hN
  obtain ⟨U, hU, hz'U, hsub⟩ := (isSpread_iff.1 hq.isSpread).2.2 z' O hO hz'O
  set U' := connectedComponentIn U (q z')
  have hU' : IsOpen U' := hU.connectedComponentIn
  have hU'c : IsPreconnected U' := isPreconnected_connectedComponentIn
  have hz'U' : q z' ∈ U' := mem_connectedComponentIn hz'U
  have hzU' : q z ∈ U' := hzz ▸ hz'U'
  set V := connectedComponentIn (q ⁻¹' U') z
  set V' := connectedComponentIn (q ⁻¹' U') z'
  have hV'N : V' ⊆ N := ((connectedComponentIn_mono _
    (preimage_mono (connectedComponentIn_subset U (q z')))).trans hsub).trans hON
  obtain ⟨y, hyU, hyD⟩ := hD.inter_open_nonempty U' hU' ⟨_, hz'U'⟩
  have himg := (spread_connected_image hq).2 U' hU' hU'c
  obtain ⟨w, hwV, hwy⟩ : y ∈ q '' V := by
    rw [himg V (isCompOf_connectedComponentIn hzU')]; exact hyU
  obtain ⟨w', hw'V, hw'y⟩ : y ∈ q '' V' := by
    rw [himg V' (isCompOf_connectedComponentIn hz'U')]; exact hyU
  obtain ⟨g, hgG, hgw⟩ := htr w w' (hwy.trans hw'y.symm) (hwy ▸ hyD)
  have hgq := hG hgG
  refine ⟨g, hgG, hV'N ?_⟩
  have h1 : g '' V = connectedComponentIn (q ⁻¹' U') (g z) := deck_image_connectedComponentIn q hgq hzU'
  have h2 : V = connectedComponentIn (q ⁻¹' U') w := connectedComponentIn_eq hwV
  have h3 : V' = connectedComponentIn (q ⁻¹' U') w' := connectedComponentIn_eq hw'V
  have h4 : g '' V = V' := by
    rw [h2, deck_image_connectedComponentIn q hgq (show q w ∈ U' from hwy ▸ hyU), hgw, ← h3]
  rw [← h4, h1]
  exact mem_connectedComponentIn (show q (g z) ∈ U' by rw [deck_apply q hgq]; exact hzU')

/-- The orbit of `x` under a group of homeomorphisms, as a subset of the fibre `p⁻¹(p x)`. -/
def fiberOrbit (p : X → Y) (H : Subgroup (X ≃ₜ X)) (x : X) : Set (p ⁻¹' {p x}) :=
  {z | ∃ φ ∈ H, φ x = z}

/-- Density in the fibre from the neighbourhood form. -/
theorem dense_fiberOrbit_of {H : Subgroup (X ≃ₜ X)} {x : X}
    (h : ∀ z, p z = p x → ∀ N ∈ 𝓝 z, ∃ φ ∈ H, φ x ∈ N) (hH : H ≤ deckGroup p) :
    Dense (fiberOrbit p H x) := by
  rw [dense_iff_inter_open]
  rintro W hW ⟨z, hz⟩
  obtain ⟨W', hW', rfl⟩ := isOpen_induced_iff.1 hW
  obtain ⟨φ, hφ, hφx⟩ := h z z.2 W' (hW'.mem_nhds hz)
  have hm : φ x ∈ p ⁻¹' {p x} := deck_mem_fiber p (hH hφ) rfl
  exact ⟨⟨φ x, hm⟩, hφx, φ, hφ, rfl⟩

/-- **`lem:dense_orbits`** (`RamcovGX.tex:1469`; quasi-Galoisian as ruled by DEC-57, SCOPE (a)). For a
quasi-Galoisian branched covering, the orbit `Γ(X/Y) x̂` is dense in the fibre `p⁻¹(p x̂)`. -/
theorem dense_orbits [T2Space X] [T2Space Y] [LocPathConnectedSpace Y]
    [FirstCountableTopology Y] (hp : IsQuasiGaloisian p) (x : X) :
    Dense (fiberOrbit p (deckGroup p) x) := by
  obtain ⟨O, hO, -, htr⟩ := hp.exists_transitive
  exact dense_fiberOrbit_of (fun z hz N hN =>
    exists_mem_nhds_of_transitive hp.1 le_rfl hO.dense htr hz.symm hN) le_rfl

/-- In a discrete fibre, an action with dense orbits is transitive. -/
theorem exists_eq_of_discreteTopology_fiber {H : Subgroup (X ≃ₜ X)} (hH : H ≤ deckGroup p)
    {b : Y} (hdisc : DiscreteTopology (p ⁻¹' {b}))
    (hdense : ∀ x x', p x = p x' → ∀ N ∈ 𝓝 x', ∃ φ ∈ H, φ x ∈ N) {x x' : X} (hx : p x = b)
    (hx' : p x' = b) : ∃ φ ∈ H, φ x = x' := by
  have ho : IsOpen ({⟨x', hx'⟩} : Set (p ⁻¹' {b})) := isOpen_discrete _
  obtain ⟨N, hN, hNe⟩ := isOpen_induced_iff.1 ho
  have hx'N : x' ∈ N := by
    have : (⟨x', hx'⟩ : p ⁻¹' {b}) ∈ Subtype.val ⁻¹' N := by rw [hNe]; rfl
    exact this
  obtain ⟨φ, hφ, hφN⟩ := hdense x x' (hx.trans hx'.symm) N (hN.mem_nhds hx'N)
  have hm : φ x ∈ p ⁻¹' {b} := deck_mem_fiber p (hH hφ) hx
  have : (⟨φ x, hm⟩ : p ⁻¹' {b}) ∈ Subtype.val ⁻¹' N := hφN
  rw [hNe] at this
  exact ⟨φ, hφ, congrArg Subtype.val this⟩

/-- Dense orbits for a quasi-Galoisian covering, neighbourhood form. -/
theorem IsQuasiGaloisian.exists_mem_nhds [T2Space X] [T2Space Y] [LocPathConnectedSpace Y]
    [FirstCountableTopology Y] (hp : IsQuasiGaloisian p) {x x' : X} (h : p x = p x')
    {N : Set X} (hN : N ∈ 𝓝 x') : ∃ φ ∈ deckGroup p, φ x ∈ N := by
  obtain ⟨O, hO, -, htr⟩ := hp.exists_transitive
  exact exists_mem_nhds_of_transitive hp.1 le_rfl hO.dense htr h hN

/-- A quasi-Galoisian covering: `Γ(X/Y)` acts transitively on the components of `p⁻¹(U)`, `U` open
connected. -/
theorem IsQuasiGaloisian.exists_image_eq [T2Space X] [T2Space Y] [LocPathConnectedSpace Y]
    [FirstCountableTopology Y] (hp : IsQuasiGaloisian p) {U : Set Y} (hU : IsOpen U)
    (hUc : IsPreconnected U) {C D : Set X} (hC : IsCompOf p U C) (hD : IsCompOf p U D) :
    ∃ φ ∈ deckGroup p, φ '' C = D := by
  obtain ⟨O, hO, -, htr⟩ := hp.exists_transitive
  obtain ⟨c, hc⟩ := hC.nonempty
  obtain ⟨y, hyU, hyO⟩ := hO.dense.inter_open_nonempty U hU ⟨p c, hC.subset hc⟩
  have himg := (spread_connected_image hp.1).2 U hU hUc
  obtain ⟨w, hwC, hwy⟩ : y ∈ p '' C := by rw [himg C hC]; exact hyU
  obtain ⟨w', hwD, hw'y⟩ : y ∈ p '' D := by rw [himg D hD]; exact hyU
  obtain ⟨φ, hφ, hφw⟩ := htr w w' (hwy.trans hw'y.symm) (hwy ▸ hyO)
  refine ⟨φ, hφ, ?_⟩
  rw [hC.eq_of_mem hwC, deck_image_connectedComponentIn p hφ (show p w ∈ U from hwy ▸ hyU), hφw,
    ← hD.eq_of_mem hwD]

/-! ### `prop:Galoisian_fiber` -/

section GaloisFiber

variable (p)

/-- The discrete space `Γ(X/Y)/Γ_{Û}`, `Û` the component of `x̂` in `p⁻¹(U)`. -/
def GaloisCoset (x : X) (U : Set Y) : Type _ :=
  Deck p ⧸ deckSetStab p (connectedComponentIn (p ⁻¹' U) x)

instance (x : X) (U : Set Y) : TopologicalSpace (GaloisCoset p x U) := ⊥

instance (x : X) (U : Set Y) : DiscreteTopology (GaloisCoset p x U) := ⟨rfl⟩

/-- The coset of `φ` in `Γ(X/Y)/Γ_{Û}`. -/
def galoisMk (x : X) (U : Set Y) (φ : Deck p) : GaloisCoset p x U :=
  (QuotientGroup.mk φ : Deck p ⧸ deckSetStab p (connectedComponentIn (p ⁻¹' U) x))

theorem galoisMk_surjective (x : X) (U : Set Y) : Surjective (galoisMk p x U) :=
  QuotientGroup.mk_surjective

instance (x : X) (U : Set Y) : Nonempty (GaloisCoset p x U) := ⟨galoisMk p x U 1⟩

theorem coe_mul_image (a b : Deck p) (s : Set X) :
    ((a * b : Deck p) : X ≃ₜ X) '' s = (a : X ≃ₜ X) '' ((b : X ≃ₜ X) '' s) := by
  rw [Subgroup.coe_mul, image_image]; rfl

theorem galoisMk_eq_iff {x : X} {U : Set Y} {a b : Deck p} :
    galoisMk p x U a = galoisMk p x U b ↔
      (a : X ≃ₜ X) '' connectedComponentIn (p ⁻¹' U) x =
        (b : X ≃ₜ X) '' connectedComponentIn (p ⁻¹' U) x := by
  set C := connectedComponentIn (p ⁻¹' U) x
  change (QuotientGroup.mk a : Deck p ⧸ deckSetStab p C) = QuotientGroup.mk b ↔ _
  rw [QuotientGroup.eq]
  show ((a⁻¹ * b : Deck p) : X ≃ₜ X) '' C = C ↔ _
  rw [coe_mul_image]
  constructor
  · intro h
    calc (a : X ≃ₜ X) '' C = (a : X ≃ₜ X) '' (((a⁻¹ : Deck p) : X ≃ₜ X) '' ((b : X ≃ₜ X) '' C)) := by
          rw [h]
      _ = ((a * a⁻¹ : Deck p) : X ≃ₜ X) '' ((b : X ≃ₜ X) '' C) := (coe_mul_image p _ _ _).symm
      _ = (b : X ≃ₜ X) '' C := by rw [mul_inv_cancel, OneMemClass.coe_one]; exact image_id _
  · intro h
    rw [← h, ← coe_mul_image, inv_mul_cancel, OneMemClass.coe_one]
    exact image_id _

/-- The component `φ(Û)` of `p⁻¹(U)` attached to a coset (`Γ(X/Y)/Γ_{Û} ≃ X_U`). -/
def galoisComp (x : X) (U : Set Y) (c : GaloisCoset p x U) : Set X :=
  Quotient.liftOn' c (fun φ : Deck p => (φ : X ≃ₜ X) '' connectedComponentIn (p ⁻¹' U) x)
    fun _ _ hab => (galoisMk_eq_iff p).1 (Quotient.sound' hab)

theorem galoisComp_mk (x : X) (U : Set Y) (φ : Deck p) :
    galoisComp p x U (galoisMk p x U φ) = (φ : X ≃ₜ X) '' connectedComponentIn (p ⁻¹' U) x :=
  rfl

theorem galoisComp_injective (x : X) (U : Set Y) : Injective (galoisComp p x U) := by
  intro c c' h
  obtain ⟨a, rfl⟩ := galoisMk_surjective p x U c
  obtain ⟨b, rfl⟩ := galoisMk_surjective p x U c'
  exact (galoisMk_eq_iff p).2 h

/-- The natural map `Γ/Γ_{Û_U} → Γ/Γ_{Û_V}` (`U ⊆ V`) is well defined. -/
theorem deckSetStab_mono {x : X} {U V : Set Y} (hx : p x ∈ U) (hUV : U ⊆ V) :
    deckSetStab p (connectedComponentIn (p ⁻¹' U) x) ≤
      deckSetStab p (connectedComponentIn (p ⁻¹' V) x) := by
  intro φ hφ
  show (φ : X ≃ₜ X) '' _ = _
  rw [deck_image_connectedComponentIn p φ.2 (hUV hx)]
  have hmem : (φ : X ≃ₜ X) x ∈ connectedComponentIn (p ⁻¹' V) x := by
    have : (φ : X ≃ₜ X) x ∈ (φ : X ≃ₜ X) '' connectedComponentIn (p ⁻¹' U) x :=
      mem_image_of_mem _ (mem_connectedComponentIn hx)
    rw [show (φ : X ≃ₜ X) '' _ = _ from hφ] at this
    exact connectedComponentIn_mono _ (preimage_mono hUV) this
  exact (connectedComponentIn_eq hmem).symm

/-- `prop:Galoisian_fiber`. The projective limit `lim_{U ∈ 𝓤} Γ(X/Y)/Γ_{Û_U}` of the natural maps
`φΓ_{Û_U} ↦ φΓ_{Û_V}` (`U ⊆ V`), with the topology of the product of the discrete factors. -/
@[ext]
structure GaloisThread (x : X) (𝓤 : Set (Set Y)) where
  /-- The family of cosets. -/
  toFun : ∀ U : 𝓤, GaloisCoset p x U
  compat : ∀ U V : 𝓤, (U : Set Y) ⊆ V → ∀ φ : Deck p,
    toFun U = galoisMk p x U φ → toFun V = galoisMk p x V φ

instance (x : X) (𝓤 : Set (Set Y)) : TopologicalSpace (GaloisThread p x 𝓤) :=
  TopologicalSpace.induced GaloisThread.toFun inferInstance

variable {p}

/-- The comparison map `lim Γ/Γ_{Û_U} → lim X_U`. -/
def galoisThreadToFiber {x : X} {𝓤 : Set (Set Y)} (hx : ∀ U ∈ 𝓤, p x ∈ U)
    (c : GaloisThread p x 𝓤) : FiberThread p 𝓤 where
  toFun U := galoisComp p x U (c.toFun U)
  isCompOf U := by
    obtain ⟨φ, hφ⟩ := galoisMk_surjective p x U (c.toFun U)
    rw [← hφ, galoisComp_mk, deck_image_connectedComponentIn p φ.2 (hx U U.2)]
    exact isCompOf_connectedComponentIn (by rw [deck_apply p φ.2]; exact hx U U.2)
  mono U V hUV := by
    obtain ⟨φ, hφ⟩ := galoisMk_surjective p x U (c.toFun U)
    rw [← hφ, c.compat U V hUV φ hφ.symm, galoisComp_mk, galoisComp_mk]
    exact image_mono (connectedComponentIn_mono _ (preimage_mono hUV))

theorem galoisThreadToFiber_bijective [T2Space X] [T2Space Y] [LocPathConnectedSpace Y]
    [FirstCountableTopology Y] (hp : IsQuasiGaloisian p) {x : X} {𝓤 : Set (Set Y)}
    (h𝓤 : ∀ U ∈ 𝓤, IsOpen U ∧ IsPreconnected U) (hx : ∀ U ∈ 𝓤, p x ∈ U) :
    Bijective (galoisThreadToFiber (p := p) hx) := by
  refine ⟨fun c c' h => GaloisThread.ext (funext fun U => galoisComp_injective p x U ?_),
    fun s => ?_⟩
  · exact congrFun (congrArg FiberThread.toFun h) U
  · have hex : ∀ U : 𝓤, ∃ φ : Deck p, (φ : X ≃ₜ X) '' connectedComponentIn (p ⁻¹' U) x =
        s.toFun U := fun U => by
      obtain ⟨φ, hφ, h⟩ := hp.exists_image_eq (h𝓤 U U.2).1 (h𝓤 U U.2).2
        (isCompOf_connectedComponentIn (hx U U.2)) (s.isCompOf U)
      exact ⟨⟨φ, hφ⟩, h⟩
    choose φ hφ using hex
    refine ⟨⟨fun U => galoisMk p x U (φ U), fun U V hUV ψ hψ => ?_⟩,
      FiberThread.ext (funext fun U => hφ U)⟩
    apply galoisComp_injective p x V
    rw [galoisComp_mk, galoisComp_mk, hφ V]
    have hψU : (ψ : X ≃ₜ X) '' connectedComponentIn (p ⁻¹' U) x = s.toFun U := by
      rw [← galoisComp_mk, ← hψ, galoisComp_mk, hφ U]
    have hC : IsCompOf p V ((ψ : X ≃ₜ X) '' connectedComponentIn (p ⁻¹' V) x) := by
      rw [deck_image_connectedComponentIn p ψ.2 (hx V V.2)]
      exact isCompOf_connectedComponentIn (by rw [deck_apply p ψ.2]; exact hx V V.2)
    obtain ⟨z, hz⟩ := (s.isCompOf U).nonempty
    refine (hC.eq_of_meets (s.isCompOf V) ⟨z, ?_, s.mono U V hUV hz⟩).symm
    rw [← hψU] at hz
    exact image_mono (connectedComponentIn_mono _ (preimage_mono hUV)) hz

/-- The comparison `lim Γ/Γ_{Û_U} ≃ₜ lim X_U`. -/
def galoisThreadHomeomorph [T2Space X] [T2Space Y] [LocPathConnectedSpace Y]
    [FirstCountableTopology Y] (hp : IsQuasiGaloisian p) {x : X} {𝓤 : Set (Set Y)}
    (h𝓤 : ∀ U ∈ 𝓤, IsOpen U ∧ IsPreconnected U) (hx : ∀ U ∈ 𝓤, p x ∈ U) :
    GaloisThread p x 𝓤 ≃ₜ FiberThread p 𝓤 := by
  let e := Equiv.ofBijective _ (galoisThreadToFiber_bijective hp h𝓤 hx)
  have hcoord : ∀ U : 𝓤, Continuous fun c : GaloisThread p x 𝓤 => c.toFun U :=
    fun U => (continuous_apply U).comp continuous_induced_dom
  have hcoord' : ∀ U : 𝓤, Continuous fun s : FiberThread p 𝓤 => s.coords U :=
    FiberThread.continuous_coord
  refine ⟨e, ?_, ?_⟩
  · refine continuous_induced_rng.2 (continuous_pi fun U => ?_)
    exact continuous_of_discreteTopology.comp (hcoord U)
  · refine continuous_induced_rng.2 (continuous_pi fun U => ?_)
    have : (fun s : FiberThread p 𝓤 => (e.symm s).toFun U) =
        fun s => Function.invFun (galoisComp p x U) (s.toFun U) := by
      funext s
      have h1 : galoisComp p x U ((e.symm s).toFun U) = s.toFun U :=
        congrFun (congrArg FiberThread.toFun (e.apply_symm_apply s)) U
      show (e.symm s).toFun U = Function.invFun (galoisComp p x U) (s.toFun U)
      rw [← h1]
      exact (Function.leftInverse_invFun (galoisComp_injective p x U) _).symm
    show Continuous fun s : FiberThread p 𝓤 => (e.symm s).toFun U
    rw [this]
    exact (continuous_of_discreteTopology (f := fun d : DiscreteSets X =>
      Function.invFun (galoisComp p x U) d)).comp (hcoord' U)

/-- **`prop:Galoisian_fiber`** (`RamcovGX.tex:1478`; DEC-57: quasi-Galoisian as the completion of
a Galoisian covering over a portly `O`, an open connected basis). For a quasi-Galoisian branched covering,
`b ∈ Y`, a basis `𝓤` of open connected neighbourhoods of `b` and `x̂ ∈ p⁻¹(b)`,
`p⁻¹(b) ≃ₜ lim_{U ∈ 𝓤} Γ(X/Y)/Γ_{Û_U}`. -/
theorem galoisian_fiber [T2Space X] [T2Space Y] [LocPathConnectedSpace Y]
    [FirstCountableTopology Y] (hp : IsQuasiGaloisian p) {b : Y} {𝓤 : Set (Set Y)}
    (h𝓤 : ∀ U ∈ 𝓤, IsCNbhd b U) (hbasis : ∀ N ∈ 𝓝 b, ∃ U ∈ 𝓤, U ⊆ N) {x : X} (hx : p x = b) :
    Nonempty (p ⁻¹' {b} ≃ₜ GaloisThread p x 𝓤) :=
  ⟨(fiberHomeomorph hp.1.isSpread hp.1.isComplete h𝓤 hbasis).trans
    (galoisThreadHomeomorph hp (fun U hU => ⟨(h𝓤 U hU).1, (h𝓤 U hU).2.1⟩)
      (fun U hU => hx ▸ (h𝓤 U hU).2.2)).symm⟩

end GaloisFiber

/-! ### `lem:alternative_countable` -/

/-- A countable basis of open connected neighbourhoods of `b`. -/
theorem exists_countable_isCNbhd_basis [FirstCountableTopology Y] [LocallyConnectedSpace Y]
    (b : Y) : ∃ 𝓤 : Set (Set Y), 𝓤.Countable ∧ (∀ U ∈ 𝓤, IsCNbhd b U) ∧
      ∀ N ∈ 𝓝 b, ∃ U ∈ 𝓤, U ⊆ N := by
  obtain ⟨x, hx⟩ := (𝓝 b).exists_antitone_basis
  refine ⟨range fun n => connectedComponentIn (interior (x n)) b, countable_range _, ?_, ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact ⟨isOpen_interior.connectedComponentIn, isPreconnected_connectedComponentIn,
      mem_connectedComponentIn (mem_interior_iff_mem_nhds.2 (hx.mem n))⟩
  · intro N hN
    obtain ⟨n, -, hn⟩ := hx.toHasBasis.mem_iff.1 hN
    exact ⟨_, ⟨n, rfl⟩, (connectedComponentIn_subset _ _).trans (interior_subset.trans hn)⟩

/-- The inverse limit of `prop:spread_fiber` is a closed subspace of the product of the discrete
`X_U`. -/
theorem FiberThread.isClosedEmbedding_coords {p : X → Y} {𝓤 : Set (Set Y)} :
    IsClosedEmbedding (FiberThread.coords : FiberThread p 𝓤 → 𝓤 → DiscreteSets X) := by
  refine ⟨⟨⟨rfl⟩, fun s t h => FiberThread.ext h⟩, ?_⟩
  have hrange : range (FiberThread.coords : FiberThread p 𝓤 → 𝓤 → DiscreteSets X) =
      (⋂ U : 𝓤, {c : 𝓤 → DiscreteSets X | IsCompOf p U (c U)}) ∩
        ⋂ U : 𝓤, ⋂ V : 𝓤, {c : 𝓤 → DiscreteSets X |
          (U : Set Y) ⊆ V → @HasSubset.Subset (Set X) _ (c U) (c V)} := by
    ext c
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨mem_iInter.2 fun U => s.isCompOf U,
        mem_iInter.2 fun U => mem_iInter.2 fun V => fun h => s.mono U V h⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨c, fun U => mem_iInter.1 h1 U, fun U V h => mem_iInter.1 (mem_iInter.1 h2 U) V h⟩,
        rfl⟩
  rw [hrange]
  refine IsClosed.inter (isClosed_iInter fun U => ?_)
    (isClosed_iInter fun U => isClosed_iInter fun V => ?_)
  · have hc : Continuous fun c : 𝓤 → DiscreteSets X => c U := continuous_apply U
    exact (isClosed_discrete (α := DiscreteSets X) {S | IsCompOf p U S}).preimage hc
  · have hc : Continuous fun c : 𝓤 → DiscreteSets X => (c U, c V) :=
      (continuous_apply U).prodMk (continuous_apply V)
    exact (isClosed_discrete (α := DiscreteSets X × DiscreteSets X) {r |
      (U : Set Y) ⊆ V → @HasSubset.Subset (Set X) _ r.1 r.2}).preimage hc

/-- The fibre of a complete spread over a first countable base is completely metrizable
(it is a closed subspace of a countable product of discrete spaces, `prop:spread_fiber`). -/
theorem isCompletelyMetrizableSpace_fiber [T0Space X] [T1Space Y] [LocallyConnectedSpace Y]
    [FirstCountableTopology Y] (hp : IsSpread p) (hc : IsCompleteSpread p) (b : Y) :
    TopologicalSpace.IsCompletelyMetrizableSpace (p ⁻¹' {b}) := by
  obtain ⟨𝓤, h𝓤c, h𝓤, hbasis⟩ := exists_countable_isCNbhd_basis b
  haveI : Countable 𝓤 := h𝓤c.to_subtype
  have e := fiberHomeomorph hp hc h𝓤 hbasis
  exact (FiberThread.isClosedEmbedding_coords.comp e.isClosedEmbedding).IsCompletelyMetrizableSpace

/-- Baire: a non-empty countable T1 Baire space has an isolated point. -/
theorem exists_isOpen_singleton_of_countable {Z : Type*} [TopologicalSpace Z] [T1Space Z]
    [BaireSpace Z] [Nonempty Z] [Countable Z] : ∃ z : Z, IsOpen ({z} : Set Z) := by
  obtain ⟨z, w, hw⟩ := nonempty_interior_of_iUnion_of_closed (f := fun z : Z => ({z} : Set Z))
    (fun _ => isClosed_singleton) (iUnion_of_singleton Z)
  have hwz : w ∈ ({z} : Set Z) := interior_subset hw
  rw [mem_singleton_iff] at hwz
  subst hwz
  have : interior {w} = ({w} : Set Z) := Subset.antisymm interior_subset (singleton_subset_iff.2 hw)
  exact ⟨w, this ▸ isOpen_interior⟩

/-- A countable fibre of a complete spread over a first countable base, on which a group of
automorphisms acts with dense orbits, is discrete (Baire). -/
theorem discreteTopology_fiber_of_countable [T2Space X] [T1Space Y] [LocallyConnectedSpace Y]
    [FirstCountableTopology Y] (hp : IsSpread p) (hc : IsCompleteSpread p)
    {H : Subgroup (X ≃ₜ X)} (hH : H ≤ deckGroup p)
    (hdense : ∀ x x', p x = p x' → ∀ N ∈ 𝓝 x', ∃ φ ∈ H, φ x ∈ N) {b : Y}
    (hcount : (p ⁻¹' {b}).Countable) : DiscreteTopology (p ⁻¹' {b}) := by
  rcases isEmpty_or_nonempty (p ⁻¹' {b}) with he | hne
  · infer_instance
  haveI := isCompletelyMetrizableSpace_fiber hp hc b
  haveI : Countable (p ⁻¹' {b}) := hcount.to_subtype
  obtain ⟨z₀, hz₀⟩ := exists_isOpen_singleton_of_countable (Z := p ⁻¹' {b})
  rw [discreteTopology_iff_isOpen_singleton]
  intro z
  obtain ⟨N, hN, hNe⟩ := isOpen_induced_iff.1 hz₀
  have hz₀N : (z₀ : X) ∈ N := by
    have : z₀ ∈ Subtype.val ⁻¹' N := by rw [hNe]; rfl
    exact this
  obtain ⟨φ, hφ, hφN⟩ := hdense z z₀ (z.2.trans z₀.2.symm) N (hN.mem_nhds hz₀N)
  have hφp := hH hφ
  let F : p ⁻¹' {b} → p ⁻¹' {b} := fun w => ⟨φ w, deck_mem_fiber p hφp w.2⟩
  have hF : Continuous F := (φ.continuous.comp continuous_subtype_val).subtype_mk _
  have hFz : F z = z₀ := by
    have : F z ∈ Subtype.val ⁻¹' N := hφN
    rw [hNe] at this
    exact this
  have : ({z} : Set (p ⁻¹' {b})) = F ⁻¹' {z₀} := by
    ext w
    simp only [mem_singleton_iff, mem_preimage]
    constructor
    · rintro rfl; exact hFz
    · intro hw
      apply Subtype.ext
      apply φ.injective
      have := congrArg Subtype.val (hw.trans hFz.symm)
      exact this
  rw [this]
  exact hz₀.preimage hF

/-- **`lem:alternative_countable`** (`RamcovGX.tex:1492`; quasi-Galoisian as ruled by DEC-57).
Let `p` be a quasi-Galoisian branched covering with `Γ(X/Y)` countable and `b ∈ Y`. Then (i) `p⁻¹(b)` is discrete, (ii) `p⁻¹(b)` is
countable, (iii) `Γ(X/Y)` acts transitively on `p⁻¹(b)` are equivalent. -/
theorem alternative_countable [T2Space X] [T2Space Y] [LocPathConnectedSpace Y]
    [FirstCountableTopology Y] (hp : IsQuasiGaloisian p)
    (hΓ : (deckGroup p : Set (X ≃ₜ X)).Countable) (b : Y) :
    (DiscreteTopology (p ⁻¹' {b}) ↔ (p ⁻¹' {b}).Countable) ∧
      ((p ⁻¹' {b}).Countable ↔
        ∀ x ∈ p ⁻¹' {b}, ∀ x' ∈ p ⁻¹' {b}, ∃ φ ∈ deckGroup p, φ x = x') := by
  have hdense : ∀ x x', p x = p x' → ∀ N ∈ 𝓝 x', ∃ φ ∈ deckGroup p, φ x ∈ N :=
    fun x x' h N hN => hp.exists_mem_nhds h hN
  have i_iii : DiscreteTopology (p ⁻¹' {b}) →
      ∀ x ∈ p ⁻¹' {b}, ∀ x' ∈ p ⁻¹' {b}, ∃ φ ∈ deckGroup p, φ x = x' :=
    fun hd x hx x' hx' => exists_eq_of_discreteTopology_fiber le_rfl hd hdense hx hx'
  have iii_ii : (∀ x ∈ p ⁻¹' {b}, ∀ x' ∈ p ⁻¹' {b}, ∃ φ ∈ deckGroup p, φ x = x') →
      (p ⁻¹' {b}).Countable := by
    intro h
    rcases (p ⁻¹' {b}).eq_empty_or_nonempty with he | ⟨x, hx⟩
    · rw [he]; exact countable_empty
    · refine (hΓ.image fun φ => φ x).mono fun x' hx' => ?_
      obtain ⟨φ, hφ, rfl⟩ := h x hx x' hx'
      exact ⟨φ, hφ, rfl⟩
  have ii_i : (p ⁻¹' {b}).Countable → DiscreteTopology (p ⁻¹' {b}) :=
    discreteTopology_fiber_of_countable hp.1.isSpread hp.1.isComplete le_rfl hdense
  exact ⟨⟨fun h => iii_ii (i_iii h), ii_i⟩, ⟨fun h => i_iii (ii_i h), iii_ii⟩⟩

/-! ### `def:semi_locally_simple_connectedness` -/

/-- `def:semi_locally_simple_connectedness` (`RamcovGX.tex:1451`), HOMOTOPY form (the paper's
notion, DEC-55, is `GX.IsSLSCAtCC`; this form implies it, `GX.IsSLSCAt.isSLSCAtCC`). `U` is
*semi-locally simply connected at `x`* (a point of `closure U` in the paper) if some connected open neighbourhood `V`
of `x` is such that every loop of `Ω(x,x,V ∩ U)`, seen in `Ω(x,x,U)`, is almost trivial. -/
def IsSLSCAt (U : Set X) (x : X) : Prop :=
  ∃ V : Set X, IsOpen V ∧ IsPreconnected V ∧ x ∈ V ∧
    ∀ γ : Path x x, MemOmega (V ∩ U) γ → AlmostTrivial U γ

/-- `def:semi_locally_simple_connectedness`. `U` is *semi-locally simply connected in `X`*
if it is dense and semi-locally simply connected at every point of `X`. -/
def IsSLSCIn (U : Set X) : Prop :=
  Dense U ∧ ∀ x, IsSLSCAt U x

/-- **`def:semi_locally_simple_connectedness`** (`RamcovGX.tex:1451`) in its **literal** form
(DEC-55): `U` is *semi-locally simply connected at `x`* if some connected open neighbourhood `V`
of `x` is such that every loop of `Ω(x,x,V ∩ U)`, seen in `Ω(x,x,U)`, is almost trivial in the
sense of `def:almost_trivial_loop` — its connected component in the compact-open `Ω(x,x,U)` meets
`Ω(x,x,W ∩ U)` for every neighbourhood `W` of `x` (`GX.AlmostTrivialCC`). -/
def IsSLSCAtCC (U : Set X) (x : X) : Prop :=
  ∃ V : Set X, IsOpen V ∧ IsPreconnected V ∧ x ∈ V ∧
    ∀ γ : Path x x, MemOmega (V ∩ U) γ → AlmostTrivialCC U γ

/-- **`def:semi_locally_simple_connectedness`**, literal form (DEC-55): `U` is *semi-locally
simply connected in `X`* if it is dense and semi-locally simply connected at every point of `X`. -/
def IsSLSCInCC (U : Set X) : Prop :=
  Dense U ∧ ∀ x, IsSLSCAtCC U x

/-- The homotopy form of semi-local simple connectedness at `x` implies the literal one. -/
theorem IsSLSCAt.isSLSCAtCC {U : Set X} {x : X} (h : IsSLSCAt U x) : IsSLSCAtCC U x := by
  obtain ⟨V, hV, hVc, hxV, hloop⟩ := h
  exact ⟨V, hV, hVc, hxV, fun γ hγ => (hloop γ hγ).almostTrivialCC⟩

/-- The homotopy form of semi-local simple connectedness in `X` implies the literal one. -/
theorem IsSLSCIn.isSLSCInCC {U : Set X} (h : IsSLSCIn U) : IsSLSCInCC U :=
  ⟨h.1, fun x => (h.2 x).isSLSCAtCC⟩

/-- DEC-55: the literal form implies the homotopy form for `U` open and semilocally simply
connected in a locally path-connected `X` (`GX.AlmostTrivialCC.almostTrivial`). -/
theorem IsSLSCAtCC.isSLSCAt [LocPathConnectedSpace X] {U : Set X} (hU : IsOpen U)
    (hsc : SemilocallySimplyConnected U) {x : X} (h : IsSLSCAtCC U x) : IsSLSCAt U x := by
  obtain ⟨V, hV, hVc, hxV, hloop⟩ := h
  exact ⟨V, hV, hVc, hxV, fun γ hγ => (hloop γ hγ).almostTrivial hU hsc⟩

/-- DEC-55: for `U` open and semilocally simply connected in a locally path-connected `X`, the
literal and the homotopy forms of semi-local simple connectedness in `X` agree. -/
theorem isSLSCInCC_iff [LocPathConnectedSpace X] {U : Set X} (hU : IsOpen U)
    (hsc : SemilocallySimplyConnected U) : IsSLSCInCC U ↔ IsSLSCIn U :=
  ⟨fun h => ⟨h.1, fun x => (h.2 x).isSLSCAt hU hsc⟩, IsSLSCIn.isSLSCInCC⟩

/-! ### Splitting a loop at its midpoint -/

section Split

variable {x y : X}

/-- `1/2 ∈ [0,1]`. -/
def halfI : I := ⟨1 / 2, by norm_num, by norm_num⟩

/-- `t ↦ (1+t)/2`. -/
def tailParam (t : I) : I := ⟨(1 + t) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩

/-- `t ↦ (1-t)/2`. -/
def headParam (t : I) : I := ⟨(1 - t) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩

theorem continuous_tailParam : Continuous tailParam :=
  ((continuous_const.add continuous_subtype_val).div_const 2).subtype_mk _

theorem continuous_headParam : Continuous headParam :=
  ((continuous_const.sub continuous_subtype_val).div_const 2).subtype_mk _

theorem tailParam_zero : tailParam 0 = halfI :=
  Subtype.ext (by show (1 + ((0 : I) : ℝ)) / 2 = 1 / 2; norm_num)

theorem tailParam_one : tailParam 1 = 1 :=
  Subtype.ext (by show (1 + ((1 : I) : ℝ)) / 2 = 1; norm_num)

theorem headParam_zero : headParam 0 = halfI :=
  Subtype.ext (by show (1 - ((0 : I) : ℝ)) / 2 = 1 / 2; norm_num)

theorem headParam_one : headParam 1 = 0 :=
  Subtype.ext (by show (1 - ((1 : I) : ℝ)) / 2 = 0; norm_num)

/-- The second half of a path, `t ↦ δ((1+t)/2)`. -/
def tailHalf (δ : Path x y) : Path (δ halfI) y where
  toFun t := δ (tailParam t)
  continuous_toFun := δ.continuous.comp continuous_tailParam
  source' := by show δ (tailParam 0) = δ halfI; rw [tailParam_zero]
  target' := by show δ (tailParam 1) = y; rw [tailParam_one, δ.target]

/-- The first half of a path, reversed, `t ↦ δ((1-t)/2)`. -/
def headHalfRev (δ : Path x y) : Path (δ halfI) x where
  toFun t := δ (headParam t)
  continuous_toFun := δ.continuous.comp continuous_headParam
  source' := by show δ (headParam 0) = δ halfI; rw [headParam_zero]
  target' := by show δ (headParam 1) = x; rw [headParam_one, δ.source]

theorem tailHalf_apply (δ : Path x y) (t : I) : tailHalf δ t = δ (tailParam t) := rfl

theorem headHalfRev_apply (δ : Path x y) (t : I) : headHalfRev δ t = δ (headParam t) := rfl

/-- The loop `(headHalfRev δ)⁻¹ * tailHalf δ` is `δ`. -/
theorem headHalfRev_symm_trans_tailHalf (δ : Path x y) :
    (headHalfRev δ).symm.trans (tailHalf δ) = δ := by
  ext t
  rw [Path.trans_apply]
  split_ifs with h
  · simp only [Path.symm, Path.coe_mk_mk, Function.comp_apply]
    show δ (headParam _) = δ t
    congr 1; apply Subtype.ext
    show (1 - (1 - 2 * (t : ℝ))) / 2 = t
    ring
  · rw [tailHalf_apply]
    congr 1; apply Subtype.ext
    show (1 + (2 * (t : ℝ) - 1)) / 2 = t
    ring

/-- Before time `1`, the halves are interior values of `δ`. -/
theorem tailHalf_mem {U : Set X} {δ : Path x y} (hδ : MemOmega U δ) {t : I} (ht : (t : ℝ) < 1) :
    tailHalf δ t ∈ U := by
  rw [tailHalf_apply]
  exact hδ _ (by show (0 : ℝ) < (1 + t) / 2; linarith [t.2.1])
    (by show (1 + (t : ℝ)) / 2 < 1; linarith)

theorem headHalfRev_mem {U : Set X} {δ : Path x y} (hδ : MemOmega U δ) {t : I}
    (ht : (t : ℝ) < 1) : headHalfRev δ t ∈ U := by
  rw [headHalfRev_apply]
  exact hδ _ (by show (0 : ℝ) < (1 - t) / 2; linarith)
    (by show (1 - (t : ℝ)) / 2 < 1; linarith [t.2.1])

theorem MemOmega.of_lt_one {U : Set X} {x' y' : X} {γ : Path x' y'}
    (h : ∀ t : I, (t : ℝ) < 1 → γ t ∈ U) : MemOmega U γ :=
  fun t _ h1 => h t h1

end Split

/-! ### Discrete fibres and semi-local simple connectedness (`prop:Galoisian_semilocal`) -/

/-- `prop:Galoisian_semilocal`, (ii) ⇒ (discrete fibres): if `Y ∖ S` is semi-locally simply
connected at `y`, the fibre over `y` of any covering possibly branched over `S` is discrete. -/
theorem discreteTopology_fiber_of_isSLSCAt [T2Space X] [LocPathConnectedSpace X]
    [FirstCountableTopology X] [LocallyConnectedSpace Y] {p : X → Y} (hp : IsBranchedCovering p)
    {S : Set Y} (hS : IsSkeletal S) (hpS : IsPossiblyBranchedOver p S) {y : Y}
    (h : IsSLSCAt Sᶜ y) : DiscreteTopology (p ⁻¹' {y}) := by
  obtain ⟨U, hU, -, hyU, hloop⟩ := h
  have cov := isCoveringMap_restrict_compl hp hS hpS
  have hP : IsPortly (p ⁻¹' Sᶜ) := hp.isPortly_preimage hS
  have hpc := hp.isSpread.continuous
  rw [discreteTopology_iff_isOpen_singleton]
  rintro ⟨x, hx⟩
  have hx' : p x = y := hx
  set V := connectedComponentIn (p ⁻¹' U) x
  have hxU : p x ∈ U := by rw [hx']; exact hyU
  have hVo : IsOpen V := (hU.preimage hpc).connectedComponentIn
  have hVc : IsPreconnected V := isPreconnected_connectedComponentIn
  have hxV : x ∈ V := mem_connectedComponentIn hxU
  have key : ∀ x' ∈ V, p x' = y → x' = x := by
    intro x' hx'V hx'y
    obtain ⟨e₀, he₀V, he₀P⟩ := hP.dense.inter_open_nonempty V hVo ⟨x, hxV⟩
    obtain ⟨Γ₁, hΓ₁V, hΓ₁P⟩ := exists_path_of_isPortly_of_isOpen hP hVo hVc he₀P he₀V hxV
    obtain ⟨Γ₂, hΓ₂V, hΓ₂P⟩ := exists_path_of_isPortly_of_isOpen hP hVo hVc he₀P he₀V hx'V
    set γ₁ : Path (p e₀) y := (Γ₁.map hpc).cast rfl hx'.symm
    set γ₂ : Path (p e₀) y := (Γ₂.map hpc).cast rfl hx'y.symm
    have hm : ∀ {x'' : X} (Γ : Path e₀ x'') (hΓV : ∀ t, Γ t ∈ V)
        (hΓP : ∀ t : I, (t : ℝ) < 1 → Γ t ∈ p ⁻¹' Sᶜ) (hy : p x'' = y),
        MemOmega (U ∩ Sᶜ) ((Γ.map hpc).cast rfl hy.symm) := by
      intro x'' Γ hΓV hΓP hy t _ h1
      exact ⟨(connectedComponentIn_subset (p ⁻¹' U) x (hΓV t) : p (Γ t) ∈ U), hΓP t h1⟩
    have he₀ : p e₀ ∈ U ∩ Sᶜ :=
      ⟨(connectedComponentIn_subset (p ⁻¹' U) x he₀V : p e₀ ∈ U), he₀P⟩
    have hδ : MemOmega (U ∩ Sᶜ) (γ₂.symm.trans γ₁) :=
      MemOmega.loop he₀ (hm Γ₁ hΓ₁V hΓ₁P hx') (hm Γ₂ hΓ₂V hΓ₂P hx'y)
    have hat : AlmostHomotopic Sᶜ γ₁ γ₂ := hloop _ hδ
    have := lift_end_eq_of_almostHomotopic hp.isSpread cov hat (Γ₁ := Γ₁.toContinuousMap)
      (Γ₂ := Γ₂.toContinuousMap) (fun t => rfl) (fun t => rfl) (by simp)
    simpa using this.symm
  have : ({⟨x, hx⟩} : Set (p ⁻¹' {y})) = Subtype.val ⁻¹' V := by
    ext ⟨x', hx''⟩
    simp only [mem_singleton_iff, mem_preimage, Subtype.mk.injEq]
    exact ⟨fun h => h ▸ hxV, fun h => key x' h hx''⟩
  rw [this]
  exact hVo.preimage continuous_subtype_val

/-- `prop:Galoisian_semilocal`, (discrete fibres) ⇒ (ii): for a covering possibly branched over
`S` whose part over `Y ∖ S` is simply connected, a discrete fibre over `y` makes `Y ∖ S`
semi-locally simply connected at `y`. -/
theorem isSLSCAt_of_discreteTopology_fiber [T2Space X] [LocPathConnectedSpace X] [T1Space Y]
    [LocPathConnectedSpace Y] [FirstCountableTopology Y] {p : X → Y} (hp : IsBranchedCovering p)
    {S : Set Y} (hS : IsSkeletal S) (hpS : IsPossiblyBranchedOver p S)
    [SimplyConnectedSpace (p ⁻¹' Sᶜ)] {y : Y} (hd : DiscreteTopology (p ⁻¹' {y})) :
    IsSLSCAt Sᶜ y := by
  have cov := isCoveringMap_restrict_compl hp hS hpS
  have hpc := hp.isSpread.continuous
  obtain ⟨x, hx⟩ := hp.surjective y
  have ho : IsOpen ({⟨x, hx⟩} : Set (p ⁻¹' {y})) := isOpen_discrete _
  obtain ⟨N, hN, hNe⟩ := isOpen_induced_iff.1 ho
  have hxN : x ∈ N := by
    have : (⟨x, hx⟩ : p ⁻¹' {y}) ∈ Subtype.val ⁻¹' N := by rw [hNe]; rfl
    exact this
  obtain ⟨U₀, hU₀, hxU₀, hsub⟩ := (isSpread_iff.1 hp.isSpread).2.2 x N hN hxN
  rw [hx] at hxU₀
  set U := connectedComponentIn U₀ y
  have hU : IsOpen U := hU₀.connectedComponentIn
  have hUc : IsPreconnected U := isPreconnected_connectedComponentIn
  have hyU : y ∈ U := mem_connectedComponentIn hxU₀
  refine ⟨U, hU, hUc, hyU, fun δ hδ => ?_⟩
  have hxU : p x ∈ U := by rw [hx]; exact hyU
  set V := connectedComponentIn (p ⁻¹' U) x
  have hVN : V ⊆ N := (connectedComponentIn_mono _ (preimage_mono
    (connectedComponentIn_subset U₀ y))).trans hsub
  have hVfib : ∀ x' ∈ V, p x' = y → x' = x := by
    intro x' hx'V hx'y
    have : (⟨x', hx'y⟩ : p ⁻¹' {y}) ∈ Subtype.val ⁻¹' N := hVN hx'V
    rw [hNe] at this
    exact congrArg Subtype.val this
  have hδU : ∀ t, δ t ∈ U := fun t => by
    rcases eq_or_lt_of_le t.2.1 with h0 | h0
    · have : t = 0 := Subtype.ext h0.symm
      rw [this, δ.source]; exact hyU
    rcases eq_or_lt_of_le t.2.2 with h1 | h1
    · have : t = 1 := Subtype.ext h1
      rw [this, δ.target]; exact hyU
    exact (hδ t h0 h1).1
  have hδS : MemOmega Sᶜ δ := fun t h0 h1 => (hδ t h0 h1).2
  have hz : δ halfI ∈ U ∩ Sᶜ := hδ halfI (by norm_num [halfI]) (by norm_num [halfI])
  obtain ⟨zh, hzhV, hzhz⟩ : δ halfI ∈ p '' V := by
    rw [(spread_connected_image hp).2 U hU hUc V (isCompOf_connectedComponentIn hxU)]
    exact hz.1
  -- the two halves and their lifts from `zh`
  have lift : ∀ P : Path (δ halfI) y, (∀ t, P t ∈ U) → (∀ t : I, (t : ℝ) < 1 → P t ∈ Sᶜ) →
      ∃ Γ : C(I, X), (∀ t, p (Γ t) = P t) ∧ Γ 0 = zh ∧ Γ 1 = x := by
    intro P hPU hPS
    obtain ⟨Γ, hΓ, hΓ0⟩ := exists_lift hp.isSpread hp.isComplete cov P.toContinuousMap hPS
      (by rw [hzhz]; exact P.source.symm)
    refine ⟨Γ, hΓ, hΓ0, hVfib _ ?_ (by rw [hΓ]; exact P.target)⟩
    have hrange : range Γ ⊆ V := by
      rw [show V = connectedComponentIn (p ⁻¹' U) zh from connectedComponentIn_eq hzhV]
      exact (isPreconnected_range Γ.continuous).subset_connectedComponentIn
        ⟨0, hΓ0⟩ (by rintro _ ⟨t, rfl⟩; show p (Γ t) ∈ U; rw [hΓ]; exact hPU t)
    exact hrange (mem_range_self 1)
  have hP₁U : ∀ t, tailHalf δ t ∈ U := fun t => by rw [tailHalf_apply]; exact hδU _
  have hP₂U : ∀ t, headHalfRev δ t ∈ U := fun t => by rw [headHalfRev_apply]; exact hδU _
  obtain ⟨Γ₁, hΓ₁, hΓ₁0, hΓ₁1⟩ := lift (tailHalf δ) hP₁U fun t ht => tailHalf_mem hδS ht
  obtain ⟨Γ₂, hΓ₂, hΓ₂0, hΓ₂1⟩ := lift (headHalfRev δ) hP₂U fun t ht => headHalfRev_mem hδS ht
  have hah : AlmostHomotopic Sᶜ (tailHalf δ) (headHalfRev δ) :=
    almostHomotopic_of_lift_end_eq hp hS hz.2 (MemOmega.of_lt_one fun t ht => tailHalf_mem hδS ht)
      (MemOmega.of_lt_one fun t ht => headHalfRev_mem hδS ht) hΓ₁ hΓ₂ (hΓ₁0.trans hΓ₂0.symm)
      (hΓ₁1.trans hΓ₂1.symm)
  have : AlmostTrivial Sᶜ ((headHalfRev δ).symm.trans (tailHalf δ)) := hah
  rwa [headHalfRev_symm_trans_tailHalf] at this

/-! ### `rem:definition_semi_locally_simply_connected` -/

/-- `rem:definition_semi_locally_simply_connected` (`RamcovGX.tex:1455`), the true direction: a
semi-locally simply connected space (DEC-41) is semi-locally simply connected in itself. The
converse is false (the harmonic archipelago, `GX.harmonicArchipelago_counterexample`). -/
theorem isSLSCIn_univ_of_semilocallySimplyConnected [LocallyConnectedSpace X]
    (h : SemilocallySimplyConnected X) : IsSLSCIn (univ : Set X) := by
  refine ⟨dense_univ, fun x => ?_⟩
  obtain ⟨U, hU, hloop⟩ := h x
  obtain ⟨V, hV, hVU⟩ := exists_isCNbhd_subset isOpen_interior (mem_interior_iff_mem_nhds.2 hU)
  refine ⟨V, hV.1, hV.2.1, hV.2.2, fun γ hγ => ⟨fun t h0 h1 => mem_univ _, fun W hW => ?_⟩⟩
  have hγU : ∀ t, γ t ∈ U := fun t => by
    rcases eq_or_lt_of_le t.2.1 with h0 | h0
    · have : t = 0 := Subtype.ext h0.symm
      rw [this, γ.source]; exact interior_subset (hVU hV.2.2)
    rcases eq_or_lt_of_le t.2.2 with h1 | h1
    · have : t = 1 := Subtype.ext h1
      rw [this, γ.target]; exact interior_subset (hVU hV.2.2)
    exact interior_subset (hVU (hγ t h0 h1).1)
  obtain ⟨F⟩ := hloop γ hγU
  exact ⟨Path.refl x, fun t _ _ => ⟨mem_of_mem_nhds hW, mem_univ _⟩, F, fun _ _ _ _ => mem_univ _⟩

/-- `rem:definition_semi_locally_simply_connected` (`RamcovGX.tex:1455`) in the literal
reading (DEC-55), the true direction: a semi-locally simply connected space (DEC-41) is
semi-locally simply connected in itself — the corrected statement. The converse is false (the
harmonic archipelago, `GX.harmonicArchipelago_counterexample`; SCOPE (e)). -/
theorem isSLSCInCC_univ_of_semilocallySimplyConnected [LocallyConnectedSpace X]
    (h : SemilocallySimplyConnected X) : IsSLSCInCC (univ : Set X) :=
  (isSLSCIn_univ_of_semilocallySimplyConnected h).isSLSCInCC

/-! ### `rem:simple_cases` -/

/-- Almost triviality is preserved by continuous maps. -/
theorem AlmostTrivial.map {Z : Type*} [TopologicalSpace Z] {f : Z → X} (hf : Continuous f)
    {A : Set X} {z : Z} {δ : Path z z} (h : AlmostTrivial (f ⁻¹' A) δ) :
    AlmostTrivial A (δ.map hf) := by
  refine ⟨fun t h0 h1 => h.1 t h0 h1, fun N hN => ?_⟩
  obtain ⟨δ', hδ', F, hF⟩ := h.2 (f ⁻¹' N) (hf.continuousAt.preimage_mem_nhds hN)
  exact ⟨δ'.map hf, fun t h0 h1 => hδ' t h0 h1, F.map ⟨f, hf⟩, fun s t h0 h1 => hF s t h0 h1⟩

/-- Semi-local simple connectedness at a point is local: it transfers along an open embedding. -/
theorem IsSLSCAt.of_isOpenEmbedding {Z : Type*} [TopologicalSpace Z] {f : Z → X}
    (hf : IsOpenEmbedding f) {A : Set X} {z : Z} (h : IsSLSCAt (f ⁻¹' A) z) : IsSLSCAt A (f z) := by
  obtain ⟨W, hW, hWc, hzW, hloop⟩ := h
  refine ⟨f '' W, hf.isOpenMap W hW, hWc.image f hf.continuous.continuousOn,
    mem_image_of_mem f hzW, fun γ hγ => ?_⟩
  have hrange : ∀ t, γ t ∈ range f := fun t => by
    rcases eq_or_lt_of_le t.2.1 with h0 | h0
    · have : t = 0 := Subtype.ext h0.symm
      rw [this, γ.source]; exact mem_range_self z
    rcases eq_or_lt_of_le t.2.2 with h1 | h1
    · have : t = 1 := Subtype.ext h1
      rw [this, γ.target]; exact mem_range_self z
    obtain ⟨w, -, hw⟩ := (hγ t h0 h1).1
    exact ⟨w, hw⟩
  set e := hf.isEmbedding.toHomeomorph
  have hz : e.symm ⟨f z, mem_range_self z⟩ = z := hf.isEmbedding.toHomeomorph_symm_apply z
  set γ' : Path z z := ((pathToSub γ hrange).map e.symm.continuous).cast hz.symm hz.symm
  have hfγ : ∀ t, f (γ' t) = γ t := fun t => by
    show f (e.symm ⟨γ t, hrange t⟩) = γ t
    have := congrArg Subtype.val (e.apply_symm_apply ⟨γ t, hrange t⟩)
    rw [IsEmbedding.toHomeomorph_apply_coe] at this
    exact this
  have hγ' : MemOmega (W ∩ f ⁻¹' A) γ' := by
    intro t h0 h1
    obtain ⟨⟨w, hwW, hw⟩, hA⟩ := hγ t h0 h1
    have : γ' t = w := hf.injective ((hfγ t).trans hw.symm)
    refine ⟨this ▸ hwW, ?_⟩
    show f (γ' t) ∈ A
    rw [hfγ]; exact hA
  have h' := (hloop γ' hγ').map hf.continuous
  have heq : γ'.map hf.continuous = γ := by ext t; exact hfγ t
  rwa [heq] at h'

/-- `rem:simple_cases`, second item, in the weakest form the argument uses: if every point has an
open neighbourhood `V` with `V ∩ U` semi-locally simply connected in `V`, then `U` is
semi-locally simply connected in `X`. -/
theorem isSLSCIn_of_local {U : Set X}
    (h : ∀ x, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ IsSLSCIn (((↑) : V → X) ⁻¹' U)) : IsSLSCIn U := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · obtain ⟨V, hV, hxV, hd, -⟩ := h x
    rw [mem_closure_iff_nhds]
    intro N hN
    have hN' : ((↑) : V → X) ⁻¹' N ∈ 𝓝 (⟨x, hxV⟩ : V) :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds hN
    obtain ⟨w, hwN, hwU⟩ := mem_closure_iff_nhds.1 (hd ⟨x, hxV⟩) _ hN'
    exact ⟨w, hwN, hwU⟩
  · obtain ⟨V, hV, hxV, -, hs⟩ := h x
    exact (hs ⟨x, hxV⟩).of_isOpenEmbedding hV.isOpenEmbedding_subtypeVal

/-- Semi-local simple connectedness in the space transfers along homeomorphisms. -/
theorem IsSLSCIn.of_homeomorph {Z : Type*} [TopologicalSpace Z] (φ : X ≃ₜ Z) {A : Set Z}
    (h : IsSLSCIn A) : IsSLSCIn (φ ⁻¹' A) :=
  ⟨h.1.preimage φ.isOpenMap, fun x => by
    have h' : IsSLSCAt (φ.symm ⁻¹' (φ ⁻¹' A)) (φ x) := by
      rw [show φ.symm ⁻¹' (φ ⁻¹' A) = A by ext; simp]; exact h.2 (φ x)
    have := h'.of_isOpenEmbedding φ.symm.isOpenEmbedding
    rwa [φ.symm_apply_apply] at this⟩

/-- Almost triviality in the literal (compact-open) sense of DEC-55 is preserved by continuous
maps: `g ↦ f ∘ g` is continuous for the compact-open topologies, so it carries the connected
component of `δ` in `Ω(z,z,f⁻¹(A))` into that of `f ∘ δ` in `Ω(f z, f z, A)`. -/
theorem AlmostTrivialCC.map {Z : Type*} [TopologicalSpace Z] {f : Z → X} (hf : Continuous f)
    {A : Set X} {z : Z} {δ : Path z z} (h : AlmostTrivialCC (f ⁻¹' A) δ) :
    AlmostTrivialCC A (δ.map hf) := by
  set F : C(I, Z) → C(I, X) := (ContinuousMap.mk f hf).comp
  have hF : Continuous F := ContinuousMap.continuous_postcomp _
  have hmaps : ∀ {B : Set X}, MapsTo F (OmegaSet (f ⁻¹' B) z z) (OmegaSet B (f z) (f z)) := by
    intro B g hg
    refine ⟨?_, ?_, fun t h0 h1 => hg.2.2 t h0 h1⟩
    · show f (g 0) = f z; rw [hg.1]
    · show f (g 1) = f z; rw [hg.2.1]
  have hFδ : F δ.toContinuousMap = (δ.map hf).toContinuousMap := ContinuousMap.ext fun t => rfl
  refine ⟨hFδ ▸ hmaps h.1, fun N hN => ?_⟩
  obtain ⟨η, hηC, hηN⟩ := h.2 (f ⁻¹' N) (hf.continuousAt.preimage_mem_nhds hN)
  refine ⟨F η, ?_, hmaps (B := N ∩ A) hηN⟩
  rw [← hFδ]
  refine (isPreconnected_connectedComponentIn.image F hF.continuousOn).subset_connectedComponentIn
    (mem_image_of_mem F (mem_connectedComponentIn h.1)) ?_ (mem_image_of_mem F hηC)
  rintro _ ⟨g, hg, rfl⟩
  exact hmaps (connectedComponentIn_subset _ _ hg)

/-- Literal semi-local simple connectedness at `x` from a subspace `V ∋ x`: if every loop of
`Ω_V(x,x,W ∩ U)` is almost trivial in `V` and `W' ∋ x` is an open preconnected subset of `X`
lying in `W`, then `U` is semi-locally simply connected at `x` (literal form). -/
theorem isSLSCAtCC_of_subtype {U V : Set X} {x : X} (hxV : x ∈ V) {W : Set V}
    (hloop : ∀ γ : Path (⟨x, hxV⟩ : V) ⟨x, hxV⟩, MemOmega (W ∩ (((↑) : V → X) ⁻¹' U)) γ →
      AlmostTrivialCC (((↑) : V → X) ⁻¹' U) γ)
    {W' : Set X} (hW'o : IsOpen W') (hW'c : IsPreconnected W') (hxW' : x ∈ W')
    (hW'W : ∀ y ∈ W', ∃ h : y ∈ V, (⟨y, h⟩ : V) ∈ W) : IsSLSCAtCC U x := by
  refine ⟨W', hW'o, hW'c, hxW', fun γ hγ => ?_⟩
  have hV : ∀ t, γ t ∈ V := fun t => by
    rcases eq_or_lt_of_le t.2.1 with h0 | h0
    · rw [show t = 0 from Subtype.ext h0.symm, γ.source]; exact hxV
    rcases eq_or_lt_of_le t.2.2 with h1 | h1
    · rw [show t = 1 from Subtype.ext h1, γ.target]; exact hxV
    exact (hW'W _ (hγ t h0 h1).1).1
  have hγ' : MemOmega (W ∩ (((↑) : V → X) ⁻¹' U)) (pathToSub γ hV) := fun t h0 h1 =>
    ⟨(hW'W _ (hγ t h0 h1).1).2, (hγ t h0 h1).2⟩
  have := (hloop (pathToSub γ hV) hγ').map continuous_subtype_val
  have heq : (pathToSub γ hV).map continuous_subtype_val = γ := by ext t; rfl
  rwa [heq] at this

/-- Density of `U` from density in subspaces `V ∋ x`. -/
theorem dense_of_local_subtype {U : Set X}
    (h : ∀ x : X, ∃ V : Set X, x ∈ V ∧ Dense (((↑) : V → X) ⁻¹' U)) : Dense U := by
  intro x
  obtain ⟨V, hxV, hd⟩ := h x
  rw [mem_closure_iff_nhds]
  intro N hN
  have hN' : ((↑) : V → X) ⁻¹' N ∈ 𝓝 (⟨x, hxV⟩ : V) :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds hN
  obtain ⟨w, hwN, hwU⟩ := mem_closure_iff_nhds.1 (hd ⟨x, hxV⟩) _ hN'
  exact ⟨w, hwN, hwU⟩

/-- `rem:simple_cases`, second item, literal form (DEC-55), for open neighbourhoods: if every
point has an open neighbourhood `V` with `V ∩ U` semi-locally simply connected in `V`, then `U` is
semi-locally simply connected in `X` (no hypothesis on `X`). -/
theorem isSLSCInCC_of_local {U : Set X}
    (h : ∀ x, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ IsSLSCInCC (((↑) : V → X) ⁻¹' U)) :
    IsSLSCInCC U := by
  refine ⟨dense_of_local_subtype fun x => ?_, fun x => ?_⟩
  · obtain ⟨V, -, hxV, hd, -⟩ := h x
    exact ⟨V, hxV, hd⟩
  · obtain ⟨V, hV, hxV, -, hs⟩ := h x
    obtain ⟨W, hW, hWc, hxW, hloop⟩ := hs ⟨x, hxV⟩
    refine isSLSCAtCC_of_subtype hxV hloop (hV.isOpenMap_subtype_val W hW)
      (hWc.image _ continuous_subtype_val.continuousOn) ⟨_, hxW, rfl⟩ ?_
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨w.2, hw⟩

/-- **`rem:simple_cases`, second item** (`RamcovGX.tex:1464`), literal form (DEC-55): in a
locally connected `X`, if every point `x` has a neighbourhood `V` (not necessarily open; one per
point suffices, a fortiori a basis) with `V ∩ U` semi-locally simply connected in `V`, then `U` is
semi-locally simply connected in `X`. -/
theorem isSLSCInCC_of_local_nhds [LocallyConnectedSpace X] {U : Set X}
    (h : ∀ x : X, ∃ V ∈ 𝓝 x, IsSLSCInCC (((↑) : V → X) ⁻¹' U)) : IsSLSCInCC U := by
  refine ⟨dense_of_local_subtype fun x => ?_, fun x => ?_⟩
  · obtain ⟨V, hV, hd, -⟩ := h x
    exact ⟨V, mem_of_mem_nhds hV, hd⟩
  · obtain ⟨V, hV, -, hs⟩ := h x
    have hxV : x ∈ V := mem_of_mem_nhds hV
    obtain ⟨W, hW, hWc, hxW, hloop⟩ := hs ⟨x, hxV⟩
    obtain ⟨O, hO, hOW⟩ := isOpen_induced_iff.1 hW
    have hxO : x ∈ O := by
      rw [← hOW] at hxW; exact hxW
    have hxW' : x ∈ connectedComponentIn (O ∩ interior V) x :=
      mem_connectedComponentIn ⟨hxO, mem_interior_iff_mem_nhds.2 hV⟩
    refine isSLSCAtCC_of_subtype hxV hloop (hO.inter isOpen_interior).connectedComponentIn
      isPreconnected_connectedComponentIn hxW' fun y hy => ?_
    have hy' := connectedComponentIn_subset _ _ hy
    refine ⟨interior_subset hy'.2, ?_⟩
    rw [← hOW]; exact hy'.1

section Linear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `rem:simple_cases`, first item, the linear model: the complement of a closed proper linear
subspace `L` of a real normed space is semi-locally simply connected in it (radial contraction
towards the base point; no codimension condition is needed for this notion). -/
theorem isSLSCIn_compl_submodule (L : Submodule ℝ E) (hL : IsClosed (L : Set E)) (hLt : L ≠ ⊤) :
    IsSLSCIn ((L : Set E)ᶜ) := by
  refine ⟨?_, fun x => ?_⟩
  · rw [← interior_eq_empty_iff_dense_compl]
    by_contra hne
    exact hLt (L.eq_top_of_nonempty_interior' (Set.nonempty_iff_ne_empty.2 hne))
  -- the radius
  obtain ⟨r, hr, hball⟩ : ∃ r > 0, x ∉ L → Metric.ball x r ⊆ (L : Set E)ᶜ := by
    by_cases hx : x ∈ L
    · exact ⟨1, one_pos, fun h => absurd hx h⟩
    · obtain ⟨r, hr, hrb⟩ := Metric.isOpen_iff.1 hL.isOpen_compl x hx
      exact ⟨r, hr, fun _ => hrb⟩
  -- radial points stay off `L`
  have key : ∀ v ∈ Metric.ball x r ∩ (L : Set E)ᶜ, ∀ μ : ℝ, 0 < μ → μ ≤ 1 →
      x + μ • (v - x) ∈ (L : Set E)ᶜ := by
    rintro v ⟨hvb, hvL⟩ μ hμ hμ1
    by_cases hx : x ∈ L
    · intro hmem
      apply hvL
      have h1 : μ • (v - x) ∈ L := by
        have := L.sub_mem hmem hx
        simpa using this
      have h2 : v - x ∈ L := (L.smul_mem_iff hμ.ne').1 h1
      have := L.add_mem h2 hx
      simpa using this
    · apply hball hx
      rw [Metric.mem_ball, dist_eq_norm] at hvb ⊢
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hμ.le]
      calc μ * ‖v - x‖ ≤ 1 * ‖v - x‖ := by gcongr
        _ < r := by rw [one_mul]; exact hvb
  refine ⟨Metric.ball x r, Metric.isOpen_ball, (convex_ball x r).isPreconnected,
    Metric.mem_ball_self hr, fun γ hγ => ⟨fun t h0 h1 => (hγ t h0 h1).2, fun W hW => ?_⟩⟩
  obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.1 hW
  set lam : ℝ := min 1 (ε / r)
  have hlam : 0 < lam := lt_min one_pos (div_pos hε hr)
  have hlam1 : lam ≤ 1 := min_le_left _ _
  have hlamr : lam * r ≤ ε := by
    calc lam * r ≤ ε / r * r := by gcongr; exact min_le_right _ _
      _ = ε := div_mul_cancel₀ ε hr.ne'
  let γs : Path x x :=
    { toFun := fun t => x + lam • (γ t - x)
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp }
  have hγs : ∀ t, γs t = x + lam • (γ t - x) := fun _ => rfl
  refine ⟨γs, fun t h0 h1 => ⟨hεW ?_, key _ (hγ t h0 h1) lam hlam hlam1⟩, lineHomotopy γ γs,
    fun s t h0 h1 => ?_⟩
  · rw [hγs, Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hlam.le]
    have := (hγ t h0 h1).1
    rw [Metric.mem_ball, dist_eq_norm] at this
    calc lam * ‖γ t - x‖ < lam * r := by gcongr
      _ ≤ ε := hlamr
  · rw [lineHomotopy_apply, AffineMap.lineMap_apply_module, hγs]
    have : (1 - (s : ℝ)) • γ t + (s : ℝ) • (x + lam • (γ t - x)) =
        x + (1 - (s : ℝ) + s * lam) • (γ t - x) := by module
    rw [this]
    refine key _ (hγ t h0 h1) _ ?_ ?_
    · nlinarith [s.2.1, s.2.2]
    · nlinarith [s.2.1, s.2.2]

/-- `rem:simple_cases`, the radial criterion: if near `x` the subset `M ⊆ E` and `A` are stable
under the radial contraction `v ↦ x + μ (v - x)`, `0 < μ ≤ 1`, then `M ∩ A` is semi-locally simply
connected at `x` in `M`. -/
theorem isSLSCAt_of_radial_contraction {M A : Set E} (x : M) {r : ℝ} (hr : 0 < r)
    (hM : ∀ v ∈ M, dist v (x : E) < r → ∀ μ : ℝ, 0 ≤ μ → μ ≤ 1 → (x : E) + μ • (v - x) ∈ M)
    (hA : ∀ v ∈ M, dist v (x : E) < r → v ∈ A → ∀ μ : ℝ, 0 < μ → μ ≤ 1 →
      (x : E) + μ • (v - x) ∈ A) :
    IsSLSCAt (((↑) : M → E) ⁻¹' A) x := by
  have hball : ∀ {v : M} {μ : ℝ}, dist v x < r → 0 ≤ μ → μ ≤ 1 →
      dist ((x : E) + μ • ((v : E) - x)) x = μ * dist v x := by
    intro v μ _ hμ _
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hμ, Subtype.dist_eq,
      dist_eq_norm]
  refine ⟨Metric.ball x r, Metric.isOpen_ball, ?_, Metric.mem_ball_self hr, fun γ hγ =>
    ⟨fun t h0 h1 => (hγ t h0 h1).2, fun W hW => ?_⟩⟩
  · refine Topology.IsInducing.subtypeVal.isPreconnected_image.1 ?_
    have hstar : StarConvex ℝ (x : E) (((↑) : M → E) '' Metric.ball x r) := by
      rintro _ ⟨v, hv, rfl⟩ a b ha hb hab
      have hb1 : b ≤ 1 := by linarith
      refine ⟨⟨_, hM _ v.2 hv b hb hb1⟩, ?_, ?_⟩
      · rw [Metric.mem_ball, Subtype.dist_eq, hball hv hb hb1]
        calc b * dist v x ≤ 1 * dist v x := by gcongr
          _ < r := by rw [one_mul]; exact hv
      · show (x : E) + b • ((v : E) - x) = a • (x : E) + b • (v : E)
        rw [show a = 1 - b by linarith]; module
    exact (hstar.isPathConnected ⟨x, Metric.mem_ball_self hr, rfl⟩).isConnected.isPreconnected
  have hγb : ∀ t, dist (γ t) x < r := fun t => by
    rcases eq_or_lt_of_le t.2.1 with h0 | h0
    · have : t = 0 := Subtype.ext h0.symm
      rw [this, γ.source, dist_self]; exact hr
    rcases eq_or_lt_of_le t.2.2 with h1 | h1
    · have : t = 1 := Subtype.ext h1
      rw [this, γ.target, dist_self]; exact hr
    exact (hγ t h0 h1).1
  obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.1 hW
  set lam : ℝ := min 1 (ε / r)
  have hlam : 0 < lam := lt_min one_pos (div_pos hε hr)
  have hlam1 : lam ≤ 1 := min_le_left _ _
  have hlamr : lam * r ≤ ε := by
    calc lam * r ≤ ε / r * r := by gcongr; exact min_le_right _ _
      _ = ε := div_mul_cancel₀ ε hr.ne'
  set c : I → ℝ := fun s => 1 - (s : ℝ) + s * lam
  have hc0 : ∀ s, 0 < c s := fun s => by
    show 0 < 1 - (s : ℝ) + s * lam
    nlinarith [s.2.1, s.2.2]
  have hc1 : ∀ s, c s ≤ 1 := fun s => by
    show 1 - (s : ℝ) + s * lam ≤ 1
    nlinarith [s.2.1, s.2.2]
  let F : I × I → M := fun w =>
    ⟨(x : E) + c w.1 • ((γ w.2 : E) - x), hM _ (γ w.2).2 (hγb w.2) _ (hc0 w.1).le (hc1 w.1)⟩
  have hFc : Continuous F := by
    refine Continuous.subtype_mk ?_ _
    have : Continuous fun w : I × I => c w.1 := by
      show Continuous fun w : I × I => 1 - (w.1 : ℝ) + w.1 * lam
      fun_prop
    exact continuous_const.add (this.smul
      ((continuous_subtype_val.comp (γ.continuous.comp continuous_snd)).sub continuous_const))
  let γs : Path x x :=
    { toFun := fun t => F (1, t)
      continuous_toFun := hFc.comp (Continuous.prodMk_right 1)
      source' := Subtype.ext (by simp [F, γ.source])
      target' := Subtype.ext (by simp [F, γ.target]) }
  let H : Path.Homotopy γ γs :=
    { toFun := F
      continuous_toFun := hFc
      map_zero_left := fun t => Subtype.ext (by simp [F, c])
      map_one_left := fun t => rfl
      prop' := fun s t ht => by
        rcases ht with rfl | rfl
        · exact Subtype.ext (by simp [F, γ.source])
        · exact Subtype.ext (by simp [F, γ.target]) }
  refine ⟨γs, fun t h0 h1 => ⟨hεW ?_, ?_⟩, H, fun s t h0 h1 => ?_⟩
  · show dist (F (1, t)) x < ε
    rw [Subtype.dist_eq]
    show dist ((x : E) + c 1 • ((γ t : E) - x)) x < ε
    rw [hball (hγb t) (hc0 1).le (hc1 1), show c 1 = lam by simp [c]]
    calc lam * dist (γ t) x < lam * r := by gcongr; exact hγb t
      _ ≤ ε := hlamr
  · exact hA _ (γ t).2 (hγb t) (hγ t h0 h1).2 _ (hc0 1) (hc1 1)
  · exact hA _ (γ t).2 (hγb t) (hγ t h0 h1).2 _ (hc0 s) (hc1 s)

/-- A real normed space is semi-locally simply connected in itself (radial contraction). -/
theorem isSLSCIn_univ_of_normedSpace : IsSLSCIn (univ : Set E) :=
  ⟨dense_univ, fun x => (isSLSCAt_of_radial_contraction (M := univ) (A := univ)
    (⟨x, trivial⟩ : (univ : Set E)) one_pos (fun _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ => trivial)).of_isOpenEmbedding isOpen_univ.isOpenEmbedding_subtypeVal⟩

/-- `rem:simple_cases`, first item, for a closed subset `X ∖ U` which is locally flat: every point
`x` of `X` (of `U` or of `X ∖ U`) has an open neighbourhood `V` with a homeomorphism `φ : V ≃ₜ E`
such that EITHER `V ⊆ U` (a chart at a point of `U` away from `X ∖ U`) OR `V ∖ U` is `φ⁻¹(L)` for a
closed proper linear subspace `L` of `E` (a flat chart at, or near, a point of `X ∖ U`). This is the
situation of a locally flat submanifold `X ∖ U` (of codimension `≥ 2`, or of any codimension `≥ 1`)
of an `E`-manifold `X`, `E = ℝⁿ`; `X ∖ U = ∅` is allowed. Then `U` is semi-locally simply connected
in `X`. -/
theorem isSLSCIn_of_locally_linear {U : Set X}
    (h : ∀ x, ∃ (V : Set X) (_ : IsOpen V) (_ : x ∈ V) (φ : V ≃ₜ E),
      V ⊆ U ∨ ∃ L : Submodule ℝ E, IsClosed (L : Set E) ∧ L ≠ ⊤ ∧
        ∀ v : V, (v : X) ∈ U ↔ φ v ∉ L) : IsSLSCIn U := by
  refine isSLSCIn_of_local fun x => ?_
  obtain ⟨V, hV, hxV, φ, hVU | ⟨L, hL, hLt, hφ⟩⟩ := h x
  · refine ⟨V, hV, hxV, ?_⟩
    have := (isSLSCIn_univ_of_normedSpace (E := E)).of_homeomorph φ
    rw [preimage_univ] at this
    rwa [show ((↑) : V → X) ⁻¹' U = univ from eq_univ_of_forall fun v => hVU v.2]
  · refine ⟨V, hV, hxV, ?_⟩
    have := (isSLSCIn_compl_submodule L hL hLt).of_homeomorph φ
    rwa [show φ ⁻¹' (L : Set E)ᶜ = ((↑) : V → X) ⁻¹' U by ext v; exact (hφ v).symm] at this

/-- In a simplex `τ`, a face `t ⊆ τ` containing a point `x + μ (v - x)` of the half-open segment
`]x, v]` (`x`, `v ∈ τ`) contains `v` (barycentric coordinates). -/
theorem mem_convexHull_face_of_add_smul_sub_mem {τ t : Finset E}
    (hτ : AffineIndependent ℝ ((↑) : τ → E)) (ht : t ⊆ τ) {x v : E}
    (hx : x ∈ convexHull ℝ (τ : Set E)) (hv : v ∈ convexHull ℝ (τ : Set E)) {μ : ℝ} (hμ : 0 < μ)
    (hμ1 : μ ≤ 1) (hw : x + μ • (v - x) ∈ convexHull ℝ (t : Set E)) :
    v ∈ convexHull ℝ (t : Set E) := by
  obtain ⟨a, ha0, ha1, hax⟩ := Finset.mem_convexHull'.1 hx
  obtain ⟨b, hb0, hb1, hbv⟩ := Finset.mem_convexHull'.1 hv
  obtain ⟨c, hc0, hc1, hcw⟩ := Finset.mem_convexHull'.1 hw
  set c' : E → ℝ := fun y => if y ∈ t then c y else 0
  set d : E → ℝ := fun y => (1 - μ) * a y + μ * b y
  have hc'1 : ∑ y ∈ τ, c' y = 1 := by
    rw [← hc1, ← Finset.sum_subset ht (fun y _ hy => by simp [c', hy])]
    exact Finset.sum_congr rfl fun y hy => by simp [c', hy]
  have hc'w : ∑ y ∈ τ, c' y • y = x + μ • (v - x) := by
    rw [← hcw, ← Finset.sum_subset ht (fun y _ hy => by simp [c', hy])]
    exact Finset.sum_congr rfl fun y hy => by simp [c', hy]
  have hd1 : ∑ y ∈ τ, d y = 1 := by
    simp only [d, Finset.sum_add_distrib, ← Finset.mul_sum, ha1, hb1]; ring
  have hdw : ∑ y ∈ τ, d y • y = x + μ • (v - x) := by
    simp only [d, add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum, hax, hbv]
    module
  have heq := hτ.eq_of_sum_eq_sum_subtype (hd1.trans hc'1.symm) (hdw.trans hc'w.symm)
  have hb : ∀ y ∈ τ, y ∉ t → b y = 0 := fun y hy hyt => by
    have h1 := heq y hy
    simp only [d, c', hyt, if_false] at h1
    have := ha0 y hy
    have := hb0 y hy
    nlinarith
  refine Finset.mem_convexHull'.2 ⟨b, fun y hy => hb0 y (ht hy), ?_, ?_⟩
  · rw [← hb1]
    exact Finset.sum_subset ht fun y hy hyt => hb y hy hyt
  · rw [← hbv]
    exact Finset.sum_subset ht fun y hy hyt => by rw [hb y hy hyt, zero_smul]

/-- `rem:simple_cases`, first item, simplicial case. Let `K` be a LOCALLY FINITE geometric
simplicial complex in a real normed space (its closed faces form a locally finite family of `E`;
`|K|` carries the subspace topology) and `S` a union of closed faces of `K` (the paper's "union of
facets", read as faces) whose complement `U` is dense in `|K|` (the paper's proviso). Then `U` is
semi-locally simply connected in `|K|` (radial contraction inside the closed star; no dimension
condition is needed). -/
theorem isSLSCIn_compl_faces_of_locallyFinite (K : Geometry.SimplicialComplex ℝ E)
    (hK : LocallyFinite fun τ : K.faces => convexHull ℝ ((τ : Finset E) : Set E))
    (F : Set (Finset E)) (hF : F ⊆ K.faces)
    (hd : Dense (((↑) : K.space → E) ⁻¹' (⋃ s ∈ F, convexHull ℝ (s : Set E))ᶜ)) :
    IsSLSCIn (((↑) : K.space → E) ⁻¹' (⋃ s ∈ F, convexHull ℝ (s : Set E))ᶜ) := by
  refine ⟨hd, fun x => ?_⟩
  -- the union of the faces not containing `x`
  set g : K.faces → Set E := fun τ =>
    if (x : E) ∈ convexHull ℝ ((τ : Finset E) : Set E) then ∅
    else convexHull ℝ ((τ : Finset E) : Set E)
  set B : Set E := ⋃ τ, g τ
  have hB : IsClosed B := by
    refine (hK.subset fun τ => ?_).isClosed_iUnion fun τ => ?_
    · simp only [g]; split_ifs
      · exact empty_subset _
      · exact subset_rfl
    · simp only [g]; split_ifs
      · exact isClosed_empty
      · exact (τ : Finset E).finite_toSet.isClosed_convexHull (𝕜 := ℝ)
  have hxB : (x : E) ∉ B := by
    simp only [B, mem_iUnion, not_exists]
    intro τ
    simp only [g]; split_ifs with h
    · exact notMem_empty _
    · exact h
  obtain ⟨r, hr, hrB⟩ := Metric.isOpen_iff.1 hB.isOpen_compl _ hxB
  -- a point of `|K|` near `x` lies in a face containing `x`
  have hface : ∀ v ∈ K.space, dist v (x : E) < r → ∃ τ ∈ K.faces,
      v ∈ convexHull ℝ (τ : Set E) ∧ (x : E) ∈ convexHull ℝ (τ : Set E) := by
    intro v hv hvr
    obtain ⟨τ, hτ, hvτ⟩ := Geometry.SimplicialComplex.mem_space_iff.1 hv
    refine ⟨τ, hτ, hvτ, by_contra fun hxτ => hrB (Metric.mem_ball.2 hvr) ?_⟩
    refine mem_iUnion.2 ⟨⟨τ, hτ⟩, ?_⟩
    simp only [g]
    rw [if_neg hxτ]
    exact hvτ
  refine isSLSCAt_of_radial_contraction x hr (fun v hv hvr μ hμ hμ1 => ?_)
    (fun v hv hvr hvA μ hμ hμ1 => ?_)
  · obtain ⟨τ, hτ, hvτ, hxτ⟩ := hface v hv hvr
    exact Geometry.SimplicialComplex.convexHull_subset_space hτ
      ((convex_convexHull ℝ _).add_smul_sub_mem hxτ hvτ ⟨hμ, hμ1⟩)
  · obtain ⟨τ, hτ, hvτ, hxτ⟩ := hface v hv hvr
    intro hw
    apply hvA
    obtain ⟨ρ, hρ, hwρ⟩ := mem_iUnion₂.1 hw
    have hwτ := (convex_convexHull ℝ _).add_smul_sub_mem hxτ hvτ ⟨hμ.le, hμ1⟩
    have hint := K.inter_subset_convexHull (hF hρ) hτ ⟨hwρ, hwτ⟩
    rw [← Finset.coe_inter] at hint
    have := mem_convexHull_face_of_add_smul_sub_mem (K.indep hτ) Finset.inter_subset_right hxτ hvτ
      hμ hμ1 hint
    exact mem_iUnion₂.2 ⟨ρ, hρ, convexHull_mono (by simp) this⟩

/-- `rem:simple_cases`, first item, simplicial case, for a FINITE geometric simplicial complex `K`
(a special case of `GX.isSLSCIn_compl_faces_of_locallyFinite`). -/
theorem isSLSCIn_compl_faces (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (F : Set (Finset E)) (hF : F ⊆ K.faces)
    (hd : Dense (((↑) : K.space → E) ⁻¹' (⋃ s ∈ F, convexHull ℝ (s : Set E))ᶜ)) :
    IsSLSCIn (((↑) : K.space → E) ⁻¹' (⋃ s ∈ F, convexHull ℝ (s : Set E))ᶜ) :=
  haveI : Finite K.faces := hK.to_subtype
  isSLSCIn_compl_faces_of_locallyFinite K (locallyFinite_of_finite _) F hF hd

/-! #### `rem:simple_cases`, first item, in the literal reading (DEC-55) -/

/-- **`rem:simple_cases`**, linear model, literal form: the complement of a closed proper linear
subspace of a real normed space is semi-locally simply connected in it. -/
theorem isSLSCInCC_compl_submodule (L : Submodule ℝ E) (hL : IsClosed (L : Set E))
    (hLt : L ≠ ⊤) : IsSLSCInCC ((L : Set E)ᶜ) :=
  (isSLSCIn_compl_submodule L hL hLt).isSLSCInCC

/-- **`rem:simple_cases`**, the radial criterion, literal form. -/
theorem isSLSCAtCC_of_radial_contraction {M A : Set E} (x : M) {r : ℝ} (hr : 0 < r)
    (hM : ∀ v ∈ M, dist v (x : E) < r → ∀ μ : ℝ, 0 ≤ μ → μ ≤ 1 → (x : E) + μ • (v - x) ∈ M)
    (hA : ∀ v ∈ M, dist v (x : E) < r → v ∈ A → ∀ μ : ℝ, 0 < μ → μ ≤ 1 →
      (x : E) + μ • (v - x) ∈ A) :
    IsSLSCAtCC (((↑) : M → E) ⁻¹' A) x :=
  (isSLSCAt_of_radial_contraction x hr hM hA).isSLSCAtCC

/-- A real normed space is semi-locally simply connected in itself, literal form. -/
theorem isSLSCInCC_univ_of_normedSpace : IsSLSCInCC (univ : Set E) :=
  (isSLSCIn_univ_of_normedSpace (E := E)).isSLSCInCC

/-- **`rem:simple_cases`, first item** (`RamcovGX.tex:1462`), manifold case, literal form, under
DEC-57 (a codimension-`≥ 2` submanifold is read as LOCALLY FLAT): if every point of `X` has an
open chart `V ≃ₜ E` either contained in `U` or carrying `V ∖ U` onto a closed proper linear
subspace of `E`, then `U` is semi-locally simply connected in `X` (no codimension condition is
needed). -/
theorem isSLSCInCC_of_locally_linear {U : Set X}
    (h : ∀ x, ∃ (V : Set X) (_ : IsOpen V) (_ : x ∈ V) (φ : V ≃ₜ E),
      V ⊆ U ∨ ∃ L : Submodule ℝ E, IsClosed (L : Set E) ∧ L ≠ ⊤ ∧
        ∀ v : V, (v : X) ∈ U ↔ φ v ∉ L) : IsSLSCInCC U :=
  (isSLSCIn_of_locally_linear h).isSLSCInCC

/-- **`rem:simple_cases`, first item** (`RamcovGX.tex:1462`), simplicial case, literal form,
under DEC-57 (`X = |K|` for a LOCALLY FINITE geometric simplicial complex, "facets" = closed
faces): if `S` is a union of closed faces of `K` with dense complement `U`, then `U` is
semi-locally simply connected in `|K|`. -/
theorem isSLSCInCC_compl_faces_of_locallyFinite (K : Geometry.SimplicialComplex ℝ E)
    (hK : LocallyFinite fun τ : K.faces => convexHull ℝ ((τ : Finset E) : Set E))
    (F : Set (Finset E)) (hF : F ⊆ K.faces)
    (hd : Dense (((↑) : K.space → E) ⁻¹' (⋃ s ∈ F, convexHull ℝ (s : Set E))ᶜ)) :
    IsSLSCInCC (((↑) : K.space → E) ⁻¹' (⋃ s ∈ F, convexHull ℝ (s : Set E))ᶜ) :=
  (isSLSCIn_compl_faces_of_locallyFinite K hK F hF hd).isSLSCInCC

/-- `rem:simple_cases`, simplicial case, finite complex, literal form. -/
theorem isSLSCInCC_compl_faces (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (F : Set (Finset E)) (hF : F ⊆ K.faces)
    (hd : Dense (((↑) : K.space → E) ⁻¹' (⋃ s ∈ F, convexHull ℝ (s : Set E))ᶜ)) :
    IsSLSCInCC (((↑) : K.space → E) ⁻¹' (⋃ s ∈ F, convexHull ℝ (s : Set E))ᶜ) :=
  (isSLSCIn_compl_faces K hK F hF hd).isSLSCInCC

end Linear

end General

/-! ### `rem:definition_semi_locally_simply_connected`: the harmonic archipelago

The counterexample to the converse (DEC-27, WP-35b). `𝔸 ⊆ ℂ × ℝ = ℝ³` is the graph, over the
open half-plane `Re z > 0` (the plane chart `w = 1/z`, in which the Hawaiian-earring circles
`Re(1/z) = k/2` through the base point `0` are the vertical lines `Re w = k/2`), of the height
`h(w) = sin²(2π Re w) / (1 + (Im w)²)`, together with the base point `0`: a hill of height `1`
over each crescent between consecutive circles, the summits `(1/c, 1)`, `c = k/2 + 1/4`,
accumulating at the missing point `(0, 1)`. Off the base point it is a surface
(`GX.isOpenEmbedding_archPt`). Every loop at the base point is homotopic into any neighbourhood
of it (`GX.archPush`: a compact loop climbs no far hill, and the near hills are pushed onto one
circle), but the loop `Re w = N/2` (`GX.archLoop`) is not null-homotopic: a null-homotopy misses
the summit of a far hill, and off that summit `GX.archF` maps `𝔸` to `ℂ ∖ {0}` with the loop of
winding number `1`. -/

section Archipelago

/-- The height of the harmonic archipelago above the point `w⁻¹` of the plane. -/
def archH (w : ℂ) : ℝ := Real.sin (2 * Real.pi * w.re) ^ 2 / (1 + w.im ^ 2)

/-- The point of the archipelago above `w⁻¹`. -/
def archE (w : ℂ) : ℂ × ℝ := (w⁻¹, archH w)

/-- The harmonic archipelago as a subset of `ℂ × ℝ = ℝ³`. -/
def archSet : Set (ℂ × ℝ) := {p | p = 0 ∨ (0 < p.1.re ∧ p.2 = archH p.1⁻¹)}

/-- The harmonic archipelago. -/
abbrev HarmonicArchipelago : Type := archSet

/-- The open right half-plane `Re w > 0`, the chart of the archipelago off its base point. -/
def archHalf : Set ℂ := {w | 0 < w.re}

local notation "𝔸" => HarmonicArchipelago

theorem archH_nonneg (w : ℂ) : 0 ≤ archH w := by unfold archH; positivity

theorem archH_le (w : ℂ) : archH w ≤ 1 / (1 + w.im ^ 2) := by
  unfold archH
  gcongr
  rw [sq_le_one_iff_abs_le_one]; exact Real.abs_sin_le_one _

theorem continuous_archH : Continuous archH := by
  unfold archH
  exact Continuous.div (by fun_prop) (by fun_prop) (fun w => by positivity)

theorem arch_re_inv_pos {w : ℂ} (hw : 0 < w.re) : 0 < (w⁻¹).re := by
  rw [Complex.inv_re]
  have : w ≠ 0 := fun h => by simp [h] at hw
  exact div_pos hw (Complex.normSq_pos.2 this)

theorem arch_ne_zero_of_re_pos {w : ℂ} (hw : 0 < w.re) : w ≠ 0 := fun h => by simp [h] at hw

theorem archE_mem {w : ℂ} (hw : 0 < w.re) : archE w ∈ archSet :=
  Or.inr ⟨arch_re_inv_pos hw, by simp [archE]⟩

/-- The base point of the archipelago. -/
def archO : 𝔸 := ⟨0, Or.inl rfl⟩

/-- The point of the archipelago above `w⁻¹`, `Re w > 0`. -/
def archPt (w : ℂ) (hw : 0 < w.re) : 𝔸 := ⟨archE w, archE_mem hw⟩

theorem archPt_ne (w : ℂ) (hw : 0 < w.re) : archPt w hw ≠ archO := fun h => by
  have := congrArg (fun p : 𝔸 => ((p : ℂ × ℝ).1)) h
  simp [archPt, archO, archE, arch_ne_zero_of_re_pos hw] at this

theorem arch_fst_eq_zero_iff (p : 𝔸) : (p : ℂ × ℝ).1 = 0 ↔ p = archO := by
  constructor
  · intro h
    rcases p.2 with h' | ⟨h1, -⟩
    · exact Subtype.ext h'
    · rw [h] at h1; simp at h1
  · rintro rfl; rfl

theorem arch_cases (p : 𝔸) :
    p = archO ∨ ∃ hw : 0 < (((p : ℂ × ℝ).1)⁻¹).re, p = archPt _ hw := by
  rcases p.2 with h | ⟨h1, h2⟩
  · exact Or.inl (Subtype.ext h)
  · refine Or.inr ⟨arch_re_inv_pos h1, Subtype.ext ?_⟩
    show (p : ℂ × ℝ) = archE _
    ext
    · simp [archE]
    · simp [archE, h2]

theorem dist_archO (p : 𝔸) : dist p archO = max ‖(p : ℂ × ℝ).1‖ |(p : ℂ × ℝ).2| := by
  rw [Subtype.dist_eq, Prod.dist_eq]
  simp [archO, dist_zero_right]

theorem dist_archPt (w : ℂ) (hw : 0 < w.re) : dist (archPt w hw) archO = max ‖w‖⁻¹ (archH w) := by
  rw [dist_archO]
  simp [archPt, archE, norm_inv, abs_of_nonneg (archH_nonneg w)]

theorem arch_norm_inv_le_re {w : ℂ} (hw : 0 < w.re) : ‖w‖⁻¹ ≤ (w.re)⁻¹ :=
  inv_anti₀ hw (Complex.re_le_norm w)

/-- The chart `w ↦ archPt w` of the archipelago off its base point. -/
def archHomeo : archHalf ≃ₜ {p : 𝔸 // p ≠ archO} where
  toFun w := ⟨archPt w.1 w.2, archPt_ne _ _⟩
  invFun p := ⟨((p.1 : ℂ × ℝ).1)⁻¹, by
    rcases arch_cases p.1 with h | ⟨hw, -⟩
    · exact absurd h p.2
    · exact hw⟩
  left_inv w := Subtype.ext (by simp [archPt, archE])
  right_inv p := by
    rcases arch_cases p.1 with h | ⟨hw, h⟩
    · exact absurd h p.2
    · exact Subtype.ext h.symm
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    show Continuous fun w : archHalf => archE w.1
    unfold archE
    exact (continuous_subtype_val.inv₀ fun w => arch_ne_zero_of_re_pos w.2).prodMk
      (continuous_archH.comp continuous_subtype_val)
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    refine Continuous.inv₀ (continuous_fst.comp (continuous_subtype_val.comp
      continuous_subtype_val)) fun p => ?_
    exact fun h => p.2 ((arch_fst_eq_zero_iff _).1 h)

theorem isOpen_ne_archO : IsOpen {p : 𝔸 | p ≠ archO} := isOpen_ne

/-- `w ↦ archPt w` is an open embedding of the half-plane onto the archipelago minus its base
point. -/
theorem isOpenEmbedding_archPt :
    IsOpenEmbedding (fun w : archHalf => archPt w.1 w.2) :=
  isOpen_ne_archO.isOpenEmbedding_subtypeVal.comp archHomeo.isOpenEmbedding

/-- A compact subset of the archipelago stays away from its missing limit segment
`{0} × ]0,1]`: on it, height `≥ δ` forces `‖z‖ ≥ r`. -/
theorem arch_compact_bound {K : Set 𝔸} (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r > 0, ∀ p ∈ K, δ ≤ (p : ℂ × ℝ).2 → r ≤ ‖(p : ℂ × ℝ).1‖ := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, fun p hp => absurd hp (notMem_empty p)⟩
  set f : 𝔸 → ℝ := fun p => ‖(p : ℂ × ℝ).1‖ + max 0 (δ - (p : ℂ × ℝ).2)
  have hf : Continuous f := by fun_prop
  obtain ⟨p₀, hp₀, hmin⟩ := hK.exists_isMinOn hne hf.continuousOn
  refine ⟨f p₀, ?_, fun p hp hδp => ?_⟩
  · by_cases h0 : (p₀ : ℂ × ℝ).1 = 0
    · have := (arch_fst_eq_zero_iff p₀).1 h0
      subst this
      simp [f, archO, hδ]
    · have : 0 < ‖(p₀ : ℂ × ℝ).1‖ := norm_pos_iff.2 h0
      have : 0 ≤ max 0 (δ - (p₀ : ℂ × ℝ).2) := le_max_left _ _
      show 0 < ‖(p₀ : ℂ × ℝ).1‖ + max 0 (δ - (p₀ : ℂ × ℝ).2)
      linarith
  · have := hmin hp
    simp only [mem_setOf_eq] at this
    have hm : max 0 (δ - (p : ℂ × ℝ).2) = 0 := max_eq_left (by linarith)
    calc f p₀ ≤ f p := this
      _ = ‖(p : ℂ × ℝ).1‖ := by simp only [f, hm, add_zero]

/-! #### Paths to the base point: pushing `|Im w|` to infinity -/

section Ray

variable (w : ℂ) (sg : ℝ)

/-- First coordinate of the ray from `archPt w` to the base point (`z = w⁻¹` moved along the
circle `Re(1/z) = Re w`). -/
def archRayZ (s : ℝ) : ℂ :=
  ((1 - s : ℝ) : ℂ) * w⁻¹ / (((1 - s : ℝ) : ℂ) + ((sg * s : ℝ) : ℂ) * w⁻¹ * Complex.I)

/-- Second coordinate (height) of the ray. -/
def archRayH (s : ℝ) : ℝ :=
  (1 - s) ^ 2 * Real.sin (2 * Real.pi * w.re) ^ 2 / ((1 - s) ^ 2 + ((1 - s) * w.im + sg * s) ^ 2)

/-- The point `w + i sg s / (1 - s)` of the half-plane. -/
def archRayW (s : ℝ) : ℂ := w + ((sg * s / (1 - s) : ℝ) : ℂ) * Complex.I

variable {w sg}

theorem archRayW_re (s : ℝ) : (archRayW w sg s).re = w.re := by
  simp only [archRayW, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

theorem archRayW_im (s : ℝ) : (archRayW w sg s).im = w.im + sg * s / (1 - s) := by
  simp only [archRayW, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

theorem archRayZ_den_ne (hw : 0 < w.re) (hsg : sg ^ 2 = 1) (s : ℝ) :
    ((1 - s : ℝ) : ℂ) + ((sg * s : ℝ) : ℂ) * w⁻¹ * Complex.I ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp at him hre
  have hsg0 : sg ≠ 0 := by rintro rfl; norm_num at hsg
  have hz := arch_re_inv_pos hw
  rcases him with ((h1 | h1) | h1)
  · exact hsg0 h1
  · subst h1; simp at hre
  · rcases h1 with h1 | h1
    · linarith
    · simp [h1] at hw

theorem archRayH_den_pos (hsg : sg ^ 2 = 1) (s : ℝ) :
    0 < (1 - s) ^ 2 + ((1 - s) * w.im + sg * s) ^ 2 := by
  by_cases h : 1 - s = 0
  · have : s = 1 := by linarith
    subst this; simp [hsg]
  · have := pow_pos (abs_pos.2 h) 2
    rw [sq_abs] at this
    positivity

theorem archRayZ_eq (hw : 0 < w.re) (hsg : sg ^ 2 = 1) {s : ℝ} (hs : s < 1) :
    archRayZ w sg s = (archRayW w sg s)⁻¹ := by
  have hD := archRayZ_den_ne hw hsg s
  have h1 : (1 - s : ℝ) ≠ 0 := by linarith
  have hw0 := arch_ne_zero_of_re_pos hw
  refine eq_inv_of_mul_eq_one_left ?_
  unfold archRayZ archRayW
  rw [div_mul_eq_mul_div, div_eq_one_iff_eq hD]
  have h1' : (1 : ℂ) - s ≠ 0 := by exact_mod_cast h1
  push_cast
  field_simp

theorem archRayH_eq (hsg : sg ^ 2 = 1) {s : ℝ} (hs : s < 1) : archRayH w sg s = archH (archRayW w sg s) := by
  have h1 : (1 - s : ℝ) ≠ 0 := by linarith
  unfold archRayH archH
  rw [archRayW_re, archRayW_im]
  have := archRayH_den_pos (w := w) hsg s
  field_simp

theorem arch_norm_le_norm_rayW (hsgw : 0 ≤ sg * w.im) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < 1) :
    ‖w‖ ≤ ‖archRayW w sg s‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply,
    archRayW_re, archRayW_im]
  have h1 : 0 < 1 - s := by linarith
  have : 0 ≤ sg * s / (1 - s) * w.im := by
    rw [div_mul_eq_mul_div, mul_comm sg s, mul_assoc]
    exact div_nonneg (mul_nonneg hs0 hsgw) h1.le
  nlinarith [sq_nonneg (sg * s / (1 - s))]

theorem archH_rayW_le (hsgw : 0 ≤ sg * w.im) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < 1) :
    archH (archRayW w sg s) ≤ archH w := by
  unfold archH
  rw [archRayW_re, archRayW_im]
  have h1 : 0 < 1 - s := by linarith
  have : 0 ≤ sg * s / (1 - s) * w.im := by
    rw [div_mul_eq_mul_div, mul_comm sg s, mul_assoc]
    exact div_nonneg (mul_nonneg hs0 hsgw) h1.le
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  nlinarith [sq_nonneg (sg * s / (1 - s))]

theorem archRayMem (hw : 0 < w.re) (hsg : sg ^ 2 = 1) {s : ℝ} (hs1 : s ≤ 1) :
    (archRayZ w sg s, archRayH w sg s) ∈ archSet := by
  rcases lt_or_eq_of_le hs1 with hs | rfl
  · have hre : 0 < (archRayW w sg s).re := by rw [archRayW_re]; exact hw
    have : (archRayZ w sg s, archRayH w sg s) = archE (archRayW w sg s) := by
      rw [archRayZ_eq hw hsg hs, archRayH_eq hsg hs]; rfl
    rw [this]; exact archE_mem hre
  · left; simp [archRayZ, archRayH]

/-- The path from `archPt w` to the base point along which `|Im w|` increases to infinity
(`sg = ±1`, `sg · Im w ≥ 0`): the distance to the base point does not increase along it. -/
def archRay (hw : 0 < w.re) (hsg : sg ^ 2 = 1) : Path (archPt w hw) archO where
  toFun s := ⟨(archRayZ w sg s, archRayH w sg s), archRayMem hw hsg s.2.2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.prodMk ?_ ?_) _
    · unfold archRayZ
      exact Continuous.div (by fun_prop) (by fun_prop) fun s => archRayZ_den_ne hw hsg s
    · unfold archRayH
      exact Continuous.div (by fun_prop) (by fun_prop) fun s => (archRayH_den_pos hsg s).ne'
  source' := by
    apply Subtype.ext
    show (archRayZ w sg 0, archRayH w sg 0) = archE w
    simp [archRayZ, archRayH, archE, archH]
  target' := by
    apply Subtype.ext
    show (archRayZ w sg 1, archRayH w sg 1) = 0
    simp [archRayZ, archRayH]

theorem dist_archRay_le (hw : 0 < w.re) (hsg : sg ^ 2 = 1) (hsgw : 0 ≤ sg * w.im) (s : I) :
    dist (archRay hw hsg s) archO ≤ dist (archPt w hw) archO := by
  rcases lt_or_eq_of_le s.2.2 with hs | hs
  · have hre : 0 < (archRayW w sg s).re := by rw [archRayW_re]; exact hw
    have : archRay hw hsg s = archPt _ hre := Subtype.ext (by
      show (archRayZ w sg s, archRayH w sg s) = archE _
      rw [archRayZ_eq hw hsg hs, archRayH_eq hsg hs]; rfl)
    rw [this, dist_archPt, dist_archPt]
    have hn := arch_norm_le_norm_rayW hsgw s.2.1 hs
    exact max_le_max (inv_anti₀ (norm_pos_iff.2 (arch_ne_zero_of_re_pos hw)) hn)
      (archH_rayW_le hsgw s.2.1 hs)
  · have : s = 1 := Subtype.ext hs
    rw [this, Path.target, dist_self]; exact dist_nonneg

end Ray

/-- Every point is joined to the base point inside every ball around the base point that
contains it. -/
theorem arch_joinedIn_ball (p : 𝔸) {ε : ℝ} (hp : dist p archO < ε) :
    JoinedIn (Metric.ball archO ε) p archO := by
  rcases arch_cases p with rfl | ⟨hw, h⟩
  · exact JoinedIn.refl hp
  · rw [h] at hp ⊢
    set w := ((p : ℂ × ℝ).1)⁻¹
    set sg : ℝ := if 0 ≤ w.im then 1 else -1
    have hsg : sg ^ 2 = 1 := by simp only [sg]; split_ifs <;> norm_num
    have hsgw : 0 ≤ sg * w.im := by
      simp only [sg]; split_ifs with h
      · simpa using h
      · nlinarith
    exact ⟨archRay hw hsg, fun s => lt_of_le_of_lt (dist_archRay_le hw hsg hsgw s) hp⟩

instance : PathConnectedSpace 𝔸 :=
  ⟨⟨archO⟩, fun x y => by
    have hx := (arch_joinedIn_ball x (lt_add_one (dist x archO))).joined
    have hy := (arch_joinedIn_ball y (lt_add_one (dist y archO))).joined
    exact hx.trans hy.symm⟩

instance : LocPathConnectedSpace archHalf :=
  (isOpen_lt continuous_const Complex.continuous_re).locPathConnectedSpace

instance : LocPathConnectedSpace 𝔸 := by
  refine locPathConnectedSpace_iff_pathComponentIn_mem_nhds.2 fun x u hu hxu => ?_
  rcases arch_cases x with rfl | ⟨hw, hx⟩
  · obtain ⟨ε, hε, hεu⟩ := Metric.isOpen_iff.1 hu archO hxu
    refine mem_of_superset (Metric.ball_mem_nhds archO hε) fun q hq => ?_
    exact ((arch_joinedIn_ball q hq).symm).mono hεu
  · set f := fun w : archHalf => archPt w.1 w.2
    have hf := isOpenEmbedding_archPt
    set w : archHalf := ⟨_, hw⟩
    have hfw : f w = x := hx.symm
    have hu' : IsOpen (f ⁻¹' u) := hu.preimage hf.continuous
    have hwu : w ∈ f ⁻¹' u := by show f w ∈ u; rw [hfw]; exact hxu
    have h1 := locPathConnectedSpace_iff_pathComponentIn_mem_nhds.1 inferInstance w _ hu' hwu
    have h2 : f '' pathComponentIn (f ⁻¹' u) w ∈ 𝓝 (f w) := (hf.image_mem_nhds).2 h1
    rw [hfw] at h2
    refine mem_of_superset h2 ?_
    rintro _ ⟨y, hy, rfl⟩
    have : JoinedIn u (f w) (f y) := (hy.map hf.continuous).mono (image_preimage_subset f u)
    rw [hfw] at this
    exact this

/-! #### The deformation pushing the hills `Re w < n` onto the circle `Re w = n` -/

section Push

/-- The half-plane coordinate `p ↦ (p.1)⁻¹` (`0` at the base point). -/
def archW (p : 𝔸) : ℂ := ((p : ℂ × ℝ).1)⁻¹

theorem archPt_archW {p : 𝔸} (hw : 0 < (archW p).re) : archPt (archW p) hw = p := by
  rcases arch_cases p with h | ⟨hw', h⟩
  · subst h; simp [archW, archO] at hw
  · exact h.symm

theorem arch_fst_ne_zero_of_re_pos {p : 𝔸} (hw : 0 < (archW p).re) : (p : ℂ × ℝ).1 ≠ 0 := by
  intro h; simp [archW, h] at hw

theorem re_archW_pos {p : 𝔸} (h : (p : ℂ × ℝ).1 ≠ 0) : 0 < (archW p).re := by
  rcases arch_cases p with h' | ⟨hw, -⟩
  · exact absurd ((arch_fst_eq_zero_iff _).2 h') h
  · exact hw

/-- `w ↦ w + t·max(0, n - Re w)`. -/
def archPushW (n t : ℝ) (w : ℂ) : ℂ := w + ((t * max 0 (n - w.re) : ℝ) : ℂ)

theorem archPushW_re (n t : ℝ) (w : ℂ) : (archPushW n t w).re = w.re + t * max 0 (n - w.re) := by
  simp [archPushW]

theorem archPushW_im (n t : ℝ) (w : ℂ) : (archPushW n t w).im = w.im := by simp [archPushW]

theorem archPushW_re_pos {n t : ℝ} {w : ℂ} (ht : 0 ≤ t) (hw : 0 < w.re) : 0 < (archPushW n t w).re := by
  rw [archPushW_re]; have := mul_nonneg ht (le_max_left 0 (n - w.re)); linarith

theorem archPushW_zero (n : ℝ) (w : ℂ) : archPushW n 0 w = w := by simp [archPushW]

theorem archPushW_of_le {n t : ℝ} {w : ℂ} (h : n ≤ w.re) : archPushW n t w = w := by
  simp [archPushW, max_eq_left (sub_nonpos.2 h)]

theorem archPushW_one_re {n : ℝ} {w : ℂ} (h : w.re < n) : (archPushW n 1 w).re = n := by
  rw [archPushW_re, max_eq_right (sub_nonneg.2 h.le)]; ring

theorem dist_archE_zero (w : ℂ) : dist (archE w) 0 = max ‖w‖⁻¹ (archH w) := by
  rw [Prod.dist_eq]
  simp [archE, norm_inv, abs_of_nonneg (archH_nonneg w)]

/-- The estimate behind the continuity of the push at the base point: points close to the base
point stay close to it, uniformly in time. -/
theorem archPush_estimate (n : ℝ) {ε : ℝ} (hε : 0 < ε) : ∃ δ > 0, ∀ w : ℂ, 0 < w.re →
    max ‖w‖⁻¹ (archH w) < δ → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      max ‖archPushW n t w‖⁻¹ (archH (archPushW n t w)) < ε := by
  set R : ℝ := |n| + 1 + 1 / ε
  have hR : 0 < R := by positivity
  refine ⟨min ε (1 / R), lt_min hε (by positivity), fun w hw hδ t ht0 ht1 => ?_⟩
  have hδ1 := lt_of_lt_of_le hδ (min_le_left _ _)
  have hδ2 := lt_of_lt_of_le hδ (min_le_right _ _)
  by_cases hnw : n ≤ w.re
  · rw [archPushW_of_le hnw]; exact hδ1
  rw [not_le] at hnw
  have hw0 : 0 < ‖w‖ := norm_pos_iff.2 (arch_ne_zero_of_re_pos hw)
  have hwR : R < ‖w‖ := by
    have := (max_lt_iff.1 hδ2).1
    rw [inv_lt_comm₀ hw0 (by positivity), one_div, inv_inv] at this
    exact this
  have him : 1 + 1 / ε < |w.im| := by
    have h1 := Complex.norm_le_abs_re_add_abs_im w
    have h2 : |w.re| = w.re := abs_of_pos hw
    have h3 : w.re ≤ |n| := hnw.le.trans (le_abs_self n)
    simp only [R] at hwR
    linarith
  have hε' : 1 / ε < |w.im| := by linarith
  have him1 : 1 < |w.im| := by linarith [show (0 : ℝ) < 1 / ε by positivity]
  have hpos : 0 < |w.im| := by linarith
  rw [max_lt_iff]
  constructor
  · calc ‖archPushW n t w‖⁻¹ ≤ |(archPushW n t w).im|⁻¹ :=
          inv_anti₀ (by rwa [archPushW_im]) (Complex.abs_im_le_norm _)
      _ = |w.im|⁻¹ := by rw [archPushW_im]
      _ < ε := by
          rw [inv_lt_comm₀ hpos hε]; rwa [one_div] at hε'
  · calc archH (archPushW n t w) ≤ 1 / (1 + (archPushW n t w).im ^ 2) := archH_le _
      _ = 1 / (1 + |w.im| ^ 2) := by rw [archPushW_im, sq_abs]
      _ < ε := by
          rw [div_lt_iff₀ (by positivity)]
          rw [div_lt_iff₀ hε] at hε'
          nlinarith

/-- The value of the push. -/
def archPushVal (n : ℝ) (x : I × 𝔸) : ℂ × ℝ :=
  if (x.2 : ℂ × ℝ).1 = 0 then 0 else archE (archPushW n x.1 (archW x.2))

theorem archPushVal_mem (n : ℝ) (x : I × 𝔸) : archPushVal n x ∈ archSet := by
  unfold archPushVal
  split_ifs with h
  · exact Or.inl rfl
  · exact archE_mem (archPushW_re_pos x.1.2.1 (re_archW_pos h))

theorem continuous_archPushVal (n : ℝ) : Continuous (archPushVal n) := by
    refine continuous_iff_continuousAt.2 fun x => ?_
    obtain ⟨t, p⟩ := x
    by_cases hp : (p : ℂ × ℝ).1 = 0
    · rw [ContinuousAt, show archPushVal n (t, p) = 0 by simp [archPushVal, hp],
        Metric.tendsto_nhds]
      intro ε hε
      obtain ⟨δ, hδ, hest⟩ := archPush_estimate n hε
      have hpo : p = archO := (arch_fst_eq_zero_iff p).1 hp
      subst hpo
      filter_upwards [(continuous_snd.tendsto (t, archO)).eventually
        (Metric.ball_mem_nhds archO hδ)] with x hx
      by_cases hx0 : (x.2 : ℂ × ℝ).1 = 0
      · simp [archPushVal, hx0, hε]
      · simp only [archPushVal, if_neg hx0]
        rw [dist_archE_zero]
        have hw := re_archW_pos hx0
        have hd : dist x.2 archO < δ := hx
        rw [← archPt_archW hw, dist_archPt] at hd
        exact hest _ hw hd _ x.1.2.1 x.1.2.2
    · have hW : ContinuousAt (fun x : I × 𝔸 => archW x.2) (t, p) :=
        ((continuous_fst.comp continuous_subtype_val).comp continuous_snd).continuousAt.inv₀ hp
      have hev : archPushVal n =ᶠ[𝓝 (t, p)] fun x => archE (archPushW n x.1 (archW x.2)) := by
        have : IsOpen {x : I × 𝔸 | (x.2 : ℂ × ℝ).1 ≠ 0} :=
          isOpen_ne_fun ((continuous_fst.comp continuous_subtype_val).comp continuous_snd)
            continuous_const
        filter_upwards [this.mem_nhds hp] with x hx
        simp only [archPushVal, if_neg (show (x.2 : ℂ × ℝ).1 ≠ 0 from hx)]
      have hpush : ContinuousAt (fun x : I × 𝔸 => archPushW n x.1 (archW x.2)) (t, p) := by
        unfold archPushW
        exact hW.add (Complex.continuous_ofReal.continuousAt.comp
          (((continuous_subtype_val.comp continuous_fst).continuousAt).mul
            (continuousAt_const.max (continuousAt_const.sub
              (Complex.continuous_re.continuousAt.comp hW)))))
      have hne : archPushW n t (archW p) ≠ 0 :=
        arch_ne_zero_of_re_pos (archPushW_re_pos t.2.1 (re_archW_pos hp))
      have hE : ContinuousAt archE (archPushW n t (archW p)) :=
        (continuousAt_inv₀ hne).prodMk continuous_archH.continuousAt
      have hc : ContinuousAt (fun x : I × 𝔸 => archE (archPushW n x.1 (archW x.2))) (t, p) :=
        ContinuousAt.comp (x := (t, p)) (f := fun x : I × 𝔸 => archPushW n x.1 (archW x.2)) hE hpush
      exact hc.congr hev.symm

/-- The push `[0,1] × 𝔸 → 𝔸`: at time `t` the hills `Re w < n` are pushed by `t·(n - Re w)`
towards the circle `Re w = n`; the base point is fixed. -/
def archPush (n : ℝ) : C(I × 𝔸, 𝔸) where
  toFun x := ⟨archPushVal n x, archPushVal_mem n x⟩
  continuous_toFun := (continuous_archPushVal n).subtype_mk _

theorem archPush_apply (n : ℝ) (x : I × 𝔸) : (archPush n x : ℂ × ℝ) = archPushVal n x := rfl

theorem archPush_zero (n : ℝ) (p : 𝔸) : archPush n (0, p) = p := by
  apply Subtype.ext
  rw [archPush_apply]
  unfold archPushVal
  split_ifs with h
  · have := (arch_fst_eq_zero_iff p).1 h
    subst this; rfl
  · show archE (archPushW n 0 (archW p)) = (p : ℂ × ℝ)
    rw [archPushW_zero]
    exact congrArg Subtype.val (archPt_archW (re_archW_pos h))

theorem archPush_base (n : ℝ) (t : I) : archPush n (t, archO) = archO :=
  Subtype.ext (by rw [archPush_apply]; simp [archPushVal, archO])

end Push

/-! #### Semi-local simple connectedness in itself -/

/-- After the push `archPush n` at time `1`, a point `p` of a set on which height `≥ ε/2` forces
`‖z‖ ≥ r` lies in the `ε`-ball around the base point, as soon as `1/n < min r ε`. -/
theorem dist_archPush_one_lt {n : ℕ} {ε r : ℝ} (hε : 0 < ε) (hn : 0 < n) (hnr : (n : ℝ)⁻¹ < r)
    (hnε : (n : ℝ)⁻¹ < ε) {p : 𝔸} (hp : ε / 2 ≤ (p : ℂ × ℝ).2 → r ≤ ‖(p : ℂ × ℝ).1‖) :
    dist (archPush n (1, p)) archO < ε := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  by_cases h0 : (p : ℂ × ℝ).1 = 0
  · have := (arch_fst_eq_zero_iff p).1 h0
    subst this
    rw [archPush_base, dist_self]; exact hε
  have hw := re_archW_pos h0
  set w := archW p
  have hdist : dist (archPush n (1, p)) archO = dist (archE (archPushW n 1 w)) 0 := by
    rw [Subtype.dist_eq, archPush_apply]
    simp only [archPushVal, if_neg h0]; rfl
  rw [hdist, dist_archE_zero, max_lt_iff]
  by_cases hnw : (n : ℝ) ≤ w.re
  · rw [archPushW_of_le hnw]
    have hwn : ‖w‖⁻¹ ≤ (n : ℝ)⁻¹ := (arch_norm_inv_le_re hw).trans (inv_anti₀ hn' hnw)
    refine ⟨hwn.trans_lt hnε, ?_⟩
    have hpw : p = archPt w hw := (archPt_archW hw).symm
    have h2 : (p : ℂ × ℝ).2 = archH w := by rw [hpw]; rfl
    have h1 : ‖(p : ℂ × ℝ).1‖ = ‖w‖⁻¹ := by rw [hpw]; simp [archPt, archE, norm_inv]
    by_contra hge
    rw [not_lt] at hge
    have := hp (by rw [h2]; linarith)
    rw [h1] at this
    linarith
  · rw [not_le] at hnw
    have hre := archPushW_one_re hnw
    refine ⟨?_, ?_⟩
    · calc ‖archPushW n 1 w‖⁻¹ ≤ ((archPushW n 1 w).re)⁻¹ := arch_norm_inv_le_re (by rw [hre]; exact hn')
        _ = (n : ℝ)⁻¹ := by rw [hre]
        _ < ε := hnε
    · have : archH (archPushW n 1 w) = 0 := by
        unfold archH
        rw [hre, show 2 * Real.pi * (n : ℝ) = ((2 * n : ℕ) : ℝ) * Real.pi by push_cast; ring,
          Real.sin_nat_mul_pi]
        simp
      rw [this]; exact hε

/-- The archipelago is semi-locally simply connected in itself at its base point, in the
homotopy form: every loop is homotopic (rel ends) to a loop in any given neighbourhood. -/
theorem harmonicArchipelago_isSLSCAt_base : IsSLSCAt (univ : Set 𝔸) archO := by
  refine ⟨univ, isOpen_univ, isPreconnected_univ, trivial, fun γ _ =>
    ⟨fun _ _ _ => trivial, fun W hW => ?_⟩⟩
  obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.1 hW
  obtain ⟨r, hr, hK⟩ := arch_compact_bound (isCompact_range γ.continuous) (half_pos hε)
  obtain ⟨n, hn⟩ := exists_nat_gt (max r⁻¹ ε⁻¹)
  have hn0 : 0 < n := by
    have : (0 : ℝ) < n := lt_of_le_of_lt (le_max_of_le_left (inv_pos.2 hr).le) hn
    exact_mod_cast this
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hnr : (n : ℝ)⁻¹ < r := by
    rw [inv_lt_comm₀ hn' hr]; exact lt_of_le_of_lt (le_max_left _ _) hn
  have hnε : (n : ℝ)⁻¹ < ε := by
    rw [inv_lt_comm₀ hn' hε]; exact lt_of_le_of_lt (le_max_right _ _) hn
  let γ' : Path archO archO :=
    { toFun := fun t => archPush n (1, γ t)
      continuous_toFun := (archPush n).continuous.comp (continuous_const.prodMk γ.continuous)
      source' := by simp [archPush_base]
      target' := by simp [archPush_base] }
  let H : Path.Homotopy γ γ' :=
    { toFun := fun x => archPush n (x.1, γ x.2)
      continuous_toFun := (archPush n).continuous.comp (continuous_fst.prodMk
        (γ.continuous.comp continuous_snd))
      map_zero_left := fun t => archPush_zero _ _
      map_one_left := fun t => rfl
      prop' := fun s t ht => by
        rcases ht with rfl | rfl
        · simp [archPush_base]
        · simp [archPush_base] }
  refine ⟨γ', fun t _ _ => ⟨hεW ?_, trivial⟩, H, fun _ _ _ _ => trivial⟩
  exact dist_archPush_one_lt hε hn0 hnr hnε (hK _ (mem_range_self t))

/-- Off its base point the archipelago is a surface (the half-plane chart). -/
theorem harmonicArchipelago_isSLSCAt_pt (w : ℂ) (hw : 0 < w.re) :
    IsSLSCAt (univ : Set 𝔸) (archPt w hw) := by
  have h := isSLSCAt_of_radial_contraction (M := archHalf) (A := univ) ⟨w, hw⟩ one_pos
    (fun v hv _ μ hμ0 hμ1 => by
      show 0 < (w + μ • (v - w)).re
      have hv' : 0 < v.re := hv
      simp only [Complex.add_re, Complex.smul_re, Complex.sub_re, smul_eq_mul]
      rcases eq_or_lt_of_le hμ0 with h0 | h0
      · rw [← h0]; linarith
      · nlinarith [mul_pos h0 hv', mul_nonneg (sub_nonneg.2 hμ1) hw.le])
    (fun _ _ _ _ _ _ _ => trivial)
  rw [preimage_univ] at h
  have h' := IsSLSCAt.of_isOpenEmbedding isOpenEmbedding_archPt (A := univ)
    (by rw [preimage_univ]; exact h)
  exact h'

/-- **`rem:definition_semi_locally_simply_connected`, the counterexample to the converse**:
the harmonic archipelago is semi-locally simply connected in itself (homotopy form). -/
theorem harmonicArchipelago_isSLSCIn : IsSLSCIn (univ : Set 𝔸) := by
  refine ⟨dense_univ, fun p => ?_⟩
  rcases arch_cases p with rfl | ⟨hw, h⟩
  · exact harmonicArchipelago_isSLSCAt_base
  · rw [h]; exact harmonicArchipelago_isSLSCAt_pt _ hw

/-- The harmonic archipelago is semi-locally simply connected in itself in the literal sense of
`def:semi_locally_simple_connectedness` (DEC-55). -/
theorem harmonicArchipelago_isSLSCInCC : IsSLSCInCC (univ : Set 𝔸) :=
  harmonicArchipelago_isSLSCIn.isSLSCInCC

/-! #### The small loops `Re w = N/2` are not null-homotopic -/

section Loop

/-- The circle `Re(1/z) = N/2` through the base point, `z = 4 sin(πs) / (2N sin(πs) + i cos(πs))`
(`1/z = N/2 + (i/4) cot(πs)`). -/
def archLz (N : ℕ) (s : ℝ) : ℂ :=
  ((4 * Real.sin (Real.pi * s) : ℝ) : ℂ) /
    (((2 * N * Real.sin (Real.pi * s) : ℝ) : ℂ) + (Real.cos (Real.pi * s) : ℂ) * Complex.I)

theorem arch_re_ofReal_add_mul_I (a b : ℝ) : ((a : ℂ) + (b : ℂ) * Complex.I).re = a := by simp

theorem arch_im_ofReal_add_mul_I (a b : ℝ) : ((a : ℂ) + (b : ℂ) * Complex.I).im = b := by simp

theorem arch_ofReal_add_mul_I_ne {a b : ℝ} (h : a ≠ 0 ∨ b ≠ 0) : (a : ℂ) + (b : ℂ) * Complex.I ≠ 0 := by
  intro h0
  have h1 := congrArg Complex.re h0
  have h2 := congrArg Complex.im h0
  rw [arch_re_ofReal_add_mul_I, Complex.zero_re] at h1
  rw [arch_im_ofReal_add_mul_I, Complex.zero_im] at h2
  rcases h with h | h
  · exact h h1
  · exact h h2

theorem archLz_den_ne {N : ℕ} (hN : 0 < N) (s : ℝ) :
    (((2 * N * Real.sin (Real.pi * s) : ℝ) : ℂ) + (Real.cos (Real.pi * s) : ℂ) * Complex.I) ≠ 0 := by
  apply arch_ofReal_add_mul_I_ne
  by_contra h
  push Not at h
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hs : Real.sin (Real.pi * s) = 0 := by
    rcases mul_eq_zero.1 h.1 with h' | h'
    · exfalso; exact hN' (by linarith)
    · exact h'
  have := Real.sin_sq_add_cos_sq (Real.pi * s)
  rw [hs, h.2] at this; norm_num at this

theorem archLz_div_eq_inv (S C n : ℝ) (hS : S ≠ 0) :
    ((4 * S : ℝ) : ℂ) / (((2 * n * S : ℝ) : ℂ) + (C : ℂ) * Complex.I) =
      (((n / 2 : ℝ) : ℂ) + ((C / (4 * S) : ℝ) : ℂ) * Complex.I)⁻¹ := by
  have hS' : (S : ℂ) ≠ 0 := by exact_mod_cast hS
  rw [show (((n / 2 : ℝ) : ℂ) + ((C / (4 * S) : ℝ) : ℂ) * Complex.I) =
      (((2 * n * S : ℝ) : ℂ) + (C : ℂ) * Complex.I) / ((4 * S : ℝ) : ℂ) by
    push_cast; field_simp; ring, inv_div]

theorem archLz_eq {N : ℕ} {s : ℝ} (hs : Real.sin (Real.pi * s) ≠ 0) :
    archLz N s = (((N / 2 : ℝ) : ℂ) +
      ((Real.cos (Real.pi * s) / (4 * Real.sin (Real.pi * s)) : ℝ) : ℂ) * Complex.I)⁻¹ :=
  archLz_div_eq_inv _ _ _ hs

theorem archLz_of_sin_eq_zero {N : ℕ} {s : ℝ} (hs : Real.sin (Real.pi * s) = 0) :
    archLz N s = 0 := by
  simp [archLz, hs]

theorem archH_half_nat (N : ℕ) (v : ℝ) : archH (((N / 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) = 0 := by
  unfold archH
  have : (((N / 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I).re = N / 2 := by simp
  rw [this, show 2 * Real.pi * ((N : ℝ) / 2) = (N : ℝ) * Real.pi by ring, Real.sin_nat_mul_pi]
  simp

theorem archLoopMem {N : ℕ} (hN : 0 < N) (s : ℝ) : (archLz N s, (0 : ℝ)) ∈ archSet := by
  by_cases hs : Real.sin (Real.pi * s) = 0
  · left; rw [archLz_of_sin_eq_zero hs]; rfl
  · right
    rw [archLz_eq hs, inv_inv]
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    refine ⟨arch_re_inv_pos (by rw [arch_re_ofReal_add_mul_I]; positivity), ?_⟩
    exact (archH_half_nat N _).symm

/-- The loop `Re(1/z) = N/2` of the archipelago at its base point (height `0`). -/
def archLoop (N : ℕ) (hN : 0 < N) : Path archO archO where
  toFun s := ⟨(archLz N s, 0), archLoopMem hN s⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.prodMk ?_ continuous_const) _
    unfold archLz
    exact Continuous.div (by fun_prop) (by fun_prop) fun s => archLz_den_ne hN s
  source' := Subtype.ext (by
    show (archLz N 0, (0 : ℝ)) = 0
    rw [archLz_of_sin_eq_zero (by simp)]; rfl)
  target' := Subtype.ext (by
    show (archLz N 1, (0 : ℝ)) = 0
    rw [archLz_of_sin_eq_zero (by simp)]; rfl)

theorem dist_archLoop_le {N : ℕ} (hN : 0 < N) (s : I) :
    dist (archLoop N hN s) archO ≤ 2 / N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [dist_archO]
  show max ‖archLz N s‖ |(0 : ℝ)| ≤ 2 / N
  rw [abs_zero]
  refine max_le ?_ (by positivity)
  by_cases hs : Real.sin (Real.pi * s) = 0
  · rw [archLz_of_sin_eq_zero hs, norm_zero]; positivity
  · rw [archLz_eq hs, norm_inv]
    have hre : 0 < (((N / 2 : ℝ) : ℂ) +
        ((Real.cos (Real.pi * s) / (4 * Real.sin (Real.pi * s)) : ℝ) : ℂ) * Complex.I).re := by
      rw [arch_re_ofReal_add_mul_I]; positivity
    refine (arch_norm_inv_le_re hre).trans (le_of_eq ?_)
    rw [arch_re_ofReal_add_mul_I]; field_simp

/-! The map to `ℂ ∖ {0}` detecting the loops, continuous off the summit `archPt c`. -/

/-- `ζ = max(0, c - Re w) - i Im w`. -/
def archZeta (c : ℝ) (w : ℂ) : ℂ := ((max 0 (c - w.re) : ℝ) : ℂ) - (w.im : ℂ) * Complex.I

/-- `ζ² / |ζ|²` (`-1` where `ζ = 0`). -/
def archFc (c : ℝ) (w : ℂ) : ℂ :=
  if archZeta c w = 0 then -1 else archZeta c w ^ 2 / (Complex.normSq (archZeta c w) : ℂ)

/-- The detecting map `𝔸 → ℂ ∖ {0}`: `-1` at the base point. -/
def archF (c : ℝ) (p : 𝔸) : ℂ := if (p : ℂ × ℝ).1 = 0 then -1 else archFc c (archW p)

theorem archZeta_re (c : ℝ) (w : ℂ) : (archZeta c w).re = max 0 (c - w.re) := by simp [archZeta]

theorem archZeta_im (c : ℝ) (w : ℂ) : (archZeta c w).im = -w.im := by simp [archZeta]

theorem continuous_archZeta (c : ℝ) : Continuous (archZeta c) := by
  unfold archZeta; fun_prop

theorem archFc_ne_zero (c : ℝ) (w : ℂ) : archFc c w ≠ 0 := by
  unfold archFc
  split_ifs with h
  · norm_num
  · exact div_ne_zero (pow_ne_zero 2 h) (by exact_mod_cast (Complex.normSq_pos.2 h).ne')

theorem archF_ne_zero (c : ℝ) (p : 𝔸) : archF c p ≠ 0 := by
  unfold archF; split_ifs
  · norm_num
  · exact archFc_ne_zero c _

theorem normSq_archZeta (c : ℝ) (w : ℂ) :
    (Complex.normSq (archZeta c w) : ℂ) = ((max 0 (c - w.re) : ℝ) : ℂ) ^ 2 + (w.im : ℂ) ^ 2 := by
  rw [Complex.normSq_apply, archZeta_re, archZeta_im]; push_cast; ring

/-- `ζ²/|ζ|² + 1 = 2 max(0, c - Re w) ζ / |ζ|²`. -/
theorem archFc_add_one (c : ℝ) {w : ℂ} (h : archZeta c w ≠ 0) :
    archFc c w + 1 = 2 * ((max 0 (c - w.re) : ℝ) : ℂ) * archZeta c w /
      (Complex.normSq (archZeta c w) : ℂ) := by
  have hn : (Complex.normSq (archZeta c w) : ℂ) ≠ 0 := by
    exact_mod_cast (Complex.normSq_pos.2 h).ne'
  rw [archFc, if_neg h, div_add_one hn]
  congr 1
  rw [normSq_archZeta]
  unfold archZeta
  ring_nf
  rw [Complex.I_sq]
  ring

theorem norm_archFc_add_one_le {c : ℝ} (hc : 0 ≤ c) {w : ℂ} (hw : 0 ≤ w.re) (hv : w.im ≠ 0) :
    ‖archFc c w + 1‖ ≤ 2 * c / |w.im| := by
  have hζ : archZeta c w ≠ 0 := fun h => hv (by
    have := congrArg Complex.im h; rw [archZeta_im] at this; simpa using this)
  rw [archFc_add_one c hζ]
  have hnz : 0 < ‖archZeta c w‖ := norm_pos_iff.2 hζ
  have hnsq : (Complex.normSq (archZeta c w) : ℂ) = ((‖archZeta c w‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.normSq_eq_norm_sq]
  have hΛ0 : 0 ≤ max 0 (c - w.re) := le_max_left _ _
  have hΛ : max 0 (c - w.re) ≤ c := max_le hc (by linarith)
  have hvz : |w.im| ≤ ‖archZeta c w‖ := by
    have := Complex.abs_im_le_norm (archZeta c w)
    rwa [archZeta_im, abs_neg] at this
  rw [hnsq, norm_div, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg hΛ0, abs_of_nonneg (by positivity), Complex.norm_two]
  rw [show 2 * max 0 (c - w.re) * ‖archZeta c w‖ / ‖archZeta c w‖ ^ 2 =
    2 * max 0 (c - w.re) / ‖archZeta c w‖ by field_simp]
  exact div_le_div₀ (by positivity) (by linarith) (abs_pos.2 hv) hvz

theorem archFc_of_le {c : ℝ} {w : ℂ} (h : c ≤ w.re) : archFc c w = -1 := by
  unfold archFc
  split_ifs with hζ
  · rfl
  · have hz : archZeta c w = -((w.im : ℂ) * Complex.I) := by
      simp [archZeta, max_eq_left (sub_nonpos.2 h)]
    have hv : (w.im : ℂ) ≠ 0 := fun hv => hζ (by rw [hz, hv]; simp)
    rw [normSq_archZeta, max_eq_left (sub_nonpos.2 h), hz]
    push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring

theorem continuousAt_archFc {c : ℝ} {w : ℂ} (hw : w ≠ (c : ℂ)) : ContinuousAt (archFc c) w := by
  by_cases hζ : archZeta c w = 0
  · have him : w.im = 0 := by
      have := congrArg Complex.im hζ; rw [archZeta_im] at this; simpa using this
    have hre : c ≤ w.re := by
      have := congrArg Complex.re hζ; rw [archZeta_re] at this
      simp at this; linarith
    have hlt : c < w.re := lt_of_le_of_ne hre fun h => hw (Complex.ext (by simp [h]) (by simp [him]))
    have hev : archFc c =ᶠ[𝓝 w] fun _ => -1 := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hlt] with u hu
      exact archFc_of_le (le_of_lt hu)
    exact continuousAt_const.congr hev.symm
  · have hev : archFc c =ᶠ[𝓝 w] fun u => archZeta c u ^ 2 / (Complex.normSq (archZeta c u) : ℂ) := by
      filter_upwards [isOpen_ne_fun (continuous_archZeta c) continuous_const |>.mem_nhds hζ]
        with u hu
      simp only [archFc, if_neg (show archZeta c u ≠ 0 from hu)]
    refine ContinuousAt.congr ?_ hev.symm
    have hcz := (continuous_archZeta c).continuousAt (x := w)
    refine (hcz.pow 2).div (Complex.continuous_ofReal.continuousAt.comp
      (Complex.continuous_normSq.continuousAt.comp hcz)) ?_
    exact_mod_cast (Complex.normSq_pos.2 hζ).ne'

/-- `archF c` is continuous off the summit `archPt c`. -/
theorem continuousOn_archF {c : ℝ} (hc : 0 < c) :
    ContinuousOn (archF c) {archPt (c : ℂ) (by simpa using hc)}ᶜ := by
  intro p hp
  refine ContinuousAt.continuousWithinAt ?_
  by_cases h0 : (p : ℂ × ℝ).1 = 0
  · have := (arch_fst_eq_zero_iff p).1 h0
    subst this
    rw [ContinuousAt, show archF c archO = -1 by simp [archF, archO], Metric.tendsto_nhds]
    intro ε hε
    set δ : ℝ := 1 / (c + 2 * c / ε + 1)
    have hδ : 0 < δ := by positivity
    filter_upwards [Metric.ball_mem_nhds archO hδ] with q hq
    by_cases hq0 : (q : ℂ × ℝ).1 = 0
    · simp [archF, hq0, hε]
    simp only [archF, if_neg hq0]
    have hw := re_archW_pos hq0
    set w := archW q
    have hd : dist q archO < δ := hq
    rw [← archPt_archW hw, dist_archPt] at hd
    have hn := (max_lt_iff.1 hd).1
    have hw0 : 0 < ‖w‖ := norm_pos_iff.2 (arch_ne_zero_of_re_pos hw)
    have hwR : c + 2 * c / ε + 1 < ‖w‖ := by
      rw [inv_lt_comm₀ hw0 hδ] at hn
      simpa [δ] using hn
    rw [dist_eq_norm, sub_neg_eq_add]
    by_cases hcw : c ≤ w.re
    · rw [archFc_of_le hcw]; simpa using hε
    rw [not_le] at hcw
    have him : 2 * c / ε + 1 < |w.im| := by
      have := Complex.norm_le_abs_re_add_abs_im w
      rw [abs_of_pos hw] at this; linarith
    have hv : w.im ≠ 0 := fun h => by rw [h, abs_zero] at him; linarith [show 0 ≤ 2 * c / ε by positivity]
    refine (norm_archFc_add_one_le hc.le hw.le hv).trans_lt ?_
    rw [div_lt_iff₀ (abs_pos.2 hv)]
    have := (div_lt_iff₀ hε).1 (show 2 * c / ε < |w.im| by linarith)
    linarith
  · have hW : ContinuousAt archW p :=
      (continuous_fst.comp continuous_subtype_val).continuousAt.inv₀ h0
    have hev : archF c =ᶠ[𝓝 p] fun q => archFc c (archW q) := by
      have : IsOpen {q : 𝔸 | (q : ℂ × ℝ).1 ≠ 0} :=
        isOpen_ne_fun (continuous_fst.comp continuous_subtype_val) continuous_const
      filter_upwards [this.mem_nhds h0] with q hq
      simp only [archF, if_neg (show (q : ℂ × ℝ).1 ≠ 0 from hq)]
    refine ContinuousAt.congr ?_ hev.symm
    have hne : archW p ≠ (c : ℂ) := by
      intro h
      apply hp
      show p = _
      rw [← archPt_archW (re_archW_pos h0)]
      congr 1
    exact ContinuousAt.comp (x := p) (f := archW) (continuousAt_archFc hne) hW

/-! The lift of the detected loop through `exp`. -/

/-- `ξ(s) = a sin(πs) - (i/4) cos(πs)` (`= sin(πs) · ζ` along the loop). -/
def archXi (a s : ℝ) : ℂ :=
  ((a * Real.sin (Real.pi * s) : ℝ) : ℂ) + ((-(Real.cos (Real.pi * s) / 4) : ℝ) : ℂ) * Complex.I

theorem arch_sin_pi_nonneg (s : I) : 0 ≤ Real.sin (Real.pi * s) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg Real.pi_pos.le s.2.1)
    (by nlinarith [s.2.2, Real.pi_pos])

theorem arch_cos_ne_zero_of_sin_eq_zero {x : ℝ} (h : Real.sin x = 0) : Real.cos x ≠ 0 := by
  intro hc
  have := Real.sin_sq_add_cos_sq x
  rw [h, hc] at this; norm_num at this

theorem archXi_mem_slitPlane {a : ℝ} (ha : 0 < a) (s : I) : archXi a s ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  unfold archXi
  rw [arch_re_ofReal_add_mul_I, arch_im_ofReal_add_mul_I]
  rcases eq_or_lt_of_le (arch_sin_pi_nonneg s) with h | h
  · right
    have := arch_cos_ne_zero_of_sin_eq_zero h.symm
    intro h'; apply this; linarith
  · left; positivity

theorem continuous_archXi (a : ℝ) : Continuous (archXi a) := by unfold archXi; fun_prop

theorem arch_exp_two_arg_mul_I {ξ : ℂ} (h : ξ ≠ 0) :
    Complex.exp (2 * Complex.arg ξ * Complex.I) = ξ ^ 2 / (Complex.normSq ξ : ℂ) := by
  have hn : (‖ξ‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.2 h).ne'
  have h1 : Complex.exp (Complex.arg ξ * Complex.I) = ξ / ‖ξ‖ := by
    rw [eq_div_iff hn, mul_comm]; exact Complex.norm_mul_exp_arg_mul_I ξ
  rw [show 2 * Complex.arg ξ * Complex.I = Complex.arg ξ * Complex.I + Complex.arg ξ * Complex.I by
    ring, Complex.exp_add, h1, Complex.normSq_eq_norm_sq]
  push_cast
  field_simp

theorem archXi_ne_zero {a : ℝ} (ha : 0 < a) (s : I) : archXi a s ≠ 0 :=
  Complex.slitPlane_ne_zero (archXi_mem_slitPlane ha s)

theorem arch_sq_div_normSq_ofReal_mul_I {b : ℝ} (hb : b ≠ 0) :
    ((b : ℂ) * Complex.I) ^ 2 / (Complex.normSq ((b : ℂ) * Complex.I) : ℂ) = -1 := by
  rw [Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_I, mul_pow, Complex.I_sq]
  have : (b : ℂ) ≠ 0 := by exact_mod_cast hb
  push_cast
  field_simp

theorem arch_sq_div_normSq_ofReal_mul {S : ℝ} (hS : S ≠ 0) (ζ : ℂ) :
    ((S : ℂ) * ζ) ^ 2 / (Complex.normSq ((S : ℂ) * ζ) : ℂ) = ζ ^ 2 / (Complex.normSq ζ : ℂ) := by
  rw [Complex.normSq_mul, Complex.normSq_ofReal, mul_pow]
  have : (S : ℂ) ≠ 0 := by exact_mod_cast hS
  push_cast
  rw [show (S : ℂ) * (S : ℂ) = (S : ℂ) ^ 2 by ring]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 this)

theorem archXi_eq_aux (a S C : ℝ) (hS : S ≠ 0) :
    ((a * S : ℝ) : ℂ) + ((-(C / 4) : ℝ) : ℂ) * Complex.I =
      (S : ℂ) * ((a : ℂ) + ((-(C / (4 * S)) : ℝ) : ℂ) * Complex.I) := by
  have : (S : ℂ) ≠ 0 := by exact_mod_cast hS
  push_cast
  field_simp

/-- Along the loop `Re w = N/2`, the detecting map is `ξ²/|ξ|²`. -/
theorem archF_archLoop {c : ℝ} {N : ℕ} (hN : 0 < N) (hcN : (N : ℝ) / 2 < c) (s : I) :
    archF c (archLoop N hN s) = archXi (c - N / 2) s ^ 2 /
      (Complex.normSq (archXi (c - N / 2) s) : ℂ) := by
  set a := c - (N : ℝ) / 2
  have ha : 0 < a := by simp only [a]; linarith
  have hfst : ((archLoop N hN s : 𝔸) : ℂ × ℝ).1 = archLz N s := rfl
  by_cases hs : Real.sin (Real.pi * s) = 0
  · have h0 : ((archLoop N hN s : 𝔸) : ℂ × ℝ).1 = 0 := by rw [hfst, archLz_of_sin_eq_zero hs]
    rw [archF, if_pos h0]
    have hcos := Real.sin_sq_add_cos_sq (Real.pi * s)
    rw [hs] at hcos
    have hx : archXi a s = ((-(Real.cos (Real.pi * s) / 4) : ℝ) : ℂ) * Complex.I := by
      simp [archXi, hs]
    rw [hx, arch_sq_div_normSq_ofReal_mul_I]
    have := arch_cos_ne_zero_of_sin_eq_zero hs
    intro h'; apply this; linarith
  · have h0 : ((archLoop N hN s : 𝔸) : ℂ × ℝ).1 ≠ 0 := by
      rw [hfst, archLz_eq hs]
      exact inv_ne_zero (arch_ofReal_add_mul_I_ne (Or.inl (by
        have : (0 : ℝ) < N := by exact_mod_cast hN
        positivity)))
    rw [archF, if_neg h0]
    have hW : archW (archLoop N hN s) = (((N / 2 : ℝ) : ℂ) +
        ((Real.cos (Real.pi * s) / (4 * Real.sin (Real.pi * s)) : ℝ) : ℂ) * Complex.I) := by
      rw [archW, hfst, archLz_eq hs, inv_inv]
    rw [hW]
    set v : ℝ := Real.cos (Real.pi * s) / (4 * Real.sin (Real.pi * s))
    have hz : archZeta c (((N / 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) =
        (a : ℂ) + ((-v : ℝ) : ℂ) * Complex.I := by
      unfold archZeta
      rw [arch_re_ofReal_add_mul_I, arch_im_ofReal_add_mul_I, max_eq_right ha.le]
      push_cast; ring
    have hζ : (a : ℂ) + ((-v : ℝ) : ℂ) * Complex.I ≠ 0 := arch_ofReal_add_mul_I_ne (Or.inl ha.ne')
    have hξ : archXi a s = (Real.sin (Real.pi * s) : ℂ) * ((a : ℂ) + ((-v : ℝ) : ℂ) * Complex.I) :=
      archXi_eq_aux a _ _ hs
    rw [archFc, hz, if_neg hζ, hξ, arch_sq_div_normSq_ofReal_mul hs]

/-- **The small loops of the archipelago are not null-homotopic**: `archLoop N` is not homotopic
(rel ends) to the constant loop. A null-homotopy has compact image, which misses the summit
`archPt c` of a far enough hill (`c = M/2 + 1/4`); off that summit `archF c` is a continuous map to
`ℂ ∖ {0}`, along which the loop has winding number `1`. -/
theorem archLoop_not_homotopic {N : ℕ} (hN : 0 < N) :
    ¬ (archLoop N hN).Homotopic (Path.refl archO) := by
  rintro ⟨H⟩
  obtain ⟨r, hr, hK⟩ := arch_compact_bound (isCompact_range H.continuous)
    (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨M, hM⟩ := exists_nat_gt (max (N : ℝ) (2 * r⁻¹))
  set c : ℝ := M / 2 + 1 / 4
  have hc : 0 < c := by positivity
  have hcN : (N : ℝ) / 2 < c := by
    have := le_max_left (N : ℝ) (2 * r⁻¹); simp only [c]; linarith
  have hcr : c⁻¹ < r := by
    rw [inv_lt_comm₀ hc hr]
    have := le_max_right (N : ℝ) (2 * r⁻¹); simp only [c]; linarith
  have hcre : 0 < (c : ℂ).re := by simpa using hc
  set P : 𝔸 := archPt (c : ℂ) hcre
  have hPh : (P : ℂ × ℝ).2 = 1 := by
    show archH (c : ℂ) = 1
    unfold archH
    simp only [Complex.ofReal_re, Complex.ofReal_im]
    rw [show 2 * Real.pi * c = (M : ℝ) * Real.pi + Real.pi / 2 by simp only [c]; ring,
      Real.sin_add_pi_div_two, Real.cos_nat_mul_pi]
    simp [← pow_mul, pow_mul']
  have hPn : ‖(P : ℂ × ℝ).1‖ = c⁻¹ := by
    show ‖(c : ℂ)⁻¹‖ = c⁻¹
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  have hHP : ∀ x, H x ∈ ({P}ᶜ : Set 𝔸) := fun x hx => by
    rw [mem_singleton_iff] at hx
    have := hK (H x) (mem_range_self x) (by rw [hx, hPh]; norm_num)
    rw [hx, hPn] at this
    linarith
  have hcont : Continuous fun x => archF c (H x) :=
    (continuousOn_archF hc).comp_continuous H.continuous hHP
  let m1 : CStar := ⟨-1, by norm_num⟩
  have hbase : archF c archO = -1 := by simp [archF, archO]
  let δ : Path m1 m1 :=
    { toFun := fun s => ⟨archF c (archLoop N hN s), archF_ne_zero _ _⟩
      continuous_toFun := by
        refine Continuous.subtype_mk ?_ _
        have : Continuous fun s : I => archF c (H (0, s)) := hcont.comp (Continuous.prodMk_right 0)
        refine this.congr fun s => ?_
        rw [H.apply_zero]; rfl
      source' := Subtype.ext (by simp [hbase, m1])
      target' := Subtype.ext (by simp [hbase, m1]) }
  let G : Path.Homotopy δ (Path.refl m1) :=
    { toFun := fun x => ⟨archF c (H x), archF_ne_zero _ _⟩
      continuous_toFun := hcont.subtype_mk _
      map_zero_left := fun s => Subtype.ext (by simp [δ, H.apply_zero])
      map_one_left := fun s => Subtype.ext (by simp [H.apply_one, hbase, m1])
      prop' := fun t s hs => by
        rcases hs with rfl | rfl
        · exact Subtype.ext (by simp [δ, hbase])
        · exact Subtype.ext (by simp [δ, hbase]) }
  have h1 := cWinding_homotopic ⟨G⟩
  set a : ℝ := c - N / 2
  have ha : 0 < a := by simp only [a]; linarith
  let Γ : C(I, ℂ) := ⟨fun s => 2 * Complex.arg (archXi a s) * Complex.I, by
    refine continuous_iff_continuousAt.2 fun s => ?_
    have h := ((Complex.continuousAt_arg (archXi_mem_slitPlane ha s)).comp
      (continuous_archXi a).continuousAt).comp (x := s) continuous_subtype_val.continuousAt
    exact (continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.comp h)).mul
      continuousAt_const⟩
  have hΓ : ∀ s, Complex.exp (Γ s) = δ s := fun s => by
    show Complex.exp (2 * Complex.arg (archXi a s) * Complex.I) = archF c (archLoop N hN s)
    rw [arch_exp_two_arg_mul_I (archXi_ne_zero ha s), archF_archLoop hN hcN s]
  have hδ1 : cWinding δ = 1 := by
    refine cWinding_eq δ hΓ ?_
    show 2 * Complex.arg (archXi a 1) * Complex.I =
      2 * Complex.arg (archXi a 0) * Complex.I + ((1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I)
    have e0 : archXi a 0 = ((1 / 4 : ℝ) : ℂ) * (-Complex.I) := by simp [archXi]
    have e1 : archXi a 1 = ((1 / 4 : ℝ) : ℂ) * Complex.I := by simp [archXi]; ring
    rw [e0, e1, Complex.arg_real_mul _ (by norm_num), Complex.arg_real_mul _ (by norm_num),
      Complex.arg_I, Complex.arg_neg_I]
    push_cast; ring
  have hr0 : cWinding (Path.refl m1) = 0 := by
    refine cWinding_eq _ (Γ := ContinuousMap.const I (Complex.log (-1))) (fun _ => ?_) (by simp)
    simp [m1, Complex.exp_log (show (-1 : ℂ) ≠ 0 by norm_num)]
  rw [hδ1, hr0] at h1
  exact one_ne_zero h1

/-- **The harmonic archipelago is not semi-locally simply connected** (at its base point): every
neighbourhood of it contains a loop `archLoop N` which is not null-homotopic. -/
theorem harmonicArchipelago_not_semilocallySimplyConnected : ¬ SemilocallySimplyConnected 𝔸 := by
  intro h
  obtain ⟨U, hU, hloop⟩ := h archO
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / ε)
  have hN0 : 0 < N := by
    have : (0 : ℝ) < N := lt_trans (by positivity) hN
    exact_mod_cast this
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN0
  refine archLoop_not_homotopic hN0 (hloop _ fun t => hεU ?_)
  refine lt_of_le_of_lt (dist_archLoop_le hN0 t) ?_
  rw [div_lt_iff₀ hN']
  rw [div_lt_iff₀ hε] at hN
  linarith

end Loop


/-! #### The counterexample -/

/-- **`rem:definition_semi_locally_simply_connected`, the converse is false**: the harmonic
archipelago `𝔸 ⊆ ℂ × ℝ = ℝ³` is Hausdorff, path-connected, locally path-connected (and metrizable)
and semi-locally simply connected in itself in the literal sense of
`def:semi_locally_simple_connectedness` (DEC-55), but it is not semi-locally simply connected. -/
theorem harmonicArchipelago_counterexample :
    T2Space 𝔸 ∧ PathConnectedSpace 𝔸 ∧ LocPathConnectedSpace 𝔸 ∧
      IsSLSCInCC (univ : Set 𝔸) ∧ ¬ SemilocallySimplyConnected 𝔸 :=
  ⟨inferInstance, inferInstance, inferInstance, harmonicArchipelago_isSLSCInCC,
    harmonicArchipelago_not_semilocallySimplyConnected⟩

/-- `rem:definition_semi_locally_simply_connected` as printed ("`X` is semi-locally simply
connected iff it is semi-locally simply connected in itself", `X` Hausdorff, connected, locally
path-connected) is false: the direction "slsc in itself ⇒ slsc" fails (the harmonic
archipelago). -/
theorem not_semilocallySimplyConnected_of_isSLSCInCC_univ :
    ¬ ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [LocPathConnectedSpace X],
      IsSLSCInCC (univ : Set X) → SemilocallySimplyConnected X :=
  fun h => harmonicArchipelago_not_semilocallySimplyConnected
    (h 𝔸 harmonicArchipelago_isSLSCInCC)

/-- `theo:Galois_cor` (DEC-70): its added hypothesis "`Y ∖ S` semi-locally simply connected" is
not implied by "`Y ∖ S` semi-locally simply connected in `Y`": `Y` the harmonic archipelago
(connected, locally path-connected, Hausdorff, first countable) and `S = ∅` (skeletal). -/
theorem harmonicArchipelago_compl_empty :
    IsSkeletal (∅ : Set 𝔸) ∧ IsSLSCInCC ((∅ : Set 𝔸)ᶜ) ∧ IsSLSCIn ((∅ : Set 𝔸)ᶜ) ∧
      ¬ SemilocallySimplyConnected ((∅ : Set 𝔸)ᶜ : Set 𝔸) := by
  refine ⟨isSkeletal_empty, by rw [compl_empty]; exact harmonicArchipelago_isSLSCInCC,
    by rw [compl_empty]; exact harmonicArchipelago_isSLSCIn, fun h => ?_⟩
  exact harmonicArchipelago_not_semilocallySimplyConnected
    (h.of_homeomorph ((Homeomorph.setCongr compl_empty).trans (Homeomorph.Set.univ 𝔸)))

end Archipelago

/-! ### The maximal covering possibly branched over `S` -/

section MaxCover

variable {Y : Type u} [TopologicalSpace Y] [T2Space Y] [LocPathConnectedSpace Y]
  [FirstCountableTopology Y] [ConnectedSpace Y] {S : Set Y}

/-- The instances of `\widetilde Y^S`. -/
theorem maxBranched_instances (hS : IsSkeletal S) (hSc : SemilocallySimplyConnected (Sᶜ : Set Y))
    (y₀ : (Sᶜ : Set Y)) :
    LocPathConnectedSpace (MaxBranchedCover S y₀) ∧ FirstCountableTopology (MaxBranchedCover S y₀) ∧
      T2Space (MaxBranchedCover S y₀) :=
  ⟨(maxBranched_basic hS hSc y₀).2.2.2.2.1, inferInstance, inferInstance⟩

/-- A deck transformation of `\widetilde{Y∖S}` extends to one of `\widetilde Y^S`. -/
theorem maxBranched_deck_of_universalCover (y₀ : (Sᶜ : Set Y))
    (θ : UniversalCover (Sᶜ : Set Y) y₀ ≃ₜ UniversalCover (Sᶜ : Set Y) y₀)
    (hθ : ∀ c, univCoverProj S y₀ (θ c) = univCoverProj S y₀ c) :
    ∃ Φ ∈ deckGroup (SpreadEnd.base : MaxBranchedCover S y₀ → Y),
      ∀ c, Φ (SpreadEnd.ofPoint _ c) = SpreadEnd.ofPoint _ (θ c) := by
  have hc : ∀ c, univCoverProj S y₀ (θ c) = id (univCoverProj S y₀ c) := hθ
  have hc' : ∀ c, univCoverProj S y₀ (θ.symm c) = id (univCoverProj S y₀ c) := fun c => by
    have := hθ (θ.symm c)
    rw [θ.apply_symm_apply] at this
    exact this.symm
  set M := SpreadEnd.map continuous_id θ.continuous hc
  set M' := SpreadEnd.map continuous_id θ.symm.continuous hc'
  have hM'M : M' ∘ M = id := by
    refine SpreadEnd.denseRange_ofPoint.equalizer
      ((SpreadEnd.continuous_map _ _ _).comp (SpreadEnd.continuous_map _ _ _)) continuous_id
      (funext fun c => ?_)
    simp only [comp_apply, id, M, M', SpreadEnd.map_ofPoint, Homeomorph.symm_apply_apply]
  have hMM' : M ∘ M' = id := by
    refine SpreadEnd.denseRange_ofPoint.equalizer
      ((SpreadEnd.continuous_map _ _ _).comp (SpreadEnd.continuous_map _ _ _)) continuous_id
      (funext fun c => ?_)
    simp only [comp_apply, id, M, M', SpreadEnd.map_ofPoint, Homeomorph.apply_symm_apply]
  let Φ : MaxBranchedCover S y₀ ≃ₜ MaxBranchedCover S y₀ :=
    { toFun := M
      invFun := M'
      left_inv := congrFun hM'M
      right_inv := congrFun hMM'
      continuous_toFun := SpreadEnd.continuous_map _ _ _
      continuous_invFun := SpreadEnd.continuous_map _ _ _ }
  exact ⟨Φ, funext fun e => SpreadEnd.base_map continuous_id θ.continuous hc e,
    fun c => SpreadEnd.map_ofPoint continuous_id θ.continuous hc c⟩

/-- `\widetilde{Y∖S}` is Galoisian: its deck group acts transitively on the fibres. -/
theorem universalCover_exists_leftMul {Z : Type u} [TopologicalSpace Z] {z₀ : Z}
    (c c' : UniversalCover Z z₀) (h : c.pt = c'.pt) :
    ∃ g : Path.Homotopic.Quotient z₀ z₀, UniversalCover.leftMul g c = c' := by
  obtain ⟨w, a⟩ := c
  obtain ⟨w', b⟩ := c'
  simp only at h
  subst h
  refine ⟨b.trans a.symm, ?_⟩
  simp only [UniversalCover.leftMul, Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.trans_refl]

/-- Over `Y ∖ S`, `Γ(\widetilde Y^S / Y)` acts transitively on the fibres. -/
theorem maxBranched_transitive (hS : IsSkeletal S) (hSc : SemilocallySimplyConnected (Sᶜ : Set Y))
    (y₀ : (Sᶜ : Set Y)) (e e' : MaxBranchedCover S y₀) (h : e.base = e'.base) (he : e.base ∈ Sᶜ) :
    ∃ φ ∈ deckGroup (SpreadEnd.base : MaxBranchedCover S y₀ → Y), φ e = e' := by
  obtain ⟨-, -, -, hpre, -, -⟩ := maxBranched_basic hS hSc y₀
  have he' : e'.base ∈ Sᶜ := h ▸ he
  obtain ⟨c, rfl⟩ : e ∈ range (SpreadEnd.ofPoint (univCoverProj S y₀)) := by
    rw [← hpre]; exact he
  obtain ⟨c', rfl⟩ : e' ∈ range (SpreadEnd.ofPoint (univCoverProj S y₀)) := by
    rw [← hpre]; exact he'
  have hpt : c.pt = c'.pt := Subtype.ext h
  obtain ⟨g, hg⟩ := universalCover_exists_leftMul c c' hpt
  obtain ⟨Φ, hΦ, hΦc⟩ := maxBranched_deck_of_universalCover y₀
    (UniversalCover.leftMulHomeomorph g) (fun _ => rfl)
  exact ⟨Φ, hΦ, (hΦc c).trans (congrArg _ hg)⟩

/-- `\widetilde Y^S` is quasi-Galoisian (the completion of the Galoisian `\widetilde{Y∖S}`). -/
theorem maxBranched_isQuasiGaloisian (hS : IsSkeletal S)
    (hSc : SemilocallySimplyConnected (Sᶜ : Set Y)) (y₀ : (Sᶜ : Set Y)) :
    IsQuasiGaloisian (SpreadEnd.base : MaxBranchedCover S y₀ → Y) := by
  obtain ⟨hbc, hpb⟩ := maxBranched_isBranchedCovering hS hSc y₀
  have hOp : (Sᶜ : Set Y) ⊆ ordY (SpreadEnd.base : MaxBranchedCover S y₀ → Y) := fun y hy => by
    by_contra h
    exact hy (hpb h)
  exact isQuasiGaloisian_iff.2 ⟨hbc, Sᶜ, isSkeletal_iff.1 hS, hOp,
    fun e e' h he => maxBranched_transitive hS hSc y₀ e e' h he⟩

/-- `Γ(\widetilde Y^S / Y)` is countable when `Y` is second countable (it injects in the fibre over
`y₀`, which is `π₁(Y ∖ S, y₀)`). -/
theorem countable_deck_maxBranched [SecondCountableTopology Y] (hS : IsSkeletal S)
    (hSc : SemilocallySimplyConnected (Sᶜ : Set Y)) (y₀ : (Sᶜ : Set Y)) :
    ((deckGroup (SpreadEnd.base : MaxBranchedCover S y₀ → Y) :
      Set (MaxBranchedCover S y₀ ≃ₜ MaxBranchedCover S y₀))).Countable := by
  obtain ⟨-, hbc, hpb, hpre, -, hsp⟩ := maxBranched_basic hS hSc y₀
  haveI : LocPathConnectedSpace (Sᶜ : Set Y) := (isSkeletal_iff.1 hS).isOpen.locPathConnectedSpace
  haveI := UniversalCover.countable_fundamentalGroup hSc y₀
  haveI : Countable (Path.Homotopic.Quotient y₀ y₀) :=
    Function.Injective.countable (f := FundamentalGroup.fromPath (X := (Sᶜ : Set Y)) (x := y₀))
      fun _ _ h => h
  set e₀ : MaxBranchedCover S y₀ := SpreadEnd.ofPoint _ (UniversalCover.base y₀)
  have he₀ : e₀.base = y₀ := rfl
  have hOp : (Sᶜ : Set Y) ⊆ ordY (SpreadEnd.base : MaxBranchedCover S y₀ → Y) := fun y hy => by
    by_contra h
    exact hy (hpb h)
  -- the fibre over `y₀` is countable
  have hfib : ((SpreadEnd.base : MaxBranchedCover S y₀ → Y) ⁻¹' {(y₀ : Y)}).Countable := by
    let F : {c : UniversalCover (Sᶜ : Set Y) y₀ // c.pt = y₀} → Path.Homotopic.Quotient y₀ y₀ :=
      fun c => c.1.cls.cast rfl c.2.symm
    have hF : Injective F := by
      rintro ⟨⟨w, a⟩, ha⟩ ⟨⟨w', b⟩, hb⟩ hab
      simp only at ha hb
      subst ha; subst hb
      have : a = b := by
        have h1 := Path.Homotopic.Quotient.cast_heq (γ := a) rfl rfl
        have h2 := Path.Homotopic.Quotient.cast_heq (γ := b) rfl rfl
        exact eq_of_heq (h1.symm.trans ((heq_of_eq hab).trans h2))
      subst this; rfl
    haveI : Countable {c : UniversalCover (Sᶜ : Set Y) y₀ // c.pt = y₀} := hF.countable
    refine ((countable_range fun c : {c : UniversalCover (Sᶜ : Set Y) y₀ // c.pt = y₀} =>
      SpreadEnd.ofPoint (univCoverProj S y₀) c.1)).mono fun e he => ?_
    have heS : e ∈ (SpreadEnd.base : MaxBranchedCover S y₀ → Y) ⁻¹' Sᶜ := by
      show e.base ∈ Sᶜ
      rw [show e.base = y₀ from he]; exact y₀.2
    rw [hpre] at heS
    obtain ⟨c, rfl⟩ := heS
    exact ⟨⟨c, Subtype.ext he⟩, rfl⟩
  refine MapsTo.countable_of_injOn (f := fun φ => φ e₀) (t := _ ⁻¹' {(y₀ : Y)}) ?_ ?_ hfib
  · intro φ hφ
    show (φ e₀).base = y₀
    rw [deck_apply _ hφ]; exact he₀
  · intro φ hφ ψ hψ h
    exact deck_eq_of_apply_eq hbc hφ hψ (hOp (by rw [he₀]; exact y₀.2)) h

/-- `prop:Galoisian_semilocal`, (ii) ⇒ (i), without second countability: if `Y ∖ S` is
semi-locally simply connected in `Y`, then `\widetilde Y^S` is Galoisian. -/
theorem maxBranched_isGaloisian (hS : IsSkeletal S) (hSc : SemilocallySimplyConnected (Sᶜ : Set Y))
    (y₀ : (Sᶜ : Set Y)) (h : IsSLSCIn (Sᶜ : Set Y)) :
    IsGaloisian (SpreadEnd.base : MaxBranchedCover S y₀ → Y) := by
  obtain ⟨hl, -, -⟩ := maxBranched_instances hS hSc y₀
  haveI := hl
  obtain ⟨hbc, hpb⟩ := maxBranched_isBranchedCovering hS hSc y₀
  have hq := maxBranched_isQuasiGaloisian hS hSc y₀
  refine ⟨hbc, fun e e' hee => ?_⟩
  haveI := discreteTopology_fiber_of_isSLSCAt hbc hS hpb (h.2 e.base)
  exact exists_eq_of_discreteTopology_fiber le_rfl ‹_›
    (fun x x' hxx N hN => hq.exists_mem_nhds hxx hN) rfl hee.symm

/-- The fibres of a Galoisian `\widetilde Y^S` are discrete (second countable `Y`). -/
theorem discreteTopology_fiber_maxBranched [SecondCountableTopology Y] (hS : IsSkeletal S)
    (hSc : SemilocallySimplyConnected (Sᶜ : Set Y)) (y₀ : (Sᶜ : Set Y))
    (h : IsGaloisian (SpreadEnd.base : MaxBranchedCover S y₀ → Y)) (y : Y) :
    DiscreteTopology ((SpreadEnd.base : MaxBranchedCover S y₀ → Y) ⁻¹' {y}) := by
  have hq := maxBranched_isQuasiGaloisian hS hSc y₀
  have := alternative_countable hq (countable_deck_maxBranched hS hSc y₀) y
  exact this.1.2 (this.2.2 fun x _ x' hx' => h.2 x x' (by rw [show _ = y from hx'] ; assumption))

/-- `prop:Galoisian_semilocal` (`RamcovGX.tex:1514`), HOMOTOPY form of "almost trivial" (the
literal statement, DEC-55, is `GX.galoisian_semilocal_cc`). Let `Y` be connected, locally
path-connected, second countable, Hausdorff, `S ⊆ Y` skeletal with `Y ∖ S` semi-locally simply
connected. Then `\widetilde Y^S → Y` is Galoisian iff `Y ∖ S` is semi-locally simply connected
in `Y`. -/
theorem galoisian_semilocal [SecondCountableTopology Y] (hS : IsSkeletal S)
    (hSc : SemilocallySimplyConnected (Sᶜ : Set Y)) (y₀ : (Sᶜ : Set Y)) :
    IsGaloisian (SpreadEnd.base : MaxBranchedCover S y₀ → Y) ↔ IsSLSCIn (Sᶜ : Set Y) := by
  refine ⟨fun h => ⟨(isSkeletal_iff.1 hS).dense, fun y => ?_⟩, maxBranched_isGaloisian hS hSc y₀⟩
  obtain ⟨hl, -, -⟩ := maxBranched_instances hS hSc y₀
  haveI := hl
  obtain ⟨-, hsc⟩ := maxBranched_lifting hS hSc y₀
  haveI := hsc
  obtain ⟨hbc, hpb⟩ := maxBranched_isBranchedCovering hS hSc y₀
  exact isSLSCAt_of_discreteTopology_fiber hbc hS hpb
    (discreteTopology_fiber_maxBranched hS hSc y₀ h y)

/-- `prop:Galoisian_semilocal`, (ii) ⇒ (i), literal form (DEC-55), without second
countability. -/
theorem maxBranched_isGaloisian_cc (hS : IsSkeletal S)
    (hSc : SemilocallySimplyConnected (Sᶜ : Set Y)) (y₀ : (Sᶜ : Set Y))
    (h : IsSLSCInCC (Sᶜ : Set Y)) : IsGaloisian (SpreadEnd.base : MaxBranchedCover S y₀ → Y) :=
  maxBranched_isGaloisian hS hSc y₀ ((isSLSCInCC_iff (isSkeletal_iff.1 hS).isOpen hSc).1 h)

/-- **`prop:Galoisian_semilocal`** (`RamcovGX.tex:1514`), literal reading of "almost trivial"
(DEC-55). Let `Y` be connected, locally path-connected, second countable, Hausdorff, `S ⊆ Y`
skeletal with `Y ∖ S` semi-locally simply connected. Then `\widetilde Y^S → Y` is Galoisian iff
`Y ∖ S` is semi-locally simply connected in `Y` (`GX.IsSLSCInCC`). Under the proposition's own
hypotheses the literal and the homotopy forms agree (`GX.isSLSCInCC_iff`), which is how the
paper's homotopy arguments apply. -/
theorem galoisian_semilocal_cc [SecondCountableTopology Y] (hS : IsSkeletal S)
    (hSc : SemilocallySimplyConnected (Sᶜ : Set Y)) (y₀ : (Sᶜ : Set Y)) :
    IsGaloisian (SpreadEnd.base : MaxBranchedCover S y₀ → Y) ↔ IsSLSCInCC (Sᶜ : Set Y) := by
  rw [isSLSCInCC_iff (isSkeletal_iff.1 hS).isOpen hSc]
  exact galoisian_semilocal hS hSc y₀

/-! ### `theo:Galois_cor` -/

/-- The fibres of `\widetilde Y^S` are discrete when `Y ∖ S` is semi-locally simply connected in
`Y` (no countability). -/
theorem discreteTopology_fiber_maxBranched_of_isSLSCIn (hS : IsSkeletal S)
    (hSc : SemilocallySimplyConnected (Sᶜ : Set Y)) (y₀ : (Sᶜ : Set Y)) (h : IsSLSCIn (Sᶜ : Set Y))
    (y : Y) : DiscreteTopology ((SpreadEnd.base : MaxBranchedCover S y₀ → Y) ⁻¹' {y}) := by
  obtain ⟨hl, -, -⟩ := maxBranched_instances hS hSc y₀
  haveI := hl
  obtain ⟨hbc, hpb⟩ := maxBranched_isBranchedCovering hS hSc y₀
  exact discreteTopology_fiber_of_isSLSCAt hbc hS hpb (h.2 y)

/-- `theo:Galois_cor`, second assertion (`RamcovGX.tex:1555`). If `Y ∖ S` is semi-locally
simply connected in `Y`, every covering `p : X → Y` possibly branched over `S` (Hausdorff, locally
path-connected, first countable) is isomorphic over `Y` to the quotient of `\widetilde Y^S` by a
subgroup `H` of `Γ(\widetilde Y^S / Y)`; `H` is the group of automorphisms of the universal map
`\widetilde Y^S → X`. -/
theorem galois_cor_quotient (hS : IsSkeletal S) (hSc : SemilocallySimplyConnected (Sᶜ : Set Y))
    (y₀ : (Sᶜ : Set Y)) (h : IsSLSCIn (Sᶜ : Set Y)) {X : Type*} [TopologicalSpace X] [T2Space X]
    [LocPathConnectedSpace X] [FirstCountableTopology X] {p : X → Y} (hp : IsBranchedCovering p)
    (hpS : IsPossiblyBranchedOver p S) :
    ∃ H : Subgroup (MaxBranchedCover S y₀ ≃ₜ MaxBranchedCover S y₀),
      H ≤ deckGroup (SpreadEnd.base : MaxBranchedCover S y₀ → Y) ∧
        ∃ hX : HomeoQuotient H ≃ₜ X, ∀ e, p (hX (homeoQuotientMk H e)) = e.base := by
  obtain ⟨hl, -, -⟩ := maxBranched_instances hS hSc y₀
  haveI := hl
  obtain ⟨hbc, -⟩ := maxBranched_isBranchedCovering hS hSc y₀
  obtain ⟨Φ, hΦc, hΦp, hΦbc, -⟩ := maxBranched_universal hS hSc y₀ hp hpS
  have hO : IsPortly (Sᶜ : Set Y) := isSkeletal_iff.1 hS
  have hOp : (Sᶜ : Set Y) ⊆ ordY p := fun y hy => by
    by_contra h'
    exact hy (hpS h')
  have hH : deckGroup Φ ≤ deckGroup (SpreadEnd.base : MaxBranchedCover S y₀ → Y) :=
    fun φ hφ => funext fun e => by
      show (φ e).base = e.base
      rw [← hΦp, ← hΦp e, deck_apply Φ hφ]
  -- transitivity of `deckGroup Φ` over the dense `p⁻¹(Y ∖ S)`
  have htr : ∀ z z', Φ z = Φ z' → Φ z ∈ p ⁻¹' Sᶜ → ∃ g ∈ deckGroup Φ, g z = z' := by
    intro z z' hzz hz
    have hb : z.base = z'.base := by rw [← hΦp, ← hΦp z', hzz]
    have hzS : z.base ∈ Sᶜ := by rw [← hΦp]; exact hz
    obtain ⟨φ, hφ, hφz⟩ := maxBranched_transitive hS hSc y₀ z z' hb hzS
    refine ⟨φ, ?_, hφz⟩
    have := eq_of_comp_eq_of_mem_portly hbc hp hO hOp (hΦc.comp φ.continuous) hΦc
      (fun e => by simp only [comp_apply, hΦp, deck_apply _ hφ]) hΦp hzS
      (by simp only [comp_apply, hφz, hzz])
    exact this
  have hD : Dense (p ⁻¹' Sᶜ) := (hp.isPortly_preimage hS).dense
  have hdense : ∀ z z', Φ z = Φ z' → ∀ N ∈ 𝓝 z', ∃ g ∈ deckGroup Φ, g z ∈ N :=
    fun z z' hzz N hN => exists_mem_nhds_of_transitive hΦbc le_rfl hD htr hzz hN
  have hfib : ∀ z z', Φ z = Φ z' ↔ ∃ φ ∈ deckGroup Φ, φ z = z' := by
    intro z z'
    refine ⟨fun hzz => ?_, fun ⟨φ, hφ, h'⟩ => by rw [← h', deck_apply Φ hφ]⟩
    have hdisc : DiscreteTopology (Φ ⁻¹' {Φ z'}) := by
      haveI := discreteTopology_fiber_maxBranched_of_isSLSCIn hS hSc y₀ h (p (Φ z'))
      have hsub : Φ ⁻¹' {Φ z'} ⊆ (SpreadEnd.base : MaxBranchedCover S y₀ → Y) ⁻¹' {p (Φ z')} :=
        fun w hw => by
          show w.base = p (Φ z')
          rw [← hΦp, show Φ w = Φ z' from hw]
      exact (Topology.IsEmbedding.inclusion hsub).discreteTopology
    exact exists_eq_of_discreteTopology_fiber le_rfl hdisc hdense hzz rfl
  exact ⟨deckGroup Φ, hH, exists_homeomorph_homeoQuotient hΦc (spread_connected_image hΦbc).1
    hΦbc.surjective hfib |>.imp fun hX hX' e => by rw [hX', hΦp]⟩

/-- `theo:Galois_cor`, third assertion (`RamcovGX.tex:1557`). If `Y ∖ S` is semi-locally
simply connected in `Y` and `X ≃ H\widetilde Y^S` over `Y` for a subgroup `H ≤ Γ(\widetilde Y^S/Y)`,
then `H` is normal in `Γ(\widetilde Y^S/Y)` iff `X → Y` is Galoisian. -/
theorem galois_cor_normal (hS : IsSkeletal S) (hSc : SemilocallySimplyConnected (Sᶜ : Set Y))
    (y₀ : (Sᶜ : Set Y)) (h : IsSLSCIn (Sᶜ : Set Y)) {X : Type*} [TopologicalSpace X] [T2Space X]
    {p : X → Y} (hp : IsBranchedCovering p) (hpS : IsPossiblyBranchedOver p S)
    {H : Subgroup (MaxBranchedCover S y₀ ≃ₜ MaxBranchedCover S y₀)}
    (hH : H ≤ deckGroup (SpreadEnd.base : MaxBranchedCover S y₀ → Y))
    (hX : HomeoQuotient H ≃ₜ X) (hXp : ∀ e, p (hX (homeoQuotientMk H e)) = e.base) :
    (H.subgroupOf (deckGroup (SpreadEnd.base : MaxBranchedCover S y₀ → Y))).Normal ↔
      IsGaloisian p := by
  set Γ := deckGroup (SpreadEnd.base : MaxBranchedCover S y₀ → Y)
  obtain ⟨hbc, hpb⟩ := maxBranched_isBranchedCovering hS hSc y₀
  have hGal := maxBranched_isGaloisian hS hSc y₀ h
  have hO : IsPortly (Sᶜ : Set Y) := isSkeletal_iff.1 hS
  have hOp : (Sᶜ : Set Y) ⊆ ordY p := fun y hy => by
    by_contra h'
    exact hy (hpS h')
  have hOb : (Sᶜ : Set Y) ⊆ ordY (SpreadEnd.base : MaxBranchedCover S y₀ → Y) := fun y hy => by
    by_contra h'
    exact hy (hpb h')
  set Φ : MaxBranchedCover S y₀ → X := fun e => hX (homeoQuotientMk H e)
  have hΦc : Continuous Φ := hX.continuous.comp continuous_quotient_mk'
  have hΦp : ∀ e, p (Φ e) = e.base := hXp
  have hΦ : ∀ e e', Φ e = Φ e' ↔ ∃ η ∈ H, η e = e' := fun e e' =>
    ⟨fun he => Quotient.exact (hX.injective he), fun he => congrArg hX (Quotient.sound he)⟩
  have hΦη : ∀ η ∈ H, ∀ e, Φ (η e) = Φ e := fun η hη e => ((hΦ e (η e)).2 ⟨η, hη, rfl⟩).symm
  set e₀ : MaxBranchedCover S y₀ := SpreadEnd.ofPoint _ (UniversalCover.base y₀)
  have he₀ : e₀.base ∈ Sᶜ := y₀.2
  -- an automorphism of `\widetilde Y^S` over `X` lies in `H`
  have hA : ∀ φ ∈ Γ, (∀ e, Φ (φ e) = Φ e) → φ ∈ H := by
    intro φ hφ hφΦ
    obtain ⟨η, hη, hηe⟩ := (hΦ e₀ (φ e₀)).1 (hφΦ e₀).symm
    rw [deck_eq_of_apply_eq hbc hφ (hH hη) (hOb he₀) hηe.symm]
    exact hη
  constructor
  · -- `H` normal ⇒ `X` Galoisian
    intro hN
    refine ⟨hp, fun x x' hxx => ?_⟩
    have hconj : ∀ φ ∈ Γ, ∀ η ∈ H, φ * η * φ⁻¹ ∈ H := by
      intro φ hφ η hη
      have := hN.conj_mem ⟨η, hH hη⟩ (Subgroup.mem_subgroupOf.2 hη) ⟨φ, hφ⟩
      exact Subgroup.mem_subgroupOf.1 this
    obtain ⟨qx, rfl⟩ := hX.surjective x
    obtain ⟨qx', rfl⟩ := hX.surjective x'
    induction qx using Quotient.inductionOn with | h e => ?_
    induction qx' using Quotient.inductionOn with | h e' => ?_
    have hb : e.base = e'.base := by rw [← hΦp, ← hΦp e']; exact hxx
    obtain ⟨φ, hφ, hφe⟩ := hGal.2 e e' hb
    have hcompat : ∀ (θ : MaxBranchedCover S y₀ ≃ₜ MaxBranchedCover S y₀), θ ∈ Γ →
        ∀ a b, (subgroupOrbitSetoid H) a b → (subgroupOrbitSetoid H) (θ a) (θ b) := by
      rintro θ hθ a b ⟨η, hη, rfl⟩
      refine ⟨θ * η * θ⁻¹, hconj θ hθ η hη, ?_⟩
      simp only [Homeomorph.mul_apply, Homeomorph.inv_apply, Homeomorph.symm_apply_apply]
    let φi : MaxBranchedCover S y₀ ≃ₜ MaxBranchedCover S y₀ := φ⁻¹
    let Q : HomeoQuotient H ≃ₜ HomeoQuotient H :=
      { toFun := Quotient.map' φ (hcompat φ hφ)
        invFun := Quotient.map' φi (hcompat φi (inv_mem hφ))
        left_inv := fun q => by
          induction q using Quotient.inductionOn with | h a => ?_
          show homeoQuotientMk H (φi (φ a)) = homeoQuotientMk H a
          rw [Homeomorph.inv_apply, Homeomorph.symm_apply_apply]
        right_inv := fun q => by
          induction q using Quotient.inductionOn with | h a => ?_
          show homeoQuotientMk H (φ (φi a)) = homeoQuotientMk H a
          rw [Homeomorph.inv_apply, Homeomorph.apply_symm_apply]
        continuous_toFun := φ.continuous.quotient_map' _
        continuous_invFun := φi.continuous.quotient_map' _ }
    have hQ : ∀ a, Q (homeoQuotientMk H a) = homeoQuotientMk H (φ a) := fun _ => rfl
    let ψ : X ≃ₜ X := hX.symm.trans (Q.trans hX)
    refine ⟨ψ, funext fun z => ?_, ?_⟩
    · obtain ⟨qz, rfl⟩ := hX.surjective z
      induction qz using Quotient.inductionOn with | h a => ?_
      show p (hX (Q (hX.symm (hX (homeoQuotientMk H a))))) = p (hX (homeoQuotientMk H a))
      rw [Homeomorph.symm_apply_apply, hQ, hXp, hXp, deck_apply _ hφ]
    · show hX (Q (hX.symm (hX (homeoQuotientMk H e)))) = hX (homeoQuotientMk H e')
      rw [Homeomorph.symm_apply_apply, hQ, hφe]
  · -- `X` Galoisian ⇒ `H` normal
    intro hXG
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨η, hηΓ⟩ := n
    obtain ⟨φ, hφ⟩ := g
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv] at hn ⊢
    obtain ⟨ψ, hψ, hψe⟩ := hXG.2 (Φ e₀) (Φ (φ e₀)) (by rw [hΦp, hΦp, deck_apply _ hφ])
    have hψΦ : (fun e => ψ (Φ e)) = fun e => Φ (φ e) :=
      eq_of_comp_eq_of_mem_portly hbc hp hO hOp (ψ.continuous.comp hΦc) (hΦc.comp φ.continuous)
        (fun e => by simp only [deck_apply p hψ, hΦp]) (fun e => by rw [hΦp, deck_apply _ hφ])
        he₀ hψe
    refine hA _ (mul_mem (mul_mem hφ hηΓ) (inv_mem hφ)) fun e => ?_
    simp only [Homeomorph.mul_apply, Homeomorph.inv_apply]
    have h1 := congrFun hψΦ (η (φ.symm e))
    have h2 := congrFun hψΦ (φ.symm e)
    simp only [Homeomorph.apply_symm_apply] at h1 h2
    rw [← h1, hΦη η hn, h2]

/-- `theo:Galois_cor` (`RamcovGX.tex:1550`), the Galois correspondence, HOMOTOPY form of "almost
trivial" (the literal statement, DEC-55, is `GX.galois_correspondence_cc`). Let `Y` be connected,
locally path-connected, Hausdorff (first countable, §3 standing), `S ⊆ Y` skeletal, `Y ∖ S`
semi-locally simply connected (so that `\widetilde Y^S` exists) and semi-locally simply connected
in `Y`. Then `\widetilde Y^S` is Galoisian; every covering `X` of `Y` possibly branched over `S`
is isomorphic over `Y` to `H\widetilde Y^S` for a subgroup `H ≤ Γ(\widetilde Y^S/Y)`; and for any
such `H`, `H` is normal iff `X` is Galoisian. -/
theorem galois_correspondence (hS : IsSkeletal S) (hSc : SemilocallySimplyConnected (Sᶜ : Set Y))
    (y₀ : (Sᶜ : Set Y)) (h : IsSLSCIn (Sᶜ : Set Y)) :
    IsGaloisian (SpreadEnd.base : MaxBranchedCover S y₀ → Y) ∧
      (∀ (X : Type v) [TopologicalSpace X] [T2Space X] [LocPathConnectedSpace X]
        [FirstCountableTopology X] (p : X → Y), IsBranchedCovering p →
        IsPossiblyBranchedOver p S →
        ∃ H : Subgroup (MaxBranchedCover S y₀ ≃ₜ MaxBranchedCover S y₀),
          H ≤ deckGroup (SpreadEnd.base : MaxBranchedCover S y₀ → Y) ∧
            ∃ hX : HomeoQuotient H ≃ₜ X, ∀ e, p (hX (homeoQuotientMk H e)) = e.base) ∧
      (∀ (X : Type v) [TopologicalSpace X] [T2Space X] (p : X → Y), IsBranchedCovering p →
        IsPossiblyBranchedOver p S →
        ∀ H : Subgroup (MaxBranchedCover S y₀ ≃ₜ MaxBranchedCover S y₀),
          H ≤ deckGroup (SpreadEnd.base : MaxBranchedCover S y₀ → Y) →
          ∀ hX : HomeoQuotient H ≃ₜ X, (∀ e, p (hX (homeoQuotientMk H e)) = e.base) →
            ((H.subgroupOf (deckGroup (SpreadEnd.base : MaxBranchedCover S y₀ → Y))).Normal ↔
              IsGaloisian p)) :=
  ⟨maxBranched_isGaloisian hS hSc y₀ h,
    fun _ _ _ _ _ _ hp hpS => galois_cor_quotient hS hSc y₀ h hp hpS,
    fun _ _ _ _ hp hpS _ hH hX hXp => galois_cor_normal hS hSc y₀ h hp hpS hH hX hXp⟩

/-- **`theo:Galois_cor`** (`RamcovGX.tex:1550`) in the literal reading of "almost trivial"
(DEC-55): the hypothesis "`Y ∖ S` semi-locally simply connected in `Y`" is `GX.IsSLSCInCC`.
`Y ∖ S` semi-locally simply connected is CARRIED by the author's ruling DEC-70 (the hypothesis of
`prop:universality`, under which alone the maximal covering exists; its omission from the printed
statement is recorded, and it is not implied by slsc in `Y`: `GX.harmonicArchipelago_compl_empty`);
under it the literal and homotopy forms agree (`GX.isSLSCInCC_iff`). -/
theorem galois_correspondence_cc (hS : IsSkeletal S)
    (hSc : SemilocallySimplyConnected (Sᶜ : Set Y)) (y₀ : (Sᶜ : Set Y))
    (h : IsSLSCInCC (Sᶜ : Set Y)) :
    IsGaloisian (SpreadEnd.base : MaxBranchedCover S y₀ → Y) ∧
      (∀ (X : Type v) [TopologicalSpace X] [T2Space X] [LocPathConnectedSpace X]
        [FirstCountableTopology X] (p : X → Y), IsBranchedCovering p →
        IsPossiblyBranchedOver p S →
        ∃ H : Subgroup (MaxBranchedCover S y₀ ≃ₜ MaxBranchedCover S y₀),
          H ≤ deckGroup (SpreadEnd.base : MaxBranchedCover S y₀ → Y) ∧
            ∃ hX : HomeoQuotient H ≃ₜ X, ∀ e, p (hX (homeoQuotientMk H e)) = e.base) ∧
      (∀ (X : Type v) [TopologicalSpace X] [T2Space X] (p : X → Y), IsBranchedCovering p →
        IsPossiblyBranchedOver p S →
        ∀ H : Subgroup (MaxBranchedCover S y₀ ≃ₜ MaxBranchedCover S y₀),
          H ≤ deckGroup (SpreadEnd.base : MaxBranchedCover S y₀ → Y) →
          ∀ hX : HomeoQuotient H ≃ₜ X, (∀ e, p (hX (homeoQuotientMk H e)) = e.base) →
            ((H.subgroupOf (deckGroup (SpreadEnd.base : MaxBranchedCover S y₀ → Y))).Normal ↔
              IsGaloisian p)) :=
  galois_correspondence hS hSc y₀ ((isSLSCInCC_iff (isSkeletal_iff.1 hS).isOpen hSc).1 h)

end MaxCover

end GX
