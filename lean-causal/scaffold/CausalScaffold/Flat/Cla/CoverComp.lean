import CausalScaffold.Flat.Nonloxodromic
import CausalScaffold.Flat.TitsNull
import CausalScaffold.Flat.Loxodromic
import CausalScaffold.CompactCauchy
import CausalScaffold.CurvesExtend

/-!
# `CausalScaffold.Flat.Cla.CoverComp` — a finite cover of a finite cover is a finite cover

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), Theorem B
(`bthm:cauclo`, l.353–359) and its proof (l.3536–3548, l.3573–3581). No label is certified here:
this module proves the one general-topology step that `Flat/Classification.lean`'s
`cauclo_from_embedding` lists as its step (5), "the composition of finite covers"
(`docs/BARBOT-THEOREMS.md` §6, G9). Line numbers are those of the **labelled**
`papers/barbot/legacy/labeled/GHFspace.tex`.

> Up to finite coverings,
> every maximal Cauchy-compact globally hyperbolic flat spacetime is isometric
> to a translation spacetime, a Misner spacetime, or
> the twisted product of a standart spacetime (Cauchy-compact
> Cauchy-hyperbolic GH spacetime) by an euclidean torus. (l.355–359)

> As observed previously, unipotent spacetimes cannot
> be Cauchy-compact; thus, together with their finite coverings, they
> disappear in the Cauchy-compact version. (l.3546–3548)

> some finite covering $M'$ of $M$ tamely embeds in some
> model spacetime $M_{1}$. Hence, some finite covering $M'_{0}$
> of $M_{0}$ embeds isometrically in $M_{1}$. (l.3589–3591)

The paper composes finite coverings silently ("up to finite coverings" absorbs a finite cover of
a finite cover); this module is that step.

## What is proved

* `Causal.Flat.IsFiniteCover.comp` — if `q : Y → Z` and `p : X → Y` are finite covers
  (`IsFiniteCover d`: a covering map, a local isometry, finite fibres), so is `q ∘ p`. Sorry-free.
  - covering: `Causal.isCoveringMap_comp_of_finite` (`Port/UniversalCover.lean`, sorry-free,
    reached transitively through `Flat.Developing`): over an evenly covered `U ∋ z` for `q` with
    its finitely many sheets `Vᵢ ∋ yᵢ`, and evenly covered `Wᵢ ∋ yᵢ` for `p`, the open set
    `U ∩ ⋂ᵢ q (Vᵢ ∩ Wᵢ)` is evenly covered by `q ∘ p` — the finite intersection is where the
    finiteness of `q`'s fibres is used;
  - local isometry: `IsLocalIsometry.comp` (`Flat/FlatSpacetime.lean`);
  - finite fibres: `(q ∘ p)⁻¹{z} = p⁻¹(q⁻¹{z})`, a finite union of finite fibres
    (`Set.Finite.preimage'`).

## Hypothesis checklist

| paper | here |
|---|---|
| finite covering (undefined; a covering map of flat spacetimes with finite fibres) | ✓ carried as `IsFiniteCover d` (BARBOT-THEOREMS' definition: `IsCoveringMap`, local isometry, finite fibres; surjectivity not asked) |
| spaces are flat spacetimes (Hausdorff, connected, `(Isom 𝐌ⁿ, 𝐌ⁿ)`-structure) | ⚠ weakened: only `TopologicalSpace` + `ChartedSpace (Minkowski d)` on `X`, `Y`, `Z`; no `T2`, connectedness or `HasGroupoid` asked |

## SCOPE (disclosed)

* Finiteness of the fibres of the **second** map `q` is used for the covering property (and
  the finiteness of both for the fibres of `q ∘ p`). Without it a composite of coverings need
  not be a covering (Hawaiian-earring-type bases; recorded in `Port/UniversalCover.lean`, not
  proved); flat spacetimes are locally path-connected and semilocally simply connected, where
  `isCoveringMap_comp_of_semilocallySimplyConnected` would also apply, but that is not needed.
* Surjectivity is not part of `IsFiniteCover`, so none is claimed or needed.
* The other steps (1)–(4) of `cauclo_from_embedding` are untouched.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
Classification step (5) of `cauclo_from_embedding` (`Flat/Classification.lean:2447`).
-/

namespace Causal.Flat.Cla

open Set

variable {d : ℕ}

/-- **The composite of two finite covers is a finite cover** (`cauclo_from_embedding`, step (5):
the "up to finite coverings" of Theorem B, l.355, absorbs a finite covering of a finite covering,
l.3589–3591). Covering by `Causal.isCoveringMap_comp_of_finite` (the finite fibres of `q` make the
shrunk evenly covered neighbourhood a finite intersection of open sets), local isometry by
`IsLocalIsometry.comp`, finite fibres since `(q ∘ p)⁻¹{z} = p⁻¹(q⁻¹{z})`. -/
theorem IsFiniteCover.comp {X Y Z : Type*} [TopologicalSpace X] [ChartedSpace (Minkowski d) X]
    [TopologicalSpace Y] [ChartedSpace (Minkowski d) Y] [TopologicalSpace Z]
    [ChartedSpace (Minkowski d) Z] {p : X → Y} {q : Y → Z} (hq : IsFiniteCover d q)
    (hp : IsFiniteCover d p) : IsFiniteCover d (q ∘ p) := by
  obtain ⟨hqc, hql, hqf⟩ := hq
  obtain ⟨hpc, hpl, hpf⟩ := hp
  refine ⟨Causal.isCoveringMap_comp_of_finite hqc hpc hqf, hql.comp hpl, fun z => ?_⟩
  rw [preimage_comp]
  exact (hqf z).preimage' fun y _ => hpf y

end Causal.Flat.Cla
