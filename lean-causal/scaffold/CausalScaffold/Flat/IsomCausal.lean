import CausalScaffold.Flat.Form
import Causal.GXStructure
import Causal.CauchyExtension

/-!
# `CausalScaffold.Flat.IsomCausal` — isometries of `𝐌ⁿ` are causal automorphisms, and every flat spacetime carries its causality

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §2.2–2.3,
`GHFspace.tex` l.471–492. No ledger label is certified: both subsections are prose, without an
environment. This module is the bridge "flat spacetime = `(Isom(𝐌ⁿ), 𝐌ⁿ)`-manifold" into the ETT
framework, i.e. `prop:GX_espace_temps_topo` of ETT (`Causal/GXStructure.lean`) for `X = 𝐌ⁿ`.

> We denote by $\mbox{Isom}({\bf M}^{n})$ the group of isometries of \mink. (l.481–482)

> Truely speaking, every spacetimes considered in this work are flat, i.e., locally modeled on
> the Minkowski space. In other words, in the language of geometric structures (see e.g.
> \cite{gold}), they are $(G,X)$-manifolds with $X = {\bf M}^{n}$ and $G = \mbox{Isom}(M^{n})$.
> (l.485–490)

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; the library's `Minkowski d =
ℝ × EuclideanSpace ℝ (Fin d)` has `d` spatial dimensions, so Barbot's `n` is `d + 1`.

* `isomImage g U` — the image of an open set by an isometry, as an open set, with its simp
  lemmas; it is an `abbrev` for `smulOpens g U` of `Causal/GXStructure.lean` (open because
  `isom.toHomeomorph g` is a homeomorphism), so one name survives graduation.
* `le_iff_le_isomImage`, `lt_iff_lt_isomImage` (and `isom_le_iff`, `isom_lt_iff`, the other
  direction) — **for every open `U`**, `p ≤_U q ↔ g p ≤_{g U} g q`, and the same for `≪`.
  `Jplus_isomImage`, `Jminus_isomImage`, `Iplus_isomImage`, `Iminus_isomImage` — the same for the
  causal and chronological futures and pasts of sets.
* `isom_strongMorphism` — every `g • ·` is a strong morphism of `minkowski d` (the hypothesis `hG`
  of `existsUnique_causality_GX_maximal`), `isom_localIsomorphism`, `isom_isEMorphism`,
  `isom_weakMorphism`.
* `flat_existsUnique_causality` — an `(Isom(𝐌ⁿ), 𝐌ⁿ)`-manifold carries an absolutely minimal
  causality making every chart of its maximal atlas an isomorphism onto `minkowski d`, and it is
  the only absolutely minimal one. `flatCausality d M` is that causality, with
  `flatCausality_chartIso`, `flatCausality_absolutelyMinimal`, `eq_flatCausality`;
  `flatCausality_self` is the non-vacuity witness (`𝐌ⁿ` itself gets back `minkowski d`);
  `eq_flatCausality_of_covering_chart` — with a chart of the maximal atlas defined on all of `M`,
  uniqueness holds outright, without absolute minimality.
* General, not about Minkowski space (namespace `Causal.Causality`): `imp_of_agree_on_basis`,
  `eq_of_agree_on_basis` — two causalities absolutely minimal on every open set and agreeing on
  the members of a basis are equal.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| isometries: affine, linear part in `SO₀(1,n−1)` | ✓ carried: `isom d` of `Form` |
| flat spacetime: a `(G,X)`-manifold, `X = 𝐌ⁿ`, `G = Isom(𝐌ⁿ)` | ✓ carried (DEC-16): `ChartedSpace (Minkowski d) M`, `HasGroupoid M (gxGroupoid (isom d) (Minkowski d))`, the maximal atlas |
| `M` Hausdorff, second countable, connected | ⚠ weakened: not used |
| the causal structure of a flat spacetime | the paper takes it from the Lorentzian metric; here it is ETT's, produced by `prop:GX_espace_temps_topo` — a modelling choice, not compared with the metric one on a general `M` (see SCOPE) |

## SCOPE (disclosed)

* The paper never states that isometries preserve the causal relations of open subsets; it is the
  implicit content of "locally modeled on the Minkowski space" (l.486). The proof here does not
  push curves through a boost: on a **convex** open set both relations are the cones
  (`le_iff_of_convex`), an isometry maps convex sets to convex sets and preserves the cones, so the
  causality transported along `g` agrees with `minkowski d` on every convex open set; both are
  absolutely minimal on every open set, and convex balls form a basis, so they are equal
  (`isomTransport_eq`).
* Uniqueness of `flatCausality` is among **absolutely minimal** causalities, as in
  `existsUnique_causality_GX_maximal` (ETT's SCOPE (d) there: without gluing it is false in
  general, `GX_maximal_not_unique`).
  The paper claims no uniqueness (l.484–492): this is extra content, not a strengthened paper
  hypothesis. With a covering chart it holds outright (`eq_flatCausality_of_covering_chart`).
* The metric-defined causality of a general flat Lorentzian manifold is **not** compared with
  `flatCausality` here. What is proved is local: on a convex open subset of `𝐌ⁿ` (all of `𝐌ⁿ`
  included) `minkowski d` is the future cone (`le_iff_of_convex`, `lt_iff_of_convex`,
  `le_top_iff_minkQ`), and through `flatCausality_chartIso` the relation of `flatCausality` on the
  chart preimage of a convex open set is that cone — the metric's relation on such a set. That
  the metric relation of an arbitrary open subset of `M` is the one these local cones generate is
  not proved here.
* The non-vacuity witness `flatCausality_self` uses `𝐌ⁿ` with its one-chart atlas, where
  uniqueness holds outright (`eq_of_chartIso_of_source_eq_univ`); it does not exercise a
  non-trivial maximal atlas. A quotient example (translation spacetimes, `Γ \ Ω`) is wave 2's.
* `flatCausality` is defined by `Classical.choose`; only its characteristic lemmas should be used.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
WP-30a (wave 1).
-/

namespace Causal

open Set TopologicalSpace

universe u

/-! ### Two absolutely minimal causalities agreeing on a basis are equal -/

namespace Causality

variable {M : Type u} [TopologicalSpace M]

/-- If `C₁` is absolutely minimal on every open set and every relation of `C₁` in a member of a
basis `B` is one of `C₂`, every relation of `C₁` is one of `C₂`: a relation in `V` is a chain of
relations in members of `B` contained in `V`. -/
theorem imp_of_agree_on_basis {C₁ C₂ : Causality M} (B : Set (Opens M))
    (hB : ∀ V : Opens M, ∀ x ∈ V, ∃ O ∈ B, O ≤ V ∧ x ∈ O)
    (h₁ : ∀ V : Opens M, C₁.AbsolutelyMinimalOn V)
    (hagree : ∀ O ∈ B, ∀ x y, (C₁.le O x y → C₂.le O x y) ∧ (C₁.lt O x y → C₂.lt O x y))
    (V : Opens M) (x y : M) : (C₁.le V x y → C₂.le V x y) ∧ (C₁.lt V x y → C₂.lt V x y) := by
  let S : Set (Opens M) := {O | O ∈ B ∧ O ≤ V}
  have hS : ∀ z ∈ V, ∃ O ∈ S, z ∈ O := fun z hz => by
    obtain ⟨O, hO, hOV, hzO⟩ := hB V z hz
    exact ⟨O, ⟨hO, hOV⟩, hzO⟩
  refine ⟨fun hxy => ?_, fun hxy => ?_⟩
  · refine Precausality.le_of_transGen (S := S)
      (Relation.TransGen.mono ?_ ((h₁ V S hS V le_rfl x y).1 hxy))
    rintro a b ⟨O, ⟨hO, hOV⟩, hab⟩
    have hVO : V ⊓ O = O := inf_eq_right.2 hOV
    rw [hVO] at hab
    exact ⟨O, ⟨hO, hOV⟩, by rw [hVO]; exact (hagree O hO a b).1 hab⟩
  · refine Precausality.lt_of_transGen (S := S)
      (Relation.TransGen.mono ?_ ((h₁ V S hS V le_rfl x y).2 hxy))
    rintro a b ⟨O, ⟨hO, hOV⟩, hab⟩
    have hVO : V ⊓ O = O := inf_eq_right.2 hOV
    rw [hVO] at hab
    exact ⟨O, ⟨hO, hOV⟩, by rw [hVO]; exact (hagree O hO a b).2 hab⟩

/-- **Two causalities absolutely minimal on every open set, which agree on every member of a
basis of the topology, are equal.** -/
theorem eq_of_agree_on_basis {C₁ C₂ : Causality M} (B : Set (Opens M))
    (hB : ∀ V : Opens M, ∀ x ∈ V, ∃ O ∈ B, O ≤ V ∧ x ∈ O)
    (h₁ : ∀ V : Opens M, C₁.AbsolutelyMinimalOn V) (h₂ : ∀ V : Opens M, C₂.AbsolutelyMinimalOn V)
    (hagree : ∀ O ∈ B, ∀ x y, (C₁.le O x y ↔ C₂.le O x y) ∧ (C₁.lt O x y ↔ C₂.lt O x y)) :
    C₁ = C₂ := by
  have h12 := imp_of_agree_on_basis B hB h₁
    (fun O hO x y => ⟨(hagree O hO x y).1.1, (hagree O hO x y).2.1⟩)
  have h21 := imp_of_agree_on_basis B hB h₂
    (fun O hO x y => ⟨(hagree O hO x y).1.2, (hagree O hO x y).2.2⟩)
  apply Causality.ext_toPrecausality
  ext V x y
  · exact ⟨(h12 V x y).1, (h21 V x y).1⟩
  · exact ⟨(h12 V x y).2, (h21 V x y).2⟩

end Causality

namespace Flat

variable {d : ℕ}

/-! ### The image of an open set by an isometry -/

/-- The image `g(U)` of an open set by an isometry, as an open set: `smulOpens g U` of
`Causal/GXStructure.lean` (an `abbrev`, so the library's `smul_rel_iff` applies verbatim). It is
open because `g` is the homeomorphism `isom.toHomeomorph g`. -/
noncomputable abbrev isomImage (g : isom d) (U : Opens (Minkowski d)) : Opens (Minkowski d) :=
  smulOpens g U

section isomImage

variable {g h : isom d} {U V : Opens (Minkowski d)} {p q : Minkowski d}

@[simp] theorem coe_isomImage (g : isom d) (U : Opens (Minkowski d)) :
    (isomImage g U : Set (Minkowski d)) = (fun p => g • p) '' U := rfl

@[simp] theorem smul_mem_isomImage : g • p ∈ isomImage g U ↔ p ∈ U :=
  (MulAction.injective g).mem_set_image

theorem mem_isomImage : q ∈ isomImage g U ↔ g⁻¹ • q ∈ U := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    simpa using hp
  · intro hq
    exact ⟨g⁻¹ • q, hq, by simp⟩

/-- `isomImage` is `smulOpens` of `Causal/GXStructure.lean`. -/
theorem isomImage_eq_smulOpens (g : isom d) (U : Opens (Minkowski d)) :
    isomImage g U = smulOpens g U := rfl

@[simp] theorem isomImage_top (g : isom d) : isomImage g ⊤ = ⊤ := by
  apply SetLike.coe_injective
  simp only [coe_isomImage, Opens.coe_top, image_univ]
  exact (MulAction.surjective g).range_eq

@[simp] theorem isomImage_one (U : Opens (Minkowski d)) : isomImage 1 U = U := by
  apply SetLike.coe_injective
  simp

theorem isomImage_mul (g h : isom d) (U : Opens (Minkowski d)) :
    isomImage (g * h) U = isomImage g (isomImage h U) := by
  apply SetLike.coe_injective
  simp only [coe_isomImage, image_image, mul_smul]

theorem isomImage_mono (hUV : U ≤ V) : isomImage g U ≤ isomImage g V :=
  image_mono hUV

theorem isomImage_inf : isomImage g (U ⊓ V) = isomImage g U ⊓ isomImage g V := by
  apply SetLike.coe_injective
  simp only [coe_isomImage, Opens.coe_inf]
  exact image_inter (MulAction.injective g)

theorem isomImage_inv_isomImage : isomImage g⁻¹ (isomImage g U) = U := by
  rw [← isomImage_mul, inv_mul_cancel, isomImage_one]

/-- If `V = g⁻¹(U)`, then `g(V) = U`. -/
theorem isomImage_eq_of_coe_eq_preimage (hV : (V : Set (Minkowski d)) = (fun p => g • p) ⁻¹' U) :
    isomImage g V = U := by
  apply SetLike.coe_injective
  rw [coe_isomImage, hV]
  exact image_preimage_eq _ (MulAction.surjective g)

/-- An isometry maps a convex set to a convex set. -/
theorem convex_isomImage (hU : Convex ℝ (U : Set (Minkowski d))) :
    Convex ℝ (isomImage g U : Set (Minkowski d)) := by
  have := hU.affine_image ((g : Minkowski d ≃ᵃ[ℝ] Minkowski d) : Minkowski d →ᵃ[ℝ] Minkowski d)
  simpa [coe_isomImage, isom_smul_def] using this

end isomImage

/-! ### The causality transported along an isometry -/

/-- An isometry, as a chart of `𝐌ⁿ` defined everywhere. -/
noncomputable def isomChart (g : isom d) : OpenPartialHomeomorph (Minkowski d) (Minkowski d) :=
  (isom.toHomeomorph g).toOpenPartialHomeomorph

@[simp] theorem isomChart_apply (g : isom d) (p : Minkowski d) : isomChart g p = g • p := rfl

@[simp] theorem isomChart_source (g : isom d) : (isomChart g).source = univ := rfl

theorem chartImage_isomChart (g : isom d) (U : Opens (Minkowski d)) :
    chartImage (isomChart g) U = isomImage g U := by
  apply SetLike.coe_injective
  simp only [coe_chartImage, isomChart_source, univ_inter, coe_isomImage]
  rfl

/-- The causality `minkowski d` transported along the isometry `g`: `p ≤_U q` iff
`g p ≤_{g U} g q`. -/
noncomputable def isomTransport (g : isom d) : Causality (Minkowski d) :=
  (minkowski d).chartTransport (isomChart g)

theorem isomTransport_chartIso (g : isom d) :
    ChartIso (isomTransport g) (minkowski d) (isomChart g) :=
  (minkowski d).chartTransport_chartIso _

/-- The transported causality is absolutely minimal on every open set. -/
theorem isomTransport_absolutelyMinimalOn (g : isom d) (W : Opens (Minkowski d)) :
    (isomTransport g).AbsolutelyMinimalOn W :=
  (isomTransport_chartIso g).absolutelyMinimalOn (fun _ _ => trivial)
    (minkowski_causallyArcConnected.absolutelyMinimalOn_all _)

/-- On a convex open set, the transported relation is the future cone. -/
theorem isomTransport_le_iff_of_convex (g : isom d) {O : Opens (Minkowski d)}
    (hO : Convex ℝ (O : Set (Minkowski d))) {p q : Minkowski d} :
    (isomTransport g).le O p q ↔ (minkowski d).le O p q := by
  have hiso := isomTransport_chartIso g
  rw [le_iff_of_convex hO]
  constructor
  · intro h
    have hp := (isomTransport g).le_mem_left h
    have hq := (isomTransport g).le_mem_right h
    have h' := ((hiso O (fun _ _ => trivial) p hp q hq).1).1 h
    rw [chartImage_isomChart, isomChart_apply, isomChart_apply,
      le_iff_of_convex (convex_isomImage hO), isom_le_top_iff] at h'
    exact ⟨hp, hq, h'.2.2⟩
  · rintro ⟨hp, hq, h⟩
    refine ((hiso O (fun _ _ => trivial) p hp q hq).1).2 ?_
    rw [chartImage_isomChart, isomChart_apply, isomChart_apply,
      le_iff_of_convex (convex_isomImage hO), isom_le_top_iff]
    exact ⟨smul_mem_isomImage.2 hp, smul_mem_isomImage.2 hq, h⟩

/-- On a convex open set, the transported chronology is the open future timelike cone. -/
theorem isomTransport_lt_iff_of_convex (g : isom d) {O : Opens (Minkowski d)}
    (hO : Convex ℝ (O : Set (Minkowski d))) {p q : Minkowski d} :
    (isomTransport g).lt O p q ↔ (minkowski d).lt O p q := by
  have hiso := isomTransport_chartIso g
  rw [lt_iff_of_convex hO]
  constructor
  · intro h
    have hp := (isomTransport g).lt_mem_left h
    have hq := (isomTransport g).lt_mem_right h
    have h' := ((hiso O (fun _ _ => trivial) p hp q hq).2).1 h
    rw [chartImage_isomChart, isomChart_apply, isomChart_apply,
      lt_iff_of_convex (convex_isomImage hO), isom_lt_top_iff] at h'
    exact ⟨hp, hq, h'.2.2⟩
  · rintro ⟨hp, hq, h⟩
    refine ((hiso O (fun _ _ => trivial) p hp q hq).2).2 ?_
    rw [chartImage_isomChart, isomChart_apply, isomChart_apply,
      lt_iff_of_convex (convex_isomImage hO), isom_lt_top_iff]
    exact ⟨smul_mem_isomImage.2 hp, smul_mem_isomImage.2 hq, h⟩

/-- Every point of an open set of `𝐌ⁿ` lies in a convex open subset (a ball). -/
theorem exists_convex_opens (V : Opens (Minkowski d)) (x : Minkowski d) (hx : x ∈ V) :
    ∃ O ∈ {O : Opens (Minkowski d) | Convex ℝ (O : Set (Minkowski d))}, O ≤ V ∧ x ∈ O := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 V.isOpen x hx
  exact ⟨⟨Metric.ball x ε, Metric.isOpen_ball⟩, convex_ball x ε, hball, Metric.mem_ball_self hε⟩

/-- **The causality transported along an isometry is the causality of `𝐌ⁿ`.** -/
theorem isomTransport_eq (g : isom d) : isomTransport g = minkowski d :=
  Causality.eq_of_agree_on_basis _ exists_convex_opens (isomTransport_absolutelyMinimalOn g)
    (minkowski_causallyArcConnected.absolutelyMinimalOn_all)
    fun _ hO _ _ => ⟨isomTransport_le_iff_of_convex g hO, isomTransport_lt_iff_of_convex g hO⟩

/-! ### Isometries preserve the relations of every open set -/

/-- The two relations of `U` and of `g(U)` correspond. -/
theorem rel_iff_rel_isomImage (g : isom d) (U : Opens (Minkowski d)) (p q : Minkowski d) :
    ((minkowski d).le U p q ↔ (minkowski d).le (isomImage g U) (g • p) (g • q)) ∧
      ((minkowski d).lt U p q ↔ (minkowski d).lt (isomImage g U) (g • p) (g • q)) := by
  have hiso := isomTransport_chartIso g
  rw [isomTransport_eq] at hiso
  by_cases hp : p ∈ U
  · by_cases hq : q ∈ U
    · have := hiso U (fun _ _ => trivial) p hp q hq
      rwa [chartImage_isomChart, isomChart_apply, isomChart_apply] at this
    · refine ⟨⟨fun h => absurd ((minkowski d).le_mem_right h) hq, fun h => ?_⟩,
        ⟨fun h => absurd ((minkowski d).lt_mem_right h) hq, fun h => ?_⟩⟩
      · exact absurd (smul_mem_isomImage.1 ((minkowski d).le_mem_right h)) hq
      · exact absurd (smul_mem_isomImage.1 ((minkowski d).lt_mem_right h)) hq
  · refine ⟨⟨fun h => absurd ((minkowski d).le_mem_left h) hp, fun h => ?_⟩,
      ⟨fun h => absurd ((minkowski d).lt_mem_left h) hp, fun h => ?_⟩⟩
    · exact absurd (smul_mem_isomImage.1 ((minkowski d).le_mem_left h)) hp
    · exact absurd (smul_mem_isomImage.1 ((minkowski d).lt_mem_left h)) hp

/-- **Isometries preserve `≤` of every open set**: `p ≤_U q ↔ g p ≤_{g U} g q`. -/
theorem le_iff_le_isomImage (g : isom d) (U : Opens (Minkowski d)) (p q : Minkowski d) :
    (minkowski d).le U p q ↔ (minkowski d).le (isomImage g U) (g • p) (g • q) :=
  (rel_iff_rel_isomImage g U p q).1

/-- **Isometries preserve `≪` of every open set**: `p ≪_U q ↔ g p ≪_{g U} g q`. -/
theorem lt_iff_lt_isomImage (g : isom d) (U : Opens (Minkowski d)) (p q : Minkowski d) :
    (minkowski d).lt U p q ↔ (minkowski d).lt (isomImage g U) (g • p) (g • q) :=
  (rel_iff_rel_isomImage g U p q).2

@[simp] theorem isom_le_iff (g : isom d) (U : Opens (Minkowski d)) (p q : Minkowski d) :
    (minkowski d).le (isomImage g U) (g • p) (g • q) ↔ (minkowski d).le U p q :=
  (le_iff_le_isomImage g U p q).symm

@[simp] theorem isom_lt_iff (g : isom d) (U : Opens (Minkowski d)) (p q : Minkowski d) :
    (minkowski d).lt (isomImage g U) (g • p) (g • q) ↔ (minkowski d).lt U p q :=
  (lt_iff_lt_isomImage g U p q).symm

/-- `g(J⁺_U(A)) = J⁺_{g U}(g A)`. -/
theorem Jplus_isomImage (g : isom d) (U : Opens (Minkowski d)) (A : Set (Minkowski d)) :
    (minkowski d).Jplus (isomImage g U) ((fun p => g • p) '' A) =
      (fun p => g • p) '' (minkowski d).Jplus U A := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, hxy⟩
    obtain ⟨z, -, rfl⟩ := ((minkowski d).le_mem_right hxy : y ∈ isomImage g U)
    exact ⟨z, ⟨x, hx, (isom_le_iff g U x z).1 hxy⟩, rfl⟩
  · rintro ⟨z, ⟨x, hx, hxz⟩, rfl⟩
    exact ⟨g • x, ⟨x, hx, rfl⟩, (isom_le_iff g U x z).2 hxz⟩

/-- `g(J⁻_U(A)) = J⁻_{g U}(g A)`. -/
theorem Jminus_isomImage (g : isom d) (U : Opens (Minkowski d)) (A : Set (Minkowski d)) :
    (minkowski d).Jminus (isomImage g U) ((fun p => g • p) '' A) =
      (fun p => g • p) '' (minkowski d).Jminus U A := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, hxy⟩
    obtain ⟨z, -, rfl⟩ := ((minkowski d).le_mem_left hxy : y ∈ isomImage g U)
    exact ⟨z, ⟨x, hx, (isom_le_iff g U z x).1 hxy⟩, rfl⟩
  · rintro ⟨z, ⟨x, hx, hxz⟩, rfl⟩
    exact ⟨g • x, ⟨x, hx, rfl⟩, (isom_le_iff g U z x).2 hxz⟩

/-- `g(I⁺_U(A)) = I⁺_{g U}(g A)`. -/
theorem Iplus_isomImage (g : isom d) (U : Opens (Minkowski d)) (A : Set (Minkowski d)) :
    (minkowski d).Iplus (isomImage g U) ((fun p => g • p) '' A) =
      (fun p => g • p) '' (minkowski d).Iplus U A := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, hxy⟩
    obtain ⟨z, -, rfl⟩ := ((minkowski d).lt_mem_right hxy : y ∈ isomImage g U)
    exact ⟨z, ⟨x, hx, (isom_lt_iff g U x z).1 hxy⟩, rfl⟩
  · rintro ⟨z, ⟨x, hx, hxz⟩, rfl⟩
    exact ⟨g • x, ⟨x, hx, rfl⟩, (isom_lt_iff g U x z).2 hxz⟩

/-- `g(I⁻_U(A)) = I⁻_{g U}(g A)`. -/
theorem Iminus_isomImage (g : isom d) (U : Opens (Minkowski d)) (A : Set (Minkowski d)) :
    (minkowski d).Iminus (isomImage g U) ((fun p => g • p) '' A) =
      (fun p => g • p) '' (minkowski d).Iminus U A := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, hxy⟩
    obtain ⟨z, -, rfl⟩ := ((minkowski d).lt_mem_left hxy : y ∈ isomImage g U)
    exact ⟨z, ⟨x, hx, (isom_lt_iff g U z x).1 hxy⟩, rfl⟩
  · rintro ⟨z, ⟨x, hx, hxz⟩, rfl⟩
    exact ⟨g • x, ⟨x, hx, rfl⟩, (isom_lt_iff g U z x).2 hxz⟩

/-! ### Isometries are morphisms of topological spacetimes -/

/-- **Every isometry is a strong morphism** of `minkowski d` — exactly the hypothesis `hG` of
`existsUnique_causality_GX_maximal` for `G = Isom(𝐌ⁿ)`. -/
theorem isom_strongMorphism (g : isom d) :
    StrongMorphism (minkowski d) (minkowski d) fun p => g • p where
  continuous := (isom.toHomeomorph g).continuous
  isOpenMap := (isom.toHomeomorph g).isOpenMap
  map_le U V hV x y hxy := by
    rw [le_iff_le_isomImage g, isomImage_eq_of_coe_eq_preimage hV] at hxy
    exact hxy
  map_lt U V hV x y hxy := by
    rw [lt_iff_lt_isomImage g, isomImage_eq_of_coe_eq_preimage hV] at hxy
    exact hxy

theorem isom_weakMorphism (g : isom d) :
    WeakMorphism (minkowski d) (minkowski d) fun p => g • p :=
  (isom_strongMorphism g).weakMorphism

/-- Every isometry is a local isomorphism of `minkowski d` (with `V = 𝐌ⁿ` around every point). -/
theorem isom_localIsomorphism (g : isom d) :
    LocalIsomorphism (minkowski d) (minkowski d) fun p => g • p := by
  refine ⟨(isom.toHomeomorph g).isLocalHomeomorph, fun x => ⟨⊤, trivial,
    (MulAction.injective g).injOn, fun V' _ U hU y _ z _ => ?_⟩⟩
  have hU' : U = isomImage g V' := SetLike.coe_injective hU
  subst hU'
  exact rel_iff_rel_isomImage g V' y z

/-- Every isometry is an abstract `𝕄≥0`-morphism of `minkowski d` (`isEMorphism_iff`). -/
theorem isom_isEMorphism (g : isom d) :
    IsEMorphism (minkowski d) (minkowski d) fun p => g • p :=
  isEMorphism_iff.2 ⟨isom_strongMorphism g, isom_localIsomorphism g⟩

/-! ### Flat spacetimes -/

section FlatSpacetime

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (Minkowski d) M]
  [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))]

/-- **A flat spacetime carries its causality** (`prop:GX_espace_temps_topo` for
`(Isom(𝐌ⁿ), 𝐌ⁿ)`): an `(Isom(𝐌ⁿ), 𝐌ⁿ)`-manifold `M` carries an absolutely minimal causality for
which every chart of the maximal atlas is an isomorphism onto `minkowski d`, and it is the only
absolutely minimal one. -/
theorem flat_existsUnique_causality :
    ∃ C : Causality M,
      (∀ e ∈ (gxGroupoid (isom d) (Minkowski d)).maximalAtlas M, ChartIso C (minkowski d) e) ∧
      C.AbsolutelyMinimal ∧
      ∀ C' : Causality M,
        (∀ e ∈ (gxGroupoid (isom d) (Minkowski d)).maximalAtlas M, ChartIso C' (minkowski d) e) →
          C'.AbsolutelyMinimal → C' = C :=
  existsUnique_causality_GX_maximal (minkowski d) minkowski_causallyArcConnected
    isom_strongMorphism

variable (d M) in
/-- **The causality of a flat spacetime**: the absolutely minimal causality of
`flat_existsUnique_causality`. Use it through `flatCausality_chartIso`,
`flatCausality_absolutelyMinimal` and `eq_flatCausality`. -/
noncomputable def flatCausality : Causality M :=
  Classical.choose (flat_existsUnique_causality (d := d) (M := M))

/-- Every chart of the maximal atlas is an isomorphism from `flatCausality` onto `minkowski d`. -/
theorem flatCausality_chartIso {e : OpenPartialHomeomorph M (Minkowski d)}
    (he : e ∈ (gxGroupoid (isom d) (Minkowski d)).maximalAtlas M) :
    ChartIso (flatCausality d M) (minkowski d) e :=
  (Classical.choose_spec (flat_existsUnique_causality (d := d) (M := M))).1 e he

/-- The chart at a point is an isomorphism from `flatCausality` onto `minkowski d`. -/
theorem flatCausality_chartIso_chartAt (x : M) :
    ChartIso (flatCausality d M) (minkowski d) (chartAt (Minkowski d) x) :=
  flatCausality_chartIso ((gxGroupoid (isom d) (Minkowski d)).subset_maximalAtlas
    (chart_mem_atlas (Minkowski d) x))

/-- `flatCausality` is absolutely minimal. -/
theorem flatCausality_absolutelyMinimal : (flatCausality d M).AbsolutelyMinimal :=
  (Classical.choose_spec (flat_existsUnique_causality (d := d) (M := M))).2.1

/-- `flatCausality` is the only absolutely minimal causality making every chart of the maximal
atlas an isomorphism onto `minkowski d`. -/
theorem eq_flatCausality (C : Causality M)
    (hC : ∀ e ∈ (gxGroupoid (isom d) (Minkowski d)).maximalAtlas M, ChartIso C (minkowski d) e)
    (hmin : C.AbsolutelyMinimal) : C = flatCausality d M :=
  (Classical.choose_spec (flat_existsUnique_causality (d := d) (M := M))).2.2 C hC hmin

/-- With a chart of the maximal atlas defined on all of `M`, `flatCausality` is unique
**outright**: any causality making every chart of the maximal atlas an isomorphism onto
`minkowski d` is `flatCausality`, absolutely minimal or not
(`existsUnique_causality_GX_of_covering_chart`). -/
theorem eq_flatCausality_of_covering_chart
    (hcov : ∃ e ∈ (gxGroupoid (isom d) (Minkowski d)).maximalAtlas M, e.source = univ)
    (C : Causality M)
    (hC : ∀ e ∈ (gxGroupoid (isom d) (Minkowski d)).maximalAtlas M, ChartIso C (minkowski d) e) :
    C = flatCausality d M := by
  obtain ⟨e, he, hs⟩ := hcov
  exact eq_of_chartIso_of_source_eq_univ (hC e he) (flatCausality_chartIso he) hs

end FlatSpacetime

/-- **Non-vacuity.** `𝐌ⁿ` with its own chart is a flat spacetime, and its causality is
`minkowski d`. -/
theorem flatCausality_self : flatCausality d (Minkowski d) = minkowski d := by
  have hatlas : ∀ e ∈ atlas (Minkowski d) (Minkowski d), ChartIso (minkowski d) (minkowski d) e :=
    (causality_GX_self (G := isom d) (minkowski d) minkowski_causallyArcConnected
      isom_strongMorphism).1
  exact (eq_flatCausality (minkowski d) (fun e he => chartIso_of_mem_maximalAtlas
    minkowski_causallyArcConnected isom_strongMorphism hatlas minkowski_absolutelyMinimal he)
    minkowski_absolutelyMinimal).symm

end Flat

end Causal
