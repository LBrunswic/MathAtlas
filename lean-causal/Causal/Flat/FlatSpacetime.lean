import Causal.Flat.IsomCausal
import Causal.Flat.Achronal
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Covering.Basic

/-!
# `Causal.Flat.FlatSpacetime` — flat spacetimes, isometric embeddings, GH, MGH, AMGH

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §2.3–2.5.
No b-label is certified: §2 is prose (its one environment, Rem 2.3 `clomax`, is OQ-22's corrected
statement, DEC-44, not attempted here). This module is the vocabulary of `docs/BARBOT-THEOREMS.md`
§1, with the rulings DEC-43/44/45. Line numbers are those of the **labelled**
`papers/barbot/legacy/labeled/GHFspace.tex` (`docs/BARBOT.md` uses the original's, 2–6 lines
earlier here).

> they are $(G,X)$-manifolds with $X = {\bf M}^{n}$ and $G = \mbox{Isom}(M^{n})$. (l.489–490)

> A $S$-embedding of $M$ is a isometric embedding $f: M \rightarrow M'$ where $M'$ is a
> spacetime, such that $f(S)$ is still a Cauchy hypersurface in $M'$. Actually, this notion does
> not depend on the choice of the Cauchy hypersurface […] we call such a map a \emph{Cauchy
> embedding.\/} Now, a globally hyperbolic manifold $M$ is said maximal if any Cauchy embedding of
> $M$ into some globally hyperbolic spacetime $N$ is necessarly surjective. (l.519–527)

> MGH spacetimes may admit nonsurjective isometric embeddings in bigger MGH spacetimes. (l.538–540)

> We call such a spacetime \emph{Cauchy-compact\/} GH spacetime (abbreviation CGH). (l.564–565)

> We say that a flat Cauchy-complete GH spacetime $M$ is absolutely maximal (abbreviation AMGH) if
> any isometric embedding into another Cauchy-complete flat GH spacetime is surjective. (l.573–575)

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; `Minkowski d =
ℝ × EuclideanSpace ℝ (Fin d)` has `d` spatial dimensions, so Barbot's `n` is `d + 1`.

## What is proved

* `closedUnderRestriction_gxGroupoid` (instance, any `G`, `X`): so mathlib's
  `Opens.instChartedSpace`/`Opens.instHasGroupoid` make an open subset a `(G,X)`-manifold.
* `flatCausality_absolutelyMinimalOn` — the flat causality is absolutely minimal on every open set.
* `IsLocalIsometry d f` (continuous; near each `x`, `chart(f x) ∘ f ∘ chart(x)⁻¹` is some
  `g ∈ isom d`), `IsIsometricEmbedding` (DEC-45: + injective), `IsTameEmbedding` (+ bijective on
  every `π₁`, `FundamentalGroup.map`), `IsFiniteCover`. `isLocalIsometry_iff_eventually` (the
  pointwise form `chart(f x)(f y) = g • chart(x) y`), `exists_opens`, identity and composition
  for all three map classes.
* **Through the charts and `IsomCausal`**: a local isometry is a local homeomorphism, a
  `LocalIsomorphism` and a `StrongMorphism` of the flat causalities, hence an `IsEMorphism`; an
  isometric embedding is an open embedding and an isomorphism onto its image on **every** open
  set (`IsIsometricEmbedding.rel_iff`). General: `LocalIso.strongMorphism` (a local isomorphism
  out of an absolutely minimal causality is strong), `LocalIso.rel_of_image` (an injective one
  into a causality absolutely minimal on every open set reflects the relations).
* Open subsets: `isIsometricEmbedding_subtype_val`, and `flatCausality_opens` — **the flat
  causality of `W` is the restriction of `M`'s** (`((flatCausality d M).restrict W).toSubtype`).
* `FlatSpacetime d` (bundled: `T2`, connected, charted, `HasGroupoid`), `of`, `minkowskiSpace`,
  `ofOpens` (a connected open subset). `GH`, `BarbotGH`, `IsFlatCauchyEmbedding`, `MGH`,
  `AbsMax P`, `AMGH CC`, `CauchyCompact`; `isFlatCauchyEmbedding_iff`,
  `IsFlatCauchyEmbedding.isCauchySurface_image` (l.521–524: independent of the hypersurface),
  `barbotGH_of_gh` (Geroch (i)⇒(iii)), `MGH.of_absMax`, `AbsMax.mono`,
  `CauchyCompact.of_isCauchySurface` (the acausal conjunct is redundant under causal
  arc-connectedness + `CurvesExtend`); `FlatSpacetime.instFirstCountableTopology` (from the charts).
* `𝐌ⁿ`: `gh_minkowskiSpace`, `barbotGH_minkowskiSpace`, `isIsometricEmbedding_smul`; the future
  cone is not absolutely maximal among GH targets (`not_absMax_futureTimelikeConeSpace`).

## Hypothesis checklist

| paper | here |
|---|---|
| flat spacetime: `(Isom(𝐌ⁿ), 𝐌ⁿ)`-manifold (l.485–490) | ✓ carried: `ChartedSpace`, `HasGroupoid (gxGroupoid (isom d) _)` |
| a manifold: Hausdorff, second countable; a spacetime: connected | ⚠ weakened: bundled `FlatSpacetime` asks `T2` + connected; no second countability; the map-level lemmas ask neither |
| isometric embedding (undefined, l.519) | ⚠ reading DEC-45: injective local `(isom d, 𝐌ⁿ)`-morphism, read in the preferred charts |
| GH: proper time function, Cauchy fibres (l.500–509) | ⚠ reading: `GH` is ETT's (causal + compact diamonds); Barbot's is `BarbotGH` (a Cauchy surface); relation below |
| MGH: targets "some globally hyperbolic spacetime" (l.526–527) | ⚠ narrowed to flat targets of the same dimension and universe (justified by Rem 2.1, l.532–535); the targets are not asked second countable (harmless, see SCOPE) |
| AMGH: "any isometric embedding into another Cauchy-complete flat GH spacetime" (l.573–575) | ⚠ same universe, no second countability asked of the target (see SCOPE) |
| Cauchy-complete (l.551–553) | not defined: AMGH takes it as a parameter `CC` (DEC-35; `Flat/CauchyComplete` later) |
| Cauchy-compact: closed spacelike Cauchy hypersurface (l.560–565) | ⚠ reading: a compact **acausal** Cauchy surface (spacelikeness needs the length layer); the acausal conjunct is redundant under causal arc-connectedness + `CurvesExtend` (`CauchyCompact.of_isCauchySurface`) |

## SCOPE (disclosed)

* **Universes.** `FlatSpacetime.{u} d` has `carrier : Type u`; `MGH` and `AbsMax` quantify over
  targets **in the same universe `u`**. Barbot's "any" ranges over all spacetimes; every target the
  paper builds is a quotient of an open set of `𝐌ⁿ`, so `u = 0` loses nothing the paper uses.
  Nor does the restriction lose anything in principle: a connected flat spacetime is second
  countable (below), so it has cardinality at most that of `ℝ` and is homeomorphic to one in
  `Type 0`.
* **No second countability.** The bundled class, hence the target class of `MGH` and `AbsMax`,
  does not ask second countability, so it is formally larger than Barbot's class of manifolds.
  This is harmless: a connected Lorentzian manifold is paracompact (Geroch 1968), hence second
  countable, so the class does not actually grow; the fact is cited, not proved here.
* **GH vs Barbot's GH.** `barbotGH_of_gh` is `geroch_i_imp_iii` with its hypotheses (admissible
  measures, tarentin, causal arc-connectedness, `J^±(p) ≠ {p}`, first countability) carried as
  named hypotheses: none is proved for a general flat spacetime here (first countability is no
  longer carried: `FlatSpacetime.instFirstCountableTopology`). The converse is the cited
  (iii)⇒(i) of `CausalScaffold.GerochEquiv` (a `sorry`), not imported. **Non-vacuity**
  (kb/0011/0012): on `𝐌ⁿ` the hypotheses are `minkowski_tarentin` (`Causal/Minkowski.lean`),
  `minkowski_causallyArcConnected`, `J^±(p) ≠ {p}` (elementary) and `minkowski_mesure_dieckmann`
  (`Causal.MinkowskiMeasure`, sorry-free since 2026-11-20, not imported here); the
  library's sorry-free joint witness is the timelike line (`Causal/Geroch.lean`,
  `timelikeLine_admissible_past_and_future`), which is not a flat spacetime. The conclusion for
  `𝐌ⁿ` is proved directly (`barbotGH_minkowskiSpace`), so nothing here is used vacuously.
* `IsLocalIsometry` reads `chartAt` at `x` and `f x`. Its independence of the charts over the
  maximal atlases is **proved, sorry-free, in `Causal.Port.GXBasic`**
  (`IsGXMorphism.exists_smul_eq_of_mem_maximalAtlas`, with `isGXMorphism_id`,
  `IsGXMorphism.comp`, `IsGXMorphism.isLocalHomeomorph`), and `IsLocalIsometry d f` is
  definitionally `IsGXMorphism (isom d) (Minkowski d) f` (`isGXMorphism_iff'`; the right side of
  `isLocalIsometry_iff_eventually` is literally it). It is **deliberately not imported**: `Port/*`
  has not graduated (campaign rule), so `id`, `comp` and `isLocalHomeomorph` are re-proved here.
  Follow-up when Port graduates: `isLocalIsometry_iff_isGXMorphism` (a one-liner) and
  deduplicate.
* `closedUnderRestriction_gxGroupoid` is fully general (any `G`, `X`) but sits in `Causal.Flat`;
  follow-up: move it to `Causal/GXStructure` or `Port/GXBasic` when the scaffold graduates, and
  correct `Flat/Developing.lean`'s SCOPE (l.74, "`gxGroupoid` is not yet shown
  `ClosedUnderRestriction`"), which this instance makes stale.
* `IsFiniteCover` is BARBOT-THEOREMS' definition (`IsCoveringMap`, local isometry, finite fibres;
  surjectivity not asked); no lemma beyond projections, `id` not proved (no `IsCoveringMap` of a
  homeomorphism found at this pin).
* Rem 2.2 (l.538–545): only that the future cone `Ω` embeds non-surjectively in the GH `𝐌ⁿ` is
  proved; that `Ω` is MGH and that `Ω ∩ {Q = −1}` is Cauchy in `Ω` are not (the latter half's
  failure in `𝐌ⁿ` is `Flat.Achronal`'s `not_isCauchySurface_connectedComponentIn_inter`).
* No MGH or AMGH witness is proved (MGH of `𝐌ⁿ` needs an argument on inextensible curves leaving
  the image; `AbsMax (fun _ => False) M` is the trivial one).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
wave 2, package WP-31a-FlatSpacetime.
-/

namespace Causal.Flat

open Set TopologicalSpace Topology Filter Function Relation

universe u v w

variable {d : ℕ}

/-! ### The `(G, X)`-groupoid is closed under restriction -/

/-- **`gxGroupoid G X` is closed under restriction**: a restriction of a map which is locally the
action of `G` is still one. This is what makes an open subset of a `(G,X)`-manifold a
`(G,X)`-manifold through mathlib's `TopologicalSpace.Opens.instHasGroupoid`. -/
instance closedUnderRestriction_gxGroupoid {G : Type w} {X : Type v} [TopologicalSpace X]
    [Group G] [MulAction G X] [ContinuousConstSMul G X] :
    ClosedUnderRestriction (gxGroupoid G X) := by
  refine ⟨fun {e} he s _ => ?_⟩
  rw [gxGroupoid, mem_groupoid_of_pregroupoid] at he ⊢
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨g, hg⟩ := he.1 x (by rw [OpenPartialHomeomorph.restr_source] at hx; exact hx.1)
    exact ⟨g, by simpa using hg⟩
  · obtain ⟨g, hg⟩ := he.2 x (by rw [OpenPartialHomeomorph.restr_target] at hx; exact hx.1)
    exact ⟨g, by simpa using hg⟩

/-! ### The flat causality is absolutely minimal on every open set -/

section AbsMin

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (Minkowski d) M]
  [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))]

/-- `flatCausality` is absolutely minimal on **every** open set. -/
theorem flatCausality_absolutelyMinimalOn (W : Opens M) :
    (flatCausality d M).AbsolutelyMinimalOn W :=
  absolutelyMinimalOn_of_locally flatCausality_absolutelyMinimal (fun x =>
    ⟨chartSource (chartAt (Minkowski d) x), mem_chart_source _ x, fun _ hW =>
      (flatCausality_chartIso_chartAt x).absolutelyMinimalOn hW
        (minkowski_causallyArcConnected.absolutelyMinimalOn_all _)⟩) W


end AbsMin

/-! ### Local isomorphisms: two general facts -/

namespace LocalIso

variable {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
  {C : Causality M} {D : Causality N} {φ : M → N}

/-- A local isomorphism out of a causality absolutely minimal (on `M`) is a strong morphism: a
relation of `φ⁻¹(U)` is a chain of relations in small open sets, each of which `φ` carries into
a relation of its image, contained in `U`. -/
theorem strongMorphism (hφ : LocalIsomorphism C D φ) (hmin : C.AbsolutelyMinimal) :
    StrongMorphism C D φ := by
  choose V₁ hx₁ _hi₁ hV₁ using hφ.2
  let S : Set (Opens M) := range V₁
  have hS : ∀ z ∈ (⊤ : Opens M), ∃ O ∈ S, z ∈ O := fun z _ => ⟨_, ⟨z, rfl⟩, hx₁ z⟩
  have hmin' := (Precausality.absolutelyMinimal_iff.1 hmin) S hS
  have himg : ∀ O : Opens M, IsOpen (φ '' O) := fun O => hφ.1.isOpenMap _ O.isOpen
  refine ⟨hφ.1.continuous, hφ.1.isOpenMap, fun U V hV x y hxy => ?_, fun U V hV x y hxy => ?_⟩
  · have hc := (hmin' V le_top x y).1 hxy
    clear hxy
    induction hc with
    | single hl =>
      obtain ⟨O, ⟨z, rfl⟩, hab⟩ := hl
      have ha := C.le_mem_left hab
      have hb := C.le_mem_right hab
      have h1 := ((hV₁ z (V ⊓ V₁ z) inf_le_right ⟨_, himg _⟩ rfl _ ha _ hb).1).1 hab
      refine D.le_mono ?_ h1
      rintro _ ⟨w, hw, rfl⟩
      have : w ∈ φ ⁻¹' (U : Set N) := hV ▸ hw.1
      exact this
    | tail _ hl ih =>
      obtain ⟨O, ⟨z, rfl⟩, hab⟩ := hl
      have ha := C.le_mem_left hab
      have hb := C.le_mem_right hab
      have h1 := ((hV₁ z (V ⊓ V₁ z) inf_le_right ⟨_, himg _⟩ rfl _ ha _ hb).1).1 hab
      refine D.le_trans ih (D.le_mono ?_ h1)
      rintro _ ⟨w, hw, rfl⟩
      have : w ∈ φ ⁻¹' (U : Set N) := hV ▸ hw.1
      exact this
  · have hc := (hmin' V le_top x y).2 hxy
    clear hxy
    induction hc with
    | single hl =>
      obtain ⟨O, ⟨z, rfl⟩, hab⟩ := hl
      have ha := C.lt_mem_left hab
      have hb := C.lt_mem_right hab
      have h1 := ((hV₁ z (V ⊓ V₁ z) inf_le_right ⟨_, himg _⟩ rfl _ ha _ hb).2).1 hab
      refine D.lt_mono ?_ h1
      rintro _ ⟨w, hw, rfl⟩
      have : w ∈ φ ⁻¹' (U : Set N) := hV ▸ hw.1
      exact this
    | tail _ hl ih =>
      obtain ⟨O, ⟨z, rfl⟩, hab⟩ := hl
      have ha := C.lt_mem_left hab
      have hb := C.lt_mem_right hab
      have h1 := ((hV₁ z (V ⊓ V₁ z) inf_le_right ⟨_, himg _⟩ rfl _ ha _ hb).2).1 hab
      refine D.lt_trans ih (D.lt_mono ?_ h1)
      rintro _ ⟨w, hw, rfl⟩
      have : w ∈ φ ⁻¹' (U : Set N) := hV ▸ hw.1
      exact this

-- Lifting a chain of image relations along an injective map.
omit [TopologicalSpace M] [TopologicalSpace N] in
private theorem lift_transGen (hinj : Injective φ) {R : M → M → Prop} (hR : ∀ {a b c}, R a b → R b c → R a c)
    {x : M} {b' : N}
    (h : TransGen (fun a' b' => ∃ a b, a' = φ a ∧ b' = φ b ∧ R a b) (φ x) b') :
    ∃ b, b' = φ b ∧ R x b := by
  induction h with
  | single hl =>
    obtain ⟨a, b, ha, rfl, hab⟩ := hl
    exact ⟨b, rfl, hinj ha ▸ hab⟩
  | tail _ hl ih =>
    obtain ⟨c, rfl, hxc⟩ := ih
    obtain ⟨a, b, ha, rfl, hab⟩ := hl
    exact ⟨b, rfl, hR hxc (hinj ha ▸ hab)⟩

/-- An **injective** local isomorphism into a causality absolutely minimal on every open set
reflects the relations: a relation of `φ(V)` between two images is one of `V`. -/
theorem rel_of_image (hφ : LocalIsomorphism C D φ) (hinj : Injective φ)
    (hD : ∀ U : Opens N, D.AbsolutelyMinimalOn U) (V : Opens M) (U : Opens N)
    (hU : (U : Set N) = φ '' V) (x y : M) :
    (D.le U (φ x) (φ y) → C.le V x y) ∧ (D.lt U (φ x) (φ y) → C.lt V x y) := by
  choose V₁ hx₁ _hi₁ hV₁ using hφ.2
  have himg : ∀ O : Opens M, IsOpen (φ '' O) := fun O => hφ.1.isOpenMap _ O.isOpen
  let O' : M → Opens N := fun z => ⟨φ '' ((V ⊓ V₁ z : Opens M) : Set M), himg _⟩
  let S : Set (Opens N) := range O'
  have hS : ∀ p ∈ U, ∃ O ∈ S, p ∈ O := by
    intro p hp
    rw [← SetLike.mem_coe, hU] at hp
    obtain ⟨a, ha, rfl⟩ := hp
    exact ⟨O' a, ⟨a, rfl⟩, a, ⟨ha, hx₁ a⟩, rfl⟩
  have hOU : ∀ z, (U ⊓ O' z : Set N) = φ '' (V ⊓ V₁ z : Opens M) := by
    intro z
    apply Set.inter_eq_right.2
    rintro _ ⟨w, hw, rfl⟩
    rw [hU]; exact ⟨w, hw.1, rfl⟩
  constructor
  · intro hxy
    have hc := ((hD U) S hS U le_rfl _ _).1 hxy
    have hc' : TransGen (fun a' b' => ∃ a b, a' = φ a ∧ b' = φ b ∧ C.le V a b) (φ x) (φ y) := by
      refine TransGen.mono (fun a' b' => ?_) hc
      rintro ⟨O, ⟨z, rfl⟩, hab⟩
      have ha := D.le_mem_left hab
      have hb := D.le_mem_right hab
      obtain ⟨a, ha', rfl⟩ : a' ∈ φ '' (V ⊓ V₁ z : Opens M) := hOU z ▸ ha
      obtain ⟨b, hb', rfl⟩ : b' ∈ φ '' (V ⊓ V₁ z : Opens M) := hOU z ▸ hb
      exact ⟨a, b, rfl, rfl, C.le_mono inf_le_left
        (((hV₁ z _ inf_le_right _ (hOU z) a ha' b hb').1).2 hab)⟩
    obtain ⟨b, hb, hxb⟩ := lift_transGen hinj (R := C.le V) (fun h₁ h₂ => C.le_trans h₁ h₂) hc'
    rwa [← hinj hb] at hxb
  · intro hxy
    have hc := ((hD U) S hS U le_rfl _ _).2 hxy
    have hc' : TransGen (fun a' b' => ∃ a b, a' = φ a ∧ b' = φ b ∧ C.lt V a b) (φ x) (φ y) := by
      refine TransGen.mono (fun a' b' => ?_) hc
      rintro ⟨O, ⟨z, rfl⟩, hab⟩
      have ha := D.lt_mem_left hab
      have hb := D.lt_mem_right hab
      obtain ⟨a, ha', rfl⟩ : a' ∈ φ '' (V ⊓ V₁ z : Opens M) := hOU z ▸ ha
      obtain ⟨b, hb', rfl⟩ : b' ∈ φ '' (V ⊓ V₁ z : Opens M) := hOU z ▸ hb
      exact ⟨a, b, rfl, rfl, C.lt_mono inf_le_left
        (((hV₁ z _ inf_le_right _ (hOU z) a ha' b hb').2).2 hab)⟩
    obtain ⟨b, hb, hxb⟩ := lift_transGen hinj (R := C.lt V) (fun h₁ h₂ => C.lt_trans h₁ h₂) hc'
    rwa [← hinj hb] at hxb

end LocalIso

/-! ### Local isometries -/

section Maps

variable {M : Type u} {N : Type v} {P : Type w}
  [TopologicalSpace M] [ChartedSpace (Minkowski d) M]
  [TopologicalSpace N] [ChartedSpace (Minkowski d) N]
  [TopologicalSpace P] [ChartedSpace (Minkowski d) P]

variable (d) in
/-- **A local isometry** of flat spacetimes (a local `(Isom(𝐌ⁿ), 𝐌ⁿ)`-morphism, DEC-45): a
continuous map which, read in the charts at `x` and at `f x`, is near `x` the action of an
element of `isom d`. -/
def IsLocalIsometry (f : M → N) : Prop :=
  Continuous f ∧ ∀ x : M, ∃ g : isom d,
    (chartAt (Minkowski d) (f x)) ∘ f ∘ (chartAt (Minkowski d) x).symm
      =ᶠ[𝓝 (chartAt (Minkowski d) x x)] fun p => g • p

variable (d) in
/-- **An isometric embedding** (DEC-45, BARBOT-THEOREMS §5 (i)): an injective local isometry. -/
def IsIsometricEmbedding (f : M → N) : Prop := IsLocalIsometry d f ∧ Injective f

variable (d) in
/-- **A tame embedding**: an isometric embedding inducing a bijection of every fundamental
group. -/
def IsTameEmbedding (f : M → N) : Prop :=
  ∃ hf : Continuous f, IsIsometricEmbedding d f ∧
    ∀ x : M, Bijective (FundamentalGroup.map ⟨f, hf⟩ x)

variable (d) in
/-- **A finite cover**: a covering map which is a local isometry, with finite fibres. -/
def IsFiniteCover (p : M → N) : Prop :=
  IsCoveringMap p ∧ IsLocalIsometry d p ∧ ∀ y : N, (p ⁻¹' {y}).Finite

theorem IsLocalIsometry.continuous {f : M → N} (hf : IsLocalIsometry d f) : Continuous f := hf.1

/-- The pointwise form: near `x`, `chart(f x) (f y) = g • chart(x) y`. -/
theorem isLocalIsometry_iff_eventually {f : M → N} :
    IsLocalIsometry d f ↔ Continuous f ∧ ∀ x : M, ∃ g : isom d, ∀ᶠ y in 𝓝 x,
      chartAt (Minkowski d) (f x) (f y) = g • chartAt (Minkowski d) x y := by
  refine and_congr_right fun _ => forall_congr' fun x => exists_congr fun g => ?_
  constructor
  · intro h
    have h1 := ((chartAt (Minkowski d) x).continuousAt (mem_chart_source _ x)).eventually h
    filter_upwards [h1, (chartAt (Minkowski d) x).open_source.mem_nhds (mem_chart_source _ x)]
      with y hy hys
    simp only [comp_apply] at hy
    rwa [(chartAt (Minkowski d) x).left_inv hys] at hy
  · intro h
    have hsymm : Tendsto (chartAt (Minkowski d) x).symm (𝓝 (chartAt (Minkowski d) x x)) (𝓝 x) := by
      have := (chartAt (Minkowski d) x).continuousAt_symm (mem_chart_target _ x)
      rw [ContinuousAt, (chartAt (Minkowski d) x).left_inv (mem_chart_source _ x)] at this
      exact this
    filter_upwards [hsymm.eventually h,
      (chartAt (Minkowski d) x).open_target.mem_nhds (mem_chart_target _ x)] with p hp hpt
    simp only [comp_apply]
    rwa [(chartAt (Minkowski d) x).right_inv hpt] at hp

/-- Near each point, on an open set in the chart's source mapped into the target chart's source,
a local isometry is `chart(f x) ∘ f = g • chart(x)`. -/
theorem IsLocalIsometry.exists_opens {f : M → N} (hf : IsLocalIsometry d f) (x : M) :
    ∃ g : isom d, ∃ O : Opens M, x ∈ O ∧ (O : Set M) ⊆ (chartAt (Minkowski d) x).source ∧
      MapsTo f O (chartAt (Minkowski d) (f x)).source ∧
      ∀ y ∈ O, chartAt (Minkowski d) (f x) (f y) = g • chartAt (Minkowski d) x y := by
  obtain ⟨hc, h⟩ := isLocalIsometry_iff_eventually.1 hf
  obtain ⟨g, hg⟩ := h x
  have hall : ∀ᶠ y in 𝓝 x, y ∈ (chartAt (Minkowski d) x).source ∧
      f y ∈ (chartAt (Minkowski d) (f x)).source ∧
      chartAt (Minkowski d) (f x) (f y) = g • chartAt (Minkowski d) x y := by
    filter_upwards [(chartAt (Minkowski d) x).open_source.mem_nhds (mem_chart_source _ x),
      hc.continuousAt.eventually
        ((chartAt (Minkowski d) (f x)).open_source.mem_nhds (mem_chart_source _ (f x))), hg]
      with y h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨O, hOs, hO, hxO⟩ := mem_nhds_iff.1 hall
  exact ⟨g, ⟨O, hO⟩, hxO, fun y hy => (hOs hy).1, fun y hy => (hOs hy).2.1,
    fun y hy => (hOs hy).2.2⟩

theorem isLocalIsometry_id : IsLocalIsometry d (id : M → M) :=
  isLocalIsometry_iff_eventually.2 ⟨continuous_id, fun x => ⟨1, Eventually.of_forall fun y => by
    simp⟩⟩

theorem IsLocalIsometry.comp {f : M → N} {h : N → P} (hh : IsLocalIsometry d h)
    (hf : IsLocalIsometry d f) : IsLocalIsometry d (h ∘ f) := by
  obtain ⟨hfc, hf'⟩ := isLocalIsometry_iff_eventually.1 hf
  obtain ⟨hhc, hh'⟩ := isLocalIsometry_iff_eventually.1 hh
  refine isLocalIsometry_iff_eventually.2 ⟨hhc.comp hfc, fun x => ?_⟩
  obtain ⟨g, hg⟩ := hf' x
  obtain ⟨g', hg'⟩ := hh' (f x)
  refine ⟨g' * g, ?_⟩
  filter_upwards [hfc.continuousAt.eventually hg', hg] with y h1 h2
  simp only [comp_apply, h1, h2, mul_smul]

/-- A local isometry is a local homeomorphism. -/
theorem IsLocalIsometry.isLocalHomeomorph {f : M → N} (hf : IsLocalIsometry d f) :
    IsLocalHomeomorph f := by
  refine IsLocalHomeomorph.mk f fun x => ?_
  obtain ⟨g, O, hxO, hOs, hmaps, heq⟩ := hf.exists_opens x
  set e := chartAt (Minkowski d) x
  set e' := chartAt (Minkowski d) (f x)
  let E := ((e.restrOpen O O.isOpen).trans (isomChart g)).trans e'.symm
  have hsrc : ∀ y ∈ O, y ∈ E.source := by
    intro y hy
    simp only [E, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.restrOpen_source,
      isomChart_source, OpenPartialHomeomorph.symm_source, mem_inter_iff, mem_preimage,
      OpenPartialHomeomorph.coe_trans, comp_apply, OpenPartialHomeomorph.coe_restrOpen,
      isomChart_apply, mem_univ, and_true]
    refine ⟨⟨hOs hy, hy⟩, ?_⟩
    rw [← heq y hy]
    exact e'.map_source (hmaps hy)
  refine ⟨E, hsrc x hxO, fun y hy => ?_⟩
  have hyO : y ∈ O := by
    simp only [E, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.restrOpen_source,
      mem_inter_iff] at hy
    exact hy.1.1.2
  simp only [E, OpenPartialHomeomorph.coe_trans, comp_apply, OpenPartialHomeomorph.coe_restrOpen,
    isomChart_apply]
  rw [← heq y hyO, e'.left_inv (hmaps hyO)]

theorem IsLocalIsometry.isOpenMap {f : M → N} (hf : IsLocalIsometry d f) : IsOpenMap f :=
  hf.isLocalHomeomorph.isOpenMap

theorem IsIsometricEmbedding.isLocalIsometry {f : M → N} (hf : IsIsometricEmbedding d f) :
    IsLocalIsometry d f := hf.1

theorem IsIsometricEmbedding.injective {f : M → N} (hf : IsIsometricEmbedding d f) :
    Injective f := hf.2

theorem IsIsometricEmbedding.continuous {f : M → N} (hf : IsIsometricEmbedding d f) :
    Continuous f := hf.1.1

/-- **An isometric embedding is an open embedding.** -/
theorem IsIsometricEmbedding.isOpenEmbedding {f : M → N} (hf : IsIsometricEmbedding d f) :
    IsOpenEmbedding f :=
  hf.1.isLocalHomeomorph.isOpenEmbedding_of_injective hf.2

theorem isIsometricEmbedding_id : IsIsometricEmbedding d (id : M → M) :=
  ⟨isLocalIsometry_id, injective_id⟩

theorem IsIsometricEmbedding.comp {f : M → N} {h : N → P} (hh : IsIsometricEmbedding d h)
    (hf : IsIsometricEmbedding d f) : IsIsometricEmbedding d (h ∘ f) :=
  ⟨hh.1.comp hf.1, hh.2.comp hf.2⟩

theorem IsTameEmbedding.isIsometricEmbedding {f : M → N} (hf : IsTameEmbedding d f) :
    IsIsometricEmbedding d f := hf.2.1

theorem isTameEmbedding_id : IsTameEmbedding d (id : M → M) := by
  refine ⟨continuous_id, isIsometricEmbedding_id, fun x => ?_⟩
  have : (FundamentalGroup.map ⟨(id : M → M), continuous_id⟩ x :
      FundamentalGroup M x → FundamentalGroup M x) = id := by
    funext p
    rcases p
    rfl
  rw [this]
  exact bijective_id

theorem IsTameEmbedding.comp {f : M → N} {h : N → P} (hh : IsTameEmbedding d h)
    (hf : IsTameEmbedding d f) : IsTameEmbedding d (h ∘ f) := by
  obtain ⟨hfc, hfe, hfb⟩ := hf
  obtain ⟨hhc, hhe, hhb⟩ := hh
  refine ⟨hhc.comp hfc, hhe.comp hfe, fun x => ?_⟩
  have : (FundamentalGroup.map ⟨h ∘ f, hhc.comp hfc⟩ x : FundamentalGroup M x → _) =
      (FundamentalGroup.map ⟨h, hhc⟩ (f x)) ∘ (FundamentalGroup.map ⟨f, hfc⟩ x) := by
    funext p
    rcases p
    rfl
  rw [this]
  exact (hhb (f x)).comp (hfb x)

theorem IsFiniteCover.isLocalIsometry {p : M → N} (hp : IsFiniteCover d p) :
    IsLocalIsometry d p := hp.2.1

theorem IsFiniteCover.isCoveringMap {p : M → N} (hp : IsFiniteCover d p) : IsCoveringMap p :=
  hp.1

end Maps

/-! ### Local isometries are morphisms of the flat causalities -/

section Causal

variable {M : Type u} {N : Type v}
  [TopologicalSpace M] [ChartedSpace (Minkowski d) M]
  [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))]
  [TopologicalSpace N] [ChartedSpace (Minkowski d) N]
  [HasGroupoid N (gxGroupoid (isom d) (Minkowski d))]

/-- **A local isometry is a local isomorphism of the flat causalities.** -/
theorem IsLocalIsometry.localIsomorphism {f : M → N} (hf : IsLocalIsometry d f) :
    LocalIsomorphism (flatCausality d M) (flatCausality d N) f := by
  refine ⟨hf.isLocalHomeomorph, fun x => ?_⟩
  obtain ⟨g, O, hxO, hOs, hmaps, heq⟩ := hf.exists_opens x
  have hinj : InjOn f O := by
    intro y hy z hz hyz
    have h1 := heq y hy
    rw [hyz, heq z hz] at h1
    exact (chartAt (Minkowski d) x).injOn (hOs hy) (hOs hz) (MulAction.injective g h1).symm
  refine ⟨O, hxO, hinj, fun V' hV' U hU y hy z hz => ?_⟩
  have hVs : V' ≤ chartSource (chartAt (Minkowski d) x) := fun p hp => hOs (hV' hp)
  have hUs : U ≤ chartSource (chartAt (Minkowski d) (f x)) := by
    intro p hp
    rw [← SetLike.mem_coe, hU] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact hmaps (hV' hq)
  have himg : chartImage (chartAt (Minkowski d) (f x)) U =
      isomImage g (chartImage (chartAt (Minkowski d) x) V') := by
    apply SetLike.coe_injective
    rw [coe_chartImage_of_le hUs, coe_isomImage, coe_chartImage_of_le hVs, hU, image_image,
      image_image]
    exact image_congr fun q hq => heq q (hV' hq)
  have hfy : f y ∈ U := by rw [← SetLike.mem_coe, hU]; exact mem_image_of_mem f hy
  have hfz : f z ∈ U := by rw [← SetLike.mem_coe, hU]; exact mem_image_of_mem f hz
  have h1 := flatCausality_chartIso_chartAt (d := d) x V' hVs y hy z hz
  have h2 := flatCausality_chartIso_chartAt (d := d) (f x) U hUs (f y) hfy (f z) hfz
  rw [himg, heq y (hV' hy), heq z (hV' hz)] at h2
  exact ⟨h1.1.trans ((le_iff_le_isomImage g _ _ _).trans h2.1.symm),
    h1.2.trans ((lt_iff_lt_isomImage g _ _ _).trans h2.2.symm)⟩

/-- **A local isometry is a strong morphism of the flat causalities.** -/
theorem IsLocalIsometry.strongMorphism {f : M → N} (hf : IsLocalIsometry d f) :
    StrongMorphism (flatCausality d M) (flatCausality d N) f :=
  LocalIso.strongMorphism hf.localIsomorphism flatCausality_absolutelyMinimal

/-- **A local isometry is an abstract `𝕄≥0`-morphism of the flat causalities.** -/
theorem IsLocalIsometry.isEMorphism {f : M → N} (hf : IsLocalIsometry d f) :
    IsEMorphism (flatCausality d M) (flatCausality d N) f :=
  isEMorphism_iff.2 ⟨hf.strongMorphism, hf.localIsomorphism⟩

theorem IsIsometricEmbedding.isEMorphism {f : M → N} (hf : IsIsometricEmbedding d f) :
    IsEMorphism (flatCausality d M) (flatCausality d N) f := hf.1.isEMorphism

theorem IsIsometricEmbedding.strongMorphism {f : M → N} (hf : IsIsometricEmbedding d f) :
    StrongMorphism (flatCausality d M) (flatCausality d N) f := hf.1.strongMorphism

theorem IsIsometricEmbedding.localIsomorphism {f : M → N} (hf : IsIsometricEmbedding d f) :
    LocalIsomorphism (flatCausality d M) (flatCausality d N) f := hf.1.localIsomorphism

/-- **An isometric embedding is an isomorphism onto its image, on every open set**: for every
open `V` of `M` and `U = f(V)`, `x ≤_V y ↔ f x ≤_U f y` and `x ≪_V y ↔ f x ≪_U f y`. -/
theorem IsIsometricEmbedding.rel_iff {f : M → N} (hf : IsIsometricEmbedding d f) (V : Opens M)
    (U : Opens N) (hU : (U : Set N) = f '' V) (x y : M) :
    ((flatCausality d M).le V x y ↔ (flatCausality d N).le U (f x) (f y)) ∧
      ((flatCausality d M).lt V x y ↔ (flatCausality d N).lt U (f x) (f y)) := by
  have hmaps : MapsTo f V U := fun p hp => by rw [hU]; exact mem_image_of_mem f hp
  have hr := LocalIso.rel_of_image hf.localIsomorphism hf.2 flatCausality_absolutelyMinimalOn V U
    hU x y
  exact ⟨⟨hf.strongMorphism.le_of_mapsTo hmaps, hr.1⟩,
    ⟨hf.strongMorphism.lt_of_mapsTo hmaps, hr.2⟩⟩

variable (d) in
/-- **A flat Cauchy embedding**: an isometric embedding which is a Cauchy embedding of the flat
causalities (`IsCauchyEmbedding`, `Causal/CauchyExtension.lean`). -/
def IsFlatCauchyEmbedding (f : M → N) : Prop :=
  IsIsometricEmbedding d f ∧ IsCauchyEmbedding (flatCausality d M) (flatCausality d N) f

/-- A flat Cauchy embedding is an isometric embedding between GH spacetimes carrying some Cauchy
surface onto a Cauchy surface: the morphism and injectivity clauses of `IsCauchyEmbedding` are
automatic. -/
theorem isFlatCauchyEmbedding_iff {f : M → N} :
    IsFlatCauchyEmbedding d f ↔ IsIsometricEmbedding d f ∧
      (flatCausality d M).GloballyHyperbolic ∧ (flatCausality d N).GloballyHyperbolic ∧
      ∃ S : Set M, (flatCausality d M).IsCauchySurface S ∧
        (flatCausality d N).IsCauchySurface (f '' S) :=
  ⟨fun ⟨hf, hc⟩ => ⟨hf, hc.globallyHyperbolic_source, hc.globallyHyperbolic_target,
      hc.exists_cauchy⟩,
    fun ⟨hf, hM, hN, hS⟩ => ⟨hf, ⟨hM, hN, hf.isEMorphism, hf.2, hS⟩⟩⟩

/-- Barbot l.521–524: **the notion does not depend on the Cauchy hypersurface** — a flat Cauchy
embedding into a Hausdorff spacetime carries every Cauchy surface onto a Cauchy surface. -/
theorem IsFlatCauchyEmbedding.isCauchySurface_image [T2Space N] {f : M → N}
    (hf : IsFlatCauchyEmbedding d f) {S : Set M} (hS : (flatCausality d M).IsCauchySurface S) :
    (flatCausality d N).IsCauchySurface (f '' S) :=
  hf.2.isCauchySurface_image hS

end Causal

/-! ### Open subsets -/

section Opens

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (Minkowski d) M]
  [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))]

omit [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))] in
/-- The inclusion of an open subset is a local isometry (the charts of `W` are those of `M`,
restricted). -/
theorem isLocalIsometry_subtype_val (W : Opens M) :
    IsLocalIsometry d (Subtype.val : W → M) :=
  isLocalIsometry_iff_eventually.2 ⟨continuous_subtype_val, fun x => ⟨1,
    Eventually.of_forall fun y => by rw [one_smul]; rfl⟩⟩

omit [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))] in
/-- **The inclusion of an open subset is an isometric embedding.** -/
theorem isIsometricEmbedding_subtype_val (W : Opens M) :
    IsIsometricEmbedding d (Subtype.val : W → M) :=
  ⟨isLocalIsometry_subtype_val W, Subtype.val_injective⟩

/-- **The flat causality of an open subset is the restriction of the flat causality**: for
every open `V` of `W`, `x ≤_V y` in `W` iff `x ≤_V y` in `M`. -/
theorem flatCausality_opens (W : Opens M) :
    flatCausality d W = ((flatCausality d M).restrict W).toSubtype := by
  apply Causality.ext_toPrecausality
  ext V x y
  · exact ((isIsometricEmbedding_subtype_val W).rel_iff V (imageOpens V) rfl x y).1
  · exact ((isIsometricEmbedding_subtype_val W).rel_iff V (imageOpens V) rfl x y).2

end Opens

/-! ### The bundled structure -/

/-- **A flat spacetime** (Barbot l.484–490, BARBOT-THEOREMS §1): a connected Hausdorff
`(Isom(𝐌ⁿ), 𝐌ⁿ)`-manifold. Its causality is `flatCausality d M`. -/
structure FlatSpacetime (d : ℕ) : Type (u + 1) where
  /-- The underlying space. -/
  carrier : Type u
  [top : TopologicalSpace carrier]
  [t2 : T2Space carrier]
  [conn : ConnectedSpace carrier]
  [cs : ChartedSpace (Minkowski d) carrier]
  [gx : HasGroupoid carrier (gxGroupoid (isom d) (Minkowski d))]

namespace FlatSpacetime

instance : CoeSort (FlatSpacetime.{u} d) (Type u) := ⟨carrier⟩

attribute [instance] top t2 conn cs gx

/-- A flat spacetime is first countable: near each point it is a chart's domain, and the model
`𝐌ⁿ` is metrizable. -/
instance instFirstCountableTopology (M : FlatSpacetime.{u} d) : FirstCountableTopology M :=
  ⟨fun x => by
    rw [← (chartAt (Minkowski d) x).symm_map_nhds_eq (mem_chart_source (Minkowski d) x)]
    infer_instance⟩

/-- The flat spacetime of a type carrying the structure. -/
def of (M : Type u) [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [ChartedSpace (Minkowski d) M] [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))] :
    FlatSpacetime.{u} d :=
  ⟨M⟩

/-- **`𝐌ⁿ` itself**, with its one-chart atlas. -/
def minkowskiSpace (d : ℕ) : FlatSpacetime.{0} d := of (Minkowski d)

/-- **A connected open subset of a flat spacetime is a flat spacetime.** -/
noncomputable def ofOpens (M : FlatSpacetime.{u} d) (W : Opens M) (hW : IsConnected (W : Set M)) :
    FlatSpacetime.{u} d :=
  haveI : ConnectedSpace W := isConnected_iff_connectedSpace.1 hW
  of W

end FlatSpacetime

open FlatSpacetime

/-! ### Global hyperbolicity, maximality, absolute maximality -/

section Spacetimes

/-- **GH** (BARBOT-THEOREMS §1): ETT's global hyperbolicity of the flat causality — causal, with
compact diamonds. -/
def GH (M : FlatSpacetime.{u} d) : Prop := (flatCausality d M).GloballyHyperbolic

/-- **Barbot's GH** (l.500–509): the existence of a Cauchy surface (ETT's, DEC-14). -/
def BarbotGH (M : FlatSpacetime.{u} d) : Prop := ∃ S : Set M, (flatCausality d M).IsCauchySurface S

/-- **MGH** (l.525–527): GH, and every flat Cauchy embedding into a flat spacetime of the same
universe is surjective. -/
def MGH (M : FlatSpacetime.{u} d) : Prop :=
  GH M ∧ ∀ (N : FlatSpacetime.{u} d) (f : M → N), IsFlatCauchyEmbedding d f → Surjective f

/-- **Absolute maximality in the class `P`** (DEC-45): every isometric embedding into a GH flat
spacetime of class `P` (same dimension, same universe) is surjective. -/
def AbsMax (P : FlatSpacetime.{u} d → Prop) (M : FlatSpacetime.{u} d) : Prop :=
  ∀ N : FlatSpacetime.{u} d, GH N → P N → ∀ f : M → N, IsIsometricEmbedding d f → Surjective f

/-- **AMGH** (Rem 2.3, l.573–575), with Cauchy-completeness an abstract parameter `CC`: GH, of
class `CC`, and absolutely maximal in the class `CC`. -/
def AMGH (CC : FlatSpacetime.{u} d → Prop) (M : FlatSpacetime.{u} d) : Prop :=
  GH M ∧ CC M ∧ AbsMax CC M

/-- **Cauchy-compact** (l.560–565), topological form: a compact acausal Cauchy surface. -/
def CauchyCompact (M : FlatSpacetime.{u} d) : Prop :=
  ∃ S : Set M, (flatCausality d M).IsCauchySurface S ∧ IsCompact S ∧
    (flatCausality d M).IsAcausal S

theorem AbsMax.mono {P Q : FlatSpacetime.{u} d → Prop} (hPQ : ∀ N, P N → Q N)
    {M : FlatSpacetime.{u} d} (h : AbsMax Q M) : AbsMax P M :=
  fun N hN hP f hf => h N hN (hPQ N hP) f hf

theorem AMGH.gh {CC : FlatSpacetime.{u} d → Prop} {M : FlatSpacetime.{u} d} (h : AMGH CC M) :
    GH M := h.1

theorem AMGH.absMax {CC : FlatSpacetime.{u} d → Prop} {M : FlatSpacetime.{u} d}
    (h : AMGH CC M) : AbsMax CC M := h.2.2

/-- **Absolutely maximal among all targets ⇒ maximal**: a flat Cauchy embedding is an isometric
embedding into a GH spacetime. -/
theorem MGH.of_absMax {M : FlatSpacetime.{u} d} (hM : GH M) (h : AbsMax (fun _ => True) M) :
    MGH M :=
  ⟨hM, fun N f hf => h N hf.2.globallyHyperbolic_target trivial f hf.1⟩

/-- **GH ⇒ Barbot's GH**, through `geroch_i_imp_iii` (`Causal/Geroch.lean`), under its
hypotheses on the flat causality, carried here as named hypotheses: a pair of admissible
measures, the tarentin property, causal arc-connectedness, `J^±(p) ≠ {p}`, first countability
(metrizability read weakly; first countability is not carried, it is
`FlatSpacetime.instFirstCountableTopology`, from the charts). The converse is `theo:geroch`'s
cited (iii) ⇒ (i) (`CausalScaffold.GerochEquiv`, one `sorry`), not imported here. -/
theorem barbotGH_of_gh {M : FlatSpacetime.{u} d} [MeasurableSpace M]
    [BorelSpace M] {μp μm : MeasureTheory.Measure M}
    (hμp : (flatCausality d M).AdmissibleFuture μp) (hμm : (flatCausality d M).AdmissiblePast μm)
    (hT : (flatCausality d M).Tarentin) (hC : (flatCausality d M).CausallyArcConnected)
    (hJm : ∀ p : M, (flatCausality d M).Jminus ⊤ {p} ≠ {p})
    (hJp : ∀ p : M, (flatCausality d M).Jplus ⊤ {p} ≠ {p}) (hG : GH M) : BarbotGH M :=
  ⟨_, Causality.geroch_i_imp_iii hμp hμm hT hC hJm hJp hG⟩

theorem CauchyCompact.barbotGH {M : FlatSpacetime.{u} d} (h : CauchyCompact M) : BarbotGH M :=
  let ⟨S, hS, _⟩ := h; ⟨S, hS⟩

/-- **The acausal conjunct of `CauchyCompact` is redundant** under causal arc-connectedness and
`CurvesExtend` (`IsCauchySurface.isAcausal`, `Causal/CauchyExtension.lean`): a causal curve from
`x ≤ y` on a Cauchy surface, extended to an inextensible one, would meet it twice. Neither
hypothesis is proved here for a general flat spacetime. -/
theorem CauchyCompact.of_isCauchySurface {M : FlatSpacetime.{u} d}
    (hC : (flatCausality d M).CausallyArcConnected) (hext : (flatCausality d M).CurvesExtend)
    {S : Set M} (hS : (flatCausality d M).IsCauchySurface S) (hK : IsCompact S) :
    CauchyCompact M :=
  ⟨S, hS, hK, hS.isAcausal hC hext⟩

/-- The identity of a GH flat spacetime with a Cauchy surface is a flat Cauchy embedding. -/
theorem isFlatCauchyEmbedding_id {M : FlatSpacetime.{u} d} (hM : GH M) (hB : BarbotGH M) :
    IsFlatCauchyEmbedding d (id : M → M) := by
  obtain ⟨S, hS⟩ := hB
  exact ⟨isIsometricEmbedding_id, hM, hM, IsEMorphism.id, injective_id, S, hS, by rwa [image_id]⟩

end Spacetimes

/-! ### Minkowski space -/

section Minkowski

/-- The flat causality of `minkowskiSpace d` is `minkowski d`. -/
theorem flatCausality_minkowskiSpace :
    flatCausality d (minkowskiSpace d) = minkowski d :=
  flatCausality_self

/-- **`𝐌ⁿ` is GH.** -/
theorem gh_minkowskiSpace : GH (minkowskiSpace d) := by
  show (flatCausality d (Minkowski d)).GloballyHyperbolic
  rw [flatCausality_self]
  exact minkowski_globallyHyperbolic

/-- **`𝐌ⁿ` is GH in Barbot's sense**: the slice `t = 0` is a Cauchy surface. -/
theorem barbotGH_minkowskiSpace : BarbotGH (minkowskiSpace d) := by
  refine ⟨graph fun _ => (0 : ℝ), ?_⟩
  show (flatCausality d (Minkowski d)).IsCauchySurface _
  rw [flatCausality_self]
  exact isCauchySurface_graph_zero

/-- **Every isometry of `𝐌ⁿ` is an isometric embedding** (and surjective). -/
theorem isIsometricEmbedding_smul (g : isom d) :
    IsIsometricEmbedding d (fun p : Minkowski d => g • p) :=
  ⟨isLocalIsometry_iff_eventually.2 ⟨continuous_const_smul g, fun _ => ⟨g,
    Eventually.of_forall fun _ => by simp⟩⟩, MulAction.injective g⟩

/-- The open future timelike cone `{t > ‖x‖}` of `𝐌ⁿ` (Rem 2.2's `Ω`, the future component of
`{Q < 0}`, `connectedComponentIn_of_fst_pos` in `Flat.Achronal`), as an open set. -/
def futureTimelikeCone (d : ℕ) : Opens (Minkowski d) :=
  ⟨{p | IsFutureTimelike p}, (isOpen_lt continuous_const continuous_fst).inter
    (isOpen_lt continuous_minkQ continuous_const)⟩

theorem isConnected_futureTimelikeCone :
    IsConnected (futureTimelikeCone d : Set (Minkowski d)) :=
  convex_isFutureTimelike.isConnected ⟨_, isFutureTimelike_vertical⟩

/-- The future timelike cone, as a flat spacetime. -/
noncomputable def futureTimelikeConeSpace (d : ℕ) : FlatSpacetime.{0} d :=
  ofOpens (minkowskiSpace d) (futureTimelikeCone d) isConnected_futureTimelikeCone

/-- **Rem 2.2's first sentence, in the absolute form** (l.538–543: "MGH spacetimes may admit
nonsurjective isometric embeddings in bigger MGH spacetimes"): the future cone sits in `𝐌ⁿ`, a
GH flat spacetime, by a non-surjective isometric embedding, so it is **not** absolutely maximal
among all GH targets. Its maximality, which the remark also asserts, is not proved here. -/
theorem not_absMax_futureTimelikeConeSpace :
    ¬ AbsMax (fun _ => True) (futureTimelikeConeSpace d) := by
  intro h
  obtain ⟨⟨p, hp⟩, rfl⟩ := h (minkowskiSpace d) gh_minkowskiSpace trivial
    (Subtype.val : futureTimelikeCone d → Minkowski d)
    (isIsometricEmbedding_subtype_val (futureTimelikeCone d)) (0 : Minkowski d)
  exact lt_irrefl _ hp.1

end Minkowski

end Causal.Flat
