import CausalScaffold.Flat.Nonloxodromic
import CausalScaffold.Flat.TitsNull
import CausalScaffold.Flat.Loxodromic
import CausalScaffold.CompactCauchy
import CausalScaffold.CurvesExtend
import CausalScaffold.Flat.Cla.LocallyCauchy

/-!
# `CausalScaffold.Flat.Cla.CoverMGH` — a finite cover of a maximal Cauchy-compact GH flat spacetime is GH, Cauchy-compact, maximal, and absolutely maximal

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), proof of
Theorem B (`bthm:cauclo`, l.3535–3548 of `papers/barbot/legacy/labeled/GHFspace.tex`) and §11.3
(ii) (l.3572–3581). **No label is marked**: this module proves steps (1)–(3) of
`Flat/Classification.lean`'s `cauclo_from_embedding` (the finite cover `M'` is GH,
Cauchy-compact and maximal; every isometric embedding of it into a GH spacetime is onto a
Cauchy-compact one) up to **one** tagged `sorry`, the maximality of `M'` (finding 2).

* `mgh_cauchyCompact_of_isFiniteCover` — the statement, **assembled, one upstream `sorry`**
  (`maximal_of_isFiniteCover`: every flat Cauchy embedding of `M'` is onto; finding 2).
* **Proved, no `sorry`:** **GH lifts along a finite cover** (`gh_of_isFiniteCover`): causality
  (`isCausal_of_isLocalIsometry`, through `eq_of_le_of_apply_eq`) and **compact diamonds**
  (`isCompact_diamond_of_isFiniteCover`: `J(x', y')` is a closed subset of the compact
  `p⁻¹(J(p x', p y'))` — by a finite-chain argument over finitely many evenly covered causally
  convex opens, no limit curve); **Cauchy-compactness lifts** (`cauchyCompact_of_isFiniteCover`:
  the preimage of a compact set under a covering with finite fibres is compact,
  `isCompact_preimage_of_isCoveringMap`; acausality lifts, `isAcausal_preimage`; Develop's
  `isCauchySurface_preimage`); a Cauchy surface of a causal flat spacetime is connected
  (`isConnected_of_isCauchySurface`); and the last conjunct (every isometric embedding
  `f : M' → B`, `B` GH, is onto and `B` Cauchy-compact) **from** `MGH M'`, lemma K (`hK`) and L8
  (`LocallyCauchy`).

> A fundamental observation is that in a GH spacetime, every closed spacelike hypersurface is
> necessarely a Cauchy surface, hence, every GH spacetime containing an embedded copy of $M$ is
> necessarely Cauchy-compact. (l.3536–3540)

> Actually, (ii) follows from (i), since, as noted previously, closed spacelike hypersurfaces in
> GH spacetimes are always Cauchy hypersurfaces. In other words, maximal Cauchy-compact GH
> spacetimes are also absolutely maximal. (l.3578–3581)

> In remark \ref{defdep}, we claimed that for maximal Cauchy-compact spacetimes,
> $\Omega(\widetilde{S})$ is the Cauchy domain of $\widetilde{S}$. (l.3552–3554)

> Now, a globally hyperbolic manifold $M$ is said maximal if any Cauchy embedding of $M$ into some
> globally hyperbolic spacetime $N$ is necessarly surjective. (l.525–527)

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; `Minkowski d` has `d` spatial
dimensions: Barbot's `n` is `d + 1`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `M` GH, Cauchy-compact, maximal (l.3536, l.3573) | ✓ carried: `GH M`, `CauchyCompact M`, `MGH M` |
| `M'` a finite covering of `M` (l.3573 "finite quotient"; l.355 "up to finite coverings") | ✓ carried: `IsFiniteCover d p` (covering map, local isometry, finite fibres) |
| "closed spacelike hypersurfaces in GH spacetimes are Cauchy" (l.3537–3538, l.3579–3580) | ⚠ strengthened (DEC-44): lemma K in conclusion form `hK`, over `FlatSpacetime.{0}` — compact, connected and locally Cauchy two-sided ⇒ Cauchy; Classification derives it from `FlatLemmaKData` exactly as in `absMax_of_cauchyCompact_of_mgh` |
| the embedded copy of the Cauchy surface is a spacelike hypersurface | L8 (`CausalScaffold.Flat.Cla.LocallyCauchy`): the image of a compact acausal Cauchy surface under an isometric embedding is locally Cauchy two-sided |
| GH of the cover (used silently, l.3573) | ✓ proved (`gh_of_isFiniteCover`), not assumed |
| maximality of `M'` (not in the paper: finding 2) | ⚠ the one `sorry` (SCOPE) |
| universes | `M` in any universe; `M'`, the targets of `MGH M'` and `B` in `Type` (as `hK` and `cauclo_from_embedding`); `isCompact_diamond_of_isFiniteCover` in any two universes |

## SCOPE (disclosed)

* **The one `sorry`** is `maximal_of_isFiniteCover`: every flat Cauchy embedding `g : M' → N'`
  is onto (finding 2: the paper never states it; it says "up to finite coverings" and uses the
  maximality of the cover silently, l.3573–3581). It is the descent of a Cauchy extension of `M'`
  to one of `M`, which needs either the uniqueness of maximal Cauchy developments (gx's CBG,
  DEC-29) or Rem `dependance` (l.3552: the developing map of a maximal Cauchy-compact `M` is a
  homeomorphism of `M̃` onto the domain of dependence `int D(Σ)` of `Σ = 𝒟(S̃)`). Neither is in
  the library; the precise obstruction is at the `sorry`.
* Everything else is proved: all of `GH M'` (causality and compact diamonds), all of
  `CauchyCompact M'`, and the last conjunct from `MGH M'`, `hK` and L8.
* `MGH M` is used by nothing proved; it enters only the `sorry` (with a universe transport from
  `Type` to `M`'s universe, `MGH M` quantifying over targets in `M`'s universe).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal.Flat.Cla

open Set Function Filter Topology TopologicalSpace

universe u v

variable {d : ℕ}

/-! ## §1 Local isometries reflect causality -/

section Lift

variable {E : Type*} [TopologicalSpace E] [ChartedSpace (Minkowski d) E]
  [HasGroupoid E (gxGroupoid (isom d) (Minkowski d))]
  {X : Type*} [TopologicalSpace X] [ChartedSpace (Minkowski d) X]
  [HasGroupoid X (gxGroupoid (isom d) (Minkowski d))] {p : E → X}

/-- A local isometry pushes the causal order forward. -/
theorem le_apply_of_isLocalIsometry (hloc : IsLocalIsometry d p) {a b : E}
    (h : (flatCausality d E).le ⊤ a b) : (flatCausality d X).le ⊤ (p a) (p b) :=
  hloc.strongMorphism.le_of_mapsTo (U := ⊤) (V := ⊤) (fun _ _ => trivial) h

/-- **Two causally related points with the same image under a local isometry into a causal
spacetime are equal.** The relation `a ≤ b` is a chain of relations inside open sets on which
`p` is injective (absolute minimality of the flat causality); every intermediate point `c` lies
between `p a` and `p b = p a` downstairs, so `p c = p a` (causality), and the first step of the
chain does not move (injectivity on its sheet). No covering property is used. -/
theorem eq_of_le_of_apply_eq (hloc : IsLocalIsometry d p) (hX : (flatCausality d X).IsCausal)
    {a b : E} (h : (flatCausality d E).le ⊤ a b) (hab : p a = p b) : a = b := by
  let S : Set (Opens E) := {U | InjOn p U}
  have hS : ∀ z ∈ (⊤ : Opens E), ∃ O ∈ S, z ∈ O := by
    intro z _
    obtain ⟨e, hz, he⟩ := hloc.isLocalHomeomorph z
    exact ⟨⟨e.source, e.open_source⟩, show InjOn p e.source by rw [he]; exact e.injOn, hz⟩
  have hch := ((Precausality.absolutelyMinimal_iff.1
    (flatCausality_absolutelyMinimal (d := d) (M := E))) S hS ⊤ le_rfl a b).1 h
  have step : ∀ {c : E}, (∃ O ∈ S, (flatCausality d E).le (⊤ ⊓ O) a c) →
      (flatCausality d E).le ⊤ c b → c = a := by
    rintro c ⟨O, hO, hle⟩ hc
    have hle' := (flatCausality d E).le_mono inf_le_right hle
    have h1 := le_apply_of_isLocalIsometry hloc ((flatCausality d E).le_mono le_top hle')
    have h2 := le_apply_of_isLocalIsometry hloc hc
    rw [← hab] at h2
    exact hO ((flatCausality d E).le_mem_right hle') ((flatCausality d E).le_mem_left hle')
      (hX h2 h1)
  have key : ∀ {c : E},
      Relation.TransGen (fun x y => ∃ O ∈ S, (flatCausality d E).le (⊤ ⊓ O) x y) a c →
      (flatCausality d E).le ⊤ c b → c = a := by
    intro c hac
    induction hac with
    | single hx => exact step hx
    | tail _ hbc ih =>
      intro hc
      obtain ⟨O, hO, hle⟩ := hbc
      have hb : (flatCausality d E).le ⊤ _ b := (flatCausality d E).le_trans
        ((flatCausality d E).le_mono le_top hle) hc
      have := ih hb
      subst this
      exact step ⟨O, hO, hle⟩ hc
  exact (key hch ((flatCausality d E).le_refl (show b ∈ (⊤ : Opens E) from trivial))).symm

/-- **Causality lifts along a local isometry**: a causal loop `a ≤ b ≤ a` projects to one, so
`p a = p b`, and `eq_of_le_of_apply_eq` closes. -/
theorem isCausal_of_isLocalIsometry (hloc : IsLocalIsometry d p)
    (hX : (flatCausality d X).IsCausal) : (flatCausality d E).IsCausal :=
  fun _ _ hab hba => eq_of_le_of_apply_eq hloc hX hab
    (hX (le_apply_of_isLocalIsometry hloc hab) (le_apply_of_isLocalIsometry hloc hba))

/-- **Acausality lifts along a local isometry**: two related points of `p⁻¹(S)` project to two
related, hence equal, points of `S`. -/
theorem isAcausal_preimage (hloc : IsLocalIsometry d p) (hX : (flatCausality d X).IsCausal)
    {S : Set X} (hS : (flatCausality d X).IsAcausal S) :
    (flatCausality d E).IsAcausal (p ⁻¹' S) :=
  fun _ ha _ hb hab => eq_of_le_of_apply_eq hloc hX hab
    (hS _ ha _ hb (le_apply_of_isLocalIsometry hloc hab))


/-- **A local isometry injective on an open `T` reflects the relations of `T`**: a relation of
`W = p(T)` between two images is one of `T` (`rel_iff` for the isometric embedding
`p ∘ val : T → X`, transported to `E` along `val`). -/
theorem le_of_injOn (hloc : IsLocalIsometry d p) {T : Opens E} {W : Opens X}
    (hinj : InjOn p T) (hW : (W : Set X) = p '' T) {a b : E} (ha : a ∈ T) (hb : b ∈ T)
    (h : (flatCausality d X).le W (p a) (p b)) : (flatCausality d E).le T a b := by
  have hg : IsIsometricEmbedding d (p ∘ (Subtype.val : T → E)) :=
    ⟨hloc.comp (isLocalIsometry_subtype_val T), fun x y hxy => Subtype.ext (hinj x.2 y.2 hxy)⟩
  have hW' : (W : Set X) = (p ∘ (Subtype.val : T → E)) '' ((⊤ : Opens T) : Set T) := by
    rw [hW, Opens.coe_top, image_univ, range_comp, Subtype.range_coe]
  have h1 := ((hg.rel_iff ⊤ W hW' ⟨a, ha⟩ ⟨b, hb⟩).1).2 h
  have hT' : ((T : Opens E) : Set E) = (Subtype.val : T → E) '' ((⊤ : Opens T) : Set T) := by
    rw [Opens.coe_top, image_univ, Subtype.range_coe]
  exact (((isIsometricEmbedding_subtype_val T).rel_iff ⊤ T hT' ⟨a, ha⟩ ⟨b, hb⟩).1).1 h1

end Lift

/-! ## §2 A covering map with finite fibres has compact preimages of compact sets -/

section Proper

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}

/-- **The preimage of a compact set under a covering map with finite fibres is compact.** For an
ultrafilter `𝒰` on `p⁻¹(K)`, `p 𝒰` converges to some `w ∈ K`; over an evenly covered `U ∋ w`
the finitely many sheets partition `p⁻¹(U) ∈ 𝒰`, so one sheet `T` is in `𝒰`, and `𝒰` converges
to the point of `T` above `w` (`p` maps `T` homeomorphically onto `U`). -/
theorem isCompact_preimage_of_isCoveringMap (hp : IsCoveringMap p)
    (hfin : ∀ y, (p ⁻¹' {y}).Finite) {K : Set X} (hK : IsCompact K) :
    IsCompact (p ⁻¹' K) := by
  rw [isCompact_iff_ultrafilter_le_nhds]
  intro 𝒰 h𝒰
  have hmap : ((𝒰.map p : Ultrafilter X) : Filter X) ≤ 𝓟 K := by
    rw [Ultrafilter.coe_map]
    refine (Filter.map_mono h𝒰).trans ?_
    rw [map_principal]
    exact principal_mono.2 (image_preimage_subset p K)
  obtain ⟨w, hwK, hw⟩ := (isCompact_iff_ultrafilter_le_nhds.1 hK) _ hmap
  rw [Ultrafilter.coe_map] at hw
  obtain ⟨hdisc, U, hwU, hU, hpU, H, hH⟩ := hp w
  haveI : Finite (p ⁻¹' {w}) := (hfin w).to_subtype
  -- the sheets
  let T : (p ⁻¹' {w}) → Set E := fun i => Subtype.val '' {e : p ⁻¹' U | (H e).2 = i}
  have hUmem : p ⁻¹' U ∈ 𝒰 := hw (hU.mem_nhds hwU)
  have hcover : p ⁻¹' U = ⋃ i ∈ (univ : Set (p ⁻¹' {w})), T i := by
    ext e
    rw [mem_iUnion₂]
    constructor
    · intro he
      exact ⟨(H ⟨e, he⟩).2, mem_univ _, ⟨e, he⟩, rfl, rfl⟩
    · rintro ⟨i, -, e', -, rfl⟩
      exact e'.2
  rw [hcover] at hUmem
  obtain ⟨i, -, hTi⟩ := (Ultrafilter.finite_biUnion_mem_iff finite_univ).1 hUmem
  -- the sheet `T i` is open and `p` is injective on it
  have hTopen : IsOpen (T i) := by
    refine hpU.isOpenMap_subtype_val _ ?_
    have : {e : p ⁻¹' U | (H e).2 = i} = (fun e => (H e).2) ⁻¹' {i} := rfl
    rw [this]
    exact (isOpen_discrete {i}).preimage (continuous_snd.comp H.continuous)
  have hTinj : InjOn p (T i) := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩ hee'
    have h1 : (H e).1 = (H e').1 := Subtype.ext (by rw [hH, hH]; exact hee')
    have h2 : (H e).2 = (H e').2 := by rw [show (H e).2 = i from he, show (H e').2 = i from he']
    have := H.injective (Prod.ext h1 h2)
    rw [this]
  -- the limit point
  set e₀ : E := (H.symm (⟨w, hwU⟩, i)).1 with he₀
  have hpe₀ : p e₀ = w := by
    have := hH (H.symm (⟨w, hwU⟩, i))
    rw [H.apply_symm_apply] at this
    exact this.symm
  have he₀T : e₀ ∈ T i := ⟨H.symm (⟨w, hwU⟩, i), by
    show (H (H.symm (⟨w, hwU⟩, i))).2 = i
    rw [H.apply_symm_apply], rfl⟩
  refine ⟨e₀, by rw [mem_preimage, hpe₀]; exact hwK, fun V hV => ?_⟩
  obtain ⟨V', hV'V, hV'o, he₀V'⟩ := mem_nhds_iff.1 hV
  have himg : p '' (V' ∩ T i) ∈ 𝓝 w := by
    rw [← hpe₀]
    exact (hp.isOpenMap _ (hV'o.inter hTopen)).mem_nhds ⟨e₀, ⟨he₀V', he₀T⟩, rfl⟩
  have h1 : p ⁻¹' (p '' (V' ∩ T i)) ∈ 𝒰 := hw himg
  refine Filter.mem_of_superset (Filter.inter_mem h1 hTi) ?_
  rintro e ⟨⟨e', ⟨he'V, he'T⟩, hpe⟩, heT⟩
  exact hV'V (hTinj he'T heT hpe ▸ he'V)

end Proper

/-! ## §2b The sheets of a covering map over an evenly covered open set -/

section Sheets

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}

/-- **The sheets over an evenly covered open set `W ∋ c`**, indexed by the fibre over `c`: open
sets covering `p⁻¹(W)`, pairwise disjoint, each mapped injectively onto `W`. -/
theorem exists_sheets_of_isCoveringMap (hp : IsCoveringMap p) (c : X) :
    ∃ W : Opens X, c ∈ W ∧ ∃ T : (p ⁻¹' {c}) → Opens E,
      (∀ e, p e ∈ W → ∃ i, e ∈ T i) ∧ (∀ i, InjOn p (T i)) ∧
      (∀ i, (W : Set X) = p '' (T i)) ∧ (∀ i j e, e ∈ T i → e ∈ T j → i = j) := by
  obtain ⟨hdisc, U, hcU, hU, hpU, H, hH⟩ := hp c
  refine ⟨⟨U, hU⟩, hcU, fun i => ⟨Subtype.val '' {e : p ⁻¹' U | (H e).2 = i}, ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine hpU.isOpenMap_subtype_val _ ?_
    have : {e : p ⁻¹' U | (H e).2 = i} = (fun e => (H e).2) ⁻¹' {i} := rfl
    rw [this]
    exact (isOpen_discrete {i}).preimage (continuous_snd.comp H.continuous)
  · intro e he
    exact ⟨(H ⟨e, he⟩).2, ⟨e, he⟩, rfl, rfl⟩
  · intro i
    rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩ hee'
    have h1 : (H e).1 = (H e').1 := Subtype.ext (by rw [hH, hH]; exact hee')
    have h2 : (H e).2 = (H e').2 := by
      rw [show (H e).2 = i from he, show (H e').2 = i from he']
    rw [H.injective (Prod.ext h1 h2)]
  · intro i
    ext v
    constructor
    · intro hv
      refine ⟨(H.symm (⟨v, hv⟩, i)).1, ⟨H.symm (⟨v, hv⟩, i), ?_, rfl⟩, ?_⟩
      · show (H (H.symm (⟨v, hv⟩, i))).2 = i
        rw [H.apply_symm_apply]
      · have := hH (H.symm (⟨v, hv⟩, i))
        rw [H.apply_symm_apply] at this
        exact this.symm
    · rintro ⟨_, ⟨e, -, rfl⟩, rfl⟩
      exact e.2
  · rintro i j _ ⟨e, he, rfl⟩ ⟨e', he', hee'⟩
    have : e' = e := Subtype.ext hee'
    subst this
    exact (show (H e').2 = i from he).symm.trans he'

end Sheets

/-! ## §2c Chains along a list of labels, and the shortcut -/

section Chains

variable {σ E : Type*}

/-- **A chain along a list of labels**: `a = c₀ R_{s₁} c₁ R_{s₂} ⋯ R_{sₖ} cₖ = b`. -/
def LabelChain (R : σ → E → E → Prop) : List σ → E → E → Prop
  | [], a, b => a = b
  | s :: l, a, b => ∃ c, R s a c ∧ LabelChain R l c b

theorem labelChain_append (R : σ → E → E → Prop) (l₁ l₂ : List σ) (a b : E) :
    LabelChain R (l₁ ++ l₂) a b ↔ ∃ c, LabelChain R l₁ a c ∧ LabelChain R l₂ c b := by
  induction l₁ generalizing a with
  | nil => simp [LabelChain]
  | cons s l ih =>
    simp only [List.cons_append, LabelChain, ih]
    constructor
    · rintro ⟨c, hc, e, he, he'⟩
      exact ⟨e, ⟨c, hc, he⟩, he'⟩
    · rintro ⟨e, ⟨c, hc, he⟩, he'⟩
      exact ⟨c, hc, e, he, he'⟩

/-- A chain of steps of a preorder-compatible family is a relation of the preorder. -/
theorem LabelChain.rel {R : σ → E → E → Prop} {Q : E → E → Prop} (hrefl : ∀ a, Q a a)
    (htrans : ∀ a b c, Q a b → Q b c → Q a c) (hR : ∀ s a b, R s a b → Q a b) :
    ∀ {l : List σ} {a b : E}, LabelChain R l a b → Q a b
  | [], a, _, h => h ▸ hrefl a
  | _ :: _, _, _, ⟨_, hc, h⟩ => htrans _ _ _ (hR _ _ _ hc) (LabelChain.rel hrefl htrans hR h)

/-- **The shortcut**: if two steps with the same label `s` can be merged whenever their outer
ends are related (`hshort`), a step followed by a chain with pairwise distinct labels is again a
chain with pairwise distinct labels. -/
theorem exists_nodup_labelChain {R : σ → E → E → Prop} {Q : E → E → Prop}
    (hrefl : ∀ a, Q a a) (htrans : ∀ a b c, Q a b → Q b c → Q a c)
    (hR : ∀ s a b, R s a b → Q a b)
    (hshort : ∀ s a b c e, R s a b → R s c e → Q a e → R s a e)
    {s : σ} {a c b : E} (hac : R s a c) {l : List σ} (hl : l.Nodup)
    (hcb : LabelChain R l c b) : ∃ l' : List σ, l'.Nodup ∧ LabelChain R l' a b := by
  by_cases hs : s ∈ l
  · obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hs
    obtain ⟨e, h₁, f, hef, h₂⟩ := (labelChain_append R l₁ (s :: l₂) c b).1 hcb
    have hQ : Q a f := htrans _ _ _
      (htrans _ _ _ (hR _ _ _ hac) (LabelChain.rel hrefl htrans hR h₁)) (hR _ _ _ hef)
    exact ⟨s :: l₂, hl.sublist (List.sublist_append_right _ _), f,
      hshort _ _ _ _ _ hac hef hQ, h₂⟩
  · exact ⟨s :: l, List.nodup_cons.2 ⟨hs, hl⟩, c, hac, hcb⟩

/-- Lists of bounded length over a finite type form a finite set (`List.finite_length_le`,
whose file this module does not import): a list of length `≤ N` is determined by its first `N`
optional entries. -/
theorem finite_length_le' (σ : Type*) [Finite σ] (N : ℕ) :
    {l : List σ | l.length ≤ N}.Finite := by
  have hinj : InjOn (fun l : List σ => fun i : Fin N => l[(i : ℕ)]?) {l | l.length ≤ N} := by
    intro l₁ h₁ l₂ h₂ h
    have h₁' : l₁.length ≤ N := h₁
    have h₂' : l₂.length ≤ N := h₂
    apply List.ext_getElem?
    intro n
    by_cases hn : n < N
    · exact congrFun h ⟨n, hn⟩
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  exact Set.Finite.of_finite_image (Set.toFinite _) hinj

end Chains

/-! ## §2d Compact diamonds of a finite cover -/

section Diamonds

/-- **The diamonds of a finite cover of a GH flat spacetime are compact.**
`J(x', y') ⊆ K = p⁻¹(J(p x', p y'))`, compact (`isCompact_preimage_of_isCoveringMap`); it remains
to see that a limit `z'` of points of `J(x', y')` lies in it. Over finitely many evenly covered
opens `W_c` (`exists_sheets_of_isCoveringMap`), with causally convex neighbourhoods
`V_c ⊆ W_c` (strong causality, `GloballyHyperbolic.stronglyCausal`) and opens `U_c` with
`closure U_c ⊆ V_c` covering
`J(p x', p y')`, a relation `x' ≤ e` with every intermediate point in `K` is a chain of steps in
the small sheets over the `U_c`, and one with **pairwise distinct** sheets
(`exists_nodup_labelChain`: two steps in one sheet merge, the sheet being causally convex in
`M'` because `V_c` is in `M`). There are finitely many such shapes (`finite_length_le'`), so
one shape carries the ultrafilter; the intermediate points converge in the compact `K`, and each
step passes to the limit: downstairs by closedness of `≤_M` (`GloballyHyperbolic.isClosed_le`),
then into `W_c` by convexity of `V_c`, then up into the sheet (`le_of_injOn`), the limits staying
in the same sheet because the sheets are open and disjoint. No limit curve is used. -/
theorem isCompact_diamond_of_isFiniteCover {M : FlatSpacetime.{u} d} {M' : FlatSpacetime.{v} d}
    {p : M' → M} (hGH : GH M) (hp : IsFiniteCover d p) (x y : M') :
    IsCompact ((flatCausality d M').diamond ⊤ x y) := by
  classical
  set C := flatCausality d M with hCdef
  set C' := flatCausality d M' with hC'def
  have hT : C.Tarentin := tarentin_flatCausality
  have hclosed : IsClosed {z : M × M | C.le ⊤ z.1 z.2} := hGH.isClosed_le hT
  have hSC : C.StronglyCausal := hGH.stronglyCausal hT
  have harc : C.CausallyArcConnected := flatCausality_causallyArcConnected d M
  have hpc : Continuous p := hp.isLocalIsometry.continuous
  have hmor : ∀ {a b : M'}, C'.le ⊤ a b → C.le ⊤ (p a) (p b) := fun h =>
    le_apply_of_isLocalIsometry hp.isLocalIsometry h
  haveI : ∀ c : M, Finite (p ⁻¹' {c}) := fun c => (hp.2.2 c).to_subtype
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (Minkowski d) M
  -- the local data at every point
  choose W hcW T hTcov hTinj hTimg hTdisj using
    exists_sheets_of_isCoveringMap hp.isCoveringMap
  have hV : ∀ c : M, ∃ V ∈ 𝓝 c, V ⊆ (W c : Set M) ∧ C.CausallyConvexIn V ⊤ := fun c =>
    hSC c _ ((W c).isOpen.mem_nhds (hcW c))
  choose V hVn hVW hVconv using hV
  have hU : ∀ c : M, ∃ U : Opens M, c ∈ U ∧ closure (U : Set M) ⊆ V c := by
    intro c
    obtain ⟨t, htn, htc, htV⟩ := exists_mem_nhds_isClosed_subset (hVn c)
    exact ⟨⟨interior t, isOpen_interior⟩, mem_interior_iff_mem_nhds.2 htn,
      (closure_minimal interior_subset htc).trans htV⟩
  choose U hcU hUV using hU
  have hUW : ∀ c, (U c : Set M) ⊆ W c := fun c =>
    subset_closure.trans ((hUV c).trans (hVW c))
  -- the compact sets
  set D := C.diamond ⊤ (p x) (p y) with hD
  have hDc : IsCompact D := hGH.2 _ _
  set K := p ⁻¹' D with hKdef
  have hKc : IsCompact K := isCompact_preimage_of_isCoveringMap hp.isCoveringMap hp.2.2 hDc
  obtain ⟨t, -, hDt⟩ := hDc.elim_nhds_subcover (fun c => (U c : Set M))
    (fun c _ => (U c).isOpen.mem_nhds (hcU c))
  -- the labels: a centre of `t` and a sheet over it
  let σ := Σ c : t, p ⁻¹' {(c : M)}
  haveI : Fintype σ := Fintype.ofFinite σ
  let B : σ → Opens M' := fun s => T s.1.1 s.2
  let Sm : σ → Opens M' := fun s =>
    B s ⊓ ⟨p ⁻¹' U s.1.1, (U s.1.1).isOpen.preimage hpc⟩
  let R : σ → M' → M' → Prop := fun s a b => a ∈ Sm s ∧ b ∈ Sm s ∧ C'.le (B s) a b
  have hRle : ∀ s a b, R s a b → C'.le ⊤ a b := fun _ _ _ h => C'.le_mono le_top h.2.2
  have hrefl : ∀ a : M', C'.le ⊤ a a := fun _ => C'.le_refl trivial
  have htrans : ∀ a b c : M', C'.le ⊤ a b → C'.le ⊤ b c → C'.le ⊤ a c :=
    fun _ _ _ h₁ h₂ => C'.le_trans h₁ h₂
  have hSmB : ∀ s a, a ∈ Sm s → a ∈ B s := fun _ _ h => (Opens.mem_inf.1 h).1
  have hSmU : ∀ s a, a ∈ Sm s → p a ∈ U s.1.1 := fun _ _ h => (Opens.mem_inf.1 h).2
  -- two points of one sheet related in `M'` are related in the sheet
  have hconvB : ∀ s a e, a ∈ Sm s → e ∈ Sm s → C'.le ⊤ a e → C'.le (B s) a e := by
    intro s a e ha he hae
    have hW : C.le (W s.1.1) (p a) (p e) :=
      Causality.le_of_causallyConvexIn harc (hVconv _) (hVW _)
        (hUV _ (subset_closure (hSmU s a ha))) (hUV _ (subset_closure (hSmU s e he))) (hmor hae)
    exact le_of_injOn hp.isLocalIsometry (hTinj _ _) (hTimg _ _) (hSmB s a ha) (hSmB s e he) hW
  have hshort : ∀ s a b c e, R s a b → R s c e → C'.le ⊤ a e → R s a e :=
    fun s a _ _ e hab hce hae => ⟨hab.1, hce.2.1, hconvB s a e hab.1 hce.2.1 hae⟩
  -- the small sheets cover `K`
  have hcov : ∀ z ∈ K, ∃ s, z ∈ Sm s := by
    intro z hz
    obtain ⟨c, hc, hzc⟩ := mem_iUnion₂.1 (hDt hz)
    obtain ⟨i, hi⟩ := hTcov c z (hUW c hzc)
    exact ⟨⟨⟨c, hc⟩, i⟩, Opens.mem_inf.2 ⟨hi, hzc⟩⟩
  -- (1) a relation with its intermediate points in `K` is a chain with distinct sheets
  have hchain : ∀ a b : M', C'.le ⊤ a b → (∀ z, C'.le ⊤ a z → C'.le ⊤ z b → z ∈ K) →
      ∃ l : List σ, l.Nodup ∧ LabelChain R l a b := by
    intro a b hab
    let S : Set (Opens M') := range Sm ∪ {⟨Kᶜ, hKc.isClosed.isOpen_compl⟩}
    have hS : ∀ z ∈ (⊤ : Opens M'), ∃ O ∈ S, z ∈ O := by
      intro z _
      by_cases hz : z ∈ K
      · obtain ⟨s, hs⟩ := hcov z hz
        exact ⟨Sm s, Or.inl ⟨s, rfl⟩, hs⟩
      · exact ⟨_, Or.inr rfl, hz⟩
    have htg := ((Precausality.absolutelyMinimal_iff.1
      (flatCausality_absolutelyMinimal (d := d) (M := M'))) S hS ⊤ le_rfl a b).1 hab
    have hle : ∀ {u w : M'}, (∃ O ∈ S, C'.le (⊤ ⊓ O) u w) → C'.le ⊤ u w :=
      fun ⟨_, _, h⟩ => C'.le_mono inf_le_left h
    have hTG : ∀ {u w : M'}, Relation.TransGen (fun u w => ∃ O ∈ S, C'.le (⊤ ⊓ O) u w) u w →
        C'.le ⊤ u w := by
      intro u w h
      induction h with
      | single h => exact hle h
      | tail _ h ih => exact C'.le_trans ih (hle h)
    have hstep : ∀ {u w : M'}, u ∈ K → (∃ O ∈ S, C'.le (⊤ ⊓ O) u w) → ∃ s, R s u w := by
      rintro u w hu ⟨O, hO, h⟩
      have h' := C'.le_mono inf_le_right h
      rcases hO with ⟨s, rfl⟩ | hO
      · exact ⟨s, C'.le_mem_left h', C'.le_mem_right h', C'.le_mono inf_le_left h'⟩
      · rw [mem_singleton_iff] at hO
        subst hO
        exact absurd hu (C'.le_mem_left h')
    clear hab
    induction htg using Relation.TransGen.head_induction_on with
    | single h =>
      intro hK
      obtain ⟨s, hs⟩ := hstep (hK _ (hrefl _) (hle h)) h
      exact ⟨[s], List.nodup_singleton s, b, hs, rfl⟩
    | head h' h ih =>
      intro hK
      obtain ⟨s, hs⟩ := hstep (hK _ (hrefl _) (C'.le_trans (hle h') (hTG h))) h'
      obtain ⟨l, hl, hch⟩ := ih fun z hz₁ hz₂ => hK z (C'.le_trans (hle h') hz₁) hz₂
      exact exists_nodup_labelChain hrefl htrans hRle hshort hs hl hch
  -- (2) one step passes to the limit
  have hlim1 : ∀ (s : σ) (F G : M' → M') (𝒰 : Ultrafilter M') (u w : M'),
      Tendsto F 𝒰 (𝓝 u) → Tendsto G 𝒰 (𝓝 w) → (∀ᶠ e in (𝒰 : Filter M'), R s (F e) (G e)) →
      C'.le ⊤ u w := by
    intro s F G 𝒰 u w hF hG hR
    have hsheet : ∀ (H : M' → M') (z : M'), Tendsto H 𝒰 (𝓝 z) → p z ∈ W s.1.1 →
        (∀ᶠ e in (𝒰 : Filter M'), H e ∈ B s) → z ∈ B s := by
      intro H z hH hz hHT
      obtain ⟨j, hj⟩ := hTcov _ z hz
      have hev : ∀ᶠ e in (𝒰 : Filter M'), H e ∈ T s.1.1 j := hH ((T _ j).isOpen.mem_nhds hj)
      obtain ⟨e, he1, he2⟩ := (hHT.and hev).exists
      have hij := hTdisj _ s.2 j (H e) he1 he2
      show z ∈ T s.1.1 s.2
      rw [hij]
      exact hj
    have hu1 : p u ∈ closure (U s.1.1 : Set M) :=
      mem_closure_of_tendsto ((hpc.tendsto u).comp hF) (hR.mono fun e he => hSmU s _ he.1)
    have hw1 : p w ∈ closure (U s.1.1 : Set M) :=
      mem_closure_of_tendsto ((hpc.tendsto w).comp hG) (hR.mono fun e he => hSmU s _ he.2.1)
    have huB := hsheet F u hF (hVW _ (hUV _ hu1)) (hR.mono fun e he => hSmB s _ he.1)
    have hwB := hsheet G w hG (hVW _ (hUV _ hw1)) (hR.mono fun e he => hSmB s _ he.2.1)
    have hlimD : C.le ⊤ (p u) (p w) :=
      hclosed.mem_of_tendsto (((hpc.tendsto u).comp hF).prodMk_nhds ((hpc.tendsto w).comp hG))
        (hR.mono fun e he => hmor (hRle s _ _ he))
    have hW : C.le (W s.1.1) (p u) (p w) :=
      Causality.le_of_causallyConvexIn harc (hVconv _) (hVW _) (hUV _ hu1) (hUV _ hw1) hlimD
    exact C'.le_mono le_top (le_of_injOn hp.isLocalIsometry (hTinj _ _) (hTimg _ _) huB hwB hW)
  -- (3) a chain of a fixed shape passes to the limit
  have hlim : ∀ (l : List σ) (F G : M' → M') (𝒰 : Ultrafilter M') (u v : M'),
      Tendsto F 𝒰 (𝓝 u) → Tendsto G 𝒰 (𝓝 v) →
      (∀ᶠ e in (𝒰 : Filter M'), LabelChain R l (F e) (G e)) →
      (∀ᶠ e in (𝒰 : Filter M'), ∀ z, C'.le ⊤ (F e) z → C'.le ⊤ z (G e) → z ∈ K) →
      C'.le ⊤ u v := by
    intro l
    induction l with
    | nil =>
      intro F G 𝒰 u v hF hG hch _
      have hG' : Tendsto F 𝒰 (𝓝 v) := hG.congr' (hch.mono fun e he => he.symm)
      rw [tendsto_nhds_unique hF hG']
      exact hrefl v
    | cons s l ih =>
      intro F G 𝒰 u v hF hG hch hK
      let c' : M' → M' := fun e =>
        if h : ∃ c, R s (F e) c ∧ LabelChain R l c (G e) then h.choose else e
      have hc' : ∀ᶠ e in (𝒰 : Filter M'), R s (F e) (c' e) ∧ LabelChain R l (c' e) (G e) :=
        hch.mono fun e he => by
          have hce : c' e = he.choose := dif_pos he
          rw [hce]
          exact he.choose_spec
      have hcK : ∀ᶠ e in (𝒰 : Filter M'), c' e ∈ K := (hc'.and hK).mono
        fun e ⟨⟨h1, h2⟩, h3⟩ => h3 _ (hRle _ _ _ h1) (LabelChain.rel hrefl htrans hRle h2)
      obtain ⟨w, -, hw⟩ := (isCompact_iff_ultrafilter_le_nhds.1 hKc) (𝒰.map c')
        (by rw [Ultrafilter.coe_map, le_principal_iff]; exact hcK)
      have hw' : Tendsto c' 𝒰 (𝓝 w) := by
        rw [Ultrafilter.coe_map] at hw
        exact hw
      have h1 := hlim1 s F c' 𝒰 u w hF hw' (hc'.mono fun e he => he.1)
      have h2 := ih c' G 𝒰 w v hw' hG (hc'.mono fun e he => he.2) ((hc'.and hK).mono
        fun e ⟨⟨h1, _⟩, h3⟩ z hz1 hz2 => h3 z (C'.le_trans (hRle _ _ _ h1) hz1) hz2)
      exact C'.le_trans h1 h2
  -- (4) finitely many shapes
  have hfinite : ∀ (P : List σ → M' → Prop) (𝒰 : Ultrafilter M'),
      (∀ᶠ e in (𝒰 : Filter M'), ∃ l : List σ, l.Nodup ∧ P l e) →
      ∃ l : List σ, ∀ᶠ e in (𝒰 : Filter M'), P l e := by
    intro P 𝒰 h
    have hL : {l : List σ | l.length ≤ Fintype.card σ}.Finite := finite_length_le' σ _
    have hmem : (⋃ l ∈ {l : List σ | l.length ≤ Fintype.card σ}, {e | P l e}) ∈ 𝒰 :=
      Filter.mem_of_superset h fun e ⟨l, hl, hP⟩ =>
        mem_iUnion₂.2 ⟨l, show l.length ≤ Fintype.card σ from hl.length_le_card, hP⟩
    obtain ⟨l, -, hl⟩ := (Ultrafilter.finite_biUnion_mem_iff hL).1 hmem
    exact ⟨l, hl⟩
  -- (5) the limit of an ultrafilter on the diamond lies in the diamond
  have hDK : C'.diamond ⊤ x y ⊆ K := fun z hz => by
    obtain ⟨h1, h2⟩ := Causality.mem_diamond.1 hz
    exact Causality.mem_diamond.2 ⟨hmor h1, hmor h2⟩
  rw [isCompact_iff_ultrafilter_le_nhds]
  intro 𝒰 h𝒰
  obtain ⟨z, -, hz⟩ := (isCompact_iff_ultrafilter_le_nhds.1 hKc) 𝒰
    (h𝒰.trans (principal_mono.2 hDK))
  refine ⟨z, ?_, hz⟩
  have hev : ∀ᶠ e in (𝒰 : Filter M'), e ∈ C'.diamond ⊤ x y := le_principal_iff.1 h𝒰
  have hzid : Tendsto id 𝒰 (𝓝 z) := tendsto_id.mono_left hz
  have hxz : C'.le ⊤ x z := by
    have hK1 : ∀ᶠ e in (𝒰 : Filter M'), ∀ w, C'.le ⊤ x w → C'.le ⊤ w e → w ∈ K :=
      hev.mono fun e he w h1 h2 => Causality.mem_diamond.2
        ⟨hmor h1, C.le_trans (hmor h2) (hmor (Causality.mem_diamond.1 he).2)⟩
    obtain ⟨l, hl⟩ := hfinite (fun l e => LabelChain R l x e) 𝒰
      ((hev.and hK1).mono fun e ⟨he, hK⟩ => hchain x e (Causality.mem_diamond.1 he).1 hK)
    exact hlim l (fun _ => x) id 𝒰 x z tendsto_const_nhds hzid hl hK1
  have hzy : C'.le ⊤ z y := by
    have hK1 : ∀ᶠ e in (𝒰 : Filter M'), ∀ w, C'.le ⊤ e w → C'.le ⊤ w y → w ∈ K :=
      hev.mono fun e he w h1 h2 => Causality.mem_diamond.2
        ⟨C.le_trans (hmor (Causality.mem_diamond.1 he).1) (hmor h1), hmor h2⟩
    obtain ⟨l, hl⟩ := hfinite (fun l e => LabelChain R l e y) 𝒰
      ((hev.and hK1).mono fun e ⟨he, hK⟩ => hchain e y (Causality.mem_diamond.1 he).2 hK)
    exact hlim l id (fun _ => y) 𝒰 z y hzid tendsto_const_nhds hl hK1
  exact Causality.mem_diamond.2 ⟨hxz, hzy⟩

end Diamonds

/-! ## §3 GH, Cauchy-compactness and maximality lift along a finite cover -/

section Cover

variable {M : FlatSpacetime.{u} d} {M' : FlatSpacetime.{0} d} {p : M' → M}

/-- **A finite cover of a causal flat spacetime is causal.** -/
theorem isCausal_of_isFiniteCover (hGH : GH M) (hp : IsFiniteCover d p) :
    (flatCausality d M').IsCausal :=
  isCausal_of_isLocalIsometry hp.isLocalIsometry hGH.1

/-- **A finite cover of a GH flat spacetime is GH**: causal (`isCausal_of_isFiniteCover`), with
compact diamonds (`isCompact_diamond_of_isFiniteCover`). -/
theorem gh_of_isFiniteCover (hGH : GH M) (hp : IsFiniteCover d p) : GH M' :=
  ⟨isCausal_of_isFiniteCover hGH hp, isCompact_diamond_of_isFiniteCover hGH hp⟩

/-- **Cauchy-compactness lifts along a finite cover**: `p⁻¹(S)` is compact
(`isCompact_preimage_of_isCoveringMap`), Cauchy (`isCauchySurface_preimage`: inextensible causal
curves project to inextensible ones) and acausal (`isAcausal_preimage`). -/
theorem cauchyCompact_of_isFiniteCover (hGH : GH M) (hC : CauchyCompact M)
    (hp : IsFiniteCover d p) : CauchyCompact M' := by
  obtain ⟨S, hS, hSc, hSac⟩ := hC
  exact ⟨p ⁻¹' S, isCauchySurface_preimage hp.isCoveringMap hp.isLocalIsometry hGH.1 hS,
    isCompact_preimage_of_isCoveringMap hp.isCoveringMap hp.2.2 hSc,
    isAcausal_preimage hp.isLocalIsometry hGH.1 hSac⟩

/-- **A Cauchy surface of a causal flat spacetime is connected** (through the splitting
`S × ℝ ≃ₜ N` along it: `flat_exists_isCauchySplitting` with the chronal causal flow of every
flat spacetime, `flat_hasChronalCausalFlow`; `N` is connected). -/
theorem isConnected_of_isCauchySurface {N : FlatSpacetime.{u} d}
    (hcaus : (flatCausality d N).IsCausal) {S : Set N}
    (hS : (flatCausality d N).IsCauchySurface S) (hac : (flatCausality d N).IsAcausal S) :
    IsConnected S := by
  have hflow : (flatCausality d N).HasChronalCausalFlow := flat_hasChronalCausalFlow
  obtain ⟨ψ, -⟩ := flat_exists_isCauchySplitting hflow hcaus hS hac
  haveI : ConnectedSpace (S × ℝ) := ψ.symm.surjective.connectedSpace ψ.symm.continuous
  haveI : Nonempty S := by
    obtain ⟨m⟩ : Nonempty N := inferInstance
    exact ⟨(ψ.symm m).1⟩
  haveI : ConnectedSpace S := (Prod.fst_surjective (β := ℝ)).connectedSpace continuous_fst
  simpa using isConnected_range (continuous_subtype_val (p := (· ∈ S)))

/-- **Maximality of a finite cover** (finding 2): every flat Cauchy embedding of `M'` is onto.
The paper never states it (it says "up to finite coverings" and uses the maximality of the cover
silently, l.3573–3581). -/
theorem maximal_of_isFiniteCover (hGH : GH M) (hC : CauchyCompact M) (hM : MGH M)
    (hp : IsFiniteCover d p) :
    ∀ (N : FlatSpacetime.{0} d) (g : M' → N), IsFlatCauchyEmbedding d g → Surjective g := by
  sorry -- SORRY(bthm:cauclo, finding 2): descent of a Cauchy extension `g : M' → N'` of the cover to one of `M`, not in the library. Route: pass to the Galois core `M'' → M` (normal core of the finite-index `p_*π₁M'` in `π₁M`; finite deck group `G`; the composition of finite covers is not in mathlib at this pin), extend `G` to the Cauchy development `N''` of `M''` — either by the uniqueness of maximal Cauchy developments (gx's CBG, DEC-29, not graduated) or flatly: lift `g` to universal covers with `𝒟_{N''} ∘ g̃ = 𝒟_M` after normalisation (no lifting lemma for flat Cauchy embeddings to universal covers is in Develop), show `𝒟(Ñ'') ⊆ int D(Σ)` for `Σ = 𝒟(S̃)` (Develop's `bprop_danom` needs `DevelopsCC`, i.e. (CC′) for `Σ`, which is Classification's open `isCauchyComplete_of_cauchyCompact`), that `ρ(π₁M)` acts freely (torsion fixes the barycentre of an orbit in the convex `Ω(S̃)` ⊇ `𝒟(M̃)`, `bprop_ghyp`) and properly on `int D(Σ)`, so that `ρ(π₁M)\int D(Σ)` is a GH Cauchy extension of `M` (Examples' `globallyHyperbolic_quotient` is for Barbot's GH), which `MGH M` forces to be onto after a universe transport from `Type` to `M`'s universe; then `𝒟(M̃) = int D(Σ) ⊇ 𝒟(Ñ')` and `g` is onto

/-- **A finite cover of a maximal Cauchy-compact GH flat spacetime is maximal GH**:
`gh_of_isFiniteCover` (proved) and `maximal_of_isFiniteCover` (the one `sorry`). -/
theorem mgh_of_isFiniteCover (hGH : GH M) (hC : CauchyCompact M) (hM : MGH M)
    (hp : IsFiniteCover d p) : MGH M' :=
  ⟨gh_of_isFiniteCover hGH hp, maximal_of_isFiniteCover hGH hC hM hp⟩

end Cover

/-! ## §4 The statement -/

/-- **A finite cover `M'` of a maximal Cauchy-compact GH flat spacetime is maximal
Cauchy-compact GH, and every isometric embedding of `M'` into a GH spacetime `B` is onto a
Cauchy-compact `B`** (l.3536–3540, l.3578–3581; steps (1)–(3) of `cauclo_from_embedding`).
GH: `gh_of_isFiniteCover` (proved); maximality: `maximal_of_isFiniteCover` (the one
`sorry`); Cauchy-compactness: `cauchyCompact_of_isFiniteCover`; the last conjunct: the image
of the compact acausal Cauchy
surface `S` of `M'` is compact, connected (`isConnected_of_isCauchySurface`) and locally Cauchy
two-sided (L8), hence Cauchy by lemma K (`hK`), so `f` is a flat Cauchy embedding
(`isFlatCauchyEmbedding_iff`), onto by `MGH M'`, and `f(S)` is acausal by `rel_iff`. -/
theorem mgh_cauchyCompact_of_isFiniteCover
    (hK : ∀ N : FlatSpacetime.{0} d, GH N → ∀ S : Set N, IsCompact S → IsConnected S →
      (flatCausality d N).IsLocallyCauchyTwoSided S → (flatCausality d N).IsCauchySurface S)
    {M : FlatSpacetime.{u} d} (hGH : GH M) (hC : CauchyCompact M) (hM : MGH M)
    {M' : FlatSpacetime.{0} d} {p : M' → M} (hp : IsFiniteCover d p) :
    GH M' ∧ CauchyCompact M' ∧ MGH M' ∧
      ∀ (B : FlatSpacetime.{0} d) (f : M' → B), GH B → IsIsometricEmbedding d f →
        Surjective f ∧ CauchyCompact B := by
  have hMGH' : MGH M' := mgh_of_isFiniteCover hGH hC hM hp
  have hC' : CauchyCompact M' := cauchyCompact_of_isFiniteCover hGH hC hp
  refine ⟨hMGH'.1, hC', hMGH', fun B f hB hf => ?_⟩
  obtain ⟨S, hS, hSc, hSac⟩ := hC'
  have hSconn : IsConnected S := isConnected_of_isCauchySurface hMGH'.1.1 hS hSac
  have himage : (flatCausality d B).IsCauchySurface (f '' S) :=
    hK B hB (f '' S) (hSc.image hf.continuous) (hSconn.image f hf.continuous.continuousOn)
      (isLocallyCauchyTwoSided_image_of_isIsometricEmbedding hMGH'.1 hB hf hS hSac)
  have hsurj : Surjective f :=
    hMGH'.2 B f (isFlatCauchyEmbedding_iff.2 ⟨hf, hMGH'.1, hB, S, hS, himage⟩)
  refine ⟨hsurj, f '' S, himage, hSc.image hf.continuous, ?_⟩
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
  have hU : ((⊤ : Opens B) : Set B) = f '' ((⊤ : Opens M') : Set M') := by
    rw [Opens.coe_top, Opens.coe_top, image_univ, hsurj.range_eq]
  rw [hSac a ha b hb (((hf.rel_iff ⊤ ⊤ hU a b).1).2 hab)]

end Causal.Flat.Cla
