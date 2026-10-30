import Causal.ArcConnected
import Causal.Lines
import Causal.Local
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Topology.Order.IntermediateValue

/-!
# Morphisms of topological spacetimes, and time functions

**`defi:categorie_C`** — `ETT.tex:232`. **`def:category_topological_spacetimes`** — `ETT.tex:254`.
`ex:open_subset` — `ETT.tex:259`. **`defi:fonction_temps`** — `ETT.tex:1028`.
The readings (a), (b), (c) of SCOPE were ruled by the author on 2026-10-30 (DEC-12, which rules
OQ-12) as taken here, so the first, second and fourth are certified. `ex:open_subset` is not
marked: its uniqueness is false as written, in both sentences (OQ-13).

> Let $\mathbf{C}$ be the category whose objects are triples $(X,\leq, \tlleq)$ where $X$ is a
> topological space, $\leq$ is a preorder, and $\tlleq$ is a transitive relation contained in
> $\leq$ and open […]; and whose morphisms are the non-decreasing maps.

> A strong morphism $M\rightarrow N$ between topological spacetimes $M$ and $N$ is an open map
> inducing a sheaf morphism. A weak morphism $\phi:M\rightarrow N$ is a continuous map such that
> for every $x\in M$ and every neighbourhood $\U$ of $\phi(x)$ there exists a neighbourhood
> $\V\subset \phi^{-1}(\U)$ of $x$ such that $\phi_{|\V}^{|\U}$ is non-decreasing.

> An open subset of a topological spacetime carries a unique topological spacetime structure for
> which the inclusion is a strong morphism. More generally, if $\phi:N\rightarrow M$ is a local
> homeomorphism onto a topological spacetime $M$, then $N$ carries a unique causality for which
> $\phi$ is a local isomorphism of topological spacetimes.

> A time function $T$ on $M$ is a morphism of topological spacetimes
> $(M,\leq,\ll)\xrightarrow{~~T~~}(\RR,\leq,<)$.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| spacetimes second countable, Hausdorff | ⚠ weakened: used by no lemma; carried in the bundled `Spacetime` only |
| strong morphism: open, inducing a sheaf morphism | ✓ carried (DEC-10): continuous, open, and a morphism of `𝐂` from `φ⁻¹U` to `U` for every open `U` (`StrongMorphism.of_components`, `component`) |
| time function: a morphism to `(ℝ,≤,<)` | ✓ carried as a strong morphism (DEC-10) to `timelikeLine` |
| `ex:open_subset`, uniqueness, first sentence | ⚠ strengthened: false as written (`openSubset_not_unique`); proved for an inclusion which also reflects the relations (`InclusionStrong.eq_restrict`) |
| `ex:open_subset`, uniqueness, second sentence | ⚠ strengthened: false as written (`localIsomorphism_not_unique`); proved among absolutely minimal causalities (`LocalIsomorphism.unique`) |
| `ex:open_subset`, existence | ✓ carried: `restrict_inclusionStrong`, `pullback_localIsomorphism` (any local homeomorphism) |

## SCOPE (disclosed)

* **(a)** (ruled, DEC-12) "Non-decreasing" (a morphism of `𝐂`) is read `≤ ↦ ≤` **and** `≪ ↦ ≪`. Morphisms of
  `𝐂` are not asked to be continuous. Consequence: a weak morphism from the *lightlike* line is a
  causal curve and one from the *timelike* line a chronal curve (`weakMorphism_lightlikeLine_iff`,
  `weakMorphism_timelikeLine_iff`).
* **(b)** (ruled, DEC-12: "both are valid, but the local construction of causality gives the
  within component one") `(ℝ,≤,<)` is `timelikeLine` (related within a component of the open set). The other
  reading is `orderLine` (the order restricted to the open set). They agree for a causally
  arc-connected `M` (`isTimeFunction_iff_order`) and differ in general
  (`orderLine_id_not_isTimeFunction`).
* **(c)** (ruled, DEC-12) "Neighbourhood" in a weak morphism is read *open*. "Local isomorphism" is read: a local
  homeomorphism such that each point has an open neighbourhood `V`, `φ` injective on `V`, with
  `y ≤_{V'} z ↔ φ y ≤_{φ V'} φ z` (and `≪`) for every open `V' ⊆ V` and `y, z ∈ V'`.
  `N` is not asked to be second countable or Hausdorff; the paper says nothing of `N`, and a
  local homeomorphism (the line with two origins onto `ℝ`) need not have a Hausdorff source.
* **Second sentence: uniqueness fails without a gluing property.** The witness
  `timelikeLineTop` is a causality only because, like the paper's "equivalently" form,
  `Causality` has no gluing axiom; it is not causal, not absolutely minimal, not local in the
  sheaf sense. Among absolutely minimal causalities uniqueness holds (`LocalIsomorphism.unique`).
  First sentence: the witness `diagonal` is not of that kind (equality on each open set, glued
  from any cover); there uniqueness fails because a strong morphism only asks the relations of
  `W` to imply those of `M`.
* `ex:open_subset` is stated with `LocalCausality W` (kb/0001): `InclusionStrong` says the
  inclusion is a strong morphism, and `inclusionStrong_iff` proves it is `StrongMorphism` for the
  subspace `↥W` (the one bridge through a subtype, with `Causality.toCObj`, `toSubtype`).
* Naturality of the sheaf morphism is automatic (its components are restrictions of `φ`) and is
  not stated.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Relation CategoryTheory

universe u v w

/-! ### The category `𝐂` -/

/-- The triple `(X, le, lt)` is an object of `𝐂`: `le` is a preorder, `lt` is a transitive relation
contained in `le` and open. -/
structure IsCObject (X : Type u) [TopologicalSpace X] (le lt : X → X → Prop) : Prop where
  le_refl : ∀ x, le x x
  le_trans : ∀ {x y z}, le x y → le y z → le x z
  lt_trans : ∀ {x y z}, lt x y → lt y z → lt x z
  le_of_lt : ∀ {x y}, lt x y → le x y
  isOpen_lt_right : ∀ x, IsOpen {y | lt x y}
  isOpen_lt_left : ∀ x, IsOpen {y | lt y x}

/-- `defi:categorie_C`: an object of `𝐂`. -/
structure CObj where
  carrier : Type u
  [top : TopologicalSpace carrier]
  le : carrier → carrier → Prop
  lt : carrier → carrier → Prop
  isCObject : IsCObject carrier le lt

attribute [instance] CObj.top

/-- `defi:categorie_C`: a morphism of `𝐂`, a non-decreasing map, reading (a). -/
structure CObj.Hom (A : CObj.{u}) (B : CObj.{v}) where
  /-- The underlying map. -/
  toFun : A.carrier → B.carrier
  map_le : ∀ {x y}, A.le x y → B.le (toFun x) (toFun y)
  map_lt : ∀ {x y}, A.lt x y → B.lt (toFun x) (toFun y)

/-- `defi:categorie_C`: the category `𝐂`. -/
instance : Category CObj.{u} where
  Hom := CObj.Hom
  id _ := ⟨id, id, id⟩
  comp f g := ⟨g.toFun ∘ f.toFun, fun h => g.map_le (f.map_le h), fun h => g.map_lt (f.map_lt h)⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

variable {M : Type u} {N : Type v} {P : Type w}
  [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]

/-- `defi:causalite`, first sentence, on the side of objects: `(U, ≤_U, ≪_U)` is an object of
`𝐂`. (A subtype, because the objects of `𝐂` are spaces: see SCOPE.) -/
abbrev Causality.toCObj (C : Causality M) (U : Opens M) : CObj.{u} where
  carrier := U
  le x y := C.le U x y
  lt x y := C.lt U x y
  isCObject :=
    { le_refl := fun x => C.le_refl x.2
      le_trans := fun h₁ h₂ => C.le_trans h₁ h₂
      lt_trans := fun h₁ h₂ => C.lt_trans h₁ h₂
      le_of_lt := fun h => C.le_of_lt h
      isOpen_lt_right := fun x =>
        (C.isOpen_lt_right U x).preimage continuous_subtype_val
      isOpen_lt_left := fun x =>
        (C.isOpen_lt_left U x).preimage continuous_subtype_val }

/-- The preimage of an open set under a continuous map, as an open set. -/
def preimageOpens {φ : M → N} (hφ : Continuous φ) (U : Opens N) : Opens M :=
  ⟨φ ⁻¹' U, hφ.isOpen_preimage _ U.isOpen⟩

@[simp] theorem coe_preimageOpens {φ : M → N} (hφ : Continuous φ) (U : Opens N) :
    (preimageOpens hφ U : Set M) = φ ⁻¹' U := rfl

/-! ### Strong and weak morphisms -/

/-- `def:category_topological_spacetimes`: a **strong morphism** (DEC-10). `φ` is continuous and
open, and for every open `U` of `N` it is a morphism of `𝐂` from `(φ⁻¹U, ≤_{φ⁻¹U}, ≪_{φ⁻¹U})`
to `(U, ≤_U, ≪_U)`. The open set `φ⁻¹U` is quantified as any `V` with `V = φ⁻¹U`. -/
structure StrongMorphism (C : Causality M) (D : Causality N) (φ : M → N) : Prop where
  continuous : Continuous φ
  isOpenMap : IsOpenMap φ
  map_le : ∀ (U : Opens N) (V : Opens M), (V : Set M) = φ ⁻¹' U →
    ∀ ⦃x y : M⦄, C.le V x y → D.le U (φ x) (φ y)
  map_lt : ∀ (U : Opens N) (V : Opens M), (V : Set M) = φ ⁻¹' U →
    ∀ ⦃x y : M⦄, C.lt V x y → D.lt U (φ x) (φ y)

/-- `def:category_topological_spacetimes`: a **weak morphism**, neighbourhoods read open. -/
structure WeakMorphism (C : Causality M) (D : Causality N) (φ : M → N) : Prop where
  continuous : Continuous φ
  local_mono : ∀ (x : M) (U : Opens N), φ x ∈ U → ∃ V : Opens M, x ∈ V ∧ MapsTo φ V U ∧
    (∀ ⦃y z : M⦄, C.le V y z → D.le U (φ y) (φ z)) ∧
    (∀ ⦃y z : M⦄, C.lt V y z → D.lt U (φ y) (φ z))

variable {C : Causality M} {D : Causality N} {E : Causality P} {φ : M → N} {ψ : N → P}

namespace StrongMorphism

/-- A strong morphism maps the relations of every open `V` with `φ(V) ⊆ U` into those of `U`. -/
theorem le_of_mapsTo (h : StrongMorphism C D φ) {U : Opens N} {V : Opens M}
    (hV : MapsTo φ V U) {x y : M} (hxy : C.le V x y) : D.le U (φ x) (φ y) :=
  h.map_le U (preimageOpens h.continuous U) rfl
    (C.le_mono (show V ≤ preimageOpens h.continuous U from hV) hxy)

theorem lt_of_mapsTo (h : StrongMorphism C D φ) {U : Opens N} {V : Opens M}
    (hV : MapsTo φ V U) {x y : M} (hxy : C.lt V x y) : D.lt U (φ x) (φ y) :=
  h.map_lt U (preimageOpens h.continuous U) rfl
    (C.lt_mono (show V ≤ preimageOpens h.continuous U from hV) hxy)

/-- The component at `U` of the sheaf morphism: a morphism of `𝐂`. -/
def component (h : StrongMorphism C D φ) (U : Opens N) :
    CObj.Hom (C.toCObj (preimageOpens h.continuous U)) (D.toCObj U) :=
  CObj.Hom.mk (fun (x : preimageOpens h.continuous U) => (⟨φ x, x.2⟩ : U))
    (fun hxy => h.map_le U (preimageOpens h.continuous U) rfl hxy)
    (fun hxy => h.map_lt U (preimageOpens h.continuous U) rfl hxy)

/-- A continuous open map is a strong morphism as soon as each restriction is a morphism of
`𝐂`: the definition is DEC-10's word for word. -/
theorem of_components (hc : Continuous φ) (ho : IsOpenMap φ)
    (f : ∀ U : Opens N, CObj.Hom (C.toCObj (preimageOpens hc U)) (D.toCObj U))
    (hf : ∀ U (x : preimageOpens hc U), ((f U).toFun x).1 = φ x) : StrongMorphism C D φ where
  continuous := hc
  isOpenMap := ho
  map_le U V hV x y hxy := by
    have hV' : V = preimageOpens hc U := SetLike.coe_injective hV
    subst hV'
    have h' : D.le U ((f U).toFun ⟨x, C.le_mem_left hxy⟩).1 ((f U).toFun ⟨y, C.le_mem_right hxy⟩).1 :=
      (f U).map_le hxy
    rwa [hf, hf] at h'
  map_lt U V hV x y hxy := by
    have hV' : V = preimageOpens hc U := SetLike.coe_injective hV
    subst hV'
    have h' : D.lt U ((f U).toFun ⟨x, C.lt_mem_left hxy⟩).1 ((f U).toFun ⟨y, C.lt_mem_right hxy⟩).1 :=
      (f U).map_lt hxy
    rwa [hf, hf] at h'

/-- The identity is a strong morphism. -/
protected theorem id : StrongMorphism C C id where
  continuous := continuous_id
  isOpenMap := IsOpenMap.id
  map_le U V hV _ _ hxy := by
    have : V = U := SetLike.coe_injective hV
    subst this; exact hxy
  map_lt U V hV _ _ hxy := by
    have : V = U := SetLike.coe_injective hV
    subst this; exact hxy

/-- Strong morphisms compose. -/
theorem comp (hψ : StrongMorphism D E ψ) (hφ : StrongMorphism C D φ) :
    StrongMorphism C E (ψ ∘ φ) where
  continuous := hψ.continuous.comp hφ.continuous
  isOpenMap := hψ.isOpenMap.comp hφ.isOpenMap
  map_le W V hV _ _ hxy :=
    hψ.map_le W (preimageOpens hψ.continuous W) rfl
      (hφ.map_le (preimageOpens hψ.continuous W) V hV hxy)
  map_lt W V hV _ _ hxy :=
    hψ.map_lt W (preimageOpens hψ.continuous W) rfl
      (hφ.map_lt (preimageOpens hψ.continuous W) V hV hxy)

/-- A strong morphism is a weak morphism. -/
theorem weakMorphism (h : StrongMorphism C D φ) : WeakMorphism C D φ where
  continuous := h.continuous
  local_mono _ U hx := ⟨preimageOpens h.continuous U, hx, fun _ hy => hy,
    fun _ _ hyz => h.map_le U _ rfl hyz, fun _ _ hyz => h.map_lt U _ rfl hyz⟩

end StrongMorphism

namespace WeakMorphism

protected theorem id : WeakMorphism C C id where
  continuous := continuous_id
  local_mono _ U hx := ⟨U, hx, fun _ hy => hy, fun _ _ h => h, fun _ _ h => h⟩

/-- Weak morphisms compose. -/
theorem comp (hψ : WeakMorphism D E ψ) (hφ : WeakMorphism C D φ) :
    WeakMorphism C E (ψ ∘ φ) where
  continuous := hψ.continuous.comp hφ.continuous
  local_mono x W hx := by
    obtain ⟨U, hxU, hUW, hle, hlt⟩ := hψ.local_mono (φ x) W hx
    obtain ⟨V, hxV, hVU, hle', hlt'⟩ := hφ.local_mono x U hxU
    exact ⟨V, hxV, hUW.comp hVU, fun _ _ h => hle (hle' h), fun _ _ h => hlt (hlt' h)⟩

end WeakMorphism

/-- `def:category_topological_spacetimes`: a topological spacetime, bundled. -/
structure Spacetime where
  carrier : Type u
  [top : TopologicalSpace carrier]
  [t2 : T2Space carrier]
  [secondCountable : SecondCountableTopology carrier]
  causality : Causality carrier

attribute [instance] Spacetime.top Spacetime.t2 Spacetime.secondCountable

/-- `def:category_topological_spacetimes`: the category of topological spacetimes and strong
morphisms. -/
instance : Category Spacetime.{u} where
  Hom X Y := {φ : X.carrier → Y.carrier // StrongMorphism X.causality Y.causality φ}
  id _ := ⟨id, StrongMorphism.id⟩
  comp f g := ⟨g.1 ∘ f.1, g.2.comp f.2⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-! ### Weak morphisms from a line are curves -/

section Curves

variable {c : ℝ → M} {W : Opens M} {a b : ℝ}

/-- An open set of `ℝ` around `t` contains an interval around `t`. -/
theorem exists_Ioo_subset_opens {V : Opens ℝ} {t : ℝ} (ht : t ∈ V) :
    ∃ l u, l < t ∧ t < u ∧ Ioo l u ⊆ (V : Set ℝ) := by
  obtain ⟨l, u, ⟨hl, hu⟩, hlu⟩ := mem_nhds_iff_exists_Ioo_subset.1 (V.isOpen.mem_nhds ht)
  exact ⟨l, u, hl, hu, hlu⟩

/-- Under reading (a), a weak morphism from the lightlike line is a causal curve. -/
theorem WeakMorphism.causalCurveOn (h : WeakMorphism lightlikeLine C c)
    (hW : ∀ t ∈ Icc a b, c t ∈ W) : C.CausalCurveOn W c a b where
  mem := hW
  rel t _ N _ htN := by
    obtain ⟨V, htV, -, hle, -⟩ := h.local_mono t N htN
    obtain ⟨l, u, hl, hu, hlu⟩ := exists_Ioo_subset_opens htV
    exact ⟨l, u, hl, hu, fun s _ s' _ h1 h2 h3 =>
      hle ⟨h2.le, fun z hz => hlu ⟨h1.trans_le hz.1, hz.2.trans_lt h3⟩⟩⟩

/-- Under reading (a), a weak morphism from the timelike line is a chronal curve. -/
theorem WeakMorphism.chronalCurveOn (h : WeakMorphism timelikeLine C c)
    (hW : ∀ t ∈ Icc a b, c t ∈ W) : C.ChronalCurveOn W c a b where
  mem := hW
  rel t _ N _ htN := by
    obtain ⟨V, htV, -, -, hlt⟩ := h.local_mono t N htN
    obtain ⟨l, u, hl, hu, hlu⟩ := exists_Ioo_subset_opens htV
    exact ⟨l, u, hl, hu, fun s _ s' _ h1 h2 h3 =>
      hlt ⟨h2, fun z hz => hlu ⟨h1.trans_le hz.1, hz.2.trans_lt h3⟩⟩⟩

/-- A map from `ℝ` which is a curve, for the relations `r`, over every segment: around each `t`,
an interval on which `c` is related by `r U` in the order of the parameters, inside `U`. -/
theorem exists_interval_of_curveOn {r : Opens M → M → M → Prop} (hr : IsRelFamily r)
    (hc : ∀ a b, CurveOn r ⊤ c a b) (t : ℝ) (U : Opens M) (htU : c t ∈ U) :
    ∃ l u, l < t ∧ t < u ∧ (∀ s ∈ Ioo l u, c s ∈ U) ∧
      ∀ s s', l < s → s < s' → s' < u → r U (c s) (c s') := by
  obtain ⟨l, u, hl, hu, hrel⟩ := (hc (t - 1) (t + 1)).rel t ⟨by linarith, by linarith⟩ U le_top htU
  refine ⟨max l (t - 1), min u (t + 1), max_lt hl (by linarith), lt_min hu (by linarith), ?_, ?_⟩
  · rintro s ⟨hs1, hs2⟩
    have hs : s ∈ Icc (t - 1) (t + 1) :=
      ⟨(le_max_right _ _).trans hs1.le, hs2.le.trans (min_le_right _ _)⟩
    have ht : t ∈ Icc (t - 1) (t + 1) := ⟨by linarith, by linarith⟩
    rcases lt_trichotomy s t with h | h | h
    · exact hr.mem_left (hrel s hs t ht ((le_max_left _ _).trans_lt hs1) h hu)
    · exact h ▸ htU
    · exact hr.mem_right (hrel t ht s hs hl h (hs2.trans_le (min_le_left _ _)))
  · intro s s' h1 h2 h3
    exact hrel s ⟨(le_max_right _ _).trans h1.le, (h2.trans h3).le.trans (min_le_right _ _)⟩ s'
      ⟨((le_max_right _ _).trans_lt (h1.trans h2)).le, h3.le.trans (min_le_right _ _)⟩
      ((le_max_left _ _).trans_lt h1) h2 (h3.trans_le (min_le_left _ _))

theorem continuous_of_curveOn {r : Opens M → M → M → Prop} (hr : IsRelFamily r)
    (hc : ∀ a b, CurveOn r ⊤ c a b) : Continuous c := by
  rw [continuous_iff_continuousAt]
  intro t
  exact ((hc (t - 1) (t + 1)).continuousOn hr).continuousAt
    (Icc_mem_nhds (by linarith) (by linarith))

/-- Reading (a): weak morphisms from the lightlike line are exactly the maps which are causal
curves over every segment. -/
theorem weakMorphism_lightlikeLine_iff :
    WeakMorphism lightlikeLine C c ↔ ∀ a b, C.CausalCurveOn ⊤ c a b := by
  refine ⟨fun h a b => h.causalCurveOn fun _ _ => trivial, fun h => ?_⟩
  refine ⟨continuous_of_curveOn C.isRelFamily_le h, fun t U htU => ?_⟩
  obtain ⟨l, u, hl, hu, hmem, hrel⟩ := exists_interval_of_curveOn C.isRelFamily_le h t U htU
  refine ⟨⟨Ioo l u, isOpen_Ioo⟩, ⟨hl, hu⟩, fun s hs => hmem s hs, ?_, fun _ _ h => h.elim⟩
  rintro s s' ⟨hss', hsub⟩
  have hs : s ∈ Ioo l u := hsub (left_mem_Icc.2 hss')
  have hs' : s' ∈ Ioo l u := hsub (right_mem_Icc.2 hss')
  rcases hss'.eq_or_lt with h' | h'
  · subst h'; exact C.le_refl (hmem s hs)
  · exact hrel s s' hs.1 h' hs'.2

/-- Reading (a): weak morphisms from the timelike line are exactly the maps which are chronal
curves over every segment. -/
theorem weakMorphism_timelikeLine_iff :
    WeakMorphism timelikeLine C c ↔ ∀ a b, C.ChronalCurveOn ⊤ c a b := by
  refine ⟨fun h a b => h.chronalCurveOn fun _ _ => trivial, fun h => ?_⟩
  refine ⟨continuous_of_curveOn C.isRelFamily_lt h, fun t U htU => ?_⟩
  obtain ⟨l, u, hl, hu, hmem, hrel⟩ := exists_interval_of_curveOn C.isRelFamily_lt h t U htU
  refine ⟨⟨Ioo l u, isOpen_Ioo⟩, ⟨hl, hu⟩, fun s hs => hmem s hs, ?_, ?_⟩
  · rintro s s' ⟨hss', hsub⟩
    have hs : s ∈ Ioo l u := hsub (left_mem_Icc.2 hss')
    have hs' : s' ∈ Ioo l u := hsub (right_mem_Icc.2 hss')
    rcases hss'.eq_or_lt with h' | h'
    · subst h'; exact C.le_refl (hmem s hs)
    · exact C.le_of_lt (hrel s s' hs.1 h' hs'.2)
  · rintro s s' ⟨hss', hsub⟩
    have hs : s ∈ Ioo l u := hsub (left_mem_Icc.2 hss'.le)
    have hs' : s' ∈ Ioo l u := hsub (right_mem_Icc.2 hss'.le)
    exact hrel s s' hs.1 hss' hs'.2

end Curves

/-! ### `ex:open_subset`, first sentence: an open subset -/

section OpenSubset

variable {W : Opens M}

/-- The inclusion of the open set `W`, with the causality `L`, into `(M, C)` is a strong
morphism: the preimage of the open `U` is `U ⊓ W`, and the inclusion is continuous and open. -/
def LocalCausality.InclusionStrong (L : LocalCausality W) (C : Causality M) : Prop :=
  ∀ (U : Opens M) ⦃x y : M⦄, (L.le (U ⊓ W) x y → C.le U x y) ∧ (L.lt (U ⊓ W) x y → C.lt U x y)

/-- `ex:open_subset`: the inclusion is a strong morphism for the restriction. -/
theorem Causality.restrict_inclusionStrong (C : Causality M) (W : Opens M) :
    (C.restrict W).InclusionStrong C := fun _ _ _ =>
  ⟨fun h => C.le_mono inf_le_left h, fun h => C.lt_mono inf_le_left h⟩

/-- The restriction is the greatest causality on `W` for which the inclusion is a strong
morphism. -/
theorem LocalCausality.InclusionStrong.le_restrict {L : LocalCausality W}
    (h : L.InclusionStrong C) {V : Opens M} (hV : V ≤ W) {x y : M} :
    (L.le V x y → C.le V x y) ∧ (L.lt V x y → C.lt V x y) := by
  have hVW : V ⊓ W = V := inf_eq_left.2 hV
  have := h V (x := x) (y := y)
  rwa [hVW] at this

/-- `ex:open_subset`, uniqueness, under an added hypothesis: the restriction is the unique
causality on `W` for which the inclusion is a strong morphism *reflecting* the relations. -/
theorem LocalCausality.InclusionStrong.eq_restrict {L : LocalCausality W}
    (h : L.InclusionStrong C)
    (hrefl : ∀ V : Opens M, V ≤ W → ∀ x y, (C.le V x y → L.le V x y) ∧ (C.lt V x y → L.lt V x y))
    {V : Opens M} (hV : V ≤ W) (x y : M) :
    (L.le V x y ↔ (C.restrict W).le V x y) ∧ (L.lt V x y ↔ (C.restrict W).lt V x y) :=
  ⟨⟨(h.le_restrict hV).1, (hrefl V hV x y).1⟩, ⟨(h.le_restrict hV).2, (hrefl V hV x y).2⟩⟩

/-- The diagonal causality on `W`: `≤_V` is equality on `V`, `≪_V` is empty. -/
def LocalCausality.diagonal (W : Opens M) : LocalCausality W where
  le U x y := x = y ∧ x ∈ U
  lt _ _ _ := False
  le_mem_left _ h := h.2
  le_mem_right _ h := h.1 ▸ h.2
  lt_mem_left _ h := h.elim
  lt_mem_right _ h := h.elim
  le_refl _ hx := ⟨rfl, hx⟩
  le_trans _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2⟩
  lt_trans _ h _ := h
  le_mono _ hVU _ _ h := ⟨h.1, hVU h.2⟩
  lt_mono _ _ _ _ h := h
  le_of_lt _ h := h.elim
  isOpen_lt_right _ _ _ := by simp
  isOpen_lt_left _ _ _ := by simp

/-- The inclusion is a strong morphism for the diagonal causality, whatever `C`. -/
theorem LocalCausality.diagonal_inclusionStrong (C : Causality M) :
    (LocalCausality.diagonal W).InclusionStrong C := by
  rintro U x y
  refine ⟨?_, fun h => h.elim⟩
  rintro ⟨rfl, hx⟩
  exact C.le_refl ((inf_le_left : U ⊓ W ≤ U) hx)

/-- **`ex:open_subset`, first sentence, uniqueness is false as written**: on the timelike line,
the open set `ℝ` carries two distinct causalities for which the inclusion is a strong morphism. -/
theorem openSubset_not_unique :
    ∃ L₁ L₂ : LocalCausality (⊤ : Opens ℝ), L₁.InclusionStrong timelikeLine ∧
      L₂.InclusionStrong timelikeLine ∧ L₁.le ⊤ 0 1 ∧ ¬ L₂.le ⊤ 0 1 := by
  refine ⟨timelikeLine.restrict ⊤, LocalCausality.diagonal ⊤,
    timelikeLine.restrict_inclusionStrong ⊤, LocalCausality.diagonal_inclusionStrong _, ?_, ?_⟩
  · exact ⟨zero_le_one, fun _ _ => trivial⟩
  · rintro ⟨h, -⟩
    exact zero_ne_one h

/-- The image in `M` of an open set of the subspace `W`. -/
def imageOpens (V : Opens W) : Opens M :=
  ⟨Subtype.val '' (V : Set W), W.isOpen.isOpenMap_subtype_val _ V.isOpen⟩

theorem imageOpens_le (V : Opens W) : imageOpens V ≤ W := by
  rintro _ ⟨x, -, rfl⟩; exact x.2

theorem imageOpens_mono {V V' : Opens W} (h : V ≤ V') : imageOpens V ≤ imageOpens V' :=
  image_mono h

theorem val_mem_imageOpens {V : Opens W} {x : W} : x.1 ∈ imageOpens V ↔ x ∈ V :=
  Subtype.val_injective.mem_set_image

/-- The causality `L` on `W`, read on the subspace `↥W`: the bridge between the library's
`LocalCausality W` and the paper's "`W` carries a topological spacetime structure". -/
def LocalCausality.toSubtype (L : LocalCausality W) : Causality W where
  le V x y := L.le (imageOpens V) x y
  lt V x y := L.lt (imageOpens V) x y
  le_mem_left h := val_mem_imageOpens.1 (L.le_mem_left (imageOpens_le _) h)
  le_mem_right h := val_mem_imageOpens.1 (L.le_mem_right (imageOpens_le _) h)
  lt_mem_left h := val_mem_imageOpens.1 (L.lt_mem_left (imageOpens_le _) h)
  lt_mem_right h := val_mem_imageOpens.1 (L.lt_mem_right (imageOpens_le _) h)
  le_refl hx := L.le_refl (imageOpens_le _) (val_mem_imageOpens.2 hx)
  le_trans h₁ h₂ := L.le_trans (imageOpens_le _) h₁ h₂
  lt_trans h₁ h₂ := L.lt_trans (imageOpens_le _) h₁ h₂
  le_mono h _ _ h' := L.le_mono (imageOpens_le _) (imageOpens_mono h) h'
  lt_mono h _ _ h' := L.lt_mono (imageOpens_le _) (imageOpens_mono h) h'
  le_of_lt h := L.le_of_lt (imageOpens_le _) h
  isOpen_lt_right V x :=
    (L.isOpen_lt_right (imageOpens V) x (imageOpens_le _)).preimage continuous_subtype_val
  isOpen_lt_left V x :=
    (L.isOpen_lt_left (imageOpens V) x (imageOpens_le _)).preimage continuous_subtype_val

theorem imageOpens_eq_inf {U : Opens M} {V : Opens W}
    (hV : (V : Set W) = Subtype.val ⁻¹' (U : Set M)) : imageOpens V = U ⊓ W := by
  apply SetLike.coe_injective
  change Subtype.val '' (V : Set W) = (U : Set M) ∩ W
  rw [hV]
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩; exact ⟨hq, q.2⟩
  · rintro ⟨hpU, hpW⟩; exact ⟨⟨p, hpW⟩, hpU, rfl⟩

/-- `InclusionStrong` is the strong morphism of `def:category_topological_spacetimes`, for the
inclusion `↥W → M`. -/
theorem LocalCausality.inclusionStrong_iff (L : LocalCausality W) (C : Causality M) :
    L.InclusionStrong C ↔ StrongMorphism L.toSubtype C Subtype.val := by
  constructor
  · intro h
    refine ⟨continuous_subtype_val, W.isOpen.isOpenMap_subtype_val, fun U V hV x y hxy => ?_,
      fun U V hV x y hxy => ?_⟩
    · have hxy' : L.le (imageOpens V) x y := hxy
      rw [imageOpens_eq_inf hV] at hxy'
      exact (h U).1 hxy'
    · have hxy' : L.lt (imageOpens V) x y := hxy
      rw [imageOpens_eq_inf hV] at hxy'
      exact (h U).2 hxy'
  · intro h U x y
    let V : Opens W := ⟨Subtype.val ⁻¹' (U : Set M), U.isOpen.preimage continuous_subtype_val⟩
    have hV : (V : Set W) = Subtype.val ⁻¹' (U : Set M) := rfl
    refine ⟨fun hxy => ?_, fun hxy => ?_⟩
    · have hx : x ∈ W := (inf_le_right : U ⊓ W ≤ W) (L.le_mem_left inf_le_right hxy)
      have hy : y ∈ W := (inf_le_right : U ⊓ W ≤ W) (L.le_mem_right inf_le_right hxy)
      have hxy' : L.toSubtype.le V ⟨x, hx⟩ ⟨y, hy⟩ := by
        show L.le (imageOpens V) x y
        rw [imageOpens_eq_inf hV]; exact hxy
      exact h.map_le U V hV hxy'
    · have hx : x ∈ W := (inf_le_right : U ⊓ W ≤ W) (L.lt_mem_left inf_le_right hxy)
      have hy : y ∈ W := (inf_le_right : U ⊓ W ≤ W) (L.lt_mem_right inf_le_right hxy)
      have hxy' : L.toSubtype.lt V ⟨x, hx⟩ ⟨y, hy⟩ := by
        show L.lt (imageOpens V) x y
        rw [imageOpens_eq_inf hV]; exact hxy
      exact h.map_lt U V hV hxy'

end OpenSubset

/-! ### `ex:open_subset`, second sentence: the pull-back along a local homeomorphism -/

section LocalHomeomorph

variable {φ : N → M}

/-- A **local isomorphism** of topological spacetimes `(N, C) → (M, D)` (the reading of SCOPE):
a local homeomorphism such that every point has an open neighbourhood `V` on which `φ` is
injective and matches the relations of every open `V' ⊆ V` with those of `φ(V')`. -/
def LocalIsomorphism (C : Causality N) (D : Causality M) (φ : N → M) : Prop :=
  IsLocalHomeomorph φ ∧ ∀ x : N, ∃ V : Opens N, x ∈ V ∧ InjOn φ V ∧
    ∀ V' : Opens N, V' ≤ V → ∀ U : Opens M, (U : Set M) = φ '' V' → ∀ y ∈ V', ∀ z ∈ V',
      (C.le V' y z ↔ D.le U (φ y) (φ z)) ∧ (C.lt V' y z ↔ D.lt U (φ y) (φ z))

/-- One step of the pulled-back relation in `V`: inside an open `W ⊆ V` on which `φ` is injective,
the relation of `φ(W)`. -/
def PullLink (r : Opens M → M → M → Prop) (φ : N → M) (V : Opens N) (a b : N) : Prop :=
  ∃ W : Opens N, W ≤ V ∧ InjOn φ W ∧ a ∈ W ∧ b ∈ W ∧
    ∃ U : Opens M, (U : Set M) = φ '' W ∧ r U (φ a) (φ b)

namespace PullLink

variable {r : Opens M → M → M → Prop} {V V' : Opens N} {a b : N}

theorem mem_left (h : PullLink r φ V a b) : a ∈ V := by
  obtain ⟨W, hW, -, ha, -⟩ := h; exact hW ha

theorem mem_right (h : PullLink r φ V a b) : b ∈ V := by
  obtain ⟨W, hW, -, -, hb, -⟩ := h; exact hW hb

theorem mono (hV : V ≤ V') (h : PullLink r φ V a b) : PullLink r φ V' a b := by
  obtain ⟨W, hW, hi, ha, hb, U, hU, hr⟩ := h
  exact ⟨W, hW.trans hV, hi, ha, hb, U, hU, hr⟩

theorem transGen_mem_left (h : TransGen (PullLink r φ V) a b) : a ∈ V := by
  rcases TransGen.head'_iff.1 h with ⟨c, hac, -⟩
  exact hac.mem_left

theorem transGen_mem_right (h : TransGen (PullLink r φ V) a b) : b ∈ V := by
  rcases TransGen.tail'_iff.1 h with ⟨c, -, hcb⟩
  exact hcb.mem_right

/-- A chain of steps in `V` gives the relation of `φ(V)`. -/
theorem transGen_imp (hr : IsRelFamily r) {U : Opens M} (hU : (U : Set M) = φ '' V)
    (h : TransGen (PullLink r φ V) a b) : r U (φ a) (φ b) := by
  have step : ∀ {a b}, PullLink r φ V a b → r U (φ a) (φ b) := by
    rintro a b ⟨W, hW, -, -, -, U', hU', hr'⟩
    refine hr.mono ?_ hr'
    intro p hp
    have hp' : p ∈ φ '' W := by rw [← hU']; exact hp
    show p ∈ (U : Set M)
    rw [hU]
    exact image_mono hW hp'
  induction h with
  | single hl => exact step hl
  | tail _ hl ih => exact hr.trans ih (step hl)

/-- The set of points reached by a chain from `x` is open when every relation is open. -/
theorem isOpen_transGen_right (hφ : Continuous φ)
    (hopen : ∀ (U : Opens M) (p : M), IsOpen {q | r U p q}) (x : N) :
    IsOpen {y | TransGen (PullLink r φ V) x y} := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  obtain ⟨a, hxa, W, hW, hi, ha, hyW, U, hU, hr⟩ := TransGen.tail'_iff.1 hy
  have hO : IsOpen ((W : Set N) ∩ φ ⁻¹' {q | r U (φ a) q}) :=
    W.isOpen.inter ((hopen U (φ a)).preimage hφ)
  refine Filter.mem_of_superset (hO.mem_nhds ⟨hyW, hr⟩) ?_
  rintro y' ⟨hy'W, hy'⟩
  exact TransGen.tail'_iff.2 ⟨a, hxa, W, hW, hi, ha, hy'W, U, hU, hy'⟩

theorem isOpen_transGen_left (hφ : Continuous φ)
    (hopen : ∀ (U : Opens M) (p : M), IsOpen {q | r U q p}) (x : N) :
    IsOpen {y | TransGen (PullLink r φ V) y x} := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  obtain ⟨a, ⟨W, hW, hi, hyW, ha, U, hU, hr⟩, hax⟩ := TransGen.head'_iff.1 hy
  have hO : IsOpen ((W : Set N) ∩ φ ⁻¹' {q | r U q (φ a)}) :=
    W.isOpen.inter ((hopen U (φ a)).preimage hφ)
  refine Filter.mem_of_superset (hO.mem_nhds ⟨hyW, hr⟩) ?_
  rintro y' ⟨hy'W, hy'⟩
  exact TransGen.head'_iff.2 ⟨a, ⟨W, hW, hi, hy'W, ha, U, hU, hy'⟩, hax⟩

end PullLink

/-- The causality pulled back along the continuous map `φ`: chains of relations read through `φ`
in open sets on which `φ` is injective. -/
def Causality.pullback (D : Causality M) (hφ : Continuous φ) : Causality N where
  le V x y := (x = y ∧ x ∈ V) ∨ TransGen (PullLink D.le φ V) x y
  lt V x y := TransGen (PullLink D.lt φ V) x y
  le_mem_left := by
    rintro V x y (⟨-, hx⟩ | h)
    · exact hx
    · exact PullLink.transGen_mem_left h
  le_mem_right := by
    rintro V x y (⟨rfl, hx⟩ | h)
    · exact hx
    · exact PullLink.transGen_mem_right h
  lt_mem_left h := PullLink.transGen_mem_left h
  lt_mem_right h := PullLink.transGen_mem_right h
  le_refl hx := Or.inl ⟨rfl, hx⟩
  le_trans := by
    rintro V x y z (⟨rfl, -⟩ | h₁) h₂
    · exact h₂
    · rcases h₂ with ⟨rfl, -⟩ | h₂
      · exact Or.inr h₁
      · exact Or.inr (h₁.trans h₂)
  lt_trans h₁ h₂ := h₁.trans h₂
  le_mono := by
    rintro U V hVU x y (⟨rfl, hx⟩ | h)
    · exact Or.inl ⟨rfl, hVU hx⟩
    · exact Or.inr (TransGen.mono (fun _ _ => PullLink.mono hVU) h)
  lt_mono hVU _ _ h := TransGen.mono (fun _ _ => PullLink.mono hVU) h
  le_of_lt h := Or.inr (TransGen.mono (fun _ _ ⟨W, hW, hi, ha, hb, U, hU, hr⟩ =>
    ⟨W, hW, hi, ha, hb, U, hU, D.le_of_lt hr⟩) h)
  isOpen_lt_right _ x := PullLink.isOpen_transGen_right hφ D.isOpen_lt_right x
  isOpen_lt_left _ x := PullLink.isOpen_transGen_left hφ D.isOpen_lt_left x

/-- `ex:open_subset`, second sentence, existence: along a local homeomorphism, the pulled-back
causality makes `φ` a local isomorphism. -/
theorem Causality.pullback_localIsomorphism (D : Causality M) (hφ : IsLocalHomeomorph φ) :
    LocalIsomorphism (D.pullback hφ.continuous) D φ := by
  refine ⟨hφ, fun x => ?_⟩
  obtain ⟨e, hxe, rfl⟩ := hφ x
  refine ⟨⟨e.source, e.open_source⟩, hxe, e.injOn, fun V' hV' U hU y hy z hz => ⟨?_, ?_⟩⟩
  · constructor
    · rintro (⟨rfl, -⟩ | h)
      · exact D.le_refl (by rw [← SetLike.mem_coe, hU]; exact mem_image_of_mem _ hy)
      · exact PullLink.transGen_imp D.isRelFamily_le hU h
    · intro h
      exact Or.inr (TransGen.single ⟨V', le_rfl, e.injOn.mono hV', hy, hz, U, hU, h⟩)
  · constructor
    · exact PullLink.transGen_imp D.isRelFamily_lt hU
    · intro h
      exact TransGen.single ⟨V', le_rfl, e.injOn.mono hV', hy, hz, U, hU, h⟩

/-- If `C₁` is absolutely minimal and both `C₁`, `C₂` make `φ` a local isomorphism, the
relations of `C₁` are relations of `C₂`. -/
theorem LocalIsomorphism.le_of_absolutelyMinimal {D : Causality M} {C₁ C₂ : Causality N}
    (h₁ : LocalIsomorphism C₁ D φ) (h₂ : LocalIsomorphism C₂ D φ)
    (hmin : C₁.AbsolutelyMinimal) (V : Opens N) (x y : N) :
    (C₁.le V x y → C₂.le V x y) ∧ (C₁.lt V x y → C₂.lt V x y) := by
  choose V₁ hx₁ _hi₁ hV₁ using h₁.2
  choose V₂ hx₂ _hi₂ hV₂ using h₂.2
  let S : Set (Opens N) := range fun z => V₁ z ⊓ V₂ z
  have hS : ∀ z ∈ (⊤ : Opens N), ∃ O ∈ S, z ∈ O := fun z _ => ⟨_, ⟨z, rfl⟩, hx₁ z, hx₂ z⟩
  have hmin' := (Precausality.absolutelyMinimal_iff.1 hmin) S hS V le_top x y
  have hU : ∀ O : Opens N, ∃ U : Opens M, (U : Set M) = φ '' O :=
    fun O => ⟨⟨φ '' O, h₁.1.isOpenMap _ O.isOpen⟩, rfl⟩
  constructor
  · intro hxy
    refine Precausality.le_of_transGen (S := S) (TransGen.mono ?_ (hmin'.1 hxy))
    rintro a b ⟨O, ⟨z, rfl⟩, hab⟩
    refine ⟨_, ⟨z, rfl⟩, ?_⟩
    obtain ⟨U, hU⟩ := hU (V ⊓ (V₁ z ⊓ V₂ z))
    have ha := C₁.le_mem_left hab
    have hb := C₁.le_mem_right hab
    have h1 := ((hV₁ z _ (inf_le_right.trans inf_le_left) U hU a ha b hb).1).1 hab
    exact ((hV₂ z _ (inf_le_right.trans inf_le_right) U hU a ha b hb).1).2 h1
  · intro hxy
    refine Precausality.lt_of_transGen (S := S) (TransGen.mono ?_ (hmin'.2 hxy))
    rintro a b ⟨O, ⟨z, rfl⟩, hab⟩
    refine ⟨_, ⟨z, rfl⟩, ?_⟩
    obtain ⟨U, hU⟩ := hU (V ⊓ (V₁ z ⊓ V₂ z))
    have ha := C₁.lt_mem_left hab
    have hb := C₁.lt_mem_right hab
    have h1 := ((hV₁ z _ (inf_le_right.trans inf_le_left) U hU a ha b hb).2).1 hab
    exact ((hV₂ z _ (inf_le_right.trans inf_le_right) U hU a ha b hb).2).2 h1

/-- `ex:open_subset`, second sentence, uniqueness, under an added hypothesis: among absolutely
minimal causalities, at most one makes `φ` a local isomorphism. -/
theorem LocalIsomorphism.unique {D : Causality M} {C₁ C₂ : Causality N}
    (h₁ : LocalIsomorphism C₁ D φ) (h₂ : LocalIsomorphism C₂ D φ)
    (m₁ : C₁.AbsolutelyMinimal) (m₂ : C₂.AbsolutelyMinimal) : C₁ = C₂ := by
  have key : C₁.toPrecausality = C₂.toPrecausality := by
    ext V x y
    · exact ⟨(h₁.le_of_absolutelyMinimal h₂ m₁ V x y).1,
        (h₂.le_of_absolutelyMinimal h₁ m₂ V x y).1⟩
    · exact ⟨(h₁.le_of_absolutelyMinimal h₂ m₁ V x y).2,
        (h₂.le_of_absolutelyMinimal h₁ m₂ V x y).2⟩
  cases C₁; cases C₂; cases key; rfl

/-- The timelike line, with every pair of points related in `ℝ` itself.

**A pathological witness, disclosed.** It satisfies every axiom of `Causality` (the paper's
"equivalently" form, which carries no gluing axiom), and it is nothing else: it is not causal
(`timelikeLineTop_not_isCausal`), not absolutely minimal (`timelikeLineTop_not_absolutelyMinimal`),
and not local in the sheaf sense — its relation on `ℝ` is not generated by its relations on the
small open sets, on which it is the timelike line. It exists only to show that uniqueness in
`ex:open_subset` needs a gluing property. -/
def timelikeLineTop : Causality ℝ where
  le U x y := U = ⊤ ∨ timelikeLine.le U x y
  lt U x y := timelikeLine.lt U x y
  le_mem_left := by
    rintro U x y (rfl | h)
    · trivial
    · exact timelikeLine.le_mem_left h
  le_mem_right := by
    rintro U x y (rfl | h)
    · trivial
    · exact timelikeLine.le_mem_right h
  lt_mem_left h := timelikeLine.lt_mem_left h
  lt_mem_right h := timelikeLine.lt_mem_right h
  le_refl hx := Or.inr (timelikeLine.le_refl hx)
  le_trans := by
    rintro U x y z (rfl | h₁) h₂
    · exact Or.inl rfl
    · rcases h₂ with rfl | h₂
      · exact Or.inl rfl
      · exact Or.inr (timelikeLine.le_trans h₁ h₂)
  lt_trans h₁ h₂ := timelikeLine.lt_trans h₁ h₂
  le_mono := by
    rintro U V hVU x y (rfl | h)
    · exact Or.inl (top_le_iff.1 hVU)
    · exact Or.inr (timelikeLine.le_mono hVU h)
  lt_mono hVU _ _ h := timelikeLine.lt_mono hVU h
  le_of_lt h := Or.inr (timelikeLine.le_of_lt h)
  isOpen_lt_right := timelikeLine.isOpen_lt_right
  isOpen_lt_left := timelikeLine.isOpen_lt_left

theorem id_localIsomorphism_of_eq {C : Causality ℝ} (V : ℝ → Opens ℝ) (hV : ∀ x, x ∈ V x)
    (hC : ∀ x, ∀ V' : Opens ℝ, V' ≤ V x → ∀ y z,
      (C.le V' y z ↔ timelikeLine.le V' y z) ∧ (C.lt V' y z ↔ timelikeLine.lt V' y z)) :
    LocalIsomorphism C timelikeLine id := by
  refine ⟨(Homeomorph.refl ℝ).isLocalHomeomorph, fun x => ⟨V x, hV x, injOn_id _,
    fun V' hV' U hU y _ z _ => ?_⟩⟩
  have : U = V' := SetLike.coe_injective (by rw [hU, image_id])
  subst this
  exact hC x U hV' y z

/-- `timelikeLineTop` is not causal: `1 ≤_ℝ 0` and `0 ≤_ℝ 1`. -/
theorem timelikeLineTop_not_isCausal : ¬ timelikeLineTop.IsCausal := fun h =>
  zero_ne_one (h (Or.inl rfl) (Or.inl rfl))

/-- `timelikeLineTop` is not absolutely minimal: on the cover by the intervals `]x-1, x+1[` its
relations are those of the timelike line, which never chain `1` to `0`. -/
theorem timelikeLineTop_not_absolutelyMinimal : ¬ timelikeLineTop.AbsolutelyMinimal := by
  intro h
  let S : Set (Opens ℝ) := range fun x : ℝ => (⟨Ioo (x - 1) (x + 1), isOpen_Ioo⟩ : Opens ℝ)
  have hS : ∀ z ∈ (⊤ : Opens ℝ), ∃ O ∈ S, z ∈ O :=
    fun z _ => ⟨_, ⟨z, rfl⟩, show z ∈ Ioo (z - 1) (z + 1) from ⟨by linarith, by linarith⟩⟩
  have hchain := ((Precausality.absolutelyMinimal_iff.1 h) S hS ⊤ le_top 1 0).1 (Or.inl rfl)
  have key : ∀ a b : ℝ, TransGen (fun a b => ∃ O ∈ S, timelikeLineTop.le (⊤ ⊓ O) a b) a b →
      a ≤ b := by
    intro a b hab
    have step : ∀ a b : ℝ, (∃ O ∈ S, timelikeLineTop.le (⊤ ⊓ O) a b) → a ≤ b := by
      rintro a b ⟨O, ⟨x, rfl⟩, hO | hO⟩
      · have : x + 1 ∈ (⊤ ⊓ (⟨Ioo (x - 1) (x + 1), isOpen_Ioo⟩ : Opens ℝ) : Opens ℝ) := by
          rw [hO]; trivial
        exact absurd this.2.2 (lt_irrefl _)
      · exact hO.1
    induction hab with
    | single hl => exact step _ _ hl
    | tail _ hl ih => exact ih.trans (step _ _ hl)
  exact absurd (key 1 0 hchain) (by norm_num)

/-- **`ex:open_subset`, second sentence, uniqueness fails without a gluing property**: the identity
of `ℝ`, a local homeomorphism, is a local isomorphism from two distinct causalities to the timelike
line. The second, `timelikeLineTop`, is a causality only because the library (as the paper's
"equivalently" form) carries no gluing axiom: it is not causal, not absolutely minimal, not local
in the sheaf sense. Among absolutely minimal causalities uniqueness holds
(`LocalIsomorphism.unique`). -/
theorem localIsomorphism_not_unique :
    LocalIsomorphism timelikeLine timelikeLine id ∧
      LocalIsomorphism timelikeLineTop timelikeLine id ∧ timelikeLineTop ≠ timelikeLine := by
  refine ⟨id_localIsomorphism_of_eq (fun _ => ⊤) (fun _ => trivial)
    (fun _ _ _ _ _ => ⟨Iff.rfl, Iff.rfl⟩), ?_, ?_⟩
  · refine id_localIsomorphism_of_eq (fun x => ⟨Ioo (x - 1) (x + 1), isOpen_Ioo⟩)
      (fun x => ⟨by linarith, by linarith⟩) fun x V' hV' y z => ⟨?_, Iff.rfl⟩
    have hne : V' ≠ ⊤ := by
      rintro rfl
      have : x + 1 ∈ Ioo (x - 1) (x + 1) := hV' (show x + 1 ∈ (⊤ : Opens ℝ) from trivial)
      exact lt_irrefl _ this.2
    exact ⟨fun h => h.resolve_left hne, Or.inr⟩
  · intro h
    have h1 : timelikeLineTop.le ⊤ 1 0 := Or.inl rfl
    rw [h] at h1
    exact absurd h1.1 (by norm_num)

end LocalHomeomorph

/-! ### `defi:fonction_temps`: time functions -/

section TimeFunction

/-- The order of `ℝ`, restricted to each open set: reading (b), alternative. -/
def orderLine : Causality ℝ where
  le U x y := x ≤ y ∧ x ∈ U ∧ y ∈ U
  lt U x y := x < y ∧ x ∈ U ∧ y ∈ U
  le_mem_left h := h.2.1
  le_mem_right h := h.2.2
  lt_mem_left h := h.2.1
  lt_mem_right h := h.2.2
  le_refl hx := ⟨le_rfl, hx, hx⟩
  le_trans h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.1, h₂.2.2⟩
  lt_trans h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.1, h₂.2.2⟩
  le_mono h _ _ h' := ⟨h'.1, h h'.2.1, h h'.2.2⟩
  lt_mono h _ _ h' := ⟨h'.1, h h'.2.1, h h'.2.2⟩
  le_of_lt h := ⟨h.1.le, h.2⟩
  isOpen_lt_right U x := by
    by_cases hx : x ∈ U
    · simp only [hx, true_and]; exact isOpen_Ioi.inter U.isOpen
    · simp [hx]
  isOpen_lt_left U x := by
    by_cases hx : x ∈ U
    · simp only [hx, and_true]; exact isOpen_Iio.inter U.isOpen
    · simp [hx]

namespace Causality

variable (C : Causality M)

/-- `defi:fonction_temps` (DEC-10): a **time function** is a strong morphism to the timelike line
`(ℝ, ≤, <)`. -/
def IsTimeFunction (T : M → ℝ) : Prop := StrongMorphism C timelikeLine T

/-- `defi:fonction_temps`, reading (b) alternative: a strong morphism to `orderLine`. -/
def IsTimeFunctionOrder (T : M → ℝ) : Prop := StrongMorphism C orderLine T

variable {C} {T : M → ℝ} {U V W : Opens M} {x y : M}

namespace IsTimeFunction

theorem continuous (h : C.IsTimeFunction T) : Continuous T := StrongMorphism.continuous h

theorem isOpenMap (h : C.IsTimeFunction T) : IsOpenMap T := StrongMorphism.isOpenMap h

/-- A time function is non-decreasing for the causal relation of any open set. -/
theorem le (h : C.IsTimeFunction T) (hxy : C.le V x y) : T x ≤ T y :=
  (StrongMorphism.le_of_mapsTo h (U := ⊤) (fun _ _ => trivial) hxy).1

/-- A time function is increasing for the chronological relation of any open set. -/
theorem lt (h : C.IsTimeFunction T) (hxy : C.lt V x y) : T x < T y :=
  (StrongMorphism.lt_of_mapsTo h (U := ⊤) (fun _ _ => trivial) hxy).1

/-- If `x ≤_V y` and `T(V) ⊂ O`, the segment `[T x, T y]` lies in `O`. -/
theorem Icc_subset (h : C.IsTimeFunction T) {O : Opens ℝ} (hV : MapsTo T V O)
    (hxy : C.le V x y) : Icc (T x) (T y) ⊆ O :=
  (StrongMorphism.le_of_mapsTo h hV hxy).2

/-- A time function is non-decreasing along a future causal curve. -/
theorem monotoneOn (h : C.IsTimeFunction T) {c : ℝ → M} {a b : ℝ}
    (hc : C.CausalCurveOn W c a b) : MonotoneOn (T ∘ c) (Icc a b) :=
  fun _ hs _ hs' hss' => h.le (hc.le_of_le hs.1 hss' hs'.2)

/-- A time function is increasing along a future chronal curve. -/
theorem strictMonoOn (h : C.IsTimeFunction T) {c : ℝ → M} {a b : ℝ}
    (hc : C.ChronalCurveOn W c a b) : StrictMonoOn (T ∘ c) (Icc a b) :=
  fun _ hs _ hs' hss' => h.lt (hc.lt_of_lt hs.1 hss' hs'.2)

/-- A time function is a weak morphism. -/
theorem weakMorphism (h : C.IsTimeFunction T) : WeakMorphism C timelikeLine T :=
  StrongMorphism.weakMorphism h

/-- Precomposition by a strong morphism. -/
theorem comp {M' : Type*} [TopologicalSpace M'] {C' : Causality M'} {φ : M' → M}
    (h : C.IsTimeFunction T) (hφ : StrongMorphism C' C φ) : C'.IsTimeFunction (T ∘ φ) :=
  StrongMorphism.comp h hφ

/-- A time function is a time function in the reading of the order (`orderLine`). -/
theorem isTimeFunctionOrder (h : C.IsTimeFunction T) : C.IsTimeFunctionOrder T where
  continuous := h.continuous
  isOpenMap := h.isOpenMap
  map_le O V hV _ _ hxy := by
    have := StrongMorphism.map_le h O V hV hxy
    exact ⟨this.1, this.2 (left_mem_Icc.2 this.1), this.2 (right_mem_Icc.2 this.1)⟩
  map_lt O V hV _ _ hxy := by
    have := StrongMorphism.map_lt h O V hV hxy
    exact ⟨this.1, this.2 (left_mem_Icc.2 this.1.le), this.2 (right_mem_Icc.2 this.1.le)⟩

/-- Past from future (kb/0002): `-T` is a time function for the reversed causality. -/
theorem dual (h : C.IsTimeFunction T) : C.dual.IsTimeFunction (fun x => -T x) where
  continuous := h.continuous.neg
  isOpenMap := (Homeomorph.neg ℝ).isOpenMap.comp h.isOpenMap
  map_le O V hV x y hxy := by
    let O' : Opens ℝ := ⟨Neg.neg ⁻¹' (O : Set ℝ), O.isOpen.preimage continuous_neg⟩
    have := StrongMorphism.map_le h O' V hV hxy
    refine ⟨neg_le_neg this.1, fun z hz => ?_⟩
    have : -z ∈ (O' : Set ℝ) := this.2 ⟨le_neg.1 hz.2, neg_le.1 hz.1⟩
    simpa [O'] using this
  map_lt O V hV x y hxy := by
    let O' : Opens ℝ := ⟨Neg.neg ⁻¹' (O : Set ℝ), O.isOpen.preimage continuous_neg⟩
    have := StrongMorphism.map_lt h O' V hV hxy
    refine ⟨neg_lt_neg this.1, fun z hz => ?_⟩
    have : -z ∈ (O' : Set ℝ) := this.2 ⟨le_neg.1 hz.2, neg_le.1 hz.1⟩
    simpa [O'] using this

end IsTimeFunction

theorem dual_isTimeFunction : C.dual.IsTimeFunction (fun x => -T x) ↔ C.IsTimeFunction T :=
  ⟨fun h => by simpa using h.dual, IsTimeFunction.dual⟩

/-- In the reading of the order, a time function is a continuous open map, non-decreasing for
`≤_M` and increasing for `≪_M`. -/
theorem isTimeFunctionOrder_iff : C.IsTimeFunctionOrder T ↔ Continuous T ∧ IsOpenMap T ∧
    (∀ x y, C.le ⊤ x y → T x ≤ T y) ∧ (∀ x y, C.lt ⊤ x y → T x < T y) := by
  constructor
  · intro h
    exact ⟨h.continuous, h.isOpenMap,
      fun _ _ hxy => (h.map_le ⊤ ⊤ rfl hxy).1, fun _ _ hxy => (h.map_lt ⊤ ⊤ rfl hxy).1⟩
  · rintro ⟨hc, ho, hle, hlt⟩
    refine ⟨hc, ho, fun O V hV x y hxy => ?_, fun O V hV x y hxy => ?_⟩
    · have hx : T x ∈ O := by
        have := C.le_mem_left hxy; rw [← SetLike.mem_coe, hV] at this; exact this
      have hy : T y ∈ O := by
        have := C.le_mem_right hxy; rw [← SetLike.mem_coe, hV] at this; exact this
      exact ⟨hle x y (C.le_mono le_top hxy), hx, hy⟩
    · have hx : T x ∈ O := by
        have := C.lt_mem_left hxy; rw [← SetLike.mem_coe, hV] at this; exact this
      have hy : T y ∈ O := by
        have := C.lt_mem_right hxy; rw [← SetLike.mem_coe, hV] at this; exact this
      exact ⟨hlt x y (C.lt_mono le_top hxy), hx, hy⟩

/-- Along a curve in `V`, the image by a continuous `T` of the segment between the endpoints lies
in `T(V)`. -/
theorem Icc_subset_of_curveOn {r : Opens M → M → M → Prop} (hr : IsRelFamily r)
    (hT : Continuous T) {c : ℝ → M} (hc : CurveOn r V c 0 1) {O : Opens ℝ}
    (hV : MapsTo T V O) : Icc (T (c 0)) (T (c 1)) ⊆ O := by
  have hcont : ContinuousOn (T ∘ c) (Icc 0 1) := hT.comp_continuousOn (hc.continuousOn hr)
  intro z hz
  obtain ⟨s, hs, rfl⟩ := intermediate_value_Icc zero_le_one hcont hz
  exact hV (hc.mem s hs)

/-- **The two readings (b) agree on a causally arc-connected spacetime.** -/
theorem isTimeFunction_iff_order (hC : C.CausallyArcConnected) :
    C.IsTimeFunction T ↔ C.IsTimeFunctionOrder T := by
  refine ⟨IsTimeFunction.isTimeFunctionOrder, fun h => ?_⟩
  obtain ⟨hc, ho, hle, hlt⟩ := isTimeFunctionOrder_iff.1 h
  refine ⟨hc, ho, fun O V hV x y hxy => ?_, fun O V hV x y hxy => ?_⟩
  · have hmaps : MapsTo T V O := fun p hp => by
      have : p ∈ T ⁻¹' O := by rw [← hV]; exact hp
      exact this
    obtain ⟨c, hcV, rfl, rfl⟩ := ((hC V le_top _ _).1).1 hxy
    exact ⟨hle _ _ (C.le_mono le_top hxy), Icc_subset_of_curveOn C.isRelFamily_le hc hcV hmaps⟩
  · have hmaps : MapsTo T V O := fun p hp => by
      have : p ∈ T ⁻¹' O := by rw [← hV]; exact hp
      exact this
    obtain ⟨c, hcV, rfl, rfl⟩ := ((hC V le_top _ _).2).1 hxy
    exact ⟨hlt _ _ (C.lt_mono le_top hxy), Icc_subset_of_curveOn C.isRelFamily_lt hc hcV hmaps⟩

end Causality

/-- The identity of `ℝ` is a time function on the timelike line. -/
theorem timelikeLine_isTimeFunction_id : timelikeLine.IsTimeFunction id := StrongMorphism.id

/-- **The two readings (b) differ in general**: the identity is a time function on `orderLine` in
the reading of the order, and not in the reading of the timelike line. -/
theorem orderLine_id_not_isTimeFunction :
    orderLine.IsTimeFunctionOrder id ∧ ¬ orderLine.IsTimeFunction id := by
  refine ⟨StrongMorphism.id, fun h => ?_⟩
  let O : Opens ℝ := ⟨Iio 1 ∪ Ioi 2, isOpen_Iio.union isOpen_Ioi⟩
  have hxy : orderLine.le O 0 3 :=
    ⟨by norm_num, Or.inl (by norm_num : (0 : ℝ) < 1), Or.inr (by norm_num : (2 : ℝ) < 3)⟩
  have := h.Icc_subset (O := O) (fun _ hp => hp) hxy
  have h15 : (3 / 2 : ℝ) ∈ (O : Set ℝ) := this ⟨by norm_num, by norm_num⟩
  rcases h15 with h15 | h15
  · exact absurd (mem_Iio.1 h15) (by norm_num)
  · exact absurd (mem_Ioi.1 h15) (by norm_num)

/-- The timelike line `(ℝ, ≤, <)` as an object of the category of topological spacetimes. -/
def timelikeSpacetime : Spacetime.{0} where
  carrier := ℝ
  causality := timelikeLine

/-- `defi:fonction_temps`, literally: a time function on `X` is a morphism `X ⟶ (ℝ, ≤, <)` of the
category of topological spacetimes. -/
theorem isTimeFunction_iff_exists_hom (X : Spacetime.{0}) (T : X.carrier → ℝ) :
    X.causality.IsTimeFunction T ↔ ∃ f : X ⟶ timelikeSpacetime, f.1 = T :=
  ⟨fun h => ⟨⟨T, h⟩, rfl⟩, by rintro ⟨f, rfl⟩; exact f.2⟩

end TimeFunction

end Causal
