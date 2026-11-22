import Causal.GluingGeneric.Basic
import Causal.CausalIsoInvariance
import Causal.CBG.FamilyGluing
import Causal.ChronalNeighbourBridge

/-!
# Gluing in its hereditary form, generic constructions (2): pullback, transport, charts

No label of `ETT.tex` is marked by this file (target `T-abs-gluing-generic`, DEC-167 step 1a).
Cited, unmarked: `ex:open_subset` — `ETT.tex:259`, `prop:GX_espace_temps_topo` — `ETT.tex:589`.

> More generally, if $\phi:N\rightarrow M$ is a local homeomorphism onto a topological spacetime
> $M$, then $N$ carries a unique causality for which $\phi$ is a local isomorphism of topological
> spacetimes. (`ETT.tex:262`)

## What is proved (no `sorry` in this file)

* **Pullback along an open continuous map** (`Causality.pullback`, the existence half of
  `ex:open_subset`'s second sentence): if `D` is absolutely minimal on every open subset of the
  range, the pullback is hereditarily minimal (`pullback_absolutelyMinimalOn_all`); in particular
  along a local homeomorphism (`pullback_absolutelyMinimalOn_all_of_isLocalHomeomorph`) and an
  open embedding (`pullback_absolutelyMinimalOn_all_of_isOpenEmbedding`). The step is
  `pullLink_refine`.
* **The M-only form is not preserved, even along an open embedding**: the pullback along the
  inclusion of an open set `W` is the restriction to `W` as a spacetime
  (`pullback_val_absolutelyMinimalOn_iff`, `pullback_val_absolutelyMinimal_iff`), and the
  transparent-point line along `ℝ ∖ {0} → ℝ` gives a non absolutely minimal pullback
  (`transparentLine_pullback_val_not_absolutelyMinimal`).
* **Openness of the map cannot be dropped**: along the continuous bijection
  `Bool → Prop` (discrete onto Sierpiński space, not open, `not_isOpenMap_sierpinskiMap`) the
  pullback of a hereditarily minimal causality (the library's `sierpinskiCausality` of
  `Causal.ChronalNeighbourBridge`; every precausality on Sierpiński space is hereditarily minimal,
  `Precausality.absolutelyMinimalOn_prop`) is not absolutely minimal
  (`sierpinski_pullback_not_absolutelyMinimal`).
* **Transport by a homeomorphism / causal isomorphism**: both forms, both directions
  (`IsCausalIso.absolutelyMinimalOn_all_iff`, `Causality.transport_absolutelyMinimalOn_all_iff`,
  `Causality.transport_absolutelyMinimal_iff`; the M-only one for `IsCausalIso` is the library's
  `IsCausalIso.absolutelyMinimal_iff`).
* **Transport along a chart** (`Causality.chartTransport`, the local pieces of
  `prop:GX_espace_temps_topo`): hereditary on the chart images ⇒ hereditary
  (`chartTransport_absolutelyMinimalOn_all`); the M-only form fails, along the chart of an open
  subset (`chartTransport_subtypeCoe_absolutelyMinimal_iff`,
  `transparentLine_chartTransport_not_absolutelyMinimal`).

## Hypothesis checklist

| the construction | here |
|---|---|
| `ex:open_subset`: `φ` a local homeomorphism | ⚠ weakened: `φ` continuous and open, for the hereditary form; counterexample without openness |
| `N` second countable, Hausdorff | ⚠ weakened: not used |

## SCOPE (disclosed)

* The counterexamples live on subtypes (`↥realMinusZero`) and on `Bool`, `Prop`: they are the
  domains of the maps in question, not a statement indexed by a subtype of `M` (kb/0001).
* The Sierpiński witness (the space is not Hausdorff) shows the openness hypothesis of the
  pullback lemma is used, not that it fails for spacetimes.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Relation Function GluingGeneric

universe u v w

variable {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]

/-! ### Pullback along an open map -/

/-- **The refinement step.** A step of the pulled-back relation in `V` (a relation of `φ(W₀)` with
`φ` injective on `W₀ ⊆ V`) is, when `r` is absolutely minimal on the open subsets of the range and
`φ` is open, a chain of steps in the sets `V ⊓ O`, `O` in any cover `S` of an open `W ⊇ V`. -/
theorem pullLink_refine {r : Opens M → M → M → Prop} {φ : N → M} (ho : IsOpenMap φ)
    (hmem : ∀ {U : Opens M} {c d : M}, r U c d → c ∈ U ∧ d ∈ U)
    (hmin : ∀ U : Opens M, (U : Set M) ⊆ range φ → ∀ T : Set (Opens M),
      (∀ z ∈ U, ∃ O ∈ T, z ∈ O) → ∀ c d, r U c d →
        TransGen (fun c d => ∃ O ∈ T, r (U ⊓ O) c d) c d)
    {S : Set (Opens N)} {W V : Opens N} (hS : ∀ z ∈ W, ∃ O ∈ S, z ∈ O) (hV : V ≤ W) {a b : N}
    (h : PullLink r φ V a b) : TransGen (fun c d => ∃ O ∈ S, PullLink r φ (V ⊓ O) c d) a b := by
  obtain ⟨W₀, hW₀V, hinj, ha, hb, U, hU, hr⟩ := h
  let img : Opens N → Opens M := fun O => ⟨φ '' ((W₀ ⊓ O : Opens N) : Set N), ho _ (W₀ ⊓ O).isOpen⟩
  have hUr : (U : Set M) ⊆ range φ := by rw [hU]; exact image_subset_range _ _
  have hT : ∀ z ∈ U, ∃ O' ∈ img '' S, z ∈ O' := by
    intro z hz
    rw [← SetLike.mem_coe, hU] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨O, hO, hwO⟩ := hS w (hV (hW₀V hw))
    exact ⟨img O, mem_image_of_mem _ hO, ⟨w, ⟨hw, hwO⟩, rfl⟩⟩
  refine transGen_of_image (f := φ) (s := (W₀ : Set N)) ?_ ?_ ha hb (hmin U hUr _ hT _ _ hr)
  · rintro c d ⟨O', -, hcd⟩
    have hc : c ∈ U := (inf_le_left : U ⊓ O' ≤ U) (hmem hcd).1
    rw [← SetLike.mem_coe, hU] at hc
    exact hc
  · rintro x hx y hy ⟨_, ⟨O, hO, rfl⟩, hxy⟩
    have lift : ∀ z ∈ (W₀ : Set N), φ z ∈ img O → z ∈ W₀ ⊓ O := by
      intro z hz hzO
      obtain ⟨z', hz', hzz'⟩ := hzO
      have : z' = z := hinj hz'.1 hz hzz'
      subst this
      exact hz'
    have hxO := lift x hx ((hmem hxy).1).2
    have hyO := lift y hy ((hmem hxy).2).2
    refine ⟨O, hO, W₀ ⊓ O, inf_le_inf_right O hW₀V, hinj.mono inf_le_left, hxO, hyO, U ⊓ img O,
      ?_, hxy⟩
    show (U : Set M) ∩ φ '' ((W₀ : Set N) ∩ O) = φ '' ((W₀ : Set N) ∩ O)
    rw [hU]
    exact inter_eq_right.2 (image_mono inter_subset_left)

namespace Causality

/-- **Pullback, hereditary form.** Along an open continuous map `φ`, the pullback of a causality
absolutely minimal on every open subset of the range of `φ` is absolutely minimal on every open
set. -/
theorem pullback_absolutelyMinimalOn_all (D : Causality M) {φ : N → M} (hφ : Continuous φ)
    (ho : IsOpenMap φ)
    (hD : ∀ U : Opens M, (U : Set M) ⊆ range φ → D.AbsolutelyMinimalOn U) (W : Opens N) :
    (D.pullback hφ).AbsolutelyMinimalOn W := by
  intro S hS V hV x y
  have hminle : ∀ U : Opens M, (U : Set M) ⊆ range φ → ∀ T : Set (Opens M),
      (∀ z ∈ U, ∃ O ∈ T, z ∈ O) → ∀ c d, D.le U c d →
        TransGen (fun c d => ∃ O ∈ T, D.le (U ⊓ O) c d) c d :=
    fun U hU T hT c d => ((hD U hU) T hT U le_rfl c d).1
  have hminlt : ∀ U : Opens M, (U : Set M) ⊆ range φ → ∀ T : Set (Opens M),
      (∀ z ∈ U, ∃ O ∈ T, z ∈ O) → ∀ c d, D.lt U c d →
        TransGen (fun c d => ∃ O ∈ T, D.lt (U ⊓ O) c d) c d :=
    fun U hU T hT c d => ((hD U hU) T hT U le_rfl c d).2
  refine ⟨fun hxy => ?_, fun hxy => ?_⟩
  · rcases hxy with ⟨rfl, hx⟩ | hxy
    · obtain ⟨O, hO, hxO⟩ := hS x (hV hx)
      exact TransGen.single ⟨O, hO, Or.inl ⟨rfl, hx, hxO⟩⟩
    · refine transGen_flatten (fun a b hab => ?_) hxy
      refine TransGen.mono (fun c d hcd => ?_)
        (pullLink_refine ho (fun h => ⟨D.le_mem_left h, D.le_mem_right h⟩) hminle hS hV hab)
      obtain ⟨O, hO, hcd⟩ := hcd
      exact ⟨O, hO, Or.inr (TransGen.single hcd)⟩
  · refine transGen_flatten (fun a b hab => ?_) hxy
    refine TransGen.mono (fun c d hcd => ?_)
      (pullLink_refine ho (fun h => ⟨D.lt_mem_left h, D.lt_mem_right h⟩) hminlt hS hV hab)
    obtain ⟨O, hO, hcd⟩ := hcd
    exact ⟨O, hO, TransGen.single hcd⟩

/-- `ex:open_subset`, second sentence, existence, hereditary form: along a local homeomorphism the
pullback of a hereditarily minimal causality is hereditarily minimal. -/
theorem pullback_absolutelyMinimalOn_all_of_isLocalHomeomorph (D : Causality M) {φ : N → M}
    (hφ : IsLocalHomeomorph φ) (hD : ∀ U : Opens M, D.AbsolutelyMinimalOn U) (W : Opens N) :
    (D.pullback hφ.continuous).AbsolutelyMinimalOn W :=
  D.pullback_absolutelyMinimalOn_all hφ.continuous hφ.isOpenMap (fun U _ => hD U) W

/-- Along an open embedding, absolute minimality of `D` on the open subsets of the image
suffices. -/
theorem pullback_absolutelyMinimalOn_all_of_isOpenEmbedding (D : Causality M) {φ : N → M}
    (hφ : IsOpenEmbedding φ) (hD : ∀ U : Opens M, (U : Set M) ⊆ range φ → D.AbsolutelyMinimalOn U)
    (W : Opens N) : (D.pullback hφ.continuous).AbsolutelyMinimalOn W :=
  D.pullback_absolutelyMinimalOn_all hφ.continuous hφ.isOpenMap hD W

/-- The pullback along the inclusion of an open set `W` is the restriction to `W` read on `↥W`. -/
theorem pullback_val_agree (C : Causality M) (W : Opens M) (V : Opens W) (x y : W) :
    ((C.pullback continuous_subtype_val).le V x y ↔ ((C.restrict W).toSubtype).le V x y) ∧
      ((C.pullback continuous_subtype_val).lt V x y ↔ ((C.restrict W).toSubtype).lt V x y) := by
  exact C.pullback_le_lt_iff_of_injective continuous_subtype_val Subtype.val_injective
    (V := V) (U := imageOpens V) rfl x y

theorem pullback_val_absolutelyMinimalOn_iff (C : Causality M) (W : Opens M) (V : Opens W) :
    (C.pullback continuous_subtype_val).AbsolutelyMinimalOn V ↔
      C.AbsolutelyMinimalOn (imageOpens V) := by
  exact (Precausality.absolutelyMinimalOn_congr fun V' _ x y => C.pullback_val_agree W V' x y).trans
    (C.restrict_toSubtype_absolutelyMinimalOn_iff W V)

/-- **Pullback along an open embedding, M-only form**: along the inclusion of `W` it is absolute
minimality of `C` on `W`, which `C.AbsolutelyMinimal` does not give. -/
theorem pullback_val_absolutelyMinimal_iff (C : Causality M) (W : Opens M) :
    (C.pullback (continuous_subtype_val (p := (· ∈ W)))).AbsolutelyMinimal ↔
      C.AbsolutelyMinimalOn W := by
  rw [Precausality.absolutelyMinimal_iff, pullback_val_absolutelyMinimalOn_iff, imageOpens_top]

end Causality

/-- **The M-only form is not preserved by pullback along an open embedding**: the transparent-point
line is absolutely minimal, its pullback along `ℝ ∖ {0} → ℝ` is not. -/
theorem transparentLine_pullback_val_not_absolutelyMinimal :
    transparentLine.AbsolutelyMinimal ∧
      ¬ (transparentLine.pullback
        (continuous_subtype_val (p := (· ∈ realMinusZero)))).AbsolutelyMinimal := by
  exact ⟨transparentLine_absolutelyMinimal, fun h => transparentLine_not_absolutelyMinimalOn
    ((Causality.pullback_val_absolutelyMinimal_iff _ _).1 h)⟩

/-! ### Openness of the map cannot be dropped: Sierpiński space -/

/-- Every precausality on Sierpiński space `Prop` is absolutely minimal on every open set: a cover
of an open set containing a point always has a member containing the whole set. -/
theorem Precausality.absolutelyMinimalOn_prop (P : Precausality Prop) (W : Opens Prop) :
    P.AbsolutelyMinimalOn W := by
  intro S hS V hV x y
  have key : x ∈ V → ∃ O ∈ S, V ⊓ O = V := by
    intro hx
    by_cases hF : False ∈ V
    · obtain ⟨O, hO, hFO⟩ := hS False (hV hF)
      have hOu : (O : Set Prop) ∈ 𝓝 False := O.isOpen.mem_nhds hFO
      rw [nhds_false, Filter.mem_top] at hOu
      refine ⟨O, hO, inf_eq_left.2 fun z _ => ?_⟩
      show z ∈ (O : Set Prop)
      rw [hOu]
      trivial
    · have hT : ∀ z ∈ V, z = True := fun z hz => by
        by_cases h : z
        · exact eq_true h
        · have : z = False := eq_false h
          subst this
          exact absurd hz hF
      obtain ⟨O, hO, hxO⟩ := hS x (hV hx)
      refine ⟨O, hO, inf_eq_left.2 fun z hz => ?_⟩
      rw [hT z hz]
      rw [hT x hx] at hxO
      exact hxO
  refine ⟨fun hxy => ?_, fun hxy => ?_⟩
  · obtain ⟨O, hO, hVO⟩ := key (P.le_mem_left hxy)
    exact TransGen.single ⟨O, hO, by rwa [hVO]⟩
  · obtain ⟨O, hO, hVO⟩ := key (P.lt_mem_left hxy)
    exact TransGen.single ⟨O, hO, by rwa [hVO]⟩

/-- The continuous bijection from the discrete `Bool` onto Sierpiński space. -/
def sierpinskiMap : Bool → Prop := fun b => b = true

theorem continuous_sierpinskiMap : Continuous sierpinskiMap := continuous_of_discreteTopology

theorem not_isOpenMap_sierpinskiMap : ¬ IsOpenMap sierpinskiMap := by
  intro h
  have ho := h {false} (isOpen_discrete _)
  have hF : (False : Prop) ∈ sierpinskiMap '' {false} := ⟨false, rfl, eq_false Bool.false_ne_true⟩
  have hu : sierpinskiMap '' {false} ∈ 𝓝 False := ho.mem_nhds hF
  rw [nhds_false, Filter.mem_top] at hu
  have hT : (True : Prop) ∈ sierpinskiMap '' {false} := by rw [hu]; trivial
  obtain ⟨b, hb, hbT⟩ := hT
  rw [mem_singleton_iff] at hb
  subst hb
  exact Bool.false_ne_true (of_eq_true hbT)

/-- **Pullback along a continuous map which is not open**: the library's `sierpinskiCausality`
(`Causal.ChronalNeighbourBridge`) is hereditarily minimal, its pullback along `sierpinskiMap`
relates `false` to `true` in `Bool` and is not absolutely minimal (on the cover by points, every
step is trivial). -/
theorem sierpinski_pullback_not_absolutelyMinimal :
    (∀ W : Opens Prop, sierpinskiCausality.AbsolutelyMinimalOn W) ∧
      ¬ (sierpinskiCausality.pullback continuous_sierpinskiMap).AbsolutelyMinimal := by
  refine ⟨fun W => Precausality.absolutelyMinimalOn_prop _ W, fun h => ?_⟩
  rw [Precausality.absolutelyMinimal_iff] at h
  let P := sierpinskiCausality.pullback continuous_sierpinskiMap
  have hinj : InjOn sierpinskiMap ((⊤ : Opens Bool) : Set Bool) := by
    intro a _ b _ hab
    revert hab
    cases a <;> cases b <;> simp [sierpinskiMap]
  have himg : ((⊤ : Opens Prop) : Set Prop) = sierpinskiMap '' ((⊤ : Opens Bool) : Set Bool) := by
    ext p
    simp only [Opens.coe_top, mem_univ, image_univ, mem_range, true_iff]
    by_cases hp : p
    · exact ⟨true, by simp [sierpinskiMap, hp]⟩
    · exact ⟨false, by simp [sierpinskiMap, hp]⟩
  have hle : P.le ⊤ false true := Or.inr (TransGen.single
    ⟨⊤, le_rfl, hinj, trivial, trivial, ⊤, himg, Or.inr rfl⟩)
  let S : Set (Opens Bool) := range fun b : Bool => (⟨{b}, isOpen_discrete _⟩ : Opens Bool)
  have hS : ∀ z ∈ (⊤ : Opens Bool), ∃ O ∈ S, z ∈ O := fun z _ => ⟨_, ⟨z, rfl⟩, rfl⟩
  have key : ∀ a b : Bool, TransGen (fun a b => ∃ O ∈ S, P.le (⊤ ⊓ O) a b) a b → a = b := by
    intro a b hab
    induction hab with
    | @single b' hl =>
      obtain ⟨_, ⟨c, rfl⟩, hl⟩ := hl
      have h1 : a = c := (P.le_mem_left hl).2
      have h2 : b' = c := (P.le_mem_right hl).2
      exact h1.trans h2.symm
    | @tail b' c' _ hl ih =>
      obtain ⟨_, ⟨c, rfl⟩, hl⟩ := hl
      have h1 : b' = c := (P.le_mem_left hl).2
      have h2 : c' = c := (P.le_mem_right hl).2
      exact ih.trans (h1.trans h2.symm)
  exact Bool.false_ne_true (key _ _ ((h S hS ⊤ le_top false true).1 hle))

/-! ### Transport by a homeomorphism -/

/-- **Causal isomorphisms preserve the hereditary form, both ways.** -/
theorem IsCausalIso.absolutelyMinimalOn_all_iff {C : Causality M} {D : Causality N} {e : M ≃ₜ N}
    (h : IsCausalIso C D e) :
    (∀ W : Opens M, C.AbsolutelyMinimalOn W) ↔ ∀ W : Opens N, D.AbsolutelyMinimalOn W := by
  constructor
  · intro hC W
    have := h.absolutelyMinimalOn (hC (e.symm.opensCongr W))
    rwa [opensCongr_symm_opensCongr] at this
  · intro hD W
    exact h.absolutelyMinimalOn_iff.2 (hD _)

theorem Causality.transport_absolutelyMinimalOn_all_iff (C : Causality M) (e : M ≃ₜ N) :
    (∀ W : Opens N, (C.transport e).AbsolutelyMinimalOn W) ↔
      ∀ W : Opens M, C.AbsolutelyMinimalOn W :=
  (isCausalIso_transport C e).absolutelyMinimalOn_all_iff.symm

theorem Causality.transport_absolutelyMinimal_iff (C : Causality M) (e : M ≃ₜ N) :
    (C.transport e).AbsolutelyMinimal ↔ C.AbsolutelyMinimal :=
  (isCausalIso_transport C e).absolutelyMinimal_iff.symm

/-! ### Transport along a chart -/

namespace Causality

variable {X : Type w} [TopologicalSpace X]

/-- **Chart transport, hereditary form**: the causality of the model transported along a chart is
hereditarily minimal when the model is absolutely minimal on the images of the open subsets of the
source. -/
theorem chartTransport_absolutelyMinimalOn_all (D : Causality X) (e : OpenPartialHomeomorph M X)
    (hD : ∀ W : Opens M, W ≤ chartSource e → D.AbsolutelyMinimalOn (chartImage e W))
    (W : Opens M) : (D.chartTransport e).AbsolutelyMinimalOn W :=
  LocalCausality.extend_absolutelyMinimalOn_all (chartLocal D e)
    (fun W' hW' => (D.chartTransport_chartIso e).absolutelyMinimalOn hW' (hD W' hW')) W

/-- Along the chart of an open subset `W` of the model, the transported causality is the
restriction of the model to `W`, read on `↥W`. -/
theorem chartTransport_subtypeCoe_agree (D : Causality X) (W : Opens X) (hW : Nonempty W)
    (V : Opens W) (x y : W) :
    ((D.chartTransport (W.openPartialHomeomorphSubtypeCoe hW)).le V x y ↔
        ((D.restrict W).toSubtype).le V x y) ∧
      ((D.chartTransport (W.openPartialHomeomorphSubtypeCoe hW)).lt V x y ↔
        ((D.restrict W).toSubtype).lt V x y) := by
  set e := W.openPartialHomeomorphSubtypeCoe hW with he_def
  have he : ∀ z : W, e z = z.1 := fun z => by simp [e]
  have hsrc : V ≤ chartSource e := fun z _ => by simp [chartSource, e]
  have hiso := D.chartTransport_chartIso e V hsrc
  have himg : chartImage e V = imageOpens V := by
    apply SetLike.coe_injective
    rw [coe_chartImage_of_le hsrc]
    ext p
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, (he z).symm⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, he z⟩
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
  · have := ((hiso x ((D.chartTransport e).le_mem_left h) y
      ((D.chartTransport e).le_mem_right h)).1).1 h
    rw [himg, he, he] at this
    exact this
  · have hx : x ∈ V := ((D.restrict W).toSubtype).le_mem_left h
    have hy : y ∈ V := ((D.restrict W).toSubtype).le_mem_right h
    refine ((hiso x hx y hy).1).2 ?_
    rw [himg, he, he]
    exact h
  · have := ((hiso x ((D.chartTransport e).lt_mem_left h) y
      ((D.chartTransport e).lt_mem_right h)).2).1 h
    rw [himg, he, he] at this
    exact this
  · have hx : x ∈ V := ((D.restrict W).toSubtype).lt_mem_left h
    have hy : y ∈ V := ((D.restrict W).toSubtype).lt_mem_right h
    refine ((hiso x hx y hy).2).2 ?_
    rw [himg, he, he]
    exact h

/-- **Chart transport, M-only form**: along the chart of `W` it is absolute minimality of the
model on `W`, which the model's absolute minimality does not give. -/
theorem chartTransport_subtypeCoe_absolutelyMinimal_iff (D : Causality X) (W : Opens X)
    (hW : Nonempty W) :
    (D.chartTransport (W.openPartialHomeomorphSubtypeCoe hW)).AbsolutelyMinimal ↔
      D.AbsolutelyMinimalOn W := by
  exact Precausality.absolutelyMinimal_iff.trans
    ((Precausality.absolutelyMinimalOn_congr fun V _ x y =>
      chartTransport_subtypeCoe_agree D W hW V x y).trans
      (Precausality.absolutelyMinimal_iff.symm.trans
        (Causality.restrict_toSubtype_absolutelyMinimal_iff D W)))

end Causality

/-- The chart `ℝ ∖ {0} → ℝ` of the transparent-point line transports an absolutely minimal
causality to a non absolutely minimal one. -/
theorem transparentLine_chartTransport_not_absolutelyMinimal :
    transparentLine.AbsolutelyMinimal ∧
      ¬ (transparentLine.chartTransport
        (realMinusZero.openPartialHomeomorphSubtypeCoe ⟨⟨1, one_ne_zero⟩⟩)).AbsolutelyMinimal := by
  exact ⟨transparentLine_absolutelyMinimal, fun h => transparentLine_not_absolutelyMinimalOn
    ((Causality.chartTransport_subtypeCoe_absolutelyMinimal_iff _ _ _).1 h)⟩

end Causal
