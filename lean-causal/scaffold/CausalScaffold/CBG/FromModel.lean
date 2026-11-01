import CausalScaffold.CBG.Geometry
import CausalScaffold.GXSingular
import CausalScaffold.CBG.FamilyGluing

/-!
# Level B ⇒ Level A: the geometry of a local model (`Geometry.ofLocalModel`)

Package 11 of the CBG campaign (design `docs/CBG-DESIGN.md` §2 "`Geometry.ofLocalModel :
Level B → Level A`", §5 row 11). No paper label is marked. Cited, unmarked: `theo:CBG` —
`ETT.tex:1884`; `cor:ext_continue` — `ETT.tex:2144`; `cor:model_corresponding` — `ETT.tex:2158`;
`theo:causalite_engendre` — `ETT.tex:514`; `prop:GX_espace_temps_topo` — `ETT.tex:589`;
`prop:GX_sing_espace_temps_topo` — `ETT.tex:616` (the singular form, `Y = 𝕄 ⊕ Σ 𝔼_α`); thesis
`prop:GX_liouville` (`these.tex:1476`), `def:singular_GX` (`these.tex:3040`); Sbierski 1309.7591,
Lemma 3.8, Thm 3.6.

> $\mass{\geq0}$-morphism means a map which reads as an element of $\isom(\mass{})$ in the charts
> of Section \ref{subsec:sing_spacetime_defi}; such a map is in particular a local homeomorphism
> and a morphism of topological spacetimes. (`ETT.tex:1852–1854`)

> Soient $(M_1,\A), (M_2,\B)$ deux $(G,X)$-variétés et soient $f_1,f_2:M_1 \rightarrow M_2$ deux
> morphismes de $(G,X)$-variétés. Si $M_1$ est connexe et s'il existe un ouvert non vide $\U$ de
> $M_1$ tel que ${f_1}_{|\U}={f_2}_{|\U}$ alors $f_1=f_2$. (`prop:GX_liouville`,
> `these.tex:1476–1480`)

> Lemma 3.8. Let U be a CGHD of M and M′ with isometric embedding ψ : U ⊆ M → M′. Then the set C
> is open in ∂U and the isometric embedding ψ : U → M′ extends smoothly to ψ : U ∪ C → M′.
> (Sbierski, p. 16)

> Let $(p,q)\in C$. Then $f$ extends continuously to $p$ by setting $f(p)=q$.
> (`cor:ext_continue`, `ETT.tex:2144–2146`)

## What is proved (no `sorry`)

* **The morphism calculus** of `LiftPropOn G.IsLocalStructomorphWithinAt` over any structure
  groupoid closed under restriction, through the *forward local form* `RepOn` (`chartAt (f x) ∘ f
  = e ∘ chartAt x` on an open set, `e ∈ G`; `liftPropOn_iff_repOn`): the sheaf laws
  `liftPropOn_mono_of_le`, `liftPropOn_of_locally`, `liftPropOn_id`, `liftPropOn_congr_of_eqOn`,
  `liftPropOn_comp`; the inverse `liftPropOn_invFunOn`; chart independence
  `liftPropOn_of_maximalAtlas_rep`; **A1 from B1** `eqOn_of_liftPropOn` (open–closed argument,
  `LocallyConnectedSpace Y`, Hausdorff target).
* **The generated causality of the atlas**: preferred charts are `ChartIso`s
  (`chartedCausality_chartIso`, from B3 `chartIso_mem` and `absolutelyMinimalOn_Y`), absolute
  minimality on every open set (`chartedCausality_absolutelyMinimalOn`); **every Level-B morphism
  is an `IsEMorphismOn`** (`isEMorphismOn_of_liftPropOn`: local isomorphism by three `ChartIso`s,
  strong-morphism half by absolute minimality); morphisms preserve `sing_α`
  (`mem_chartedSing_iff_of_liftPropOn`, B3 `sing_mem`).
* **Restriction** (mathlib's `Opens` charted space, `ClosedUnderRestriction`), **transport**
  along a homeomorphism (`transportChartedSpace`, `transport_hasGroupoid`,
  `liftPropOn_transport`), **gluing** along open embeddings covering `Z` (`gluedChartedSpace`,
  `gluedChartedSpace_hasGroupoid`, `liftPropOn_glue`; transitions `glueTransition`) and its
  **public `FamilyGlueData` form for gx's B21 Lemma 2.3** (gx review C5):
  `FamilyGlueData.chartedSpace`, `FamilyGlueData.hasGroupoid_chartedSpace`,
  `FamilyGlueData.liftPropOn_ι`, `FamilyGlueData.glueTransition_eq` (the canonical transition is
  `φ i j`), `FamilyGlueData.preimage_ι_range_ι`, and the wrappers
  `FamilyGlueData.hasGroupoid_chartedSpace_of_eqOn`/`liftPropOn_ι_of_eqOn` (transitions given by
  any morphism agreeing with `φ i j` on `U i j`).
* `Geometry.ofLocalModelOfGermSlice 𝔐 hA3f hA3p hA4f hA4p : Geometry`: **every field of Level A
  except A3/A4 derived from Level B** — interface round 2's `timeFunction` included, from
  `LocalModel.timeFunction` — A3/A4 taken as the hypotheses `𝔐.GermExtFuture`,
  `GermExtPast`, `SliceFuture`, `SlicePast` (the Level A field types read on `𝔐`).
* The B2 step of A3 with the connectedness made a hypothesis:
  `LocalModel.exists_eqOn_of_connected_reg` (B2 `localUnique_reg`, any maximal-atlas charts),
  `LocalModel.exists_eqOn_of_connected_sing` (B2 `localUnique_sing`),
  `LocalModel.exists_eqOn_of_connected_sing_adherent` (round 2's past-side B2
  `localUnique_sing_adherent`, its largeness clause a hypothesis, passed verbatim),
  `LocalModel.mapClusterPt_chart` (Def 3.5 read in charts),
  `LocalModel.exists_extension_of_eqOn` (one element of `G` ⇒ a morphism extending `ψ`).
* **The shape of A3's past-side piece**: `Causality.CausallyConvexIn.Iplus_inter_Iminus_subset`
  (`U ∩ I⁻_W(r) ⊇ I⁺_W(p) ∩ I⁻_W(r)` for `U` causally convex, `p ∈ closure U`, `r ∈ U`; model-free)
  and its chart reading `chartedCausality_image_Iplus_inter_Iminus`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `prop:GX_espace_temps_topo` (`ETT.tex:589–595`) and its singular form `prop:GX_sing_espace_temps_topo` (`ETT.tex:616–624`): `(G,X)` (resp. `(G,X,X_A)`) analytic, `X` (and each `X_α`) a causally arc-connected (Baire) spacetime, `G` acting by morphisms | ⚠ strengthened (the paper's hypotheses are replaced by two of its consequences, asked directly; see SCOPE): every `e ∈ G` is a `ChartIso D D e` and `D` is absolutely minimal on every open set (B3 `chartIso_mem`, `absolutelyMinimalOn_Y`). This is a different hypothesis, not a subset of the paper's: analyticity, arc-connectedness and Baire are what the paper's route uses to reach these two facts, and here the facts are asked directly. Only the preferred charts are proved isomorphisms (`chartedCausality_chartIso`); uniqueness is not redone |
| `ETT.tex:1852–1854`: a map reading as an element of `Isom` in the charts is a local homeomorphism and a morphism | ✓ carried (`isEMorphismOn_of_liftPropOn`: local isomorphism by three `ChartIso`s, strong-morphism half by absolute minimality) |
| `cor:model_corresponding` (`ETT.tex:2158–2160`), type of a corresponding point | ⚠ weakened (reading): only the morphism half, i.e. a Level-B morphism preserves `sing_α` (`mem_chartedSing_iff_of_liftPropOn`, from B3 `sing_mem`). The statement about corresponding boundary points is package 5's (`CGHDData.mem_sing_iff`) |
| `prop:GX_liouville` (`these.tex:1476–1480`): `M₁` connected, `f₁ = f₂` on a non-empty open set | ⚠ strengthened: model rigidity B1 (in place of analyticity), `LocallyConnectedSpace Y`, target `T2` (Level A asks it) |
| design §2: sheaf laws, identity, composition, congruence, `inv`, `restrict`, `corestrict`, `transport` | ✓ carried (derived from Level B, `ClosedUnderRestriction G`) |
| design §2: `glue` | ✓ carried; the construction glues the non-empty pieces (an empty piece embeds vacuously) |
| design §2: `sing`, `isMor_sing`, A2 fields | ✓ carried (`LocalModel.sing`, B3 `sing_mem`; the B3 fields read through `s.1`, `s.2`) |
| design §2: A3 (`germExt_*`) from B2 + `regularChart` | ⚠ strengthened: not derived. `ofLocalModelOfGermSlice` takes `GermExtFuture`/`GermExtPast` as hypotheses; in `ofLocalModel` they are `sorry`. The B2 step is proved with the connected piece as a hypothesis (both sides; the past-side BTZ case with round 2's clause as a hypothesis). The field states A3 for carriers **not** assumed second countable, while every B3 fact is (SCOPE) |
| design §2: A4 (`slice_*`) from B4 | ⚠ strengthened: not derived. Taken as `SliceFuture`/`SlicePast` in `ofLocalModelOfGermSlice`, `sorry` in `ofLocalModel` (Sbierski Thm 3.6's geometric half, package 6) |

## SCOPE (disclosed)

* `Geometry.ofLocalModel 𝔐 := ofLocalModelOfGermSlice 𝔐 …` rests on the four tagged `sorry`s
  A3/A4; a downstream instance proving them for its model (package 12, gx) should use
  `ofLocalModelOfGermSlice`, which is sorry-free.
* **A3 and connectedness (the design risk).** B2 is stated for a map on a *connected* open set
  (`localUnique_reg`) or on `reg(U')`, `U'` a connected open set through a singular point
  (`localUnique_sing`). For a CGHD `U` and a chart neighbourhood `W` of `p ∈ ∂U`, `U ∩ W` need not
  be connected. The connected piece Sbierski's proof uses is `U ∩ W ∩ J⁺_W(r)` (`r ∈ U` below
  `p`): connected through causal curves from `r` (A2 `causallyArcConnected` on every open set)
  that stay in `U` (causal convexity of a Cauchy inclusion, package 2,
  `causallyConvexIn_of_isCauchySurfaceOn`), and `ψ` of it lies near `q` by Prop 3.7 (package 5).
  At a regular `p` this then closes by `exists_eqOn_of_connected_reg` + `regularChart` +
  `exists_extension_of_eqOn`. At a **BTZ** `p` (`I⁻(p) = ∅`), the future side needs a singular
  point of `p`'s line below `p` in `U` (thesis `lem:passe_pgcd`, `these.tex:6541`); on the past side
  the connected piece `U ∩ I⁻_W(r)` can be a regular set adherent to `p` which is not `reg` of a
  neighbourhood: `localUnique_sing` needs `f` on all of `reg(U')`, `localUnique_reg` a fully
  regular component, and round 2's `localUnique_sing_adherent` a largeness clause this piece meets
  only vacuously (next bullets).
* **A4** is Sbierski's slice construction (Lemma 3.11, the maximum of `τ` on the compact
  `J⁻(q) ∩ Uᶜ ∩ J⁺(Σ)`, the GH open of B4, GH of `U ∪ N`); B4 supplies only the local `τ`, and its
  transport to `M` by `chartedCausality_chartIso` is the only Level-B part.
* **`prop:GX_espace_temps_topo` / `prop:GX_sing_espace_temps_topo` are read, not proved.** The
  paper's hypotheses (analyticity, causal arc-connectedness, Baire, `G` acting by morphisms; for the
  singular form, (b) on each `X_α`) are not assumed; their two consequences used by the proof —
  every `e ∈ G` is a `ChartIso D D e`, `D` absolutely minimal on every open set — are B3 fields
  (`chartIso_mem`, `absolutelyMinimalOn_Y`). This is a different hypothesis, not a subset of the
  paper's (verdict `⚠ strengthened` in the checklist). Only the preferred charts are proved
  isomorphisms; uniqueness is not redone (`Causal/GXStructure.lean` has it for `gxGroupoid`).
* **The round-2 past-side largeness clause is vacuous as transcribed** (design §6 "Interface
  round 2" (2), now `LocalModel.localUnique_sing_adherent` in `Geometry.lean`):
  `∃ r ∈ O, y₀ ≤_O r ∧ reg ∩ I⁻_O(r) ⊆ U`
  holds for every `U`, by `r := y₀` (`Causality.BTZAxiomsCorr.exists_le_inter_Iminus_subset`),
  because the chronological past of every BTZ point is empty in every open set
  (`Causality.BTZAxiomsCorr.Iminus_opens_eq_empty`, from `Iminus_eq_empty` and `lt_mono`); the same
  holds for any `r` on `y₀`'s line (`inter_Iminus_opens_subset`). With `≪` in place of `≤` the
  clause asks `U ⊇ reg(I⁻_O(r))` for an open neighbourhood `I⁻_O(r)` of `y₀`, the case
  `localUnique_sing` already covers (by hand). **`germExtPast` does not use the field through
  this vacuity.** The piece A3-past produces at a BTZ `p` is `U ∩ I⁻_W(r)`, `r ∈ U` regular above
  `p`, which contains the chronological diamond `I⁺_W(p) ∩ I⁻_W(r)` and in gx's example is that
  diamond near `p`; with `r` regular and `y₀ ≪_O r` the clause fails for it (by hand,
  `germExtPast`'s `SORRY`). The clause it does meet is the diamond form
  `∃ r ∈ O, y₀ ≪_O r ∧ reg ∩ I⁺_O(y₀) ∩ I⁻_O(r) ⊆ U` (REPORT, message for gx).
* **A3 and A4 carry no second countability, Level B's facts all do.** `germExt_*`/`slice_*` (and
  so `GermExtFuture`, …) quantify over `T2`, connected `M`, `N`; every B3 field the derivation
  consumes (`singularFlatAxioms`, `curvesExtend`, `timeFunction`, `isCompact_*`) asks
  `[SecondCountableTopology M]`, and `secondCountable_of_cauchy` needs a second-countable Cauchy
  surface, which A3/A4 do not give. So A3/A4 as stated are not derivable from Level B by
  Sbierski's route, independently of the work; the repair is an interface change (add the
  second countability of `M`, `N` to A3 and of `M` to A4), not this file's.
* `Geometry`/`LocalModel` still have no inhabitant (kb/0011, kb/0012): this file proves the
  derivation, not satisfiability; the flat check is package 12.
* `glue` field: Level A's `glue` does not require the pieces non-empty; the construction glues
  the non-empty ones (an empty piece embeds vacuously).
* **The exported `FamilyGlueData` form (gx review C5) has two constraints gx's B21 Lemma 2.3
  must bridge.** (i) It asks `[∀ i, Nonempty (M i)]` (the inverse of an open embedding as an
  `OpenPartialHomeomorph` needs a junk value); a family with empty pieces must first drop them,
  as the Level A `glue` field does internally. (ii) The transition hypothesis of
  `hasGroupoid_chartedSpace`/`liftPropOn_ι` is `LiftPropOn` of the canonical extension
  `glueTransition D.isOpenEmbedding_ι i j` on `D.U i j`, not of `D.φ i j` (a map on the subtype);
  `glueTransition_eq` links the two on `D.U i j`, and the wrappers
  `hasGroupoid_chartedSpace_of_eqOn`/`liftPropOn_ι_of_eqOn` take instead any morphism `φ' i j`
  on `D.U i j` agreeing with `D.φ i j` there (`liftPropOn_glueTransition_of_eqOn`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set Topology Filter Function TopologicalSpace ChartedSpace StructureGroupoid

universe u

namespace CBG

/-! ### The morphism calculus of `LiftPropOn G.IsLocalStructomorphWithinAt` -/

section Calculus

variable {Y : Type*} [TopologicalSpace Y] {G : StructureGroupoid Y}
  {M : Type*} {N : Type*} {P : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [TopologicalSpace P] [ChartedSpace Y M] [ChartedSpace Y N] [ChartedSpace Y P]

variable (G) in
/-- **The forward local form of a morphism**: on the open set `O ∋ x`, read in the preferred
charts at `x` and `f x`, `f` is one element `e` of `G`: `chartAt (f x) ∘ f = e ∘ chartAt x` on
`O`. No `symm` of a chart is evaluated, so no junk value enters. -/
def RepOn (f : M → N) (O : Set M) (x : M) : Prop :=
  IsOpen O ∧ O ⊆ (chartAt Y x).source ∧ MapsTo f O (chartAt Y (f x)).source ∧ ContinuousOn f O ∧
    ∃ e ∈ G, MapsTo (chartAt Y x) O e.source ∧
      ∀ z ∈ O, chartAt Y (f x) (f z) = e (chartAt Y x z)

theorem RepOn.mono {f : M → N} {O O' : Set M} {x : M} (h : RepOn G f O x) (hO' : IsOpen O')
    (hle : O' ⊆ O) : RepOn G f O' x := by
  obtain ⟨-, hs, hm, hc, e, he, hme, heq⟩ := h
  exact ⟨hO', hle.trans hs, hm.mono_left hle, hc.mono hle, e, he, hme.mono_left hle,
    fun z hz => heq z (hle hz)⟩

/-- `LiftPropOn G.IsLocalStructomorphWithinAt` on an open set is the forward local form at every
point. -/
theorem liftPropOn_iff_repOn [ClosedUnderRestriction G] {f : M → N} {W : Set M} (hW : IsOpen W) :
    LiftPropOn G.IsLocalStructomorphWithinAt f W ↔
      ∀ x ∈ W, ∃ O, x ∈ O ∧ O ⊆ W ∧ RepOn G f O x := by
  constructor
  · intro h x hx
    have hcont : ContinuousOn f W := fun y hy => (h y hy).continuousWithinAt
    obtain ⟨-, hprop⟩ := h x hx
    set c := chartAt Y x
    set c' := chartAt Y (f x)
    obtain ⟨e, he, heq, hxe⟩ := hprop (show c.symm (c x) ∈ W by rw [c.left_inv (mem_chart_source Y x)]; exact hx)
    refine ⟨W ∩ f ⁻¹' c'.source ∩ (c.source ∩ c ⁻¹' e.source),
      ⟨⟨hx, mem_chart_source Y (f x)⟩, mem_chart_source Y x, hxe⟩,
      fun z hz => hz.1.1, ?_⟩
    have hopen : IsOpen (W ∩ f ⁻¹' c'.source ∩ (c.source ∩ c ⁻¹' e.source)) :=
      (hcont.isOpen_inter_preimage hW c'.open_source).inter (c.isOpen_inter_preimage e.open_source)
    refine ⟨hopen, fun z hz => hz.2.1, fun z hz => hz.1.2, hcont.mono fun z hz => hz.1.1, e, he,
      fun z hz => hz.2.2, fun z hz => ?_⟩
    have hzc : c.symm (c z) = z := c.left_inv hz.2.1
    have := heq ⟨show c.symm (c z) ∈ W by rw [hzc]; exact hz.1.1, hz.2.2⟩
    simp only [comp_apply, hzc] at this
    exact this
  · intro h x hx
    obtain ⟨O, hxO, hOW, hO, hs, hm, hc, e, he, hme, heq⟩ := h x hx
    refine ⟨(hc.continuousAt (hO.mem_nhds hxO)).continuousWithinAt, fun _ => ?_⟩
    set c := chartAt Y x
    have hcO : IsOpen (c '' O) := c.isOpen_image_of_subset_source hO hs
    refine ⟨e.restr (c '' O), closedUnderRestriction' he hcO, ?_, ?_⟩
    · rintro y ⟨-, hye, hyO⟩
      rw [hcO.interior_eq] at hyO
      obtain ⟨z, hz, rfl⟩ := hyO
      simp only [comp_apply, c.left_inv (hs hz)]
      exact heq z hz
    · refine ⟨hme hxO, ?_⟩
      rw [hcO.interior_eq]
      exact mem_image_of_mem _ hxO

/-- Sheaf law, restriction. -/
theorem liftPropOn_mono_of_le [ClosedUnderRestriction G] {f : M → N} {W W' : Set M}
    (hW : IsOpen W) (hW' : IsOpen W') (h : LiftPropOn G.IsLocalStructomorphWithinAt f W)
    (hle : W' ⊆ W) : LiftPropOn G.IsLocalStructomorphWithinAt f W' := by
  rw [liftPropOn_iff_repOn hW] at h
  rw [liftPropOn_iff_repOn hW']
  intro x hx
  obtain ⟨O, hxO, -, hO⟩ := h x (hle hx)
  exact ⟨O ∩ W', ⟨hxO, hx⟩, inter_subset_right, hO.mono (hO.1.inter hW') inter_subset_left⟩

/-- Sheaf law, locality. -/
theorem liftPropOn_of_locally [ClosedUnderRestriction G] {f : M → N} {W : Set M} (hW : IsOpen W)
    (h : ∀ x ∈ W, ∃ V : Set M, IsOpen V ∧ V ⊆ W ∧ x ∈ V ∧
      LiftPropOn G.IsLocalStructomorphWithinAt f V) :
    LiftPropOn G.IsLocalStructomorphWithinAt f W := by
  rw [liftPropOn_iff_repOn hW]
  intro x hx
  obtain ⟨V, hV, hVW, hxV, hf⟩ := h x hx
  obtain ⟨O, hxO, hOV, hO⟩ := (liftPropOn_iff_repOn hV).1 hf x hxV
  exact ⟨O, hxO, hOV.trans hVW, hO⟩

/-- Sheaf law, identity. -/
theorem liftPropOn_id [ClosedUnderRestriction G] {W : Set M} (hW : IsOpen W) :
    LiftPropOn G.IsLocalStructomorphWithinAt (id : M → M) W := by
  rw [liftPropOn_iff_repOn hW]
  intro x hx
  refine ⟨W ∩ (chartAt Y x).source, ⟨hx, mem_chart_source Y x⟩, inter_subset_left,
    hW.inter (chartAt Y x).open_source, fun z hz => hz.2, fun z hz => hz.2,
    continuousOn_id, OpenPartialHomeomorph.refl Y, G.id_mem, fun _ _ => trivial, fun z _ => rfl⟩

/-- Sheaf law, congruence. -/
theorem liftPropOn_congr_of_eqOn [ClosedUnderRestriction G] {f g : M → N} {W : Set M}
    (hW : IsOpen W) (h : LiftPropOn G.IsLocalStructomorphWithinAt f W) (hfg : EqOn f g W) :
    LiftPropOn G.IsLocalStructomorphWithinAt g W := by
  rw [liftPropOn_iff_repOn hW] at h ⊢
  intro x hx
  obtain ⟨O, hxO, hOW, hO, hs, hm, hc, e, he, hme, heq⟩ := h x hx
  have hgx : g x = f x := (hfg hx).symm
  refine ⟨O, hxO, hOW, hO, hs, fun z hz => ?_, hc.congr fun z hz => (hfg (hOW hz)).symm, e, he,
    hme, fun z hz => ?_⟩
  · rw [hgx, ← hfg (hOW hz)]; exact hm hz
  · rw [hgx, ← hfg (hOW hz)]; exact heq z hz

/-- Sheaf law, composition. -/
theorem liftPropOn_comp [ClosedUnderRestriction G] {f : M → N} {g : N → P} {W : Set M}
    {V : Set N} (hW : IsOpen W) (hV : IsOpen V) (hg : LiftPropOn G.IsLocalStructomorphWithinAt g V)
    (hf : LiftPropOn G.IsLocalStructomorphWithinAt f W) (hmaps : MapsTo f W V) :
    LiftPropOn G.IsLocalStructomorphWithinAt (g ∘ f) W := by
  rw [liftPropOn_iff_repOn hW] at hf ⊢
  rw [liftPropOn_iff_repOn hV] at hg
  intro x hx
  obtain ⟨O₁, hxO₁, hO₁W, hO₁, hs₁, hm₁, hc₁, e₁, he₁, hme₁, heq₁⟩ := hf x hx
  obtain ⟨O₂, hxO₂, hO₂V, hO₂, hs₂, hm₂, hc₂, e₂, he₂, hme₂, heq₂⟩ := hg (f x) (hmaps hx)
  have hO : IsOpen (O₁ ∩ f ⁻¹' O₂) := hc₁.isOpen_inter_preimage hO₁ hO₂
  refine ⟨O₁ ∩ f ⁻¹' O₂, ⟨hxO₁, hxO₂⟩, fun z hz => hO₁W hz.1, hO, fun z hz => hs₁ hz.1,
    fun z hz => hm₂ hz.2, hc₂.comp (hc₁.mono inter_subset_left) (fun z hz => hz.2),
    e₁.trans e₂, G.trans he₁ he₂, fun z hz => ?_, fun z hz => ?_⟩
  · refine ⟨hme₁ hz.1, ?_⟩
    show e₁ (chartAt Y x z) ∈ e₂.source
    rw [← heq₁ z hz.1]
    exact hme₂ hz.2
  · show chartAt Y (g (f x)) (g (f z)) = e₂ (e₁ (chartAt Y x z))
    rw [heq₂ (f z) hz.2, heq₁ z hz.1]

/-- **The forward local form in any charts of the maximal atlases**: if, on an open `O`, a map
read in charts `κ`, `κ'` of the maximal atlases is one element `g` of `G`, it is a morphism on
`O`. For instances (package 12): a morphism may be checked in any compatible charts. -/
theorem liftPropOn_of_maximalAtlas_rep [ClosedUnderRestriction G] [HasGroupoid M G]
    [HasGroupoid N G] {κ : OpenPartialHomeomorph M Y} {κ' : OpenPartialHomeomorph N Y}
    (hκ : κ ∈ G.maximalAtlas M) (hκ' : κ' ∈ G.maximalAtlas N) {f : M → N} {O : Set M}
    (hO : IsOpen O) (hOs : O ⊆ κ.source) (hm : MapsTo f O κ'.source) (hc : ContinuousOn f O)
    {g : OpenPartialHomeomorph Y Y} (hg : g ∈ G) (hmg : MapsTo κ O g.source)
    (heq : ∀ z ∈ O, κ' (f z) = g (κ z)) : LiftPropOn G.IsLocalStructomorphWithinAt f O := by
  have hG := isLocalStructomorphWithinAt_localInvariantProp G
  intro x hx
  rw [hG.liftPropWithinAt_indep_chart hκ (hOs hx) hκ' (hm hx)]
  refine ⟨hc x hx, fun _ => ?_⟩
  have hκO : IsOpen (κ '' O) := κ.isOpen_image_of_subset_source hO hOs
  refine ⟨g.restr (κ '' O), closedUnderRestriction' hg hκO, ?_, hmg hx, ?_⟩
  · rintro y ⟨-, -, hyO⟩
    rw [hκO.interior_eq] at hyO
    obtain ⟨z, hz, rfl⟩ := hyO
    simp only [comp_apply, κ.left_inv (hOs hz)]
    exact heq z hz
  · rw [hκO.interior_eq]; exact mem_image_of_mem _ hx

/-- The image of a forward-local-form set is open. -/
theorem RepOn.isOpen_image {f : M → N} {O : Set M} {x : M} (h : RepOn G f O x) :
    IsOpen (f '' O) := by
  obtain ⟨hO, hs, hm, -, e, -, hme, heq⟩ := h
  set c := chartAt Y x
  set c' := chartAt Y (f x)
  have h1 : IsOpen (c '' O) := c.isOpen_image_of_subset_source hO hs
  have h2 : IsOpen (e '' (c '' O)) :=
    e.isOpen_image_of_subset_source h1 (by rintro _ ⟨z, hz, rfl⟩; exact hme hz)
  have : f '' O = c'.source ∩ c' ⁻¹' (e '' (c '' O)) := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨hm hz, chartAt Y x z, ⟨z, hz, rfl⟩, (heq z hz).symm⟩
    · rintro ⟨hw, _, ⟨z, hz, rfl⟩, hwz⟩
      refine ⟨z, hz, c'.injOn (hm hz) hw ?_⟩
      rw [heq z hz, hwz]
  rw [this]
  exact c'.isOpen_inter_preimage h2

/-- `f` is injective on a forward-local-form set. -/
theorem RepOn.injOn {f : M → N} {O : Set M} {x : M} (h : RepOn G f O x) : InjOn f O := by
  obtain ⟨-, hs, -, -, e, -, hme, heq⟩ := h
  intro a ha b hb hab
  have : e (chartAt Y x a) = e (chartAt Y x b) := by rw [← heq a ha, ← heq b hb, hab]
  exact (chartAt Y x).injOn (hs ha) (hs hb) (e.injOn (hme ha) (hme hb) this)

/-- **Inverse** of an injective morphism, on the image. -/
theorem liftPropOn_invFunOn [ClosedUnderRestriction G] [Nonempty M] {f : M → N} {W : Set M}
    (hW : IsOpen W) (hf : LiftPropOn G.IsLocalStructomorphWithinAt f W) (hinj : InjOn f W) :
    LiftPropOn G.IsLocalStructomorphWithinAt (invFunOn f W) (f '' W) := by
  have hrep := (liftPropOn_iff_repOn hW).1 hf
  have hW' : IsOpen (f '' W) := by
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨O, hxO, hOW, hO⟩ := hrep x hx
    exact mem_of_superset (hO.isOpen_image.mem_nhds (mem_image_of_mem f hxO)) (image_mono hOW)
  rw [liftPropOn_iff_repOn hW']
  rintro _ ⟨x, hx, rfl⟩
  have hgx : invFunOn f W (f x) = x := hinj.leftInvOn_invFunOn hx
  obtain ⟨O, hxO, hOW, hO⟩ := hrep x hx
  have hOimg := hO.isOpen_image
  obtain ⟨-, hs, hm, -, e, he, hme, heq⟩ := hO
  set c := chartAt Y x
  set c' := chartAt Y (f x)
  have hgz : ∀ z ∈ O, invFunOn f W (f z) = z := fun z hz => hinj.leftInvOn_invFunOn (hOW hz)
  refine ⟨f '' O, mem_image_of_mem f hxO, image_mono hOW, hOimg, ?_, ?_, ?_, e.symm, G.symm he,
    ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩; exact hm hz
  · rw [hgx]; rintro _ ⟨z, hz, rfl⟩; rw [hgz z hz]; exact hs hz
  · -- on `f '' O`, `invFunOn f W = c.symm ∘ e.symm ∘ c'`
    have hcont : ContinuousOn (c.symm ∘ e.symm ∘ c') (f '' O) := by
      refine c.continuousOn_symm.comp (e.continuousOn_symm.comp
        (c'.continuousOn.mono ?_) ?_) ?_
      · rintro _ ⟨z, hz, rfl⟩; exact hm hz
      · rintro _ ⟨z, hz, rfl⟩
        show c' (f z) ∈ e.target
        rw [heq z hz]; exact e.map_source (hme hz)
      · rintro _ ⟨z, hz, rfl⟩
        show e.symm (c' (f z)) ∈ c.target
        rw [heq z hz, e.left_inv (hme hz)]; exact c.map_source (hs hz)
    refine hcont.congr ?_
    rintro _ ⟨z, hz, rfl⟩
    simp only [comp_apply]
    rw [hgz z hz, heq z hz, e.left_inv (hme hz), c.left_inv (hs hz)]
  · rintro _ ⟨z, hz, rfl⟩
    show c' (f z) ∈ e.target
    rw [heq z hz]; exact e.map_source (hme hz)
  · rintro _ ⟨z, hz, rfl⟩
    rw [hgx, hgz z hz, heq z hz]
    exact (e.left_inv (hme hz)).symm

/-- **A1 from B1** (`prop:GX_liouville`, `these.tex:1476`): if elements of `G` agreeing on a
non-empty open subset of a preconnected open set agree on it, and `Y` is locally connected, two
morphisms into a Hausdorff space defined on a preconnected open `V` and agreeing on a non-empty
open `O ⊆ V` agree on `V`. The open–closed argument: the set where `f` and `g` agree near the
point is open; at a point of its closure in `V` they agree (continuity, `T2`), and in the charts
at that point they are two elements of `G` agreeing on a non-empty open subset of a connected
chart neighbourhood. -/
theorem eqOn_of_liftPropOn [ClosedUnderRestriction G] [LocallyConnectedSpace Y] [T2Space N]
    (hrig : ∀ e ∈ G, ∀ e' ∈ G, ∀ U : Set Y, IsOpen U → IsPreconnected U → U ⊆ e.source →
      U ⊆ e'.source → ∀ O ⊆ U, IsOpen O → O.Nonempty → EqOn e e' O → EqOn e e' U)
    {f g : M → N} {V O : Set M} (hV : IsOpen V) (hVc : IsPreconnected V)
    (hf : LiftPropOn G.IsLocalStructomorphWithinAt f V)
    (hg : LiftPropOn G.IsLocalStructomorphWithinAt g V) (hO : IsOpen O) (hOV : O ⊆ V)
    (hOne : O.Nonempty) (hfg : EqOn f g O) : EqOn f g V := by
  have hrf := (liftPropOn_iff_repOn hV).1 hf
  have hrg := (liftPropOn_iff_repOn hV).1 hg
  have hcf : ContinuousOn f V := fun y hy => (hf y hy).continuousWithinAt
  have hcg : ContinuousOn g V := fun y hy => (hg y hy).continuousWithinAt
  set A : Set M := {z | ∀ᶠ w in 𝓝 z, f w = g w}
  have hA : IsOpen A := isOpen_setOf_eventually_nhds
  have hAeq : ∀ z ∈ A, f z = g z := fun z hz => hz.self_of_nhds
  have hVA : (V ∩ A).Nonempty := by
    obtain ⟨z, hz⟩ := hOne
    exact ⟨z, hOV hz, mem_of_superset (hO.mem_nhds hz) hfg⟩
  have hsub : V ⊆ A := by
    refine hVc.subset_of_closure_inter_subset hA hVA ?_
    rintro x ⟨hxA, hxV⟩
    -- `f x = g x`
    have hne : (𝓝[A] x).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hxA
    have hfx : f x = g x := by
      have h1 : Tendsto f (𝓝[A] x) (𝓝 (f x)) :=
        ((hcf.continuousAt (hV.mem_nhds hxV)).tendsto).mono_left nhdsWithin_le_nhds
      have h2 : Tendsto f (𝓝[A] x) (𝓝 (g x)) := by
        refine (((hcg.continuousAt (hV.mem_nhds hxV)).tendsto).mono_left
          nhdsWithin_le_nhds).congr' ?_
        exact eventually_nhdsWithin_of_forall fun z hz => (hAeq z hz).symm
      exact tendsto_nhds_unique h1 h2
    obtain ⟨Of, hxOf, -, hOf, hsf, hmf, -, ef, hef, hmef, heqf⟩ := hrf x hxV
    obtain ⟨Og, hxOg, -, hOg, hsg, hmg, -, eg, heg, hmeg, heqg⟩ := hrg x hxV
    rw [← hfx] at hmg heqg
    set c := chartAt Y x
    set c' := chartAt Y (f x)
    have hPo : IsOpen (c '' (Of ∩ Og)) :=
      c.isOpen_image_of_subset_source (hOf.inter hOg) fun z hz => hsf hz.1
    set Q := connectedComponentIn (c '' (Of ∩ Og)) (c x)
    have hQo : IsOpen Q := hPo.connectedComponentIn
    have hQP : Q ⊆ c '' (Of ∩ Og) := connectedComponentIn_subset _ _
    have hxQ : c x ∈ Q := mem_connectedComponentIn ⟨x, ⟨hxOf, hxOg⟩, rfl⟩
    have hQf : Q ⊆ ef.source := fun y hy => by
      obtain ⟨z, hz, rfl⟩ := hQP hy; exact hmef hz.1
    have hQg : Q ⊆ eg.source := fun y hy => by
      obtain ⟨z, hz, rfl⟩ := hQP hy; exact hmeg hz.2
    set T : Set M := A ∩ (Of ∩ Og) ∩ (c.source ∩ c ⁻¹' Q)
    have hTo : IsOpen T := (hA.inter (hOf.inter hOg)).inter (c.isOpen_inter_preimage hQo)
    have hTne : T.Nonempty := by
      have hN : IsOpen ((Of ∩ Og) ∩ (c.source ∩ c ⁻¹' Q)) :=
        (hOf.inter hOg).inter (c.isOpen_inter_preimage hQo)
      obtain ⟨z, hz, hzA⟩ := mem_closure_iff.1 hxA _ hN
        ⟨⟨hxOf, hxOg⟩, mem_chart_source Y x, hxQ⟩
      exact ⟨z, ⟨hzA, hz.1⟩, hz.2⟩
    have hTs : T ⊆ c.source := fun z hz => hz.2.1
    have hEq : EqOn ef eg Q := by
      refine hrig ef hef eg heg Q hQo isPreconnected_connectedComponentIn hQf hQg (c '' T)
        (fun y hy => by obtain ⟨z, hz, rfl⟩ := hy; exact hz.2.2)
        (c.isOpen_image_of_subset_source hTo hTs) (hTne.image _) ?_
      rintro _ ⟨z, hz, rfl⟩
      rw [← heqf z hz.1.2.1, ← heqg z hz.1.2.2, hAeq z hz.1.1]
    refine mem_of_superset (((hOf.inter hOg).inter (c.isOpen_inter_preimage hQo)).mem_nhds
      ⟨⟨hxOf, hxOg⟩, mem_chart_source Y x, hxQ⟩) ?_
    rintro w ⟨⟨hwf, hwg⟩, -, hwQ⟩
    refine c'.injOn (hmf hwf) (hmg hwg) ?_
    rw [heqf w hwf, heqg w hwg]
    exact hEq hwQ
  exact fun z hz => hAeq z (hsub hz)

end Calculus

/-! ### The generated causality of an atlas with transitions in `G` -/

section ChartedCausality

variable {Y : Type u} [TopologicalSpace Y] {G : StructureGroupoid Y} {D : Causality Y}
  {M : Type u} [TopologicalSpace M] [ChartedSpace Y M] [HasGroupoid M G]

/-- The transports of `D` along the preferred charts agree on the overlaps, when every element of
`G` is an isomorphism of `D` (B3 `chartIso_mem`) and `D` is absolutely minimal on every open set
(B3 `absolutelyMinimalOn_Y`): (B) of `theo:causalite_engendre` (kb/0018). -/
theorem chartTransport_compatible (hGD : ∀ e ∈ G, ChartIso D D e)
    (hA : ∀ W : Opens Y, D.AbsolutelyMinimalOn W) :
    Precausality.Compatible (fun x : M => chartSource (chartAt Y x))
      (fun x => (D.chartTransport (chartAt Y x)).toPrecausality) := by
  refine compatible_of_agree_locally (fun x W hW =>
    (D.chartTransport_chartIso _).absolutelyMinimalOn hW (hA _)) ?_
  intro x x' z hz
  refine ⟨chartSource (chartAt Y x) ⊓ chartSource (chartAt Y x'), hz, ?_⟩
  refine ChartIso.agreeOn_of_localIso (D.chartTransport_chartIso _) (D.chartTransport_chartIso _)
    (ψ := (chartAt Y x).symm.trans (chartAt Y x'))
    (hGD _ (G.compatible (chart_mem_atlas Y x) (chart_mem_atlas Y x'))) le_rfl ?_
  intro w hw
  refine ⟨⟨(chartAt Y x).map_source hw.1, ?_⟩, ?_⟩
  · show (chartAt Y x).symm ((chartAt Y x) w) ∈ (chartAt Y x').source
    rw [(chartAt Y x).left_inv hw.1]; exact hw.2
  · show (chartAt Y x') ((chartAt Y x).symm ((chartAt Y x) w)) = (chartAt Y x') w
    rw [(chartAt Y x).left_inv hw.1]

/-- **Every preferred chart is an isomorphism** of the generated causality onto the model. -/
theorem chartedCausality_chartIso (hGD : ∀ e ∈ G, ChartIso D D e)
    (hA : ∀ W : Opens Y, D.AbsolutelyMinimalOn W) (x : M) :
    ChartIso (chartedCausality D M) D (chartAt Y x) := by
  have hB := chartTransport_compatible (M := M) hGD hA
  refine (D.chartTransport_chartIso (chartAt Y x)).congr fun V hV a b => ?_
  exact ⟨Precausality.generated_le_iff (hU := fun x : M => ⟨x, mem_chart_source Y x⟩) hB hV,
    Precausality.generated_lt_iff (hU := fun x : M => ⟨x, mem_chart_source Y x⟩) hB hV⟩

/-- **A chronological diamond read in the preferred chart** is the chronological diamond of the
model, in the chart image of the open set: `κ '' (I⁺_W(p) ∩ I⁻_W(r)) = I⁺_{κ W}(κ p) ∩ I⁻_{κ W}(κ r)`
for `W` in the source of `κ = chartAt Y x`. This is how the past-side piece of A3 at a boundary
point `p` (`Causality.CausallyConvexIn.Iplus_inter_Iminus_subset`) is read in `Y`, where the
largeness clause of `LocalModel.localUnique_sing_adherent` is stated. -/
theorem chartedCausality_image_Iplus_inter_Iminus (hGD : ∀ e ∈ G, ChartIso D D e)
    (hA : ∀ W : Opens Y, D.AbsolutelyMinimalOn W) (x : M) {W : Opens M}
    (hW : W ≤ chartSource (chartAt Y x)) {p r : M} (hp : p ∈ W) (hr : r ∈ W) :
    chartAt Y x '' ((chartedCausality D M).Iplus W {p} ∩ (chartedCausality D M).Iminus W {r}) =
      D.Iplus (chartImage (chartAt Y x) W) {chartAt Y x p} ∩
        D.Iminus (chartImage (chartAt Y x) W) {chartAt Y x r} := by
  have hc := chartedCausality_chartIso (M := M) hGD hA x
  ext y
  simp only [mem_image, mem_inter_iff, Precausality.mem_Iplus_singleton,
    Precausality.mem_Iminus_singleton]
  constructor
  · rintro ⟨z, ⟨hpz, hzr⟩, rfl⟩
    have hz : z ∈ W := (chartedCausality D M).lt_mem_right hpz
    exact ⟨((hc W hW p hp z hz).2).1 hpz, ((hc W hW z hz r hr).2).1 hzr⟩
  · rintro ⟨hpy, hyr⟩
    obtain ⟨z, -, hz, rfl, -⟩ := exists_of_mem_chartImage (D.lt_mem_right hpy)
    exact ⟨z, ⟨((hc W hW p hp z hz).2).2 hpy, ((hc W hW z hz r hr).2).2 hyr⟩, rfl⟩

/-- The generated causality is absolutely minimal. -/
theorem chartedCausality_absolutelyMinimal (hA : ∀ W : Opens Y, D.AbsolutelyMinimalOn W) :
    (chartedCausality D M).AbsolutelyMinimal :=
  Causality.generated_absolutelyMinimal _ fun x =>
    (D.chartTransport_chartIso (chartAt Y x)).absolutelyMinimalOn le_rfl (hA _)

/-- **The generated causality is absolutely minimal on every open set** (Level A
`absolutelyMinimalOn`, kb/0014). -/
theorem chartedCausality_absolutelyMinimalOn (hGD : ∀ e ∈ G, ChartIso D D e)
    (hA : ∀ W : Opens Y, D.AbsolutelyMinimalOn W) (W : Opens M) :
    (chartedCausality D M).AbsolutelyMinimalOn W :=
  absolutelyMinimalOn_of_locally (chartedCausality_absolutelyMinimal hA)
    (fun x => ⟨chartSource (chartAt Y x), mem_chart_source Y x, fun _ hW =>
      (chartedCausality_chartIso hGD hA x).absolutelyMinimalOn hW (hA _)⟩) W

end ChartedCausality

section EMorphism

variable {Y : Type u} [TopologicalSpace Y] {G : StructureGroupoid Y} {D : Causality Y}
  {M N : Type u} [TopologicalSpace M] [TopologicalSpace N] [ChartedSpace Y M] [ChartedSpace Y N]
  [HasGroupoid M G] [HasGroupoid N G]

/-- On a forward-local-form set, `f` is an isomorphism of the generated causalities onto its
image: the composite of the chart at `x`, an element of `G` and the inverse chart at `f x`, three
`ChartIso`s. -/
theorem RepOn.rel_iff (hGD : ∀ e ∈ G, ChartIso D D e)
    (hA : ∀ W : Opens Y, D.AbsolutelyMinimalOn W) {f : M → N} {O : Set M} {x : M}
    (h : RepOn G f O x) (V : Opens M) (hVO : (V : Set M) ⊆ O) (U : Opens N)
    (hU : (U : Set N) = f '' V) {a b : M} (ha : a ∈ V) (hb : b ∈ V) :
    ((chartedCausality D M).le V a b ↔ (chartedCausality D N).le U (f a) (f b)) ∧
      ((chartedCausality D M).lt V a b ↔ (chartedCausality D N).lt U (f a) (f b)) := by
  obtain ⟨-, hs, hm, -, e, he, hme, heq⟩ := h
  set c := chartAt Y x
  set c' := chartAt Y (f x)
  have hc := chartedCausality_chartIso (M := M) hGD hA x
  have hc' := chartedCausality_chartIso (M := N) hGD hA (f x)
  have hVc : V ≤ chartSource c := fun z hz => hs (hVO hz)
  have hUc : U ≤ chartSource c' := by
    intro w hw
    have hw' : w ∈ (U : Set N) := hw
    rw [hU] at hw'
    obtain ⟨z, hz, rfl⟩ := hw'; exact hm (hVO hz)
  have hVe : chartImage c V ≤ chartSource e := by
    intro y hy
    obtain ⟨z, -, hzV, rfl, -⟩ := exists_of_mem_chartImage hy
    exact hme (hVO hzV)
  have himg : chartImage e (chartImage c V) = chartImage c' U := by
    apply SetLike.coe_injective
    rw [coe_chartImage_of_le hVe, coe_chartImage_of_le hVc, coe_chartImage_of_le hUc, hU,
      image_image, image_image]
    exact image_congr fun z hz => (heq z (hVO hz)).symm
  have h1 := hc V hVc a ha b hb
  have h2 := hGD e he (chartImage c V) hVe _ (mem_chartImage_of_mem (hVc ha) ha) _
    (mem_chartImage_of_mem (hVc hb) hb)
  have hfa : f a ∈ U := by rw [← SetLike.mem_coe, hU]; exact mem_image_of_mem f ha
  have hfb : f b ∈ U := by rw [← SetLike.mem_coe, hU]; exact mem_image_of_mem f hb
  have h3 := hc' U hUc _ hfa _ hfb
  rw [himg, ← heq a (hVO ha), ← heq b (hVO hb)] at h2
  exact ⟨h1.1.trans (h2.1.trans h3.1.symm), h1.2.trans (h2.2.trans h3.2.symm)⟩

/-- **A structure morphism is an abstract `𝕄≥0`-morphism** (Level A `isEMorphismOn_of_isMor`;
`ETT.tex:1852–1854`): continuity and openness from the forward local form, the local isomorphism
from `RepOn.rel_iff`, and the strong-morphism half by absolute minimality (every relation of an
open `V ⊆ W` is a chain of relations in forward-local-form sets). -/
theorem isEMorphismOn_of_liftPropOn [ClosedUnderRestriction G] (hGD : ∀ e ∈ G, ChartIso D D e)
    (hA : ∀ W : Opens Y, D.AbsolutelyMinimalOn W) {f : M → N} {W : Opens M}
    (hf : LiftPropOn G.IsLocalStructomorphWithinAt f W) :
    IsEMorphismOn (chartedCausality D M) (chartedCausality D N) W f := by
  have hrep := (liftPropOn_iff_repOn W.isOpen).1 hf
  set CM := chartedCausality D M
  set CN := chartedCausality D N
  have hcont : ContinuousOn f W := fun y hy => (hf y hy).continuousWithinAt
  have himgOpen : ∀ V : Opens M, V ≤ W → IsOpen (f '' V) := by
    intro V hV
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨O, hxO, -, hO⟩ := hrep x (hV hx)
    have hO' := hO.mono (hO.1.inter V.isOpen) inter_subset_left
    exact mem_of_superset (hO'.isOpen_image.mem_nhds (mem_image_of_mem f ⟨hxO, hx⟩))
      (image_mono inter_subset_right)
  -- the cover by forward-local-form sets
  set S : Set (Opens M) := {O | ∃ x, RepOn G f O x}
  have hS : ∀ V : Opens M, V ≤ W → ∀ x ∈ V, ∃ O ∈ S, x ∈ O := by
    intro V hV x hx
    obtain ⟨O, hxO, -, hO⟩ := hrep x (hV hx)
    exact ⟨⟨O, hO.1⟩, ⟨x, hO⟩, hxO⟩
  have step : ∀ (V : Opens M) (U : Opens N), V ≤ W → MapsTo f V U → ∀ O ∈ S, ∀ a b : M,
      (CM.le (V ⊓ O) a b → CN.le U (f a) (f b)) ∧ (CM.lt (V ⊓ O) a b → CN.lt U (f a) (f b)) := by
    rintro V U - hmaps O ⟨x₀, hO⟩ a b
    have hO' : RepOn G f (V ⊓ O : Opens M) x₀ := hO.mono (V ⊓ O).isOpen inter_subset_right
    set U' : Opens N := ⟨f '' (V ⊓ O : Opens M), hO'.isOpen_image⟩
    have hU'U : U' ≤ U := by
      rintro _ ⟨z, hz, rfl⟩; exact hmaps hz.1
    refine ⟨fun hab => ?_, fun hab => ?_⟩
    · have := ((hO.rel_iff hGD hA (V ⊓ O) inter_subset_right U' rfl (CM.le_mem_left hab)
        (CM.le_mem_right hab)).1).1 hab
      exact CN.le_mono hU'U this
    · have := ((hO.rel_iff hGD hA (V ⊓ O) inter_subset_right U' rfl (CM.lt_mem_left hab)
        (CM.lt_mem_right hab)).2).1 hab
      exact CN.lt_mono hU'U this
  have hmin := chartedCausality_absolutelyMinimalOn (M := M) hGD hA
  refine ⟨hcont, himgOpen, ?_, ?_, ?_⟩
  · intro V U hV hmaps x y hxy
    have hc := ((hmin V S (hS V hV) V le_rfl x y).1 hxy)
    clear hxy
    induction hc with
    | single hl =>
      obtain ⟨O, hO, h⟩ := hl
      exact (step V U hV hmaps O hO _ _).1 h
    | tail _ hl ih =>
      obtain ⟨O, hO, h⟩ := hl
      exact CN.le_trans ih ((step V U hV hmaps O hO _ _).1 h)
  · intro V U hV hmaps x y hxy
    have hc := ((hmin V S (hS V hV) V le_rfl x y).2 hxy)
    clear hxy
    induction hc with
    | single hl =>
      obtain ⟨O, hO, h⟩ := hl
      exact (step V U hV hmaps O hO _ _).2 h
    | tail _ hl ih =>
      obtain ⟨O, hO, h⟩ := hl
      exact CN.lt_trans ih ((step V U hV hmaps O hO _ _).2 h)
  · intro x hx
    obtain ⟨O, hxO, hOW, hO⟩ := hrep x hx
    refine ⟨⟨O, hO.1⟩, hOW, hxO, hO.injOn, fun V' hV' U hU y hy z hz => ?_⟩
    exact hO.rel_iff hGD hA V' hV' U hU hy hz

end EMorphism

/-! ### Singular loci, transport along a homeomorphism -/

section SingTransport

variable {Y : Type u} [TopologicalSpace Y] {G : StructureGroupoid Y}
  {M N : Type u} [TopologicalSpace M] [TopologicalSpace N] [ChartedSpace Y M] [ChartedSpace Y N]

/-- **Morphisms preserve the type of a point** (`cor:model_corresponding`), from B3 `sing_mem`. -/
theorem mem_chartedSing_iff_of_liftPropOn [ClosedUnderRestriction G] {singY : ℝ → Set Y}
    (hsing : ∀ e ∈ G, ∀ y ∈ e.source, ∀ α : ℝ, 0 ≤ α → (y ∈ singY α ↔ e y ∈ singY α))
    {f : M → N} {W : Set M} (hW : IsOpen W) (hf : LiftPropOn G.IsLocalStructomorphWithinAt f W)
    {x : M} (hx : x ∈ W) {α : ℝ} (hα : 0 ≤ α) :
    x ∈ chartedSing singY M α ↔ f x ∈ chartedSing singY N α := by
  obtain ⟨O, hxO, -, -, -, -, -, e, he, hme, heq⟩ := (liftPropOn_iff_repOn hW).1 hf x hx
  show chartAt Y x x ∈ singY α ↔ chartAt Y (f x) (f x) ∈ singY α
  rw [heq x hxO]
  exact hsing e he _ (hme hxO) α hα

variable (Y) in
/-- **Transport of an atlas along a homeomorphism** (Level A `transport`): the charts of `M'` are
`e.symm` followed by the charts of `M`. -/
@[reducible] noncomputable def transportChartedSpace {M' : Type*} [TopologicalSpace M']
    (e : M ≃ₜ M') : ChartedSpace Y M' where
  atlas := {c' | ∃ c ∈ atlas Y M, c' = e.symm.toOpenPartialHomeomorph.trans c}
  chartAt x' := e.symm.toOpenPartialHomeomorph.trans (chartAt Y (e.symm x'))
  mem_chart_source x' := by
    simp only [OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
      univ_inter, mem_preimage, Homeomorph.toOpenPartialHomeomorph_apply]
    exact mem_chart_source Y _
  chart_mem_atlas x' := ⟨_, chart_mem_atlas Y _, rfl⟩

theorem transport_hasGroupoid [HasGroupoid M G] {M' : Type*} [TopologicalSpace M']
    (e : M ≃ₜ M') : @HasGroupoid Y _ M' _ (transportChartedSpace Y e) G := by
  letI := transportChartedSpace Y e
  refine ⟨?_⟩
  rintro _ _ ⟨c₁, hc₁, rfl⟩ ⟨c₂, hc₂, rfl⟩
  have h : (e.symm.toOpenPartialHomeomorph.trans c₁).symm.trans
      (e.symm.toOpenPartialHomeomorph.trans c₂) = c₁.symm.trans c₂ := by
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc,
      ← OpenPartialHomeomorph.trans_assoc e.symm.toOpenPartialHomeomorph.symm,
      ← Homeomorph.symm_toOpenPartialHomeomorph, Homeomorph.symm_symm,
      ← Homeomorph.trans_toOpenPartialHomeomorph, Homeomorph.self_trans_symm,
      Homeomorph.refl_toOpenPartialHomeomorph, OpenPartialHomeomorph.refl_trans]
  rw [h]
  exact G.compatible hc₁ hc₂

/-- The homeomorphism is a morphism into the transported atlas (Level A `isMor_transport`). -/
theorem liftPropOn_transport [ClosedUnderRestriction G] [HasGroupoid M G] {M' : Type u}
    [TopologicalSpace M'] (e : M ≃ₜ M') :
    @LiftPropOn Y M Y M' _ _ _ _ _ (transportChartedSpace Y e) G.IsLocalStructomorphWithinAt e
      univ := by
  letI := transportChartedSpace Y e
  rw [liftPropOn_iff_repOn isOpen_univ]
  intro x _
  refine ⟨(chartAt Y x).source, mem_chart_source Y x, subset_univ _,
    (chartAt Y x).open_source, subset_rfl, ?_, e.continuous.continuousOn,
    OpenPartialHomeomorph.refl Y, G.id_mem, fun _ _ => trivial, ?_⟩
  · intro z hz
    show e z ∈ univ ∩ e.symm.toOpenPartialHomeomorph ⁻¹' (chartAt Y (e.symm (e x))).source
    simp only [Homeomorph.toOpenPartialHomeomorph_apply, e.symm_apply_apply]
    exact ⟨trivial, by simpa only [mem_preimage, e.symm_apply_apply] using hz⟩
  · intro z _
    show chartAt Y (e.symm (e x)) (e.symm (e z)) = chartAt Y x z
    simp only [e.symm_apply_apply]

end SingTransport

/-! ### Gluing atlases along open embeddings (Level A `glue`; gx review C5) -/

section Glue

variable {Y : Type*} [TopologicalSpace Y] {G : StructureGroupoid Y}
  {Z : Type*} [TopologicalSpace Z] {ι : Type*} {M : ι → Type*} [∀ i, TopologicalSpace (M i)]
  [∀ i, Nonempty (M i)] [∀ i, ChartedSpace Y (M i)] {e : ∀ i, M i → Z}

/-- The open embedding `e i`, as an open partial homeomorphism (source `M i`, target its range). -/
noncomputable def glueEmb (he : ∀ i, IsOpenEmbedding (e i)) (i : ι) :
    OpenPartialHomeomorph (M i) Z :=
  (he i).toOpenPartialHomeomorph (e i)

@[simp] theorem glueEmb_apply (he : ∀ i, IsOpenEmbedding (e i)) (i : ι) (x : M i) :
    glueEmb he i x = e i x := by
  simp [glueEmb]

theorem glueEmb_symm_apply (he : ∀ i, IsOpenEmbedding (e i)) (i : ι) (x : M i) :
    (glueEmb he i).symm (e i x) = x :=
  (he i).toOpenPartialHomeomorph_left_inv (e i)

/-- The piece chosen at a point of `Z`. -/
noncomputable def glueIndex (hcov : ∀ z, ∃ i, z ∈ range (e i)) (z : Z) : ι := (hcov z).choose

/-- The point of the chosen piece over `z`. -/
noncomputable def gluePoint (hcov : ∀ z, ∃ i, z ∈ range (e i)) (z : Z) :
    M (glueIndex hcov z) :=
  (hcov z).choose_spec.choose

omit [TopologicalSpace Z] [∀ i, TopologicalSpace (M i)] [∀ i, Nonempty (M i)] in
theorem apply_gluePoint (hcov : ∀ z, ∃ i, z ∈ range (e i)) (z : Z) :
    e (glueIndex hcov z) (gluePoint hcov z) = z :=
  (hcov z).choose_spec.choose_spec

theorem glueEmb_symm_gluePoint (he : ∀ i, IsOpenEmbedding (e i))
    (hcov : ∀ z, ∃ i, z ∈ range (e i)) (z : Z) :
    (glueEmb he (glueIndex hcov z)).symm z = gluePoint hcov z := by
  have h := glueEmb_symm_apply he (glueIndex hcov z) (gluePoint hcov z)
  rwa [apply_gluePoint (e := e) hcov z] at h

/-- The chart of the glued atlas at `z`: the inverse of the chosen embedding, then the preferred
chart of the piece. -/
noncomputable def glueChart (he : ∀ i, IsOpenEmbedding (e i))
    (hcov : ∀ z, ∃ i, z ∈ range (e i)) (z : Z) : OpenPartialHomeomorph Z Y :=
  (glueEmb he (glueIndex hcov z)).symm.trans (chartAt Y (gluePoint hcov z))

variable (Y) in
/-- **The glued charted space** (gx review C5: the charted-space structure on a gluing of charted
spaces along open embeddings covering `Z`; exported for gx's B21 Lemma 2.3). -/
@[reducible] noncomputable def gluedChartedSpace (he : ∀ i, IsOpenEmbedding (e i))
    (hcov : ∀ z, ∃ i, z ∈ range (e i)) : ChartedSpace Y Z where
  atlas := range (glueChart he hcov)
  chartAt := glueChart he hcov
  mem_chart_source z := by
    refine ⟨?_, ?_⟩
    · show z ∈ (glueEmb he (glueIndex hcov z)).target
      rw [glueEmb, IsOpenEmbedding.toOpenPartialHomeomorph_target]
      exact ⟨_, apply_gluePoint hcov z⟩
    · show (glueEmb he (glueIndex hcov z)).symm z ∈ (chartAt Y (gluePoint hcov z)).source
      rw [glueEmb_symm_gluePoint]
      exact mem_chart_source Y _
  chart_mem_atlas z := mem_range_self z

/-- The canonical transition `M i → M j`, defined on `e i ⁻¹' range (e j)`. -/
noncomputable def glueTransition (he : ∀ i, IsOpenEmbedding (e i)) (i j : ι) : M i → M j :=
  (glueEmb he j).symm ∘ e i

/-- **The glued atlas has transitions in `G`** when every canonical transition is a morphism. -/
theorem gluedChartedSpace_hasGroupoid [ClosedUnderRestriction G] [∀ i, HasGroupoid (M i) G]
    (he : ∀ i, IsOpenEmbedding (e i)) (hcov : ∀ z, ∃ i, z ∈ range (e i))
    (htrans : ∀ i j, LiftPropOn G.IsLocalStructomorphWithinAt (glueTransition he i j)
      (e i ⁻¹' range (e j))) :
    @HasGroupoid Y _ Z _ (gluedChartedSpace Y he hcov) G := by
  letI := gluedChartedSpace Y he hcov
  refine ⟨?_⟩
  rintro _ _ ⟨z, rfl⟩ ⟨z', rfl⟩
  set i := glueIndex hcov z
  set j := glueIndex hcov z'
  set p := gluePoint hcov z
  set q := gluePoint hcov z'
  set cp := chartAt Y p
  set cq := chartAt Y q
  set big := ((glueEmb he i).symm.trans cp).symm.trans ((glueEmb he j).symm.trans cq)
  have hbig : ∀ y, big y = (cq ∘ glueTransition he i j ∘ cp.symm) y := fun y => by
    simp [big, glueTransition, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
  have hsrc : ∀ y ∈ big.source, y ∈ cp.target ∧ e i (cp.symm y) ∈ range (e j) ∧
      glueTransition he i j (cp.symm y) ∈ cq.source := by
    intro y hy
    simp only [big, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      OpenPartialHomeomorph.symm_symm, mem_inter_iff,
      mem_preimage, OpenPartialHomeomorph.coe_trans, comp_apply, glueEmb_apply] at hy
    refine ⟨hy.1.1, ?_, ?_⟩
    · have := hy.2.1
      rwa [glueEmb, IsOpenEmbedding.toOpenPartialHomeomorph_target] at this
    · exact hy.2.2
  have hG := isLocalStructomorphWithinAt_localInvariantProp G
  apply G.locality
  intro y hy
  obtain ⟨hyt, hyr, hyq⟩ := hsrc y hy
  obtain ⟨φ, hφ, hEq, hyφ⟩ := hG.liftPropOn_indep_chart
    (G.subset_maximalAtlas (chart_mem_atlas Y p)) (G.subset_maximalAtlas (chart_mem_atlas Y q))
    (htrans i j) ⟨hyt, hyr, hyq⟩ hyr
  refine ⟨φ.source, φ.open_source, hyφ, ?_⟩
  refine G.mem_of_eqOnSource (closedUnderRestriction' hφ big.open_source)
    (OpenPartialHomeomorph.Set.EqOn.restr_eqOn_source fun t ht => ?_)
  exact (hbig t).trans (hEq ⟨(hsrc t ht.1).2.1, ht.2⟩)

/-- **Every embedding is a morphism into the glued atlas.** -/
theorem liftPropOn_glue [ClosedUnderRestriction G] [∀ i, HasGroupoid (M i) G]
    (he : ∀ i, IsOpenEmbedding (e i)) (hcov : ∀ z, ∃ i, z ∈ range (e i))
    (htrans : ∀ i j, LiftPropOn G.IsLocalStructomorphWithinAt (glueTransition he i j)
      (e i ⁻¹' range (e j))) (i : ι) :
    @LiftPropOn Y (M i) Y Z _ _ _ _ _ (gluedChartedSpace Y he hcov)
      G.IsLocalStructomorphWithinAt (e i) univ := by
  letI := gluedChartedSpace Y he hcov
  have hG := isLocalStructomorphWithinAt_localInvariantProp G
  intro w _
  refine ⟨(he i).continuous.continuousWithinAt, ?_⟩
  set k := glueIndex hcov (e i w)
  set p := gluePoint hcov (e i w)
  have hl : (chartAt Y w).symm (chartAt Y w w) = w := (chartAt Y w).left_inv (mem_chart_source Y w)
  have hfun : chartAt Y (e i w) ∘ e i ∘ (chartAt Y w).symm =
      chartAt Y p ∘ glueTransition he i k ∘ (chartAt Y w).symm := by
    funext y
    simp [glueTransition, p, k]
    rfl
  have htp : glueTransition he i k w = p := by
    show (glueEmb he k).symm (e i w) = p
    exact glueEmb_symm_gluePoint he hcov (e i w)
  have hs : IsOpen (e i ⁻¹' range (e k)) := (he k).isOpen_range.preimage (he i).continuous
  have hws : w ∈ e i ⁻¹' range (e k) := ⟨p, apply_gluePoint hcov (e i w)⟩
  have hP := hG.liftPropOn_indep_chart (G.subset_maximalAtlas (chart_mem_atlas Y w))
    (G.subset_maximalAtlas (chart_mem_atlas Y p)) (htrans i k)
    (y := chartAt Y w w) ⟨(chartAt Y w).map_source (mem_chart_source Y w), by
      show (chartAt Y w).symm (chartAt Y w w) ∈ e i ⁻¹' range (e k) ∧
        glueTransition he i k ((chartAt Y w).symm (chartAt Y w w)) ∈ (chartAt Y p).source
      rw [hl, htp]
      exact ⟨hws, mem_chart_source Y p⟩⟩
  rw [hfun, preimage_univ]
  have hu : (chartAt Y w).symm ⁻¹' (e i ⁻¹' range (e k)) ∈ 𝓝[univ] (chartAt Y w w) := by
    rw [nhdsWithin_univ]
    refine ((chartAt Y w).continuousAt_symm
      ((chartAt Y w).map_source (mem_chart_source Y w))).preimage_mem_nhds ?_
    rw [hl]
    exact hs.mem_nhds hws
  rw [hG.is_local_nhds hu, univ_inter]
  exact hP

/-! #### The charted space of a `FamilyGlueData` gluing (gx review C5) -/

namespace FamilyGlueData

variable {Y : Type*} [TopologicalSpace Y] {G : StructureGroupoid Y} {I : Type*}
  {M : I → Type*} [∀ i, TopologicalSpace (M i)] (D : FamilyGlueData I M)

theorem exists_mem_range_ι (z : D.Glued) : ∃ i, z ∈ range (D.ι i) := by
  obtain ⟨i, x, hx⟩ := D.exists_ι z
  exact ⟨i, x, hx⟩

/-- The part of `M i` glued to `M j` is the preimage of the range of `ι j`. -/
theorem preimage_ι_range_ι (i j : I) : D.ι i ⁻¹' range (D.ι j) = D.U i j := by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨h, -⟩ := D.ι_eq_ι_iff.1 hy.symm
    exact h
  · intro h
    exact ⟨D.φ i j ⟨x, h⟩, D.ι_φ i j ⟨x, h⟩⟩

variable [∀ i, Nonempty (M i)] [∀ i, ChartedSpace Y (M i)]

variable (Y) in
/-- **The charted-space structure on the gluing `D.Glued`** of charted spaces (gx review C5,
exported for gx's B21 Lemma 2.3): the atlas `glueChart` of `Causal.CBG.gluedChartedSpace` along
the open embeddings `D.ι i`. -/
@[reducible] noncomputable def chartedSpace : ChartedSpace Y D.Glued :=
  Causal.CBG.gluedChartedSpace Y D.isOpenEmbedding_ι D.exists_mem_range_ι

/-- The canonical transition of the gluing is the transition `φ i j` of the data. -/
theorem glueTransition_eq (i j : I) (x : D.U i j) :
    glueTransition D.isOpenEmbedding_ι i j x = D.φ i j x := by
  show (glueEmb D.isOpenEmbedding_ι j).symm (D.ι i x) = D.φ i j x
  rw [← D.ι_φ i j x]
  exact glueEmb_symm_apply _ j _

/-- **The glued atlas has transitions in `G`** when every `φ i j`, extended canonically, is a
morphism on `U i j`. -/
theorem hasGroupoid_chartedSpace [ClosedUnderRestriction G] [∀ i, HasGroupoid (M i) G]
    (htrans : ∀ i j, LiftPropOn G.IsLocalStructomorphWithinAt
      (glueTransition D.isOpenEmbedding_ι i j) (D.U i j)) :
    @HasGroupoid Y _ D.Glued _ (D.chartedSpace Y) G :=
  gluedChartedSpace_hasGroupoid D.isOpenEmbedding_ι D.exists_mem_range_ι fun i j => by
    rw [D.preimage_ι_range_ι i j]; exact htrans i j

/-- **Every `ι i` is a morphism into the glued atlas.** -/
theorem liftPropOn_ι [ClosedUnderRestriction G] [∀ i, HasGroupoid (M i) G]
    (htrans : ∀ i j, LiftPropOn G.IsLocalStructomorphWithinAt
      (glueTransition D.isOpenEmbedding_ι i j) (D.U i j)) (i : I) :
    @LiftPropOn Y (M i) Y D.Glued _ _ _ _ _ (D.chartedSpace Y)
      G.IsLocalStructomorphWithinAt (D.ι i) univ :=
  liftPropOn_glue D.isOpenEmbedding_ι D.exists_mem_range_ι (fun i j => by
    rw [D.preimage_ι_range_ι i j]; exact htrans i j) i

/-- **Bridge from the data's own transitions**: if a morphism `φ'` on `U i j` agrees with `φ i j`
there, the canonical extension `glueTransition` is a morphism on `U i j` (as Level A's `glue`
field does, via `liftPropOn_congr_of_eqOn`). -/
theorem liftPropOn_glueTransition_of_eqOn [ClosedUnderRestriction G] {i j : I}
    {φ' : M i → M j} (hφ' : LiftPropOn G.IsLocalStructomorphWithinAt φ' (D.U i j))
    (hφe : ∀ x : D.U i j, φ' x = D.φ i j x) :
    LiftPropOn G.IsLocalStructomorphWithinAt (glueTransition D.isOpenEmbedding_ι i j)
      (D.U i j) :=
  liftPropOn_congr_of_eqOn (D.U i j).isOpen hφ' fun x hx => by
    rw [hφe ⟨x, hx⟩]
    exact (D.glueTransition_eq i j ⟨x, hx⟩).symm

/-- `hasGroupoid_chartedSpace` with each transition given by any morphism agreeing with `φ i j`
on `U i j`. -/
theorem hasGroupoid_chartedSpace_of_eqOn [ClosedUnderRestriction G] [∀ i, HasGroupoid (M i) G]
    (φ' : ∀ i j, M i → M j)
    (hφ' : ∀ i j, LiftPropOn G.IsLocalStructomorphWithinAt (φ' i j) (D.U i j))
    (hφe : ∀ i j (x : D.U i j), φ' i j x = D.φ i j x) :
    @HasGroupoid Y _ D.Glued _ (D.chartedSpace Y) G :=
  D.hasGroupoid_chartedSpace fun i j => D.liftPropOn_glueTransition_of_eqOn (hφ' i j) (hφe i j)

/-- `liftPropOn_ι` with each transition given by any morphism agreeing with `φ i j` on
`U i j`. -/
theorem liftPropOn_ι_of_eqOn [ClosedUnderRestriction G] [∀ i, HasGroupoid (M i) G]
    (φ' : ∀ i j, M i → M j)
    (hφ' : ∀ i j, LiftPropOn G.IsLocalStructomorphWithinAt (φ' i j) (D.U i j))
    (hφe : ∀ i j (x : D.U i j), φ' i j x = D.φ i j x) (i : I) :
    @LiftPropOn Y (M i) Y D.Glued _ _ _ _ _ (D.chartedSpace Y)
      G.IsLocalStructomorphWithinAt (D.ι i) univ :=
  D.liftPropOn_ι (fun i j => D.liftPropOn_glueTransition_of_eqOn (hφ' i j) (hφe i j)) i

end FamilyGlueData

end Glue

/-! ### `Geometry.ofLocalModel` -/

namespace LocalModel

variable (𝔐 : LocalModel.{u})

/-- The structure induced on an open subset (mathlib's `Opens` charted space; `HasGroupoid` by
`ClosedUnderRestriction`). -/
noncomputable def restrictStr {M : Type u} [TopologicalSpace M] (s : 𝔐.Str M) (W : Opens M) :
    𝔐.Str W :=
  letI := s.1; haveI := s.2; ⟨inferInstance, inferInstance⟩

/-- The structure transported along a homeomorphism. -/
noncomputable def transportStr {M M' : Type u} [TopologicalSpace M] [TopologicalSpace M']
    (e : M ≃ₜ M') (s : 𝔐.Str M) : 𝔐.Str M' :=
  letI := s.1; haveI := s.2; ⟨transportChartedSpace 𝔐.Y e, transport_hasGroupoid e⟩

variable {𝔐}

/-- Level-B morphisms are abstract `𝕄≥0`-morphisms (from B3 `chartIso_mem`,
`absolutelyMinimalOn_Y`). -/
theorem isEMorphismOn_of_isMor {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    {s : 𝔐.Str M} {t : 𝔐.Str N} {W : Opens M} {f : M → N} (h : IsMor s t W f) :
    IsEMorphismOn (causality s) (causality t) W f := by
  letI := s.1; haveI := s.2; letI := t.1; haveI := t.2
  exact isEMorphismOn_of_liftPropOn 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y h

variable (𝔐)

/-- **A3 future, for a local model** (the statement of `Geometry.germExt_future`). -/
def GermExtFuture : Prop :=
  ∀ {M N : Type u} [TopologicalSpace M] [TopologicalSpace N] [T2Space M]
    [ConnectedSpace M] [T2Space N] [ConnectedSpace N] (s : 𝔐.Str M) (t : 𝔐.Str N) (U : Opens M)
    (ψ : M → N) (S : Set M) (h : IsMor s t U ψ), InjOn ψ U →
    (causality s).GloballyHyperbolic → (causality t).GloballyHyperbolic →
    (causality s).GloballyHyperbolicOn U →
    (causality t).GloballyHyperbolicOn ((isEMorphismOn_of_isMor h).imageOpens U le_rfl) →
    S ⊆ U → (causality s).IsCauchySurface S → (causality s).IsCauchySurfaceOn U S →
    (causality t).IsCauchySurface (ψ '' S) →
    (causality t).IsCauchySurfaceOn ((isEMorphismOn_of_isMor h).imageOpens U le_rfl) (ψ '' S) →
    ∀ p : M, ∀ q : N, p ∈ frontier (U : Set M) → p ∈ (causality s).Jplus ⊤ S →
      MapClusterPt q (𝓝[(U : Set M)] p) ψ →
      ∃ (O : Opens M) (φ : M → N), p ∈ O ∧ IsMor s t O φ ∧ φ p = q ∧ EqOn φ ψ (O ⊓ U : Opens M)

/-- **A3 past, for a local model** (the statement of `Geometry.germExt_past`). -/
def GermExtPast : Prop :=
  ∀ {M N : Type u} [TopologicalSpace M] [TopologicalSpace N] [T2Space M]
    [ConnectedSpace M] [T2Space N] [ConnectedSpace N] (s : 𝔐.Str M) (t : 𝔐.Str N) (U : Opens M)
    (ψ : M → N) (S : Set M) (h : IsMor s t U ψ), InjOn ψ U →
    (causality s).GloballyHyperbolic → (causality t).GloballyHyperbolic →
    (causality s).GloballyHyperbolicOn U →
    (causality t).GloballyHyperbolicOn ((isEMorphismOn_of_isMor h).imageOpens U le_rfl) →
    S ⊆ U → (causality s).IsCauchySurface S → (causality s).IsCauchySurfaceOn U S →
    (causality t).IsCauchySurface (ψ '' S) →
    (causality t).IsCauchySurfaceOn ((isEMorphismOn_of_isMor h).imageOpens U le_rfl) (ψ '' S) →
    ∀ p : M, ∀ q : N, p ∈ frontier (U : Set M) → p ∈ (causality s).Jminus ⊤ S →
      MapClusterPt q (𝓝[(U : Set M)] p) ψ →
      ∃ (O : Opens M) (φ : M → N), p ∈ O ∧ IsMor s t O φ ∧ φ p = q ∧ EqOn φ ψ (O ⊓ U : Opens M)

/-- **A4 future, for a local model** (the statement of `Geometry.slice_future`). -/
def SliceFuture : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] (s : 𝔐.Str M)
    (U : Opens M) (S : Set M), (causality s).GloballyHyperbolic →
    (causality s).GloballyHyperbolicOn U → S ⊆ U → (causality s).IsCauchySurface S →
    (causality s).IsCauchySurfaceOn U S → ∀ p : M, p ∈ frontier (U : Set M) →
    p ∈ (causality s).Jplus ⊤ S →
    (causality s).Jminus ⊤ {p} ∩ frontier (U : Set M) ∩ (causality s).Jplus ⊤ S = {p} →
    ∀ O : Opens M, p ∈ O → ∃ U' : Opens M, U < U' ∧ (U' : Set M) ⊆ U ∪ O ∧
      (causality s).GloballyHyperbolicOn U' ∧ (causality s).IsCauchySurfaceOn U' S

/-- **A4 past, for a local model** (the statement of `Geometry.slice_past`). -/
def SlicePast : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] (s : 𝔐.Str M)
    (U : Opens M) (S : Set M), (causality s).GloballyHyperbolic →
    (causality s).GloballyHyperbolicOn U → S ⊆ U → (causality s).IsCauchySurface S →
    (causality s).IsCauchySurfaceOn U S → ∀ p : M, p ∈ frontier (U : Set M) →
    p ∈ (causality s).Jminus ⊤ S →
    (causality s).Jplus ⊤ {p} ∩ frontier (U : Set M) ∩ (causality s).Jminus ⊤ S = {p} →
    ∀ O : Opens M, p ∈ O → ∃ U' : Opens M, U < U' ∧ (U' : Set M) ⊆ U ∪ O ∧
      (causality s).GloballyHyperbolicOn U' ∧ (causality s).IsCauchySurfaceOn U' S

end LocalModel

namespace Geometry

/-- **Level B ⇒ Level A, modulo A3/A4** (design §2 `Geometry.ofLocalModel`): every field of
`Geometry` except the germ extensions (A3) and the slices (A4) is derived from the local model;
those four are taken as hypotheses, so that an instance proving them (e.g. the flat one,
package 12) gets a sorry-free `Geometry`. -/
noncomputable def ofLocalModelOfGermSlice (𝔐 : LocalModel.{u}) (hA3f : 𝔐.GermExtFuture)
    (hA3p : 𝔐.GermExtPast) (hA4f : 𝔐.SliceFuture) (hA4p : 𝔐.SlicePast) : Geometry.{u} where
  toPreGeometry := 𝔐.toPreGeometry
  isMor_mono {M N} _ _ {s t W W' f} h hle := by
    letI := s.1; letI := t.1
    exact liftPropOn_mono_of_le W.isOpen W'.isOpen h hle
  isMor_of_locally {M N} _ _ {s t W f} h := by
    letI := s.1; letI := t.1
    refine liftPropOn_of_locally W.isOpen fun x hx => ?_
    obtain ⟨V, hVW, hxV, hV⟩ := h x hx
    exact ⟨V, V.isOpen, hVW, hxV, hV⟩
  isMor_id {M} _ s W := by
    letI := s.1
    exact liftPropOn_id W.isOpen
  isMor_comp {M N P} _ _ _ {s t r W V f g} hg hf hmaps := by
    letI := s.1; letI := t.1; letI := r.1
    exact liftPropOn_comp W.isOpen V.isOpen hg hf hmaps
  isMor_congr {M N} _ _ {s t W f g} h hfg := by
    letI := s.1; letI := t.1
    exact liftPropOn_congr_of_eqOn W.isOpen h hfg
  isEMorphismOn_of_isMor h := LocalModel.isEMorphismOn_of_isMor h
  absolutelyMinimalOn {M} _ s W := by
    letI := s.1; haveI := s.2
    exact chartedCausality_absolutelyMinimalOn 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y W
  isMor_inv {M N} _ _ _ {s t W f} h hinj := by
    letI := s.1; letI := t.1
    exact liftPropOn_invFunOn W.isOpen h hinj
  restrict s W := 𝔐.restrictStr s W
  isMor_corestrict_iff {M N} _ _ s W t V g := by
    letI := s.1; haveI := s.2; letI := t.1
    exact forall₂_congr fun x _ => (liftPropWithinAt_subtypeVal_comp_iff g (V : Set N) x).symm
  transport e s := 𝔐.transportStr e s
  isMor_transport {M M'} _ _ e s := by
    letI := s.1; haveI := s.2
    exact liftPropOn_transport e
  glue {Z} _ {ι} M _ s e he hcov htrans := by
    let ι' := {i : ι // Nonempty (M i)}
    let M' : ι' → Type u := fun i => M i.1
    letI : ∀ i : ι', Nonempty (M' i) := fun i => i.2
    letI : ∀ i : ι', ChartedSpace 𝔐.Y (M' i) := fun i => (s i.1).1
    haveI : ∀ i : ι', HasGroupoid (M' i) 𝔐.G := fun i => (s i.1).2
    let e' : ∀ i : ι', M' i → Z := fun i => e i.1
    have he' : ∀ i, IsOpenEmbedding (e' i) := fun i => he i.1
    have hcov' : ∀ z, ∃ i, z ∈ range (e' i) := fun z => by
      obtain ⟨i, x, hx⟩ := hcov z
      exact ⟨⟨i, ⟨x⟩⟩, x, hx⟩
    have htrans' : ∀ i j : ι', LiftPropOn 𝔐.G.IsLocalStructomorphWithinAt
        (glueTransition he' i j) (e' i ⁻¹' range (e' j)) := by
      intro i j
      obtain ⟨φ, hφ, hφe⟩ := htrans i.1 j.1
      refine liftPropOn_congr_of_eqOn ((he j.1).isOpen_range.preimage (he i.1).continuous) hφ ?_
      intro x hx
      show φ x = (glueEmb he' j).symm (e i.1 x)
      rw [← hφe x hx]
      exact (glueEmb_symm_apply he' j (φ x)).symm
    refine ⟨⟨gluedChartedSpace 𝔐.Y he' hcov', gluedChartedSpace_hasGroupoid he' hcov' htrans'⟩,
      fun i => ?_⟩
    by_cases hi : Nonempty (M i)
    · exact liftPropOn_glue he' hcov' htrans' ⟨i, hi⟩
    · intro x
      exact absurd ⟨x⟩ hi
  rigid {M N} _ _ _ s t := by
    letI := s.1; letI := t.1
    intro V hV f g hf hg O hOV hOne hfg
    exact eqOn_of_liftPropOn 𝔐.rigid V.isOpen hV.isPreconnected hf hg O.isOpen hOV hOne hfg
  sing s α := LocalModel.sing s α
  isMor_sing {M N} _ _ {s t W f} h {x} hx {α} hα := by
    letI := s.1; letI := t.1
    exact mem_chartedSing_iff_of_liftPropOn 𝔐.sing_mem W.isOpen h hx hα
  singularFlatAxioms {M} _ _ _ _ s := by
    letI := s.1; haveI := s.2
    exact 𝔐.singularFlatAxioms
  curvesExtend {M} _ _ _ _ s hGH := by
    letI := s.1; haveI := s.2
    exact 𝔐.curvesExtend hGH
  timeFunction {M} _ _ _ _ s hGH := by
    letI := s.1; haveI := s.2
    exact 𝔐.timeFunction hGH
  isCompact_Jplus_inter_Jminus {M} _ _ _ _ s hGH S hS p := by
    letI := s.1; haveI := s.2
    exact 𝔐.isCompact_Jplus_inter_Jminus hGH S hS p
  isCompact_Jminus_inter_Jplus {M} _ _ _ _ s hGH S hS p := by
    letI := s.1; haveI := s.2
    exact 𝔐.isCompact_Jminus_inter_Jplus hGH S hS p
  secondCountable_of_cauchy {M} _ _ _ s hGH S hS hSc := by
    letI := s.1; haveI := s.2
    exact 𝔐.secondCountable_of_cauchy hGH S hS hSc
  germExt_future := hA3f
  germExt_past := hA3p
  slice_future := hA4f
  slice_past := hA4p

end Geometry

/-! ### The B2 step of A3, with the connectedness made a hypothesis

What A3 needs from Level B, isolated: on a **connected** piece `A` of `U` adherent to `p`, B2
gives one element of `G`, hence an extension of `ψ` to a neighbourhood of `p`. Supplying the
connected piece (and putting `ψ(A)` into a chart at `q`) is the causal part of Sbierski Lemma 3.8
(Prop 3.7, causal convexity), which is not Level B. -/

namespace LocalModel

variable {𝔐 : LocalModel.{u}} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace 𝔐.Y M] [ChartedSpace 𝔐.Y N] [HasGroupoid M 𝔐.G] [HasGroupoid N 𝔐.G]

/-- **The extension from one element of `G`.** If `κ' ∘ ψ = e ∘ κ` on `A`, the map
`κ'.symm ∘ e ∘ κ` is a morphism on the open set where it is defined and agrees with `ψ` on `A`
there. -/
theorem exists_extension_of_eqOn {κ : OpenPartialHomeomorph M 𝔐.Y}
    {κ' : OpenPartialHomeomorph N 𝔐.Y} (hκ : κ ∈ 𝔐.G.maximalAtlas M)
    (hκ' : κ' ∈ 𝔐.G.maximalAtlas N) {e : OpenPartialHomeomorph 𝔐.Y 𝔐.Y} (he : e ∈ 𝔐.G)
    {ψ : M → N} {A : Set M} (hAψ : MapsTo ψ A κ'.source)
    (heq : ∀ z ∈ A, κ' (ψ z) = e (κ z)) :
    ∃ O : Set M, IsOpen O ∧ O = κ.source ∩ κ ⁻¹' (e.source ∩ e ⁻¹' κ'.target) ∧
      LiftPropOn 𝔐.G.IsLocalStructomorphWithinAt (κ'.symm ∘ e ∘ κ) O ∧
      EqOn (κ'.symm ∘ e ∘ κ) ψ (O ∩ A) := by
  have hO : IsOpen (κ.source ∩ κ ⁻¹' (e.source ∩ e ⁻¹' κ'.target)) :=
    κ.isOpen_inter_preimage (e.isOpen_inter_preimage κ'.open_target)
  refine ⟨_, hO, rfl, ?_, ?_⟩
  · refine liftPropOn_of_maximalAtlas_rep hκ hκ' hO (fun z hz => hz.1) ?_ ?_ he
      (fun z hz => hz.2.1) ?_
    · intro z hz; exact κ'.map_target hz.2.2
    · refine κ'.continuousOn_symm.comp (e.continuousOn.comp (κ.continuousOn.mono fun z hz => hz.1) ?_) ?_
      · intro z hz; exact hz.2.1
      · intro z hz; exact hz.2.2
    · intro z hz
      simp only [comp_apply]
      exact κ'.right_inv hz.2.2
  · intro z hz
    simp only [comp_apply]
    rw [← heq z hz.2, κ'.left_inv (hAψ hz.2)]

omit [HasGroupoid M 𝔐.G] [HasGroupoid N 𝔐.G] in
/-- **B2 at a regular point** (`localUnique_reg`, chart-independent form): an injective morphism
`ψ` on a **preconnected** non-empty open `A`, read in charts `κ`, `κ'` of the maximal atlases
landing in fully regular components (as `regularChart` provides), is one element `e` of `G`
there, defined on the components of `κ(A)`. -/
theorem exists_eqOn_of_connected_reg {κ : OpenPartialHomeomorph M 𝔐.Y}
    {κ' : OpenPartialHomeomorph N 𝔐.Y} (hκ : κ ∈ 𝔐.G.maximalAtlas M)
    (hκ' : κ' ∈ 𝔐.G.maximalAtlas N) {ψ : M → N} {A : Set M} (hAo : IsOpen A)
    (hAc : IsPreconnected A) (hAne : A.Nonempty) (hA : A ⊆ κ.source) (hAψ : MapsTo ψ A κ'.source)
    (hψ : LiftPropOn 𝔐.G.IsLocalStructomorphWithinAt ψ A) (hinj : InjOn ψ A)
    (hreg : ∀ z ∈ A, ∀ w ∈ connectedComponent (κ z), w ∈ 𝔐.regY)
    (hreg' : ∀ z ∈ A, ∀ w ∈ connectedComponent (κ' (ψ z)), w ∈ 𝔐.regY) :
    ∃ e ∈ 𝔐.G, (∀ z ∈ A, connectedComponent (κ z) ⊆ e.source) ∧
      ∀ z ∈ A, κ' (ψ z) = e (κ z) := by
  have hG := isLocalStructomorphWithinAt_localInvariantProp 𝔐.G
  set U := κ '' A
  have hUo : IsOpen U := κ.isOpen_image_of_subset_source hAo hA
  have hUc : IsConnected U := ⟨hAne.image _, hAc.image _ (κ.continuousOn.mono hA)⟩
  set f : 𝔐.Y → 𝔐.Y := κ' ∘ ψ ∘ κ.symm
  have hfA : ∀ z ∈ A, f (κ z) = κ' (ψ z) := fun z hz => by
    simp only [f, comp_apply, κ.left_inv (hA hz)]
  have hloc : ∀ y ∈ U, 𝔐.G.IsLocalStructomorphWithinAt f U y := by
    rintro _ ⟨z, hz, rfl⟩
    have hP := hG.liftPropOn_indep_chart hκ hκ' hψ
      (y := κ z) ⟨κ.map_source (hA hz), by
        simp only [mem_preimage, κ.left_inv (hA hz)]; exact ⟨hz, hAψ hz⟩⟩
    intro hy
    obtain ⟨e, he, hef, hex⟩ := hP (by simp only [mem_preimage, κ.left_inv (hA hz)]; exact hz)
    refine ⟨e, he, fun y hy => hef ⟨?_, hy.2⟩, hex⟩
    obtain ⟨w, hw, rfl⟩ := hy.1
    simp only [mem_preimage, κ.left_inv (hA hw)]; exact hw
  have hinjf : InjOn f U := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    rw [hfA a ha, hfA b hb] at hab
    rw [hinj ha hb (κ'.injOn (hAψ ha) (hAψ hb) hab)]
  have hmaps : MapsTo f U {z | ∀ w ∈ connectedComponent z, ∀ α : ℝ, 0 ≤ α → w ∉ 𝔐.singY α} := by
    rintro _ ⟨z, hz, rfl⟩ w hw
    rw [hfA z hz] at hw
    exact hreg' z hz w hw
  obtain ⟨e, he, hsrc, heq⟩ := 𝔐.localUnique_reg U hUo hUc
    (by rintro _ ⟨z, hz, rfl⟩ w hw; exact hreg z hz w hw) f hloc hinjf hmaps
  refine ⟨e, he, fun z hz => hsrc _ ⟨z, hz, rfl⟩, fun z hz => ?_⟩
  rw [← hfA z hz]
  exact heq ⟨z, hz, rfl⟩

omit [HasGroupoid M 𝔐.G] [HasGroupoid N 𝔐.G] in
/-- **B2 at a singular point** (`localUnique_sing`, chart-independent form): an injective
morphism `ψ` on the regular part `Bʳ = B ∩ κ⁻¹ reg(Y)` of a preconnected open `B ⊆ κ.source`
containing a point `b₀` with `κ b₀` singular, read in charts `κ`, `κ'`, with values in the
component of `κ b₀` (the same model), is one element `e` of `G` on `Bʳ`, defined on that whole
component. This is the form gx's past-side example needs (`U ∩ O = reg(O)`); it does **not**
cover a connected regular piece of `U` adherent to `p` that is not the whole of `reg(O)`. -/
theorem exists_eqOn_of_connected_sing {κ : OpenPartialHomeomorph M 𝔐.Y}
    {κ' : OpenPartialHomeomorph N 𝔐.Y} (hκ : κ ∈ 𝔐.G.maximalAtlas M)
    (hκ' : κ' ∈ 𝔐.G.maximalAtlas N) {ψ : M → N} {B : Set M} (hBo : IsOpen B)
    (hBc : IsPreconnected B) (hB : B ⊆ κ.source) {b₀ : M} (hb₀ : b₀ ∈ B) {α₀ : ℝ} (hα₀ : 0 ≤ α₀)
    (hsing : κ b₀ ∈ 𝔐.singY α₀)
    (hAψ : MapsTo ψ (B ∩ κ ⁻¹' 𝔐.regY) κ'.source)
    (hψ : LiftPropOn 𝔐.G.IsLocalStructomorphWithinAt ψ (B ∩ κ ⁻¹' 𝔐.regY))
    (hinj : InjOn ψ (B ∩ κ ⁻¹' 𝔐.regY))
    (hcomp : ∀ z ∈ B ∩ κ ⁻¹' 𝔐.regY, κ' (ψ z) ∈ connectedComponent (κ b₀)) :
    ∃ e ∈ 𝔐.G, connectedComponent (κ b₀) ⊆ e.source ∧
      ∀ z ∈ B ∩ κ ⁻¹' 𝔐.regY, κ' (ψ z) = e (κ z) := by
  have hG := isLocalStructomorphWithinAt_localInvariantProp 𝔐.G
  set A := B ∩ κ ⁻¹' 𝔐.regY
  have hA : A ⊆ κ.source := fun z hz => hB hz.1
  set U := κ '' B
  have hUo : IsOpen U := κ.isOpen_image_of_subset_source hBo hB
  have hUc : IsConnected U := ⟨⟨_, b₀, hb₀, rfl⟩, hBc.image _ (κ.continuousOn.mono hB)⟩
  have hreg : U ∩ 𝔐.regY = κ '' A := by
    ext y
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hy⟩; exact ⟨z, ⟨hz, hy⟩, rfl⟩
    · rintro ⟨z, hz, rfl⟩; exact ⟨⟨z, hz.1, rfl⟩, hz.2⟩
  set f : 𝔐.Y → 𝔐.Y := κ' ∘ ψ ∘ κ.symm
  have hfA : ∀ z ∈ A, f (κ z) = κ' (ψ z) := fun z hz => by
    simp only [f, comp_apply, κ.left_inv (hA hz)]
  have hloc : ∀ y ∈ U ∩ 𝔐.regY, 𝔐.G.IsLocalStructomorphWithinAt f (U ∩ 𝔐.regY) y := by
    rw [hreg]
    rintro _ ⟨z, hz, rfl⟩
    have hP := hG.liftPropOn_indep_chart hκ hκ' hψ
      (y := κ z) ⟨κ.map_source (hA hz), by
        simp only [mem_preimage, κ.left_inv (hA hz)]; exact ⟨hz, hAψ hz⟩⟩
    intro hy
    obtain ⟨e, he, hef, hex⟩ := hP (by simp only [mem_preimage, κ.left_inv (hA hz)]; exact hz)
    refine ⟨e, he, fun y hy => hef ⟨?_, hy.2⟩, hex⟩
    obtain ⟨w, hw, rfl⟩ := hy.1
    simp only [mem_preimage, κ.left_inv (hA hw)]; exact hw
  have hinjf : InjOn f (U ∩ 𝔐.regY) := by
    rw [hreg]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    rw [hfA a ha, hfA b hb] at hab
    rw [hinj ha hb (κ'.injOn (hAψ ha) (hAψ hb) hab)]
  have hmaps : MapsTo f (U ∩ 𝔐.regY) (connectedComponent (κ b₀)) := by
    rw [hreg]
    rintro _ ⟨z, hz, rfl⟩
    rw [hfA z hz]; exact hcomp z hz
  obtain ⟨e, he, hsrc, heq⟩ := 𝔐.localUnique_sing U hUo hUc (κ b₀) ⟨b₀, hb₀, rfl⟩ α₀ hα₀ hsing
    f hloc hinjf hmaps
  refine ⟨e, he, hsrc, fun z hz => ?_⟩
  rw [← hfA z hz]
  have hmem : κ z ∈ U ∩ 𝔐.regY := by rw [hreg]; exact ⟨z, hz, rfl⟩
  exact heq hmem

omit [ChartedSpace 𝔐.Y M] [ChartedSpace 𝔐.Y N] [HasGroupoid M 𝔐.G] [HasGroupoid N 𝔐.G] in
/-- **Sbierski Def 3.5 read in charts**: if `q` is a cluster point of `ψ` along `A` at `p`, then
`κ' q` is a cluster point of `κ' ∘ ψ ∘ κ.symm` along `κ '' A` at `κ p` (the cluster hypothesis
of `localUnique_sing_adherent`, from A3's `MapClusterPt q (𝓝[U] p) ψ`). -/
theorem mapClusterPt_chart {κ : OpenPartialHomeomorph M 𝔐.Y} {κ' : OpenPartialHomeomorph N 𝔐.Y}
    {ψ : M → N} {A : Set M} (hA : A ⊆ κ.source) {p : M} (hp : p ∈ κ.source) {q : N}
    (hq : q ∈ κ'.source) (h : MapClusterPt q (𝓝[A] p) ψ) :
    MapClusterPt (κ' q) (𝓝[κ '' A] (κ p)) (κ' ∘ ψ ∘ κ.symm) := by
  have h1 : 𝓝[κ '' A] (κ p) = map κ (𝓝[A] p) := by
    rw [κ.map_nhdsWithin_eq hp, inter_eq_right.2 hA]
  rw [h1, ← mapClusterPt_comp]
  have h2 : (κ' ∘ ψ ∘ κ.symm) ∘ κ =ᶠ[𝓝[A] p] κ' ∘ ψ :=
    eventually_nhdsWithin_of_forall fun z hz => by simp [κ.left_inv (hA hz)]
  rw [h2.mapClusterPt_iff]
  exact h.continuousAt_comp (κ'.continuousAt hq)

omit [HasGroupoid M 𝔐.G] [HasGroupoid N 𝔐.G] in
/-- **B2 at a singular point, past side, in charts** (`localUnique_sing_adherent`, interface
round 2 (2), chart-independent form): an injective morphism `ψ` on a preconnected non-empty open
`A ⊆ κ.source` of points with **regular** chart image, read in charts `κ`, `κ'` of the maximal
atlases, with values in the component of a singular `y₀ ∈ sing_{α₀}`, clustering at `z₀ ∈ sing_{α₀}`
along `κ '' A` at `y₀`, and with `κ '' A` satisfying the field's largeness clause **verbatim**
(`hlarge`), is one element `e` of `G` on `A`, defined on the whole component of `y₀`.

The largeness clause is passed through as a hypothesis, never produced: at `α₀ = 0` it is
satisfiable by `r := y₀` whenever `I⁻(y₀) = ∅` (`Causality.BTZAxiomsCorr.exists_le_inter_Iminus_subset`),
which is the finding against the clause, so `LocalModel.germExtPast` does **not** close its BTZ
case through this lemma (see its `SORRY`). What A3-past produces is the chart image of
`U ∩ I⁻_W(r) ⊇ I⁺_W(p) ∩ I⁻_W(r)` (`Causality.CausallyConvexIn.Iplus_inter_Iminus_subset`,
`chartedCausality_image_Iplus_inter_Iminus`). -/
theorem exists_eqOn_of_connected_sing_adherent {κ : OpenPartialHomeomorph M 𝔐.Y}
    {κ' : OpenPartialHomeomorph N 𝔐.Y} (hκ : κ ∈ 𝔐.G.maximalAtlas M)
    (hκ' : κ' ∈ 𝔐.G.maximalAtlas N) {ψ : M → N} {A : Set M} (hAo : IsOpen A)
    (hAc : IsPreconnected A) (hAne : A.Nonempty) (hA : A ⊆ κ.source)
    (hAreg : ∀ z ∈ A, κ z ∈ 𝔐.regY) {y₀ : 𝔐.Y} {α₀ : ℝ} (hα₀ : 0 ≤ α₀)
    (hsing : y₀ ∈ 𝔐.singY α₀)
    (hlarge : ∃ O : Opens 𝔐.Y, y₀ ∈ O ∧ ∃ r ∈ O, 𝔐.causalityY.le O y₀ r ∧
      𝔐.regY ∩ 𝔐.causalityY.Iminus O {r} ⊆ κ '' A)
    {z₀ : 𝔐.Y} (hz₀ : z₀ ∈ 𝔐.singY α₀) (hAψ : MapsTo ψ A κ'.source)
    (hψ : LiftPropOn 𝔐.G.IsLocalStructomorphWithinAt ψ A) (hinj : InjOn ψ A)
    (hcomp : ∀ z ∈ A, κ' (ψ z) ∈ connectedComponent y₀)
    (hclus : MapClusterPt z₀ (𝓝[κ '' A] y₀) (κ' ∘ ψ ∘ κ.symm)) :
    ∃ e ∈ 𝔐.G, connectedComponent y₀ ⊆ e.source ∧ ∀ z ∈ A, κ' (ψ z) = e (κ z) := by
  have hG := isLocalStructomorphWithinAt_localInvariantProp 𝔐.G
  set U := κ '' A
  have hUo : IsOpen U := κ.isOpen_image_of_subset_source hAo hA
  have hUc : IsConnected U := ⟨hAne.image _, hAc.image _ (κ.continuousOn.mono hA)⟩
  have hUreg : U ⊆ {y | ∀ α : ℝ, 0 ≤ α → y ∉ 𝔐.singY α} := by
    rintro _ ⟨z, hz, rfl⟩; exact hAreg z hz
  set f : 𝔐.Y → 𝔐.Y := κ' ∘ ψ ∘ κ.symm
  have hfA : ∀ z ∈ A, f (κ z) = κ' (ψ z) := fun z hz => by
    simp only [f, comp_apply, κ.left_inv (hA hz)]
  have hloc : ∀ y ∈ U, 𝔐.G.IsLocalStructomorphWithinAt f U y := by
    rintro _ ⟨z, hz, rfl⟩
    have hP := hG.liftPropOn_indep_chart hκ hκ' hψ
      (y := κ z) ⟨κ.map_source (hA hz), by
        simp only [mem_preimage, κ.left_inv (hA hz)]; exact ⟨hz, hAψ hz⟩⟩
    intro hy
    obtain ⟨e, he, hef, hex⟩ := hP (by simp only [mem_preimage, κ.left_inv (hA hz)]; exact hz)
    refine ⟨e, he, fun y hy => hef ⟨?_, hy.2⟩, hex⟩
    obtain ⟨w, hw, rfl⟩ := hy.1
    simp only [mem_preimage, κ.left_inv (hA hw)]; exact hw
  have hinjf : InjOn f U := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    rw [hfA a ha, hfA b hb] at hab
    rw [hinj ha hb (κ'.injOn (hAψ ha) (hAψ hb) hab)]
  have hmaps : MapsTo f U (connectedComponent y₀) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [hfA z hz]; exact hcomp z hz
  obtain ⟨e, he, hsrc, heq⟩ := 𝔐.localUnique_sing_adherent U hUo hUc hUreg y₀ α₀ hα₀ hsing
    hlarge z₀ hz₀ f hloc hinjf hmaps hclus
  refine ⟨e, he, hsrc, fun z hz => ?_⟩
  rw [← hfA z hz]
  exact heq ⟨z, hz, rfl⟩

end LocalModel

/-! ### A3 and A4 for a local model: stated, not derived -/

namespace LocalModel

variable (𝔐 : LocalModel.{u})

/-- **A3 future from Level B** (Sbierski Lemma 3.8; `cor:ext_continue`). Not derived here: see
the obstruction. The B2 step is proved (`exists_eqOn_of_connected_reg`/`_sing`,
`exists_extension_of_eqOn`); the causal part and the second countability are not. -/
theorem germExtFuture : 𝔐.GermExtFuture := by
  sorry -- SORRY(cor:ext_continue): (0) the field has no `[SecondCountableTopology M]`/`[… N]`, while every B3 fact the proof needs (`singularFlatAxioms`, `curvesExtend`, `timeFunction`, `isCompact_*`) is stated for second-countable carriers only and `secondCountable_of_cauchy` needs a second-countable Cauchy surface, which is not given — so A3 as stated is not derivable from Level B by Sbierski's route at all (interface: add SC of M and N to A3, consumers `CGHDData.ext_continue`/`NoCorresponding.exists_extension` have SC of M in scope); (i) Sbierski Prop 3.7: the A3-free core exists (`CGHDData.corresponding_K`, A2 only, `lem:Sigma_separe` derived) but is stated over a `𝔊 : Geometry`, whose A3/A4 fields are what this proves, so it must be re-instantiated on `chartedCausality` (or `Geometry` split into an A1/A2 core); (ii) Lemma 3.8 itself: r ∈ U ∩ I⁻(p) with the diamond J⁺(ψ r) ∩ J⁻(q) inside the chart at q (strong causality of N), the connectedness of U ∩ I⁺_W(r′) (causal convexity, push-up, `causallyArcConnected`), agreement with the extension on O ∩ U by A1; (iii) at a BTZ p, a singular point of p's line below p in U (`lem:passe_pgcd`, `these.tex:6541`), so that `exists_eqOn_of_connected_sing` applies

/-- **A3 past from Level B** (Sbierski Lemma 3.8, the `K⁺` side). Not derived here. At a BTZ
boundary point the piece is the chart image of `U ∩ I⁻_W(r) ⊇ I⁺_W(p) ∩ I⁻_W(r)`
(`Causality.CausallyConvexIn.Iplus_inter_Iminus_subset`, `chartedCausality_image_Iplus_inter_Iminus`),
and the round-2 clause is met by it only vacuously (see the `SORRY`). -/
theorem germExtPast : 𝔐.GermExtPast := by
  sorry -- SORRY(cor:ext_continue): (0)–(ii) as `germExtFuture` (no SC of M, N in the field; Prop 3.7 core over a `Geometry`; Lemma 3.8's causal part, with r ∈ U ∩ I⁺(p) ∩ J⁻(S)). (iii) At a BTZ p the connected piece is A = U ∩ I⁻_W(r), r ∈ U regular above p; proved: A ⊇ I⁺_W(p) ∩ I⁻_W(r), read in the chart as I⁺_O(y₀) ∩ I⁻_O(κ r), O = κ(W), y₀ = κ p; in gx's example (`A3-B-INVESTIGATION.md`, U = I⁺(0) ∪ {τ + r > 1/2}) A is exactly that diamond near p. `localUnique_sing_adherent`'s clause ∃ O ∋ y₀, ∃ r′ ∈ O, y₀ ≤_O r′ ∧ reg ∩ I⁻_O(r′) ⊆ κ(A) is met by this piece ONLY vacuously (r′ := y₀ or r′ on the line, I⁻_O(r′) = ∅, `BTZAxiomsCorr.exists_le_inter_Iminus_subset`); with r′ regular (the intended repair) it fails on gx's example whenever y₀ ≪_O r′ (by hand: I⁻_O(r′) is then an open neighbourhood of y₀, while J⁺(p) is closed (GH) and not a neighbourhood of p (kb/0017, J⁻(p) ⊋ {p}), so with reg dense I⁻_O(r′) holds regular points near p outside J⁺(p) ⊇ the diamond); for regular r′ ∈ J⁺(p) ∖ I⁺(p) (the radial null ray) not settled. Not closed via the vacuity. The clause this piece meets is the diamond form ∃ O ∋ y₀, ∃ r′ ∈ O, y₀ ≪_O r′ ∧ reg ∩ I⁺_O(y₀) ∩ I⁻_O(r′) ⊆ U (gx to adopt or adapt); `exists_eqOn_of_connected_sing_adherent` then transfers verbatim

/-- **A4 future from Level B** (Sbierski Thm 3.6, the slice `τ_q`, Lemma 3.11). Not derived
here. -/
theorem sliceFuture : 𝔐.SliceFuture := by
  sorry -- SORRY(theo:CBG): (0) as A3, the field has no `[SecondCountableTopology M]` and every B3 fact used (`isCompact_Jplus_inter_Jminus`, `curvesExtend`) asks it. A4 future is the geometric half of Sbierski Thm 3.6 — Lemma 3.11 (a q ∈ I⁺(p) with J⁻(q) ∩ Uᶜ ∩ J⁺(Σ) inside the B4 neighbourhood W, from `isCompact_Jplus_inter_Jminus`), the maximum c of the B4 function τ on that compact set (attained only on ∂U), the GH open N of B4 with τ⁻¹(c) ∩ W Cauchy, and global hyperbolicity of U ∪ N with Σ Cauchy; B4 is transported to M by the chart at p (`chartedCausality_chartIso`). No library proof exists (package 6 consumes A4, `NoCorresponding.exists_extension`), and whether B4 suffices is open: B4's GH open N is any one with τ⁻¹(c) ∩ W Cauchy in N, nothing ties N to the side of τ⁻¹(c) that U ∪ N must add

/-- **A4 past from Level B** (no time reversal). Not derived here. -/
theorem slicePast : 𝔐.SlicePast := by
  sorry -- SORRY(theo:CBG): A4 past, as A4 future (no SC of M in the field) with B4 `slice_past`, `isCompact_Jminus_inter_Jplus` and the time-reversed Lemma 3.11 (no duality, gx D-12(e))

end LocalModel

namespace Geometry

/-- **`Geometry.ofLocalModel`** (design §2): Level B ⇒ Level A. Every field is derived from the
local model (`ofLocalModelOfGermSlice`) except A3/A4, which rest on the four tagged
`LocalModel.germExtFuture`, `germExtPast`, `sliceFuture`, `slicePast`. -/
noncomputable def ofLocalModel (𝔐 : LocalModel.{u}) : Geometry.{u} :=
  ofLocalModelOfGermSlice 𝔐 𝔐.germExtFuture 𝔐.germExtPast 𝔐.sliceFuture 𝔐.slicePast

@[simp] theorem ofLocalModel_toPreGeometry (𝔐 : LocalModel.{u}) :
    (ofLocalModel 𝔐).toPreGeometry = 𝔐.toPreGeometry := rfl

end Geometry

end CBG

/-! ### The round-2 past-side largeness clause is vacuous at a BTZ point (model-free) -/

namespace Causality

variable {M : Type*} [TopologicalSpace M] {C : Causality M} {S₀ : Set M}

/-- **The chronological past of a BTZ point is empty in every open set**: `I⁻_O(r) = ∅` for
`r ∈ S₀`, from `BTZAxiomsCorr.Iminus_eq_empty` (`I⁻(r) = ∅`, `ETT.tex:1349`) and the monotonicity
of `≪` in the open set. -/
theorem BTZAxiomsCorr.Iminus_opens_eq_empty (h : C.BTZAxiomsCorr S₀) {r : M} (hr : r ∈ S₀)
    (O : Opens M) : C.Iminus O {r} = ∅ :=
  Set.eq_empty_of_subset_empty
    ((C.Iminus_mono_opens le_top).trans (h.Iminus_eq_empty r hr).subset)

/-- For `r` on the BTZ locus, `R ∩ I⁻_O(r) ⊆ U` holds for every `R` and `U`: a largeness clause
of the shape `reg ∩ I⁻_O(r) ⊆ U` with `r ∈ S₀` constrains nothing. -/
theorem BTZAxiomsCorr.inter_Iminus_opens_subset (h : C.BTZAxiomsCorr S₀) {r : M} (hr : r ∈ S₀)
    (O : Opens M) (R U : Set M) : R ∩ C.Iminus O {r} ⊆ U := by
  rw [h.Iminus_opens_eq_empty hr O, inter_empty]
  exact empty_subset U

/-- **The round-2 past-side clause, as transcribed, holds for every `U`** (design §6 "Interface
round 2" (2): `∃ r ∈ O, y₀ ≤_O r ∧ reg ∩ I⁻_O(r) ⊆ U`): take `r := y₀`. So a field
`localUnique_sing_adherent` guarded by it is the point-contact form, which the cone
counterexample (REPORT, interface needs (1)) refutes in `E₀`. -/
theorem BTZAxiomsCorr.exists_le_inter_Iminus_subset (h : C.BTZAxiomsCorr S₀) {y₀ : M}
    (hy₀ : y₀ ∈ S₀) {O : Opens M} (hO : y₀ ∈ O) (R U : Set M) :
    ∃ r ∈ O, C.le O y₀ r ∧ R ∩ C.Iminus O {r} ⊆ U :=
  ⟨y₀, hO, C.le_refl hO, h.inter_Iminus_opens_subset hy₀ O R U⟩

/-- **The past-side piece of A3 contains the chronological diamond above the boundary point.**
Let `U` be causally convex in the open `B` (a Cauchy inclusion is, package 2,
`causallyConvexIn_of_isCauchySurfaceOn`), `p ∈ closure U`, `r ∈ U`, `W ≤ B`. Then
`I⁺_W(p) ∩ I⁻_W(r) ⊆ U`: for `p ≪_W x ≪_W r`, the open `I⁻_B(x)` contains `p`, so meets `U` at
some `u`, and `x ∈ J_B(u, r) ⊆ U`. So the piece `U ∩ I⁻_W(r)` that Sbierski's Lemma 3.8 uses on
the past side of `Σ` (`r ∈ U` above `p`) is `⊇ I⁺_W(p) ∩ I⁻_W(r)`; in gx's past-side example
(`A3-B-INVESTIGATION.md`: `U = I⁺(0) ∪ {τ + r > 1/2}`, `Σ = {τ + r = 1}`, `p = 0` BTZ) it is
exactly that diamond near `p`. No time orientation is needed, and `p` may be BTZ. -/
theorem CausallyConvexIn.Iplus_inter_Iminus_subset {U : Set M} {B : Opens M}
    (hU : C.CausallyConvexIn U B) {p r : M} (hp : p ∈ closure U) (hr : r ∈ U) {W : Opens M}
    (hWB : W ≤ B) : C.Iplus W {p} ∩ C.Iminus W {r} ⊆ U := by
  rintro x ⟨hpx, hxr⟩
  rw [Precausality.mem_Iplus_singleton] at hpx
  rw [Precausality.mem_Iminus_singleton] at hxr
  obtain ⟨u, hux, huU⟩ := mem_closure_iff.1 hp {y | C.lt B y x} (C.isOpen_lt_left B x)
    (C.lt_mono hWB hpx)
  exact hU.2 u huU r hr
    ⟨⟨r, mem_singleton r, C.le_of_lt (C.lt_mono hWB hxr)⟩, ⟨u, mem_singleton u, C.le_of_lt hux⟩⟩

end Causality

end Causal
