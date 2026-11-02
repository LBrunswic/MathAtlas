import Causal.CBG.Geometry
import Causal.GXSingular
import Causal.CBG.FamilyGluing
import Causal.CBG.Corresponding

/-!
# Level B ⇒ Level A: the geometry of a local model (`Geometry.ofLocalModelOfBTZ`)

Package 11 of the CBG campaign (design `docs/CBG-DESIGN.md` §2 "`Geometry.ofLocalModel :
Level B → Level A`", §5 row 11; since interface round 4, 2026-11-02, the sorry-free
`Geometry.ofLocalModelOfBTZ`, the BTZ-point cases explicit hypotheses). No paper label is marked. Cited, unmarked: `theo:CBG` —
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
* **Interface round 4 (2026-11-02): `Geometry.ofLocalModelOfBTZ 𝔐 hA3f hA3p hA4f : Geometry`,
  sorry-free**: every field of Level A derived from Level B, A3 and A4 included, except their
  **BTZ-point cases**, the three explicit hypotheses `𝔐.GermExtFutureBTZ`, `𝔐.GermExtPastBTZ`,
  `𝔐.SliceFutureBTZ` (A3 future / past, A4 future, at boundary points `p ∈ sing₀`; A4 past has
  none). A3 off the BTZ locus — regular **and massive** `p` — is `germ_future_nonBTZ`,
  `germ_past_nonBTZ` (core `germ_ext_nonBTZ`), from the round-4 fields `T2Space Y`,
  `typeAgreement`, `isOpen_regY` and `dense_regY` (the last not in the agreed list); A4 is
  `slice_future_of_cone` / `slice_past_of_cone` from the fields `coneSliceFuture` /
  `coneSlicePast`. `Geometry.ofLocalModelNoBTZ 𝔐 (h0 : singY 0 = ∅)` needs no hypothesis. The
  sorried `Geometry.ofLocalModel` and `ofLocalModel_toPreGeometry` are deleted (no user).
* `Geometry.ofLocalModelOfGermSlice 𝔐 hA3f hA3p hA4f hA4p : Geometry`: **every field of Level A
  except A3/A4 derived from Level B** — interface round 2's `timeFunction` included, from
  `LocalModel.timeFunction` — A3/A4 taken as the hypotheses `𝔐.GermExtFuture`,
  `GermExtPast`, `SliceFuture`, `SlicePast` (the Level A field types read on `𝔐`).
* The B2 step of A3 with the connectedness made a hypothesis:
  `LocalModel.exists_eqOn_of_connected_reg` (B2 `localUnique_reg`, any maximal-atlas charts),
  `LocalModel.exists_eqOn_of_connected_sing` (B2 `localUnique_sing`),
  `LocalModel.exists_eqOn_of_connected_sing_adherent` (the past-side B2
  `localUnique_sing_adherent`, its largeness clause — round 3's diamond form — a hypothesis,
  passed verbatim),
  `LocalModel.mapClusterPt_chart` (Def 3.5 read in charts),
  `LocalModel.exists_extension_of_eqOn` (one element of `G` ⇒ a morphism extending `ψ`).
* **The shape of A3's past-side piece**: `Causality.CausallyConvexIn.Iplus_inter_Iminus_subset`
  (`U ∩ I⁻_W(r) ⊇ I⁺_W(p) ∩ I⁻_W(r)` for `U` causally convex, `p ∈ closure U`, `r ∈ U`; model-free)
  and its chart reading `chartedCausality_image_Iplus_inter_Iminus`.
* **Interface round 3 (2026-11-02): A3 at regular points, generic `Y`.** `germ_future_reg`,
  `germ_past_reg`: the conclusion of `GermExtFuture`/`GermExtPast` at a boundary point `p` whose
  corresponding `q` is such that both are **regular**, for any local model (`[T2Space Y]` a field
  since round 4). Core `germ_ext_reg` (any causalities `C'`, `D'`, so the past
  side is the future one for `C.dual`): a connected open piece `A ⊆ U ∩ I⁻(p)` with
  `I⁺(a) ∩ I⁻(p) ⊆ A`, inside the charts at `p`, `q` (`germ_exists_piece`: Sbierski Prop 3.7 via
  `IsCorrPair.exists_lt_forall_mem`, strong causality, causal curves from `a`, causal convexity),
  `ψ → q` along it (`germ_tendsto_of_corresponds`), B2 `localUnique_reg` through regular charts
  (`exists_regularChart_mem_maximalAtlas`), the extension `κ'⁻¹ ∘ e ∘ κ`, and B1 rigidity on the
  component of `O₀ ∩ U` through a point of `A`, which contains `O ∩ U` for an open `O ∋ p`
  (`germ_exists_open_subset_connectedComponentIn`). No chart geometry (segments, balls) is used.
  The model-free half of Prop 3.7 (`IsCorrPair.lt_of_lt_of_corresponds`, `exists_lt_forall_mem`,
  `mem_Jplus_of_corresponds`, …) is here, moved from `Flat/CBGGerm`; `isCorrPair_of_cghd` is
  `Flat/CBGGerm`'s `germ_isCorrPair` for any local model.
* **Interface round 3: A4 from a cone-slice B4, generic `Y`.** `slice_future_of_cone` (off the BTZ
  locus) and `slice_past_of_cone` (everywhere), from round 3's proposed `ConeSliceFuture`,
  `ConeSlicePast` (the `LocalModel` fields `coneSliceFuture`, `coneSlicePast` since round 4): the construction of `Flat/CBGSlice` read through
  the chart at `p` (`chart_isEMorphismOn`, `slice_assemble`, `IsEMorphismOn.isCauchySurfaceOn_image_iff`);
  the model-free assembly (`extend_of_cauchy_nbhd`, `isCauchySurfaceOn_sup_of_slice`, the cone
  lemmas) is here, moved from `Flat/CBGSlice`, plus `mem_of_le_of_mem_interior_Jplus_of_mem_Zminus`.
* **Interface round 3: the past-side piece meets the diamond clause** (`diamond_clause_of_piece`):
  `U` causally convex, `p ∈ closure U`, `r ∈ U` regular, `p ≪_W r` in a chart domain `W` ⇒
  `∃ O ∋ κ p, ∃ r' ∈ O, r' ∈ reg ∧ κ p ≪_O r' ∧ reg ∩ I⁺_O(κ p) ∩ I⁻_O(r') ⊆ κ(U ∩ I⁻_W(r) ∩ κ⁻¹ reg)`,
  the largeness clause of `localUnique_sing_adherent` as amended in round 3.

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
| design §2: A3 (`germExt_*`) from B2 + `regularChart` | ⚠ partial (round 4): derived at every boundary point `p` off the BTZ locus, regular or massive (`germExtFuture_of`, `germExtPast_of`, via `germ_future_nonBTZ`, `germ_past_nonBTZ`), from `T2Space Y`, `typeAgreement`, `isOpen_regY` (agreed) and `dense_regY` (**⚠ added, not agreed**); at BTZ `p` taken as the hypotheses `GermExtFutureBTZ`, `GermExtPastBTZ`. No `sorry` |
| design §2: A4 (`slice_*`) from B4 | ⚠ partial (round 4): derived from the cone-slice B4 fields (`slice_future_of_cone` off the BTZ locus, `slice_past_of_cone` everywhere); A4 past proved outright (`slicePast`), A4 future at BTZ `p` taken as the hypothesis `SliceFutureBTZ`. No `sorry` |

## SCOPE (disclosed)

* **Interface round 4 (2026-11-02): no `sorry`.** The seven round-3 tagged `sorry`s are gone:
  `[T2Space Y]` (A3, twice) is the field `t2Y`; the cone-slice B4 (A4, twice) are the fields
  `coneSliceFuture`/`coneSlicePast`; the singular non-BTZ cases of A3 (twice) are proved
  (`germ_ext_nonBTZ`: type agreement and same component from `typeAgreement`; the singular point
  of the piece from the massive line, `exists_massive_near`; the regular part of the piece open by
  `isOpen_regY`, dense by `dense_regY`; B2 `localUnique_sing`, extended by continuity, then the
  extension/rigidity step of `germ_ext_reg`); the BTZ cases (A3 future: `lem:passe_pgcd`; A3
  past: the regular piece above `p`; A4 future: a slice off the cone) are the explicit hypotheses
  `GermExtFutureBTZ`, `GermExtPastBTZ`, `SliceFutureBTZ` of `Geometry.ofLocalModelOfBTZ`, each
  with what gx owes for `E₀` in its docstring. **Finding (round 4): `dense_regY` is needed and is
  not in gx's agreed list** — with only `isOpen_regY`, an open piece could consist of singular
  points of uncountably many types `α`, each locus closed with empty interior, and B2 at a
  singular point would give no agreement at all; disclosed in the field, proposed to gx.
  In the future case `q` is not BTZ when `p` is not (model-free, Prop 3.7 and `I⁻ = ∅` at BTZ
  points); in the past case `typeAgreement` excludes it.
* (History, superseded by round 4.) Round 3: `Geometry.ofLocalModel 𝔐 := ofLocalModelOfGermSlice
  𝔐 …` rested on four declarations with seven tagged `sorry`s, each a named Level-B gap:
  `[T2Space Y]` (A3, twice), the singular cases of A3 (twice: type agreement and same component of
  `p`, `q`; an open set of agreement inside `reg`; BTZ future via `lem:passe_pgcd`; BTZ past via
  the diamond clause), the cone-slice B4 (A4, twice) and A4 future at BTZ points.
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
  only vacuously (next bullets). **Resolved at regular points (round 3)**: the connected piece is
  `connectedComponentIn (I⁺(x₁) ∩ I⁻(p)) a`, which contains the open diamond `I⁺(a) ∩ I⁻(p)`
  (causal curves from `a`, push-up) and lies in `U` and in both charts (strong causality at `p`,
  Prop 3.7 at `q`); agreement on all of `O ∩ U` is B1 rigidity on one component of `O₀ ∩ U`
  (causal convexity of `U` and of a strongly causal neighbourhood): `germ_ext_reg`.
* **A4** is Sbierski's slice construction (Lemma 3.11, the maximum of `τ` on the compact
  `J⁻(q) ∩ Uᶜ ∩ J⁺(Σ)`, the GH open of B4, GH of `U ∪ N`); B4 supplies only the local `τ`, and its
  transport to `M` by `chartedCausality_chartIso` is the only Level-B part. **Round 3**: the
  construction actually used is `Flat/CBGSlice`'s (a slice inside `U`, on the punctured cone of
  `p`), which needs no R1 and no Lemma 3.11; generically it needs the cone-slice B4, a
  `LocalModel` field since round 4 (`coneSliceFuture`/`coneSlicePast`), and with it A4 is proved
  (`slice_future_of_cone`, `slice_past_of_cone`); the level-set B4 was deleted in round 4.
* **`prop:GX_espace_temps_topo` / `prop:GX_sing_espace_temps_topo` are read, not proved.** The
  paper's hypotheses (analyticity, causal arc-connectedness, Baire, `G` acting by morphisms; for the
  singular form, (b) on each `X_α`) are not assumed; their two consequences used by the proof —
  every `e ∈ G` is a `ChartIso D D e`, `D` absolutely minimal on every open set — are B3 fields
  (`chartIso_mem`, `absolutelyMinimalOn_Y`). This is a different hypothesis, not a subset of the
  paper's (verdict `⚠ strengthened` in the checklist). Only the preferred charts are proved
  isomorphisms; uniqueness is not redone (`Causal/GXStructure.lean` has it for `gxGroupoid`).
* **(History; superseded by interface round 3.) The round-2 past-side largeness clause was
  vacuous as transcribed** (design §6 "Interface round 2" (2); `localUnique_sing_adherent` now
  carries round 3's diamond clause):
  `∃ r ∈ O, y₀ ≤_O r ∧ reg ∩ I⁻_O(r) ⊆ U`
  holds for every `U`, by `r := y₀` (`Causality.BTZAxiomsCorr.exists_le_inter_Iminus_subset`),
  because the chronological past of every BTZ point is empty in every open set
  (`Causality.BTZAxiomsCorr.Iminus_opens_eq_empty`, from `Iminus_eq_empty` and `lt_mono`); the same
  holds for any `r` on `y₀`'s line (`inter_Iminus_opens_subset`). With `≪` in place of `≤` the
  clause asks `U ⊇ reg(I⁻_O(r))` for an open neighbourhood `I⁻_O(r)` of `y₀`, the case
  `localUnique_sing` already covers (by hand). **A3-past (round 3's `germExtPast`) did not use the field through
  this vacuity.** The piece A3-past produces at a BTZ `p` is `U ∩ I⁻_W(r)`, `r ∈ U` regular above
  `p`, which contains the chronological diamond `I⁺_W(p) ∩ I⁻_W(r)` and in gx's example is that
  diamond near `p`; with `r` regular and `y₀ ≪_O r` the clause fails for it (by hand,
  round 3's `germExtPast` `SORRY`). The clause it does meet is the diamond form
  `∃ r ∈ O, y₀ ≪_O r ∧ reg ∩ I⁺_O(y₀) ∩ I⁻_O(r) ⊆ U` (REPORT, message for gx).
  **Round 3 adopted it** (with the regular tip `r ∈ reg`); `diamond_clause_of_piece` proves the
  piece meets it. The Lemmas of the vacuity below stay as the record of the finding.
* **(Resolved by interface round 3: the fields now carry it.) A3 and A4 carried no second
  countability, Level B's facts all do.** `germExt_*`/`slice_*` (and
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

/-! ### Level B ⇒ Level A: the structural fields -/

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
    [ConnectedSpace M] [SecondCountableTopology M] [T2Space N] [ConnectedSpace N]
    [SecondCountableTopology N] (s : 𝔐.Str M) (t : 𝔐.Str N) (U : Opens M)
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
    [ConnectedSpace M] [SecondCountableTopology M] [T2Space N] [ConnectedSpace N]
    [SecondCountableTopology N] (s : 𝔐.Str M) (t : 𝔐.Str N) (U : Opens M)
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
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [SecondCountableTopology M] (s : 𝔐.Str M) (U : Opens M) (S : Set M),
    (causality s).GloballyHyperbolic →
    (causality s).GloballyHyperbolicOn U → S ⊆ U → (causality s).IsCauchySurface S →
    (causality s).IsCauchySurfaceOn U S → ∀ p : M, p ∈ frontier (U : Set M) →
    p ∈ (causality s).Jplus ⊤ S →
    (causality s).Jminus ⊤ {p} ∩ frontier (U : Set M) ∩ (causality s).Jplus ⊤ S = {p} →
    ∀ O : Opens M, p ∈ O → ∃ U' : Opens M, U < U' ∧ (U' : Set M) ⊆ U ∪ O ∧
      (causality s).GloballyHyperbolicOn U' ∧ (causality s).IsCauchySurfaceOn U' S

/-- **A4 past, for a local model** (the statement of `Geometry.slice_past`). -/
def SlicePast : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [SecondCountableTopology M] (s : 𝔐.Str M) (U : Opens M) (S : Set M),
    (causality s).GloballyHyperbolic →
    (causality s).GloballyHyperbolicOn U → S ⊆ U → (causality s).IsCauchySurface S →
    (causality s).IsCauchySurfaceOn U S → ∀ p : M, p ∈ frontier (U : Set M) →
    p ∈ (causality s).Jminus ⊤ S →
    (causality s).Jplus ⊤ {p} ∩ frontier (U : Set M) ∩ (causality s).Jminus ⊤ S = {p} →
    ∀ O : Opens M, p ∈ O → ∃ U' : Opens M, U < U' ∧ (U' : Set M) ⊆ U ∪ O ∧
      (causality s).GloballyHyperbolicOn U' ∧ (causality s).IsCauchySurfaceOn U' S

end LocalModel

namespace Geometry

/-- **Level B ⇒ Level A, modulo A3/A4** (design §2 `Geometry.ofLocalModel`; the round-4 sorry-free
form with A3/A4 derived is `ofLocalModelOfBTZ`): every field of
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

The largeness clause is passed through as a hypothesis: since interface round 3 it is the
**diamond form with a regular tip** (`r ∈ reg`, `y₀ ≪_O r`, `reg ∩ I⁺_O(y₀) ∩ I⁻_O(r) ⊆ κ(A)`),
no longer the vacuous round-2 form (`Causality.BTZAxiomsCorr.exists_le_inter_Iminus_subset`).
What A3-past produces meets it: `diamond_clause_of_piece` (from
`Causality.CausallyConvexIn.Iplus_inter_Iminus_subset`, `chartedCausality_image_Iplus_inter_Iminus`).
A3 past at a BTZ point does not close through this lemma alone, for the model facts listed in
`LocalModel.GermExtPastBTZ` (round 4: an explicit hypothesis of `Geometry.ofLocalModelOfBTZ`). -/
theorem exists_eqOn_of_connected_sing_adherent {κ : OpenPartialHomeomorph M 𝔐.Y}
    {κ' : OpenPartialHomeomorph N 𝔐.Y} (hκ : κ ∈ 𝔐.G.maximalAtlas M)
    (hκ' : κ' ∈ 𝔐.G.maximalAtlas N) {ψ : M → N} {A : Set M} (hAo : IsOpen A)
    (hAc : IsPreconnected A) (hAne : A.Nonempty) (hA : A ⊆ κ.source)
    (hAreg : ∀ z ∈ A, κ z ∈ 𝔐.regY) {y₀ : 𝔐.Y} {α₀ : ℝ} (hα₀ : 0 ≤ α₀)
    (hsing : y₀ ∈ 𝔐.singY α₀)
    (hlarge : ∃ O : Opens 𝔐.Y, y₀ ∈ O ∧ ∃ r ∈ O, r ∈ 𝔐.regY ∧ 𝔐.causalityY.lt O y₀ r ∧
      𝔐.regY ∩ 𝔐.causalityY.Iplus O {y₀} ∩ 𝔐.causalityY.Iminus O {r} ⊆ κ '' A)
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

/-! ### A3 at regular points from Level B (interface round 3) -/

section ModelFree

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  {C : Causality M} {D : Causality N} {U : Opens M} {V : Opens N} {ψ : M → N} {g : N → M}

/-- **Step A of Sbierski Prop 3.7** (« `ψ(q) ≪ ψ(s) ≤ p′` »): for corresponding `p`, `q` and
`x ∈ U` with `x ≪ p`, `ψ x ≪ q`. -/
theorem IsCorrPair.lt_of_lt_of_corresponds (h : IsCorrPair C D U V ψ g)
    (hcv : C.CausallyConvexIn (U : Set M) ⊤) {p : M} {q : N} (hZ : p ∈ C.Zminus)
    (hPD : D.PushUp) (hclD : ∀ y, IsClosed (D.Jplus ⊤ {y}))
    (hc : Corresponds (U : Set M) ψ p q) {x : M} (hx : x ∈ U) (hxp : C.lt ⊤ x p) :
    D.lt ⊤ (ψ x) q := by
  obtain ⟨s, hxs, hsp⟩ := Causality.exists_lt_lt_of_mem_Zminus hZ hxp
  obtain ⟨u, hus, huU⟩ := mem_closure_iff_nhds.1 (mem_closure_of_corresponds hc) _
    (Causality.isOpen_Iplus.mem_nhds (show p ∈ C.Iplus ⊤ {s} by simpa using hsp))
  have hsU : s ∈ U := hcv.2 x hx u huU
    (Causality.mem_diamond.2 ⟨C.le_of_lt hxs, C.le_of_lt (by simpa using hus)⟩)
  exact h.lt_of_corresponds hPD (hclD _) hx hsU hxs (Causality.Jplus_mem_nhds_of_lt hsp) hc

/-- A point of `J⁺(T)` (`T ⊆ V`) chronologically below a point `q` corresponding to `p` lies in
`V` (causal convexity of `V`; `q ∈ closure V`). -/
theorem IsCorrPair.mem_of_lt_of_corresponds (h : IsCorrPair C D U V ψ g)
    (hcv : D.CausallyConvexIn (V : Set N) ⊤) {T : Set N} (hTV : T ⊆ V) {p : M} {q : N}
    (hc : Corresponds (U : Set M) ψ p q) {y : N} (hy : y ∈ D.Jplus ⊤ T) (hyq : D.lt ⊤ y q) :
    y ∈ V := by
  obtain ⟨τ, hτ, hτy⟩ := hy
  obtain ⟨x, hxU, -, hψx⟩ := hc univ univ_mem _
    (Causality.isOpen_Iplus.mem_nhds (show q ∈ D.Iplus ⊤ {y} by simpa using hyq))
  exact hcv.2 τ (hTV hτ) (ψ x) (h.mapsTo hxU)
    (Causality.mem_diamond.2 ⟨hτy, D.le_of_lt (by simpa using hψx)⟩)

/-- **Sbierski Prop 3.7, (i) ⇒ (ii), in the form Lemma 3.8 uses** (the strong causality of
`N` at `q`, « we can find a `q′ ∈ V′ ∩ I⁻(p′)` such that `I⁺(q′) ∩ I⁻(p′) ⊆ V′` »): for every
neighbourhood `V'` of `q` there is `x₀ ∈ U ∩ I⁻(p)` with `ψ(I⁺(x₀) ∩ I⁻(p) ∩ U) ⊆ V'`. Model-free;
`T ⊆ V` with `J⁺(T)` a neighbourhood of `q` is `lem:Sigma_separe` at `q` (`T = ψ S`). -/
theorem IsCorrPair.exists_lt_forall_mem (h : IsCorrPair C D U V ψ g)
    (hcvU : C.CausallyConvexIn (U : Set M) ⊤) (hcvV : D.CausallyConvexIn (V : Set N) ⊤)
    [T2Space N] (hGD : D.GloballyHyperbolic) (hTD : D.Tarentin) {p : M} {q : N}
    (hZp : p ∈ C.Zminus) (hZq : q ∈ D.Zminus) (hPC : C.PushUp) (hPD : D.PushUp)
    (hclC : ∀ x, IsClosed (C.Jplus ⊤ {x})) (hclD : ∀ y, IsClosed (D.Jplus ⊤ {y}))
    {T : Set N} (hTV : T ⊆ V) (hsep : D.Jplus ⊤ T ∈ 𝓝 q)
    (hc : Corresponds (U : Set M) ψ p q) {V' : Set N} (hV' : V' ∈ 𝓝 q) :
    ∃ x₀ ∈ U, C.lt ⊤ x₀ p ∧ ∀ y ∈ U, C.lt ⊤ x₀ y → C.lt ⊤ y p → ψ y ∈ V' := by
  obtain ⟨W, hW, hWsub, hWcv⟩ := hGD.stronglyCausal hTD q _ (inter_mem hV' hsep)
  obtain ⟨s', hs'I, hs'W⟩ := hZq W hW
  have hs'q : D.lt ⊤ s' q := by simpa using hs'I
  obtain ⟨s'', hs's'', hs''q⟩ := Causality.exists_lt_lt_of_mem_Zminus hZq hs'q
  have hs'J : s' ∈ D.Jplus ⊤ T := (hWsub hs'W).2
  have hs''J : s'' ∈ D.Jplus ⊤ T := by
    obtain ⟨τ, hτ, hτs⟩ := hs'J
    exact ⟨τ, hτ, D.le_trans hτs (D.le_of_lt hs's'')⟩
  have hs'V := h.mem_of_lt_of_corresponds hcvV hTV hc hs'J hs'q
  have hs''V := h.mem_of_lt_of_corresponds hcvV hTV hc hs''J hs''q
  have hx₀p : C.lt ⊤ (g s') p := h.symm.lt_of_corresponds hPC (hclC _) hs'V hs''V hs's''
    (Causality.Jplus_mem_nhds_of_lt hs''q) (h.corresponds_symm hc)
  have hx₀U : g s' ∈ U := h.mapsTo_inv hs'V
  refine ⟨g s', hx₀U, hx₀p, fun y hyU hx₀y hyp => ?_⟩
  have h1 : D.lt ⊤ s' (ψ y) := by
    have := (h.lt_iff _ hx₀U _ hyU).1 hx₀y
    rwa [h.rightInvOn hs'V] at this
  have h2 := h.lt_of_lt_of_corresponds hcvU hZp hPD hclD hc hyU hyp
  exact (hWsub (hWcv.2 s' hs'W q (mem_of_mem_nhds hW)
    (Causality.mem_diamond.2 ⟨D.le_of_lt h1, D.le_of_lt h2⟩))).1

/-- A point of `J⁺(S)` (`S ⊆ U`) chronologically below a point `p` of `closure U` lies in `U`
(causal convexity of `U`). -/
theorem mem_of_mem_Jplus_of_lt (hcv : C.CausallyConvexIn (U : Set M) ⊤) {S : Set M}
    (hSU : S ⊆ U) {p : M} (hp : p ∈ closure (U : Set M)) {x : M} (hx : x ∈ C.Jplus ⊤ S)
    (hxp : C.lt ⊤ x p) : x ∈ U := by
  obtain ⟨σ, hσ, hσx⟩ := hx
  obtain ⟨u, hux, huU⟩ := mem_closure_iff_nhds.1 hp _
    (Causality.isOpen_Iplus.mem_nhds (show p ∈ C.Iplus ⊤ {x} by simpa using hxp))
  exact hcv.2 σ (hSU hσ) u huU
    (Causality.mem_diamond.2 ⟨hσx, C.le_of_lt (by simpa using hux)⟩)

/-- **Footnote 21 of Sbierski** (« one cannot have one lying to the future and the other to the
past »): if `p ∈ ∂U` lies in the future of `S` (`J⁺(S)` a neighbourhood of `p`, `S ⊆ U` acausal)
and `q ∉ V` corresponds to `p`, then `q` is not in `J⁻(ψ S) ∖ J⁺(ψ S)`. -/
theorem IsCorrPair.mem_Jplus_of_corresponds (h : IsCorrPair C D U V ψ g)
    (hcv : C.CausallyConvexIn (U : Set M) ⊤) {p : M} {q : N} (hZ : p ∈ C.Zminus)
    (hPD : D.PushUp) (hclD : ∀ y, IsClosed (D.Jplus ⊤ {y}))
    (hc : Corresponds (U : Set M) ψ p q) (hqV : q ∉ V) (hcausM : C.IsCausal)
    (hcausN : D.IsCausal) {S : Set M} (hac : C.IsAcausal S) (hSU : S ⊆ U)
    (hsep : C.Jplus ⊤ S ∈ 𝓝 p) (hcov : q ∈ D.Jplus ⊤ (ψ '' S) ∪ D.Jminus ⊤ (ψ '' S)) :
    q ∈ D.Jplus ⊤ (ψ '' S) := by
  rcases hcov with h1 | ⟨_, ⟨σ₀, hσ₀, rfl⟩, hqσ⟩
  · exact h1
  exfalso
  obtain ⟨x, hxI, hxJ⟩ := hZ _ hsep
  have hxp : C.lt ⊤ x p := by simpa using hxI
  have hxU := mem_of_mem_Jplus_of_lt hcv hSU (mem_closure_of_corresponds hc) hxJ hxp
  have hxq := h.lt_of_lt_of_corresponds hcv hZ hPD hclD hc hxU hxp
  have hxσ₀ : C.le ⊤ x σ₀ :=
    (h.le_iff x hxU σ₀ (hSU hσ₀)).2 (D.le_trans (D.le_of_lt hxq) hqσ)
  obtain ⟨σ, hσ, hσx⟩ := hxJ
  have e : σ = σ₀ := hac σ hσ σ₀ hσ₀ (C.le_trans hσx hxσ₀)
  subst e
  have hx : x = σ := hcausM hxσ₀ hσx
  subst hx
  exact hqV (hcausN hqσ (D.le_of_lt hxq) ▸ h.mapsTo hxU)

end ModelFree

section GermPiece

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  {C : Causality M} {D : Causality N} {U : Opens M} {V : Opens N} {ψ : M → N} {g : N → M}
  {sing : ℝ → Set M}

theorem germ_isPreconnected_between (harc : C.CausallyArcConnected) {x y : M}
    (hxy : C.le ⊤ x y) :
    ∃ P : Set M, IsPreconnected P ∧ x ∈ P ∧ y ∈ P ∧ ∀ z ∈ P, C.le ⊤ x z ∧ C.le ⊤ z y := by
  obtain ⟨c, hc, hc0, hc1⟩ := ((harc ⊤ le_rfl x y).1).1 hxy
  refine ⟨c '' Icc 0 1, isPreconnected_Icc.image c (CurveOn.continuousOn C.isRelFamily_le hc),
    ⟨0, ⟨le_rfl, zero_le_one⟩, hc0⟩, ⟨1, ⟨zero_le_one, le_rfl⟩, hc1⟩, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  refine ⟨?_, ?_⟩
  · have := Causality.CausalCurveOn.le_of_le hc le_rfl ht.1 ht.2
    rwa [hc0] at this
  · have := Causality.CausalCurveOn.le_of_le hc ht.1 ht.2 le_rfl
    rwa [hc1] at this

theorem germ_mem_of_le_of_lt (hcvU : C.CausallyConvexIn (U : Set M) ⊤) {a x p : M}
    (haU : a ∈ U) (hax : C.le ⊤ a x) (hxp : C.lt ⊤ x p) (hp : p ∈ closure (U : Set M)) :
    x ∈ U := by
  obtain ⟨u, hu, huU⟩ := mem_closure_iff.1 hp _ (C.isOpen_Iplus (U := ⊤) (A := {x}))
    (Precausality.mem_Iplus_singleton.2 hxp)
  exact hcvU.2 a haU u huU
    (Causality.mem_diamond.2 ⟨hax, C.le_of_lt (Precausality.mem_Iplus_singleton.1 hu)⟩)

theorem germ_exists_open_subset_connectedComponentIn (hSC : C.StronglyCausal)
    (harc : C.CausallyArcConnected) (hcvU : C.CausallyConvexIn (U : Set M) ⊤) {p a : M}
    (hZp : p ∈ C.Zminus) (hpcl : p ∈ closure (U : Set M)) (haU : a ∈ U) (hap : C.lt ⊤ a p)
    {O' : Set M} (hO' : IsOpen O') (hpO' : p ∈ O') :
    ∃ x₃, x₃ ∈ O' ∧ C.lt ⊤ a x₃ ∧ C.lt ⊤ x₃ p ∧ ∃ O : Set M, IsOpen O ∧ p ∈ O ∧
      ∀ y ∈ O ∩ (U : Set M), y ∈ connectedComponentIn (O' ∩ (U : Set M)) x₃ := by
  obtain ⟨K, hK, hKO', hKcv⟩ := hSC p O' (hO'.mem_nhds hpO')
  obtain ⟨x₃, hx₃p, hx₃K, hx₃a⟩ := hZp _ (inter_mem (interior_mem_nhds.2 hK)
    (C.isOpen_Iplus.mem_nhds (show p ∈ C.Iplus ⊤ {a} by simpa using hap)))
  have hx₃p' : C.lt ⊤ x₃ p := by simpa using hx₃p
  have hax₃ : C.lt ⊤ a x₃ := by simpa using hx₃a
  have hx₃U : x₃ ∈ U := germ_mem_of_le_of_lt hcvU haU (C.le_of_lt hax₃) hx₃p' hpcl
  refine ⟨x₃, hKO' (interior_subset hx₃K), hax₃, hx₃p', interior K ∩ C.Iplus ⊤ {x₃},
    isOpen_interior.inter C.isOpen_Iplus,
    ⟨mem_interior_iff_mem_nhds.2 hK, by simpa using hx₃p'⟩, ?_⟩
  rintro y ⟨⟨hyK, hyI⟩, hyU⟩
  have hx₃y : C.le ⊤ x₃ y := C.le_of_lt (by simpa using hyI)
  obtain ⟨P, hP, hx₃P, hyP, hPb⟩ := germ_isPreconnected_between harc hx₃y
  refine hP.subset_connectedComponentIn (F := O' ∩ (U : Set M)) hx₃P (fun z hz => ⟨?_, ?_⟩) hyP
  · exact hKO' (hKcv.2 x₃ (interior_subset hx₃K) y (interior_subset hyK)
      (Causality.mem_diamond.2 (hPb z hz)))
  · exact hcvU.2 x₃ hx₃U y hyU (Causality.mem_diamond.2 (hPb z hz))

theorem germ_exists_piece [LocallyConnectedSpace M] (hcorr : IsCorrPair C D U V ψ g)
    (hcvU : C.CausallyConvexIn (U : Set M) ⊤) (hcvV : D.CausallyConvexIn (V : Set N) ⊤)
    [T2Space N] (hGD : D.GloballyHyperbolic) (hTD : D.Tarentin) (hSC : C.StronglyCausal)
    (harc : C.CausallyArcConnected) {p : M} {q : N}
    (hZp : p ∈ C.Zminus) (hZq : q ∈ D.Zminus) (hPC : C.PushUp) (hPD : D.PushUp)
    (hclC : ∀ x, IsClosed (C.Jplus ⊤ {x})) (hclD : ∀ y, IsClosed (D.Jplus ⊤ {y}))
    {T : Set N} (hTV : T ⊆ V) (hsep : D.Jplus ⊤ T ∈ 𝓝 q)
    (hc : Corresponds (U : Set M) ψ p q) {Q : Set M} (hQ : Q ∈ 𝓝 p) {Q' : Set N}
    (hQ' : Q' ∈ 𝓝 q) :
    ∃ a ∈ U, C.lt ⊤ a p ∧ ∃ A : Set M, IsOpen A ∧ IsPreconnected A ∧
      C.Iplus ⊤ {a} ∩ C.Iminus ⊤ {p} ⊆ A ∧
      A ⊆ (U : Set M) ∩ Q ∩ ψ ⁻¹' Q' ∩ C.Iminus ⊤ {p} := by
  have hpcl : p ∈ closure (U : Set M) := mem_closure_of_corresponds hc
  obtain ⟨x₀, hx₀U, hx₀p, hx₀⟩ := hcorr.exists_lt_forall_mem hcvU hcvV hGD hTD hZp hZq hPC hPD
    hclC hclD hTV hsep hc hQ'
  obtain ⟨K, hK, hKQ, hKcv⟩ := hSC p Q hQ
  obtain ⟨x₁, hx₁p, hx₁K, hx₁0⟩ := hZp _ (inter_mem (interior_mem_nhds.2 hK)
    (C.isOpen_Iplus.mem_nhds (show p ∈ C.Iplus ⊤ {x₀} by simpa using hx₀p)))
  have hx₁p' : C.lt ⊤ x₁ p := by simpa using hx₁p
  have hx₀x₁ : C.lt ⊤ x₀ x₁ := by simpa using hx₁0
  have hx₁U : x₁ ∈ U := germ_mem_of_le_of_lt hcvU hx₀U (C.le_of_lt hx₀x₁) hx₁p' hpcl
  obtain ⟨a, hx₁a, hap⟩ := Causality.exists_lt_lt_of_mem_Zminus hZp hx₁p'
  have haU : a ∈ U := germ_mem_of_le_of_lt hcvU hx₁U (C.le_of_lt hx₁a) hap hpcl
  set Ξ : Set M := C.Iplus ⊤ {x₁} ∩ C.Iminus ⊤ {p} with hΞ
  have hΞo : IsOpen Ξ := C.isOpen_Iplus.inter C.isOpen_Iminus
  have hΞsub : Ξ ⊆ (U : Set M) ∩ Q ∩ ψ ⁻¹' Q' ∩ C.Iminus ⊤ {p} := by
    rintro y ⟨hy1, hy2⟩
    have hx₁y : C.lt ⊤ x₁ y := by simpa using hy1
    have hyp : C.lt ⊤ y p := by simpa using hy2
    have hyU : y ∈ U := germ_mem_of_le_of_lt hcvU hx₁U (C.le_of_lt hx₁y) hyp hpcl
    refine ⟨⟨⟨hyU, hKQ (hKcv.2 x₁ (interior_subset hx₁K) p (mem_of_mem_nhds hK)
      (Causality.mem_diamond.2 ⟨C.le_of_lt hx₁y, C.le_of_lt hyp⟩))⟩, ?_⟩, hy2⟩
    exact hx₀ y hyU (hPC.lt_of_lt_of_le hx₀x₁ (C.le_of_lt hx₁y)) hyp
  have haΞ : a ∈ Ξ := ⟨by simpa using hx₁a, by simpa using hap⟩
  refine ⟨a, haU, hap, connectedComponentIn Ξ a, hΞo.connectedComponentIn,
    isPreconnected_connectedComponentIn, ?_, (connectedComponentIn_subset _ _).trans hΞsub⟩
  rintro y ⟨hy1, hy2⟩
  have hay : C.le ⊤ a y := C.le_of_lt (by simpa using hy1)
  have hyp : C.lt ⊤ y p := by simpa using hy2
  obtain ⟨P, hP, haP, hyP, hPb⟩ := germ_isPreconnected_between harc hay
  refine hP.subset_connectedComponentIn (F := Ξ) haP (fun z hz => ⟨?_, ?_⟩) hyP
  · simpa using hPC.lt_of_lt_of_le hx₁a (hPb z hz).1
  · simpa using hPC.lt_of_le_of_lt (hPb z hz).2 hyp

/-- **`germ_exists_piece` with the chronology `a ≪ p` read in any open `W ⊇ Q`** (round 4: the
type-agreement field `LocalModel.typeAgreement` reads the piece's diamond in the chart, where the
local relation `a ≪_W p` is needed). The chronal curve from `a` to `p` lies in the causally convex
neighbourhood `K ⊆ Q` of strong causality, hence in `W`. -/
theorem germ_exists_piece_lt [LocallyConnectedSpace M] (hcorr : IsCorrPair C D U V ψ g)
    (hcvU : C.CausallyConvexIn (U : Set M) ⊤) (hcvV : D.CausallyConvexIn (V : Set N) ⊤)
    [T2Space N] (hGD : D.GloballyHyperbolic) (hTD : D.Tarentin) (hSC : C.StronglyCausal)
    (harc : C.CausallyArcConnected) {p : M} {q : N}
    (hZp : p ∈ C.Zminus) (hZq : q ∈ D.Zminus) (hPC : C.PushUp) (hPD : D.PushUp)
    (hclC : ∀ x, IsClosed (C.Jplus ⊤ {x})) (hclD : ∀ y, IsClosed (D.Jplus ⊤ {y}))
    {T : Set N} (hTV : T ⊆ V) (hsep : D.Jplus ⊤ T ∈ 𝓝 q)
    (hc : Corresponds (U : Set M) ψ p q) {Q : Set M} (hQ : Q ∈ 𝓝 p) {Q' : Set N}
    (hQ' : Q' ∈ 𝓝 q) :
    ∃ a ∈ U, C.lt ⊤ a p ∧ (∀ W : Opens M, Q ⊆ W → C.lt W a p) ∧
      ∃ A : Set M, IsOpen A ∧ IsPreconnected A ∧
      C.Iplus ⊤ {a} ∩ C.Iminus ⊤ {p} ⊆ A ∧
      A ⊆ (U : Set M) ∩ Q ∩ ψ ⁻¹' Q' ∩ C.Iminus ⊤ {p} := by
  have hpcl : p ∈ closure (U : Set M) := mem_closure_of_corresponds hc
  obtain ⟨x₀, hx₀U, hx₀p, hx₀⟩ := hcorr.exists_lt_forall_mem hcvU hcvV hGD hTD hZp hZq hPC hPD
    hclC hclD hTV hsep hc hQ'
  obtain ⟨K, hK, hKQ, hKcv⟩ := hSC p Q hQ
  obtain ⟨x₁, hx₁p, hx₁K, hx₁0⟩ := hZp _ (inter_mem (interior_mem_nhds.2 hK)
    (C.isOpen_Iplus.mem_nhds (show p ∈ C.Iplus ⊤ {x₀} by simpa using hx₀p)))
  have hx₁p' : C.lt ⊤ x₁ p := by simpa using hx₁p
  have hx₀x₁ : C.lt ⊤ x₀ x₁ := by simpa using hx₁0
  have hx₁U : x₁ ∈ U := germ_mem_of_le_of_lt hcvU hx₀U (C.le_of_lt hx₀x₁) hx₁p' hpcl
  obtain ⟨a, hx₁a, hap⟩ := Causality.exists_lt_lt_of_mem_Zminus hZp hx₁p'
  have haU : a ∈ U := germ_mem_of_le_of_lt hcvU hx₁U (C.le_of_lt hx₁a) hap hpcl
  set Ξ : Set M := C.Iplus ⊤ {x₁} ∩ C.Iminus ⊤ {p} with hΞ
  have hΞo : IsOpen Ξ := C.isOpen_Iplus.inter C.isOpen_Iminus
  have hΞsub : Ξ ⊆ (U : Set M) ∩ Q ∩ ψ ⁻¹' Q' ∩ C.Iminus ⊤ {p} := by
    rintro y ⟨hy1, hy2⟩
    have hx₁y : C.lt ⊤ x₁ y := by simpa using hy1
    have hyp : C.lt ⊤ y p := by simpa using hy2
    have hyU : y ∈ U := germ_mem_of_le_of_lt hcvU hx₁U (C.le_of_lt hx₁y) hyp hpcl
    refine ⟨⟨⟨hyU, hKQ (hKcv.2 x₁ (interior_subset hx₁K) p (mem_of_mem_nhds hK)
      (Causality.mem_diamond.2 ⟨C.le_of_lt hx₁y, C.le_of_lt hyp⟩))⟩, ?_⟩, hy2⟩
    exact hx₀ y hyU (hPC.lt_of_lt_of_le hx₀x₁ (C.le_of_lt hx₁y)) hyp
  have haΞ : a ∈ Ξ := ⟨by simpa using hx₁a, by simpa using hap⟩
  have hpK : p ∈ K := mem_of_mem_nhds hK
  have haK : a ∈ K := hKcv.2 x₁ (interior_subset hx₁K) p hpK
    (Causality.mem_diamond.2 ⟨C.le_of_lt hx₁a, C.le_of_lt hap⟩)
  have hlt : ∀ W : Opens M, Q ⊆ W → C.lt W a p := by
    intro W hQW
    obtain ⟨γ, hγ, hγ0, hγ1⟩ := (harc ⊤ le_rfl a p).2.1 hap
    have hmem : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ W := fun t ht => by
      have h1 : C.le ⊤ (γ 0) (γ t) := hγ.causalCurveOn.le_of_le le_rfl ht.1 ht.2
      have h2 : C.le ⊤ (γ t) (γ 1) := hγ.causalCurveOn.le_of_le ht.1 ht.2 le_rfl
      rw [hγ0] at h1
      rw [hγ1] at h2
      exact hQW (hKQ (hKcv.2 a haK p hpK (Causality.mem_diamond.2 ⟨h1, h2⟩)))
    have hγW : C.ChronalCurveOn W γ 0 1 := CurveOn.restrict hγ le_rfl le_rfl le_top hmem
    exact (harc W le_top a p).2.2 ⟨γ, hγW, hγ0, hγ1⟩
  refine ⟨a, haU, hap, hlt, connectedComponentIn Ξ a, hΞo.connectedComponentIn,
    isPreconnected_connectedComponentIn, ?_, (connectedComponentIn_subset _ _).trans hΞsub⟩
  rintro y ⟨hy1, hy2⟩
  have hay : C.le ⊤ a y := C.le_of_lt (by simpa using hy1)
  have hyp : C.lt ⊤ y p := by simpa using hy2
  obtain ⟨P, hP, haP, hyP, hPb⟩ := germ_isPreconnected_between harc hay
  refine hP.subset_connectedComponentIn (F := Ξ) haP (fun z hz => ⟨?_, ?_⟩) hyP
  · simpa using hPC.lt_of_lt_of_le hx₁a (hPb z hz).1
  · simpa using hPC.lt_of_le_of_lt (hPb z hz).2 hyp

/-- **A massive line accumulates at each of its points from below and from above** (round 4):
for `p ∈ sing_α`, `α > 0`, every neighbourhood of `p` contains points of `sing_α` chronologically
below and above `p` (`SingularFlatAxiomsCorr.massive_line`: an inextensible chronal curve through
`p`, continuous at the parameter of `p`). -/
theorem exists_massive_near (h : C.SingularFlatAxiomsCorr sing) {α : ℝ} (hα : 0 < α) {p : M}
    (hp : p ∈ sing α) {W : Set M} (hW : W ∈ 𝓝 p) :
    (∃ b ∈ W, b ∈ sing α ∧ C.lt ⊤ b p) ∧ (∃ b ∈ W, b ∈ sing α ∧ C.lt ⊤ p b) := by
  obtain ⟨γ, hγ0, -, -, hch, hrange⟩ := h.massive_line α hα p hp
  have hc : C.ChronalCurveOn ⊤ γ (-1) 1 := hch (-1) 1
  have hcont : ContinuousAt γ 0 := (CurveOn.continuousOn C.isRelFamily_lt hc).continuousAt
    (Icc_mem_nhds (by norm_num) (by norm_num))
  have hmem : ∀ t, γ t ∈ sing α := fun t => by
    have : γ t ∈ range γ := mem_range_self t
    rw [hrange] at this
    exact connectedComponentIn_subset _ _ this
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ W := hcont.preimage_mem_nhds (by rwa [hγ0])
  constructor
  · obtain ⟨t, htW, ht⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
      (Ioo_mem_nhdsLT (show (-1 : ℝ) < 0 by norm_num))).exists
    refine ⟨γ t, htW, hmem t, ?_⟩
    have := hc.lt_of_lt ht.1.le ht.2 (by norm_num)
    rwa [hγ0] at this
  · obtain ⟨t, htW, ht⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
      (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num))).exists
    refine ⟨γ t, htW, hmem t, ?_⟩
    have := hc.lt_of_lt (by norm_num) ht.1 ht.2.le
    rwa [hγ0] at this

theorem germ_tendsto_of_corresponds (hcorr : IsCorrPair C D U V ψ g)
    (hcvU : C.CausallyConvexIn (U : Set M) ⊤) (hcvV : D.CausallyConvexIn (V : Set N) ⊤)
    [T2Space N] (hGD : D.GloballyHyperbolic) (hTD : D.Tarentin) {p : M} {q : N}
    (hZp : p ∈ C.Zminus) (hZq : q ∈ D.Zminus) (hPC : C.PushUp) (hPD : D.PushUp)
    (hclC : ∀ x, IsClosed (C.Jplus ⊤ {x})) (hclD : ∀ y, IsClosed (D.Jplus ⊤ {y}))
    {T : Set N} (hTV : T ⊆ V) (hsep : D.Jplus ⊤ T ∈ 𝓝 q)
    (hc : Corresponds (U : Set M) ψ p q) :
    Tendsto ψ (𝓝[(U : Set M) ∩ C.Iminus ⊤ {p}] p) (𝓝 q) := by
  intro V' hV'
  obtain ⟨x₀, -, hx₀p, hx₀⟩ := hcorr.exists_lt_forall_mem hcvU hcvV hGD hTD hZp hZq hPC hPD
    hclC hclD hTV hsep hc hV'
  rw [Filter.mem_map]
  filter_upwards [inter_mem_nhdsWithin ((U : Set M) ∩ C.Iminus ⊤ {p})
    (C.isOpen_Iplus.mem_nhds (show p ∈ C.Iplus ⊤ {x₀} by simpa using hx₀p))] with y hy
  exact hx₀ y hy.1.1 (by simpa using hy.2) (by simpa using hy.1.2)

end GermPiece

section ModelStep


theorem trans_mem_maximalAtlas_of_mem {H : Type*} [TopologicalSpace H] {G : StructureGroupoid H}
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X] {c : OpenPartialHomeomorph X H}
    (hc : c ∈ G.maximalAtlas X) {e : OpenPartialHomeomorph H H} (he : e ∈ G) :
    c.trans e ∈ G.maximalAtlas X := by
  intro e' he'
  obtain ⟨h1, h2⟩ := hc e' he'
  refine ⟨?_, ?_⟩
  · rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc]
    exact G.trans (G.symm he) h1
  · rw [← OpenPartialHomeomorph.trans_assoc]
    exact G.trans h2 he

theorem mem_connectedComponent_of_mem_closure {X Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Z] {f : X → Z} {A : Set X} {x : X} (hA : IsPreconnected A)
    (hf : ContinuousOn f A) (hfx : ContinuousWithinAt f A x) (hx : x ∈ closure A) :
    ∀ z ∈ A, f z ∈ connectedComponent (f x) := fun _ hz =>
  (hA.image f hf).closure.subset_connectedComponent (hfx.mem_closure_image hx)
    (subset_closure (mem_image_of_mem f hz))

variable {𝔐 : LocalModel.{u}} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace 𝔐.Y M] [ChartedSpace 𝔐.Y N] [HasGroupoid M 𝔐.G] [HasGroupoid N 𝔐.G]

theorem exists_regularChart_mem_maximalAtlas (x : M) (hx : chartAt 𝔐.Y x x ∈ 𝔐.regY) :
    ∃ κ ∈ 𝔐.G.maximalAtlas M, x ∈ κ.source ∧ ∀ w ∈ connectedComponent (κ x), w ∈ 𝔐.regY := by
  obtain ⟨e, he, hxe, hreg⟩ := 𝔐.regularChart _ hx
  exact ⟨(chartAt 𝔐.Y x).trans e,
    trans_mem_maximalAtlas_of_mem (𝔐.G.chart_mem_maximalAtlas x) he,
    ⟨mem_chart_source _ x, hxe⟩, fun w hw => hreg w hw⟩

theorem germ_ext_reg [T2Space N]
    {C' : Causality M} {D' : Causality N} (U : Opens M) {V : Opens N} {ψ : M → N} {g : N → M}
    (hψ : LiftPropOn 𝔐.G.IsLocalStructomorphWithinAt ψ U) (hinj : InjOn ψ U)
    (hcorr : IsCorrPair C' D' U V ψ g) (hcvU : C'.CausallyConvexIn (U : Set M) ⊤)
    (hcvV : D'.CausallyConvexIn (V : Set N) ⊤) (hGN : D'.GloballyHyperbolic) (hTN : D'.Tarentin)
    (hSC : C'.StronglyCausal) (harc : C'.CausallyArcConnected) {p : M} {q : N}
    (hZp : p ∈ C'.Zminus) (hZq : q ∈ D'.Zminus) (hPM : C'.PushUp) (hPN : D'.PushUp)
    (hclM : ∀ x, IsClosed (C'.Jplus ⊤ {x})) (hclN : ∀ y, IsClosed (D'.Jplus ⊤ {y}))
    {T : Set N} (hTV : T ⊆ V) (hsepN : D'.Jplus ⊤ T ∈ 𝓝 q) (hc : Corresponds (U : Set M) ψ p q)
    (hpreg : chartAt 𝔐.Y p p ∈ 𝔐.regY) (hqreg : chartAt 𝔐.Y q q ∈ 𝔐.regY) :
    ∃ (O : Opens M) (φ : M → N), p ∈ O ∧ LiftPropOn 𝔐.G.IsLocalStructomorphWithinAt φ O ∧
      φ p = q ∧ EqOn φ ψ (O ⊓ U : Opens M) := by
  haveI : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace 𝔐.Y M
  obtain ⟨κ, hκ, hpκ, hκreg⟩ := exists_regularChart_mem_maximalAtlas (𝔐 := 𝔐) p hpreg
  obtain ⟨κ', hκ', hqκ', hκ'reg⟩ := exists_regularChart_mem_maximalAtlas (𝔐 := 𝔐) q hqreg
  obtain ⟨a, haU, hap, A, hAo, hAc, hdiam, hAsub⟩ := germ_exists_piece hcorr hcvU hcvV hGN hTN hSC
    harc hZp hZq hPM hPN hclM hclN hTV hsepN hc (κ.open_source.mem_nhds hpκ)
    (κ'.open_source.mem_nhds hqκ')
  have hAU : A ⊆ U := fun z hz => (hAsub hz).1.1.1
  have hAκ : A ⊆ κ.source := fun z hz => (hAsub hz).1.1.2
  have hAψ : MapsTo ψ A κ'.source := fun z hz => (hAsub hz).1.2
  have hpcl : p ∈ closure A := by
    rw [mem_closure_iff_nhds]
    intro t ht
    obtain ⟨y, hyp, hyt, hya⟩ := hZp _ (inter_mem ht
      (C'.isOpen_Iplus.mem_nhds (show p ∈ C'.Iplus ⊤ {a} by simpa using hap)))
    exact ⟨y, hyt, hdiam ⟨hya, hyp⟩⟩
  have hAne : A.Nonempty := by
    obtain ⟨y, -, hy⟩ := mem_closure_iff_nhds.1 hpcl univ univ_mem
    exact ⟨y, hy⟩
  haveI hNe : (𝓝[A] p).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hpcl
  have hT : Tendsto ψ (𝓝[A] p) (𝓝 q) :=
    (germ_tendsto_of_corresponds hcorr hcvU hcvV hGN hTN hZp hZq hPM hPN hclM hclN hTV hsepN
      hc).mono_left (nhdsWithin_mono _ fun z hz => ⟨hAU hz, (hAsub hz).2⟩)
  have hψA : LiftPropOn 𝔐.G.IsLocalStructomorphWithinAt ψ A :=
    liftPropOn_mono_of_le U.isOpen hAo hψ hAU
  have hψc : ContinuousOn ψ A := fun y hy => (hψA y hy).continuousWithinAt
  have hcompκ : ∀ z ∈ A, κ z ∈ connectedComponent (κ p) :=
    mem_connectedComponent_of_mem_closure hAc (κ.continuousOn.mono hAκ)
      (κ.continuousAt hpκ).continuousWithinAt hpcl
  have hqcl : q ∈ closure (ψ '' A) :=
    mem_closure_of_tendsto hT (eventually_mem_nhdsWithin.mono fun z hz => mem_image_of_mem ψ hz)
  have hcompκ' : ∀ z ∈ A, κ' (ψ z) ∈ connectedComponent (κ' q) := fun z hz =>
    mem_connectedComponent_of_mem_closure (hAc.image ψ hψc)
      (κ'.continuousOn.mono (image_subset_iff.2 hAψ)) (κ'.continuousAt hqκ').continuousWithinAt
      hqcl _ (mem_image_of_mem ψ hz)
  have hreg : ∀ z ∈ A, ∀ w ∈ connectedComponent (κ z), w ∈ 𝔐.regY := fun z hz w hw =>
    hκreg w (by rw [connectedComponent_eq (hcompκ z hz)]; exact hw)
  have hreg' : ∀ z ∈ A, ∀ w ∈ connectedComponent (κ' (ψ z)), w ∈ 𝔐.regY := fun z hz w hw =>
    hκ'reg w (by rw [connectedComponent_eq (hcompκ' z hz)]; exact hw)
  obtain ⟨e, he, hsrc, heq⟩ := LocalModel.exists_eqOn_of_connected_reg hκ hκ' hAo hAc hAne hAκ
    hAψ hψA (hinj.mono hAU) hreg hreg'
  obtain ⟨z₀, hz₀⟩ := hAne
  have hκpe : κ p ∈ e.source := hsrc z₀ hz₀
    (by rw [← connectedComponent_eq (hcompκ z₀ hz₀)]; exact mem_connectedComponent)
  have hep : e (κ p) = κ' q := by
    have h1 : Tendsto (fun z => e (κ z)) (𝓝[A] p) (𝓝 (e (κ p))) :=
      ((e.continuousAt hκpe).comp (κ.continuousAt hpκ)).tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun z => e (κ z)) (𝓝[A] p) (𝓝 (κ' q)) :=
      ((κ'.continuousAt hqκ').tendsto.comp hT).congr'
        (eventually_nhdsWithin_of_forall fun z hz => heq z hz)
    exact tendsto_nhds_unique h1 h2
  obtain ⟨O₀, hO₀o, hO₀, hφ, hφeq⟩ := LocalModel.exists_extension_of_eqOn hκ hκ' he hAψ heq
  have hpO₀ : p ∈ O₀ := by
    rw [hO₀]
    refine ⟨hpκ, hκpe, ?_⟩
    show e (κ p) ∈ κ'.target
    rw [hep]; exact κ'.map_source hqκ'
  have hφp : (κ'.symm ∘ e ∘ κ) p = q := by
    simp only [comp_apply, hep, κ'.left_inv hqκ']
  obtain ⟨x₃, hx₃O₀, hax₃, hx₃p, O, hOo, hpO, hO⟩ := germ_exists_open_subset_connectedComponentIn
    hSC harc hcvU hZp (mem_closure_of_corresponds hc) haU hap hO₀o hpO₀
  have hx₃A : x₃ ∈ A := hdiam ⟨by simpa using hax₃, by simpa using hx₃p⟩
  set Ω := connectedComponentIn (O₀ ∩ (U : Set M)) x₃ with hΩdef
  have hΩo : IsOpen Ω := (hO₀o.inter U.isOpen).connectedComponentIn
  have hΩsub : Ω ⊆ O₀ ∩ U := connectedComponentIn_subset _ _
  have hx₃Ω : x₃ ∈ Ω := mem_connectedComponentIn ⟨hx₃O₀, hAU hx₃A⟩
  have hEq : EqOn (κ'.symm ∘ e ∘ κ) ψ Ω := eqOn_of_liftPropOn 𝔐.rigid hΩo
    isPreconnected_connectedComponentIn
    (liftPropOn_mono_of_le hO₀o hΩo hφ fun z hz => (hΩsub hz).1)
    (liftPropOn_mono_of_le U.isOpen hΩo hψ fun z hz => (hΩsub hz).2)
    (hΩo.inter hAo) inter_subset_left ⟨x₃, hx₃Ω, hx₃A⟩
    (fun z hz => hφeq ⟨(hΩsub hz.1).1, hz.2⟩)
  refine ⟨⟨O ∩ O₀, hOo.inter hO₀o⟩, κ'.symm ∘ e ∘ κ, ⟨hpO, hpO₀⟩,
    liftPropOn_mono_of_le hO₀o (hOo.inter hO₀o) hφ inter_subset_right, hφp, ?_⟩
  rintro y ⟨⟨hyO, -⟩, hyU⟩
  exact hEq (hO y ⟨hyO, hyU⟩)

/-- **A3's core at a non-BTZ boundary point, generic `Y`** (round 4). As `germ_ext_reg`, with the
regularity of `p`, `q` replaced by: `p` is not BTZ (`hp0`); the piece's diamond read in the
preferred chart at `p` (`hread`: the largeness clause of `LocalModel.typeAgreement`); and the
singular points accumulating at `p` from below (`hline`: for a massive `p`, its line). The piece
`A` is built in the preferred charts `κ` at `p`, `κ'` at `q` (`germ_exists_piece_lt`), and B2 is
chosen by `LocalModel.typeAgreement` on `κ(A)`: both regular ⇒ `germ_ext_reg`; both singular ⇒
`localUnique_sing` on the regular part of `A` (through a singular point `b ∈ A` of `p`'s line, and
`κ' q` in the component of `κ p`), extended to all of `A` by `dense_regY` and `T2Space Y`
(`Set.EqOn.of_subset_closure`), then the extension and the B1 rigidity step of `germ_ext_reg`. -/
theorem germ_ext_nonBTZ [T2Space N]
    {C' : Causality M} {D' : Causality N} (U : Opens M) {V : Opens N} {ψ : M → N} {g : N → M}
    (hψ : LiftPropOn 𝔐.G.IsLocalStructomorphWithinAt ψ U) (hinj : InjOn ψ U)
    (hcorr : IsCorrPair C' D' U V ψ g) (hcvU : C'.CausallyConvexIn (U : Set M) ⊤)
    (hcvV : D'.CausallyConvexIn (V : Set N) ⊤) (hGN : D'.GloballyHyperbolic) (hTN : D'.Tarentin)
    (hSC : C'.StronglyCausal) (harc : C'.CausallyArcConnected) {p : M} {q : N}
    (hZp : p ∈ C'.Zminus) (hZq : q ∈ D'.Zminus) (hPM : C'.PushUp) (hPN : D'.PushUp)
    (hclM : ∀ x, IsClosed (C'.Jplus ⊤ {x})) (hclN : ∀ y, IsClosed (D'.Jplus ⊤ {y}))
    {T : Set N} (hTV : T ⊆ V) (hsepN : D'.Jplus ⊤ T ∈ 𝓝 q) (hc : Corresponds (U : Set M) ψ p q)
    (hp0 : chartAt 𝔐.Y p p ∉ 𝔐.singY 0)
    (hread : ∀ (a : M) (A : Set M), C'.lt (chartSource (chartAt 𝔐.Y p)) a p →
      C'.Iplus (chartSource (chartAt 𝔐.Y p)) {a} ∩ C'.Iminus (chartSource (chartAt 𝔐.Y p)) {p} ⊆
        A →
      ∃ O : Opens 𝔐.Y, chartAt 𝔐.Y p p ∈ O ∧ ∃ r ∈ O,
        (𝔐.causalityY.lt O r (chartAt 𝔐.Y p p) ∧ 𝔐.causalityY.Iplus O {r} ∩
          𝔐.causalityY.Iminus O {chartAt 𝔐.Y p p} ⊆ chartAt 𝔐.Y p '' A) ∨
        (𝔐.causalityY.lt O (chartAt 𝔐.Y p p) r ∧ 𝔐.causalityY.Iplus O {chartAt 𝔐.Y p p} ∩
          𝔐.causalityY.Iminus O {r} ⊆ chartAt 𝔐.Y p '' A))
    (hline : chartAt 𝔐.Y p p ∉ 𝔐.regY → ∀ W ∈ 𝓝 p, ∃ b ∈ W, C'.lt ⊤ b p ∧
      chartAt 𝔐.Y p b ∉ 𝔐.regY) :
    ∃ (O : Opens M) (φ : M → N), p ∈ O ∧ LiftPropOn 𝔐.G.IsLocalStructomorphWithinAt φ O ∧
      φ p = q ∧ EqOn φ ψ (O ⊓ U : Opens M) := by
  haveI : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace 𝔐.Y M
  set κ := chartAt 𝔐.Y p with hκdef
  set κ' := chartAt 𝔐.Y q with hκ'def
  have hκ : κ ∈ 𝔐.G.maximalAtlas M := 𝔐.G.chart_mem_maximalAtlas p
  have hκ' : κ' ∈ 𝔐.G.maximalAtlas N := 𝔐.G.chart_mem_maximalAtlas q
  have hpκ : p ∈ κ.source := mem_chart_source _ p
  have hqκ' : q ∈ κ'.source := mem_chart_source _ q
  obtain ⟨a, haU, hap, hapW, A, hAo, hAc, hdiam, hAsub⟩ := germ_exists_piece_lt hcorr hcvU hcvV
    hGN hTN hSC harc hZp hZq hPM hPN hclM hclN hTV hsepN hc (κ.open_source.mem_nhds hpκ)
    (κ'.open_source.mem_nhds hqκ')
  have hAU : A ⊆ U := fun z hz => (hAsub hz).1.1.1
  have hAκ : A ⊆ κ.source := fun z hz => (hAsub hz).1.1.2
  have hAψ : MapsTo ψ A κ'.source := fun z hz => (hAsub hz).1.2
  have hpcl : p ∈ closure A := by
    rw [mem_closure_iff_nhds]
    intro t ht
    obtain ⟨y, hyp, hyt, hya⟩ := hZp _ (inter_mem ht
      (C'.isOpen_Iplus.mem_nhds (show p ∈ C'.Iplus ⊤ {a} by simpa using hap)))
    exact ⟨y, hyt, hdiam ⟨hya, hyp⟩⟩
  have hAne : A.Nonempty := by
    obtain ⟨y, -, hy⟩ := mem_closure_iff_nhds.1 hpcl univ univ_mem
    exact ⟨y, hy⟩
  haveI hNe : (𝓝[A] p).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hpcl
  have hT : Tendsto ψ (𝓝[A] p) (𝓝 q) :=
    (germ_tendsto_of_corresponds hcorr hcvU hcvV hGN hTN hZp hZq hPM hPN hclM hclN hTV hsepN
      hc).mono_left (nhdsWithin_mono _ fun z hz => ⟨hAU hz, (hAsub hz).2⟩)
  have hψA : LiftPropOn 𝔐.G.IsLocalStructomorphWithinAt ψ A :=
    liftPropOn_mono_of_le U.isOpen hAo hψ hAU
  have hψc : ContinuousOn ψ A := fun y hy => (hψA y hy).continuousWithinAt
  have hcompκ : ∀ z ∈ A, κ z ∈ connectedComponent (κ p) :=
    mem_connectedComponent_of_mem_closure hAc (κ.continuousOn.mono hAκ)
      (κ.continuousAt hpκ).continuousWithinAt hpcl
  have hqcl : q ∈ closure (ψ '' A) :=
    mem_closure_of_tendsto hT (eventually_mem_nhdsWithin.mono fun z hz => mem_image_of_mem ψ hz)
  have hcompκ' : ∀ z ∈ A, κ' (ψ z) ∈ connectedComponent (κ' q) := fun z hz =>
    mem_connectedComponent_of_mem_closure (hAc.image ψ hψc)
      (κ'.continuousOn.mono (image_subset_iff.2 hAψ)) (κ'.continuousAt hqκ').continuousWithinAt
      hqcl _ (mem_image_of_mem ψ hz)
  -- **type agreement**, read on `Y` (round 4 (3)), for `f = κ' ∘ ψ ∘ κ⁻¹` on `κ(A)`
  have hG := isLocalStructomorphWithinAt_localInvariantProp 𝔐.G
  set B := κ '' A with hBdef
  have hBo : IsOpen B := κ.isOpen_image_of_subset_source hAo hAκ
  have hBc : IsConnected B := ⟨hAne.image _, hAc.image _ (κ.continuousOn.mono hAκ)⟩
  set f : 𝔐.Y → 𝔐.Y := κ' ∘ ψ ∘ κ.symm with hfdef
  have hfA : ∀ z ∈ A, f (κ z) = κ' (ψ z) := fun z hz => by
    simp only [f, comp_apply, κ.left_inv (hAκ hz)]
  have hloc : ∀ y ∈ B, 𝔐.G.IsLocalStructomorphWithinAt f B y := by
    rintro _ ⟨z, hz, rfl⟩
    have hP := hG.liftPropOn_indep_chart hκ hκ' hψA
      (y := κ z) ⟨κ.map_source (hAκ hz), by
        simp only [mem_preimage, κ.left_inv (hAκ hz)]; exact ⟨hz, hAψ hz⟩⟩
    intro hy
    obtain ⟨e, he, hef, hex⟩ := hP (by simp only [mem_preimage, κ.left_inv (hAκ hz)]; exact hz)
    refine ⟨e, he, fun y hy => hef ⟨?_, hy.2⟩, hex⟩
    obtain ⟨w, hw, rfl⟩ := hy.1
    simp only [mem_preimage, κ.left_inv (hAκ hw)]; exact hw
  have hinjf : InjOn f B := by
    rintro _ ⟨a', ha', rfl⟩ _ ⟨b', hb', rfl⟩ hab
    rw [hfA a' ha', hfA b' hb'] at hab
    rw [hinj (hAU ha') (hAU hb') (κ'.injOn (hAψ ha') (hAψ hb') hab)]
  have hclus : MapClusterPt (κ' q) (𝓝[B] (κ p)) f :=
    LocalModel.mapClusterPt_chart (𝔐 := 𝔐) hAκ hpκ hqκ' hT.mapClusterPt
  have hlocdiam : C'.Iplus (chartSource κ) {a} ∩ C'.Iminus (chartSource κ) {p} ⊆ A :=
    fun z hz => hdiam ⟨C'.Iplus_mono_opens le_top hz.1, C'.Iminus_mono_opens le_top hz.2⟩
  obtain ⟨hty, hcc⟩ := 𝔐.typeAgreement B hBo hBc (κ p) hp0 (hread a A (hapW _ subset_rfl) hlocdiam)
    (κ' q) f hloc hinjf hclus
  by_cases hpreg : κ p ∈ 𝔐.regY
  · -- both regular: `germ_ext_reg`
    have hqreg : κ' q ∈ 𝔐.regY := fun α hα hq => hpreg α hα ((hty α hα).2 hq)
    exact germ_ext_reg U hψ hinj hcorr hcvU hcvV hGN hTN hSC harc hZp hZq hPM hPN hclM hclN hTV
      hsepN hc hpreg hqreg
  -- both singular: B2 at a singular point on the regular part of `A`
  have hα : ∃ α : ℝ, 0 ≤ α ∧ κ p ∈ 𝔐.singY α := 𝔐.exists_mem_singY_of_not_mem_regY hpreg
  have hqcc : κ' q ∈ connectedComponent (κ p) := hcc hα
  obtain ⟨b, ⟨hbκ, hba⟩, hbp, hbreg⟩ := hline hpreg _ (inter_mem (κ.open_source.mem_nhds hpκ)
    (C'.isOpen_Iplus.mem_nhds (show p ∈ C'.Iplus ⊤ {a} by simpa using hap)))
  have hbA : b ∈ A := hdiam ⟨hba, by simpa using hbp⟩
  obtain ⟨α₁, hα₁, hb1⟩ := 𝔐.exists_mem_singY_of_not_mem_regY hbreg
  have hccb : connectedComponent (κ b) = connectedComponent (κ p) :=
    (connectedComponent_eq (hcompκ b hbA)).symm
  have hccq : connectedComponent (κ' q) = connectedComponent (κ p) :=
    (connectedComponent_eq hqcc).symm
  have hcomp : ∀ z ∈ A ∩ κ ⁻¹' 𝔐.regY, κ' (ψ z) ∈ connectedComponent (κ b) := fun z hz => by
    rw [hccb, ← hccq]; exact hcompκ' z hz.1
  have hAro : IsOpen (A ∩ κ ⁻¹' 𝔐.regY) := by
    have h := hAo.inter (κ.isOpen_inter_preimage 𝔐.isOpen_regY)
    convert h using 1
    ext z
    exact ⟨fun hz => ⟨hz.1, hAκ hz.1, hz.2⟩, fun hz => ⟨hz.1, hz.2.2⟩⟩
  obtain ⟨e, he, hsrc, heqr⟩ := LocalModel.exists_eqOn_of_connected_sing hκ hκ' hAo hAc hAκ hbA
    hα₁ hb1 (hAψ.mono_left inter_subset_left)
    (liftPropOn_mono_of_le hAo hAro hψA inter_subset_left)
    ((hinj.mono hAU).mono inter_subset_left) hcomp
  have hκpe : κ p ∈ e.source := hsrc (by rw [hccb]; exact mem_connectedComponent)
  have hAe : MapsTo κ A e.source := fun z hz => hsrc (by rw [hccb]; exact hcompκ z hz)
  -- the regular part of `A` is dense in `A` (`dense_regY`), so the agreement extends to `A`
  have hdense : A ⊆ closure (A ∩ κ ⁻¹' 𝔐.regY) := by
    intro z hz
    rw [mem_closure_iff_nhds]
    intro t ht
    have hto : IsOpen (interior t ∩ A) := isOpen_interior.inter hAo
    have hne : (κ '' (interior t ∩ A)).Nonempty :=
      ⟨κ z, z, ⟨mem_interior_iff_mem_nhds.2 ht, hz⟩, rfl⟩
    obtain ⟨_, ⟨w, hw, rfl⟩, hwreg⟩ := 𝔐.dense_regY.inter_open_nonempty _
      (κ.isOpen_image_of_subset_source hto fun x hx => hAκ hx.2) hne
    exact ⟨w, interior_subset hw.1, hw.2, hwreg⟩
  have heq : ∀ z ∈ A, κ' (ψ z) = e (κ z) := by
    have h := Set.EqOn.of_subset_closure (f := fun z => κ' (ψ z)) (g := fun z => e (κ z))
      (s := A ∩ κ ⁻¹' 𝔐.regY) (t := A) (fun z hz => heqr z hz)
      (κ'.continuousOn.comp hψc hAψ) (e.continuousOn.comp (κ.continuousOn.mono hAκ) hAe)
      inter_subset_left hdense
    exact fun z hz => h hz
  -- the extension and the rigidity step, as in `germ_ext_reg`
  have hep : e (κ p) = κ' q := by
    have h1 : Tendsto (fun z => e (κ z)) (𝓝[A] p) (𝓝 (e (κ p))) :=
      ((e.continuousAt hκpe).comp (κ.continuousAt hpκ)).tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun z => e (κ z)) (𝓝[A] p) (𝓝 (κ' q)) :=
      ((κ'.continuousAt hqκ').tendsto.comp hT).congr'
        (eventually_nhdsWithin_of_forall fun z hz => heq z hz)
    exact tendsto_nhds_unique h1 h2
  obtain ⟨O₀, hO₀o, hO₀, hφ, hφeq⟩ := LocalModel.exists_extension_of_eqOn hκ hκ' he hAψ heq
  have hpO₀ : p ∈ O₀ := by
    rw [hO₀]
    refine ⟨hpκ, hκpe, ?_⟩
    show e (κ p) ∈ κ'.target
    rw [hep]; exact κ'.map_source hqκ'
  have hφp : (κ'.symm ∘ e ∘ κ) p = q := by
    simp only [comp_apply, hep, κ'.left_inv hqκ']
  obtain ⟨x₃, hx₃O₀, hax₃, hx₃p, O, hOo, hpO, hO⟩ := germ_exists_open_subset_connectedComponentIn
    hSC harc hcvU hZp (mem_closure_of_corresponds hc) haU hap hO₀o hpO₀
  have hx₃A : x₃ ∈ A := hdiam ⟨by simpa using hax₃, by simpa using hx₃p⟩
  set Ω := connectedComponentIn (O₀ ∩ (U : Set M)) x₃ with hΩdef
  have hΩo : IsOpen Ω := (hO₀o.inter U.isOpen).connectedComponentIn
  have hΩsub : Ω ⊆ O₀ ∩ U := connectedComponentIn_subset _ _
  have hx₃Ω : x₃ ∈ Ω := mem_connectedComponentIn ⟨hx₃O₀, hAU hx₃A⟩
  have hEq : EqOn (κ'.symm ∘ e ∘ κ) ψ Ω := eqOn_of_liftPropOn 𝔐.rigid hΩo
    isPreconnected_connectedComponentIn
    (liftPropOn_mono_of_le hO₀o hΩo hφ fun z hz => (hΩsub hz).1)
    (liftPropOn_mono_of_le U.isOpen hΩo hψ fun z hz => (hΩsub hz).2)
    (hΩo.inter hAo) inter_subset_left ⟨x₃, hx₃Ω, hx₃A⟩
    (fun z hz => hφeq ⟨(hΩsub hz.1).1, hz.2⟩)
  refine ⟨⟨O ∩ O₀, hOo.inter hO₀o⟩, κ'.symm ∘ e ∘ κ, ⟨hpO, hpO₀⟩,
    liftPropOn_mono_of_le hO₀o (hOo.inter hO₀o) hφ inter_subset_right, hφp, ?_⟩
  rintro y ⟨⟨hyO, -⟩, hyU⟩
  exact hEq (hO y ⟨hyO, hyU⟩)

end ModelStep

section Assembly


variable {𝔐 : LocalModel.{u}} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace 𝔐.Y M] [ChartedSpace 𝔐.Y N] [HasGroupoid M 𝔐.G] [HasGroupoid N 𝔐.G]

theorem isCorrPair_of_cghd [T2Space M] [T2Space N] [Nonempty M]
    (hCM : (chartedCausality 𝔐.causalityY M).CausallyArcConnected)
    (hCN : (chartedCausality 𝔐.causalityY N).CausallyArcConnected)
    (hextM : (chartedCausality 𝔐.causalityY M).CurvesExtend)
    (hextN : (chartedCausality 𝔐.causalityY N).CurvesExtend)
    (U : Opens M) {ψ : M → N} {S : Set M} (hψ : LiftPropOn 𝔐.G.IsLocalStructomorphWithinAt ψ U)
    (hinj : InjOn ψ U) (hGM : (chartedCausality 𝔐.causalityY M).GloballyHyperbolic)
    (hGN : (chartedCausality 𝔐.causalityY N).GloballyHyperbolic)
    (hGU : (chartedCausality 𝔐.causalityY M).GloballyHyperbolicOn U)
    (hGV : (chartedCausality 𝔐.causalityY N).GloballyHyperbolicOn
      ((isEMorphismOn_of_liftPropOn 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y hψ).imageOpens U
        le_rfl))
    (hSU : S ⊆ U) (hS : (chartedCausality 𝔐.causalityY M).IsCauchySurface S)
    (hSU' : (chartedCausality 𝔐.causalityY M).IsCauchySurfaceOn U S)
    (hψS : (chartedCausality 𝔐.causalityY N).IsCauchySurface (ψ '' S))
    (hψSV : (chartedCausality 𝔐.causalityY N).IsCauchySurfaceOn
      ((isEMorphismOn_of_liftPropOn 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y hψ).imageOpens U
        le_rfl) (ψ '' S)) :
    (chartedCausality 𝔐.causalityY M).CausallyConvexIn (U : Set M) ⊤ ∧
      (chartedCausality 𝔐.causalityY N).CausallyConvexIn
        ((isEMorphismOn_of_liftPropOn 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y hψ).imageOpens U
          le_rfl : Set N) ⊤ ∧
      IsCorrPair (chartedCausality 𝔐.causalityY M) (chartedCausality 𝔐.causalityY N) U
        ((isEMorphismOn_of_liftPropOn 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y hψ).imageOpens U
          le_rfl) ψ (invFunOn ψ U) := by
  set C := chartedCausality 𝔐.causalityY M
  set D := chartedCausality 𝔐.causalityY N
  have hE := isEMorphismOn_of_liftPropOn 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y hψ
  set V := hE.imageOpens U le_rfl with hVdef
  have hE' : IsEMorphismOn D C V (invFunOn ψ U) :=
    isEMorphismOn_of_liftPropOn 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y (W := V)
      (liftPropOn_invFunOn U.isOpen hψ hinj)
  have hcvU : C.CausallyConvexIn (U : Set M) ⊤ :=
    IsCauchyInclusion.causallyConvexIn ⟨le_top, hGU, hGM, S, hSU, hSU', hS⟩ hCM
      (Causality.curvesExtendOn_top.2 hextM)
  have hcvV : D.CausallyConvexIn (V : Set N) ⊤ :=
    IsCauchyInclusion.causallyConvexIn ⟨le_top, hGV, hGN, ψ '' S, image_mono hSU, hψSV, hψS⟩ hCN
      (Causality.curvesExtendOn_top.2 hextN)
  have hl := hinj.leftInvOn_invFunOn
  have hmaps : MapsTo ψ U V := fun z hz => ⟨z, hz, rfl⟩
  refine ⟨hcvU, hcvV,
    { mapsTo := hmaps
      mapsTo_inv := fun y hy => invFunOn_mem hy
      leftInvOn := hl
      rightInvOn := fun y hy => invFunOn_eq hy
      continuousOn := hE.continuousOn
      continuousOn_inv := hE'.continuousOn
      le_iff := fun x hx y hy => ⟨fun hxy => ?_, fun hxy => ?_⟩
      lt_iff := fun x hx y hy => ⟨fun hxy => ?_, fun hxy => ?_⟩ }⟩
  · exact D.le_mono le_top (hE.map_le U V le_rfl hmaps
      (Causality.le_of_causallyConvexIn_of_le hCM hcvU subset_rfl le_top hx hy hxy))
  · have hV' := Causality.le_of_causallyConvexIn_of_le hCN hcvV subset_rfl le_top (hmaps hx)
      (hmaps hy) hxy
    have := hE'.map_le V ⊤ le_rfl (fun _ _ => trivial) hV'
    rwa [hl hx, hl hy] at this
  · exact D.lt_mono le_top (hE.map_lt U V le_rfl hmaps
      (Causality.lt_of_causallyConvexIn hCM hcvU hx hy hxy))
  · have hV' := Causality.lt_of_causallyConvexIn hCN hcvV (hmaps hx) (hmaps hy) hxy
    have := hE'.map_lt V ⊤ le_rfl (fun _ _ => trivial) hV'
    rwa [hl hx, hl hy] at this

variable [T2Space M] [ConnectedSpace M] [SecondCountableTopology M]
  [T2Space N] [ConnectedSpace N] [SecondCountableTopology N]

theorem germ_future_reg (U : Opens M) (ψ : M → N) (S : Set M)
    (hψ : LiftPropOn 𝔐.G.IsLocalStructomorphWithinAt ψ U)
    (hinj : InjOn ψ U) (hGM : (chartedCausality 𝔐.causalityY M).GloballyHyperbolic)
    (hGN : (chartedCausality 𝔐.causalityY N).GloballyHyperbolic)
    (hGU : (chartedCausality 𝔐.causalityY M).GloballyHyperbolicOn U)
    (hGV : (chartedCausality 𝔐.causalityY N).GloballyHyperbolicOn
      ((isEMorphismOn_of_liftPropOn 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y hψ).imageOpens U
        le_rfl))
    (hSU : S ⊆ U) (hS : (chartedCausality 𝔐.causalityY M).IsCauchySurface S)
    (hSU' : (chartedCausality 𝔐.causalityY M).IsCauchySurfaceOn U S)
    (hψS : (chartedCausality 𝔐.causalityY N).IsCauchySurface (ψ '' S))
    (hψSV : (chartedCausality 𝔐.causalityY N).IsCauchySurfaceOn
      ((isEMorphismOn_of_liftPropOn 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y hψ).imageOpens U
        le_rfl) (ψ '' S))
    (p : M) (q : N) (hp : p ∈ frontier (U : Set M))
    (hpS : p ∈ (chartedCausality 𝔐.causalityY M).Jplus ⊤ S)
    (hcl : MapClusterPt q (𝓝[(U : Set M)] p) ψ)
    (hpreg : chartAt 𝔐.Y p p ∈ 𝔐.regY) (hqreg : chartAt 𝔐.Y q q ∈ 𝔐.regY) :
    ∃ (O : Opens M) (φ : M → N), p ∈ O ∧ LiftPropOn 𝔐.G.IsLocalStructomorphWithinAt φ O ∧
      φ p = q ∧ EqOn φ ψ (O ⊓ U : Opens M) := by
  set C := chartedCausality 𝔐.causalityY M
  set D := chartedCausality 𝔐.causalityY N
  have hAxM : C.SingularFlatAxiomsCorr (chartedSing 𝔐.singY M) := 𝔐.singularFlatAxioms
  have hAxN : D.SingularFlatAxiomsCorr (chartedSing 𝔐.singY N) := 𝔐.singularFlatAxioms
  have hextM : C.CurvesExtend := 𝔐.curvesExtend hGM
  have hextN : D.CurvesExtend := 𝔐.curvesExtend hGN
  haveI : Nonempty M := ⟨p⟩
  obtain ⟨hcvU, hcvV, hcorr⟩ := isCorrPair_of_cghd hAxM.causallyArcConnected
    hAxN.causallyArcConnected hextM hextN U hψ hinj hGM hGN hGU hGV hSU hS hSU' hψS hψSV
  set V := (isEMorphismOn_of_liftPropOn 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y hψ).imageOpens U
    le_rfl with hVdef
  have hc : Corresponds (U : Set M) ψ p q := corresponds_iff_mapClusterPt.2 hcl
  have hZp : p ∈ C.Zminus := (hAxM.mem_Zminus_iff p).2 (hpreg 0 le_rfl)
  have hZq : q ∈ D.Zminus := (hAxN.mem_Zminus_iff q).2 (hqreg 0 le_rfl)
  have hclM := hGM.isClosed_Jplus_singleton hAxM.tarentin
  have hclN := hGN.isClosed_Jplus_singleton hAxN.tarentin
  have hpU : p ∉ (U : Set M) := by rw [U.isOpen.frontier_eq] at hp; exact hp.2
  have hsepM : C.Jplus ⊤ S ∈ 𝓝 p :=
    Causality.Jplus_mem_nhds_of_isCauchySurface hGM.1 hAxM.causallyArcConnected hextM hS
      (fun x => (hAxM.K_densite_sing x).2) (𝔐.isCompact_Jminus_inter_Jplus hGM S hS)
      ⟨hpS, fun h => hpU (hSU h)⟩
  have hqfr := hcorr.mem_frontier_of_corresponds hp hc
  have hqV : q ∉ (V : Set N) := by rw [V.isOpen.frontier_eq] at hqfr; exact hqfr.2
  have hqS := hcorr.mem_Jplus_of_corresponds hcvU hZp hAxN.pushUp hclN hc hqV hGM.1 hGN.1
    (hS.isAcausal hAxM.causallyArcConnected hextM) hSU hsepM
    (Causality.mem_Jplus_union_Jminus_of_isCauchySurface hextN hψS q)
  have hsepN : D.Jplus ⊤ (ψ '' S) ∈ 𝓝 q :=
    Causality.Jplus_mem_nhds_of_isCauchySurface hGN.1 hAxN.causallyArcConnected hextN hψS
      (fun x => (hAxN.K_densite_sing x).2) (𝔐.isCompact_Jminus_inter_Jplus hGN _ hψS)
      ⟨hqS, fun h => hqV ((hcorr.mapsTo.mono_left hSU).image_subset h)⟩
  exact germ_ext_reg U hψ hinj hcorr hcvU hcvV hGN hAxN.tarentin
    (hGM.stronglyCausal hAxM.tarentin) hAxM.causallyArcConnected hZp hZq hAxM.pushUp
    hAxN.pushUp hclM hclN ((hcorr.mapsTo.mono_left hSU).image_subset) hsepN hc hpreg hqreg

theorem germ_past_reg (U : Opens M) (ψ : M → N) (S : Set M)
    (hψ : LiftPropOn 𝔐.G.IsLocalStructomorphWithinAt ψ U)
    (hinj : InjOn ψ U) (hGM : (chartedCausality 𝔐.causalityY M).GloballyHyperbolic)
    (hGN : (chartedCausality 𝔐.causalityY N).GloballyHyperbolic)
    (hGU : (chartedCausality 𝔐.causalityY M).GloballyHyperbolicOn U)
    (hGV : (chartedCausality 𝔐.causalityY N).GloballyHyperbolicOn
      ((isEMorphismOn_of_liftPropOn 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y hψ).imageOpens U
        le_rfl))
    (hSU : S ⊆ U) (hS : (chartedCausality 𝔐.causalityY M).IsCauchySurface S)
    (hSU' : (chartedCausality 𝔐.causalityY M).IsCauchySurfaceOn U S)
    (hψS : (chartedCausality 𝔐.causalityY N).IsCauchySurface (ψ '' S))
    (hψSV : (chartedCausality 𝔐.causalityY N).IsCauchySurfaceOn
      ((isEMorphismOn_of_liftPropOn 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y hψ).imageOpens U
        le_rfl) (ψ '' S))
    (p : M) (q : N) (hp : p ∈ frontier (U : Set M))
    (hpS : p ∈ (chartedCausality 𝔐.causalityY M).Jminus ⊤ S)
    (hcl : MapClusterPt q (𝓝[(U : Set M)] p) ψ)
    (hpreg : chartAt 𝔐.Y p p ∈ 𝔐.regY) (hqreg : chartAt 𝔐.Y q q ∈ 𝔐.regY) :
    ∃ (O : Opens M) (φ : M → N), p ∈ O ∧ LiftPropOn 𝔐.G.IsLocalStructomorphWithinAt φ O ∧
      φ p = q ∧ EqOn φ ψ (O ⊓ U : Opens M) := by
  set C := chartedCausality 𝔐.causalityY M
  set D := chartedCausality 𝔐.causalityY N
  have hAxM : C.SingularFlatAxiomsCorr (chartedSing 𝔐.singY M) := 𝔐.singularFlatAxioms
  have hAxN : D.SingularFlatAxiomsCorr (chartedSing 𝔐.singY N) := 𝔐.singularFlatAxioms
  have hextM : C.CurvesExtend := 𝔐.curvesExtend hGM
  have hextN : D.CurvesExtend := 𝔐.curvesExtend hGN
  haveI : Nonempty M := ⟨p⟩
  obtain ⟨hcvU, hcvV, hcorr⟩ := isCorrPair_of_cghd hAxM.causallyArcConnected
    hAxN.causallyArcConnected hextM hextN U hψ hinj hGM hGN hGU hGV hSU hS hSU' hψS hψSV
  set V := (isEMorphismOn_of_liftPropOn 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y hψ).imageOpens U
    le_rfl with hVdef
  have hc : Corresponds (U : Set M) ψ p q := corresponds_iff_mapClusterPt.2 hcl
  have hcorr' := hcorr.dual
  have hcvU' : C.dual.CausallyConvexIn (U : Set M) ⊤ := Causality.dual_causallyConvexIn.2 hcvU
  have hcvV' : D.dual.CausallyConvexIn (V : Set N) ⊤ := Causality.dual_causallyConvexIn.2 hcvV
  have hZM : ∀ x, x ∈ C.dual.Zminus := fun x => hAxM.mem_Zplus x
  have hZN : ∀ y, y ∈ D.dual.Zminus := fun y => hAxN.mem_Zplus y
  have hPM : C.dual.PushUp := Causality.dual_pushUp.2 hAxM.pushUp
  have hPN : D.dual.PushUp := Causality.dual_pushUp.2 hAxN.pushUp
  have hclM : ∀ x, IsClosed (C.dual.Jplus ⊤ {x}) := hGM.isClosed_Jminus_singleton hAxM.tarentin
  have hclN : ∀ y, IsClosed (D.dual.Jplus ⊤ {y}) := hGN.isClosed_Jminus_singleton hAxN.tarentin
  have hpU : p ∉ (U : Set M) := by rw [U.isOpen.frontier_eq] at hp; exact hp.2
  have hsepM : C.dual.Jplus ⊤ S ∈ 𝓝 p :=
    Causality.Jminus_mem_nhds_of_isCauchySurface hGM.1 hAxM.causallyArcConnected hextM hS
      (fun x => (hAxM.K_densite_sing x).1) (𝔐.isCompact_Jplus_inter_Jminus hGM S hS)
      ⟨hpS, fun h => hpU (hSU h)⟩
  have hqfr := hcorr.mem_frontier_of_corresponds hp hc
  have hqV : q ∉ (V : Set N) := by rw [V.isOpen.frontier_eq] at hqfr; exact hqfr.2
  have hqS : q ∈ D.dual.Jplus ⊤ (ψ '' S) := hcorr'.mem_Jplus_of_corresponds hcvU' (hZM p) hPN
    hclN hc hqV (Causality.dual_isCausal.2 hGM.1) (Causality.dual_isCausal.2 hGN.1)
    (Causality.dual_isAcausal.2 (hS.isAcausal hAxM.causallyArcConnected hextM)) hSU hsepM
    (Causality.mem_Jplus_union_Jminus_of_isCauchySurface hextN hψS q).symm
  have hsepN : D.dual.Jplus ⊤ (ψ '' S) ∈ 𝓝 q :=
    Causality.Jminus_mem_nhds_of_isCauchySurface hGN.1 hAxN.causallyArcConnected hextN hψS
      (fun x => (hAxN.K_densite_sing x).1) (𝔐.isCompact_Jplus_inter_Jminus hGN _ hψS)
      ⟨hqS, fun h => hqV ((hcorr.mapsTo.mono_left hSU).image_subset h)⟩
  exact germ_ext_reg U hψ hinj hcorr' hcvU' hcvV'
    (Causality.dual_globallyHyperbolic.2 hGN) (Causality.dual_tarentin.2 hAxN.tarentin)
    (Causality.dual_stronglyCausal.2 (hGM.stronglyCausal hAxM.tarentin))
    (Causality.dual_causallyArcConnectedOn.2 hAxM.causallyArcConnected) (hZM p) (hZN q) hPM hPN
    hclM hclN ((hcorr.mapsTo.mono_left hSU).image_subset) hsepN hc hpreg hqreg

end Assembly

/-! ### A4: a union with a sliced open set, and the assembly (model-free; from `Flat/CBGSlice`) -/

section SliceGeneral

variable {M : Type*} [TopologicalSpace M] {C : Causality M}

/-- **A union keeps the Cauchy surface.** If `S` is a Cauchy surface of `A`, acausal in `M` (`M`
causal, Hausdorff), and `N` is an open set with a Cauchy surface `Γ ⊆ A`, then `S` is a Cauchy
surface of `A ⊔ N`: an inextensible curve of `A ⊔ N` through `N` meets `Γ` by its component in
`N`, hence enters `A`, and its component in `A` meets `S`; uniqueness by acausality (Sbierski,
proof of Thm 3.6, last paragraph). -/
theorem isCauchySurfaceOn_sup_of_slice [T2Space M] (hcaus : C.IsCausal) {S Γ : Set M}
    (hac : C.IsAcausal S) {A N : Opens M} (hA : C.IsCauchySurfaceOn A S)
    (hN : C.IsCauchySurfaceOn N Γ) (hΓ : Γ ⊆ A) : C.IsCauchySurfaceOn (A ⊔ N) S := by
  have hanti : ∀ ⦃x y : M⦄, C.le (A ⊔ N) x y → C.le (A ⊔ N) y x → x = y :=
    fun x y h h' => hcaus (C.le_mono le_top h) (C.le_mono le_top h')
  intro I c hc
  have hmeetA : ∀ t ∈ I, c t ∈ A → (c '' I ∩ S).Nonempty := by
    intro t ht htA
    obtain ⟨_, ⟨⟨τ, hτ, rfl⟩, hτS⟩, -⟩ := hA _ c
      (Causality.inextensible_ordConnectedComponent_of_le hanti le_sup_left hc ht htA)
    exact ⟨c τ, ⟨τ, (ordConnectedComponent_subset hτ).1, rfl⟩, hτS⟩
  obtain ⟨t₀, ht₀⟩ := hc.1.nonempty
  have hex : (c '' I ∩ S).Nonempty := by
    rcases Opens.mem_sup.1 (hc.1.mem ht₀) with h | h
    · exact hmeetA t₀ ht₀ h
    · obtain ⟨_, ⟨⟨τ, hτ, rfl⟩, hτΓ⟩, -⟩ := hN _ c
        (Causality.inextensible_ordConnectedComponent_of_le hanti le_sup_right hc ht₀ h)
      exact hmeetA τ (ordConnectedComponent_subset hτ).1 (hΓ hτΓ)
  obtain ⟨x, hx⟩ := hex
  refine ⟨x, hx, ?_⟩
  rintro y ⟨⟨s, hs, rfl⟩, hyS⟩
  obtain ⟨⟨s', hs', rfl⟩, hxS⟩ := hx
  rcases le_total s s' with h | h
  · exact hac _ hyS _ hxS (C.le_mono le_top (hc.1.le_of_le hs hs' h))
  · exact (hac _ hxS _ hyS (C.le_mono le_top (hc.1.le_of_le hs' hs h))).symm

/-- **The assembly of A4 from a sliced neighbourhood.** In a causal (GH) Hausdorff spacetime,
causally arc-connected with curves extending, with Cauchy surface `S ⊆ U` of `U`: an open `N ∋ p`,
`p ∉ U`, `N ⊆ O`, with a Cauchy surface `Γ ⊆ U`, gives `U' = U ⊔ N`, strictly larger than `U`,
inside `U ∪ O`, globally hyperbolic, with `S` as a Cauchy surface. -/
theorem extend_of_cauchy_nbhd [T2Space M] (hGH : C.GloballyHyperbolic)
    (harc : C.CausallyArcConnected) (hext : C.CurvesExtend) {U : Opens M} {S : Set M}
    (hSU : S ⊆ U) (hS : C.IsCauchySurface S) (hSU' : C.IsCauchySurfaceOn U S)
    {N : Opens M} {Γ : Set M} (hN : C.IsCauchySurfaceOn N Γ) (hΓ : Γ ⊆ U) {p : M} (hpN : p ∈ N)
    (hpU : p ∉ U) {O : Set M} (hNO : (N : Set M) ⊆ O) :
    ∃ U' : Opens M, U < U' ∧ (U' : Set M) ⊆ U ∪ O ∧ C.GloballyHyperbolicOn U' ∧
      C.IsCauchySurfaceOn U' S := by
  have hac : C.IsAcausal S := hS.isAcausal harc hext
  have hSUN : C.IsCauchySurfaceOn (U ⊔ N) S := isCauchySurfaceOn_sup_of_slice hGH.1 hac hSU' hN hΓ
  have hconv : C.CausallyConvexIn ((U ⊔ N : Opens M) : Set M) ⊤ :=
    Causality.causallyConvexIn_of_isCauchySurfaceOn hGH.1 harc hext le_top
      (fun x hx => (le_sup_left : U ≤ U ⊔ N) (hSU hx)) hSUN hS
  refine ⟨U ⊔ N, lt_of_le_of_ne le_sup_left fun h => hpU ?_, fun x hx => ?_,
    Causality.GloballyHyperbolicOn.of_causallyConvexIn harc hGH hconv, hSUN⟩
  · have : p ∈ U ⊔ N := Opens.mem_sup.2 (Or.inr hpN)
    rwa [← h] at this
  · rcases Opens.mem_sup.1 hx with h | h
    · exact Or.inl h
    · exact Or.inr (hNO h)

variable {U : Opens M} {S : Set M} {p : M}

/-- **`I⁻(p) ∩ J⁺(S) ⊆ U`** for `p ∈ closure U`, `U` causally convex, `S ⊆ U`: `I⁺(z)` is an open
neighbourhood of `p`, so it meets `U` at some `u`, and `z` lies in the diamond `J(σ, u)`. -/
theorem mem_of_lt_of_mem_closure (hconv : C.CausallyConvexIn (U : Set M) ⊤) (hSU : S ⊆ U)
    (hpU : p ∈ closure (U : Set M)) {z : M} (hz : z ∈ C.Jplus ⊤ S) (hzp : C.lt ⊤ z p) : z ∈ U := by
  obtain ⟨σ, hσS, hσz⟩ := hz
  obtain ⟨u, hu, huU⟩ := mem_closure_iff.1 hpU _ (C.isOpen_Iplus (U := ⊤) (A := {z}))
    (Precausality.mem_Iplus_singleton.2 hzp)
  exact hconv.2 σ (hSU hσS) u huU
    (Causality.mem_diamond.2 ⟨hσz, C.le_of_lt (Precausality.mem_Iplus_singleton.1 hu)⟩)

/-- **Past form**: `I⁺(p) ∩ J⁻(S) ⊆ U`. -/
theorem mem_of_gt_of_mem_closure (hconv : C.CausallyConvexIn (U : Set M) ⊤) (hSU : S ⊆ U)
    (hpU : p ∈ closure (U : Set M)) {z : M} (hz : z ∈ C.Jminus ⊤ S) (hpz : C.lt ⊤ p z) :
    z ∈ U := by
  obtain ⟨σ, hσS, hzσ⟩ := hz
  obtain ⟨u, hu, huU⟩ := mem_closure_iff.1 hpU _ (C.isOpen_Iminus (U := ⊤) (A := {z}))
    (Precausality.mem_Iminus_singleton.2 hpz)
  exact hconv.2 u huU σ (hSU hσS)
    (Causality.mem_diamond.2 ⟨C.le_of_lt (Precausality.mem_Iminus_singleton.1 hu), hzσ⟩)

/-- **The corner condition puts the punctured causal past cone into `U`** (near `p`, inside the
interior of `J⁺(S)`): a point `z ≤ p`, `z ≠ p`, not in `U` is not on `∂U` (corner condition), so it
is outside `closure U`; a point `z' ≪ z` close to it (`Z⁻`) is still outside `closure U` and in
`J⁺(S)`, and `z' ≪ p` (push-up), so `z' ∈ U` (`mem_of_lt_of_mem_closure`): a contradiction. -/
theorem mem_of_le_of_mem_interior_Jplus (hconv : C.CausallyConvexIn (U : Set M) ⊤) (hSU : S ⊆ U)
    (hpU : p ∈ closure (U : Set M)) (hpush : C.PushUp) (hZ : ∀ z : M, z ∈ C.Zminus)
    (hcorner : C.Jminus ⊤ {p} ∩ frontier (U : Set M) ∩ C.Jplus ⊤ S = {p}) {z : M}
    (hz : z ∈ interior (C.Jplus ⊤ S)) (hzp : C.le ⊤ z p) (hne : z ≠ p) : z ∈ U := by
  by_contra hzU
  by_cases hzc : z ∈ closure (U : Set M)
  · have hzf : z ∈ frontier (U : Set M) := ⟨hzc, by rwa [U.isOpen.interior_eq]⟩
    have : z ∈ C.Jminus ⊤ {p} ∩ frontier (U : Set M) ∩ C.Jplus ⊤ S :=
      ⟨⟨Precausality.mem_Jminus_singleton.2 hzp, hzf⟩, interior_subset hz⟩
    rw [hcorner] at this
    exact hne this
  · have hQ : (closure (U : Set M))ᶜ ∩ interior (C.Jplus ⊤ S) ∈ 𝓝 z :=
      (isClosed_closure.isOpen_compl.inter isOpen_interior).mem_nhds ⟨hzc, hz⟩
    obtain ⟨z', hz'I, hz'c, hz'J⟩ := hZ z _ hQ
    have hz'z : C.lt ⊤ z' z := Precausality.mem_Iminus_singleton.1 hz'I
    have hz'p : C.lt ⊤ z' p := by
      have h1 : p ∈ C.Jplus ⊤ (C.Iplus ⊤ {z'}) :=
        ⟨z, Precausality.mem_Iplus_singleton.2 hz'z, hzp⟩
      exact Precausality.mem_Iplus_singleton.1 ((hpush ⊤ z').1.1 h1)
    exact hz'c (subset_closure
      (mem_of_lt_of_mem_closure hconv hSU hpU (interior_subset hz'J) hz'p))

/-- **Past form**: the punctured causal future cone of `p` near `p`, inside the interior of
`J⁻(S)`, lies in `U` under `J⁺(p) ∩ ∂U ∩ J⁻(S) = {p}` (`Z⁺`, push-up). -/
theorem mem_of_ge_of_mem_interior_Jminus (hconv : C.CausallyConvexIn (U : Set M) ⊤) (hSU : S ⊆ U)
    (hpU : p ∈ closure (U : Set M)) (hpush : C.PushUp) (hZ : ∀ z : M, z ∈ C.Zplus)
    (hcorner : C.Jplus ⊤ {p} ∩ frontier (U : Set M) ∩ C.Jminus ⊤ S = {p}) {z : M}
    (hz : z ∈ interior (C.Jminus ⊤ S)) (hpz : C.le ⊤ p z) (hne : z ≠ p) : z ∈ U := by
  by_contra hzU
  by_cases hzc : z ∈ closure (U : Set M)
  · have hzf : z ∈ frontier (U : Set M) := ⟨hzc, by rwa [U.isOpen.interior_eq]⟩
    have : z ∈ C.Jplus ⊤ {p} ∩ frontier (U : Set M) ∩ C.Jminus ⊤ S :=
      ⟨⟨Precausality.mem_Jplus_singleton.2 hpz, hzf⟩, interior_subset hz⟩
    rw [hcorner] at this
    exact hne this
  · have hQ : (closure (U : Set M))ᶜ ∩ interior (C.Jminus ⊤ S) ∈ 𝓝 z :=
      (isClosed_closure.isOpen_compl.inter isOpen_interior).mem_nhds ⟨hzc, hz⟩
    obtain ⟨z', hz'I, hz'c, hz'J⟩ := hZ z _ hQ
    have hzz' : C.lt ⊤ z z' := Precausality.mem_Iplus_singleton.1 hz'I
    have hpz' : C.lt ⊤ p z' := by
      have h1 : p ∈ C.Jminus ⊤ (C.Iminus ⊤ {z'}) :=
        ⟨z, Precausality.mem_Iminus_singleton.2 hzz', hpz⟩
      exact Precausality.mem_Iminus_singleton.1 ((hpush ⊤ z').1.2 h1)
    exact hz'c (subset_closure
      (mem_of_gt_of_mem_closure hconv hSU hpU (interior_subset hz'J) hpz'))

/-- **The cone lemma with `Z⁻` asked at the point only** (`mem_of_le_of_mem_interior_Jplus`
asks `∀ z, z ∈ Z⁻`, which fails on a BTZ line; the generic A4 needs it at the points of the
slice only). -/
theorem mem_of_le_of_mem_interior_Jplus_of_mem_Zminus (hconv : C.CausallyConvexIn (U : Set M) ⊤)
    (hSU : S ⊆ U) (hpU : p ∈ closure (U : Set M)) (hpush : C.PushUp)
    (hcorner : C.Jminus ⊤ {p} ∩ frontier (U : Set M) ∩ C.Jplus ⊤ S = {p}) {z : M}
    (hZz : z ∈ C.Zminus) (hz : z ∈ interior (C.Jplus ⊤ S)) (hzp : C.le ⊤ z p) (hne : z ≠ p) :
    z ∈ U := by
  by_contra hzU
  by_cases hzc : z ∈ closure (U : Set M)
  · have hzf : z ∈ frontier (U : Set M) := ⟨hzc, by rwa [U.isOpen.interior_eq]⟩
    have : z ∈ C.Jminus ⊤ {p} ∩ frontier (U : Set M) ∩ C.Jplus ⊤ S :=
      ⟨⟨Precausality.mem_Jminus_singleton.2 hzp, hzf⟩, interior_subset hz⟩
    rw [hcorner] at this
    exact hne this
  · have hQ : (closure (U : Set M))ᶜ ∩ interior (C.Jplus ⊤ S) ∈ 𝓝 z :=
      (isClosed_closure.isOpen_compl.inter isOpen_interior).mem_nhds ⟨hzc, hz⟩
    obtain ⟨z', hz'I, hz'c, hz'J⟩ := hZz _ hQ
    have hz'z : C.lt ⊤ z' z := Precausality.mem_Iminus_singleton.1 hz'I
    have hz'p : C.lt ⊤ z' p := by
      have h1 : p ∈ C.Jplus ⊤ (C.Iplus ⊤ {z'}) :=
        ⟨z, Precausality.mem_Iplus_singleton.2 hz'z, hzp⟩
      exact Precausality.mem_Iplus_singleton.1 ((hpush ⊤ z').1.1 h1)
    exact hz'c (subset_closure
      (mem_of_lt_of_mem_closure hconv hSU hpU (interior_subset hz'J) hz'p))

end SliceGeneral

/-! ### A4 from a cone-slice form of B4 (interface round 3) -/

namespace LocalModel

variable (𝔐 : LocalModel.{u})

/-! The cone-slice B4 (`ConeSliceFuture`/`ConeSlicePast` of round 3) are the `LocalModel` fields
`coneSliceFuture`/`coneSlicePast` since round 4 (gx-agreed 2026-11-02), statements verbatim. -/

variable {𝔐} {M : Type u} [TopologicalSpace M] [ChartedSpace 𝔐.Y M] [HasGroupoid M 𝔐.G]

/-- A preferred chart is an abstract morphism on its source (`Flat/CBGSlice`'s
`flatChart_isEMorphismOn`, for any local model). -/
theorem chart_isEMorphismOn (x : M) :
    IsEMorphismOn (chartedCausality 𝔐.causalityY M) 𝔐.causalityY (chartSource (chartAt 𝔐.Y x))
      (chartAt 𝔐.Y x) := by
  set e := chartAt 𝔐.Y x
  have hiso : ChartIso (chartedCausality 𝔐.causalityY M) 𝔐.causalityY e :=
    chartedCausality_chartIso 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y x
  have himg : ∀ V : Opens M, V ≤ chartSource e → ((chartImage e V : Opens _) : Set _) = e '' V :=
    fun V hV => coe_chartImage_of_le hV
  have hsub : ∀ (V : Opens M) (U : Opens 𝔐.Y), V ≤ chartSource e → MapsTo e V U →
      chartImage e V ≤ U := fun V U hV hmaps p hp => by
    rw [← SetLike.mem_coe, himg V hV] at hp
    obtain ⟨z, hz, rfl⟩ := hp
    exact hmaps hz
  exact
  { continuousOn := e.continuousOn
    isOpen_image := fun V hV => by rw [← himg V hV]; exact (chartImage e V).isOpen
    map_le := fun V U hV hmaps y z hyz =>
      𝔐.causalityY.le_mono (hsub V U hV hmaps)
        (((hiso V hV y ((chartedCausality 𝔐.causalityY M).le_mem_left hyz) z
          ((chartedCausality 𝔐.causalityY M).le_mem_right hyz)).1).1 hyz)
    map_lt := fun V U hV hmaps y z hyz =>
      𝔐.causalityY.lt_mono (hsub V U hV hmaps)
        (((hiso V hV y ((chartedCausality 𝔐.causalityY M).lt_mem_left hyz) z
          ((chartedCausality 𝔐.causalityY M).lt_mem_right hyz)).2).1 hyz)
    locally := fun z hz => ⟨chartSource e, le_rfl, hz, e.injOn, fun V' hV' U hU y hy w hw => by
      have hU' : chartImage e V' = U := SetLike.coe_injective (by rw [himg V' hV', hU])
      rw [← hU']; exact hiso V' hV' y hy w hw⟩ }

/-- `sing_α` read in any chart of the atlas equals `sing_α` read in the preferred chart at the
point (B3 `sing_mem` on the transition). -/
theorem chartAt_mem_singY_iff {x w : M} (hw : w ∈ (chartAt 𝔐.Y x).source) {α : ℝ} (hα : 0 ≤ α) :
    chartAt 𝔐.Y x w ∈ 𝔐.singY α ↔ chartAt 𝔐.Y w w ∈ 𝔐.singY α := by
  have he : (chartAt 𝔐.Y x).symm.trans (chartAt 𝔐.Y w) ∈ 𝔐.G :=
    𝔐.G.compatible (chart_mem_atlas _ x) (chart_mem_atlas _ w)
  have hmem : chartAt 𝔐.Y x w ∈ ((chartAt 𝔐.Y x).symm.trans (chartAt 𝔐.Y w)).source := by
    simp only [OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage,
      OpenPartialHomeomorph.symm_source]
    exact ⟨(chartAt _ x).map_source hw, by rw [(chartAt _ x).left_inv hw]; exact mem_chart_source _ w⟩
  have h := 𝔐.sing_mem _ he _ hmem α hα
  have h2 : ((chartAt 𝔐.Y x).symm.trans (chartAt 𝔐.Y w)) (chartAt 𝔐.Y x w) = chartAt 𝔐.Y w w := by
    simp [(chartAt 𝔐.Y x).left_inv hw]
  rwa [h2] at h


/-- **The assembly of A4 through a chart** (generic `Flat/CBGSlice` §3 end): an open `N ∋ κ p` of
`Y` inside `κ(W₀)` with a Cauchy surface `Γ ⊆ N` inside `κ(W₀ ∩ U)` gives, read back in `M`, an
open `N_M ∋ p` with Cauchy surface `Γ_M ⊆ U` (`IsEMorphismOn.isCauchySurfaceOn_image_iff` along
`chart_isEMorphismOn`), and `extend_of_cauchy_nbhd` concludes. -/
theorem slice_assemble [T2Space M] {x p : M} {U O W₀ : Opens M} {S : Set M}
    (hGH : (chartedCausality 𝔐.causalityY M).GloballyHyperbolic)
    (harc : (chartedCausality 𝔐.causalityY M).CausallyArcConnected)
    (hext : (chartedCausality 𝔐.causalityY M).CurvesExtend) (hSU : S ⊆ U)
    (hS : (chartedCausality 𝔐.causalityY M).IsCauchySurface S)
    (hSU' : (chartedCausality 𝔐.causalityY M).IsCauchySurfaceOn U S) (hpU : p ∉ U)
    (hpκ : p ∈ (chartAt 𝔐.Y x).source) (hW₀κ : W₀ ≤ chartSource (chartAt 𝔐.Y x))
    {N : Opens 𝔐.Y} {Γ : Set 𝔐.Y} (hNO : N ≤ chartImage (chartAt 𝔐.Y x) W₀)
    (hyN : chartAt 𝔐.Y x p ∈ N) (hΓN : Γ ⊆ N)
    (hΓG : Γ ⊆ chartAt 𝔐.Y x '' ((W₀ : Set M) ∩ U))
    (hNΓ : 𝔐.causalityY.IsCauchySurfaceOn N Γ) (hW₀O : (W₀ : Set M) ⊆ O) :
    ∃ U' : Opens M, U < U' ∧ (U' : Set M) ⊆ U ∪ O ∧
      (chartedCausality 𝔐.causalityY M).GloballyHyperbolicOn U' ∧
      (chartedCausality 𝔐.causalityY M).IsCauchySurfaceOn U' S := by
  set κ := chartAt 𝔐.Y x with hκ
  set C := chartedCausality 𝔐.causalityY M
  let NM : Opens M := ⟨κ.source ∩ κ ⁻¹' N, κ.isOpen_inter_preimage N.isOpen⟩
  set ΓM : Set M := κ.source ∩ κ ⁻¹' Γ with hΓMdef
  have hNM : (N : Set 𝔐.Y) = κ '' NM := by
    ext y
    constructor
    · intro hy
      obtain ⟨w, hws, -, rfl, -⟩ := exists_of_mem_chartImage (hNO hy)
      exact ⟨w, ⟨hws, hy⟩, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact hw.2
  have hΓM : κ '' ΓM = Γ := by
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw.2
    · intro hy
      obtain ⟨w, hws, -, rfl, -⟩ := exists_of_mem_chartImage (hNO (hΓN hy))
      exact ⟨w, ⟨hws, hy⟩, rfl⟩
  have hΓMN : ΓM ⊆ NM := fun w hw => ⟨hw.1, hΓN hw.2⟩
  have hNMcy : C.IsCauchySurfaceOn NM ΓM := by
    refine ((chart_isEMorphismOn x).isCauchySurfaceOn_image_iff κ.injOn
      (show NM ≤ chartSource κ from fun _ hw => hw.1) hNM hΓMN).2 ?_
    rw [hΓM]
    exact hNΓ
  have hΓMU : ΓM ⊆ U := by
    intro w hw
    obtain ⟨w', hw', hw'e⟩ := hΓG hw.2
    rw [← κ.injOn (hW₀κ hw'.1) hw.1 hw'e]
    exact hw'.2
  have hpNM : p ∈ NM := ⟨hpκ, hyN⟩
  have hNMO : (NM : Set M) ⊆ O := by
    intro w hw
    obtain ⟨w', hw's, hw'W, hw'e, -⟩ := exists_of_mem_chartImage (hNO hw.2)
    rw [← κ.injOn hw's hw.1 hw'e]
    exact hW₀O hw'W
  exact extend_of_cauchy_nbhd hGH harc hext hSU hS hSU' hNMcy hΓMU hpNM hpU hNMO

variable [T2Space M] [ConnectedSpace M] [SecondCountableTopology M]

/-- **A4 future from the cone-slice B4 (`coneSliceFuture`), off the BTZ locus** (Sbierski Thm 3.6, geometric half; the
construction of `Flat/CBGSlice`, generic): the corner condition puts the punctured past cone of `p`
near `p` into `U` (`mem_of_le_of_mem_interior_Jplus_of_mem_Zminus`), so the cone-slice `K` read in
the chart at `p` lies in the chart image of `U`, an open set, which therefore contains a Cauchy
surface `Γ` of an open `N ∋ p`; then `extend_of_cauchy_nbhd`. Uses neither R1 for `U` nor the
global hyperbolicity of `U`. -/
theorem slice_future_of_cone (U : Opens M) (S : Set M)
    (hGH : (chartedCausality 𝔐.causalityY M).GloballyHyperbolic) (hSU : S ⊆ U)
    (hS : (chartedCausality 𝔐.causalityY M).IsCauchySurface S)
    (hSU' : (chartedCausality 𝔐.causalityY M).IsCauchySurfaceOn U S)
    (p : M) (hp : p ∈ frontier (U : Set M))
    (hpS : p ∈ (chartedCausality 𝔐.causalityY M).Jplus ⊤ S)
    (hcorner : (chartedCausality 𝔐.causalityY M).Jminus ⊤ {p} ∩ frontier (U : Set M) ∩
      (chartedCausality 𝔐.causalityY M).Jplus ⊤ S = {p})
    (O : Opens M) (hpO : p ∈ O) (hp0 : chartAt 𝔐.Y p p ∉ 𝔐.singY 0) :
    ∃ U' : Opens M, U < U' ∧ (U' : Set M) ⊆ U ∪ O ∧
      (chartedCausality 𝔐.causalityY M).GloballyHyperbolicOn U' ∧
      (chartedCausality 𝔐.causalityY M).IsCauchySurfaceOn U' S := by
  set C := chartedCausality 𝔐.causalityY M
  have hAx : C.SingularFlatAxiomsCorr (chartedSing 𝔐.singY M) := 𝔐.singularFlatAxioms
  have harc := hAx.causallyArcConnected
  have hext : C.CurvesExtend := 𝔐.curvesExtend hGH
  have hconv : C.CausallyConvexIn (U : Set M) ⊤ :=
    Causality.causallyConvexIn_of_isCauchySurfaceOn hGH.1 harc hext le_top hSU hSU' hS
  have hpU : p ∉ U := fun h => hp.2 (by rwa [U.isOpen.interior_eq])
  have hpcl : p ∈ closure (U : Set M) := hp.1
  have hJ : C.Jplus ⊤ S ∈ 𝓝 p :=
    Causality.Jplus_mem_nhds_of_isCauchySurface hGH.1 harc hext hS
      (fun x => (hAx.K_densite_sing x).2) (𝔐.isCompact_Jminus_inter_Jplus hGH S hS)
      ⟨hpS, fun h => hpU (hSU h)⟩
  set κ := chartAt 𝔐.Y p with hκ
  have hpκ : p ∈ κ.source := mem_chart_source _ p
  let W₀ : Opens M := ⟨interior (C.Jplus ⊤ S) ∩ O ∩ κ.source,
    (isOpen_interior.inter O.isOpen).inter κ.open_source⟩
  have hpW₀ : p ∈ W₀ := ⟨⟨mem_interior_iff_mem_nhds.2 hJ, hpO⟩, hpκ⟩
  have hW₀κ : W₀ ≤ chartSource κ := fun z hz => hz.2
  have hiso := chartedCausality_chartIso (M := M) 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y p
  obtain ⟨K, hKO, hKrel, hGam⟩ := 𝔐.coneSliceFuture (κ p) hp0 (chartImage κ W₀) (mem_chartImage_of_mem hpκ hpW₀)
  have hKU : K ⊆ κ '' ((W₀ : Set M) ∩ U) := by
    intro z hz
    obtain ⟨hz0, hzne, hzle⟩ := hKrel z hz
    obtain ⟨w, hws, hwW, rfl, -⟩ := exists_of_mem_chartImage (hKO hz)
    refine ⟨w, ⟨hwW, ?_⟩, rfl⟩
    have hwp : C.le W₀ w p := ((hiso W₀ hW₀κ w hwW p hpW₀).1).2 hzle
    have hwZ : w ∈ C.Zminus :=
      (hAx.mem_Zminus_iff w).2 fun h => hz0 ((chartAt_mem_singY_iff hws le_rfl).2 h)
    exact mem_of_le_of_mem_interior_Jplus_of_mem_Zminus hconv hSU hpcl hAx.pushUp
      hcorner hwZ hwW.1.1 (C.le_mono le_top hwp) fun h => hzne (by rw [h])
  have hGo : IsOpen (κ '' ((W₀ : Set M) ∩ U)) :=
    κ.isOpen_image_of_subset_source (W₀.isOpen.inter U.isOpen) fun z hz => hz.1.2
  obtain ⟨N, Γ, hyN, hNO, hΓN, hΓG, hNΓ⟩ := hGam _ hGo hKU
  exact slice_assemble hGH harc hext hSU hS hSU' hpU hpκ hW₀κ hNO hyN hΓN hΓG hNΓ
    fun w hw => hw.1.2

/-- **A4 past from the cone-slice B4 (`coneSlicePast`), at every boundary point** (no time reversal of the model;
the slice is taken above `p`, inside the punctured future cone, which the corner condition puts
into `U` near `p`: `mem_of_ge_of_mem_interior_Jminus`, every point being in `Z⁺`). -/
theorem slice_past_of_cone (U : Opens M) (S : Set M)
    (hGH : (chartedCausality 𝔐.causalityY M).GloballyHyperbolic) (hSU : S ⊆ U)
    (hS : (chartedCausality 𝔐.causalityY M).IsCauchySurface S)
    (hSU' : (chartedCausality 𝔐.causalityY M).IsCauchySurfaceOn U S)
    (p : M) (hp : p ∈ frontier (U : Set M))
    (hpS : p ∈ (chartedCausality 𝔐.causalityY M).Jminus ⊤ S)
    (hcorner : (chartedCausality 𝔐.causalityY M).Jplus ⊤ {p} ∩ frontier (U : Set M) ∩
      (chartedCausality 𝔐.causalityY M).Jminus ⊤ S = {p})
    (O : Opens M) (hpO : p ∈ O) :
    ∃ U' : Opens M, U < U' ∧ (U' : Set M) ⊆ U ∪ O ∧
      (chartedCausality 𝔐.causalityY M).GloballyHyperbolicOn U' ∧
      (chartedCausality 𝔐.causalityY M).IsCauchySurfaceOn U' S := by
  set C := chartedCausality 𝔐.causalityY M
  have hAx : C.SingularFlatAxiomsCorr (chartedSing 𝔐.singY M) := 𝔐.singularFlatAxioms
  have harc := hAx.causallyArcConnected
  have hext : C.CurvesExtend := 𝔐.curvesExtend hGH
  have hconv : C.CausallyConvexIn (U : Set M) ⊤ :=
    Causality.causallyConvexIn_of_isCauchySurfaceOn hGH.1 harc hext le_top hSU hSU' hS
  have hpU : p ∉ U := fun h => hp.2 (by rwa [U.isOpen.interior_eq])
  have hpcl : p ∈ closure (U : Set M) := hp.1
  have hJ : C.Jminus ⊤ S ∈ 𝓝 p :=
    Causality.Jminus_mem_nhds_of_isCauchySurface hGH.1 harc hext hS
      (fun x => (hAx.K_densite_sing x).1) (𝔐.isCompact_Jplus_inter_Jminus hGH S hS)
      ⟨hpS, fun h => hpU (hSU h)⟩
  set κ := chartAt 𝔐.Y p with hκ
  have hpκ : p ∈ κ.source := mem_chart_source _ p
  let W₀ : Opens M := ⟨interior (C.Jminus ⊤ S) ∩ O ∩ κ.source,
    (isOpen_interior.inter O.isOpen).inter κ.open_source⟩
  have hpW₀ : p ∈ W₀ := ⟨⟨mem_interior_iff_mem_nhds.2 hJ, hpO⟩, hpκ⟩
  have hW₀κ : W₀ ≤ chartSource κ := fun z hz => hz.2
  have hiso := chartedCausality_chartIso (M := M) 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y p
  obtain ⟨K, hKO, hKrel, hGam⟩ := 𝔐.coneSlicePast (κ p) (chartImage κ W₀) (mem_chartImage_of_mem hpκ hpW₀)
  have hKU : K ⊆ κ '' ((W₀ : Set M) ∩ U) := by
    intro z hz
    obtain ⟨hzne, hzle⟩ := hKrel z hz
    obtain ⟨w, hws, hwW, rfl, -⟩ := exists_of_mem_chartImage (hKO hz)
    refine ⟨w, ⟨hwW, ?_⟩, rfl⟩
    have hpw : C.le W₀ p w := ((hiso W₀ hW₀κ p hpW₀ w hwW).1).2 hzle
    exact mem_of_ge_of_mem_interior_Jminus hconv hSU hpcl hAx.pushUp hAx.mem_Zplus hcorner
      hwW.1.1 (C.le_mono le_top hpw) fun h => hzne (by rw [h])
  have hGo : IsOpen (κ '' ((W₀ : Set M) ∩ U)) :=
    κ.isOpen_image_of_subset_source (W₀.isOpen.inter U.isOpen) fun z hz => hz.1.2
  obtain ⟨N, Γ, hyN, hNO, hΓN, hΓG, hNΓ⟩ := hGam _ hGo hKU
  exact slice_assemble hGH harc hext hSU hS hSU' hpU hpκ hW₀κ hNO hyN hΓN hΓG hNΓ
    fun w hw => hw.1.2

end LocalModel

/-! ### A3 at non-BTZ boundary points (interface round 4) -/

section AssemblyNonBTZ

variable {𝔐 : LocalModel.{u}} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace 𝔐.Y M] [ChartedSpace 𝔐.Y N] [HasGroupoid M 𝔐.G] [HasGroupoid N 𝔐.G]
  [T2Space M] [ConnectedSpace M] [SecondCountableTopology M]
  [T2Space N] [ConnectedSpace N] [SecondCountableTopology N]

/-- **A3 future at a non-BTZ boundary point, any local model** (round 4; Sbierski Lemma 3.8,
`cor:ext_continue`): the conclusion of `GermExtFuture` at every boundary point `p` off the BTZ
locus, regular or massive, from the Level-B fields only (`T2Space Y`, `typeAgreement`,
`dense_regY`, `isOpen_regY`, B1, B2, B3). The corresponding `q` is not BTZ either, model-free
(Prop 3.7: some `x ∈ U` with `x ≪ p` gives `ψ x ≪ q`, and a BTZ point has empty chronological
past). The diamond of the piece is read in the preferred chart at `p` (first disjunct of
`typeAgreement`'s largeness clause); a massive `p` contributes the points of its line below it
(`exists_massive_near`). -/
theorem germ_future_nonBTZ (U : Opens M) (ψ : M → N) (S : Set M)
    (hψ : LiftPropOn 𝔐.G.IsLocalStructomorphWithinAt ψ U)
    (hinj : InjOn ψ U) (hGM : (chartedCausality 𝔐.causalityY M).GloballyHyperbolic)
    (hGN : (chartedCausality 𝔐.causalityY N).GloballyHyperbolic)
    (hGU : (chartedCausality 𝔐.causalityY M).GloballyHyperbolicOn U)
    (hGV : (chartedCausality 𝔐.causalityY N).GloballyHyperbolicOn
      ((isEMorphismOn_of_liftPropOn 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y hψ).imageOpens U
        le_rfl))
    (hSU : S ⊆ U) (hS : (chartedCausality 𝔐.causalityY M).IsCauchySurface S)
    (hSU' : (chartedCausality 𝔐.causalityY M).IsCauchySurfaceOn U S)
    (hψS : (chartedCausality 𝔐.causalityY N).IsCauchySurface (ψ '' S))
    (hψSV : (chartedCausality 𝔐.causalityY N).IsCauchySurfaceOn
      ((isEMorphismOn_of_liftPropOn 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y hψ).imageOpens U
        le_rfl) (ψ '' S))
    (p : M) (q : N) (hp : p ∈ frontier (U : Set M))
    (hpS : p ∈ (chartedCausality 𝔐.causalityY M).Jplus ⊤ S)
    (hcl : MapClusterPt q (𝓝[(U : Set M)] p) ψ)
    (hp0 : chartAt 𝔐.Y p p ∉ 𝔐.singY 0) :
    ∃ (O : Opens M) (φ : M → N), p ∈ O ∧ LiftPropOn 𝔐.G.IsLocalStructomorphWithinAt φ O ∧
      φ p = q ∧ EqOn φ ψ (O ⊓ U : Opens M) := by
  set C := chartedCausality 𝔐.causalityY M
  set D := chartedCausality 𝔐.causalityY N
  have hAxM : C.SingularFlatAxiomsCorr (chartedSing 𝔐.singY M) := 𝔐.singularFlatAxioms
  have hAxN : D.SingularFlatAxiomsCorr (chartedSing 𝔐.singY N) := 𝔐.singularFlatAxioms
  have hextM : C.CurvesExtend := 𝔐.curvesExtend hGM
  have hextN : D.CurvesExtend := 𝔐.curvesExtend hGN
  haveI : Nonempty M := ⟨p⟩
  obtain ⟨hcvU, hcvV, hcorr⟩ := isCorrPair_of_cghd hAxM.causallyArcConnected
    hAxN.causallyArcConnected hextM hextN U hψ hinj hGM hGN hGU hGV hSU hS hSU' hψS hψSV
  set V := (isEMorphismOn_of_liftPropOn 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y hψ).imageOpens U
    le_rfl with hVdef
  have hc : Corresponds (U : Set M) ψ p q := corresponds_iff_mapClusterPt.2 hcl
  have hZp : p ∈ C.Zminus := (hAxM.mem_Zminus_iff p).2 hp0
  have hclM := hGM.isClosed_Jplus_singleton hAxM.tarentin
  have hclN := hGN.isClosed_Jplus_singleton hAxN.tarentin
  have hpU : p ∉ (U : Set M) := by rw [U.isOpen.frontier_eq] at hp; exact hp.2
  have hsepM : C.Jplus ⊤ S ∈ 𝓝 p :=
    Causality.Jplus_mem_nhds_of_isCauchySurface hGM.1 hAxM.causallyArcConnected hextM hS
      (fun x => (hAxM.K_densite_sing x).2) (𝔐.isCompact_Jminus_inter_Jplus hGM S hS)
      ⟨hpS, fun h => hpU (hSU h)⟩
  -- `q` is not BTZ: `ψ x ≪ q` for some `x ∈ U`, and `I⁻` of a BTZ point is empty
  have hq0 : chartAt 𝔐.Y q q ∉ 𝔐.singY 0 := by
    intro hq0
    obtain ⟨x, hxI, hxJ⟩ := hZp _ hsepM
    have hxp : C.lt ⊤ x p := by simpa using hxI
    have hxU := mem_of_mem_Jplus_of_lt hcvU hSU (mem_closure_of_corresponds hc) hxJ hxp
    have hxq := hcorr.lt_of_lt_of_corresponds hcvU hZp hAxN.pushUp hclN hc hxU hxp
    have hmem : ψ x ∈ D.Iminus ⊤ {q} := by simpa using hxq
    rw [hAxN.Iminus_eq_empty q hq0] at hmem
    exact hmem
  have hZq : q ∈ D.Zminus := (hAxN.mem_Zminus_iff q).2 hq0
  have hqfr := hcorr.mem_frontier_of_corresponds hp hc
  have hqV : q ∉ (V : Set N) := by rw [V.isOpen.frontier_eq] at hqfr; exact hqfr.2
  have hqS := hcorr.mem_Jplus_of_corresponds hcvU hZp hAxN.pushUp hclN hc hqV hGM.1 hGN.1
    (hS.isAcausal hAxM.causallyArcConnected hextM) hSU hsepM
    (Causality.mem_Jplus_union_Jminus_of_isCauchySurface hextN hψS q)
  have hsepN : D.Jplus ⊤ (ψ '' S) ∈ 𝓝 q :=
    Causality.Jplus_mem_nhds_of_isCauchySurface hGN.1 hAxN.causallyArcConnected hextN hψS
      (fun x => (hAxN.K_densite_sing x).2) (𝔐.isCompact_Jminus_inter_Jplus hGN _ hψS)
      ⟨hqS, fun h => hqV ((hcorr.mapsTo.mono_left hSU).image_subset h)⟩
  have hiso := chartedCausality_chartIso (M := M) 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y p
  have hpW : p ∈ chartSource (chartAt 𝔐.Y p) := mem_chart_source _ p
  refine germ_ext_nonBTZ U hψ hinj hcorr hcvU hcvV hGN hAxN.tarentin
    (hGM.stronglyCausal hAxM.tarentin) hAxM.causallyArcConnected hZp hZq hAxM.pushUp
    hAxN.pushUp hclM hclN ((hcorr.mapsTo.mono_left hSU).image_subset) hsepN hc hp0 ?_ ?_
  · -- the piece's diamond `I⁺_W(a) ∩ I⁻_W(p)` read in the chart: below the tip `κ p`
    intro a A hlt hsub
    have haW : a ∈ chartSource (chartAt 𝔐.Y p) := C.lt_mem_left hlt
    refine ⟨chartImage (chartAt 𝔐.Y p) (chartSource (chartAt 𝔐.Y p)),
      mem_chartImage_of_mem hpW hpW, chartAt 𝔐.Y p a, mem_chartImage_of_mem haW haW,
      Or.inl ⟨((hiso _ le_rfl a haW p hpW).2).1 hlt, ?_⟩⟩
    rw [← chartedCausality_image_Iplus_inter_Iminus 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y p
      le_rfl haW hpW]
    exact image_mono hsub
  · -- a massive `p`: the points of its line below it
    intro hpreg W hW
    obtain ⟨α, hα0, hpα⟩ := 𝔐.exists_mem_singY_of_not_mem_regY hpreg
    have hαpos : 0 < α := lt_of_le_of_ne hα0 (by rintro rfl; exact hp0 hpα)
    obtain ⟨⟨b, hbW, hbα, hbp⟩, -⟩ := exists_massive_near hAxM hαpos (p := p) hpα
      (inter_mem hW ((chartAt 𝔐.Y p).open_source.mem_nhds (mem_chart_source _ p)))
    exact ⟨b, hbW.1, hbp, fun hreg => hreg α hα0 ((LocalModel.chartAt_mem_singY_iff hbW.2 hα0).2 hbα)⟩

/-- **A3 past at a non-BTZ boundary point, any local model** (round 4; the `K⁺` side): as
`germ_future_nonBTZ` for `C.dual` (every point is in `Z⁺`, `mem_Zplus`); the piece's diamond
`I⁺_W(p) ∩ I⁻_W(a)` lies above the tip `κ p` (second disjunct of `typeAgreement`'s largeness
clause); a massive `p` contributes the points of its line above it. Here `q` may a priori be BTZ;
`typeAgreement` excludes it. -/
theorem germ_past_nonBTZ (U : Opens M) (ψ : M → N) (S : Set M)
    (hψ : LiftPropOn 𝔐.G.IsLocalStructomorphWithinAt ψ U)
    (hinj : InjOn ψ U) (hGM : (chartedCausality 𝔐.causalityY M).GloballyHyperbolic)
    (hGN : (chartedCausality 𝔐.causalityY N).GloballyHyperbolic)
    (hGU : (chartedCausality 𝔐.causalityY M).GloballyHyperbolicOn U)
    (hGV : (chartedCausality 𝔐.causalityY N).GloballyHyperbolicOn
      ((isEMorphismOn_of_liftPropOn 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y hψ).imageOpens U
        le_rfl))
    (hSU : S ⊆ U) (hS : (chartedCausality 𝔐.causalityY M).IsCauchySurface S)
    (hSU' : (chartedCausality 𝔐.causalityY M).IsCauchySurfaceOn U S)
    (hψS : (chartedCausality 𝔐.causalityY N).IsCauchySurface (ψ '' S))
    (hψSV : (chartedCausality 𝔐.causalityY N).IsCauchySurfaceOn
      ((isEMorphismOn_of_liftPropOn 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y hψ).imageOpens U
        le_rfl) (ψ '' S))
    (p : M) (q : N) (hp : p ∈ frontier (U : Set M))
    (hpS : p ∈ (chartedCausality 𝔐.causalityY M).Jminus ⊤ S)
    (hcl : MapClusterPt q (𝓝[(U : Set M)] p) ψ)
    (hp0 : chartAt 𝔐.Y p p ∉ 𝔐.singY 0) :
    ∃ (O : Opens M) (φ : M → N), p ∈ O ∧ LiftPropOn 𝔐.G.IsLocalStructomorphWithinAt φ O ∧
      φ p = q ∧ EqOn φ ψ (O ⊓ U : Opens M) := by
  set C := chartedCausality 𝔐.causalityY M
  set D := chartedCausality 𝔐.causalityY N
  have hAxM : C.SingularFlatAxiomsCorr (chartedSing 𝔐.singY M) := 𝔐.singularFlatAxioms
  have hAxN : D.SingularFlatAxiomsCorr (chartedSing 𝔐.singY N) := 𝔐.singularFlatAxioms
  have hextM : C.CurvesExtend := 𝔐.curvesExtend hGM
  have hextN : D.CurvesExtend := 𝔐.curvesExtend hGN
  haveI : Nonempty M := ⟨p⟩
  obtain ⟨hcvU, hcvV, hcorr⟩ := isCorrPair_of_cghd hAxM.causallyArcConnected
    hAxN.causallyArcConnected hextM hextN U hψ hinj hGM hGN hGU hGV hSU hS hSU' hψS hψSV
  set V := (isEMorphismOn_of_liftPropOn 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y hψ).imageOpens U
    le_rfl with hVdef
  have hc : Corresponds (U : Set M) ψ p q := corresponds_iff_mapClusterPt.2 hcl
  have hcorr' := hcorr.dual
  have hcvU' : C.dual.CausallyConvexIn (U : Set M) ⊤ := Causality.dual_causallyConvexIn.2 hcvU
  have hcvV' : D.dual.CausallyConvexIn (V : Set N) ⊤ := Causality.dual_causallyConvexIn.2 hcvV
  have hZM : ∀ x, x ∈ C.dual.Zminus := fun x => hAxM.mem_Zplus x
  have hZN : ∀ y, y ∈ D.dual.Zminus := fun y => hAxN.mem_Zplus y
  have hPM : C.dual.PushUp := Causality.dual_pushUp.2 hAxM.pushUp
  have hPN : D.dual.PushUp := Causality.dual_pushUp.2 hAxN.pushUp
  have hclM : ∀ x, IsClosed (C.dual.Jplus ⊤ {x}) := hGM.isClosed_Jminus_singleton hAxM.tarentin
  have hclN : ∀ y, IsClosed (D.dual.Jplus ⊤ {y}) := hGN.isClosed_Jminus_singleton hAxN.tarentin
  have hpU : p ∉ (U : Set M) := by rw [U.isOpen.frontier_eq] at hp; exact hp.2
  have hsepM : C.dual.Jplus ⊤ S ∈ 𝓝 p :=
    Causality.Jminus_mem_nhds_of_isCauchySurface hGM.1 hAxM.causallyArcConnected hextM hS
      (fun x => (hAxM.K_densite_sing x).1) (𝔐.isCompact_Jplus_inter_Jminus hGM S hS)
      ⟨hpS, fun h => hpU (hSU h)⟩
  have hqfr := hcorr.mem_frontier_of_corresponds hp hc
  have hqV : q ∉ (V : Set N) := by rw [V.isOpen.frontier_eq] at hqfr; exact hqfr.2
  have hqS : q ∈ D.dual.Jplus ⊤ (ψ '' S) := hcorr'.mem_Jplus_of_corresponds hcvU' (hZM p) hPN
    hclN hc hqV (Causality.dual_isCausal.2 hGM.1) (Causality.dual_isCausal.2 hGN.1)
    (Causality.dual_isAcausal.2 (hS.isAcausal hAxM.causallyArcConnected hextM)) hSU hsepM
    (Causality.mem_Jplus_union_Jminus_of_isCauchySurface hextN hψS q).symm
  have hsepN : D.dual.Jplus ⊤ (ψ '' S) ∈ 𝓝 q :=
    Causality.Jminus_mem_nhds_of_isCauchySurface hGN.1 hAxN.causallyArcConnected hextN hψS
      (fun x => (hAxN.K_densite_sing x).1) (𝔐.isCompact_Jplus_inter_Jminus hGN _ hψS)
      ⟨hqS, fun h => hqV ((hcorr.mapsTo.mono_left hSU).image_subset h)⟩
  have hiso := chartedCausality_chartIso (M := M) 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y p
  have hpW : p ∈ chartSource (chartAt 𝔐.Y p) := mem_chart_source _ p
  refine germ_ext_nonBTZ U hψ hinj hcorr' hcvU' hcvV'
    (Causality.dual_globallyHyperbolic.2 hGN) (Causality.dual_tarentin.2 hAxN.tarentin)
    (Causality.dual_stronglyCausal.2 (hGM.stronglyCausal hAxM.tarentin))
    (Causality.dual_causallyArcConnectedOn.2 hAxM.causallyArcConnected) (hZM p) (hZN q) hPM hPN
    hclM hclN ((hcorr.mapsTo.mono_left hSU).image_subset) hsepN hc hp0 ?_ ?_
  · -- the piece's diamond `I⁺_W(p) ∩ I⁻_W(a)` read in the chart: above the tip `κ p`
    intro a A hlt hsub
    have hlt' : C.lt (chartSource (chartAt 𝔐.Y p)) p a := hlt
    have haW : a ∈ chartSource (chartAt 𝔐.Y p) := C.lt_mem_right hlt'
    refine ⟨chartImage (chartAt 𝔐.Y p) (chartSource (chartAt 𝔐.Y p)),
      mem_chartImage_of_mem hpW hpW, chartAt 𝔐.Y p a, mem_chartImage_of_mem haW haW,
      Or.inr ⟨((hiso _ le_rfl p hpW a haW).2).1 hlt', ?_⟩⟩
    rw [← chartedCausality_image_Iplus_inter_Iminus 𝔐.chartIso_mem 𝔐.absolutelyMinimalOn_Y p
      le_rfl hpW haW]
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨z, hsub ⟨hz.2, hz.1⟩, rfl⟩
  · -- a massive `p`: the points of its line above it
    intro hpreg W hW
    obtain ⟨α, hα0, hpα⟩ := 𝔐.exists_mem_singY_of_not_mem_regY hpreg
    have hαpos : 0 < α := lt_of_le_of_ne hα0 (by rintro rfl; exact hp0 hpα)
    obtain ⟨-, ⟨b, hbW, hbα, hpb⟩⟩ := exists_massive_near hAxM hαpos (p := p) hpα
      (inter_mem hW ((chartAt 𝔐.Y p).open_source.mem_nhds (mem_chart_source _ p)))
    exact ⟨b, hbW.1, hpb, fun hreg => hreg α hα0 ((LocalModel.chartAt_mem_singY_iff hbW.2 hα0).2 hbα)⟩

end AssemblyNonBTZ

/-! ### A3 and A4 for a local model: derived, the BTZ cases as explicit hypotheses (round 4) -/

namespace LocalModel

variable (𝔐 : LocalModel.{u})

/-- **The residual of A3 future: BTZ boundary points** (round 4; the hypothesis `hA3f` of
`Geometry.ofLocalModelOfBTZ`). The statement of `GermExtFuture` at boundary points `p` of the BTZ
locus (`p ∈ sing s 0`, last hypothesis). Not derived here: at a BTZ `p`, `I⁻(p) = ∅`, so `p ∉ Z⁻`
and Sbierski's past piece of `U` near `p` is empty. **Owed by gx for `E₀`**: thesis
`lem:passe_pgcd` (`these.tex:6541–6554`) — a point of `p`'s line below `p` lies in `U` — then B2 at
a singular point of `U` (`localUnique_sing`), as in the massive case (`germ_ext_nonBTZ`).
Vacuous for a model without BTZ points (`germExtFutureBTZ_of_singY_zero`). -/
def GermExtFutureBTZ : Prop :=
  ∀ {M N : Type u} [TopologicalSpace M] [TopologicalSpace N] [T2Space M]
    [ConnectedSpace M] [SecondCountableTopology M] [T2Space N] [ConnectedSpace N]
    [SecondCountableTopology N] (s : 𝔐.Str M) (t : 𝔐.Str N) (U : Opens M)
    (ψ : M → N) (S : Set M) (h : IsMor s t U ψ), InjOn ψ U →
    (causality s).GloballyHyperbolic → (causality t).GloballyHyperbolic →
    (causality s).GloballyHyperbolicOn U →
    (causality t).GloballyHyperbolicOn ((isEMorphismOn_of_isMor h).imageOpens U le_rfl) →
    S ⊆ U → (causality s).IsCauchySurface S → (causality s).IsCauchySurfaceOn U S →
    (causality t).IsCauchySurface (ψ '' S) →
    (causality t).IsCauchySurfaceOn ((isEMorphismOn_of_isMor h).imageOpens U le_rfl) (ψ '' S) →
    ∀ p : M, ∀ q : N, p ∈ frontier (U : Set M) → p ∈ (causality s).Jplus ⊤ S →
      MapClusterPt q (𝓝[(U : Set M)] p) ψ → p ∈ sing s 0 →
      ∃ (O : Opens M) (φ : M → N), p ∈ O ∧ IsMor s t O φ ∧ φ p = q ∧ EqOn φ ψ (O ⊓ U : Opens M)

/-- **The residual of A3 past: BTZ boundary points** (round 4; the hypothesis `hA3p` of
`Geometry.ofLocalModelOfBTZ`). The statement of `GermExtPast` at boundary points `p` of the BTZ
locus. Not derived here. The route is mapped: `germ_exists_piece` for `C.dual` gives a connected
open `A ⊆ U ∩ I⁺(p)` with `I⁺(p) ∩ I⁻(a) ⊆ A` and `ψ → q` along `A`, whose chart image meets the
round-3 diamond clause of `localUnique_sing_adherent` (`diamond_clause_of_piece`, proved).
**Owed by gx for `E₀`**: a **regular** `a ∈ U ∩ I⁺(p)` (density of `reg` in `I⁺(p)`), `I⁺(p)`
**regular near `p`** (so the piece is a regular set, as `localUnique_sing_adherent` asks), and the
corresponding `q` BTZ with its chart in the component of `κ p` (type agreement at a BTZ point,
which `typeAgreement` does not ask). Vacuous without BTZ points. -/
def GermExtPastBTZ : Prop :=
  ∀ {M N : Type u} [TopologicalSpace M] [TopologicalSpace N] [T2Space M]
    [ConnectedSpace M] [SecondCountableTopology M] [T2Space N] [ConnectedSpace N]
    [SecondCountableTopology N] (s : 𝔐.Str M) (t : 𝔐.Str N) (U : Opens M)
    (ψ : M → N) (S : Set M) (h : IsMor s t U ψ), InjOn ψ U →
    (causality s).GloballyHyperbolic → (causality t).GloballyHyperbolic →
    (causality s).GloballyHyperbolicOn U →
    (causality t).GloballyHyperbolicOn ((isEMorphismOn_of_isMor h).imageOpens U le_rfl) →
    S ⊆ U → (causality s).IsCauchySurface S → (causality s).IsCauchySurfaceOn U S →
    (causality t).IsCauchySurface (ψ '' S) →
    (causality t).IsCauchySurfaceOn ((isEMorphismOn_of_isMor h).imageOpens U le_rfl) (ψ '' S) →
    ∀ p : M, ∀ q : N, p ∈ frontier (U : Set M) → p ∈ (causality s).Jminus ⊤ S →
      MapClusterPt q (𝓝[(U : Set M)] p) ψ → p ∈ sing s 0 →
      ∃ (O : Opens M) (φ : M → N), p ∈ O ∧ IsMor s t O φ ∧ φ p = q ∧ EqOn φ ψ (O ⊓ U : Opens M)

/-- **The residual of A4 future: BTZ boundary points** (round 4; the hypothesis `hA4f` of
`Geometry.ofLocalModelOfBTZ`). The statement of `SliceFuture` at boundary points `p` of the BTZ
locus. Not derived here: near a BTZ `p` the punctured causal past `J⁻(p) ∖ {p}` is a segment of
`p`'s line (`past_local`), so no cone slice exists (`coneSliceFuture` is asked off `sing₀`), and
the cone lemma's `Z⁻` step fails on the line (`I⁻ = ∅`). **Owed by gx for `E₀`**: a slice off the
cone — Sbierski's `τ_q`, `q ∈ I⁺(p)`, with Lemma 3.11 (the maximum of `τ_q` on the compact
`J⁻(q) ∩ Uᶜ ∩ J⁺(Σ)`), or an `E₀`-specific slice, with what the corner condition gives on the line
below `p`. Vacuous without BTZ points. -/
def SliceFutureBTZ : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [SecondCountableTopology M] (s : 𝔐.Str M) (U : Opens M) (S : Set M),
    (causality s).GloballyHyperbolic →
    (causality s).GloballyHyperbolicOn U → S ⊆ U → (causality s).IsCauchySurface S →
    (causality s).IsCauchySurfaceOn U S → ∀ p : M, p ∈ frontier (U : Set M) →
    p ∈ (causality s).Jplus ⊤ S →
    (causality s).Jminus ⊤ {p} ∩ frontier (U : Set M) ∩ (causality s).Jplus ⊤ S = {p} →
    ∀ O : Opens M, p ∈ O → p ∈ sing s 0 → ∃ U' : Opens M, U < U' ∧ (U' : Set M) ⊆ U ∪ O ∧
      (causality s).GloballyHyperbolicOn U' ∧ (causality s).IsCauchySurfaceOn U' S

variable {𝔐}

/-- **A3 future from Level B, BTZ points as a hypothesis** (Sbierski Lemma 3.8;
`cor:ext_continue`): off the BTZ locus `germ_future_nonBTZ` (regular and massive `p`), at BTZ
points `hB`. -/
theorem germExtFuture_of (hB : 𝔐.GermExtFutureBTZ) : 𝔐.GermExtFuture := by
  intro M N _ _ _ _ _ _ _ _ s t U ψ S h hinj hGM hGN hGU hGV hSU hS hSU' hψS hψSV p q hp hpS hcl
  by_cases hp0 : p ∈ sing s 0
  · exact hB s t U ψ S h hinj hGM hGN hGU hGV hSU hS hSU' hψS hψSV p q hp hpS hcl hp0
  obtain ⟨cs, hgs⟩ := s
  obtain ⟨ct, hgt⟩ := t
  exact germ_future_nonBTZ U ψ S h hinj hGM hGN hGU hGV hSU hS hSU' hψS hψSV p q hp hpS hcl hp0

/-- **A3 past from Level B, BTZ points as a hypothesis** (Sbierski Lemma 3.8, the `K⁺` side):
off the BTZ locus `germ_past_nonBTZ`, at BTZ points `hB`. -/
theorem germExtPast_of (hB : 𝔐.GermExtPastBTZ) : 𝔐.GermExtPast := by
  intro M N _ _ _ _ _ _ _ _ s t U ψ S h hinj hGM hGN hGU hGV hSU hS hSU' hψS hψSV p q hp hpS hcl
  by_cases hp0 : p ∈ sing s 0
  · exact hB s t U ψ S h hinj hGM hGN hGU hGV hSU hS hSU' hψS hψSV p q hp hpS hcl hp0
  obtain ⟨cs, hgs⟩ := s
  obtain ⟨ct, hgt⟩ := t
  exact germ_past_nonBTZ U ψ S h hinj hGM hGN hGU hGV hSU hS hSU' hψS hψSV p q hp hpS hcl hp0

/-- **A4 future from Level B, BTZ points as a hypothesis** (Sbierski Thm 3.6, geometric half):
off the BTZ locus `slice_future_of_cone` (from the field `coneSliceFuture`), at BTZ points
`hB`. -/
theorem sliceFuture_of (hB : 𝔐.SliceFutureBTZ) : 𝔐.SliceFuture := by
  intro M _ _ _ _ s U S hGH hGHU hSU hS hSU' p hp hpS hc O hpO
  by_cases hp0 : p ∈ sing s 0
  · exact hB s U S hGH hGHU hSU hS hSU' p hp hpS hc O hpO hp0
  obtain ⟨cs, hgs⟩ := s
  exact slice_future_of_cone U S hGH hSU hS hSU' p hp hpS hc O hpO hp0

variable (𝔐) in
/-- **A4 past from Level B, proved** (no time reversal, gx D-12(e)): `slice_past_of_cone`, from the
field `coneSlicePast`, at every boundary point, BTZ included (every point is in `Z⁺`). -/
theorem slicePast : 𝔐.SlicePast := by
  intro M _ _ _ _ s U S hGH _hGHU hSU hS hSU' p hp hpS hc O hpO
  obtain ⟨cs, hgs⟩ := s
  exact slice_past_of_cone U S hGH hSU hS hSU' p hp hpS hc O hpO

/-- A model without BTZ points satisfies the A3-future residual vacuously. -/
theorem germExtFutureBTZ_of_singY_zero (h0 : 𝔐.singY 0 = ∅) : 𝔐.GermExtFutureBTZ := by
  intro M N _ _ _ _ _ _ _ _ s t U ψ S h _ _ _ _ _ _ _ _ _ _ p q _ _ _ hp0
  have : _ ∈ 𝔐.singY 0 := hp0
  rw [h0] at this
  exact absurd this (Set.notMem_empty _)

/-- A model without BTZ points satisfies the A3-past residual vacuously. -/
theorem germExtPastBTZ_of_singY_zero (h0 : 𝔐.singY 0 = ∅) : 𝔐.GermExtPastBTZ := by
  intro M N _ _ _ _ _ _ _ _ s t U ψ S h _ _ _ _ _ _ _ _ _ _ p q _ _ _ hp0
  have : _ ∈ 𝔐.singY 0 := hp0
  rw [h0] at this
  exact absurd this (Set.notMem_empty _)

/-- A model without BTZ points satisfies the A4-future residual vacuously. -/
theorem sliceFutureBTZ_of_singY_zero (h0 : 𝔐.singY 0 = ∅) : 𝔐.SliceFutureBTZ := by
  intro M _ _ _ _ s U S _ _ _ _ _ p _ _ _ O _ hp0
  have : _ ∈ 𝔐.singY 0 := hp0
  rw [h0] at this
  exact absurd this (Set.notMem_empty _)

end LocalModel

namespace Geometry

/-- **Level B ⇒ Level A, the BTZ cases as explicit hypotheses** (design §2, interface round 4):
every field of `Geometry` is derived from the local model (`ofLocalModelOfGermSlice`, with A3 by
`germExtFuture_of`/`germExtPast_of`, A4 by `sliceFuture_of`/`slicePast`), except the three
BTZ-point residuals `hA3f : 𝔐.GermExtFutureBTZ`, `hA3p : 𝔐.GermExtPastBTZ`,
`hA4f : 𝔐.SliceFutureBTZ` (A3 future / past and A4 future at boundary points of the BTZ locus;
A4 past has none). Replaces the sorried `Geometry.ofLocalModel` (deleted 2026-11-02). -/
noncomputable def ofLocalModelOfBTZ (𝔐 : LocalModel.{u}) (hA3f : 𝔐.GermExtFutureBTZ)
    (hA3p : 𝔐.GermExtPastBTZ) (hA4f : 𝔐.SliceFutureBTZ) : Geometry.{u} :=
  ofLocalModelOfGermSlice 𝔐 (LocalModel.germExtFuture_of hA3f) (LocalModel.germExtPast_of hA3p)
    (LocalModel.sliceFuture_of hA4f) (LocalModel.slicePast 𝔐)

@[simp] theorem ofLocalModelOfBTZ_toPreGeometry (𝔐 : LocalModel.{u}) (hA3f : 𝔐.GermExtFutureBTZ)
    (hA3p : 𝔐.GermExtPastBTZ) (hA4f : 𝔐.SliceFutureBTZ) :
    (ofLocalModelOfBTZ 𝔐 hA3f hA3p hA4f).toPreGeometry = 𝔐.toPreGeometry := rfl

/-- **Level B ⇒ Level A for a model without BTZ points** (`singY 0 = ∅`; the flat model, or a
model with massive particles only): no hypothesis beyond the fields. -/
noncomputable def ofLocalModelNoBTZ (𝔐 : LocalModel.{u}) (h0 : 𝔐.singY 0 = ∅) : Geometry.{u} :=
  ofLocalModelOfBTZ 𝔐 (LocalModel.germExtFutureBTZ_of_singY_zero h0)
    (LocalModel.germExtPastBTZ_of_singY_zero h0) (LocalModel.sliceFutureBTZ_of_singY_zero h0)

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
counterexample (REPORT, interface needs (1)) refutes in `E₀`. Kept as the record of the
finding that led to interface round 3's diamond clause (with `r ∈ reg`, which excludes `r := y₀`). -/
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


namespace CBG

/-! ### Interface round 3: the past-side piece meets the diamond clause -/

section DiamondClause

variable {Y : Type u} [TopologicalSpace Y] {G : StructureGroupoid Y} {D : Causality Y}
  {M : Type u} [TopologicalSpace M] [ChartedSpace Y M] [HasGroupoid M G]

/-- **The round-3 diamond clause holds for A3-past's piece** (design §6, interface round 3, check
asked by gx). Let `U` be causally convex in the open `B`, `p ∈ closure U`, `r ∈ U`, `p ≪_W r` in an
open `W ≤ B` inside the source of the preferred chart `κ = chartAt Y x`, and `κ r ∈ R` (for the
field, `R = reg(Y)`). Then, with `O = κ(W)`, `y₀ = κ p`, `r' = κ r`:
`∃ O ∋ y₀, ∃ r' ∈ O, r' ∈ R ∧ y₀ ≪_O r' ∧ R ∩ I⁺_O(y₀) ∩ I⁻_O(r') ⊆ κ(U ∩ I⁻_W(r) ∩ κ⁻¹ R)` —
the largeness clause of `LocalModel.localUnique_sing_adherent` for the regular part of the piece
`U ∩ I⁻_W(r)`. From `Causality.CausallyConvexIn.Iplus_inter_Iminus_subset` and the chart reading
`chartedCausality_image_Iplus_inter_Iminus`. Unlike round 2's clause, this one is not vacuous: the
regular tip `r'` excludes `r' := y₀`. -/
theorem diamond_clause_of_piece (hGD : ∀ e ∈ G, ChartIso D D e)
    (hA : ∀ W : Opens Y, D.AbsolutelyMinimalOn W) (x : M) {W : Opens M}
    (hW : W ≤ chartSource (chartAt Y x)) {U : Set M} {B : Opens M}
    (hU : (chartedCausality D M).CausallyConvexIn U B) (hWB : W ≤ B) {p r : M}
    (hp : p ∈ closure U) (hpW : p ∈ W) (hrU : r ∈ U) (hrW : r ∈ W)
    (hpr : (chartedCausality D M).lt W p r) (R : Set Y) (hrR : chartAt Y x r ∈ R) :
    ∃ O : Opens Y, chartAt Y x p ∈ O ∧ ∃ r' ∈ O, r' ∈ R ∧ D.lt O (chartAt Y x p) r' ∧
      R ∩ D.Iplus O {chartAt Y x p} ∩ D.Iminus O {r'} ⊆
        chartAt Y x '' (U ∩ (chartedCausality D M).Iminus W {r} ∩ chartAt Y x ⁻¹' R) := by
  have hc := chartedCausality_chartIso (M := M) hGD hA x
  refine ⟨chartImage (chartAt Y x) W, mem_chartImage_of_mem (hW hpW) hpW, chartAt Y x r,
    mem_chartImage_of_mem (hW hrW) hrW, hrR, ((hc W hW p hpW r hrW).2).1 hpr, ?_⟩
  rintro y ⟨⟨hyR, hy1⟩, hy2⟩
  have hy : y ∈ chartAt Y x '' ((chartedCausality D M).Iplus W {p} ∩
      (chartedCausality D M).Iminus W {r}) := by
    rw [chartedCausality_image_Iplus_inter_Iminus hGD hA x hW hpW hrW]; exact ⟨hy1, hy2⟩
  obtain ⟨z, hz, rfl⟩ := hy
  exact ⟨z, ⟨⟨Causality.CausallyConvexIn.Iplus_inter_Iminus_subset hU hp hrU hWB hz, hz.2⟩, hyR⟩,
    rfl⟩

end DiamondClause

end CBG

end Causal
