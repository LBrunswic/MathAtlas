import Mathlib.Geometry.Manifold.HasGroupoid
import Mathlib.Topology.Algebra.ConstMulAction

/-!
# `Benzecri.Structure.Groupoid` — the groupoid of a group action (plan F2)

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332. Package WP-45c (wave 1, layer L0). No ledger label is certified here: this module
is the infrastructure (plan `campaign/WP-45-plan/CH1-PLAN.md`, F2) through which the paper's
locally projective (resp. affine) manifolds of Déf. 12
(`bzdef:c1s1d12_variete_localement_projective`, `benzecri1960_ch1.tex:304`, p. 236) and the
compatible charts of Déf. 13
(`bzdef:c1s1d13_carte_compatible`, `benzecri1960_ch1.tex:331`, p. 237) will be defined, as a
`ChartedSpace X V` with `HasGroupoid V (gxGroupoid G X)` for `(G, X) = (GS(n, ℝ), S(n))` (resp.
`(GA(n, ℝ), ℝⁿ)`). Neither label is marked or even cited as certified: that is wave 2's
`Structure/Basic`.

> 2° $GS(n, \R)$ [resp. $GA(n, \R)$] opère transitivement sur chaque fibre de $J(V)$, composée
> des jets de source donnée. (Déf. 12, `benzecri1960_ch1.tex:313`, p. 236)

The rigidity class is what Prop. 1 (`bzprop:c1s1p1_cartes_compatibles`, p. 237: two compatible
charts of a connected open set differ by a unique element of the group) needs of the action.

**Ported, not imported (DEC-112).** Everything here is a minimal local copy of
`lean-gx/GX/Structure/Basic.lean` at lean-gx commit `4a577c5`:
`GX.IsRigidAction` (l.113), `GX.IsAnalyticAction` (l.118), `GX.eq_of_eqOn` (l.132),
`GX.IsAnalyticAction.of_eq_of_eqOn` (l.138), `GX.isAnalyticAction_iff` (l.145),
`GX.gxPregroupoid` (l.162), `GX.gxGroupoid` (l.189), `GX.mem_gxGroupoid_iff` (l.191),
`GX.exists_smul_eq_of_mem_gxGroupoid` (l.199),
`GX.eventually_smul_eq_of_mem_gxGroupoid` (l.220), `GX.symm_trans_mem_gxGroupoid` (l.228),
`GX.symm_trans_mem_gxGroupoid_iff` (l.254), `GX.closedUnderRestriction_gxGroupoid` (l.264) —
themselves ported from `lean-causal/Causal/GXStructure.lean`. The definitions are verbatim, so the
later bridge `Benzecri.gxGroupoid G X = GX.gxGroupoid G X` is `rfl`. New here:
`Benzecri.gxGroupoid_mono` (monotonicity in `G`), `Benzecri.transport_mem_gxGroupoid`
(monotonicity in an open `X' ⊆ X`: along an open embedding `ι : X' → X` equivariant through
`φ : G' →* G`, an element of `gxGroupoid G' X'` transports into `gxGroupoid G X` — the groupoid-map
form of plan F2's item, needed by `bzrem:c1s1r1_affine_vers_projective`),
`Benzecri.isRigidAction_iff_eqOn_id` (the one-element form of rigidity),
`Benzecri.IsRigidAction.of_comp` (rigidity of an action through a hom),
`Benzecri.gxGroupoid_subgroup_le` (monotonicity in `G` for a subgroup) and
`Benzecri.smul_mem_gxGroupoid` (every element of `G`, as a homeomorphism of `X`, is in
`gxGroupoid G X`).

## Hypothesis checklist

| hypothesis | here |
|---|---|
| `G` a group acting on `X` by homeomorphisms | ✓ carried: `[Group G] [MulAction G X] [ContinuousConstSMul G X]` |
| rigidity (agreement on a nonempty open set ⇒ agreement) | a class, `IsRigidAction G X`, assumed only where used |

## SCOPE (disclosed)

* Infrastructure only: no statement of the paper is certified here, so nothing is marked.
* The maximal-atlas, atlas and morphism sections of the gx original (l.277–911) are not ported:
  they belong to `Structure/Basic` (wave 2).
* Monotonicity in an open `X' ⊆ X` is given in its groupoid-map form
  (`transport_mem_gxGroupoid`); the `HasGroupoid` form for a charted space (a `(G', X')`-manifold is
  a `(G, X)`-manifold through `ι`, via Mathlib's `ChartedSpace.comp`) is `Structure/Basic`'s, with
  `bzrem:c1s1r1_affine_vers_projective`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Benzecri

open Set Filter Topology

universe u v w w'

/-! ### Rigid and analytic actions -/

section Analytic

variable (G : Type w) (X : Type v) [TopologicalSpace X] [Group G] [MulAction G X]

/-- **Rigidity** of an action: two elements whose actions agree on a nonempty open set agree
everywhere. Port of `GX.IsRigidAction` (`lean-gx/GX/Structure/Basic.lean:113`). -/
class IsRigidAction : Prop where
  smul_eq_of_eqOn : ∀ {g h : G} {U : Set X}, IsOpen U → U.Nonempty →
    EqOn (fun p : X => g • p) (fun p => h • p) U → ∀ p : X, g • p = h • p

/-- **An analytical action**: faithful and rigid. Port of `GX.IsAnalyticAction`
(`lean-gx/GX/Structure/Basic.lean:118`). -/
class IsAnalyticAction : Prop extends FaithfulSMul G X, IsRigidAction G X

variable {G X}

/-- **One-element form of rigidity**: an element agreeing with the identity on a nonempty open set
acts as the identity. -/
theorem isRigidAction_iff_eqOn_id :
    IsRigidAction G X ↔ ∀ {g : G} {U : Set X}, IsOpen U → U.Nonempty →
      EqOn (fun p : X => g • p) id U → ∀ p : X, g • p = p := by
  constructor
  · intro h g U hU hne heq p
    have := h.smul_eq_of_eqOn (g := g) (h := 1) hU hne (fun x hx => by simpa using heq hx) p
    simpa using this
  · intro h
    refine ⟨fun {g k U} hU hne heq p => ?_⟩
    have := h (g := k⁻¹ * g) hU hne (fun x hx => by
      have hx' : g • x = k • x := heq hx
      simp only [id, mul_smul]
      rw [hx', inv_smul_smul]) p
    rw [mul_smul, inv_smul_eq_iff] at this
    exact this

/-- Under an analytical action, two elements agreeing on a nonempty open set are equal. Port of
`GX.eq_of_eqOn` (`lean-gx/GX/Structure/Basic.lean:132`). -/
theorem eq_of_eqOn [IsAnalyticAction G X] {g h : G} {U : Set X} (hU : IsOpen U)
    (hne : U.Nonempty) (heq : EqOn (fun p : X => g • p) (fun p => h • p) U) : g = h :=
  FaithfulSMul.eq_of_smul_eq_smul (IsRigidAction.smul_eq_of_eqOn hU hne heq)

/-- The introduction's formulation: two elements agreeing on a nonempty open set are equal. Port
of `GX.IsAnalyticAction.of_eq_of_eqOn` (`lean-gx/GX/Structure/Basic.lean:138`). -/
theorem IsAnalyticAction.of_eq_of_eqOn [Nonempty X]
    (h : ∀ {g h : G} {U : Set X}, IsOpen U → U.Nonempty →
      EqOn (fun p : X => g • p) (fun p => h • p) U → g = h) : IsAnalyticAction G X where
  eq_of_smul_eq_smul hgh := h isOpen_univ univ_nonempty fun p _ => hgh p
  smul_eq_of_eqOn hU hne heq := by rw [h hU hne heq]; exact fun _ => rfl

/-- Port of `GX.isAnalyticAction_iff` (`lean-gx/GX/Structure/Basic.lean:145`). -/
theorem isAnalyticAction_iff [Nonempty X] : IsAnalyticAction G X ↔
    ∀ {g h : G} {U : Set X}, IsOpen U → U.Nonempty →
      EqOn (fun p : X => g • p) (fun p => h • p) U → g = h :=
  ⟨fun _ _ _ _ hU hne heq => eq_of_eqOn hU hne heq, IsAnalyticAction.of_eq_of_eqOn⟩

/-- Rigidity passes to an action through a hom: if `G'` acts through `φ : G' →* G` and `G` acts
rigidly, so does `G'`. -/
theorem IsRigidAction.of_comp {G' : Type w'} [Group G'] [MulAction G' X] (φ : G' →* G)
    (hφ : ∀ (g : G') (p : X), g • p = φ g • p) [IsRigidAction G X] : IsRigidAction G' X := by
  refine ⟨fun {g h U} hU hne heq p => ?_⟩
  rw [hφ, hφ]
  exact IsRigidAction.smul_eq_of_eqOn hU hne (fun x hx => by
    simpa [hφ] using heq hx) p

end Analytic

/-! ### The groupoid of a `(G,X)`-structure -/

section Groupoid

variable {G : Type w} {X : Type v} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] {M : Type u} [TopologicalSpace M]

variable (G X) in
/-- The pregroupoid of the maps which are, near every point of the set, the action of an element
of `G`. Port of `GX.gxPregroupoid` (`lean-gx/GX/Structure/Basic.lean:162`). -/
def gxPregroupoid : Pregroupoid X where
  property f s := ∀ x ∈ s, ∃ g : G, f =ᶠ[𝓝 x] fun y => g • y
  comp {f f' u v} hf hf' _ _ _ := by
    rintro x ⟨hxu, hxv⟩
    obtain ⟨a, ha⟩ := hf x hxu
    obtain ⟨b, hb⟩ := hf' (f x) hxv
    have hcont : ContinuousAt f x :=
      (continuous_const_smul a).continuousAt.congr ha.symm
    refine ⟨b * a, ?_⟩
    filter_upwards [hcont.eventually hb, ha] with y hy hy'
    show f' (f y) = (b * a) • y
    rw [hy, hy', mul_smul]
  id_mem x _ := ⟨1, Eventually.of_forall fun y => (one_smul G y).symm⟩
  locality {f u} _ h x hx := by
    obtain ⟨v, -, hxv, hp⟩ := h x hx
    exact hp x ⟨hx, hxv⟩
  congr {f f' u} hu heq hf x hx := by
    obtain ⟨g, hg⟩ := hf x hx
    refine ⟨g, ?_⟩
    filter_upwards [hu.mem_nhds hx, hg] with y hy hy'
    rw [heq y hy, hy']

variable (G X) in
/-- **The groupoid of a `(G,X)`-structure**: the open partial homeomorphisms of `X` which, near
every point of their source, are the restriction of an element of `G` (and so is their inverse).
A `(G,X)`-manifold is a charted space `ChartedSpace X M` with `HasGroupoid M (gxGroupoid G X)`
(plan F2). Port of `GX.gxGroupoid` (`lean-gx/GX/Structure/Basic.lean:189`). -/
def gxGroupoid : StructureGroupoid X := (gxPregroupoid G X).groupoid

/-- Membership in `gxGroupoid G X`. Port of `GX.mem_gxGroupoid_iff`
(`lean-gx/GX/Structure/Basic.lean:191`). -/
theorem mem_gxGroupoid_iff {f : OpenPartialHomeomorph X X} :
    f ∈ gxGroupoid G X ↔ (∀ x ∈ f.source, ∃ g : G, f =ᶠ[𝓝 x] fun y => g • y) ∧
      ∀ x ∈ f.target, ∃ g : G, f.symm =ᶠ[𝓝 x] fun y => g • y :=
  Iff.rfl

/-- The transition between two charts is, near every point of the overlap, the action of an
element of `G`. Port of `GX.exists_smul_eq_of_mem_gxGroupoid`
(`lean-gx/GX/Structure/Basic.lean:199`). -/
theorem exists_smul_eq_of_mem_gxGroupoid {e e' : OpenPartialHomeomorph M X}
    (h : e.symm.trans e' ∈ gxGroupoid G X) {x : M} (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    ∃ g : G, ∃ O : TopologicalSpace.Opens M, x ∈ O ∧ (O : Set M) ⊆ e.source ∩ e'.source ∧
      ∀ z ∈ O, e' z = g • e z := by
  have hmem : e x ∈ (e.symm.trans e').source := by
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
    exact ⟨e.map_source hx, by simpa [e.left_inv hx] using hx'⟩
  obtain ⟨g, hg⟩ := (mem_groupoid_of_pregroupoid.1 h).1 (e x) hmem
  rw [OpenPartialHomeomorph.coe_trans] at hg
  let O : TopologicalSpace.Opens M :=
    ⟨(e.source ∩ e'.source) ∩ e ⁻¹' interior {y | e' (e.symm y) = g • y}, by
      have := e.isOpen_inter_preimage (isOpen_interior (s := {y | e' (e.symm y) = g • y}))
      convert this.inter e'.open_source using 1
      ext z; simp only [mem_inter_iff, mem_preimage]; tauto⟩
  refine ⟨g, O, ⟨⟨hx, hx'⟩, ?_⟩, fun z hz => ⟨hz.1.1, hz.1.2⟩, fun z hz => ?_⟩
  · exact mem_interior_iff_mem_nhds.2 hg
  · have := interior_subset hz.2
    simp only [mem_setOf_eq, e.left_inv hz.1.1] at this
    exact this

/-- The eventual form: near every point of the overlap, `e' = g • e`. Port of
`GX.eventually_smul_eq_of_mem_gxGroupoid` (`lean-gx/GX/Structure/Basic.lean:220`). -/
theorem eventually_smul_eq_of_mem_gxGroupoid {e e' : OpenPartialHomeomorph M X}
    (h : e.symm.trans e' ∈ gxGroupoid G X) {x : M} (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    ∃ g : G, ∀ᶠ z in 𝓝 x, e' z = g • e z := by
  obtain ⟨g, O, hxO, -, hO⟩ := exists_smul_eq_of_mem_gxGroupoid h hx hx'
  exact ⟨g, Filter.mem_of_superset (O.isOpen.mem_nhds hxO) hO⟩

/-- Conversely, if near every point of the overlap `e' = g • e` for some `g`, the transition
`e.symm ≫ e'` lies in the groupoid. Port of `GX.symm_trans_mem_gxGroupoid`
(`lean-gx/GX/Structure/Basic.lean:228`). -/
theorem symm_trans_mem_gxGroupoid {e e' : OpenPartialHomeomorph M X}
    (h : ∀ x ∈ e.source ∩ e'.source, ∃ g : G, ∀ᶠ z in 𝓝 x, e' z = g • e z) :
    e.symm.trans e' ∈ gxGroupoid G X := by
  have key : ∀ {e e' : OpenPartialHomeomorph M X},
      (∀ x ∈ e.source ∩ e'.source, ∃ g : G, ∀ᶠ z in 𝓝 x, e' z = g • e z) →
      (gxPregroupoid G X).property (e.symm.trans e') (e.symm.trans e').source := by
    intro e e' h q hq
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hq
    obtain ⟨g, hg⟩ := h (e.symm q) ⟨e.map_target hq.1, hq.2⟩
    refine ⟨g, ?_⟩
    filter_upwards [(e.continuousAt_symm hq.1).eventually hg,
      e.eventually_right_inverse hq.1] with w hw hw'
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, hw, hw']
  refine mem_groupoid_of_pregroupoid.2 ⟨key h, ?_⟩
  have h' : ∀ x ∈ e'.source ∩ e.source, ∃ g : G, ∀ᶠ z in 𝓝 x, e z = g • e' z := by
    intro x hx
    obtain ⟨g, hg⟩ := h x ⟨hx.2, hx.1⟩
    refine ⟨g⁻¹, ?_⟩
    filter_upwards [hg] with z hz
    rw [hz, inv_smul_smul]
  have := key h'
  rwa [← OpenPartialHomeomorph.symm_source, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.symm_symm]

/-- Membership of a transition in the `(G,X)`-groupoid, pointwise on the overlap. Port of
`GX.symm_trans_mem_gxGroupoid_iff` (`lean-gx/GX/Structure/Basic.lean:254`). -/
theorem symm_trans_mem_gxGroupoid_iff {e e' : OpenPartialHomeomorph M X} :
    e.symm.trans e' ∈ gxGroupoid G X ↔
      ∀ x ∈ e.source ∩ e'.source, ∃ g : G, ∀ᶠ z in 𝓝 x, e' z = g • e z :=
  ⟨fun h _ hx => eventually_smul_eq_of_mem_gxGroupoid h hx.1 hx.2, symm_trans_mem_gxGroupoid⟩

/-- **`gxGroupoid G X` is closed under restriction**, so an open subset of a `(G,X)`-manifold is a
`(G,X)`-manifold (Mathlib's `TopologicalSpace.Opens.instHasGroupoid`). Port of
`GX.closedUnderRestriction_gxGroupoid` (`lean-gx/GX/Structure/Basic.lean:264`). -/
instance closedUnderRestriction_gxGroupoid : ClosedUnderRestriction (gxGroupoid G X) := by
  refine ⟨fun {e} he s _ => ?_⟩
  rw [gxGroupoid, mem_groupoid_of_pregroupoid] at he ⊢
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨g, hg⟩ := he.1 x (by rw [OpenPartialHomeomorph.restr_source] at hx; exact hx.1)
    exact ⟨g, by simpa using hg⟩
  · obtain ⟨g, hg⟩ := he.2 x (by rw [OpenPartialHomeomorph.restr_target] at hx; exact hx.1)
    exact ⟨g, by simpa using hg⟩

/-- **Monotonicity in `G`**: if every element of `G` acts on `X` as some element of `G'`, then
`gxGroupoid G X ≤ gxGroupoid G' X`. (E.g. a subgroup, or a group acting through a hom.) -/
theorem gxGroupoid_mono {G' : Type w'} [Group G'] [MulAction G' X] [ContinuousConstSMul G' X]
    (h : ∀ g : G, ∃ g' : G', ∀ p : X, g • p = g' • p) : gxGroupoid G X ≤ gxGroupoid G' X := by
  intro f hf
  have hf : f ∈ gxGroupoid G X := hf
  show f ∈ gxGroupoid G' X
  rw [mem_gxGroupoid_iff] at hf ⊢
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨g, hg⟩ := hf.1 x hx
    obtain ⟨g', hg'⟩ := h g
    exact ⟨g', hg.trans (Eventually.of_forall fun y => hg' y)⟩
  · obtain ⟨g, hg⟩ := hf.2 x hx
    obtain ⟨g', hg'⟩ := h g
    exact ⟨g', hg.trans (Eventually.of_forall fun y => hg' y)⟩

/-- Monotonicity in `G` for a subgroup. -/
theorem gxGroupoid_subgroup_le (H : Subgroup G) [ContinuousConstSMul H X] :
    gxGroupoid H X ≤ gxGroupoid G X :=
  gxGroupoid_mono fun g => ⟨g, fun _ => rfl⟩

/-- **Monotonicity in an open `X' ⊆ X`** (plan F2): let `ι : X' → X` be an open embedding (e.g.
the inclusion of an open set, or a hemisphere chart `ℝⁿ ≃ H ⊂ S(n)`) through which `G'` acts as `G`
does, `ι (g • p) = φ g • ι p` for a hom `φ : G' →* G`. Then every element `f` of `gxGroupoid G' X'`,
transported to `X` as `ι ∘ f ∘ ι⁻¹` (on `ι(X')`), lies in `gxGroupoid G X`. -/
theorem transport_mem_gxGroupoid {G' : Type w'} {X' : Type*} [TopologicalSpace X'] [Nonempty X']
    [Group G'] [MulAction G' X'] [ContinuousConstSMul G' X'] {ι : X' → X} (hι : IsOpenEmbedding ι)
    (φ : G' →* G) (hφ : ∀ (g : G') (p : X'), ι (g • p) = φ g • ι p)
    {f : OpenPartialHomeomorph X' X'} (hf : f ∈ gxGroupoid G' X') :
    ((hι.toOpenPartialHomeomorph ι).symm.trans f).trans (hι.toOpenPartialHomeomorph ι) ∈
      gxGroupoid G X := by
  set e := hι.toOpenPartialHomeomorph ι with he
  have key : ∀ f : OpenPartialHomeomorph X' X',
      (∀ p ∈ f.source, ∃ g : G', f =ᶠ[𝓝 p] fun y => g • y) →
      ∀ x ∈ ((e.symm.trans f).trans e).source, ∃ g : G,
        ((e.symm.trans f).trans e : X → X) =ᶠ[𝓝 x] fun y => g • y := by
    intro f hf x hx
    simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      mem_inter_iff, mem_preimage] at hx
    obtain ⟨⟨hxt, hxf⟩, -⟩ := hx
    obtain ⟨g, hg⟩ := hf _ hxf
    refine ⟨φ g, ?_⟩
    have ht : e.target ∈ 𝓝 x := e.open_target.mem_nhds hxt
    filter_upwards [(e.continuousAt_symm hxt).eventually hg, ht] with y hy hyt
    simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply] at hy ⊢
    rw [hy, he, IsOpenEmbedding.toOpenPartialHomeomorph_apply, hφ]
    congr 1
    rw [← he]
    have := e.right_inv hyt
    rwa [he, IsOpenEmbedding.toOpenPartialHomeomorph_apply] at this
  rw [mem_gxGroupoid_iff] at hf ⊢
  refine ⟨key f hf.1, ?_⟩
  have hsymm : ((e.symm.trans f).trans e).symm = (e.symm.trans f.symm).trans e := by
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm,
      OpenPartialHomeomorph.trans_assoc]
  intro x hx
  have hx' : x ∈ ((e.symm.trans f).trans e).symm.source := by
    rwa [OpenPartialHomeomorph.symm_source]
  rw [hsymm] at hx' ⊢
  exact key f.symm (fun p hp => hf.2 p hp) x hx'

/-- Every element of `G`, as a homeomorphism of `X`, is in `gxGroupoid G X`. -/
theorem smul_mem_gxGroupoid (g : G) :
    (Homeomorph.smul g : X ≃ₜ X).toOpenPartialHomeomorph ∈ gxGroupoid G X := by
  rw [mem_gxGroupoid_iff]
  refine ⟨fun x _ => ⟨g, Eventually.of_forall fun _ => rfl⟩, fun x _ => ⟨g⁻¹, ?_⟩⟩
  exact Eventually.of_forall fun y => rfl

end Groupoid

end Benzecri
