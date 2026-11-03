import BenzecriScaffold.Cone.Basic
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.FiberBundle.Trivialization

/-!
# `BenzecriScaffold.Cone.Base` — the base `B = V/ℝ⁺` of an affine conical manifold (§ 2, Prop. 2)

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 1 § 2, journal p. 240; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch1.tex`, checked against the scan (PDF p. 13).
Package WP-45n (wave 3, layer L5). Indexing: the cone has dimension `n + 1` (model
`RnO (n + 1) = ℝⁿ⁺¹ − {O}`, group `GU(n+1, ℝ)`), its base dimension `n` (model `S n = S(ℝⁿ⁺¹)`,
group `GSR n`), i.e. Benzécri's `n` and `n − 1`.

* **`bzprop:c1s2p2_base_cone`** — `benzecri1960_ch1.tex:537` (Prop. 2, l.537–543, p. 240):
  `B = V/ℝ⁺` is `Benzecri.ConeBase n V` (the orbit quotient of Déf. 3's action, quotient topology);
  the quotient of a cone chart `f : U → C` is the base chart `ConeBase.baseChart` `p(U) → s(C)`,
  `p(m) ↦ s(f(m))` (`baseChart_mk`); their transitions are locally in `GS(n, ℝ)`
  (`baseChart_symm_trans_mem`: `f' = g ∘ f` gives `p(f') = i⁻¹(g) ∘ p(f)`), so they form a locally
  projective structure (`ConeBase.chartedSpace`, `ConeBase.hasGroupoid`). The jet `p(j)` of a jet
  `j ∈ J₁(V)` « par passage au quotient » is `ConeBase.pJet` (well defined: `jet_baseChart_eq`;
  every `j ∈ J₁(V)` is the jet of a cone chart, `exists_isConeChart_jet_eq`), and **the structure is
  the unique one in which every `p(j)` is a projective jet** (`ConeBase.existsUnique_baseStructure`;
  in chart form `existsUnique_baseStructure_charts`).
* `bzdef:c1s2d3_homotheties_positives` — `benzecri1960_ch1.tex:523` (Déf. 3, p. 240), the sentence
  « $V$ est ainsi munie d'une structure d'espace fibré $\R^+$-principal »: the action is free
  (`Cone/Basic`) and `V → B` has an `ℝ₊*`-equivariant local trivialisation over every base chart
  (`ConeBase.coneTrivialization`, `coneTrivialization_posSMul`, `exists_coneTrivialization`). Not
  marked here (Déf. 3 is spread over `Cone/Basic`, this file and `Cone/Section`; see the latter).

Also (groundwork for wave 4's `F⁻¹`): the projection is an open quotient map
(`isOpenQuotientMap_mk`); **Hausdorff criterion** (papers/bbs NOTES-3+1 N7–N8): if the action of
`ℝ₊*` is proper, `B` is Hausdorff (`t2Space_of_properSMul`); the base of a conical morphism
`ConeBase.map` is a projective morphism (`isGXMorphism_map`), functorially (`map_id`, `map_comp`).

> **Prop. 2.** Sur le quotient $B=V/\R^+$, appelé *base* de l'espace fibré $V$, est définie
> canoniquement une structure localement projective : soit $j$ un jet de $J_1(V)$, on en déduit par
> passage au quotient par le groupe des homothéties positives, un jet de $B$ dans $S(n-1)$, que nous
> noterons $p(j)$ : la structure localement projective de $B$ est l'unique structure telle que les
> $p(j)$ soient des jets projectifs de $B$.
>
> (Déf. 3) $V$ est ainsi munie d'une structure d'espace fibré $\R^+$-principal […].

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `V` an affine conical manifold (Déf. 2) | ✓ carried: `[ChartedSpace (RnO (n+1)) V] [HasConeCharts (n+1) V]`, and `[HasGroupoid V (coneGroupoid (n+1))]` where the jets `J₁(V)` are used |
| `V` a « variété »: Hausdorff | ✓ carried: `[T2Space V]`, needed by Déf. 3's action (`Cone/Basic`, SCOPE) |
| « structure localement projective » on `B` | ✓ carried: `ChartedSpace (S n)` with `HasGroupoid (projGroupoid n)`, the strict library's notion (Déf. 12, which carries no Hausdorffness) |
| « l'unique structure » | ✓ carried: any `(GS(n), S(n))`-structure in which every `p(j)` is a projective jet has the same maximal atlas |
| `B` a « variété » (Hausdorff) | not asserted: not claimed by Prop. 2; sufficient condition `t2Space_of_properSMul` (SCOPE) |

## SCOPE (disclosed)

* **Hausdorffness of `B`.** Prop. 2 does not claim it and nothing here proves it from `V` Hausdorff;
  the sufficient condition proved is properness of the action (`t2Space_of_properSMul`, Mathlib's
  `ProperSMul`). Whether `V` Hausdorff (with 3°) forces `B` Hausdorff is left open (REPORT
  `questions`): it matters for wave 4 (the functor `F` lands in Hausdorff cones only over Hausdorff
  `B`) and for the section of `Cone/Section`, for which `B` Hausdorff is necessary.
* The quotient is by the whole group `ℝ₊*` (N7's (B1) radiant cone): no quotient by a subgroup or
  by an element with a radial cocycle is taken here (N8's warning applies to those, § 3).
* The base charts are built from cone charts only (charts onto open cones); a general compatible
  chart of `V` is a `GU`-translate of a cone chart near each point, which is how every `p(j)` is
  reached.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Filter Topology Bundle

namespace Benzecri

universe u

/-! ### Radial coordinate and unit representatives -/

section Radial

variable {X : Type*} [TopologicalSpace X]

/-- A map into `ℝ₊*` is continuous iff its real values are. -/
theorem continuous_RPos_iff {f : X → RPos} : Continuous f ↔ Continuous fun x => ((f x : ℝˣ) : ℝ) :=
  (Units.isEmbedding_val₀.comp IsEmbedding.subtypeVal).continuous_iff

variable {n : ℕ}

/-- The radial coordinate `‖v‖ ∈ ℝ₊*` of `v ∈ ℝⁿ − {O}` (sup norm). -/
def radius (v : RnO n) : RPos := Punctured.posUnit ‖v.val‖ (norm_pos_iff.2 v.val_ne_zero)

@[simp] theorem coe_radius (v : RnO n) : ((radius v : ℝˣ) : ℝ) = ‖v.val‖ := rfl

theorem radius_smul (c : RPos) (v : RnO n) : radius (c • v) = c * radius v := by
  refine Subtype.ext (Units.ext ?_)
  simp only [coe_radius, Punctured.val_smul_pos, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Punctured.pos c)]
  rfl

theorem continuous_radius : Continuous (radius : RnO n → RPos) :=
  continuous_RPos_iff.2 (continuous_norm.comp Punctured.continuous_val)

/-- The unit representative `u(x) ∈ ℝⁿ⁺¹ − {O}` of `x ∈ S(n)`, `‖u(x)‖ = 1`. -/
def unitRep (x : S n) : RnO (n + 1) :=
  Punctured.mk (Sphere.homeomorphUnitSphere x : Fin (n + 1) → ℝ)
    (Sphere.ne_zero_of_mem_unitSphere _)

theorem continuous_unitRep : Continuous (unitRep : S n → RnO (n + 1)) := by
  refine continuous_induced_rng.2 ?_
  change Continuous fun x : S n => ((Sphere.homeomorphUnitSphere x : _) : Fin (n + 1) → ℝ)
  exact continuous_subtype_val.comp Sphere.homeomorphUnitSphere.continuous

@[simp] theorem toSphere_unitRep (x : S n) : Punctured.toSphere (unitRep x) = x := by
  conv_rhs => rw [← Sphere.homeomorphUnitSphere.symm_apply_apply x]
  rfl

theorem unitRep_toSphere (v : RnO (n + 1)) : unitRep (Punctured.toSphere v) = (radius v)⁻¹ • v := by
  apply Punctured.ext
  simp only [unitRep, Punctured.val_mk, Punctured.toSphere, Sphere.homeomorphUnitSphere_mk,
    Punctured.val_smul_pos]
  rfl

@[simp] theorem radius_unitRep (x : S n) : radius (unitRep x) = 1 := by
  refine Subtype.ext (Units.ext ?_)
  simp only [coe_radius, unitRep, Punctured.val_mk]
  exact norm_eq_of_mem_sphere _

end Radial

/-! ### The base `B = V/ℝ⁺` -/

variable {n : ℕ} {V : Type u} [TopologicalSpace V] [ChartedSpace (RnO (n + 1)) V]
  [HasConeCharts (n + 1) V] [T2Space V]

variable (n V) in
/-- The orbit relation of the positive homotheties of Déf. 3. -/
abbrev coneRel : Setoid V := @MulAction.orbitRel RPos V _ (coneMulAction (n + 1) V)

variable (n V) in
/-- **The base `B = V/ℝ⁺`** of an affine conical `(n+1)`-manifold (Prop. 2, « le quotient
$B=V/\R^+$, appelé *base* de l'espace fibré $V$ »), with the quotient topology. -/
def ConeBase : Type u := Quotient (coneRel n V)

namespace ConeBase

instance : TopologicalSpace (ConeBase n V) := instTopologicalSpaceQuotient

/-- The projection `V → B`. -/
def mk (m : V) : ConeBase n V := Quotient.mk (coneRel n V) m

theorem rel_iff {m m' : V} : coneRel n V m m' ↔ ∃ c : RPos, posSMul (n + 1) c m' = m := by
  letI := coneMulAction (n + 1) V
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  rfl

theorem mk_eq_mk_iff {m m' : V} : mk (n := n) m = mk m' ↔ ∃ c : RPos, posSMul (n + 1) c m' = m :=
  Quotient.eq.trans rel_iff

@[simp] theorem mk_posSMul (c : RPos) (m : V) : mk (n := n) (posSMul (n + 1) c m) = mk m :=
  mk_eq_mk_iff.2 ⟨c, rfl⟩

theorem mk_surjective : Function.Surjective (mk : V → ConeBase n V) := Quotient.mk_surjective

/-- **The projection `V → B` is an open quotient map** (the action of `ℝ₊*` is by
homeomorphisms). -/
theorem isOpenQuotientMap_mk : IsOpenQuotientMap (mk : V → ConeBase n V) := by
  letI := coneMulAction (n + 1) V
  haveI := continuousSMul_cone (n := n + 1) (V := V)
  exact MulAction.isOpenQuotientMap_quotientMk

theorem continuous_mk : Continuous (mk : V → ConeBase n V) := isOpenQuotientMap_mk.continuous

/-- **Hausdorff criterion for the base** (cf. papers/bbs NOTES-3+1 N7–N8): if the action of `ℝ₊*`
on `V` is proper (Bourbaki), `B` is Hausdorff. -/
theorem t2Space_of_properSMul (h : @ProperSMul RPos V _ _ _ (coneMulAction (n + 1) V)) :
    T2Space (ConeBase n V) := by
  letI := coneMulAction (n + 1) V
  exact t2Space_quotient_mulAction_of_properSMul

end ConeBase

/-! ### The charts of the base: quotients of the cone charts -/

namespace ConeBase

variable {e : OpenPartialHomeomorph V (RnO (n + 1))}

open scoped Classical in
/-- The base chart of a cone chart `f`, as a function on `B`: `p(m) ↦ s(f(m))` (`s` the projection
`ℝⁿ⁺¹ − {O} → S(n)`), « par passage au quotient par le groupe des homothéties positives ». -/
def baseFun (he : IsConeChart (n + 1) e) : ConeBase n V → S n :=
  Quotient.lift (fun m => if m ∈ e.source then Punctured.toSphere (e m) else Classical.arbitrary _)
    fun a b hab => by
      obtain ⟨c, rfl⟩ := rel_iff.1 hab
      simp only [he.smul_mem_source_iff]
      split_ifs with hb
      · rw [he.map_smul hb, Punctured.toSphere_smul_pos]
      · rfl

open scoped Classical in
theorem baseFun_mk (he : IsConeChart (n + 1) e) {m : V} (hm : m ∈ e.source) :
    baseFun he (mk m) = Punctured.toSphere (e m) := by
  show (if m ∈ e.source then _ else _) = _
  rw [if_pos hm]

open scoped Classical in
/-- The inverse of the base chart: `s(w) ↦ p(f⁻¹(w))` for `w` in the open cone `f(U)`. -/
def baseInv (he : IsConeChart (n + 1) e) : S n → ConeBase n V :=
  Sphere.lift (fun w => if Punctured.ofSubtype w ∈ e.target then mk (e.symm (Punctured.ofSubtype w))
      else mk (e.symm (Classical.arbitrary (RnO (n + 1)))))
    fun v w hvw => by
      have hvw' : Punctured.toSphere (Punctured.ofSubtype v) =
          Punctured.toSphere (Punctured.ofSubtype w) :=
        (Sphere.mk_eq_mk_iff v.2 w.2).2 hvw
      obtain ⟨c, hc⟩ := Punctured.toSphere_eq_toSphere_iff.1 hvw'
      have hiff : Punctured.ofSubtype w ∈ e.target ↔ Punctured.ofSubtype v ∈ e.target := by
        rw [← hc]
        refine ⟨fun h => ?_, fun h => he.smul_mem_target h c⟩
        have := he.smul_mem_target h c⁻¹
        rwa [inv_smul_smul] at this
      by_cases hv : Punctured.ofSubtype v ∈ e.target
      · have hw := hiff.2 hv
        simp only [if_pos hv, if_pos hw]
        rw [← hc, he.symm_smul hv, mk_posSMul]
      · have hw : Punctured.ofSubtype w ∉ e.target := fun h => hv (hiff.1 h)
        simp only [if_neg hv, if_neg hw]

open scoped Classical in
theorem baseInv_toSphere (he : IsConeChart (n + 1) e) {w : RnO (n + 1)} (hw : w ∈ e.target) :
    baseInv he (Punctured.toSphere w) = mk (e.symm w) := by
  have : baseInv he (Punctured.toSphere w) = if Punctured.ofSubtype (Punctured.toSubtype w) ∈ e.target
      then mk (e.symm (Punctured.ofSubtype (Punctured.toSubtype w)))
      else mk (e.symm (Classical.arbitrary (RnO (n + 1)))) := rfl
  rw [this, Punctured.ofSubtype_toSubtype, if_pos hw]

/-- **The base chart** `p(f)` of a cone chart `f : U → C` (Prop. 2): the open partial homeomorphism
`B ⊇ p(U) → s(C) ⊆ S(n)`, `p(m) ↦ s(f(m))`. -/
def baseChart (he : IsConeChart (n + 1) e) : OpenPartialHomeomorph (ConeBase n V) (S n) where
  toFun := baseFun he
  invFun := baseInv he
  source := mk '' e.source
  target := Punctured.toSphere '' e.target
  map_source' := by
    rintro _ ⟨m, hm, rfl⟩
    exact ⟨e m, e.map_source hm, (baseFun_mk he hm).symm⟩
  map_target' := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨e.symm w, e.map_target hw, (baseInv_toSphere he hw).symm⟩
  left_inv' := by
    rintro _ ⟨m, hm, rfl⟩
    rw [baseFun_mk he hm, baseInv_toSphere he (e.map_source hm), e.left_inv hm]
  right_inv' := by
    rintro _ ⟨w, hw, rfl⟩
    rw [baseInv_toSphere he hw, baseFun_mk he (e.map_target hw), e.right_inv hw]
  open_source := isOpenQuotientMap_mk.isOpenMap _ e.open_source
  open_target := Punctured.isOpenQuotientMap_toSphere.isOpenMap _ e.open_target
  continuousOn_toFun := by
    rintro _ ⟨m, hm, rfl⟩
    refine ContinuousAt.continuousWithinAt ?_
    rw [← isOpenQuotientMap_mk.continuousAt_comp_iff]
    refine (Punctured.continuous_toSphere.continuousAt.comp (e.continuousAt hm)).congr ?_
    filter_upwards [e.open_source.mem_nhds hm] with y hy
    exact (baseFun_mk he hy).symm
  continuousOn_invFun := by
    rintro _ ⟨w, hw, rfl⟩
    refine ContinuousAt.continuousWithinAt ?_
    rw [← Punctured.isOpenQuotientMap_toSphere.continuousAt_comp_iff]
    refine (continuous_mk.continuousAt.comp (e.continuousAt_symm hw)).congr ?_
    filter_upwards [e.open_target.mem_nhds hw] with y hy
    exact (baseInv_toSphere he hy).symm

theorem baseChart_source (he : IsConeChart (n + 1) e) : (baseChart he).source = mk '' e.source :=
  rfl

theorem baseChart_target (he : IsConeChart (n + 1) e) :
    (baseChart he).target = Punctured.toSphere '' e.target := rfl

/-- **The base chart in coordinates**: `p(f)(p(m)) = s(f(m))`. -/
theorem baseChart_mk (he : IsConeChart (n + 1) e) {m : V} (hm : m ∈ e.source) :
    baseChart he (mk m) = Punctured.toSphere (e m) :=
  baseFun_mk he hm

theorem baseChart_symm_toSphere (he : IsConeChart (n + 1) e) {w : RnO (n + 1)} (hw : w ∈ e.target) :
    (baseChart he).symm (Punctured.toSphere w) = mk (e.symm w) :=
  baseInv_toSphere he hw

/-- The source of a cone chart is saturated: `p(m) ∈ p(U) ↔ m ∈ U`. -/
theorem mk_mem_baseChart_source_iff (he : IsConeChart (n + 1) e) {m : V} :
    mk m ∈ (baseChart he).source ↔ m ∈ e.source := by
  refine ⟨?_, fun hm => ⟨m, hm, rfl⟩⟩
  rintro ⟨m', hm', h⟩
  obtain ⟨c, rfl⟩ := mk_eq_mk_iff.1 h.symm
  exact he.smul_mem_source hm' c

/-- The `ℝ₊*`-saturation of a neighbourhood: the image of a neighbourhood of `m` is a
neighbourhood of `p(m)`. -/
theorem mk_image_mem_nhds {m : V} {t : Set V} (ht : t ∈ 𝓝 m) : mk '' t ∈ 𝓝 (mk (n := n) m) :=
  isOpenQuotientMap_mk.isOpenMap.image_mem_nhds ht

variable {e' : OpenPartialHomeomorph V (RnO (n + 1))}

/-- **The transitions of the base charts are locally in `GS(n, ℝ)`**: near a common point, if
`f' = g ∘ f` with `g ∈ GU(n+1, ℝ)`, then `p(f') = i⁻¹(g) ∘ p(f)`, `i⁻¹(g) ∈ GS(n, ℝ)` the class of
`g`. -/
theorem baseChart_symm_trans_mem (he : IsConeChart (n + 1) e) (he' : IsConeChart (n + 1) e') :
    (baseChart he).symm.trans (baseChart he') ∈ projGroupoid n := by
  refine symm_trans_mem_gxGroupoid fun b hb => ?_
  obtain ⟨⟨m, hm, rfl⟩, hb'⟩ := hb
  have hm' : m ∈ e'.source := (mk_mem_baseChart_source_iff he').1 hb'
  obtain ⟨g, hg⟩ := eventually_smul_eq_of_mem_maximalAtlas he.1 he'.1 hm hm'
  refine ⟨(QuotientGroup.mk (g : GLR (n + 1)) : GSR n), ?_⟩
  have ht : {y | e' y = g • e y ∧ y ∈ e.source ∧ y ∈ e'.source} ∈ 𝓝 m :=
    Filter.Eventually.and hg (Filter.Eventually.and (e.open_source.mem_nhds hm)
      (e'.open_source.mem_nhds hm'))
  filter_upwards [mk_image_mem_nhds ht] with z hz
  obtain ⟨y, ⟨hy, hys, hys'⟩, rfl⟩ := hz
  rw [baseChart_mk he hys, baseChart_mk he' hys', hy, GSE.mk_smul]
  rfl

end ConeBase

/-! ### The locally projective structure of the base (Prop. 2) -/

namespace ConeBase

/-- **The atlas of the base**: the base charts `p(f)` of all cone charts `f` of `V`. -/
def baseAtlas : Set (OpenPartialHomeomorph (ConeBase n V) (S n)) :=
  {φ | ∃ (e : OpenPartialHomeomorph V (RnO (n + 1))) (he : IsConeChart (n + 1) e), φ = baseChart he}

/-- **The charted space of the base** (Prop. 2): the atlas of the base charts; the chart at
`b = p(m)` is the base chart of the chosen cone chart at a representative of `b`. -/
instance chartedSpace : ChartedSpace (S n) (ConeBase n V) where
  atlas := baseAtlas
  chartAt b := baseChart (isConeChart_coneChartAt (n := n + 1) (Quotient.out b))
  mem_chart_source b := ⟨Quotient.out b, mem_coneChartAt_source _, Quotient.out_eq b⟩
  chart_mem_atlas _ := ⟨_, _, rfl⟩

/-- **Prop. 2, the structure**: the base is a locally projective `n`-manifold. -/
instance hasGroupoid : HasGroupoid (ConeBase n V) (projGroupoid n) where
  compatible := by
    rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
    exact baseChart_symm_trans_mem he he'

/-- Every base chart is a compatible chart of the base. -/
theorem baseChart_mem_maximalAtlas {e : OpenPartialHomeomorph V (RnO (n + 1))}
    (he : IsConeChart (n + 1) e) :
    baseChart he ∈ (projGroupoid n).maximalAtlas (ConeBase n V) :=
  (projGroupoid n).subset_maximalAtlas ⟨e, he, rfl⟩

/-- **Prop. 2 in chart form** (`bzprop:c1s2p2_base_cone`): the base charts `p(f)` of the cone
charts `f` of `V` are compatible with the locally projective structure of `B`, and it is the only
one with this property (any `(GS(n), S(n))`-structure on `B` for which every `p(f)` is compatible
has the same maximal atlas). -/
theorem existsUnique_baseStructure_charts :
    (∀ (e : OpenPartialHomeomorph V (RnO (n + 1))) (he : IsConeChart (n + 1) e),
      baseChart he ∈ (projGroupoid n).maximalAtlas (ConeBase n V)) ∧
    ∀ cs : ChartedSpace (S n) (ConeBase n V), @HasGroupoid _ _ _ _ cs (projGroupoid n) →
      (∀ (e : OpenPartialHomeomorph V (RnO (n + 1))) (he : IsConeChart (n + 1) e),
        baseChart he ∈ @StructureGroupoid.maximalAtlas _ _ _ _ cs (projGroupoid n)) →
      @StructureGroupoid.maximalAtlas _ _ _ _ cs (projGroupoid n) =
        @StructureGroupoid.maximalAtlas _ _ _ _ chartedSpace (projGroupoid n) := by
  refine ⟨fun e he => baseChart_mem_maximalAtlas he, fun cs hcs hcs' => ?_⟩
  let f : {e : OpenPartialHomeomorph V (RnO (n + 1)) // IsConeChart (n + 1) e} →
      OpenPartialHomeomorph (ConeBase n V) (S n) := fun e => baseChart e.2
  exact (maximalAtlas_eq_of_common_cover (G := GSR n) (h := hasGroupoid) (h' := hcs) chartedSpace
    cs f
    (fun b => ⟨⟨_, isConeChart_coneChartAt (n := n + 1) (Quotient.out b)⟩,
      ⟨Quotient.out b, mem_coneChartAt_source _, Quotient.out_eq b⟩⟩)
    (fun e => baseChart_mem_maximalAtlas e.2) (fun e => hcs' _ e.2)).symm

end ConeBase

/-! ### Prop. 2 in the paper's form: the jets `p(j)` -/

namespace ConeBase

variable {e e' : OpenPartialHomeomorph V (RnO (n + 1))}

/-- **`p(j)` is well defined**: two cone charts with the same jet at `m` have base charts with the
same jet at `p(m)`. -/
theorem jet_baseChart_eq (he : IsConeChart (n + 1) e) (he' : IsConeChart (n + 1) e') {m : V}
    (hm : m ∈ e.source) (hm' : m ∈ e'.source) (h : jet m e = jet m e') :
    jet (mk m) (baseChart he) = jet (mk m) (baseChart he') := by
  rw [jet_eq_jet_iff] at h ⊢
  have ht : {y | e y = e' y ∧ y ∈ e.source ∧ y ∈ e'.source} ∈ 𝓝 m :=
    Filter.Eventually.and h (Filter.Eventually.and (e.open_source.mem_nhds hm)
      (e'.open_source.mem_nhds hm'))
  filter_upwards [mk_image_mem_nhds ht] with z hz
  obtain ⟨y, ⟨hy, hys, hys'⟩, rfl⟩ := hz
  rw [baseChart_mk he hys, baseChart_mk he' hys', hy]

open scoped Classical in
/-- **The jet `p(j)` of `B` into `S(n)`** deduced from a jet `j` of `V` into `ℝⁿ⁺¹ − {O}` « par
passage au quotient par le groupe des homothéties positives » (Prop. 2): for `j` the jet at `m` of
a cone chart `f`, `p(j)` is the jet at `p(m)` of the base chart `p(f)` (independent of `f`,
`jet_baseChart_eq`); every `j ∈ J₁(V)` is of this form (`exists_isConeChart_jet_eq`). A junk value
otherwise. -/
def pJet (j : Jet V (RnO (n + 1))) : Jet (ConeBase n V) (S n) :=
  if h : ∃ (e : OpenPartialHomeomorph V (RnO (n + 1))) (_ : IsConeChart (n + 1) e),
      j.1 ∈ e.source ∧ jet j.1 e = j then
    jet (mk j.1) (baseChart h.choose_spec.choose)
  else jet (mk j.1) fun _ => Classical.arbitrary (S n)

theorem pJet_jet (he : IsConeChart (n + 1) e) {m : V} (hm : m ∈ e.source) :
    pJet (jet m e) = jet (mk m) (baseChart he) := by
  have h : ∃ (e' : OpenPartialHomeomorph V (RnO (n + 1))) (he' : IsConeChart (n + 1) e'),
      (jet m e).1 ∈ e'.source ∧ jet (jet m e).1 e' = jet m e := ⟨e, he, hm, rfl⟩
  rw [pJet, dif_pos h]
  exact jet_baseChart_eq _ he h.choose_spec.choose_spec.1 hm h.choose_spec.choose_spec.2

variable [HasGroupoid V (coneGroupoid (n + 1))]

/-- For a `(GS(n), S(n))`-structure on `B`: all the `p(j)`, `j ∈ J₁(V)`, are projective jets iff
all the base charts `p(f)` are compatible. -/
theorem forall_pJet_mem_iff (cs : ChartedSpace (S n) (ConeBase n V))
    (hcs : @HasGroupoid _ _ _ _ cs (projGroupoid n)) :
    (∀ j ∈ jets (GUR (n + 1)) (RnO (n + 1)) V, pJet j ∈ @jets (GSR n) (S n) _ _ _ _ _ _ cs) ↔
      ∀ (e : OpenPartialHomeomorph V (RnO (n + 1))) (he : IsConeChart (n + 1) e),
        baseChart he ∈ @StructureGroupoid.maximalAtlas _ _ _ _ cs (projGroupoid n) := by
  constructor
  · intro h e he
    rw [@mem_maximalAtlas_iff_jets _ _ _ _ (GSR n) _ _ _ cs hcs]
    rintro _ ⟨m, hm, rfl⟩
    rw [← pJet_jet he hm]
    exact h _ (jet_mem_jets he.1 hm)
  · rintro h ⟨x, γ⟩ hj
    obtain ⟨e, he, hx, rfl⟩ := exists_isConeChart_jet_eq (n := n + 1) hj
    change pJet (jet x e) ∈ _
    rw [pJet_jet he hx]
    exact @jet_mem_jets _ _ _ _ (GSR n) _ _ _ cs _ (h e he) _ ⟨x, hx, rfl⟩

/-- **Prop. 2** (`bzprop:c1s2p2_base_cone`): « Sur le quotient $B=V/\R^+$ … est définie
canoniquement une structure localement projective : soit $j$ un jet de $J_1(V)$, on en déduit par
passage au quotient … un jet de $B$ dans $S(n-1)$, que nous noterons $p(j)$ : la structure
localement projective de $B$ est l'unique structure telle que les $p(j)$ soient des jets projectifs
de $B$. » For the structure `ConeBase.chartedSpace`/`hasGroupoid`, every `p(j)` is a projective jet,
and any `(GS(n), S(n))`-structure on `B` in which every `p(j)` is a projective jet has the same
maximal atlas. -/
theorem existsUnique_baseStructure :
    (∀ j ∈ jets (GUR (n + 1)) (RnO (n + 1)) V, pJet j ∈ jets (GSR n) (S n) (ConeBase n V)) ∧
    ∀ cs : ChartedSpace (S n) (ConeBase n V), @HasGroupoid _ _ _ _ cs (projGroupoid n) →
      (∀ j ∈ jets (GUR (n + 1)) (RnO (n + 1)) V, pJet j ∈ @jets (GSR n) (S n) _ _ _ _ _ _ cs) →
      @StructureGroupoid.maximalAtlas _ _ _ _ cs (projGroupoid n) =
        @StructureGroupoid.maximalAtlas _ _ _ _ chartedSpace (projGroupoid n) := by
  refine ⟨(forall_pJet_mem_iff chartedSpace hasGroupoid).2 fun e he =>
    baseChart_mem_maximalAtlas he, fun cs hcs h => ?_⟩
  exact existsUnique_baseStructure_charts.2 cs hcs ((forall_pJet_mem_iff cs hcs).1 h)

end ConeBase

/-! ### `V → B` is a principal `ℝ₊*`-bundle (Déf. 3) -/

namespace ConeBase

variable {e : OpenPartialHomeomorph V (RnO (n + 1))}

theorem unitRep_baseChart_mem_target (he : IsConeChart (n + 1) e) {b : ConeBase n V}
    (hb : b ∈ (baseChart he).source) : unitRep (baseChart he b) ∈ e.target := by
  obtain ⟨m, hm, rfl⟩ := hb
  rw [baseChart_mk he hm, unitRep_toSphere]
  exact he.smul_mem_target (e.map_source hm) _

/-- **The local trivialisation of `V → B` over the domain of a base chart**: `m ↦ (p(m), ‖f(m)‖)`,
with inverse `(b, λ) ↦ λ f⁻¹(u(p(f)(b)))`, `u` the unit representative. It is
`ℝ₊*`-equivariant (`coneTrivialization_posSMul`): « $V$ est ainsi munie d'une structure d'espace
fibré $\R^+$-principal ». -/
def coneTrivialization (he : IsConeChart (n + 1) e) :
    Trivialization RPos (mk : V → ConeBase n V) where
  toFun m := (mk m, radius (e m))
  invFun p := posSMul (n + 1) p.2 (e.symm (unitRep (baseChart he p.1)))
  source := mk ⁻¹' (baseChart he).source
  target := (baseChart he).source ×ˢ univ
  map_source' _ hm := ⟨hm, trivial⟩
  map_target' p hp := by
    show mk (posSMul (n + 1) p.2 (e.symm (unitRep (baseChart he p.1)))) ∈ (baseChart he).source
    rw [mk_posSMul]
    exact ⟨_, e.map_target (unitRep_baseChart_mem_target he hp.1), rfl⟩
  left_inv' m hm := by
    have hm' : m ∈ e.source := (mk_mem_baseChart_source_iff he).1 hm
    show posSMul (n + 1) (radius (e m)) (e.symm (unitRep (baseChart he (mk m)))) = m
    rw [baseChart_mk he hm', unitRep_toSphere, he.symm_smul (e.map_source hm'), e.left_inv hm',
      ← posSMul_mul, mul_inv_cancel, posSMul_one]
  right_inv' p hp := by
    obtain ⟨b, c⟩ := p
    have hb : b ∈ (baseChart he).source := hp.1
    have hw := unitRep_baseChart_mem_target he hb
    have hsrc : e.symm (unitRep (baseChart he b)) ∈ e.source := e.map_target hw
    show (mk (posSMul (n + 1) c (e.symm (unitRep (baseChart he b)))),
      radius (e (posSMul (n + 1) c (e.symm (unitRep (baseChart he b)))))) = (b, c)
    refine Prod.ext ?_ ?_
    · rw [mk_posSMul]
      refine (baseChart he).injOn ⟨_, hsrc, rfl⟩ hb ?_
      rw [baseChart_mk he hsrc, e.right_inv hw, toSphere_unitRep]
    · show radius (e (posSMul (n + 1) c (e.symm (unitRep (baseChart he b))))) = c
      rw [he.map_smul hsrc, e.right_inv hw, radius_smul, radius_unitRep, mul_one]
  open_source := (baseChart he).open_source.preimage continuous_mk
  open_target := (baseChart he).open_source.prod isOpen_univ
  continuousOn_toFun := by
    refine continuous_mk.continuousOn.prodMk ?_
    refine (continuous_radius.comp_continuousOn e.continuousOn).mono fun m hm => ?_
    exact (mk_mem_baseChart_source_iff he).1 hm
  continuousOn_invFun := by
    have h1 : ContinuousOn (fun b => e.symm (unitRep (baseChart he b))) (baseChart he).source :=
      e.continuousOn_symm.comp (continuous_unitRep.comp_continuousOn (baseChart he).continuousOn)
        fun b hb => unitRep_baseChart_mem_target he hb
    have h2 : ContinuousOn (fun p : ConeBase n V × RPos =>
        (p.2, e.symm (unitRep (baseChart he p.1)))) ((baseChart he).source ×ˢ univ) :=
      continuous_snd.continuousOn.prodMk (h1.comp continuous_fst.continuousOn fun p hp => hp.1)
    exact (continuous_posSMul (n := n + 1) (V := V)).comp_continuousOn h2
  baseSet := (baseChart he).source
  open_baseSet := (baseChart he).open_source
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

theorem coneTrivialization_apply (he : IsConeChart (n + 1) e) (m : V) :
    coneTrivialization he m = (mk m, radius (e m)) := rfl

/-- **The trivialisations are `ℝ₊*`-equivariant**: `T(λm) = (p(m), λ · T(m)₂)`. -/
theorem coneTrivialization_posSMul (he : IsConeChart (n + 1) e) {m : V} (hm : m ∈ e.source)
    (c : RPos) :
    coneTrivialization he (posSMul (n + 1) c m) =
      ((coneTrivialization he m).1, c * (coneTrivialization he m).2) := by
  simp only [coneTrivialization_apply, mk_posSMul, he.map_smul hm, radius_smul]

/-- **`V → B` is a principal `ℝ₊*`-bundle** (Déf. 3, « $V$ est ainsi munie d'une structure d'espace
fibré $\R^+$-principal »): the action is free (`eq_one_of_posSMul_eq`) and every point of `B` lies
in the base of an equivariant local trivialisation `coneTrivialization`. -/
theorem exists_coneTrivialization (b : ConeBase n V) :
    ∃ (e : OpenPartialHomeomorph V (RnO (n + 1))) (he : IsConeChart (n + 1) e),
      b ∈ (coneTrivialization he).baseSet :=
  ⟨_, isConeChart_coneChartAt (n := n + 1) (Quotient.out b),
    ⟨Quotient.out b, mem_coneChartAt_source _, Quotient.out_eq b⟩⟩

end ConeBase

/-! ### The base of a morphism (groundwork for § 2's functor `F⁻¹`, wave 4) -/

namespace ConeBase

variable [HasGroupoid V (coneGroupoid (n + 1))] {W : Type*} [TopologicalSpace W]
  [ChartedSpace (RnO (n + 1)) W] [HasGroupoid W (coneGroupoid (n + 1))] [HasConeCharts (n + 1) W]
  [T2Space W] {φ : V → W}

/-- **The base `F⁻¹(φ)` of a conical morphism** `φ : V → W`: `p(m) ↦ p(φ(m))`, well defined since
`φ` commutes with the homotheties (`IsGXMorphism.map_posSMul`). -/
def map (hφ : IsGXMorphism (GUR (n + 1)) (RnO (n + 1)) φ) : ConeBase n V → ConeBase n W :=
  Quotient.lift (fun m => mk (φ m)) fun a b hab => by
    obtain ⟨c, rfl⟩ := rel_iff.1 hab
    show mk (φ (posSMul (n + 1) c b)) = mk (φ b)
    rw [hφ.map_posSMul, mk_posSMul]

theorem map_mk (hφ : IsGXMorphism (GUR (n + 1)) (RnO (n + 1)) φ) (m : V) :
    map hφ (mk m) = mk (φ m) := rfl

theorem continuous_map (hφ : IsGXMorphism (GUR (n + 1)) (RnO (n + 1)) φ) :
    Continuous (map hφ) :=
  isOpenQuotientMap_mk.isQuotientMap.continuous_iff.2 (continuous_mk.comp hφ.continuous)

/-- **`F⁻¹(φ)` is a morphism of the locally projective structures**: in base charts it reads as
`i⁻¹(g) ∈ GS(n, ℝ)` where `φ` reads as `g ∈ GU(n+1, ℝ)`. -/
theorem isGXMorphism_map (hφ : IsGXMorphism (GUR (n + 1)) (RnO (n + 1)) φ) :
    IsGXMorphism (GSR n) (S n) (map hφ) := by
  refine isGXMorphism_of_mem_maximalAtlas (continuous_map hφ) fun b => ?_
  obtain ⟨m, rfl⟩ := mk_surjective b
  set e₁ := coneChartAt (n + 1) m
  set e₂ := coneChartAt (n + 1) (φ m)
  have he₁ := isConeChart_coneChartAt (n := n + 1) m
  have hm₁ := mem_coneChartAt_source (n := n + 1) m
  have he₂ := isConeChart_coneChartAt (n := n + 1) (φ m)
  have hm₂ := mem_coneChartAt_source (n := n + 1) (φ m)
  obtain ⟨g, hg⟩ := hφ.exists_smul_eq_of_mem_maximalAtlas he₁.1 he₂.1 hm₁ hm₂
  refine ⟨baseChart he₁, baseChart_mem_maximalAtlas he₁, baseChart he₂,
    baseChart_mem_maximalAtlas he₂, ⟨m, hm₁, rfl⟩, ⟨φ m, hm₂, rfl⟩,
    (QuotientGroup.mk (g : GLR (n + 1)) : GSR n), ?_⟩
  have ht : {y | e₂ (φ y) = g • e₁ y ∧ y ∈ e₁.source ∧ φ y ∈ e₂.source} ∈ 𝓝 m :=
    Filter.Eventually.and hg (Filter.Eventually.and (e₁.open_source.mem_nhds hm₁)
      (hφ.continuous.continuousAt.preimage_mem_nhds (e₂.open_source.mem_nhds hm₂)))
  filter_upwards [mk_image_mem_nhds ht] with z hz
  obtain ⟨y, ⟨hy, hy1, hy2⟩, rfl⟩ := hz
  rw [map_mk, baseChart_mk he₂ hy2, baseChart_mk he₁ hy1, hy, GSE.mk_smul]
  rfl

/-- `F⁻¹(id) = id`. -/
theorem map_id : map (isGXMorphism_id (G := GUR (n + 1)) (X := RnO (n + 1)) (M := V)) = id := by
  funext b
  obtain ⟨m, rfl⟩ := mk_surjective b
  rfl

/-- `F⁻¹(ψ ∘ φ) = F⁻¹(ψ) ∘ F⁻¹(φ)`. -/
theorem map_comp {U : Type*} [TopologicalSpace U] [ChartedSpace (RnO (n + 1)) U]
    [HasGroupoid U (coneGroupoid (n + 1))] [HasConeCharts (n + 1) U] [T2Space U] {ψ : W → U}
    (hψ : IsGXMorphism (GUR (n + 1)) (RnO (n + 1)) ψ)
    (hφ : IsGXMorphism (GUR (n + 1)) (RnO (n + 1)) φ) :
    map (hψ.comp hφ) = map hψ ∘ map hφ := by
  funext b
  obtain ⟨m, rfl⟩ := mk_surjective b
  rfl

end ConeBase

end Benzecri
