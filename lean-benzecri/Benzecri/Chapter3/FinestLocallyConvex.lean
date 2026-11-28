import Mathlib

/-!
# The finest locally convex topology on a real vector space

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 3 § 1, journal p. 260; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch3.tex`. Target T-bz-c3-facette-ouverte. This
module certifies no label by itself: it builds the topology that Prop. 1
(`bzprop:c3s1p1_facette_ouverte` — `benzecri1960_ch3.tex:141`) puts on the support of a facette,
and that § 5 Prop. 7 uses again; Prop. 1 itself is `Benzecri.Chapter3.FacetteOuverte`.

> **Proposition 1.** Soit $F$ une facette d'un convexe $W$, et soit $L$ la variété linéaire
> support de $F$; $F$ est un ouvert de $L$, supposé muni de sa topologie localement convexe la
> plus fine.
>
> *Démonstration.* Il suffit de démontrer que si $A\in F$, et si $l$ est une sous-variété
> linéaire de dimension finie telle que $A\in l$ et $l\subset L$, alors $A$ est intérieur à
> $l\cap F$ pour la topologie de $l$.

Mathlib at the pin has no « finest locally convex topology ». It is built here as the topology
`Benzecri.finestLC V` of the family of **all** real seminorms on `V`, and the following are proved:

* it is a topological vector space topology (`isTopologicalAddGroup_finestLC`,
  `continuousSMul_finestLC`), locally convex (`locallyConvexSpace_finestLC`), Hausdorff
  (`t2Space_finestLC`);
* it is *the finest* such topology: `finestLC_le` (finer than every locally convex vector
  topology) and `isLeast_finestLC` (the least element, for Mathlib's order on topologies, of the
  set of locally convex vector topologies, i.e. `sInf` of that set, `finestLC_eq_sInf`);
* every linear map out of it into a locally convex space is continuous
  (`continuous_linearMap_finestLC`);
* its neighbourhoods of `x` are the sets containing a seminorm ball (`mem_nhds_finestLC_iff`);
* a **convex** set is open iff it is *algebraically open*: every point is a core point
  (`isOpen_finestLC_iff_core`), iff it is open in every finite-dimensional subspace through each
  of its points, for that subspace's canonical topology (`isOpen_finestLC_iff_finiteDimensional`,
  the printed reduction of Prop. 1);
* it induces on every finite-dimensional subspace its canonical topology
  (`induced_finestLC_eq_moduleTopology`), and on a finite-dimensional space it is the canonical
  topology (`finestLC_eq_moduleTopology`), hence any Hausdorff vector topology there
  (`finestLC_eq_of_finiteDimensional`: on `ℝ × ℝ` the usual one).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| « sa topologie localement convexe la plus fine » | ✓ carried: `finestLC`, with `isLeast_finestLC` proving it is the least (finest) locally convex vector topology |
| a real vector space, any dimension | ✓ carried: `[AddCommGroup V] [Module ℝ V]`, no topology, no dimension hypothesis |

## SCOPE (disclosed)

* The definition is the seminorm topology of all seminorms; that it is the finest locally convex
  topology is a theorem (`isLeast_finestLC`), not the definition. A locally convex topology is
  read as Mathlib's `LocallyConvexSpace ℝ` together with `IsTopologicalAddGroup` and
  `ContinuousSMul ℝ` (a locally convex topological vector space; Hausdorffness is not required,
  and `finestLC` is Hausdorff anyway).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open Set Filter Topology

namespace Benzecri

section FinestLC

variable (V : Type*) [AddCommGroup V] [Module ℝ V]

/-- The family of all real seminorms on `V`, indexed by themselves. -/
def allSeminorms : SeminormFamily ℝ V (Seminorm ℝ V) := fun q => q

/-- **The finest locally convex topology** on a real vector space `V`: the topology of the family
of all seminorms (`isLeast_finestLC` proves it is the finest locally convex vector topology). -/
@[reducible] noncomputable def finestLC : TopologicalSpace V :=
  (allSeminorms V).moduleFilterBasis.topology

theorem withSeminorms_finestLC :
    letI := finestLC V; WithSeminorms (allSeminorms V) := by
  letI := finestLC V; exact ⟨rfl⟩

theorem isTopologicalAddGroup_finestLC : @IsTopologicalAddGroup V (finestLC V) _ := by
  letI := finestLC V; exact (withSeminorms_finestLC V).topologicalAddGroup

theorem continuousSMul_finestLC : @ContinuousSMul ℝ V _ _ (finestLC V) := by
  letI := finestLC V; exact (withSeminorms_finestLC V).continuousSMul

theorem locallyConvexSpace_finestLC : @LocallyConvexSpace ℝ V _ _ _ _ (finestLC V) := by
  letI := finestLC V; exact (withSeminorms_finestLC V).toLocallyConvexSpace

theorem t2Space_finestLC : @T2Space V (finestLC V) := by
  letI := finestLC V
  haveI := isTopologicalAddGroup_finestLC V
  haveI : T1Space V := (withSeminorms_finestLC V).T1_of_separating (fun x hx => by
    obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero ℝ hx
    exact ⟨(normSeminorm ℝ ℝ).comp φ, by simpa [allSeminorms] using hφ⟩)
  infer_instance

variable {V}

/-- Every linear map from `V` with its finest locally convex topology to a locally convex
topological vector space is continuous. -/
theorem continuous_linearMap_finestLC {X : Type*} [AddCommGroup X] [Module ℝ X]
    [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
    (f : V →ₗ[ℝ] X) : Continuous[finestLC V, _] f := by
  letI := finestLC V
  refine WithSeminorms.continuous_of_isBounded (withSeminorms_finestLC V)
    (with_gaugeSeminormFamily (𝕜 := ℝ) (E := X)) f (fun i => ⟨{(gaugeSeminormFamily ℝ X i).comp f}, 1, ?_⟩)
  simp [allSeminorms]

/-- `finestLC` is finer than every locally convex vector topology on `V`. -/
theorem finestLC_le (t : TopologicalSpace V) [@IsTopologicalAddGroup V t _]
    [@ContinuousSMul ℝ V _ _ t] [@LocallyConvexSpace ℝ V _ _ _ _ t] : finestLC V ≤ t := by
  rw [← continuous_id_iff_le]
  exact continuous_linearMap_finestLC (X := V) LinearMap.id

variable (V) in
/-- The set of locally convex vector topologies on `V`. -/
def LCTopologies : Set (TopologicalSpace V) :=
  {t | @IsTopologicalAddGroup V t _ ∧ @ContinuousSMul ℝ V _ _ t ∧
    @LocallyConvexSpace ℝ V _ _ _ _ t}

variable (V) in
/-- **« la topologie localement convexe la plus fine »**: `finestLC V` is a locally convex vector
topology, finer than (`≤`, Mathlib's order) every other one. -/
theorem isLeast_finestLC : IsLeast (LCTopologies V) (finestLC V) := by
  refine ⟨⟨isTopologicalAddGroup_finestLC V, continuousSMul_finestLC V,
    locallyConvexSpace_finestLC V⟩, ?_⟩
  rintro t ⟨h1, h2, h3⟩
  exact finestLC_le t

variable (V) in
theorem finestLC_eq_sInf : finestLC V = sInf (LCTopologies V) :=
  (isLeast_finestLC V).isGLB.sInf_eq.symm

/-- The neighbourhoods of `x` for `finestLC` are the sets containing a seminorm ball at `x`. -/
theorem mem_nhds_finestLC_iff (x : V) (U : Set V) :
    U ∈ @nhds V (finestLC V) x ↔ ∃ q : Seminorm ℝ V, ∃ r > 0, q.ball x r ⊆ U := by
  letI := finestLC V
  rw [(withSeminorms_finestLC V).mem_nhds_iff]
  constructor
  · rintro ⟨s, r, hr, h⟩
    exact ⟨s.sup (allSeminorms V), r, hr, h⟩
  · rintro ⟨q, r, hr, h⟩
    exact ⟨{q}, r, hr, by simpa [allSeminorms] using h⟩

/-- A convex set `C` is a `finestLC`-neighbourhood of each of its core points. -/
theorem mem_nhds_finestLC_of_core {C : Set V} (hC : Convex ℝ C) {x : V}
    (hx : ∀ v : V, ∀ᶠ t in 𝓝 (0 : ℝ), x + t • v ∈ C) : C ∈ @nhds V (finestLC V) x := by
  set S : Set V := (fun u => x + u) ⁻¹' C with hS
  have hSc : Convex ℝ S := hC.translate_preimage_right x
  set U : Set V := S ∩ -S with hU
  have hUc : Convex ℝ U := hSc.inter hSc.neg
  have hU0 : (0 : V) ∈ U := by
    have := (hx 0).self_of_nhds
    simp only [smul_zero, add_zero] at this
    simp [hU, hS, this]
  have hUb : Balanced ℝ U := by
    rw [balanced_iff_neg_mem hUc]
    rintro u ⟨h1, h2⟩
    exact ⟨h2, by simpa using h1⟩
  have hUa : Absorbent ℝ U := by
    rw [absorbent_iff_eventually_nhdsNE_zero]
    intro v
    refine ((hx v).and (hx (-v))).filter_mono nhdsWithin_le_nhds |>.mono ?_
    rintro c ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    show x + -(c • v) ∈ C
    simpa [smul_neg] using h2
  let p := gaugeSeminorm hUb hUc hUa
  refine (mem_nhds_finestLC_iff x C).2 ⟨p, 1, one_pos, fun y hy => ?_⟩
  rw [Seminorm.mem_ball] at hy
  have : y - x ∈ U := gauge_lt_one_subset_self hUc hU0 hUa hy
  have h := this.1
  simpa [hS] using h

/-- **A convex set is open for `finestLC` iff it is algebraically open** (every point is a core
point). -/
theorem isOpen_finestLC_iff_core {C : Set V} (hC : Convex ℝ C) :
    IsOpen[finestLC V] C ↔ ∀ x ∈ C, ∀ v : V, ∀ᶠ t in 𝓝 (0 : ℝ), x + t • v ∈ C := by
  letI := finestLC V
  haveI := isTopologicalAddGroup_finestLC V
  haveI := continuousSMul_finestLC V
  constructor
  · intro hO x hx v
    have hc : Continuous fun t : ℝ => x + t • v := continuous_const.add (continuous_id.smul continuous_const)
    have : (fun t : ℝ => x + t • v) ⁻¹' C ∈ 𝓝 (0 : ℝ) :=
      (hO.preimage hc).mem_nhds (by simpa using hx)
    exact this
  · intro h
    rw [isOpen_iff_mem_nhds]
    intro x hx
    exact mem_nhds_finestLC_of_core hC (h x hx)

/-- **The printed reduction of Prop. 1**: a convex set is open for `finestLC` iff each of its
points `x` is interior to `(x + l) ∩ C` for the canonical topology of every finite-dimensional
subspace `l`. -/
theorem isOpen_finestLC_iff_finiteDimensional {C : Set V} (hC : Convex ℝ C) :
    IsOpen[finestLC V] C ↔ ∀ x ∈ C, ∀ l : Submodule ℝ V, FiniteDimensional ℝ l →
      {u : l | x + (u : V) ∈ C} ∈ @nhds l (moduleTopology ℝ l) 0 := by
  rw [isOpen_finestLC_iff_core hC]
  constructor
  · intro h x hx l _
    letI := finestLC V
    haveI := isTopologicalAddGroup_finestLC V
    haveI := continuousSMul_finestLC V
    letI : TopologicalSpace l := moduleTopology ℝ l
    haveI : IsModuleTopology ℝ l := ⟨rfl⟩
    have hc : Continuous (l.subtype) := IsModuleTopology.continuous_of_linearMap l.subtype
    have hO : IsOpen C := (isOpen_finestLC_iff_core hC).2 h
    have hc' : Continuous fun u : l => x + (u : V) := continuous_const.add hc
    exact (hO.preimage hc').mem_nhds (by simpa using hx)
  · intro h x hx v
    let l : Submodule ℝ V := ℝ ∙ v
    letI : TopologicalSpace l := moduleTopology ℝ l
    haveI : IsModuleTopology ℝ l := ⟨rfl⟩
    haveI : ContinuousSMul ℝ l := IsModuleTopology.toContinuousSMul ℝ l
    have hN := h x hx l inferInstance
    let w : l := ⟨v, Submodule.mem_span_singleton_self v⟩
    have hc : Continuous fun t : ℝ => t • w := continuous_id.smul continuous_const
    have ht : Tendsto (fun t : ℝ => t • w) (𝓝 0) (𝓝 0) := by
      simpa using hc.tendsto 0
    exact (ht.eventually hN).mono fun t ht => by simpa [w] using ht

/-- `finestLC` induces on every subspace its own finest locally convex topology. -/
theorem induced_finestLC_eq_finestLC (S : Submodule ℝ V) :
    TopologicalSpace.induced (Subtype.val : S → V) (finestLC V) = finestLC S := by
  letI := finestLC V
  haveI := isTopologicalAddGroup_finestLC V
  haveI := continuousSMul_finestLC V
  haveI := locallyConvexSpace_finestLC V
  refine le_antisymm ?_ ?_
  · obtain ⟨T, hT⟩ := S.exists_isCompl
    let π : V →ₗ[ℝ] S := Submodule.projectionOnto S T hT
    letI tS : TopologicalSpace S := finestLC S
    haveI := isTopologicalAddGroup_finestLC S
    haveI := continuousSMul_finestLC S
    haveI := locallyConvexSpace_finestLC S
    have hπ : Continuous π := continuous_linearMap_finestLC π
    have hid : Continuous[TopologicalSpace.induced (Subtype.val : S → V) (finestLC V), tS]
        (id : S → S) := by
      have : (id : S → S) = π ∘ Subtype.val := by
        funext s; exact (Submodule.projectionOnto_apply_left hT s).symm
      rw [this]
      exact @Continuous.comp _ _ _ (TopologicalSpace.induced (Subtype.val : S → V) (finestLC V))
        (finestLC V) tS _ _ hπ (continuous_induced_dom (t := finestLC V))
    exact continuous_id_iff_le.1 hid
  · rw [← continuous_iff_le_induced]
    exact continuous_linearMap_finestLC S.subtype

variable (V) in
/-- On a finite-dimensional space `finestLC` is the canonical topology. -/
theorem finestLC_eq_moduleTopology [FiniteDimensional ℝ V] : finestLC V = moduleTopology ℝ V := by
  letI := finestLC V
  haveI := isTopologicalAddGroup_finestLC V
  haveI := continuousSMul_finestLC V
  haveI := t2Space_finestLC V
  haveI : IsModuleTopology ℝ V := isModuleTopologyOfFiniteDimensional
  exact eq_moduleTopology ℝ V

/-- `finestLC` induces on every finite-dimensional subspace its canonical topology. -/
theorem induced_finestLC_eq_moduleTopology (l : Submodule ℝ V) [FiniteDimensional ℝ l] :
    TopologicalSpace.induced (Subtype.val : l → V) (finestLC V) = moduleTopology ℝ l := by
  rw [induced_finestLC_eq_finestLC, finestLC_eq_moduleTopology]

/-- On a finite-dimensional space `finestLC` is every Hausdorff vector topology (the usual one
of `ℝⁿ`). -/
theorem finestLC_eq_of_finiteDimensional [FiniteDimensional ℝ V] [t : TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V] : finestLC V = t := by
  haveI : IsModuleTopology ℝ V := isModuleTopologyOfFiniteDimensional
  rw [finestLC_eq_moduleTopology, ← eq_moduleTopology ℝ V]

end FinestLC

end Benzecri
