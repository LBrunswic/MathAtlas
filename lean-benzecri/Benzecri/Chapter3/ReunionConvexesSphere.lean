import Benzecri.Chapter3.ReunionConvexes
import Benzecri.Chapter3.AppuiSphere
import Benzecri.Chapter3.PointsExtremaux
import Benzecri.Chapter3.BooleProjectif

/-!
# Chapter 3 § 5, Theorem 1′ — a compact convex `V` of a convex body `W` of S(n): I′ ⇔ II′ ⇔ III′

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 3 § 5, journal pp. 280–281; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch3.tex` (TO BE CHECKED BY THE AUTHOR, OQ-160; the
statement was checked here against the page image of the scan, PDF p. 53). Target
T-bz-c3-reunion-convexes-sphere.

* `bzthm:c3s5t1prime_reunion_convexes_sphere` — `benzecri1960_ch3.tex:1399` (printed
  « THÉORÈME 1 », the théorème 1′ of the head of § 5, l.1399–1411; proof l.1414–1418) —
  `Benzecri.reunion_convexes_sphere` (TFAE of I′, II′, III′ for a convex body `W` of `S(n)`, every
  `n`, `n = 0` included), and the stronger `Benzecri.reunion_convexes_sphere_of_isCompact` (`W`
  only a compact strict convex part: the interior is never used). Not marked: III′ is proved in
  the reading « $H$ a CLOSED hemisphere of $L$ » (see SCOPE); under the reading « open
  hemisphere » I′ ⇒ III′ fails (`ReunionSphereInstance.demiTriangle_sans_hemisphereOuvert`).
  The parts: `Sphere.proprieteIIIS_of_proprieteIS` (I′ ⇒ III′), `Sphere.proprieteIS_of_proprieteIIISlarge`
  (III′ ⇒ I′ in every reading of « hémisphère de L », no topology),
  `Sphere.proprieteIIS_iff_systemeFondamental` (the printed form of II′ is its reformulation).
  New definitions `Sphere.ProprieteIS` (I′), `Sphere.ProprieteIIS` (II′), `Sphere.ProprieteIIIS`
  (III′), `Sphere.DemiSphereFermeeDe`, `Sphere.DemiSphereDe`, `Sphere.ProprieteIIISlarge`,
  `Sphere.ProprieteIIISouvert`; instances in `ReunionSphereInstance`: `demiTriangle_proprietes`,
  `vertex_proprietes` (I′, II′, III′ for the closed half `x₁ ≤ x₀` of the closed triangle of
  `S(2)` and for a vertex of it), `demiSphereFermeeDe_univ`, `demiSphereDe_univ`,
  `demiTriangle_proprieteIIISlarge`, `simplexS_proprieteIIISouvert`.

> **Théorème 1** [1′]. Soit $W$ un corps convexe de $S(n)$, $V$ une partie compacte convexe non
> vide de $W$; alors les trois propriétés ci-dessous sont équivalentes :
> I′$(V, W)$ : $W-V$ est convexe;
> II′$(V, W)$ : les hémisphères ouverts contenant $V$ coupent $W$ suivant un système fondamental
> de voisinages de $V$ considéré comme partie de $W$;
> III′$(V, W)$ : le support de $V$ est une variété d'appui $L$ de $W$, et $V$ est l'intersection
> de $W$ avec un hémisphère $H$ de $L$.
>
> *Démonstration.* En effet, le corps convexe $W$ appartient à un hémisphère ouvert de $S(n)$
> muni canoniquement d'une structure d'espace affine à $n$ dimensions. Dans cet espace, le
> théorème 1′ est un corollaire du théorème 1.

## The proof formalized

The printed proof: `W` lies in an open hemisphere `ℓ > 0` (`exists_forall_pos_of_isCompact`, the
proof of the strict `IsCorpsConvexeS.exists_forall_pos`, which uses compactness and strictness
only), whose affine chart is read as the section `ℓ = 1` of the cone (`coneSection`, as in the
strict `Chapter3/PointsExtremaux`). The transfer the paper leaves implicit is built here:
convexity (`isConvexPart_iff_convex_coneSection`), set difference (`coneSection_sdiff`),
compactness (`isCompact_coneSection`), so I′ is I of the sections (`proprieteI_coneSection_iff`);
open hemispheres ↔ open half-spaces of `ℝⁿ⁺¹` meeting the section, so II′ is II of the sections
(`proprieteII_coneSection_iff`). The affine Theorem 1 (strict `reunion_convexes_affine`) is applied
in `ℝⁿ⁺¹ ≠ 0` (the section is a compact convex part of the hyperplane `ℓ = 1`), so the
dimension-zero defect of the affine theorem does not occur. For III′ the cones are used rather than
the sections: I′ is I of the cones `F(·) ∪ {O}` (`proprieteI_kPrime_iff`), the affine I ⇔ III
(strict `proprieteI_iff_proprieteIII`, any dimension, `V` closed) applies to them, the affine
support of `F(V) ∪ {O}` is `span F(V)` (`affineSpan_kPrime`), so the variété d'appui of Déf. 3 is
that of Déf. 6, and a half-space `L ∩ {f ≤ c}` meeting a cone in a cone is `L ∩ {f ≤ 0}`, the
closed hemisphere of `−f`; when `V = L ∩ W` the hemisphere `ℓ ≥ 0` of `L` contains `W ∩ L`, so no
« éventuellement » case is needed. III′ ⇒ I′ goes through Prop. 4 on the cones (strict
`proprieteI_of_isVarieteAppui`).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| « $W$ un corps convexe de $S(n)$ » | ✓ carried: `IsCorpsConvexeS n W`; ⚠ weakened in `reunion_convexes_sphere_of_isCompact`: `IsStrictConvexPart W`, `IsCompact W` (interior unused) |
| « $V$ une partie compacte convexe non vide de $W$ » | ✓ carried: `IsCompact V`, `IsConvexPart V`, `V.Nonempty`, `V ⊆ W` |
| « $W - V$ est convexe » | ✓ `ProprieteIS V W` (`V ⊆ W`, `V` and `W − V` convex parts, as the affine `ProprieteI`; the first two are hypotheses of the theorem) |
| « les hémisphères ouverts … système fondamental de voisinages de $V$ … partie de $W$ » | ✓ `ProprieteIIS` (for every open `O ⊇ V` an open hemisphere `H ⊇ V`, `H ∩ W ⊆ O`), proved equivalent to the printed form (`proprieteIIS_iff_systemeFondamental`); hemispheres of non-zero continuous forms (Déf. 5, DEC-114) |
| « le support de $V$ est une variété d'appui $L$ de $W$ » | ✓ `IsVarieteAppuiK W (supportK V)` (Déf. 6, the strict `Chapter3/AppuiSphere`) |
| « un hémisphère $H$ de $L$ » | reading: a closed hemisphere `L ∩ closedHemisphere l`, `l` not identically zero on `F(L)` (`DemiSphereFermeeDe`); III′ ⇒ I′ holds for every reading (`ProprieteIIISlarge`: open or closed, `l = 0` admitted) |

## SCOPE (disclosed)

* The label is **not marked**: the statement is proved in full, with no `sorry` and no added
  hypothesis, in every dimension, **in the reading « $H$ a closed hemisphere of $L$ »**. The paper
  does not say whether the hemisphere of III′ is open or closed. Under the open reading I′ ⇒ III′
  is false: the closed half `x₁ ≤ x₀` of the closed triangle has I′ but is not `W ∩ L ∩ H` for any
  open hemisphere `H` (`demiTriangle_sans_hemisphereOuvert`). III′ ⇒ I′ holds in every reading.
  The planner's conjecture (reading (a)) holds: unlike the affine III, no « éventuellement $H = L$ »
  case is needed, since `W ∩ L` lies in the genuine hemisphere `ℓ ≥ 0` of `L`.
* II′ is read as the strict `ProprieteII` is: for every open `O ⊇ V` of `S(n)` an open hemisphere
  `H ⊇ V` with `H ∩ W ⊆ O`; it is proved equivalent to the printed « système fondamental »
  formulation.
* `n = 0` needs no treatment: the chart lives in `ℝⁿ⁺¹ ≠ 0`, and the theorem holds there
  (contrast the affine Theorem 1, strict `reunion_convexes_dimZero`).
* The affine chart of the hemisphere `ℓ > 0` is the section `ℓ = 1` of the cone, not
  `instAddTorsorHemi` (the same chart, `kb/0129`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open Set Filter Topology

namespace Benzecri

namespace Sphere

section Defs

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- **`I′(V, W)`**: `V ⊆ W`, and `V` and `W − V` are convex parts of `S(E)`. -/
def ProprieteIS (V W : Set (Sphere E)) : Prop :=
  V ⊆ W ∧ IsConvexPart V ∧ IsConvexPart (W \ V)

/-- **`II′(V, W)`**: for every open `O ⊇ V` of `S(E)` there is an open hemisphere `H` (of a
non-zero continuous form) with `V ⊆ H` and `H ∩ W ⊆ O`. -/
def ProprieteIIS [TopologicalSpace E] (V W : Set (Sphere E)) : Prop :=
  ∀ O : Set (Sphere E), IsOpen O → V ⊆ O → ∃ l : StrongDual ℝ E, l ≠ 0 ∧
    V ⊆ openHemisphere (l : Module.Dual ℝ E) ∧ openHemisphere (l : Module.Dual ℝ E) ∩ W ⊆ O

/-- A *closed hemisphere of the linear subvariety* `L`: `L ∩ closedHemisphere l` for a form `l`
not identically zero on `F(L)`. -/
def DemiSphereFermeeDe (L H : Set (Sphere E)) : Prop :=
  ∃ l : Module.Dual ℝ E, (∃ v ∈ F L, l v ≠ 0) ∧ H = L ∩ closedHemisphere l

/-- **`III′(V, W)`**: the support of `V` is a variété d'appui `L` of `W` (Déf. 6), and `V` is the
intersection of `W` with a closed hemisphere `H` of `L`. -/
def ProprieteIIIS (V W : Set (Sphere E)) : Prop :=
  IsVarieteAppuiK W (supportK V) ∧ ∃ H, DemiSphereFermeeDe (supportK V) H ∧ V = W ∩ H

/-- The widest reading of « un hémisphère $H$ de $L$ »: `L ∩ closedHemisphere l` or
`L ∩ openHemisphere l` for any form `l` (`l = 0` admitted, giving `L` and `∅`). -/
def DemiSphereDe (L H : Set (Sphere E)) : Prop :=
  ∃ l : Module.Dual ℝ E, H = L ∩ closedHemisphere l ∨ H = L ∩ openHemisphere l

/-- `III′(V, W)` in the widest reading (`DemiSphereDe`). -/
def ProprieteIIISlarge (V W : Set (Sphere E)) : Prop :=
  IsVarieteAppuiK W (supportK V) ∧ ∃ H, DemiSphereDe (supportK V) H ∧ V = W ∩ H

/-- `III′(V, W)` in the reading « an OPEN hemisphere of `L` » (for the counterexample). -/
def ProprieteIIISouvert (V W : Set (Sphere E)) : Prop :=
  IsVarieteAppuiK W (supportK V) ∧ ∃ l : Module.Dual ℝ E, (∃ v ∈ F (supportK V), l v ≠ 0) ∧
    V = W ∩ (supportK V ∩ openHemisphere l)

theorem DemiSphereFermeeDe.demiSphereDe {L H : Set (Sphere E)} (h : DemiSphereFermeeDe L H) :
    DemiSphereDe L H := by
  obtain ⟨l, -, rfl⟩ := h
  exact ⟨l, Or.inl rfl⟩

theorem ProprieteIIIS.large {V W : Set (Sphere E)} (h : ProprieteIIIS V W) :
    ProprieteIIISlarge V W := by
  obtain ⟨hL, H, hH, hV⟩ := h
  exact ⟨hL, H, hH.demiSphereDe, hV⟩

theorem ProprieteIIISouvert.large {V W : Set (Sphere E)} (h : ProprieteIIISouvert V W) :
    ProprieteIIISlarge V W := by
  obtain ⟨hL, l, -, hV⟩ := h
  exact ⟨hL, _, ⟨l, Or.inr rfl⟩, hV⟩

/-- The printed first formulation of `II′(V, W)`: the traces on `W` of the open hemispheres
containing `V` form a fundamental system of neighbourhoods of `V` in the subspace `W`. -/
theorem proprieteIIS_iff_systemeFondamental [TopologicalSpace E] [T1Space E]
    {V W : Set (Sphere E)} (hVW : V ⊆ W) :
    ProprieteIIS V W ↔
      (∀ l : StrongDual ℝ E, l ≠ 0 → V ⊆ openHemisphere (l : Module.Dual ℝ E) →
          ((↑) ⁻¹' openHemisphere (l : Module.Dual ℝ E) : Set W) ∈ 𝓝ˢ ((↑) ⁻¹' V : Set W)) ∧
        ∀ N ∈ 𝓝ˢ ((↑) ⁻¹' V : Set W), ∃ l : StrongDual ℝ E, l ≠ 0 ∧
          V ⊆ openHemisphere (l : Module.Dual ℝ E) ∧
          ((↑) ⁻¹' openHemisphere (l : Module.Dual ℝ E) : Set W) ⊆ N := by
  constructor
  · intro h
    refine ⟨fun l _ hVl => ((isOpen_openHemisphere l).preimage continuous_subtype_val).mem_nhdsSet.2
      (fun x hx => hVl hx), fun N hN => ?_⟩
    obtain ⟨U', hU'o, hVU', hU'N⟩ := mem_nhdsSet_iff_exists.1 hN
    obtain ⟨U, hUo, rfl⟩ := isOpen_induced_iff.1 hU'o
    obtain ⟨l, hl, hVl, hlW⟩ := h U hUo (fun v hv => hVU' (show (⟨v, hVW hv⟩ : W) ∈ _ from hv))
    exact ⟨l, hl, hVl, fun x hx => hU'N (hlW ⟨hx, x.2⟩)⟩
  · rintro ⟨-, h⟩ O hO hVO
    have hN : ((↑) ⁻¹' O : Set W) ∈ 𝓝ˢ ((↑) ⁻¹' V : Set W) :=
      (hO.preimage continuous_subtype_val).mem_nhdsSet.2 (fun x hx => hVO hx)
    obtain ⟨l, hl, hVl, hlN⟩ := h _ hN
    exact ⟨l, hl, hVl, fun x hx => hlN (show (⟨x, hx.2⟩ : W) ∈
      ((↑) ⁻¹' openHemisphere (l : Module.Dual ℝ E) : Set W) from hx.1)⟩

end Defs

/-! ### The cone `k′ = F(k) ∪ {O}`: I′ and III′ on `S(E)` are I and III on the cones -/

section Cone

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem F_sdiff (A B : Set (Sphere E)) : F (A \ B) = F A \ F B := by
  ext v
  constructor
  · rintro ⟨hv, hA, hB⟩
    exact ⟨⟨hv, hA⟩, fun ⟨_, hB'⟩ => hB hB'⟩
  · rintro ⟨⟨hv, hA⟩, hB⟩
    exact ⟨hv, hA, fun h => hB ⟨hv, h⟩⟩

theorem kPrime_sdiff_kPrime (V W : Set (Sphere E)) : kPrime W \ kPrime V = F (W \ V) := by
  ext v
  by_cases hv : v = 0
  · subst hv
    simp [kPrime, zero_notMem_F]
  · rw [Set.mem_sdiff, mem_kPrime_of_ne hv, mem_kPrime_of_ne hv, F_sdiff]
    rfl

/-- **I′ is I on the cones**: for `W` strict, `I′(V, W) ⇔ I(F(V) ∪ {O}, F(W) ∪ {O})`. -/
theorem proprieteI_kPrime_iff {V W : Set (Sphere E)} (hW : IsStrictConvexPart W) :
    ProprieteI (kPrime V) (kPrime W) ↔ ProprieteIS V W := by
  have hsub : kPrime V ⊆ kPrime W ↔ V ⊆ W := by
    rw [← F_subset_F_iff]
    constructor
    · intro h v hv
      exact (mem_kPrime_of_ne hv.1).1 (h (mem_insert_of_mem _ hv))
    · intro h
      exact insert_subset_insert h
  have hconv : Convex ℝ (kPrime W \ kPrime V) ↔ IsConvexPart (W \ V) := by
    rw [kPrime_sdiff_kPrime, ← isStrictConvexPart_iff_convex_F]
    exact ⟨fun h => h.1, fun h => ⟨h, fun m hm hm' => hW.2 m hm.1 hm'.1⟩⟩
  exact and_congr hsub (and_congr Iff.rfl hconv)

/-- The affine support of the cone `F(V) ∪ {O}` is the vector subspace `span F(V)`. -/
theorem affineSpan_kPrime (V : Set (Sphere E)) :
    affineSpan ℝ (kPrime V) = (Submodule.span ℝ (F V)).toAffineSubspace := by
  have hpos : IsPosCone (kPrime V) := fun c hc v hv => smul_mem_kPrime hv hc.le
  apply SetLike.coe_injective
  rw [coe_affineSpan_eq_span_of_isPosCone hpos ⟨0, zero_mem_kPrime V⟩, kPrime,
    Submodule.span_insert_zero]
  rfl

/-- **Theorem 1′, III′ ⇒ I′**, for every reading of « hémisphère de L », no topology. -/
theorem proprieteIS_of_proprieteIIISlarge {V W : Set (Sphere E)} (hW : IsStrictConvexPart W)
    (hV : IsConvexPart V) (h : ProprieteIIISlarge V W) : ProprieteIS V W := by
  obtain ⟨hL, H, ⟨l, hH⟩, hVe⟩ := h
  have hL' : IsVarieteAppui (kPrime W) (affineSpan ℝ (kPrime V)) := by
    rw [affineSpan_kPrime]
    exact isVarieteAppuiK_linearSubvariety_iff.1 hL
  have hVW : V ⊆ W := hVe ▸ inter_subset_left
  have key : ∀ (v : E) (hv : v ≠ 0), v ∈ F V ↔ v ∈ F W ∧ mk v hv ∈ H := by
    intro v hv
    rw [← mk_mem_iff_mem_F hv, Set.ext_iff.1 hVe (mk v hv), mem_inter_iff, mk_mem_iff_mem_F hv]
  have hWF : Convex ℝ (F W) := isStrictConvexPart_iff_convex_F.1 hW
  rw [← proprieteI_kPrime_iff hW]
  refine proprieteI_of_isVarieteAppui (convex_kPrime hW.1) hL' ⟨fun v hv =>
    ⟨subset_affineSpan ℝ _ hv, insert_subset_insert (F_mono hVW) hv⟩, hV, ?_⟩
  rw [affineSpan_kPrime]
  have h0 : (0 : E) ∉ (((Submodule.span ℝ (F V)).toAffineSubspace : Set E) ∩
      kPrime W) \ kPrime V := fun h => h.2 (zero_mem_kPrime V)
  rcases hH with rfl | rfl
  · have e : (((Submodule.span ℝ (F V)).toAffineSubspace : Set E) ∩ kPrime W) \ kPrime V =
        F W ∩ ((Submodule.span ℝ (F V) : Set E) ∩ {v | l v < 0}) := by
      ext v
      by_cases hv : v = 0
      · subst hv
        exact iff_of_false h0 fun h => zero_notMem_F W h.1
      rw [Set.mem_sdiff, mem_inter_iff, mem_kPrime_of_ne hv, mem_kPrime_of_ne hv, key v hv]
      simp only [supportK, mem_inter_iff, mk_mem_linearSubvariety hv, mk_mem_closedHemisphere hv,
        mem_setOf_eq, SetLike.mem_coe, Submodule.mem_toAffineSubspace]
      constructor
      · rintro ⟨⟨hvL, hvW⟩, hn⟩
        exact ⟨hvW, hvL, lt_of_not_ge fun h => hn ⟨hvW, hvL, h⟩⟩
      · rintro ⟨hvW, hvL, hlt⟩
        exact ⟨⟨hvL, hvW⟩, fun ⟨_, _, h⟩ => absurd h (not_le.2 hlt)⟩
    rw [e]
    exact hWF.inter ((Submodule.convex _).inter (convex_halfSpace_lt l.isLinear 0))
  · have e : (((Submodule.span ℝ (F V)).toAffineSubspace : Set E) ∩ kPrime W) \ kPrime V =
        F W ∩ ((Submodule.span ℝ (F V) : Set E) ∩ {v | l v ≤ 0}) := by
      ext v
      by_cases hv : v = 0
      · subst hv
        exact iff_of_false h0 fun h => zero_notMem_F W h.1
      rw [Set.mem_sdiff, mem_inter_iff, mem_kPrime_of_ne hv, mem_kPrime_of_ne hv, key v hv]
      simp only [supportK, mem_inter_iff, mk_mem_linearSubvariety hv, mk_mem_openHemisphere hv,
        mem_setOf_eq, SetLike.mem_coe, Submodule.mem_toAffineSubspace]
      constructor
      · rintro ⟨⟨hvL, hvW⟩, hn⟩
        exact ⟨hvW, hvL, le_of_not_gt fun h => hn ⟨hvW, hvL, h⟩⟩
      · rintro ⟨hvW, hvL, hle⟩
        exact ⟨⟨hvL, hvW⟩, fun ⟨_, _, h⟩ => absurd h (not_lt.2 hle)⟩
    rw [e]
    exact hWF.inter ((Submodule.convex _).inter (convex_halfSpace_le l.isLinear 0))

theorem proprieteIS_of_proprieteIIIS {V W : Set (Sphere E)} (hW : IsStrictConvexPart W)
    (hV : IsConvexPart V) (h : ProprieteIIIS V W) : ProprieteIS V W :=
  proprieteIS_of_proprieteIIISlarge hW hV h.large

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T1Space E]

omit [IsTopologicalAddGroup E] in
/-- `F(V) ∪ {O}` is closed for a closed `V`. -/
theorem isClosed_kPrime {V : Set (Sphere E)} (hV : IsClosed V) : IsClosed (kPrime V) := by
  have h := F_closure V
  rw [hV.closure_eq] at h
  have e : kPrime V = {0} ∪ closure (F V) := by
    rw [kPrime]
    conv_lhs => rw [h]
    ext v
    by_cases hv : v = 0 <;> simp [hv]
  rw [e]
  exact isClosed_singleton.union isClosed_closure

/-- **Theorem 1′, I′ ⇒ III′** (closed hemispheres), for every strict convex `W` contained in an
open hemisphere `ℓ > 0` and every closed non-empty `V`. -/
theorem proprieteIIIS_of_proprieteIS {V W : Set (Sphere E)} (hW : IsStrictConvexPart W)
    {ℓ : Module.Dual ℝ E} (hℓ : ∀ v ∈ F W, 0 < ℓ v)
    (hV : IsClosed V) (hne : V.Nonempty) (h : ProprieteIS V W) : ProprieteIIIS V W := by
  have hI := (proprieteI_kPrime_iff hW).2 h
  obtain ⟨hL, H, hH, hVH⟩ := proprieteIII_of_proprieteI (convex_kPrime hW.1) (isClosed_kPrime hV)
    ⟨0, zero_mem_kPrime V⟩ hI
  rw [affineSpan_kPrime] at hL hH
  refine ⟨isVarieteAppuiK_linearSubvariety_iff.2 hL, ?_⟩
  set L := Submodule.span ℝ (F V) with hLdef
  -- membership in `V` through the cone
  have key : ∀ (v : E) (hv : v ≠ 0), mk v hv ∈ V ↔ v ∈ H ∧ v ∈ F W := by
    intro v hv
    rw [mk_mem_iff_mem_F hv, ← mem_kPrime_of_ne hv, hVH, mem_inter_iff, mem_kPrime_of_ne hv]
  rcases hH with ⟨f, ⟨x, hx, y, hy, hxy⟩, c, rfl⟩ | rfl
  · refine ⟨_, ⟨-f, ⟨x - y, ?_, ?_⟩, rfl⟩, ?_⟩
    · have hx' : x ∈ L := Submodule.mem_toAffineSubspace.1 hx
      have hy' : y ∈ L := Submodule.mem_toAffineSubspace.1 hy
      have hne' : x - y ≠ 0 := fun h0 => hxy (by rw [sub_eq_zero.1 h0])
      rw [supportK, F_linearSubvariety]
      exact ⟨L.sub_mem hx' hy', hne'⟩
    · rw [LinearMap.neg_apply, map_sub, neg_ne_zero, sub_ne_zero]
      exact hxy
    · have hc : 0 ≤ c := by
        have : (0 : E) ∈ ((L.toAffineSubspace : Set E) ∩ {x | f x ≤ c}) ∩ kPrime W := by
          rw [← hVH]; exact zero_mem_kPrime V
        simpa using this.1.2
      ext z
      induction z using ind with
      | h v hv =>
      rw [key v hv, supportK]
      simp only [mem_inter_iff]
      rw [mk_mem_linearSubvariety hv, mk_mem_closedHemisphere hv, mk_mem_iff_mem_F hv (A := W)]
      simp only [mem_setOf_eq, SetLike.mem_coe, Submodule.mem_toAffineSubspace,
        LinearMap.neg_apply, neg_nonneg]
      constructor
      · rintro ⟨⟨hvL, hfc⟩, hvW⟩
        refine ⟨hvW, hvL, ?_⟩
        by_contra hpos
        rw [not_le] at hpos
        have hmem : ((c + 1) / f v) • v ∈ kPrime V :=
          smul_mem_kPrime (mem_insert_of_mem _ ((mk_mem_iff_mem_F hv).1
            ((key v hv).2 ⟨⟨hvL, hfc⟩, hvW⟩))) (div_pos (by linarith) hpos).le
        rw [hVH] at hmem
        have := hmem.1.2
        simp only [mem_setOf_eq, map_smul, smul_eq_mul, div_mul_cancel₀ _ hpos.ne'] at this
        linarith
      · rintro ⟨hvW, hvL, hf⟩
        exact ⟨⟨hvL, hf.trans hc⟩, hvW⟩
  · obtain ⟨z₀, hz₀⟩ := hne
    obtain ⟨v₀, hv₀0, rfl⟩ := exists_isRep z₀
    have hv₀ : v₀ ∈ F V := ⟨hv₀0, hz₀⟩
    refine ⟨_, ⟨ℓ, ⟨v₀, ?_, (hℓ v₀ (F_mono h.1 hv₀)).ne'⟩, rfl⟩, ?_⟩
    · rw [supportK, F_linearSubvariety]
      exact ⟨Submodule.subset_span hv₀, hv₀0⟩
    · ext z
      induction z using ind with
      | h v hv =>
      rw [key v hv, supportK]
      simp only [mem_inter_iff]
      rw [mk_mem_linearSubvariety hv, mk_mem_closedHemisphere hv, mk_mem_iff_mem_F hv (A := W)]
      simp only [SetLike.mem_coe, Submodule.mem_toAffineSubspace]
      constructor
      · rintro ⟨hvL, hvW⟩
        exact ⟨hvW, hvL, (hℓ v hvW).le⟩
      · rintro ⟨hvW, hvL, -⟩
        exact ⟨hvL, hvW⟩

theorem proprieteIS_iff_proprieteIIIS {V W : Set (Sphere E)} (hW : IsStrictConvexPart W)
    {ℓ : Module.Dual ℝ E} (hℓ : ∀ v ∈ F W, 0 < ℓ v)
    (hV : IsClosed V) (hVc : IsConvexPart V) (hne : V.Nonempty) :
    ProprieteIS V W ↔ ProprieteIIIS V W :=
  ⟨proprieteIIIS_of_proprieteIS hW hℓ hV hne, proprieteIS_of_proprieteIIIS hW hVc⟩

end Cone

/-! ### The affine chart `ℓ = 1`: I′ and II′ on `S(E)` are I and II on the sections -/

section Chart

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem coneSection_mono {A B : Set (Sphere E)} (h : A ⊆ B) (ℓ : Module.Dual ℝ E) :
    coneSection A ℓ ⊆ coneSection B ℓ := fun _ hv => ⟨F_mono h hv.1, hv.2⟩

theorem coneSection_sdiff (A B : Set (Sphere E)) (ℓ : Module.Dual ℝ E) :
    coneSection (A \ B) ℓ = coneSection A ℓ \ coneSection B ℓ := by
  ext v
  simp only [coneSection, Set.mem_sdiff, mem_setOf_eq, F_sdiff]
  tauto

/-- Every point of `k` has a representative in the section `ℓ = 1`. -/
theorem exists_mem_coneSection {k : Set (Sphere E)} {ℓ : Module.Dual ℝ E}
    (hℓ : ∀ v ∈ F k, 0 < ℓ v) {x : Sphere E} (hx : x ∈ k) :
    ∃ v ∈ coneSection k ℓ, ∃ h : v ≠ 0, mk v h = x := by
  obtain ⟨v, hv0, rfl⟩ := exists_isRep x
  have hvF : v ∈ F k := ⟨hv0, hx⟩
  have hs := inv_smul_mem_coneSection hvF (hℓ v hvF)
  exact ⟨_, hs, hs.1.1, mk_smul hv0 (inv_pos.2 (hℓ v hvF)) _⟩

/-- **Convexity through the chart**: a part `k` of the open hemisphere `ℓ > 0` is a convex part
of `S(E)` iff its image `{v ∈ F(k) | ℓ v = 1}` in the affine chart is convex. -/
theorem isConvexPart_iff_convex_coneSection {k : Set (Sphere E)} {ℓ : Module.Dual ℝ E}
    (hℓ : ∀ v ∈ F k, 0 < ℓ v) : IsConvexPart k ↔ Convex ℝ (coneSection k ℓ) := by
  constructor
  · intro hk x hx y hy a b ha hb hab
    have hz := hk (mem_insert_of_mem _ hx.1) (mem_insert_of_mem _ hy.1) ha hb hab
    have hℓz : ℓ (a • x + b • y) = 1 := by
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hx.2, hy.2, mul_one, mul_one, hab]
    refine ⟨?_, hℓz⟩
    rcases mem_insert_iff.1 hz with h0 | h
    · rw [h0, map_zero] at hℓz
      exact absurd hℓz zero_ne_one
    · exact h
  · intro hc
    show Convex ℝ (insert 0 (F k))
    refine convex_iff_forall_pos.2 fun x hx y hy a b ha hb hab => ?_
    rcases mem_insert_iff.1 hx with rfl | hxF
    · rw [smul_zero, zero_add]
      rcases mem_insert_iff.1 hy with rfl | hyF
      · rw [smul_zero]; exact mem_insert _ _
      · exact mem_insert_of_mem _ (smul_mem_F hyF hb)
    rcases mem_insert_iff.1 hy with rfl | hyF
    · rw [smul_zero, add_zero]
      exact mem_insert_of_mem _ (smul_mem_F hxF ha)
    have hpx := hℓ x hxF
    have hpy := hℓ y hyF
    set s := a * ℓ x + b * ℓ y with hs
    have hs0 : 0 < s := by positivity
    have hz := hc (inv_smul_mem_coneSection hxF hpx) (inv_smul_mem_coneSection hyF hpy)
      (div_pos (mul_pos ha hpx) hs0).le (div_pos (mul_pos hb hpy) hs0).le
      (by rw [← add_div, div_self hs0.ne'])
    have e : a • x + b • y = s • ((a * ℓ x / s) • ((ℓ x)⁻¹ • x) + (b * ℓ y / s) • ((ℓ y)⁻¹ • y)) := by
      rw [smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
      congr 2 <;> field_simp
    rw [e]
    exact mem_insert_of_mem _ (smul_mem_F hz.1 hs0)

/-- **I′ is I in the chart**. -/
theorem proprieteI_coneSection_iff {V W : Set (Sphere E)} {ℓ : Module.Dual ℝ E}
    (hℓ : ∀ v ∈ F W, 0 < ℓ v) (hVW : V ⊆ W) :
    ProprieteI (coneSection V ℓ) (coneSection W ℓ) ↔ ProprieteIS V W := by
  have hℓV : ∀ v ∈ F V, 0 < ℓ v := fun v hv => hℓ v (F_mono hVW hv)
  have hℓD : ∀ v ∈ F (W \ V), 0 < ℓ v := fun v hv => hℓ v (F_mono sdiff_subset hv)
  constructor
  · rintro ⟨-, hcV, hcD⟩
    refine ⟨hVW, (isConvexPart_iff_convex_coneSection hℓV).2 hcV,
      (isConvexPart_iff_convex_coneSection hℓD).2 ?_⟩
    rwa [coneSection_sdiff]
  · rintro ⟨-, hV, hD⟩
    refine ⟨coneSection_mono hVW ℓ, (isConvexPart_iff_convex_coneSection hℓV).1 hV, ?_⟩
    rw [← coneSection_sdiff]
    exact (isConvexPart_iff_convex_coneSection hℓD).1 hD

end Chart

section ChartTop

variable {n : ℕ}

/-- **II′ is II in the chart** (`E = ℝⁿ⁺¹`, `ℓ > 0` on `F(W)`, `V ⊆ W` non-empty). -/
theorem proprieteII_coneSection_iff {V W : Set (S n)} {ℓ : StrongDual ℝ (Fin (n + 1) → ℝ)}
    (hℓ : ∀ v ∈ F W, 0 < ℓ v) (hVW : V ⊆ W) (hne : V.Nonempty) :
    ProprieteII (coneSection V (ℓ : Module.Dual ℝ _)) (coneSection W (ℓ : Module.Dual ℝ _)) ↔
      ProprieteIIS V W := by
  have hℓV : ∀ v ∈ F V, 0 < ℓ v := fun v hv => hℓ v (F_mono hVW hv)
  constructor
  · intro hII O hO hVO
    have hFO : IsOpen (F O) := isOpen_iff_F.1 hO
    obtain ⟨H, ⟨f, -, c, rfl⟩, hVH, hHW⟩ :=
      hII (F O) hFO (fun v hv => F_mono hVO hv.1)
    have hmem : ∀ (v : Fin (n + 1) → ℝ) (hv : v ≠ 0), ℓ v = 1 →
        (mk v hv ∈ openHemisphere ((c • ℓ - f : StrongDual ℝ _) : Module.Dual ℝ _) ↔ f v < c) := by
      intro v hv h1
      rw [mk_mem_openHemisphere]
      simp only [ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_smul, LinearMap.sub_apply,
        LinearMap.smul_apply, ContinuousLinearMap.coe_coe, smul_eq_mul, h1, mul_one, sub_pos]
    have hV : V ⊆ openHemisphere ((c • ℓ - f : StrongDual ℝ _) : Module.Dual ℝ _) := by
      intro x hx
      obtain ⟨v, hvs, hv0, rfl⟩ := exists_mem_coneSection hℓV hx
      exact (hmem v hv0 hvs.2).2 (hVH hvs)
    refine ⟨c • ℓ - f, ?_, hV, ?_⟩
    · intro h0
      obtain ⟨x, hx⟩ := hne
      obtain ⟨v, hvs, hv0, rfl⟩ := exists_mem_coneSection hℓV hx
      have := (mk_mem_openHemisphere hv0).1 (hV hx)
      rw [h0] at this
      simp at this
    · rintro y ⟨hyH, hyW⟩
      obtain ⟨w, hws, hw0, rfl⟩ := exists_mem_coneSection hℓ hyW
      exact (mk_mem_iff_mem_F hw0).2 (hHW ⟨(hmem w hw0 hws.2).1 hyH, hws⟩).1
  · intro hII O' hO' hVO'
    set C : Set (Fin (n + 1) → ℝ) := {v | 0 < ℓ v ∧ (ℓ v)⁻¹ • v ∈ O'} with hCdef
    have hC : IsPosCone C := by
      rintro t ht v ⟨h1, h2⟩
      have e : (ℓ (t • v))⁻¹ • (t • v) = (ℓ v)⁻¹ • v := by
        rw [map_smul, smul_eq_mul, smul_smul]
        congr 1
        field_simp
      refine ⟨?_, ?_⟩
      · rw [map_smul, smul_eq_mul]; positivity
      · rw [e]; exact h2
    have hCo : IsOpen C := by
      have hcont : ContinuousOn (fun v : Fin (n + 1) → ℝ => (ℓ v)⁻¹ • v) {v | 0 < ℓ v} :=
        (ℓ.continuous.continuousOn.inv₀ fun v hv => ne_of_gt hv).smul continuousOn_id
      exact hcont.isOpen_inter_preimage (isOpen_lt continuous_const ℓ.continuous) hO'
    have hO : IsOpen (ofCone C) := isOpen_ofCone hC hCo
    have hVO : V ⊆ ofCone C := by
      intro x hx
      obtain ⟨v, hvs, hv0, rfl⟩ := exists_mem_coneSection hℓV hx
      have h1 : ℓ v = 1 := hvs.2
      refine mk_mem_ofCone hv0 ⟨by rw [h1]; exact one_pos, ?_⟩
      rw [h1, inv_one, one_smul]
      exact hVO' hvs
    obtain ⟨l, hl, hVl, hlW⟩ := hII _ hO hVO
    refine ⟨{v | (-l) v < 0}, ⟨-l, neg_ne_zero.2 hl, 0, rfl⟩, ?_, ?_⟩
    · intro v hvs
      have := (mk_mem_openHemisphere hvs.1.1).1 (hVl hvs.1.2)
      simp only [mem_setOf_eq, neg_apply, neg_neg_iff_pos]
      exact this
    · rintro v ⟨hv, hvW⟩
      have hl' : 0 < l v := by simpa using hv
      have hm := hlW ⟨(mk_mem_openHemisphere hvW.1.1).2 hl', hvW.1.2⟩
      rw [mk_mem_ofCone_iff hC] at hm
      have h1 : ℓ v = 1 := hvW.2
      have h2 := hm.2
      rw [h1, inv_one, one_smul] at h2
      exact ⟨h2, hvW⟩

/-- **A compact strict convex part of `S(n)` lies in an open hemisphere** (the proof of
`IsCorpsConvexeS.exists_forall_pos`, which never uses the interior). -/
theorem exists_forall_pos_of_isCompact {W : Set (S n)} (hW : IsStrictConvexPart W)
    (hWc : IsCompact W) : ∃ ℓ : StrongDual ℝ (Fin (n + 1) → ℝ), ∀ v ∈ F W, 0 < ℓ v := by
  have hloc : ∀ X ∈ W, ∃ f : StrongDual ℝ (Fin (n + 1) → ℝ), (∀ v ∈ F W, 0 ≤ f v) ∧
      X ∈ openHemisphere (f : Module.Dual ℝ (Fin (n + 1) → ℝ)) := by
    intro X hX
    obtain ⟨x, hx0, rfl⟩ := exists_isRep X
    have hnx : -x ∉ insert (0 : Fin (n + 1) → ℝ) (F W) := by
      rintro (h | ⟨h0, hk⟩)
      · exact hx0 (neg_eq_zero.1 h)
      · apply hW.2 _ hX
        rwa [neg_mk]
    obtain ⟨f, u, hfu, hf⟩ :=
      geometric_hahn_banach_point_closed hW.1 (isClosed_kPrime hWc.isClosed) hnx
    have hu : u < 0 := by simpa using hf 0 (mem_insert _ _)
    refine ⟨f, fun v hv => ?_, ?_⟩
    · by_contra hneg
      push Not at hneg
      have := hf ((u / f v) • v)
        (mem_insert_of_mem _ (smul_mem_F hv (div_pos_of_neg_of_neg hu hneg)))
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hneg.ne] at this
      exact lt_irrefl _ this
    · rw [mk_mem_openHemisphere]
      have : f (-x) < 0 := hfu.trans hu
      simpa using this
  choose! f hf0 hfX using hloc
  obtain ⟨t, ht⟩ := hWc.elim_finite_subcover
    (fun X : W => openHemisphere (f X : Module.Dual ℝ (Fin (n + 1) → ℝ)))
    (fun X => isOpen_openHemisphere (f X)) (fun X hX => mem_iUnion.2 ⟨⟨X, hX⟩, hfX X hX⟩)
  refine ⟨∑ i ∈ t, f i, fun v hv => ?_⟩
  rw [_root_.sum_apply]
  refine Finset.sum_pos' (fun i _ => hf0 i i.2 v hv) ?_
  obtain ⟨hv0, hvK⟩ := hv
  obtain ⟨i, hi, hiv⟩ := mem_iUnion₂.1 (ht hvK)
  exact ⟨i, hi, by simpa using (mk_mem_openHemisphere hv0).1 hiv⟩

/-- On the cone of a non-empty compact part, a positive form is bounded below by a multiple of
the norm (the proof of `IsCorpsConvexeS.exists_mul_norm_le`). -/
theorem exists_mul_norm_le_of_isCompact {W : Set (S n)} (hWc : IsCompact W) (hne : W.Nonempty)
    {ℓ : StrongDual ℝ (Fin (n + 1) → ℝ)} (hℓ : ∀ v ∈ F W, 0 < ℓ v) :
    ∃ c > 0, ∀ v ∈ F W, c * ‖v‖ ≤ ℓ v := by
  let g : S n → ℝ := fun X => ℓ (homeomorphUnitSphere X : Fin (n + 1) → ℝ)
  have hg : Continuous g :=
    ℓ.continuous.comp (continuous_subtype_val.comp homeomorphUnitSphere.continuous)
  have hgK : ∀ X ∈ W, 0 < g X := by
    intro X hX
    obtain ⟨x, hx0, rfl⟩ := exists_isRep X
    simp only [g, homeomorphUnitSphere_mk]
    exact hℓ _ (smul_mem_F ⟨hx0, hX⟩ (inv_pos.2 (norm_pos_iff.2 hx0)))
  obtain ⟨X₀, hX₀, hmin⟩ := hWc.exists_isMinOn hne hg.continuousOn
  refine ⟨g X₀, hgK X₀ hX₀, fun v hv => ?_⟩
  obtain ⟨hv0, hvK⟩ := hv
  have h1 : g X₀ ≤ g (mk v hv0) := hmin hvK
  simp only [g, homeomorphUnitSphere_mk, map_smul, smul_eq_mul] at h1
  have hn : 0 < ‖v‖ := norm_pos_iff.2 hv0
  rwa [le_inv_mul_iff₀ hn, mul_comm] at h1

/-- The image in the chart `ℓ = 1` of a compact part `W` (`ℓ > 0` on `F(W)`) is compact. -/
theorem isCompact_coneSection {W : Set (S n)} (hWc : IsCompact W) (hne : W.Nonempty)
    {ℓ : StrongDual ℝ (Fin (n + 1) → ℝ)} (hℓ : ∀ v ∈ F W, 0 < ℓ v) :
    IsCompact (coneSection W (ℓ : Module.Dual ℝ _)) := by
  obtain ⟨c, hc, hcn⟩ := exists_mul_norm_le_of_isCompact hWc hne hℓ
  have hBeq : coneSection W (ℓ : Module.Dual ℝ _) = insert 0 (F W) ∩ ℓ ⁻¹' {1} := by
    ext v
    simp only [coneSection, mem_setOf_eq, mem_inter_iff, mem_insert_iff, mem_preimage,
      mem_singleton_iff, ContinuousLinearMap.coe_coe]
    constructor
    · rintro ⟨hv, h1⟩; exact ⟨Or.inr hv, h1⟩
    · rintro ⟨rfl | hv, h1⟩
      · rw [map_zero] at h1; exact absurd h1 zero_ne_one
      · exact ⟨hv, h1⟩
  have hBcl : IsClosed (coneSection W (ℓ : Module.Dual ℝ _)) := by
    rw [hBeq]
    exact (isClosed_kPrime hWc.isClosed).inter (isClosed_singleton.preimage ℓ.continuous)
  have hBbd : Bornology.IsBounded (coneSection W (ℓ : Module.Dual ℝ _)) := by
    refine (Metric.isBounded_closedBall (x := (0 : Fin (n + 1) → ℝ)) (r := 1 / c)).subset ?_
    rintro v ⟨hv, h1⟩
    rw [Metric.mem_closedBall, dist_zero_right, le_div_iff₀ hc, mul_comm]
    have := hcn v hv
    rw [ContinuousLinearMap.coe_coe] at h1
    linarith
  exact Metric.isCompact_of_isClosed_isBounded hBcl hBbd

end ChartTop

end Sphere

open Sphere

/-- **Ch. 3 § 5, Theorem 1′, general form**: for `W` a compact strict convex part of `S(n)` (no
interior needed) and `V ⊆ W` compact, convex, non-empty, I′, II′, III′ are equivalent. -/
theorem reunion_convexes_sphere_of_isCompact {n : ℕ} {V W : Set (S n)}
    (hW : IsStrictConvexPart W) (hWk : IsCompact W)
    (hV : IsCompact V) (hVc : IsConvexPart V) (hne : V.Nonempty) (hVW : V ⊆ W) :
    List.TFAE [ProprieteIS V W, ProprieteIIS V W, ProprieteIIIS V W] := by
  obtain ⟨ℓ, hℓ⟩ := exists_forall_pos_of_isCompact hW hWk
  have hℓV : ∀ v ∈ F V, 0 < ℓ v := fun v hv => hℓ v (F_mono hVW hv)
  have hWc := isCompact_coneSection hWk (hne.mono hVW) hℓ
  have hWconv : Convex ℝ (coneSection W (ℓ : Module.Dual ℝ _)) :=
    (isConvexPart_iff_convex_coneSection hℓ).1 hW.1
  have hVconv : Convex ℝ (coneSection V (ℓ : Module.Dual ℝ _)) :=
    (isConvexPart_iff_convex_coneSection hℓV).1 hVc
  have hVeq : coneSection V (ℓ : Module.Dual ℝ _) = kPrime V ∩ ℓ ⁻¹' {1} := by
    ext v
    simp only [coneSection, kPrime, mem_setOf_eq, mem_inter_iff, mem_insert_iff, mem_preimage,
      mem_singleton_iff, ContinuousLinearMap.coe_coe]
    constructor
    · rintro ⟨hv, h1⟩; exact ⟨Or.inr hv, h1⟩
    · rintro ⟨rfl | hv, h1⟩
      · rw [map_zero] at h1; exact absurd h1 zero_ne_one
      · exact ⟨hv, h1⟩
  have hVcl : IsClosed (coneSection V (ℓ : Module.Dual ℝ _)) := by
    rw [hVeq]
    exact (isClosed_kPrime hV.isClosed).inter (isClosed_singleton.preimage ℓ.continuous)
  have hVcomp : IsCompact (coneSection V (ℓ : Module.Dual ℝ _)) :=
    hWc.of_isClosed_subset hVcl (coneSection_mono hVW _)
  have hVne : (coneSection V (ℓ : Module.Dual ℝ _)).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨v, hv, -⟩ := exists_mem_coneSection hℓV hx
    exact ⟨v, hv⟩
  have hT := reunion_convexes_affine hWc hWconv hVcomp hVconv hVne (coneSection_mono hVW _)
  have h1 := proprieteI_coneSection_iff (ℓ := (ℓ : Module.Dual ℝ _)) hℓ hVW
  have h2 := proprieteII_coneSection_iff hℓ hVW hne
  have h3 := proprieteIS_iff_proprieteIIIS hW (ℓ := (ℓ : Module.Dual ℝ _)) hℓ hV.isClosed hVc hne
  tfae_have 1 ↔ 2 := h1.symm.trans ((hT.out 0 1).trans h2)
  tfae_have 1 ↔ 3 := h3
  tfae_finish

/-- **Ch. 3 § 5, Theorem 1′.** For `W` a convex body of `S(n)` and `V ⊆ W` compact, convex,
non-empty, `I′(V, W)`, `II′(V, W)`, `III′(V, W)` are equivalent. -/
theorem reunion_convexes_sphere {n : ℕ} {V W : Set (S n)} (hW : IsCorpsConvexeS n W)
    (hV : IsCompact V) (hVc : IsConvexPart V) (hne : V.Nonempty) (hVW : V ⊆ W) :
    List.TFAE [ProprieteIS V W, ProprieteIIS V W, ProprieteIIIS V W] :=
  reunion_convexes_sphere_of_isCompact hW.1 hW.2.1 hV hVc hne hVW

/-! ### Instances in `S(2)`: the closed triangle, a closed half of it, a vertex -/

namespace ReunionSphereInstance

open TriangleInstance

/-- The cone of the closed half `x₁ ≤ x₀` of the closed triangle. -/
def demiOrthant : Set (Fin 3 → ℝ) := {v | (∀ i, 0 ≤ v i) ∧ v 1 ≤ v 0}

/-- The closed half `x₁ ≤ x₀` of the closed triangle `simplexS 2` of `S(2)`. -/
def demiTriangle : Set (S 2) := ofCone demiOrthant

theorem isPosCone_demiOrthant : IsPosCone demiOrthant := by
  rintro c hc v ⟨h1, h2⟩
  refine ⟨fun i => ?_, ?_⟩
  · simpa using mul_nonneg hc.le (h1 i)
  · simpa using mul_le_mul_of_nonneg_left h2 hc.le

theorem mk_mem_demiTriangle {v : Fin 3 → ℝ} (hv : v ≠ 0) :
    mk v hv ∈ demiTriangle ↔ (∀ i, 0 ≤ v i) ∧ v 1 ≤ v 0 :=
  mk_mem_ofCone_iff isPosCone_demiOrthant hv

theorem mk_mem_simplexS {v : Fin 3 → ℝ} (hv : v ≠ 0) :
    mk v hv ∈ simplexS 2 ↔ ∀ i, 0 ≤ v i :=
  mk_mem_ofCone_iff (fun _ hc _ hv => orthant_smul hc hv) hv

theorem isClosed_ofCone_of_isClosed {C : Set (Fin 3 → ℝ)} (hC : IsPosCone C)
    (h0 : (0 : Fin 3 → ℝ) ∈ C) (hcl : IsClosed C) : IsClosed (ofCone C) := by
  rw [← isOpen_compl_iff, isOpen_iff_F, F_compl, F_ofCone hC]
  convert hcl.isOpen_compl using 1
  ext v
  simp only [Set.mem_sdiff, mem_compl_iff, mem_singleton_iff, not_and, not_not]
  constructor
  · rintro ⟨hv, h⟩ hC'
    exact hv (h hC')
  · intro hC'
    exact ⟨fun hv => hC' (hv ▸ h0), fun h => absurd h hC'⟩

theorem demiTriangle_subset : demiTriangle ⊆ simplexS 2 :=
  ofCone_subset_ofCone fun _ hv => hv.1

theorem isCompact_demiTriangle : IsCompact demiTriangle := by
  refine (isClosed_ofCone_of_isClosed isPosCone_demiOrthant ⟨fun _ => le_rfl, le_rfl⟩ ?_).isCompact
  simp only [demiOrthant, Set.setOf_and, Set.setOf_forall]
  exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
    (isClosed_le (continuous_apply 1) (continuous_apply 0))

theorem isConvexPart_demiTriangle : IsConvexPart demiTriangle := by
  refine isConvexPart_ofCone_of_cone ?_ isPosCone_demiOrthant
  intro x hx y hy a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · simpa using add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left hx.2 ha, mul_le_mul_of_nonneg_left hy.2 hb]

theorem point11_ne : (![1, 1, 0] : Fin 3 → ℝ) ≠ 0 := fun h => by
  simpa using congrFun h 0

theorem mk_point11_mem : mk ![1, 1, 0] point11_ne ∈ demiTriangle := by
  rw [mk_mem_demiTriangle]
  refine ⟨fun i => ?_, by simp⟩
  fin_cases i <;> simp

theorem demiTriangle_nonempty : demiTriangle.Nonempty := ⟨_, mk_point11_mem⟩

/-- **Instance of `I′`**: the closed half `x₁ ≤ x₀` of the closed triangle. -/
theorem demiTriangle_proprieteIS : ProprieteIS demiTriangle (simplexS 2) := by
  refine ⟨demiTriangle_subset, isConvexPart_demiTriangle, ?_⟩
  have hA : IsPosCone {v : Fin 3 → ℝ | (∀ i, 0 ≤ v i) ∧ v 0 < v 1} := by
    rintro c hc v ⟨h1, h2⟩
    refine ⟨fun i => ?_, ?_⟩
    · simpa using mul_nonneg hc.le (h1 i)
    · simpa using mul_lt_mul_of_pos_left h2 hc
  have e : simplexS 2 \ demiTriangle = ofCone {v : Fin 3 → ℝ | (∀ i, 0 ≤ v i) ∧ v 0 < v 1} := by
    ext x
    induction x using ind with
    | h v hv =>
    rw [Set.mem_sdiff, mk_mem_simplexS hv, mk_mem_demiTriangle hv, mk_mem_ofCone_iff hA hv]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, lt_of_not_ge fun h => h2 ⟨h1, h⟩⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun h => absurd h.2 (not_le.2 h2)⟩
  rw [e]
  refine isConvexPart_ofCone_of_cone ?_ hA
  intro x hx y hy a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · simpa using add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases ha.eq_or_lt with rfl | ha'
    · rw [zero_add] at hab; subst hab; simpa using hy.2
    · nlinarith [mul_lt_mul_of_pos_left hx.2 ha', mul_le_mul_of_nonneg_left hy.2.le hb]

/-- **Theorem 1′, instance**: the closed half of the closed triangle has I′, II′ and III′. -/
theorem demiTriangle_proprietes :
    ProprieteIS demiTriangle (simplexS 2) ∧ ProprieteIIS demiTriangle (simplexS 2) ∧
      ProprieteIIIS demiTriangle (simplexS 2) := by
  have h := reunion_convexes_sphere isCorpsConvexeS_simplexS isCompact_demiTriangle
    isConvexPart_demiTriangle demiTriangle_nonempty demiTriangle_subset
  exact ⟨demiTriangle_proprieteIS, (h.out 0 1).1 demiTriangle_proprieteIS,
    (h.out 0 2).1 demiTriangle_proprieteIS⟩

/-- **Under the reading « an OPEN hemisphere of `L` », `III′` fails** for the closed half of the
closed triangle, although `I′` holds: an open hemisphere containing `s(1, 1, 0)` also contains
`s(1, 1 + t, 0)` for small `t > 0`, a point of the triangle outside the half. -/
theorem demiTriangle_sans_hemisphereOuvert :
    ProprieteIS demiTriangle (simplexS 2) ∧ ¬ ProprieteIIISouvert demiTriangle (simplexS 2) := by
  refine ⟨demiTriangle_proprieteIS, ?_⟩
  rintro ⟨-, l, -, hVe⟩
  have hp := Set.ext_iff.1 hVe (mk ![1, 1, 0] point11_ne) |>.1 mk_point11_mem
  have ha : 0 < l ![1, 1, 0] := (mk_mem_openHemisphere point11_ne).1 hp.2.2
  set a := l ![1, 1, 0] with ha_def
  set b := l ![0, 1, 0] with hb_def
  set t : ℝ := a / (2 * (|b| + 1)) with ht_def
  have hb1 : 0 < |b| + 1 := by positivity
  have ht : 0 < t := by positivity
  have htb : t * |b| < a := by
    rw [ht_def, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg b]
  have eq : (![1, 1 + t, 0] : Fin 3 → ℝ) = ![1, 1, 0] + t • ![0, 1, 0] := by
    ext i; fin_cases i <;> simp
  have hq0 : (![1, 1 + t, 0] : Fin 3 → ℝ) ≠ 0 := fun h => by simpa using congrFun h 0
  have hqW : mk ![1, 1 + t, 0] hq0 ∈ simplexS 2 := by
    rw [mk_mem_simplexS]
    intro i; fin_cases i <;> simp [add_nonneg zero_le_one ht.le]
  have hqL : mk ![1, 1 + t, 0] hq0 ∈ supportK demiTriangle := by
    rw [supportK, mk_mem_linearSubvariety]
    have h11 : (![1, 1, 0] : Fin 3 → ℝ) ∈ F demiTriangle :=
      (mk_mem_iff_mem_F point11_ne).1 mk_point11_mem
    have h10ne : (![1, 0, 0] : Fin 3 → ℝ) ≠ 0 := fun h => by simpa using congrFun h 0
    have h10 : (![1, 0, 0] : Fin 3 → ℝ) ∈ F demiTriangle := by
      refine (mk_mem_iff_mem_F h10ne).1 ((mk_mem_demiTriangle h10ne).2 ⟨fun i => ?_, by simp⟩)
      fin_cases i <;> simp
    have e2 : (![1, 1 + t, 0] : Fin 3 → ℝ) = (1 + t) • ![1, 1, 0] - t • ![1, 0, 0] := by
      ext i; fin_cases i <;> simp
    rw [e2]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span h11))
      (Submodule.smul_mem _ _ (Submodule.subset_span h10))
  have hqH : mk ![1, 1 + t, 0] hq0 ∈ openHemisphere l := by
    rw [mk_mem_openHemisphere, eq, map_add, map_smul, smul_eq_mul]
    have := neg_abs_le b
    nlinarith
  have hqV := (Set.ext_iff.1 hVe _).2 ⟨hqW, hqL, hqH⟩
  have := ((mk_mem_demiTriangle hq0).1 hqV).2
  simp at this
  linarith

/-- **Instance of `I′`**: a vertex of the closed triangle. -/
theorem vertex_proprieteIS : ProprieteIS {vertex (0 : Fin 3)} (simplexS 2) := by
  refine ⟨singleton_subset_iff.2 (single_mem_coneSection (m := 2) 0).1.2, isConvexPart_singleton_pt _, ?_⟩
  set A : Set (Fin 3 → ℝ) := {v | (∀ i, 0 ≤ v i) ∧ (0 < v 1 ∨ 0 < v 2)} with hAdef
  have hA : IsPosCone A := by
    rintro c hc v ⟨h1, h2⟩
    refine ⟨fun i => ?_, ?_⟩
    · simpa using mul_nonneg hc.le (h1 i)
    · simp only [Pi.smul_apply, smul_eq_mul]
      rcases h2 with h | h
      · exact Or.inl (mul_pos hc h)
      · exact Or.inr (mul_pos hc h)
  have hs0 : (Pi.single (0 : Fin 3) (1 : ℝ) : Fin 3 → ℝ) ≠ 0 := by simp
  have e : simplexS 2 \ {vertex (0 : Fin 3)} = ofCone A := by
    ext x
    induction x using ind with
    | h v hv =>
    rw [Set.mem_sdiff, mk_mem_simplexS hv, mk_mem_ofCone_iff hA hv, mem_singleton_iff, vertex,
      mk_eq_mk_iff_exists_pos hv hs0]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      by_contra hn
      push Not at hn
      have hv1 : v 1 = 0 := le_antisymm hn.1 (h1 1)
      have hv2 : v 2 = 0 := le_antisymm hn.2 (h1 2)
      have hv0 : 0 < v 0 := by
        refine lt_of_le_of_ne (h1 0) fun h0 => hv ?_
        ext i; fin_cases i <;> simp [← h0, hv1, hv2]
      refine h2 ⟨(v 0)⁻¹, inv_pos.2 hv0, ?_⟩
      ext i; fin_cases i <;> simp [hv1, hv2, inv_mul_cancel₀ hv0.ne']
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rintro ⟨c, hc, hcv⟩
      have e1 := congrFun hcv 1
      have e2 := congrFun hcv 2
      simp only [Pi.smul_apply, smul_eq_mul] at e1 e2
      rw [Pi.single_eq_of_ne (by decide)] at e1 e2
      rcases h2 with h | h
      · exact (mul_pos hc h).ne' e1
      · exact (mul_pos hc h).ne' e2
  rw [e]
  refine isConvexPart_ofCone_of_cone ?_ hA
  intro x hx y hy a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · simpa using add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases ha.eq_or_lt with rfl | ha'
    · rw [zero_add] at hab; subst hab; simpa using hy.2
    · rcases hx.2 with h | h
      · exact Or.inl (by nlinarith [mul_nonneg hb (hy.1 1)])
      · exact Or.inr (by nlinarith [mul_nonneg hb (hy.1 2)])

/-- **Theorem 1′, instance**: a vertex of the closed triangle has I′, II′ and III′. -/
theorem vertex_proprietes :
    ProprieteIS {vertex (0 : Fin 3)} (simplexS 2) ∧ ProprieteIIS {vertex (0 : Fin 3)} (simplexS 2) ∧
      ProprieteIIIS {vertex (0 : Fin 3)} (simplexS 2) := by
  have h := reunion_convexes_sphere isCorpsConvexeS_simplexS isCompact_singleton
    (isConvexPart_singleton_pt _) (singleton_nonempty _)
    (singleton_subset_iff.2 (single_mem_coneSection (m := 2) 0).1.2)
  exact ⟨vertex_proprieteIS, (h.out 0 1).1 vertex_proprieteIS, (h.out 0 2).1 vertex_proprieteIS⟩

/-- The coordinate form `xᵢ` of `ℝ³`. -/
def projForm (i : Fin 3) : Module.Dual ℝ (Fin 3 → ℝ) := LinearMap.proj i

/-- **Instance of `DemiSphereFermeeDe`**: the closed hemisphere `x₀ ≥ x₁` of `S(2)`, as a closed
hemisphere of the linear subvariety `S(2)` itself. -/
theorem demiSphereFermeeDe_univ :
    DemiSphereFermeeDe (univ : Set (S 2))
      (univ ∩ closedHemisphere (projForm 0 - projForm 1)) := by
  have h0 : (Pi.single (0 : Fin 3) (1 : ℝ) : Fin 3 → ℝ) ≠ 0 := by simp
  refine ⟨_, ⟨Pi.single 0 1, ⟨h0, mem_univ _⟩, ?_⟩, rfl⟩
  simp [projForm]

/-- **Instance of `DemiSphereDe`**. -/
theorem demiSphereDe_univ :
    DemiSphereDe (univ : Set (S 2))
      (univ ∩ closedHemisphere (projForm 0 - projForm 1)) :=
  demiSphereFermeeDe_univ.demiSphereDe

/-- **Instance of `ProprieteIIISlarge`**. -/
theorem demiTriangle_proprieteIIISlarge : ProprieteIIISlarge demiTriangle (simplexS 2) :=
  demiTriangle_proprietes.2.2.large

/-- **Instance of `ProprieteIIISouvert`**: `V = W`, the triangle itself, is cut out of `W` by the
open hemisphere `∑ xᵢ > 0`. -/
theorem simplexS_proprieteIIISouvert : ProprieteIIISouvert (simplexS 2) (simplexS 2) := by
  have hI : ProprieteIS (simplexS 2) (simplexS 2) := by
    refine ⟨subset_rfl, isCorpsConvexeS_simplexS.1.1, ?_⟩
    rw [sdiff_self]
    show Convex ℝ (insert 0 (F (∅ : Set (S 2))))
    have : F (∅ : Set (S 2)) = ∅ := by ext v; simp [F]
    rw [this, insert_empty_eq]
    exact convex_singleton 0
  have hIII := proprieteIIIS_of_proprieteIS isCorpsConvexeS_simplexS.1
    (fun v hv => sumForm_pos hv) (isCorpsConvexeS_simplexS (m := 2)).2.1.isClosed
    ⟨_, (single_mem_coneSection (m := 2) 0).1.2⟩ hI
  have hv := single_mem_coneSection (m := 2) 0
  refine ⟨hIII.1, sumForm 2, ⟨Pi.single 0 1, ?_, (sumForm_pos hv.1).ne'⟩, ?_⟩
  · rw [supportK, F_linearSubvariety]
    exact ⟨Submodule.subset_span hv.1, hv.1.1⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨v, hv0, rfl⟩ := exists_isRep x
      exact ⟨hx, subset_supportK _ hx, (mk_mem_openHemisphere hv0).2 (sumForm_pos ⟨hv0, hx⟩)⟩
    · exact fun hx => hx.1

end ReunionSphereInstance

end Benzecri
