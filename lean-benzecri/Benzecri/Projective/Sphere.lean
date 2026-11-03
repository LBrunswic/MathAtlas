import Mathlib.LinearAlgebra.Ray
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Analysis.Normed.Module.Ray
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# `Benzecri.Projective.Sphere` — the projective sphere `S(E)` (Ch. 1 § 1, Déf. 3)

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 1 § 1, journal p. 234; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch1.tex`. Package WP-45a (wave 1, layer L0).

* **`bzdef:c1s1d3_sphere`** — `benzecri1960_ch1.tex:167` (Déf. 3, l.167–184, p. 234). Certified
  under DEC-114: `S(E)` and `P(E)` as the quotients of `E - {O}` by `ℝ⁺` and `ℝ*`, the projection `s`,
  the correspondence `F`, and the quotient topologies of both, for every topological vector space
  structure on `E`; the default topology (« la topologie localement convexe la plus fine ») is
  certified on `ℝⁿ`, where it is the product topology
  (`Benzecri.isLeast_pi_locallyConvexTopology`), the one `S(n)` is built from
  (`Benzecri.S.topology_eq`). See SCOPE for the infinite-dimensional default.

> Soit $E$ un espace vectoriel sur $\R$. Le groupe multiplicatif $\R^+$ (resp.
> $\R^*=\R-\{O\}$) opère sur $E$ comme groupe des homothéties positives (resp. des homothéties non
> nulles).
>
> Nous appellerons *sphère* associée à $E$, et noterons $S(E)$ (resp. *espace projectif*, $P(E)$,
> associé à $E$), le quotient de $E-\{O\}$ par $\R^+$ (resp. $\R^*$), $O$ étant l'origine de $E$.
>
> Quand aucune autre structure topologique ne sera spécifiée sur $E$, nous supposerons $E$ muni de
> la topologie localement convexe la plus fine.
>
> Une structure d'espace vectoriel topologique sur $E$ induit une topologie sur $E-\{O\}$ : $S(E)$
> [resp. $P(E)$] sera muni de la topologie quotient.
>
> Nous noterons $s$ la projection canonique de $E-\{O\}$ sur $S(E)$; nous noterons $F$ la
> correspondance qui, à une partie de $S(E)$, associe son image réciproque dans $E-\{O\}$.

and, p. 236: « $S(\R^n)$ sera appelée la sphère projective de dimension $(n-1)$ et notée
$S(n-1)$. » (`benzecri1960_ch1.tex:278`).

## The model (DEC-113, plan F1)

`Benzecri.Sphere E` is Mathlib's `Module.Ray ℝ E` — the nonzero vectors modulo `SameRay`, i.e.
modulo the positive homotheties (`Sphere.mk_eq_mk_iff_exists_pos`) — as a type synonym carrying
the **quotient topology** of `{v : E // v ≠ 0}` (`Sphere.isQuotientMap_s`). It is never Mathlib's
`Projectivization` (`ℙ ℝ E`, Benzécri's `P(E)`, here the synonym `Benzecri.ProjSpace E`); the
2-to-1 map `Sphere.toProjectivization` identifies exactly antipodal rays
(`Sphere.toProjectivization_eq_iff`).

Main declarations:
* `Sphere.s` (the projection `s`), `Sphere.F` (the correspondence `F`), with `F` injective and
  stable under positive homotheties; `Sphere.ofCone` (the set of rays of a cone, `F ∘ ofCone`);
* `Sphere.isQuotientMap_s`, `Sphere.isOpenMap_s` (`s` is open as soon as the homotheties are
  continuous), `Sphere.isOpen_iff_F`;
* the antipodal map `Sphere.antipodal : Sphere E ≃ₜ Sphere E`, fixed-point free;
* the action of continuous linear equivalences, `Sphere.map : (E ≃L[ℝ] E') → Sphere E ≃ₜ Sphere E'`,
  functorial; for finite-dimensional `E` the action of every linear automorphism
  (`Sphere.continuous_smul_linearEquiv`, the `MulAction (E ≃ₗ[ℝ] E)` of `Module.Ray`);
* **`Sphere.homeomorphUnitSphere : Sphere E ≃ₜ Metric.sphere (0 : E) 1`** for every real normed
  space `E` (no finite dimension needed), `x ↦ ‖v‖⁻¹ • v`;
* `T2Space (Sphere E)` for normed `E`, `CompactSpace (Sphere E)` for finite-dimensional normed `E`;
* **`P(E)`**: `Benzecri.ProjSpace E`, Mathlib's `Projectivization ℝ E` as a type synonym carrying the
  quotient topology of `E - {O}` (`ProjSpace.isQuotientMap_p`, `ProjSpace.p_eq_p_iff`: the quotient by
  `ℝ*`); the 2-to-1 map `Sphere.toProjectivization` identifies exactly antipodal rays
  (`Sphere.toProjectivization_eq_iff`), and **the two quotient topologies agree**: the one from
  `E - {O}` is the one from `S(E)` through the antipodal quotient
  (`Sphere.coinduced_toProjectivization`, `Sphere.isQuotientMap_toProjectivization`);
* **the default topology**: `Benzecri.isLeast_pi_locallyConvexTopology` (the product topology of
  `ℝⁿ` is the finest locally convex topology), `Benzecri.isLeast_pi_vectorSpaceTopology` (indeed the
  finest vector-space topology), `Benzecri.pi_le_of_isTopologicalAddGroup`, and for any
  finite-dimensional `E`, `Benzecri.le_of_t2_of_finiteDimensional` (a Hausdorff vector-space
  topology is the finest vector-space topology);
* the index convention `Benzecri.S n = Sphere (Fin (n + 1) → ℝ)` (Benzécri's `S(n) = S(ℝⁿ⁺¹)`),
  compact, Hausdorff, nonempty, homeomorphic to the Euclidean unit sphere of `ℝⁿ⁺¹`, and carrying the
  quotient topology of the default topology of `ℝⁿ⁺¹` (`Benzecri.S.topology_eq`).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `E` a real vector space | ✓ carried (`[AddCommGroup E] [Module ℝ E]`) |
| a topological vector space structure on `E` (« Une structure d'espace vectoriel topologique ») | ⚠ weakened: the quotient topologies need only `[TopologicalSpace E]`; openness of `s` needs `[ContinuousConstSMul ℝ E]`, the antipodal map `[ContinuousNeg E]` |
| by default, the finest locally convex topology | ✓ carried for `E = ℝⁿ`, every space Ch. 1 equips with it: the finest locally convex (indeed vector-space) topology of `ℝⁿ` is the product topology (`isLeast_pi_locallyConvexTopology`), which `S(n)` carries; not constructed for an infinite-dimensional `E` (SCOPE) |
| `P(E)` with the quotient topology | ✓ carried (`ProjSpace`, coinduced from `E - {O}`; equal to the topology through `S(E)`) |
| `S(E) ≃ₜ` unit sphere (DEC-113: "in finite dimension") | ⚠ weakened: proved for every real normed space |

## SCOPE (disclosed)

* The mark rests on DEC-114: Déf. 3 is certified with the lemma that the product topology on `ℝⁿ` is
  the finest locally convex one. For an infinite-dimensional `E` the finest locally convex topology is
  not constructed (Mathlib has none); every statement here is for the topology `E` is given, and
  Chapter 1 equips only `ℝⁿ` with the default.
* `P(E)` is `ProjSpace E`, a synonym of Mathlib's `ℙ ℝ E` (as `Sphere E` is of `Module.Ray ℝ E`), so
  the quotient topology is not an orphan instance on a Mathlib type.
* The action of a linear automorphism is continuous for every continuous linear equivalence
  (`Sphere.map`), and for every linear equivalence in finite dimension; joint continuity of the
  action of `GL` (with a topology on `GL`) is not stated.
* Four names of `namespace Benzecri.Sphere` that would shadow root lemmas are `protected`:
  `Sphere.map_neg`, `Sphere.neg_ne_self`, `Sphere.continuous_neg`, `Sphere.normalize`; the homothety
  of `E - {O}` is `Sphere.homothetyNZ` (`Benzecri.homothety` is `ℝˣ →* GL(E)`, `Projective/Groups`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Topology

namespace Benzecri

/-- **Benzécri's sphere `S(E)`** (Déf. 3, `bzdef:c1s1d3_sphere`, p. 234): the quotient of
`E - {O}` by the multiplicative group `ℝ⁺` of positive homotheties, i.e. Mathlib's `Module.Ray ℝ E`
(nonzero vectors modulo `SameRay`), as a type synonym that carries the quotient topology. -/
def Sphere (E : Type*) [AddCommGroup E] [Module ℝ E] : Type _ := Module.Ray ℝ E

namespace Sphere

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The point of `S(E)` defined by a nonzero vector (`s(v)` in Benzécri's notation). -/
def mk (v : E) (hv : v ≠ 0) : Sphere E := rayOfNeZero ℝ v hv

/-- **The canonical projection `s : E - {O} → S(E)`** (Déf. 3, « Nous noterons $s$ la projection
canonique de $E-\{O\}$ sur $S(E)$ »). -/
def s : {v : E // v ≠ 0} → Sphere E := fun v => mk v.1 v.2

@[simp] theorem s_apply (v : {v : E // v ≠ 0}) : s v = mk v.1 v.2 := rfl

/-- Induction principle: every point of `S(E)` is `s(v)` for a nonzero `v`. -/
@[elab_as_elim]
theorem ind {C : Sphere E → Prop} (h : ∀ (v : E) (hv : v ≠ 0), C (mk v hv)) (x : Sphere E) :
    C x :=
  Module.Ray.ind ℝ h x

theorem s_surjective : Function.Surjective (s : {v : E // v ≠ 0} → Sphere E) := by
  intro x
  induction x using ind with
  | h v hv => exact ⟨⟨v, hv⟩, rfl⟩

theorem mk_eq_mk_iff {v w : E} (hv : v ≠ 0) (hw : w ≠ 0) :
    mk v hv = mk w hw ↔ SameRay ℝ v w :=
  ray_eq_iff hv hw

/-- `S(E)` is the quotient of `E - {O}` by the **positive homotheties** (Déf. 3): two nonzero
vectors have the same image iff one is a positive multiple of the other. -/
theorem mk_eq_mk_iff_exists_pos {v w : E} (hv : v ≠ 0) (hw : w ≠ 0) :
    mk v hv = mk w hw ↔ ∃ c : ℝ, 0 < c ∧ c • v = w := by
  rw [mk_eq_mk_iff, exists_pos_left_iff_sameRay hv hw]

@[simp] theorem mk_smul {v : E} (hv : v ≠ 0) {c : ℝ} (hc : 0 < c) (hcv : c • v ≠ 0) :
    mk (c • v) hcv = mk v hv :=
  ray_pos_smul hv hc hcv

theorem smul_ne_zero_of_pos {v : E} (hv : v ≠ 0) {c : ℝ} (hc : 0 < c) : c • v ≠ 0 :=
  smul_ne_zero hc.ne' hv

/-- A function on nonzero vectors invariant under positive homotheties descends to `S(E)`. -/
def lift {α : Sort*} (f : {v : E // v ≠ 0} → α)
    (hf : ∀ v w : {v : E // v ≠ 0}, SameRay ℝ (v : E) w → f v = f w) : Sphere E → α :=
  Quotient.lift (fun v : RayVector ℝ E => f ⟨v.1, v.2⟩) fun v w h => hf ⟨v.1, v.2⟩ ⟨w.1, w.2⟩ h

@[simp] theorem lift_mk {α : Sort*} (f : {v : E // v ≠ 0} → α) (hf) (v : E) (hv : v ≠ 0) :
    lift f hf (mk v hv) = f ⟨v, hv⟩ := rfl

theorem lift_comp_s {α : Sort*} (f : {v : E // v ≠ 0} → α) (hf) : lift f hf ∘ s = f := rfl

/-! ### The correspondence `F` -/

/-- **The correspondence `F`** (Déf. 3, « nous noterons $F$ la correspondance qui, à une partie de
$S(E)$, associe son image réciproque dans $E-\{O\}$ »), with values in subsets of `E`. -/
def F (A : Set (Sphere E)) : Set E := {v | ∃ hv : v ≠ 0, mk v hv ∈ A}

theorem mem_F {A : Set (Sphere E)} {v : E} : v ∈ F A ↔ ∃ hv : v ≠ 0, mk v hv ∈ A := Iff.rfl

theorem mk_mem_iff_mem_F {A : Set (Sphere E)} {v : E} (hv : v ≠ 0) : mk v hv ∈ A ↔ v ∈ F A :=
  ⟨fun h => ⟨hv, h⟩, fun ⟨_, h⟩ => h⟩

theorem zero_notMem_F (A : Set (Sphere E)) : (0 : E) ∉ F A := fun ⟨h, _⟩ => h rfl

theorem F_subset_compl_zero (A : Set (Sphere E)) : F A ⊆ {0}ᶜ := fun _ ⟨h, _⟩ => h

/-- `F(A)` is the image of the preimage `s⁻¹(A)` in `E`. -/
theorem F_eq_image (A : Set (Sphere E)) : F A = Subtype.val '' (s ⁻¹' A) := by
  ext v
  constructor
  · rintro ⟨hv, h⟩
    exact ⟨⟨v, hv⟩, h, rfl⟩
  · rintro ⟨⟨w, hw⟩, h, rfl⟩
    exact ⟨hw, h⟩

theorem s_preimage_eq (A : Set (Sphere E)) : s ⁻¹' A = Subtype.val ⁻¹' F A := by
  ext ⟨v, hv⟩
  exact (mk_mem_iff_mem_F hv)

/-- `F(A)` is stable under the positive homotheties. -/
theorem smul_mem_F {A : Set (Sphere E)} {v : E} (hv : v ∈ F A) {c : ℝ} (hc : 0 < c) :
    c • v ∈ F A := by
  obtain ⟨hv0, h⟩ := hv
  exact ⟨smul_ne_zero_of_pos hv0 hc, by rwa [mk_smul hv0 hc]⟩

theorem F_mono {A B : Set (Sphere E)} (h : A ⊆ B) : F A ⊆ F B := fun _ ⟨hv, hA⟩ => ⟨hv, h hA⟩

theorem F_subset_F_iff {A B : Set (Sphere E)} : F A ⊆ F B ↔ A ⊆ B := by
  refine ⟨fun h x hx => ?_, F_mono⟩
  induction x using ind with
  | h v hv => exact (h ⟨hv, hx⟩).2

/-- `F` is injective: a part of `S(E)` is determined by its cone. -/
theorem F_injective : Function.Injective (F : Set (Sphere E) → Set E) := fun _ _ h =>
  (F_subset_F_iff.1 h.le).antisymm (F_subset_F_iff.1 h.ge)

@[simp] theorem F_empty : F (∅ : Set (Sphere E)) = ∅ := by
  ext v; simp [mem_F]

@[simp] theorem F_univ : F (univ : Set (Sphere E)) = {0}ᶜ := by
  ext v; simp [mem_F]

theorem F_union (A B : Set (Sphere E)) : F (A ∪ B) = F A ∪ F B := by
  ext v
  simp only [mem_F, mem_union]
  constructor
  · rintro ⟨hv, h | h⟩
    exacts [Or.inl ⟨hv, h⟩, Or.inr ⟨hv, h⟩]
  · rintro (⟨hv, h⟩ | ⟨hv, h⟩)
    exacts [⟨hv, Or.inl h⟩, ⟨hv, Or.inr h⟩]

theorem F_inter (A B : Set (Sphere E)) : F (A ∩ B) = F A ∩ F B := by
  ext v
  simp only [mem_F, mem_inter_iff]
  constructor
  · rintro ⟨hv, h1, h2⟩
    exact ⟨⟨hv, h1⟩, ⟨hv, h2⟩⟩
  · rintro ⟨⟨hv, h1⟩, ⟨_, h2⟩⟩
    exact ⟨hv, h1, h2⟩

theorem F_compl (A : Set (Sphere E)) : F Aᶜ = {0}ᶜ \ F A := by
  ext v
  simp only [mem_F, mem_compl_iff, mem_sdiff, mem_singleton_iff]
  constructor
  · rintro ⟨hv, h⟩
    exact ⟨hv, fun ⟨_, h'⟩ => h h'⟩
  · rintro ⟨hv, h⟩
    exact ⟨hv, fun h' => h ⟨hv, h'⟩⟩

/-! ### The rays of a cone -/

/-- The set of rays of a subset `C ⊆ E`: `s(C - {O})`. -/
def ofCone (C : Set E) : Set (Sphere E) := s '' (Subtype.val ⁻¹' C)

theorem mk_mem_ofCone {C : Set E} {v : E} (hv : v ≠ 0) (h : v ∈ C) : mk v hv ∈ ofCone C :=
  ⟨⟨v, hv⟩, h, rfl⟩

theorem mem_ofCone {C : Set E} {x : Sphere E} :
    x ∈ ofCone C ↔ ∃ (v : E) (hv : v ≠ 0), v ∈ C ∧ mk v hv = x := by
  constructor
  · rintro ⟨⟨v, hv⟩, h, rfl⟩
    exact ⟨v, hv, h, rfl⟩
  · rintro ⟨v, hv, h, rfl⟩
    exact mk_mem_ofCone hv h

/-- For a set `C` stable under the positive homotheties, `F(s(C - {O})) = C - {O}`. -/
theorem F_ofCone {C : Set E} (hC : ∀ c : ℝ, 0 < c → ∀ v ∈ C, c • v ∈ C) :
    F (ofCone C) = C \ {0} := by
  ext v
  constructor
  · rintro ⟨hv, ⟨⟨w, hw⟩, hwC, hwv⟩⟩
    refine ⟨?_, hv⟩
    obtain ⟨c, hc, rfl⟩ := (mk_eq_mk_iff_exists_pos hw hv).1 hwv
    exact hC c hc w hwC
  · rintro ⟨hvC, hv⟩
    exact ⟨hv, mk_mem_ofCone hv hvC⟩

theorem mk_mem_ofCone_iff {C : Set E} (hC : ∀ c : ℝ, 0 < c → ∀ v ∈ C, c • v ∈ C) {v : E}
    (hv : v ≠ 0) : mk v hv ∈ ofCone C ↔ v ∈ C := by
  rw [mk_mem_iff_mem_F, F_ofCone hC]
  simp [hv]

@[simp] theorem ofCone_F (A : Set (Sphere E)) : ofCone (F A) = A := by
  ext x
  induction x using ind with
  | h v hv =>
    rw [mk_mem_ofCone_iff (fun c hc w hw => smul_mem_F hw hc) hv, mk_mem_iff_mem_F]

/-! ### The quotient topology -/

section Topology

variable [TopologicalSpace E]

/-- **The quotient topology** of `S(E)` (Déf. 3, « $S(E)$ sera muni de la topologie quotient »):
coinduced from `E - {O}` by `s`. -/
instance instTopologicalSpace : TopologicalSpace (Sphere E) :=
  TopologicalSpace.coinduced s inferInstance

/-- `s : E - {O} → S(E)` is a quotient map. -/
theorem isQuotientMap_s : IsQuotientMap (s : {v : E // v ≠ 0} → Sphere E) :=
  ⟨⟨rfl⟩, s_surjective⟩

theorem continuous_s : Continuous (s : {v : E // v ≠ 0} → Sphere E) :=
  isQuotientMap_s.continuous

theorem continuous_mk_comp {X : Type*} [TopologicalSpace X] {f : X → E} (hf : Continuous f)
    (hf0 : ∀ x, f x ≠ 0) : Continuous fun x => mk (f x) (hf0 x) :=
  continuous_s.comp (hf.subtype_mk hf0)

theorem isOpen_iff {A : Set (Sphere E)} : IsOpen A ↔ IsOpen (s ⁻¹' A) := isOpen_coinduced

/-- A continuous function on `E - {O}` invariant under positive homotheties induces a continuous
function on `S(E)`. -/
theorem continuous_lift {X : Type*} [TopologicalSpace X] (f : {v : E // v ≠ 0} → X)
    (hf : ∀ v w : {v : E // v ≠ 0}, SameRay ℝ (v : E) w → f v = f w) (hc : Continuous f) :
    Continuous (lift f hf) :=
  isQuotientMap_s.continuous_iff.2 hc

/-- **Openness through `F`**: when `{O}` is closed, a part `A ⊆ S(E)` is open iff its cone `F(A)` is
open in `E`. -/
theorem isOpen_iff_F [T1Space E] {A : Set (Sphere E)} : IsOpen A ↔ IsOpen (F A) := by
  have hopen : IsOpen ({0}ᶜ : Set E) := isOpen_compl_singleton
  rw [isOpen_iff, s_preimage_eq]
  constructor
  · intro h
    have := hopen.isOpenEmbedding_subtypeVal.isOpenMap _ h
    convert this using 1
    ext v
    exact ⟨fun hv => ⟨⟨v, F_subset_compl_zero A hv⟩, hv, rfl⟩, fun ⟨_, hv, h⟩ => h ▸ hv⟩
  · exact fun h => h.preimage continuous_subtype_val

theorem isOpen_ofCone [T1Space E] {C : Set E} (hC : ∀ c : ℝ, 0 < c → ∀ v ∈ C, c • v ∈ C)
    (hCo : IsOpen C) : IsOpen (ofCone C) := by
  rw [isOpen_iff_F, F_ofCone hC]
  exact hCo.sdiff isClosed_singleton

section Homotheties

variable [ContinuousConstSMul ℝ E]

/-- The homothety of ratio `c > 0` on `E - {O}` (named `homothetyNZ`, for *nonzero vectors*, to
keep it apart from `Benzecri.homothety : ℝˣ →* GL(E)` of `Projective/Groups`). -/
def homothetyNZ (c : ℝ) (hc : 0 < c) : {v : E // v ≠ 0} → {v : E // v ≠ 0} :=
  fun v => ⟨c • v.1, smul_ne_zero_of_pos v.2 hc⟩

theorem continuous_homothetyNZ (c : ℝ) (hc : 0 < c) : Continuous (homothetyNZ (E := E) c hc) :=
  ((continuous_const_smul c).comp continuous_subtype_val).subtype_mk _

omit [TopologicalSpace E] [ContinuousConstSMul ℝ E] in
theorem s_preimage_image (U : Set {v : E // v ≠ 0}) :
    s ⁻¹' (s '' U) = ⋃ (c : ℝ) (hc : 0 < c), homothetyNZ c hc ⁻¹' U := by
  ext ⟨w, hw⟩
  simp only [mem_preimage, mem_image, mem_iUnion]
  constructor
  · rintro ⟨⟨u, hu⟩, huU, huw⟩
    obtain ⟨c, hc, rfl⟩ := (mk_eq_mk_iff_exists_pos hw hu).1 huw.symm
    exact ⟨c, hc, huU⟩
  · rintro ⟨c, hc, h⟩
    exact ⟨_, h, mk_smul hw hc _⟩

/-- **`s` is an open map** as soon as the homotheties of `E` are continuous. -/
theorem isOpenMap_s : IsOpenMap (s : {v : E // v ≠ 0} → Sphere E) := by
  intro U hU
  rw [isOpen_iff, s_preimage_image]
  exact isOpen_iUnion fun c => isOpen_iUnion fun hc => hU.preimage (continuous_homothetyNZ c hc)

end Homotheties

end Topology

/-! ### The antipodal map -/

instance : InvolutiveNeg (Sphere E) := inferInstanceAs (InvolutiveNeg (Module.Ray ℝ E))

theorem neg_mk (v : E) (hv : v ≠ 0) : -mk v hv = mk (-v) (neg_ne_zero.2 hv) := rfl

/-- No point is its own antipode (diametrically opposite points, p. 234, example after Déf. 4, are
`x, -x`: see `Benzecri.Sphere.linearSubvariety_span_singleton` in `Projective/Subvariety`).
Protected: it would shadow the root `neg_ne_self` inside `namespace Benzecri.Sphere`. -/
protected theorem neg_ne_self (x : Sphere E) : -x ≠ x := fun h => Module.Ray.ne_neg_self x h.symm

theorem F_neg (A : Set (Sphere E)) : F (-A) = -F A := by
  ext v
  simp only [mem_F, Set.mem_neg]
  constructor
  · rintro ⟨hv, h⟩
    refine ⟨neg_ne_zero.2 hv, ?_⟩
    rwa [← neg_mk]
  · rintro ⟨hv, h⟩
    refine ⟨neg_ne_zero.1 hv, ?_⟩
    have : -mk v (neg_ne_zero.1 hv) = mk (-v) hv := neg_mk _ _
    rw [this]; exact h

section Antipodal

variable [TopologicalSpace E] [ContinuousNeg E]

/-- The antipodal map is continuous. Protected: it would shadow the root `continuous_neg`. -/
protected theorem continuous_neg : Continuous (fun x : Sphere E => -x) := by
  have : (fun x : Sphere E => -x) =
      lift (fun v => mk (-v.1) (neg_ne_zero.2 v.2)) (fun v w h => by
        simpa [mk_eq_mk_iff] using h) := by
    funext x
    induction x using ind with
    | h v hv => rfl
  rw [this]
  exact continuous_lift _ _ (continuous_mk_comp (continuous_subtype_val.neg) _)

/-- **The antipodal map** of `S(E)`, a fixed-point-free involutive homeomorphism. -/
def antipodal : Sphere E ≃ₜ Sphere E where
  toFun x := -x
  invFun x := -x
  left_inv x := neg_neg x
  right_inv x := neg_neg x
  continuous_toFun := Sphere.continuous_neg
  continuous_invFun := Sphere.continuous_neg

@[simp] theorem antipodal_apply (x : Sphere E) : antipodal x = -x := rfl

end Antipodal

/-! ### The action of linear automorphisms -/

section Map

variable {E' E'' : Type*} [AddCommGroup E'] [Module ℝ E'] [AddCommGroup E''] [Module ℝ E'']

/-- The bijection `S(E) ≃ S(E')` induced by a linear equivalence (Mathlib's `Module.Ray.map`). -/
def mapEquiv (e : E ≃ₗ[ℝ] E') : Sphere E ≃ Sphere E' := Module.Ray.map e

@[simp] theorem mapEquiv_mk (e : E ≃ₗ[ℝ] E') (v : E) (hv : v ≠ 0) :
    mapEquiv e (mk v hv) = mk (e v) (e.map_ne_zero_iff.2 hv) := rfl

theorem mapEquiv_neg (e : E ≃ₗ[ℝ] E') (x : Sphere E) : mapEquiv e (-x) = -mapEquiv e x :=
  Module.Ray.map_neg e x

theorem mapEquiv_symm (e : E ≃ₗ[ℝ] E') : (mapEquiv e).symm = mapEquiv e.symm := rfl

theorem mapEquiv_trans (e : E ≃ₗ[ℝ] E') (e' : E' ≃ₗ[ℝ] E'') :
    mapEquiv (e.trans e') = (mapEquiv e).trans (mapEquiv e') := by
  ext x
  induction x using ind with
  | h v hv => rfl

@[simp] theorem mapEquiv_refl : mapEquiv (LinearEquiv.refl ℝ E) = Equiv.refl _ :=
  Module.Ray.map_refl

variable [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace E'']

theorem continuous_mapEquiv (e : E ≃ₗ[ℝ] E') (he : Continuous e) : Continuous (mapEquiv e) := by
  have : (mapEquiv e : Sphere E → Sphere E') =
      lift (fun v => mk (e v.1) (e.map_ne_zero_iff.2 v.2)) (fun v w h => by
        simpa [mk_eq_mk_iff] using h.map e.toLinearMap) := by
    funext x
    induction x using ind with
    | h v hv => rfl
  rw [this]
  exact continuous_lift _ _ (continuous_mk_comp (he.comp continuous_subtype_val) _)

/-- **The action of a continuous linear equivalence on the sphere**: a homeomorphism
`S(E) ≃ₜ S(E')`. -/
def map (e : E ≃L[ℝ] E') : Sphere E ≃ₜ Sphere E' where
  toEquiv := mapEquiv e.toLinearEquiv
  continuous_toFun := continuous_mapEquiv _ e.continuous
  continuous_invFun := continuous_mapEquiv e.symm.toLinearEquiv e.symm.continuous

@[simp] theorem map_mk (e : E ≃L[ℝ] E') (v : E) (hv : v ≠ 0) :
    map e (mk v hv) = mk (e v) (e.map_ne_zero_iff.2 hv) := rfl

/-- `map e` commutes with the antipodal map. Protected: it would shadow the root `map_neg`. -/
protected theorem map_neg (e : E ≃L[ℝ] E') (x : Sphere E) : map e (-x) = -map e x :=
  mapEquiv_neg _ x

@[simp] theorem map_refl : map (ContinuousLinearEquiv.refl ℝ E) = Homeomorph.refl _ := by
  ext x
  induction x using ind with
  | h v hv => rfl

theorem map_trans (e : E ≃L[ℝ] E') (e' : E' ≃L[ℝ] E'') :
    map (e.trans e') = (map e).trans (map e') := by
  ext x
  induction x using ind with
  | h v hv => rfl

theorem map_symm (e : E ≃L[ℝ] E') : (map e).symm = map e.symm := rfl

/-- The action of a linear automorphism (`Module.Ray`'s `MulAction (E ≃ₗ[ℝ] E)`) is `mapEquiv`. -/
instance : MulAction (E ≃ₗ[ℝ] E) (Sphere E) :=
  inferInstanceAs (MulAction (E ≃ₗ[ℝ] E) (Module.Ray ℝ E))

omit [TopologicalSpace E] in
theorem smul_eq_mapEquiv (g : E ≃ₗ[ℝ] E) (x : Sphere E) : g • x = mapEquiv g x := rfl

omit [TopologicalSpace E] in
@[simp] theorem smul_mk (g : E ≃ₗ[ℝ] E) (v : E) (hv : v ≠ 0) :
    g • mk v hv = mk (g v) (g.map_ne_zero_iff.2 hv) := rfl

/-- In finite dimension (Hausdorff topological vector space), **every linear automorphism acts
continuously** on `S(E)`. -/
theorem continuous_smul_linearEquiv [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [FiniteDimensional ℝ E] (g : E ≃ₗ[ℝ] E) : Continuous fun x : Sphere E => g • x :=
  continuous_mapEquiv g g.toLinearMap.continuous_of_finiteDimensional

instance [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] [FiniteDimensional ℝ E] :
    ContinuousConstSMul (E ≃ₗ[ℝ] E) (Sphere E) :=
  ⟨continuous_smul_linearEquiv⟩

end Map

/-! ### The homeomorphism with the unit sphere -/

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem ne_zero_of_mem_unitSphere (u : Metric.sphere (0 : E) 1) : (u : E) ≠ 0 := by
  intro h
  have := u.2
  simp [h] at this

/-- Normalisation `v ↦ ‖v‖⁻¹ • v` on `E - {O}`. Protected: it would shadow the root `normalize`. -/
protected def normalize (v : {v : E // v ≠ 0}) : Metric.sphere (0 : E) 1 :=
  ⟨‖v.1‖⁻¹ • v.1, by
    simp [norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.2 v.2)]⟩

theorem continuous_normalize : Continuous (Sphere.normalize (E := E)) :=
  (((continuous_norm.comp continuous_subtype_val).inv₀ fun v => norm_ne_zero_iff.2 v.2).smul
    continuous_subtype_val).subtype_mk _

theorem normalize_eq_of_sameRay (v w : {v : E // v ≠ 0}) (h : SameRay ℝ (v : E) w) :
    Sphere.normalize v = Sphere.normalize w :=
  Subtype.ext (h.inv_norm_smul_eq v.2 w.2)

/-- **`S(E)` is homeomorphic to the unit sphere** of any real normed space `E` (DEC-113; plan F1):
`s(v) ↦ ‖v‖⁻¹ • v`, with inverse `u ↦ s(u)`. -/
def homeomorphUnitSphere : Sphere E ≃ₜ Metric.sphere (0 : E) 1 where
  toFun := lift Sphere.normalize normalize_eq_of_sameRay
  invFun u := mk (u : E) (ne_zero_of_mem_unitSphere u)
  left_inv x := by
    induction x using ind with
    | h v hv =>
      change mk (‖v‖⁻¹ • v) _ = mk v hv
      exact mk_smul hv (inv_pos.2 (norm_pos_iff.2 hv)) _
  right_inv u := by
    apply Subtype.ext
    change ‖(u : E)‖⁻¹ • (u : E) = u
    simp [norm_eq_of_mem_sphere u]
  continuous_toFun := continuous_lift _ _ continuous_normalize
  continuous_invFun := continuous_mk_comp continuous_subtype_val _

@[simp] theorem homeomorphUnitSphere_mk (v : E) (hv : v ≠ 0) :
    (homeomorphUnitSphere (mk v hv) : E) = ‖v‖⁻¹ • v := rfl

@[simp] theorem homeomorphUnitSphere_symm_apply (u : Metric.sphere (0 : E) 1) :
    homeomorphUnitSphere.symm u = mk (u : E) (ne_zero_of_mem_unitSphere u) := rfl

/-- `S(E)` is Hausdorff for a normed `E`. -/
instance : T2Space (Sphere E) := homeomorphUnitSphere.symm.t2Space

/-- `S(E)` is compact for a finite-dimensional normed `E`. -/
instance [FiniteDimensional ℝ E] : CompactSpace (Sphere E) :=
  homeomorphUnitSphere.symm.compactSpace

end Normed

/-! ### The projective space `P(E)` and its quotient topology -/

end Sphere

/-- **Benzécri's projective space `P(E)`** (Déf. 3, « *espace projectif*, $P(E)$, associé à $E$, le
quotient de $E-\{O\}$ par $\R^*$ »): Mathlib's `Projectivization ℝ E` (`ℙ ℝ E`, the nonzero vectors
modulo the nonzero homotheties), as a type synonym that carries the quotient topology — the same
device as `Benzecri.Sphere` over `Module.Ray`, so that no orphan topology lands on a Mathlib
type. -/
def ProjSpace (E : Type*) [AddCommGroup E] [Module ℝ E] : Type _ := Projectivization ℝ E

namespace ProjSpace

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The canonical projection `E - {O} → P(E)`. -/
def p : {v : E // v ≠ 0} → ProjSpace E := Projectivization.mk' ℝ

@[simp] theorem p_apply (v : {v : E // v ≠ 0}) :
    (p v : ProjSpace E) = Projectivization.mk ℝ v.1 v.2 :=
  rfl

theorem p_surjective : Function.Surjective (p : {v : E // v ≠ 0} → ProjSpace E) := by
  intro x
  induction x using Projectivization.ind with
  | h v hv => exact ⟨⟨v, hv⟩, rfl⟩

/-- `P(E)` is the quotient of `E - {O}` by the **nonzero homotheties** (Déf. 3). -/
theorem p_eq_p_iff (v w : {v : E // v ≠ 0}) :
    p v = p w ↔ ∃ c : ℝ, c ≠ 0 ∧ c • (w : E) = v := by
  change (Projectivization.mk ℝ (v : E) v.2 : Projectivization ℝ E) =
    Projectivization.mk ℝ (w : E) w.2 ↔ _
  rw [Projectivization.mk_eq_mk_iff' ℝ _ _ v.2 w.2]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, fun h0 => v.2 ?_, ha⟩
    rw [h0, zero_smul] at ha
    exact ha.symm
  · rintro ⟨c, -, h⟩
    exact ⟨c, h⟩

variable [TopologicalSpace E]

/-- **The quotient topology of `P(E)`** (Déf. 3, « $S(E)$ [resp. $P(E)$] sera muni de la topologie
quotient »): coinduced from `E - {O}` by the projection. -/
instance instTopologicalSpace : TopologicalSpace (ProjSpace E) :=
  TopologicalSpace.coinduced p inferInstance

/-- `E - {O} → P(E)` is a quotient map. -/
theorem isQuotientMap_p : IsQuotientMap (p : {v : E // v ≠ 0} → ProjSpace E) :=
  ⟨⟨rfl⟩, p_surjective⟩

theorem continuous_p : Continuous (p : {v : E // v ≠ 0} → ProjSpace E) := isQuotientMap_p.continuous

end ProjSpace

namespace Sphere

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The 2-to-1 map `S(E) → P(E)`. -/
def toProjectivization : Sphere E → ProjSpace E :=
  lift (fun v => Projectivization.mk ℝ v.1 v.2) fun v w h => by
    obtain ⟨c, hc, hcw⟩ := h.exists_pos_left v.2 w.2
    exact (Projectivization.mk_eq_mk_iff' ℝ _ _ v.2 w.2).2 ⟨c⁻¹, by
      rw [← hcw, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]⟩

@[simp] theorem toProjectivization_mk (v : E) (hv : v ≠ 0) :
    toProjectivization (mk v hv) = (Projectivization.mk ℝ v hv : ProjSpace E) := rfl

/-- The projection `E - {O} → P(E)` factors through `S(E)`. -/
theorem toProjectivization_comp_s :
    toProjectivization ∘ s = (ProjSpace.p : {v : E // v ≠ 0} → ProjSpace E) := rfl

theorem toProjectivization_surjective : Function.Surjective (toProjectivization (E := E)) := by
  intro p
  induction p using Projectivization.ind with
  | h v hv => exact ⟨mk v hv, rfl⟩

/-- Two points of `S(E)` have the same image in `P(E)` iff they are equal or diametrically
opposite: `P(E)` is the quotient of `S(E)` by the antipodal map. -/
theorem toProjectivization_eq_iff (x y : Sphere E) :
    toProjectivization x = toProjectivization y ↔ y = x ∨ y = -x := by
  induction x using ind with
  | h v hv =>
  induction y using ind with
  | h w hw =>
  change (Projectivization.mk ℝ v hv : Projectivization ℝ E) = Projectivization.mk ℝ w hw ↔ _
  rw [Projectivization.mk_eq_mk_iff' ℝ _ _ hv hw, neg_mk, mk_eq_mk_iff_exists_pos,
    mk_eq_mk_iff_exists_pos]
  constructor
  · rintro ⟨a, ha⟩
    have ha0 : a ≠ 0 := by rintro rfl; simp at ha; exact hv ha.symm
    rcases ha0.lt_or_gt with h | h
    · exact Or.inr ⟨-a, neg_pos.2 h, by rw [neg_smul, ha]⟩
    · exact Or.inl ⟨a, h, ha⟩
  · rintro (⟨c, _, h⟩ | ⟨c, _, h⟩)
    · exact ⟨c, h⟩
    · exact ⟨-c, by rw [neg_smul, h, neg_neg]⟩

/-- The antipodal map does not move the image in `P(E)`. -/
theorem toProjectivization_neg (x : Sphere E) : toProjectivization (-x) = toProjectivization x :=
  ((toProjectivization_eq_iff x (-x)).2 (Or.inr rfl)).symm

section Topology

variable [TopologicalSpace E]

/-- **The two quotient topologies of `P(E)` agree**: the topology coinduced from `E - {O}` (Déf. 3)
is the topology coinduced from `S(E)` by the antipodal quotient `S(E) → P(E)`. -/
theorem coinduced_toProjectivization :
    TopologicalSpace.coinduced (toProjectivization (E := E)) inferInstance =
      ProjSpace.instTopologicalSpace := by
  rw [instTopologicalSpace, coinduced_compose, toProjectivization_comp_s]
  rfl

/-- `S(E) → P(E)`, the quotient by the antipodal map, is a quotient map. -/
theorem isQuotientMap_toProjectivization : IsQuotientMap (toProjectivization (E := E)) :=
  ⟨⟨coinduced_toProjectivization.symm⟩, toProjectivization_surjective⟩

theorem continuous_toProjectivization : Continuous (toProjectivization (E := E)) :=
  isQuotientMap_toProjectivization.continuous

end Topology

end Sphere

/-! ### The index convention `S(n)` -/

/-- **Benzécri's `S(n)`** (p. 236, « $S(\R^n)$ sera appelée la sphère projective de dimension
$(n-1)$ et notée $S(n-1)$ »): the sphere of `ℝⁿ⁺¹`, of dimension `n`. -/
abbrev S (n : ℕ) : Type := Sphere (Fin (n + 1) → ℝ)

example (n : ℕ) : CompactSpace (S n) := inferInstance
example (n : ℕ) : T2Space (S n) := inferInstance

instance (n : ℕ) : Nonempty (S n) :=
  ⟨Sphere.mk (fun _ => 1) (fun h => by simpa using congr_fun h 0)⟩

/-- `S(n)` is homeomorphic to the Euclidean unit sphere of `ℝⁿ⁺¹`. -/
def S.homeomorphEuclideanSphere (n : ℕ) :
    S n ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
  (Sphere.map (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm).trans Sphere.homeomorphUnitSphere

/-! ### The default topology (Déf. 3): the finest locally convex topology of `ℝⁿ` -/

/-- **The product topology of `ℝⁿ` is finer than every vector-space topology**: for any topology `t`
on `Fin n → ℝ` making addition and scalar multiplication continuous, the identity
`(ℝⁿ, product) → (ℝⁿ, t)` is continuous (`LinearMap.continuous_on_pi`). -/
theorem pi_le_of_isTopologicalAddGroup {n : ℕ} (t : TopologicalSpace (Fin n → ℝ))
    [h₁ : @IsTopologicalAddGroup _ t _] [h₂ : @ContinuousSMul ℝ _ _ _ t] :
    (Pi.topologicalSpace : TopologicalSpace (Fin n → ℝ)) ≤ t := by
  rw [← continuous_id_iff_le]
  exact @LinearMap.continuous_on_pi (Fin n) ℝ (Fin n → ℝ) _ _ _ _ _ t h₁.toContinuousAdd h₂
    LinearMap.id

/-- **In finite dimension, a Hausdorff vector-space topology is the finest vector-space
topology**: if `t₀` makes the finite-dimensional real vector space `E` a Hausdorff topological
vector space, then `t₀` is finer than every topology `t` making `E` a topological vector space
(every linear map out of `(E, t₀)` is continuous). The form of Déf. 3's default for any finite-dimensional `E`. -/
theorem le_of_t2_of_finiteDimensional {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] (t₀ t : TopologicalSpace E) [h₀ : @IsTopologicalAddGroup E t₀ _]
    [h₀' : @ContinuousSMul ℝ E _ _ t₀] [h₀'' : @T2Space E t₀] [h : @IsTopologicalAddGroup E t _]
    [h' : @ContinuousSMul ℝ E _ _ t] : t₀ ≤ t := by
  rw [← continuous_id_iff_le]
  exact @LinearMap.continuous_of_finiteDimensional ℝ _ E _ _ t₀ h₀ h₀' E _ _ t h h' _ h₀'' _
    LinearMap.id

/-- **The topology of `ℝⁿ` is the finest vector-space topology**: the product topology is the least
(i.e. finest) topology on `Fin n → ℝ` for which `ℝⁿ` is a topological vector space. -/
theorem isLeast_pi_vectorSpaceTopology (n : ℕ) :
    IsLeast {t : TopologicalSpace (Fin n → ℝ) |
        @IsTopologicalAddGroup _ t _ ∧ @ContinuousSMul ℝ _ _ _ t}
      Pi.topologicalSpace :=
  ⟨⟨inferInstance, inferInstance⟩, fun t ⟨_, _⟩ => pi_le_of_isTopologicalAddGroup t⟩

/-- **Déf. 3's default topology, for `E = ℝⁿ`** (« Quand aucune autre structure topologique ne sera
spécifiée sur $E$, nous supposerons $E$ muni de la topologie localement convexe la plus fine »):
the finest locally convex topology on `ℝⁿ` is the product topology, which is the topology `S(n)`
is built from. It is locally convex (`NormedSpace.toLocallyConvexSpace`, for the sup norm) and finer
than every vector-space topology, a fortiori than every locally convex one. -/
theorem isLeast_pi_locallyConvexTopology (n : ℕ) :
    IsLeast {t : TopologicalSpace (Fin n → ℝ) |
        @IsTopologicalAddGroup _ t _ ∧ @ContinuousSMul ℝ _ _ _ t ∧
          @LocallyConvexSpace ℝ (Fin n → ℝ) _ _ _ _ t}
      Pi.topologicalSpace :=
  ⟨⟨inferInstance, inferInstance, inferInstance⟩,
    fun t ⟨_, _, _⟩ => pi_le_of_isTopologicalAddGroup t⟩

/-- **The topology of `S(n)` is the quotient topology of Déf. 3 for the default topology of
`ℝⁿ⁺¹`**: it is coinduced by `s` from `ℝⁿ⁺¹ - {O}` with the subspace topology of the finest locally
convex topology (`isLeast_pi_locallyConvexTopology`). -/
theorem S.topology_eq (n : ℕ) :
    (inferInstance : TopologicalSpace (S n)) =
      TopologicalSpace.coinduced Sphere.s
        (TopologicalSpace.induced (Subtype.val : {v : Fin (n + 1) → ℝ // v ≠ 0} → _)
          Pi.topologicalSpace) :=
  rfl

end Benzecri
