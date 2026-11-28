import Benzecri.Chapter3.FacetteConique

/-!
# Chapter 3 § 4, the Remark after Déf. 6: the closed sum of convex bodies of supplementary linear subvarieties is a convex body, of which their relative interiors are conical facettes

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 3 § 4, journal p. 276; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch3.tex` (TO BE CHECKED BY THE AUTHOR, OQ-160),
checked against the OCR layer of PDF p. 49. Target T-bz-c3-somme-facettes-coniques.

* `bzrem:c3s4r1_somme_facettes_coniques` — `benzecri1960_ch3.tex:1142` (Remarque, l.1142–1148;
  no proof printed) — NOT marked: a reading. `Benzecri.SommeFacettes.remarque_somme_facettes_coniques`
  proves, for `E = ⊕ Lᵢ` (`DirectSum.IsInternal L`), `Wᵢ` a convex body of `lᵢ = s(Lᵢ − O)`
  (`IsCorpsConvexeDans`) and every `w` sum of the `Wᵢ` (§ 2 Déf. 5, `EstSommeS w W`, which
  exists: `estSommeS_sommeS`): `closure w` is a convex body of `S(n)` and, for each `i`, the
  relative interior of `Wᵢ` (its interior for the topology of `lᵢ`, `relInterior`) is a conical
  facette of `closure w` (Déf. 5, `IsFacetteConique`), of closure `Wᵢ` and support `lᵢ`. The
  reading: a facette is an α-class, relatively open, so « les `Wᵢ` sont des facettes coniques »
  is read « the relative interior of `Wᵢ` is a conical facette, of closure `Wᵢ` ». This is
  an abuse of language: read literally the conclusion is false for every `Wᵢ` that is not a
  point (a facette is relatively open, and a strict closed `Wᵢ` of nonempty interior in `lᵢ` is
  relatively open only when it is a point); the intended form is proved. Literally it holds
  exactly when `Wᵢ` is its own relative interior
  (`isFacetteK_iff_relInterior_eq`; so for a point, e.g. the vertices of the simplex,
  `TriangleInstance.isFacetteK_vertex`) and fails
  for the closed edge of the triangle (`SommeFacettesInstance.exemple_arete_fermee`).

> **Remarque.** Supposons données $p$ sous-variétés linéaires $L_1$, \ldots, $L_i$, \ldots, $L_p$
> dont $S(n)$ soit la somme. Soient $W_1$, \ldots, $W_i$, \ldots, $W_p$ des corps convexes de
> $L_1$, \ldots, $L_i$, \ldots, $L_p$ ($W_i$ convexe fermé d'intérieur non vide pour la topologie
> de $L_i$). La fermeture de la somme des $W_i$ est un corps convexe de $S(n)$ dont les $W_i$ sont
> des facettes coniques.

## The proof formalized (none is printed)

Write `Kᵢ = F(Wᵢ) ∪ {O}` (a closed salient convex cone of `Lᵢ`) and `pᵢ` the projections of
`E = ⊕ Lᵢ`. The closure of `F(w) = Σ F(Wᵢ)` is `K = {v | ∀ i, pᵢ v ∈ Kᵢ}` (closed: the `pᵢ` are
continuous; every `v ∈ K` is the limit of `v + s Σ Aᵢ`, `Aᵢ` interior points), so
`closure w = s(K − O)` (`closure_eq_ofCone_coneSomme`). `K` is salient (`pᵢ v, −pᵢ v ∈ Kᵢ`), and
`⋂ pᵢ⁻¹(F(Uᵢ))`, `Uᵢ ∩ lᵢ ⊆ Wᵢ` open, is an open set inside `K`: a convex body. Call `B` a
*core point* of `Kᵢ` (`IsCore`) if `B ∈ Lᵢ` and `B + t v ∈ Kᵢ` for small `t > 0`, every `v ∈ Lᵢ`.
For a core point `A`, the facette of `A` in `K` is the set of core points
(`facetteOf_coneSomme`: `A + ε(A − B) ∈ K` kills the components `pⱼ B`, `j ≠ i`, by salience,
and `B` is then a convex combination of `A` and `B + δ(B − A) ∈ Kᵢ`), whose projection is the
relative interior of `Wᵢ` (`relInterior_eq_ofCone_coreSet`), of closure `Wᵢ` and span `Lᵢ`. The
supporting cone at `s(A)` is `ℝA + K = {v | ∀ j ≠ i, pⱼ v ∈ Kⱼ}` (`coneAppuiVec_coneSomme`),
closed, so it is the contingent, and its noyau is `{v | pⱼ v = 0, j ≠ i} = Lᵢ`: the facette is
conical.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| « $p$ sous-variétés linéaires $L_i$ dont $S(n)$ soit la somme » | ⚠ reading (question): `DirectSum.IsInternal L`, `E = ⊕ Lᵢ` (equivalently `iSupIndep L ∧ ⨆ Lᵢ = ⊤`); for `p = 2` it is Déf. 6's bracket, `EstSommeLineaire ⇔ IsCompl` (Chapter3/FacetteConique) |
| « $W_i$ des corps convexes de $L_i$ » | ✓ carried, `IsCorpsConvexeDans (L i) (W i)`: strict convex (Déf. 11's « corps convexe »), contained in `lᵢ`, closed (compact), with nonempty interior for the topology of `lᵢ` |
| « ($W_i$ convexe fermé d'intérieur non vide pour la topologie de $L_i$) » | ⚠ strengthened (by the paper's own Déf. 11): strictness is assumed; the parenthetical omits « de noyau vide » (l.795: « les convexes fermés d'intérieur non vide, et de noyau vide »); without it the Remark fails (`exemple_sans_stricte`) |
| « la somme des $W_i$ » | ✓ carried: any `w` with `EstSommeS w W` (§ 2 Déf. 5); one exists (`estSommeS_sommeS`); reading (a): its closure is `s(Σ (F(Wᵢ) ∪ {O}) − O)` (`closure_eq_ofCone_coneSomme`) |
| « La fermeture … est un corps convexe de $S(n)$ » | ✓ carried: `IsCorpsConvexeS n (closure w)` |
| « dont les $W_i$ sont des facettes coniques » | ⚠ reading (question, abuse of language): `relInterior (L i) (W i)` is a conical facette of `closure w`, of closure `W i`, of support `lᵢ`; literal form iff `relInterior = W i` |

## SCOPE (disclosed)

* The label is not marked: the conclusion « les `Wᵢ` sont des facettes coniques » is proved in
  the reading above, and « `S(n)` somme des `Lᵢ` » is read `E = ⊕ Lᵢ`. Every other assertion is
  proved as printed, for every `p` (the case
  `p = 1`, `L₁ = E`, is the interior facette, of support `S(n)`) and every sum `w`.
* Instances (`Benzecri.SommeFacettesInstance`): for any surjective `f : {0, …, n} → I` the
  coordinate blocks `Lⱼ` and the block simplices `Wⱼ` satisfy every hypothesis
  (`isCorpsConvexeDans_blockW`, `isInternal_blockL`) and the closed sum is the closed simplex
  `TriangleInstance.simplexS n` (`closure_somme_blockW`); for `f = id` the `Wⱼ` are the vertices
  (`blockW_id`, `simplexS_closure_somme_vertices`); on `S(3)` the closed quarter arcs of
  `⟨e₀, e₁⟩`, `⟨e₂, e₃⟩` (`exemple_arcs_S3`); on `S(2)` the closed edge plus the opposite vertex,
  where the closed edge is not a facette (`exemple_arete_fermee`).
* General facts proved here: the projections `proj` of an internal direct sum and their
  calculus (`sum_proj`, `proj_sum`, `mem_iff_proj`), core points (`IsCore.comb`, `span_core`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/
noncomputable section
open Set Topology Filter
namespace Benzecri
namespace SommeFacettes
open Sphere
variable {n : ℕ}
def relInterior (L : Submodule ℝ (Fin (n + 1) → ℝ)) (W : Set (S n)) : Set (S n) :=
  Subtype.val '' interior ((Subtype.val : linearSubvariety L → S n) ⁻¹' W)

def IsCorpsConvexeDans (L : Submodule ℝ (Fin (n + 1) → ℝ)) (W : Set (S n)) : Prop :=
  IsStrictConvexPart W ∧ W ⊆ linearSubvariety L ∧ IsClosed W ∧ (relInterior L W).Nonempty

theorem mem_relInterior_iff {L : Submodule ℝ (Fin (n + 1) → ℝ)} {W : Set (S n)} {x : S n} :
    x ∈ relInterior L W ↔
      x ∈ linearSubvariety L ∧ ∃ U : Set (S n), IsOpen U ∧ x ∈ U ∧ U ∩ linearSubvariety L ⊆ W := by
  constructor
  · rintro ⟨⟨x, hx⟩, hxi, rfl⟩
    obtain ⟨U, hU, hUeq⟩ := isOpen_induced_iff.1 (isOpen_interior (s := (Subtype.val : linearSubvariety L → S n) ⁻¹' W))
    refine ⟨hx, U, hU, ?_, ?_⟩
    · have : (⟨x, hx⟩ : linearSubvariety L) ∈ Subtype.val ⁻¹' U := by rw [hUeq]; exact hxi
      exact this
    · rintro y ⟨hyU, hyl⟩
      have : (⟨y, hyl⟩ : linearSubvariety L) ∈ Subtype.val ⁻¹' U := hyU
      rw [hUeq] at this
      exact interior_subset (s := (Subtype.val : linearSubvariety L → S n) ⁻¹' W) this
  · rintro ⟨hx, U, hU, hxU, hUW⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    refine interior_maximal (t := Subtype.val ⁻¹' U) (fun y hy => hUW ⟨hy, y.2⟩)
      (hU.preimage continuous_subtype_val) hxU

section Core
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
def IsCore (L : Submodule ℝ E) (K : Set E) (B : E) : Prop :=
  B ∈ L ∧ ∀ v ∈ L, ∃ t : ℝ, 0 < t ∧ B + t • v ∈ K

theorem IsCore.mem {L : Submodule ℝ E} {K : Set E} {B : E} (h : IsCore L K B) : B ∈ K := by
  obtain ⟨t, -, ht⟩ := h.2 0 L.zero_mem
  simpa using ht

/-- A convex combination with positive weight on a core point is a core point. -/
theorem IsCore.comb {L : Submodule ℝ E} {K : Set E} (hK : Convex ℝ K) (hKL : K ⊆ L) {B C : E}
    (hB : IsCore L K B) (hC : C ∈ K) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1) :
    IsCore L K (a • B + b • C) := by
  refine ⟨L.add_mem (L.smul_mem _ hB.1) (L.smul_mem _ (hKL hC)), fun v hv => ?_⟩
  obtain ⟨t, ht, hBt⟩ := hB.2 v hv
  refine ⟨a * t, mul_pos ha ht, ?_⟩
  have := hK hBt hC ha.le hb hab
  convert this using 1
  rw [smul_add, smul_smul]; abel

theorem IsCore.smul {L : Submodule ℝ E} {K : Set E} (hK : IsPosCone K) {B : E}
    (hB : IsCore L K B) {c : ℝ} (hc : 0 < c) : IsCore L K (c • B) := by
  refine ⟨L.smul_mem _ hB.1, fun v hv => ?_⟩
  obtain ⟨t, ht, hBt⟩ := hB.2 v hv
  refine ⟨t * c, mul_pos ht hc, ?_⟩
  have := hK c hc _ hBt
  convert this using 1
  rw [smul_add, smul_smul, mul_comm]

/-- In a salient cone of a nonzero `L`, a core point is nonzero. -/
theorem IsCore.ne_zero {L : Submodule ℝ E} {K : Set E} (hK : IsPosCone K)
    (hsal : ∀ v, v ∈ K → -v ∈ K → v = 0) (hL : L ≠ ⊥) {B : E} (hB : IsCore L K B) : B ≠ 0 := by
  rintro rfl
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hL
  obtain ⟨t, ht, h1⟩ := hB.2 v hv
  obtain ⟨t', ht', h2⟩ := hB.2 (-v) (L.neg_mem hv)
  rw [zero_add] at h1 h2
  have h1' := hK t⁻¹ (inv_pos.2 ht) _ h1
  have h2' := hK t'⁻¹ (inv_pos.2 ht') _ h2
  rw [smul_smul, inv_mul_cancel₀ ht.ne', one_smul] at h1'
  rw [smul_smul, inv_mul_cancel₀ ht'.ne', one_smul] at h2'
  exact hv0 (hsal v h1' h2')

/-- The span of the core points is `L` (when there is one). -/
theorem span_core {L : Submodule ℝ E} {K : Set E} (hK : Convex ℝ K) (hKL : K ⊆ L) {A : E}
    (hA : IsCore L K A) : Submodule.span ℝ {B | IsCore L K B} = L := by
  apply le_antisymm
  · rw [Submodule.span_le]; exact fun B hB => hB.1
  · intro v hv
    obtain ⟨t, ht, hAt⟩ := hA.2 v hv
    have hc := hA.comb hK hKL hAt (a := 1 / 2) (b := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
    have e : v = (2 / t) • ((1 / 2 : ℝ) • A + (1 / 2 : ℝ) • (A + t • v)) - (2 / t) • A := by
      match_scalars <;> field_simp
      ring
    rw [e]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span hc))
      (Submodule.smul_mem _ _ (Submodule.subset_span hA))
end Core

variable {I : Type*} [Fintype I] [DecidableEq I] {L : I → Submodule ℝ (Fin (n + 1) → ℝ)}

def proj (hL : DirectSum.IsInternal L) (i : I) :
    (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ) :=
  (L i).subtype ∘ₗ (DirectSum.component ℝ I (fun i => L i) i) ∘ₗ
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap L) hL).symm.toLinearMap

omit [Fintype I] in
theorem proj_apply (hL : DirectSum.IsInternal L) (i : I) (v : Fin (n + 1) → ℝ) :
    proj hL i v = ((LinearEquiv.ofBijective (DirectSum.coeLinearMap L) hL).symm v i : _) := rfl

omit [Fintype I] in
theorem proj_mem (hL : DirectSum.IsInternal L) (i : I) (v : Fin (n + 1) → ℝ) :
    proj hL i v ∈ L i := by
  rw [proj_apply]; exact Subtype.coe_prop _

omit [Fintype I] in
theorem proj_of_mem (hL : DirectSum.IsInternal L) {i : I} {v : Fin (n + 1) → ℝ} (hv : v ∈ L i) :
    proj hL i v = v := by
  rw [proj_apply, hL.ofBijective_coeLinearMap_of_mem hv]

omit [Fintype I] in
theorem proj_of_mem_ne (hL : DirectSum.IsInternal L) {i j : I} (hij : i ≠ j)
    {v : Fin (n + 1) → ℝ} (hv : v ∈ L i) : proj hL j v = 0 := by
  rw [proj_apply, hL.ofBijective_coeLinearMap_of_mem_ne hij hv]; rfl

theorem sum_proj (hL : DirectSum.IsInternal L) (v : Fin (n + 1) → ℝ) :
    ∑ i, proj hL i v = v := by
  set e := LinearEquiv.ofBijective (DirectSum.coeLinearMap L) hL
  conv_rhs => rw [← e.apply_symm_apply v]
  conv_rhs => rw [← DirectSum.sum_univ_of (e.symm v)]
  rw [LinearEquiv.ofBijective_apply, map_sum]
  simp [proj_apply, e]

theorem proj_sum (hL : DirectSum.IsInternal L) {x : I → Fin (n + 1) → ℝ} (hx : ∀ j, x j ∈ L j)
    (i : I) : proj hL i (∑ j, x j) = x i := by
  rw [map_sum, Finset.sum_eq_single i (fun j _ hji => proj_of_mem_ne hL hji (hx j))
    (by simp), proj_of_mem hL (hx i)]

omit [Fintype I] in
theorem proj_proj (hL : DirectSum.IsInternal L) (i j : I) (v : Fin (n + 1) → ℝ) :
    proj hL j (proj hL i v) = if i = j then proj hL i v else 0 := by
  split_ifs with h
  · subst h; exact proj_of_mem hL (proj_mem hL i v)
  · exact proj_of_mem_ne hL h (proj_mem hL i v)

theorem eq_of_proj (hL : DirectSum.IsInternal L) {v w : Fin (n + 1) → ℝ}
    (h : ∀ i, proj hL i v = proj hL i w) : v = w := by
  rw [← sum_proj hL v, ← sum_proj hL w]; exact Finset.sum_congr rfl fun i _ => h i

theorem mem_iff_proj (hL : DirectSum.IsInternal L) {i : I} {v : Fin (n + 1) → ℝ} :
    v ∈ L i ↔ ∀ j, j ≠ i → proj hL j v = 0 := by
  constructor
  · intro hv j hj; exact proj_of_mem_ne hL (Ne.symm hj) hv
  · intro h
    have : v = proj hL i v := by
      conv_lhs => rw [← sum_proj hL v]
      exact Finset.sum_eq_single i (fun j _ hj => h j hj) (by simp)
    rw [this]; exact proj_mem hL i v

omit [Fintype I] in
theorem continuous_proj (hL : DirectSum.IsInternal L) (i : I) : Continuous (proj hL i) :=
  LinearMap.continuous_of_finiteDimensional _


/-! ### The cone of a convex body of `l` -/

section Body

variable {M : Submodule ℝ (Fin (n + 1) → ℝ)} {W : Set (S n)}

theorem kPrime_subset (h : IsCorpsConvexeDans M W) : kPrime W ⊆ M := by
  rintro v (rfl | ⟨hv, hvW⟩)
  · exact M.zero_mem
  · exact (mk_mem_linearSubvariety hv).1 (h.2.1 hvW)

theorem isPosCone_kPrime (W : Set (S n)) : IsPosCone (kPrime W) :=
  fun _ hc _ hv => smul_mem_kPrime hv hc.le

theorem salient_kPrime (h : IsStrictConvexPart W) {v : Fin (n + 1) → ℝ} (hv : v ∈ kPrime W)
    (hv' : -v ∈ kPrime W) : v = 0 := by
  by_contra h0
  rw [mem_kPrime_of_ne h0] at hv
  rw [mem_kPrime_of_ne (neg_ne_zero.2 h0)] at hv'
  obtain ⟨_, hvW⟩ := hv
  obtain ⟨_, hvW'⟩ := hv'
  exact h.2 _ hvW (by rw [neg_mk]; exact hvW')

/-- A point of `l` with a neighbourhood `U` such that `U ∩ l ⊆ W` is a core point. -/
theorem isCore_of_open {U : Set (S n)} (hU : IsOpen U) (hUW : U ∩ linearSubvariety M ⊆ W)
    {B : Fin (n + 1) → ℝ} (hBM : B ∈ M) (hB : B ∈ F U) : IsCore M (kPrime W) B := by
  refine ⟨hBM, fun v hv => ?_⟩
  have hFU : IsOpen (F U) := isOpen_iff_F.1 hU
  have hc : Continuous fun t : ℝ => B + t • v := continuous_const.add (continuous_id.smul continuous_const)
  have hS : IsOpen ((fun t : ℝ => B + t • v) ⁻¹' F U) := hFU.preimage hc
  have h0 : (0 : ℝ) ∈ (fun t : ℝ => B + t • v) ⁻¹' F U := by simpa using hB
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hS 0 h0
  have hmem : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith
  refine ⟨ε / 2, by positivity, ?_⟩
  obtain ⟨hne, hU'⟩ := hball hmem
  refine mem_insert_of_mem _ ⟨hne, hUW ⟨hU', (mk_mem_linearSubvariety hne).2 ?_⟩⟩
  exact M.add_mem hBM (M.smul_mem _ hv)

theorem isCore_of_mem_relInterior {B : Fin (n + 1) → ℝ} (hB : B ≠ 0)
    (h : mk B hB ∈ relInterior M W) : IsCore M (kPrime W) B := by
  obtain ⟨hl, U, hU, hxU, hUW⟩ := mem_relInterior_iff.1 h
  exact isCore_of_open hU hUW ((mk_mem_linearSubvariety hB).1 hl) ⟨hB, hxU⟩

theorem exists_isCore (h : IsCorpsConvexeDans M W) : ∃ A, IsCore M (kPrime W) A := by
  obtain ⟨x, hx⟩ := h.2.2.2
  induction x using ind with
  | h B hB => exact ⟨B, isCore_of_mem_relInterior hB hx⟩

theorem ne_bot (h : IsCorpsConvexeDans M W) : M ≠ ⊥ := by
  rintro rfl
  obtain ⟨x, hx⟩ := h.2.2.2
  have := (mem_relInterior_iff.1 hx).1
  rw [linearSubvariety_eq_empty_iff.2 rfl] at this
  exact this

theorem isCore_ne_zero (h : IsCorpsConvexeDans M W) {B : Fin (n + 1) → ℝ}
    (hB : IsCore M (kPrime W) B) : B ≠ 0 :=
  hB.ne_zero (isPosCone_kPrime W) (fun _ h1 h2 => salient_kPrime h.1 h1 h2) (ne_bot h)

theorem isCore_mem_F (h : IsCorpsConvexeDans M W) {B : Fin (n + 1) → ℝ}
    (hB : IsCore M (kPrime W) B) : B ∈ F W :=
  (mem_kPrime_of_ne (isCore_ne_zero h hB)).1 hB.mem

end Body


/-! ### The cone of the closed sum -/

section Somme

variable (hL : DirectSum.IsInternal L) {W : I → Set (S n)}

/-- The closed convex cone `K = Σ (F(Wᵢ) ∪ {O})`, in coordinates. -/
def coneSomme (W : I → Set (S n)) : Set (Fin (n + 1) → ℝ) :=
  {v | ∀ i, proj hL i v ∈ kPrime (W i)}

/-- The cone `{v | ∀ j ≠ i, pⱼ v ∈ F(Wⱼ) ∪ {O}}`, the supporting cone at the facette `i`. -/
def coneAppuiSomme (W : I → Set (S n)) (i : I) : Set (Fin (n + 1) → ℝ) :=
  {v | ∀ j, j ≠ i → proj hL j v ∈ kPrime (W j)}

include hL in
omit [Fintype I] in
theorem nonempty_index : Nonempty I := by
  by_contra h
  rw [not_nonempty_iff] at h
  have := hL.submodule_iSup_eq_top
  rw [iSup_of_empty] at this
  have h1 : (Pi.single 0 1 : Fin (n + 1) → ℝ) ∈ (⊥ : Submodule ℝ (Fin (n + 1) → ℝ)) :=
    this ▸ Submodule.mem_top
  rw [Submodule.mem_bot] at h1
  simpa using congrFun h1 0

omit [Fintype I] in
theorem zero_mem_coneSomme : (0 : Fin (n + 1) → ℝ) ∈ coneSomme hL W :=
  fun i => by rw [map_zero]; exact zero_mem_kPrime _

omit [Fintype I] in
theorem isPosCone_coneSomme : IsPosCone (coneSomme hL W) :=
  fun c hc v hv i => by rw [map_smul]; exact smul_mem_kPrime (hv i) hc.le

omit [Fintype I] in
theorem convex_coneSomme (hW : ∀ i, IsCorpsConvexeDans (L i) (W i)) :
    Convex ℝ (coneSomme hL W) := by
  have : coneSomme hL W = ⋂ i, proj hL i ⁻¹' kPrime (W i) := by
    ext v; simp [coneSomme]
  rw [this]
  exact convex_iInter fun i => (convex_kPrime (hW i).1.1).linear_preimage _

omit [Fintype I] in
theorem isClosed_coneSomme (hW : ∀ i, IsCorpsConvexeDans (L i) (W i)) :
    IsClosed (coneSomme hL W) := by
  have : coneSomme hL W = ⋂ i, proj hL i ⁻¹' kPrime (W i) := by
    ext v; simp [coneSomme]
  rw [this]
  exact isClosed_iInter fun i =>
    (isClosed_kPrime_of_isClosed (hW i).2.2.1).preimage (continuous_proj hL i)

theorem salient_coneSomme (hW : ∀ i, IsCorpsConvexeDans (L i) (W i)) {v : Fin (n + 1) → ℝ}
    (hv : v ∈ coneSomme hL W) (hv' : -v ∈ coneSomme hL W) : v = 0 := by
  rw [← sum_proj hL v]
  refine Finset.sum_eq_zero fun i _ => salient_kPrime (hW i).1 (hv i) ?_
  have := hv' i
  rwa [map_neg] at this

omit [Fintype I] in
theorem mem_coneSomme_of_mem (hW : ∀ i, IsCorpsConvexeDans (L i) (W i)) {i : I}
    {v : Fin (n + 1) → ℝ} (hv : v ∈ kPrime (W i)) : v ∈ coneSomme hL W := by
  intro j
  by_cases h : i = j
  · subst h; rw [proj_of_mem hL (kPrime_subset (hW i) hv)]; exact hv
  · rw [proj_of_mem_ne hL h (kPrime_subset (hW i) hv)]; exact zero_mem_kPrime _

omit [Fintype I] in
theorem mem_kPrime_of_mem_coneSomme {i : I} {v : Fin (n + 1) → ℝ} (hv : v ∈ coneSomme hL W)
    (hvL : v ∈ L i) : v ∈ kPrime (W i) := by
  have := hv i
  rwa [proj_of_mem hL hvL] at this

omit [Fintype I] in
theorem isPosCone_coneAppuiSomme (i : I) : IsPosCone (coneAppuiSomme hL W i) :=
  fun c hc v hv j hj => by rw [map_smul]; exact smul_mem_kPrime (hv j hj) hc.le

omit [Fintype I] in
theorem zero_mem_coneAppuiSomme (i : I) : (0 : Fin (n + 1) → ℝ) ∈ coneAppuiSomme hL W i :=
  fun j _ => by rw [map_zero]; exact zero_mem_kPrime _

omit [Fintype I] in
theorem convex_coneAppuiSomme (hW : ∀ i, IsCorpsConvexeDans (L i) (W i)) (i : I) :
    Convex ℝ (coneAppuiSomme hL W i) := by
  have : coneAppuiSomme hL W i = ⋂ j, ⋂ (_ : j ≠ i), proj hL j ⁻¹' kPrime (W j) := by
    ext v; simp [coneAppuiSomme]
  rw [this]
  exact convex_iInter fun j => convex_iInter fun _ => (convex_kPrime (hW j).1.1).linear_preimage _

omit [Fintype I] in
theorem isClosed_coneAppuiSomme (hW : ∀ i, IsCorpsConvexeDans (L i) (W i)) (i : I) :
    IsClosed (coneAppuiSomme hL W i) := by
  have : coneAppuiSomme hL W i = ⋂ j, ⋂ (_ : j ≠ i), proj hL j ⁻¹' kPrime (W j) := by
    ext v; simp [coneAppuiSomme]
  rw [this]
  exact isClosed_iInter fun j => isClosed_iInter fun _ =>
    (isClosed_kPrime_of_isClosed (hW j).2.2.1).preimage (continuous_proj hL j)

/-- The sum of core points lies in the interior of the cone. -/
theorem exists_core_interior (hW : ∀ i, IsCorpsConvexeDans (L i) (W i)) :
    ∃ A : I → Fin (n + 1) → ℝ, (∀ i, IsCore (L i) (kPrime (W i)) (A i)) ∧
      (∑ i, A i) ∈ interior (coneSomme hL W) := by
  have hx : ∀ i, ∃ B : Fin (n + 1) → ℝ, ∃ hB : B ≠ 0, mk B hB ∈ relInterior (L i) (W i) := by
    intro i
    obtain ⟨x, hx⟩ := (hW i).2.2.2
    induction x using ind with
    | h B hB => exact ⟨B, hB, hx⟩
  choose A hA0 hA using hx
  have hU := fun i => (mem_relInterior_iff.1 (hA i)).2
  choose U hUo hAU hUW using hU
  refine ⟨A, fun i => isCore_of_mem_relInterior (hA0 i) (hA i), ?_⟩
  have hAL : ∀ i, A i ∈ L i := fun i =>
    (mk_mem_linearSubvariety (hA0 i)).1 (mem_relInterior_iff.1 (hA i)).1
  refine mem_interior.2 ⟨⋂ i, proj hL i ⁻¹' F (U i), ?_, ?_, ?_⟩
  · intro v hv i
    have hvi : proj hL i v ∈ F (U i) := mem_iInter.1 hv i
    obtain ⟨hne, hvU⟩ := hvi
    exact mem_insert_of_mem _ ⟨hne, hUW i ⟨hvU, (mk_mem_linearSubvariety hne).2 (proj_mem hL i v)⟩⟩
  · exact isOpen_iInter_of_finite fun i =>
      (isOpen_iff_F.1 (hUo i)).preimage (continuous_proj hL i)
  · refine mem_iInter.2 fun i => ?_
    rw [mem_preimage, proj_sum hL hAL]
    exact ⟨hA0 i, hAU i⟩


/-- **Reading (a), « la somme des `Wᵢ` »** (§ 2 Déf. 5): `s(Σ F(Wᵢ))`, every summand nonzero. -/
def sommeS (W : I → Set (S n)) : Set (S n) :=
  ofCone ((fun x : I → (Fin (n + 1) → ℝ) => ∑ i, x i) '' univ.pi (fun i => F (W i)))

theorem sum_image_subset (hW : ∀ i, IsCorpsConvexeDans (L i) (W i)) :
    (fun x : I → (Fin (n + 1) → ℝ) => ∑ i, x i) '' univ.pi (fun i => F (W i)) ⊆
      coneSomme hL W := by
  rintro _ ⟨x, hx, rfl⟩ i
  have hxL : ∀ j, x j ∈ L j := fun j => kPrime_subset (hW j) (mem_insert_of_mem _ (hx j trivial))
  rw [proj_sum hL hxL]
  exact mem_insert_of_mem _ (hx i trivial)

/-- The closure of `Σ F(Wᵢ)` is `Σ (F(Wᵢ) ∪ {O})`. -/
theorem closure_sum_image (hW : ∀ i, IsCorpsConvexeDans (L i) (W i)) :
    closure ((fun x : I → (Fin (n + 1) → ℝ) => ∑ i, x i) '' univ.pi (fun i => F (W i))) =
      coneSomme hL W := by
  refine Subset.antisymm (closure_minimal (sum_image_subset hL hW) (isClosed_coneSomme hL hW)) ?_
  intro v hv
  obtain ⟨A, hA, -⟩ := exists_core_interior hL hW
  have ht : Tendsto (fun s : ℝ => v + s • ∑ i, A i) (𝓝[>] 0) (𝓝 v) := by
    have : Tendsto (fun s : ℝ => v + s • ∑ i, A i) (𝓝 0) (𝓝 (v + (0 : ℝ) • ∑ i, A i)) :=
      (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
    rw [zero_smul, add_zero] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  refine mem_closure_of_tendsto ht ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
  refine ⟨fun i => proj hL i v + s • A i, fun i _ => ?_, ?_⟩
  · have hmem : proj hL i v + s • A i ∈ kPrime (W i) :=
      add_mem_kPrime (hW i).1.1 (hv i) (smul_mem_kPrime (hA i).mem hs.le)
    have hne : proj hL i v + s • A i ≠ 0 := by
      intro h0
      have h1 : -(s • A i) ∈ kPrime (W i) := by
        rw [← eq_neg_of_add_eq_zero_left h0]; exact hv i
      have := salient_kPrime (hW i).1 (smul_mem_kPrime (hA i).mem hs.le) h1
      exact isCore_ne_zero (hW i) (hA i) ((smul_eq_zero.1 this).resolve_left hs.ne')
    exact (mem_kPrime_of_ne hne).1 hmem
  · simp only [Finset.sum_add_distrib, ← Finset.smul_sum, sum_proj hL v]

include hL in
theorem F_sommeS (hW : ∀ i, IsCorpsConvexeDans (L i) (W i)) : F (sommeS W) =
    (fun x : I → (Fin (n + 1) → ℝ) => ∑ i, x i) '' univ.pi (fun i => F (W i)) := by
  refine F_ofCone_of_zero_notMem ?_ ?_
  · rintro c hc _ ⟨x, hx, rfl⟩
    exact ⟨fun i => c • x i, fun i _ => smul_mem_F (hx i trivial) hc, by simp [Finset.smul_sum]⟩
  · rintro ⟨x, hx, h0⟩
    obtain ⟨i⟩ := nonempty_index hL
    have hxL : ∀ j, x j ∈ L j := fun j =>
      kPrime_subset (hW j) (mem_insert_of_mem _ (hx j trivial))
    have := proj_sum hL hxL i
    simp only at h0
    rw [h0, map_zero] at this
    exact zero_notMem_F _ (this ▸ hx i trivial)

omit [DecidableEq I] in
theorem F_eq_of_estSommeS {w : Set (S n)} (hw : EstSommeS w W) :
    F w = (fun x : I → (Fin (n + 1) → ℝ) => ∑ i, x i) '' univ.pi (fun i => F (W i)) :=
  ((isSommeConvexes_iff_bijOn _ _).1 hw.2).2.image_eq.symm

include hL in
/-- « la somme des `Wᵢ` » exists (§ 2 Déf. 5): `sommeS W`. -/
theorem estSommeS_sommeS (hW : ∀ i, IsCorpsConvexeDans (L i) (W i)) : EstSommeS (sommeS W) W := by
  have hc : ∀ i, Convex ℝ (F (W i)) := fun i => isStrictConvexPart_iff_convex_F.1 (hW i).1
  refine ⟨hc, (isSommeConvexes_iff_bijOn _ _).2 ⟨hc, ?_⟩⟩
  rw [F_sommeS hL hW]
  refine Set.InjOn.bijOn_image fun x hx y hy hxy => funext fun i => ?_
  have hxL : ∀ j, x j ∈ L j := fun j => kPrime_subset (hW j) (mem_insert_of_mem _ (hx j trivial))
  have hyL : ∀ j, y j ∈ L j := fun j => kPrime_subset (hW j) (mem_insert_of_mem _ (hy j trivial))
  rw [← proj_sum hL hxL i, ← proj_sum hL hyL i]
  exact congrArg _ hxy

/-- Reading (a): the closure of the sum is `s(Σ (F(Wᵢ) ∪ {O}) − O)`. -/
theorem closure_eq_ofCone_coneSomme (hW : ∀ i, IsCorpsConvexeDans (L i) (W i))
    {w : Set (S n)} (hw : EstSommeS w W) : closure w = ofCone (coneSomme hL W) := by
  apply F_injective
  rw [F_closure, F_eq_of_estSommeS hw, closure_sum_image hL hW, F_ofCone (isPosCone_coneSomme hL)]

omit [Fintype I] in
theorem isConvexPart_ofCone_coneSomme (hW : ∀ i, IsCorpsConvexeDans (L i) (W i)) :
    IsConvexPart (ofCone (coneSomme hL W)) :=
  isConvexPart_ofCone_of_cone (convex_coneSomme hL hW) (isPosCone_coneSomme hL)

omit [Fintype I] in
theorem kPrime_ofCone_coneSomme : kPrime (ofCone (coneSomme hL W)) = coneSomme hL W := by
  rw [kPrime, insert_zero_F_ofCone (isPosCone_coneSomme hL),
    insert_eq_of_mem (zero_mem_coneSomme hL)]

/-- The closed sum is a convex body of `S(n)`. -/
theorem isCorpsConvexeS_ofCone_coneSomme (hW : ∀ i, IsCorpsConvexeDans (L i) (W i)) :
    IsCorpsConvexeS n (ofCone (coneSomme hL W)) := by
  have hpos := isPosCone_coneSomme hL (W := W)
  refine ⟨⟨isConvexPart_ofCone_coneSomme hL hW, fun m hm hm' => ?_⟩,
    (isClosed_ofCone hpos (isClosed_coneSomme hL hW) (zero_mem_coneSomme hL)).isCompact, ?_⟩
  · induction m using ind with
    | h v hv =>
    rw [neg_mk] at hm'
    rw [mk_mem_ofCone_iff hpos] at hm hm'
    exact hv (salient_coneSomme hL hW hm hm')
  · obtain ⟨A, hA, hint⟩ := exists_core_interior hL hW
    obtain ⟨i⟩ := nonempty_index hL
    have hAL : ∀ j, A j ∈ L j := fun j => (hA j).1
    have hne : ∑ j, A j ≠ 0 := by
      intro h0
      have := proj_sum hL hAL i
      rw [h0, map_zero] at this
      exact isCore_ne_zero (hW i) (hA i) this.symm
    refine ⟨mk _ hne, (mk_mem_iff_mem_F hne).2 ?_⟩
    rw [F_interior, F_ofCone hpos]
    rw [show coneSomme hL W \ {0} = coneSomme hL W ∩ {0}ᶜ from rfl, interior_inter,
      isOpen_compl_singleton.interior_eq]
    exact ⟨hint, hne⟩


/-! ### The facette of a core point -/

/-- The core points of `F(Wᵢ) ∪ {O}` relative to `Lᵢ`. -/
def coreSet (L : I → Submodule ℝ (Fin (n + 1) → ℝ)) (W : I → Set (S n)) (i : I) : Set (Fin (n + 1) → ℝ) :=
  {B | IsCore (L i) (kPrime (W i)) B}

omit [Fintype I] in
omit [DecidableEq I] in
theorem isPosCone_coreSet (i : I) : IsPosCone (coreSet L W i) :=
  fun _ hc _ hB => IsCore.smul (isPosCone_kPrime _) hB hc

omit [Fintype I] in
omit [DecidableEq I] in
theorem zero_notMem_coreSet (hW : ∀ i, IsCorpsConvexeDans (L i) (W i)) (i : I) :
    (0 : Fin (n + 1) → ℝ) ∉ coreSet L W i :=
  fun h => isCore_ne_zero (hW i) h rfl

/-- **The facette of a core point `A` of `F(Wᵢ) ∪ {O}` in the cone `K` is the set of core
points.** -/
theorem facetteOf_coneSomme (hW : ∀ i, IsCorpsConvexeDans (L i) (W i)) {i : I}
    {A : Fin (n + 1) → ℝ} (hA : IsCore (L i) (kPrime (W i)) A) :
    facetteOf (coneSomme hL W) A = coreSet L W i := by
  have hK := convex_coneSomme hL hW
  have hKi : Convex ℝ (kPrime (W i)) := convex_kPrime (hW i).1.1
  have hKiL := kPrime_subset (hW i)
  ext B
  simp only [facetteOf, mem_setOf_eq, FW, alphaW_iff_extend hK, coreSet]
  constructor
  · rintro ⟨⟨-, hB, ε, hε, h1⟩, -, -, δ, hδ, h2⟩
    have hBL : B ∈ L i := by
      refine (mem_iff_proj hL).2 fun j hj => ?_
      have h1j := h1 j
      rw [map_add, map_smul, map_sub, proj_of_mem_ne hL (Ne.symm hj) hA.1, zero_sub, zero_add,
        smul_neg] at h1j
      have := smul_mem_kPrime h1j (inv_pos.2 hε).le
      rw [smul_neg, smul_smul, inv_mul_cancel₀ hε.ne', one_smul] at this
      exact salient_kPrime (hW j).1 (hB j) this
    have hC : B + δ • (B - A) ∈ kPrime (W i) :=
      mem_kPrime_of_mem_coneSomme hL h2 (Submodule.add_mem _ hBL
        (Submodule.smul_mem _ _ (Submodule.sub_mem _ hBL hA.1)))
    have := hA.comb hKi hKiL hC (a := δ / (1 + δ)) (b := 1 / (1 + δ)) (by positivity)
      (by positivity) (by field_simp; ring)
    convert this using 1
    match_scalars <;> field_simp
    ring
  · intro hB
    have hBK : B ∈ coneSomme hL W := mem_coneSomme_of_mem hL hW hB.mem
    have hAK : A ∈ coneSomme hL W := mem_coneSomme_of_mem hL hW hA.mem
    obtain ⟨t, ht, h1⟩ := hA.2 (A - B) (Submodule.sub_mem _ hA.1 hB.1)
    obtain ⟨t', ht', h2⟩ := hB.2 (B - A) (Submodule.sub_mem _ hB.1 hA.1)
    exact ⟨⟨hAK, hBK, t, ht, mem_coneSomme_of_mem hL hW h1⟩,
      ⟨hBK, hAK, t', ht', mem_coneSomme_of_mem hL hW h2⟩⟩

omit [Fintype I] in
theorem mk_mem_ofCone_coneSomme (hW : ∀ i, IsCorpsConvexeDans (L i) (W i)) {i : I}
    {A : Fin (n + 1) → ℝ} (hA : IsCore (L i) (kPrime (W i)) A) :
    mk A (isCore_ne_zero (hW i) hA) ∈ ofCone (coneSomme hL W) :=
  mk_mem_ofCone _ (mem_coneSomme_of_mem hL hW hA.mem)

/-- The k-facette of `s(A)`, `A` a core point, is `s(core points)`. -/
theorem facetteK_eq_ofCone_coreSet (hW : ∀ i, IsCorpsConvexeDans (L i) (W i)) {i : I}
    {A : Fin (n + 1) → ℝ} (hA : IsCore (L i) (kPrime (W i)) A) :
    facetteK (ofCone (coneSomme hL W)) (mk A (isCore_ne_zero (hW i) hA)) =
      ofCone (coreSet L W i) := by
  rw [facetteK_eq_ofCone (isConvexPart_ofCone_coneSomme hL hW) (isRep_mk _ _),
    kPrime_ofCone_coneSomme, facetteOf_coneSomme hL hW hA]

omit [Fintype I] in
omit [DecidableEq I] in
/-- The relative interior of `Wᵢ` is `s(core points)`. -/
theorem relInterior_eq_ofCone_coreSet (hW : ∀ i, IsCorpsConvexeDans (L i) (W i)) (i : I) :
    relInterior (L i) (W i) = ofCone (coreSet L W i) := by
  ext x
  constructor
  · intro hx
    induction x using ind with
    | h B hB => exact mk_mem_ofCone hB (isCore_of_mem_relInterior hB hx)
  · intro hx
    obtain ⟨B, hB0, hB, rfl⟩ := mem_ofCone.1 hx
    obtain ⟨x0, hx0⟩ := (hW i).2.2.2
    induction x0 using ind with
    | h A0 hA00 =>
    obtain ⟨hl0, U0, hU0, hA0U, hU0W⟩ := mem_relInterior_iff.1 hx0
    have hA0L : A0 ∈ L i := (mk_mem_linearSubvariety hA00).1 hl0
    obtain ⟨ε, hε, hC⟩ := hB.2 (B - A0) (Submodule.sub_mem _ hB.1 hA0L)
    have hmu : ε / (1 + ε) ≠ 0 := (by positivity : 0 < ε / (1 + ε)).ne'
    let φ : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) := fun z =>
      (1 / (1 + ε)) • (B + ε • (B - A0)) + (ε / (1 + ε)) • z
    have hφ : IsOpenMap φ :=
      (isOpenMap_add_left ((1 / (1 + ε)) • (B + ε • (B - A0)))).comp (isOpenMap_smul₀ hmu)
    have hO : IsOpen (φ '' F U0) := hφ _ (isOpen_iff_F.1 hU0)
    have hBφ : φ A0 = B := by
      simp only [φ]
      match_scalars <;> field_simp
      ring
    refine mem_relInterior_iff.2 ⟨(mk_mem_linearSubvariety hB0).2 hB.1, ofCone (φ '' F U0),
      isOpenMap_s _ (hO.preimage continuous_subtype_val),
      mk_mem_ofCone hB0 ⟨A0, ⟨hA00, hA0U⟩, hBφ⟩, ?_⟩
    rintro y ⟨hy, hyl⟩
    obtain ⟨u, hu0, ⟨z, ⟨hz0, hzU⟩, rfl⟩, rfl⟩ := mem_ofCone.1 hy
    have huL : φ z ∈ L i := (mk_mem_linearSubvariety hu0).1 hyl
    have hCL : B + ε • (B - A0) ∈ L i := kPrime_subset (hW i) hC
    have hzL : z ∈ L i := by
      have : z = (ε / (1 + ε))⁻¹ • (φ z - (1 / (1 + ε)) • (B + ε • (B - A0))) := by
        simp only [φ, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hmu, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _ huL (Submodule.smul_mem _ _ hCL))
    have hzK : z ∈ kPrime (W i) :=
      mem_insert_of_mem _ ⟨hz0, hU0W ⟨hzU, (mk_mem_linearSubvariety hz0).2 hzL⟩⟩
    have := convex_kPrime (hW i).1.1 hC hzK (a := 1 / (1 + ε)) (b := ε / (1 + ε))
      (by positivity) (by positivity) (by field_simp)
    exact ((mem_kPrime_of_ne hu0).1 this).2

omit [Fintype I] in
omit [DecidableEq I] in
theorem closure_ofCone_coreSet (hW : ∀ i, IsCorpsConvexeDans (L i) (W i)) (i : I) :
    closure (ofCone (coreSet L W i)) = W i := by
  have hF : F (ofCone (coreSet L W i)) = coreSet L W i :=
    F_ofCone_of_zero_notMem (isPosCone_coreSet i) (zero_notMem_coreSet hW i)
  have hsub : ofCone (coreSet L W i) ⊆ W i :=
    ofCone_subset_of_subset_kPrime fun _ hB => IsCore.mem hB
  refine Subset.antisymm (closure_minimal hsub (hW i).2.2.1) ?_
  intro x hx
  induction x using ind with
  | h B hB =>
  rw [mk_mem_iff_mem_F, F_closure, hF]
  refine ⟨?_, hB⟩
  obtain ⟨A, hA⟩ := exists_isCore (hW i)
  have hBK : B ∈ kPrime (W i) := mem_insert_of_mem _ ⟨hB, hx⟩
  have ht : Tendsto (fun s : ℝ => s • A + (1 - s) • B) (𝓝[>] 0) (𝓝 B) := by
    have hc : Continuous (fun s : ℝ => s • A + (1 - s) • B) := by fun_prop
    have : Tendsto (fun s : ℝ => s • A + (1 - s) • B) (𝓝 0) (𝓝 ((0 : ℝ) • A + ((1 : ℝ) - 0) • B)) :=
      hc.tendsto 0
    simpa using tendsto_nhdsWithin_of_tendsto_nhds this
  refine mem_closure_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
  exact hA.comb (convex_kPrime (hW i).1.1) (kPrime_subset (hW i)) hBK (a := s) (b := 1 - s)
    hs.1 (by linarith [hs.2]) (by ring)

omit [Fintype I] in
omit [DecidableEq I] in
theorem supportK_ofCone_coreSet (hW : ∀ i, IsCorpsConvexeDans (L i) (W i)) (i : I) :
    supportK (ofCone (coreSet L W i)) = linearSubvariety (L i) := by
  rw [supportK_ofCone (isPosCone_coreSet i) (zero_notMem_coreSet hW i)]
  obtain ⟨A, hA⟩ := exists_isCore (hW i)
  rw [coreSet, span_core (convex_kPrime (hW i).1.1) (kPrime_subset (hW i)) hA]

omit [Fintype I] in
/-- The supporting cone of the closed sum at `s(A)`, `A` a core point of `F(Wᵢ) ∪ {O}`. -/
theorem coneAppuiVec_coneSomme (hW : ∀ i, IsCorpsConvexeDans (L i) (W i)) {i : I}
    {A : Fin (n + 1) → ℝ} (hA : IsCore (L i) (kPrime (W i)) A) :
    coneAppuiVec (ofCone (coneSomme hL W)) A = coneAppuiSomme hL W i := by
  have hFK : F (ofCone (coneSomme hL W)) = coneSomme hL W \ {0} :=
    F_ofCone (isPosCone_coneSomme hL)
  have hKi : Convex ℝ (kPrime (W i)) := convex_kPrime (hW i).1.1
  have hKiL := kPrime_subset (hW i)
  ext v
  simp only [coneAppuiVec, hFK, mem_setOf_eq]
  constructor
  · rintro ⟨l, P, ⟨hP, -⟩, rfl⟩ j hj
    rw [map_add, map_smul, proj_of_mem_ne hL (Ne.symm hj) hA.1, smul_zero, zero_add]
    exact hP j
  · intro hv
    obtain ⟨t, ht, hAt⟩ := hA.2 (proj hL i v) (proj_mem hL i v)
    have hc := hA.comb hKi hKiL hAt (a := 1 / 2) (b := 1 / 2) (by norm_num) (by norm_num)
      (by norm_num)
    have hc2 := hc.smul (isPosCone_kPrime _) (c := 2 / t) (by positivity)
    have hPL := hc2.1
    refine ⟨-(2 / t), (2 / t) • ((1 / 2 : ℝ) • A + (1 / 2 : ℝ) • (A + t • proj hL i v)) +
      (v - proj hL i v), ⟨?_, ?_⟩, ?_⟩
    · intro j
      rw [map_add, map_sub]
      by_cases hj : j = i
      · subst hj
        rw [proj_of_mem hL hPL, proj_of_mem hL (proj_mem hL j v), sub_self, add_zero]
        exact hc2.mem
      · rw [proj_of_mem_ne hL (Ne.symm hj) hPL, proj_of_mem_ne hL (Ne.symm hj) (proj_mem hL i v),
          sub_zero, zero_add]
        exact hv j hj
    · intro h0
      have := congrArg (proj hL i) h0
      rw [map_add, map_sub, proj_of_mem hL hPL, proj_of_mem hL (proj_mem hL i v), sub_self,
        add_zero, map_zero] at this
      exact isCore_ne_zero (hW i) hc2 this
    · simp only [smul_add, smul_smul]
      rw [show 2 / t * (1 / 2 * t) = 1 by field_simp]
      module

theorem noyau_ofCone_coneAppuiSomme (hW : ∀ i, IsCorpsConvexeDans (L i) (W i)) (i : I) :
    noyau (ofCone (coneAppuiSomme hL W i)) = linearSubvariety (L i) := by
  have hpos := isPosCone_coneAppuiSomme hL (W := W) i
  rw [noyau_eq (isConvexPart_ofCone_of_cone (convex_coneAppuiSomme hL hW i) hpos)]
  ext x
  induction x using ind with
  | h v hv =>
  simp only [mem_setOf_eq]
  rw [neg_mk, mk_mem_ofCone_iff hpos, mk_mem_ofCone_iff hpos, mk_mem_linearSubvariety hv,
    mem_iff_proj hL]
  constructor
  · rintro ⟨h1, h2⟩ j hj
    have := h2 j hj
    rw [map_neg] at this
    exact salient_kPrime (hW j).1 (h1 j hj) this
  · intro h
    exact ⟨fun j hj => by rw [h j hj]; exact zero_mem_kPrime _,
      fun j hj => by rw [map_neg, h j hj, neg_zero]; exact zero_mem_kPrime _⟩


/-- The relative interior of `Wᵢ` is the facette of the closed sum at each of its points. -/
theorem relInterior_eq_facetteK (hW : ∀ i, IsCorpsConvexeDans (L i) (W i)) {i : I} {a : S n}
    (ha : a ∈ relInterior (L i) (W i)) :
    relInterior (L i) (W i) = facetteK (ofCone (coneSomme hL W)) a := by
  induction a using ind with
  | h A hA0 =>
  have hA := isCore_of_mem_relInterior hA0 ha
  rw [facetteK_eq_ofCone_coreSet hL hW hA, relInterior_eq_ofCone_coreSet hW i]

/-! ### The Remark -/

include hL in
/-- **The Remark after Déf. 6.** If `S(n)` is the sum of the linear subvarieties `lᵢ = s(Lᵢ − O)`
(`E = ⊕ Lᵢ`) and `Wᵢ` is a convex body of `lᵢ`, the closure of the sum `w` of the `Wᵢ` is a
convex body of `S(n)`, and for each `i` the relative interior of `Wᵢ` is a conical facette of it,
of closure `Wᵢ` and support `lᵢ`. -/
theorem remarque_somme_facettes_coniques (hW : ∀ i, IsCorpsConvexeDans (L i) (W i))
    {w : Set (S n)} (hw : EstSommeS w W) :
    IsCorpsConvexeS n (closure w) ∧
      ∀ i, IsFacetteConique (closure w) (relInterior (L i) (W i)) ∧
        closure (relInterior (L i) (W i)) = W i ∧
        supportK (relInterior (L i) (W i)) = linearSubvariety (L i) := by
  rw [closure_eq_ofCone_coneSomme hL hW hw]
  refine ⟨isCorpsConvexeS_ofCone_coneSomme hL hW, fun i => ?_⟩
  rw [relInterior_eq_ofCone_coreSet hW i]
  obtain ⟨A, hA⟩ := exists_isCore (hW i)
  refine ⟨⟨⟨_, mk_mem_ofCone_coneSomme hL hW hA, (facetteK_eq_ofCone_coreSet hL hW hA).symm⟩,
    mk A (isCore_ne_zero (hW i) hA), mk_mem_ofCone _ hA, ?_⟩,
    closure_ofCone_coreSet hW i, supportK_ofCone_coreSet hW i⟩
  rw [supportK_ofCone_coreSet hW i, contingent,
    coneAppui_eq_ofCone (isConvexPart_ofCone_coneSomme hL hW) (mk_mem_ofCone_coneSomme hL hW hA)
      (isRep_mk _ _), coneAppuiVec_coneSomme hL hW hA,
    (isClosed_ofCone (isPosCone_coneAppuiSomme hL i) (isClosed_coneAppuiSomme hL hW i)
      (zero_mem_coneAppuiSomme hL i)).closure_eq, noyau_ofCone_coneAppuiSomme hL hW i]

include hL in
/-- **« les `Wᵢ` sont des facettes », read literally**: `Wᵢ` is a facette of the closed sum iff it
is its own relative interior. -/
theorem isFacetteK_iff_relInterior_eq (hW : ∀ i, IsCorpsConvexeDans (L i) (W i))
    {w : Set (S n)} (hw : EstSommeS w W) (i : I) :
    IsFacetteK (closure w) (W i) ↔ relInterior (L i) (W i) = W i := by
  constructor
  · rintro ⟨b, -, hWb⟩
    rw [closure_eq_ofCone_coneSomme hL hW hw] at hWb
    obtain ⟨a, ha⟩ := (hW i).2.2.2
    have haW : a ∈ W i := by
      obtain ⟨y, hy, rfl⟩ := ha
      exact interior_subset (s := (Subtype.val : linearSubvariety (L i) → S n) ⁻¹' W i) hy
    rw [relInterior_eq_facetteK hL hW ha, hWb]
    rw [hWb] at haW
    exact (facetteK_eq_of_fk (isConvexPart_ofCone_coneSomme hL hW) haW).symm
  · intro h
    rw [← h]
    exact ((remarque_somme_facettes_coniques hL hW hw).2 i).1.1

end Somme

end SommeFacettes

/-! ### Instances: coordinate blocks and the closed simplex -/

namespace SommeFacettesInstance

open Sphere TriangleInstance

variable {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]

/-- The coordinate block `Lⱼ = {v | v_c = 0 for f c ≠ j}` of a map `f : {0, …, n} → I`. -/
def blockL (f : Fin (n + 1) → I) (j : I) : Submodule ℝ (Fin (n + 1) → ℝ) where
  carrier := {v | ∀ c, f c ≠ j → v c = 0}
  add_mem' {a b} ha hb c hc := by simp [ha c hc, hb c hc]
  zero_mem' c _ := rfl
  smul_mem' r a ha c hc := by simp [ha c hc]

omit [Fintype I] in
omit [DecidableEq I] in
theorem mem_blockL {f : Fin (n + 1) → I} {j : I} {v : Fin (n + 1) → ℝ} :
    v ∈ blockL f j ↔ ∀ c, f c ≠ j → v c = 0 := Iff.rfl

/-- The restriction of `v` to the block `j`. -/
def restrictB (f : Fin (n + 1) → I) (j : I) (v : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  fun c => if f c = j then v c else 0

omit [Fintype I] in
theorem restrictB_mem (f : Fin (n + 1) → I) (j : I) (v : Fin (n + 1) → ℝ) :
    restrictB f j v ∈ blockL f j := fun c hc => by simp [restrictB, hc]

theorem sum_restrictB (f : Fin (n + 1) → I) (v : Fin (n + 1) → ℝ) :
    ∑ j, restrictB f j v = v := by
  funext c
  simp [restrictB, Finset.sum_apply]

/-- **`E = ⊕ Lⱼ`** for the coordinate blocks. -/
theorem isInternal_blockL (f : Fin (n + 1) → I) : DirectSum.IsInternal (blockL f) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · rw [iSupIndep_def]
    intro j
    rw [Submodule.disjoint_def]
    intro v hv hv'
    have hP : ∀ c, f c = j → v c = 0 := by
      refine Submodule.iSup_induction _ (motive := fun v => ∀ c, f c = j → v c = 0) hv' ?_ ?_ ?_
      · intro k x hx
        refine Submodule.iSup_induction _ (motive := fun v => ∀ c, f c = j → v c = 0) hx ?_ ?_ ?_
        · intro hk y hy c hc
          exact hy c (by rw [hc]; exact Ne.symm hk)
        · intro c _; rfl
        · intro x y hx hy c hc; simp [hx c hc, hy c hc]
      · intro c _; rfl
      · intro x y hx hy c hc; simp [hx c hc, hy c hc]
    funext c
    by_cases hc : f c = j
    · exact hP c hc
    · exact hv c hc
  · rw [eq_top_iff]
    intro v _
    rw [← sum_restrictB f v]
    exact Submodule.sum_mem _ fun j _ => Submodule.mem_iSup_of_mem j (restrictB_mem f j v)

theorem proj_blockL (f : Fin (n + 1) → I) (j : I) (v : Fin (n + 1) → ℝ) :
    SommeFacettes.proj (isInternal_blockL f) j v = restrictB f j v := by
  conv_lhs => rw [← sum_restrictB f v]
  exact SommeFacettes.proj_sum _ (fun k => restrictB_mem f k v) j

/-- The block `j` of the positive orthant. -/
def blockCone (f : Fin (n + 1) → I) (j : I) : Set (Fin (n + 1) → ℝ) :=
  {v | (∀ c, f c ≠ j → v c = 0) ∧ ∀ c, 0 ≤ v c}

/-- `Wⱼ`: the closed simplex of the block `j`, a convex body of `lⱼ`. -/
def blockW (f : Fin (n + 1) → I) (j : I) : Set (S n) := ofCone (blockCone f j)

omit [Fintype I] in
omit [DecidableEq I] in
theorem isPosCone_blockCone (f : Fin (n + 1) → I) (j : I) : IsPosCone (blockCone f j) :=
  fun c hc v hv => ⟨fun k hk => by simp [hv.1 k hk], fun k => by
    simpa using mul_nonneg hc.le (hv.2 k)⟩

omit [Fintype I] in
omit [DecidableEq I] in
theorem zero_mem_blockCone (f : Fin (n + 1) → I) (j : I) :
    (0 : Fin (n + 1) → ℝ) ∈ blockCone f j := ⟨fun _ _ => rfl, fun _ => le_rfl⟩

omit [Fintype I] in
omit [DecidableEq I] in
theorem convex_blockCone (f : Fin (n + 1) → I) (j : I) : Convex ℝ (blockCone f j) := by
  intro x hx y hy a b ha hb _
  exact ⟨fun c hc => by simp [hx.1 c hc, hy.1 c hc], fun c => by
    simpa using add_nonneg (mul_nonneg ha (hx.2 c)) (mul_nonneg hb (hy.2 c))⟩

omit [Fintype I] in
omit [DecidableEq I] in
theorem kPrime_blockW (f : Fin (n + 1) → I) (j : I) : kPrime (blockW f j) = blockCone f j := by
  rw [blockW, kPrime, insert_zero_F_ofCone (isPosCone_blockCone f j),
    insert_eq_of_mem (zero_mem_blockCone f j)]

omit [Fintype I] in
omit [DecidableEq I] in
theorem isClosed_blockCone (f : Fin (n + 1) → I) (j : I) : IsClosed (blockCone f j) := by
  have : blockCone f j = (⋂ c, ⋂ (_ : f c ≠ j), {v : Fin (n + 1) → ℝ | v c = 0}) ∩
      ⋂ c, {v : Fin (n + 1) → ℝ | 0 ≤ v c} := by
    ext v; simp [blockCone]
  rw [this]
  exact (isClosed_iInter fun c => isClosed_iInter fun _ =>
      isClosed_eq (continuous_apply c) continuous_const).inter
    (isClosed_iInter fun c => isClosed_le continuous_const (continuous_apply c))

omit [Fintype I] in
/-- **Instance of `IsCorpsConvexeDans`**: each block of the closed simplex is a convex body of
its coordinate subvariety (every block nonempty). -/
theorem isCorpsConvexeDans_blockW {f : Fin (n + 1) → I} (hf : Function.Surjective f) (j : I) :
    SommeFacettes.IsCorpsConvexeDans (blockL f j) (blockW f j) := by
  have hpos := isPosCone_blockCone f j
  refine ⟨⟨isConvexPart_ofCone_of_cone (convex_blockCone f j) hpos, fun m hm hm' => ?_⟩,
    ofCone_subset_ofCone fun v hv => hv.1,
    isClosed_ofCone hpos (isClosed_blockCone f j) (zero_mem_blockCone f j), ?_⟩
  · induction m using ind with
    | h v hv =>
    rw [neg_mk] at hm'
    rw [blockW, mk_mem_ofCone_iff hpos] at hm hm'
    exact hv (funext fun c => le_antisymm (by simpa using hm'.2 c) (hm.2 c))
  · obtain ⟨c0, hc0⟩ := hf j
    set B : Fin (n + 1) → ℝ := fun c => if f c = j then 1 else 0
    have hB0 : B ≠ 0 := fun h => by simpa [B, hc0] using congrFun h c0
    have hBL : B ∈ blockL f j := fun c hc => by simp [B, hc]
    let P : Set (Fin (n + 1) → ℝ) := {v | ∀ c, f c = j → 0 < v c}
    have hPpos : IsPosCone P := fun t ht v hv c hc => by simpa using mul_pos ht (hv c hc)
    have hPo : IsOpen P := by
      have : P = ⋂ c, {v : Fin (n + 1) → ℝ | f c = j → 0 < v c} := by ext v; simp [P]
      rw [this]
      refine isOpen_iInter_of_finite fun c => ?_
      by_cases h : f c = j
      · simpa [h] using isOpen_lt continuous_const (continuous_apply c)
      · simp [h]
    refine ⟨mk B hB0, SommeFacettes.mem_relInterior_iff.2 ⟨(mk_mem_linearSubvariety hB0).2 hBL,
      ofCone P, isOpen_ofCone hPpos hPo, mk_mem_ofCone hB0 fun c hc => by simp [B, hc], ?_⟩⟩
    rintro x ⟨hxP, hxl⟩
    induction x using ind with
    | h v hv =>
    rw [mk_mem_ofCone_iff hPpos] at hxP
    rw [mk_mem_linearSubvariety hv] at hxl
    rw [blockW, mk_mem_ofCone_iff hpos]
    refine ⟨hxl, fun c => ?_⟩
    by_cases h : f c = j
    · exact (hxP c h).le
    · rw [hxl c h]

theorem coneSomme_blockW (f : Fin (n + 1) → I) :
    SommeFacettes.coneSomme (isInternal_blockL f) (blockW f) = orthant n := by
  ext v
  show (∀ j, SommeFacettes.proj _ j v ∈ kPrime (blockW f j)) ↔ ∀ c, 0 ≤ v c
  simp only [proj_blockL, kPrime_blockW]
  constructor
  · intro h c
    simpa [restrictB] using (h (f c)).2 c
  · intro h j
    exact ⟨(restrictB_mem f j v), fun c => by
      unfold restrictB; split_ifs
      · exact h c
      · exact le_rfl⟩

/-- **The instance of the Remark**: for every surjective `f : {0, …, n} → I`, the blocks of the
closed simplex satisfy the hypotheses of the Remark, their sum exists, and the closure of the
sum is the closed simplex `simplexS n`. -/
theorem closure_somme_blockW {f : Fin (n + 1) → I} (hf : Function.Surjective f) :
    (∀ j, SommeFacettes.IsCorpsConvexeDans (blockL f j) (blockW f j)) ∧
      EstSommeS (SommeFacettes.sommeS (blockW f)) (blockW f) ∧
      ∀ w : Set (S n), EstSommeS w (blockW f) → closure w = simplexS n := by
  have hW := isCorpsConvexeDans_blockW hf
  refine ⟨hW, SommeFacettes.estSommeS_sommeS (isInternal_blockL f) hW, fun w hw => ?_⟩
  rw [SommeFacettes.closure_eq_ofCone_coneSomme (isInternal_blockL f) hW hw, coneSomme_blockW,
    simplexS]

/-- The blocks of `f = id` are the vertices: `S(n)` is the sum of the `n + 1` lines `ℝ eᵢ`,
and the closed simplex is the closed sum of its vertices. -/
theorem blockW_id (j : Fin (n + 1)) : blockW id j = {vertex j} := by
  ext x
  induction x using ind with
  | h v hv =>
  rw [blockW, mk_mem_ofCone_iff (isPosCone_blockCone _ j), mem_singleton_iff, vertex,
    mk_eq_mk_iff_exists_pos]
  constructor
  · rintro ⟨h0, hpos⟩
    have hvj : v = v j • Pi.single j 1 := by
      funext c
      by_cases hc : c = j
      · subst hc; simp
      · simp [hc, h0 c hc]
    have hj : 0 < v j := lt_of_le_of_ne (hpos j) fun h => hv (by rw [hvj, ← h, zero_smul])
    refine ⟨(v j)⁻¹, inv_pos.2 hj, ?_⟩
    rw [show (v j)⁻¹ • v = (v j)⁻¹ • (v j • Pi.single j (1 : ℝ)) from congrArg _ hvj, smul_smul,
      inv_mul_cancel₀ hj.ne', one_smul]
  · rintro ⟨t, ht, htv⟩
    have hv' : v = t⁻¹ • Pi.single j 1 := by
      rw [← htv, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
    refine ⟨fun c hc => by simp [hv', show c ≠ j from hc], fun c => ?_⟩
    rw [hv']
    by_cases hc : c = j
    · subst hc; simp [ht.le]
    · simp [hc]

theorem simplexS_closure_somme_vertices :
    ∀ w : Set (S n), EstSommeS w (blockW (id : Fin (n + 1) → Fin (n + 1))) →
      closure w = simplexS n :=
  (closure_somme_blockW Function.surjective_id).2.2


/-! ### A non-degenerate instance: the closed edge is not a facette, the open edge is -/

/-- `S(2) = l₀ ⊕ l₁` with `L₀ = ⟨e₀, e₁⟩`, `L₁ = ℝ e₂`. -/
def fArete : Fin 3 → Fin 2 := ![0, 0, 1]

theorem fArete_surjective : Function.Surjective fArete := by
  intro j
  fin_cases j
  · exact ⟨0, rfl⟩
  · exact ⟨2, rfl⟩

/-- **The literal reading of « les `Wᵢ` sont des facettes » fails off the points**: for the
closed triangle written as the closed sum of its closed edge `W₀ = [s(e₀), s(e₁)]` (in
`l₀ = s(⟨e₀, e₁⟩ − O)`) and its opposite vertex `W₁ = {s(e₂)}`, `W₀` is not a facette of the
closed sum, while its relative interior, the open edge, is a conical facette of closure `W₀`. -/
theorem exemple_arete_fermee (w : Set (S 2)) (hw : EstSommeS w (blockW fArete)) :
    ¬ IsFacetteK (closure w) (blockW fArete 0) ∧
      IsFacetteConique (closure w) (SommeFacettes.relInterior (blockL fArete 0) (blockW fArete 0)) ∧
      closure (SommeFacettes.relInterior (blockL fArete 0) (blockW fArete 0)) = blockW fArete 0 := by
  have hW := isCorpsConvexeDans_blockW fArete_surjective
  have hR := (SommeFacettes.remarque_somme_facettes_coniques (isInternal_blockL fArete) hW hw).2 0
  refine ⟨fun h => ?_, hR.1, hR.2.1⟩
  rw [SommeFacettes.isFacetteK_iff_relInterior_eq (isInternal_blockL fArete) hW hw] at h
  have he0 : (Pi.single 0 1 : Fin 3 → ℝ) ≠ 0 := by simp
  have hmem : mk _ he0 ∈ blockW fArete 0 := by
    rw [blockW, mk_mem_ofCone_iff (isPosCone_blockCone _ _)]
    refine ⟨fun c hc => ?_, fun c => ?_⟩
    · fin_cases c <;> simp_all [fArete]
    · fin_cases c <;> simp
  rw [← h] at hmem
  have hcore := SommeFacettes.isCore_of_mem_relInterior he0 hmem
  have hv : -(Pi.single 1 1 : Fin 3 → ℝ) ∈ blockL fArete 0 := by
    intro c hc
    fin_cases c <;> simp_all [fArete]
  obtain ⟨t, ht, hK⟩ := hcore.2 _ hv
  rw [kPrime_blockW] at hK
  have := hK.2 1
  simp at this
  linarith

/-! ### Reading (b): without strictness the Remark fails -/

/-- **Reading (b)**: the parenthetical « convexe fermé d'intérieur non vide » alone does not
suffice. `W = S(0) = l` (`L = E`, `p = 1`) is convex, closed, with nonempty interior in `l`; its
sum « `F(W)` » is not defined (`F(W) = E − O` is not convex, so no `w` is a sum of `W` in the
sense of § 2 Déf. 5), and reading (a)'s closure `s(F(W) ∪ {O} − O) = S(0)` is not a convex body. -/
theorem exemple_sans_stricte :
    IsConvexPart (univ : Set (S 0)) ∧ IsClosed (univ : Set (S 0)) ∧
      (univ : Set (S 0)) ⊆ linearSubvariety ⊤ ∧
      (SommeFacettes.relInterior ⊤ (univ : Set (S 0))).Nonempty ∧
      ofCone (kPrime (univ : Set (S 0))) = univ ∧ ¬ IsCorpsConvexeS 0 (univ : Set (S 0)) ∧
      ¬ ∃ w : Set (S 0), EstSommeS w (fun _ : Unit => (univ : Set (S 0))) := by
  have hku : kPrime (univ : Set (S 0)) = univ := by
    ext v; by_cases hv : v = 0
    · simp [hv, zero_mem_kPrime]
    · simp [mem_kPrime_of_ne hv, hv]
  have he : (fun _ => 1 : Fin 1 → ℝ) ≠ 0 := fun h => by simpa using congrFun h 0
  refine ⟨?_, isClosed_univ, by rw [linearSubvariety_eq_univ_iff.2 rfl], ?_, ?_, ?_, ?_⟩
  · show Convex ℝ (kPrime univ)
    rw [hku]; exact convex_univ
  · obtain ⟨x⟩ := (inferInstance : Nonempty (S 0))
    exact ⟨x, SommeFacettes.mem_relInterior_iff.2 ⟨by rw [linearSubvariety_eq_univ_iff.2 rfl]; trivial,
      univ, isOpen_univ, trivial, subset_univ _⟩⟩
  · rw [hku]
    ext x; induction x using ind with
    | h v hv => exact ⟨fun _ => trivial, fun _ => mk_mem_ofCone hv trivial⟩
  · rintro ⟨⟨-, h⟩, -⟩
    exact h (mk _ he) trivial trivial
  · rintro ⟨w, hw, -⟩
    have hc := hw ()
    have h1 : (fun _ => 1 : Fin 1 → ℝ) ∈ F (univ : Set (S 0)) := ⟨he, trivial⟩
    have h2 : -(fun _ => 1 : Fin 1 → ℝ) ∈ F (univ : Set (S 0)) := ⟨neg_ne_zero.2 he, trivial⟩
    have := hc h1 h2 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    rw [smul_neg, add_neg_cancel] at this
    exact zero_notMem_F _ this

/-- `S(3) = l₀ ⊕ l₁` with `L₀ = ⟨e₀, e₁⟩`, `L₁ = ⟨e₂, e₃⟩`. -/
def fArcs : Fin 4 → Fin 2 := ![0, 0, 1, 1]

theorem fArcs_surjective : Function.Surjective fArcs := by
  intro j
  fin_cases j
  · exact ⟨0, rfl⟩
  · exact ⟨2, rfl⟩

/-- **The planner's instance on `S(3)`**: the closed quarter arcs `Wᵢ` of `l₀ = s(⟨e₀, e₁⟩ − O)`
and `l₁ = s(⟨e₂, e₃⟩ − O)` are convex bodies of the `lᵢ`, the closure of their sum is the closed
simplex of `S(3)`, and their open arcs (two opposite open edges) are conical facettes of it, of
closures the closed arcs and supports the `lᵢ`. -/
theorem exemple_arcs_S3 (w : Set (S 3)) (hw : EstSommeS w (blockW fArcs)) :
    closure w = simplexS 3 ∧ ∀ i, IsFacetteConique (closure w)
      (SommeFacettes.relInterior (blockL fArcs i) (blockW fArcs i)) ∧
      closure (SommeFacettes.relInterior (blockL fArcs i) (blockW fArcs i)) = blockW fArcs i ∧
      supportK (SommeFacettes.relInterior (blockL fArcs i) (blockW fArcs i)) =
        linearSubvariety (blockL fArcs i) := by
  have hW := isCorpsConvexeDans_blockW fArcs_surjective
  exact ⟨(closure_somme_blockW fArcs_surjective).2.2 w hw,
    (SommeFacettes.remarque_somme_facettes_coniques (isInternal_blockL fArcs) hW hw).2⟩

end SommeFacettesInstance
end Benzecri
