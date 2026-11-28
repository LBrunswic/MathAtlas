import Benzecri.Chapter3.BalayableSommeProduit

/-!
# Chapter 3 § 2, Proposition 4: on the open segment, compatibility needs the torus factor

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 3 § 2, journal p. 268; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch3.tex` (TO BE CHECKED BY THE AUTHOR).
Target T-bz-c3-prop4-tore (OQ-171).

* `bzprop:c3s2p4_automorphisme_compatible` — `benzecri1960_ch3.tex:599` (Prop. 4, l.599–611),
  NOT marked (a strengthening of the evidence for OQ-171, not of Prop. 4; OQ-168 and OQ-171 are
  OPEN). The file proves, with no `sorry`, the clause that `BalayableSommeProduit.lean`'s SCOPE
  argued without formalizing: on the open segment `w = simplexO 1` of `S(1)` (two simple
  summands, each `Bᵢ` a point of `S(0)`), for EVERY projective isomorphism
  `Ψ : F⁻¹(F(B₀) × F(B₁)) ≃ w`, some projective automorphism of `w` is, once transported,
  compatible (`IsCompatiblePi`, Ch. 1 § 3 Déf. 2) but compatible ONLY with a torus factor
  `t ≠ 1`: `Benzecri.BooleProjectifInstance.simplexO_one_prop4_tore`.

> **Proposition 4.** Soient $w$ un ouvert convexe de $S(\R^{n+1})=S(n)$, de noyau vide, $l_i$
> les $p$ sous-variétés distinguées simples relatives à $w$, $v_i$ les convexes de $l_i$ dont
> $w$ est la somme; on peut écrire avec les notations du chapitre 1, paragraphes 1 et 2
> $$ w=F^{-1}(F(v_1)\times\ldots\times F(v_p)) $$
> tout automorphisme projectif de $w$ est un automorphisme compatible au sens du chapitre 1,
> paragraphe 3, définition 2.
>
> *Démonstration.* En effet, un automorphisme projectif de $w$ est un élément de $GP(n, \R)$ qui
> permute entre elles les variétés distinguées simples.

The pieces, each proved:

* `IsCompatibleAssocPiOne σ f`: Déf. 2's `f ∈ {F⁻¹(φ)} × (ℝ^{+p}/ℝ^+)` with the torus factor
  `t = 1`, i.e. `f = F⁻¹(φ)` (`isCompatibleAssocPiOne_iff`); instance `isCompatibleAssocPiOne_one`.
* `OpensZero.coneIso_eq_self`: for `B` a one-point open of `S(0)`, the only conical automorphism
  of `F(B) ≅ ℝ₊*` is the identity (a conical morphism is `±1` in the global cone chart, and it
  preserves the half-line); `OpensZero.coneIso_unique`. The argument rests on Benzécri's own
  definition of conical isomorphisms as `GU` maps, `|det| = 1` (ch. 1, l.489–512).
* `PointFactors.ncard_compatibleOne_le`: with `p = q + 1` factors, each a point of `S(0)`, at
  most `p!` automorphisms of `F⁻¹(F(B₀) × … × F(B_q))` are compatible with `t = 1`.
* `torus_ne_one_of_not_compatibleOne`: not compatible with `t = 1` means every representation
  `f = t ∘ F⁻¹(φ)` (Déf. 2, `IsCompatibleAssocPi`) has `t ≠ 1`.
* `transportAut` (`Ψ⁻¹ ∘ f ∘ Ψ`, injective) and `isCompatiblePi_transportAut`: compatibility of
  every transport along `prop4_produit`'s own `Ψ₀` gives it along EVERY `Ψ`.
* `Segment.infinite_aut`: the automorphisms `s(diag(1, j + 1))` of the open segment are
  pairwise distinct; `Segment.exists_aut_not_compatibleOne`: for every `Ψ`, one of them is
  compatible with no `t = 1`.
* Instance: `BooleProjectifInstance.simplexO_one_prop4_tore_instance` (the hypotheses are met,
  through `prop4_produit` at `n = 1`).

## Hypothesis checklist

| paper hypothesis / claim | here |
|---|---|
| `w` the open segment of `S(1)`, `p = 2`, `Bᵢ` points of `S(0)` | ✓ `simplexO 1`; the `Bᵢ` are Prop. 4's `s(bᵢ(F(vᵢ)))` for EVERY enumeration `l` and bases `b` |
| « on peut écrire … $w=F^{-1}(F(v_1)\times F(v_2))$ » | ✓ EVERY projective isomorphism `Ψ` (`IsProjIso (pdim k) 1 Ψ`), not only `prop4_produit`'s |
| « automorphisme compatible » | ✓ the transport is `IsCompatiblePi` (from `prop4_produit` and conjugation) |
| the printed proof's « élément de $GP(n, \R)$ », read as `t = 1` | refuted for this `w`: `¬ ∃ σ, IsCompatibleAssocPiOne σ _`, equivalently every representation has `t ≠ 1` |

## SCOPE (disclosed)

* This is evidence for a reading (OQ-171), not a new statement of Prop. 4, which `prop4_produit`
  already proves in the reading with a torus factor: no mark changes.
* The concrete automorphism is produced by a counting argument (at most `2! = 2` automorphisms
  compatible with `t = 1`, infinitely many automorphisms of `w`, the transport injective); it is
  one of the `s(diag(1, j + 1))`, not named as `s(diag(1, 2))`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Function Filter Topology

namespace Benzecri

attribute [local instance] t2Space_RnO

/-! ### Compatibility with the torus factor `t = 1` -/

section One

open PiCone

variable {q : ℕ} {n : Fin (q + 1) → ℕ} {B : Fin (q + 1) → Type*} [∀ i, TopologicalSpace (B i)]
  [∀ i, ChartedSpace (S (n i)) (B i)] [∀ i, HasGroupoid (B i) (projGroupoid (n i))]
  [∀ i, T2Space (B i)]

/-- **Compatible with the torus factor `t = 1`** (Déf. 2's `f ∈ {F⁻¹(φ)} × (ℝ^{+p}/ℝ^+)` with
the factor in `ℝ^{+p}/ℝ^+` trivial): `f = F⁻¹(φ)`, `φ(m)ᵢ = φᵢ m_{σ(i)}`, the `φᵢ` conical
affine isomorphisms `F(B_{σ(i)}) ≅ F(Bᵢ)`. -/
def IsCompatibleAssocPiOne (σ : Equiv.Perm (Fin (q + 1)))
    (f : GXAut (GSR (pdim n)) (S (pdim n)) (PiBase n B)) : Prop :=
  ∃ φ : ∀ i, FCone (n (σ i)) (B (σ i)) ≃ₜ FCone (n i) (B i),
    (∀ i, IsConeIso (n (σ i)) (n i) (φ i)) ∧
      ∀ x : ∀ i, FCone (n i) (B i), f • (ConeBase.mk x : PiBase n B) =
        ConeBase.mk fun i => φ i (x (σ i))

/-- `IsCompatibleAssocPiOne` is `IsCompatibleAssocPi` with `t = 1`. -/
theorem isCompatibleAssocPiOne_iff {σ : Equiv.Perm (Fin (q + 1))}
    {f : GXAut (GSR (pdim n)) (S (pdim n)) (PiBase n B)} :
    IsCompatibleAssocPiOne σ f ↔
      ∃ φ : ∀ i, FCone (n (σ i)) (B (σ i)) ≃ₜ FCone (n i) (B i),
        (∀ i, IsConeIso (n (σ i)) (n i) (φ i)) ∧
          ∀ x : ∀ i, FCone (n i) (B i), f • (ConeBase.mk x : PiBase n B) =
            piTorusAut n (fun i => FCone (n i) (B i)) 1 • ConeBase.mk fun i => φ i (x (σ i)) := by
  simp only [IsCompatibleAssocPiOne, map_one, one_smul]

/-- Compatible with `t = 1` implies compatible. -/
theorem IsCompatibleAssocPiOne.isCompatibleAssocPi
    {σ : Equiv.Perm (Fin (q + 1))} {f : GXAut (GSR (pdim n)) (S (pdim n)) (PiBase n B)}
    (h : IsCompatibleAssocPiOne σ f) : IsCompatibleAssocPi σ f := by
  obtain ⟨φ, hφ, hx⟩ := isCompatibleAssocPiOne_iff.1 h
  exact ⟨φ, hφ, 1, hx⟩

/-- **Not compatible with `t = 1` means: every representation `f = t ∘ F⁻¹(φ)` has `t ≠ 1`.** -/
theorem torus_ne_one_of_not_compatibleOne {f : GXAut (GSR (pdim n)) (S (pdim n)) (PiBase n B)}
    (hf : ¬ ∃ σ, IsCompatibleAssocPiOne σ f) {σ : Equiv.Perm (Fin (q + 1))}
    {φ : ∀ i, FCone (n (σ i)) (B (σ i)) ≃ₜ FCone (n i) (B i)}
    (hφ : ∀ i, IsConeIso (n (σ i)) (n i) (φ i)) {t : PiTorus q}
    (ht : ∀ x : ∀ i, FCone (n i) (B i), f • (ConeBase.mk x : PiBase n B) =
      piTorusAut n (fun i => FCone (n i) (B i)) t • ConeBase.mk fun i => φ i (x (σ i))) :
    t ≠ 1 := by
  rintro rfl
  exact hf ⟨σ, isCompatibleAssocPiOne_iff.2 ⟨φ, hφ, ht⟩⟩

/-- **Instance**: the identity is compatible with `t = 1`, associated with the identity. -/
theorem isCompatibleAssocPiOne_one :
    IsCompatibleAssocPiOne (n := n) (B := B) 1 1 := by
  exact ⟨fun i => Homeomorph.refl _, fun _ => IsConeIso.refl, fun x => rfl⟩

end One

/-! ### A one-point open of `S(0)`: its cone `ℝ₊*` has only the identity as conical automorphism -/

namespace OpensZero

/-- An element of `GU(1)` fixing the ray of `v` fixes `v` (it is `±1`, and `-1` moves the ray). -/
theorem GUR_one_smul_eq_self {g : GUR 1} {v : RnO 1}
    (h : Punctured.toSphere (g • v) = Punctured.toSphere v) : g • v = v := by
  obtain ⟨c, hc, hcv⟩ :=
    (Sphere.mk_eq_mk_iff_exists_pos v.val_ne_zero (g • v).val_ne_zero).1 h.symm
  set G : (Fin 1 → ℝ) ≃ₗ[ℝ] (Fin 1 → ℝ) := (g : GLR 1) with hG
  have hGv : G v.val = c • v.val := by
    rw [hcv]
    rfl
  have hv0 : v.val 0 ≠ 0 := fun h0 => v.val_ne_zero (funext fun i => by
    obtain rfl : i = 0 := Fin.fin_one_eq_zero i
    exact h0)
  have hlin : (G : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ)) = c • LinearMap.id := by
    refine LinearMap.ext fun u => ?_
    have hu : u = (u 0 / v.val 0) • v.val := funext fun i => by
      obtain rfl : i = 0 := Fin.fin_one_eq_zero i
      simp [div_mul_cancel₀ _ hv0]
    rw [LinearMap.smul_apply, LinearMap.id_apply, LinearEquiv.coe_coe, hu, map_smul, hGv,
      smul_comm]
  have hdet : |((LinearEquiv.det G : ℝˣ) : ℝ)| = 1 := mem_GU.1 g.2
  rw [LinearEquiv.coe_det, hlin, LinearMap.det_smul, LinearMap.det_id, Module.finrank_fin_fun,
    pow_one, mul_one, abs_of_pos hc] at hdet
  subst hdet
  exact Punctured.ext (by rw [← hcv, one_smul])

/-- **The only conical automorphism of `F(B)`, `B` a one-point open of `S(0)`, is the
identity.** -/
theorem coneIso_eq_self {B : TopologicalSpace.Opens (S 0)} (hB : (B : Set (S 0)).Subsingleton)
    {φ : FCone 0 B ≃ₜ FCone 0 B} (hφ : IsConeIso 0 0 φ) (x : FCone 0 B) : φ x = x := by
  obtain ⟨hk, g, hg⟩ := hφ.exists_smul_eq x
  have hc : ∀ y : FCone 0 B, chartAt (RnO (0 + 1)) y = OpensCone.gcc (FCone.proj y) :=
    fun _ => rfl
  have hmem : ∀ (x₀ : B) (y : FCone 0 B),
      Punctured.toSphere (OpensCone.gcc x₀ y) ∈ (B : Set (S 0)) := fun x₀ y => by
    have h1 := (OpensCone.gcc x₀).map_source (x := y) (by rw [OpensCone.gcc_source]; trivial)
    rwa [OpensCone.gcc_target] at h1
  have h1 : OpensCone.gcc (FCone.proj (φ x)) (φ x) = g • OpensCone.gcc (FCone.proj x) x := by
    rw [← hc, ← hc]
    exact hg.self_of_nhds
  have h2 : OpensCone.gcc (FCone.proj x) (φ x) = OpensCone.gcc (FCone.proj x) x := by
    have h3 : OpensCone.gcc (FCone.proj (φ x)) (φ x) = OpensCone.gcc (FCone.proj x) (φ x) := rfl
    rw [← h3, h1]
    refine GUR_one_smul_eq_self ?_
    rw [← h1]
    exact hB (hmem _ _) (hmem _ _)
  exact (OpensCone.gcc (FCone.proj x)).injOn (by rw [OpensCone.gcc_source]; trivial)
    (by rw [OpensCone.gcc_source]; trivial) h2

/-- **Two conical isomorphisms onto the cone of a one-point open of `S(0)` agree.** -/
theorem coneIso_unique {B B' : TopologicalSpace.Opens (S 0)} (hB' : (B' : Set (S 0)).Subsingleton)
    {φ φ' : FCone 0 B ≃ₜ FCone 0 B'} (hφ : IsConeIso 0 0 φ) (hφ' : IsConeIso 0 0 φ') :
    φ = φ' := by
  ext y
  have h := coneIso_eq_self hB' (hφ'.symm.trans hφ) (φ' y)
  simpa using h

/-- **A part of `S(0)` with a convex cone is at most a point** (`F(B)` convex and `O ∉ F(B)`, so
`F(B)` does not meet both half-lines). -/
theorem subsingleton_of_convex_F {k : ℕ} (hk : k = 0) {B : Set (S k)}
    (h : Convex ℝ (Sphere.F B)) : B.Subsingleton := by
  subst hk
  intro x hx y hy
  induction x using Sphere.ind with
  | h u hu =>
  induction y using Sphere.ind with
  | h v hv =>
  have hu' : u ∈ Sphere.F B := ⟨hu, hx⟩
  have hv' : v ∈ Sphere.F B := ⟨hv, hy⟩
  have h0 : ∀ w : Fin (0 + 1) → ℝ, w ≠ 0 → w 0 ≠ 0 := fun w hw h0 => hw (funext fun i => by
    obtain rfl : i = 0 := Fin.fin_one_eq_zero i
    exact h0)
  have ha := h0 u hu
  have hb := h0 v hv
  rcases lt_or_gt_of_ne (mul_ne_zero ha hb) with hab | hab
  · exfalso
    have hba : v 0 - u 0 ≠ 0 := fun h => by
      have : v 0 = u 0 := sub_eq_zero.1 h
      rw [this] at hab
      nlinarith [mul_self_nonneg (u 0)]
    have hα : 0 ≤ v 0 / (v 0 - u 0) ∧ 0 ≤ -u 0 / (v 0 - u 0) := by
      rcases lt_or_gt_of_ne ha with hu0 | hu0
      · have hv0 : 0 < v 0 := by nlinarith
        exact ⟨div_nonneg hv0.le (by linarith), div_nonneg (by linarith) (by linarith)⟩
      · have hv0 : v 0 < 0 := by nlinarith
        exact ⟨div_nonneg_of_nonpos hv0.le (by linarith),
          div_nonneg_of_nonpos (by linarith) (by linarith)⟩
    have hsum : v 0 / (v 0 - u 0) + -u 0 / (v 0 - u 0) = 1 := by
      field_simp
      ring
    have hm := h hu' hv' hα.1 hα.2 hsum
    have hz : (v 0 / (v 0 - u 0)) • u + (-u 0 / (v 0 - u 0)) • v = 0 := funext fun i => by
      obtain rfl : i = 0 := Fin.fin_one_eq_zero i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      field_simp
      ring
    rw [hz] at hm
    exact Sphere.zero_notMem_F _ hm
  · refine (Sphere.mk_eq_mk_iff_exists_pos hu hv).2 ⟨v 0 / u 0, ?_, funext fun i => ?_⟩
    · rcases lt_or_gt_of_ne ha with hu0 | hu0
      · exact div_pos_of_neg_of_neg (by nlinarith) hu0
      · exact div_pos (by nlinarith) hu0
    · obtain rfl : i = 0 := Fin.fin_one_eq_zero i
      simp only [Pi.smul_apply, smul_eq_mul]
      field_simp

end OpensZero

/-! ### `p` factors, each a point of `S(0)`: at most `p!` automorphisms compatible with `t = 1` -/

namespace PointFactors

open PiCone

variable {q : ℕ} {B : Fin (q + 1) → TopologicalSpace.Opens (S 0)}

/-- **Uniqueness per permutation**: two automorphisms compatible with `t = 1` for the same `σ`
are equal, when every `Bᵢ` is a point of `S(0)`. -/
theorem IsCompatibleAssocPiOne.unique (hB : ∀ i, (B i : Set (S 0)).Subsingleton)
    {σ : Equiv.Perm (Fin (q + 1))}
    {f f' : GXAut (GSR (pdim fun _ : Fin (q + 1) => 0)) (S (pdim fun _ : Fin (q + 1) => 0))
      (PiBase (fun _ : Fin (q + 1) => 0) fun i => B i)}
    (h : IsCompatibleAssocPiOne (n := fun _ => 0) (B := fun i => B i) σ f)
    (h' : IsCompatibleAssocPiOne (n := fun _ => 0) (B := fun i => B i) σ f') : f = f' := by
  obtain ⟨φ, hφ, hx⟩ := h
  obtain ⟨φ', hφ', hx'⟩ := h'
  have he : ∀ i, φ i = φ' i := fun i => OpensZero.coneIso_unique (hB i) (hφ i) (hφ' i)
  refine FaithfulSMul.eq_of_smul_eq_smul
    fun p : PiBase (fun _ : Fin (q + 1) => 0) (fun i => B i) => ?_
  obtain ⟨x, rfl⟩ := ConeBase.mk_surjective p
  rw [hx, hx']
  exact congrArg ConeBase.mk (funext fun i => by rw [he i])

/-- **At most `p!` automorphisms of `F⁻¹(F(B₀) × … × F(B_q))` are compatible with `t = 1`**, when
every `Bᵢ` is a point of `S(0)`; the set is finite. -/
theorem ncard_compatibleOne_le (hB : ∀ i, (B i : Set (S 0)).Subsingleton) :
    {f : GXAut (GSR (pdim fun _ : Fin (q + 1) => 0)) (S (pdim fun _ : Fin (q + 1) => 0))
        (PiBase (fun _ : Fin (q + 1) => 0) fun i => B i) |
        ∃ σ, IsCompatibleAssocPiOne (n := fun _ => 0) (B := fun i => B i) σ f}.Finite ∧
      {f : GXAut (GSR (pdim fun _ : Fin (q + 1) => 0)) (S (pdim fun _ : Fin (q + 1) => 0))
        (PiBase (fun _ : Fin (q + 1) => 0) fun i => B i) |
        ∃ σ, IsCompatibleAssocPiOne (n := fun _ => 0) (B := fun i => B i) σ f}.ncard ≤ (q + 1).factorial := by
  classical
  set T := {f : GXAut (GSR (pdim fun _ : Fin (q + 1) => 0)) (S (pdim fun _ : Fin (q + 1) => 0))
      (PiBase (fun _ : Fin (q + 1) => 0) fun i => B i) |
      ∃ σ, IsCompatibleAssocPiOne (n := fun _ => 0) (B := fun i => B i) σ f} with hT
  let g : Equiv.Perm (Fin (q + 1)) → GXAut (GSR (pdim fun _ : Fin (q + 1) => 0))
      (S (pdim fun _ : Fin (q + 1) => 0)) (PiBase (fun _ : Fin (q + 1) => 0) fun i => B i) :=
    fun σ => if h : ∃ f, IsCompatibleAssocPiOne (n := fun _ => 0) (B := fun i => B i) σ f then
      h.choose else 1
  have hsub : T ⊆ range g := by
    rintro f ⟨σ, hf⟩
    have h : ∃ f, IsCompatibleAssocPiOne (n := fun _ => 0) (B := fun i => B i) σ f := ⟨f, hf⟩
    refine ⟨σ, ?_⟩
    show (if h : ∃ f, IsCompatibleAssocPiOne (n := fun _ => 0) (B := fun i => B i) σ f then
      h.choose else 1) = f
    rw [dif_pos h]
    exact IsCompatibleAssocPiOne.unique hB h.choose_spec hf
  refine ⟨(Set.finite_range g).subset hsub, ?_⟩
  calc T.ncard ≤ (range g).ncard := Set.ncard_le_ncard hsub (Set.finite_range g)
    _ = (g '' univ).ncard := by rw [Set.image_univ]
    _ ≤ (univ : Set (Equiv.Perm (Fin (q + 1)))).ncard := Set.ncard_image_le Set.finite_univ
    _ = (q + 1).factorial := by
      rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]

end PointFactors

/-! ### Transport of automorphisms along a projective isomorphism -/

section Transport

variable {k m : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (S k) X]
  {W : TopologicalSpace.Opens (S m)}

/-- **The transport** `Ψ⁻¹ ∘ f ∘ Ψ` of an automorphism of `W` along `Ψ : X ≃ W`. -/
def transportAut {Ψ : X ≃ₜ W} (hΨ : IsProjIso k m Ψ) (f : GXAut (GSR m) (S m) W) :
    GXAut (GSR k) (S k) X :=
  ((hΨ.trans (⟨rfl, f.isGXMorphism⟩ : IsProjIso m m f.toHomeomorph)).trans hΨ.symm).toAut

theorem transportAut_smul {Ψ : X ≃ₜ W} (hΨ : IsProjIso k m Ψ) (f : GXAut (GSR m) (S m) W)
    (x : X) : transportAut hΨ f • x = Ψ.symm (f • Ψ x) := rfl

/-- The transport is injective. -/
theorem transportAut_injective {Ψ : X ≃ₜ W} (hΨ : IsProjIso k m Ψ) :
    Injective (transportAut hΨ) := by
  intro f f' h
  refine FaithfulSMul.eq_of_smul_eq_smul fun y : W => Ψ.symm.injective ?_
  have h1 := congrArg (· • Ψ.symm y) h
  simp only [transportAut_smul, Homeomorph.apply_symm_apply] at h1
  exact h1

/-- **A subgroup containing every transport along one `Ψ₀` contains every transport along every
`Ψ`** (`Ψ⁻¹ f Ψ = a⁻¹ (Ψ₀⁻¹ f Ψ₀) a`, `a = Ψ₀⁻¹ Ψ` itself the transport of `Ψ Ψ₀⁻¹`). -/
theorem transportAut_mem_of_forall {Ψ₀ Ψ : X ≃ₜ W} (hΨ₀ : IsProjIso k m Ψ₀)
    (hΨ : IsProjIso k m Ψ) (P : Subgroup (GXAut (GSR k) (S k) X))
    (h₀ : ∀ f, transportAut hΨ₀ f ∈ P) (f : GXAut (GSR m) (S m) W) : transportAut hΨ f ∈ P := by
  set a := transportAut hΨ₀ (hΨ₀.symm.trans hΨ).toAut with ha
  have key : transportAut hΨ f = a⁻¹ * (transportAut hΨ₀ f * a) := by
    refine FaithfulSMul.eq_of_smul_eq_smul fun x : X => ?_
    rw [mul_smul, mul_smul, eq_inv_smul_iff, ha]
    simp only [transportAut_smul, IsProjIso.toAut_smul, Homeomorph.trans_apply,
      Homeomorph.apply_symm_apply, Homeomorph.symm_apply_apply]
  rw [key]
  exact P.mul_mem (P.inv_mem (h₀ _)) (P.mul_mem (h₀ f) (h₀ _))

end Transport

section TransportPi

open PiCone

variable {q : ℕ} {n : Fin (q + 1) → ℕ} {B : Fin (q + 1) → Type*} [∀ i, TopologicalSpace (B i)]
  [∀ i, ChartedSpace (S (n i)) (B i)] [∀ i, HasGroupoid (B i) (projGroupoid (n i))]
  [∀ i, T2Space (B i)] {m : ℕ} {W : TopologicalSpace.Opens (S m)}

/-- **Compatibility along one `Ψ₀` gives compatibility along every `Ψ`** (`compatibleSubgroup`
is a subgroup): `prop4_produit` for its own `Ψ₀` holds for every projective isomorphism. -/
theorem isCompatiblePi_transportAut {Ψ₀ Ψ : PiBase n B ≃ₜ W} (hΨ₀ : IsProjIso (pdim n) m Ψ₀)
    (hΨ : IsProjIso (pdim n) m Ψ)
    (h₀ : ∀ f : GXAut (GSR m) (S m) W,
      ∃ h : IsProjIso (pdim n) (pdim n) ((Ψ₀.trans f.toHomeomorph).trans Ψ₀.symm),
        IsCompatiblePi h.toAut)
    (f : GXAut (GSR m) (S m) W) : IsCompatiblePi (transportAut hΨ f) :=
  transportAut_mem_of_forall hΨ₀ hΨ (compatibleSubgroup n B)
    (fun f => (h₀ f).elim fun _ hc => hc) f

end TransportPi

/-! ### The open segment `simplexO 1` of `S(1)` -/

namespace Segment

open PiCone

/-- The open segment `s{(a, b) | a, b > 0}` of `S(1)`, as an open. -/
abbrev wO : TopologicalSpace.Opens (S 1) := ⟨BooleProjectifInstance.simplexO 1, BooleProjectifInstance.isOpen_simplexO⟩

/-- The diagonal coefficients `(1, j + 1)`. -/
def diagC (j : ℕ) (i : Fin 2) : ℝ := (j : ℝ) * ((i : ℕ) : ℝ) + 1

theorem diagC_pos (j : ℕ) (i : Fin 2) : 0 < diagC j i := by
  unfold diagC
  positivity

/-- `diag(1, j + 1)`. -/
def diagL (j : ℕ) : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ) where
  toFun v i := diagC j i * v i
  invFun v i := (diagC j i)⁻¹ * v i
  map_add' v w := funext fun i => mul_add _ _ _
  map_smul' c v := funext fun i => by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
  left_inv v := funext fun i => inv_mul_cancel_left₀ (diagC_pos j i).ne' _
  right_inv v := funext fun i => mul_inv_cancel_left₀ (diagC_pos j i).ne' _

theorem diagL_apply (j : ℕ) (v : Fin 2 → ℝ) (i : Fin 2) : diagL j v i = diagC j i * v i := rfl

/-- `s(diag(1, j + 1))` preserves the open segment. -/
theorem diagL_mem_iff (j : ℕ) (x : S 1) :
    (QuotientGroup.mk (diagL j) : GSR 1) • x ∈ wO ↔ x ∈ wO := by
  induction x using Sphere.ind with
  | h v hv =>
  show _ ∈ BooleProjectifInstance.simplexO 1 ↔ _ ∈ BooleProjectifInstance.simplexO 1
  rw [GSE.mk_smul, Sphere.smul_mk, Sphere.mk_mem_iff_mem_F, Sphere.mk_mem_iff_mem_F,
    BooleProjectifInstance.F_simplexO]
  simp only [BooleProjectifInstance.orthO, Set.mem_setOf_eq, diagL_apply]
  exact forall_congr' fun i => mul_pos_iff_of_pos_left (diagC_pos j i)

/-- **The automorphism `s(diag(1, j + 1))` of the open segment.** -/
def diagAut (j : ℕ) : GXAut (GSR 1) (S 1) wO :=
  GXAut.ofOpens wO (QuotientGroup.mk (diagL j) : GSR 1) (diagL_mem_iff j)

/-- The `s(diag(1, j + 1))` are pairwise distinct. -/
theorem diagAut_injective : Injective diagAut := by
  intro j j' h
  have h1 : (1 : Fin 2 → ℝ) ≠ 0 := fun h0 => by simpa using congrFun h0 0
  have hx : Sphere.mk (1 : Fin 2 → ℝ) h1 ∈ wO := by
    show _ ∈ BooleProjectifInstance.simplexO 1
    rw [Sphere.mk_mem_iff_mem_F, BooleProjectifInstance.F_simplexO]
    intro i
    exact one_pos
  have h2 := congrArg (fun f : GXAut (GSR 1) (S 1) wO =>
    ((f • (⟨_, hx⟩ : wO) : wO) : S 1)) h
  simp only [diagAut, GXAut.ofOpens_smul, GSE.mk_smul, Sphere.smul_mk] at h2
  obtain ⟨c, hc, hcv⟩ := (Sphere.mk_eq_mk_iff_exists_pos _ _).1 h2
  have h0 := congrFun hcv 0
  have h1' := congrFun hcv 1
  simp only [Pi.smul_apply, diagL_apply, diagC, Pi.one_apply, smul_eq_mul] at h0 h1'
  norm_num at h0 h1'
  subst h0
  simpa using h1'

/-- **The open segment has infinitely many projective automorphisms.** -/
theorem infinite_aut : Infinite (GXAut (GSR 1) (S 1) wO) :=
  Infinite.of_injective _ diagAut_injective

/-- `exists_aut_not_compatibleOne` with the dimensions `nᵢ = 0` given. -/
theorem exists_aut_not_compatibleOne_zero {B : Fin (1 + 1) → TopologicalSpace.Opens (S 0)}
    (hB : ∀ i, (B i : Set (S 0)).Subsingleton)
    (Ψ : PiBase (fun _ : Fin (1 + 1) => 0) (fun i => B i) ≃ₜ wO)
    (hΨ : IsProjIso (pdim fun _ : Fin (1 + 1) => 0) 1 Ψ) :
    ∃ f : GXAut (GSR 1) (S 1) wO, ¬ ∃ σ, IsCompatibleAssocPiOne (n := fun _ => 0)
      (B := fun i => B i) σ (transportAut hΨ f) := by
  haveI := infinite_aut
  obtain ⟨hfin, -⟩ := PointFactors.ncard_compatibleOne_le (q := 1) hB
  obtain ⟨f, hf⟩ := (hfin.preimage (transportAut_injective hΨ).injOn).infinite_compl.nonempty
  exact ⟨f, hf⟩

/-- **For every projective isomorphism `Ψ : F⁻¹(F(B₀) × F(B₁)) ≃ w`, `Bᵢ` points of `S(0)`, some
automorphism of the open segment `w` is, once transported, compatible with no `t = 1`.** -/
theorem exists_aut_not_compatibleOne {n : Fin (1 + 1) → ℕ} {B : ∀ i, TopologicalSpace.Opens (S (n i))}
    (hB : ∀ i, (B i : Set (S (n i))).Subsingleton)
    (Ψ : PiBase n (fun i => B i) ≃ₜ wO) (hΨ : IsProjIso (pdim n) 1 Ψ) :
    ∃ f : GXAut (GSR 1) (S 1) wO,
      ¬ ∃ σ, IsCompatibleAssocPiOne (n := n) (B := fun i => B i) σ (transportAut hΨ f) := by
  have hp : pdim n = 1 := hΨ.1
  have hn : n = fun _ => 0 := by
    unfold pdim at hp
    rw [Fin.sum_univ_two] at hp
    funext i
    fin_cases i <;> simp <;> omega
  subst hn
  exact exists_aut_not_compatibleOne_zero hB Ψ hΨ

end Segment

/-! ### Prop. 4's own `Bᵢ` on the open segment -/

namespace BooleProjectifInstance

open Sphere Segment PiCone

/-- **Prop. 4 on the open segment needs the torus factor** (OQ-171): for every enumeration `l`
of the two simple distinguished subvarieties of `w = simplexO 1`, every bases `bᵢ`, and EVERY
projective isomorphism `Ψ : F⁻¹(F(B₀) × F(B₁)) ≃ w` (`Bᵢ = s(bᵢ(F(vᵢ)))`), some projective
automorphism of `w` is, transported, compatible (Déf. 2) and every representation of it as
`t ∘ F⁻¹(φ)` has `t ≠ 1`. -/
theorem simplexO_one_prop4_tore (l : Fin (1 + 1) ≃ simplesS (simplexO 1)) (k : Fin (1 + 1) → ℕ)
    (b : ∀ i, (l i : Submodule ℝ (Fin (1 + 1) → ℝ)) ≃ₗ[ℝ] (Fin (k i + 1) → ℝ))
    (hB : ∀ i, IsOpen (ofCone (b i '' (Subtype.val ⁻¹' sommandeS (simplexO 1) (l i))) :
      Set (S (k i))))
    (Ψ : PiBase k (fun i => (⟨_, hB i⟩ : TopologicalSpace.Opens (S (k i)))) ≃ₜ wO)
    (hΨ : IsProjIso (pdim k) 1 Ψ) :
    ∃ f : GXAut (GSR 1) (S 1) wO, IsCompatiblePi (transportAut hΨ f) ∧
      ¬ ∃ σ, IsCompatibleAssocPiOne (n := k)
        (B := fun i => (⟨_, hB i⟩ : TopologicalSpace.Opens (S (k i)))) σ (transportAut hΨ f) := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := simplexO_hyps4 (n := 1)
  have H : Hyps4 (simplexO 1) := ⟨h1, h2, h3, h4, h5⟩
  have hp : pdim k = 1 := hΨ.1
  have hk : ∀ i, k i = 0 := by
    unfold pdim at hp
    rw [Fin.sum_univ_two] at hp
    intro i
    fin_cases i <;> simp <;> omega
  have hsub : ∀ i, ((⟨_, hB i⟩ : TopologicalSpace.Opens (S (k i))) : Set (S (k i))).Subsingleton :=
    fun i => by
      refine OpensZero.subsingleton_of_convex_F (hk i) ?_
      show Convex ℝ (F (ofCone (Produit.cset l k b i)))
      rw [Produit.F_ofCone_cset H i]
      exact ((H.convex_sommande (l i : Submodule ℝ (Fin (1 + 1) → ℝ))).linear_preimage
        (l i : Submodule ℝ (Fin (1 + 1) → ℝ)).subtype).linear_image (b i).toLinearMap
  obtain ⟨f, hf⟩ := exists_aut_not_compatibleOne hsub Ψ hΨ
  refine ⟨f, ?_, hf⟩
  exact (prop4_produit h1 h2 h3 h4 h5 l k b).elim fun _ h => h.elim fun Ψ₀ h =>
    isCompatiblePi_transportAut h.1 hΨ h.2 f

/-- **Instance**: the hypotheses of `simplexO_one_prop4_tore` are met (`prop4_produit` at `n = 1`
provides `l`, `k`, `b` and a projective isomorphism `Ψ`). -/
theorem simplexO_one_prop4_tore_instance :
    ∃ (l : Fin (1 + 1) ≃ simplesS (simplexO 1)) (k : Fin (1 + 1) → ℕ)
      (b : ∀ i, (l i : Submodule ℝ (Fin (1 + 1) → ℝ)) ≃ₗ[ℝ] (Fin (k i + 1) → ℝ))
      (hB : ∀ i, IsOpen (ofCone (b i '' (Subtype.val ⁻¹' sommandeS (simplexO 1) (l i))) :
        Set (S (k i))))
      (Ψ : PiBase k (fun i => (⟨_, hB i⟩ : TopologicalSpace.Opens (S (k i)))) ≃ₜ wO)
      (hΨ : IsProjIso (pdim k) 1 Ψ),
      ∃ f : GXAut (GSR 1) (S 1) wO, IsCompatiblePi (transportAut hΨ f) ∧
        ¬ ∃ σ, IsCompatibleAssocPiOne (n := k)
          (B := fun i => (⟨_, hB i⟩ : TopologicalSpace.Opens (S (k i)))) σ (transportAut hΨ f) := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := simplexO_hyps4 (n := 1)
  refine (simplexO_prop4 (n := 1)).elim fun l _ => ?_
  refine (exists_bases_simplesS l).elim fun k hk => hk.elim fun b => ?_
  exact (prop4_produit h1 h2 h3 h4 h5 l k b).elim fun hB h => h.elim fun Ψ h =>
    ⟨l, k, b, hB, Ψ, h.1, simplexO_one_prop4_tore l k b hB Ψ h.1⟩

end BooleProjectifInstance

end Benzecri
