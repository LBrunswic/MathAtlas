import Benzecri.Chapter3.Sature
import Benzecri.Chapter3.ReunionConvexesSphere
import Mathlib.LinearAlgebra.Basis.Fin
import Benzecri.Chapter3.PointsExtremaux
import Benzecri.Chapter2.Hilbert

/-!
# Chapter 3 § 6, Prop. 3 — joining two convex bodies cut by hemispheres (« raccorder », « accoler »)

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 3 § 6, journal pp. 282–283; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch3.tex` (TO BE CHECKED BY THE AUTHOR; checked here
against the scan, PDF p. 56). Target T-bz-c3-raccordement.

* `bzprop:c3s6p3_raccordement` — `benzecri1960_ch3.tex:1527` (l.1527–1548, proof l.1550–1568),
  NOT marked (partial): the statement is proved for `n ≥ 1` (`Benzecri.prop3_raccordement`), in
  the stronger « accolant » form (`Benzecri.prop3_accole`: `g₁` the identity), and it FAILS in
  `S(0)` (`Benzecri.raccordement_dimZero`, « imprecise »: the hypotheses hold there, the
  conclusion does not). The two named notions of the statement (OQ-160 (c), no row of their own)
  are `Benzecri.Raccorde` and `Benzecri.Accole` (witnesses kept by `Benzecri.RaccordeVia`).
  Instance: `RaccordementInstance.simplexS_hypotheses` (the simplex of `S(m+1)`, `H = {x₀ ≥ 0}`:
  every hypothesis of Prop. 3 holds), hence `RaccordementInstance.accole_simplexS`,
  `RaccordementInstance.raccorde_simplexS`.

> **Proposition 3.** Soit $W_1$ (resp. $W_2$) un corps convexe de $S(n)$; $H_1$ (resp. $H_2$) un
> hémisphère fermé tel que $W_1\subset H_1$ (resp. $W_2\subset H_2$) et que le saturé $V_1$ (resp.
> $V_2$) de $W_1$ (resp. $W_2$) au-delà de $\mathring{H}_1$ (resp. $\mathring{H}_2$) soit distinct
> de $W_1$ (resp. $W_2$). On peut trouver un corps convexe $W'$ et deux hémisphères fermés
> $H'_1$, $H'_2$ tels que :
>
> 1° $H'_1\cap W'=W'_1$; $H'_2\cap W'=W'_2$, $W'_1\cap W'_2=\emptyset$, $W'$ étant l'enveloppe
> convexe de $W'_1$ et de $W'_2$.
>
> 2° Il existe deux transformations projectives $g_1$, $g_2$ de l'espace telles que
> $g_1H_1=H'_1$; $g_1W_1=W'_1$; $g_2H_2=H'_2$; $g_2W_2=W'_2$.
>
> Nous dirons que $W'$ est obtenu en *raccordant* $W_1$ et $W_2$ suivant les intersections de ces
> corps avec les hyperplans $h_1$, $h_2$ frontières de $H_1$, $H_2$; si $g_1$ est l'identité, nous
> dirons que $W'$ est obtenu en *accolant* $W_2$ à $W_1$ suivant $h_1\cap W_1$, $h_2\cap W_2$.

## The proof formalized

Not the printed construction (parallel hyperplanes `h′₁`, `h′₂` of an affine chart), but the same
idea in cones, with `g₁ = 1`. For each piece (`pair_data`): `V ≠ W` gives `B ∈ F(V)` with
`l B < 0` (the trace `V ∩ H = W ∩ H`, Déf. 1); for `n ≥ 1` it gives a point `f` of `W ∩ h`
(an open set of `ℝⁿ⁺¹` is not in the line `ℝB`, `exists_mem_notMem_span`), used to make `ν B > 0`
for a form `ν > 0` on `F(W)`; the open cone `U` (the image of `F(W̊) ∩ {l > 0}` under the
involution `y ↦ y + 2 l(y)/(−l B) B`) consists of points `x + c B`, `x ∈ F(W)`, `c > 0`, so that
`a + y ∈ F(V)` for `a ∈ F(W) ∪ {O}`, `y ∈ U`, and `a + y ∈ F(W) ∪ {O}` as soon as `l(a + y) ≥ 0`.
The automorphism (`exists_squeeze`): in coordinates adapted to the two pieces
(`exists_linearEquiv_normal`, from `Basis.mkFinCons`), `Φ_s (x₀, x₁, x′) = (s²x₁, x₀, s x′)`
satisfies `Φ_s ∘ Φ_s = s²`, and as `s → 0` it sends the compact base of `F(W₂)` into `U₁` and that
of `F(W₁)` into `U₂` (the tube lemma). The assembly (`accole_of_squeeze`): `W′ = conv(W₁ ∪ γW₂)`
has cone `F(W₁) ∪ {O} + γ(F(W₂) ∪ {O})` (`enveloppeConvexe_union_eq`); `H₁ ∩ W′ = W₁` and
`γH₂ ∩ W′ = γW₂` by the property of `U₁`, `U₂`; `W₁ ∩ γW₂ = ∅` as `l₁ < 0` on `U₁`; `W′` is a
convex body (`ν₁ > 0` on its cone; compact as the rays of the convex join of two compact bases).
This proves the printed proof's « Il est clair que les transformations $g_1$, $g_2$ utilisées
permettront de raccorder $W_1$ et $W_2$ », which the paper does not argue.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| « $W_i$ un corps convexe de $S(n)$ » | ✓ carried: `IsCorpsConvexeS n Wᵢ` |
| « $H_i$ un hémisphère fermé tel que $W_i\subset H_i$ » | ✓ carried: `Wᵢ ⊆ closedHemisphere lᵢ`, `lᵢ ≠ 0` (a closed hemisphere of Ch. 1 Déf. 5 is one, `IsClosedHemisphere.exists_eq`, DEC-114) |
| « le saturé $V_i$ … soit distinct de $W_i$ » | ✓ carried: `sature lᵢ Wᵢ ≠ Wᵢ` (`Benzecri.sature`, Prop. 1, whose hypotheses a convex body in `Hᵢ` meets) |
| (not printed) `n ≥ 1` | ⚠ strengthened: n ≥ 1 added in `prop3_accole` / `prop3_raccordement`: for `n = 0` the statement is false (`raccordement_dimZero`) |
| conclusion: « $H'_i$ hémisphères fermés » | ✓ `closedHemisphere l'ᵢ`, `l'ᵢ ≠ 0` |
| conclusion: « transformations projectives » | ✓ `g₁ g₂ : GSR n` (`GS(n, ℝ)`), acting on parts by `•` |
| conclusion: « $W'$ l'enveloppe convexe de $W'_1$ et de $W'_2$ » | ✓ `W' = enveloppeConvexe (g₁ • W₁ ∪ g₂ • W₂)` |
| conclusion 1° and 2° | ✓ all carried in `RaccordeVia`, with `W'ᵢ = gᵢ • Wᵢ`; `prop3_accole` gives `g₁ = 1` (Lean ≥ paper) |

## SCOPE (disclosed)

* **Not marked**: the printed statement fails for `n = 0` (`raccordement_dimZero`): in `S(0)`,
  `W = H = {e}` is a convex body, its saturated convex is all of `S(0)` (a convex part, not
  strict, under DEC-120), but a convex body of `S(0)` is one point and cannot contain two
  disjoint nonempty parts. The planner's evidence (« n = 0 makes the hypothesis V₁ ≠ W₁
  unsatisfiable ») is wrong. Prop. 4 two lines below prints « $(n\geqq 1)$ », Prop. 3 does not.
* « raccordant » / « accolant » are read as relations between `(W₁, H₁)`, `(W₂, H₂)` and `W'`,
  the hemispheres `H'ᵢ` and transformations `gᵢ` existentially quantified (`Raccorde`,
  `Accole`); `RaccordeVia` keeps them. They do not include the hypotheses `Vᵢ ≠ Wᵢ`.
* The planner's instance (two discs cut by chords) is replaced by the simplex of `S(m+1)` cut by a
  facet hyperplane (the triangle of `S(2)` for `m = 1`), two copies of it joined.
* General lemmas proved here (`F_smul_linearEquiv`, `smul_closedHemisphere_linearEquiv`,
  `isLeast_ofCone_add`, `enveloppeConvexe_union_eq`, `isCompact_ofCone`,
  `exists_linearEquiv_normal`) could move upstream at graduation.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Filter Topology
open scoped Pointwise

namespace Benzecri

open Sphere

/-! ### General lemmas on `S(E)` and `S(n)` -/


section General
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem inv_smul_mk_linearEquiv (γ : E ≃ₗ[ℝ] E) (v : E) (hv : v ≠ 0) :
    (QuotientGroup.mk γ : GSE E)⁻¹ • mk v hv = mk (γ.symm v) (by simpa using hv) := by
  rw [← QuotientGroup.mk_inv, GSE.mk_smul, smul_mk]
  rfl

theorem F_smul_linearEquiv (γ : E ≃ₗ[ℝ] E) (A : Set (Sphere E)) :
    F ((QuotientGroup.mk γ : GSE E) • A) = γ '' F A := by
  ext v
  rw [γ.image_eq_preimage_symm]
  constructor
  · rintro ⟨hv, hA⟩
    rw [mem_smul_set_iff_inv_smul_mem, inv_smul_mk_linearEquiv] at hA
    exact ⟨_, hA⟩
  · rintro ⟨hv, hA⟩
    have hv0 : v ≠ 0 := fun h => hv (by simp [h])
    refine ⟨hv0, ?_⟩
    rw [mem_smul_set_iff_inv_smul_mem, inv_smul_mk_linearEquiv]
    exact hA

theorem kPrime_smul_linearEquiv (γ : E ≃ₗ[ℝ] E) (A : Set (Sphere E)) :
    kPrime ((QuotientGroup.mk γ : GSE E) • A) = γ '' kPrime A := by
  rw [kPrime, kPrime, F_smul_linearEquiv, image_insert_eq, map_zero]

theorem smul_closedHemisphere_linearEquiv (γ : E ≃ₗ[ℝ] E) (l : Module.Dual ℝ E) :
    (QuotientGroup.mk γ : GSE E) • closedHemisphere l =
      closedHemisphere (l ∘ₗ γ.symm.toLinearMap) := by
  ext x
  obtain ⟨X, hX, rfl⟩ := exists_isRep x
  rw [mem_smul_set_iff_inv_smul_mem, inv_smul_mk_linearEquiv, mk_mem_closedHemisphere,
    mk_mem_closedHemisphere]
  rfl

theorem one_smul_set (A : Set (Sphere E)) : (1 : GSE E) • A = A := one_smul _ A

theorem isConvexPart_smul_linearEquiv (γ : E ≃ₗ[ℝ] E) {A : Set (Sphere E)}
    (hA : IsConvexPart A) : IsConvexPart ((QuotientGroup.mk γ : GSE E) • A) := by
  unfold IsConvexPart at *
  rw [F_smul_linearEquiv, ← map_zero γ, ← image_insert_eq]
  exact hA.linear_image γ.toLinearMap

theorem openHemisphere_zero : openHemisphere (0 : Module.Dual ℝ E) = ∅ := by
  ext x
  obtain ⟨X, hX, rfl⟩ := exists_isRep x
  simp [mk_mem_openHemisphere]

/-- The rays of `F(A) ∪ {O} + F(B) ∪ {O}` form the least convex part containing `A ∪ B`. -/
theorem isLeast_ofCone_add {A B : Set (Sphere E)} (hA : IsConvexPart A) (hB : IsConvexPart B) :
    IsLeast {k | IsConvexPart k ∧ A ∪ B ⊆ k} (ofCone (kPrime A + kPrime B)) := by
  have h₁ : Prolonge 0 A A := prolonge_self hA
  have h₂ : Prolonge 0 A B := ⟨hB, by rw [openHemisphere_zero, inter_empty, inter_empty]⟩
  obtain ⟨h3, hs1, hs2⟩ := prolonge_join h₁ h₂
  refine ⟨⟨h3.1, union_subset hs1 hs2⟩, fun k ⟨hk, hABk⟩ => ?_⟩
  intro x hx
  obtain ⟨z, hz0, hz, rfl⟩ := mem_ofCone.1 hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.1 hz
  have ha' : a ∈ hk.cone := by
    rcases mem_insert_iff.1 ha with rfl | ⟨ha0, haA⟩
    · exact mem_insert _ _
    · exact mem_insert_of_mem _ ⟨ha0, hABk (Or.inl haA)⟩
  have hb' : b ∈ hk.cone := by
    rcases mem_insert_iff.1 hb with rfl | ⟨hb0, hbB⟩
    · exact mem_insert _ _
    · exact mem_insert_of_mem _ ⟨hb0, hABk (Or.inr hbB)⟩
  obtain ⟨_, h⟩ := (mem_insert_iff.1 (hk.cone.add_mem ha' hb')).resolve_left hz0
  exact h

/-- `ofCone C` is compact for a compact `C` avoiding `O`. -/
theorem isCompact_ofCone [TopologicalSpace E] {C : Set E} (hC : IsCompact C) (h0 : (0 : E) ∉ C) :
    IsCompact (ofCone C) := by
  have : IsCompact (Subtype.val ⁻¹' C : Set {v : E // v ≠ 0}) := by
    rw [Subtype.isCompact_iff]
    convert hC using 1
    ext v
    simp only [mem_image, mem_preimage, Subtype.exists, exists_and_right, exists_eq_right]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨fun h' => h0 (h' ▸ h), h⟩⟩
  exact this.image continuous_s

end General

section Sn
variable {n : ℕ}
local notation "Eₙ" => (Fin (n + 1) → ℝ)

theorem enveloppeConvexe_union_eq {A B : Set (S n)} (hA : IsConvexPart A) (hB : IsConvexPart B) :
    enveloppeConvexe (A ∪ B) = ofCone (kPrime A + kPrime B) :=
  ((isLeast_iff_eq_enveloppeConvexe _).1 (isLeast_ofCone_add hA hB)).symm

/-- In `ℝⁿ⁺¹`, `n ≥ 1`, a nonempty open set is not contained in a line. -/
theorem exists_mem_notMem_span (hn : 1 ≤ n) {O : Set Eₙ} (hO : IsOpen O) (hne : O.Nonempty)
    (B : Eₙ) : ∃ Y ∈ O, Y ∉ Submodule.span ℝ {B} := by
  by_contra h
  push Not at h
  have htop : Submodule.span ℝ {B} = ⊤ := by
    apply Submodule.eq_top_of_nonempty_interior'
    obtain ⟨y, hy⟩ := hne
    exact ⟨y, interior_mono h (hO.interior_eq.symm ▸ hy)⟩
  have h1 := finrank_span_le_card (R := ℝ) ({B} : Set Eₙ)
  rw [htop, finrank_top, Module.finrank_fin_fun] at h1
  simp at h1
  omega

/-- The trace of the saturated convex on `H`: `F(V) ∪ {O}` meets `{l ≥ 0}` inside `F(W) ∪ {O}`. -/
theorem kPrime_sature_trace {l : Module.Dual ℝ Eₙ} {W : Set (S n)} (hW : IsConvexPart W)
    (hWc : IsClosed W) (hne : (W ∩ openHemisphere l).Nonempty) {z : Eₙ}
    (hz : z ∈ kPrime (sature l W)) (hlz : 0 ≤ l z) : z ∈ kPrime W := by
  have hg := isGreatest_sature (l := l) hW
  have hVc := isClosed_sature l.continuous_of_finiteDimensional hW hWc
  have htr := inter_closedHemisphere_eq_of_prolonge hW hg.1 (by rwa [inter_comm]) hWc hVc
  rcases mem_insert_iff.1 hz with rfl | ⟨hz0, hzV⟩
  · exact mem_insert _ _
  · have : mk z hz0 ∈ sature l W ∩ closedHemisphere l :=
      ⟨hzV, (mk_mem_closedHemisphere hz0).2 hlz⟩
    rw [← htr] at this
    exact mem_insert_of_mem _ ⟨hz0, this.1⟩

/-- **The data of one piece** `(W, H)` with `V ≠ W`: a form `ν > 0` on `F(W)`, and an open cone
`U` (around the rays `s B + w`, `B` a point of `F(V)` beyond `h`) such that adding a point of `U`
to the cone of `W` stays in it as long as `l ≥ 0`; `U` contains a point `p` on which some
other form `ν' > 0` on `F(W)` vanishes. -/
theorem pair_data (hn : 1 ≤ n) {l : Module.Dual ℝ Eₙ} (hl : l ≠ 0) {W : Set (S n)}
    (hW : IsCorpsConvexeS n W) (hWH : W ⊆ closedHemisphere l) (hV : sature l W ≠ W) :
    ∃ (ν : Module.Dual ℝ Eₙ) (U : Set Eₙ), (∀ v ∈ F W, 0 < ν v) ∧ IsOpen U ∧ IsPosCone U ∧
      (∀ y ∈ U, 0 < ν y ∧ l y < 0 ∧ ∀ a ∈ kPrime W, 0 ≤ l (a + y) → a + y ∈ kPrime W) ∧
      ∃ p ∈ U, ∃ ν' : Module.Dual ℝ Eₙ, (∀ v ∈ F W, 0 < ν' v) ∧ ν' p = 0 := by
  obtain ⟨hstrict, hcomp, hint⟩ := hW
  have hWconv : IsConvexPart W := hstrict.1
  have hWc : IsClosed W := hcomp.isClosed
  have hne := inter_openHemisphere_nonempty hl hWH hint
  have hg := isGreatest_sature (l := l) hWconv
  set V := sature l W with hVdef
  have hWV : W ⊆ V := hg.2 (prolonge_self hWconv)
  have hVconv : IsConvexPart V := hg.1.1
  have htr : ∀ z ∈ kPrime V, 0 ≤ l z → z ∈ kPrime W := fun z hz hlz =>
    kPrime_sature_trace hWconv hWc hne hz hlz
  have hKV : ∀ z ∈ kPrime W, z ∈ kPrime V := fun z hz => by
    rcases mem_insert_iff.1 hz with rfl | ⟨hz0, hzW⟩
    · exact mem_insert _ _
    · exact mem_insert_of_mem _ ⟨hz0, hWV hzW⟩
  have hlW : ∀ v ∈ F W, 0 ≤ l v := fun v ⟨hv0, hvW⟩ => (mk_mem_closedHemisphere hv0).1 (hWH hvW)
  have hlc : Continuous l := l.continuous_of_finiteDimensional
  -- a point `B₀` of `V` beyond `h`
  obtain ⟨x, hxV, hxW⟩ : ∃ x ∈ V, x ∉ W := by
    by_contra h
    push Not at h
    exact hV (Subset.antisymm h hWV)
  obtain ⟨B₀, hB₀, rfl⟩ := exists_isRep x
  have hlB₀ : l B₀ < 0 := by
    by_contra h
    push Not at h
    rcases mem_insert_iff.1 (htr B₀ (mem_insert_of_mem _ ⟨hB₀, hxV⟩) h) with h0 | ⟨_, hW'⟩
    · exact hB₀ h0
    · exact hxW hW'
  -- the open cone `O` of the interior of `W`, in `H̊`
  set O : Set Eₙ := F (interior W) ∩ {v | 0 < l v} with hOdef
  have hOo : IsOpen O :=
    (isOpen_iff_F.1 isOpen_interior).inter (isOpen_lt continuous_const hlc)
  have hOne : O.Nonempty := by
    obtain ⟨y, hyi, hyH⟩ := inter_openHemisphere_nonempty hl (interior_subset.trans hWH)
      (by rw [interior_interior]; exact hint)
    obtain ⟨Y, hY, rfl⟩ := exists_isRep y
    exact ⟨Y, ⟨hY, hyi⟩, (mk_mem_openHemisphere hY).1 hyH⟩
  have hOW : ∀ v ∈ O, v ∈ F W := fun v hv => F_mono interior_subset hv.1
  -- a point `f` of `W ∩ h`
  obtain ⟨f, hfW, hlf⟩ : ∃ f ∈ F W, l f = 0 := by
    obtain ⟨Y, hYO, hYs⟩ := exists_mem_notMem_span hn hOo hOne B₀
    have hlY : 0 < l Y := hYO.2
    have hZV : l Y • B₀ + (-l B₀) • Y ∈ kPrime V :=
      hVconv.cone.add_mem (hVconv.cone.smul_mem hlY (mem_insert_of_mem _ ⟨hB₀, hxV⟩))
        (hVconv.cone.smul_mem (neg_pos.2 hlB₀) (hKV _ (mem_insert_of_mem _ (hOW Y hYO))))
    have hlZ : l (l Y • B₀ + (-l B₀) • Y) = 0 := by
      simp only [map_add, map_smul, smul_eq_mul]; ring
    have hZ0 : l Y • B₀ + (-l B₀) • Y ≠ 0 := by
      intro h
      apply hYs
      have hY : Y = (l Y / l B₀) • B₀ := by
        have h' : (l B₀) • Y = l Y • B₀ := by
          rw [neg_smul, ← sub_eq_add_neg, sub_eq_zero] at h; exact h.symm
        rw [div_eq_inv_mul, mul_smul, ← h', smul_smul, inv_mul_cancel₀ hlB₀.ne, one_smul]
      rw [hY]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self B₀)
    rcases mem_insert_iff.1 (htr _ hZV hlZ.ge) with h | h
    · exact absurd h hZ0
    · exact ⟨_, h, hlZ⟩
  -- the form `ν`
  obtain ⟨ℓ, hℓ⟩ := IsCorpsConvexeS.exists_forall_pos ⟨hstrict, hcomp, hint⟩
  set ν : Module.Dual ℝ Eₙ := (ℓ : Eₙ →ₗ[ℝ] ℝ) with hνdef
  have hν : ∀ v ∈ F W, 0 < ν v := hℓ
  have hνc : Continuous ν := ν.continuous_of_finiteDimensional
  have hνf := hν f hfW
  -- the point `B = B₀ + M f` of `V`, with `ν B > 0`
  set M : ℝ := (|ν B₀| + 1) / ν f with hMdef
  have hM : 0 < M := div_pos (by positivity) hνf
  set B := B₀ + M • f with hBdef
  have hlB : l B = l B₀ := by simp [B, hlf]
  have hνB : 0 < ν B := by
    have : ν B = ν B₀ + (|ν B₀| + 1) := by
      simp only [B, map_add, map_smul, smul_eq_mul, M]
      field_simp
    rw [this]; linarith [neg_abs_le (ν B₀)]
  have hBV : B ∈ kPrime V :=
    hVconv.cone.add_mem (mem_insert_of_mem _ ⟨hB₀, hxV⟩)
      (hVconv.cone.smul_mem hM (hKV _ (mem_insert_of_mem _ hfW)))
  have hlBn : l B < 0 := hlB ▸ hlB₀
  have hlB0 : l B ≠ 0 := hlBn.ne
  -- the open cone `U`: the image of `O` under the linear involution `y ↦ y + t(y) B`
  set t : Eₙ → ℝ := fun y => 2 * l y / (-l B) with htdef
  have hlx : ∀ y, l (y + t y • B) = -l y := fun y => by
    simp only [t, map_add, map_smul, smul_eq_mul]
    field_simp
    ring
  set U : Set Eₙ := {y | 0 < ν y ∧ y + t y • B ∈ O} with hUdef
  have hOpos : IsPosCone O := fun c hc v ⟨hvF, hvl⟩ =>
    ⟨smul_mem_F hvF hc, by simp only [mem_setOf_eq, map_smul, smul_eq_mul]; exact mul_pos hc hvl⟩
  refine ⟨ν, U, hν, ?_, ?_, ?_, ?_⟩
  · refine (isOpen_lt continuous_const hνc).inter (hOo.preimage ?_)
    exact continuous_id.add (((continuous_const.mul hlc).div_const _).smul continuous_const)
  · rintro c hc y ⟨hνy, hyO⟩
    refine ⟨by simp only [map_smul, smul_eq_mul]; exact mul_pos hc hνy, ?_⟩
    have : c • y + t (c • y) • B = c • (y + t y • B) := by
      simp only [t, map_smul, smul_eq_mul, smul_add, smul_smul]
      congr 2
      ring
    rw [this]
    exact hOpos c hc _ hyO
  · rintro y ⟨hνy, hyO⟩
    have hly : l y < 0 := by
      have := hyO.2
      simp only [mem_setOf_eq, hlx] at this
      linarith
    refine ⟨hνy, hly, fun a ha hla => ?_⟩
    have hct : 0 < -t y := by
      simp only [t]
      rw [← neg_div, neg_div_neg_eq]
      exact div_pos_of_neg_of_neg (by linarith) hlBn
    have hdec : a + y = (a + (y + t y • B)) + (-t y) • B := by
      rw [neg_smul]; abel
    rw [hdec] at hla ⊢
    refine htr _ (hVconv.cone.add_mem (hKV _ (hWconv.cone.add_mem ha
      (mem_insert_of_mem _ (hOW _ hyO)))) (hVconv.cone.smul_mem hct hBV)) hla
  · obtain ⟨x₀, hx₀⟩ := hOne
    have hlx₀ : 0 < l x₀ := hx₀.2
    have hc₀ : 0 < 2 * l x₀ / (-l B) := div_pos (by linarith) (by linarith)
    set p := x₀ + (2 * l x₀ / (-l B)) • B with hpdef
    have hlp : l p = -l x₀ := by
      simp only [p, map_add, map_smul, smul_eq_mul]
      field_simp
      ring
    have hνp : 0 < ν p := by
      simp only [p, map_add, map_smul, smul_eq_mul]
      have := hν x₀ (hOW x₀ hx₀)
      positivity
    have hpU : p ∈ U := by
      refine ⟨hνp, ?_⟩
      have : p + t p • B = x₀ := by
        simp only [t, hlp, p, add_assoc, ← add_smul]
        have : 2 * l x₀ / -l B + 2 * -l x₀ / -l B = 0 := by ring
        rw [this, zero_smul, add_zero]
      rw [this]; exact hx₀
    refine ⟨p, hpU, ν + (ν p / (-l p)) • l, fun v hv => ?_, ?_⟩
    · have h1 := hν v hv
      have h2 := hlW v hv
      have h3 : 0 ≤ ν p / -l p := div_nonneg hνp.le (by linarith)
      simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      positivity
    · simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      have : l p ≠ 0 := by linarith
      rw [div_mul_eq_mul_div, div_neg, mul_div_assoc, div_self this]
      ring

end Sn

/-! ### The squeezing automorphism -/

section Squeeze

variable {m : ℕ}

/-- The hyperbolic map `Φ_s : (x₀, x₁, x') ↦ (s² x₁, x₀, s x')` of `ℝᵐ⁺²`; `Φ_s ∘ Φ_s = s²`. -/
def phiMap (s : ℝ) : (Fin (m + 2) → ℝ) →ₗ[ℝ] (Fin (m + 2) → ℝ) where
  toFun x i := if i = 0 then s ^ 2 * x 1 else if i = 1 then x 0 else s * x i
  map_add' x y := by
    ext i
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' c x := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

theorem phiMap_apply (s : ℝ) (x : Fin (m + 2) → ℝ) (i : Fin (m + 2)) :
    phiMap s x i = if i = 0 then s ^ 2 * x 1 else if i = 1 then x 0 else s * x i := rfl

theorem phiMap_phiMap (s : ℝ) (x : Fin (m + 2) → ℝ) : phiMap s (phiMap s x) = s ^ 2 • x := by
  ext i
  have h10 : (1 : Fin (m + 2)) ≠ 0 := Fin.zero_lt_one.ne'
  simp only [phiMap_apply, Pi.smul_apply, smul_eq_mul, if_neg h10]
  by_cases h0 : i = 0
  · subst h0; simp
  · by_cases h1 : i = 1
    · subst h1; simp [h10]
    · simp only [if_neg h0, if_neg h1]; ring

theorem phiMap_zero (x : Fin (m + 2) → ℝ) : phiMap 0 x = x 0 • Pi.single 1 1 := by
  ext i
  have h10 : (1 : Fin (m + 2)) ≠ 0 := Fin.zero_lt_one.ne'
  simp only [phiMap_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  by_cases h0 : i = 0
  · subst h0; simp [h10.symm]
  · by_cases h1 : i = 1
    · subst h1; simp [h10]
    · simp [h0, h1]

theorem continuous_phiMap :
    Continuous fun q : ℝ × (Fin (m + 2) → ℝ) => phiMap q.1 q.2 := by
  refine continuous_pi fun i => ?_
  simp only [phiMap_apply]
  split_ifs
  · exact ((continuous_fst.pow 2).mul ((continuous_apply 1).comp continuous_snd))
  · exact (continuous_apply 0).comp continuous_snd
  · exact continuous_fst.mul ((continuous_apply i).comp continuous_snd)

/-- `Φ_s` as an automorphism, `s ≠ 0`. -/
def phiEquiv (s : ℝ) (hs : s ≠ 0) : (Fin (m + 2) → ℝ) ≃ₗ[ℝ] (Fin (m + 2) → ℝ) :=
  LinearEquiv.ofLinear (phiMap s) ((s ^ 2)⁻¹ • phiMap s)
    (LinearMap.ext fun x => by
      rw [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, phiMap_phiMap, smul_smul,
        inv_mul_cancel₀ (pow_ne_zero 2 hs), one_smul, LinearMap.id_apply])
    (LinearMap.ext fun x => by
      rw [LinearMap.comp_apply, LinearMap.smul_apply, phiMap_phiMap, smul_smul,
        inv_mul_cancel₀ (pow_ne_zero 2 hs), one_smul, LinearMap.id_apply])

theorem phiEquiv_apply (s : ℝ) (hs : s ≠ 0) (x : Fin (m + 2) → ℝ) :
    phiEquiv s hs x = phiMap s x := rfl

theorem phiEquiv_symm_apply (s : ℝ) (hs : s ≠ 0) (x : Fin (m + 2) → ℝ) :
    (phiEquiv s hs).symm x = (s ^ 2)⁻¹ • phiMap s x := rfl

theorem exists_linearEquiv_normal {m : ℕ} (ν : Module.Dual ℝ (Fin (m + 2) → ℝ))
    {u p : Fin (m + 2) → ℝ} (hu : ν u = 1) (hp : ν p = 0) (hp0 : p ≠ 0) :
    ∃ h : (Fin (m + 2) → ℝ) ≃ₗ[ℝ] (Fin (m + 2) → ℝ), (∀ x, h x 0 = ν x) ∧
      h p = Pi.single 1 1 := by
  obtain ⟨j, hj⟩ : ∃ j, p j ≠ 0 := by
    by_contra h
    push Not at h
    exact hp0 (funext h)
  set ω : Module.Dual ℝ (Fin (m + 2) → ℝ) := (p j)⁻¹ • LinearMap.proj j with hωdef
  have hω : ω p = 1 := by simp [ω, hj]
  set N : Submodule ℝ (Fin (m + 2) → ℝ) := LinearMap.ker ν ⊓ LinearMap.ker ω with hNdef
  have hpK : p ∈ LinearMap.ker ν := hp
  have hli : ∀ (c : ℝ), ∀ x ∈ N, c • p + x = 0 → c = 0 := by
    intro c x hx h
    have := congrArg ω h
    rw [map_add, map_smul, hω, (LinearMap.mem_ker.1 hx.2), map_zero] at this
    simpa using this
  have hsp : ∀ z ∈ LinearMap.ker ν, ∃ c : ℝ, z + c • p ∈ N := by
    intro z hz
    refine ⟨-ω z, ?_, ?_⟩
    · simp [LinearMap.mem_ker.1 hz, hp]
    · simp [hω]
  have hli' : ∀ (c : ℝ), ∀ x ∈ LinearMap.ker ν, c • u + x = 0 → c = 0 := by
    intro c x hx h
    have := congrArg ν h
    rw [map_add, map_smul, hu, LinearMap.mem_ker.1 hx, map_zero] at this
    simpa using this
  have hsp' : ∀ z, ∃ c : ℝ, z + c • u ∈ LinearMap.ker ν := by
    intro z
    refine ⟨-ν z, ?_⟩
    simp [hu]
  have hN : Module.finrank ℝ N = m := by
    have b0 := Module.Basis.mkFinCons u (Module.Basis.mkFinConsOfLE p hpK (Module.finBasis ℝ N) inf_le_left
      hli hsp) hli' hsp'
    have := Module.finrank_eq_card_basis b0
    rw [Module.finrank_fin_fun, Fintype.card_fin] at this
    omega
  let bK := Module.Basis.mkFinConsOfLE p hpK (Module.finBasisOfFinrankEq ℝ N hN) inf_le_left hli hsp
  let b : Module.Basis (Fin (m + 2)) ℝ (Fin (m + 2) → ℝ) := Module.Basis.mkFinCons u bK hli' hsp'
  have hb0 : b 0 = u := by simp [b]
  have hb1 : b 1 = p := by
    have : (1 : Fin (m + 2)) = Fin.succ 0 := rfl
    rw [this]
    simp [b, bK]
  have hbs : ∀ k : Fin (m + 1), ν (b k.succ) = 0 := by
    intro k
    simp only [b, Module.Basis.coe_mkFinCons, Fin.cons_succ, Function.comp_apply]
    exact LinearMap.mem_ker.1 (bK k).2
  refine ⟨b.equivFun, fun x => ?_, ?_⟩
  · have : (LinearMap.proj (R := ℝ) (φ := fun _ : Fin (m + 2) => ℝ) 0) ∘ₗ
        b.equivFun.toLinearMap = ν := by
      refine b.ext fun i => ?_
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        Module.Basis.equivFun_self, LinearMap.coe_proj, Function.eval]
      refine Fin.cases ?_ (fun k => ?_) i
      · simp [hb0, hu]
      · rw [hbs k, if_neg (Fin.succ_ne_zero k)]
    exact LinearMap.congr_fun this x
  · rw [← hb1]
    ext i
    rw [Module.Basis.equivFun_self, Pi.single_apply]
    exact if_congr eq_comm rfl rfl

/-- **The squeezing step**: for two compact parts `W₁`, `W₂` of `S(m+1)` and two open cones
`Uᵢ` containing points `pᵢ` on which forms `νᵢ > 0` on `F(Wᵢ)` vanish, some automorphism `γ`
sends `F(W₂)` into `U₁` while `γ⁻¹` sends `F(W₁)` into `U₂`. -/
theorem exists_squeeze {W₁ W₂ : Set (S (m + 1))} (hW₁c : IsCompact W₁) (hW₂c : IsCompact W₂)
    (hne₁ : W₁.Nonempty) (hne₂ : W₂.Nonempty) {U₁ U₂ : Set (Fin (m + 2) → ℝ)}
    (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) (hU₁c : IsPosCone U₁) (hU₂c : IsPosCone U₂)
    {p₁ p₂ : Fin (m + 2) → ℝ} (hp₁ : p₁ ∈ U₁) (hp₂ : p₂ ∈ U₂) (hp₁0 : p₁ ≠ 0) (hp₂0 : p₂ ≠ 0)
    {ν₁ ν₂ : Module.Dual ℝ (Fin (m + 2) → ℝ)} (hν₁ : ∀ v ∈ F W₁, 0 < ν₁ v)
    (hν₂ : ∀ v ∈ F W₂, 0 < ν₂ v) (h₁ : ν₁ p₁ = 0) (h₂ : ν₂ p₂ = 0) :
    ∃ γ : (Fin (m + 2) → ℝ) ≃ₗ[ℝ] (Fin (m + 2) → ℝ),
      (∀ x ∈ F W₂, γ x ∈ U₁) ∧ (∀ y ∈ F W₁, γ.symm y ∈ U₂) := by
  have hu : ∀ {W : Set (S (m + 1))} {ν : Module.Dual ℝ (Fin (m + 2) → ℝ)}, W.Nonempty →
      (∀ v ∈ F W, 0 < ν v) → ∃ u, ν u = 1 := by
    intro W ν hne hν
    obtain ⟨w, hw⟩ := hne
    obtain ⟨v, hv0, rfl⟩ := exists_isRep w
    have := hν v ⟨hv0, hw⟩
    exact ⟨(ν v)⁻¹ • v, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ this.ne']⟩
  obtain ⟨u₁, hu₁⟩ := hu hne₁ hν₁
  obtain ⟨u₂, hu₂⟩ := hu hne₂ hν₂
  obtain ⟨k₁, hk₁0, hk₁p⟩ := exists_linearEquiv_normal ν₁ hu₁ h₁ hp₁0
  obtain ⟨k₂, hk₂0, hk₂p⟩ := exists_linearEquiv_normal ν₂ hu₂ h₂ hp₂0
  -- the two families
  set ψ₁ : ℝ × (Fin (m + 2) → ℝ) → (Fin (m + 2) → ℝ) := fun q => k₁.symm (phiMap q.1 (k₂ q.2))
  set ψ₂ : ℝ × (Fin (m + 2) → ℝ) → (Fin (m + 2) → ℝ) := fun q => k₂.symm (phiMap q.1 (k₁ q.2))
  have hcont : ∀ (a b : (Fin (m + 2) → ℝ) ≃ₗ[ℝ] (Fin (m + 2) → ℝ)),
      Continuous fun q : ℝ × (Fin (m + 2) → ℝ) => a.symm (phiMap q.1 (b q.2)) := by
    intro a b
    have ha : Continuous a.symm := a.symm.toLinearMap.continuous_of_finiteDimensional
    have hb : Continuous b := b.toLinearMap.continuous_of_finiteDimensional
    exact ha.comp (continuous_phiMap.comp (continuous_fst.prodMk (hb.comp continuous_snd)))
  have hψ₀ : ∀ (a b : (Fin (m + 2) → ℝ) ≃ₗ[ℝ] (Fin (m + 2) → ℝ)) (p : Fin (m + 2) → ℝ),
      a p = Pi.single 1 1 → ∀ x, a.symm (phiMap 0 (b x)) = b x 0 • p := by
    intro a b p hap x
    rw [phiMap_zero, map_smul, ← hap, LinearEquiv.symm_apply_apply]
  -- the compact bases
  set ℓ₁ := LinearMap.toContinuousLinearMap ν₁
  set ℓ₂ := LinearMap.toContinuousLinearMap ν₂
  have hB₁ := isCompact_coneSection hW₁c hne₁ (ℓ := ℓ₁) (by simpa [ℓ₁] using hν₁)
  have hB₂ := isCompact_coneSection hW₂c hne₂ (ℓ := ℓ₂) (by simpa [ℓ₂] using hν₂)
  have hc₁ : ((ℓ₁ : Module.Dual ℝ (Fin (m + 2) → ℝ))) = ν₁ := LinearMap.coe_toContinuousLinearMap ν₁
  have hc₂ : ((ℓ₂ : Module.Dual ℝ (Fin (m + 2) → ℝ))) = ν₂ := LinearMap.coe_toContinuousLinearMap ν₂
  rw [hc₁] at hB₁
  rw [hc₂] at hB₂
  have ev₁ : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ x ∈ coneSection W₂ ν₂, ψ₁ (s, x) ∈ U₁ := by
    refine hB₂.eventually_forall_of_forall_eventually fun x hx => ?_
    have hmem : ψ₁ (0, x) ∈ U₁ := by
      simp only [ψ₁]
      rw [hψ₀ k₁ k₂ p₁ hk₁p, hk₂0, hx.2, one_smul]
      exact hp₁
    exact ((hcont k₁ k₂).tendsto (0, x)).eventually (hU₁.mem_nhds hmem)
  have ev₂ : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ y ∈ coneSection W₁ ν₁, ψ₂ (s, y) ∈ U₂ := by
    refine hB₁.eventually_forall_of_forall_eventually fun y hy => ?_
    have hmem : ψ₂ (0, y) ∈ U₂ := by
      simp only [ψ₂]
      rw [hψ₀ k₂ k₁ p₂ hk₂p, hk₁0, hy.2, one_smul]
      exact hp₂
    exact ((hcont k₂ k₁).tendsto (0, y)).eventually (hU₂.mem_nhds hmem)
  obtain ⟨s, ⟨hs₁, hs₂⟩, hs⟩ :=
    (((ev₁.and ev₂).filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
  have hs0 : s ≠ 0 := (mem_Ioi.1 hs).ne'
  refine ⟨k₂.trans ((phiEquiv s hs0).trans k₁.symm), fun x hx => ?_, fun y hy => ?_⟩
  · have hx' := hν₂ x hx
    have hxs : (ν₂ x)⁻¹ • x ∈ coneSection W₂ ν₂ :=
      ⟨smul_mem_F hx (inv_pos.2 hx'), by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hx'.ne']⟩
    have := hU₁c _ hx' _ (hs₁ _ hxs)
    simp only [ψ₁, map_smul, smul_smul, mul_inv_cancel₀ hx'.ne', one_smul] at this
    exact this
  · have hy' := hν₁ y hy
    have hys : (ν₁ y)⁻¹ • y ∈ coneSection W₁ ν₁ :=
      ⟨smul_mem_F hy (inv_pos.2 hy'), by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hy'.ne']⟩
    have := hU₂c _ (mul_pos (inv_pos.2 (pow_pos (mem_Ioi.1 hs) 2)) hy') _ (hs₂ _ hys)
    simp only [ψ₂, map_smul, smul_smul, mul_assoc, mul_inv_cancel₀ hy'.ne', mul_one] at this
    simp only [LinearEquiv.symm_trans_apply, phiEquiv_symm_apply, map_smul]
    exact this


end Squeeze

/-! ### The definitions « raccordant », « accolant » -/

variable {n : ℕ}

local notation "Eₙ" => (Fin (n + 1) → ℝ)

/-- **« $W'$ est obtenu en raccordant $W_1$ et $W_2$ »**, with its witnesses: the transformations
`g₁ g₂ ∈ GS(n, ℝ)` and the equations `l₁' l₂'` of the hemispheres `H'ᵢ`. -/
def RaccordeVia (l₁ : Module.Dual ℝ Eₙ) (W₁ : Set (S n)) (l₂ : Module.Dual ℝ Eₙ)
    (W₂ : Set (S n)) (W' : Set (S n)) (g₁ g₂ : GSR n) (l₁' l₂' : Module.Dual ℝ Eₙ) : Prop :=
  IsCorpsConvexeS n W' ∧ l₁' ≠ 0 ∧ l₂' ≠ 0 ∧
    closedHemisphere l₁' ∩ W' = g₁ • W₁ ∧ closedHemisphere l₂' ∩ W' = g₂ • W₂ ∧
    (g₁ • W₁) ∩ (g₂ • W₂) = ∅ ∧ W' = enveloppeConvexe ((g₁ • W₁) ∪ (g₂ • W₂)) ∧
    g₁ • closedHemisphere l₁ = closedHemisphere l₁' ∧
    g₂ • closedHemisphere l₂ = closedHemisphere l₂'

/-- **« raccordant »**: `W'` is obtained by joining `W₁` and `W₂` along `h₁ ∩ W₁`, `h₂ ∩ W₂`. -/
def Raccorde (l₁ : Module.Dual ℝ Eₙ) (W₁ : Set (S n)) (l₂ : Module.Dual ℝ Eₙ)
    (W₂ : Set (S n)) (W' : Set (S n)) : Prop :=
  ∃ (g₁ g₂ : GSR n) (l₁' l₂' : Module.Dual ℝ Eₙ), RaccordeVia l₁ W₁ l₂ W₂ W' g₁ g₂ l₁' l₂'

/-- **« accolant »**: `W'` is obtained by joining with `g₁` the identity. -/
def Accole (l₁ : Module.Dual ℝ Eₙ) (W₁ : Set (S n)) (l₂ : Module.Dual ℝ Eₙ)
    (W₂ : Set (S n)) (W' : Set (S n)) : Prop :=
  ∃ (g₂ : GSR n) (l₁' l₂' : Module.Dual ℝ Eₙ), RaccordeVia l₁ W₁ l₂ W₂ W' 1 g₂ l₁' l₂'

theorem Accole.raccorde {l₁ l₂ : Module.Dual ℝ Eₙ} {W₁ W₂ W' : Set (S n)}
    (h : Accole l₁ W₁ l₂ W₂ W') : Raccorde l₁ W₁ l₂ W₂ W' := by
  obtain ⟨g₂, l₁', l₂', h⟩ := h
  exact ⟨1, g₂, l₁', l₂', h⟩

/-! ### Prop. 3 -/

/-- **The assembly**: an automorphism `γ` squeezing `F(W₂)` into `U₁` and `F(W₁)` into `U₂` (by
`γ⁻¹`) joins `W₁` and `γ W₂`: `W' = conv(W₁ ∪ γ W₂)` is cut by `H₁` along `W₁` and by `γ H₂`
along `γ W₂` (the step the printed proof calls « clair »). -/
theorem accole_of_squeeze {l₁ l₂ : Module.Dual ℝ Eₙ} (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0)
    {W₁ W₂ : Set (S n)} (hW₁ : IsCorpsConvexeS n W₁) (hW₂ : IsCorpsConvexeS n W₂)
    (hH₁ : W₁ ⊆ closedHemisphere l₁) (hH₂ : W₂ ⊆ closedHemisphere l₂)
    {ν₁ : Module.Dual ℝ Eₙ} {U₁ U₂ : Set Eₙ}
    (hν₁ : ∀ v ∈ F W₁, 0 < ν₁ v)
    (hU₁ : ∀ y ∈ U₁, 0 < ν₁ y ∧ l₁ y < 0 ∧ ∀ a ∈ kPrime W₁, 0 ≤ l₁ (a + y) → a + y ∈ kPrime W₁)
    (hU₂ : ∀ y ∈ U₂, l₂ y < 0 ∧ ∀ a ∈ kPrime W₂, 0 ≤ l₂ (a + y) → a + y ∈ kPrime W₂)
    (γ : Eₙ ≃ₗ[ℝ] Eₙ) (hγ₁ : ∀ x ∈ F W₂, γ x ∈ U₁) (hγ₂ : ∀ y ∈ F W₁, γ.symm y ∈ U₂) :
    Accole l₁ W₁ l₂ W₂ (enveloppeConvexe (W₁ ∪ (QuotientGroup.mk γ : GSR n) • W₂)) := by
  set g : GSR n := QuotientGroup.mk γ with hgdef
  set W₂' := g • W₂ with hW₂'def
  have hW₁conv : IsConvexPart W₁ := hW₁.1.1
  have hW₂conv : IsConvexPart W₂ := hW₂.1.1
  have hW₂'conv : IsConvexPart W₂' := isConvexPart_smul_linearEquiv γ hW₂conv
  have hF₂' : F W₂' = γ '' F W₂ := F_smul_linearEquiv γ W₂
  have hK₂' : kPrime W₂' = γ '' kPrime W₂ := kPrime_smul_linearEquiv γ W₂
  set W' := enveloppeConvexe (W₁ ∪ W₂') with hW'def
  set C := kPrime W₁ + kPrime W₂' with hCdef
  have hW'eq : W' = ofCone C := enveloppeConvexe_union_eq hW₁conv hW₂'conv
  have hCpos : IsPosCone C := by
    intro c hc z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.1 hz
    exact Set.mem_add.2 ⟨c • a, hW₁conv.cone.smul_mem hc ha, c • b,
      hW₂'conv.cone.smul_mem hc hb, (smul_add c a b).symm⟩
  have hmemW' : ∀ z (hz : z ≠ 0), mk z hz ∈ W' ↔ z ∈ C := fun z hz => by
    rw [hW'eq]; exact mk_mem_ofCone_iff hCpos hz
  have hlW₁ : ∀ v ∈ F W₁, 0 ≤ l₁ v := fun v ⟨hv0, hvW⟩ =>
    (mk_mem_closedHemisphere hv0).1 (hH₁ hvW)
  -- every nonzero point of the cone `C` has `ν₁ > 0`
  have hνC : ∀ z ∈ C, z ≠ 0 → 0 < ν₁ z := by
    intro z hz hz0
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.1 hz
    rw [hK₂'] at hb
    obtain ⟨w, hw, rfl⟩ := hb
    rw [map_add]
    rcases mem_insert_iff.1 ha with rfl | haF
    · rcases mem_insert_iff.1 hw with rfl | hwF
      · simp at hz0
      · rw [map_zero, zero_add]; exact (hU₁ _ (hγ₁ w hwF)).1
    · rcases mem_insert_iff.1 hw with rfl | hwF
      · rw [map_zero, map_zero, add_zero]; exact hν₁ a haF
      · exact add_pos (hν₁ a haF) (hU₁ _ (hγ₁ w hwF)).1
  refine ⟨g, l₁, l₂ ∘ₗ γ.symm.toLinearMap, ?_, hl₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `W'` is a convex body
    have hW'conv : IsConvexPart W' := (enveloppeConvexe_isLeast _).1
    refine ⟨⟨hW'conv, fun x hx hnx => ?_⟩, ?_, ?_⟩
    · obtain ⟨z, hz0, rfl⟩ := exists_isRep x
      rw [neg_mk] at hnx
      have h1 := hνC z ((hmemW' z hz0).1 hx) hz0
      have h2 := hνC (-z) ((hmemW' _ _).1 hnx) (neg_ne_zero.2 hz0)
      rw [map_neg] at h2
      linarith
    · set ℓ := LinearMap.toContinuousLinearMap ν₁ with hℓdef
      have hc : ((ℓ : Module.Dual ℝ Eₙ)) = ν₁ := LinearMap.coe_toContinuousLinearMap ν₁
      have hW₂'c : IsCompact W₂' := hW₂.2.1.smul g
      have hne₁ : W₁.Nonempty := hW₁.2.2.mono interior_subset
      have hne₂' : W₂'.Nonempty := (hW₂.2.2.mono interior_subset).smul_set
      have hν₂' : ∀ v ∈ F W₂', 0 < ν₁ v := by
        rw [hF₂']
        rintro _ ⟨w, hw, rfl⟩
        exact (hU₁ _ (hγ₁ w hw)).1
      have hB₁ := isCompact_coneSection hW₁.2.1 hne₁ (ℓ := ℓ) (by simpa [ℓ] using hν₁)
      have hB₂ := isCompact_coneSection hW₂'c hne₂' (ℓ := ℓ) (by simpa [ℓ] using hν₂')
      rw [hc] at hB₁ hB₂
      have hnorm : ∀ {k : Set (S n)}, (∀ v ∈ F k, 0 < ν₁ v) → ∀ v ∈ F k,
          (ν₁ v)⁻¹ • v ∈ coneSection k ν₁ := fun hk v hv =>
        ⟨smul_mem_F hv (inv_pos.2 (hk v hv)),
          by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ (hk v hv).ne']⟩
      have hBne₁ : (coneSection W₁ ν₁).Nonempty := by
        obtain ⟨w, hw⟩ := hne₁
        obtain ⟨v, hv0, rfl⟩ := exists_isRep w
        exact ⟨_, hnorm hν₁ v ⟨hv0, hw⟩⟩
      have hBne₂ : (coneSection W₂' ν₁).Nonempty := by
        obtain ⟨w, hw⟩ := hne₂'
        obtain ⟨v, hv0, rfl⟩ := exists_isRep w
        exact ⟨_, hnorm hν₂' v ⟨hv0, hw⟩⟩
      set D := convexJoin ℝ (coneSection W₁ ν₁) (coneSection W₂' ν₁) with hDdef
      have hD : IsCompact D := isCompact_convexJoin hB₁ hB₂
      have hνD : ∀ v ∈ D, ν₁ v = 1 := by
        intro v hv
        obtain ⟨a, ha, b, hb, s, t, hs, ht, hst, rfl⟩ := mem_convexJoin.1 hv
        rw [map_add, map_smul, map_smul, ha.2, hb.2, smul_eq_mul, smul_eq_mul, mul_one, mul_one,
          hst]
      have hD0 : (0 : Eₙ) ∉ D := fun h => by simpa using hνD 0 h
      have hDC : D ⊆ C := by
        intro v hv
        obtain ⟨a, ha, b, hb, s, t, hs, ht, hst, rfl⟩ := mem_convexJoin.1 hv
        have hs1 : s ≤ 1 := by linarith
        have ht1 : t ≤ 1 := by linarith
        refine Set.mem_add.2 ⟨s • a, ?_, t • b, ?_, rfl⟩
        · have := hW₁conv (mem_insert_of_mem _ ha.1) (mem_insert _ _) hs (sub_nonneg.2 hs1)
            (by ring)
          rwa [smul_zero, add_zero] at this
        · have := hW₂'conv (mem_insert_of_mem _ hb.1) (mem_insert _ _) ht (sub_nonneg.2 ht1)
            (by ring)
          rwa [smul_zero, add_zero] at this
      have hWD : W' = ofCone D := by
        ext x
        obtain ⟨z, hz0, rfl⟩ := exists_isRep x
        rw [hmemW' z hz0]
        constructor
        · intro hz
          have hpos := hνC z hz hz0
          have hzD : (ν₁ z)⁻¹ • z ∈ D := by
            obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.1 hz
            rcases mem_insert_iff.1 ha with rfl | haF
            · rcases mem_insert_iff.1 hb with rfl | hbF
              · simp at hz0
              · rw [zero_add]
                exact subset_convexJoin_right hBne₁ (hnorm hν₂' b hbF)
            · rcases mem_insert_iff.1 hb with rfl | hbF
              · rw [add_zero]
                exact subset_convexJoin_left hBne₂ (hnorm hν₁ a haF)
              · have hνa := hν₁ a haF
                have hνb := hν₂' b hbF
                refine mem_convexJoin.2 ⟨_, hnorm hν₁ a haF, _, hnorm hν₂' b hbF,
                  ν₁ a / ν₁ (a + b), ν₁ b / ν₁ (a + b), by positivity, by positivity, ?_, ?_⟩
                · rw [← add_div, ← map_add, div_self hpos.ne']
                · rw [smul_smul, smul_smul, smul_add]
                  congr 1
                  · rw [div_mul_eq_mul_div, mul_inv_cancel₀ hνa.ne', one_div]
                  · rw [div_mul_eq_mul_div, mul_inv_cancel₀ hνb.ne', one_div]
          exact mem_ofCone.2 ⟨_, smul_ne_zero (inv_ne_zero hpos.ne') hz0, hzD,
            mk_smul hz0 (inv_pos.2 hpos) _⟩
        · intro hx
          obtain ⟨v, hv0, hvD, hvz⟩ := mem_ofCone.1 hx
          obtain ⟨c, hc, rfl⟩ := (mk_eq_mk_iff_exists_pos hv0 hz0).1 hvz
          exact hCpos c hc v (hDC hvD)
      rw [hWD]
      exact isCompact_ofCone hD hD0
    · exact hW₁.2.2.mono (interior_mono (subset_enveloppeConvexe _ |>.trans' subset_union_left))
  · intro h
    apply hl₂
    refine LinearMap.ext fun v => ?_
    have := LinearMap.congr_fun h (γ v)
    simpa using this
  · -- `H₁ ∩ W' = W₁`
    rw [one_smul]
    ext x
    obtain ⟨z, hz0, rfl⟩ := exists_isRep x
    constructor
    · rintro ⟨hzH, hzW'⟩
      have hlz := (mk_mem_closedHemisphere hz0).1 hzH
      have hzC := (hmemW' z hz0).1 hzW'
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.1 hzC
      rw [hK₂'] at hb
      obtain ⟨w, hw, rfl⟩ := hb
      have hmem : a + γ w ∈ kPrime W₁ := by
        rcases mem_insert_iff.1 hw with rfl | hwF
        · rw [map_zero, add_zero]; exact ha
        · exact (hU₁ _ (hγ₁ w hwF)).2.2 a ha hlz
      obtain ⟨_, h⟩ := (mem_insert_iff.1 hmem).resolve_left hz0
      exact h
    · intro hx
      exact ⟨hH₁ hx, subset_enveloppeConvexe _ (Or.inl hx)⟩
  · -- `γ H₂ ∩ W' = γ W₂`
    ext x
    obtain ⟨z, hz0, rfl⟩ := exists_isRep x
    constructor
    · rintro ⟨hzH, hzW'⟩
      have hlz := (mk_mem_closedHemisphere hz0).1 hzH
      have hzC := (hmemW' z hz0).1 hzW'
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.1 hzC
      rw [hK₂'] at hb
      obtain ⟨w, hw, rfl⟩ := hb
      have hmem : w + γ.symm a ∈ kPrime W₂ := by
        rcases mem_insert_iff.1 ha with rfl | haF
        · rw [map_zero, add_zero]; exact hw
        · refine (hU₂ _ (hγ₂ a haF)).2 w hw ?_
          have : (l₂ ∘ₗ γ.symm.toLinearMap) (a + γ w) = l₂ (w + γ.symm a) := by
            simp [add_comm]
          rwa [this] at hlz
      have hz' : a + γ w = γ (w + γ.symm a) := by simp [add_comm]
      have hne : w + γ.symm a ≠ 0 := fun h => hz0 (by rw [hz', h, map_zero])
      obtain ⟨_, h⟩ := (mem_insert_iff.1 hmem).resolve_left hne
      have : a + γ w ∈ F W₂' := by rw [hF₂', hz']; exact ⟨_, ⟨hne, h⟩, rfl⟩
      exact this.2
    · intro hx
      refine ⟨?_, subset_enveloppeConvexe _ (Or.inr hx)⟩
      rw [← smul_closedHemisphere_linearEquiv]
      exact smul_set_mono hH₂ hx
  · -- `W₁ ∩ γ W₂ = ∅`
    rw [one_smul, eq_empty_iff_forall_notMem]
    rintro x ⟨hx1, hx2⟩
    obtain ⟨z, hz0, rfl⟩ := exists_isRep x
    have hz2 : z ∈ F W₂' := ⟨hz0, hx2⟩
    rw [hF₂'] at hz2
    obtain ⟨w, hw, hwz⟩ := hz2
    have h1 := (hU₁ _ (hγ₁ w hw)).2.1
    rw [hwz] at h1
    exact absurd (hlW₁ z ⟨hz0, hx1⟩) (not_le.2 h1)
  · rw [one_smul]
  · exact one_smul _ _
  · exact smul_closedHemisphere_linearEquiv γ l₂

/-- **Prop. 3, accolant form**, for `n ≥ 1`. -/
theorem prop3_accole (hn : 1 ≤ n) {l₁ l₂ : Module.Dual ℝ Eₙ} (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0)
    {W₁ W₂ : Set (S n)} (hW₁ : IsCorpsConvexeS n W₁) (hW₂ : IsCorpsConvexeS n W₂)
    (hH₁ : W₁ ⊆ closedHemisphere l₁) (hH₂ : W₂ ⊆ closedHemisphere l₂)
    (hV₁ : sature l₁ W₁ ≠ W₁) (hV₂ : sature l₂ W₂ ≠ W₂) :
    ∃ W', Accole l₁ W₁ l₂ W₂ W' := by
  obtain ⟨ν₁, U₁, hν₁, hU₁o, hU₁c, hU₁, p₁, hp₁, ν₁', hν₁', hp₁'⟩ := pair_data hn hl₁ hW₁ hH₁ hV₁
  obtain ⟨ν₂, U₂, hν₂, hU₂o, hU₂c, hU₂, p₂, hp₂, ν₂', hν₂', hp₂'⟩ := pair_data hn hl₂ hW₂ hH₂ hV₂
  have hp₁0 : p₁ ≠ 0 := fun h => by
    have := (hU₁ p₁ hp₁).1; rw [h, map_zero] at this; exact lt_irrefl _ this
  have hp₂0 : p₂ ≠ 0 := fun h => by
    have := (hU₂ p₂ hp₂).1; rw [h, map_zero] at this; exact lt_irrefl _ this
  have hne₁ : W₁.Nonempty := hW₁.2.2.mono interior_subset
  have hne₂ : W₂.Nonempty := hW₂.2.2.mono interior_subset
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨γ, hγ₁, hγ₂⟩ := exists_squeeze hW₁.2.1 hW₂.2.1 hne₁ hne₂ hU₁o hU₂o hU₁c hU₂c hp₁ hp₂
    hp₁0 hp₂0 hν₁' hν₂' hp₁' hp₂'
  exact ⟨_, accole_of_squeeze hl₁ hl₂ hW₁ hW₂ hH₁ hH₂ hν₁ hU₁
    (fun y hy => (hU₂ y hy).2) γ hγ₁ hγ₂⟩

/-- **Prop. 3** (`bzprop:c3s6p3_raccordement`), for `n ≥ 1`. -/
theorem prop3_raccordement (hn : 1 ≤ n) {l₁ l₂ : Module.Dual ℝ Eₙ} (hl₁ : l₁ ≠ 0)
    (hl₂ : l₂ ≠ 0) {W₁ W₂ : Set (S n)} (hW₁ : IsCorpsConvexeS n W₁) (hW₂ : IsCorpsConvexeS n W₂)
    (hH₁ : W₁ ⊆ closedHemisphere l₁) (hH₂ : W₂ ⊆ closedHemisphere l₂)
    (hV₁ : sature l₁ W₁ ≠ W₁) (hV₂ : sature l₂ W₂ ≠ W₂) :
    ∃ W', Raccorde l₁ W₁ l₂ W₂ W' := by
  obtain ⟨W', h⟩ := prop3_accole hn hl₁ hl₂ hW₁ hW₂ hH₁ hH₂ hV₁ hV₂
  exact ⟨W', h.raccorde⟩

/-- In `S(0)` two distinct points are diametrically opposite. -/
theorem S0_eq_neg_of_ne {x y : S 0} (h : x ≠ y) : y = -x := by
  obtain ⟨a, ha, rfl⟩ := exists_isRep x
  obtain ⟨b, hb, rfl⟩ := exists_isRep y
  have hfun : ∀ v : Fin 1 → ℝ, v = v 0 • (fun _ => (1 : ℝ)) := fun v => by
    funext i; rw [Subsingleton.elim i 0]; simp
  have ha0 : a 0 ≠ 0 := fun h0 => ha (by rw [hfun a, h0, zero_smul])
  have hb0 : b 0 ≠ 0 := fun h0 => hb (by rw [hfun b, h0, zero_smul])
  have hq : b 0 / a 0 = a 0 * b 0 / a 0 ^ 2 := by
    rw [pow_two, mul_comm (a 0) (b 0), mul_div_mul_right _ _ ha0]
  rw [neg_mk, mk_eq_mk_iff_exists_pos]
  rcases lt_or_gt_of_ne (mul_ne_zero ha0 hb0) with hneg | hpos
  · have hq' : a 0 / b 0 = a 0 * b 0 / b 0 ^ 2 := by
      rw [pow_two, mul_div_mul_right _ _ hb0]
    refine ⟨-(a 0 / b 0), ?_, ?_⟩
    · have : a 0 / b 0 < 0 := by
        rw [hq']; exact div_neg_of_neg_of_pos hneg (by positivity)
      linarith
    · funext i
      obtain rfl : i = 0 := Subsingleton.elim (α := Fin 1) i 0
      simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul, neg_mul]
      rw [div_mul_cancel₀ _ hb0]
  · exfalso
    apply h
    rw [mk_eq_mk_iff_exists_pos]
    refine ⟨b 0 / a 0, ?_, ?_⟩
    · rw [hq]; exact div_pos hpos (by positivity)
    · funext i
      obtain rfl : i = 0 := Subsingleton.elim (α := Fin 1) i 0
      simp only [Pi.smul_apply, smul_eq_mul]
      exact div_mul_cancel₀ _ ha0

/-- **`n = 0`: Prop. 3 fails** (« imprecise »: a degenerate case the paper plausibly excludes).
In `S(0)` (two points), `W = H = {e}` is a convex body, its saturated convex is all of `S(0)`, yet
no convex body contains two disjoint nonempty parts. -/
theorem raccordement_dimZero : ∃ (l : Module.Dual ℝ (Fin 1 → ℝ)) (W : Set (S 0)), l ≠ 0 ∧
    IsCorpsConvexeS 0 W ∧ W ⊆ closedHemisphere l ∧ sature l W ≠ W ∧
    ∀ W', ¬ Raccorde l W l W W' := by
  set l : Module.Dual ℝ (Fin 1 → ℝ) := LinearMap.proj 0 with hldef
  have he : (fun _ => (1 : ℝ) : Fin 1 → ℝ) ≠ 0 := fun h => by simpa using congrFun h 0
  set e : S 0 := mk (fun _ => (1 : ℝ)) he with hedef
  have hl : l ≠ 0 := fun h => by
    have := LinearMap.congr_fun h (fun _ => (1 : ℝ))
    simp [l] at this
  have hfun : ∀ v : Fin 1 → ℝ, v = v 0 • (fun _ => (1 : ℝ)) := fun v => by
    funext i; rw [Subsingleton.elim i 0]; simp
  have heH : e ∈ openHemisphere l := (mk_mem_openHemisphere he).2 (by simp [l])
  have hHo : IsOpen (openHemisphere l) :=
    isOpen_ofCone (isPosCone_pos l) (isOpen_lt continuous_const l.continuous_of_finiteDimensional)
  refine ⟨l, closedHemisphere l, hl, ⟨⟨isConvexPart_closedHemisphere l, fun x hx hnx => ?_⟩,
    (isClosed_closedHemisphere' l).isCompact, ⟨e, ?_⟩⟩, subset_rfl, ?_, ?_⟩
  · obtain ⟨v, hv, rfl⟩ := exists_isRep x
    rw [neg_mk] at hnx
    have h1 := (mk_mem_closedHemisphere hv).1 hx
    have h2 := (mk_mem_closedHemisphere _).1 hnx
    simp only [map_neg] at h2
    have h0 : l v = 0 := by linarith
    apply hv
    rw [hfun v]
    simp only [l, LinearMap.coe_proj, Function.eval] at h0
    rw [h0, zero_smul]
  · exact interior_maximal (openHemisphere_subset_closedHemisphere' l) hHo heH
  · intro h
    have huniv : Prolonge l (closedHemisphere l) univ :=
      ⟨isConvexPart_iff_isSegConvex.2 isSegConvex_univ, by
        rw [univ_inter, inter_eq_right.2 (openHemisphere_subset_closedHemisphere' l)]⟩
    have hsub : (univ : Set (S 0)) ⊆ sature l (closedHemisphere l) :=
      subset_sUnion_of_mem huniv
    rw [h] at hsub
    have := hsub (mem_univ (-e))
    rw [hedef, neg_mk, mk_mem_closedHemisphere] at this
    simp [l] at this
    linarith
  · rintro W' ⟨g₁, g₂, l₁', l₂', hbody, -, -, h1, h2, hdisj, -, -, -⟩
    have hne : ∀ g : GSR 0, (g • closedHemisphere l).Nonempty := fun g =>
      ⟨g • e, smul_mem_smul_set (openHemisphere_subset_closedHemisphere' l heH)⟩
    obtain ⟨x, hx⟩ := hne g₁
    obtain ⟨y, hy⟩ := hne g₂
    have hxW : x ∈ W' := by rw [← h1] at hx; exact hx.2
    have hyW : y ∈ W' := by rw [← h2] at hy; exact hy.2
    have hxy : x ≠ y := fun hxy => by
      rw [hxy] at hx
      have : y ∈ (g₁ • closedHemisphere l) ∩ (g₂ • closedHemisphere l) := ⟨hx, hy⟩
      rw [hdisj] at this
      exact this
    rw [S0_eq_neg_of_ne hxy] at hyW
    exact hbody.1.2 x hxW hyW

/-! ### Instances -/

namespace RaccordementInstance

open TriangleInstance

variable (m : ℕ)

/-- The form `x₀` on `ℝᵐ⁺²`. -/
def formX0 : Module.Dual ℝ (Fin (m + 1 + 1) → ℝ) := LinearMap.proj 0

/-- The cone of a prolongation of the simplex beyond `{x₀ > 0}`: `x₀ + x₁ ≥ 0`, `xᵢ ≥ 0`
(`i ≠ 0`). -/
def prolongeCone : Set (Fin (m + 1 + 1) → ℝ) := {v | 0 ≤ v 0 + v 1 ∧ ∀ i, i ≠ 0 → 0 ≤ v i}

/-- The point `(−1, 1, 0, …)`, beyond `h = {x₀ = 0}`. -/
def pointQ : Fin (m + 1 + 1) → ℝ := Pi.single 1 1 - Pi.single 0 1

theorem pointQ_zero : pointQ m 0 = -1 := by
  simp [pointQ]

theorem pointQ_ne : pointQ m ≠ 0 := fun h => by
  have := pointQ_zero m
  rw [h] at this
  simp at this

theorem pointQ_mem : pointQ m ∈ prolongeCone m := by
  have h10 : (1 : Fin (m + 1 + 1)) ≠ 0 := (Fin.zero_lt_one (n := m)).ne'
  refine ⟨?_, fun i hi => ?_⟩
  · rw [pointQ_zero]
    simp [pointQ, h10]
  · simp only [pointQ, Pi.sub_apply, Pi.single_apply, if_neg hi, sub_zero]
    split_ifs <;> norm_num

/-- **The hypotheses of Prop. 3 hold** for the simplex of `S(m+1)` and `H = {x₀ ≥ 0}`: a convex
body whose saturated convex beyond `H̊` is strictly larger (it contains `(−1, 1, 0, …)`). -/
theorem simplexS_hypotheses : formX0 m ≠ 0 ∧ IsCorpsConvexeS (m + 1) (simplexS (m + 1)) ∧
    simplexS (m + 1) ⊆ closedHemisphere (formX0 m) ∧
    sature (formX0 m) (simplexS (m + 1)) ≠ simplexS (m + 1) := by
  have horth : IsPosCone (orthant (m + 1)) := fun _ hc _ hv => orthant_smul hc hv
  refine ⟨fun h => ?_, isCorpsConvexeS_simplexS, fun x hx => ?_, fun h => ?_⟩
  · have := LinearMap.congr_fun h (Pi.single 0 1)
    simp [formX0] at this
  · obtain ⟨v, hv, rfl⟩ := exists_isRep x
    rw [simplexS, mk_mem_ofCone_iff horth] at hx
    rw [mk_mem_closedHemisphere]
    exact hx 0
  · have hPpos : IsPosCone (prolongeCone m) := by
      rintro c hc v ⟨h1, h2⟩
      refine ⟨?_, fun i hi => ?_⟩
      · simp only [Pi.smul_apply, smul_eq_mul, ← mul_add]; exact mul_nonneg hc.le h1
      · simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg hc.le (h2 i hi)
    have hPconv : Convex ℝ (prolongeCone m) := by
      rintro v ⟨hv1, hv2⟩ w ⟨hw1, hw2⟩ a b ha hb _
      refine ⟨?_, fun i hi => ?_⟩
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        nlinarith [mul_nonneg ha hv1, mul_nonneg hb hw1]
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        exact add_nonneg (mul_nonneg ha (hv2 i hi)) (mul_nonneg hb (hw2 i hi))
    have hP : Prolonge (formX0 m) (simplexS (m + 1)) (ofCone (prolongeCone m)) := by
      refine ⟨isConvexPart_ofCone hPpos ⟨by simp, fun i _ => le_rfl⟩ hPconv, ?_⟩
      ext x
      obtain ⟨v, hv, rfl⟩ := exists_isRep x
      rw [mem_inter_iff, mem_inter_iff, mk_mem_ofCone_iff hPpos, simplexS,
        mk_mem_ofCone_iff horth, mk_mem_openHemisphere]
      simp only [formX0, LinearMap.coe_proj, Function.eval]
      constructor
      · rintro ⟨⟨_, h2⟩, h0⟩
        refine ⟨fun i => ?_, h0⟩
        by_cases hi : i = 0
        · rw [hi]; exact h0.le
        · exact h2 i hi
      · rintro ⟨h1, h0⟩
        exact ⟨⟨add_nonneg (h1 0) (h1 1), fun i _ => h1 i⟩, h0⟩
    have hsub : ofCone (prolongeCone m) ⊆ sature (formX0 m) (simplexS (m + 1)) :=
      subset_sUnion_of_mem hP
    rw [h] at hsub
    have := hsub (mk_mem_ofCone (pointQ_ne m) (pointQ_mem m))
    rw [simplexS, mk_mem_ofCone_iff horth] at this
    have h0 := this 0
    rw [pointQ_zero] at h0
    norm_num at h0

/-- **An instance of « accoler »** (hence of « raccorder »): two copies of the simplex of
`S(m+1)`, cut by `h = {x₀ = 0}`, can be joined. -/
theorem accole_simplexS :
    ∃ W', Accole (formX0 m) (simplexS (m + 1)) (formX0 m) (simplexS (m + 1)) W' := by
  obtain ⟨hl, hW, hH, hV⟩ := simplexS_hypotheses m
  exact prop3_accole (by omega) hl hl hW hW hH hH hV hV

theorem raccorde_simplexS :
    ∃ W', Raccorde (formX0 m) (simplexS (m + 1)) (formX0 m) (simplexS (m + 1)) W' := by
  obtain ⟨W', h⟩ := accole_simplexS m
  exact ⟨W', h.raccorde⟩

end RaccordementInstance

end Benzecri
