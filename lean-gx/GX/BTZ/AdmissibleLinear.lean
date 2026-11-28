import GX.BTZ.Uniformization
import Causal.Flat.ACDProof
import Causal.Flat.MaxUnipProof
import Causal.Flat.BieberbachProof
import Causal.Flat.Lox.SecondNullFix

/-!
# btz § 4.1: the linear part of the holonomy of `Reg M` is faithful and discrete (Barbot, in 2+1)

Target `T-btz-linear-part-faithful` (`roadmap/roadmap.toml`). `papers/btz/legacy/labeled/BTZ_1.tex`,
l.1149: « Barbot [barbot_globally_2004] proved that the linear part `ρ_L` of the holonomy of such a
manifold is discrete and faithful ». This module proves it, for the holonomy group of a
`(Isom 𝐌³, 𝐌³)`-spacetime under §8's standing data (`Causal.Flat.CCAction`), from lean-causal's
proved Barbot (DEC-34: `Causal.Flat.auslanderCarriereDalbo`, `Causal.Flat.maxUnipotentSubspace`,
`Causal.Flat.bieberbachI`, all proved, DEC-121/DEC-110), with no new external.

* `GX.BTZAdm.linOf_eq_one_imp_of_ccAction` — **faithfulness**: an element of `Γ` with trivial
  linear part is trivial, when `Γ` is not metabelian and has a loxodromic element. Barbot's
  `𝒩 = ker L ∩ Γ` spans a spacelike `E` (`Causal.Flat.span_kerTranslations_spacelike`) fixed by a
  power of the loxodromic, hence `E ⊆ ℝe` for a unit spacelike `e`; `L(Γ)` preserves the lattice
  `𝒩`, so `L(γ) e = ± e`, and then `Γ` is metabelian (`GX.BTZAdm.isMetabelianOn_of_sign`).
* `GX.BTZAdm.isNonelementary_of_ccAction` — `Γ` is nonelementary: otherwise a finite-index subgroup
  fixes two null directions (`Causal.Flat.Lox.fix_second_null`), every `L(γ)` preserves the
  spacelike line orthogonal to both up to sign, and `Γ` is metabelian again (torsion-freeness
  is spent on the elements whose powers have trivial linear part).
* `GX.BTZAdm.discreteTopology_linearImage_of_ccAction` — **discreteness**: Barbot's maximal
  unipotent subspace `U` (Props 10.4, 10.5, `Causal.Flat.bprop_U_timelike`,
  `Causal.Flat.bprop_LU_discrete`) is all of `𝐌³`: a timelike line or plane invariant under `Γ`
  would again make `Γ` metabelian, or fix a timelike vector of a loxodromic element. With `U = 𝐌³`,
  `L_U(Γ)` is `L(Γ)` conjugated by an isometry of `𝐌³`, so `L(Γ)` is discrete.
* `GX.BTZAdm.linearPart_comp_faithful_discrete` — the two together for a holonomy `ρ`.

Answer to the roadmap's question (« whether `loxo_generic_centralExtension`'s group is `Γ'`
itself or its restriction `Γ'_U` »): it is the restriction `Γ'_U`, so family (b) is not consumed
here; `U = 𝐌³` is proved instead (`GX.BTZAdm.discreteTopology_linearImage_of_ccAction`, the cases
`d₁ = 0, 1`), and `bprop_LU_discrete` is applied to `Γ` itself.

No label is marked: the module is the input of `GX.BTZAdm.e0RegM_linearPart_faithful_discrete`
(`GX/BTZ/Admissible.lean`, `btzprop:holonomy_globally_hyperbolic_cauchy_compact`).

## Hypothesis checklist

| paper (l.1149, Barbot) | here |
|---|---|
| `M*` globally hyperbolic, Cauchy-complete, `𝔼`-maximal flat spacetime | ✓ through `Causal.Flat.CCAction ρ(π₁) Σ` (`Causal.Flat.ccAction_of_developsCC`), which is what GH + Cauchy-complete give (`Causal.Flat.exists_developsCC_of_isCauchyComplete'`); maximality is not used here (for `Reg M` it enters through `GX.E0AbsMax.cor_abs_max_C1`, which gives Cauchy-completeness) |
| anabelian fundamental group | ⚠ read as « `Γ = ρ(π₁)` not metabelian » (`GX.IsMetabelianOn`), as in the strict `GX.e0RegM_holonomy` (`π₁` not metabelian and `ρ` faithful give it) |
| (silent) a loxodromic element, torsion-freeness | ✓ hypotheses of the group-level lemmas here, discharged for `ρ(π₁)` in `GX.BTZ.Admissible` by the strict `GX.e0RegM_holonomy` (DEC-75, Cor 10.3); not assumed by the exported theorem |
| `ρ_L` faithful | ✓ `L` injective on `Γ` |
| `ρ_L` discrete | ✓ `DiscreteTopology (linearImage Γ)` in `Causal.Flat.lorentzTopology` (the operator-norm topology of `SO₀(1,2)`) |

## SCOPE (disclosed)

* 2+1 only (`Minkowski 2`): the linear algebra (a spacelike line orthogonal to two null
  directions, stabilizers of spacelike vectors abelian) is that of `SO₀(1, 2)`.
* The proof is not Barbot's text: Barbot reads the faithfulness off his classification
  (l.3405–3440 of `barbot_globally_2004`, « `L` might be noninjective! »). Here the kernel and the
  elementary case are both excluded by the same metabelian argument, which uses that `π₁` is
  not metabelian in place of the classification.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; Causal at `51cbb00`.
-/

namespace GX

namespace BTZAdm

open Set Function
open Causal.Flat
open scoped commutatorElement

/-! ## Linear algebra of `SO₀(1, 2)` in a null frame -/

section Frame

variable {u e w : Causal.Minkowski 2}

/-- **A null frame through two non-orthogonal null vectors**: for `u, u'` null with
`⟨u | u'⟩ ≠ 0`, there is a unit spacelike `e` with `(u, e, (−⟨u|u'⟩)⁻¹ u')` a null frame. -/
theorem exists_isNullFrame2_of_null_pair {u u' : Causal.Minkowski 2}
    (hq : Causal.Flat.minkQ u = 0) (hq' : Causal.Flat.minkQ u' = 0) (huu' : minkB u u' ≠ 0) :
    ∃ e, IsNullFrame2 u e ((-minkB u u')⁻¹ • u') := by
  have hu0 : u ≠ 0 := fun h => huu' (by rw [h, minkB_zero_left])
  obtain ⟨e₀, w₀, F₀⟩ := exists_isNullFrame2 hu0 hq
  have hquu : minkB u u = 0 := by rw [← minkQ_eq_minkB]; exact hq
  have hqu' : minkB u' u' = 0 := by rw [← minkQ_eq_minkB]; exact hq'
  refine ⟨e₀ + (-(minkB e₀ u') / minkB u u') • u, ⟨hquu, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [minkB_smul_left, minkB_smul_right, hqu']; ring
  · rw [minkB_smul_right]; field_simp
  · simp only [minkB_add_left, minkB_add_right, minkB_smul_left, minkB_smul_right, F₀.ee, F₀.ue,
      F₀.eu, hquu]
    ring
  · simp only [minkB_add_right, minkB_smul_right, F₀.ue, hquu]; ring
  · simp only [minkB_add_right, minkB_smul_left, minkB_smul_right, minkB_comm u' e₀,
      minkB_comm u' u]
    field_simp
    ring

/-- A vector orthogonal to the two null vectors of a null frame is a multiple of its spacelike
vector: `x = ⟨x | e⟩ e`. -/
theorem frame_eq_smul_e_of_orth (F : IsNullFrame2 u e w) {x : Causal.Minkowski 2}
    (hu : minkB x u = 0) (hw : minkB x w = 0) : x = minkB x e • e := by
  conv_lhs => rw [F.expand x]
  rw [hu, hw]; simp

/-- An element of `SO₀(1, 2)` fixing the spacelike vector of a null frame is diagonal in the
frame: `X u = a u`, `X w = a⁻¹ w` (the swap `u ↔ w` has determinant `−1`). -/
theorem frame_diag_of_fix (F : IsNullFrame2 u e w)
    {X : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2} (hX : X ∈ lorentz 2) (hXe : X e = e) :
    ∃ a : ℝ, a ≠ 0 ∧ X u = a • u ∧ X w = a⁻¹ • w := by
  have hB := lorentz.minkB_apply hX
  have hue : minkB (X u) e = 0 := by rw [← hXe, hB, F.ue]
  have hwe : minkB (X w) e = 0 := by rw [← hXe, hB, F.we]
  have huu : minkB (X u) (X u) = 0 := by rw [hB, F.uu]
  have hww : minkB (X w) (X w) = 0 := by rw [hB, F.ww]
  have huw : minkB (X u) (X w) = -1 := by rw [hB, F.uw]
  rw [F.minkB_eq, hue] at huu
  rw [F.minkB_eq, hwe] at hww
  rw [F.minkB_eq, hue, hwe] at huw
  have hXu := F.expand (X u)
  have hXw := F.expand (X w)
  rw [hue] at hXu
  rw [hwe] at hXw
  set p := minkB (X u) w
  set q := minkB (X u) u
  set r := minkB (X w) w
  set s := minkB (X w) u
  have hpq : p * q = 0 := by linarith
  have hrs : r * s = 0 := by linarith
  rcases mul_eq_zero.1 hpq with hp | hq
  · -- the swap `u ↦ −q w`, `w ↦ −r u`: determinant `−1`
    exfalso
    have hqr : q * r = 1 := by rw [hp] at huw; linarith
    have hs : s = 0 := (mul_eq_zero.1 hrs).resolve_left (by rintro h; rw [h] at hqr; simp at hqr)
    have hdet := hX.2.2
    rw [← LinearMap.det_toMatrix F.basis, Matrix.det_fin_three] at hdet
    simp only [F.toMatrix_apply, frameCoord, LinearEquiv.coe_coe, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, hXe, F.ee,
      F.ew, F.eu, hue, hwe] at hdet
    rw [show minkB (X u) w = p from rfl, show minkB (X u) u = q from rfl,
      show minkB (X w) w = r from rfl, show minkB (X w) u = s from rfl, hp, hs] at hdet
    linarith
  · have hps : p * s = 1 := by rw [hq] at huw; linarith
    have hr : r = 0 := (mul_eq_zero.1 hrs).resolve_right (by rintro h; rw [h] at hps; simp at hps)
    have hp0 : p ≠ 0 := by rintro h; rw [h] at hps; simp at hps
    refine ⟨-p, neg_ne_zero.2 hp0, ?_, ?_⟩
    · rw [hXu, hq]; simp
    · rw [hXw, hr]
      have : (-p)⁻¹ = -s := by
        rw [inv_neg, inv_eq_of_mul_eq_one_right hps]
      rw [this]; simp

/-- **The stabilizer of a spacelike vector in `SO₀(1, 2)` is abelian.** -/
theorem frame_commute_of_fix (F : IsNullFrame2 u e w)
    {X Y : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2} (hX : X ∈ lorentz 2) (hY : Y ∈ lorentz 2)
    (hXe : X e = e) (hYe : Y e = e) : X * Y = Y * X := by
  obtain ⟨a, -, hXu, hXw⟩ := frame_diag_of_fix F hX hXe
  obtain ⟨b, -, hYu, hYw⟩ := frame_diag_of_fix F hY hYe
  refine F.ext ?_ ?_ ?_
  · simp only [LinearEquiv.mul_apply, hXu, hYu, map_smul, smul_smul, mul_comm]
  · simp only [LinearEquiv.mul_apply, hXe, hYe]
  · simp only [LinearEquiv.mul_apply, hXw, hYw, map_smul, smul_smul, mul_comm]

/-- A vector of `minkQ = 1` orthogonal to the two null vectors of a null frame is `± e`. -/
theorem frame_pm_of_orth {u e w : Causal.Minkowski 2} (F : IsNullFrame2 u e w)
    {y : Causal.Minkowski 2} (hy : minkB y y = 1) (h1 : minkB y u = 0) (h2 : minkB y w = 0) :
    y = e ∨ y = -e := by
  have hx := frame_eq_smul_e_of_orth F h1 h2
  rw [hx, minkB_smul_left, minkB_smul_right, F.ee] at hy
  have : (minkB y e - 1) * (minkB y e + 1) = 0 := by linear_combination hy
  rcases mul_eq_zero.1 this with h | h
  · left; rw [hx, show minkB y e = 1 by linarith, one_smul]
  · right; rw [hx, show minkB y e = -1 by linarith, neg_one_smul]

/-- An element of `SO₀(1, 2)` preserving the two null lines of a null frame maps its spacelike
vector to `± e`. -/
theorem frame_fix_or_neg_of_null_eigen (F : IsNullFrame2 u e w)
    {X : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2} (hX : X ∈ lorentz 2) {a b : ℝ}
    (ha : X u = a • u) (hb : X w = b • w) : a * b = 1 ∧ (X e = e ∨ X e = -e) := by
  have hB := lorentz.minkB_apply hX
  have hab : a * b = 1 := by
    have := hB u w
    rw [ha, hb, minkB_smul_left, minkB_smul_right, F.uw] at this
    linarith
  have ha0 : a ≠ 0 := by rintro rfl; simp at hab
  have hb0 : b ≠ 0 := by rintro rfl; simp at hab
  have h1 : minkB (X e) u = 0 := by
    have := hB e u
    rw [ha, minkB_smul_right, F.eu] at this
    exact (mul_eq_zero.1 this).resolve_left ha0
  have h2 : minkB (X e) w = 0 := by
    have := hB e w
    rw [hb, minkB_smul_right, F.ew] at this
    exact (mul_eq_zero.1 this).resolve_left hb0
  have hx := frame_eq_smul_e_of_orth F h1 h2
  set c := minkB (X e) e
  have hq : minkB (X e) (X e) = 1 := by rw [hB, F.ee]
  rw [hx, minkB_smul_left, minkB_smul_right, F.ee] at hq
  refine ⟨hab, ?_⟩
  have hc : c = 1 ∨ c = -1 := by
    have : (c - 1) * (c + 1) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  rcases hc with hc | hc
  · left; rw [hx, hc, one_smul]
  · right; rw [hx, hc, neg_one_smul]

end Frame

/-! ## Isometries -/

section Isom

/-- An isometry with trivial linear and translation parts is the identity. -/
theorem isom_eq_one_of_linOf_trOf {g : isom 2} (h1 : linOf g = 1) (h0 : trOf g = 0) : g = 1 := by
  refine Subtype.ext (AffineEquiv.ext fun x => ?_)
  have := smul_eq_lin_add g x
  rw [h1, h0, add_zero, isom_smul_def] at this
  exact this

/-- **The translation part of a commutator** of isometries whose linear parts fix `v`, when the
commutator is a translation, is orthogonal to `v`: `τ = (L_a − 1) τ_b − (L_b − 1) τ_a`. -/
theorem minkB_trOf_commutator {a b : isom 2} {v : Causal.Minkowski 2} (ha : linOf a v = v)
    (hb : linOf b v = v) (h1 : linOf ⁅a, b⁆ = 1) : minkB (trOf ⁅a, b⁆) v = 0 := by
  have hrel : ⁅a, b⁆ * b * a = a * b := by rw [commutatorElement_def]; group
  have ht := congrArg trOf hrel
  rw [trOf_mul, trOf_mul, trOf_mul, linOf_mul, h1, one_mul] at ht
  have hfix : ∀ g : isom 2, linOf g v = v → ∀ x, minkB (linOf g x - x) v = 0 := by
    intro g hg x
    have := lorentz.minkB_apply (linOf_mem g) x v
    rw [hg] at this
    rw [minkB_sub_left, this, sub_self]
  have hτ : trOf ⁅a, b⁆ = (linOf a (trOf b) - trOf b) - (linOf b (trOf a) - trOf a) := by
    simp only [LinearEquiv.coe_one, id_eq] at ht
    rw [← sub_eq_zero] at ht ⊢
    rw [← ht]; abel
  rw [hτ, minkB_sub_left, hfix a ha, hfix b hb, sub_self]

/-- **The metabelian criterion**: if every linear part of `Γ ≤ Isom(𝐌³)` maps the spacelike vector
`e` of a null frame to `± e`, and the translations of `Γ` orthogonal to `e` are trivial, then `Γ`
is metabelian (the commutators fix `e`, their linear parts commute, and the commutator of two
of them is a translation orthogonal to `e`). -/
theorem isMetabelianOn_of_sign {u e w : Causal.Minkowski 2} (F : IsNullFrame2 u e w)
    {Γ : Subgroup (isom 2)} (hs : ∀ γ ∈ Γ, linOf γ e = e ∨ linOf γ e = -e)
    (hK : ∀ γ ∈ Γ, linOf γ = 1 → minkB (trOf γ) e = 0 → γ = 1) : IsMetabelianOn Γ := by
  -- the signs: `L(γ) e = s e` with `s² = 1`, and the same for `L(γ)⁻¹`
  have hsgn : ∀ γ ∈ Γ, ∃ s : ℝ, s * s = 1 ∧ linOf γ e = s • e := by
    intro γ hγ
    rcases hs γ hγ with h | h
    · exact ⟨1, by norm_num, by rw [h, one_smul]⟩
    · exact ⟨-1, by norm_num, by rw [h, neg_one_smul]⟩
  have hinv : ∀ (A : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2) (s : ℝ), s * s = 1 →
      A e = s • e → A⁻¹ e = s • e := by
    intro A s hs1 hA
    apply A.injective
    rw [show A (A⁻¹ e) = e from A.apply_symm_apply e, map_smul, hA, smul_smul, hs1, one_smul]
  -- commutators fix `e`
  have key : ∀ x ∈ Γ, ∀ y ∈ Γ, linOf ⁅x, y⁆ e = e := by
    intro x hx y hy
    obtain ⟨s, hs1, hxs⟩ := hsgn x hx
    obtain ⟨t, ht1, hyt⟩ := hsgn y hy
    rw [commutatorElement_def, linOf_mul, linOf_mul, linOf_mul, linOf_inv, linOf_inv]
    simp only [LinearEquiv.mul_apply, hinv _ s hs1 hxs, hinv _ t ht1 hyt, map_smul, hxs, hyt,
      smul_smul]
    have : s * (t * (s * t)) = 1 := by linear_combination (t * t) * hs1 + ht1
    rw [show t * (s * (t * s)) = s * (t * (s * t)) by ring, this, one_smul]
  have hmem : ∀ x ∈ Γ, ∀ y ∈ Γ, ⁅x, y⁆ ∈ Γ := fun x hx y hy => by
    rw [commutatorElement_def]
    exact Γ.mul_mem (Γ.mul_mem (Γ.mul_mem hx hy) (Γ.inv_mem hx)) (Γ.inv_mem hy)
  intro a ha b hb c hc d hd
  have hX := key a ha b hb
  have hY := key c hc d hd
  have hcomm := frame_commute_of_fix F (linOf_mem ⁅a, b⁆) (linOf_mem ⁅c, d⁆) hX hY
  have h1 := linOf_commutator_eq_one hcomm
  exact hK _ (hmem _ (hmem a ha b hb) _ (hmem c hc d hd)) h1 (minkB_trOf_commutator hX hY h1)

end Isom

/-! ## Barbot in 2+1: faithfulness, nonelementarity, discreteness -/

section Barbot

variable {Γ : Subgroup (isom 2)} {S : Set (Causal.Minkowski 2)}

/-- **The linear part is faithful on `Γ`** (Barbot, l.1149 of BTZ_1; `barbot_globally_2004`
l.3405–3440): under §8's data, with a loxodromic element and `Γ` not metabelian, an element of
`Γ` with trivial linear part is trivial. -/
theorem linOf_eq_one_imp_of_ccAction (h : CCAction Γ S) (hlox : ∃ γ ∈ Γ, IsLoxodromic (linOf γ))
    (hnm : ¬IsMetabelianOn Γ) : ∀ γ ∈ Γ, linOf γ = 1 → γ = 1 := by
  intro γ hγ h1
  by_contra hne
  have hvT : trOf γ ∈ kerTranslations Γ := ⟨γ, hγ, h1, rfl⟩
  have hv0 : trOf γ ≠ 0 := fun h0 => hne (isom_eq_one_of_linOf_trOf h1 h0)
  -- Barbot's `E = span 𝒩` is fixed pointwise by a finite-index `Γ'` (l.3412–3417)
  obtain ⟨Γ', -, hidx, hfixE⟩ := exists_finiteIndex_linOf_eq_on_span_kerTranslations h hlox
  obtain ⟨γ₀, hγ₀, hlox₀⟩ := hlox
  obtain ⟨k, hk, -, hk'⟩ := Subgroup.exists_pow_mem_of_relIndex_ne_zero hidx hγ₀
  obtain ⟨-, u, u', l, -, -, -, -, -, hq, hq', huu', hl, hl1, hAu, hAu', -⟩ := hlox₀.frame
  have hpow : ∀ (y : Causal.Minkowski 2) (c : ℝ), linOf γ₀ y = c • y →
      ∀ n : ℕ, linOf (γ₀ ^ n) y = c ^ n • y := by
    intro y c hy n
    induction n with
    | zero => simp [linOf_one']
    | succ n ih => rw [pow_succ, linOf_mul, LinearEquiv.mul_apply, hy, map_smul, ih, smul_smul,
        pow_succ, mul_comm]
  -- the fixed vectors of the loxodromic `L(γ₀ᵏ)` are orthogonal to its null eigenvectors
  have horth : ∀ x, linOf (γ₀ ^ k) x = x → minkB x u = 0 ∧ minkB x u' = 0 := by
    intro x hx
    have hB := lorentz.minkB_apply (linOf_mem (γ₀ ^ k))
    have e1 := hB x u
    rw [hx, hpow u l hAu k, minkB_smul_right] at e1
    have e2 := hB x u'
    rw [hx, hpow u' l⁻¹ hAu' k, minkB_smul_right] at e2
    have hln : l ^ k ≠ 1 := fun h => hl1 ((pow_eq_one_iff_of_nonneg hl.le hk.ne').1 h)
    have hln' : l⁻¹ ^ k ≠ 1 := fun h =>
      hl1 (inv_eq_one.1 ((pow_eq_one_iff_of_nonneg (inv_pos.2 hl).le hk.ne').1 h))
    refine ⟨?_, ?_⟩
    · have : (l ^ k - 1) * minkB x u = 0 := by linear_combination e1
      exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hln)
    · have : (l⁻¹ ^ k - 1) * minkB x u' = 0 := by linear_combination e2
      exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hln')
  obtain ⟨e, F⟩ := exists_isNullFrame2_of_null_pair hq hq' huu'
  -- so `E ⊆ ℝ e`
  have hE : ∀ x ∈ Submodule.span ℝ (kerTranslations Γ), x = minkB x e • e := by
    intro x hx
    obtain ⟨h1, h2⟩ := horth x (hfixE _ hk'.1 x hx)
    exact frame_eq_smul_e_of_orth F h1 (by rw [minkB_smul_right, h2, mul_zero])
  have hT : ∀ x ∈ kerTranslations Γ, x = minkB x e • e := fun x hx =>
    hE x (Submodule.subset_span hx)
  obtain ⟨c, hc⟩ : ∃ c : ℝ, trOf γ = c • e := ⟨_, hT _ hvT⟩
  have hc0 : c ≠ 0 := by rintro rfl; rw [zero_smul] at hc; exact hv0 hc
  -- `L(Γ)` preserves `𝒩`, hence maps `e` to `± e`
  have hs : ∀ δ ∈ Γ, linOf δ e = e ∨ linOf δ e = -e := by
    intro δ hδ
    obtain ⟨c', hc'⟩ : ∃ c' : ℝ, linOf δ (trOf γ) = c' • e :=
      ⟨_, hT _ (linOf_mem_kerTranslations hδ hvT)⟩
    have hQ := lorentz.minkB_apply (linOf_mem δ) (trOf γ) (trOf γ)
    rw [hc', hc, minkB_smul_left, minkB_smul_right, minkB_smul_left, minkB_smul_right, F.ee] at hQ
    have hLe : c • linOf δ e = c' • e := by rw [← map_smul, ← hc, hc']
    have hsq : (c' - c) * (c' + c) = 0 := by linear_combination hQ
    rcases mul_eq_zero.1 hsq with h0 | h0
    · left
      have : c' = c := by linarith
      rw [this] at hLe
      exact smul_right_injective _ hc0 hLe
    · right
      have : c' = -c := by linarith
      rw [this, neg_smul, ← smul_neg] at hLe
      exact smul_right_injective _ hc0 hLe
  have hK : ∀ δ ∈ Γ, linOf δ = 1 → minkB (trOf δ) e = 0 → δ = 1 := by
    intro δ hδ hL h0
    refine isom_eq_one_of_linOf_trOf hL ?_
    rw [hT _ ⟨δ, hδ, hL, rfl⟩, h0, zero_smul]
  exact hnm (isMetabelianOn_of_sign F hs hK)

/-- **`Γ` is nonelementary** (Barbot's [10.G] case, l.3336–3337): under §8's data, with a
loxodromic element, `Γ` torsion-free and not metabelian. -/
theorem isNonelementary_of_ccAction (h : CCAction Γ S) (hlox : ∃ γ ∈ Γ, IsLoxodromic (linOf γ))
    (hnm : ¬IsMetabelianOn Γ) (htf : IsTorsionFreeSubgroup Γ) : IsNonelementary Γ := by
  have hinj := linOf_eq_one_imp_of_ccAction h hlox hnm
  intro H hH hHi hu
  obtain ⟨γ₀, hγ₀, hlox₀⟩ := hlox
  -- the elementary case (Barbot [10.M], l.3237–3299): a finite-index `Γ₁` fixing the two fixed
  -- points `u₀ ≠ u₁` of `L(γ₀)` on `𝒮`
  obtain ⟨Γ₁, hΓ₁, hΓ₁i, k, hk, hγ₀k, u₀, u₁, hu₀₁, -, hf₁, hfix₀⟩ :=
    Lox.exists_finiteIndex_fix_loxodromic hγ₀ hlox₀ ⟨H, hH, hHi, hu⟩
  have hloxk : IsLoxodromic (linOf (γ₀ ^ k)) := by
    have := hlox₀.zpow_linOf (n := (k : ℤ)) (by exact_mod_cast hk.ne')
    rwa [zpow_natCast] at this
  have hf₀' : ∀ γ ∈ Γ₁, lorentzSphere (linearPart γ) u₀ = u₀ := fun γ hγ =>
    hfix₀ _ ⟨γ, hγ, rfl⟩
  obtain ⟨s₀, hs₀⟩ := exists_invariant_nullLevel_of_ccAction h hΓ₁ hf₀' ⟨_, hγ₀k, hloxk⟩
  have hf₁' : ∀ γ ∈ Γ₁, lorentzSphere (linearPart γ) u₁ = u₁ :=
    Lox.fix_second_null (bieberbachI (E := EuclideanSpace ℝ (Fin 1))) h hΓ₁ hγ₀k hloxk hu₀₁ hf₀'
      (by rw [map_pow]; exact Lox.lorentzSphere_fix_pow hf₁ k) hs₀
  -- in vectors: `L(γ)` scales `nullVec u₀` and `nullVec u₁`
  have hvec : ∀ γ : isom 2, ∀ v : PenroseSphere 2, lorentzSphere (linearPart γ) v = v →
      ∃ a : ℝ, linOf γ (nullVec v) = a • nullVec v := by
    intro γ v hv
    refine ⟨lorentzScale (linearPart γ) v, ?_⟩
    have e := nullVec_lorentzSphere (linearPart γ) v
    rw [hv] at e
    rw [linOf_eq_linearPart]
    conv_rhs => rw [e]
    rw [smul_smul, mul_inv_cancel₀ (lorentzScale_pos _ _).ne', one_smul]
  have h01 : minkB (nullVec u₀) (nullVec u₁) ≠ 0 := by
    rw [minkB_nullVec_nullVec]
    have : ‖((u₀ : EuclideanSpace ℝ (Fin 2)) - u₁)‖ ≠ 0 := by
      rw [norm_ne_zero_iff, sub_ne_zero]
      exact fun h => hu₀₁ (Subtype.ext h)
    have := pow_pos (lt_of_le_of_ne (norm_nonneg _) this.symm) 2
    intro h; linarith
  obtain ⟨e, F⟩ := exists_isNullFrame2_of_null_pair (minkQ_nullVec u₀) (minkQ_nullVec u₁) h01
  set w := (-minkB (nullVec u₀) (nullVec u₁))⁻¹ • nullVec u₁ with hw
  have hvec₁ : ∀ γ ∈ Γ₁, ∃ b : ℝ, linOf γ w = b • w := by
    intro γ hγ
    obtain ⟨b, hb⟩ := hvec γ u₁ (hf₁' γ hγ)
    exact ⟨b, by rw [hw, map_smul, hb, smul_comm]⟩
  -- every `L(g)`, `g ∈ Γ`, maps `e` to `± e`
  have hs : ∀ g ∈ Γ, linOf g e = e ∨ linOf g e = -e := by
    intro g hg
    obtain ⟨m, hm, -, hgm⟩ := Subgroup.exists_pow_mem_of_relIndex_ne_zero hΓ₁i hg
    set z := g ^ m with hzdef
    obtain ⟨a, ha⟩ := hvec z u₀ (hf₀' z hgm.1)
    obtain ⟨b, hb⟩ := hvec₁ z hgm.1
    obtain ⟨hab, hze⟩ := frame_fix_or_neg_of_null_eigen F (linOf_mem z) ha hb
    have hZu : linOf (z * z) (nullVec u₀) = (a * a) • nullVec u₀ := by
      rw [linOf_mul, LinearEquiv.mul_apply, ha, map_smul, ha, smul_smul]
    have hZw : linOf (z * z) w = (b * b) • w := by
      rw [linOf_mul, LinearEquiv.mul_apply, hb, map_smul, hb, smul_smul]
    have hZe : linOf (z * z) e = e := by
      rcases hze with h' | h'
      · rw [linOf_mul, LinearEquiv.mul_apply, h', h']
      · rw [linOf_mul, LinearEquiv.mul_apply, h', map_neg, h', neg_neg]
    have hzzΓ : z * z ∈ Γ := Γ.mul_mem hgm.2 hgm.2
    have hzz : z * z = g ^ (m + m) := by rw [hzdef, pow_add]
    by_cases ha2 : a * a = 1
    · have hbb : b * b = 1 := by
        have : (a * a) * (b * b) = 1 := by rw [show (a * a) * (b * b) = (a * b) * (a * b) by ring,
          hab, one_mul]
        rwa [ha2, one_mul] at this
      have hZ1 : linOf (z * z) = 1 := by
        refine F.ext ?_ ?_ ?_
        · rw [hZu, ha2, one_smul]; rfl
        · rw [hZe]; rfl
        · rw [hZw, hbb, one_smul]; rfl
      have h1 := hinj _ hzzΓ hZ1
      have hfin : IsOfFinOrder g :=
        isOfFinOrder_iff_pow_eq_one.2 ⟨m + m, by omega, by rw [← hzz]; exact h1⟩
      left
      rw [htf g hg hfin, linOf_one']
      rfl
    · have hbb : b * b ≠ 1 := by
        intro hbb
        apply ha2
        have : (a * a) * (b * b) = 1 := by rw [show (a * a) * (b * b) = (a * b) * (a * b) by ring,
          hab, one_mul]
        rwa [hbb, mul_one] at this
      -- `L(g) e` is fixed by `L(g)^{2m}`, whose fixed vectors are orthogonal to `u₀`, `w`
      have hcomm : linOf (z * z) (linOf g e) = linOf g e := by
        have hc : linOf (z * z) (linOf g e) = linOf g (linOf (z * z) e) := by
          rw [hzz, linOf_pow, ← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← pow_succ,
            ← pow_succ']
        rw [hc, hZe]
      have hB := lorentz.minkB_apply (linOf_mem (z * z))
      have e1 := hB (linOf g e) (nullVec u₀)
      rw [hcomm, hZu, minkB_smul_right] at e1
      have e2 := hB (linOf g e) w
      rw [hcomm, hZw, minkB_smul_right] at e2
      have o1 : minkB (linOf g e) (nullVec u₀) = 0 := by
        have : (a * a - 1) * minkB (linOf g e) (nullVec u₀) = 0 := by linear_combination e1
        exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 ha2)
      have o2 : minkB (linOf g e) w = 0 := by
        have : (b * b - 1) * minkB (linOf g e) w = 0 := by linear_combination e2
        exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hbb)
      have hq : minkB (linOf g e) (linOf g e) = 1 := by
        rw [lorentz.minkB_apply (linOf_mem g), F.ee]
      exact frame_pm_of_orth F hq o1 o2
  exact hnm (isMetabelianOn_of_sign F hs fun δ hδ hL _ => hinj δ hδ hL)

/-- **The linear part of `Γ` is discrete** (Barbot, l.1149 of BTZ_1): under §8's data, with a
loxodromic element, `Γ` torsion-free and not metabelian, `L(Γ)` is a discrete subgroup of
`SO₀(1, 2)`. -/
theorem discreteTopology_linearImage_of_ccAction (h : CCAction Γ S)
    (hlox : ∃ γ ∈ Γ, IsLoxodromic (linOf γ)) (hnm : ¬IsMetabelianOn Γ)
    (htf : IsTorsionFreeSubgroup Γ) : DiscreteTopology (linearImage Γ) := by
  have hinj := linOf_eq_one_imp_of_ccAction h hlox hnm
  have hne := isNonelementary_of_ccAction h hlox hnm htf
  have hΓd : DiscreteTopology Γ := Lox.ccAction_discreteTopology h
  have hA := auslanderCarriereDalbo 2
  have hU := maxUnipotentSubspace 2
  -- Barbot's maximal unipotent subspace `U` (l.3339–3362), `Γ`-invariant and timelike
  obtain ⟨U, -, hmax, hinv⟩ := exists_invariant_maxUnipotent hA hU hΓd
  have hUt := bprop_U_timelike hA hU hΓd h hne hmax
  obtain ⟨d₁, ι, -, rfl⟩ := exists_affineMinkEmbedding_of_isTimelike hUt
  have hrange : (ι.range : Set (Causal.Minkowski 2)) = Set.range ι := by
    rw [AffineMinkEmbedding.range, AffineSubspace.coe_map, AffineSubspace.top_coe, image_univ]
  have hpres : ∀ γ ∈ Γ, (fun p => γ • p) '' Set.range ι = Set.range ι := by
    intro γ hγ
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      rw [← hrange] at hp ⊢
      exact (hinv γ hγ p).2 hp
    · intro hq
      refine ⟨γ⁻¹ • q, ?_, smul_inv_smul γ q⟩
      rw [← hrange] at hq ⊢
      exact (hinv γ hγ _).1 (by rwa [smul_inv_smul])
  have hlin : ∀ γ ∈ Γ, ∀ v, linOf γ (ι.lin v) = ι.lin (Lox.restrictLin ι γ v) := fun γ hγ v =>
    (Lox.lin_restrictLin (hpres γ hγ) v).symm
  have hd₁ : d₁ ≤ 2 := Lox.le_of_affineMinkEmbedding ι
  obtain ⟨γ₀, hγ₀, hlox₀⟩ := hlox
  rcases (by omega : d₁ = 0 ∨ d₁ = 1 ∨ d₁ = 2) with rfl | rfl | rfl
  · -- `U` a timelike line: its direction is fixed by `L(γ₀)²`, impossible for a loxodromic
    exfalso
    set f := ι.lin ((1 : ℝ), 0) with hfdef
    have hf : Causal.Flat.minkQ f = -1 := ι.minkQ_lin_timeVec
    obtain ⟨r, hr⟩ : ∃ r : ℝ, linOf γ₀ f = r • f := by
      refine ⟨(Lox.restrictLin ι γ₀ ((1 : ℝ), 0)).1, ?_⟩
      rw [hfdef, hlin γ₀ hγ₀, ← map_smul]
      congr 1
      exact Prod.ext (by simp) (Subsingleton.elim _ _)
    have hr2 : r * r = 1 := by
      have := lorentz.minkQ_apply (linOf_mem γ₀) f
      rw [hr, minkQ_smul, hf] at this
      linarith
    have hfix : ((linearPart γ₀ ^ 2 : lorentz 2) : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2) f =
        f := by
      rw [← map_pow, ← linOf_eq_linearPart, linOf_pow, sq, LinearEquiv.mul_apply, hr, map_smul, hr,
        smul_smul, hr2, one_smul]
    have hlx : IsLoxodromic ((linearPart γ₀ : lorentz 2) : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2) := by
      rw [← linOf_eq_linearPart]; exact hlox₀
    have hf0 : f ≠ 0 := by intro h0; rw [h0] at hf; simp [Causal.Flat.minkQ] at hf
    have := minkQ_pos_of_fixed_pow_loxodromic hlx two_ne_zero hfix hf0
    linarith
  · -- `U` a timelike plane: `L(Γ)` maps its unit normal `e` to `± e`, and `Γ` is metabelian
    exfalso
    set e₀ : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1 with he₀
    have hdec : ∀ r : Causal.Minkowski 1, r = ((r.1 + r.2 0) / 2) • ((1 : ℝ), e₀) +
        ((r.1 - r.2 0) / 2) • ((1 : ℝ), -e₀) := by
      intro r
      refine Prod.ext ?_ ?_
      · simp; ring
      · ext i
        fin_cases i
        simp [he₀]
        ring
    have hn : Causal.Flat.minkQ (ι.lin ((1 : ℝ), e₀)) = 0 := by
      rw [ι.minkQ_lin]; simp [Causal.Flat.minkQ, he₀]
    have hn' : Causal.Flat.minkQ (ι.lin ((1 : ℝ), -e₀)) = 0 := by
      rw [ι.minkQ_lin]; simp [Causal.Flat.minkQ, he₀]
    have hnn' : minkB (ι.lin ((1 : ℝ), e₀)) (ι.lin ((1 : ℝ), -e₀)) ≠ 0 := by
      rw [ι.minkB_lin]; simp [minkB, he₀]
    obtain ⟨e, F⟩ := exists_isNullFrame2_of_null_pair hn hn' hnn'
    have hk0 : (-minkB (ι.lin ((1 : ℝ), e₀)) (ι.lin ((1 : ℝ), -e₀)))⁻¹ ≠ 0 :=
      inv_ne_zero (neg_ne_zero.2 hnn')
    have he_orth : ∀ r, minkB e (ι.lin r) = 0 := by
      intro r
      have h1 : minkB e (ι.lin ((1 : ℝ), e₀)) = 0 := by rw [minkB_comm]; exact F.ue
      have h2 : minkB e (ι.lin ((1 : ℝ), -e₀)) = 0 := by
        have := F.we
        rw [minkB_smul_left, minkB_comm (ι.lin ((1 : ℝ), -e₀)) e] at this
        exact (mul_eq_zero.1 this).resolve_left hk0
      rw [hdec r, map_add, map_smul, map_smul, minkB_add_right, minkB_smul_right, minkB_smul_right,
        h1, h2]
      ring
    have hs : ∀ γ ∈ Γ, linOf γ e = e ∨ linOf γ e = -e := by
      intro γ hγ
      have hperp : ∀ r, minkB (linOf γ e) (ι.lin r) = 0 := by
        intro r
        have : ι.lin r = linOf γ (ι.lin (Lox.restrictLin ι γ⁻¹ r)) := by
          rw [← hlin γ⁻¹ (Γ.inv_mem hγ), ← LinearEquiv.mul_apply, ← linOf_mul, mul_inv_cancel,
            linOf_one']
          rfl
        rw [this, lorentz.minkB_apply (linOf_mem γ), he_orth]
      refine frame_pm_of_orth F (by rw [lorentz.minkB_apply (linOf_mem γ), F.ee]) (hperp _) ?_
      rw [minkB_smul_right, hperp, mul_zero]
    exact hnm (isMetabelianOn_of_sign F hs fun δ hδ hL _ => hinj δ hδ hL)
  · -- `U = 𝐌³`: every element restricts, and `L_U(Γ)` is `L(Γ)` conjugated by `ι.lin`
    have hsurj : Function.Surjective ι.lin :=
      LinearMap.injective_iff_surjective.1 ι.lin_injective
    set P : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2 :=
      LinearEquiv.ofBijective ι.lin ⟨ι.lin_injective, hsurj⟩ with hP
    have hPx : ∀ x, P x = ι.lin x := fun x => rfl
    have hres : ι.RestrictsIn Γ := by
      intro γ hγ
      refine Lox.exists_restricts_of_det_eq_one (hpres γ hγ) ?_
      have hcl : ι.coproj ∘ₗ ι.lin = LinearMap.id := LinearMap.ext ι.coproj_lin
      have hdet1 : LinearMap.det ι.coproj * LinearMap.det ι.lin = 1 := by
        rw [← LinearMap.det_comp, hcl, LinearMap.det_id]
      show LinearMap.det (ι.coproj ∘ₗ
        ((γ : Causal.Minkowski 2 ≃ᵃ[ℝ] Causal.Minkowski 2).linear :
          Causal.Minkowski 2 →ₗ[ℝ] Causal.Minkowski 2) ∘ₗ ι.lin) = 1
      rw [LinearMap.det_comp, LinearMap.det_comp, (linOf_mem γ).2.2]
      linear_combination hdet1
    have hD := bprop_LU_discrete hA hU hΓd h hne ι hmax hres
    have hconj : ∀ γ ∈ Γ, ∃ g ∈ ι.restrictGroup Γ, linOf g = P.symm * linOf γ * P := by
      intro γ hγ
      obtain ⟨g, hg⟩ := hres γ hγ
      refine ⟨g, ⟨γ, hγ, hg⟩, LinearEquiv.ext fun x => P.injective ?_⟩
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.apply_symm_apply, hPx, hPx]
      exact hg.lin x
    have hmem : ∀ A : linearImage Γ,
        P.symm * ((A : lorentz 2) : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2) * P ∈ lorentz 2 := by
      rintro ⟨_, γ, hγ, rfl⟩
      obtain ⟨g, -, hg⟩ := hconj γ hγ
      rw [← linOf_eq_linearPart, ← hg]
      exact linOf_mem g
    have hmem' : ∀ A : linearImage Γ,
        (⟨_, hmem A⟩ : lorentz 2) ∈ linearImage (ι.restrictGroup Γ) := by
      rintro ⟨_, γ, hγ, rfl⟩
      obtain ⟨g, hgΓ, hg⟩ := hconj γ hγ
      refine ⟨g, hgΓ, Subtype.ext ?_⟩
      show (linearPart g : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2) = _
      rw [← linOf_eq_linearPart, hg, linOf_eq_linearPart]
    let f : linearImage Γ → linearImage (ι.restrictGroup Γ) := fun A => ⟨⟨_, hmem A⟩, hmem' A⟩
    have hfc : Continuous f := by
      have hc : Continuous fun A : linearImage Γ => linToCLM P.symm *
          linToCLM ((A : lorentz 2) : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2) * linToCLM P :=
        (continuous_const.mul (continuous_lorentz_linToCLM.comp continuous_subtype_val)).mul
          continuous_const
      refine Continuous.subtype_mk ?_ _
      refine isEmbedding_lorentz_linToCLM.isInducing.continuous_iff.2 ?_
      refine hc.congr fun A => ?_
      show _ = linToCLM (P.symm * ((A : lorentz 2) : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2) * P)
      rw [linToCLM_mul, linToCLM_mul]
    have hfi : Function.Injective f := by
      intro A B hAB
      have h1 := congrArg (fun C : linearImage (ι.restrictGroup Γ) =>
        ((C : lorentz 2) : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2)) hAB
      simp only [f] at h1
      exact Subtype.ext (Subtype.ext (mul_left_cancel (mul_right_cancel h1)))
    haveI := hD
    exact DiscreteTopology.of_continuous_injective hfc hfi

/-- **Barbot's theorem for a holonomy representation** (l.1149): if `ρ` is faithful, `ρ(G)`
satisfies §8's data, has a loxodromic element, is torsion-free and not metabelian, then
`L ∘ ρ` is faithful with discrete image. -/
theorem linearPart_comp_faithful_discrete {G : Type*} [Group G] {ρ : G →* isom 2}
    (h : CCAction ρ.range S) (hρ : Function.Injective ρ)
    (hlox : ∃ γ ∈ ρ.range, IsLoxodromic (linOf γ)) (hnm : ¬IsMetabelianOn ρ.range)
    (htf : IsTorsionFreeSubgroup ρ.range) :
    Function.Injective (linearPart.comp ρ) ∧ DiscreteTopology (linearPart.comp ρ).range := by
  have hinj := linOf_eq_one_imp_of_ccAction h hlox hnm
  refine ⟨fun a b hab => hρ ?_, ?_⟩
  · have hL : linOf (ρ a) = linOf (ρ b) := by
      rw [linOf_eq_linearPart, linOf_eq_linearPart]
      exact congrArg (fun A : lorentz 2 => (A : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2)) hab
    have : ρ a * (ρ b)⁻¹ = 1 :=
      hinj _ (ρ.range.mul_mem ⟨a, rfl⟩ (ρ.range.inv_mem ⟨b, rfl⟩))
        (by rw [linOf_mul, linOf_inv, hL, mul_inv_cancel])
    exact mul_inv_eq_one.1 this
  · rw [MonoidHom.range_comp]
    exact discreteTopology_linearImage_of_ccAction h hlox hnm htf

end Barbot

end BTZAdm

end GX
