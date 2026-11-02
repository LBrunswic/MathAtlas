import Causal.Minkowski
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
import Mathlib.LinearAlgebra.Determinant

/-!
# `Causal.Flat.Form` — the Minkowski form, the Lorentz group and `Isom(𝐌ⁿ)`

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §2.2
"Minkowski space" (`GHFspace.tex` l.453–480):

> The isometry group of the (unoriented) Minkowski space is the space of affine transformations
> with linear part in `O(1,n−1)`, but since here the consider 𝐌ⁿ as oriented and chronologically
> orientated, the term isometry will be reserved to affine transformations admitting linear parts
> in the identity component `SO₀(1,n−1)` […]. We denote by `Isom(𝐌ⁿ)` the group of isometries.

The section carries no environment, hence no ledger label; this module is the vocabulary the rest
of `Flat` is written in.

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; the library's `Minkowski d =
ℝ × EuclideanSpace ℝ (Fin d)` (`Causal/Minkowski.lean`) has `d` spatial dimensions, so Barbot's
`n` is `d + 1`. Signature `(−, +, …, +)`: `minkQ (t, x) = −t² + ‖x‖²`.

* `minkQ`, `minkB` — the form and its polar bilinear form; `minkQ_eq_minkB`.
* `le_top_iff_minkQ`, `lt_top_iff_minkQ` — the causality `minkowski d` of the ETT library (defined
  by curves) is the future cone of `minkQ`, read globally.
* `IsFutureCausal`, `IsFutureTimelike` — the closed future cone and the open future timelike cone.
* `lorentz d` — **`SO₀(1, d)`**, as the linear automorphisms preserving `minkQ`, preserving the
  future causal cone (orthochronous) and of determinant `1` (orientation).
* `isom d` — **`Isom(𝐌ⁿ)`**: affine automorphisms with linear part in `lorentz d`; `linearPart`
  is Barbot's `L`.
* `isom_le_top_iff`, `isom_lt_top_iff` — an isometry preserves `≤` and `≪` of `minkowski d`
  on all of `M` (`U = ⊤`); the statement for every open `U` is `Causal.Flat.IsomCausal`.
* The action of `isom d` on `Minkowski d`, by homeomorphisms (`ContinuousConstSMul`).
* `le_iff_of_convex`, `lt_iff_of_convex` — on a **convex** open set `V`, `≤_V` and `≪_V` are the
  cones restricted to `V` (the affine segment, `staticCurve_segment_of_convex`).

## Hypothesis checklist
* ✓ carried — linear part in the identity component: orthochronous **and** determinant `1`. The
  identity component of `O(1,d)` is cut out by these two conditions; that equality is not proved
  here and nothing downstream needs it.

## SCOPE (disclosed)
* The norm on `Minkowski d` is the product (sup) norm of `ℝ × EuclideanSpace`, as in
  `Causal/Minkowski.lean`; it is used only for topology. The Lorentzian geometry is `minkQ`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Written by the master
session of the Barbot campaign (WP-30, DEC-34) as the base the wave-1 authors build on.
-/

namespace Causal.Flat

open Set

variable {d : ℕ}

/-! ### The form -/

/-- **The Minkowski quadratic form** `−t² + ‖x‖²` on `Minkowski d`. -/
noncomputable def minkQ (v : Minkowski d) : ℝ := -v.1 ^ 2 + ‖v.2‖ ^ 2

/-- The polar form of `minkQ`: `⟨v | w⟩ = −v₀w₀ + ⟪v₁, w₁⟫`. -/
noncomputable def minkB (v w : Minkowski d) : ℝ := -(v.1 * w.1) + inner ℝ v.2 w.2

theorem minkB_comm (v w : Minkowski d) : minkB v w = minkB w v := by
  simp only [minkB, mul_comm v.1, real_inner_comm]

theorem minkQ_eq_minkB (v : Minkowski d) : minkQ v = minkB v v := by
  simp only [minkQ, minkB, real_inner_self_eq_norm_sq]; ring

@[simp] theorem minkQ_neg (v : Minkowski d) : minkQ (-v) = minkQ v := by
  simp [minkQ]

@[simp] theorem minkQ_zero : minkQ (0 : Minkowski d) = 0 := by simp [minkQ]

theorem minkQ_smul (c : ℝ) (v : Minkowski d) : minkQ (c • v) = c ^ 2 * minkQ v := by
  simp only [minkQ, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, norm_smul, Real.norm_eq_abs]
  rw [mul_pow, mul_pow, sq_abs]; ring

theorem continuous_minkQ : Continuous (minkQ (d := d)) := by
  unfold minkQ; fun_prop

/-! ### The cones -/

/-- `v` lies in the closed future cone: `v₀ ≥ 0` and `minkQ v ≤ 0`. -/
def IsFutureCausal (v : Minkowski d) : Prop := 0 ≤ v.1 ∧ minkQ v ≤ 0

/-- `v` lies in the open future timelike cone: `v₀ > 0` and `minkQ v < 0`. -/
def IsFutureTimelike (v : Minkowski d) : Prop := 0 < v.1 ∧ minkQ v < 0

theorem minkQ_nonneg_of_fst_eq_zero {v : Minkowski d} (h : v.1 = 0) : 0 ≤ minkQ v := by
  simp [minkQ, h]

/-- A causal vector with `v₀ = 0` is `0`. -/
theorem eq_zero_of_fst_eq_zero {v : Minkowski d} (h0 : v.1 = 0) (hq : minkQ v ≤ 0) : v = 0 := by
  have : ‖v.2‖ ^ 2 ≤ 0 := by simpa [minkQ, h0] using hq
  have h2 : v.2 = 0 := by
    have := pow_eq_zero_iff (n := 2) (two_ne_zero) |>.1 (le_antisymm this (sq_nonneg _))
    exact norm_eq_zero.1 this
  exact Prod.ext h0 h2

theorem minkQ_le_zero_iff {v : Minkowski d} : minkQ v ≤ 0 ↔ ‖v.2‖ ^ 2 ≤ v.1 ^ 2 := by
  unfold minkQ; constructor <;> intro h <;> linarith

theorem minkQ_lt_zero_iff {v : Minkowski d} : minkQ v < 0 ↔ ‖v.2‖ ^ 2 < v.1 ^ 2 := by
  unfold minkQ; constructor <;> intro h <;> linarith

/-- **The causality of the ETT library is the future cone of `minkQ`**, globally. -/
theorem le_top_iff_minkQ {p q : Minkowski d} :
    (minkowski d).le ⊤ p q ↔ IsFutureCausal (q - p) := by
  rw [minkowski_le_top_iff_sq, IsFutureCausal, minkQ_le_zero_iff]
  simp only [Prod.fst_sub, Prod.snd_sub, sub_nonneg]

/-- **The chronology of the ETT library is the open future timelike cone of `minkQ`**. -/
theorem lt_top_iff_minkQ {p q : Minkowski d} :
    (minkowski d).lt ⊤ p q ↔ IsFutureTimelike (q - p) := by
  rw [minkowski_lt_top_iff_sq, IsFutureTimelike, minkQ_lt_zero_iff]
  simp only [Prod.fst_sub, Prod.snd_sub, sub_pos]

/-- A timelike vector (`minkQ v < 0`) is future or past timelike. -/
theorem isFutureTimelike_or_neg {v : Minkowski d} (hv : minkQ v < 0) :
    IsFutureTimelike v ∨ IsFutureTimelike (-v) := by
  rcases lt_trichotomy v.1 0 with h | h | h
  · exact Or.inr ⟨by simpa using h, by simpa using hv⟩
  · exact absurd hv (not_lt.2 (minkQ_nonneg_of_fst_eq_zero h))
  · exact Or.inl ⟨h, hv⟩

/-! ### The Lorentz group `SO₀(1, d)` -/

/-- **`SO₀(1, d)`**: linear automorphisms of `Minkowski d` preserving `minkQ`, mapping the closed
future cone into itself, and of determinant `1`. -/
noncomputable def lorentz (d : ℕ) : Subgroup (Minkowski d ≃ₗ[ℝ] Minkowski d) where
  carrier := {A | (∀ v, minkQ (A v) = minkQ v) ∧ (∀ v, IsFutureCausal v → IsFutureCausal (A v)) ∧
    LinearMap.det (A : Minkowski d →ₗ[ℝ] Minkowski d) = 1}
  one_mem' := ⟨fun _ => rfl, fun _ h => h, by simp⟩
  mul_mem' := by
    rintro A B ⟨hA, hA', hA''⟩ ⟨hB, hB', hB''⟩
    refine ⟨fun v => ?_, fun v hv => ?_, ?_⟩
    · show minkQ (A (B v)) = minkQ v; rw [hA, hB]
    · exact hA' _ (hB' _ hv)
    · show LinearMap.det ((A : Minkowski d →ₗ[ℝ] Minkowski d) ∘ₗ (B : Minkowski d →ₗ[ℝ] _)) = 1
      rw [LinearMap.det_comp, hA'', hB'', one_mul]
  inv_mem' := by
    rintro A ⟨hA, hA', hA''⟩
    have hQ : ∀ v, minkQ (A.symm v) = minkQ v := fun v => by
      rw [← hA (A.symm v), LinearEquiv.apply_symm_apply]
    refine ⟨hQ, fun v hv => ?_, ?_⟩
    · -- `w = A⁻¹ v` is causal; were it past-directed, `A (−w) = −v` would be future too.
      set w := A.symm v
      have hw : minkQ w ≤ 0 := by rw [hQ]; exact hv.2
      by_cases h : 0 ≤ w.1
      · exact ⟨h, hw⟩
      · have hneg : IsFutureCausal (-w) := ⟨by simp; linarith, by simpa using hw⟩
        have h1 := hA' _ hneg
        rw [map_neg, show A w = v from LinearEquiv.apply_symm_apply A v] at h1
        have hv0 : v.1 = 0 := le_antisymm (by simpa using h1.1) hv.1
        have := eq_zero_of_fst_eq_zero hv0 hv.2
        exact absurd (by simp [w, this] : w.1 = 0) (by intro h'; exact h (h'.symm ▸ le_rfl))
    · have h1 : LinearEquiv.det A = 1 := Units.ext (by rw [LinearEquiv.coe_det]; exact hA'')
      rw [← LinearEquiv.coe_det, map_inv, h1, inv_one, Units.val_one]

namespace lorentz

variable {A : Minkowski d ≃ₗ[ℝ] Minkowski d}

theorem minkQ_apply (hA : A ∈ lorentz d) (v : Minkowski d) : minkQ (A v) = minkQ v := hA.1 v

theorem isFutureCausal_apply (hA : A ∈ lorentz d) {v : Minkowski d} (hv : IsFutureCausal v) :
    IsFutureCausal (A v) := hA.2.1 v hv

theorem det_eq_one (hA : A ∈ lorentz d) :
    LinearMap.det (A : Minkowski d →ₗ[ℝ] Minkowski d) = 1 := hA.2.2

theorem isFutureCausal_apply_iff (hA : A ∈ lorentz d) {v : Minkowski d} :
    IsFutureCausal (A v) ↔ IsFutureCausal v := by
  refine ⟨fun h => ?_, isFutureCausal_apply hA⟩
  have := isFutureCausal_apply ((lorentz d).inv_mem hA) h
  simpa using this

theorem isFutureTimelike_apply (hA : A ∈ lorentz d) {v : Minkowski d}
    (hv : IsFutureTimelike v) : IsFutureTimelike (A v) := by
  have hq : minkQ (A v) < 0 := by rw [minkQ_apply hA]; exact hv.2
  have hc := isFutureCausal_apply hA (v := v) ⟨hv.1.le, hv.2.le⟩
  refine ⟨lt_of_le_of_ne hc.1 fun h => ?_, hq⟩
  exact absurd hq (not_lt.2 (minkQ_nonneg_of_fst_eq_zero h.symm))

theorem isFutureTimelike_apply_iff (hA : A ∈ lorentz d) {v : Minkowski d} :
    IsFutureTimelike (A v) ↔ IsFutureTimelike v := by
  refine ⟨fun h => ?_, isFutureTimelike_apply hA⟩
  have := isFutureTimelike_apply ((lorentz d).inv_mem hA) h
  simpa using this

end lorentz

/-! ### `Isom(𝐌ⁿ)` -/

/-- **`Isom(𝐌ⁿ)`**: affine automorphisms of `Minkowski d` whose linear part lies in `SO₀(1, d)`. -/
noncomputable def isom (d : ℕ) : Subgroup (Minkowski d ≃ᵃ[ℝ] Minkowski d) :=
  (lorentz d).comap AffineEquiv.linearHom

/-- Barbot's `L`: the linear part of an isometry. -/
noncomputable def linearPart : isom d →* lorentz d :=
  (AffineEquiv.linearHom.restrict (isom d)).codRestrict (lorentz d) fun g => g.2

@[simp] theorem linearPart_apply (g : isom d) (v : Minkowski d) :
    (linearPart g : Minkowski d ≃ₗ[ℝ] Minkowski d) v = (g : Minkowski d ≃ᵃ[ℝ] Minkowski d).linear v :=
  rfl

theorem mem_isom_iff {g : Minkowski d ≃ᵃ[ℝ] Minkowski d} : g ∈ isom d ↔ g.linear ∈ lorentz d :=
  Iff.rfl

/-- The difference of two images is the linear part applied to the difference. -/
theorem isom_sub (g : Minkowski d ≃ᵃ[ℝ] Minkowski d) (p q : Minkowski d) :
    g q - g p = g.linear (q - p) := by
  rw [← vsub_eq_sub, ← vsub_eq_sub]
  exact (g.toAffineMap.linearMap_vsub q p).symm

/-- **Translations are isometries.** -/
theorem constVAdd_mem_isom (v : Minkowski d) : AffineEquiv.constVAdd ℝ (Minkowski d) v ∈ isom d := by
  rw [mem_isom_iff]
  exact (lorentz d).one_mem

noncomputable instance : MulAction (isom d) (Minkowski d) where
  smul g p := (g : Minkowski d ≃ᵃ[ℝ] Minkowski d) p
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem isom_smul_def (g : isom d) (p : Minkowski d) :
    g • p = (g : Minkowski d ≃ᵃ[ℝ] Minkowski d) p := rfl

/-- An isometry acts by a homeomorphism. -/
noncomputable def isom.toHomeomorph (g : isom d) : Minkowski d ≃ₜ Minkowski d :=
  (g : Minkowski d ≃ᵃ[ℝ] Minkowski d).toHomeomorphOfFiniteDimensional

@[simp] theorem isom.coe_toHomeomorph (g : isom d) :
    ⇑(isom.toHomeomorph g) = fun p => g • p := rfl

instance : ContinuousConstSMul (isom d) (Minkowski d) where
  continuous_const_smul g := (isom.toHomeomorph g).continuous

/-! ### Isometries preserve the causal order of `𝐌ⁿ` -/

/-- An isometry preserves `≤` of `minkowski d` on all of `M`. -/
theorem isom_le_top_iff (g : isom d) {p q : Minkowski d} :
    (minkowski d).le ⊤ (g • p) (g • q) ↔ (minkowski d).le ⊤ p q := by
  rw [le_top_iff_minkQ, le_top_iff_minkQ, isom_smul_def, isom_smul_def, isom_sub]
  exact lorentz.isFutureCausal_apply_iff g.2

/-- An isometry preserves `≪` of `minkowski d` on all of `M`. -/
theorem isom_lt_top_iff (g : isom d) {p q : Minkowski d} :
    (minkowski d).lt ⊤ (g • p) (g • q) ↔ (minkowski d).lt ⊤ p q := by
  rw [lt_top_iff_minkQ, lt_top_iff_minkQ, isom_smul_def, isom_smul_def, isom_sub]
  exact lorentz.isFutureTimelike_apply_iff g.2

/-- An isometry preserves `minkQ` of differences. -/
theorem isom_minkQ_sub (g : isom d) (p q : Minkowski d) :
    minkQ (g • q - g • p) = minkQ (q - p) := by
  rw [isom_smul_def, isom_smul_def, isom_sub]; exact lorentz.minkQ_apply g.2 _

/-! ### On a convex open set, the relations are the cones -/

/-- The affine segment from `p` to `q` is the graph over time of an `L`-Lipschitz map, and it lies
in any convex set containing `p` and `q`. -/
theorem staticCurve_segment_of_convex {V : Set (Minkowski d)} (hV : Convex ℝ V)
    {p q : Minkowski d} (hp : p ∈ V) (hq : q ∈ V) (hpq : p.1 < q.1) {L : ℝ}
    (hL : ‖q.2 - p.2‖ ≤ L * (q.1 - p.1)) :
    ∃ γ : ℝ → EuclideanSpace ℝ (Fin d), γ p.1 = p.2 ∧ γ q.1 = q.2 ∧
      StaticCurve L V γ p.1 q.1 := by
  have hΔ : 0 < q.1 - p.1 := sub_pos.2 hpq
  set γ : ℝ → EuclideanSpace ℝ (Fin d) := fun τ => p.2 + ((τ - p.1) / (q.1 - p.1)) • (q.2 - p.2)
  refine ⟨γ, by simp [γ], ?_, ⟨fun τ _ τ' _ => ?_, fun τ hτ => ?_⟩⟩
  · simp only [γ, div_self hΔ.ne', one_smul, add_sub_cancel]
  · rw [dist_eq_norm]
    simp only [γ, add_sub_add_left_eq_sub, ← sub_smul, norm_smul, Real.norm_eq_abs]
    rw [show (τ - p.1) / (q.1 - p.1) - (τ' - p.1) / (q.1 - p.1) = (τ - τ') / (q.1 - p.1) by ring,
      abs_div, abs_of_pos hΔ, div_mul_eq_mul_div, div_le_iff₀ hΔ]
    calc |τ - τ'| * ‖q.2 - p.2‖ ≤ |τ - τ'| * (L * (q.1 - p.1)) :=
          mul_le_mul_of_nonneg_left hL (abs_nonneg _)
      _ = L * |τ - τ'| * (q.1 - p.1) := by ring
  · have hs : (τ - p.1) / (q.1 - p.1) ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg (by linarith [hτ.1]) hΔ.le, (div_le_one hΔ).2 (by linarith [hτ.2])⟩
    have hmem := hV.add_smul_sub_mem hp hq hs
    convert hmem using 1
    refine Prod.ext ?_ rfl
    simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
    field_simp
    ring

/-- **On a convex open set `V`, `≤_V` is the future cone**: `p ≤_V q` iff `p, q ∈ V` and
`q − p` is future causal. -/
theorem le_iff_of_convex {V : TopologicalSpace.Opens (Minkowski d)}
    (hV : Convex ℝ (V : Set (Minkowski d))) {p q : Minkowski d} :
    (minkowski d).le V p q ↔ p ∈ V ∧ q ∈ V ∧ (minkowski d).le ⊤ p q := by
  refine ⟨fun h => ⟨(minkowski d).le_mem_left h, (minkowski d).le_mem_right h,
    (minkowski d).le_mono le_top h⟩, fun ⟨hp, hq, h⟩ => ?_⟩
  have hd := minkowski_le_top_iff.1 h
  have h1 : p.1 ≤ q.1 := (norm_nonneg _).trans hd |> sub_nonneg.1
  rcases h1.eq_or_lt with he | hlt
  · have : q.2 = p.2 := by
      rw [he, sub_self] at hd; exact (sub_eq_zero.1 (norm_le_zero_iff.1 hd))
    have hpq : p = q := Prod.ext he this.symm
    subst hpq
    exact (minkowski d).le_refl hp
  obtain ⟨γ, h0, h1', hγ⟩ := staticCurve_segment_of_convex hV hp hq hlt (L := 1) (by simpa using hd)
  exact ⟨hlt.le, γ, h0, h1', hγ⟩

/-- **On a convex open set `V`, `≪_V` is the open future timelike cone.** -/
theorem lt_iff_of_convex {V : TopologicalSpace.Opens (Minkowski d)}
    (hV : Convex ℝ (V : Set (Minkowski d))) {p q : Minkowski d} :
    (minkowski d).lt V p q ↔ p ∈ V ∧ q ∈ V ∧ (minkowski d).lt ⊤ p q := by
  refine ⟨fun h => ⟨(minkowski d).lt_mem_left h, (minkowski d).lt_mem_right h,
    (minkowski d).lt_mono le_top h⟩, fun ⟨hp, hq, h⟩ => ?_⟩
  have hd := minkowski_lt_top_iff.1 h
  have hlt : p.1 < q.1 := sub_pos.1 ((norm_nonneg _).trans_lt hd)
  have hΔ : 0 < q.1 - p.1 := sub_pos.2 hlt
  obtain ⟨γ, h0, h1', hγ⟩ := staticCurve_segment_of_convex hV hp hq hlt
    (L := ‖q.2 - p.2‖ / (q.1 - p.1)) (by rw [div_mul_cancel₀ _ hΔ.ne'])
  exact ⟨hlt, _, (div_lt_one hΔ).2 hd, γ, h0, h1', hγ⟩

end Causal.Flat
