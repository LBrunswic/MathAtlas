import Causal.Flat.Develop
import Causal.Flat.Externals
import Causal.Flat.Bieberbach
import Causal.Flat.TwistedProduct
import Causal.Flat.Examples
import Causal.Flat.CauchyComplete
import Causal.Flat.Nonlox.BTrivial
import Causal.Flat.Nonlox.UnipotentFrame
import Causal.Flat.Nonlox.UnipotentRestriction
import Causal.Flat.Nonlox.NullSlices

/-!
# `Causal.Flat.Nonlox.UnipotentUpToFrame` — [9.U] holds up to a null frame change: proved

T. Barbot, *Globally hyperbolic flat space-times*, §9, the purely unipotent case `[9.U]`
(`GHFspace.tex` l.2873–2938 of `papers/barbot/legacy/labeled/`), served for
`Causal.Flat.exists_unipotent_restriction_up_to_frame` and hence
`Causal.Flat.nonloxodromic_parabolic`. `[9.U]` is a step of §9.2 (`prabb`), not a numbered
statement: it is cited UNMARKED. Barbot's `𝐌ⁿ` is `Minkowski (d + 1)` (`n = d + 2`, `z ∈ ℝᵈ`).

* `exists_unipotentRestriction_upToFrame` — under the hypotheses of the dispatched
  `exists_unipotent_restriction` (`CCAction G Σ`, `L(G)` fixing `v₀ = ofNull 1 0 0`, `b ≡ 0`, a
  parabolic element) and `BieberbachI ℝᵈ` (DEC-36), `UnipotentRestrictionConclusion d (ψGψ⁻¹) (ψΣ)`
  for the null frame change `ψ = ψ_w` (`uftPsi`: `(x, z, y) ↦ (x + ⟨w|z⟩ − (y/2)|w|², z − y w, y)`,
  fixing `v₀` and `y`). No `sorry`; axioms `propext`, `Classical.choice`, `Quot.sound`.
  The frame-free form is false (`not_unipotentRestrictionStatement`): the frame is necessary.

> According to point (3) above, `Γ` acts freely and properly discontinuously on `P̄₀ × {0}` …
> According to Bieberbach's theorem, up to finite index, `Γ` acts effectively by translations on
> some affine subspace `𝒰̄₀ × {0} ⊂ P̄₀ × {0}`. … But this observation works for any `t ∈ I`: there
> is some affine subspace `𝒰̄_t × {t} ⊂ P̄₀ × {t}` on which the action of `α(γ)` has the
> expression `α(γ)(z,t) = (z + u(γ) + tv(γ), t)` … Hence, every `v(γ)` belongs to `𝒰̄₀`:
> `𝒰̄_t` does not depend on `t`. (l.2874–2892)

> Since the action of `Γ` on `P̄₀ × {0}` is effective, `u : Γ → P̄₀` is injective. … there is a
> linear map `T` from `E` into `P̄₀` such that `α(u)(z,y) = (z + u + yT(u), y)`. Moreover, `Γ` is
> isomorphic to `ℤᵏ`. In particular, it is abelian … It follows, for every `u`, `u'` in `E`:
> `⟨u | T(u')⟩ = ⟨u' | T(u)⟩` (l.2909–2924)

**The proof** (the correction of l.2881–2892). Bieberbach is applied on TWO slices `y₀ ≠ t₁` of
`I = π₁(S̃)` (`uft_bieberbach`, discreteness from `uft_isDiscreteEucl`): finite-index `K₀`, `K₁`,
points `p₀ ∈ 𝒰̄_{y₀}`, `p₁ ∈ 𝒰̄_{t₁}`. On `K = K₀ ∩ K₁` (abelian, `uft_comm`) let `W` be the
common fixed space of the rotations `R(γ)`; both directions lie in `W`, so
`e_i(γ) = λ_{t_i}(γ) p_i − p_i ∈ W` and, for `w = (p₁ − p₀)/(t₁ − y₀)`,
`v(γ) + R(γ) w − w = (e₁ − e₀)/(t₁ − y₀) ∈ W`: after `ψ_w` (`uft_conj_nf`) every `v` lies in `W`,
which is Barbot's "`v(γ) ∈ 𝒰̄₀`" in the frame where it is true. With `z₀ = p₀ − y₀ w` and
`J : ℝ^{d₁} ≅ W`, `ι (x, z, y) = (x, z₀ + J z, y + y₀)` (`uftIota`) is preserved and each `γ`
restricts to `A(a, b, c)` (`uft_restricts`); `b` is injective (freeness, `uft_eq_one_of_fixed`),
its image `L` is ball-finite (discreteness at `y₀`), and `T`, `ℓ` are the linear extensions of
`b ↦ a`, `b ↦ c + ⟨b|a⟩/2` from the lattice `L` (`uft_exists_linear_extension`, `uft_lattice`).
The heights `]ylo, yhi[` come from `Flat/Nonlox/NullSlices`.

## Hypothesis checklist
| paper hypothesis | here |
|---|---|
| `Γ` free, properly discontinuous on `S̃` complete (CC′) | ✓ carried (`CCAction`) |
| `L(Γ)` fixes `v₀`; `b ≡ 0` ([9.b], l.2867) | ✓ carried |
| some element parabolic (§9.2) | ✓ carried |
| Bieberbach's theorem | ✓ carried as `BieberbachI ℝᵈ` (DEC-36 external, as dispatched) |
| `0 ∈ I` (l.2873) | ✓ by the shift `y₀ ∈ I` of `ι` |
| "`𝒰̄₀` maximal", "`𝒰̄_t` independent of `t`" (l.2889–2892) | not used (false in a fixed frame) |

## SCOPE (disclosed)
* **Finding (l.2881–2892, repaired).** The conclusion needs a frame `ψ`; the one used is the null
  rotation `ψ_w` fixing `v₀` and preserving `y`, `w` read off two Bieberbach subspaces (a
  cocycle-is-a-coboundary step that Barbot's maximality argument was meant to supply). Barbot's
  `𝒰̄₀` is replaced by `W`, the common fixed space of the rotations of `K`; no maximality is used.
* `d₁ = dim W` may exceed `dim span L` (the directions of `W` with no translation are kept).
* Bieberbach's theorem remains the external `BieberbachI` (unchanged from the dispatched form).
* `set_option maxHeartbeats 1600000` on `exists_unipotentRestriction_upToFrame` (one long assembly).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
WP-34c-Nonloxodromic (2026-11-01), closing the one `sorry` of `Flat/Nonloxodromic`.
-/

namespace Causal.Flat.Nonlox

open Causal.Flat Set Filter Topology Module Submodule
open scoped RealInnerProductSpace Pointwise

variable {d : ℕ}

/-! ### The normal form of `Stab(v₀) ∩ {b = 0}` -/

/-- `γ` acts in null coordinates by `(R, u, v, μ)` with `b = 0` (l.2701–2713). -/
def UftNF (γ : isom (d + 1)) (R : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (u v : EuclideanSpace ℝ (Fin d)) (μ : ℝ) : Prop :=
  ∀ x y z, γ • ofNull x y z = ofNull (x - ⟪v, R z⟫ - y / 2 * ‖v‖ ^ 2 + μ) y (R z + y • v + u)

theorem uft_exists_nf {γ : isom (d + 1)} (hfix : linOf γ (ofNull 1 0 0) = ofNull 1 0 0)
    (hb : ∀ p : Minkowski (d + 1), nullY (γ • p) = nullY p) : ∃ R u v μ, UftNF γ R u v μ := by
  obtain ⟨g, hg⟩ := BTrivialAux.exists_nolParam (d := d) (γ := γ) hfix
  have hb0 : g.b = 0 := by
    have h1 := hb (ofNull 0 0 0)
    have h2 := hg (0, 0, 0)
    simp only [BTrivialAux.nolToMink] at h2
    rw [h2, nullY_ofNull, nullY_ofNull] at h1
    simpa [BTrivialAux.NolParam.act] using h1
  refine ⟨g.R, g.u, g.v, g.μ, fun x y z => ?_⟩
  have := hg (x, z, y)
  simp only [BTrivialAux.nolToMink, BTrivialAux.NolParam.act, hb0, add_zero] at this
  exact this

/-- The chosen normal-form data. -/
noncomputable def uftData (γ : isom (d + 1)) :
    (EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) ×
      EuclideanSpace ℝ (Fin d) × ℝ :=
  open Classical in
  if h : ∃ p : (EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) ×
      EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) × ℝ, UftNF γ p.1 p.2.1 p.2.2.1 p.2.2.2
  then Classical.choose h else (LinearIsometryEquiv.refl ℝ _, 0, 0, 0)

/-- The hypotheses of [9.U] on the linear parts: `L(G)` fixes `v₀` and `G` preserves `y`. -/
def UftHyp (G : Subgroup (isom (d + 1))) : Prop :=
  (∀ γ ∈ G, linOf γ (ofNull 1 0 0) = ofNull 1 0 0) ∧
    ∀ γ ∈ G, ∀ p : Minkowski (d + 1), nullY (γ • p) = nullY p

theorem uft_nf {G : Subgroup (isom (d + 1))} (h : UftHyp G) {γ : isom (d + 1)} (hγ : γ ∈ G) :
    UftNF γ (uftData γ).1 (uftData γ).2.1 (uftData γ).2.2.1 (uftData γ).2.2.2 := by
  obtain ⟨R, u, v, μ, hn⟩ := uft_exists_nf (h.1 γ hγ) (h.2 γ hγ)
  have hex : ∃ p : (EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) ×
      EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) × ℝ,
      UftNF γ p.1 p.2.1 p.2.2.1 p.2.2.2 := ⟨(R, u, v, μ), hn⟩
  rw [uftData, dif_pos hex]
  exact Classical.choose_spec hex

theorem UftNF.nullZ {γ : isom (d + 1)} {R u v μ} (h : UftNF γ R u v μ) (x y : ℝ)
    (z : EuclideanSpace ℝ (Fin d)) : nullZ (γ • ofNull x y z) = R z + y • v + u := by
  rw [h, nullZ_ofNull]

theorem UftNF.nullY {γ : isom (d + 1)} {R u v μ} (h : UftNF γ R u v μ) (x y : ℝ)
    (z : EuclideanSpace ℝ (Fin d)) : Causal.Flat.nullY (γ • ofNull x y z) = y := by
  rw [h, nullY_ofNull]

theorem UftNF.smul_eq {γ : isom (d + 1)} {R u v μ} (h : UftNF γ R u v μ) (x y : ℝ)
    (z : EuclideanSpace ℝ (Fin d)) :
    γ • ofNull x y z = ofNull (nullX (γ • ofNull x y z)) y (R z + y • v + u) := by
  conv_lhs => rw [← nsl_ofNull_null (γ • ofNull x y z)]
  rw [h.nullY, h.nullZ]

/-! ### The slices `λ_t(γ)` (l.2694–2700) -/

/-- **`λ_t(γ)`**: the euclidean isometry `z ↦ R z + u + t v` of the slice `{y = t}`. -/
noncomputable def uftSlice (t : ℝ) (γ : isom (d + 1)) :
    EuclideanSpace ℝ (Fin d) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin d) :=
  (uftData γ).1.toAffineIsometryEquiv.trans
    (AffineIsometryEquiv.constVAdd ℝ (EuclideanSpace ℝ (Fin d)) (t • (uftData γ).2.2.1 + (uftData γ).2.1))

theorem uftSlice_apply (t : ℝ) (γ : isom (d + 1)) (z : EuclideanSpace ℝ (Fin d)) :
    uftSlice t γ z = (uftData γ).1 z + t • (uftData γ).2.2.1 + (uftData γ).2.1 := by
  simp only [uftSlice, AffineIsometryEquiv.coe_trans, Function.comp_apply,
    AffineIsometryEquiv.coe_constVAdd, LinearIsometryEquiv.coe_toAffineIsometryEquiv, vadd_eq_add]
  abel

theorem uftSlice_eq_nullZ {G : Subgroup (isom (d + 1))} (h : UftHyp G) {γ : isom (d + 1)}
    (hγ : γ ∈ G) (t x : ℝ) (z : EuclideanSpace ℝ (Fin d)) :
    uftSlice t γ z = nullZ (γ • ofNull x t z) := by
  rw [uftSlice_apply, (uft_nf h hγ).nullZ]

theorem uft_smul_ofNull {G : Subgroup (isom (d + 1))} (h : UftHyp G) {γ : isom (d + 1)}
    (hγ : γ ∈ G) (t x : ℝ) (z : EuclideanSpace ℝ (Fin d)) :
    γ • ofNull x t z = ofNull (nullX (γ • ofNull x t z)) t (uftSlice t γ z) := by
  rw [uftSlice_apply]; exact (uft_nf h hγ).smul_eq x t z

/-- **`λ_t : G → Isom(ℝᵈ)` is a morphism** (`b ≡ 0`: the slices are preserved). -/
noncomputable def uftHom {G : Subgroup (isom (d + 1))} (h : UftHyp G) (t : ℝ) :
    G →* (EuclideanSpace ℝ (Fin d) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin d)) where
  toFun γ := uftSlice t γ
  map_one' := by
    refine AffineIsometryEquiv.ext fun z => ?_
    show uftSlice t 1 z = z
    rw [uftSlice_eq_nullZ h G.one_mem t 0 z]
    simp [nullZ_ofNull]
  map_mul' γ γ' := by
    refine AffineIsometryEquiv.ext fun z => ?_
    show uftSlice t (γ * γ' : isom (d + 1)) z = uftSlice t γ (uftSlice t γ' z)
    rw [uftSlice_eq_nullZ h (G.mul_mem γ.2 γ'.2) t 0 z, mul_smul,
      uft_smul_ofNull h γ'.2 t 0 z, ← uftSlice_eq_nullZ h γ.2]

theorem uftHom_apply {G : Subgroup (isom (d + 1))} (h : UftHyp G) (t : ℝ) (γ : G)
    (z : EuclideanSpace ℝ (Fin d)) : uftHom h t γ z = uftSlice t γ z := rfl

/-- **A slice isometry with a fixed point comes from the identity** (freeness on `S̃`, and one
point of `S̃` per `v₀`-line). -/
theorem uft_eq_one_of_fixed {G : Subgroup (isom (d + 1))} {St : Set (Minkowski (d + 1))}
    (hcc : CCAction G St) (h : UftHyp G) {t : ℝ} (ht : t ∈ nullY '' St) {γ : isom (d + 1)}
    (hγ : γ ∈ G) {z : EuclideanSpace ℝ (Fin d)} (hz : uftSlice t γ z = z) : γ = 1 := by
  set σ := ofNull (nslX St t z) t z
  have hσ : σ ∈ St := nslX_mem hcc.cc ht z
  have h1 : γ • σ ∈ St := hcc.smul_mem hγ hσ
  have h2 : γ • σ = σ := by
    refine nsl_eq_of_nullY_nullZ hcc.cc.entire.acausal h1 hσ ?_ ?_
    · rw [(uft_nf h hγ).nullY, nullY_ofNull]
    · rw [← uftSlice_eq_nullZ h hγ, hz, nullZ_ofNull]
  by_contra hne
  exact hcc.free γ hγ hne σ hσ h2

theorem uftHom_injective {G : Subgroup (isom (d + 1))} {St : Set (Minkowski (d + 1))}
    (hcc : CCAction G St) (h : UftHyp G) {t : ℝ} (ht : t ∈ nullY '' St) :
    Function.Injective (uftHom h t) := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  have := uft_eq_one_of_fixed hcc h ht γ.2 (z := 0) (by
    show uftHom h t γ 0 = 0
    rw [hγ]; rfl)
  exact Subtype.ext this

/-- **Point (3)** (l.2660–2663): for `t ∈ π₁(S̃)`, `λ_t(Γ)` is a discrete group of isometries of
`ℝᵈ` (finite in every ball), from the properness of `Γ` on `S̃` and the compactness of the section
of `S̃` over a ball (`isCompact_nslSection`). -/
theorem uft_isDiscreteEucl {G : Subgroup (isom (d + 1))} {St : Set (Minkowski (d + 1))}
    (hcc : CCAction G St) (h : UftHyp G) {t : ℝ} (ht : t ∈ nullY '' St) :
    IsDiscreteEucl (uftHom h t).range := by
  intro x R
  obtain ⟨hKc, hKS⟩ := isCompact_nslSection hcc.cc ht (isCompact_closedBall x R)
  have hfin := hcc.proper _ hKS hKc
  classical
  let F : isom (d + 1) → (EuclideanSpace ℝ (Fin d) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin d)) :=
    fun γ => if hγ : γ ∈ G then uftHom h t ⟨γ, hγ⟩ else 1
  refine (hfin.image F).subset ?_
  rintro f ⟨⟨γ, rfl⟩, hdist⟩
  have hR : 0 ≤ R := le_trans dist_nonneg hdist
  have hσ := nslX_mem hcc.cc ht x
  have h1 := hcc.smul_mem γ.2 hσ
  have heq : (γ : isom (d + 1)) • nslSection St t x = nslSection St t (uftSlice t γ x) := by
    show (γ : isom (d + 1)) • ofNull (nslX St t x) t x = ofNull (nslX St t (uftSlice t γ x)) t (uftSlice t γ x)
    rw [uft_smul_ofNull h γ.2] at h1 ⊢
    rw [nslX_unique hcc.cc h1]
  have hx : x ∈ Metric.closedBall x R := Metric.mem_closedBall_self hR
  have hy : uftSlice t γ x ∈ Metric.closedBall x R := Metric.mem_closedBall.2 hdist
  have hm1 : nslSection St t (uftSlice t γ x) ∈ (γ : isom (d + 1)) • (nslSection St t '' Metric.closedBall x R) := by
    rw [← heq]; exact Set.smul_mem_smul_set (Set.mem_image_of_mem _ hx)
  have hm2 : nslSection St t (uftSlice t γ x) ∈ nslSection St t '' Metric.closedBall x R :=
    Set.mem_image_of_mem _ hy
  refine ⟨γ, ⟨γ.2, _, hm1, hm2⟩, ?_⟩
  · show F γ = uftHom h t γ
    simp only [F, dif_pos γ.2]

/-! ### Bieberbach on a slice, pulled back to `Γ` -/

theorem uft_bieberbach (hB : BieberbachI (EuclideanSpace ℝ (Fin d)))
    {G : Subgroup (isom (d + 1))} {St : Set (Minkowski (d + 1))}
    (hcc : CCAction G St) (h : UftHyp G) {t : ℝ} (ht : t ∈ nullY '' St) :
    ∃ K : Subgroup G, K.index ≠ 0 ∧ ∃ U : AffineSubspace ℝ (EuclideanSpace ℝ (Fin d)),
      ∃ p ∈ U, (∀ γ ∈ K, ∃ c ∈ U.direction, ∀ q ∈ U, uftSlice t (γ : isom (d + 1)) q = c +ᵥ q) ∧
        (∀ γ ∈ K, (∀ q ∈ U, uftSlice t (γ : isom (d + 1)) q = q) → γ = 1) := by
  obtain ⟨U, ⟨p, hp⟩, -, Γ', hle, hfi, htr, heff⟩ := hB _ (uft_isDiscreteEucl hcc h ht)
  refine ⟨Γ'.comap (uftHom h t), ?_, U, p, hp, fun γ hγ => htr _ hγ, fun γ hγ hfix => ?_⟩
  · have e : Γ'.comap (uftHom h t) =
        (Γ'.subgroupOf (uftHom h t).range).comap (uftHom h t).rangeRestrict := by
      ext γ; simp [Subgroup.mem_subgroupOf]
    rw [e, Subgroup.index_comap_of_surjective _ (uftHom h t).rangeRestrict_surjective]
    exact hfi.index_ne_zero
  · have h1 : uftHom h t γ = 1 := heff _ hγ hfix
    exact uftHom_injective hcc h ht (h1.trans (map_one _).symm)

/-- On a subspace where `λ_t(γ)` translates, its rotation `R(γ)` is the identity. -/
theorem uft_rot_fix_of_translation {t : ℝ} {γ : isom (d + 1)}
    {U : AffineSubspace ℝ (EuclideanSpace ℝ (Fin d))} {c : EuclideanSpace ℝ (Fin d)}
    (hc : ∀ q ∈ U, uftSlice t γ q = c +ᵥ q) {p : EuclideanSpace ℝ (Fin d)} (hp : p ∈ U)
    {e : EuclideanSpace ℝ (Fin d)} (he : e ∈ U.direction) : (uftData γ).1 e = e := by
  have h1 := hc p hp
  have h2 := hc (e +ᵥ p) (AffineSubspace.vadd_mem_of_mem_direction he hp)
  rw [uftSlice_apply] at h1 h2
  simp only [vadd_eq_add] at h1 h2
  rw [map_add] at h2
  linear_combination (norm := module) h2 - h1

/-- **`Γ'` is abelian** (it acts effectively by translations on `U`). -/
theorem uft_comm {G : Subgroup (isom (d + 1))} (h : UftHyp G) {t : ℝ} {K : Subgroup G}
    {U : AffineSubspace ℝ (EuclideanSpace ℝ (Fin d))}
    (htr : ∀ γ ∈ K, ∃ c ∈ U.direction, ∀ q ∈ U, uftSlice t (γ : isom (d + 1)) q = c +ᵥ q)
    (heff : ∀ γ ∈ K, (∀ q ∈ U, uftSlice t (γ : isom (d + 1)) q = q) → γ = 1) :
    ∀ γ ∈ K, ∀ γ' ∈ K, γ * γ' = γ' * γ := by
  have hPmul : ∀ (γ γ' : G) (c c' : EuclideanSpace ℝ (Fin d)), c' ∈ U.direction →
      (∀ q ∈ U, uftHom h t γ q = c +ᵥ q) → (∀ q ∈ U, uftHom h t γ' q = c' +ᵥ q) →
        ∀ q ∈ U, uftHom h t (γ * γ') q = (c + c') +ᵥ q := by
    intro γ γ' c c' hc' hP hP' q hq
    rw [map_mul, AffineIsometryEquiv.coe_mul, Function.comp_apply, hP' q hq,
      hP _ (AffineSubspace.vadd_mem_of_mem_direction hc' hq), vadd_vadd]
  have hPinv : ∀ (γ : G) (c : EuclideanSpace ℝ (Fin d)), c ∈ U.direction →
      (∀ q ∈ U, uftHom h t γ q = c +ᵥ q) → ∀ q ∈ U, uftHom h t γ⁻¹ q = -c +ᵥ q := by
    intro γ c hc hP q hq
    have h1 : uftHom h t γ (uftHom h t γ⁻¹ q) = q := by
      rw [← Function.comp_apply (f := uftHom h t γ), ← AffineIsometryEquiv.coe_mul, ← map_mul,
        mul_inv_cancel, map_one]; rfl
    have h2 : uftHom h t γ (-c +ᵥ q) = q := by
      rw [hP _ (AffineSubspace.vadd_mem_of_mem_direction (U.direction.neg_mem hc) hq), vadd_vadd,
        add_neg_cancel, zero_vadd]
    exact (uftHom h t γ).injective (h1.trans h2.symm)
  intro γ hγ γ' hγ'
  obtain ⟨c, hc, hcq⟩ := htr γ hγ
  obtain ⟨c', hc', hcq'⟩ := htr γ' hγ'
  have h4 := hPmul _ _ _ _ (U.direction.neg_mem hc')
      (hPmul _ _ _ _ (U.direction.neg_mem hc) (hPmul _ _ _ _ hc' hcq hcq') (hPinv _ _ hc hcq))
      (hPinv _ _ hc' hcq')
  have hcomm : γ * γ' * γ⁻¹ * γ'⁻¹ = 1 := by
    refine heff _ (K.mul_mem (K.mul_mem (K.mul_mem hγ hγ') (K.inv_mem hγ)) (K.inv_mem hγ'))
      fun q hq => ?_
    have h5 : uftHom h t (γ * γ' * γ⁻¹ * γ'⁻¹) q = q := by
      rw [h4 q hq, show c + c' + -c + -c' = 0 by abel, zero_vadd]
    exact h5
  calc γ * γ' = (γ * γ' * γ⁻¹ * γ'⁻¹) * (γ' * γ) := by group
    _ = γ' * γ := by rw [hcomm, one_mul]

/-! ### The frame change `ψ` (Rem 9.2, corrected) and the conjugated normal form -/

theorem uft_det_basisFun (n : ℕ) :
    LinearMap.det ((EuclideanSpace.basisFun (Fin n) ℝ).repr.toLinearEquiv :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) = 1 := by
  have : ((EuclideanSpace.basisFun (Fin n) ℝ).repr.toLinearEquiv :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) = LinearMap.id :=
    LinearMap.ext fun v => by ext i; rfl
  rw [this, LinearMap.det_id]

theorem uft_basisFun_repr {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) :
    (EuclideanSpace.basisFun (Fin n) ℝ).repr v = v := by ext i; rfl

/-- **The null frame change `ψ_w`**: `(x, z, y) ↦ (x + ⟨w | z⟩ − (y/2)|w|², z − y w, y)`. -/
noncomputable def uftPsi (w : EuclideanSpace ℝ (Fin d)) : isom (d + 1) :=
  ufrPsi (EuclideanSpace.basisFun (Fin d) ℝ) (uft_det_basisFun d) w

theorem uftPsi_smul (w : EuclideanSpace ℝ (Fin d)) (x y : ℝ) (z : EuclideanSpace ℝ (Fin d)) :
    uftPsi w • ofNull x y z = ofNull (x + ⟪w, z⟫ - y / 2 * ‖w‖ ^ 2) y (z - y • w) := by
  rw [uftPsi, ufrPsi_smul, uft_basisFun_repr]

theorem uftPsi_inv_smul (w : EuclideanSpace ℝ (Fin d)) (x y : ℝ) (z : EuclideanSpace ℝ (Fin d)) :
    (uftPsi w)⁻¹ • ofNull x y z = ofNull (x - ⟪w, z⟫ - y / 2 * ‖w‖ ^ 2) y (z + y • w) := by
  rw [inv_smul_eq_iff, uftPsi_smul]
  congr 1
  · rw [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]; ring
  · abel

theorem uftPsi_nullY (w : EuclideanSpace ℝ (Fin d)) (p : Minkowski (d + 1)) :
    nullY (uftPsi w • p) = nullY p := by
  rw [← nsl_ofNull_null p, uftPsi_smul, nullY_ofNull, nullY_ofNull]

/-- **Conjugation by the frame change** (Rem 9.2 corrected, the cocycle `v ↦ v − (id − R) w`):
`ψ_w (R, u, v, μ) ψ_w⁻¹ = (R, u, v + R w − w, μ + ⟨w | u⟩)`. -/
theorem uft_conj_nf {γ : isom (d + 1)} {R : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)}
    {u v : EuclideanSpace ℝ (Fin d)} {μ : ℝ} (hnf : UftNF γ R u v μ) (w : EuclideanSpace ℝ (Fin d)) :
    UftNF (uftPsi w * γ * (uftPsi w)⁻¹) R u (v + R w - w) (μ + ⟪w, u⟫) := by
  intro x y z
  rw [mul_smul, mul_smul, uftPsi_inv_smul, hnf, uftPsi_smul]
  congr 1
  · simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_sub_left,
      inner_sub_right, inner_smul_right, LinearIsometryEquiv.inner_map_map,
      ← real_inner_self_eq_norm_sq]
    rw [real_inner_comm v (R w), real_inner_comm w v, real_inner_comm w (R w)]
    ring
  · simp only [map_add, map_smul]; module

/-! ### The unipotent elements `A(a, b, c)` of `𝐌^{d₁+2}` -/

/-- `g ↦ (b, a, c)` read off: `b = z(g • 0)`, `a = z(g • vₙ) − b`, `c = x(g • 0)`. -/
noncomputable def uftβ {d₁ : ℕ} (g : isom (d₁ + 1)) : EuclideanSpace ℝ (Fin d₁) :=
  nullZ (g • ofNull 0 0 (0 : EuclideanSpace ℝ (Fin d₁)))

noncomputable def uftα {d₁ : ℕ} (g : isom (d₁ + 1)) : EuclideanSpace ℝ (Fin d₁) :=
  nullZ (g • ofNull 0 1 (0 : EuclideanSpace ℝ (Fin d₁))) -
    nullZ (g • ofNull 0 0 (0 : EuclideanSpace ℝ (Fin d₁)))

noncomputable def uftκ {d₁ : ℕ} (g : isom (d₁ + 1)) : ℝ :=
  nullX (g • ofNull 0 0 (0 : EuclideanSpace ℝ (Fin d₁)))

theorem UftNF.params {d₁ : ℕ} {g : isom (d₁ + 1)} {a b : EuclideanSpace ℝ (Fin d₁)} {c : ℝ}
    (h : UftNF g (LinearIsometryEquiv.refl ℝ _) b a c) : uftβ g = b ∧ uftα g = a ∧ uftκ g = c := by
  refine ⟨?_, ?_, ?_⟩
  · rw [uftβ, h.nullZ]; simp
  · rw [uftα, h.nullZ, h.nullZ]; simp
  · rw [uftκ, h, nullX_ofNull]; simp

theorem UftNF.mul_unip {d₁ : ℕ} {g g' : isom (d₁ + 1)} {a b a' b' : EuclideanSpace ℝ (Fin d₁)}
    {c c' : ℝ} (h : UftNF g (LinearIsometryEquiv.refl ℝ _) b a c)
    (h' : UftNF g' (LinearIsometryEquiv.refl ℝ _) b' a' c') :
    UftNF (g * g') (LinearIsometryEquiv.refl ℝ _) (b + b') (a + a') (c + c' - ⟪a, b'⟫) := by
  intro x y z
  rw [mul_smul, h', h]
  simp only [LinearIsometryEquiv.coe_refl, id]
  congr 1
  · simp only [inner_add_left, inner_add_right, inner_smul_right, @norm_add_sq_real]; ring
  · module

theorem uft_one_nf {d₁ : ℕ} : UftNF (1 : isom (d₁ + 1)) (LinearIsometryEquiv.refl ℝ _) 0 0 0 := by
  intro x y z; simp

/-- **The element `A(a, b, c)`** of `Isom(𝐌^{d₁+2})`: `(x, z, y) ↦ (x − ⟨a | z⟩ − (y/2)|a|² + c,
z + b + y a, y)`: the null frame change by `−a`, then the translation by `ofNull c 0 b`. -/
noncomputable def uftA {d₁ : ℕ} (a b : EuclideanSpace ℝ (Fin d₁)) (c : ℝ) : isom (d₁ + 1) :=
  isomTrans (ofNull c 0 b) * uftPsi (-a)

theorem uftA_nf {d₁ : ℕ} (a b : EuclideanSpace ℝ (Fin d₁)) (c : ℝ) :
    UftNF (uftA a b c) (LinearIsometryEquiv.refl ℝ _) b a c := by
  intro x y z
  rw [uftA, mul_smul, uftPsi_smul]
  show ofNull c 0 b + _ = _
  rw [nsl_ofNull_add]
  simp only [LinearIsometryEquiv.coe_refl, id, inner_neg_left, norm_neg, smul_neg, sub_neg_eq_add]
  congr 1
  · ring
  · ring
  · abel

/-! ### The embedding `ι : (x, z, y) ↦ (x, z₀ + J z, y + y₀)` -/

/-- The linear part of `ι`. -/
noncomputable def uftIotaLin {d₁ : ℕ}
    (J : EuclideanSpace ℝ (Fin d₁) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    Minkowski (d₁ + 1) →ₗ[ℝ] Minkowski (d + 1) :=
  (ufrCoord (d := d)).symm.toLinearMap ∘ₗ
    (LinearMap.prodMap LinearMap.id (LinearMap.prodMap J.toLinearMap LinearMap.id)) ∘ₗ
      (ufrCoord (d := d₁)).toLinearMap

theorem uftIotaLin_apply {d₁ : ℕ} (J : EuclideanSpace ℝ (Fin d₁) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (p : Minkowski (d₁ + 1)) : uftIotaLin J p = ofNull (nullX p) (nullY p) (J (nullZ p)) := rfl

/-- **The embedding `ι`**, an isometric affine embedding `𝐌^{d₁+2} → 𝐌^{d+2}`. -/
noncomputable def uftIota {d₁ : ℕ} (J : EuclideanSpace ℝ (Fin d₁) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (z₀ : EuclideanSpace ℝ (Fin d)) (y₀ : ℝ) : AffineMinkEmbedding (d₁ + 1) (d + 1) where
  toAffineMap :=
    { toFun := fun p => uftIotaLin J p + ofNull 0 y₀ z₀
      linear := uftIotaLin J
      map_vadd' := fun p v => by
        simp only [vadd_eq_add, map_add]; abel }
  minkQ_linear v := by
    show minkQ (uftIotaLin J v) = minkQ v
    rw [uftIotaLin_apply, minkQ_eq_null, minkQ_eq_null, nullX_ofNull, nullY_ofNull,
      nullZ_ofNull, LinearIsometry.norm_map]

theorem uftIota_apply {d₁ : ℕ} (J : EuclideanSpace ℝ (Fin d₁) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (z₀ : EuclideanSpace ℝ (Fin d)) (y₀ x y : ℝ) (z : EuclideanSpace ℝ (Fin d₁)) :
    uftIota J z₀ y₀ (ofNull x y z) = ofNull x (y + y₀) (z₀ + J z) := by
  show uftIotaLin J (ofNull x y z) + ofNull 0 y₀ z₀ = _
  rw [uftIotaLin_apply, nullX_ofNull, nullY_ofNull, nullZ_ofNull, nsl_ofNull_add]
  congr 1
  · ring
  · abel

theorem uftIota_orthochronous {d₁ : ℕ}
    (J : EuclideanSpace ℝ (Fin d₁) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (z₀ : EuclideanSpace ℝ (Fin d)) (y₀ : ℝ) : (uftIota J z₀ y₀).Orthochronous := by
  show 0 < (uftIotaLin J (1, 0)).1
  rw [uftIotaLin_apply]
  show 0 < (nullX ((1, 0) : Minkowski (d₁ + 1)) - nullY ((1, 0) : Minkowski (d₁ + 1))) / √2
  simp only [nullX, nullY]
  have : (0 : ℝ) < √2 := by positivity
  ring_nf
  positivity

/-- **One element restricted** (l.2893–2903): if `γ` acts by `(R, u, v, μ)` with `R` fixing
`J(ℝ^{d₁})`, `v = J a` and `R z₀ − z₀ + y₀ v + u = J b`, then `γ` preserves `ι(𝐌^{d₁+2})` and
restricts to `A(a, b, c)`. -/
theorem uft_restricts {d₁ : ℕ} (J : EuclideanSpace ℝ (Fin d₁) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (z₀ : EuclideanSpace ℝ (Fin d)) (y₀ : ℝ) {γ : isom (d + 1)}
    {R : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)} {u v : EuclideanSpace ℝ (Fin d)}
    {μ : ℝ} (hnf : UftNF γ R u v μ) (hR : ∀ z₁, R (J z₁) = J z₁)
    {a b : EuclideanSpace ℝ (Fin d₁)} (ha : J a = v) (hb : J b = R z₀ - z₀ + y₀ • v + u) :
    (uftIota J z₀ y₀).Restricts γ (uftA a b (μ - ⟪v, R z₀⟫ - y₀ / 2 * ‖v‖ ^ 2)) := by
  intro p
  rw [← nsl_ofNull_null p, uftA_nf a b _, uftIota_apply, uftIota_apply, hnf]
  simp only [LinearIsometryEquiv.coe_refl, id]
  congr 1
  · rw [map_add, inner_add_right, hR, ← ha, LinearIsometry.inner_map_map, LinearIsometry.norm_map]
    ring
  · rw [map_add, map_add, map_add, map_smul, hR, ha, hb]
    module

/-! ### Lattices: additive maps extend linearly, symmetry spreads to the span -/

/-- **An additive map on a discrete subgroup extends to a linear map** (`L` is a `ℤ`-lattice in
its span, `Bieberbach.spanLattice`, whose `ℤ`-basis is an `ℝ`-basis of the span). -/
theorem uft_exists_linear_extension {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] {V : Type*} [AddCommGroup V] [Module ℝ V] (L : AddSubgroup F)
    (hL : BallFinite L) (φ : L →+ V) : ∃ Φ : F →ₗ[ℝ] V, ∀ x : L, Φ x = φ x := by
  classical
  let Lz : Submodule ℤ F := AddSubgroup.toIntSubmodule L
  haveI : DiscreteTopology Lz := discreteTopology_of_finite_ball L (hL.finite_ball 1)
  let M := spanLattice Lz
  let b := Module.Free.chooseBasis ℤ M
  let b' := b.ofZLatticeBasis ℝ M
  have hbL : ∀ i, (((b i : M) : span ℝ (Lz : Set F)) : F) ∈ L := fun i => (b i).2
  let Φ' : span ℝ (Lz : Set F) →ₗ[ℝ] V := b'.constr ℝ fun i => φ ⟨_, hbL i⟩
  obtain ⟨Φ, hΦ⟩ := LinearMap.exists_extend Φ'
  refine ⟨Φ, fun x => ?_⟩
  let xs : span ℝ (Lz : Set F) := ⟨x, subset_span x.2⟩
  have h1 : Φ x = Φ' xs := by
    rw [← hΦ]; rfl
  rw [h1]
  let f₁ : M →ₗ[ℤ] V := (Φ'.restrictScalars ℤ).comp M.subtype
  let ι' : M →+ L :=
    { toFun := fun y => ⟨((y : span ℝ (Lz : Set F)) : F), y.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let f₂ : M →ₗ[ℤ] V := (φ.comp ι').toIntLinearMap
  have hf : f₁ = f₂ := b.ext fun i => by
    simp only [f₁, f₂, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
      LinearMap.coe_restrictScalars, AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.coe_comp]
    have : ((b i : M) : span ℝ (Lz : Set F)) = b' i := by
      rw [Basis.ofZLatticeBasis_apply]
    rw [this, Basis.constr_basis]
    rfl
  have := LinearMap.congr_fun hf ⟨xs, x.2⟩
  exact this

/-- **Symmetry on `L` spreads to `span L`.** -/
theorem uft_symm_span {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {L : AddSubgroup F}
    {T : F →ₗ[ℝ] F} (h : ∀ u ∈ L, ∀ u' ∈ L, ⟪u, T u'⟫ = ⟪u', T u⟫) :
    ∀ u ∈ span ℝ (L : Set F), ∀ u' ∈ span ℝ (L : Set F), ⟪u, T u'⟫ = ⟪u', T u⟫ := by
  have h1 : ∀ u ∈ L, ∀ u' ∈ span ℝ (L : Set F), ⟪u, T u'⟫ = ⟪u', T u⟫ := by
    intro u hu u' hu'
    induction hu' using Submodule.span_induction with
    | mem y hy => exact h u hu y hy
    | zero => simp
    | add y z _ _ hy hz => rw [map_add, inner_add_right, inner_add_left, hy, hz]
    | smul c y _ hy => rw [map_smul, inner_smul_right, inner_smul_left, hy]; simp
  intro u hu u' hu'
  induction hu using Submodule.span_induction with
  | mem y hy => exact h1 y hy u' hu'
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, inner_add_right, inner_add_left, hy, hz]
  | smul c y _ hy => rw [map_smul, inner_smul_right, inner_smul_left, hy]; simp

/-! ### A parabolic element survives in the finite-index subgroup -/

/-- A positive power of a parabolic `A` is not elliptic (the Jordan pair `A v₁ = v₁ + v₀`). -/
theorem uft_not_isElliptic_pow {A : Minkowski (d + 1) ≃ₗ[ℝ] Minkowski (d + 1)} (hA : IsParabolic A)
    {n : ℕ} (hn : n ≠ 0) : ¬IsElliptic (A ^ n) := by
  intro he
  obtain ⟨v₁, v₀, hv0, h1, h0⟩ := hA.exists_jordan
  have hp0 : ∀ k : ℕ, (A ^ k) v₀ = v₀ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, LinearEquiv.mul_apply, h0, ih]
  have hp1 : ∀ k : ℕ, (A ^ k) v₁ = v₁ + (k : ℝ) • v₀ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, LinearEquiv.mul_apply, h1, map_add, ih, hp0]; push_cast
                   rw [add_smul, one_smul, add_assoc]
  have hmem : (n : ℝ) • v₀ ∈ LinearMap.range (pOf (A ^ n)) ⊓ LinearMap.ker (pOf (A ^ n)) :=
    ⟨⟨v₁, by rw [pOf_apply, hp1, add_sub_cancel_left]⟩,
      by show pOf (A ^ n) _ = 0; rw [pOf_apply, map_smul, hp0, sub_self]⟩
  rw [he.range_inf_ker, Submodule.mem_bot] at hmem
  exact smul_ne_zero (by exact_mod_cast hn) hv0 hmem

/-- **Non-elliptic ⇒ `v ∉ Im (id − R)`** (`BTrivial.hpar_coord`, for a non-elliptic linear part). -/
theorem uft_v_ne {γ : isom (d + 1)} (hne : ¬IsElliptic (linOf γ))
    (hfix : linOf γ (ofNull 1 0 0) = ofNull 1 0 0)
    {R : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)} {u v : EuclideanSpace ℝ (Fin d)}
    {μ : ℝ} (hnf : UftNF γ R u v μ) (c : EuclideanSpace ℝ (Fin d)) : v + (c - R c) ≠ 0 := by
  intro h0
  set g : BTrivialAux.NolParam (EuclideanSpace ℝ (Fin d)) := ⟨R, u, v, μ, 0⟩
  have hg : ∀ X, γ • BTrivialAux.nolToMink X = BTrivialAux.nolToMink (g.act X) := by
    intro X
    simp only [BTrivialAux.nolToMink, BTrivialAux.NolParam.act, g, add_zero]
    exact hnf _ _ _
  have hv : v = R c - c := by rw [eq_neg_of_add_eq_zero_left h0, neg_sub]
  set W : ℝ × EuclideanSpace ℝ (Fin d) × ℝ := (0, -c, 1) with hW_def
  have hW : linOf γ (BTrivialAux.nolToMink W) = BTrivialAux.nolToMink W := by
    rw [BTrivialAux.linOf_nolToMink hg]
    congr 1
    simp only [hW_def, BTrivialAux.NolParam.act, g, Prod.fst_zero, Prod.snd_zero, map_zero,
      inner_zero_right, zero_div, zero_mul, zero_smul, Prod.mk_sub_mk, Prod.mk.injEq]
    refine ⟨?_, ?_, by ring⟩
    · rw [hv, map_neg, inner_neg_right, inner_sub_left, @norm_sub_sq_real,
        LinearIsometryEquiv.norm_map, real_inner_self_eq_norm_sq, LinearIsometryEquiv.norm_map,
        real_inner_comm c (R c)]
      ring
    · rw [hv, map_neg]; module
  have hq : minkQ (BTrivialAux.nolToMink (d := d) (1, 0, 0)) = 0 := by
    rw [BTrivialAux.minkQ_nolToMink]; simp [BTrivialAux.nolQ]
  have := minkB_eq_zero_of_fixed_of_not_isElliptic (linOf_mem γ) hne hq hfix hW
  rw [BTrivialAux.minkB_nolToMink] at this
  simp [BTrivialAux.nolB, hW_def] at this

/-! ### [9.U] up to a frame -/

/-- **The lattice data of a unipotent group** (l.2905–2925): a commutative group `RG` of elements
`A(α g, β g, κ g)` on which `β` is injective with ball-finite image gives `L = β(RG)` ball-finite,
`T` linear with `T ∘ β = α`, symmetric on `span L`, and `ℓ` linear with
`ℓ ∘ β = κ + ⟨β | α⟩/2` (Barbot's "`Γ ≅ ℤᵏ`", "`v = T ∘ u`", and the cocycle `μ`). -/
theorem uft_lattice {d₁ : ℕ} (RG : Subgroup (isom (d₁ + 1)))
    (hNF : ∀ g ∈ RG, UftNF g (LinearIsometryEquiv.refl ℝ _) (uftβ g) (uftα g) (uftκ g))
    (hcommRG : ∀ g ∈ RG, ∀ g' ∈ RG, g * g' = g' * g)
    (hinj : ∀ g ∈ RG, ∀ g' ∈ RG, uftβ g = uftβ g' → g = g')
    (hball : ∀ R₀ : ℝ, {v | (∃ g ∈ RG, uftβ g = v) ∧ ‖v‖ ≤ R₀}.Finite)
    (hparRG : ∃ g ∈ RG, uftα g ≠ 0) :
    ∃ (L : AddSubgroup (EuclideanSpace ℝ (Fin d₁)))
      (T : EuclideanSpace ℝ (Fin d₁) →ₗ[ℝ] EuclideanSpace ℝ (Fin d₁))
      (ℓ : EuclideanSpace ℝ (Fin d₁) →ₗ[ℝ] ℝ),
      BallFinite L ∧ (∃ u ∈ L, T u ≠ 0) ∧
      (∀ u ∈ span ℝ (L : Set (EuclideanSpace ℝ (Fin d₁))),
        ∀ u' ∈ span ℝ (L : Set (EuclideanSpace ℝ (Fin d₁))), ⟪u, T u'⟫ = ⟪u', T u⟫) ∧
      (∀ g ∈ RG, ∃ u ∈ L, ∀ x y z, g • ofNull x y z =
        ofNull (x - ⟪T u, z⟫ - y / 2 * ‖T u‖ ^ 2 + (ℓ u - ⟪u, T u⟫ / 2)) y (z + u + y • T u)) ∧
      (∀ u ∈ L, ∃ g ∈ RG, ∀ x y z, g • ofNull x y z =
        ofNull (x - ⟪T u, z⟫ - y / 2 * ‖T u‖ ^ 2 + (ℓ u - ⟪u, T u⟫ / 2)) y (z + u + y • T u)) := by
  classical
  have hmulp : ∀ g ∈ RG, ∀ g' ∈ RG, uftβ (g * g') = uftβ g + uftβ g' ∧
      uftα (g * g') = uftα g + uftα g' ∧ uftκ (g * g') = uftκ g + uftκ g' - ⟪uftα g, uftβ g'⟫ :=
    fun g hg g' hg' => ((hNF g hg).mul_unip (hNF g' hg')).params
  have hone := (uft_one_nf (d₁ := d₁)).params
  have hsymm : ∀ g ∈ RG, ∀ g' ∈ RG, ⟪uftα g, uftβ g'⟫ = ⟪uftα g', uftβ g⟫ := by
    intro g hg g' hg'
    have h1 := (hmulp g hg g' hg').2.2
    have h2 := (hmulp g' hg' g hg).2.2
    rw [hcommRG g hg g' hg'] at h1
    linarith
  -- the lattice `L = β(RG)` and the maps `T`, `ℓ`
  let βH : Additive RG →+ EuclideanSpace ℝ (Fin d₁) :=
    { toFun := fun g => uftβ ((Additive.toMul g : RG) : isom (d₁ + 1))
      map_zero' := hone.1
      map_add' := fun g g' => (hmulp _ (Additive.toMul g).2 _ (Additive.toMul g').2).1 }
  let αH : Additive RG →+ EuclideanSpace ℝ (Fin d₁) :=
    { toFun := fun g => uftα ((Additive.toMul g : RG) : isom (d₁ + 1))
      map_zero' := hone.2.1
      map_add' := fun g g' => (hmulp _ (Additive.toMul g).2 _ (Additive.toMul g').2).2.1 }
  have hνadd : ∀ g ∈ RG, ∀ g' ∈ RG, uftκ (g * g') + ⟪uftβ (g * g'), uftα (g * g')⟫ / 2 =
      (uftκ g + ⟪uftβ g, uftα g⟫ / 2) + (uftκ g' + ⟪uftβ g', uftα g'⟫ / 2) := by
    intro g hg g' hg'
    obtain ⟨e1, e2, e3⟩ := hmulp g hg g' hg'
    rw [e1, e2, e3]
    have hs : ⟪uftβ g, uftα g'⟫ = ⟪uftβ g', uftα g⟫ := by
      rw [real_inner_comm, ← hsymm g hg g' hg']
      exact real_inner_comm (uftβ g') (uftα g)
    simp only [inner_add_left, inner_add_right]
    rw [real_inner_comm (uftβ g') (uftα g), hs]
    ring
  let νH : Additive RG →+ ℝ := AddMonoidHom.mk'
    (fun g => uftκ ((Additive.toMul g : RG) : isom (d₁ + 1)) +
      ⟪uftβ ((Additive.toMul g : RG) : isom (d₁ + 1)), uftα ((Additive.toMul g : RG) : isom (d₁ + 1))⟫ / 2)
    (fun g g' => hνadd _ (Additive.toMul g).2 _ (Additive.toMul g').2)
  have hβinj : Function.Injective βH := fun g g' he =>
    Additive.toMul.injective (Subtype.ext (hinj _ (Additive.toMul g).2 _ (Additive.toMul g').2 he))
  have hBall' : BallFinite βH.range := ⟨fun R₀ => (hball R₀).subset fun v ⟨hvL, hvR⟩ => by
    obtain ⟨g, rfl⟩ := hvL
    exact ⟨⟨_, (Additive.toMul g).2, rfl⟩, hvR⟩⟩
  let e := AddMonoidHom.ofInjective hβinj
  obtain ⟨T, hT⟩ := uft_exists_linear_extension βH.range hBall' (αH.comp e.symm.toAddMonoidHom)
  obtain ⟨ℓ, hℓ⟩ := uft_exists_linear_extension βH.range hBall' (νH.comp e.symm.toAddMonoidHom)
  have he : ∀ g (hg : g ∈ RG), ((e (Additive.ofMul ⟨g, hg⟩) : βH.range) :
      EuclideanSpace ℝ (Fin d₁)) = uftβ g := fun g hg => AddMonoidHom.ofInjective_apply hβinj
  have hes : ∀ g (hg : g ∈ RG), e.symm (e (Additive.ofMul ⟨g, hg⟩)) = Additive.ofMul ⟨g, hg⟩ :=
    fun g hg => e.symm_apply_apply _
  have hTg : ∀ g ∈ RG, T (uftβ g) = uftα g := by
    intro g hg
    calc T (uftβ g) = T ((e (Additive.ofMul ⟨g, hg⟩) : βH.range) : EuclideanSpace ℝ (Fin d₁)) := by
          rw [he g hg]
      _ = αH (e.symm (e (Additive.ofMul ⟨g, hg⟩))) := hT _
      _ = uftα g := by rw [hes g hg]; rfl
  have hℓg : ∀ g ∈ RG, ℓ (uftβ g) = uftκ g + ⟪uftβ g, uftα g⟫ / 2 := by
    intro g hg
    calc ℓ (uftβ g) = ℓ ((e (Additive.ofMul ⟨g, hg⟩) : βH.range) : EuclideanSpace ℝ (Fin d₁)) := by
          rw [he g hg]
      _ = νH (e.symm (e (Additive.ofMul ⟨g, hg⟩))) := hℓ _
      _ = uftκ g + ⟪uftβ g, uftα g⟫ / 2 := by rw [hes g hg]; rfl
  obtain ⟨L, hLdef⟩ : ∃ L : AddSubgroup (EuclideanSpace ℝ (Fin d₁)), L = βH.range := ⟨_, rfl⟩
  have hmemL : ∀ g ∈ RG, uftβ g ∈ L := fun g hg => by
    rw [hLdef]; exact ⟨Additive.ofMul ⟨g, hg⟩, rfl⟩
  have hLmem : ∀ u ∈ L, ∃ g ∈ RG, uftβ g = u := by
    intro u hu
    rw [hLdef] at hu
    obtain ⟨g, rfl⟩ := hu
    exact ⟨_, (Additive.toMul g).2, rfl⟩
  have hBall : BallFinite L := hLdef ▸ hBall'
  have hpar' : ∃ u ∈ L, T u ≠ 0 := by
    obtain ⟨g, hg, hα⟩ := hparRG
    exact ⟨uftβ g, hmemL g hg, by rw [hTg g hg]; exact hα⟩
  have hsymL : ∀ u ∈ L, ∀ u' ∈ L, ⟪u, T u'⟫ = ⟪u', T u⟫ := by
    intro u hu u' hu'
    obtain ⟨g, hg, rfl⟩ := hLmem u hu
    obtain ⟨g', hg', rfl⟩ := hLmem u' hu'
    rw [hTg g' hg', hTg g hg, real_inner_comm, hsymm g' hg' g hg]
    exact real_inner_comm _ _
  refine ⟨L, T, ℓ, hBall, hpar', fun u hu u' hu' => uft_symm_span hsymL u hu u' hu', ?_, ?_⟩
  · intro g hg
    refine ⟨uftβ g, hmemL g hg, fun x y z => ?_⟩
    rw [hTg g hg, hℓg g hg, hNF g hg]
    simp only [LinearIsometryEquiv.coe_refl, id]
    congr 1
    · ring
    · abel
  · intro u hu
    obtain ⟨g, hg, hgu⟩ := hLmem u hu
    refine ⟨g, hg, fun x y z => ?_⟩
    rw [← hgu, hTg g hg, hℓg g hg, hNF g hg]
    simp only [LinearIsometryEquiv.coe_refl, id]
    congr 1
    · ring
    · abel

theorem uft_relIndex_map_subtype {G : Subgroup (isom (d + 1))} (K : Subgroup G) :
    (K.map G.subtype).relIndex G = K.index := by
  have : (K.map G.subtype).subgroupOf G = K := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.coe_subtype]
    constructor
    · rintro ⟨y, hy, hyx⟩; rwa [← Subtype.ext hyx]
    · intro hx; exact ⟨x, hx, rfl⟩
  rw [Subgroup.relIndex, this]

set_option maxHeartbeats 1600000 in
/-- **[9.U], up to a frame** (`GHFspace.tex` l.2865–2938, corrected). Under the hypotheses of the
dispatched `exists_unipotent_restriction` — `CCAction G Σ`, `L(G)` fixing `v₀ = ofNull 1 0 0`,
`b ≡ 0`, a parabolic element — and Bieberbach in `ℝᵈ`, the conclusion
`UnipotentRestrictionConclusion` holds after conjugating `(G, Σ)` by the null frame change
`ψ = ψ_w` (`uftPsi`), `w = (p₁ − p₀)/(t₁ − t₀)` read off the Bieberbach subspaces of two slices. -/
theorem exists_unipotentRestriction_upToFrame (hBieb : BieberbachI (EuclideanSpace ℝ (Fin d)))
    {G : Subgroup (isom (d + 1))} {St : Set (Minkowski (d + 1))} (hcc : CCAction G St)
    (hfix : ∀ γ ∈ G, linOf γ (ofNull 1 0 0) = ofNull 1 0 0)
    (hb : ∀ γ ∈ G, ∀ p : Minkowski (d + 1), nullY (γ • p) = nullY p)
    (hpar : ∃ γ ∈ G, IsParabolic (linOf γ)) :
    ∃ ψ : isom (d + 1), UnipotentRestrictionConclusion d (frameConj ψ G) (ψ • St) := by
  classical
  have h : UftHyp G := ⟨hfix, hb⟩
  -- the heights and their normalisation
  obtain ⟨y₀, hy₀, ylo, yhi, hlo, hhi, hnorm, hiff⟩ :=
    nsl_exists_normalisation (hcc.nonempty.image _) (nsl_heights_ordConnected hcc.cc)
      (fun t ht => nsl_heights_noMax hcc.cc ht) (fun t ht => nsl_heights_noMin hcc.cc ht)
  obtain ⟨t₁, ht₁, hlt⟩ := nsl_heights_noMax hcc.cc hy₀
  -- Bieberbach on the slices `y₀` and `t₁`
  obtain ⟨K₀, hK₀, U₀, p₀, hp₀, htr₀, heff₀⟩ := uft_bieberbach hBieb hcc h hy₀
  obtain ⟨K₁, hK₁, U₁, p₁, hp₁, htr₁, -⟩ := uft_bieberbach hBieb hcc h ht₁
  set K := K₀ ⊓ K₁ with hKdef
  have hKidx : K.index ≠ 0 := Subgroup.index_inf_ne_zero hK₀ hK₁
  have hcomm : ∀ γ ∈ K, ∀ γ' ∈ K, γ * γ' = γ' * γ := fun γ hγ γ' hγ' =>
    uft_comm h htr₀ heff₀ γ hγ.1 γ' hγ'.1
  -- the common fixed space `W` of the rotations
  let W : Submodule ℝ (EuclideanSpace ℝ (Fin d)) :=
    { carrier := {z | ∀ γ ∈ K, (uftData (γ : isom (d + 1))).1 z = z}
      add_mem' := fun ha hb γ hγ => by rw [map_add, ha γ hγ, hb γ hγ]
      zero_mem' := fun γ _ => map_zero _
      smul_mem' := fun c z hz γ hγ => by rw [map_smul, hz γ hγ] }
  have hmemW : ∀ z, z ∈ W ↔ ∀ γ ∈ K, (uftData (γ : isom (d + 1))).1 z = z := fun _ => Iff.rfl
  have he₀ : ∀ γ ∈ K, uftSlice y₀ (γ : isom (d + 1)) p₀ - p₀ ∈ W := by
    intro γ hγ
    obtain ⟨c, hc, hcq⟩ := htr₀ γ hγ.1
    rw [hcq p₀ hp₀, vadd_eq_add, add_sub_cancel_right, hmemW]
    intro γ' hγ'
    obtain ⟨c', -, hcq'⟩ := htr₀ γ' hγ'.1
    exact uft_rot_fix_of_translation hcq' hp₀ hc
  have he₁ : ∀ γ ∈ K, uftSlice t₁ (γ : isom (d + 1)) p₁ - p₁ ∈ W := by
    intro γ hγ
    obtain ⟨c, hc, hcq⟩ := htr₁ γ hγ.2
    rw [hcq p₁ hp₁, vadd_eq_add, add_sub_cancel_right, hmemW]
    intro γ' hγ'
    obtain ⟨c', -, hcq'⟩ := htr₁ γ' hγ'.2
    exact uft_rot_fix_of_translation hcq' hp₁ hc
  -- the frame `w` and the base point `z₀`
  have hne : t₁ - y₀ ≠ 0 := sub_ne_zero.2 hlt.ne'
  set w : EuclideanSpace ℝ (Fin d) := (t₁ - y₀)⁻¹ • (p₁ - p₀) with hw
  have hV : ∀ γ ∈ K, (uftData (γ : isom (d + 1))).2.2.1 + (uftData (γ : isom (d + 1))).1 w - w ∈ W := by
    intro γ hγ
    have key : (t₁ - y₀) • ((uftData (γ : isom (d + 1))).2.2.1 + (uftData (γ : isom (d + 1))).1 w - w) =
        (uftSlice t₁ (γ : isom (d + 1)) p₁ - p₁) - (uftSlice y₀ (γ : isom (d + 1)) p₀ - p₀) := by
      rw [uftSlice_apply, uftSlice_apply, hw, map_smul, map_sub]
      simp only [smul_add, smul_sub, smul_smul, mul_inv_cancel₀ hne, one_smul]
      module
    have : (uftData (γ : isom (d + 1))).2.2.1 + (uftData (γ : isom (d + 1))).1 w - w =
        (t₁ - y₀)⁻¹ • ((uftSlice t₁ (γ : isom (d + 1)) p₁ - p₁) -
          (uftSlice y₀ (γ : isom (d + 1)) p₀ - p₀)) := by
      rw [← key, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [this]
    exact W.smul_mem _ (W.sub_mem (he₁ γ hγ) (he₀ γ hγ))
  set z₀ : EuclideanSpace ℝ (Fin d) := p₀ - y₀ • w with hz₀
  have hE₀ : ∀ γ : G, (uftData (γ : isom (d + 1))).1 z₀ - z₀ +
      y₀ • ((uftData (γ : isom (d + 1))).2.2.1 + (uftData (γ : isom (d + 1))).1 w - w) +
        (uftData (γ : isom (d + 1))).2.1 = uftSlice y₀ (γ : isom (d + 1)) p₀ - p₀ := by
    intro γ
    rw [uftSlice_apply, hz₀, map_sub, map_smul]
    module
  -- the isometric embedding `J : ℝ^{d₁} → W`
  let eW := stdOrthonormalBasis ℝ W
  let J : EuclideanSpace ℝ (Fin (finrank ℝ W)) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d) :=
    W.subtypeₗᵢ.comp eW.repr.symm.toLinearIsometry
  have hJW : ∀ a, J a ∈ W := fun a => (eW.repr.symm a).2
  have hJsurj : ∀ x ∈ W, ∃ a, J a = x := fun x hx => ⟨eW.repr ⟨x, hx⟩, by
    simp [J]⟩
  have hd₁ : finrank ℝ W ≤ d := (Submodule.finrank_le W).trans (by simp)
  set ψ := uftPsi w with hψ
  set ι := uftIota J z₀ y₀ with hιdef
  set G'' := frameConj ψ (K.map G.subtype) with hG''
  -- one element restricted
  have hres : ∀ γ : G, γ ∈ K → ∃ a b c, ι.Restricts (ψ * γ * ψ⁻¹) (uftA a b c) ∧
      J b = uftSlice y₀ (γ : isom (d + 1)) p₀ - p₀ ∧
      J a = (uftData (γ : isom (d + 1))).2.2.1 + (uftData (γ : isom (d + 1))).1 w - w := by
    intro γ hγ
    obtain ⟨a, ha⟩ := hJsurj _ (hV γ hγ)
    obtain ⟨b, hb'⟩ := hJsurj _ (he₀ γ hγ)
    exact ⟨a, b, _, uft_restricts J z₀ y₀ (uft_conj_nf (uft_nf h γ.2) w)
      (fun z₁ => (hmemW _).1 (hJW z₁) γ hγ) ha (by rw [hb', ← hE₀ γ]), hb', ha⟩
  have hmemG'' : ∀ γs ∈ G'', ∃ γ : G, γ ∈ K ∧ γs = ψ * γ * ψ⁻¹ := by
    intro γs hγs
    obtain ⟨γ', hγ', rfl⟩ := Subgroup.mem_map.1 hγs
    obtain ⟨γ, hγK, rfl⟩ := Subgroup.mem_map.1 hγ'
    exact ⟨γ, hγK, rfl⟩
  set RG := ι.restrictGroup G'' with hRGdef
  have hRG : ∀ g ∈ RG, ∃ γ : G, γ ∈ K ∧ ι.Restricts (ψ * γ * ψ⁻¹) g ∧
      UftNF g (LinearIsometryEquiv.refl ℝ _) (uftβ g) (uftα g) (uftκ g) ∧
      J (uftβ g) = uftSlice y₀ (γ : isom (d + 1)) p₀ - p₀ ∧
      J (uftα g) = (uftData (γ : isom (d + 1))).2.2.1 + (uftData (γ : isom (d + 1))).1 w - w := by
    intro g hg
    obtain ⟨γs, hγs, hgr⟩ := ι.mem_restrictGroup.1 hg
    obtain ⟨γ, hγK, rfl⟩ := hmemG'' γs hγs
    obtain ⟨a, b, c, hr, hJb, hJa⟩ := hres γ hγK
    have hg' : g = uftA a b c := hgr.unique hr
    have hnf := uftA_nf a b c
    rw [← hg'] at hnf
    obtain ⟨h1, h2, h3⟩ := hnf.params
    refine ⟨γ, hγK, hgr, by rw [h1, h2, h3]; exact hnf, by rw [h1]; exact hJb, by rw [h2]; exact hJa⟩
  have hNF : ∀ g ∈ RG, UftNF g (LinearIsometryEquiv.refl ℝ _) (uftβ g) (uftα g) (uftκ g) :=
    fun g hg => (hRG g hg).choose_spec.2.2.1
  have hmulp : ∀ g ∈ RG, ∀ g' ∈ RG, uftβ (g * g') = uftβ g + uftβ g' ∧
      uftα (g * g') = uftα g + uftα g' ∧ uftκ (g * g') = uftκ g + uftκ g' - ⟪uftα g, uftβ g'⟫ :=
    fun g hg g' hg' => ((hNF g hg).mul_unip (hNF g' hg')).params
  have hone := (uft_one_nf (d₁ := finrank ℝ W)).params
  have hcommRG : ∀ g ∈ RG, ∀ g' ∈ RG, g * g' = g' * g := by
    intro g hg g' hg'
    obtain ⟨γ, hγ, hr, -⟩ := hRG g hg
    obtain ⟨γ', hγ', hr', -⟩ := hRG g' hg'
    have e : ψ * γ * ψ⁻¹ * (ψ * γ' * ψ⁻¹) = ψ * γ' * ψ⁻¹ * (ψ * γ * ψ⁻¹) := by
      have := congrArg (fun x : G => ψ * (x : isom (d + 1)) * ψ⁻¹) (hcomm γ hγ γ' hγ')
      simp only [Subgroup.coe_mul] at this
      calc ψ * γ * ψ⁻¹ * (ψ * γ' * ψ⁻¹) = ψ * (γ * γ') * ψ⁻¹ := by group
        _ = ψ * (γ' * γ) * ψ⁻¹ := this
        _ = _ := by group
    exact (hr.mul hr').unique (e ▸ hr'.mul hr)
  have hinj : ∀ g ∈ RG, ∀ g' ∈ RG, uftβ g = uftβ g' → g = g' := by
    intro g hg g' hg' he
    have hk : g⁻¹ * g' ∈ RG := RG.mul_mem (RG.inv_mem hg) hg'
    have hβ0 : uftβ (g⁻¹ * g') = 0 := by
      have e1 := (hmulp _ (RG.inv_mem hg) _ hg').1
      have e2 := (hmulp _ (RG.inv_mem hg) _ hg).1
      rw [inv_mul_cancel, hone.1] at e2
      rw [e1, ← he]; exact e2.symm
    obtain ⟨γ, hγ, hr, -, hJb, -⟩ := hRG _ hk
    rw [hβ0, map_zero] at hJb
    have hγ1 : (γ : isom (d + 1)) = 1 :=
      uft_eq_one_of_fixed hcc h hy₀ γ.2 (sub_eq_zero.1 hJb.symm)
    rw [hγ1, mul_one, mul_inv_cancel] at hr
    have := hr.unique (AffineMinkEmbedding.Restricts.one (ι := uftIota J z₀ y₀))
    rw [inv_mul_eq_one] at this
    exact this
  have hball : ∀ R₀ : ℝ, {v | (∃ g ∈ RG, uftβ g = v) ∧ ‖v‖ ≤ R₀}.Finite := by
    intro R₀
    have hD := uft_isDiscreteEucl hcc h hy₀ p₀ R₀
    refine Set.Finite.of_finite_image ((hD.image fun f => f p₀ - p₀).subset ?_) J.injective.injOn
    rintro _ ⟨v, ⟨⟨g, hg, rfl⟩, hvR⟩, rfl⟩
    obtain ⟨γ, -, -, -, hJb, -⟩ := hRG g hg
    refine ⟨uftHom h y₀ γ, ⟨⟨γ, rfl⟩, ?_⟩, ?_⟩
    · rw [dist_eq_norm, uftHom_apply, ← hJb, LinearIsometry.norm_map]; exact hvR
    · show uftHom h y₀ γ p₀ - p₀ = J (uftβ g)
      rw [uftHom_apply, hJb]
  -- the parabolic element survives: `T ≠ 0` on `L`
  have hparRG : ∃ g ∈ RG, uftα g ≠ 0 := by
    obtain ⟨γ₁, hγ₁G, hγ₁par⟩ := hpar
    obtain ⟨n, hn, -, hpow⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hKidx (⟨γ₁, hγ₁G⟩ : G)
    set γ₂ : G := ⟨γ₁, hγ₁G⟩ ^ n with hγ₂
    have hne₂ : ¬IsElliptic (linOf (γ₂ : isom (d + 1))) := by
      rw [hγ₂, Subgroup.coe_pow, linOf_pow]
      exact uft_not_isElliptic_pow hγ₁par hn.ne'
    have hv₂ := uft_v_ne hne₂ (hfix _ γ₂.2) (uft_nf h γ₂.2) (-w)
    obtain ⟨a, b, c, hr, -, hJa⟩ := hres γ₂ hpow
    have hgRG : uftA a b c ∈ RG :=
      ι.mem_restrictGroup.2 ⟨_, Subgroup.mem_map.2 ⟨_, Subgroup.mem_map.2 ⟨γ₂, hpow, rfl⟩, rfl⟩, hr⟩
    refine ⟨uftA a b c, hgRG, ?_⟩
    rw [(uftA_nf a b c).params.2.1]
    intro ha0
    apply hv₂
    rw [ha0, map_zero] at hJa
    rw [map_neg]
    have := hJa.symm
    rw [← this]; abel
  obtain ⟨L, T, ℓ, hBall, hpar', hsym, hform, hform'⟩ :=
    uft_lattice RG hNF hcommRG hinj hball hparRG
  refine ⟨ψ, G'', Subgroup.map_mono (Subgroup.map_subtype_le K), ?_, finrank ℝ W, hd₁, J, z₀, y₀, ι,
    uftIota_apply J z₀ y₀, uftIota_orthochronous J z₀ y₀, ?_, L, T, ℓ, ylo, yhi, hBall, hpar',
    hsym, hform, hform', hlo, hhi, hnorm, ?_, ?_⟩
  · show (frameConj ψ (K.map G.subtype)).relIndex (frameConj ψ G) ≠ 0
    rw [frameConj, frameConj, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj ψ).injective,
      uft_relIndex_map_subtype]
    exact hKidx
  · intro γs hγs
    obtain ⟨γ, hγK, rfl⟩ := hmemG'' γs hγs
    obtain ⟨a, b, c, hr, -⟩ := hres γ hγK
    exact ⟨_, hr⟩
  · intro y h1 h2
    obtain ⟨q, hq, hqy⟩ := (hiff y).1 ⟨h1, h2⟩
    obtain ⟨x, hx⟩ := nsl_exists_mem hcc.cc.nullSat hq (z₀ + (y + y₀) • w)
    rw [hqy] at hx
    refine ⟨ofNull (x + ⟪w, z₀ + (y + y₀) • w⟫ - (y + y₀) / 2 * ‖w‖ ^ 2) y 0, ?_,
      nullY_ofNull _ _ _⟩
    rw [uftIota_apply, map_zero, add_zero]
    have e1 : ψ • ofNull x (y + y₀) (z₀ + (y + y₀) • w) =
        ofNull (x + ⟪w, z₀ + (y + y₀) • w⟫ - (y + y₀) / 2 * ‖w‖ ^ 2) (y + y₀) z₀ := by
      rw [hψ, uftPsi_smul, add_sub_cancel_right]
    rw [← e1]
    exact Set.smul_mem_smul_set hx
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := hp
    rw [hψ, uftPsi_nullY]
    exact (hiff _).2 (by rw [sub_add_cancel]; exact ⟨q, hq, rfl⟩)

end Causal.Flat.Nonlox
