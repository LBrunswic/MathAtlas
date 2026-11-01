import CausalScaffold.Flat.Develop
import CausalScaffold.Flat.Externals
import CausalScaffold.Flat.Bieberbach
import CausalScaffold.Flat.TwistedProduct
import CausalScaffold.Flat.Examples
import CausalScaffold.Flat.CauchyComplete
import CausalScaffold.Flat.Nonlox.BTrivial
import CausalScaffold.Flat.Nonlox.UnipotentFrame

/-!
# `CausalScaffold.Flat.Nonlox.NullSlices` — a (CC′) surface over the null slices `{y = t}`, and the slab of its heights

T. Barbot, *Globally hyperbolic flat space-times*, §9, the parabolic case, points (1) and (3)
(`GHFspace.tex` l.2651–2663 of `papers/barbot/legacy/labeled/`) and the normalisation
`y₋ = −y₊` (l.2934–2938), served for `[9.U]` (`Flat/Nonlox/UnipotentUpToFrame`). Barbot's labels
are cited UNMARKED: nothing here certifies a label; these are the inputs the proof of [9.U] uses.

> The projection `π₀(S̃)` is an open set of the form `f⁻¹(I)` where `I` is a segment of the
> affine line `Q₁` (cf. corollary `quoiso`). (l.2653–2654)

> The action of `Γ` on `π₀(S̃)` via `α` is free and properly discontinuous (since the restriction
> of `π₀` to `S̃` is a homeomorphism onto its image). (l.2660–2663)

> Denote by `y₋`, `y₊` the extremities (maybe infinite) of the intervall `I = π₁(S̃)`. Remember
> that we assume here `y₋ < 0 < y₊`. When `y±` are both finite, we change the coordinates so that
> `y₋ = −y₊`. (l.2934–2938)

In the null coordinates `ofNull x y z` of `Flat/Examples` (`v₀ = ofNull 1 0 0`), for `S̃` with
(CC′) (`CCPrime`):
* `nsl_eq_of_nullY_nullZ` — two points of an acausal set on one `v₀`-line coincide;
* `nsl_exists_mem` — (CC′)(b) at `ℓ = v₀`: if `S̃` meets `{y = t}`, it meets every `v₀`-line of it;
* `nslX`, `nslX_mem`, `nslX_unique` — the section `z ↦ ofNull (nslX S̃ t z) t z ∈ S̃` over each
  height `t ∈ nullY '' S̃`, and `continuous_nslX` — it is continuous (`S̃` is the graph of a strict
  contraction, so `x ↦ (time − f)(ofNull x t z)` is strictly increasing: `nsl_continuous_of_zero`);
  `isCompact_nslSection` — the section over a compact set is compact (the input of point (3));
* `nsl_heights_ordConnected`, `nsl_heights_noMax`, `nsl_heights_noMin` — `I = nullY '' S̃` is an
  open interval; `nsl_exists_normalisation` — a height `y₀ ∈ I` and `ylo < 0 < yhi` with
  `ylo = −yhi ∨ yhi = ⊤ ∨ ylo = ⊥` and `y ∈ ]ylo, yhi[ ↔ y + y₀ ∈ I`.

## Hypothesis checklist
| paper hypothesis | here |
|---|---|
| `S̃` complete spacelike, `Γ`-invariant | ⚠ weakened: (CC′) (`CCPrime`) only; `Γ` is not used |
| `π₀ ∣ S̃` a homeomorphism onto `f⁻¹(I)` | proved here in the form used (section continuous, onto `ℝᵈ × I`) |

## SCOPE (disclosed)
* The homeomorphism `π₀ ∣ S̃ → f⁻¹(I)` is not stated as such: only its inverse section over each
  height, and its continuity in `z` (what point (3)'s properness needs).
* `y₀` is the midpoint of `I` when both ends are finite, and any point `t ± 1` from the finite end
  otherwise; Barbot's normalisation is the first case.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
WP-34c-Nonloxodromic, serving `Causal.Flat.exists_unipotent_restriction_up_to_frame` ([9.U]).
-/

namespace Causal.Flat.Nonlox

open Causal.Flat Set Filter Topology Module
open scoped RealInnerProductSpace

variable {d : ℕ}

/-! ### Null-coordinate algebra -/

theorem nsl_ofNull_eq (x y : ℝ) (z : EuclideanSpace ℝ (Fin d)) :
    ofNull x y z = ufrCoord.symm (x, z, y) := rfl

theorem nsl_ofNull_add (x y x' y' : ℝ) (z z' : EuclideanSpace ℝ (Fin d)) :
    ofNull x y z + ofNull x' y' z' = ofNull (x + x') (y + y') (z + z') := by
  rw [nsl_ofNull_eq, nsl_ofNull_eq, nsl_ofNull_eq, ← map_add]; rfl

theorem nsl_ofNull_sub (x y x' y' : ℝ) (z z' : EuclideanSpace ℝ (Fin d)) :
    ofNull x y z - ofNull x' y' z' = ofNull (x - x') (y - y') (z - z') := by
  rw [nsl_ofNull_eq, nsl_ofNull_eq, nsl_ofNull_eq, ← map_sub]; rfl

theorem nsl_ofNull_zero : ofNull 0 0 (0 : EuclideanSpace ℝ (Fin d)) = 0 := by
  rw [nsl_ofNull_eq]; exact map_zero _

theorem nsl_ofNull_null (p : Minkowski (d + 1)) : ofNull (nullX p) (nullY p) (nullZ p) = p :=
  ufr_ofNull_null p

theorem nsl_continuous_ofNull :
    Continuous (fun X : ℝ × EuclideanSpace ℝ (Fin d) × ℝ => ofNull X.1 X.2.2 X.2.1) :=
  (ufrCoord (d := d)).symm.toLinearMap.continuous_of_finiteDimensional

theorem nsl_continuous_coord : Continuous (ufrCoord (d := d)) :=
  (ufrCoord (d := d)).toLinearMap.continuous_of_finiteDimensional

theorem nsl_continuous_nullY : Continuous (nullY : Minkowski (d + 1) → ℝ) :=
  continuous_snd.comp (continuous_snd.comp nsl_continuous_coord)

/-- `minkB p v₀ = y(p)`. -/
theorem nsl_minkB_v₀ (p : Minkowski (d + 1)) : minkB p (ofNull 1 0 0) = nullY p := by
  rw [← nsl_ofNull_null p]
  have := BTrivialAux.minkB_nolToMink (d := d) (nullX p, nullZ p, nullY p) (1, 0, 0)
  simp only [BTrivialAux.nolToMink] at this
  rw [this]
  simp [BTrivialAux.nolB, nullY_ofNull]

theorem nsl_minkQ_v₀ : minkQ (ofNull 1 0 (0 : EuclideanSpace ℝ (Fin d))) = 0 := by
  rw [minkQ_eq_null, nullX_ofNull, nullY_ofNull, nullZ_ofNull]; simp

theorem nsl_v₀_ne_zero : ofNull 1 0 (0 : EuclideanSpace ℝ (Fin d)) ≠ 0 := by
  intro h
  have := congrArg nullX h
  rw [nullX_ofNull, ← nsl_ofNull_zero, nullX_ofNull] at this
  exact one_ne_zero this

/-! ### One point per null line, every null line of a met slice -/

/-- **Two points of an acausal set on one `v₀`-line coincide**: their difference is a multiple of
the null vector `v₀`, hence causal. -/
theorem nsl_eq_of_nullY_nullZ {St : Set (Minkowski (d + 1))} (hac : (minkowski (d + 1)).IsAcausal St)
    {p q : Minkowski (d + 1)} (hp : p ∈ St) (hq : q ∈ St) (hy : nullY p = nullY q)
    (hz : nullZ p = nullZ q) : p = q := by
  have key : ∀ a b : Minkowski (d + 1), a ∈ St → b ∈ St → nullY a = nullY b → nullZ a = nullZ b →
      nullX a ≤ nullX b → a = b := by
    intro a b ha hb hy hz hx
    apply hac a ha b hb
    rw [le_top_iff_minkQ]
    rw [← nsl_ofNull_null a, ← nsl_ofNull_null b, nsl_ofNull_sub, hy, hz, sub_self, sub_self]
    refine ⟨?_, ?_⟩
    · show 0 ≤ ((nullX b - nullX a) - 0) / √2
      exact div_nonneg (by linarith) (Real.sqrt_nonneg _)
    · rw [minkQ_eq_null, nullY_ofNull]; simp [nullZ_ofNull]
  rcases le_total (nullX p) (nullX q) with h | h
  · exact key p q hp hq hy hz h
  · exact (key q p hq hp hy.symm hz.symm h).symm

/-- **(CC′)(b) at `ℓ = v₀`** (Cor 8.3, `quoiso`, l.2280–2284): if `S̃` meets the null hyperplane
`{y = y(q)}`, it meets each of its `v₀`-lines. -/
theorem nsl_exists_mem {St : Set (Minkowski (d + 1))} (hns : NullSaturated St) {q : Minkowski (d + 1)}
    (hq : q ∈ St) (z : EuclideanSpace ℝ (Fin d)) : ∃ x : ℝ, ofNull x (nullY q) z ∈ St := by
  obtain ⟨s, hs⟩ := hns q (ofNull 1 0 0) nsl_v₀_ne_zero nsl_minkQ_v₀ ⟨q, hq, by
    rw [sub_self, nsl_minkB_v₀, ← nsl_ofNull_zero, nullY_ofNull]⟩ (ofNull 0 (nullY q) z) (by
      rw [nsl_minkB_v₀, ← nsl_ofNull_null q, nsl_ofNull_sub, nullY_ofNull, nullY_ofNull,
        sub_self])
  refine ⟨s, ?_⟩
  have e : ofNull 0 (nullY q) z + s • ofNull 1 0 (0 : EuclideanSpace ℝ (Fin d)) =
      ofNull s (nullY q) z := by
    rw [nsl_ofNull_eq, nsl_ofNull_eq, nsl_ofNull_eq, ← map_smul, ← map_add]
    congr 1
    simp
  rwa [e] at hs

/-! ### The section over a height -/

/-- The `x`-coordinate of the point of `S̃` over `(z, t)` (junk `0` if there is none). -/
noncomputable def nslX (St : Set (Minkowski (d + 1))) (t : ℝ) (z : EuclideanSpace ℝ (Fin d)) : ℝ :=
  open Classical in
  if h : ∃ x : ℝ, ofNull x t z ∈ St then Classical.choose h else 0

theorem nslX_mem {St : Set (Minkowski (d + 1))} (hcc : CCPrime St) {t : ℝ} (ht : t ∈ nullY '' St)
    (z : EuclideanSpace ℝ (Fin d)) : ofNull (nslX St t z) t z ∈ St := by
  obtain ⟨q, hq, rfl⟩ := ht
  have h := nsl_exists_mem hcc.nullSat hq z
  rw [nslX, dif_pos h]
  exact Classical.choose_spec h

theorem nslX_unique {St : Set (Minkowski (d + 1))} (hcc : CCPrime St) {t x : ℝ}
    {z : EuclideanSpace ℝ (Fin d)} (hx : ofNull x t z ∈ St) : nslX St t z = x := by
  have ht : t ∈ nullY '' St := ⟨_, hx, nullY_ofNull _ _ _⟩
  have h := nsl_eq_of_nullY_nullZ hcc.entire.acausal (nslX_mem hcc ht z) hx
    (by rw [nullY_ofNull, nullY_ofNull]) (by rw [nullZ_ofNull, nullZ_ofNull])
  have := congrArg nullX h
  rwa [nullX_ofNull, nullX_ofNull] at this

/-- **A zero of a family strictly increasing in the first variable is continuous in the second.** -/
theorem nsl_continuous_of_zero {X : Type*} [TopologicalSpace X] {ψ : ℝ → X → ℝ}
    (hc : ∀ a, Continuous (ψ a)) (hm : ∀ z, StrictMono fun a => ψ a z) {h : X → ℝ}
    (hz : ∀ z, ψ (h z) z = 0) : Continuous h := by
  refine continuous_iff_continuousAt.2 fun z => tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · have h1 : ψ a z < 0 := by rw [← hz z]; exact hm z ha
    filter_upwards [(hc a).continuousAt.eventually (gt_mem_nhds h1)] with z' hz'
    by_contra hle
    push Not at hle
    have := (hm z').monotone hle
    rw [hz z'] at this
    linarith
  · have h1 : 0 < ψ b z := by rw [← hz z]; exact hm z hb
    filter_upwards [(hc b).continuousAt.eventually (lt_mem_nhds h1)] with z' hz'
    by_contra hle
    push Not at hle
    have := (hm z').monotone hle
    rw [hz z'] at this
    linarith

/-- The spatial part of `ofNull δ 0 0` has the norm of its time part. -/
theorem nsl_norm_snd_v (δ : ℝ) :
    ‖(ofNull δ 0 (0 : EuclideanSpace ℝ (Fin d))).2‖ = |(ofNull δ 0 (0 : EuclideanSpace ℝ (Fin d))).1| := by
  have h := nsl_minkQ_v₀ (d := d)
  have hq : minkQ (ofNull δ 0 (0 : EuclideanSpace ℝ (Fin d))) = 0 := by
    rw [minkQ_eq_null, nullY_ofNull]; simp [nullZ_ofNull]
  rw [minkQ] at hq
  have h2 : ‖(ofNull δ 0 (0 : EuclideanSpace ℝ (Fin d))).2‖ ^ 2 =
      |(ofNull δ 0 (0 : EuclideanSpace ℝ (Fin d))).1| ^ 2 := by
    rw [sq_abs]; linarith
  exact (pow_left_inj₀ (norm_nonneg _) (abs_nonneg _) two_ne_zero).1 h2

/-- **The section is strictly monotone along `v₀`**: for `S̃ = graph f`, `f` a strict contraction,
`x ↦ time − f(space)` at `ofNull x t z` is strictly increasing. -/
theorem nsl_strictMono_timeSub {f : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} (hf : IsStrictContraction f)
    (t : ℝ) (z : EuclideanSpace ℝ (Fin d)) :
    StrictMono fun x : ℝ => (ofNull x t z).1 - f (ofNull x t z).2 := by
  intro x x' hxx'
  have e : ofNull x' t z = ofNull x t z + ofNull (x' - x) 0 0 := by
    rw [nsl_ofNull_add]; congr 1 <;> simp
  set a := ofNull (x' - x) 0 (0 : EuclideanSpace ℝ (Fin d))
  have ha1 : a.1 = (x' - x) / √2 := by
    show ((x' - x) - 0) / √2 = _; ring
  have hpos : 0 < a.1 := by rw [ha1]; exact div_pos (by linarith) (by positivity)
  have hn : ‖a.2‖ = a.1 := by rw [nsl_norm_snd_v, abs_of_pos hpos]
  have hne : (ofNull x t z).2 + a.2 ≠ (ofNull x t z).2 := by
    intro h0
    have : a.2 = 0 := by simpa using h0
    rw [this, norm_zero] at hn; linarith
  have hc := hf _ _ hne
  rw [add_sub_cancel_left, hn] at hc
  show (ofNull x t z).1 - f (ofNull x t z).2 < (ofNull x' t z).1 - f (ofNull x' t z).2
  rw [e, Prod.fst_add, Prod.snd_add]
  have := (abs_lt.1 hc).2
  linarith

theorem continuous_nslX {St : Set (Minkowski (d + 1))} (hcc : CCPrime St) {t : ℝ}
    (ht : t ∈ nullY '' St) : Continuous (nslX St t) := by
  obtain ⟨f, hf, hSt⟩ := isEntireAcausalGraph_iff.1 hcc.entire
  have hfc : Continuous f := hf.lipschitzWith.continuous
  have hcont : Continuous fun X : ℝ × EuclideanSpace ℝ (Fin d) => ofNull X.1 t X.2 :=
    nsl_continuous_ofNull.comp (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))
  refine nsl_continuous_of_zero (ψ := fun x z => (ofNull x t z).1 - f (ofNull x t z).2)
    (fun a => ?_) (fun z => nsl_strictMono_timeSub hf t z) (fun z => ?_)
  · have h2 : Continuous fun z : EuclideanSpace ℝ (Fin d) => ofNull a t z :=
      hcont.comp (continuous_const.prodMk continuous_id)
    exact (continuous_fst.comp h2).sub (hfc.comp (continuous_snd.comp h2))
  · have h := nslX_mem hcc ht z
    have h' : ofNull (nslX St t z) t z ∈ graph f := hSt ▸ h
    show (ofNull (nslX St t z) t z).1 - f (ofNull (nslX St t z) t z).2 = 0
    rw [mem_graph] at h'
    rw [h', sub_self]

/-- The section `z ↦ ofNull (nslX S̃ t z) t z`. -/
noncomputable def nslSection (St : Set (Minkowski (d + 1))) (t : ℝ)
    (z : EuclideanSpace ℝ (Fin d)) : Minkowski (d + 1) :=
  ofNull (nslX St t z) t z

theorem continuous_nslSection {St : Set (Minkowski (d + 1))} (hcc : CCPrime St) {t : ℝ}
    (ht : t ∈ nullY '' St) : Continuous (nslSection St t) :=
  nsl_continuous_ofNull.comp ((continuous_nslX hcc ht).prodMk
    (continuous_id.prodMk continuous_const))

/-- **The section over a compact set is a compact subset of `S̃`** (point (3), l.2660–2663: what
the properness of `α(Γ)` on the slice reads off from that of `Γ` on `S̃`). -/
theorem isCompact_nslSection {St : Set (Minkowski (d + 1))} (hcc : CCPrime St) {t : ℝ}
    (ht : t ∈ nullY '' St) {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K) :
    IsCompact (nslSection St t '' K) ∧ nslSection St t '' K ⊆ St :=
  ⟨hK.image (continuous_nslSection hcc ht), by
    rintro _ ⟨z, -, rfl⟩; exact nslX_mem hcc ht z⟩

/-! ### The heights -/

theorem nsl_heights_ordConnected {St : Set (Minkowski (d + 1))} (hcc : CCPrime St) :
    (nullY '' St).OrdConnected := by
  obtain ⟨f, hf, hSt⟩ := isEntireAcausalGraph_iff.1 hcc.entire
  have hfc : Continuous f := hf.lipschitzWith.continuous
  have hr : St = range fun s : EuclideanSpace ℝ (Fin (d + 1)) => ((f s, s) : Minkowski (d + 1)) := by
    rw [hSt]; ext p
    simp only [mem_graph, mem_range]
    exact ⟨fun h => ⟨p.2, by rw [← h]⟩, by rintro ⟨s, rfl⟩; rfl⟩
  rw [hr, ← range_comp]
  exact (isPreconnected_range (nsl_continuous_nullY.comp
    ((hfc.prodMk continuous_id)))).ordConnected

theorem nsl_heights_shift {St : Set (Minkowski (d + 1))} (hcc : CCPrime St) {t : ℝ}
    (ht : t ∈ nullY '' St) (c : ℝ) (hc : c ≠ 0) :
    ∃ t' ∈ nullY '' St, t' ≠ t ∧ (0 < c → t < t') ∧ (c < 0 → t' < t) := by
  obtain ⟨f, hf, hSt⟩ := isEntireAcausalGraph_iff.1 hcc.entire
  obtain ⟨q, hq, rfl⟩ := ht
  set e : EuclideanSpace ℝ (Fin (d + 1)) := EuclideanSpace.single 0 c
  set q' : Minkowski (d + 1) := (f (q.2 + e), q.2 + e)
  have hq' : q' ∈ St := by rw [hSt]; rfl
  have hq1 : q.1 = f q.2 := by rw [hSt] at hq; exact hq
  have hne : q.2 + e ≠ q.2 := by
    intro h0
    have : e = 0 := by simpa using h0
    have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin (d + 1)) => v 0) this
    simp [e] at h1
    exact hc h1
  have hcon := hf _ _ hne
  have hen : ‖e‖ = |c| := by simp [e]
  rw [add_sub_cancel_left, hen] at hcon
  have hy : nullY q' - nullY q = (c - (f (q.2 + e) - f q.2)) / √2 := by
    simp only [nullY, q', hq1, PiLp.add_apply, e]
    simp; ring
  have hs : (0 : ℝ) < √2 := by positivity
  have hlt := abs_lt.1 hcon
  refine ⟨nullY q', ⟨q', hq', rfl⟩, ?_, fun h => ?_, fun h => ?_⟩
  · intro h0
    rw [h0, sub_self] at hy
    have : c - (f (q.2 + e) - f q.2) = 0 := by
      rcases (div_eq_zero_iff.1 hy.symm) with h | h
      · exact h
      · exact absurd h hs.ne'
    rcases lt_or_gt_of_ne hc with hc' | hc'
    · rw [abs_of_neg hc'] at hlt; linarith
    · rw [abs_of_pos hc'] at hlt; linarith
  · rw [abs_of_pos h] at hlt
    have : 0 < nullY q' - nullY q := by rw [hy]; exact div_pos (by linarith) hs
    linarith
  · rw [abs_of_neg h] at hlt
    have : nullY q' - nullY q < 0 := by rw [hy]; exact div_neg_of_neg_of_pos (by linarith) hs
    linarith

theorem nsl_heights_noMax {St : Set (Minkowski (d + 1))} (hcc : CCPrime St) {t : ℝ}
    (ht : t ∈ nullY '' St) : ∃ t' ∈ nullY '' St, t < t' := by
  obtain ⟨t', ht', -, h, -⟩ := nsl_heights_shift hcc ht 1 one_ne_zero
  exact ⟨t', ht', h one_pos⟩

theorem nsl_heights_noMin {St : Set (Minkowski (d + 1))} (hcc : CCPrime St) {t : ℝ}
    (ht : t ∈ nullY '' St) : ∃ t' ∈ nullY '' St, t' < t := by
  obtain ⟨t', ht', -, -, h⟩ := nsl_heights_shift hcc ht (-1) (by norm_num)
  exact ⟨t', ht', h (by norm_num)⟩

/-! ### The normalisation `y₋ = −y₊` (l.2934–2938) -/

/-- **An open interval of `ℝ`, recentred**: a nonempty order-connected `I ⊆ ℝ` without max or
min has a point `y₀` and ends `ylo < 0 < yhi` (in `EReal`) after the shift by `y₀`, normalised
(`ylo = −yhi` when both are finite). -/
theorem nsl_exists_normalisation {I : Set ℝ} (hne : I.Nonempty) (hc : I.OrdConnected)
    (hmax : ∀ t ∈ I, ∃ t' ∈ I, t < t') (hmin : ∀ t ∈ I, ∃ t' ∈ I, t' < t) :
    ∃ y₀ ∈ I, ∃ ylo yhi : EReal, ylo < 0 ∧ 0 < yhi ∧ (ylo = -yhi ∨ yhi = ⊤ ∨ ylo = ⊥) ∧
      ∀ y : ℝ, (ylo < (y : EReal) ∧ (y : EReal) < yhi) ↔ y + y₀ ∈ I := by
  have hmemI : ∀ a b t : ℝ, a ∈ I → b ∈ I → a ≤ t → t ≤ b → t ∈ I :=
    fun a b t ha hb h1 h2 => hc.out ha hb ⟨h1, h2⟩
  by_cases hA : BddAbove I <;> by_cases hB : BddBelow I
  · -- both ends finite
    set a := sInf I
    set b := sSup I
    have hIoo : ∀ t, t ∈ I ↔ a < t ∧ t < b := by
      intro t
      constructor
      · intro ht
        obtain ⟨t₁, ht₁, h₁⟩ := hmin t ht
        obtain ⟨t₂, ht₂, h₂⟩ := hmax t ht
        exact ⟨lt_of_le_of_lt (csInf_le hB ht₁) h₁, lt_of_lt_of_le h₂ (le_csSup hA ht₂)⟩
      · rintro ⟨h1, h2⟩
        obtain ⟨t₁, ht₁, h₁⟩ := exists_lt_of_csInf_lt hne h1
        obtain ⟨t₂, ht₂, h₂⟩ := exists_lt_of_lt_csSup hne h2
        exact hmemI t₁ t₂ t ht₁ ht₂ h₁.le h₂.le
    obtain ⟨t, ht⟩ := hne
    have hab := (hIoo t).1 ht
    have hab' : a < b := hab.1.trans hab.2
    refine ⟨(a + b) / 2, (hIoo _).2 ⟨by linarith, by linarith⟩, (((a - b) / 2 : ℝ) : EReal),
      (((b - a) / 2 : ℝ) : EReal), ?_, ?_, Or.inl ?_, fun y => ?_⟩
    · exact_mod_cast (by linarith : (a - b) / 2 < 0)
    · exact_mod_cast (by linarith : (0 : ℝ) < (b - a) / 2)
    · rw [← EReal.coe_neg]; congr 1; ring
    · rw [EReal.coe_lt_coe_iff, EReal.coe_lt_coe_iff, hIoo]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  · -- bounded above only: `I = ]−∞, b[`
    set b := sSup I
    have hIio : ∀ t, t ∈ I ↔ t < b := by
      intro t
      constructor
      · intro ht
        obtain ⟨t₂, ht₂, h₂⟩ := hmax t ht
        exact lt_of_lt_of_le h₂ (le_csSup hA ht₂)
      · intro h2
        obtain ⟨t₂, ht₂, h₂⟩ := exists_lt_of_lt_csSup hne h2
        obtain ⟨t₁, ht₁, h₁⟩ := not_bddBelow_iff.1 hB t
        exact hmemI t₁ t₂ t ht₁ ht₂ h₁.le h₂.le
    refine ⟨b - 1, (hIio _).2 (by linarith), ⊥, ((1 : ℝ) : EReal), EReal.bot_lt_coe 0,
      by exact_mod_cast one_pos, Or.inr (Or.inr rfl), fun y => ?_⟩
    rw [hIio, EReal.coe_lt_coe_iff]
    constructor
    · rintro ⟨-, h⟩; linarith
    · intro h; exact ⟨EReal.bot_lt_coe y, by linarith⟩
  · -- bounded below only: `I = ]a, +∞[`
    set a := sInf I
    have hIoi : ∀ t, t ∈ I ↔ a < t := by
      intro t
      constructor
      · intro ht
        obtain ⟨t₁, ht₁, h₁⟩ := hmin t ht
        exact lt_of_le_of_lt (csInf_le hB ht₁) h₁
      · intro h1
        obtain ⟨t₁, ht₁, h₁⟩ := exists_lt_of_csInf_lt hne h1
        obtain ⟨t₂, ht₂, h₂⟩ := not_bddAbove_iff.1 hA t
        exact hmemI t₁ t₂ t ht₁ ht₂ h₁.le h₂.le
    refine ⟨a + 1, (hIoi _).2 (by linarith), (((-1 : ℝ)) : EReal), ⊤,
      by exact_mod_cast (by norm_num : (-1 : ℝ) < 0), EReal.coe_lt_top 0, Or.inr (Or.inl rfl),
      fun y => ?_⟩
    rw [hIoi, EReal.coe_lt_coe_iff]
    constructor
    · rintro ⟨h, -⟩; linarith
    · intro h; exact ⟨by linarith, EReal.coe_lt_top y⟩
  · -- `I = ℝ`
    have huniv : ∀ t, t ∈ I := by
      intro t
      obtain ⟨t₁, ht₁, h₁⟩ := not_bddBelow_iff.1 hB t
      obtain ⟨t₂, ht₂, h₂⟩ := not_bddAbove_iff.1 hA t
      exact hmemI t₁ t₂ t ht₁ ht₂ h₁.le h₂.le
    refine ⟨0, huniv 0, ⊥, ⊤, EReal.bot_lt_coe 0, EReal.coe_lt_top 0, Or.inr (Or.inl rfl),
      fun y => ⟨fun _ => huniv _, fun _ => ⟨EReal.bot_lt_coe y, EReal.coe_lt_top y⟩⟩⟩

end Causal.Flat.Nonlox
