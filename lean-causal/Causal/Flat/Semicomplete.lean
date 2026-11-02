import Causal.Flat.AgissonsGeneral

/-!
# `Causal.Flat.Semicomplete` — geodesic (semi)completeness, and Barbot Prop 4.16 in full

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §2 and
§4.3; line numbers are those of the labelled `papers/barbot/legacy/labeled/GHFspace.tex`. Barbot's
`𝐌ⁿ` has total dimension `n`; the library's `Minkowski d` has `d` spatial dimensions (kb/0024).
Label certified:

* **`bprop:agissons`** — `GHFspace.tex:1174` (`bprop_agissons_full`: properly discontinuous;
  for torsion-free `Γ`, free, and `Γ\Ω` a Cauchy-complete **semicomplete** GH flat spacetime),
  in the readings of `Flat/AgissonsGeneral.lean` (DEC-88 regular domain, DEC-35 Cauchy-complete,
  `ρ(Γ)` read as `Γ`) and with "semicomplete" defined here (DEC-103); no `sorry`.

Definitions (unlabelled prose of §2, l.444–451): `IsGeodesicOn`, `IsGeodesicallyCompleteFor`,
`IsFutureGeodesicallyComplete`, `IsPastGeodesicallyComplete`, `IsGeodesicallySemicomplete`, and
the stronger `IsFutureCausallyGeodesicallyComplete` (timelike and null rays).

> A spacetime is geodesically complete if every timelike geodesics admit geodesic
> parame\-trizations by $]-\infty, +\infty[$. It is \emph{geodesically complete in the future}
> (resp., in the past) if every future oriented (resp. past oriented) timelike geodesic ray admits
> a geodesic parametrization by $]0, +\infty[$. Finally, a \emph{geodesically semicomplete\/}
> spacetime is a spacetime which is either geodesically complete in the future or geodesically
> complete in the past. (l.444–451)

> If $\Gamma$ preserves a future complete regular convex domain $\Omega$, then, the action of
> $\rho(\Gamma)$ on $\Omega$ is properly discontinuous. If moreover $\Gamma$ is torsionfree, then
> this action is free, and the quotient $\Gamma\backslash\Omega$ is a Cauchy-complete semicomplete
> GH spacetime. (l.1176–1180)

## The definitions

A **geodesic** of a flat spacetime `M` on a set `s ⊆ ℝ` (`IsGeodesicOn P c s`) is a curve
`c : ℝ → M` which is, at every `t ∈ s`, read in the chart at `c t`, an affinely parametrised
straight line `t' ↦ chart(c t) + (t' − t) v` near `t` (within `s`), with velocity `v` satisfying
`P`. A geodesic is continuous on `s` (`IsGeodesicOn.continuousOn`), and on a preconnected `s` a
geodesic is determined by its germ at one point (`IsGeodesicOn.eqOn_of_eventuallyEq`, `M`
Hausdorff): that uniqueness is what makes "the maximal geodesic" meaningful, and the
completeness notion below is its extension form. `M` is **geodesically complete for `P`** if every
geodesic ray `c` on `[0, a)`, `a > 0`, with `P`-velocities, extends to a geodesic on `[0, ∞)`
(`IsGeodesicallyCompleteFor`). Future: `P = IsFutureTimelike`; past: `P v = IsFutureTimelike (−v)`;
semicomplete: future or past (l.450).

## How it is proved

`isGeodesicallyCompleteFor_of_isLocalIsometry`: if `π : Ω → M` is a surjective local isometry
from an open `Ω ⊆ 𝐌ⁿ` which is future complete as a set (`p ∈ Ω`, `v` future causal, `t ≥ 0` ⇒
`p + t v ∈ Ω`), then `M` is geodesically complete for every `P` contained in the future causal
cone and invariant under `SO₀(1, d)`. Lift the germ of the ray at `0` through the chart of `π`
at a preimage `p` of `c 0` (`chart(π y) = g • y` near `p`): it is `π(p + t w)`, `w = L(g)⁻¹ v`;
the straight line `p + t w` stays in `Ω` for all `t ≥ 0`, `π` maps it to a geodesic on `[0, ∞)`
(its velocity in the chart at `π(p + t₀ w)` is `L(g') w`), and uniqueness of geodesics makes it
agree with `c` on all of `[0, a)`. For `Ω = Ω⁺(Λ)` future completeness is
`add_smul_mem_omegaPlus` (l.909), so **every** quotient `M` of `Ω⁺(Λ)` (`IsQuotientOf`) is future
geodesically complete, for timelike and for null rays (`isFutureGeodesicallyComplete_of_isQuotientOf`).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `Γ` discrete in `Isom(𝐌ⁿ)`, preserves `Ω`, `Ω` future complete regular convex | ✓ as in `bprop_agissons_general`: `DiscreteTopology Γ`, `PreservesOmega Λ Γ`, `Ω = Ω⁺(Λ)`, `CosmoRegular Λ` (DEC-88) |
| `Γ` torsion-free | ✓ carried (`IsTorsionFreeSubgroup Γ`) |
| "semicomplete" (l.450) | ✓ `IsGeodesicallySemicomplete` (DEC-103); proved in the future form, for timelike and null rays, for any quotient of `Ω⁺(Λ)`: no hypothesis on `Γ` is used |
| "Cauchy-complete", "GH" | ✓ as in `bprop_agissons_general` (DEC-35; ETT's `GH` and an acausal Cauchy surface) |

## SCOPE (disclosed)

* **Reading of "geodesic"** (DEC-103): affinely parametrised, read in the preferred chart
  `chartAt (c t)`. The transitions of a flat spacetime's atlas are locally elements of
  `Isom(𝐌ⁿ)`, affine with linear part in `SO₀(1, d)`, so the notion and the time orientation of
  the velocity do not depend on the atlas chart chosen; that independence is not formalized here.
  "Timelike geodesic ray … parametrization by `]0, +∞[`" is read as: every geodesic on `[0, a)`
  extends to one on `[0, ∞)` (equivalently, with uniqueness, the maximal geodesic of its initial
  data is defined on `[0, ∞)`); the closed or open end at `0` is immaterial.
* The paper's completeness is about **timelike** rays (l.446–448); the quotients are also proved
  complete for **null** rays (`IsFutureCausallyGeodesicallyComplete`), which is stronger.
* Non-vacuity of the notion (kb/0011): `𝐌ⁿ` is future complete
  (`isFutureGeodesicallyComplete_minkowskiSpace`), the open half-space `{x₀ < 1}` is not
  (`not_isFutureGeodesicallyComplete_halfSpace`). Non-vacuity of the hypotheses of
  `bprop_agissons_full`: `bprop_agissons_general_cone` (the trivial group on the future cone).
* `Flat/AgissonsGeneral.lean`'s readings carry over unchanged: `ρ(Γ)` read as `Γ`; the
  Riemannian argument on `S_t` replaced by the Gauss map.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign.
-/

namespace Causal.Flat

open Set Function TopologicalSpace Topology Filter
open scoped Pointwise

universe u

variable {d : ℕ}

section Geodesic

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (Minkowski d) M]

/-- **A geodesic on `s` with velocities in `P`**: at every `t ∈ s`, read in the chart at `c t`,
`c` is near `t` (within `s`) the affinely parametrised straight line `t' ↦ chart(c t) + (t' − t) v`,
for a velocity `v` with `P v`. -/
def IsGeodesicOn (P : Minkowski d → Prop) (c : ℝ → M) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, ∃ v, P v ∧ ∀ᶠ t' in 𝓝[s] t, c t' ∈ (chartAt (Minkowski d) (c t)).source ∧
    chartAt (Minkowski d) (c t) (c t') = chartAt (Minkowski d) (c t) (c t) + (t' - t) • v

variable (d) in
/-- **Geodesic completeness for `P`**: every geodesic ray `c` on `[0, a)`, `a > 0`, with
velocities in `P`, extends to a geodesic on `[0, ∞)` with velocities in `P`. -/
def IsGeodesicallyCompleteFor (P : Minkowski d → Prop) (M : Type u) [TopologicalSpace M]
    [ChartedSpace (Minkowski d) M] : Prop :=
  ∀ a : ℝ, 0 < a → ∀ c : ℝ → M, IsGeodesicOn P c (Ico 0 a) →
    ∃ c' : ℝ → M, IsGeodesicOn P c' (Ici 0) ∧ EqOn c' c (Ico 0 a)

variable (d) in
/-- **Geodesically complete in the future** (l.446–448): every future oriented timelike geodesic
ray extends to `[0, ∞)`. -/
def IsFutureGeodesicallyComplete (M : Type u) [TopologicalSpace M]
    [ChartedSpace (Minkowski d) M] : Prop :=
  IsGeodesicallyCompleteFor d (IsFutureTimelike (d := d)) M

variable (d) in
/-- **Geodesically complete in the past** (l.446–448): every past oriented timelike geodesic ray
extends to `[0, ∞)`. -/
def IsPastGeodesicallyComplete (M : Type u) [TopologicalSpace M]
    [ChartedSpace (Minkowski d) M] : Prop :=
  IsGeodesicallyCompleteFor d (fun v : Minkowski d => IsFutureTimelike (-v)) M

variable (d) in
/-- **Geodesically semicomplete** (l.449–451): geodesically complete in the future or in the past. -/
def IsGeodesicallySemicomplete (M : Type u) [TopologicalSpace M]
    [ChartedSpace (Minkowski d) M] : Prop :=
  IsFutureGeodesicallyComplete d M ∨ IsPastGeodesicallyComplete d M

variable (d) in
/-- **Future complete for causal rays**, timelike and null (stronger than the paper's notion):
every future oriented nonconstant causal geodesic ray extends to `[0, ∞)`. -/
def IsFutureCausallyGeodesicallyComplete (M : Type u) [TopologicalSpace M]
    [ChartedSpace (Minkowski d) M] : Prop :=
  IsGeodesicallyCompleteFor d (fun v : Minkowski d => IsFutureCausal v ∧ v ≠ 0) M

theorem IsGeodesicOn.mono {P : Minkowski d → Prop} {c : ℝ → M} {s s' : Set ℝ}
    (h : IsGeodesicOn P c s) (hs : s' ⊆ s) : IsGeodesicOn P c s' := fun t ht =>
  let ⟨v, hv, h'⟩ := h t (hs ht)
  ⟨v, hv, h'.filter_mono (nhdsWithin_mono _ hs)⟩

/-- A geodesic is continuous within its domain at each of its points. -/
theorem IsGeodesicOn.continuousWithinAt {P : Minkowski d → Prop} {c : ℝ → M} {s : Set ℝ}
    (h : IsGeodesicOn P c s) {t : ℝ} (ht : t ∈ s) : ContinuousWithinAt c s t := by
  obtain ⟨v, -, h'⟩ := h t ht
  set e := chartAt (Minkowski d) (c t)
  have hct : c t ∈ e.source := mem_chart_source _ _
  have hf : ContinuousAt (fun t' : ℝ => e.symm (e (c t) + (t' - t) • v)) t := by
    have h1 : ContinuousAt e.symm (e (c t) + (t - t) • v) := by
      rw [sub_self, zero_smul, add_zero]; exact e.continuousAt_symm (e.map_source hct)
    exact h1.comp (f := fun t' : ℝ => e (c t) + (t' - t) • v) (by fun_prop)
  refine hf.continuousWithinAt.congr_of_eventuallyEq
    (h'.mono fun t' h'' => by show c t' = e.symm _; rw [← h''.2, e.left_inv h''.1]) ?_
  simp [e.left_inv hct]

theorem IsGeodesicOn.continuousOn {P : Minkowski d → Prop} {c : ℝ → M} {s : Set ℝ}
    (h : IsGeodesicOn P c s) : ContinuousOn c s := fun _ ht => h.continuousWithinAt ht

/-- **Uniqueness of geodesics**: on a preconnected set, two geodesics (of a Hausdorff flat
spacetime) with the same germ at one point agree. -/
theorem IsGeodesicOn.eqOn_of_eventuallyEq [T2Space M] {P Q : Minkowski d → Prop} {c c' : ℝ → M}
    {s : Set ℝ} (hs : IsPreconnected s) (hc : IsGeodesicOn P c s) (hc' : IsGeodesicOn Q c' s)
    {t₀ : ℝ} (ht₀ : t₀ ∈ s) (h0 : c =ᶠ[𝓝[s] t₀] c') : EqOn c c' s := by
  haveI : PreconnectedSpace s := Subtype.preconnectedSpace hs
  let A : Set s := {t | ∀ᶠ t' in 𝓝[s] (t : ℝ), c t' = c' t'}
  have hA : A = {t : s | ∀ᶠ t' : s in 𝓝 t, c t' = c' t'} := by
    ext t; exact (eventually_nhds_subtype_iff s t (fun x => c x = c' x)).symm
  have hAo : IsOpen A := by rw [hA]; exact isOpen_setOf_eventually_nhds
  have hcont : Continuous (s.restrict c) := hc.continuousOn.restrict
  have hcont' : Continuous (s.restrict c') := hc'.continuousOn.restrict
  have hB : IsClosed {t : s | c t = c' t} := isClosed_eq hcont hcont'
  have hAB : A ⊆ {t : s | c t = c' t} := fun t ht => ht.self_of_nhdsWithin t.2
  have hAc : IsClosed A := by
    refine isClosed_of_closure_subset fun t ht => ?_
    have hct : c t = c' t := hB.closure_subset_iff.2 hAB ht
    obtain ⟨v₁, -, h1⟩ := hc t t.2
    obtain ⟨v₂, -, h2⟩ := hc' t t.2
    rw [← hct] at h2
    set e := chartAt (Minkowski d) (c t)
    have h12 : ∀ᶠ x : s in 𝓝 t, (c x ∈ e.source ∧ e (c x) = e (c t) + ((x : ℝ) - t) • v₁) ∧
        (c' x ∈ e.source ∧ e (c' x) = e (c t) + ((x : ℝ) - t) • v₂) :=
      (eventually_nhds_subtype_iff s t _).2 (h1.and h2)
    obtain ⟨t₁, ht₁A, ⟨-, he1⟩, -, he2⟩ :=
      ((mem_closure_iff_frequently.1 ht).and_eventually h12).exists
    by_cases htt : (t₁ : ℝ) = t
    · have : t₁ = t := Subtype.ext htt
      rwa [this] at ht₁A
    · have hv : v₁ = v₂ := by
        have h3 : c t₁ = c' t₁ := hAB ht₁A
        rw [h3, he2, add_right_inj] at he1
        exact smul_right_injective _ (sub_ne_zero.2 htt) he1.symm
      show ∀ᶠ t' in 𝓝[s] (t : ℝ), c t' = c' t'
      filter_upwards [h1, h2] with t' h1' h2'
      exact e.injOn h1'.1 h2'.1 (by rw [h1'.2, h2'.2, hv])
  have hAu : A = univ := (IsClopen.eq_univ ⟨hAc, hAo⟩ ⟨⟨t₀, ht₀⟩, h0⟩)
  intro t ht
  have : (⟨t, ht⟩ : s) ∈ A := hAu ▸ mem_univ _
  exact this.self_of_nhdsWithin ht

end Geodesic

section Complete

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (Minkowski d) M]

/-- **Geodesic completeness from a future complete developing domain**: if `π : Ω → M` is a
surjective local isometry from an open `Ω ⊆ 𝐌ⁿ` which is future complete as a set, then `M` is
geodesically complete for every velocity class `P` contained in the future causal cone and
invariant under `SO₀(1, d)`. -/
theorem isGeodesicallyCompleteFor_of_isLocalIsometry [T2Space M] {P : Minkowski d → Prop}
    (hPc : ∀ v, P v → IsFutureCausal v) (hPL : ∀ A ∈ lorentz d, ∀ v, P (A v) ↔ P v)
    {Ω : Opens (Minkowski d)}
    (hΩ : ∀ p ∈ Ω, ∀ v, IsFutureCausal v → ∀ t : ℝ, 0 ≤ t → p + t • v ∈ Ω)
    {π : Ω → M} (hπ : IsLocalIsometry d π) (hsurj : Surjective π) :
    IsGeodesicallyCompleteFor d P M := by
  intro a ha c hc
  obtain ⟨v, hPv, hev⟩ := hc 0 ⟨le_rfl, ha⟩
  obtain ⟨p, hp⟩ := hsurj (c 0)
  obtain ⟨hπc, hloc⟩ := isLocalIsometry_iff_eventually.1 hπ
  obtain ⟨g, hg⟩ := hloc p
  set w := (linOf g).symm v with hw
  have hgw : linOf g w = v := linOf_symm_apply g v
  have hPw : P w := (hPL _ (linOf_mem g) w).1 (by rw [hgw]; exact hPv)
  have hwc : IsFutureCausal w := hPc w hPw
  let ℓ : ℝ → Ω := fun t => ⟨p + max t 0 • w, hΩ p p.2 w hwc _ (le_max_right _ _)⟩
  have hℓ : Continuous ℓ := by
    refine Continuous.subtype_mk ?_ _
    fun_prop
  have hℓv : ∀ t, 0 ≤ t → ((ℓ t : Ω) : Minkowski d) = p + t • w := fun t ht => by
    simp [ℓ, max_eq_left ht]
  have hℓ0 : ℓ 0 = p := Subtype.ext (by simp [ℓ])
  -- the candidate extension `t ↦ π(p + t w)` is a geodesic on `[0, ∞)`
  have hgeo : IsGeodesicOn P (fun t => π (ℓ t)) (Ici 0) := by
    intro t₀ ht₀
    obtain ⟨g', hg'⟩ := hloc (ℓ t₀)
    refine ⟨linOf g' w, (hPL _ (linOf_mem g') w).2 hPw, ?_⟩
    have h1 : ∀ᶠ t in 𝓝 t₀, chartAt (Minkowski d) (π (ℓ t₀)) (π (ℓ t)) =
        g' • chartAt (Minkowski d) (ℓ t₀) (ℓ t) := hℓ.continuousAt.eventually hg'
    have h2 : ∀ᶠ t in 𝓝 t₀, π (ℓ t) ∈ (chartAt (Minkowski d) (π (ℓ t₀))).source :=
      (hπc.comp hℓ).continuousAt.eventually
        ((chartAt (Minkowski d) (π (ℓ t₀))).open_source.mem_nhds (mem_chart_source _ _))
    have h0 : chartAt (Minkowski d) (π (ℓ t₀)) (π (ℓ t₀)) = g' • (p + t₀ • w) := by
      rw [hg'.self_of_nhds, chartAt_opens_apply, hℓv t₀ ht₀]
    filter_upwards [nhdsWithin_le_nhds h1, nhdsWithin_le_nhds h2, self_mem_nhdsWithin]
      with t ht1 ht2 (ht : 0 ≤ t)
    refine ⟨ht2, ?_⟩
    rw [ht1, h0, chartAt_opens_apply, hℓv t ht, ← isom_smul_add_smul]
    congr 1
    rw [add_assoc, ← add_smul, add_sub_cancel]
  refine ⟨fun t => π (ℓ t), hgeo, ?_⟩
  -- it has the germ of `c` at `0`, so agrees with `c` on `[0, a)`
  have hgerm : c =ᶠ[𝓝[Ico 0 a] 0] fun t => π (ℓ t) := by
    rw [← hp] at hev
    have hT : Tendsto ℓ (𝓝 0) (𝓝 p) := hℓ0 ▸ hℓ.tendsto 0
    have h1 : ∀ᶠ t in 𝓝 (0 : ℝ), chartAt (Minkowski d) (π p) (π (ℓ t)) =
        g • chartAt (Minkowski d) p (ℓ t) := hT.eventually hg
    have h2 : ∀ᶠ t in 𝓝 (0 : ℝ), π (ℓ t) ∈ (chartAt (Minkowski d) (π p)).source :=
      ((hπc.tendsto p).comp hT).eventually
        ((chartAt (Minkowski d) (π p)).open_source.mem_nhds (mem_chart_source _ _))
    have h0 : chartAt (Minkowski d) (π p) (π p) = g • (p : Minkowski d) := by
      rw [hg.self_of_nhds, chartAt_opens_apply]
    filter_upwards [hev, nhdsWithin_le_nhds h1, nhdsWithin_le_nhds h2, self_mem_nhdsWithin]
      with t hev' ht1 ht2 (ht : t ∈ Ico 0 a)
    refine (chartAt (Minkowski d) (π p)).injOn hev'.1 ht2 ?_
    rw [hev'.2, ht1, h0, chartAt_opens_apply, hℓv t ht.1, isom_smul_add_smul, hgw, sub_zero]
  exact ((hc.eqOn_of_eventuallyEq isPreconnected_Ico (hgeo.mono Ico_subset_Ici_self)
    ⟨le_rfl, ha⟩ hgerm)).symm

/-- The future timelike velocities satisfy the hypotheses of
`isGeodesicallyCompleteFor_of_isLocalIsometry`. -/
theorem isFutureGeodesicallyComplete_of_isLocalIsometry [T2Space M] {Ω : Opens (Minkowski d)}
    (hΩ : ∀ p ∈ Ω, ∀ v, IsFutureCausal v → ∀ t : ℝ, 0 ≤ t → p + t • v ∈ Ω)
    {π : Ω → M} (hπ : IsLocalIsometry d π) (hsurj : Surjective π) :
    IsFutureGeodesicallyComplete d M ∧ IsFutureCausallyGeodesicallyComplete d M :=
  ⟨isGeodesicallyCompleteFor_of_isLocalIsometry (fun _ hv => hv.isFutureCausal)
      (fun _ hA _ => lorentz.isFutureTimelike_apply_iff hA) hΩ hπ hsurj,
    isGeodesicallyCompleteFor_of_isLocalIsometry (fun _ hv => hv.1)
      (fun A hA _ => and_congr (lorentz.isFutureCausal_apply_iff hA) A.map_ne_zero_iff)
      hΩ hπ hsurj⟩

variable {Λ : Set (PenroseSphere d × ℝ)} {Γ : Subgroup (isom d)}

/-- **Every quotient of `Ω⁺(Λ)` is future geodesically complete**, for timelike and for null
rays: no hypothesis on `Γ` is used beyond `M` being the quotient `Γ\Ω⁺(Λ)`. -/
theorem isFutureGeodesicallyComplete_of_isQuotientOf (hc : CosmoRegular Λ) [T2Space M]
    (hM : IsQuotientOf M Γ hc.regular.opens) :
    IsFutureGeodesicallyComplete d M ∧ IsFutureCausallyGeodesicallyComplete d M := by
  obtain ⟨π, -, hπ, hsurj, -⟩ := hM.quot
  exact isFutureGeodesicallyComplete_of_isLocalIsometry
    (fun p hp _ hv _ ht => add_smul_mem_omegaPlus (Λ := Λ) hp hv ht) hπ hsurj

/-- The same, as Barbot's semicompleteness. -/
theorem isGeodesicallySemicomplete_of_isQuotientOf (hc : CosmoRegular Λ) [T2Space M]
    (hM : IsQuotientOf M Γ hc.regular.opens) : IsGeodesicallySemicomplete d M :=
  Or.inl (isFutureGeodesicallyComplete_of_isQuotientOf hc hM).1

end Complete

/-! ### Non-vacuity of the notion -/

section Witnesses

/-- **`𝐌ⁿ` is future geodesically complete** (timelike and null rays). -/
theorem isFutureGeodesicallyComplete_minkowskiSpace :
    IsFutureGeodesicallyComplete d (FlatSpacetime.minkowskiSpace d) ∧
      IsFutureCausallyGeodesicallyComplete d (FlatSpacetime.minkowskiSpace d) :=
  isFutureGeodesicallyComplete_of_isLocalIsometry (Ω := ⊤) (fun _ _ _ _ _ _ => trivial)
    (isLocalIsometry_subtype_val (M := Minkowski d) ⊤) fun x => ⟨⟨x, trivial⟩, rfl⟩

/-- The open half-space `{x₀ < 1}` of `𝐌ⁿ`. -/
def halfSpaceLtOne (d : ℕ) : Opens (Minkowski d) :=
  ⟨{p | p.1 < 1}, isOpen_lt continuous_fst continuous_const⟩

/-- **The half-space `{x₀ < 1}` is not future geodesically complete**: the ray `t ↦ (t, 0)`
leaves it at `t = 1`. -/
theorem not_isFutureGeodesicallyComplete_halfSpace :
    ¬ IsFutureGeodesicallyComplete d (halfSpaceLtOne d) := by
  intro h
  let W := halfSpaceLtOne d
  have hW0 : ((0 : ℝ), (0 : EuclideanSpace ℝ (Fin d))) ∈ W := show (0 : ℝ) < 1 from one_pos
  let c : ℝ → W := fun t =>
    if ht : t < 1 then ⟨(t, 0), show t < 1 from ht⟩ else ⟨(0, 0), hW0⟩
  have hcv : ∀ t, t < 1 → ((c t : W) : Minkowski d) = (t, 0) := fun t ht => by
    simp [c, ht]
  have hv : IsFutureTimelike ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin d))) :=
    ⟨one_pos, by simp [minkQ]⟩
  have hgeo : IsGeodesicOn (IsFutureTimelike (d := d)) c (Ico 0 1) := by
    intro t₀ ht₀
    refine ⟨((1 : ℝ), 0), hv, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t (ht : t ∈ Ico 0 1)
    refine ⟨?_, ?_⟩
    · rw [TopologicalSpace.Opens.chartAt_eq]
      simp [OpenPartialHomeomorph.subtypeRestr]
    · rw [chartAt_opens_apply, chartAt_opens_apply, hcv t ht.2, hcv t₀ ht₀.2]
      ext <;> simp
  obtain ⟨c', hc', heq⟩ := h 1 one_pos c hgeo
  have hcont : ContinuousWithinAt (fun t => ((c' t : W) : Minkowski d).1) (Ico 0 1) 1 :=
    (continuous_fst.comp continuous_subtype_val).continuousAt.comp_continuousWithinAt
      ((hc'.continuousWithinAt (show (1 : ℝ) ∈ Ici 0 from mem_Ici.2 zero_le_one)).mono Ico_subset_Ici_self)
  have hlim : Tendsto (fun t => ((c' t : W) : Minkowski d).1) (𝓝[Ico 0 1] 1) (𝓝 1) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds (f := id) tendsto_id |>.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : t ∈ Ico 0 1)
    simp [heq ht, hcv t ht.2]
  haveI : (𝓝[Ico (0 : ℝ) 1] 1).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ico zero_ne_one]
    exact ⟨zero_le_one, le_rfl⟩
  have h1 : ((c' 1 : W) : Minkowski d).1 = 1 := tendsto_nhds_unique hcont hlim
  have h2 : ((c' 1 : W) : Minkowski d).1 < 1 := (c' 1).2
  exact h2.ne h1

end Witnesses

/-! ### Prop 4.16 in full -/

section Full

variable {Λ : Set (PenroseSphere d × ℝ)} {Γ : Subgroup (isom d)}

/-- **Prop 4.16** (`bprop:agissons`, l.1176–1180), the printed statement in full: for a discrete
`Γ ≤ Isom(𝐌ⁿ)` preserving a future complete regular convex domain `Ω = Ω⁺(Λ)` (`CosmoRegular Λ`,
DEC-88), the action is properly discontinuous; if moreover `Γ` is torsion-free, it is free, and
`Γ\Ω` is a flat spacetime, globally hyperbolic (ETT's `GH`, and an acausal Cauchy surface),
Cauchy-complete (DEC-35) and geodesically **semicomplete** (DEC-103; in fact future complete, for
timelike and null rays). -/
theorem bprop_agissons_full (hc : CosmoRegular Λ) (hdisc : DiscreteTopology Γ)
    (hP : PreservesOmega Λ Γ) :
    (∀ K ⊆ omegaPlus Λ, IsCompact K → {γ : isom d | γ ∈ Γ ∧ (γ • K ∩ K).Nonempty}.Finite) ∧
      (IsTorsionFreeSubgroup Γ →
        ActsFreelyProperlyOn Γ (omegaPlus Λ) ∧
          ∃ M : FlatSpacetime.{0} d, IsQuotientOf M Γ hc.regular.opens ∧ GH M ∧
            IsCauchyComplete d M ∧ IsGeodesicallySemicomplete d M ∧
            IsFutureGeodesicallyComplete d M ∧ IsFutureCausallyGeodesicallyComplete d M ∧
            ∃ Sc : Set M, (flatCausality d M).IsCauchySurface Sc ∧
              (flatCausality d M).IsAcausal Sc) := by
  obtain ⟨h1, h2⟩ := bprop_agissons_general hc hdisc hP
  refine ⟨h1, fun htf => ?_⟩
  obtain ⟨hfp, M, hq, hgh, hcc, hS⟩ := h2 htf
  have hfc := isFutureGeodesicallyComplete_of_isQuotientOf hc hq
  exact ⟨hfp, M, hq, hgh, hcc, Or.inl hfc.1, hfc.1, hfc.2, hS⟩

end Full

end Causal.Flat
