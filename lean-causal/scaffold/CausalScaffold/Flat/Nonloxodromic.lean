import CausalScaffold.Flat.Develop
import CausalScaffold.Flat.Externals
import CausalScaffold.Flat.Bieberbach
import CausalScaffold.Flat.TwistedProduct
import CausalScaffold.Flat.Examples
import CausalScaffold.Flat.CauchyComplete
import Mathlib.NumberTheory.Real.Irrational

/-!
# `CausalScaffold.Flat.Nonloxodromic` — Barbot §9, the nonloxodromic case

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §9 "The
nonloxodromic case" (label `nol`), lines of the **labelled** `papers/barbot/legacy/labeled/GHFspace.tex`.

* **`bprop:extension`** — `GHFspace.tex:2992` (Prop 9.5) — `bprop_extension` (with
  `bprop_extension_bounded`, `bprop_extension_top`, `bprop_extension_bot`): closed, no `sorry`.
* `bprop:limites` — `GHFspace.tex:2940` (Prop 9.3) — `bprop_limites` (in `𝐌ⁿ`),
  `bprop_limites_model`, `limites_of_leading`: proved, no `sorry`, in Barbot's coordinates for a
  fixed null frame and with the normalisation `y₋ = −y₊` as a case (partial, SCOPE).
* `bprop:sanloxo` — `GHFspace.tex:2572` (Prop 9.1) — `bprop_sanloxo`: proved from the external
  `BenoistNoLox` (DEC-36, `Flat/Externals`), refined by the trichotomy (partial: external).
* Unmarked prose: [9.E] l.2604–2617 (`omegaS_eq_univ_of_isElliptic`, `isElliptic_of_relIndex`,
  `omegaS_eq_univ_of_relIndex`, `nonloxodromic_elliptic`);
  [9.P] l.2619–2735 (`NolParam`, `act_mul`, `act_proj₀` = (∗∗), `act_of_isU` = (∗∗′));
  Rem 9.2 `choixcoord` l.2737–2760, corrected (`frameChange`, `choixcoord`); [9.b] l.2767–2787
  (`b_trivial_model`, `b_eq_zero_model`); [9.U] l.2865–2938 (`inner_comm_of_commute`,
  `isSymmOn_span`, `nu_mul`); Rem 9.4 `unipcomplet` l.2958–2963 (`unipcomplet_model`); [9.A]
  l.3101–3129 (`nolA_mul`, `choixcoord_nolA`, `unipAction_nolToMink`, `conclusion_model`,
  `nonloxodromic_parabolic`); `Stab(v₀)` in coordinates (`exists_nolParam`) and [9.b] in `𝐌ⁿ`
  (`b_trivial`); G6, closed for `Ω(S̃)` of the whole holonomy group (`perp_invariant_omegaS_of_null`,
  `UGamma_add_mem`, `Ug_add_mem_of_isParabolic`, and the finite-index bridge
  `linOf_fix_of_relIndex`, `perp_invariant_omegaS_of_relIndex`,
  `perp_invariant_omegaS_of_developsCC`); the assembly `nonloxodromic`.

> If $\Gamma$ does not contain loxodromic elements, it is elementary; i.e., up to finite index,
> its linear part is either contained in $SO(n-1)$ (up to conjugacy), or its linear part
> stabilizes an isotropic vector. (l.2575–2577)

> At least one of the extremities $y_{\pm}$ is finite. If they are both finite then, reducing as
> above to the case $y_{-} = -y_{+}$, for every $u$ in $E$ we have: $\mid y_{+}T(u) \mid \leq \mid
> u \mid$. If $y_{+} = +\infty$, then for every $u$ in $E$: $\langle u \mid T(u) \rangle \geq
> -y_{-}\mid T(u) \mid^{2}$. If $y_{-} = -\infty$, then for every $u$ in $E$: $\langle u \mid
> T(u) \rangle \leq -y_{+}\mid T(u) \mid^{2}$ (l.2943–2955)

> The map $T: E \rightarrow \overline{P}_{0}$ can be extended to a linear map
> $\widehat{T}: \overline{P}_{0} \rightarrow \overline{P}_{0}$ satisfying the same properties
> (l.2995–2996) [symmetric; the three inequalities, l.3000–3014]

> According to lemma \ref{suspendre}, $M(S)$ is thus a linear twisted product over a translation
> spacetime. (l.2615–2617)

> It follows that ${\mathcal D}(\widetilde{M})$ is contained in $\Omega$, i.e., that $M$ can be
> embedded in the unipotent spacetime $\Gamma\backslash\Omega$. (l.3126–3127)

> When every elements of $\Gamma$ are nonlinear unipotent isometries, $\Omega(\widetilde{S})$
> is the entire Minkowski space. Then, according to proposition \ref{limites}, $I$ and $I'$ are
> not equal. (l.2958–2962)

> If $w$ belongs to $\overline{P}_{0} = P_{0} \cap v_{n}$, then $y'=y$ […] It follows:
> $\mu'(g) = \mu(g) + \langle u(g) \mid w \rangle$ (l.2754–2758)

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; `Minkowski d` has `d` spatial
dimensions: Barbot's `n` is `d + 1`. In Barbot's coordinates (`nolToMink`, through
`Flat/Examples`' null coordinates) `𝐌ⁿ = Minkowski (d + 1)`, `n = d + 2`, `P̄₀ = ℝᵈ = ℝ^{n−2}`.
In Lean, `ylo`, `yhi` are Barbot's `y₋`, `y₊`.

## The two outputs (for `Flat/Classification`)

Both branches take a subgroup `Γ' ≤ Γ` **of finite index** (`Γ'.relIndex Γ ≠ 0`); without it
the conclusions, which concern `Ω(S̃)` of all of `Γ`, are false (`Γ' = ⊥`).

* `nonloxodromic_elliptic`: `L(Γ')` fixes a timelike vector ⇒ ∃ `Γ'' ≤ Γ'` of finite index,
  `B` with `IsQuotientOf B Γ'' Ω(S̃)` (here `Ω(S̃) = 𝐌ⁿ`), and `B` an LTP (`IsLTPOver`) over an
  `IsTranslationSpacetime` of dimension `≤ d`: `M(S)`, up to finite index, as l.2615–2617 says.
* `nonloxodromic_parabolic` (DEC-43 R1, l.3120–3127): `L(Γ')` fixes a nonzero null `v₀`, `Γ'` has
  a parabolic element, `Γ` no loxodromic one ⇒ ∃ `Γ'' ≤ Γ'` of finite index and an open
  `Γ''`-invariant `Ω` with `𝒟(M̃) ⊆ Ω ⊆ Ω(S̃)` such that `B = Γ''\Ω` is an LTP over an
  `IsUnipotentSpacetime` `M₁`. The output concerns `M`, through `𝒟(M̃) ⊆ Ω`, **not** `M(S)`:
  by Rem 9.4, `M(S) = Γ\Ω(S̃)` need not embed in any unipotent spacetime (finding 6).
* `nonloxodromic`: their assembly from `bprop_sanloxo` (no loxodromic element in `Γ`), in the
  common form `∃ Γ'' Ω B, 𝒟(M̃) ⊆ Ω ⊆ Ω(S̃) ∧ IsQuotientOf B Γ'' Ω ∧ (…)`, with `Ω = Ω(S̃)` in
  the elliptic disjunct.

The §8 input is Develop's `IsDevelopingPair`, `DevelopsCC` (and `IsCausal` where Prop 8.12 is
used), with `M` Hausdorff (`T2Space M`: Develop's Prop 8.12 is false without it), never the
metric notion; `Γ = ρ.range`, `Σ = 𝒟(p⁻¹S)`, `Ω(S̃) = omegaSOpens Γ Σ`. The
finite-index passage is explicit: `Γ'' ≤ Γ`, `Γ''.relIndex Γ ≠ 0`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| 9.5: `T : E → P̄₀` linear, symmetric, the inequality of its case | ✓ carried (`IsSymmOn E T`, `LimitesIneq`); `T` given on all of `V` (values off `E` unused); `P̄₀` ⚠ weakened to any finite-dimensional real inner product space |
| 9.5: `y₋ < 0 < y₊`, the three cases after "reducing as above" | ✓ carried (`hlo`, `hhi`, `hnorm`, `hfin`) |
| 9.3: `S̃` achronal, `Γ`-invariant, `Γ ⊆ 𝒜(v₀)`, `v = T u` | ✓ carried; ⚠ weakened: acausal (`bprop_limites`) or `0 ≤ Q(X − X')` (`_model`) instead of (CC′) |
| 9.3: `I = π₁(S̃)` with extremities `y±` | ⚠ weakened: `π₁(S̃) ⊇ ]y₋, y₊[` |
| 9.3: "`u(Γ)` is a lattice of `E`" | ⚠ weakened: `L` an additive subgroup, `E = span L` (`nonneg_on_span_of_addSubgroup`) |
| 9.3: coordinates `x v₀ + z + y vₙ` for the `v₀` of `Γ`; "reducing as above to `y₋ = −y₊`" | ⚠ strengthened: the fixed frame `nolToMink` (`v₀ = ofNull 1 0 0`) and the bounded case only in the normalised form `ylo = −yhi` (SCOPE) |
| 9.1: no loxodromic element; Benoist | ✓ carried; Benoist as the external `BenoistNoLox` |
| [9.b]: `γ₁` parabolic, `b(γ₀) ≠ 0` | ⚠ strengthened: `γ₁` purely unipotent (`R = id`), with `b(γ₁) = 0` (`b_eq_zero_model` proves it from `v(γ₁) ≠ 0`) |
| [9.E], [9.A]: Bieberbach | carried as the external `BieberbachI` (`Flat/Bieberbach`) |
| [9.E], [9.P]: "up to finite index" (l.2575, l.2621) | ✓ carried: `Γ'.relIndex Γ ≠ 0` in both branches |
| [9.P]: no loxodromic element in `Γ` (the §9 case) | ✓ carried (`hnl` on `Γ`; used by `linOf_fix_of_relIndex`) |
| `M` a manifold | ✓ carried as `T2Space M` (Develop's Prop 8.12) |

## SCOPE (disclosed)

* **Sorries (3)**: `exists_timelike_fixed_of_elliptic_of_null` (the branch of 9.1 the paper does
  not treat), `nonloxodromic_elliptic`, `nonloxodromic_parabolic` (the `𝐌ⁿ` assemblies; their
  obstructions are in the tags). Everything else is proved; `nonloxodromic` is assembled (no
  `sorry` of its own).
* **The parabolic output was restated (audit, 2026-11-01).** An earlier draft concluded that
  `M(S) = Γ''\Ω(S̃)` is an LTP over a spacetime embedding in a unipotent one; Rem 9.4 refutes it
  (finding 6), and the statement now follows l.3126 and DEC-43 R1: `B = Γ''\Ω` with
  `𝒟(M̃) ⊆ Ω ⊆ Ω(S̃)`, an LTP over a unipotent spacetime. Both branches gained the finite-index
  hypothesis `Γ'.relIndex Γ ≠ 0`, and the parabolic one `hnl` on `Γ`.
* **Coordinates.** §1–§3 work in `ℝ × E × ℝ` (`nolQ = 2xy + |z|²`) and, for `E = ℝᵈ`, in
  `𝐌ⁿ` through `nolToMink` (`minkQ_nolToMink`, `nolToMink_sub`, `nolToMink_minkToNol`):
  `v₀ = ofNull 1 0 0`, `vₙ = ofNull 0 1 0`; every isometry whose linear part fixes this `v₀` is a
  `NolParam` (`exists_nolParam`, l.2701–2713). The frame `φ ∈ Isom(𝐌ⁿ)` taking the `v₀` of `Γ`
  there is not formalized.
* **G1** (one-sided 9.3/9.5, BARBOT-THEOREMS §6): discharged at the level of 9.3 and 9.5 (both
  infinite-extremity cases are proved); its use in [11.i] is downstream. **G6** is closed for
  `Ω(S̃)` of the whole holonomy group in the parabolic case: a finite-index `Γ'` fixing `v₀` with
  a parabolic element forces all of `Γ` to fix `v₀` when `Γ` has no loxodromic element
  (`linOf_fix_of_relIndex`), and then (`perp_invariant_omegaS_of_null`) every
  `U(γ)` is `v₀^⊥`-invariant (elliptic: `𝐌ⁿ`; linear parabolic: `J = ℝ v₀` for every
  decomposition, `nullPart_eq_span_of_fix`; tangent: `𝐌ⁿ`; transverse: excluded by `nini`), and
  components of a translation-invariant open set are translation-invariant (`omegaS_add_mem`).
* **9.5's proof is not Barbot's**: compactness and `Q(λ, v)` (l.3040–3099) are replaced by one
  coercive extension (`exists_symm_extension_of_coercive`: `T̂(e + w) = T e`, `w ⊥ T(E)`) and the
  substitution `P = (1 + y₊T)/2` for the case `y₋ = −y₊`.
* **[9.b]** is proved without Lemma 7.1 (false as printed for `n ≥ 4`, `Flat/AchronalDomains`)
  and without Cor 8.3: heights `y₀ ± k b(γ₀)` and the leading term of 9.3 suffice; written for a
  purely unipotent `γ₁` (`b_trivial` in `𝐌ⁿ`, with `b(γ₁) = 0` itself proved by the quartic,
  `b_eq_zero_model`). Rotation parts `R ≠ id` (the leading term on `Fix R`) are not treated.
* **Findings.** (1) Rem 9.2 (l.2739–2758): `vₙ + w` (`w ∈ P̄₀`) and `vₙ + a v₀` are not null
  (`frameChange_null`); the frame change is `vₙ' = vₙ + w − (|w|²/2) v₀`, under which Barbot's
  `μ' = μ + ⟨u | w⟩` holds exactly (`choixcoord`); the first bullet is not a frame change.
  (2) l.2621–2622: "`Γ` contains a parabolic element `γ₁`" does not follow from 9.1 when `L(Γ')`
  fixes a null `v₀` and is all-elliptic. (3) l.588–590 / [9.E]: spacelike translation vectors do
  not give a spacelike span (`spacelike_translations_null_span`); the reading
  `IsTranslationSpacetime` needs the latter. (4) l.2659: for `γ ∈ 𝒜(v₀)` linear, `U(γ)` is
  `π₁⁻¹(ℝ ∖ {y_γ})` (l.2929), the preimage of the complement of a point, not of "a half-line".
  (5) 9.3 needs no discreteness of `u(Γ)`. (6) Rem 9.4 (l.2958–2962) has a consequence the
  paper's prose of l.2904–2907 and BARBOT-THEOREMS §3's reading ("conclusions about
  `M(S) = Γ\Ω(S̃)`", l.3120–3127) do not draw: when every element of `Γ` is a nonlinear unipotent
  isometry, `Ω(S̃) = 𝐌ⁿ` while `𝒟(M̃)` lies in a slab `{α < y < β} ≠ 𝐌ⁿ`, and `M(S) = Γ\𝐌ⁿ`
  embeds in **no** unipotent spacetime (an injective local isometry of `Γ_U\𝐌ⁿ` into
  `Γ_N\φ(]α,β[)` lifts to a global isometry of `𝐌ⁿ` onto the slab, forcing `]α,β[ = ℝ`, `ℓ = 0`,
  `Γ_N` translations, against the nontrivial unipotent linear part of `Γ_U`). Example: `𝐌⁴`,
  `ℓ = (1, 0)`, `Γ = ⟨φ(e₁ + e₂)⟩` on `{y > −1}`. The parabolic conclusion is about `M`
  (`𝒟(M̃) ⊆ Ω`, l.3126), with `Ω ≠ Ω(S̃)` in general; the dispatch's output (2) for
  Classification ("`M(S)` is an LTP over a spacetime embedding in a unipotent one") inherits the
  defect and is replaced by this one.
* Non-vacuity: `Flat/Examples`' unipotent groups are `A_{T, 0}` for diagonal `T`
  (`unipAction_nolToMink`, `isSymmOn_diagLin`); no model inhabitant of `bprop_limites_model`'s
  hypotheses (an achronal `S_f`) is given here.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
wave 5, package WP-34c-Nonloxodromic.
-/

namespace Causal.Flat

open Set Function Filter Topology Submodule
open scoped RealInnerProductSpace

/-! ## §0 Linear algebra: symmetric extensions (`bprop:extension`) -/

section LinearAlgebra

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- `T` is **symmetric on `E`**: `⟨u | T u'⟩ = ⟨u' | T u⟩` for `u, u' ∈ E` (l.2924, l.3000). -/
def IsSymmOn (E : Submodule ℝ V) (T : V →ₗ[ℝ] V) : Prop :=
  ∀ u ∈ E, ∀ u' ∈ E, ⟪u, T u'⟫ = ⟪u', T u⟫

variable [FiniteDimensional ℝ V]

/-- **The coercive symmetric extension.** If `T` is symmetric on `E` and
`c ‖T u‖² ≤ ⟨u | T u⟩` on `E` for some `c > 0`, then `T|_E` extends to a symmetric `T̂` on all of
`V` with the same inequality: `T̂ (e + w) = T e` for `e ∈ E`, `w ⊥ T(E)`. -/
theorem exists_symm_extension_of_coercive {E : Submodule ℝ V} {T : V →ₗ[ℝ] V}
    (hT : IsSymmOn E T) {c : ℝ} (hc : 0 < c) (hcoer : ∀ u ∈ E, c * ‖T u‖ ^ 2 ≤ ⟪u, T u⟫) :
    ∃ T' : V →ₗ[ℝ] V, (∀ u ∈ E, T' u = T u) ∧ IsSymmOn ⊤ T' ∧
      ∀ x, c * ‖T' x‖ ^ 2 ≤ ⟪x, T' x⟫ := by
  set F : Submodule ℝ V := E.map T with hF
  -- the kernel: `E ∩ F^⊥ ⊆ ker T`
  have hker : ∀ e ∈ E, e ∈ Fᗮ → T e = 0 := by
    intro e he hw
    have h0 : ⟪e, T e⟫ = 0 := by
      exact (Submodule.mem_orthogonal' F e).1 hw _ ⟨e, he, rfl⟩
    have := hcoer e he
    rw [h0] at this
    have hn : ‖T e‖ ^ 2 ≤ 0 := by
      by_contra hneg
      exact absurd (mul_pos hc (lt_of_not_ge hneg)) (not_lt.2 this)
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm hn (sq_nonneg _)))
  -- `E ⊔ F^⊥ = ⊤`
  have hsup : E ⊔ Fᗮ = ⊤ := by
    have hbot : Eᗮ ⊓ F = ⊥ := by
      rw [eq_bot_iff]
      rintro f ⟨hfE, e, he, rfl⟩
      have heF : e ∈ Fᗮ := by
        rw [Submodule.mem_orthogonal']
        rintro _ ⟨e', he', rfl⟩
        rw [hT e he e' he']
        rw [real_inner_comm]
        exact (Submodule.mem_orthogonal' E _).1 hfE e' he'
      rw [Submodule.mem_bot]
      exact hker e he heF
    have : (E ⊔ Fᗮ)ᗮ = ⊥ := by
      rw [← Submodule.inf_orthogonal, Submodule.orthogonal_orthogonal]; exact hbot
    exact (Submodule.orthogonal_eq_bot_iff).1 this
  -- the two partial maps and their sum
  let f : V →ₗ.[ℝ] V := ⟨E, T.domRestrict E⟩
  let g : V →ₗ.[ℝ] V := ⟨Fᗮ, 0⟩
  have H : ∀ (x : f.domain) (y : g.domain), (x : V) = y → f x = g y := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    show T x = 0
    exact hker x hx (by rw [show x = y from hxy]; exact hy)
  let ι : V →ₗ[ℝ] (f.sup g H).domain :=
    LinearMap.codRestrict _ LinearMap.id fun x => by
      show x ∈ E ⊔ Fᗮ
      rw [hsup]; trivial
  refine ⟨(f.sup g H).toFun ∘ₗ ι, ?_⟩
  -- evaluation along a decomposition `x = e + w`
  have heval : ∀ e ∈ E, ∀ w ∈ Fᗮ, ((f.sup g H).toFun ∘ₗ ι) (e + w) = T e := by
    intro e he w hw
    have := LinearPMap.sup_apply H ⟨e, he⟩ ⟨w, hw⟩ (ι (e + w)) rfl
    rw [LinearMap.comp_apply]
    refine this.trans ?_
    show T e + 0 = T e
    rw [add_zero]
  have hdec : ∀ x : V, ∃ e ∈ E, ∃ w ∈ Fᗮ, e + w = x := fun x => by
    have hx : x ∈ E ⊔ Fᗮ := by rw [hsup]; trivial
    obtain ⟨e, he, w, hw, hew⟩ := Submodule.mem_sup.1 hx
    exact ⟨e, he, w, hw, hew⟩
  have hTF : ∀ e ∈ E, ∀ w ∈ Fᗮ, ⟪w, T e⟫ = 0 := fun e he w hw =>
    (Submodule.mem_orthogonal' F w).1 hw _ ⟨e, he, rfl⟩
  refine ⟨fun u hu => by simpa using heval u hu 0 (Submodule.zero_mem _), ?_, ?_⟩
  · intro x _ x' _
    obtain ⟨e, he, w, hw, rfl⟩ := hdec x
    obtain ⟨e', he', w', hw', rfl⟩ := hdec x'
    rw [heval e he w hw, heval e' he' w' hw', inner_add_left, inner_add_left, hTF e' he' w hw,
      hTF e he w' hw', hT e he e' he']
  · intro x
    obtain ⟨e, he, w, hw, rfl⟩ := hdec x
    rw [heval e he w hw, inner_add_left, hTF e he w hw, add_zero]
    exact hcoer e he

/-- **Prop 9.5, the case `ylo = −yhi`** (l.3003–3005, l.3029–3099): if `T` is symmetric on `E` and
`|yhi T u| ≤ |u|` on `E`, it extends to a symmetric `T̂` on `V` with `|yhi T̂ x| ≤ |x|`. The proof
is not Barbot's (compactness and the forms `Q(λ, v)`): `P = (1 + yhiT)/2` satisfies
`‖P u‖² ≤ ⟨u | P u⟩ ⟺ ‖yhi T u‖ ≤ ‖u‖`, so the coercive extension of `P` gives `T̂ = (2P̂ − 1)/yhi`. -/
theorem bprop_extension_bounded {E : Submodule ℝ V} {T : V →ₗ[ℝ] V} (hT : IsSymmOn E T)
    {a : ℝ} (ha : 0 < a) (h : ∀ u ∈ E, ‖a • T u‖ ≤ ‖u‖) :
    ∃ T' : V →ₗ[ℝ] V, (∀ u ∈ E, T' u = T u) ∧ IsSymmOn ⊤ T' ∧ ∀ x, ‖a • T' x‖ ≤ ‖x‖ := by
  set P : V →ₗ[ℝ] V := (1 / 2 : ℝ) • (LinearMap.id + a • T) with hP
  have hPapp : ∀ x, P x = (1 / 2 : ℝ) • (x + a • T x) := fun x => rfl
  have hPs : IsSymmOn E P := by
    intro u hu u' hu'
    rw [hPapp, hPapp, inner_smul_right, inner_smul_right, inner_add_right, inner_add_right,
      inner_smul_right, inner_smul_right, hT u hu u' hu', real_inner_comm u u']
  have hPc : ∀ u ∈ E, (1 : ℝ) * ‖P u‖ ^ 2 ≤ ⟪u, P u⟫ := by
    intro u hu
    have h1 := h u hu
    have h2 : ‖a • T u‖ ^ 2 ≤ ‖u‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [hPapp, norm_smul, mul_pow, inner_smul_right, inner_add_right, @norm_add_sq_real,
      real_inner_self_eq_norm_sq]
    have : ‖(1 / 2 : ℝ)‖ ^ 2 = 1 / 4 := by norm_num
    rw [this]
    nlinarith [h2]
  obtain ⟨P', hext, hsym, hcoer⟩ := exists_symm_extension_of_coercive hPs one_pos hPc
  set T' : V →ₗ[ℝ] V := a⁻¹ • ((2 : ℝ) • P' - LinearMap.id) with hT'
  have hT'app : ∀ x, T' x = a⁻¹ • ((2 : ℝ) • P' x - x) := fun x => rfl
  refine ⟨T', fun u hu => ?_, fun x _ x' _ => ?_, fun x => ?_⟩
  · rw [hT'app, hext u hu, hPapp, smul_smul]
    norm_num
    rw [smul_smul, inv_mul_cancel₀ ha.ne', one_smul]
  · rw [hT'app, hT'app, inner_smul_right, inner_smul_right, inner_sub_right, inner_sub_right,
      inner_smul_right, inner_smul_right, hsym x trivial x' trivial, real_inner_comm x x']
  · have hc := hcoer x
    rw [hT'app, smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
    have key : ‖(2 : ℝ) • P' x - x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
      rw [@norm_sub_sq_real, norm_smul, inner_smul_left, mul_pow, real_inner_comm]
      norm_num
      nlinarith [hc]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 key

/-- **Prop 9.5, the case `yhi = +∞`** (l.3007–3009, l.3019–3026), with `b = ylo < 0`. -/
theorem bprop_extension_top {E : Submodule ℝ V} {T : V →ₗ[ℝ] V} (hT : IsSymmOn E T)
    {b : ℝ} (hb : b < 0) (h : ∀ u ∈ E, -b * ‖T u‖ ^ 2 ≤ ⟪u, T u⟫) :
    ∃ T' : V →ₗ[ℝ] V, (∀ u ∈ E, T' u = T u) ∧ IsSymmOn ⊤ T' ∧
      ∀ x, -b * ‖T' x‖ ^ 2 ≤ ⟪x, T' x⟫ :=
  exists_symm_extension_of_coercive hT (by linarith) h

/-- **Prop 9.5, the case `ylo = −∞`** (l.3012–3014, l.3028: "completely similar"), with
`a = yhi > 0`: apply the case `yhi = +∞` to `−T`. -/
theorem bprop_extension_bot {E : Submodule ℝ V} {T : V →ₗ[ℝ] V} (hT : IsSymmOn E T)
    {a : ℝ} (ha : 0 < a) (h : ∀ u ∈ E, ⟪u, T u⟫ ≤ -a * ‖T u‖ ^ 2) :
    ∃ T' : V →ₗ[ℝ] V, (∀ u ∈ E, T' u = T u) ∧ IsSymmOn ⊤ T' ∧
      ∀ x, ⟪x, T' x⟫ ≤ -a * ‖T' x‖ ^ 2 := by
  have hT' : IsSymmOn E (-T) := fun u hu u' hu' => by
    simp only [LinearMap.neg_apply, inner_neg_right, hT u hu u' hu']
  obtain ⟨S, hext, hsym, hcoer⟩ := exists_symm_extension_of_coercive hT' ha fun u hu => by
    simp only [LinearMap.neg_apply, norm_neg, inner_neg_right]; linarith [h u hu]
  refine ⟨-S, fun u hu => by simp [hext u hu], fun x _ x' _ => ?_, fun x => ?_⟩
  · simp only [LinearMap.neg_apply, inner_neg_right, hsym x trivial x' trivial]
  · simp only [LinearMap.neg_apply, norm_neg, inner_neg_right]; linarith [hcoer x]

/-- **The inequalities of Prop 9.3 / Prop 9.5** for the extremities `ylo < 0 < yhi` (in
`[−∞, +∞]`) of `I = π₁(S̃)`, in Barbot's three cases (l.2943–2955, l.3003–3014): `ylo = −yhi`
finite, `yhi = +∞`, `ylo = −∞`. -/
def LimitesIneq (E : Submodule ℝ V) (T : V →ₗ[ℝ] V) (ylo yhi : EReal) : Prop :=
  (∀ a : ℝ, yhi = a → ylo = ((-a : ℝ) : EReal) → ∀ u ∈ E, ‖a • T u‖ ≤ ‖u‖) ∧
    (∀ b : ℝ, ylo = b → yhi = ⊤ → ∀ u ∈ E, -b * ‖T u‖ ^ 2 ≤ ⟪u, T u⟫) ∧
    (∀ a : ℝ, yhi = a → ylo = ⊥ → ∀ u ∈ E, ⟪u, T u⟫ ≤ -a * ‖T u‖ ^ 2)

/-- **Prop 9.5** (`bprop:extension`, l.2992–3016): `T : E → P̄₀`, symmetric, satisfying the
inequalities of Prop 9.3 in Barbot's normalisation (`ylo = −yhi`, or one extremity infinite),
extends to a symmetric `T̂ : P̄₀ → P̄₀` satisfying the same inequalities on all of `P̄₀`. -/
theorem bprop_extension {E : Submodule ℝ V} {T : V →ₗ[ℝ] V} (hT : IsSymmOn E T)
    {ylo yhi : EReal} (hlo : ylo < 0) (hhi : 0 < yhi) (hnorm : ylo = -yhi ∨ yhi = ⊤ ∨ ylo = ⊥)
    (hfin : ¬(ylo = ⊥ ∧ yhi = ⊤)) (h : LimitesIneq E T ylo yhi) :
    ∃ T' : V →ₗ[ℝ] V, (∀ u ∈ E, T' u = T u) ∧ IsSymmOn ⊤ T' ∧ LimitesIneq ⊤ T' ylo yhi := by
  induction yhi using EReal.rec with
  | bot => exact absurd hhi (not_lt.2 bot_le)
  | top =>
    induction ylo using EReal.rec with
    | bot => exact absurd ⟨rfl, rfl⟩ hfin
    | top => exact absurd hlo (not_lt.2 le_top)
    | coe b =>
      have hb : b < 0 := by exact_mod_cast hlo
      obtain ⟨T', hext, hsym, hc⟩ := bprop_extension_top hT hb (h.2.1 b rfl rfl)
      refine ⟨T', hext, hsym, fun a ha => absurd ha (EReal.top_ne_coe a), fun b' hb' _ x _ => ?_,
        fun a ha => absurd ha (EReal.top_ne_coe a)⟩
      rw [← EReal.coe_eq_coe_iff.1 hb']; exact hc x
  | coe a =>
    have ha : 0 < a := by exact_mod_cast hhi
    rcases hnorm with hn | hn | hn
    · have hy : ylo = ((-a : ℝ) : EReal) := by rw [hn]; rfl
      obtain ⟨T', hext, hsym, hc⟩ := bprop_extension_bounded hT ha (h.1 a rfl hy)
      refine ⟨T', hext, hsym, fun a' ha' _ x _ => ?_, fun _ _ h' => absurd h' (EReal.coe_ne_top a),
        fun _ _ h' => absurd (hy ▸ h') (EReal.coe_ne_bot _)⟩
      rw [← EReal.coe_eq_coe_iff.1 ha']; exact hc x
    · exact absurd hn (EReal.coe_ne_top a)
    · obtain ⟨T', hext, hsym, hc⟩ := bprop_extension_bot hT ha (h.2.2 a rfl hn)
      refine ⟨T', hext, hsym, fun _ _ h' => absurd (hn ▸ h') (EReal.bot_ne_coe _),
        fun _ _ h' => absurd h' (EReal.coe_ne_top a), fun a' ha' _ x _ => ?_⟩
      rw [← EReal.coe_eq_coe_iff.1 ha']; exact hc x

omit [FiniteDimensional ℝ V] in
/-- **No pole inside `I`** (what l.3120–3122 uses: "our choice of `T̂` … makes sure that `S̃` is
contained in a connected component `Ω` of `Ω(A)`"): under the inequalities on all of `V`, for
every `y` strictly between `ylo` and `yhi`, `1 + y T̂` is injective. -/
theorem LimitesIneq.add_smul_ne_zero {T : V →ₗ[ℝ] V} {ylo yhi : EReal} (hlo : ylo < 0)
    (hhi : 0 < yhi)
    (hnorm : ylo = -yhi ∨ yhi = ⊤ ∨ ylo = ⊥) (hfin : ¬(ylo = ⊥ ∧ yhi = ⊤))
    (h : LimitesIneq ⊤ T ylo yhi) {y : ℝ} (hylo : ylo < y) (hyhi : (y : EReal) < yhi) {x : V}
    (hx : x ≠ 0) : x + y • T x ≠ 0 := by
  intro h0
  have hy0 : y ≠ 0 := by rintro rfl; simp at h0; exact hx h0
  have hTx : T x = (-y⁻¹) • x := by
    have : y • T x = -x := eq_neg_of_add_eq_zero_right h0
    rw [← inv_smul_smul₀ hy0 (T x), this, smul_neg, neg_smul]
  have hx2 : 0 < ‖x‖ ^ 2 := by have := norm_pos_iff.2 hx; positivity
  have e1 : ‖T x‖ ^ 2 = y⁻¹ ^ 2 * ‖x‖ ^ 2 := by
    rw [hTx, norm_smul, mul_pow, norm_neg, norm_inv, Real.norm_eq_abs, inv_pow, sq_abs, inv_pow]
  have e2 : ⟪x, T x⟫ = -y⁻¹ * ‖x‖ ^ 2 := by
    rw [hTx, inner_smul_right, real_inner_self_eq_norm_sq]
  have hyy : y ^ 2 * y⁻¹ ^ 2 = 1 := by rw [← mul_pow, mul_inv_cancel₀ hy0, one_pow]
  have hyy' : y ^ 2 * y⁻¹ = y := by rw [sq, mul_assoc, mul_inv_cancel₀ hy0, mul_one]
  induction yhi using EReal.rec with
  | bot => exact absurd hhi (not_lt.2 bot_le)
  | top =>
    induction ylo using EReal.rec with
    | bot => exact hfin ⟨rfl, rfl⟩
    | top => exact absurd hlo (not_lt.2 le_top)
    | coe b =>
      have hby : b < y := by exact_mod_cast hylo
      have hc := h.2.1 b rfl rfl x trivial
      rw [e1, e2] at hc
      have k1 : -b * y⁻¹ ^ 2 ≤ -y⁻¹ := le_of_mul_le_mul_right (by linarith) hx2
      have k2 := mul_le_mul_of_nonneg_left k1 (sq_nonneg y)
      have : y ^ 2 * (-b * y⁻¹ ^ 2) = -b := by linear_combination (-b) * hyy
      have : y ^ 2 * (-y⁻¹) = -y := by linear_combination (-1 : ℝ) * hyy'
      linarith
  | coe a =>
    have hya : y < a := by exact_mod_cast hyhi
    rcases hnorm with hn | hn | hn
    · have hy' : ylo = ((-a : ℝ) : EReal) := by rw [hn]; rfl
      have hay : -a < y := by rw [hy'] at hylo; exact_mod_cast hylo
      have hc := h.1 a rfl hy' x trivial
      have hc2 : ‖a • T x‖ ^ 2 ≤ ‖x‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hc 2
      rw [norm_smul, mul_pow, e1, Real.norm_eq_abs, sq_abs] at hc2
      have k1 : a ^ 2 * y⁻¹ ^ 2 ≤ 1 := le_of_mul_le_mul_right (by linarith) hx2
      have k2 := mul_le_mul_of_nonneg_left k1 (sq_nonneg y)
      have : y ^ 2 * (a ^ 2 * y⁻¹ ^ 2) = a ^ 2 := by linear_combination a ^ 2 * hyy
      nlinarith
    · exact absurd hn (EReal.coe_ne_top a)
    · have hc := h.2.2 a rfl hn x trivial
      rw [e1, e2] at hc
      have k1 : -y⁻¹ ≤ -a * y⁻¹ ^ 2 := le_of_mul_le_mul_right (by linarith) hx2
      have k2 := mul_le_mul_of_nonneg_left k1 (sq_nonneg y)
      have : y ^ 2 * (-a * y⁻¹ ^ 2) = -a := by linear_combination (-a) * hyy
      have : y ^ 2 * (-y⁻¹) = -y := by linear_combination (-1 : ℝ) * hyy'
      linarith

omit [FiniteDimensional ℝ V] in
/-- **Symmetry on a spanning set is symmetry on the span** (l.2922–2924: "It follows, for every
`u, u'` in `E`"). -/
theorem isSymmOn_span {s : Set V} {T : V →ₗ[ℝ] V} (h : ∀ u ∈ s, ∀ u' ∈ s, ⟪u, T u'⟫ = ⟪u', T u⟫) :
    IsSymmOn (span ℝ s) T := by
  have h1 : ∀ u ∈ s, ∀ x ∈ span ℝ s, ⟪u, T x⟫ = ⟪x, T u⟫ := by
    intro u hu x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact h u hu x hx
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, inner_add_right, inner_add_left, hx, hy]
    | smul a x _ hx => rw [map_smul, inner_smul_right, inner_smul_left, hx]; simp
  intro x hx y hy
  induction hx using Submodule.span_induction with
  | mem x hx' => exact h1 x hx' y hy
  | zero => simp
  | add x z _ _ hx' hz => rw [map_add, inner_add_right, inner_add_left, hx', hz]
  | smul a x _ hx' => rw [map_smul, inner_smul_right, inner_smul_left, hx']; simp

/-! ### Prop 9.3, the algebraic core -/

omit [FiniteDimensional ℝ V] in
/-- `⌊N c⌋ / N → c`. -/
theorem tendsto_floor_mul_div_nat (c : ℝ) :
    Tendsto (fun N : ℕ => ((⌊(N : ℝ) * c⌋ : ℤ) : ℝ) / N) atTop (𝓝 c) := by
  have h1 : Tendsto (fun N : ℕ => c - 1 / (N : ℝ)) atTop (𝓝 c) := by
    simpa using tendsto_const_nhds.sub (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h1 tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    rw [le_div_iff₀ hN', sub_mul, one_div, inv_mul_cancel₀ hN'.ne']
    have := Int.lt_floor_add_one ((N : ℝ) * c)
    linarith
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_le_iff₀ hN']
    have := Int.floor_le ((N : ℝ) * c)
    linarith

omit [FiniteDimensional ℝ V] in
/-- **"This inequality extends to any `u` in `E` since `u(Γ)` is a lattice of `E`"**
(l.2982–2987): a continuous `q`, homogeneous of degree 2, nonnegative on an additive subgroup
`L`, is nonnegative on its real span (by `x = lim N⁻¹ ∑ ⌊N cᵢ⌋ ℓᵢ`). Discreteness of `L` is not
needed. -/
theorem nonneg_on_span_of_addSubgroup {L : AddSubgroup V} {q : V → ℝ} (hq : Continuous q)
    (hhom : ∀ (c : ℝ) (x : V), q (c • x) = c ^ 2 * q x) (hL : ∀ u ∈ L, 0 ≤ q u) :
    ∀ x ∈ span ℝ (L : Set V), 0 ≤ q x := by
  intro x hx
  obtain ⟨n, f, g, rfl⟩ := Submodule.mem_span_set'.1 hx
  set ℓ : ℕ → V := fun N => ∑ i, (⌊(N : ℝ) * f i⌋ : ℤ) • (g i : V) with hℓ
  have hmem : ∀ N, ℓ N ∈ L := fun N =>
    AddSubgroup.sum_mem _ fun i _ => AddSubgroup.zsmul_mem _ (g i).2 _
  have heq : ∀ N : ℕ, (1 / (N : ℝ)) • ℓ N =
      ∑ i, (((⌊(N : ℝ) * f i⌋ : ℤ) : ℝ) / N) • (g i : V) := by
    intro N
    rw [hℓ, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Int.cast_smul_eq_zsmul ℝ, smul_smul]
    ring_nf
  have hlim : Tendsto (fun N : ℕ => (1 / (N : ℝ)) • ℓ N) atTop (𝓝 (∑ i, f i • (g i : V))) := by
    simp_rw [heq]
    exact tendsto_finsetSum _ fun i _ => (tendsto_floor_mul_div_nat (f i)).smul_const _
  refine ge_of_tendsto ((hq.tendsto _).comp hlim) (Eventually.of_forall fun N => ?_)
  show 0 ≤ q ((1 / (N : ℝ)) • ℓ N)
  rw [hhom]
  exact mul_nonneg (sq_nonneg _) (hL _ (hmem N))

omit [FiniteDimensional ℝ V] in
/-- The leading coefficient `⟨u + y v | u + y' v⟩` (l.2976) is affine in each variable. -/
theorem nol_leading_eq (u v : V) (y y' : ℝ) :
    ⟪u + y • v, u + y' • v⟫ = ‖u‖ ^ 2 + (y + y') * ⟪u, v⟫ + y * y' * ‖v‖ ^ 2 := by
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    real_inner_self_eq_norm_sq, conj_trivial]
  rw [real_inner_comm v u]; ring

/-- **Prop 9.3, the algebraic core** (l.2940–2989): if the leading coefficient
`⟨u + y T u | u + y' T u⟩` is nonnegative for every `u` in an additive subgroup `L` of `V` and
every `y, y'` strictly between `ylo < 0 < yhi` (Barbot's `y₋`, `y₊`), and `T u ≠ 0` for some
`u ∈ L` (a parabolic element), then `ylo`, `yhi` are not both infinite and Barbot's
inequalities hold on all of `E = span L`. -/
theorem limites_of_leading {L : AddSubgroup V} {T : V →ₗ[ℝ] V} {ylo yhi : EReal}
    (hlo : ylo < 0) (hhi : 0 < yhi)
    (hlead : ∀ u ∈ L, ∀ y y' : ℝ, ylo < y → (y : EReal) < yhi → ylo < y' → (y' : EReal) < yhi →
      0 ≤ ⟪u + y • T u, u + y' • T u⟫)
    (hpar : ∃ u ∈ L, T u ≠ 0) :
    ¬(ylo = ⊥ ∧ yhi = ⊤) ∧ LimitesIneq (span ℝ (L : Set V)) T ylo yhi := by
  have hTc : Continuous T := LinearMap.continuous_of_finiteDimensional T
  simp_rw [nol_leading_eq] at hlead
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- both infinite: `y = N`, `y' = −N`
    rintro ⟨rfl, rfl⟩
    obtain ⟨u, hu, hTu⟩ := hpar
    have hT2 : 0 < ‖T u‖ ^ 2 := by have := norm_pos_iff.2 hTu; positivity
    obtain ⟨N, hN⟩ := exists_nat_gt (‖u‖ ^ 2 / ‖T u‖ ^ 2)
    have := hlead u hu N (-N) (EReal.bot_lt_coe _) (EReal.coe_lt_top _) (EReal.bot_lt_coe _)
      (EReal.coe_lt_top _)
    have hN1 : (1 : ℝ) ≤ N := by
      have : (0 : ℝ) ≤ ‖u‖ ^ 2 / ‖T u‖ ^ 2 := by positivity
      have h0 : (0 : ℝ) < N := by linarith
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at h0)
    rw [div_lt_iff₀ hT2] at hN
    nlinarith
  · -- `ylo = −yhi = −a`: the limit `y = a`, `y' = −a`
    rintro a rfl hylo
    have ha : 0 < a := by exact_mod_cast hhi
    have hu : ∀ u ∈ L, 0 ≤ ‖u‖ ^ 2 - ‖a • T u‖ ^ 2 := by
      intro u hu
      have hg : Continuous fun ε : ℝ =>
          ‖u‖ ^ 2 + ((a - ε) + (-a + ε)) * ⟪u, T u⟫ + (a - ε) * (-a + ε) * ‖T u‖ ^ 2 := by
        fun_prop
      have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
          0 ≤ ‖u‖ ^ 2 + ((a - ε) + (-a + ε)) * ⟪u, T u⟫ + (a - ε) * (-a + ε) * ‖T u‖ ^ 2 := by
        filter_upwards [Ioo_mem_nhdsGT ha] with ε hε
        refine hlead u hu (a - ε) (-a + ε) ?_ ?_ ?_ ?_
        · rw [hylo]; exact_mod_cast (by linarith [hε.2] : -a < a - ε)
        · exact_mod_cast (by linarith [hε.1] : a - ε < a)
        · rw [hylo]; exact_mod_cast (by linarith [hε.1] : -a < -a + ε)
        · exact_mod_cast (by linarith [hε.2] : -a + ε < a)
      have := ge_of_tendsto ((hg.tendsto 0).mono_left nhdsWithin_le_nhds) hpos
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      have h2 : a * a * ‖T u‖ ^ 2 ≤ ‖u‖ ^ 2 := by simpa using this
      nlinarith [h2]
    intro u hu'
    have hhom : ∀ (c : ℝ) (x : V), ‖c • x‖ ^ 2 - ‖a • T (c • x)‖ ^ 2 =
        c ^ 2 * (‖x‖ ^ 2 - ‖a • T x‖ ^ 2) := by
      intro c x
      simp only [map_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]; ring
    have := nonneg_on_span_of_addSubgroup (q := fun u => ‖u‖ ^ 2 - ‖a • T u‖ ^ 2)
      (by fun_prop) hhom hu u hu'
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (by linarith)
  · -- `yhi = +∞`, `ylo = b`: `y' → b`, then `y → +∞`
    rintro b rfl rfl
    have hb : b < 0 := by exact_mod_cast hlo
    have hu : ∀ u ∈ L, 0 ≤ ⟪u, T u⟫ + b * ‖T u‖ ^ 2 := by
      intro u hu
      -- first `y' = b` in the limit, for each `y > 0`
      have hy : ∀ y : ℝ, 0 < y → 0 ≤ ‖u‖ ^ 2 + (y + b) * ⟪u, T u⟫ + y * b * ‖T u‖ ^ 2 := by
        intro y hy
        have hg : Continuous fun ε : ℝ =>
            ‖u‖ ^ 2 + (y + (b + ε)) * ⟪u, T u⟫ + y * (b + ε) * ‖T u‖ ^ 2 := by fun_prop
        have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
            0 ≤ ‖u‖ ^ 2 + (y + (b + ε)) * ⟪u, T u⟫ + y * (b + ε) * ‖T u‖ ^ 2 := by
          filter_upwards [self_mem_nhdsWithin] with ε hε
          refine hlead u hu y (b + ε) ?_ (EReal.coe_lt_top _) ?_ (EReal.coe_lt_top _)
          · exact_mod_cast (by linarith : b < y)
          · exact_mod_cast (by linarith [show (0 : ℝ) < ε from hε] : b < b + ε)
        have := ge_of_tendsto ((hg.tendsto 0).mono_left nhdsWithin_le_nhds) hpos
        simpa using this
      by_contra hneg
      push Not at hneg
      set k := ⟪u, T u⟫ + b * ‖T u‖ ^ 2
      have hk : 0 < -k := by linarith
      obtain ⟨N, hN⟩ := exists_nat_gt ((‖u‖ ^ 2 + b * ⟪u, T u⟫) / -k)
      have hy0 : (0 : ℝ) < N + 1 := by positivity
      have := hy (N + 1) hy0
      have e : ‖u‖ ^ 2 + (↑N + 1 + b) * ⟪u, T u⟫ + (↑N + 1) * b * ‖T u‖ ^ 2 =
          (‖u‖ ^ 2 + b * ⟪u, T u⟫) + (N + 1) * k := by simp only [k]; ring
      rw [e] at this
      rw [div_lt_iff₀ hk] at hN
      nlinarith
    intro u hu'
    have hhom : ∀ (c : ℝ) (x : V), ⟪c • x, T (c • x)⟫ + b * ‖T (c • x)‖ ^ 2 =
        c ^ 2 * (⟪x, T x⟫ + b * ‖T x‖ ^ 2) := by
      intro c x
      simp only [map_smul, norm_smul, mul_pow, inner_smul_left, inner_smul_right,
        Real.norm_eq_abs, sq_abs, conj_trivial]; ring
    have := nonneg_on_span_of_addSubgroup (q := fun u => ⟪u, T u⟫ + b * ‖T u‖ ^ 2)
      (by fun_prop) hhom hu u hu'
    linarith
  · -- `ylo = −∞`, `yhi = a`: `y → a`, then `y' → −∞`
    rintro a rfl rfl
    have ha : 0 < a := by exact_mod_cast hhi
    have hu : ∀ u ∈ L, 0 ≤ -⟪u, T u⟫ - a * ‖T u‖ ^ 2 := by
      intro u hu
      have hy : ∀ y' : ℝ, y' < 0 → 0 ≤ ‖u‖ ^ 2 + (a + y') * ⟪u, T u⟫ + a * y' * ‖T u‖ ^ 2 := by
        intro y' hy'
        have hg : Continuous fun ε : ℝ =>
            ‖u‖ ^ 2 + ((a - ε) + y') * ⟪u, T u⟫ + (a - ε) * y' * ‖T u‖ ^ 2 := by fun_prop
        have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
            0 ≤ ‖u‖ ^ 2 + ((a - ε) + y') * ⟪u, T u⟫ + (a - ε) * y' * ‖T u‖ ^ 2 := by
          filter_upwards [self_mem_nhdsWithin] with ε hε
          refine hlead u hu (a - ε) y' (EReal.bot_lt_coe _) ?_ (EReal.bot_lt_coe _) ?_
          · exact_mod_cast (by linarith [show (0 : ℝ) < ε from hε] : a - ε < a)
          · exact_mod_cast (by linarith : y' < a)
        have := ge_of_tendsto ((hg.tendsto 0).mono_left nhdsWithin_le_nhds) hpos
        simpa using this
      by_contra hneg
      push Not at hneg
      set k := ⟪u, T u⟫ + a * ‖T u‖ ^ 2
      have hk : 0 < k := by linarith
      obtain ⟨N, hN⟩ := exists_nat_gt ((‖u‖ ^ 2 + a * ⟪u, T u⟫) / k)
      have := hy (-(N + 1)) (by linarith [show (0 : ℝ) ≤ N from N.cast_nonneg])
      have e : ‖u‖ ^ 2 + (a + -(↑N + 1)) * ⟪u, T u⟫ + a * -(↑N + 1) * ‖T u‖ ^ 2 =
          (‖u‖ ^ 2 + a * ⟪u, T u⟫) - (N + 1) * k := by simp only [k]; ring
      rw [e] at this
      rw [div_lt_iff₀ hk] at hN
      nlinarith
    intro u hu'
    have hhom : ∀ (c : ℝ) (x : V), -⟪c • x, T (c • x)⟫ - a * ‖T (c • x)‖ ^ 2 =
        c ^ 2 * (-⟪x, T x⟫ - a * ‖T x‖ ^ 2) := by
      intro c x
      simp only [map_smul, norm_smul, mul_pow, inner_smul_left, inner_smul_right,
        Real.norm_eq_abs, sq_abs, conj_trivial]; ring
    have := nonneg_on_span_of_addSubgroup (q := fun u => -⟪u, T u⟫ - a * ‖T u‖ ^ 2)
      (by fun_prop) hhom hu u hu'
    linarith

end LinearAlgebra

/-! ## §1 [9.P] Barbot's coordinates `x v₀ + z + y vₙ` (l.2677–2735)

A point `x v₀ + z + y vₙ` (`v₀`, `vₙ` null, `⟨v₀ | vₙ⟩ = 1`, `z ∈ P̄₀ = {v₀, vₙ}^⊥`) is the triple
`(x, z, y) : ℝ × E × ℝ`, `E` a real inner product space standing for `P̄₀`; the form is
`Q = 2xy + |z|²` (`nolQ`). An element of `G(v₀)` is given by Barbot's data
`(R, u, v, μ, b)` (`NolParam`), acting by the formula of l.2705–2709 (`NolParam.act`). -/

section Model

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The Minkowski form in Barbot's coordinates**: `|x v₀ + z + y vₙ|² = 2xy + |z|²`. -/
noncomputable def nolQ (X : ℝ × E × ℝ) : ℝ := 2 * X.1 * X.2.2 + ‖X.2.1‖ ^ 2

/-- Its polar form: `⟨X | X'⟩ = x y' + x' y + ⟨z | z'⟩`. -/
noncomputable def nolB (X X' : ℝ × E × ℝ) : ℝ := X.1 * X'.2.2 + X'.1 * X.2.2 + ⟪X.2.1, X'.2.1⟫

variable (E) in
/-- **An element of `G(v₀)` in Barbot's coordinates** (l.2694–2710): the rotation `R` of `P̄₀`,
the vectors `u, v ∈ P̄₀`, and the reals `μ` (the `v₀`-component of the translation part, "not
characterized by `α(g)`") and `b` (the induced translation of `Q₁`). -/
@[ext] structure NolParam where
  /-- `R(g)`, a rotation of `P̄₀`. -/
  R : E ≃ₗᵢ[ℝ] E
  /-- `u(g)`. -/
  u : E
  /-- `v(g)`. -/
  v : E
  /-- `μ(g)`. -/
  μ : ℝ
  /-- `b(g)`. -/
  b : ℝ

namespace NolParam

/-- **The action of `g ∈ G(v₀)`** (l.2705–2709): linear part
`x v₀ + z + y vₙ ↦ (x − ⟨v | R z⟩ − (y/2)|v|²) v₀ + (R z + y v) + y vₙ`, translation part
`μ v₀ + u + b vₙ`. -/
noncomputable def act (g : NolParam E) (X : ℝ × E × ℝ) : ℝ × E × ℝ :=
  (X.1 - ⟪g.v, g.R X.2.1⟫ - X.2.2 / 2 * ‖g.v‖ ^ 2 + g.μ, g.R X.2.1 + X.2.2 • g.v + g.u,
    X.2.2 + g.b)

/-- The composition law of `G(v₀)` in Barbot's coordinates (cf. the commented l.2842–2844):
`R(gg') = R R'`, `v(gg') = v + R v'`, `u(gg') = u + R u' + b' v`, `b(gg') = b + b'`,
`μ(gg') = μ + μ' − ⟨v | R u'⟩ − (b'/2)|v|²`. -/
noncomputable def mul (g g' : NolParam E) : NolParam E where
  R := g'.R.trans g.R
  u := g.u + g.R g'.u + g'.b • g.v
  v := g.v + g.R g'.v
  μ := g.μ + g'.μ - ⟪g.v, g.R g'.u⟫ - g'.b / 2 * ‖g.v‖ ^ 2
  b := g.b + g'.b

/-- **The composition law** (`act` is a morphism). -/
theorem act_mul (g g' : NolParam E) (X : ℝ × E × ℝ) : (g.mul g').act X = g.act (g'.act X) := by
  obtain ⟨x, z, y⟩ := X
  simp only [act, mul, LinearIsometryEquiv.coe_trans, comp_apply, map_add, map_smul,
    Prod.mk.injEq]
  refine ⟨?_, by module, by ring⟩
  simp only [inner_add_left, inner_add_right, inner_smul_right, @norm_add_sq_real,
    LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.norm_map]
  ring

/-- **`G(v₀)` acts by isometries of `Q`**: `|g X − g X'|² = |X − X'|²`. -/
theorem nolQ_act_sub (g : NolParam E) (X X' : ℝ × E × ℝ) :
    nolQ (g.act X - g.act X') = nolQ (X - X') := by
  obtain ⟨x, z, y⟩ := X
  obtain ⟨x', z', y'⟩ := X'
  simp only [nolQ, act, Prod.mk_sub_mk]
  have e : g.R z + y • g.v + g.u - (g.R z' + y' • g.v + g.u) = g.R (z - z') + (y - y') • g.v := by
    rw [map_sub, sub_smul]; abel
  rw [e, @norm_add_sq_real, LinearIsometryEquiv.norm_map, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs, inner_smul_right, map_sub, inner_sub_left, real_inner_comm g.v (g.R z),
    real_inner_comm g.v (g.R z')]
  ring

/-- **(∗∗)** (l.2693–2694): the projection `π₀ : 𝐌ⁿ → Q₀ = 𝐌ⁿ/Δ₀`, `(x, z, y) ↦ (z, y)`, is
equivariant for `α(g)(z, y) = (R z + u + y v, y + b)`. -/
theorem act_proj₀ (g : NolParam E) (X : ℝ × E × ℝ) :
    ((g.act X).2.1, (g.act X).2.2) = (g.R X.2.1 + g.u + X.2.2 • g.v, X.2.2 + g.b) := by
  simp only [act, Prod.mk.injEq, and_true]; abel

/-- **`π₁ : 𝐌ⁿ → Q₁ = 𝐌ⁿ/P₀`** (l.2640–2643): `g` induces the translation by `b(g)`. -/
theorem act_proj₁ (g : NolParam E) (X : ℝ × E × ℝ) : (g.act X).2.2 = X.2.2 + g.b := rfl

/-- The translation part is `μ v₀ + u + b vₙ` (l.2709). -/
theorem act_zero (g : NolParam E) : g.act 0 = (g.μ, g.u, g.b) := by
  simp [act]

/-- **Purely unipotent** elements of `G(v₀)`, the group `𝒰(v₀)` (l.2718–2724): `R = id`. -/
def IsU (g : NolParam E) : Prop := g.R = LinearIsometryEquiv.refl ℝ E

/-- **The kernel `𝒜(v₀)` of `b : 𝒰(v₀) → ℝ`** (l.2731–2735). -/
def IsA (g : NolParam E) : Prop := g.IsU ∧ g.b = 0

/-- **(∗∗′)** (l.2721–2729): the action of a purely unipotent element. -/
theorem act_of_isU {g : NolParam E} (hg : g.IsU) (X : ℝ × E × ℝ) :
    g.act X = (X.1 - ⟪g.v, X.2.1⟫ - X.2.2 / 2 * ‖g.v‖ ^ 2 + g.μ, X.2.1 + X.2.2 • g.v + g.u,
      X.2.2 + g.b) := by
  rw [act, hg]; rfl

/-- `𝒰(v₀)` is closed under composition ("Therefore, they form a group", l.2724). -/
theorem IsU.mul {g g' : NolParam E} (hg : g.IsU) (hg' : g'.IsU) : (g.mul g').IsU := by
  simp only [IsU, NolParam.mul] at *; rw [hg, hg']; rfl

/-- `𝒜(v₀)` is closed under composition. -/
theorem IsA.mul {g g' : NolParam E} (hg : g.IsA) (hg' : g'.IsA) : (g.mul g').IsA :=
  ⟨hg.1.mul hg'.1, by simp [NolParam.mul, hg.2, hg'.2]⟩

/-- **"`Γ` is abelian ⇒ `⟨u(γ') | v(γ)⟩ = ⟨u(γ) | v(γ')⟩`"** (l.2918–2924): two commuting
elements of `𝒜(v₀)`. -/
theorem inner_comm_of_commute {g g' : NolParam E} (hg : g.IsA) (hg' : g'.IsA)
    (hc : ∀ X, g.act (g'.act X) = g'.act (g.act X)) : ⟪g'.u, g.v⟫ = ⟪g.u, g'.v⟫ := by
  have h := congrArg Prod.fst (hc 0)
  rw [← act_mul, ← act_mul, act_zero, act_zero] at h
  have h1 : g.R = LinearIsometryEquiv.refl ℝ E := hg.1
  have h1' : g'.R = LinearIsometryEquiv.refl ℝ E := hg'.1
  simp only [NolParam.mul, h1, h1', hg.2, hg'.2, LinearIsometryEquiv.coe_refl, id] at h
  rw [real_inner_comm g.v g'.u, real_inner_comm g'.v g.u]
  linarith

/-- **The `p`-th power of `g ∈ 𝒜(v₀)`** (l.2969): `u(gᵖ) = p u`, `v(gᵖ) = p v`,
`μ(gᵖ) = p μ + (p(1−p)/2) ⟨u | v⟩`. -/
noncomputable def powA (g : NolParam E) (p : ℕ) : NolParam E :=
  ⟨LinearIsometryEquiv.refl ℝ E, (p : ℝ) • g.u, (p : ℝ) • g.v,
    p * g.μ + p * (1 - p) / 2 * ⟪g.u, g.v⟫, 0⟩

theorem mul_powA {g : NolParam E} (hg : g.IsA) (p : ℕ) : g.mul (g.powA p) = g.powA (p + 1) := by
  have hR : g.R = LinearIsometryEquiv.refl ℝ E := hg.1
  ext x
  · simp [NolParam.mul, powA, hR]
  · simp only [NolParam.mul, powA, hR, LinearIsometryEquiv.coe_refl, id, zero_smul, add_zero]
    push_cast; module
  · simp only [NolParam.mul, powA, hR, LinearIsometryEquiv.coe_refl, id]
    push_cast; module
  · simp only [NolParam.mul, powA, hR, LinearIsometryEquiv.coe_refl, id, inner_smul_right,
      real_inner_comm g.u g.v]
    push_cast; ring
  · simp [NolParam.mul, powA, hg.2]

/-- **`gᵖ` acts as the `p`-th iterate of `g`.** -/
theorem iterate_act {g : NolParam E} (hg : g.IsA) (p : ℕ) (X : ℝ × E × ℝ) :
    g.act^[p] X = (g.powA p).act X := by
  induction p with
  | zero => simp [powA, act]
  | succ p ih => rw [iterate_succ_apply', ih, ← act_mul, mul_powA hg]

/-- **The iterates `γᵖ(x, z, y)`** (l.2972). -/
theorem powA_act (g : NolParam E) (p : ℕ) (X : ℝ × E × ℝ) :
    (g.powA p).act X = (X.1 + p * g.μ + p * (1 - p) / 2 * ⟪g.u, g.v⟫ - p * ⟪g.v, X.2.1⟫ -
      X.2.2 / 2 * p ^ 2 * ‖g.v‖ ^ 2, X.2.1 + (p : ℝ) • g.u + (X.2.2 * p) • g.v, X.2.2) := by
  simp only [act, powA, LinearIsometryEquiv.coe_refl, id, inner_smul_left, norm_smul,
    conj_trivial, Real.norm_eq_abs, mul_pow, sq_abs, Prod.mk.injEq, add_zero, and_true]
  refine ⟨by ring, ?_⟩
  rw [smul_smul, mul_comm]; abel

/-- **The leading term** (l.2974–2976): `|γᵖ X − X'|² = p² ⟨u + y v | u + y' v⟩ + p B + |X − X'|²`
for `γ ∈ 𝒜(v₀)`, `X = (x, z, y)`, `X' = (x', z', y')`; the coefficient of `p²` is Barbot's
`|u|² + (y + y')⟨u | v⟩ + y y' |v|²`. -/
theorem nolQ_powA_sub (g : NolParam E) (p : ℕ) (X X' : ℝ × E × ℝ) :
    nolQ ((g.powA p).act X - X') =
      (p : ℝ) ^ 2 * ⟪g.u + X.2.2 • g.v, g.u + X'.2.2 • g.v⟫ +
        p * (2 * (X.2.2 - X'.2.2) * (g.μ + ⟪g.u, g.v⟫ / 2 - ⟪g.v, X.2.1⟫) +
          2 * ⟪X.2.1 - X'.2.1, g.u + X.2.2 • g.v⟫) + nolQ (X - X') := by
  obtain ⟨x, z, y⟩ := X
  obtain ⟨x', z', y'⟩ := X'
  rw [powA_act]
  simp only [nolQ, Prod.mk_sub_mk]
  have e : z + (p : ℝ) • g.u + (y * p) • g.v - z' = (z - z') + (p : ℝ) • (g.u + y • g.v) := by
    rw [smul_add, smul_smul, mul_comm (p : ℝ) y]; abel
  rw [e, @norm_add_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inner_smul_right,
    ← real_inner_self_eq_norm_sq (g.u + y • g.v), nol_leading_eq, nol_leading_eq]
  ring

end NolParam

/-- **A quadratic nonnegative at every natural number has nonnegative leading coefficient.** -/
theorem leading_nonneg_of_forall_nat {A B C : ℝ} (h : ∀ p : ℕ, 0 ≤ (p : ℝ) ^ 2 * A + p * B + C) :
    0 ≤ A := by
  by_contra hA
  push Not at hA
  obtain ⟨N, hN⟩ := exists_nat_gt ((|B| + |C|) / -A)
  have hN1 : (1 : ℝ) ≤ N + 1 := by linarith [show (0 : ℝ) ≤ N from N.cast_nonneg]
  have h1 := h (N + 1)
  push_cast at h1
  rw [div_lt_iff₀ (by linarith)] at hN
  have hB : (N + 1 : ℝ) * B ≤ (N + 1) * |B| :=
    mul_le_mul_of_nonneg_left (le_abs_self B) (by linarith)
  have hC : C ≤ (N + 1) * |C| := by nlinarith [le_abs_self C, abs_nonneg C]
  have hneg : (N + 1 : ℝ) * A + |B| + |C| < 0 := by nlinarith
  have : (N + 1 : ℝ) * ((N + 1) * A + |B| + |C|) < 0 := mul_neg_of_pos_of_neg (by linarith) hneg
  nlinarith

end Model

/-! ## §2 Prop 9.3, [9.b], Rem 9.4, Rem 9.2 and the group `A`, in Barbot's coordinates -/

section ModelResults

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open NolParam

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- An invariant set is invariant under every iterate. -/
theorem nol_iterate_mem {f : ℝ × E × ℝ → ℝ × E × ℝ} {St : Set (ℝ × E × ℝ)}
    (hinv : ∀ X ∈ St, f X ∈ St) (p : ℕ) {X : ℝ × E × ℝ} (hX : X ∈ St) : f^[p] X ∈ St := by
  induction p with
  | zero => exact hX
  | succ p ih => rw [iterate_succ_apply']; exact hinv _ ih

/-- **"No `γ`-iterate of `X` can be in the causal future of `X'`, [so] this term must be
positive"** (l.2978–2979): for `γ ∈ 𝒜(v₀)` preserving an achronal set `St`
(`0 ≤ |X − X'|²` on `St`) and `X, X' ∈ St`, the leading coefficient is `≥ 0`. -/
theorem leading_nonneg_of_achronal {St : Set (ℝ × E × ℝ)}
    (hach : ∀ X ∈ St, ∀ X' ∈ St, 0 ≤ nolQ (X - X')) {g : NolParam E} (hg : g.IsA)
    (hinv : ∀ X ∈ St, g.act X ∈ St) {X X' : ℝ × E × ℝ} (hX : X ∈ St) (hX' : X' ∈ St) :
    0 ≤ ⟪g.u + X.2.2 • g.v, g.u + X'.2.2 • g.v⟫ := by
  refine leading_nonneg_of_forall_nat (B := 2 * (X.2.2 - X'.2.2) *
    (g.μ + ⟪g.u, g.v⟫ / 2 - ⟪g.v, X.2.1⟫) + 2 * ⟪X.2.1 - X'.2.1, g.u + X.2.2 • g.v⟫)
    (C := nolQ (X - X')) fun p => ?_
  have := hach _ (nol_iterate_mem hinv p hX) X' hX'
  rwa [iterate_act hg, nolQ_powA_sub] at this

/-- **Prop 9.3 in Barbot's coordinates** (`bprop:limites`, l.2940–2989): let `St` (Barbot's
`S̃`) be achronal, with `π₁(St) ⊇ ]ylo, yhi[`, `ylo < 0 < yhi`, preserved by elements of `𝒜(v₀)`
with `u`-vectors forming an additive group `L` and `v = T u` for a linear `T`; let some element
be parabolic (`T u ≠ 0`). Then `ylo`, `yhi` are not both infinite and Barbot's inequalities hold
on `E = span L`. -/
theorem bprop_limites_model [FiniteDimensional ℝ E] {St : Set (ℝ × E × ℝ)}
    (hach : ∀ X ∈ St, ∀ X' ∈ St, 0 ≤ nolQ (X - X')) {T : E →ₗ[ℝ] E} {L : AddSubgroup E}
    (hΓ : ∀ u ∈ L, ∃ g : NolParam E, g.IsA ∧ g.u = u ∧ g.v = T u ∧ ∀ X ∈ St, g.act X ∈ St)
    {ylo yhi : EReal} (hlo : ylo < 0) (hhi : 0 < yhi)
    (hI : ∀ y : ℝ, ylo < y → (y : EReal) < yhi → ∃ X ∈ St, X.2.2 = y)
    (hpar : ∃ u ∈ L, T u ≠ 0) :
    ¬(ylo = ⊥ ∧ yhi = ⊤) ∧ LimitesIneq (span ℝ (L : Set E)) T ylo yhi := by
  refine limites_of_leading hlo hhi (fun u hu y y' hy hy' hy₂ hy₂' => ?_) hpar
  obtain ⟨g, hg, rfl, hv, hinv⟩ := hΓ u hu
  obtain ⟨X, hX, rfl⟩ := hI y hy hy'
  obtain ⟨X', hX', rfl⟩ := hI y' hy₂ hy₂'
  rw [← hv]
  exact leading_nonneg_of_achronal hach hg hinv hX hX'

/-- **Rem 9.4** (`unipcomplet`, l.2958–2963), the computation behind "`Ω(S̃)` is the entire
Minkowski space": for `γ ∈ 𝒜(v₀)` with `u + y v ≠ 0` for every `y` (no linear iterate),
`|γᵖ X − X|² = p² |u + y v|² > 0` for every `X` and `p ≥ 1`, so `Ω_γ` is everything. With
`bprop_limites_model`, `I ≠ ℝ = I'`. Consequence (module SCOPE, finding 6): in that case
`M(S) = Γ\𝐌ⁿ` is strictly larger than the unipotent `Γ\Ω`, `Ω` the slab containing `𝒟(M̃)`, so
the parabolic output (`nonloxodromic_parabolic`) is stated for `M`, not for `M(S)`. -/
theorem unipcomplet_model {g : NolParam E} (hg : ∀ y : ℝ, g.u + y • g.v ≠ 0) (X : ℝ × E × ℝ)
    {p : ℕ} (hp : 0 < p) : 0 < nolQ ((g.powA p).act X - X) := by
  rw [nolQ_powA_sub, sub_self, sub_self, sub_self]
  simp only [mul_zero, zero_mul, inner_zero_left, add_zero]
  have h0 : nolQ (0 : ℝ × E × ℝ) = 0 := by simp [nolQ]
  rw [h0, add_zero, real_inner_self_eq_norm_sq]
  have : 0 < ‖g.u + X.2.2 • g.v‖ := norm_pos_iff.2 (hg _)
  have : (0 : ℝ) < p := by exact_mod_cast hp
  positivity

/-- **[9.b], the triviality of `b`** (l.2767–2787), proved without Lemma 7.1 and Cor 8.3: if the
achronal `St` is preserved by `γ₀` with `b(γ₀) ≠ 0` and by an element `γ₀'` with
`b(γ₀') = −b(γ₀)` (e.g. `γ₀⁻¹`), then `π₁(St)` is unbounded both ways, and a purely unipotent
parabolic `γ₁ ∈ 𝒜(v₀)` (`v(γ₁) ≠ 0`) preserving `St` gives a negative leading coefficient at
heights `y₀ + k b`, `y₀ − k b`: contradiction. -/
theorem b_trivial_model {St : Set (ℝ × E × ℝ)} (hach : ∀ X ∈ St, ∀ X' ∈ St, 0 ≤ nolQ (X - X'))
    (hne : St.Nonempty) {g₁ : NolParam E} (hg₁ : g₁.IsA) (hv : g₁.v ≠ 0)
    (hinv₁ : ∀ X ∈ St, g₁.act X ∈ St) {g₀ g₀' : NolParam E} (hb : g₀.b ≠ 0) (hb' : g₀'.b = -g₀.b)
    (hinv₀ : ∀ X ∈ St, g₀.act X ∈ St) (hinv₀' : ∀ X ∈ St, g₀'.act X ∈ St) : False := by
  obtain ⟨X₀, hX₀⟩ := hne
  have hh : ∀ (g : NolParam E) (k : ℕ) (X : ℝ × E × ℝ), (g.act^[k] X).2.2 = X.2.2 + k * g.b := by
    intro g k X
    induction k with
    | zero => simp
    | succ k ih => rw [iterate_succ_apply', act_proj₁, ih]; push_cast; ring
  have hv2 : 0 < ‖g₁.v‖ ^ 2 := by have := norm_pos_iff.2 hv; positivity
  have hb2 : 0 < g₀.b ^ 2 := by positivity
  set y₀ := X₀.2.2
  set K := ‖g₁.u‖ ^ 2 + 2 * y₀ * ⟪g₁.u, g₁.v⟫ + y₀ ^ 2 * ‖g₁.v‖ ^ 2
  obtain ⟨k, hk⟩ := exists_nat_gt (K / (g₀.b ^ 2 * ‖g₁.v‖ ^ 2))
  have hk1 : (k : ℝ) ≤ (k : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos k with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ k := by exact_mod_cast h
      nlinarith
  have := leading_nonneg_of_achronal hach hg₁ hinv₁ (nol_iterate_mem hinv₀ k hX₀)
    (nol_iterate_mem hinv₀' k hX₀)
  rw [hh, hh, hb', nol_leading_eq] at this
  rw [div_lt_iff₀ (by positivity)] at hk
  have e : ‖g₁.u‖ ^ 2 + (y₀ + k * g₀.b + (y₀ + k * -g₀.b)) * ⟪g₁.u, g₁.v⟫ +
      (y₀ + k * g₀.b) * (y₀ + k * -g₀.b) * ‖g₁.v‖ ^ 2 = K - k ^ 2 * (g₀.b ^ 2 * ‖g₁.v‖ ^ 2) := by
    simp only [K]; ring
  rw [e] at this
  nlinarith [mul_pos hb2 hv2]

/-- **The `p`-th power of a purely unipotent `g ∈ 𝒰(v₀)`** (with `b ≠ 0` allowed):
`u_p = p u + (b p(p−1)/2) v`, `v_p = p v`, `b_p = p b`,
`μ_p = p μ − (p(p−1)/2) ⟨u | v⟩ − b |v|² (p−1)p(2p−1)/12`. -/
noncomputable def NolParam.powU (g : NolParam E) (p : ℕ) : NolParam E :=
  ⟨LinearIsometryEquiv.refl ℝ E, (p : ℝ) • g.u + (g.b * p * (p - 1) / 2) • g.v, (p : ℝ) • g.v,
    p * g.μ - p * (p - 1) / 2 * ⟪g.u, g.v⟫ - g.b * ‖g.v‖ ^ 2 * ((p - 1) * p * (2 * p - 1) / 12),
    p * g.b⟩

theorem mul_powU {g : NolParam E} (hg : g.IsU) (p : ℕ) : g.mul (g.powU p) = g.powU (p + 1) := by
  have hR : g.R = LinearIsometryEquiv.refl ℝ E := hg
  ext x
  · simp [NolParam.mul, NolParam.powU, hR]
  · simp only [NolParam.mul, NolParam.powU, hR, LinearIsometryEquiv.coe_refl, id]
    push_cast; module
  · simp only [NolParam.mul, NolParam.powU, hR, LinearIsometryEquiv.coe_refl, id]
    push_cast; module
  · simp only [NolParam.mul, NolParam.powU, hR, LinearIsometryEquiv.coe_refl, id, inner_add_right,
      inner_smul_right, real_inner_self_eq_norm_sq, real_inner_comm g.u g.v]
    push_cast; ring
  · simp only [NolParam.mul, NolParam.powU]; push_cast; ring

theorem iterate_act_U {g : NolParam E} (hg : g.IsU) (p : ℕ) (X : ℝ × E × ℝ) :
    g.act^[p] X = (g.powU p).act X := by
  induction p with
  | zero => simp [NolParam.powU, act]
  | succ p ih => rw [iterate_succ_apply', ih, ← act_mul, mul_powU hg]

/-- **The quartic** (cf. AchronalDomains' transverse case): for `g ∈ 𝒰(v₀)`,
`|gᵖ X − X|² = p² (γ − b² |v|² p² / 12)`. -/
theorem nolQ_powU_sub (g : NolParam E) (p : ℕ) (X : ℝ × E × ℝ) :
    nolQ ((g.powU p).act X - X) = (p : ℝ) ^ 2 * ((2 * g.b * (g.μ - ⟪g.v, X.2.1⟫) -
      g.b * X.2.2 * ‖g.v‖ ^ 2 + ‖g.u + X.2.2 • g.v‖ ^ 2 + g.b ^ 2 * ‖g.v‖ ^ 2 / 12) -
        g.b ^ 2 * ‖g.v‖ ^ 2 * p ^ 2 / 12) := by
  obtain ⟨x, z, y⟩ := X
  simp only [nolQ, act, NolParam.powU, LinearIsometryEquiv.coe_refl, id, Prod.mk_sub_mk]
  have e : z + y • (p : ℝ) • g.v + ((p : ℝ) • g.u + (g.b * p * (p - 1) / 2) • g.v) - z =
      (p : ℝ) • (g.u + y • g.v) + (g.b * p * (p - 1) / 2) • g.v := by
    rw [smul_add, smul_smul, smul_smul, mul_comm y (p : ℝ)]; abel
  rw [e, @norm_add_sq_real]
  simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inner_smul_left, inner_smul_right,
    inner_add_left, real_inner_self_eq_norm_sq, conj_trivial]
  ring

/-- **Purely unipotent parabolic elements are not transverse, in coordinates** (Lemma 8.6 and
Rem 8.9 `nini`; the commented item (4), l.2665–2666: "If `γ` is parabolic, `b(γ) = 0`"): a
`g ∈ 𝒰(v₀)` with `v ≠ 0` preserving a nonempty achronal set has `b = 0`. -/
theorem b_eq_zero_model {St : Set (ℝ × E × ℝ)} (hach : ∀ X ∈ St, ∀ X' ∈ St, 0 ≤ nolQ (X - X'))
    {X : ℝ × E × ℝ} (hX : X ∈ St) {g : NolParam E} (hg : g.IsU) (hv : g.v ≠ 0)
    (hinv : ∀ X ∈ St, g.act X ∈ St) : g.b = 0 := by
  by_contra hb
  set Γc := 2 * g.b * (g.μ - ⟪g.v, X.2.1⟫) - g.b * X.2.2 * ‖g.v‖ ^ 2 + ‖g.u + X.2.2 • g.v‖ ^ 2 +
    g.b ^ 2 * ‖g.v‖ ^ 2 / 12
  have hm : 0 < g.b ^ 2 * ‖g.v‖ ^ 2 / 12 := by
    have := norm_pos_iff.2 hv
    have : 0 < g.b ^ 2 := by positivity
    positivity
  set m := g.b ^ 2 * ‖g.v‖ ^ 2 / 12 with hm'
  have key : ∀ p : ℕ, 0 ≤ (p : ℝ) ^ 2 * (-m) + p * (-2 * m) + (Γc - m) := by
    intro p
    have h1 := hach _ (nol_iterate_mem hinv (p + 1) hX) X hX
    rw [iterate_act_U hg, nolQ_powU_sub] at h1
    have hp : (0 : ℝ) < ((p + 1 : ℕ) : ℝ) ^ 2 := by positivity
    have h2 := (mul_nonneg_iff_of_pos_left hp).1 h1
    push_cast at h2
    nlinarith [h2]
  have := leading_nonneg_of_forall_nat key
  linarith

/-- **The frame change of Rem 9.2**, corrected: replacing `vₙ` by the null vector
`vₙ' = vₙ + w − (|w|²/2) v₀` (`w ∈ P̄₀`) changes coordinates by
`(x, z, y) ↦ (x + ⟨w | z⟩ − (y/2)|w|², z − y w, y)`, which is the action of the element
`(id, 0, −w, 0, 0)` of `𝒜(v₀)`. -/
noncomputable def frameChange (w : E) : NolParam E := ⟨LinearIsometryEquiv.refl ℝ E, 0, -w, 0, 0⟩

theorem frameChange_isA (w : E) : (frameChange w).IsA := ⟨rfl, rfl⟩

theorem frameChange_act (w : E) (X : ℝ × E × ℝ) :
    (frameChange w).act X = (X.1 + ⟪w, X.2.1⟫ - X.2.2 / 2 * ‖w‖ ^ 2, X.2.1 - X.2.2 • w, X.2.2) := by
  simp only [act, frameChange, LinearIsometryEquiv.coe_refl, id, inner_neg_left, norm_neg,
    smul_neg, add_zero, Prod.mk.injEq, and_true]
  exact ⟨by ring, by abel⟩

/-- **The new frame is a null frame**, and Barbot's is not. The vectors `v₀ = (1, 0, 0)`,
`vₙ = (0, 0, 1)` and `vₙ' = (−|w|²/2, w, 1)`: `vₙ'` is null with `⟨v₀ | vₙ'⟩ = 1`, while
Rem 9.2's `vₙ + w` (`w ∈ P̄₀`) has `|vₙ + w|² = |w|²` and `vₙ + a v₀` has `|vₙ + a v₀|² = 2a`:
neither is null unless `w = 0`, `a = 0`. -/
theorem frameChange_null (w : E) :
    nolQ ((-(‖w‖ ^ 2 / 2), w, 1) : ℝ × E × ℝ) = 0 ∧
      nolB ((1, 0, 0) : ℝ × E × ℝ) (-(‖w‖ ^ 2 / 2), w, 1) = 1 ∧
      nolQ ((0, w, 1) : ℝ × E × ℝ) = ‖w‖ ^ 2 ∧ ∀ a : ℝ, nolQ ((a, 0, 1) : ℝ × E × ℝ) = 2 * a := by
  refine ⟨by simp [nolQ]; ring, by simp [nolB], by simp [nolQ], fun a => by simp [nolQ]⟩

/-- The frame change identity: `x v₀ + z + y vₙ = x' v₀ + (z' − ⟨z' | w⟩ v₀) + y' vₙ'` for
`(x', z', y') = (frameChange w).act (x, z, y)`, `vₙ' = vₙ + w − (|w|²/2) v₀`; and
`z' − ⟨z' | w⟩ v₀ ⊥ vₙ'`. -/
theorem frameChange_coords (w : E) (X : ℝ × E × ℝ) :
    let X' := (frameChange w).act X
    X = (X'.1 - ⟪X'.2.1, w⟫ - X'.2.2 * (‖w‖ ^ 2 / 2), X'.2.1 + X'.2.2 • w, X'.2.2) ∧
      nolB ((-⟪X'.2.1, w⟫, X'.2.1, 0) : ℝ × E × ℝ) (-(‖w‖ ^ 2 / 2), w, 1) = 0 := by
  intro X'
  obtain ⟨x, z, y⟩ := X
  simp only [X', frameChange_act, nolB]
  refine ⟨?_, by ring⟩
  simp only [Prod.mk.injEq, sub_add_cancel, and_true]
  rw [inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq, real_inner_comm]
  simp only [conj_trivial]; ring

/-- `frameChange (−w)` is the inverse of `frameChange w`. -/
theorem frameChange_mul_neg (w : E) (X : ℝ × E × ℝ) :
    ((frameChange w).mul (frameChange (-w))).act X = X := by
  rw [act_mul, frameChange_act, frameChange_act]
  obtain ⟨x, z, y⟩ := X
  simp only [Prod.mk.injEq, inner_sub_right, inner_neg_left, inner_neg_right, norm_neg,
    inner_smul_right, real_inner_self_eq_norm_sq, smul_neg, and_true]
  exact ⟨by ring, by abel⟩

/-- **Rem 9.2** (`choixcoord`, l.2737–2760), in the corrected frame: conjugating `g ∈ 𝒜(v₀)` by
the frame change keeps `u` and `v` and replaces `μ` by `μ + ⟨u | w⟩`, which is Barbot's
formula `μ'(g) = μ(g) + ⟨u(g) | w⟩` (l.2758). -/
theorem choixcoord {g : NolParam E} (hg : g.IsA) (w : E) :
    (frameChange w).mul (g.mul (frameChange (-w))) =
      ⟨LinearIsometryEquiv.refl ℝ E, g.u, g.v, g.μ + ⟪w, g.u⟫, 0⟩ := by
  have hR : g.R = LinearIsometryEquiv.refl ℝ E := hg.1
  ext x
  · simp [NolParam.mul, frameChange, hR]
  · simp [NolParam.mul, frameChange, hR, hg.2]
  · simp [NolParam.mul, frameChange, hR]
  · simp [NolParam.mul, frameChange, hR, hg.2]
  · simp [NolParam.mul, frameChange, hg.2]

/-- **The abelian group `A`** (l.3101–3111), basis-free: for a linear `T` and a linear form
`ℓ`, `t ↦ (id, t, T t, ℓ t − ⟨t | T t⟩/2, 0)`. With `T` diagonal in an orthonormal basis
(`T eᵢ = λᵢ eᵢ`) and `ℓ = ∑ tᵢ(μᵢ + λᵢ/2)`, this is Barbot's `φ`. -/
noncomputable def nolA (T : E →ₗ[ℝ] E) (ℓ : E →ₗ[ℝ] ℝ) (t : E) : NolParam E :=
  ⟨LinearIsometryEquiv.refl ℝ E, t, T t, ℓ t - ⟪t, T t⟫ / 2, 0⟩

theorem nolA_isA (T : E →ₗ[ℝ] E) (ℓ : E →ₗ[ℝ] ℝ) (t : E) : (nolA T ℓ t).IsA := ⟨rfl, rfl⟩

/-- **"`φ` is a morphism"** (l.3104, "It is easy to check"): exactly when `T` is symmetric. -/
theorem nolA_mul {T : E →ₗ[ℝ] E} (hT : IsSymmOn ⊤ T) (ℓ : E →ₗ[ℝ] ℝ) (t t' : E) :
    (nolA T ℓ t).mul (nolA T ℓ t') = nolA T ℓ (t + t') := by
  have h := hT t trivial t' trivial
  ext x
  · simp [NolParam.mul, nolA]
  · simp [NolParam.mul, nolA]
  · simp [NolParam.mul, nolA]
  · simp only [NolParam.mul, nolA, LinearIsometryEquiv.coe_refl, id, map_add, inner_add_left,
      inner_add_right, zero_div, zero_mul, sub_zero]
    rw [real_inner_comm t' (T t), ← h]; ring
  · simp [NolParam.mul, nolA]

/-- **The normalisation `μᵢ = −λᵢ/2`** (l.3113–3118): if `⟨w | t⟩ = −ℓ t` for all `t`, the
frame change by `w` conjugates `A_{T, ℓ}` to `A_{T, 0}`, whose `μ`-component is `−⟨t | T t⟩/2`
(Barbot's `−∑ λᵢ tᵢ²/2`). -/
theorem choixcoord_nolA (T : E →ₗ[ℝ] E) (ℓ : E →ₗ[ℝ] ℝ) {w : E} (hw : ∀ t, ⟪w, t⟫ = -ℓ t)
    (t : E) : (frameChange w).mul ((nolA T ℓ t).mul (frameChange (-w))) = nolA T 0 t := by
  rw [choixcoord (nolA_isA T ℓ t)]
  simp only [nolA, hw, LinearMap.zero_apply]
  congr 1; ring

/-- **The cocycle `μ`** (l.2920): for commuting `γ, γ' ∈ 𝒜(v₀)` with `v = T u`, the corrected
`ν(γ) = μ(γ) + ⟨u | T u⟩/2` is additive, so it is `ℓ ∘ u` for a linear `ℓ` once `u(Γ)` is a
lattice of `E` (Barbot's choice of the `μᵢ`, l.3106–3108). -/
theorem nu_mul {T : E →ₗ[ℝ] E} {g g' : NolParam E} (hg : g.IsA) (hg' : g'.IsA)
    (hv : g.v = T g.u) (hsym : ⟪g.u, T g'.u⟫ = ⟪g'.u, T g.u⟫) :
    (g.mul g').μ + ⟪(g.mul g').u, T (g.mul g').u⟫ / 2 =
      (g.μ + ⟪g.u, T g.u⟫ / 2) + (g'.μ + ⟪g'.u, T g'.u⟫ / 2) := by
  have hR : g.R = LinearIsometryEquiv.refl ℝ E := hg.1
  simp only [NolParam.mul, hR, LinearIsometryEquiv.coe_refl, id, hg'.2, zero_smul, add_zero,
    zero_div, zero_mul, sub_zero, map_add, inner_add_left, inner_add_right, hv]
  rw [real_inner_comm g'.u (T g.u), ← hsym]
  ring

/-- A purely unipotent element with `v = T u` and `μ + ⟨u | T u⟩/2 = ℓ u` lies in `A_{T, ℓ}`
("`φ(u(γ)) = γ`", l.3108–3109). -/
theorem eq_nolA {T : E →ₗ[ℝ] E} {ℓ : E →ₗ[ℝ] ℝ} {g : NolParam E} (hg : g.IsA) (hv : g.v = T g.u)
    (hμ : g.μ + ⟪g.u, T g.u⟫ / 2 = ℓ g.u) : g = nolA T ℓ g.u := by
  ext x
  · rw [show g.R = _ from hg.1]; rfl
  · rfl
  · exact hv
  · simp only [nolA]; linarith
  · exact hg.2

/-- **The no-pole slab lies in `Ω(A)`** (l.2927–2932, l.3120–3122): for `T̂` given by Prop 9.5,
every point with `y ∈ ]ylo, yhi[` lies in Barbot's `Ω(A) = {(x, z, y) | ∀ t ≠ 0, t + y T̂ t ≠ 0}`. -/
theorem mem_omegaA_of_limites [FiniteDimensional ℝ E] {T : E →ₗ[ℝ] E} {ylo yhi : EReal}
    (hlo : ylo < 0)
    (hhi : 0 < yhi) (hnorm : ylo = -yhi ∨ yhi = ⊤ ∨ ylo = ⊥) (hfin : ¬(ylo = ⊥ ∧ yhi = ⊤))
    (h : LimitesIneq ⊤ T ylo yhi) {X : ℝ × E × ℝ} (hX₁ : ylo < X.2.2)
    (hX₂ : (X.2.2 : EReal) < yhi) :
    ∀ t : E, t ≠ 0 → t + X.2.2 • T t ≠ 0 :=
  fun _ ht => h.add_smul_ne_zero hlo hhi hnorm hfin hX₁ hX₂ ht

/-- **"In summary, we have proven that `Γ` is precisely as described in the introduction"**
(l.3101–3122), in Barbot's coordinates: from Prop 9.3 and Prop 9.5, a symmetric `T̂` on all of
`P̄₀` extending `T`, and one frame change `w` (Rem 9.2, `μᵢ = −λᵢ/2`), such that every element of
`Γ` (in `𝒜(v₀)`, `v = T u`, with the cocycle `μ + ⟨u | T u⟩/2` equal to a linear form `ℓ` on
`u`) is conjugate to the element `u` of the abelian group `A_{T̂, 0}`, and `S̃ ⊆ Ω(A_{T̂})` (the
heights of `S̃` lie in `]ylo, yhi[`, where `1 + y T̂` is injective). -/
theorem conclusion_model [FiniteDimensional ℝ E] {St : Set (ℝ × E × ℝ)}
    (hach : ∀ X ∈ St, ∀ X' ∈ St, 0 ≤ nolQ (X - X')) {T : E →ₗ[ℝ] E} {L : AddSubgroup E}
    (hΓ : ∀ u ∈ L, ∃ g : NolParam E, g.IsA ∧ g.u = u ∧ g.v = T u ∧ ∀ X ∈ St, g.act X ∈ St)
    (hsym : IsSymmOn (span ℝ (L : Set E)) T) {ylo yhi : EReal} (hlo : ylo < 0) (hhi : 0 < yhi)
    (hnorm : ylo = -yhi ∨ yhi = ⊤ ∨ ylo = ⊥)
    (hI : ∀ y : ℝ, ylo < y → (y : EReal) < yhi → ∃ X ∈ St, X.2.2 = y)
    (hIsub : ∀ X ∈ St, ylo < X.2.2 ∧ (X.2.2 : EReal) < yhi) (hpar : ∃ u ∈ L, T u ≠ 0)
    (ℓ : E →ₗ[ℝ] ℝ) :
    ∃ T' : E →ₗ[ℝ] E, (∀ u ∈ span ℝ (L : Set E), T' u = T u) ∧ IsSymmOn ⊤ T' ∧ ∃ w : E,
      (∀ g : NolParam E, g.IsA → g.v = T g.u → g.u ∈ span ℝ (L : Set E) →
        g.μ + ⟪g.u, T g.u⟫ / 2 = ℓ g.u →
          (frameChange w).mul (g.mul (frameChange (-w))) = nolA T' 0 g.u) ∧
      ∀ X ∈ St, ∀ t : E, t ≠ 0 → t + ((frameChange w).act X).2.2 • T' t ≠ 0 := by
  obtain ⟨hfin, hineq⟩ := bprop_limites_model hach hΓ hlo hhi hI hpar
  obtain ⟨T', hext, hsym', hineq'⟩ := bprop_extension hsym hlo hhi hnorm hfin hineq
  set w : E := (InnerProductSpace.toDual ℝ E).symm (-(LinearMap.toContinuousLinearMap ℓ))
  have hw : ∀ t, ⟪w, t⟫ = -ℓ t := fun t => by
    rw [InnerProductSpace.toDual_symm_apply]; rfl
  refine ⟨T', hext, hsym', w, fun g hg hv hu hμ => ?_, fun X hX t ht => ?_⟩
  · have h1 : g = nolA T ℓ g.u := eq_nolA hg hv hμ
    have h2 : nolA T ℓ g.u = nolA T' ℓ g.u := by
      simp only [nolA, hext _ hu]
    rw [h1, h2, choixcoord_nolA T' ℓ hw]
    rfl
  · rw [act_proj₁, show (frameChange w).b = 0 from rfl, add_zero]
    exact mem_omegaA_of_limites hlo hhi hnorm hfin hineq' (hIsub X hX).1 (hIsub X hX).2 t ht

end ModelResults

/-! ## §3 The coordinates in `𝐌ⁿ`, and the unipotent groups of `Flat/Examples` -/

section Minkowski

variable {d : ℕ}

/-- **Barbot's coordinates in `𝐌ⁿ`, `n = d + 2`**, through `Flat/Examples`' null coordinates:
`(x, z, y) ↦ ofNull x y z`, so `v₀ = ofNull 1 0 0`, `vₙ = ofNull 0 1 0` (null, `⟨v₀ | vₙ⟩ = 1`)
and `P̄₀ = {x = y = 0} ≅ ℝᵈ`. -/
noncomputable def nolToMink (X : ℝ × EuclideanSpace ℝ (Fin d) × ℝ) : Minkowski (d + 1) :=
  ofNull X.1 X.2.2 X.2.1

/-- The inverse chart. -/
noncomputable def minkToNol (p : Minkowski (d + 1)) : ℝ × EuclideanSpace ℝ (Fin d) × ℝ :=
  (nullX p, nullZ p, nullY p)

theorem minkToNol_nolToMink (X : ℝ × EuclideanSpace ℝ (Fin d) × ℝ) :
    minkToNol (nolToMink X) = X := by
  simp [minkToNol, nolToMink, nullX_ofNull, nullY_ofNull, nullZ_ofNull]

theorem minkQ_nolToMink (X : ℝ × EuclideanSpace ℝ (Fin d) × ℝ) :
    minkQ (nolToMink X) = nolQ X := by
  rw [minkQ_eq_null, nolToMink, nullX_ofNull, nullY_ofNull, nullZ_ofNull, nolQ]

theorem nolToMink_sub (X X' : ℝ × EuclideanSpace ℝ (Fin d) × ℝ) :
    nolToMink (X - X') = nolToMink X - nolToMink X' := by
  refine Prod.ext ?_ ?_
  · simp only [nolToMink, ofNull, Prod.fst_sub, Prod.snd_sub]; ring
  · ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [nolToMink, ofNull]; ring
    · simp [nolToMink, ofNull]

/-- **The diagonal operator** `T eᵢ = λᵢ eᵢ` (l.3101–3102), in the standard basis of `ℝᵈ`. -/
noncomputable def diagLin (ℓ : Fin d → ℝ) :
    EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d) where
  toFun t := WithLp.toLp 2 fun i => ℓ i * t i
  map_add' x y := by ext i; simp; ring
  map_smul' c x := by ext i; simp; ring

theorem isSymmOn_diagLin (ℓ : Fin d → ℝ) : IsSymmOn ⊤ (diagLin ℓ) := by
  intro u _ u' _
  simp only [diagLin, LinearMap.coe_mk, AddHom.coe_mk, PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **The unipotent groups of `Flat/Examples` are Barbot's `A`** (l.3101–3122): `unipAction ℓ t`
is, in Barbot's coordinates, the action of `A_{T, 0}` for the diagonal `T = diag(λ)`. -/
theorem unipAction_nolToMink (ℓ : Fin d → ℝ) (t : EuclideanSpace ℝ (Fin d))
    (X : ℝ × EuclideanSpace ℝ (Fin d) × ℝ) :
    unipAction ℓ t (nolToMink X) = nolToMink ((nolA (diagLin ℓ) 0 t).act X) := by
  obtain ⟨x, z, y⟩ := X
  simp only [unipAction, nolToMink, nullX_ofNull, nullY_ofNull, nullZ_ofNull, NolParam.act,
    nolA, LinearIsometryEquiv.coe_refl, id, LinearMap.zero_apply, add_zero]
  congr 1
  · simp only [diagLin, LinearMap.coe_mk, AddHom.coe_mk, PiLp.inner_apply, RCLike.inner_apply,
      conj_trivial, EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
    simp only [Finset.mul_sum, Finset.sum_div, sub_eq_add_neg, ← Finset.sum_neg_distrib,
      zero_add, add_assoc, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  · ext i; simp [diagLin]; ring

theorem nolToMink_minkToNol (p : Minkowski (d + 1)) : nolToMink (minkToNol p) = p := by
  have h : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2 : √2 ≠ 0 := by positivity
  refine Prod.ext ?_ ?_
  · simp only [nolToMink, minkToNol, ofNull, nullX, nullY]
    field_simp
    linear_combination (-p.1) * h
  · ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [nolToMink, minkToNol, ofNull, nullX, nullY]
      simp only [Fin.cons_zero]
      field_simp
      linear_combination (-p.2 0) * h
    · simp [nolToMink, minkToNol, ofNull, nullZ]

/-! ### `Stab(v₀)` in Barbot's coordinates (l.2701–2713), and [9.b] in `𝐌ⁿ` -/

/-- `nolToMink` is linear. -/
noncomputable def nolToMinkₗ : (ℝ × EuclideanSpace ℝ (Fin d) × ℝ) →ₗ[ℝ] Minkowski (d + 1) where
  toFun := nolToMink
  map_add' X X' := by
    have h := nolToMink_sub (X + X') X'
    rw [add_sub_cancel_right] at h
    rw [h, sub_add_cancel]
  map_smul' c X := by
    refine Prod.ext ?_ ?_
    · simp only [nolToMink, ofNull, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]
      ring
    · ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [nolToMink, ofNull]; ring
      · simp [nolToMink, ofNull]

/-- `minkToNol` is linear. -/
noncomputable def minkToNolₗ : Minkowski (d + 1) →ₗ[ℝ] (ℝ × EuclideanSpace ℝ (Fin d) × ℝ) where
  toFun := minkToNol
  map_add' p q := by
    simp only [minkToNol, nullX, nullY, nullZ, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk,
      Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · simp; ring
    · ext i; simp
    · simp; ring
  map_smul' c p := by
    simp only [minkToNol, nullX, nullY, nullZ, Prod.smul_fst, Prod.smul_snd, Prod.smul_mk,
      smul_eq_mul, RingHom.id_apply, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · simp; ring
    · ext i; simp
    · simp; ring

theorem nolQ_minkToNol (p : Minkowski (d + 1)) : nolQ (minkToNol p) = minkQ p := by
  rw [← minkQ_nolToMink, nolToMink_minkToNol]

theorem nolQ_add {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X Y : ℝ × E × ℝ) : nolQ (X + Y) = nolQ X + 2 * nolB X Y + nolQ Y := by
  simp only [nolQ, nolB, Prod.fst_add, Prod.snd_add, @norm_add_sq_real]; ring

/-- **The structure of `Stab(v₀)`** (l.2701–2713): an isometry whose linear part fixes
`v₀ = ofNull 1 0 0` acts, in Barbot's coordinates, as an element of `G(v₀)` (`NolParam`). -/
theorem exists_nolParam {γ : isom (d + 1)}
    (hfix : linOf γ (nolToMink (1, 0, 0)) = nolToMink (1, 0, 0)) :
    ∃ g : NolParam (EuclideanSpace ℝ (Fin d)), ∀ X, γ • nolToMink X = nolToMink (g.act X) := by
  set Λ : (ℝ × EuclideanSpace ℝ (Fin d) × ℝ) →ₗ[ℝ] (ℝ × EuclideanSpace ℝ (Fin d) × ℝ) :=
    minkToNolₗ ∘ₗ (linOf γ : Minkowski (d + 1) →ₗ[ℝ] Minkowski (d + 1)) ∘ₗ nolToMinkₗ
  have hΛ : ∀ X, Λ X = minkToNol (linOf γ (nolToMink X)) := fun _ => rfl
  have hQ : ∀ X, nolQ (Λ X) = nolQ X := fun X => by
    rw [hΛ, nolQ_minkToNol, lorentz.minkQ_apply (linOf_mem γ), minkQ_nolToMink]
  have hB : ∀ X Y, nolB (Λ X) (Λ Y) = nolB X Y := fun X Y => by
    have h1 := hQ (X + Y)
    rw [map_add, nolQ_add, nolQ_add, hQ, hQ] at h1
    linarith
  have h100 : Λ (1, 0, 0) = (1, 0, 0) := by
    rw [hΛ, hfix, minkToNol_nolToMink]
  set c := Λ (0, 0, 1) with hc
  have hc3 : c.2.2 = 1 := by
    have := hB (0, 0, 1) (1, 0, 0)
    rw [h100] at this
    simpa [nolB] using this
  have hc1 : c.1 = -(‖c.2.1‖ ^ 2 / 2) := by
    have := hQ (0, 0, 1)
    rw [← hc] at this
    simp only [nolQ, hc3] at this
    simp at this
    linarith
  -- the `z`-part
  set R₀ : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
    (LinearMap.fst ℝ (EuclideanSpace ℝ (Fin d)) ℝ ∘ₗ
      LinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin d) × ℝ)) ∘ₗ Λ ∘ₗ
      LinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin d) × ℝ) ∘ₗ
      LinearMap.inl ℝ (EuclideanSpace ℝ (Fin d)) ℝ
  have hR₀ : ∀ z, R₀ z = (Λ (0, z, 0)).2.1 := fun _ => rfl
  have hβ : ∀ z, (Λ (0, z, 0)).2.2 = 0 := fun z => by
    have := hB (0, z, 0) (1, 0, 0)
    rw [h100] at this
    simpa [nolB] using this
  have hnorm : ∀ z, ‖R₀ z‖ = ‖z‖ := fun z => by
    have := hQ (0, z, 0)
    simp only [nolQ, hβ, mul_zero, zero_add] at this
    rw [hR₀]
    have h2 : ‖(Λ (0, z, 0)).2.1‖ ^ 2 = ‖z‖ ^ 2 := by simpa using this
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2
  have ha : ∀ z, (Λ (0, z, 0)).1 = -⟪c.2.1, R₀ z⟫ := fun z => by
    have := hB (0, z, 0) (0, 0, 1)
    rw [← hc] at this
    simp only [nolB, hβ, hc3, mul_one, mul_zero, add_zero] at this
    simp at this
    rw [hR₀, real_inner_comm]
    linarith
  set R : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d) :=
    LinearIsometry.toLinearIsometryEquiv ⟨R₀, hnorm⟩ rfl
  have hR : ∀ z, R z = R₀ z := fun _ => rfl
  refine ⟨⟨R, (minkToNol (trOf γ)).2.1, c.2.1, (minkToNol (trOf γ)).1,
    (minkToNol (trOf γ)).2.2⟩, fun X => ?_⟩
  obtain ⟨x, z, y⟩ := X
  have hdec : ((x, z, y) : ℝ × EuclideanSpace ℝ (Fin d) × ℝ) =
      x • (1, 0, 0) + (0, z, 0) + y • (0, 0, 1) := by
    simp
  have hΛX : Λ (x, z, y) = (x - ⟪c.2.1, R z⟫ - y / 2 * ‖c.2.1‖ ^ 2, R z + y • c.2.1, y) := by
    rw [hdec, map_add, map_add, map_smul, map_smul, h100, ← hc]
    obtain ⟨c₁, cv, c₃⟩ := c
    simp only at hc1 hc3
    have e1 := ha z
    have e2 := hβ z
    have e3 := hR₀ z
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, mul_one, e1, hc1, hR]; ring
    · simp [← e3, hR]
    · simp only [Prod.snd_add, Prod.smul_snd, e2, hc3, smul_eq_mul]; simp
  rw [smul_eq_lin_add, ← nolToMink_minkToNol (linOf γ (nolToMink _) + trOf γ)]
  congr 1
  change minkToNolₗ (linOf γ (nolToMink (x, z, y)) + trOf γ) = _
  rw [map_add]
  change Λ (x, z, y) + minkToNol (trOf γ) = _
  rw [hΛX]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [NolParam.act, Prod.fst_add]
  · simp only [NolParam.act, Prod.snd_add, Prod.fst_add]
  · simp only [NolParam.act, Prod.snd_add]

/-- **Acausal sets are achronal in Barbot's coordinates**: `0 ≤ |X − X'|²` on the preimage. -/
theorem nolQ_nonneg_of_isAcausal {St : Set (Minkowski (d + 1))}
    (hac : (minkowski (d + 1)).IsAcausal St) {X X' : ℝ × EuclideanSpace ℝ (Fin d) × ℝ}
    (hX : nolToMink X ∈ St) (hX' : nolToMink X' ∈ St) : 0 ≤ nolQ (X - X') := by
  by_contra hneg
  push Not at hneg
  rw [← minkQ_nolToMink, nolToMink_sub] at hneg
  rcases isFutureTimelike_or_neg hneg with h | h
  · have hle : (minkowski (d + 1)).le ⊤ (nolToMink X') (nolToMink X) :=
      le_top_iff_minkQ.2 ⟨h.1.le, h.2.le⟩
    have := hac _ hX' _ hX hle
    rw [this, sub_self, minkQ_zero] at hneg; exact lt_irrefl _ hneg
  · rw [neg_sub] at h
    have hle : (minkowski (d + 1)).le ⊤ (nolToMink X) (nolToMink X') :=
      le_top_iff_minkQ.2 ⟨h.1.le, h.2.le⟩
    have := hac _ hX _ hX' hle
    rw [this, sub_self, minkQ_zero] at hneg; exact lt_irrefl _ hneg

/-- **Prop 9.3** (`bprop:limites`, l.2940–2989) for `S̃ ⊆ 𝐌ⁿ`, in Barbot's coordinates
(`v₀ = ofNull 1 0 0`, `vₙ = ofNull 0 1 0`): `S̃` acausal and preserved by `Γ`, whose elements
`u ∈ L` act through `𝒜(v₀)` with `v = T u`; `π₁(S̃) = nullY(S̃) ⊇ ]ylo, yhi[`, `ylo < 0 < yhi`;
some element parabolic. Then at least one extremity is finite and the inequalities hold on
`E = span L`. -/
theorem bprop_limites {St : Set (Minkowski (d + 1))} (hac : (minkowski (d + 1)).IsAcausal St)
    {T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)}
    {L : AddSubgroup (EuclideanSpace ℝ (Fin d))}
    (hΓ : ∀ u ∈ L, ∃ γ : isom (d + 1), (∀ p ∈ St, γ • p ∈ St) ∧ ∃ μ : ℝ, ∀ X,
      γ • nolToMink X =
        nolToMink ((⟨LinearIsometryEquiv.refl ℝ _, u, T u, μ, 0⟩ : NolParam _).act X))
    {ylo yhi : EReal} (hlo : ylo < 0) (hhi : 0 < yhi)
    (hI : ∀ y : ℝ, ylo < y → (y : EReal) < yhi → ∃ p ∈ St, nullY p = y)
    (hpar : ∃ u ∈ L, T u ≠ 0) :
    ¬(ylo = ⊥ ∧ yhi = ⊤) ∧ LimitesIneq (span ℝ (L : Set (EuclideanSpace ℝ (Fin d)))) T ylo yhi := by
  refine bprop_limites_model (St := nolToMink ⁻¹' St)
    (fun X hX X' hX' => nolQ_nonneg_of_isAcausal hac hX hX') (fun u hu => ?_) hlo hhi
    (fun y hy hy' => ?_) hpar
  · obtain ⟨γ, hinv, μ, hγ⟩ := hΓ u hu
    exact ⟨⟨LinearIsometryEquiv.refl ℝ _, u, T u, μ, 0⟩, ⟨rfl, rfl⟩, rfl, rfl, fun X hX => by
      show nolToMink _ ∈ St
      rw [← hγ]; exact hinv _ hX⟩
  · obtain ⟨p, hp, rfl⟩ := hI y hy hy'
    exact ⟨minkToNol p, by show nolToMink _ ∈ St; rw [nolToMink_minkToNol]; exact hp, rfl⟩

theorem nullY_nolToMink (X : ℝ × EuclideanSpace ℝ (Fin d) × ℝ) : nullY (nolToMink X) = X.2.2 :=
  nullY_ofNull _ _ _

/-- **[9.b] in `𝐌ⁿ`: the triviality of `b`** (l.2767–2787), in Barbot's coordinates: if the
linear parts of `Γ` fix `v₀ = ofNull 1 0 0`, `Γ` preserves a nonempty acausal `S̃` and contains a
purely unipotent parabolic `γ₁` (in coordinates `R(γ₁) = id`, `v(γ₁) ≠ 0`), then every element
of `Γ` preserves each null hyperplane `{y = c}`: `b ≡ 0`, the action of `Γ` on `Q₁` is trivial
(l.2867–2868). Neither Lemma 7.1 nor Cor 8.3 is used. -/
theorem b_trivial {Γ : Subgroup (isom (d + 1))} {St : Set (Minkowski (d + 1))}
    (hac : (minkowski (d + 1)).IsAcausal St) (hne : St.Nonempty)
    (hinv : ∀ γ ∈ Γ, ∀ p ∈ St, γ • p ∈ St)
    (hfix : ∀ γ ∈ Γ, linOf γ (nolToMink (1, 0, 0)) = nolToMink (1, 0, 0))
    {γ₁ : isom (d + 1)} (hγ₁ : γ₁ ∈ Γ) {g₁ : NolParam (EuclideanSpace ℝ (Fin d))} (hU : g₁.IsU)
    (hv : g₁.v ≠ 0) (hg₁ : ∀ X, γ₁ • nolToMink X = nolToMink (g₁.act X)) :
    ∀ γ ∈ Γ, ∀ p : Minkowski (d + 1), nullY (γ • p) = nullY p := by
  set St' := nolToMink ⁻¹' St
  have hach : ∀ X ∈ St', ∀ X' ∈ St', 0 ≤ nolQ (X - X') := fun X hX X' hX' =>
    nolQ_nonneg_of_isAcausal hac hX hX'
  obtain ⟨p₀, hp₀⟩ := hne
  have hX₀ : minkToNol p₀ ∈ St' := by
    show nolToMink _ ∈ St; rw [nolToMink_minkToNol]; exact hp₀
  have hinv' : ∀ {γ : isom (d + 1)} {g : NolParam (EuclideanSpace ℝ (Fin d))}, γ ∈ Γ →
      (∀ X, γ • nolToMink (d := d) X = nolToMink (g.act X)) → ∀ X ∈ St', g.act X ∈ St' := by
    intro γ g hγ hg X hX
    show nolToMink _ ∈ St
    rw [← hg]; exact hinv γ hγ _ hX
  have hb₁ : g₁.b = 0 := b_eq_zero_model hach hX₀ hU hv (hinv' hγ₁ hg₁)
  intro γ hγ p
  obtain ⟨g, hg⟩ := exists_nolParam (hfix γ hγ)
  obtain ⟨g', hg'⟩ := exists_nolParam (hfix γ⁻¹ (Γ.inv_mem hγ))
  have hbb : g'.b = -g.b := by
    have h1 : g'.act (g.act (minkToNol p₀)) = minkToNol p₀ := by
      have := congrArg minkToNol (hg' (g.act (minkToNol p₀)))
      rw [minkToNol_nolToMink, ← hg, ← mul_smul, inv_mul_cancel, one_smul,
        nolToMink_minkToNol] at this
      exact this.symm
    have h2 := congrArg (fun X => X.2.2) h1
    simp only [NolParam.act_proj₁] at h2
    linarith
  have hb : g.b = 0 := by
    by_contra hb
    exact b_trivial_model hach ⟨_, hX₀⟩ ⟨hU, hb₁⟩ hv (hinv' hγ₁ hg₁) hb hbb (hinv' hγ hg)
      (hinv' (Γ.inv_mem hγ) hg')
  rw [← nolToMink_minkToNol p, hg, nullY_nolToMink, NolParam.act_proj₁, hb, add_zero,
    nullY_nolToMink]

end Minkowski

/-! ## §4 The nonloxodromic case in `𝐌ⁿ`: Prop 9.1, [9.E], the invariance G6 -/

section Spacetime

variable {d : ℕ}

/-- **Prop 9.1** (`bprop:sanloxo`, l.2572–2597), through the external `BenoistNoLox`
(`Flat/Externals`), refined by the trichotomy: a group of isometries without loxodromic
element has a finite-index subgroup `Γ'` whose linear parts fix a timelike vector (and are
elliptic, [9.E]), or fix a nonzero null vector `v₀` — and then `Γ'` either contains a
parabolic element ([9.P], l.2621–2622) or consists of elliptic elements only (a branch the
paper does not treat, `exists_timelike_fixed_of_elliptic_of_null`). -/
theorem bprop_sanloxo (hB : BenoistNoLox d) {Γ : Subgroup (isom d)}
    (hΓ : ∀ γ ∈ Γ, ¬IsLoxodromic (linOf γ)) :
    ∃ Γ' : Subgroup (isom d), Γ' ≤ Γ ∧ Γ'.relIndex Γ ≠ 0 ∧
      ((∃ v : Minkowski d, minkQ v < 0 ∧ ∀ γ ∈ Γ', linOf γ v = v ∧ IsElliptic (linOf γ)) ∨
        ∃ v₀ : Minkowski d, v₀ ≠ 0 ∧ minkQ v₀ = 0 ∧ (∀ γ ∈ Γ', linOf γ v₀ = v₀) ∧
          ((∃ γ ∈ Γ', IsParabolic (linOf γ)) ∨ ∀ γ ∈ Γ', IsElliptic (linOf γ))) := by
  obtain ⟨Γ', hle, hidx, h⟩ := exists_finiteIndex_fixes_of_noLox hB hΓ
  refine ⟨Γ', hle, hidx, h.imp id fun ⟨v₀, hv0, hv, hfix⟩ => ⟨v₀, hv0, hv, hfix, ?_⟩⟩
  by_cases hp : ∃ γ ∈ Γ', IsParabolic (linOf γ)
  · exact Or.inl hp
  · push Not at hp
    refine Or.inr fun γ hγ => ?_
    rcases lorentz_trichotomy (linOf_mem γ) with h | h | h
    · exact h
    · exact absurd h (hΓ γ (hle hγ))
    · exact absurd h (hp γ hγ)

/-- **The branch Barbot does not treat** (l.2621–2622 asserts a parabolic `γ₁` "up to finite
index"): linear parts fixing a null `v₀` and all elliptic. -/
theorem exists_timelike_fixed_of_elliptic_of_null {Γ : Subgroup (isom d)} {v₀ : Minkowski d}
    (_hv0 : v₀ ≠ 0) (_hv : minkQ v₀ = 0) (_hfix : ∀ γ ∈ Γ, linOf γ v₀ = v₀)
    (_hell : ∀ γ ∈ Γ, IsElliptic (linOf γ)) :
    ∃ Γ' : Subgroup (isom d), Γ' ≤ Γ ∧ Γ'.relIndex Γ ≠ 0 ∧
      ∃ v : Minkowski d, minkQ v < 0 ∧ ∀ γ ∈ Γ', linOf γ v = v := by
  sorry -- SORRY(bprop:sanloxo, branch): `L(Γ)` lies in the stabiliser of `v₀`, which acts on the horosphere `P̄₀` as `Isom⁺(P̄₀)` (l.2711–2714: `g` elliptic iff `λ(g)` has a fixed point in `P̄₀`); a finite-index subgroup fixing a timelike vector is a finite-index subgroup of `λ(Γ)` with a global fixed point in `P̄₀`. The question is a cocycle one: writing `λ(g) = (r(g), c(g))` (rotation, translation), each `c(g)` lies in `range(r(g) − 1)`, and one needs `c` to be a coboundary on a finite-index subgroup. This holds when `Γ` is finitely generated (bounded orbits) or through the Zariski-closure argument of the proof of 9.1 (l.2596–2597); neither is in the library, and the paper does not raise the branch

/-- An elliptic `γ` which is not nonspacelike elliptic has `Ω_γ = 𝐌ⁿ` ([7.E], l.2045). -/
theorem achronalDomain_eq_univ_of_elliptic_not_nonspacelike {γ : isom d} (hE : IsElliptic (linOf γ))
    (hns : ¬IsNonspacelikeElliptic γ) : achronalDomain γ = univ := by
  obtain ⟨v, hv⟩ := IsElliptic.exists_transConj_fixed γ.2 hE
  set g := isomConj v γ
  have hτ : linOf g (trOf g) = trOf g := by
    show linOf γ _ = _; exact hv
  have hE' : IsElliptic (linOf g) := by rw [linOf_isomConj]; exact hE
  have htr : trOf g = γ • (-v) - (-v) := by
    show transPart (transConj v γ) = _
    rw [transPart, transConj_apply, add_zero, isom_smul_def]; abel
  have hpos : 0 < minkQ (trOf g) := by
    by_contra hle
    push Not at hle
    refine hns ⟨hE, -v, ?_, ?_⟩
    · rw [← htr]; rw [linOf_isomConj] at hτ; exact hτ
    · rw [← htr]; exact hle
  rw [achronalDomain_eq_preimage_isomConj v γ, achronalDomain_elliptic_spacelike hE' hτ hpos,
    preimage_univ]

/-- **[9.E]: `U(Γ) = 𝐌ⁿ`** (l.2606–2610): under the standing hypotheses (`CCAction`), if every
element of `Γ` has elliptic linear part, every `U(γ)` is `𝐌ⁿ` (Lemma 8.6: the elliptic elements
are spacelike). -/
theorem UGamma_eq_univ_of_isElliptic {Γ : Subgroup (isom d)} {St : Set (Minkowski d)}
    (h : CCAction Γ St) (hell : ∀ γ ∈ Γ, IsElliptic (linOf γ)) : UGamma Γ = univ := by
  refine eq_univ_of_forall fun x γ hγ h1 => ?_
  have hns := h.not_isNonspacelikeElliptic hγ h1
  have hlp : ¬IsLinearParabolic γ := fun hp => hp.1.not_isElliptic (hell γ hγ)
  rw [Ug, if_neg hns, if_neg hlp,
    achronalDomain_eq_univ_of_elliptic_not_nonspacelike (hell γ hγ) hns]
  trivial

/-- **[9.E]: `Ω(S̃) = 𝐌ⁿ`, and `Γ` acts freely on `𝐌ⁿ`** (l.2609–2610). -/
theorem omegaS_eq_univ_of_isElliptic {Γ : Subgroup (isom d)} {St : Set (Minkowski d)}
    (h : CCAction Γ St) (hell : ∀ γ ∈ Γ, IsElliptic (linOf γ)) :
    omegaS Γ St = univ ∧ ∀ γ ∈ Γ, γ ≠ 1 → ∀ x : Minkowski d, γ • x ≠ x := by
  have hU := UGamma_eq_univ_of_isElliptic h hell
  refine ⟨?_, fun γ hγ h1 x hx => ?_⟩
  · obtain ⟨x₀, hx₀⟩ := h.nonempty
    refine eq_univ_of_forall fun y => mem_iUnion₂.2 ⟨x₀, hx₀, ?_⟩
    rw [omegaGamma, hU, interior_univ, connectedComponentIn_univ,
      PreconnectedSpace.connectedComponent_eq_univ]
    trivial
  · have := Ug_subset_achronalDomain γ (show x ∈ Ug γ from (hU ▸ mem_univ x : x ∈ UGamma Γ) γ hγ h1)
      1 one_ne_zero
    rw [zpow_one, hx, sub_self, minkQ_zero] at this
    exact lt_irrefl _ this

/-- **Components of a translation-invariant open set are translation-invariant** (G6, the
topological half): if `U(Γ)` is invariant under the translations by a subspace `W`, so are
`Ω(Γ) = int U(Γ)` and each component `Ω(S̃)`. -/
theorem omegaS_add_mem {Γ : Subgroup (isom d)} {St : Set (Minkowski d)}
    {W : Submodule ℝ (Minkowski d)} (hU : ∀ x ∈ UGamma Γ, ∀ w ∈ W, x + w ∈ UGamma Γ) :
    ∀ x ∈ omegaS Γ St, ∀ w ∈ W, x + w ∈ omegaS Γ St := by
  have hΩ : ∀ x ∈ omegaGamma Γ, ∀ w ∈ W, x + w ∈ omegaGamma Γ := by
    intro x hx w hw
    have himg : (Homeomorph.addRight w) '' UGamma Γ ⊆ UGamma Γ := by
      rintro _ ⟨y, hy, rfl⟩; exact hU y hy w hw
    have := interior_mono himg ((Homeomorph.addRight w).image_interior (UGamma Γ) ▸
      mem_image_of_mem _ hx)
    exact this
  intro x hx w hw
  obtain ⟨x₀, hx₀, hxc⟩ := mem_iUnion₂.1 hx
  refine mem_iUnion₂.2 ⟨x₀, hx₀, ?_⟩
  have hseg : segment ℝ x (x + w) ⊆ omegaGamma Γ := by
    rw [segment_eq_image']
    rintro _ ⟨θ, -, rfl⟩
    rw [add_sub_cancel_left]
    exact hΩ x (connectedComponentIn_subset _ _ hxc) _ (W.smul_mem θ hw)
  rw [connectedComponentIn_eq hxc]
  exact (convex_segment x (x + w)).isPreconnected.subset_connectedComponentIn
    (left_mem_segment ℝ x (x + w)) hseg (right_mem_segment ℝ x (x + w))

/-- **G6, the hypothesis of Lemma 5.5 for `Ω(S̃)`, reduced to `U(Γ)`**: if `U(Γ)` is invariant
under the translations by `v₀^⊥` and the timelike subspace `U = range ι` contains the direction
`v₀`, then `Ω(S̃)` is invariant under the translations by `U^⊥` (`IsLTPData.perp_invariant`). -/
theorem perp_invariant_omegaS {d₁ : ℕ} {Γ : Subgroup (isom d)} {St : Set (Minkowski d)}
    {v₀ : Minkowski d} (hU : ∀ x ∈ UGamma Γ, ∀ w ∈ orthSub v₀, x + w ∈ UGamma Γ)
    (ι : AffineMinkEmbedding d₁ d) (hv₀ : ∃ u, ι.lin u = v₀) :
    ∀ w ∈ ι.perp, ∀ p ∈ omegaSOpens Γ St, p + w ∈ omegaSOpens Γ St := by
  obtain ⟨u, rfl⟩ := hv₀
  intro w hw p hp
  exact omegaS_add_mem hU p hp w (by rw [mem_orthSub]; exact hw u)

/-- **The null line `J` of a parabolic element fixing a null `v₀` is `ℝ v₀`**: for every
parabolic decomposition `L(γ) = R U`, `nullPart U = ℝ v₀` (a parabolic fixes no second null
direction, else it would fix a timelike vector and be elliptic). -/
theorem nullPart_eq_span_of_fix {γ : isom d} {R U : Minkowski d ≃ₗ[ℝ] Minkowski d}
    (hpair : IsParabolicPair γ R U) {v₀ : Minkowski d} (hv0 : v₀ ≠ 0) (hv : minkQ v₀ = 0)
    (hfix : linOf γ v₀ = v₀) : nullPart U = ℝ ∙ v₀ := by
  obtain ⟨hR, hU, hRe, hn, hU1, hg, hc⟩ := hpair
  obtain ⟨n, hnJ, hn0⟩ := exists_mem_nullPart_ne_zero hU.1 hn (pOf_ne_zero hU1)
  have hJ := nullPart_eq_span_of_mem hnJ hn0
  have hUn : U n = n := by
    have := pOf_eq_zero_of_mem_nullPart hU.1 hnJ
    rw [pOf_apply] at this; exact sub_eq_zero.1 this
  have hRn : R n = n := parabolic_R_fix_nullPart hR hU hRe hc hnJ
  have hLn : linOf γ n = n := by rw [hg, LinearEquiv.mul_apply, hUn, hRn]
  have hqn : minkQ n = 0 := minkQ_eq_zero_of_mem_nullPart hnJ
  by_cases hB : minkB n v₀ = 0
  · obtain ⟨c, hc'⟩ := eq_smul_of_null_orth hqn hn0 hv hB
    have hc0 : c ≠ 0 := by rintro rfl; rw [zero_smul] at hc'; exact hv0 hc'
    rw [hJ, hc', span_singleton_smul_eq (IsUnit.mk0 c hc0)]
  · exfalso
    have hw : minkQ (n + (-minkB n v₀) • v₀) < 0 := by
      rw [minkQ_add, minkQ_smul, hv, minkB_smul_right, hqn]
      nlinarith [sq_pos_of_ne_zero hB]
    have hLw : linOf γ (n + (-minkB n v₀) • v₀) = n + (-minkB n v₀) • v₀ := by
      rw [map_add, map_smul, hLn, hfix]
    exact (show IsParabolic (linOf γ) from ⟨R, U, hR, hU, hRe, hn, hU1, hg, hc⟩).not_isElliptic
      (isElliptic_of_fixed_timelike (lorentz.minkQ_apply (linOf_mem γ)) hw hLw)

/-- A tangent parabolic `γ` has `Ω_γ = 𝐌ⁿ` ([7.P], l.2122–2138), through the normal form
(the argument of Develop's `isCausalPiece_achronalDomain_tangent`). -/
theorem achronalDomain_tangent_eq_univ {g : isom d} (h : IsTangentParabolic g) :
    achronalDomain g = univ := by
  obtain ⟨R, U, ⟨hR, hU, hRe, hn, hU1, hg, hc⟩, hT⟩ := h
  have hrange := parabolic_range_le_minkOrth_nullPart hR hU hRe hn hU1 hc
  obtain ⟨vₙ, v₁, -, h1, -, -, -, -, hq1, -⟩ := unipotent_frame hU.1 hn (pOf_ne_zero hU1)
  obtain ⟨v, hv, -⟩ := parabolic_exists_transConj_normal hR hU hRe hn hU1 hc hg
    (v₁ := v₁) ⟨vₙ, h1⟩ hq1.ne'
  have hT' : IsTangentCase U (transConj v (g : Minkowski d ≃ᵃ[ℝ] Minkowski d)) := by
    refine ⟨?_, fun h' => hT.2 ((isLinearCase_transConj_iff v _).1 h')⟩
    have hr : LinearMap.range (pOf (linOf g)) ≤ minkOrth (nullPart U) := by
      rw [hg]; exact hrange
    rw [transPart_transConj_mem_iff hr v]; exact hT.1
  rw [achronalDomain_eq_preimage_isomConj v g, achronalDomain_parabolic_tangent hR hU hRe hn hU1 hc
    (g := isomConj v g) (by rw [linOf_isomConj]; exact hg) hv hT', preimage_univ]

/-- **G6 for a parabolic member** (l.2656–2659: "every `U(γ)` is a preimage by `π₁`"): for
`γ ∈ Γ` with parabolic linear part fixing the null `v₀`, `U(γ)` is invariant under the
translations by `v₀^⊥`: in the linear case `U(γ)` is the complement of the hyperplanes
`c + J^⊥ = c + v₀^⊥` (`nullPart_eq_span_of_fix`); otherwise `γ` is tangent (`Ω_γ = 𝐌ⁿ`), the
transverse case being excluded by `nini`. -/
theorem Ug_add_mem_of_isParabolic {Γ : Subgroup (isom d)} {St : Set (Minkowski d)}
    (h : CCAction Γ St) {v₀ : Minkowski d} (hv0 : v₀ ≠ 0) (hv : minkQ v₀ = 0) {γ : isom d}
    (hγ : γ ∈ Γ) (h1 : γ ≠ 1) (hfix : linOf γ v₀ = v₀) (hp : IsParabolic (linOf γ)) :
    ∀ x ∈ Ug γ, ∀ w ∈ orthSub v₀, x + w ∈ Ug γ := by
  have hns : ¬IsNonspacelikeElliptic γ := fun h' => hp.not_isElliptic h'.1
  by_cases hlp : IsLinearParabolic γ
  · rw [Ug, if_neg hns, if_pos hlp]
    intro x hx w hw hxw
    obtain ⟨R, U, hpair, c, hc, hxc⟩ := hxw
    apply hx
    refine ⟨R, U, hpair, c, hc, ?_⟩
    have hJ := nullPart_eq_span_of_fix hpair hv0 hv hfix
    rw [hJ, mem_minkOrth_span_singleton] at hxc ⊢
    have hw' : minkB v₀ w = 0 := by rw [minkB_comm]; exact mem_orthSub.1 hw
    have e : x - c = (x + w - c) - w := by abel
    rw [e, minkB_sub_right, hxc, hw', sub_zero]
  · rw [Ug, if_neg hns, if_neg hlp]
    obtain ⟨R, U, hR, hU, hRe, hn, hU1, hg, hc⟩ := hp
    have hpair : IsParabolicPair γ R U := ⟨hR, hU, hRe, hn, hU1, hg, hc⟩
    rcases linear_or_tangent_or_transverse U (γ : Minkowski d ≃ᵃ[ℝ] Minkowski d) with hL | hT | hT
    · obtain ⟨c, hc'⟩ := (exists_fixed_iff _).2 hL
      exact absurd ⟨⟨R, U, hR, hU, hRe, hn, hU1, hg, hc⟩, c, by rw [isom_smul_def]; exact hc'⟩ hlp
    · rw [achronalDomain_tangent_eq_univ ⟨R, U, hpair, hT⟩]
      intros; trivial
    · exact absurd ⟨R, U, hpair, hT⟩ (nini h hγ h1).2.1

/-- **G6: `U(Γ)` is invariant under `v₀^⊥`** when `L(Γ)` fixes the null `v₀` and `Γ` has no
loxodromic element (elliptic members: `U(γ) = 𝐌ⁿ`; parabolic members:
`Ug_add_mem_of_isParabolic`). -/
theorem UGamma_add_mem {Γ : Subgroup (isom d)} {St : Set (Minkowski d)} (h : CCAction Γ St)
    {v₀ : Minkowski d} (hv0 : v₀ ≠ 0) (hv : minkQ v₀ = 0) (hfix : ∀ γ ∈ Γ, linOf γ v₀ = v₀)
    (hnl : ∀ γ ∈ Γ, ¬IsLoxodromic (linOf γ)) :
    ∀ x ∈ UGamma Γ, ∀ w ∈ orthSub v₀, x + w ∈ UGamma Γ := by
  intro x hx w hw γ hγ h1
  rcases lorentz_trichotomy (linOf_mem γ) with hE | hL | hP
  · have hns := h.not_isNonspacelikeElliptic hγ h1
    have hlp : ¬IsLinearParabolic γ := fun hp => hp.1.not_isElliptic hE
    rw [Ug, if_neg hns, if_neg hlp, achronalDomain_eq_univ_of_elliptic_not_nonspacelike hE hns]
    trivial
  · exact absurd hL (hnl γ hγ)
  · exact Ug_add_mem_of_isParabolic h hv0 hv hγ h1 (hfix γ hγ) hP x (hx γ hγ h1) w hw

/-- The standing hypotheses pass to subgroups (the finite-index passages of §9). -/
theorem CCAction.mono {Γ Γ' : Subgroup (isom d)} {St : Set (Minkowski d)} (h : CCAction Γ St)
    (hle : Γ' ≤ Γ) : CCAction Γ' St where
  cc := h.cc
  inv γ hγ := h.inv γ (hle hγ)
  free γ hγ := h.free γ (hle hγ)
  proper K hK hKc := (h.proper K hK hKc).subset fun _ hγ => ⟨hle hγ.1, hγ.2⟩

/-- **G6** (BARBOT-THEOREMS §6; the hypothesis of Lemma 5.5 for `Ω(S̃)`, asserted at l.2904):
if the linear parts of `Γ` fix a nonzero null `v₀` and `Γ` has no loxodromic element, then
`Ω(S̃)` is invariant under the translations by `U^⊥` for every timelike `U = range ι` whose
direction contains `v₀` — in particular Barbot's `𝒰 = ℝ ⊕ 𝒰̄₀ ⊕ ℝ` (l.2895). -/
theorem perp_invariant_omegaS_of_null {d₁ : ℕ} {Γ : Subgroup (isom d)} {St : Set (Minkowski d)}
    (h : CCAction Γ St) {v₀ : Minkowski d} (hv0 : v₀ ≠ 0) (hv : minkQ v₀ = 0)
    (hfix : ∀ γ ∈ Γ, linOf γ v₀ = v₀) (hnl : ∀ γ ∈ Γ, ¬IsLoxodromic (linOf γ))
    (ι : AffineMinkEmbedding d₁ d) (hv₀ : ∃ u, ι.lin u = v₀) :
    ∀ w ∈ ι.perp, ∀ p ∈ omegaSOpens Γ St, p + w ∈ omegaSOpens Γ St :=
  perp_invariant_omegaS (UGamma_add_mem h hv0 hv hfix hnl) ι hv₀

/-- **A positive power of a non-elliptic element of `SO₀(1, d)` is not elliptic** (loxodromic:
a null eigenvalue `l ≠ 1`, `l > 0` gives `lⁿ ≠ 1`; parabolic: the Jordan pair `A v₁ = v₁ + v₀`
gives `Aⁿ v₁ = v₁ + n v₀`, a nonzero vector of `range ∩ ker` of `Aⁿ − id`). -/
theorem not_isElliptic_linEquiv_pow {A : Minkowski d ≃ₗ[ℝ] Minkowski d} (hA : A ∈ lorentz d)
    (hne : ¬IsElliptic A) {n : ℕ} (hn : n ≠ 0) : ¬IsElliptic (A ^ n) := by
  intro he
  rcases lorentz_trichotomy hA with hE | hX | hP
  · exact hne hE
  · obtain ⟨u, hu0, -, l, hl, hl1, hAu⟩ := hX.exists_eigen
    have hpow : ∀ k : ℕ, (A ^ k) u = l ^ k • u := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, LinearEquiv.mul_apply, hAu, map_smul, ih, smul_smul, pow_succ,
          mul_comm]
    have h1 := he.eigen_sq hu0 (hpow n)
    have hln : l ^ n = 1 := by
      have := pow_pos hl n
      nlinarith
    exact hl1 ((pow_eq_one_iff_of_nonneg hl.le hn).1 hln)
  · obtain ⟨v₁, v₀, hv0, h1, h0⟩ := hP.exists_jordan
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

/-- **A uniform power lands in a finite-index subgroup**: if `Γ'.relIndex Γ ≠ 0`, then
`a ^ (Γ'.relIndex Γ)! ∈ Γ'` for every `a ∈ Γ` (mathlib's
`pow_mem_of_relIndex_ne_zero_of_dvd`). -/
theorem pow_factorial_mem_of_relIndex {Γ Γ' : Subgroup (isom d)} (hidx : Γ'.relIndex Γ ≠ 0)
    {a : isom d} (ha : a ∈ Γ) : a ^ (Γ'.relIndex Γ).factorial ∈ Γ' :=
  (Subgroup.pow_mem_of_relIndex_ne_zero_of_dvd hidx ha fun _ hm hle =>
    Nat.dvd_factorial hm hle).1

/-- **[9.E], the finite-index passage**: if the linear parts of a finite-index `Γ' ≤ Γ` are all
elliptic, so are those of `Γ` (a power of a parabolic or loxodromic element is parabolic or
loxodromic, `isElliptic_linOf_zpow_iff`). -/
theorem isElliptic_of_relIndex {Γ Γ' : Subgroup (isom d)} (hidx : Γ'.relIndex Γ ≠ 0)
    (hell : ∀ γ ∈ Γ', IsElliptic (linOf γ)) : ∀ g ∈ Γ, IsElliptic (linOf g) := by
  intro g hg
  by_contra hne
  have h := hell _ (pow_factorial_mem_of_relIndex hidx hg)
  rw [linOf_pow] at h
  exact not_isElliptic_linEquiv_pow (linOf_mem g) hne (Nat.factorial_pos _).ne' h

/-- **G6, the bridge from `Γ'` to `Γ`** (l.2621–2622 reads "up to finite index"; the invariance
G6 needs all of `Γ`): if a finite-index `Γ' ≤ Γ` has linear parts fixing the nonzero null `v₀`
and contains a parabolic `γ₁`, and `Γ` has no loxodromic element, then **every** linear part of
`Γ` fixes `v₀`. For `g ∈ Γ` and `N = (Γ'.relIndex Γ)!`, `g γ₁ᴺ g⁻¹ ∈ Γ'`, so the parabolic
`L(γ₁ᴺ)` fixes the null vectors `v₀` and `L(g)⁻¹ v₀`; a parabolic fixes a unique null direction
(else it fixes a timelike vector), so `L(g) v₀ = c v₀`, `c > 0`, and `c = 1` since otherwise
`L(g)` is loxodromic (`isLoxodromic_of_null_eigen`). -/
theorem linOf_fix_of_relIndex {Γ Γ' : Subgroup (isom d)} (hle : Γ' ≤ Γ)
    (hidx : Γ'.relIndex Γ ≠ 0) (hnl : ∀ γ ∈ Γ, ¬IsLoxodromic (linOf γ)) {v₀ : Minkowski d}
    (hv0 : v₀ ≠ 0) (hv : minkQ v₀ = 0) (hfix : ∀ γ ∈ Γ', linOf γ v₀ = v₀)
    (hpar : ∃ γ ∈ Γ', IsParabolic (linOf γ)) : ∀ g ∈ Γ, linOf g v₀ = v₀ := by
  obtain ⟨γ₁, hγ₁, hp⟩ := hpar
  set N := (Γ'.relIndex Γ).factorial with hN
  have hpN : ¬IsElliptic (linOf (γ₁ ^ N)) := by
    rw [linOf_pow]
    exact not_isElliptic_linEquiv_pow (linOf_mem γ₁) hp.not_isElliptic (Nat.factorial_pos _).ne'
  have hAv : linOf (γ₁ ^ N) v₀ = v₀ := hfix _ (Γ'.pow_mem hγ₁ N)
  intro g hg
  set w := (linOf g).symm v₀ with hw
  have hgw : linOf g w = v₀ := linOf_symm_apply g v₀
  have hconj : g * γ₁ ^ N * g⁻¹ ∈ Γ' := by
    have := pow_factorial_mem_of_relIndex hidx
      (Γ.mul_mem (Γ.mul_mem hg (hle hγ₁)) (Γ.inv_mem hg))
    rwa [conj_pow] at this
  have hAw : linOf (γ₁ ^ N) w = w := by
    have h1 := hfix _ hconj
    rw [linOf_mul, linOf_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, linOf_inv] at h1
    apply (linOf g).injective
    rw [hgw, ← h1]
    rfl
  have hwq : minkQ w = 0 := by rw [hw, minkQ_linOf_symm, hv]
  have hw0 : w ≠ 0 := fun h0 => hv0 (by rw [← hgw, h0, map_zero])
  -- `w ⊥ v₀`, else `L(γ₁ᴺ)` fixes a timelike vector
  have hB : minkB w v₀ = 0 := by
    by_contra hB
    have ht : minkQ (w + (-minkB w v₀) • v₀) < 0 := by
      rw [minkQ_add, minkQ_smul, hv, minkB_smul_right, hwq]
      nlinarith [sq_pos_of_ne_zero hB]
    have hfx : linOf (γ₁ ^ N) (w + (-minkB w v₀) • v₀) = w + (-minkB w v₀) • v₀ := by
      rw [map_add, map_smul, hAw, hAv]
    exact hpN
      (isElliptic_of_fixed_timelike (lorentz.minkQ_apply (linOf_mem _)) ht hfx)
  obtain ⟨c, hc⟩ := eq_smul_of_null_orth hwq hw0 hv hB
  have hgv : linOf g v₀ = c • v₀ := by
    conv_lhs => rw [hc]
    rw [map_smul, hgw]
  have hcpos := lorentz.eigen_pos_of_null (linOf_mem g) hv0 hv hgv
  by_contra hne
  have hc1 : c ≠ 1 := fun h1 => hne (by rw [hgv, h1, one_smul])
  exact hnl g hg (isLoxodromic_of_null_eigen (linOf_mem g) hv0 hv hcpos hc1 hgv)

/-- **G6 for `Ω(S̃)` of the whole group** (BARBOT-THEOREMS §6, the hypothesis of Lemma 5.5 as
the parabolic output uses it): under `CCAction Γ St`, if a finite-index `Γ' ≤ Γ` fixes the null
`v₀` and contains a parabolic element and `Γ` has no loxodromic element, `Ω(S̃)` of `Γ` is
invariant under `U^⊥` for every timelike `U = range ι` containing the direction `v₀`
(`linOf_fix_of_relIndex`, then `perp_invariant_omegaS_of_null`). -/
theorem perp_invariant_omegaS_of_relIndex {d₁ : ℕ} {Γ Γ' : Subgroup (isom d)}
    {St : Set (Minkowski d)} (h : CCAction Γ St) (hle : Γ' ≤ Γ) (hidx : Γ'.relIndex Γ ≠ 0)
    (hnl : ∀ γ ∈ Γ, ¬IsLoxodromic (linOf γ)) {v₀ : Minkowski d} (hv0 : v₀ ≠ 0)
    (hv : minkQ v₀ = 0) (hfix : ∀ γ ∈ Γ', linOf γ v₀ = v₀)
    (hpar : ∃ γ ∈ Γ', IsParabolic (linOf γ)) (ι : AffineMinkEmbedding d₁ d)
    (hv₀ : ∃ u, ι.lin u = v₀) :
    ∀ w ∈ ι.perp, ∀ p ∈ omegaSOpens Γ St, p + w ∈ omegaSOpens Γ St :=
  perp_invariant_omegaS_of_null h hv0 hv (linOf_fix_of_relIndex hle hidx hnl hv0 hv hfix hpar)
    hnl ι hv₀

/-- **Finding ([9.E] / [3.T]): "translations by spacelike vectors" does not make the span
spacelike.** In `𝐌ⁿ`, `n ≥ 4` (`Minkowski (d + 2)`), the translations by `e = e₁` and
`w = n + √2 e` (`n = e₀ + e₂` null) generate a rank-2 group all of whose nonzero translation
vectors `m e + k w` are spacelike (`√2` irrational), while its span contains the nonzero null
vector `n = w − √2 e`; so it is in no frame a group of horizontal translations
(`IsTranslationSpacetime`'s reading). -/
theorem spacelike_translations_null_span :
    let e : Minkowski (d + 2) := spaceUnit 0
    let w : Minkowski (d + 2) := (timeUnit (d + 2) + spaceUnit 1) + √2 • e
    (∀ m k : ℤ, ¬(m = 0 ∧ k = 0) → 0 < minkQ ((m : ℝ) • e + (k : ℝ) • w)) ∧
      w - √2 • e ≠ 0 ∧ minkQ (w - √2 • e) = 0 := by
  intro e w
  have hn : minkQ (timeUnit (d + 2) + spaceUnit 1) = 0 := by
    rw [minkQ_add, minkQ_timeUnit, minkQ_spaceUnit, minkB_timeUnit_spaceUnit]; ring
  have hen : minkB e (timeUnit (d + 2) + spaceUnit 1) = 0 := by
    rw [minkB_add_right, minkB_comm, minkB_timeUnit_spaceUnit,
      minkB_spaceUnit_spaceUnit (by simp : (0 : Fin (d + 2)) ≠ 1)]; ring
  have hsub : w - √2 • e = timeUnit (d + 2) + spaceUnit 1 := by simp [w]
  refine ⟨fun m k hmk => ?_, ?_, by rw [hsub, hn]⟩
  · have e1 : (m : ℝ) • e + (k : ℝ) • w =
        ((m : ℝ) + k * √2) • e + (k : ℝ) • (timeUnit (d + 2) + spaceUnit 1) := by
      simp only [w, smul_add, add_smul, smul_smul]; abel
    rw [e1, minkQ_add, minkQ_smul, minkQ_smul, minkB_smul_left, minkB_smul_right, hen, hn,
      minkQ_spaceUnit]
    have hne : (m : ℝ) + k * √2 ≠ 0 := by
      intro h0
      by_cases hk : k = 0
      · subst hk; simp at h0; exact hmk ⟨by exact_mod_cast h0, rfl⟩
      · have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
        refine irrational_sqrt_two ⟨(-m / k : ℚ), ?_⟩
        push_cast
        field_simp
        linarith
    have := pow_pos (abs_pos.2 hne) 2
    rw [sq_abs] at this
    simpa using this
  · rw [hsub]
    intro h0
    have := congrArg Prod.fst h0
    simp [timeUnit, spaceUnit] at this

end Spacetime

/-! ## §5 The two outputs, for `Flat/Classification`

`Σ = 𝒟(S̃)`, `S̃ = p⁻¹(S)`, `Γ = ρ(Deck)`, `Ω(S̃) = omegaS Γ Σ` (Develop), and Barbot's
`M(S) = Γ\Ω(S̃)`, read up to the finite-index passage as `B = Γ''\Ω(S̃)`
(`IsQuotientOf B Γ'' Ω(S̃)`). -/

section Main

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Minkowski d) M]
  [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))] {x₀ : M}
  {D : UniversalCover M x₀ → Minkowski d} {ρ : Deck (UniversalCover.proj M x₀) →* isom d}
  {S : Set M}

/-- **[9.E], proved part** (l.2606–2610): if a finite-index `Γ' ≤ Γ = ρ(Deck)` has elliptic
linear parts, then `Ω(S̃) = 𝐌ⁿ` and `Γ` acts freely on `𝐌ⁿ` (`isElliptic_of_relIndex`,
`omegaS_eq_univ_of_isElliptic`, `ccAction_of_developsCC`). -/
theorem omegaS_eq_univ_of_relIndex [T2Space M] (hpair : IsDevelopingPair x₀ D ρ) (h : DevelopsCC x₀ D S)
    {Γ' : Subgroup (isom d)} (hidx : Γ'.relIndex ρ.range ≠ 0)
    (hell : ∀ γ ∈ Γ', IsElliptic (linOf γ)) :
    omegaS ρ.range (D '' (UniversalCover.proj M x₀ ⁻¹' S)) = univ ∧
      ∀ γ ∈ ρ.range, γ ≠ 1 → ∀ x : Minkowski d, γ • x ≠ x :=
  omegaS_eq_univ_of_isElliptic (ccAction_of_developsCC hpair h) (isElliptic_of_relIndex hidx hell)

/-- **G6 for the developing data** (BARBOT-THEOREMS §6, l.2904): in the parabolic case
(`Γ' ≤ Γ = ρ(Deck)` of finite index fixing the null `v₀`, with a parabolic element, `Γ` without
loxodromic element), `Ω(S̃)` is invariant under `U^⊥` for every timelike `U ∋ v₀`. -/
theorem perp_invariant_omegaS_of_developsCC [T2Space M] {d₁ : ℕ} (hpair : IsDevelopingPair x₀ D ρ)
    (h : DevelopsCC x₀ D S) {Γ' : Subgroup (isom d)} (hle : Γ' ≤ ρ.range)
    (hidx : Γ'.relIndex ρ.range ≠ 0) (hnl : ∀ γ ∈ ρ.range, ¬IsLoxodromic (linOf γ))
    {v₀ : Minkowski d} (hv0 : v₀ ≠ 0) (hv : minkQ v₀ = 0) (hfix : ∀ γ ∈ Γ', linOf γ v₀ = v₀)
    (hpar : ∃ γ ∈ Γ', IsParabolic (linOf γ)) (ι : AffineMinkEmbedding d₁ d)
    (hv₀ : ∃ u, ι.lin u = v₀) :
    ∀ w ∈ ι.perp, ∀ p ∈ omegaSOpens ρ.range (D '' (UniversalCover.proj M x₀ ⁻¹' S)),
      p + w ∈ omegaSOpens ρ.range (D '' (UniversalCover.proj M x₀ ⁻¹' S)) :=
  perp_invariant_omegaS_of_relIndex (ccAction_of_developsCC hpair h) hle hidx hnl hv0 hv hfix
    hpar ι hv₀

/-- **[9.E] The elliptic case** (l.2604–2617): if the linear parts of a finite-index subgroup
`Γ' ≤ Γ` fix a timelike vector, then, up to finite index, `M(S) = Γ''\Ω(S̃)` is a linear
twisted product over a translation spacetime (`Ω(S̃) = 𝐌ⁿ`, `omegaS_eq_univ_of_relIndex`). -/
theorem nonloxodromic_elliptic [T2Space M]
    (_hBieb : ∀ k : ℕ, k ≤ d + 1 → BieberbachI (EuclideanSpace ℝ (Fin k)))
    (_hpair : IsDevelopingPair x₀ D ρ) (_h : DevelopsCC x₀ D S) {Γ' : Subgroup (isom d)}
    (_hle : Γ' ≤ ρ.range) (_hidx : Γ'.relIndex ρ.range ≠ 0)
    (_hell : ∃ v : Minkowski d, minkQ v < 0 ∧ ∀ γ ∈ Γ', linOf γ v = v) :
    ∃ Γ'' : Subgroup (isom d), Γ'' ≤ Γ' ∧ Γ''.relIndex Γ' ≠ 0 ∧
      ∃ B : FlatSpacetime.{0} d,
        IsQuotientOf B Γ'' (omegaSOpens ρ.range (D '' (UniversalCover.proj M x₀ ⁻¹' S))) ∧
        ∃ d₁ : ℕ, d₁ ≤ d ∧ ∃ M₁ : FlatSpacetime.{0} d₁, IsTranslationSpacetime M₁ ∧
          IsLTPOver B M₁ := by
  sorry -- SORRY([9.E]): proved here: all of `Γ` is elliptic (`isElliptic_of_relIndex`), `Ω(S̃) = 𝐌ⁿ` and `Γ` free on `𝐌ⁿ` (`omegaS_eq_univ_of_relIndex`). Missing: (1) proper discontinuity of `Γ''` on all of `𝐌ⁿ` (Develop's `holonomy_proper` is stated on `Σ` only; the passage to `𝐌ⁿ` needs Prop 8.10's properness on `Ω(S̃)`) and the bundled quotient `B` (`FlatQuotient.toFlatSpacetime`); (2) transporting `Γ'` to `E ≃ᵃⁱ[ℝ] E` for the euclidean form `⟨x | y⟩ − 2⟨x | v⟩⟨y | v⟩/|v|²` fixed by `L(Γ')` and applying `BieberbachI` there, with `BieberbachMaxConclusion` (maximal `U`) and `mem_direction_of_fixed` (the fixed `v` lies in `U`'s direction, l.2613–2615, so `U` is timelike); (3) the parametrization `ι` of `U` and `RestrictsIn` (orientation of `U`, after an index-2 passage, TwistedProduct's finding) for `suspendre`, `𝐌ⁿ` being trivially `U^⊥`-invariant; (4) `IsTranslationSpacetime` for `Γ''_U\U` needs the span of the translation vectors spacelike: each is spacelike (Lemma 8.6), and a degenerate span (`spacelike_translations_null_span`) must be excluded by (CC′) — an invariant graph `t = x₂ + h`, `h` periodic along a dense line in the null direction's projection, cannot be strictly contracting (SCOPE finding 3)

/-- **[9.P]–[9.A] The parabolic case** (l.2619–3129), in the form of l.3120–3127 and DEC-43 (R1):
if the linear parts of a finite-index `Γ' ≤ Γ` fix a nonzero null vector `v₀`, `Γ'` contains a
parabolic element and `Γ` has no loxodromic element, then, up to finite index (`Γ'' ≤ Γ'`),
there is an open `Γ''`-invariant `Ω` with `𝒟(M̃) ⊆ Ω ⊆ Ω(S̃)` — Barbot's component of `Ω(A)`
containing `S̃`, thickened by `U^⊥` — such that `B = Γ''\Ω` is a linear twisted product over a
**unipotent spacetime**. The conclusion concerns `M` (through `𝒟(M̃) ⊆ Ω`), **not** `M(S)`:
by Rem 9.4 `Ω(S̃)` may be all of `𝐌ⁿ` while `Ω` is a slab (SCOPE, finding 6). -/
theorem nonloxodromic_parabolic [T2Space M]
    (_hBieb : ∀ k : ℕ, k ≤ d + 1 → BieberbachI (EuclideanSpace ℝ (Fin k)))
    (_hpair : IsDevelopingPair x₀ D ρ) (_hcaus : (flatCausality d M).IsCausal)
    (_h : DevelopsCC x₀ D S) {Γ' : Subgroup (isom d)} (_hle : Γ' ≤ ρ.range)
    (_hidx : Γ'.relIndex ρ.range ≠ 0) (_hnl : ∀ γ ∈ ρ.range, ¬IsLoxodromic (linOf γ))
    {v₀ : Minkowski d} (_hv0 : v₀ ≠ 0) (_hv : minkQ v₀ = 0)
    (_hfix : ∀ γ ∈ Γ', linOf γ v₀ = v₀) (_hpar : ∃ γ ∈ Γ', IsParabolic (linOf γ)) :
    ∃ Γ'' : Subgroup (isom d), Γ'' ≤ Γ' ∧ Γ''.relIndex Γ' ≠ 0 ∧
      ∃ Ω : TopologicalSpace.Opens (Minkowski d), range D ⊆ Ω ∧
        (Ω : Set (Minkowski d)) ⊆ omegaS ρ.range (D '' (UniversalCover.proj M x₀ ⁻¹' S)) ∧
        ∃ B : FlatSpacetime.{0} d, IsQuotientOf B Γ'' Ω ∧
          ∃ d₁ : ℕ, d₁ + 1 ≤ d ∧ ∃ M₁ : FlatSpacetime.{0} (d₁ + 1), IsUnipotentSpacetime M₁ ∧
            IsLTPOver B M₁ := by
  sorry -- SORRY([9.P]–[9.A]): proved here, in Barbot's coordinates: (∗∗) and the group laws (`NolParam`), the structure of `Stab(v₀)` (`exists_nolParam`), [9.b] for a purely unipotent parabolic `γ₁` (`b_trivial`, `b_trivial_model`, `b_eq_zero_model`), Prop 9.3 (`bprop_limites`), Prop 9.5 (`bprop_extension`), Rem 9.2 corrected (`choixcoord`), the group `A` and its identification with Examples' `unipAction` (`nolA_mul`, `unipAction_nolToMink`), the assembly `conclusion_model`, all of `Γ` fixing `v₀` (`linOf_fix_of_relIndex`) and G6 for `Ω(S̃)` of `Γ` (`perp_invariant_omegaS_of_developsCC`); `𝒟(M̃) ⊆ Ω(S̃)` is Develop's `bprop_danom`. Missing: (1) a frame `φ ∈ Isom(𝐌ⁿ)` taking `v₀` to `ofNull 1 0 0` (transitivity of `SO₀(1, d)` on null rays) and the conjugation of `Γ'`, `S̃`, `Ω(S̃)` by it; (2) [9.b] for a parabolic `γ₁ = R U` with `R ≠ id` (the leading term on `Fix R`); (3) [9.U]: Bieberbach for `λ(Γ)` on `P̄₀ × {0}` (properness of `α(Γ)`, point (3) l.2660–2663, needs Cor 8.3's homeomorphism), the maximality argument making `𝒰̄_t` independent of `t` (l.2881–2892), and `Γ ≅ ℤᵏ` with `v = T ∘ u` linear (`u(Γ)` a lattice of `E`); (4) the normalisation `ylo = −yhi` by a change of origin in `y` (l.2937–2938), which changes `u` and `T`; (5) the linear form `ℓ` extending the additive `ν = μ + ⟨u|Tu⟩/2` from the lattice (`nu_mul`); (6) `RestrictsIn` for `suspendre` (orientation of `𝒰`, an index-2 passage); (7) `Ω := π_𝒰⁻¹(Ω_A)`, `Ω_A` the component of `Ω(A) ⊆ 𝒰` containing `S̃ ∩ 𝒰` (`mem_omegaA_of_limites`, `IsUnipComponent`): `Ω ⊆ Ω(S̃)` (`Ω(A) ⊆ U(Γ'') = U(Γ)` by `UGamma_eq_of_index`, then G6), `𝒟(M̃) ⊆ π₀⁻¹(π₀ S̃) ⊆ Ω` (l.3123–3125: every null geodesic of `M̃` meets `S̃`, from the proof of Prop 8.12), and the quotients `B = Γ''\Ω`, `M₁ = Γ''_𝒰\Ω_A` (properness on `Ω ⊆ Ω(S̃)`)

/-- **The nonloxodromic case** (§9), assembled: under Benoist's theorem (Prop 9.1, external)
and Bieberbach's (external), if `Γ` has no loxodromic element, a finite-index `Γ'' ≤ Γ` and an
open `Γ''`-invariant `Ω` with `𝒟(M̃) ⊆ Ω ⊆ Ω(S̃)` make `B = Γ''\Ω` either (elliptic case,
`Ω = Ω(S̃)`, so `B` is `M(S)` up to finite index) a linear twisted product over a translation
spacetime, or (parabolic case) a linear twisted product over a unipotent spacetime. -/
theorem nonloxodromic [T2Space M] (hB : BenoistNoLox d)
    (hBieb : ∀ k : ℕ, k ≤ d + 1 → BieberbachI (EuclideanSpace ℝ (Fin k)))
    (hpair : IsDevelopingPair x₀ D ρ) (hcaus : (flatCausality d M).IsCausal)
    (h : DevelopsCC x₀ D S) (hnl : ∀ γ ∈ ρ.range, ¬IsLoxodromic (linOf γ)) :
    ∃ Γ'' : Subgroup (isom d), Γ'' ≤ ρ.range ∧ Γ''.relIndex ρ.range ≠ 0 ∧
      ∃ Ω : TopologicalSpace.Opens (Minkowski d), range D ⊆ Ω ∧
        (Ω : Set (Minkowski d)) ⊆ omegaS ρ.range (D '' (UniversalCover.proj M x₀ ⁻¹' S)) ∧
        ∃ B : FlatSpacetime.{0} d, IsQuotientOf B Γ'' Ω ∧
        ((Ω = omegaSOpens ρ.range (D '' (UniversalCover.proj M x₀ ⁻¹' S)) ∧
            ∃ d₁ : ℕ, d₁ ≤ d ∧ ∃ M₁ : FlatSpacetime.{0} d₁, IsTranslationSpacetime M₁ ∧
              IsLTPOver B M₁) ∨
          ∃ d₁ : ℕ, d₁ + 1 ≤ d ∧ ∃ M₁ : FlatSpacetime.{0} (d₁ + 1), IsUnipotentSpacetime M₁ ∧
            IsLTPOver B M₁) := by
  have hD := (bprop_danom hpair hcaus h).2
  obtain ⟨Γ₁, hle₁, hidx₁, hcase⟩ := bprop_sanloxo hB hnl
  rcases hcase with ⟨v, hv, hfix⟩ | ⟨v₀, hv0, hv, hfix, hpar | hell⟩
  · obtain ⟨Γ₂, hle₂, hidx₂, B, hB', hrest⟩ :=
      nonloxodromic_elliptic hBieb hpair h hle₁ hidx₁ ⟨v, hv, fun γ hγ => (hfix γ hγ).1⟩
    exact ⟨Γ₂, hle₂.trans hle₁, Subgroup.relIndex_ne_zero_trans hidx₂ hidx₁, _, hD, subset_rfl,
      B, hB', Or.inl ⟨rfl, hrest⟩⟩
  · obtain ⟨Γ₂, hle₂, hidx₂, Ω, hDΩ, hΩ, B, hB', hrest⟩ :=
      nonloxodromic_parabolic hBieb hpair hcaus h hle₁ hidx₁ hnl hv0 hv hfix hpar
    exact ⟨Γ₂, hle₂.trans hle₁, Subgroup.relIndex_ne_zero_trans hidx₂ hidx₁, Ω, hDΩ, hΩ, B, hB',
      Or.inr hrest⟩
  · obtain ⟨Γ₂, hle₂, hidx₂, v, hv', hfix'⟩ :=
      exists_timelike_fixed_of_elliptic_of_null hv0 hv hfix hell
    have hidx₂₁ := Subgroup.relIndex_ne_zero_trans hidx₂ hidx₁
    obtain ⟨Γ₃, hle₃, hidx₃, B, hB', hrest⟩ :=
      nonloxodromic_elliptic hBieb hpair h (hle₂.trans hle₁) hidx₂₁ ⟨v, hv', hfix'⟩
    exact ⟨Γ₃, hle₃.trans (hle₂.trans hle₁), Subgroup.relIndex_ne_zero_trans hidx₃ hidx₂₁, _, hD,
      subset_rfl, B, hB', Or.inl ⟨rfl, hrest⟩⟩

end Main

end Causal.Flat
