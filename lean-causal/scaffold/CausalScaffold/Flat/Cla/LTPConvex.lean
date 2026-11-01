import CausalScaffold.Flat.Nonloxodromic
import CausalScaffold.Flat.TitsNull
import CausalScaffold.Flat.Loxodromic
import CausalScaffold.CompactCauchy
import CausalScaffold.CurvesExtend

/-!
# `CausalScaffold.Flat.Cla.LTPConvex` — a linear twisted product over a unipotent spacetime has a convex presentation, and every connected-carrying presentation of it is convex

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257),
`papers/barbot/legacy/labeled/GHFspace.tex`. A plan lemma of Classification (L1): it serves
`Causal.Flat.nonloxodromic_parabolic_convex` (the convexity of the parabolic `Ω`,
`Classification.lean:375`) and `exists_absMax_unipotent_ltp` (convex LTP data,
`Classification.lean:2324`). **No label is marked**: the file certifies no label of the paper by
itself; it proves, without `sorry`, the convexity step those two declarations need.

* `exists_isLTPData_convex_of_unipotent` — **proved, no `sorry`.** (1) If `B` is a linear twisted
  product over a unipotent spacetime `M₁`, it has LTP data `(Γ, Ω, ι)` with `Ω` and `ι⁻¹Ω`
  convex; (2) every presentation `B = Γ\Ω` in which `Ω` contains a nonempty preconnected
  `Γ`-invariant set is convex.
* The tools, proved: `exists_isomImage_of_isQuotientOf` (presentation rigidity, the argument of
  [11.i], l.3586–3599: a convex presentation lifts into any other presentation of the same
  space as an isometry `g`, and `gΩ'` is a "fundamental piece": its `Γ`-translates are equal or
  disjoint and cover `Ω`), `isQuotientOf_stabIn` (a fundamental piece presents the space with its
  stabiliser), `eq_one_of_smul_eq_of_isQuotientOf` (a presentation acts freely), `stabIn`,
  `unipDomain_nonempty` (the slabs `{α < y < β}` are nonempty; their convexity is Examples'
  `convex_unipDomain`).

> In summary, we have proven that $\Gamma$ is precisely as described in the introduction for the
> definition of unipotent spacetimes. Moreover, our choice of $\widehat{T}$ in proposition
> \ref{extension} makes sure that $\widetilde{S}$ is contained in a connected component $\Omega$ of
> $\Omega(A)$ (l.3120–3122)

> It follows that ${\mathcal D}(\widetilde{M})$ is contained in $\Omega$, i.e., that $M$ can be
> embedded in the unipotent spacetime $\Gamma\backslash\Omega$. (l.3125–3127)

> Then, a connected component $\Omega$ of $\Omega(A)$ is the set of $(x,y,z)$ with
> $y_{j} < y < y_{j+1}$ for some index $j$. (l.668–670)

> When $N$ is an euclidean linear space and $r$ takes value in linear isometries (i.e.,
> $r(\Gamma)$ admits a global fixed point in $N$), then we say that $B$ is a \emph{linear twisted
> product over $M$.} (l.1793–1797)

> By construction, every $M_{i}$ is the quotient of some open domain convex $\Omega_{i}$ of \mink
> by the holonomy group $\Gamma_{i}$. The embedding of $M'_{0}$ in $M_{1}$ lifts to a isometric
> embedding $F: \Omega_{0} \rightarrow \Omega_{1}$. As any locally defined isometry between open
> subsets of \mink, $F$ extends to a bijective isometry of the entire Minkowski space
> (l.3592–3598)

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| [9.A]: `Ω` a connected component of `Ω(A)`, a slab (l.668–670, l.3120–3122) | ✓ carried: `IsUnipotentSpacetime`'s presentation is `isomImage φ (unipDomain α β)` with `α < β` (`IsUnipComponent`); its convexity is Examples' `convex_unipDomain` |
| LTP in quotient form (l.1751–1797, l.1834; BARBOT-THEOREMS §1) | ✓ carried: `IsLTPOver B M₁` (TwistedProduct's `IsLTPData`) |
| [11.i]'s lifting + rigidity (l.3586–3599) | ✓ proved here for two presentations of one space (`exists_isomImage_of_isQuotientOf`), with the convex one simply connected (`Convex.contractibleSpace`) |
| part (2): `Ω` "connected" (the paper's `Ω` are components) | ⚠ weakened: only a nonempty preconnected `Γ`-invariant `C ⊆ Ω` is asked (in Classification, `C = 𝒟(M̃)`); `Ω` itself need not be connected a priori, its connectedness follows |

## SCOPE (disclosed)

* **Part (1) may change the data.** The given `Ω` of an LTP may be disconnected (two convex
  pieces exchanged by `Γ`); the data returned are `(Stab_Γ(K), K, ι)` with
  `K = {p | q(p) ∈ gΩ₁}` (`q = ι.retract`, `Ω₁` the slab presentation of `M₁`), a union of
  `U^⊥`-fibres over the convex piece `gΩ₁` of `ι⁻¹Ω`. `ι` is unchanged.
* **Nothing about `B` beyond its presentations is used**; no global hyperbolicity, no
  completeness, no injectivity.
* **Copied, private:** `isLocalIsometry_of_comp_left` is Classification's
  `IsLocalIsometry.of_comp_left_of_continuous` (this file is upstream of Classification); the
  freeness argument follows Classification's `isCancelSMul_of_isCoveringMap`, stated pointwise.
* **Findings.** (1) The convexity of a presentation domain is not an invariant of the
  presented space unless the domain is connected-carrying: `Ω ⊔ γΩ` presents the same space as
  `Ω` with a larger group. Hence part (2)'s hypothesis `C`, and part (1)'s passage to a piece.
  (2) The paper's "As any locally defined isometry … extends" (l.3596–3597) is used for a
  *connected* domain only; here this is `developing_unique_of_preconnected` on the convex `Ω'`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
Classification plan lemma L1 (Cla.LTPConvex).
-/

namespace Causal.Flat.Cla

open Set Function Filter Topology TopologicalSpace

universe u v

variable {d : ℕ}

/-! ### Generic facts on presentations -/

/-- Cancelling a local isometry on the left, for a continuous map (Classification's
`IsLocalIsometry.of_comp_left_of_continuous`, copied: this file is upstream of Classification). -/
private theorem isLocalIsometry_of_comp_left {X M N : Type*} [TopologicalSpace X]
    [ChartedSpace (Minkowski d) X] [TopologicalSpace M] [ChartedSpace (Minkowski d) M]
    [TopologicalSpace N] [ChartedSpace (Minkowski d) N] {f : X → M} {h : M → N}
    (hh : IsLocalIsometry d h) (hfc : Continuous f) (hhf : IsLocalIsometry d (h ∘ f)) :
    IsLocalIsometry d f := by
  obtain ⟨-, hhf'⟩ := isLocalIsometry_iff_eventually.1 hhf
  obtain ⟨-, hh'⟩ := isLocalIsometry_iff_eventually.1 hh
  refine isLocalIsometry_iff_eventually.2 ⟨hfc, fun x => ?_⟩
  obtain ⟨g₁, hg₁⟩ := hhf' x
  obtain ⟨g₂, hg₂⟩ := hh' (f x)
  refine ⟨g₂⁻¹ * g₁, ?_⟩
  filter_upwards [hg₁, hfc.continuousAt.eventually hg₂] with y h1 h2
  simp only [comp_apply] at h1
  rw [mul_smul, ← h1, h2, inv_smul_smul]

/-- Under `Γ`-invariance of `S`, `γ • p ∈ S ↔ p ∈ S` for `γ ∈ Γ`. -/
theorem smul_mem_iff_of_inv {Γ : Subgroup (isom d)} {S : Set (Minkowski d)}
    (hinv : ∀ γ ∈ Γ, (fun p : Minkowski d => γ • p) '' S = S) {γ : isom d} (hγ : γ ∈ Γ)
    (p : Minkowski d) : γ • p ∈ S ↔ p ∈ S := by
  have h := (MulAction.injective γ).mem_set_image (s := S) (a := p)
  rwa [hinv γ hγ] at h

/-- **A presentation acts freely**: if `γ ∈ Γ` fixes a point of `Ω`, then `γ = 1` (the covering
`π` is injective near the point and `π (γ q) = π q`, so `γ` fixes an open set; rigidity). -/
theorem eq_one_of_smul_eq_of_isQuotientOf {X : Type*} [TopologicalSpace X]
    [ChartedSpace (Minkowski d) X] {Γ : Subgroup (isom d)} {Ω : Opens (Minkowski d)}
    (hq : IsQuotientOf X Γ Ω) {γ : isom d} (hγ : γ ∈ Γ) {p : Minkowski d} (hp : p ∈ Ω)
    (hfix : γ • p = p) : γ = 1 := by
  obtain ⟨π, hcov, -, -, hfib⟩ := hq.quot
  obtain ⟨φ, hpφ, hφ⟩ := hcov.isLocalHomeomorph ⟨p, hp⟩
  have hmem : ∀ q : Ω, γ • (q : Minkowski d) ∈ (Ω : Set (Minkowski d)) := fun q =>
    (smul_mem_iff_of_inv hq.inv hγ q).2 q.2
  let s : Ω → Ω := fun q => ⟨γ • (q : Minkowski d), hmem q⟩
  have hsc : Continuous s :=
    ((continuous_const_smul γ).comp continuous_subtype_val).subtype_mk _
  let W : Set Ω := φ.source ∩ s ⁻¹' φ.source
  have hWo : IsOpen W := φ.open_source.inter (φ.open_source.preimage hsc)
  have hps : s ⟨p, hp⟩ = ⟨p, hp⟩ := Subtype.ext hfix
  have hpW : (⟨p, hp⟩ : Ω) ∈ W := ⟨hpφ, by show s ⟨p, hp⟩ ∈ φ.source; rw [hps]; exact hpφ⟩
  have hfixW : ∀ q ∈ W, γ • (q : Minkowski d) = q := by
    rintro q ⟨hq1, hq2⟩
    have hπ : π (s q) = π q := ((hfib q (s q)).2 ⟨γ, hγ, rfl⟩).symm
    rw [hφ] at hπ
    exact congrArg Subtype.val (φ.injOn hq2 hq1 hπ)
  have hVo : IsOpen (Subtype.val '' W : Set (Minkowski d)) := Ω.isOpen.isOpenMap_subtype_val W hWo
  refine Causal.eq_of_eqOn hVo ⟨p, ⟨p, hp⟩, hpW, rfl⟩ ?_
  rintro _ ⟨q, hq, rfl⟩
  simp only [one_smul]
  exact hfixW q hq

/-! ### Presentation rigidity -/

/-- **Presentation rigidity** (the lifting and rigidity argument of [11.i], l.3586–3599, for two
presentations of one space). Let `X = Γ\Ω = Γ'\Ω'` with `Ω'` convex and nonempty. Then for some
`g ∈ Isom(𝐌ⁿ)`, `K := gΩ' ⊆ Ω`, the `Γ`-translates of `K` are equal to `K` or disjoint from it,
and they cover `Ω`.

Proof: `π' : Ω' → X` lifts through the covering `π : Ω → X` (`Ω'` contractible) to a local
isometry `F`, which is `g|Ω'` (rigidity on the connected `Ω'`). If `γ (F x) = F y`, then
`π' x = π' y`, so `γ' x = y` for some `γ' ∈ Γ'`; `γ ∘ F` and `F ∘ γ'` are two lifts of `π'`
agreeing at `x`, hence equal, so `γ g = g γ'` and `γ` preserves `K`. Covering: for `q ∈ Ω`,
`π q = π' x = π (F x)`. -/
theorem exists_isomImage_of_isQuotientOf {X : Type*} [TopologicalSpace X]
    [ChartedSpace (Minkowski d) X] {Γ Γ' : Subgroup (isom d)} {Ω Ω' : Opens (Minkowski d)}
    (hq : IsQuotientOf X Γ Ω) (hq' : IsQuotientOf X Γ' Ω')
    (hcv : Convex ℝ (Ω' : Set (Minkowski d))) (hne : (Ω' : Set (Minkowski d)).Nonempty) :
    ∃ g : isom d, (isomImage g Ω' : Set (Minkowski d)) ⊆ Ω ∧
      (∀ γ ∈ Γ, (∃ p ∈ isomImage g Ω', γ • p ∈ isomImage g Ω') →
        ∀ q, γ • q ∈ isomImage g Ω' ↔ q ∈ isomImage g Ω') ∧
      ∀ q ∈ Ω, ∃ γ ∈ Γ, γ • q ∈ isomImage g Ω' := by
  obtain ⟨π, hcov, hπl, hπs, hfib⟩ := hq.quot
  obtain ⟨π', -, hπ'l, hπ's, hfib'⟩ := hq'.quot
  haveI : Nonempty Ω' := hne.to_subtype
  haveI : ContractibleSpace Ω' := hcv.contractibleSpace hne
  haveI : LocPathConnectedSpace Ω' := locPathConnectedSpace_of_flat d Ω'
  haveI : PreconnectedSpace Ω' := Subtype.preconnectedSpace hcv.isPreconnected
  obtain ⟨a₀⟩ := (inferInstance : Nonempty Ω')
  obtain ⟨e₀, he₀⟩ := hπs (π' a₀)
  obtain ⟨F, ⟨-, hF⟩, -⟩ := hcov.existsUnique_continuousMap_lifts ⟨π', hπ'l.continuous⟩
    a₀ e₀ he₀
  have hFl : IsLocalIsometry d F :=
    isLocalIsometry_of_comp_left hπl F.continuous (by rw [hF]; exact hπ'l)
  have hvl : IsLocalIsometry d (Subtype.val : Ω' → Minkowski d) := isLocalIsometry_subtype_val Ω'
  have hvF : IsLocalIsometry d (Subtype.val ∘ F : Ω' → Minkowski d) :=
    (isLocalIsometry_subtype_val Ω).comp hFl
  obtain ⟨g, hg, -⟩ := developing_unique_of_preconnected (G := isom d) (X := Minkowski d)
    (N := Ω') (D := Subtype.val) (D' := Subtype.val ∘ F)
    (isLocalIsometry_iff_eventually.1 hvl |> fun h' => ⟨h'.1, h'.2⟩)
    (isLocalIsometry_iff_eventually.1 hvF |> fun h' => ⟨h'.1, h'.2⟩)
  have hFg : ∀ z : Ω', ((F z : Ω) : Minkowski d) = g • (z : Minkowski d) := hg
  have hπF : ∀ z, π (F z) = π' z := fun z => congrFun hF z
  refine ⟨g, ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    have h := (F ⟨z, hz⟩).2
    rwa [hFg] at h
  · rintro γ hγ ⟨p, hp, hγp⟩ q
    obtain ⟨x, hx, rfl⟩ := hp
    obtain ⟨y, hy, hyx⟩ := hγp
    have hγF : γ • ((F ⟨x, hx⟩ : Ω) : Minkowski d) = (F ⟨y, hy⟩ : Ω) := by
      rw [hFg, hFg]; exact hyx.symm
    have h1 : π' ⟨x, hx⟩ = π' ⟨y, hy⟩ := by
      rw [← hπF, ← hπF]; exact (hfib _ _).2 ⟨γ, hγ, hγF⟩
    obtain ⟨γ', hγ', hγ'x⟩ := (hfib' _ _).1 h1
    have hmemΩ : ∀ z : Ω', γ • ((F z : Ω) : Minkowski d) ∈ (Ω : Set (Minkowski d)) :=
      fun z => (smul_mem_iff_of_inv hq.inv hγ _).2 (F z).2
    have hmemΩ' : ∀ z : Ω', γ' • (z : Minkowski d) ∈ (Ω' : Set (Minkowski d)) :=
      fun z => (smul_mem_iff_of_inv hq'.inv hγ' _).2 z.2
    let A₁ : Ω' → Ω := fun z => ⟨γ • ((F z : Ω) : Minkowski d), hmemΩ z⟩
    let A₂ : Ω' → Ω := fun z => F ⟨γ' • (z : Minkowski d), hmemΩ' z⟩
    have hA₁ : Continuous A₁ :=
      ((continuous_const_smul γ).comp (continuous_subtype_val.comp F.continuous)).subtype_mk _
    have hA₂ : Continuous A₂ :=
      F.continuous.comp (((continuous_const_smul γ').comp continuous_subtype_val).subtype_mk _)
    have hcomp : π ∘ A₁ = π ∘ A₂ := funext fun z => by
      simp only [comp_apply]
      rw [show π (A₁ z) = π (F z) from ((hfib (F z) (A₁ z)).2 ⟨γ, hγ, rfl⟩).symm, hπF, hπF]
      exact (hfib' z _).2 ⟨γ', hγ', rfl⟩
    have hx' : (⟨γ' • x, hmemΩ' ⟨x, hx⟩⟩ : Ω') = ⟨y, hy⟩ := Subtype.ext hγ'x
    have hA : A₁ = A₂ := hcov.eq_of_comp_eq hA₁ hA₂ hcomp ⟨x, hx⟩
      (Subtype.ext (hγF.trans (congrArg (fun z => ((F z : Ω) : Minkowski d)) hx').symm))
    have hcomm : γ * g = g * γ' := by
      refine Causal.eq_of_eqOn Ω'.isOpen hne fun z hz => ?_
      have h2 : γ • ((F ⟨z, hz⟩ : Ω) : Minkowski d) =
          ((F ⟨γ' • z, hmemΩ' ⟨z, hz⟩⟩ : Ω) : Minkowski d) :=
        congrArg Subtype.val (congrFun hA ⟨z, hz⟩)
      calc (γ * g) • z = γ • ((F ⟨z, hz⟩ : Ω) : Minkowski d) := by rw [mul_smul, hFg]
        _ = ((F ⟨γ' • z, hmemΩ' ⟨z, hz⟩⟩ : Ω) : Minkowski d) := h2
        _ = (g * γ') • z := by rw [hFg, mul_smul]
    have hc' : g⁻¹ * γ = γ' * g⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq, mul_assoc, hcomm, inv_mul_cancel_left]
    rw [mem_isomImage, mem_isomImage, ← mul_smul, hc', mul_smul]
    exact smul_mem_iff_of_inv hq'.inv hγ' _
  · intro q hq
    obtain ⟨x, hx⟩ := hπ's (π ⟨q, hq⟩)
    obtain ⟨γ, hγ, hγq⟩ := (hfib (F x) ⟨q, hq⟩).1 (by rw [hπF, hx])
    refine ⟨γ⁻¹, Γ.inv_mem hγ, ?_⟩
    have hγq' : γ • ((F x : Ω) : Minkowski d) = q := hγq
    rw [← hγq', inv_smul_smul, hFg]
    exact smul_mem_isomImage.2 x.2

/-! ### The stabiliser of a fundamental piece presents the space -/

/-- **The stabiliser in `Γ` of a set `K`**: `{γ ∈ Γ | ∀ q, γ q ∈ K ↔ q ∈ K}`. -/
def stabIn (Γ : Subgroup (isom d)) (K : Set (Minkowski d)) : Subgroup (isom d) where
  carrier := {γ | γ ∈ Γ ∧ ∀ q, γ • q ∈ K ↔ q ∈ K}
  one_mem' := ⟨Γ.one_mem, fun q => by rw [one_smul]⟩
  mul_mem' := by
    rintro γ γ' ⟨hγ, h⟩ ⟨hγ', h'⟩
    exact ⟨Γ.mul_mem hγ hγ', fun q => by rw [mul_smul, h, h']⟩
  inv_mem' := by
    rintro γ ⟨hγ, h⟩
    exact ⟨Γ.inv_mem hγ, fun q => by rw [← h (γ⁻¹ • q), smul_inv_smul]⟩

theorem mem_stabIn {Γ : Subgroup (isom d)} {K : Set (Minkowski d)} {γ : isom d} :
    γ ∈ stabIn Γ K ↔ γ ∈ Γ ∧ ∀ q, γ • q ∈ K ↔ q ∈ K := Iff.rfl

/-- **A fundamental piece presents the space with its stabiliser** ((Comp)). If `X = Γ\Ω` and
`K ⊆ Ω` is open, with `Γ`-translates equal to `K` or disjoint from it and covering `Ω`, then
`X = Stab_Γ(K)\K`. The covering property is mathlib's `IsQuotientCoveringMap` criterion: the
action of the stabiliser on `K` is free (`eq_one_of_smul_eq_of_isQuotientOf`) and every point
has a neighbourhood on which `π` is injective. -/
theorem isQuotientOf_stabIn {X : Type*} [TopologicalSpace X] [ChartedSpace (Minkowski d) X]
    {Γ : Subgroup (isom d)} {Ω K : Opens (Minkowski d)} (hq : IsQuotientOf X Γ Ω)
    (hKΩ : (K : Set (Minkowski d)) ⊆ Ω)
    (hstab : ∀ γ ∈ Γ, (∃ p ∈ K, γ • p ∈ K) → ∀ q, γ • q ∈ K ↔ q ∈ K)
    (hcover : ∀ q ∈ Ω, ∃ γ ∈ Γ, γ • q ∈ K) : IsQuotientOf X (stabIn Γ K) K := by
  obtain ⟨π, hcov, hπl, hπs, hfib⟩ := hq.quot
  have hinv : ∀ γ ∈ stabIn Γ K,
      (fun p : Minkowski d => γ • p) '' (K : Set (Minkowski d)) = K := by
    intro γ hγ
    obtain ⟨-, h⟩ := mem_stabIn.1 hγ
    ext x
    refine ⟨?_, fun hx => ⟨γ⁻¹ • x, (h _).1 (by rwa [smul_inv_smul]), smul_inv_smul γ x⟩⟩
    rintro ⟨p, hp, rfl⟩
    exact (h p).2 hp
  haveI : FlatQuotient.Invariant (stabIn Γ K) K := (FlatQuotient.invariant_iff _ _).2 hinv
  let j : K → Ω := Set.inclusion hKΩ
  have hjc : Continuous j := continuous_inclusion hKΩ
  have hjl : IsLocalIsometry d j :=
    isLocalIsometry_of_comp_left (isLocalIsometry_subtype_val Ω) hjc
      (isLocalIsometry_subtype_val K)
  let πK : K → X := π ∘ j
  have hπKl : IsLocalIsometry d πK := hπl.comp hjl
  have hfibK : ∀ p q : K, πK p = πK q ↔ ∃ γ ∈ stabIn Γ K, γ • (p : Minkowski d) = q := by
    intro p q
    constructor
    · intro h
      obtain ⟨γ, hγ, hγp⟩ := (hfib (j p) (j q)).1 h
      have hγp' : γ • (p : Minkowski d) = q := hγp
      exact ⟨γ, ⟨hγ, hstab γ hγ ⟨p, p.2, by rw [hγp']; exact q.2⟩⟩, hγp'⟩
    · rintro ⟨γ, hγ, hγp⟩
      exact (hfib (j p) (j q)).2 ⟨γ, (mem_stabIn.1 hγ).1, hγp⟩
  have hπKs : Surjective πK := by
    intro x
    obtain ⟨q, rfl⟩ := hπs x
    obtain ⟨γ, hγ, hγq⟩ := hcover q q.2
    exact ⟨⟨γ • (q : Minkowski d), hγq⟩, ((hfib q _).2 ⟨γ, hγ, rfl⟩).symm⟩
  refine ⟨hinv, πK, ?_, hπKl, hπKs, hfibK⟩
  have hQ : IsQuotientCoveringMap πK (stabIn Γ K) := by
    refine (isQuotientCoveringMap_iff _ _).2 ⟨?_, inferInstance, ?_, ?_⟩
    · exact IsOpenQuotientMap.isQuotientMap
        { surjective := hπKs, continuous := hπKl.continuous, isOpenMap := hπKl.isOpenMap }
    · intro e₁ e₂
      rw [MulAction.mem_orbit_iff]
      constructor
      · intro h
        obtain ⟨γ, hγ, h'⟩ := (hfibK e₂ e₁).1 h.symm
        exact ⟨⟨γ, hγ⟩, Subtype.ext h'⟩
      · rintro ⟨γ, h⟩
        exact ((hfibK e₂ e₁).2 ⟨γ, γ.2, congrArg Subtype.val h⟩).symm
    · intro e
      obtain ⟨φ, hφe, hφ⟩ := hcov.isLocalHomeomorph (j e)
      refine ⟨j ⁻¹' φ.source, (φ.open_source.preimage hjc).mem_nhds hφe, ?_⟩
      rintro γ ⟨_, ⟨u, hu, rfl⟩, hγu⟩
      have hγΓ : (γ : isom d) ∈ Γ := (mem_stabIn.1 γ.2).1
      have hπ : π (j (γ • u)) = π (j u) :=
        ((hfib (j u) (j (γ • u))).2 ⟨γ, hγΓ, rfl⟩).symm
      rw [hφ] at hπ
      have hfix : (γ : isom d) • (u : Minkowski d) = u :=
        congrArg Subtype.val (φ.injOn hγu hu hπ)
      exact Subtype.ext (eq_one_of_smul_eq_of_isQuotientOf hq hγΓ (hKΩ u.2) hfix)
  exact hQ.isCoveringMap

/-! ### The slabs `{α < y < β}` are nonempty -/

/-- The slab `{α < y < β}` is nonempty when `α < β` (its convexity is Examples'
`convex_unipDomain`, l.668–670). -/
theorem unipDomain_nonempty {k : ℕ} {α β : EReal} (h : α < β) :
    (unipDomain (d := k) α β : Set (Minkowski (k + 1))).Nonempty := by
  obtain ⟨y, hαy, hyβ⟩ := EReal.lt_iff_exists_real_btwn.1 h
  refine ⟨ofNull 0 y 0, ?_⟩
  show α < (nullY (ofNull 0 y (0 : EuclideanSpace ℝ (Fin k))) : EReal) ∧
    (nullY (ofNull 0 y (0 : EuclideanSpace ℝ (Fin k))) : EReal) < β
  rw [nullY_ofNull]
  exact ⟨hαy, hyβ⟩

/-! ### Part 1: convex LTP data -/

private theorem retract_add_perp {d₁ : ℕ} (ι : AffineMinkEmbedding d₁ d) (p : Minkowski d)
    {w : Minkowski d} (hw : w ∈ ι.perp) : ι.retract (p + w) = ι.retract p := by
  unfold AffineMinkEmbedding.retract
  rw [show p + w - ι 0 = (p - ι 0) + w by abel, map_add, ι.coproj_eq_zero_of_mem_perp hw,
    add_zero]

private theorem retract_combo {d₁ : ℕ} (ι : AffineMinkEmbedding d₁ d) (p q : Minkowski d)
    {a b : ℝ} (hab : a + b = 1) :
    ι.retract (a • p + b • q) = a • ι.retract p + b • ι.retract q := by
  unfold AffineMinkEmbedding.retract
  rw [← map_smul, ← map_smul, ← map_add]
  congr 1
  have hb : b = 1 - a := by linarith
  subst hb
  module

/-- **Part (1)**: an LTP over a unipotent spacetime has convex LTP data. -/
theorem exists_isLTPData_convex_of_unipotent_aux {e : ℕ} {B : FlatSpacetime.{u} d}
    {M₁ : FlatSpacetime.{v} (e + 1)} (hU : IsUnipotentSpacetime M₁) (hB : IsLTPOver B M₁) :
    ∃ (Γ : Subgroup (isom d)) (Ω : Opens (Minkowski d)) (ι : AffineMinkEmbedding (e + 1) d),
      IsLTPData B M₁ Γ Ω ι ∧ Convex ℝ (Ω : Set (Minkowski d)) ∧
        Convex ℝ (ι.preimageOpens Ω : Set (Minkowski (e + 1))) := by
  obtain ⟨Γ, Ω, ι, hD⟩ := hB
  obtain ⟨φ, ℓ, α, β, L, Γ₀, -, hcomp, -, -, hq₁⟩ := hU
  have hcv₁ : Convex ℝ (isomImage φ (unipDomain α β) : Set (Minkowski (e + 1))) :=
    convex_isomImage (convex_unipDomain (α := α) (β := β))
  have hne₁ : (isomImage φ (unipDomain α β) : Set (Minkowski (e + 1))).Nonempty := by
    obtain ⟨p, hp⟩ := unipDomain_nonempty (k := e) hcomp.1
    exact ⟨φ • p, smul_mem_isomImage.2 hp⟩
  obtain ⟨g, hsub, hstab, hcover⟩ :=
    exists_isomImage_of_isQuotientOf hD.quotient_base hq₁ hcv₁ hne₁
  set K₁ := isomImage g (isomImage φ (unipDomain α β)) with hK₁def
  have hK₁cv : Convex ℝ (K₁ : Set (Minkowski (e + 1))) := convex_isomImage hcv₁
  let K : Opens (Minkowski d) :=
    ⟨{p | ι.retract p ∈ K₁}, K₁.isOpen.preimage ι.continuous_retract⟩
  have hmemK : ∀ p, p ∈ K ↔ ι.retract p ∈ K₁ := fun _ => Iff.rfl
  have hιK : ∀ x, ι x ∈ K ↔ x ∈ K₁ := fun x => by rw [hmemK, ι.retract_apply]
  have hpre : ι.preimageOpens K = K₁ := SetLike.ext fun x => hιK x
  have hKΩ : (K : Set (Minkowski d)) ⊆ Ω := fun p hp =>
    (ι.mem_iff_retract_mem hD.perp_invariant).2 (hsub hp)
  have hkey : ∀ {γ : isom d} {g' : isom (e + 1)}, ι.Restricts γ g' →
      ∀ q, γ • q ∈ K ↔ g' • ι.retract q ∈ K₁ := fun hr q => by
    rw [hmemK, hr.retract_smul]
  have hstabU : ∀ γ ∈ Γ, (∃ p ∈ K, γ • p ∈ K) → ∀ q, γ • q ∈ K ↔ q ∈ K := by
    rintro γ hγ ⟨p, hp, hγp⟩ q
    obtain ⟨g', hg'⟩ := hD.restricts γ hγ
    have h := hstab g' ⟨γ, hγ, hg'⟩ ⟨ι.retract p, hp, (hkey hg' p).1 hγp⟩
    rw [hkey hg', h, hmemK]
  have hcoverU : ∀ q ∈ Ω, ∃ γ ∈ Γ, γ • q ∈ K := by
    intro q hq
    obtain ⟨g', ⟨γ, hγ, hr⟩, hg'q⟩ :=
      hcover _ ((ι.mem_iff_retract_mem hD.perp_invariant).1 hq)
    exact ⟨γ, hγ, (hkey hr q).2 hg'q⟩
  have hQ : IsQuotientOf B (stabIn Γ K) K := isQuotientOf_stabIn hD.quotient hKΩ hstabU hcoverU
  have hQ₁ : IsQuotientOf M₁ (stabIn (ι.restrictGroup Γ) K₁) K₁ :=
    isQuotientOf_stabIn hD.quotient_base hsub hstab hcover
  have hgrp : ι.restrictGroup (stabIn Γ K) = stabIn (ι.restrictGroup Γ) K₁ := by
    ext g'
    constructor
    · rintro ⟨γ, hγ, hr⟩
      obtain ⟨hγΓ, hγK⟩ := mem_stabIn.1 hγ
      refine mem_stabIn.2 ⟨⟨γ, hγΓ, hr⟩, fun x => ?_⟩
      exact (hιK (g' • x)).symm.trans ((by rw [hr x] : ι (g' • x) ∈ K ↔ γ • ι x ∈ K).trans
        ((hγK (ι x)).trans (hιK x)))
    · intro hg'
      obtain ⟨⟨γ, hγ, hr⟩, hst⟩ := mem_stabIn.1 hg'
      refine ⟨γ, mem_stabIn.2 ⟨hγ, fun q => ?_⟩, hr⟩
      exact (hkey hr q).trans ((hst _).trans (hmemK q).symm)
  have hKcv : Convex ℝ (K : Set (Minkowski d)) := by
    intro p hp q hq a b ha hb hab
    show ι.retract (a • p + b • q) ∈ K₁
    rw [retract_combo ι p q hab]
    exact hK₁cv hp hq ha hb hab
  refine ⟨stabIn Γ K, K, ι, ⟨hD.timelike, hD.orthochronous,
    fun γ hγ => hD.preserves γ (mem_stabIn.1 hγ).1,
    fun γ hγ => hD.restricts γ (mem_stabIn.1 hγ).1,
    fun w hw p hp => by
      show ι.retract (p + w) ∈ K₁
      rw [retract_add_perp ι p hw]; exact hp,
    hQ, by rw [hgrp, hpre]; exact hQ₁⟩, hKcv, by rw [hpre]; exact hK₁cv⟩

/-! ### The statement -/

/-- **Convexity of the presentations of an LTP over a unipotent spacetime.** (1) `B` has LTP data
over `M₁` with `Ω` and `ι⁻¹Ω` convex. (2) Every presentation `B = Γ\Ω` in which `Ω` contains a
nonempty preconnected `Γ`-invariant set `C` has `Ω` convex: by presentation rigidity
(`exists_isomImage_of_isQuotientOf`) against the convex presentation of (1), `Ω` contains a convex
piece `gΩ'` whose translates are equal or disjoint and cover `Ω`; `C` lies in one translate
(preconnected), which is then `Γ`-invariant, so it is all of `Ω`. -/
theorem exists_isLTPData_convex_of_unipotent {e : ℕ} {B : FlatSpacetime.{u} d}
    {M₁ : FlatSpacetime.{v} (e + 1)} (hU : IsUnipotentSpacetime M₁) (hB : IsLTPOver B M₁) :
    (∃ (Γ : Subgroup (isom d)) (Ω : Opens (Minkowski d)) (ι : AffineMinkEmbedding (e + 1) d),
        IsLTPData B M₁ Γ Ω ι ∧ Convex ℝ (Ω : Set (Minkowski d)) ∧
          Convex ℝ (ι.preimageOpens Ω : Set (Minkowski (e + 1)))) ∧
      ∀ (Γ : Subgroup (isom d)) (Ω : Opens (Minkowski d)), IsQuotientOf B Γ Ω →
        ∀ C ⊆ (Ω : Set (Minkowski d)), IsPreconnected C → C.Nonempty →
          (∀ γ ∈ Γ, ∀ p ∈ C, γ • p ∈ C) → Convex ℝ (Ω : Set (Minkowski d)) := by
  have h1 := exists_isLTPData_convex_of_unipotent_aux hU hB
  refine ⟨h1, fun Γ Ω hq C hCΩ hCp hCne hCinv => ?_⟩
  obtain ⟨Γ', Ω', ι', hD', hcv', -⟩ := h1
  have hne' : (Ω' : Set (Minkowski d)).Nonempty := by
    obtain ⟨π, -, -, hπs, -⟩ := hD'.quotient.quot
    obtain ⟨b⟩ : Nonempty B := inferInstance
    obtain ⟨p, -⟩ := hπs b
    exact ⟨p, p.2⟩
  obtain ⟨g, hsub, hstab, hcover⟩ := exists_isomImage_of_isQuotientOf hq hD'.quotient hcv' hne'
  set K := isomImage g Ω' with hKdef
  obtain ⟨c₀, hc₀⟩ := hCne
  obtain ⟨γ₀, hγ₀, hγ₀c⟩ := hcover c₀ (hCΩ hc₀)
  set V : Set (Minkowski d) :=
    ⋃ γ ∈ {γ : isom d | γ ∈ Γ ∧ ∀ p ∈ K, γ • p ∉ K}, (fun q => γ • q) ⁻¹' (K : Set _)
    with hVdef
  have hVo : IsOpen V :=
    isOpen_biUnion fun γ _ => K.isOpen.preimage (continuous_const_smul γ)
  have hdisj : Disjoint (K : Set (Minkowski d)) V := by
    rw [Set.disjoint_left]
    intro q hqK hqV
    obtain ⟨γ, ⟨-, hγ⟩, hγq⟩ := Set.mem_iUnion₂.1 hqV
    exact hγ q hqK hγq
  have hCKV : C ⊆ (K : Set (Minkowski d)) ∪ V := by
    intro q hq
    obtain ⟨γ, hγ, hγq⟩ := hcover q (hCΩ hq)
    by_cases h : ∀ p ∈ K, γ • p ∉ K
    · exact Or.inr (Set.mem_iUnion₂.2 ⟨γ, ⟨hγ, h⟩, hγq⟩)
    · push Not at h
      exact Or.inl ((hstab γ hγ h q).1 hγq)
  have hCK : C ⊆ (K : Set (Minkowski d)) :=
    hCp.subset_left_of_subset_union K.isOpen hVo hdisj hCKV
      ⟨γ₀ • c₀, hCinv γ₀ hγ₀ c₀ hc₀, hγ₀c⟩
  have hΩK : (Ω : Set (Minkowski d)) = K := by
    refine Subset.antisymm (fun q hq => ?_) hsub
    obtain ⟨γ, hγ, hγq⟩ := hcover q hq
    exact (hstab γ hγ ⟨c₀, hCK hc₀, hCK (hCinv γ hγ c₀ hc₀)⟩ q).1 hγq
  rw [hΩK]
  exact convex_isomImage hcv'

end Causal.Flat.Cla
