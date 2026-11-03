import GXScaffold.BTZ.AbsMax
import GX.BTZ.Manifolds
import Causal.Flat.Lox.PastProper

/-!
# `GXScaffold.BTZ.Uniformization` — uniformization of GH Cauchy-compact Cauchy-maximal `𝔼₀`-manifolds

Packages WP-41n and WP-43f (WAVE5-PLAN.md, WP-39n). `papers/gx`, §4.6 (`RamcovGX.tex:2348–2396`), DEC-28's
Cauchy-compact form (`brunswic2021cauchy` Prop 2.17 / Cor 2.18), DEC-75/76/77.
**No ledger label is certified in full here, so nothing is marked.** Two rows, both partial:

* `theo:globally_hyperbolic_cauchy_complete_cauchy_maximal` — `RamcovGX.tex:2363`, partial
  (DEC-27/28): `GX.btz_uniformization` — for `M` GH, Cauchy-compact, Cauchy-maximal, with a BTZ
  point (`s ≥ 1`) and `π₁(Reg M)` not metabelian, and **every** developing pair `(𝒟, ρ)` of
  `Reg M`: `𝒟` injective on `Reg M̃`; `ρ` faithful, discrete, torsion-free; a loxodromic in
  `ρ(Γ)` (DEC-75); the `Γ`-invariant family of lightlike planes `(Π_w)_{w ∈ Λ(Γ)}`;
  `𝒟(Reg M̃) = ⋂_w I⁺(Π_w)` (an equality, future case, DEC-77 (a)); `Γ` free and properly
  discontinuous; `Reg M̃` future complete; `𝒟` induces an isometry `Reg M ≅ ρ(Γ)\Ω⁺`. The future
  case is PROVED (WP-43f, 0 `sorry` in this file): `GX.e0RegM_range_not_subset_omegaMinus`, from
  `GX.false_of_sing_of_pastComplete` (a BTZ point forbids an injective past-complete developed
  `Reg M̃`; standard axioms only). The (O2) hypothesis `hLine` of WP-41n is discharged
  (`GX.E0AbsMax.cor_abs_max_e0`). The `sorry`s left beneath the row are upstream only (SCOPE (d)). The BTZ
  half (`𝒟` on `sing M̃`, the rays `Δ_i`, `T_BTZ` near them) is not formalized (SCOPE (b)), except
  the injectivity step `GX.BTZTildeData.injective_D_of_isBTZFutureComplete` (l.2392–2394).
* `prop:globally_hyperbolic_cauchy_complete_manifolds` — `RamcovGX.tex:2348`, partial, corrected
  (DEC-77): `GX.btz_reg_isFutureComplete` — GH + Cauchy-compact + Cauchy-maximal + `π₁(Reg M)` not
  metabelian + a BTZ point ⇒ the **regular part** is future complete (the proof's first step,
  l.2350); the BTZ rays (B21 Lemma 2.3) are not. The counterexample to the printed statement
  (D-11) is built, 0 `sorry`: `GX.e0PastHalf_counterexample` — `{τ<0} ⊂ 𝔼₀` is a GH
  `𝔼₀`-manifold with BTZ points, and for every developing pair of `Reg {τ<0}` and every `z`,
  `𝒟(I⁺(z)) ≠ I⁺(𝒟 z)` (`GX.e0PastHalf_not_isFutureComplete`); its Cauchy-completeness (DEC-31)
  is not stated, the scaffold having no DEC-31 predicate for `𝔼₀`-manifolds (SCOPE (c)).

Proved here, of general use (0 `sorry`, standard axioms only):

* `GX.uniformization_range_eq_of_absMax`, `GX.uniformization_of_absMax`: Barbot's equality
  `𝒟(M̃) = Ω^±(Λ(Γ))` for any absolutely maximal flat spacetime with (CC′) and a loxodromic, with
  the quotient `M ≅ ρ(Γ)\Ω^±` (`GX.exists_isometry_quotient_of_absMax`, `GX.uniformization_quotient_aux`).
* `GX.isFutureComplete_of_range_eq_omegaPlus`: `𝒟` injective onto `Ω⁺(Λ)` ⇒ `M̃` future complete.
* `GX.injective_of_isFutureComplete`: the injectivity step of l.2392–2394, for any causality.
* `GX.exists_affine_eq_of_locally`: a function locally affine through an open map is globally
  affine on a preconnected space; `GX.pastHalf_rad_locally`: `r` is affine in `𝒟` near every point.
* `GX.false_of_sing_of_pastComplete` (WP-43f): an `𝔼₀`-manifold with a BTZ point has no developing
  map of `Reg M̃` that is injective with a past-complete image — the radial segment into the BTZ
  point lifts into one component of the lifted sector, where `𝒟 = g • chartMap`
  (`GX.dev_eventually_chartMap_sector`, `GX.exists_isom_eq_of_locally`), so its development
  converges to a point of `J⁻(𝒟 z̃)`; past completeness and the open embedding `𝒟` would make the
  BTZ point regular.

> \begin{prop} Globally hyperbolic Cauchy-complete $\BTZ$-manifolds are future complete.
> \end{prop} \begin{proof} From Theorem 3 of \cite{brunswic2021cauchy} the regular par of $M$ is
> globally hyperbolic and Cauchy-complete. Barbot uniformization Theorem \cite{barbot_globally_2004}
> then implies future completeness of the regular part. Finally Lemma 2.4 of
> \cite{brunswic2021cauchy} implies that the singular locus contains full future BTZ rays.
> \end{proof} (l.2348–2353)

> \begin{thm} Let $M$ be a globally hyperbolic Cauchy-complete Cauchy-maximal $\mass{0}$-manifold,
> let $\widetilde M$ its maximal covering branched over $\sing(M)$, of developing map and holonomy
> $(\D,\rho)$. […] Then, up to time reversal of $M$: $\D$ is injective; $\rho$ is faithful,
> discrete and torsion-free; there exists a $\Gamma$-invariant family of relatively open future
> complete lightlike rays $(\Delta_i)_{i\in I}$ and a $\Gamma$-invariant family of lightlike planes
> $(\Pi_j)_{j\in J}$ such that $\D(\widetilde M) = \bigcap_{i\in I} J^+(\Delta_i) \cup
> \bigcap_{j\in I} I^+(\Pi_j)$; endowing $\D(\widetilde M)$ with the BTZ topology in the
> neighborhood of the lightlike rays $(\Delta_i)_{i\in I}$, the developing map induces an
> isomorphism $M\xrightarrow{~~\overline \D~~} \rho\backslash\D(\widetilde M)$. \end{thm}
> (l.2363–2376)

## Hypothesis checklist

| paper / ruling | here |
|---|---|
| `M` globally hyperbolic (l.2363) | ✓ carried: `(CE M).GloballyHyperbolic` (ETT's, the charted causality) |
| Cauchy-complete (l.2363) | ⚠ strengthened: **Cauchy-compact** `E0CauchyCompact M` (DEC-28; Barbot's equality needs absolute maximality, which B21 gives only via Cor 2.18) |
| Cauchy-maximal (l.2363) | ✓ carried: `IsE0CauchyMaximal M` (DEC-77 (c), `Dev.IsETTMaximal` among `𝔼₀`-manifolds) |
| finite type, `π₁(Σ∖sing)` non-abelian, `s ≥ 1` (DEC-76) | ⚠ strengthened: `π₁(Reg M)` **not metabelian** (Holonomy's finding: non-abelian is refuted algebraically); `s ≥ 1` ✓ as `(chartedSing e0SingY M 0).Nonempty` |
| "up to time reversal" (dropped, DEC-77 (a)) | ✓ the future case is concluded and PROVED (`e0RegM_range_not_subset_omegaMinus`, WP-43f) |
| `M` second countable | ⚠ carried, as in `GXScaffold.BTZ.AbsMax` (Cor 2.18's form; implicit in "manifold"); (O2) `hLine` is no longer a hypothesis (`E0AbsMax.e0_hLine`) |
| the given pair `(𝒟, ρ)` (l.2365) | ✓ every developing pair of `Reg M` is a hypothesis, not an `∃` |
| `𝒟` injective | ⚠ on `Reg M̃` ✓; on `M̃`: the step l.2392–2394 proved, its inputs carried |
| `ρ` faithful, discrete, torsion-free | ✓ |
| `D(M̃) = (⋃Δᵢ) ∪ ⋂ I⁺(Πⱼ)` (DEC-28's display) | ⚠ the regular half `𝒟(Reg M̃) = ⋂ I⁺(Π_w)` ✓ (equality); the rays `Δ_i` ✗ |
| `M ≅ ρ\D(M̃)`, BTZ topology | ⚠ `Reg M ≅ ρ(Γ)\Ω⁺` ✓ (isometry, `𝒟`-induced); at the BTZ points ✗ |

## SCOPE (disclosed)

* (a) **The future-case selection** (DEC-77 (a)) is PROVED (WP-43f), by a route that needs neither
  `𝒟` extended to the BTZ points nor the parabolic holonomy of the loop around a line: in the past
  case `𝒟(Reg M̃) = Ω⁻(Λ)` is past complete, and `GX.false_of_sing_of_pastComplete` refutes that.
  The future case `Ω⁺ ⊆ Ω⁻` is excluded by `Ω⁺ ∩ Ω⁻ = ∅` (`Λ ≠ ∅`, the loxodromic).
* (b) **The BTZ half of the headline is not formalized**: `𝒟` on `sing M̃`, the rays
  `Δ_i = 𝒟(S_x)` in `∂Ω`, the image `(⋃Δ_i) ∪ Ω`, and `M ≅ ρ\𝒟(M̃)` for the BTZ topology. They live
  on the maximal branched covering `BTZTildeData` (GX.BTZ.Manifolds), built over the
  `SingularGXStructure` presentation of `M`, while Cauchy-compactness, Cauchy-maximality and
  absolute maximality of `Reg M` are stated for `ChartedSpace E0Y M` (GXScaffold.BTZ.AbsMax). No
  bridge identifies the two presentations, nor `reg M̃` with the universal cover of `Reg M`. The
  injectivity step is proved abstractly and on `BTZTildeData`, with its inputs as hypotheses.
* (c) `prop:globally_hyperbolic_cauchy_complete_manifolds`: the regular part only; "full future
  BTZ rays" (B21 Lemma 2.3, the paper's "Lemma 2.4") and future completeness at BTZ points are
  not formalized. The counterexample `{τ<0} ⊂ 𝔼₀` (D-11, §4b) is proved GH
  (`GX.e0PastHalf_globallyHyperbolic`), with BTZ points (`GX.e0PastHalf_sing_nonempty`), and not
  future complete on its regular part for every developing pair
  (`GX.e0PastHalf_not_isFutureComplete`): `r = t − x` read through `𝒟` is globally affine, strictly
  increasing along `I⁺` and bounded by `r(z) − 2τ(z)` there since `τ < 0`, while an affine
  function is unbounded on a timelike ray. Its Cauchy-completeness (the printed hypothesis, the
  plane `{τ = −1}` with `dr² + r²dθ²`) is **not stated**: the scaffold has no DEC-31 predicate for
  `𝔼₀`-manifolds (the induced length structure across the BTZ lines is Surgery's obstruction
  (3)), and `Causal.Flat.IsCauchyComplete` of `Reg {τ<0}` is not the paper's hypothesis (we expect
  it to fail: no cusp surgery is available below `τ = 0`).
* (d) Upstream `sorry`s inherited (`#print axioms`, `campaign/WP-43f/axioms.out`), all through
  `GX.E0AbsMax.cor_abs_max_e0` (B21 Cor 2.18): the three open leaves of `GXScaffold.BTZ.AbsMax`
  and `GX.E0Surgery.regM_isCauchyComplete` (`GXScaffold.BTZ.Surgery`). Everything proved in this
  file, the `M̃` injectivity step included (WP-43e removed its upstream input), is on standard
  axioms; the headline row cannot be marked until those upstream rows close.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; lean-causal `ca2ad78`
(`lake-manifest.json`).
-/

namespace GX

open Set Function

universe u

/-! ## §1 Barbot's equality for an absolutely maximal flat spacetime with a loxodromic holonomy -/

section FlatEquality

variable {d : ℕ}

/-- **Equality `𝒟(M̃) = Ω^±(Λ(Γ))`** (Barbot §11.3 with Cor 10.3; gx l.2378–2380): for a causal
flat spacetime `M` (Type 0) with a Cauchy surface developing as in (CC′), a loxodromic element in
its holonomy, and `M` absolutely maximal (Barbot's sense, every GH flat target), the image of the
developing map is the whole regular domain `Ω⁺(Λ(Γ))` (future case) or `Ω⁻(Λ(Γ))` (past case),
on which `Γ = ρ(π₁)` acts freely and properly discontinuously. -/
theorem uniformization_range_eq_of_absMax (M : Causal.Flat.FlatSpacetime.{0} d) {x₀ : M}
    {D : Causal.UniversalCover M x₀ → Causal.Minkowski d}
    {ρ : Causal.Deck (Causal.UniversalCover.proj M x₀) →* Causal.Flat.isom d} {S : Set M}
    (hpair : Causal.Flat.IsDevelopingPair x₀ D ρ)
    (hcaus : (Causal.Flat.flatCausality d M).IsCausal) (h : Causal.Flat.DevelopsCC x₀ D S)
    (hlox : ∃ γ ∈ ρ.range, Causal.Flat.IsLoxodromic (Causal.Flat.linOf γ))
    (hmax : Causal.Flat.AbsMax (fun _ => True) M) :
    (Causal.Flat.FutureRegular (Causal.Flat.limitSetJ ρ.range) ∧
        range D = Causal.Flat.omegaPlus (Causal.Flat.limitSetJ ρ.range) ∧
        Causal.Flat.ActsFreelyProperlyOn ρ.range
          (Causal.Flat.omegaPlus (Causal.Flat.limitSetJ ρ.range))) ∨
      (Causal.Flat.PastRegular (Causal.Flat.limitSetJ ρ.range) ∧
        range D = Causal.Flat.omegaMinus (Causal.Flat.limitSetJ ρ.range) ∧
        Causal.Flat.ActsFreelyProperlyOn ρ.range
          (Causal.Flat.omegaMinus (Causal.Flat.limitSetJ ρ.range))) := by
  have hcc := Causal.Flat.ccAction_of_developsCC hpair h
  obtain ⟨hfp, B, hq, hGHB, -⟩ := Causal.Flat.Lox.bcor_loxo_proper_both hcc hlox
  have hr := Causal.Flat.range_eq_omegaS_of_absMax M hpair hcaus h B hq hGHB trivial hmax
  rcases Causal.Flat.blem_loxregular hcc hlox with ⟨hF, he⟩ | ⟨hP, he⟩
  · exact Or.inl ⟨hF, hr.trans he, he ▸ hfp⟩
  · exact Or.inr ⟨hP, hr.trans he, he ▸ hfp⟩


/-- **The developing map induces `M ≅ ρ(Γ)\Ω`** (gx l.2400–2403 on the regular part; Barbot §11.3):
if `𝒟` is injective with image the open set `Ω`, `B` a GH presentation of `ρ(Γ)\Ω` (projection
`π`), and `M` absolutely maximal, then the map `M → B`, `[z] ↦ π(𝒟 z)`, is a homeomorphism and a
local isometry. (The proof of `Causal.Flat.equality_of_absMax`, kept to its end.) -/
theorem exists_isometry_quotient_of_absMax {P : Causal.Flat.FlatSpacetime.{u} d → Prop}
    (M : Causal.Flat.FlatSpacetime.{u} d) {x₀ : M}
    {D : Causal.UniversalCover M x₀ → Causal.Minkowski d}
    {ρ : Causal.Deck (Causal.UniversalCover.proj M x₀) →* Causal.Flat.isom d}
    (hpair : Causal.Flat.IsDevelopingPair x₀ D ρ) (hinj : Injective D)
    {Ω : TopologicalSpace.Opens (Causal.Minkowski d)} (hΩ : range D ⊆ Ω)
    (B : Causal.Flat.FlatSpacetime.{u} d) (π : Ω → B) (hπl : Causal.Flat.IsLocalIsometry d π)
    (hfib : ∀ p q : Ω, π p = π q ↔ ∃ γ ∈ ρ.range, γ • (p : Causal.Minkowski d) = q)
    (hGHB : Causal.Flat.GH B) (hPB : P B) (hmax : Causal.Flat.AbsMax P M) :
    ∃ f : M ≃ₜ B, Causal.Flat.IsLocalIsometry d f ∧
      ∀ z (hz : D z ∈ Ω), f (Causal.UniversalCover.proj M x₀ z) = π ⟨D z, hz⟩ := by
  letI := Causal.Flat.flatCoverChartedSpace d M x₀
  haveI := Causal.Flat.locPathConnectedSpace_of_flat d M
  haveI : PathConnectedSpace M := pathConnectedSpace_iff_connectedSpace.2 inferInstance
  have hqs : Surjective (Causal.UniversalCover.proj M x₀) := Causal.UniversalCover.proj_surjective
  have hql : Causal.Flat.IsLocalIsometry d (Causal.UniversalCover.proj M x₀) :=
    Causal.Flat.isLocalIsometry_flatCover_proj x₀
  set D' : Causal.UniversalCover M x₀ → Ω := fun z => ⟨D z, hΩ (mem_range_self z)⟩
  have hDl : Causal.Flat.IsLocalIsometry d D :=
    Causal.Flat.isLocalIsometry_iff_eventually.2 ⟨hpair.gx.1, hpair.gx.2⟩
  have hD'l : Causal.Flat.IsLocalIsometry d D' :=
    Causal.Flat.IsLocalIsometry.of_comp_left (Causal.Flat.isIsometricEmbedding_subtype_val Ω) hDl
  set f : M → B := fun x => π (D' (surjInv hqs x))
  have key : ∀ z, f (Causal.UniversalCover.proj M x₀ z) = π (D' z) := by
    intro z
    set z' := surjInv hqs (Causal.UniversalCover.proj M x₀ z)
    obtain ⟨γ, hγ⟩ := Causal.Flat.UniversalCover.exists_deck_apply_eq z z'
      (surjInv_eq hqs (Causal.UniversalCover.proj M x₀ z)).symm
    refine ((hfib (D' z) (D' z')).2 ⟨ρ γ, ⟨γ, rfl⟩, ?_⟩).symm
    simp only [D']
    rw [← hpair.equiv, hγ]
  have hfq : f ∘ (Causal.UniversalCover.proj M x₀) = π ∘ D' := funext key
  have hfl : Causal.Flat.IsLocalIsometry d f := hql.of_comp_right hqs (hfq ▸ hπl.comp hD'l)
  have hfi : Injective f := by
    intro x x' hxx'
    obtain ⟨z, rfl⟩ := hqs x
    obtain ⟨z', rfl⟩ := hqs x'
    rw [key, key] at hxx'
    obtain ⟨_, ⟨γ, rfl⟩, hγ⟩ := (hfib _ _).1 hxx'
    have h1 : D (γ.1 z) = D z' := by rw [hpair.equiv]; exact hγ
    rw [← hinj h1]
    exact (Causal.Flat.proj_deck_apply γ z).symm
  have hfs := hmax B hGHB hPB f ⟨hfl, hfi⟩
  refine ⟨(IsHomeomorph.mk hfl.continuous hfl.isOpenMap ⟨hfi, hfs⟩).homeomorph f, hfl,
    fun z hz => key z⟩

/-- The quotient package on a given open set `Ω = Ω(S̃)`: `range 𝒟 = Ω`, and `M ≅ ρ(Γ)\Ω` through a
GH presentation `π : Ω → B` (covering, local isometry, onto, fibres the `ρ(Γ)`-orbits). -/
theorem uniformization_quotient_aux (M : Causal.Flat.FlatSpacetime.{0} d) {x₀ : M}
    {D : Causal.UniversalCover M x₀ → Causal.Minkowski d}
    {ρ : Causal.Deck (Causal.UniversalCover.proj M x₀) →* Causal.Flat.isom d} {S : Set M}
    (hpair : Causal.Flat.IsDevelopingPair x₀ D ρ)
    (hcaus : (Causal.Flat.flatCausality d M).IsCausal) (h : Causal.Flat.DevelopsCC x₀ D S)
    (hlox : ∃ γ ∈ ρ.range, Causal.Flat.IsLoxodromic (Causal.Flat.linOf γ))
    (hmax : Causal.Flat.AbsMax (fun _ => True) M) (Ω : TopologicalSpace.Opens (Causal.Minkowski d))
    (hΩe : Causal.Flat.omegaS ρ.range (D '' (Causal.UniversalCover.proj M x₀ ⁻¹' S)) = Ω) :
    range D = Ω ∧ ∃ (B : Causal.Flat.FlatSpacetime.{0} d) (π : Ω → B),
      IsCoveringMap π ∧ Causal.Flat.IsLocalIsometry d π ∧ Surjective π ∧
      (∀ p q : Ω, π p = π q ↔ ∃ γ ∈ ρ.range, γ • (p : Causal.Minkowski d) = q) ∧
      Causal.Flat.GH B ∧
      ∃ f : M ≃ₜ B, Causal.Flat.IsLocalIsometry d f ∧
        ∀ z (hz : D z ∈ Ω), f (Causal.UniversalCover.proj M x₀ z) = π ⟨D z, hz⟩ := by
  have hcc := Causal.Flat.ccAction_of_developsCC hpair h
  obtain ⟨-, B, hq, hGHB, -⟩ := Causal.Flat.Lox.bcor_loxo_proper_both hcc hlox
  have hr := Causal.Flat.range_eq_omegaS_of_absMax M hpair hcaus h B hq hGHB trivial hmax
  have hopens : Causal.Flat.omegaSOpens ρ.range (D '' (Causal.UniversalCover.proj M x₀ ⁻¹' S)) = Ω :=
    TopologicalSpace.Opens.ext hΩe
  rw [hopens] at hq
  obtain ⟨π, hcov, hπl, hπs, hfib⟩ := hq.quot
  have hinj := Causal.Flat.uniformization_injective hpair hcaus h
  have hrΩ : range D = Ω := hr.trans hΩe
  obtain ⟨f, hfl, hf⟩ := exists_isometry_quotient_of_absMax M hpair hinj hrΩ.subset B π hπl hfib
    hGHB trivial hmax
  exact ⟨hrΩ, B, π, hcov, hπl, hπs, hfib, hGHB, f, hfl, hf⟩

/-- **Barbot's uniformization of an absolutely maximal flat spacetime, with the quotient** (gx
l.2378–2380 and l.2400–2403 on the regular part): `𝒟` injective, `𝒟(M̃) = Ω⁺(Λ(Γ))` (future case)
or `Ω⁻(Λ(Γ))` (past case), `Γ` free and properly discontinuous there, and `𝒟` induces
`M ≅ ρ(Γ)\Ω^±`, presented by a GH flat spacetime `B` with projection `π`. -/
theorem uniformization_of_absMax (M : Causal.Flat.FlatSpacetime.{0} d) {x₀ : M}
    {D : Causal.UniversalCover M x₀ → Causal.Minkowski d}
    {ρ : Causal.Deck (Causal.UniversalCover.proj M x₀) →* Causal.Flat.isom d} {S : Set M}
    (hpair : Causal.Flat.IsDevelopingPair x₀ D ρ)
    (hcaus : (Causal.Flat.flatCausality d M).IsCausal) (h : Causal.Flat.DevelopsCC x₀ D S)
    (hlox : ∃ γ ∈ ρ.range, Causal.Flat.IsLoxodromic (Causal.Flat.linOf γ))
    (hmax : Causal.Flat.AbsMax (fun _ => True) M) :
    Injective D ∧
    ((Causal.Flat.FutureRegular (Causal.Flat.limitSetJ ρ.range) ∧
        range D = Causal.Flat.omegaPlus (Causal.Flat.limitSetJ ρ.range) ∧
        Causal.Flat.ActsFreelyProperlyOn ρ.range
          (Causal.Flat.omegaPlus (Causal.Flat.limitSetJ ρ.range)) ∧
        ∃ (B : Causal.Flat.FlatSpacetime.{0} d) (π : Causal.Flat.limitOpensPlus ρ.range → B),
          IsCoveringMap π ∧ Causal.Flat.IsLocalIsometry d π ∧ Surjective π ∧
          (∀ p q : Causal.Flat.limitOpensPlus ρ.range,
            π p = π q ↔ ∃ γ ∈ ρ.range, γ • (p : Causal.Minkowski d) = q) ∧
          Causal.Flat.GH B ∧
          ∃ f : M ≃ₜ B, Causal.Flat.IsLocalIsometry d f ∧
            ∀ z (hz : D z ∈ Causal.Flat.limitOpensPlus ρ.range),
              f (Causal.UniversalCover.proj M x₀ z) = π ⟨D z, hz⟩) ∨
      (Causal.Flat.PastRegular (Causal.Flat.limitSetJ ρ.range) ∧
        range D = Causal.Flat.omegaMinus (Causal.Flat.limitSetJ ρ.range) ∧
        Causal.Flat.ActsFreelyProperlyOn ρ.range
          (Causal.Flat.omegaMinus (Causal.Flat.limitSetJ ρ.range)) ∧
        ∃ (B : Causal.Flat.FlatSpacetime.{0} d) (π : Causal.Flat.limitOpensMinus ρ.range → B),
          IsCoveringMap π ∧ Causal.Flat.IsLocalIsometry d π ∧ Surjective π ∧
          (∀ p q : Causal.Flat.limitOpensMinus ρ.range,
            π p = π q ↔ ∃ γ ∈ ρ.range, γ • (p : Causal.Minkowski d) = q) ∧
          Causal.Flat.GH B ∧
          ∃ f : M ≃ₜ B, Causal.Flat.IsLocalIsometry d f ∧
            ∀ z (hz : D z ∈ Causal.Flat.limitOpensMinus ρ.range),
              f (Causal.UniversalCover.proj M x₀ z) = π ⟨D z, hz⟩)) := by
  have hcc := Causal.Flat.ccAction_of_developsCC hpair h
  have hfp := (Causal.Flat.Lox.bcor_loxo_proper_both hcc hlox).1
  refine ⟨Causal.Flat.uniformization_injective hpair hcaus h, ?_⟩
  rcases Causal.Flat.blem_loxregular hcc hlox with ⟨hF, he⟩ | ⟨hP, he⟩
  · obtain ⟨hr, hB⟩ := uniformization_quotient_aux M hpair hcaus h hlox hmax
      (Causal.Flat.limitOpensPlus ρ.range) he
    exact Or.inl ⟨hF, hr, he ▸ hfp, hB⟩
  · obtain ⟨hr, hB⟩ := uniformization_quotient_aux M hpair hcaus h hlox hmax
      (Causal.Flat.limitOpensMinus ρ.range) he
    exact Or.inr ⟨hP, hr, he ▸ hfp, hB⟩

end FlatEquality

/-! ## §2 Future completeness of the regular part (the first step of l.2350) -/

section RegFutureComplete

/-- **`Reg M̃` is future complete** (gx l.2350, "Barbot uniformization Theorem then implies future
completeness of the regular part"; `def:manifold_future_complete_all`'s condition for the universal
cover of a flat spacetime): if the developing map is injective with image `Ω⁺(Λ)`, then
`𝒟(J⁺(z)) = J⁺(𝒟 z)` and `𝒟(I⁺(z)) = I⁺(𝒟 z)` for every `z`. `Ω⁺(Λ)` is convex (so its causality
is the restricted one of `𝐌³`) and a future set (`J⁺(Ω⁺) ⊆ Ω⁺`). -/
theorem isFutureComplete_of_range_eq_omegaPlus (M : Causal.Flat.FlatSpacetime.{u} 2) {x₀ : M}
    {D : Causal.UniversalCover M x₀ → Causal.Minkowski 2}
    {ρ : Causal.Deck (Causal.UniversalCover.proj M x₀) →* Causal.Flat.isom 2}
    (hpair : Causal.Flat.IsDevelopingPair x₀ D ρ) (hinj : Injective D)
    {Λ : Set (Causal.Flat.PenroseSphere 2 × ℝ)} (hr : range D = Causal.Flat.omegaPlus Λ) :
    letI := Causal.Flat.flatCoverChartedSpace 2 M x₀
    haveI := Causal.Flat.hasGroupoid_flatCover (d := 2) M x₀
    IsFutureComplete (Causal.Flat.flatCausality 2 (Causal.UniversalCover M x₀)) D := by
  letI := Causal.Flat.flatCoverChartedSpace 2 M x₀
  haveI := Causal.Flat.hasGroupoid_flatCover (d := 2) M x₀
  have hDl : Causal.Flat.IsLocalIsometry 2 D :=
    Causal.Flat.isLocalIsometry_iff_eventually.2 ⟨hpair.gx.1, hpair.gx.2⟩
  have hemb : Causal.Flat.IsIsometricEmbedding 2 D := ⟨hDl, hinj⟩
  set U : TopologicalSpace.Opens (Causal.Minkowski 2) := ⟨range D, hDl.isOpenMap.isOpen_range⟩
  have hUc : Convex ℝ (U : Set (Causal.Minkowski 2)) := by
    show Convex ℝ (range D); rw [hr]; exact Causal.Flat.convex_omegaPlus Λ
  have hU : (U : Set (Causal.Minkowski 2)) = D '' ((⊤ : TopologicalSpace.Opens (Causal.UniversalCover M x₀)) : Set (Causal.UniversalCover M x₀)) := by
    simp [U, image_univ]
  have hrel := hemb.rel_iff ⊤ U hU
  rw [Causal.Flat.flatCausality_self] at hrel
  intro z
  have hfut : ∀ q, (Causal.minkowski 2).le ⊤ (D z) q → q ∈ range D := fun q hq => by
    rw [hr]; exact Causal.Flat.Jplus_omegaPlus_subset Λ ⟨D z, hr ▸ mem_range_self z, hq⟩
  constructor
  · ext q
    simp only [mem_image, Causal.Precausality.mem_Jplus_singleton]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ((Causal.Flat.le_iff_of_convex hUc).1 (((hrel z w).1).1 hw)).2.2
    · intro hq
      obtain ⟨w, rfl⟩ := hfut q hq
      exact ⟨w, ((hrel z w).1).2 ((Causal.Flat.le_iff_of_convex hUc).2
        ⟨mem_range_self z, mem_range_self w, hq⟩), rfl⟩
  · ext q
    simp only [mem_image, Causal.Precausality.mem_Iplus_singleton]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ((Causal.Flat.lt_iff_of_convex hUc).1 (((hrel z w).2).1 hw)).2.2
    · intro hq
      obtain ⟨w, rfl⟩ := hfut q ((Causal.minkowski 2).le_of_lt hq)
      exact ⟨w, ((hrel z w).2).2 ((Causal.Flat.lt_iff_of_convex hUc).2
        ⟨mem_range_self z, mem_range_self w, hq⟩), rfl⟩

end RegFutureComplete

/-! ## §3 The injectivity step of the headline's proof (l.2392–2394), abstractly -/

section InjectivityStep

variable {N : Type*} [TopologicalSpace N]

/-- **The injectivity step** (gx l.2392–2394): "Let `x, y ∈ M̃` with `𝒟(x) = 𝒟(y)`. Since `M` is
future complete, `𝒟(I⁺(x)) = I⁺(𝒟(x)) = I⁺(𝒟(y)) = 𝒟(I⁺(y))`, and since `I⁺(x)`, `I⁺(y)` are
subsets of `reg` and `𝒟|reg` is a bijection, `I⁺(x) = I⁺(y)`; `M̃` is future distinguishing, so
`x = y`." For any causality `C` and any `𝒟` future complete in the sense of
`def:manifold_future_complete_all`, injective on a set `R` containing every `I⁺(x)`. -/
theorem injective_of_isFutureComplete {C : Causal.Causality N} {D : N → Causal.Minkowski 2}
    (hfc : IsFutureComplete C D) {R : Set N} (hR : InjOn D R) (hI : ∀ x, C.Iplus ⊤ {x} ⊆ R)
    (hdist : IsFutureDistinguishing C) : Injective D := by
  intro x y hxy
  apply hdist
  have h : D '' C.Iplus ⊤ {x} = D '' C.Iplus ⊤ {y} := by
    rw [(hfc x).2, (hfc y).2, hxy]
  exact (hR.image_eq_image_iff (hI x) (hI y)).1 h

end InjectivityStep

/-! ## §3b The future-case selection: a BTZ point forbids a past-complete `Reg M̃` (DEC-77 (a)) -/

section FutureSelectionTools

open Filter Topology

open scoped Real
attribute [local instance] btzE0Structure

/-- Near a point of its source lying in the sector of `y₀`, a chart of `BTZE0`'s maximal a.e.
atlas is `g •` the sector chart `chartMap y₀` of the fixed base `y₀` (the angle branch of `y₀`). -/
theorem aeChart_eventually_chartMap_sector {c : OpenPartialHomeomorph BTZE0 (Causal.Minkowski 2)}
    (hc : c ∈ aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) {x : BTZE0}
    (hx : x ∈ c.source) {y₀ : E0} (hy₀ : y₀.2 ≠ 0) (hxs : E0.toPaper x ∈ E0.sector y₀) :
    ∃ g : Causal.Flat.isom 2, ∀ᶠ z in 𝓝 x,
      c z = g • E0.chartMap y₀ (E0.toPaper z) := by
  set y := E0.toPaper x
  have hyax : y ∉ E0.axis := E0.not_mem_axis_of_mem_sector hxs
  set p : ℝ × ℝ × ℝ := (y.1, E0.rad y, E0.angle y₀ y)
  have hpx : orbitMk (GammaA (2 * π)) (btzPaperCyl p) = x := by
    rw [← E0.toPaper_symm_eq_orbitMk hyax (E0.polar_angle hy₀ y), Homeomorph.symm_apply_apply]
  obtain ⟨g, hg⟩ := btz_chart_eq_smul_btzPaperDev isBTZStructure_btzE0 hc
    (p := p) (E0.rad_pos.2 hyax) (by rw [hpx]; exact hx)
  set φ : BTZE0 → ℝ × ℝ × ℝ := fun z =>
    ((E0.toPaper z).1, E0.rad (E0.toPaper z), E0.angle y₀ (E0.toPaper z))
  have hφ : ContinuousAt φ x := by
    have hang : ContinuousAt (E0.angle y₀) y :=
      (E0.continuousOn_angle y₀).continuousAt ((E0.isOpen_sector y₀).mem_nhds hxs)
    have h3 : ContinuousAt (fun z => E0.angle y₀ (E0.toPaper z)) x :=
      ContinuousAt.comp (g := E0.angle y₀) (f := E0.toPaper) hang E0.toPaper.continuous.continuousAt
    exact (continuous_fst.comp E0.toPaper.continuous).continuousAt.prodMk
      ((E0.continuous_rad.comp E0.toPaper.continuous).continuousAt.prodMk h3)
  have h1 : ∀ᶠ z in 𝓝 x, c (orbitMk (GammaA (2 * π)) (btzPaperCyl (φ z))) =
      g • btzPaperDev (φ z) := hφ.eventually hg
  have h2 : ∀ᶠ z in 𝓝 x, E0.toPaper z ∈ E0.sector y₀ :=
    E0.toPaper.continuous.continuousAt.preimage_mem_nhds
      ((E0.isOpen_sector y₀).mem_nhds hxs)
  refine ⟨g, ?_⟩
  filter_upwards [h1, h2] with z hz1 hz2
  have hzax : E0.toPaper z ∉ E0.axis := E0.not_mem_axis_of_mem_sector hz2
  have hz : orbitMk (GammaA (2 * π)) (btzPaperCyl (φ z)) = z := by
    rw [← E0.toPaper_symm_eq_orbitMk hzax (E0.polar_angle hy₀ (E0.toPaper z)),
      Homeomorph.symm_apply_apply]
  rw [hz] at hz1
  rw [hz1, E0.chartMap_eq]

/-- **A locally isometric reading through an open map is globally one isometry** on a
preconnected space: if near every point `D = g • F` for some `g ∈ Isom(𝐌³)`, one `g` works
everywhere (two isometries agreeing on the non-empty open `D(t)` are equal). -/
theorem exists_isom_eq_of_locally {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    [Nonempty X] {D F : X → Causal.Minkowski 2} (hD : IsOpenMap D)
    (h : ∀ x, ∃ g : Causal.Flat.isom 2, ∀ᶠ y in 𝓝 x, D y = g • F y) :
    ∃ g : Causal.Flat.isom 2, ∀ y, D y = g • F y := by
  have huniq : ∀ (x : X) (g g' : Causal.Flat.isom 2), (∀ᶠ y in 𝓝 x, D y = g • F y) →
      (∀ᶠ y in 𝓝 x, D y = g' • F y) → g = g' := by
    intro x g g' h1 h2
    obtain ⟨t, ht, hto, hxt⟩ := eventually_nhds_iff.1 (h1.and h2)
    have hA : ((g⁻¹ : Causal.Flat.isom 2) : Causal.Minkowski 2 ≃ᵃ[ℝ] Causal.Minkowski 2).toAffineMap =
        ((g'⁻¹ : Causal.Flat.isom 2) : Causal.Minkowski 2 ≃ᵃ[ℝ] Causal.Minkowski 2).toAffineMap := by
      refine AffineMap.ext_on ((hD t hto).affineSpan_eq_top ⟨D x, x, hxt, rfl⟩) ?_
      rintro _ ⟨y, hy, rfl⟩
      show ((g⁻¹ : Causal.Flat.isom 2) : Causal.Minkowski 2 ≃ᵃ[ℝ] Causal.Minkowski 2) (D y) =
        ((g'⁻¹ : Causal.Flat.isom 2) : Causal.Minkowski 2 ≃ᵃ[ℝ] Causal.Minkowski 2) (D y)
      rw [← Causal.Flat.isom_smul_def, ← Causal.Flat.isom_smul_def]
      conv_lhs => rw [(ht y hy).1, inv_smul_smul]
      rw [(ht y hy).2, inv_smul_smul]
    have : (g⁻¹ : Causal.Flat.isom 2) = g'⁻¹ :=
      Subtype.ext (AffineEquiv.toAffineMap_injective hA)
    exact inv_injective this
  choose A hA using h
  have hlc : IsLocallyConstant A := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    filter_upwards [(hA x).eventually_nhds] with y hy
    exact huniq y _ _ (hA y) hy
  obtain ⟨x₀⟩ := ‹Nonempty X›
  refine ⟨A x₀, fun y => ?_⟩
  rw [← hlc.apply_eq_of_preconnectedSpace y x₀]
  exact (hA y).self_of_nhds

end FutureSelectionTools

section FutureSelection

open Filter Topology TopologicalSpace E0CBG E0Spear E0AbsMax
open scoped Causal.Flat
attribute [local instance] btzE0Structure

variable {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
  [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]

/-- The base point in `M` of a point of `Reg M̃` (the universal cover of `Reg M`). -/
noncomputable def regCoverBase {x₀ : e0RegMFlat M}
    (w : Causal.UniversalCover (e0RegMFlat M) x₀) : M :=
  (show E0LM.e0RegM M from Causal.UniversalCover.proj (e0RegMFlat M) x₀ w).1

theorem continuous_regCoverBase {x₀ : e0RegMFlat M} :
    Continuous (regCoverBase (M := M) (x₀ := x₀)) :=
  continuous_subtype_val.comp (Causal.Flat.isCoveringMap_flatCover_proj 2 (e0RegMFlat M) x₀).continuous

/-- **Near a regular point read in a BTZ chart, the developing map is `g •` the sector chart**:
if `w ∈ Reg M̃` lies over a point of the source of the chart `chartAt E0Y x` of `M`, read in the
`𝔼₀` part in the sector of `y₀`, then near `w`, `𝒟 = g • chartMap y₀ ∘ paperOfY ∘ chartAt E0Y x`
for some `g ∈ Isom(𝐌³)` (the developing map, the cover's charts, the flat chart of `Reg M`, and the
transition to the chart at `x`, each locally an isometry). -/
theorem dev_eventually_chartMap_sector {x₀ : e0RegMFlat M}
    {D : Causal.UniversalCover (e0RegMFlat M) x₀ → Causal.Minkowski 2}
    {ρ : Causal.Deck (Causal.UniversalCover.proj (e0RegMFlat M) x₀) →* Causal.Flat.isom 2}
    (hpair : Causal.Flat.IsDevelopingPair x₀ D ρ) (x : M) {y₀ : E0} (hy₀ : y₀.2 ≠ 0)
    (w : Causal.UniversalCover (e0RegMFlat M) x₀)
    (hw : regCoverBase w ∈ (chartAt E0Y x).source)
    (hwr : chartAt E0Y x (regCoverBase w) ∈ range Sum.inr)
    (hws : E0.paperOfY (chartAt E0Y x (regCoverBase w)) ∈ E0.sector y₀) :
    ∃ g : Causal.Flat.isom 2, ∀ᶠ w' in 𝓝 w,
      D w' = g • E0.chartMap y₀ (E0.paperOfY (chartAt E0Y x (regCoverBase w'))) := by
  letI := Causal.Flat.flatCoverChartedSpace 2 (e0RegMFlat M) x₀
  haveI := Causal.Flat.hasGroupoid_flatCover (d := 2) (e0RegMFlat M) x₀
  have hDl : Causal.Flat.IsLocalIsometry 2 D :=
    Causal.Flat.isLocalIsometry_iff_eventually.2 ⟨hpair.gx.1, hpair.gx.2⟩
  obtain ⟨g2, hg2⟩ := (Causal.Flat.isLocalIsometry_iff_eventually.1 hDl).2 w
  have hpl := Causal.Flat.isLocalIsometry_flatCover_proj (d := 2) (M := e0RegMFlat M) x₀
  obtain ⟨g1, hg1⟩ := (Causal.Flat.isLocalIsometry_iff_eventually.1 hpl).2 w
  set q := Causal.UniversalCover.proj (e0RegMFlat M) x₀ with hq
  set y : E0LM.e0RegM M := q w with hy
  have hyw : (y : M) = regCoverBase w := rfl
  set e := chartAt E0Y x with he
  set em := chartAt E0Y (y : M) with hem
  rw [← hyw] at hw hwr hws
  obtain ⟨u, hu⟩ := hwr
  have hus : E0.toPaper u ∈ E0.sector y₀ := by rw [← E0.paperOfY_inr, hu]; exact hws
  have hureg : u ∈ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0 :=
    (E0.mem_reg_iff_toPaper u).2 (E0.not_mem_axis_of_mem_sector hus)
  obtain ⟨c'', hc'', hu''⟩ := mem_support.1 hureg
  obtain ⟨g3, hg3⟩ := aeChart_eventually_chartMap_sector hc'' hu'' hy₀ hus
  set c₂ := e0Inr.symm.trans c'' with hc₂def
  have hc₂ : c₂ ∈ e0Atlas := e0InrChart_mem_e0Atlas hc''
  set R := E0LM.regAtlasChart y with hR
  have ht : e.symm.trans em ∈ e0Groupoid :=
    HasGroupoid.compatible (chart_mem_atlas E0Y x) (chart_mem_atlas E0Y (y : M))
  have hyem : (y : M) ∈ em.source := mem_chart_source E0Y (y : M)
  have hc₂src : e (y : M) ∈ c₂.source := by
    rw [← hu]; exact mem_e0InrChart_source.2 ⟨u, hu'', rfl⟩
  have hvsrc : c₂ (e y) ∈ (c₂.symm.trans ((e.symm.trans em).trans R)).source := by
    simp only [OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage,
      OpenPartialHomeomorph.symm_source, OpenPartialHomeomorph.coe_trans, comp_apply,
      c₂.left_inv hc₂src, e.left_inv hw]
    exact ⟨c₂.map_source hc₂src, ⟨e.map_source hw, hyem⟩, E0LM.mem_regAtlasChart_source y⟩
  obtain ⟨g4, hg4⟩ := E0LM.e0_flat_transition_aux ht hc₂ (E0LM.regAtlasChart_mem y) _ hvsrc
  have hcont : ContinuousAt (fun m => c₂ (e m)) (y : M) :=
    (c₂.continuousAt hc₂src).comp (e.continuousAt hw)
  have hM : ∀ᶠ m in 𝓝 (y : M), R (em m) = (g4 * g3) • E0.chartMap y₀ (E0.paperOfY (e m)) := by
    have hA := hcont.eventually hg4
    have hB : ∀ᶠ m in 𝓝 (y : M), e m ∈ c₂.source :=
      (e.continuousAt hw).preimage_mem_nhds (c₂.open_source.mem_nhds hc₂src)
    have hC : ∀ᶠ m in 𝓝 (y : M), m ∈ e.source := e.open_source.mem_nhds hw
    have hval : e0Inr.symm (e (y : M)) = u := by rw [← hu, e0Inr_symm_inr]
    have hT : Tendsto (fun m => e0Inr.symm (e m)) (𝓝 (y : M)) (𝓝 u) := by
      have h0 : ContinuousAt (fun m => e0Inr.symm (e m)) (y : M) :=
        (e0Inr.symm.continuousAt (by rw [e0Inr_symm_source]; exact ⟨u, hu⟩)).comp
          (e.continuousAt hw)
      have h1 := h0.tendsto
      rwa [hval] at h1
    have hD' := hT.eventually hg3
    filter_upwards [hA, hB, hC, hD'] with m hA hB hC hD'
    simp only [OpenPartialHomeomorph.coe_trans, comp_apply] at hA
    rw [c₂.left_inv hB, e.left_inv hC] at hA
    rw [hA, mul_smul]
    congr 1
  have hbc : ContinuousAt (fun w' => regCoverBase w') w := continuous_regCoverBase.continuousAt
  have hM' := hbc.eventually hM
  refine ⟨g2 * g1⁻¹ * (g4 * g3), ?_⟩
  filter_upwards [hg2, hg1, hM'] with w' h2 h1 h0
  have hchart : (chartAt (Causal.Minkowski 2) (q w)) (q w') = R (em (regCoverBase w')) := by
    show ((E0LM.regChartM y).subtypeRestr ⟨y⟩) (q w') = _
    rw [regChart_subtypeRestr_eq]
    rfl
  rw [chartAt_self_eq, OpenPartialHomeomorph.refl_apply, id] at h2
  rw [hchart, h0] at h1
  have h1' : (chartAt (Causal.Minkowski 2) w) w' =
      g1⁻¹ • (g4 * g3) • E0.chartMap y₀ (E0.paperOfY (e (regCoverBase w'))) := by
    rw [h1, inv_smul_smul]
  rw [h2, h1', ← mul_smul, ← mul_smul]

/-- `btzPaperDev (τ₁ + s, s, 0) = (τ₁ + s, (τ₁, 0))`: the radial ray at angle `0`. -/
theorem btzPaperDev_ray (τ₁ s : ℝ) :
    btzPaperDev (τ₁ + s, s, 0) =
      ((τ₁ + s, WithLp.toLp 2 ![τ₁, 0]) : Causal.Minkowski 2) := by
  simp only [btzPaperDev]
  refine Prod.ext (by simp) ?_
  ext i; fin_cases i <;> simp

/-- **A BTZ point forbids a past-complete developed regular part** (the future-case selection,
DEC-77 (a); D-11 (d)'s mechanism without extending `𝒟`): if `M` has a BTZ point `x`, no developing
map of `Reg M̃` is injective with a past-complete image (`p ≤ 𝒟 z ⇒ p ∈ 𝒟(Reg M̃)`). Proof: in the
chart at `x` (paper coordinates, `x ↦ (τ₁, 0)`), the radial segment `c(s) = (τ₁ + s, s)`, `s ↓ 0`,
runs in `Reg M` towards `x`; on the component `X` of the lifted sector containing a lift `z̃` of
`c(δ)`, `𝒟 = g • chartMap` (`dev_eventually_chartMap_sector`, `exists_isom_eq_of_locally`), so the
lifts `c̃(s) ∈ X` develop to `g • (τ₁ + s, τ₁, 0) → p := g • (τ₁, τ₁, 0) ≤ 𝒟 z̃`. Past completeness
gives `p = 𝒟 w̃`; `𝒟` is an open embedding, so `c̃(s) → w̃`, and the base points `c(s)` converge
both to the regular point `w̃`'s base and to the BTZ point `x` in the Hausdorff `M`. -/
theorem false_of_sing_of_pastComplete (hsing : (Causal.CBG.chartedSing e0SingY M 0).Nonempty)
    {x₀ : e0RegMFlat M}
    {D : Causal.UniversalCover (e0RegMFlat M) x₀ → Causal.Minkowski 2}
    {ρ : Causal.Deck (Causal.UniversalCover.proj (e0RegMFlat M) x₀) →* Causal.Flat.isom 2}
    (hpair : Causal.Flat.IsDevelopingPair x₀ D ρ) (hinj : Injective D)
    (hpast : ∀ (p : Causal.Minkowski 2) (z : Causal.UniversalCover (e0RegMFlat M) x₀),
      (Causal.minkowski 2).le ⊤ p (D z) → p ∈ range D) : False := by
  letI := Causal.Flat.flatCoverChartedSpace 2 (e0RegMFlat M) x₀
  haveI := Causal.Flat.hasGroupoid_flatCover (d := 2) (e0RegMFlat M) x₀
  haveI := Causal.Flat.locPathConnectedSpace_of_flat 2 (Causal.UniversalCover (e0RegMFlat M) x₀)
  haveI := Causal.Flat.locPathConnectedSpace_of_flat 2 (e0RegMFlat M)
  haveI : PathConnectedSpace (e0RegMFlat M) := pathConnectedSpace_iff_connectedSpace.2 inferInstance
  have hcov := Causal.Flat.isCoveringMap_flatCover_proj 2 (e0RegMFlat M) x₀
  have hDl : Causal.Flat.IsLocalIsometry 2 D :=
    Causal.Flat.isLocalIsometry_iff_eventually.2 ⟨hpair.gx.1, hpair.gx.2⟩
  set q := Causal.UniversalCover.proj (e0RegMFlat M) x₀ with hq
  obtain ⟨x, hx⟩ := hsing
  set e := chartAt E0Y x with he
  obtain ⟨b, hb, hbax⟩ := E0LM.mem_e0SingY_zero_iff.1 (show e x ∈ e0SingY 0 from hx)
  set a := E0.toPaper b with ha
  have ha2 : a.2 = 0 := hbax
  set Φ := e.trans E0.paperOfY with hΦ
  have hxΦ : x ∈ Φ.source := by
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨mem_chart_source E0Y x, ?_⟩
    show e x ∈ E0.paperOfY.source
    rw [E0.paperOfY_source, hb]; exact ⟨b, rfl⟩
  have hΦx : Φ x = a := by
    show E0.paperOfY (e x) = a
    rw [hb, E0.paperOfY_inr]
  have hat : a ∈ Φ.target := hΦx ▸ Φ.map_source hxΦ
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 Φ.open_target a hat
  set y₀ : E0 := (a.1, 1) with hy₀def
  have hy₀ : y₀.2 ≠ 0 := one_ne_zero
  set V : Set E0 := Metric.ball a ε ∩ E0.sector y₀ with hV
  have hVo : IsOpen V := Metric.isOpen_ball.inter (E0.isOpen_sector y₀)
  set c : ℝ → E0 := fun s => (a.1 + s, (s : ℂ)) with hcdef
  have hcc : Continuous c := (continuous_const.add continuous_id).prodMk Complex.continuous_ofReal
  have hc0 : c 0 = a := Prod.ext (by simp [c]) (by simp [c, ha2])
  have hcV : ∀ s, 0 < s → s < ε → c s ∈ V := by
    intro s hs hsε
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, Prod.dist_eq]
      have h1 : dist (a.1 + s) a.1 = s := by
        rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos hs]
      have h2 : dist (s : ℂ) a.2 = s := by
        rw [ha2, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg hs.le]
      show max (dist (a.1 + s) a.1) (dist (s : ℂ) a.2) < ε
      rw [h1, h2, max_self]; exact hsε
    · show (s : ℂ) / 1 ∈ Complex.slitPlane
      rw [div_one]; exact Complex.ofReal_mem_slitPlane.2 hs
  have hctgt : ∀ s, 0 < s → s < ε → c s ∈ Φ.target := fun s hs hsε => hball (hcV s hs hsε).1
  set κ : ℝ → M := fun s => Φ.symm (c s) with hκdef
  have hκsrc : ∀ s, 0 < s → s < ε → κ s ∈ Φ.source := fun s hs hsε => Φ.map_target (hctgt s hs hsε)
  have hΦκ : ∀ s, 0 < s → s < ε → Φ (κ s) = c s := fun s hs hsε => Φ.right_inv (hctgt s hs hsε)
  have hκW : ∀ s, 0 < s → s < ε → κ s ∈ Φ.source ∩ Φ ⁻¹' V := fun s hs hsε =>
    ⟨hκsrc s hs hsε, by rw [mem_preimage, hΦκ s hs hsε]; exact hcV s hs hsε⟩
  -- the points of `Φ.source ∩ Φ⁻¹ V` are regular
  have hWreg : ∀ m ∈ Φ.source ∩ Φ ⁻¹' V, m ∈ E0LM.e0RegM M := by
    rintro m ⟨hm, hmV⟩
    rw [OpenPartialHomeomorph.trans_source] at hm
    obtain ⟨hm1, hm2⟩ := hm
    rw [E0LM.mem_e0RegM_iff hm1]
    rw [mem_preimage, E0.paperOfY_source] at hm2
    obtain ⟨u, hu⟩ := hm2
    rw [← hu, E0.inr_mem_e0Reg_iff_toPaper]
    have : E0.toPaper u = Φ m := by
      show E0.toPaper u = E0.paperOfY (e m); rw [← hu, E0.paperOfY_inr]
    rw [this]; exact E0.not_mem_axis_of_mem_sector hmV.2
  -- `κ s → x` as `s ↓ 0`
  have hκt : Tendsto κ (𝓝[>] 0) (𝓝 x) := by
    have h1 : Tendsto c (𝓝 0) (𝓝 a) := by rw [← hc0]; exact hcc.tendsto 0
    have h2 : Tendsto Φ.symm (𝓝 a) (𝓝 x) := by
      have := Φ.continuousAt_symm hat
      rw [ContinuousAt, ← hΦx, Φ.left_inv hxΦ, hΦx] at this
      exact this
    exact (h2.comp h1).mono_left nhdsWithin_le_nhds
  set δ : ℝ := ε / 2 with hδdef
  have hδ : 0 < δ := half_pos hε
  have hδε : δ < ε := half_lt_self hε
  -- the base lift
  obtain ⟨z₁, hz₁⟩ := Causal.UniversalCover.proj_surjective (Y := e0RegMFlat M) (y₀ := x₀)
    (show e0RegMFlat M from ⟨κ δ, hWreg _ (hκW δ hδ hδε)⟩)
  have hz₁b : regCoverBase z₁ = κ δ := by
    show (show E0LM.e0RegM M from q z₁).1 = κ δ
    rw [show q z₁ = _ from hz₁]
  set X0 : Set (Causal.UniversalCover (e0RegMFlat M) x₀) :=
    regCoverBase ⁻¹' (Φ.source ∩ Φ ⁻¹' V) with hX0
  have hX0o : IsOpen X0 := (Φ.isOpen_inter_preimage hVo).preimage continuous_regCoverBase
  have hz₁X0 : z₁ ∈ X0 := by rw [hX0, mem_preimage, hz₁b]; exact hκW δ hδ hδε
  set X := connectedComponentIn X0 z₁ with hXdef
  have hXo : IsOpen X := hX0o.connectedComponentIn
  have hXX0 : X ⊆ X0 := connectedComponentIn_subset _ _
  have hz₁X : z₁ ∈ X := mem_connectedComponentIn hz₁X0
  -- on `X`, `𝒟 = g • chartMap y₀ ∘ Φ`
  haveI : PreconnectedSpace X := Subtype.preconnectedSpace isPreconnected_connectedComponentIn
  haveI : Nonempty X := ⟨⟨z₁, hz₁X⟩⟩
  obtain ⟨g, hg⟩ := exists_isom_eq_of_locally (X := X) (D := fun w => D w.1)
    (F := fun w => E0.chartMap y₀ (E0.paperOfY (e (regCoverBase w.1))))
    (hDl.isOpenMap.comp hXo.isOpenMap_subtype_val) (fun w => by
      have hw := hXX0 w.2
      rw [hX0, mem_preimage] at hw
      obtain ⟨hw1, hw2⟩ := hw
      rw [OpenPartialHomeomorph.trans_source] at hw1
      obtain ⟨g', hg'⟩ := dev_eventually_chartMap_sector hpair x hy₀ w.1 hw1.1
        (by rw [← E0.paperOfY_source]; exact hw1.2) hw2.2
      exact ⟨g', (continuous_subtype_val.tendsto w).eventually hg'⟩)
  have hgX : ∀ w ∈ X, D w = g • E0.chartMap y₀ (Φ (regCoverBase w)) := fun w hw => hg ⟨w, hw⟩
  -- lifts of the segment
  have hlift : ∀ s, 0 < s → s ≤ δ → ∃ w ∈ X, regCoverBase w = κ s := by
    intro s hs hsδ
    set σ : unitInterval → ℝ := fun t => δ + (t : ℝ) * (s - δ) with hσ
    have hσc : Continuous σ := continuous_const.add (continuous_subtype_val.mul continuous_const)
    have hσlo : ∀ t, s ≤ σ t := fun t => by
      have h1 : (t : ℝ) ≤ 1 := t.2.2
      have : (t : ℝ) * (s - δ) ≥ 1 * (s - δ) := mul_le_mul_of_nonpos_right h1 (by linarith)
      simp only [σ]; linarith
    have hσhi : ∀ t, σ t ≤ δ := fun t => by
      have h0 : 0 ≤ (t : ℝ) := t.2.1
      have : (t : ℝ) * (s - δ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h0 (by linarith)
      simp only [σ]; linarith
    have hσpos : ∀ t, 0 < σ t := fun t => hs.trans_le (hσlo t)
    have hσε : ∀ t, σ t < ε := fun t => (hσhi t).trans_lt hδε
    have hκσ : Continuous fun t => κ (σ t) :=
      Φ.continuousOn_symm.comp_continuous (hcc.comp hσc) fun t => hctgt _ (hσpos t) (hσε t)
    let γ : C(unitInterval, e0RegMFlat M) :=
      ⟨fun t => (show e0RegMFlat M from ⟨κ (σ t), hWreg _ (hκW _ (hσpos t) (hσε t))⟩),
        hκσ.subtype_mk _⟩
    have hγ0 : γ 0 = q z₁ := by
      rw [show q z₁ = _ from hz₁]; apply Subtype.ext
      show κ (σ 0) = κ δ
      simp [σ]
    set Γ := hcov.liftPath γ z₁ hγ0 with hΓ
    have hΓq : ∀ t, regCoverBase (Γ t) = κ (σ t) := fun t => by
      have := congrFun (hcov.liftPath_lifts γ z₁ hγ0) t
      show (show E0LM.e0RegM M from q (Γ t)).1 = _
      rw [show q (Γ t) = γ t from this]
      rfl
    have hsub : range Γ ⊆ X0 := by
      rintro _ ⟨t, rfl⟩
      rw [hX0, mem_preimage, hΓq]; exact hκW _ (hσpos t) (hσε t)
    have hΓX : range Γ ⊆ X := (isPreconnected_range Γ.continuous).subset_connectedComponentIn
      ⟨0, hcov.liftPath_zero γ z₁ hγ0⟩ hsub
    refine ⟨Γ 1, hΓX ⟨1, rfl⟩, ?_⟩
    rw [hΓq]; simp [σ]
  have hlift' : ∀ s : ℝ, ∃ w, 0 < s → s ≤ δ → w ∈ X ∧ regCoverBase w = κ s := by
    intro s
    by_cases h : 0 < s ∧ s ≤ δ
    · obtain ⟨w, hw, hw'⟩ := hlift s h.1 h.2
      exact ⟨w, fun _ _ => ⟨hw, hw'⟩⟩
    · exact ⟨z₁, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose C hC using hlift'
  -- the developed lifts
  set v : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![a.1, 0] with hv
  have hDc : ∀ s, 0 < s → s ≤ δ → D (C s) = g • ((a.1 + s, v) : Causal.Minkowski 2) := by
    intro s hs hsδ
    obtain ⟨hCX, hCb⟩ := hC s hs hsδ
    rw [hgX _ hCX, hCb, hΦκ s hs (hsδ.trans_lt hδε), E0.chartMap_eq]
    have hrad : E0.rad (c s) = s := by
      simp only [E0.rad, c, Complex.norm_real, Real.norm_of_nonneg hs.le]
    have hang : E0.angle y₀ (c s) = 0 := by
      simp only [E0.angle, y₀, c, Complex.arg_one, div_one, zero_add]
      exact Complex.arg_ofReal_of_nonneg hs.le
    rw [hrad, hang]
    exact congrArg _ (btzPaperDev_ray a.1 s)
  have hDz₁ : D z₁ = g • ((a.1 + δ, v) : Causal.Minkowski 2) := by
    have hC1 := hC δ hδ le_rfl
    rw [hgX _ hz₁X, hz₁b, ← hC1.2, ← hgX _ hC1.1]
    exact hDc δ hδ le_rfl
  set p : Causal.Minkowski 2 := g • ((a.1, v) : Causal.Minkowski 2) with hp
  have hle : (Causal.minkowski 2).le ⊤ p (D z₁) := by
    rw [hDz₁, hp, Causal.Flat.isom_le_top_iff, Causal.minkowski_le_top_iff]
    simp only [sub_self, norm_zero, add_sub_cancel_left]
    exact hδ.le
  obtain ⟨w₁, hw₁⟩ := hpast p z₁ hle
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioo 0 δ := Ioo_mem_nhdsGT hδ
  have hDt : Tendsto (D ∘ C) (𝓝[>] 0) (𝓝 (D w₁)) := by
    rw [hw₁]
    have h1 : Tendsto (fun s : ℝ => g • ((a.1 + s, v) : Causal.Minkowski 2)) (𝓝[>] 0) (𝓝 p) := by
      have hcont : Continuous fun s : ℝ => g • ((a.1 + s, v) : Causal.Minkowski 2) :=
        (continuous_const_smul g).comp ((continuous_const.add continuous_id).prodMk continuous_const)
      have := hcont.tendsto 0
      simp only [add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine h1.congr' ?_
    filter_upwards [hev] with s hs
    exact (hDc s hs.1 hs.2.le).symm
  have hemb : IsOpenEmbedding D :=
    .of_continuous_injective_isOpenMap hDl.continuous hinj hDl.isOpenMap
  have hCt : Tendsto C (𝓝[>] 0) (𝓝 w₁) := hemb.isEmbedding.tendsto_nhds_iff.2 hDt
  have hbt : Tendsto (regCoverBase ∘ C) (𝓝[>] 0) (𝓝 (regCoverBase w₁)) :=
    (continuous_regCoverBase.tendsto _).comp hCt
  have hbx : Tendsto (regCoverBase ∘ C) (𝓝[>] 0) (𝓝 x) := by
    refine hκt.congr' ?_
    filter_upwards [hev] with s hs
    exact ((hC s hs.1 hs.2.le).2).symm
  have hxw : regCoverBase w₁ = x := tendsto_nhds_unique hbt hbx
  have hreg : regCoverBase w₁ ∈ E0LM.e0RegM M := (show E0LM.e0RegM M from q w₁).2
  rw [hxw] at hreg
  exact hreg hx

end FutureSelection

/-! ## §4 The `𝔼₀` case: `Reg M` of a GH Cauchy-compact Cauchy-maximal `𝔼₀`-manifold -/

section E0

open E0CBG E0Spear E0AbsMax
open scoped Causal.Flat

variable {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [SecondCountableTopology M]
  [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]

/-- **The uniformization of `Reg M`** (gx l.2377–2381 and l.2400–2403 on the regular part, in
DEC-28's Cauchy-compact form): for `M` a globally hyperbolic, Cauchy-compact, Cauchy-maximal
`𝔼₀`-manifold whose `π₁(Reg M)` is not metabelian, and **every** developing pair `(𝒟, ρ)` of
`Reg M`: a loxodromic element in `ρ(π₁)` (DEC-75); `𝒟` injective; `ρ` faithful, discrete,
torsion-free; the lightlike planes `Π_w` (`w ∈ Λ = Λ(ρ(π₁))`) a `ρ(π₁)`-invariant family; and, in
the future case, `𝒟(Reg M̃) = Ω⁺(Λ) = ⋂_w I⁺(Π_w)` (**equality**, Barbot §11.3 from B21 Cor 2.18),
`ρ(π₁)` free and properly discontinuous on it, `Reg M̃` future complete, and `𝒟` induces
`Reg M ≅ ρ(π₁)\Ω⁺(Λ)` — or the time-reversed statement. The case selection is
`btz_uniformization`'s. -/
theorem btz_uniformization_reg (hGH : (CE M).GloballyHyperbolic) (hCC : E0CauchyCompact M)
    (hmax : IsE0CauchyMaximal M) (x₀ : e0RegMFlat M)
    (hnm : ¬IsMetabelianGroup (Causal.Deck (Causal.UniversalCover.proj (e0RegMFlat M) x₀)))
    (D : Causal.UniversalCover (e0RegMFlat M) x₀ → Causal.Minkowski 2)
    (ρ : Causal.Deck (Causal.UniversalCover.proj (e0RegMFlat M) x₀) →* Causal.Flat.isom 2)
    (hpair : Causal.Flat.IsDevelopingPair x₀ D ρ) :
    (∃ γ ∈ ρ.range, Causal.Flat.IsLoxodromic (Causal.Flat.linOf γ)) ∧ Injective D ∧
      Injective ρ ∧ DiscreteTopology ρ.range ∧ Causal.Flat.IsTorsionFreeSubgroup ρ.range ∧
      (∀ γ ∈ ρ.range, ∀ w ∈ Causal.Flat.limitSetJ ρ.range,
        Causal.Flat.isomPenrose γ w ∈ Causal.Flat.limitSetJ ρ.range ∧
          (fun p => γ • p) '' nullPlane w = nullPlane (Causal.Flat.isomPenrose γ w)) ∧
      ((Causal.Flat.FutureRegular (Causal.Flat.limitSetJ ρ.range) ∧
          range D = Causal.Flat.omegaPlus (Causal.Flat.limitSetJ ρ.range) ∧
          Causal.Flat.omegaPlus (Causal.Flat.limitSetJ ρ.range) =
            ⋂ w ∈ Causal.Flat.limitSetJ ρ.range, (Causal.minkowski 2).Iplus ⊤ (nullPlane w) ∧
          Causal.Flat.ActsFreelyProperlyOn ρ.range
            (Causal.Flat.omegaPlus (Causal.Flat.limitSetJ ρ.range)) ∧
          (letI := Causal.Flat.flatCoverChartedSpace 2 (e0RegMFlat M) x₀
           haveI := Causal.Flat.hasGroupoid_flatCover (d := 2) (e0RegMFlat M) x₀
           IsFutureComplete
            (Causal.Flat.flatCausality 2 (Causal.UniversalCover (e0RegMFlat M) x₀)) D) ∧
          ∃ (B : Causal.Flat.FlatSpacetime.{0} 2) (π : Causal.Flat.limitOpensPlus ρ.range → B),
            IsCoveringMap π ∧ Causal.Flat.IsLocalIsometry 2 π ∧ Surjective π ∧
            (∀ p q : Causal.Flat.limitOpensPlus ρ.range,
              π p = π q ↔ ∃ γ ∈ ρ.range, γ • (p : Causal.Minkowski 2) = q) ∧
            Causal.Flat.GH B ∧
            ∃ f : e0RegMFlat M ≃ₜ B, Causal.Flat.IsLocalIsometry 2 f ∧
              ∀ z (hz : D z ∈ Causal.Flat.limitOpensPlus ρ.range),
                f (Causal.UniversalCover.proj (e0RegMFlat M) x₀ z) = π ⟨D z, hz⟩) ∨
        (Causal.Flat.PastRegular (Causal.Flat.limitSetJ ρ.range) ∧
          range D = Causal.Flat.omegaMinus (Causal.Flat.limitSetJ ρ.range) ∧
          Causal.Flat.omegaMinus (Causal.Flat.limitSetJ ρ.range) =
            ⋂ w ∈ Causal.Flat.limitSetJ ρ.range, (Causal.minkowski 2).Iminus ⊤ (nullPlane w) ∧
          Causal.Flat.ActsFreelyProperlyOn ρ.range
            (Causal.Flat.omegaMinus (Causal.Flat.limitSetJ ρ.range)) ∧
          ∃ (B : Causal.Flat.FlatSpacetime.{0} 2) (π : Causal.Flat.limitOpensMinus ρ.range → B),
            IsCoveringMap π ∧ Causal.Flat.IsLocalIsometry 2 π ∧ Surjective π ∧
            (∀ p q : Causal.Flat.limitOpensMinus ρ.range,
              π p = π q ↔ ∃ γ ∈ ρ.range, γ • (p : Causal.Minkowski 2) = q) ∧
            Causal.Flat.GH B ∧
            ∃ f : e0RegMFlat M ≃ₜ B, Causal.Flat.IsLocalIsometry 2 f ∧
              ∀ z (hz : D z ∈ Causal.Flat.limitOpensMinus ρ.range),
                f (Causal.UniversalCover.proj (e0RegMFlat M) x₀ z) = π ⟨D z, hz⟩)) := by
  obtain ⟨hGH', hCC', hAM⟩ := cor_abs_max_e0 hGH hCC hmax
  obtain ⟨hlox, hD, hρ, hdisc, htf, hinv, -⟩ := e0RegM_holonomy M hGH' hCC' x₀ hnm D ρ hpair
  obtain ⟨S, hS⟩ := Causal.Flat.exists_developsCC_of_isCauchyComplete' (e0RegMFlat M) hGH' hCC' hpair
  obtain ⟨-, hcase⟩ := uniformization_of_absMax (e0RegMFlat M) hpair hGH'.1 hS hlox hAM
  refine ⟨hlox, hD, hρ, hdisc, htf, hinv, ?_⟩
  rcases hcase with ⟨hF, hr, hfp, hB⟩ | ⟨hP, hr, hfp, hB⟩
  · exact Or.inl ⟨hF, hr, omegaPlus_eq_iInter_Iplus _, hfp,
      isFutureComplete_of_range_eq_omegaPlus (e0RegMFlat M) hpair hD hr, hB⟩
  · exact Or.inr ⟨hP, hr, omegaMinus_eq_iInter_Iminus _, hfp, hB⟩

/-- **The future case is forced by a BTZ line** (DEC-77 (a); SCOPE D-11 (d)): if `M` has a BTZ
point, the developed regular part does not lie in a past regular domain. By Barbot's equality
(`btz_uniformization_reg`) `𝒟(Reg M̃) = Ω⁺(Λ)` or `Ω⁻(Λ)`; the first is disjoint from `Ω⁻(Λ)`
(`Λ ≠ ∅`), the second is past complete, which `false_of_sing_of_pastComplete` refutes. -/
theorem e0RegM_range_not_subset_omegaMinus (hGH : (CE M).GloballyHyperbolic)
    (hCC : E0CauchyCompact M) (hmax : IsE0CauchyMaximal M)
    (hsing : (Causal.CBG.chartedSing e0SingY M 0).Nonempty) (x₀ : e0RegMFlat M)
    (hnm : ¬IsMetabelianGroup (Causal.Deck (Causal.UniversalCover.proj (e0RegMFlat M) x₀)))
    (D : Causal.UniversalCover (e0RegMFlat M) x₀ → Causal.Minkowski 2)
    (ρ : Causal.Deck (Causal.UniversalCover.proj (e0RegMFlat M) x₀) →* Causal.Flat.isom 2)
    (hpair : Causal.Flat.IsDevelopingPair x₀ D ρ) :
    ¬ range D ⊆ Causal.Flat.omegaMinus (Causal.Flat.limitSetJ ρ.range) := by
  intro hsub
  obtain ⟨hlox, hD, -, -, -, -, hcase⟩ :=
    btz_uniformization_reg hGH hCC hmax x₀ hnm D ρ hpair
  rcases hcase with ⟨-, hr, -⟩ | ⟨-, hr, -⟩
  · -- future case: `Ω⁺(Λ) ⊆ Ω⁻(Λ)` is impossible, `Λ ≠ ∅` (the loxodromic's fixed points)
    obtain ⟨γ, hγ, hl⟩ := hlox
    obtain ⟨w, hw, -⟩ := Causal.Flat.exists_two_loxRepSet hγ hl
    have hΛ : (Causal.Flat.limitSetJ ρ.range).Nonempty :=
      ⟨w, Causal.Flat.loxRepSet_subset_limitSetJ _ hw⟩
    set z := Causal.UniversalCover.base x₀
    exact Set.disjoint_left.1 (Causal.Flat.disjoint_omegaPlus_omegaMinus hΛ)
      (hr ▸ mem_range_self z) (hsub (mem_range_self z))
  · -- past case: `𝒟(Reg M̃) = Ω⁻(Λ)` is past complete, which a BTZ point forbids
    exact false_of_sing_of_pastComplete hsing hpair hD fun p z hpz => by
      rw [hr]
      exact Causal.Flat.Jminus_omegaMinus_subset _ ⟨D z, hr ▸ mem_range_self z, hpz⟩

/-- **THE HEADLINE on the regular part, future case** (`theo:globally_hyperbolic_cauchy_complete_cauchy_maximal`,
gx l.2363, in DEC-28's Cauchy-compact form with DEC-76/77): for `M` a globally hyperbolic,
Cauchy-compact, Cauchy-maximal `𝔼₀`-manifold with at least one BTZ point and `π₁(Reg M)` not
metabelian, and every developing pair `(𝒟, ρ)` of `Reg M`: a loxodromic in `ρ(π₁)`; `𝒟`
injective; `ρ` faithful, discrete and torsion-free; the null planes `(Π_w)_{w ∈ Λ}` form a
`ρ(π₁)`-invariant family; `𝒟(Reg M̃) = Ω⁺(Λ) = ⋂_w I⁺(Π_w)` on which `ρ(π₁)` acts freely and
properly discontinuously; `Reg M̃` is future complete; and `𝒟` induces an isometry
`Reg M ≅ ρ(π₁)\Ω⁺(Λ)`. The future case is selected by `e0RegM_range_not_subset_omegaMinus`. -/
theorem btz_uniformization (hGH : (CE M).GloballyHyperbolic) (hCC : E0CauchyCompact M)
    (hmax : IsE0CauchyMaximal M) (hsing : (Causal.CBG.chartedSing e0SingY M 0).Nonempty)
    (x₀ : e0RegMFlat M)
    (hnm : ¬IsMetabelianGroup (Causal.Deck (Causal.UniversalCover.proj (e0RegMFlat M) x₀)))
    (D : Causal.UniversalCover (e0RegMFlat M) x₀ → Causal.Minkowski 2)
    (ρ : Causal.Deck (Causal.UniversalCover.proj (e0RegMFlat M) x₀) →* Causal.Flat.isom 2)
    (hpair : Causal.Flat.IsDevelopingPair x₀ D ρ) :
    (∃ γ ∈ ρ.range, Causal.Flat.IsLoxodromic (Causal.Flat.linOf γ)) ∧ Injective D ∧
      Injective ρ ∧ DiscreteTopology ρ.range ∧ Causal.Flat.IsTorsionFreeSubgroup ρ.range ∧
      (∀ γ ∈ ρ.range, ∀ w ∈ Causal.Flat.limitSetJ ρ.range,
        Causal.Flat.isomPenrose γ w ∈ Causal.Flat.limitSetJ ρ.range ∧
          (fun p => γ • p) '' nullPlane w = nullPlane (Causal.Flat.isomPenrose γ w)) ∧
      Causal.Flat.FutureRegular (Causal.Flat.limitSetJ ρ.range) ∧
      range D = Causal.Flat.omegaPlus (Causal.Flat.limitSetJ ρ.range) ∧
      Causal.Flat.omegaPlus (Causal.Flat.limitSetJ ρ.range) =
        ⋂ w ∈ Causal.Flat.limitSetJ ρ.range, (Causal.minkowski 2).Iplus ⊤ (nullPlane w) ∧
      Causal.Flat.ActsFreelyProperlyOn ρ.range
        (Causal.Flat.omegaPlus (Causal.Flat.limitSetJ ρ.range)) ∧
      (letI := Causal.Flat.flatCoverChartedSpace 2 (e0RegMFlat M) x₀
       haveI := Causal.Flat.hasGroupoid_flatCover (d := 2) (e0RegMFlat M) x₀
       IsFutureComplete
        (Causal.Flat.flatCausality 2 (Causal.UniversalCover (e0RegMFlat M) x₀)) D) ∧
      ∃ (B : Causal.Flat.FlatSpacetime.{0} 2) (π : Causal.Flat.limitOpensPlus ρ.range → B),
        IsCoveringMap π ∧ Causal.Flat.IsLocalIsometry 2 π ∧ Surjective π ∧
        (∀ p q : Causal.Flat.limitOpensPlus ρ.range,
          π p = π q ↔ ∃ γ ∈ ρ.range, γ • (p : Causal.Minkowski 2) = q) ∧
        Causal.Flat.GH B ∧
        ∃ f : e0RegMFlat M ≃ₜ B, Causal.Flat.IsLocalIsometry 2 f ∧
          ∀ z (hz : D z ∈ Causal.Flat.limitOpensPlus ρ.range),
            f (Causal.UniversalCover.proj (e0RegMFlat M) x₀ z) = π ⟨D z, hz⟩ := by
  obtain ⟨hlox, hD, hρ, hdisc, htf, hinv, hcase⟩ :=
    btz_uniformization_reg hGH hCC hmax x₀ hnm D ρ hpair
  rcases hcase with ⟨hF, hr, hI, hfp, hfc, hB⟩ | ⟨-, hr, -⟩
  · exact ⟨hlox, hD, hρ, hdisc, htf, hinv, hF, hr, hI, hfp, hfc, hB⟩
  · exact absurd hr.subset
      (e0RegM_range_not_subset_omegaMinus hGH hCC hmax hsing x₀ hnm D ρ hpair)

/-- **`prop:globally_hyperbolic_cauchy_complete_manifolds` (l.2348), corrected (DEC-77), on the regular
part**: a globally hyperbolic, Cauchy-compact, Cauchy-maximal `𝔼₀`-manifold with a BTZ point and
`π₁(Reg M)` not metabelian has its regular part future complete: for every developing pair of
`Reg M` and every `z ∈ Reg M̃`, `𝒟(J⁺(z)) = J⁺(𝒟 z)` and `𝒟(I⁺(z)) = I⁺(𝒟 z)` (the first step of
the paper's proof, l.2350). -/
theorem btz_reg_isFutureComplete (hGH : (CE M).GloballyHyperbolic) (hCC : E0CauchyCompact M)
    (hmax : IsE0CauchyMaximal M) (hsing : (Causal.CBG.chartedSing e0SingY M 0).Nonempty)
    (x₀ : e0RegMFlat M)
    (hnm : ¬IsMetabelianGroup (Causal.Deck (Causal.UniversalCover.proj (e0RegMFlat M) x₀)))
    (D : Causal.UniversalCover (e0RegMFlat M) x₀ → Causal.Minkowski 2)
    (ρ : Causal.Deck (Causal.UniversalCover.proj (e0RegMFlat M) x₀) →* Causal.Flat.isom 2)
    (hpair : Causal.Flat.IsDevelopingPair x₀ D ρ) :
    letI := Causal.Flat.flatCoverChartedSpace 2 (e0RegMFlat M) x₀
    haveI := Causal.Flat.hasGroupoid_flatCover (d := 2) (e0RegMFlat M) x₀
    IsFutureComplete (Causal.Flat.flatCausality 2 (Causal.UniversalCover (e0RegMFlat M) x₀)) D :=
  (btz_uniformization hGH hCC hmax hsing x₀ hnm D ρ hpair).2.2.2.2.2.2.2.2.2.2.1

end E0

/-! ## §4b The counterexample `{τ<0} ⊂ 𝔼₀` to the printed proposition (D-11, DEC-77) -/

section PastHalf

open TopologicalSpace E0CBG E0Spear E0AbsMax
open scoped Causal.Flat

/-- **The past half `{τ < 0}` of `𝔼₀`** (D-11's counterexample), an open subset of `Y = 𝕄 ⊕ 𝔼₀`,
hence an `𝔼₀`-manifold (`Opens`' charted structure; Hausdorff, second countable, connected). -/
noncomputable def e0PastHalf : Opens E0Y :=
  ⟨E0.paperInY '' {w : E0 | w.1 < 0},
    E0.paperInY.isOpen_image_of_subset_source (isOpen_lt continuous_fst continuous_const)
      (by simp)⟩

/-- A point of `Y` lies in `{τ<0}` iff it is in the `𝔼₀` part with paper time `τ < 0`. -/
theorem mem_e0PastHalf_iff {y : E0Y} :
    y ∈ e0PastHalf ↔ y ∈ E0.paperOfY.source ∧ (E0.paperOfY y).1 < 0 := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨by rw [E0.paperOfY_source]; exact ⟨_, rfl⟩, ?_⟩
    simpa using hw
  · rintro ⟨hs, hy⟩
    rw [E0.paperOfY_source] at hs
    obtain ⟨x, rfl⟩ := hs
    refine ⟨E0.toPaper x, ?_, ?_⟩
    · simpa using hy
    · simp

/-- `{τ<0}` is connected (the image of a half-space of `ℝ × ℂ`). -/
instance e0PastHalf_connectedSpace : ConnectedSpace e0PastHalf := by
  have hc : IsConnected {w : E0 | w.1 < 0} := by
    refine ⟨⟨(-1, 0), by norm_num⟩, ?_⟩
    exact (convex_halfSpace_lt (f := fun w : E0 => w.1) ⟨fun _ _ => rfl, fun _ _ => rfl⟩ 0).isPreconnected
  have := hc.image _ (E0.paperInY.continuousOn.mono (by simp))
  exact isConnected_iff_connectedSpace.1 this

/-- On `{τ<0}`, every paper chart is defined everywhere. -/
theorem chartSource_paperChart_pastHalf (x : e0PastHalf) :
    Causal.chartSource (paperChart x) = ⊤ := by
  ext a
  simp only [Causal.coe_chartSource, paperChart, OpenPartialHomeomorph.trans_source]
  refine iff_of_true ⟨?_, ?_⟩ trivial
  · show a ∈ ((chartAt E0Y (x : E0Y)).subtypeRestr ⟨x⟩).source
    rw [OpenPartialHomeomorph.subtypeRestr_source]; exact trivial
  · show ((chartAt E0Y (x : E0Y)).subtypeRestr ⟨x⟩ a) ∈ E0.paperOfY.source
    rw [OpenPartialHomeomorph.subtypeRestr_coe]
    exact (mem_e0PastHalf_iff.1 a.2).1


/-- A chronological relation of `{τ<0}` is one of `𝔼₀` in the paper's coordinates. -/
theorem pastHalf_lt_paper {a b : e0PastHalf} (h : (CE e0PastHalf).lt ⊤ a b) :
    ∃ U, E0.causality.lt U (E0.paperOfY a) (E0.paperOfY b) := by
  have hU : (⊤ : Opens e0PastHalf) ≤ Causal.chartSource (paperChart a) := by
    rw [chartSource_paperChart_pastHalf]
  exact ⟨_, ((chartIso_paperChart a ⊤ hU a trivial b trivial).2).1 h⟩

/-- The paper coordinates of the base point of `z ∈ Reg {τ<0}~`. -/
noncomputable def pastHalfPaper {x₀ : e0RegMFlat e0PastHalf}
    (z : Causal.UniversalCover (e0RegMFlat e0PastHalf) x₀) : E0 :=
  E0.paperOfY (show E0LM.e0RegM e0PastHalf from
    Causal.UniversalCover.proj (e0RegMFlat e0PastHalf) x₀ z).1.1

/-- The base point of a point of `Reg {τ<0}~` has `τ < 0`. -/
theorem pastHalfPaper_fst_neg {x₀ : e0RegMFlat e0PastHalf}
    (z : Causal.UniversalCover (e0RegMFlat e0PastHalf) x₀) : (pastHalfPaper z).1 < 0 :=
  (mem_e0PastHalf_iff.1 (show E0LM.e0RegM e0PastHalf from
    Causal.UniversalCover.proj (e0RegMFlat e0PastHalf) x₀ z).1.2).2

/-- **A chronological relation of `Reg {τ<0}~` is one of `𝔼₀`** (through `Reg {τ<0}`, its
`𝔼₀` causality `flatCausality_e0RegM_eq`, the inclusion into `{τ<0}`, and the paper chart). -/
theorem pastHalf_cover_lt {x₀ : e0RegMFlat e0PastHalf}
    {z w : Causal.UniversalCover (e0RegMFlat e0PastHalf) x₀}
    (h : letI := Causal.Flat.flatCoverChartedSpace 2 (e0RegMFlat e0PastHalf) x₀
      haveI := Causal.Flat.hasGroupoid_flatCover (d := 2) (e0RegMFlat e0PastHalf) x₀
      (Causal.Flat.flatCausality 2 (Causal.UniversalCover (e0RegMFlat e0PastHalf) x₀)).lt ⊤ z w) :
    ∃ U, E0.causality.lt U (pastHalfPaper z) (pastHalfPaper w) := by
  letI := Causal.Flat.flatCoverChartedSpace 2 (e0RegMFlat e0PastHalf) x₀
  haveI := Causal.Flat.hasGroupoid_flatCover (d := 2) (e0RegMFlat e0PastHalf) x₀
  have h1 := (Causal.Flat.isLocalIsometry_flatCover_proj (d := 2) x₀).strongMorphism.map_lt ⊤ ⊤
    rfl h
  have h2 : (CE (E0LM.e0RegM e0PastHalf)).lt ⊤
      (Causal.UniversalCover.proj (e0RegMFlat e0PastHalf) x₀ z)
      (Causal.UniversalCover.proj (e0RegMFlat e0PastHalf) x₀ w) := by
    rw [← flatCausality_e0RegM_eq]; exact h1
  have hval : Causal.IsEMorphism (CE (E0LM.e0RegM e0PastHalf)) (CE e0PastHalf) Subtype.val :=
    isEMorphismOn_of_isE0Mor (W := ⊤) (isE0Mor_val _)
  have h3 := (Causal.isEMorphism_iff.1 hval).1.map_lt ⊤ ⊤ rfl h2
  exact pastHalf_lt_paper h3


section PastHalfGH

/-- `paperOfY ∘ paperInY = id`. -/
theorem pastHalf_paperOfY_paperInY (w : E0) : E0.paperOfY (E0.paperInY w) = w := by simp

/-- `paperInY ∘ paperOfY = id` on the `𝔼₀` part. -/
theorem pastHalf_paperInY_paperOfY {y : E0Y} (hy : y ∈ E0.paperOfY.source) :
    E0.paperInY (E0.paperOfY y) = y := by
  rw [E0.paperOfY_source] at hy
  obtain ⟨x, rfl⟩ := hy
  simp

/-- The chart image of `{τ<0}` in the paper's coordinates is `{τ < 0}`. -/
theorem mem_chartImage_paperChart_pastHalf (p : e0PastHalf) (w : E0) :
    w ∈ Causal.chartImage (paperChart p) ⊤ ↔ w.1 < 0 := by
  rw [← SetLike.mem_coe, Causal.coe_chartImage_of_le (by rw [chartSource_paperChart_pastHalf])]
  constructor
  · rintro ⟨a, -, rfl⟩
    exact (mem_e0PastHalf_iff.1 a.2).2
  · intro hw
    refine ⟨⟨E0.paperInY w, w, hw, rfl⟩, trivial, ?_⟩
    show E0.paperOfY (E0.paperInY w) = w
    exact pastHalf_paperOfY_paperInY w

/-- A causal relation of `𝔼₀` ending in `{τ<0}` is one of any open set containing `{τ<0}` (a future
causal curve has `τ` non-decreasing). -/
theorem e0_le_of_le_top_of_fst_neg {U : Opens E0} (hU : ∀ w : E0, w.1 < 0 → w ∈ U) {x y : E0}
    (h : E0.causality.le ⊤ x y) (hy : y.1 < 0) : E0.causality.le U x y := by
  obtain ⟨a, b, hab, c, hc, rfl, rfl⟩ := h
  refine ⟨a, b, hab, c, ⟨fun t ht => hU _ ?_, fun t ht N _ hN => hc.rel t ht N le_top hN⟩, rfl, rfl⟩
  rcases ht.2.lt_or_eq with htb | rfl
  · have := (hc.rel_of_lt E0.isRelFamily_le ht.1 htb le_rfl).2.2
    exact this.closed.1.trans_lt hy
  · exact hy

/-- **The causal relation of `{τ<0}` is that of `𝔼₀`** in the paper's coordinates. -/
theorem pastHalf_le_iff (p : e0PastHalf) {a b : e0PastHalf} :
    (CE e0PastHalf).le ⊤ a b ↔ E0.Le (E0.paperOfY a) (E0.paperOfY b) := by
  have hU : (⊤ : Opens e0PastHalf) ≤ Causal.chartSource (paperChart p) := by
    rw [chartSource_paperChart_pastHalf]
  rw [((chartIso_paperChart p ⊤ hU a trivial b trivial).1)]
  constructor
  · intro h; exact E0.CLe.le h
  · intro h
    exact e0_le_of_le_top_of_fst_neg (fun w hw => (mem_chartImage_paperChart_pastHalf p w).2 hw)
      (E0.le_top_iff.2 h) (mem_e0PastHalf_iff.1 b.2).2

/-- **`{τ<0}` is globally hyperbolic** (D-11's first hypothesis): its charted causality is that of
`𝔼₀` restricted to `{τ<0}` (`pastHalf_le_iff`), `𝔼₀` is causal, and a diamond is the closed set
`J⁺(p) ∩ J⁻(q)` of `𝔼₀`, bounded by `dist ≤ 3Δτ` (`E0.Le.dist_le`). -/
theorem e0PastHalf_globallyHyperbolic : (CE e0PastHalf).GloballyHyperbolic := by
  refine ⟨fun a b hab hba => ?_, fun p q => ?_⟩
  · have h1 := (pastHalf_le_iff a).1 hab
    have h2 := (pastHalf_le_iff a).1 hba
    have := E0.isCausal (E0.le_top_iff.2 h1) (E0.le_top_iff.2 h2)
    apply Subtype.ext
    rw [← pastHalf_paperInY_paperOfY (mem_e0PastHalf_iff.1 a.2).1,
      ← pastHalf_paperInY_paperOfY (mem_e0PastHalf_iff.1 b.2).1, this]
  · set P := E0.paperOfY p
    set Q := E0.paperOfY q
    set K : Set E0 := E0.causality.Jplus ⊤ {P} ∩ E0.causality.Jminus ⊤ {Q}
    have hK : IsCompact K := by
      refine Metric.isCompact_of_isClosed_isBounded
        ((E0.isClosed_Jplus P).inter (E0.isClosed_Jminus Q)) ?_
      refine (Metric.isBounded_closedBall (x := P) (r := 3 * (Q.1 - P.1))).subset ?_
      rintro w ⟨hw1, hw2⟩
      rw [Causal.Precausality.mem_Jplus_singleton, E0.le_top_iff] at hw1
      rw [Causal.Precausality.mem_Jminus_singleton, E0.le_top_iff] at hw2
      rw [Metric.mem_closedBall, dist_comm]
      have := hw1.dist_le
      have := hw2.closed.1
      linarith
    rw [Subtype.isCompact_iff]
    have himg : ((↑) : e0PastHalf → E0Y) '' (CE e0PastHalf).diamond ⊤ p q = E0.paperInY '' K := by
      ext y
      constructor
      · rintro ⟨a, ⟨haq, hpa⟩, rfl⟩
        rw [Causal.Precausality.mem_Jminus_singleton, pastHalf_le_iff p] at haq
        rw [Causal.Precausality.mem_Jplus_singleton, pastHalf_le_iff p] at hpa
        refine ⟨E0.paperOfY a, ⟨?_, ?_⟩, pastHalf_paperInY_paperOfY (mem_e0PastHalf_iff.1 a.2).1⟩
        · rw [Causal.Precausality.mem_Jplus_singleton, E0.le_top_iff]; exact hpa
        · rw [Causal.Precausality.mem_Jminus_singleton, E0.le_top_iff]; exact haq
      · rintro ⟨w, ⟨hw1, hw2⟩, rfl⟩
        rw [Causal.Precausality.mem_Jplus_singleton, E0.le_top_iff] at hw1
        rw [Causal.Precausality.mem_Jminus_singleton, E0.le_top_iff] at hw2
        have hw : w.1 < 0 := hw2.closed.1.trans_lt (mem_e0PastHalf_iff.1 q.2).2
        have hmem : E0.paperInY w ∈ e0PastHalf := ⟨w, hw, rfl⟩
        refine ⟨⟨_, hmem⟩, ⟨?_, ?_⟩, rfl⟩
        · rw [Causal.Precausality.mem_Jminus_singleton, pastHalf_le_iff p]
          show E0.Le (E0.paperOfY (E0.paperInY w)) Q
          rw [pastHalf_paperOfY_paperInY]; exact hw2
        · rw [Causal.Precausality.mem_Jplus_singleton, pastHalf_le_iff p]
          show E0.Le P (E0.paperOfY (E0.paperInY w))
          rw [pastHalf_paperOfY_paperInY]; exact hw1
    rw [himg]
    exact hK.image_of_continuousOn (E0.paperInY.continuousOn.mono (by simp))

/-- `{τ<0}` has BTZ points (`s ≥ 1`): the axis point `(−1, 0)`. -/
theorem e0PastHalf_sing_nonempty : (Causal.CBG.chartedSing e0SingY e0PastHalf 0).Nonempty := by
  have hmem : E0.paperInY ((-1, 0) : E0) ∈ e0PastHalf := ⟨_, by norm_num, rfl⟩
  refine ⟨⟨_, hmem⟩, ?_⟩
  show E0.paperInY ((-1, 0) : E0) ∈ e0SingY 0
  refine ⟨rfl, ?_⟩
  rw [E0.paperInY_apply, inr_mem_e0Reg_iff, E0.mem_reg_iff_toPaper,
    Homeomorph.apply_symm_apply, not_not]
  rfl

end PastHalfGH

section AeChartLocal

open Filter Topology
open scoped Real
attribute [local instance] btzE0Structure

/-- Near a point of its source, a chart of `BTZE0`'s maximal a.e. atlas is `g •` the sector chart
`chartMap` (the step of `E0.chartIso_aeAtlas`). -/
theorem pastHalf_aeChart_eventually {c : OpenPartialHomeomorph BTZE0 (Causal.Minkowski 2)}
    (hc : c ∈ aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) {x : BTZE0}
    (hx : x ∈ c.source) :
    ∃ g : Causal.Flat.isom 2, ∀ᶠ z in 𝓝 x,
      c z = g • E0.chartMap (E0.toPaper x) (E0.toPaper z) := by
  set y := E0.toPaper x
  have hxr : x ∈ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0 :=
    mem_support.2 ⟨c, hc, hx⟩
  have hyax : y ∉ E0.axis := (E0.mem_reg_iff_toPaper x).1 hxr
  have hy : y.2 ≠ 0 := hyax
  set p : ℝ × ℝ × ℝ := (y.1, E0.rad y, E0.angle y y)
  have hpx : orbitMk (GammaA (2 * π)) (btzPaperCyl p) = x := by
    rw [← E0.toPaper_symm_eq_orbitMk hyax (E0.polar_angle hy y), Homeomorph.symm_apply_apply]
  obtain ⟨g, hg⟩ := btz_chart_eq_smul_btzPaperDev isBTZStructure_btzE0 hc
    (p := p) (E0.rad_pos.2 hyax) (by rw [hpx]; exact hx)
  set φ : BTZE0 → ℝ × ℝ × ℝ := fun z =>
    ((E0.toPaper z).1, E0.rad (E0.toPaper z), E0.angle y (E0.toPaper z))
  have hφ : ContinuousAt φ x := by
    have hang : ContinuousAt (E0.angle y) y :=
      (E0.continuousOn_angle y).continuousAt ((E0.isOpen_sector y).mem_nhds (E0.mem_sector_self hy))
    have h3 : ContinuousAt (fun z => E0.angle y (E0.toPaper z)) x :=
      ContinuousAt.comp (g := E0.angle y) (f := E0.toPaper) hang E0.toPaper.continuous.continuousAt
    exact (continuous_fst.comp E0.toPaper.continuous).continuousAt.prodMk
      ((E0.continuous_rad.comp E0.toPaper.continuous).continuousAt.prodMk h3)
  have h1 : ∀ᶠ z in 𝓝 x, c (orbitMk (GammaA (2 * π)) (btzPaperCyl (φ z))) =
      g • btzPaperDev (φ z) := hφ.eventually hg
  have h2 : ∀ᶠ z in 𝓝 x, E0.toPaper z ∈ E0.sector y :=
    E0.toPaper.continuous.continuousAt.preimage_mem_nhds
      ((E0.isOpen_sector y).mem_nhds (E0.mem_sector_self hy))
  refine ⟨g, ?_⟩
  filter_upwards [h1, h2] with z hz1 hz2
  have hzax : E0.toPaper z ∉ E0.axis := E0.not_mem_axis_of_mem_sector hz2
  have hz : orbitMk (GammaA (2 * π)) (btzPaperCyl (φ z)) = z := by
    rw [← E0.toPaper_symm_eq_orbitMk hzax (E0.polar_angle hy (E0.toPaper z)),
      Homeomorph.symm_apply_apply]
  rw [hz] at hz1
  rw [hz1, E0.chartMap_eq]

end AeChartLocal

/-- The null functional `t − x` of `𝐌³`; it reads `r` off the paper's developing map. -/
noncomputable def minkTMinusX : Causal.Minkowski 2 →ₗ[ℝ] ℝ :=
  LinearMap.fst ℝ ℝ _ -
    ((EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) : _ →ₗ[ℝ] ℝ) ∘ₗ
      LinearMap.snd ℝ ℝ _

/-- `t − x` of the paper's developing map is `r`. -/
theorem minkTMinusX_btzPaperDev (p : ℝ × ℝ × ℝ) : minkTMinusX (btzPaperDev p) = p.2.1 := by
  simp [minkTMinusX, btzPaperDev]

/-- `t − x` of a sector chart is `r`. -/
theorem minkTMinusX_chartMap (y w : E0) : minkTMinusX (E0.chartMap y w) = E0.rad w := by
  rw [E0.chartMap_eq, minkTMinusX_btzPaperDev]


section AffineLocal

open Filter Topology

/-- **A locally affine reading through an open map is globally affine** on a preconnected space:
if near every point `F = a ∘ D` for some affine `a`, one `a` works everywhere (two affine maps
agreeing on the non-empty open `D(t)` are equal). -/
theorem exists_affine_eq_of_locally {X E : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {D : X → E} (hD : IsOpenMap D) {F : X → ℝ}
    (h : ∀ x, ∃ a : E →ᵃ[ℝ] ℝ, ∀ᶠ y in 𝓝 x, F y = a (D y)) :
    ∃ a : E →ᵃ[ℝ] ℝ, ∀ y, F y = a (D y) := by
  have huniq : ∀ (x : X) (a a' : E →ᵃ[ℝ] ℝ), (∀ᶠ y in 𝓝 x, F y = a (D y)) →
      (∀ᶠ y in 𝓝 x, F y = a' (D y)) → a = a' := by
    intro x a a' h1 h2
    obtain ⟨t, ht, hto, hxt⟩ := eventually_nhds_iff.1 (h1.and h2)
    refine AffineMap.ext_on ((hD t hto).affineSpan_eq_top ⟨D x, x, hxt, rfl⟩) ?_
    rintro _ ⟨y, hy, rfl⟩
    exact (ht y hy).1.symm.trans (ht y hy).2
  choose A hA using h
  have hlc : IsLocallyConstant A := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    filter_upwards [(hA x).eventually_nhds] with y hy
    exact huniq y _ _ (hA y) hy
  cases isEmpty_or_nonempty X with
  | inl _ => exact ⟨0, fun y => isEmptyElim y⟩
  | inr hne =>
    obtain ⟨x₀⟩ := hne
    refine ⟨A x₀, fun y => ?_⟩
    rw [← hlc.apply_eq_of_preconnectedSpace y x₀]
    exact (hA y).self_of_nhds

end AffineLocal


section PastHalfRad

open Filter Topology

/-- **`r` is locally affine in `𝒟` on `Reg {τ<0}~`**: near every point, `r = a ∘ 𝒟` with `a` affine
(`r = t − x` on the paper's developing map, and every flat chart is `g •` it). -/
theorem pastHalf_rad_locally {x₀ : e0RegMFlat e0PastHalf}
    {D : Causal.UniversalCover (e0RegMFlat e0PastHalf) x₀ → Causal.Minkowski 2}
    {ρ : Causal.Deck (Causal.UniversalCover.proj (e0RegMFlat e0PastHalf) x₀) →* Causal.Flat.isom 2}
    (hpair : Causal.Flat.IsDevelopingPair x₀ D ρ)
    (z : Causal.UniversalCover (e0RegMFlat e0PastHalf) x₀) :
    ∃ a : Causal.Minkowski 2 →ᵃ[ℝ] ℝ, ∀ᶠ w in 𝓝 z, E0.rad (pastHalfPaper w) = a (D w) := by
  letI := Causal.Flat.flatCoverChartedSpace 2 (e0RegMFlat e0PastHalf) x₀
  haveI := Causal.Flat.hasGroupoid_flatCover (d := 2) (e0RegMFlat e0PastHalf) x₀
  have hDl : Causal.Flat.IsLocalIsometry 2 D :=
    Causal.Flat.isLocalIsometry_iff_eventually.2 ⟨hpair.gx.1, hpair.gx.2⟩
  obtain ⟨g2, hg2⟩ := (Causal.Flat.isLocalIsometry_iff_eventually.1 hDl).2 z
  have hpl := Causal.Flat.isLocalIsometry_flatCover_proj (d := 2) (M := e0RegMFlat e0PastHalf) x₀
  obtain ⟨g1, hg1⟩ := (Causal.Flat.isLocalIsometry_iff_eventually.1 hpl).2 z
  set q := Causal.UniversalCover.proj (e0RegMFlat e0PastHalf) x₀ with hq
  set y : E0LM.e0RegM e0PastHalf := q z
  set pt : Causal.UniversalCover (e0RegMFlat e0PastHalf) x₀ → E0Y :=
    fun w => (show E0LM.e0RegM e0PastHalf from q w).1.1 with hpt
  have hptc : Continuous pt :=
    continuous_subtype_val.comp (continuous_subtype_val.comp hpl.continuous)
  have hrange : ∀ w, pt w ∈ range Sum.inr := fun w => by
    rw [← E0.paperOfY_source]
    exact (mem_e0PastHalf_iff.1 (show E0LM.e0RegM e0PastHalf from q w).1.2).1
  obtain ⟨x, hx⟩ := hrange z
  have hsrc : Sum.inr x ∈ (E0LM.regAtlasChart y).source := by
    rw [hx]; exact E0LM.mem_regAtlasChart_source y
  obtain ⟨c', hc', hceq, hxc⟩ := exists_of_mem_e0Atlas_inr (E0LM.regAtlasChart_mem y) hsrc
  obtain ⟨g, hg⟩ := pastHalf_aeChart_eventually hc' hxc
  set φ := fun w => e0Inr.symm (pt w) with hφ
  have hφz : φ z = x := by simp only [hφ, ← hx, e0Inr_symm_inr]
  have hφc : ContinuousAt φ z := by
    refine ContinuousAt.comp (g := e0Inr.symm) ?_ hptc.continuousAt
    exact e0Inr.symm.continuousAt (by rw [e0Inr_symm_source]; exact hrange z)
  have hgφ : ∀ᶠ w in 𝓝 z, c' (φ w) = g • E0.chartMap (E0.toPaper x) (E0.toPaper (φ w)) :=
    hφc.preimage_mem_nhds (t := {u | c' u = g • E0.chartMap (E0.toPaper x) (E0.toPaper u)})
      (by rw [hφz]; exact hg)
  set h := g2 * g1⁻¹ * g
  refine ⟨minkTMinusX.toAffineMap.comp
    ((h⁻¹ : Causal.Flat.isom 2) : Causal.Minkowski 2 ≃ᵃ[ℝ] Causal.Minkowski 2).toAffineMap, ?_⟩
  filter_upwards [hg2, hg1, hgφ] with w h2 h1 h0
  have hchart : (chartAt (Causal.Minkowski 2) (q z)) (q w) = c' (φ w) := by
    show ((E0LM.regChartM y).subtypeRestr ⟨y⟩) (q w) = _
    rw [regChart_subtypeRestr_eq, hceq]
    rfl
  have hpap : E0.toPaper (φ w) = pastHalfPaper w := rfl
  have hDw : D w = h • E0.chartMap (E0.toPaper x) (pastHalfPaper w) := by
    rw [chartAt_self_eq, OpenPartialHomeomorph.refl_apply, id] at h2
    rw [hchart, h0, hpap] at h1
    have h1' : (chartAt (Causal.Minkowski 2) z) w =
        g1⁻¹ • g • E0.chartMap (E0.toPaper x) (pastHalfPaper w) := by
      rw [h1, inv_smul_smul]
    rw [h2, h1', ← mul_smul, ← mul_smul]
  show E0.rad (pastHalfPaper w) =
    minkTMinusX (((h⁻¹ : Causal.Flat.isom 2) : Causal.Minkowski 2 ≃ᵃ[ℝ] Causal.Minkowski 2) (D w))
  rw [← Causal.Flat.isom_smul_def, hDw, inv_smul_smul, minkTMinusX_chartMap]


/-- **The past half `{τ<0}` of `𝔼₀` is not future complete** (D-11, DEC-77; the conclusion of
`prop:globally_hyperbolic_cauchy_complete_manifolds` fails on `Reg {τ<0}`): for **every** developing
pair `(𝒟, ρ)` of `Reg {τ<0}` and every `z`, `𝒟(I⁺(z)) ≠ I⁺(𝒟 z)`. Globally `r = a ∘ 𝒟` with `a`
affine (`pastHalf_rad_locally`, `exists_affine_eq_of_locally`); along `I⁺(z)`, `r` increases strictly
and stays below `r(z) − 2τ(z)` (`E0.calculus_lt`, `τ < 0`), while `a(𝒟 z + t e₀)` is affine in `t`. -/
theorem e0PastHalf_not_isFutureComplete {x₀ : e0RegMFlat e0PastHalf}
    {D : Causal.UniversalCover (e0RegMFlat e0PastHalf) x₀ → Causal.Minkowski 2}
    {ρ : Causal.Deck (Causal.UniversalCover.proj (e0RegMFlat e0PastHalf) x₀) →* Causal.Flat.isom 2}
    (hpair : Causal.Flat.IsDevelopingPair x₀ D ρ)
    (z : Causal.UniversalCover (e0RegMFlat e0PastHalf) x₀) :
    letI := Causal.Flat.flatCoverChartedSpace 2 (e0RegMFlat e0PastHalf) x₀
    haveI := Causal.Flat.hasGroupoid_flatCover (d := 2) (e0RegMFlat e0PastHalf) x₀
    D '' (Causal.Flat.flatCausality 2 (Causal.UniversalCover (e0RegMFlat e0PastHalf) x₀)).Iplus ⊤
      {z} ≠ (Causal.minkowski 2).Iplus ⊤ {D z} := by
  letI := Causal.Flat.flatCoverChartedSpace 2 (e0RegMFlat e0PastHalf) x₀
  haveI := Causal.Flat.hasGroupoid_flatCover (d := 2) (e0RegMFlat e0PastHalf) x₀
  have hDl : Causal.Flat.IsLocalIsometry 2 D :=
    Causal.Flat.isLocalIsometry_iff_eventually.2 ⟨hpair.gx.1, hpair.gx.2⟩
  obtain ⟨a, ha⟩ := exists_affine_eq_of_locally hDl.isOpenMap (pastHalf_rad_locally hpair)
  intro hfc
  set e : Causal.Minkowski 2 := ((1 : ℝ), 0)
  have key : ∀ t : ℝ, 0 < t → E0.rad (pastHalfPaper z) < E0.rad (pastHalfPaper z) + t * a.linear e ∧
      E0.rad (pastHalfPaper z) + t * a.linear e <
        E0.rad (pastHalfPaper z) - 2 * (pastHalfPaper z).1 := by
    intro t ht
    have hq : D z + t • e ∈ (Causal.minkowski 2).Iplus ⊤ {D z} := by
      rw [Causal.Precausality.mem_Iplus_singleton, Causal.minkowski_lt_top_iff]
      simp [e, ht]
    rw [← hfc] at hq
    obtain ⟨w, hw, hDw⟩ := hq
    rw [Causal.Precausality.mem_Iplus_singleton] at hw
    obtain ⟨U, hU⟩ := pastHalf_cover_lt hw
    obtain ⟨hr, -, -, hf, -⟩ := E0.calculus_lt hU
    have hneg := pastHalfPaper_fst_neg w
    have hrw : E0.rad (pastHalfPaper w) = E0.rad (pastHalfPaper z) + t * a.linear e := by
      rw [ha w, ha z, hDw, add_comm (D z), ← vadd_eq_add, a.map_vadd, vadd_eq_add,
        a.linear.map_smul, smul_eq_mul, add_comm]
    rw [← hrw]
    refine ⟨hr, ?_⟩
    simp only [E0.fcoord] at hf
    linarith
  have hℓ : 0 < a.linear e := by
    have := (key 1 one_pos).1; linarith
  have hτ := pastHalfPaper_fst_neg z
  have := (key (-2 * (pastHalfPaper z).1 / a.linear e + 1) (by
    have : 0 < -2 * (pastHalfPaper z).1 / a.linear e := div_pos (by linarith) hℓ
    linarith)).2
  rw [add_mul, div_mul_cancel₀ _ hℓ.ne'] at this
  linarith

/-- **D-11's counterexample to `prop:globally_hyperbolic_cauchy_complete_manifolds` as printed**
(DEC-27, DEC-77): the past half `{τ<0}` of `𝔼₀` is a globally hyperbolic `𝔼₀`-manifold with BTZ
points (`s ≥ 1`), and the conclusion of the corrected proposition (`btz_reg_isFutureComplete`)
fails on it: for **every** developing pair `(𝒟, ρ)` of `Reg {τ<0}` and **every** `z ∈ Reg {τ<0}~`,
`𝒟(I⁺(z)) ≠ I⁺(𝒟 z)`; in particular `Reg {τ<0}~` is not future complete. Its Cauchy surface
`{τ = −1}` carries the flat complete metric `dr² + r²dθ²` (DEC-31's Cauchy-completeness of the
paper's hypothesis; not stated here, see SCOPE (c)). It is neither Cauchy-compact nor
Cauchy-maximal (`{τ<0} ⊂ 𝔼₀` is a Cauchy embedding), and `π₁(Reg {τ<0}) ≅ ℤ`. -/
theorem e0PastHalf_counterexample :
    (CE e0PastHalf).GloballyHyperbolic ∧ (Causal.CBG.chartedSing e0SingY e0PastHalf 0).Nonempty ∧
      ∀ (x₀ : e0RegMFlat e0PastHalf)
        (D : Causal.UniversalCover (e0RegMFlat e0PastHalf) x₀ → Causal.Minkowski 2)
        (ρ : Causal.Deck (Causal.UniversalCover.proj (e0RegMFlat e0PastHalf) x₀) →*
          Causal.Flat.isom 2),
        Causal.Flat.IsDevelopingPair x₀ D ρ →
          letI := Causal.Flat.flatCoverChartedSpace 2 (e0RegMFlat e0PastHalf) x₀
          haveI := Causal.Flat.hasGroupoid_flatCover (d := 2) (e0RegMFlat e0PastHalf) x₀
          ¬ IsFutureComplete
            (Causal.Flat.flatCausality 2 (Causal.UniversalCover (e0RegMFlat e0PastHalf) x₀)) D :=
  ⟨e0PastHalf_globallyHyperbolic, e0PastHalf_sing_nonempty, fun x₀ _ _ hpair hfc =>
    e0PastHalf_not_isFutureComplete hpair (Causal.UniversalCover.base x₀) (hfc _).2⟩

end PastHalfRad

end PastHalf

/-! ## §5 `M̃` with `T_BTZ`: the injectivity step on the maximal branched covering -/

section TildeM

universe v

attribute [local instance] btzE0Structure

variable {M : Type v} [TopologicalSpace M] [T2Space M] [LocPathConnectedSpace M]
  [FirstCountableTopology M] [ConnectedSpace M]
  [SingularGXStructure (Causal.Flat.isom 2) (Causal.Minkowski 2) M]
  {y₀ : ((Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M)ᶜ : Set M)}
  {yN : ((Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0)ᶜ : Set BTZE0)}
  {Φ : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) yN ≃ₜ DInfty × ℝ}

/-- **`𝒟` is injective on `M̃`** (the headline's first bullet, the step l.2392–2394 on the maximal
branched covering with `T_BTZ`, DEC-77 (b)): if `M` is globally hyperbolic, `M` future complete
(`def:manifold_future_complete_all`, the conclusion of
`prop:globally_hyperbolic_cauchy_complete_manifolds`), `𝒟` injective on `reg M̃` (Barbot) and every
`I⁺(x)` regular (B21: a BTZ point is not in the chronological future of anything), then `𝒟` is
injective on `M̃`. Future distinguishing is `BTZTildeData.isFutureDistinguishing_of_base`. -/
theorem BTZTildeData.injective_D_of_isBTZFutureComplete (d : BTZTildeData M y₀ Φ)
    (hM : IsBTZSingModelled M) (hG : (e0ManifoldCausality M hM).GloballyHyperbolic)
    (hfc : BTZTildeData.IsBTZFutureComplete M d)
    (hreg : InjOn d.D {e | e.base ∈ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) M})
    (hI : ∀ x : d.Space, d.causality.Iplus ⊤ {x} ⊆
      {e | e.base ∈ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) M}) :
    Injective d.D :=
  injective_of_isFutureComplete (N := d.Space) hfc hreg hI (d.isFutureDistinguishing_of_base hM hG)

end TildeM

end GX
