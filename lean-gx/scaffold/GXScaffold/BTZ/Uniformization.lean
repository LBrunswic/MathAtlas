import GXScaffold.BTZ.AbsMax
import GXScaffold.BTZ.Manifolds
import Causal.Flat.Lox.PastProper

/-!
# `GXScaffold.BTZ.Uniformization` — uniformization of GH Cauchy-compact Cauchy-maximal `𝔼₀`-manifolds

Package WP-41n (WAVE5-PLAN.md, WP-39n). `papers/gx`, §4.6 (`RamcovGX.tex:2348–2396`), DEC-28's
Cauchy-compact form (`brunswic2021cauchy` Prop 2.17 / Cor 2.18), DEC-75/76/77.
**No ledger label is certified in full here, so nothing is marked.** Two rows, both partial:

* `theo:globally_hyperbolic_cauchy_complete_cauchy_maximal` — `RamcovGX.tex:2363`, partial
  (DEC-27/28): `GX.btz_uniformization` — for `M` GH, Cauchy-compact, Cauchy-maximal, with a BTZ
  point (`s ≥ 1`) and `π₁(Reg M)` not metabelian, and **every** developing pair `(𝒟, ρ)` of
  `Reg M`: `𝒟` injective on `Reg M̃`; `ρ` faithful, discrete, torsion-free; a loxodromic in
  `ρ(Γ)` (DEC-75); the `Γ`-invariant family of lightlike planes `(Π_w)_{w ∈ Λ(Γ)}`;
  `𝒟(Reg M̃) = ⋂_w I⁺(Π_w)` (an equality, future case, DEC-77 (a)); `Γ` free and properly
  discontinuous; `Reg M̃` future complete; `𝒟` induces an isometry `Reg M ≅ ρ(Γ)\Ω⁺`. The future
  case rests on ONE tagged `sorry` (`GX.e0RegM_range_not_subset_omegaMinus`); without it,
  `GX.btz_uniformization_reg` (0 `sorry` of its own) is the time-reversal disjunction. The BTZ
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
| "up to time reversal" (dropped, DEC-77 (a)) | ✓ the future case is concluded; it rests on the tagged `sorry` `e0RegM_range_not_subset_omegaMinus` |
| `M` second countable; (O2) `hLine` | ⚠ strengthened: carried, as in `GXScaffold.BTZ.AbsMax` (Cor 2.18's form) |
| the given pair `(𝒟, ρ)` (l.2365) | ✓ every developing pair of `Reg M` is a hypothesis, not an `∃` |
| `𝒟` injective | ⚠ on `Reg M̃` ✓; on `M̃`: the step l.2392–2394 proved, its inputs carried |
| `ρ` faithful, discrete, torsion-free | ✓ |
| `D(M̃) = (⋃Δᵢ) ∪ ⋂ I⁺(Πⱼ)` (DEC-28's display) | ⚠ the regular half `𝒟(Reg M̃) = ⋂ I⁺(Π_w)` ✓ (equality); the rays `Δ_i` ✗ |
| `M ≅ ρ\D(M̃)`, BTZ topology | ⚠ `Reg M ≅ ρ(Γ)\Ω⁺` ✓ (isometry, `𝒟`-induced); at the BTZ points ✗ |

## SCOPE (disclosed)

* (a) **The future-case selection** (DEC-77 (a)) is the one tagged `sorry` of this file,
  `GX.e0RegM_range_not_subset_omegaMinus`: D-11 (d)'s argument needs `𝒟` extended to the BTZ
  points and the parabolic holonomy of the loop around a BTZ line, read through the regular charts
  of `Reg M` (the obstruction is in the `SORRY` text).
* (b) **The BTZ half of the headline is not formalized**: `𝒟` on `sing M̃`, the rays
  `Δ_i = 𝒟(S_x)` in `∂Ω`, the image `(⋃Δ_i) ∪ Ω`, and `M ≅ ρ\𝒟(M̃)` for the BTZ topology. They live
  on the maximal branched covering `BTZTildeData` (GXScaffold.BTZ.Manifolds), built over the
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
* (d) Upstream `sorry`s inherited (`#print axioms`, `campaign/WP-41n/axioms.out`): the five leaves
  of `GXScaffold.BTZ.AbsMax` (through `absMax_e0RegM`), `GX.E0Surgery.regM_isCauchyComplete`, and,
  for the `M̃` step only, `GX.BTZTildeData.globallyHyperbolic_of_base`.

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

/-! ## §4 The `𝔼₀` case: `Reg M` of a GH Cauchy-compact Cauchy-maximal `𝔼₀`-manifold -/

section E0

open E0CBG E0Spear E0AbsMax
open scoped Causal.Flat

variable
  (hLine : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [SecondCountableTopology M] [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid],
    E0LM.E0GlobalBTZ (Causal.CBG.chartedCausality E0LM.D M) (Causal.CBG.chartedSing e0SingY M 0))

variable {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [SecondCountableTopology M]
  [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]

include hLine in
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
  obtain ⟨hGH', hCC', hAM⟩ := cor_abs_max hLine hGH hCC hmax
  obtain ⟨hlox, hD, hρ, hdisc, htf, hinv, -⟩ := e0RegM_holonomy M hGH' hCC' x₀ hnm D ρ hpair
  obtain ⟨S, hS⟩ := Causal.Flat.exists_developsCC_of_isCauchyComplete' (e0RegMFlat M) hGH' hCC' hpair
  obtain ⟨-, hcase⟩ := uniformization_of_absMax (e0RegMFlat M) hpair hGH'.1 hS hlox hAM
  refine ⟨hlox, hD, hρ, hdisc, htf, hinv, ?_⟩
  rcases hcase with ⟨hF, hr, hfp, hB⟩ | ⟨hP, hr, hfp, hB⟩
  · exact Or.inl ⟨hF, hr, omegaPlus_eq_iInter_Iplus _, hfp,
      isFutureComplete_of_range_eq_omegaPlus (e0RegMFlat M) hpair hD hr, hB⟩
  · exact Or.inr ⟨hP, hr, omegaMinus_eq_iInter_Iminus _, hfp, hB⟩

include hLine in
/-- **The future case is forced by a BTZ line** (DEC-77 (a); SCOPE D-11 (d)): if `M` has a BTZ
point, the developed regular part does not lie in a past regular domain. -/
theorem e0RegM_range_not_subset_omegaMinus (hGH : (CE M).GloballyHyperbolic)
    (hCC : E0CauchyCompact M) (hmax : IsE0CauchyMaximal M)
    (hsing : (Causal.CBG.chartedSing e0SingY M 0).Nonempty) (x₀ : e0RegMFlat M)
    (hnm : ¬IsMetabelianGroup (Causal.Deck (Causal.UniversalCover.proj (e0RegMFlat M) x₀)))
    (D : Causal.UniversalCover (e0RegMFlat M) x₀ → Causal.Minkowski 2)
    (ρ : Causal.Deck (Causal.UniversalCover.proj (e0RegMFlat M) x₀) →* Causal.Flat.isom 2)
    (hpair : Causal.Flat.IsDevelopingPair x₀ D ρ) :
    ¬ range D ⊆ Causal.Flat.omegaMinus (Causal.Flat.limitSetJ ρ.range) := by
  sorry -- SORRY(theo:globally_hyperbolic_cauchy_complete_cauchy_maximal): FUTURE CASE SELECTION. D-11 (d)'s argument — a BTZ point x has a nontrivial stabiliser (the loop around its line, parabolic holonomy ρ(γ_x) ≠ 1 fixing D̂(x)), so D̂(x) ∉ Ω (free action), while y ∈ I⁺(x) regular gives D̂(x) ∈ J⁻(D ỹ) ⊆ Ω⁻ in the past case — needs the developing map EXTENDED to the BTZ points (D̂ on M̃) and its identification, near a BTZ line, with the E₀ model's developing map read through the Reg M charts `E0LM.regChartM` (a chain of flat charts along a curve of Reg M converging to x); neither the extension of D across sing₀(M) from the universal cover of Reg M nor the loop γ_x ∈ π₁(Reg M) with its parabolic holonomy is built (the BTZTildeData of GXScaffold.BTZ.Manifolds lives over the SingularGXStructure presentation, with no bridge to ChartedSpace E0Y M, where E0CauchyCompact / IsE0CauchyMaximal / AbsMax live). A causal-only route fails: a past-inextensible causal curve of Reg M ending at x develops to a past causal curve of Ω⁻ whose convergence (finite length near the line) is again an E₀-chart computation. A second route avoids D̂ but is not built either: along a full future BTZ ray at x (B21 Lemma 2.3, `GX.E0Spear.exists_fullFutureBTZRay`, itself resting on the upstream `lem_tube` and needing the extra hypothesis hSC), the regular points at fixed r, θ develop (one sector chart, `GX.pastHalf_aeChart_eventually`) to h•(τ·(1,1,0) + O(1)) as τ → ∞, which leaves every I⁻(Π_w) whose null direction is not h•(1,1,0); Λ(ρΓ) has two distinct points (the loxodromic). It needs the lift of that curve to the universal cover of Reg M with 𝒟 = h•chartMap along it (the interval analogue of `GX.exists_affine_eq_of_locally`) and the half-space form of I⁻(Π_w).

include hLine in
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
    btz_uniformization_reg hLine hGH hCC hmax x₀ hnm D ρ hpair
  rcases hcase with ⟨hF, hr, hI, hfp, hfc, hB⟩ | ⟨-, hr, -⟩
  · exact ⟨hlox, hD, hρ, hdisc, htf, hinv, hF, hr, hI, hfp, hfc, hB⟩
  · exact absurd hr.subset
      (e0RegM_range_not_subset_omegaMinus hLine hGH hCC hmax hsing x₀ hnm D ρ hpair)

include hLine in
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
  (btz_uniformization hLine hGH hCC hmax hsing x₀ hnm D ρ hpair).2.2.2.2.2.2.2.2.2.2.1

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
