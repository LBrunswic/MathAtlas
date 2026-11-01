import CausalScaffold.Flat.Nonloxodromic
import CausalScaffold.Flat.Loxodromic
import CausalScaffold.CompactCauchy
import CausalScaffold.CurvesExtend

/-!
# `CausalScaffold.Flat.Classification` — Barbot §11: Theorems A and B, absolute maximality

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §11
"Summary of the proof" (`sumup`, `GHFspace.tex` l.3477–3679 of the labelled file
`papers/barbot/legacy/labeled/GHFspace.tex`) and the two theorems it assembles. **No label is
marked**: both rest on tagged `sorry`s (here and upstream) and on named external hypotheses
(DEC-36), so both are partial (SCOPE).

* `bthm:caucomp` — `GHFspace.tex:338` (Theorem A), **stated and assembled** under reading R1
  (DEC-43): `barbot_A`, through the layering G3 `barbot_A₀` (embedding) → [11.i] → `barbot_A`.
* `bthm:cauclo` — `GHFspace.tex:353` (Theorem B), **stated and assembled**: `barbot_B`, with
  "standard" read as Cauchy-compact Cauchy-hyperbolic (G4). G4 is realised in the statement by
  `CauchyCompact` on the torus product (`IsCHTorusProduct M₁ ∧ CauchyCompact M₁`, exactly
  BARBOT-THEOREMS §2), which is equivalent (the torus fibre being compact; not proved here) to
  its Cauchy-hyperbolic base being standard;
  `IsStandard` states G4 for a spacetime and is not used by the statements (the library builds no
  base spacetime of a torus product to apply it to).
* Prose: [11.i] absolute maximality (`maxi`, l.3563–3679): `amgh_of_isTranslationSpacetime`,
  `amgh_of_isMisnerSpacetime` (F1's nonzero boost is in `IsMisnerSpacetime`, G2),
  `amgh_of_isCHCentralExtension`, and G1 + G3 for the unipotent family
  (`exists_absMax_unipotent_ltp`); [11.ii] (l.3573–3581): `surjective_of_mgh_cauchyCompact` (G8);
  Rem 2.3 `clomax` corrected (DEC-44, l.571–578): `absMax_of_cauchyCompact_of_mgh`, through lemma K
  (`Causality.isCauchySurface_of_isLocallyCauchyTwoSided`) under its named hypotheses
  (`FlatLemmaKData`); G9 (l.3542–3548): `cauclo_from_embedding`.
* gx exports: **`equality_of_absMax`** (the §11.3 lifting argument, l.3607–3611, `AbsMax P M →
  range 𝒟 = Ω`, `P` parametric) — **proved, no `sorry`**; `range_eq_omegaS_of_absMax`.
* The bridge connection (wave 3, written in parallel): `developsCC_iff_bridge`,
  `exists_developsCC_of_isCauchyComplete'` — CauchyComplete's bridge conclusion is Develop's
  `DevelopsCC`; proved here.

> Up to finite coverings and linear twisted products, every Cauchy-complete globally hyperbolic
> flat spacetime can be tamely embedded in an absolutely maximal globally hyperbolic spacetime
> which is a translation spacetime, a Misner spacetime, a unipotent spacetime, or the twisted
> product of a Cauchy-hyperbolic flat GH spacetime by an euclidean torus. (l.340–347)

> Up to finite coverings, every maximal Cauchy-compact globally hyperbolic flat spacetime is
> isometric to a translation spacetime, a Misner spacetime, or the twisted product of a standart
> spacetime (Cauchy-compact Cauchy-hyperbolic GH spacetime) by an euclidean torus. (l.355–359)

> (i) Translation spacetimes, Misner spacetimes, and twisted products of Cauchy-hyperbolic
> spacetimes by flat torii are absolutely maximal, and any unipotent spacetime can be tamely
> embedded in some absolutely maximal unipotent spacetime. (l.3568–3571)

> (ii) Any maximal Cauchy-compact GH spacetime is not only embedded in a finite quotient of a
> translation spacetime, a Misner spacetime or the twisted product of a standart spacetime by a
> flat torus, it is actually \emph{isometric} to one of them. (l.3573–3576)

> Hence, if the inclusion $\Omega_{0} \subset \Omega_{1}$ is actually surjective, then
> $\Gamma'_{0} = \Gamma_{1}$, and $f$ is a surjective embedding. (l.3609–3611)

> It follows that nontrivial linear twisted products destroy Cauchy-compactness (l.3542–3543)

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; `Minkowski d` has `d` spatial
dimensions: Barbot's `n` is `d + 1`. The Misner and unipotent families live in
`Minkowski (e + 1)` (Examples); `IsMisnerFamily`, `IsUnipotentFamily` extend them by `False` to
`d₁ = 0`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| A: `M` Cauchy-complete GH flat | ✓ carried: `GH M` (ETT's) + `IsCauchyComplete d M` (CauchyComplete's metric notion, DEC-35; Lean ≥ paper) |
| A, B: "any dimension" (l.388, l.411) | ⚠ strengthened: `1 ≤ d` (Barbot's `n ≥ 2`), added in `barbot_A`, `barbot_A₀` and `barbot_B` (not in BARBOT-THEOREMS §2's B signature); used to write `d = d' + 1` in the Misner branch. For `d = 0` (`𝐌¹`) the statement is not attempted |
| A/B: external group theory (Benoist, Bieberbach, Auslander–Carrière–Dal'bo, Carrière–Dal'bo, cited) | ⚠ strengthened: named hypotheses bundled in `BarbotExternals d` (DEC-36): `BenoistNoLox k`, `BieberbachI (ℝᵏ)` (`k ≤ d + 1`), `AuslanderCarriereDalbo k`, `MaxUnipotentSubspace k` for `k ≤ d` |
| B: `M` maximal Cauchy-compact GH | ✓ carried: `GH M`, `CauchyCompact M`, `MGH M` |
| B: π₁ finitely generated ⇒ family (a) (DEC-44, Selberg) | ⚠ strengthened: `SelbergLemma (Minkowski d)` (named external) |
| B: "closed spacelike hypersurfaces are Cauchy" (l.3537–3540, asserted) | ⚠ strengthened: lemma K's named data `FlatLemmaKData` on **every** GH flat target of dimension `d` (DEC-44): tarentin, causal arc-connectedness, `J^±(p) ≠ {p}`, `CurvesExtend`, a chronal causal flow, an acausal Cauchy surface. The non-vacuity witness `flatLemmaKData_minkowskiSpace` is **pointwise** (one instance, `𝐌ⁿ`); the universal form `∀ N, GH N → FlatLemmaKData N` is true by standard GH facts (Geroch / Bernal–Sánchez for the acausal Cauchy surface, a complete timelike flow), not certified here |
| Rem 2.3: CGH ⇒ AMGH | ⚠ corrected (DEC-44): GH + Cauchy-compact + **MGH** ⇒ `AbsMax (fun _ => True)` |
| §11.3 equality: `M` absolutely maximal, `M(S)` a GH spacetime of the class | ✓ carried, `P` parametric (DEC-45): `AbsMax P M`, `GH B`, `P B`, `IsQuotientOf B Γ Ω`, `𝒟` injective, `range 𝒟 ⊆ Ω` |
| universes | targets of `AbsMax` are flat spacetimes of the same universe (`FlatSpacetime.{u}`); the models, `M'` and `B` are in `Type` (`FlatSpacetime.{0}`), as upstream |

## SCOPE (disclosed)

* **Readings.** Theorem A is R1 (DEC-43): a finite cover `M'` of `M` tamely embeds in an LTP `B`
  over a model `M₁` of dimension `≤ d`, `M₁` AMGH in its own dimension for Cauchy-complete targets
  (`CauchyCompleteClass`); the fourth family is the central-extension form (b),
  `IsCHCentralExtension` (DEC-44). Theorem B: "standard" is Cauchy-compact Cauchy-hyperbolic (G4);
  its third family is (a), `IsCHTorusProduct ∧ CauchyCompact` (π₁ finitely generated, Selberg),
  where `CauchyCompact` of the product carries G4 (`IsStandard` is stated, unused).
* **Lemma K's data is universal, its witness pointwise.** `barbot_B`,
  `absMax_of_cauchyCompact_of_mgh` and `surjective_of_mgh_cauchyCompact` carry
  `hK : ∀ N, GH N → FlatLemmaKData N`; it cannot be narrowed to the targets used, because absolute
  maximality quantifies over every GH target. `flatLemmaKData_minkowskiSpace` shows one instance
  (`𝐌ⁿ`) only; the universal form rests on standard GH facts (an acausal Cauchy surface,
  Bernal–Sánchez; a complete timelike flow; tarentin and causal arc-connectedness of GH flat
  spacetimes), which the library does not prove for a general flat spacetime (`Splitting.lean`'s
  target 4 is itself a tagged `sorry`).
* **Namespace.** `UniversalCover.exists_deck_apply_eq` is declared in `Causal.Flat` (the campaign's
  namespace rule), so its full name is `Causal.Flat.UniversalCover.exists_deck_apply_eq` and dot
  notation on the ported `Causal.UniversalCover` does not find it; it is called by full name.
* **Assembly, proved here (no `sorry` of their own):** `barbot_A₀` (bridge → developing pair →
  case split loxodromic / not → §9, §10 → the finite cover), `barbot_A` (A₀ + [11.i] + G1/G3),
  `barbot_B` (A₀ + G9 + Rem 2.3 corrected + [11.ii]), `caseOutput` and its three branches,
  `absMax_of_cauchyCompact_of_mgh` (Rem 2.3 corrected, from lemma K's proved form),
  `surjective_of_mgh_cauchyCompact` ([11.ii], G8), `equality_of_absMax`,
  `range_eq_omegaS_of_absMax`, the bridge connection.
* **Sorries in this file (each tagged with its obstruction):** `nonloxodromic_parabolic_convex`
  (Nonloxodromic's parabolic export omits the convexity of its `Ω`, which tameness needs: a
  finding for that file), `exists_finiteCover_tameEmbedding` (the intermediate cover
  `ρ⁻¹(Γ'')\M̃` and π₁ of the quotients), `amgh_of_isTranslationSpacetime`,
  `amgh_of_isMisnerSpacetime`, `amgh_of_isCHCentralExtension` ([11.i], the lifting argument; GH
  and Cauchy-completeness of the models), `exists_absMax_unipotent_ltp` (G1 + G3),
  `isLocallyCauchyTwoSided_image` (an embedded acausal compact Cauchy surface is locally Cauchy
  and two-sided in the target: lemma K's input), `isCauchyComplete_of_cauchyCompact` (smoothing
  of a topological Cauchy surface), `cauclo_from_embedding` (G9, the passage (b) → (a), finite
  covers of maximal CGH spacetimes).
* **Upstream sorries** reached by `barbot_A` / `barbot_B` (`#print axioms`, REPORT.json): from
  CauchyComplete `isCoveringMap_projAlong_comp`, `bcor_quoiso`, `exists_splitting_of_isCauchySurface`;
  from Nonloxodromic `nonloxodromic_elliptic`, `exists_timelike_fixed_of_elliptic_of_null`; from
  Loxodromic `loxo_elementary_misner`, `loxo_generic_centralExtension`; and those beneath them.
* **Build note.** At the time of writing `Flat.Loxodromic` does not compile (its section
  Uniformization lacks `[T2Space M]`, now required by Develop's `bprop_danom`); this file was
  typechecked against a private copy with that one binder added. The declarations used here are
  outside that section.
* **Not attempted:** the corollary on closed Cauchy hypersurfaces (finitely covered by
  `Tᵏ × closed hyperbolic manifold`, l.383–386): the library has no notion of a closed hyperbolic
  manifold.
* **Findings.** (1) Nonloxodromic's `nonloxodromic_parabolic` should export `Convex ℝ Ω` (true:
  `Ω = π_𝒰⁻¹(Ω_A)`, a slab between null hyperplanes), without which no tame embedding into
  `B = Γ''\Ω` can be derived (π₁(B) is an extension of `Γ''` by π₁(Ω)). (2) Barbot's (ii) "follows
  from (i)" (l.3578) also needs that a finite cover of a maximal CGH spacetime is maximal, which the
  paper does not state (used in `cauclo_from_embedding`). (3) [11.i]'s proof applies Theorem A to the
  target `N` (l.3588–3590): the layering A₀ → (i) → A (G3) is what makes that non-circular; here
  `barbot_A₀` carries the embedding and (i) is stated after it.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
wave 5, package WP-34e-Classification.
-/

namespace Causal.Flat

open Set Function Filter Topology TopologicalSpace

universe u

variable {d : ℕ}

/-! ## §0 The families in every dimension, the externals, lemma K's data -/

section Families

/-- **The Misner family in dimension `d₁`** (`Examples`' `IsMisnerSpacetime` lives in
`Minkowski (e + 1)`; there is none in `𝐌¹`). -/
def IsMisnerFamily : (d₁ : ℕ) → FlatSpacetime.{u} d₁ → Prop
  | 0, _ => False
  | _ + 1, M => IsMisnerSpacetime M

/-- **The unipotent family in dimension `d₁`** (none in `𝐌¹`). -/
def IsUnipotentFamily : (d₁ : ℕ) → FlatSpacetime.{u} d₁ → Prop
  | 0, _ => False
  | _ + 1, M => IsUnipotentSpacetime M

variable (d) in
/-- **The class of Cauchy-complete targets** (DEC-45 (α)): CauchyComplete's metric notion. -/
def CauchyCompleteClass : FlatSpacetime.{u} d → Prop := fun N => IsCauchyComplete d N

/-- **Theorem A's four model families** (DEC-43, DEC-44): translation, Misner (with a nonzero
boost, F1), unipotent, and the central-extension form (b) of "Cauchy-hyperbolic × torus". -/
def IsModelA {d₁ : ℕ} (M₁ : FlatSpacetime.{u} d₁) : Prop :=
  IsTranslationSpacetime M₁ ∨ IsMisnerFamily d₁ M₁ ∨ IsUnipotentFamily d₁ M₁ ∨
    IsCHCentralExtension M₁

/-- **G4: a standard spacetime** (l.358): a Cauchy-compact Cauchy-hyperbolic spacetime. Stated for
reference: Theorem B carries G4 as `CauchyCompact` of the torus product (`IsModelB`), since the
library constructs no base spacetime of an `IsCHTorusProduct` to which `IsStandard` could apply. -/
def IsStandard (M : FlatSpacetime.{u} d) : Prop := IsCauchyHyperbolic M ∧ CauchyCompact M

/-- **Theorem B's three families**: translation, Misner, and the literal twisted product (a) of a
standard spacetime by a torus — family (a), Cauchy-compact. -/
def IsModelB (M₁ : FlatSpacetime.{u} d) : Prop :=
  IsTranslationSpacetime M₁ ∨ IsMisnerFamily d M₁ ∨ (IsCHTorusProduct M₁ ∧ CauchyCompact M₁)

variable (d) in
/-- **The external group theory of §5, §9, §10** (DEC-36), as named hypotheses in every dimension
`≤ d` (Theorem A's proof of absolute maximality applies Theorem A in the model's dimension):
Benoist's elementarity (Prop 9.1), Bieberbach I (§5), Auslander–Carrière–Dal'bo (5.1) and
Carrière–Dal'bo's maximal unipotent subspace (5.2). -/
structure BarbotExternals : Prop where
  benoist : ∀ k ≤ d, BenoistNoLox k
  bieberbach : ∀ k ≤ d + 1, BieberbachI (EuclideanSpace ℝ (Fin k))
  auslander : ∀ k ≤ d, AuslanderCarriereDalbo k
  unipotent : ∀ k ≤ d, MaxUnipotentSubspace k

theorem BarbotExternals.mono {d₁ : ℕ} (h : BarbotExternals d) (h₁ : d₁ ≤ d) :
    BarbotExternals d₁ :=
  ⟨fun k hk => h.benoist k (hk.trans h₁), fun k hk => h.bieberbach k (by omega),
    fun k hk => h.auslander k (hk.trans h₁), fun k hk => h.unipotent k (hk.trans h₁)⟩

/-- **Lemma K's named data on a flat spacetime** (`CausalScaffold.CompactCauchy`, DEC-44): the
hypotheses of its proved form `isCauchySurface_of_isLocallyCauchyTwoSided` beyond GH, with the
splitting supplied by a chronal causal flow (`Splitting.lean`, target 4, itself a tagged `sorry`
for a general flat spacetime). -/
structure FlatLemmaKData (N : FlatSpacetime.{u} d) : Prop where
  tarentin : (flatCausality d N).Tarentin
  arc : (flatCausality d N).CausallyArcConnected
  jminus : ∀ p : N, (flatCausality d N).Jminus ⊤ {p} ≠ {p}
  jplus : ∀ p : N, (flatCausality d N).Jplus ⊤ {p} ≠ {p}
  curvesExtend : (flatCausality d N).CurvesExtend
  flow : (flatCausality d N).HasChronalCausalFlow
  exists_cauchy : ∃ S : Set N, (flatCausality d N).IsCauchySurface S ∧
    (flatCausality d N).IsAcausal S

/-- **Non-vacuity** (kb/0012): `𝐌ⁿ` carries lemma K's data. -/
theorem flatLemmaKData_minkowskiSpace : FlatLemmaKData (FlatSpacetime.minkowskiSpace d) := by
  have h : flatCausality d (FlatSpacetime.minkowskiSpace d) = minkowski d := flatCausality_self
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h]; exact minkowski_tarentin
  · rw [h]; exact minkowski_causallyArcConnected
  · rw [h]; exact staticCausality.Jminus_ne_singleton
  · rw [h]; exact staticCausality.Jplus_ne_singleton
  · rw [h]; exact minkowski_curvesExtend d
  · exact Flat.flatCausality_self_hasChronalCausalFlow
  · rw [h]
    refine ⟨graph fun _ => (0 : ℝ), isCauchySurface_graph_zero, ?_⟩
    exact isAcausal_graph_iff.2 fun x y hxy => by simpa using norm_pos_iff.2 (sub_ne_zero.2 hxy)

end Families

/-! ## §1 The bridge connected to `DevelopsCC` (wave 3, written in parallel) -/

section Bridge

/-- **CauchyComplete's bridge conclusion is Develop's `DevelopsCC`**: (CC′) is the conjunction of
`IsEntireAcausalGraph` and `NullSaturated`. -/
theorem developsCC_iff_bridge {M : Type*} [TopologicalSpace M] [ChartedSpace (Minkowski d) M]
    [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))] {x₀ : M}
    {D : UniversalCover M x₀ → Minkowski d} {S : Set M} :
    DevelopsCC x₀ D S ↔ (flatCausality d M).IsCauchySurface S ∧
      InjOn D (UniversalCover.proj M x₀ ⁻¹' S) ∧
      IsEntireAcausalGraph (D '' (UniversalCover.proj M x₀ ⁻¹' S)) ∧
      NullSaturated (D '' (UniversalCover.proj M x₀ ⁻¹' S)) :=
  ⟨fun h => ⟨h.cauchy, h.injOn, h.cc.entire, h.cc.nullSat⟩,
    fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, ⟨h3, h4⟩⟩⟩

/-- **The bridge, in Develop's terms** (DEC-35): a GH Cauchy-complete flat spacetime has, for every
developing pair, a Cauchy surface `S` with `DevelopsCC x₀ D S`. -/
theorem exists_developsCC_of_isCauchyComplete' (M : FlatSpacetime.{u} d) (hGH : GH M)
    (hCC : IsCauchyComplete d M) {x₀ : M} {D : UniversalCover M x₀ → Minkowski d}
    {ρ : Deck (UniversalCover.proj M x₀) →* isom d} (hpair : IsDevelopingPair x₀ D ρ) :
    ∃ S : Set M, DevelopsCC x₀ D S := by
  obtain ⟨S, h⟩ := exists_developsCC_of_isCauchyComplete M hGH hCC x₀
  exact ⟨S, developsCC_iff_bridge.2 (h D hpair.gx)⟩

end Bridge

/-! ## §2 The case split: the common output of §9 and §10 -/

section Cases

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Minkowski d) M]
  [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))] {x₀ : M}
  {D : UniversalCover M x₀ → Minkowski d} {ρ : Deck (UniversalCover.proj M x₀) →* isom d}
  {S : Set M}

/-- **The common output of §9 and §10** (DEC-43 R1): a finite-index `Γ'' ≤ Γ = ρ(Deck)`, a
convex open `Γ''`-invariant `Ω ⊇ 𝒟(M̃)`, the quotient `B = Γ''\Ω`, and `B` an LTP over a model
`M₁` of Theorem A's families, of dimension `≤ d`. -/
def CaseOutput (D : UniversalCover M x₀ → Minkowski d)
    (ρ : Deck (UniversalCover.proj M x₀) →* isom d) : Prop :=
  ∃ Γ : Subgroup (isom d), Γ ≤ ρ.range ∧ Γ.relIndex ρ.range ≠ 0 ∧
    ∃ Ω : Opens (Minkowski d), range D ⊆ Ω ∧ Convex ℝ (Ω : Set (Minkowski d)) ∧
      ∃ B : FlatSpacetime.{0} d, IsQuotientOf B Γ Ω ∧
        ∃ d₁ : ℕ, d₁ ≤ d ∧ ∃ M₁ : FlatSpacetime.{0} d₁, IsModelA M₁ ∧ IsLTPOver B M₁

/-- `Ω(S̃)` is convex (Prop 8.10). -/
theorem convex_omegaS_of_developsCC [T2Space M] (hpair : IsDevelopingPair x₀ D ρ)
    (h : DevelopsCC x₀ D S) :
    Convex ℝ ((omegaSOpens ρ.range (D '' (UniversalCover.proj M x₀ ⁻¹' S)) : Opens _) :
      Set (Minkowski d)) :=
  (bprop_ghyp (ccAction_of_developsCC hpair h)).2.1

/-- **[9.P]–[9.A] with the convexity of `Ω`.** Nonloxodromic's `nonloxodromic_parabolic`, with
`Convex ℝ Ω` added to its conclusion (needed for tameness, `exists_finiteCover_tameEmbedding`). -/
theorem nonloxodromic_parabolic_convex [T2Space M]
    (_hBieb : ∀ k : ℕ, k ≤ d + 1 → BieberbachI (EuclideanSpace ℝ (Fin k)))
    (_hpair : IsDevelopingPair x₀ D ρ) (_hcaus : (flatCausality d M).IsCausal)
    (_h : DevelopsCC x₀ D S) {Γ' : Subgroup (isom d)} (_hle : Γ' ≤ ρ.range)
    (_hidx : Γ'.relIndex ρ.range ≠ 0) (_hnl : ∀ γ ∈ ρ.range, ¬IsLoxodromic (linOf γ))
    {v₀ : Minkowski d} (_hv0 : v₀ ≠ 0) (_hv : minkQ v₀ = 0)
    (_hfix : ∀ γ ∈ Γ', linOf γ v₀ = v₀) (_hpar : ∃ γ ∈ Γ', IsParabolic (linOf γ)) :
    ∃ Γ'' : Subgroup (isom d), Γ'' ≤ Γ' ∧ Γ''.relIndex Γ' ≠ 0 ∧
      ∃ Ω : TopologicalSpace.Opens (Minkowski d), range D ⊆ Ω ∧
        Convex ℝ (Ω : Set (Minkowski d)) ∧
        ∃ B : FlatSpacetime.{0} d, IsQuotientOf B Γ'' Ω ∧
          ∃ d₁ : ℕ, d₁ + 1 ≤ d ∧ ∃ M₁ : FlatSpacetime.{0} (d₁ + 1), IsUnipotentSpacetime M₁ ∧
            IsLTPOver B M₁ := by
  sorry -- SORRY([9.P]–[9.A], convexity): `Flat.Nonloxodromic.nonloxodromic_parabolic` (itself a tagged sorry) exports `range D ⊆ Ω ⊆ Ω(S̃)` but not `Convex ℝ Ω`, and its `Ω` is existential, so the convexity cannot be added after the fact. In its construction (its obstruction (7)) `Ω = π_𝒰⁻¹(Ω_A)` with `Ω_A` a component `{α < y < β}` of `Ω(A)` in `𝒰` (`unipDomain`, a slab between two null hyperplanes, convex) and `π_𝒰` affine, so `Ω` is convex; the export should carry it (finding 1)

/-- **The nonloxodromic case in the common form** (§9, `nonloxodromic` with convexity). -/
theorem caseOutput_nonloxodromic [T2Space M] (hB : BenoistNoLox d)
    (hBieb : ∀ k : ℕ, k ≤ d + 1 → BieberbachI (EuclideanSpace ℝ (Fin k)))
    (hpair : IsDevelopingPair x₀ D ρ) (hcaus : (flatCausality d M).IsCausal)
    (h : DevelopsCC x₀ D S) (hnl : ∀ γ ∈ ρ.range, ¬IsLoxodromic (linOf γ)) :
    CaseOutput D ρ := by
  have hD := (bprop_danom hpair hcaus h).2
  have hcv := convex_omegaS_of_developsCC hpair h
  obtain ⟨Γ₁, hle₁, hidx₁, hcase⟩ := bprop_sanloxo hB hnl
  rcases hcase with ⟨v, hv, hfix⟩ | ⟨v₀, hv0, hv, hfix, hpar | hell⟩
  · obtain ⟨Γ₂, hle₂, hidx₂, B, hB', d₁, hd₁, M₁, hM₁, hltp⟩ :=
      nonloxodromic_elliptic hBieb hpair h hle₁ hidx₁ ⟨v, hv, fun γ hγ => (hfix γ hγ).1⟩
    exact ⟨Γ₂, hle₂.trans hle₁, Subgroup.relIndex_ne_zero_trans hidx₂ hidx₁, _, hD, hcv, B, hB',
      d₁, hd₁, M₁, Or.inl hM₁, hltp⟩
  · obtain ⟨Γ₂, hle₂, hidx₂, Ω, hDΩ, hΩ, B, hB', d₁, hd₁, M₁, hM₁, hltp⟩ :=
      nonloxodromic_parabolic_convex hBieb hpair hcaus h hle₁ hidx₁ hnl hv0 hv hfix hpar
    exact ⟨Γ₂, hle₂.trans hle₁, Subgroup.relIndex_ne_zero_trans hidx₂ hidx₁, Ω, hDΩ, hΩ, B, hB',
      d₁ + 1, hd₁, M₁, Or.inr (Or.inr (Or.inl hM₁)), hltp⟩
  · obtain ⟨Γ₂, hle₂, hidx₂, v, hv', hfix'⟩ :=
      exists_timelike_fixed_of_elliptic_of_null hv0 hv hfix hell
    have hidx₂₁ := Subgroup.relIndex_ne_zero_trans hidx₂ hidx₁
    obtain ⟨Γ₃, hle₃, hidx₃, B, hB', d₁, hd₁, M₁, hM₁, hltp⟩ :=
      nonloxodromic_elliptic hBieb hpair h (hle₂.trans hle₁) hidx₂₁ ⟨v, hv', hfix'⟩
    exact ⟨Γ₃, hle₃.trans (hle₂.trans hle₁), Subgroup.relIndex_ne_zero_trans hidx₃ hidx₂₁, _, hD,
      hcv, B, hB', d₁, hd₁, M₁, Or.inl hM₁, hltp⟩

/-- **The nonelementary loxodromic case in the common form** ([10.G], family (b)). -/
theorem caseOutput_generic [T2Space M] (hA : AuslanderCarriereDalbo d)
    (hU : MaxUnipotentSubspace d) (hpair : IsDevelopingPair x₀ D ρ)
    (hcaus : (flatCausality d M).IsCausal) (h : DevelopsCC x₀ D S)
    (hlox : ∃ γ ∈ ρ.range, IsLoxodromic (linOf γ)) (hne : IsNonelementary ρ.range) :
    CaseOutput D ρ := by
  obtain ⟨Γ', hle, hidx, B, hB', d₁, M₁, hd₁, hltp, hM₁⟩ :=
    loxo_generic_centralExtension hpair hcaus h hlox hne hA hU
  exact ⟨Γ', hle, hidx, _, (bprop_danom hpair hcaus h).2, convex_omegaS_of_developsCC hpair h, B,
    hB', d₁, hd₁, M₁, Or.inr (Or.inr (Or.inr hM₁)), hltp⟩

end Cases

/-- **The elementary loxodromic case in the common form** ([10.M], Misner), in `𝐌^{d'+2}`. -/
theorem caseOutput_misner {d' : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (Minkowski (d' + 1)) M]
    [HasGroupoid M (gxGroupoid (isom (d' + 1)) (Minkowski (d' + 1)))] [T2Space M] {x₀ : M}
    {D : UniversalCover M x₀ → Minkowski (d' + 1)}
    {ρ : Deck (UniversalCover.proj M x₀) →* isom (d' + 1)} {S : Set M}
    (hpair : IsDevelopingPair x₀ D ρ) (hcaus : (flatCausality (d' + 1) M).IsCausal)
    (h : DevelopsCC x₀ D S) (hlox : ∃ γ ∈ ρ.range, IsLoxodromic (linOf γ))
    (helem : ¬IsNonelementary ρ.range) : CaseOutput D ρ := by
  obtain ⟨Γ', hle, hidx, B, hB', d₁, M₁, hd₁, hltp, hM₁⟩ :=
    loxo_elementary_misner hpair hcaus h hlox helem
  exact ⟨Γ', hle, hidx, _, (bprop_danom hpair hcaus h).2, convex_omegaS_of_developsCC hpair h, B,
    hB', d₁ + 1, by omega, M₁, Or.inr (Or.inl hM₁), hltp⟩

/-- **The case split** (BARBOT.md's spine, step 1.4): from (CC′) and the externals, loxodromic or
not (Isometries' classes), then elementary or not. -/
theorem caseOutput {M : Type*} [TopologicalSpace M] [ChartedSpace (Minkowski d) M]
    [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))] [T2Space M] {x₀ : M}
    {D : UniversalCover M x₀ → Minkowski d} {ρ : Deck (UniversalCover.proj M x₀) →* isom d}
    {S : Set M} (hE : BarbotExternals d) (hd : 1 ≤ d) (hpair : IsDevelopingPair x₀ D ρ)
    (hcaus : (flatCausality d M).IsCausal) (h : DevelopsCC x₀ D S) : CaseOutput D ρ := by
  by_cases hlox : ∃ γ ∈ ρ.range, IsLoxodromic (linOf γ)
  · by_cases hne : IsNonelementary ρ.range
    · exact caseOutput_generic (hE.auslander d le_rfl) (hE.unipotent d le_rfl) hpair hcaus h
        hlox hne
    · obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
      exact caseOutput_misner hpair hcaus h hlox hne
  · push Not at hlox
    exact caseOutput_nonloxodromic (hE.benoist d le_rfl) hE.bieberbach hpair hcaus h hlox

/-! ## §3 The finite cover and the tame embedding -/

/-- **The finite cover `M' = ρ⁻¹(Γ'')\M̃` tamely embeds in `B = Γ''\Ω`** (l.3586–3592; R1's
"finite cover", DEC-43). -/
theorem exists_finiteCover_tameEmbedding (M : FlatSpacetime.{u} d) {x₀ : M}
    {D : UniversalCover M x₀ → Minkowski d} {ρ : Deck (UniversalCover.proj M x₀) →* isom d}
    (_hpair : IsDevelopingPair x₀ D ρ) (_hinj : Injective D) {Γ : Subgroup (isom d)}
    (_hle : Γ ≤ ρ.range) (_hidx : Γ.relIndex ρ.range ≠ 0) {Ω : Opens (Minkowski d)}
    (_hΩ : range D ⊆ Ω) (_hcv : Convex ℝ (Ω : Set (Minkowski d))) {B : FlatSpacetime.{0} d}
    (_hB : IsQuotientOf B Γ Ω) :
    ∃ (M' : FlatSpacetime.{0} d) (p : M' → M), IsFiniteCover d p ∧
      ∃ f : M' → B, IsTameEmbedding d f := by
  sorry -- SORRY(bthm:caucomp, finite cover): `W := range D` is open (`hpair.gx.isOpenMap`), `Γ`-invariant (equivariance, `Γ ≤ ρ.range`) and `D : M̃ ≃ W`; the candidate is `M' := Γ\W` (`FlatQuotient.toFlatSpacetime`, which needs `ProperlyDiscontinuousSMul Γ W` — the deck group's properness `finite_deck_of_isCompact` transported along the open embedding `D` — and `IsCancelSMul`, from freeness of the deck action), `f := FlatQuotient.quotInclusion Γ (W ≤ Ω)` (an isometric embedding, `isIsometricEmbedding_quotInclusion`, after identifying `B` with `Γ\Ω` by `IsQuotientOf.exists_homeomorph`), and `p : Γ\W → M` induced by `proj ∘ D⁻¹`, a covering with fibres `ρ.range/Γ`, finite by `hidx`. Missing: (1) the descent `M ≃ ρ.range\W` (a covering-space quotient of `M̃` by its deck group, not in the port), (2) the finite-fibre covering `Γ\W → ρ.range\W`, (3) tameness: π₁ of `Γ\X` for `X` simply connected (here `W ≅ M̃`, and `Ω` convex, hence contractible) is `Γ`, and `quotInclusion` induces the identity on it — the library has no computation of π₁ of a quotient by a free properly discontinuous action

/-! ## §4 Theorem A₀ — the embedding layer (G3) -/

/-- **The output of the embedding layer** of Theorem A: a finite cover `M'` of `M` tamely embeds in
`B = Γ\Ω` (`Ω` convex), an LTP over a model `M₁` of dimension `≤ d`. -/
def EmbeddingOutput (M : FlatSpacetime.{u} d) : Prop :=
  ∃ (M' : FlatSpacetime.{0} d) (p : M' → M), IsFiniteCover d p ∧
    ∃ (Γ : Subgroup (isom d)) (Ω : Opens (Minkowski d)), Convex ℝ (Ω : Set (Minkowski d)) ∧
      ∃ B : FlatSpacetime.{0} d, IsQuotientOf B Γ Ω ∧ (∃ f : M' → B, IsTameEmbedding d f) ∧
        ∃ d₁ : ℕ, d₁ ≤ d ∧ ∃ M₁ : FlatSpacetime.{0} d₁, IsModelA M₁ ∧ IsLTPOver B M₁

/-- **Theorem A₀ (G3's first layer: the embedding, without absolute maximality).** Under the
externals (`BarbotExternals d`), a Cauchy-complete GH flat spacetime `M` (`1 ≤ d`) has a finite
cover `M'` which tamely embeds in an LTP `B` over a model `M₁` (translation, Misner, unipotent,
family (b)) of dimension `≤ d`. Proof: the bridge (`exists_developsCC_of_isCauchyComplete'`), the
case split (`caseOutput`), the finite cover (`exists_finiteCover_tameEmbedding`). -/
theorem barbot_A₀ (hE : BarbotExternals d) (M : FlatSpacetime.{u} d) (hd : 1 ≤ d) (hGH : GH M)
    (hCC : IsCauchyComplete d M) : EmbeddingOutput M := by
  obtain ⟨x₀⟩ : Nonempty M := inferInstance
  obtain ⟨D, ρ, hpair⟩ := exists_isDevelopingPair (d := d) x₀
  obtain ⟨S, h⟩ := exists_developsCC_of_isCauchyComplete' M hGH hCC hpair
  have hinj := (bprop_danom hpair hGH.1 h).1
  obtain ⟨Γ, hle, hidx, Ω, hDΩ, hcv, B, hB, d₁, hd₁, M₁, hM₁, hltp⟩ :=
    caseOutput hE hd hpair hGH.1 h
  obtain ⟨M', p, hp, f, hf⟩ :=
    exists_finiteCover_tameEmbedding M hpair hinj hle hidx hDΩ hcv hB
  exact ⟨M', p, hp, Γ, Ω, hcv, B, hB, ⟨f, hf⟩, d₁, hd₁, M₁, hM₁, hltp⟩

/-! ## §5 [11.i] Absolute maximality of the models (G1, G2, G3) -/

section AbsMax

/-- **[11.i], translation spacetimes are AMGH** (l.3616–3618: `Ω₀ = 𝐌ⁿ`). -/
theorem amgh_of_isTranslationSpacetime {d₁ : ℕ} (_hE : BarbotExternals d₁)
    (M₁ : FlatSpacetime.{0} d₁) (_h : IsTranslationSpacetime M₁) :
    AMGH (CauchyCompleteClass d₁) M₁ := by
  sorry -- SORRY([11.i], translation): (1) GH of `M₁ = Γ\𝐌ⁿ` in the `IsQuotientOf` form: Examples proves it for the constructed quotient (`gh_translation_frame`); the transfer along `IsQuotientOf.exists_homeomorph` needs the homeomorphism `Φ` to be a local isometry (charts), not stated; (2) Cauchy-completeness of `M₁` (Examples SCOPE: "completeness not stated"; the slice `t = 0` descends to a flat torus-like quotient, complete); (3) absolute maximality, l.3586–3618: for `f : M₁ → N` (`N` GH Cauchy-complete), Theorem A₀ (`barbot_A₀`, in dimension `d₁`) applied to `N` gives a finite cover `N'` tamely embedding in a model `M₂ = Γ₂\Ω₂`; the lift of `M₁' → M₂` is an isometric embedding `𝐌ⁿ = Ω₀ → Ω₂`, which extends to a global isometry (rigidity: a `(G,X)`-morphism of connected open sets is the restriction of one `g ∈ Isom`, `Port.Developing.IsGXMorphism.eq_of_eventuallyEq`), so `Ω₂ = 𝐌ⁿ` and `f` is onto. The lifting of embeddings along finite covers and the identification of `Γ₀'` with a subgroup of `Γ₂` are not formalized

/-- **[11.i], Misner spacetimes are AMGH** (l.3620–3626), with F1's nonzero boost (G2), which is a
field of `IsMisnerSpacetime`. -/
theorem amgh_of_isMisnerSpacetime {e : ℕ} (_hE : BarbotExternals (e + 1))
    (M₁ : FlatSpacetime.{0} (e + 1)) (_h : IsMisnerSpacetime M₁) :
    AMGH (CauchyCompleteClass (e + 1)) M₁ := by
  sorry -- SORRY([11.i], Misner): (1) GH of `M₁` in the `IsQuotientOf` form (Examples' `gh_misner`, `gh_frameConj` for the constructed quotients; transfer as for translation spacetimes); (2) Cauchy-completeness (Examples SCOPE: not stated); (3) absolute maximality, l.3620–3626: after Theorem A₀ on the target and the lift to `Ω₀ ⊆ Ω₂`, `Γ₂ ⊇ Γ₀'` contains the loxodromic element of nonzero boost (G2 = F1: without it the wedge sits non-surjectively in `𝐌ⁿ`), and `Ω₂ ⊆ Ω₀` because both are the regular domains of the repulsive fixed points of the loxodromic elements (Loxodromic's `limitSetJ`, `blem_loxregular`; the monotonicity `Λ(Γ₀') ⊆ Λ(Γ₂)` ⇒ `Ω(Λ(Γ₂)) ⊆ Ω(Λ(Γ₀'))`, and `Λ(Γ₀') = Λ(Γ₀)` for a finite-index subgroup). None of the lifting steps is formalized

/-- **[11.i], family (b) is AMGH** (l.3620–3626, "twisted products of Cauchy-hyperbolic spacetimes
by flat torii", in the central-extension form, DEC-44). -/
theorem amgh_of_isCHCentralExtension {d₁ : ℕ} (_hE : BarbotExternals d₁)
    (M₁ : FlatSpacetime.{0} d₁) (_h : IsCHCentralExtension M₁) :
    AMGH (CauchyCompleteClass d₁) M₁ := by
  sorry -- SORRY([11.i], family (b)): as for Misner spacetimes: GH of `Γ\Ω^±(Λ(Γ))` in the `IsQuotientOf` form (Loxodromic's `bcor_loxo_proper`, future case, itself resting on `loxo_properlyDiscontinuous`), Cauchy-completeness (`loxo_cauchyComplete`, a sorry), and the lifting argument of l.3620–3626 with `Ω₂ = Ω^±(Λ(Γ₂)) ⊆ Ω^±(Λ(Γ₀')) = Ω₀`; also the sign: a future `Ω₀` cannot sit in a past `Ω₂` (both contain a complete future, resp. past, timelike ray). Not formalized

/-- **[11.i] for the unipotent family, with G3** (l.3570–3571, l.3629–3679; G1 is the unbounded
case l.3678–3679): an LTP `B` over a unipotent spacetime `M₁`, presented as the quotient of a
convex `Ω`, tamely embeds in an LTP `B₂` over an **absolutely maximal** unipotent spacetime `M₂`. -/
theorem exists_absMax_unipotent_ltp {e : ℕ} (_hE : BarbotExternals d) (_he : e + 1 ≤ d)
    (M₁ : FlatSpacetime.{0} (e + 1)) (_hU : IsUnipotentSpacetime M₁) (B : FlatSpacetime.{0} d)
    (_hB : IsLTPOver B M₁) {Γ : Subgroup (isom d)} {Ω : Opens (Minkowski d)}
    (_hq : IsQuotientOf B Γ Ω) (_hcv : Convex ℝ (Ω : Set (Minkowski d))) :
    ∃ M₂ : FlatSpacetime.{0} (e + 1), IsUnipotentSpacetime M₂ ∧
      AMGH (CauchyCompleteClass (e + 1)) M₂ ∧
      ∃ B₂ : FlatSpacetime.{0} d, IsLTPOver B₂ M₂ ∧ ∃ g : B → B₂, IsTameEmbedding d g := by
  sorry -- SORRY([11.i] unipotent, G1 + G3): proved upstream: Prop 9.3 (`bprop_limites`, both infinite-extremity cases) and Prop 9.5 (`bprop_extension`, bounded and one-sided: G1 at the level of 9.3/9.5). Missing: (1) G1 proper — the maximal interval `]−Y₊, Y₊[` (`Y₊` the inverse operator norm of `T₀`, l.3657–3664) and its one-sided analogues, the abelian group `A` of `T̂` and the component `Ω = π₁⁻¹(]−Y₊, Y₊[)` of `Ω(A)` (`IsUnipComponent`), so `M₁ ↪ M₂ := Γ₀\Ω` tamely (`quotInclusion`, convex domains); (2) `M₂` absolutely maximal (l.3668–3676: Theorem A₀ on the target, the lift `Ω ⊆ Ω₁`, and 9.3 for `Γ₁ ⊇ Γ₀` forcing `π₁(Ω₁) ⊆ ]−Y₊, Y₊[`), its GH (Examples' `barbotGH_unip`; ETT's GH of the quotient not done upstream) and Cauchy-completeness (`unipcomplet`, l.744–753); (3) G3 — the LTP over `M₂`: `B₂ := Γ\(Ω_{M₂} ⊕ U^⊥)` with `Γ` restricting to `Γ_U` on `U` (`IsLTPData.restricts`), `B ↪ B₂` induced by the inclusion `Ω ⊆ Ω_{M₂} ⊕ U^⊥`; this needs the LTP data of `hB` to be the convex presentation `hq` (both are existential; the statement is nevertheless true as written: `hq`'s `Ω` is convex, and IsLTPOver's domain `Ω_{M₁} ⊕ U^⊥` is convex too (a unipotent slab plus a subspace), so both are simply connected developing images of the universal cover of `B` and agree up to an element of `Isom(𝐌ⁿ)` — uniqueness of the developing pair, not derived here)

end AbsMax

/-! ## §6 Theorem A -/

/-- **Theorem A** (`bthm:caucomp`, l.338–347), in reading R1 (DEC-43), the fourth family in the
central-extension form (b) (DEC-44), absolute maximality for Cauchy-complete targets (DEC-45 (α)).
Under the named externals `BarbotExternals d` — `BenoistNoLox`, `BieberbachI`,
`AuslanderCarriereDalbo`, `MaxUnipotentSubspace` in every dimension `≤ d` (DEC-36) — every GH,
Cauchy-complete (`IsCauchyComplete`, DEC-35) flat spacetime `M` with `1 ≤ d` has a finite cover
`M'` which tamely embeds in a linear twisted product `B` over a model `M₁` of dimension `d₁ ≤ d`,
`M₁` AMGH in its dimension and a translation, Misner, unipotent spacetime or of family (b).
Assembled from `barbot_A₀` (the embedding), [11.i] (`amgh_of_*`) and G1 + G3
(`exists_absMax_unipotent_ltp`); partial (SCOPE). -/
theorem barbot_A (hE : BarbotExternals d) (M : FlatSpacetime.{u} d) (hd : 1 ≤ d) (hGH : GH M)
    (hCC : IsCauchyComplete d M) :
    ∃ (M' : FlatSpacetime.{0} d) (p : M' → M), IsFiniteCover d p ∧
      ∃ (d₁ : ℕ) (_ : d₁ ≤ d) (M₁ : FlatSpacetime.{0} d₁) (B : FlatSpacetime.{0} d),
        AMGH (CauchyCompleteClass d₁) M₁ ∧
        (IsTranslationSpacetime M₁ ∨ IsMisnerFamily d₁ M₁ ∨ IsUnipotentFamily d₁ M₁ ∨
          IsCHCentralExtension M₁) ∧
        IsLTPOver B M₁ ∧ ∃ f : M' → B, IsTameEmbedding d f := by
  obtain ⟨M', p, hp, Γ, Ω, hcv, B, hq, ⟨f, hf⟩, d₁, hd₁, M₁, hM₁, hltp⟩ :=
    barbot_A₀ hE M hd hGH hCC
  have hE₁ := hE.mono hd₁
  rcases hM₁ with hT | hMis | hU | hCH
  · exact ⟨M', p, hp, d₁, hd₁, M₁, B, amgh_of_isTranslationSpacetime hE₁ M₁ hT, Or.inl hT, hltp,
      f, hf⟩
  · cases d₁ with
    | zero => exact (hMis : False).elim
    | succ e =>
      exact ⟨M', p, hp, e + 1, hd₁, M₁, B, amgh_of_isMisnerSpacetime hE₁ M₁ hMis,
        Or.inr (Or.inl hMis), hltp, f, hf⟩
  · cases d₁ with
    | zero => exact (hU : False).elim
    | succ e =>
      obtain ⟨M₂, hU₂, hamgh, B₂, hltp₂, g, hg⟩ :=
        exists_absMax_unipotent_ltp hE hd₁ M₁ hU B hltp hq hcv
      exact ⟨M', p, hp, e + 1, hd₁, M₂, B₂, hamgh, Or.inr (Or.inr (Or.inl hU₂)), hltp₂, g ∘ f,
        hg.comp hf⟩
  · exact ⟨M', p, hp, d₁, hd₁, M₁, B, amgh_of_isCHCentralExtension hE₁ M₁ hCH,
      Or.inr (Or.inr (Or.inr hCH)), hltp, f, hf⟩

/-! ## §7 Rem 2.3 corrected (DEC-44), [11.ii] (G8) -/

section CauchyCompact

/-- **An embedded compact acausal Cauchy surface is locally Cauchy and two-sided in the target**
(the "spacelike hypersurface" input of lemma K, l.576–578, l.3537–3538). -/
theorem isLocallyCauchyTwoSided_image {M N : FlatSpacetime.{u} d} (_hM : GH M) (_hN : GH N)
    {f : M → N} (_hf : IsIsometricEmbedding d f) {S : Set M}
    (_hS : (flatCausality d M).IsCauchySurface S) (_hac : (flatCausality d M).IsAcausal S) :
    (flatCausality d N).IsLocallyCauchyTwoSided (f '' S) := by
  sorry -- SORRY(clomax, lemma K input): for `x = f s`, the neighbourhood is a domain of dependence: in a flat chart of `N` at `x` inside the open `f(M)`, `S` reads as an acausal graph (Achronal's `isAcausal_graph_iff`), and `LipschitzGraph`'s `graph_subset_interior_dependenceDomain` gives a causally convex open `U ∋ x` (a small domain of dependence of a piece of `f(S)`) with `f(S) ∩ U` Cauchy in `U`; two-sidedness from the splitting of `U` by the graph's time function. Missing: the transport of `S`'s Cauchy property along the local isometry `f` into a chart (only causal convexity of `f⁻¹(U)` is immediate), the local graph form of a topological acausal Cauchy surface (S need not be Lipschitz in a chart: it is achronal there, hence 1-Lipschitz, but strict contraction holds only along `S`), and the domain-of-dependence lemmas for a graph defined on a ball rather than on all of `ℝᵈ` (LipschitzGraph's are for entire graphs)

/-- **Rem 2.3 corrected** (`clomax`, l.571–578; DEC-44): a GH, Cauchy-compact, **maximal** flat
spacetime is absolutely maximal among all GH flat targets, under lemma K's named data on every GH
flat spacetime (`FlatLemmaKData`). Proof: the image `f(S)` of a compact acausal Cauchy surface is
compact, connected (`S × ℝ ≃ₜ M` along `S`) and locally Cauchy two-sided
(`isLocallyCauchyTwoSided_image`), hence Cauchy (lemma K,
`Causality.isCauchySurface_of_isLocallyCauchyTwoSided`), so `f` is a flat Cauchy embedding and
maximality makes it onto. The printed form is false (`Examples.not_cauchyCompact_absMax`). -/
theorem absMax_of_cauchyCompact_of_mgh (hK : ∀ N : FlatSpacetime.{u} d, GH N → FlatLemmaKData N)
    (M : FlatSpacetime.{u} d) (hGH : GH M) (hC : CauchyCompact M) (hM : MGH M) :
    AbsMax (fun _ => True) M := by
  intro N hN _ f hf
  obtain ⟨S, hS, hSc, hSac⟩ := hC
  have hKM := hK M hGH
  have hKN := hK N hN
  -- `S` is connected, through the splitting `S × ℝ ≃ₜ M`
  obtain ⟨ψ, hψ⟩ := Flat.flat_exists_isCauchySplitting hKM.flow hGH.1 hS hSac
  have hSconn : IsConnected S := by
    haveI : ConnectedSpace (S × ℝ) := ψ.symm.surjective.connectedSpace ψ.symm.continuous
    haveI : Nonempty S := by
      obtain ⟨m⟩ : Nonempty M := inferInstance
      exact ⟨(ψ.symm m).1⟩
    haveI : ConnectedSpace S := (Prod.fst_surjective (β := ℝ)).connectedSpace continuous_fst
    simpa using isConnected_range (continuous_subtype_val (p := (· ∈ S)))
  -- a splitting of `N`, from its acausal Cauchy surface and flow
  obtain ⟨S₀, hS₀, hac₀⟩ := hKN.exists_cauchy
  obtain ⟨ψN, hψN⟩ := Flat.flat_exists_isCauchySplitting hKN.flow hN.1 hS₀ hac₀
  have himage : (flatCausality d N).IsCauchySurface (f '' S) :=
    Causality.isCauchySurface_of_isLocallyCauchyTwoSided hKN.tarentin hN hKN.arc hKN.jminus
      hKN.jplus hKN.curvesExtend hψN (hSc.image hf.continuous)
      (hSconn.image f hf.continuous.continuousOn)
      (isLocallyCauchyTwoSided_image hGH hN hf hS hSac)
  exact hM.2 N f (isFlatCauchyEmbedding_iff.2 ⟨hf, hGH, hN, S, hS, himage⟩)

/-- **[11.ii] (G8)** (l.3573–3581): a GH, Cauchy-compact, maximal flat spacetime is not only
embedded in a GH flat spacetime — every isometric embedding of it into one is onto (lemma K in
place of Rem `dependance`, G8). -/
theorem surjective_of_mgh_cauchyCompact
    (hK : ∀ N : FlatSpacetime.{u} d, GH N → FlatLemmaKData N) {M B : FlatSpacetime.{u} d}
    (hGH : GH M) (hC : CauchyCompact M) (hM : MGH M) (hB : GH B) {f : M → B}
    (hf : IsIsometricEmbedding d f) : Surjective f :=
  absMax_of_cauchyCompact_of_mgh hK M hGH hC hM B hB trivial f hf

/-- **A Cauchy-compact GH flat spacetime is Cauchy-complete** (compact ⇒ complete), the
input of Theorem A in Theorem B's proof ("Reconsider the proof above when M is assumed
Cauchy-compact", l.3536). -/
theorem isCauchyComplete_of_cauchyCompact (M : FlatSpacetime.{u} d) (_hGH : GH M)
    (_hC : CauchyCompact M) : IsCauchyComplete d M := by
  sorry -- SORRY(bthm:cauclo, compact ⇒ complete): `CauchyCompact` gives a compact acausal TOPOLOGICAL Cauchy surface, while `IsCauchyComplete` asks a spacelike Lipschitz one (`IsSpacelikeLipschitz`, `c < 1` point-locally in charts) with complete induced length and the topology field. Missing: (1) a spacelike Cauchy surface from a topological one (smoothing, Bernal–Sánchez; or the level set of a Cauchy time function made uniformly spacelike in charts) — not in the library; (2) for a compact spacelike Lipschitz `S`, completeness of `InducedLengthSpace d S` (a compact length space whose pseudo-emetric induces the subspace topology — the gluing of `IsSpacelikeLipschitzIn.isHomeomorph_toSubtype` over charts, CauchyComplete SCOPE)

end CauchyCompact

/-! ## §8 Theorem B -/

/-- **G9 and the identification of Theorem B** (l.3536–3548, l.3573–3581): for `M` maximal
Cauchy-compact GH with the embedding data of Theorem A₀, a finite cover of `M` is a maximal
Cauchy-compact GH spacetime of one of Theorem B's families. -/
theorem cauclo_from_embedding (_hSel : SelbergLemma (Minkowski d))
    (_hK : ∀ N : FlatSpacetime.{0} d, GH N → FlatLemmaKData N) (M : FlatSpacetime.{u} d)
    (_hGH : GH M) (_hC : CauchyCompact M) (_hM : MGH M) {M' : FlatSpacetime.{0} d} {p : M' → M}
    (_hp : IsFiniteCover d p) {Γ : Subgroup (isom d)} {Ω : Opens (Minkowski d)}
    (_hcv : Convex ℝ (Ω : Set (Minkowski d))) {B : FlatSpacetime.{0} d} (_hq : IsQuotientOf B Γ Ω)
    {f : M' → B} (_hf : IsTameEmbedding d f) {d₁ : ℕ} (_hd₁ : d₁ ≤ d) {M₁ : FlatSpacetime.{0} d₁}
    (_hM₁ : IsModelA M₁) (_hltp : IsLTPOver B M₁) :
    ∃ (M₁' : FlatSpacetime.{0} d) (q : M₁' → M), IsFiniteCover d q ∧ IsModelB M₁' ∧ GH M₁' ∧
      CauchyCompact M₁' ∧ MGH M₁' := by
  sorry -- SORRY(bthm:cauclo, G9): the chain of l.3536–3548 and (ii). (1) `M'` is GH, Cauchy-compact and maximal: GH and Cauchy-compactness lift along the finite cover `p` (preimage of a compact Cauchy surface; diamonds), maximality of a finite cover of a maximal CGH spacetime is not stated by the paper (finding 2: a Cauchy extension of `M'` should descend, through the uniqueness of the maximal Cauchy development, gx's CBG, DEC-29); (2) `B` is GH (Prop 8.10/Cor 10.3 for the quotient of `Ω`; not exported by the case theorems); then [11.ii] (`surjective_of_mgh_cauchyCompact`, proved here) makes `f` onto, so `f` is a bijective local isometry `M' ≃ B` and `p ∘ f⁻¹ : B → M` a finite cover; (3) G9: in a Cauchy-compact `B`, an LTP over `M₁` is trivial (`d₁ = d`, `U = 𝐌ⁿ`: a nontrivial `U^⊥` makes every Cauchy surface non-compact, `Ω + U^⊥ = Ω`, l.3542–3543), and `M₁` is not unipotent (l.744: `Ω` a slab between null hyperplanes, no compact Cauchy surface of the quotient, l.3546–3548); (4) family (b) to (a): `π₁(M)` finitely generated (compact Cauchy surface; not in the library) and Selberg (`hSel`, `exists_finiteIndex_torsionFree_linOf`) give a further finite cover with torsion-free linear part, i.e. `IsCHTorusProduct`; (5) the composition of finite covers (finite fibres; not in mathlib at this pin)

/-- **Theorem B** (`bthm:cauclo`, l.353–359), "standard" read as Cauchy-compact Cauchy-hyperbolic
(G4), the torus product in its literal form (a) (π₁ finitely generated, Selberg, DEC-44). Under the
named externals `BarbotExternals d`, `SelbergLemma (Minkowski d)` and lemma K's data
`FlatLemmaKData` on every GH flat spacetime of dimension `d` (DEC-36, DEC-44), every maximal
Cauchy-compact GH flat spacetime `M` (`1 ≤ d`) is finitely covered by an AMGH spacetime `M₁` which
is a translation spacetime, a Misner spacetime, or a Cauchy-compact twisted product (a) of a
standard spacetime by a torus. Assembled from `barbot_A₀`, `cauclo_from_embedding` (G9),
`isCauchyComplete_of_cauchyCompact` and Rem 2.3 corrected (`absMax_of_cauchyCompact_of_mgh`);
partial (SCOPE). -/
theorem barbot_B (hE : BarbotExternals d) (hSel : SelbergLemma (Minkowski d))
    (hK : ∀ N : FlatSpacetime.{0} d, GH N → FlatLemmaKData N) (M : FlatSpacetime.{u} d)
    (hd : 1 ≤ d) (hGH : GH M) (hC : CauchyCompact M) (hM : MGH M) :
    ∃ (M₁ : FlatSpacetime.{0} d) (p : M₁ → M), IsFiniteCover d p ∧
      AMGH (CauchyCompleteClass d) M₁ ∧
      (IsTranslationSpacetime M₁ ∨ IsMisnerFamily d M₁ ∨
        (IsCHTorusProduct M₁ ∧ CauchyCompact M₁)) := by
  have hCC := isCauchyComplete_of_cauchyCompact M hGH hC
  obtain ⟨M', p, hp, Γ, Ω, hcv, B, hq, ⟨f, hf⟩, d₁, hd₁, M₁, hM₁, hltp⟩ :=
    barbot_A₀ hE M hd hGH hCC
  obtain ⟨M₁', q, hq', hmod, hGH', hC', hM'⟩ :=
    cauclo_from_embedding hSel hK M hGH hC hM hp hcv hq hf hd₁ hM₁ hltp
  exact ⟨M₁', q, hq', ⟨hGH', isCauchyComplete_of_cauchyCompact M₁' hGH' hC',
    (absMax_of_cauchyCompact_of_mgh hK M₁' hGH' hC' hM').mono fun _ _ => trivial⟩, hmod⟩

/-! ## §9 The gx export: equality (§11.3) -/

section Equality

variable {X M N : Type*} [TopologicalSpace X] [ChartedSpace (Minkowski d) X]
  [TopologicalSpace M] [ChartedSpace (Minkowski d) M]
  [TopologicalSpace N] [ChartedSpace (Minkowski d) N]

/-- **Cancelling an isometric embedding on the left**: if `h ∘ f` is a local isometry and `h` an
isometric embedding, `f` is a local isometry. -/
theorem IsLocalIsometry.of_comp_left {f : X → M} {h : M → N} (hh : IsIsometricEmbedding d h)
    (hhf : IsLocalIsometry d (h ∘ f)) : IsLocalIsometry d f := by
  have hfc : Continuous f := hh.isOpenEmbedding.isEmbedding.continuous_iff.2 hhf.1
  obtain ⟨-, hhf'⟩ := isLocalIsometry_iff_eventually.1 hhf
  obtain ⟨-, hh'⟩ := isLocalIsometry_iff_eventually.1 hh.1
  refine isLocalIsometry_iff_eventually.2 ⟨hfc, fun x => ?_⟩
  obtain ⟨g₁, hg₁⟩ := hhf' x
  obtain ⟨g₂, hg₂⟩ := hh' (f x)
  refine ⟨g₂⁻¹ * g₁, ?_⟩
  filter_upwards [hg₁, hfc.continuousAt.eventually hg₂] with y h1 h2
  simp only [comp_apply] at h1
  rw [mul_smul, ← h1, h2, inv_smul_smul]

/-- **Descending a local isometry along a surjective local isometry**: if `q` is a surjective
local isometry and `f ∘ q` a local isometry, `f` is a local isometry. -/
theorem IsLocalIsometry.of_comp_right {q : X → M} {f : M → N} (hq : IsLocalIsometry d q)
    (hqs : Surjective q) (hfq : IsLocalIsometry d (f ∘ q)) : IsLocalIsometry d f := by
  have hfc : Continuous f :=
    (hq.isOpenMap.isQuotientMap hq.continuous hqs).continuous_iff.2 hfq.1
  obtain ⟨-, hfq'⟩ := isLocalIsometry_iff_eventually.1 hfq
  obtain ⟨-, hq'⟩ := isLocalIsometry_iff_eventually.1 hq
  refine isLocalIsometry_iff_eventually.2 ⟨hfc, fun x => ?_⟩
  obtain ⟨z, rfl⟩ := hqs x
  obtain ⟨g₁, hg₁⟩ := hfq' z
  obtain ⟨g₂, hg₂⟩ := hq' z
  refine ⟨g₁ * g₂⁻¹, ?_⟩
  have hA : {w | chartAt (Minkowski d) (f (q z)) (f (q w)) =
      (g₁ * g₂⁻¹) • chartAt (Minkowski d) (q z) (q w)} ∈ 𝓝 z := by
    filter_upwards [hg₁, hg₂] with w h1 h2
    simp only [comp_apply] at h1
    rw [h1, h2, mul_smul, inv_smul_smul]
  filter_upwards [hq.isOpenMap.image_mem_nhds hA] with y hy
  obtain ⟨w, hw, rfl⟩ := hy
  exact hw

end Equality

/-- **The deck group acts transitively on the fibres** of the universal cover. -/
theorem UniversalCover.exists_deck_apply_eq {Y : Type*} [TopologicalSpace Y] {y₀ : Y}
    (c c' : UniversalCover Y y₀) (h : UniversalCover.proj Y y₀ c = UniversalCover.proj Y y₀ c') :
    ∃ γ : Deck (UniversalCover.proj Y y₀), γ.1 c = c' := by
  obtain ⟨a, ca⟩ := c
  obtain ⟨b, cb⟩ := c'
  change a = b at h
  subst h
  refine ⟨⟨UniversalCover.leftMulHomeomorph (cb.trans ca.symm), rfl⟩, ?_⟩
  change (⟨a, (cb.trans ca.symm).trans ca⟩ : UniversalCover Y y₀) = ⟨a, cb⟩
  rw [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.trans_refl]

/-- **The gx export, equality** (§11.3, l.3607–3611; `docs/BARBOT-THEOREMS.md` §3, the contract
with gx), `P` parametric (DEC-45): let `(𝒟, ρ)` be a developing pair of a flat spacetime `M`, `𝒟`
injective with image in an open `Ω`, and `B = ρ(Deck)\Ω` a GH flat spacetime of class `P`. If `M` is
absolutely maximal in the class `P`, then `𝒟(M̃) = Ω`. Proof: `𝒟` descends to an isometric
embedding `M → B` (equivariance and injectivity of `𝒟`), which `AbsMax P M` makes onto, and
`𝒟(M̃)` is `ρ(Deck)`-invariant. No `sorry`. -/
theorem equality_of_absMax {P : FlatSpacetime.{u} d → Prop} (M : FlatSpacetime.{u} d) {x₀ : M}
    {D : UniversalCover M x₀ → Minkowski d} {ρ : Deck (UniversalCover.proj M x₀) →* isom d}
    (hpair : IsDevelopingPair x₀ D ρ) (hinj : Injective D) {Ω : Opens (Minkowski d)}
    (hΩ : range D ⊆ Ω) (B : FlatSpacetime.{u} d) (hB : IsQuotientOf B ρ.range Ω) (hGHB : GH B)
    (hPB : P B) (hmax : AbsMax P M) : range D = Ω := by
  letI := flatCoverChartedSpace d M x₀
  haveI := locPathConnectedSpace_of_flat d M
  haveI : PathConnectedSpace M := pathConnectedSpace_iff_connectedSpace.2 inferInstance
  have hqs : Surjective (UniversalCover.proj M x₀) := UniversalCover.proj_surjective
  have hql : IsLocalIsometry d (UniversalCover.proj M x₀) := isLocalIsometry_flatCover_proj x₀
  obtain ⟨π, -, hπl, -, hfib⟩ := hB.quot
  -- `𝒟` as a map into `Ω`
  set D' : UniversalCover M x₀ → Ω := fun z => ⟨D z, hΩ (mem_range_self z)⟩
  have hDl : IsLocalIsometry d D := isLocalIsometry_iff_eventually.2 ⟨hpair.gx.1, hpair.gx.2⟩
  have hD'l : IsLocalIsometry d D' :=
    IsLocalIsometry.of_comp_left (isIsometricEmbedding_subtype_val Ω) hDl
  -- the descended map
  set f : M → B := fun x => π (D' (surjInv hqs x))
  have key : ∀ z, f (UniversalCover.proj M x₀ z) = π (D' z) := by
    intro z
    set z' := surjInv hqs (UniversalCover.proj M x₀ z)
    obtain ⟨γ, hγ⟩ := UniversalCover.exists_deck_apply_eq z z'
      (surjInv_eq hqs (UniversalCover.proj M x₀ z)).symm
    refine ((hfib (D' z) (D' z')).2 ⟨ρ γ, ⟨γ, rfl⟩, ?_⟩).symm
    simp only [D']
    rw [← hpair.equiv, hγ]
  have hfq : f ∘ (UniversalCover.proj M x₀) = π ∘ D' := funext key
  have hfl : IsLocalIsometry d f := hql.of_comp_right hqs (hfq ▸ hπl.comp hD'l)
  have hfi : Injective f := by
    intro x x' hxx'
    obtain ⟨z, rfl⟩ := hqs x
    obtain ⟨z', rfl⟩ := hqs x'
    rw [key, key] at hxx'
    obtain ⟨_, ⟨γ, rfl⟩, hγ⟩ := (hfib _ _).1 hxx'
    have h1 : D (γ.1 z) = D z' := by rw [hpair.equiv]; exact hγ
    rw [← hinj h1]
    exact (proj_deck_apply γ z).symm
  have hfs := hmax B hGHB hPB f ⟨hfl, hfi⟩
  refine Subset.antisymm hΩ fun p hp => ?_
  obtain ⟨x, hx⟩ := hfs (π ⟨p, hp⟩)
  obtain ⟨z, rfl⟩ := hqs x
  rw [key] at hx
  obtain ⟨_, ⟨γ, rfl⟩, hγ⟩ := (hfib _ _).1 hx
  exact ⟨γ.1 z, by rw [hpair.equiv]; exact hγ⟩

/-- **Equality for `Ω(S̃)`** (§11.3 with Develop's §8): under (CC′), if `M(S) = Γ\Ω(S̃)` is a GH
flat spacetime of class `P` and `M` is absolutely maximal in `P`, then `𝒟(M̃) = Ω(S̃)`. -/
theorem range_eq_omegaS_of_absMax {P : FlatSpacetime.{u} d → Prop} (M : FlatSpacetime.{u} d)
    {x₀ : M} {D : UniversalCover M x₀ → Minkowski d}
    {ρ : Deck (UniversalCover.proj M x₀) →* isom d} {S : Set M} (hpair : IsDevelopingPair x₀ D ρ)
    (hcaus : (flatCausality d M).IsCausal) (h : DevelopsCC x₀ D S) (B : FlatSpacetime.{u} d)
    (hB : IsQuotientOf B ρ.range (omegaSOpens ρ.range (D '' (UniversalCover.proj M x₀ ⁻¹' S))))
    (hGHB : GH B) (hPB : P B) (hmax : AbsMax P M) :
    range D = omegaS ρ.range (D '' (UniversalCover.proj M x₀ ⁻¹' S)) :=
  equality_of_absMax M hpair (bprop_danom hpair hcaus h).1 (bprop_danom hpair hcaus h).2 B hB
    hGHB hPB hmax

end Causal.Flat
