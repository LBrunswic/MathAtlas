# What gx's Section 4 consumes from the Barbot campaign (lean-causal), as agreed 2026-10-31

Read with `lean-causal/docs/BARBOT.md` ("The contract with gx") and `lean-causal/docs/BARBOT-WAVE3.md` §1E.
gx imports `Causal.*` only from Section 4 modules (DEC-33); GX.* names are primary, `Causal.Flat.*`
is qualified fully, never `open Causal GX` together. lean-causal never imports lean-gx.

| need | where (lean-causal) | gx must discharge |
|---|---|---|
| Minkowski base: `minkQ`, `minkB`, `lorentz d`, `isom d` (MulAction + ContinuousConstSMul instances), cone bridge `le_top_iff_minkQ`, `le_iff_of_convex` | `Causal.Flat.Form` | — (E₀ extends it) |
| `IsAnalyticAction (isom d) (Minkowski d)` | `CausalScaffold.Flat.Developing.isAnalyticAction_isom` (Causal namespace) | re-prove/bridge as `GX.IsAnalyticAction` (same proof) |
| flat developing theorem | `Flat.flat_developing_theorem` / `_unique` / `_descends` (ported from GX) | — |
| lemma K | `CausalScaffold.CompactCauchy`: `Causal.Causality.isCauchySurface_of_isLocallyCauchyTwoSided` [T2, connected, Tarentin, GH, CausallyArcConnected, J^±(p) ≠ {p}, CurvesExtend, IsCauchySplitting S₀ ψ, S compact connected, IsLocallyCauchyTwoSided S] | two-sidedness at BTZ points FROM E₀'s TOPOLOGY directly (the lemma J^+\S = I^+ fails at points with empty chronological past — `lightlikeLine_Jplus_diff_ne_Iplus`; it holds under "chronal threads": `isLocallyCauchyTwoSided_of_threads`) |
| splitting ψ : S × ℝ ≃ₜ M | `CausalScaffold.Splitting` (6968b14): `IsCausalFlow.exists_isCauchySplitting` (needs causal, causal flow φ, S Cauchy acausal, J^±(S) closed); `isClosed_Jplus_of_nhds` pointwise test | a causal flow on E₀-manifolds (time translation: causal, NOT chronal at BTZ points) and closedness of J^±(S) via the pointwise test; slices Cauchy when φ_t preserves inextensible curves (`isCauchySurface_flow_image`) |
| CurvesExtend | `CausalScaffold.CurvesExtend` (0e63fd5, 0 sorry): `exists_inextensible_of_timeFunction`, `curvesExtend_of_timeFunction` (continuous T strictly increasing along ≤) | a continuous T on E₀-manifolds strictly increasing along ≤ (the t-coordinate; the BTZ line is t-parametrised). Lemma K = `isCauchySurface_of_isLocallyCauchyTwoSided hT hG hC hJm hJp (curvesExtend_of_timeFunction hTc hTs) hψ hSc hSconn hloc` |
| cosmological time of regular domains | `Flat.Cosmological` (0 sorry): level sets Cauchy and spacelike; Bonsante Lemma 4.9 | regular-domain input to U2 |
| induced length, Cauchy-complete | `Flat.LipschitzGraph` / `Flat.CauchyComplete` (wave 3): `IsLipschitzHypersurfaceIn V Σ`, `IsSpacelikeLipschitzIn` (c < 1 POINT-LOCAL, contract item (f)), `lorentzLength`, `lengthOn Σ V`, `InducedLength Σ V` + PseudoEMetricSpace; isom-invariance, locality, piecewise-smooth specialisation (DEC-31) | glue over Reg charts, complete across BTZ points |
| Barbot exports | uniformization: D injective; D(M̃) ⊆ Ω^±(Λ); ρ(Γ) acts freely and properly discontinuously on Ω; equality `AbsMax P M → range D = Ω` (take P = True) | apply to Reg(M), absolutely maximal by `brunswic2021cauchy` Cor 2.18 (Cauchy-compact, DEC-28); Selberg under π₁ f.g. |

Findings from the Barbot side that touch gx: F1 (Misner spacetimes need a loxodromic element), F2
(torsion of L(Γ): Selberg under π₁ finitely generated), slices of a splitting are Cauchy only for a
well-chosen flow (`minkowski_skew_slice_not_isCauchySurface`).

## Barbot wave 2a (e9bcf54)

| need | where (lean-causal) | note |
|---|---|---|
| flat spacetime vocabulary: `IsLocalIsometry` (defeq Port.GXBasic's IsGXMorphism), `IsIsometricEmbedding` (DEC-45), `IsTameEmbedding`, `IsFiniteCover`, GH, BarbotGH, `IsFlatCauchyEmbedding`, MGH, `AbsMax P`, AMGH CC (CC abstract), `CauchyCompact` (compact acausal Cauchy surface) | `CausalScaffold.Flat.FlatSpacetime` (0 sorry) | universe caveat: MGH / AbsMax quantify over targets in M's own universe |
| `ClosedUnderRestriction (gxGroupoid G X)` (general G, X); `flatCausality_opens`; inclusions isometric | `CausalScaffold.Flat.FlatSpacetime` | the Causal copy; gx still adds its own for `GX.gxGroupoid` (wave 3 strict-fix) |
| Γ\Ω flat spacetime for Γ ≤ isom d free, properly discontinuous on open Ω; projection covering + local isometry; Γ-invariant Cauchy surfaces descend | `CausalScaffold.Flat.Quotient` (0 sorry) | gx's M ≅ ρ(Γ)\D(M̃) |
| 1-Lipschitz hypersurfaces: null-line criterion, causal convexity of Cauchy developments, domains of dependence | `CausalScaffold.Flat.LipschitzGraph` (1 tagged sorry) | |
| uniformization U1 | Barbot's §8 spine `Develop` (`bprop_danom` + Γ-action lemmas), in progress | |

## Barbot wave 5 (f415991)

- **Signature change:** `[T2Space M]` is an instance argument of Develop's `bprop_danom` / `holonomy_proper` /
  `ccAction_of_developsCC` and of Loxodromic's Uniformization section (without it `bprop_danom` is false:
  two copies of Mⁿ glued along {t<0}). gx's manifolds are Hausdorff.
- `Loxodromic.lean`: `uniformization_injective` (no case hypothesis); `uniformization_image` (a loxodromic in
  Γ ⇒ 𝒟(M̃) ⊆ Ω⁺(Λ(Γ)) with Λ future regular, or Ω⁻ with Λ past regular); `uniformization_properlyDiscontinuous`;
  `uniformization` (combined). **Upstream tagged sorries: `#print axioms` before relying on one.**
- `Classification.lean`: `equality_of_absMax {P}`, `range_eq_omegaS_of_absMax`.
- `Develop.lean`: `bprop_danom` 0 sorry: 𝒟 injective, range ⊆ Ω(S̃), from DevelopsCC + IsCausal + T2.

## Flat CBG (DEC-29), owned by the Barbot session in lean-causal (agreed 2026-11-01)

Abstract ETT statement of the maximal Cauchy development (existence + uniqueness), Sbierski's
dezornified order (1309.7591), with a LOCAL-MODEL interface for gx to discharge on E₀:
(i) rigidity of local isomorphisms, (ii) a Hausdorffness criterion for the glued union of
developments, (iii) the local causal facts the proof uses. Flat instance from IsAnalyticAction (isom d).
New files, no ETT marks (ETT's theo:CBG / SubExtension flagged for the ETT ledger). Interface
signatures to be sent before authoring. U1/U2 exports stay first in that session's order.

## U1/U2 verified sorry-free (gx master session, 2026-11-01 ~11:10Z)

`#print axioms` on `Causal.Flat.uniformization`, `uniformization_injective`, `uniformization_image`,
`uniformization_properlyDiscontinuous` (CausalScaffold.Flat.Loxodromic) and `equality_of_absMax`,
`range_eq_omegaS_of_absMax` (CausalScaffold.Flat.Classification): propext, Classical.choice, Quot.sound only.
Requested: a strict split (e.g. `Causal.Flat.Uniformization`) so gx's strict Section 4 never imports a scaffold.

## CBG design (DEC-59..61, e9224a5; lean-causal/docs/CBG-DESIGN.md)

- DEC-59: maximal = Sbierski's universal property (every Cauchy development maps uniquely into M̄); the form B21 Lemma 2.3 uses.
- DEC-60: CBG in the thesis framework (rigid morphisms of singular (G,X)-manifolds), not ETT §4's causal IsRigid.
- Level A abstract Geometry (Str, causality, IsMor + sheaf laws, rigidity A1, causal facts A2, germ extension A3, slices A4, both time directions); Level B local model (model Y, StructureGroupoid, ChartedSpace + HasGroupoid, rigidity, local uniqueness = thesis / B21 prop:isom).
- **gx's E₀ obligations:** model + SingularFlatAxioms; a.e. rigidity (lem:liouville); prop:isom at α = 0; slices through BTZ points both directions; K± calculus at BTZ points; second countability of E_{≥0}-manifolds; σ-compactness of J⁺(Σ)∩J⁻(p).
- Geometry's exact signatures will be sent for review after its audit. gx's next DEC: DEC-62.

## Lemma K, bare form (CausalScaffold/LemmaKBare.lean, 0 sorry) — gx's entry point

Core: connected, T2, tarentin, GH, causally arc-connected, J^±(p) ≠ {p}, Σ compact connected IsLocallyCauchy,
CurvesExtend, strict causal future and past of Σ open ⇒ Σ Cauchy (no splitting; acausality from connectedness).
**gx uses `isCauchySurface_of_isLocallyCauchyTwoSided_of_pushUp`**: past side free from push-up and Z⁺ = M
(SingularFlatAxioms); future side needs two-sidedness in charts + **J⁺(V) open for every open V**.
gx E₀ obligation: J⁺(V) open at BTZ lines (sketch: BTZ neighbourhoods of x ∈ Δ contain I⁺(p) ∪ (p,+∞),
p < x on Δ; J⁺(x) \ Δ ⊆ I⁺(x') for x' < x on Δ). Z⁻ fails at BTZ points.

## CBG Geometry approved (gx, 2026-11-01)

Revised per CBG-REVIEW C1–C4 (`SingularFlatAxiomsCorr` with `Iplus_of_lt`; SC on admissible M and `Dev`;
`secondCountable_of_cauchy`; `curvesExtend` on GH M; `localUnique_sing` strong). DEC-64 (author): ETT's strict
library is fixed the same way next. gx discharges for E₀: the corrected bundle, `secondCountable_of_cauchy` via
`IsCausalFlow.exists_isCauchySplitting`, A3's two connectedness arguments + past-side B2 + K⁺ injectivity
(A3-B-INVESTIGATION.md), J⁺(V) open at BTZ points (lemma K). Instance: Y = 𝕄 ⊕ E₀, G = a.e.-isomorphisms.

## Flat Geroch (a106584, DEC-65)

`CausalScaffold.Flat.GerochFlat.flatGerochGH : FlatGerochGH d` — every flat spacetime GH in ETT's sense (causal +
compact diamonds) has a Cauchy surface; standard axioms only. Lightweight chain (Flat/Geroch/*; no Loxodromic,
Classification, CBG). `Flat/Geroch/Reach.lean`: PushUp, Z∓, K∓ = I∓ for flatCausality. Regular-flat only:
gx must extend across BTZ points for E₀ (or apply it to Reg M where that suffices).

## CBG packages 4,5,6,9,11 (e4c0d3a) — two interface decisions by gx (2026-11-01)

- E₀ constructor: `Geometry.ofLocalModelOfGermSlice 𝔐 hA3f hA3p hA4f hA4p` (sorry-free; A3/A4 on the model as
  hypotheses), NOT `ofLocalModel` (4 tagged sorries). Gluing: `Causal.CBG.FamilyGlueData.chartedSpace`,
  `Causal.CBG.gluedChartedSpace` (+ `_of_eqOn` wrappers; nonempty pieces; transition = glueTransition).
- (1) ACCEPTED field `timeFunction` (GH ⇒ HasTimeFunction on admissible M); gx discharges on E₀ via SingularGeroch.
- (2) gx FIXES the past-side field `localUnique_sing_adherent` with the WRAP-AROUND largeness hypothesis:
  ∃ O ∋ y₀ open, ∃ r ∈ O, y₀ ≤_O r, reg ∩ I⁻_O(r) ⊆ U (point contact refuted by the cone example; the
  segment-in-closure form rejected: boosts along Δ). gx proves it for E₀ by holonomy: a loop around Δ forces
  the lift to normalise ⟨P⟩.

## Barbot Theorem A sorry-free (b09c061)

`barbot_A`, `barbot_A₀`: standard axioms, conditional on the named externals bundle BarbotExternals (DEC-36),
read under R1 (DEC-43). `loxo_elementary_misner` now takes `hBieb` (callers pass `hE.bieberbach`). gx's six
exports unchanged. Theorem B: 2 sorry leaves (`Cla.exists_capEnvelope_succ`; `Cla.maximal_of_isFiniteCover`
waits on CBG's `cbg`). gx's Section 4 uses only the six exports, not Theorem A/B directly.

## All CBG packages landed (9aaea26); interface round 2 in progress

Maximal: universality (DEC-59) proved; GH of M̄ before SC; `cbg_of_hasTimeFunctions` sorry-free (`cbg_proof`'s
one sorry = the missing timeFunction field). Flat/CBG: `flat_cbg_of` sorry-free under R1 compactness + flat A3/A4.
Finding: Sbierski's transitivity step (pdftotext l.1166–1170) needs U₁₂ ∩ ψ⁻¹(U₂₃) a CGHD, unshown; the cocycle is
proved another way. Round 2: Geometry + LocalModel gain `timeFunction`; LocalModel gains `localUnique_sing_adherent`
(wrap-around); `cbg` moves to CBG/Maximal.lean (same names, proved). **gx's E₀ instance:
`Geometry.ofLocalModelOfGermSlice` + the two new LocalModel fields (exact text to come).**

## flat_cbg sorry-free (f2d4202); interface round 3 in progress

`flat_cbg`: every flat spacetime with a Cauchy surface (or GH) has a universal maximal Cauchy development; standard
axioms (abstract `cbg` too). Round 3 applies the gx rulings: past-side clause = chronological DIAMOND with a regular
tip (`r ∈ regY ∧ y₀ ≪_O r ∧ reg ∩ I⁺_O(y₀) ∩ I⁻_O(r) ⊆ U`); SC on germExt_* / slice_*.
Reusable templates for gx's E₀ discharges:
- Flat/CBGCompact: `Causality.isCompact_Jminus_inter_of_isCauchySurface` (T2, locally compact, causal, causally
  arc-connected, closed ≤, time function, J⁻ of opens open, Σ acausal Cauchy with J^±(Σ) closed) — model-free,
  no limit curves.
- Flat/CBGGerm: Lemma 3.8's causal step, regular case (connected piece U ∩ κ⁻¹(ball ∩ open cone at c)).
- Flat/CBGSlice: Thm 3.6's slices.

## CBG interface round 3 (e6fd8ad) and gx's round-4 rulings (2026-11-02)

FromModel proves for any LocalModel: A3 at regular points (`germ_future_reg`, `germ_past_reg`); A4 from cone-slice B4
(`slice_future_of_cone` off BTZ, `slice_past_of_cone` everywhere); `diamond_clause_of_piece`.
gx accepted as Level B fields (round 4): (1) `[T2Space Y]`; (2) B4 in cone-slice form `ConeSliceFuture` (off BTZ) /
`ConeSlicePast` (everywhere), REPLACING the level-set B4; (3) type agreement ONLY at corresponding pairs (same stratum,
same component); (4) `isOpen_regY`. gx's E₀ instance additionally owes (in hA3f/hA3p/hA4f/hA4p): lem:passe_pgcd
(A3 future), an E₀ future slice off the cone (τ_q, Lemma 3.11), a regular a ∈ U ∩ I⁺(p) and I⁺(p) regular near p (A3 past);
past cone-slices at BTZ points: K = J⁺_O(y) ∩ {τ + r = c}, c slightly above τ(y) (the cap of the future cone; CORRECTED 2026-11-02 — a segment of the line, below or above y, does not inhabit `coneSlicePast`).

## Graduation (pending): CausalScaffold.X → Causal.X, 95 modules, no declaration renamed

After it lands, gx's pinned modules: Causal.{CompactCauchy, CurvesExtend, Splitting, LemmaKBare, Flat.Developing,
Flat.FlatSpacetime, Flat.Quotient, Flat.LipschitzGraph, Flat.Loxodromic, Flat.Classification, Flat.GerochFlat}
(+ Flat.Form, Flat.Cosmological, Flat.CBGCompact, Flat.Geroch.*). Step 6 (Causal.Flat.Uniformization) SKIPPED at gx's
request. Stays scaffold: CBG.*, Flat.CBG, Flat.CBGGerm, Flat.CBGSlice, the CompactCauchy stub (bare lemma K).
**Blocker for gx's strict Section 4:** CBG.* imports ETT's sorried SubExtension — requested to cut that dependency.
gx imports specific modules only, never the `Causal` root.

## Graduation LANDED (ba5ed22) — read every `CausalScaffold.X` above as `Causal.X` except:

CBG.*, Flat.CBG, Flat.CBGGerm, Flat.CBGSlice, and the stub `CausalScaffold.CompactCauchy` (bare lemma K, sorry), which
stay in the scaffold until round 4 + DEC-73 (SubExtension split, GXSingular graduated). Note: commit 82ee40f does not
build (renames without content); base nothing on it. TODO (gx, after wave 4b): update the docstring mention at
GX/Structure/Basic.lean:263 to the Causal.* path.

## CBG GRADUATED (259242f) — gx's E₀ obligations, final form (round 4)

Imports for gx's strict Section 4: `Causal.CBG.{Geometry, FromModel, Maximal, …}`, `Causal.Flat.CBG`; `Causal.SubExtension`
(sorry-free part, DEC-73), `Causal.GXSingular`. `cbg`, `flat_cbg`: standard axioms.
LocalModel fields gx discharges for Y = 𝕄 ⊕ E₀: `[t2Y : T2Space Y]`; `isOpen_regY`; `dense_regY` (accepted);
`typeAgreement` (BTZ y₀ excluded; U may contain singular points); `coneSliceFuture` (off BTZ); `coneSlicePast`
(everywhere; at BTZ: K = the τ+r cap of J⁺_O(y)); `timeFunction`; `localUnique_sing_adherent` (diamond, regular tip);
plus the round-1/2 fields (rigid, localUnique_sing strong, localUnique_reg, regularChart, chartIso_mem, sing_mem,
singularFlatAxioms (Corr), curvesExtend on GH, isCompact_*, secondCountable_of_cauchy).
Constructor: `Geometry.ofLocalModelOfBTZ 𝔐 (hA3f : 𝔐.GermExtFutureBTZ) (hA3p : 𝔐.GermExtPastBTZ) (hA4f : 𝔐.SliceFutureBTZ)`
(A4 past has no BTZ residual). `ofLocalModelNoBTZ 𝔐 (h0 : singY 0 = ∅)` for BTZ-free models.

## DEC-64 landed (f84b69e) — SUPERSEDES every `BTZAxiomsCorr` / `SingularFlatAxiomsCorr` mention above

Strict `Causal.Causality.BTZAxioms` now carries `Iplus_of_lt` (`Iplus_eq` is gone). The Corr bundles and `toCorr` bridges
are DELETED; CBG uses the library's `BTZAxioms` / `SingularFlatAxioms`. FromModel lemmas renamed:
`BTZAxioms.Iminus_opens_eq_empty`, `.inter_Iminus_opens_subset`, `.exists_le_inter_Iminus_subset`.
`SingularFlatAxioms.lt_of_le_of_not_mem` deleted (false in E₀): use `lt_of_lt_of_le_of_not_mem`. `K_monotone` stronger.
**gx's E₀ model supplies the library `SingularFlatAxioms` (with `Iplus_of_lt`) as LocalModel's `singularFlatAxioms`.**

## SingularGeroch split (DEC-78, author) — gx's timeFunction obligation reduced

Strict (verbatim, after the split): SingularFlatSpacetime, `ModelMeasures`, `mesure_admissible`, `geroch_hypotheses*`,
`geroch_sing_i_imp_ii` (GH ⇒ Cauchy time function, strictly increasing along ≤), `geroch_sing_i_imp_iii`, `geroch_sing_split`.
Scaffold: `geroch_sing_of_stronglyCausal`. **gx's timeFunction discharge for E₀ = `SingularFlatAxioms` + `ModelMeasures`
on E₀-manifolds** (local admissible measures in causally convex charts). Template: Causal.Flat.Geroch.{ConeNull,
ChartNull, ChartMeasure} (frontier of a past set meets each vertical line at most once ⇒ null by Fubini; try on the E₀
chart minus the BTZ line). Pin: after the split's sha (f84b69e is the DEC-64 sha).

## Levin's theorem (ca2ad78, strict `Causal.LevinUtility`) — a shortcut for the timeFunction field, AFTER the next pin bump

`Causal.Causality.exists_timeFunction_of_secondCountable [T2Space M] [SecondCountableTopology M] (hT : C.Tarentin)
(hG : C.GloballyHyperbolic)` : a continuous τ, monotone, strictly increasing along ≤ (not Cauchy); no measures;
also `curvesExtend_of_secondCountable`. Exactly the body of CBG's `timeFunction` field. gx stays pinned at 731ed99 during
wave 5 (no re-pin while a wave builds); if WP-41f's ModelMeasures route proves costly, re-pin at ≥ ca2ad78 afterwards and
replace it by Levin (T2 + SC + tarentin from SingularFlatAxioms + GH).
