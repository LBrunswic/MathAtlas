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
