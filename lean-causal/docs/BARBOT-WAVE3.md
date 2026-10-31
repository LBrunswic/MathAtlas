# Barbot wave 3 — design: LipschitzGraph, UniversalCover, Developing, CauchyComplete, Develop

A design note, written 2026-10-31 by a read-only design agent (WP-32). Line numbers refer to
`papers/barbot/legacy/labeled/GHFspace.tex` as it stands; they run about 25 lines later than
`docs/BARBOT.md`'s §7–§8 numbers. Since this was written, DEC-37's cover is no longer data: it is
ported from gx (`CausalScaffold.Port.*`, `Flat/Developing.lean`), so §2's `UniversalCoverData` is
superseded wherever the ported `Causal.UniversalCover` serves.

Current locations in the labelled file:

| item | lines |
|---|---|
| §8 | 2212 |
| Prop 8.1 | 2232–2261 |
| Cor 8.2 | 2263–2271 |
| Cor 8.3 | 2277–2290 |
| Cor 8.4 | 2292–2305 |
| graph and length remark | 2306–2319 |
| Def 8.5 | 2332–2349 |
| Lemma 8.6 | 2353–2390 |
| Def 8.7 | 2394–2400 |
| Rem 8.8 | 2403 |
| Rem 8.9 | 2411 |
| Prop 8.10 | 2420–2451 |
| Prop 8.11 | 2459–2467 |
| Prop 8.12 | 2469–2494 |
| Rem 8.13 | 2516 |
| Ω_g | 2023 |
| Rem 2.2 | 535–543 |

## 0. Defects found (DEC-27 rule)

The W-prefix keeps these apart from `BARBOT-THEOREMS.md`'s F1/F2.

- **W1 — an error in our plan, not in the paper.** "An entire acausal graph is a Cauchy surface of
  𝐌ⁿ" is false. The hyperboloid (Rem 2.2) is a counterexample: along the null line `(s, s e)`,
  `t − f = s − √(1+s²) < 0` for all `s`. The correct statements are the null-line criterion and the
  `c < 1` case.
- **W2 (l.2316–2319).** The length formula `√(1−φ'(c)²)‖c'‖` holds only for n−1 = 1. Moreover
  `φ'(c(t))` need not exist along `c`. Correct form: `√(‖x'‖² − ((φ∘x)')²) = √minkQ(γ')`.
- **W3 (pitfall).** An acausal 1-Lipschitz graph can have induced length identically 0: for d = 1,
  take `f = ∫σ` with `σ = ±1`, both signs of positive measure in every interval. Its pseudo-metric is
  complete but its topology is wrong. So completeness is asked of **uniformly spacelike**
  (locally `c < 1`) Lipschitz surfaces, with a topology-compatibility field.
- **W4 (l.2023, l.2355).** `Ω_g` must quantify over `q ≠ 0`, and `U(Γ)` over `γ ≠ 1`, since
  `U(id) = ∅`. U(g) is not open in [7.L]; only its interior is used.
- **W5 (l.2243–2261).** Prop 8.1's Cauchy-sequence step needs rectifiable paths. Repair: lift
  straight segments.
- **W6 (l.2287–2290).** Cor 8.3's "completely similar" is a sketch. A full repair is in §3.
- **W7 (l.2490–2491).** "Every nonspacelike line meets D(S̃×{t})" is false: in the hyperboloid
  quotient, null lines through the vertex miss every slice. The slices are also not known to be
  complete or achronal. Repaired below, without slices.
- **W8 (l.2443–2451).** Prop 8.10 needs the components of `int U(γ)` to be convex **and causally
  convex**, which is not stated. This is an obligation on wave 1's AchronalDomains.
- **W9 (l.2299–2305).** Cor 8.4: Γ does not act on Q(Δ), since Δ is not Γ-invariant. It is G-class.
- **W10 (ETT).** `IsCauchySurfaceOn` counts image points, so a Cauchy surface does not by itself give
  `IsCausal`. Wave-3 statements carry `IsCausal`, which ETT's GH implies.

## 1. `Flat/LipschitzGraph.lean` — the general theory of 1-Lipschitz hypersurfaces in 𝐌ⁿ

Throughout, `E := EuclideanSpace ℝ (Fin d)`. If `Achronal.lean` already has `graph`, reuse it.

### A. Graphs

```
def lgraph (f : E → ℝ) : Set (Minkowski d) := {p | p.1 = f p.2}
def timeSub (f) (p : Minkowski d) : ℝ := p.1 - f p.2
def IsStrictContraction (f) : Prop := ∀ x y, x ≠ y → |f x - f y| < dist x y
theorem isAchronal_lgraph_iff : IsAchronal (lgraph f) ↔ LipschitzWith 1 f
theorem isAcausal_lgraph_iff  : (minkowski d).IsAcausal (lgraph f) ↔ IsStrictContraction f
theorem isTimeFunction_timeSub (hf : LipschitzWith 1 f) : (minkowski d).IsTimeFunction (timeSub f)
```

`isTimeFunction_timeSub` is `staticCausality.isTimeFunction_sub`, Static.lean:1189.

### B. Cauchy criteria in 𝐌ⁿ

```
theorem isCauchyTimeFunction_timeSub_of_lt (hf : LipschitzWith c f) (hc : c < 1) :
  (minkowski d).IsCauchyTimeFunction (timeSub f)
theorem isCauchySurface_lgraph_of_lt (hf : LipschitzWith c f) (hc : c < 1) :
  (minkowski d).IsCauchySurface (lgraph f)
theorem isCauchySurface_lgraph_iff (hf : IsStrictContraction f) :
  (minkowski d).IsCauchySurface (lgraph f) ↔
    ∀ p v, v ≠ 0 → minkQ v = 0 → ∃ s : ℝ, p + s • v ∈ lgraph f      -- null-line criterion
theorem not_isCauchySurface_hyperboloid (hd : 0 < d) :
  ¬ (minkowski d).IsCauchySurface (lgraph fun x => √(1 + ‖x‖^2))     -- Rem 2.2
```

- **The `c < 1` case.** Along a causal step `ΔT ≥ (1−c)Δt` (`CausalCurveIn.dist_le`, Static:1046).
  Then use `tendsto_time_atTop/atBot` (:1069/:1094) after `Inextensible.reparam` (Cauchy:251), and
  conclude with `IsCauchyTimeFunction.isCauchySurface` (Geroch:227).
- **Criterion, ⇒.** Null lines are inextensible (`inextensible_of_unbounded`, Static:1002).
- **Criterion, ⇐.** Suppose `T∘c > 0` throughout. Then:
  1. `K := J⁻(c 0) ∩ {T ≥ 0}` is unbounded.
  2. Limits of the segments `[c(−n), c 0]` give a past causal ray inside `{T ≥ 0}`; compactness of
     the direction sphere supplies them.
  3. The ray cannot touch `T = 0`, by acausality, so `T > 0` on the whole line.
  4. That contradicts "meets every timelike line" if the line is timelike, and the hypothesis if it
     is null.

### C. Cauchy surfaces of an open `W`, reused by the rest of the wave

```
theorem segment_subset_of_isCauchySurfaceOn {W : Opens (Minkowski d)} (hΣW : Σ ⊆ W)
  (hac : (minkowski d).IsAcausal Σ) (hC : (minkowski d).IsCauchySurfaceOn W Σ)
  (hp : p ∈ W) (hq : q ∈ W) (hpq : (minkowski d).le ⊤ p q) :
  segment ℝ p q ⊆ W ∧ (minkowski d).le W p q                     -- W causally convex
theorem isCompact_Jminus_timeSub (hf : IsStrictContraction f) (hW : lgraph f ⊆ W)
  (hC : IsCauchySurfaceOn W (lgraph f)) (hz : z ∈ W) (hT : 0 ≤ timeSub f z) :
  IsCompact ((minkowski d).Jminus ⊤ {z} ∩ {q | 0 ≤ timeSub f q}) ∧
    (minkowski d).Jminus ⊤ {z} ∩ {q | 0 ≤ timeSub f q} ⊆ W       -- hub lemma; + dual
theorem ccPrime_of_isCauchySurfaceOn (h : CCPrime Σ) (hΣW : Σ ⊆ W) (hC : IsCauchySurfaceOn W Σ)
  (hΣ'W : Σ' ⊆ W) (hC' : IsCauchySurfaceOn W Σ') : CCPrime Σ'     -- (CC′) transfers
```

- **Causal convexity.** The components in W of the causal line through p and q are inextensible in W
  (`inextensible_ordConnectedComponent`, CauchyExtension:688). Each meets Σ, which the line meets at
  most once, so the components coincide. The curve is `staticCurve_segment_of_convex` (Form).
- **Hub lemma.** The ray argument of B, run in the component of the line in W.

### D. Domain of dependence

```
def dependenceDomain (C : Causality M) (W : Opens M) (S : Set M) : Set M :=
  {p ∈ W | ∀ I c, C.Inextensible W I c → p ∈ c '' I → (c '' I ∩ S).Nonempty}
theorem lgraph_subset_interior_dependenceDomain (hf : IsStrictContraction f) :
  lgraph f ⊆ interior (dependenceDomain (minkowski d) ⊤ (lgraph f))
theorem isOpen_dependenceDomain (hf : IsStrictContraction f) : IsOpen (dependenceDomain …)
theorem isCauchySurfaceOn_dependenceDomain (hf) : IsCauchySurfaceOn ⟨dependenceDomain .., _⟩ (lgraph f)
theorem dependenceDomain_hyperboloid : dependenceDomain (minkowski d) ⊤ (lgraph √(1+‖x‖²)) = {p | IsFutureTimelike p}
```

- **S ⊆ interior.** Use a cylinder: strictness plus compactness of the sphere give δ.
  - A past causal curve that reaches the cylinder wall ends with `T ≤ 0`.
  - One that stays inside has `T → −∞`.
  - In both cases the intermediate value theorem on `T∘c` (`continuousOn_Icc`, CauchyExtension:136)
    gives the meeting point.
- **Openness** comes from the hub lemma. If it proves expensive, keep `interior` throughout.
- **Library gap:** a W-relative `pastExtensible_of_tendsto` (only `exists_prepend` is used).

### E. Induced length — the gx contract (a)–(e)

```
structure IsLipschitzHypersurfaceIn (V : Opens (Minkowski d)) (Σ : Set (Minkowski d)) : Prop where
  subset : Σ ⊆ V
  achronal : ∀ p ∈ Σ, ∀ q ∈ Σ, ¬ (minkowski d).lt V p q
  locGraph : ∀ p ∈ Σ, ∃ (g : isom d) (O : Opens _) (U : Set E) (f : E → ℝ), p ∈ O ∧ O ≤ V ∧
    IsOpen U ∧ LipschitzOnWith 1 f U ∧ g • (Σ ∩ O) = (g • O) ∩ {q | q.2 ∈ U ∧ q.1 = f q.2}
def IsSpacelikeLipschitzIn V Σ : Prop  -- same, with ∃ c < 1, LipschitzOnWith c f U
noncomputable def lorentzLength (γ : ℝ → Minkowski d) (a b : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Set.Ioc a b, ENNReal.ofReal (Real.sqrt (minkQ (deriv γ t)))
noncomputable def lengthOn (Σ) (V : Opens _) (γ : C(unitInterval, ↥(Σ ∩ V))) : ℝ≥0∞ :=
  if ∃ K, LipschitzWith K (fun t => (γ t : Minkowski d)) then lorentzLength (IccExtend γ) 0 1 else ⊤
def InducedLength (Σ) (V) : Type := ↥(Σ ∩ (V : Set _))          -- type synonym
noncomputable instance : PseudoEMetricSpace (InducedLength Σ V)  -- edist = ⨅ lengthOn
theorem lorentzLength_isom (g : isom d) : lorentzLength (fun t => g • γ t) a b = lorentzLength γ a b   -- (b)
theorem lengthOn_congr … ; theorem lorentzLength_add …                                            -- (c)
theorem lengthOn_eq_integral (hγ : piecewise C¹) :
  lengthOn Σ V γ = ENNReal.ofReal (∫ t in (0:ℝ)..1, √(minkQ (deriv γ t)))          -- (d), DEC-31
theorem tendsto_chordSum (hγ : C¹) : chord sums → the integral as mesh → 0
theorem IsSpacelikeLipschitzIn.isHomeomorph_toSubtype : emetric topology = subspace topology
```

- **(b)** The derivative of `g∘γ` is `g.linear (deriv γ t)`, and `g∘γ` fails to be differentiable
  exactly where `γ` does. Then apply `lorentz.minkQ_apply`.
- **(c)** The length depends only on the curve. gx glues charts with `exists_subdivision_Icc` and
  `exists_smul_eq_of_mem_gxGroupoid`.
- **(d)** Follows from the definition and `ofReal_integral_eq_lintegral_ofReal`. **Never** define the
  length as a sup or an inf of chord sums: `√minkQ` satisfies the triangle inequality in spacelike
  planes and its reverse in timelike ones.
- **(e)** The pseudo-emetric axioms:
  - the self-distance is 0 because a constant curve has length 0;
  - symmetry by reversing the curve (`minkQ_neg`);
  - the triangle inequality by concatenation (`minkQ_smul`, additivity).

  For spacelike Σ the topology is right: `√(1−c²)‖Δx‖ ≤ d ≤ ‖Δx‖`.
- **Rademacher:** `LipschitzWith.ae_differentiableAt`.

## 2. Universal cover, deck group, developing pair

**Superseded where the port serves.** Still needed:
- the deck group's free, properly discontinuous action;
- the pulled-back flat structure, with `p` and the deck maps `IsEMorphism`s of `flatCausality`;
- `isCauchySurface_preimage (hcaus) (hS) : (flatCausality Ũ).IsCauchySurface (p ⁻¹' S)`, the second
  half of Prop 8.11 (class T);
- `ofConvex Ω Γ`, the cover of Γ\Ω for convex Ω, which is Ω itself
  (`StarConvex.contractibleSpace`);
- the lifting lemmas:
  - the maximal lift of an inextensible causal curve is inextensible;
  - lifts of nearby segments stay close.

## 3. `CauchyComplete.lean`, `Develop.lean`

Context: a flat M (T2, connected), `C := flatCausality M`, the universal cover, and the developing
pair `(D, ρ)`. Write `Ŝ := p ⁻¹' S`, `Σ := D '' Ŝ`, `Γ := ρ.range`.

### (CC′)

```
structure IsEntireAcausalGraph (Σ) : Prop where
  acausal : (minkowski d).IsAcausal Σ
  meets : ∀ p v, IsFutureTimelike v → ∃ s : ℝ, p + s • v ∈ Σ
def NullSaturated (Σ) : Prop := ∀ p ℓ, ℓ ≠ 0 → minkQ ℓ = 0 →
  (∃ q ∈ Σ, minkB (q - p) ℓ = 0) → ∀ r, minkB (r - p) ℓ = 0 → ∃ s : ℝ, r + s • ℓ ∈ Σ
structure CCPrime (Σ) : Prop where entire : IsEntireAcausalGraph Σ; nullSat : NullSaturated Σ
structure DevelopsCC (S) : Prop where
  cauchy : C.IsCauchySurface S; injOn : InjOn D Ŝ; cc : CCPrime (D '' Ŝ)
theorem ccPrime_smul (g : isom d) : CCPrime Σ → CCPrime (g • Σ)
```

### The metric notion

```
def IsCauchyComplete (M) : Prop := ∃ S, C.IsCauchySurface S ∧ IsSpacelikeLipschitz S ∧
  CompleteSpace (InducedLengthSpace S) ∧ Continuous (Subtype.val ∘ toInducedLength.symm)
```

### Prop 8.1 (`bprop:project`)

```
structure SpacelikeDevelopment (X) [TopologicalSpace X] (F : X → Minkowski d) : Prop
theorem bprop_project [ConnectedSpace X] [T2Space X] (hF : SpacelikeDevelopment F)
  (hc : CompleteSpace (PulledLength F)) (Δ) (hΔ : IsFutureTimelike Δ) : IsHomeomorph (projAlong Δ ∘ F)
```

- Boost to `Δ = e₀`.
- Lift straight segments: the lifted path's length is at most the segment's, so it is Cauchy and
  converges.
- Radial lifts give sheets, hence a covering of ℝᵈ, hence a homeomorphism.
- Consequence: Σ is a 1-Lipschitz graph, strict because a null segment cannot lie in S.

### Cor 8.2 (`bcor:quo`)

```
theorem bcor_quo (hcaus : C.IsCausal) (h : DevelopsCC S) :
  Function.Injective ρ ∧ IsPreconnected Ŝ ∧ (∀ γ, ρ γ • Σ = Σ) ∧ Γ free and properly discontinuous on Σ
```

The immersion form needs `π₁(S) → π₁(M)` data, so it is partial.

### Cor 8.3 (`bcor:quoiso`)

```
theorem bcor_quoiso (same hypotheses as bprop_project) : NullSaturated (range F)
```

Work in the frame `P₀ = {t − x₁ = c}`, `Δ₀ = (1, e₁)`, and set
`Y_c = {y ⊥ e₁ | ∃ s, f(y+se₁) − s = c}`:
- `Y_c` is open: the function is strictly decreasing, then the intermediate value theorem.
- `Y_c` is closed: the lift `y ↦ y + s(y)e₁` of a segment has `minkQ`-length equal to the segment's
  Euclidean length, so 8.1's completeness argument applies.
- `e₁^⊥` is connected, so `Y_c` is empty or everything.

### The bridge

```
theorem developsCC_of_isCauchyComplete (hcaus) (hS) (hL : IsSpacelikeLipschitz S)
  (hc : CompleteSpace (InducedLengthSpace S)) (htop) : DevelopsCC S
```

### Def 8.5, Def 8.7

```
def omegaG (g : isom d) : Set (Minkowski d) := {x | ∀ q : ℤ, q ≠ 0 → 0 < minkQ ((g ^ q) • x - x)}
noncomputable def Ug g := if IsNonspacelikeElliptic g then ∅ else if IsLinearParabolic g then (nullHyperplane (fixedLine g))ᶜ else omegaG g
def UGamma (Γ : Subgroup (isom d)) := ⋂ (γ : Γ) (_ : γ ≠ 1), Ug γ
def omegaGamma Γ := interior (UGamma Γ)
def omegaS Γ Σ x₀ := connectedComponentIn (omegaGamma Γ) x₀
```

### Lemma 8.6 (`blem:SdanU`), in pure Minkowski space

```
theorem blem_SdanU (hΣ : CCPrime Σ) (hinv : ∀ γ ∈ Γ, γ • Σ = Σ) (hfree) (hprop) :
  (∀ γ ∈ Γ, γ ≠ 1 → ¬IsNonspacelikeElliptic γ ∧ ¬IsTransverseParabolic γ) ∧ Σ ⊆ omegaGamma Γ
```

- The first part follows the paper, case by case:
  - elliptic: the fixed timelike line meets Σ, contradicting freeness;
  - linear parabolic: by `NullSaturated`;
  - transverse: by Lemma 7.1.
- The interior part is repaired, because the paper's "small convex B" is unjustified. Let
  `W := interior D(Σ)`. Suppose `y ≤ γy` for some `y ∈ W` and `γ ≠ 1`, and run the γ-invariant chain:
  - if `T` changes sign along it, acausality and freeness give a contradiction;
  - otherwise there is a fixed point in the hub compact set; properness then makes `⟨γ⟩` finite,
    which is torsion, already excluded.

### Prop 8.10 (`bprop:ghyp`)

```
theorem bprop_ghyp : let Ω := omegaS Γ Σ;
  IsOpen Ω ∧ Convex ℝ Ω ∧ (minkowski d).GloballyHyperbolicOn ⟨Ω, _⟩ ∧ (∀ γ ∈ Γ, γ • Ω = Ω) ∧
  ∀ γ ∈ Γ, γ ≠ 1 → ∀ x ∈ Ω, γ • x ≠ x ∧ ¬ (minkowski d).le ⊤ x (γ • x)
```

The components are convex and causally convex (W8). Diamonds in Ω are Minkowski diamonds
(`le_iff_of_convex`), so GH holds in ETT's sense; Beem–Ehrlich is not cited.

### Prop 8.11

`isCauchySurface_preimage` (class T). The homeomorphism `M ≃ₜ S × ℝ` (class E, through
GerochEquiv's `sorry`) is not used below.

### Prop 8.12 (`bprop:danom`), repaired

```
theorem bprop_danom (hcaus : C.IsCausal) (h : DevelopsCC S) :
  Function.Injective D ∧ range D ⊆ omegaS Γ Σ
```

1. D is injective: vertical maximal lifts meet Ŝ once (l.2475–2486).
2. D is an isomorphism onto `Ω' := range D`, so Σ is Cauchy in Ω' (`isCauchySurfaceOn_image_iff`,
   CauchyExtension:330).
3. Ω' is causally convex, by §1C.
4. Γ is free and achronal on Ω': a closed causal curve in a causal M is constant.
5. `Ω' ⊆ U(γ)`: from step 4 for `γ^q`; in the linear parabolic case, by 8.6.
6. Ω' is open and connected and contains Σ, so `Ω' ⊆ Ω(S̃)`.

No slices, no completeness of slices, no splitting.

## 4. Where the metric hypothesis is needed

- **Metric:** only 8.1, 8.3 and the bridge.
- **(CC′):** 8.2, 8.5, 8.6, 8.7, Rems 8.8–8.9, 8.10, the lift half of 8.11, 8.12, and the (CC′)
  transfer.
- **External:** the homeomorphism half of 8.11.
- Theorem A carries `IsCauchyComplete` and goes through the bridge.

## 5. Order and risks

**Order:**
1. Cover and deck lemmas.
2. LipschitzGraph A, C, E. This unblocks gx.
3. The lifting lemmas.
4. Develop from (CC′): 8.5, 8.6 (first part), 8.10, 8.12. This unblocks waves 4 and 5.
5. CauchyComplete: 8.1, 8.3, the bridge (the costliest).
6. LipschitzGraph B, D, in parallel with step 5.

**Risks:**
- **R1** Building a covering from segment lifts: about 500 lines. Reuse gx's lifting where it fits;
  a tagged `sorry` is legitimate here.
- **R2** `flatCausality` must be causally arc-connected; p, D and the deck maps must be `IsEMorphism`s.
- **R3** Wave 1: components of `int U(γ)` must be convex and causally convex, and finite-order
  isometries must be nonspacelike elliptic.
- **R4** The measure-theory API.
- **R5** The W-relative extension lemma.
- **R6** Openness of D(S).
