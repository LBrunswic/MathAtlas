# The Barbot campaign — *Globally hyperbolic flat space-times* on the ETT library

T. Barbot, *Globally hyperbolic flat space-times*, J. Geom. Phys. 53 (2005) 123–165, arXiv
math/0402257 (`barbot_globally_2004`). Rulings: DEC-34 … DEC-38; open questions OQ-21 … OQ-23;
work packages WP-29 … WP-34. Read `docs/CAMPAIGN.md` (the protocol) and `kb/INDEX.md` first —
**kb/0024** in particular — then this file.

| what | where |
|---|---|
| the paper, labelled, read-only | `papers/barbot/legacy/labeled/GHFspace.tex`. **Line numbers in this file are those of `legacy/orig/GHFspace.tex`**; the labelled copy runs 3–45 lines later (each inserted `\label` is one line) |
| the PDF | `papers/gx/sources/math_0402257/math_0402257.pdf` |
| the ledger | `papers/barbot/ledger/LEDGER.md` — 44 statements, 5 terminal |
| the Lean | `Causal/Flat/*` (strict, namespace `Causal.Flat`), `scaffold/CausalScaffold/Flat/*` (scaffold) |
| graduation | **2026-11-02** (`docs/BARBOT-GRADUATION.md`): 93 modules moved `CausalScaffold.X` → `Causal.X` (`Flat.*` incl. `Lox/`, `Nonlox/`, `Cla/`, `Geroch/`; `Port.*`; `CompactCauchy`'s proved part, `CurvesExtend`, `Splitting`, `LemmaKBare`) — module renames only, no declaration renamed. Still scaffold: only `CausalScaffold.CompactCauchy` (the bare lemma K). The CBG work (`Causal.CBG.*`, `Causal.Flat.CBG{,Germ,Slice}`) graduated the same day, after interface round 4 and the DEC-73 split of ETT's `SubExtension` (the bare lemma K, a `sorry`) |

**Who consumes it.** gx's Section 4 (WP-28) uses Barbot's classification (DEC-26, DEC-30) and may
import `Causal` (DEC-33); this campaign proves it, gx imports it (DEC-34). Keep statements in the
generality gx needs: arbitrary dimension, no 2+1 specialisation.

## Conventions specific to this campaign

- **Dimension.** Barbot's `𝐌ⁿ` has total dimension `n`. The library's `Minkowski d =
  ℝ × EuclideanSpace ℝ (Fin d)` (`Causal/Minkowski.lean:72`) has `d` spatial dimensions: Barbot's
  `n` is `d + 1`. Every docstring says so once.
- **Signature.** Barbot uses `(−,+,…,+)`; write `minkQ (t, x) = −t² + ‖x‖²`. Time orientation is the
  `t`-coordinate: `minkowski d` is `staticCausality`, so `le ⊤ p q ↔ ‖q.2 − p.2‖ ≤ q.1 − p.1`
  (`minkowski_le_top_iff`, `:80`).
- **Isometries** are affine maps with linear part in `SO₀(1, d)` (Barbot l.469–480: orientation and
  time orientation preserved).
- **Labels** are `bthm: bprop: blem: bcor: bdef:` (kb/0024). Prose-only items (no environment in the
  paper) are cited in docstrings by section and line, e.g. "[3.M] Misner spacetimes, l.595–627",
  without a mark.
- **Defects** (DEC-27's rule, adopted here): a statement false as written is formalized in its
  strongest true form, with a counterexample where it fails, and the correction is reported as a
  finding; the row is `partial`.
- **Externals** (DEC-36) are `Prop`s named after their source (`AuslanderCarriereDalbo`, …), each with
  a non-vacuity witness (kb/0012). Never an `axiom`.

## The statement map

Classes: **T** causal / order-topological / affine in Minkowski space; **D** metric or differential;
**G** group theory; **E** external. `[x.Y]` is an unnumbered prose item.

### §2 Preliminaries (l.418–577)
- Isom(𝐌ⁿ), linear part `L` (l.469) — T.
- flat spacetime = (Isom(𝐌ⁿ), 𝐌ⁿ)-manifold (l.482) — T, `Causal/GXStructure.lean`.
- GH, Cauchy embedding, MGH (l.496–528) — T. Barbot's GH is "has a Cauchy hypersurface"; ETT's
  `GloballyHyperbolic` is causal + compact diamonds (`Causal/Properties.lean:144`), i.e. Beem–Ehrlich's
  criterion is the definition. Relate them through `Causal/Geroch.lean`.
- Rem 2.2 (l.536): the cone `{Q<0, t>0}` is MGH, its inclusion in 𝐌ⁿ is not a Cauchy embedding — T.
- Cauchy-complete (l.549) — D (DEC-35). Cauchy-compact (l.558) — T.
- Rem 2.3 `clomax` (l.569): AMGH; "CGH ⇒ AMGH" is false as written — OQ-22.

### §3 Elementary examples (prose)
- [3.T] translation spacetimes (l.584) — T.
- [3.M] Misner spacetimes (l.595–627): `2dxdy + dz²`, `Ω = {xy<0, x>0}`, `G₀ ≅ ℝⁿ⁻¹` — T; completeness D.
- [3.U] unipotent spacetimes (l.630–753): the group 𝒜, the abelian `A ≅ ℝⁿ⁻²`, components of `Ω(A)`
  are slabs, the hypersurface `S_f`, complete for suitable `f`, Cauchy — T; completeness D.
  **Gap:** the Cauchy argument checks causal geodesics only (l.726–739); prove it for inextensible
  causal curves. Typo l.696: "yᵢ = 0" should read "yᵢ = ∞".

### §4 Cauchy-hyperbolic spacetimes (l.755–1665)
- [4.J] the Penrose boundary 𝒥 ≅ 𝒮⁺ × ℝ and the action of Isom on it (l.762–849) — T. Normalisation
  slip at l.780.
- `bprop:laoucapulse` 4.2 (l.852) — T.
- `bdef:omega_lambda` 4.4, `bdef:regular_domain` 4.5 — T.
- `blem:fermons` 4.6, `bcor:closeregular` 4.7, `blem:closecool` 4.8, `blem:fermonsbis` 4.9 — T.
- `bprop:regular_iff_bounded` 4.10 — T. **Sign error**: the statement says `s < C`, the proof gives
  `s` bounded below for future regular.
- `bcor:futetpast` 4.11 — T.
- [4.CT] the cosmological time (l.1032–1059, quoted from Bonsante) — E, attempted T in wave 4.
- `bprop:lip` 4.12, `bcor:level_sets_complete` 4.13 — D.
- `bprop:regular_cauchy_complete` 4.14 — E+D.
- `bprop:agissons` 4.16 — E+D; the core is T/G.
- `bprop:admlox` 4.17 — T given the limit-set fact (E).
- `bdef:definitioncauchyhyp` 4.18 — T+G.
- [4.H] cohomology, 𝒯⁺ (l.1283–1335) — T.
- Terminal (bucket T): `blem:admissible_cone` 4.20, `bprop:tri` 4.22, `bdef:geometrically_finite` 4.24,
  `bthm:convex_cocompact` 4.25.

### §5 Around Bieberbach (l.1667–1822)
- `bthm:ausl` 5.1, `bthm:unip` 5.2 — E (cited).
- [5.B] Bieberbach — G; the light part is proved (DEC-36).
- [5.S] suspensions and twisted products, Rem 5.3, Rem 5.4 — T/G.
- `blem:suspendre` 5.5 — T.

### §6 Classification of isometries (l.1824–1993, prose)
- [6.N] normal forms through `p = L(g) − id` (`ker p = (Im p)^⊥`) — T.
- [6.U] the unipotent trichotomy linear / tangent / transverse — T.
- [6.P] the parabolic case — T. Typo l.1851.

### §7 Achronal domains (l.1995–2185, prose)
- `Ω_g = {x : ∀ q ∈ ℤ, |gᵠx − x|² > 0}` (l.1997) — T.
- [7.E] elliptic, [7.L] loxodromic, [7.P] parabolic — T. **[7.L] is inaccurate**: when `τ ≠ 0` the
  points with `xy = 0` also qualify, so `Ω_g = {xy ≤ 0}` is not open; the later use takes the interior.
- `blem:paranongh` 7.1 (l.2149) — T.

### §8 Spacelike hypersurfaces (l.2187–2530)
- `bprop:project` 8.1 — **D: completeness is spent here**.
- `bcor:quo` 8.2 — T given 8.1.
- [8.G] the hypersurface is an achronal graph (l.2278) — T.
- `bcor:quoiso` 8.3 — **D: the second, independent use of completeness**; the proof is "completely
  similar" and sketchy.
- `bcor:abel` 8.4 — G; a step is under-justified, since Δ need not be Γ-invariant.
- `bdef:U_g` 8.5, `blem:SdanU` 8.6, `bdef:omega_gamma` 8.7, Rems 8.8–8.9 — T.
- `bprop:ghyp` 8.10 — T, since GH is ETT's definition.
- `bprop:splitting` 8.11 — E, Geroch; ETT's (iii)⇒(i) is a sorry.
- `bprop:danom` 8.12 — T. **Gap:** the slices `S̃ × {t}` are not known to be complete or achronal
  in 𝐌ⁿ; repair it causally (DEC-35).
- Rem 8.13 — T.

### §9 The nonloxodromic case (l.2532–3093)
- `bprop:sanloxo` 9.1 — G/E (Benoist).
- [9.E] the elliptic subcase, [9.P] the parabolic set-up, [9.b] `b ≡ 0`, [9.U] the purely unipotent
  case — G+T.
- `bprop:limites` 9.3, `bprop:extension` 9.5 — T (linear algebra).
- [9.A] the conclusion — T.

### §10 The loxodromic case (l.3095–3432)
- `blem:sanlox` 10.1 — T.
- `blem:loxregular` 10.2 — T, with a gap: "the reader can easily check".
- `bcor:loxo_proper` 10.3 — T+E/D.
- [10.M] the Misner case — G+T.
- `bprop:U_timelike` 10.4, `bprop:LU_discrete` 10.5 — G.
- [10.G] the generic case — G+T. **Gap:** the torsion of `L(Γ)` is never addressed.

### §11 Summary, and §12
- `bthm:caucomp` Theorem A, `bthm:cauclo` Theorem B; [11.i] absolute maximality, [11.ii].
  - **Gap:** [11.i]'s unbounded unipotent case is "similar", and not written.
  - **Gap:** Theorem B's "standard spacetime" identification is asserted in a parenthesis.
- `bthm:cmc` 12.1 — terminal.

## Findings of the statement design (2026-10-31, `docs/BARBOT-THEOREMS.md`)

- **F1** — [11.i] "Misner spacetimes are absolutely maximal" is false when `Γ` has no loxodromic
  element (Γ trivial: the wedge `{t > |x₁|}` sits non-surjectively in 𝐌ⁿ); the proof assumes one.
  The Misner family carries "∃ γ ∈ Γ with nonzero boost parameter".
- **F2** — [10.G] never treats torsion in `L(Γ)`; a candidate counterexample (infinitely generated
  `π₁`) to the literal "Cauchy-hyperbolic × torus" family is in `BARBOT-THEOREMS.md` §5 G5, to be checked.
- Rem 2.3 is false as written (slab `Γ\{0<t<1}` in a translation spacetime); the corrected form needs
  **lemma K** (a closed connected spacelike hypersurface of a GH spacetime is Cauchy), which gx needs
  too.
- **F3** — [10.M], l.3320–3321: "the action on π_P⁻¹(0) is free and properly discontinuous" is false
  for Γ. In 𝐌⁴, Γ = ⟨γ₀⟩ with γ₀(x,z,y) = (e⁻¹x, R_θ z, e y), θ/π irrational, is elementary
  loxodromic and acts freely and properly on the domain, but acts on π_P⁻¹(0) by a rotation fixing 0.
  The claim holds for Γ₀ = ker a; [10.M]'s conclusion is not refuted (that example is Misner in 𝐌²).
  Found 2026-11-01, WP-34d REPORT.json.
- **F4** — [10.M], l.3264–3269: the conjugation formula holds only if α(γ) fixes the origin of Q₀; a
  loxodromic with a screw part fixes no point and its conjugates drift by n Rⁿ(I − R(γ'))u, so
  "v(γ') = 0" is unjustified as written. The conclusion is true and proved another way (translation
  lengths are conjugation-invariant, `Lox.fix_second_null`, under Bieberbach I). Also l.3287
  ("L(Γ₀) is finite") needs the U = 𝐌ⁿ reduction made just before it (Carrière–Dal'bo).
- **[10.M] carries `hBieb`** (2026-11-01): its statement was shown to imply Bieberbach I, so the named
  external is added, as in `BarbotExternals.bieberbach` and the `nonloxodromic_*` statements.

## Findings against ETT (for the author; the ETT ledger is not edited from this campaign)

- **Offered to the ETT campaign (DEC-65, 2026-11-01):** `Flat/GerochFlat.lean`'s
  `minkowski_frontier_null_measure` has exactly the statement of ETT's sorried
  `minkowski_exists_measure` (`CausalScaffold/MinkowskiMeasure.lean`, `prop:mesure_dieckmann_Lorentz`)
  and is sorry-free — the frontier of a past set meets each vertical line at most once (no Lipschitz
  graph needed), so it is null by Fubini. Not applied to the ETT file from this campaign.

- **ETT.tex:1792**, the "Moreover" of `theo:geroch_sing`: "ψ is a local diffeomorphism" needs `Σ`
  smooth and transverse to the field; for a topological Cauchy surface the replacement is "J^±(Σ)
  closed" — necessary and sufficient for the flow map to be a splitting
  (`Causal.Splitting`, `isClosed_iff_exists_isCauchySplitting`). `lem:Sigma_separe` derives
  that closedness *from* the splitting, so it cannot build it.
- On the lightlike line (ETT's BTZ-line model) `J⁺(S)∖S ≠ I⁺(S)` (`lightlikeLine_Jplus_diff_ne_Iplus`).
- **`BTZAxioms.Iplus_eq` (`Causal/SingularFlat.lean:146`, I⁺(p) = J⁺(p) ∖ S₀) is FALSE in E₀** (gx review
  of CBG/Geometry, 2026-11-01, `lean-gx/campaign/WP-28-scope/CBG-REVIEW.md` C1): in −2dτdr + dr² + r²dθ²,
  f = τ − r/2 is non-decreasing along causal and strictly increasing along timelike curves, so the radial
  null ray (s/2, s, θ₀) from p = (0,0) lies in J⁺(p) ∖ S₀ but not in I⁺(p). This refutes ETT.tex l.1351's
  "asserted without proof — verify". Proposed replacement: `Iplus_of_lt : ∀ p p' ∈ S₀, p ≤ p' → p ≠ p' →
  J⁺(p') ∖ S₀ ⊆ I⁺(p)`; downstream users to audit (`K_monotone`'s "x ∈ S, y ∉ S, x ≤ y → x ≪ y" fails
  at the same point). Theorems in ETT's strict library resting on the named `BTZAxioms` are not unsound,
  but vacuous for E₀. **The ETT strict file is not edited from this campaign** — the author rules.
  **Ruled DEC-64 ("fix it now") and applied 2026-11-02:** the field is now `Iplus_of_lt`;
  `lt_of_le_of_not_mem` is deleted (replaced by `lt_of_lt_of_le_of_not_mem`); `K_monotone`,
  `K_densite_sing`, `K_ordre` re-proved, statements unchanged; `Causality.K_monotone`'s BTZ
  hypothesis weakened to the true form; CBG's `SingularFlatAxiomsCorr` deleted (CBG asks the
  library bundle); recorded in the ETT ledger row `defi:causal_E0`.

## The spine

1. **Theorem A.**
   1. §2 + [4.J].
   2. §6 + §7.
   3. (CC′) — 8.2 — 8.5/8.6 — 8.9 — 8.10 — 8.11 — 8.12.
   4. Then the case split:
      - **no loxodromic** (9.1): [9.E], or [9.P]–[9.b]–[9.U]–9.3–9.5–[9.A];
      - **loxodromic**: 4.6/4.8/4.9 — 10.1 — 10.2 — 10.3 — [10.M], or 10.4–10.5–[10.G] (with 4.17, 4.18).
   5. [11.i].
2. **Theorem B.** The spine of A, plus "closed spacelike ⇒ Cauchy", plus "unipotent spacetimes are
   never CGH", plus [11.ii].

## (CC′) — the topological form of Cauchy-completeness (DEC-35)

The paper spends completeness in `bprop:project` and `bcor:quoiso` only; everything downstream reads
the Γ-invariant `Σ = D(S̃) ⊆ 𝐌ⁿ`. (CC′) asks that `D ∘ f̃ : S̃ → 𝐌ⁿ` be injective onto a closed
achronal `Σ` such that:

- **(a)** Σ is the graph of a 1-Lipschitz function on all of ℝᵈ, i.e. it meets every timelike line
  exactly once; and
- **(b)** for every lightlike affine hyperplane `P` with null direction `Δ₀`, `Σ ∩ P` is empty or
  meets every `Δ₀`-line in `P`.

Lemma 8.6 needs Σ strictly achronal. The bridge (paper ⇒ (CC′)) is wave 3. The models satisfy (CC′)
through explicit slices (§3) and the cosmological time (wave 4).

## The contract with gx (agreed 2026-10-31, binding)

gx's Section 4 (WP-28) imports `Causal.Flat.*` and redefines none of Minkowski space, `isom d` or
the flat causality; its BTZ models extend them. Therefore:

- `isom d`'s `MulAction` and `ContinuousConstSMul` stay **instances** (gx's analytic-action class is
  stated over them). Names in `Form`, `IsomCausal`, `Achronal`, `Penrose` are an API once graduated:
  rename only with a message to the gx session.
- **The induced length** (`LipschitzGraph` / `CauchyComplete`, DEC-35) must provide:
  (a) chart-local — the length structure of an achronal 1-Lipschitz hypersurface `Σ` of an **open**
  `V ⊆ Minkowski d`, as a length of curves in `Σ ∩ V`;
  (b) `isom`-invariance — `φ ∈ isom d` maps `Σ` to `φ(Σ)` and preserves lengths;
  (c) locality — the length of a curve depends only on `Σ` near the curve, agreeing on overlaps;
  (d) **the specialisation theorem** — for a piecewise-smooth spacelike `Σ`, the induced length is
  the classical one (DEC-31, the author's ruling for gx, holds through it);
  (e) wanted — `lengthOn Σ V : C(I, Σ ∩ V) → ℝ≥0∞` and the induced `PseudoEMetricSpace` on `Σ ∩ V`,
  so that Cauchy-complete is `CompleteSpace` of the glued metric.
  (f) **spacelikeness is point-local** — `IsSpacelikeLipschitzIn V Σ` asks, for EACH point of
  `Σ ∩ V`, a neighbourhood on which `Σ` is a `c`-Lipschitz graph with `c < 1`, `c` depending on the
  point; never one `c` uniform over `V` (near a BTZ line the slope tends to 1; gx completes the
  regular part's metric). A uniform `c` is a blocking audit finding.
- `lean-causal` never imports `lean-gx` (gx imports `Causal`, DEC-33): the universal cover and the
  developing theorem are ported from `GX.Topology.UniversalCover` / `GX.Structure.Developing` once
  they graduate, with the origin cited.

## Waves

| wave | WP | files (`scaffold/CausalScaffold/Flat/`) |
|---|---|---|
| 1 | WP-30 | `Form`, `Lorentz`, `IsomCausal`, `Achronal`, `Penrose`, `Isometries`, `AchronalDomains` |
| 2 | WP-31 | `FlatSpacetime`, `Quotient`, `Examples`, `TwistedProduct` |
| 3 | WP-32 | `UniversalCover`, `Developing`, `CauchyComplete`, `Develop` |
| 4 | WP-33 | `Externals`, `Bieberbach`, `Cosmological` |
| 5 | WP-34 | `Nonloxodromic`, `Loxodromic`, `Classification` |

The plan is `~/.claude/plans/fetch-barbot-paper-on-shiny-dusk.md`.
