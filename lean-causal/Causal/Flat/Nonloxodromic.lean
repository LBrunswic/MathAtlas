import Causal.Flat.Develop
import Causal.Flat.Externals
import Causal.Flat.Bieberbach
import Causal.Flat.TwistedProduct
import Causal.Flat.Examples
import Causal.Flat.CauchyComplete
import Causal.Flat.Nonlox.EllipticBieberbach
import Causal.Flat.Nonlox.SpacelikeSpan
import Causal.Flat.Nonlox.TranslationLTP
import Causal.Flat.Nonlox.NullFrame
import Causal.Flat.Nonlox.BTrivial
import Causal.Flat.Nonlox.UnipotentRestriction
import Causal.Flat.Nonlox.UnipotentFrame
import Causal.Flat.Nonlox.UnipotentLTP
import Causal.Flat.Nonlox.UnipotentUpToFrame
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-!
# `Causal.Flat.Nonloxodromic` — Barbot §9, the nonloxodromic case

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §9 "The
nonloxodromic case" (label `nol`), lines of the **labelled** `papers/barbot/legacy/labeled/GHFspace.tex`.

* **`bprop:extension`** — `GHFspace.tex:2992` (Prop 9.5) — `bprop_extension` (with
  `bprop_extension_bounded`, `bprop_extension_top`, `bprop_extension_bot`): closed, no `sorry`.
* `bprop:limites` — `GHFspace.tex:2940` (Prop 9.3) — `bprop_limites` (in `𝐌ⁿ`),
  `bprop_limites_model`, `limites_of_leading`: proved, no `sorry`, in Barbot's coordinates for a
  fixed null frame and with the normalisation `y₋ = −y₊` as a case (partial, SCOPE).
* `bprop:sanloxo` — `GHFspace.tex:2572` (Prop 9.1) — `bprop_sanloxo`: proved from the external
  `BenoistNoLox` (DEC-36, `Flat/Externals`), refined by the trichotomy (partial: external); its
  third branch (null `v₀` fixed, all elliptic, which l.2621–2622 overlooks) in true form
  `exists_timelike_fixed_of_elliptic_of_null` (statement changed 2026-11-01: `Γ` discrete,
  through the hypothesis `TitsVirtuallyAbelianNull` defined here — proved downstream in
  `Flat/TitsNull` (`titsVirtuallyAbelianNull`, DEC-50, no `sorry`; TitsNull imports this
  file, so the hypothesis stays here and is discharged in `Flat/Classification`) — and the proved
  `exists_timelike_fixed_of_comm_elliptic`; the discreteness from the §8 data is
  `discreteTopology_of_ccAction` / `discreteTopology_of_developsCC`); from Barbot-cited
  externals only under `Γ_nd` of finite index (`exists_timelike_fixed_of_elliptic_of_ausl`,
  through `AuslanderCarriereDalbo` and the proved `exists_timelike_fixed_of_nilpotent_elliptic`).
* Unmarked prose: [9.E] l.2604–2617 (`omegaS_eq_univ_of_isElliptic`, `isElliptic_of_relIndex`,
  `omegaS_eq_univ_of_relIndex`, the free proper action on `𝐌ⁿ` and the quotient
  `CCAction.finite_of_fix_timelike`, `exists_isQuotientOf_omegaS_of_fix_timelike`, the null-span
  exclusion `not_null_recurrent_of_isEntireAcausalGraph`, `nonloxodromic_elliptic` — closed,
  no `sorry`, through `Flat/Nonlox/{EllipticBieberbach,SpacelikeSpan,TranslationLTP}`);
  [9.P] l.2619–2735 (`NolParam`, `act_mul`, `act_proj₀` = (∗∗), `act_of_isU` = (∗∗′));
  Rem 9.2 `choixcoord` l.2737–2760, corrected (`frameChange`, `choixcoord`); [9.b] l.2767–2787
  (`b_trivial_model`, `b_eq_zero_model`); [9.U] l.2865–2938 (`inner_comm_of_commute`,
  `isSymmOn_span`, `nu_mul`); Rem 9.4 `unipcomplet` l.2958–2963 (`unipcomplet_model`); [9.A]
  l.3101–3129 (`nolA_mul`, `choixcoord_nolA`, `unipAction_nolToMink`, `conclusion_model`,
  `nonloxodromic_parabolic` — assembled, no `sorry`: its [9.U] step
  `exists_unipotent_restriction_up_to_frame`, whose frame-free form is refuted in
  `Flat/Nonlox/UnipotentRestriction`, is proved up to a null frame change in
  `Flat/Nonlox/UnipotentUpToFrame`); `Stab(v₀)` in coordinates (`exists_nolParam`) and [9.b] in `𝐌ⁿ`
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
  the elliptic disjunct. Its third branch (null `v₀` fixed, all elliptic, no parabolic) goes to
  the elliptic output through `exists_timelike_fixed_of_elliptic_of_null`, which needs the
  hypothesis `TitsVirtuallyAbelianNull d` (of `nonloxodromic` since 2026-11-01; discharged
  downstream by `Flat/TitsNull`'s `titsVirtuallyAbelianNull d`, DEC-50, at Classification's
  `caseOutput`) and the discreteness of `Γ` (proved, `discreteTopology_of_developsCC`).

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
| [9.P] l.2621–2622: "`Γ` contains a parabolic element" (the null-fixed, all-elliptic branch it overlooks) | ⚠ added hypothesis `DiscreteTopology Γ` (`isomTopology`) and the external `TitsVirtuallyAbelianNull` in `exists_timelike_fixed_of_elliptic_of_null`; the discreteness is proved from the §8 data (`discreteTopology_of_developsCC`), so `nonloxodromic` only gains `TitsVirtuallyAbelianNull d` — no longer an external: proved in `Flat/TitsNull` (`titsVirtuallyAbelianNull`, DEC-50, no `sorry`) and discharged at Classification's `caseOutput`. Alternative (Barbot-cited externals only): `AuslanderCarriereDalbo` plus ⚠ added `Γ_nd` of finite index (`exists_timelike_fixed_of_elliptic_of_ausl`) |
| [9.b]: `γ₁` parabolic, `b(γ₀) ≠ 0` | ⚠ strengthened in `b_trivial`: `γ₁` purely unipotent (`R = id`), with `b(γ₁) = 0` (`b_eq_zero_model` proves it from `v(γ₁) ≠ 0`); ✓ carried in `Nonlox.nullY_smul_eq_of_isParabolic` (any parabolic `γ₁ = R U`), the one `nonloxodromic_parabolic` uses |
| [9.E], [9.A]: Bieberbach | carried as the external `BieberbachI` (`Flat/Bieberbach`) |
| [9.E], [9.P]: "up to finite index" (l.2575, l.2621) | ✓ carried: `Γ'.relIndex Γ ≠ 0` in both branches |
| [9.P]: no loxodromic element in `Γ` (the §9 case) | ✓ carried (`hnl` on `Γ`; used by `linOf_fix_of_relIndex`) |
| `M` a manifold | ✓ carried as `T2Space M` (Develop's Prop 8.12) |

## SCOPE (disclosed)

* **Sorries (0).** `exists_unipotent_restriction_up_to_frame` ([9.U], §4b) is PROVED
  (WP-34c, 2026-11-01) by `Nonlox.exists_unipotentRestriction_upToFrame`
  (`Flat/Nonlox/UnipotentUpToFrame`, with `Flat/Nonlox/NullSlices`), from `BieberbachI ℝᵈ` only.
  **Integration (WP-34c, 2026-11-01)**: `nonloxodromic_elliptic` is CLOSED (no `sorry`,
  axioms `propext`, `Classical.choice`, `Quot.sound`) from `Flat/Nonlox/EllipticBieberbach`
  (Bieberbach for `Γ'` in the euclidean form fixed by `L(Γ')`), `SpacelikeSpan` (the span of the
  translation vectors is spacelike) and `TranslationLTP` (`suspendre`); `nonloxodromic_parabolic`
  is assembled from `Flat/Nonlox/NullFrame` (the frame `φ` taking `v₀` to `ofNull 1 0 0`),
  `BTrivial` ([9.b] for any parabolic `γ₁`), Prop 9.3/9.5 here, `UnipotentFrame` (the frame `φ₁`
  diagonalising `T`) and `UnipotentLTP` (`Ω ⊆ Ω(S̃)`, `𝒟(M̃) ⊆ Ω`, the quotients), and
  `UnipotentUpToFrame` ([9.U] in the frame `ψ_w`); it no longer depends on `sorryAx`.
  `nonloxodromic` is assembled (no `sorry` of its own).
* **The parabolic output was restated (audit, 2026-11-01).** An earlier draft concluded that
  `M(S) = Γ''\Ω(S̃)` is an LTP over a spacetime embedding in a unipotent one; Rem 9.4 refutes it
  (finding 6), and the statement now follows l.3126 and DEC-43 R1: `B = Γ''\Ω` with
  `𝒟(M̃) ⊆ Ω ⊆ Ω(S̃)`, an LTP over a unipotent spacetime. Both branches gained the finite-index
  hypothesis `Γ'.relIndex Γ ≠ 0`, and the parabolic one `hnl` on `Γ`.
* **Coordinates.** §1–§3 work in `ℝ × E × ℝ` (`nolQ = 2xy + |z|²`) and, for `E = ℝᵈ`, in
  `𝐌ⁿ` through `nolToMink` (`minkQ_nolToMink`, `nolToMink_sub`, `nolToMink_minkToNol`):
  `v₀ = ofNull 1 0 0`, `vₙ = ofNull 0 1 0`; every isometry whose linear part fixes this `v₀` is a
  `NolParam` (`exists_nolParam`, l.2701–2713). The frame `φ ∈ Isom(𝐌ⁿ)` taking the `v₀` of `Γ`
  there is `Nonlox.exists_isom_linear_null_frame`; the §8 data transport along it
  (`CCAction.frameConj_smul`).
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
  `b_eq_zero_model`). Rotation parts `R ≠ id` (the leading term on `Fix R`) are treated in
  `Flat/Nonlox/BTrivial` (`Nonlox.nullY_smul_eq_of_isParabolic`).
* **Findings.** (1) Rem 9.2 (l.2739–2758): `vₙ + w` (`w ∈ P̄₀`) and `vₙ + a v₀` are not null
  (`frameChange_null`); the frame change is `vₙ' = vₙ + w − (|w|²/2) v₀`, under which Barbot's
  `μ' = μ + ⟨u | w⟩` holds exactly (`choixcoord`); the first bullet is not a frame change.
  (2) l.2621–2622: "`Γ` contains a parabolic element `γ₁`" does not follow from 9.1 when `L(Γ')`
  fixes a null `v₀` and is all-elliptic. (3) l.588–590 / [9.E]: spacelike translation vectors do
  not give a spacelike span (`spacelike_translations_null_span`); the reading
  `IsTranslationSpacetime` needs the latter. In [9.E] acausality of `Σ` alone excludes a null
  direction of the span once it is recurrent (`not_null_recurrent_of_isEntireAcausalGraph`;
  the example group preserves no entire acausal graph, `not_isEntireAcausalGraph_null_span`);
  recurrence for a lattice of the span (pigeonhole in the torus) is not formalized. Barbot
  states only freeness on `𝐌ⁿ` (l.2609–2610); properness, needed for the quotient, is proved
  (`CCAction.finite_of_fix_timelike`). (4) l.2659: for `γ ∈ 𝒜(v₀)` linear, `U(γ)` is
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
  defect and is replaced by this one. (7) **`exists_timelike_fixed_of_elliptic_of_null` is false
  as stated for `d ≥ 5`** (closer, 2026-11-01). In Barbot's coordinates on `Minkowski 5`
  (`P̄₀ = ℝ⁴ ≅ ℍ`), the linear isometries with `NolParam`s `(L_a, 0, 0, 0, 0)` and
  `(L_b, 0, e, 0, 0)` (`L_q z = q z`, `a, b` a free pair of unit quaternions, `e ≠ 0`) generate
  a 2-generated `Γ` with `L(Γ)` fixing `v₀ = ofNull 1 0 0`, every element elliptic (the
  horosphere map `z ↦ q z + c` has `q ≠ 1` unless `γ = 1`, and `L_q − 1` is invertible), and no
  finite-index subgroup fixing a timelike vector (a common fixed point `z` of
  `λ(γ_a^k), λ(γ_b^m)` is `0`, and `λ(γ_b^m) 0 = (L_b^m − 1)(L_b − 1)⁻¹ e ≠ 0`). It is true
  for `d ≤ 3` and when `λ(Γ)` is discrete. **Fixer, 2026-11-01 (DEC-27 statement change):** the
  lemma now carries `DiscreteTopology Γ` (the counterexample's `Γ` fixes `0`, so it is not
  discrete — its closure contains `SO(4)`-elements) and the external
  `TitsVirtuallyAbelianNull` (amenability of the `v₀`-stabiliser, Tits' alternative, compact
  solvable groups are tori; it is *not* in Barbot, whose Benoist argument yields a parabolic
  element of the Zariski closure `G₀` only), and is proved from them through
  `exists_timelike_fixed_of_comm_elliptic` (commuting elliptic linear parts fix a common
  timelike vector, proved in every `d`). The §8 data supply the discreteness
  (`discreteTopology_of_ccAction`: a group acting properly on a nonempty closed invariant `Σ`
  is discrete), so the third branch of `nonloxodromic` closes with its conclusion unchanged
  and `nonloxodromic` gains the hypothesis `TitsVirtuallyAbelianNull d` (since proved in
  `Flat/TitsNull`, DEC-50, with no `sorry`; discharged downstream). The counterexample
  itself is not formalized (it needs the freeness of a pair of unit quaternions). **Second
  fixer pass (2026-11-01), no statement changed:** (a) `λ(Γ)` discrete is not supplied by the
  call sites (only `Γ` is discrete; l.2551–2562, Barbot's own commented example, has discrete
  `Γ` and non-discrete linear part; point (3) l.2660–2675 gives `α(Γ)` discrete); (b) no
  external faithful to Prop 9.1's citation can give the conclusion, since the linear
  counterexample satisfies `BenoistNoLox` (it fixes `v₀`) and its Zariski closure contains null
  rotations (the closure of `λ(Γ)` contains `z ↦ b z` and `z ↦ b z + e`, hence the translation
  `z ↦ z + e`), so Barbot's "`G₀` admits only elliptic elements" (l.2596) is false for it; the
  Barbot-cited external that does reach the branch is Thm 5.1 (`AuslanderCarriereDalbo`, which
  uses `Γ`'s discreteness), and it does so on `Γ_nd` only: `exists_timelike_fixed_nonDiscretePart`
  (through the proved `exists_timelike_fixed_of_nilpotent_elliptic`), and the branch when
  `Γ_nd` has finite index, `exists_timelike_fixed_of_elliptic_of_ausl`. Why the counterexample
  is not cheap: a torsion one cannot exist (a torsion linear group is locally finite (Schur),
  so virtually abelian in `SO(n − 2)` (Jordan), and its commutators are elliptic translations of
  `P̄₀`, i.e. trivial; then the commuting case applies), so any counterexample contains a free
  group (Tits) and needs a formalized free pair in `SU(2)`. (8) **[9.U] in a fixed null frame is
  false** (`Flat/Nonlox/UnipotentRestriction`, `Nonlox.not_unipotentRestrictionStatement`, given
  Bieberbach in `ℝ³`): l.2881–2892's "`𝒰̄_t` does not depend on `t`" fails for an irrational
  screw motion in `𝐌⁵` (the `𝒰̄_t` are parallel axes `t w + ℝ e₂`). The assembly therefore rests on
  the corrected form `exists_unipotent_restriction_up_to_frame` (the same conclusion after SOME
  frame `ψ`; in the counterexample the null rotation `n_w` works), now PROVED in general
  (`Flat/Nonlox/UnipotentUpToFrame`): the frame is the null rotation `ψ_w` fixing `v₀` and `y`,
  `w = (p₁ − p₀)/(t₁ − t₀)` for points `pᵢ` of the Bieberbach subspaces of two slices `{y = tᵢ}`
  (then `v(γ) + R(γ) w − w` lies in the common fixed space of the rotations), which replaces
  Barbot's maximality argument.
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
paper does not treat; for discrete `Γ`, `exists_timelike_fixed_of_elliptic_of_null`). -/
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

/-! ### The branch Barbot does not treat: null `v₀` fixed, every element elliptic

Barbot's l.2621–2622 asserts that, up to finite index, `Γ` "contains a parabolic element `γ₁`"
when `L(Γ)` fixes an isotropic vector; Prop 9.1's proof (l.2585–2594) only gives a parabolic
element of the **Zariski closure** `G₀`, not of `Γ` (SCOPE, findings (2), (7)). The statement an
earlier pass sorried here — *`L(Γ)` fixing a null `v₀` and all elliptic ⇒ a finite-index
subgroup fixes a timelike vector* — is **false for `d ≥ 5`** with no further hypothesis (a free
pair of unit quaternions acting on `P̄₀ = ℝ⁴`, finding (7)). Its strongest true form here:

* `exists_timelike_fixed_of_comm_elliptic` (proved, every `d`): elliptic linear parts that
  pairwise commute fix a common timelike vector;
* `TitsVirtuallyAbelianNull` (a hypothesis here; proved in `Flat/TitsNull`,
  `titsVirtuallyAbelianNull`, DEC-50, with no `sorry`): for `Γ` **discrete** in
  `Isom(𝐌ⁿ)`, the null-fixing all-elliptic case has a finite-index subgroup with commuting
  linear parts;
* `exists_timelike_fixed_of_elliptic_of_null` (proved from the two, with `DiscreteTopology Γ`);
* `discreteTopology_of_ccAction` (proved): the §8 data supply that discreteness;
* the Barbot-cited route (fixer, 2026-11-01): `exists_timelike_fixed_of_nilpotent_elliptic`
  (proved, every `d`: a nilpotent group of elliptic linear parts fixes a common timelike
  vector), hence through `AuslanderCarriereDalbo` (Thm 5.1) the linear parts of `Γ_nd` fix one
  (`exists_timelike_fixed_nonDiscretePart`), and the branch closes when `Γ_nd` has finite index
  (`exists_timelike_fixed_of_elliptic_of_ausl`). `λ(Γ)` discrete is **not** available at the
  call site: only `Γ` is discrete (Barbot's own commented example l.2551–2562 is a discrete
  group with non-discrete linear part), and point (3), l.2660–2675, makes `α(Γ)` discrete, not
  `λ(Γ)`. -/

/-- `W ∩ W^⊥ = 0` for a subspace `W` containing a timelike vector. -/
theorem disjoint_minkOrth_of_timelike {W : Submodule ℝ (Minkowski d)} {t : Minkowski d}
    (ht : t ∈ W) (htq : minkQ t < 0) : Disjoint W (minkOrth W) := by
  rw [Submodule.disjoint_def]
  intro w hw hw'
  by_contra h0
  have h1 : minkB t w = 0 := hw' t ht
  have h2 : minkB w w = 0 := hw' w hw
  have h3 := minkQ_pos_of_orth_timelike htq h1 h0
  rw [minkQ_eq_minkB, h2] at h3
  exact lt_irrefl _ h3

/-- **`𝐌ⁿ = W ⊕ W^⊥`** for a subspace `W` containing a timelike vector. -/
theorem isCompl_minkOrth_of_timelike {W : Submodule ℝ (Minkowski d)} {t : Minkowski d}
    (ht : t ∈ W) (htq : minkQ t < 0) : IsCompl W (minkOrth W) := by
  rw [minkOrth, LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint minkForm_isRefl]
  exact disjoint_minkOrth_of_timelike ht htq

/-- **An elliptic `B` preserving a subspace `W` that contains a timelike vector fixes a timelike
vector of `W`**: decompose a timelike `u` fixed by `B` along `W ⊕ W^⊥`; the `W`-part `a` is
fixed (uniqueness of the decomposition) and `|a|² ≤ |u|² < 0` (`W^⊥` is spacelike). -/
theorem exists_timelike_fixed_mem_of_invariant {W : Submodule ℝ (Minkowski d)} {t : Minkowski d}
    (ht : t ∈ W) (htq : minkQ t < 0) {B : Minkowski d ≃ₗ[ℝ] Minkowski d} (hB : B ∈ lorentz d)
    (hBW : ∀ w ∈ W, B w ∈ W) (hBW' : ∀ w ∈ W, B.symm w ∈ W) (hell : IsElliptic B) :
    ∃ a ∈ W, minkQ a < 0 ∧ B a = a := by
  obtain ⟨u, hu, hBu⟩ := hell.exists_fixed_timelike hB
  have hc := isCompl_minkOrth_of_timelike ht htq
  have hu' : u ∈ W ⊔ minkOrth W := by rw [hc.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hu'
  have hQ : ∀ v, minkQ (B v) = minkQ v := fun v => lorentz.minkQ_apply hB v
  have hab0 : minkB a b = 0 := hb a ha
  have hb0 : 0 ≤ minkQ b := by
    by_cases h : b = 0
    · rw [h, minkQ_zero]
    · exact (minkQ_pos_of_orth_timelike htq (hb t ht) h).le
  have hqa : minkQ a < 0 := by
    have e := minkQ_add a b
    rw [hab, hab0] at e
    linarith [hu.2]
  have hBb : B b ∈ minkOrth W := by
    rw [mem_minkOrth]
    intro w hw
    have e := minkB_map_of_minkQ (A := (B : Minkowski d →ₗ[ℝ] Minkowski d)) hQ (B.symm w) b
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at e
    rw [e]
    exact hb _ (hBW' w hw)
  refine ⟨a, ha, hqa, ?_⟩
  have hsum : B a + B b = a + b := by rw [← map_add, hab, hBu]
  have hdiff : B a - a ∈ W ⊓ minkOrth W := by
    refine ⟨W.sub_mem (hBW a ha) ha, ?_⟩
    have e : B a - a = b - B b := by
      rw [sub_eq_sub_iff_add_eq_add, add_comm b a]; exact hsum
    rw [e]
    exact (minkOrth W).sub_mem hb hBb
  rw [hc.inf_eq_bot, Submodule.mem_bot, sub_eq_zero] at hdiff
  exact hdiff

/-- **Commuting elliptic linear parts fix a common timelike vector** (every `d`; no discreteness,
no finite generation). Induction on the dimension of a `Γ`-invariant subspace `W` containing a
timelike vector: if some `L(γ)` moves `W`, `W ∩ Fix L(γ)` is smaller, `Γ`-invariant (the linear
parts commute) and contains a timelike vector (`exists_timelike_fixed_mem_of_invariant`). -/
theorem exists_timelike_fixed_of_comm_elliptic {Γ : Subgroup (isom d)}
    (hcomm : ∀ g ∈ Γ, ∀ h ∈ Γ, linOf g * linOf h = linOf h * linOf g)
    (hell : ∀ γ ∈ Γ, IsElliptic (linOf γ)) :
    ∃ v : Minkowski d, minkQ v < 0 ∧ ∀ γ ∈ Γ, linOf γ v = v := by
  suffices H : ∀ n : ℕ, ∀ W : Submodule ℝ (Minkowski d), Module.finrank ℝ W ≤ n →
      (∀ γ ∈ Γ, ∀ w ∈ W, linOf γ w ∈ W) → (∃ t ∈ W, minkQ t < 0) →
      ∃ v ∈ W, minkQ v < 0 ∧ ∀ γ ∈ Γ, linOf γ v = v by
    obtain ⟨v, -, hv⟩ := H _ ⊤ le_rfl (fun _ _ _ _ => Submodule.mem_top)
      ⟨timeUnit d, Submodule.mem_top, by rw [minkQ_timeUnit]; norm_num⟩
    exact ⟨v, hv⟩
  intro n
  induction n with
  | zero =>
    rintro W hW - ⟨t, ht, htq⟩
    have hW0 : W = ⊥ := Submodule.finrank_eq_zero.1 (Nat.le_zero.1 hW)
    rw [hW0, Submodule.mem_bot] at ht
    rw [ht, minkQ_zero] at htq
    exact absurd htq (lt_irrefl 0)
  | succ n ih =>
    rintro W hW hinv ⟨t, ht, htq⟩
    by_cases hall : ∀ γ ∈ Γ, ∀ w ∈ W, linOf γ w = w
    · exact ⟨t, ht, htq, fun γ hγ => hall γ hγ t ht⟩
    push Not at hall
    obtain ⟨γ, hγ, w₀, hw₀, hne⟩ := hall
    set W' : Submodule ℝ (Minkowski d) := W ⊓ LinearMap.ker (pOf (linOf γ)) with hW'
    have hmem : ∀ x, x ∈ W' ↔ x ∈ W ∧ linOf γ x = x := fun x => by
      rw [hW', Submodule.mem_inf, LinearMap.mem_ker, pOf_apply, sub_eq_zero]
    have hγW' : ∀ w ∈ W, (linOf γ).symm w ∈ W := fun w hw => by
      have := hinv γ⁻¹ (Γ.inv_mem hγ) w hw
      rw [linOf_inv] at this
      exact this
    obtain ⟨a, ha, haq, hfa⟩ :=
      exists_timelike_fixed_mem_of_invariant ht htq (linOf_mem γ) (hinv γ hγ) hγW' (hell γ hγ)
    have hlt : W' < W := by
      refine lt_of_le_of_ne inf_le_left fun heq => hne ?_
      have : w₀ ∈ W' := heq ▸ hw₀
      exact ((hmem w₀).1 this).2
    have hrank : Module.finrank ℝ W' ≤ n := by
      have := Submodule.finrank_lt_finrank_of_lt hlt
      omega
    have hinv' : ∀ g ∈ Γ, ∀ w ∈ W', linOf g w ∈ W' := by
      intro g hg w hw
      rw [hmem] at hw ⊢
      refine ⟨hinv g hg w hw.1, ?_⟩
      have e := LinearEquiv.congr_fun (hcomm γ hγ g hg) w
      simp only [LinearEquiv.mul_apply] at e
      rw [e, hw.2]
    obtain ⟨v, hv, hvq, hvfix⟩ := ih W' hrank hinv' ⟨a, (hmem a).2 ⟨ha, hfa⟩, haq⟩
    exact ⟨v, ((hmem v).1 hv).1, hvq, hvfix⟩

variable (d) in
/-- **The null-fixing, all-elliptic case is virtually abelian** (not cited by Barbot — it fills
the gap of l.2621–2622). Stated here as a hypothesis-shaped `Prop`; **proved** (DEC-50) in
`Causal.Flat.TitsNull` as `titsVirtuallyAbelianNull d`, with no `sorry` (its former tagged
`sorry`, the Auslander/Cartan local step `exists_commute_screenRot_of_discrete`, is proved), and
directly for `d ≤ 2` (`titsVirtuallyAbelianNull_of_le_two`); TitsNull imports this file, so the lemmas here
keep `hT` and the discharge happens in `Flat/Classification`. For `Γ` **discrete** in `Isom(𝐌ⁿ)` (`isomTopology`,
as `AuslanderCarriereDalbo`) whose linear parts fix a nonzero null `v₀` and are all elliptic, a
finite-index subgroup has pairwise commuting linear parts. Sources and derivation: (i) the
isometries whose linear part fixes `v₀` form an amenable Lie group
(`(SO(n − 2) ⋉ ℝⁿ⁻²) ⋉ ℝⁿ`), whose closed — e.g. discrete — subgroups are amenable, hence contain
no free group of rank 2; (ii) Tits' alternative (J. Tits, *Free subgroups in linear groups*,
J. Algebra 20 (1972), Thm 1; characteristic 0, no finite generation needed): `Γ` is virtually
solvable; (iii) the closure of a solvable subgroup of the compact `SO(n − 2)` has finitely many
components and a torus as identity component, so on a finite-index `Γ₀` the rotation parts
(the action on `P̄₀ = v₀^⊥/ℝv₀`) commute; (iv) a commutator in `Γ₀` then has trivial rotation
part, so its linear part is a null rotation, unipotent, and elliptic, hence `id`. **Discreteness
cannot be dropped**: a free pair of unit quaternions acting linearly on `P̄₀ = ℝ⁴` (`d = 5`)
violates the conclusion (SCOPE, finding (7); not formalized: it needs the freeness of the pair).
Non-vacuity: `titsVirtuallyAbelianNull_zero`. -/
def TitsVirtuallyAbelianNull : Prop :=
  ∀ Γ : Subgroup (isom d), DiscreteTopology Γ → ∀ v₀ : Minkowski d, v₀ ≠ 0 → minkQ v₀ = 0 →
    (∀ γ ∈ Γ, linOf γ v₀ = v₀) → (∀ γ ∈ Γ, IsElliptic (linOf γ)) →
    ∃ Γ' : Subgroup (isom d), Γ' ≤ Γ ∧ Γ'.relIndex Γ ≠ 0 ∧
      ∀ g ∈ Γ', ∀ h ∈ Γ', linOf g * linOf h = linOf h * linOf g

/-- **Witness (not false)**: `TitsVirtuallyAbelianNull 0` holds (Barbot's `n = 1`; `SO₀(1, 0)`
is trivial, so all linear parts commute; degenerate, as `benoistNoLox_zero`). -/
theorem titsVirtuallyAbelianNull_zero : TitsVirtuallyAbelianNull 0 :=
  fun Γ _ _ _ _ _ _ => ⟨Γ, le_rfl, by rw [Subgroup.relIndex_self]; exact one_ne_zero,
    fun g _ h _ => by rw [lorentz_zero_eq_one (linOf_mem g), lorentz_zero_eq_one (linOf_mem h)]⟩

/-- **The branch Barbot does not treat, in its true form** (l.2621–2622; DEC-27 statement change,
2026-11-01): linear parts fixing a null `v₀` and all elliptic, `Γ` **discrete** — then a
finite-index subgroup fixes a timelike vector. Through `TitsVirtuallyAbelianNull` (proved in
`Flat/TitsNull`, DEC-50) and the proved `exists_timelike_fixed_of_comm_elliptic`. Without `DiscreteTopology Γ` the
statement is false for `d ≥ 5` (SCOPE, finding (7)); it is supplied by the §8 data
(`discreteTopology_of_ccAction`). -/
theorem exists_timelike_fixed_of_elliptic_of_null (hT : TitsVirtuallyAbelianNull d)
    {Γ : Subgroup (isom d)} (hdisc : DiscreteTopology Γ) {v₀ : Minkowski d}
    (hv0 : v₀ ≠ 0) (hv : minkQ v₀ = 0) (hfix : ∀ γ ∈ Γ, linOf γ v₀ = v₀)
    (hell : ∀ γ ∈ Γ, IsElliptic (linOf γ)) :
    ∃ Γ' : Subgroup (isom d), Γ' ≤ Γ ∧ Γ'.relIndex Γ ≠ 0 ∧
      ∃ v : Minkowski d, minkQ v < 0 ∧ ∀ γ ∈ Γ', linOf γ v = v := by
  obtain ⟨Γ', hle, hidx, hcomm⟩ := hT Γ hdisc v₀ hv0 hv hfix hell
  exact ⟨Γ', hle, hidx, exists_timelike_fixed_of_comm_elliptic hcomm fun γ hγ => hell γ (hle hγ)⟩

/-- **Elliptic linear parts commuting on an invariant subspace `W₀` fix a common timelike vector of
`W₀`**, when `W₀` contains a timelike vector (the relative form of
`exists_timelike_fixed_of_comm_elliptic`, with the same induction on the dimension; the
commutation is only asked on `W₀`). -/
theorem exists_timelike_fixed_of_comm_elliptic_on {W₀ : Submodule ℝ (Minkowski d)}
    {s : Set (isom d)} (hinv : ∀ γ ∈ s, ∀ w ∈ W₀, linOf γ w ∈ W₀)
    (hinv' : ∀ γ ∈ s, ∀ w ∈ W₀, (linOf γ).symm w ∈ W₀)
    (hcomm : ∀ g ∈ s, ∀ h ∈ s, ∀ w ∈ W₀, linOf g (linOf h w) = linOf h (linOf g w))
    (hell : ∀ γ ∈ s, IsElliptic (linOf γ)) (ht : ∃ t ∈ W₀, minkQ t < 0) :
    ∃ v ∈ W₀, minkQ v < 0 ∧ ∀ γ ∈ s, linOf γ v = v := by
  suffices H : ∀ n : ℕ, ∀ W : Submodule ℝ (Minkowski d), W ≤ W₀ → Module.finrank ℝ W ≤ n →
      (∀ γ ∈ s, ∀ w ∈ W, linOf γ w ∈ W) → (∀ γ ∈ s, ∀ w ∈ W, (linOf γ).symm w ∈ W) →
      (∃ t ∈ W, minkQ t < 0) → ∃ v ∈ W, minkQ v < 0 ∧ ∀ γ ∈ s, linOf γ v = v from
    H _ W₀ le_rfl le_rfl hinv hinv' ht
  intro n
  induction n with
  | zero =>
    rintro W - hW - - ⟨t, ht, htq⟩
    have hW0 : W = ⊥ := Submodule.finrank_eq_zero.1 (Nat.le_zero.1 hW)
    rw [hW0, Submodule.mem_bot] at ht
    rw [ht, minkQ_zero] at htq
    exact absurd htq (lt_irrefl 0)
  | succ n ih =>
    rintro W hW₀ hW hinvW hinvW' ⟨t, ht, htq⟩
    by_cases hall : ∀ γ ∈ s, ∀ w ∈ W, linOf γ w = w
    · exact ⟨t, ht, htq, fun γ hγ => hall γ hγ t ht⟩
    push Not at hall
    obtain ⟨γ, hγ, w₀, hw₀, hne⟩ := hall
    set W' : Submodule ℝ (Minkowski d) := W ⊓ LinearMap.ker (pOf (linOf γ)) with hW'
    have hmem : ∀ x, x ∈ W' ↔ x ∈ W ∧ linOf γ x = x := fun x => by
      rw [hW', Submodule.mem_inf, LinearMap.mem_ker, pOf_apply, sub_eq_zero]
    obtain ⟨a, ha, haq, hfa⟩ := exists_timelike_fixed_mem_of_invariant ht htq (linOf_mem γ)
      (hinvW γ hγ) (hinvW' γ hγ) (hell γ hγ)
    have hlt : W' < W := by
      refine lt_of_le_of_ne inf_le_left fun heq => hne ?_
      have : w₀ ∈ W' := heq ▸ hw₀
      exact ((hmem w₀).1 this).2
    have hrank : Module.finrank ℝ W' ≤ n := by
      have := Submodule.finrank_lt_finrank_of_lt hlt
      omega
    have hinv₁ : ∀ g ∈ s, ∀ w ∈ W', linOf g w ∈ W' := by
      intro g hg w hw
      rw [hmem] at hw ⊢
      refine ⟨hinvW g hg w hw.1, ?_⟩
      rw [hcomm γ hγ g hg w (hW₀ hw.1), hw.2]
    have hinv₂ : ∀ g ∈ s, ∀ w ∈ W', (linOf g).symm w ∈ W' := by
      intro g hg w hw
      rw [hmem] at hw ⊢
      refine ⟨hinvW' g hg w hw.1, ?_⟩
      have e := hcomm γ hγ g hg _ (hW₀ (hinvW' g hg w hw.1))
      rw [LinearEquiv.apply_symm_apply, hw.2] at e
      have e' := congrArg (linOf g).symm e
      rw [LinearEquiv.symm_apply_apply] at e'
      exact e'.symm
    obtain ⟨v, hv, hvq, hvfix⟩ := ih W' ((inf_le_left).trans hW₀) hrank hinv₁ hinv₂
      ⟨a, (hmem a).2 ⟨ha, hfa⟩, haq⟩
    exact ⟨v, ((hmem v).1 hv).1, hvq, hvfix⟩

/-- The common fixed subspace `{w | ∀ γ ∈ s, L(γ) w = w}` of the linear parts of a set of
isometries. -/
def linFixSub (s : Set (isom d)) : Submodule ℝ (Minkowski d) where
  carrier := {w | ∀ γ ∈ s, linOf γ w = w}
  add_mem' {a b} ha hb γ hγ := by rw [map_add, ha γ hγ, hb γ hγ]
  zero_mem' γ _ := map_zero _
  smul_mem' c w hw γ hγ := by rw [map_smul, hw γ hγ]

/-- **A nilpotent group of isometries with elliptic linear parts fixes a common timelike vector**
(every `d`; no discreteness, no finite generation). Induction along the upper central series
`Z₀ = 1 ≤ Z₁ ≤ ⋯ ≤ Z_c = Γ`: the common fixed space `W_k` of `L(Z_k)` is `Γ`-invariant (`Z_k` is
normal) and contains a timelike vector; on it the linear parts of `Z_{k+1}` commute (their
commutators lie in `Z_k`, which acts trivially on `W_k`), so
`exists_timelike_fixed_of_comm_elliptic_on` gives a timelike vector of `W_{k+1}`. -/
theorem exists_timelike_fixed_of_nilpotent_elliptic {Γ : Subgroup (isom d)}
    [hN : Group.IsNilpotent Γ] (hell : ∀ γ ∈ Γ, IsElliptic (linOf γ)) :
    ∃ v : Minkowski d, minkQ v < 0 ∧ ∀ γ ∈ Γ, linOf γ v = v := by
  set Z : ℕ → Set (isom d) := fun k => Subtype.val '' (Subgroup.upperCentralSeries Γ k : Set Γ)
    with hZ
  have hinvF : ∀ k, ∀ γ ∈ Γ, ∀ w ∈ linFixSub (Z k), linOf γ w ∈ linFixSub (Z k) := by
    rintro k γ hγ w hw _ ⟨z, hz, rfl⟩
    have hz' : (⟨γ, hγ⟩ : Γ)⁻¹ * z * ((⟨γ, hγ⟩ : Γ)⁻¹)⁻¹ ∈ Subgroup.upperCentralSeries Γ k :=
      (inferInstance : (Subgroup.upperCentralSeries Γ k).Normal).conj_mem z hz _
    rw [inv_inv] at hz'
    have h1 := hw _ ⟨_, hz', rfl⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, linOf_mul, linOf_inv,
      LinearEquiv.mul_apply] at h1
    have h2 := congrArg (linOf γ) h1
    rw [show (linOf γ)⁻¹ = (linOf γ).symm from rfl, LinearEquiv.apply_symm_apply] at h2
    exact h2
  have hinvF' : ∀ k, ∀ γ ∈ Γ, ∀ w ∈ linFixSub (Z k), (linOf γ).symm w ∈ linFixSub (Z k) :=
    fun k γ hγ w hw => by
      have := hinvF k γ⁻¹ (Γ.inv_mem hγ) w hw
      rw [linOf_inv] at this
      exact this
  have hstep : ∀ k, ∃ t ∈ linFixSub (Z k), minkQ t < 0 := by
    intro k
    induction k with
    | zero =>
      refine ⟨timeUnit d, ?_, by rw [minkQ_timeUnit]; norm_num⟩
      rintro _ ⟨z, hz, rfl⟩
      rw [Subgroup.upperCentralSeries_zero] at hz
      rw [(Subgroup.mem_bot).1 hz, OneMemClass.coe_one, linOf_eq_linearPart, map_one]
      rfl
    | succ k ih =>
      obtain ⟨v, hv, hvq, hfix⟩ := exists_timelike_fixed_of_comm_elliptic_on (W₀ := linFixSub (Z k))
        (s := Z (k + 1))
        (fun γ ⟨z, _, hzγ⟩ => hzγ ▸ hinvF k z z.2)
        (fun γ ⟨z, _, hzγ⟩ => hzγ ▸ hinvF' k z z.2)
        (by
          rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ w hw
          have hc := (Subgroup.mem_upperCentralSeries_succ_iff.1 ha) b
          rw [commutatorElement_def] at hc
          have hab : (a : isom d) * b = ((a * b * a⁻¹ * b⁻¹ : Γ) : isom d) * (b * a) := by
            simp [mul_assoc]
          have e1 := congrArg (fun g => linOf g w) hab
          simp only [linOf_mul, LinearEquiv.mul_apply] at e1
          rw [e1]
          have hm : linOf (b : isom d) (linOf (a : isom d) w) ∈ linFixSub (Z k) :=
            hinvF k b b.2 _ (hinvF k a a.2 w hw)
          exact hm _ ⟨_, hc, rfl⟩)
        (fun γ ⟨z, _, hzγ⟩ => hzγ ▸ hell z z.2) ih
      exact ⟨v, fun γ hγ => hfix γ hγ, hvq⟩
  obtain ⟨n, hn⟩ := hN.nilpotent'
  obtain ⟨v, hv, hvq⟩ := hstep n
  refine ⟨v, hvq, fun γ hγ => hv γ ⟨⟨γ, hγ⟩, ?_, rfl⟩⟩
  rw [hn]; exact Subgroup.mem_top _

/-- **Through Auslander–Carrière–Dal'bo** (`bthm:ausl`, Thm 5.1, cited by Barbot; the external
`AuslanderCarriereDalbo`, `Flat/Externals`): for `Γ` discrete with elliptic linear parts, the
linear parts of the non-discrete part `Γ_nd = L⁻¹(G₀ ∩ L(Γ))` (l.1702–1703) fix a common
timelike vector — `Γ_nd` is nilpotent (Thm 5.1) and `exists_timelike_fixed_of_nilpotent_elliptic`.
No null vector is needed. -/
theorem exists_timelike_fixed_nonDiscretePart (hA : AuslanderCarriereDalbo d)
    {Γ : Subgroup (isom d)} (hdisc : DiscreteTopology Γ)
    (hell : ∀ γ ∈ Γ, IsElliptic (linOf γ)) :
    ∃ v : Minkowski d, minkQ v < 0 ∧ ∀ γ ∈ nonDiscretePart Γ, linOf γ v = v := by
  haveI := (hA Γ hdisc).2
  exact exists_timelike_fixed_of_nilpotent_elliptic fun γ hγ => hell γ (nonDiscretePart_le Γ hγ)

/-- **The branch l.2621–2622 overlooks, from externals Barbot cites** (option (b) of the
2026-11-01 fixer dispatch; DEC-27): `Γ` discrete with elliptic linear parts **and `Γ_nd` of
finite index in `Γ`** — i.e. `L(Γ)` meets finitely many components of its closure — has a
finite-index subgroup (`Γ_nd` itself) whose linear parts fix a timelike vector. The added
hypothesis is exactly the gap: Benoist (Prop 9.1's citation) cannot fill it (the linear
counterexample of SCOPE finding (7) satisfies `BenoistNoLox`'s conclusion, and its Zariski
closure contains null rotations, so Barbot's step "a connected group of elliptic elements is
compact", l.2596–2597, does not fire), and Thm 5.1 controls `Γ_nd` only. Without it, the branch
goes through `exists_timelike_fixed_of_elliptic_of_null` and the non-Barbot
`TitsVirtuallyAbelianNull`. -/
theorem exists_timelike_fixed_of_elliptic_of_ausl (hA : AuslanderCarriereDalbo d)
    {Γ : Subgroup (isom d)} (hdisc : DiscreteTopology Γ)
    (hell : ∀ γ ∈ Γ, IsElliptic (linOf γ)) (hfin : (nonDiscretePart Γ).relIndex Γ ≠ 0) :
    ∃ Γ' : Subgroup (isom d), Γ' ≤ Γ ∧ Γ'.relIndex Γ ≠ 0 ∧
      ∃ v : Minkowski d, minkQ v < 0 ∧ ∀ γ ∈ Γ', linOf γ v = v :=
  ⟨nonDiscretePart Γ, nonDiscretePart_le Γ, hfin, exists_timelike_fixed_nonDiscretePart hA hdisc hell⟩

/-- `γ ↦ γ • x` is continuous on `Isom(𝐌ⁿ)` (`isomTopology`). -/
theorem continuous_isom_smul_apply (x : Minkowski d) :
    Continuous (fun γ : isom d => γ • x) := by
  have e : (fun γ : isom d => γ • x) =
      (fun p : (Minkowski d →L[ℝ] Minkowski d) × Minkowski d => p.1 x + p.2) ∘ isomPair := by
    funext γ
    simp only [Function.comp_apply, isomPair, linToCLM, LinearMap.coe_toContinuousLinearMap']
    rw [smul_eq_lin_add]
    rfl
  rw [e]
  exact ((continuous_fst.clm_apply continuous_const).add continuous_snd).comp
    continuous_induced_dom

/-- **The §8 data make `Γ` discrete** (in `isomTopology`): a group acting properly on a
nonempty closed invariant `Σ` (here: `CCAction`, `Σ` an entire graph) is discrete. For `γ₀ ∈ Γ`
and `x ∈ Σ`, every `γ ∈ Γ` with `|γ x − γ₀ x| < 1` moves `x ∈ K` into `K`, `K` the compact
`Σ ∩ (B̄(x, 1) ∪ B̄(γ₀ x, 1))`; there are finitely many. -/
theorem discreteTopology_of_ccAction {Γ : Subgroup (isom d)} {St : Set (Minkowski d)}
    (h : CCAction Γ St) : DiscreteTopology Γ := by
  haveI : T2Space (isom d) :=
    (show IsEmbedding (isomPair (d := d)) from ⟨⟨rfl⟩, isomPair_injective⟩).t2Space
  obtain ⟨x, hx⟩ := h.nonempty
  have hcl : IsClosed St := by
    obtain ⟨g, hg, hS⟩ := isEntireAcausalGraph_iff.1 h.cc.entire
    rw [hS]; exact isClosed_graph hg.lipschitzWith.continuous
  rw [discreteTopology_iff_isOpen_singleton]
  intro γ₀
  set K : Set (Minkowski d) :=
    St ∩ Metric.closedBall x 1 ∪ St ∩ Metric.closedBall ((γ₀ : isom d) • x) 1 with hK
  have hKc : IsCompact K :=
    ((isCompact_closedBall x 1).inter_left hcl).union
      ((isCompact_closedBall _ 1).inter_left hcl)
  have hKS : K ⊆ St := union_subset inter_subset_left inter_subset_left
  have hfin := h.proper K hKS hKc
  set U : Set Γ := {γ | dist ((γ : isom d) • x) ((γ₀ : isom d) • x) < 1} with hU
  have hUo : IsOpen U :=
    isOpen_lt (((continuous_isom_smul_apply x).comp continuous_subtype_val).dist continuous_const)
      continuous_const
  have hUfin : U.Finite := by
    refine (hfin.preimage Subtype.val_injective.injOn).subset fun γ hγ => ⟨γ.2, ?_⟩
    refine ⟨(γ : isom d) • x, smul_mem_smul_set (Or.inl ⟨hx, Metric.mem_closedBall_self zero_le_one⟩),
      Or.inr ⟨h.smul_mem γ.2 hx, ?_⟩⟩
    exact Metric.mem_closedBall.2 (le_of_lt hγ)
  have hγ₀ : γ₀ ∈ U := by
    show dist _ _ < 1
    rw [dist_self]; exact zero_lt_one
  rw [← Set.sdiff_sdiff_cancel_left (singleton_subset_iff.2 hγ₀)]
  exact hUo.sdiff ((hUfin.subset sdiff_subset).isClosed)


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

/-! ### [9.E]: the free proper action on `𝐌ⁿ`, and the null-span exclusion -/

section EllipticProper

open scoped Pointwise

/-- **The lift along a timelike direction is compact** ([9.E], l.2609–2610, implicit): for an
entire acausal graph `Σ = graph g` and a future timelike `v`, the points `k + s v ∈ Σ`, `k` in a
compact `K`, lie in one compact `K' ⊆ Σ`: `g` is 1-Lipschitz, so
`|s| (v₀ − |v̄|) ≤ |k₀ − g(k̄)|`, bounded on `K`. -/
theorem exists_compact_lift_of_entire {St : Set (Minkowski d)} (hS : IsEntireAcausalGraph St)
    {v : Minkowski d} (hv : IsFutureTimelike v) {K : Set (Minkowski d)} (hK : IsCompact K) :
    ∃ K' ⊆ St, IsCompact K' ∧
      ∀ k ∈ K, ∀ s : ℝ, k + s • v ∈ St → k + s • v ∈ K' := by
  obtain ⟨g, hg, rfl⟩ := isEntireAcausalGraph_iff.1 hS
  have hgc : Continuous g := hg.lipschitzWith.continuous
  have hv' := isFutureTimelike_iff_norm_lt.1 hv
  have hcpos : 0 < v.1 - ‖v.2‖ := by linarith
  have hf : ContinuousOn (fun k : Minkowski d => k.1 - g k.2) K :=
    (continuous_fst.sub (hgc.comp continuous_snd)).continuousOn
  obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn hf
  set R := A / (v.1 - ‖v.2‖)
  refine ⟨graph g ∩ (fun p : Minkowski d × ℝ => p.1 + p.2 • v) '' (K ×ˢ Icc (-R) R),
    inter_subset_left, ((hK.prod isCompact_Icc).image (by fun_prop)).inter_left
      (isClosed_graph hgc), fun k hk s hs => ⟨hs, ⟨(k, s), ⟨hk, abs_le.1 ?_⟩, rfl⟩⟩⟩
  have h1 : (k + s • v).1 = g (k + s • v).2 := hs
  simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul] at h1
  have hl : |g (k.2 + s • v.2) - g k.2| ≤ |s| * ‖v.2‖ := by
    have := hg.lipschitzWith.dist_le_mul (k.2 + s • v.2) k.2
    rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at this
    simpa using this
  have hAk := hA k hk
  rw [Real.norm_eq_abs] at hAk
  have e : s * v.1 = (g (k.2 + s • v.2) - g k.2) - (k.1 - g k.2) := by linarith
  have hsv : |s| * v.1 ≤ |s| * ‖v.2‖ + A := by
    calc |s| * v.1 = |s * v.1| := by rw [abs_mul, abs_of_pos hv.1]
      _ ≤ _ := by rw [e]; exact (abs_sub _ _).trans (add_le_add hl hAk)
  rw [le_div_iff₀ hcpos]
  nlinarith

/-- A timelike vector fixed by a group of linear parts gives a future timelike one (`v` or `−v`). -/
theorem exists_futureTimelike_fixed {H : Subgroup (isom d)} {v : Minkowski d} (hv : minkQ v < 0)
    (hfix : ∀ γ ∈ H, linOf γ v = v) :
    ∃ w : Minkowski d, IsFutureTimelike w ∧ ∀ γ ∈ H, linOf γ w = w := by
  have h1 : v.1 ≠ 0 := by
    intro h0
    rw [minkQ, h0] at hv
    nlinarith [sq_nonneg ‖v.2‖]
  rcases lt_or_gt_of_ne h1 with h | h
  · refine ⟨-v, ⟨by simp; linarith, by rw [minkQ_neg]; exact hv⟩, fun γ hγ => ?_⟩
    rw [map_neg, hfix γ hγ]
  · exact ⟨v, ⟨h, hv⟩, hfix⟩

/-- **[9.E] Properness on all of `𝐌ⁿ`** (l.2609–2610: Barbot states only freeness; the quotient
`Γ\𝐌ⁿ` needs properness too): if `H ≤ Γ` has linear parts fixing a timelike `v`, then for every
compact `K ⊆ 𝐌ⁿ` finitely many `γ ∈ H` meet `γ K ∩ K`. The `v`-line through `k ∈ K` meets `Σ` at
`k + s v`, and `γ (k + s v) = γ k + s v`: so `γ K ∩ K ≠ ∅` gives `γ K' ∩ K' ≠ ∅` for the compact
`K' ⊆ Σ` of `exists_compact_lift_of_entire`, and Develop's properness on `Σ` applies. -/
theorem CCAction.finite_of_fix_timelike {Γ H : Subgroup (isom d)} {St : Set (Minkowski d)}
    (h : CCAction Γ St) (hle : H ≤ Γ) {v : Minkowski d} (hv : minkQ v < 0)
    (hfix : ∀ γ ∈ H, linOf γ v = v) {K : Set (Minkowski d)} (hK : IsCompact K) :
    {γ : isom d | γ ∈ H ∧ (γ • K ∩ K).Nonempty}.Finite := by
  obtain ⟨w, hw, hfw⟩ := exists_futureTimelike_fixed hv hfix
  obtain ⟨K', hK'S, hK'c, hR⟩ := exists_compact_lift_of_entire h.cc.entire hw hK
  refine (h.proper K' hK'S hK'c).subset ?_
  rintro γ ⟨hγH, _, ⟨k, hk, rfl⟩, hk'⟩
  obtain ⟨s, hs⟩ := h.cc.entire.meets k w hw
  have hγs : γ • (k + s • w) = γ • k + s • w := by rw [isom_smul_add_smul, hfw γ hγH]
  have h2 : γ • k + s • w ∈ St := hγs ▸ h.smul_mem (hle hγH) hs
  exact ⟨hle hγH, γ • (k + s • w), smul_mem_smul_set (hR k hk s hs), hγs ▸ hR _ hk' s h2⟩

/-- **[9.E] Freeness on all of `𝐌ⁿ`** (l.2609–2610), for `H ≤ Γ` with linear parts fixing a
timelike `v`: a fixed `x` gives the fixed point `x + s v ∈ Σ`. -/
theorem CCAction.free_of_fix_timelike {Γ H : Subgroup (isom d)} {St : Set (Minkowski d)}
    (h : CCAction Γ St) (hle : H ≤ Γ) {v : Minkowski d} (hv : minkQ v < 0)
    (hfix : ∀ γ ∈ H, linOf γ v = v) {γ : isom d} (hγ : γ ∈ H) (h1 : γ ≠ 1)
    (x : Minkowski d) : γ • x ≠ x := by
  intro hx
  obtain ⟨w, hw, hfw⟩ := exists_futureTimelike_fixed hv hfix
  obtain ⟨s, hs⟩ := h.cc.entire.meets x w hw
  exact h.free γ (hle hγ) h1 _ hs (by rw [isom_smul_add_smul, hfw γ hγ, hx])

/-- Every subgroup of `Isom(𝐌ⁿ)` preserves `⊤`. -/
theorem invariant_top_of_subgroup (H : Subgroup (isom d)) :
    FlatQuotient.Invariant H (⊤ : TopologicalSpace.Opens (Minkowski d)) :=
  ⟨fun _ _ _ => trivial⟩

/-- `CCAction.finite_of_fix_timelike` in mathlib's form, on the subtype `⊤`. -/
theorem CCAction.properlyDiscontinuousSMul_top_of_fix_timelike {Γ H : Subgroup (isom d)}
    {St : Set (Minkowski d)} (h : CCAction Γ St) (hle : H ≤ Γ) {v : Minkowski d}
    (hv : minkQ v < 0) (hfix : ∀ γ ∈ H, linOf γ v = v) :
    letI := invariant_top_of_subgroup H
    ProperlyDiscontinuousSMul H (⊤ : TopologicalSpace.Opens (Minkowski d)) := by
  letI := invariant_top_of_subgroup H
  refine ⟨fun {K L} hK hL => ?_⟩
  have hc : IsCompact ((Subtype.val '' K ∪ Subtype.val '' L : Set (Minkowski d))) :=
    (hK.image continuous_subtype_val).union (hL.image continuous_subtype_val)
  refine ((h.finite_of_fix_timelike hle hv hfix hc).preimage
    Subtype.val_injective.injOn).subset ?_
  rintro γ ⟨_, ⟨k, hk, rfl⟩, hl⟩
  refine ⟨γ.2, (γ : isom d) • (k : Minkowski d),
    smul_mem_smul_set (Or.inl ⟨k, hk, rfl⟩), Or.inr ⟨_, hl, rfl⟩⟩

/-- `CCAction.free_of_fix_timelike` in mathlib's form, on the subtype `⊤`. -/
theorem CCAction.isCancelSMul_top_of_fix_timelike {Γ H : Subgroup (isom d)}
    {St : Set (Minkowski d)} (h : CCAction Γ St) (hle : H ≤ Γ) {v : Minkowski d}
    (hv : minkQ v < 0) (hfix : ∀ γ ∈ H, linOf γ v = v) :
    letI := invariant_top_of_subgroup H
    IsCancelSMul H (⊤ : TopologicalSpace.Opens (Minkowski d)) := by
  letI := invariant_top_of_subgroup H
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro γ x hx
  by_contra h1
  exact h.free_of_fix_timelike hle hv hfix γ.2 (fun e => h1 (Subtype.ext e)) x
    (congrArg Subtype.val hx)

/-- **[9.E] The quotient `H\𝐌ⁿ` exists** (`FlatQuotient.toFlatSpacetime`), for `H ≤ Γ` with
linear parts fixing a timelike vector: item (1) of `nonloxodromic_elliptic`'s obstruction. -/
theorem CCAction.exists_isQuotientOf_top_of_fix_timelike {Γ H : Subgroup (isom d)}
    {St : Set (Minkowski d)} (h : CCAction Γ St) (hle : H ≤ Γ) {v : Minkowski d}
    (hv : minkQ v < 0) (hfix : ∀ γ ∈ H, linOf γ v = v) :
    ∃ B : FlatSpacetime.{0} d, IsQuotientOf B H ⊤ := by
  letI := invariant_top_of_subgroup H
  haveI := h.properlyDiscontinuousSMul_top_of_fix_timelike hle hv hfix
  haveI := h.isCancelSMul_top_of_fix_timelike hle hv hfix
  exact ⟨_, FlatQuotient.isQuotientOf_toFlatSpacetime H ⊤ FlatQuotient.isConnected_top⟩

/-- **[9.E] / [3.T]: a recurrent null direction excludes an invariant entire acausal graph**
(SCOPE finding 3, item (4) of `nonloxodromic_elliptic`'s obstruction). Let `Σ` be an entire
acausal graph, `p₀ ∈ Σ`, and `n` a future null vector such that, for every `ε > 0`, some
`s ≥ 1` and some `τ` with `p₀ + τ ∈ Σ` have `‖s n − τ‖ < ε`. This is impossible: writing
`Σ = graph g`, `F(s) = g(x₀ + s n̄) − g(x₀) − s n₀` satisfies `F(s) ≤ F(1) < 0` for `s ≥ 1`
(strict contraction), while `p₀ + τ ∈ Σ` and `τ ≈ s n` give `F(s) > −2ε`. The recurrence holds
whenever the translation vectors `τ` of a group preserving `Σ` form a lattice of a subspace
containing `n` (pigeonhole in the torus); only acausality is used, not (CC′)'s null saturation. -/
theorem not_null_recurrent_of_isEntireAcausalGraph {St : Set (Minkowski d)}
    (hS : IsEntireAcausalGraph St) {p₀ : Minkowski d} (hp₀ : p₀ ∈ St) {n : Minkowski d}
    (hn1 : 0 < n.1) (hn : minkQ n = 0)
    (hrec : ∀ ε > 0, ∃ s : ℝ, 1 ≤ s ∧ ∃ τ : Minkowski d, p₀ + τ ∈ St ∧ ‖s • n - τ‖ < ε) :
    False := by
  obtain ⟨g, hg, rfl⟩ := isEntireAcausalGraph_iff.1 hS
  have hlip : ∀ a b, |g a - g b| ≤ ‖a - b‖ := fun a b => by
    by_cases hab : a = b
    · subst hab; simp
    · exact (hg a b hab).le
  have hnn : ‖n.2‖ = n.1 := by
    have h0 : ‖n.2‖ ^ 2 = n.1 ^ 2 := by rw [minkQ] at hn; linarith
    have := (sq_eq_sq₀ (norm_nonneg _) hn1.le).1 h0
    exact this
  set x₀ := p₀.2
  have hp : p₀.1 = g x₀ := hp₀
  set F : ℝ → ℝ := fun s => g (x₀ + s • n.2) - g x₀ - s * n.1
  have hF1 : F 1 < 0 := by
    have hne : x₀ + n.2 ≠ x₀ := by
      intro h
      have : n.2 = 0 := by simpa using h
      rw [this, norm_zero] at hnn; linarith
    have := hg _ _ hne
    rw [add_sub_cancel_left, hnn] at this
    simp only [F, one_smul, one_mul]
    linarith [le_abs_self (g (x₀ + n.2) - g x₀)]
  have hFle : ∀ s, 1 ≤ s → F s ≤ F 1 := fun s hs => by
    have := hlip (x₀ + s • n.2) (x₀ + n.2)
    rw [show x₀ + s • n.2 - (x₀ + n.2) = (s - 1) • n.2 by rw [sub_smul, one_smul]; abel,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg (show (0:ℝ) ≤ s - 1 by linarith), hnn] at this
    simp only [F, one_smul, one_mul]
    linarith [le_abs_self (g (x₀ + s • n.2) - g (x₀ + n.2))]
  obtain ⟨s, hs, τ, hτ, hsτ⟩ := hrec (-F 1 / 2) (by linarith)
  have hτ' : g x₀ + τ.1 = g (x₀ + τ.2) := by
    have : (p₀ + τ).1 = g (p₀ + τ).2 := hτ
    simpa [hp] using this
  have h2 : ‖s • n.2 - τ.2‖ < -F 1 / 2 := (norm_snd_le (s • n - τ)).trans_lt hsτ
  have h1 : |s * n.1 - τ.1| < -F 1 / 2 := by
    have := (norm_fst_le (s • n - τ)).trans_lt hsτ
    simpa [Real.norm_eq_abs] using this
  have h3 := hlip (x₀ + s • n.2) (x₀ + τ.2)
  rw [show x₀ + s • n.2 - (x₀ + τ.2) = s • n.2 - τ.2 by abel] at h3
  have hFs := hFle s hs
  simp only [F, one_smul, one_mul] at hFs hF1 h1 h2
  linarith [neg_abs_le (g (x₀ + s • n.2) - g (x₀ + τ.2)), le_abs_self (s * n.1 - τ.1)]

/-- **The group of `spacelike_translations_null_span` preserves no entire acausal graph**:
`⟨e, w⟩` (`e = e₁`, `w = n + √2 e`, `n = e₀ + e₂` null) has every nonzero translation vector
spacelike and a degenerate span, and Dirichlet's approximation `|k √2 − j| ≤ 1/(N + 1)` makes `n`
recurrent (`k n − (k w − j e) = (j − k √2) e`), so `not_null_recurrent_of_isEntireAcausalGraph`
applies. Hence that span cannot arise from the §8 data (`CCAction`); acausality alone excludes
it. -/
theorem not_isEntireAcausalGraph_null_span {St : Set (Minkowski (d + 2))}
    (hS : IsEntireAcausalGraph St)
    (he : ∀ p ∈ St, p + spaceUnit 0 ∈ St)
    (hw : ∀ p ∈ St, p + ((timeUnit (d + 2) + spaceUnit 1) + √2 • spaceUnit 0) ∈ St)
    (hneg : ∀ p ∈ St, p - spaceUnit 0 ∈ St) : False := by
  obtain ⟨s₀, hp₀⟩ := hS.meets 0 _ (isFutureTimelike_vertical (d := d + 2))
  set e : Minkowski (d + 2) := spaceUnit 0
  set n : Minkowski (d + 2) := timeUnit (d + 2) + spaceUnit 1
  set w : Minkowski (d + 2) := n + √2 • e
  have hn : minkQ n = 0 := by
    rw [minkQ_add, minkQ_timeUnit, minkQ_spaceUnit, minkB_timeUnit_spaceUnit]; ring
  have hn1 : 0 < n.1 := by simp [n, timeUnit, spaceUnit]
  -- the translates `p + k w + m e`, `k : ℕ`, `m : ℤ`, stay in `St`
  have hmemZ : ∀ p ∈ St, ∀ m : ℤ, p + (m : ℝ) • e ∈ St := by
    intro p hp m
    induction m using Int.induction_on with
    | zero => simpa using hp
    | succ k ih =>
      have := he _ ih
      have e2 : p + (((k : ℤ) + 1 : ℤ) : ℝ) • e = p + ((k : ℤ) : ℝ) • e + e := by
        push_cast; rw [add_smul, one_smul, add_assoc]
      rw [e2]; exact this
    | pred k ih =>
      have := hneg _ ih
      have e2 : p + ((-(k : ℤ) - 1 : ℤ) : ℝ) • e = p + ((-(k : ℤ) : ℤ) : ℝ) • e - e := by
        push_cast; rw [sub_smul, one_smul, add_sub_assoc]
      rw [e2]; exact this
  have hmemN : ∀ p ∈ St, ∀ k : ℕ, p + (k : ℝ) • w ∈ St := by
    intro p hp k
    induction k with
    | zero => simpa using hp
    | succ k ih =>
      have := hw _ ih
      have e2 : p + ((k + 1 : ℕ) : ℝ) • w = p + (k : ℝ) • w + w := by
        push_cast; rw [add_smul, one_smul, add_assoc]
      rw [e2]; exact this
  refine not_null_recurrent_of_isEntireAcausalGraph hS hp₀ hn1 hn fun ε hε => ?_
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp at hN; linarith [one_div_pos.2 hε]
    · exact h
  obtain ⟨j, k, hk0, -, hjk⟩ := Real.exists_int_int_abs_mul_sub_le √2 hNpos
  obtain ⟨k', rfl⟩ : ∃ k' : ℕ, k = (k' : ℤ) := ⟨k.toNat, by omega⟩
  have hk1 : (1 : ℝ) ≤ k' := by exact_mod_cast (show 1 ≤ k' by omega)
  refine ⟨k', hk1, (k' : ℝ) • w + ((-j : ℤ) : ℝ) • e, ?_, ?_⟩
  · have := hmemZ _ (hmemN _ hp₀ k') (-j)
    simpa [add_assoc] using this
  · have e1 : (k' : ℝ) • n - ((k' : ℝ) • w + ((-j : ℤ) : ℝ) • e) =
        ((j : ℝ) - k' * √2) • e := by
      simp only [w, smul_add, smul_smul]; push_cast; rw [sub_smul, neg_smul]; abel_nf
    rw [e1, norm_smul, Real.norm_eq_abs, abs_sub_comm]
    have he1 : ‖e‖ ≤ 1 := by
      simp [e, spaceUnit, Prod.norm_def]
    calc |(k' : ℝ) * √2 - j| * ‖e‖ ≤ 1 / (N + 1) * 1 := by
          refine mul_le_mul ?_ he1 (norm_nonneg _) (by positivity)
          exact_mod_cast hjk
      _ < ε := by
          rw [mul_one, div_lt_iff₀ (by positivity)]
          rw [div_lt_iff₀ hε] at hN
          nlinarith

end EllipticProper

end Spacetime

/-! ## §4b Frames and the [9.U] step (integration of `Flat/Nonlox/*`)

Bookkeeping for the two assemblies of §5: conjugating the §8 data by a frame `φ ∈ Isom(𝐌ⁿ)`
(`CCAction.frameConj_smul`), and the [9.U] step in the corrected form that
`Flat/Nonlox/UnipotentRestriction`'s counterexample leaves open
(`exists_unipotent_restriction_up_to_frame`, proved in `Flat/Nonlox/UnipotentUpToFrame`). -/

section Frames

open scoped Pointwise

variable {d : ℕ}

private theorem nol_frameConj_mul (a b : isom d) (H : Subgroup (isom d)) :
    frameConj (a * b) H = frameConj a (frameConj b H) := by
  simp only [frameConj, Subgroup.map_map, map_mul]
  rfl

private theorem nol_frameConj_frameConj_inv (φ : isom d) (H : Subgroup (isom d)) :
    frameConj φ (frameConj φ⁻¹ H) = H := by
  rw [← nol_frameConj_mul, mul_inv_cancel, frameConj_one]

private theorem nol_frameConj_inv_frameConj (φ : isom d) (H : Subgroup (isom d)) :
    frameConj φ⁻¹ (frameConj φ H) = H := by
  rw [← nol_frameConj_mul, inv_mul_cancel, frameConj_one]

private theorem nol_frameConj_mono {φ : isom d} {H K : Subgroup (isom d)} (h : H ≤ K) :
    frameConj φ H ≤ frameConj φ K :=
  Subgroup.map_mono h

private theorem nol_relIndex_frameConj (φ : isom d) (H K : Subgroup (isom d)) :
    (frameConj φ H).relIndex (frameConj φ K) = H.relIndex K :=
  Subgroup.relIndex_map_map_of_injective H K (MulAut.conj φ).injective

/-- **The standing hypotheses of §8 in a frame**: `CCAction Γ Σ` gives
`CCAction (φΓφ⁻¹) (φΣ)` for every `φ ∈ Isom(𝐌ⁿ)` (`ccPrime_smul` for (CC′)). -/
theorem CCAction.frameConj_smul {Γ : Subgroup (isom d)} {St : Set (Minkowski d)}
    (h : CCAction Γ St) (φ : isom d) : CCAction (frameConj φ Γ) (φ • St) where
  cc := ccPrime_smul φ h.cc
  inv γ' hγ' := by
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hγ'
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [smul_smul, inv_mul_cancel_right, mul_smul, h.inv γ hγ]
  free γ' hγ' h1 x hx := by
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hγ'
    obtain ⟨y, hy, rfl⟩ := hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1 ⊢
    have hγ1 : γ ≠ 1 := fun e => h1 (by rw [e, mul_one, mul_inv_cancel])
    intro e
    apply h.free γ hγ hγ1 y hy
    have := congrArg (φ⁻¹ • ·) e
    simpa [smul_smul, mul_assoc] using this
  proper K hK hKc := by
    have hK' : φ⁻¹ • K ⊆ St := by
      rintro _ ⟨k, hk, rfl⟩
      obtain ⟨y, hy, rfl⟩ := hK hk
      simpa [smul_smul] using hy
    have hKc' : IsCompact (φ⁻¹ • K) := hKc.smul _
    refine ((h.proper _ hK' hKc').image (MulAut.conj φ)).subset ?_
    rintro γ' ⟨hγ', x, ⟨k, hk, rfl⟩, hxK⟩
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hγ'
    refine ⟨γ, ⟨hγ, φ⁻¹ • (φ * γ * φ⁻¹) • k, ⟨φ⁻¹ • k, ⟨k, hk, rfl⟩, ?_⟩, ⟨_, hxK, rfl⟩⟩, rfl⟩
    simp [smul_smul, mul_assoc]

/-- **[9.U], up to a frame — the [9.U] step of `nonloxodromic_parabolic`** (l.2865–2938,
unmarked; PROVED, `Nonlox.exists_unipotentRestriction_upToFrame`). Hypotheses: those of the dispatched
`exists_unipotent_restriction` (`Flat/Nonlox/UnipotentRestriction`'s
`UnipotentRestrictionStatement`): `CCAction G Σ`, `L(G)` fixing `v₀ = ofNull 1 0 0`, `y`
preserved (`b ≡ 0`, [9.b]), a parabolic element. Conclusion: the dispatched conclusion
`Nonlox.UnipotentRestrictionConclusion` (Barbot's `𝒰 = ℝ v₀ ⊕ 𝒰̄₀ ⊕ ℝ vₙ` parametrised by `ι`,
`Γ'' ≤ G` of finite index restricting to it as a group `A_{T,ℓ}` over a ball-finite `L`,
`T` symmetric on `span L`, the interval `]ylo, yhi[` of heights met on `𝒰`) **after conjugating
`(G, Σ)` by some frame `ψ ∈ Isom(𝐌ⁿ)`**.

Why the frame: the frame-free form is FALSE — `Nonlox.not_unipotentRestrictionStatement`
(a counterexample in `𝐌⁵`: the axes `𝒰̄_t` of the screw motions `λ_t(γ)` depend on `t`, against
l.2881–2892's "`𝒰̄_t` does not depend on `t`"). In that example the conclusion holds after the
null rotation `n_w` fixing `v₀`. The corrected form holds in general
(`Flat/Nonlox/UnipotentUpToFrame`): `ψ = ψ_w` with `w` read off the Bieberbach subspaces of two
slices; point (3) and the heights are `Flat/Nonlox/NullSlices`. -/
theorem exists_unipotent_restriction_up_to_frame
    (hBieb : BieberbachI (EuclideanSpace ℝ (Fin d))) {G : Subgroup (isom (d + 1))}
    {St : Set (Minkowski (d + 1))} (hcc : CCAction G St)
    (hfix : ∀ γ ∈ G, linOf γ (ofNull 1 0 0) = ofNull 1 0 0)
    (hb : ∀ γ ∈ G, ∀ p : Minkowski (d + 1), nullY (γ • p) = nullY p)
    (hpar : ∃ γ ∈ G, IsParabolic (linOf γ)) :
    ∃ ψ : isom (d + 1), Nonlox.UnipotentRestrictionConclusion d (frameConj ψ G) (ψ • St) :=
  Nonlox.exists_unipotentRestriction_upToFrame hBieb hcc hfix hb hpar

end Frames

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

/-- **The holonomy group and its subgroups are discrete** (`isomTopology`), for a Hausdorff `M`:
`discreteTopology_of_ccAction` on the standing hypotheses (`ccAction_of_developsCC`). -/
theorem discreteTopology_of_developsCC [T2Space M] (hpair : IsDevelopingPair x₀ D ρ)
    (h : DevelopsCC x₀ D S) {Γ' : Subgroup (isom d)} (hle : Γ' ≤ ρ.range) :
    DiscreteTopology Γ' :=
  DiscreteTopology.of_subset (s := (ρ.range : Set (isom d))) (t := (Γ' : Set (isom d)))
    (discreteTopology_of_ccAction (ccAction_of_developsCC hpair h)) hle

/-- **[9.E], the quotient** (l.2609–2610): if the linear parts of a finite-index `Γ' ≤ Γ` fix a
timelike vector, then `Ω(S̃) = ⊤` and, for every `Γ'' ≤ Γ'`, `Γ''\Ω(S̃)` exists as a flat
spacetime (`CCAction.exists_isQuotientOf_top_of_fix_timelike`). -/
theorem exists_isQuotientOf_omegaS_of_fix_timelike [T2Space M] (hpair : IsDevelopingPair x₀ D ρ)
    (h : DevelopsCC x₀ D S) {Γ' Γ'' : Subgroup (isom d)} (hle : Γ' ≤ ρ.range)
    (hidx : Γ'.relIndex ρ.range ≠ 0) {v : Minkowski d} (hv : minkQ v < 0)
    (hfix : ∀ γ ∈ Γ', linOf γ v = v) (hle'' : Γ'' ≤ Γ') :
    omegaSOpens ρ.range (D '' (UniversalCover.proj M x₀ ⁻¹' S)) = ⊤ ∧
      ∃ B : FlatSpacetime.{0} d,
        IsQuotientOf B Γ'' (omegaSOpens ρ.range (D '' (UniversalCover.proj M x₀ ⁻¹' S))) := by
  have hcc := ccAction_of_developsCC hpair h
  have htop : omegaSOpens ρ.range (D '' (UniversalCover.proj M x₀ ⁻¹' S)) = ⊤ :=
    TopologicalSpace.Opens.ext ((omegaS_eq_univ_of_relIndex hpair h hidx fun γ hγ =>
      isElliptic_of_fixed_timelike (linOf_mem γ).1 hv (hfix γ hγ)).1)
  rw [htop]
  exact ⟨rfl, hcc.exists_isQuotientOf_top_of_fix_timelike (hle''.trans hle) hv
    fun γ hγ => hfix γ (hle'' hγ)⟩


/-- **`𝒟(M̃) ⊆ D(Σ)`** (step 3 of Prop 8.12, l.2469–2473, as inside Develop's `bprop_danom`):
for a Hausdorff `M`, `Σ = 𝒟(S̃)` is a Cauchy surface of the open `𝒟(M̃)`, so every point of
`𝒟(M̃)` lies in the domain of dependence of `Σ` in `𝐌ⁿ`; in particular every null line through
it meets `Σ` (`exists_mem_nullLine_of_mem_dependenceDomain`, l.3123–3125). -/
theorem range_subset_dependenceDomain_of_developsCC [T2Space M] (hpair : IsDevelopingPair x₀ D ρ)
    (hcaus : (flatCausality d M).IsCausal) (h : DevelopsCC x₀ D S) :
    range D ⊆ dependenceDomain (minkowski d) ⊤ (D '' (UniversalCover.proj M x₀ ⁻¹' S)) := by
  letI := flatCoverChartedSpace d M x₀
  haveI := hasGroupoid_flatCover (d := d) M x₀
  set Sh := UniversalCover.proj M x₀ ⁻¹' S
  have hinj : Injective D := injective_of_developsCC hpair h
  have hiso : IsIsometricEmbedding d D :=
    ⟨isLocalIsometry_iff_eventually.2 ⟨hpair.gx.1, hpair.gx.2⟩, hinj⟩
  have hopen : IsOpen (range D) := hpair.gx.isOpenMap.isOpen_range
  set W : TopologicalSpace.Opens (Minkowski d) := ⟨range D, hopen⟩
  have hW : (W : Set (Minkowski d)) = D '' ((⊤ : TopologicalSpace.Opens (UniversalCover M x₀)) :
      Set (UniversalCover M x₀)) := by
    rw [TopologicalSpace.Opens.coe_top, image_univ]; rfl
  have hC : (minkowski d).IsCauchySurfaceOn W (D '' Sh) := by
    have := (hiso.isEMorphism.isCauchySurfaceOn_image_iff hinj.injOn le_rfl hW
      (subset_univ Sh)).1 (isCauchySurface_liftSet x₀ hcaus h.cauchy)
    rwa [flatCausality_self] at this
  intro y hy
  refine ⟨trivial, fun I c hc ⟨t, ht, hct⟩ => ?_⟩
  have hcW : c t ∈ W := by rw [hct]; exact hy
  obtain ⟨_, ⟨⟨r, hr, rfl⟩, hrS⟩, -⟩ := hC _ c
    (Causality.inextensible_ordConnectedComponent minkowski_isCausal hc ht hcW)
  exact ⟨c r, ⟨r, (ordConnectedComponent_subset hr).1, rfl⟩, hrS⟩

open scoped Pointwise in
/-- **[9.E] The elliptic case** (l.2604–2617): if the linear parts of a finite-index subgroup
`Γ' ≤ Γ` fix a timelike vector, then, up to finite index, `M(S) = Γ''\Ω(S̃)` is a linear
twisted product over a translation spacetime (`Ω(S̃) = 𝐌ⁿ`, `omegaS_eq_univ_of_relIndex`).
Closed (no `sorry`): Bieberbach in the euclidean form fixed by `L(Γ')`
(`Nonlox.exists_translationSubspace_of_fix_timelike`), a spacelike span of the translation
vectors (`Nonlox.minkQ_pos_of_mem_span_of_invariant`, with
`not_null_recurrent_of_isEntireAcausalGraph`), and `suspendre`
(`Nonlox.exists_isTranslationSpacetime_isLTPOver`). -/
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
  have hcc := ccAction_of_developsCC _hpair _h
  obtain ⟨v, hv, hfix⟩ := _hell
  have hprop : ∀ K : Set (Minkowski d), IsCompact K →
      {γ : isom d | γ ∈ Γ' ∧ (γ • K ∩ K).Nonempty}.Finite :=
    fun K hK => hcc.finite_of_fix_timelike _hle hv hfix hK
  -- (2) Bieberbach for `Γ'` in the euclidean form fixed by `L(Γ')`: a maximal `U ∋ v`
  obtain ⟨H', hH'le, hidx', U, hUne, hvU, Λ, hΛU, htr, htr'⟩ :=
    Nonlox.exists_translationSubspace_of_fix_timelike (_hBieb (d + 1) le_rfl) hv hfix hprop
  -- (1) the quotient `B = H'\Ω(S̃)`, `Ω(S̃) = 𝐌ⁿ`
  obtain ⟨htop, B, hB⟩ :=
    exists_isQuotientOf_omegaS_of_fix_timelike _hpair _h _hle _hidx hv hfix hH'le
  have hfix' : ∀ γ ∈ H', linOf γ v = v := fun γ hγ => hfix γ (hH'le hγ)
  letI := invariant_top_of_subgroup H'
  haveI := hcc.properlyDiscontinuousSMul_top_of_fix_timelike (hH'le.trans _hle) hv hfix'
  haveI := hcc.isCancelSMul_top_of_fix_timelike (hH'le.trans _hle) hv hfix'
  -- a point `p₀` of `Σ` on `U` (`U` contains a timelike line)
  obtain ⟨p₀, hp₀S, hp₀U⟩ : ∃ p₀, p₀ ∈ D '' (UniversalCover.proj M x₀ ⁻¹' S) ∧ p₀ ∈ U := by
    obtain ⟨q, hq⟩ := hUne
    have key : ∀ w ∈ U.direction, IsFutureTimelike w →
        ∃ p₀, p₀ ∈ D '' (UniversalCover.proj M x₀ ⁻¹' S) ∧ p₀ ∈ U := fun w hwU hw => by
      obtain ⟨s, hs⟩ := hcc.cc.entire.meets q w hw
      refine ⟨_, hs, ?_⟩
      have := AffineSubspace.vadd_mem_of_mem_direction (U.direction.smul_mem s hwU) hq
      simpa [vadd_eq_add, add_comm] using this
    rcases isFutureTimelike_or_neg hv with hw | hw
    · exact key v hvU hw
    · exact key (-v) (U.direction.neg_mem hvU) hw
  have hΛ : ∀ τ ∈ Λ, p₀ + τ ∈ D '' (UniversalCover.proj M x₀ ⁻¹' S) := by
    intro τ hτ
    obtain ⟨γ, hγ, hγτ⟩ := htr' τ hτ
    rw [← hγτ p₀ hp₀U]
    exact hcc.smul_mem (_hle (hH'le hγ)) hp₀S
  -- (4) the span of the translation vectors is spacelike
  have hsp := Nonlox.minkQ_pos_of_mem_span_of_invariant hcc.cc.entire hp₀S Λ hΛ
    (fun n hn1 hn hrec =>
      not_null_recurrent_of_isEntireAcausalGraph hcc.cc.entire hp₀S hn1 hn hrec)
  -- (3) `suspendre`: `B` is an LTP over the translation spacetime `H'_U\U`
  rw [htop] at hB
  obtain ⟨d₁, hd₁, M₁, hM₁, hLTP⟩ :=
    Nonlox.exists_isTranslationSpacetime_isLTPOver B hB ⟨v, hvU, hv⟩ hΛU htr hsp
      (fun K hK => (hprop K hK).subset fun γ hγ => ⟨hH'le hγ.1, hγ.2⟩)
  exact ⟨H', hH'le, hidx', B, htop ▸ hB, d₁, hd₁, M₁, hM₁, hLTP⟩

open scoped Pointwise in
/-- **[9.P]–[9.A] The parabolic case** (l.2619–3129), in the form of l.3120–3127 and DEC-43 (R1):
if the linear parts of a finite-index `Γ' ≤ Γ` fix a nonzero null vector `v₀`, `Γ'` contains a
parabolic element and `Γ` has no loxodromic element, then, up to finite index (`Γ'' ≤ Γ'`),
there is an open `Γ''`-invariant `Ω` with `𝒟(M̃) ⊆ Ω ⊆ Ω(S̃)` — Barbot's component of `Ω(A)`
containing `S̃`, thickened by `U^⊥` — such that `B = Γ''\Ω` is a linear twisted product over a
**unipotent spacetime**. The conclusion concerns `M` (through `𝒟(M̃) ⊆ Ω`), **not** `M(S)`:
by Rem 9.4 `Ω(S̃)` may be all of `𝐌ⁿ` while `Ω` is a slab (SCOPE, finding 6).
Assembled: frame `φ` (`Nonlox.exists_isom_linear_null_frame`), [9.b]
(`Nonlox.nullY_smul_eq_of_isParabolic`), [9.U] up to a further frame `ψ`
(`exists_unipotent_restriction_up_to_frame`, proved in `Flat/Nonlox/UnipotentUpToFrame`;
SCOPE finding 8), Prop 9.3
(`bprop_limites_model`), Prop 9.5 (`bprop_extension`), `mem_omegaA_of_limites`, the frame `φ₁`
(`Nonlox.exists_unipotent_frame_of_symm`) and [9.A] (`Nonlox.exists_unipotent_ltp_of_frame`,
with `𝒟(M̃) ⊆ D(Σ)`, `range_subset_dependenceDomain_of_developsCC`). `d = 0` is vacuous. -/
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
  obtain _ | d := d
  · exfalso
    apply _hv0
    have h2 : v₀.2 = 0 := Subsingleton.elim _ _
    have h1 : v₀.1 = 0 := by
      have := _hv
      simp only [minkQ, h2, norm_zero] at this
      nlinarith [sq_nonneg v₀.1]
    exact Prod.ext h1 h2
  have hcc := ccAction_of_developsCC _hpair _h
  have hDD := range_subset_dependenceDomain_of_developsCC _hpair _hcaus _h
  set Sg := D '' (UniversalCover.proj M x₀ ⁻¹' S) with hSg
  have hcc' : CCAction Γ' Sg := hcc.mono _hle
  obtain ⟨γp, hγp, hγpar⟩ := _hpar
  obtain ⟨φ, -, c, hc, hφv⟩ :=
    Nonlox.exists_isom_linear_null_frame _hv0 _hv ⟨_, linOf_mem γp, hγpar⟩
  set G := frameConj φ Γ'
  have hccG : CCAction G (φ • Sg) := hcc'.frameConj_smul φ
  have hconjlin : ∀ g : isom (d + 1),
      linOf (φ * g * φ⁻¹) = linOf φ * linOf g * (linOf φ)⁻¹ := fun g => by
    rw [linOf_mul, linOf_mul, linOf_inv]
  have he : ofNull 1 0 0 = linOf φ (c⁻¹ • v₀) := by
    rw [map_smul, hφv, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hfixG : ∀ γ ∈ G, linOf γ (ofNull 1 0 0) = ofNull 1 0 0 := by
    intro γ hγ
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hγ
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hconjlin, he, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    simp [map_smul, _hfix g hg]
  have hparG : ∃ γ ∈ G, IsParabolic (linOf γ) :=
    ⟨φ * γp * φ⁻¹, Subgroup.mem_map.2 ⟨γp, hγp, rfl⟩, by
      rw [hconjlin]; exact hγpar.conj (linOf_mem φ)⟩
  obtain ⟨γ₁, hγ₁, hpar₁⟩ := hparG
  have hb := Nonlox.nullY_smul_eq_of_isParabolic hccG.cc.entire.acausal hccG.nonempty
    (fun γ hγ p hp => hccG.smul_mem hγ hp) hfixG hγ₁ hpar₁
  obtain ⟨ψ, hconc⟩ :=
    exists_unipotent_restriction_up_to_frame (_hBieb d (by omega)) hccG hfixG hb ⟨γ₁, hγ₁, hpar₁⟩
  rw [← nol_frameConj_mul, smul_smul] at hconc
  set φ' := ψ * φ
  have hccG' : CCAction (frameConj φ' Γ') (φ' • Sg) := hcc'.frameConj_smul φ'
  obtain ⟨G'', hG''le, hidxG, d₁, hd₁, J, z₀, y₀, ι, hι, hιo, hres, L, T, ℓ, ylo, yhi, hL, hTpar,
    hsym, hform, hform', hlo, hhi, hnorm, hI, hIsub⟩ := hconc
  set St₁ : Set (ℝ × EuclideanSpace ℝ (Fin d₁) × ℝ) := nolToMink ⁻¹' (ι ⁻¹' (φ' • Sg))
  have hach : ∀ X ∈ St₁, ∀ X' ∈ St₁, 0 ≤ nolQ (X - X') := fun X hX X' hX' => by
    have := nolQ_nonneg_of_isAcausal hccG'.cc.entire.acausal
      (X := minkToNol (ι (nolToMink X))) (X' := minkToNol (ι (nolToMink X')))
      (by rw [nolToMink_minkToNol]; exact hX) (by rw [nolToMink_minkToNol]; exact hX')
    rwa [← minkQ_nolToMink, nolToMink_sub, nolToMink_minkToNol, nolToMink_minkToNol, ι.apply_sub,
      ι.minkQ_lin, ← nolToMink_sub, minkQ_nolToMink] at this
  have hΓ : ∀ u ∈ L, ∃ g : NolParam (EuclideanSpace ℝ (Fin d₁)), g.IsA ∧ g.u = u ∧ g.v = T u ∧
      ∀ X ∈ St₁, g.act X ∈ St₁ := by
    intro u hu
    obtain ⟨g, hg, hgf⟩ := hform' u hu
    obtain ⟨γ, hγ, hgr⟩ := (ι.mem_restrictGroup).1 hg
    refine ⟨⟨LinearIsometryEquiv.refl ℝ _, u, T u, ℓ u - ⟪u, T u⟫ / 2, 0⟩, ⟨rfl, rfl⟩, rfl, rfl,
      fun X hX => ?_⟩
    have e : nolToMink (NolParam.act ⟨LinearIsometryEquiv.refl ℝ _, u, T u,
        ℓ u - ⟪u, T u⟫ / 2, 0⟩ X) = g • nolToMink X := by
      obtain ⟨x, z, y⟩ := X
      simp only [nolToMink, NolParam.act, hgf, LinearIsometryEquiv.coe_refl, id_eq, add_zero]
      congr 1
      abel
    show ι (nolToMink _) ∈ φ' • Sg
    rw [e, hgr]
    exact hccG'.smul_mem (hG''le hγ) hX
  obtain ⟨hfin, hineq⟩ := bprop_limites_model hach hΓ hlo hhi
    (fun y h1 h2 => by
      obtain ⟨p, hp, hpy⟩ := hI y h1 h2
      exact ⟨minkToNol p, by
        show nolToMink (minkToNol p) ∈ ι ⁻¹' (φ' • Sg); rw [nolToMink_minkToNol]; exact hp, hpy⟩)
    hTpar
  obtain ⟨T', hext, hsym', hineq'⟩ :=
    bprop_extension (fun u hu u' hu' => hsym u hu u' hu') hlo hhi hnorm hfin hineq
  have hpole : ∀ y : ℝ, ylo < y → (y : EReal) < yhi →
      ∀ t : EuclideanSpace ℝ (Fin d₁), t ≠ 0 → t + y • T' t ≠ 0 := fun y h1 h2 =>
    mem_omegaA_of_limites (X := ((0 : ℝ), (0 : EuclideanSpace ℝ (Fin d₁)), y)) hlo hhi hnorm hfin
      hineq' h1 h2
  have hTT : ∀ u ∈ L, T' u = T u := fun u hu => hext u (subset_span hu)
  obtain ⟨φ₁, ℓ', α, β, L', ΓA, hL', hαβ, hA, hA', hH, hφ₁, hα, hβ⟩ :=
    Nonlox.exists_unipotent_frame_of_symm (H := ι.restrictGroup G'') hL
      (fun u u' => hsym' u trivial u' trivial) ℓ
      (fun g hg => by
        obtain ⟨u, hu, hgu⟩ := hform g hg
        exact ⟨u, hu, by simpa only [hTT u hu] using hgu⟩)
      (fun u hu => by
        obtain ⟨g, hg, hgu⟩ := hform' u hu
        exact ⟨g, hg, by simpa only [hTT u hu] using hgu⟩)
      (hlo.trans hhi) hpole
  set Γ'' := frameConj φ'⁻¹ G''
  have hΓ''G : frameConj φ' Γ'' = G'' := nol_frameConj_frameConj_inv φ' G''
  have hΓ''le : Γ'' ≤ Γ' := by
    have := nol_frameConj_mono (φ := φ'⁻¹) hG''le
    rwa [nol_frameConj_inv_frameConj] at this
  have hΓ''idx : Γ''.relIndex Γ' ≠ 0 := by
    rw [← nol_relIndex_frameConj φ', hΓ''G]; exact hidxG
  have hD : ∀ p ∈ range D, ∃ s : ℝ, p + s • (linOf φ').symm (ofNull 1 0 0) ∈ Sg := fun p hp =>
    exists_mem_nullLine_of_mem_dependenceDomain (hDD hp)
      (fun h0 => Nonlox.ULTP.ofNull_one_ne_zero (by
        rw [← linOf_symm_apply φ' (ofNull 1 0 0), h0, map_zero]))
      (by rw [minkQ_linOf_symm]; exact Nonlox.ULTP.minkQ_ofNull_one)
  have hSt : ∀ p ∈ Sg, α < ((nullY (φ' • p) - y₀ : ℝ) : EReal) ∧
      ((nullY (φ' • p) - y₀ : ℝ) : EReal) < β := fun p hp => by
    have := hIsub (φ' • p) (Set.smul_mem_smul_set hp)
    exact ⟨lt_of_le_of_lt hα this.1, lt_of_lt_of_le this.2 hβ⟩
  obtain ⟨Ω, hDΩ, hΩ, B, hB, M₁, hM₁, hLTP⟩ :=
    Nonlox.exists_unipotent_ltp_of_frame hcc (hΓ''le.trans _hle)
      (Subgroup.relIndex_ne_zero_trans hΓ''idx _hidx) φ' hD J z₀ y₀ ι hι hιo (hΓ''G ▸ hres) hL' hαβ
      hA hA' (hΓ''G ▸ hH) hφ₁ hSt
  exact ⟨Γ'', hΓ''le, hΓ''idx, Ω, hDΩ, hΩ, B, hB, d₁, by omega, M₁, hM₁, hLTP⟩

/-- **The nonloxodromic case** (§9), assembled: under Benoist's theorem (Prop 9.1, external),
`TitsVirtuallyAbelianNull` (for the branch l.2621–2622 overlooks: null `v₀` fixed, all
elliptic; with the holonomy's discreteness `discreteTopology_of_developsCC`; proved in
`Flat/TitsNull` as `titsVirtuallyAbelianNull d`, DEC-50, and supplied downstream) and
Bieberbach's (external), if `Γ` has no loxodromic element, a finite-index `Γ'' ≤ Γ` and an
open `Γ''`-invariant `Ω` with `𝒟(M̃) ⊆ Ω ⊆ Ω(S̃)` make `B = Γ''\Ω` either (elliptic case,
`Ω = Ω(S̃)`, so `B` is `M(S)` up to finite index) a linear twisted product over a translation
spacetime, or (parabolic case) a linear twisted product over a unipotent spacetime. -/
theorem nonloxodromic [T2Space M] (hB : BenoistNoLox d) (hT : TitsVirtuallyAbelianNull d)
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
      exists_timelike_fixed_of_elliptic_of_null hT
        (discreteTopology_of_developsCC hpair h hle₁) hv0 hv hfix hell
    have hidx₂₁ := Subgroup.relIndex_ne_zero_trans hidx₂ hidx₁
    obtain ⟨Γ₃, hle₃, hidx₃, B, hB', hrest⟩ :=
      nonloxodromic_elliptic hBieb hpair h (hle₂.trans hle₁) hidx₂₁ ⟨v, hv', hfix'⟩
    exact ⟨Γ₃, hle₃.trans (hle₂.trans hle₁), Subgroup.relIndex_ne_zero_trans hidx₃ hidx₂₁, _, hD,
      subset_rfl, B, hB', Or.inl ⟨rfl, hrest⟩⟩

end Main

end Causal.Flat
