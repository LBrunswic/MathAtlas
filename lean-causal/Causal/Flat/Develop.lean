import Causal.Flat.Developing
import Causal.Flat.LipschitzGraph
import Causal.Flat.AchronalDomains
import Causal.Flat.Penrose
import Causal.Flat.FlatSpacetime
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible

/-!
# `Causal.Flat.Develop` — Barbot §8 from (CC′): `U(g)`, `Ω(Γ)`, `Ω(S̃)`, Lemma 8.6, Prop 8.10, Cauchy surfaces lift, Prop 8.12

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §8,
`GHFspace.tex` l.2212–2526 (labelled file). Design: `docs/BARBOT-WAVE3.md` §3 (DEC-35: everything
after Prop 8.1 / Cor 8.3 runs from (CC′)); defects W4, W7, W8, W10 of its §0 apply. One label is
certified, **in a reading, disclosed** (DEC-83, the author's ruling; checklist below):
`blem:SdanU`. The others are `partial` (SCOPE), several being fully proved in a reading.

* `bcor:quo` (Cor 8.2, l.2263–2271), partial (DEC-35 reading, `M` Hausdorff; **no `sorry`**) —
  `bcor_quo`, `holonomy_proper`, `isOpenEmbedding_of_developsCC`,
  `isPreconnected_liftSet_of_developsCC`:
  > The maps $f$ and ${\mathcal D} \circ \tilde{f}$ are embeddings. The natural morphism
  > $\Gamma \subset \pi_{1}(M)$ and the morphism $\rho$ are injective. Moreover,
  > ${\mathcal D} \circ \tilde{f}(\widetilde{S})$ intersects every timelike geodesic.
* `bdef:U_g` (Def 8.5, l.2332–2349), partial (readings) — `Ug`:
  > - $U(g) = \Omega_{g}$ if $g$ is loxodromic, or spacelike elliptic, or non linear parabolic.
  > - $U(g) = \emptyset$ if $g$ is nonspacelike elliptic, - $U(g) = {\bf M}^{n} \setminus J^{\perp}$
  > if $g$ is linear parabolic, where $J$ is the lightlike affine line of fixed points of $g$,
* **`blem:SdanU`** — `GHFspace.tex:2353` (Lemma 8.6, l.2353–2358), marked (DEC-83; the (CC′)
  reading, DEC-35, and W4; **no `sorry`**) — `blem_SdanU`:
  > The complete spacelike hypersurface $\widetilde{S}$ is contained in the interior of
  > $U(\Gamma) = \bigcap_{\gamma \in \Gamma} U(\gamma)$.
* `bdef:omega_gamma` (Def 8.7, l.2394–2400), partial (W4) — `omegaGamma`, `omegaS`, `omegaS_eq`:
  > The interior of $U(\Gamma)$ is denoted by $\Omega(\Gamma)$ […] The connected component
  > of the interior of $U(\Gamma)$ containing $\widetilde{S}$ is denoted by $\Omega(\widetilde{S})$.
* Rem 8.8 `remplacefini` (l.2403–2408), unlabelled in the ledger — `achronalDomain_subset_zpow`,
  `UGamma_antitone`, `Ug_zpow` (**no `sorry`**, readings of `Ug`), `UGamma_eq_of_index`:
  > For any isometry $g$, and for every nonzero integer $n$ we have $U(g^{n}) = U(g)$.
* Rem 8.9 `nini` (l.2411–2415), unlabelled — `nini`, **no `sorry`**:
  > we will assume that the group $\Gamma$ does not contain nonspacelike elliptic and transverse
  > parabolic elements, since we have shown that in this case […]
* `bprop:ghyp` (Prop 8.10, l.2420–2426), partial (DEC-35/W4 readings; **no `sorry`**) —
  `bprop_ghyp` (W8 discharged here), `bprop_ghyp_of_trichotomy`:
  > $\Omega(\widetilde{S})$ is a convex open set. It is globally hyperbolic. The action of
  > $\Gamma$ on it is free and achronal.
* `bprop:splitting` (Prop 8.11, l.2459–2464), partial: the lift half only, **no `sorry`** —
  `isCauchySurface_preimage`, `isCauchySurface_liftSet`:
  > Any nonspacelike geodesic in $\widetilde{M}$ intersect $\widetilde{S}$.
* `bprop:danom` (Prop 8.12, l.2469–2473), partial (DEC-35 reading, `M` Hausdorff and causal;
  **no `sorry`**) — `bprop_danom`, step 1 `injective_of_developsCC`:
  > The developing map ${\mathcal D}: \widetilde{M} \rightarrow {\bf M}^{n}$ is injective, with
  > image contained in $\Omega(\widetilde{S})$.

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; `Minkowski d` has `d` spatial
dimensions: Barbot's `n` is `d + 1`.

## Main declarations

* `ccPrime_smul` — (CC′) is `Isom(𝐌ⁿ)`-invariant. `isNonspacelikeElliptic_of_pow_eq_one` — a
  finite-order isometry fixes a point and a future timelike vector (barycentres), so it is
  nonspacelike elliptic.
* Classes on `isom d`: `IsNonspacelikeElliptic`, `IsSpacelikeElliptic`, `IsParabolicPair`,
  `IsLinearParabolic`, `IsTransverseParabolic`, `nullHyperplanes`; `Ug`, `UGamma`, `omegaGamma`,
  `omegaS`, `omegaSOpens`; `Ug_subset_achronalDomain`; conjugation `smul_mem_Ug`, `smul_UGamma`.
* `CCAction Γ Σ` — the standing hypotheses in `𝐌ⁿ`: (CC′), `Γ Σ = Σ`, free, properly
  discontinuous. Under it: `CCAction.false_of_le_smul` (the repaired interior argument),
  `dependenceDomain_subset_UGamma` (`D(Σ) ⊆ U(Γ)`), `blem_SdanU`, `nini`, torsion-freeness.
* Powers (Rem 8.8): `linOf_zpow`; `IsElliptic.zpow_linOf`, `IsLoxodromic.zpow_linOf`,
  `IsParabolic.zpow_linOf`, `isElliptic_linOf_zpow_iff`, `isParabolic_linOf_zpow_iff`;
  `zpow_smul_eq_add`, `exists_smul_eq_self_of_pow` (barycentre), `fixedTrans_eq`,
  `isNonspacelikeElliptic_zpow_iff`, `isLinearParabolic_zpow_iff`,
  `zpow_smul_eq_self_of_smul_eq`, `exists_fixed_trans`, `IsParabolicPair.exists_fixed_null`,
  `minkB_eq_zero_of_fixed_of_not_isElliptic`, `mem_nullHyperplanes_iff` (`J^⊥` independent of
  the decomposition), `nullHyperplanes_zpow`, `achronalDomain_inv`, `achronalDomain_zpow`,
  `Ug_zpow`.
* `IsCausalPiece`, `convex_causallyConvex_connectedComponentIn` (W8: components of `int A` are
  convex and causally convex when `A` is a piece), `pos_mul_of_null`, the per-class pieces
  `isCausalPiece_compl_nullHyperplanes`, `_achronalDomain_lox`, `_spacelikeElliptic`, `_tangent`.
* Flat coverings: `causalCurveIn_of_lift` (a continuous lift of a causal curve through a local
  isometry is causal), `lift_causalCurveIn`, `inextensible_comp`, `isCauchySurface_preimage`;
  `continuousOn_of_strictMonoOn`; `finite_deck_of_isCompact` (the deck group of a covering of a
  Hausdorff space acts properly discontinuously). `IsDevelopingPair`, `DevelopsCC`, `bcor_quo`,
  `injective_of_developsCC` (maximal lifts of vertical lines through the local homeomorphism
  `𝒟`, private section `MaxLift`), `isOpenEmbedding_of_developsCC`, `holonomy_proper`,
  `ccAction_of_developsCC`, `isPreconnected_liftSet_of_developsCC`, `bprop_danom`; the witness
  `developsCC_minkowski`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `blem:SdanU` (**marked**, DEC-83) | ⚠ reading: the (CC′) reading (DEC-35): `S̃` read as the `CCAction Γ Σ` data in `𝐌ⁿ`, Cor 8.3 carried as (CC′)(b); W4: `U(Γ) = ⋂_{γ ≠ 1} U(γ)` (as printed `U(Γ) = ∅`), with the readings of `Ug` (SCOPE); no external; the paper's interior argument replaced (finding) |
| `S` a complete Riemannian hypersurface, `f` an isometric immersion (l.2215–2216) | ⚠ strengthened (DEC-35 reading): `S` a Cauchy surface of `M` with `DevelopsCC` ((CC′) for `Σ = 𝒟(p⁻¹S)`, `𝒟` injective on `p⁻¹S`); `S̃ := p⁻¹(S) ⊆ M̃`, not the universal cover of `S` |
| `Γ = π₁(S)` acting on `S̃` (free, properly discontinuous) | ⚠ strengthened in `𝐌ⁿ`: `CCAction` carries it; on `M` it is `ρ(Deck(M̃ → M))` (`bcor_quo`; properness `holonomy_proper`) |
| (implicit) `M` a manifold: Hausdorff | ✓ carried as `[T2Space M]` exactly where used: `injective_of_developsCC`, `isOpenEmbedding_of_developsCC`, `holonomy_proper`, `ccAction_of_developsCC`, `isPreconnected_liftSet_of_developsCC`, `bprop_danom` (false without it, SCOPE). Connectedness of `M` is not used and not asked |
| `M` globally hyperbolic (§8 from l.2454) | ⚠ weakened to `(flatCausality d M).IsCausal` (W10) where used: `isCauchySurface_preimage`, `bprop_danom` |
| Lemma 8.6 uses Cor 8.3 (`quoiso`) | ✓ carried as (CC′)(b) `NullSaturated` |
| Rem 8.8, `Γ'` of finite index in `Γ` (l.2405) | ⚠ strengthened: `Γ` torsion-free (`UGamma_eq_of_index`; needed under W4, counterexample in its docstring) |
| (implicit) the classification of isometries, Prop 8.10 | ✓ carried: `lorentz_trichotomy` (Flat/Isometries), packaged as `LorentzTrichotomy` |

## SCOPE (disclosed)

* **Readings.** `Ω_g` with `q ≠ 0` (AchronalDomains); `U(Γ) = ⋂_{γ ≠ 1}` (W4: `U(id) = ∅`
  since `id` is nonspacelike elliptic, so as printed `U(Γ) = ∅`); "nonspacelike elliptic":
  `L(g)` elliptic and some `g x − x` fixed by `L(g)` with `|g x − x|² ≤ 0` (fixed points
  included); "linear parabolic": parabolic with a fixed point; `J^⊥` is the union, over the
  parabolic decompositions `L(g) = R U` and the fixed points `c`, of `c + (nullPart U)^⊥` (the
  decomposition is not proved unique); the last branch of `Ug` is `Ω_g`, which covers
  "loxodromic, spacelike elliptic, non linear parabolic" exactly when `lorentz_trichotomy` holds.
  `Ω(S̃)` is the union of the components of `Ω(Γ)` meeting `Σ` (one component, `omegaS_eq`).
* **Proof repairs.** Lemma 8.6's "small convex `B`" (l.2383–2389) is replaced by `int D(Σ)`
  (`graph_subset_interior_dependenceDomain`) and `D(Σ) ⊆ U(Γ)`; Prop 8.10's "convexity of the
  components of every `U(γ)`" (W8) by the piece property `IsCausalPiece`, proved class by class
  (loxodromic quadrants, spacelike elliptic, tangent, transverse) over Isometries'
  `lorentz_trichotomy`; Beem–Ehrlich is not used (ETT's GH from causal convexity,
  `globallyHyperbolicOn_of_causallyConvexIn`); Prop 8.12's slices `S̃ × {t}` (l.2487–2493, W7) by
  `𝒟(M̃) ⊆ D(Σ)`, `Σ` being a Cauchy surface of `𝒟(M̃)`.
* **Sorries: none.** `holonomy_proper` and `bprop_danom`'s step 1 are proved (fixer pass,
  WP-32f), under `[T2Space M]`. `bprop_ghyp` uses `lorentz_trichotomy` (Flat/Isometries).
* **Finding (closer pass, WP-32f; repaired by the fixer): without `[T2Space M]`, `bprop_danom`
  is false**, because the library's flat `(Isom(𝐌ⁿ), 𝐌ⁿ)`-manifolds (`ChartedSpace` +
  `HasGroupoid`) need not be Hausdorff, whereas Barbot's spacetimes are manifolds.
  Counterexample, any `d`: `M` = two copies of `𝐌ⁿ` glued along the open half-space `{t < 0}`
  (flat, simply connected, non-Hausdorff; `t ∘ fold` is a time function, so `M` is causal),
  `S = {t = −1}` (Cauchy: along an inextensible causal curve `t` is unbounded both ways), `𝒟` the
  fold map composed with the bijective `M̃ → M`, `ρ = 1`. `DevelopsCC` holds (`Σ = {t = −1}`,
  `ccPrime_graph_const`) and the two origins have the same image. `[T2Space M]` is therefore
  added to `bprop_danom`, `holonomy_proper` and `ccAction_of_developsCC` (a statement change by
  the fixer, the master's ruling pending; `bcor_quo` and the rest of the file do not need it).
* **Proof route of step 1** (`injective_of_developsCC`, l.2476–2485 repaired): Barbot's "maximal
  lift of the vertical line" is built by hand — lifts over open intervals are unique on overlaps
  (Hausdorff `M̃`, locally injective `𝒟`), their union is a lift, and it has no limit at a finite
  end of its domain (a local inverse of `𝒟` would continue it). A strict extension of it in the
  sense of `StrictlyExtends` would produce such a limit (the time coordinate of `𝒟` is a clock
  along the lift), so it is inextensible and meets `S̃`; injectivity on `S̃` and uniqueness of
  lifts conclude. No ODE, no Zorn, and neither `IsCausal` nor the holonomy is used.
* **Cor 8.2** now proved in the reading, under `[T2Space M]`: "`𝒟 ∘ f̃` is an embedding"
  (`isOpenEmbedding_of_developsCC`: `𝒟` is even an open embedding of `M̃`) and the design's
  conjunct `IsPreconnected S̃` (`isPreconnected_liftSet_of_developsCC`). "`f` is an embedding" is
  the inclusion `S ⊆ M` in the DEC-35 reading (`S` a subset, not an immersed manifold).
* Non-vacuity: `ccAction_bot` (any (CC′) surface, trivial `Γ`; the hyperboloid in an `example`);
  `developsCC_minkowski` (`M = 𝐌ⁿ`, `𝒟 = proj`, `S = {t = 0}`, trivial holonomy). No inhabitant
  of `DevelopsCC` with nontrivial holonomy is formalized.
* **Findings.** Rem 8.8's `Ω_{gⁿ} = Ω_g` holds for every isometry, with no class analysis
  (`achronalDomain_zpow`: causally related iterates iterate), and `J^⊥` does not depend on the
  parabolic decomposition (`mem_nullHyperplanes_iff`), which answers the uniqueness question
  left open by the union reading. Lemma 8.6's transverse case needs no Lemma 7.1 (false for `d ≥ 3`,
  AchronalDomains): `Σ ⊆ Ω_γ` and `Ω_γ = ∅`. Rem 8.8's `U(Γ') = U(Γ)` needs `Γ` torsion-free
  under W4 (`UGamma_eq_of_index`). Prop 8.12 needs no "free and achronal on `Ω'`" step.
* The homeomorphism `M ≃ S × ℝ` of `bprop:splitting` is Splitting's, not used here.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
wave 3, package WP-32f-Develop.
-/

namespace Causal.Flat

open Set Function TopologicalSpace Topology Filter
open scoped Pointwise

variable {d : ℕ}

/-! ### (CC′) is invariant under `Isom(𝐌ⁿ)` -/

theorem isom_smul_add_smul (g : isom d) (x w : Minkowski d) (s : ℝ) :
    g • (x + s • w) = g • x + s • linOf g w := by
  rw [smul_eq_lin_add, smul_eq_lin_add, map_add, map_smul]; abel

theorem linOf_symm_apply (g : isom d) (v : Minkowski d) : linOf g ((linOf g).symm v) = v :=
  (linOf g).apply_symm_apply v

theorem minkQ_linOf_symm (g : isom d) (v : Minkowski d) : minkQ ((linOf g).symm v) = minkQ v := by
  rw [← lorentz.minkQ_apply (linOf_mem g) ((linOf g).symm v), linOf_symm_apply]

theorem minkB_linOf (g : isom d) (v w : Minkowski d) : minkB (linOf g v) (linOf g w) = minkB v w :=
  minkB_map (lorentz.minkQ_apply (linOf_mem g)) v w

theorem smul_sub_smul (g : isom d) (x y : Minkowski d) : g • x - g • y = linOf g (x - y) := by
  rw [isom_smul_def, isom_smul_def, isom_sub]

theorem ccPrime_smul (g : isom d) {S : Set (Minkowski d)} (h : CCPrime S) : CCPrime (g • S) := by
  have hmem : ∀ x, x ∈ g • S ↔ g⁻¹ • x ∈ S := fun x => Set.mem_smul_set_iff_inv_smul_mem
  have hback : ∀ (x w : Minkowski d) (s : ℝ), g⁻¹ • x + s • (linOf g).symm w ∈ S →
      x + s • w ∈ g • S := by
    intro x w s hx
    rw [Set.mem_smul_set]
    refine ⟨_, hx, ?_⟩
    rw [isom_smul_add_smul, smul_inv_smul, linOf_symm_apply]
  refine ⟨⟨fun x hx y hy hxy => ?_, fun p v hv => ?_⟩, ?_⟩
  · rw [hmem] at hx hy
    have : (minkowski d).le ⊤ (g • g⁻¹ • x) (g • g⁻¹ • y) := by rwa [smul_inv_smul, smul_inv_smul]
    have := h.entire.acausal _ hx _ hy ((isom_le_top_iff g).1 this)
    simpa using congrArg (g • ·) this
  · have hv' : IsFutureTimelike ((linOf g).symm v) := by
      rw [← lorentz.isFutureTimelike_apply_iff (linOf_mem g), linOf_symm_apply]; exact hv
    obtain ⟨s, hs⟩ := h.entire.meets (g⁻¹ • p) _ hv'
    exact ⟨s, hback p v s hs⟩
  · intro p ℓ hℓ0 hℓ ⟨q, hq, hqp⟩ r hr
    have hB : ∀ x, minkB (g⁻¹ • x - g⁻¹ • p) ((linOf g).symm ℓ) = minkB (x - p) ℓ := by
      intro x
      rw [← minkB_linOf g, ← smul_sub_smul, smul_inv_smul, smul_inv_smul, linOf_symm_apply]
    have hℓ0' : (linOf g).symm ℓ ≠ 0 := fun h0 => hℓ0 (by
      rw [← linOf_symm_apply g ℓ, h0, map_zero])
    obtain ⟨s, hs⟩ := h.nullSat (g⁻¹ • p) _ hℓ0' (by rw [minkQ_linOf_symm]; exact hℓ)
      ⟨g⁻¹ • q, (hmem q).1 hq, by rw [hB]; exact hqp⟩ (g⁻¹ • r) (by rw [hB]; exact hr)
    exact ⟨s, hback r ℓ s hs⟩

/-! ### The classes of isometries used by Def 8.5 -/

/-- **Nonspacelike elliptic** (l.2340, [6.N]): `L(g)` elliptic and `g x = x + τ` for some `x` with
`τ` fixed by `L(g)` and `|τ|² ≤ 0` (fixed points, `τ = 0`, included: `id` is one). -/
def IsNonspacelikeElliptic (g : isom d) : Prop :=
  IsElliptic (linOf g) ∧ ∃ x : Minkowski d, linOf g (g • x - x) = g • x - x ∧ minkQ (g • x - x) ≤ 0

/-- **Spacelike elliptic** (l.2337): as above with `|τ|² > 0`. -/
def IsSpacelikeElliptic (g : isom d) : Prop :=
  IsElliptic (linOf g) ∧ ∃ x : Minkowski d, linOf g (g • x - x) = g • x - x ∧ 0 < minkQ (g • x - x)

/-- A **parabolic decomposition** `L(g) = R U` (Flat/Isometries' `IsParabolic`, unpacked). -/
def IsParabolicPair (g : isom d) (R U : Minkowski d ≃ₗ[ℝ] Minkowski d) : Prop :=
  R ∈ lorentz d ∧ U ∈ lorentz d ∧ IsElliptic R ∧ IsUnipotent U ∧ U ≠ 1 ∧ linOf g = R * U ∧
    R * U = U * R

/-- **Linear parabolic** (l.2342): parabolic with a fixed point (Isometries' `IsLinearCase`). -/
def IsLinearParabolic (g : isom d) : Prop := IsParabolic (linOf g) ∧ ∃ c : Minkowski d, g • c = c

/-- **Transverse parabolic** (l.2413): `τ ∉ J^⊥` for some decomposition. -/
def IsTransverseParabolic (g : isom d) : Prop :=
  ∃ R U, IsParabolicPair g R U ∧ IsTransverseCase U (g : Minkowski d ≃ᵃ[ℝ] Minkowski d)

/-- **Barbot's `J^⊥`** (l.2342–2344) for a linear parabolic `g`: the null affine hyperplanes
`c + (nullPart U)^⊥` through the fixed points `c`, over all decompositions `L(g) = R U`. -/
def nullHyperplanes (g : isom d) : Set (Minkowski d) :=
  {x | ∃ R U, IsParabolicPair g R U ∧ ∃ c, g • c = c ∧ x - c ∈ minkOrth (nullPart U)}

open Classical in
/-- **Def 8.5** (`bdef:U_g`, l.2332–2349), in the readings of SCOPE: `∅` for nonspacelike
elliptic `g`, the complement of `J^⊥` for linear parabolic `g`, `Ω_g` otherwise. -/
noncomputable def Ug (g : isom d) : Set (Minkowski d) :=
  if IsNonspacelikeElliptic g then ∅
  else if IsLinearParabolic g then (nullHyperplanes g)ᶜ
  else achronalDomain g

/-- `U(Γ) = ⋂_{γ ∈ Γ, γ ≠ 1} U(γ)` (l.2357, W4: `γ ≠ 1`). -/
def UGamma (Γ : Subgroup (isom d)) : Set (Minkowski d) := {x | ∀ γ ∈ Γ, γ ≠ 1 → x ∈ Ug γ}

/-- **Def 8.7** (`bdef:omega_gamma`): the achronal domain `Ω(Γ) = int U(Γ)`. -/
def omegaGamma (Γ : Subgroup (isom d)) : Set (Minkowski d) := interior (UGamma Γ)

/-- **Def 8.7**: `Ω(S̃)`, the union of the components of `Ω(Γ)` meeting `Σ`; one component under
the standing hypotheses (`omegaS_eq`). -/
def omegaS (Γ : Subgroup (isom d)) (S : Set (Minkowski d)) : Set (Minkowski d) :=
  ⋃ x ∈ S, connectedComponentIn (omegaGamma Γ) x

/-! ### Finite-order isometries are nonspacelike elliptic -/

theorem linOf_pow (g : isom d) (n : ℕ) : linOf (g ^ n) = linOf g ^ n := by
  show AffineEquiv.linearHom ((g ^ n : isom d) : Minkowski d ≃ᵃ[ℝ] Minkowski d) = _
  rw [Subgroup.coe_pow, map_pow]
  rfl

theorem IsFutureTimelike.add {a b : Minkowski d} (ha : IsFutureTimelike a)
    (hb : IsFutureTimelike b) : IsFutureTimelike (a + b) := by
  rw [isFutureTimelike_iff_norm_lt] at ha hb ⊢
  calc ‖(a + b).2‖ ≤ ‖a.2‖ + ‖b.2‖ := norm_add_le _ _
    _ < a.1 + b.1 := add_lt_add ha hb

/-- **A nontrivial isometry of finite order is nonspacelike elliptic**: the barycentre of an orbit
is a fixed point, and the sum of the `L(g)`-iterates of a future timelike vector is a fixed future
timelike vector. -/
theorem isNonspacelikeElliptic_of_pow_eq_one (g : isom d) {n : ℕ} (hn : 0 < n) (h : g ^ n = 1) :
    IsNonspacelikeElliptic g := by
  have hL : linOf g ^ n = 1 := by rw [← linOf_pow, h]; rfl
  -- a fixed future timelike vector
  set e₀ : Minkowski d := ((1 : ℝ), 0)
  set u : Minkowski d := ∑ k ∈ Finset.range n, (linOf g ^ k) e₀ with hudef
  have hu : IsFutureTimelike u := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [hudef]
    clear hL h hn hudef u
    induction m with
    | zero => simpa using isFutureTimelike_vertical
    | succ m ih =>
      rw [Finset.sum_range_succ]
      exact ih.add (lorentz.isFutureTimelike_apply (pow_mem (linOf_mem g) _)
        isFutureTimelike_vertical)
  have hLu : linOf g u = u := by
    rw [hudef, map_sum]
    have : ∀ k, linOf g ((linOf g ^ k) e₀) = (linOf g ^ (k + 1)) e₀ := fun k => by
      rw [pow_succ', LinearEquiv.mul_apply]
    simp only [this]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Finset.sum_range_succ, Finset.sum_range_succ' (fun k => (linOf g ^ k) e₀), hL]
    simp
  -- a fixed point: the barycentre of the orbit of `0`
  set w : Minkowski d := ∑ k ∈ Finset.range n, (g ^ k) • (0 : Minkowski d) with hwdef
  set c : Minkowski d := (n : ℝ)⁻¹ • w
  have hsum : ∑ k ∈ Finset.range n, linOf g ((g ^ k) • (0 : Minkowski d)) =
      w - (n : ℝ) • trOf g := by
    have : ∀ k, linOf g ((g ^ k) • (0 : Minkowski d)) = (g ^ (k + 1)) • (0 : Minkowski d) - trOf g :=
      fun k => by rw [pow_succ', mul_smul, smul_eq_lin_add (g := g)]; abel
    simp only [this, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [hwdef, Finset.sum_range_succ (fun k => (g ^ (k + 1)) • (0 : Minkowski d)),
      Finset.sum_range_succ' (fun k => (g ^ k) • (0 : Minkowski d)), h, pow_zero, Nat.cast_smul_eq_nsmul ℝ]
  have hc : g • c = c := by
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [smul_eq_lin_add, map_smul, hwdef, map_sum, hsum, smul_sub, smul_smul, inv_mul_cancel₀ hn',
      one_smul]
    abel
  exact ⟨isElliptic_of_fixed_timelike (lorentz.minkQ_apply (linOf_mem g)) hu.2 hLu, c,
    by rw [hc, sub_self, map_zero], by rw [hc, sub_self, minkQ_zero]⟩

/-! ### Lines through a point of the domain of dependence -/

private theorem fst_pos_of_future {v : Minkowski d} (hv : IsFutureCausal v) (hv0 : v ≠ 0) :
    0 < v.1 :=
  lt_of_le_of_ne hv.1 fun h => hv0 (eq_zero_of_fst_eq_zero h.symm hv.2)

/-- Every causal line through a point of `D(S)` meets `S`. -/
theorem exists_mem_line_of_mem_dependenceDomain {S : Set (Minkowski d)} {y : Minkowski d}
    (hy : y ∈ dependenceDomain (minkowski d) ⊤ S) {v : Minkowski d} (hv : IsFutureCausal v)
    (hv0 : v ≠ 0) : ∃ s : ℝ, y + s • v ∈ S := by
  have hv1 := fst_pos_of_future hv hv0
  obtain ⟨_, ⟨τ, -, rfl⟩, hτS⟩ := hy.2 univ (timeLine y v) (inextensible_timeLine y hv hv0)
    ⟨y.1, trivial, timeLine_self hv1⟩
  exact ⟨(τ - y.1) / v.1, by rwa [timeLine_eq_add_smul] at hτS⟩

/-- Every null line through a point of `D(S)` meets `S`, in either time orientation. -/
theorem exists_mem_nullLine_of_mem_dependenceDomain {S : Set (Minkowski d)} {y : Minkowski d}
    (hy : y ∈ dependenceDomain (minkowski d) ⊤ S) {ℓ : Minkowski d} (hℓ0 : ℓ ≠ 0)
    (hℓ : minkQ ℓ = 0) : ∃ s : ℝ, y + s • ℓ ∈ S := by
  have h1 : ℓ.1 ≠ 0 := fun h => hℓ0 (eq_zero_of_fst_eq_zero h hℓ.le)
  rcases lt_or_gt_of_ne h1 with hlt | hgt
  · obtain ⟨s, hs⟩ := exists_mem_line_of_mem_dependenceDomain hy (v := -ℓ)
      ⟨by simp; linarith, by simpa using hℓ.le⟩ (neg_ne_zero.2 hℓ0)
    exact ⟨-s, by rwa [neg_smul, ← smul_neg]⟩
  · exact exists_mem_line_of_mem_dependenceDomain hy ⟨hgt.le, hℓ.le⟩ hℓ0

/-! ### Compactness of `J^∓(y) ∩ S` (the hub step) -/

variable {f : EuclideanSpace ℝ (Fin d) → ℝ}

theorem isCompact_Jminus_inter_graph (hf : IsStrictContraction f) {z : Minkowski d}
    (hmeet : ∀ v : Minkowski d, IsFutureCausal v → v ≠ 0 → ∃ s : ℝ, z + s • v ∈ graph f) :
    IsCompact ((minkowski d).Jminus ⊤ {z} ∩ graph f) := by
  have hlip := hf.lipschitzWith
  have hK : IsCompact ((minkowski d).Jminus ⊤ {z} ∩ {q | 0 ≤ timeSub f q}) := by
    obtain ⟨b, hb⟩ := bddBelow_fst_Jminus_inter hf hmeet
    refine Metric.isCompact_of_isClosed_isBounded
      ((staticCausality.isClosed_Jminus_top z).inter
        (isClosed_le continuous_const (continuous_timeSub hlip)))
      ((Metric.isBounded_closedBall (x := z) (r := z.1 - b)).subset fun q hq => ?_)
    have h1 := hb ⟨q, hq, rfl⟩
    have h2 := minkowski_le_top_iff.1 (Precausality.mem_Jminus_singleton.1 hq.1)
    rw [Metric.mem_closedBall, Prod.dist_eq, Real.dist_eq, dist_eq_norm, norm_sub_rev,
      abs_of_nonpos (by linarith [norm_nonneg (z.2 - q.2)])]
    exact max_le (by linarith) (by linarith)
  refine hK.of_isClosed_subset ((staticCausality.isClosed_Jminus_top z).inter
    (isClosed_graph hlip.continuous)) fun q hq => ⟨hq.1, ?_⟩
  exact le_of_eq (mem_graph_iff_timeSub.1 hq.2).symm

theorem isCompact_Jplus_inter_graph (hf : IsStrictContraction f) {z : Minkowski d}
    (hmeet : ∀ v : Minkowski d, IsFutureCausal v → v ≠ 0 → ∃ s : ℝ, z + s • v ∈ graph f) :
    IsCompact ((minkowski d).Jplus ⊤ {z} ∩ graph f) := by
  have hlip := hf.lipschitzWith
  have hK : IsCompact ((minkowski d).Jplus ⊤ {z} ∩ {q | timeSub f q ≤ 0}) := by
    obtain ⟨b, hb⟩ := bddAbove_fst_Jplus_inter hf hmeet
    refine Metric.isCompact_of_isClosed_isBounded
      ((staticCausality.isClosed_Jplus_top z).inter
        (isClosed_le (continuous_timeSub hlip) continuous_const))
      ((Metric.isBounded_closedBall (x := z) (r := b - z.1)).subset fun q hq => ?_)
    have h1 := hb ⟨q, hq, rfl⟩
    have h2 := minkowski_le_top_iff.1 (Precausality.mem_Jplus_singleton.1 hq.1)
    rw [Metric.mem_closedBall, Prod.dist_eq, Real.dist_eq, dist_eq_norm,
      abs_of_nonneg (by linarith [norm_nonneg (q.2 - z.2)])]
    exact max_le (by linarith) (by linarith)
  refine hK.of_isClosed_subset ((staticCausality.isClosed_Jplus_top z).inter
    (isClosed_graph hlip.continuous)) fun q hq => ⟨hq.1, ?_⟩
  exact le_of_eq (mem_graph_iff_timeSub.1 hq.2)

/-! ### The standing hypotheses of §8 in `𝐌ⁿ` -/

/-- **The standing hypotheses of §8, read in `𝐌ⁿ`** (l.2240–2275 and Cor 8.2, l.2266–2275):
`Σ = 𝒟(S̃)` satisfies (CC′) (DEC-35), and the holonomy group `Γ` preserves `Σ` and acts on it
freely and properly discontinuously (as `π₁(S)` acts on the universal cover `S̃`). -/
structure CCAction (Γ : Subgroup (isom d)) (S : Set (Minkowski d)) : Prop where
  cc : CCPrime S
  inv : ∀ γ ∈ Γ, γ • S = S
  free : ∀ γ ∈ Γ, γ ≠ 1 → ∀ x ∈ S, γ • x ≠ x
  proper : ∀ K ⊆ S, IsCompact K → {γ : isom d | γ ∈ Γ ∧ (γ • K ∩ K).Nonempty}.Finite

variable {Γ : Subgroup (isom d)} {S : Set (Minkowski d)}

namespace CCAction

theorem nonempty (h : CCAction Γ S) : S.Nonempty := by
  obtain ⟨s, hs⟩ := h.cc.entire.meets 0 _ isFutureTimelike_vertical
  exact ⟨_, hs⟩

theorem smul_mem (h : CCAction Γ S) {γ : isom d} (hγ : γ ∈ Γ) {x : Minkowski d} (hx : x ∈ S) :
    γ • x ∈ S := by
  have := Set.smul_mem_smul_set (a := γ) hx
  rwa [h.inv γ hγ] at this

/-- **Lemma 8.6, the nonspacelike elliptic case** (l.2374–2379): the fixed timelike line of
`L(γ)` through any point meets `Σ` at `y`, and `γ y = y + τ` with `τ` nonspacelike, against
freeness (`τ = 0`) or acausality (`τ ≠ 0`). -/
theorem not_isNonspacelikeElliptic (h : CCAction Γ S) {γ : isom d} (hγ : γ ∈ Γ) (h1 : γ ≠ 1) :
    ¬IsNonspacelikeElliptic γ := by
  rintro ⟨hE, x, -, hq⟩
  obtain ⟨u, hu, hLu⟩ := hE.exists_fixed_timelike (linOf_mem γ)
  obtain ⟨s, hs⟩ := h.cc.entire.meets x u hu
  have hτ : γ • (x + s • u) - (x + s • u) = γ • x - x := by
    rw [isom_smul_add_smul, hLu]; abel
  by_cases e : γ • (x + s • u) = x + s • u
  · exact h.free γ hγ h1 _ hs e
  · have := isAcausal_iff_minkQ.1 h.cc.entire.acausal _ hs _ (h.smul_mem hγ hs) (Ne.symm e)
    rw [hτ] at this
    linarith

/-- `Γ` is torsion-free. -/
theorem pow_ne_one (h : CCAction Γ S) {γ : isom d} (hγ : γ ∈ Γ) (h1 : γ ≠ 1) {n : ℕ}
    (hn : 0 < n) : γ ^ n ≠ 1 := fun e =>
  h.not_isNonspacelikeElliptic hγ h1 (isNonspacelikeElliptic_of_pow_eq_one γ hn e)

theorem zpow_ne_one (h : CCAction Γ S) {γ : isom d} (hγ : γ ∈ Γ) (h1 : γ ≠ 1) {n : ℤ}
    (hn : n ≠ 0) : γ ^ n ≠ 1 := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · rw [zpow_natCast]; exact h.pow_ne_one hγ h1 (by omega)
  · rw [zpow_neg, zpow_natCast, inv_ne_one]; exact h.pow_ne_one hγ h1 (by omega)

theorem not_isOfFinOrder (h : CCAction Γ S) {γ : isom d} (hγ : γ ∈ Γ) (h1 : γ ≠ 1) :
    ¬IsOfFinOrder γ := fun ho => by
  obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 ho
  exact h.pow_ne_one hγ h1 hn e

/-- Infinitely many elements of `Γ` cannot move a compact `K ⊆ Σ` onto itself. -/
theorem false_of_injective (h : CCAction Γ S) {K : Set (Minkowski d)} (hK : K ⊆ S)
    (hKc : IsCompact K) {g : ℕ → isom d} (hg : Injective g)
    (hmem : ∀ m, g m ∈ Γ ∧ (g m • K ∩ K).Nonempty) : False := by
  have hfin := (h.proper K hK hKc).subset (show range g ⊆ _ from by
    rintro _ ⟨m, rfl⟩; exact hmem m)
  exact Set.infinite_range_of_injective hg hfin

/-- **The repaired interior argument** (`docs/BARBOT-WAVE3.md` §3, Lemma 8.6): no point `y` of
the domain of dependence of `Σ` lies causally below its image under a nontrivial element of `Γ`.
If `T(y) ≥ 0`, the points `k^{-m} z₀`, `z₀ ∈ Σ` below `y`, all lie in the compact
`J⁻(y) ∩ Σ` (hub step); properness makes `⟨k⟩` finite, which torsion-freeness excludes. If
`T(y) ≤ 0`, the same with `k^m` and `J⁺(y) ∩ Σ`. -/
theorem false_of_le_smul (h : CCAction Γ S) {k : isom d} (hk : k ∈ Γ) (h1 : k ≠ 1)
    {y : Minkowski d} (hy : y ∈ dependenceDomain (minkowski d) ⊤ S)
    (hle : (minkowski d).le ⊤ y (k • y)) : False := by
  obtain ⟨f, hf, rfl⟩ := isEntireAcausalGraph_iff.1 h.cc.entire
  have hmeet := fun (v : Minkowski d) (hv : IsFutureCausal v) (hv0 : v ≠ 0) =>
    exists_mem_line_of_mem_dependenceDomain hy hv hv0
  have hinj : Injective fun m : ℕ => k ^ m :=
    injective_pow_iff_not_isOfFinOrder.2 (h.not_isOfFinOrder hk h1)
  have hz₀ : ((f y.2, y.2) : Minkowski d) ∈ graph f := mk_mem_graph y.2
  rcases le_total 0 (timeSub f y) with hT | hT
  · -- backwards: `k^{-m} y ≤ y`
    have hback : ∀ m : ℕ, (minkowski d).le ⊤ ((k ^ m)⁻¹ • y) y := by
      intro m
      induction m with
      | zero => simpa using (minkowski d).le_refl (show y ∈ (⊤ : Opens (Minkowski d)) from trivial)
      | succ m ih =>
        refine (minkowski d).le_trans ?_ ih
        have := (isom_le_top_iff (k ^ (m + 1))⁻¹).2 hle
        rwa [← mul_smul, pow_succ', mul_inv_rev, inv_mul_cancel_right, ← mul_inv_rev, ← pow_succ']
          at this
    have hz₀y : (minkowski d).le ⊤ ((f y.2, y.2) : Minkowski d) y := by
      rw [minkowski_le_top_iff]; simpa [timeSub] using hT
    refine h.false_of_injective inter_subset_right (isCompact_Jminus_inter_graph hf hmeet)
      hinj fun m => ⟨pow_mem hk m, ⟨(f y.2, y.2), ?_, ?_, hz₀⟩⟩
    · refine ⟨(k ^ m)⁻¹ • ((f y.2, y.2) : Minkowski d), ⟨?_, h.smul_mem (inv_mem (pow_mem hk m)) hz₀⟩,
        smul_inv_smul _ _⟩
      exact Precausality.mem_Jminus_singleton.2 ((minkowski d).le_trans
        ((isom_le_top_iff _).2 hz₀y) (hback m))
    · exact Precausality.mem_Jminus_singleton.2 hz₀y
  · -- forwards: `y ≤ k^m y`
    have hfwd : ∀ m : ℕ, (minkowski d).le ⊤ y ((k ^ m) • y) := by
      intro m
      induction m with
      | zero => simpa using (minkowski d).le_refl (show y ∈ (⊤ : Opens (Minkowski d)) from trivial)
      | succ m ih =>
        refine (minkowski d).le_trans ih ?_
        have := (isom_le_top_iff (k ^ m)).2 hle
        rwa [← mul_smul, ← pow_succ] at this
    have hyz₀ : (minkowski d).le ⊤ y ((f y.2, y.2) : Minkowski d) := by
      rw [minkowski_le_top_iff]; simpa [timeSub] using hT
    refine h.false_of_injective inter_subset_right (isCompact_Jplus_inter_graph hf hmeet)
      (inv_injective.comp hinj) fun m => ⟨inv_mem (pow_mem hk m), ⟨(f y.2, y.2), ?_, ?_, hz₀⟩⟩
    · refine ⟨(k ^ m) • ((f y.2, y.2) : Minkowski d), ⟨?_, h.smul_mem (pow_mem hk m) hz₀⟩,
        inv_smul_smul _ _⟩
      exact Precausality.mem_Jplus_singleton.2 ((minkowski d).le_trans (hfwd m)
        ((isom_le_top_iff _).2 hyz₀))
    · exact Precausality.mem_Jplus_singleton.2 hyz₀

/-- **`D(Σ) ⊆ Ω_γ`** for every nontrivial `γ ∈ Γ`. -/
theorem dependenceDomain_subset_achronalDomain (h : CCAction Γ S) {γ : isom d} (hγ : γ ∈ Γ)
    (h1 : γ ≠ 1) : dependenceDomain (minkowski d) ⊤ S ⊆ achronalDomain γ := by
  intro y hy q hq
  by_contra hneg
  have hk : γ ^ q ∈ Γ := zpow_mem hγ q
  have hk1 : γ ^ q ≠ 1 := h.zpow_ne_one hγ h1 hq
  rcases le_top_or_of_minkQ_nonpos (not_lt.1 hneg) with hle | hle
  · exact h.false_of_le_smul hk hk1 hy hle
  · refine h.false_of_le_smul (inv_mem hk) (inv_ne_one.2 hk1) hy ?_
    have := (isom_le_top_iff (γ ^ q)⁻¹).2 hle
    rwa [inv_smul_smul] at this

/-- **Lemma 8.6, the linear parabolic case** (l.2368–2372), on `D(Σ)`: a null line of direction
`J` through `y ∈ D(Σ)` meets `Σ`, so the null hyperplane `c + J^⊥` through `y` meets `Σ`; by
(CC′)(b) (Barbot's Cor 8.3) `Σ` then meets the line `c + J` of fixed points, against freeness. -/
theorem dependenceDomain_subset_compl_nullHyperplanes (h : CCAction Γ S) {γ : isom d}
    (hγ : γ ∈ Γ) (h1 : γ ≠ 1) : dependenceDomain (minkowski d) ⊤ S ⊆ (nullHyperplanes γ)ᶜ := by
  rintro y hy ⟨R, U, ⟨hR, hU, hRe, hn, hU1, hg, hc⟩, c, hcfix, hyc⟩
  obtain ⟨v₀, hv₀, hv₀0⟩ := exists_mem_nullPart_ne_zero hU.1 hn (pOf_ne_zero hU1)
  have hq0 := minkQ_eq_zero_of_mem_nullPart hv₀
  have hUv : U v₀ = v₀ := by
    have := pOf_eq_zero_of_mem_nullPart hU.1 hv₀
    rwa [pOf_apply, sub_eq_zero] at this
  have hfix : linOf γ v₀ = v₀ := by
    rw [hg, LinearEquiv.mul_apply, hUv, parabolic_R_fix_nullPart hR hU hRe hc hv₀]
  obtain ⟨s, hs⟩ := exists_mem_nullLine_of_mem_dependenceDomain hy hv₀0 hq0
  have hyc' : minkB (y - c) v₀ = 0 := mem_minkOrth'.1 hyc v₀ hv₀
  obtain ⟨t, ht⟩ := h.cc.nullSat c v₀ hv₀0 hq0 ⟨y + s • v₀, hs, by
    rw [show y + s • v₀ - c = (y - c) + s • v₀ by abel, minkB_add_left, minkB_smul_left, hyc',
      ← minkQ_eq_minkB, hq0]; ring⟩ c (by simp [minkB])
  exact h.free γ hγ h1 _ ht (by rw [isom_smul_add_smul, hcfix, hfix])

/-- **Lemma 8.6, core**: `D(Σ) ⊆ U(Γ)`. -/
theorem dependenceDomain_subset_UGamma (h : CCAction Γ S) :
    dependenceDomain (minkowski d) ⊤ S ⊆ UGamma Γ := by
  intro y hy γ hγ h1
  unfold Ug
  split_ifs with h2 h3
  · exact (h.not_isNonspacelikeElliptic hγ h1 h2).elim
  · exact h.dependenceDomain_subset_compl_nullHyperplanes hγ h1 hy
  · exact h.dependenceDomain_subset_achronalDomain hγ h1 hy

end CCAction

/-- **Lemma 8.6** (`blem:SdanU`, l.2353–2358): `Σ ⊆ U(γ)` for every nontrivial `γ ∈ Γ`, and `Σ`
lies in the interior `Ω(Γ)` of `U(Γ)`, because the interior of the domain of dependence of `Σ` is
a neighbourhood of `Σ` inside `U(Γ)`. -/
theorem blem_SdanU (h : CCAction Γ S) :
    (∀ γ ∈ Γ, γ ≠ 1 → S ⊆ Ug γ) ∧ S ⊆ omegaGamma Γ := by
  have hD : S ⊆ dependenceDomain (minkowski d) ⊤ S := subset_dependenceDomain fun _ _ => trivial
  refine ⟨fun γ hγ h1 x hx => h.dependenceDomain_subset_UGamma (hD hx) γ hγ h1, ?_⟩
  obtain ⟨f, hf, hfS⟩ := isEntireAcausalGraph_iff.1 h.cc.entire
  have := graph_subset_interior_dependenceDomain hf
  rw [← hfS] at this
  exact this.trans (interior_mono h.dependenceDomain_subset_UGamma)

/-- **Non-vacuity of `CCAction`** (kb/0011): any (CC′) surface with the trivial group, e.g. the
hyperboloid (`ccPrime_graph_hyperboloid`) or a horizontal hyperplane. -/
theorem ccAction_bot {S : Set (Minkowski d)} (h : CCPrime S) : CCAction ⊥ S where
  cc := h
  inv γ hγ := by rw [Subgroup.mem_bot.1 hγ, one_smul]
  free γ hγ h1 := absurd (Subgroup.mem_bot.1 hγ) h1
  proper K _ _ := (Set.finite_singleton (1 : isom d)).subset fun γ hγ =>
    Subgroup.mem_bot.1 hγ.1

example : (∀ γ ∈ (⊥ : Subgroup (isom d)), γ ≠ 1 → graph (hyperboloid d) ⊆ Ug γ) ∧
    graph (hyperboloid d) ⊆ omegaGamma ⊥ :=
  blem_SdanU (ccAction_bot ccPrime_graph_hyperboloid)

/-! ### Rem 8.9 (`nini`): no nonspacelike elliptic, no transverse parabolic, no torsion -/

/-- A transverse parabolic isometry has empty achronal domain (AchronalDomains' [7.P], carried to
the whole class through the normal form). -/
theorem achronalDomain_eq_empty_of_isTransverseParabolic {g : isom d}
    (ht : IsTransverseParabolic g) : achronalDomain g = ∅ := by
  obtain ⟨R, U, ⟨hR, hU, hRe, hn, hU1, hg, hc⟩, hT⟩ := ht
  obtain ⟨vₙ, v₁, -, h1, -, -, -, -, hq1, -⟩ := unipotent_frame hU.1 hn (pOf_ne_zero hU1)
  obtain ⟨v, hv, -⟩ := parabolic_exists_transConj_normal hR hU hRe hn hU1 hc hg
    (v₁ := v₁) ⟨vₙ, h1⟩ hq1.ne'
  have hT' : IsTransverseCase U (transConj v (g : Minkowski d ≃ᵃ[ℝ] Minkowski d)) :=
    (parabolic_isTransverseCase_transConj_iff hR hU hRe hn hU1 hc hg v).2 hT
  have h0 := achronalDomain_parabolic_transverse hR hU hRe hn hU1 hc
    (g := isomConj v g) (by rw [linOf_isomConj]; exact hg) hv hT'
  rw [achronalDomain_eq_preimage_isomConj v g, h0, preimage_empty]

/-- **Rem 8.9** (`nini`, l.2411–2415): under the standing hypotheses, `Γ` has no nonspacelike
elliptic element, no transverse parabolic element, and no torsion. -/
theorem nini (h : CCAction Γ S) {γ : isom d} (hγ : γ ∈ Γ) (h1 : γ ≠ 1) :
    ¬IsNonspacelikeElliptic γ ∧ ¬IsTransverseParabolic γ ∧ ∀ n : ℤ, n ≠ 0 → γ ^ n ≠ 1 := by
  refine ⟨h.not_isNonspacelikeElliptic hγ h1, fun ht => ?_, fun n hn => h.zpow_ne_one hγ h1 hn⟩
  obtain ⟨x, hx⟩ := h.nonempty
  have := h.dependenceDomain_subset_achronalDomain hγ h1
    (subset_dependenceDomain (C := minkowski d) (W := ⊤) (fun _ _ => trivial) hx)
  rw [achronalDomain_eq_empty_of_isTransverseParabolic ht] at this
  exact this

/-! ### `U(g) ⊆ Ω_g` -/

/-- In the linear parabolic case the complement of the null hyperplanes `c + J^⊥` lies in `Ω_g`
(AchronalDomains' [7.P] linear case, after conjugating the fixed point `c` to `0`). -/
theorem compl_nullHyperplanes_subset_achronalDomain {g : isom d} (hL : IsLinearParabolic g) :
    (nullHyperplanes g)ᶜ ⊆ achronalDomain g := by
  obtain ⟨⟨R, U, hR, hU, hRe, hn, hU1, hg, hc⟩, c, hcfix⟩ := hL
  intro y hy
  have hyc : y - c ∉ minkOrth (nullPart U) := fun hm =>
    hy ⟨R, U, ⟨hR, hU, hRe, hn, hU1, hg, hc⟩, c, hcfix, hm⟩
  have hτ : trOf g = c - linOf g c := by
    have e := smul_eq_lin_add g c
    rw [hcfix] at e
    rw [eq_sub_iff_add_eq, add_comm]; exact e.symm
  have h0 : trOf (isomConj (-c) g) = 0 := by
    rw [trOf_isomConj, map_neg, pOf_apply, hτ]; abel
  have hmem := achronalDomain_parabolic_linear hR hU hRe hn hU1 hc (g := isomConj (-c) g)
    (by rw [linOf_isomConj]; exact hg) h0
  have : y - c ∈ achronalDomain (isomConj (-c) g) := by
    rw [hmem]; exact fun h' => hyc h'.1
  rw [mem_achronalDomain_isomConj, neg_neg, add_sub_cancel] at this
  exact this

/-- **`U(g) ⊆ Ω_g`** for every isometry. -/
theorem Ug_subset_achronalDomain (g : isom d) : Ug g ⊆ achronalDomain g := by
  unfold Ug
  split_ifs with h1 h2
  · exact empty_subset _
  · exact compl_nullHyperplanes_subset_achronalDomain h2
  · exact subset_rfl

/-! ### Conjugation: `U(h g h⁻¹) = h U(g)` -/

theorem linOf_mul (a b : isom d) : linOf (a * b) = linOf a * linOf b := by
  show AffineEquiv.linearHom ((a * b : isom d) : Minkowski d ≃ᵃ[ℝ] Minkowski d) = _
  rw [Subgroup.coe_mul, map_mul]
  rfl

theorem linOf_inv (a : isom d) : linOf a⁻¹ = (linOf a)⁻¹ := by
  show AffineEquiv.linearHom ((a⁻¹ : isom d) : Minkowski d ≃ᵃ[ℝ] Minkowski d) = _
  rw [Subgroup.coe_inv, map_inv]
  rfl

theorem linOf_conj (h g : isom d) :
    linOf (h * g * h⁻¹) = linOf h * linOf g * (linOf h)⁻¹ := by
  rw [linOf_mul, linOf_mul, linOf_inv]

theorem conj_smul_smul (h g : isom d) (x : Minkowski d) :
    (h * g * h⁻¹) • (h • x) = h • (g • x) := by
  rw [mul_smul, mul_smul, inv_smul_smul]

private theorem linEquiv_conj_apply (C A : Minkowski d ≃ₗ[ℝ] Minkowski d) (w : Minkowski d) :
    (C * A * C⁻¹) (C w) = C (A w) := by
  simp [LinearEquiv.mul_apply]

private theorem linEquiv_inv_apply_self (C : Minkowski d ≃ₗ[ℝ] Minkowski d) (w : Minkowski d) :
    C⁻¹ (C w) = w := by
  simp

private theorem linEquiv_apply_inv_apply (C : Minkowski d ≃ₗ[ℝ] Minkowski d) (w : Minkowski d) :
    C (C⁻¹ w) = w := by
  simp

private theorem conj_conj_inv_isom (h g : isom d) : h⁻¹ * (h * g * h⁻¹) * h⁻¹⁻¹ = g := by group

theorem IsNonspacelikeElliptic.conj {g : isom d} (hg : IsNonspacelikeElliptic g) (h : isom d) :
    IsNonspacelikeElliptic (h * g * h⁻¹) := by
  obtain ⟨hE, x, hx1, hx2⟩ := hg
  refine ⟨linOf_conj h g ▸ hE.conj _, h • x, ?_, ?_⟩
  · rw [conj_smul_smul, smul_sub_smul, linOf_conj, linEquiv_conj_apply, hx1]
  · rw [conj_smul_smul, isom_minkQ_sub]; exact hx2

theorem isNonspacelikeElliptic_conj_iff (h g : isom d) :
    IsNonspacelikeElliptic (h * g * h⁻¹) ↔ IsNonspacelikeElliptic g := by
  refine ⟨fun H => ?_, fun H => H.conj h⟩
  have := H.conj h⁻¹
  rwa [conj_conj_inv_isom] at this

theorem IsLinearParabolic.conj {g : isom d} (hg : IsLinearParabolic g) (h : isom d) :
    IsLinearParabolic (h * g * h⁻¹) := by
  obtain ⟨hP, c, hc⟩ := hg
  exact ⟨linOf_conj h g ▸ hP.conj (linOf_mem h), h • c, by rw [conj_smul_smul, hc]⟩

theorem isLinearParabolic_conj_iff (h g : isom d) :
    IsLinearParabolic (h * g * h⁻¹) ↔ IsLinearParabolic g := by
  refine ⟨fun H => ?_, fun H => H.conj h⟩
  have := H.conj h⁻¹
  rwa [conj_conj_inv_isom] at this

theorem IsParabolicPair.conj {g : isom d} {R U : Minkowski d ≃ₗ[ℝ] Minkowski d}
    (hp : IsParabolicPair g R U) (h : isom d) :
    IsParabolicPair (h * g * h⁻¹) (linOf h * R * (linOf h)⁻¹) (linOf h * U * (linOf h)⁻¹) := by
  obtain ⟨hR, hU, hRe, hn, hU1, hg, hc⟩ := hp
  refine ⟨lorentz.conj_mem (linOf_mem h) hR, lorentz.conj_mem (linOf_mem h) hU, hRe.conj _,
    hn.conj _, fun e => hU1 ?_, by rw [linOf_conj, hg]; group, ?_⟩
  · have := congrArg (fun X => (linOf h)⁻¹ * X * linOf h) e
    simpa [mul_assoc] using this
  · rw [show linOf h * R * (linOf h)⁻¹ * (linOf h * U * (linOf h)⁻¹) =
      linOf h * (R * U) * (linOf h)⁻¹ by group, hc]
    group

theorem mem_nullPart_of_conj {C U : Minkowski d ≃ₗ[ℝ] Minkowski d} (hC : C ∈ lorentz d)
    {v : Minkowski d} (hv : v ∈ nullPart (C * U * C⁻¹)) : C⁻¹ v ∈ nullPart U := by
  obtain ⟨⟨y, rfl⟩, h2⟩ := hv
  refine ⟨⟨C⁻¹ y, by rw [pOf_conj, linEquiv_inv_apply_self]⟩, mem_minkOrth.2 ?_⟩
  rintro _ ⟨z, rfl⟩
  have := mem_minkOrth.1 h2 _ ⟨C z, rfl⟩
  rw [pOf_conj, linEquiv_inv_apply_self] at this
  rw [← minkB_map hC.1, linEquiv_apply_inv_apply]
  exact this

theorem smul_mem_nullHyperplanes (h : isom d) {g : isom d} {x : Minkowski d}
    (hx : x ∈ nullHyperplanes g) : h • x ∈ nullHyperplanes (h * g * h⁻¹) := by
  obtain ⟨R, U, hp, c, hc, hxc⟩ := hx
  refine ⟨_, _, hp.conj h, h • c, by rw [conj_smul_smul, hc], mem_minkOrth.2 fun v hv => ?_⟩
  have := mem_nullPart_of_conj (linOf_mem h) hv
  rw [smul_sub_smul, ← linEquiv_apply_inv_apply (linOf h) v, minkB_linOf]
  exact mem_minkOrth.1 hxc _ this

theorem smul_mem_Ug (h : isom d) {g : isom d} {x : Minkowski d} (hx : x ∈ Ug g) :
    h • x ∈ Ug (h * g * h⁻¹) := by
  by_cases hN : IsNonspacelikeElliptic g
  · rw [Ug, if_pos hN] at hx; exact absurd hx (notMem_empty x)
  have hN' : ¬IsNonspacelikeElliptic (h * g * h⁻¹) := fun H =>
    hN ((isNonspacelikeElliptic_conj_iff h g).1 H)
  by_cases hL : IsLinearParabolic g
  · rw [Ug, if_neg hN, if_pos hL] at hx
    rw [Ug, if_neg hN', if_pos (hL.conj h)]
    intro hm
    apply hx
    have := smul_mem_nullHyperplanes h⁻¹ hm
    rwa [conj_conj_inv_isom, inv_smul_smul] at this
  · have hL' : ¬IsLinearParabolic (h * g * h⁻¹) := fun H => hL ((isLinearParabolic_conj_iff h g).1 H)
    rw [Ug, if_neg hN, if_neg hL] at hx
    rw [Ug, if_neg hN', if_neg hL', mem_achronalDomain_conj, inv_smul_smul]
    exact hx

theorem smul_mem_UGamma {γ' : isom d} (hγ' : γ' ∈ Γ) {x : Minkowski d} (hx : x ∈ UGamma Γ) :
    γ' • x ∈ UGamma Γ := by
  intro γ hγ h1
  have hm : γ'⁻¹ * γ * γ'⁻¹⁻¹ ∈ Γ :=
    Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hγ') hγ) (Γ.inv_mem (Γ.inv_mem hγ'))
  have hne : γ'⁻¹ * γ * γ'⁻¹⁻¹ ≠ 1 := fun e => h1 (by
    have := congrArg (fun X => γ' * X * γ'⁻¹) e
    simpa [mul_assoc] using this)
  have := smul_mem_Ug γ' (hx _ hm hne)
  rwa [show γ' * (γ'⁻¹ * γ * γ'⁻¹⁻¹) * γ'⁻¹ = γ by group] at this

theorem smul_UGamma {γ' : isom d} (hγ' : γ' ∈ Γ) : γ' • UGamma Γ = UGamma Γ := by
  refine Subset.antisymm (Set.smul_set_subset_iff.2 fun x hx => smul_mem_UGamma hγ' hx)
    fun x hx => Set.mem_smul_set_iff_inv_smul_mem.2 (smul_mem_UGamma (Γ.inv_mem hγ') hx)

theorem smul_omegaGamma {γ' : isom d} (hγ' : γ' ∈ Γ) : γ' • omegaGamma Γ = omegaGamma Γ := by
  rw [omegaGamma, ← interior_smul, smul_UGamma hγ']

/-! ### `Ω(S̃)` is one connected component -/

theorem isPreconnected_graph (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : Continuous f) :
    IsPreconnected (graph f) := by
  have : graph f = range fun x : EuclideanSpace ℝ (Fin d) => ((f x, x) : Minkowski d) := by
    ext p
    simp only [mem_graph, mem_range]
    exact ⟨fun h => ⟨p.2, Prod.ext h.symm rfl⟩, by rintro ⟨x, rfl⟩; rfl⟩
  rw [this]
  exact isPreconnected_range (hf.prodMk continuous_id)

theorem CCAction.isPreconnected (h : CCAction Γ S) : IsPreconnected S := by
  obtain ⟨f, hf, rfl⟩ := isEntireAcausalGraph_iff.1 h.cc.entire
  exact isPreconnected_graph f hf.lipschitzWith.continuous

/-- **`Ω(S̃)` is the connected component of `Ω(Γ)` containing `Σ`** (Def 8.7), any of its points
naming it. -/
theorem omegaS_eq (h : CCAction Γ S) {x : Minkowski d} (hx : x ∈ S) :
    omegaS Γ S = connectedComponentIn (omegaGamma Γ) x := by
  have hsub : S ⊆ connectedComponentIn (omegaGamma Γ) x :=
    h.isPreconnected.subset_connectedComponentIn hx (blem_SdanU h).2
  ext z
  simp only [omegaS, mem_iUnion]
  constructor
  · rintro ⟨y, hy, hz⟩
    rwa [← connectedComponentIn_eq (hsub hy)] at hz
  · exact fun hz => ⟨x, hx, hz⟩

theorem subset_omegaS (h : CCAction Γ S) : S ⊆ omegaS Γ S := fun x hx => by
  rw [omegaS_eq h hx]
  exact mem_connectedComponentIn ((blem_SdanU h).2 hx)

theorem isOpen_omegaS (Γ : Subgroup (isom d)) (S : Set (Minkowski d)) : IsOpen (omegaS Γ S) :=
  isOpen_biUnion fun _ _ => isOpen_interior.connectedComponentIn

theorem omegaS_subset_omegaGamma (Γ : Subgroup (isom d)) (S : Set (Minkowski d)) :
    omegaS Γ S ⊆ omegaGamma Γ :=
  iUnion₂_subset fun _ _ => connectedComponentIn_subset _ _

/-- `Ω(S̃)` as an open set. -/
def omegaSOpens (Γ : Subgroup (isom d)) (S : Set (Minkowski d)) : Opens (Minkowski d) :=
  ⟨omegaS Γ S, isOpen_omegaS Γ S⟩

theorem smul_omegaS (h : CCAction Γ S) {γ' : isom d} (hγ' : γ' ∈ Γ) :
    γ' • omegaS Γ S = omegaS Γ S := by
  obtain ⟨x, hx⟩ := h.nonempty
  have hsub := subset_omegaS h
  rw [omegaS_eq h hx] at hsub ⊢
  have := (isom.toHomeomorph γ').image_connectedComponentIn ((blem_SdanU h).2 hx)
  simp only [isom.coe_toHomeomorph, Set.image_smul] at this
  rw [this, smul_omegaGamma hγ']
  exact (connectedComponentIn_eq (hsub (h.smul_mem hγ' hx))).symm

/-! ### Convexity and causal convexity of the components (obligation W8) -/

/-- **The piece property** of `A ⊆ 𝐌ⁿ`: two points of a connected subset of `int A` span a
segment inside `A`, and, if causally related, a diamond inside `A`. -/
def IsCausalPiece (A : Set (Minkowski d)) : Prop :=
  ∀ s : Set (Minkowski d), IsPreconnected s → s ⊆ interior A → ∀ x ∈ s, ∀ y ∈ s,
    segment ℝ x y ⊆ A ∧ ((minkowski d).le ⊤ x y → (minkowski d).diamond ⊤ x y ⊆ A)

theorem isCausalPiece_empty : IsCausalPiece (∅ : Set (Minkowski d)) := fun _ _ hs x hx => by
  rw [interior_empty] at hs; exact absurd (hs hx) (notMem_empty x)

theorem minkB_nonpos_of_future {a b : Minkowski d} (ha : IsFutureCausal a)
    (hb : IsFutureCausal b) : minkB a b ≤ 0 := by
  have han : ‖a.2‖ ≤ a.1 := (sq_le_sq₀ (norm_nonneg _) ha.1).1 (minkQ_le_zero_iff.1 ha.2)
  have hbn : ‖b.2‖ ≤ b.1 := (sq_le_sq₀ (norm_nonneg _) hb.1).1 (minkQ_le_zero_iff.1 hb.2)
  have hin := real_inner_le_norm a.2 b.2
  simp only [minkB]
  nlinarith [norm_nonneg a.2, norm_nonneg b.2]

/-- **The linear parabolic `U(g)`, the complement of the null hyperplanes, has the piece
property**: on a connected set avoiding `c + J^⊥` the affine function `⟨v₀ | · − c⟩` keeps one
sign, and it is monotone along causal curves. -/
theorem isCausalPiece_compl_nullHyperplanes (g : isom d) :
    IsCausalPiece (nullHyperplanes g)ᶜ := by
  intro s hs hsA x hx y hy
  have hsA' : s ⊆ (nullHyperplanes g)ᶜ := hsA.trans interior_subset
  -- the claim, hyperplane by hyperplane
  suffices key : ∀ z, (z ∈ segment ℝ x y ∨ ((minkowski d).le ⊤ x z ∧ (minkowski d).le ⊤ z y)) →
      z ∉ nullHyperplanes g by
    refine ⟨fun z hz => key z (Or.inl hz), fun _ z hz => key z (Or.inr ?_)⟩
    exact Causality.mem_diamond.1 hz
  rintro z hz ⟨R, U, hp, c, hc, hzc⟩
  have hp0 := hp
  obtain ⟨-, hU, -, hn, hU1, -, -⟩ := hp0
  obtain ⟨v₀, hv₀, hv₀0⟩ := exists_mem_nullPart_ne_zero hU.1 hn (pOf_ne_zero hU1)
  have hspan := nullPart_eq_span_of_mem hv₀ hv₀0
  have hq0 := minkQ_eq_zero_of_mem_nullPart hv₀
  set φ : Minkowski d → ℝ := fun w => minkB v₀ (w - c) with hφ
  have hiff : ∀ w, w - c ∈ minkOrth (nullPart U) ↔ φ w = 0 := by
    intro w
    refine ⟨fun hw => mem_minkOrth.1 hw v₀ hv₀, fun hw => mem_minkOrth.2 fun u hu => ?_⟩
    rw [hspan] at hu
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hu
    rw [minkB_smul_left]; simp [φ] at hw; rw [hw, mul_zero]
  have hne : ∀ w ∈ s, φ w ≠ 0 := fun w hw h0 => hsA' hw ⟨R, U, hp, c, hc, (hiff w).2 h0⟩
  have hφc : Continuous φ :=
    ((minkForm d v₀).continuous_of_finiteDimensional).comp (continuous_id.sub continuous_const)
  -- `φ` keeps one sign on `s`
  have hsign : 0 < φ x * φ y := by
    rcases lt_or_gt_of_ne (hne x hx) with h1 | h1 <;>
      rcases lt_or_gt_of_ne (hne y hy) with h2 | h2
    · nlinarith
    · exfalso
      obtain ⟨w, hw, hw0⟩ := hs.intermediate_value hx hy hφc.continuousOn ⟨h1.le, h2.le⟩
      exact hne w hw hw0
    · exfalso
      obtain ⟨w, hw, hw0⟩ := hs.intermediate_value hy hx hφc.continuousOn ⟨h2.le, h1.le⟩
      exact hne w hw hw0
    · nlinarith
  -- `φ z` lies between `φ x` and `φ y`
  have hφsub : ∀ a b, φ b - φ a = minkB v₀ (b - a) := fun a b => by
    simp only [φ]; rw [← minkB_sub_right]; congr 1; abel
  have hbetween : (φ z - φ x) * (φ z - φ y) ≤ 0 := by
    rcases hz with hz | ⟨hxz, hzy⟩
    · rw [segment_eq_image'] at hz
      obtain ⟨t, ht, rfl⟩ := hz
      have e : φ (x + t • (y - x)) = φ x + t * (φ y - φ x) := by
        rw [hφsub x y]; simp only [φ]
        rw [show x + t • (y - x) - c = (x - c) + t • (y - x) by abel, minkB_add_right,
          minkB_smul_right]
      rw [e]
      nlinarith [ht.1, ht.2, sq_nonneg (φ y - φ x), mul_nonneg ht.1 (sub_nonneg.2 ht.2)]
    · have h1 : v₀.1 ≠ 0 := fun h => hv₀0 (eq_zero_of_fst_eq_zero h hq0.le)
      have hzx := le_top_iff_minkQ.1 hxz
      have hyz := le_top_iff_minkQ.1 hzy
      rcases lt_or_gt_of_ne h1 with hlt | hgt
      · have hfut : IsFutureCausal (-v₀) := ⟨by simp; linarith, by simpa using hq0.le⟩
        have a1 := minkB_nonpos_of_future hfut hzx
        have a2 := minkB_nonpos_of_future hfut hyz
        rw [minkB_neg_left, ← hφsub] at a1 a2
        nlinarith
      · have hfut : IsFutureCausal v₀ := ⟨hgt.le, hq0.le⟩
        have a1 := minkB_nonpos_of_future hfut hzx
        have a2 := minkB_nonpos_of_future hfut hyz
        rw [← hφsub] at a1 a2
        nlinarith
  have hz0 : φ z = 0 := (hiff z).1 hzc
  rw [hz0] at hbetween
  nlinarith
/-- **A null affine function keeps its sign** on the segments and diamonds of a connected set
on which it does not vanish: `ψ = ⟨w | · − c⟩` with `w` null is affine, and monotone along `≤`. -/
theorem pos_mul_of_null {w c : Minkowski d} (hw0 : w ≠ 0) (hw : minkQ w = 0)
    {s : Set (Minkowski d)} (hs : IsPreconnected s) (hne : ∀ z ∈ s, minkB w (z - c) ≠ 0)
    {x y : Minkowski d} (hx : x ∈ s) (hy : y ∈ s) {z : Minkowski d}
    (hz : z ∈ segment ℝ x y ∨ ((minkowski d).le ⊤ x z ∧ (minkowski d).le ⊤ z y)) :
    0 < minkB w (x - c) * minkB w (z - c) := by
  set φ : Minkowski d → ℝ := fun a => minkB w (a - c) with hφ
  have hφc : Continuous φ :=
    ((minkForm d w).continuous_of_finiteDimensional).comp (continuous_id.sub continuous_const)
  have hsign : 0 < φ x * φ y := by
    rcases lt_or_gt_of_ne (hne x hx) with h1 | h1 <;>
      rcases lt_or_gt_of_ne (hne y hy) with h2 | h2
    · nlinarith
    · exfalso
      obtain ⟨a, ha, ha0⟩ := hs.intermediate_value hx hy hφc.continuousOn ⟨h1.le, h2.le⟩
      exact hne a ha ha0
    · exfalso
      obtain ⟨a, ha, ha0⟩ := hs.intermediate_value hy hx hφc.continuousOn ⟨h2.le, h1.le⟩
      exact hne a ha ha0
    · nlinarith
  have hφsub : ∀ a b, φ b - φ a = minkB w (b - a) := fun a b => by
    simp only [φ]; rw [← minkB_sub_right]; congr 1; abel
  have hbetween : (φ z - φ x) * (φ z - φ y) ≤ 0 := by
    rcases hz with hz | ⟨hxz, hzy⟩
    · rw [segment_eq_image'] at hz
      obtain ⟨t, ht, rfl⟩ := hz
      have e : φ (x + t • (y - x)) = φ x + t * (φ y - φ x) := by
        rw [hφsub x y]; simp only [φ]
        rw [show x + t • (y - x) - c = (x - c) + t • (y - x) by abel, minkB_add_right,
          minkB_smul_right]
      rw [e]
      nlinarith [ht.1, ht.2, sq_nonneg (φ y - φ x), mul_nonneg ht.1 (sub_nonneg.2 ht.2)]
    · have h1 : w.1 ≠ 0 := fun h => hw0 (eq_zero_of_fst_eq_zero h hw.le)
      have hzx := le_top_iff_minkQ.1 hxz
      have hyz := le_top_iff_minkQ.1 hzy
      rcases lt_or_gt_of_ne h1 with hlt | hgt
      · have hfut : IsFutureCausal (-w) := ⟨by simp; linarith, by simpa using hw.le⟩
        have a1 := minkB_nonpos_of_future hfut hzx
        have a2 := minkB_nonpos_of_future hfut hyz
        rw [minkB_neg_left, ← hφsub] at a1 a2
        nlinarith
      · have hfut : IsFutureCausal w := ⟨hgt.le, hw.le⟩
        have a1 := minkB_nonpos_of_future hfut hzx
        have a2 := minkB_nonpos_of_future hfut hyz
        rw [← hφsub] at a1 a2
        nlinarith
  show 0 < φ x * φ z
  rcases lt_or_gt_of_ne (hne x hx) with h1 | h1
  · have h2 : φ y < 0 := by nlinarith
    have h3 : φ z < 0 := by
      by_contra h3; push Not at h3; nlinarith
    exact mul_pos_of_neg_of_neg h1 h3
  · have h2 : 0 < φ y := by nlinarith
    have h3 : 0 < φ z := by
      by_contra h3; push Not at h3; nlinarith
    exact mul_pos h1 h3

theorem isCausalPiece_univ : IsCausalPiece (univ : Set (Minkowski d)) :=
  fun _ _ _ _ _ _ _ => ⟨subset_univ _, fun _ => subset_univ _⟩

/-- The piece property is invariant under translation. -/
theorem IsCausalPiece.preimage_add {A : Set (Minkowski d)} (hA : IsCausalPiece A)
    (v : Minkowski d) : IsCausalPiece ((fun x => v + x) ⁻¹' A) := by
  intro s hs hsA x hx y hy
  have hle : ∀ a b : Minkowski d, (minkowski d).le ⊤ (v + a) (v + b) ↔ (minkowski d).le ⊤ a b :=
    fun a b => by simp only [minkowski_le_top_iff, Prod.snd_add, Prod.fst_add,
      add_sub_add_left_eq_sub]
  have hint : (fun x => v + x) ⁻¹' interior A = interior ((fun x => v + x) ⁻¹' A) :=
    (Homeomorph.addLeft v).preimage_interior A
  have hs' : IsPreconnected ((fun x => v + x) '' s) := hs.image _ (continuous_const.add
    continuous_id).continuousOn
  have hsA' : (fun x => v + x) '' s ⊆ interior A := by
    rintro _ ⟨a, ha, rfl⟩
    have := hsA ha
    rw [← hint] at this
    exact this
  obtain ⟨h1, h2⟩ := hA _ hs' hsA' (v + x) ⟨x, hx, rfl⟩ (v + y) ⟨y, hy, rfl⟩
  refine ⟨fun z hz => h1 ((mem_segment_translate ℝ v).2 hz), fun hxy z hz => ?_⟩
  obtain ⟨hxz, hzy⟩ := Causality.mem_diamond.1 hz
  exact h2 ((hle x y).2 hxy) (Causality.mem_diamond.2 ⟨(hle x z).2 hxz, (hle z y).2 hzy⟩)

/-- Transport along the conjugation by a translation. -/
theorem isCausalPiece_of_isomConj {g : isom d} (v : Minkowski d)
    (h : IsCausalPiece (achronalDomain (isomConj v g))) : IsCausalPiece (achronalDomain g) := by
  rw [achronalDomain_eq_preimage_isomConj v g]
  exact h.preimage_add v

/-- **A set whose interior is `{xy < 0}` in a null frame is a piece**: on a connected subset of
`{xy < 0}` both null coordinates keep their sign along segments and diamonds. -/
theorem isCausalPiece_of_interior_eq_nullXY {A : Set (Minkowski d)} {u u' : Minkowski d}
    (hu : minkQ u = 0) (hu' : minkQ u' = 0) (hB : minkB u u' ≠ 0)
    (hint : interior A = {z | nullXY u u' z < 0}) : IsCausalPiece A := by
  have hu0 : u ≠ 0 := fun h => hB (by simp [h, minkB])
  have hu'0 : u' ≠ 0 := fun h => hB (by simp [h, minkB])
  intro s hs hsA x hx y hy
  rw [hint] at hsA
  have hxy0 : ∀ z ∈ s, minkB z u ≠ 0 ∧ minkB z u' ≠ 0 := fun z hz => by
    have := hsA hz
    simp only [mem_setOf_eq, nullXY] at this
    constructor <;> intro h0 <;> simp [h0] at this
  have key : ∀ z, (z ∈ segment ℝ x y ∨ ((minkowski d).le ⊤ x z ∧ (minkowski d).le ⊤ z y)) →
      z ∈ A := by
    intro z hz
    have hP := pos_mul_of_null (c := 0) hu0 hu hs (fun a ha => by
      rw [sub_zero, minkB_comm]; exact (hxy0 a ha).1) hx hy hz
    have hQ := pos_mul_of_null (c := 0) hu'0 hu' hs (fun a ha => by
      rw [sub_zero, minkB_comm]; exact (hxy0 a ha).2) hx hy hz
    simp only [sub_zero] at hP hQ
    rw [minkB_comm u x, minkB_comm u z] at hP
    rw [minkB_comm u' x, minkB_comm u' z] at hQ
    have hxneg : nullXY u u' x < 0 := hsA hx
    have hprod : 0 < nullXY u u' x * nullXY u u' z := by
      have e : nullXY u u' x * nullXY u u' z =
          4 * ((minkB x u * minkB z u) * (minkB x u' * minkB z u')) / minkB u u' ^ 2 := by
        unfold nullXY; field_simp; ring
      rw [e]
      exact div_pos (by positivity) (pow_pos (abs_pos.2 hB) 2 |>.trans_eq (sq_abs _))
    have hz' : nullXY u u' z < 0 := by
      by_contra h3; push Not at h3; nlinarith
    exact interior_subset (show z ∈ interior A by rw [hint]; exact hz')
  exact ⟨fun z hz => key z (Or.inl hz), fun _ z hz => key z (Or.inr (Causality.mem_diamond.1 hz))⟩

/-- **Tangent parabolic** ([6.U]): `τ ∈ J^⊥`, not linear, for some decomposition. -/
def IsTangentParabolic (g : isom d) : Prop :=
  ∃ R U, IsParabolicPair g R U ∧ IsTangentCase U (g : Minkowski d ≃ᵃ[ℝ] Minkowski d)

theorem isCausalPiece_achronalDomain_lox {g : isom d} (h : IsLoxodromic (linOf g)) :
    IsCausalPiece (achronalDomain g) := by
  obtain ⟨v, hv⟩ := IsLoxodromic.exists_transConj_fixed g.2 h
  refine isCausalPiece_of_isomConj v ?_
  obtain ⟨u, u', hu, hu', hB, hint, -⟩ :=
    achronalDomain_isLoxodromic (g := isomConj v g) (by rw [linOf_isomConj]; exact h) hv
  exact isCausalPiece_of_interior_eq_nullXY hu hu' hB hint

theorem isCausalPiece_achronalDomain_spacelikeElliptic {g : isom d}
    (h : IsSpacelikeElliptic g) : IsCausalPiece (achronalDomain g) := by
  obtain ⟨hE, x, hx1, hx2⟩ := h
  have htr : trOf (isomConj (-x) g) = g • x - x := by
    rw [trOf_isomConj, map_neg, pOf_apply, smul_eq_lin_add]; abel
  refine isCausalPiece_of_isomConj (-x) ?_
  rw [achronalDomain_elliptic_spacelike (g := isomConj (-x) g) (by rw [linOf_isomConj]; exact hE)
    (by rw [linOf_isomConj, htr]; exact hx1) (by rw [htr]; exact hx2)]
  exact isCausalPiece_univ

theorem isCausalPiece_achronalDomain_tangent {g : isom d} (h : IsTangentParabolic g) :
    IsCausalPiece (achronalDomain g) := by
  obtain ⟨R, U, ⟨hR, hU, hRe, hn, hU1, hg, hc⟩, hT⟩ := h
  have hrange := parabolic_range_le_minkOrth_nullPart hR hU hRe hn hU1 hc
  obtain ⟨vₙ, v₁, -, h1, -, -, -, -, hq1, -⟩ := unipotent_frame hU.1 hn (pOf_ne_zero hU1)
  obtain ⟨v, hv, -⟩ := parabolic_exists_transConj_normal hR hU hRe hn hU1 hc hg
    (v₁ := v₁) ⟨vₙ, h1⟩ hq1.ne'
  refine isCausalPiece_of_isomConj v ?_
  have hT' : IsTangentCase U (transConj v (g : Minkowski d ≃ᵃ[ℝ] Minkowski d)) := by
    refine ⟨?_, fun h' => hT.2 ((isLinearCase_transConj_iff v _).1 h')⟩
    have hr : LinearMap.range (pOf (linOf g)) ≤ minkOrth (nullPart U) := by
      rw [hg]; exact hrange
    rw [transPart_transConj_mem_iff hr v]; exact hT.1
  rw [achronalDomain_parabolic_tangent hR hU hRe hn hU1 hc
    (g := isomConj v g) (by rw [linOf_isomConj]; exact hg) hv hT']
  exact isCausalPiece_univ

/-- **The trichotomy of `SO₀(1, d)`** ([6.N], l.1868–1901), as a named statement: every element
is elliptic, loxodromic or parabolic. It is Flat/Isometries' `lorentz_trichotomy`. -/
def LorentzTrichotomy (d : ℕ) : Prop :=
  ∀ A : Minkowski d ≃ₗ[ℝ] Minkowski d, A ∈ lorentz d → IsElliptic A ∨ IsLoxodromic A ∨ IsParabolic A

/-- The trichotomy holds: Flat/Isometries' `lorentz_trichotomy` (proved there, WP-30d fixer pass). -/
theorem lorentzTrichotomy : LorentzTrichotomy d := fun _ hA => lorentz_trichotomy hA

/-- **The classes left to the last branch of `Ug`**: loxodromic, spacelike elliptic, tangent or
transverse parabolic — given the trichotomy of `SO₀(1, d)`. -/
theorem classes_of_not (htri : LorentzTrichotomy d) {g : isom d}
    (hN : ¬IsNonspacelikeElliptic g) (hL : ¬IsLinearParabolic g) :
    IsLoxodromic (linOf g) ∨ IsSpacelikeElliptic g ∨ IsTangentParabolic g ∨
      IsTransverseParabolic g := by
  rcases htri (linOf g) (linOf_mem g) with hE | hX | hP
  · obtain ⟨v, hv⟩ := IsElliptic.exists_transConj_fixed g.2 hE
    have htr : g • (-v) - (-v) = trOf (isomConj v g) := by
      rw [trOf_isomConj, pOf_apply, smul_eq_lin_add, map_neg]; abel
    have hfix : linOf g (g • (-v) - (-v)) = g • (-v) - (-v) := by rw [htr]; exact hv
    rcases le_or_gt (minkQ (g • (-v) - (-v))) 0 with hq | hq
    · exact absurd ⟨hE, -v, hfix, hq⟩ hN
    · exact Or.inr (Or.inl ⟨hE, -v, hfix, hq⟩)
  · exact Or.inl hX
  · obtain ⟨R, U, hR, hU, hRe, hn, hU1, hg, hc⟩ := hP
    have hp : IsParabolicPair g R U := ⟨hR, hU, hRe, hn, hU1, hg, hc⟩
    rcases linear_or_tangent_or_transverse U (g : Minkowski d ≃ᵃ[ℝ] Minkowski d) with h | h | h
    · obtain ⟨c, hc'⟩ := (exists_fixed_iff _).2 h
      exact absurd ⟨⟨R, U, hR, hU, hRe, hn, hU1, hg, hc⟩, c, hc'⟩ hL
    · exact Or.inr (Or.inr (Or.inl ⟨R, U, hp, h⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨R, U, hp, h⟩))

/-- **The remaining classes**: for `g` neither nonspacelike elliptic nor linear parabolic,
`U(g) = Ω_g` has the piece property (resting only on the trichotomy, `classes_of_not`). -/
theorem isCausalPiece_achronalDomain (htri : LorentzTrichotomy d) {g : isom d}
    (hN : ¬IsNonspacelikeElliptic g) (hL : ¬IsLinearParabolic g) :
    IsCausalPiece (achronalDomain g) := by
  rcases classes_of_not htri hN hL with h | h | h | h
  · exact isCausalPiece_achronalDomain_lox h
  · exact isCausalPiece_achronalDomain_spacelikeElliptic h
  · exact isCausalPiece_achronalDomain_tangent h
  · rw [achronalDomain_eq_empty_of_isTransverseParabolic h]; exact isCausalPiece_empty

/-- **`U(g)` has the piece property** for every isometry `g`. -/
theorem isCausalPiece_Ug (htri : LorentzTrichotomy d) (g : isom d) : IsCausalPiece (Ug g) := by
  unfold Ug
  split_ifs with h1 h2
  · exact isCausalPiece_empty
  · exact isCausalPiece_compl_nullHyperplanes g
  · exact isCausalPiece_achronalDomain htri h1 h2

/-- **`U(Γ)` has the piece property**: an intersection of pieces is a piece. -/
theorem isCausalPiece_UGamma (htri : LorentzTrichotomy d) (Γ : Subgroup (isom d)) :
    IsCausalPiece (UGamma Γ) := by
  intro s hs hsU x hx y hy
  have hγ : ∀ γ ∈ Γ, γ ≠ 1 → segment ℝ x y ⊆ Ug γ ∧
      ((minkowski d).le ⊤ x y → (minkowski d).diamond ⊤ x y ⊆ Ug γ) := fun γ hγ h1 =>
    isCausalPiece_Ug htri γ s hs (hsU.trans (interior_mono fun z hz => hz γ hγ h1)) x hx y hy
  exact ⟨fun z hz γ hγ' h1 => (hγ γ hγ' h1).1 hz,
    fun hxy z hz γ hγ' h1 => (hγ γ hγ' h1).2 hxy hz⟩

/-- **The components of `int A` are convex and causally convex** when `A` has the piece
property: a small ball around each endpoint stays in the component, so the segment (and the
diamond, after pushing the endpoints a little into the past and the future) has a neighbourhood
inside `A`. This is the step Barbot's proof of Prop 8.10 leaves implicit (l.2430–2431,
l.2444–2451; obligation W8). -/
theorem convex_causallyConvex_connectedComponentIn {A : Set (Minkowski d)} (hA : IsCausalPiece A)
    (x₀ : Minkowski d) :
    Convex ℝ (connectedComponentIn (interior A) x₀) ∧
      (minkowski d).CausallyConvexIn (connectedComponentIn (interior A) x₀) ⊤ := by
  set C := connectedComponentIn (interior A) x₀ with hCdef
  have hCo : IsOpen C := isOpen_interior.connectedComponentIn
  have hCsub : C ⊆ interior A := connectedComponentIn_subset _ _
  have hCpre : IsPreconnected C := isPreconnected_connectedComponentIn
  have hCeq : ∀ x ∈ C, connectedComponentIn (interior A) x = C := fun x hx =>
    (connectedComponentIn_eq hx).symm
  have hball : ∀ x ∈ C, ∀ y ∈ C, ∃ ε > 0, Metric.ball x ε ⊆ C ∧ Metric.ball y ε ⊆ C := by
    intro x hx y hy
    obtain ⟨ε₁, hε₁, h₁⟩ := Metric.isOpen_iff.1 hCo x hx
    obtain ⟨ε₂, hε₂, h₂⟩ := Metric.isOpen_iff.1 hCo y hy
    exact ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (Metric.ball_subset_ball (min_le_left _ _)).trans h₁,
      (Metric.ball_subset_ball (min_le_right _ _)).trans h₂⟩
  have hshift : ∀ x u : Minkowski d, ∀ ε, ‖u‖ < ε → x + u ∈ Metric.ball x ε := fun x u ε hu => by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]; exact hu
  -- the segment of two points of `C` lies in `int A`
  have hseg : ∀ x ∈ C, ∀ y ∈ C, segment ℝ x y ⊆ interior A := by
    intro x hx y hy z hz
    obtain ⟨ε, hε, hbx, hby⟩ := hball x hx y hy
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
    refine mem_interior_iff_mem_nhds.2 (Metric.mem_nhds_iff.2 ⟨ε, hε, fun w hw => ?_⟩)
    set u := w - (a • x + b • y)
    have hu : ‖u‖ < ε := by rw [← dist_eq_norm]; exact hw
    have hxu := hbx (hshift x u ε hu)
    have hyu := hby (hshift y u ε hu)
    refine (hA C hCpre hCsub _ hxu _ hyu).1 ⟨a, b, ha, hb, hab, ?_⟩
    have : w = (a • x + b • y) + u := by simp [u]
    rw [this, smul_add, smul_add, add_add_add_comm, ← add_smul, hab, one_smul]
  have hsegC : ∀ x ∈ C, ∀ y ∈ C, segment ℝ x y ⊆ C := fun x hx y hy => by
    rw [← hCeq x hx]
    exact (convex_segment x y).isPreconnected.subset_connectedComponentIn (left_mem_segment ℝ x y)
      (hseg x hx y hy)
  refine ⟨fun x hx y hy a b ha hb hab => hsegC x hx y hy ⟨a, b, ha, hb, hab, rfl⟩,
    fun _ _ => trivial, fun p hp q hq => ?_⟩
  -- the diamond of two points of `C` lies in `int A`
  obtain ⟨ε, hε, hbp, hbq⟩ := hball p hp q hq
  set e₀ : Minkowski d := ((1 : ℝ), 0)
  have he₀ : ‖(ε / 2) • e₀‖ < ε := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)]
    have : ‖e₀‖ = 1 := by simp [e₀, Prod.norm_def]
    rw [this]; linarith
  have hp' : p + -((ε / 2) • e₀) ∈ C := hbp (hshift p _ ε (by rwa [norm_neg]))
  have hq' : q + (ε / 2) • e₀ ∈ C := hbq (hshift q _ ε he₀)
  have hdiam : (minkowski d).diamond ⊤ p q ⊆ interior A := by
    intro z hz
    obtain ⟨hpz, hzq⟩ := Causality.mem_diamond.1 hz
    have hpz' := minkowski_le_top_iff.1 hpz
    have hzq' := minkowski_le_top_iff.1 hzq
    have hpq' : (minkowski d).le ⊤ (p + -((ε / 2) • e₀)) (q + (ε / 2) • e₀) := by
      rw [minkowski_le_top_iff]
      have := minkowski_le_top_iff.1 ((minkowski d).le_trans hpz hzq)
      simp only [e₀, Prod.snd_add, Prod.fst_add, Prod.smul_snd, Prod.smul_fst, Prod.snd_neg,
        Prod.fst_neg, smul_zero, neg_zero, add_zero, smul_eq_mul, mul_one]
      linarith
    have hD := (hA C hCpre hCsub _ hp' _ hq').2 hpq'
    refine mem_interior_iff_mem_nhds.2 (Metric.mem_nhds_iff.2 ⟨ε / 4, by linarith, fun w hw => ?_⟩)
    have hw' : ‖w - z‖ < ε / 4 := by rw [← dist_eq_norm]; exact hw
    have h1 : |w.1 - z.1| < ε / 4 := by
      have := (norm_fst_le (w - z)).trans_lt hw'
      rwa [Prod.fst_sub, Real.norm_eq_abs] at this
    have h2 : ‖w.2 - z.2‖ < ε / 4 := by
      have := (norm_snd_le (w - z)).trans_lt hw'
      rwa [Prod.snd_sub] at this
    refine hD (Causality.mem_diamond.2 ⟨?_, ?_⟩)
    · rw [minkowski_le_top_iff]
      simp only [e₀, Prod.snd_add, Prod.fst_add, Prod.smul_snd, Prod.smul_fst, Prod.snd_neg,
        Prod.fst_neg, smul_zero, neg_zero, add_zero, smul_eq_mul, mul_one]
      have := norm_sub_le_norm_sub_add_norm_sub w.2 z.2 p.2
      linarith [abs_lt.1 h1]
    · rw [minkowski_le_top_iff]
      simp only [e₀, Prod.snd_add, Prod.fst_add, Prod.smul_snd, Prod.smul_fst, smul_zero,
        add_zero, smul_eq_mul, mul_one]
      have := norm_sub_le_norm_sub_add_norm_sub q.2 z.2 w.2
      rw [norm_sub_rev z.2 w.2] at this
      linarith [abs_lt.1 h1]
  intro z hz
  have hpq : (minkowski d).le ⊤ p q :=
    (minkowski d).le_trans (Causality.mem_diamond.1 hz).1 (Causality.mem_diamond.1 hz).2
  have hstar : StarConvex ℝ p ((minkowski d).diamond ⊤ p q) := by
    intro w hw a b ha hb hab
    obtain ⟨hpw, hwq⟩ := Causality.mem_diamond.1 hw
    obtain ⟨h1, h2⟩ := le_top_of_mem_segment hpw ⟨a, b, ha, hb, hab, rfl⟩
    exact Causality.mem_diamond.2 ⟨h1, (minkowski d).le_trans h2 hwq⟩
  have hpD : p ∈ (minkowski d).diamond ⊤ p q :=
    Causality.mem_diamond.2 ⟨(minkowski d).le_refl trivial, hpq⟩
  rw [← hCeq p hp]
  exact (StarConvex.isPathConnected hstar hpD).isConnected.isPreconnected.subset_connectedComponentIn
    hpD hdiam hz

/-- **Prop 8.10** (`bprop:ghyp`, l.2420–2426): `Ω(S̃)` is open, convex, globally hyperbolic
(ETT's definition: causal with compact diamonds, through `le_iff_of_convex`-style causal
convexity and `minkowski_globallyHyperbolic`; Beem–Ehrlich is not used), `Γ`-invariant, and `Γ`
acts on it freely and achronally. -/
theorem bprop_ghyp_of_trichotomy (htri : LorentzTrichotomy d) (h : CCAction Γ S) :
    IsOpen (omegaS Γ S) ∧ Convex ℝ (omegaS Γ S) ∧
      (minkowski d).GloballyHyperbolicOn (omegaSOpens Γ S) ∧
      (∀ γ ∈ Γ, γ • omegaS Γ S = omegaS Γ S) ∧
      ∀ γ ∈ Γ, γ ≠ 1 → ∀ x ∈ omegaS Γ S, γ • x ≠ x ∧ ¬(minkowski d).le ⊤ x (γ • x) := by
  obtain ⟨x₀, hx₀⟩ := h.nonempty
  obtain ⟨hcv, hcc⟩ := convex_causallyConvex_connectedComponentIn (isCausalPiece_UGamma htri Γ) x₀
  rw [← omegaGamma, ← omegaS_eq h hx₀] at hcv hcc
  refine ⟨isOpen_omegaS Γ S, hcv, globallyHyperbolicOn_of_causallyConvexIn hcc,
    fun γ hγ => smul_omegaS h hγ, fun γ hγ h1 x hx => ?_⟩
  have hU := Ug_subset_achronalDomain γ
    (interior_subset (omegaS_subset_omegaGamma Γ S hx) γ hγ h1) 1 one_ne_zero
  rw [zpow_one] at hU
  refine ⟨fun e => by rw [e, sub_self, minkQ_zero] at hU; exact lt_irrefl _ hU, fun hle => ?_⟩
  exact absurd (le_top_iff_minkQ.1 hle).2 (not_le.2 hU)

/-- **Prop 8.10** (`bprop:ghyp`), unconditionally: `bprop_ghyp_of_trichotomy` at
`lorentzTrichotomy` (Isometries' `lorentz_trichotomy`). -/
theorem bprop_ghyp (h : CCAction Γ S) :
    IsOpen (omegaS Γ S) ∧ Convex ℝ (omegaS Γ S) ∧
      (minkowski d).GloballyHyperbolicOn (omegaSOpens Γ S) ∧
      (∀ γ ∈ Γ, γ • omegaS Γ S = omegaS Γ S) ∧
      ∀ γ ∈ Γ, γ ≠ 1 → ∀ x ∈ omegaS Γ S, γ • x ≠ x ∧ ¬(minkowski d).le ⊤ x (γ • x) :=
  bprop_ghyp_of_trichotomy lorentzTrichotomy h

/-! ### Rem 8.8 (`remplacefini`) -/

theorem achronalDomain_subset_zpow (g : isom d) {n : ℤ} (hn : n ≠ 0) :
    achronalDomain g ⊆ achronalDomain (g ^ n) := fun x hx q hq => by
  rw [← zpow_mul]; exact hx _ (mul_ne_zero hn hq)

/-- `U(Γ)` is antitone in `Γ`. -/
theorem UGamma_antitone {Γ' : Subgroup (isom d)} (hle : Γ' ≤ Γ) : UGamma Γ ⊆ UGamma Γ' :=
  fun _ hx γ hγ h1 => hx γ (hle hγ) h1

/-! #### Powers: the classes, `J^⊥` and `Ω_g` are unchanged by a nonzero power -/

theorem linOf_zpow (g : isom d) (n : ℤ) : linOf (g ^ n) = linOf g ^ n := by
  show AffineEquiv.linearHom ((g ^ n : isom d) : Minkowski d ≃ᵃ[ℝ] Minkowski d) = _
  rw [Subgroup.coe_zpow, map_zpow]
  rfl

private theorem linEquiv_zpow_apply_eq_self {A : Minkowski d ≃ₗ[ℝ] Minkowski d}
    {u : Minkowski d} (h : A u = u) (n : ℤ) : (A ^ n) u = u := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · rw [zpow_natCast]; exact pow_apply_eq_self h m
  · rw [zpow_neg, zpow_natCast]
    conv_lhs => rw [← pow_apply_eq_self h m]
    exact linEquiv_inv_apply_self _ _

private theorem linEquiv_zpow_apply_eigen {A : Minkowski d ≃ₗ[ℝ] Minkowski d} {u : Minkowski d}
    {c : ℝ} (hc : c ≠ 0) (h : A u = c • u) (n : ℤ) : (A ^ n) u = c ^ n • u := by
  have hnat : ∀ m : ℕ, (A ^ m) u = c ^ m • u := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ', LinearEquiv.mul_apply, ih, map_smul, h, smul_smul, pow_succ]
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · rw [zpow_natCast, zpow_natCast]; exact hnat m
  · rw [zpow_neg, zpow_natCast, zpow_neg, zpow_natCast]
    have hcm : c ^ m ≠ 0 := pow_ne_zero _ hc
    calc ((A ^ m)⁻¹) u = ((A ^ m)⁻¹) ((c ^ m)⁻¹ • (A ^ m) u) := by
          rw [hnat m, smul_smul, inv_mul_cancel₀ hcm, one_smul]
      _ = (c ^ m)⁻¹ • u := by rw [map_smul, linEquiv_inv_apply_self]

private theorem linEquiv_zpow_apply_jordan {A : Minkowski d ≃ₗ[ℝ] Minkowski d}
    {v₁ v₀ : Minkowski d} (h1 : A v₁ = v₁ + v₀) (h0 : A v₀ = v₀) (n : ℤ) :
    (A ^ n) v₁ = v₁ + (n : ℝ) • v₀ := by
  have hinv : A⁻¹ v₁ = v₁ - v₀ := by
    have e : A (v₁ - v₀) = v₁ := by rw [map_sub, h1, h0, add_sub_cancel_right]
    calc A⁻¹ v₁ = A⁻¹ (A (v₁ - v₀)) := by rw [e]
      _ = v₁ - v₀ := linEquiv_inv_apply_self _ _
  refine Int.induction_on n (by simp) (fun i ih => ?_) (fun i ih => ?_)
  · rw [zpow_add_one, LinearEquiv.mul_apply, h1, map_add, ih,
      linEquiv_zpow_apply_eq_self h0, Int.cast_add, Int.cast_one, add_smul, one_smul]
    abel
  · rw [zpow_sub_one, LinearEquiv.mul_apply, hinv, map_sub, ih,
      linEquiv_zpow_apply_eq_self h0, Int.cast_sub, Int.cast_one, sub_smul, one_smul]
    abel

/-- A Jordan block `A v₁ = v₁ + v₀`, `A v₀ = v₀`, `v₀ ≠ 0` puts `v₀` in `Im p ∩ ker p`. -/
private theorem range_inf_ker_ne_bot_of_jordan {A : Minkowski d ≃ₗ[ℝ] Minkowski d}
    {v₁ v₀ : Minkowski d} (hv0 : v₀ ≠ 0) (h1 : A v₁ = v₁ + v₀) (h0 : A v₀ = v₀) :
    LinearMap.range (pOf A) ⊓ LinearMap.ker (pOf A) ≠ ⊥ := by
  intro hbot
  have hmem : v₀ ∈ LinearMap.range (pOf A) ⊓ LinearMap.ker (pOf A) :=
    ⟨⟨v₁, by rw [pOf_apply, h1, add_sub_cancel_left]⟩,
      by show pOf A v₀ = 0; rw [pOf_apply, h0, sub_self]⟩
  rw [hbot, Submodule.mem_bot] at hmem
  exact hv0 hmem

theorem IsElliptic.zpow_linOf {g : isom d} (h : IsElliptic (linOf g)) (n : ℤ) :
    IsElliptic (linOf (g ^ n)) := by
  obtain ⟨u, hu, hAu⟩ := h.exists_fixed_timelike (linOf_mem g)
  rw [linOf_zpow]
  exact isElliptic_of_fixed_timelike (fun v => by rw [← linOf_zpow]; exact (linOf_mem _).1 v)
    hu.2 (linEquiv_zpow_apply_eq_self hAu n)

theorem IsLoxodromic.zpow_linOf {g : isom d} (h : IsLoxodromic (linOf g)) {n : ℤ} (hn : n ≠ 0) :
    IsLoxodromic (linOf (g ^ n)) := by
  obtain ⟨u, hu0, hq, l, hl, hl1, hAu⟩ := h.exists_eigen
  refine isLoxodromic_of_null_eigen (linOf_mem (g ^ n)) hu0 hq (zpow_pos hl n) (fun h1 => hn ?_)
    (by rw [linOf_zpow]; exact linEquiv_zpow_apply_eigen hl.ne' hAu n)
  exact zpow_right_injective₀ hl hl1 (by simpa using h1)

theorem IsParabolic.zpow_linOf {g : isom d} (h : IsParabolic (linOf g)) {n : ℤ} (hn : n ≠ 0) :
    IsParabolic (linOf (g ^ n)) := by
  obtain ⟨v₁, v₀, hv0, h1, h0⟩ := h.exists_jordan
  have hJ := range_inf_ker_ne_bot_of_jordan (A := linOf (g ^ n)) (v₁ := v₁)
    (v₀ := (n : ℝ) • v₀) (smul_ne_zero (by exact_mod_cast hn) hv0)
    (by rw [linOf_zpow]; exact linEquiv_zpow_apply_jordan h1 h0 n)
    (by rw [linOf_zpow, map_smul, linEquiv_zpow_apply_eq_self h0])
  rcases lorentz_trichotomy (linOf_mem (g ^ n)) with hE | hX | hP
  · exact absurd hE.range_inf_ker hJ
  · exact absurd hX.range_inf_ker hJ
  · exact hP

/-- `L(gⁿ)` is elliptic iff `L(g)` is (`n ≠ 0`), by the trichotomy and its exclusivity. -/
theorem isElliptic_linOf_zpow_iff (g : isom d) {n : ℤ} (hn : n ≠ 0) :
    IsElliptic (linOf (g ^ n)) ↔ IsElliptic (linOf g) := by
  refine ⟨fun h => ?_, fun h => h.zpow_linOf n⟩
  rcases lorentz_trichotomy (linOf_mem g) with hE | hX | hP
  · exact hE
  · exact absurd h (hX.zpow_linOf hn).not_isElliptic
  · exact absurd h (hP.zpow_linOf hn).not_isElliptic

/-- `L(gⁿ)` is parabolic iff `L(g)` is (`n ≠ 0`). -/
theorem isParabolic_linOf_zpow_iff (g : isom d) {n : ℤ} (hn : n ≠ 0) :
    IsParabolic (linOf (g ^ n)) ↔ IsParabolic (linOf g) := by
  refine ⟨fun h => ?_, fun h => h.zpow_linOf hn⟩
  rcases lorentz_trichotomy (linOf_mem g) with hE | hX | hP
  · exact absurd (hE.zpow_linOf n) h.not_isElliptic
  · exact absurd (hX.zpow_linOf hn) h.not_isLoxodromic
  · exact hP

/-- Along a translation `τ = g x − x` fixed by `L(g)`, `gᵏ x = x + k τ` for every `k ∈ ℤ`. -/
theorem zpow_smul_eq_add {g : isom d} {x : Minkowski d} (hτ : linOf g (g • x - x) = g • x - x)
    (k : ℤ) : (g ^ k) • x = x + (k : ℝ) • (g • x - x) := by
  set τ := g • x - x with hτdef
  have hstep : ∀ s : ℝ, g • (x + s • τ) = x + (s + 1) • τ := fun s => by
    rw [isom_smul_add_smul, hτ, add_smul, one_smul, hτdef]; abel
  have hstep' : ∀ s : ℝ, g⁻¹ • (x + s • τ) = x + (s - 1) • τ := fun s => by
    rw [inv_smul_eq_iff, hstep, sub_add_cancel]
  refine Int.induction_on k (by simp) (fun i ih => ?_) (fun i ih => ?_)
  · rw [add_comm (i : ℤ) 1, zpow_add, zpow_one, mul_smul, ih, hstep, Int.cast_add, Int.cast_one,
      add_comm (1 : ℝ)]
  · rw [show -(i : ℤ) - 1 = -1 + -(i : ℤ) by ring, zpow_add, zpow_neg_one, mul_smul, ih, hstep']
    congr 2; push_cast; ring

theorem zpow_smul_eq_self_of_smul_eq {g : isom d} {c : Minkowski d} (h : g • c = c) (k : ℤ) :
    (g ^ k) • c = c := by
  have hτ : linOf g (g • c - c) = g • c - c := by rw [h, sub_self, map_zero]
  rw [zpow_smul_eq_add hτ, h, sub_self, smul_zero, add_zero]

/-- **If `gᵐ` fixes a point (`m > 0`), so does `g`**: the barycentre of the orbit. -/
theorem exists_smul_eq_self_of_pow {g : isom d} {c : Minkowski d} {m : ℕ} (hm : 0 < m)
    (h : (g ^ m) • c = c) : ∃ b : Minkowski d, g • b = b := by
  set w : Minkowski d := ∑ k ∈ Finset.range m, (g ^ k) • c with hwdef
  have hsum : ∑ k ∈ Finset.range m, linOf g ((g ^ k) • c) = w - (m : ℝ) • trOf g := by
    have : ∀ k, linOf g ((g ^ k) • c) = (g ^ (k + 1)) • c - trOf g :=
      fun k => by rw [pow_succ', mul_smul, smul_eq_lin_add (g := g)]; abel
    simp only [this, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [hwdef, Finset.sum_range_succ (fun k => (g ^ (k + 1)) • c),
      Finset.sum_range_succ' (fun k => (g ^ k) • c), h, pow_zero, one_smul,
      Nat.cast_smul_eq_nsmul ℝ]
  refine ⟨(m : ℝ)⁻¹ • w, ?_⟩
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [smul_eq_lin_add, map_smul, hwdef, map_sum, hsum, smul_sub, smul_smul, inv_mul_cancel₀ hm',
    one_smul]
  abel

/-- An elliptic `L(g)` admits a point whose displacement `g x − x` is fixed by `L(g)` (l.1873). -/
theorem exists_fixed_trans {g : isom d} (hE : IsElliptic (linOf g)) :
    ∃ x : Minkowski d, linOf g (g • x - x) = g • x - x := by
  obtain ⟨v, hv⟩ := IsElliptic.exists_transConj_fixed g.2 hE
  have htr : g • (-v) - (-v) = trOf (isomConj v g) := by
    rw [trOf_isomConj, pOf_apply, smul_eq_lin_add, map_neg]; abel
  exact ⟨-v, by rw [htr]; exact hv⟩

/-- **The `L(g)`-fixed displacement of an elliptic `g` is unique** (`Im p ∩ ker p = 0`). -/
theorem fixedTrans_eq {g : isom d} (hE : IsElliptic (linOf g)) {x y : Minkowski d}
    (hx : linOf g (g • x - x) = g • x - x) (hy : linOf g (g • y - y) = g • y - y) :
    g • x - x = g • y - y := by
  have e : (g • x - x) - (g • y - y) = pOf (linOf g) (x - y) := by
    rw [pOf_apply, ← smul_sub_smul]; abel
  have hk : pOf (linOf g) (pOf (linOf g) (x - y)) = 0 := by
    rw [← e, pOf_apply, map_sub, hx, hy, sub_self]
  have hmem : pOf (linOf g) (x - y) ∈
      LinearMap.range (pOf (linOf g)) ⊓ LinearMap.ker (pOf (linOf g)) := ⟨⟨x - y, rfl⟩, hk⟩
  rw [hE.range_inf_ker, Submodule.mem_bot] at hmem
  rw [← sub_eq_zero, e, hmem]

/-- **"Nonspacelike elliptic" is unchanged by a nonzero power**: `gⁿ x − x = n (g x − x)` along
a fixed displacement, and the fixed displacement is unique. -/
theorem isNonspacelikeElliptic_zpow_iff (g : isom d) {n : ℤ} (hn : n ≠ 0) :
    IsNonspacelikeElliptic (g ^ n) ↔ IsNonspacelikeElliptic g := by
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 (by exact_mod_cast hn : (n : ℝ) ≠ 0)).symm
  have key : ∀ x : Minkowski d, linOf g (g • x - x) = g • x - x →
      linOf (g ^ n) ((g ^ n) • x - x) = (g ^ n) • x - x ∧
        minkQ ((g ^ n) • x - x) = (n : ℝ) ^ 2 * minkQ (g • x - x) := fun x hx => by
    rw [zpow_smul_eq_add hx, add_sub_cancel_left, linOf_zpow, map_smul,
      linEquiv_zpow_apply_eq_self hx, minkQ_smul]
    exact ⟨rfl, rfl⟩
  constructor
  · rintro ⟨hE', y, hy, hqy⟩
    have hE := (isElliptic_linOf_zpow_iff g hn).1 hE'
    obtain ⟨x, hx⟩ := exists_fixed_trans hE
    refine ⟨hE, x, hx, ?_⟩
    obtain ⟨hx', hq⟩ := key x hx
    rw [fixedTrans_eq hE' hy hx', hq] at hqy
    by_contra hc
    linarith [mul_pos hn2 (not_le.1 hc)]
  · rintro ⟨hE, x, hx, hq⟩
    obtain ⟨hx', hq'⟩ := key x hx
    exact ⟨hE.zpow_linOf n, x, hx', by rw [hq']; nlinarith⟩

/-- **"Linear parabolic" is unchanged by a nonzero power** (a fixed point of `gⁿ` gives one of
`g`, the barycentre of its orbit). -/
theorem isLinearParabolic_zpow_iff (g : isom d) {n : ℤ} (hn : n ≠ 0) :
    IsLinearParabolic (g ^ n) ↔ IsLinearParabolic g := by
  constructor
  · rintro ⟨hP, c, hc⟩
    refine ⟨(isParabolic_linOf_zpow_iff g hn).1 hP, ?_⟩
    rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
    · rw [zpow_natCast] at hc
      exact exists_smul_eq_self_of_pow (by omega) hc
    · rw [zpow_neg, zpow_natCast, inv_smul_eq_iff] at hc
      exact exists_smul_eq_self_of_pow (by omega) hc.symm
  · rintro ⟨hP, c, hc⟩
    exact ⟨hP.zpow_linOf hn, c, zpow_smul_eq_self_of_smul_eq hc n⟩

/-- **A vector fixed by a non-elliptic Lorentz map is orthogonal to its fixed null vectors**:
otherwise a combination of the two would be a fixed timelike vector. -/
theorem minkB_eq_zero_of_fixed_of_not_isElliptic {A : Minkowski d ≃ₗ[ℝ] Minkowski d}
    (hA : A ∈ lorentz d) (hne : ¬IsElliptic A) {v₀ w : Minkowski d} (hq : minkQ v₀ = 0)
    (h0 : A v₀ = v₀) (hw : A w = w) : minkB w v₀ = 0 := by
  by_contra hb
  set s : ℝ := -(minkQ w + 1) / (2 * minkB w v₀) with hs
  have hz : minkQ (w + s • v₀) = -1 := by
    rw [minkQ_add, minkQ_smul, hq, minkB_smul_right, hs]
    field_simp
    ring
  exact hne (isElliptic_of_fixed_timelike hA.1 (by rw [hz]; norm_num)
    (by rw [map_add, map_smul, hw, h0]))

/-- The null line `J` of a parabolic decomposition is pointwise fixed by `L(g)`. -/
theorem IsParabolicPair.exists_fixed_null {g : isom d} {R U : Minkowski d ≃ₗ[ℝ] Minkowski d}
    (hp : IsParabolicPair g R U) :
    ∃ v ∈ nullPart U, v ≠ 0 ∧ minkQ v = 0 ∧ linOf g v = v := by
  obtain ⟨hR, hU, hRe, hn, hU1, hg, hc⟩ := hp
  obtain ⟨v₀, hv₀, hv₀0⟩ := exists_mem_nullPart_ne_zero hU.1 hn (pOf_ne_zero hU1)
  have hUv : U v₀ = v₀ := by
    have := pOf_eq_zero_of_mem_nullPart hU.1 hv₀
    rwa [pOf_apply, sub_eq_zero] at this
  refine ⟨v₀, hv₀, hv₀0, minkQ_eq_zero_of_mem_nullPart hv₀, ?_⟩
  rw [hg, LinearEquiv.mul_apply, hUv, parabolic_R_fix_nullPart hR hU hRe hc hv₀]

/-- **`J^⊥` does not depend on the decomposition**: for parabolic `L(g)` fixing the null
`v₀ ≠ 0`, `nullHyperplanes g` is the union of the null hyperplanes `c + v₀^⊥` through the fixed
points `c` (every `J` of a decomposition is the line of `v₀`). -/
theorem mem_nullHyperplanes_iff {g : isom d} (hP : IsParabolic (linOf g)) {v₀ : Minkowski d}
    (hv0 : v₀ ≠ 0) (hq : minkQ v₀ = 0) (hfix : linOf g v₀ = v₀) (x : Minkowski d) :
    x ∈ nullHyperplanes g ↔ ∃ c, g • c = c ∧ minkB (x - c) v₀ = 0 := by
  have hne := hP.not_isElliptic
  have hline : ∀ R U, IsParabolicPair g R U → v₀ ∈ nullPart U ∧ nullPart U = ℝ ∙ v₀ := by
    intro R U hp
    obtain ⟨v, hv, hv0', hqv, hfv⟩ := hp.exists_fixed_null
    have hB := minkB_eq_zero_of_fixed_of_not_isElliptic (linOf_mem g) hne hqv hfv hfix
    obtain ⟨a, ha⟩ := eq_smul_of_null_orth hqv hv0' hq (by rw [minkB_comm]; exact hB)
    have hmem : v₀ ∈ nullPart U := by rw [ha]; exact Submodule.smul_mem _ _ hv
    exact ⟨hmem, nullPart_eq_span_of_mem hmem hv0⟩
  constructor
  · rintro ⟨R, U, hp, c, hc, hxc⟩
    exact ⟨c, hc, mem_minkOrth'.1 hxc v₀ (hline R U hp).1⟩
  · rintro ⟨c, hc, hB⟩
    obtain ⟨R, U, hR, hU, hRe, hn, hU1, hg, hcomm⟩ := hP
    have hp : IsParabolicPair g R U := ⟨hR, hU, hRe, hn, hU1, hg, hcomm⟩
    refine ⟨R, U, hp, c, hc, mem_minkOrth'.2 fun y hy => ?_⟩
    rw [(hline R U hp).2] at hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
    rw [minkB_smul_right, hB, mul_zero]

/-- **`J^⊥(gⁿ) = J^⊥(g)`** for linear parabolic `g`: the fixed points of `gⁿ` differ from those of
`g` by `L(gⁿ)`-fixed vectors, orthogonal to `J` because `L(gⁿ)` is not elliptic. -/
theorem nullHyperplanes_zpow {g : isom d} (hL : IsLinearParabolic g) {n : ℤ} (hn : n ≠ 0) :
    nullHyperplanes (g ^ n) = nullHyperplanes g := by
  obtain ⟨hP, c₀, hc₀⟩ := hL
  obtain ⟨R, U, hR, hU, hRe, hnil, hU1, hg, hcomm⟩ := id hP
  obtain ⟨v₀, -, hv0, hq, hfix⟩ :=
    (show IsParabolicPair g R U from ⟨hR, hU, hRe, hnil, hU1, hg, hcomm⟩).exists_fixed_null
  have hPn := hP.zpow_linOf hn
  have hfixn : linOf (g ^ n) v₀ = v₀ := by
    rw [linOf_zpow]; exact linEquiv_zpow_apply_eq_self hfix n
  ext x
  rw [mem_nullHyperplanes_iff hPn hv0 hq hfixn, mem_nullHyperplanes_iff hP hv0 hq hfix]
  constructor
  · rintro ⟨c, hc, hB⟩
    refine ⟨c₀, hc₀, ?_⟩
    have hw : linOf (g ^ n) (c - c₀) = c - c₀ := by
      rw [← smul_sub_smul, hc, zpow_smul_eq_self_of_smul_eq hc₀]
    have h0 := minkB_eq_zero_of_fixed_of_not_isElliptic (linOf_mem _) hPn.not_isElliptic hq
      hfixn hw
    rw [show x - c₀ = (x - c) + (c - c₀) by abel, minkB_add_left, hB, h0, add_zero]
  · rintro ⟨c, hc, hB⟩
    exact ⟨c, zpow_smul_eq_self_of_smul_eq hc n, hB⟩

theorem achronalDomain_inv (g : isom d) : achronalDomain g⁻¹ = achronalDomain g := by
  ext x
  simp only [achronalDomain, mem_setOf_eq]
  constructor <;> intro h q hq
  · have := h (-q) (neg_ne_zero.2 hq)
    rwa [inv_zpow', neg_neg] at this
  · rw [inv_zpow']; exact h (-q) (neg_ne_zero.2 hq)

/-- **`Ω_{gⁿ} = Ω_g`** for `n ≠ 0`, with no case analysis: if `x` and `g^q x` are causally
related, `x ≤ g^r x` for `r = ±q`, hence `x ≤ (g^r)^m x = (g^m)^r x` by iteration. -/
theorem achronalDomain_zpow (g : isom d) {n : ℤ} (hn : n ≠ 0) :
    achronalDomain (g ^ n) = achronalDomain g := by
  suffices H : ∀ m : ℕ, 0 < m → achronalDomain (g ^ m) ⊆ achronalDomain g by
    refine Subset.antisymm ?_ (achronalDomain_subset_zpow g hn)
    rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
    · rw [zpow_natCast]; exact H m (by omega)
    · rw [zpow_neg, achronalDomain_inv, zpow_natCast]; exact H m (by omega)
  intro m hm x hx q hq
  by_contra hneg
  obtain ⟨r, hr, hle⟩ : ∃ r : ℤ, r ≠ 0 ∧ (minkowski d).le ⊤ x ((g ^ r) • x) := by
    rcases le_top_or_of_minkQ_nonpos (not_lt.1 hneg) with h | h
    · exact ⟨q, hq, h⟩
    · refine ⟨-q, neg_ne_zero.2 hq, ?_⟩
      have := (isom_le_top_iff (g ^ q)⁻¹).2 h
      rwa [inv_smul_smul, ← zpow_neg] at this
  have hfwd : ∀ j : ℕ, (minkowski d).le ⊤ x (((g ^ r) ^ j) • x) := by
    intro j
    induction j with
    | zero => simpa using (minkowski d).le_refl (show x ∈ (⊤ : Opens (Minkowski d)) from trivial)
    | succ j ih =>
      refine (minkowski d).le_trans ih ?_
      have := (isom_le_top_iff ((g ^ r) ^ j)).2 hle
      rwa [← mul_smul, ← pow_succ] at this
  have h1 := hx r hr
  have h2 := (le_top_iff_minkQ.1 (hfwd m)).2
  rw [show ((g ^ r) ^ m : isom d) = (g ^ m) ^ r by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]] at h2
  linarith

/-- **Rem 8.8, first sentence** (l.2404): `U(gⁿ) = U(g)` for `n ≠ 0`. The class of `g`
(nonspacelike elliptic, linear parabolic, or neither) is that of `gⁿ`
(`isNonspacelikeElliptic_zpow_iff`, `isLinearParabolic_zpow_iff`), `J^⊥(gⁿ) = J^⊥(g)`
(`nullHyperplanes_zpow`) and `Ω_{gⁿ} = Ω_g` (`achronalDomain_zpow`). -/
theorem Ug_zpow (g : isom d) {n : ℤ} (hn : n ≠ 0) : Ug (g ^ n) = Ug g := by
  unfold Ug
  by_cases hN : IsNonspacelikeElliptic g
  · rw [if_pos ((isNonspacelikeElliptic_zpow_iff g hn).2 hN), if_pos hN]
  · rw [if_neg (mt (isNonspacelikeElliptic_zpow_iff g hn).1 hN), if_neg hN]
    by_cases hL : IsLinearParabolic g
    · rw [if_pos ((isLinearParabolic_zpow_iff g hn).2 hL), if_pos hL, nullHyperplanes_zpow hL hn]
    · rw [if_neg (mt (isLinearParabolic_zpow_iff g hn).1 hL), if_neg hL, achronalDomain_zpow g hn]

/-- **Rem 8.8, second sentence** (l.2405–2407): for a finite-index `Γ' ≤ Γ` and `Γ` torsion-free,
`U(Γ') = U(Γ)`. Torsion-freeness is needed with the reading `γ ≠ 1` (W4): for `Γ = {1, γ}`,
`γ² = 1`, and `Γ' = 1`, `U(Γ') = 𝐌ⁿ` while `U(Γ) = U(γ) = ∅`. -/
theorem UGamma_eq_of_index {Γ' : Subgroup (isom d)} (hle : Γ' ≤ Γ)
    (hidx : (Γ'.subgroupOf Γ).index ≠ 0) (htf : ∀ γ ∈ Γ, γ ≠ 1 → ∀ n : ℕ, 0 < n → γ ^ n ≠ 1) :
    UGamma Γ' = UGamma Γ := by
  refine Subset.antisymm (fun x hx γ hγ h1 => ?_) (UGamma_antitone hle)
  obtain ⟨n, hn, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hidx ⟨γ, hγ⟩
  have hmem' : γ ^ n ∈ Γ' := by
    rw [Subgroup.mem_subgroupOf] at hmem; simpa using hmem
  have := hx _ hmem' (htf γ hγ h1 n hn)
  rwa [← zpow_natCast, Ug_zpow γ (by exact_mod_cast hn.ne')] at this

/-! ## Curves through a flat covering, and the lift of Cauchy surfaces (`bprop:splitting`) -/

/-- A strictly monotone reparametrisation of an interval onto an interval is continuous. -/
theorem continuousOn_of_strictMonoOn {I : Set ℝ} {φ : ℝ → ℝ} (hφ : StrictMonoOn φ I)
    (hJ : (φ '' I).OrdConnected) : ContinuousOn φ I := by
  intro a ha
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · by_cases hex : ∃ c ∈ I, c < a
    · obtain ⟨c, hc, hca⟩ := hex
      have hφca := hφ hc ha hca
      obtain ⟨v, hv1, hv2⟩ := exists_between (max_lt hb hφca)
      obtain ⟨c', hc', rfl⟩ : v ∈ φ '' I :=
        hJ.out ⟨c, hc, rfl⟩ ⟨a, ha, rfl⟩ ⟨(le_max_right _ _).trans hv1.le, hv2.le⟩
      have hc'a : c' < a := (hφ.lt_iff_lt hc' ha).1 hv2
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds hc'a)] with x hx hx'
      exact ((le_max_left _ _).trans_lt hv1).trans (hφ hc' hx hx')
    · push Not at hex
      filter_upwards [self_mem_nhdsWithin] with x hx
      rcases (hex x hx).eq_or_lt with h | h
      · rw [← h]; exact hb
      · exact hb.trans (hφ ha hx h)
  · by_cases hex : ∃ c ∈ I, a < c
    · obtain ⟨c, hc, hac⟩ := hex
      have hφac := hφ ha hc hac
      obtain ⟨v, hv1, hv2⟩ := exists_between (lt_min hb hφac)
      obtain ⟨c', hc', rfl⟩ : v ∈ φ '' I :=
        hJ.out ⟨a, ha, rfl⟩ ⟨c, hc, rfl⟩ ⟨hv1.le, hv2.le.trans (min_le_right _ _)⟩
      have hac' : a < c' := (hφ.lt_iff_lt ha hc').1 hv1
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hac')] with x hx hx'
      exact (hφ hx hc' hx').trans (hv2.trans_le (min_le_left _ _))
    · push Not at hex
      filter_upwards [self_mem_nhdsWithin] with x hx
      rcases (hex x hx).eq_or_lt with h | h
      · rw [h]; exact hb
      · exact (hφ hx ha h).trans hb

/-- A map continuous on every segment of an interval is continuous on the interval. -/
theorem continuousOn_of_forall_Icc {X : Type*} [TopologicalSpace X] {I : Set ℝ} {f : ℝ → X}
    (h : ∀ a ∈ I, ∀ b ∈ I, ContinuousOn f (Icc a b)) : ContinuousOn f I := by
  intro t ht
  have hL : ContinuousWithinAt f (I ∩ Iic t) t := by
    by_cases hex : ∃ a ∈ I, a < t
    · obtain ⟨a, ha, hat⟩ := hex
      refine ((h a ha t ht) t ⟨hat.le, le_rfl⟩).mono_of_mem_nhdsWithin ?_
      exact mem_nhdsWithin.2 ⟨Ioi a, isOpen_Ioi, hat, fun s hs => ⟨le_of_lt hs.1, hs.2.2⟩⟩
    · simp only [not_exists, not_and, not_lt] at hex
      exact continuousWithinAt_singleton.mono fun s hs => le_antisymm hs.2 (hex s hs.1)
  have hR : ContinuousWithinAt f (I ∩ Ici t) t := by
    by_cases hex : ∃ b ∈ I, t < b
    · obtain ⟨b, hb, htb⟩ := hex
      refine ((h t ht b hb) t ⟨le_rfl, htb.le⟩).mono_of_mem_nhdsWithin ?_
      exact mem_nhdsWithin.2 ⟨Iio b, isOpen_Iio, htb, fun s hs => ⟨hs.2.2, le_of_lt hs.1⟩⟩
    · simp only [not_exists, not_and, not_lt] at hex
      exact continuousWithinAt_singleton.mono fun s hs => le_antisymm (hex s hs.1) hs.2
  have := hL.union hR
  rwa [← inter_union_distrib_left, Iic_union_Ici, inter_univ] at this

/-- An interval of `ℝ` is locally path-connected. -/
theorem locPathConnectedSpace_of_ordConnected {I : Set ℝ} (hI : I.OrdConnected) :
    LocPathConnectedSpace I := by
  refine LocPathConnectedSpace.of_bases (p := fun _ (ε : ℝ) => 0 < ε)
    (s := fun x ε => (Subtype.val : I → ℝ) ⁻¹' (I ∩ Metric.ball (x : ℝ) ε)) (fun x => ?_)
    (fun x ε hε => ?_)
  · rw [nhds_subtype]
    refine ((Metric.nhds_basis_ball (x := (x : ℝ))).comap (Subtype.val : I → ℝ)).congr
      (fun _ => Iff.rfl) (fun ε _ => ?_)
    ext y
    simp
  · exact ((hI.convex.inter (convex_ball _ _)).isPathConnected
      ⟨x, x.2, Metric.mem_ball_self hε⟩).preimage_coe inter_subset_left

section Covering

variable {E : Type*} [TopologicalSpace E] [ChartedSpace (Minkowski d) E]
  [HasGroupoid E (gxGroupoid (isom d) (Minkowski d))]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (Minkowski d) M]
  [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))]
  {p : E → M}

/-- **A continuous lift of a causal curve through a local isometry is a causal curve**: if
`p ∘ c' = c` on `I`, `c` a causal curve of `M` over `I` and `c'` continuous on `I`, then `c'` is a
causal curve of `E` over `I` (no covering property is used). -/
theorem causalCurveIn_of_lift (hloc : IsLocalIsometry d p) {I : Set ℝ} {c : ℝ → M}
    (hc : (flatCausality d M).CausalCurveIn ⊤ I c) {c' : ℝ → E} (hc'cont : ContinuousOn c' I)
    (hlift : ∀ t ∈ I, p (c' t) = c t) : (flatCausality d E).CausalCurveIn ⊤ I c' := by
  refine ⟨hc.nonempty, hc.ordConnected, fun a ha b hb => ?_⟩
  refine ⟨fun _ _ => trivial, fun t ht N _ htN => ?_⟩
  have hIcc : Icc a b ⊆ I := hc.ordConnected.out ha hb
  obtain ⟨V, hxV, -, hV⟩ := hloc.localIsomorphism.2 (c' t)
  let V' : Opens E := V ⊓ N
  let U : Opens M := ⟨p '' V', hloc.isOpenMap _ V'.isOpen⟩
  have hcU : c t ∈ U := ⟨c' t, ⟨hxV, htN⟩, hlift t (hIcc ht)⟩
  obtain ⟨l₁, u₁, hl₁, hu₁, hrel⟩ := (hc.curve a ha b hb).rel t ht U le_top hcU
  have hev : ∀ᶠ s in 𝓝[Icc a b] t, c' s ∈ V' :=
    (hc'cont.mono hIcc) t ht (V'.isOpen.mem_nhds ⟨hxV, htN⟩)
  obtain ⟨O, hO, htO, hOsub⟩ := mem_nhdsWithin.1 hev
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO t htO
  refine ⟨max l₁ (t - ε), min u₁ (t + ε), max_lt hl₁ (by linarith), lt_min hu₁ (by linarith),
    fun s hs s' hs' h1 h2 h3 => ?_⟩
  have hmem : ∀ r ∈ Icc a b, max l₁ (t - ε) < r → r < min u₁ (t + ε) → c' r ∈ V' := by
    intro r hr hr1 hr2
    refine hOsub ⟨hball ?_, hr⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
    constructor
    · linarith [min_le_right u₁ (t + ε)]
    · linarith [le_max_right l₁ (t - ε)]
  have hsV := hmem s hs h1 (h2.trans h3)
  have hs'V := hmem s' hs' (h1.trans h2) h3
  have hcs := hrel s hs s' hs' ((le_max_left _ _).trans_lt h1) h2 (h3.trans_le (min_le_left _ _))
  rw [← hlift s (hIcc hs), ← hlift s' (hIcc hs')] at hcs
  exact (flatCausality d E).le_mono inf_le_right
    (((hV V' inf_le_left U rfl (c' s) hsV (c' s') hs'V).1).2 hcs)

/-- **Causal curves lift through a flat covering** `p` (a covering map and a local isometry),
from any point above their value at a parameter `t₀`. The proof is `Flat/Quotient`'s
`liftsCausalCurves`, with the starting point free. -/
theorem lift_causalCurveIn (hp : IsCoveringMap p) (hloc : IsLocalIsometry d p) {I : Set ℝ}
    {c : ℝ → M} (hc : (flatCausality d M).CausalCurveIn ⊤ I c) {t₀ : ℝ} (ht₀ : t₀ ∈ I) {e₀ : E}
    (he₀ : p e₀ = c t₀) :
    ∃ c' : ℝ → E, (flatCausality d E).CausalCurveIn ⊤ I c' ∧ c' t₀ = e₀ ∧
      ∀ t ∈ I, p (c' t) = c t := by
  have hcont : ContinuousOn c I :=
    continuousOn_of_forall_Icc fun a ha b hb => hc.continuousOn_Icc ha hb
  haveI : ContractibleSpace I := hc.ordConnected.convex.contractibleSpace hc.nonempty
  haveI : LocPathConnectedSpace I := locPathConnectedSpace_of_ordConnected hc.ordConnected
  obtain ⟨F, ⟨hF0, hFl⟩, -⟩ := hp.existsUnique_continuousMap_lifts
    ⟨I.restrict c, hcont.restrict⟩ ⟨t₀, ht₀⟩ e₀ he₀
  classical
  let c' : ℝ → E := fun t => if h : t ∈ I then F ⟨t, h⟩ else e₀
  have hc'I : ∀ t (h : t ∈ I), c' t = F ⟨t, h⟩ := fun t h => dif_pos h
  have hlift : ∀ t ∈ I, p (c' t) = c t := fun t h => by
    rw [hc'I t h]; exact congrFun hFl ⟨t, h⟩
  have hc'cont : ContinuousOn c' I := by
    rw [continuousOn_iff_continuous_restrict]
    have : I.restrict c' = F := funext fun ⟨t, h⟩ => hc'I t h
    rw [this]
    exact F.continuous
  exact ⟨c', causalCurveIn_of_lift hloc hc hc'cont hlift, by rw [hc'I t₀ ht₀]; exact hF0, hlift⟩

/-- **The projection of an inextensible causal curve through a flat covering is inextensible**:
an extension downstairs lifts (`lift_causalCurveIn`, started above the old curve), the lift agrees
with the old curve by uniqueness of lifts on the connected interval, and its new point projects
to the new point. -/
theorem inextensible_comp (hp : IsCoveringMap p) (hloc : IsLocalIsometry d p) {I : Set ℝ}
    {c : ℝ → E} (hc : (flatCausality d E).Inextensible ⊤ I c) :
    (flatCausality d M).Inextensible ⊤ I (p ∘ c) := by
  refine ⟨hloc.isEMorphism.causalCurveIn_comp le_rfl (U := ⊤) (fun _ _ => trivial) hc.1, ?_⟩
  rintro ⟨I', c', hcurve, ⟨φ, h1, h2, h3, h4⟩, ⟨t', ht', h5⟩⟩
  obtain ⟨t₀, ht₀⟩ := hc.1.nonempty
  obtain ⟨d', hd', hd0, hdl⟩ := lift_causalCurveIn hp hloc hcurve (h2 ht₀) (e₀ := c t₀)
    (by rw [h4 t₀ ht₀]; rfl)
  have hcI : ContinuousOn c I :=
    continuousOn_of_forall_Icc fun a ha b hb => hc.1.continuousOn_Icc ha hb
  have hd'I : ContinuousOn d' I' :=
    continuousOn_of_forall_Icc fun a ha b hb => hd'.continuousOn_Icc ha hb
  have hφc : ContinuousOn φ I := continuousOn_of_strictMonoOn h1 h3
  have heq : EqOn (d' ∘ φ) c I := hp.eqOn_of_comp_eqOn hc.1.ordConnected.isPreconnected
    (hd'I.comp hφc h2) hcI (fun t ht => by
      simp only [comp_apply]; rw [hdl _ (h2 ht), h4 t ht]; rfl) ht₀ hd0
  apply hc.2
  refine ⟨I', d', hd', ⟨φ, h1, h2, h3, fun t ht => heq ht⟩, ⟨t', ht', fun t ht he => ?_⟩⟩
  apply h5 t ht
  rw [← hdl t' ht', he]
  rfl

/-- **Cauchy surfaces lift through a flat covering** (the second sentence of
`bprop:splitting`, l.2462–2463, in ETT's reading: every inextensible causal curve of the cover
meets `p⁻¹(S)` exactly once). Existence: the projection is inextensible (`inextensible_comp`).
Uniqueness: two meeting points project to one point of `S`, so the projected curve is constant
between them (`C` causal, W10), and so is the curve (a lift of a constant path). -/
theorem isCauchySurface_preimage (hp : IsCoveringMap p) (hloc : IsLocalIsometry d p)
    (hcaus : (flatCausality d M).IsCausal) {S : Set M}
    (hS : (flatCausality d M).IsCauchySurface S) :
    (flatCausality d E).IsCauchySurface (p ⁻¹' S) := by
  intro I c hc
  have hpc := inextensible_comp hp hloc hc
  obtain ⟨_, ⟨⟨t, ht, rfl⟩, htS⟩, huniq⟩ := hS I (p ∘ c) hpc
  refine ⟨c t, ⟨⟨t, ht, rfl⟩, htS⟩, ?_⟩
  rintro _ ⟨⟨s, hs, rfl⟩, hsS⟩
  have hst : p (c s) = p (c t) := huniq _ ⟨⟨s, hs, rfl⟩, hsS⟩
  have hcI : ContinuousOn c I :=
    continuousOn_of_forall_Icc fun a ha b hb => hc.1.continuousOn_Icc ha hb
  -- `p ∘ c` is constant between `s` and `t`
  have key : ∀ a ∈ I, ∀ b ∈ I, a ≤ b → p (c a) = p (c b) → c a = c b := by
    intro a ha b hb hab he
    have hIcc : Icc a b ⊆ I := hc.1.ordConnected.out ha hb
    have hconst : EqOn c (fun _ => c a) (Icc a b) := hp.eqOn_of_comp_eqOn isPreconnected_Icc
      (hcI.mono hIcc) continuousOn_const (fun r hr => by
        simp only [comp_apply]
        have h1 := hpc.1.le_of_le ha (hIcc hr) hr.1
        have h2 := hpc.1.le_of_le (hIcc hr) hb hr.2
        simp only [comp_apply] at h1 h2
        rw [← he] at h2
        exact hcaus h2 h1) (left_mem_Icc.2 hab) rfl
    exact (hconst (right_mem_Icc.2 hab)).symm
  rcases le_total s t with h | h
  · exact key s hs t ht h hst
  · exact (key t ht s hs h hst.symm).symm

end Covering

/-! ### Maximal lifts of a path through a local homeomorphism (Prop 8.12, step 1)

Topology only: `D : X → Y` a local homeomorphism with `X` Hausdorff, `γ : ℝ → Y` continuous. A
lift of `γ` over an open interval through `x₀` at `t₀` is unique on overlaps; the union of all
of them is the maximal lift, and it cannot have a limit at a finite end of its interval. -/

section MaxLift

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {D : X → Y} {γ : ℝ → Y}
  {t₀ : ℝ} {x₀ : X}

/-- A lift of `γ` through `D`, over an open interval containing `t₀`, through `x₀` at `t₀`. -/
private def IsIntervalLift (D : X → Y) (γ : ℝ → Y) (t₀ : ℝ) (x₀ : X) (I : Set ℝ) (f : ℝ → X) :
    Prop :=
  IsOpen I ∧ I.OrdConnected ∧ t₀ ∈ I ∧ ContinuousOn f I ∧ f t₀ = x₀ ∧ ∀ s ∈ I, D (f s) = γ s

/-- Two intervals sharing a point have an order-connected union. -/
private theorem ordConnected_union_of_mem {A B : Set ℝ} (hA : A.OrdConnected)
    (hB : B.OrdConnected) {a : ℝ} (haA : a ∈ A) (haB : a ∈ B) : (A ∪ B).OrdConnected := by
  refine ⟨fun x hx y hy z hz => ?_⟩
  rcases le_or_gt z a with hza | hza
  · rcases hx with hx | hx
    · exact Or.inl (hA.out hx haA ⟨hz.1, hza⟩)
    · exact Or.inr (hB.out hx haB ⟨hz.1, hza⟩)
  · rcases hy with hy | hy
    · exact Or.inl (hA.out haA hy ⟨hza.le, hz.2⟩)
    · exact Or.inr (hB.out haB hy ⟨hza.le, hz.2⟩)

/-- **Uniqueness of lifts** on the common interval (`X` Hausdorff, `D` locally injective). -/
private theorem IsIntervalLift.eqOn [T2Space X] (hD : IsLocalHomeomorph D) {I J : Set ℝ}
    {f g : ℝ → X} (hf : IsIntervalLift D γ t₀ x₀ I f) (hg : IsIntervalLift D γ t₀ x₀ J g) :
    EqOn f g (I ∩ J) :=
  (T2Space.isSeparatedMap D).eqOn_of_comp_eqOn hD.isLocallyInjective
    (hf.2.1.inter hg.2.1).isPreconnected (hf.2.2.2.1.mono inter_subset_left)
    (hg.2.2.2.1.mono inter_subset_right)
    (fun s hs => by simp only [comp_apply]; rw [hf.2.2.2.2.2 s hs.1, hg.2.2.2.2.2 s hs.2])
    ⟨hf.2.2.1, hg.2.2.1⟩ (by rw [hf.2.2.2.2.1, hg.2.2.2.2.1])

/-- **Extension**: a lift `f` over `I` with a limit `p` above `γ b` at a
point `b` of the closure of `I` extends to a lift over `I ∪ ]b − ε, b + ε[` (a local inverse of
`D` near `p`). -/
private theorem IsIntervalLift.extend (hD : IsLocalHomeomorph D) (hγ : Continuous γ) {I : Set ℝ}
    {f : ℝ → X} (hf : IsIntervalLift D γ t₀ x₀ I f) {b : ℝ} {p : X} (hb : b ∈ closure I)
    (hp : D p = γ b) (htend : Tendsto f (𝓝[I] b) (𝓝 p)) :
    ∃ ε > 0, ∃ g : ℝ → X, IsIntervalLift D γ t₀ x₀ (I ∪ Metric.ball b ε) g := by
  obtain ⟨e, hpe, he⟩ := hD p
  have hDe : ∀ x, D x = e x := fun x => congrFun he x
  have hO : γ b ∈ e.target := by rw [← hp, hDe]; exact e.map_source hpe
  obtain ⟨ε₁, hε₁, hsub1⟩ := Metric.mem_nhdsWithin_iff.1 (htend (e.open_source.mem_nhds hpe))
  obtain ⟨ε₂, hε₂, hball2⟩ := Metric.isOpen_iff.1 (e.open_target.preimage hγ) b hO
  set ε := min ε₁ ε₂ with hε
  have hB2 : ∀ s ∈ Metric.ball b ε, γ s ∈ e.target := fun s hs =>
    hball2 (Metric.ball_subset_ball (min_le_right _ _) hs)
  have hfe : ∀ s ∈ I, s ∈ Metric.ball b ε → f s = e.symm (γ s) := by
    intro s hs hsB
    have hfs : f s ∈ e.source := hsub1 ⟨Metric.ball_subset_ball (min_le_left _ _) hsB, hs⟩
    rw [← hf.2.2.2.2.2 s hs, hDe, e.left_inv hfs]
  classical
  let g : ℝ → X := fun s => if s ∈ I then f s else e.symm (γ s)
  have hgI : ∀ s ∈ I, g s = f s := fun s hs => if_pos hs
  have hgB : ∀ s ∈ Metric.ball b ε, g s = e.symm (γ s) := by
    intro s hs
    by_cases h : s ∈ I
    · rw [hgI s h, hfe s h hs]
    · exact if_neg h
  have hεpos : 0 < ε := lt_min hε₁ hε₂
  obtain ⟨a, haB, haI⟩ := (Metric.mem_closure_iff.1 hb) ε hεpos
  refine ⟨ε, hεpos, g, hf.1.union Metric.isOpen_ball, ?_, Or.inl hf.2.2.1, ?_, ?_, ?_⟩
  · refine ordConnected_union_of_mem hf.2.1 ?_ haB (Metric.mem_ball.2 (by rwa [dist_comm]))
    rw [Real.ball_eq_Ioo]; exact ordConnected_Ioo
  · intro s hs
    refine ContinuousAt.continuousWithinAt ?_
    rcases hs with hs | hs
    · exact (hf.2.2.2.1.continuousAt (hf.1.mem_nhds hs)).congr
        (Filter.eventuallyEq_of_mem (hf.1.mem_nhds hs) fun r hr => (hgI r hr).symm)
    · exact ((e.continuousAt_symm (hB2 s hs)).comp hγ.continuousAt).congr
        (Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hs) fun r hr => (hgB r hr).symm)
  · rw [hgI t₀ hf.2.2.1]; exact hf.2.2.2.2.1
  · rintro s (hs | hs)
    · rw [hgI s hs]; exact hf.2.2.2.2.2 s hs
    · rw [hgB s hs, hDe, e.right_inv (hB2 s hs)]

/-- **A lift starts**: some lift of `γ` through `x₀` at `t₀` exists. -/
private theorem exists_isIntervalLift (hD : IsLocalHomeomorph D) (hγ : Continuous γ)
    (h0 : D x₀ = γ t₀) : ∃ I f, IsIntervalLift D γ t₀ x₀ I f := by
  obtain ⟨e, hx, he⟩ := hD x₀
  have hDe : ∀ x, D x = e x := fun x => congrFun he x
  have hO : γ t₀ ∈ e.target := by rw [← h0, hDe]; exact e.map_source hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (e.open_target.preimage hγ) t₀ hO
  refine ⟨Metric.ball t₀ ε, fun s => e.symm (γ s), Metric.isOpen_ball, ?_,
    Metric.mem_ball_self hε, e.continuousOn_symm.comp hγ.continuousOn fun s hs => hball hs, ?_, ?_⟩
  · rw [Real.ball_eq_Ioo]; exact ordConnected_Ioo
  · simp only; rw [← h0, hDe, e.left_inv hx]
  · intro s hs; simp only; rw [hDe, e.right_inv (hball hs)]

/-- The domain of the maximal lift: the union of the domains of all lifts. -/
private def maxLiftDom (D : X → Y) (γ : ℝ → Y) (t₀ : ℝ) (x₀ : X) : Set ℝ :=
  ⋃₀ {I | ∃ f, IsIntervalLift D γ t₀ x₀ I f}

open Classical in
/-- The maximal lift: at `s`, the value of any lift defined at `s`. -/
private noncomputable def maxLift (D : X → Y) (γ : ℝ → Y) (t₀ : ℝ) (x₀ : X) (s : ℝ) : X :=
  if h : ∃ I f, IsIntervalLift D γ t₀ x₀ I f ∧ s ∈ I then h.choose_spec.choose s else x₀

private theorem maxLift_eqOn [T2Space X] (hD : IsLocalHomeomorph D) {I : Set ℝ} {f : ℝ → X}
    (hf : IsIntervalLift D γ t₀ x₀ I f) : EqOn (maxLift D γ t₀ x₀) f I := by
  intro s hs
  have h : ∃ I f, IsIntervalLift D γ t₀ x₀ I f ∧ s ∈ I := ⟨I, f, hf, hs⟩
  rw [maxLift, dif_pos h]
  exact (h.choose_spec.choose_spec.1.eqOn hD hf) ⟨h.choose_spec.choose_spec.2, hs⟩

/-- **The maximal lift is a lift.** -/
private theorem isIntervalLift_maxLift [T2Space X] (hD : IsLocalHomeomorph D) (hγ : Continuous γ)
    (h0 : D x₀ = γ t₀) :
    IsIntervalLift D γ t₀ x₀ (maxLiftDom D γ t₀ x₀) (maxLift D γ t₀ x₀) := by
  obtain ⟨I₀, f₀, hf₀⟩ := exists_isIntervalLift hD hγ h0
  have ht₀ : t₀ ∈ maxLiftDom D γ t₀ x₀ := ⟨I₀, ⟨f₀, hf₀⟩, hf₀.2.2.1⟩
  refine ⟨isOpen_sUnion fun I ⟨f, hf⟩ => hf.1, ⟨fun x hx y hy z hz => ?_⟩, ht₀, ?_, ?_, ?_⟩
  · obtain ⟨I, ⟨f, hf⟩, hxI⟩ := hx
    obtain ⟨J, ⟨g, hg⟩, hyJ⟩ := hy
    rcases le_or_gt z t₀ with h | h
    · exact ⟨I, ⟨f, hf⟩, hf.2.1.out hxI hf.2.2.1 ⟨hz.1, h⟩⟩
    · exact ⟨J, ⟨g, hg⟩, hg.2.1.out hg.2.2.1 hyJ ⟨h.le, hz.2⟩⟩
  · rintro s ⟨I, ⟨f, hf⟩, hsI⟩
    exact ((hf.2.2.2.1.continuousAt (hf.1.mem_nhds hsI)).congr
      (Filter.eventuallyEq_of_mem (hf.1.mem_nhds hsI) fun r hr =>
        (maxLift_eqOn hD hf hr).symm)).continuousWithinAt
  · rw [maxLift_eqOn hD hf₀ hf₀.2.2.1]; exact hf₀.2.2.2.2.1
  · rintro s ⟨I, ⟨f, hf⟩, hsI⟩
    rw [maxLift_eqOn hD hf hsI]; exact hf.2.2.2.2.2 s hsI

/-- **Maximality**: the maximal lift has no limit at a point of the closure of its domain outside
it (`Y` Hausdorff for the limit to lie over `γ b`). -/
private theorem mem_maxLiftDom_of_tendsto [T2Space X] [T2Space Y] (hD : IsLocalHomeomorph D)
    (hγ : Continuous γ) (h0 : D x₀ = γ t₀) {b : ℝ} {p : X}
    (hb : b ∈ closure (maxLiftDom D γ t₀ x₀))
    (htend : Tendsto (maxLift D γ t₀ x₀) (𝓝[maxLiftDom D γ t₀ x₀] b) (𝓝 p)) :
    b ∈ maxLiftDom D γ t₀ x₀ := by
  have L := isIntervalLift_maxLift hD hγ h0
  haveI := mem_closure_iff_nhdsWithin_neBot.1 hb
  have h1 : Tendsto γ (𝓝[maxLiftDom D γ t₀ x₀] b) (𝓝 (D p)) :=
    ((hD.continuous.tendsto p).comp htend).congr'
      (eventuallyEq_nhdsWithin_of_eqOn fun s hs => L.2.2.2.2.2 s hs)
  have hp : D p = γ b :=
    tendsto_nhds_unique h1 (hγ.continuousAt.mono_left nhdsWithin_le_nhds)
  obtain ⟨ε, hε, g, hg⟩ := L.extend hD hγ hb hp htend
  exact ⟨_, ⟨g, hg⟩, Or.inr (Metric.mem_ball_self hε)⟩

/-- **The end of a reparametrised sub-arc** (the real-analysis core of inextensibility): if
`c' ∘ φ = c` on the open `J`, `φ` strictly increasing into the interval `I'` and bounded by a
point `t'` of `I'`, `c'` continuous on `I'`, and `c` carries a continuous "clock" `T` with
`T (c s) = s`, then `J` is bounded above and `c` has a limit at `sup J ∉ J`. -/
private theorem exists_end_of_upper {Z : Type*} [TopologicalSpace Z] {J I' : Set ℝ}
    {c c' : ℝ → Z} {φ : ℝ → ℝ} (T : Z → ℝ) (hT : Continuous T) (hTc : ∀ s ∈ J, T (c s) = s)
    (hJo : IsOpen J) (hJ : J.Nonempty) (hφ : StrictMonoOn φ J) (hmaps : MapsTo φ J I')
    (hI' : I'.OrdConnected) (hc' : ContinuousOn c' I') (heq : ∀ s ∈ J, c' (φ s) = c s)
    {t' : ℝ} (ht' : t' ∈ I') (hup : ∀ s ∈ J, φ s < t') :
    ∃ b p, b ∈ closure J ∧ b ∉ J ∧ Tendsto c (𝓝[J] b) (𝓝 p) := by
  obtain ⟨s₀, hs₀⟩ := hJ
  have hne : (φ '' J).Nonempty := ⟨_, s₀, hs₀, rfl⟩
  have hbdd : BddAbove (φ '' J) := ⟨t', by rintro _ ⟨s, hs, rfl⟩; exact (hup s hs).le⟩
  set τ := sSup (φ '' J)
  have hle : ∀ s ∈ J, φ s ≤ τ := fun s hs => le_csSup hbdd ⟨s, hs, rfl⟩
  have hτt' : τ ≤ t' := csSup_le hne (by rintro _ ⟨s, hs, rfl⟩; exact (hup s hs).le)
  have hτI : τ ∈ I' := hI'.out (hmaps hs₀) ht' ⟨hle s₀ hs₀, hτt'⟩
  have key : ∀ N ∈ 𝓝 (c' τ), ∃ s₁ ∈ J, ∀ s ∈ J, s₁ ≤ s → c s ∈ N := by
    intro N hN
    obtain ⟨η, hη, hηsub⟩ := Metric.mem_nhdsWithin_iff.1 (hc' τ hτI hN)
    obtain ⟨_, ⟨s₁, hs₁, rfl⟩, h1⟩ := exists_lt_of_lt_csSup hne (show τ - η < τ by linarith)
    refine ⟨s₁, hs₁, fun s hs hs₁s => ?_⟩
    have h2 : φ s₁ ≤ φ s := hφ.monotoneOn hs₁ hs hs₁s
    rw [← heq s hs]
    refine hηsub ⟨?_, hmaps hs⟩
    rw [Real.ball_eq_Ioo]
    exact ⟨by linarith, by linarith [hle s hs]⟩
  have hbddJ : BddAbove J := by
    obtain ⟨s₁, hs₁, h⟩ := key (T ⁻¹' Iio (T (c' τ) + 1))
      (hT.continuousAt.preimage_mem_nhds (Iio_mem_nhds (by linarith)))
    refine ⟨max s₁ (T (c' τ) + 1), fun s hs => ?_⟩
    rcases le_total s₁ s with h' | h'
    · have := h s hs h'
      rw [mem_preimage, mem_Iio, hTc s hs] at this
      exact le_max_of_le_right this.le
    · exact le_max_of_le_left h'
  have hbcl : sSup J ∈ closure J := csSup_mem_closure ⟨s₀, hs₀⟩ hbddJ
  have hbJ : sSup J ∉ J := fun hb => by
    obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.1 hJo _ hb
    have : sSup J + ε / 2 ∈ J := hsub (by rw [Real.ball_eq_Ioo]; constructor <;> linarith)
    linarith [le_csSup hbddJ this]
  refine ⟨sSup J, c' τ, hbcl, hbJ, tendsto_def.2 fun N hN => ?_⟩
  obtain ⟨s₁, hs₁, h⟩ := key N hN
  have hs₁b : s₁ < sSup J :=
    lt_of_le_of_ne (le_csSup hbddJ hs₁) (fun h => hbJ (h ▸ hs₁))
  exact mem_nhdsWithin.2 ⟨Ioi s₁, isOpen_Ioi, hs₁b, fun s ⟨hs1, hsJ⟩ => h s hsJ (le_of_lt hs1)⟩

/-- The mirror image of `exists_end_of_upper`: `φ` bounded below by `t' ∈ I'`. -/
private theorem exists_end_of_lower {Z : Type*} [TopologicalSpace Z] {J I' : Set ℝ}
    {c c' : ℝ → Z} {φ : ℝ → ℝ} (T : Z → ℝ) (hT : Continuous T) (hTc : ∀ s ∈ J, T (c s) = s)
    (hJo : IsOpen J) (hJ : J.Nonempty) (hφ : StrictMonoOn φ J) (hmaps : MapsTo φ J I')
    (hI' : I'.OrdConnected) (hc' : ContinuousOn c' I') (heq : ∀ s ∈ J, c' (φ s) = c s)
    {t' : ℝ} (ht' : t' ∈ I') (hlow : ∀ s ∈ J, t' < φ s) :
    ∃ b p, b ∈ closure J ∧ b ∉ J ∧ Tendsto c (𝓝[J] b) (𝓝 p) := by
  obtain ⟨s₀, hs₀⟩ := hJ
  obtain ⟨b, p, hb, hbJ, ht⟩ := exists_end_of_upper (J := -J) (I' := -I')
    (c := fun s => c (-s)) (c' := fun u => c' (-u)) (φ := fun s => -φ (-s)) (fun z => -T z)
    hT.neg (fun s hs => by rw [hTc (-s) hs, neg_neg]) hJo.neg ⟨-s₀, by simpa using hs₀⟩
    (fun s hs s' hs' h => neg_lt_neg (hφ hs' hs (neg_lt_neg h)))
    (fun s hs => by simpa using hmaps hs)
    ⟨fun x hx y hy z hz => hI'.out hy hx ⟨neg_le_neg hz.2, neg_le_neg hz.1⟩⟩
    (hc'.comp continuous_neg.continuousOn fun u hu => hu)
    (fun s hs => by simp only [neg_neg]; exact heq _ hs) (by simpa using ht')
    (fun s hs => neg_lt_neg (hlow _ hs))
  refine ⟨-b, p, ?_, by simpa using hbJ, ?_⟩
  · rw [← Set.mem_neg, neg_closure]; exact hb
  · have hneg : Tendsto (fun s : ℝ => -s) (𝓝[J] (-b)) (𝓝[-J] b) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have := (continuous_neg.tendsto (-b)).mono_left (nhdsWithin_le_nhds (s := J))
        rwa [neg_neg] at this
      · filter_upwards [self_mem_nhdsWithin] with s hs
        simpa using hs
    have := ht.comp hneg
    simpa [comp_def] using this

end MaxLift


/-! ## §8 on a flat spacetime: the developing pair and (CC′) -/

/-- The universal cover of a space with an atlas over `𝐌ⁿ` is a covering map. -/
theorem isCoveringMap_flatCover_proj (d : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (Minkowski d) M] (x₀ : M) : IsCoveringMap (UniversalCover.proj M x₀) :=
  haveI := locPathConnectedSpace_of_flat d M
  UniversalCover.isCoveringMap_proj (semilocallySimplyConnected_of_flat d M)

/-- A deck transformation of `M̃` with a fixed point is the identity. -/
theorem deck_eq_one_of_apply_eq (d : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (Minkowski d) M] {x₀ : M} (γ : Deck (UniversalCover.proj M x₀))
    {z : UniversalCover M x₀} (h : γ.1 z = z) : γ = 1 := by
  have hcov := isCoveringMap_flatCover_proj d M x₀
  have : (γ.1 : UniversalCover M x₀ → UniversalCover M x₀) = id :=
    hcov.eq_of_comp_eq γ.1.continuous continuous_id γ.2 z h
  apply Subtype.ext
  exact Homeomorph.ext fun w => by simpa using congrFun this w

/-- A covering space of a Hausdorff space is Hausdorff (a local copy of `Flat/CauchyComplete`'s
`t2Space_of_isCoveringMap`, which this file does not import). -/
private theorem t2Space_of_isCoveringMap' {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [T2Space X] {p : E → X} (hp : IsCoveringMap p) : T2Space E :=
  ⟨fun x₁ x₂ hne => by
    by_cases h : p x₁ = p x₂
    · exact hp.isSeparatedMap x₁ x₂ h hne
    · obtain ⟨u, v, hu, hv, hxu, hxv, huv⟩ := t2_separation h
      exact ⟨p ⁻¹' u, p ⁻¹' v, hu.preimage hp.continuous, hv.preimage hp.continuous, hxu, hxv,
        huv.preimage p⟩⟩

/-- **The deck group of a covering of a Hausdorff space acts properly discontinuously**: a compact
`K` meets only finitely many of its deck translates. Each pair `(x, y)` has neighbourhoods
`U ∋ x`, `V ∋ y` with at most one deck transformation sending a point of `U` into `V` —
separate `p x ≠ p y` in `X`, or, if `p x = p y`, take `V` a sheet at `y` and `U` the component of
`x` over its image: such a transformation agrees on `U` with the local section (uniqueness of
lifts), so it sends `x` to `y` — and finitely many such boxes cover `K × K`. -/
theorem finite_deck_of_isCompact {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [T2Space X] [PreconnectedSpace E] [LocallyConnectedSpace E] {p : E → X}
    (hp : IsCoveringMap p) {K : Set E} (hK : IsCompact K) :
    {γ : Deck p | (γ.1 '' K ∩ K).Nonempty}.Finite := by
  have hpγ : ∀ (γ : Deck p) (w : E), p (γ.1 w) = p w := fun γ w =>
    congrFun ((mem_deckGroup_iff _ _).1 γ.2) w
  have hfree : ∀ γ₁ γ₂ : Deck p, ∀ x, γ₁.1 x = γ₂.1 x → γ₁ = γ₂ := by
    intro γ₁ γ₂ x hx
    have : (γ₁.1 : E → E) = γ₂.1 := hp.eq_of_comp_eq γ₁.1.continuous γ₂.1.continuous
      (((mem_deckGroup_iff _ _).1 γ₁.2).trans ((mem_deckGroup_iff _ _).1 γ₂.2).symm) x hx
    exact Subtype.ext (Homeomorph.ext fun w => congrFun this w)
  have hbox : ∀ x y : E, ∃ U V : Set E, IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧
      ∀ γ₁ γ₂ : Deck p, (γ₁.1 '' U ∩ V).Nonempty → (γ₂.1 '' U ∩ V).Nonempty → γ₁ = γ₂ := by
    intro x y
    by_cases hxy : p x = p y
    · obtain ⟨e, hye, he⟩ := hp.isLocalHomeomorph y
      have hpe : ∀ w, p w = e w := fun w => congrFun he w
      have hxt : x ∈ p ⁻¹' e.target := by
        rw [mem_preimage, hxy, hpe]; exact e.map_source hye
      set U := connectedComponentIn (p ⁻¹' e.target) x
      have hUsub : U ⊆ p ⁻¹' e.target := connectedComponentIn_subset _ _
      have hkey : ∀ γ : Deck p, (γ.1 '' U ∩ e.source).Nonempty → γ.1 x = y := by
        rintro γ ⟨_, ⟨z, hzU, rfl⟩, hzs⟩
        have heqOn : EqOn γ.1 (fun w => e.symm (p w)) U :=
          hp.eqOn_of_comp_eqOn isPreconnected_connectedComponentIn γ.1.continuous.continuousOn
            (e.continuousOn_symm.comp hp.continuous.continuousOn hUsub)
            (fun w hw => by
              simp only [comp_apply]
              rw [hpγ, hpe (e.symm (p w)), e.right_inv (hUsub hw)])
            hzU (show γ.1 z = e.symm (p z) by rw [← hpγ γ z, hpe, e.left_inv hzs])
        rw [heqOn (mem_connectedComponentIn hxt)]
        simp only
        rw [hxy, hpe, e.left_inv hye]
      exact ⟨U, e.source, (e.open_target.preimage hp.continuous).connectedComponentIn,
        e.open_source, mem_connectedComponentIn hxt, hye,
        fun γ₁ γ₂ h1 h2 => hfree γ₁ γ₂ x ((hkey γ₁ h1).trans (hkey γ₂ h2).symm)⟩
    · obtain ⟨A, B, hA, hB, hxA, hyB, hAB⟩ := t2_separation hxy
      refine ⟨p ⁻¹' A, p ⁻¹' B, hA.preimage hp.continuous, hB.preimage hp.continuous, hxA, hyB,
        fun γ₁ _ h1 _ => ?_⟩
      obtain ⟨_, ⟨z, hz, rfl⟩, hzB⟩ := h1
      exact (Set.disjoint_left.1 hAB hz (by rw [← hpγ γ₁ z]; exact hzB)).elim
  choose U V hU hV hxU hyV hone using hbox
  obtain ⟨t, -, hcover⟩ := (hK.prod hK).elim_nhds_subcover (fun q => U q.1 q.2 ×ˢ V q.1 q.2)
    (fun q _ => ((hU q.1 q.2).prod (hV q.1 q.2)).mem_nhds ⟨hxU _ _, hyV _ _⟩)
  refine (t.finite_toSet.biUnion fun q _ =>
    (show {γ : Deck p | (γ.1 '' U q.1 q.2 ∩ V q.1 q.2).Nonempty}.Subsingleton from
      fun γ₁ h1 γ₂ h2 => hone _ _ γ₁ γ₂ h1 h2).finite).subset ?_
  rintro γ ⟨_, ⟨k, hk, rfl⟩, hγk⟩
  obtain ⟨q, hq, hmem⟩ := mem_iUnion₂.1 (hcover (show (k, γ.1 k) ∈ K ×ˢ K from ⟨hk, hγk⟩))
  exact mem_iUnion₂.2 ⟨q, hq, ⟨γ.1 k, ⟨k, hmem.1, rfl⟩, hmem.2⟩⟩

section Develop

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Minkowski d) M]
  [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))] (x₀ : M)

omit [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))] in
/-- The covering map `M̃ → M` is a local isometry for the pulled-back flat structure. -/
theorem isLocalIsometry_flatCover_proj :
    letI := flatCoverChartedSpace d M x₀
    IsLocalIsometry d (UniversalCover.proj M x₀) := by
  letI := flatCoverChartedSpace d M x₀
  have h := isGXMorphism_flatCover_proj (d := d) M x₀
  exact isLocalIsometry_iff_eventually.2 ⟨h.1, h.2⟩


/-- **The lift half of `bprop:splitting`** (l.2462–2463): for `M` causal (W10), the preimage
`S̃ = p⁻¹(S)` of a Cauchy surface `S` of `M` is a Cauchy surface of the universal cover `M̃`. -/
theorem isCauchySurface_liftSet (hcaus : (flatCausality d M).IsCausal) {S : Set M}
    (hS : (flatCausality d M).IsCauchySurface S) :
    letI := flatCoverChartedSpace d M x₀
    haveI := hasGroupoid_flatCover (d := d) M x₀
    (flatCausality d (UniversalCover M x₀)).IsCauchySurface (UniversalCover.proj M x₀ ⁻¹' S) := by
  letI := flatCoverChartedSpace d M x₀
  haveI := hasGroupoid_flatCover (d := d) M x₀
  exact isCauchySurface_preimage (isCoveringMap_flatCover_proj d M x₀)
    (isLocalIsometry_flatCover_proj x₀) hcaus hS

/-- **A developing pair** `(𝒟, ρ)` of `M` at `x₀` (Barbot l.2217–2226; `flat_developing_theorem`):
`𝒟 : M̃ → 𝐌ⁿ` an `(Isom(𝐌ⁿ), 𝐌ⁿ)`-morphism, equivariant for `ρ : Deck(M̃ → M) →* Isom(𝐌ⁿ)`. -/
structure IsDevelopingPair (D : UniversalCover M x₀ → Minkowski d)
    (ρ : Deck (UniversalCover.proj M x₀) →* isom d) : Prop where
  gx : letI := flatCoverChartedSpace d M x₀; IsGXMorphism (isom d) (Minkowski d) D
  equiv : ∀ (γ : Deck (UniversalCover.proj M x₀)) (z : UniversalCover M x₀),
    D (γ.1 z) = ρ γ • D z

theorem exists_isDevelopingPair :
    ∃ (D : UniversalCover M x₀ → Minkowski d) (ρ : Deck (UniversalCover.proj M x₀) →* isom d),
      IsDevelopingPair x₀ D ρ := by
  obtain ⟨D, ρ, hD, -, hρ⟩ := flat_developing_theorem (d := d) M x₀
  exact ⟨D, ρ, hD, hρ⟩

/-- **(CC′) for a Cauchy surface `S` of `M`** (DEC-35, `docs/BARBOT-WAVE3.md` §3): `𝒟` is
injective on the lift `S̃ = p⁻¹(S)`, and `Σ = 𝒟(S̃)` satisfies (CC′). -/
structure DevelopsCC (D : UniversalCover M x₀ → Minkowski d) (S : Set M) : Prop where
  cauchy : (flatCausality d M).IsCauchySurface S
  injOn : InjOn D (UniversalCover.proj M x₀ ⁻¹' S)
  cc : CCPrime (D '' (UniversalCover.proj M x₀ ⁻¹' S))

variable {x₀}


variable {D : UniversalCover M x₀ → Minkowski d} {ρ : Deck (UniversalCover.proj M x₀) →* isom d}
  {S : Set M}

omit [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))] in
theorem proj_deck_apply (γ : Deck (UniversalCover.proj M x₀)) (z : UniversalCover M x₀) :
    UniversalCover.proj M x₀ (γ.1 z) = UniversalCover.proj M x₀ z :=
  congrFun γ.2 z

omit [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))] in
/-- **Cor 8.2, `Γ` preserves `Σ`**: `ρ(γ) Σ = Σ`. -/
theorem holonomy_smul_eq (hpair : IsDevelopingPair x₀ D ρ) (γ : Deck (UniversalCover.proj M x₀)) :
    ρ γ • (D '' (UniversalCover.proj M x₀ ⁻¹' S)) = D '' (UniversalCover.proj M x₀ ⁻¹' S) := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  constructor
  · rintro ⟨z, hz, hzx⟩
    refine ⟨γ.1 z, by rwa [mem_preimage, proj_deck_apply], ?_⟩
    rw [hpair.equiv, hzx, smul_inv_smul]
  · rintro ⟨z, hz, rfl⟩
    refine ⟨γ⁻¹.1 z, by rwa [mem_preimage, proj_deck_apply], ?_⟩
    rw [hpair.equiv, map_inv]

/-- **Cor 8.2, freeness**: a point of `Σ` fixed by `ρ(γ)` forces `γ = 1`. -/
theorem eq_one_of_holonomy_fix (hpair : IsDevelopingPair x₀ D ρ) (h : DevelopsCC x₀ D S)
    {γ : Deck (UniversalCover.proj M x₀)} {x : Minkowski d}
    (hx : x ∈ D '' (UniversalCover.proj M x₀ ⁻¹' S)) (hfix : ρ γ • x = x) : γ = 1 := by
  obtain ⟨z, hz, rfl⟩ := hx
  rw [← hpair.equiv] at hfix
  exact deck_eq_one_of_apply_eq d γ (h.injOn (by rwa [mem_preimage, proj_deck_apply]) hz hfix)

/-- **Cor 8.2** (`bcor:quo`, l.2263–2271), the parts that hold from (CC′): `ρ` is injective, its
image `Γ` preserves `Σ = 𝒟(S̃)` and acts freely on it, and `Σ` meets every timelike line. -/
theorem bcor_quo (hpair : IsDevelopingPair x₀ D ρ) (h : DevelopsCC x₀ D S) :
    Injective ρ ∧ (∀ γ ∈ ρ.range, γ • (D '' (UniversalCover.proj M x₀ ⁻¹' S)) =
        D '' (UniversalCover.proj M x₀ ⁻¹' S)) ∧
      (∀ γ ∈ ρ.range, γ ≠ 1 → ∀ x ∈ D '' (UniversalCover.proj M x₀ ⁻¹' S), γ • x ≠ x) ∧
      ∀ p v : Minkowski d, IsFutureTimelike v →
        ∃ s : ℝ, p + s • v ∈ D '' (UniversalCover.proj M x₀ ⁻¹' S) := by
  refine ⟨(injective_iff_map_eq_one ρ).2 fun γ hγ => ?_, ?_, ?_, h.cc.entire.meets⟩
  · obtain ⟨s, hs⟩ := h.cc.entire.meets 0 _ isFutureTimelike_vertical
    exact eq_one_of_holonomy_fix hpair h hs (by rw [hγ, one_smul])
  · rintro _ ⟨γ, rfl⟩; exact holonomy_smul_eq hpair γ
  · rintro _ ⟨γ, rfl⟩ h1 x hx hfix
    exact h1 (by rw [eq_one_of_holonomy_fix hpair h hx hfix, map_one])

/-- **Prop 8.12, step 1** (`bprop:danom`, l.2476–2485), for a Hausdorff `M`: **the developing map
is injective.** Through each `z̃ ∈ M̃` the vertical line `δ` through `𝒟 z̃` has a maximal lift
through the local homeomorphism `𝒟` (`maxLift`; unique on overlaps since `M̃` is Hausdorff); it
is a causal curve (`causalCurveIn_of_lift`) and is inextensible — an extension would give it a
limit at a finite end of its interval (`exists_end_of_upper`/`_lower`, the clock being the time
coordinate of `𝒟`), where the lift continues (`mem_maxLiftDom_of_tendsto`). It therefore meets
`S̃` (`inextensible_comp`, `h.cauchy`), at a parameter where `δ` meets `Σ = graph g`: one
parameter for both points of a fibre of `𝒟`, where the two lifts agree by `h.injOn`, hence
everywhere by uniqueness of lifts. Neither `IsCausal` nor the holonomy is used. -/
theorem injective_of_developsCC [T2Space M] (hpair : IsDevelopingPair x₀ D ρ)
    (h : DevelopsCC x₀ D S) : Injective D := by
  letI := flatCoverChartedSpace d M x₀
  haveI := hasGroupoid_flatCover (d := d) M x₀
  have hcov := isCoveringMap_flatCover_proj d M x₀
  haveI : T2Space (UniversalCover M x₀) := t2Space_of_isCoveringMap' hcov
  have hloc : IsLocalIsometry d D := isLocalIsometry_iff_eventually.2 ⟨hpair.gx.1, hpair.gx.2⟩
  have hD := hloc.isLocalHomeomorph
  set Sh := UniversalCover.proj M x₀ ⁻¹' S
  have hv : IsFutureCausal ((1, 0) : Minkowski d) := ⟨zero_le_one, by simp [minkQ]⟩
  have hv0 : ((1, 0) : Minkowski d) ≠ 0 := fun h0 => one_ne_zero (congrArg Prod.fst h0)
  have hv1 : (0 : ℝ) < ((1, 0) : Minkowski d).1 := zero_lt_one
  -- each point lies on a lift of its vertical line, and that lift meets `S̃`
  have key : ∀ z : UniversalCover M x₀, ∃ (J : Set ℝ) (c : ℝ → UniversalCover M x₀),
      J.OrdConnected ∧ (D z).1 ∈ J ∧ ContinuousOn c J ∧ c (D z).1 = z ∧
      (∀ s ∈ J, D (c s) = timeLine (D z) (1, 0) s) ∧ ∃ s ∈ J, c s ∈ Sh := by
    intro z
    set γ : ℝ → Minkowski d := timeLine (D z) (1, 0) with hγdef
    have hγ : Continuous γ := by
      rw [hγdef]; unfold timeLine; fun_prop
    have h0 : D z = γ (D z).1 := (timeLine_self hv1).symm
    have L := isIntervalLift_maxLift hD hγ h0
    set J := maxLiftDom D γ (D z).1 z
    set c := maxLift D γ (D z).1 z
    have hγc : (flatCausality d (Minkowski d)).CausalCurveIn ⊤ J γ := by
      rw [flatCausality_self]
      have := (inextensible_timeLine (D z) hv hv0).1
      exact ⟨⟨_, L.2.2.1⟩, L.2.1, fun a _ b _ => this.curve a trivial b trivial⟩
    have hcJ : (flatCausality d (UniversalCover M x₀)).CausalCurveIn ⊤ J c :=
      causalCurveIn_of_lift hloc hγc L.2.2.2.1 L.2.2.2.2.2
    have hT : Continuous fun w : UniversalCover M x₀ => (D w).1 :=
      continuous_fst.comp hD.continuous
    have hTc : ∀ s ∈ J, (fun w => (D w).1) (c s) = s := fun s hs => by
      simp only; rw [L.2.2.2.2.2 s hs, timeLine_fst hv1]
    have hinext : (flatCausality d (UniversalCover M x₀)).Inextensible ⊤ J c := by
      refine ⟨hcJ, ?_⟩
      rintro ⟨I', c', hcurve, ⟨φ, hφ, hmaps, hφoc, hφeq⟩, ⟨t', ht', hgrow⟩⟩
      have hc' : ContinuousOn c' I' :=
        continuousOn_of_forall_Icc fun a ha b hb => hcurve.continuousOn_Icc ha hb
      have hne : ∀ s ∈ J, φ s ≠ t' := fun s hs he => hgrow s hs (by rw [← he, hφeq s hs])
      have hend : ∃ b p, b ∈ closure J ∧ b ∉ J ∧ Tendsto c (𝓝[J] b) (𝓝 p) := by
        by_cases hup : ∀ s ∈ J, φ s < t'
        · exact exists_end_of_upper _ hT hTc L.1 ⟨_, L.2.2.1⟩ hφ hmaps hcurve.ordConnected hc'
            hφeq ht' hup
        · push Not at hup
          obtain ⟨s₁, hs₁, h₁⟩ := hup
          refine exists_end_of_lower _ hT hTc L.1 ⟨_, L.2.2.1⟩ hφ hmaps hcurve.ordConnected hc'
            hφeq ht' fun s hs => ?_
          by_contra hlt
          push Not at hlt
          obtain ⟨s₂, hs₂, he⟩ := hφoc.out ⟨s, hs, rfl⟩ ⟨s₁, hs₁, rfl⟩ ⟨hlt, h₁⟩
          exact hne s₂ hs₂ he
      obtain ⟨b, p, hb, hbJ, ht⟩ := hend
      exact hbJ (mem_maxLiftDom_of_tendsto hD hγ h0 hb ht)
    obtain ⟨_, ⟨⟨s, hs, rfl⟩, hsS⟩, -⟩ :=
      h.cauchy J _ (inextensible_comp hcov (isLocalIsometry_flatCover_proj x₀) hinext)
    exact ⟨J, c, L.2.1, L.2.2.1, L.2.2.2.1, L.2.2.2.2.1, L.2.2.2.2.2, s, hs, hsS⟩
  -- a vertical line meets `Σ = graph g` at one parameter
  obtain ⟨g, -, hgr⟩ := isEntireAcausalGraph_iff.1 h.cc.entire
  have hline : ∀ (y : Minkowski d) (s : ℝ), timeLine y (1, 0) s ∈ D '' Sh → s = g y.2 := by
    intro y s hs
    rw [hgr] at hs
    have h1 : (timeLine y (1, 0) s).1 = g (timeLine y (1, 0) s).2 := hs
    rwa [timeLine_fst hv1, show (timeLine y (1, 0) s).2 = y.2 by simp [timeLine]] at h1
  intro a b hab
  obtain ⟨Ja, ca, ha1, ha2, ha3, ha4, ha5, sa, hsa, hsaS⟩ := key a
  obtain ⟨Jb, cb, hb1, hb2, hb3, hb4, hb5, sb, hsb, hsbS⟩ := key b
  rw [hab] at ha2 ha4 ha5
  have hss : sa = sb :=
    (hline _ _ ⟨ca sa, hsaS, ha5 sa hsa⟩).trans (hline _ _ ⟨cb sb, hsbS, hb5 sb hsb⟩).symm
  subst hss
  have hcs : ca sa = cb sa := h.injOn hsaS hsbS (by rw [ha5 sa hsa, hb5 sa hsb])
  have hEq := (T2Space.isSeparatedMap D).eqOn_of_comp_eqOn hD.isLocallyInjective
    (ha1.inter hb1).isPreconnected (ha3.mono inter_subset_left) (hb3.mono inter_subset_right)
    (fun r hr => by simp only [comp_apply]; rw [ha5 r hr.1, hb5 r hr.2]) ⟨hsa, hsb⟩ hcs
  exact ha4.symm.trans ((hEq ⟨ha2, hb2⟩).trans hb4)

/-- **Cor 8.2, "`𝒟 ∘ f̃` is an embedding"** (l.2264), for a Hausdorff `M`: `𝒟` is an open
embedding of `M̃` (`injective_of_developsCC` and the local homeomorphism `𝒟`), so in particular
its restriction to `S̃` is an embedding onto `Σ`. -/
theorem isOpenEmbedding_of_developsCC [T2Space M] (hpair : IsDevelopingPair x₀ D ρ)
    (h : DevelopsCC x₀ D S) : IsOpenEmbedding D := by
  letI := flatCoverChartedSpace d M x₀
  exact (isLocalIsometry_iff_eventually.2 ⟨hpair.gx.1, hpair.gx.2⟩).isLocalHomeomorph
    |>.isOpenEmbedding_of_injective (injective_of_developsCC hpair h)

/-- **Cor 8.2, proper discontinuity on `Σ`** (`π₁(S)` acting properly on `S̃`), for a Hausdorff
`M`: `𝒟` is an open embedding (`isOpenEmbedding_of_developsCC`), so `𝒟⁻¹(K)` is compact for a
compact `K ⊆ Σ`, and it meets finitely many of its deck translates (`finite_deck_of_isCompact`);
`ρ(γ) K ∩ K ≠ ∅` forces `γ 𝒟⁻¹(K) ∩ 𝒟⁻¹(K) ≠ ∅` by equivariance. -/
theorem holonomy_proper [T2Space M] (hpair : IsDevelopingPair x₀ D ρ)
    (h : DevelopsCC x₀ D S) :
    ∀ K ⊆ D '' (UniversalCover.proj M x₀ ⁻¹' S), IsCompact K →
      {γ : isom d | γ ∈ ρ.range ∧ (γ • K ∩ K).Nonempty}.Finite := by
  intro K hKS hK
  haveI := locPathConnectedSpace_of_flat d M
  have hK' : IsCompact (D ⁻¹' K) := (isOpenEmbedding_of_developsCC hpair h).isInducing
    |>.isCompact_preimage' hK (hKS.trans (image_subset_range _ _))
  refine ((finite_deck_of_isCompact (isCoveringMap_flatCover_proj d M x₀) hK').image ρ).subset ?_
  rintro _ ⟨⟨γ, rfl⟩, _, ⟨k, hk, rfl⟩, hkK⟩
  obtain ⟨k', -, rfl⟩ := hKS hk
  refine ⟨γ, ⟨γ.1 k', ⟨k', hk, rfl⟩, ?_⟩, rfl⟩
  rw [mem_preimage, hpair.equiv]
  exact hkK

/-- **The standing hypotheses hold for `(ρ(Deck), Σ)`**, for a Hausdorff `M`. -/
theorem ccAction_of_developsCC [T2Space M] (hpair : IsDevelopingPair x₀ D ρ)
    (h : DevelopsCC x₀ D S) :
    CCAction ρ.range (D '' (UniversalCover.proj M x₀ ⁻¹' S)) :=
  ⟨h.cc, (bcor_quo hpair h).2.1, (bcor_quo hpair h).2.2.1, holonomy_proper hpair h⟩

/-- **The design's conjunct `IsPreconnected S̃`** (`docs/BARBOT-WAVE3.md` §3; Barbot's `S̃` is the
universal cover of the connected `S`), for a Hausdorff `M`: `𝒟` is an embedding
(`isOpenEmbedding_of_developsCC`) and `Σ = 𝒟(S̃)` is connected (`CCAction.isPreconnected`). -/
theorem isPreconnected_liftSet_of_developsCC [T2Space M] (hpair : IsDevelopingPair x₀ D ρ)
    (h : DevelopsCC x₀ D S) : IsPreconnected (UniversalCover.proj M x₀ ⁻¹' S) :=
  (isOpenEmbedding_of_developsCC hpair h).isInducing.isPreconnected_image.1
    (ccAction_of_developsCC hpair h).isPreconnected

/-- **Prop 8.12** (`bprop:danom`, l.2469–2473), for a Hausdorff `M` (Barbot's spacetimes are
manifolds; without `T2Space M` the statement is false, module SCOPE), by the causal repair of
`docs/BARBOT-WAVE3.md` §3 (no slices): `𝒟` is injective (`injective_of_developsCC`, step 1)
and `𝒟(M̃) ⊆ Ω(S̃)`. -/
theorem bprop_danom [T2Space M] (hpair : IsDevelopingPair x₀ D ρ)
    (hcaus : (flatCausality d M).IsCausal) (h : DevelopsCC x₀ D S) :
    Injective D ∧ range D ⊆ omegaS ρ.range (D '' (UniversalCover.proj M x₀ ⁻¹' S)) := by
  letI := flatCoverChartedSpace d M x₀
  haveI := hasGroupoid_flatCover (d := d) M x₀
  set Sh := UniversalCover.proj M x₀ ⁻¹' S
  -- step 1
  have hinj : Injective D := by
    exact injective_of_developsCC hpair h
  -- step 2: `Σ` is a Cauchy surface of the open `𝒟(M̃)`
  have hiso : IsIsometricEmbedding d D :=
    ⟨isLocalIsometry_iff_eventually.2 ⟨hpair.gx.1, hpair.gx.2⟩, hinj⟩
  have hopen : IsOpen (range D) := hpair.gx.isOpenMap.isOpen_range
  set W : Opens (Minkowski d) := ⟨range D, hopen⟩
  have hW : (W : Set (Minkowski d)) = D '' ((⊤ : Opens (UniversalCover M x₀)) :
      Set (UniversalCover M x₀)) := by
    rw [Opens.coe_top, image_univ]; rfl
  have hC : (minkowski d).IsCauchySurfaceOn W (D '' Sh) := by
    have := (hiso.isEMorphism.isCauchySurfaceOn_image_iff hinj.injOn le_rfl hW
      (subset_univ Sh)).1 (isCauchySurface_liftSet x₀ hcaus h.cauchy)
    rwa [flatCausality_self] at this
  -- steps 3–5: `𝒟(M̃) ⊆ D(Σ) ⊆ U(Γ)`
  have hD : range D ⊆ dependenceDomain (minkowski d) ⊤ (D '' Sh) := by
    intro y hy
    refine ⟨trivial, fun I c hc ⟨t, ht, hct⟩ => ?_⟩
    have hcW : c t ∈ W := by rw [hct]; exact hy
    obtain ⟨_, ⟨⟨r, hr, rfl⟩, hrS⟩, -⟩ := hC _ c
      (Causality.inextensible_ordConnectedComponent minkowski_isCausal hc ht hcW)
    exact ⟨c r, ⟨r, (ordConnectedComponent_subset hr).1, rfl⟩, hrS⟩
  have hU := hD.trans (ccAction_of_developsCC hpair h).dependenceDomain_subset_UGamma
  -- step 6: `𝒟(M̃)` is open, connected and contains `Σ`
  have hΩ : range D ⊆ omegaGamma ρ.range := interior_maximal hU hopen
  obtain ⟨x, hx⟩ := (ccAction_of_developsCC hpair h).nonempty
  rw [omegaS_eq (ccAction_of_developsCC hpair h) hx]
  have hxD : x ∈ range D := image_subset_range _ _ hx
  exact ⟨hinj, (isPreconnected_range hpair.gx.1).subset_connectedComponentIn hxD hΩ⟩

end Develop

/-! ### Non-vacuity of `DevelopsCC` (kb/0011): `𝐌ⁿ` itself, `Σ` a horizontal hyperplane -/

/-- Over the simply connected `𝐌ⁿ`, the covering `M̃ → M` is injective. -/
theorem injective_proj_minkowski (x₀ : Minkowski d) :
    Injective (UniversalCover.proj (Minkowski d) x₀) := by
  rintro ⟨a, ca⟩ ⟨b, cb⟩ (hab : a = b)
  subst hab
  congr
  induction ca using Quotient.inductionOn
  induction cb using Quotient.inductionOn
  exact Quotient.sound (SimplyConnectedSpace.paths_homotopic _ _)

/-- `(proj, 1)` is a developing pair of `𝐌ⁿ`. -/
theorem isDevelopingPair_minkowski (x₀ : Minkowski d) :
    IsDevelopingPair x₀ (UniversalCover.proj (Minkowski d) x₀) 1 where
  gx := isGXMorphism_flatCover_proj (d := d) (Minkowski d) x₀
  equiv γ z := by rw [MonoidHom.one_apply, one_smul]; exact congrFun γ.2 z

/-- **`DevelopsCC` is inhabited**: `M = 𝐌ⁿ`, `𝒟 = proj`, `S = {t = 0}`. -/
theorem developsCC_minkowski (x₀ : Minkowski d) :
    DevelopsCC x₀ (UniversalCover.proj (Minkowski d) x₀)
      (graph fun _ : EuclideanSpace ℝ (Fin d) => (0 : ℝ)) where
  cauchy := by rw [flatCausality_self]; exact isCauchySurface_graph_zero
  injOn := (injective_proj_minkowski x₀).injOn
  cc := by
    rw [image_preimage_eq _ (UniversalCover.proj_surjective)]
    exact ccPrime_graph_const 0

example (x₀ : Minkowski d) := bcor_quo (isDevelopingPair_minkowski x₀) (developsCC_minkowski x₀)

example (x₀ : Minkowski d) :=
  holonomy_proper (isDevelopingPair_minkowski x₀) (developsCC_minkowski x₀)

end Causal.Flat
