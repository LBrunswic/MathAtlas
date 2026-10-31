import CausalScaffold.Flat.Developing
import CausalScaffold.Flat.LipschitzGraph
import CausalScaffold.Flat.AchronalDomains
import CausalScaffold.Flat.Penrose
import CausalScaffold.Flat.FlatSpacetime
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible

/-!
# `CausalScaffold.Flat.Develop` — Barbot §8 from (CC′): `U(g)`, `Ω(Γ)`, `Ω(S̃)`, Lemma 8.6, Prop 8.10, Cauchy surfaces lift, Prop 8.12

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §8,
`GHFspace.tex` l.2212–2526 (labelled file). Design: `docs/BARBOT-WAVE3.md` §3 (DEC-35: everything
after Prop 8.1 / Cor 8.3 runs from (CC′)); defects W4, W7, W8, W10 of its §0 apply. **No label is
marked**: each is `partial` (SCOPE), several being fully proved in a reading.

* `bcor:quo` (Cor 8.2, l.2263–2271), partial — `bcor_quo`, `holonomy_proper` (`sorry`):
  > The maps $f$ and ${\mathcal D} \circ \tilde{f}$ are embeddings. The natural morphism
  > $\Gamma \subset \pi_{1}(M)$ and the morphism $\rho$ are injective. Moreover,
  > ${\mathcal D} \circ \tilde{f}(\widetilde{S})$ intersects every timelike geodesic.
* `bdef:U_g` (Def 8.5, l.2332–2349), partial (readings) — `Ug`:
  > - $U(g) = \Omega_{g}$ if $g$ is loxodromic, or spacelike elliptic, or non linear parabolic.
  > - $U(g) = \emptyset$ if $g$ is nonspacelike elliptic, - $U(g) = {\bf M}^{n} \setminus J^{\perp}$
  > if $g$ is linear parabolic, where $J$ is the lightlike affine line of fixed points of $g$,
* `blem:SdanU` (Lemma 8.6, l.2353–2358), partial (W4 reading; **no `sorry`**) — `blem_SdanU`:
  > The complete spacelike hypersurface $\widetilde{S}$ is contained in the interior of
  > $U(\Gamma) = \bigcap_{\gamma \in \Gamma} U(\gamma)$.
* `bdef:omega_gamma` (Def 8.7, l.2394–2400), partial (W4) — `omegaGamma`, `omegaS`, `omegaS_eq`:
  > The interior of $U(\Gamma)$ is denoted by $\Omega(\Gamma)$ […] The connected component
  > of the interior of $U(\Gamma)$ containing $\widetilde{S}$ is denoted by $\Omega(\widetilde{S})$.
* Rem 8.8 `remplacefini` (l.2403–2408), unlabelled in the ledger — `achronalDomain_subset_zpow`,
  `UGamma_antitone`, `Ug_zpow` (`sorry`), `UGamma_eq_of_index`:
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
* `bprop:danom` (Prop 8.12, l.2469–2473), partial (steps 3–6 proved; step 1 and properness
  `sorry`) — `bprop_danom`:
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
* `IsCausalPiece`, `convex_causallyConvex_connectedComponentIn` (W8: components of `int A` are
  convex and causally convex when `A` is a piece), `pos_mul_of_null`, the per-class pieces
  `isCausalPiece_compl_nullHyperplanes`, `_achronalDomain_lox`, `_spacelikeElliptic`, `_tangent`.
* Flat coverings: `lift_causalCurveIn`, `inextensible_comp`, `isCauchySurface_preimage`;
  `continuousOn_of_strictMonoOn`. `IsDevelopingPair`, `DevelopsCC`, `bcor_quo`,
  `ccAction_of_developsCC`, `bprop_danom`; the witness `developsCC_minkowski`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `S` a complete Riemannian hypersurface, `f` an isometric immersion (l.2215–2216) | ⚠ strengthened (DEC-35 reading): `S` a Cauchy surface of `M` with `DevelopsCC` ((CC′) for `Σ = 𝒟(p⁻¹S)`, `𝒟` injective on `p⁻¹S`); `S̃ := p⁻¹(S) ⊆ M̃`, not the universal cover of `S` |
| `Γ = π₁(S)` acting on `S̃` (free, properly discontinuous) | ⚠ strengthened in `𝐌ⁿ`: `CCAction` carries it; on `M` it is `ρ(Deck(M̃ → M))` (`bcor_quo`; properness `sorry`) |
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
* **Sorries (3).** `Ug_zpow` (Rem 8.8); `holonomy_proper` (`𝒟|S̃` an embedding, deck group
  proper); `bprop_danom` step 1 (maximal lifts through the local homeomorphism `𝒟`).
  `bprop_ghyp` uses `lorentz_trichotomy`, proved in Isometries' source; an Isometries olean built
  before that proof still carries `sorryAx` until it is rebuilt.
* **Cor 8.2, not proved:** "`f` and `𝒟 ∘ f̃` are embeddings" and the design's conjunct
  `IsPreconnected S̃` (`S̃ = p⁻¹S`); both need `𝒟|S̃ : S̃ → Σ` to be a homeomorphism (fact (1) of
  `holonomy_proper`'s `sorry`), since `Σ` is connected (`CCAction.isPreconnected`).
* Non-vacuity: `ccAction_bot` (any (CC′) surface, trivial `Γ`; the hyperboloid in an `example`);
  `developsCC_minkowski` (`M = 𝐌ⁿ`, `𝒟 = proj`, `S = {t = 0}`, trivial holonomy). No inhabitant
  of `DevelopsCC` with nontrivial holonomy is formalized.
* **Findings.** Lemma 8.6's transverse case needs no Lemma 7.1 (false for `d ≥ 3`,
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

/-- **Rem 8.8, first sentence** (l.2404): `U(gⁿ) = U(g)` for `n ≠ 0`. -/
theorem Ug_zpow (g : isom d) {n : ℤ} (hn : n ≠ 0) : Ug (g ^ n) = Ug g := by
  sorry -- SORRY(remplacefini): needs each class stable under nonzero powers with the same `U` — `Ω_{gⁿ} ⊇ Ω_g` is `achronalDomain_subset_zpow`, but `Ω_{gⁿ} ⊆ Ω_g` and the stability of "nonspacelike elliptic", "linear parabolic" and of the hyperplanes `c + J^⊥` under powers need the normal forms of §6–§7 class by class (over `lorentz_trichotomy`, which is available) and the mutual exclusivity of the classes for a power, which nothing in the library states

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
  refine ⟨c', ⟨hc.nonempty, hc.ordConnected, fun a ha b hb => ?_⟩, by rw [hc'I t₀ ht₀]; exact hF0,
    hlift⟩
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

/-- **Cor 8.2, proper discontinuity on `Σ`** (Barbot's "`𝒟 ∘ f̃` is an embedding" and `π₁(S)`
acting properly on `S̃`). -/
theorem holonomy_proper (_hpair : IsDevelopingPair x₀ D ρ) (_h : DevelopsCC x₀ D S) :
    ∀ K ⊆ D '' (UniversalCover.proj M x₀ ⁻¹' S), IsCompact K →
      {γ : isom d | γ ∈ ρ.range ∧ (γ • K ∩ K).Nonempty}.Finite := by
  sorry -- SORRY(bcor:quo): two facts are missing. (1) `𝒟|S̃ : S̃ → Σ` is a homeomorphism (Barbot's "`𝒟 ∘ f̃` is an embedding", from Prop 8.1's homeomorphism, which (CC′) does not carry): it needs `S̃` to be, in each flat chart, an edgeless achronal set hence a local graph over an open set of `ℝᵈ`, so that the injective `𝒟|S̃` is open onto `Σ`. (2) The deck group of `M̃ → M` acts properly discontinuously on `M̃` (finitely many sheets of a compact set); neither is in the library or the port

/-- **The standing hypotheses hold for `(ρ(Deck), Σ)`.** -/
theorem ccAction_of_developsCC (hpair : IsDevelopingPair x₀ D ρ) (h : DevelopsCC x₀ D S) :
    CCAction ρ.range (D '' (UniversalCover.proj M x₀ ⁻¹' S)) :=
  ⟨h.cc, (bcor_quo hpair h).2.1, (bcor_quo hpair h).2.2.1, holonomy_proper hpair h⟩

/-- **Prop 8.12** (`bprop:danom`, l.2469–2473), by the causal repair of
`docs/BARBOT-WAVE3.md` §3 (no slices): `𝒟` is injective and `𝒟(M̃) ⊆ Ω(S̃)`. -/
theorem bprop_danom (hpair : IsDevelopingPair x₀ D ρ) (hcaus : (flatCausality d M).IsCausal)
    (h : DevelopsCC x₀ D S) :
    Injective D ∧ range D ⊆ omegaS ρ.range (D '' (UniversalCover.proj M x₀ ⁻¹' S)) := by
  letI := flatCoverChartedSpace d M x₀
  haveI := hasGroupoid_flatCover (d := d) M x₀
  set Sh := UniversalCover.proj M x₀ ⁻¹' S
  -- step 1
  have hinj : Injective D := by
    sorry -- SORRY(bprop:danom, step 1): l.2476–2485. For `z̃ ∈ M̃`, the connected component `d(z̃)` of `𝒟⁻¹(δ)` through `z̃` (`δ` the vertical line through `𝒟 z̃`) is an inextensible causal curve of `M̃` (the maximal lift of `δ` through the local homeomorphism `𝒟`, which is not a covering map), so it meets `S̃` (`isCauchySurface_liftSet`) at one point; equal images give equal meeting points by `h.injOn`, hence equal components, on which `𝒟` is injective. The maximal-lift construction through a local homeomorphism (`docs/BARBOT-WAVE3.md` §5 R1) is not in the library
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

end Causal.Flat
