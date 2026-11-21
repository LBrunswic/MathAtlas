import Causal.Static
import Causal.CausalIsoInvariance
import Causal.LadderLocal
import Causal.CauchyDual
import Causal.Flat.LipschitzGraph
import Causal.InextensiblePiece

/-!
# ERS Lemma 4.86 on `ℝ × E`: a slope-`δ` cone nested in `C` makes the boundary of a development a graph, the development on one side

Programme target `T-loc-quasilinear-one-sided` (`programme/roadmap.toml`; layer 3, localisation,
model `quasilinear`, uses `curve_nested`, `globally_hyperbolic`; provides nothing:
`one_sided_boundary` is no node, OQ-52 (b)). Paper: Eperon–Reall–Sbierski 1802.03020,
`papers/ers-predictability/legacy/labeled/ghd_02_19.tex`. The paper's labels are not marked
(SCOPE: readings); the target's own statements are.

* `erslem:PropertyTimelike` — `ghd_02_19.tex:1143` (Lemma 4.86; proof `:1159–1169`), not marked:
  `Causal.ers_lemma_4_86` gives (4.83) at every point of `∂U₁ ∖ closure S`
  (`Causal.BoundaryGraph`: the identity chart, time-reversed below `{t = 0}`), for either time
  orientation of `∂₀`; `Causal.ers_lemma_4_86_oneSidedBoundary` its topological content
  `Causal.Causality.OneSidedBoundary U₁ (closure S)`; `Causal.ers_lemma_4_86_edge` with `∂S` read
  as `closure S ∖ S` (the same set, `frontier_diff_closure_eq_frontier_diff_edge`).
* `ersthm:ThmNotBlocking` — `ghd_02_19.tex:1100` (Theorem 4.82), not marked:
  `Causal.ers_theorem_4_82_of_slopeCone`, the skeleton with (4.83) supplied by Lemma 4.86.
* **`T-loc-quasilinear-one-sided/1-one-sided`** — the target's statement on `ℝ × E`: the slope-`δ`
  cone (`slopeCone E δ hδ`) curve-nested in `C` on `U₁` and `S ⊆ {t = 0}` a Cauchy surface of `U₁`
  give the graph (`ers_lemma_4_86`) and `OneSidedBoundary U₁ (closure S)`
  (`ers_lemma_4_86_oneSidedBoundary`), the `honesided` of
  `Causal.Causality.ers_theorem_4_82_of_oneSidedBoundary`; global hyperbolicity and the openness of
  `S` are not used.
* **`T-loc-quasilinear-one-sided/2-theorem-4-82`** — `ers_theorem_4_82_of_slopeCone`.
* **`T-loc-quasilinear-one-sided/3-inextensible-piece`** — model-free:
  `Causal.Causality.inextensible_connectedComponentIn`, the maximal piece in `W` of a curve
  parametrised by a continuous time is inextensible in `W`; hoisted with its three companions,
  same names, into the ETT-layer `Causal.InextensiblePiece` (T-abs-hoist-inextensible-piece),
  which this module imports.
* **`T-loc-quasilinear-one-sided/4-minkowski-slab`** — `minkowskiSlab_ers_lemma_4_86`: Minkowski
  space, any slope `δ ≤ 1` (`slopeCone_leNested_staticCausality`), the slab `{|t| < 1}`,
  `S = {t = 0}`: the hypotheses hold and `∂U₁ ∖ closure S ≠ ∅`.

The cone `slopeCone E δ hδ` is the static causality of `Causal.Static` transported along
`(t, x) ↦ (t, δ • x)` (`p ≤ q ⟺ ‖q.2 − p.2‖ ≤ δ (q.1 − p.1)`; its curves include the graphs of
`δ`-Lipschitz maps). The causal step (`slopeLine_mem_of_curveNestedOn`): a line of slope `≤ δ`
through `z ∈ U₁` stays in `U₁` down to `{t = 0}` and meets `S` there, else its maximal piece misses
`S`. The topology (`exists_lipschitz_graph_of_cone`): from that cone property alone, `∂U₁` is the
graph of a `1/δ`-Lipschitz `f⁺`.

> Let $u_1 : U_1 \to \R$ be a GHD of given initial data posed on an open and connected subset $S$
> of $\{x^0=0\}$ for a  quasilinear wave equation of the form \eqref{QuasilinearEq}. Furthermore,
> assume that […] there exists a $\delta >0$ such that $\partial_0 + \sum_{i=1}^d \delta_i \partial_i$
> is timelike with respect to $g(u_1, du_1)$ for all $\delta_i \in \R$ with
> $\sum_{i=1}^d |\delta_i| < \delta$. […] Then the condition \eqref{PropertyBoundary} is satisfied.
> (`ghd_02_19.tex:1143–1150`)

> for every $p \in (\partial U_1 \setminus \partial S)$ there exists a neighbourhood $V$ of $p$
> together with a chart $\psi : V \to (-\varepsilon, \varepsilon)^{d+1}$, $\varepsilon >0$, and a
> continuous function $f : (-\varepsilon, \varepsilon)^d \to (-\varepsilon, \varepsilon)$ such that
> $\psi^{-1}(\mathrm{graph} f) = \partial U_1 \cap V$, all points below $\mathrm{graph} f$ in
> $(-\varepsilon, \varepsilon)^{d+1}$ are mapped into $U_1$ and all points above $\mathrm{graph} f$ in
> $(-\varepsilon, \varepsilon)^{d+1}$ are mapped into $\R^{d+1} \setminus U_1$. (4.83,
> `ghd_02_19.tex:1104`)

> This however gives rise to a past directed and past inextendible timelike curve in $U_1$
> starting at […] $q \in I^+_{g(u_1, du_1)}(S,U_1)$, which does not intersect $S$. This contradicts
> $S$ being a Cauchy hypersurface. (`ghd_02_19.tex:1162`)

## Hypothesis checklist

| paper | here |
|---|---|
| `u₁ : U₁ → ℝ` a GHD (`:814`): `U₁ ⊆ ℝ^{d+1}` open, globally hyperbolic for `g(u₁, du₁)` with Cauchy hypersurface `S` | ⚠ reading: `U₁ : Opens (ℝ × E)`, `g(u₁, du₁)` through its causality `C` (any `Causality (ℝ × E)`), `S` a Cauchy surface of `U₁` for `C` (`IsCauchySurfaceOn`, DEC-14; met at least once is what is used); ⚠ weakened: global hyperbolicity and `S ⊆ U₁` not used |
| `S` open and connected in `{x⁰ = 0}` | ⚠ weakened: `S ⊆ {t = 0}` only; `U₁ ∩ {t = 0} ⊆ S` follows |
| (4.87) | ⚠ reading: `CurveNestedOn (slopeCone E δ hδ) C U₁` or `… C.dual U₁` (`∂₀` future- or past-directed: the paper's "without loss of generality") |
| `ℝ^{d+1}`, the `ℓ¹` cone `Σ|δᵢ| < δ` | ⚠ weakened: `ℝ × E`, `E` any real normed space; `ℓ¹` is `E = WithLp 1 (Fin d → ℝ)`, the closed cone of any `δ' < δ` |
| (4.83) | ⚠ reading: in the identity chart (`LiesBelowGraphAt`), time-reversed where `t₀ < 0`, on a cylinder rather than the paper's cube (SCOPE); `f` is moreover `1/δ`-Lipschitz (`exists_lipschitz_graph_of_cone`) |

## SCOPE (disclosed)

* **(4.87) is read as a nesting** (binder `erslem:PropertyTimelike`): that the `δ`-Lipschitz
  graphs in `U₁` are causal curves of `C_g` is the smooth content of (4.87) (a closed cone of slope
  `δ' < δ` is `g`-timelike), not formalised (T-pkg-smooth-lorentz).
* **The chart** of (4.83) is the translation by `−p` (after `(t, x) ↦ (−t, x)` when `t₀ < 0`), `V`
  the cylinder `(t₀ − ε, t₀ + ε) × B_E(x₀, ρ)`. For `E = Fin d → ℝ` (sup norm) `B_E` is a cube of
  side `2ρ`; the paper's `(−ε, ε)^{d+1}` is its image under a linear rescaling of space, not
  formalised.
* **`∂S` is read as `closure S`**; OQ-41 (e) reads it as `closure S ∖ S` (`ers_lemma_4_86_edge`);
  for `S ⊆ U₁` the two give the same set (`frontier_diff_closure_eq_frontier_diff_edge`).
* **Witnesses.** On Minkowski space `ℝ^{1,d}` (`C = minkowski d`, any `δ ≤ 1`), the slab
  `U₁ = {|t| < 1}` with `S = {t = 0}` (Cauchy by `Causal.Flat.isCauchySurfaceOn_graph_of_saturated`):
  `∂U₁ = {|t| = 1} ≠ ∅` and the lemma applies (`minkowskiSlab_ers_lemma_4_86`). Not a
  quasilinear development: the library has no smooth `g(u, du)` (T-pkg-smooth-lorentz).
* Imports `Causal.Static`, `Causal.CausalIsoInvariance`, `Causal.LadderLocal`, `Causal.CauchyDual`,
  `Causal.InextensiblePiece` (section 2's lemmas, ETT layer) and, for the slab only (section 8),
  `Causal.Flat.LipschitzGraph` (closure adds `Causal.Minkowski`, `Causal.Flat.Form`, `.Achronal`,
  `.Cosmological`, `.Penrose`): no `Causal.Port.*`, `Causal.Model.*`, `Causal.CBG.*`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Metric

/-! ### 1. The static cone of slope `δ` -/

section SlopeCone

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The spatial scaling `(t, x) ↦ (t, δ • x)` of `ℝ × E`, `δ > 0`. -/
noncomputable def slopeScale (δ : ℝ) (hδ : 0 < δ) : (ℝ × E) ≃ₜ (ℝ × E) :=
  (Homeomorph.refl ℝ).prodCongr (Homeomorph.smulOfNeZero δ hδ.ne')

/-- **The static cone of slope `δ` around `∂₀`** on `ℝ × E`: the static causality of `E`
(`Causal.Static`, slope 1) transported along `(t, x) ↦ (t, δ • x)`. Its `≤_U` is joined by graphs
of `δ`-Lipschitz maps in `U` (`slopeCone_causalCurveOn_graph`); globally
`p ≤ q ⟺ ‖q.2 − p.2‖ ≤ δ (q.1 − p.1)` (`slopeCone_le_top_iff`). -/
noncomputable def slopeCone (δ : ℝ) (hδ : 0 < δ) : Causality (ℝ × E) :=
  (staticCausality E).transport (slopeScale E δ hδ)

variable {E}

theorem slopeScale_apply {δ : ℝ} (hδ : 0 < δ) (p : ℝ × E) :
    slopeScale E δ hδ p = (p.1, δ • p.2) := rfl

theorem slopeScale_symm_apply {δ : ℝ} (hδ : 0 < δ) (p : ℝ × E) :
    (slopeScale E δ hδ).symm p = (p.1, δ⁻¹ • p.2) := rfl

/-- **Sanity: the cone of slope `δ`.** Globally, `p ≤ q` iff `‖q.2 − p.2‖ ≤ δ (q.1 − p.1)`. -/
theorem slopeCone_le_top_iff {δ : ℝ} (hδ : 0 < δ) {p q : ℝ × E} :
    (slopeCone E δ hδ).le ⊤ p q ↔ ‖q.2 - p.2‖ ≤ δ * (q.1 - p.1) := by
  change (staticCausality E).le ((slopeScale E δ hδ).symm.opensCongr ⊤)
    ((slopeScale E δ hδ).symm p) ((slopeScale E δ hδ).symm q) ↔ _
  rw [opensCongr_top, staticCausality.le_top_iff, slopeScale_symm_apply, slopeScale_symm_apply,
    dist_smul₀, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hδ), dist_eq_norm, norm_sub_rev,
    inv_mul_le_iff₀ hδ]

/-- **The graphs of `δ`-Lipschitz maps are causal curves of the slope-`δ` cone.** -/
theorem slopeCone_causalCurveOn_graph {δ : ℝ} (hδ : 0 < δ) {W : Opens (ℝ × E)} {γ : ℝ → E}
    {a b : ℝ} (hγ : StaticCurve δ (W : Set (ℝ × E)) γ a b) :
    (slopeCone E δ hδ).CausalCurveOn W (fun τ => (τ, γ τ)) a b := by
  set e := slopeScale E δ hδ
  have h1 : StaticCurve 1 ((e.symm.opensCongr W : Opens (ℝ × E)) : Set (ℝ × E))
      (fun τ => δ⁻¹ • γ τ) a b := by
    refine ⟨fun τ hτ τ' hτ' => ?_, fun τ hτ => ?_⟩
    · rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hδ), one_mul,
        inv_mul_le_iff₀ hδ]
      exact hγ.lip τ hτ τ' hτ'
    · have : ((τ, δ⁻¹ • γ τ) : ℝ × E) = e.symm (τ, γ τ) := rfl
      rw [SetLike.mem_coe, this, mem_opensCongr]
      exact hγ.mem τ hτ
  have h2 := (isCausalIso_transport (staticCausality E) e).causalCurveOn_iff.1
    (staticCausality.causalCurveOn_graph h1)
  rw [opensCongr_symm_opensCongr] at h2
  have h3 : (e ∘ fun τ => ((τ, δ⁻¹ • γ τ) : ℝ × E)) = fun τ => (τ, γ τ) := by
    funext τ
    simp only [Function.comp, e, slopeScale_apply, smul_inv_smul₀ hδ.ne']
  rw [h3] at h2
  exact h2

/-- **The slope-`δ` cone, `δ ≤ 1`, is `≤`-nested in the static cone** (`Causal.Static`, slope 1):
a `δ`-Lipschitz graph is `1`-Lipschitz. -/
theorem slopeCone_leNested_staticCausality {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Causality.LeNested (slopeCone E δ hδ) (staticCausality E) := by
  intro U p q h
  set e := slopeScale E δ hδ
  change staticLe ((e.symm.opensCongr U : Opens (ℝ × E)) : Set (ℝ × E)) (e.symm p) (e.symm q)
    at h
  obtain ⟨hpq, γ, hγp, hγq, hγ⟩ := h
  rw [slopeScale_symm_apply] at hpq hγp hγq
  rw [slopeScale_symm_apply, slopeScale_symm_apply] at hγ
  refine ⟨hpq, fun τ => δ • γ τ, ?_, ?_, fun τ hτ τ' hτ' => ?_, fun τ hτ => ?_⟩
  · simp only [hγp, smul_inv_smul₀ hδ.ne']
  · simp only [hγq, smul_inv_smul₀ hδ.ne']
  · rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hδ]
    have := hγ.lip τ hτ τ' hτ'
    rw [one_mul] at this ⊢
    nlinarith [abs_nonneg (τ - τ'), dist_nonneg (x := γ τ) (y := γ τ')]
  · have hmem := hγ.mem τ hτ
    have : ((τ, γ τ) : ℝ × E) = e.symm (τ, δ • γ τ) := by
      rw [slopeScale_symm_apply, inv_smul_smul₀ hδ.ne']
    rw [SetLike.mem_coe, this, mem_opensCongr] at hmem
    exact hmem

end SlopeCone

/-! ### 2. A model-free lemma: a maximal piece of a time-parametrised curve is inextensible

Hoisted into the ETT layer, same full names (T-abs-hoist-inextensible-piece):
`Causality.futureInextensible_of_isLUB_notMem`, `Causality.pastInextensible_of_isGLB_notMem`,
`Causality.inextensible_connectedComponentIn` and
`Causality.IsCauchySurfaceOn.exists_mem_connectedComponentIn` are in `Causal.InextensiblePiece`,
which this module imports; section 3 uses the last. -/

/-! ### 3. Lines of slope at most `δ` -/

section Lines

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The line of `ℝ × E` through `z` with spatial velocity `v`, parametrised by time. -/
def slopeLine (z : ℝ × E) (v : E) (τ : ℝ) : ℝ × E := (τ, z.2 + (τ - z.1) • v)

variable {δ : ℝ} (hδ : 0 < δ) {C : Causality (ℝ × E)} {U : Opens (ℝ × E)} {S : Set (ℝ × E)}

include hδ in
/-- **The causal step of ERS Lemma 4.86** ((4.87) read as a nesting). If the slope-`δ` cone is
curve-nested in `C` on `U` and `S ⊆ {t = 0}` is a Cauchy surface of `U` for `C`, every line of
slope `≤ δ` through `z ∈ U` stays in `U` between `z` and `{t = 0}`, and meets `S` there: its
maximal piece in `U` is an inextensible causal curve of `U` for `C`
(`Causality.inextensible_connectedComponentIn`), so it meets `S`, at time `0`; the piece is an
interval containing `z.1` and `0`. -/
theorem slopeLine_mem_of_curveNestedOn (hnest : Causality.CurveNestedOn (slopeCone E δ hδ) C U)
    (hS : C.IsCauchySurfaceOn U S) (hS0 : ∀ q ∈ S, q.1 = 0) {z : ℝ × E} (hz : z ∈ U) {v : E}
    (hv : ‖v‖ ≤ δ) : (∀ τ ∈ uIcc 0 z.1, slopeLine z v τ ∈ U) ∧ slopeLine z v 0 ∈ S := by
  set ℓ := slopeLine z v with hℓdef
  have hℓ : Continuous ℓ :=
    continuous_id.prodMk (continuous_const.add ((continuous_id.sub continuous_const).smul
      continuous_const))
  have hTℓ : ∀ τ, (ℓ τ).1 = τ := fun τ => rfl
  have hcurve : ∀ a b, a ≤ b → (∀ τ ∈ Icc a b, ℓ τ ∈ U) → C.CausalCurveOn U ℓ a b := by
    intro a b _ hmem
    apply hnest
    refine slopeCone_causalCurveOn_graph hδ (γ := fun τ => z.2 + (τ - z.1) • v)
      ⟨fun τ _ τ' _ => ?_, fun τ hτ => hmem τ hτ⟩
    rw [dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul, Real.norm_eq_abs,
      show τ - z.1 - (τ' - z.1) = τ - τ' by ring, mul_comm]
    exact mul_le_mul_of_nonneg_right hv (abs_nonneg _)
  have hz' : ℓ z.1 ∈ U := by
    have : ℓ z.1 = z := by simp [hℓdef, slopeLine]
    rw [this]; exact hz
  obtain ⟨s, hs, hsS⟩ := hS.exists_mem_connectedComponentIn hℓ continuous_fst hTℓ hcurve hz'
  have hs0 : s = 0 := by have := hS0 _ hsS; rwa [hTℓ] at this
  subst hs0
  have hIc := (isPreconnected_connectedComponentIn (F := ℓ ⁻¹' (U : Set (ℝ × E)))
    (x := z.1)).ordConnected
  refine ⟨fun τ hτ => ?_, hsS⟩
  exact connectedComponentIn_subset (ℓ ⁻¹' (U : Set (ℝ × E))) z.1
    (hIc.uIcc_subset hs (mem_connectedComponentIn hz') hτ)

include hδ in
/-- **The double cone**: with `z ∈ U`, every `z'` between `{t = 0}` and `z` in time with
`‖z'.2 − z.2‖ ≤ δ |z.1 − z'.1|` is in `U` (the line from `z` through `z'`). -/
theorem mem_of_cone_of_curveNestedOn (hnest : Causality.CurveNestedOn (slopeCone E δ hδ) C U)
    (hS : C.IsCauchySurfaceOn U S) (hS0 : ∀ q ∈ S, q.1 = 0) {z z' : ℝ × E} (hz : z ∈ U)
    (hz' : z'.1 ∈ uIcc 0 z.1) (hd : ‖z'.2 - z.2‖ ≤ δ * |z.1 - z'.1|) : z' ∈ U := by
  by_cases h : z'.1 = z.1
  · have h2 : z'.2 = z.2 := by
      have : ‖z'.2 - z.2‖ ≤ 0 := by simpa [h] using hd
      exact sub_eq_zero.1 (norm_le_zero_iff.1 this)
    have : z' = z := Prod.ext h h2
    exact this ▸ hz
  · have hne : z'.1 - z.1 ≠ 0 := sub_ne_zero.2 h
    set v := (z'.1 - z.1)⁻¹ • (z'.2 - z.2) with hvdef
    have hv : ‖v‖ ≤ δ := by
      rw [hvdef, norm_smul, norm_inv, Real.norm_eq_abs, inv_mul_le_iff₀ (abs_pos.2 hne),
        abs_sub_comm, mul_comm]
      exact hd
    have := (slopeLine_mem_of_curveNestedOn hδ hnest hS hS0 hz hv).1 z'.1 hz'
    have heq : slopeLine z v z'.1 = z' := by
      simp only [slopeLine, hvdef, smul_smul, mul_inv_cancel₀ hne, one_smul, add_sub_cancel]
    rwa [heq] at this

include hδ in
/-- **Every point of `U` projects vertically into `S`** (the line of velocity `0`). In particular
`U ∩ {t = 0} ⊆ S`. -/
theorem proj_mem_of_curveNestedOn (hnest : Causality.CurveNestedOn (slopeCone E δ hδ) C U)
    (hS : C.IsCauchySurfaceOn U S) (hS0 : ∀ q ∈ S, q.1 = 0) {z : ℝ × E} (hz : z ∈ U) :
    ((0 : ℝ), z.2) ∈ S := by
  have := (slopeLine_mem_of_curveNestedOn hδ hnest hS hS0 hz (v := 0)
    (by rw [norm_zero]; exact hδ.le)).2
  simpa [slopeLine] using this

end Lines

/-! ### 4. The graph, from the cone property alone -/

section Graph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable (E) in
/-- Time reversal `(t, x) ↦ (−t, x)` (`Causal.flipT`) as a homeomorphism, an involution. -/
def flipTHomeomorph : (ℝ × E) ≃ₜ (ℝ × E) where
  toFun := flipT
  invFun := flipT
  left_inv _ := flipT_flipT
  right_inv _ := flipT_flipT
  continuous_toFun := continuous_flipT
  continuous_invFun := continuous_flipT

omit [NormedSpace ℝ E] in
theorem flipT_mem_frontier_preimage {U : Set (ℝ × E)} {p : ℝ × E} (hp : p ∈ frontier U) :
    flipT p ∈ frontier (flipT ⁻¹' U) := by
  have h := (flipTHomeomorph E).preimage_frontier U
  have : (flipTHomeomorph E : (ℝ × E) → (ℝ × E)) = flipT := rfl
  rw [this] at h
  rw [← h, mem_preimage, flipT_flipT]
  exact hp

/-- **(4.83) at `p` in the identity chart.** A cylinder `(p.1 − ε, p.1 + ε) × ball p.2 ρ` and `f`
continuous on the ball, with values in `(p.1 − ε, p.1 + ε)`, through `p`: inside the cylinder `U`
is the part below the graph of `f` (so the part above misses `U`) and `frontier U` is the graph. -/
def LiesBelowGraphAt (U : Set (ℝ × E)) (p : ℝ × E) : Prop :=
  ∃ ε > 0, ∃ ρ > 0, ∃ f : E → ℝ, ContinuousOn f (ball p.2 ρ) ∧ f p.2 = p.1 ∧
    (∀ y ∈ ball p.2 ρ, |f y - p.1| < ε) ∧
    ∀ z : ℝ × E, z.2 ∈ ball p.2 ρ → |z.1 - p.1| < ε →
      (z ∈ U ↔ z.1 < f z.2) ∧ (z ∈ frontier U ↔ z.1 = f z.2)

/-- **(4.83) at `p`**: `U` below a graph in the identity chart, or in the time-reversed chart
`(t, x) ↦ (−t, x)` (above a graph in the identity chart). -/
def BoundaryGraphAt (U : Set (ℝ × E)) (p : ℝ × E) : Prop :=
  LiesBelowGraphAt U p ∨ LiesBelowGraphAt (flipT ⁻¹' U) (flipT p)

/-- **(4.83) off `B`**: at every boundary point of `U` outside `B`. With `B = closure S` it is
ERS's condition at `∂U₁ ∖ ∂S` with `∂S` read as `closure S`; OQ-41 (e)'s `closure S ∖ S` is
`ers_lemma_4_86_edge`. -/
def BoundaryGraph (U : Set (ℝ × E)) (B : Set (ℝ × E)) : Prop :=
  ∀ p ∈ frontier U \ B, BoundaryGraphAt U p

omit [NormedSpace ℝ E] in
/-- **The graph `f⁺` of ERS's proof, `1/δ`-Lipschitz**, from the cone property alone: `f⁺(y)` is
the supremum of the times `τ ≥ 0` with `(τ, y) ∈ U`; the cone bounds it by the time of `p` plus
`‖y − p.2‖/δ` (else `p ∈ U`), the vertical segment below `p` is in `U` (`p ∈ closure U`), and the
cone moves `f⁺` by at most `‖y − y'‖/δ`. -/
theorem exists_lipschitz_graph_of_cone {δ : ℝ} (hδ : 0 < δ) {U : Set (ℝ × E)} (hU : IsOpen U)
    (hcone : ∀ z ∈ U, ∀ z' : ℝ × E, 0 ≤ z'.1 → z'.1 ≤ z.1 →
      ‖z'.2 - z.2‖ ≤ δ * (z.1 - z'.1) → z' ∈ U)
    {p : ℝ × E} (hp : p ∈ frontier U) (hp0 : 0 < p.1) :
    ∃ ε > 0, ∃ ρ > 0, ∃ f : E → ℝ,
      (∀ y ∈ ball p.2 ρ, ∀ y' ∈ ball p.2 ρ, |f y - f y'| ≤ ‖y - y'‖ / δ) ∧ f p.2 = p.1 ∧
      (∀ y ∈ ball p.2 ρ, |f y - p.1| < ε) ∧
      ∀ z : ℝ × E, z.2 ∈ ball p.2 ρ → |z.1 - p.1| < ε →
        (z ∈ U ↔ z.1 < f z.2) ∧ (z ∈ frontier U ↔ z.1 = f z.2) := by
  rw [hU.frontier_eq] at hp
  obtain ⟨hpcl, hpU⟩ := hp
  -- the vertical fibres above `{t = 0}` and their suprema
  set A : E → Set ℝ := fun y => {τ | 0 ≤ τ ∧ (τ, y) ∈ U} with hAdef
  set F : E → ℝ := fun y => sSup (A y) with hFdef
  have hA_bdd : ∀ y, ∀ τ ∈ A y, τ < p.1 + ‖y - p.2‖ / δ := by
    intro y τ hτ
    by_contra h'
    have h := not_lt.1 h'
    have hq : 0 ≤ ‖y - p.2‖ / δ := div_nonneg (norm_nonneg _) hδ.le
    refine hpU (hcone (τ, y) hτ.2 p hp0.le (by simp only; linarith) ?_)
    simp only
    rw [norm_sub_rev]
    have h1 : ‖y - p.2‖ / δ ≤ τ - p.1 := by linarith
    calc ‖y - p.2‖ = δ * (‖y - p.2‖ / δ) := by field_simp
      _ ≤ δ * (τ - p.1) := mul_le_mul_of_nonneg_left h1 hδ.le
  have hbdd : ∀ y, BddAbove (A y) := fun y =>
    ⟨p.1 + ‖y - p.2‖ / δ, fun τ hτ => (hA_bdd y τ hτ).le⟩
  have hF0 : ∀ y, 0 ≤ F y := fun y => Real.sSup_nonneg fun τ hτ => hτ.1
  -- the vertical segment below `p` lies in `U`
  have hvert : ∀ t, 0 ≤ t → t < p.1 → (t, p.2) ∈ U := by
    intro t ht0 htp
    set r := δ * (p.1 - t) / (δ + 1) with hrdef
    have hr : 0 < r := div_pos (mul_pos hδ (by linarith)) (by linarith)
    have hr' : r * (δ + 1) = δ * (p.1 - t) := by rw [hrdef]; field_simp
    have hrt : r < p.1 - t := by
      by_contra hc'
      have hc := not_lt.1 hc'
      nlinarith [mul_le_mul_of_nonneg_left hc hδ.le]
    obtain ⟨b, hb, hdist⟩ := Metric.mem_closure_iff.1 hpcl r hr
    rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, dist_eq_norm, abs_lt] at hdist
    obtain ⟨⟨h1, h2⟩, h3⟩ := hdist
    refine hcone b hb (t, p.2) ht0 (by simp only; linarith) ?_
    simp only
    nlinarith [mul_pos hδ (by linarith : 0 < b.1 - p.1 + r)]
  -- the fibre over `y` contains `[0, p.1 − ‖y − p.2‖/δ)`
  have hA_low : ∀ y τ, 0 ≤ τ → τ < p.1 - ‖y - p.2‖ / δ → τ ∈ A y := by
    intro y τ hτ0 hτ
    have hq : 0 ≤ ‖y - p.2‖ / δ := div_nonneg (norm_nonneg _) hδ.le
    set t := (τ + ‖y - p.2‖ / δ + p.1) / 2 with htdef
    have ht := hvert t (by linarith) (by linarith)
    refine ⟨hτ0, hcone _ ht (τ, y) hτ0 (by simp only; linarith) ?_⟩
    simp only
    have h1 : ‖y - p.2‖ / δ ≤ t - τ := by linarith
    calc ‖y - p.2‖ = δ * (‖y - p.2‖ / δ) := by field_simp
      _ ≤ δ * (t - τ) := mul_le_mul_of_nonneg_left h1 hδ.le
  -- fibres are closed downwards, and move by at most `‖y' − y‖/δ`
  have hA_down : ∀ y τ τ', τ ∈ A y → 0 ≤ τ' → τ' ≤ τ → τ' ∈ A y := by
    intro y τ τ' hτ h0 hle
    refine ⟨h0, hcone _ hτ.2 (τ', y) h0 hle ?_⟩
    simp only [sub_self, norm_zero]
    nlinarith
  have hA_shift : ∀ y y' τ, τ ∈ A y → ‖y' - y‖ / δ ≤ τ → τ - ‖y' - y‖ / δ ∈ A y' := by
    intro y y' τ hτ hle
    have hq : 0 ≤ ‖y' - y‖ / δ := div_nonneg (norm_nonneg _) hδ.le
    refine ⟨by linarith, hcone _ hτ.2 _ (by simp only; linarith) (by simp only; linarith) ?_⟩
    simp only
    rw [show τ - (τ - ‖y' - y‖ / δ) = ‖y' - y‖ / δ by ring]
    exact le_of_eq (by field_simp)
  set B := ball p.2 (δ * p.1) with hBdef
  have hAne : ∀ y ∈ B, (0 : ℝ) ∈ A y := by
    intro y hy
    refine hA_low y 0 le_rfl ?_
    rw [hBdef, mem_ball, dist_eq_norm] at hy
    rw [sub_pos, div_lt_iff₀ hδ]
    linarith [mul_comm δ p.1]
  have hLip : ∀ y ∈ B, ∀ y', F y ≤ F y' + ‖y' - y‖ / δ := by
    intro y hy y'
    refine csSup_le ⟨0, hAne y hy⟩ fun τ hτ => ?_
    by_cases h : ‖y' - y‖ / δ ≤ τ
    · have := le_csSup (hbdd y') (hA_shift y y' τ hτ h)
      linarith
    · linarith [hF0 y']
  have hFabs : ∀ y ∈ B, ∀ y' ∈ B, |F y - F y'| ≤ ‖y - y'‖ / δ := by
    intro y hy y' hy'
    have h1 := hLip y hy y'
    have h2 := hLip y' hy' y
    rw [norm_sub_rev] at h1
    rw [abs_le]
    constructor <;> linarith
  have hpB : p.2 ∈ B := mem_ball_self (mul_pos hδ hp0)
  have hFp : F p.2 = p.1 := by
    apply le_antisymm
    · refine csSup_le ⟨0, hAne p.2 hpB⟩ fun τ hτ => ?_
      have := hA_bdd p.2 τ hτ
      rw [sub_self, norm_zero, zero_div, add_zero] at this
      exact this.le
    · refine le_of_forall_lt fun c hc => ?_
      have hm : max c 0 < p.1 := max_lt hc hp0
      have hτA : (max c 0 + p.1) / 2 ∈ A p.2 := hA_low p.2 _
        (by linarith [le_max_right c 0]) (by rw [sub_self, norm_zero, zero_div, sub_zero]; linarith)
      exact lt_of_lt_of_le (by linarith [le_max_left c 0]) (le_csSup (hbdd _) hτA)
  -- `U` is the part below the graph of `F`
  have hiff : ∀ z : ℝ × E, z.2 ∈ B → 0 ≤ z.1 → (z ∈ U ↔ z.1 < F z.2) := by
    intro z hzB hz0
    constructor
    · intro hz
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU z hz
      have hmem : (z.1 + r / 2, z.2) ∈ U := hball (by
        rw [mem_ball, Prod.dist_eq, Real.dist_eq, dist_self,
          show z.1 + r / 2 - z.1 = r / 2 by ring, abs_of_pos (by linarith),
          max_eq_left (by linarith)]
        linarith)
      have := le_csSup (hbdd z.2) (⟨by linarith, hmem⟩ : z.1 + r / 2 ∈ A z.2)
      linarith
    · intro hlt
      obtain ⟨τ, hτ, hzτ⟩ := exists_lt_of_lt_csSup ⟨0, hAne z.2 hzB⟩ hlt
      exact (hA_down z.2 τ z.1 hτ hz0 hzτ.le).2
  -- and its frontier is the graph
  have hfr : ∀ z : ℝ × E, z.2 ∈ B → 0 < z.1 → (z ∈ closure U \ U ↔ z.1 = F z.2) := by
    intro z hzB hz0
    constructor
    · rintro ⟨hcl, hnot⟩
      have hge : F z.2 ≤ z.1 := not_lt.1 fun h => hnot ((hiff z hzB hz0.le).2 h)
      by_contra hne
      have hgt : F z.2 < z.1 := lt_of_le_of_ne hge (Ne.symm hne)
      obtain ⟨r₀, hr₀, hball₀⟩ := Metric.isOpen_iff.1 isOpen_ball z.2 hzB
      set g := z.1 - F z.2 with hgdef
      have hg : 0 < g := by linarith
      set r := min r₀ (min (g / 2) (δ * g / 2)) with hrdef
      have hr : 0 < r := lt_min hr₀ (lt_min (by linarith) (by positivity))
      have hr1 : r ≤ g / 2 := (min_le_right _ _).trans (min_le_left _ _)
      have hr2 : r ≤ δ * g / 2 := (min_le_right _ _).trans (min_le_right _ _)
      have hrδ : r / δ ≤ g / 2 := by rw [div_le_iff₀ hδ]; linarith
      obtain ⟨w, hw, hdist⟩ := Metric.mem_closure_iff.1 hcl r hr
      rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, abs_lt] at hdist
      obtain ⟨⟨h1, h2⟩, h3⟩ := hdist
      have hwB : w.2 ∈ B := hball₀ (by
        rw [mem_ball, dist_comm]; exact lt_of_lt_of_le h3 (min_le_left _ _))
      have hd : ‖z.2 - w.2‖ / δ < r / δ := by
        rw [← dist_eq_norm]; exact div_lt_div_of_pos_right h3 hδ
      have hFw := hLip w.2 hwB z.2
      have hw0 : 0 ≤ w.1 := by linarith [hF0 z.2]
      have := (hiff w hwB hw0).1 hw
      linarith
    · intro heq
      refine ⟨Metric.mem_closure_iff.2 fun ε hε => ?_, fun hz => ?_⟩
      · set m := min (ε / 2) (z.1 / 2) with hmdef
        have hm : 0 < m := lt_min (by linarith) (by linarith)
        have hm1 : m ≤ ε / 2 := min_le_left _ _
        have hm2 : m ≤ z.1 / 2 := min_le_right _ _
        refine ⟨(z.1 - m, z.2), (hiff (z.1 - m, z.2) hzB (by simp only; linarith)).2
          (by simp only; linarith), ?_⟩
        rw [Prod.dist_eq, Real.dist_eq, dist_self, show z.1 - (z.1 - m) = m by ring,
          abs_of_pos hm, max_eq_left hm.le]
        linarith
      · have := (hiff z hzB hz0.le).1 hz
        linarith
  -- the cylinder `(p.1 − p.1/2, p.1 + p.1/2) × ball p.2 (δ p.1/2)`
  have hsub : ball p.2 (δ * (p.1 / 2)) ⊆ B := ball_subset_ball (by nlinarith)
  refine ⟨p.1 / 2, by positivity, δ * (p.1 / 2), mul_pos hδ (by positivity), F,
    fun y hy y' hy' => hFabs y (hsub hy) y' (hsub hy'), hFp, fun y hy => ?_, fun z hz hz1 => ?_⟩
  · have := hFabs y (hsub hy) p.2 hpB
    rw [hFp] at this
    rw [mem_ball, dist_eq_norm] at hy
    calc |F y - p.1| ≤ ‖y - p.2‖ / δ := this
      _ < p.1 / 2 := by rw [div_lt_iff₀ hδ]; linarith [mul_comm δ (p.1 / 2)]
  · rw [abs_lt] at hz1
    have hz0 : 0 < z.1 := by linarith [hz1.1]
    refine ⟨hiff z (hsub hz) hz0.le, ?_⟩
    rw [hU.frontier_eq]
    exact hfr z (hsub hz) hz0

omit [NormedSpace ℝ E] in
/-- **The graph from the cone property**: an open `U` containing, with each of its points `z`
above `{t = 0}`, the truncated past cone of slope `δ` of `z` down to `{t = 0}`, lies below a
graph at each of its boundary points above `{t = 0}`. No causality is involved. -/
theorem liesBelowGraphAt_of_cone {δ : ℝ} (hδ : 0 < δ) {U : Set (ℝ × E)} (hU : IsOpen U)
    (hcone : ∀ z ∈ U, ∀ z' : ℝ × E, 0 ≤ z'.1 → z'.1 ≤ z.1 →
      ‖z'.2 - z.2‖ ≤ δ * (z.1 - z'.1) → z' ∈ U)
    {p : ℝ × E} (hp : p ∈ frontier U) (hp0 : 0 < p.1) : LiesBelowGraphAt U p := by
  obtain ⟨ε, hε, ρ, hρ, f, hlip, hfp, hfε, hgraph⟩ :=
    exists_lipschitz_graph_of_cone hδ hU hcone hp hp0
  refine ⟨ε, hε, ρ, hρ, f, ?_, hfp, hfε, hgraph⟩
  rw [Metric.continuousOn_iff]
  intro y hy η hη
  refine ⟨δ * η, mul_pos hδ hη, fun y' hy' hd => ?_⟩
  rw [Real.dist_eq]
  rw [dist_eq_norm] at hd
  calc |f y' - f y| ≤ ‖y' - y‖ / δ := hlip y' hy' y hy
    _ < η := by rw [div_lt_iff₀ hδ]; linarith [mul_comm η δ]

/-- **(4.83) gives one-sidedness** (the layer-3 step that `Causal.Causality.OneSidedAt`'s
docstring leaves out): below a continuous graph over a ball, `V ∩ U` is the image of
`ball × (0, 1)`, preconnected, in arbitrarily small cylinders `V`. -/
theorem LiesBelowGraphAt.oneSidedAt {U : Set (ℝ × E)} {p : ℝ × E} (h : LiesBelowGraphAt U p) :
    Causality.OneSidedAt U p := by
  obtain ⟨ε, hε, ρ, hρ, f, hfc, hfp, -, hgraph⟩ := h
  intro N hN
  obtain ⟨r, hr, hballN⟩ := Metric.mem_nhds_iff.1 hN
  set ε' := min ε r with hε'def
  have hε' : 0 < ε' := lt_min hε hr
  have hcont : ContinuousAt f p.2 := hfc.continuousAt (ball_mem_nhds p.2 hρ)
  obtain ⟨η, hη, hfη⟩ := Metric.continuousAt_iff.1 hcont ε' hε'
  set ρ' := min (min ρ r) η with hρ'def
  have hρ' : 0 < ρ' := lt_min (lt_min hρ hr) hη
  have hρρ : ρ' ≤ ρ := (min_le_left _ _).trans (min_le_left _ _)
  set V : Set (ℝ × E) := {z | |z.1 - p.1| < ε' ∧ z.2 ∈ ball p.2 ρ'} with hVdef
  have hVsub : ∀ z ∈ V, z.2 ∈ ball p.2 ρ ∧ |z.1 - p.1| < ε := fun z hz =>
    ⟨ball_subset_ball hρρ hz.2, lt_of_lt_of_le hz.1 (min_le_left _ _)⟩
  have hfV : ∀ y ∈ ball p.2 ρ', p.1 - ε' < f y ∧ f y < p.1 + ε' := by
    intro y hy
    have := hfη (lt_of_lt_of_le (mem_ball.1 hy) (min_le_right _ _))
    rw [Real.dist_eq, hfp, abs_lt] at this
    constructor <;> linarith [this.1, this.2]
  refine ⟨V, ?_, ?_, ?_⟩
  · refine Metric.mem_nhds_iff.2 ⟨min ε' ρ', lt_min hε' hρ', fun z hz => ?_⟩
    rw [mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq] at hz
    exact ⟨lt_of_lt_of_le hz.1 (min_le_left _ _),
      mem_ball.2 (lt_of_lt_of_le hz.2 (min_le_right _ _))⟩
  · intro z hz
    apply hballN
    rw [mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq]
    exact ⟨lt_of_lt_of_le hz.1 (min_le_right _ _),
      lt_of_lt_of_le (mem_ball.1 hz.2) ((min_le_left _ _).trans (min_le_right _ _))⟩
  · -- `V ∩ U` is the region between `t = p.1 − ε'` and the graph: an image of `ball × (0, 1)`
    set g : E × ℝ → ℝ × E := fun q => (p.1 - ε' + q.2 * (f q.1 - (p.1 - ε')), q.1) with hgdef
    have hgc : ContinuousOn g (ball p.2 ρ' ×ˢ Ioo 0 1) := by
      have hf' : ContinuousOn (fun q : E × ℝ => f q.1) (ball p.2 ρ' ×ˢ Ioo 0 1) :=
        (hfc.mono (ball_subset_ball hρρ)).comp continuousOn_fst (fun q hq => hq.1)
      exact (continuousOn_const.add (continuousOn_snd.mul (hf'.sub continuousOn_const))).prodMk
        continuousOn_fst
    have himg : V ∩ U = g '' (ball p.2 ρ' ×ˢ Ioo 0 1) := by
      ext z
      constructor
      · rintro ⟨hzV, hzU⟩
        have hlt := ((hgraph z (hVsub z hzV).1 (hVsub z hzV).2).1).1 hzU
        have hz1 := abs_lt.1 hzV.1
        have hfz := hfV z.2 hzV.2
        have hD : 0 < f z.2 - (p.1 - ε') := by linarith
        refine ⟨(z.2, (z.1 - (p.1 - ε')) / (f z.2 - (p.1 - ε'))), ⟨hzV.2, ?_, ?_⟩, ?_⟩
        · exact div_pos (by linarith) hD
        · rw [div_lt_one hD]; linarith
        · simp only [hgdef]
          rw [div_mul_cancel₀ _ hD.ne']
          ext <;> simp
      · rintro ⟨⟨y, s⟩, ⟨hy, hs0, hs1⟩, rfl⟩
        have hfy := hfV y hy
        have hD : 0 < f y - (p.1 - ε') := by linarith
        have hlow : 0 < s * (f y - (p.1 - ε')) := mul_pos hs0 hD
        have hhigh : s * (f y - (p.1 - ε')) < f y - (p.1 - ε') := by nlinarith
        have hzV : g (y, s) ∈ V := ⟨by
          simp only [hgdef]
          rw [abs_lt]; constructor <;> linarith, hy⟩
        refine ⟨hzV, ((hgraph _ (hVsub _ hzV).1 (hVsub _ hzV).2).1).2 ?_⟩
        simp only [hgdef]
        linarith
    rw [himg]
    exact ((convex_ball p.2 ρ').isPreconnected.prod isPreconnected_Ioo).image g hgc

omit [NormedSpace ℝ E] in
/-- One-sidedness is invariant under the time reversal `flipT`. -/
theorem oneSidedAt_of_flipT {U : Set (ℝ × E)} {p : ℝ × E}
    (h : Causality.OneSidedAt (flipT ⁻¹' U) (flipT p)) : Causality.OneSidedAt U p := by
  intro N hN
  have hN' : flipT ⁻¹' N ∈ 𝓝 (flipT p) := by
    apply continuous_flipT.continuousAt.preimage_mem_nhds
    rw [flipT_flipT]; exact hN
  obtain ⟨V, hV, hVN, hconn⟩ := h _ hN'
  refine ⟨flipT ⁻¹' V, continuous_flipT.continuousAt.preimage_mem_nhds hV, fun z hz => ?_, ?_⟩
  · have := hVN hz
    rwa [mem_preimage, flipT_flipT] at this
  · have : flipT ⁻¹' V ∩ U = flipT '' (V ∩ flipT ⁻¹' U) := by
      ext z
      constructor
      · rintro ⟨hzV, hzU⟩
        exact ⟨flipT z, ⟨hzV, by rwa [mem_preimage, flipT_flipT]⟩, flipT_flipT⟩
      · rintro ⟨w, ⟨hwV, hwU⟩, rfl⟩
        exact ⟨by rwa [mem_preimage, flipT_flipT], hwU⟩
    rw [this]
    exact hconn.image _ continuous_flipT.continuousOn

/-- **(4.83) gives `OneSidedBoundary`.** -/
theorem BoundaryGraph.oneSidedBoundary {U : Opens (ℝ × E)} {B : Set (ℝ × E)}
    (h : BoundaryGraph (U : Set (ℝ × E)) B) : Causality.OneSidedBoundary U B := fun p hp =>
  (h p hp).elim LiesBelowGraphAt.oneSidedAt fun h' => oneSidedAt_of_flipT h'.oneSidedAt

end Graph

/-! ### 5. ERS Lemma 4.86 -/

section Lemma486

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {δ : ℝ} (hδ : 0 < δ) {C : Causality (ℝ × E)} {U₁ : Opens (ℝ × E)} {S : Set (ℝ × E)}

include hδ in
/-- **ERS Lemma 4.86, `∂₀` future-directed.** At `p ∈ ∂U₁ ∖ closure S`: `p.1 ≠ 0` (a boundary point
on `{t = 0}` is a limit of vertical projections of points of `U₁`, which lie in `S`); above
`{t = 0}` the double cone gives `liesBelowGraphAt_of_cone`, below it the same after `flipT`. -/
theorem ers_lemma_4_86_future (hnest : Causality.CurveNestedOn (slopeCone E δ hδ) C U₁)
    (hS : C.IsCauchySurfaceOn U₁ S) (hS0 : ∀ q ∈ S, q.1 = 0) :
    BoundaryGraph (U₁ : Set (ℝ × E)) (closure S) := by
  rintro p ⟨hp, hpS⟩
  have hU : IsOpen (U₁ : Set (ℝ × E)) := U₁.isOpen
  rcases lt_trichotomy p.1 0 with hneg | hzero | hpos
  · -- below `{t = 0}`: `U₁` lies above the graph, the time-reversed chart
    right
    refine liesBelowGraphAt_of_cone hδ (hU.preimage continuous_flipT) ?_
      (flipT_mem_frontier_preimage hp) (by rw [flipT_fst]; linarith)
    intro w hw w' h0 hle hd
    show flipT w' ∈ U₁
    refine mem_of_cone_of_curveNestedOn hδ hnest hS hS0 hw (z' := flipT w') ?_ ?_
    · rw [flipT_fst, flipT_fst, uIcc_of_ge (by linarith : -w.1 ≤ 0)]
      exact ⟨by linarith, by linarith⟩
    · rw [flipT_fst, flipT_fst, flipT_snd, flipT_snd,
        show -w.1 - -w'.1 = -(w.1 - w'.1) by ring, abs_neg, abs_of_nonneg (by linarith)]
      exact hd
  · -- on `{t = 0}`: impossible off `closure S`, every point of `U₁` projects vertically into `S`
    exfalso
    apply hpS
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨b, hb, hdist⟩ := Metric.mem_closure_iff.1 (frontier_subset_closure hp) ε hε
    refine ⟨((0 : ℝ), b.2), proj_mem_of_curveNestedOn hδ hnest hS hS0 hb, ?_⟩
    calc dist p ((0 : ℝ), b.2) = max (dist p.1 0) (dist p.2 b.2) := Prod.dist_eq
      _ = dist p.2 b.2 := by rw [hzero, dist_self, max_eq_right dist_nonneg]
      _ ≤ dist p b := by rw [Prod.dist_eq]; exact le_max_right _ _
      _ < ε := hdist
  · -- above `{t = 0}`: `U₁` lies below the graph
    left
    refine liesBelowGraphAt_of_cone hδ hU (fun z hz z' h0 hle hd => ?_) hp hpos
    refine mem_of_cone_of_curveNestedOn hδ hnest hS hS0 hz ?_ ?_
    · rw [uIcc_of_le (h0.trans hle)]; exact ⟨h0, hle⟩
    · rw [abs_of_nonneg (by linarith)]; exact hd

include hδ in
/-- **ERS Lemma 4.86** (`erslem:PropertyTimelike`, `ghd_02_19.tex:1143`), (4.87) read as the
slope-`δ` cone curve-nested in `C` on `U₁`, `∂₀` future- or past-directed (`C.dual`): (4.83) holds
at every point of `∂U₁ ∖ closure S`. -/
theorem ers_lemma_4_86
    (hnest : Causality.CurveNestedOn (slopeCone E δ hδ) C U₁ ∨
      Causality.CurveNestedOn (slopeCone E δ hδ) C.dual U₁)
    (hS : C.IsCauchySurfaceOn U₁ S) (hS0 : ∀ q ∈ S, q.1 = 0) :
    BoundaryGraph (U₁ : Set (ℝ × E)) (closure S) := by
  rcases hnest with h | h
  · exact ers_lemma_4_86_future hδ h hS hS0
  · exact ers_lemma_4_86_future hδ h (Causality.dual_isCauchySurfaceOn.2 hS) hS0

include hδ in
/-- **ERS Lemma 4.86, topological content**: `OneSidedBoundary U₁ (closure S)`, the `honesided` of
`Causal.Causality.ers_theorem_4_82_of_oneSidedBoundary`. -/
theorem ers_lemma_4_86_oneSidedBoundary
    (hnest : Causality.CurveNestedOn (slopeCone E δ hδ) C U₁ ∨
      Causality.CurveNestedOn (slopeCone E δ hδ) C.dual U₁)
    (hS : C.IsCauchySurfaceOn U₁ S) (hS0 : ∀ q ∈ S, q.1 = 0) :
    Causality.OneSidedBoundary U₁ (closure S) :=
  (ers_lemma_4_86 hδ hnest hS hS0).oneSidedBoundary

omit [NormedSpace ℝ E] in
/-- **OQ-41 (e) is immaterial here**: when `S ⊆ U₁` (a GHD contains its initial surface), removing
`closure S` or the edge `closure S ∖ S` from `∂U₁` leaves the same set, `U₁` being open. -/
theorem frontier_diff_closure_eq_frontier_diff_edge (hSU : S ⊆ U₁) :
    frontier (U₁ : Set (ℝ × E)) \ closure S = frontier (U₁ : Set (ℝ × E)) \ (closure S \ S) := by
  ext p
  constructor
  · rintro ⟨hp, hpS⟩
    exact ⟨hp, fun h => hpS h.1⟩
  · rintro ⟨hp, hpS⟩
    refine ⟨hp, fun h => hpS ⟨h, fun hS' => ?_⟩⟩
    rw [U₁.isOpen.frontier_eq] at hp
    exact hp.2 (hSU hS')

include hδ in
/-- **ERS Lemma 4.86 with `∂S` read as the edge `closure S ∖ S`** (the other reading of OQ-41 (e)),
for `S ⊆ U₁`: the same statement. -/
theorem ers_lemma_4_86_edge
    (hnest : Causality.CurveNestedOn (slopeCone E δ hδ) C U₁ ∨
      Causality.CurveNestedOn (slopeCone E δ hδ) C.dual U₁)
    (hS : C.IsCauchySurfaceOn U₁ S) (hS0 : ∀ q ∈ S, q.1 = 0) (hSU : S ⊆ U₁) :
    BoundaryGraph (U₁ : Set (ℝ × E)) (closure S \ S) := by
  intro p hp
  rw [← frontier_diff_closure_eq_frontier_diff_edge hSU] at hp
  exact ers_lemma_4_86 hδ hnest hS hS0 p hp

end Lemma486

/-! ### 6. ERS Theorem 4.82 with (4.83) supplied by Lemma 4.86 -/

section Theorem482

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **ERS Theorem 4.82 under the hypotheses of Lemma 4.86 for the development `i₁`.** Corollary of
`Causal.Causality.ers_theorem_4_82_of_oneSidedBoundary`: its `honesided` is
`ers_lemma_4_86_oneSidedBoundary` for `dom i₁`, `cau i₁`; every other hypothesis is that
theorem's. -/
theorem ers_theorem_4_82_of_slopeCone {ι : Type*} (dom : ι → Opens (ℝ × E))
    (cau : ι → Causality (ℝ × E)) {S : Set (ℝ × E)} {s₀ : ℝ × E} (hs₀ : s₀ ∈ S) (i₁ : ι)
    (hSU : ∀ i, S ⊆ dom i)
    (hmax : ∀ i, dom i₁ ≤ dom i → dom i = dom i₁)
    (hconn : ∀ i, IsPreconnected (dom i : Set (ℝ × E)))
    (hcaus : ∀ i ⦃x y : ℝ × E⦄, (cau i).le (dom i) x y → (cau i).le (dom i) y x → x = y)
    (hsplit : ∀ i, ∀ q ∈ dom i, q ∈ (cau i).Jplus (dom i) S ∪ (cau i).Jminus (dom i) S)
    (hJm : ∀ i, ∀ x ∈ dom i, closure ((cau i).Jminus (dom i) {x}) ∩ dom i ⊆
      (cau i).Jminus (dom i) {x})
    (hJp : ∀ i, ∀ x ∈ dom i, closure ((cau i).Jplus (dom i) {x}) ∩ dom i ⊆
      (cau i).Jplus (dom i) {x})
    (hKm : ∀ i q, IsCompact ((cau i).Jminus (dom i) {q} ∩ (cau i).Jplus (dom i) S))
    (hKp : ∀ i q, IsCompact ((cau i).Jplus (dom i) {q} ∩ (cau i).Jminus (dom i) S))
    (hSclosed : ∀ i, closure S ∩ dom i ⊆ S)
    {δ : ℝ} (hδ : 0 < δ)
    (hnest : Causality.CurveNestedOn (slopeCone E δ hδ) (cau i₁) (dom i₁) ∨
      Causality.CurveNestedOn (slopeCone E δ hδ) (cau i₁).dual (dom i₁))
    (hS : (cau i₁).IsCauchySurfaceOn (dom i₁) S) (hS0 : ∀ q ∈ S, q.1 = 0)
    (hstep : ∀ i, ∀ p ∈ frontier (connectedComponentIn ((dom i₁ : Set (ℝ × E)) ∩ dom i) s₀) ∩
        dom i,
      ((cau i).Jminus (dom i) {p} ∩
          frontier (connectedComponentIn ((dom i₁ : Set (ℝ × E)) ∩ dom i) s₀)
          ∩ (cau i).Jplus (dom i) S = {p} ∨
        (cau i).Jplus (dom i) {p} ∩
          frontier (connectedComponentIn ((dom i₁ : Set (ℝ × E)) ∩ dom i) s₀)
          ∩ (cau i).Jminus (dom i) S = {p}) →
      (∃ V ∈ 𝓝 p, V ⊆ dom i ∧
        V ∩ dom i₁ ⊆ connectedComponentIn ((dom i₁ : Set (ℝ × E)) ∩ dom i) s₀) →
      ∃ j, dom i₁ < dom j) :
    ∀ i, dom i ≤ dom i₁ :=
  Causality.ers_theorem_4_82_of_oneSidedBoundary dom cau hs₀ i₁ hSU hmax hconn hcaus hsplit hJm
    hJp hKm hKp hSclosed (ers_lemma_4_86_oneSidedBoundary hδ hnest hS hS0) hstep

end Theorem482

/-! ### 7. The hypotheses are satisfiable -/

section Witness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `{t = 0}` is a Cauchy surface of the slope-`δ` cone on `ℝ × E`, `E` complete: Geroch's
(ii)⇒(iii) (`IsCauchyTimeFunction.isCauchySurface`) for the static cone, with the time `t`, carried
by the spatial scaling (`IsCausalIso.isCauchySurface_image_iff`). -/
theorem slopeCone_isCauchySurface_slice [CompleteSpace E] {δ : ℝ} (hδ : 0 < δ) :
    (slopeCone E δ hδ).IsCauchySurface {q : ℝ × E | q.1 = 0} := by
  have hstrict : ∀ x y : ℝ × E, (staticCausality E).le ⊤ x y → x ≠ y → x.1 < y.1 :=
    fun x y hxy hne => by
      have h' := staticCausality.le_top_iff.1 hxy
      refine lt_of_le_of_ne (by linarith [dist_nonneg (x := x.2) (y := y.2)]) fun e => hne ?_
      exact staticLe.eq_of_fst_eq hxy e
  have hstat := (staticCausality.isCauchyTimeFunction_fst (X := E)).isCauchySurface
    staticCausality.causallyArcConnected staticCausality.stronglyCausal
    staticCausality.Jminus_ne_singleton staticCausality.Jplus_ne_singleton hstrict
  have h := (isCausalIso_transport (staticCausality E) (slopeScale E δ hδ)).isCauchySurface_image_iff.1
    hstat
  have himg : (slopeScale E δ hδ) '' ((fun p : ℝ × E => p.1) ⁻¹' {0}) = {q : ℝ × E | q.1 = 0} := by
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hq
      refine ⟨(slopeScale E δ hδ).symm q, ?_, (slopeScale E δ hδ).apply_symm_apply q⟩
      show ((slopeScale E δ hδ).symm q).1 = 0
      rw [slopeScale_symm_apply]
      exact hq
  rw [himg] at h
  exact h

/-- **The hypotheses of `ers_lemma_4_86` are satisfiable** (kb/0011): the slope-`δ` cone, nested in
itself, on `U₁ = ℝ × E` (`E` complete) with `S = {t = 0}`. Here `∂U₁ = ∅`, so the conclusion is
vacuous; the witness says only that the hypothesis set is consistent. -/
theorem ers_lemma_4_86_hypotheses_slopeCone [CompleteSpace E] {δ : ℝ} (hδ : 0 < δ) :
    (Causality.CurveNestedOn (slopeCone E δ hδ) (slopeCone E δ hδ) ⊤ ∨
      Causality.CurveNestedOn (slopeCone E δ hδ) (slopeCone E δ hδ).dual ⊤) ∧
    (slopeCone E δ hδ).IsCauchySurfaceOn ⊤ {q : ℝ × E | q.1 = 0} ∧
    ∀ q ∈ {q : ℝ × E | q.1 = 0}, q.1 = 0 :=
  ⟨Or.inl ((Causality.LeNested.refl _).curveNestedOn ⊤), slopeCone_isCauchySurface_slice hδ,
    fun _ hq => hq⟩

end Witness

/-! ### 8. A witness with a non-empty boundary: the slab of Minkowski space -/

section Slab

/-- The slab `{|t| < 1}` of Minkowski space `ℝ^{1,d}`. -/
def minkowskiSlab (d : ℕ) : Opens (Minkowski d) :=
  ⟨{p | |p.1| < 1}, isOpen_lt (continuous_abs.comp continuous_fst) continuous_const⟩

/-- **`{t = 0}` is a Cauchy surface of the slab** for Minkowski's causality: the saturation
criterion `Causal.Flat.isCauchySurfaceOn_graph_of_saturated` for the graph of `0`. -/
theorem minkowski_isCauchySurfaceOn_slab (d : ℕ) :
    (minkowski d).IsCauchySurfaceOn (minkowskiSlab d) {p | p.1 = 0} := by
  have hf : Flat.IsStrictContraction (d := d) (fun _ => (0 : ℝ)) := fun x y hxy => by
    simpa using norm_pos_iff.2 (sub_ne_zero.2 hxy)
  have hS : (minkowski d).IsCauchySurface (Flat.graph (d := d) (fun _ => (0 : ℝ))) :=
    Flat.isCauchySurface_graph (κ := 0) (LipschitzWith.const 0) (by norm_num)
  refine Flat.isCauchySurfaceOn_graph_of_saturated hf
    (fun z _ v hv hv0 => Flat.exists_mem_line_of_isCauchySurfaceOn hS (W := ⊤) trivial hv hv0)
    (fun z hz q hqz hq => ?_) (fun z hz q hzq hq => ?_)
  · have h := minkowski_le_top_iff.1 hqz
    have hz' : |z.1| < 1 := hz
    rw [Flat.timeSub_apply, sub_zero] at hq
    show |q.1| < 1
    rw [abs_lt] at hz' ⊢
    constructor <;> linarith [norm_nonneg (z.2 - q.2)]
  · have h := minkowski_le_top_iff.1 hzq
    have hz' : |z.1| < 1 := hz
    rw [Flat.timeSub_apply, sub_zero] at hq
    show |q.1| < 1
    rw [abs_lt] at hz' ⊢
    constructor <;> linarith [norm_nonneg (q.2 - z.2)]

/-- **ERS Lemma 4.86 on the Minkowski slab: a witness with a non-empty boundary** (kb/0011). On
`ℝ^{1,d}` with `C = minkowski d`, every slope `δ ≤ 1`, `U₁ = {|t| < 1}` and `S = {t = 0}`, the
hypotheses of `ers_lemma_4_86` hold, `∂U₁ ∖ closure S = {|t| = 1}` is non-empty, and the lemma
applies: (4.83) and `OneSidedBoundary` there. -/
theorem minkowskiSlab_ers_lemma_4_86 (d : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Causality.CurveNestedOn (slopeCone (EuclideanSpace ℝ (Fin d)) δ hδ) (minkowski d)
        (minkowskiSlab d) ∧
      (minkowski d).IsCauchySurfaceOn (minkowskiSlab d) {p | p.1 = 0} ∧
      (frontier (minkowskiSlab d : Set (Minkowski d)) \
        closure {p : Minkowski d | p.1 = 0}).Nonempty ∧
      BoundaryGraph (minkowskiSlab d : Set (Minkowski d)) (closure {p : Minkowski d | p.1 = 0}) ∧
      Causality.OneSidedBoundary (minkowskiSlab d) (closure {p : Minkowski d | p.1 = 0}) := by
  have hnest : Causality.CurveNestedOn (slopeCone (EuclideanSpace ℝ (Fin d)) δ hδ) (minkowski d)
      (minkowskiSlab d) := (slopeCone_leNested_staticCausality hδ hδ1).curveNestedOn _
  have hS := minkowski_isCauchySurfaceOn_slab d
  have hS0 : ∀ q ∈ {p : Minkowski d | p.1 = 0}, q.1 = 0 := fun _ hq => hq
  refine ⟨hnest, hS, ⟨((1 : ℝ), 0), ?_, ?_⟩, ers_lemma_4_86 hδ (Or.inl hnest) hS hS0,
    ers_lemma_4_86_oneSidedBoundary hδ (Or.inl hnest) hS hS0⟩
  · rw [(minkowskiSlab d).isOpen.frontier_eq]
    refine ⟨Metric.mem_closure_iff.2 fun ε hε => ?_, fun h => ?_⟩
    · set m := min (ε / 2) (1 / 2) with hmdef
      have hm : 0 < m := lt_min (by linarith) (by norm_num)
      have hm1 : m ≤ ε / 2 := min_le_left _ _
      have hm2 : m ≤ 1 / 2 := min_le_right _ _
      refine ⟨((1 - m : ℝ), 0), ?_, ?_⟩
      · show |(1 - m : ℝ)| < 1
        rw [abs_lt]; constructor <;> linarith
      · rw [Prod.dist_eq, Real.dist_eq, dist_self, show (1 : ℝ) - (1 - m) = m by ring,
          abs_of_pos hm, max_eq_left hm.le]
        linarith
    · have h' : |(1 : ℝ)| < 1 := h
      rw [abs_one] at h'
      exact lt_irrefl _ h'
  · rw [(isClosed_eq continuous_fst continuous_const).closure_eq]
    exact one_ne_zero

end Slab

end Causal
