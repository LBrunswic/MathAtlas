import GX.BTZ.CBG
import Causal.SingularGeroch
import Causal.LevinUtility
import Causal.LemmaKLocal

/-!
# `GX.BTZ.Spear` — spear neighbourhoods and full future BTZ rays (B21 Lemmas 2.3, 2.4)

Package WP-41i (WAVE5-PLAN.md, WP-39i), fixer round 2; WP-43a; **WP-44d (DEC-108): 0 `sorry`**;
WP-46b (DEC-116 (b)(c); Def 2.1's boundary sentence is the field `IsSpearNbhd.isClosed`); WP-47b
(DEC-125 (a)(b)(c): the last three readings ruled, all four rows closed and marked).
`brunswic2021cauchy` (**B21**, `papers/gx/sources/2108.12631/src/BTZ_1.tex`) Def 2.1 (l.611),
Lemma 2.3 `lem:tube` (l.635), Lemma 2.4 `lem:add_BTZ_param` (l.685), cited by `papers/gx` at
`RamcovGX.tex:2352` (proof of `prop:globally_hyperbolic_cauchy_complete_manifolds`, l.2348) as
« Lemma 2.4 » — **the right citation is Lemma 2.3** (finding). Cited results built here (DEC-23),
not gx ledger rows: marked with their source prefix `brunswic2021cauchy:`. For `𝔼₀`-manifolds
only, by DEC-116 (b) and DEC-125 (a) (gx §4 is `𝔼₀`, DEC-77 (c)):

* **`brunswic2021cauchy:lem:tube`** (B21 Lemma 2.3, l.635) — **closed, 0 `sorry`**
  (`GX.E0Spear.lem_tube`, CBG parameters `hLine`, `hSC`; **parameter-free**
  `GX.E0Spear.lem_tube_e0`, the parameters being `E0LM.e0_globalBTZ`,
  `E0LM.e0_secondCountable_of_cauchy`), under DEC-116 (b) (`𝔼₀` only) and (c) (Def 2.1's spear).
  The gluing (`exists_spearDevelopment`, §4a–§4c): `M₀ = M ∖ J⁺(κ⁻¹Π)`, under B21's normalisation
  (l.647: the chart cylinder **causally convex in `M`**, `CylChartData.convex`; `κ⁻¹Π` acausal;
  overlap `𝒫 ∩ {τ < v + ε/2}`), glued to the spear piece `𝒫` (`CylChartData.glueData`): an
  `𝔼₀`-manifold, Hausdorff, second countable, connected; **`M₂` globally hyperbolic** (DEC-108,
  `CylChartData.globallyHyperbolic_glued`: a `Causal.Causality.TwoPiece`, mixed diamonds
  `CylChartData.isCompact_diamond_mixed`); **`Σ` Cauchy in `M₂`** (`CylChartData.isCauchySurface_glued`).
* **`full future BTZ rays (RamcovGX.tex:2352)`** — **closed** under DEC-125 (b) (the reading
  `IsFullFutureBTZRay`) and DEC-77 (c) (GH + Cauchy-maximal, counterexample `{τ < 0}`):
  `GX.E0Spear.exists_fullFutureBTZRay`, parameter-free `exists_fullFutureBTZRay_e0`; the reading
  implies every natural one, each proved (`IsFullFutureBTZRay.{mem_S0, injOn, continuousOn, le,
  not_tendsto, exists_eq_of_line}`). No gx label (not registered by the ledger).
* **`brunswic2021cauchy:Def 2.1`** (spear neighbourhood, l.611) — **closed** under DEC-116 (c)
  and DEC-125 (a) (`𝔼₀` only; the boundary sentence l.617 = the field `IsSpearNbhd.isClosed`,
  **equivalent** to it in every `𝔼₀`-manifold, `frontier_spearImage_eq_iff_isClosed`,
  `IsSpearNbhd.frontier_eq`, model `frontier_spear`; automatic for GH `M`, `isClosed_spearImage`,
  `IsSpearNbhd.of_chart`, `isSpearNbhd_iff_chart`): free vertex `(v, 0)`, head `{f = v, r ≤ R}`,
  shaft `{r = R, τ ≥ v + R/2}` (`spear`, `spearHead`, `spearShaft`, `IsSpearNbhd`); « neighbourhood
  of `]p,+∞[` » (`IsSpearNbhd.exists_ray_mem_nhds`; on `Δ` itself `IsSpearNbhd.mem_nhds_of_line`).
* **`brunswic2021cauchy:lem:add_BTZ_param`** (B21 Lemma 2.4, l.685) — **closed** under DEC-116
  (b)(c) and DEC-125 (c) (`τ_Σ` continuous, `continuousOn_tauS`): both cases, 0 `sorry`
  (`lem_add_BTZ_param_line(_e0)`, `lem_add_BTZ_param_of_cauchyMaximal(_e0)`; « `q` in the
  future of `p` » by `exists_spearNbhd_below`, DEC-108). Smoothness is false for B21's
  topological Cauchy surfaces (l.224) (finding, `Σ = {τ = |Re z|/4}` in `𝔼₀`).

> \begin{defou}[Spear neighborhood] Let $M$ be a $\mass{\geq0}$-manifold and let $\Delta$ be a
> BTZ-line. A spear neighborhood around $\Delta$ of vertex $p\in \Delta$ and radius $R>0$ is a
> neighborhood of $]p,+\infty[$ such that there exists a singular $\mass{}$-isomorphism
> $\phi: \U\rightarrow \V\subset \mass{0}$ with $\phi(p)=(-2R,0,0),\quad \V:= J^+(\phi(p)) \cap
> \{\r\leq R\}\subset \mass{0}$. The boundary of $\U$ is the union of the light cone
> $\phi^{-1}(\{\r = 2(\tau-R),\r<R\})$ and a half-tube $\phi^{-1}(\{\r=R, \tau\geq 0\})$. The former
> is called the \textbf{head} and the latter the \textbf{shaft} of $\U$. \end{defou} (l.611–619)
>
> \begin{lemou} Let $M$ be a globally hyperbolic $\mass{\geq0}$-manifold. If $M$ is
> Cauchy-maximal then, for any BTZ line $\Delta$ and any $p\in \Delta$, there exists a spear
> neighborhood around $\Delta$ of vertex $p$. \end{lemou} (l.635–638)
>
> \begin{lemou} Let $M$ be a globally hyperbolic $\mass{\geq0}$-manifold, let $\Sigma$ be
> Cauchy-surface of $M$ and let a BTZ line $\Delta$ of $M$ admitting a spear neighborhood. Then,
> for all $p\in \Delta\cap I^-(\Sigma)$, there exists a spear neighborhood
> $\phi:\mathcal S \rightarrow \mass{0}$ around $\Delta$ of vertex $p$ and some radius $R>0$ such
> that $\Sigma\cap \S$ lie in the shaft of $\Delta$ and $\phi(\Sigma\cap \mathcal S)\subset \mass{0}$
> is the graph of a smooth positive function $\tau_\Sigma: \mathbb D_R\rightarrow \RR_+^*$.
> \end{lemou} (l.685–695)
>
> Finally Lemma 2.4 of \cite{brunswic2021cauchy} implies that the singular locus contains full
> future BTZ rays. (`RamcovGX.tex:2352`)

## What is built

* **§5′ Def 2.1 in `M` (WP-46b fixer)**: `isCompact_spear_inter_le`, `isClosed_spearImage`,
  `interior_spearImage`, `frontier_spearImage_eq_iff_isClosed`, `frontier_spearImage`,
  `IsSpearNbhd.of_chart`, `isSpearNbhd_iff_chart`, `IsSpearNbhd.frontier_eq`,
  `IsSpearNbhd.mem_nhds_of_line`; `isClosed_spearY`, `isClosed_image_spearY_of_subset` (round 2).
* **§1 the model.** `spear v R = {f ≥ v, r ≤ R} = J⁺((v,0)) ∩ {r ≤ R}` (`spear`,
  `spear_eq_Jplus_inter`), closed, containing the ray `[v, +∞[`; spears and cylinders are causally
  convex (`mem_spear_of_le`, `mem_cyl_of_le`, `le_of_le_top_of_mem_cyl`); vertical lines are future
  null (`le_vertical`); `spear_diff_Jplus_disc`; head and shaft corrected, and **the boundary of a
  spear is its head and its shaft** (`interior_spear`, `frontier_spear`).
* **§2 spear neighbourhoods and full rays** (`IsSpearNbhd`, `IsFullFutureBTZRay`); transfer of the
  relations of `𝔼₀` along `𝔼₀`-morphisms (`le_of_isE0Mor`, `le_of_isE0Mor_paper`) and back through
  a chart (`chart_le_iff`); a chart cylinder at every BTZ point (`exists_cyl_chart`), causally
  convex in a globally hyperbolic `M` (`exists_cylChartData`); horizontal discs of `𝔼₀` are
  acausal (`eq_of_le_of_fst_eq`).
* **§3 Cauchy-maximality** (`IsE0CauchyMaximal`; DEC-77(c): `isE0CauchyMaximal_iff_isETTMaximal`)
  and universality over Cauchy sub-developments (`IsE0CauchyMaximal.exists_morphism_of_dev`).
* **§4a′ relative curve extension (WP-43a)**: a causal curve of an open `W` lying on a
  time-parametrised curve of `W` that reaches further in time is extensible, constant pieces
  allowed (`causalCurveIn_comp_monotoneOn`, `extensible_of_timeGraph_openEnd`,
  `extensible_of_timeGraph_future`, `extensible_of_timeGraph_past`); a Cauchy surface inside an
  open past set is Cauchy there (`isCauchySurfaceOn_of_isPast`).
* **§4a″ connected Cauchy surfaces without compactness (WP-43a)**: futures of closed pieces of a
  Cauchy surface are closed under R1 (`isClosed_Jplus_of_subset_cauchy`), and a closed acausal
  Cauchy surface of a connected GH spacetime is connected (`isConnected_of_isCauchySurface_closed`,
  the non-compact form of WP-41k's `E0AbsMax.isConnected_of_isCauchySurface_abstract`).
* **§4a–§4b the gluing of Lemma 2.3** (above), **§4 Lemma 2.3** (`SpearDevelopment`, `lem_tube`,
  `exists_fullFutureBTZRay`, `exists_isCauchySurface_of_globalBTZ`: a GH `𝔼₀`-manifold has a Cauchy
  surface, strict `geroch_sing_i_imp_iii`), level sets of Cauchy time functions are Cauchy
  (`isCauchySurface_level`).
* **§4c the causality of `M₂` (WP-44d)**: `pieceChart_of_isE0Mor`, `gluePY_le_iff`,
  `CylChartData.{W0_le_iff, twoPiece, le_ι0_iff, le_Ψ_iff, le_ι0_Ψ_iff, globallyHyperbolic_W0o,
  diamond_eq_empty, exists_overlap_of_le, isCompact_diamond_mixed, not_inextensible_above}`,
  `globallyHyperbolic_gluePY`, `isCompact_diamond_E0`, `exists_le_fst_eq`,
  `isCompact_Jplus_singleton_inter_Jminus_of_isCompact`, `pastExtensible_gluePaper`.
* **§5 the future case of Lemma 2.4 (WP-44d)**: `CylChartData.exists_spear_below` (the gluing of
  one chart cylinder to a spear chart), `exists_spearNbhd_below` (continuation),
  `le_iff_of_mem_e0Groupoid`, `isE0Mor_of_mem_e0Groupoid`, `D_le_rangeInr_iff`.
* **§7 parameter-free forms**: `lem_tube_e0`, `exists_fullFutureBTZRay_e0`,
  `lem_add_BTZ_param_line_e0`, `lem_add_BTZ_param_of_cauchyMaximal_e0`.
* **§5–6 Lemma 2.4** (`spear_shaft_vertical`, `spear_vertical_meets`, `continuousOn_tauS`,
  `lem_add_BTZ_param`, `IsFullFutureBTZRay.exists_eq_of_line`, `lem_add_BTZ_param_line`,
  `lem_add_BTZ_param_of_cauchyMaximal`), with `not_lt_self`, `notMem_of_mem_Iminus`,
  `exists_tendsto_of_monotone` and the escape lemmas `axis_noLimit`, `spear_vertical_noLimit`.
  Non-vacuity: `isSpearNbhd_model`.

## Hypothesis checklist

| paper | here |
|---|---|
| `𝔼_{≥0}`-manifold (Lemmas 2.3, 2.4) | ✓ ruled (DEC-116 (b), DEC-77 (c)): `𝔼₀`-manifolds only, `ChartedSpace E0Y M`, `HasGroupoid M e0Groupoid` (`Y = 𝕄 ⊕ 𝔼₀`; massive cones not in `Y`, as WP-41e/f), Hausdorff, second countable, connected (DEC-66) |
| globally hyperbolic | ✓ `(CE M).GloballyHyperbolic`; the Cauchy surface is **derived** (`exists_isCauchySurface_of_globalBTZ`, `CylChartData.exists_cauchy_subset_W0`), not assumed |
| Cauchy-maximal | ✓ read (DEC-77(c)): `IsE0CauchyMaximal` = `Dev.IsETTMaximal` |
| « full future BTZ rays » (`RamcovGX.tex:2352`) | ✓ ruled (DEC-125 (b)): `IsFullFutureBTZRay`, implying every natural reading, each proved (in `sing₀`, injective, continuous, future causal, no future endpoint, covering `[p,+∞[ ⊆ Δ` for GH `M`); hypotheses GH + Cauchy-maximal (DEC-77 (c), counterexample `{τ < 0}`), Cauchy-completeness unused |
| spear neighbourhood, `φ(p) = (−2R,0,0)` | ✓ ruled (DEC-116 (c)): `ψ = φ⁻¹` an injective `𝔼₀`-morphism on an open `W ⊇ 𝒮`, vertex `(v,0)`, `v` free; head `{f = v, r ≤ R}`, shaft `{r = R, τ ≥ v + R/2}` (`frontier_spear`; the printed formulas fit neither the printed vertex nor each other, finding) |
| Def 2.1: `𝔼_{≥0}`-manifold | ✓ ruled (DEC-125 (a), extending DEC-116 (b)): `𝔼₀`-manifolds only (B21 uses spear neighbourhoods only in Lemmas 2.3/2.4 and §2.2, all `𝔼₀`) |
| Def 2.1: « the boundary of `𝒰` is the head ∪ the shaft » (l.617) | ✓ ruled (DEC-125 (a)), read as part of the definition (audit option (a)): the field `IsSpearNbhd.isClosed`, equivalent for every spear chart in every `𝔼₀`-manifold to `∂𝒰 = ψ(head ∪ shaft)` (`frontier_spearImage_eq_iff_isClosed`, via `interior_spearImage`); hence `IsSpearNbhd.frontier_eq` with no global hypothesis; in `𝔼₀` `frontier_spear`. For GH `M` (Lemmas 2.3/2.4) the field is automatic: `isClosed_spearImage` (`axis_noLimit` + `exists_tendsto_of_monotone`), `IsSpearNbhd.of_chart`, `isSpearNbhd_iff_chart` — so Lemmas 2.3/2.4 are unchanged in content |
| « neighbourhood of `]p,+∞[` » | ✓ of the chart ray `ψ(]v,+∞[)`: `IsSpearNbhd.exists_ray_mem_nhds`; of `]p,+∞[ ⊆ Δ` itself for GH `M`: `IsSpearNbhd.mem_nhds_of_line` (via `IsFullFutureBTZRay.exists_eq_of_line`, the chart ray covers `[p,+∞[`) |
| CBG (hidden in « `M₂` embeds into `M` ») | ✓ `E0CBG.e0_cbg`; `hLine` (O2), `hSC` (O4) discharged in the `_e0` forms (`E0LM.e0_globalBTZ`, `E0LM.e0_secondCountable_of_cauchy`) |
| Lemma 2.4: `M` GH | ✓ `hLM` (the BTZ lines of `M`) discharged by `E0LM.e0_globalBTZ` in `lem_add_BTZ_param_line_e0` (`M` connected, DEC-66) |
| Lemma 2.4: « `Δ` admitting a spear neighbourhood », `p ∈ Δ ∩ I⁻(Σ)` | ✓ `lem_add_BTZ_param_line`: spear of vertex `q`, `p ∈ connectedComponentIn (S0 M) q` (`Δ` = component of `sing₀`); both cases proved |
| Lemma 2.4: `τ_Σ` « smooth positive » | ✓ ruled (DEC-125 (c)): `C⁰`, the strongest true form for B21's topological Cauchy surfaces (l.224): `ContinuousOn τ_Σ (closedBall 0 R′)`; smoothness is false without `Σ` smooth (paper counterexample `Σ = {τ = |Re z|/4}` in `𝔼₀`, every spear chart of the axis being a rotation-translation, B21 `prop:isom_strong`: `τ_Σ` is not differentiable at `0`; not formalized); « positive » read as `τ_Σ > v + R′/2` (DEC-116 (c)). The row closes (DEC-27 with DEC-125 (c)) |
| Lemma 2.4: « in the shaft » | ✓ ruled (DEC-116 (c)): the open region `τ > v + R′/2` above the rim of the head (B21 Prop 2.17, PDF l.1983, uses the conclusion as « a circle in the shaft ») |

## SCOPE (disclosed; 0 `sorry`)

* WP-44d closed the three tagged `sorry`s of WP-43a under DEC-108: `globallyHyperbolic_glued`
  (§4c: two-piece structure, mixed diamonds), `isCauchySurface_glued` (now with
  `[SecondCountableTopology M]`, which its only caller carries; past ends above `Π` converge in `𝒫`,
  `pastExtensible_gluePaper`) and the future case of `lem_add_BTZ_param_line` (§5's continuation).
* WP-46b (DEC-116 (b)(c)): the readings `𝔼₀`-manifolds only, Def 2.1's free
  vertex and corrected head/shaft, and « in the shaft » = `τ > v + R′/2` are ruled; `lem:tube`
  and Def 2.1 close and are marked; the full future BTZ rays close, unmarked (reading unruled).
  Fixer round 1: Def 2.1's boundary assertion proved **in `M`** (GH). Fixer round 2 (audit major,
  option (a)): the sentence is the field `IsSpearNbhd.isClosed` (equivalent to it in every
  `𝔼₀`-manifold, automatic in GH `M`); `IsSpearNbhd.of_ray` gains `[HasGroupoid M e0Groupoid]`,
  `CylChartData.exists_spear_below` and `IsE0CauchyMaximal.isSpearNbhd_of_spearDevelopment` gain
  `hGH` (both internal, GH callers only); `IsSpearNbhd.frontier_eq` loses its `hGH`/`T2Space`
  (strengthened); §4 (`lem:tube`) moved after §5 so that it can use `isClosed_spearImage`.
* WP-47b (DEC-125 (a)(b)(c), docstrings only, no declaration changed): Def 2.1 for `𝔼₀` only with
  its boundary sentence = `IsSpearNbhd.isClosed` (a), « full future BTZ rays » = `IsFullFutureBTZRay`
  (b) and Lemma 2.4 with `τ_Σ` continuous (c) are ruled; the full rays and Lemma 2.4 close and are
  marked, Def 2.1's mark now rests on a ruling. Nothing remains partial.
* Lemma 2.4's `τ_Σ` is continuous, not smooth (ruled, DEC-125 (c)). B21's Cauchy surfaces are
  topological (l.224) and its proof's transversality (l.729) uses `Σ` smooth spacelike; for a
  topological (even piecewise-smooth spacelike) `Σ` the smooth conclusion is false (the kinked
  `Σ = {τ = |Re z|/4}` of `𝔼₀`). The `C¹` path of gx §4 (DEC-107, DEC-117) takes the `C¹`-ness of
  the rim circle from `IsE0C1SpacelikeCauchy.rim` (`GX.BTZ.Surgery`), not from Lemma 2.4.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; lean-causal `ca2ad78`
(`lake-manifest.json`; imports `Causal.SingularGeroch`, strict, DEC-33).
-/

namespace GX

open Set Filter Topology Function TopologicalSpace
open scoped Real

namespace E0Spear

open E0

/-! ### §1 Spears in the model `𝔼₀` (paper coordinates `(τ, z = r e^{iθ})`) -/

section Model

/-- The vertex `(v, 0)` on the BTZ line of `𝔼₀`. -/
def vertex (v : ℝ) : E0 := (v, 0)

theorem vertex_mem_axis (v : ℝ) : vertex v ∈ axis := rfl

/-- **The spear of `𝔼₀` of vertex `(v,0)` and radius `R`** (B21 Def 2.1, `BTZ_1.tex:616`):
`J⁺((v,0)) ∩ {r ≤ R} = {f ≥ v, r ≤ R}`, `f = τ − r/2` (`spear_eq_Jplus_inter`). -/
def spear (v R : ℝ) : Set E0 := {x | v ≤ fcoord x ∧ rad x ≤ R}

/-- The head of the spear: the piece `{f = v, r ≤ R}` of the light cone of the vertex
(corrected form of the printed `{r = 2(τ − R), r < R}`, finding). -/
def spearHead (v R : ℝ) : Set E0 := {x | fcoord x = v ∧ rad x ≤ R}

/-- The shaft of the spear: the half-tube `{r = R, τ ≥ v + R/2}` above the rim of the head. -/
def spearShaft (v R : ℝ) : Set E0 := {x | rad x = R ∧ v + R / 2 ≤ x.1}

theorem mem_spear {v R : ℝ} {x : E0} : x ∈ spear v R ↔ v ≤ fcoord x ∧ rad x ≤ R := Iff.rfl

theorem spear_eq_Jplus_inter (v R : ℝ) :
    spear v R = causality.Jplus ⊤ {vertex v} ∩ {x | rad x ≤ R} := by
  rw [Jplus_axis (vertex_mem_axis v)]
  rfl

theorem isClosed_spear (v R : ℝ) : IsClosed (spear v R) :=
  (isClosed_le continuous_const continuous_fcoord).inter
    (isClosed_le continuous_rad continuous_const)

/-- The BTZ ray `[v, +∞[` of the axis lies in the spear. -/
theorem axis_mem_spear {v R t : ℝ} (hR : 0 ≤ R) (ht : v ≤ t) : ((t, 0) : E0) ∈ spear v R := by
  have h0 : rad ((t, 0) : E0) = 0 := rad_eq_zero.2 rfl
  refine ⟨?_, ?_⟩
  · simp only [fcoord, h0]; linarith
  · rw [h0]; exact hR

theorem vertex_mem_spear {v R : ℝ} (hR : 0 ≤ R) : vertex v ∈ spear v R :=
  axis_mem_spear hR le_rfl

theorem spear_mono {v v' R R' : ℝ} (hv : v ≤ v') (hR : R' ≤ R) : spear v' R' ⊆ spear v R :=
  fun _ hx => ⟨hv.trans hx.1, hx.2.trans hR⟩

/-- The interior of a spear of positive radius: `{f > v, r < R}`. -/
theorem interior_spear {v R : ℝ} (hR : 0 < R) :
    interior (spear v R) = {x | v < fcoord x ∧ rad x < R} := by
  apply Subset.antisymm
  · intro x hx
    have hxS : x ∈ spear v R := interior_subset hx
    have hnhds : interior (spear v R) ∈ 𝓝 x := isOpen_interior.mem_nhds hx
    refine ⟨?_, ?_⟩
    · by_contra hf
      have hf' : fcoord x = v := le_antisymm (not_lt.1 hf) hxS.1
      -- move down along the vertical line: `f` decreases below `v`
      let c : ℝ → E0 := fun ε => (x.1 - ε, x.2)
      have hc : Continuous c := (continuous_const.sub continuous_id).prodMk continuous_const
      have hc0 : c 0 = x := by simp [c]
      have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), c ε ∈ interior (spear v R) :=
        hc.continuousAt.preimage_mem_nhds (by rw [hc0]; exact hnhds)
      obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
      have hmem := interior_subset (hball (show dist (δ / 2) 0 < δ by
        rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith))
      have : fcoord (c (δ / 2)) = fcoord x - δ / 2 := by simp [c, fcoord, rad]; ring
      have h1 := hmem.1
      rw [this, hf'] at h1
      linarith
    · by_contra hr
      have hr' : rad x = R := le_antisymm hxS.2 (not_lt.1 hr)
      -- move outwards along a radial null-or-spacelike line keeping `f ≥ v`
      let c : ℝ → E0 := fun ε => (x.1 + ε * R, ((1 + ε : ℝ) : ℂ) * x.2)
      have hc : Continuous c := (continuous_const.add (continuous_id.mul continuous_const)).prodMk
        ((Complex.continuous_ofReal.comp (continuous_const.add continuous_id)).mul
          continuous_const)
      have hc0 : c 0 = x := by simp [c]
      have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), c ε ∈ interior (spear v R) :=
        hc.continuousAt.preimage_mem_nhds (by rw [hc0]; exact hnhds)
      obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
      have hmem := interior_subset (hball (show dist (δ / 2) 0 < δ by
        rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith))
      have hrc : rad (c (δ / 2)) = (1 + δ / 2) * R := by
        simp only [c, rad, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        rw [abs_of_pos (by linarith)]
        exact congrArg _ hr'
      have h2 := hmem.2
      rw [hrc] at h2
      nlinarith
  · exact interior_maximal (fun x hx => ⟨hx.1.le, hx.2.le⟩)
      ((isOpen_lt continuous_const continuous_fcoord).inter
        (isOpen_lt continuous_rad continuous_const))

/-- **The boundary of a spear is its head and its shaft** (Def 2.1, l.617, in the corrected
form: the head is the cone piece `{f = v, r ≤ R}`, the shaft the half-tube `{r = R, τ ≥ v + R/2}`;
the printed `{r = 2(τ − R)}` and `{τ ≥ 0}` do not fit the printed vertex `(−2R, 0, 0)`). -/
theorem frontier_spear {v R : ℝ} (hR : 0 < R) :
    frontier (spear v R) = spearHead v R ∪ spearShaft v R := by
  rw [frontier, (isClosed_spear v R).closure_eq, interior_spear hR]
  ext x
  simp only [spear, spearHead, spearShaft, Set.mem_sdiff, mem_setOf_eq, mem_union, not_and_or,
    not_lt, fcoord]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3 | h3⟩
    · exact Or.inl ⟨le_antisymm h3 h1, h2⟩
    · exact Or.inr ⟨le_antisymm h2 h3, by rw [← le_antisymm h2 h3]; linarith⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨⟨h1.ge, h2⟩, Or.inl h1.le⟩
    · exact ⟨⟨by rw [h1]; linarith, h1.le⟩, Or.inr h1.ge⟩

/-- **Spears are causally convex in `𝔼₀`**: `f` and `r` are non-decreasing along `≤`. -/
theorem mem_spear_of_le {v R : ℝ} {U V : Opens E0} {x y z : E0} (hx : x ∈ spear v R)
    (hz : z ∈ spear v R) (hxy : causality.le U x y) (hyz : causality.le V y z) :
    y ∈ spear v R :=
  ⟨hx.1.trans (calculus_le hxy).2.2.2.2.1, ((calculus_le hyz).2.2.2.1).trans hz.2⟩

/-- **The open cylinders `{a < τ < b, r < ρ}` are causally convex in `𝔼₀`.** -/
def cyl (a b ρ : ℝ) : Set E0 := {x | a < x.1 ∧ x.1 < b ∧ rad x < ρ}

theorem isOpen_cyl (a b ρ : ℝ) : IsOpen (cyl a b ρ) :=
  (isOpen_lt continuous_const continuous_fst).inter
    ((isOpen_lt continuous_fst continuous_const).inter (isOpen_lt continuous_rad continuous_const))

theorem mem_cyl_of_le {a b ρ : ℝ} {U V : Opens E0} {x y z : E0} (hx : x ∈ cyl a b ρ)
    (hz : z ∈ cyl a b ρ) (hxy : causality.le U x y) (hyz : causality.le V y z) :
    y ∈ cyl a b ρ :=
  ⟨hx.1.trans_le (calculus_le hxy).2.2.1, ((calculus_le hyz).2.2.1).trans_lt hz.2.1,
    ((calculus_le hyz).2.2.2.1).trans_lt hz.2.2⟩

/-- **Two causally related points of `𝔼₀` at the same time `τ` coincide** (the horizontal discs
`{τ = c}` are acausal): `0 ≤ Δr ≤ 2Δτ = 0` and `r₁ r₂ δ² ≤ −(Δr)²` force `Δr = 0` and then
`r = 0` or `δ = 0`. -/
theorem eq_of_le_of_fst_eq {U : Opens E0} {x y : E0} (h : causality.le U x y)
    (hτ : x.1 = y.1) : x = y := by
  obtain ⟨θ₁, θ₂, h₁, h₂, -, -, hq⟩ := le_iff_closed.1 (E0.le_of_le h)
  have hrx := rad_nonneg x
  have hry := rad_nonneg y
  have hsq : 0 ≤ rad x * rad y * (θ₂ - θ₁) ^ 2 := by positivity
  rw [hτ, sub_self, mul_zero, zero_sub] at hq
  have hreq : rad y = rad x := by nlinarith [sq_nonneg (rad y - rad x)]
  rw [hreq] at hq
  have h0 : rad x * rad x * (θ₂ - θ₁) ^ 2 = 0 := by
    have : rad x * rad x * (θ₂ - θ₁) ^ 2 ≤ 0 := by simpa using hq
    exact le_antisymm this (by positivity)
  refine Prod.ext hτ ?_
  rw [h₁, h₂, hreq]
  rcases mul_eq_zero.1 h0 with h | h
  · rcases mul_eq_zero.1 h with h | h <;> simp [h]
  · have : θ₂ = θ₁ := by
      have := pow_eq_zero_iff (two_ne_zero) |>.1 h
      linarith
    rw [this]

/-- The vertical segment from `(τ, z)` to `(τ', z)`, read through the development. -/
theorem lift_vertical (τ τ' s : ℝ) (z : ℂ) (θ : ℝ) :
    seg (lift (τ, z) θ) (lift (τ', z) θ) s = lift (τ + s * (τ' - τ), z) θ := by
  simp only [seg, lift, btzPaperNull, rad]
  ext <;> simp; ring

/-- **The vertical lines `θ, r` fixed are future null** (`∂_τ` is null for
`−2dτdr + dr² + r²dθ²`): `(τ, z) ≤_U (τ', z)` for `τ ≤ τ'` as soon as the vertical segment lies
in `U`. -/
theorem le_vertical {U : Opens E0} {τ τ' : ℝ} {z : ℂ} (h : τ ≤ τ')
    (hU : ∀ s ∈ Icc (0 : ℝ) 1, ((τ + s * (τ' - τ), z) : E0) ∈ U) :
    causality.le U (τ, z) (τ', z) := by
  have hx : Polar ((τ, z) : E0) (Complex.arg z) := polar_arg ((τ, z) : E0)
  have hy : Polar ((τ', z) : E0) (Complex.arg z) := polar_arg ((τ', z) : E0)
  refine cle_of_seg hx hy ?_ fun s hs => ?_
  · rw [nullCone_lift_iff]
    refine ⟨h, le_rfl, ?_⟩
    simp [rad]
  · rw [lift_vertical, unlift_lift (polar_arg ((τ + s * (τ' - τ), z) : E0))]
    exact hU s hs

theorem le_vertical_top {τ τ' : ℝ} {z : ℂ} (h : τ ≤ τ') :
    causality.le ⊤ ((τ, z) : E0) (τ', z) :=
  le_vertical h fun _ _ => trivial

/-- **Above a horizontal disc, the spear is in its causal future**: a point of `spear v R` with
`τ ≥ c` lies above the point `(c, z)` of the disc `Π = {τ = c, r ≤ R}`; hence the part of the
spear outside `J⁺(Π)` lies below the level `τ = c` (`spear_diff_Jplus_disc`). -/
def disc (c R : ℝ) : Set E0 := {x | x.1 = c ∧ rad x ≤ R}

theorem spear_diff_Jplus_disc (v R c : ℝ) :
    spear v R \ causality.Jplus ⊤ (disc c R) ⊆ {x | x.1 < c} := by
  rintro ⟨τ, z⟩ ⟨hx, hnot⟩
  by_contra hc
  refine hnot ⟨(c, z), ⟨rfl, hx.2⟩, le_vertical_top (not_lt.1 hc)⟩

end Model

/-! ### §2 Spear neighbourhoods and full future BTZ rays in an `𝔼₀`-manifold -/

section Manifold

open E0CBG

/-- `f` is an `𝔼₀`-morphism on `W` (`LiftPropOn` of the a.e.-isomorphism groupoid, DEC-62's local
form; the morphisms of `E0CBG.e0Geometry`, `E0CBG.e0Geometry_isMor`). -/
abbrev IsE0Mor {X N : Type} [TopologicalSpace X] [TopologicalSpace N] [ChartedSpace E0Y X]
    [ChartedSpace E0Y N] (f : X → N) (W : Set X) : Prop :=
  ChartedSpace.LiftPropOn e0Groupoid.IsLocalStructomorphWithinAt f W

/-- The vertex `(v, 0)` of `𝔼₀` in the model space `Y = 𝕄 ⊕ 𝔼₀`. -/
noncomputable def yVertex (v : ℝ) : E0Y := paperInY (vertex v)

/-- The spear `spear v R` in the model space `Y`. -/
noncomputable def spearY (v R : ℝ) : Set E0Y := paperInY '' spear v R

/-- The axis point `(v + t, 0)` in `Y`. -/
noncomputable def yAxis (v t : ℝ) : E0Y := paperInY ((v + t, 0) : E0)

variable {M : Type} [TopologicalSpace M] [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]

/-- **A spear neighbourhood around the BTZ line through `p`, of vertex `p` and radius `R`**
(B21 Def 2.1, `BTZ_1.tex:611–620`): a subset `U = ψ(S)` of `M`, `S = J⁺((v,0)) ∩ {r ≤ R}` the
spear of `𝔼₀`, for an injective `𝔼₀`-morphism `ψ` defined on an open neighbourhood `W` of `S` in
`Y`, sending the vertex to `p`. The paper's « singular `𝔼`-isomorphism `φ : 𝒰 → 𝒱` » is
`ψ⁻¹`; the vertex's `τ`-coordinate `v` is free (the paper's `(−2R, 0, 0)` is a normalisation by a
`τ`-translation, and is inconsistent with its own head formula: finding). -/
structure IsSpearNbhd (p : M) (R : ℝ) (U : Set M) : Prop where
  pos : 0 < R
  /-- B21 Def 2.1's sentence « the boundary of `𝒰` is the union of the head and the shaft »
  (l.617), read as part of the definition (WP-46b fixer round 2, audit option (a)): given
  `chart`, it is **equivalent** to `IsClosed U` (`frontier_spearImage_eq_iff_isClosed`, no global
  hypothesis; then `IsSpearNbhd.frontier_eq`), and it is **automatic** in a globally hyperbolic `M`
  (`isClosed_spearImage`, `IsSpearNbhd.of_chart`, `isSpearNbhd_iff_chart`). -/
  isClosed : IsClosed U
  chart : ∃ (v : ℝ) (W : Set E0Y) (ψ : E0Y → M), IsOpen W ∧ spearY v R ⊆ W ∧ IsE0Mor ψ W ∧
    InjOn ψ W ∧ ψ (yVertex v) = p ∧ U = ψ '' spearY v R

/-- **A full future BTZ ray from `p`** (`RamcovGX.tex:2352`, « the singular locus contains full
future BTZ rays »): `γ(t) = ψ(v + t, 0)` for an injective `𝔼₀`-morphism `ψ` defined on an open
neighbourhood of the **whole** model ray `{(v + t, 0) : t ≥ 0}` — the ray is complete for the
affine parameter of the BTZ line, which the morphism preserves. `γ 0 = p`. The paper's
undefined « full future BTZ ray » is read so by DEC-125 (b) (`RamcovGX.tex:2352`). -/
def IsFullFutureBTZRay (p : M) (γ : ℝ → M) : Prop :=
  ∃ (v : ℝ) (W : Set E0Y) (ψ : E0Y → M), IsOpen W ∧ (∀ t, 0 ≤ t → yAxis v t ∈ W) ∧
    IsE0Mor ψ W ∧ InjOn ψ W ∧ ψ (yVertex v) = p ∧ ∀ t, γ t = ψ (yAxis v t)

end Manifold

/-! ### §2a Transferring the causal relations of `𝔼₀` along `𝔼₀`-morphisms -/

section Transfer

open E0CBG

theorem chartImage_refl {X : Type*} [TopologicalSpace X] (V : Opens X) :
    Causal.chartImage (OpenPartialHomeomorph.refl X) V = V := by
  apply SetLike.coe_injective
  rw [Causal.coe_chartImage]
  simp

/-- On the model `Y` charted over itself, the charted causality is the model causality `D`. -/
theorem ceY_le_iff {V : Opens E0Y} {a b : E0Y} (ha : a ∈ V) (hb : b ∈ V) :
    (CE E0Y).le V a b ↔ E0LM.D.le V a b := by
  have h := Causal.CBG.chartedCausality_chartIso (M := E0Y) (G := e0Groupoid)
    E0.chartIso_mem_e0Groupoid E0.absolutelyMinimalOn_YBTZ a V
    (fun x _ => by simp [Causal.chartSource]) a ha b hb
  rw [chartAt_self_eq, chartImage_refl] at h
  exact h.1

/-- The relations of `𝔼₀` (paper coordinates) are those of `D` on `Y` through `paperInY`. -/
theorem D_le_of_le {U : Opens E0} {x y : E0} (h : causality.le U x y) :
    E0LM.D.le (Causal.chartImage paperInY U) (paperInY x) (paperInY y) :=
  ((chartIso_paperInY U (fun z _ => by simp [Causal.chartSource]) x (causality.le_mem_left h) y
    (causality.le_mem_right h)).1).1 h

/-- **An `𝔼₀`-morphism maps `D`-relations inside its domain to relations of the target.** -/
theorem le_of_isE0Mor {N : Type} [TopologicalSpace N] [ChartedSpace E0Y N]
    [HasGroupoid N e0Groupoid] {ψ : E0Y → N} {W : Set E0Y} (hW : IsOpen W) (hψ : IsE0Mor ψ W)
    {V : Opens E0Y} (hV : (V : Set E0Y) ⊆ W) {a b : E0Y} (h : E0LM.D.le V a b) :
    (CE N).le ⊤ (ψ a) (ψ b) :=
  (Causal.CBG.isEMorphismOn_of_liftPropOn E0.chartIso_mem_e0Groupoid E0.absolutelyMinimalOn_YBTZ
    (W := ⟨W, hW⟩) hψ).map_le V ⊤ hV (fun _ _ => trivial)
    ((ceY_le_iff (E0LM.D.le_mem_left h) (E0LM.D.le_mem_right h)).2 h)

/-- **An `𝔼₀`-morphism maps relations of `𝔼₀` inside (the preimage of) its domain to relations of
the target.** -/
theorem le_of_isE0Mor_paper {N : Type} [TopologicalSpace N] [ChartedSpace E0Y N]
    [HasGroupoid N e0Groupoid] {ψ : E0Y → N} {W : Set E0Y} (hW : IsOpen W) (hψ : IsE0Mor ψ W)
    {U : Opens E0} (hU : (U : Set E0) ⊆ paperInY ⁻¹' W) {x y : E0} (h : causality.le U x y) :
    (CE N).le ⊤ (ψ (paperInY x)) (ψ (paperInY y)) := by
  refine le_of_isE0Mor hW hψ ?_ (D_le_of_le h)
  rw [Causal.coe_chartImage]
  rintro _ ⟨z, ⟨-, hz⟩, rfl⟩
  exact hU hz

theorem continuous_paperInY : Continuous paperInY := by
  rw [← continuousOn_univ, ← paperInY_source]; exact paperInY.continuousOn

theorem isOpen_paperInY_image {A : Set E0} (hA : IsOpen A) : IsOpen (paperInY '' A) := by
  have := paperInY.isOpen_image_source_inter hA
  rwa [paperInY_source, univ_inter] at this

/-- The spear `spearY v R` is closed in the model `Y` (`paperInY = Sum.inr ∘ toPaper.symm` is a
closed embedding). -/
theorem isClosed_spearY (v R : ℝ) : IsClosed (spearY v R) := by
  have h : (⇑paperInY : E0 → E0Y) = Sum.inr ∘ GX.E0.toPaper.symm := funext paperInY_apply
  rw [spearY, h]
  exact (Topology.IsClosedEmbedding.inr.comp GX.E0.toPaper.symm.isClosedEmbedding).isClosedMap _
    (isClosed_spear v R)

theorem yAxis_mem_e0SingY (v t : ℝ) : yAxis v t ∈ e0SingY 0 := by
  rw [yAxis, paperInY_apply, E0LM.inr_mem_e0SingY_zero_iff, Homeomorph.apply_symm_apply]
  rfl

theorem yAxis_zero (v : ℝ) : yAxis v 0 = yVertex v := by
  simp [yAxis, yVertex, vertex]

theorem yAxis_injective (v : ℝ) : Injective (yAxis v) := by
  intro s t h
  have h1 := paperInY.injOn (by simp) (by simp) h
  simp only [Prod.mk.injEq, add_right_inj, and_true] at h1
  exact h1

theorem continuous_yAxis (v : ℝ) : Continuous (yAxis v) :=
  continuous_paperInY.comp ((continuous_const.add continuous_id).prodMk continuous_const)

end Transfer

/-! ### §2b A spear neighbourhood gives a full future BTZ ray; properties of full rays -/

section Rays

open E0CBG

variable {M : Type} [TopologicalSpace M] [ChartedSpace E0Y M]

theorem yAxis_mem_spearY {v R t : ℝ} (hR : 0 ≤ R) (ht : 0 ≤ t) : yAxis v t ∈ spearY v R :=
  ⟨_, axis_mem_spear hR (by linarith), rfl⟩

/-- **A spear neighbourhood of vertex `p` contains a full future BTZ ray from `p`** (Def 2.1:
« a neighbourhood of `]p, +∞[` »). -/
theorem IsSpearNbhd.exists_ray {p : M} {R : ℝ} {U : Set M} (h : IsSpearNbhd p R U) :
    ∃ γ : ℝ → M, IsFullFutureBTZRay p γ ∧ ∀ t, 0 ≤ t → γ t ∈ U := by
  obtain ⟨v, W, ψ, hW, hSW, hψ, hinj, hp, rfl⟩ := h.chart
  refine ⟨fun t => ψ (yAxis v t), ⟨v, W, ψ, hW, fun t ht => hSW (yAxis_mem_spearY h.pos.le ht),
    hψ, hinj, hp, fun _ => rfl⟩, fun t ht => ⟨_, yAxis_mem_spearY h.pos.le ht, rfl⟩⟩

/-- **`U` is a neighbourhood of the open ray `]p, +∞[`**: the interior `{f > v, r < R}` of the
spear is open, contains the axis points above the vertex, and `ψ` is an open map on `W`. -/
theorem IsSpearNbhd.exists_ray_mem_nhds [HasGroupoid M e0Groupoid] {p : M} {R : ℝ} {U : Set M} (h : IsSpearNbhd p R U) :
    ∃ γ : ℝ → M, IsFullFutureBTZRay p γ ∧ ∀ t, 0 < t → U ∈ 𝓝 (γ t) := by
  obtain ⟨v, W, ψ, hW, hSW, hψ, hinj, hp, rfl⟩ := h.chart
  refine ⟨fun t => ψ (yAxis v t), ⟨v, W, ψ, hW,
    fun t ht => hSW (yAxis_mem_spearY h.pos.le ht), hψ, hinj, hp, fun _ => rfl⟩, fun t ht => ?_⟩
  set O : Set E0 := {x | v < fcoord x ∧ rad x < R} with hOdef
  have hOo : IsOpen O := (isOpen_lt continuous_const continuous_fcoord).inter
    (isOpen_lt continuous_rad continuous_const)
  have hOS : O ⊆ spear v R := fun x hx => ⟨hx.1.le, hx.2.le⟩
  have hPo : IsOpen (paperInY '' O) := by
    have := paperInY.isOpen_image_source_inter hOo
    rwa [paperInY_source, univ_inter] at this
  have hPW : paperInY '' O ⊆ W := fun _ hy => hSW (image_mono hOS hy)
  have hE := Causal.CBG.isEMorphismOn_of_liftPropOn E0.chartIso_mem_e0Groupoid
    E0.absolutelyMinimalOn_YBTZ (W := ⟨W, hW⟩) hψ
  have hopen := hE.isOpen_image ⟨_, hPo⟩ hPW
  have hmem : yAxis v t ∈ paperInY '' O := by
    refine ⟨((v + t, 0) : E0), ⟨?_, ?_⟩, rfl⟩
    · have h0 : rad (((v + t, 0) : E0)) = 0 := rad_eq_zero.2 rfl
      simp only [fcoord, h0]; linarith
    · rw [rad_eq_zero.2 rfl]; exact h.pos
  exact Filter.mem_of_superset (hopen.mem_nhds (mem_image_of_mem ψ hmem))
    (image_mono (image_mono hOS))

namespace IsFullFutureBTZRay

variable {p : M} {γ : ℝ → M}

theorem zero (h : IsFullFutureBTZRay p γ) : γ 0 = p := by
  obtain ⟨v, W, ψ, -, -, -, -, hp, hγ⟩ := h
  rw [hγ, yAxis_zero, hp]

/-- The ray lies in the BTZ locus `sing₀(M)` (morphisms preserve the type of a point). -/
theorem mem_S0 (h : IsFullFutureBTZRay p γ) {t : ℝ} (ht : 0 ≤ t) : γ t ∈ S0 M := by
  obtain ⟨v, W, ψ, hW, hray, hψ, -, -, hγ⟩ := h
  rw [hγ]
  refine (Causal.CBG.mem_chartedSing_iff_of_liftPropOn e0_sing_mem hW hψ (hray t ht)
    le_rfl).1 ?_
  show chartAt E0Y (yAxis v t) (yAxis v t) ∈ e0SingY 0
  rw [chartAt_self_eq]
  exact yAxis_mem_e0SingY v t

/-- The ray is injective. -/
theorem injOn (h : IsFullFutureBTZRay p γ) : InjOn γ (Ici 0) := by
  obtain ⟨v, W, ψ, -, hray, -, hinj, -, hγ⟩ := h
  intro s hs t ht hst
  rw [hγ, hγ] at hst
  exact yAxis_injective v (hinj (hray s hs) (hray t ht) hst)

/-- The ray is continuous. -/
theorem continuousOn (h : IsFullFutureBTZRay p γ) : ContinuousOn γ (Ici 0) := by
  obtain ⟨v, W, ψ, -, hray, hψ, -, -, hγ⟩ := h
  have hγ' : γ = ψ ∘ yAxis v := funext hγ
  rw [hγ']
  have hψc : ContinuousOn ψ W := fun x hx => (hψ x hx).continuousWithinAt
  exact hψc.comp (continuous_yAxis v).continuousOn (fun t ht => hray t ht)

/-- **The ray is future directed**: `γ s ≤ γ t` for `0 ≤ s ≤ t`. -/
theorem le [HasGroupoid M e0Groupoid] (h : IsFullFutureBTZRay p γ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (CE M).le ⊤ (γ s) (γ t) := by
  obtain ⟨v, W, ψ, hW, hray, hψ, -, -, hγ⟩ := h
  rw [hγ, hγ]
  set U : Opens E0 := ⟨paperInY ⁻¹' W, hW.preimage continuous_paperInY⟩
  refine le_of_isE0Mor_paper hW hψ (U := U) subset_rfl ?_
  refine le_vertical (by linarith) fun r hr => ?_
  show paperInY ((v + s + r * (v + t - (v + s)), 0) : E0) ∈ W
  have : v + s + r * (v + t - (v + s)) = v + (s + r * (t - s)) := by ring
  rw [this]
  exact hray _ (by nlinarith [hr.1, hr.2])

end IsFullFutureBTZRay

end Rays

/-- **Non-vacuity**: in the model itself (`M = Y`), the spear `spearY v R` is a spear neighbourhood
of the vertex (`ψ = id`). -/
theorem isSpearNbhd_model (v : ℝ) {R : ℝ} (hR : 0 < R) :
    IsSpearNbhd (M := E0Y) (yVertex v) R (spearY v R) :=
  ⟨hR, isClosed_spearY v R, v, univ, id, isOpen_univ, subset_univ _,
    Causal.CBG.liftPropOn_id isOpen_univ, injOn_id _, rfl, (image_id _).symm⟩

/-! ### §2c A chart cylinder at a BTZ point -/

section CylChart

open E0CBG

variable {M : Type} [TopologicalSpace M] [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]

/-- **A chart cylinder at a BTZ point** (the first step of the proof of B21 Lemma 2.3, « a
neighbourhood `𝒰̄` of `p` isomorphic to `{τ ∈ [τ₁, R/2], r ≤ R}` »): every BTZ point `p` is the
image of the axis point `(v,0)` under an injective `𝔼₀`-morphism `ψ` (the inverse of the preferred
chart) defined on a neighbourhood of a cylinder `{|τ − v| < ε, r < ε}` of `𝔼₀`. -/
theorem exists_cyl_chart {p : M} (hp : p ∈ S0 M) :
    ∃ (v ε : ℝ) (W : Set E0Y) (ψ : E0Y → M), 0 < ε ∧ IsOpen W ∧
      paperInY '' cyl (v - ε) (v + ε) ε ⊆ W ∧ IsE0Mor ψ W ∧ InjOn ψ W ∧ ψ (yVertex v) = p := by
  set κ := chartAt E0Y p with hκ
  have hκp : κ p ∈ e0SingY 0 := hp
  obtain ⟨x, hx, hax⟩ := E0LM.mem_e0SingY_zero_iff.1 hκp
  set w := E0.toPaper x with hw
  have hwv : w = vertex w.1 := Prod.ext rfl hax
  have hpw : paperInY w = κ p := by
    rw [paperInY_apply, hw, Homeomorph.symm_apply_apply, hx]
  have hT : IsOpen (paperInY ⁻¹' κ.target) := κ.open_target.preimage continuous_paperInY
  have hwT : w ∈ paperInY ⁻¹' κ.target := by
    show paperInY w ∈ κ.target
    rw [hpw]; exact κ.map_source (mem_chart_source E0Y p)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hT w hwT
  have hQ : ∀ y : E0Y, e0Groupoid.IsLocalStructomorphWithinAt id univ y := fun y _ =>
    ⟨OpenPartialHomeomorph.refl E0Y, e0Groupoid.id_mem, fun _ _ => rfl, trivial⟩
  refine ⟨w.1, δ / 2, κ.target, κ.symm, by linarith, κ.open_target, ?_,
    e0Groupoid.isLocalStructomorphWithinAt_localInvariantProp.liftPropOn_chart_symm hQ,
    κ.symm.injOn, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    refine hball ?_
    rw [Metric.mem_ball, Prod.dist_eq]
    refine max_lt ?_ ?_
    · rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hy.1, hy.2.1]
    · have h0 : w.2 = 0 := hax
      rw [h0, dist_zero_right]
      exact hy.2.2.trans (by linarith)
  · show κ.symm (paperInY (vertex w.1)) = p
    rw [← hwv, hpw, κ.left_inv (mem_chart_source E0Y p)]

end CylChart

/-! ### §3 Cauchy-maximality (DEC-77(c)) and universality over Cauchy sub-developments -/

section CauchyMaximal

open E0CBG

/-- **Cauchy-maximality of an `𝔼₀`-manifold** (B21 « Cauchy-maximal », DEC-77(c)): every Cauchy
embedding of `M` into an `𝔼₀`-manifold (Hausdorff, connected, second countable) which is an
`𝔼₀`-morphism is bijective. This is `Dev.IsETTMaximal` of `M` as a development of itself
(`isE0CauchyMaximal_iff_isETTMaximal`), stated without the CBG geometry's parameters. -/
def IsE0CauchyMaximal (M : Type) [TopologicalSpace M] [ChartedSpace E0Y M] : Prop :=
  ∀ (N : Type) [TopologicalSpace N] [T2Space N] [ConnectedSpace N] [SecondCountableTopology N]
    [ChartedSpace E0Y N] [HasGroupoid N e0Groupoid] (f : M → N),
    Causal.IsCauchyEmbedding (CE M) (CE N) f → IsE0Mor f univ → Bijective f

variable
  (hLine : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [SecondCountableTopology M] [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid],
    E0LM.E0GlobalBTZ (Causal.CBG.chartedCausality E0LM.D M) (Causal.CBG.chartedSing e0SingY M 0))
  (hSC : ∀ {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [ChartedSpace E0Y M]
    [HasGroupoid M e0Groupoid], (Causal.CBG.chartedCausality E0LM.D M).GloballyHyperbolic →
    ∀ S : Set M, (Causal.CBG.chartedCausality E0LM.D M).IsCauchySurface S →
    SecondCountableTopology S → SecondCountableTopology M)

/-- The causality of a structure of `e0Geometry` is the charted causality of its atlas. -/
theorem e0Geometry_causality_str {X : Type} [TopologicalSpace X]
    (s : (e0Geometry hLine hSC).Str X) :
    (e0Geometry hLine hSC).causality s = @Causal.CBG.chartedCausality E0Y _ E0LM.D X _ s.1 :=
  rfl

/-- The morphisms of `e0Geometry` between two structures are the `𝔼₀`-morphisms of the atlases. -/
theorem e0Geometry_isMor_str {X N : Type} [TopologicalSpace X] [TopologicalSpace N]
    (s : (e0Geometry hLine hSC).Str X) (t : (e0Geometry hLine hSC).Str N) (W : Opens X)
    (f : X → N) :
    (e0Geometry hLine hSC).IsMor s t W f ↔ @IsE0Mor X N _ _ s.1 t.1 f W :=
  Iff.rfl

/-- An `𝔼₀`-morphism is an abstract `𝕄≥0`-morphism of the charted causalities. -/
theorem isEMorphismOn_of_isE0Mor {X N : Type} [TopologicalSpace X] [TopologicalSpace N]
    [ChartedSpace E0Y X] [ChartedSpace E0Y N] [HasGroupoid X e0Groupoid]
    [HasGroupoid N e0Groupoid] {f : X → N} {W : Opens X} (hf : IsE0Mor f W) :
    Causal.IsEMorphismOn (CE X) (CE N) W f :=
  Causal.CBG.isEMorphismOn_of_liftPropOn E0.chartIso_mem_e0Groupoid E0.absolutelyMinimalOn_YBTZ hf

variable {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [SecondCountableTopology M]
  [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]

/-- **DEC-77(c)**: `IsE0CauchyMaximal M` is `Dev.IsETTMaximal` of `M` as its own development in the
CBG geometry `E0CBG.e0Geometry` (whose structures are the `𝔼₀`-atlases, morphisms the
`𝔼₀`-morphisms, causality the charted one). -/
theorem isE0CauchyMaximal_iff_isETTMaximal (hGH : (CE M).GloballyHyperbolic) {S : Set M}
    (hS : (CE M).IsCauchySurface S) :
    IsE0CauchyMaximal M ↔
      (Causal.CBG.Dev.self (e0Geometry hLine hSC) (e0Str hLine hSC M) hGH hS).IsETTMaximal := by
  constructor
  · intro hmax N f hf
    letI : ChartedSpace E0Y N.carrier := N.str.1
    haveI : HasGroupoid N.carrier e0Groupoid := N.str.2
    obtain ⟨hf1, hf2⟩ := hf
    have hfe : f = N.emb := hf2
    subst hfe
    exact hmax N.carrier N.emb N.isCauchyEmbedding hf1
  · intro hETT N _ _ _ _ _ _ f hf hfm
    let Nd : Causal.CBG.Dev (e0Geometry hLine hSC).toPreGeometry (e0Str hLine hSC M) :=
      { carrier := N
        str := e0Str hLine hSC N
        emb := f
        isCauchyEmbedding := hf
        isMor := hfm }
    exact hETT Nd f ⟨hfm, rfl⟩

/-- **Cauchy-maximality gives universality over every Cauchy sub-development** (the step hidden in
B21 Lemma 2.3's « since `M` is Cauchy-maximal, `M₂` embeds into `M` », SCOPE R2(c)): if `M₀`
Cauchy-embeds in a Cauchy-maximal `M` by an `𝔼₀`-morphism `ι`, every Cauchy development `N` of
`M₀` maps into `M` by an injective `𝔼₀`-morphism over `ι`. Proof: CBG (`e0_cbg`) gives the
universal development `M̄` of `M₀`; the morphism `g : M → M̄` over `M₀` is a Cauchy embedding
(Sbierski Lemma 3.3, `sbierski_lemma_3_3`, Levin's time function on `M`), hence bijective by
Cauchy-maximality; then `F = g⁻¹ ∘ h` for `h : N → M̄`, injective by Lemma 3.3 on `N`. -/
theorem IsE0CauchyMaximal.exists_morphism_of_dev (hmax : IsE0CauchyMaximal M)
    {M₀ : Type} [TopologicalSpace M₀] [T2Space M₀] [ConnectedSpace M₀] [SecondCountableTopology M₀]
    [ChartedSpace E0Y M₀] [HasGroupoid M₀ e0Groupoid] (ι : M₀ → M)
    (hι : Causal.IsCauchyEmbedding (CE M₀) (CE M) ι) (hιm : IsE0Mor ι univ)
    (N : Causal.CBG.Dev (e0Geometry hLine hSC).toPreGeometry (e0Str hLine hSC M₀)) :
    ∃ F : N.carrier → M, (e0Geometry hLine hSC).IsMor N.str (e0Str hLine hSC M) ⊤ F ∧
      F ∘ N.emb = ι ∧ Injective F := by
  obtain ⟨S₀, hS₀, -⟩ := hι.exists_cauchy
  obtain ⟨Mbar, hU⟩ := e0_cbg hLine hSC hι.globallyHyperbolic_source hS₀
  have hGM : (CE M).GloballyHyperbolic := hι.globallyHyperbolic_target
  let DM : Causal.CBG.Dev (e0Geometry hLine hSC).toPreGeometry (e0Str hLine hSC M₀) :=
    { carrier := M
      str := e0Str hLine hSC M
      emb := ι
      isCauchyEmbedding := hι
      isMor := hιm }
  obtain ⟨g, hg, -⟩ := hU DM
  letI : ChartedSpace E0Y Mbar.carrier := Mbar.str.1
  haveI : HasGroupoid Mbar.carrier e0Groupoid := Mbar.str.2
  have hGbar : (CE Mbar.carrier).GloballyHyperbolic := Mbar.isCauchyEmbedding.globallyHyperbolic_target
  -- `g` is a Cauchy embedding
  have hgm : IsE0Mor g (⊤ : Opens M) := hg.1
  have hgE : Causal.IsEMorphism (CE M) (CE Mbar.carrier) g := isEMorphismOn_of_isE0Mor hgm
  have hιS : (CE M).IsCauchySurface (ι '' S₀) := hι.isCauchySurface_image hS₀
  have hgS : g '' (ι '' S₀) = Mbar.emb '' S₀ := by
    rw [image_image]; exact image_congr fun x _ => congrFun hg.2 x
  have hbarS : (CE Mbar.carrier).IsCauchySurface (Mbar.emb '' S₀) :=
    Mbar.isCauchyEmbedding.isCauchySurface_image hS₀
  obtain ⟨T, hTc, hT⟩ := E0LM.e0_timeFunction hGM
  have hgC : Causal.IsCauchyEmbedding (CE M) (CE Mbar.carrier) g := by
    refine Causal.CBG.sbierski_lemma_3_3 hGM hGbar hgE hTc hT hιS (by rw [hgS]; exact hbarS) ?_
      E0LM.e0_causallyArcConnected (E0LM.e0_curvesExtend hGbar)
    rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩ hxy
    have hxy' : Mbar.emb x = Mbar.emb y := by
      have h1 := congrFun hg.2 x; have h2 := congrFun hg.2 y
      simp only [comp_apply] at h1 h2
      rw [← h1, ← h2]; exact hxy
    rw [Mbar.isCauchyEmbedding.injective hxy']
  have hbij : Bijective g := hmax Mbar.carrier g hgC hg.1
  -- the inverse of `g` is a morphism
  haveI : Nonempty M := ⟨ι (Classical.arbitrary M₀)⟩
  have hinv := (e0Geometry hLine hSC).isMor_inv hg.1 hbij.1.injOn
  have htop : ((e0Geometry hLine hSC).isEMorphismOn_of_isMor hg.1).imageOpens ⊤ le_rfl = ⊤ := by
    apply SetLike.coe_injective
    rw [Causal.IsEMorphismOn.coe_imageOpens, Opens.coe_top, image_univ_of_surjective hbij.2,
      Opens.coe_top]
  rw [htop] at hinv
  set k := invFunOn g ((⊤ : Opens M) : Set M) with hk
  have hkg : k ∘ g = id := funext fun x =>
    hbij.1.injOn.leftInvOn_invFunOn (show x ∈ ((⊤ : Opens M) : Set M) from trivial)
  obtain ⟨h, hh, -⟩ := hU N
  refine ⟨k ∘ h, (e0Geometry hLine hSC).isMor_comp hinv hh.1 (fun _ _ => trivial), ?_, ?_⟩
  · rw [comp_assoc, hh.2, ← hg.2, ← comp_assoc, hkg, id_comp]
  · -- injectivity: Lemma 3.3 on `N`
    letI : ChartedSpace E0Y N.carrier := N.str.1
    haveI : HasGroupoid N.carrier e0Groupoid := N.str.2
    have hGN : (CE N.carrier).GloballyHyperbolic := N.isCauchyEmbedding.globallyHyperbolic_target
    have hFm : (e0Geometry hLine hSC).IsMor N.str (e0Str hLine hSC M) ⊤ (k ∘ h) :=
      (e0Geometry hLine hSC).isMor_comp hinv hh.1 (fun _ _ => trivial)
    have hFm' : IsE0Mor (k ∘ h) (⊤ : Opens N.carrier) := hFm
    have hFE : Causal.IsEMorphism (CE N.carrier) (CE M) (k ∘ h) := isEMorphismOn_of_isE0Mor hFm'
    have hFι : (k ∘ h) ∘ N.emb = ι := by
      rw [comp_assoc, hh.2, ← hg.2, ← comp_assoc, hkg, id_comp]
    obtain ⟨TN, hTNc, hTN⟩ := E0LM.e0_timeFunction hGN
    have hNS : (CE N.carrier).IsCauchySurface (N.emb '' S₀) :=
      N.isCauchyEmbedding.isCauchySurface_image hS₀
    refine Causal.CBG.injective_of_mapsTo_cauchy hFE hTNc hTN hNS ?_ hιS ?_ hGM.1
      E0LM.e0_causallyArcConnected (E0LM.e0_curvesExtend hGM)
    · rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩ hxy
      have h1 := congrFun hFι x; have h2 := congrFun hFι y
      simp only [comp_apply] at h1 h2 hxy
      rw [hι.injective (h1.symm.trans (hxy.trans h2))]
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨x, hx, (congrFun hFι x).symm⟩

end CauchyMaximal

/-! ### §4a The pieces of the gluing of Lemma 2.3: `M₀ = M ∖ J⁺(φ⁻¹Π)` and the spear piece

Normalisation (BTZ_1.tex:643–654, with the radii fixed): the chart `κ = chartAt p` reads a cylinder
`{|τ − v| < ε, r < ε}` around `p = κ⁻¹(v, 0)`, causally convex in `M` (`CylChartData`; B21's
« small enough so that `φ⁻¹Π` is acausal in `M` », l.647, in the stronger form the proof uses). The disc is
`Π = {τ = v + ε/2, r ≤ ε/4}` (`glueDisc`), `M₀ = M ∖ J⁺(κ⁻¹Π)` (`CylChartData.W0`), the spear piece is the
open `𝒫 = {f > v − ε/2, r < ε/4}` of `𝔼₀` (`gluePaper`, containing the spear `spear v (ε/8)`),
glued to `M₀` along `𝒫 ∩ cyl ∩ κ(M₀)`, which by the convexity is exactly
`𝒫 ∩ cyl ∩ {τ < v + ε/2}` (`CylChartData.mem_U10_iff`). That overlap lies in the compact `glueF ⊆ cyl` (points of
`𝒫 ∩ cyl` above `Π` are in `J⁺(κ⁻¹Π)`), which is what makes the gluing Hausdorff. -/

section GluePieces

open E0CBG

variable {M : Type} [TopologicalSpace M] [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]

/-- The open set `κ⁻¹(A) = source ∩ κ⁻¹(paperInY A)` of `M`, for `κ = chartAt p`. -/
noncomputable def chartOpen (p : M) (A : Opens E0) : Opens M :=
  ⟨(chartAt E0Y p).source ∩ chartAt E0Y p ⁻¹' (paperInY '' (A : Set E0)),
    (chartAt E0Y p).isOpen_inter_preimage (isOpen_paperInY_image A.isOpen)⟩

omit [HasGroupoid M e0Groupoid] in
theorem mem_chartOpen {p : M} {A : Opens E0}
    (hA : paperInY '' (A : Set E0) ⊆ (chartAt E0Y p).target) {x : E0} (hx : x ∈ A) :
    (chartAt E0Y p).symm (paperInY x) ∈ chartOpen p A :=
  ⟨(chartAt E0Y p).map_target (hA ⟨x, hx, rfl⟩), by
    show chartAt E0Y p ((chartAt E0Y p).symm (paperInY x)) ∈ paperInY '' (A : Set E0)
    rw [(chartAt E0Y p).right_inv (hA ⟨x, hx, rfl⟩)]; exact ⟨x, hx, rfl⟩⟩

omit [HasGroupoid M e0Groupoid] in
/-- A point of `chartOpen p A` is `κ⁻¹(paperInY x)` for some `x ∈ A`. -/
theorem exists_of_mem_chartOpen {p : M} {A : Opens E0} {z : M} (hz : z ∈ chartOpen p A) :
    ∃ x ∈ A, (chartAt E0Y p).symm (paperInY x) = z := by
  obtain ⟨hzs, x, hx, hxz⟩ := hz
  exact ⟨x, hx, by rw [hxz]; exact (chartAt E0Y p).left_inv hzs⟩

/-- **The relations of `M` inside the chart, read in `𝔼₀`**: for `A` open in `𝔼₀` inside the
chart target, `κ⁻¹ x ≤ κ⁻¹ y` in `κ⁻¹(A)` iff `x ≤ y` in `A`
(`Causal.CBG.chartedCausality_chartIso` composed with `chartIso_paperInY`). -/
theorem chart_le_iff (p : M) {A : Opens E0}
    (hA : paperInY '' (A : Set E0) ⊆ (chartAt E0Y p).target) {x y : E0} (hx : x ∈ A)
    (hy : y ∈ A) :
    (CE M).le (chartOpen p A) ((chartAt E0Y p).symm (paperInY x))
        ((chartAt E0Y p).symm (paperInY y)) ↔ causality.le A x y := by
  have hc := Causal.CBG.chartedCausality_chartIso (M := M) (G := e0Groupoid)
    E0.chartIso_mem_e0Groupoid E0.absolutelyMinimalOn_YBTZ p
  have h1 := (hc (chartOpen p A) (fun z hz => hz.1) _ (mem_chartOpen hA hx) _
    (mem_chartOpen hA hy)).1
  rw [(chartAt E0Y p).right_inv (hA ⟨x, hx, rfl⟩),
    (chartAt E0Y p).right_inv (hA ⟨y, hy, rfl⟩)] at h1
  have himg : Causal.chartImage (chartAt E0Y p) (chartOpen p A) =
      Causal.chartImage paperInY A := by
    apply SetLike.coe_injective
    rw [Causal.coe_chartImage, Causal.coe_chartImage, paperInY_source, univ_inter]
    ext u
    constructor
    · rintro ⟨z, ⟨-, hzs, hzA⟩, rfl⟩; exact hzA
    · rintro ⟨x', hx', rfl⟩
      exact ⟨_, ⟨(mem_chartOpen hA hx').1, mem_chartOpen hA hx'⟩,
        (chartAt E0Y p).right_inv (hA ⟨x', hx', rfl⟩)⟩
  rw [himg] at h1
  exact h1.trans ((chartIso_paperInY A (fun z _ => by simp [Causal.chartSource]) x hx y hy).1).symm

/-- **The chart cylinder at a BTZ point** (data form of `exists_cyl_chart`, with the chart
`κ = chartAt p` itself): `κ⁻¹` is defined on the cylinder `{|τ − v| < ε, r < ε}` and sends its
axis point `(v, 0)` to `p`; and — B21's normalisation « one can take this neighbourhood small
enough so that `φ⁻¹Π` is acausal in `M` » (`BTZ_1.tex:647`), here in the stronger form used by
the proof — **the chart cylinder `κ⁻¹(cyl)` is causally convex in `M`** (`convex`; obtained by
strong causality of the globally hyperbolic `M` in `exists_cylChartData`). Consequences:
the relations of `M` between points of the cylinder are those of `𝔼₀` (`CylChartData.le_model`),
`κ⁻¹Π` is acausal (`CylChartData.isAcausal_K`) and the overlap of the gluing is exactly
`𝒫 ∩ cyl ∩ {τ < v + ε/2}` (`CylChartData.mem_W0_iff`, `CylChartData.mem_U10_iff`). -/
structure CylChartData (p : M) where
  v : ℝ
  ε : ℝ
  pos : 0 < ε
  cyl_sub : paperInY '' cyl (v - ε) (v + ε) ε ⊆ (chartAt E0Y p).target
  vertex_eq : (chartAt E0Y p).symm (yVertex v) = p
  convex : (CE M).CausallyConvexIn
    ((chartAt E0Y p).symm '' (paperInY '' cyl (v - ε) (v + ε) ε)) ⊤

omit [HasGroupoid M e0Groupoid] in
/-- A cylinder `{|τ − τ_w| < ε, r < ε}` around an axis point `w` lies in the ball of radius `η > ε`. -/
theorem cyl_subset_ball {w : E0} (hw : w.2 = 0) {ε η : ℝ} (h : ε < η) :
    cyl (w.1 - ε) (w.1 + ε) ε ⊆ Metric.ball w η := by
  intro y hy
  rw [Metric.mem_ball, Prod.dist_eq]
  refine max_lt ?_ ?_
  · rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hy.1, hy.2.1]
  · rw [hw, dist_zero_right]
    exact hy.2.2.trans h

theorem cyl_mono {a b ρ a' b' ρ' : ℝ} (ha : a ≤ a') (hb : b' ≤ b) (hρ : ρ' ≤ ρ) :
    cyl a' b' ρ' ⊆ cyl a b ρ :=
  fun _ hx => ⟨ha.trans_lt hx.1, hx.2.1.trans_le hb, hx.2.2.trans_le hρ⟩

/-- Every BTZ point of a globally hyperbolic `𝔼₀`-manifold has a chart cylinder, causally convex
in `M` (`exists_cyl_chart`'s proof, keeping `κ = chartAt p`, then shrinking `ε` inside a causally
convex neighbourhood of `p` given by strong causality, `GloballyHyperbolic.stronglyCausal`; a
causal diamond of `M` between two points of the small cylinder lies in that neighbourhood, hence
in the big chart cylinder, where it is a diamond of `𝔼₀`, and cylinders of `𝔼₀` are causally
convex). -/
theorem exists_cylChartData [T2Space M] (hGH : (CE M).GloballyHyperbolic) {p : M}
    (hp : p ∈ S0 M) : Nonempty (CylChartData p) := by
  set κ := chartAt E0Y p with hκ
  have hκp : κ p ∈ e0SingY 0 := hp
  obtain ⟨x, hx, hax⟩ := E0LM.mem_e0SingY_zero_iff.1 hκp
  set w := E0.toPaper x with hw
  have hw0 : w.2 = 0 := hax
  have hwv : w = vertex w.1 := Prod.ext rfl hax
  have hpw : paperInY w = κ p := by
    rw [paperInY_apply, hw, Homeomorph.symm_apply_apply, hx]
  have hT : IsOpen (paperInY ⁻¹' κ.target) := κ.open_target.preimage continuous_paperInY
  have hwT : w ∈ paperInY ⁻¹' κ.target := by
    show paperInY w ∈ κ.target
    rw [hpw]; exact κ.map_source (mem_chart_source E0Y p)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hT w hwT
  have hsub : ∀ ε, ε < δ → paperInY '' cyl (w.1 - ε) (w.1 + ε) ε ⊆ κ.target := by
    rintro ε hε _ ⟨y, hy, rfl⟩
    exact hball (cyl_subset_ball hw0 hε hy)
  -- the big cylinder `A₁` and its chart preimage `N₁ ∋ p`
  set ε₁ := δ / 2 with hε₁
  have hε₁pos : 0 < ε₁ := by linarith
  let A₁ : Opens E0 := ⟨cyl (w.1 - ε₁) (w.1 + ε₁) ε₁, isOpen_cyl _ _ _⟩
  have hA₁ : paperInY '' (A₁ : Set E0) ⊆ κ.target := hsub ε₁ (by linarith)
  have hgw : κ.symm (paperInY w) = p := by rw [hpw, κ.left_inv (mem_chart_source E0Y p)]
  have hwA₁ : w ∈ A₁ := by
    show w ∈ cyl (w.1 - ε₁) (w.1 + ε₁) ε₁
    refine ⟨by linarith, by linarith, ?_⟩
    show ‖w.2‖ < ε₁
    rw [hw0, norm_zero]; exact hε₁pos
  have hpN : p ∈ chartOpen p A₁ := by
    have := mem_chartOpen hA₁ hwA₁; rwa [hgw] at this
  obtain ⟨V, hV, hVN, hconv⟩ := (hGH.stronglyCausal E0LM.e0_tarentin) p _
    ((chartOpen p A₁).isOpen.mem_nhds hpN)
  -- shrink to a cylinder inside `V`
  have hg : ContinuousAt (fun y : E0 => κ.symm (paperInY y)) w :=
    (κ.continuousOn_symm.continuousAt (κ.open_target.mem_nhds hwT)).comp
      continuous_paperInY.continuousAt
  have hgV : (fun y : E0 => κ.symm (paperInY y)) ⁻¹' V ∈ 𝓝 w :=
    hg.preimage_mem_nhds (by rw [hgw]; exact hV)
  obtain ⟨η, hη, hηV⟩ := Metric.mem_nhds_iff.1 hgV
  set ε := min ε₁ (η / 2) with hεdef
  have hεpos : 0 < ε := lt_min hε₁pos (by linarith)
  have hεε₁ : ε ≤ ε₁ := min_le_left _ _
  have hεη : ε < η := (min_le_right _ _).trans_lt (by linarith)
  have hcA₁ : cyl (w.1 - ε) (w.1 + ε) ε ⊆ A₁ :=
    cyl_mono (by linarith) (by linarith) hεε₁
  have hcV : ∀ y ∈ cyl (w.1 - ε) (w.1 + ε) ε, κ.symm (paperInY y) ∈ V :=
    fun y hy => hηV (cyl_subset_ball hw0 hεη hy)
  refine ⟨⟨w.1, ε, hεpos, hsub ε (by linarith), ?_, ?_⟩⟩
  · show κ.symm (paperInY (vertex w.1)) = p
    rw [← hwv, hgw]
  · refine ⟨fun _ _ => trivial, ?_⟩
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩ _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩ z hz
    obtain ⟨h1, h2⟩ := Causal.Causality.mem_diamond.1 hz
    have hzV : z ∈ V := hconv.2 _ (hcV a ha) _ (hcV b hb) hz
    obtain ⟨c, hcA, rfl⟩ := exists_of_mem_chartOpen (hVN hzV)
    have h1' := Causal.Causality.le_of_causallyConvexIn E0LM.e0_causallyArcConnected hconv hVN
      (hcV a ha) hzV h1
    have h2' := Causal.Causality.le_of_causallyConvexIn E0LM.e0_causallyArcConnected hconv hVN
      hzV (hcV b hb) h2
    rw [chart_le_iff p hA₁ (hcA₁ ha) hcA] at h1'
    rw [chart_le_iff p hA₁ hcA (hcA₁ hb)] at h2'
    exact ⟨paperInY c, ⟨c, mem_cyl_of_le ha hb h1' h2', rfl⟩, rfl⟩

/-- The disc `Π = {τ = v + ε/2, r ≤ ε/4}` of the gluing. -/
def glueDisc (v ε : ℝ) : Set E0 := disc (v + ε / 2) (ε / 4)

/-- The spear piece `𝒫 = {f > v − ε/2, r < ε/4}`, paper coordinates. -/
def gluePaper (v ε : ℝ) : Set E0 := {x | v - ε / 2 < fcoord x ∧ rad x < ε / 4}

/-- The compact `F = {v − ε/2 ≤ τ ≤ v + ε/2, r ≤ ε/4}` containing the overlap. -/
def glueF (v ε : ℝ) : Set E0 := {x | v - ε / 2 ≤ x.1 ∧ x.1 ≤ v + ε / 2 ∧ rad x ≤ ε / 4}

theorem glueDisc_eq (v ε : ℝ) :
    glueDisc v ε = ({v + ε / 2} : Set ℝ) ×ˢ Metric.closedBall (0 : ℂ) (ε / 4) := by
  ext ⟨τ, z⟩
  simp [glueDisc, disc, rad]

theorem isCompact_glueDisc (v ε : ℝ) : IsCompact (glueDisc v ε) := by
  rw [glueDisc_eq]; exact isCompact_singleton.prod (isCompact_closedBall _ _)

theorem glueF_eq (v ε : ℝ) :
    glueF v ε = Icc (v - ε / 2) (v + ε / 2) ×ˢ Metric.closedBall (0 : ℂ) (ε / 4) := by
  ext ⟨τ, z⟩
  simp [glueF, rad, and_assoc]

theorem isCompact_glueF (v ε : ℝ) : IsCompact (glueF v ε) := by
  rw [glueF_eq]; exact isCompact_Icc.prod (isCompact_closedBall _ _)

theorem glueDisc_subset_cyl {v ε : ℝ} (hε : 0 < ε) : glueDisc v ε ⊆ cyl (v - ε) (v + ε) ε :=
  fun x hx => ⟨by rw [hx.1]; linarith, by rw [hx.1]; linarith, hx.2.trans_lt (by linarith)⟩

theorem glueF_subset_cyl {v ε : ℝ} (hε : 0 < ε) : glueF v ε ⊆ cyl (v - ε) (v + ε) ε :=
  fun x hx => ⟨by linarith [hx.1], by linarith [hx.2.1], hx.2.2.trans_lt (by linarith)⟩

theorem isOpen_gluePaper (v ε : ℝ) : IsOpen (gluePaper v ε) :=
  (isOpen_lt continuous_const continuous_fcoord).inter (isOpen_lt continuous_rad continuous_const)

theorem spear_subset_gluePaper {v ε : ℝ} (hε : 0 < ε) : spear v (ε / 8) ⊆ gluePaper v ε :=
  fun x hx => ⟨by linarith [hx.1], hx.2.trans_lt (by linarith)⟩

theorem vertex_mem_gluePaper {v ε : ℝ} (hε : 0 < ε) : vertex v ∈ gluePaper v ε :=
  spear_subset_gluePaper hε (vertex_mem_spear (by linarith))

theorem vertex_mem_cyl {v ε : ℝ} (hε : 0 < ε) : vertex v ∈ cyl (v - ε) (v + ε) ε := by
  refine ⟨by simp [vertex]; linarith, by simp [vertex]; linarith, ?_⟩
  rw [rad_eq_zero.2 (vertex_mem_axis v)]; exact hε

/-- `𝒫` is connected: the image of `]v − ε/2, +∞[ × D(0, ε/4)` under `(s, z) ↦ (s + |z|/2, z)`. -/
theorem isConnected_gluePaper {v ε : ℝ} (hε : 0 < ε) : IsConnected (gluePaper v ε) := by
  have heq : gluePaper v ε =
      (fun q : ℝ × ℂ => ((q.1 + ‖q.2‖ / 2, q.2) : E0)) '' (Ioi (v - ε / 2) ×ˢ
        Metric.ball (0 : ℂ) (ε / 4)) := by
    ext ⟨τ, z⟩
    simp only [gluePaper, fcoord, rad, mem_setOf_eq, mem_image, mem_prod, mem_Ioi,
      mem_ball_zero_iff, Prod.exists, Prod.mk.injEq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨τ - ‖z‖ / 2, z, ⟨h1, h2⟩, by ring, rfl⟩
    · rintro ⟨s, z', ⟨h1, h2⟩, h3, rfl⟩
      refine ⟨?_, h2⟩
      rw [← h3]; simpa using h1
  rw [heq]
  refine (isConnected_Ioi.prod (Metric.isConnected_ball (by linarith))).image _ ?_
  exact ((continuous_fst.add (continuous_norm.comp continuous_snd |>.div_const 2)).prodMk
    continuous_snd).continuousOn

/-- **Cylinders are causally convex**, relations realised inside. -/
theorem le_of_le_top_of_mem_cyl {a b ρ : ℝ} {U : Opens E0} (hU : cyl a b ρ ⊆ U) {x y : E0}
    (hx : x ∈ cyl a b ρ) (hy : y ∈ cyl a b ρ) (h : causality.le ⊤ x y) : causality.le U x y := by
  obtain ⟨c, hc, hc0, hc1⟩ := (E0.causallyArcConnected ⊤ le_rfl x y).1.1 h
  have hmem : ∀ s ∈ Icc (0 : ℝ) 1, c s ∈ U := fun s hs => by
    have h1 : causality.le ⊤ x (c s) := by rw [← hc0]; exact hc.le_of_le le_rfl hs.1 hs.2
    have h2 : causality.le ⊤ (c s) y := by rw [← hc1]; exact hc.le_of_le hs.1 hs.2 le_rfl
    exact hU (mem_cyl_of_le hx hy h1 h2)
  exact (E0.causallyArcConnected U le_top x y).1.2
    ⟨c, Causal.CurveOn.restrict hc le_rfl le_rfl le_top hmem, hc0, hc1⟩

variable {p : M} (d : CylChartData p)

theorem isE0Mor_chartAt_symm (p : M) :
    IsE0Mor (chartAt E0Y p).symm (chartAt E0Y p).target := by
  have hQ : ∀ y : E0Y, e0Groupoid.IsLocalStructomorphWithinAt id univ y := fun y _ =>
    ⟨OpenPartialHomeomorph.refl E0Y, e0Groupoid.id_mem, fun _ _ => rfl, trivial⟩
  exact e0Groupoid.isLocalStructomorphWithinAt_localInvariantProp.liftPropOn_chart_symm hQ

omit [HasGroupoid M e0Groupoid] in
theorem CylChartData.cyl_sub' : cyl (d.v - d.ε) (d.v + d.ε) d.ε ⊆
    paperInY ⁻¹' (chartAt E0Y p).target := fun x hx => d.cyl_sub ⟨x, hx, rfl⟩

/-- **The relations of the cylinder transfer to `M`** through `κ⁻¹`. -/
theorem CylChartData.le_of_le {x y : E0} (hx : x ∈ cyl (d.v - d.ε) (d.v + d.ε) d.ε)
    (hy : y ∈ cyl (d.v - d.ε) (d.v + d.ε) d.ε) (h : causality.le ⊤ x y) :
    (CE M).le ⊤ ((chartAt E0Y p).symm (paperInY x)) ((chartAt E0Y p).symm (paperInY y)) :=
  le_of_isE0Mor_paper (chartAt E0Y p).open_target (isE0Mor_chartAt_symm p)
    (U := ⟨cyl (d.v - d.ε) (d.v + d.ε) d.ε, isOpen_cyl _ _ _⟩) d.cyl_sub'
    (le_of_le_top_of_mem_cyl subset_rfl hx hy h)

/-- The compact `κ⁻¹Π` of `M`. -/
noncomputable def CylChartData.K : Set M :=
  (chartAt E0Y p).symm '' (paperInY '' glueDisc d.v d.ε)

omit [HasGroupoid M e0Groupoid] in
theorem CylChartData.isCompact_K : IsCompact d.K := by
  rw [CylChartData.K, image_image]
  refine (isCompact_glueDisc d.v d.ε).image_of_continuousOn ?_
  exact (chartAt E0Y p).continuousOn_symm.comp continuous_paperInY.continuousOn
    fun x hx => d.cyl_sub' (glueDisc_subset_cyl d.pos hx)

/-- The set `M₀ = M ∖ J⁺(κ⁻¹Π)`. -/
def CylChartData.W0 : Set M := ((CE M).Jplus ⊤ d.K)ᶜ

theorem CylChartData.isOpen_W0 [T2Space M] (hGH : (CE M).GloballyHyperbolic) :
    IsOpen d.W0 :=
  (Causal.Causality.isClosed_Jplus_of_isCompact (hGH.isClosed_le E0LM.e0_tarentin)
    d.isCompact_K).isOpen_compl

omit [HasGroupoid M e0Groupoid] in
/-- `M₀` is a past set. -/
theorem CylChartData.mem_W0_of_le {x y : M} (hx : x ∈ d.W0) (hyx : (CE M).le ⊤ y x) :
    y ∈ d.W0 := by
  rintro ⟨k, hk, hky⟩
  exact hx ⟨k, hk, (CE M).le_trans hky hyx⟩

/-- **`p ∈ M₀`**: were `κ⁻¹(c, z) ≤ p` for a point of `Π`, the vertex being below `(c, z)` in the
cylinder, `p ≤ κ⁻¹(c, z) ≤ p`, so `(c, z)` would be the vertex. -/
theorem CylChartData.mem_W0 (hGH : (CE M).GloballyHyperbolic) : p ∈ d.W0 := by
  rintro ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, hyp⟩
  have hyc := glueDisc_subset_cyl d.pos hy
  have hvy : causality.le ⊤ (vertex d.v) y := by
    rw [le_top_iff, le_axis_iff (vertex_mem_axis d.v)]
    have h1 : y.1 = d.v + d.ε / 2 := hy.1
    have h2 : rad y ≤ d.ε / 4 := hy.2
    simp only [fcoord, vertex]; linarith [d.pos]
  have h1 := d.le_of_le (vertex_mem_cyl d.pos) hyc hvy
  have hpv : (chartAt E0Y p).symm (paperInY (vertex d.v)) = p := d.vertex_eq
  rw [hpv] at h1
  have heq := hGH.1 h1 hyp
  have h2 : paperInY y = paperInY (vertex d.v) := by
    have := (chartAt E0Y p).symm.injOn (d.cyl_sub ⟨y, hyc, rfl⟩)
      (d.cyl_sub ⟨_, vertex_mem_cyl d.pos, rfl⟩) (heq.symm.trans hpv.symm)
    exact this
  have h3 := paperInY.injOn (by simp) (by simp) h2
  have : y.1 = d.v := by rw [h3]; rfl
  have h4 : y.1 = d.v + d.ε / 2 := hy.1
  linarith [d.pos]

/-- **The points of `𝒫 ∩ cyl` whose image is in `M₀` lie in the compact `F`** (below `Π`). -/
theorem CylChartData.mem_glueF {x : E0} (hxP : x ∈ gluePaper d.v d.ε)
    (hxC : x ∈ cyl (d.v - d.ε) (d.v + d.ε) d.ε)
    (hxW : (chartAt E0Y p).symm (paperInY x) ∈ d.W0) : x ∈ glueF d.v d.ε := by
  refine ⟨?_, ?_, hxP.2.le⟩
  · have := hxP.1; simp only [fcoord] at this; linarith [rad_nonneg x]
  · by_contra hc
    push Not at hc
    have hd : ((d.v + d.ε / 2, x.2) : E0) ∈ glueDisc d.v d.ε := ⟨rfl, hxP.2.le⟩
    have hle : causality.le ⊤ ((d.v + d.ε / 2, x.2) : E0) x := le_vertical_top hc.le
    exact hxW ⟨_, ⟨_, ⟨_, hd, rfl⟩, rfl⟩,
      d.le_of_le (glueDisc_subset_cyl d.pos hd) hxC hle⟩

/-- The chart cylinder `κ⁻¹(cyl)` as an open set of `M`. -/
noncomputable def CylChartData.cylO : Opens E0 :=
  ⟨cyl (d.v - d.ε) (d.v + d.ε) d.ε, isOpen_cyl _ _ _⟩

/-- **The relations of `M` between points of the chart cylinder are those of `𝔼₀`** (the converse
of `CylChartData.le_of_le`): the cylinder is causally convex in `M` (`CylChartData.convex`), so a
relation of `M` between two of its points is realised inside it (`le_of_causallyConvexIn`), where
the chart is an isomorphism (`chart_le_iff`). -/
theorem CylChartData.le_model {x y : E0} (hx : x ∈ cyl (d.v - d.ε) (d.v + d.ε) d.ε)
    (hy : y ∈ cyl (d.v - d.ε) (d.v + d.ε) d.ε)
    (h : (CE M).le ⊤ ((chartAt E0Y p).symm (paperInY x)) ((chartAt E0Y p).symm (paperInY y))) :
    causality.le d.cylO x y := by
  have hsub : (chartAt E0Y p).symm '' (paperInY '' cyl (d.v - d.ε) (d.v + d.ε) d.ε) ⊆
      chartOpen p d.cylO := by
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact mem_chartOpen (A := d.cylO) d.cyl_sub hz
  have h' := Causal.Causality.le_of_causallyConvexIn E0LM.e0_causallyArcConnected d.convex hsub
    ⟨_, ⟨x, hx, rfl⟩, rfl⟩ ⟨_, ⟨y, hy, rfl⟩, rfl⟩ h
  exact (chart_le_iff p (A := d.cylO) d.cyl_sub hx hy).1 h'

/-- **`κ⁻¹Π` is acausal in `M`** (B21 `BTZ_1.tex:647`, « small enough so that `φ⁻¹Π` is acausal
in `M` »): a relation between two of its points is one of `𝔼₀` (`le_model`) between two points at
the same time `τ = v + ε/2`, which coincide (`eq_of_le_of_fst_eq`). -/
theorem CylChartData.isAcausal_K : (CE M).IsAcausal d.K := by
  rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩ _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩ h
  have hab := eq_of_le_of_fst_eq
    (d.le_model (glueDisc_subset_cyl d.pos ha) (glueDisc_subset_cyl d.pos hb) h)
    (ha.1.trans hb.1.symm)
  rw [hab]

/-- **The overlap of the gluing**: a point of `𝒫 ∩ cyl` is sent by `κ⁻¹` into
`M₀ = M ∖ J⁺(κ⁻¹Π)` iff it lies strictly below the disc, `τ < v + ε/2`. (`→` is `mem_glueF`'s
vertical-segment argument; `←` is where the causal convexity of the chart cylinder is used: a
relation `κ⁻¹k ≤ κ⁻¹x`, `k ∈ Π`, is one of `𝔼₀`, along which `τ` does not decrease.) -/
theorem CylChartData.mem_W0_iff {x : E0} (hxP : x ∈ gluePaper d.v d.ε)
    (hxC : x ∈ cyl (d.v - d.ε) (d.v + d.ε) d.ε) :
    (chartAt E0Y p).symm (paperInY x) ∈ d.W0 ↔ x.1 < d.v + d.ε / 2 := by
  constructor
  · intro hxW
    by_contra hc
    push Not at hc
    have hd : ((d.v + d.ε / 2, x.2) : E0) ∈ glueDisc d.v d.ε := ⟨rfl, hxP.2.le⟩
    have hle : causality.le ⊤ ((d.v + d.ε / 2, x.2) : E0) x := le_vertical_top hc
    exact hxW ⟨_, ⟨_, ⟨_, hd, rfl⟩, rfl⟩,
      d.le_of_le (glueDisc_subset_cyl d.pos hd) hxC hle⟩
  · rintro hx ⟨_, ⟨_, ⟨k, hk, rfl⟩, rfl⟩, hkx⟩
    have h := calculus_le (d.le_model (glueDisc_subset_cyl d.pos hk) hxC hkx)
    have hk1 : k.1 = d.v + d.ε / 2 := hk.1
    linarith [h.2.2.1]

end GluePieces

/-! ### §4a′ Relative curve extension (WP-43a): curves of an open past set

The relative extension theory B21's `c₀` argument needs, model-free: a causal curve `c` of an
open `W` lying on a curve `γ` of `W` parametrised by a continuous time function `T`
(`T ∘ γ = id`), with `γ` reaching strictly further in time, is **extensible** in `W`
(`extensible_of_timeGraph_future`, `extensible_of_timeGraph_past`) — constant pieces of `c`
allowed: the extension is `γ ∘ h` with `h` continuous non-decreasing
(`causalCurveIn_comp_monotoneOn`), after an `arctan` reparametrisation making the open end
bounded (`extensible_of_timeGraph_openEnd`). Consequence: **a Cauchy surface of `X` inside an
open past set `W` is a Cauchy surface of `W`** (`isCauchySurfaceOn_of_isPast`; the time function
is Levin's `Causal.Causality.exists_timeFunction_of_secondCountable`, the extension of `c` to an
inextensible curve of `X` is `Causal.Causality.exists_inextensible_of_timeFunction`). -/

section CurveExt

variable {X : Type} [TopologicalSpace X] {C : Causal.Causality X} {W : Opens X}

/-- A causal curve read through a continuous non-decreasing change of parameter is a causal
curve (constant pieces allowed: `≤_N` is reflexive). -/
theorem causalCurveOn_comp_monotoneOn {γ : ℝ → X} {h : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hγ : C.CausalCurveOn W γ (h a) (h b)) (hh : MonotoneOn h (Icc a b))
    (hhc : ContinuousOn h (Icc a b)) : C.CausalCurveOn W (γ ∘ h) a b := by
  have hmaps : ∀ s ∈ Icc a b, h s ∈ Icc (h a) (h b) := fun s hs =>
    ⟨hh ⟨le_rfl, hab⟩ hs hs.1, hh hs ⟨hab, le_rfl⟩ hs.2⟩
  refine ⟨fun t ht => hγ.mem _ (hmaps t ht), fun t ht N hN htN => ?_⟩
  obtain ⟨l, u, hl, hu, hrel⟩ := hγ.rel (h t) (hmaps t ht) N hN htN
  have hpre : h ⁻¹' Ioo l u ∈ 𝓝[Icc a b] t := hhc t ht (Ioo_mem_nhds hl hu)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.1 hpre
  have hin : ∀ s ∈ Icc a b, t - δ < s → s < t + δ → h s ∈ Ioo l u := fun s hs h1 h2 =>
    hball ⟨by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith, hs⟩
  -- every value of `γ ∘ h` in the window lies in `N`
  have hmemN : ∀ s ∈ Icc a b, t - δ < s → s < t + δ → γ (h s) ∈ N := by
    intro s hs h1 h2
    obtain ⟨hl', hu'⟩ := hin s hs h1 h2
    rcases lt_trichotomy (h s) (h t) with e | e | e
    · exact C.isRelFamily_le.mem_left (hrel _ (hmaps s hs) _ (hmaps t ht) hl' e hu)
    · rw [e]; exact htN
    · exact C.isRelFamily_le.mem_right (hrel _ (hmaps t ht) _ (hmaps s hs) hl e hu')
  refine ⟨t - δ, t + δ, by linarith, by linarith, fun s hs s' hs' h1 h2 h3 => ?_⟩
  have e := hh hs hs' h2.le
  rcases e.lt_or_eq with e | e
  · exact hrel _ (hmaps s hs) _ (hmaps s' hs') (hin s hs h1 (h2.trans h3)).1 e
      (hin s' hs' (h1.trans h2) h3).2
  · show C.le N (γ (h s)) (γ (h s'))
    rw [← e]
    exact C.le_refl (hmemN s hs h1 (h2.trans h3))

/-- The interval form of `causalCurveOn_comp_monotoneOn`. -/
theorem causalCurveIn_comp_monotoneOn {γ : ℝ → X} {h : ℝ → ℝ} {J I' : Set ℝ}
    (hγ : C.CausalCurveIn W J γ) (hne : I'.Nonempty) (hoc : I'.OrdConnected)
    (hh : MonotoneOn h I') (hhc : ContinuousOn h I') (hmaps : MapsTo h I' J) :
    C.CausalCurveIn W I' (γ ∘ h) := by
  refine ⟨hne, hoc, fun a ha b hb => ?_⟩
  rcases le_or_gt a b with hab | hab
  · have hsub : Icc a b ⊆ I' := hoc.out ha hb
    exact causalCurveOn_comp_monotoneOn hab (hγ.curve _ (hmaps ha) _ (hmaps hb)) (hh.mono hsub)
      (hhc.mono hsub)
  · exact Causal.CurveOn.of_lt hab

/-- A causal curve over an interval is continuous on it. -/
theorem continuousOn_of_causalCurveIn {I : Set ℝ} {c : ℝ → X} (hc : C.CausalCurveIn W I c) :
    ContinuousOn c I := by
  intro s hs
  by_cases hleft : ∃ j ∈ I, j < s
  · obtain ⟨j, hj, hjs⟩ := hleft
    by_cases hright : ∃ i ∈ I, s < i
    · obtain ⟨i, hi, hsi⟩ := hright
      have hmem : Icc j i ∈ 𝓝[I] s :=
        nhdsWithin_le_nhds (Icc_mem_nhds hjs hsi)
      exact ((hc.continuousOn_Icc hj hi) s ⟨hjs.le, hsi.le⟩).mono_of_mem_nhdsWithin hmem
    · push Not at hright
      have hmem : Icc j s ∈ 𝓝[I] s := by
        refine mem_nhdsWithin.2 ⟨Ioi j, isOpen_Ioi, hjs, fun x hx => ⟨hx.1.le, hright x hx.2⟩⟩
      exact ((hc.continuousOn_Icc hj hs) s ⟨hjs.le, le_rfl⟩).mono_of_mem_nhdsWithin hmem
  · push Not at hleft
    by_cases hright : ∃ i ∈ I, s < i
    · obtain ⟨i, hi, hsi⟩ := hright
      have hmem : Icc s i ∈ 𝓝[I] s := by
        refine mem_nhdsWithin.2 ⟨Iio i, isOpen_Iio, hsi, fun x hx => ⟨hleft x hx.2, hx.1.le⟩⟩
      exact ((hc.continuousOn_Icc hs hi) s ⟨le_rfl, hsi.le⟩).mono_of_mem_nhdsWithin hmem
    · push Not at hright
      have hI : I ⊆ {s} := fun x hx => le_antisymm (hright x hx) (hleft x hx)
      exact (continuousWithinAt_singleton (f := c) (x := s)).mono hI

variable {T : X → ℝ} {J I : Set ℝ} {γ c : ℝ → X}

/-- **Extension at an open, bounded future end along a time-parametrised curve.** -/
theorem extensible_of_timeGraph_openEnd (hγ : C.CausalCurveIn W J γ)
    (hTγ : ∀ τ ∈ J, T (γ τ) = τ) (hc : C.CausalCurveIn W I c)
    (hcγ : ∀ t ∈ I, T (c t) ∈ J ∧ γ (T (c t)) = c t) (hmono : MonotoneOn (T ∘ c) I)
    (hTcont : ContinuousOn (T ∘ c) I) (hbdd : BddAbove I) (hnomax : ∀ t ∈ I, ∃ s ∈ I, t < s)
    {t' : ℝ} (ht' : t' ∈ J) (hlt : ∀ t ∈ I, T (c t) < t') : C.Extensible W I c := by
  have hne := hc.nonempty
  set b := sSup I with hb
  have hltb : ∀ t ∈ I, t < b := fun t ht => by
    obtain ⟨s, hs, hts⟩ := hnomax t ht
    exact hts.trans_le (le_csSup hbdd hs)
  have hTbdd : BddAbove ((T ∘ c) '' I) := ⟨t', by rintro _ ⟨t, ht, rfl⟩; exact (hlt t ht).le⟩
  have hTne : ((T ∘ c) '' I).Nonempty := hne.image _
  set k := sSup ((T ∘ c) '' I) with hk
  have hTk : ∀ t ∈ I, T (c t) ≤ k := fun t ht => le_csSup hTbdd ⟨t, ht, rfl⟩
  have hkt' : k ≤ t' := csSup_le hTne (by rintro _ ⟨t, ht, rfl⟩; exact (hlt t ht).le)
  obtain ⟨t₀, ht₀⟩ := hne
  set L := t' - k with hL
  set I' : Set ℝ := I ∪ Icc b (b + L) with hI'
  set hfun : ℝ → ℝ := fun s => if s < b then T (c s) else k + (s - b) with hhfun
  have hlow : ∀ s ∈ I', s < b → s ∈ I := by
    rintro s (hs | hs) hsb
    · exact hs
    · exact absurd hs.1 (not_le.2 hsb)
  have hoc : I'.OrdConnected := by
    refine ⟨fun x hx y hy z hz => ?_⟩
    rcases lt_or_ge z b with hzb | hzb
    · have hxI : x ∈ I := hlow x hx (hz.1.trans_lt hzb)
      obtain ⟨i, hi, hzi⟩ := exists_lt_of_lt_csSup ⟨t₀, ht₀⟩ hzb
      exact Or.inl (hc.ordConnected.out hxI hi ⟨hz.1, hzi.le⟩)
    · rcases hy with hy | hy
      · exact absurd (hltb y hy) (not_lt.2 (hzb.trans hz.2))
      · exact Or.inr ⟨hzb, hz.2.trans hy.2⟩
  have hTJ : ∀ s ∈ I', hfun s ∈ J := by
    intro s hs
    rcases lt_or_ge s b with hsb | hsb
    · simp only [hhfun, if_pos hsb]; exact (hcγ s (hlow s hs hsb)).1
    · simp only [hhfun, if_neg (not_lt.2 hsb)]
      have hs' : s ∈ Icc b (b + L) := by
        rcases hs with hs | hs
        · exact absurd (hltb s hs) (not_lt.2 hsb)
        · exact hs
      refine hγ.ordConnected.out (hcγ t₀ ht₀).1 ht' ⟨?_, ?_⟩
      · linarith [hTk t₀ ht₀, hs'.1]
      · linarith [hs'.2]
  have hmonoh : MonotoneOn hfun I' := by
    intro x hx y hy hxy
    rcases lt_or_ge y b with hyb | hyb
    · have hxb : x < b := hxy.trans_lt hyb
      simp only [hhfun, if_pos hxb, if_pos hyb]
      exact hmono (hlow x hx hxb) (hlow y hy hyb) hxy
    · simp only [hhfun, if_neg (not_lt.2 hyb)]
      rcases lt_or_ge x b with hxb | hxb
      · simp only [if_pos hxb]; linarith [hTk x (hlow x hx hxb)]
      · simp only [if_neg (not_lt.2 hxb)]; linarith
  have hcont : ContinuousOn hfun I' := by
    intro s hs
    rcases lt_trichotomy s b with hsb | hsb | hsb
    · -- below `b`, `hfun = T ∘ c`
      have hsI : s ∈ I := hlow s hs hsb
      have hmem : I ∈ 𝓝[I'] s := mem_nhdsWithin.2 ⟨Iio b, isOpen_Iio, hsb,
        fun x hx => hlow x hx.2 hx.1⟩
      have h1 : ContinuousWithinAt hfun I s := by
        refine (hTcont s hsI).congr (fun x hx => ?_) ?_
        · simp only [hhfun, if_pos (hltb x hx)]; rfl
        · simp only [hhfun, if_pos hsb]; rfl
      exact h1.mono_of_mem_nhdsWithin hmem
    · -- at `b`
      rw [hsb]
      have hb' : hfun b = k := by
        simp only [hhfun, lt_irrefl, if_false, sub_self, add_zero]
      refine ContinuousWithinAt.union ?_ ?_
      · rw [ContinuousWithinAt, hb', Metric.tendsto_nhdsWithin_nhds]
        intro ε hε
        obtain ⟨_, ⟨i, hi, rfl⟩, hki⟩ := exists_lt_of_lt_csSup hTne (show k - ε < k by linarith)
        refine ⟨b - i, by linarith [hltb i hi], fun x hx hxd => ?_⟩
        have hxb := hltb x hx
        rw [Real.dist_eq, abs_lt] at hxd
        have hix : i ≤ x := by linarith [hxd.1]
        have hfx : hfun x = T (c x) := by simp only [hhfun, if_pos hxb]
        rw [hfx, Real.dist_eq, abs_lt]
        have := hmono hi hx hix
        simp only [Function.comp] at this hki
        constructor <;> linarith [hTk x hx]
      · have : ContinuousOn (fun s => k + (s - b)) (Icc b (b + L)) := by
          fun_prop
        refine (this _ ⟨le_rfl, by linarith⟩).congr (fun x hx => ?_) ?_
        · rcases hx.1.lt_or_eq with hx' | hx'
          · simp only [hhfun, if_neg (not_lt.2 hx'.le)]
          · simp only [hhfun, ← hx', lt_irrefl, if_false]
        · rw [hb']; ring
    · -- above `b`, affine
      have hmem : Ioi b ∈ 𝓝[I'] s := nhdsWithin_le_nhds (Ioi_mem_nhds hsb)
      have h1 : ContinuousWithinAt (fun s => k + (s - b)) I' s :=
        (by fun_prop : Continuous (fun s : ℝ => k + (s - b))).continuousWithinAt
      refine h1.congr_of_eventuallyEq ?_ ?_
      · filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hsb)] with x hx
        simp [hhfun, not_lt.2 (le_of_lt (show b < x from hx))]
      · simp [hhfun, not_lt.2 hsb.le]
  have hL0 : 0 ≤ L := by rw [hL]; linarith
  have hcurve : C.CausalCurveIn W I' (γ ∘ hfun) :=
    causalCurveIn_comp_monotoneOn hγ ⟨t₀, Or.inl ht₀⟩ hoc hmonoh hcont hTJ
  refine ⟨I', γ ∘ hfun, hcurve, ⟨id, strictMonoOn_id, fun t ht => Or.inl ht,
    by rw [image_id]; exact hc.ordConnected, fun t ht => ?_⟩,
    ⟨b + L, Or.inr ⟨by linarith, le_rfl⟩, fun t ht heq => ?_⟩⟩
  · show γ (hfun t) = c t
    simp only [hhfun, if_pos (hltb t ht)]
    exact (hcγ t ht).2
  · have h1 : hfun (b + L) = t' := by
      simp only [hhfun, if_neg (not_lt.2 (show b ≤ b + L by linarith))]
      rw [hL]; ring
    have h2 : T ((γ ∘ hfun) (b + L)) = t' := by
      simp only [Function.comp, h1]; exact hTγ t' ht'
    rw [heq] at h2
    linarith [hlt t ht]

/-- **A causal curve lying on a time-parametrised curve `γ` that goes further to the future is
extensible** (constant pieces of `c` allowed). -/
theorem extensible_of_timeGraph_future (hC : C.CausallyArcConnected) (hcaus : C.IsCausal)
    (hTc : Continuous T) (hT : ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y)
    (hγ : C.CausalCurveIn W J γ) (hTγ : ∀ τ ∈ J, T (γ τ) = τ) (hc : C.CausalCurveIn W I c)
    (hcγ : ∀ t ∈ I, T (c t) ∈ J ∧ γ (T (c t)) = c t)
    {t' : ℝ} (ht' : t' ∈ J) (hlt : ∀ t ∈ I, T (c t) < t') : C.Extensible W I c := by
  by_cases hmax : ∃ b, IsGreatest I b
  · obtain ⟨b, hb⟩ := hmax
    refine Causal.Causality.extensible_of_isGreatest hC hcaus hc hb fun heq => ?_
    have hmem : γ t' ∈ C.Jplus W {c b} := by
      refine ⟨c b, rfl, ?_⟩
      have := hγ.le_of_le (hcγ b hb.1).1 ht' (hlt b hb.1).le
      rwa [(hcγ b hb.1).2] at this
    rw [heq, mem_singleton_iff] at hmem
    have h2 := hTγ t' ht'
    rw [hmem] at h2
    linarith [hlt b hb.1]
  · push Not at hmax
    have hnomax : ∀ t ∈ I, ∃ s ∈ I, t < s := fun t ht => by
      by_contra h
      push Not at h
      exact hmax t ⟨ht, h⟩
    have htan : ∀ t, Real.tan (Real.arctan t) = t := Real.tan_arctan
    set I₁ := Real.arctan '' I with hI₁
    set d : ℝ → X := c ∘ Real.tan with hd
    have hsub : I₁ ⊆ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      rintro _ ⟨t, -, rfl⟩
      exact ⟨Real.neg_pi_div_two_lt_arctan t, Real.arctan_lt_pi_div_two t⟩
    have hmaps : MapsTo Real.tan I₁ I := by
      rintro _ ⟨t, ht, rfl⟩; rw [htan]; exact ht
    have hdc : C.CausalCurveIn W I₁ d :=
      hc.comp (hc.nonempty.image _)
        (isPreconnected_iff_ordConnected.1
          (hc.ordConnected.isPreconnected.image _ Real.continuous_arctan.continuousOn))
        (Real.strictMonoOn_tan.mono hsub) (Real.continuousOn_tan_Ioo.mono hsub) hmaps
    have hdγ : ∀ s ∈ I₁, T (d s) ∈ J ∧ γ (T (d s)) = d s := by
      rintro _ ⟨t, ht, rfl⟩
      simp only [hd, Function.comp, htan]
      exact hcγ t ht
    have hdext : C.Extensible W I₁ d := by
      refine extensible_of_timeGraph_openEnd hγ hTγ hdc hdγ
        (fun x hx y hy hxy => Causal.Causality.CausalCurveIn.time_mono hT hdc hx hy hxy)
        (hTc.comp_continuousOn (continuousOn_of_causalCurveIn hdc))
        ⟨Real.pi / 2, fun x hx => (hsub hx).2.le⟩ ?_ ht' ?_
      · rintro _ ⟨t, ht, rfl⟩
        obtain ⟨u, hu, htu⟩ := hnomax t ht
        exact ⟨Real.arctan u, ⟨u, hu, rfl⟩, Real.arctan_strictMono htu⟩
      · rintro _ ⟨t, ht, rfl⟩
        simp only [hd, Function.comp, htan]
        exact hlt t ht
    exact hdext.of_comp (ψ := Real.arctan) (Real.arctan_strictMono.strictMonoOn _)
      (mapsTo_image _ _) (surjOn_image _ _) fun t _ => by simp only [hd, Function.comp, htan]

/-- The past form of `extensible_of_timeGraph_future` (reversed causality). -/
theorem extensible_of_timeGraph_past (hC : C.CausallyArcConnected) (hcaus : C.IsCausal)
    (hTc : Continuous T) (hT : ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y)
    (hγ : C.CausalCurveIn W J γ) (hTγ : ∀ τ ∈ J, T (γ τ) = τ) (hc : C.CausalCurveIn W I c)
    (hcγ : ∀ t ∈ I, T (c t) ∈ J ∧ γ (T (c t)) = c t)
    {t' : ℝ} (ht' : t' ∈ J) (hgt : ∀ t ∈ I, t' < T (c t)) : C.Extensible W I c := by
  apply Causal.Causality.Extensible.of_dual_reverse
  refine extensible_of_timeGraph_future (C := C.dual) (T := fun x => -T x) (J := -J)
    (γ := fun τ => γ (-τ)) (Causal.Causality.dual_causallyArcConnectedOn.2 hC)
    (Causal.Causality.dual_isCausal.2 hcaus) hTc.neg ?_ hγ.reverse ?_ hc.reverse ?_
    (t' := -t') (by simpa using ht') ?_
  · intro x y hxy hne
    have := hT y x hxy (Ne.symm hne)
    linarith
  · intro τ hτ
    have := hTγ (-τ) hτ
    simp only [this, neg_neg]
  · intro t ht
    obtain ⟨h1, h2⟩ := hcγ (-t) ht
    refine ⟨by simpa using h1, ?_⟩
    simp only [neg_neg]; exact h2
  · intro t ht
    have := hgt (-t) ht
    linarith

/-- **A Cauchy surface of `X` inside an open past set `W` is a Cauchy surface of `W`**, given a
continuous function strictly increasing along `≤`. -/
theorem isCauchySurfaceOn_of_isPast (hC : C.CausallyArcConnected) (hcaus : C.IsCausal)
    (hTc : Continuous T) (hT : ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y)
    (hW : ∀ x y, x ∈ W → C.le ⊤ y x → y ∈ W) {S : Set X} (hSW : S ⊆ W)
    (hS : C.IsCauchySurface S) : C.IsCauchySurfaceOn W S := by
  intro I c hc
  have hcT := hc.1.mono_opens le_top
  obtain ⟨J, γ, hγ, hsub, hTγ⟩ := Causal.Causality.exists_inextensible_of_timeFunction hTc hT hcT
  obtain ⟨_, ⟨⟨tS, htS, rfl⟩, hγS⟩, -⟩ := hS J γ hγ
  have hcγ : ∀ t ∈ I, T (c t) ∈ J ∧ γ (T (c t)) = c t := by
    intro t ht
    obtain ⟨u, hu, hcu⟩ := hsub ⟨t, ht, rfl⟩
    rw [← hcu, hTγ u hu]; exact ⟨hu, rfl⟩
  have hac : C.IsAcausal S := hS.isAcausal_of_timeFunction hC hTc hT
  have hex : ∃ t ∈ I, c t ∈ S := by
    by_contra hno
    push Not at hno
    have hne : ∀ t ∈ I, T (c t) ≠ tS := fun t ht e =>
      hno t ht (by rw [← (hcγ t ht).2, e]; exact hγS)
    set J' : Set ℝ := {u | u ∈ J ∧ (u ≤ tS ∨ ∃ t ∈ I, u ≤ T (c t))} with hJ'
    have hJ'mem : ∀ u ∈ J', γ u ∈ W := by
      rintro u ⟨hu, hu' | ⟨t, ht, hut⟩⟩
      · exact hW _ _ (hSW hγS) (hγ.1.le_of_le hu htS hu')
      · have h1 := hγ.1.le_of_le hu (hcγ t ht).1 hut
        rw [(hcγ t ht).2] at h1
        exact hW _ _ (hc.1.mem ht) h1
    have hJ'oc : J'.OrdConnected := ⟨fun x hx y hy z hz => by
      refine ⟨hγ.1.ordConnected.out hx.1 hy.1 hz, ?_⟩
      rcases hy.2 with h | ⟨t, ht, h⟩
      · exact Or.inl (hz.2.trans h)
      · exact Or.inr ⟨t, ht, hz.2.trans h⟩⟩
    have htS' : tS ∈ J' := ⟨htS, Or.inl le_rfl⟩
    have hγ' : C.CausalCurveIn W J' γ := ⟨⟨tS, htS'⟩, hJ'oc, fun a ha b hb =>
      Causal.CurveOn.restrict (hγ.1.curve a ha.1 b hb.1) le_rfl le_rfl le_top
        fun u hu => hJ'mem u (hJ'oc.out ha hb hu)⟩
    have hcγ' : ∀ t ∈ I, T (c t) ∈ J' ∧ γ (T (c t)) = c t := fun t ht =>
      ⟨⟨(hcγ t ht).1, Or.inr ⟨t, ht, le_rfl⟩⟩, (hcγ t ht).2⟩
    have hTγ' : ∀ τ ∈ J', T (γ τ) = τ := fun τ hτ => hTγ τ hτ.1
    by_cases hall : ∀ t ∈ I, T (c t) < tS
    · exact hc.2 (extensible_of_timeGraph_future hC hcaus hTc hT hγ' hTγ' hc.1 hcγ' htS' hall)
    · push Not at hall
      obtain ⟨t₁, ht₁, h₁⟩ := hall
      have hgt : ∀ t ∈ I, tS < T (c t) := by
        intro t ht
        by_contra h
        push Not at h
        have hsub' : uIcc t t₁ ⊆ I := hc.1.ordConnected.uIcc_subset ht ht₁
        have hcont : ContinuousOn (T ∘ c) (uIcc t t₁) :=
          hTc.comp_continuousOn ((continuousOn_of_causalCurveIn hc.1).mono hsub')
        obtain ⟨s, hs, hse⟩ := intermediate_value_uIcc hcont (Set.mem_uIcc_of_le h h₁)
        exact hne s (hsub' hs) hse
      exact hc.2 (extensible_of_timeGraph_past hC hcaus hTc hT hγ' hTγ' hc.1 hcγ' htS' hgt)
  obtain ⟨t, ht, hcS⟩ := hex
  refine ⟨c t, ⟨mem_image_of_mem c ht, hcS⟩, ?_⟩
  rintro _ ⟨⟨s, hs, rfl⟩, hsS⟩
  rcases le_total s t with h | h
  · exact hac _ hsS _ hcS ((hc.1.mono_opens le_top).le_of_le hs ht h)
  · exact (hac _ hcS _ hsS ((hc.1.mono_opens le_top).le_of_le ht hs h)).symm

end CurveExt

/-! ### §4a″ Connected Cauchy surfaces without compactness (WP-43a)

`GX.E0AbsMax.isConnected_of_isCauchySurface_abstract` (WP-41k) proves a **compact** acausal
Cauchy surface of a connected globally hyperbolic spacetime connected. Lemma 2.3's `M₀` needs the
non-compact case (the level set `T = a` of a Cauchy time function of an arbitrary GH
`𝔼₀`-manifold): compactness of `S` is replaced by R1 (`J⁺(S) ∩ J⁻(q)` and `J⁻(S) ∩ J⁺(q)`
compact, `E0LM.sfa_isCompact_Jplus_inter_Jminus`), which makes the futures and pasts of the
closed pieces of `S` closed (`isClosed_Jplus_of_subset_cauchy`, `isClosed_Jminus_of_subset_cauchy`),
and the minimal-point argument goes through unchanged (`not_le_of_le_of_isCauchySurface_closed`,
`isConnected_of_isCauchySurface_closed`). -/

section CauchyConnected

variable {X : Type} [TopologicalSpace X] {C : Causal.Causality X}

/-- **The causal future of a closed piece `A` of a Cauchy surface `S` is closed**, when the
`J⁺(S) ∩ J⁻(q)` are compact (R1): near `y`, inside a tarentin diamond `J(p, q)`, `J⁺(A)` is the
causal future of the compact `A ∩ J⁻(q)`. -/
theorem isClosed_Jplus_of_subset_cauchy [T2Space X] (hT : C.Tarentin) (hG : C.GloballyHyperbolic)
    {S A : Set X} (hcomp : ∀ q : X, IsCompact (C.Jplus ⊤ S ∩ C.Jminus ⊤ {q}))
    (hAS : A ⊆ S) (hA : IsClosed A) : IsClosed (C.Jplus ⊤ A) := by
  have hle := hG.isClosed_le hT
  refine isClosed_of_closure_subset fun y hy => ?_
  obtain ⟨p, -, q, -, hσ⟩ := hT y univ univ_mem
  set N := C.openDiamond ⊤ p q with hN
  have hNq : ∀ z ∈ N, C.le ⊤ z q := fun z hz =>
    (Causal.Causality.mem_diamond.1 (Causal.Causality.openDiamond_subset_diamond hz)).2
  set A' := A ∩ C.Jminus ⊤ {q} with hA'
  have hA'c : IsCompact A' := by
    refine (hcomp q).of_isClosed_subset (hA.inter (hG.isClosed_Jminus_singleton hT q)) ?_
    rintro z ⟨hzA, hzq⟩
    exact ⟨⟨z, hAS hzA, C.le_refl trivial⟩, hzq⟩
  have hcl := Causal.Causality.isClosed_Jplus_of_isCompact hle hA'c
  have hsub : N ∩ C.Jplus ⊤ A ⊆ C.Jplus ⊤ A' := by
    rintro z ⟨hzN, a, ha, haz⟩
    exact ⟨a, ⟨ha, Causal.Precausality.mem_Jminus_singleton.2 (C.le_trans haz (hNq z hzN))⟩, haz⟩
  have hy' : y ∈ closure (N ∩ C.Jplus ⊤ A) :=
    Causal.Causality.isOpen_openDiamond.inter_closure ⟨hσ, hy⟩
  have h2 := closure_mono hsub hy'
  rw [hcl.closure_eq] at h2
  obtain ⟨a, ha, haz⟩ := h2
  exact ⟨a, ha.1, haz⟩

/-- The past form of `isClosed_Jplus_of_subset_cauchy` (reversed causality). -/
theorem isClosed_Jminus_of_subset_cauchy [T2Space X] (hT : C.Tarentin)
    (hG : C.GloballyHyperbolic) {S A : Set X}
    (hcomp : ∀ q : X, IsCompact (C.Jminus ⊤ S ∩ C.Jplus ⊤ {q}))
    (hAS : A ⊆ S) (hA : IsClosed A) : IsClosed (C.Jminus ⊤ A) :=
  isClosed_Jplus_of_subset_cauchy (C := C.dual) (Causal.Causality.dual_tarentin.2 hT)
    (Causal.Causality.dual_globallyHyperbolic.2 hG) hcomp hAS hA

/-- The core of `isConnected_of_isCauchySurface_closed` (the argument of
`GX.E0AbsMax.not_le_of_le_of_isCauchySurface`, WP-41k, for a **closed, not necessarily compact**
Cauchy surface: compactness of `S` is replaced by R1, `J⁺(S) ∩ J⁻(x)` compact, and the closedness
of the futures of the two pieces). -/
theorem not_le_of_le_of_isCauchySurface_closed [T2Space X] (hT : C.Tarentin) (hG : C.GloballyHyperbolic)
    (hC : C.CausallyArcConnected) (hext : C.CurvesExtend) {S S₁ S₂ : Set X}
    (hS : C.IsCauchySurface S) (hSac : C.IsAcausal S) (hScl : IsClosed S)
    (hcomp : ∀ q : X, IsCompact (C.Jplus ⊤ S ∩ C.Jminus ⊤ {q}))
    (hS₁ : IsClosed (C.Jplus ⊤ S₁)) (hS₂ : IsClosed (C.Jplus ⊤ S₂))
    (hSS : S = S₁ ∪ S₂) (hdisj : Disjoint S₁ S₂) {x a b : X} (ha : a ∈ S₁) (hb : b ∈ S₂)
    (hax : C.le ⊤ a x) (hbx : C.le ⊤ b x) : False := by
  have hle := hG.isClosed_le hT
  set K : Set X := C.Jminus ⊤ {x} ∩ C.Jplus ⊤ S₁ ∩ C.Jplus ⊤ S₂ with hKdef
  have hKcl : IsClosed K :=
    ((hG.isClosed_Jminus_singleton hT x).inter hS₁).inter hS₂
  have hKsub : K ⊆ C.Jplus ⊤ S ∩ C.Jminus ⊤ {x} := by
    rintro z ⟨⟨hzx, σ', hσ', hσ'z⟩, -⟩
    exact ⟨⟨σ', hSS ▸ Or.inl hσ', hσ'z⟩, hzx⟩
  have hKc : IsCompact K := (hcomp x).of_isClosed_subset hKcl hKsub
  have hxK : x ∈ K := ⟨⟨Causal.Precausality.mem_Jminus_singleton.2 (C.le_refl trivial),
    a, ha, hax⟩, b, hb, hbx⟩
  obtain ⟨y₀, hy₀K, hmin⟩ := Causal.Causality.exists_minimal_of_isCompact hG.1
    (fun z => hG.isClosed_Jminus_singleton hT z) hKc ⟨x, hxK⟩
  obtain ⟨⟨hy₀x, a', ha', ha'y⟩, b', hb', hb'y⟩ := hy₀K
  have hy₀x' : C.le ⊤ y₀ x := Causal.Precausality.mem_Jminus_singleton.1 hy₀x
  have hSa' : a' ∈ S := hSS ▸ Or.inl ha'
  have hSb' : b' ∈ S := hSS ▸ Or.inr hb'
  -- `y₀ ∉ S`
  have hy₀S : y₀ ∉ S := by
    intro hy
    have e1 := hSac a' hSa' y₀ hy ha'y
    have e2 := hSac b' hSb' y₀ hy hb'y
    exact Set.disjoint_left.1 hdisj ha' (e1.trans e2.symm ▸ hb')
  have hSU : C.IsCauchySurfaceOn ⊤ (S ∩ (⊤ : Opens X)) := by
    rw [Opens.coe_top, inter_univ]; exact hS
  obtain ⟨s, ⟨hsS, -⟩, N, hN, -, hNs⟩ :=
    Causal.Causality.exists_nhds_subset_Jplus_of_isCauchySurfaceOn hT hG hC hext
      Causal.Causality.causallyConvexIn_top hScl hSU ⟨hSa', trivial⟩ trivial hy₀S ha'y
  -- the curve from the other piece's point `e ≤ y₀` meets `N ∖ {y₀}` just before `y₀`
  have hclose : ∀ e, e ∈ S → C.le ⊤ e y₀ →
      ∃ z ∈ N, C.le ⊤ e z ∧ C.le ⊤ z y₀ ∧ z ≠ y₀ := by
    intro e heS hey
    obtain ⟨c, hc, hc0, hc1⟩ := (hC ⊤ le_rfl e y₀).1.1 hey
    have hcont : ContinuousOn c (Icc 0 1) := hc.continuousOn C.isRelFamily_le
    set T : Set ℝ := {t | t ∈ Icc (0 : ℝ) 1 ∧ c t = y₀} with hTdef
    have h1T : (1 : ℝ) ∈ T := ⟨right_mem_Icc.2 zero_le_one, hc1⟩
    have hTbdd : BddBelow T := ⟨0, fun t ht => ht.1.1⟩
    have hTcl : IsClosed T := by
      have : T = Icc 0 1 ∩ c ⁻¹' {y₀} := rfl
      rw [this]
      exact hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
    have hτ : sInf T ∈ T := hTcl.csInf_mem ⟨1, h1T⟩ hTbdd
    have hτ0 : 0 < sInf T := by
      rcases hτ.1.1.eq_or_lt with h | h
      · exfalso
        have : c 0 = y₀ := by rw [h]; exact hτ.2
        rw [hc0] at this
        exact hy₀S (this ▸ heS)
      · exact h
    -- points just before `sInf T`
    have hpre : c ⁻¹' N ∈ 𝓝[Icc 0 1] (sInf T) :=
      (hcont _ hτ.1).preimage_mem_nhdsWithin (by rw [hτ.2]; exact hN)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hpre
    set t := max (sInf T - ε / 2) (sInf T / 2) with htdef
    have ht0 : 0 ≤ t := le_max_of_le_right (by linarith)
    have htlt : t < sInf T := max_lt (by linarith) (by linarith)
    have ht1 : t ≤ 1 := htlt.le.trans hτ.1.2
    have htN : c t ∈ N := by
      refine hball ⟨?_, ht0, ht1⟩
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [le_max_left (sInf T - ε / 2) (sInf T / 2)]
    refine ⟨c t, htN, ?_, ?_, ?_⟩
    · have := hc.le_of_le le_rfl ht0 ht1; rwa [hc0] at this
    · have := hc.le_of_le ht0 htlt.le hτ.1.2; rwa [hτ.2] at this
    · intro he
      exact absurd (csInf_le hTbdd ⟨⟨ht0, ht1⟩, he⟩) (not_le.2 htlt)
  have hsS' : s ∈ S₁ ∪ S₂ := hSS ▸ hsS
  rcases hsS' with hs1 | hs2
  · obtain ⟨z, hzN, hb'z, hzy, hne⟩ := hclose b' hSb' hb'y
    exact hne (hmin z ⟨⟨Causal.Precausality.mem_Jminus_singleton.2 (C.le_trans hzy hy₀x'),
      s, hs1, hNs z hzN⟩, b', hb', hb'z⟩ hzy)
  · obtain ⟨z, hzN, ha'z, hzy, hne⟩ := hclose a' hSa' ha'y
    exact hne (hmin z ⟨⟨Causal.Precausality.mem_Jminus_singleton.2 (C.le_trans hzy hy₀x'),
      a', ha', ha'z⟩, s, hs2, hNs z hzN⟩ hzy)

/-- **A closed acausal Cauchy surface of a connected globally hyperbolic spacetime is connected**,
given R1 (`J⁺(S) ∩ J⁻(q)`, `J⁻(S) ∩ J⁺(q)` compact) — the non-compact form of
`GX.E0AbsMax.isConnected_of_isCauchySurface_abstract` (WP-41k), whose proof is followed. -/
theorem isConnected_of_isCauchySurface_closed [T2Space X] [ConnectedSpace X] (hT : C.Tarentin)
    (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected) (hext : C.CurvesExtend)
    {S : Set X} (hS : C.IsCauchySurface S) (hScl : IsClosed S) (hSac : C.IsAcausal S)
    (hcomp : ∀ q : X, IsCompact (C.Jplus ⊤ S ∩ C.Jminus ⊤ {q}))
    (hcomp' : ∀ q : X, IsCompact (C.Jminus ⊤ S ∩ C.Jplus ⊤ {q})) :
    IsConnected S := by
  have hle := hG.isClosed_le hT
  -- every point is causally related to a point of `S`
  have hrel : ∀ x : X, ∃ σ ∈ S, C.le ⊤ σ x ∨ C.le ⊤ x σ := by
    intro x
    obtain ⟨I, c, hc, hsub⟩ := hext _ 0 1 zero_le_one
      (Causal.Causality.causalCurveOn_const (p := x) (W := ⊤) trivial)
    obtain ⟨v, hv, hcv⟩ := hsub ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
    have hcv' : c v = x := hcv
    obtain ⟨σ, ⟨⟨u, hu, rfl⟩, hσ⟩, -⟩ := hS I c hc
    refine ⟨c u, hσ, ?_⟩
    rcases le_total u v with h | h
    · exact Or.inl (hcv' ▸ hc.1.le_of_le hu hv h)
    · exact Or.inr (hcv' ▸ hc.1.le_of_le hv hu h)
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  obtain ⟨σ₀, hσ₀, -⟩ := hrel x₀
  refine ⟨⟨σ₀, hσ₀⟩, ?_⟩
  rw [isPreconnected_closed_iff]
  intro t t' ht ht' hSt hne hne'
  by_contra hempty
  have hdisj : Disjoint (S ∩ t) (S ∩ t') := Set.disjoint_left.2 fun z h1 h2 =>
    hempty ⟨z, h1.1, h1.2, h2.2⟩
  have hS₁c : IsClosed (S ∩ t) := hScl.inter ht
  have hS₂c : IsClosed (S ∩ t') := hScl.inter ht'
  have hJp₁ := isClosed_Jplus_of_subset_cauchy hT hG hcomp inter_subset_left hS₁c
  have hJp₂ := isClosed_Jplus_of_subset_cauchy hT hG hcomp inter_subset_left hS₂c
  have hJm₁ := isClosed_Jminus_of_subset_cauchy hT hG hcomp' inter_subset_left hS₁c
  have hJm₂ := isClosed_Jminus_of_subset_cauchy hT hG hcomp' inter_subset_left hS₂c
  have hSS : S = S ∩ t ∪ S ∩ t' := by
    ext z
    constructor
    · intro hz
      rcases hSt hz with h | h
      · exact Or.inl ⟨hz, h⟩
      · exact Or.inr ⟨hz, h⟩
    · rintro (h | h) <;> exact h.1
  set U₁ := C.Jplus ⊤ (S ∩ t) ∪ C.Jminus ⊤ (S ∩ t) with hU₁
  set U₂ := C.Jplus ⊤ (S ∩ t') ∪ C.Jminus ⊤ (S ∩ t') with hU₂
  have hU₁c : IsClosed U₁ := hJp₁.union hJm₁
  have hU₂c : IsClosed U₂ := hJp₂.union hJm₂
  have hcover : (univ : Set X) ⊆ U₁ ∪ U₂ := by
    intro x _
    obtain ⟨σ, hσ, h⟩ := hrel x
    rcases hSt hσ with hσt | hσt'
    · rcases h with h | h
      · exact Or.inl (Or.inl ⟨σ, ⟨hσ, hσt⟩, h⟩)
      · exact Or.inl (Or.inr ⟨σ, ⟨hσ, hσt⟩, h⟩)
    · rcases h with h | h
      · exact Or.inr (Or.inl ⟨σ, ⟨hσ, hσt'⟩, h⟩)
      · exact Or.inr (Or.inr ⟨σ, ⟨hσ, hσt'⟩, h⟩)
  obtain ⟨a, ha⟩ := hne
  obtain ⟨b, hb⟩ := hne'
  obtain ⟨x, -, hx₁, hx₂⟩ := (isPreconnected_closed_iff.1 isPreconnected_univ) U₁ U₂ hU₁c hU₂c
    hcover ⟨a, trivial, Or.inl ⟨a, ha, C.le_refl trivial⟩⟩
    ⟨b, trivial, Or.inl ⟨b, hb, C.le_refl trivial⟩⟩
  have hacS : ∀ {a' b'}, a' ∈ S ∩ t → b' ∈ S ∩ t' → C.le ⊤ a' b' → False := fun ha' hb' h =>
    Set.disjoint_left.1 hdisj ha' (hSac _ ha'.1 _ hb'.1 h ▸ hb')
  have hacS' : ∀ {a' b'}, a' ∈ S ∩ t → b' ∈ S ∩ t' → C.le ⊤ b' a' → False := fun ha' hb' h =>
    Set.disjoint_left.1 hdisj ha' ((hSac _ hb'.1 _ ha'.1 h).symm ▸ hb')
  rcases hx₁ with ⟨a', ha', h1⟩ | ⟨a', ha', h1⟩ <;> rcases hx₂ with ⟨b', hb', h2⟩ | ⟨b', hb', h2⟩
  · exact not_le_of_le_of_isCauchySurface_closed hT hG hC hext hS hSac hScl hcomp hJp₁ hJp₂ hSS hdisj
      ha' hb' h1 h2
  · exact hacS ha' hb' (C.le_trans h1 h2)
  · exact hacS' ha' hb' (C.le_trans h2 h1)
  · exact not_le_of_le_of_isCauchySurface_closed (C := C.dual)
      (Causal.Causality.dual_tarentin.2 hT) (Causal.Causality.dual_globallyHyperbolic.2 hG)
      (Causal.Causality.dual_causallyArcConnectedOn.2 hC) hext.dual
      (Causal.Causality.dual_isCauchySurfaceOn.2 hS) (Causal.Causality.dual_isAcausal.2 hSac) hScl
      hcomp' hJm₁ hJm₂ hSS hdisj ha' hb' h1 h2


end CauchyConnected

/-! ### §4b The glue data of Lemma 2.3 (`Causal.CBG.FamilyGlueData`, two pieces) -/

section GlueData

open E0CBG

/-- The two pieces of the gluing of Lemma 2.3: `false ↦ M₀`, `true ↦ 𝒫`. -/
def gluePiece {M : Type} [TopologicalSpace M] (A : Opens M) (B : Opens E0Y) : Bool → Type
  | false => A
  | true => B

instance gluePiece.instTop {M : Type} [TopologicalSpace M] (A : Opens M) (B : Opens E0Y) :
    ∀ b, TopologicalSpace (gluePiece A B b)
  | false => inferInstanceAs (TopologicalSpace A)
  | true => inferInstanceAs (TopologicalSpace B)

noncomputable instance gluePiece.instCharted {M : Type} [TopologicalSpace M] [ChartedSpace E0Y M]
    (A : Opens M) (B : Opens E0Y) : ∀ b, ChartedSpace E0Y (gluePiece A B b)
  | false => inferInstanceAs (ChartedSpace E0Y A)
  | true => inferInstanceAs (ChartedSpace E0Y B)

instance gluePiece.instHasGroupoid {M : Type} [TopologicalSpace M] [ChartedSpace E0Y M]
    [HasGroupoid M e0Groupoid] (A : Opens M) (B : Opens E0Y) :
    ∀ b, HasGroupoid (gluePiece A B b) e0Groupoid
  | false => inferInstanceAs (HasGroupoid A e0Groupoid)
  | true => inferInstanceAs (HasGroupoid B e0Groupoid)

instance gluePiece.instT2 {M : Type} [TopologicalSpace M] [T2Space M] (A : Opens M)
    (B : Opens E0Y) : ∀ b, T2Space (gluePiece A B b)
  | false => inferInstanceAs (T2Space A)
  | true => inferInstanceAs (T2Space B)

/-- `Y = 𝕄 ⊕ 𝔼₀` is second countable (as in `E0LM.e0_chart_source_secondCountable`). -/
instance secondCountableTopology_E0Y_spear : SecondCountableTopology E0Y := by
  haveI : SecondCountableTopology BTZE0 :=
    (quotientBase_topology (Z := ℝ) btz_two_pi_ne_zero).2.2 inferInstance
  infer_instance

instance gluePiece.instSC {M : Type} [TopologicalSpace M] [SecondCountableTopology M]
    (A : Opens M) (B : Opens E0Y) : ∀ b, SecondCountableTopology (gluePiece A B b)
  | false => inferInstanceAs (SecondCountableTopology A)
  | true => inferInstanceAs (SecondCountableTopology B)

/-- The spear piece `𝒫` as an open set of `Y`. -/
noncomputable def gluePY (v ε : ℝ) : Opens E0Y :=
  ⟨paperInY '' gluePaper v ε, isOpen_paperInY_image (isOpen_gluePaper v ε)⟩

/-- The chart cylinder in `Y`. -/
noncomputable def glueCY (v ε : ℝ) : Set E0Y := paperInY '' cyl (v - ε) (v + ε) ε

theorem isOpen_glueCY (v ε : ℝ) : IsOpen (glueCY v ε) := isOpen_paperInY_image (isOpen_cyl _ _ _)

variable {M : Type} [TopologicalSpace M] [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]
  [T2Space M] {p : M} (d : CylChartData p) (hGH : (CE M).GloballyHyperbolic)

/-- `M₀` as an open set. -/
noncomputable def CylChartData.W0o : Opens M := ⟨d.W0, d.isOpen_W0 hGH⟩

/-- The part of `M₀` glued to `𝒫`: `κ⁻¹(cyl ∩ 𝒫) ∩ M₀`. -/
noncomputable def CylChartData.U01 : Opens (d.W0o hGH) :=
  ⟨Subtype.val ⁻¹' ((chartAt E0Y p).source ∩ chartAt E0Y p ⁻¹' (glueCY d.v d.ε ∩ gluePY d.v d.ε)),
    ((chartAt E0Y p).isOpen_inter_preimage ((isOpen_glueCY _ _).inter
      (gluePY d.v d.ε).isOpen)).preimage continuous_subtype_val⟩

/-- The part of `𝒫` glued to `M₀`: `cyl ∩ 𝒫 ∩ κ(M₀)`. -/
noncomputable def CylChartData.U10 : Opens (gluePY d.v d.ε) :=
  ⟨Subtype.val ⁻¹' (glueCY d.v d.ε ∩ (chartAt E0Y p).symm ⁻¹' d.W0), by
    have h : glueCY d.v d.ε ∩ (chartAt E0Y p).symm ⁻¹' d.W0 =
        glueCY d.v d.ε ∩ ((chartAt E0Y p).symm.source ∩ (chartAt E0Y p).symm ⁻¹' d.W0) := by
      ext y
      exact ⟨fun h => ⟨h.1, d.cyl_sub h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
    rw [h]
    exact ((isOpen_glueCY _ _).inter ((chartAt E0Y p).symm.isOpen_inter_preimage
      (d.isOpen_W0 hGH))).preimage continuous_subtype_val⟩

/-- The overlap `𝒫 ∩ cyl ∩ {τ < v + ε/2}` of the gluing, in paper coordinates. -/
def glueOverlap (v ε : ℝ) : Set E0 :=
  gluePaper v ε ∩ cyl (v - ε) (v + ε) ε ∩ {x | x.1 < v + ε / 2}

/-- **The overlap of the gluing is `𝒫 ∩ cyl ∩ {τ < v + ε/2}`** (normalisation of
`CylChartData`, `mem_W0_iff`): so the part of `𝒫` not identified with `M₀` is
`𝒫 ∖ cyl ∪ {τ ≥ v + ε/2}`, whose frontier against the overlap inside the chart cylinder is
`Π` — B21's « the boundary of `M₀` in `M₂` is `Π` » (l.661). -/
theorem CylChartData.mem_U10_iff (y : gluePY d.v d.ε) :
    y ∈ d.U10 hGH ↔ ∃ x ∈ glueOverlap d.v d.ε, paperInY x = y.1 := by
  obtain ⟨_, x, hxP, rfl⟩ := y
  have hinj : ∀ {a b : E0}, paperInY a = paperInY b → a = b :=
    fun h => paperInY.injOn (by simp) (by simp) h
  show (paperInY x ∈ glueCY d.v d.ε ∧ (chartAt E0Y p).symm (paperInY x) ∈ d.W0) ↔ _
  constructor
  · rintro ⟨⟨x', hx'C, hx'x⟩, hW⟩
    have := hinj hx'x
    subst this
    exact ⟨x', ⟨⟨hxP, hx'C⟩, (d.mem_W0_iff hxP hx'C).1 hW⟩, rfl⟩
  · rintro ⟨x', ⟨⟨-, hx'C⟩, hx'τ⟩, hx'x⟩
    have := hinj hx'x
    subst this
    exact ⟨⟨x', hx'C, rfl⟩, (d.mem_W0_iff hxP hx'C).2 hx'τ⟩

/-- The transition `M₀ ⊇ U₀₁ → 𝒫`, `x ↦ κ x`. -/
noncomputable def CylChartData.φ01 (x : d.U01 hGH) : gluePY d.v d.ε :=
  ⟨chartAt E0Y p x.1.1, x.2.2.2⟩

/-- The transition `𝒫 ⊇ U₁₀ → M₀`, `y ↦ κ⁻¹ y`. -/
noncomputable def CylChartData.φ10 (y : d.U10 hGH) : d.W0o hGH :=
  ⟨(chartAt E0Y p).symm y.1.1, y.2.2⟩

/-- The open sets of the glue data. -/
noncomputable def CylChartData.glueU : (i j : Bool) → Opens (gluePiece (d.W0o hGH) (gluePY d.v d.ε) i)
  | false, false => ⊤
  | false, true => d.U01 hGH
  | true, false => d.U10 hGH
  | true, true => ⊤

/-- The transitions of the glue data. -/
noncomputable def CylChartData.glueφ : (i j : Bool) → d.glueU hGH i j →
    gluePiece (d.W0o hGH) (gluePY d.v d.ε) j
  | false, false => fun x => x.1
  | false, true => fun x => d.φ01 hGH x
  | true, false => fun y => d.φ10 hGH y
  | true, true => fun x => x.1

/-- **The glue data of Lemma 2.3**: `M₀` and `𝒫` glued along `U₀₁ ≅ U₁₀` by the chart `κ`. -/
noncomputable def CylChartData.glueData :
    Causal.CBG.FamilyGlueData Bool (gluePiece (d.W0o hGH) (gluePY d.v d.ε)) where
  U := d.glueU hGH
  φ := d.glueφ hGH
  continuous_φ := by
    rintro (_ | _) (_ | _)
    · exact continuous_subtype_val
    · exact ((chartAt E0Y p).continuousOn.comp_continuous
        (continuous_subtype_val.comp continuous_subtype_val) fun x => x.2.1).subtype_mk _
    · exact ((chartAt E0Y p).continuousOn_symm.comp_continuous
        (continuous_subtype_val.comp continuous_subtype_val) fun y => d.cyl_sub y.2.1).subtype_mk _
    · exact continuous_subtype_val
  φ_mem := by
    rintro (_ | _) (_ | _) x
    · trivial
    · show (chartAt E0Y p x.1.1 ∈ glueCY d.v d.ε) ∧
        (chartAt E0Y p).symm (chartAt E0Y p x.1.1) ∈ d.W0
      exact ⟨x.2.2.1, by rw [(chartAt E0Y p).left_inv x.2.1]; exact x.1.2⟩
    · show (chartAt E0Y p).symm x.1.1 ∈ (chartAt E0Y p).source ∧
        chartAt E0Y p ((chartAt E0Y p).symm x.1.1) ∈ glueCY d.v d.ε ∩ gluePY d.v d.ε
      exact ⟨(chartAt E0Y p).map_target (d.cyl_sub x.2.1), by
        rw [(chartAt E0Y p).right_inv (d.cyl_sub x.2.1)]; exact ⟨x.2.1, x.1.2⟩⟩
    · trivial
  U_self := by rintro (_ | _) <;> rfl
  φ_self := by rintro (_ | _) x <;> rfl
  cocycle := by
    rintro (_ | _) (_ | _) (_ | _) x h
    · exact ⟨trivial, rfl⟩
    · exact ⟨h, rfl⟩
    · exact ⟨trivial, Subtype.ext ((chartAt E0Y p).left_inv x.2.1)⟩
    · exact ⟨x.2, rfl⟩
    · exact ⟨x.2, rfl⟩
    · exact ⟨trivial, Subtype.ext ((chartAt E0Y p).right_inv (d.cyl_sub x.2.1))⟩
    · exact ⟨h, rfl⟩
    · exact ⟨trivial, rfl⟩

/-- The graph of a self-transition of a family gluing is the diagonal. -/
theorem familyGlue_graph_self {I : Type} {X : I → Type} [∀ i, TopologicalSpace (X i)]
    (D : Causal.CBG.FamilyGlueData I X) (i : I) :
    Causal.Gluing.graph (Subtype.val : D.U i i → X i) (D.φ i i) = diagonal (X i) := by
  ext ⟨a, b⟩
  constructor
  · rintro ⟨w, hw⟩
    simp only [Prod.mk.injEq, D.φ_self] at hw
    exact hw.1.symm.trans hw.2
  · intro h
    have h' : a = b := h
    subst h'
    exact ⟨⟨a, D.mem_U_self i a⟩, by simp [D.φ_self]⟩

/-- The graph of `φ j i` is the transpose of the graph of `φ i j`. -/
theorem familyGlue_mem_graph_swap {I : Type} {X : I → Type} [∀ i, TopologicalSpace (X i)]
    (D : Causal.CBG.FamilyGlueData I X) {i j : I} {a : X j} {b : X i}
    (h : (a, b) ∈ Causal.Gluing.graph (Subtype.val : D.U j i → X j) (D.φ j i)) :
    (b, a) ∈ Causal.Gluing.graph (Subtype.val : D.U i j → X i) (D.φ i j) := by
  obtain ⟨w, hw⟩ := h
  simp only [Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  exact ⟨⟨D.φ j i w, D.φ_mem j i w⟩, by simp [D.φ_φ]⟩

theorem familyGlue_graph_swap {I : Type} {X : I → Type} [∀ i, TopologicalSpace (X i)]
    (D : Causal.CBG.FamilyGlueData I X) (i j : I) :
    Causal.Gluing.graph (Subtype.val : D.U j i → X j) (D.φ j i) =
      Prod.swap ⁻¹' Causal.Gluing.graph (Subtype.val : D.U i j → X i) (D.φ i j) := by
  ext ⟨a, b⟩
  exact ⟨familyGlue_mem_graph_swap D, familyGlue_mem_graph_swap D⟩

/-- **The graph of `κ⁻¹ : U₁₀ → M₀` is closed** (the Hausdorffness of `M₂`, which B21 asserts
without proof): off the compact `F ⊇ U₁₀` the complement is open; at `(y, x)` with `y ∈ F`,
`κ⁻¹` is continuous at `y`, so either `x = κ⁻¹ y` (and `(y, x)` is on the graph) or `x` and
`κ⁻¹ y` are separated in `M`. -/
theorem CylChartData.isClosed_graph10 :
    IsClosed (range fun w : d.U10 hGH => ((w.1 : gluePY d.v d.ε), d.φ10 hGH w)) := by
  set κ := chartAt E0Y p with hκ
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  rintro ⟨y, x⟩ hyx
  set FY : Set E0Y := paperInY '' glueF d.v d.ε with hFY
  have hFc : IsClosed FY := ((isCompact_glueF _ _).image continuous_paperInY).isClosed
  have hFsub : ∀ w : d.U10 hGH, ((w.1 : gluePY d.v d.ε) : E0Y) ∈ FY := by
    intro w
    obtain ⟨e, he, hee⟩ := w.1.2
    obtain ⟨e', he', hee'⟩ := w.2.1
    have hee2 : e = e' := paperInY.injOn (by simp) (by simp) (hee.trans hee'.symm)
    subst hee2
    refine ⟨e, d.mem_glueF he he' ?_, hee⟩
    rw [hee]; exact w.2.2
  by_cases hyF : (y : E0Y) ∈ FY
  · have hyC : (y : E0Y) ∈ glueCY d.v d.ε := by
      obtain ⟨e, he, hee⟩ := hyF; exact ⟨e, glueF_subset_cyl d.pos he, hee⟩
    have hyT : (y : E0Y) ∈ κ.target := d.cyl_sub hyC
    by_cases hxy : κ.symm y = (x : M)
    · exfalso
      apply hyx
      refine ⟨⟨y, hyC, show κ.symm y ∈ d.W0 by rw [hxy]; exact x.2⟩, ?_⟩
      exact Prod.ext rfl (Subtype.ext hxy)
    · obtain ⟨V1, V2, hV1, hV2, h1, h2, hV12⟩ := t2_separation hxy
      refine ⟨{q | (q.1 : E0Y) ∈ κ.target ∩ κ.symm ⁻¹' V1 ∧ (q.2 : M) ∈ V2}, ?_, ?_,
        ⟨⟨hyT, h1⟩, h2⟩⟩
      · rintro ⟨y', x'⟩ ⟨⟨-, h1'⟩, h2'⟩ ⟨w, hw⟩
        simp only [Prod.mk.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        exact Set.disjoint_left.1 hV12 h1' h2'
      · refine IsOpen.inter ?_ (hV2.preimage (continuous_subtype_val.comp continuous_snd))
        have := κ.symm.isOpen_inter_preimage hV1
        rw [OpenPartialHomeomorph.symm_source] at this
        exact this.preimage (continuous_subtype_val.comp continuous_fst)
  · refine ⟨{q | (q.1 : E0Y) ∉ FY}, ?_,
      hFc.isOpen_compl.preimage (continuous_subtype_val.comp continuous_fst), hyF⟩
    rintro ⟨y', x'⟩ hy' ⟨w, hw⟩
    simp only [Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    exact hy' (hFsub w)

/-- **`M₂` is Hausdorff** (`FamilyGlueData.t2Space_iff_isClosed_graph`). -/
theorem CylChartData.t2Space_glued : T2Space (d.glueData hGH).Glued := by
  rw [Causal.CBG.FamilyGlueData.t2Space_iff_isClosed_graph]
  have h10 : IsClosed (Causal.Gluing.graph (Subtype.val : (d.glueData hGH).U true false → _)
      ((d.glueData hGH).φ true false)) := d.isClosed_graph10 hGH
  rintro (_ | _) (_ | _)
  · rw [familyGlue_graph_self]; exact isClosed_diagonal
  · rw [familyGlue_graph_swap]; exact h10.preimage continuous_swap
  · exact h10
  · rw [familyGlue_graph_self]; exact isClosed_diagonal

/-- **`M₂` is second countable** (a countable gluing of second-countable pieces). -/
theorem CylChartData.secondCountable_glued [SecondCountableTopology M] :
    SecondCountableTopology (d.glueData hGH).Glued :=
  (d.glueData hGH).secondCountableTopology

omit [HasGroupoid M e0Groupoid] [T2Space M] in
/-- **Corestriction of `𝔼₀`-morphisms to an open set** (mathlib's
`ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff`). -/
theorem isE0Mor_corestrict_iff {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
    [ChartedSpace E0Y X] [ChartedSpace E0Y Z] {U : Opens Z} (g : X → U) (s : Set X) :
    IsE0Mor (Subtype.val ∘ g) s ↔ IsE0Mor g s :=
  forall₂_congr fun x _ => ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff g s x

omit [HasGroupoid M e0Groupoid] [T2Space M] in
/-- The inclusion of an open set is an `𝔼₀`-morphism. -/
theorem isE0Mor_val {X : Type} [TopologicalSpace X] [ChartedSpace E0Y X]
    [HasGroupoid X e0Groupoid] (U : Opens X) : IsE0Mor (Subtype.val : U → X) univ := by
  have h : IsE0Mor (Subtype.val ∘ (id : U → U)) univ :=
    (isE0Mor_corestrict_iff (id : U → U) univ).2 (Causal.CBG.liftPropOn_id isOpen_univ)
  exact h

/-- The point `(v, 0)` of `𝒫`. -/
noncomputable def CylChartData.vertexP : gluePY d.v d.ε :=
  ⟨paperInY (vertex d.v), vertex d.v, vertex_mem_gluePaper d.pos, rfl⟩

/-- The point `p` of `M₀`. -/
noncomputable def CylChartData.pW0 : d.W0o hGH := ⟨p, d.mem_W0 hGH⟩

/-- The pieces are non-empty. -/
@[reducible] noncomputable def CylChartData.glueNonempty :
    ∀ b, Nonempty (gluePiece (d.W0o hGH) (gluePY d.v d.ε) b)
  | false => ⟨d.pW0 hGH⟩
  | true => ⟨d.vertexP⟩

/-- `κ` read `M₀ → 𝒫` (junk value off `U₀₁`). -/
noncomputable def CylChartData.φ'01 (x : d.W0o hGH) : gluePY d.v d.ε := by
  classical
  exact if h : chartAt E0Y p x.1 ∈ gluePY d.v d.ε then ⟨_, h⟩ else d.vertexP

/-- `κ⁻¹` read `𝒫 → M₀` (junk value off `U₁₀`). -/
noncomputable def CylChartData.φ'10 (y : gluePY d.v d.ε) : d.W0o hGH := by
  classical
  exact if h : (chartAt E0Y p).symm y.1 ∈ d.W0 then ⟨_, h⟩ else d.pW0 hGH

/-- The transitions, as maps of the whole pieces. -/
noncomputable def CylChartData.glueφ' : (i j : Bool) →
    gluePiece (d.W0o hGH) (gluePY d.v d.ε) i → gluePiece (d.W0o hGH) (gluePY d.v d.ε) j
  | false, false => id
  | false, true => d.φ'01 hGH
  | true, false => d.φ'10 hGH
  | true, true => id

theorem CylChartData.glueφ'_eq (i j : Bool) (x : (d.glueData hGH).U i j) :
    d.glueφ' hGH i j x = (d.glueData hGH).φ i j x := by
  classical
  cases i <;> cases j
  · rfl
  · show d.φ'01 hGH x.1 = d.φ01 hGH x
    unfold CylChartData.φ'01
    split_ifs with h
    · rfl
    · exact absurd x.2.2.2 h
  · show d.φ'10 hGH x.1 = d.φ10 hGH x
    unfold CylChartData.φ'10
    split_ifs with h
    · rfl
    · exact absurd x.2.2 h
  · rfl

/-- **The transitions are `𝔼₀`-morphisms** on the glued parts (`κ`, `κ⁻¹` read through the
inclusions and corestricted). -/
theorem CylChartData.liftPropOn_glueφ' (i j : Bool) :
    ChartedSpace.LiftPropOn e0Groupoid.IsLocalStructomorphWithinAt (d.glueφ' hGH i j)
      ((d.glueData hGH).U i j) := by
  classical
  have hQ : ∀ y : E0Y, e0Groupoid.IsLocalStructomorphWithinAt id univ y := fun y _ =>
    ⟨OpenPartialHomeomorph.refl E0Y, e0Groupoid.id_mem, fun _ _ => rfl, trivial⟩
  cases i <;> cases j
  · exact Causal.CBG.liftPropOn_id ((d.glueData hGH).U false false).isOpen
  · show IsE0Mor (d.φ'01 hGH) (d.U01 hGH)
    rw [← isE0Mor_corestrict_iff]
    have hκ : IsE0Mor (chartAt E0Y p) (chartAt E0Y p).source :=
      e0Groupoid.isLocalStructomorphWithinAt_localInvariantProp.liftPropOn_chart hQ
    have hval : IsE0Mor (Subtype.val : d.W0o hGH → M) (d.U01 hGH) :=
      Causal.CBG.liftPropOn_mono_of_le isOpen_univ (d.U01 hGH).isOpen (isE0Mor_val _)
        (subset_univ _)
    have hc := Causal.CBG.liftPropOn_comp (d.U01 hGH).isOpen (chartAt E0Y p).open_source hκ hval
      fun x hx => hx.1
    refine Causal.CBG.liftPropOn_congr_of_eqOn (d.U01 hGH).isOpen hc fun x hx => ?_
    have hx' : chartAt E0Y p x.1 ∈ gluePY d.v d.ε := hx.2.2
    simp only [comp_apply, CylChartData.φ'01, dif_pos hx']
  · show IsE0Mor (d.φ'10 hGH) (d.U10 hGH)
    rw [← isE0Mor_corestrict_iff]
    have hval : IsE0Mor (Subtype.val : gluePY d.v d.ε → E0Y) (d.U10 hGH) :=
      Causal.CBG.liftPropOn_mono_of_le isOpen_univ (d.U10 hGH).isOpen (isE0Mor_val _)
        (subset_univ _)
    have hc := Causal.CBG.liftPropOn_comp (d.U10 hGH).isOpen (chartAt E0Y p).open_target
      (isE0Mor_chartAt_symm p) hval fun y hy => d.cyl_sub hy.1
    refine Causal.CBG.liftPropOn_congr_of_eqOn (d.U10 hGH).isOpen hc fun y hy => ?_
    have hy' : (chartAt E0Y p).symm y.1 ∈ d.W0 := hy.2
    simp only [comp_apply, CylChartData.φ'10, dif_pos hy']
  · exact Causal.CBG.liftPropOn_id ((d.glueData hGH).U true true).isOpen

/-- **The atlas of `M₂`**: `FamilyGlueData.chartedSpace` (`Causal.CBG.gluedChartedSpace`). -/
@[reducible] noncomputable def CylChartData.glueCS : ChartedSpace E0Y (d.glueData hGH).Glued :=
  letI := d.glueNonempty hGH
  (d.glueData hGH).chartedSpace E0Y

/-- **`M₂` is an `𝔼₀`-manifold** (`FamilyGlueData.hasGroupoid_chartedSpace_of_eqOn`). -/
theorem CylChartData.glue_hasGroupoid :
    @HasGroupoid E0Y _ (d.glueData hGH).Glued _ (d.glueCS hGH) e0Groupoid :=
  letI := d.glueNonempty hGH
  (d.glueData hGH).hasGroupoid_chartedSpace_of_eqOn (d.glueφ' hGH) (d.liftPropOn_glueφ' hGH)
    (d.glueφ'_eq hGH)

/-- **The pieces embed by `𝔼₀`-morphisms** (`FamilyGlueData.liftPropOn_ι_of_eqOn`). -/
theorem CylChartData.glue_liftPropOn_ι (i : Bool) :
    @IsE0Mor _ _ _ _ _ (d.glueCS hGH) ((d.glueData hGH).ι i) univ :=
  letI := d.glueNonempty hGH
  (d.glueData hGH).liftPropOn_ι_of_eqOn (d.glueφ' hGH) (d.liftPropOn_glueφ' hGH)
    (d.glueφ'_eq hGH) i

/-- The corestriction `Y → 𝒫` (junk value off `𝒫`). -/
noncomputable def CylChartData.gIntoP (y : E0Y) : gluePY d.v d.ε := by
  classical
  exact if h : y ∈ gluePY d.v d.ε then ⟨y, h⟩ else d.vertexP

/-- **The spear chart of `M₂`**: `𝒫 ∋ y ↦ [y] ∈ M₂`. -/
noncomputable def CylChartData.ψN (y : E0Y) : (d.glueData hGH).Glued :=
  (d.glueData hGH).ι true (d.gIntoP y)

omit [HasGroupoid M e0Groupoid] [T2Space M] in
theorem CylChartData.gIntoP_of_mem {y : E0Y} (hy : y ∈ gluePY d.v d.ε) :
    d.gIntoP y = ⟨y, hy⟩ := by
  unfold CylChartData.gIntoP
  rw [dif_pos hy]

theorem CylChartData.isE0Mor_ψN :
    @IsE0Mor _ _ _ _ _ (d.glueCS hGH) (d.ψN hGH) (gluePY d.v d.ε : Set E0Y) := by
  letI := d.glueCS hGH
  have hg : IsE0Mor d.gIntoP (gluePY d.v d.ε : Set E0Y) := by
    rw [← isE0Mor_corestrict_iff]
    refine Causal.CBG.liftPropOn_congr_of_eqOn (gluePY d.v d.ε).isOpen
      (Causal.CBG.liftPropOn_id (gluePY d.v d.ε).isOpen) fun y hy => ?_
    simp only [comp_apply, d.gIntoP_of_mem hy, id]
  exact Causal.CBG.liftPropOn_comp (gluePY d.v d.ε).isOpen isOpen_univ
    (d.glue_liftPropOn_ι hGH true) hg (mapsTo_univ _ _)

theorem CylChartData.injOn_ψN : InjOn (d.ψN hGH) (gluePY d.v d.ε : Set E0Y) := by
  intro y hy y' hy' h
  have h1 := (d.glueData hGH).injective_ι true h
  rw [d.gIntoP_of_mem hy, d.gIntoP_of_mem hy'] at h1
  exact congrArg Subtype.val h1

theorem CylChartData.vertexP_mem_U10 : d.vertexP ∈ d.U10 hGH :=
  ⟨⟨vertex d.v, vertex_mem_cyl d.pos, rfl⟩, by
    show (chartAt E0Y p).symm (paperInY (vertex d.v)) ∈ d.W0
    rw [show paperInY (vertex d.v) = yVertex d.v from rfl, d.vertex_eq]; exact d.mem_W0 hGH⟩

/-- **The vertex of the spear chart of `M₂` is `p`** (glued to `p ∈ M₀`). -/
theorem CylChartData.ψN_vertex :
    d.ψN hGH (yVertex d.v) = (d.glueData hGH).ι false (d.pW0 hGH) := by
  have hmem : yVertex d.v ∈ gluePY d.v d.ε := d.vertexP.2
  rw [CylChartData.ψN, d.gIntoP_of_mem hmem]
  refine (d.glueData hGH).ι_eq_ι_iff.2 ⟨d.vertexP_mem_U10 hGH, ?_⟩
  exact Subtype.ext d.vertex_eq

omit [HasGroupoid M e0Groupoid] [T2Space M] in
theorem CylChartData.spearY_subset : spearY d.v (d.ε / 8) ⊆ (gluePY d.v d.ε : Set E0Y) :=
  image_mono (spear_subset_gluePaper d.pos)

omit [HasGroupoid M e0Groupoid] [T2Space M] in
theorem CylChartData.connectedSpace_gluePY : ConnectedSpace (gluePY d.v d.ε) :=
  isConnected_iff_connectedSpace.1 ((isConnected_gluePaper d.pos).image _
    continuous_paperInY.continuousOn)

/-- **`M₂` is connected** once `M₀` is: the two pieces are connected and meet at `p`. -/
theorem CylChartData.connectedSpace_glued [ConnectedSpace (d.W0o hGH)] :
    ConnectedSpace (d.glueData hGH).Glued := by
  haveI : ConnectedSpace (gluePiece (d.W0o hGH) (gluePY d.v d.ε) false) :=
    ‹ConnectedSpace (d.W0o hGH)›
  haveI : ConnectedSpace (gluePiece (d.W0o hGH) (gluePY d.v d.ε) true) :=
    d.connectedSpace_gluePY
  have h0 := isConnected_range ((d.glueData hGH).continuous_ι false)
  have h1 := isConnected_range ((d.glueData hGH).continuous_ι true)
  have hx0 : (d.glueData hGH).ι false (d.pW0 hGH) ∈ range ((d.glueData hGH).ι false) :=
    mem_range_self _
  have hx1 : (d.glueData hGH).ι false (d.pW0 hGH) ∈ range ((d.glueData hGH).ι true) :=
    ⟨d.gIntoP (yVertex d.v), d.ψN_vertex hGH⟩
  have hU : range ((d.glueData hGH).ι false) ∪ range ((d.glueData hGH).ι true) = univ := by
    refine eq_univ_of_forall fun z => ?_
    obtain ⟨i, x, rfl⟩ := (d.glueData hGH).exists_ι z
    cases i
    · exact Or.inl ⟨x, rfl⟩
    · exact Or.inr ⟨x, rfl⟩
  rw [connectedSpace_iff_univ, ← hU]
  exact IsConnected.union ⟨_, hx0, hx1⟩ h0 h1

/-- The inclusion `M₀ → M` is an abstract morphism. -/
theorem CylChartData.isEMorphism_val :
    Causal.IsEMorphism (CE (d.W0o hGH)) (CE M) (Subtype.val : d.W0o hGH → M) :=
  isEMorphismOn_of_isE0Mor (W := ⊤) (isE0Mor_val (d.W0o hGH))

/-- **`M₀` is globally hyperbolic in `M`**: a past set is causally convex. -/
theorem CylChartData.globallyHyperbolicOn_W0 :
    (CE M).GloballyHyperbolicOn (d.W0o hGH) :=
  Causal.Causality.GloballyHyperbolicOn.of_causallyConvexIn E0LM.e0_causallyArcConnected hGH
    ⟨le_top, fun _ _ _ hq _ hz => d.mem_W0_of_le hq (Causal.Causality.mem_diamond.1 hz).2⟩

/-- **The level sets of a Cauchy time function strictly increasing along `≤` are Cauchy
surfaces** (`Causal.Causality.IsCauchyTimeFunction.isCauchySurface` at an arbitrary level). -/
theorem isCauchySurface_level {X : Type} [TopologicalSpace X] [T1Space X]
    {C : Causal.Causality X} (hC : C.CausallyArcConnected) (hcaus : C.IsCausal)
    (hJm : ∀ q : X, C.Jminus ⊤ {q} ≠ {q}) (hJp : ∀ q : X, C.Jplus ⊤ {q} ≠ {q}) {T : X → ℝ}
    (hT : C.IsCauchyTimeFunction T) (hstrict : ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y) (a : ℝ) :
    C.IsCauchySurface (T ⁻¹' {a}) := by
  intro I c hc
  obtain ⟨ψ, -, -, hψr, hcψ⟩ := hc.reparam hC hcaus hJm hJp
  obtain ⟨hbot, htop⟩ := hT.2 _ hcψ
  have hcont : Continuous (T ∘ (c ∘ ψ)) := hT.1.continuous.comp hcψ.1.continuous
  obtain ⟨s₁, hs₁⟩ := (hbot.eventually (eventually_le_atBot a)).exists
  obtain ⟨s₂, hs₂⟩ := (htop.eventually (eventually_ge_atTop a)).exists
  obtain ⟨s, hs⟩ := intermediate_value_univ s₁ s₂ hcont ⟨hs₁, hs₂⟩
  refine ⟨c (ψ s), ⟨⟨ψ s, hψr ▸ mem_range_self s, rfl⟩, hs⟩, ?_⟩
  rintro y ⟨⟨t, ht, rfl⟩, hy0⟩
  have hy0' : T (c t) = a := hy0
  have hs' : T (c (ψ s)) = a := hs
  have hψs : ψ s ∈ I := hψr ▸ mem_range_self s
  by_contra hne
  rcases le_total (ψ s) t with h | h
  · have := hstrict _ _ (hc.1.le_of_le hψs ht h) (Ne.symm hne)
    linarith
  · have := hstrict _ _ (hc.1.le_of_le ht hψs h) hne
    linarith

include hGH in
/-- **A Cauchy surface of `M` inside `M₀`**: a level `T = a` of the Cauchy time function of
`geroch_sing_i_imp_ii`, below the compact `κ⁻¹Π` (`a < min_{κ⁻¹Π} T`). -/
theorem CylChartData.exists_cauchy_subset_W0 [SecondCountableTopology M]
    (hLM : E0LM.E0GlobalBTZ (CE M) (S0 M)) :
    ∃ S : Set M, S ⊆ d.W0 ∧ (CE M).IsCauchySurface S := by
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  have hA := E0LM.e0_singularFlatAxioms_of E0.chartIso_mem_e0Groupoid hLM
  obtain ⟨T, hT, hstrict⟩ := hA.geroch_sing_i_imp_ii (E0LM.e0_modelMeasures M hGH) hGH
  have hd0 : ((d.v + d.ε / 2, (0 : ℂ)) : E0) ∈ glueDisc d.v d.ε := by
    refine ⟨rfl, ?_⟩
    show ‖(0 : ℂ)‖ ≤ d.ε / 4
    rw [norm_zero]; linarith [d.pos]
  have hKne : d.K.Nonempty := ⟨_, _, ⟨_, hd0, rfl⟩, rfl⟩
  obtain ⟨k₀, hk₀, hmin⟩ := d.isCompact_K.exists_isMinOn hKne hT.1.continuous.continuousOn
  refine ⟨T ⁻¹' {T k₀ - 1}, ?_, isCauchySurface_level E0LM.e0_causallyArcConnected hGH.1
    hA.Jminus_ne_singleton hA.Jplus_ne_singleton hT hstrict _⟩
  rintro x hx ⟨k, hk, hkx⟩
  have hx' : T x = T k₀ - 1 := hx
  have h1 : T k₀ ≤ T k := hmin hk
  have h2 : T k ≤ T x := by
    by_cases hkx' : k = x
    · rw [hkx']
    · exact (hstrict _ _ hkx hkx').le
  linarith

include hGH in
/-- `exists_cauchy_subset_W0` with the Cauchy surface **closed** (a level set of a continuous
function). -/
theorem CylChartData.exists_closed_cauchy_subset_W0 [SecondCountableTopology M]
    (hLM : E0LM.E0GlobalBTZ (CE M) (S0 M)) :
    ∃ S : Set M, S ⊆ d.W0 ∧ (CE M).IsCauchySurface S ∧ IsClosed S := by
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  have hA := E0LM.e0_singularFlatAxioms_of E0.chartIso_mem_e0Groupoid hLM
  obtain ⟨T, hT, hstrict⟩ := hA.geroch_sing_i_imp_ii (E0LM.e0_modelMeasures M hGH) hGH
  have hd0 : ((d.v + d.ε / 2, (0 : ℂ)) : E0) ∈ glueDisc d.v d.ε := by
    refine ⟨rfl, ?_⟩
    show ‖(0 : ℂ)‖ ≤ d.ε / 4
    rw [norm_zero]; linarith [d.pos]
  have hKne : d.K.Nonempty := ⟨_, _, ⟨_, hd0, rfl⟩, rfl⟩
  obtain ⟨k₀, hk₀, hmin⟩ := d.isCompact_K.exists_isMinOn hKne hT.1.continuous.continuousOn
  refine ⟨T ⁻¹' {T k₀ - 1}, ?_, isCauchySurface_level E0LM.e0_causallyArcConnected hGH.1
    hA.Jminus_ne_singleton hA.Jplus_ne_singleton hT hstrict _,
    isClosed_singleton.preimage hT.1.continuous⟩
  rintro x hx ⟨k, hk, hkx⟩
  have hx' : T x = T k₀ - 1 := hx
  have h1 : T k₀ ≤ T k := hmin hk
  have h2 : T k ≤ T x := by
    by_cases hkx' : k = x
    · rw [hkx']
    · exact (hstrict _ _ hkx hkx').le
  linarith

/-! ### §4c The causality of the gluing `M₂` (WP-44d, DEC-108): two pieces, two charts

`M₂` is covered by the two open pieces `A = ι₀(M₀)` and `B = ι₁(𝒫)`, glued along the overlap
`𝒫 ∩ {τ < v + ε/2}`, which is causally convex in each piece; the glued causality is absolutely
minimal, so it is a `Causal.Causality.TwoPiece` (`CylChartData.twoPiece`), each piece read through
its chart (`pieceChart_of_isE0Mor`: an injective `𝔼₀`-morphism matches the relations of its image,
through the inverse morphism). -/

omit [HasGroupoid M e0Groupoid] [T2Space M] in
/-- **An injective `𝔼₀`-morphism is a chart of its image** (`Causal.Causality.PieceChart`): an open
embedding whose image relations are those of the source (`←` the morphism; `→` its inverse on the
image, `Causal.CBG.liftPropOn_invFunOn`). -/
theorem pieceChart_of_isE0Mor {X N : Type} [TopologicalSpace X] [TopologicalSpace N]
    [ChartedSpace E0Y X] [ChartedSpace E0Y N] [HasGroupoid X e0Groupoid]
    [HasGroupoid N e0Groupoid] [Nonempty X] {e : X → N} (he : IsE0Mor e univ)
    (hinj : Injective e) (A : Opens N) (hA : (A : Set N) = range e) :
    Causal.Causality.PieceChart (CE N) A (CE X) e := by
  have hE : Causal.IsEMorphismOn (CE X) (CE N) ⊤ e := isEMorphismOn_of_isE0Mor (W := ⊤) he
  have hcont : Continuous e := by
    have := hE.continuousOn; rwa [Opens.coe_top, continuousOn_univ] at this
  have hO : IsOpen (e '' univ) := hE.isOpen_image ⊤ le_rfl
  have hg : IsE0Mor (invFunOn e univ) (e '' univ) :=
    Causal.CBG.liftPropOn_invFunOn isOpen_univ he hinj.injOn
  have hgE : Causal.IsEMorphismOn (CE N) (CE X) ⟨e '' univ, hO⟩ (invFunOn e univ) :=
    isEMorphismOn_of_isE0Mor hg
  have hAle : A ≤ ⟨e '' univ, hO⟩ := by
    intro z hz
    rw [← SetLike.mem_coe, hA] at hz
    obtain ⟨x, rfl⟩ := hz
    exact ⟨x, mem_univ _, rfl⟩
  refine ⟨.of_continuous_injective_isOpenMap hcont hinj fun V hV =>
    hE.isOpen_image ⟨V, hV⟩ le_top, hA.symm, fun a b => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have h' := hgE.map_le A ⊤ hAle (fun _ _ => trivial) h
    rwa [hinj.injOn.leftInvOn_invFunOn (mem_univ a),
      hinj.injOn.leftInvOn_invFunOn (mem_univ b)] at h'
  · refine hE.map_le ⊤ A le_rfl (fun x _ => ?_) h
    show e x ∈ (A : Set N)
    rw [hA]; exact mem_range_self x

omit [HasGroupoid M e0Groupoid] [T2Space M] in
/-- **`𝒫` is causally convex in `𝔼₀`** (`f` and `r` non-decreasing along `≤`, `calculus_le`). -/
theorem mem_gluePaper_of_le {v ε : ℝ} {U V : Opens E0} {x y z : E0} (hx : x ∈ gluePaper v ε)
    (hz : z ∈ gluePaper v ε) (h1 : causality.le U x y) (h2 : causality.le V y z) :
    y ∈ gluePaper v ε := by
  have c1 := calculus_le h1
  have c2 := calculus_le h2
  exact ⟨hx.1.trans_le c1.2.2.2.2.1, c2.2.2.2.1.trans_lt hz.2⟩

omit [HasGroupoid M e0Groupoid] [T2Space M] in
/-- Relations of `𝔼₀` between points of `𝒫` are realised inside `𝒫`. -/
theorem le_of_le_top_of_mem_gluePaper {v ε : ℝ} {U : Opens E0} (hU : gluePaper v ε ⊆ U)
    {x y : E0} (hx : x ∈ gluePaper v ε) (hy : y ∈ gluePaper v ε) (h : causality.le ⊤ x y) :
    causality.le U x y := by
  obtain ⟨c, hc, hc0, hc1⟩ := (E0.causallyArcConnected ⊤ le_rfl x y).1.1 h
  have hmem : ∀ s ∈ Icc (0 : ℝ) 1, c s ∈ U := fun s hs => by
    have h1 : causality.le ⊤ x (c s) := by rw [← hc0]; exact hc.le_of_le le_rfl hs.1 hs.2
    have h2 : causality.le ⊤ (c s) y := by rw [← hc1]; exact hc.le_of_le hs.1 hs.2 le_rfl
    exact hU (mem_gluePaper_of_le hx hy h1 h2)
  exact (E0.causallyArcConnected U le_top x y).1.2
    ⟨c, Causal.CurveOn.restrict hc le_rfl le_rfl le_top hmem, hc0, hc1⟩

/-- `𝒫` as an open set of `𝔼₀`. -/
def gluePaperO (v ε : ℝ) : Opens E0 := ⟨gluePaper v ε, isOpen_gluePaper v ε⟩

omit [HasGroupoid M e0Groupoid] [T2Space M] in
theorem chartImage_gluePaperO (v ε : ℝ) :
    Causal.chartImage paperInY (gluePaperO v ε) = gluePY v ε := by
  apply SetLike.coe_injective
  rw [Causal.coe_chartImage, paperInY_source, univ_inter]
  rfl

/-- The point of `𝒫 ⊆ Y` with paper coordinates `x ∈ 𝒫`. -/
noncomputable def gluePt {v ε : ℝ} {x : E0} (hx : x ∈ gluePaper v ε) : gluePY v ε :=
  ⟨paperInY x, x, hx, rfl⟩

omit [HasGroupoid M e0Groupoid] [T2Space M] in
/-- **The relations of the spear piece `𝒫` are those of `𝔼₀`** (chart `Subtype.val` of `𝒫 ⊆ Y`,
`ceY_le_iff`, `chartIso_paperInY`, and the causal convexity of `𝒫` in `𝔼₀`). -/
theorem gluePY_le_iff {v ε : ℝ} [Nonempty (gluePY v ε)] {x y : E0} (hx : x ∈ gluePaper v ε)
    (hy : y ∈ gluePaper v ε) :
    (CE (gluePY v ε)).le ⊤ (gluePt hx) (gluePt hy) ↔ causality.le ⊤ x y := by
  have hc := pieceChart_of_isE0Mor (isE0Mor_val (gluePY v ε)) Subtype.val_injective (gluePY v ε)
    Subtype.range_coe.symm
  rw [← hc.le_iff]
  change (CE E0Y).le (gluePY v ε) (paperInY x) (paperInY y) ↔ _
  have hxY : paperInY x ∈ gluePY v ε := ⟨x, hx, rfl⟩
  have hyY : paperInY y ∈ gluePY v ε := ⟨y, hy, rfl⟩
  rw [ceY_le_iff hxY hyY, ← chartImage_gluePaperO,
    ← (chartIso_paperInY (gluePaperO v ε) (fun z _ => by simp [Causal.chartSource]) x hx y hy).1]
  exact ⟨fun h => causality.le_mono le_top h,
    fun h => le_of_le_top_of_mem_gluePaper subset_rfl hx hy h⟩

/-- `M₀` is causally convex in `M` (a past set). -/
theorem CylChartData.convex_W0 : (CE M).CausallyConvexIn (d.W0o hGH : Set M) ⊤ :=
  ⟨le_top, fun _ _ _ hq _ hz => d.mem_W0_of_le hq (Causal.Causality.mem_diamond.1 hz).2⟩

/-- **The relations of `M₀` are those of `M`.** -/
theorem CylChartData.W0_le_iff (a b : d.W0o hGH) :
    (CE (d.W0o hGH)).le ⊤ a b ↔ (CE M).le ⊤ a.1 b.1 := by
  haveI : Nonempty (d.W0o hGH) := ⟨d.pW0 hGH⟩
  have hc := pieceChart_of_isE0Mor (isE0Mor_val (d.W0o hGH)) Subtype.val_injective (d.W0o hGH)
    Subtype.range_coe.symm
  rw [← hc.le_iff]
  exact ⟨fun h => (CE M).le_mono le_top h, fun h => Causal.Causality.le_of_causallyConvexIn
    E0LM.e0_causallyArcConnected (d.convex_W0 hGH) subset_rfl a.2 b.2 h⟩

omit [HasGroupoid M e0Groupoid] [T2Space M] in
/-- A point of `𝒫` strictly below the disc level lies in the overlap (`𝒫 ∩ {τ < v + ε/2} ⊆ cyl`). -/
theorem mem_glueOverlap_of {v ε : ℝ} (hε : 0 < ε) {x : E0} (hx : x ∈ gluePaper v ε)
    (hτ : x.1 < v + ε / 2) : x ∈ glueOverlap v ε := by
  refine ⟨⟨hx, ?_, by linarith, hx.2.trans_le (by linarith)⟩, hτ⟩
  have h1 := hx.1
  simp only [fcoord] at h1
  linarith [rad_nonneg x]

/-- The causality of `M₂`. -/
noncomputable abbrev CylChartData.CG : Causal.Causality (d.glueData hGH).Glued :=
  @CE (d.glueData hGH).Glued _ (d.glueCS hGH)

theorem CylChartData.ι0_mem_O1_iff (a : d.W0o hGH) :
    (d.glueData hGH).ι false a ∈ (d.glueData hGH).O true ↔ a ∈ d.U01 hGH := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨h, -⟩ := (d.glueData hGH).ι_eq_ι_iff.1 hy.symm
    exact h
  · intro h
    exact ⟨_, (d.glueData hGH).ι_φ false true ⟨a, h⟩⟩

theorem CylChartData.ι1_mem_O0_iff (b : gluePY d.v d.ε) :
    (d.glueData hGH).ι true b ∈ (d.glueData hGH).O false ↔ b ∈ d.U10 hGH := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨h, -⟩ := (d.glueData hGH).ι_eq_ι_iff.1 hy.symm
    exact h
  · intro h
    exact ⟨_, (d.glueData hGH).ι_φ true false ⟨b, h⟩⟩

/-- The paper coordinates of a point of `U₀₁`: it is `κ⁻¹(x)` for a point `x` of the overlap. -/
theorem CylChartData.exists_coord_U01 {a : d.W0o hGH} (ha : a ∈ d.U01 hGH) :
    ∃ x ∈ glueOverlap d.v d.ε, chartAt E0Y p a.1 = paperInY x ∧
      (chartAt E0Y p).symm (paperInY x) = a.1 := by
  obtain ⟨hs, ⟨x, hxC, hx⟩, ⟨x', hxP, hx'⟩⟩ := ha
  have hxx : x = x' := paperInY.injOn (by simp) (by simp) (hx.trans hx'.symm)
  subst hxx
  have hk : (chartAt E0Y p).symm (paperInY x) = a.1 := by
    rw [hx]; exact (chartAt E0Y p).left_inv hs
  refine ⟨x, ⟨⟨hxP, hxC⟩, (d.mem_W0_iff hxP hxC).1 ?_⟩, hx.symm, hk⟩
  rw [hk]; exact a.2

/-- The spear piece read in paper coordinates: `Ψ(x) = [paperInY x] ∈ M₂`. -/
noncomputable def CylChartData.Ψ (x : E0) : (d.glueData hGH).Glued := d.ψN hGH (paperInY x)

theorem CylChartData.Ψ_eq {x : E0} (hx : x ∈ gluePaper d.v d.ε) :
    d.Ψ hGH x = (d.glueData hGH).ι true (gluePt hx) := by
  unfold CylChartData.Ψ CylChartData.ψN
  rw [d.gIntoP_of_mem (⟨x, hx, rfl⟩ : paperInY x ∈ gluePY d.v d.ε)]
  rfl

/-- **On the overlap the two pieces are identified**: `Ψ(x) = ι₀(κ⁻¹ x)`. -/
theorem CylChartData.Ψ_eq_ι0 {x : E0} (hx : x ∈ glueOverlap d.v d.ε) :
    d.Ψ hGH x = (d.glueData hGH).ι false ⟨(chartAt E0Y p).symm (paperInY x),
      (d.mem_W0_iff hx.1.1 hx.1.2).2 hx.2⟩ := by
  rw [d.Ψ_eq hGH hx.1.1]
  have hU : gluePt hx.1.1 ∈ d.U10 hGH := (d.mem_U10_iff hGH _).2 ⟨x, hx, rfl⟩
  exact ((d.glueData hGH).ι_φ true false ⟨_, hU⟩).symm

theorem CylChartData.Ψ_mem_O0_iff {x : E0} (hx : x ∈ gluePaper d.v d.ε) :
    d.Ψ hGH x ∈ (d.glueData hGH).O false ↔ x ∈ glueOverlap d.v d.ε := by
  rw [d.Ψ_eq hGH hx, d.ι1_mem_O0_iff, d.mem_U10_iff]
  constructor
  · rintro ⟨x', hx', h⟩
    have : x' = x := paperInY.injOn (by simp) (by simp) h
    exact this ▸ hx'
  · intro h; exact ⟨x, h, rfl⟩

/-- `ι₀ : M₀ → M₂` is a chart of the piece `ι₀(M₀)`. -/
theorem CylChartData.chart0 : Causal.Causality.PieceChart (d.CG hGH) ((d.glueData hGH).O false)
    (CE (d.W0o hGH)) ((d.glueData hGH).ι false) := by
  letI := d.glueCS hGH
  haveI := d.glue_hasGroupoid hGH
  haveI : Nonempty (gluePiece (d.W0o hGH) (gluePY d.v d.ε) false) := ⟨d.pW0 hGH⟩
  exact pieceChart_of_isE0Mor (d.glue_liftPropOn_ι hGH false) ((d.glueData hGH).injective_ι false)
    _ rfl

/-- `ι₁ : 𝒫 → M₂` is a chart of the piece `ι₁(𝒫)`. -/
theorem CylChartData.chart1 : Causal.Causality.PieceChart (d.CG hGH) ((d.glueData hGH).O true)
    (CE (gluePY d.v d.ε)) ((d.glueData hGH).ι true) := by
  letI := d.glueCS hGH
  haveI := d.glue_hasGroupoid hGH
  haveI : Nonempty (gluePiece (d.W0o hGH) (gluePY d.v d.ε) true) := ⟨d.vertexP⟩
  exact pieceChart_of_isE0Mor (d.glue_liftPropOn_ι hGH true) ((d.glueData hGH).injective_ι true)
    _ rfl

omit [T2Space M] in
/-- The relations of `M` between points `κ⁻¹ x`, `κ⁻¹ y` of the chart cylinder are those of `𝔼₀`. -/
theorem CylChartData.le_iff_model {x y : E0} (hx : x ∈ cyl (d.v - d.ε) (d.v + d.ε) d.ε)
    (hy : y ∈ cyl (d.v - d.ε) (d.v + d.ε) d.ε) :
    (CE M).le ⊤ ((chartAt E0Y p).symm (paperInY x)) ((chartAt E0Y p).symm (paperInY y)) ↔
      causality.le ⊤ x y :=
  ⟨fun h => causality.le_mono le_top (d.le_model hx hy h), d.le_of_le hx hy⟩

/-- **The overlap is causally convex in `M₀`.** -/
theorem CylChartData.mem_U01_of_le {a b c : d.W0o hGH} (ha : a ∈ d.U01 hGH) (hc : c ∈ d.U01 hGH)
    (hab : (CE M).le ⊤ a.1 b.1) (hbc : (CE M).le ⊤ b.1 c.1) : b ∈ d.U01 hGH := by
  obtain ⟨a', ha', -, hka⟩ := d.exists_coord_U01 hGH ha
  obtain ⟨c', hc', -, hkc⟩ := d.exists_coord_U01 hGH hc
  have hdia : b.1 ∈ (CE M).diamond ⊤ a.1 c.1 := Causal.Causality.mem_diamond.2 ⟨hab, hbc⟩
  obtain ⟨_, ⟨b', hb'C, rfl⟩, hkb⟩ := d.convex.2 _ ⟨_, ⟨a', ha'.1.2, rfl⟩, hka⟩ _
    ⟨_, ⟨c', hc'.1.2, rfl⟩, hkc⟩ hdia
  rw [← hka, ← hkb] at hab
  rw [← hkc, ← hkb] at hbc
  have h1 := d.le_model ha'.1.2 hb'C hab
  have h2 := d.le_model hb'C hc'.1.2 hbc
  have hb'P := mem_gluePaper_of_le ha'.1.1 hc'.1.1 h1 h2
  have hT := d.cyl_sub ⟨b', hb'C, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · show b.1 ∈ (chartAt E0Y p).source
    rw [← hkb]; exact (chartAt E0Y p).map_target hT
  · show chartAt E0Y p b.1 ∈ glueCY d.v d.ε
    rw [← hkb, (chartAt E0Y p).right_inv hT]; exact ⟨b', hb'C, rfl⟩
  · show chartAt E0Y p b.1 ∈ paperInY '' gluePaper d.v d.ε
    rw [← hkb, (chartAt E0Y p).right_inv hT]; exact ⟨b', hb'P, rfl⟩

/-- **The overlap is causally convex in `𝒫`.** -/
theorem CylChartData.mem_U10_of_le {a b c : gluePY d.v d.ε} (ha : a ∈ d.U10 hGH)
    (hc : c ∈ d.U10 hGH) (hab : (CE (gluePY d.v d.ε)).le ⊤ a b)
    (hbc : (CE (gluePY d.v d.ε)).le ⊤ b c) : b ∈ d.U10 hGH := by
  haveI : Nonempty (gluePY d.v d.ε) := ⟨d.vertexP⟩
  obtain ⟨_, a', ha'P, rfl⟩ := a
  obtain ⟨_, b', hb'P, rfl⟩ := b
  obtain ⟨_, c', hc'P, rfl⟩ := c
  have h1 := (gluePY_le_iff ha'P hb'P).1 hab
  have h2 := (gluePY_le_iff hb'P hc'P).1 hbc
  obtain ⟨c'', hc'', hcc⟩ := (d.mem_U10_iff hGH _).1 hc
  have hcc' : c'' = c' := paperInY.injOn (by simp) (by simp) hcc
  subst hcc'
  refine (d.mem_U10_iff hGH _).2 ⟨b', mem_glueOverlap_of d.pos hb'P ?_, rfl⟩
  exact (calculus_le h2).2.2.1.trans_lt hc''.2

/-- **On the overlap the relations of `M₀` and of `𝒫` agree.** -/
theorem CylChartData.le_iff_U01 {a b : d.W0o hGH} (ha : a ∈ d.U01 hGH) (hb : b ∈ d.U01 hGH) :
    (CE M).le ⊤ a.1 b.1 ↔ (CE (gluePY d.v d.ε)).le ⊤ (d.φ01 hGH ⟨a, ha⟩) (d.φ01 hGH ⟨b, hb⟩) := by
  haveI : Nonempty (gluePY d.v d.ε) := ⟨d.vertexP⟩
  obtain ⟨a', ha', hκa, hka⟩ := d.exists_coord_U01 hGH ha
  obtain ⟨b', hb', hκb, hkb⟩ := d.exists_coord_U01 hGH hb
  have e1 : d.φ01 hGH ⟨a, ha⟩ = gluePt ha'.1.1 := Subtype.ext hκa
  have e2 : d.φ01 hGH ⟨b, hb⟩ = gluePt hb'.1.1 := Subtype.ext hκb
  rw [e1, e2, gluePY_le_iff, ← hka, ← hkb]
  exact d.le_iff_model ha'.1.2 hb'.1.2

/-- **`M₂` is a two-piece spacetime** (`Causal.Causality.TwoPiece`): covered by `ι₀(M₀)`,
`ι₁(𝒫)`; its charted causality is absolutely minimal; the overlap is causally convex in each piece
(`mem_U01_of_le`, `mem_U10_of_le`) and the two relations agree there (`le_iff_U01`). -/
theorem CylChartData.twoPiece :
    (d.CG hGH).TwoPiece ((d.glueData hGH).O false) ((d.glueData hGH).O true) := by
  letI := d.glueCS hGH
  haveI := d.glue_hasGroupoid hGH
  have c0 := d.chart0 hGH
  have c1 := d.chart1 hGH
  refine ⟨fun z => ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨i, x, rfl⟩ := (d.glueData hGH).exists_ι z
    cases i
    · exact Or.inl ⟨x, rfl⟩
    · exact Or.inr ⟨x, rfl⟩
  · exact Causal.CBG.chartedCausality_absolutelyMinimalOn E0.chartIso_mem_e0Groupoid
      E0.absolutelyMinimalOn_YBTZ ⊤
  · intro x y z hx hz hxy hyz
    obtain ⟨a, rfl⟩ := c0.exists_eq ((d.CG hGH).le_mem_left hxy)
    obtain ⟨b, rfl⟩ := c0.exists_eq ((d.CG hGH).le_mem_right hxy)
    obtain ⟨c, rfl⟩ := c0.exists_eq ((d.CG hGH).le_mem_right hyz)
    rw [d.ι0_mem_O1_iff] at hx hz ⊢
    exact d.mem_U01_of_le hGH hx hz ((d.W0_le_iff hGH a b).1 ((c0.le_iff a b).1 hxy))
      ((d.W0_le_iff hGH b c).1 ((c0.le_iff b c).1 hyz))
  · intro x y z hx hz hxy hyz
    obtain ⟨a, rfl⟩ := c1.exists_eq ((d.CG hGH).le_mem_left hxy)
    obtain ⟨b, rfl⟩ := c1.exists_eq ((d.CG hGH).le_mem_right hxy)
    obtain ⟨c, rfl⟩ := c1.exists_eq ((d.CG hGH).le_mem_right hyz)
    rw [d.ι1_mem_O0_iff] at hx hz ⊢
    exact d.mem_U10_of_le hGH hx hz ((c1.le_iff a b).1 hxy) ((c1.le_iff b c).1 hyz)
  · intro x y hxA hxB hyA hyB
    obtain ⟨a, rfl⟩ := c0.exists_eq hxA
    obtain ⟨b, rfl⟩ := c0.exists_eq hyA
    rw [d.ι0_mem_O1_iff] at hxB hyB
    have e1 := ((d.glueData hGH).ι_φ false true ⟨a, hxB⟩).symm
    have e2 := ((d.glueData hGH).ι_φ false true ⟨b, hyB⟩).symm
    rw [c0.le_iff a b, d.W0_le_iff hGH a b, d.le_iff_U01 hGH hxB hyB]
    conv_rhs => rw [e1, e2]
    exact (c1.le_iff _ _).symm

/-- **Between two points of `M₀`, the relation of `M₂` is that of `M`.** -/
theorem CylChartData.le_ι0_iff (a b : d.W0o hGH) :
    (d.CG hGH).le ⊤ ((d.glueData hGH).ι false a) ((d.glueData hGH).ι false b) ↔
      (CE M).le ⊤ a.1 b.1 := by
  have h := d.twoPiece hGH
  have c0 := d.chart0 hGH
  constructor
  · intro hab
    exact (d.W0_le_iff hGH a b).1 ((c0.le_iff a b).1 (h.le_of_le_top (c0.mem a) (c0.mem b) hab))
  · intro hab
    exact (d.CG hGH).le_mono le_top ((c0.le_iff a b).2 ((d.W0_le_iff hGH a b).2 hab))

/-- **Between two points of `𝒫`, the relation of `M₂` is that of `𝔼₀`.** -/
theorem CylChartData.le_Ψ_iff {x y : E0} (hx : x ∈ gluePaper d.v d.ε) (hy : y ∈ gluePaper d.v d.ε) :
    (d.CG hGH).le ⊤ (d.Ψ hGH x) (d.Ψ hGH y) ↔ causality.le ⊤ x y := by
  haveI : Nonempty (gluePY d.v d.ε) := ⟨d.vertexP⟩
  have h := d.twoPiece hGH
  have c1 := d.chart1 hGH
  rw [d.Ψ_eq hGH hx, d.Ψ_eq hGH hy, ← gluePY_le_iff hx hy]
  constructor
  · intro hab
    exact (c1.le_iff _ _).1 (h.symm.le_of_le_top (c1.mem _) (c1.mem _) hab)
  · intro hab
    exact (d.CG hGH).le_mono le_top ((c1.le_iff _ _).2 hab)

/-- **A relation of `M₂` from `M₀` to `𝒫` passes through the overlap.** -/
theorem CylChartData.le_ι0_Ψ_iff (a : d.W0o hGH) {y : E0} (hy : y ∈ gluePaper d.v d.ε) :
    (d.CG hGH).le ⊤ ((d.glueData hGH).ι false a) (d.Ψ hGH y) ↔
      ∃ u ∈ glueOverlap d.v d.ε, (CE M).le ⊤ a.1 ((chartAt E0Y p).symm (paperInY u)) ∧
        causality.le ⊤ u y := by
  have h := d.twoPiece hGH
  constructor
  · intro hay
    have hyB : d.Ψ hGH y ∈ (d.glueData hGH).O true := by
      rw [d.Ψ_eq hGH hy]; exact (d.chart1 hGH).mem _
    obtain ⟨w, hwA, hwB, haw, hwy⟩ := h.exists_mid ((d.chart0 hGH).mem a) hyB hay
    obtain ⟨m, rfl⟩ := (d.chart0 hGH).exists_eq hwA
    obtain ⟨u, hu, -, hku⟩ := d.exists_coord_U01 hGH ((d.ι0_mem_O1_iff hGH m).1 hwB)
    have e : (d.glueData hGH).ι false m = d.Ψ hGH u := by
      rw [d.Ψ_eq_ι0 hGH hu]; congr 1; exact Subtype.ext hku.symm
    refine ⟨u, hu, ?_, ?_⟩
    · rw [hku]; exact (d.le_ι0_iff hGH a m).1 ((d.CG hGH).le_mono le_top haw)
    · rw [e] at hwy; exact (d.le_Ψ_iff hGH hu.1.1 hy).1 ((d.CG hGH).le_mono le_top hwy)
  · rintro ⟨u, hu, hau, huy⟩
    have h1 := (d.le_ι0_iff hGH a ⟨_, (d.mem_W0_iff hu.1.1 hu.1.2).2 hu.2⟩).2 hau
    rw [← d.Ψ_eq_ι0 hGH hu] at h1
    exact (d.CG hGH).le_trans h1 ((d.le_Ψ_iff hGH hu.1.1 hy).2 huy)

omit [HasGroupoid M e0Groupoid] [T2Space M] in
/-- **The diamonds of `𝔼₀` are compact** (closed: `isClosed_Jplus`, `isClosed_Jminus`; bounded:
`dist ≤ 3Δτ` along `≤`, `Le.dist_le`). -/
theorem isCompact_diamond_E0 (x y : E0) : IsCompact (causality.diamond ⊤ x y) := by
  have hcl : IsClosed (causality.diamond ⊤ x y) := (E0.isClosed_Jminus y).inter (E0.isClosed_Jplus x)
  refine Metric.isCompact_of_isClosed_isBounded hcl ?_
  refine (Metric.isBounded_closedBall (x := x) (r := 3 * (y.1 - x.1))).subset fun z hz => ?_
  obtain ⟨h1, h2⟩ := Causal.Causality.mem_diamond.1 hz
  rw [Metric.mem_closedBall, dist_comm]
  have := (le_top_iff.1 h1).dist_le
  have := (calculus_le h2).2.2.1
  linarith

omit [HasGroupoid M e0Groupoid] [T2Space M] in
/-- **Crossing a level of `τ` in `𝔼₀`**: a relation `u ≤ y` with `τ(u) ≤ c ≤ τ(y)` passes through a
point at time `c` (intermediate values along a causal curve). -/
theorem exists_le_fst_eq {u y : E0} (h : causality.le ⊤ u y) {c : ℝ} (hu : u.1 ≤ c)
    (hy : c ≤ y.1) : ∃ w : E0, w.1 = c ∧ causality.le ⊤ u w ∧ causality.le ⊤ w y := by
  obtain ⟨γ, hγ, hγ0, hγ1⟩ := (E0.causallyArcConnected ⊤ le_rfl u y).1.1 h
  have hcont : ContinuousOn (fun s => (γ s).1) (Icc 0 1) :=
    continuous_fst.comp_continuousOn (hγ.continuousOn causality.isRelFamily_le)
  have hmem : c ∈ Icc (γ 0).1 (γ 1).1 := by rw [hγ0, hγ1]; exact ⟨hu, hy⟩
  obtain ⟨s, hs, hsc⟩ := intermediate_value_Icc zero_le_one hcont hmem
  exact ⟨γ s, hsc, by rw [← hγ0]; exact hγ.le_of_le le_rfl hs.1 hs.2,
    by rw [← hγ1]; exact hγ.le_of_le hs.1 hs.2 le_rfl⟩

omit [HasGroupoid M e0Groupoid] [T2Space M] in
theorem mem_gluePaper_of_above {v ε : ℝ} (hε : 0 < ε) {z : E0} (hz : v + ε / 2 ≤ z.1)
    (hr : rad z < ε / 4) : z ∈ gluePaper v ε := by
  refine ⟨?_, hr⟩
  simp only [fcoord]
  linarith

/-- **`J⁺(x) ∩ J⁻(K)` is compact** for `K` compact in a tarentin globally hyperbolic Hausdorff
spacetime: closed, and inside finitely many diamonds `J(x, b_i)` (a cover of `K` by open
diamonds, `GloballyHyperbolic.exists_diamond_subset`). -/
theorem isCompact_Jplus_singleton_inter_Jminus_of_isCompact {X : Type} [TopologicalSpace X]
    [T2Space X]
    {C : Causal.Causality X} (hT : C.Tarentin) (hG : C.GloballyHyperbolic) (x : X) {K : Set X}
    (hK : IsCompact K) : IsCompact (C.Jplus ⊤ {x} ∩ C.Jminus ⊤ K) := by
  have hcl : IsClosed (C.Jplus ⊤ {x} ∩ C.Jminus ⊤ K) :=
    (hG.isClosed_Jplus_singleton hT x).inter
      (Causal.Causality.isClosed_Jminus_of_isCompact (hG.isClosed_le hT) hK)
  have hex : ∀ k : X, ∃ ab : X × X, k ∈ C.openDiamond ⊤ ab.1 ab.2 := fun k => by
    obtain ⟨a, b, hk, -⟩ := hG.exists_diamond_subset hT k univ_mem
    exact ⟨(a, b), hk⟩
  choose ab hab using hex
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun k => C.openDiamond ⊤ (ab k).1 (ab k).2)
    fun k _ => isOpen_interior.mem_nhds (hab k)
  refine (t.isCompact_biUnion fun k _ => hG.2 x (ab k).2).of_isClosed_subset hcl ?_
  rintro z ⟨hxz, k₀, hk₀, hzk₀⟩
  obtain ⟨k, hkt, hk₀k⟩ := mem_iUnion₂.1 (ht hk₀)
  have hk₀b : C.le ⊤ k₀ (ab k).2 := (Causal.Causality.mem_diamond.1 (interior_subset hk₀k)).2
  exact mem_iUnion₂.2 ⟨k, hkt, Causal.Causality.mem_diamond.2
    ⟨Causal.Precausality.mem_Jplus_singleton.1 hxz, C.le_trans hzk₀ hk₀b⟩⟩

/-- **`M₀` is globally hyperbolic** (as an `𝔼₀`-manifold: its relations are those of `M`, its
diamonds those of `M`, which lie in the past set `M₀`). -/
theorem CylChartData.globallyHyperbolic_W0o : (CE (d.W0o hGH)).GloballyHyperbolic := by
  refine ⟨fun a b hab hba => Subtype.ext (hGH.1 ((d.W0_le_iff hGH a b).1 hab)
    ((d.W0_le_iff hGH b a).1 hba)), fun a b => ?_⟩
  have heq : (CE (d.W0o hGH)).diamond ⊤ a b = Subtype.val ⁻¹' (CE M).diamond ⊤ a.1 b.1 := by
    ext z
    simp only [Causal.Causality.mem_diamond, mem_preimage, d.W0_le_iff]
  have himg : Subtype.val '' (Subtype.val ⁻¹' (CE M).diamond ⊤ a.1 b.1 : Set (d.W0o hGH)) =
      (CE M).diamond ⊤ a.1 b.1 := by
    ext z
    exact ⟨fun ⟨w, hw, e⟩ => e ▸ hw, fun hz => ⟨⟨z, (d.convex_W0 hGH).2 _ a.2 _ b.2 hz⟩, hz, rfl⟩⟩
  rw [heq, Subtype.isCompact_iff, himg]
  exact hGH.2 _ _

/-- **The spear piece `𝒫` is globally hyperbolic** (its relations are those of `𝔼₀`, its diamonds
the diamonds of `𝔼₀`, inside `𝒫` by causal convexity). -/
theorem globallyHyperbolic_gluePY {v ε : ℝ} [Nonempty (gluePY v ε)] :
    (CE (gluePY v ε)).GloballyHyperbolic := by
  refine ⟨?_, fun a b => ?_⟩
  · rintro ⟨_, a', ha', rfl⟩ ⟨_, b', hb', rfl⟩ hab hba
    have h := E0.isCausal ((gluePY_le_iff ha' hb').1 hab) ((gluePY_le_iff hb' ha').1 hba)
    subst h
    rfl
  · obtain ⟨_, a', ha', rfl⟩ := a
    obtain ⟨_, b', hb', rfl⟩ := b
    show IsCompact ((CE (gluePY v ε)).diamond ⊤ (gluePt ha') (gluePt hb'))
    rw [Subtype.isCompact_iff]
    have himg : Subtype.val '' (CE (gluePY v ε)).diamond ⊤ (gluePt ha') (gluePt hb') =
        paperInY '' causality.diamond ⊤ a' b' := by
      ext w
      constructor
      · rintro ⟨⟨_, z, hz, rfl⟩, hzd, rfl⟩
        obtain ⟨h1, h2⟩ := Causal.Causality.mem_diamond.1 hzd
        exact ⟨z, Causal.Causality.mem_diamond.2 ⟨(gluePY_le_iff ha' hz).1 h1,
          (gluePY_le_iff hz hb').1 h2⟩, rfl⟩
      · rintro ⟨z, hzd, rfl⟩
        obtain ⟨h1, h2⟩ := Causal.Causality.mem_diamond.1 hzd
        have hz := mem_gluePaper_of_le ha' hb' h1 h2
        exact ⟨gluePt hz, Causal.Causality.mem_diamond.2 ⟨(gluePY_le_iff ha' hz).2 h1,
          (gluePY_le_iff hz hb').2 h2⟩, rfl⟩
    rw [himg]
    exact (isCompact_diamond_E0 a' b').image continuous_paperInY

/-- **No relation goes from the part of `𝒫` above the disc down to `M₀`**: a diamond `J(x, y)` of
`M₂` with `x ∈ 𝒫 ∖ M₀`, `y ∈ M₀` is empty (`τ` would decrease from `x` to the overlap). -/
theorem CylChartData.diamond_eq_empty {x y : (d.glueData hGH).Glued}
    (hxB : x ∈ (d.glueData hGH).O true) (hxA : x ∉ (d.glueData hGH).O false)
    (hyA : y ∈ (d.glueData hGH).O false) : (d.CG hGH).diamond ⊤ x y = ∅ := by
  haveI : Nonempty (gluePY d.v d.ε) := ⟨d.vertexP⟩
  have h := d.twoPiece hGH
  have c1 := d.chart1 hGH
  refine eq_empty_iff_forall_notMem.2 fun z hz => ?_
  obtain ⟨h1, h2⟩ := Causal.Causality.mem_diamond.1 hz
  obtain ⟨u, huB, huA, hxu, -⟩ := h.symm.exists_mid hxB hyA ((d.CG hGH).le_trans h1 h2)
  obtain ⟨⟨_, x', hx', rfl⟩, rfl⟩ := c1.exists_eq hxB
  obtain ⟨⟨_, u', hu', rfl⟩, rfl⟩ := c1.exists_eq huB
  have hxu' := (gluePY_le_iff hx' hu').1 ((c1.le_iff _ _).1 hxu)
  have hu'O : u' ∈ glueOverlap d.v d.ε := by
    rw [← d.Ψ_mem_O0_iff hGH hu', d.Ψ_eq hGH hu']; exact huA
  have hx'O : x' ∉ glueOverlap d.v d.ε := by
    rw [← d.Ψ_mem_O0_iff hGH hx', d.Ψ_eq hGH hx']; exact hxA
  exact hx'O (mem_glueOverlap_of d.pos hx' ((calculus_le hxu').2.2.1.trans_lt hu'O.2))

include hGH in
/-- **Leaving `M₀` towards `Π`, through the overlap** (the converse half of the mixed diamonds):
if `m ∈ M₀` is below `κ⁻¹(w)`, `w` a point of the disc level `τ = v + ε/2` with `r(w) < ε/4`,
then `m ≤ κ⁻¹(u) ≤ κ⁻¹(w)` for a point `u` of the overlap. A causal curve from `m` to `κ⁻¹(w)` lies
in `M₀ ∪ {κ⁻¹ w}` (acausality of `κ⁻¹Π`), and by connectedness meets `M₀ ∩ κ⁻¹(𝒫 ∩ cyl)`. -/
theorem CylChartData.exists_overlap_of_le {m : M} (hm : m ∈ d.W0) {w : E0}
    (hw1 : w.1 = d.v + d.ε / 2) (hw2 : rad w < d.ε / 4)
    (h : (CE M).le ⊤ m ((chartAt E0Y p).symm (paperInY w))) :
    ∃ u ∈ glueOverlap d.v d.ε, (CE M).le ⊤ m ((chartAt E0Y p).symm (paperInY u)) ∧
      causality.le ⊤ u w := by
  set κ := chartAt E0Y p with hκ
  have hwD : w ∈ glueDisc d.v d.ε := ⟨hw1, hw2.le⟩
  have hwC := glueDisc_subset_cyl d.pos hwD
  have hwP : w ∈ gluePaper d.v d.ε := mem_gluePaper_of_above d.pos hw1.ge hw2
  set kw := κ.symm (paperInY w) with hkw
  have hkwK : kw ∈ d.K := ⟨_, ⟨w, hwD, rfl⟩, rfl⟩
  let PC : Opens E0 := ⟨gluePaper d.v d.ε ∩ cyl (d.v - d.ε) (d.v + d.ε) d.ε,
    (isOpen_gluePaper _ _).inter (isOpen_cyl _ _ _)⟩
  have hPC : paperInY '' (PC : Set E0) ⊆ κ.target :=
    (image_mono inter_subset_right).trans d.cyl_sub
  have hkwN : kw ∈ chartOpen p PC := mem_chartOpen hPC ⟨hwP, hwC⟩
  obtain ⟨γ, hγ, hγ0, hγ1⟩ := (E0LM.e0_causallyArcConnected ⊤ le_rfl m kw).1.1 h
  have hcont : ContinuousOn γ (Icc 0 1) := hγ.continuousOn (CE M).isRelFamily_le
  have hle0 : ∀ s ∈ Icc (0 : ℝ) 1, (CE M).le ⊤ m (γ s) := fun s hs => by
    rw [← hγ0]; exact hγ.le_of_le le_rfl hs.1 hs.2
  have hle1 : ∀ s ∈ Icc (0 : ℝ) 1, (CE M).le ⊤ (γ s) kw := fun s hs => by
    rw [← hγ1]; exact hγ.le_of_le hs.1 hs.2 le_rfl
  have hsub : γ '' Icc 0 1 ⊆ d.W0 ∪ chartOpen p PC := by
    rintro _ ⟨s, hs, rfl⟩
    by_cases hW : γ s ∈ d.W0
    · exact Or.inl hW
    · right
      obtain ⟨k₁, hk₁, hk₁s⟩ := not_not.1 hW
      have hk := d.isAcausal_K _ hk₁ _ hkwK ((CE M).le_trans hk₁s (hle1 s hs))
      rw [hk] at hk₁s
      rw [hGH.1 (hle1 s hs) hk₁s]
      exact hkwN
  obtain ⟨_, ⟨s, hs, rfl⟩, hsW, hsN⟩ := (isPreconnected_Icc.image γ hcont) _ _
    (d.isOpen_W0 hGH) (chartOpen p PC).isOpen hsub ⟨m, ⟨0, ⟨le_rfl, zero_le_one⟩, hγ0⟩, hm⟩
    ⟨kw, ⟨1, ⟨zero_le_one, le_rfl⟩, hγ1⟩, hkwN⟩
  obtain ⟨u, hu, hku⟩ := exists_of_mem_chartOpen hsN
  have huτ : u.1 < d.v + d.ε / 2 := (d.mem_W0_iff hu.1 hu.2).1 (by rw [hku]; exact hsW)
  refine ⟨u, ⟨hu, huτ⟩, by rw [hku]; exact hle0 s hs, ?_⟩
  have := hle1 s hs
  rw [← hku] at this
  exact causality.le_mono le_top (d.le_model hu.2 hwC this)

omit [T2Space M] in
include hGH in
/-- A point of `M ∖ M₀` below a point `κ⁻¹ w` of `κ⁻¹Π` is that point (`κ⁻¹Π` acausal, `M` causal). -/
theorem CylChartData.eq_of_notMem_W0 {m : M} (hm : m ∉ d.W0) {w : E0} (hw : w ∈ glueDisc d.v d.ε)
    (h : (CE M).le ⊤ m ((chartAt E0Y p).symm (paperInY w))) :
    m = (chartAt E0Y p).symm (paperInY w) := by
  obtain ⟨k₁, hk₁, hk₁m⟩ := not_not.1 hm
  have hkwK : (chartAt E0Y p).symm (paperInY w) ∈ d.K := ⟨_, ⟨w, hw, rfl⟩, rfl⟩
  have hk := d.isAcausal_K _ hk₁ _ hkwK ((CE M).le_trans hk₁m h)
  rw [hk] at hk₁m
  exact hGH.1 h hk₁m

/-- **The mixed diamonds of `M₂` are compact** (DEC-108, the step B21 never argues, and which
`Causal.CBG.TwoPiece.isCompact_diamond_mixed` cannot give: `𝒫` and `M₀` have no common Cauchy
surface). For `x ∈ M₀` and `y ∈ 𝒫` above the disc (`τ(y) ≥ v + ε/2`):
`J(ι₀ x, Ψ y) = j(D₀) ∪ Ψ(D₁)`, where `H = {τ = v + ε/2, r ≤ r(y)} ∩ J⁻(y)` (compact),
`G = H ∩ κ(J⁺_M(x))` (compact), `D₁ = {τ ≥ v + ε/2} ∩ J⁻(y) ∩ J⁺(G)` (compact in `𝔼₀`, inside `𝒫`),
`D₀ = J⁺_M(x) ∩ J⁻_M(κ⁻¹H)` (compact in `M`, `isCompact_Jplus_singleton_inter_Jminus_of_isCompact`), and
`j : M₀ ∪ κ⁻¹(𝒫 ∩ cyl) → M₂` the continuous map equal to `ι₀` on `M₀` and to `Ψ ∘ κ` on the chart
(`D₀ ⊆ M₀ ∪ κ⁻¹H` by acausality of `κ⁻¹Π`). A relation from `M₀` into `𝒫` crosses the level
`τ = v + ε/2` (`exists_le_fst_eq`) at a point of `H`; conversely a relation of `M` from `M₀` to
`κ⁻¹ w`, `w ∈ H`, passes through the overlap (`exists_overlap_of_le`). -/
theorem CylChartData.isCompact_diamond_mixed (x : d.W0o hGH) {y : E0}
    (hyP : y ∈ gluePaper d.v d.ε) (hyτ : d.v + d.ε / 2 ≤ y.1) :
    IsCompact ((d.CG hGH).diamond ⊤ ((d.glueData hGH).ι false x) (d.Ψ hGH y)) := by
  classical
  letI := d.glueCS hGH
  haveI := d.glue_hasGroupoid hGH
  set κ := chartAt E0Y p with hκ
  set c := d.v + d.ε / 2 with hc
  have hry : rad y < d.ε / 4 := hyP.2
  -- `H`: the points of the disc level below `y`
  set H : Set E0 := {w | w.1 = c ∧ rad w ≤ rad y ∧ causality.le ⊤ w y} with hH
  have hHmem : ∀ w ∈ H, w ∈ glueDisc d.v d.ε ∧ rad w < d.ε / 4 ∧ w ∈ gluePaper d.v d.ε := by
    intro w hw
    have hr : rad w < d.ε / 4 := hw.2.1.trans_lt hry
    exact ⟨⟨hw.1, hr.le⟩, hr, mem_gluePaper_of_above d.pos hw.1.ge hr⟩
  have hHcl : IsClosed H := by
    have : H = {w : E0 | w.1 = c} ∩ {w | rad w ≤ rad y} ∩ causality.Jminus ⊤ {y} := by
      ext w
      simp only [hH, mem_setOf_eq, mem_inter_iff, Causal.Precausality.mem_Jminus_singleton,
        and_assoc]
    rw [this]
    exact ((isClosed_eq continuous_fst continuous_const).inter
      (isClosed_le continuous_rad continuous_const)).inter (E0.isClosed_Jminus y)
  have hHc : IsCompact H := by
    refine ((isCompact_singleton (x := c)).prod
      (isCompact_closedBall (0 : ℂ) (rad y))).of_isClosed_subset hHcl ?_
    rintro w ⟨h1, h2, -⟩
    exact ⟨h1, mem_closedBall_zero_iff.2 h2⟩
  have hk : ContinuousOn (fun w : E0 => κ.symm (paperInY w)) H :=
    κ.continuousOn_symm.comp continuous_paperInY.continuousOn fun w hw =>
      d.cyl_sub ⟨w, glueDisc_subset_cyl d.pos (hHmem w hw).1, rfl⟩
  -- `G`: the points of `H` above `x`
  set G : Set E0 := H ∩ (fun w => κ.symm (paperInY w)) ⁻¹' (CE M).Jplus ⊤ {x.1} with hG
  have hGc : IsCompact G := hHc.of_isClosed_subset (hk.preimage_isClosed_of_isClosed hHcl
    (hGH.isClosed_Jplus_singleton E0LM.e0_tarentin x.1)) inter_subset_left
  have hle : IsClosed {z : E0 × E0 | causality.le ⊤ z.1 z.2} :=
    Causal.Causality.isClosed_le E0.tarentin E0.isClosed_Jplus E0.isClosed_Jminus
  -- `D₁`: the part of the diamond in `𝒫` above the disc
  set D1 : Set E0 := {z | c ≤ z.1} ∩ causality.Jminus ⊤ {y} ∩ causality.Jplus ⊤ G with hD1
  have hD1sub : ∀ z ∈ D1, z ∈ gluePaper d.v d.ε := fun z hz =>
    mem_gluePaper_of_above d.pos hz.1.1
      ((calculus_le (Causal.Precausality.mem_Jminus_singleton.1 hz.1.2)).2.2.2.1.trans_lt hry)
  have hD1c : IsCompact D1 := by
    refine ((isCompact_Icc (a := c) (b := y.1)).prod
      (isCompact_closedBall (0 : ℂ) (rad y))).of_isClosed_subset
      (((isClosed_le continuous_const continuous_fst).inter (E0.isClosed_Jminus y)).inter
        (Causal.Causality.isClosed_Jplus_of_isCompact hle hGc)) ?_
    rintro z ⟨⟨h1, h2⟩, -⟩
    have h2' := calculus_le (Causal.Precausality.mem_Jminus_singleton.1 h2)
    exact ⟨⟨h1, h2'.2.2.1⟩, mem_closedBall_zero_iff.2 h2'.2.2.2.1⟩
  -- `D₀`: the part of the diamond in `M₀`, closed up by `κ⁻¹ H`
  set D0 : Set M :=
    (CE M).Jplus ⊤ {x.1} ∩ (CE M).Jminus ⊤ ((fun w => κ.symm (paperInY w)) '' H) with hD0
  have hD0c : IsCompact D0 :=
    isCompact_Jplus_singleton_inter_Jminus_of_isCompact E0LM.e0_tarentin hGH x.1
    (hHc.image_of_continuousOn hk)
  -- the map `j`
  let PC : Opens E0 := ⟨gluePaper d.v d.ε ∩ cyl (d.v - d.ε) (d.v + d.ε) d.ε,
    (isOpen_gluePaper _ _).inter (isOpen_cyl _ _ _)⟩
  have hPC : paperInY '' (PC : Set E0) ⊆ κ.target :=
    (image_mono inter_subset_right).trans d.cyl_sub
  set Q := chartOpen p PC with hQ
  let j : M → (d.glueData hGH).Glued := fun m =>
    if h : m ∈ d.W0 then (d.glueData hGH).ι false (⟨m, h⟩ : d.W0o hGH) else d.ψN hGH (κ m)
  have hjW : ∀ m (h : m ∈ d.W0), j m = (d.glueData hGH).ι false (⟨m, h⟩ : d.W0o hGH) :=
    fun m h => dif_pos h
  have hjQ : ∀ m ∈ (Q : Set M), j m = d.ψN hGH (κ m) := by
    intro m hm
    obtain ⟨hms, x', hx', hxe⟩ := hm
    by_cases h : m ∈ d.W0
    · rw [hjW m h]
      have hU : (⟨m, h⟩ : d.W0o hGH) ∈ d.U01 hGH := ⟨hms, ⟨x', hx'.2, hxe⟩, ⟨x', hx'.1, hxe⟩⟩
      rw [← (d.glueData hGH).ι_φ false true ⟨_, hU⟩]
      unfold CylChartData.ψN
      rw [d.gIntoP_of_mem (⟨x', hx'.1, hxe⟩ : κ m ∈ gluePY d.v d.ε)]
      rfl
    · exact dif_neg h
  have hψc : ContinuousOn (d.ψN hGH) (gluePY d.v d.ε) := fun y hy => ((d.isE0Mor_ψN hGH) y hy).1
  have hΨc : ContinuousOn (d.Ψ hGH) (gluePaper d.v d.ε) :=
    hψc.comp continuous_paperInY.continuousOn fun z hz => ⟨z, hz, rfl⟩
  have hjc : ContinuousOn j (d.W0 ∪ (Q : Set M)) := by
    intro m hm
    apply ContinuousAt.continuousWithinAt
    rcases hm with hm | hm
    · have hcont : ContinuousOn j d.W0 := by
        rw [continuousOn_iff_continuous_restrict]
        have : d.W0.restrict j =
            fun a : d.W0 => (d.glueData hGH).ι false (⟨a.1, a.2⟩ : d.W0o hGH) :=
          funext fun a => hjW a.1 a.2
        rw [this]
        exact ((d.glueData hGH).continuous_ι false).comp (continuous_subtype_val.subtype_mk _)
      exact hcont.continuousAt ((d.isOpen_W0 hGH).mem_nhds hm)
    · have hκm : κ m ∈ gluePY d.v d.ε := by
        obtain ⟨-, x', hx', hxe⟩ := hm
        exact ⟨x', hx'.1, hxe⟩
      have h1 : ContinuousAt (fun m' => d.ψN hGH (κ m')) m :=
        (hψc.continuousAt ((gluePY d.v d.ε).isOpen.mem_nhds hκm)).comp (κ.continuousAt hm.1)
      exact h1.congr (Filter.eventually_of_mem (Q.isOpen.mem_nhds hm)
        fun m' hm' => (hjQ m' hm').symm)
  have hD0sub : D0 ⊆ d.W0 ∪ (Q : Set M) := by
    rintro m ⟨-, _, ⟨w, hwH, rfl⟩, hmw⟩
    by_cases h : m ∈ d.W0
    · exact Or.inl h
    · right
      obtain ⟨hwD, -, hwP⟩ := hHmem w hwH
      rw [d.eq_of_notMem_W0 hGH h hwD hmw]
      exact mem_chartOpen hPC ⟨hwP, glueDisc_subset_cyl d.pos hwD⟩
  -- the decomposition
  have hEq : (d.CG hGH).diamond ⊤ ((d.glueData hGH).ι false x) (d.Ψ hGH y) =
      j '' D0 ∪ d.Ψ hGH '' D1 := by
    ext z
    constructor
    · intro hz
      obtain ⟨h1, h2⟩ := Causal.Causality.mem_diamond.1 hz
      by_cases hzA : z ∈ (d.glueData hGH).O false
      · obtain ⟨m, rfl⟩ := (d.chart0 hGH).exists_eq hzA
        left
        obtain ⟨u, hu, hmu, huy⟩ := (d.le_ι0_Ψ_iff hGH m hyP).1 h2
        obtain ⟨w, hw1, huw, hwy⟩ := exists_le_fst_eq huy hu.2.le hyτ
        have hwH : w ∈ H := ⟨hw1, (calculus_le hwy).2.2.2.1, hwy⟩
        have hkuw := d.le_of_le hu.1.2 (glueDisc_subset_cyl d.pos (hHmem w hwH).1) huw
        refine ⟨m.1, ⟨Causal.Precausality.mem_Jplus_singleton.2 ((d.le_ι0_iff hGH x m).1 h1),
          _, ⟨w, hwH, rfl⟩, (CE M).le_trans hmu hkuw⟩, ?_⟩
        exact hjW m.1 m.2
      · right
        have hzB := ((d.twoPiece hGH).cover z).resolve_left hzA
        obtain ⟨z₁, rfl⟩ := (d.chart1 hGH).exists_eq hzB
        obtain ⟨z', hz', hz'e⟩ := z₁.2
        have e : (d.glueData hGH).ι true z₁ = d.Ψ hGH z' := by
          rw [d.Ψ_eq hGH hz']; congr 1; exact Subtype.ext hz'e.symm
        rw [e] at h1 h2 hzA ⊢
        have hz'c : c ≤ z'.1 := not_lt.1 fun hlt =>
          hzA ((d.Ψ_mem_O0_iff hGH hz').2 (mem_glueOverlap_of d.pos hz' hlt))
        have hz'y := (d.le_Ψ_iff hGH hz' hyP).1 h2
        obtain ⟨u, hu, hxu, huz⟩ := (d.le_ι0_Ψ_iff hGH x hz').1 h1
        obtain ⟨w, hw1, huw, hwz⟩ := exists_le_fst_eq huz hu.2.le hz'c
        have hwy := causality.le_trans hwz hz'y
        have hwH : w ∈ H := ⟨hw1, (calculus_le hwy).2.2.2.1, hwy⟩
        have hwG : w ∈ G := ⟨hwH, Causal.Precausality.mem_Jplus_singleton.2 ((CE M).le_trans hxu
          (d.le_of_le hu.1.2 (glueDisc_subset_cyl d.pos (hHmem w hwH).1) huw))⟩
        exact ⟨z', ⟨⟨hz'c, Causal.Precausality.mem_Jminus_singleton.2 hz'y⟩, w, hwG, hwz⟩, rfl⟩
    · rintro (⟨m, ⟨hxm, _, ⟨w₀, hw₀H, rfl⟩, hmw⟩, rfl⟩ |
        ⟨z', ⟨⟨hz'c, hz'y⟩, w, ⟨hwH, hxw⟩, hwz'⟩, rfl⟩)
      · have hxm' := Causal.Precausality.mem_Jplus_singleton.1 hxm
        obtain ⟨hw₀D, hw₀r, hw₀P⟩ := hHmem w₀ hw₀H
        by_cases hmW : m ∈ d.W0
        · rw [hjW m hmW]
          refine Causal.Causality.mem_diamond.2 ⟨(d.le_ι0_iff hGH x ⟨m, hmW⟩).2 hxm',
            (d.le_ι0_Ψ_iff hGH ⟨m, hmW⟩ hyP).2 ?_⟩
          obtain ⟨u, hu, hmu, huw⟩ := d.exists_overlap_of_le hGH hmW hw₀H.1 hw₀r hmw
          exact ⟨u, hu, hmu, causality.le_trans huw hw₀H.2.2⟩
        · have hme := d.eq_of_notMem_W0 hGH hmW hw₀D hmw
          have hmQ : m ∈ (Q : Set M) := by
            rw [hme]; exact mem_chartOpen hPC ⟨hw₀P, glueDisc_subset_cyl d.pos hw₀D⟩
          have hjm : j m = d.Ψ hGH w₀ := by
            rw [hjQ m hmQ, hme,
              κ.right_inv (d.cyl_sub ⟨w₀, glueDisc_subset_cyl d.pos hw₀D, rfl⟩)]
            rfl
          rw [hjm]
          rw [hme] at hxm'
          obtain ⟨u, hu, hxu, huw⟩ := d.exists_overlap_of_le hGH x.2 hw₀H.1 hw₀r hxm'
          exact Causal.Causality.mem_diamond.2 ⟨(d.le_ι0_Ψ_iff hGH x hw₀P).2 ⟨u, hu, hxu, huw⟩,
            (d.le_Ψ_iff hGH hw₀P hyP).2 hw₀H.2.2⟩
      · have hz'P := hD1sub z' ⟨⟨hz'c, hz'y⟩, w, ⟨hwH, hxw⟩, hwz'⟩
        obtain ⟨-, hwr, -⟩ := hHmem w hwH
        obtain ⟨u, hu, hxu, huw⟩ := d.exists_overlap_of_le hGH x.2 hwH.1 hwr
          (Causal.Precausality.mem_Jplus_singleton.1 hxw)
        exact Causal.Causality.mem_diamond.2 ⟨(d.le_ι0_Ψ_iff hGH x hz'P).2
          ⟨u, hu, hxu, causality.le_trans huw hwz'⟩,
          (d.le_Ψ_iff hGH hz'P hyP).2 (Causal.Precausality.mem_Jminus_singleton.1 hz'y)⟩
  rw [hEq]
  exact (hD0c.image_of_continuousOn (hjc.mono hD0sub)).union
    (hD1c.image_of_continuousOn (hΨc.mono hD1sub))

/-! #### Four facts of Lemma 2.3: two proved in WP-43a, two in WP-44d (DEC-108)

All four are stated for a `CylChartData`, i.e. **under B21's normalisation** (`BTZ_1.tex:647`):
the chart cylinder is causally convex in `M` (`CylChartData.convex`, obtained from strong
causality in `exists_cylChartData`), so `κ⁻¹Π` is acausal (`CylChartData.isAcausal_K`) and the
overlap is exactly `𝒫 ∩ cyl ∩ {τ < v + ε/2}` (`CylChartData.mem_U10_iff`). This is what makes
the frontier of `M₀` in `M₂` the disc `Π` (B21 l.661), on which the `c₀ ∪ c₁` argument rests;
for a chart cylinder chosen only inside the chart target the overlap could be smaller (a causal
curve leaving the cylinder from `κ⁻¹Π` and returning below `Π` removes the points it reaches
from `M₀`, and they stay as extra points of `𝒫`), and the two glued leaves would not follow
from that argument (audit round 2). -/

/-- **`M₀ = M ∖ J⁺(κ⁻¹Π)` is connected** (needed: CBG's `M₀` is a connected development
carrier; B21 leaves it implicit). Proved (WP-43a): every point of `M₀` is joined inside `M₀` (a
past set) to the closed Cauchy surface `S = {T = a}` below `κ⁻¹Π` along the segment of an
inextensible curve through it (`E0LM.e0_curvesExtend`), and `S` is connected
(`isConnected_of_isCauchySurface_closed`: R1 from `E0LM.sfa_isCompact_Jplus_inter_Jminus`,
no splitting and no compactness of `S`). -/
theorem CylChartData.connectedSpace_W0 [ConnectedSpace M] [SecondCountableTopology M]
    (hLM : E0LM.E0GlobalBTZ (CE M) (S0 M)) : ConnectedSpace (d.W0o hGH) := by
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  have hA := E0LM.e0_singularFlatAxioms_of E0.chartIso_mem_e0Groupoid hLM
  obtain ⟨S, hSW, hS, hScl⟩ := d.exists_closed_cauchy_subset_W0 hGH hLM
  obtain ⟨T, hTc, hTs⟩ := E0LM.e0_timeFunction hGH
  have hext := E0LM.e0_curvesExtend hGH
  have hC : (CE M).CausallyArcConnected := E0LM.e0_causallyArcConnected
  have hac : (CE M).IsAcausal S := hS.isAcausal hC hext
  have hSconn : IsConnected S := isConnected_of_isCauchySurface_closed E0LM.e0_tarentin hGH hC
    hext hS hScl hac (fun q => E0LM.sfa_isCompact_Jplus_inter_Jminus hA hGH hTc hTs hS q)
    (fun q => E0LM.sfa_isCompact_Jminus_inter_Jplus hA hGH hTc hTs hS q)
  -- every point of `M₀` is joined inside `M₀` to `S`, along an inextensible curve through it
  have hjoin : ∀ y ∈ d.W0, ∃ t ⊆ d.W0, y ∈ t ∧ (t ∩ S).Nonempty ∧ IsPreconnected t := by
    intro y hy
    obtain ⟨I, c, hc, hsub⟩ := hext _ 0 1 zero_le_one
      (Causal.Causality.causalCurveOn_const (p := y) (W := ⊤) trivial)
    obtain ⟨v, hv, hcv⟩ := hsub ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
    have hcv' : c v = y := hcv
    obtain ⟨_, ⟨⟨u, hu, rfl⟩, hσ⟩, -⟩ := hS I c hc
    refine ⟨c '' uIcc v u, ?_, ⟨v, left_mem_uIcc, hcv'⟩, ⟨c u, ⟨u, right_mem_uIcc, rfl⟩, hσ⟩,
      isPreconnected_uIcc.image _ ((continuousOn_of_causalCurveIn hc.1).mono
        (hc.1.ordConnected.uIcc_subset hv hu))⟩
    rintro _ ⟨w, hw, rfl⟩
    have hwI : w ∈ I := hc.1.ordConnected.uIcc_subset hv hu hw
    rcases le_total v u with h | h
    · rw [uIcc_of_le h] at hw
      exact d.mem_W0_of_le (hSW hσ) (hc.1.le_of_le hwI hu hw.2)
    · rw [uIcc_of_ge h] at hw
      exact d.mem_W0_of_le hy (hcv' ▸ hc.1.le_of_le hwI hv hw.2)
  have hW0 : IsConnected d.W0 := by
    obtain ⟨s₀, hs₀⟩ := hSconn.nonempty
    refine ⟨⟨s₀, hSW hs₀⟩, isPreconnected_of_forall s₀ fun y hy => ?_⟩
    obtain ⟨t, htW, hyt, ⟨z, hzt, hzS⟩, htc⟩ := hjoin y hy
    exact ⟨t ∪ S, union_subset htW hSW, Or.inr hs₀, Or.inl hyt,
      IsPreconnected.union z hzt hzS htc hSconn.isPreconnected⟩
  exact isConnected_iff_connectedSpace.1 hW0

/-- **A Cauchy surface of `M` inside the past set `M₀` is a Cauchy surface of `M₀`.** True: the
maximal extension `c′` in `M` of an inextensible curve `c` of `M₀` meets `M₀` in an initial
segment (`M₀` is a past set), which is `c` by inextensibility; it contains the point of `c′` on
`S ⊆ M₀`. Proved (WP-43a): Levin's time function and `isCauchySurfaceOn_of_isPast` (the
relative extension lemmas of §4a′ handle the constant pieces and unbounded parameters that
blocked round 2). -/
theorem CylChartData.isCauchySurfaceOn_W0 [SecondCountableTopology M] {S : Set M} (hSW : S ⊆ d.W0)
    (hS : (CE M).IsCauchySurface S) : (CE M).IsCauchySurfaceOn (d.W0o hGH) S := by
  obtain ⟨τ, hτ, -, hτs⟩ :=
    Causal.Causality.exists_timeFunction_of_secondCountable E0LM.e0_tarentin hGH
  exact isCauchySurfaceOn_of_isPast E0LM.e0_causallyArcConnected hGH.1 hτ hτs
    (fun _ _ hx hyx => d.mem_W0_of_le hx hyx) hSW hS

/-- **`M₂` is globally hyperbolic** (DEC-108; B21 does not argue it: it shows `Σ` Cauchy in `M₂`
and concludes). Causal: a two-piece spacetime of causal pieces (`TwoPiece.isCausal`). Diamonds:
inside `M₀` or inside `𝒫`, those of the piece (`PieceChart.isCompact_diamond`, both pieces GH);
from `𝒫 ∖ M₀` to `M₀`, empty (`diamond_eq_empty`); from `M₀` to `𝒫 ∖ M₀`, compact
(`isCompact_diamond_mixed`). Under the normalisation of `CylChartData`. -/
theorem CylChartData.globallyHyperbolic_glued :
    (@CE (d.glueData hGH).Glued _ (d.glueCS hGH)).GloballyHyperbolic := by
  letI := d.glueCS hGH
  haveI := d.glue_hasGroupoid hGH
  haveI : Nonempty (gluePY d.v d.ε) := ⟨d.vertexP⟩
  have h := d.twoPiece hGH
  have c0 := d.chart0 hGH
  have c1 := d.chart1 hGH
  have hG0 := d.globallyHyperbolic_W0o hGH
  have hG1 : (CE (gluePY d.v d.ε)).GloballyHyperbolic := globallyHyperbolic_gluePY
  refine ⟨h.isCausal (c0.antisymm hG0.1) (c1.antisymm hG1.1), fun x y => ?_⟩
  have hmixed : ∀ x y, x ∈ (d.glueData hGH).O false → y ∈ (d.glueData hGH).O true →
      y ∉ (d.glueData hGH).O false → IsCompact ((d.CG hGH).diamond ⊤ x y) := by
    intro x y hxA hyB hyA
    obtain ⟨a, rfl⟩ := c0.exists_eq hxA
    obtain ⟨y₁, rfl⟩ := c1.exists_eq hyB
    obtain ⟨y', hy', hye⟩ := y₁.2
    have e : (d.glueData hGH).ι true y₁ = d.Ψ hGH y' := by
      rw [d.Ψ_eq hGH hy']; congr 1; exact Subtype.ext hye.symm
    rw [e] at hyA ⊢
    have hyτ : d.v + d.ε / 2 ≤ y'.1 := not_lt.1 fun hlt =>
      hyA ((d.Ψ_mem_O0_iff hGH hy').2 (mem_glueOverlap_of d.pos hy' hlt))
    exact d.isCompact_diamond_mixed hGH a hy' hyτ
  by_cases hxA : x ∈ (d.glueData hGH).O false <;> by_cases hyA : y ∈ (d.glueData hGH).O false
  · exact c0.isCompact_diamond h hG0 hxA hyA
  · exact hmixed x y hxA ((h.cover y).resolve_left hyA) hyA
  · have hxB := (h.cover x).resolve_left hxA
    rw [d.diamond_eq_empty hGH hxB hxA hyA]
    exact isCompact_empty
  · exact c1.isCompact_diamond h.symm hG1 ((h.cover x).resolve_left hxA)
      ((h.cover y).resolve_left hyA)

omit [HasGroupoid M e0Groupoid] [T2Space M] in
/-- **Past ends above the disc converge in `𝒫`** (as `E0.pastExtensible_sliceDom`): a causal curve
of `𝒫` (paper coordinates) at `τ ≥ v + ε/2`, over a parameter interval bounded below, converges at
its past end (`τ`, `r` monotone and bounded, `E0.exists_tendsto_of_bddBelow`) to a point still in
`𝒫` (`τ ≥ v + ε/2`, `r` no larger), where it is adjoined. -/
theorem pastExtensible_gluePaper {v ε : ℝ} (hε : 0 < ε) {J : Set ℝ} {γ : ℝ → E0}
    (hγ : causality.CausalCurveIn (gluePaperO v ε) J γ) (hJ : BddBelow J)
    (hT : ∀ u ∈ J, v + ε / 2 ≤ (γ u).1) : causality.PastExtensible (gluePaperO v ε) J γ := by
  by_cases hmin : ∃ a', IsLeast J a'
  · obtain ⟨a', ha⟩ := hmin
    exact Causal.Causality.pastExtensible_of_isLeast E0.causallyArcConnected E0.isCausal hγ ha
      (E0.Jminus_ne_singleton (hγ.mem ha.1))
  have hglb : IsGLB J (sInf J) := isGLB_csInf hγ.nonempty hJ
  have hαJ : sInf J ∉ J := fun hα => hmin ⟨_, hα, hglb.1⟩
  have hgt : ∀ u ∈ J, sInf J < u := fun u hu =>
    lt_of_le_of_ne (hglb.1 hu) fun he => hαJ (he ▸ hu)
  have hle := E0.le_of_le_top_curve hγ
  obtain ⟨u₀, hu₀⟩ := hγ.nonempty
  have hbdd : BddBelow ((fun u => (γ u).1) '' J) := ⟨v + ε / 2, by
    rintro _ ⟨u, hu, rfl⟩; exact hT u hu⟩
  obtain ⟨q, hq⟩ := E0.exists_tendsto_of_bddBelow
    (fun u hu u' hu' h => E0.le_top_iff.1 (hle u hu u' hu' h)) hγ.nonempty hγ.ordConnected hglb
    hαJ hbdd
  have hsub := Causal.Flat.Ioo_subset_of_isGLB hγ.ordConnected hglb hu₀
  have hev : ∀ᶠ u in 𝓝[>] (sInf J), u ∈ J :=
    mem_of_superset (Ioo_mem_nhdsGT (hgt u₀ hu₀)) hsub
  have hqz : causality.le ⊤ q (γ u₀) := by
    refine Causal.Precausality.mem_Jminus_singleton.1
      ((E0.isClosed_Jminus (γ u₀)).mem_of_tendsto hq ?_)
    filter_upwards [Ioo_mem_nhdsGT (hgt u₀ hu₀)] with u hu
    exact Causal.Precausality.mem_Jminus_singleton.2 (hle u (hsub hu) u₀ hu₀ hu.2.le)
  have hτq : v + ε / 2 ≤ q.1 := (isClosed_le continuous_const continuous_fst).mem_of_tendsto hq
    (hev.mono fun u hu => hT u hu)
  have hqP : q ∈ gluePaperO v ε :=
    mem_gluePaper_of_above hε hτq ((calculus_le hqz).2.2.2.1.trans_lt (hγ.mem hu₀).2)
  exact Causal.Causality.pastExtensible_of_tendsto_opens E0.isClosed_Jminus E0.stronglyCausal
    E0.causallyArcConnected E0.isCausal hγ hqP hgt
    (Causal.Flat.ordConnected_insert_of_isGLB hγ.ordConnected hglb) hq (E0.Jminus_ne_singleton hqP)

/-- **No inextensible causal curve of `M₂` stays in `𝒫` above the disc** (B21's « `c₁` reaches
`Π` », l.663): read in paper coordinates (through `ψN⁻¹` and `paperOfY`, inextensibility
transported by `IsEMorphismOn.inextensible_iff_invComp`), such a curve is an inextensible causal
curve of `𝒫` at `τ ≥ v + ε/2`, and its past end converges in `𝒫` (`pastExtensible_gluePaper`). -/
theorem CylChartData.not_inextensible_above {I : Set ℝ} {c : ℝ → (d.glueData hGH).Glued}
    (hc : (d.CG hGH).Inextensible ⊤ I c) (hA : ∀ t ∈ I, c t ∉ (d.glueData hGH).O false) :
    False := by
  letI := d.glueCS hGH
  haveI := d.glue_hasGroupoid hGH
  haveI := d.t2Space_glued hGH
  have hGG := d.globallyHyperbolic_glued hGH
  have h := d.twoPiece hGH
  have hB : ∀ t ∈ I, c t ∈ (d.glueData hGH).O true := fun t ht =>
    (h.cover (c t)).resolve_left (hA t ht)
  obtain ⟨t₀, ht₀⟩ := hc.1.nonempty
  have hcB : (d.CG hGH).Inextensible ((d.glueData hGH).O true) I c := by
    have hJ := Causal.Causality.inextensible_ordConnectedComponent_of_le (U := ⊤)
      (W := (d.glueData hGH).O true) (fun x y h₁ h₂ => hGG.1 h₁ h₂) le_top hc ht₀ (hB t₀ ht₀)
    have hI : I ∩ c ⁻¹' ((d.glueData hGH).O true : Set _) = I :=
      inter_eq_left.2 fun t ht => hB t ht
    haveI : I.OrdConnected := hc.1.ordConnected
    rwa [hI, show ordConnectedComponent I t₀ = I from
      subset_antisymm ordConnectedComponent_subset (subset_ordConnectedComponent ht₀ subset_rfl)]
      at hJ
  -- to `𝒫 ⊆ Y` through `ψN`
  have hψE : Causal.IsEMorphismOn (CE E0Y) (d.CG hGH) (gluePY d.v d.ε) (d.ψN hGH) :=
    isEMorphismOn_of_isE0Mor (d.isE0Mor_ψN hGH)
  have hg₁ : LeftInvOn (invFunOn (d.ψN hGH) (gluePY d.v d.ε : Set E0Y)) (d.ψN hGH)
      (gluePY d.v d.ε) := (d.injOn_ψN hGH).leftInvOn_invFunOn
  have hrange : (((d.glueData hGH).O true : Opens _) : Set _) =
      d.ψN hGH '' (gluePY d.v d.ε : Set E0Y) := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.1, y.2, by rw [CylChartData.ψN, d.gIntoP_of_mem y.2]; rfl⟩
    · rintro ⟨y, -, rfl⟩
      exact ⟨d.gIntoP y, rfl⟩
  have h1 := (hψE.inextensible_iff_invComp (d.injOn_ψN hGH) hg₁ le_rfl hrange hB).1 hcB
  -- the charted causality of `Y` is the model causality `D`
  have h2 : E0LM.D.Inextensible (gluePY d.v d.ε) I
      (invFunOn (d.ψN hGH) (gluePY d.v d.ε : Set E0Y) ∘ c) :=
    (Causal.Causality.inextensible_congr_causality fun N _ x y =>
      ⟨fun hxy => (ceY_le_iff ((CE E0Y).le_mem_left hxy) ((CE E0Y).le_mem_right hxy)).1 hxy,
        fun hxy => (ceY_le_iff (E0LM.D.le_mem_left hxy) (E0LM.D.le_mem_right hxy)).2 hxy⟩).1 h1
  -- to paper coordinates through `paperInY`
  have hpE := E0CBG.isEMorphismOn_of_chartIso chartIso_paperInY
  have hgp : LeftInvOn paperOfY paperInY (Causal.chartSource paperInY) := fun w _ => by
    simp [paperInY_apply]
  have hVW : gluePaperO d.v d.ε ≤ Causal.chartSource paperInY := fun w _ => by
    show w ∈ paperInY.source; rw [paperInY_source]; trivial
  have heU : ∀ t ∈ I, (invFunOn (d.ψN hGH) (gluePY d.v d.ε : Set E0Y) ∘ c) t ∈ gluePY d.v d.ε :=
    fun t ht => (Causal.IsEMorphismOn.leftInvOn_image hg₁ le_rfl hrange (hB t ht)).1
  have h3 := (hpE.inextensible_iff_invComp paperInY.injOn hgp hVW rfl heU).1 h2
  -- the curve stays above the disc
  have hτ : ∀ t ∈ I, d.v + d.ε / 2 ≤
      (paperOfY (invFunOn (d.ψN hGH) (gluePY d.v d.ε : Set E0Y) (c t))).1 := by
    intro t ht
    have hP : paperOfY (invFunOn (d.ψN hGH) (gluePY d.v d.ε : Set E0Y) (c t)) ∈
        gluePaper d.v d.ε := h3.1.mem ht
    have e1 := (Causal.IsEMorphismOn.leftInvOn_image hgp hVW rfl (heU t ht)).2
    have e2 := (Causal.IsEMorphismOn.leftInvOn_image hg₁ le_rfl hrange (hB t ht)).2
    refine not_lt.1 fun hlt => hA t ht ?_
    have hO := (d.Ψ_mem_O0_iff hGH hP).2 (mem_glueOverlap_of d.pos hP hlt)
    simp only [comp_apply] at e1 e2
    rwa [CylChartData.Ψ, e1, e2] at hO
  obtain ⟨hpi, -⟩ := Causal.Causality.inextensible_iff.1 h3
  obtain ⟨hd, hsub, htan, hpast, -⟩ := h3.1.arctanReparam
  exact hpi.2 (hpast (pastExtensible_gluePaper d.pos hd
    ⟨-(Real.pi / 2), fun u hu => (hsub hu).1.le⟩ fun u hu => hτ _ (htan u hu)))

/-- **`Σ` is a Cauchy surface of `M₂`** (B21 l.660–666: a past-inextensible causal curve of `M₂`
splits as `c₀ = c ∩ M₀`, `c₁ = c ∖ M₀`, `c₁` reaching `Π` and never `Σ`, `c₀` meeting `Σ` once).
An inextensible curve meets `M₀` (`not_inextensible_above`); its component there is inextensible in
`M₀`, where `Σ` is Cauchy (`isCauchySurfaceOn_W0`); two points of `Σ` on it are related in `M`,
where `Σ` is acausal. Under the normalisation of `CylChartData`. -/
theorem CylChartData.isCauchySurface_glued [SecondCountableTopology M] {S : Set M}
    (hSW : S ⊆ d.W0) (hS : (CE M).IsCauchySurface S) :
    (@CE (d.glueData hGH).Glued _ (d.glueCS hGH)).IsCauchySurface
      ((d.glueData hGH).ι false '' (Subtype.val ⁻¹' S : Set (d.W0o hGH))) := by
  letI := d.glueCS hGH
  haveI := d.glue_hasGroupoid hGH
  haveI := d.t2Space_glued hGH
  have hGG := d.globallyHyperbolic_glued hGH
  -- `S` is a Cauchy surface of `M₀` (`isCauchySurfaceOn_W0`), hence of the piece `ι₀(M₀)`
  have hS0 : (CE (d.W0o hGH)).IsCauchySurface (Subtype.val ⁻¹' S : Set (d.W0o hGH)) := by
    have hval := d.isEMorphism_val hGH
    have hU : ((d.W0o hGH : Opens M) : Set M) =
        Subtype.val '' ((⊤ : Opens (d.W0o hGH)) : Set (d.W0o hGH)) := by
      rw [Opens.coe_top, image_univ, Subtype.range_coe]
    refine (hval.isCauchySurfaceOn_image_iff Subtype.val_injective.injOn le_rfl hU
      (subset_univ _)).2 ?_
    have himg : Subtype.val '' (Subtype.val ⁻¹' S : Set (d.W0o hGH)) = S := by
      ext x
      exact ⟨fun ⟨y, hy, hyx⟩ => hyx ▸ hy, fun hx => ⟨⟨x, hSW hx⟩, hx, rfl⟩⟩
    rw [himg]
    exact d.isCauchySurfaceOn_W0 hGH hSW hS
  have hE0 : Causal.IsEMorphismOn (CE (d.W0o hGH)) (d.CG hGH) ⊤ ((d.glueData hGH).ι false) :=
    isEMorphismOn_of_isE0Mor (W := ⊤) (d.glue_liftPropOn_ι hGH false)
  have hSA := (hE0.isCauchySurfaceOn_image_iff ((d.glueData hGH).injective_ι false).injOn le_rfl
    (U := (d.glueData hGH).O false) (by rw [Opens.coe_top, image_univ]; rfl)
    (subset_univ _)).1 (Causal.Causality.isCauchySurfaceOn_top.2 hS0)
  have hac := hS.isAcausal E0LM.e0_causallyArcConnected (E0LM.e0_curvesExtend hGH)
  intro I c hc
  obtain ⟨x, hx⟩ : ∃ x, x ∈ c '' I ∩
      ((d.glueData hGH).ι false '' (Subtype.val ⁻¹' S : Set (d.W0o hGH))) := by
    by_cases hmeet : ∃ t ∈ I, c t ∈ (d.glueData hGH).O false
    · obtain ⟨t₀, ht₀, hmem⟩ := hmeet
      obtain ⟨_, ⟨⟨τ, hτ, rfl⟩, hxS⟩, -⟩ := hSA _ c
        (Causal.Causality.inextensible_ordConnectedComponent_of_le (U := ⊤)
          (fun x y h₁ h₂ => hGG.1 h₁ h₂) le_top hc ht₀ hmem)
      exact ⟨c τ, ⟨τ, (ordConnectedComponent_subset hτ).1, rfl⟩, hxS⟩
    · exact (d.not_inextensible_above hGH hc fun t ht hm => hmeet ⟨t, ht, hm⟩).elim
  refine ⟨x, hx, ?_⟩
  have key : ∀ a ∈ (d.glueData hGH).ι false '' (Subtype.val ⁻¹' S : Set (d.W0o hGH)),
      ∀ b ∈ (d.glueData hGH).ι false '' (Subtype.val ⁻¹' S : Set (d.W0o hGH)),
      (d.CG hGH).le ⊤ a b → a = b := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    rw [Subtype.ext (hac _ ha _ hb ((d.le_ι0_iff hGH a b).1 hab))]
  rintro _ ⟨⟨s, hs, rfl⟩, hyS⟩
  obtain ⟨⟨t, ht, rfl⟩, hxS⟩ := hx
  rcases le_total s t with hst | hts
  · exact key _ hyS _ hxS (hc.1.le_of_le hs ht hst)
  · exact (key _ hxS _ hyS (hc.1.le_of_le ht hs hts)).symm

end GlueData

/-! ### §5 B21 Lemma 2.4 (`lem:add_BTZ_param`): a Cauchy surface as a graph over the spear -/

section AddBTZParam

open E0CBG

variable {M : Type} [TopologicalSpace M] [ChartedSpace E0Y M]

/-- **A closed piece of a closed spear image is closed**: if `ψ(spearY v R)` is closed in `M`
(`ψ` an injective `𝔼₀`-morphism on an open `W ⊇ spearY v R`), so is `ψ(S')` for every closed
`S' ⊆ spearY v R` of `Y` (`ψ` is an open map on `W`; no global hypothesis on `M`). -/
theorem isClosed_image_spearY_of_subset [HasGroupoid M e0Groupoid] {v R : ℝ} {W : Set E0Y}
    {ψ : E0Y → M} (hW : IsOpen W) (hsub : spearY v R ⊆ W) (hψ : IsE0Mor ψ W) (hinj : InjOn ψ W)
    (hcl : IsClosed (ψ '' spearY v R)) {S' : Set E0Y} (hS' : IsClosed S')
    (hS'S : S' ⊆ spearY v R) : IsClosed (ψ '' S') := by
  have hE := Causal.CBG.isEMorphismOn_of_liftPropOn E0.chartIso_mem_e0Groupoid
    E0.absolutelyMinimalOn_YBTZ (W := ⟨W, hW⟩) hψ
  refine isClosed_of_closure_subset fun m hm => ?_
  have hmU : m ∈ ψ '' spearY v R := hcl.closure_subset (closure_mono (image_mono hS'S) hm)
  obtain ⟨y, hy, rfl⟩ := hmU
  by_contra hyS'
  have hyS'' : y ∉ S' := fun h => hyS' ⟨y, h, rfl⟩
  have hNo : IsOpen (W ∩ S'ᶜ) := hW.inter hS'.isOpen_compl
  have hopen := hE.isOpen_image ⟨_, hNo⟩ inter_subset_left
  obtain ⟨_, ⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩ :=
    mem_closure_iff.1 hm _ hopen ⟨y, ⟨hsub hy, hyS''⟩, rfl⟩
  exact ha.2 (by rw [hinj ha.1 (hsub (hS'S hb)) hab.symm]; exact hb)

/-- **Moving the vertex up the ray**: a spear neighbourhood of vertex `q` gives one of vertex
every point `γ t` of its ray, of the same radius (the first case of the proof of Lemma 2.4,
« if `q` is in the past of `p` »). -/
theorem IsSpearNbhd.of_ray [HasGroupoid M e0Groupoid] {q : M} {R : ℝ} {U : Set M}
    (h : IsSpearNbhd q R U) :
    ∃ (v : ℝ) (W : Set E0Y) (ψ : E0Y → M), IsOpen W ∧ spearY v R ⊆ W ∧ IsE0Mor ψ W ∧
      InjOn ψ W ∧ ψ (yVertex v) = q ∧ ∀ t, 0 ≤ t → IsSpearNbhd (ψ (yAxis v t)) R
        (ψ '' spearY (v + t) R) := by
  obtain ⟨v, W, ψ, hW, hSW, hψ, hinj, hq, rfl⟩ := h.chart
  have hsub : ∀ t, 0 ≤ t → spearY (v + t) R ⊆ spearY v R := fun t ht =>
    image_mono (spear_mono (by linarith) le_rfl)
  refine ⟨v, W, ψ, hW, hSW, hψ, hinj, hq, fun t ht => ⟨h.pos,
    isClosed_image_spearY_of_subset hW hSW hψ hinj h.isClosed (isClosed_spearY _ _) (hsub t ht),
    v + t, W, ψ, hW, (hsub t ht).trans hSW, hψ, hinj, rfl, rfl⟩⟩

/-- **`≪` is irreflexive on a globally hyperbolic `𝔼₀`-manifold**: `I⁺(x) ∩ I⁻(x)` is open and,
by causality, contained in `{x}`, while `x` is not isolated. -/
theorem not_lt_self (hGH : (CE M).GloballyHyperbolic) (x : M) : ¬ (CE M).lt ⊤ x x := by
  intro hx
  have hO : IsOpen ({y | (CE M).lt ⊤ x y} ∩ {y | (CE M).lt ⊤ y x}) :=
    ((CE M).isOpen_lt_right ⊤ x).inter ((CE M).isOpen_lt_left ⊤ x)
  have hsub : {y | (CE M).lt ⊤ x y} ∩ {y | (CE M).lt ⊤ y x} ⊆ {x} := fun y hy =>
    hGH.1 ((CE M).le_of_lt hy.2) ((CE M).le_of_lt hy.1)
  haveI := E0LM.charted_nhdsNE_neBot (M := M) E0LM.e0Y_nhdsNE_neBot x
  have h1 : ({x} : Set M) ∈ 𝓝 x := Filter.mem_of_superset (hO.mem_nhds ⟨hx, hx⟩) hsub
  have h2 : ({x}ᶜ ∩ {x} : Set M) ∈ 𝓝[≠] x :=
    Filter.inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds h1)
  obtain ⟨y, hy1, hy2⟩ := Filter.nonempty_of_mem h2
  exact hy1 hy2

/-- **A Cauchy surface does not meet its chronological past.** -/
theorem notMem_of_mem_Iminus [HasGroupoid M e0Groupoid] [T2Space M] [SecondCountableTopology M]
    (hGH : (CE M).GloballyHyperbolic) {Sig : Set M}
    (hSig : (CE M).IsCauchySurface Sig) {x : M} (hx : x ∈ (CE M).Iminus ⊤ Sig) : x ∉ Sig := by
  intro hxS
  obtain ⟨σ, hσ, hxσ⟩ := hx
  have hac := hSig.isAcausal E0LM.e0_causallyArcConnected (E0LM.e0_curvesExtend hGH)
  have := hac x hxS σ hσ ((CE M).le_of_lt hxσ)
  subst this
  exact not_lt_self hGH x hxσ

theorem isOpen_Iminus (A : Set M) : IsOpen ((CE M).Iminus ⊤ A) := by
  have : (CE M).Iminus ⊤ A = ⋃ a ∈ A, {y | (CE M).lt ⊤ y a} := by
    ext y; simp [Causal.Precausality.mem_Iminus]
  rw [this]
  exact isOpen_biUnion fun a _ => (CE M).isOpen_lt_left ⊤ a

/-- **B21 Lemma 2.4, proved part** (`BTZ_1.tex:685–695` and the second half of its proof,
l.727–741): for a spear neighbourhood of vertex `p ∈ I⁻(Σ)`, after shrinking the radius,
(a) `Σ` meets the spear only in its shaft region `τ > v + R′/2`, and (b) on each vertical null
line `{z} × ℝ` of the spear it meets it at most once (the paper's « each `c_{θ₀,r₀}` intersects
`Φ(Σ ∩ 𝒮′)` at most once »; here the vertical half of `c_{θ₀,r₀}` suffices). -/
theorem spear_shaft_vertical [HasGroupoid M e0Groupoid] [T2Space M] [SecondCountableTopology M]
    (hGH : (CE M).GloballyHyperbolic) {Sig : Set M}
    (hSig : (CE M).IsCauchySurface Sig) {p : M} {R : ℝ} {U : Set M} (hU : IsSpearNbhd p R U)
    (hpS : p ∈ (CE M).Iminus ⊤ Sig) :
    ∃ (R' v : ℝ) (W : Set E0Y) (ψ : E0Y → M), 0 < R' ∧ R' ≤ R ∧ IsOpen W ∧ spearY v R' ⊆ W ∧
      IsE0Mor ψ W ∧ InjOn ψ W ∧ ψ (yVertex v) = p ∧
      (∀ x ∈ spear v R', x.1 ≤ v + R' / 2 → ψ (paperInY x) ∈ (CE M).Iminus ⊤ Sig) ∧
      (∀ x ∈ spear v R', ψ (paperInY x) ∈ Sig → v + R' / 2 < x.1) ∧
      (∀ x ∈ spear v R', ∀ y ∈ spear v R', x.2 = y.2 → ψ (paperInY x) ∈ Sig →
        ψ (paperInY y) ∈ Sig → x = y) := by
  obtain ⟨v, W, ψ, hW, hSW, hψ, hinj, hp, -⟩ := hU.chart
  have hR := hU.pos
  -- the open neighbourhood of the vertex mapped into `I⁻(Σ)`
  set Φ : E0 → M := ψ ∘ paperInY with hΦ
  have hψc : ContinuousOn ψ W := fun x hx => (hψ x hx).continuousWithinAt
  have hPo : IsOpen (paperInY ⁻¹' W) := hW.preimage continuous_paperInY
  have hΦc : ContinuousOn Φ (paperInY ⁻¹' W) :=
    hψc.comp continuous_paperInY.continuousOn (fun _ h => h)
  have hV : IsOpen (paperInY ⁻¹' W ∩ Φ ⁻¹' ((CE M).Iminus ⊤ Sig)) :=
    hΦc.isOpen_inter_preimage hPo (isOpen_Iminus Sig)
  have hvV : vertex v ∈ paperInY ⁻¹' W ∩ Φ ⁻¹' ((CE M).Iminus ⊤ Sig) := by
    refine ⟨hSW ⟨_, vertex_mem_spear hR.le, rfl⟩, ?_⟩
    show ψ (yVertex v) ∈ (CE M).Iminus ⊤ Sig
    rw [hp]; exact hpS
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV _ hvV
  set R' := min R (ε / 2) with hR'
  have hR'pos : 0 < R' := lt_min hR (by linarith)
  have hR'R : R' ≤ R := min_le_left _ _
  have hR'ε : R' ≤ ε / 2 := min_le_right _ _
  have hsub : spearY v R' ⊆ W := (image_mono (spear_mono le_rfl hR'R)).trans hSW
  have hac := hSig.isAcausal E0LM.e0_causallyArcConnected (E0LM.e0_curvesExtend hGH)
  have hlow : ∀ x ∈ spear v R', x.1 ≤ v + R' / 2 → ψ (paperInY x) ∈ (CE M).Iminus ⊤ Sig := by
    intro x hx hτ
    have hτv : v + rad x / 2 ≤ x.1 := by have := hx.1; simp only [fcoord] at this; linarith
    have hdist : dist x (vertex v) < ε := by
      rw [Prod.dist_eq]
      refine max_lt ?_ ?_
      · rw [Real.dist_eq, vertex, abs_lt]
        constructor <;> nlinarith [rad_nonneg x, hx.2]
      · rw [vertex, dist_zero_right]
        exact (hx.2.trans hR'ε).trans_lt (by linarith)
    exact (hball hdist).2
  refine ⟨R', v, W, ψ, hR'pos, hR'R, hW, hsub, hψ, hinj, hp, hlow, ?_, ?_⟩
  · intro x hx hxS
    by_contra hτ
    push Not at hτ
    exact notMem_of_mem_Iminus hGH hSig (hlow x hx hτ) hxS
  · rintro ⟨τ₁, z⟩ hx ⟨τ₂, z'⟩ hy hzz hxS hyS
    simp only at hzz
    subst hzz
    have key : ∀ a b : ℝ, ((a, z) : E0) ∈ spear v R' → ((b, z) : E0) ∈ spear v R' → a ≤ b →
        ψ (paperInY (a, z)) ∈ Sig → ψ (paperInY (b, z)) ∈ Sig → a = b := by
      intro a b ha hb hab haS hbS
      have hle : (CE M).le ⊤ (ψ (paperInY (a, z))) (ψ (paperInY (b, z))) := by
        set O : Opens E0 := ⟨paperInY ⁻¹' W, hPo⟩
        refine le_of_isE0Mor_paper hW hψ (U := O) subset_rfl (le_vertical hab fun s hs => ?_)
        have hmem : ((a + s * (b - a), z) : E0) ∈ spear v R' :=
          ⟨by
            have h1 := ha.1
            simp only [fcoord, rad] at h1 ⊢
            nlinarith [hs.1, hs.2],
            hb.2⟩
        exact hsub ⟨_, hmem, rfl⟩
      have heq := hac _ haS _ hbS hle
      have h2 := hinj (hsub ⟨_, ha, rfl⟩) (hsub ⟨_, hb, rfl⟩) heq
      have h3 := paperInY.injOn (by simp) (by simp) h2
      exact (Prod.mk.injEq _ _ _ _ ▸ h3).1
    rcases le_total τ₁ τ₂ with h | h
    · rw [key τ₁ τ₂ hx hy h hxS hyS]
    · rw [key τ₂ τ₁ hy hx h hyS hxS]

/-- A cluster point of a map that eventually lies in a closed set lies in it. -/
theorem mem_of_mapClusterPt_of_eventually {ι X : Type*} [TopologicalSpace X] {l : Filter ι}
    {u : ι → X} {q : X} {A : Set X} (hA : IsClosed A) (hq : MapClusterPt q l u)
    (h : ∀ᶠ i in l, u i ∈ A) : q ∈ A := by
  have hq' : ClusterPt q (map u l) := hq
  have : ClusterPt q (𝓟 A) := hq'.mono (le_principal_iff.2 (Filter.mem_map.2 h))
  exact hA.closure_subset this.mem_closure

/-- In `𝔼₀`, a causal relation between two points of a spear is realised inside every open set
containing the spear (spears are causally convex, `𝔼₀` causally arc-connected). -/
theorem le_of_le_top_of_mem_spear {v R : ℝ} {U : Opens E0} (hU : spear v R ⊆ U) {x y : E0}
    (hx : x ∈ spear v R) (hy : y ∈ spear v R) (h : causality.le ⊤ x y) : causality.le U x y := by
  obtain ⟨c, hc, hc0, hc1⟩ := (E0.causallyArcConnected ⊤ le_rfl x y).1.1 h
  have hmem : ∀ s ∈ Icc (0 : ℝ) 1, c s ∈ U := fun s hs => by
    have h1 : causality.le ⊤ x (c s) := by rw [← hc0]; exact hc.le_of_le le_rfl hs.1 hs.2
    have h2 : causality.le ⊤ (c s) y := by rw [← hc1]; exact hc.le_of_le hs.1 hs.2 le_rfl
    exact hU (mem_spear_of_le hx hy h1 h2)
  exact (E0.causallyArcConnected U le_top x y).1.2
    ⟨c, Causal.CurveOn.restrict hc le_rfl le_rfl le_top hmem, hc0, hc1⟩

/-- **A future-monotone curve eventually in a compact set converges** in a globally hyperbolic
`𝔼₀`-manifold: its cluster points are all above the curve (`J⁺` closed) and below each other
(`J⁻` closed), hence equal by causality. -/
theorem exists_tendsto_of_monotone [HasGroupoid M e0Groupoid] [T2Space M] (hGH : (CE M).GloballyHyperbolic)
    {γ : ℝ → M} {t₀ : ℝ} (hmono : ∀ s t, t₀ ≤ s → s ≤ t → (CE M).le ⊤ (γ s) (γ t))
    {K : Set M} (hK : IsCompact K) (hKγ : ∀ t, t₀ ≤ t → γ t ∈ K) :
    ∃ q, Tendsto γ atTop (𝓝 q) := by
  have hT := E0LM.e0_tarentin (M := M)
  have hev : ∀ᶠ t in atTop, γ t ∈ K := eventually_atTop.2 ⟨t₀, hKγ⟩
  obtain ⟨q, -, hq⟩ := hK.exists_mapClusterPt (f := atTop) (u := γ) (le_principal_iff.2 hev)
  have habove : ∀ q', MapClusterPt q' atTop γ → ∀ s, t₀ ≤ s → (CE M).le ⊤ (γ s) q' := by
    intro q' hq' s hs
    have := mem_of_mapClusterPt_of_eventually (hGH.isClosed_Jplus_singleton hT (γ s)) hq'
      (eventually_atTop.2 ⟨s, fun t ht => by simpa using hmono s t hs ht⟩)
    simpa using this
  have huniq : ∀ q', MapClusterPt q' atTop γ → q' = q := by
    intro q' hq'
    have h1 : (CE M).le ⊤ q' q := by
      have := mem_of_mapClusterPt_of_eventually (hGH.isClosed_Jminus_singleton hT q) hq'
        (eventually_atTop.2 ⟨t₀, fun t ht => by simpa using habove q hq t ht⟩)
      simpa using this
    have h2 : (CE M).le ⊤ q q' := by
      have := mem_of_mapClusterPt_of_eventually (hGH.isClosed_Jminus_singleton hT q') hq
        (eventually_atTop.2 ⟨t₀, fun t ht => by simpa using habove q' hq' t ht⟩)
      simpa using this
    exact hGH.1 h1 h2
  exact ⟨q, hK.tendsto_nhds_of_unique_mapClusterPt hev fun x _ hx => huniq x hx⟩

attribute [local instance] btzE0Structure in
/-- **The BTZ ray of a spear chart has no future endpoint in `M`** (« full » rays are
inextensible). At a limit point `q` (a BTZ point, `sing₀` being closed), `f = κ ∘ ψ` (`κ` the
chart at `q`) is, on the connected component `U` of its domain around the tail, a local
`G`-structomorphism into `𝔼₀` near a singular point; WP-41c's core (`btzE0_localUnique_core`,
B21 `prop:isom_strong`) gives a **global** homeomorphism `Ψ` of `𝔼₀` with `f = Ψ` on a non-empty
open set, hence on `U` (rigidity `e0_eqOn_of_eqOn_open`, density of the regular part). Then
`f (ray) → κ q ∈ range Ψ`, so the ray itself converges in `𝔼₀` — but its `τ` tends to `+∞`. -/
theorem axis_noLimit [HasGroupoid M e0Groupoid] [T2Space M] {v : ℝ} {W : Set E0Y} {ψ : E0Y → M}
    (hW : IsOpen W) (hray : ∀ t, 0 ≤ t → yAxis v t ∈ W) (hψ : IsE0Mor ψ W) (hinj : InjOn ψ W)
    (q : M) : ¬ Tendsto (fun t => ψ (yAxis v t)) atTop (𝓝 q) := by
  intro hlim
  have hR : IsFullFutureBTZRay (ψ (yVertex v)) (fun t => ψ (yAxis v t)) :=
    ⟨v, W, ψ, hW, hray, hψ, hinj, rfl, fun _ => rfl⟩
  have hS0 : IsClosed (S0 M) :=
    E0LM.charted_isClosed_sing e0_sing_mem le_rfl (E0LM.isClosed_e0SingY 0)
  have hq : q ∈ S0 M := hS0.mem_of_tendsto hlim (eventually_atTop.2 ⟨0, fun t ht => hR.mem_S0 ht⟩)
  set κ := chartAt E0Y q with hκ
  have hκq : κ q ∈ e0SingY 0 := hq
  obtain ⟨x₀, hx₀, -⟩ := E0LM.mem_e0SingY_zero_iff.1 hκq
  have hψc : ContinuousOn ψ W := fun x hx => (hψ x hx).continuousWithinAt
  have hOq : IsOpen (κ.source ∩ κ ⁻¹' range Sum.inr) :=
    κ.isOpen_inter_preimage isOpen_range_inr
  set V : Set E0Y := W ∩ ψ ⁻¹' (κ.source ∩ κ ⁻¹' range Sum.inr) with hV
  have hVo : IsOpen V := hψc.isOpen_inter_preimage hW hOq
  obtain ⟨T, hT⟩ := eventually_atTop.1
    (hlim.eventually (hOq.mem_nhds ⟨mem_chart_source E0Y q, ⟨x₀, hx₀.symm⟩⟩))
  set T' := max T 0 with hT'
  have htail : ∀ t, T' ≤ t → yAxis v t ∈ V := fun t ht =>
    ⟨hray t ((le_max_right _ _).trans ht), hT t ((le_max_left _ _).trans ht)⟩
  set U := connectedComponentIn V (yAxis v T') with hU
  have hUo : IsOpen U := hVo.connectedComponentIn
  have hUV : U ⊆ V := connectedComponentIn_subset _ _
  have hUc : IsPreconnected U := isPreconnected_connectedComponentIn
  have htailU : ∀ t, T' ≤ t → yAxis v t ∈ U := by
    have hpre : IsPreconnected (yAxis v '' Ici T') :=
      isPreconnected_Ici.image _ (continuous_yAxis v).continuousOn
    have hsub := hpre.subset_connectedComponentIn (x := yAxis v T') ⟨T', self_mem_Ici, rfl⟩
      (by rintro _ ⟨t, ht, rfl⟩; exact htail t ht)
    exact fun t ht => hsub ⟨t, ht, rfl⟩
  -- `U` lies in the `𝔼₀` summand
  have hUinr : U ⊆ range Sum.inr := by
    rcases Sum.isPreconnected_iff.1 hUc with ⟨t, -, ht⟩ | ⟨t, -, ht⟩
    · exfalso
      have h0 := htailU T' le_rfl
      rw [ht] at h0
      obtain ⟨m, -, hm⟩ := h0
      simp [yAxis, paperInY_apply] at hm
    · rw [ht]; exact image_subset_range _ _
  -- `f = κ ∘ ψ` is an `𝔼₀`-morphism on `U`, with values in the `𝔼₀` summand
  set f : E0Y → E0Y := κ ∘ ψ with hf
  have hQ : ∀ y : E0Y, e0Groupoid.IsLocalStructomorphWithinAt id univ y := fun y _ =>
    ⟨OpenPartialHomeomorph.refl E0Y, e0Groupoid.id_mem, fun _ _ => rfl, trivial⟩
  have hψU : IsE0Mor ψ U :=
    Causal.CBG.liftPropOn_mono_of_le hW hUo hψ (fun y hy => (hUV hy).1)
  have hfU : IsE0Mor f U :=
    Causal.CBG.liftPropOn_comp hUo κ.open_source
      (e0Groupoid.isLocalStructomorphWithinAt_localInvariantProp.liftPropOn_chart hQ) hψU
      (fun y hy => (hUV hy).2.1)
  have hfinr : ∀ y ∈ U, f y ∈ range Sum.inr := fun y hy => (hUV hy).2.2
  set S : Set E0Y := U ∩ e0Reg with hSdef
  have hSo : IsOpen S := hUo.inter isOpen_e0Reg
  have hSc : IsPreconnected S := isPreconnected_inter_e0Reg hUo hUc
  have hfS : ∀ y ∈ S, e0Groupoid.IsLocalStructomorphWithinAt f S y := by
    intro y hy _
    have h := (hfU y hy.1).2
    simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_apply,
      preimage_id_eq] at h
    obtain ⟨e, he, hfe, hye⟩ := h hy.1
    exact ⟨e, he, fun z hz => hfe ⟨hz.1.1, hz.2⟩, hye⟩
  have hfinj : InjOn f S := fun y hy y' hy' h =>
    hinj (hUV hy.1).1 (hUV hy'.1).1 (κ.injOn (hUV hy.1).2.1 (hUV hy'.1).2.1 h)
  -- the core: a global homeomorphism `Ψ` of `𝔼₀`
  set U' : Set BTZE0 := Sum.inr ⁻¹' U
  set F : BTZE0 → BTZE0 := fun x => e0Inr.symm (f (Sum.inr x))
  have hfF : ∀ x ∈ U', f (Sum.inr x) = Sum.inr (F x) := fun x hx => by
    obtain ⟨z, hz⟩ := hfinr (Sum.inr x) hx
    simp only [F, ← hz, e0Inr_symm_inr]
  have hloc : ∀ x ∈ U' ∩ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0,
      ∃ e ∈ e0Groupoid, Sum.inr x ∈ e.source ∧ f =ᶠ[𝓝 (Sum.inr x)] e := by
    rintro x ⟨hx, hxr⟩
    have hxS : (Sum.inr x : E0Y) ∈ S := ⟨hx, inr_mem_e0Reg_iff.2 hxr⟩
    obtain ⟨e, he, hfe, hxe⟩ := hfS _ hxS hxS
    exact ⟨e, he, hxe, Filter.eventually_of_mem ((hSo.inter e.open_source).mem_nhds ⟨hxS, hxe⟩)
      fun z hz => hfe hz⟩
  have hFc : ∀ x ∈ U' ∩ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0, ContinuousAt F x := by
    intro x hx
    obtain ⟨e, -, hxe, hfe⟩ := hloc x hx
    have hfc : ContinuousAt f (Sum.inr x) := (e.continuousAt hxe).congr hfe.symm
    have h1 : ContinuousAt e0Inr.symm (f (Sum.inr x)) :=
      e0Inr.symm.continuousAt (by rw [e0Inr_symm_source, hfF x hx.1]; exact ⟨_, rfl⟩)
    exact ContinuousAt.comp (g := e0Inr.symm) (f := fun x : BTZE0 => f (Sum.inr x)) h1
      (ContinuousAt.comp (g := f) (f := Sum.inr) hfc continuous_inr.continuousAt)
  have hFreg : ∀ x ∈ U' ∩ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0,
      F x ∈ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0 := by
    rintro x ⟨hx, hxr⟩
    have hxS : (Sum.inr x : E0Y) ∈ S := ⟨hx, inr_mem_e0Reg_iff.2 hxr⟩
    obtain ⟨e, he, hfe, hxe⟩ := hfS _ hxS hxS
    have hfe' : ∀ z ∈ S ∩ e.source, f z = e z := fun z hz => hfe hz
    have := mapsTo_e0Reg_of_mem he hxe hxS.2
    rw [← hfe' _ ⟨hxS, hxe⟩, hfF x hx] at this
    exact inr_mem_e0Reg_iff.1 this
  have hFloc : ∀ x ∈ U' ∩ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0,
      ∃ c ∈ aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0, x ∈ c.source ∧
      ∃ c' ∈ aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0, F x ∈ c'.source ∧
      ∃ h : Causal.Flat.isom 2, ∀ᶠ z in 𝓝 x, c' (F z) = h • c z := by
    rintro x ⟨hx, hxr⟩
    have hxS : (Sum.inr x : E0Y) ∈ S := ⟨hx, inr_mem_e0Reg_iff.2 hxr⟩
    obtain ⟨e, he, hfe, hxe⟩ := hfS _ hxS hxS
    have hfe' : ∀ z ∈ S ∩ e.source, f z = e z := fun z hz => hfe hz
    obtain ⟨c, hc, hxc⟩ := mem_support.1 hxr
    obtain ⟨c', hc', hFxc⟩ := mem_support.1 (hFreg x ⟨hx, hxr⟩)
    have hex : e (Sum.inr x) = Sum.inr (F x) := by rw [← hfe' _ ⟨hxS, hxe⟩, hfF x hx]
    obtain ⟨-, hch⟩ := ((mem_e0Groupoid_iff.1 he).1 _ hxe).2 hxS.2
    obtain ⟨h, hh⟩ := hch _ (e0InrChart_mem_e0Atlas hc) _ (e0InrChart_mem_e0Atlas hc')
      (mem_e0InrChart_source.2 ⟨x, hxc, rfl⟩)
      (by rw [hex]; exact mem_e0InrChart_source.2 ⟨_, hFxc, rfl⟩)
    refine ⟨c, hc, hxc, c', hc', hFxc, h, ?_⟩
    have hS' : Sum.inr ⁻¹' S ∈ 𝓝 x := (hSo.preimage continuous_inr).mem_nhds hxS
    have he' : Sum.inr ⁻¹' e.source ∈ 𝓝 x := (e.open_source.preimage continuous_inr).mem_nhds hxe
    filter_upwards [continuous_inr.continuousAt.eventually hh, hS', he'] with z hz hzS hze
    rw [← hfe' _ ⟨hzS, hze⟩, hfF z hzS.1, e0InrChart_inr, e0InrChart_inr] at hz
    exact hz
  have hFinj : InjOn F (U' ∩ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) := by
    rintro x ⟨hx, hxr⟩ x' ⟨hx', hxr'⟩ hxx'
    have := hfinj ⟨hx, inr_mem_e0Reg_iff.2 hxr⟩ ⟨hx', inr_mem_e0Reg_iff.2 hxr'⟩
      (by rw [hfF x hx, hfF x' hx', show F x = F x' from hxx'])
    exact Sum.inr_injective this
  set a₀ : BTZE0 := E0.toPaper.symm ((v + T', 0) : E0)
  have ha₀ : (Sum.inr a₀ : E0Y) = yAxis v T' := by simp [a₀, yAxis, paperInY_apply]
  have ha₀U : a₀ ∈ U' := by show (Sum.inr a₀ : E0Y) ∈ U; rw [ha₀]; exact htailU T' le_rfl
  have ha₀reg : a₀ ∉ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0 := by
    rw [← inr_mem_e0Reg_iff, ha₀]
    have := yAxis_mem_e0SingY v T'
    exact this.2
  obtain ⟨Ψ, ψ', g, hlift, hpos, hD, W₀, hW₀o, hW₀ne, hW₀U, hW₀eq⟩ :=
    btzE0_localUnique_core ha₀reg (hUo.preimage continuous_inr) ha₀U hFc hFreg hFloc hFinj
  set e := e0Lift Ψ with he
  have heG : e ∈ e0Groupoid := e0Lift_mem Ψ ψ' g hlift hpos hD
  have hSe : S ⊆ e.source := fun y hy => by rw [e0Lift_source]; exact hUinr hy.1
  have heqW : EqOn f e (Sum.inr '' W₀) := by
    rintro _ ⟨w, hw, rfl⟩
    rw [hfF w (hW₀U hw).1, e0Lift_apply, hW₀eq hw]
  have heqS : EqOn f e S :=
    e0_eqOn_of_eqOn_open hSo hSc hfS heG hSe (isOpenMap_inr _ hW₀o) (hW₀ne.image _)
      (by rintro _ ⟨w, hw, rfl⟩; exact ⟨(hW₀U hw).1, inr_mem_e0Reg_iff.2 (hW₀U hw).2⟩) heqW
  -- on the whole tail
  have hfc : ContinuousOn f U := fun y hy => (hfU y hy).continuousWithinAt
  have heq_tail : ∀ t, T' ≤ t → f (yAxis v t) = e (yAxis v t) := by
    intro t ht
    have hy := htailU t ht
    refine e0_eq_of_mem_closure ((hfc _ hy).continuousAt (hUo.mem_nhds hy))
      (e.continuousAt (by rw [e0Lift_source]; exact hUinr hy))
      (dense_e0Reg.open_subset_closure_inter hUo hy) heqS
  -- the ray converges in `𝔼₀`
  have hκc : ContinuousAt κ q := κ.continuousAt (mem_chart_source E0Y q)
  have hflim : Tendsto (fun t => e (yAxis v t)) atTop (𝓝 (κ q)) :=
    (hκc.tendsto.comp hlim).congr' (eventually_atTop.2 ⟨T', fun t ht => heq_tail t ht⟩)
  have hκqt : κ q ∈ e.target := by rw [e0Lift_target]; exact ⟨x₀, hx₀.symm⟩
  have hylim : Tendsto (fun t => yAxis v t) atTop (𝓝 (e.symm (κ q))) := by
    refine ((e.continuousAt_symm hκqt).tendsto.comp hflim).congr' ?_
    refine eventually_atTop.2 ⟨T', fun t ht => ?_⟩
    exact e.left_inv (by rw [e0Lift_source]; exact hUinr (htailU t ht))
  have hys : e.symm (κ q) ∈ paperOfY.source := by
    rw [paperOfY_source, ← e0Lift_source Ψ]; exact e.map_target hκqt
  have hplim := ((paperOfY.continuousAt hys).tendsto.comp hylim)
  have hcoord : ∀ t, paperOfY (yAxis v t) = ((v + t, 0) : E0) := fun t => by
    simp [yAxis, paperInY_apply]
  have h1 : Tendsto (fun t : ℝ => (((v + t, 0) : E0)).1) atTop
      (𝓝 (paperOfY (e.symm (κ q))).1) := by
    have := (continuous_fst.tendsto _).comp hplim
    refine this.congr' (Filter.Eventually.of_forall fun t => ?_)
    simp only [comp_apply, hcoord]
  have h2 : Tendsto (fun t : ℝ => (((v + t, 0) : E0)).1) atTop atTop :=
    tendsto_atTop_add_const_left _ v tendsto_id
  exact not_tendsto_nhds_of_tendsto_atTop h2 _ h1

/-- **A full future BTZ ray has no future endpoint in `M`** (it is future inextensible: « full »). -/
theorem IsFullFutureBTZRay.not_tendsto [HasGroupoid M e0Groupoid] [T2Space M] {p : M}
    {γ : ℝ → M} (h : IsFullFutureBTZRay p γ) (q : M) : ¬ Tendsto γ atTop (𝓝 q) := by
  obtain ⟨v, W, ψ, hW, hray, hψ, hinj, -, hγ⟩ := h
  have : γ = fun t => ψ (yAxis v t) := funext hγ
  rw [this]
  exact axis_noLimit hW hray hψ hinj q

/-- **The image of a vertical null ray of a spear chart has no future endpoint in `M`.** Were
`ψ(t, z) → q`, the BTZ ray below (`(t, 0) ≤ (t + |z|/2, z)`, `J⁺((t,0)) = {f ≥ t}`) would be a
future-monotone curve in the compact diamond `J(ψ(v,0), q)`, hence convergent
(`exists_tendsto_of_monotone`), against `axis_noLimit`. -/
theorem spear_vertical_noLimit [HasGroupoid M e0Groupoid] [T2Space M] [SecondCountableTopology M]
    (hGH : (CE M).GloballyHyperbolic)
    {R' v : ℝ} {W : Set E0Y} {ψ : E0Y → M} (hW : IsOpen W) (hsub : spearY v R' ⊆ W)
    (hψ : IsE0Mor ψ W) (hinj : InjOn ψ W) {z : ℂ} (hz : ‖z‖ ≤ R') (q : M) :
    ¬ Tendsto (fun t : ℝ => ψ (paperInY (t, z))) atTop (𝓝 q) := by
  intro hlim
  have hR' : 0 ≤ R' := (norm_nonneg z).trans hz
  have hT := E0LM.e0_tarentin (M := M)
  have hPo : IsOpen (paperInY ⁻¹' W) := hW.preimage continuous_paperInY
  set O : Opens E0 := ⟨paperInY ⁻¹' W, hPo⟩
  have hSO : spear v R' ⊆ O := fun x hx => hsub ⟨x, hx, rfl⟩
  set c : ℝ := v + ‖z‖ / 2 with hc
  have hmemz : ∀ t, c ≤ t → ((t, z) : E0) ∈ spear v R' := fun t ht => by
    refine ⟨?_, hz⟩; simp only [fcoord, rad]; linarith [hc]
  have hvert : ∀ s t, c ≤ s → s ≤ t →
      (CE M).le ⊤ (ψ (paperInY (s, z))) (ψ (paperInY (t, z))) := fun s t hs hst =>
    le_of_isE0Mor_paper hW hψ (U := O) subset_rfl
      (le_of_le_top_of_mem_spear hSO (hmemz s hs) (hmemz t (hs.trans hst)) (le_vertical_top hst))
  -- the vertical line lies below `q`
  have hbelow : ∀ t, c ≤ t → (CE M).le ⊤ (ψ (paperInY (t, z))) q := fun t ht => by
    have := (hGH.isClosed_Jplus_singleton hT (ψ (paperInY (t, z)))).mem_of_tendsto hlim
      (eventually_atTop.2 ⟨t, fun s hs => by simpa using hvert t s ht hs⟩)
    simpa using this
  -- the BTZ ray lies below the vertical line, hence below `q`
  have haxis : ∀ s, 0 ≤ s → (CE M).le ⊤ (ψ (yAxis v s)) (ψ (paperInY (v + s + ‖z‖ / 2, z))) := by
    intro s hs
    have h1 : ((v + s, 0) : E0) ∈ spear v R' := axis_mem_spear hR' (by linarith)
    have h2 := hmemz (v + s + ‖z‖ / 2) (show v + ‖z‖ / 2 ≤ v + s + ‖z‖ / 2 by linarith)
    refine le_of_isE0Mor_paper hW hψ (U := O) subset_rfl (le_of_le_top_of_mem_spear hSO h1 h2 ?_)
    rw [le_top_iff, le_axis_iff rfl]
    simp only [fcoord, rad]; linarith
  have hmonoA : ∀ s t, 0 ≤ s → s ≤ t → (CE M).le ⊤ (ψ (yAxis v s)) (ψ (yAxis v t)) := by
    have hray : IsFullFutureBTZRay (ψ (yVertex v)) (fun t => ψ (yAxis v t)) :=
      ⟨v, W, ψ, hW, fun t ht => hsub (yAxis_mem_spearY hR' ht), hψ, hinj, rfl, fun _ => rfl⟩
    exact fun s t hs hst => hray.le hs hst
  obtain ⟨q', hq'⟩ := exists_tendsto_of_monotone hGH hmonoA (hGH.2 (ψ (yAxis v 0)) q)
    fun t ht => Causal.Causality.mem_diamond.2 ⟨hmonoA 0 t le_rfl ht,
      (CE M).le_trans (haxis t ht) (hbelow _ (show v + ‖z‖ / 2 ≤ v + t + ‖z‖ / 2 by linarith))⟩
  exact axis_noLimit hW (fun t ht => hsub (yAxis_mem_spearY hR' ht)) hψ hinj q' hq'

/-- **Every vertical null line of the shrunk spear meets `Σ`** (the existence half of « `Φ(Σ ∩ 𝒮′)`
is exactly the graph of `τ_Σ` », `BTZ_1.tex:756–757`): the vertical line starts in `I⁻(Σ)` (at the
bottom of the shaft); were it in `J⁻(Σ)` forever, it would be a monotone curve in the compact
`J⁻(Σ) ∩ J⁺(γ t₀)`, hence convergent (cluster points are unique: `≤` is closed and `M` causal),
against `spear_vertical_noLimit`; so it reaches `J⁺(Σ)`, and by connectedness it meets
`J⁺(Σ) ∩ J⁻(Σ) = Σ`. -/
theorem spear_vertical_meets [HasGroupoid M e0Groupoid] [T2Space M] [SecondCountableTopology M]
    (hLM : E0LM.E0GlobalBTZ (CE M) (S0 M))
    (hGH : (CE M).GloballyHyperbolic) {Sig : Set M} (hSig : (CE M).IsCauchySurface Sig)
    {R' v : ℝ} {W : Set E0Y} {ψ : E0Y → M} (hW : IsOpen W)
    (hsub : spearY v R' ⊆ W) (hψ : IsE0Mor ψ W) (hinj : InjOn ψ W)
    (hshaft : ∀ x ∈ spear v R', x.1 ≤ v + R' / 2 → ψ (paperInY x) ∈ (CE M).Iminus ⊤ Sig)
    {z : ℂ} (hz : ‖z‖ ≤ R') :
    ∃ τ : ℝ, ((τ, z) : E0) ∈ spear v R' ∧ ψ (paperInY (τ, z)) ∈ Sig := by
  have hA := E0LM.e0_singularFlatAxioms_of E0.chartIso_mem_e0Groupoid hLM
  have hext := E0LM.e0_curvesExtend hGH
  have hac := hSig.isAcausal E0LM.e0_causallyArcConnected hext
  obtain ⟨T, hTc, hT⟩ := E0LM.e0_timeFunction hGH
  set t₀ : ℝ := v + R' / 2 with ht₀
  set γ : ℝ → M := fun t => ψ (paperInY (t, z)) with hγ
  have hmem : ∀ t, t₀ ≤ t → ((t, z) : E0) ∈ spear v R' := fun t ht => by
    refine ⟨?_, hz⟩
    simp only [fcoord, rad]; linarith
  have hPo : IsOpen (paperInY ⁻¹' W) := hW.preimage continuous_paperInY
  have hmono : ∀ s t, t₀ ≤ s → s ≤ t → (CE M).le ⊤ (γ s) (γ t) := by
    intro s t hs hst
    set O : Opens E0 := ⟨paperInY ⁻¹' W, hPo⟩
    refine le_of_isE0Mor_paper hW hψ (U := O) subset_rfl (le_vertical hst fun r hr => ?_)
    exact hsub ⟨_, hmem _ (by nlinarith [hr.1, hr.2]), rfl⟩
  have hψc : ContinuousOn ψ W := fun x hx => (hψ x hx).continuousWithinAt
  have hγc : ContinuousOn γ (Ici t₀) := by
    refine hψc.comp (continuous_paperInY.comp (continuous_id.prodMk continuous_const)).continuousOn
      fun t ht => hsub ⟨_, hmem t ht, rfl⟩
  have hJp := E0LM.sfa_isClosed_Jplus_cauchy hA hGH hext hSig
  have hJm := E0LM.sfa_isClosed_Jminus_cauchy hA hGH hext hSig
  have hle_closed := hGH.isClosed_le hA.tarentin
  -- the vertical line reaches `J⁺(Σ)`
  obtain ⟨t₁, ht₁, ht₁S⟩ : ∃ t₁, t₀ ≤ t₁ ∧ γ t₁ ∈ (CE M).Jplus ⊤ Sig := by
    by_contra hcon
    push Not at hcon
    have hin : ∀ t, t₀ ≤ t → γ t ∈ (CE M).Jminus ⊤ Sig ∩ (CE M).Jplus ⊤ {γ t₀} := fun t ht =>
      ⟨((Causal.Causality.mem_Jplus_union_Jminus_of_isCauchySurface hext hSig (γ t)).resolve_left
        (hcon t ht)), by simpa using hmono t₀ t le_rfl ht⟩
    have hK := E0LM.sfa_isCompact_Jminus_inter_Jplus hA hGH hTc hT hSig (γ t₀)
    have hev : ∀ᶠ t in atTop, γ t ∈ (CE M).Jminus ⊤ Sig ∩ (CE M).Jplus ⊤ {γ t₀} :=
      eventually_atTop.2 ⟨t₀, hin⟩
    obtain ⟨q, -, hq⟩ := hK.exists_mapClusterPt (f := atTop) (u := γ) (le_principal_iff.2 hev)
    -- every cluster point is above the whole line
    have habove : ∀ q', MapClusterPt q' atTop γ → ∀ s, t₀ ≤ s → (CE M).le ⊤ (γ s) q' := by
      intro q' hq' s hs
      have := mem_of_mapClusterPt_of_eventually
        (hGH.isClosed_Jplus_singleton hA.tarentin (γ s)) hq'
        (eventually_atTop.2 ⟨s, fun t ht => by simpa using hmono s t hs ht⟩)
      simpa using this
    have huniq : ∀ q', MapClusterPt q' atTop γ → q' = q := by
      intro q' hq'
      have h1 : (CE M).le ⊤ q' q := by
        have := mem_of_mapClusterPt_of_eventually
          (hGH.isClosed_Jminus_singleton hA.tarentin q) hq'
          (eventually_atTop.2 ⟨t₀, fun t ht => by simpa using habove q hq t ht⟩)
        simpa using this
      have h2 : (CE M).le ⊤ q q' := by
        have := mem_of_mapClusterPt_of_eventually
          (hGH.isClosed_Jminus_singleton hA.tarentin q') hq
          (eventually_atTop.2 ⟨t₀, fun t ht => by simpa using habove q' hq' t ht⟩)
        simpa using this
      exact hGH.1 h1 h2
    have htend : Tendsto γ atTop (𝓝 q) :=
      hK.tendsto_nhds_of_unique_mapClusterPt hev fun x _ hx => huniq x hx
    exact spear_vertical_noLimit hGH hW hsub hψ hinj hz q htend
  -- the start of the vertical line is in `J⁻(Σ)`
  have ht₀S : γ t₀ ∈ (CE M).Jminus ⊤ Sig := by
    obtain ⟨σ, hσ, hlt⟩ := hshaft _ (hmem t₀ le_rfl) le_rfl
    exact ⟨σ, hσ, (CE M).le_of_lt hlt⟩
  -- connectedness of the segment
  have hpre : IsPreconnected (γ '' Icc t₀ t₁) :=
    isPreconnected_Icc.image γ (hγc.mono fun t ht => ht.1)
  obtain ⟨_, ⟨t, ht, rfl⟩, hγt⟩ := isPreconnected_closed_iff.1 hpre _ _ hJp hJm
    (fun _ ⟨t, _, ht⟩ => ht ▸ Causal.Causality.mem_Jplus_union_Jminus_of_isCauchySurface hext hSig _)
    ⟨γ t₁, ⟨t₁, ⟨ht₁, le_rfl⟩, rfl⟩, ht₁S⟩ ⟨γ t₀, ⟨t₀, ⟨le_rfl, ht₁⟩, rfl⟩, ht₀S⟩
  refine ⟨t, hmem t ht.1, ?_⟩
  rw [← Causal.Causality.Jplus_inter_Jminus_eq hGH.1 hac]
  exact hγt

/-- **The graph function `τ_Σ` is continuous on the closed disc** (B21 Lemma 2.4's « smooth », its
`C⁰` part; B21 Prop 2.17, PDF l.1983, uses the conclusion as « a circle in the shaft »). If `Σ`
meets the shrunk spear exactly along the graph of `τ_Σ` over `D_{R′}`, in the shaft, then `τ_Σ` is
continuous: for `a < τ_Σ(z)` the point `ψ(a, z)` is not in the closed `J⁺(Σ)` (else it would be in
`Σ`, below the graph point), so neither is `ψ(a, z′)` for `z′` near `z`, whence `a < τ_Σ(z′)`;
symmetrically with `J⁻(Σ)` above the graph. -/
theorem continuousOn_tauS [HasGroupoid M e0Groupoid] [T2Space M] [SecondCountableTopology M]
    (hLM : E0LM.E0GlobalBTZ (CE M) (S0 M)) (hGH : (CE M).GloballyHyperbolic) {Sig : Set M}
    (hSig : (CE M).IsCauchySurface Sig) {R' v : ℝ} {W : Set E0Y} {ψ : E0Y → M} (hW : IsOpen W)
    (hsub : spearY v R' ⊆ W) (hψ : IsE0Mor ψ W) {τS : ℂ → ℝ}
    (hpos : ∀ z : ℂ, ‖z‖ ≤ R' → v + R' / 2 < τS z)
    (hgraph : ∀ x ∈ spear v R', (ψ (paperInY x) ∈ Sig ↔ x.1 = τS x.2)) :
    ContinuousOn τS (Metric.closedBall 0 R') := by
  have hA := E0LM.e0_singularFlatAxioms_of E0.chartIso_mem_e0Groupoid hLM
  have hext := E0LM.e0_curvesExtend hGH
  have hac := hSig.isAcausal E0LM.e0_causallyArcConnected hext
  have hJp := E0LM.sfa_isClosed_Jplus_cauchy hA hGH hext hSig
  have hJm := E0LM.sfa_isClosed_Jminus_cauchy hA hGH hext hSig
  have hPo : IsOpen (paperInY ⁻¹' W) := hW.preimage continuous_paperInY
  have hψc : ContinuousOn ψ W := fun x hx => (hψ x hx).continuousWithinAt
  set t₀ : ℝ := v + R' / 2 with ht₀
  have hmem : ∀ (t : ℝ) (z : ℂ), ‖z‖ ≤ R' → t₀ ≤ t → ((t, z) : E0) ∈ spear v R' :=
    fun t z hz ht => ⟨by simp only [fcoord, rad]; linarith, hz⟩
  have hmono : ∀ z : ℂ, ‖z‖ ≤ R' → ∀ s t, t₀ ≤ s → s ≤ t →
      (CE M).le ⊤ (ψ (paperInY ((s, z) : E0))) (ψ (paperInY ((t, z) : E0))) := by
    intro z hz s t hs hst
    set O : Opens E0 := ⟨paperInY ⁻¹' W, hPo⟩
    refine le_of_isE0Mor_paper hW hψ (U := O) subset_rfl (le_vertical hst fun r hr => ?_)
    exact hsub ⟨_, hmem _ z hz (by nlinarith [hr.1, hr.2]), rfl⟩
  have hcont : ∀ t, t₀ ≤ t →
      ContinuousOn (fun z : ℂ => ψ (paperInY ((t, z) : E0))) (Metric.closedBall 0 R') :=
    fun t ht => hψc.comp (continuous_paperInY.comp (continuous_const.prodMk continuous_id)).continuousOn
      fun z hz => hsub ⟨_, hmem t z (mem_closedBall_zero_iff.1 hz) ht, rfl⟩
  have hS : ∀ z : ℂ, ‖z‖ ≤ R' → ψ (paperInY ((τS z, z) : E0)) ∈ Sig := fun z hz =>
    (hgraph _ (hmem _ z hz (hpos z hz).le)).2 rfl
  have hJJ : (CE M).Jplus ⊤ Sig ∩ (CE M).Jminus ⊤ Sig = Sig :=
    Causal.Causality.Jplus_inter_Jminus_eq hGH.1 hac
  intro z hz
  have hz' := mem_closedBall_zero_iff.1 hz
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · by_cases hat : a < t₀
    · exact eventually_nhdsWithin_of_forall fun z' hz'' =>
        hat.trans (hpos z' (mem_closedBall_zero_iff.1 hz''))
    push Not at hat
    have hnot : ψ (paperInY ((a, z) : E0)) ∉ (CE M).Jplus ⊤ Sig := by
      intro h
      have hJ : ψ (paperInY ((a, z) : E0)) ∈ (CE M).Jminus ⊤ Sig :=
        ⟨_, hS z hz', hmono z hz' a (τS z) hat ha.le⟩
      have hin : ψ (paperInY ((a, z) : E0)) ∈ Sig := by rw [← hJJ]; exact ⟨h, hJ⟩
      have h1 : a = τS z := (hgraph _ (hmem a z hz' hat)).1 hin
      linarith
    filter_upwards [hcont a hat z hz (hJp.isOpen_compl.mem_nhds hnot), self_mem_nhdsWithin]
      with z' h1 h2
    have h2' := mem_closedBall_zero_iff.1 h2
    by_contra hle
    push Not at hle
    exact h1 ⟨_, hS z' h2', hmono z' h2' (τS z') a (hpos z' h2').le hle⟩
  · have hbt : t₀ ≤ b := ((hpos z hz').trans hb).le
    have hnot : ψ (paperInY ((b, z) : E0)) ∉ (CE M).Jminus ⊤ Sig := by
      intro h
      have hJ : ψ (paperInY ((b, z) : E0)) ∈ (CE M).Jplus ⊤ Sig :=
        ⟨_, hS z hz', hmono z hz' (τS z) b (hpos z hz').le hb.le⟩
      have hin : ψ (paperInY ((b, z) : E0)) ∈ Sig := by rw [← hJJ]; exact ⟨hJ, h⟩
      have h1 : b = τS z := (hgraph _ (hmem b z hz' hbt)).1 hin
      linarith
    filter_upwards [hcont b hbt z hz (hJm.isOpen_compl.mem_nhds hnot), self_mem_nhdsWithin]
      with z' h1 h2
    have h2' := mem_closedBall_zero_iff.1 h2
    by_contra hle
    push Not at hle
    exact h1 ⟨_, hS z' h2', hmono z' h2' b (τS z') hbt hle⟩

/-- **B21 Lemma 2.4** (`lem:add_BTZ_param`, `BTZ_1.tex:685–695`), for a spear of vertex `p` (the
paper's hypothesis « `Δ` admits a spear neighbourhood » with the vertex moved to `p`, see
`IsSpearNbhd.of_ray`, `lem_add_BTZ_param_line` for the paper's form, and
`lem_add_BTZ_param_of_cauchyMaximal`): after shrinking the radius, `Σ` meets the spear exactly
along the graph of a **continuous** function `τ_Σ` over the closed disc `D_{R′}`
(`continuousOn_tauS`), and that graph lies in the shaft `τ > v + R′/2` (the paper's « positive »
after its normalisation `Φ(p) = (−R/2, 0, 0)`). Smoothness of `τ_Σ` is not claimed: `Σ` is a
topological Cauchy surface here (the paper's transversality argument uses `Σ` spacelike smooth);
the `C⁰` form is the ruled reading (DEC-125 (c)). -/
theorem lem_add_BTZ_param [HasGroupoid M e0Groupoid] [T2Space M] [SecondCountableTopology M]
    (hLM : E0LM.E0GlobalBTZ (CE M) (S0 M)) (hGH : (CE M).GloballyHyperbolic) {Sig : Set M}
    (hSig : (CE M).IsCauchySurface Sig) {p : M} {R : ℝ} {U : Set M} (hU : IsSpearNbhd p R U)
    (hpS : p ∈ (CE M).Iminus ⊤ Sig) :
    ∃ (R' v : ℝ) (W : Set E0Y) (ψ : E0Y → M), 0 < R' ∧ R' ≤ R ∧ IsOpen W ∧ spearY v R' ⊆ W ∧
      IsE0Mor ψ W ∧ InjOn ψ W ∧ ψ (yVertex v) = p ∧
      ∃ τS : ℂ → ℝ, ContinuousOn τS (Metric.closedBall 0 R') ∧
        (∀ z : ℂ, ‖z‖ ≤ R' → v + R' / 2 < τS z) ∧
        ∀ x ∈ spear v R', (ψ (paperInY x) ∈ Sig ↔ x.1 = τS x.2) := by
  obtain ⟨R', v, W, ψ, hR', hR'R, hW, hsub, hψ, hinj, hp, hlow, hshaft, huniq⟩ :=
    spear_shaft_vertical hGH hSig hU hpS
  have hmeet : ∀ z : ℂ, ‖z‖ ≤ R' →
      ∃ τ : ℝ, ((τ, z) : E0) ∈ spear v R' ∧ ψ (paperInY (τ, z)) ∈ Sig := fun z hz =>
    spear_vertical_meets hLM hGH hSig hW hsub hψ hinj hlow hz
  classical
  let τS : ℂ → ℝ := fun z => if h : ‖z‖ ≤ R' then (hmeet z h).choose else v + R'
  have hτS : ∀ z (hz : ‖z‖ ≤ R'), ((τS z, z) : E0) ∈ spear v R' ∧
      ψ (paperInY (τS z, z)) ∈ Sig := fun z hz => by
    simp only [τS, dif_pos hz]; exact (hmeet z hz).choose_spec
  have hpos : ∀ z : ℂ, ‖z‖ ≤ R' → v + R' / 2 < τS z := fun z hz =>
    hshaft _ (hτS z hz).1 (hτS z hz).2
  have hgraph : ∀ x ∈ spear v R', (ψ (paperInY x) ∈ Sig ↔ x.1 = τS x.2) := by
    intro x hx
    have hz : ‖x.2‖ ≤ R' := hx.2
    constructor
    · intro hxS
      have := huniq x hx _ (hτS x.2 hz).1 rfl hxS (hτS x.2 hz).2
      rw [this]
    · intro hx1
      have : x = (τS x.2, x.2) := Prod.ext hx1 rfl
      rw [this]; exact (hτS x.2 hz).2
  exact ⟨R', v, W, ψ, hR', hR'R, hW, hsub, hψ, hinj, hp, τS,
    continuousOn_tauS hLM hGH hSig hW hsub hψ hpos hgraph, hpos, hgraph⟩

/-- **The future half of a BTZ line is covered by any full future ray from its point** (the
first case of B21 Lemma 2.4's proof, « if `q` is in the past of `p`, then `p ∈ 𝒮` »): if `γ` is
the BTZ line through `q` (a closed embedding, future causal, onto the component of `sing₀`
through `q`, as `E0LM.E0GlobalBTZ.line` gives), every `γ s`, `s ≥ 0`, lies on a full future BTZ
ray `r` from `q`. Proof: `r` lies in the component, so `r = γ ∘ h` with `h` continuous (`γ` an
embedding); `h ≥ 0` (else `r t ≤ q ≤ r t`, so `t = 0`); `h` is unbounded (else `r` is a monotone
curve in the compact `γ([0, B])`, hence convergent, against `IsFullFutureBTZRay.not_tendsto`); the
intermediate value theorem concludes. -/
theorem IsFullFutureBTZRay.exists_eq_of_line [HasGroupoid M e0Groupoid] [T2Space M]
    (hGH : (CE M).GloballyHyperbolic) {q : M} {r : ℝ → M} (hr : IsFullFutureBTZRay q r)
    {γ : ℝ → M} (hγ0 : γ 0 = q) (hγe : IsClosedEmbedding γ)
    (hγc : (CE M).CausalCurveIn ⊤ univ γ) (hγr : range γ = connectedComponentIn (S0 M) q)
    {s : ℝ} (hs : 0 ≤ s) : ∃ t, 0 ≤ t ∧ r t = γ s := by
  have hrr : ∀ t, 0 ≤ t → r t ∈ range γ := by
    intro t ht
    rw [hγr]
    have hpre : IsPreconnected (r '' Ici 0) := isPreconnected_Ici.image r hr.continuousOn
    have hsub := hpre.subset_connectedComponentIn (x := q) ⟨0, self_mem_Ici, hr.zero⟩
      (by rintro _ ⟨u, hu, rfl⟩; exact hr.mem_S0 hu)
    exact hsub ⟨t, ht, rfl⟩
  classical
  let h : ℝ → ℝ := fun t => if ht : 0 ≤ t then (hrr t ht).choose else 0
  have hh : ∀ t, 0 ≤ t → γ (h t) = r t := fun t ht => by
    simp only [h, dif_pos ht]; exact (hrr t ht).choose_spec
  have hhc : ContinuousOn h (Ici 0) := by
    rw [hγe.isInducing.continuousOn_iff]
    exact hr.continuousOn.congr fun t ht => hh t ht
  have hh0 : h 0 = 0 := hγe.injective (by rw [hh 0 le_rfl, hr.zero, hγ0])
  have hhnn : ∀ t, 0 ≤ t → 0 ≤ h t := by
    intro t ht
    by_contra hneg
    push Not at hneg
    have h1 : (CE M).le ⊤ (r t) q := by
      rw [← hh t ht, ← hγ0]; exact hγc.le_of_le trivial trivial hneg.le
    have h2 : (CE M).le ⊤ q (r t) := by rw [← hr.zero]; exact hr.le le_rfl ht
    have h3 : r t = r 0 := (hGH.1 h1 h2).trans hr.zero.symm
    have h4 : t = 0 := hr.injOn ht (show (0 : ℝ) ∈ Ici 0 from mem_Ici.2 le_rfl) h3
    subst h4
    rw [hh0] at hneg
    exact lt_irrefl _ hneg
  obtain ⟨t₁, ht₁, hst₁⟩ : ∃ t, 0 ≤ t ∧ s ≤ h t := by
    by_contra hcon
    push Not at hcon
    have hK : IsCompact (γ '' Icc 0 s) := isCompact_Icc.image hγe.continuous
    obtain ⟨q', hq'⟩ := exists_tendsto_of_monotone hGH (t₀ := 0) (fun a b ha hab => hr.le ha hab)
      hK fun t ht => ⟨h t, ⟨hhnn t ht, (hcon t ht).le⟩, hh t ht⟩
    exact hr.not_tendsto q' hq'
  obtain ⟨t, ht, hts⟩ := intermediate_value_Icc ht₁ (hhc.mono Icc_subset_Ici_self)
    ⟨by rw [hh0]; exact hs, hst₁⟩
  exact ⟨t, ht.1, by rw [← hh t ht.1, hts]⟩

/-! #### The boundary of a spear neighbourhood in `M` (B21 Def 2.1, l.617; WP-46b fixer)

Def 2.1 asserts that the boundary of `𝒰 = ψ(𝒮)` **in `M`** is its head and its shaft. In the model
this is `frontier_spear`; in `M` it needs `𝒰` **closed**, which is not local: a sequence of the
spear either stays in a compact part `{τ ≤ T}` (whose image is compact, hence closed, `M` being
Hausdorff) or climbs, and then every axis point `γ(s)` lies below its limit (`J⁺(γ s)` is closed);
the ray `γ` would be a monotone curve in the compact diamond `J(γ 0, m)`, hence convergent
(`exists_tendsto_of_monotone`), against `axis_noLimit`. So **global hyperbolicity** is used;
it is the hypothesis of Lemmas 2.3/2.4, the only places B21 uses spear neighbourhoods. The
interior is the image of the model interior (`ψ` an injective open map on `W`).

WP-46b fixer round 2 (audit option (a)): the boundary sentence is read **as part of Def 2.1**,
the field `IsSpearNbhd.isClosed`; `frontier_spearImage_eq_iff_isClosed` proves the field
equivalent to the sentence for every spear chart in every `𝔼₀`-manifold, so
`IsSpearNbhd.frontier_eq` holds with no global hypothesis, and `isClosed_spearImage` makes the
field automatic in GH `M` (`IsSpearNbhd.of_chart`, `isSpearNbhd_iff_chart`). -/

/-- The part `{τ ≤ T}` of a spear of `𝔼₀` is compact. -/
theorem isCompact_spear_inter_le (v R T : ℝ) : IsCompact (spear v R ∩ {x : E0 | x.1 ≤ T}) := by
  refine ((isCompact_Icc (a := v) (b := T)).prod
    (isCompact_closedBall (0 : ℂ) R)).of_isClosed_subset ((isClosed_spear v R).inter (isClosed_le continuous_fst continuous_const)) ?_
  rintro x ⟨⟨h1, h2⟩, h3⟩
  simp only [fcoord] at h1
  refine ⟨⟨by linarith [rad_nonneg x], h3⟩, ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]; exact h2

/-- **The image of a spear under an injective `𝔼₀`-morphism is closed in a globally hyperbolic
`M`** (B21 Def 2.1: the boundary of `𝒰` is contained in `𝒰`). -/
theorem isClosed_spearImage [HasGroupoid M e0Groupoid] [T2Space M]
    (hGH : (CE M).GloballyHyperbolic) {v R : ℝ} (hR : 0 ≤ R) {W : Set E0Y} {ψ : E0Y → M}
    (hW : IsOpen W) (hsub : spearY v R ⊆ W) (hψ : IsE0Mor ψ W) (hinj : InjOn ψ W) :
    IsClosed (ψ '' spearY v R) := by
  have hT := E0LM.e0_tarentin (M := M)
  have hψc : ContinuousOn ψ W := fun x hx => (hψ x hx).continuousWithinAt
  have hPo : IsOpen (paperInY ⁻¹' W) := hW.preimage continuous_paperInY
  set O : Opens E0 := ⟨paperInY ⁻¹' W, hPo⟩
  have hSO : spear v R ⊆ O := fun x hx => hsub ⟨x, hx, rfl⟩
  set A : ℝ → Set M := fun T => ψ '' (paperInY '' (spear v R ∩ {x | x.1 ≤ T})) with hAdef
  set B : ℝ → Set M := fun T => ψ '' (paperInY '' (spear v R ∩ {x | T ≤ x.1})) with hBdef
  have hA : ∀ T, IsClosed (A T) := fun T =>
    (((isCompact_spear_inter_le v R T).image continuous_paperInY).image_of_continuousOn
      (hψc.mono (by rintro _ ⟨x, hx, rfl⟩; exact hsub ⟨x, hx.1, rfl⟩))).isClosed
  have hAS : ∀ T, A T ⊆ ψ '' spearY v R := fun T => image_mono (image_mono inter_subset_left)
  have hAB : ∀ T, ψ '' spearY v R = A T ∪ B T := by
    intro T
    simp only [hAdef, hBdef, spearY, ← image_union, ← inter_union_distrib_left]
    congr 2
    ext x
    simp only [mem_inter_iff, mem_union, mem_setOf_eq, iff_self_and]
    intro _; exact le_total _ _
  -- the high part of the spear lies above the axis point `γ s`
  have hB : ∀ s, 0 ≤ s → B (v + s + R / 2) ⊆ (CE M).Jplus ⊤ {ψ (yAxis v s)} := by
    rintro s hs _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨_, rfl, ?_⟩
    refine le_of_isE0Mor_paper hW hψ (U := O) subset_rfl
      (le_of_le_top_of_mem_spear hSO (axis_mem_spear hR (by linarith)) hx.1 ?_)
    rw [le_top_iff, le_axis_iff rfl]
    have h1 := hx.1.2
    have h2 : v + s + R / 2 ≤ x.1 := hx.2
    simp only [fcoord]; linarith
  refine isClosed_of_closure_subset fun m hm => ?_
  by_contra hmS
  have hmB : ∀ s, 0 ≤ s → (CE M).le ⊤ (ψ (yAxis v s)) m := by
    intro s hs
    rw [hAB (v + s + R / 2), closure_union, (hA _).closure_eq] at hm
    rcases hm with hm | hm
    · exact absurd (hAS _ hm) hmS
    · have := closure_minimal (hB s hs) (hGH.isClosed_Jplus_singleton hT _) hm
      simpa using this
  have hray : IsFullFutureBTZRay (ψ (yVertex v)) (fun t => ψ (yAxis v t)) :=
    ⟨v, W, ψ, hW, fun t ht => hsub (yAxis_mem_spearY hR ht), hψ, hinj, rfl, fun _ => rfl⟩
  have hmonoA : ∀ s t, 0 ≤ s → s ≤ t → (CE M).le ⊤ (ψ (yAxis v s)) (ψ (yAxis v t)) :=
    fun s t hs hst => hray.le hs hst
  obtain ⟨q', hq'⟩ := exists_tendsto_of_monotone hGH hmonoA (hGH.2 (ψ (yAxis v 0)) m)
    fun t ht => Causal.Causality.mem_diamond.2 ⟨hmonoA 0 t le_rfl ht, hmB t ht⟩
  exact axis_noLimit hW (fun t ht => hsub (yAxis_mem_spearY hR ht)) hψ hinj q' hq'

/-- **The interior of a spear image is the image of the model interior** `{f > v, r < R}`
(`ψ` is an injective open map on the open set `W`; no global hypothesis on `M`). -/
theorem interior_spearImage [HasGroupoid M e0Groupoid] {v R : ℝ} (hR : 0 < R) {W : Set E0Y}
    {ψ : E0Y → M} (hW : IsOpen W) (hsub : spearY v R ⊆ W) (hψ : IsE0Mor ψ W)
    (hinj : InjOn ψ W) :
    interior (ψ '' spearY v R) = ψ '' (paperInY '' {x | v < fcoord x ∧ rad x < R}) := by
  have hψc : ContinuousOn ψ W := fun x hx => (hψ x hx).continuousWithinAt
  apply Subset.antisymm
  · intro y hy
    obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := interior_subset hy
    set O' : Set E0 := paperInY ⁻¹' (W ∩ ψ ⁻¹' interior (ψ '' spearY v R)) with hO'def
    have hO' : IsOpen O' :=
      (hψc.isOpen_inter_preimage hW isOpen_interior).preimage continuous_paperInY
    have hxO' : x ∈ O' := ⟨hsub ⟨x, hx, rfl⟩, hy⟩
    have hO'S : O' ⊆ spear v R := by
      intro x' hx'
      obtain ⟨_, ⟨x'', hx'', rfl⟩, he⟩ := interior_subset hx'.2
      have h1 := hinj (hsub ⟨x'', hx'', rfl⟩) hx'.1 he
      have h2 := paperInY.injOn (by simp) (by simp) h1
      exact h2 ▸ hx''
    have hxi : x ∈ interior (spear v R) := interior_maximal hO'S hO' hxO'
    rw [interior_spear hR] at hxi
    exact ⟨_, ⟨x, hxi, rfl⟩, rfl⟩
  · have hOo : IsOpen {x : E0 | v < fcoord x ∧ rad x < R} :=
      (isOpen_lt continuous_const continuous_fcoord).inter
        (isOpen_lt continuous_rad continuous_const)
    have hOS : {x : E0 | v < fcoord x ∧ rad x < R} ⊆ spear v R := fun x hx => ⟨hx.1.le, hx.2.le⟩
    have hPW : paperInY '' {x : E0 | v < fcoord x ∧ rad x < R} ⊆ W :=
      fun _ hy => hsub (image_mono hOS hy)
    have hE := Causal.CBG.isEMorphismOn_of_liftPropOn E0.chartIso_mem_e0Groupoid
      E0.absolutelyMinimalOn_YBTZ (W := ⟨W, hW⟩) hψ
    have hopen := hE.isOpen_image ⟨_, isOpen_paperInY_image hOo⟩ hPW
    exact interior_maximal (image_mono (image_mono hOS)) hopen

/-- **B21 Def 2.1's boundary sentence is closedness** (no global hypothesis on `M`): for a spear
chart `ψ`, `∂(ψ 𝒮) = ψ(head ∪ shaft)` **iff** `ψ 𝒮` is closed in `M` (the interior is always the
image of the model interior, `interior_spearImage`, and `head ∪ shaft ⊆ 𝒮`). This is why
`IsSpearNbhd.isClosed` is the paper's sentence. -/
theorem frontier_spearImage_eq_iff_isClosed [HasGroupoid M e0Groupoid] {v R : ℝ} (hR : 0 < R)
    {W : Set E0Y} {ψ : E0Y → M} (hW : IsOpen W) (hsub : spearY v R ⊆ W) (hψ : IsE0Mor ψ W)
    (hinj : InjOn ψ W) :
    frontier (ψ '' spearY v R) = ψ '' (paperInY '' (spearHead v R ∪ spearShaft v R)) ↔
      IsClosed (ψ '' spearY v R) := by
  have hpinj : Injective paperInY := fun a b h => paperInY.injOn (by simp) (by simp) h
  have hint := interior_spearImage hR hW hsub hψ hinj
  constructor
  · intro hfr
    refine isClosed_of_closure_subset ?_
    rw [closure_eq_interior_union_frontier, hfr]
    refine union_subset interior_subset (image_mono (image_mono ?_))
    rw [← frontier_spear hR]
    exact (isClosed_spear v R).frontier_subset
  · intro hcl
    rw [frontier, hcl.closure_eq, hint, ← frontier_spear hR, frontier,
      (isClosed_spear v R).closure_eq, interior_spear hR, image_sdiff hpinj]
    exact ((hinj.mono hsub).image_sdiff_subset
      (image_mono fun x (hx : v < fcoord x ∧ rad x < R) => ⟨hx.1.le, hx.2.le⟩)).symm

/-- **B21 Def 2.1 in `M`: the boundary of a spear neighbourhood is its head and its shaft**,
`∂(ψ 𝒮) = ψ(head ∪ shaft)`, for a globally hyperbolic `M` (closedness, `isClosed_spearImage`). -/
theorem frontier_spearImage [HasGroupoid M e0Groupoid] [T2Space M]
    (hGH : (CE M).GloballyHyperbolic) {v R : ℝ} (hR : 0 < R) {W : Set E0Y} {ψ : E0Y → M}
    (hW : IsOpen W) (hsub : spearY v R ⊆ W) (hψ : IsE0Mor ψ W) (hinj : InjOn ψ W) :
    frontier (ψ '' spearY v R) = ψ '' (paperInY '' (spearHead v R ∪ spearShaft v R)) :=
  (frontier_spearImage_eq_iff_isClosed hR hW hsub hψ hinj).2
    (isClosed_spearImage hGH hR.le hW hsub hψ hinj)

/-- **In a globally hyperbolic `M`, a spear chart gives a spear neighbourhood**: the field
`IsSpearNbhd.isClosed` (Def 2.1's boundary sentence) is automatic (`isClosed_spearImage`). -/
theorem IsSpearNbhd.of_chart [HasGroupoid M e0Groupoid] [T2Space M]
    (hGH : (CE M).GloballyHyperbolic) {p : M} {R : ℝ} {U : Set M} (hR : 0 < R)
    (h : ∃ (v : ℝ) (W : Set E0Y) (ψ : E0Y → M), IsOpen W ∧ spearY v R ⊆ W ∧ IsE0Mor ψ W ∧
      InjOn ψ W ∧ ψ (yVertex v) = p ∧ U = ψ '' spearY v R) : IsSpearNbhd p R U := by
  refine ⟨hR, ?_, h⟩
  obtain ⟨v, W, ψ, hW, hsub, hψ, hinj, -, rfl⟩ := h
  exact isClosed_spearImage hGH hR.le hW hsub hψ hinj

/-- **In a globally hyperbolic `M`, a spear neighbourhood is exactly a spear chart** (so the
statements of Lemmas 2.3/2.4, all for GH `M`, are unchanged by the field `isClosed`). -/
theorem isSpearNbhd_iff_chart [HasGroupoid M e0Groupoid] [T2Space M]
    (hGH : (CE M).GloballyHyperbolic) {p : M} {R : ℝ} {U : Set M} :
    IsSpearNbhd p R U ↔ 0 < R ∧ ∃ (v : ℝ) (W : Set E0Y) (ψ : E0Y → M), IsOpen W ∧
      spearY v R ⊆ W ∧ IsE0Mor ψ W ∧ InjOn ψ W ∧ ψ (yVertex v) = p ∧ U = ψ '' spearY v R :=
  ⟨fun h => ⟨h.pos, h.chart⟩, fun h => IsSpearNbhd.of_chart hGH h.1 h.2⟩

/-- **B21 Def 2.1, in every `𝔼₀`-manifold: a spear neighbourhood is closed, with interior the
image of `{f > v, r < R}` and boundary the image of the head and the shaft** (l.617, with the
corrected head/shaft of DEC-116 (c); no global hypothesis on `M`, the boundary sentence being the
field `IsSpearNbhd.isClosed`, `frontier_spearImage_eq_iff_isClosed`). -/
theorem IsSpearNbhd.frontier_eq [HasGroupoid M e0Groupoid] {p : M} {R : ℝ} {U : Set M}
    (h : IsSpearNbhd p R U) :
    ∃ (v : ℝ) (W : Set E0Y) (ψ : E0Y → M), IsOpen W ∧ spearY v R ⊆ W ∧ IsE0Mor ψ W ∧
      InjOn ψ W ∧ ψ (yVertex v) = p ∧ U = ψ '' spearY v R ∧ IsClosed U ∧
      interior U = ψ '' (paperInY '' {x | v < fcoord x ∧ rad x < R}) ∧
      frontier U = ψ '' (paperInY '' (spearHead v R ∪ spearShaft v R)) := by
  obtain ⟨v, W, ψ, hW, hsub, hψ, hinj, hp, rfl⟩ := h.chart
  exact ⟨v, W, ψ, hW, hsub, hψ, hinj, hp, rfl, h.isClosed,
    interior_spearImage h.pos hW hsub hψ hinj,
    (frontier_spearImage_eq_iff_isClosed h.pos hW hsub hψ hinj).2 h.isClosed⟩

/-- **A spear neighbourhood is a neighbourhood of `]p, +∞[` ⊆ `Δ`** (B21 Def 2.1, read on the BTZ
line `Δ` itself rather than on the chart ray): for `γ` a parametrisation of `Δ` (the connected
component of `sing₀` through `p`) as in `IsFullFutureBTZRay.exists_eq_of_line`, every `γ s`,
`s > 0`, is a point of the chart ray strictly above `p`, hence an interior point
(`IsSpearNbhd.exists_ray_mem_nhds`). -/
theorem IsSpearNbhd.mem_nhds_of_line [HasGroupoid M e0Groupoid] [T2Space M]
    (hGH : (CE M).GloballyHyperbolic) {p : M} {R : ℝ} {U : Set M} (h : IsSpearNbhd p R U)
    {γ : ℝ → M} (hγ0 : γ 0 = p) (hγe : IsClosedEmbedding γ)
    (hγc : (CE M).CausalCurveIn ⊤ univ γ) (hγr : range γ = connectedComponentIn (S0 M) p)
    {s : ℝ} (hs : 0 < s) : U ∈ 𝓝 (γ s) := by
  obtain ⟨r, hr, hU⟩ := h.exists_ray_mem_nhds
  obtain ⟨t, ht, hrt⟩ := hr.exists_eq_of_line hGH hγ0 hγe hγc hγr hs.le
  rcases ht.lt_or_eq with ht | ht
  · rw [← hrt]; exact hU t ht
  · subst ht
    rw [hr.zero, ← hγ0] at hrt
    exact absurd (hγe.injective hrt) hs.ne

/-! #### The future case of Lemma 2.4 (WP-44d, DEC-108): continuation along the BTZ line

B21 l.725–733 covers the segment `[p, q]` of the BTZ line by axis charts and glues them, after
normalising the changes of charts to isometries of `𝔼₀`, with the spear chart. Here the gluing is
done **one chart at a time** (`CylChartData.exists_spear_below`): a spear chart `ψ` of vertex
`b` and the chart cylinder `κ` of a BTZ point `a` below `b` (with `b` in the cylinder) glue into a
spear chart of vertex any axis point of the cylinder below `b`. The transition `κ ∘ ψ` is, on the
connected component `U₀` of its domain around the vertex, a global isometry `e` of `𝔼₀`
(`btzE0_localUnique_core`, B21 `prop:isom_strong`, and rigidity `e0_eqOn_of_eqOn_open` — the
normalisation of the change of chart, on a **connected** overlap); the glued chart is `ψ` above the
level `w + η/3` and on `U₀`, and `κ⁻¹ ∘ e` on `U₀` and below that level. It is injective because a
point of the spear above the vertex sent by `ψ` into the chart cylinder lies in `U₀` (causal
convexity of the chart cylinder, `CylChartData.convex`: the whole causal diamond from the vertex is
sent into the cylinder). Then a continuation (`exists_spearNbhd_below`, the infimum of the
parameters of the line that are spear vertices) covers the segment. -/

omit [ChartedSpace E0Y M] in
/-- An element of the groupoid is an `𝔼₀`-morphism on its source. -/
theorem isE0Mor_of_mem_e0Groupoid {e : OpenPartialHomeomorph E0Y E0Y} (he : e ∈ e0Groupoid) :
    IsE0Mor e e.source := by
  have hQ : ∀ y : E0Y, e0Groupoid.IsLocalStructomorphWithinAt id univ y := fun y _ =>
    ⟨OpenPartialHomeomorph.refl E0Y, e0Groupoid.id_mem, fun _ _ => rfl, trivial⟩
  exact e0Groupoid.isLocalStructomorphWithinAt_localInvariantProp.liftPropOn_of_mem_maximalAtlas hQ
    (e0Groupoid.mem_maximalAtlas_of_mem_groupoid he)

omit [ChartedSpace E0Y M] in
/-- The relations of `D` on the `𝔼₀` summand of `Y` are those of `𝔼₀`. -/
theorem D_le_rangeInr_iff (x y : E0) :
    E0LM.D.le ⟨range Sum.inr, isOpen_range_inr⟩ (paperInY x) (paperInY y) ↔
      causality.le ⊤ x y := by
  have h := (chartIso_paperInY ⊤ (fun z _ => by simp [Causal.chartSource]) x trivial y trivial).1
  have himg : Causal.chartImage paperInY ⊤ = ⟨range Sum.inr, isOpen_range_inr⟩ := by
    apply SetLike.coe_injective
    rw [Causal.coe_chartImage, paperInY_source, univ_inter]
    ext z
    constructor
    · rintro ⟨w, -, rfl⟩; exact ⟨_, (paperInY_apply w).symm⟩
    · rintro ⟨x', rfl⟩; exact ⟨E0.toPaper x', trivial, by simp [paperInY_apply]⟩
  rw [himg] at h
  exact h.symm

omit [ChartedSpace E0Y M] in
theorem paperOfY_paperInY (x : E0) : paperOfY (paperInY x) = x := by simp [paperInY_apply]

omit [ChartedSpace E0Y M] in
/-- **An element of the groupoid defined on the whole `𝔼₀` summand preserves and reflects the
causal relation of `𝔼₀`** (`chartIso_mem_e0Groupoid` on `range Sum.inr`). -/
theorem le_iff_of_mem_e0Groupoid {e : OpenPartialHomeomorph E0Y E0Y} (he : e ∈ e0Groupoid)
    (hs : e.source = range Sum.inr) (ht : e.target = range Sum.inr) (x y : E0) :
    causality.le ⊤ x y ↔
      causality.le ⊤ (paperOfY (e (paperInY x))) (paperOfY (e (paperInY y))) := by
  let RI : Opens E0Y := ⟨range Sum.inr, isOpen_range_inr⟩
  have hRI : RI ≤ Causal.chartSource e := fun z hz => by
    show z ∈ e.source; rw [hs]; exact hz
  have hmem : ∀ x : E0, paperInY x ∈ RI := fun x => ⟨_, (paperInY_apply x).symm⟩
  have h := (E0.chartIso_mem_e0Groupoid e he RI hRI (paperInY x) (hmem x) (paperInY y)
    (hmem y)).1
  have himg : Causal.chartImage e RI = RI := by
    apply SetLike.coe_injective
    rw [Causal.coe_chartImage_of_le hRI]
    show e '' range Sum.inr = range Sum.inr
    calc e '' range Sum.inr = e '' e.source := by rw [hs]
      _ = e.target := e.image_source_eq_target
      _ = range Sum.inr := ht
  rw [himg] at h
  have hE : ∀ x : E0, e (paperInY x) = paperInY (paperOfY (e (paperInY x))) := fun x =>
    (paperInY_paperOfY (by rw [← ht]; exact e.map_source (by rw [hs]; exact hmem x))).symm
  rw [← D_le_rangeInr_iff, h, hE x, hE y, D_le_rangeInr_iff, paperOfY_paperInY,
    paperOfY_paperInY]

attribute [local instance] btzE0Structure in
/-- **The gluing step of B21 Lemma 2.4's future case**: if `b = κ⁻¹(w′, 0)`, a point of the axis
of the chart cylinder of `a`, is the vertex of a spear neighbourhood, so is every axis point
`κ⁻¹(u″, 0)` of the cylinder below it. -/
theorem CylChartData.exists_spear_below [HasGroupoid M e0Groupoid] [T2Space M] {a : M}
    (d : CylChartData a) (hGH : (CE M).GloballyHyperbolic) {R : ℝ} {U : Set M} {w' : ℝ}
    (hU : IsSpearNbhd ((chartAt E0Y a).symm (paperInY ((w', 0) : E0))) R U)
    (hw' : ((w', 0) : E0) ∈ cyl (d.v - d.ε) (d.v + d.ε) d.ε)
    {u'' : ℝ} (hu1 : d.v - d.ε < u'') (hu2 : u'' ≤ w') :
    ∃ R' U', IsSpearNbhd ((chartAt E0Y a).symm (paperInY ((u'', 0) : E0))) R' U' := by
  classical
  set κ := chartAt E0Y a with hκ
  set C : Set E0Y := paperInY '' cyl (d.v - d.ε) (d.v + d.ε) d.ε with hC
  have hCo : IsOpen C := isOpen_paperInY_image (isOpen_cyl _ _ _)
  have hCt : C ⊆ κ.target := d.cyl_sub
  have hCinr : C ⊆ range Sum.inr := by
    rintro _ ⟨x, -, rfl⟩; exact ⟨_, (paperInY_apply x).symm⟩
  set b := κ.symm (paperInY ((w', 0) : E0)) with hbdef
  obtain ⟨w, W, ψ, hW, hSW, hψ, hinj, hψb, -⟩ := hU.chart
  have hR := hU.pos
  have hψc : ContinuousOn ψ W := fun x hx => (hψ x hx).continuousWithinAt
  have hwC : paperInY ((w', 0) : E0) ∈ C := ⟨_, hw', rfl⟩
  have hbS : b ∈ κ.source := κ.map_target (hCt hwC)
  have hκb : κ b = paperInY ((w', 0) : E0) := κ.right_inv (hCt hwC)
  set V : Set E0Y := W ∩ ψ ⁻¹' (κ.source ∩ κ ⁻¹' C) with hV
  have hVo : IsOpen V := hψc.isOpen_inter_preimage hW (κ.isOpen_inter_preimage hCo)
  have hvW : yVertex w ∈ W := hSW ⟨vertex w, vertex_mem_spear hR.le, rfl⟩
  have hvV : yVertex w ∈ V := ⟨hvW, by rw [hψb]; exact hbS, by
    show κ (ψ (yVertex w)) ∈ C; rw [hψb, hκb]; exact hwC⟩
  set U₀ := connectedComponentIn V (yVertex w) with hU₀
  have hU₀o : IsOpen U₀ := hVo.connectedComponentIn
  have hU₀V : U₀ ⊆ V := connectedComponentIn_subset _ _
  have hU₀c : IsPreconnected U₀ := isPreconnected_connectedComponentIn
  have hvU₀ : yVertex w ∈ U₀ := mem_connectedComponentIn hvV
  have hspearW : spear w R ⊆ paperInY ⁻¹' W := fun x hx => hSW ⟨x, hx, rfl⟩
  have hW' : IsOpen (paperInY ⁻¹' W) := hW.preimage continuous_paperInY
  -- (1) a point of the spear sent by `ψ` into the chart cylinder lies in `U₀`
  have hcomp : ∀ x₁ ∈ spear w R, ψ (paperInY x₁) ∈ κ.source → κ (ψ (paperInY x₁)) ∈ C →
      paperInY x₁ ∈ U₀ := by
    intro x₁ hx₁ hs hc
    have hvs : vertex w ∈ spear w R := vertex_mem_spear hR.le
    have hvx : causality.le ⊤ (vertex w) x₁ := by
      rw [E0.le_top_iff, le_axis_iff (vertex_mem_axis w)]; exact hx₁.1
    obtain ⟨c, hc', hc0, hc1⟩ := (E0.causallyArcConnected ⊤ le_rfl _ _).1.1 hvx
    have hbmem : ψ (paperInY (vertex w)) ∈ κ.symm '' C := ⟨_, hwC, hψb.symm⟩
    have hx₁mem : ψ (paperInY x₁) ∈ κ.symm '' C := ⟨_, hc, κ.left_inv hs⟩
    have hpts : ∀ s ∈ Icc (0 : ℝ) 1, paperInY (c s) ∈ V := by
      intro s hs'
      have h1 : causality.le ⊤ (vertex w) (c s) := by
        rw [← hc0]; exact hc'.le_of_le le_rfl hs'.1 hs'.2
      have h2 : causality.le ⊤ (c s) x₁ := by
        rw [← hc1]; exact hc'.le_of_le hs'.1 hs'.2 le_rfl
      have hcs : c s ∈ spear w R := mem_spear_of_le hvs hx₁ h1 h2
      have hM1 : (CE M).le ⊤ (ψ (paperInY (vertex w))) (ψ (paperInY (c s))) :=
        le_of_isE0Mor_paper hW hψ (U := ⟨_, hW'⟩) subset_rfl
          (le_of_le_top_of_mem_spear hspearW hvs hcs h1)
      have hM2 : (CE M).le ⊤ (ψ (paperInY (c s))) (ψ (paperInY x₁)) :=
        le_of_isE0Mor_paper hW hψ (U := ⟨_, hW'⟩) subset_rfl
          (le_of_le_top_of_mem_spear hspearW hcs hx₁ h2)
      obtain ⟨z, hzC, hz⟩ := d.convex.2 _ hbmem _ hx₁mem
        (Causal.Causality.mem_diamond.2 ⟨hM1, hM2⟩)
      refine ⟨hspearW hcs, ?_, ?_⟩
      · show ψ (paperInY (c s)) ∈ κ.source
        rw [← hz]; exact κ.map_target (hCt hzC)
      · show κ (ψ (paperInY (c s))) ∈ C
        rw [← hz, κ.right_inv (hCt hzC)]; exact hzC
    have hpre : IsPreconnected ((fun s => paperInY (c s)) '' Icc 0 1) :=
      isPreconnected_Icc.image _
        (continuous_paperInY.comp_continuousOn (hc'.continuousOn causality.isRelFamily_le))
    have hsub := hpre.subset_connectedComponentIn (x := yVertex w)
      ⟨0, ⟨le_rfl, zero_le_one⟩, by simp only [hc0]; rfl⟩
      (by rintro _ ⟨s, hs', rfl⟩; exact hpts s hs')
    have := hsub ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩
    simp only [hc1] at this
    exact this
  -- (2) the transition `κ ∘ ψ` on `U₀` is a global isometry `e` of `𝔼₀`
  have hUinr : U₀ ⊆ range Sum.inr := by
    rcases Sum.isPreconnected_iff.1 hU₀c with ⟨t, -, ht⟩ | ⟨t, -, ht⟩
    · exfalso
      have h0 := hvU₀
      rw [ht] at h0
      obtain ⟨m, -, hm⟩ := h0
      simp [yVertex, vertex, paperInY_apply] at hm
    · rw [ht]; exact image_subset_range _ _
  set f : E0Y → E0Y := κ ∘ ψ with hf
  have hQ : ∀ y : E0Y, e0Groupoid.IsLocalStructomorphWithinAt id univ y := fun y _ =>
    ⟨OpenPartialHomeomorph.refl E0Y, e0Groupoid.id_mem, fun _ _ => rfl, trivial⟩
  have hψU : IsE0Mor ψ U₀ :=
    Causal.CBG.liftPropOn_mono_of_le hW hU₀o hψ (fun y hy => (hU₀V hy).1)
  have hfU : IsE0Mor f U₀ :=
    Causal.CBG.liftPropOn_comp hU₀o κ.open_source
      (e0Groupoid.isLocalStructomorphWithinAt_localInvariantProp.liftPropOn_chart hQ) hψU
      (fun y hy => (hU₀V hy).2.1)
  have hfinr : ∀ y ∈ U₀, f y ∈ range Sum.inr := fun y hy => hCinr (hU₀V hy).2.2
  set S : Set E0Y := U₀ ∩ e0Reg with hSdef
  have hSo : IsOpen S := hU₀o.inter isOpen_e0Reg
  have hSc : IsPreconnected S := isPreconnected_inter_e0Reg hU₀o hU₀c
  have hfS : ∀ y ∈ S, e0Groupoid.IsLocalStructomorphWithinAt f S y := by
    intro y hy _
    have h := (hfU y hy.1).2
    simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_apply,
      preimage_id_eq] at h
    obtain ⟨e, he, hfe, hye⟩ := h hy.1
    exact ⟨e, he, fun z hz => hfe ⟨hz.1.1, hz.2⟩, hye⟩
  have hfinj : InjOn f S := fun y hy y' hy' h =>
    hinj (hU₀V hy.1).1 (hU₀V hy'.1).1 (κ.injOn (hU₀V hy.1).2.1 (hU₀V hy'.1).2.1 h)
  set U' : Set BTZE0 := Sum.inr ⁻¹' U₀
  set F : BTZE0 → BTZE0 := fun x => e0Inr.symm (f (Sum.inr x))
  have hfF : ∀ x ∈ U', f (Sum.inr x) = Sum.inr (F x) := fun x hx => by
    obtain ⟨z, hz⟩ := hfinr (Sum.inr x) hx
    simp only [F, ← hz, e0Inr_symm_inr]
  have hloc : ∀ x ∈ U' ∩ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0,
      ∃ e ∈ e0Groupoid, Sum.inr x ∈ e.source ∧ f =ᶠ[𝓝 (Sum.inr x)] e := by
    rintro x ⟨hx, hxr⟩
    have hxS : (Sum.inr x : E0Y) ∈ S := ⟨hx, inr_mem_e0Reg_iff.2 hxr⟩
    obtain ⟨e, he, hfe, hxe⟩ := hfS _ hxS hxS
    exact ⟨e, he, hxe, Filter.eventually_of_mem ((hSo.inter e.open_source).mem_nhds ⟨hxS, hxe⟩)
      fun z hz => hfe hz⟩
  have hFc : ∀ x ∈ U' ∩ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0,
      ContinuousAt F x := by
    intro x hx
    obtain ⟨e, -, hxe, hfe⟩ := hloc x hx
    have hfc : ContinuousAt f (Sum.inr x) := (e.continuousAt hxe).congr hfe.symm
    have h1 : ContinuousAt e0Inr.symm (f (Sum.inr x)) :=
      e0Inr.symm.continuousAt (by rw [e0Inr_symm_source, hfF x hx.1]; exact ⟨_, rfl⟩)
    exact ContinuousAt.comp (g := e0Inr.symm) (f := fun x : BTZE0 => f (Sum.inr x)) h1
      (ContinuousAt.comp (g := f) (f := Sum.inr) hfc continuous_inr.continuousAt)
  have hFreg : ∀ x ∈ U' ∩ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0,
      F x ∈ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0 := by
    rintro x ⟨hx, hxr⟩
    have hxS : (Sum.inr x : E0Y) ∈ S := ⟨hx, inr_mem_e0Reg_iff.2 hxr⟩
    obtain ⟨e, he, hfe, hxe⟩ := hfS _ hxS hxS
    have hfe' : ∀ z ∈ S ∩ e.source, f z = e z := fun z hz => hfe hz
    have := mapsTo_e0Reg_of_mem he hxe hxS.2
    rw [← hfe' _ ⟨hxS, hxe⟩, hfF x hx] at this
    exact inr_mem_e0Reg_iff.1 this
  have hFloc : ∀ x ∈ U' ∩ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0,
      ∃ c ∈ aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0, x ∈ c.source ∧
      ∃ c' ∈ aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0, F x ∈ c'.source ∧
      ∃ h : Causal.Flat.isom 2, ∀ᶠ z in 𝓝 x, c' (F z) = h • c z := by
    rintro x ⟨hx, hxr⟩
    have hxS : (Sum.inr x : E0Y) ∈ S := ⟨hx, inr_mem_e0Reg_iff.2 hxr⟩
    obtain ⟨e, he, hfe, hxe⟩ := hfS _ hxS hxS
    have hfe' : ∀ z ∈ S ∩ e.source, f z = e z := fun z hz => hfe hz
    obtain ⟨c, hc, hxc⟩ := mem_support.1 hxr
    obtain ⟨c', hc', hFxc⟩ := mem_support.1 (hFreg x ⟨hx, hxr⟩)
    have hex : e (Sum.inr x) = Sum.inr (F x) := by rw [← hfe' _ ⟨hxS, hxe⟩, hfF x hx]
    obtain ⟨-, hch⟩ := ((mem_e0Groupoid_iff.1 he).1 _ hxe).2 hxS.2
    obtain ⟨h, hh⟩ := hch _ (e0InrChart_mem_e0Atlas hc) _ (e0InrChart_mem_e0Atlas hc')
      (mem_e0InrChart_source.2 ⟨x, hxc, rfl⟩)
      (by rw [hex]; exact mem_e0InrChart_source.2 ⟨_, hFxc, rfl⟩)
    refine ⟨c, hc, hxc, c', hc', hFxc, h, ?_⟩
    have hS' : Sum.inr ⁻¹' S ∈ 𝓝 x := (hSo.preimage continuous_inr).mem_nhds hxS
    have he' : Sum.inr ⁻¹' e.source ∈ 𝓝 x :=
      (e.open_source.preimage continuous_inr).mem_nhds hxe
    filter_upwards [continuous_inr.continuousAt.eventually hh, hS', he'] with z hz hzS hze
    rw [← hfe' _ ⟨hzS, hze⟩, hfF z hzS.1, e0InrChart_inr, e0InrChart_inr] at hz
    exact hz
  have hFinj : InjOn F (U' ∩ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) := by
    rintro x ⟨hx, hxr⟩ x' ⟨hx', hxr'⟩ hxx'
    have := hfinj ⟨hx, inr_mem_e0Reg_iff.2 hxr⟩ ⟨hx', inr_mem_e0Reg_iff.2 hxr'⟩
      (by rw [hfF x hx, hfF x' hx', show F x = F x' from hxx'])
    exact Sum.inr_injective this
  set a₀ : BTZE0 := E0.toPaper.symm ((w, 0) : E0)
  have ha₀ : (Sum.inr a₀ : E0Y) = yVertex w := by simp [a₀, yVertex, vertex, paperInY_apply]
  have ha₀U : a₀ ∈ U' := by show (Sum.inr a₀ : E0Y) ∈ U₀; rw [ha₀]; exact hvU₀
  have ha₀reg : a₀ ∉ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0 := by
    rw [← inr_mem_e0Reg_iff, ha₀]
    have := yAxis_mem_e0SingY w 0
    rw [yAxis_zero] at this
    exact this.2
  obtain ⟨Ψ, ψ', g, hlift, hpos, hD, W₀, hW₀o, hW₀ne, hW₀U, hW₀eq⟩ :=
    btzE0_localUnique_core ha₀reg (hU₀o.preimage continuous_inr) ha₀U hFc hFreg hFloc hFinj
  set e := e0Lift Ψ with he
  have heG : e ∈ e0Groupoid := e0Lift_mem Ψ ψ' g hlift hpos hD
  have hSe : S ⊆ e.source := fun y hy => by rw [e0Lift_source]; exact hUinr hy.1
  have heqW : EqOn f e (Sum.inr '' W₀) := by
    rintro _ ⟨w₁, hw₁, rfl⟩
    rw [hfF w₁ (hW₀U hw₁).1, e0Lift_apply, hW₀eq hw₁]
  have heqS : EqOn f e S :=
    e0_eqOn_of_eqOn_open hSo hSc hfS heG hSe (isOpenMap_inr _ hW₀o) (hW₀ne.image _)
      (by rintro _ ⟨w₁, hw₁, rfl⟩; exact ⟨(hW₀U hw₁).1, inr_mem_e0Reg_iff.2 (hW₀U hw₁).2⟩) heqW
  have hfc : ContinuousOn f U₀ := fun y hy => (hfU y hy).continuousWithinAt
  have heqU : ∀ y ∈ U₀, f y = e y := fun y hy =>
    e0_eq_of_mem_closure ((hfc _ hy).continuousAt (hU₀o.mem_nhds hy))
      (e.continuousAt (by rw [e0Lift_source]; exact hUinr hy))
      (dense_e0Reg.open_subset_closure_inter hU₀o hy) heqS
  -- (3) the axis segment `[w, w + η]` lies in `U₀`
  have hψvc : ContinuousAt ψ (yAxis w 0) := by
    rw [yAxis_zero]; exact (hψc _ hvW).continuousAt (hW.mem_nhds hvW)
  have hc0 : ContinuousAt (fun t => ψ (yAxis w t)) 0 :=
    ContinuousAt.comp (g := ψ) (f := yAxis w) hψvc (continuous_yAxis w).continuousAt
  have hNb : κ.source ∩ κ ⁻¹' C ∈ 𝓝 (ψ (yAxis w 0)) := by
    rw [yAxis_zero, hψb]
    exact (κ.isOpen_inter_preimage hCo).mem_nhds ⟨hbS, by show κ b ∈ C; rw [hκb]; exact hwC⟩
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.1 (hc0.preimage_mem_nhds hNb)
  set η' := η / 2 with hη'
  have hη'pos : 0 < η' := by linarith
  have hsegV : ∀ t ∈ Icc (0 : ℝ) η', yAxis w t ∈ V := fun t ht =>
    ⟨hSW (yAxis_mem_spearY hR.le ht.1), hball (by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]; linarith [ht.2])⟩
  have hsegU₀ : ∀ t ∈ Icc (0 : ℝ) η', yAxis w t ∈ U₀ := by
    have hsub := (isPreconnected_Icc.image _ (continuous_yAxis w).continuousOn).subset_connectedComponentIn
      (x := yVertex w) ⟨0, ⟨le_rfl, hη'pos.le⟩, yAxis_zero w⟩
      (by rintro _ ⟨t, ht, rfl⟩; exact hsegV t ht)
    exact fun t ht => hsub ⟨t, ht, rfl⟩
  -- (4) the new vertex, an axis point `(u, 0)` in the coordinates of `ψ`
  have hpu : paperInY ((u'', 0) : E0) ∈ e.target := by
    rw [e0Lift_target]; exact ⟨_, (paperInY_apply _).symm⟩
  set yu := e.symm (paperInY ((u'', 0) : E0)) with hyu
  have hyu_src : yu ∈ e.source := e.map_target hpu
  have heyu : e yu = paperInY ((u'', 0) : E0) := e.right_inv hpu
  obtain ⟨u, hyu_eq⟩ : ∃ u : ℝ, yu = paperInY ((u, 0) : E0) := by
    have hsing : paperInY ((u'', 0) : E0) ∉ e0Reg := by
      rw [paperInY_mem_e0Reg_iff, not_not]; rfl
    have hreg : yu ∉ e0Reg := fun h => hsing (heyu ▸ mapsTo_e0Reg_of_mem heG hyu_src h)
    obtain ⟨x, hx⟩ : yu ∈ range Sum.inr := by rw [← e0Lift_source Ψ]; exact hyu_src
    have hxp : yu = paperInY (E0.toPaper x) := by rw [← hx]; simp [paperInY_apply]
    rw [hxp, paperInY_mem_e0Reg_iff, not_not] at hreg
    refine ⟨(E0.toPaper x).1, ?_⟩
    rw [hxp]
    congr 1
    exact Prod.ext rfl hreg
  have hle_e := le_iff_of_mem_e0Groupoid heG (e0Lift_source Ψ) (e0Lift_target Ψ)
  have hE : ∀ x : E0, e (paperInY x) = paperInY (paperOfY (e (paperInY x))) := fun x =>
    (paperInY_paperOfY (by
      rw [← e0Lift_target Ψ]
      exact e.map_source (by rw [e0Lift_source]; exact ⟨_, (paperInY_apply x).symm⟩))).symm
  have hEw : paperOfY (e (paperInY ((w, 0) : E0))) = ((w', 0) : E0) := by
    have h1 : e (yVertex w) = paperInY ((w', 0) : E0) := by
      rw [← heqU _ hvU₀]; show κ (ψ (yVertex w)) = _; rw [hψb, hκb]
    show paperOfY (e (yVertex w)) = _
    rw [h1, paperOfY_paperInY]
  have hEu : paperOfY (e (paperInY ((u, 0) : E0))) = ((u'', 0) : E0) := by
    rw [← hyu_eq, heyu, paperOfY_paperInY]
  have huw : u ≤ w := by
    have h1 : causality.le ⊤ ((u'', 0) : E0) ((w', 0) : E0) :=
      E0.le_top_iff.2 (le_axis rfl rfl hu2)
    rw [← hEu, ← hEw, ← hle_e] at h1
    have := (le_axis_iff (show ((u, 0) : E0) ∈ axis from rfl)).1 (E0.le_top_iff.1 h1)
    simpa [fcoord, rad] using this
  have hEcyl : ∀ t : ℝ, u ≤ t → t ≤ w → e (paperInY ((t, 0) : E0)) ∈ C := by
    intro t h1 h2
    have hut : causality.le ⊤ ((u, 0) : E0) ((t, 0) : E0) := E0.le_top_iff.2 (le_axis rfl rfl h1)
    have htw : causality.le ⊤ ((t, 0) : E0) ((w, 0) : E0) := E0.le_top_iff.2 (le_axis rfl rfl h2)
    rw [hle_e, hEu] at hut
    rw [hle_e, hEw] at htw
    obtain ⟨hzax, hzw⟩ := (le_axis_iff' (show ((w', 0) : E0) ∈ axis from rfl)).1
      (E0.le_top_iff.1 htw)
    have hzu := (le_axis_iff (show ((u'', 0) : E0) ∈ axis from rfl)).1 (E0.le_top_iff.1 hut)
    rw [fcoord_of_axis hzax] at hzu
    rw [hE]
    have hw'2 : w' < d.v + d.ε := hw'.2.1
    refine ⟨_, ⟨by simp only at hzu ⊢; linarith, by simp only at hzw ⊢; linarith, ?_⟩, rfl⟩
    rw [rad_eq_zero.2 hzax]; exact d.pos
  -- (5) the glued chart `Φ`
  set c₁ := w + η' / 3 with hc₁
  set L : Set E0Y := (e.source ∩ e ⁻¹' C) ∩ paperInY '' {x | fcoord x < c₁} with hL
  set W₁ : Set E0Y := paperInY '' {x | c₁ < fcoord x ∧ rad x < R} with hW₁
  have hLo : IsOpen L := (e.isOpen_inter_preimage hCo).inter
    (isOpen_paperInY_image (isOpen_lt continuous_fcoord continuous_const))
  have hW₁o : IsOpen W₁ := isOpen_paperInY_image
    ((isOpen_lt continuous_const continuous_fcoord).inter (isOpen_lt continuous_rad continuous_const))
  have hW₁sp : ∀ y ∈ W₁, ∃ x ∈ spear w R, paperInY x = y := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, ⟨by linarith [hx.1], hx.2.le⟩, rfl⟩
  have hW₁W : W₁ ⊆ W := fun y hy => by
    obtain ⟨x, hx, rfl⟩ := hW₁sp y hy; exact hSW ⟨x, hx, rfl⟩
  have hLW₁ : ∀ y ∈ L, y ∉ W₁ := by
    rintro _ ⟨-, x, hx, rfl⟩ ⟨x', hx', hxx'⟩
    have : x' = x := paperInY.injOn (by simp) (by simp) hxx'
    subst this
    exact lt_asymm hx hx'.1
  have hUL : ∀ z ∈ U₀ ∪ L, z ∈ e.source ∧ e z ∈ κ.target := by
    rintro z (hz | hz)
    · exact ⟨by rw [e0Lift_source]; exact hUinr hz, by
        rw [← heqU z hz]; exact hCt (hU₀V hz).2.2⟩
    · exact ⟨hz.1.1, hCt hz.1.2⟩
  let Φ : E0Y → M := fun y => if y ∈ W₁ ∪ U₀ then ψ y else κ.symm (e y)
  have hΦ1 : ∀ y ∈ W₁ ∪ U₀, Φ y = ψ y := fun y hy => if_pos hy
  have hΦ2 : ∀ y ∈ U₀ ∪ L, Φ y = κ.symm (e y) := by
    intro y hy
    by_cases hyU : y ∈ U₀
    · rw [hΦ1 y (Or.inr hyU), ← heqU y hyU]
      exact (κ.left_inv (hU₀V hyU).2.1).symm
    · have hyL : y ∈ L := hy.resolve_left hyU
      have : y ∉ W₁ ∪ U₀ := fun h => h.elim (hLW₁ y hyL) hyU
      exact if_neg this
  set W' := W₁ ∪ U₀ ∪ L with hW'def
  have hW'o : IsOpen W' := (hW₁o.union hU₀o).union hLo
  have hκe : IsE0Mor (fun y => κ.symm (e y)) (e.source ∩ e ⁻¹' κ.target) :=
    Causal.CBG.liftPropOn_comp (e.isOpen_inter_preimage κ.open_target) κ.open_target
      (isE0Mor_chartAt_symm a)
      (Causal.CBG.liftPropOn_mono_of_le e.open_source (e.isOpen_inter_preimage κ.open_target)
        (isE0Mor_of_mem_e0Groupoid heG) inter_subset_left)
      (fun y hy => hy.2)
  have hΦmor : IsE0Mor Φ W' := by
    refine Causal.CBG.liftPropOn_of_locally hW'o fun y hy => ?_
    by_cases hy1 : y ∈ W₁ ∪ U₀
    · refine ⟨W₁ ∪ U₀, hW₁o.union hU₀o, fun z hz => Or.inl hz, hy1, ?_⟩
      exact Causal.CBG.liftPropOn_congr_of_eqOn (hW₁o.union hU₀o)
        (Causal.CBG.liftPropOn_mono_of_le hW (hW₁o.union hU₀o) hψ
          (union_subset hW₁W fun z hz => (hU₀V hz).1)) fun z hz => (hΦ1 z hz).symm
    · have hyL : y ∈ L := hy.resolve_left hy1
      refine ⟨U₀ ∪ L, hU₀o.union hLo, fun z hz => hz.elim (fun h => Or.inl (Or.inr h)) Or.inr,
        Or.inr hyL, ?_⟩
      exact Causal.CBG.liftPropOn_congr_of_eqOn (hU₀o.union hLo)
        (Causal.CBG.liftPropOn_mono_of_le (e.isOpen_inter_preimage κ.open_target)
          (hU₀o.union hLo) hκe fun z hz => hUL z hz) fun z hz => (hΦ2 z hz).symm
  have hκeinj : InjOn (fun y => κ.symm (e y)) (U₀ ∪ L) := by
    intro y₁ h₁ y₂ h₂ h
    exact e.injOn (hUL y₁ h₁).1 (hUL y₂ h₂).1
      (κ.symm.injOn (by rw [OpenPartialHomeomorph.symm_source]; exact (hUL y₁ h₁).2)
        (by rw [OpenPartialHomeomorph.symm_source]; exact (hUL y₂ h₂).2) h)
  -- a point of `W₁` sent into the chart cylinder lies in `U₀`
  have hW₁U : ∀ y ∈ W₁, Φ y ∈ κ.symm '' C → y ∈ U₀ := by
    intro y hy hΦy
    obtain ⟨x, hx, rfl⟩ := hW₁sp y hy
    obtain ⟨z, hzC, hz⟩ := hΦy
    rw [hΦ1 _ (Or.inl hy)] at hz
    refine hcomp x hx (by rw [← hz]; exact κ.map_target (hCt hzC)) ?_
    rw [← hz, κ.right_inv (hCt hzC)]; exact hzC
  have hΦinj : InjOn Φ W' := by
    have hLC : ∀ y ∈ L, Φ y ∈ κ.symm '' C := fun y hy =>
      ⟨e y, hy.1.2, (hΦ2 y (Or.inr hy)).symm⟩
    intro y₁ h₁ y₂ h₂ h
    by_cases c1 : y₁ ∈ U₀ ∪ L <;> by_cases c2 : y₂ ∈ U₀ ∪ L
    · exact hκeinj c1 c2 (by show κ.symm (e y₁) = κ.symm (e y₂); rw [← hΦ2 _ c1, ← hΦ2 _ c2]; exact h)
    · have hy₂W : y₂ ∈ W₁ ∪ U₀ := by
        rcases h₂ with h₂ | h₂
        · exact h₂
        · exact absurd (Or.inr h₂) c2
      have hy₂W₁ : y₂ ∈ W₁ := hy₂W.resolve_right fun h => c2 (Or.inl h)
      by_cases hy₁W : y₁ ∈ W₁ ∪ U₀
      · rw [hΦ1 _ hy₁W, hΦ1 _ hy₂W] at h
        exact hinj (union_subset hW₁W (fun z hz => (hU₀V hz).1) hy₁W)
          (union_subset hW₁W (fun z hz => (hU₀V hz).1) hy₂W) h
      · have hy₁L : y₁ ∈ L := c1.resolve_left fun h => hy₁W (Or.inr h)
        exact absurd (Or.inl (hW₁U y₂ hy₂W₁ (h ▸ hLC y₁ hy₁L))) c2
    · have hy₁W : y₁ ∈ W₁ ∪ U₀ := by
        rcases h₁ with h₁ | h₁
        · exact h₁
        · exact absurd (Or.inr h₁) c1
      have hy₁W₁ : y₁ ∈ W₁ := hy₁W.resolve_right fun h => c1 (Or.inl h)
      by_cases hy₂W : y₂ ∈ W₁ ∪ U₀
      · rw [hΦ1 _ hy₁W, hΦ1 _ hy₂W] at h
        exact hinj (union_subset hW₁W (fun z hz => (hU₀V hz).1) hy₁W)
          (union_subset hW₁W (fun z hz => (hU₀V hz).1) hy₂W) h
      · have hy₂L : y₂ ∈ L := c2.resolve_left fun h => hy₂W (Or.inr h)
        exact absurd (Or.inl (hW₁U y₁ hy₁W₁ (h.symm ▸ hLC y₂ hy₂L))) c1
    · have hy₁ : y₁ ∈ W₁ ∪ U₀ := by
        rcases h₁ with h₁ | h₁
        · exact h₁
        · exact absurd (Or.inr h₁) c1
      have hy₂ : y₂ ∈ W₁ ∪ U₀ := by
        rcases h₂ with h₂ | h₂
        · exact h₂
        · exact absurd (Or.inr h₂) c2
      rw [hΦ1 _ hy₁, hΦ1 _ hy₂] at h
      exact hinj (union_subset hW₁W (fun z hz => (hU₀V hz).1) hy₁)
        (union_subset hW₁W (fun z hz => (hU₀V hz).1) hy₂) h
  -- (6) the new spear lies in the domain
  set Seg : Set E0 := (fun t : ℝ => ((t, 0) : E0)) '' Icc u c₁ with hSeg
  have hSegc : IsCompact Seg := isCompact_Icc.image (continuous_id.prodMk continuous_const)
  set O : Set E0 := paperInY ⁻¹' (U₀ ∪ L) with hO
  have hOo : IsOpen O := (hU₀o.union hLo).preimage continuous_paperInY
  have hSegO : Seg ⊆ O := by
    rintro _ ⟨t, ht, rfl⟩
    by_cases htw : w ≤ t
    · left
      have h1 := hsegU₀ (t - w) ⟨by linarith, by linarith [ht.2]⟩
      have h2 : yAxis w (t - w) = paperInY ((t, 0) : E0) := by simp [yAxis]
      rw [h2] at h1
      exact h1
    · push Not at htw
      right
      refine ⟨⟨by rw [e0Lift_source]; exact ⟨_, (paperInY_apply _).symm⟩,
        hEcyl t ht.1 htw.le⟩, ⟨(t, 0), ?_, rfl⟩⟩
      show fcoord ((t, 0) : E0) < c₁
      rw [fcoord_of_axis rfl]; simp only; linarith
  obtain ⟨δ, hδ, hthick⟩ := hSegc.exists_thickening_subset_open hOo hSegO
  set R' := min (R / 2) (δ / 2) with hR'def
  have hR' : 0 < R' := lt_min (by linarith) (by linarith)
  have hsub' : spearY u R' ⊆ W' := by
    rintro _ ⟨x, hx, rfl⟩
    have hrx : rad x ≤ R' := hx.2
    by_cases hxf : c₁ < fcoord x
    · exact Or.inl (Or.inl ⟨x, ⟨hxf, hrx.trans_lt
        ((min_le_left _ _).trans_lt (by linarith))⟩, rfl⟩)
    · have hxO : x ∈ O := by
        refine hthick (Metric.mem_thickening_iff.2 ⟨((fcoord x, 0) : E0),
          ⟨fcoord x, ⟨hx.1, not_lt.1 hxf⟩, rfl⟩, ?_⟩)
        have hr : rad x ≤ δ / 2 := hrx.trans (min_le_right _ _)
        rw [Prod.dist_eq]
        refine max_lt ?_ ?_
        · rw [Real.dist_eq]
          simp only [fcoord]
          rw [show x.1 - (x.1 - rad x / 2) = rad x / 2 by ring,
            abs_of_nonneg (by linarith [rad_nonneg x])]
          linarith
        · rw [dist_zero_right]; show rad x < δ; linarith
      rcases hxO with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  -- (7) the vertex
  have huSeg : paperInY ((u, 0) : E0) ∈ U₀ ∪ L :=
    hSegO ⟨u, ⟨le_rfl, by linarith⟩, rfl⟩
  have hvert : Φ (yVertex u) = κ.symm (paperInY ((u'', 0) : E0)) := by
    show Φ (paperInY ((u, 0) : E0)) = _
    rw [hΦ2 _ huSeg, ← hyu_eq, heyu]
  exact ⟨R', Φ '' spearY u R',
    IsSpearNbhd.of_chart hGH hR' ⟨u, W', Φ, hW'o, hsub', hΦmor, hΦinj, hvert, rfl⟩⟩

/-- **Continuation along the BTZ line** (B21 l.725–733, DEC-108): if the point `γ 0` of a BTZ line
`γ` (continuous, in `sing₀`, future causal) is the vertex of a spear neighbourhood, so is every
`γ s`, `s ≤ 0`. The infimum `t₀` of the parameters in `[s, 0]` that are spear vertices is one, and
equals `s`: at `γ t₀` take a chart cylinder (`exists_cylChartData`); the line near `t₀` runs along
its axis, a spear vertex `γ t₁` (`t₁` close to `t₀`) lies in it, and `exists_spear_below` makes
every axis point of the cylinder below `γ t₁` a spear vertex, `γ t₀` and the points just below
included. -/
theorem exists_spearNbhd_below [HasGroupoid M e0Groupoid] [T2Space M]
    (hGH : (CE M).GloballyHyperbolic) {γ : ℝ → M} (hγc : Continuous γ) (hγS : ∀ t, γ t ∈ S0 M)
    (hγle : ∀ s t, s ≤ t → (CE M).le ⊤ (γ s) (γ t)) {R : ℝ} {U : Set M}
    (hU : IsSpearNbhd (γ 0) R U) {s : ℝ} (hs : s ≤ 0) : ∃ R' U', IsSpearNbhd (γ s) R' U' := by
  set T : Set ℝ := {t | s ≤ t ∧ t ≤ 0 ∧ ∃ R' U', IsSpearNbhd (γ t) R' U'} with hT
  have h0T : (0 : ℝ) ∈ T := ⟨hs, le_rfl, R, U, hU⟩
  have hTb : BddBelow T := ⟨s, fun t ht => ht.1⟩
  set t₀ := sInf T with ht₀
  have hst₀ : s ≤ t₀ := le_csInf ⟨0, h0T⟩ fun t ht => ht.1
  have ht₀0 : t₀ ≤ 0 := csInf_le hTb h0T
  obtain ⟨d⟩ := exists_cylChartData hGH (hγS t₀)
  set κ := chartAt E0Y (γ t₀) with hκ
  let CO : Opens E0 := ⟨cyl (d.v - d.ε) (d.v + d.ε) d.ε, isOpen_cyl _ _ _⟩
  have hCt : paperInY '' (CO : Set E0) ⊆ κ.target := d.cyl_sub
  have hmemN : γ t₀ ∈ chartOpen (γ t₀) CO := by
    have h := mem_chartOpen (A := CO) hCt (vertex_mem_cyl d.pos)
    have hv : κ.symm (paperInY (vertex d.v)) = γ t₀ := d.vertex_eq
    rwa [hv] at h
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.1
    ((chartOpen (γ t₀) CO).isOpen.preimage hγc) t₀ hmemN
  -- points of the line near `t₀` are axis points of the cylinder
  have hcoord : ∀ t, |t - t₀| < η → ∃ τ : ℝ, ((τ, 0) : E0) ∈ cyl (d.v - d.ε) (d.v + d.ε) d.ε ∧
      κ.symm (paperInY ((τ, 0) : E0)) = γ t := by
    intro t ht
    have htN : γ t ∈ chartOpen (γ t₀) CO := hball (by rw [Metric.mem_ball, Real.dist_eq]; exact ht)
    obtain ⟨x, hxC, hxe⟩ := exists_of_mem_chartOpen htN
    have hκx : κ (γ t) = paperInY x := by rw [← hxe]; exact κ.right_inv (hCt ⟨x, hxC, rfl⟩)
    have hsing : κ (γ t) ∈ e0SingY 0 :=
      (E0CBG.chartAt_mem_e0SingY_iff htN.1 le_rfl).2 (hγS t)
    rw [hκx] at hsing
    have hax : x ∈ axis := by
      have := hsing.2
      rwa [paperInY_mem_e0Reg_iff, not_not] at this
    have hxeq : x = ((x.1, 0) : E0) := Prod.ext rfl hax
    exact ⟨x.1, hxeq ▸ hxC, by rw [← hxeq]; exact hxe⟩
  obtain ⟨t₁, ht₁T, ht₁lt⟩ := exists_lt_of_csInf_lt ⟨0, h0T⟩ (show sInf T < t₀ + η by linarith)
  have ht₀t₁ : t₀ ≤ t₁ := csInf_le hTb ht₁T
  obtain ⟨τ₁, hτ₁C, hτ₁⟩ := hcoord t₁ (by rw [abs_lt]; constructor <;> linarith)
  obtain ⟨-, -, R₁, U₁, hU₁⟩ := ht₁T
  rw [← hτ₁] at hU₁
  set t₂ := max s (t₀ - η / 2) with ht₂
  have ht₂t₀ : t₂ ≤ t₀ := max_le hst₀ (by linarith)
  obtain ⟨τ₂, hτ₂C, hτ₂⟩ := hcoord t₂ (by
    rw [abs_lt]; constructor <;> linarith [le_max_right s (t₀ - η / 2)])
  have hτ₂τ₁ : τ₂ ≤ τ₁ := by
    have h := hγle t₂ t₁ (ht₂t₀.trans ht₀t₁)
    rw [← hτ₁, ← hτ₂] at h
    exact (calculus_le (d.le_model hτ₂C hτ₁C h)).2.2.1
  obtain ⟨R₂, U₂, hU₂⟩ := d.exists_spear_below hGH hU₁ hτ₁C hτ₂C.1 hτ₂τ₁
  rw [hτ₂] at hU₂
  have ht₂T : t₂ ∈ T := ⟨le_max_left _ _, ht₂t₀.trans ht₀0, R₂, U₂, hU₂⟩
  have ht₀t₂ : t₀ ≤ t₂ := csInf_le hTb ht₂T
  have hs₂ : t₂ = s := by
    rcases max_cases s (t₀ - η / 2) with ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · linarith
  rw [← hs₂]
  exact ⟨R₂, U₂, hU₂⟩

/-- **B21 Lemma 2.4, the paper's statement** (`lem:add_BTZ_param`, `BTZ_1.tex:685–695`): the BTZ
line `Δ` (the component of `sing₀(M)` through `q`) admits a spear neighbourhood, of vertex `q`;
then for every `p ∈ Δ ∩ I⁻(Σ)` there is a spear neighbourhood of vertex `p` meeting `Σ` exactly
along the graph of a **continuous** function `τ_Σ` over the closed disc, in the shaft
(`τ_Σ > v + R′/2`, the paper's « positive » after its normalisation). Proof: `Δ` is the line
`γ` of `hLM`; if `p = γ s`, `s ≥ 0` (« `q` in the past of `p` »), `p` is on the spear's ray
(`IsFullFutureBTZRay.exists_eq_of_line`), the vertex moves up (`IsSpearNbhd.of_ray`) and
`lem_add_BTZ_param` concludes. The case `s < 0` (« `q` in the future of `p` », the charts along
`[p, q]` glued, DEC-108) is the continuation `exists_spearNbhd_below`. -/
theorem lem_add_BTZ_param_line [HasGroupoid M e0Groupoid] [T2Space M] [SecondCountableTopology M]
    (hLM : E0LM.E0GlobalBTZ (CE M) (S0 M)) (hGH : (CE M).GloballyHyperbolic) {Sig : Set M}
    (hSig : (CE M).IsCauchySurface Sig) {q : M} {R : ℝ} {U : Set M} (hU : IsSpearNbhd q R U)
    {p : M} (hpq : p ∈ connectedComponentIn (S0 M) q) (hpS : p ∈ (CE M).Iminus ⊤ Sig) :
    ∃ (R' v : ℝ) (W : Set E0Y) (ψ : E0Y → M), 0 < R' ∧ IsOpen W ∧ spearY v R' ⊆ W ∧
      IsE0Mor ψ W ∧ InjOn ψ W ∧ ψ (yVertex v) = p ∧
      ∃ τS : ℂ → ℝ, ContinuousOn τS (Metric.closedBall 0 R') ∧
        (∀ z : ℂ, ‖z‖ ≤ R' → v + R' / 2 < τS z) ∧
        ∀ x ∈ spear v R', (ψ (paperInY x) ∈ Sig ↔ x.1 = τS x.2) := by
  obtain ⟨v, W, ψ, hW, hSW, hψ, hinj, hq, hrays⟩ := hU.of_ray
  have hR := hU.pos
  have hr : IsFullFutureBTZRay q (fun t => ψ (yAxis v t)) :=
    ⟨v, W, ψ, hW, fun t ht => hSW (yAxis_mem_spearY hR.le ht), hψ, hinj, hq, fun _ => rfl⟩
  have hq0 : q ∈ S0 M := by
    have := hr.mem_S0 (le_refl 0)
    rwa [hr.zero] at this
  obtain ⟨γ, hγ0, hγe, hγi, hγr⟩ := hLM.line q hq0
  have hpγ : p ∈ range γ := by rw [hγr]; exact hpq
  obtain ⟨s, rfl⟩ := hpγ
  rcases le_or_gt 0 s with hs | hs
  · obtain ⟨t, ht, hts⟩ := hr.exists_eq_of_line hGH hγ0 (hγe hGH.1) hγi.1 hγr hs
    have hsp := hrays t ht
    have hts' : ψ (yAxis v t) = γ s := hts
    rw [hts'] at hsp
    obtain ⟨R', v', W', ψ', hR', -, hW', hsub', hψ', hinj', hp', τS, h0, h1, h2⟩ :=
      lem_add_BTZ_param hLM hGH hSig hsp hpS
    exact ⟨R', v', W', ψ', hR', hW', hsub', hψ', hinj', hp', τS, h0, h1, h2⟩
  · have hγe' := hγe hGH.1
    have hγS : ∀ t, γ t ∈ S0 M := fun t => by
      have : γ t ∈ connectedComponentIn (S0 M) q := hγr ▸ mem_range_self t
      exact connectedComponentIn_subset _ _ this
    have hU' : IsSpearNbhd (γ 0) R U := by rw [hγ0]; exact hU
    obtain ⟨R₁, U₁, hsp⟩ := exists_spearNbhd_below hGH hγe'.continuous hγS
      (fun s t hst => hγi.1.le_of_le trivial trivial hst) hU' hs.le
    obtain ⟨R', v', W', ψ', hR', -, hW', hsub', hψ', hinj', hp', τS, h0, h1, h2⟩ :=
      lem_add_BTZ_param hLM hGH hSig hsp hpS
    exact ⟨R', v', W', ψ', hR', hW', hsub', hψ', hinj', hp', τS, h0, h1, h2⟩

end AddBTZParam

/-! ### §4 B21 Lemma 2.3 (`lem:tube`): spear neighbourhoods in Cauchy-maximal `𝔼₀`-manifolds

(Placed after §5, WP-46b fixer round 2: the spear chart it produces is closed in `M` by
`isClosed_spearImage`, a §5′ lemma, which `IsSpearNbhd`'s `isClosed` field needs.) -/

section Tube

open E0CBG

/-- **The output of the gluing in the proof of B21 Lemma 2.3** (`BTZ_1.tex:642–670`): a Cauchy
sub-development `ι : M₀ → M` of `M` (the paper's `M₀ = M ∖ J⁺(φ⁻¹Π)`, through which `p = ι p₀`
is reached), and a Cauchy development `emb : M₀ → N` of `M₀` (the paper's
`M₂ = (M₀ ⊔ 𝒮)/∼`) carrying a spear chart `ψ` of vertex `emb p₀`. -/
structure SpearDevelopment (M : Type) [TopologicalSpace M] [ChartedSpace E0Y M] (p : M) where
  /-- The Cauchy sub-development `M₀`. -/
  M₀ : Type
  [top₀ : TopologicalSpace M₀]
  [t2₀ : T2Space M₀]
  [conn₀ : ConnectedSpace M₀]
  [sc₀ : SecondCountableTopology M₀]
  [cs₀ : ChartedSpace E0Y M₀]
  [hg₀ : HasGroupoid M₀ e0Groupoid]
  /-- The development `M₂` of `M₀` containing the spear. -/
  N : Type
  [topN : TopologicalSpace N]
  [t2N : T2Space N]
  [connN : ConnectedSpace N]
  [scN : SecondCountableTopology N]
  [csN : ChartedSpace E0Y N]
  [hgN : HasGroupoid N e0Groupoid]
  ι : M₀ → M
  isCauchyEmbedding_ι : Causal.IsCauchyEmbedding (CE M₀) (CE M) ι
  isE0Mor_ι : IsE0Mor ι univ
  emb : M₀ → N
  isCauchyEmbedding_emb : Causal.IsCauchyEmbedding (CE M₀) (CE N) emb
  isE0Mor_emb : IsE0Mor emb univ
  R : ℝ
  pos : 0 < R
  v : ℝ
  W : Set E0Y
  isOpen_W : IsOpen W
  spear_subset : spearY v R ⊆ W
  ψ : E0Y → N
  isE0Mor_ψ : IsE0Mor ψ W
  injOn_ψ : InjOn ψ W
  p₀ : M₀
  ι_p₀ : ι p₀ = p
  ψ_vertex : ψ (yVertex v) = emb p₀

attribute [instance] SpearDevelopment.top₀ SpearDevelopment.t2₀ SpearDevelopment.conn₀
  SpearDevelopment.sc₀ SpearDevelopment.cs₀ SpearDevelopment.hg₀ SpearDevelopment.topN
  SpearDevelopment.t2N SpearDevelopment.connN SpearDevelopment.scN SpearDevelopment.csN
  SpearDevelopment.hgN

variable
  (hLine : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [SecondCountableTopology M] [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid],
    E0LM.E0GlobalBTZ (Causal.CBG.chartedCausality E0LM.D M) (Causal.CBG.chartedSing e0SingY M 0))
  (hSC : ∀ {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [ChartedSpace E0Y M]
    [HasGroupoid M e0Groupoid], (Causal.CBG.chartedCausality E0LM.D M).GloballyHyperbolic →
    ∀ S : Set M, (Causal.CBG.chartedCausality E0LM.D M).IsCauchySurface S →
    SecondCountableTopology S → SecondCountableTopology M)

variable {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [SecondCountableTopology M]
  [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]

include hLine hSC in
/-- **The last step of B21 Lemma 2.3** (`BTZ_1.tex:666–667`): « `M₀ → M₂` is a Cauchy-embedding,
since `M` is Cauchy-maximal `M₂` embeds into `M`. The spear `𝒮` thus embeds in `M` around `Δ` »
— the embedding is `IsE0CauchyMaximal.exists_morphism_of_dev` (CBG universality), and the spear
chart of `M₂` composed with it is a spear chart of `M`. -/
theorem IsE0CauchyMaximal.isSpearNbhd_of_spearDevelopment (hGH : (CE M).GloballyHyperbolic)
    (hmax : IsE0CauchyMaximal M) {p : M}
    (D : SpearDevelopment M p) : ∃ R U, IsSpearNbhd p R U := by
  let Nd : Causal.CBG.Dev (e0Geometry hLine hSC).toPreGeometry (e0Str hLine hSC D.M₀) :=
    { carrier := D.N
      str := e0Str hLine hSC D.N
      emb := D.emb
      isCauchyEmbedding := D.isCauchyEmbedding_emb
      isMor := D.isE0Mor_emb }
  obtain ⟨F, hF, hFe, hFi⟩ := IsE0CauchyMaximal.exists_morphism_of_dev hLine hSC hmax D.ι
    D.isCauchyEmbedding_ι D.isE0Mor_ι Nd
  have hF' : IsE0Mor F univ := hF
  refine ⟨D.R, F '' (D.ψ '' spearY D.v D.R), IsSpearNbhd.of_chart hGH D.pos
    ⟨D.v, D.W, F ∘ D.ψ, D.isOpen_W, D.spear_subset,
    Causal.CBG.liftPropOn_comp D.isOpen_W isOpen_univ hF' D.isE0Mor_ψ (mapsTo_univ _ _),
    hFi.comp_injOn D.injOn_ψ, ?_, by rw [image_comp]⟩⟩
  change F (D.ψ (yVertex D.v)) = p
  have h1 : D.ψ (yVertex D.v) = D.emb D.p₀ := D.ψ_vertex
  exact (congrArg F h1).trans ((congrFun hFe D.p₀).trans D.ι_p₀)

include hLine hSC in
/-- **`M₀ → M` is a Cauchy embedding** (the inclusion of the past set `M₀`): `M₀` is globally
hyperbolic (causally convex in `M`, `Geometry.causality_restrict`), and the level set
`T = a` below `κ⁻¹Π` is a Cauchy surface of `M` and of `M₀`. -/
theorem CylChartData.isCauchyEmbedding_val {p : M} (d : CylChartData p)
    (hGH : (CE M).GloballyHyperbolic) :
    Causal.IsCauchyEmbedding (CE (d.W0o hGH)) (CE M) (Subtype.val : d.W0o hGH → M) := by
  have hres := Causal.CBG.Geometry.causality_restrict (𝔊 := e0Geometry hLine hSC)
    (e0Str hLine hSC M) (d.W0o hGH)
  have hCE : CE (d.W0o hGH) = ((CE M).restrict (d.W0o hGH)).toSubtype := hres
  obtain ⟨S, hSW, hS⟩ := d.exists_cauchy_subset_W0 hGH (hLine M)
  have hval := d.isEMorphism_val hGH
  have hU : ((d.W0o hGH : Opens M) : Set M) =
      Subtype.val '' ((⊤ : Opens (d.W0o hGH)) : Set (d.W0o hGH)) := by
    rw [Opens.coe_top, image_univ, Subtype.range_coe]
  have himg : Subtype.val '' (Subtype.val ⁻¹' S : Set (d.W0o hGH)) = S := by
    ext x
    exact ⟨fun ⟨y, hy, hyx⟩ => hyx ▸ hy, fun hx => ⟨⟨x, hSW hx⟩, hx, rfl⟩⟩
  refine ⟨?_, hGH, hval, Subtype.val_injective, Subtype.val ⁻¹' S, ?_, by rw [himg]; exact hS⟩
  · rw [hCE]; exact Causal.Causality.globallyHyperbolic_toSubtype (d.globallyHyperbolicOn_W0 hGH)
  · refine (hval.isCauchySurfaceOn_image_iff Subtype.val_injective.injOn le_rfl hU
      (subset_univ _)).2 ?_
    rw [himg]
    exact d.isCauchySurfaceOn_W0 hGH hSW hS

include hLine hSC in
/-- **The gluing of B21 Lemma 2.3** (`BTZ_1.tex:643–667`): around every BTZ point `p` of a
globally hyperbolic `𝔼₀`-manifold there is a `SpearDevelopment`. Built: `M₀ = M ∖ J⁺(κ⁻¹Π)`
(`CylChartData.W0o`), `M₂` the `Causal.CBG.FamilyGlueData` gluing of `M₀` and the spear piece
`𝒫` along `κ` (`CylChartData.glueData`), its atlas `FamilyGlueData.chartedSpace`
(`Causal.CBG.gluedChartedSpace`) with transitions in the groupoid (`glue_hasGroupoid`), Hausdorff
(`t2Space_glued`, closed graph), second countable, connected, `M₀ → M` a Cauchy embedding
(`isCauchyEmbedding_val`), the spear chart `ψN` of vertex `p`, `M₀` connected
(`connectedSpace_W0`) and the level set Cauchy in `M₀` (`isCauchySurfaceOn_W0`), `M₂` globally
hyperbolic (`globallyHyperbolic_glued`) with `Σ` a Cauchy surface (`isCauchySurface_glued`). -/
theorem exists_spearDevelopment (hGH : (CE M).GloballyHyperbolic) {p : M} (hp : p ∈ S0 M) :
    Nonempty (SpearDevelopment M p) := by
  obtain ⟨d⟩ := exists_cylChartData hGH hp
  letI := d.glueCS hGH
  haveI := d.glue_hasGroupoid hGH
  haveI := d.t2Space_glued hGH
  haveI := d.secondCountable_glued hGH
  haveI : ConnectedSpace (d.W0o hGH) := d.connectedSpace_W0 hGH (hLine M)
  haveI := d.connectedSpace_glued hGH
  have hι := d.isCauchyEmbedding_val hLine hSC hGH
  obtain ⟨S, hSW, hS⟩ := d.exists_cauchy_subset_W0 hGH (hLine M)
  have hemb : IsE0Mor ((d.glueData hGH).ι false : d.W0o hGH → (d.glueData hGH).Glued) univ :=
    d.glue_liftPropOn_ι hGH false
  have hembE : Causal.IsEMorphism (CE (d.W0o hGH)) (CE (d.glueData hGH).Glued)
      ((d.glueData hGH).ι false) := isEMorphismOn_of_isE0Mor (W := ⊤) hemb
  have hSsub : (CE (d.W0o hGH)).IsCauchySurface (Subtype.val ⁻¹' S : Set (d.W0o hGH)) := by
    have hval := d.isEMorphism_val hGH
    have hU : ((d.W0o hGH : Opens M) : Set M) =
        Subtype.val '' ((⊤ : Opens (d.W0o hGH)) : Set (d.W0o hGH)) := by
      rw [Opens.coe_top, image_univ, Subtype.range_coe]
    refine (hval.isCauchySurfaceOn_image_iff Subtype.val_injective.injOn le_rfl hU
      (subset_univ _)).2 ?_
    have himg : Subtype.val '' (Subtype.val ⁻¹' S : Set (d.W0o hGH)) = S := by
      ext x
      exact ⟨fun ⟨y, hy, hyx⟩ => hyx ▸ hy, fun hx => ⟨⟨x, hSW hx⟩, hx, rfl⟩⟩
    rw [himg]
    exact d.isCauchySurfaceOn_W0 hGH hSW hS
  exact ⟨{ M₀ := d.W0o hGH
           N := (d.glueData hGH).Glued
           ι := Subtype.val
           isCauchyEmbedding_ι := hι
           isE0Mor_ι := isE0Mor_val _
           emb := (d.glueData hGH).ι false
           isCauchyEmbedding_emb := ⟨hι.globallyHyperbolic_source, d.globallyHyperbolic_glued hGH,
             hembE, (d.glueData hGH).injective_ι false, _, hSsub,
             d.isCauchySurface_glued hGH hSW hS⟩
           isE0Mor_emb := hemb
           R := d.ε / 8
           pos := by linarith [d.pos]
           v := d.v
           W := gluePY d.v d.ε
           isOpen_W := (gluePY d.v d.ε).isOpen
           spear_subset := d.spearY_subset
           ψ := d.ψN hGH
           isE0Mor_ψ := d.isE0Mor_ψN hGH
           injOn_ψ := d.injOn_ψN hGH
           p₀ := d.pW0 hGH
           ι_p₀ := rfl
           ψ_vertex := d.ψN_vertex hGH }⟩

/-- **A globally hyperbolic `𝔼₀`-manifold has a Cauchy surface** (the strict
`Causal.Causality.SingularFlatAxioms.geroch_sing_i_imp_iii`, from `SingularFlatAxioms` — given by its BTZ lines
`hLM`, `E0LM.e0_singularFlatAxioms_of` — and the local admissible measures
`E0LM.e0_modelMeasures`). Used to drop the Cauchy-surface hypothesis of Lemma 2.3 (audit round 1). -/
theorem exists_isCauchySurface_of_globalBTZ {N : Type} [TopologicalSpace N] [T2Space N]
    [SecondCountableTopology N] [ChartedSpace E0Y N] [HasGroupoid N e0Groupoid]
    (hLM : E0LM.E0GlobalBTZ (CE N) (S0 N)) (hGH : (CE N).GloballyHyperbolic) :
    ∃ S : Set N, (CE N).IsCauchySurface S := by
  letI : MeasurableSpace N := borel N
  haveI : BorelSpace N := ⟨rfl⟩
  exact (E0LM.e0_singularFlatAxioms_of E0.chartIso_mem_e0Groupoid hLM).geroch_sing_i_imp_iii
    (E0LM.e0_modelMeasures N hGH) hGH

include hLine hSC in
/-- **B21 Lemma 2.3** (`lem:tube`, `BTZ_1.tex:635–638`): in a globally hyperbolic, Cauchy-maximal
`𝔼₀`-manifold, every BTZ point `p` is the vertex of a spear neighbourhood around its BTZ line.
Parameters `hLine`, `hSC`: those of CBG for `𝔼₀` (`E0CBG.e0Geometry`, WP-41f's (O2), (O4)). No
Cauchy surface is assumed: the gluing builds its own (`CylChartData.exists_cauchy_subset_W0`,
a level of the Cauchy time function of `geroch_sing_i_imp_ii`). -/
theorem lem_tube (hGH : (CE M).GloballyHyperbolic) (hmax : IsE0CauchyMaximal M) {p : M}
    (hp : p ∈ S0 M) : ∃ R U, IsSpearNbhd p R U := by
  exact IsE0CauchyMaximal.isSpearNbhd_of_spearDevelopment hLine hSC hGH hmax
    (exists_spearDevelopment hLine hSC hGH hp).some

include hLine hSC in
/-- **Full future BTZ rays** (`RamcovGX.tex:2352`'s « the singular locus contains full future BTZ
rays », correctly cited as B21 Lemma 2.3, not « Lemma 2.4 »: finding): in a globally hyperbolic
Cauchy-maximal `𝔼₀`-manifold, from every BTZ point starts a full future BTZ ray (the reading
`IsFullFutureBTZRay`, ruled by DEC-125 (b)). -/
theorem exists_fullFutureBTZRay (hGH : (CE M).GloballyHyperbolic) (hmax : IsE0CauchyMaximal M)
    {p : M} (hp : p ∈ S0 M) : ∃ γ : ℝ → M, IsFullFutureBTZRay p γ := by
  obtain ⟨R, U, h⟩ := lem_tube hLine hSC hGH hmax hp
  obtain ⟨γ, hγ, -⟩ := h.exists_ray
  exact ⟨γ, hγ⟩

end Tube

/-! ### §6 Lemma 2.4 in the setting where B21 applies it: Cauchy-maximal manifolds -/

section AddBTZParamMax

open E0CBG

variable
  (hLine : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [SecondCountableTopology M] [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid],
    E0LM.E0GlobalBTZ (Causal.CBG.chartedCausality E0LM.D M) (Causal.CBG.chartedSing e0SingY M 0))
  (hSC : ∀ {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [ChartedSpace E0Y M]
    [HasGroupoid M e0Groupoid], (Causal.CBG.chartedCausality E0LM.D M).GloballyHyperbolic →
    ∀ S : Set M, (Causal.CBG.chartedCausality E0LM.D M).IsCauchySurface S →
    SecondCountableTopology S → SecondCountableTopology M)

variable {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [SecondCountableTopology M]
  [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]

include hLine hSC in
/-- **B21 Lemma 2.4 for Cauchy-maximal `M`** (the setting of B21 Prop 2.17, where it is used): for
every BTZ point `p ∈ I⁻(Σ)` there is a spear neighbourhood of vertex `p` meeting `Σ` along the
graph of a function over the disc, in the shaft. The vertex is placed at `p` by Lemma 2.3. -/
theorem lem_add_BTZ_param_of_cauchyMaximal (hGH : (CE M).GloballyHyperbolic) {Sig : Set M}
    (hSig : (CE M).IsCauchySurface Sig) (hmax : IsE0CauchyMaximal M) {p : M} (hp : p ∈ S0 M)
    (hpS : p ∈ (CE M).Iminus ⊤ Sig) :
    ∃ (R' v : ℝ) (W : Set E0Y) (ψ : E0Y → M), 0 < R' ∧ IsOpen W ∧ spearY v R' ⊆ W ∧
      IsE0Mor ψ W ∧ InjOn ψ W ∧ ψ (yVertex v) = p ∧
      ∃ τS : ℂ → ℝ, ContinuousOn τS (Metric.closedBall 0 R') ∧
        (∀ z : ℂ, ‖z‖ ≤ R' → v + R' / 2 < τS z) ∧
        ∀ x ∈ spear v R', (ψ (paperInY x) ∈ Sig ↔ x.1 = τS x.2) := by
  obtain ⟨R, U, hU⟩ := lem_tube hLine hSC hGH hmax hp
  obtain ⟨R', v, W, ψ, hR', -, hW, hsub, hψ, hinj, hpv, τS, h0, h1, h2⟩ :=
    lem_add_BTZ_param (hLine M) hGH hSig hU hpS
  exact ⟨R', v, W, ψ, hR', hW, hsub, hψ, hinj, hpv, τS, h0, h1, h2⟩

end AddBTZParamMax

/-! ### §7 The parameter-free forms (WP-44d): the CBG inputs discharged

The parameters `hLine`, `hSC` (the CBG inputs (O2), (O4) of `E0CBG.e0Geometry`) and the
hypothesis `hLM` of Lemma 2.4 are discharged by the strict library: `E0LM.e0_globalBTZ` (O2) and
`E0LM.e0_secondCountable_of_cauchy` (O4), as in `GX.BTZ.Surgery`. -/

section ParameterFree

open E0CBG

variable {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [SecondCountableTopology M]
  [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]

/-- **B21 Lemma 2.3, with no parameter** (`lem:tube`): in a globally hyperbolic, Cauchy-maximal
`𝔼₀`-manifold every BTZ point is the vertex of a spear neighbourhood. -/
theorem lem_tube_e0 (hGH : (CE M).GloballyHyperbolic) (hmax : IsE0CauchyMaximal M) {p : M}
    (hp : p ∈ S0 M) : ∃ R U, IsSpearNbhd p R U :=
  lem_tube E0LM.e0_globalBTZ (fun {_} _ _ _ _ _ => E0LM.e0_secondCountable_of_cauchy) hGH hmax hp

/-- **Full future BTZ rays, with no parameter** (`RamcovGX.tex:2352`). -/
theorem exists_fullFutureBTZRay_e0 (hGH : (CE M).GloballyHyperbolic)
    (hmax : IsE0CauchyMaximal M) {p : M} (hp : p ∈ S0 M) :
    ∃ γ : ℝ → M, IsFullFutureBTZRay p γ :=
  exists_fullFutureBTZRay E0LM.e0_globalBTZ
    (fun {_} _ _ _ _ _ => E0LM.e0_secondCountable_of_cauchy) hGH hmax hp

/-- **B21 Lemma 2.4, the paper's statement, with no added hypothesis** (`lem:add_BTZ_param`):
`hLM` is `E0LM.e0_globalBTZ M`. -/
theorem lem_add_BTZ_param_line_e0 (hGH : (CE M).GloballyHyperbolic) {Sig : Set M}
    (hSig : (CE M).IsCauchySurface Sig) {q : M} {R : ℝ} {U : Set M} (hU : IsSpearNbhd q R U)
    {p : M} (hpq : p ∈ connectedComponentIn (S0 M) q) (hpS : p ∈ (CE M).Iminus ⊤ Sig) :
    ∃ (R' v : ℝ) (W : Set E0Y) (ψ : E0Y → M), 0 < R' ∧ IsOpen W ∧ spearY v R' ⊆ W ∧
      IsE0Mor ψ W ∧ InjOn ψ W ∧ ψ (yVertex v) = p ∧
      ∃ τS : ℂ → ℝ, ContinuousOn τS (Metric.closedBall 0 R') ∧
        (∀ z : ℂ, ‖z‖ ≤ R' → v + R' / 2 < τS z) ∧
        ∀ x ∈ spear v R', (ψ (paperInY x) ∈ Sig ↔ x.1 = τS x.2) :=
  lem_add_BTZ_param_line (E0LM.e0_globalBTZ M) hGH hSig hU hpq hpS

/-- **B21 Lemma 2.4 for Cauchy-maximal `M`, with no parameter.** -/
theorem lem_add_BTZ_param_of_cauchyMaximal_e0 (hGH : (CE M).GloballyHyperbolic) {Sig : Set M}
    (hSig : (CE M).IsCauchySurface Sig) (hmax : IsE0CauchyMaximal M) {p : M} (hp : p ∈ S0 M)
    (hpS : p ∈ (CE M).Iminus ⊤ Sig) :
    ∃ (R' v : ℝ) (W : Set E0Y) (ψ : E0Y → M), 0 < R' ∧ IsOpen W ∧ spearY v R' ⊆ W ∧
      IsE0Mor ψ W ∧ InjOn ψ W ∧ ψ (yVertex v) = p ∧
      ∃ τS : ℂ → ℝ, ContinuousOn τS (Metric.closedBall 0 R') ∧
        (∀ z : ℂ, ‖z‖ ≤ R' → v + R' / 2 < τS z) ∧
        ∀ x ∈ spear v R', (ψ (paperInY x) ∈ Sig ↔ x.1 = τS x.2) :=
  lem_add_BTZ_param_of_cauchyMaximal E0LM.e0_globalBTZ
    (fun {_} _ _ _ _ _ => E0LM.e0_secondCountable_of_cauchy) hGH hSig hmax hp hpS

end ParameterFree


end E0Spear

end GX
