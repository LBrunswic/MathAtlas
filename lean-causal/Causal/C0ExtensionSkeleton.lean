import Causal.DiamondConfinement
import Causal.SchwCausalLemmas

/-!
# The causal skeleton of Sbierski's `C⁰`-inextendibility proofs (1507.00601 Thm 3.1, Thm 4.10)

Programme target `T-abs-c0-extension-skeleton` (`programme/roadmap.toml`; layer 1, stream abstract,
ETT-layer imports only, no model, no metric). Source: J. Sbierski, *The C⁰-inextendibility of the
Schwarzschild spacetime and the spacelike diameter in Lorentzian geometry*, arXiv 1507.00601 v2,
`papers/sbierski-schwarzschild/legacy/labeled/InexSchwarzschild2.tex`. **No label is marked**: the
rows `schwthm:MinkInex` (Thm 3.1), `schwthm:Exterior` (Thm 4.10), `schwthm:MainThm` (Thm 4.9) and
`schwdef:extension` (Def 2.15) are statements about `C⁰` Lorentzian manifolds; this file is their
causal skeleton for any causality, the setting which the metric obstruction (timelike diameter,
layer 3) contradicts.

* **The setting** `Causality.ExitDiamonds W γ`: near the endpoint `γ 1`, inside any neighbourhood,
  an open `Ũ ∋ γ 1` and `s₀ < 1` with `γ([s₀, 1]) ⊆ Ũ` such that, for `s₀ ≤ r < s`, the chart
  diamond `I⁺(γ r, Ũ) ∩ I⁻(γ s, Ũ)` (`s ≤ 1`) has compact closure in `Ũ`, and (`s < 1`) the
  identification (1.2)'s `⊇`: `I⁺(γ r, W) ∩ I⁻(γ s, W) = I⁺(γ r, W ⊓ Ũ) ∩ I⁻(γ s, W ⊓ Ũ)
  ⊆ I⁺(γ r, Ũ) ∩ I⁻(γ s, Ũ)`, a diamond containing `γ((r, s))`.
* **The given-curve form** (the hypothesis of Thms 4.10, 4.11): `exitDiamonds_of_curve`, and
  `exitDiamonds_of_stronglyCausalOn` (local strong causality at `γ 1` only).
* **The assembly** (Thm 3.1 Steps 1, 1.2, 3; §1 `:145–158`): `exists_c0_extension_skeleton` (the
  target's form), `…_of_frontier` (strong causality near `∂W` only),
  `…_of_hasChronalNeighbourEverywhere` (the node `has_chronal_neighbour`).
* **The extension** (Def 2.15 read causally): `IsSpacetimeExtension CN C ι` (`ι` an open
  embedding with proper range and a `ChartIso` onto `ι(N)`, Rem 2.3); `rel_top_iff`,
  `image_Iplus_inter_Iminus`, `causallyArcConnectedOn`, `futureOneConnectedOn`, `dual`,
  `preimage_curve` (Step 1: `ι⁻¹ ∘ γ̃` future-inextensible in `N`), `exitDiamonds_of_curve`,
  `exists_c0_skeleton` (the corollary), `exists_c0_skeleton_of_hasChronalNeighbourEverywhere`;
  `ChartIso.causalCurveOn_image`.
* Witnesses (kb/0011): `timelikeLine_exists_c0_extension_skeleton` (`W = (−∞, 0)`),
  `exp_isSpacetimeExtension`, `timelikeLine_exp_c0_skeleton` (`exp : ℝ → ℝ`, onto `(0, ∞)`).

> One assumes that there is a C⁰-extension ι : M_max ↪ M̃ […]. Lemma 2.17 shows that there is then a
> timelike curve γ̃ in M̃ leaving the Schwarzschild spacetime M_max. […] we can choose s₀ such that
> the closure of I⁺(γ̃(s₀), Ũ) ∩ I⁻(γ̃(0), Ũ) in M̃ is contained in Ũ. (`:146`)

> By Lemma 2.17, we can then find a timelike curve γ̃ : [−1,0] → M̃ such that
> γ := ι⁻¹ ∘ γ̃|[−1,0) : [−1,0) → M_Mink is a timelike curve in M_Mink and γ̃(0) ∈ M̃ ∖ ι(M_Mink).
> Without loss of generality we can assume that γ is future directed (otherwise reverse the time
> orientation), and hence it is future inextendible in M_Mink. (`:485`)

> There does not exist a C⁰-extension ι : M_ext ↪ M̃ and a timelike curve γ : [−1, 0) → M_ext with
> (v* ∘ γ)(s) → ∞ for s ↗ 0 such that ι ∘ γ : [−1,0) → M̃ can be extended as a timelike curve to
> [−1,0]. (`:785–788`) […] One first repeats literally Step 1.1 - Step 1.3. […] Step 3 is then
> virtually identical again. (`:1078`)

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `M̃` a connected `C⁰` Lorentzian manifold (`:228`, `:401`) | ⚠ weakened: any causality, `[PreconnectedSpace M]`, `[LocallyCompactSpace M]`, `[T2Space M]` (`R₁` for the given-curve form, no connectedness) |
| `ι` a smooth isometric embedding onto a proper subset, same dimension (Def 2.15, `:406`) | ⚠ weakened: `W ⊊ M` open, non-empty; or `IsSpacetimeExtension` (open embedding, `range ι ≠ univ`, `ChartIso`) |
| `M̃` not necessarily time-orientable (Rem 2.16 (2), `:417`) | ⚠ a reading: `M̃` carries a causality, hence is time-oriented, and `ι` preserves the orientation (the binder's reading R3, OQ-115, open) |
| Lemma 2.17's chronal neighbour at `∂ι(M)` (`:431`) | ✓ carried, the edge hypothesis `chronal_neighbour_at_boundary`, or the node `has_chronal_neighbour` |
| `≪` realised by timelike curves in `M̃` and in `M` (Def 2.2) | ✓ carried: `CausallyArcConnected` of `M`, `CausallyArcConnectedOn W` (or of `N`) |
| `M` future one-connected (Step 2.1, Prop 4.12) | ✓ carried: `FutureOneConnectedOn W` (or `FutureOneConnected` of `N`) |
| Lemma 2.4's chart and the cone estimates (3.2) (Steps 1.1–1.2) | ⚠ replaced by the named localisation `LocallyStronglyCausal` (`T-lad-c0-extension-nodes`), used at `γ 1` only |
| Thm 4.10: `v* ∘ γ → ∞`, `ι ∘ γ` extends timelike to `[−1, 0]` | ⚠ weakened: a chronal curve of `M` over `[0, 1]` in `W` on `[0, 1)`; neither the divergence nor `γ 1 ∉ W` is used |

## SCOPE (disclosed)

* Nothing is marked. The steps left out are metric (Steps 1.3, 2.2, Prop 4.14, the contradiction
  of Step 3): `T-loc-c0-chart-diameter`, `T-loc-minkowski-timelike-diameter`,
  `T-loc-schw-exterior-divergence`. That a `C⁰` metric is a causality, that Lemma 2.4's chart is
  strongly causal and that a `C⁰` extension is an `IsSpacetimeExtension` (for a time-oriented `M̃`
  and an orientation-preserving `ι`: reading R3, OQ-115) is `T-loc-c0-metric-causality`.
* Curves are read as chronal curves over `[0, 1]` (`γ̃ : [−1, 0]` after an affine change), timelike
  as future or past: `D = C ∨ D = C.dual`, Sbierski's "otherwise reverse the time orientation".
* `ExitDiamonds` asks `Ũ` inside every neighbourhood of `γ 1` (Sbierski's `Ũ` is a chart domain).
* `LocallyStronglyCausal` is a named hypothesis (no ladder node yet); `causal_ladder` is not used:
  every ladder property enters as a hypothesis.
* **Moved in** (T-abs-sc-open-hoist): `IsSpacetimeExtension.isEMorphismOn`, an extension is an
  abstract `𝕄≥0`-morphism on `N` (`IsEMorphismOn`, `Causal.CauchyExtension`), from
  `Causal.FlrwType`, byte for byte under the same full name, in the namespace
  `IsSpacetimeExtension` after `dual` (it uses `le_chartSource` and `coe_chartImage_eq`). No import
  is added.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

/-!
## The reading

* **`M̃` is `M`, `ι(M)` the open `W`** (kb/0001, Rem 2.3 `:249`): `I^±(·, Ũ)` and `I^±(·, W)` are
  the relations of the opens `Ũ`, `W`. A spacetime `N` embedded by `ι` enters through
  `IsSpacetimeExtension`, whose `ChartIso` makes `N`'s relations those of `ι(N)`
  (`rel_top_iff`, `image_Iplus_inter_Iminus`), so every statement is made on `W = ι(N)` and
  transported.
* **"Future inextendible in `M`"** (`:485`) is DEC-13's `FutureInextensible` in `W`, and in `N` for
  `ι⁻¹ ∘ γ` (`preimage_curve`); Sbierski's own Def 2.10 sense is
  `Causal.Causality.not_continuousExtension_preimage` (`Causal.SchwCausalLemmas`).
* **The closure of the chart diamond** (Step 1.2, `:528`; Step 3, `:621`) is asked between every
  two vertices `γ r`, `γ s`, `s₀ ≤ r < s ≤ 1`; `r = s₀`, `s = 1` is the printed one, up to
  `γ̃(0)`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Function

universe u v

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable {C : Causality M} {W U : Opens M} {γ : ℝ → M}

variable (C) in
/-- **The causal setting at the end of `γ`** that Sbierski's metric obstruction contradicts (§1,
`:146–158`; Thm 3.1 Steps 1.2 and 3, `:528`, `:619–621`): for every neighbourhood `N` of `γ 1`,
an open `Ũ ∋ γ 1` inside `N` and `s₀ ∈ [0, 1)` with `γ([s₀, 1]) ⊆ Ũ` such that, for all
`s₀ ≤ r < s` (Sbierski's vertices `γ̃(s₀)`, `γ̃(s)`; the first one may be moved towards `1`),

* for `s ≤ 1`, the chart diamond `I⁺(γ r, Ũ) ∩ I⁻(γ s, Ũ)` has compact closure, in `Ũ`
  (`s = 1` is Step 1.2's printed diamond, up to `γ̃(0)`);
* for `s < 1`, the diamond of `W` from `γ r` to `γ s` contains `γ((r, s))` and equals that of
  `W ⊓ Ũ`, hence lies in the chart diamond: (1.2)'s `⊇` (`:153–158`). -/
def ExitDiamonds (W : Opens M) (γ : ℝ → M) : Prop :=
  ∀ N ∈ 𝓝 (γ 1), ∃ Ũ : Opens M, γ 1 ∈ Ũ ∧ (Ũ : Set M) ⊆ N ∧ ∃ s₀ ∈ Ico (0 : ℝ) 1,
    MapsTo γ (Icc s₀ 1) Ũ ∧
    (∀ r ∈ Ico s₀ 1, ∀ s ∈ Ioc r 1, IsCompact (closure (C.Iplus Ũ {γ r} ∩ C.Iminus Ũ {γ s})) ∧
      closure (C.Iplus Ũ {γ r} ∩ C.Iminus Ũ {γ s}) ⊆ Ũ) ∧
    ∀ r ∈ Ico s₀ 1, ∀ s ∈ Ioo r 1, (∀ t ∈ Ioo r s, γ t ∈ C.Iplus W {γ r} ∩ C.Iminus W {γ s}) ∧
      C.Iplus W {γ r} ∩ C.Iminus W {γ s} = C.Iplus (W ⊓ Ũ) {γ r} ∩ C.Iminus (W ⊓ Ũ) {γ s} ∧
      C.Iplus W {γ r} ∩ C.Iminus W {γ s} ⊆ C.Iplus Ũ {γ r} ∩ C.Iminus Ũ {γ s}

/-- **The given-curve form, with strong causality at the endpoint only**: a chronal curve `γ` of
`M` over `[0, 1]` lying in the causally arc-connected, future one-connected open `W` on `[0, 1)`,
whose endpoint has an open neighbourhood `U` strongly causal as a spacetime, on a locally compact
`R₁` space. The endpoint need not leave `W`. Proof: `StronglyCausalOn.exists_isCompact_closure`
gives `Ũ` and `V ∋ γ 1`; `γ([s₀, 1]) ⊆ V ∩ Ũ` by continuity at `1`; the segment `[r, s]`,
reparametrised over `[0, 1]`, is the chronal curve of `W` in `Ũ` which
`Iplus_inter_Iminus_eq_inf_of_futureOneConnectedOn` asks. -/
theorem exitDiamonds_of_stronglyCausalOn [LocallyCompactSpace M] [R1Space M]
    (hcac : C.CausallyArcConnectedOn W) (hfoc : C.FutureOneConnectedOn W)
    (hγ : C.ChronalCurveOn ⊤ γ 0 1) (hmem : ∀ t ∈ Ico (0 : ℝ) 1, γ t ∈ W)
    (hU : C.StronglyCausalOn U) (h1U : γ 1 ∈ U) : C.ExitDiamonds W γ := by
  intro N hN
  obtain ⟨Ũ, h1Ũ, -, hŨN, V, hV, hV'⟩ := hU.exists_isCompact_closure h1U hN
  -- the end of the curve lies in `V ∩ Ũ`
  have hcont : ContinuousWithinAt γ (Icc 0 1) 1 :=
    CurveOn.continuousOn C.isRelFamily_lt hγ 1 ⟨zero_le_one, le_rfl⟩
  obtain ⟨s₀, hs₀, hseg⟩ : ∃ s₀ ∈ Ico (0 : ℝ) 1, ∀ t ∈ Icc s₀ 1, γ t ∈ V ∩ Ũ := by
    have hpre := hcont.preimage_mem_nhdsWithin (inter_mem hV (Ũ.isOpen.mem_nhds h1Ũ))
    obtain ⟨u, hu, hsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hpre
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hu
    refine ⟨max 0 (1 - ε / 2), ⟨le_max_left _ _, max_lt one_pos (by linarith)⟩,
      fun t ht => hsub ⟨hball ?_, (le_max_left _ _).trans ht.1, ht.2⟩⟩
    have h1 := (le_max_right 0 (1 - ε / 2)).trans ht.1
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.2]
  refine ⟨Ũ, h1Ũ, hŨN, s₀, hs₀, fun t ht => (hseg t ht).2, fun r hr s hs => ?_,
    fun r hr s hs => ?_⟩
  · have hx := (hseg r ⟨hr.1, hr.2.le⟩).1
    have hy := (hseg s ⟨hr.1.trans hs.1.le, hs.2⟩).1
    exact ⟨(hV' _ hx _ hy).2.2.2.1, (hV' _ hx _ hy).2.2.2.2⟩
  · have hx := (hseg r ⟨hr.1, hr.2.le⟩).1
    have hy := (hseg s ⟨hr.1.trans hs.1.le, hs.2.le⟩).1
    have hcl := (hV' _ hx _ hy).2.2.2.2
    -- the segment of `γ` from `γ r` to `γ s`, a chronal curve of `W`
    have hr0 : 0 ≤ r := hs₀.1.trans hr.1
    have hres : C.ChronalCurveOn W γ r s :=
      CurveOn.restrict hγ hr0 hs.2.le le_top
        (fun t ht => hmem t ⟨hr0.trans ht.1, ht.2.trans_lt hs.2⟩)
    have hk : 0 < s - r := sub_pos.2 hs.1
    have hσ : C.ChronalCurveOn W (fun τ => γ ((s - r) * τ + r)) 0 1 := by
      refine CurveOn.comp_affine (k := s - r) (m := r) (a' := 0) (b' := 1) hk ?_
      have e0 : (s - r) * 0 + r = r := by ring
      have e1 : (s - r) * 1 + r = s := by ring
      rw [e0, e1]
      exact hres
    have hσ0 : (fun τ => γ ((s - r) * τ + r)) 0 = γ r := by simp
    have hσ1 : (fun τ => γ ((s - r) * τ + r)) 1 = γ s := by simp
    have hσŨ : MapsTo (fun τ => γ ((s - r) * τ + r)) (Icc 0 1) Ũ := fun τ hτ =>
      (hseg _ ⟨by nlinarith [hτ.1, hr.1], by nlinarith [hτ.2, hs.2]⟩).2
    refine ⟨fun t ht => ⟨Precausality.mem_Iplus_singleton.2 (hres.lt_of_lt le_rfl ht.1 ht.2.le),
        Precausality.mem_Iminus_singleton.2 (hres.lt_of_lt ht.1.le ht.2 le_rfl)⟩,
      Iplus_inter_Iminus_eq_inf_of_futureOneConnectedOn hcac hfoc hσ hσ0 hσ1 hσŨ hcl,
      Iplus_inter_Iminus_subset_of_futureOneConnectedOn hcac hfoc hσ hσ0 hσ1 hσŨ hcl⟩

/-- **The given-curve form** (the hypothesis of Sbierski Thms 4.10, 4.11, `:785–793`): on a locally
compact `R₁` space with a locally strongly causal causality, a chronal curve of `M` over `[0, 1]`
lying in the causally arc-connected, future one-connected open `W` on `[0, 1)` has
`ExitDiamonds W γ`. -/
theorem exitDiamonds_of_curve [LocallyCompactSpace M] [R1Space M]
    (hlsc : C.LocallyStronglyCausal) (hcac : C.CausallyArcConnectedOn W)
    (hfoc : C.FutureOneConnectedOn W) (hγ : C.ChronalCurveOn ⊤ γ 0 1)
    (hmem : ∀ t ∈ Ico (0 : ℝ) 1, γ t ∈ W) : C.ExitDiamonds W γ := by
  obtain ⟨U, h1U, hU⟩ := hlsc (γ 1)
  exact exitDiamonds_of_stronglyCausalOn hcac hfoc hγ hmem hU h1U

/-- **The assembly, with strong causality near `∂W` only**: `M` preconnected, locally compact,
Hausdorff and causally arc-connected; `W ⊊ M` open and non-empty, every frontier point with a
chronal neighbour and an open neighbourhood strongly causal as a spacetime; `W` causally
arc-connected and future one-connected. Then a chronal curve `γ` of `C` or of `C.dual` lies in `W`
on `[0, 1)`, ends on `∂W`, is future-inextensible in `W` over `[0, 1)`, and `ExitDiamonds W γ`. -/
theorem exists_c0_extension_skeleton_of_frontier [PreconnectedSpace M] [LocallyCompactSpace M]
    [T2Space M] (hC : C.CausallyArcConnected) (hne : (W : Set M).Nonempty)
    (hproper : (W : Set M) ≠ univ) (hchr : ∀ p ∈ frontier (W : Set M), C.HasChronalNeighbour p)
    (hsc : ∀ p ∈ frontier (W : Set M), ∃ U : Opens M, p ∈ U ∧ C.StronglyCausalOn U)
    (hcac : C.CausallyArcConnectedOn W) (hfoc : C.FutureOneConnectedOn W) :
    ∃ D : Causality M, (D = C ∨ D = C.dual) ∧ ∃ γ : ℝ → M, D.ChronalCurveOn ⊤ γ 0 1 ∧
      (∀ t ∈ Ico (0 : ℝ) 1, γ t ∈ W) ∧ γ 1 ∉ W ∧ γ 1 ∈ frontier (W : Set M) ∧
      D.FutureInextensible W (Ico 0 1) γ ∧ D.ExitDiamonds W γ := by
  obtain ⟨γ, hγ, hmem, h1, hfr⟩ := exists_leaving hC W.isOpen hne hproper hchr
  obtain ⟨U, h1U, hU⟩ := hsc (γ 1) hfr
  rcases hγ with h | h
  · exact ⟨C, Or.inl rfl, γ, h, hmem, h1, hfr,
      h.futureInextensible_of_leaving zero_lt_one le_top hmem h1,
      exitDiamonds_of_stronglyCausalOn hcac hfoc h hmem hU h1U⟩
  · exact ⟨C.dual, Or.inr rfl, γ, h, hmem, h1, hfr,
      h.futureInextensible_of_leaving zero_lt_one le_top hmem h1,
      exitDiamonds_of_stronglyCausalOn (dual_causallyArcConnectedOn.2 hcac)
        (dual_futureOneConnectedOn.2 hfoc) h hmem (dual_stronglyCausalOn.2 hU) h1U⟩

/-- **The causal skeleton of Sbierski Thm 3.1 and Thm 4.9** (`:475–624`, `:797–813`; §1
`:145–158`), the target's form: `M` preconnected, locally compact, Hausdorff, causally
arc-connected and locally strongly causal; `W ⊊ M` open, non-empty, with chronal neighbours at `∂W`
(`chronal_neighbour_at_boundary`), causally arc-connected and future one-connected. Then a chronal
curve `γ` of `C` or `C.dual` leaves `W` at `γ 1 ∈ ∂W`, is future-inextensible in `W`, and for
some open `Ũ ∋ γ 1` (inside any neighbourhood) and `s₀ < 1`, for all `s ∈ (s₀, 1)`,
`I⁺(γ s₀, W) ∩ I⁻(γ s, W) ⊆ I⁺(γ s₀, Ũ) ∩ I⁻(γ s, Ũ)`, the latter of compact closure in `Ũ`
(`ExitDiamonds`). -/
theorem exists_c0_extension_skeleton [PreconnectedSpace M] [LocallyCompactSpace M] [T2Space M]
    (hC : C.CausallyArcConnected) (hlsc : C.LocallyStronglyCausal) (hne : (W : Set M).Nonempty)
    (hproper : (W : Set M) ≠ univ) (hchr : ∀ p ∈ frontier (W : Set M), C.HasChronalNeighbour p)
    (hcac : C.CausallyArcConnectedOn W) (hfoc : C.FutureOneConnectedOn W) :
    ∃ D : Causality M, (D = C ∨ D = C.dual) ∧ ∃ γ : ℝ → M, D.ChronalCurveOn ⊤ γ 0 1 ∧
      (∀ t ∈ Ico (0 : ℝ) 1, γ t ∈ W) ∧ γ 1 ∉ W ∧ γ 1 ∈ frontier (W : Set M) ∧
      D.FutureInextensible W (Ico 0 1) γ ∧ D.ExitDiamonds W γ :=
  exists_c0_extension_skeleton_of_frontier hC hne hproper hchr (fun p _ => hlsc p) hcac hfoc

/-- The assembly with the node `has_chronal_neighbour` (`HasChronalNeighbourEverywhere`) in place
of its boundary form. -/
theorem exists_c0_extension_skeleton_of_hasChronalNeighbourEverywhere [PreconnectedSpace M]
    [LocallyCompactSpace M] [T2Space M] (hC : C.CausallyArcConnected)
    (hE : C.HasChronalNeighbourEverywhere) (hlsc : C.LocallyStronglyCausal)
    (hne : (W : Set M).Nonempty) (hproper : (W : Set M) ≠ univ)
    (hcac : C.CausallyArcConnectedOn W) (hfoc : C.FutureOneConnectedOn W) :
    ∃ D : Causality M, (D = C ∨ D = C.dual) ∧ ∃ γ : ℝ → M, D.ChronalCurveOn ⊤ γ 0 1 ∧
      (∀ t ∈ Ico (0 : ℝ) 1, γ t ∈ W) ∧ γ 1 ∉ W ∧ γ 1 ∈ frontier (W : Set M) ∧
      D.FutureInextensible W (Ico 0 1) γ ∧ D.ExitDiamonds W γ :=
  exists_c0_extension_skeleton hC hlsc hne hproper (fun p _ => hE p) hcac hfoc

end Causality

/-! ### A chart isomorphism carries causal curves -/

namespace ChartIso

variable {X : Type v} [TopologicalSpace X] {C : Causality M} {D : Causality X}
  {e : OpenPartialHomeomorph M X} {W : Opens M} {c : ℝ → M} {a b : ℝ}

/-- A chart which is an isomorphism carries the future causal curves of an open `W` of its source
to those of `e(W)`: the `≤` twin of `ChartIso.chronalCurveOn_image` (`Causal.GXStructure`). -/
theorem causalCurveOn_image (h : ChartIso C D e) (hW : W ≤ chartSource e)
    (hc : C.CausalCurveOn W c a b) : D.CausalCurveOn (chartImage e W) (e ∘ c) a b := by
  refine ⟨fun t ht => mem_chartImage_of_mem (hW (hc.mem t ht)) (hc.mem t ht),
    fun t ht N' _ htN' => ?_⟩
  let N : Opens M := W ⊓ ⟨e.source ∩ e ⁻¹' N', e.isOpen_inter_preimage N'.isOpen⟩
  have htN : c t ∈ N := ⟨hc.mem t ht, hW (hc.mem t ht), htN'⟩
  obtain ⟨l, u, hl, hu, hrel⟩ := hc.rel t ht N inf_le_left htN
  refine ⟨l, u, hl, hu, fun s hs s' hs' h1 h2 h3 => ?_⟩
  have hr := hrel s hs s' hs' h1 h2 h3
  have hNW : N ≤ chartSource e := inf_le_left.trans hW
  have hD := ((h N hNW _ (C.le_mem_left hr) _ (C.le_mem_right hr)).1).1 hr
  refine D.le_mono ?_ hD
  rintro _ ⟨z, ⟨_, hzN⟩, rfl⟩
  exact hzN.2.2

end ChartIso

/-! ### The ETT notion of an extension -/

section Extension

variable {N : Type v} [TopologicalSpace N] [Nonempty N]

/-- **An extension of topological spacetimes** (Sbierski Def 2.15, `:403–411`, read causally): `ι`
is an open embedding onto a proper subset of `M` which is an isomorphism of topological spacetimes
from `N` onto the open set `ι(N)` (`ChartIso` along `ι`): the relations of every open `U` of `N`
are those of `ι(U)` in `M` (Rem 2.3, `:249`). Only `ι(N)` open is used of the embedding
(Lemma 2.17), the isometry only through the causality. `M̃` is time-oriented and `ι` preserves the
orientation, which Def 2.15 does not ask (Rem 2.16 (2), `:417`): the binder's reading R3, OQ-115. -/
structure IsSpacetimeExtension (CN : Causality N) (C : Causality M) (ι : N → M) : Prop where
  isOpenEmbedding : IsOpenEmbedding ι
  range_ne_univ : range ι ≠ univ
  chartIso : ChartIso CN C (isOpenEmbedding.toOpenPartialHomeomorph ι)

namespace IsSpacetimeExtension

variable {CN : Causality N} {C : Causality M} {ι : N → M}

/-- The image `ι(N)`, as an open set of `M`. -/
def rangeOpens (hι : IsSpacetimeExtension CN C ι) : Opens M :=
  ⟨range ι, hι.isOpenEmbedding.isOpen_range⟩

@[simp] theorem coe_rangeOpens (hι : IsSpacetimeExtension CN C ι) :
    (hι.rangeOpens : Set M) = range ι := rfl

/-- Every open set of `N` lies in the source of the chart `ι`. -/
theorem le_chartSource (hι : IsSpacetimeExtension CN C ι) (U : Opens N) :
    U ≤ chartSource (hι.isOpenEmbedding.toOpenPartialHomeomorph ι) := fun x _ => by
  simp [mem_chartSource]

/-- The image of an open set by the chart `ι` is its image by `ι`. -/
theorem coe_chartImage_eq (hι : IsSpacetimeExtension CN C ι) (U : Opens N) :
    (chartImage (hι.isOpenEmbedding.toOpenPartialHomeomorph ι) U : Set M) = ι '' U := by
  simp [Causal.coe_chartImage]

/-- The image of `N` by the chart `ι` is `ι(N)`. -/
theorem chartImage_top (hι : IsSpacetimeExtension CN C ι) :
    chartImage (hι.isOpenEmbedding.toOpenPartialHomeomorph ι) ⊤ = hι.rangeOpens :=
  SetLike.coe_injective (by rw [hι.coe_chartImage_eq]; simp)

/-- **Remark 2.3 read through the extension**: the relations of `N` are those of the open set
`ι(N)` of `M`. -/
theorem rel_top_iff (hι : IsSpacetimeExtension CN C ι) (x y : N) :
    (CN.le ⊤ x y ↔ C.le hι.rangeOpens (ι x) (ι y)) ∧
      (CN.lt ⊤ x y ↔ C.lt hι.rangeOpens (ι x) (ι y)) := by
  have h := hι.chartIso ⊤ (hι.le_chartSource ⊤) x trivial y trivial
  rw [hι.chartImage_top] at h
  simpa only [IsOpenEmbedding.toOpenPartialHomeomorph_apply] using h

/-- An extension is one of the time-reversed causalities. -/
theorem dual (hι : IsSpacetimeExtension CN C ι) : IsSpacetimeExtension CN.dual C.dual ι :=
  ⟨hι.isOpenEmbedding, hι.range_ne_univ,
    fun U hU x hx y hy => ⟨(hι.chartIso U hU y hy x hx).1, (hι.chartIso U hU y hy x hx).2⟩⟩

/-- **An extension is an abstract `𝕄≥0`-morphism** on `N`: the `ChartIso` along `ι` gives the
strong morphism and the local isomorphism (one chart, `V = N`). -/
theorem isEMorphismOn (hι : IsSpacetimeExtension CN C ι) : IsEMorphismOn CN C ⊤ ι where
  continuousOn := hι.isOpenEmbedding.continuous.continuousOn
  isOpen_image V _ := hι.isOpenEmbedding.isOpenMap V V.isOpen
  map_le V U _ hmaps x y hxy := by
    have h := ((hι.chartIso V (hι.le_chartSource V) x (CN.le_mem_left hxy) y
      (CN.le_mem_right hxy)).1).1 hxy
    simp only [IsOpenEmbedding.toOpenPartialHomeomorph_apply] at h
    refine C.le_mono ?_ h
    intro z hz
    rw [← SetLike.mem_coe, hι.coe_chartImage_eq] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact hmaps hw
  map_lt V U _ hmaps x y hxy := by
    have h := ((hι.chartIso V (hι.le_chartSource V) x (CN.lt_mem_left hxy) y
      (CN.lt_mem_right hxy)).2).1 hxy
    simp only [IsOpenEmbedding.toOpenPartialHomeomorph_apply] at h
    refine C.lt_mono ?_ h
    intro z hz
    rw [← SetLike.mem_coe, hι.coe_chartImage_eq] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact hmaps hw
  locally x _ := ⟨⊤, le_rfl, trivial, hι.isOpenEmbedding.injective.injOn,
    fun V' _ U hU y hy z hz => by
      have h := hι.chartIso V' (hι.le_chartSource V') y hy z hz
      have hVU : chartImage (hι.isOpenEmbedding.toOpenPartialHomeomorph ι) V' = U :=
        SetLike.coe_injective (by rw [hι.coe_chartImage_eq, hU])
      rw [hVU] at h
      simpa only [IsOpenEmbedding.toOpenPartialHomeomorph_apply] using h⟩

/-- **The diamonds of `N` are those of `ι(N)`**: `ι(I⁺(x, N) ∩ I⁻(y, N)) =
I⁺(ι x, ι(N)) ∩ I⁻(ι y, ι(N))`, the identification of `M` with `ι(M)` in (1.2) (`:155`). -/
theorem image_Iplus_inter_Iminus (hι : IsSpacetimeExtension CN C ι) (x y : N) :
    ι '' (CN.Iplus ⊤ {x} ∩ CN.Iminus ⊤ {y}) =
      C.Iplus hι.rangeOpens {ι x} ∩ C.Iminus hι.rangeOpens {ι y} := by
  ext p
  constructor
  · rintro ⟨z, ⟨hxz, hzy⟩, rfl⟩
    rw [Precausality.mem_Iplus_singleton] at hxz
    rw [Precausality.mem_Iminus_singleton] at hzy
    exact ⟨Precausality.mem_Iplus_singleton.2 ((hι.rel_top_iff x z).2.1 hxz),
      Precausality.mem_Iminus_singleton.2 ((hι.rel_top_iff z y).2.1 hzy)⟩
  · rintro ⟨hxp, hpy⟩
    rw [Precausality.mem_Iplus_singleton] at hxp
    rw [Precausality.mem_Iminus_singleton] at hpy
    obtain ⟨z, rfl⟩ : p ∈ range ι := C.lt_mem_right hxp
    exact ⟨z, ⟨Precausality.mem_Iplus_singleton.2 ((hι.rel_top_iff x z).2.2 hxp),
      Precausality.mem_Iminus_singleton.2 ((hι.rel_top_iff z y).2.2 hpy)⟩, rfl⟩

/-- Causal arc-connectedness passes from `N` to the open set `ι(N)`: a relation in an open
`U ≤ ι(N)` is one in `ι⁻¹(U)`, joined there by a curve whose image joins in `U`. (The converse
direction, model to chart source, is `ChartIso.causallyArcConnectedOn` of the model-layer
`Causal.Remarks.MassiveManifold`.) -/
theorem causallyArcConnectedOn (hι : IsSpacetimeExtension CN C ι)
    (hN : CN.CausallyArcConnected) : C.CausallyArcConnectedOn hι.rangeOpens := by
  rw [Causality.causallyArcConnectedOn_iff]
  intro U hU p q
  set e := hι.isOpenEmbedding.toOpenPartialHomeomorph ι
  let U' : Opens N := ⟨ι ⁻¹' U, U.isOpen.preimage hι.isOpenEmbedding.continuous⟩
  have hUU' : chartImage e U' = U := by
    refine SetLike.coe_injective ?_
    rw [hι.coe_chartImage_eq]
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hz
      obtain ⟨w, rfl⟩ : z ∈ range ι := hU hz
      exact ⟨w, hz, rfl⟩
  have hiso : ∀ x y : N, ι x ∈ U → ι y ∈ U →
      (CN.le U' x y ↔ C.le U (ι x) (ι y)) ∧ (CN.lt U' x y ↔ C.lt U (ι x) (ι y)) := by
    intro x y hx hy
    have h := hι.chartIso U' (hι.le_chartSource U') x hx y hy
    rw [hUU'] at h
    simpa only [e, IsOpenEmbedding.toOpenPartialHomeomorph_apply] using h
  refine ⟨fun hpq => ?_, fun hpq => ?_⟩
  · have hp := C.le_mem_left hpq
    have hq := C.le_mem_right hpq
    obtain ⟨p', rfl⟩ : p ∈ range ι := hU hp
    obtain ⟨q', rfl⟩ : q ∈ range ι := hU hq
    obtain ⟨c, hc, hc0, hc1⟩ :=
      ((hN U' le_top p' q').1).1 ((hiso p' q' hp hq).1.2 hpq)
    have himg := ChartIso.causalCurveOn_image hι.chartIso (hι.le_chartSource U') hc
    rw [hUU'] at himg
    refine ⟨ι ∘ c, ?_, by simp [hc0], by simp [hc1]⟩
    simpa only [e, IsOpenEmbedding.toOpenPartialHomeomorph_apply] using himg
  · have hp := C.lt_mem_left hpq
    have hq := C.lt_mem_right hpq
    obtain ⟨p', rfl⟩ : p ∈ range ι := hU hp
    obtain ⟨q', rfl⟩ : q ∈ range ι := hU hq
    obtain ⟨c, hc, hc0, hc1⟩ :=
      ((hN U' le_top p' q').2).1 ((hiso p' q' hp hq).2.2 hpq)
    have himg := ChartIso.chronalCurveOn_image hι.chartIso (hι.le_chartSource U') hc
    rw [hUU'] at himg
    refine ⟨ι ∘ c, ?_, by simp [hc0], by simp [hc1]⟩
    simpa only [e, IsOpenEmbedding.toOpenPartialHomeomorph_apply] using himg

/-- Future one-connectedness passes from `N` to the open set `ι(N)`
(`ChartIso.futureOneConnectedOn_iff`). -/
theorem futureOneConnectedOn (hι : IsSpacetimeExtension CN C ι)
    (hN : CN.FutureOneConnected) : C.FutureOneConnectedOn hι.rangeOpens := by
  have h := (ChartIso.futureOneConnectedOn_iff hι.chartIso (hι.le_chartSource ⊤)).1 hN
  rwa [hι.chartImage_top] at h

/-- **The given-curve form for an extension** (Sbierski Thm 4.10's hypothesis, `:785–788`, and
Thm 4.11's, `:790–793`): `N` causally arc-connected and future one-connected, `M` locally compact,
`R₁` and locally strongly causal, and a chronal curve `γ` of `M` over `[0, 1]` lying in `ι(N)` on
`[0, 1)` (`ι ∘ γ` extended to `[−1, 0]`). Then `ExitDiamonds ι(N) γ`; the diamonds of `N` are
read off by `image_Iplus_inter_Iminus`. -/
theorem exitDiamonds_of_curve [LocallyCompactSpace M] [R1Space M]
    (hι : IsSpacetimeExtension CN C ι) (hlsc : C.LocallyStronglyCausal)
    (hcac : CN.CausallyArcConnected) (hfoc : CN.FutureOneConnected) {γ : ℝ → M}
    (hγ : C.ChronalCurveOn ⊤ γ 0 1) (hmem : ∀ t ∈ Ico (0 : ℝ) 1, γ t ∈ range ι) :
    C.ExitDiamonds hι.rangeOpens γ :=
  Causality.exitDiamonds_of_curve hlsc (hι.causallyArcConnectedOn hcac)
    (hι.futureOneConnectedOn hfoc) hγ hmem

/-- **Sbierski Thm 3.1 Step 1, in `N`** (`:485`): a chronal curve `γ` of `M` over `[0, 1]` lying in
`ι(N)` on `[0, 1)` and leaving it at `1` is `ι ∘ δ` on `[0, 1)` for a curve `δ` of `N` which is
chronal over every `[0, s]`, `s < 1`, and future-inextensible in `N` over `[0, 1)`, on a Hausdorff
`M`. -/
theorem preimage_curve [T2Space M] (hι : IsSpacetimeExtension CN C ι) {γ : ℝ → M}
    (hγ : C.ChronalCurveOn ⊤ γ 0 1) (hmem : ∀ t ∈ Ico (0 : ℝ) 1, γ t ∈ range ι)
    (h1 : γ 1 ∉ range ι) :
    ∃ δ : ℝ → N, (∀ t ∈ Ico (0 : ℝ) 1, ι (δ t) = γ t) ∧
      (∀ s ∈ Ico (0 : ℝ) 1, CN.ChronalCurveOn ⊤ δ 0 s) ∧ CN.FutureInextensible ⊤ (Ico 0 1) δ := by
  set e := hι.isOpenEmbedding.toOpenPartialHomeomorph ι
  have hιδ : ∀ t ∈ Ico (0 : ℝ) 1, ι (e.symm (γ t)) = γ t := fun t ht =>
    IsOpenEmbedding.toOpenPartialHomeomorph_right_inv _ _ (hmem t ht)
  have hδ : ∀ s ∈ Ico (0 : ℝ) 1, CN.ChronalCurveOn ⊤ (fun t => e.symm (γ t)) 0 s := by
    intro s hs
    have hd : C.ChronalCurveOn (chartImage e ⊤) γ 0 s := by
      rw [hι.chartImage_top]
      exact CurveOn.restrict hγ le_rfl hs.2.le le_top
        (fun t ht => hmem t ⟨ht.1, ht.2.trans_lt hs.2⟩)
    exact ChartIso.chronalCurveOn_symm_image hι.chartIso (hι.le_chartSource ⊤) hd
  refine ⟨fun t => e.symm (γ t), hιδ, hδ, ?_⟩
  have hcurve : CN.CausalCurveIn ⊤ (Ico 0 1) (fun t => e.symm (γ t)) := by
    refine ⟨⟨0, left_mem_Ico.2 zero_lt_one⟩, ordConnected_Ico, fun a ha b hb => ?_⟩
    rcases le_or_gt a b with hab | hab
    · exact CurveOn.restrict (hδ b hb).causalCurveOn ha.1 le_rfl le_rfl (fun _ _ => trivial)
    · exact CurveOn.of_lt hab
  refine Causality.futureInextensible_of_forall_not_tendsto hcurve (isLUB_Ico zero_lt_one)
    (fun h => lt_irrefl (1 : ℝ) h.2) fun p _ hp => h1 ⟨p, ?_⟩
  have hcont : ContinuousWithinAt γ (Icc 0 1) 1 :=
    CurveOn.continuousOn C.isRelFamily_lt hγ 1 ⟨zero_le_one, le_rfl⟩
  have hlim : Tendsto γ (𝓝[<] 1) (𝓝 (γ 1)) := by
    rw [← nhdsWithin_Ico_eq_nhdsLT zero_lt_one]
    exact (hcont.mono Ico_subset_Icc_self).tendsto
  have hlim' : Tendsto γ (𝓝[<] 1) (𝓝 (ι p)) := by
    refine ((hι.isOpenEmbedding.continuous.tendsto p).comp hp).congr' ?_
    filter_upwards [Ico_mem_nhdsLT zero_lt_one] with t ht using hιδ t ht
  exact (tendsto_nhds_unique hlim hlim').symm

/-- **The corollary for an extension** (Sbierski Thm 3.1, Thm 4.9, causal skeleton): `ι : N → M` an
`IsSpacetimeExtension`, `M` preconnected, locally compact, Hausdorff, causally arc-connected and
locally strongly causal with chronal neighbours at `∂ι(N)`, `N` causally arc-connected and future
one-connected. For `(D, DN) = (C, CN)` or `(C.dual, CN.dual)` (the time orientation reversed), a
chronal curve `γ` of `D` leaves `ι(N)` at `γ 1 ∈ ∂ι(N)`; `γ = ι ∘ δ` on `[0, 1)` with `δ` chronal
in `N` on every `[0, s]` and future-inextensible in `N`; `ExitDiamonds ι(N) γ`; and the diamonds
of `N` between points of `δ` are, through `ι`, those of `ι(N)`. -/
theorem exists_c0_skeleton [PreconnectedSpace M] [LocallyCompactSpace M] [T2Space M]
    (hι : IsSpacetimeExtension CN C ι) (hC : C.CausallyArcConnected)
    (hlsc : C.LocallyStronglyCausal) (hchr : ∀ p ∈ frontier (range ι), C.HasChronalNeighbour p)
    (hcac : CN.CausallyArcConnected) (hfoc : CN.FutureOneConnected) :
    ∃ D : Causality M, ∃ DN : Causality N, ((D = C ∧ DN = CN) ∨ (D = C.dual ∧ DN = CN.dual)) ∧
      IsSpacetimeExtension DN D ι ∧
      ∃ γ : ℝ → M, ∃ δ : ℝ → N, D.ChronalCurveOn ⊤ γ 0 1 ∧
        (∀ t ∈ Ico (0 : ℝ) 1, ι (δ t) = γ t) ∧ γ 1 ∉ range ι ∧ γ 1 ∈ frontier (range ι) ∧
        (∀ s ∈ Ico (0 : ℝ) 1, DN.ChronalCurveOn ⊤ δ 0 s) ∧ DN.FutureInextensible ⊤ (Ico 0 1) δ ∧
        D.ExitDiamonds hι.rangeOpens γ ∧
        ∀ s₀ ∈ Ico (0 : ℝ) 1, ∀ s ∈ Ico (0 : ℝ) 1,
          ι '' (DN.Iplus ⊤ {δ s₀} ∩ DN.Iminus ⊤ {δ s}) =
            D.Iplus hι.rangeOpens {γ s₀} ∩ D.Iminus hι.rangeOpens {γ s} := by
  obtain ⟨D, hD, γ, hγ, hmem, h1, hfr, -, -⟩ :=
    Causality.exists_leaving_futureInextensible_of_isOpenEmbedding hι.isOpenEmbedding
      hι.range_ne_univ hC hchr
  have key : ∀ (D : Causality M) (DN : Causality N), IsSpacetimeExtension DN D ι →
      D.LocallyStronglyCausal → DN.CausallyArcConnected → DN.FutureOneConnected →
      D.ChronalCurveOn ⊤ γ 0 1 → ∃ δ : ℝ → N, (∀ t ∈ Ico (0 : ℝ) 1, ι (δ t) = γ t) ∧
        (∀ s ∈ Ico (0 : ℝ) 1, DN.ChronalCurveOn ⊤ δ 0 s) ∧ DN.FutureInextensible ⊤ (Ico 0 1) δ ∧
        D.ExitDiamonds hι.rangeOpens γ ∧
        ∀ s₀ ∈ Ico (0 : ℝ) 1, ∀ s ∈ Ico (0 : ℝ) 1,
          ι '' (DN.Iplus ⊤ {δ s₀} ∩ DN.Iminus ⊤ {δ s}) =
            D.Iplus hι.rangeOpens {γ s₀} ∩ D.Iminus hι.rangeOpens {γ s} := by
    intro D DN hι' hl hc hf hγ'
    obtain ⟨δ, hιδ, hδ, hinex⟩ := hι'.preimage_curve hγ' hmem h1
    refine ⟨δ, hιδ, hδ, hinex, hι'.exitDiamonds_of_curve hl hc hf hγ' hmem,
      fun s₀ hs₀ s hs => ?_⟩
    rw [hι'.image_Iplus_inter_Iminus, hιδ s₀ hs₀, hιδ s hs]
    rfl
  rcases hD with rfl | rfl
  · obtain ⟨δ, hιδ, hδ, hinex, hex, himg⟩ := key D CN hι hlsc hcac hfoc hγ
    exact ⟨D, CN, Or.inl ⟨rfl, rfl⟩, hι, γ, δ, hγ, hιδ, h1, hfr, hδ, hinex, hex, himg⟩
  · obtain ⟨δ, hιδ, hδ, hinex, hex, himg⟩ := key C.dual CN.dual hι.dual
      (Causality.dual_locallyStronglyCausal.2 hlsc)
      ((Causality.dual_causallyArcConnectedOn (W := ⊤)).2 hcac)
      (Causality.dual_futureOneConnected.2 hfoc) hγ
    exact ⟨C.dual, CN.dual, Or.inr ⟨rfl, rfl⟩, hι.dual, γ, δ, hγ, hιδ, h1, hfr, hδ, hinex, hex,
      himg⟩

/-- The corollary for an extension with the node `has_chronal_neighbour` of `M`. -/
theorem exists_c0_skeleton_of_hasChronalNeighbourEverywhere [PreconnectedSpace M]
    [LocallyCompactSpace M] [T2Space M] (hι : IsSpacetimeExtension CN C ι)
    (hC : C.CausallyArcConnected) (hE : C.HasChronalNeighbourEverywhere)
    (hlsc : C.LocallyStronglyCausal) (hcac : CN.CausallyArcConnected)
    (hfoc : CN.FutureOneConnected) :
    ∃ D : Causality M, ∃ DN : Causality N, ((D = C ∧ DN = CN) ∨ (D = C.dual ∧ DN = CN.dual)) ∧
      IsSpacetimeExtension DN D ι ∧
      ∃ γ : ℝ → M, ∃ δ : ℝ → N, D.ChronalCurveOn ⊤ γ 0 1 ∧
        (∀ t ∈ Ico (0 : ℝ) 1, ι (δ t) = γ t) ∧ γ 1 ∉ range ι ∧ γ 1 ∈ frontier (range ι) ∧
        (∀ s ∈ Ico (0 : ℝ) 1, DN.ChronalCurveOn ⊤ δ 0 s) ∧ DN.FutureInextensible ⊤ (Ico 0 1) δ ∧
        D.ExitDiamonds hι.rangeOpens γ ∧
        ∀ s₀ ∈ Ico (0 : ℝ) 1, ∀ s ∈ Ico (0 : ℝ) 1,
          ι '' (DN.Iplus ⊤ {δ s₀} ∩ DN.Iminus ⊤ {δ s}) =
            D.Iplus hι.rangeOpens {γ s₀} ∩ D.Iminus hι.rangeOpens {γ s} :=
  hι.exists_c0_skeleton hC hlsc (fun p _ => hE p) hcac hfoc

end IsSpacetimeExtension

end Extension

/-! ### Witnesses -/

/-- The open half-line `(−∞, 0)`. -/
def negHalfLine : Opens ℝ := ⟨Iio 0, isOpen_Iio⟩

/-- **Non-vacuity of the assembly** (kb/0011): the timelike line and `W = (−∞, 0)` satisfy every
hypothesis of `exists_c0_extension_skeleton` (preconnected, locally compact, Hausdorff, causally
arc-connected, strongly causal, chronal neighbours everywhere, `W` causally arc-connected and future
one-connected); `ExitDiamonds` puts `γ((s₀, s))` in the identified diamond, so it is not empty. -/
theorem timelikeLine_exists_c0_extension_skeleton :
    ∃ D : Causality ℝ, (D = timelikeLine ∨ D = timelikeLine.dual) ∧ ∃ γ : ℝ → ℝ,
      D.ChronalCurveOn ⊤ γ 0 1 ∧ (∀ t ∈ Ico (0 : ℝ) 1, γ t ∈ negHalfLine) ∧ γ 1 ∉ negHalfLine ∧
      γ 1 ∈ frontier (negHalfLine : Set ℝ) ∧ D.FutureInextensible negHalfLine (Ico 0 1) γ ∧
      D.ExitDiamonds negHalfLine γ :=
  Causality.exists_c0_extension_skeleton timelikeLine_causallyArcConnected
    timelikeLine_locallyStronglyCausal ⟨-1, show (-1 : ℝ) < 0 by norm_num⟩
    (fun h => lt_irrefl (0 : ℝ) (show (0 : ℝ) ∈ (negHalfLine : Set ℝ) from h ▸ mem_univ 0))
    (fun p _ => timelikeLine_hasChronalNeighbour p)
    (Causality.CausallyArcConnectedOn.mono timelikeLine_causallyArcConnected le_top)
    (timelikeLine_futureOneConnectedOn _)

/-- A strictly increasing open embedding `ℝ → ℝ` is an isomorphism of the timelike line onto its
image: `[x, y] ⊆ U` iff `[ι x, ι y] ⊆ ι(U)`, by the intermediate value theorem and injectivity. -/
theorem timelikeLine_chartIso_of_strictMono {ι : ℝ → ℝ} (hι : IsOpenEmbedding ι)
    (hmono : StrictMono ι) :
    ChartIso timelikeLine timelikeLine (hι.toOpenPartialHomeomorph ι) := by
  intro U _ x _ y _
  simp only [timelikeLine_le, timelikeLine_lt, Causal.coe_chartImage,
    IsOpenEmbedding.toOpenPartialHomeomorph_apply,
    IsOpenEmbedding.toOpenPartialHomeomorph_source, univ_inter]
  have key : x ≤ y → (Icc x y ⊆ (U : Set ℝ) ↔ Icc (ι x) (ι y) ⊆ ι '' U) := by
    intro hxy
    constructor
    · intro h z hz
      obtain ⟨w, hw, rfl⟩ := intermediate_value_Icc hxy hι.continuous.continuousOn hz
      exact ⟨w, h hw, rfl⟩
    · intro h w hw
      obtain ⟨u, hu, hue⟩ := h ⟨hmono.monotone hw.1, hmono.monotone hw.2⟩
      rwa [hmono.injective hue] at hu
  refine ⟨⟨fun h => ⟨hmono.monotone h.1, (key h.1).1 h.2⟩, fun h => ?_⟩,
    ⟨fun h => ⟨hmono h.1, (key h.1.le).1 h.2⟩, fun h => ?_⟩⟩
  · have hxy : x ≤ y := hmono.le_iff_le.1 h.1
    exact ⟨hxy, (key hxy).2 h.2⟩
  · have hxy : x < y := hmono.lt_iff_lt.1 h.1
    exact ⟨hxy, (key hxy.le).2 h.2⟩

/-- **An extension of the timelike line into itself**: `exp`, onto `(0, ∞)`. -/
theorem exp_isSpacetimeExtension : IsSpacetimeExtension timelikeLine timelikeLine Real.exp :=
  ⟨Real.isOpenEmbedding_exp, fun h => by
    have h0 : (0 : ℝ) ∈ range Real.exp := h ▸ mem_univ 0
    rw [Real.range_exp] at h0
    exact lt_irrefl (0 : ℝ) (mem_Ioi.1 h0),
    timelikeLine_chartIso_of_strictMono _ Real.exp_strictMono⟩

/-- **The extension form on a witness**: `exp : ℝ → ℝ` is an extension of the timelike line into
the timelike line, onto `(0, ∞)`, and every hypothesis of `IsSpacetimeExtension.exists_c0_skeleton`
holds; its conclusion follows. -/
theorem timelikeLine_exp_c0_skeleton :
    ∃ D : Causality ℝ, ∃ DN : Causality ℝ,
      ((D = timelikeLine ∧ DN = timelikeLine) ∨ (D = timelikeLine.dual ∧ DN = timelikeLine.dual)) ∧
      IsSpacetimeExtension DN D Real.exp ∧
      ∃ γ : ℝ → ℝ, ∃ δ : ℝ → ℝ, D.ChronalCurveOn ⊤ γ 0 1 ∧
        (∀ t ∈ Ico (0 : ℝ) 1, Real.exp (δ t) = γ t) ∧ γ 1 ∉ range Real.exp ∧
        γ 1 ∈ frontier (range Real.exp) ∧
        (∀ s ∈ Ico (0 : ℝ) 1, DN.ChronalCurveOn ⊤ δ 0 s) ∧ DN.FutureInextensible ⊤ (Ico 0 1) δ ∧
        D.ExitDiamonds exp_isSpacetimeExtension.rangeOpens γ ∧
        ∀ s₀ ∈ Ico (0 : ℝ) 1, ∀ s ∈ Ico (0 : ℝ) 1,
          Real.exp '' (DN.Iplus ⊤ {δ s₀} ∩ DN.Iminus ⊤ {δ s}) =
            D.Iplus exp_isSpacetimeExtension.rangeOpens {γ s₀} ∩
              D.Iminus exp_isSpacetimeExtension.rangeOpens {γ s} :=
  exp_isSpacetimeExtension.exists_c0_skeleton timelikeLine_causallyArcConnected
    timelikeLine_locallyStronglyCausal (fun p _ => timelikeLine_hasChronalNeighbour p)
    timelikeLine_causallyArcConnected timelikeLine_futureOneConnected

end Causal
