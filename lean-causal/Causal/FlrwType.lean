import Causal.C0ExtensionSkeleton
import Causal.PastInextensibleMeetsCauchy

/-!
# Abstract FLRW-type past inextendibility: no past boundary chart (Sbierski 2312.07443 Thm 1.5)

Programme target `T-abs-flrw-type` (`programme/roadmap.toml`; layer 1, stream abstract: it imports
`Causal.C0ExtensionSkeleton` and `Causal.PastInextensibleMeetsCauchy`, both ETT-layer; no model; no
metric, curve length or geodesic in a statement). 2312.07443 is not ledgered and has no binder, so
**no label is marked**. Source: J. Sbierski, *The C⁰-inextendibility of a class of FLRW
spacetimes*, `references/sbierski/text/sbierski2023c.txt`: the proof of Thm 1.5 (§4.1,
`:1057–1145`), Prop 2.1 and (2.4) (`:328–358`), Prop 3.6 (`:704–739`).

> Assume there exists a continuous extension ι : M ,→ M̃ such that ∂ − ι(M ) ̸= ∅. Let p̃ be a past
> boundary point. By Proposition 2.1 there exists a past boundary chart φ̃ : Ũ → (−ε0 , ε0 ) ×
> (−ε1 , ε1 )d around p̃. Consider the future directed timelike curve γ̃ : [0, ε0 ) → Ũ given in
> coordinates by s 7→ (s, 0). Then γ̃|(0,ε0 ) corresponds to a future directed and past inextendible
> timelike curve γ := ι−1 ◦ γ̃|(0,ε0 ) in M . (`:1057–1061`)

> Since the set I + p̃, Ũ ∩ I − γ̃(s0 ), Ũ is compactly contained in Ũ , there is an
> x0 ∈ (−ε1 , ε1 )d such that the timelike curve σ̃ : f (x0 ), ε0 ) → Ũ , given by s 7→ (s, x0 ),
> does not enter this set. […] To the future it contains a point in
> I + γ(s0 ), M ⊆ I + {t0 } × Sd , M by (4.1), but it does not intersect the Cauchy
> hypersurface {t0 } × Sd by (4.3). This is a contradiction (`:1137–1144`)

## What is proved (no `sorry`)

1. **The predicate** `Causality.PastBoundaryChart C W Ũ p` (`Nonempty` of the six-field structure
   `PastBoundaryChartData`), and its time reversal `FutureBoundaryChart` (Prop 2.1 as printed).
2. **The theorem** `Causality.not_pastBoundaryChart_of_flrwType`: on a T2, second countable space,
   an open `W`, causally arc-connected, future one-connected, with `≤_W` antisymmetric, (A) and
   (B), has a past boundary chart at no point. Its time reversal
   `not_futureBoundaryChart_of_flrwType`.
3. **The steps**: (a) `ChronalCurveOn.pastInextensible_Ioc_of_start_notMem`; (4.2) as an
   equality, `PastBoundaryChartData.biUnion_Iplus_inter_Iminus_eq` (its `⊆`:
   `Iplus_inter_Iminus_subset`); with (A), `Iminus_eq_diamond` (`I⁻(γ̃ s₀, W)` *is* the chart
   diamond); (4.3), `subset_diamond`.
4. **The corollary for an extension** `IsSpacetimeExtension.not_pastBoundaryChart_of_flrwType`
   (OQ-154's reading), through `isCauchySurfaceOn_image`, `le_antisymm_rangeOpens`,
   `iUnion_Iplus_eq_of_pastInextensible` and `exists_isCauchySurfaceOn_subset_Iminus`, and two
   transport lemmas first proved here and moved out by T-abs-sc-open-hoist, byte for byte under
   the same full names: `IsSpacetimeExtension.isEMorphismOn`, now in `Causal.C0ExtensionSkeleton`
   beside `IsSpacetimeExtension`, and `IsEMorphismOn.pastInextensible_invComp`, now in
   `Causal.CauchyExtension`, in the namespace of `IsEMorphismOn.inextensible_iff_invComp` (a last
   block that keeps this module's binder order, kb/0255).
5. **Witnesses** (kb/0011): the hypotheses hold jointly on `W = (0, ∞)` of the timelike line
   (`timelikeLine_flrwType_hypotheses_posHalfLine`), and the theorem applies there
   (`timelikeLine_posHalfLine_not_pastBoundaryChart`); the corollary applies to `exp : ℝ → ℝ`
   (`timelikeLine_exp_not_pastBoundaryChart`). On the timelike line no open set has a past
   boundary chart at all (`timelikeLine_not_pastBoundaryChart`: one dimension leaves no room for
   field (vi)), so these witnesses show the hypotheses consistent, not the predicate inhabited.

## Hypothesis checklist

| Sbierski Thm 1.5 / the target | here |
|---|---|
| `M̃` a manifold; the target: T2, second countable | ✓ `[T2Space M] [SecondCountableTopology M]` |
| `ι(M)` (the target's reading, kb/0001) | ✓ an open `W`; or `IsSpacetimeExtension` (OQ-154) |
| `≪` realised by timelike curves | ✓ `C.CausallyArcConnectedOn W` |
| `M` future one-connected (Prop 3.1, `d ≥ 2`) | ✓ `C.FutureOneConnectedOn W` |
| `M` globally hyperbolic, causal | ⚠ weakened: `≤_W` antisymmetric (inline); GH only through (B) |
| Prop 3.6, first claim | ⚠ a hypothesis: (A), for every past-inextensible curve chronal on its segments (Prop 3.6 itself is layer 3) |
| Prop 3.6, second claim | ⚠ a hypothesis: (B), at every point of `W` (used at `γ̃ s₀` only) |
| a past boundary chart around `p̃` (Prop 2.1, (2.4), (4.1)) | ✓ `PastBoundaryChart C W Ũ p` |
| conclusion: `∂⁻ι(M) = ∅` | ⚠ the ETT form: `¬ C.PastBoundaryChart W Ũ p` for every `Ũ`, `p`; `∂⁻ι(M) = ∅` follows once Prop 2.1 gives an ETT chart at each `p̃ ∈ ∂⁻ι(M)` (layer 3, `T-loc-c0-past-boundary-chart`) |

## SCOPE (disclosed)

* **The chart is a programme definition** (as `ExitDiamonds`, `IsSpacetimeExtension` were): that
  a `C⁰` past boundary chart (cone sandwich, Lipschitz graph, (4.1)) yields one is layer 3
  (`T-loc-c0-past-boundary-chart`).
* **No instance of `PastBoundaryChart` is built here** (layer 1 imports no model). On the
  timelike line it has none (`timelikeLine_not_pastBoundaryChart`), and the witnesses on `(0, ∞)`
  show the theorem's hypotheses consistent, not a chart inhabited. The instance is layer 3:
  `Causal.minkowski_pastBoundaryChart` (`Causal.Model.MinkowskiPastBoundaryChart`,
  T-loc-minkowski-past-boundary-chart), the half-space `{t > 0}` of `𝐌^{1+n}`, `n ≥ 1`, at `0`,
  where (A) and (B) both fail, so the theorem is not vacuous.
* **Sbierski's Thm 1.5 for FLRW is not proved here**: Props 2.1, 3.1 and 3.6 are layer 3, and enter
  as the chart predicate and the hypotheses (A), (B) and future one-connectedness.
* Field (iii) has the shape of `T-abs-boundary-chart-cauchy`'s conclusion
  (`∀ x ∈ V, C.Iplus Ũ {x} ⊆ C.Iplus V {x}`). The proof uses field (vi) at one compact set only,
  the closure of the chart diamond of (v).
* Timelike curves are chronal curves (DEC-6) over `[0, 1]`; "past inextendible" is DEC-13's
  `PastInextensible`; Cauchy surfaces are DEC-14's.
* `causal_ladder` is not used: no statement concludes a ladder property. At `W = ⊤` the theorem
  is empty (no point lies off `⊤`); its ladder form is the extension corollary, whose hypotheses
  on `N` are the nodes `causally_arc_connected`, `future_one_connected` and `is_causal`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set Function TopologicalSpace Topology Filter

universe u v

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable {C : Causality M} {W Ũ : Opens M} {p : M}

/-! ### The past boundary chart -/

variable (C) in
/-- **The data of a past boundary chart** `Ũ` of the open `W` at `p`: Sbierski's Prop 2.1 read for
the past boundary (`:328–358`), with the two vertical curves of §4.1 (`:1059–1072`, `:1137–1138`),
in ETT (kb/0001: `M̃` is `M`, `ι(M)` the open `W`, `I^±(·, Ũ)` the relations of the open `Ũ`).

* (i) `p ∈ Ũ ∖ W` (Prop 2.1 i), `p̃ ∈ ∂⁻ι(M)`).
* (ii) an open `V ≤ W ⊓ Ũ`, Sbierski's `Ũ_> = {x₀ > f(x)}`, which (2.2) reversed puts in `ι(M)`.
* (iii) `V` future-closed in `Ũ`: `I⁺(x, Ũ) ⊆ I⁺(x, V)` for `x ∈ V`, (2.4) read for the past
  boundary, in relation form (the shape of `T-abs-boundary-chart-cauchy`'s conclusion).
* (iv) the vertical curve `γ̃`, a chronal curve of `Ũ` over `[0, 1]` from `p` into `V`
  (`s ↦ (s, 0)`, `:1059`, reparametrised so that `γ̃ 1 = (ε₀/2, 0)`).
* (v) `s₀ ∈ (0, 1)` with `closure (I⁺(p, Ũ) ∩ I⁻(γ̃ s₀, Ũ))` compact and in `Ũ` (`:1077`, read on
  `≪`: the `I`-diamond lies in the `J_{g̃_w}`-diamond).
* (vi) for every compact `K ⊆ Ũ`, a chronal curve `σ` of `Ũ` over `[0, 1]` from a point off `W`
  through `V ∖ K` into `I⁺(γ̃ 1, Ũ)` (`s ↦ (s, x₀)` with `x₀` off the projection of `K`,
  `:1137–1138`, whose end (4.1) puts in `I⁺((ε₀/2, 0), Ũ)`, `:1062–1072`).

Fields (ii)–(vi) are the layer-3 content of Prop 2.1 and (4.1) for `C⁰` metrics. It is a
structure in `Type`: a `Prop` structure cannot carry the data `V`, `γ̃`, `s₀`. -/
structure PastBoundaryChartData (W Ũ : Opens M) (p : M) where
  /-- (i) `p ∈ Ũ`. -/
  mem : p ∈ Ũ
  /-- (i) `p ∉ W`: a boundary point. -/
  not_mem : p ∉ W
  /-- (ii) the inside `V`, Sbierski's `Ũ_>`. -/
  inside : Opens M
  /-- (ii) `V ≤ W ⊓ Ũ`. -/
  inside_le : inside ≤ W ⊓ Ũ
  /-- (iii) `V` is future-closed in `Ũ`: (2.4) reversed, in relation form. -/
  futureClosed : ∀ x ∈ inside, C.Iplus Ũ {x} ⊆ C.Iplus inside {x}
  /-- (iv) the vertical curve `γ̃`. -/
  curve : ℝ → M
  /-- (iv) `γ̃` is a chronal curve of `Ũ` over `[0, 1]`. -/
  chronalCurveOn : C.ChronalCurveOn Ũ curve 0 1
  /-- (iv) `γ̃ 0 = p`. -/
  curve_zero : curve 0 = p
  /-- (iv) `γ̃ t ∈ V` for `t ∈ (0, 1]`. -/
  curve_mem : ∀ t ∈ Ioc (0 : ℝ) 1, curve t ∈ inside
  /-- (v) the second vertex `γ̃ s₀`. -/
  s₀ : ℝ
  /-- (v) `s₀ ∈ (0, 1)`. -/
  s₀_mem : s₀ ∈ Ioo (0 : ℝ) 1
  /-- (v) the chart diamond at `p` has compact closure … -/
  isCompact_closure : IsCompact (closure (C.Iplus Ũ {p} ∩ C.Iminus Ũ {curve s₀}))
  /-- (v) … in `Ũ`. -/
  closure_subset : closure (C.Iplus Ũ {p} ∩ C.Iminus Ũ {curve s₀}) ⊆ Ũ
  /-- (vi) the avoiding curves. -/
  avoid : ∀ K : Set M, IsCompact K → K ⊆ Ũ → ∃ σ : ℝ → M, C.ChronalCurveOn Ũ σ 0 1 ∧
    σ 0 ∉ W ∧ (∀ t ∈ Ioc (0 : ℝ) 1, σ t ∈ inside ∧ σ t ∉ K) ∧ C.lt Ũ (curve 1) (σ 1)

variable (C) in
/-- **`Ũ` is a past boundary chart of `W` at `p`**: some data `PastBoundaryChartData C W Ũ p`
exist. A programme definition, as `ExitDiamonds` and `IsSpacetimeExtension` were for the `C⁰`
skeleton; whether it is the ETT notion of record is the author's. -/
def PastBoundaryChart (W Ũ : Opens M) (p : M) : Prop := Nonempty (C.PastBoundaryChartData W Ũ p)

variable (C) in
/-- **`Ũ` is a future boundary chart of `W` at `p`** (Sbierski's Prop 2.1 as printed): the past
boundary chart of `C.dual`. Read for `C`: `p ∈ Ũ ∖ W`, `V ≤ W ⊓ Ũ` past-closed in `Ũ`
(`I⁻(x, Ũ) ⊆ I⁻(x, V)`, (2.4) as printed), `γ̃` a past-directed chronal curve of `Ũ` from `p` into
`V`, `closure (I⁻(p, Ũ) ∩ I⁺(γ̃ s₀, Ũ))` compact in `Ũ`, and past-directed avoiding curves. -/
def FutureBoundaryChart (W Ũ : Opens M) (p : M) : Prop := C.dual.PastBoundaryChart W Ũ p

/-! ### Step (a): a curve entering `W` from outside is past-inextensible in `W` -/

/-- **Step (a)** (`:1059–1061`, `:1139–1140`): a chronal curve `c` of an open `Ũ` over `[0, 1]`
starting off `W` and lying in `W` on `(0, s]` is, over `(0, s]`, a past-inextensible chronal curve
of `W`, on a Hausdorff space. It is `ChronalCurveOn.futureInextensible_of_leaving` for `C.dual` and
the reversed curve, with `U = W ⊔ Ũ`, read back by `dual_futureInextensible_Ico_iff`. -/
theorem ChronalCurveOn.pastInextensible_Ioc_of_start_notMem [T2Space M] {c : ℝ → M}
    (hc : C.ChronalCurveOn Ũ c 0 1) {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1)
    (hmem : ∀ t ∈ Ioc (0 : ℝ) s, c t ∈ W) (h0 : c 0 ∉ W) :
    C.PastInextensible W (Ioc 0 s) c ∧
      ∀ a ∈ Ioc (0 : ℝ) s, ∀ b ∈ Ioc (0 : ℝ) s, C.ChronalCurveOn W c a b := by
  have hcs : C.ChronalCurveOn Ũ c 0 s :=
    CurveOn.restrict hc le_rfl hs.2 le_rfl (fun t ht => hc.mem t ⟨ht.1, ht.2.trans hs.2⟩)
  refine ⟨?_, fun a ha b hb => ?_⟩
  · have h1 : C.ChronalCurveOn (W ⊔ Ũ) c (-0) (-(-s)) := by
      rw [neg_zero, neg_neg]
      exact CurveOn.mono_opens C.isRelFamily_lt hcs le_sup_right
    have h2 : C.dual.ChronalCurveOn (W ⊔ Ũ) (fun t => c (-t)) (-s) 0 := CurveOn.neg h1
    have h3 := ChronalCurveOn.futureInextensible_of_leaving (C := C.dual) h2
      (by linarith [hs.1]) le_sup_left
      (fun t ht => hmem (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩) (by simpa using h0)
    have h4 := dual_futureInextensible_Ico_iff.1 h3
    simpa only [neg_neg, neg_zero] using h4
  · rcases le_or_gt a b with hab | hab
    · refine CurveOn.mono_opens C.isRelFamily_lt (CurveOn.restrict hc ha.1.le (hb.2.trans hs.2)
        (inf_le_right : W ⊓ Ũ ≤ Ũ) (fun t ht => ⟨hmem t ⟨ha.1.trans_le ht.1, ht.2.trans hb.2⟩,
          hc.mem t ⟨(ha.1.trans_le ht.1).le, ht.2.trans (hb.2.trans hs.2)⟩⟩)) inf_le_left
    · exact CurveOn.of_lt hab

namespace PastBoundaryChartData

/-- **Step (b), (4.2)'s `⊆`** (`:1108–1109`, Prop 3.1 with Lemma 2.8): for `0 < s < s₀`, the
diamond of `W` from `γ̃ s` to `γ̃ s₀` lies in the chart diamond at `p`. The curve is `γ̃` on
`[s, s₀]` (a chronal curve of `W`, through `V`), the closure hypothesis comes from (v), and the
confinement is `Iplus_inter_Iminus_subset_of_futureOneConnectedOn`. -/
theorem Iplus_inter_Iminus_subset (d : C.PastBoundaryChartData W Ũ p)
    (hcac : C.CausallyArcConnectedOn W) (hfoc : C.FutureOneConnectedOn W) {s : ℝ}
    (hs : s ∈ Ioo 0 d.s₀) :
    C.Iplus W {d.curve s} ∩ C.Iminus W {d.curve d.s₀} ⊆
      C.Iplus Ũ {p} ∩ C.Iminus Ũ {d.curve d.s₀} := by
  have hs₀ := d.s₀_mem
  have hk : 0 < d.s₀ - s := sub_pos.2 hs.2
  -- `γ̃` on `[s, s₀]`, a chronal curve of `W`, affinely reparametrised over `[0, 1]`
  have hseg : C.ChronalCurveOn W d.curve ((d.s₀ - s) * 0 + s) ((d.s₀ - s) * 1 + s) := by
    rw [mul_zero, zero_add, mul_one, sub_add_cancel]
    exact CurveOn.mono_opens C.isRelFamily_lt (CurveOn.restrict d.chronalCurveOn hs.1.le
      hs₀.2.le (d.inside_le.trans inf_le_right)
      (fun t ht => d.curve_mem t ⟨hs.1.trans_le ht.1, ht.2.trans hs₀.2.le⟩))
      (d.inside_le.trans inf_le_left)
  have hc : C.ChronalCurveOn W (fun t => d.curve ((d.s₀ - s) * t + s)) 0 1 :=
    CurveOn.comp_affine hk hseg
  have hx : (fun t => d.curve ((d.s₀ - s) * t + s)) 0 = d.curve s := by simp
  have hy : (fun t => d.curve ((d.s₀ - s) * t + s)) 1 = d.curve d.s₀ := by simp
  have hmaps : MapsTo (fun t => d.curve ((d.s₀ - s) * t + s)) (Icc 0 1) Ũ := fun t ht =>
    d.chronalCurveOn.mem _ ⟨by nlinarith [ht.1, hs.1], by nlinarith [ht.2, hs₀.2]⟩
  -- the closure hypothesis, from (v): `I⁺(γ̃ s, Ũ) ⊆ I⁺(p, Ũ)`
  have hps : C.lt Ũ p (d.curve s) := by
    have := d.chronalCurveOn.lt_of_lt le_rfl hs.1 (hs.2.trans hs₀.2).le
    rwa [d.curve_zero] at this
  have hsub : C.Iplus Ũ {d.curve s} ⊆ C.Iplus Ũ {p} := fun z hz =>
    Precausality.mem_Iplus_singleton.2 (C.lt_trans hps (Precausality.mem_Iplus_singleton.1 hz))
  have hcl : closure (C.Iplus Ũ {d.curve s} ∩ C.Iminus Ũ {d.curve d.s₀}) ⊆ Ũ :=
    (closure_mono (inter_subset_inter_left _ hsub)).trans d.closure_subset
  intro z hz
  obtain ⟨h1, h2⟩ :=
    Iplus_inter_Iminus_subset_of_futureOneConnectedOn hcac hfoc hc hx hy hmaps hcl hz
  exact ⟨hsub h1, h2⟩

/-- **(4.2) as an equality** (`:1077–1109`): `⋃_{0<s<s₀} I⁺(γ̃ s, W) ∩ I⁻(γ̃ s₀, W) =
I⁺(p, Ũ) ∩ I⁻(γ̃ s₀, Ũ)`. `⊆` is step (b); `⊇` is `I⁺(p, Ũ) = ⋃ I⁺(γ̃ s, Ũ)`
(`Iplus_eq_biUnion_Ioc`, over `(0, s₀/2]`) and field (iii) twice. -/
theorem biUnion_Iplus_inter_Iminus_eq (d : C.PastBoundaryChartData W Ũ p)
    (hcac : C.CausallyArcConnectedOn W) (hfoc : C.FutureOneConnectedOn W) :
    ⋃ s ∈ Ioo 0 d.s₀, C.Iplus W {d.curve s} ∩ C.Iminus W {d.curve d.s₀} =
      C.Iplus Ũ {p} ∩ C.Iminus Ũ {d.curve d.s₀} := by
  refine subset_antisymm (iUnion₂_subset fun s hs => d.Iplus_inter_Iminus_subset hcac hfoc hs) ?_
  rintro z ⟨hpz, hzy⟩
  have hs₀ := d.s₀_mem
  -- `I⁺(p, Ũ) = ⋃_{0 < s ≤ s₀/2} I⁺(γ̃ s, Ũ)`, by openness of `I⁺` (`Iplus_eq_biUnion_Ioc`)
  have hhalf : C.ChronalCurveOn Ũ d.curve 0 (d.s₀ / 2) :=
    CurveOn.restrict d.chronalCurveOn le_rfl (by linarith [hs₀.2]) le_rfl
      (fun t ht => d.chronalCurveOn.mem t ⟨ht.1, by linarith [ht.2, hs₀.2]⟩)
  have hU := Iplus_eq_biUnion_Ioc hhalf (by linarith [hs₀.1])
  rw [d.curve_zero] at hU
  rw [hU] at hpz
  obtain ⟨s, hs, hsz⟩ := mem_iUnion₂.1 hpz
  -- (iii) twice: `γ̃ s ≪_V z` and `z ≪_V γ̃ s₀`
  have hsV : d.curve s ∈ d.inside := d.curve_mem s ⟨hs.1, by linarith [hs.2, hs₀.2]⟩
  have hzV' := d.futureClosed _ hsV hsz
  have hzV : z ∈ d.inside := C.lt_mem_right (Precausality.mem_Iplus_singleton.1 hzV')
  have hzy' := d.futureClosed z hzV
    (Precausality.mem_Iplus_singleton.2 (Precausality.mem_Iminus_singleton.1 hzy))
  have hVW : d.inside ≤ W := d.inside_le.trans inf_le_left
  refine mem_iUnion₂.2 ⟨s, ⟨hs.1, by linarith [hs.2, hs₀.1]⟩, ?_, ?_⟩
  · exact Precausality.mem_Iplus_singleton.2
      (C.lt_mono hVW (Precausality.mem_Iplus_singleton.1 hzV'))
  · exact Precausality.mem_Iminus_singleton.2
      (C.lt_mono hVW (Precausality.mem_Iplus_singleton.1 hzy'))

/-- **(4.2) with Prop 3.6's first claim**: under (A), `I⁻(γ̃ s₀, W)` *is* the chart diamond
`I⁺(p, Ũ) ∩ I⁻(γ̃ s₀, Ũ)`: (A) applied to `γ̃` over `(0, s₀/2]` (step (a)) puts every point of `W`
in some `I⁺(γ̃ s, W)` with `s < s₀`. -/
theorem Iminus_eq_diamond [T2Space M] (d : C.PastBoundaryChartData W Ũ p)
    (hcac : C.CausallyArcConnectedOn W) (hfoc : C.FutureOneConnectedOn W)
    (hA : ∀ (I : Set ℝ) (γ : ℝ → M), C.PastInextensible W I γ →
      (∀ a ∈ I, ∀ b ∈ I, C.ChronalCurveOn W γ a b) → ⋃ t ∈ I, C.Iplus W {γ t} = W) :
    C.Iminus W {d.curve d.s₀} = C.Iplus Ũ {p} ∩ C.Iminus Ũ {d.curve d.s₀} := by
  rw [← d.biUnion_Iplus_inter_Iminus_eq hcac hfoc]
  refine subset_antisymm (fun x hx => ?_) (iUnion₂_subset fun s _ => inter_subset_right)
  have hs₀ := d.s₀_mem
  have hhalf : d.s₀ / 2 ∈ Ioc (0 : ℝ) 1 := ⟨by linarith [hs₀.1], by linarith [hs₀.2]⟩
  -- step (a): `γ̃` over `(0, s₀/2]` is a past-inextensible chronal curve of `W`
  obtain ⟨hinex, hchr⟩ := ChronalCurveOn.pastInextensible_Ioc_of_start_notMem d.chronalCurveOn
    hhalf (fun t ht => (d.inside_le (d.curve_mem t ⟨ht.1, ht.2.trans hhalf.2⟩)).1)
    (by rw [d.curve_zero]; exact d.not_mem)
  -- (A): its chronological future is `W`
  have hxW : x ∈ (W : Set M) := Precausality.Iminus_subset_carrier hx
  rw [← hA _ _ hinex hchr] at hxW
  obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.1 hxW
  exact mem_iUnion₂.2 ⟨t, ⟨ht.1, by linarith [ht.2, hs₀.1]⟩, hxt, hx⟩

/-- **(4.3)** (`:1110–1114`): under (A), arc-connectedness and future one-connectedness, a set
inside `I⁻(γ̃ s₀, W)` (Sbierski's slice `{t₀} × S^d`, a Cauchy surface by (B)) lies in the chart
diamond at `p`. Neither (B) nor the Cauchy property is used. -/
theorem subset_diamond [T2Space M] (d : C.PastBoundaryChartData W Ũ p)
    (hcac : C.CausallyArcConnectedOn W) (hfoc : C.FutureOneConnectedOn W)
    (hA : ∀ (I : Set ℝ) (γ : ℝ → M), C.PastInextensible W I γ →
      (∀ a ∈ I, ∀ b ∈ I, C.ChronalCurveOn W γ a b) → ⋃ t ∈ I, C.Iplus W {γ t} = W)
    {S : Set M} (hS : S ⊆ C.Iminus W {d.curve d.s₀}) :
    S ⊆ C.Iplus Ũ {p} ∩ C.Iminus Ũ {d.curve d.s₀} :=
  hS.trans (d.Iminus_eq_diamond hcac hfoc hA).subset

end PastBoundaryChartData

/-! ### The theorem -/

/-- **Sbierski 2312.07443 Thm 1.5, abstract** (§4.1, `:1057–1144`): on a T2, second countable
space, let `W` be an open set, causally arc-connected, future one-connected, with `≤_W`
antisymmetric, such that

* (A) the chronological future in `W` of every past-inextensible chronal curve of `W` is `W`
  (Prop 3.6's first claim, `:729–736`);
* (B) every `I⁻(x, W)` contains a Cauchy surface of `W` (Prop 3.6's second claim, `:737–739`).

Then `W` has a past boundary chart at no point. Proof: (B) gives `S` Cauchy in `I⁻(γ̃ s₀, W)`;
(4.3) puts it in the chart diamond `K`, compact in `Ũ`; field (vi) gives `σ` avoiding `K`,
past-inextensible in `W` (step (a)), with `σ 1 ∈ I⁺(γ̃ s₀, W) ⊆ I⁺(S, W)` (field (iii));
`PastInextensible.exists_mem_of_mem_Iplus` ((2.4)) makes `σ` meet `S ⊆ K`. No instance of
`PastBoundaryChart` is built in this module (see SCOPE); the layer-3 instance
`Causal.minkowski_pastBoundaryChart` makes the theorem non-vacuous. -/
theorem not_pastBoundaryChart_of_flrwType [T2Space M] [SecondCountableTopology M]
    (hcac : C.CausallyArcConnectedOn W) (hfoc : C.FutureOneConnectedOn W)
    (hcaus : ∀ ⦃x y : M⦄, C.le W x y → C.le W y x → x = y)
    (hA : ∀ (I : Set ℝ) (γ : ℝ → M), C.PastInextensible W I γ →
      (∀ a ∈ I, ∀ b ∈ I, C.ChronalCurveOn W γ a b) → ⋃ t ∈ I, C.Iplus W {γ t} = W)
    (hB : ∀ x ∈ W, ∃ S : Set M, C.IsCauchySurfaceOn W S ∧ S ⊆ C.Iminus W {x})
    (Ũ : Opens M) (p : M) : ¬ C.PastBoundaryChart W Ũ p := by
  rintro ⟨d⟩
  have hs₀ := d.s₀_mem
  have hVW : d.inside ≤ W := d.inside_le.trans inf_le_left
  have hyV : d.curve d.s₀ ∈ d.inside := d.curve_mem _ ⟨hs₀.1, hs₀.2.le⟩
  -- (B): a Cauchy surface `S` of `W` in `I⁻(γ̃ s₀, W)`; by (4.3) it lies in the chart diamond
  obtain ⟨S, hS, hSy⟩ := hB _ (hVW hyV)
  have hSK : S ⊆ closure (C.Iplus Ũ {p} ∩ C.Iminus Ũ {d.curve d.s₀}) :=
    (d.subset_diamond hcac hfoc hA hSy).trans subset_closure
  -- (vi): a curve `σ` avoiding that compact set
  obtain ⟨σ, hσ, hσ0, hσmem, hσ1⟩ := d.avoid _ d.isCompact_closure d.closure_subset
  -- step (d): `σ` is past-inextensible in `W` over `(0, 1]` …
  have hσinex : C.PastInextensible W (Ioc 0 1) σ :=
    (ChronalCurveOn.pastInextensible_Ioc_of_start_notMem hσ ⟨zero_lt_one, le_rfl⟩
      (fun t ht => hVW (hσmem t ht).1) hσ0).1
  -- … `S` is non-empty, since `W` has an inextensible causal curve …
  obtain ⟨x₀, hx₀⟩ : S.Nonempty := by
    obtain ⟨J, Z, hZ, -⟩ := exists_inextensible_of_t1_secondCountable hσinex.1
    obtain ⟨x, ⟨-, hxS⟩, -⟩ := hS J Z hZ
    exact ⟨x, hxS⟩
  -- … and `σ 1 ∈ I⁺(S, W)`: `γ̃ s₀ ≪_Ũ γ̃ 1 ≪_Ũ σ 1`, and (iii) at `γ̃ s₀`
  have hy1 : C.lt W (d.curve d.s₀) (σ 1) := by
    have h1 : C.lt Ũ (d.curve d.s₀) (σ 1) :=
      C.lt_trans (d.chronalCurveOn.lt_of_lt hs₀.1.le hs₀.2 le_rfl) hσ1
    exact C.lt_mono hVW (Precausality.mem_Iplus_singleton.1
      (d.futureClosed _ hyV (Precausality.mem_Iplus_singleton.2 h1)))
  have hx₀y : C.lt W x₀ (d.curve d.s₀) := Precausality.mem_Iminus_singleton.1 (hSy hx₀)
  -- step (e): `σ` meets `S` (2.4), inside the compact set it avoids
  obtain ⟨t, ht, htS⟩ := hσinex.exists_mem_of_mem_Iplus hS hcac hcaus
    ⟨1, ⟨zero_lt_one, le_rfl⟩, x₀, hx₀, C.lt_trans hx₀y hy1⟩
  exact (hσmem t ht).2 (hSK htS)

/-- **The time reversal**: no future boundary chart, under (A) for future-inextensible curves
and their chronological pasts, and (B) with `S ⊆ I⁺(x, W)`. It is the theorem for `C.dual`. -/
theorem not_futureBoundaryChart_of_flrwType [T2Space M] [SecondCountableTopology M]
    (hcac : C.CausallyArcConnectedOn W) (hfoc : C.FutureOneConnectedOn W)
    (hcaus : ∀ ⦃x y : M⦄, C.le W x y → C.le W y x → x = y)
    (hA : ∀ (I : Set ℝ) (γ : ℝ → M), C.FutureInextensible W I γ →
      (∀ a ∈ I, ∀ b ∈ I, C.ChronalCurveOn W γ a b) → ⋃ t ∈ I, C.Iminus W {γ t} = W)
    (hB : ∀ x ∈ W, ∃ S : Set M, C.IsCauchySurfaceOn W S ∧ S ⊆ C.Iplus W {x})
    (Ũ : Opens M) (p : M) : ¬ C.FutureBoundaryChart W Ũ p := by
  refine not_pastBoundaryChart_of_flrwType (C := C.dual) (dual_causallyArcConnectedOn.2 hcac)
    (dual_futureOneConnectedOn.2 hfoc) (fun x y h1 h2 => hcaus h2 h1) ?_ ?_ Ũ p
  · intro I γ hγ hchr
    have h1 : C.FutureInextensible W (-I) (fun t => γ (-t)) := by
      have := (dual_pastInextensible_iff (C := C) (W := W) (I := -I) (c := fun t => γ (-t))).1
      simp only [neg_neg] at this
      exact this hγ
    have h2 : ∀ a ∈ -I, ∀ b ∈ -I, C.ChronalCurveOn W (fun t => γ (-t)) a b := fun a ha b hb =>
      CurveOn.neg (hchr (-b) hb (-a) ha)
    rw [← hA (-I) _ h1 h2]
    ext x
    simp only [mem_iUnion, exists_prop, Set.mem_neg]
    constructor
    · rintro ⟨t, ht, hx⟩
      exact ⟨-t, by rwa [neg_neg], by rw [neg_neg]; exact hx⟩
    · rintro ⟨t, ht, hx⟩
      exact ⟨-t, ht, hx⟩
  · intro x hx
    obtain ⟨S, hS, hSx⟩ := hB x hx
    exact ⟨S, dual_isCauchySurfaceOn.2 hS, hSx⟩

end Causality

/-! ### The corollary for an extension -/

open Causality

namespace IsSpacetimeExtension

variable {N : Type v} [TopologicalSpace N] [Nonempty N] {CN : Causality N} {C : Causality M}
  {ι : N → M}

/-- **Cauchy surfaces are pushed forward**: `ι(S)` is a Cauchy surface of `ι(N)` for every Cauchy
surface `S` of `N` (`IsEMorphismOn.isCauchySurfaceOn_image_iff`). -/
theorem isCauchySurfaceOn_image (hι : IsSpacetimeExtension CN C ι) {S : Set N}
    (hS : CN.IsCauchySurface S) : C.IsCauchySurfaceOn hι.rangeOpens (ι '' S) :=
  (hι.isEMorphismOn.isCauchySurfaceOn_image_iff hι.isOpenEmbedding.injective.injOn le_rfl
    (by rw [coe_rangeOpens, Opens.coe_top, image_univ]) (fun _ _ => trivial)).1 hS

/-- **Antisymmetry is transported**: `N` causal makes `≤_{ι(N)}` antisymmetric (`rel_top_iff`). -/
theorem le_antisymm_rangeOpens (hι : IsSpacetimeExtension CN C ι) (hcaus : CN.IsCausal) :
    ∀ ⦃x y : M⦄, C.le hι.rangeOpens x y → C.le hι.rangeOpens y x → x = y := by
  intro x y hxy hyx
  obtain ⟨x', rfl⟩ : x ∈ range ι := C.le_mem_left hxy
  obtain ⟨y', rfl⟩ : y ∈ range ι := C.le_mem_right hxy
  rw [hcaus ((hι.rel_top_iff x' y').1.2 hxy) ((hι.rel_top_iff y' x').1.2 hyx)]

/-- **(A) is transported**: if every past-inextensible chronal curve of `N` has chronological
future `N`, every past-inextensible chronal curve of `ι(N)` has chronological future `ι(N)`. The
curve is read in `N` through `ι⁻¹` (`pastInextensible_invComp`,
`ChartIso.chronalCurveOn_symm_image`) and the relations back through `rel_top_iff`. -/
theorem iUnion_Iplus_eq_of_pastInextensible (hι : IsSpacetimeExtension CN C ι)
    (hA : ∀ (I : Set ℝ) (δ : ℝ → N), CN.PastInextensible ⊤ I δ →
      (∀ a ∈ I, ∀ b ∈ I, CN.ChronalCurveOn ⊤ δ a b) → ⋃ t ∈ I, CN.Iplus ⊤ {δ t} = univ) :
    ∀ (I : Set ℝ) (γ : ℝ → M), C.PastInextensible hι.rangeOpens I γ →
      (∀ a ∈ I, ∀ b ∈ I, C.ChronalCurveOn hι.rangeOpens γ a b) →
      ⋃ t ∈ I, C.Iplus hι.rangeOpens {γ t} = hι.rangeOpens := by
  intro I γ hγ hchr
  have hg : LeftInvOn (hι.isOpenEmbedding.toOpenPartialHomeomorph ι).symm ι
      ((⊤ : Opens N) : Set N) := fun _ _ =>
    IsOpenEmbedding.toOpenPartialHomeomorph_left_inv _ hι.isOpenEmbedding
  have hU : (hι.rangeOpens : Set M) = ι '' ((⊤ : Opens N) : Set N) := by
    rw [coe_rangeOpens, Opens.coe_top, image_univ]
  -- `δ = ι⁻¹ ∘ γ` is a past-inextensible chronal curve of `N`
  have hδ := hι.isEMorphismOn.pastInextensible_invComp hι.isOpenEmbedding.injective.injOn hg
    le_rfl hU hγ
  have hδc : ∀ a ∈ I, ∀ b ∈ I,
      CN.ChronalCurveOn ⊤ ((hι.isOpenEmbedding.toOpenPartialHomeomorph ι).symm ∘ γ) a b :=
    fun a ha b hb => ChartIso.chronalCurveOn_symm_image hι.chartIso (hι.le_chartSource ⊤)
      (by rw [hι.chartImage_top]; exact hchr a ha b hb)
  have huniv := hA I _ hδ hδc
  ext x
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨t, -, hxt⟩ := mem_iUnion₂.1 hx
    exact Precausality.Iplus_subset_carrier hxt
  · obtain ⟨y, rfl⟩ : x ∈ range ι := hx
    have hy : y ∈ ⋃ t ∈ I,
        CN.Iplus ⊤ {((hι.isOpenEmbedding.toOpenPartialHomeomorph ι).symm ∘ γ) t} :=
      huniv ▸ mem_univ y
    obtain ⟨t, ht, hyt⟩ := mem_iUnion₂.1 hy
    have h1 := (hι.rel_top_iff _ y).2.1 (Precausality.mem_Iplus_singleton.1 hyt)
    have h2 : ι (((hι.isOpenEmbedding.toOpenPartialHomeomorph ι).symm ∘ γ) t) = γ t :=
      IsOpenEmbedding.toOpenPartialHomeomorph_right_inv _ _ (hγ.1.mem ht)
    rw [h2] at h1
    exact mem_iUnion₂.2 ⟨t, ht, Precausality.mem_Iplus_singleton.2 h1⟩

/-- **(B) is transported**: if every `I⁻(x, N)` contains a Cauchy surface of `N`, every
`I⁻(x, ι(N))` contains a Cauchy surface of `ι(N)`, its image. -/
theorem exists_isCauchySurfaceOn_subset_Iminus (hι : IsSpacetimeExtension CN C ι)
    (hB : ∀ x : N, ∃ S : Set N, CN.IsCauchySurface S ∧ S ⊆ CN.Iminus ⊤ {x}) :
    ∀ x ∈ hι.rangeOpens, ∃ S : Set M, C.IsCauchySurfaceOn hι.rangeOpens S ∧
      S ⊆ C.Iminus hι.rangeOpens {x} := by
  intro x hx
  obtain ⟨y, rfl⟩ : x ∈ range ι := hx
  obtain ⟨S, hS, hSy⟩ := hB y
  refine ⟨ι '' S, hι.isCauchySurfaceOn_image hS, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact Precausality.mem_Iminus_singleton.2
    ((hι.rel_top_iff z y).2.1 (Precausality.mem_Iminus_singleton.1 (hSy hz)))

/-- **The corollary for an extension** (the target's deliverable (iv)): `ι : N → M` an
`IsSpacetimeExtension` (OQ-154's reading of an extension, recorded, not decided), `M` T2 and second
countable, `N` causally arc-connected, future one-connected and causal, with (A) and (B) on `N`.
Then `ι(N)` has a past boundary chart at no point of `M`: Sbierski's `∂⁻ι(M) = ∅`, abstractly. -/
theorem not_pastBoundaryChart_of_flrwType [T2Space M] [SecondCountableTopology M]
    (hι : IsSpacetimeExtension CN C ι) (hcac : CN.CausallyArcConnected)
    (hfoc : CN.FutureOneConnected) (hcaus : CN.IsCausal)
    (hA : ∀ (I : Set ℝ) (δ : ℝ → N), CN.PastInextensible ⊤ I δ →
      (∀ a ∈ I, ∀ b ∈ I, CN.ChronalCurveOn ⊤ δ a b) → ⋃ t ∈ I, CN.Iplus ⊤ {δ t} = univ)
    (hB : ∀ x : N, ∃ S : Set N, CN.IsCauchySurface S ∧ S ⊆ CN.Iminus ⊤ {x})
    (Ũ : Opens M) (p : M) : ¬ C.PastBoundaryChart hι.rangeOpens Ũ p :=
  Causality.not_pastBoundaryChart_of_flrwType (hι.causallyArcConnectedOn hcac)
    (hι.futureOneConnectedOn hfoc) (hι.le_antisymm_rangeOpens hcaus)
    (hι.iUnion_Iplus_eq_of_pastInextensible hA) (hι.exists_isCauchySurfaceOn_subset_Iminus hB) Ũ p

end IsSpacetimeExtension

/-! ### Witnesses on the timelike line -/

/-- The open half-line `(0, ∞)` of the timelike line, the witness's `W`. -/
def posHalfLine : Opens ℝ := ⟨Ioi 0, isOpen_Ioi⟩

/-- **One dimension leaves no room for field (vi)**: on the timelike line no open set has a past
boundary chart at any point. With `K = [p, γ̃ 1]`, the curve `σ` of (vi) cannot cross `γ̃ 1`, so
`σ 0 > γ̃ 1`, and (iii) puts `σ 0` in `V ⊆ W`. -/
theorem timelikeLine_not_pastBoundaryChart (W Ũ : Opens ℝ) (p : ℝ) :
    ¬ timelikeLine.PastBoundaryChart W Ũ p := by
  rintro ⟨d⟩
  have h1 : timelikeLine.lt Ũ p (d.curve 1) := by
    have := d.chronalCurveOn.lt_of_lt le_rfl zero_lt_one le_rfl
    rwa [d.curve_zero] at this
  rw [timelikeLine_lt] at h1
  -- (vi) at `K = [p, γ̃ 1]`
  obtain ⟨σ, hσ, hσ0, hσmem, hσ1⟩ := d.avoid (Icc p (d.curve 1)) isCompact_Icc h1.2
  have hσ01 := hσ.lt_of_lt le_rfl zero_lt_one le_rfl
  rw [timelikeLine_lt] at hσ01 hσ1
  have hV1 : d.curve 1 ∈ d.inside := d.curve_mem 1 ⟨zero_lt_one, le_rfl⟩
  rcases le_or_gt (σ 0) (d.curve 1) with hle | hlt
  · -- `σ` passes through `γ̃ 1`: at `0` it would be in `V ⊆ W`, later in `K`
    have hcont := CurveOn.continuousOn timelikeLine.isRelFamily_lt hσ
    obtain ⟨t, ht, hσt⟩ := intermediate_value_Icc zero_le_one hcont ⟨hle, hσ1.1.le⟩
    rcases ht.1.eq_or_lt with h0 | h0
    · subst h0
      have : σ 0 ∈ d.inside := by rw [hσt]; exact hV1
      exact hσ0 (d.inside_le this).1
    · exact (hσmem t ⟨h0, ht.2⟩).2 (by rw [hσt]; exact ⟨h1.1.le, le_rfl⟩)
  · -- `σ 0` above `γ̃ 1` in `Ũ`: (iii) puts it in `V ⊆ W`
    have hlt' : timelikeLine.lt Ũ (d.curve 1) (σ 0) :=
      timelikeLine_lt.2 ⟨hlt, (Icc_subset_Icc_right hσ01.1.le).trans hσ1.2⟩
    have := d.futureClosed _ hV1 (Precausality.mem_Iplus_singleton.2 hlt')
    exact hσ0 (d.inside_le
      (timelikeLine.lt_mem_right (Precausality.mem_Iplus_singleton.1 this))).1

/-- **(A) on the timelike line**: every past-inextensible causal curve of `ℝ` has chronological
future `ℝ`; below any `x` it meets the Cauchy surface `{x - 1}` ((2.4)). -/
theorem timelikeLine_iUnion_Iplus_eq_univ (I : Set ℝ) (δ : ℝ → ℝ)
    (hδ : timelikeLine.PastInextensible ⊤ I δ) : ⋃ t ∈ I, timelikeLine.Iplus ⊤ {δ t} = univ := by
  refine eq_univ_of_forall fun x => ?_
  obtain ⟨t₁, ht₁⟩ := hδ.1.nonempty
  rcases lt_or_ge (δ t₁) x with h | h
  · exact mem_iUnion₂.2 ⟨t₁, ht₁, Precausality.mem_Iplus_singleton.2
      (timelikeLine_lt.2 ⟨h, fun _ _ => trivial⟩)⟩
  · -- `δ t₁ ∈ J⁺({x - 1})`, so `δ` meets the Cauchy surface `{x - 1}` (2.4)
    obtain ⟨t, ht, htS⟩ := hδ.exists_mem_of_mem_Jplus
      (timelikeLine_isCauchySurface_singleton (x - 1)) timelikeLine_causallyArcConnected
      timelikeLine_isCausal
      ⟨t₁, ht₁, x - 1, rfl, timelikeLine_le.2 ⟨by linarith, fun _ _ => trivial⟩⟩
    refine mem_iUnion₂.2 ⟨t, ht, Precausality.mem_Iplus_singleton.2 ?_⟩
    rw [mem_singleton_iff.1 htS]
    exact timelikeLine_lt.2 ⟨by linarith, fun _ _ => trivial⟩

/-- **(B) on the timelike line**: `{x - 1}` is a Cauchy surface of `ℝ` inside `I⁻(x)`. -/
theorem timelikeLine_exists_cauchy_Iminus (x : ℝ) :
    ∃ S : Set ℝ, timelikeLine.IsCauchySurface S ∧ S ⊆ timelikeLine.Iminus ⊤ {x} :=
  ⟨{x - 1}, timelikeLine_isCauchySurface_singleton _, singleton_subset_iff.2
    (Precausality.mem_Iminus_singleton.2 (timelikeLine_lt.2 ⟨by linarith, fun _ _ => trivial⟩))⟩

/-- The image of `exp_isSpacetimeExtension` is `(0, ∞)`. -/
theorem exp_rangeOpens_eq : exp_isSpacetimeExtension.rangeOpens = posHalfLine :=
  SetLike.coe_injective (by rw [IsSpacetimeExtension.coe_rangeOpens]; exact Real.range_exp)

/-- **The corollary on a witness**: `exp : ℝ → ℝ`, an extension of the timelike line into itself
onto `(0, ∞)`, satisfies every hypothesis of
`IsSpacetimeExtension.not_pastBoundaryChart_of_flrwType`; its image has no past boundary chart. -/
theorem timelikeLine_exp_not_pastBoundaryChart (Ũ : Opens ℝ) (p : ℝ) :
    ¬ timelikeLine.PastBoundaryChart exp_isSpacetimeExtension.rangeOpens Ũ p :=
  exp_isSpacetimeExtension.not_pastBoundaryChart_of_flrwType timelikeLine_causallyArcConnected
    timelikeLine_futureOneConnected timelikeLine_isCausal
    (fun I δ hδ _ => timelikeLine_iUnion_Iplus_eq_univ I δ hδ) timelikeLine_exists_cauchy_Iminus
    Ũ p

/-- **The hypotheses hold jointly** on `W = (0, ∞)` of the timelike line: causal
arc-connectedness, future one-connectedness, antisymmetry, (A) and (B), transported from `ℝ`
through `exp`. -/
theorem timelikeLine_flrwType_hypotheses_posHalfLine :
    timelikeLine.CausallyArcConnectedOn posHalfLine ∧
      timelikeLine.FutureOneConnectedOn posHalfLine ∧
      (∀ ⦃x y : ℝ⦄, timelikeLine.le posHalfLine x y → timelikeLine.le posHalfLine y x → x = y) ∧
      (∀ (I : Set ℝ) (γ : ℝ → ℝ), timelikeLine.PastInextensible posHalfLine I γ →
        (∀ a ∈ I, ∀ b ∈ I, timelikeLine.ChronalCurveOn posHalfLine γ a b) →
        ⋃ t ∈ I, timelikeLine.Iplus posHalfLine {γ t} = posHalfLine) ∧
      (∀ x ∈ posHalfLine, ∃ S : Set ℝ, timelikeLine.IsCauchySurfaceOn posHalfLine S ∧
        S ⊆ timelikeLine.Iminus posHalfLine {x}) := by
  rw [← exp_rangeOpens_eq]
  exact ⟨exp_isSpacetimeExtension.causallyArcConnectedOn timelikeLine_causallyArcConnected,
    timelikeLine_futureOneConnectedOn _,
    exp_isSpacetimeExtension.le_antisymm_rangeOpens timelikeLine_isCausal,
    exp_isSpacetimeExtension.iUnion_Iplus_eq_of_pastInextensible
      (fun I δ hδ _ => timelikeLine_iUnion_Iplus_eq_univ I δ hδ),
    exp_isSpacetimeExtension.exists_isCauchySurfaceOn_subset_Iminus
      timelikeLine_exists_cauchy_Iminus⟩

/-- **The theorem applied** on `W = (0, ∞)`: `0 ∉ W` (the past boundary point Sbierski's argument
starts from) and no `Ũ` is a past boundary chart of `W` at any point, by
`not_pastBoundaryChart_of_flrwType` (not by `timelikeLine_not_pastBoundaryChart`). -/
theorem timelikeLine_posHalfLine_not_pastBoundaryChart (Ũ : Opens ℝ) (p : ℝ) :
    (0 : ℝ) ∉ posHalfLine ∧ ¬ timelikeLine.PastBoundaryChart posHalfLine Ũ p := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := timelikeLine_flrwType_hypotheses_posHalfLine
  exact ⟨lt_irrefl (0 : ℝ), not_pastBoundaryChart_of_flrwType h1 h2 h3 h4 h5 Ũ p⟩

end Causal
