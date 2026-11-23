import Causal.ChronalNeighbourBridge
import Causal.Inextensible
import Causal.LinesCurves
import Causal.LineDevelopment

/-!
# Sbierski 1507.00601 §2's causal lemmas in ETT: pasts along a curve, leaving, separation

Programme target `T-abs-schw-causal-lemmas` (`programme/roadmap.toml`; layer 1, stream abstract,
ETT-layer imports only, no model, no metric). Source: J. Sbierski, *The C⁰-inextendibility of the
Schwarzschild spacetime and the spacelike diameter in Lorentzian geometry*, arXiv 1507.00601 v2,
`papers/sbierski-schwarzschild/legacy/labeled/InexSchwarzschild2.tex`. **No label is marked**: each
row is a statement about `C⁰` Lorentzian manifolds, and what is here is its ETT argument for any
causality (layer 1); the rows need the `C⁰` model's layer 3 to become the paper's statements.

* `schwprop:UnionPasts` — `InexSchwarzschild2.tex:310` (proof 318–320): `schw_prop_2_7`
  (`I⁻_W(γ 1) = ⋃_{0 ≤ s < 1} I⁻_W(γ s)` for a future chronal curve `γ` of any open `W` over
  `[0, 1]`), over any `[a, b]`, `a < b`: `Iminus_eq_biUnion_Ico`; the time-reversed form
  `Iplus_eq_biUnion_Ioc`. No hypothesis beyond the curve.
* `schwdef:timelike_separated_set` — `InexSchwarzschild2.tex:390` (and the sentence after it,
  `:393`): `ChronallySeparatedOn W K A B` (every future or past chronal curve of `W` over `[0, 1]`
  from `A` to `B` meets `K`), `ChronallySeparated`; the reformulation for `K` closed,
  `schw_def_2_14_iff` (`W = M`), `chronallySeparatedOn_iff_of_isClosed` (any open `W`),
  `chronallySeparatedOn_iff_of_coe_eq` (any open `V = W ∖ K`); its `⇐` needs nothing
  (`chronallySeparatedOn_of_Iplus_Iminus`), its `⇒` causal arc-connectedness of `W ∖ K`
  (`Iplus_Iminus_of_chronallySeparatedOn`), which cannot be dropped
  (`allRelated_chronallySeparated_not_iff`).
* The inextensibility step of `schwthm:MinkInex` (`InexSchwarzschild2.tex:485`, Thm 3.1 Step 1:
  "and hence it is future inextendible in M_Mink") and of `schwthm:MainThm` (`:798`, the proof of
  Thm 4.9): `exists_leaving_futureInextensible_of_isOpenEmbedding` (Lemma 2.17's curve, for `D = C`
  or `C.dual`, is a future-inextensible causal curve of the open `ι(N)` over `[0, 1)`, `M`
  Hausdorff), through `futureInextensible_of_leaving` (any causal curve of `M` over `[a, b]` lying
  in an open `W` on `[a, b)` with `γ b ∉ W`) and the separation-free core
  `futureInextensible_of_forall_not_tendsto` (no limit in `W` at the supremum of the parameter).
  Sbierski's own notion (Def 2.10, a continuous extension): `not_continuousExtension_of_tendsto`
  (in `W`), `not_continuousExtension_preimage` (in `N`, of `ι⁻¹ ∘ γ`, the paper's literal
  sentence), and Sbierski's notion implies ETT's, `futureInextensible_of_not_continuousExtension`.

> Proposition 2.7. Let (M, g) be a Lorentzian manifold with a continuous metric g. Let
> γ : [0,1] → M be a future directed timelike curve. Then the following holds:
> I⁻(γ(1), M) = ⋃_{0 ≤ s < 1} I⁻(γ(s), M).
> Proof. The inclusion "⊇" is clear. In order to prove "⊆", let q ∈ I⁻(γ(1), M). Hence, it
> follows that γ(1) ∈ I⁺(q, M). By Proposition 2.6, I⁺(q, M) is open and thus contains γ(s) for s
> close enough to 1. (`InexSchwarzschild2.tex:310–320`)

> Definition 2.14. Given two sets A, B ⊆ M, we say that A and B are timelike separated by a set
> K ⊆ M if, and only if, every timelike curve connecting A and B intersects K - i.e., for any
> timelike curve σ : [0,1] → M with σ(0) ∈ A and σ(1) ∈ B there exists an s₀ ∈ [0,1] with
> σ(s₀) ∈ K. If K is a closed set, then M ∖ K is again a Lorentzian manifold. In this case, we
> clearly have that A and B are timelike seperated by K if, and only if, I⁺(A, M ∖ K) ∩ B = ∅ and
> I⁻(A, M ∖ K) ∩ B = ∅. (`InexSchwarzschild2.tex:390–393`)

> By Lemma 2.17, we can then find a timelike curve γ̃ : [−1, 0] → M̃ such that
> γ := ι⁻¹ ∘ γ̃|[−1,0) : [−1, 0) → M_Mink is a timelike curve in M_Mink and γ̃(0) ∈ M̃ ∖ ι(M_Mink).
> Without loss of generality we can assume that γ is future directed (otherwise reverse the time
> orientation), and hence it is future inextendible in M_Mink. (`InexSchwarzschild2.tex:485`; the
> same sentence for M_max at `:798`)
-/

/-!
## The reading

* **Timelike curves are chronal curves of `C` or of `C.dual`** (`Causal.Curves`). Sbierski's
  timelike curve (Def 2.1, `:235`) keeps its one-sided tangents in one cone, so in a time-oriented
  `M` it is future or past directed (Def 2.2, `:241`: "at some point of `I` (and hence at all
  points of `I`)"); a past directed one is a future chronal curve of the time reversal `C.dual`.
  Def 2.14 says "timelike curve" with no direction: `ChronallySeparatedOn` quantifies over both.
* **`I^±(A, M ∖ K)` is `C.Iplus V A`, `C.Iminus V A` for the open `V = W ∖ K`**: ETT's relations
  are indexed by the open sets (Rem 2.3, `:248`), and Sbierski's `≪` is defined by curves; the two
  agree on `V` when `V` is causally arc-connected (the binder's rows of Defs 2.1, 2.2), which is the
  hypothesis of the `⇒` and the target's `uses` (`causally_arc_connected`).
* **"Future inextendible in M"** is ETT's `FutureInextensible` (DEC-11, DEC-13: no strict causal
  extension at the future end), stated in the open `W = ι(N)` of `M̃` with the relations of `C` at
  the open subsets of `W` (kb/0001; Rem 2.3: `ι(N)` is a spacetime in its own right). Sbierski's
  Def 2.10 (a *continuous* extension to `I ∪ {b}`) is also given, in `W` and in `N`; it implies
  ETT's (`futureInextensible_of_not_continuousExtension`; the converse is Rem 2.11's failure).
* **The direction of the leaving curve**: Lemma 2.17 gives a curve of `C` or of `C.dual`
  (`exists_leaving_of_isOpenEmbedding`); Sbierski's "otherwise reverse the time orientation" is
  `D = C.dual`, and the conclusion is `D.FutureInextensible`; for `D = C.dual` it is
  `C.PastInextensible` of the reversed curve (`dual_futureInextensible_Ico_iff`).
* **The binder's readings R2 (Cauchy hypersurfaces, OQ-114) and R3 (time-orientability of `M̃`,
  OQ-115) are not decided here**: no statement mentions a Cauchy surface; every statement is about
  one causality `C` on `M̃`, i.e. a time-oriented `M̃`, and its time reversal `C.dual`, which is
  what any reading of OQ-115 gives once a time orientation (or the double cover) is chosen.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| Prop 2.7: `(M, g)` continuous metric; `γ` future directed timelike over `[0, 1]` | ⚠ weakened: any causality (a continuous metric's is one, the C⁰ layer 3); ✓ carried: `C.ChronalCurveOn W γ 0 1`, any open `W` (`W = ⊤` is `M`) |
| Prop 2.7: Prop 2.6 (`I⁺(q)` open) | ✓ free: an axiom of an ETT causality (`isOpen_lt_right`) |
| Def 2.14: `A, B, K ⊆ M`; timelike curves over `[0, 1]` | ✓ carried: chronal curves of `C` or `C.dual` over `[0, 1]` in the open `W` |
| reformulation: `K` closed | ✓ carried (`schw_def_2_14_iff`); ⚠ weakened in `chronallySeparatedOn_iff_of_coe_eq`: only `W ∖ K` open |
| reformulation: `≪` of `M ∖ K` realised by timelike curves (Def 2.2) | ✓ carried, `⇒` only: `C.CausallyArcConnectedOn (W ∖ K)`; `⇐` needs none |
| Thm 3.1 Step 1: `M̃` a manifold (Hausdorff, `:228`), `ι` an isometric embedding, `ι(M)` proper | ✓ carried: `[T2Space M]`, used and needed (`forkPoint_leaving_futureExtensible`); ⚠ weakened: `ι` an open embedding (only `ι(N)` open is used, as in `exists_leaving_of_isOpenEmbedding`); `not_continuousExtension_preimage` asks `ι` continuous only |
| Thm 3.1 Step 1: the curve future directed timelike | ⚠ weakened in `futureInextensible_of_leaving`: a future causal curve of any open `U ≥ W` |
| Lemma 2.17's hypotheses (connected `M̃`, chronal neighbours at `∂ι(M)`) | ✓ carried as in `exists_leaving_of_isOpenEmbedding` (Causal/LocateExtension.lean:418); ⚠ strengthened: `C.CausallyArcConnected` and `[Nonempty N]`, which that theorem asks |

## SCOPE (disclosed)

* Nothing is marked (the convention of the external Sbierski rows, `certificate/curation.toml`):
  the ETT argument is proved for every causality, the `C⁰` layer 3 (that Sbierski's curve relation
  is a causally arc-connected ETT causality whose chronal curves include his timelike curves) is
  `T-loc-c0-metric-causality`'s.
* The leaving curve's inextensibility is stated in the open `ι(N) ⊆ M̃`, not in `N`: a causality on
  `N` transported by `ι` (Rem 2.3, `Causal.ChartIso`) is `T-abs-c0-extension-skeleton`'s. In `N`,
  Sbierski's own continuous notion is proved (`not_continuousExtension_preimage`), for any
  continuous `ι`.
* Witnesses (kb/0011): on the timelike line, `{0}` and `{2}` are separated by `{1}` and not by `∅`
  (`timelikeLine_chronallySeparated`, `timelikeLine_not_chronallySeparated_empty`), and Lemma 2.17's
  hypotheses hold for `ι : (0, ∞) ↪ ℝ` (`timelikeLine_exists_leaving_futureInextensible`), with
  the explicit curve `t ↦ 1 - t` of the reversed line (`timelikeLine_dual_futureInextensible`).
  `allRelated ℝ` (every continuous map chronal) shows the `⇒` of the reformulation needs
  arc-connectedness. The three-point non-Hausdorff space `ForkPoint` (with `allRelated`) shows
  `[T2Space M]` cannot be dropped from `futureInextensible_of_leaving`
  (`forkPoint_leaving_futureExtensible`; hence `forkPoint_not_t2Space`).
* `futureInextensible_of_forall_not_tendsto` is the bounded case of the argument of
  `futureInextensible_of_isLUB_notMem` (`Causal/InextensiblePiece.lean:86`), freed of its time
  function, of the openness of `I`, of the continuity of `c` on `ℝ` and of the Hausdorff axiom.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Function

universe u v

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable {C : Causality M} {W : Opens M} {γ : ℝ → M} {a b : ℝ}

/-! ### Proposition 2.7: the past of the endpoint is the union of the pasts along the curve -/

/-- **Sbierski Prop 2.7, over any segment**: along a future chronal curve of the open `W` over
`[a, b]`, `a < b`, the chronological past in `W` of the endpoint is the union of those of the
points before it. `⊇` is `lt_of_lt` and transitivity, `⊆` the openness of `I⁺_W(q)` (an axiom)
and the continuity of the curve at `b`. -/
theorem Iminus_eq_biUnion_Ico (hγ : C.ChronalCurveOn W γ a b) (hab : a < b) :
    C.Iminus W {γ b} = ⋃ s ∈ Ico a b, C.Iminus W {γ s} := by
  ext q
  simp only [mem_iUnion, Precausality.mem_Iminus_singleton, exists_prop]
  constructor
  · intro hq
    have hO : IsOpen {y | C.lt W q y} := C.isOpen_lt_right W q
    have hcont : ContinuousWithinAt γ (Icc a b) b :=
      CurveOn.continuousOn C.isRelFamily_lt hγ b (right_mem_Icc.2 hab.le)
    have hev : ∀ᶠ s in 𝓝[Ico a b] b, γ s ∈ {y | C.lt W q y} :=
      (hcont.mono Ico_subset_Icc_self).tendsto.eventually (hO.mem_nhds hq)
    haveI : (𝓝[Ico a b] b).NeBot := right_nhdsWithin_Ico_neBot hab
    obtain ⟨s, hs, hqs⟩ := (hev.and self_mem_nhdsWithin).exists
    exact ⟨s, hqs, hs⟩
  · rintro ⟨s, hs, hqs⟩
    exact C.lt_trans hqs (hγ.lt_of_lt hs.1 hs.2 le_rfl)

/-- **Sbierski 1507.00601 Prop 2.7 in ETT**: for a future chronal curve `γ` of the open `W` over
`[0, 1]`, `I⁻_W(γ(1)) = ⋃_{0 ≤ s < 1} I⁻_W(γ(s))`. -/
theorem schw_prop_2_7 (hγ : C.ChronalCurveOn W γ 0 1) :
    C.Iminus W {γ 1} = ⋃ s ∈ Ico (0 : ℝ) 1, C.Iminus W {γ s} :=
  Iminus_eq_biUnion_Ico hγ zero_lt_one

/-- **Prop 2.7, time-reversed**: the chronological future in `W` of the starting point is the union
of those of the points after it. -/
theorem Iplus_eq_biUnion_Ioc (hγ : C.ChronalCurveOn W γ a b) (hab : a < b) :
    C.Iplus W {γ a} = ⋃ s ∈ Ioc a b, C.Iplus W {γ s} := by
  have hrev : C.dual.ChronalCurveOn W (fun t => γ (a + b - t)) a b := CurveOn.reverse hγ
  have h := Iminus_eq_biUnion_Ico hrev hab
  have hb : a + b - b = a := by ring
  simp only [hb] at h
  change C.Iplus W {γ a} = ⋃ s ∈ Ico a b, C.Iplus W {γ (a + b - s)} at h
  rw [h]
  ext q
  simp only [mem_iUnion, exists_prop]
  constructor
  · rintro ⟨s, hs, hq⟩
    exact ⟨a + b - s, ⟨by linarith [hs.2], by linarith [hs.1]⟩, hq⟩
  · rintro ⟨s, hs, hq⟩
    refine ⟨a + b - s, ⟨by linarith [hs.2], by linarith [hs.1]⟩, ?_⟩
    have : a + b - (a + b - s) = s := by ring
    rw [this]; exact hq

/-! ### The leaving curve is future-inextensible -/

/-- **A curve with no limit in `W` at the supremum of its parameter is future-inextensible in
`W`**, with no separation axiom: a strict extension at the future end passes, at the supremum of
the reparametrised domain, through a point of `W`, which is then the limit of the curve at `b`. -/
theorem futureInextensible_of_forall_not_tendsto {I : Set ℝ} {c : ℝ → M}
    (hc : C.CausalCurveIn W I c) (hI : IsLUB I b) (hb : b ∉ I)
    (h : ∀ p ∈ W, ¬ Tendsto c (𝓝[<] b) (𝓝 p)) : C.FutureInextensible W I c := by
  refine ⟨hc, ?_⟩
  rintro ⟨I', c', hcurve, ⟨φ, hφmono, hφmaps, -, hφeq, hφend⟩, ⟨t', ht', hgrow⟩⟩
  obtain ⟨s₀, hs₀⟩ := hc.nonempty
  -- the new value comes after the whole reparametrised curve
  have hafter : ∀ s ∈ I, φ s < t' := by
    intro s hs
    by_contra h'
    obtain ⟨w, hw, hwt⟩ := hφend s hs t' ht' (not_lt.1 h')
    exact hgrow w hw (by rw [← hwt, hφeq w hw])
  have hne : (φ '' I).Nonempty := ⟨_, mem_image_of_mem φ hs₀⟩
  have hbdd : BddAbove (φ '' I) := ⟨t', by rintro _ ⟨s, hs, rfl⟩; exact (hafter s hs).le⟩
  set σ := sSup (φ '' I) with hσdef
  have hle : ∀ s ∈ I, φ s ≤ σ := fun s hs => le_csSup hbdd (mem_image_of_mem φ hs)
  have hσt : σ ≤ t' := csSup_le hne (by rintro _ ⟨s, hs, rfl⟩; exact (hafter s hs).le)
  have hσI : σ ∈ I' := hcurve.ordConnected.out (hφmaps hs₀) ht' ⟨hle s₀ hs₀, hσt⟩
  have hcont' : ContinuousWithinAt c' (Icc (φ s₀) σ) σ :=
    CurveOn.continuousOn C.isRelFamily_le (hcurve.curve _ (hφmaps hs₀) _ hσI) _
      ⟨hle _ hs₀, le_rfl⟩
  have hPW : c' σ ∈ W := hcurve.mem hσI
  have hlt : ∀ s ∈ I, s < b := fun s hs =>
    lt_of_le_of_ne (hI.1 hs) (fun he => hb (he ▸ hs))
  have hIoo : ∀ s₁ ∈ I, Ioo s₁ b ⊆ I := fun s₁ hs₁ τ hτ => by
    obtain ⟨s, hs, hτs⟩ := (lt_isLUB_iff hI).1 hτ.2
    exact hc.ordConnected.out hs₁ hs ⟨hτ.1.le, hτs.le⟩
  have hs₀b : s₀ < b := hlt s₀ hs₀
  have hφlim : Tendsto φ (𝓝[<] b) (𝓝[Icc (φ s₀) σ] σ) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · refine tendsto_order.2 ⟨fun a' ha' => ?_, fun a' ha' => ?_⟩
      · obtain ⟨_, ⟨s₁, hs₁, rfl⟩, has₁⟩ := exists_lt_of_lt_csSup hne ha'
        filter_upwards [Ioo_mem_nhdsLT (hlt s₁ hs₁)] with s hs
        exact has₁.trans (hφmono hs₁ (hIoo s₁ hs₁ hs) hs.1)
      · filter_upwards [Ioo_mem_nhdsLT hs₀b] with s hs
        exact (hle s (hIoo s₀ hs₀ hs)).trans_lt ha'
    · filter_upwards [Ioo_mem_nhdsLT hs₀b] with s hs
      exact ⟨(hφmono hs₀ (hIoo s₀ hs₀ hs) hs.1).le, hle s (hIoo s₀ hs₀ hs)⟩
  have hlim : Tendsto c (𝓝[<] b) (𝓝 (c' σ)) := by
    refine (hcont'.tendsto.comp hφlim).congr' ?_
    filter_upwards [Ioo_mem_nhdsLT hs₀b] with s hs using hφeq s (hIoo s₀ hs₀ hs)
  exact h _ hPW hlim

/-- On a Hausdorff space, a map tending to a point outside `W` tends to no point of `W`. -/
theorem forall_not_tendsto_of_tendsto_notMem [T2Space M] {l : Filter ℝ} [l.NeBot] {c : ℝ → M}
    {q : M} (hlim : Tendsto c l (𝓝 q)) (hq : q ∉ W) : ∀ p ∈ W, ¬ Tendsto c l (𝓝 p) :=
  fun p hp hp' => hq (by rw [tendsto_nhds_unique hlim hp']; exact hp)

/-- **The leaving curve is future-inextensible** (Sbierski Thm 3.1 Step 1, `:485`): a future
causal curve of an open `U` over `[a, b]` lying in the open `W ≤ U` on `[a, b)` with `γ b ∉ W` is,
over `[a, b)`, a future-inextensible causal curve of `W`, on a Hausdorff space. -/
theorem futureInextensible_of_leaving [T2Space M] {U : Opens M} (hγ : C.CausalCurveOn U γ a b)
    (hab : a < b) (hWU : W ≤ U) (hmem : ∀ t ∈ Ico a b, γ t ∈ W) (hb : γ b ∉ W) :
    C.FutureInextensible W (Ico a b) γ := by
  have hc : C.CausalCurveIn W (Ico a b) γ := by
    refine ⟨⟨a, left_mem_Ico.2 hab⟩, ordConnected_Ico, fun s hs s' hs' => ?_⟩
    rcases le_or_gt s s' with hss' | hss'
    · exact CurveOn.restrict hγ hs.1 hs'.2.le hWU
        (fun t ht => hmem t ⟨hs.1.trans ht.1, ht.2.trans_lt hs'.2⟩)
    · exact CurveOn.of_lt hss'
  have hcont : ContinuousWithinAt γ (Icc a b) b :=
    CurveOn.continuousOn C.isRelFamily_le hγ b (right_mem_Icc.2 hab.le)
  have hlim : Tendsto γ (𝓝[<] b) (𝓝 (γ b)) := by
    rw [← nhdsWithin_Ico_eq_nhdsLT hab]
    exact (hcont.mono Ico_subset_Icc_self).tendsto
  exact futureInextensible_of_forall_not_tendsto hc (isLUB_Ico hab) (fun h => lt_irrefl b h.2)
    (forall_not_tendsto_of_tendsto_notMem hlim hb)

/-- The chronal form of `futureInextensible_of_leaving`, the paper's timelike curve. -/
theorem ChronalCurveOn.futureInextensible_of_leaving [T2Space M] {U : Opens M}
    (hγ : C.ChronalCurveOn U γ a b) (hab : a < b) (hWU : W ≤ U)
    (hmem : ∀ t ∈ Ico a b, γ t ∈ W) (hb : γ b ∉ W) : C.FutureInextensible W (Ico a b) γ :=
  Causality.futureInextensible_of_leaving hγ.causalCurveOn hab hWU hmem hb

/-- For the reversed causality, future-inextensibility over `[a, b)` is past-inextensibility of
the reversed curve over `(-b, -a]`. -/
theorem dual_futureInextensible_Ico_iff :
    C.dual.FutureInextensible W (Ico a b) γ ↔
      C.PastInextensible W (Ioc (-b) (-a)) (fun t => γ (-t)) := by
  have h := dual_futureInextensible_iff (C := C) (W := W) (I := Ioc (-b) (-a))
    (c := fun t => γ (-t))
  simp only [neg_neg, neg_Ioc] at h
  exact h

/-- **Sbierski Thm 3.1 Step 1 and the proof of Thm 4.9 in ETT** (`:485`, `:798`): the leaving
curve of Lemma 2.17 (`exists_leaving_of_isOpenEmbedding`) is, for `D = C` or `D = C.dual`, a
future-inextensible causal curve over `[0, 1)` of the open `ι(N)`, on a Hausdorff `M`. -/
theorem exists_leaving_futureInextensible_of_isOpenEmbedding [T2Space M] {N : Type v}
    [TopologicalSpace N] [Nonempty N] [PreconnectedSpace M] {ι : N → M} (hι : IsOpenEmbedding ι)
    (hproper : range ι ≠ univ) (hC : C.CausallyArcConnected)
    (hchr : ∀ p ∈ frontier (range ι), C.HasChronalNeighbour p) :
    ∃ D : Causality M, (D = C ∨ D = C.dual) ∧ ∃ γ : ℝ → M, D.ChronalCurveOn ⊤ γ 0 1 ∧
      (∀ t ∈ Ico (0 : ℝ) 1, γ t ∈ range ι) ∧ γ 1 ∉ range ι ∧ γ 1 ∈ frontier (range ι) ∧
      (∀ s ∈ Ico (0 : ℝ) 1, D.ChronalCurveOn ⟨range ι, hι.isOpen_range⟩ γ 0 s) ∧
      D.FutureInextensible ⟨range ι, hι.isOpen_range⟩ (Ico 0 1) γ := by
  obtain ⟨D, hD, γ, hγ, hmem, h1, hfr, hW⟩ := exists_leaving_of_isOpenEmbedding hι hproper hC hchr
  exact ⟨D, hD, γ, hγ, hmem, h1, hfr, hW,
    ChronalCurveOn.futureInextensible_of_leaving hγ zero_lt_one le_top hmem h1⟩

/-- **The same, with `C` alone**: the leaving curve is future-inextensible for `C` over `[0, 1)`,
or, reversed, past-inextensible for `C` over `(-1, 0]`. -/
theorem exists_leaving_inextensible_of_isOpenEmbedding [T2Space M] {N : Type v}
    [TopologicalSpace N] [Nonempty N] [PreconnectedSpace M] {ι : N → M} (hι : IsOpenEmbedding ι)
    (hproper : range ι ≠ univ) (hC : C.CausallyArcConnected)
    (hchr : ∀ p ∈ frontier (range ι), C.HasChronalNeighbour p) :
    ∃ γ : ℝ → M, (∀ t ∈ Ico (0 : ℝ) 1, γ t ∈ range ι) ∧ γ 1 ∈ frontier (range ι) ∧
      ((C.ChronalCurveOn ⊤ γ 0 1 ∧ C.FutureInextensible ⟨range ι, hι.isOpen_range⟩ (Ico 0 1) γ) ∨
        (C.dual.ChronalCurveOn ⊤ γ 0 1 ∧
          C.PastInextensible ⟨range ι, hι.isOpen_range⟩ (Ioc (-1) 0) (fun t => γ (-t)))) := by
  obtain ⟨D, hD, γ, hγ, hmem, -, hfr, -, hinex⟩ :=
    exists_leaving_futureInextensible_of_isOpenEmbedding hι hproper hC hchr
  refine ⟨γ, hmem, hfr, ?_⟩
  rcases hD with rfl | rfl
  · exact Or.inl ⟨hγ, hinex⟩
  · refine Or.inr ⟨hγ, ?_⟩
    have h := dual_futureInextensible_Ico_iff.1 hinex
    simpa using h

/-! ### Sbierski's own notion (Def 2.10): no continuous extension -/

/-- **No continuous extension to `[a, b]` with a value in `S` at `b`** (Sbierski Def 2.10) for a
map tending at `b⁻` to a point outside `S`, on a Hausdorff space. -/
theorem not_continuousExtension_of_tendsto [T2Space M] {S : Set M} {q : M} (hab : a < b)
    (hlim : Tendsto γ (𝓝[<] b) (𝓝 q)) (hq : q ∉ S) :
    ¬ ∃ γ' : ℝ → M, ContinuousOn γ' (Icc a b) ∧ EqOn γ' γ (Ico a b) ∧ γ' b ∈ S := by
  rintro ⟨γ', hcont, heq, hS⟩
  have h1 : Tendsto γ' (𝓝[<] b) (𝓝 (γ' b)) := by
    rw [← nhdsWithin_Ico_eq_nhdsLT hab]
    exact ((hcont b (right_mem_Icc.2 hab.le)).mono Ico_subset_Icc_self).tendsto
  have h2 : Tendsto γ (𝓝[<] b) (𝓝 (γ' b)) := by
    refine h1.congr' ?_
    filter_upwards [Ico_mem_nhdsLT hab] with s hs using heq hs
  exact hq (by rw [tendsto_nhds_unique hlim h2]; exact hS)

/-- **Sbierski's sentence in `N`** (`:485`, Def 2.10): if `ι ∘ δ = γ` on `[a, b)` (`δ = ι⁻¹ ∘ γ`)
and `γ` tends at `b⁻` to a point outside `ι(N)`, then `δ` has no continuous extension to `[a, b]`
in `N`; `ι` is only asked to be continuous. -/
theorem not_continuousExtension_preimage [T2Space M] {N : Type v} [TopologicalSpace N]
    {ι : N → M} (hι : Continuous ι) {δ : ℝ → N} {q : M} (hab : a < b)
    (hδ : ∀ t ∈ Ico a b, ι (δ t) = γ t) (hlim : Tendsto γ (𝓝[<] b) (𝓝 q)) (hq : q ∉ range ι) :
    ¬ ∃ δ' : ℝ → N, ContinuousOn δ' (Icc a b) ∧ EqOn δ' δ (Ico a b) := by
  rintro ⟨δ', hcont, heq⟩
  exact not_continuousExtension_of_tendsto hab hlim hq
    ⟨ι ∘ δ', hι.comp_continuousOn hcont, fun t ht => by
      simp only [Function.comp, heq ht, hδ t ht], mem_range_self _⟩

/-- **Sbierski's continuous inextendibility implies ETT's** (the binder's note on Def 2.10): a
causal curve of `W` over `[a, b)` with no continuous extension to `[a, b]` taking a value in `W`
at `b` is future-inextensible in `W`; no separation axiom. -/
theorem futureInextensible_of_not_continuousExtension {c : ℝ → M}
    (hc : C.CausalCurveIn W (Ico a b) c)
    (h : ¬ ∃ c' : ℝ → M, ContinuousOn c' (Icc a b) ∧ EqOn c' c (Ico a b) ∧ c' b ∈ W) :
    C.FutureInextensible W (Ico a b) c := by
  obtain ⟨s₀, hs₀⟩ := hc.nonempty
  have hab : a < b := hs₀.1.trans_lt hs₀.2
  refine futureInextensible_of_forall_not_tendsto hc (isLUB_Ico hab) (fun h => lt_irrefl b h.2)
    fun p hp hlim => h ⟨update c b p, ?_, ?_, by simpa using hp⟩
  · intro t ht
    rcases ht.2.lt_or_eq with htb | rfl
    · rw [continuousWithinAt_update_of_ne htb.ne]
      obtain ⟨t', htt', ht'b⟩ := exists_between htb
      have hcon : ContinuousWithinAt c (Icc a t') t :=
        CurveOn.continuousOn C.isRelFamily_le (hc.curve a ⟨le_rfl, hab⟩ t'
          ⟨ht.1.trans htt'.le, ht'b⟩) t ⟨ht.1, htt'.le⟩
      refine hcon.mono_of_mem_nhdsWithin ?_
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds htt')] with s hs hs'
      exact ⟨hs.1, (show s < t' from hs').le⟩
    · rw [continuousWithinAt_update_same, Icc_sdiff_right, nhdsWithin_Ico_eq_nhdsLT hab]
      exact hlim
  · intro t ht
    exact update_of_ne ht.2.ne _ _

/-! ### Definition 2.14: timelike separation by a set -/

variable (C) in
/-- **Sbierski 1507.00601 Def 2.14 in ETT**: `A` and `B` are *timelike separated by `K`* in the
spacetime `W` if every chronal curve of `W` over `[0, 1]`, future or past (a chronal curve of `C`
or of `C.dual`), from `A` to `B` meets `K`. -/
def ChronallySeparatedOn (W : Opens M) (K A B : Set M) : Prop :=
  ∀ σ : ℝ → M, (C.ChronalCurveOn W σ 0 1 ∨ C.dual.ChronalCurveOn W σ 0 1) → σ 0 ∈ A → σ 1 ∈ B →
    ∃ s ∈ Icc (0 : ℝ) 1, σ s ∈ K

variable (C) in
/-- Def 2.14 for the spacetime `M` itself. -/
def ChronallySeparated (K A B : Set M) : Prop := C.ChronallySeparatedOn ⊤ K A B

variable {K K' A A' B B' : Set M}

/-- Time reversal does not change timelike separation. -/
theorem dual_chronallySeparatedOn :
    C.dual.ChronallySeparatedOn W K A B ↔ C.ChronallySeparatedOn W K A B :=
  ⟨fun h σ hσ => h σ hσ.symm, fun h σ hσ => h σ hσ.symm⟩

/-- Timelike separation is symmetric in `A` and `B` (a curve run backwards). -/
theorem ChronallySeparatedOn.symm (h : C.ChronallySeparatedOn W K A B) :
    C.ChronallySeparatedOn W K B A := by
  intro σ hσ h0 h1
  have hrev : C.ChronalCurveOn W (fun t => σ (0 + 1 - t)) 0 1 ∨
      C.dual.ChronalCurveOn W (fun t => σ (0 + 1 - t)) 0 1 := by
    rcases hσ with hσ | hσ
    · exact Or.inr (CurveOn.reverse hσ)
    · exact Or.inl (CurveOn.reverse hσ)
  obtain ⟨s, hs, hK⟩ := h _ hrev (by simpa using h1) (by simpa using h0)
  exact ⟨0 + 1 - s, ⟨by linarith [hs.2], by linarith [hs.1]⟩, hK⟩

/-- Timelike separation by `K` is separation by every larger set, between smaller sets. -/
theorem ChronallySeparatedOn.mono (h : C.ChronallySeparatedOn W K A B) (hK : K ⊆ K')
    (hA : A' ⊆ A) (hB : B' ⊆ B) : C.ChronallySeparatedOn W K' A' B' := fun σ hσ h0 h1 =>
  let ⟨s, hs, hsK⟩ := h σ hσ (hA h0) (hB h1)
  ⟨s, hs, hK hsK⟩

/-- **The reformulation, `⇐`**, with no hypothesis on `C`: if `V = W ∖ K` is open and `A` has no
point of `B` in its chronological future or past in `V`, then `A` and `B` are timelike separated
by `K` in `W` (a curve avoiding `K` is a chronal curve of `V`, `CurveOn.restrict`). -/
theorem chronallySeparatedOn_of_Iplus_Iminus {V : Opens M} (hV : (V : Set M) = (W : Set M) \ K)
    (hplus : C.Iplus V A ∩ B = ∅) (hminus : C.Iminus V A ∩ B = ∅) :
    C.ChronallySeparatedOn W K A B := by
  intro σ hσ h0 h1
  by_contra hne
  have hnK : ∀ s ∈ Icc (0 : ℝ) 1, σ s ∉ K := fun s hs hK => hne ⟨s, hs, hK⟩
  have hVW : V ≤ W := fun x hx => by
    have hx' : x ∈ (V : Set M) := hx
    rw [hV] at hx'
    exact hx'.1
  have hσW : ∀ t ∈ Icc (0 : ℝ) 1, σ t ∈ W := fun t ht => by
    rcases hσ with hσ | hσ
    · exact hσ.mem t ht
    · exact hσ.mem t ht
  have hmemV : ∀ t ∈ Icc (0 : ℝ) 1, σ t ∈ V := fun t ht => by
    show σ t ∈ (V : Set M)
    rw [hV]
    exact ⟨hσW t ht, hnK t ht⟩
  rcases hσ with hσ | hσ
  · have hc : C.ChronalCurveOn V σ 0 1 := CurveOn.restrict hσ le_rfl le_rfl hVW hmemV
    have hlt : C.lt V (σ 0) (σ 1) := hc.lt_of_lt le_rfl zero_lt_one le_rfl
    exact (eq_empty_iff_forall_notMem.1 hplus) (σ 1) ⟨⟨σ 0, h0, hlt⟩, h1⟩
  · have hc : C.dual.ChronalCurveOn V σ 0 1 := CurveOn.restrict hσ le_rfl le_rfl hVW hmemV
    have hlt : C.lt V (σ 1) (σ 0) := hc.lt_of_lt le_rfl zero_lt_one le_rfl
    exact (eq_empty_iff_forall_notMem.1 hminus) (σ 1) ⟨⟨σ 0, h0, hlt⟩, h1⟩

/-- **The reformulation, `⇒`**, when `V = W ∖ K` is causally arc-connected: a point of `B` in
`I^±_V(A)` is joined to `A` by a chronal curve of `V`, which avoids `K`. -/
theorem Iplus_Iminus_of_chronallySeparatedOn {V : Opens M} (hV : (V : Set M) = (W : Set M) \ K)
    (hC : C.CausallyArcConnectedOn V) (h : C.ChronallySeparatedOn W K A B) :
    C.Iplus V A ∩ B = ∅ ∧ C.Iminus V A ∩ B = ∅ := by
  have hVW : V ≤ W := fun x hx => by
    have hx' : x ∈ (V : Set M) := hx
    rw [hV] at hx'
    exact hx'.1
  have hVK : ∀ x ∈ V, x ∉ K := fun x hx => by
    have hx' : x ∈ (V : Set M) := hx
    rw [hV] at hx'
    exact hx'.2
  constructor
  · refine eq_empty_iff_forall_notMem.2 ?_
    rintro q ⟨⟨x, hx, hxq⟩, hq⟩
    obtain ⟨σ, hσ, h0, h1⟩ := (hC V le_rfl x q).2.1 hxq
    obtain ⟨s, hs, hsK⟩ := h σ (Or.inl (CurveOn.mono_opens C.isRelFamily_lt hσ hVW))
      (h0 ▸ hx) (h1 ▸ hq)
    exact hVK _ (hσ.mem s hs) hsK
  · refine eq_empty_iff_forall_notMem.2 ?_
    rintro q ⟨⟨x, hx, hqx⟩, hq⟩
    obtain ⟨σ, hσ, h0, h1⟩ := (hC V le_rfl q x).2.1 hqx
    have hrev : C.dual.ChronalCurveOn V (fun t => σ (0 + 1 - t)) 0 1 := CurveOn.reverse hσ
    obtain ⟨s, hs, hsK⟩ := h _ (Or.inr (CurveOn.mono_opens C.dual.isRelFamily_lt hrev hVW))
      (by simpa [h1] using hx) (by simpa [h0] using hq)
    exact hVK _ (hrev.mem s hs) hsK

/-- **The reformulation of Def 2.14**, for any open `V = W ∖ K` causally arc-connected. -/
theorem chronallySeparatedOn_iff_of_coe_eq {V : Opens M} (hV : (V : Set M) = (W : Set M) \ K)
    (hC : C.CausallyArcConnectedOn V) :
    C.ChronallySeparatedOn W K A B ↔ C.Iplus V A ∩ B = ∅ ∧ C.Iminus V A ∩ B = ∅ :=
  ⟨Iplus_Iminus_of_chronallySeparatedOn hV hC,
    fun h => chronallySeparatedOn_of_Iplus_Iminus hV h.1 h.2⟩

/-- **The reformulation of Def 2.14 for `K` closed**, in a causally arc-connected open `W`:
`A` and `B` are timelike separated by `K` iff `I⁺(A, W ∖ K) ∩ B = ∅ = I⁻(A, W ∖ K) ∩ B`. -/
theorem chronallySeparatedOn_iff_of_isClosed (hK : IsClosed K) (hC : C.CausallyArcConnectedOn W) :
    C.ChronallySeparatedOn W K A B ↔
      C.Iplus (W ⊓ ⟨Kᶜ, hK.isOpen_compl⟩) A ∩ B = ∅ ∧
        C.Iminus (W ⊓ ⟨Kᶜ, hK.isOpen_compl⟩) A ∩ B = ∅ :=
  chronallySeparatedOn_iff_of_coe_eq (by ext x; simp [Set.mem_sdiff])
    (CausallyArcConnectedOn.mono hC inf_le_left)

/-- **Sbierski 1507.00601 Def 2.14's reformulation in ETT** (`:393`): in a causally arc-connected
spacetime `M`, for `K` closed, `A` and `B` are timelike separated by `K` iff
`I⁺(A, M ∖ K) ∩ B = ∅` and `I⁻(A, M ∖ K) ∩ B = ∅`. -/
theorem schw_def_2_14_iff (hK : IsClosed K) (hC : C.CausallyArcConnected) :
    C.ChronallySeparated K A B ↔
      C.Iplus ⟨Kᶜ, hK.isOpen_compl⟩ A ∩ B = ∅ ∧ C.Iminus ⟨Kᶜ, hK.isOpen_compl⟩ A ∩ B = ∅ :=
  chronallySeparatedOn_iff_of_coe_eq (by ext x; simp [Set.mem_sdiff])
    (CausallyArcConnectedOn.mono hC le_top)

end Causality

/-! ### Witnesses -/

open Causality

/-- On the timelike line, `{0}` and `{2}` are timelike separated by `{1}`. -/
theorem timelikeLine_chronallySeparated :
    timelikeLine.ChronallySeparated {1} {0} {2} := by
  refine (schw_def_2_14_iff isClosed_singleton timelikeLine_causallyArcConnected).2 ⟨?_, ?_⟩
  · refine eq_empty_iff_forall_notMem.2 ?_
    rintro q ⟨⟨x, hx, hxq⟩, hq⟩
    rw [mem_singleton_iff] at hx hq
    subst hx hq
    have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 2 := ⟨by norm_num, by norm_num⟩
    exact (timelikeLine_lt.1 hxq).2 h1 rfl
  · refine eq_empty_iff_forall_notMem.2 ?_
    rintro q ⟨⟨x, hx, hqx⟩, hq⟩
    rw [mem_singleton_iff] at hx hq
    subst hx hq
    have := (timelikeLine_lt.1 hqx).1
    norm_num at this

/-- On the timelike line, `{0}` and `{2}` are not timelike separated by `∅`. -/
theorem timelikeLine_not_chronallySeparated_empty :
    ¬ timelikeLine.ChronallySeparated ∅ {0} {2} := by
  intro h
  obtain ⟨s, -, hs⟩ := h (fun t => 0 + t * (2 - 0))
    (Or.inl (timelikeLine_chronalCurveOn_affine (by norm_num) (fun _ _ => trivial)))
    (by simp) (by norm_num)
  exact hs

/-- **The `⇒` of the reformulation needs arc-connectedness**: for `allRelated ℝ` (every two points
of an open set related), `{-1}` and `{1}` are timelike separated by the closed `{0}` (every chronal
curve is continuous), yet `1 ∈ I⁺(-1, ℝ ∖ {0})`. -/
theorem allRelated_chronallySeparated_not_iff :
    (LineDevelopment.allRelated ℝ).ChronallySeparated {0} {-1} {1} ∧
      ¬ ((LineDevelopment.allRelated ℝ).Iplus ⟨{0}ᶜ, isClosed_singleton.isOpen_compl⟩ {-1} ∩ {1}
        = ∅) := by
  constructor
  · intro σ hσ h0 h1
    have hcont : ContinuousOn σ (Icc 0 1) := by
      rcases hσ with hσ | hσ
      · exact CurveOn.continuousOn (LineDevelopment.allRelated ℝ).isRelFamily_lt hσ
      · exact CurveOn.continuousOn (LineDevelopment.allRelated ℝ).dual.isRelFamily_lt hσ
    rw [mem_singleton_iff] at h0 h1
    have hmem : (0 : ℝ) ∈ Icc (σ 0) (σ 1) := by rw [h0, h1]; norm_num
    obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc zero_le_one hcont hmem
    exact ⟨s, hs, hs0⟩
  · intro h
    have hm : (1 : ℝ) ∈ (LineDevelopment.allRelated ℝ).Iplus
        ⟨{0}ᶜ, isClosed_singleton.isOpen_compl⟩ {-1} ∩ {1} :=
      ⟨⟨-1, rfl, show (-1 : ℝ) ∈ ({0}ᶜ : Set ℝ) by norm_num,
        show (1 : ℝ) ∈ ({0}ᶜ : Set ℝ) by norm_num⟩, rfl⟩
    rw [h] at hm
    exact hm

/-- On the reversed timelike line, `t ↦ 1 - t` is a future chronal curve over `[0, 1]`. -/
theorem timelikeLine_dual_chronalCurveOn :
    timelikeLine.dual.ChronalCurveOn ⊤ (fun t => 1 - t) 0 1 := by
  have h := CurveOn.reverse (timelikeLine_chronalCurveOn_affine (U := ⊤) (p := 0) (q := 1)
    zero_lt_one (fun _ _ => trivial))
  exact CurveOn.congr h (fun t _ => by show 0 + (0 + 1 - t) * (1 - 0) = 1 - t; ring)

/-- On the reversed timelike line, `t ↦ 1 - t` leaves `(0, ∞)` at `t = 1`: over `[0, 1)` it is a
future-inextensible causal curve of `(0, ∞)`. -/
theorem timelikeLine_dual_futureInextensible :
    timelikeLine.dual.FutureInextensible ⟨Ioi 0, isOpen_Ioi⟩ (Ico 0 1) (fun t => 1 - t) :=
  ChronalCurveOn.futureInextensible_of_leaving timelikeLine_dual_chronalCurveOn zero_lt_one le_top
    (fun t ht => show (0 : ℝ) < 1 - t by linarith [ht.2])
    (show ¬ (0 : ℝ) < 1 - 1 by norm_num)

/-- The hypotheses of `exists_leaving_futureInextensible_of_isOpenEmbedding` hold for the timelike
line and the inclusion of `(0, ∞)`. -/
theorem timelikeLine_exists_leaving_futureInextensible :
    ∃ D : Causality ℝ, (D = timelikeLine ∨ D = timelikeLine.dual) ∧ ∃ γ : ℝ → ℝ,
      D.ChronalCurveOn ⊤ γ 0 1 ∧ (∀ t ∈ Ico (0 : ℝ) 1, γ t ∈ Ioi 0) ∧ γ 1 ∉ Ioi 0 ∧
      D.FutureInextensible ⟨Ioi 0, isOpen_Ioi⟩ (Ico 0 1) γ := by
  haveI : Nonempty (Ioi (0 : ℝ)) := ⟨⟨1, by norm_num⟩⟩
  have hι : IsOpenEmbedding ((↑) : Ioi (0 : ℝ) → ℝ) := isOpen_Ioi.isOpenEmbedding_subtypeVal
  obtain ⟨D, hD, γ, hγ, hmem, h1, -, -, hinex⟩ :=
    exists_leaving_futureInextensible_of_isOpenEmbedding (C := timelikeLine) hι
      (by rw [Subtype.range_coe]; exact Ioi_zero_ne_univ) timelikeLine_causallyArcConnected
      (fun p _ => timelikeLine_hasChronalNeighbour p)
  have hW : (⟨range ((↑) : Ioi (0 : ℝ) → ℝ), hι.isOpen_range⟩ : Opens ℝ) = ⟨Ioi 0, isOpen_Ioi⟩ :=
    Opens.ext Subtype.range_coe
  rw [hW] at hinex
  rw [Subtype.range_coe] at hmem h1
  exact ⟨D, hD, γ, hγ, hmem, h1, hinex⟩

/-- A three-point space with no Hausdorff separation: `x` is generic (in every non-empty open),
`p` and `q` lie in its closure and cannot be separated. -/
inductive ForkPoint
  | x
  | p
  | q
  deriving DecidableEq

namespace ForkPoint

/-- The topology generated by `{x}`, `{x, p}` and `{x, q}`. -/
instance : TopologicalSpace ForkPoint :=
  TopologicalSpace.generateFrom
    {{ForkPoint.x}, {ForkPoint.x, ForkPoint.p}, {ForkPoint.x, ForkPoint.q}}

/-- The open set `{x, p}`. -/
def xp : Opens ForkPoint :=
  ⟨{ForkPoint.x, ForkPoint.p}, TopologicalSpace.isOpen_generateFrom_of_mem (by simp)⟩

/-- The curve resting at `x` before `1` and at `q` from `1` on. -/
noncomputable def toQ (t : ℝ) : ForkPoint := if t < 1 then ForkPoint.x else ForkPoint.q

/-- The curve resting at `x` before `1` and at `p` from `1` on. -/
noncomputable def toP (t : ℝ) : ForkPoint := if t < 1 then ForkPoint.x else ForkPoint.p

theorem continuous_toQ : Continuous toQ := by
  refine continuous_generateFrom_iff.2 ?_
  rintro s (rfl | rfl | rfl)
  · have : toQ ⁻¹' {ForkPoint.x} = Iio 1 := by
      ext t; by_cases h : t < 1 <;> simp [toQ, h]
    rw [this]; exact isOpen_Iio
  · have : toQ ⁻¹' {ForkPoint.x, ForkPoint.p} = Iio 1 := by
      ext t; by_cases h : t < 1 <;> simp [toQ, h]
    rw [this]; exact isOpen_Iio
  · have : toQ ⁻¹' {ForkPoint.x, ForkPoint.q} = univ := by
      ext t; by_cases h : t < 1 <;> simp [toQ, h]
    rw [this]; exact isOpen_univ

theorem continuous_toP : Continuous toP := by
  refine continuous_generateFrom_iff.2 ?_
  rintro s (rfl | rfl | rfl)
  · have : toP ⁻¹' {ForkPoint.x} = Iio 1 := by
      ext t; by_cases h : t < 1 <;> simp [toP, h]
    rw [this]; exact isOpen_Iio
  · have : toP ⁻¹' {ForkPoint.x, ForkPoint.p} = univ := by
      ext t; by_cases h : t < 1 <;> simp [toP, h]
    rw [this]; exact isOpen_univ
  · have : toP ⁻¹' {ForkPoint.x, ForkPoint.q} = Iio 1 := by
      ext t; by_cases h : t < 1 <;> simp [toP, h]
    rw [this]; exact isOpen_Iio

end ForkPoint

open ForkPoint in
/-- **The Hausdorff hypothesis of `futureInextensible_of_leaving` cannot be dropped**: on the
non-Hausdorff `ForkPoint` with `allRelated`, `toQ` is a chronal curve of the space over `[0, 1]`,
lies in the open `xp = {x, p}` on `[0, 1)` and leaves it at `1` (`toQ 1 = q`), yet over `[0, 1)` it
is future-extensible in `{x, p}`: `toP` over `[0, 1]` extends it by `p`, the other limit. -/
theorem forkPoint_leaving_futureExtensible :
    (LineDevelopment.allRelated ForkPoint).ChronalCurveOn ⊤ toQ 0 1 ∧
      (∀ t ∈ Ico (0 : ℝ) 1, toQ t ∈ ForkPoint.xp) ∧ toQ 1 ∉ ForkPoint.xp ∧
      (LineDevelopment.allRelated ForkPoint).FutureExtensible ForkPoint.xp (Ico 0 1) toQ := by
  have hQ : ∀ t ∈ Ico (0 : ℝ) 1, toQ t = ForkPoint.x := fun t ht => by simp [toQ, ht.2]
  refine ⟨LineDevelopment.allRelated_chronalCurveOn continuous_toQ 0 1,
    fun t ht => by rw [hQ t ht]; simp [ForkPoint.xp], by simp [toQ, ForkPoint.xp], ?_⟩
  have hPW : ∀ t ∈ Icc (0 : ℝ) 1, toP t ∈ ForkPoint.xp := fun t _ => by
    by_cases h : t < 1 <;> simp [toP, h, ForkPoint.xp]
  refine ⟨Icc 0 1, toP, ⟨⟨0, left_mem_Icc.2 zero_le_one⟩, ordConnected_Icc, fun a ha b hb => ?_⟩,
    ⟨id, strictMonoOn_id, fun t ht => ⟨ht.1, ht.2.le⟩, by rw [image_id]; exact ordConnected_Ico,
      fun t ht => ?_, fun t ht t' ht' htt' => ⟨t', ⟨ht'.1, htt'.trans_lt ht.2⟩, rfl⟩⟩,
    ⟨1, right_mem_Icc.2 zero_le_one, fun t ht => ?_⟩⟩
  · rcases le_or_gt a b with hab | hab
    · have hc : (LineDevelopment.allRelated ForkPoint).ChronalCurveOn ForkPoint.xp toP a b :=
        CurveOn.restrict (LineDevelopment.allRelated_chronalCurveOn continuous_toP 0 1)
          ha.1 hb.2 le_top fun t ht => hPW t ⟨ha.1.trans ht.1, ht.2.trans hb.2⟩
      exact hc.causalCurveOn
    · exact CurveOn.of_lt hab
  · simp [toP, hQ t ht, ht.2]
  · rw [hQ t ht]; simp [toP]

open ForkPoint in
/-- So `ForkPoint` is not Hausdorff (from `futureInextensible_of_leaving` itself). -/
theorem forkPoint_not_t2Space : ¬ T2Space ForkPoint := by
  intro hT
  obtain ⟨hγ, hmem, h1, hext⟩ := forkPoint_leaving_futureExtensible
  exact (ChronalCurveOn.futureInextensible_of_leaving hγ zero_lt_one le_top hmem h1).2 hext

end Causal
