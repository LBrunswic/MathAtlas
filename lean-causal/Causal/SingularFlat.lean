import Causal.PushUp
import Causal.LinesCurves
import Causal.Inextensible
import Causal.GlobalHyperbolicity
import Causal.StrongCausality

/-!
# Singular flat spacetimes, abstractly: the model facts as one structure, and the causal
properties of Section 3.3 derived from it

`lem:past_BTZ` — `ETT.tex:1515`. `cor:K_injectif` — `ETT.tex:1575`.
`prop:K_densite_sing` — `ETT.tex:1634`. `cor:K_ordre` — `ETT.tex:1692`.
`lem:cup_cap_BTZ` — `ETT.tex:1825`, stated for globally hyperbolic `M` as the author ruled
(DEC-19), certificate `cupCapBTZAsPrinted_of_globallyHyperbolic` (`CausalScaffold.SingularGeroch`)
on `SingularFlatAxioms.cup_cap_BTZ`. None is marked: each is a statement about
`E^{1,2}_{≥0}`-manifolds, which the library does not define (the model spaces `E_α` are not built
and the paper does not construct `E_0`, `ETT.tex:1328–1356`). The causal facts the paper draws
from the model spaces are the fields of `SingularFlatAxioms C sing` (kb/0012), each with the line
it stands for; every theorem here is proved from them.

> `lem:past_BTZ`. Let $M$ be a singular spacetime. Then (a) for every $\alpha\in \RR_+$, each
> connected component of $\sing_\alpha(M)$ is an inextensible causal curve; if $\alpha>0$, such a
> connected component is moreover chronal; (b) every causal curve $c$ of $M$ decomposes as
> $c=\Delta\cup c^0$ with $\Delta=c\cap \sing_0(M)$ and $c^0=c\setminus \sing_0(M)$. Moreover
> $\Delta$ and $c^0$ are connected, $\Delta$ is closed and lies in the past of $c^0$.

> `cor:K_injectif`. If $M$ is a strongly causal $\mass{\geq 0}$-manifold, then the map
> $x\mapsto K^\pm(x)$ is injective.

> `prop:K_densite_sing`. Let $M$ be a strongly causal $\mass{\geq0}$-manifold. Then for every
> $x\in M$, $J^\pm(x)\subset \overline{K^\pm(x)}.$

> `cor:K_ordre`. Let $M$ be a globally hyperbolic $\mass{\geq0}$-manifold. Then for all
> $x,y\in M$, $x\leq y \iff K^-(x)\subset K^-(y) \iff K^+(y)\subset K^+(x).$

> `lem:cup_cap_BTZ`. Let $M$ be a strongly causal singular flat spacetime, let $p\in M$ and let
> $(p_n)$ be a sequence of $M$ converging to $p$. If $p \notin J^-(p_n)$ for every $n$ and if
> $p\in \sing_0(M)$, then $\bigcup_{N}\bigcap_{n\geq N} J^-(p_n)=J^-(p)\setminus \{p\}.$

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `E_{≥0}`-manifold / singular spacetime | ⚠ strengthened: `SingularFlatAxioms C sing` (fields below), `sing α` standing for `sing_α(M)` |
| `lem:past_BTZ` (a) | ⚠ strengthened: it is a field (`line`, `massive_line`), the parametrisation a closed embedding when `M` is causal |
| `lem:past_BTZ` (b) | ✓ derived from `past_local` and `isClosed_sing` (`past_BTZ_b`), for curves over any interval |
| `cor:K_injectif`: strongly causal | ✓ carried |
| `prop:K_densite_sing`: strongly causal | ⚠ weakened: not used (`K_densite_sing`) |
| `cor:K_ordre`: globally hyperbolic | ✓ carried |
| `lem:cup_cap_BTZ`: globally hyperbolic (DEC-19; printed "strongly causal") | ✓ carried (`SingularFlatAxioms.cup_cap_BTZ`); ⚠ weakened: `J^+(z)` closed for every `z` suffices (`cup_cap_BTZ_of_isClosed`); `⊇` holds with no hypothesis on `M` |

The fields: `pushUp` (`cor:pushup_sing`, l.1419), `absolutelyMinimal` (`cor:massA_causalite`,
l.1396), `causallyArcConnected` (`cor:massA_cac`, l.1408), `tarentin` (`rem:sing_tarentin`,
l.1364), `mem_Zplus`, `mem_Zminus_iff` (`rem:btz_pas_tarentin`, l.1358), `t2`,
`secondCountable`, `metrizable`, `locallyCompact`, `noIsolated`, `isClosed_sing`,
`interior_sing` (`prop:GX_sing_dec`, l.1435: a 3-manifold, `sing_α` a closed 1-submanifold),
`massive_line` (`lem:past_BTZ` (a), α > 0); at the points of `sing 0` (`BTZAxioms`):
`singularPastAt`, `Iminus_eq_empty`, `Iplus_eq`, `past_local` (`defi:causal_E0`, l.1344–1356), `line`
(`lem:past_BTZ` (a), α = 0).

## SCOPE (disclosed)

* **What is abstracted.** No model space, chart or smooth structure: `M` is a topological space
  with a causality `C` and sets `sing α`; "a smooth 3-manifold" is read as its topological
  consequences used here (metrizable, second countable, locally compact, no isolated point) and
  "a closed 1-submanifold" as closed with empty interior. The BTZ facts of `defi:causal_E0` are
  stated globally, as the proofs of `prop:K_monotone` and `cor:K_injectif` use them, except
  `past_local`, the chart form (`J^-_U(p) ⊂ sing_0`), from which (b) is proved as the paper does.
* **"connected"** in (b) is `IsPreconnected` (`Δ` may be empty), "`Δ` closed" is closed in the
  curve (`closure Δ ∩ c(I) ⊂ Δ`), "in the past of" is `≤_W` from every point of `Δ` to every point
  of `c⁰`. `J^-(p)` for a BTZ point `p` is the half-line of its line below `p` once `M` is causal
  (`Jminus_eq_image`), derived from (a), (b) and causal arc-connectedness.
* **`lem:past_BTZ` (a), the closed embedding, is asked only when `M` is causal.** It is used only
  there (`Jminus_eq_image`, `isClosed_Jminus`). Under DEC-6 a causal curve need not be injective,
  so a non-causal singular flat spacetime may have a compact singular component (`E_α` or `E_0`
  modulo a translation along its singular line: the component is a circle); the conditional
  form no longer excludes it by the embedding. In a causal `M` the closed embedding remains
  stronger than the paper's "inextensible causal curve".
* **`Iplus_eq` stands on an assertion the paper does not prove.** The field
  `I^+(p) = J^+(p) ∖ sing_0` is the sentence of `defi:causal_E0` flagged at l.1351 as "quoted
  from \cite{thesis}, where it is asserted without proof -- verify". It is used by
  `lt_of_le_of_not_mem`, hence by `K_monotone`, `K_densite_sing` (past half), `K_ordre` and,
  in `CausalScaffold.SingularGeroch`, `mesure_admissible` and everything built on it.
* **`prop:K_densite_sing` needs neither strong causality nor `lem:densite_modele`, given the
  field `Iplus_eq` in its global form.** Every point being strongly tarentin in the future,
  push-up gives the future at once; in the past a regular `y` is strongly tarentin in the past,
  and a BTZ `y < x` with `x` regular has `y ≪ x` by `I^+(y) = J^+(y) ∖ sing_0`. The paper states
  that identity in the model only (l.1352); deriving the global form in `M` is the chart and
  causal arc-connectedness argument of l.1663–1669, which the field absorbs. So the shortcut
  removes strong causality and `lem:densite_modele`, and removes causal arc-connectedness only
  because `Iplus_eq` is assumed globally.
* **`lem:cup_cap_BTZ`'s `⊂` needs `z ≤ p` from `z ≤ p_n`, i.e. `J^+(z)` closed at `p`.** Finding
  (by hand, not formalized: the library has no `E_0`): in `E_0 ∖ {w}`, `w` a point of the BTZ line
  below `p` and `z` a point of that line below `w`, `z ≪ p_n` for regular `p_n → p` with
  `p ∉ J^-(p_n)` (a chronal curve from a BTZ point leaves the line at once and avoids `w`), while
  `J^-(p)` is the segment `]w, p]`: the lemma fails for this strongly causal singular flat
  spacetime, granted that `E_0` is strongly causal. Its one use (l.2122) is globally hyperbolic,
  where it holds (`cup_cap_BTZ`). This finding is why the author ruled (DEC-19) that the lemma is
  stated for globally hyperbolic `M`: its certificate is `cupCapBTZAsPrinted_of_globallyHyperbolic`
  (`CausalScaffold.SingularGeroch`). The printed form (strong causality only) is not asserted: it
  stays the `Prop` `CupCapBTZAsPrinted` there, with this finding.
* **Finding on `defi:causal_E0` (by hand).** l.1329–1331 give `E_0` the metric
  `−dτ² + dρ² + ρ²dθ²` and call `{ρ = 0}` a lightlike line; with that metric `∂_τ` has norm `−1`
  on `{ρ = 0}`, which is timelike. Most likely a transcription error: the flat extreme-BTZ metric
  has the form `−2 dτ dρ + ρ² dθ²`, for which `{ρ = 0}` is lightlike. Nothing here depends on
  the metric: the BTZ facts are fields.
* **Satisfiability (kb/0012), and what has no witness.** The timelike line with every
  `sing α = ∅` satisfies the whole structure (`timelikeLine_singularFlatAxioms`), and every
  theorem whose hypotheses can hold with `sing 0 = ∅` is instantiated there — in its regular
  branch only. **The full structure with `sing 0 ≠ ∅` has no witness in the library**, so the
  BTZ branches (`K_calcul` (b)–(c) at a BTZ point, `Jminus_eq_image`, `isClosed_Jminus`,
  `lt_of_le_of_not_mem`, `SingularFlatAxioms.cup_cap_BTZ`, and the BTZ cases inside
  `K_injectif`, `K_densite_sing`, `K_monotone`) are never instantiated with a BTZ point. The
  lightlike line with `sing_0 = ℝ` satisfies `BTZAxioms` alone (`lightlikeLine_btzAxioms`) and
  the hypotheses of `cup_cap_BTZ_of_isClosed` (`lightlikeLine_cup_cap_BTZ`). Neither of these two
  lines carries the whole structure with `sing 0 ≠ ∅` (`timelikeLine_sing_zero`,
  `lightlikeLine_not_mem_Zplus`); that is proved for these two lines only, not for every line,
  and no dimension bound is proved.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter

universe u

variable {M : Type u} [TopologicalSpace M]

namespace Causality

/-! ### The structure -/

/-- The causal facts of a BTZ point (`defi:causal_E0`, `ETT.tex:1344–1356`, and
`lem:past_BTZ` (a) for `α = 0`, `ETT.tex:1518–1519`), at every point of the set `S₀` standing
for `sing_0(M)`. -/
structure BTZAxioms (C : Causality M) (S₀ : Set M) : Prop where
  /-- The past of a BTZ point is a half-line along which `K^-` is computed (`ETT.tex:1349`, as
  the proof of `prop:K_calcul` (c) uses it, `ETT.tex:1565–1573`). -/
  singularPastAt : ∀ p ∈ S₀, C.SingularPastAt p
  /-- `I^-(p) = ∅` (`ETT.tex:1349`). -/
  Iminus_eq_empty : ∀ p ∈ S₀, C.Iminus ⊤ {p} = ∅
  /-- `I^+(p) = J^+(p) ∖ sing_0` (`ETT.tex:1352–1355`, "asserted without proof" in the paper's
  source). -/
  Iplus_eq : ∀ p ∈ S₀, C.Iplus ⊤ {p} = C.Jplus ⊤ {p} \ S₀
  /-- In a chart at a BTZ point, `J^-_U(p) ⊂ sing_0(U)` (`ETT.tex:1349` read in a chart, as the
  proof of `lem:past_BTZ` (b) uses it, `ETT.tex:1534–1536`). -/
  past_local : ∀ p ∈ S₀, ∃ U : Opens M, p ∈ U ∧ ∀ q, C.le U q p → q ∈ S₀
  /-- `lem:past_BTZ` (a), `α = 0`: the connected component of `sing_0` through `p` is an
  inextensible causal curve parametrised by `ℝ`, a closed embedding when `M` is causal
  (`ETT.tex:1518, 1527–1531`). -/
  line : ∀ p ∈ S₀, ∃ γ : ℝ → M, γ 0 = p ∧ (C.IsCausal → IsClosedEmbedding γ) ∧
    C.Inextensible ⊤ univ γ ∧ range γ = connectedComponentIn S₀ p

/-- **The causal facts the paper derives for `E^{1,2}_{≥0}`-manifolds**, `sing α` standing for
`sing_α(M)` (`α ≥ 0`; other values are unconstrained). -/
structure SingularFlatAxioms (C : Causality M) (sing : ℝ → Set M) : Prop
    extends BTZAxioms C (sing 0) where
  /-- `cor:pushup_sing`, `ETT.tex:1419`. -/
  pushUp : C.PushUp
  /-- `cor:massA_causalite`, `ETT.tex:1396`. -/
  absolutelyMinimal : C.AbsolutelyMinimal
  /-- `cor:massA_cac`, `ETT.tex:1408`. -/
  causallyArcConnected : C.CausallyArcConnected
  /-- `rem:sing_tarentin`, `ETT.tex:1364`. -/
  tarentin : C.Tarentin
  /-- `rem:btz_pas_tarentin`, `ETT.tex:1358`: every point is strongly tarentin in the future. -/
  mem_Zplus : ∀ p, p ∈ C.Zplus
  /-- `rem:btz_pas_tarentin`: the points not strongly tarentin in the past are the BTZ points. -/
  mem_Zminus_iff : ∀ p, p ∈ C.Zminus ↔ p ∉ sing 0
  /-- `prop:GX_sing_dec`, `ETT.tex:1435` (a manifold): Hausdorff. -/
  t2 : T2Space M
  /-- `prop:GX_sing_dec`: second countable. -/
  secondCountable : SecondCountableTopology M
  /-- `prop:GX_sing_dec`: a manifold is metrizable. -/
  metrizable : MetrizableSpace M
  /-- `prop:GX_sing_dec`: a manifold is locally compact. -/
  locallyCompact : LocallyCompactSpace M
  /-- `prop:GX_sing_dec`: a 3-manifold has no isolated point. -/
  noIsolated : ∀ p : M, (𝓝[≠] p).NeBot
  /-- `prop:GX_sing_dec`: `sing_α(M)` is a closed 1-submanifold — closed. -/
  isClosed_sing : ∀ α : ℝ, 0 ≤ α → IsClosed (sing α)
  /-- `prop:GX_sing_dec`: a 1-submanifold of a 3-manifold has empty interior. -/
  interior_sing : ∀ α : ℝ, 0 ≤ α → interior (sing α) = ∅
  /-- `lem:past_BTZ` (a), `α > 0`: each component of `sing_α` is an inextensible chronal curve,
  a closed embedding when `M` is causal (`ETT.tex:1518–1519, 1527–1531`). -/
  massive_line : ∀ α : ℝ, 0 < α → ∀ p ∈ sing α, ∃ γ : ℝ → M, γ 0 = p ∧
    (C.IsCausal → IsClosedEmbedding γ) ∧
    C.Inextensible ⊤ univ γ ∧ (∀ a b, C.ChronalCurveOn ⊤ γ a b) ∧
    range γ = connectedComponentIn (sing α) p

variable {C : Causality M} {p q x y z : M}

/-! ### The past of a BTZ point -/

/-- `SingularPastAt p` puts `p` in the closure of `J^-(p) ∖ {p}`. -/
theorem SingularPastAt.mem_closure (hS : C.SingularPastAt p) :
    p ∈ closure (C.Jminus ⊤ {p} \ {p}) := by
  obtain ⟨⟨u, hu, hup⟩, -⟩ := hS
  exact mem_closure_of_tendsto hu (Eventually.of_forall fun n =>
    ⟨by simpa using (hup n).1, (hup n).2⟩)

/-- `J^-(p) ∖ {p} ⊂ K^-(p)` at a point with `SingularPastAt p`, with no causality asked. -/
theorem SingularPastAt.Jminus_diff_subset_Kminus (hS : C.SingularPastAt p) :
    C.Jminus ⊤ {p} \ {p} ⊆ C.Kminus ⊤ {p} := by
  rintro x ⟨hxJ, hxne⟩
  obtain ⟨u, hu, hmono, hint, hx0⟩ := hS.2 x (by simpa using hxJ) hxne
  rw [Kminus_eq_of_tendsto hu hint]
  refine mem_iUnion.2 ⟨0, interiorWithin_mono ?_ hx0⟩
  intro w hw
  simp only [mem_iInter]
  intro n _
  have hw0 : C.le ⊤ w (u 0) := by simpa using hw
  simpa using C.le_trans hw0 (hmono 0 n (Nat.zero_le n))

/-! ### `lem:past_BTZ` (b) -/

/-- The core of `lem:past_BTZ` (b): if `S₀` is closed and, at each of its points, the past in some
open set stays in `S₀`, then along a causal curve the parameters mapped into `S₀` form an initial
segment. The proof of the paper (`ETT.tex:1530–1548`), with an infimum. -/
theorem mem_of_causalCurveOn {S₀ : Set M} (hS : IsClosed S₀)
    (hloc : ∀ p ∈ S₀, ∃ U : Opens M, p ∈ U ∧ ∀ q, C.le U q p → q ∈ S₀)
    {W : Opens M} {c : ℝ → M} {a b : ℝ} (hc : C.CausalCurveOn W c a b) {s s' : ℝ}
    (hs' : a ≤ s') (hs's : s' ≤ s) (hs : s ≤ b) (hcs : c s ∈ S₀) : c s' ∈ S₀ := by
  have hcont : ContinuousOn c (Icc s' s) :=
    (hc.continuousOn C.isRelFamily_le).mono (Icc_subset_Icc hs' hs)
  set F : Set ℝ := Icc s' s ∩ c ⁻¹' S₀ with hF
  have hFc : IsClosed F := hcont.preimage_isClosed_of_isClosed isClosed_Icc hS
  have hsF : s ∈ F := ⟨⟨hs's, le_rfl⟩, hcs⟩
  have hbdd : BddBelow F := ⟨s', fun t ht => ht.1.1⟩
  have ht₀ : sInf F ∈ F := hFc.csInf_mem ⟨s, hsF⟩ hbdd
  rcases (ht₀.1.1).eq_or_lt with h | h
  · rw [h]; exact ht₀.2
  · exfalso
    set t₀ := sInf F
    obtain ⟨U, hU, hUS⟩ := hloc (c t₀) ht₀.2
    have ht₀ab : t₀ ∈ Icc a b := ⟨hs'.trans ht₀.1.1, ht₀.1.2.trans hs⟩
    have hW : c t₀ ∈ W := hc.mem t₀ ht₀ab
    obtain ⟨l, u, hl, hu, hrel⟩ :=
      hc.rel t₀ ht₀ab (U ⊓ W) inf_le_right ⟨hU, hW⟩
    set m : ℝ := max l s' with hm
    have hm1 : m < t₀ := max_lt hl h
    set σ : ℝ := (m + t₀) / 2 with hσ
    have hσ1 : m < σ := by rw [hσ]; linarith
    have hσ2 : σ < t₀ := by rw [hσ]; linarith
    have hlσ : l < σ := lt_of_le_of_lt (le_max_left _ _) hσ1
    have hs'σ : s' < σ := lt_of_le_of_lt (le_max_right _ _) hσ1
    have hσab : σ ∈ Icc a b := ⟨hs'.trans hs'σ.le, hσ2.le.trans ht₀ab.2⟩
    have hle : C.le (U ⊓ W) (c σ) (c t₀) := hrel σ hσab t₀ ht₀ab hlσ hσ2 hu
    have hσS : c σ ∈ S₀ := hUS _ (C.le_mono inf_le_left hle)
    have hσF : σ ∈ F := ⟨⟨hs'σ.le, hσ2.le.trans ht₀.1.2⟩, hσS⟩
    exact absurd (csInf_le hbdd hσF) (not_le.2 hσ2)

namespace SingularFlatAxioms

variable {sing : ℝ → Set M}

/-- Along a causal curve over `[a, b]`, the parameters mapped to BTZ points form an initial
segment. -/
theorem mem_sing_zero_of_causalCurveOn (h : C.SingularFlatAxioms sing) {W : Opens M}
    {c : ℝ → M} {a b : ℝ} (hc : C.CausalCurveOn W c a b) {s s' : ℝ} (hs' : a ≤ s')
    (hs's : s' ≤ s) (hs : s ≤ b) (hcs : c s ∈ sing 0) : c s' ∈ sing 0 :=
  mem_of_causalCurveOn (h.isClosed_sing 0 le_rfl) h.past_local hc hs' hs's hs hcs

/-- `lem:past_BTZ` (b): along a causal curve `c` of `W` over an interval `I`, the parameters
mapped into `sing_0` form an initial segment of `I`; `Δ = c(I) ∩ sing_0` and
`c⁰ = c(I) ∖ sing_0` are preconnected, `Δ` is closed in `c(I)`, and every point of `Δ` is in the
past (in `W`) of every point of `c⁰`. -/
theorem past_BTZ_b (h : C.SingularFlatAxioms sing) {W : Opens M} {I : Set ℝ} {c : ℝ → M}
    (hc : C.CausalCurveIn W I c) :
    (∀ s ∈ I, ∀ s' ∈ I, s' ≤ s → c s ∈ sing 0 → c s' ∈ sing 0) ∧
    c '' I = (c '' I ∩ sing 0) ∪ (c '' I \ sing 0) ∧
    IsPreconnected (c '' I ∩ sing 0) ∧ IsPreconnected (c '' I \ sing 0) ∧
    closure (c '' I ∩ sing 0) ∩ c '' I ⊆ c '' I ∩ sing 0 ∧
    ∀ x ∈ c '' I ∩ sing 0, ∀ y ∈ c '' I \ sing 0, C.le W x y := by
  have hseg : ∀ s ∈ I, ∀ s' ∈ I, s' ≤ s → c s ∈ sing 0 → c s' ∈ sing 0 :=
    fun s hs s' hs' hle hcs =>
      h.mem_sing_zero_of_causalCurveOn (hc.curve s' hs' s hs) le_rfl hle le_rfl hcs
  -- the image of a segment of `I` is preconnected
  have hseg_pre : ∀ σ ∈ I, ∀ τ ∈ I, σ ≤ τ → IsPreconnected (c '' Icc σ τ) := fun σ hσ τ hτ _ =>
    isPreconnected_Icc.image c ((hc.curve σ hσ τ hτ).continuousOn C.isRelFamily_le)
  have hIcc : ∀ σ ∈ I, ∀ τ ∈ I, Icc σ τ ⊆ I := fun σ hσ τ hτ => hc.ordConnected.out hσ hτ
  refine ⟨hseg, (inter_union_sdiff _ _).symm, ?_, ?_, ?_, ?_⟩
  · refine isPreconnected_of_forall_pair ?_
    rintro _ ⟨⟨σ, hσ, rfl⟩, hσS⟩ _ ⟨⟨τ, hτ, rfl⟩, hτS⟩
    rcases le_total σ τ with hστ | hτσ
    · refine ⟨c '' Icc σ τ, ?_, ⟨σ, left_mem_Icc.2 hστ, rfl⟩, ⟨τ, right_mem_Icc.2 hστ, rfl⟩,
        hseg_pre σ hσ τ hτ hστ⟩
      rintro _ ⟨ρ, hρ, rfl⟩
      exact ⟨⟨ρ, hIcc σ hσ τ hτ hρ, rfl⟩, hseg τ hτ ρ (hIcc σ hσ τ hτ hρ) hρ.2 hτS⟩
    · refine ⟨c '' Icc τ σ, ?_, ⟨σ, right_mem_Icc.2 hτσ, rfl⟩, ⟨τ, left_mem_Icc.2 hτσ, rfl⟩,
        hseg_pre τ hτ σ hσ hτσ⟩
      rintro _ ⟨ρ, hρ, rfl⟩
      exact ⟨⟨ρ, hIcc τ hτ σ hσ hρ, rfl⟩, hseg σ hσ ρ (hIcc τ hτ σ hσ hρ) hρ.2 hσS⟩
  · refine isPreconnected_of_forall_pair ?_
    rintro _ ⟨⟨σ, hσ, rfl⟩, hσS⟩ _ ⟨⟨τ, hτ, rfl⟩, hτS⟩
    rcases le_total σ τ with hστ | hτσ
    · refine ⟨c '' Icc σ τ, ?_, ⟨σ, left_mem_Icc.2 hστ, rfl⟩, ⟨τ, right_mem_Icc.2 hστ, rfl⟩,
        hseg_pre σ hσ τ hτ hστ⟩
      rintro _ ⟨ρ, hρ, rfl⟩
      exact ⟨⟨ρ, hIcc σ hσ τ hτ hρ, rfl⟩, fun hρS =>
        hσS (hseg ρ (hIcc σ hσ τ hτ hρ) σ hσ hρ.1 hρS)⟩
    · refine ⟨c '' Icc τ σ, ?_, ⟨σ, right_mem_Icc.2 hτσ, rfl⟩, ⟨τ, left_mem_Icc.2 hτσ, rfl⟩,
        hseg_pre τ hτ σ hσ hτσ⟩
      rintro _ ⟨ρ, hρ, rfl⟩
      exact ⟨⟨ρ, hIcc τ hτ σ hσ hρ, rfl⟩, fun hρS =>
        hτS (hseg ρ (hIcc τ hτ σ hσ hρ) τ hτ hρ.1 hρS)⟩
  · rintro x ⟨hx, hxI⟩
    have : x ∈ closure (sing 0) := closure_mono inter_subset_right hx
    rw [(h.isClosed_sing 0 le_rfl).closure_eq] at this
    exact ⟨hxI, this⟩
  · rintro _ ⟨⟨σ, hσ, rfl⟩, hσS⟩ _ ⟨⟨τ, hτ, rfl⟩, hτS⟩
    rcases le_or_gt σ τ with hστ | hτσ
    · exact hc.le_of_le hσ hτ hστ
    · exact absurd (hseg σ hσ τ hτ hτσ.le hσS) hτS

/-- The causal past of a BTZ point consists of BTZ points (from (b) and causal
arc-connectedness), and lies in the connected component of `sing_0` through it. -/
theorem Jminus_subset_component (h : C.SingularFlatAxioms sing) (hp : p ∈ sing 0)
    (hqp : C.le ⊤ q p) : q ∈ connectedComponentIn (sing 0) p := by
  obtain ⟨c, hc, rfl, rfl⟩ := (h.causallyArcConnected ⊤ le_rfl q p).1.1 hqp
  have hsub : c '' Icc 0 1 ⊆ sing 0 := by
    rintro _ ⟨t, ht, rfl⟩
    exact h.mem_sing_zero_of_causalCurveOn hc ht.1 ht.2 le_rfl hp
  have hpre : IsPreconnected (c '' Icc 0 1) :=
    isPreconnected_Icc.image c (hc.continuousOn C.isRelFamily_le)
  exact hpre.subset_connectedComponentIn ⟨1, right_mem_Icc.2 zero_le_one, rfl⟩ hsub
    ⟨0, left_mem_Icc.2 zero_le_one, rfl⟩

/-- `J^-(p) ⊂ sing_0` for a BTZ point `p`. -/
theorem mem_sing_zero_of_le (h : C.SingularFlatAxioms sing) (hp : p ∈ sing 0)
    (hqp : C.le ⊤ q p) : q ∈ sing 0 :=
  connectedComponentIn_subset _ _ (h.Jminus_subset_component hp hqp)

/-- `x ≤ y`, `x` BTZ and `y` regular give `x ≪ y` (`I^+(x) = J^+(x) ∖ sing_0`). -/
theorem lt_of_le_of_not_mem (h : C.SingularFlatAxioms sing) (hx : x ∈ sing 0)
    (hy : y ∉ sing 0) (hxy : C.le ⊤ x y) : C.lt ⊤ x y := by
  have : y ∈ C.Iplus ⊤ {x} := by
    rw [h.Iplus_eq x hx]
    exact ⟨by simpa using hxy, hy⟩
  simpa using this

/-- In a causal `E_{≥0}`-manifold, the past of a BTZ point `p` is the half-line below `p` of its
BTZ line (`ETT.tex:1593`): `J^-(γ 0) = γ(]-∞, 0])`. -/
theorem Jminus_eq_image (h : C.SingularFlatAxioms sing) (hc : C.IsCausal) (hp : p ∈ sing 0)
    {γ : ℝ → M} (hγ0 : γ 0 = p) (hγ : IsClosedEmbedding γ) (hγc : C.CausalCurveIn ⊤ univ γ)
    (hγr : range γ = connectedComponentIn (sing 0) p) :
    C.Jminus ⊤ {p} = γ '' Iic 0 := by
  ext q
  constructor
  · intro hq
    have hqp : C.le ⊤ q p := by simpa using hq
    have hqr : q ∈ range γ := by rw [hγr]; exact h.Jminus_subset_component hp hqp
    obtain ⟨t, rfl⟩ := hqr
    refine ⟨t, ?_, rfl⟩
    by_contra ht
    have ht' : 0 < t := not_le.1 ht
    have h0t : C.le ⊤ (γ 0) (γ t) := hγc.le_of_le trivial trivial ht'.le
    rw [hγ0] at h0t
    have heq : γ t = γ 0 := (hc hqp h0t).trans hγ0.symm
    exact ht'.ne' (hγ.injective heq)
  · rintro ⟨t, ht, rfl⟩
    have := hγc.le_of_le trivial trivial (show t ≤ 0 from ht)
    rw [hγ0] at this
    simpa using this

/-- In a causal `E_{≥0}`-manifold, the causal past of a BTZ point is closed. -/
theorem isClosed_Jminus (h : C.SingularFlatAxioms sing) (hc : C.IsCausal) (hp : p ∈ sing 0) :
    IsClosed (C.Jminus ⊤ {p}) := by
  obtain ⟨γ, hγ0, hγ, hγi, hγr⟩ := h.line p hp
  rw [h.Jminus_eq_image hc hp hγ0 (hγ hc) hγi.1 hγr]
  exact (hγ hc).isClosedMap _ isClosed_Iic

/-! ### `prop:K_calcul` and `prop:K_monotone` for the structure -/

/-- `prop:K_calcul` under the structure (`Causal.PushUp`). -/
theorem K_calcul (h : C.SingularFlatAxioms sing) :
    (∀ p ∉ sing 0, C.Kplus ⊤ {p} = C.Iplus ⊤ {p} ∧ C.Kminus ⊤ {p} = C.Iminus ⊤ {p}) ∧
    (∀ p ∈ sing 0, C.Kplus ⊤ {p} = C.Iplus ⊤ {p}) ∧
    (C.IsCausal → ∀ p ∈ sing 0, C.Kminus ⊤ {p} = C.Jminus ⊤ {p} \ {p}) := by
  haveI := h.secondCountable
  exact Causality.K_calcul h.pushUp h.mem_Zplus (fun p hp => (h.mem_Zminus_iff p).2 hp)
    h.singularPastAt

/-- `prop:K_monotone` under the structure (`Causal.PushUp`), the two inclusions on `J^-` being
`mem_sing_zero_of_le` and `lt_of_le_of_not_mem`. -/
theorem K_monotone (h : C.SingularFlatAxioms sing) (hc : C.IsCausal) (hqp : C.le ⊤ q p) :
    C.Kminus ⊤ {q} ⊆ C.Kminus ⊤ {p} ∧ C.Kplus ⊤ {p} ⊆ C.Kplus ⊤ {q} := by
  haveI := h.secondCountable
  exact Causality.K_monotone hc h.pushUp h.mem_Zplus (fun p hp => (h.mem_Zminus_iff p).2 hp)
    h.singularPastAt (fun _ hp _ hqp => h.mem_sing_zero_of_le hp hqp)
    (fun _ hx _ hy hxy => h.lt_of_le_of_not_mem hx hy hxy) hqp

/-! ### `cor:K_injectif` -/

/-- `cor:K_injectif`: on a strongly causal `E_{≥0}`-manifold, `x ↦ K^+(x)` and `x ↦ K^-(x)` are
injective. -/
theorem K_injectif (h : C.SingularFlatAxioms sing) (hSC : C.StronglyCausal) :
    Function.Injective (fun x => C.Kplus ⊤ {x}) ∧
      Function.Injective (fun x => C.Kminus ⊤ {x}) := by
  haveI := h.t2
  haveI := h.secondCountable
  have hc : C.IsCausal := hSC.isCausal
  have hKp : ∀ x, C.Kplus ⊤ {x} = C.Iplus ⊤ {x} := fun x => h.pushUp.Kplus_eq_Iplus (h.mem_Zplus x)
  refine ⟨fun x y hxy => ?_, fun x y hxy => ?_⟩
  · have hI : C.Iplus ⊤ {x} = C.Iplus ⊤ {y} := by
      have : C.Kplus ⊤ {x} = C.Kplus ⊤ {y} := hxy
      rwa [hKp, hKp] at this
    exact Iplus_injOn_Zplus hSC (h.mem_Zplus x) (h.mem_Zplus y) hI
  · have hK : C.Kminus ⊤ {x} = C.Kminus ⊤ {y} := hxy
    -- a BTZ point and a regular point cannot share `K^-`
    have hmixed : ∀ a b : M, a ∈ sing 0 → b ∉ sing 0 →
        C.Kminus ⊤ {a} ≠ C.Kminus ⊤ {b} := by
      intro a b ha hb hab
      have hbZ := (h.mem_Zminus_iff b).2 hb
      rw [h.pushUp.Kminus_eq_Iminus hbZ] at hab
      have hsub : C.Iminus ⊤ {b} ⊆ sing 0 := by
        rw [← hab]
        intro w hw
        exact h.mem_sing_zero_of_le ha (by simpa using Kminus_subset_Jminus hw)
      have hint : C.Iminus ⊤ {b} ⊆ interior (sing 0) := interior_maximal hsub isOpen_Iminus
      rw [h.interior_sing 0 le_rfl] at hint
      obtain ⟨w, hw⟩ := Iminus_nonempty_of_mem_Zminus hbZ
      exact hint hw
    by_cases hx : x ∈ sing 0 <;> by_cases hy : y ∈ sing 0
    · have hJ : C.Jminus ⊤ {x} \ {x} = C.Jminus ⊤ {y} \ {y} := by
        rw [← (h.K_calcul).2.2 hc x hx, ← (h.K_calcul).2.2 hc y hy]; exact hK
      have hxy : C.le ⊤ x y := by
        have h1 := (h.singularPastAt x hx).mem_closure
        rw [hJ] at h1
        have h2 := closure_mono sdiff_subset h1
        rw [(h.isClosed_Jminus hc hy).closure_eq] at h2
        simpa using h2
      have hyx : C.le ⊤ y x := by
        have h1 := (h.singularPastAt y hy).mem_closure
        rw [← hJ] at h1
        have h2 := closure_mono sdiff_subset h1
        rw [(h.isClosed_Jminus hc hx).closure_eq] at h2
        simpa using h2
      exact hc hxy hyx
    · exact absurd hK (hmixed x y hx hy)
    · exact absurd hK.symm (hmixed y x hy hx)
    · have hxZ := (h.mem_Zminus_iff x).2 hx
      have hyZ := (h.mem_Zminus_iff y).2 hy
      have hI : C.Iminus ⊤ {x} = C.Iminus ⊤ {y} := by
        rwa [h.pushUp.Kminus_eq_Iminus hxZ, h.pushUp.Kminus_eq_Iminus hyZ] at hK
      exact Iminus_injOn_Zminus hSC hxZ hyZ hI

/-! ### `prop:K_densite_sing` -/

/-- `prop:K_densite_sing`: on an `E_{≥0}`-manifold, `J^±(x) ⊂ closure K^±(x)` for every `x`.
Strong causality is not used. -/
theorem K_densite_sing (h : C.SingularFlatAxioms sing) (x : M) :
    C.Jplus ⊤ {x} ⊆ closure (C.Kplus ⊤ {x}) ∧ C.Jminus ⊤ {x} ⊆ closure (C.Kminus ⊤ {x}) := by
  haveI := h.secondCountable
  constructor
  · rw [h.pushUp.Kplus_eq_Iplus (h.mem_Zplus x)]
    intro y hy
    have hxy : C.le ⊤ x y := by simpa using hy
    rw [mem_closure_iff_nhds]
    intro N hN
    obtain ⟨w, hw, hwN⟩ := h.mem_Zplus y N hN
    have hyw : C.lt ⊤ y w := by simpa using hw
    exact ⟨w, hwN, by simpa using h.pushUp.lt_of_le_of_lt hxy hyw⟩
  · by_cases hx : x ∈ sing 0
    · have hS := h.singularPastAt x hx
      intro y hy
      by_cases hyx : y = x
      · subst hyx
        exact closure_mono hS.Jminus_diff_subset_Kminus hS.mem_closure
      · exact subset_closure (hS.Jminus_diff_subset_Kminus ⟨hy, hyx⟩)
    · rw [h.pushUp.Kminus_eq_Iminus ((h.mem_Zminus_iff x).2 hx)]
      intro y hy
      have hyx : C.le ⊤ y x := by simpa using hy
      by_cases hyS : y ∈ sing 0
      · exact subset_closure (by simpa using h.lt_of_le_of_not_mem hyS hx hyx)
      · rw [mem_closure_iff_nhds]
        intro N hN
        obtain ⟨w, hw, hwN⟩ := (h.mem_Zminus_iff y).2 hyS N hN
        have hwy : C.lt ⊤ w y := by simpa using hw
        exact ⟨w, hwN, by simpa using h.pushUp.lt_of_lt_of_le hwy hyx⟩

/-- `prop:K_densite_sing` with the paper's hypotheses (strong causality carried, unused). -/
theorem K_densite_sing_of_stronglyCausal (h : C.SingularFlatAxioms sing)
    (_hSC : C.StronglyCausal) (x : M) :
    C.Jplus ⊤ {x} ⊆ closure (C.Kplus ⊤ {x}) ∧ C.Jminus ⊤ {x} ⊆ closure (C.Kminus ⊤ {x}) :=
  h.K_densite_sing x

/-! ### `cor:K_ordre` -/

/-- `cor:K_ordre`: on a globally hyperbolic `E_{≥0}`-manifold, `x ≤ y ↔ K^-(x) ⊂ K^-(y)` and
`x ≤ y ↔ K^+(y) ⊂ K^+(x)`; `K^-` is an order isomorphism onto its image and `K^+` an
anti-isomorphism (both injective). -/
theorem K_ordre (h : C.SingularFlatAxioms sing) (hG : C.GloballyHyperbolic) :
    (∀ x y, C.le ⊤ x y ↔ C.Kminus ⊤ {x} ⊆ C.Kminus ⊤ {y}) ∧
    (∀ x y, C.le ⊤ x y ↔ C.Kplus ⊤ {y} ⊆ C.Kplus ⊤ {x}) ∧
    Function.Injective (fun x => C.Kminus ⊤ {x}) ∧
    Function.Injective (fun x => C.Kplus ⊤ {x}) := by
  haveI := h.t2
  have hemb := K_order_embedding (hG.isClosed_Jplus_singleton h.tarentin)
    (hG.isClosed_Jminus_singleton h.tarentin) (fun x => (h.K_densite_sing x).1)
    (fun x => (h.K_densite_sing x).2)
  exact ⟨hemb.2.2.2.1 fun _ _ hqp => (h.K_monotone hG.1 hqp).1,
    hemb.2.2.2.2 fun _ _ hqp => (h.K_monotone hG.1 hqp).2, (hemb.2.2.1 hG.1).1,
    (hemb.2.2.1 hG.1).2⟩

end SingularFlatAxioms

/-! ### `lem:cup_cap_BTZ` -/

/-- `lem:cup_cap_BTZ`, `⊇`, at a point with `SingularPastAt p`: no hypothesis on `M`, and
`p ∉ J^-(p_n)` is not used. -/
theorem SingularPastAt.Jminus_diff_subset_iUnion_iInter (hS : C.SingularPastAt p) {u : ℕ → M}
    (hu : Tendsto u atTop (𝓝 p)) :
    C.Jminus ⊤ {p} \ {p} ⊆ ⋃ N : ℕ, ⋂ n ≥ N, C.Jminus ⊤ {u n} := by
  rintro z ⟨hzJ, hzne⟩
  obtain ⟨v, -, -, hint, hz0⟩ := hS.2 z (by simpa using hzJ) hzne
  have hzv : C.le ⊤ z (v 0) := by simpa using interiorWithin_subset hz0
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hu.eventually (isOpen_interior.mem_nhds (hint 0)))
  refine mem_iUnion.2 ⟨N, ?_⟩
  simp only [mem_iInter]
  intro n hn
  have hvu : C.le ⊤ (v 0) (u n) := by simpa using interior_subset (hN n hn)
  simpa using C.le_trans hzv hvu

/-- `lem:cup_cap_BTZ`, `⊂`, when the causal futures of points are closed. -/
theorem iUnion_iInter_subset_Jminus_diff (hJ : ∀ z, IsClosed (C.Jplus ⊤ {z})) {u : ℕ → M}
    (hu : Tendsto u atTop (𝓝 p)) (hp : ∀ n, ¬ C.le ⊤ p (u n)) :
    ⋃ N : ℕ, ⋂ n ≥ N, C.Jminus ⊤ {u n} ⊆ C.Jminus ⊤ {p} \ {p} := by
  intro z hz
  obtain ⟨N, hN⟩ := mem_iUnion.1 hz
  simp only [mem_iInter] at hN
  have hzu : ∀ n ≥ N, C.le ⊤ z (u n) := fun n hn => by simpa using hN n hn
  have hev : ∀ᶠ n in atTop, u n ∈ C.Jplus ⊤ {z} :=
    eventually_atTop.2 ⟨N, fun n hn => by simpa using hzu n hn⟩
  have hpz : p ∈ C.Jplus ⊤ {z} := (hJ z).mem_of_tendsto hu hev
  refine ⟨by simpa using hpz, fun hzp => ?_⟩
  rw [mem_singleton_iff] at hzp
  subst hzp
  exact hp N (hzu N le_rfl)

/-- `lem:cup_cap_BTZ` when causal futures are closed (⚠ weakened from global hyperbolicity,
DEC-19; the printed "strongly causal" does not give it, see SCOPE). -/
theorem cup_cap_BTZ_of_isClosed (hS : C.SingularPastAt p) (hJ : ∀ z, IsClosed (C.Jplus ⊤ {z}))
    {u : ℕ → M} (hu : Tendsto u atTop (𝓝 p)) (hp : ∀ n, ¬ C.le ⊤ p (u n)) :
    ⋃ N : ℕ, ⋂ n ≥ N, C.Jminus ⊤ {u n} = C.Jminus ⊤ {p} \ {p} :=
  Subset.antisymm (iUnion_iInter_subset_Jminus_diff hJ hu hp)
    (hS.Jminus_diff_subset_iUnion_iInter hu)

/-- `lem:cup_cap_BTZ` on a globally hyperbolic `E_{≥0}`-manifold, as the author ruled it is stated
(DEC-19), the setting of its use (`ETT.tex:2122`). -/
theorem SingularFlatAxioms.cup_cap_BTZ {sing : ℝ → Set M} (h : C.SingularFlatAxioms sing)
    (hG : C.GloballyHyperbolic) (hp0 : p ∈ sing 0) {u : ℕ → M} (hu : Tendsto u atTop (𝓝 p))
    (hp : ∀ n, ¬ C.le ⊤ p (u n)) :
    ⋃ N : ℕ, ⋂ n ≥ N, C.Jminus ⊤ {u n} = C.Jminus ⊤ {p} \ {p} := by
  haveI := h.t2
  exact cup_cap_BTZ_of_isClosed (h.singularPastAt p hp0)
    (hG.isClosed_Jplus_singleton h.tarentin) hu hp

end Causality

/-! ### Satisfiability -/

section Witness

open Causality

/-- **Witness.** The timelike line, with no singular point, satisfies the whole structure. -/
theorem timelikeLine_singularFlatAxioms : timelikeLine.SingularFlatAxioms (fun _ => ∅) where
  singularPastAt _ hp := hp.elim
  Iminus_eq_empty _ hp := hp.elim
  Iplus_eq _ hp := hp.elim
  past_local _ hp := hp.elim
  line _ hp := hp.elim
  pushUp := timelikeLine_pushUp
  absolutelyMinimal := timelikeLine_absolutelyMinimal
  causallyArcConnected := timelikeLine_causallyArcConnected
  tarentin := timelikeLine_tarentin
  mem_Zplus := timelikeLine_mem_Zplus
  mem_Zminus_iff p := ⟨fun _ => notMem_empty p, fun _ => timelikeLine_mem_Zminus p⟩
  t2 := inferInstance
  secondCountable := inferInstance
  metrizable := inferInstance
  locallyCompact := inferInstance
  noIsolated _ := inferInstance
  isClosed_sing _ _ := isClosed_empty
  interior_sing _ _ := interior_empty
  massive_line _ _ _ hp := hp.elim

/-- A causal curve of the lightlike line: a continuous non-decreasing map (the relation is the
one of the timelike line). -/
theorem lightlikeLine_causalCurveOn_of_monotone {f : ℝ → ℝ} (hf : Monotone f)
    (hc : Continuous f) (a b : ℝ) : lightlikeLine.CausalCurveOn ⊤ f a b :=
  timelikeLine_causalCurveOn_of_monotone hf hc a b

/-- **Witness.** The lightlike line, every point a BTZ point, satisfies `BTZAxioms`: a BTZ line
with empty chronological pasts and futures. -/
theorem lightlikeLine_btzAxioms : lightlikeLine.BTZAxioms (univ : Set ℝ) where
  singularPastAt p _ := (lightlikeLine_singularPastAt p).1
  Iminus_eq_empty _ _ := by ext; simp
  Iplus_eq _ _ := by ext; simp
  past_local _ _ := ⟨⊤, trivial, fun _ _ => trivial⟩
  line p _ := by
    refine ⟨fun t => p + t, by simp, fun _ => (Homeomorph.addLeft p).isClosedEmbedding, ⟨⟨⟨0, trivial⟩,
      ordConnected_univ, fun a _ b _ => lightlikeLine_causalCurveOn_of_monotone
        (fun _ _ h => by simpa using h) (continuous_const.add continuous_id) a b⟩,
      fun ⟨_, c', _, _, ⟨t', _, hgrow⟩⟩ => hgrow (c' t' - p) trivial (by ring)⟩, ?_⟩
    rw [connectedComponentIn_univ, PreconnectedSpace.connectedComponent_eq_univ]
    exact eq_univ_of_forall fun y => ⟨y - p, by ring⟩

/-- The timelike line carries the structure only with `sing 0 = ∅`: every point is strongly
tarentin in the past. -/
theorem timelikeLine_sing_zero {sing : ℝ → Set ℝ} (h : timelikeLine.SingularFlatAxioms sing) :
    sing 0 = ∅ :=
  eq_empty_of_forall_notMem fun p => (h.mem_Zminus_iff p).1 (timelikeLine_mem_Zminus p)

/-- The lightlike line does not carry the structure: no point is strongly tarentin in the
future. -/
theorem lightlikeLine_not_mem_Zplus (p : ℝ) : p ∉ lightlikeLine.Zplus := by
  intro h
  obtain ⟨y, hy⟩ := Iplus_nonempty_of_mem_Zplus h
  simp at hy

/-- **Witness of `past_BTZ_b`**: on the timelike line, `id` over `ℝ` meets no singular point. -/
theorem timelikeLine_past_BTZ_b :
    (∀ s ∈ (univ : Set ℝ), ∀ s' ∈ (univ : Set ℝ), s' ≤ s →
      id s ∈ ((fun _ => (∅ : Set ℝ)) : ℝ → Set ℝ) 0 → id s' ∈ ((fun _ => (∅ : Set ℝ)) : ℝ → Set ℝ) 0) ∧
    id '' univ = (id '' univ ∩ ((fun _ => (∅ : Set ℝ)) : ℝ → Set ℝ) 0) ∪
      (id '' univ \ ((fun _ => (∅ : Set ℝ)) : ℝ → Set ℝ) 0) ∧
    IsPreconnected (id '' univ ∩ ((fun _ => (∅ : Set ℝ)) : ℝ → Set ℝ) 0) ∧
    IsPreconnected (id '' univ \ ((fun _ => (∅ : Set ℝ)) : ℝ → Set ℝ) 0) ∧
    closure (id '' univ ∩ ((fun _ => (∅ : Set ℝ)) : ℝ → Set ℝ) 0) ∩ id '' univ ⊆
      id '' univ ∩ ((fun _ => (∅ : Set ℝ)) : ℝ → Set ℝ) 0 ∧
    ∀ x ∈ id '' univ ∩ ((fun _ => (∅ : Set ℝ)) : ℝ → Set ℝ) 0,
      ∀ y ∈ id '' univ \ ((fun _ => (∅ : Set ℝ)) : ℝ → Set ℝ) 0, timelikeLine.le ⊤ x y :=
  timelikeLine_singularFlatAxioms.past_BTZ_b timelikeLine_inextensible_id.1

/-- **Witness of `K_injectif`**: its hypotheses hold on the timelike line. -/
theorem timelikeLine_K_injectif :
    Function.Injective (fun x : ℝ => timelikeLine.Kplus ⊤ {x}) ∧
      Function.Injective (fun x : ℝ => timelikeLine.Kminus ⊤ {x}) :=
  timelikeLine_singularFlatAxioms.K_injectif timelikeLine_stronglyCausal

/-- **Witness of `K_densite_sing`**. -/
theorem timelikeLine_K_densite_sing (x : ℝ) :
    timelikeLine.Jplus ⊤ {x} ⊆ closure (timelikeLine.Kplus ⊤ {x}) ∧
      timelikeLine.Jminus ⊤ {x} ⊆ closure (timelikeLine.Kminus ⊤ {x}) :=
  timelikeLine_singularFlatAxioms.K_densite_sing_of_stronglyCausal timelikeLine_stronglyCausal x

/-- **Witness of `K_ordre`**. -/
theorem timelikeLine_K_ordre :
    (∀ x y : ℝ, timelikeLine.le ⊤ x y ↔ timelikeLine.Kminus ⊤ {x} ⊆ timelikeLine.Kminus ⊤ {y}) ∧
    (∀ x y : ℝ, timelikeLine.le ⊤ x y ↔ timelikeLine.Kplus ⊤ {y} ⊆ timelikeLine.Kplus ⊤ {x}) ∧
    Function.Injective (fun x : ℝ => timelikeLine.Kminus ⊤ {x}) ∧
    Function.Injective (fun x : ℝ => timelikeLine.Kplus ⊤ {x}) :=
  timelikeLine_singularFlatAxioms.K_ordre timelikeLine_globallyHyperbolic

/-- **Witness of `cup_cap_BTZ_of_isClosed`**, at a BTZ point of the lightlike line, with
`p_n = p - 1/(n+1)`: both sides are `]-∞, p[`. -/
theorem lightlikeLine_cup_cap_BTZ (p : ℝ) :
    ⋃ N : ℕ, ⋂ n ≥ N, lightlikeLine.Jminus ⊤ {p - 1 / ((n : ℝ) + 1)} =
      lightlikeLine.Jminus ⊤ {p} \ {p} := by
  refine cup_cap_BTZ_of_isClosed (lightlikeLine_singularPastAt p).1 (fun z => ?_)
    (tendsto_sub_div_nat p 1) (fun n hn => ?_)
  · have : lightlikeLine.Jplus ⊤ {z} = Ici z := by ext; simp
    rw [this]; exact isClosed_Ici
  · have h1 : p ≤ p - 1 / ((n : ℝ) + 1) := (lightlikeLine_le_top).1 hn
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith

end Witness

end Causal
