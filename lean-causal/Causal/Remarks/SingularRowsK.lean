import Causal.Port.SFAManifolds
import Causal.LinesReachable
import Causal.CauchyDiamond
import Causal.CurvesExtendSecondCountable

/-!
# The `K^±` rows of Section 3.3 at every `E_{≥0}`-manifold: the past of a BTZ point, the
injectivity, density and order of `K^±`, and the cup-cap formula at BTZ points (DEC-19)

Target `T-ett-singular-rows`. Cited, all unmarked (SCOPE): `lem:past_BTZ` (unmarked) —
`ETT.tex:1515`; `cor:K_injectif` (unmarked) — `ETT.tex:1575`; `prop:K_densite_sing` (unmarked) —
`ETT.tex:1634`; `cor:K_ordre` (unmarked) — `ETT.tex:1692`; `lem:cup_cap_BTZ` (unmarked) —
`ETT.tex:1825`, in DEC-19's globally hyperbolic form; `rem:K_plongement_hypotheses` (unmarked) —
`ETT.tex:951`, its hypothesis (b) discharged; `cor:K_ordre_Sigma` (unmarked) — `ETT.tex:2082`,
its hypothesis `hK` discharged.

For a singular `(Isom(𝐌³), 𝐌³)`-manifold `M` (DEC-25), Hausdorff and second countable, and every
absolutely minimal causality `C` with an isomorphic chart at each point over the family `E_{≥0}`
(`IsoChartsCoverDEC25 … massAModelCausality`; the natural causality is one), each theorem of
`Causal.SingularFlat` behind these rows is applied to `SFAManifolds.singularFlatAxioms`, with
`sing_α(M)` read as `SFALocal.sing M α` and the paper's own hypotheses (strong causality, global
hyperbolicity) carried. Beside them stand forms that drop what they do not use: Hausdorff, second
countability, and absolute minimality where the chart facts suffice.

> Let $M$ be a singular spacetime. Then (a) for every $\alpha\in \RR_+$, each connected component
> of $\sing_\alpha(M)$ is an inextensible causal curve; if $\alpha>0$, such a connected component
> is moreover chronal; (b) every causal curve $c$ of $M$ decomposes as $c=\Delta\cup c^0$ with
> $\Delta=c\cap \sing_0(M)$ and $c^0=c\setminus \sing_0(M)$. Moreover $\Delta$ and $c^0$ are
> connected, $\Delta$ is closed and lies in the past of $c^0$. (`lem:past_BTZ`,
> `ETT.tex:1516–1525`)

> If $M$ is a strongly causal $\mass{\geq 0}$-manifold, then the map $x\mapsto K^\pm(x)$ is
> injective. (`cor:K_injectif`, `ETT.tex:1575–1579`)

> Let $M$ be a strongly causal $\mass{\geq0}$-manifold. Then for every $x\in M$,
> $J^\pm(x)\subset \overline{K^\pm(x)}.$ (`prop:K_densite_sing`, `ETT.tex:1634–1637`)

> Let $M$ be a globally hyperbolic $\mass{\geq0}$-manifold. Then for all $x,y\in M$,
> $x\leq y \iff K^-(x)\subset K^-(y) \iff K^+(y)\subset K^+(x).$ In particular
> $x\mapsto K^-(x)$ is an isomorphism of ordered sets from $(M,\leq)$ onto its image in
> $\left(\mathcal P(M),\subset\right)$, and $x\mapsto K^+(x)$ is an anti-isomorphism onto its
> image. (`cor:K_ordre`, `ETT.tex:1692–1697`)

> Let $M$ be a strongly causal singular flat spacetime, let $p\in M$ and let $(p_n)_{n\in \N}$ be
> a sequence of $M$ converging to $p$. If $p \notin J^-(p_n)$ for every $n\in \N$ and if
> $p\in \sing_0(M)$, then $\bigcup_{N\in \N}\bigcap_{n\geq N} J^-(p_n)=J^-(p)\setminus \{p\}.$
> (`lem:cup_cap_BTZ`, `ETT.tex:1825–1830`; DEC-19 reads « globally hyperbolic » for « strongly
> causal »)

> Neither hypothesis can be dispensed with. Without $(a)$ one only gets
> $x\in \overline{J^-(y)}$; global hyperbolicity supplies $(a)$ through Proposition
> \ref{prop:GH_Jferme}. Hypothesis $(b)$ is where push-up enters: at a point which is strongly
> tarentin in the past and around which $M$ is causally plain, $K^-(x)=I^-(x)$ (Proposition
> \ref{prop:tarentin_fort_K}) and $(b)$ reads $J^-(x)\subset\overline{I^-(x)}$, the classical
> density of the chronological past in the causal past. Proposition \ref{prop:K_densite_sing}
> establishes $(b)$ for singular flat spacetimes --- including at BTZ points, where $I^-(x)$ is
> empty and only $K^-(x)$ can be dense. (`rem:K_plongement_hypotheses`, `ETT.tex:951–959`)

> Let $M$ be a globally hyperbolic singular flat spacetime, let $\Sigma$ be a Cauchy surface of
> $M$ and let $x,y\in J^+(\Sigma)\setminus \Sigma$. If
> $K^-(x)\cap J^+(\Sigma)\subset K^-(y)\cap J^+(\Sigma)$, then $x\leq y$. In particular
> $x\mapsto K^-(x)\cap J^+(\Sigma)$ is injective on $J^+(\Sigma)\setminus \Sigma$.
> (`cor:K_ordre_Sigma`, `ETT.tex:2082–2087`)

## What is proved (no `sorry` in this file)

* `lem:past_BTZ` (unmarked): (b) at every `E_{≥0}`-manifold, for every causality with an
  isomorphic chart at each point (`past_BTZ_b_local`: no absolute minimality, no separation, no
  countability), through the model-free `past_BTZ_b_of` (the paper's argument, from `past_local`
  and the closedness of `sing₀(M)`); (b) through the assembly (`past_BTZ_b`); (a) and (b)
  together at every Hausdorff `E_{≥0}`-manifold (`past_BTZ`; (a) is `SFALine.line` and
  `SFAMassiveLine.massive_line`).
* `cor:K_injectif` (unmarked): `K_injectif`, strong causality carried.
* `prop:K_densite_sing` (unmarked): `K_densite_sing` (strong causality not used),
  `K_densite_sing_of_stronglyCausal` (carried, unused), and `K_densite_sing_local`, with neither
  Hausdorff nor second countability: the proof of `SingularFlatAxioms.K_densite_sing` run on the
  chartwise and BTZ layers (`SFALocal.pushUp`, `SFABTZ.singularPastAt`, `SFABTZ.Iplus_of_lt`).
* `cor:K_ordre` (unmarked): `K_ordre`, global hyperbolicity carried; `K_ordre_of_t2`, without
  second countability (`K_densite_sing_local`, `SFABTZ.K_monotone`).
* `lem:cup_cap_BTZ` (unmarked), DEC-19: `cup_cap_BTZ` at every globally hyperbolic `M`;
  `cup_cap_BTZ_of_isClosed`, the closedness of every `J⁺(z)` in place of global hyperbolicity,
  with neither Hausdorff nor second countability. The printed strongly causal form is refuted at
  `E₀ ∖ {w}` (`CupCapBTZCounterexample.not_cupCapBTZAsPrinted`), not here.
* `rem:K_plongement_hypotheses` (unmarked): hypothesis (a) from global hyperbolicity
  (`hypothesis_a`) and hypothesis (b) at every point (`hypothesis_b`); at a point strongly
  tarentin in the past, `K⁻(x) = I⁻(x)` and the classical density `J⁻(x) ⊆ cl I⁻(x)`, `M` being
  causally plain (`hypothesis_b_tarentin`); at a BTZ point, `I⁻(x) = ∅`, so `I⁻(x)` is not dense in
  `J⁻(x)`, while `K⁻(x)` is (`hypothesis_b_btz`); the conclusion of `prop:K_plongement_ordre` at
  every globally hyperbolic `M` (`K_order_embedding`); assembled in `K_plongement_hypotheses`.
* `cor:K_ordre_Sigma` (unmarked): `K_ordre_Sigma`, `hK` discharged, `lem:Sigma_separe`'s
  neighbourhood fact `hS` named; `K_ordre_Sigma_of_splitting`, `Σ` a Cauchy surface and `hS` from
  `Causality.sigma_separe` under the splitting `ψ` of `theo:geroch_sing` (named,
  `IsCauchySplitting`), `Σ` acausal by `IsCauchySurface.isAcausal_of_t1_secondCountable`. A
  non-vacuous `S` for `hS`: `J⁺(q) ∖ I⁺(q)` for a BTZ point `q` (`btz_cone_shell`, from the
  model-free `cone_shell`).
* **The natural causality** (`IsAtlasCausalityDEC25`): the rows at once,
  `rows_of_isAtlasCausalityDEC25`.
* **Witnesses** (kb/0011), each conclusion out of this file's theorems (except
  `nonvacuous_e0_certificate`, which applies the strict certificate): `nonvacuous_e0` (`E₀`,
  `sing₀ = axis ≠ ∅`, strongly causal, globally hyperbolic: (a) on the axis, the three `K` rows,
  hypothesis (b) at the axis points), `nonvacuous_e0_plongement` (the assembly of
  `rem:K_plongement_hypotheses` at `E₀`), `nonvacuous_e0_past` (a causal curve of `E₀` from the axis
  to a regular point, both parts of (b) non-empty), `nonvacuous_e0_cup_cap` (`lem:cup_cap_BTZ` at
  the BTZ point `(0, 0)`, along the axis from below: `SingularFlatAxioms.cup_cap_BTZ` instantiated
  with a BTZ point), `nonvacuous_e0_certificate` (the certificate of record,
  `Causality.cupCapBTZAsPrinted_of_globallyHyperbolic`, at `E₀`, its antecedents holding),
  `nonvacuous_e0_Sigma` (`cor:K_ordre_Sigma` with `S = J⁺(q) ∖ I⁺(q)`,
  `J⁺(S) ∖ S = I⁺(q) ≠ ∅`), `nonvacuous_e0_natural` (`E₀` with its natural causality over the
  family), `nonvacuous_epi` (`E_π`, `sing_π ≠ ∅`: the massive line and the three `K` rows).

## Hypothesis checklist

| paper | here |
|---|---|
| singular spacetime, `E_{≥0}`-manifold, singular flat spacetime | ⚠ read (DEC-25, OQ-18): `[SingularGXStructure (Flat.isom 2) (Minkowski 2) M]`, `C` absolutely minimal with `IsoChartsCoverDEC25` over `massAModelCausality`; the natural causality in `rows_of_isAtlasCausalityDEC25` |
| — Hausdorff, second countable (« manifold », `ETT.tex:254`) | ✓ carried by the assembly forms; ⚠ weakened: `past_BTZ_b_local`, `K_densite_sing_local`, `hypothesis_b_tarentin`, `hypothesis_b_btz`, `cup_cap_BTZ_of_isClosed` use neither; `past_BTZ`, `K_ordre_of_t2`, `hypothesis_a` use Hausdorff only |
| — connected (l.1502) | ⚠ weakened: not used |
| — absolute minimality (OQ-18's reading of the causality) | ⚠ weakened: `past_BTZ_b_local`, `past_BTZ`, `hypothesis_a` do not use it |
| `lem:past_BTZ` (a): « an inextensible causal curve », chronal if `α > 0` | ✓ the component through `p` is the range of an inextensible causal curve `γ : ℝ → M`, `γ 0 = p`, chronal for `α > 0`; ✓ with a stronger conclusion: a closed embedding when `C` is causal |
| `lem:past_BTZ` (b): « every causal curve `c` of `M` » | ⚠ weakened: causal curves of any open `W` over any interval `I`; « connected » read `IsPreconnected`, « closed » closed in `c(I)`, « in the past » `≤_W` |
| `cor:K_injectif`: strongly causal | ✓ carried (DEC-7's `StronglyCausal`) |
| `prop:K_densite_sing`: strongly causal | ⚠ weakened: not used (carried, unused, by `K_densite_sing_of_stronglyCausal`) |
| `cor:K_ordre`: globally hyperbolic | ✓ carried; « isomorphism of ordered sets onto its image » read as the two equivalences and injectivity |
| `lem:cup_cap_BTZ`: strongly causal (as printed) | ✓ carried as ruled (DEC-19): globally hyperbolic; ⚠ weakened: `J⁺(z)` closed for every `z` (`cup_cap_BTZ_of_isClosed`) |
| `rem:K_plongement_hypotheses`: « around which `M` is causally plain » | ✓ discharged: every `E_{≥0}`-manifold is causally plain (`SFALocal.causallyPlain`) |
| `rem:K_plongement_hypotheses`: « strongly tarentin in the past » | ✓ carried, `x ∈ C.Zminus` |
| `cor:K_ordre_Sigma`: `Σ` a Cauchy surface | ⚠ weakened in `K_ordre_Sigma`: any `S` with `hS` (named, `lem:Sigma_separe`); ✓ carried by `K_ordre_Sigma_of_splitting`, with the `ψ` of `theo:geroch_sing` named (⚠ strengthened: a named hypothesis) |
| `E₀`, `Isom(E^{1,2})` | ⚠ read: `Causal.E0` (OQ-34, OQ-35), `Flat.isom 2` (OQ-82) |

## SCOPE (disclosed)

* **Why unmarked.** Every row rests on the readings DEC-25 (the manifolds), OQ-18 (the causality
  of a singular spacetime), OQ-34/OQ-35 (`E₀`) and OQ-82 (the group). `lem:cup_cap_BTZ` is stated
  in DEC-19's form. `cor:K_ordre_Sigma` keeps `lem:Sigma_separe`'s neighbourhood fact, or the
  splitting `ψ` of `theo:geroch_sing`, as a named hypothesis: `theo:geroch_sing` is not proved at
  `M`. The first sentence of `rem:K_plongement_hypotheses` (« neither hypothesis can be dispensed
  with ») is certified by the counterexamples of `Causal.LinesReachable`, not at
  `E_{≥0}`-manifolds, and its « around which `M` is causally plain » by global plainness there.
* **`sing_α(M)`** is `SFALocal.sing M α` (brunswic2021cauchy Cor. 1.5), as in `Causal.SFALocal`.
* **The witness of `cor:K_ordre_Sigma`** at `E₀` takes `S = J⁺(q) ∖ I⁺(q)`, which is not a Cauchy
  surface: `K_ordre_Sigma` does not ask for one. `K_ordre_Sigma_of_splitting` is instantiated at `E₀`
  in `Causal.Remarks.SingularRowsSplitting` (`nonvacuous_e0`, the τ-flow splitting), and the
  form for every Cauchy surface is `Causal.SingularRowsCauchy.K_ordre_Sigma`.
* **Witnesses.** `E₀` has BTZ points only and `E_π` massive points only; no witness has points of
  both kinds (`Causal.SFALocal` SCOPE).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Imports the strict
`Causal.Port.SFAManifolds`, `Causal.LinesReachable` (`K_order_embedding_of_globallyHyperbolic`),
`Causal.CauchyDiamond` (`sigma_separe`) and `Causal.CurvesExtendSecondCountable`
(`IsCauchySurface.isAcausal_of_t1_secondCountable`).
-/

namespace Causal

open Set Filter Topology TopologicalSpace

universe u

namespace SingularRowsK

/-! ### Model-free lemmas -/

section General

variable {M : Type u} [TopologicalSpace M] {C : Causality M}

/-- `lem:past_BTZ` (b), model-free: if `S₀` is closed and, at each of its points, the past in some
open set stays in `S₀`, then along a causal curve `c` of `W` over an interval `I` the parameters
mapped into `S₀` form an initial segment of `I`, `c(I) ∩ S₀` and `c(I) ∖ S₀` are preconnected,
`c(I) ∩ S₀` is closed in `c(I)` and lies in the past (in `W`) of `c(I) ∖ S₀`. The proof of
`Causality.SingularFlatAxioms.past_BTZ_b`, whose only uses of the structure are these two facts
(`ETT.tex:1534–1554`). -/
theorem past_BTZ_b_of {S₀ : Set M} (hS : IsClosed S₀)
    (hloc : ∀ p ∈ S₀, ∃ U : Opens M, p ∈ U ∧ ∀ q, C.le U q p → q ∈ S₀)
    {W : Opens M} {I : Set ℝ} {c : ℝ → M} (hc : C.CausalCurveIn W I c) :
    (∀ s ∈ I, ∀ s' ∈ I, s' ≤ s → c s ∈ S₀ → c s' ∈ S₀) ∧
    c '' I = (c '' I ∩ S₀) ∪ (c '' I \ S₀) ∧
    IsPreconnected (c '' I ∩ S₀) ∧ IsPreconnected (c '' I \ S₀) ∧
    closure (c '' I ∩ S₀) ∩ c '' I ⊆ c '' I ∩ S₀ ∧
    ∀ x ∈ c '' I ∩ S₀, ∀ y ∈ c '' I \ S₀, C.le W x y := by
  have hseg : ∀ s ∈ I, ∀ s' ∈ I, s' ≤ s → c s ∈ S₀ → c s' ∈ S₀ :=
    fun s hs s' hs' hle hcs =>
      Causality.mem_of_causalCurveOn hS hloc (hc.curve s' hs' s hs) le_rfl hle le_rfl hcs
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
    have : x ∈ closure S₀ := closure_mono inter_subset_right hx
    rw [hS.closure_eq] at this
    exact ⟨hxI, this⟩
  · rintro _ ⟨⟨σ, hσ, rfl⟩, hσS⟩ _ ⟨⟨τ, hτ, rfl⟩, hτS⟩
    rcases le_or_gt σ τ with hστ | hτσ
    · exact hc.le_of_le hσ hτ hστ
    · exact absurd (hseg σ hσ τ hτ hτσ.le hσS) hτS

/-- A cheap set for `cor:K_ordre_Sigma`'s neighbourhood hypothesis, model-free: if `q ≪ q` fails,
`S := J⁺(q) ∖ I⁺(q)` has `J⁺(S) = J⁺(q)`, `J⁺(S) ∖ S = I⁺(q)`, and `J⁺(S)` is a neighbourhood of
each point of `J⁺(S) ∖ S` (`I⁺(q)` is open). -/
theorem cone_shell {q : M} (hq : ¬ C.lt ⊤ q q) :
    C.Jplus ⊤ (C.Jplus ⊤ {q} \ C.Iplus ⊤ {q}) \ (C.Jplus ⊤ {q} \ C.Iplus ⊤ {q}) =
        C.Iplus ⊤ {q} ∧
      ∀ x ∈ C.Jplus ⊤ (C.Jplus ⊤ {q} \ C.Iplus ⊤ {q}) \ (C.Jplus ⊤ {q} \ C.Iplus ⊤ {q}),
        C.Jplus ⊤ (C.Jplus ⊤ {q} \ C.Iplus ⊤ {q}) ∈ 𝓝 x := by
  have hqS : q ∈ C.Jplus ⊤ {q} \ C.Iplus ⊤ {q} :=
    ⟨Precausality.mem_Jplus_singleton.2 (C.le_refl trivial),
      fun h => hq (Precausality.mem_Iplus_singleton.1 h)⟩
  have hJ : C.Jplus ⊤ (C.Jplus ⊤ {q} \ C.Iplus ⊤ {q}) = C.Jplus ⊤ {q} := by
    apply Subset.antisymm
    · rintro y ⟨s, ⟨hs, -⟩, hsy⟩
      exact Precausality.mem_Jplus_singleton.2
        (C.le_trans (Precausality.mem_Jplus_singleton.1 hs) hsy)
    · exact Precausality.Jplus_mono (singleton_subset_iff.2 hqS)
  have hIJ : C.Iplus ⊤ {q} ⊆ C.Jplus ⊤ {q} := fun y hy =>
    Precausality.mem_Jplus_singleton.2 (C.le_of_lt (Precausality.mem_Iplus_singleton.1 hy))
  have heq : C.Jplus ⊤ (C.Jplus ⊤ {q} \ C.Iplus ⊤ {q}) \ (C.Jplus ⊤ {q} \ C.Iplus ⊤ {q}) =
      C.Iplus ⊤ {q} := by
    rw [hJ, sdiff_sdiff_cancel_left hIJ]
  refine ⟨heq, fun x hx => ?_⟩
  rw [heq] at hx
  rw [hJ]
  exact Filter.mem_of_superset (C.isOpen_Iplus.mem_nhds hx) hIJ

end General

section Manifold

variable {M : Type u} [TopologicalSpace M] [SingularGXStructure (Flat.isom 2) (Minkowski 2) M]
  {C : Causality M}

/-! ### `lem:past_BTZ` -/

/-- `lem:past_BTZ` (b) at every `E_{≥0}`-manifold (unmarked), for every causality with an isomorphic
chart at each point: no absolute minimality, no separation axiom, no countability. `past_local`
is `SFALocal.pastLocal`, the closedness of `sing₀(M)` is `SFALine.isClosed_sing_zero`. -/
theorem past_BTZ_b_local
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    {W : Opens M} {I : Set ℝ} {c : ℝ → M} (hc : C.CausalCurveIn W I c) :
    (∀ s ∈ I, ∀ s' ∈ I, s' ≤ s → c s ∈ SFALocal.sing M 0 → c s' ∈ SFALocal.sing M 0) ∧
    c '' I = (c '' I ∩ SFALocal.sing M 0) ∪ (c '' I \ SFALocal.sing M 0) ∧
    IsPreconnected (c '' I ∩ SFALocal.sing M 0) ∧ IsPreconnected (c '' I \ SFALocal.sing M 0) ∧
    closure (c '' I ∩ SFALocal.sing M 0) ∩ c '' I ⊆ c '' I ∩ SFALocal.sing M 0 ∧
    ∀ x ∈ c '' I ∩ SFALocal.sing M 0, ∀ y ∈ c '' I \ SFALocal.sing M 0, C.le W x y :=
  past_BTZ_b_of (SFALine.isClosed_sing_zero hC) (SFALocal.pastLocal hC) hc

/-- `lem:past_BTZ` (b) at every Hausdorff, second countable `E_{≥0}`-manifold (unmarked): the
`SingularFlatAxioms` form `Causality.SingularFlatAxioms.past_BTZ_b` applied to
`SFAManifolds.singularFlatAxioms`. -/
theorem past_BTZ_b [T2Space M] [SecondCountableTopology M] (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    {W : Opens M} {I : Set ℝ} {c : ℝ → M} (hc : C.CausalCurveIn W I c) :
    (∀ s ∈ I, ∀ s' ∈ I, s' ≤ s → c s ∈ SFALocal.sing M 0 → c s' ∈ SFALocal.sing M 0) ∧
    c '' I = (c '' I ∩ SFALocal.sing M 0) ∪ (c '' I \ SFALocal.sing M 0) ∧
    IsPreconnected (c '' I ∩ SFALocal.sing M 0) ∧ IsPreconnected (c '' I \ SFALocal.sing M 0) ∧
    closure (c '' I ∩ SFALocal.sing M 0) ∩ c '' I ⊆ c '' I ∩ SFALocal.sing M 0 ∧
    ∀ x ∈ c '' I ∩ SFALocal.sing M 0, ∀ y ∈ c '' I \ SFALocal.sing M 0, C.le W x y :=
  (SFAManifolds.singularFlatAxioms hmin hC).past_BTZ_b hc

/-- `lem:past_BTZ` at every Hausdorff `E_{≥0}`-manifold (unmarked), (a) and (b): through every
point of `sing₀(M)` an inextensible causal curve `γ : ℝ → M` onto its component, a closed embedding
when `C` is causal (`SFALine.line`); through every point of `sing_α(M)`, `α > 0`, an inextensible
causal curve, chronal over every segment, onto its component (`SFAMassiveLine.massive_line`); and
(b) for every causal curve of every open set over every interval (`past_BTZ_b_local`). Neither
absolute minimality nor second countability is used. -/
theorem past_BTZ [T2Space M]
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) :
    (∀ p ∈ SFALocal.sing M 0, ∃ γ : ℝ → M, γ 0 = p ∧ (C.IsCausal → IsClosedEmbedding γ) ∧
      C.Inextensible ⊤ univ γ ∧ range γ = connectedComponentIn (SFALocal.sing M 0) p) ∧
    (∀ α : ℝ, 0 < α → ∀ p ∈ SFALocal.sing M α, ∃ γ : ℝ → M, γ 0 = p ∧
      (C.IsCausal → IsClosedEmbedding γ) ∧ C.Inextensible ⊤ univ γ ∧
      (∀ a b, C.ChronalCurveOn ⊤ γ a b) ∧ range γ = connectedComponentIn (SFALocal.sing M α) p) ∧
    ∀ (W : Opens M) (I : Set ℝ) (c : ℝ → M), C.CausalCurveIn W I c →
      (∀ s ∈ I, ∀ s' ∈ I, s' ≤ s → c s ∈ SFALocal.sing M 0 → c s' ∈ SFALocal.sing M 0) ∧
      c '' I = (c '' I ∩ SFALocal.sing M 0) ∪ (c '' I \ SFALocal.sing M 0) ∧
      IsPreconnected (c '' I ∩ SFALocal.sing M 0) ∧ IsPreconnected (c '' I \ SFALocal.sing M 0) ∧
      closure (c '' I ∩ SFALocal.sing M 0) ∩ c '' I ⊆ c '' I ∩ SFALocal.sing M 0 ∧
      ∀ x ∈ c '' I ∩ SFALocal.sing M 0, ∀ y ∈ c '' I \ SFALocal.sing M 0, C.le W x y :=
  ⟨SFALine.line hC, SFAMassiveLine.massive_line hC, fun _ _ _ hc => past_BTZ_b_local hC hc⟩

/-! ### `cor:K_injectif` -/

/-- `cor:K_injectif` at every strongly causal, Hausdorff, second countable `E_{≥0}`-manifold
(unmarked): `x ↦ K⁺(x)` and `x ↦ K⁻(x)` are injective. `Causality.SingularFlatAxioms.K_injectif`
applied to `SFAManifolds.singularFlatAxioms`. -/
theorem K_injectif [T2Space M] [SecondCountableTopology M] (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hSC : C.StronglyCausal) :
    Function.Injective (fun x => C.Kplus ⊤ {x}) ∧ Function.Injective (fun x => C.Kminus ⊤ {x}) :=
  (SFAManifolds.singularFlatAxioms hmin hC).K_injectif hSC

/-! ### `prop:K_densite_sing` -/

/-- `prop:K_densite_sing` at every Hausdorff, second countable `E_{≥0}`-manifold (unmarked):
`J^±(x) ⊆ cl K^±(x)` for every `x`. `Causality.SingularFlatAxioms.K_densite_sing` applied to
`SFAManifolds.singularFlatAxioms`; strong causality is not used. -/
theorem K_densite_sing [T2Space M] [SecondCountableTopology M] (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) (x : M) :
    C.Jplus ⊤ {x} ⊆ closure (C.Kplus ⊤ {x}) ∧ C.Jminus ⊤ {x} ⊆ closure (C.Kminus ⊤ {x}) :=
  (SFAManifolds.singularFlatAxioms hmin hC).K_densite_sing x

/-- `prop:K_densite_sing` with the paper's hypothesis, strong causality, carried and unused. -/
theorem K_densite_sing_of_stronglyCausal [T2Space M] [SecondCountableTopology M]
    (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hSC : C.StronglyCausal) (x : M) :
    C.Jplus ⊤ {x} ⊆ closure (C.Kplus ⊤ {x}) ∧ C.Jminus ⊤ {x} ⊆ closure (C.Kminus ⊤ {x}) :=
  (SFAManifolds.singularFlatAxioms hmin hC).K_densite_sing_of_stronglyCausal hSC x

/-- `prop:K_densite_sing` at every `E_{≥0}`-manifold (unmarked), with neither Hausdorff nor second
countability: the proof of `Causality.SingularFlatAxioms.K_densite_sing` on the chartwise and BTZ
layers. First countability comes from the charts, push-up and `Z^±` from `SFALocal`; a BTZ
`y ≤ x`, `x` regular, is the limit of the points `u_n < y` of its line (`SFABTZ.singularPastAt`),
each `≪ x` by `SFABTZ.Iplus_of_lt` (DEC-64). -/
theorem K_densite_sing_local (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) (x : M) :
    C.Jplus ⊤ {x} ⊆ closure (C.Kplus ⊤ {x}) ∧ C.Jminus ⊤ {x} ⊆ closure (C.Kminus ⊤ {x}) := by
  haveI := SFABTZ.firstCountableTopology_of_isoChartsCover hC
  have hP := SFALocal.pushUp hmin hC
  constructor
  · rw [hP.Kplus_eq_Iplus (SFALocal.mem_Zplus hC x)]
    intro y hy
    have hxy : C.le ⊤ x y := Precausality.mem_Jplus_singleton.1 hy
    rw [mem_closure_iff_nhds]
    intro N hN
    obtain ⟨w, hw, hwN⟩ := SFALocal.mem_Zplus hC y N hN
    have hyw : C.lt ⊤ y w := Precausality.mem_Iplus_singleton.1 hw
    exact ⟨w, hwN, Precausality.mem_Iplus_singleton.2 (hP.lt_of_le_of_lt hxy hyw)⟩
  · by_cases hx : x ∈ SFALocal.sing M 0
    · have hS := SFABTZ.singularPastAt hmin hC x hx
      intro y hy
      by_cases hyx : y = x
      · subst hyx
        exact closure_mono hS.Jminus_diff_subset_Kminus hS.mem_closure
      · exact subset_closure (hS.Jminus_diff_subset_Kminus ⟨hy, hyx⟩)
    · rw [hP.Kminus_eq_Iminus (SFALocal.mem_Zminus_of_notMem hC hx)]
      intro y hy
      have hyx : C.le ⊤ y x := Precausality.mem_Jminus_singleton.1 hy
      by_cases hyS : y ∈ SFALocal.sing M 0
      · obtain ⟨u, hu, hup⟩ := (SFABTZ.singularPastAt hmin hC y hyS).1
        refine mem_closure_of_tendsto hu (Eventually.of_forall fun n => ?_)
        have huS := SFABTZ.mem_sing_zero_of_le hmin hC hyS (hup n).1
        have h := SFABTZ.Iplus_of_lt hmin hC (u n) huS y hyS (hup n).1 (hup n).2
          ⟨Precausality.mem_Jplus_singleton.2 hyx, hx⟩
        exact Precausality.mem_Iminus_singleton.2 (Precausality.mem_Iplus_singleton.1 h)
      · rw [mem_closure_iff_nhds]
        intro N hN
        obtain ⟨w, hw, hwN⟩ := SFALocal.mem_Zminus_of_notMem hC hyS N hN
        have hwy : C.lt ⊤ w y := Precausality.mem_Iminus_singleton.1 hw
        exact ⟨w, hwN, Precausality.mem_Iminus_singleton.2 (hP.lt_of_lt_of_le hwy hyx)⟩

/-! ### `cor:K_ordre` -/

/-- `cor:K_ordre` at every globally hyperbolic, Hausdorff, second countable `E_{≥0}`-manifold
(unmarked): `x ≤ y ↔ K⁻(x) ⊆ K⁻(y) ↔ K⁺(y) ⊆ K⁺(x)`, and both maps injective.
`Causality.SingularFlatAxioms.K_ordre` applied to `SFAManifolds.singularFlatAxioms`. -/
theorem K_ordre [T2Space M] [SecondCountableTopology M] (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hG : C.GloballyHyperbolic) :
    (∀ x y, C.le ⊤ x y ↔ C.Kminus ⊤ {x} ⊆ C.Kminus ⊤ {y}) ∧
    (∀ x y, C.le ⊤ x y ↔ C.Kplus ⊤ {y} ⊆ C.Kplus ⊤ {x}) ∧
    Function.Injective (fun x => C.Kminus ⊤ {x}) ∧ Function.Injective (fun x => C.Kplus ⊤ {x}) :=
  (SFAManifolds.singularFlatAxioms hmin hC).K_ordre hG

/-- `cor:K_ordre` at every globally hyperbolic Hausdorff `E_{≥0}`-manifold, without second
countability: `prop:K_plongement_ordre` with (a) from global hyperbolicity, (b) from
`K_densite_sing_local`, monotonicity from `SFABTZ.K_monotone`. -/
theorem K_ordre_of_t2 [T2Space M] (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hG : C.GloballyHyperbolic) :
    (∀ x y, C.le ⊤ x y ↔ C.Kminus ⊤ {x} ⊆ C.Kminus ⊤ {y}) ∧
    (∀ x y, C.le ⊤ x y ↔ C.Kplus ⊤ {y} ⊆ C.Kplus ⊤ {x}) ∧
    Function.Injective (fun x => C.Kminus ⊤ {x}) ∧ Function.Injective (fun x => C.Kplus ⊤ {x}) := by
  obtain ⟨h1, h2, h3, h4⟩ := Causality.K_order_embedding_of_globallyHyperbolic
    (SFALocal.tarentin hC) hG (fun x => (K_densite_sing_local hmin hC x).1)
    (fun x => (K_densite_sing_local hmin hC x).2)
  exact ⟨fun x y => ⟨fun hxy => (SFABTZ.K_monotone hmin hC hG.1 hxy).1, h1 x y⟩,
    fun x y => ⟨fun hxy => (SFABTZ.K_monotone hmin hC hG.1 hxy).2, h2 x y⟩, h3, h4⟩

/-! ### `lem:cup_cap_BTZ` (DEC-19) -/

/-- `lem:cup_cap_BTZ` in DEC-19's form at every globally hyperbolic, Hausdorff, second countable
`E_{≥0}`-manifold (unmarked): for a BTZ point `p` and `p_n → p` with `p ∉ J⁻(p_n)`,
`⋃_N ⋂_{n ≥ N} J⁻(p_n) = J⁻(p) ∖ {p}`. `Causality.SingularFlatAxioms.cup_cap_BTZ` applied to
`SFAManifolds.singularFlatAxioms`. -/
theorem cup_cap_BTZ [T2Space M] [SecondCountableTopology M] (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hG : C.GloballyHyperbolic) {p : M} (hp0 : p ∈ SFALocal.sing M 0) {u : ℕ → M}
    (hu : Tendsto u atTop (𝓝 p)) (hp : ∀ n, ¬ C.le ⊤ p (u n)) :
    ⋃ N : ℕ, ⋂ n ≥ N, C.Jminus ⊤ {u n} = C.Jminus ⊤ {p} \ {p} :=
  (SFAManifolds.singularFlatAxioms hmin hC).cup_cap_BTZ hG hp0 hu hp

/-- `lem:cup_cap_BTZ` at every `E_{≥0}`-manifold whose causal futures `J⁺(z)` are closed, with
neither Hausdorff nor second countability (`Causality.cup_cap_BTZ_of_isClosed` with
`SFABTZ.singularPastAt`). -/
theorem cup_cap_BTZ_of_isClosed (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hJ : ∀ z, IsClosed (C.Jplus ⊤ {z})) {p : M} (hp0 : p ∈ SFALocal.sing M 0) {u : ℕ → M}
    (hu : Tendsto u atTop (𝓝 p)) (hp : ∀ n, ¬ C.le ⊤ p (u n)) :
    ⋃ N : ℕ, ⋂ n ≥ N, C.Jminus ⊤ {u n} = C.Jminus ⊤ {p} \ {p} :=
  Causality.cup_cap_BTZ_of_isClosed (SFABTZ.singularPastAt hmin hC p hp0) hJ hu hp

/-! ### `rem:K_plongement_hypotheses` -/

/-- `rem:K_plongement_hypotheses`, (a) at every globally hyperbolic Hausdorff `E_{≥0}`-manifold:
`J^±(x)` closed (`prop:GH_Jferme`, tarentin from the charts). -/
theorem hypothesis_a [T2Space M]
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hG : C.GloballyHyperbolic) :
    (∀ x, IsClosed (C.Jplus ⊤ {x})) ∧ ∀ x, IsClosed (C.Jminus ⊤ {x}) :=
  hG.hypothesis_a (SFALocal.tarentin hC)

/-- `rem:K_plongement_hypotheses`, (b) at every Hausdorff, second countable `E_{≥0}`-manifold:
`prop:K_densite_sing` (`K_densite_sing`). -/
theorem hypothesis_b [T2Space M] [SecondCountableTopology M] (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) :
    (∀ x, C.Jplus ⊤ {x} ⊆ closure (C.Kplus ⊤ {x})) ∧
      ∀ x, C.Jminus ⊤ {x} ⊆ closure (C.Kminus ⊤ {x}) :=
  ⟨fun x => (K_densite_sing hmin hC x).1, fun x => (K_densite_sing hmin hC x).2⟩

/-- `rem:K_plongement_hypotheses` at a point strongly tarentin in the past of an `E_{≥0}`-manifold:
`K⁻(x) = I⁻(x)` (`prop:tarentin_fort_K`, `M` being causally plain, `SFALocal.causallyPlain`), (b)
reads `J⁻(x) ⊆ cl I⁻(x)`, and that density holds. -/
theorem hypothesis_b_tarentin (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) {x : M}
    (hx : x ∈ C.Zminus) :
    C.Kminus ⊤ {x} = C.Iminus ⊤ {x} ∧
      (C.Jminus ⊤ {x} ⊆ closure (C.Kminus ⊤ {x}) ↔ C.Jminus ⊤ {x} ⊆ closure (C.Iminus ⊤ {x})) ∧
      C.Jminus ⊤ {x} ⊆ closure (C.Iminus ⊤ {x}) := by
  haveI := SFABTZ.firstCountableTopology_of_isoChartsCover hC
  have hP := SFALocal.causallyPlain hmin hC
  have hiff := Causality.Jminus_subset_closure_Kminus_iff hP hx
  exact ⟨Causality.Kminus_eq_Iminus_of_mem_Zminus hP hx, hiff,
    hiff.1 (K_densite_sing_local hmin hC x).2⟩

/-- `rem:K_plongement_hypotheses` at a BTZ point of an `E_{≥0}`-manifold: `I⁻(x)` is empty, hence
not dense in `J⁻(x)`, and only `K⁻(x)` is. -/
theorem hypothesis_b_btz (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) {x : M}
    (hx : x ∈ SFALocal.sing M 0) :
    C.Iminus ⊤ {x} = ∅ ∧ ¬ C.Jminus ⊤ {x} ⊆ closure (C.Iminus ⊤ {x}) ∧
      C.Jminus ⊤ {x} ⊆ closure (C.Kminus ⊤ {x}) := by
  have hI := SFALocal.Iminus_eq_empty hmin hC x hx
  refine ⟨hI, fun h => ?_, (K_densite_sing_local hmin hC x).2⟩
  have hxx := h (Precausality.mem_Jminus_singleton.2 (C.le_refl trivial))
  rw [hI, closure_empty] at hxx
  exact hxx

/-- `rem:K_plongement_hypotheses`, the two hypotheses of `prop:K_plongement_ordre` discharged at
every globally hyperbolic, Hausdorff, second countable `E_{≥0}`-manifold: its conclusion
(`Causality.K_order_embedding_of_globallyHyperbolic` with `hKp`, `hKm` from `K_densite_sing`). -/
theorem K_order_embedding [T2Space M] [SecondCountableTopology M] (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hG : C.GloballyHyperbolic) :
    (∀ x y, C.Kminus ⊤ {x} ⊆ C.Kminus ⊤ {y} → C.le ⊤ x y) ∧
    (∀ x y, C.Kplus ⊤ {y} ⊆ C.Kplus ⊤ {x} → C.le ⊤ x y) ∧
    Function.Injective (fun x => C.Kminus ⊤ {x}) ∧ Function.Injective (fun x => C.Kplus ⊤ {x}) :=
  Causality.K_order_embedding_of_globallyHyperbolic (SFALocal.tarentin hC) hG
    (hypothesis_b hmin hC).1 (hypothesis_b hmin hC).2

/-- `rem:K_plongement_hypotheses` at every Hausdorff, second countable `E_{≥0}`-manifold
(unmarked), assembled: (a) under global hyperbolicity; (b) at every point; `M` causally plain; at
a point strongly tarentin in the past, `K⁻ = I⁻` and the classical density; at a BTZ point,
`I⁻ = ∅` and not dense; the order embedding under global hyperbolicity. -/
theorem K_plongement_hypotheses [T2Space M] [SecondCountableTopology M]
    (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) :
    (C.GloballyHyperbolic → (∀ x, IsClosed (C.Jplus ⊤ {x})) ∧ ∀ x, IsClosed (C.Jminus ⊤ {x})) ∧
    ((∀ x, C.Jplus ⊤ {x} ⊆ closure (C.Kplus ⊤ {x})) ∧
      ∀ x, C.Jminus ⊤ {x} ⊆ closure (C.Kminus ⊤ {x})) ∧
    C.CausallyPlain ∧
    (∀ x ∈ C.Zminus, C.Kminus ⊤ {x} = C.Iminus ⊤ {x} ∧
      C.Jminus ⊤ {x} ⊆ closure (C.Iminus ⊤ {x})) ∧
    (∀ x ∈ SFALocal.sing M 0, C.Iminus ⊤ {x} = ∅ ∧ ¬ C.Jminus ⊤ {x} ⊆ closure (C.Iminus ⊤ {x})) ∧
    (C.GloballyHyperbolic →
      (∀ x y, C.Kminus ⊤ {x} ⊆ C.Kminus ⊤ {y} → C.le ⊤ x y) ∧
      (∀ x y, C.Kplus ⊤ {y} ⊆ C.Kplus ⊤ {x} → C.le ⊤ x y) ∧
      Function.Injective (fun x => C.Kminus ⊤ {x}) ∧
      Function.Injective (fun x => C.Kplus ⊤ {x})) :=
  ⟨fun hG => hypothesis_a hC hG, hypothesis_b hmin hC, SFALocal.causallyPlain hmin hC,
    fun _ hx => ⟨(hypothesis_b_tarentin hmin hC hx).1, (hypothesis_b_tarentin hmin hC hx).2.2⟩,
    fun _ hx => ⟨(hypothesis_b_btz hmin hC hx).1, (hypothesis_b_btz hmin hC hx).2.1⟩,
    fun hG => K_order_embedding hmin hC hG⟩

/-! ### `cor:K_ordre_Sigma` -/

/-- `cor:K_ordre_Sigma` at every globally hyperbolic, Hausdorff, second countable
`E_{≥0}`-manifold (unmarked), `hK` (`prop:K_densite_sing`) discharged; `lem:Sigma_separe`'s
neighbourhood fact `hS` stays named. `Causality.K_ordre_Sigma` with tarentin from the charts. -/
theorem K_ordre_Sigma [T2Space M] [SecondCountableTopology M] (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hG : C.GloballyHyperbolic) {S : Set M}
    (hS : ∀ x ∈ C.Jplus ⊤ S \ S, C.Jplus ⊤ S ∈ 𝓝 x) :
    (∀ x ∈ C.Jplus ⊤ S \ S, ∀ y ∈ C.Jplus ⊤ S \ S,
      C.Kminus ⊤ {x} ∩ C.Jplus ⊤ S ⊆ C.Kminus ⊤ {y} ∩ C.Jplus ⊤ S → C.le ⊤ x y) ∧
    InjOn (fun x => C.Kminus ⊤ {x} ∩ C.Jplus ⊤ S) (C.Jplus ⊤ S \ S) :=
  Causality.K_ordre_Sigma (SFALocal.tarentin hC) hG (fun x => (K_densite_sing hmin hC x).2) hS

/-- `cor:K_ordre_Sigma` for a Cauchy surface `Σ` with the splitting `ψ` of `theo:geroch_sing`
named (`IsCauchySplitting`): `hS` is `lem:Sigma_separe` (`Causality.sigma_separe`), `Σ` acausal
by `IsCauchySurface.isAcausal_of_t1_secondCountable`. -/
theorem K_ordre_Sigma_of_splitting [T2Space M] [SecondCountableTopology M]
    (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hG : C.GloballyHyperbolic) {S : Set M} (hSc : C.IsCauchySurface S) {ψ : S × ℝ ≃ₜ M}
    (hψ : C.IsCauchySplitting S ψ) :
    (∀ x ∈ C.Jplus ⊤ S \ S, ∀ y ∈ C.Jplus ⊤ S \ S,
      C.Kminus ⊤ {x} ∩ C.Jplus ⊤ S ⊆ C.Kminus ⊤ {y} ∩ C.Jplus ⊤ S → C.le ⊤ x y) ∧
    InjOn (fun x => C.Kminus ⊤ {x} ∩ C.Jplus ⊤ S) (C.Jplus ⊤ S \ S) :=
  K_ordre_Sigma hmin hC hG (Causality.sigma_separe hG.1
    (hSc.isAcausal_of_t1_secondCountable (SFALocal.causallyArcConnected hmin hC)) hψ).2.2.2.2.2

/-- At a BTZ point `q` of an `E_{≥0}`-manifold, `S := J⁺(q) ∖ I⁺(q)` satisfies `cor:K_ordre_Sigma`'s
neighbourhood hypothesis non-vacuously: `J⁺(S) ∖ S = I⁺(q) ≠ ∅` (`q ≪ q` fails, `I⁻(q) = ∅`). -/
theorem btz_cone_shell (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) {q : M}
    (hq : q ∈ SFALocal.sing M 0) :
    C.Jplus ⊤ (C.Jplus ⊤ {q} \ C.Iplus ⊤ {q}) \ (C.Jplus ⊤ {q} \ C.Iplus ⊤ {q}) =
        C.Iplus ⊤ {q} ∧
      (C.Iplus ⊤ {q}).Nonempty ∧
      ∀ x ∈ C.Jplus ⊤ (C.Jplus ⊤ {q} \ C.Iplus ⊤ {q}) \ (C.Jplus ⊤ {q} \ C.Iplus ⊤ {q}),
        C.Jplus ⊤ (C.Jplus ⊤ {q} \ C.Iplus ⊤ {q}) ∈ 𝓝 x := by
  have hq' : ¬ C.lt ⊤ q q := fun h => by
    have hqq : q ∈ C.Iminus ⊤ {q} := Precausality.mem_Iminus_singleton.2 h
    rw [SFALocal.Iminus_eq_empty hmin hC q hq] at hqq
    exact hqq
  obtain ⟨h1, h2⟩ := cone_shell hq'
  exact ⟨h1, Causality.Iplus_nonempty_of_mem_Zplus (SFALocal.mem_Zplus hC q), h2⟩

/-! ### The natural causality -/

/-- The rows at every Hausdorff, second countable `E_{≥0}`-manifold with its natural causality
(`IsAtlasCausalityDEC25`, OQ-18's reading of « the causality generated by its `X_A`-atlas »,
through `SFALocal.of_isAtlasCausalityDEC25`; unmarked): `lem:past_BTZ` (b); `cor:K_injectif`
under strong causality; `prop:K_densite_sing`; `cor:K_ordre` and `lem:cup_cap_BTZ` (DEC-19) under
global hyperbolicity; `cor:K_ordre_Sigma` under global hyperbolicity and `hS`. -/
theorem rows_of_isAtlasCausalityDEC25 [T2Space M] [SecondCountableTopology M]
    (hcov : SFALocal.MassACovered M)
    (hC : IsAtlasCausalityDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) :
    (∀ (W : Opens M) (I : Set ℝ) (c : ℝ → M), C.CausalCurveIn W I c →
      (∀ s ∈ I, ∀ s' ∈ I, s' ≤ s → c s ∈ SFALocal.sing M 0 → c s' ∈ SFALocal.sing M 0) ∧
      IsPreconnected (c '' I ∩ SFALocal.sing M 0) ∧ IsPreconnected (c '' I \ SFALocal.sing M 0) ∧
      closure (c '' I ∩ SFALocal.sing M 0) ∩ c '' I ⊆ c '' I ∩ SFALocal.sing M 0 ∧
      ∀ x ∈ c '' I ∩ SFALocal.sing M 0, ∀ y ∈ c '' I \ SFALocal.sing M 0, C.le W x y) ∧
    (C.StronglyCausal → Function.Injective (fun x => C.Kplus ⊤ {x}) ∧
      Function.Injective (fun x => C.Kminus ⊤ {x})) ∧
    (∀ x, C.Jplus ⊤ {x} ⊆ closure (C.Kplus ⊤ {x}) ∧ C.Jminus ⊤ {x} ⊆ closure (C.Kminus ⊤ {x})) ∧
    (C.GloballyHyperbolic →
      (∀ x y, C.le ⊤ x y ↔ C.Kminus ⊤ {x} ⊆ C.Kminus ⊤ {y}) ∧
      (∀ x y, C.le ⊤ x y ↔ C.Kplus ⊤ {y} ⊆ C.Kplus ⊤ {x}) ∧
      Function.Injective (fun x => C.Kminus ⊤ {x}) ∧ Function.Injective (fun x => C.Kplus ⊤ {x})) ∧
    (C.GloballyHyperbolic → ∀ p ∈ SFALocal.sing M 0, ∀ u : ℕ → M, Tendsto u atTop (𝓝 p) →
      (∀ n, ¬ C.le ⊤ p (u n)) → ⋃ N : ℕ, ⋂ n ≥ N, C.Jminus ⊤ {u n} = C.Jminus ⊤ {p} \ {p}) ∧
    (C.GloballyHyperbolic → ∀ S : Set M, (∀ x ∈ C.Jplus ⊤ S \ S, C.Jplus ⊤ S ∈ 𝓝 x) →
      (∀ x ∈ C.Jplus ⊤ S \ S, ∀ y ∈ C.Jplus ⊤ S \ S,
        C.Kminus ⊤ {x} ∩ C.Jplus ⊤ S ⊆ C.Kminus ⊤ {y} ∩ C.Jplus ⊤ S → C.le ⊤ x y) ∧
      InjOn (fun x => C.Kminus ⊤ {x} ∩ C.Jplus ⊤ S) (C.Jplus ⊤ S \ S)) := by
  obtain ⟨hmin, hC'⟩ := SFALocal.of_isAtlasCausalityDEC25 hcov hC
  refine ⟨fun W I c hc => ?_, K_injectif hmin hC', K_densite_sing hmin hC',
    K_ordre hmin hC', fun hG p hp u hu hpu => cup_cap_BTZ hmin hC' hG hp hu hpu,
    fun hG S hS => K_ordre_Sigma hmin hC' hG hS⟩
  obtain ⟨h1, -, h3, h4, h5, h6⟩ := past_BTZ_b hmin hC' hc
  exact ⟨h1, h3, h4, h5, h6⟩

end Manifold

/-! ### Witnesses (kb/0011) -/

section WitnessE0

attribute [local instance] E0GX.singularGX

/-- Non-vacuity at `E₀` (kb/0011): `sing₀(E₀)` is the axis, non-empty, `E₀` is strongly causal and
globally hyperbolic; through every axis point the BTZ line (`past_BTZ`), the three `K` rows, and
hypothesis (b) at every axis point with `I⁻ = ∅`, each out of this file's theorems. -/
theorem nonvacuous_e0 :
    SFALocal.sing E0 0 = E0.axis ∧ (SFALocal.sing E0 0).Nonempty ∧
      E0.causality.StronglyCausal ∧ E0.causality.GloballyHyperbolic ∧
      (∀ p ∈ E0.axis, ∃ γ : ℝ → E0, γ 0 = p ∧ IsClosedEmbedding γ ∧
        E0.causality.Inextensible ⊤ univ γ ∧ range γ = connectedComponentIn E0.axis p) ∧
      Function.Injective (fun x : E0 => E0.causality.Kplus ⊤ {x}) ∧
      Function.Injective (fun x : E0 => E0.causality.Kminus ⊤ {x}) ∧
      (∀ x : E0, E0.causality.Jplus ⊤ {x} ⊆ closure (E0.causality.Kplus ⊤ {x}) ∧
        E0.causality.Jminus ⊤ {x} ⊆ closure (E0.causality.Kminus ⊤ {x})) ∧
      (∀ x y : E0, E0.causality.le ⊤ x y ↔
        E0.causality.Kminus ⊤ {x} ⊆ E0.causality.Kminus ⊤ {y}) ∧
      (∀ x y : E0, E0.causality.le ⊤ x y ↔
        E0.causality.Kplus ⊤ {y} ⊆ E0.causality.Kplus ⊤ {x}) ∧
      ∀ p ∈ E0.axis, E0.causality.Iminus ⊤ {p} = ∅ ∧
        ¬ E0.causality.Jminus ⊤ {p} ⊆ closure (E0.causality.Iminus ⊤ {p}) ∧
        E0.causality.Jminus ⊤ {p} ⊆ closure (E0.causality.Kminus ⊤ {p}) := by
  obtain ⟨hmin, hC, h0, hne⟩ := SFALocal.nonvacuous_e0
  obtain ⟨hKp, hKm⟩ := K_injectif hmin hC E0.stronglyCausal
  obtain ⟨hKo1, hKo2, -, -⟩ := K_ordre hmin hC E0.globallyHyperbolic
  refine ⟨h0, hne, E0.stronglyCausal, E0.globallyHyperbolic, fun p hp => ?_, hKp, hKm,
    K_densite_sing hmin hC, hKo1, hKo2, fun p hp => hypothesis_b_btz hmin hC (h0 ▸ hp)⟩
  obtain ⟨γ, hγ0, hγ, hγi, hγr⟩ := (past_BTZ hC).1 p (h0 ▸ hp)
  exact ⟨γ, hγ0, hγ E0.isCausal, hγi, h0 ▸ hγr⟩

/-- Non-vacuity of `K_plongement_hypotheses` at `E₀` (kb/0011): (a) under global hyperbolicity,
causal plainness, `K⁻ = I⁻` and the classical density at the points strongly tarentin in the past,
of which `(1, 1)` is one, and the order embedding, each out of `K_plongement_hypotheses`. -/
theorem nonvacuous_e0_plongement :
    ((∀ x : E0, IsClosed (E0.causality.Jplus ⊤ {x})) ∧
      ∀ x : E0, IsClosed (E0.causality.Jminus ⊤ {x})) ∧
      E0.causality.CausallyPlain ∧ ((1 : ℝ), (1 : ℂ)) ∈ E0.causality.Zminus ∧
      (∀ x ∈ E0.causality.Zminus, E0.causality.Kminus ⊤ {x} = E0.causality.Iminus ⊤ {x} ∧
        E0.causality.Jminus ⊤ {x} ⊆ closure (E0.causality.Iminus ⊤ {x})) ∧
      (∀ x y : E0, E0.causality.Kminus ⊤ {x} ⊆ E0.causality.Kminus ⊤ {y} →
        E0.causality.le ⊤ x y) ∧
      ∀ x y : E0, E0.causality.Kplus ⊤ {y} ⊆ E0.causality.Kplus ⊤ {x} → E0.causality.le ⊤ x y := by
  obtain ⟨hmin, hC, h0, -⟩ := SFALocal.nonvacuous_e0
  obtain ⟨ha, -, hP, hZ, -, hemb⟩ := K_plongement_hypotheses hmin hC
  have hreg : ((1 : ℝ), (1 : ℂ)) ∉ SFALocal.sing E0 0 := by
    rw [h0]
    exact one_ne_zero
  exact ⟨ha E0.globallyHyperbolic, hP, SFALocal.mem_Zminus_of_notMem hC hreg, hZ,
    (hemb E0.globallyHyperbolic).1, (hemb E0.globallyHyperbolic).2.1⟩

/-- Non-vacuity of `lem:past_BTZ` (b) at `E₀`: a causal curve from the axis point `(0, 0)` to the
regular point `(1, 1)` (causal arc-connectedness), with `Δ` and `c⁰` both non-empty, and the
conclusions of `past_BTZ_b_local`. -/
theorem nonvacuous_e0_past :
    ∃ c : ℝ → E0, E0.causality.CausalCurveIn ⊤ (Icc 0 1) c ∧ c 0 = ((0 : ℝ), (0 : ℂ)) ∧
      c 1 = ((1 : ℝ), (1 : ℂ)) ∧
      (c '' Icc 0 1 ∩ E0.axis).Nonempty ∧ (c '' Icc 0 1 \ E0.axis).Nonempty ∧
      IsPreconnected (c '' Icc 0 1 ∩ E0.axis) ∧ IsPreconnected (c '' Icc 0 1 \ E0.axis) ∧
      closure (c '' Icc 0 1 ∩ E0.axis) ∩ c '' Icc 0 1 ⊆ c '' Icc 0 1 ∩ E0.axis ∧
      ∀ x ∈ c '' Icc 0 1 ∩ E0.axis, ∀ y ∈ c '' Icc 0 1 \ E0.axis, E0.causality.le ⊤ x y := by
  obtain ⟨hmin, hC, h0, -⟩ := SFALocal.nonvacuous_e0
  have hle : E0.causality.le ⊤ ((0 : ℝ), (0 : ℂ)) ((1 : ℝ), (1 : ℂ)) := by
    rw [E0.le_top_iff, E0.le_axis_iff rfl]
    simp only [E0.fcoord, E0.rad, norm_one]
    norm_num
  obtain ⟨c, hc, hc0, hc1⟩ := (SFALocal.causallyArcConnected hmin hC ⊤ le_rfl _ _).1.1 hle
  obtain ⟨-, -, h3, h4, h5, h6⟩ := past_BTZ_b_local hC (hc.causalCurveIn_Icc zero_le_one)
  rw [h0] at h3 h4 h5 h6
  refine ⟨c, hc.causalCurveIn_Icc zero_le_one, hc0, hc1, ⟨c 0, ⟨0, left_mem_Icc.2 zero_le_one,
    rfl⟩, ?_⟩, ⟨c 1, ⟨1, right_mem_Icc.2 zero_le_one, rfl⟩, ?_⟩, h3, h4, h5, h6⟩
  · rw [hc0]
    rfl
  · rw [hc1]
    exact one_ne_zero

/-- Non-vacuity of `lem:cup_cap_BTZ` (DEC-19) at a BTZ point: at `p = (0, 0) ∈ sing₀(E₀)` with
`p_n = (−1/(n+1), 0) → p` along the axis from below, `p ∉ J⁻(p_n)`, and the conclusion of
`cup_cap_BTZ`, the set being non-empty. -/
theorem nonvacuous_e0_cup_cap :
    ((0 : ℝ), (0 : ℂ)) ∈ SFALocal.sing E0 0 ∧
      Tendsto (fun n : ℕ => ((-(1 / ((n : ℝ) + 1)) : ℝ), (0 : ℂ))) atTop
        (𝓝 ((0 : ℝ), (0 : ℂ))) ∧
      (∀ n : ℕ, ¬ E0.causality.le ⊤ ((0 : ℝ), (0 : ℂ)) ((-(1 / ((n : ℝ) + 1)) : ℝ), (0 : ℂ))) ∧
      ⋃ N : ℕ, ⋂ n ≥ N, E0.causality.Jminus ⊤ {((-(1 / ((n : ℝ) + 1)) : ℝ), (0 : ℂ))} =
        E0.causality.Jminus ⊤ {((0 : ℝ), (0 : ℂ))} \ {((0 : ℝ), (0 : ℂ))} ∧
      (E0.causality.Jminus ⊤ {((0 : ℝ), (0 : ℂ))} \ {((0 : ℝ), (0 : ℂ))}).Nonempty := by
  obtain ⟨hmin, hC, h0, -⟩ := SFALocal.nonvacuous_e0
  have hp0 : ((0 : ℝ), (0 : ℂ)) ∈ SFALocal.sing E0 0 := by rw [h0]; rfl
  have hu : Tendsto (fun n : ℕ => ((-(1 / ((n : ℝ) + 1)) : ℝ), (0 : ℂ))) atTop
      (𝓝 ((0 : ℝ), (0 : ℂ))) := by
    have h1 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
    rw [neg_zero] at h1
    exact h1.prodMk_nhds tendsto_const_nhds
  have hpu : ∀ n : ℕ,
      ¬ E0.causality.le ⊤ ((0 : ℝ), (0 : ℂ)) ((-(1 / ((n : ℝ) + 1)) : ℝ), (0 : ℂ)) := by
    intro n h
    rw [E0.le_top_iff, E0.le_axis_iff' rfl] at h
    have h2 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have h3 : (0 : ℝ) ≤ -(1 / ((n : ℝ) + 1)) := h.2
    linarith
  refine ⟨hp0, hu, hpu, cup_cap_BTZ hmin hC E0.globallyHyperbolic hp0 hu hpu, ?_⟩
  refine ⟨((-1 : ℝ), (0 : ℂ)), ?_, ?_⟩
  · rw [E0.Jminus_axis rfl]
    exact ⟨rfl, by norm_num⟩
  · intro h
    have h' := congrArg Prod.fst (mem_singleton_iff.1 h)
    norm_num at h'

/-- The certificate of record of `lem:cup_cap_BTZ` (DEC-19),
`Causality.cupCapBTZAsPrinted_of_globallyHyperbolic`, at a model with a BTZ point: `E₀` is a
strongly causal `SingularFlatSpacetime` for `SFALocal.sing` (`SFAManifolds.nonvacuous_e0`), so the
antecedents of `CupCapBTZAsPrinted` hold, and its conclusion at `(0, 0)` along the axis from below
is that of `nonvacuous_e0_cup_cap`. -/
theorem nonvacuous_e0_certificate :
    E0.causality.SingularFlatSpacetime (SFALocal.sing E0) ∧ E0.causality.StronglyCausal ∧
      E0.causality.CupCapBTZAsPrinted (SFALocal.sing E0) ∧
      ⋃ N : ℕ, ⋂ n ≥ N, E0.causality.Jminus ⊤ {((-(1 / ((n : ℝ) + 1)) : ℝ), (0 : ℂ))} =
        E0.causality.Jminus ⊤ {((0 : ℝ), (0 : ℂ))} \ {((0 : ℝ), (0 : ℂ))} := by
  obtain ⟨-, -, -, -, hSFS, hSC, -⟩ := SFAManifolds.nonvacuous_e0
  obtain ⟨hp0, hu, hpu, -, -⟩ := nonvacuous_e0_cup_cap
  have hcert := Causality.cupCapBTZAsPrinted_of_globallyHyperbolic (sing := SFALocal.sing E0)
    E0.globallyHyperbolic
  exact ⟨hSFS, hSC, hcert, hcert hSFS hSC _ hp0 _ hu hpu⟩

/-- Non-vacuity of `K_ordre_Sigma` at `E₀`: with `S = J⁺(q) ∖ I⁺(q)`, `q = (0, 0)` on the axis,
`J⁺(S) ∖ S = I⁺(q)` is non-empty, `hS` holds, and the conclusions follow. -/
theorem nonvacuous_e0_Sigma :
    ∃ S : Set E0, S = E0.causality.Jplus ⊤ {((0 : ℝ), (0 : ℂ))} \
        E0.causality.Iplus ⊤ {((0 : ℝ), (0 : ℂ))} ∧
      E0.causality.Jplus ⊤ S \ S = E0.causality.Iplus ⊤ {((0 : ℝ), (0 : ℂ))} ∧
      (E0.causality.Jplus ⊤ S \ S).Nonempty ∧
      (∀ x ∈ E0.causality.Jplus ⊤ S \ S, E0.causality.Jplus ⊤ S ∈ 𝓝 x) ∧
      (∀ x ∈ E0.causality.Jplus ⊤ S \ S, ∀ y ∈ E0.causality.Jplus ⊤ S \ S,
        E0.causality.Kminus ⊤ {x} ∩ E0.causality.Jplus ⊤ S ⊆
          E0.causality.Kminus ⊤ {y} ∩ E0.causality.Jplus ⊤ S → E0.causality.le ⊤ x y) ∧
      InjOn (fun x => E0.causality.Kminus ⊤ {x} ∩ E0.causality.Jplus ⊤ S)
        (E0.causality.Jplus ⊤ S \ S) := by
  obtain ⟨hmin, hC, h0, -⟩ := SFALocal.nonvacuous_e0
  have hq : ((0 : ℝ), (0 : ℂ)) ∈ SFALocal.sing E0 0 := by rw [h0]; rfl
  obtain ⟨h1, h2, h3⟩ := btz_cone_shell hmin hC hq
  refine ⟨_, rfl, h1, ?_, h3, K_ordre_Sigma hmin hC E0.globallyHyperbolic h3⟩
  rw [h1]
  exact h2

/-- Non-vacuity of `rows_of_isAtlasCausalityDEC25` at `E₀`: `E₀` is an `E_{≥0}`-manifold whose
natural causality over the family is `E0.causality` (`EModelsBPrime.massA_dec25_models_e0_sing`),
with a BTZ point; injectivity, the order and the cup-cap formula out of the assembly. -/
theorem nonvacuous_e0_natural :
    SFALocal.MassACovered E0 ∧
      IsAtlasCausalityDEC25 (Flat.isom 2) E0.causality (minkowski 2) massAModelCausality ∧
      (SFALocal.sing E0 0).Nonempty ∧
      Function.Injective (fun x : E0 => E0.causality.Kplus ⊤ {x}) ∧
      Function.Injective (fun x : E0 => E0.causality.Kminus ⊤ {x}) ∧
      (∀ x y : E0, E0.causality.le ⊤ x y ↔
        E0.causality.Kminus ⊤ {x} ⊆ E0.causality.Kminus ⊤ {y}) ∧
      ∀ p ∈ SFALocal.sing E0 0, ∀ u : ℕ → E0, Tendsto u atTop (𝓝 p) →
        (∀ n, ¬ E0.causality.le ⊤ p (u n)) →
          ⋃ N : ℕ, ⋂ n ≥ N, E0.causality.Jminus ⊤ {u n} = E0.causality.Jminus ⊤ {p} \ {p} := by
  obtain ⟨-, hcov, hC, -⟩ := EModelsBPrime.massA_dec25_models_e0_sing
  obtain ⟨-, -, -, hne⟩ := SFALocal.nonvacuous_e0
  obtain ⟨-, hinj, -, hord, hcc, -⟩ := rows_of_isAtlasCausalityDEC25 hcov hC
  exact ⟨hcov, hC, hne, (hinj E0.stronglyCausal).1, (hinj E0.stronglyCausal).2,
    (hord E0.globallyHyperbolic).1, hcc E0.globallyHyperbolic⟩

end WitnessE0

section WitnessEPi

attribute [local instance] EAlphaGX.singularGX EAlphaGX.fact_pi_pos

/-- Non-vacuity at `E_π` (kb/0011): `sing₀ = ∅`, `sing_π ≠ ∅`; through every point of `sing_π` the
massive line, a closed embedding (`past_BTZ`), and the three `K` rows, `E_π` being strongly causal
and globally hyperbolic. -/
theorem nonvacuous_epi :
    SFALocal.sing (Massive Real.pi) 0 = ∅ ∧ (SFALocal.sing (Massive Real.pi) Real.pi).Nonempty ∧
      (∀ p ∈ SFALocal.sing (Massive Real.pi) Real.pi, ∃ γ : ℝ → Massive Real.pi, γ 0 = p ∧
        IsClosedEmbedding γ ∧ (massive Real.pi).Inextensible ⊤ univ γ ∧
        (∀ a b, (massive Real.pi).ChronalCurveOn ⊤ γ a b) ∧
        range γ = connectedComponentIn (SFALocal.sing (Massive Real.pi) Real.pi) p) ∧
      Function.Injective (fun x : Massive Real.pi => (massive Real.pi).Kplus ⊤ {x}) ∧
      Function.Injective (fun x : Massive Real.pi => (massive Real.pi).Kminus ⊤ {x}) ∧
      (∀ x : Massive Real.pi,
        (massive Real.pi).Jplus ⊤ {x} ⊆ closure ((massive Real.pi).Kplus ⊤ {x}) ∧
        (massive Real.pi).Jminus ⊤ {x} ⊆ closure ((massive Real.pi).Kminus ⊤ {x})) ∧
      (∀ x y : Massive Real.pi, (massive Real.pi).le ⊤ x y ↔
        (massive Real.pi).Kminus ⊤ {x} ⊆ (massive Real.pi).Kminus ⊤ {y}) ∧
      ∀ x y : Massive Real.pi, (massive Real.pi).le ⊤ x y ↔
        (massive Real.pi).Kplus ⊤ {y} ⊆ (massive Real.pi).Kplus ⊤ {x} := by
  obtain ⟨hmin, hC, -, hne, h0⟩ := SFALocal.nonvacuous_epi
  obtain ⟨hKp, hKm⟩ := K_injectif hmin hC massive_stronglyCausal
  obtain ⟨hKo1, hKo2, -, -⟩ := K_ordre hmin hC massive_globallyHyperbolic
  refine ⟨h0, hne, fun p hp => ?_, hKp, hKm, K_densite_sing hmin hC, hKo1, hKo2⟩
  obtain ⟨γ, hγ0, hγ, hγi, hγc, hγr⟩ := (past_BTZ hC).2.1 Real.pi Real.pi_pos p hp
  exact ⟨γ, hγ0, hγ massive_globallyHyperbolic.1, hγi, hγc, hγr⟩

end WitnessEPi

end SingularRowsK

end Causal
