import Causal.Ers475CauchyForm
import Causal.CBG.SubExtensionAbstract

/-!
# ERS19 Theorem 4.64 and its corollaries with "GHD" read "`S` Cauchy", without arc-connectedness

Programme target `T-abs-ers-4-64-without-arc` (`programme/roadmap.toml`; layer 1: ETT-layer
imports only, `Causal.Ers475CauchyForm` and, for the witnesses, `Causal.CBG.SubExtensionAbstract`;
no model; no metric notion in a statement). Source: Eperon–Reall–Sbierski, arXiv 1802.03020,
`papers/ers-predictability` (`legacy/labeled/ghd_02_19.tex`). Causal-topological skeletons;
**no label is marked** (SCOPE):

* `ersthm:ThmUnique` — `ghd_02_19.tex:858` (proof 865–912):
  `ers_theorem_4_64_of_isCauchySurfaceOn_secondCountable_noArc`, its `_maxCommonDevelopment_`
  and `_of_localUniqueness_` forms; Step 1
  `isCommonDevelopment_maxCommonDevelopment_of_isCauchySurfaceOn_secondCountable`.
* `ersrem:RemTime` — `ghd_02_19.tex:914`, the first sentence only:
  `ers_remark_4_67_of_isCauchySurfaceOn_secondCountable_noArc`.
* `erscor:CorDisCon` — `ghd_02_19.tex:921`:
  `ers_corollary_4_68_of_isCauchySurfaceOn_secondCountable_noArc`, its `_eqOn_` form.
* `erscor:globally_defined_globally_hyperbolic` — `ghd_02_19.tex:926`:
  `ers_corollary_4_69_of_isCauchySurface_secondCountable_noArc`.
* `erscor:CorSupLum` — `ghd_02_19.tex:959` (proof 965–967):
  `ers_corollary_4_71_of_isCauchySurfaceOn_secondCountable_noArc`.
* `erscor:CorUniqueSub` — `ghd_02_19.tex:988`:
  `ers_corollary_4_73_of_isCauchySurfaceOn_secondCountable_noArc` and, for its use at `:1053`,
  `IsMDevelopment.isUniqueDevelopment_secondCountable_noArc`.

Each `…_noArc` form is a trade form of `Causal.Ers464SecondCountable` (4.64, 4.67, 4.68, 4.69,
4.71) or `Causal.ErsSecondCountable` (4.73, the m-GHD's uniqueness) **less its binder `harc`**
(`U₁` causally arc-connected for `C`; for 4.69, `M`; for the m-GHD, each `cau u` on its domain).
Every other binder and the conclusion are unchanged (checked mechanically, kb/0227). So each
form is **at least as strong** as its trade form, which follows from it by forgetting `harc`. The
trade forms stay unchanged beside them (kb/0226). Step 1 runs through
`isCauchySurfaceOn_sSup_of_secondCountable`, as Thm 4.75's region forms do
(`Causal.Ers475CauchyForm`, kb/0265), and `SplitBy U₁ S` comes from
`splitBy_of_t1_secondCountable`. **No step of these proofs uses the acausality of `S` in `U₁` for
`C`** (the 4.73 and m-GHD forms keep the paper's own hypothesis `hmacausal : Cm.IsAcausal S`).

> Theorem 4.64. Let u1 : U1 → R and u2 : U2 → R be two globally hyperbolic developments of
> (4.61) arising from the same initial data given on a connected hypersurface S ⊆ R^{d+1}.
> Assume that U1 ∩ U2 is connected. Then u1 and u2 agree on U1 ∩ U2. (`:859`)
> It is immediate that this is well-defined and that v0 : V0 → R is a common globally hyperbolic
> development with the property that any other common globally hyperbolic development is a
> subset of V0. (`:868`)

> Remark 4.67. Let us remark that the proof in particular shows that under the assumptions of
> Theorem 4.64 the intersection U1 ∩ U2 is the maximal common globally hyperbolic development of
> u1 : U1 → R and u2 : U2 → R. (`:915`)

> Corollary 4.68. […] If there exists an x ∈ U1 ∩ U2 with u1(x) ≠ u2(x), then U1 ∩ U2 is not
> connected. (`:922`) — Corollary 4.69. Let u1 : R^{d+1} → R be a globally defined globally
> hyperbolic development […]. Then u1|U2 = u2. (`:927`) — Corollary 4.71. […] we then have
> u1(x) = u2(x) for all x ∈ U1 ∩ U2. (`:962`) — Corollary 4.73. […] Then u1 = u2 on U1 ∩ U2.
> (`:990`) — We note that any m-GHD is a UGHD by Corollary 4.73. (`:1053`)

> A globally hyperbolic development (GHD) […] such that U is globally hyperbolic with respect to
> the Lorentzian metric g(u, du) with Cauchy hypersurface S. (`ghd_02_19.tex:814`)

## Hypothesis checklist

Against the paper. Rows not listed are the trade forms', carried unchanged (`hglue`, `hG`, `hT`,
`hK`, `hconn`, `hlocal`/`hloc`, `hstay`, `hstep`; 4.71's `hS`, `hC₂`, `hτ`, `honce`, `hn₁`,
`hn₂`; 4.73's `hS`, `hm`, `hmacausal`, `hmU₁`, `hC₂`, `hnest`; the m-GHD's `hsub`, `hm`,
`hmacausal`, `hS`, `h`): the checklists of `Causal.Ers464SecondCountable`,
`Causal.ErsSecondCountable` and `Causal.ErsUniqueness` stand for them.

| paper | here |
|---|---|
| background `R^{d+1}`, `U ⊆ R^{d+1}` open (`:812, 814`) | ✓ abstract `M`, `[T2Space M] [SecondCountableTopology M]`, as in the trade forms; both hold on `R^{d+1}` |
| `u₁` a GHD (`:814`), used at Step 1 (`:868`) and `:870` | ⚠ read (DEC-162): `hC₁ : C.IsCauchySurfaceOn U₁ S` (4.69: `C.IsCauchySurface S`; the m-GHD: `IsDevelopment.cauchy`), with GH, tarentin and `CompactSlabs` of `U₁` named, as in the trade forms; **the trade forms' `harc` is not asked** |
| Step 1: "`v₀` a common GHD", "immediate" (`:868`) | ✓ proved: `S` Cauchy in `V₀` from `S` Cauchy in `U₁` (`isCauchySurfaceOn_sSup_of_secondCountable`, ambient `U₁`); GH of `V₀` not concluded, as in the original |
| Step 2: "without loss of generality `q ∈ J⁺(S, U₁)`" (`:870`) | ✓ `SplitBy U₁ S` from `hC₁` (`splitBy_of_t1_secondCountable`) |
| 4.67 (first sentence): "the maximal common GHD" | ⚠ read as in the original: the greatest common development with `S` Cauchy (OQ-57 (c)); the GH form keeps `harc` (SCOPE) |

## SCOPE (disclosed)

* **No label is marked.** Every row keeps the trade forms' named inputs: `local_uniqueness`,
  `slice_restart`, `frontier_stays_in` (OQ-57 (b)); GH, tarentin, `CompactSlabs` of `U₁`; 4.71's
  `inextensible_nested` and `T`'s causality; 4.73's `curve_nested` and Minkowski's causality.
* **Where the trade forms needed `harc`, and why these do not.** The trade forms derive
  `IsAcausalOn U₁ S` from `hC₁` and `harc` (`IsCauchySurfaceOn.isAcausalOn_of_t1_secondCountable`)
  and pass it to the originals. The originals use it only in Step 1
  (`isCommonDevelopment_maxCommonDevelopment`: two points of `S` on one inextensible curve of
  `V₀` coincide), and 4.68, 4.69, 4.71, 4.73 and the m-GHD's uniqueness use it only by calling
  Theorem 4.64. Step 1 here gets `S` Cauchy in `V₀` from `S` Cauchy in the ambient `U₁`, with no
  acausality; Step 2's `hsplit` is used, as in the original, at `V₀ ∩ U₁ ∩ U₂ ≠ ∅` and at
  `exists_isSpacelikeBoundaryPoint`.
* **Beyond the target's title, by the same route**: 4.69, 4.73 and
  `IsMDevelopment.isUniqueDevelopment_secondCountable_noArc` (the target names 4.64, 4.67, 4.68
  and, if the route applies, 4.71).
* **Out of scope, unchanged.** Remark 4.67's future and past sentences
  (`ers_remark_4_67_future/past_of_isCauchySurfaceOn_secondCountable`) use the acausality
  between two points of `S` related by `≤_{U₁}` (`Jplus_inter_subset_…`), so they keep `harc`
  (kb/0265). The GH forms keep it for `V₀`'s causal convexity in `U₁`. Theorems 4.79 and 4.80
  use `harc` also for antisymmetry through curve nesting, a different route.
* **Witnesses** (kb/0011), in `ErsNoArcWitness`: `data` proves the hypotheses on `ℝ` with
  `S = {0}`, `U₁ = ℝ`, `U₂ = ]-1, 1[`, `u₁ = id`, `u₂` the clamp (the data of
  `timelikeLine_ers_theorem_4_64_of_isCauchySurfaceOn_secondCountable`). It holds for every
  causality of `ℝ` that goes up and contains the timelike line's relations. `conclusions` and
  `corollaries` run the 4.64 (three forms), 4.67, 4.69, 4.71 and 4.73 forms on it.
  `timelikeLine_ers_theorem_4_64_of_isCauchySurfaceOn_secondCountable_noArc` is the timelike
  line's proper instance. `densCausality_ers_theorem_4_64_of_isCauchySurfaceOn_secondCountable_noArc`
  takes the non-local `densCausality` of `Causal.CBG.SubExtensionAbstract`. There `harc` fails,
  so the trade forms do not apply, while the `…_noArc` forms do. `S = {0}` is acausal there, so
  the originals of `Causal.ErsUniqueness` still apply: a configuration with `S` Cauchy and not
  acausal is not given. Cor 4.68 and the m-GHD form have no witness (on the line the overlap is
  an interval, so 4.68 cannot be met with a disagreement).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Function

universe u v

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable {C : Causality M} {S : Set M}

/-! ## 1. Step 1 with `S` a Cauchy surface of `U₁` -/

/-- **ERS Thm 4.64, Step 1, with `S` Cauchy in `U₁`**, on a T2, second countable background:
`isCommonDevelopment_maxCommonDevelopment` with `hacausal` traded for `hC₁`. `S` is a Cauchy
surface of the union `V₀` of the common developments because it is one of the ambient `U₁` and
of each member (`isCauchySurfaceOn_sSup_of_secondCountable`); no acausality. -/
theorem isCommonDevelopment_maxCommonDevelopment_of_isCauchySurfaceOn_secondCountable
    [T2Space M] [SecondCountableTopology M] {U₁ U₂ : Opens M}
    {agree : Opens M → Prop} (hglue : AgreementGlues agree)
    (hanti : ∀ ⦃x y : M⦄, C.le U₁ x y → C.le U₁ y x → x = y) (hC₁ : C.IsCauchySurfaceOn U₁ S)
    (hlocal : ∃ V, C.IsCommonDevelopment S U₁ U₂ agree V) :
    C.IsCommonDevelopment S U₁ U₂ agree (C.maxCommonDevelopment S U₁ U₂ agree) := by
  obtain ⟨V₁, hV₁⟩ := hlocal
  refine ⟨sSup_le fun V hV => hV.le, hV₁.subset.trans (le_sSup hV₁ : V₁ ≤ _),
    hglue _ fun V hV => hV.agree, ?_⟩
  exact isCauchySurfaceOn_sSup_of_secondCountable hanti hC₁
    (fun V hV => (show C.IsCommonDevelopment S U₁ U₂ agree V from hV).le.trans inf_le_left)
    fun V hV => ⟨S, subset_rfl, (show C.IsCommonDevelopment S U₁ U₂ agree V from hV).cauchy⟩

/-! ## 2. Theorem 4.64 and Remark 4.67's first sentence -/

/-- **ERS19 Theorem 4.64, the maximal common development is `U₁ ∩ U₂`, with `u₁` a GHD read as
`S` Cauchy in `U₁`, without arc-connectedness** (`ersthm:ThmUnique`, unmarked), on a T2, second
countable background: `ers_theorem_4_64_maxCommonDevelopment_of_isCauchySurfaceOn_secondCountable`
less `harc`. -/
theorem ers_theorem_4_64_maxCommonDevelopment_of_isCauchySurfaceOn_secondCountable_noArc
    [T2Space M] [SecondCountableTopology M] {U₁ U₂ : Opens M}
    {agree : Opens M → Prop} (hglue : AgreementGlues agree)
    (hG : C.GloballyHyperbolicOn U₁) (hT : C.TarentinOn U₁) (hC₁ : C.IsCauchySurfaceOn U₁ S)
    (hK : C.CompactSlabs U₁ S)
    (hconn : IsPreconnected ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hlocal : ∃ V, C.IsCommonDevelopment S U₁ U₂ agree V)
    (hstay : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.FrontierStaysIn U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hstep : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.SliceRestart U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M)
        (fun _ => ∃ V', C.IsCommonDevelopment S U₁ U₂ agree V' ∧ V < V')) :
    C.maxCommonDevelopment S U₁ U₂ agree = U₁ ⊓ U₂ := by
  have hsplit : C.SplitBy U₁ S := splitBy_of_t1_secondCountable hC₁
  have hV₀ :=
    isCommonDevelopment_maxCommonDevelopment_of_isCauchySurfaceOn_secondCountable hglue hG.1 hC₁
      hlocal
  refine le_antisymm hV₀.le ?_
  by_contra hnot
  -- `V₀` meets `U₁ ∩ U₂` along `S`, which `U₁ ∩ U₂` reaches (`hsplit`) as soon as it is not `⊆ V₀`
  obtain ⟨x, hx, -⟩ := SetLike.not_le_iff_exists.1 hnot
  have hne : (((U₁ ⊓ U₂ : Opens M) : Set M) ∩ C.maxCommonDevelopment S U₁ U₂ agree).Nonempty := by
    obtain ⟨s, hsS, -⟩ | ⟨s, hsS, -⟩ := hsplit x hx.1 <;>
      exact ⟨s, hV₀.le (hV₀.subset hsS), hV₀.subset hsS⟩
  -- a frontier point `q` of `V₀` in `U₁ ∩ U₂` (`U₁ ∩ U₂` connected)
  obtain ⟨q, hq⟩ := exists_mem_frontier_inter hconn (C.maxCommonDevelopment S U₁ U₂ agree).isOpen
    hne fun h => hnot h
  -- Step 2: a spacelike frontier point `p` in `U₁ ∩ U₂`
  obtain ⟨p, hp, hsp⟩ := exists_isSpacelikeBoundaryPoint hG hT hsplit hK
    (fun x hx => hx.1) (hstay _ hV₀) hq
  -- Steps 3–5 (the restart): a strictly larger common development, against maximality
  obtain ⟨V', hV', hlt⟩ := hstep _ hV₀ p hp hsp
  exact lt_irrefl _ (hlt.trans_le (le_sSup hV'))

/-- **ERS19 Theorem 4.64 with `u₁` a GHD read as `S` Cauchy in `U₁`, without arc-connectedness**
(`ersthm:ThmUnique`, unmarked), on a T2, second countable background:
`ers_theorem_4_64_of_isCauchySurfaceOn_secondCountable` less `harc`. -/
theorem ers_theorem_4_64_of_isCauchySurfaceOn_secondCountable_noArc [T2Space M]
    [SecondCountableTopology M] {U₁ U₂ : Opens M}
    {agree : Opens M → Prop} (hglue : AgreementGlues agree)
    (hG : C.GloballyHyperbolicOn U₁) (hT : C.TarentinOn U₁) (hC₁ : C.IsCauchySurfaceOn U₁ S)
    (hK : C.CompactSlabs U₁ S)
    (hconn : IsPreconnected ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hlocal : ∃ V, C.IsCommonDevelopment S U₁ U₂ agree V)
    (hstay : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.FrontierStaysIn U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hstep : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.SliceRestart U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M)
        (fun _ => ∃ V', C.IsCommonDevelopment S U₁ U₂ agree V' ∧ V < V')) :
    agree (U₁ ⊓ U₂) := by
  rw [← ers_theorem_4_64_maxCommonDevelopment_of_isCauchySurfaceOn_secondCountable_noArc hglue hG
    hT hC₁ hK hconn hlocal hstay hstep]
  exact (isCommonDevelopment_maxCommonDevelopment_of_isCauchySurfaceOn_secondCountable hglue hG.1
    hC₁ hlocal).agree

/-- **Theorem 4.64 with Prop 4.63 assembled, with `S` Cauchy in `U₁`, without
arc-connectedness** (`ersthm:ThmUnique`, unmarked), on a T2, second countable background:
`ers_theorem_4_64_of_localUniqueness_of_isCauchySurfaceOn_secondCountable` less `harc`. The
common development of Step 1's existence is Prop 4.63's union
(`ers_prop_4_63_of_isCauchySurfaceOn_secondCountable`, no arc-connectedness either). -/
theorem ers_theorem_4_64_of_localUniqueness_of_isCauchySurfaceOn_secondCountable_noArc
    [T2Space M] [SecondCountableTopology M] {U₁ U₂ : Opens M}
    {agree : Opens M → Prop} (hglue : AgreementGlues agree)
    (hG : C.GloballyHyperbolicOn U₁) (hT : C.TarentinOn U₁) (hC₁ : C.IsCauchySurfaceOn U₁ S)
    (hK : C.CompactSlabs U₁ S)
    (hconn : IsPreconnected ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hloc : C.LocalUniqueness S (U₁ ⊓ U₂) agree)
    (hstay : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.FrontierStaysIn U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hstep : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.SliceRestart U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M)
        (fun _ => ∃ V', C.IsCommonDevelopment S U₁ U₂ agree V' ∧ V < V')) :
    agree (U₁ ⊓ U₂) := by
  exact ers_theorem_4_64_of_isCauchySurfaceOn_secondCountable_noArc hglue hG hT hC₁ hK hconn
    ⟨_, ers_prop_4_63_of_isCauchySurfaceOn_secondCountable hglue hG hC₁ hloc⟩ hstay hstep

/-- **ERS19 Remark 4.67, first sentence, with `S` Cauchy in `U₁`, without arc-connectedness**
(`ersrem:RemTime`, unmarked), on a T2, second countable background:
`ers_remark_4_67_of_isCauchySurfaceOn_secondCountable` less `harc`. -/
theorem ers_remark_4_67_of_isCauchySurfaceOn_secondCountable_noArc [T2Space M]
    [SecondCountableTopology M] {U₁ U₂ : Opens M}
    {agree : Opens M → Prop} (hglue : AgreementGlues agree)
    (hG : C.GloballyHyperbolicOn U₁) (hT : C.TarentinOn U₁) (hC₁ : C.IsCauchySurfaceOn U₁ S)
    (hK : C.CompactSlabs U₁ S)
    (hconn : IsPreconnected ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hlocal : ∃ V, C.IsCommonDevelopment S U₁ U₂ agree V)
    (hstay : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.FrontierStaysIn U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hstep : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.SliceRestart U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M)
        (fun _ => ∃ V', C.IsCommonDevelopment S U₁ U₂ agree V' ∧ V < V')) :
    IsGreatest {V | C.IsCommonDevelopment S U₁ U₂ agree V} (U₁ ⊓ U₂) := by
  have h := isCommonDevelopment_maxCommonDevelopment_of_isCauchySurfaceOn_secondCountable hglue
    hG.1 hC₁ hlocal
  rw [ers_theorem_4_64_maxCommonDevelopment_of_isCauchySurfaceOn_secondCountable_noArc hglue hG hT
    hC₁ hK hconn hlocal hstay hstep] at h
  exact ⟨h, fun V hV => hV.le⟩

/-! ## 3. Corollaries 4.68 and 4.69 -/

/-- **ERS19 Corollary 4.68 with `S` Cauchy in `U₁`, without arc-connectedness**
(`erscor:CorDisCon`, unmarked), on a T2, second countable background:
`ers_corollary_4_68_of_isCauchySurfaceOn_secondCountable` less `harc`. -/
theorem ers_corollary_4_68_of_isCauchySurfaceOn_secondCountable_noArc [T2Space M]
    [SecondCountableTopology M] {U₁ U₂ : Opens M}
    {agree : Opens M → Prop} (hglue : AgreementGlues agree)
    (hG : C.GloballyHyperbolicOn U₁) (hT : C.TarentinOn U₁) (hC₁ : C.IsCauchySurfaceOn U₁ S)
    (hK : C.CompactSlabs U₁ S)
    (hlocal : ∃ V, C.IsCommonDevelopment S U₁ U₂ agree V)
    (hstay : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.FrontierStaysIn U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hstep : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.SliceRestart U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M)
        (fun _ => ∃ V', C.IsCommonDevelopment S U₁ U₂ agree V' ∧ V < V'))
    (hdis : ¬ agree (U₁ ⊓ U₂)) :
    ¬ IsPreconnected ((U₁ ⊓ U₂ : Opens M) : Set M) := by
  exact fun hconn => hdis (ers_theorem_4_64_of_isCauchySurfaceOn_secondCountable_noArc hglue hG hT
    hC₁ hK hconn hlocal hstay hstep)

/-- **ERS19 Corollary 4.68 for two functions, as printed, with `S` Cauchy in `U₁`, without
arc-connectedness** (`erscor:CorDisCon`, unmarked), on a T2, second countable background:
`ers_corollary_4_68_eqOn_of_isCauchySurfaceOn_secondCountable` less `harc`. -/
theorem ers_corollary_4_68_eqOn_of_isCauchySurfaceOn_secondCountable_noArc [T2Space M]
    [SecondCountableTopology M] {β : Type v} {u₁ u₂ : M → β} {U₁ U₂ : Opens M}
    (hG : C.GloballyHyperbolicOn U₁) (hT : C.TarentinOn U₁) (hC₁ : C.IsCauchySurfaceOn U₁ S)
    (hK : C.CompactSlabs U₁ S)
    (hlocal : ∃ V, C.IsCommonDevelopment S U₁ U₂ (fun V => EqOn u₁ u₂ V) V)
    (hstay : ∀ V, C.IsCommonDevelopment S U₁ U₂ (fun V => EqOn u₁ u₂ V) V →
      C.FrontierStaysIn U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hstep : ∀ V, C.IsCommonDevelopment S U₁ U₂ (fun V => EqOn u₁ u₂ V) V →
      C.SliceRestart U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M)
        (fun _ => ∃ V', C.IsCommonDevelopment S U₁ U₂ (fun V => EqOn u₁ u₂ V) V' ∧ V < V'))
    (hx : ∃ x ∈ U₁ ⊓ U₂, u₁ x ≠ u₂ x) :
    ¬ IsPreconnected ((U₁ ⊓ U₂ : Opens M) : Set M) := by
  refine ers_corollary_4_68_of_isCauchySurfaceOn_secondCountable_noArc
    (agreementGlues_eqOn u₁ u₂) hG hT hC₁ hK hlocal hstay hstep fun h => ?_
  obtain ⟨x, hxU, hne⟩ := hx
  exact hne (h hxU)

/-- **ERS19 Corollary 4.69 with `u₁` a GHD on `M` read as `S` a Cauchy surface of `M`, without
arc-connectedness** (`erscor:globally_defined_globally_hyperbolic`, unmarked), on a T2, second
countable background: `ers_corollary_4_69_of_isCauchySurface_secondCountable` less `harc`
(`C.CausallyArcConnected`). `U₂` is preconnected because `S` is and is Cauchy in `U₂` for `C₂`
(`isPreconnected_of_isCauchySurfaceOn_of_t1_secondCountable`). -/
theorem ers_corollary_4_69_of_isCauchySurface_secondCountable_noArc [T2Space M]
    [SecondCountableTopology M] {C₂ : Causality M} {U₂ : Opens M}
    {agree : Opens M → Prop} (hglue : AgreementGlues agree)
    (hG : C.GloballyHyperbolic) (hT : C.Tarentin) (hC₁ : C.IsCauchySurface S)
    (hK : C.CompactSlabs ⊤ S)
    (hS : IsPreconnected S) (hC₂ : C₂.IsCauchySurfaceOn U₂ S)
    (hlocal : ∃ V, C.IsCommonDevelopment S ⊤ U₂ agree V)
    (hstay : ∀ V, C.IsCommonDevelopment S ⊤ U₂ agree V → C.FrontierStaysIn ⊤ S V U₂)
    (hstep : ∀ V, C.IsCommonDevelopment S ⊤ U₂ agree V →
      C.SliceRestart ⊤ S V U₂ (fun _ => ∃ V', C.IsCommonDevelopment S ⊤ U₂ agree V' ∧ V < V')) :
    agree U₂ := by
  have hSU₂ : S ⊆ U₂ := by
    obtain ⟨V, hV⟩ := hlocal
    exact fun s hs => (hV.le (hV.subset hs)).2
  have hconn : IsPreconnected (((⊤ : Opens M) ⊓ U₂ : Opens M) : Set M) := by
    rw [top_inf_eq]
    exact isPreconnected_of_isCauchySurfaceOn_of_t1_secondCountable hS hSU₂ hC₂
  have h := ers_theorem_4_64_of_isCauchySurfaceOn_secondCountable_noArc (U₁ := ⊤) hglue hG
    (tarentinOn_top.2 hT) hC₁ hK hconn hlocal
    (by rw [top_inf_eq]; exact hstay) (by rw [top_inf_eq]; exact hstep)
  rwa [top_inf_eq] at h

/-! ## 4. Corollaries 4.71 and 4.73 -/

/-- **ERS19 Corollary 4.71 with `S` Cauchy in `U₁`, without arc-connectedness**
(`erscor:CorSupLum`, unmarked), on a T2, second countable background:
`ers_corollary_4_71_of_isCauchySurfaceOn_secondCountable` less `harc`. Lemma 4.70
(`ers_lemma_4_70_secondCountable`) composed with Theorem 4.64 in the form above. -/
theorem ers_corollary_4_71_of_isCauchySurfaceOn_secondCountable_noArc [T2Space M]
    [SecondCountableTopology M] {Cτ C₂ : Causality M} {U₁ U₂ : Opens M}
    {agree : Opens M → Prop} (hglue : AgreementGlues agree)
    (hG : C.GloballyHyperbolicOn U₁) (hT : C.TarentinOn U₁)
    (hK : C.CompactSlabs U₁ S)
    (hS : IsPreconnected S) (hC₁ : C.IsCauchySurfaceOn U₁ S) (hC₂ : C₂.IsCauchySurfaceOn U₂ S)
    (hτ : Cτ.IsCausal)
    (honce : ∀ (I : Set ℝ) (γ : ℝ → M), Cτ.Inextensible ⊤ I γ →
      ∀ y ∈ γ '' I ∩ S, ∀ z ∈ γ '' I ∩ S, y = z)
    (hn₁ : InextensibleNestedOn Cτ C U₁) (hn₂ : InextensibleNestedOn Cτ C₂ U₂)
    (hlocal : ∃ V, C.IsCommonDevelopment S U₁ U₂ agree V)
    (hstay : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.FrontierStaysIn U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hstep : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.SliceRestart U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M)
        (fun _ => ∃ V', C.IsCommonDevelopment S U₁ U₂ agree V' ∧ V < V')) :
    agree (U₁ ⊓ U₂) := by
  have hSU : S ⊆ U₁ ⊓ U₂ := by
    obtain ⟨V, hV⟩ := hlocal
    exact fun s hs => hV.le (hV.subset hs)
  exact ers_theorem_4_64_of_isCauchySurfaceOn_secondCountable_noArc hglue hG hT hC₁ hK
    (ers_lemma_4_70_secondCountable hS (fun s hs => (hSU hs).1) (fun s hs => (hSU hs).2) hC₁ hC₂
      hτ honce hn₁ hn₂) hlocal hstay hstep

end Causality

namespace Causality

variable {S : Set M}

/-- **ERS19 Corollary 4.73 with `S` Cauchy in `U₁`, without arc-connectedness**
(`erscor:CorUniqueSub`, unmarked), on a T2, second countable background:
`ers_corollary_4_73_of_isCauchySurfaceOn_secondCountable` (`Causal.ErsSecondCountable`) less
`harc`. Lemma 4.72 (`ers_lemma_4_72_secondCountable`) composed with Theorem 4.64 in the form
above. -/
theorem ers_corollary_4_73_of_isCauchySurfaceOn_secondCountable_noArc [T2Space M]
    [SecondCountableTopology M] {C Cm C₂ : Causality M} {U₁ U₂ : Opens M}
    {agree : Opens M → Prop} (hglue : AgreementGlues agree)
    (hG : C.GloballyHyperbolicOn U₁) (hT : C.TarentinOn U₁) (hC₁ : C.IsCauchySurfaceOn U₁ S)
    (hK : C.CompactSlabs U₁ S)
    (hS : IsPreconnected S) (hm : Cm.IsCausal)
    (hmacausal : Cm.IsAcausal S) (hmU₁ : Cm.IsCauchySurfaceOn U₁ S)
    (hC₂ : C₂.IsCauchySurfaceOn U₂ S)
    (hnest : CurveNestedOn C₂ Cm U₂)
    (hlocal : ∃ V, C.IsCommonDevelopment S U₁ U₂ agree V)
    (hstay : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.FrontierStaysIn U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hstep : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.SliceRestart U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M)
        (fun _ => ∃ V', C.IsCommonDevelopment S U₁ U₂ agree V' ∧ V < V')) :
    agree (U₁ ⊓ U₂) := by
  have hSU : S ⊆ U₁ ⊓ U₂ := by
    obtain ⟨V, hV⟩ := hlocal
    exact fun s hs => hV.le (hV.subset hs)
  exact ers_theorem_4_64_of_isCauchySurfaceOn_secondCountable_noArc hglue hG hT hC₁ hK
    (ers_lemma_4_72_secondCountable hS (fun s hs => (hSU hs).1) (fun s hs => (hSU hs).2) hm
      hmacausal hmU₁ hC₂ hnest) hlocal hstay hstep

end Causality


section Developments

variable {β : Type v} {sol : Opens M → (M → β) → Prop} {cau : (M → β) → Causality M}
  {Cm : Causality M} {S : Set M}

/-- **"Any m-GHD is a UGHD by Corollary 4.73"** (`ghd_02_19.tex:1053`), on a T2, second countable
background, without arc-connectedness: `IsMDevelopment.isUniqueDevelopment_secondCountable`
(`Causal.ErsSecondCountable`) less `harc` (each `cau u` causally arc-connected on its domain).
That `harc` served only 4.73's `hacausal` (`isAcausalOn_of_curveNestedOn`); here Corollary 4.73
runs in its `_noArc` form, with `S` Cauchy in `U₁` for `cau u₁` from the m-development itself. -/
theorem IsMDevelopment.isUniqueDevelopment_secondCountable_noArc [T2Space M]
    [SecondCountableTopology M]
    (hsub : ∀ U u, sol U u → Causality.CurveNestedOn (cau u) Cm U)
    (hm : Cm.IsCausal) (hmacausal : Cm.IsAcausal S)
    (hS : IsPreconnected S)
    {U₁ : Opens M} {u₁ : M → β} (h : IsMDevelopment sol cau Cm S U₁ u₁)
    (hG : (cau u₁).GloballyHyperbolicOn U₁) (hT : (cau u₁).TarentinOn U₁)
    (hK : (cau u₁).CompactSlabs U₁ S)
    (hlocal : ∀ U₂ u₂, IsDevelopment sol cau S U₂ u₂ →
      ∃ V, (cau u₁).IsCommonDevelopment S U₁ U₂ (fun V : Opens M => EqOn u₁ u₂ V) V)
    (hstay : ∀ U₂ u₂, IsDevelopment sol cau S U₂ u₂ → ∀ V,
      (cau u₁).IsCommonDevelopment S U₁ U₂ (fun V : Opens M => EqOn u₁ u₂ V) V →
      (cau u₁).FrontierStaysIn U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hstep : ∀ U₂ u₂, IsDevelopment sol cau S U₂ u₂ → ∀ V,
      (cau u₁).IsCommonDevelopment S U₁ U₂ (fun V : Opens M => EqOn u₁ u₂ V) V →
      (cau u₁).SliceRestart U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M)
        (fun _ => ∃ V', (cau u₁).IsCommonDevelopment S U₁ U₂
          (fun V : Opens M => EqOn u₁ u₂ V) V' ∧ V < V')) :
    IsUniqueDevelopment sol cau S U₁ u₁ := by
  refine ⟨h.1, fun U₂ u₂ h₂ => ?_⟩
  exact Causality.ers_corollary_4_73_of_isCauchySurfaceOn_secondCountable_noArc (C := cau u₁)
    (C₂ := cau u₂) (Cm := Cm) (agreementGlues_eqOn u₁ u₂) hG hT h.1.cauchy hK hS hm hmacausal
    h.2 h₂.cauchy (hsub _ _ h₂.solves) (hlocal U₂ u₂ h₂) (hstay U₂ u₂ h₂) (hstep U₂ u₂ h₂)

end Developments

/-! ## 5. Witnesses (kb/0011) -/

namespace ErsNoArcWitness

open Causality

/-- The agreement of the witness: `u₁ = id` and `u₂` the clamp to `[-1, 1]` agree on `V`; they
agree on an open set iff it lies in `[-1, 1]` (the data of
`timelikeLine_ers_theorem_4_64_of_isCauchySurfaceOn_secondCountable`). -/
def clampAgree : Opens ℝ → Prop := fun V => EqOn (id : ℝ → ℝ) (fun x => max (-1) (min x 1)) V

theorem agreementGlues_clampAgree : AgreementGlues clampAgree :=
  agreementGlues_eqOn _ _

theorem clampAgree_of_subset {V : Opens ℝ} (hV : (V : Set ℝ) ⊆ Ioo (-1) 1) : clampAgree V :=
  fun x hx => by
    obtain ⟨h1, h2⟩ := hV hx
    simp [min_eq_left h2.le, max_eq_right h1.le]

theorem coe_top_inf_ersWitnessIoo :
    (((⊤ : Opens ℝ) ⊓ ersWitnessIoo : Opens ℝ) : Set ℝ) = Ioo (-1) 1 := by
  rw [Opens.coe_inf, Opens.coe_top, univ_inter]; rfl

section Up

variable {D : Causality ℝ} (hup : ∀ {U : Opens ℝ} {x y : ℝ}, D.le U x y → x ≤ y)
  (hsub : ∀ {U : Opens ℝ} {x y : ℝ}, timelikeLine.le U x y → D.le U x y)
include hup hsub

/-- A causality of `ℝ` going up and containing the timelike line's relations has `x ≤_ℝ y` iff
`x ≤ y`. -/
theorem le_top_iff {x y : ℝ} : D.le ⊤ x y ↔ x ≤ y :=
  ⟨hup, fun h => hsub ⟨h, fun _ _ => trivial⟩⟩

/-- **The hypotheses of the `…_noArc` forms on `ℝ`**, for every causality `D` of `ℝ` going up and
containing the timelike line's relations: `S = {0}`, `U₁ = ℝ`, `U₂ = ]-1, 1[`, the agreement
`clampAgree`. `D` is GH and tarentin on `ℝ`, `{0}` is Cauchy in `ℝ` and in `]-1, 1[`, the slabs
are compact, local uniqueness holds (by `]-1/2, 1/2[`), a common development exists, and the
restart and the frontier hypotheses hold. `D`'s causal curves are the timelike line's
(`DensWitness.isCauchySurfaceOn_iff_timelike`), and `≤_ℝ` is `≤`. -/
theorem data :
    D.GloballyHyperbolicOn ⊤ ∧ D.TarentinOn ⊤ ∧ D.IsCauchySurfaceOn ⊤ ({0} : Set ℝ) ∧
      D.IsCauchySurfaceOn ersWitnessIoo ({0} : Set ℝ) ∧ D.CompactSlabs ⊤ ({0} : Set ℝ) ∧
      D.LocalUniqueness ({0} : Set ℝ) (⊤ ⊓ ersWitnessIoo) clampAgree ∧
      (∃ V, D.IsCommonDevelopment ({0} : Set ℝ) ⊤ ersWitnessIoo clampAgree V) ∧
      (∀ V, D.IsCommonDevelopment ({0} : Set ℝ) ⊤ ersWitnessIoo clampAgree V →
        D.FrontierStaysIn ⊤ {0} V (((⊤ : Opens ℝ) ⊓ ersWitnessIoo : Opens ℝ) : Set ℝ)) ∧
      (∀ V, D.IsCommonDevelopment ({0} : Set ℝ) ⊤ ersWitnessIoo clampAgree V →
        D.SliceRestart ⊤ {0} V (((⊤ : Opens ℝ) ⊓ ersWitnessIoo : Opens ℝ) : Set ℝ)
          (fun _ => ∃ V', D.IsCommonDevelopment ({0} : Set ℝ) ⊤ ersWitnessIoo clampAgree V' ∧
            V < V')) := by
  have hle : ∀ {x y : ℝ}, D.le ⊤ x y ↔ x ≤ y := le_top_iff hup hsub
  have hcau : ∀ {W : Opens ℝ} {S : Set ℝ},
      D.IsCauchySurfaceOn W S ↔ timelikeLine.IsCauchySurfaceOn W S :=
    DensWitness.isCauchySurfaceOn_iff_timelike hup hsub
  have hdiam : ∀ p q : ℝ, D.diamond ⊤ p q = Icc p q := fun p q => by
    ext z; rw [mem_diamond, hle, hle]; rfl
  have hG : D.GloballyHyperbolicOn ⊤ :=
    ⟨fun _ _ h₁ h₂ => le_antisymm (hup h₁) (hup h₂), fun p q => by
      rw [hdiam]; exact isCompact_Icc⟩
  have hT : D.TarentinOn ⊤ := by
    refine tarentinOn_top.2 fun x N hN => ?_
    obtain ⟨l, u, ⟨hl, hu⟩, hlu⟩ := mem_nhds_iff_exists_Ioo_subset.1 hN
    refine ⟨(l + x) / 2, hlu ⟨by linarith, by linarith⟩, (x + u) / 2,
      hlu ⟨by linarith, by linarith⟩, ?_⟩
    rw [Causality.openDiamond, hdiam]
    exact interior_maximal Ioo_subset_Icc_self isOpen_Ioo ⟨by linarith, by linarith⟩
  have hC₁ : D.IsCauchySurfaceOn ⊤ ({0} : Set ℝ) := hcau.2 timelikeLine_isCauchySurface_zero
  have hC₂ : D.IsCauchySurfaceOn ersWitnessIoo ({0} : Set ℝ) :=
    hcau.2 (timelikeLine_isCauchySurfaceOn_Ioo one_pos rfl)
  have hK : D.CompactSlabs ⊤ ({0} : Set ℝ) := by
    intro q
    have h1 : D.Jminus ⊤ {q} ∩ D.Jplus ⊤ ({0} : Set ℝ) = Icc 0 q := by
      ext z
      simp only [mem_inter_iff, Precausality.mem_Jminus_singleton, Precausality.mem_Jplus,
        mem_singleton_iff, exists_eq_left, hle, mem_Icc]
      tauto
    have h2 : D.Jplus ⊤ {q} ∩ D.Jminus ⊤ ({0} : Set ℝ) = Icc q 0 := by
      ext z
      simp only [mem_inter_iff, Precausality.mem_Jplus_singleton, Precausality.mem_Jminus,
        mem_singleton_iff, exists_eq_left, hle, mem_Icc]
    exact ⟨h1 ▸ isCompact_Icc, h2 ▸ isCompact_Icc⟩
  have hloc : D.LocalUniqueness ({0} : Set ℝ) (⊤ ⊓ ersWitnessIoo) clampAgree := by
    rintro p rfl
    refine ⟨⟨Ioo (-(1 / 2)) (1 / 2), isOpen_Ioo⟩, show (0 : ℝ) ∈ Ioo (-(1 / 2)) (1 / 2) by
      constructor <;> norm_num, fun x hx => ?_, clampAgree_of_subset fun x hx =>
      ⟨by linarith [hx.1], by linarith [hx.2]⟩, {0}, subset_rfl,
      hcau.2 (timelikeLine_isCauchySurfaceOn_Ioo one_half_pos rfl)⟩
    rw [← SetLike.mem_coe, coe_top_inf_ersWitnessIoo]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hcdI : ∀ (r : ℝ), 0 < r → r ≤ 1 → ∀ V : Opens ℝ, (V : Set ℝ) = Ioo (-r) r →
      D.IsCommonDevelopment ({0} : Set ℝ) ⊤ ersWitnessIoo clampAgree V := by
    intro r hr hr1 V hV
    have hsubV : (V : Set ℝ) ⊆ Ioo (-1) 1 := by
      rw [hV]; exact Ioo_subset_Ioo (by linarith) hr1
    refine ⟨fun x hx => ?_, ?_, clampAgree_of_subset hsubV,
      hcau.2 (timelikeLine_isCauchySurfaceOn_Ioo hr hV)⟩
    · rw [← SetLike.mem_coe, coe_top_inf_ersWitnessIoo]; exact hsubV hx
    · rw [singleton_subset_iff, hV]; exact ⟨by linarith, hr⟩
  have hcd : D.IsCommonDevelopment ({0} : Set ℝ) ⊤ ersWitnessIoo clampAgree
      (⊤ ⊓ ersWitnessIoo) :=
    hcdI 1 one_pos le_rfl _ coe_top_inf_ersWitnessIoo
  refine ⟨hG, hT, hC₁, hC₂, hK, hloc,
    ⟨⟨Ioo (-(1 / 2)) (1 / 2), isOpen_Ioo⟩, hcdI (1 / 2) one_half_pos one_half_lt_one.le _ rfl⟩,
    ?_, ?_⟩
  · -- `FrontierStaysIn`: `J⁻(q) ∩ J⁺(0) = [0, q] ⊆ ]-1, 1[`, and the past form
    intro V _ q hq
    rw [coe_top_inf_ersWitnessIoo] at hq ⊢
    refine ⟨fun _ z hz => ?_, fun _ z hz => ?_⟩
    · obtain ⟨⟨hzq, ⟨_, rfl, h0z⟩⟩, -⟩ := hz
      rw [Precausality.mem_Jminus_singleton, hle] at hzq
      rw [hle] at h0z
      exact ⟨by linarith, hzq.trans_lt hq.2.2⟩
    · obtain ⟨⟨hqz, ⟨_, rfl, hz0⟩⟩, -⟩ := hz
      rw [Precausality.mem_Jplus_singleton, hle] at hqz
      rw [hle] at hz0
      exact ⟨hq.2.1.trans_le hqz, by linarith⟩
  · -- `SliceRestart`: `V' = ]-1, 1[`; the frontier point `p ∈ ]-1, 1[` is not in `V`
    intro V hV p hp _
    refine ⟨⊤ ⊓ ersWitnessIoo, hcd, lt_of_le_of_ne hV.le fun hVeq => ?_⟩
    have hpV : p ∈ (V : Set ℝ) := by rw [hVeq]; exact hp.2
    have := hp.1
    rw [V.isOpen.frontier_eq] at this
    exact this.2 hpV

/-- **The `…_noArc` forms of Theorem 4.64, Remark 4.67 and Corollary 4.69 on `ℝ`**, for every
causality `D` of `ℝ` going up and containing the timelike line's relations, on the data of
`data`: the solutions agree on `U₁ ∩ U₂ = ]-1, 1[` (Thm 4.64), `]-1, 1[` is the maximal common
development (its `_maxCommonDevelopment_` form) and the greatest one (Rem 4.67, first sentence),
and the solutions agree on `U₂` (Cor 4.69, `U₁ = ℝ`, `C₂ = D`). -/
theorem conclusions :
    clampAgree (⊤ ⊓ ersWitnessIoo) ∧
      D.maxCommonDevelopment ({0} : Set ℝ) ⊤ ersWitnessIoo clampAgree = ⊤ ⊓ ersWitnessIoo ∧
      IsGreatest {V | D.IsCommonDevelopment ({0} : Set ℝ) ⊤ ersWitnessIoo clampAgree V}
        (⊤ ⊓ ersWitnessIoo) ∧
      clampAgree ersWitnessIoo := by
  obtain ⟨hG, hT, hC₁, hC₂, hK, -, hlocal, hstay, hstep⟩ := data hup hsub
  have hconn : IsPreconnected (((⊤ : Opens ℝ) ⊓ ersWitnessIoo : Opens ℝ) : Set ℝ) := by
    rw [coe_top_inf_ersWitnessIoo]; exact isPreconnected_Ioo
  refine ⟨ers_theorem_4_64_of_isCauchySurfaceOn_secondCountable_noArc agreementGlues_clampAgree
      hG hT hC₁ hK hconn hlocal hstay hstep,
    ers_theorem_4_64_maxCommonDevelopment_of_isCauchySurfaceOn_secondCountable_noArc
      agreementGlues_clampAgree hG hT hC₁ hK hconn hlocal hstay hstep,
    ers_remark_4_67_of_isCauchySurfaceOn_secondCountable_noArc agreementGlues_clampAgree hG hT
      hC₁ hK hconn hlocal hstay hstep,
    ers_corollary_4_69_of_isCauchySurface_secondCountable_noArc (C₂ := D)
      agreementGlues_clampAgree hG (tarentinOn_top.1 hT) hC₁ hK isPreconnected_singleton hC₂
      hlocal (by simpa only [top_inf_eq] using hstay) (by simpa only [top_inf_eq] using hstep)⟩

/-- **The `…_noArc` forms of Theorem 4.64 with local uniqueness, Corollary 4.71 and Corollary
4.73 on `ℝ`**, on the data of `data`: three proofs that the solutions agree on `]-1, 1[`, by
`ers_theorem_4_64_of_localUniqueness_of_isCauchySurfaceOn_secondCountable_noArc` (with
`LocalUniqueness` in place of a given common development), by
`ers_corollary_4_71_of_isCauchySurfaceOn_secondCountable_noArc` (`Cτ = C₂ = D`, nested in itself;
`D` causal; a curve meets `{0}` at most once) and by
`ers_corollary_4_73_of_isCauchySurfaceOn_secondCountable_noArc` (`Cm = C₂ = D`, curve-nested in
itself; `{0}` acausal for `Cm`). Each conjunct witnesses that form's hypotheses. -/
theorem corollaries :
    clampAgree (⊤ ⊓ ersWitnessIoo) ∧ clampAgree (⊤ ⊓ ersWitnessIoo) ∧
      clampAgree (⊤ ⊓ ersWitnessIoo) := by
  obtain ⟨hG, hT, hC₁, hC₂, hK, hloc, hlocal, hstay, hstep⟩ := data hup hsub
  have hconn : IsPreconnected (((⊤ : Opens ℝ) ⊓ ersWitnessIoo : Opens ℝ) : Set ℝ) := by
    rw [coe_top_inf_ersWitnessIoo]; exact isPreconnected_Ioo
  have honce : ∀ (I : Set ℝ) (γ : ℝ → ℝ), D.Inextensible ⊤ I γ →
      ∀ y ∈ γ '' I ∩ ({0} : Set ℝ), ∀ z ∈ γ '' I ∩ ({0} : Set ℝ), y = z :=
    fun _ _ _ _ hy _ hz => (mem_singleton_iff.1 hy.2).trans (mem_singleton_iff.1 hz.2).symm
  refine ⟨ers_theorem_4_64_of_localUniqueness_of_isCauchySurfaceOn_secondCountable_noArc
      agreementGlues_clampAgree hG hT hC₁ hK hconn hloc hstay hstep,
    ers_corollary_4_71_of_isCauchySurfaceOn_secondCountable_noArc (Cτ := D) (C₂ := D)
      agreementGlues_clampAgree hG hT hK isPreconnected_singleton hC₁ hC₂ hG.1 honce
      (fun _ _ h => h) (fun _ _ h => h) hlocal hstay hstep,
    ers_corollary_4_73_of_isCauchySurfaceOn_secondCountable_noArc (Cm := D) (C₂ := D)
      agreementGlues_clampAgree hG hT hC₁ hK isPreconnected_singleton hG.1
      (fun x hx y hy _ => (mem_singleton_iff.1 hx).trans (mem_singleton_iff.1 hy).symm)
      hC₁ hC₂ (fun _ _ _ h => h) hlocal hstay hstep⟩

end Up

end ErsNoArcWitness

open ErsNoArcWitness in
/-- **A proper instance of the `…_noArc` forms** (kb/0011): on the timelike line, `U₁ = ℝ`,
`U₂ = ]-1, 1[`, `S = {0}`, `u₁ = id`, `u₂` the clamp to `[-1, 1]`, `C₂ = C`: the data of
`timelikeLine_ers_theorem_4_64_of_isCauchySurfaceOn_secondCountable`, with no arc-connectedness
asked. The solutions agree on `U₁ ∩ U₂`, which is the maximal and the greatest common development,
and on `U₂` (Cor 4.69). -/
theorem timelikeLine_ers_theorem_4_64_of_isCauchySurfaceOn_secondCountable_noArc :
    clampAgree (⊤ ⊓ ersWitnessIoo) ∧
      timelikeLine.maxCommonDevelopment ({0} : Set ℝ) ⊤ ersWitnessIoo clampAgree =
        ⊤ ⊓ ersWitnessIoo ∧
      IsGreatest {V | timelikeLine.IsCommonDevelopment ({0} : Set ℝ) ⊤ ersWitnessIoo clampAgree V}
        (⊤ ⊓ ersWitnessIoo) ∧
      clampAgree ersWitnessIoo :=
  conclusions (D := timelikeLine) (fun h => h.1) fun h => h

open ErsNoArcWitness in
/-- **The `…_noArc` forms apply where the trade forms do not** (kb/0011): `densCausality`
(`Causal.CBG.SubExtensionAbstract`: `x ≤_U y` iff `x ≤ y`, `x, y ∈ U` and `U` fills at least half
of `]x, y]`) is not causally arc-connected on `ℝ` (it is not even absolutely minimal:
`0 ≤ 1` in `]-1/4, 1/4[ ∪ ]1/2, 5/4[`), so `harc` fails and the trade forms of
`Causal.Ers464SecondCountable` do not apply; it goes up and contains the timelike line's
relations, so the hypotheses of the 4.64 (two forms), 4.67 and 4.69 `…_noArc` forms hold on the
witness data, and they give their conclusions (4.71/4.73 follow from `corollaries`, not stated
here; 4.68's `hdis` fails on this data, and the m-GHD form has no witness). (`{0}` is acausal there, so the originals of `Causal.ErsUniqueness` apply too.) -/
theorem densCausality_ers_theorem_4_64_of_isCauchySurfaceOn_secondCountable_noArc :
    ¬ DensWitness.densCausality.CausallyArcConnectedOn ⊤ ∧
      clampAgree (⊤ ⊓ ersWitnessIoo) ∧
      DensWitness.densCausality.maxCommonDevelopment ({0} : Set ℝ) ⊤ ersWitnessIoo clampAgree =
        ⊤ ⊓ ersWitnessIoo ∧
      IsGreatest {V | DensWitness.densCausality.IsCommonDevelopment ({0} : Set ℝ) ⊤ ersWitnessIoo
        clampAgree V} (⊤ ⊓ ersWitnessIoo) ∧
      clampAgree ersWitnessIoo := by
  refine ⟨fun h => ?_, conclusions (D := DensWitness.densCausality)
    (fun h => (DensWitness.densCausality_le.1 h).1) DensWitness.densCausality_le_of_timelike⟩
  -- the ladder step `causally_arc_connected ⇒ absolutely_minimal`
  have h' : DensWitness.densCausality.CausallyArcConnected := h
  have hmin : DensWitness.densCausality.AbsolutelyMinimal := by causal_ladder
  exact DensWitness.not_absolutelyMinimalOn_witness.1 (Precausality.absolutelyMinimal_iff.1 hmin)

end Causal
