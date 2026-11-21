import Causal.ErsUniqueness
import Causal.LinesCurves
import Causal.NestedConverse
import Causal.Ladder.Rules

/-!
# ERS19 Theorems 4.79 and 4.80 on a fixed background: the MUGHD and the unique m-MGHD

Programme target `T-abs-ers-mughd` (`programme/roadmap.toml`; layer 1, ETT-layer imports only,
no model, no metric). Source: Eperon–Reall–Sbierski, arXiv 1802.03020, `papers/ers-predictability`
(`legacy/labeled/ghd_02_19.tex`; text `references/sbierski/text/eperon2018predictability.txt`).
Causal-topological skeletons whose PDE, Lorentzian and Minkowski inputs are named hypotheses;
**no label is marked**:

* `ersrem:RemMGHD` — `ghd_02_19.tex:1047`: `ers_remark_4_78` (pairwise agreeing developments
  glue to a development on the union), with `exists_eqOn_of_pairwise` and the union lemma
  `Causality.isCauchySurfaceOn_iSup_of_isAcausalOn`.
* `ersthm:ThmMUGHD` — `ghd_02_19.tex:1055` (proof 1060–1064): `ers_theorem_4_79` (the MUGHD
  exists), `ers_theorem_4_79_of_exists` (from one UGHD), `IsMDevelopment.isUniqueDevelopment`
  (`ghd_02_19.tex:1053`, "any m-GHD is a UGHD by Corollary 4.73", through
  `Causality.ers_corollary_4_73`), `IsDevelopment.exists_isMDevelopment_le` (`D_m(S) ∩ U₁`),
  `IsMaximalUniqueDevelopment.unique`, `IsMaximalUniqueDevelopment.eqOn`.
* `ersthm:consider_subluminal_quasilinear_wave` — `ghd_02_19.tex:1066` (proof 1071–1073):
  `ers_theorem_4_80` (the m-MGHD exists), `ers_theorem_4_80_of_exists`,
  `IsMaximalMDevelopment.unique`; ERS's summary (`ghd_02_19.tex:1075`) "the m-MGHD is contained
  in the MUGHD": `IsMaximalMDevelopment.le_of_isMaximalUniqueDevelopment`.

> Remark 4.78. We note that the above construction of a unique maximal globally hyperbolic
> development is always possible provided the property of global uniqueness holds.

> We call a GHD u1 : U1 → R a unique globally hyperbolic development (UGHD) iff for all other
> GHDs u2 : U2 → R we have u1 = u2 on U1 ∩ U2. We note that any m-GHD is a UGHD by Corollary 4.73.

> Theorem 4.79. Consider a subluminal quasilinear wave equation of the form (4.61). Given
> initial data on a connected hypersurface S that is acausal with respect to the Minkowski metric
> there exists a UGHD u : U → R with the property that the domain of any other UGHD is
> contained in U. The UGHD u : U → R is called the maximal unique globally hyperbolic
> development (MUGHD).

> Theorem 4.80. Consider a subluminal quasilinear wave equation of the form (4.61). Given
> initial data on a connected hypersurface S that is acausal with respect to the Minkowski metric
> there exists a unique m-MGHD, i.e., a m-GHD umax : Umax → R with the property that for any
> other m-GHD u : U → R of the same initial data we have U ⊆ Umax and umax|U = u.

## The reading

* **The equation is abstract.** `sol U u`: "`u` solves (4.61) on `U` with the data on `S`", for
  `u : M → β` of which only `u|U` matters (`SolutionLocal`), local in `U` (`SolutionsGlue`).
  `cau u`: the causality of `g(u, du)`, time-oriented by `m` (subluminal), which on `V ≤ W`
  depends only on `u|W` (`CausalityFollows`). `Cm`: Minkowski's causality.
* **Developments**: `IsDevelopment sol cau S U u` (ERS's GHD) — `u` solves on `U ⊇ S`, and `S`
  is a Cauchy surface of `U` for `cau u`; global hyperbolicity is not asked (as
  `Causality.ers_theorem_4_77` and `IsCommonDevelopment`, OQ-57 (c)). `IsMDevelopment` (m-GHD)
  adds `S` Cauchy in `U` for `Cm`; `IsUniqueDevelopment` (UGHD) agrees with every development on
  the overlap; `IsMaximalUniqueDevelopment` (MUGHD); `IsMaximalMDevelopment` (m-MGHD).
* **Subluminality** is curve nesting `CurveNestedOn (cau u) Cm U` (ladder `curve_nested`), as in
  `ers_lemma_4_72`, with `≤` of `g(u)` realised by its causal curves (`CausallyArcConnectedOn U`,
  ladder `causally_arc_connected` read on `U`): then `≤_U` of `g(u)` lies in `≤` of `m`
  (`Causality.le_top_of_curveNestedOn`).

## Hypothesis checklist

| paper | here |
|---|---|
| (4.61) subluminal | ⚠ named, for every solution: `hsub` (`curve_nested`), `harc` (`causally_arc_connected` on `U`) |
| (4.61), same data | ⚠ abstract: `sol`, `SolutionLocal`, `SolutionsGlue` (non-empty families); `cau`, `CausalityFollows` |
| `S` connected | ⚠ weakened: `IsPreconnected S` (used by Cor 4.73 only) |
| `S` m-acausal | ✓ `Cm.IsAcausal S` |
| Minkowski space | ⚠ named: `Cm.IsCausal` (`is_causal`); `Cm.CurvesExtend` (`curves_extend`, Cor 4.73 only) |
| GHD: GH with Cauchy `S` | ⚠ read: `S` Cauchy in `U` for `cau u`; GH of each m-GHD named where Cor 4.73 uses it (`hG`) |
| Thm 4.75: a GHD exists | ⚠ named: `hex` |
| `D_m(S) ∩ U₁` an m-GHD (O'Neill 14.38, 14.43) | ⚠ named: `hDm` (Minkowski: `W ≤ U₁` open, `S ⊆ W` m-Cauchy, `u₁` solves on `W`); its `g`-Cauchy property from `hinext` (`InextensibleNestedOn`, proposed `inextensible_nested`, OQ-41 (b)) |
| Cor 4.73 | ✓ composed (`Causality.ers_corollary_4_73`), its named hypotheses kept: `hG`, `hT`, `hK` on each m-GHD, `hthrough` on each GHD, `hlocal`, `hstay`, `hstep` per pair (m-GHD, GHD); its `hacausal`, `hsplit`, `hnest`, `hthrough₂` derived |
| 4.79: "`u(x) := uα(x)` well-defined" | ✓ proved (`exists_eqOn_of_pairwise`) |
| 4.79, 4.80: "the same argument as in 4.77" | ⚠ read: `S` Cauchy in the union (`isCauchySurfaceOn_iSup_of_isAcausalOn`), GH not concluded; 4.77's `hpair` (Rem 4.67) and `hcaus` not needed |

## SCOPE (disclosed)

* **No label is marked.** The PDE, Lorentzian and Minkowski inputs are named hypotheses (layer 2
  and 3), and a GHD is read "`S` a Cauchy surface", not "GH with Cauchy surface `S`": GH of a union
  is Geroch (iii) ⇒ (i), unproved (`CausalScaffold.GerochEquiv`), as in `ers_theorem_4_77`.
* **The union.** `ers_theorem_4_77_greatest` is not used: it is a statement about one causality
  `C` and all open sets of which `S` is a `C`-Cauchy surface, with no solution, so it is not the
  set of UGHDs (or m-GHDs); and `ers_theorem_4_77` applied to the family under `C = cau v` would
  need `hpair` (`S` Cauchy in each pairwise overlap, to be proved through Thm 4.64 with its named
  hypotheses for every pair) and `hcaus`. `isCauchySurfaceOn_iSup_of_isAcausalOn` needs no
  `hpair` (`S` acausal in the union instead) but takes `hcaus` (`≤` antisymmetric there);
  `ers_remark_4_78` needs neither, deriving both from subluminality and `Cm`.
* **ERS's appeal to Remark 4.67 for UGHDs.** "The same argument as in the proof of Theorem 4.77"
  (`ghd_02_19.tex:1063`) uses Remark 4.67 (at `:1042`), stated under Thm 4.64's connectedness
  (`:915`), for pairs of UGHDs, without checking that their overlap is connected. It is, in ERS's
  setting (subluminal, `S` connected and m-acausal, orientations by `m`): two GHDs agreeing on
  their overlap have a connected overlap, by the argument of Lemma 4.72 with `U₁`'s `g`-Cauchy
  property and the agreement (`g(u₁) = g(u₂)` on `U₁ ∩ U₂`) in place of `U₁`'s m-global
  hyperbolicity. The Lean route bypasses the question: `S` is acausal in the union for `g(v)`.
* **Time orientation.** `cau u` is a function of the solution (`CausalityFollows`): `g(u, du)`
  time-oriented by `m`, which a subluminal equation allows. ERS's stipulation (Remark 4.67, "the
  normal of `S` future directed in `U₁` as well as in `U₂`") is then automatic on every overlap.
* **For every solution.** `hsub`, `harc`, `hinext` are asked of every `(U, u)` with `sol U u`,
  not only of developments: they are used for the glued solution on the union before it is known
  to be a development. `hDm` names the interior of the domain of dependence of `S` in `U₁` for
  `m` (O'Neill 14.38, 14.43), with `u₁` restricted to it a solution.
* **Not formalised**: the two example claims of `ghd_02_19.tex:1075`, "there are in general GHDs
  which are not contained in the maximal UGHD" and "in general the latter is strictly bigger".
* **Witness** (kb/0011): `timelikeLine_ers_theorem_4_79_4_80`, degenerate (one development
  domain, `ℝ`), every hypothesis discharged on the timelike line, `S = {0}`; `causal_ladder`
  derives the causality of the line from its global hyperbolicity.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Function

universe u v

variable {M : Type u} [TopologicalSpace M]

/-! ## 1. Unions of Cauchy developments, and subluminality -/

namespace Causality

variable {C Cm : Causality M} {S : Set M}

/-- **The union of open sets of which `S` is a Cauchy surface has `S` as Cauchy surface**, when
`S` is acausal in the union and `≤` is antisymmetric there (`M` Hausdorff). An inextensible curve
of the union meets `S` through its component in one member, and at most once because `S` is
acausal. ERS Theorem 4.77's Cauchy property ("the same argument as in the proof of Theorem 4.77",
`ghd_02_19.tex:1063, 1072`) with the acausality of `S` in place of Remark 4.67 for each pair
(`ers_theorem_4_77`'s `hpair`). -/
theorem isCauchySurfaceOn_iSup_of_isAcausalOn [T2Space M] {ι : Sort*} {U : ι → Opens M}
    (hanti : ∀ ⦃x y : M⦄, C.le (⨆ i, U i) x y → C.le (⨆ i, U i) y x → x = y)
    (hacausal : C.IsAcausalOn (⨆ i, U i) S) (hU : ∀ i, C.IsCauchySurfaceOn (U i) S) :
    C.IsCauchySurfaceOn (⨆ i, U i) S := by
  intro I c hc
  obtain ⟨t₀, ht₀⟩ := hc.1.nonempty
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hc.1.mem ht₀)
  obtain ⟨_, ⟨⟨τ, hτ, rfl⟩, hτS⟩, -⟩ :=
    hU i _ c (inextensible_ordConnectedComponent_of_le hanti (le_iSup U i) hc ht₀ hi)
  have hτI : τ ∈ I := (ordConnectedComponent_subset hτ).1
  refine ⟨c τ, ⟨⟨τ, hτI, rfl⟩, hτS⟩, ?_⟩
  rintro _ ⟨⟨σ, hσ, rfl⟩, hσS⟩
  rcases le_total σ τ with h | h
  · exact hacausal _ hσS _ hτS (hc.1.le_of_le hσ hτI h)
  · exact (hacausal _ hτS _ hσS (hc.1.le_of_le hτI hσ h)).symm

/-- **Subluminality gives ≤-nesting on an open set**: if `≤_U` of `C` is realised by causal curves
(`C` causally arc-connected on `U`) and the causal curves of `U` for `C` are causal curves for
`Cm` (curve nesting), then `x ≤_U y` for `C` gives `x ≤ y` for `Cm` in `M`. The form at `M` of
`CurveNestedOn.le_of_causallyArcConnectedOn` (`Causal.NestedConverse`). -/
theorem le_top_of_curveNestedOn {U : Opens M} (hC : C.CausallyArcConnectedOn U)
    (hn : CurveNestedOn C Cm U) {x y : M} (h : C.le U x y) : Cm.le ⊤ x y :=
  Cm.le_mono le_top (hn.le_of_causallyArcConnectedOn hC le_rfl h)

/-- Under subluminality, `≤_U` of `C` is antisymmetric when `Cm` is causal. -/
theorem antisymm_of_curveNestedOn {U : Opens M} (hC : C.CausallyArcConnectedOn U)
    (hn : CurveNestedOn C Cm U) (hm : Cm.IsCausal) ⦃x y : M⦄ (hxy : C.le U x y)
    (hyx : C.le U y x) : x = y :=
  hm (le_top_of_curveNestedOn hC hn hxy) (le_top_of_curveNestedOn hC hn hyx)

/-- Under subluminality, an `m`-acausal set is acausal in `U` for `C`. -/
theorem isAcausalOn_of_curveNestedOn {U : Opens M} (hC : C.CausallyArcConnectedOn U)
    (hn : CurveNestedOn C Cm U) (hS : Cm.IsAcausal S) : C.IsAcausalOn U S :=
  fun x hx y hy h => hS x hx y hy (le_top_of_curveNestedOn hC hn h)

/-- **The union of open sets of which an acausal `S` is a Cauchy surface, for a causal `Cm`**,
has `S` as Cauchy surface (the m-part of Theorem 4.80: the union of the m-GHDs is m-Cauchy). -/
theorem isCauchySurfaceOn_sSup_of_isCausal [T2Space M] (hm : Cm.IsCausal)
    (hS : Cm.IsAcausal S) {𝒰 : Set (Opens M)} (h𝒰 : ∀ U ∈ 𝒰, Cm.IsCauchySurfaceOn U S) :
    Cm.IsCauchySurfaceOn (sSup 𝒰) S := by
  rw [sSup_eq_iSup']
  exact isCauchySurfaceOn_iSup_of_isAcausalOn
    (fun _ _ h₁ h₂ => hm (Cm.le_mono le_top h₁) (Cm.le_mono le_top h₂)) (hS.isAcausalOn _)
    fun U => h𝒰 U.1 U.2

end Causality

/-! ## 2. Developments of one initial value problem on a fixed background -/

section Developments

variable {β : Type v}

/-- **A solution sees only its domain**: if `u = v` on `U`, `u` solves on `U` iff `v` does.
Supplier: (4.61) and its initial condition on `S ∩ U` are conditions on `u|U` (layer 3). -/
def SolutionLocal (sol : Opens M → (M → β) → Prop) : Prop :=
  ∀ ⦃U : Opens M⦄ ⦃u v : M → β⦄, EqOn u v U → sol U u → sol U v

/-- **Solutions glue**: a function solving on every member of a non-empty family of open sets
solves on its union. Supplier: (4.61) and its initial condition are local. -/
def SolutionsGlue (sol : Opens M → (M → β) → Prop) : Prop :=
  ∀ (𝒰 : Set (Opens M)) (v : M → β), 𝒰.Nonempty → (∀ U ∈ 𝒰, sol U v) → sol (sSup 𝒰) v

/-- **The causality follows the solution**: if `u = v` on `W`, the causalities of `g(u, du)` and
`g(v, dv)` have the same `≤_V` on every open `V ≤ W`. Supplier: `g` depends on `u`, `du` only
(4.61), time-oriented by `m` (subluminal), and `≤_V` is read off the causal curves of `V`. The
`Causality.FollowsSolution` of `Causal.ErsUniqueness` at every `W`
(`CausalityFollows.followsSolution`). -/
def CausalityFollows (cau : (M → β) → Causality M) : Prop :=
  ∀ ⦃u v : M → β⦄ ⦃W : Opens M⦄, EqOn u v W → ∀ V : Opens M, V ≤ W → ∀ x y,
    (cau u).le V x y ↔ (cau v).le V x y

/-- **A development** (ERS's GHD, read with `S` Cauchy, global hyperbolicity not asked): `u`
solves on `U ⊇ S`, and `S` is a Cauchy surface of `U` for the causality of `g(u, du)`. -/
structure IsDevelopment (sol : Opens M → (M → β) → Prop) (cau : (M → β) → Causality M)
    (S : Set M) (U : Opens M) (u : M → β) : Prop where
  solves : sol U u
  subset : S ⊆ U
  cauchy : (cau u).IsCauchySurfaceOn U S

/-- **An m-development** (ERS's m-GHD): a development of which `S` is also a Cauchy surface for
Minkowski's causality `Cm`. -/
def IsMDevelopment (sol : Opens M → (M → β) → Prop) (cau : (M → β) → Causality M)
    (Cm : Causality M) (S : Set M) (U : Opens M) (u : M → β) : Prop :=
  IsDevelopment sol cau S U u ∧ Cm.IsCauchySurfaceOn U S

/-- **A unique development** (ERS's UGHD, `ghd_02_19.tex:1053`): a development agreeing with every
development on the overlap. -/
def IsUniqueDevelopment (sol : Opens M → (M → β) → Prop) (cau : (M → β) → Causality M)
    (S : Set M) (U : Opens M) (u : M → β) : Prop :=
  IsDevelopment sol cau S U u ∧
    ∀ (U' : Opens M) (u' : M → β), IsDevelopment sol cau S U' u' → EqOn u u' (U ⊓ U' : Opens M)

/-- **The MUGHD** (ERS Theorem 4.79): a unique development whose domain contains the domain of
every unique development. -/
def IsMaximalUniqueDevelopment (sol : Opens M → (M → β) → Prop) (cau : (M → β) → Causality M)
    (S : Set M) (U : Opens M) (u : M → β) : Prop :=
  IsUniqueDevelopment sol cau S U u ∧
    ∀ (U' : Opens M) (u' : M → β), IsUniqueDevelopment sol cau S U' u' → U' ≤ U

/-- **The m-MGHD** (ERS Theorem 4.80): an m-development whose domain contains that of every
m-development, which it extends. -/
def IsMaximalMDevelopment (sol : Opens M → (M → β) → Prop) (cau : (M → β) → Causality M)
    (Cm : Causality M) (S : Set M) (U : Opens M) (u : M → β) : Prop :=
  IsMDevelopment sol cau Cm S U u ∧
    ∀ (U' : Opens M) (u' : M → β), IsMDevelopment sol cau Cm S U' u' → U' ≤ U ∧ EqOn u u' U'

variable {sol : Opens M → (M → β) → Prop} {cau : (M → β) → Causality M} {Cm : Causality M}
  {S : Set M}

/-- `CausalityFollows` gives `Causality.FollowsSolution` (`Causal.ErsUniqueness`) at every open
set, for the agreement predicate of two functions. -/
theorem CausalityFollows.followsSolution (h : CausalityFollows cau) (u₁ u₂ : M → β)
    (W : Opens M) :
    Causality.FollowsSolution (cau u₁) (cau u₂) (fun V : Opens M => EqOn u₁ u₂ V) W :=
  fun hW x y hxy => (h hW W le_rfl x y).1 hxy

/-! ### Remark 4.78: the union under global uniqueness -/

/-- **Pairwise agreeing functions glue** ("`u(x) := uα(x)` for `x ∈ Uα`. The latter is
well-defined", `ghd_02_19.tex:1063`): a non-empty family of pairs `(U, u)` agreeing on the
overlaps has a function agreeing with each `u` on its `U`. -/
theorem exists_eqOn_of_pairwise {𝒟 : Set (Opens M × (M → β))} (hne : 𝒟.Nonempty)
    (hagree : ∀ d ∈ 𝒟, ∀ d' ∈ 𝒟, EqOn d.2 d'.2 (d.1 ⊓ d'.1 : Opens M)) :
    ∃ v : M → β, ∀ d ∈ 𝒟, EqOn v d.2 d.1 := by
  classical
  obtain ⟨d₀, -⟩ := hne
  refine ⟨fun x => if h : ∃ d ∈ 𝒟, x ∈ d.1 then h.choose.2 x else d₀.2 x, fun d hd x hx => ?_⟩
  have h : ∃ d ∈ 𝒟, x ∈ d.1 := ⟨d, hd, hx⟩
  dsimp only
  rw [dif_pos h]
  exact hagree _ h.choose_spec.1 d hd ⟨h.choose_spec.2, hx⟩

/-- **ERS19 Remark 4.78, subluminal form** (`ersrem:RemMGHD`, unmarked): a non-empty family `𝒟`
of developments with a function `v` agreeing with each on its domain ("global uniqueness") gives
a development `v` on the union of the domains. The solution glues (`hloc`, `hglue`); `S` is a
Cauchy surface of each domain for `g(v)` (`hfollow`), hence of the union
(`isCauchySurfaceOn_iSup_of_isAcausalOn`), `S` being acausal and `≤` antisymmetric there for
`g(v)` by subluminality (`hsub`, `harc`) and Minkowski's causality (`hm`, `hmacausal`). -/
theorem ers_remark_4_78 [T2Space M] (hloc : SolutionLocal sol) (hglue : SolutionsGlue sol)
    (hfollow : CausalityFollows cau)
    (hsub : ∀ U u, sol U u → Causality.CurveNestedOn (cau u) Cm U)
    (harc : ∀ U u, sol U u → (cau u).CausallyArcConnectedOn U)
    (hm : Cm.IsCausal) (hmacausal : Cm.IsAcausal S)
    {𝒟 : Set (Opens M × (M → β))} (hne : 𝒟.Nonempty)
    (hdev : ∀ d ∈ 𝒟, IsDevelopment sol cau S d.1 d.2) {v : M → β}
    (hv : ∀ d ∈ 𝒟, EqOn v d.2 d.1) :
    IsDevelopment sol cau S (sSup (Prod.fst '' 𝒟)) v := by
  have hsol : sol (sSup (Prod.fst '' 𝒟)) v := by
    refine hglue _ v (hne.image _) ?_
    rintro _ ⟨d, hd, rfl⟩
    exact hloc (fun x hx => (hv d hd hx).symm) (hdev d hd).solves
  obtain ⟨d₀, hd₀⟩ := hne
  refine ⟨hsol, fun x hx => (le_sSup (mem_image_of_mem Prod.fst hd₀) :
    d₀.1 ≤ sSup (Prod.fst '' 𝒟)) ((hdev d₀ hd₀).subset hx), ?_⟩
  have hsol' : sol (⨆ d : 𝒟, d.1.1) v := by rw [← sSup_image']; exact hsol
  rw [sSup_image']
  refine Causality.isCauchySurfaceOn_iSup_of_isAcausalOn
    (Causality.antisymm_of_curveNestedOn (harc _ _ hsol') (hsub _ _ hsol') hm)
    (Causality.isAcausalOn_of_curveNestedOn (harc _ _ hsol') (hsub _ _ hsol') hmacausal)
    fun d => ?_
  exact Causality.isCauchySurfaceOn_of_agree
    (fun V hV x y => hfollow (fun z hz => (hv d.1 d.2 hz).symm) V hV x y) (hdev d.1 d.2).cauchy

/-! ### Non-emptiness: `D_m(S) ∩ U₁`, and every m-GHD is a UGHD -/

/-- **ERS19 Theorem 4.79, the non-emptiness** (`ghd_02_19.tex:1061`): inside every development
`(U₁, u₁)` lies an m-development `(W, u₁)`, `W ≤ U₁`.

Suppliers: `hDm` — Minkowski, O'Neill Ch. 14, 38. Theorem and 43. Lemma: `W` the interior of the
domain of dependence of `S` in `U₁` for `m`, globally hyperbolic for `m` with Cauchy surface `S`,
and `u₁` restricted to it a solution; `hinext` — the localisation `inextensible_nested`
(proposed, OQ-41 (b)): an inextensible causal curve of `W` for `g(u₁)` is one for `m` (it is
`m`-causal and has no endpoint in `W`), so `S`, `m`-Cauchy in `W`, is `g(u₁)`-Cauchy
(`IsCauchySurfaceOn.of_nested`). -/
theorem IsDevelopment.exists_isMDevelopment_le
    (hDm : ∀ U u, IsDevelopment sol cau S U u →
      ∃ W : Opens M, W ≤ U ∧ S ⊆ W ∧ Cm.IsCauchySurfaceOn W S ∧ sol W u)
    (hinext : ∀ U u, sol U u → Causality.InextensibleNestedOn (cau u) Cm U)
    {U : Opens M} {u : M → β} (h : IsDevelopment sol cau S U u) :
    ∃ W : Opens M, W ≤ U ∧ IsMDevelopment sol cau Cm S W u := by
  obtain ⟨W, hWU, hSW, hW, hsol⟩ := hDm U u h
  exact ⟨W, hWU, ⟨hsol, hSW, Causality.IsCauchySurfaceOn.of_nested (hinext W u hsol) hW⟩, hW⟩

/-- **"Any m-GHD is a UGHD by Corollary 4.73"** (`ghd_02_19.tex:1053`): `ers_corollary_4_73` for
`C = cau u₁`, `C₂ = cau u₂`, agreement `EqOn u₁ u₂`, against every development `(U₂, u₂)`.

Hypotheses as in `ers_corollary_4_73`, with suppliers there: `hG`, `hT`, `hK` — the m-GHD's
`g(u₁)` is GH and tarentin on `U₁` with compact slabs (T-loc-quasilinear-causal-ladder); `hthrough`
— through every point of a development an inextensible causal curve (integral curves of a
timelike field); `hlocal`, `hstay`, `hstep` — Prop 4.63, Step 2's `γ([0,1]) ⊆ U₂`, Steps 3–5 for
each pair; `hm`, `hmext`, `hmacausal`, `hS` — Minkowski causal with curves extending, `S`
m-acausal and connected; `hsub` — subluminality. Derived here: 4.73's `hacausal` (from `hsub`,
`harc`, `hmacausal`), `hsplit` (from the Cauchy property and `hthrough`), `hthrough₂`, `hnest`. -/
theorem IsMDevelopment.isUniqueDevelopment [T2Space M]
    (hsub : ∀ U u, sol U u → Causality.CurveNestedOn (cau u) Cm U)
    (harc : ∀ U u, sol U u → (cau u).CausallyArcConnectedOn U)
    (hm : Cm.IsCausal) (hmext : Cm.CurvesExtend) (hmacausal : Cm.IsAcausal S)
    (hS : IsPreconnected S)
    (hthrough : ∀ U u, IsDevelopment sol cau S U u → (cau u).InextensibleThrough U)
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
  have hsol₁ := h.1.solves
  exact Causality.ers_corollary_4_73 (C := cau u₁) (C₂ := cau u₂) (Cm := Cm)
    (agreementGlues_eqOn u₁ u₂) hG hT
    (Causality.isAcausalOn_of_curveNestedOn (harc _ _ hsol₁) (hsub _ _ hsol₁) hmacausal)
    (Causality.splitBy_of_inextensibleThrough h.1.cauchy (hthrough _ _ h.1)) hK hS hm hmext
    hmacausal h.2 h₂.cauchy (fun x hx => hthrough _ _ h₂ x hx.2) (hsub _ _ h₂.solves)
    (hlocal U₂ u₂ h₂) (hstay U₂ u₂ h₂) (hstep U₂ u₂ h₂)

/-! ### Theorem 4.79: the MUGHD -/

/-- **ERS19 Theorem 4.79 from one UGHD** (`ersthm:ThmMUGHD`, unmarked; proof `ghd_02_19.tex:1063`):
the union of the domains of all UGHDs, with the glued solution, is a UGHD containing the domain
of every UGHD. Hypotheses as in `ers_remark_4_78`; `hne` — a UGHD exists (the first paragraph
of the proof: `ers_theorem_4_79`). -/
theorem ers_theorem_4_79_of_exists [T2Space M] (hloc : SolutionLocal sol)
    (hglue : SolutionsGlue sol) (hfollow : CausalityFollows cau)
    (hsub : ∀ U u, sol U u → Causality.CurveNestedOn (cau u) Cm U)
    (harc : ∀ U u, sol U u → (cau u).CausallyArcConnectedOn U)
    (hm : Cm.IsCausal) (hmacausal : Cm.IsAcausal S)
    (hne : ∃ U u, IsUniqueDevelopment sol cau S U u) :
    ∃ U u, IsMaximalUniqueDevelopment sol cau S U u := by
  set 𝒟 : Set (Opens M × (M → β)) := {d | IsUniqueDevelopment sol cau S d.1 d.2} with h𝒟
  have hne' : 𝒟.Nonempty := by
    obtain ⟨U, u, h⟩ := hne
    exact ⟨(U, u), h⟩
  obtain ⟨v, hv⟩ := exists_eqOn_of_pairwise hne' fun d hd d' hd' => hd.2 d'.1 d'.2 hd'.1
  have hdev := ers_remark_4_78 hloc hglue hfollow hsub harc hm hmacausal hne'
    (fun d hd => hd.1) hv
  refine ⟨_, v, ⟨hdev, fun U₂ u₂ h₂ x hx => ?_⟩, fun U' u' h' =>
    le_sSup (mem_image_of_mem Prod.fst (show (U', u') ∈ 𝒟 from h'))⟩
  obtain ⟨_, ⟨d, hd, rfl⟩, hxd⟩ := Opens.mem_sSup.1 hx.1
  rw [hv d hd hxd]
  exact hd.2 U₂ u₂ h₂ ⟨hxd, hx.2⟩

/-- The MUGHD agrees with every development on the overlap, and extends every UGHD. -/
theorem IsMaximalUniqueDevelopment.eqOn {U U' : Opens M} {u u' : M → β}
    (h : IsMaximalUniqueDevelopment sol cau S U u) (h' : IsUniqueDevelopment sol cau S U' u') :
    U' ≤ U ∧ EqOn u u' U' :=
  ⟨h.2 U' u' h', fun _ hx => h.1.2 U' u' h'.1 ⟨h.2 U' u' h' hx, hx⟩⟩

/-- **The MUGHD is unique**: two have the same domain and agree on it. -/
theorem IsMaximalUniqueDevelopment.unique {U U' : Opens M} {u u' : M → β}
    (h : IsMaximalUniqueDevelopment sol cau S U u)
    (h' : IsMaximalUniqueDevelopment sol cau S U' u') : U = U' ∧ EqOn u u' U := by
  refine ⟨le_antisymm (h'.2 U u h.1) (h.2 U' u' h'.1), fun x hx => ?_⟩
  exact h.1.2 U' u' h'.1.1 ⟨hx, h'.2 U u h.1 hx⟩

/-- **ERS19 Theorem 4.79, causal-topological skeleton** (`ersthm:ThmMUGHD`, unmarked;
`ghd_02_19.tex:1055`, proof 1060–1064): under subluminality, with `S` m-acausal and connected,
there exists a UGHD whose domain contains the domain of every UGHD (the MUGHD). The proof's
first paragraph is `hex` (Thm 4.75), `IsDevelopment.exists_isMDevelopment_le` (`hDm`, `hinext`)
and `IsMDevelopment.isUniqueDevelopment` (Cor 4.73, its named hypotheses quantified over the
m-GHDs and the pairs (m-GHD, GHD)); the second is `ers_theorem_4_79_of_exists`. -/
theorem ers_theorem_4_79 [T2Space M] (hloc : SolutionLocal sol) (hglue : SolutionsGlue sol)
    (hfollow : CausalityFollows cau)
    (hsub : ∀ U u, sol U u → Causality.CurveNestedOn (cau u) Cm U)
    (harc : ∀ U u, sol U u → (cau u).CausallyArcConnectedOn U)
    (hinext : ∀ U u, sol U u → Causality.InextensibleNestedOn (cau u) Cm U)
    (hm : Cm.IsCausal) (hmext : Cm.CurvesExtend) (hmacausal : Cm.IsAcausal S)
    (hS : IsPreconnected S)
    (hex : ∃ U u, IsDevelopment sol cau S U u)
    (hDm : ∀ U u, IsDevelopment sol cau S U u →
      ∃ W : Opens M, W ≤ U ∧ S ⊆ W ∧ Cm.IsCauchySurfaceOn W S ∧ sol W u)
    (hthrough : ∀ U u, IsDevelopment sol cau S U u → (cau u).InextensibleThrough U)
    (hG : ∀ U u, IsMDevelopment sol cau Cm S U u → (cau u).GloballyHyperbolicOn U)
    (hT : ∀ U u, IsMDevelopment sol cau Cm S U u → (cau u).TarentinOn U)
    (hK : ∀ U u, IsMDevelopment sol cau Cm S U u → (cau u).CompactSlabs U S)
    (hlocal : ∀ U₁ u₁ U₂ u₂, IsMDevelopment sol cau Cm S U₁ u₁ → IsDevelopment sol cau S U₂ u₂ →
      ∃ V, (cau u₁).IsCommonDevelopment S U₁ U₂ (fun V : Opens M => EqOn u₁ u₂ V) V)
    (hstay : ∀ U₁ u₁ U₂ u₂, IsMDevelopment sol cau Cm S U₁ u₁ → IsDevelopment sol cau S U₂ u₂ →
      ∀ V, (cau u₁).IsCommonDevelopment S U₁ U₂ (fun V : Opens M => EqOn u₁ u₂ V) V →
      (cau u₁).FrontierStaysIn U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hstep : ∀ U₁ u₁ U₂ u₂, IsMDevelopment sol cau Cm S U₁ u₁ → IsDevelopment sol cau S U₂ u₂ →
      ∀ V, (cau u₁).IsCommonDevelopment S U₁ U₂ (fun V : Opens M => EqOn u₁ u₂ V) V →
      (cau u₁).SliceRestart U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M)
        (fun _ => ∃ V', (cau u₁).IsCommonDevelopment S U₁ U₂
          (fun V : Opens M => EqOn u₁ u₂ V) V' ∧ V < V')) :
    ∃ U u, IsMaximalUniqueDevelopment sol cau S U u := by
  obtain ⟨U₀, u₀, h₀⟩ := hex
  obtain ⟨W, -, hW⟩ := h₀.exists_isMDevelopment_le hDm hinext
  exact ers_theorem_4_79_of_exists hloc hglue hfollow hsub harc hm hmacausal
    ⟨W, u₀, hW.isUniqueDevelopment hsub harc hm hmext hmacausal hS hthrough (hG _ _ hW)
      (hT _ _ hW) (hK _ _ hW) (hlocal _ _ · · hW) (hstay _ _ · · hW) (hstep _ _ · · hW)⟩

/-! ### Theorem 4.80: the m-MGHD -/

/-- **ERS19 Theorem 4.80 from global uniqueness among m-GHDs**
(`ersthm:consider_subluminal_quasilinear_wave`, unmarked; proof `ghd_02_19.tex:1072`): the union
of the domains of all m-GHDs, with the glued solution, is an m-GHD extending every m-GHD.
`hagree` — global uniqueness for m-GHDs (Cor 4.73: `ers_theorem_4_80`); `hne` — an m-GHD exists;
the union is a development by `ers_remark_4_78` and m-Cauchy by
`Causality.isCauchySurfaceOn_sSup_of_isCausal`. -/
theorem ers_theorem_4_80_of_exists [T2Space M] (hloc : SolutionLocal sol)
    (hglue : SolutionsGlue sol) (hfollow : CausalityFollows cau)
    (hsub : ∀ U u, sol U u → Causality.CurveNestedOn (cau u) Cm U)
    (harc : ∀ U u, sol U u → (cau u).CausallyArcConnectedOn U)
    (hm : Cm.IsCausal) (hmacausal : Cm.IsAcausal S)
    (hne : ∃ U u, IsMDevelopment sol cau Cm S U u)
    (hagree : ∀ U u U' u', IsMDevelopment sol cau Cm S U u → IsMDevelopment sol cau Cm S U' u' →
      EqOn u u' (U ⊓ U' : Opens M)) :
    ∃ U u, IsMaximalMDevelopment sol cau Cm S U u := by
  set 𝒟 : Set (Opens M × (M → β)) := {d | IsMDevelopment sol cau Cm S d.1 d.2} with h𝒟
  have hne' : 𝒟.Nonempty := by
    obtain ⟨U, u, h⟩ := hne
    exact ⟨(U, u), h⟩
  obtain ⟨v, hv⟩ := exists_eqOn_of_pairwise hne' fun d hd d' hd' => hagree _ _ _ _ hd hd'
  have hdev := ers_remark_4_78 hloc hglue hfollow hsub harc hm hmacausal hne'
    (fun d hd => hd.1) hv
  have hmC : Cm.IsCauchySurfaceOn (sSup (Prod.fst '' 𝒟)) S :=
    Causality.isCauchySurfaceOn_sSup_of_isCausal hm hmacausal (by
      rintro _ ⟨d, hd, rfl⟩
      exact hd.2)
  exact ⟨_, v, ⟨hdev, hmC⟩, fun U' u' h' =>
    ⟨le_sSup (mem_image_of_mem Prod.fst (show (U', u') ∈ 𝒟 from h')), hv (U', u') h'⟩⟩

/-- **The m-MGHD is unique**: two have the same domain and agree on it. -/
theorem IsMaximalMDevelopment.unique {U U' : Opens M} {u u' : M → β}
    (h : IsMaximalMDevelopment sol cau Cm S U u)
    (h' : IsMaximalMDevelopment sol cau Cm S U' u') : U = U' ∧ EqOn u u' U :=
  ⟨le_antisymm (h'.2 U u h.1).1 (h.2 U' u' h'.1).1, fun _ hx => ((h'.2 U u h.1).2 hx).symm⟩

/-- **"In particular the m-MGHD is contained in the MUGHD"** (`ghd_02_19.tex:1075`): when every
m-GHD is a UGHD (Cor 4.73, `IsMDevelopment.isUniqueDevelopment`). -/
theorem IsMaximalMDevelopment.le_of_isMaximalUniqueDevelopment {U U' : Opens M} {u u' : M → β}
    (hmu : ∀ U u, IsMDevelopment sol cau Cm S U u → IsUniqueDevelopment sol cau S U u)
    (h : IsMaximalMDevelopment sol cau Cm S U u)
    (h' : IsMaximalUniqueDevelopment sol cau S U' u') : U ≤ U' ∧ EqOn u u' U :=
  (h'.eqOn (hmu U u h.1)).imp id fun he _ hx => (he hx).symm

/-- **ERS19 Theorem 4.80, causal-topological skeleton**
(`ersthm:consider_subluminal_quasilinear_wave`, unmarked; `ghd_02_19.tex:1066`, proof 1071–1073):
under subluminality, with `S` m-acausal and connected, there exists an m-GHD whose domain
contains that of every m-GHD, which it extends (the m-MGHD; unique by
`IsMaximalMDevelopment.unique`). Hypotheses as in `ers_theorem_4_79`: non-emptiness by `hex`,
`hDm`, `hinext`; global uniqueness for m-GHDs by Cor 4.73 (`IsMDevelopment.isUniqueDevelopment`);
the union by Remark 4.78 (`ers_theorem_4_80_of_exists`). -/
theorem ers_theorem_4_80 [T2Space M] (hloc : SolutionLocal sol) (hglue : SolutionsGlue sol)
    (hfollow : CausalityFollows cau)
    (hsub : ∀ U u, sol U u → Causality.CurveNestedOn (cau u) Cm U)
    (harc : ∀ U u, sol U u → (cau u).CausallyArcConnectedOn U)
    (hinext : ∀ U u, sol U u → Causality.InextensibleNestedOn (cau u) Cm U)
    (hm : Cm.IsCausal) (hmext : Cm.CurvesExtend) (hmacausal : Cm.IsAcausal S)
    (hS : IsPreconnected S)
    (hex : ∃ U u, IsDevelopment sol cau S U u)
    (hDm : ∀ U u, IsDevelopment sol cau S U u →
      ∃ W : Opens M, W ≤ U ∧ S ⊆ W ∧ Cm.IsCauchySurfaceOn W S ∧ sol W u)
    (hthrough : ∀ U u, IsDevelopment sol cau S U u → (cau u).InextensibleThrough U)
    (hG : ∀ U u, IsMDevelopment sol cau Cm S U u → (cau u).GloballyHyperbolicOn U)
    (hT : ∀ U u, IsMDevelopment sol cau Cm S U u → (cau u).TarentinOn U)
    (hK : ∀ U u, IsMDevelopment sol cau Cm S U u → (cau u).CompactSlabs U S)
    (hlocal : ∀ U₁ u₁ U₂ u₂, IsMDevelopment sol cau Cm S U₁ u₁ → IsDevelopment sol cau S U₂ u₂ →
      ∃ V, (cau u₁).IsCommonDevelopment S U₁ U₂ (fun V : Opens M => EqOn u₁ u₂ V) V)
    (hstay : ∀ U₁ u₁ U₂ u₂, IsMDevelopment sol cau Cm S U₁ u₁ → IsDevelopment sol cau S U₂ u₂ →
      ∀ V, (cau u₁).IsCommonDevelopment S U₁ U₂ (fun V : Opens M => EqOn u₁ u₂ V) V →
      (cau u₁).FrontierStaysIn U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hstep : ∀ U₁ u₁ U₂ u₂, IsMDevelopment sol cau Cm S U₁ u₁ → IsDevelopment sol cau S U₂ u₂ →
      ∀ V, (cau u₁).IsCommonDevelopment S U₁ U₂ (fun V : Opens M => EqOn u₁ u₂ V) V →
      (cau u₁).SliceRestart U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M)
        (fun _ => ∃ V', (cau u₁).IsCommonDevelopment S U₁ U₂
          (fun V : Opens M => EqOn u₁ u₂ V) V' ∧ V < V')) :
    ∃ U u, IsMaximalMDevelopment sol cau Cm S U u := by
  have hmu : ∀ U u, IsMDevelopment sol cau Cm S U u → IsUniqueDevelopment sol cau S U u :=
    fun U u h => h.isUniqueDevelopment hsub harc hm hmext hmacausal hS hthrough (hG _ _ h)
      (hT _ _ h) (hK _ _ h) (hlocal _ _ · · h) (hstay _ _ · · h) (hstep _ _ · · h)
  obtain ⟨U₀, u₀, h₀⟩ := hex
  obtain ⟨W, -, hW⟩ := h₀.exists_isMDevelopment_le hDm hinext
  exact ers_theorem_4_80_of_exists hloc hglue hfollow hsub harc hm hmacausal ⟨W, u₀, hW⟩
    fun U u U' u' h h' => (hmu U u h).2 U' u' h'.1

end Developments

/-! ## 3. Witness: the hypotheses are jointly satisfiable (kb/0011) -/

/-- **The degenerate instance**: on the timelike line, `S = {0}`, `Cm` and every `cau u` the
timelike line, the problem whose solutions are `id` on `ℝ` (`sol U u := U = ⊤ ∧ u = id on U`).
Every hypothesis of `ers_theorem_4_79` and `ers_theorem_4_80` holds; the MUGHD and the m-MGHD
exist. One development domain only (`ℝ`), so `hlocal`, `hstay`, `hstep` hold as in
`timelikeLine_ers_theorem_4_64`. -/
theorem timelikeLine_ers_theorem_4_79_4_80 :
    (∃ U u, IsMaximalUniqueDevelopment (fun (U : Opens ℝ) (u : ℝ → ℝ) => U = ⊤ ∧ EqOn u id U)
      (fun _ => timelikeLine) {0} U u) ∧
    (∃ U u, IsMaximalMDevelopment (fun (U : Opens ℝ) (u : ℝ → ℝ) => U = ⊤ ∧ EqOn u id U)
      (fun _ => timelikeLine) timelikeLine {0} U u) := by
  set sol₀ : Opens ℝ → (ℝ → ℝ) → Prop := fun U u => U = ⊤ ∧ EqOn u id U with hsol₀
  have hGH := timelikeLine_globallyHyperbolic
  have hm : timelikeLine.IsCausal := by causal_ladder
  have hloc : SolutionLocal sol₀ := fun U u v huv hu =>
    ⟨hu.1, fun x hx => (huv hx).symm.trans (hu.2 hx)⟩
  have hglue : SolutionsGlue sol₀ := by
    intro 𝒰 v ⟨U₀, hU₀⟩ h
    obtain ⟨hU₀top, hv⟩ := h U₀ hU₀
    have htop : sSup 𝒰 = ⊤ := top_le_iff.1 (by rw [← hU₀top]; exact le_sSup hU₀)
    refine ⟨htop, ?_⟩
    rw [htop]
    rw [hU₀top] at hv
    exact hv
  have hfollow : CausalityFollows (fun _ : ℝ → ℝ => timelikeLine) :=
    fun _ _ _ _ _ _ _ _ => Iff.rfl
  have hsub : ∀ (U : Opens ℝ) (u : ℝ → ℝ), sol₀ U u →
      Causality.CurveNestedOn timelikeLine timelikeLine U :=
    fun U _ _ => (Causality.LeNested.refl _).curveNestedOn U
  have harc : ∀ (U : Opens ℝ) (u : ℝ → ℝ), sol₀ U u → timelikeLine.CausallyArcConnectedOn U :=
    fun _ _ _ V _ => timelikeLine_causallyArcConnected V le_top
  have hinext : ∀ (U : Opens ℝ) (u : ℝ → ℝ), sol₀ U u →
      Causality.InextensibleNestedOn timelikeLine timelikeLine U :=
    fun _ _ _ _ _ h => h
  have hmacausal : timelikeLine.IsAcausal ({0} : Set ℝ) := fun x hx y hy _ =>
    (mem_singleton_iff.1 hx).trans (mem_singleton_iff.1 hy).symm
  have hex : ∃ U u, IsDevelopment sol₀ (fun _ => timelikeLine) {0} U u :=
    ⟨⊤, id, ⟨⟨rfl, fun _ _ => rfl⟩, fun _ _ => trivial, timelikeLine_isCauchySurface_zero⟩⟩
  have hDm : ∀ U u, IsDevelopment sol₀ (fun _ => timelikeLine) {0} U u →
      ∃ W : Opens ℝ, W ≤ U ∧ {0} ⊆ (W : Set ℝ) ∧ timelikeLine.IsCauchySurfaceOn W {0} ∧
        sol₀ W u := by
    rintro U u ⟨⟨rfl, hu⟩, -, -⟩
    exact ⟨⊤, le_rfl, fun _ _ => trivial, timelikeLine_isCauchySurface_zero, rfl, hu⟩
  have hthrough : ∀ U u, IsDevelopment sol₀ (fun _ => timelikeLine) {0} U u →
      timelikeLine.InextensibleThrough U := by
    rintro U u ⟨⟨rfl, -⟩, -, -⟩ x _
    exact ⟨univ, id, timelikeLine_inextensible_id, x, trivial, rfl⟩
  have hG : ∀ U u, IsMDevelopment sol₀ (fun _ => timelikeLine) timelikeLine {0} U u →
      timelikeLine.GloballyHyperbolicOn U := by
    rintro U u ⟨⟨⟨rfl, -⟩, -, -⟩, -⟩
    exact hGH
  have hT : ∀ U u, IsMDevelopment sol₀ (fun _ => timelikeLine) timelikeLine {0} U u →
      timelikeLine.TarentinOn U := by
    rintro U u ⟨⟨⟨rfl, -⟩, -, -⟩, -⟩
    exact Causality.tarentinOn_top.2 timelikeLine_tarentin
  have hK : ∀ U u, IsMDevelopment sol₀ (fun _ => timelikeLine) timelikeLine {0} U u →
      timelikeLine.CompactSlabs U {0} := by
    rintro U u ⟨⟨⟨rfl, -⟩, -, -⟩, -⟩ q
    have h1 : timelikeLine.Jminus ⊤ {q} ∩ timelikeLine.Jplus ⊤ ({0} : Set ℝ) = Icc 0 q := by
      ext z
      simp only [mem_inter_iff, Precausality.mem_Jminus_singleton, Precausality.mem_Jplus,
        mem_singleton_iff, exists_eq_left, timelikeLine_le_top, mem_Icc]
      tauto
    have h2 : timelikeLine.Jplus ⊤ {q} ∩ timelikeLine.Jminus ⊤ ({0} : Set ℝ) = Icc q 0 := by
      ext z
      simp only [mem_inter_iff, Precausality.mem_Jplus_singleton, Precausality.mem_Jminus,
        mem_singleton_iff, exists_eq_left, timelikeLine_le_top, mem_Icc]
    exact ⟨h1 ▸ isCompact_Icc, h2 ▸ isCompact_Icc⟩
  have hcd : ∀ u₁ u₂ : ℝ → ℝ, EqOn u₁ id (⊤ : Opens ℝ) → EqOn u₂ id (⊤ : Opens ℝ) →
      timelikeLine.IsCommonDevelopment ({0} : Set ℝ) ⊤ ⊤
        (fun V : Opens ℝ => EqOn u₁ u₂ V) ⊤ := fun u₁ u₂ h₁ h₂ =>
    ⟨le_inf le_rfl le_rfl, fun _ _ => trivial, fun x hx => (h₁ hx).trans (h₂ hx).symm,
      timelikeLine_isCauchySurface_zero⟩
  have hlocal : ∀ U₁ u₁ U₂ u₂,
      IsMDevelopment sol₀ (fun _ => timelikeLine) timelikeLine {0} U₁ u₁ →
      IsDevelopment sol₀ (fun _ => timelikeLine) {0} U₂ u₂ →
      ∃ V, timelikeLine.IsCommonDevelopment {0} U₁ U₂ (fun V : Opens ℝ => EqOn u₁ u₂ V) V := by
    rintro U₁ u₁ U₂ u₂ ⟨⟨⟨rfl, hu₁⟩, -, -⟩, -⟩ ⟨⟨rfl, hu₂⟩, -, -⟩
    exact ⟨⊤, hcd u₁ u₂ hu₁ hu₂⟩
  have hstay : ∀ U₁ u₁ U₂ u₂,
      IsMDevelopment sol₀ (fun _ => timelikeLine) timelikeLine {0} U₁ u₁ →
      IsDevelopment sol₀ (fun _ => timelikeLine) {0} U₂ u₂ →
      ∀ V, timelikeLine.IsCommonDevelopment {0} U₁ U₂ (fun V : Opens ℝ => EqOn u₁ u₂ V) V →
      timelikeLine.FrontierStaysIn U₁ {0} V ((U₁ ⊓ U₂ : Opens ℝ) : Set ℝ) := by
    rintro U₁ u₁ U₂ u₂ ⟨⟨⟨rfl, -⟩, -, -⟩, -⟩ ⟨⟨rfl, -⟩, -, -⟩ V _ q _
    exact ⟨fun _ _ _ => ⟨trivial, trivial⟩, fun _ _ _ => ⟨trivial, trivial⟩⟩
  have hstep : ∀ U₁ u₁ U₂ u₂,
      IsMDevelopment sol₀ (fun _ => timelikeLine) timelikeLine {0} U₁ u₁ →
      IsDevelopment sol₀ (fun _ => timelikeLine) {0} U₂ u₂ →
      ∀ V, timelikeLine.IsCommonDevelopment {0} U₁ U₂ (fun V : Opens ℝ => EqOn u₁ u₂ V) V →
      timelikeLine.SliceRestart U₁ {0} V ((U₁ ⊓ U₂ : Opens ℝ) : Set ℝ)
        (fun _ => ∃ V', timelikeLine.IsCommonDevelopment {0} U₁ U₂
          (fun V : Opens ℝ => EqOn u₁ u₂ V) V' ∧ V < V') := by
    rintro U₁ u₁ U₂ u₂ ⟨⟨⟨rfl, hu₁⟩, -, -⟩, -⟩ ⟨⟨rfl, hu₂⟩, -, -⟩ V _ p hp _
    refine ⟨⊤, hcd u₁ u₂ hu₁ hu₂, lt_top_iff_ne_top.2 fun hV => ?_⟩
    have : frontier ((V : Opens ℝ) : Set ℝ) = ∅ := by rw [hV, Opens.coe_top, frontier_univ]
    rw [this] at hp
    exact hp.1
  exact ⟨ers_theorem_4_79 hloc hglue hfollow hsub harc hinext hm timelikeLine_curvesExtend
      hmacausal isPreconnected_singleton hex hDm hthrough hG hT hK hlocal hstay hstep,
    ers_theorem_4_80 hloc hglue hfollow hsub harc hinext hm timelikeLine_curvesExtend
      hmacausal isPreconnected_singleton hex hDm hthrough hG hT hK hlocal hstay hstep⟩

end Causal
