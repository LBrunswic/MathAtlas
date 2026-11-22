import Causal.ErsSecondCountable
import Causal.ErsUnions
import Causal.ErsUniqueness
import Causal.NestedCausalities

/-!
# ERS19 §4.2–4.3 on a T1, second countable background, without the curve hypotheses

Programme target `T-abs-ers-4-64-second-countable` (`programme/roadmap.toml`; layer 1: ETT-layer
imports only, `Causal.ErsSecondCountable`, `Causal.ErsUnions`, `Causal.ErsUniqueness`,
`Causal.NestedCausalities`; no model; no metric notion in a statement). Source:
Eperon–Reall–Sbierski, arXiv 1802.03020, `papers/ers-predictability`
(`legacy/labeled/ghd_02_19.tex`). Causal-topological skeletons; **no label is marked** (SCOPE):

* `ersprop:PropLocUniqueness` — `ghd_02_19.tex:836` (proof 840–844):
  `ers_prop_4_63_globallyHyperbolicOn_secondCountable`,
  `IsCommonDevelopment.globallyHyperbolicOn_secondCountable`; the union lemmas
  `eq_of_mem_of_t1_secondCountable`, `IsCauchySurfaceOn.of_subset_of_t1_secondCountable`,
  `isCauchySurfaceOn_sSup_of_secondCountable`,
  `globallyHyperbolicOn_sSup_of_pieces_secondCountable`.
* `ersthm:ThmUnique` — `ghd_02_19.tex:858` (proof 865–912):
  `ers_theorem_4_64_of_isCauchySurfaceOn_secondCountable`, its `_maxCommonDevelopment_` and
  `_of_localUniqueness_` forms.
* `ersrem:RemTime` — `ghd_02_19.tex:914`: `ers_remark_4_67_of_isCauchySurfaceOn_secondCountable`,
  `ers_remark_4_67_globallyHyperbolicOn_secondCountable`, `ers_remark_4_67_future_secondCountable`,
  `ers_remark_4_67_past_secondCountable` and their `_of_isCauchySurfaceOn_` forms;
  `Jplus_inter_subset_of_isCauchySurfaceOn_of_t1_secondCountable` and its past form.
* `erscor:CorDisCon` — `ghd_02_19.tex:921`:
  `ers_corollary_4_68_of_isCauchySurfaceOn_secondCountable`, its `_eqOn_` form.
* `erscor:globally_defined_globally_hyperbolic` — `ghd_02_19.tex:926`:
  `ers_corollary_4_69_secondCountable`, `ers_corollary_4_69_of_isCauchySurface_secondCountable`,
  `isPreconnected_of_isCauchySurfaceOn_of_t1_secondCountable`.
* `erslem:LemConnected` — `ghd_02_19.tex:939` (proof 945–955): `ers_lemma_4_70_secondCountable`,
  `ers_lemma_4_70_isConnected_secondCountable`.
* `erscor:CorSupLum` — `ghd_02_19.tex:959` (proof 965–967): `ers_corollary_4_71_secondCountable`,
  `ers_corollary_4_71_of_isCauchySurfaceOn_secondCountable`.
* `ersthm:ThmNotBlocking` — `ghd_02_19.tex:1100`: a restatement only,
  `ers_theorem_4_82_of_isCauchySurfaceOn_secondCountable`.

Every form stands **beside** its original, which is unchanged (DEC-190; OQ-98 (b) is open, and
this follows the precedent of `Causal.ErsSecondCountable`). There are two kinds:

* `…_secondCountable` (and `…_of_t1_secondCountable`): the original less the binders that are
  **discharged**, with `[SecondCountableTopology M]` added after `[T2Space M]` (or with
  `[T1Space M]` where T2 is not needed). `hext : C.CurvesExtendOn W` is discharged by
  `curvesExtendOn_of_t1_secondCountable` (kb/0142). Each through-hypothesis is discharged by
  `inextensibleThrough_of_t1_secondCountable`. `hsplit` is discharged only where the theorem
  also has `S` Cauchy in the same `W` for the same causality (`splitBy_of_t1_secondCountable`,
  kb/0218). `hacausal` is discharged only where, moreover, `W` is causally arc-connected
  (`IsCauchySurfaceOn.isAcausalOn_of_t1_secondCountable`).
* `…_of_isCauchySurfaceOn_secondCountable`: `hacausal` and `hsplit` are **traded** for
  `hC₁ : C.IsCauchySurfaceOn U₁ S` and `harc : C.CausallyArcConnectedOn U₁` (DEC-162: a GHD
  read "`S` Cauchy"). Such a form is a sibling of the original, not stronger than it.

> A globally hyperbolic development (GHD) of initial data (f0, α0) on a hypersurface S for (4.61)
> consists of a smooth solution u : U → R of (4.61) (U ⊆ R^{d+1} being open) with S ⊆ U and
> u|S = f0, du|S = α0, and such that U is globally hyperbolic with respect to the Lorentzian
> metric g(u, du) with Cauchy hypersurface S. (`ghd_02_19.tex:814`)

> Proposition 4.63 (Local uniqueness). Let u1 : U1 → R and u2 : U2 → R be two globally
> hyperbolic developments for (4.61) of the same initial data prescribed on a hypersurface
> S ⊆ R^{d+1}. Then there exists a common globally hyperbolic development v : V → R.
> […] We now set V = ⋃_{p∈S} DS_p. It is immediate that u1 and u2 agree on this set and that V is
> globally hyperbolic with Cauchy hypersurface S. (`:837, 843`)

> Theorem 4.64. Let u1 : U1 → R and u2 : U2 → R be two globally hyperbolic developments of
> (4.61) arising from the same initial data given on a connected hypersurface S ⊆ R^{d+1}.
> Assume that U1 ∩ U2 is connected. Then u1 and u2 agree on U1 ∩ U2. (`:859`)
> It is immediate that this is well-defined and that v0 : V0 → R is a common globally hyperbolic
> development with the property that any other common globally hyperbolic development is a
> subset of V0. (`:868`) […] Without loss of generality we assume that
> q ∈ J^+_{g(u1, du1)}(S, U1). (`:870`)

> Remark 4.67. Let us remark that the proof in particular shows that under the assumptions of
> Theorem 4.64 the intersection U1 ∩ U2 is the maximal common globally hyperbolic development of
> u1 : U1 → R and u2 : U2 → R. If we fix a choice of normal of the initial data hypersurface S
> and stipulate that it is future directed in U1 as well as in U2, then it follows in particular
> that a point x ∈ U1 ∩ U2, which lies to the future of S in U1, also lies to the future of S in
> U2. Similarly for the past. (`:915`)

> Corollary 4.68. Let u1 : U1 → R and u2 : U2 → R be two globally hyperbolic developments of
> (4.61) arising from the same initial data on a connected hypersurface S ⊆ R^{d+1}. If there
> exists an x ∈ U1 ∩ U2 with u1(x) ≠ u2(x), then U1 ∩ U2 is not connected. (`:922`)

> Corollary 4.69. Let u1 : R^{d+1} → R be a globally defined globally hyperbolic development of
> (4.61) arising from some initial data on a connected hypersurface S ⊆ R^{d+1}. Let u2 : U2 → R
> be another globally hyperbolic development of (4.61) of the same initial data. Then
> u1|U2 = u2. (`:927`)

> Lemma 4.70. Assume that there exists a vector field T on R^{d+1} such that T is timelike with
> respect to g^{μν}(u, du) for all u, du, where g is as in (4.61). Let u1 : U1 → R and
> u2 : U2 → R be two globally hyperbolic developments of (4.61) arising from the same initial
> data on a connected hypersurface S which has the property that every maximal integral curve of
> T intersects S at most once. Then U1 ∩ U2 is connected. (`:940`)
> […] Let γ be the maximal integral curve of T through x. By assumption, γ intersects S at most
> once. (`:950`)

> Corollary 4.71. […] Given two globally hyperbolic developments u1 : U1 → R and u2 : U2 → R,
> we then have u1(x) = u2(x) for all x ∈ U1 ∩ U2. — This follows directly from Lemma 4.70 and
> Theorem 4.64. (`:962, 966`)

> Theorem 4.82. Let u1 : U1 → R be a MGHD of given initial data for a quasilinear wave equation
> of the form (4.61) and assume that (4.83) […] Then u1 : U1 → R is the unique MGHD, i.e., any
> other GHD u : U → R satisfies U ⊆ U1 and thus also u1|U = u. (`:1101, 1106`)

## Hypothesis checklist

This table is against the paper. The rows it does not list are the originals' and are carried
unchanged: the abstract solutions (`agree`, `AgreementGlues`), Theorem 4.64's named inputs
(`hlocal`, `hstay`, `hstep`, `hK`), `hG`, `hT`, `hfollow`, `hn₁`, `hn₂`, `hτ`, `honce`, and 4.82's
`honesided`, `hSclosed`, `hstep`. The checklists of `Causal.ErsUnions`, `Causal.ErsUniqueness`
and `Causal.NestedCausalities` stand for them.

| paper | here |
|---|---|
| background `R^{d+1}`, `U ⊆ R^{d+1}` open (`:812, 814`) | ✓ abstract `M` with `[T2Space M] [SecondCountableTopology M]` (`[T1Space M]` only where T2 is not needed: two of the four union lemmas, `Jplus`/`Jminus_inter_subset_…` and `isPreconnected_of_isCauchySurfaceOn_…`); both hold on `R^{d+1}` and its open sets |
| 4.63: "`V` is globally hyperbolic" (`:843`, not argued) | ✓ proved as in the original, with `CurvesExtendOn U₁` now proved (it was the named `hext`, `curves_extend`); ⚠ strengthened: `CausallyArcConnectedOn U₁` stays named (`causally_arc_connected`, a Lorentzian fact) |
| 4.64, 4.67, 4.68: `u₁` a GHD, used at Step 1 (`:868`: an inextensible curve meets `S` at most once) and `:870` (`q` to the future or past of `S`) | ⚠ read (DEC-162) and ⚠ strengthened: in the `_of_isCauchySurfaceOn_` forms, `C.IsCauchySurfaceOn U₁ S` and `harc` (`causally_arc_connected`, named) replace the original's `hacausal`, `hsplit`; GH, tarentin and `CompactSlabs` stay named, as in the original |
| 4.67 (GH form): "the maximal common globally hyperbolic development" | ✓ `hacausal`, `hsplit`, `hext` all derived from `hS`, `hC`, which the original already takes |
| 4.67: the normal of `S` future directed in `U₁` and `U₂` | ⚠ named as in the original (`hfollow`); the original's `hthrough` (an inextensible curve of `U₁` through each point) is proved |
| 4.69: `U₂` connected (not printed; Cor 4.69 has no proof in ERS) | ✓ proved from `S` preconnected and Cauchy in `U₂` (`isPreconnected_of_isCauchySurfaceOn_of_t1_secondCountable`); was `hthrough₂` |
| 4.69: `u₁` a GHD on `R^{d+1}` | ⚠ read: in `_of_isCauchySurface_`, `C.IsCauchySurface S` and `C.CausallyArcConnected` (`causally_arc_connected` a ladder node at `M`; `IsCauchySurface` is not one) replace `hacausal`, `hsplit` |
| 4.70: "the maximal integral curve of T through x" (`:950`) | ✓ replaced by what the proof uses: an inextensible `Cτ`-causal curve of `M` through `x` (`inextensibleThrough_of_t1_secondCountable Cτ ⊤`). This is not ERS's curve, only its role in the proof. `honce` applies to it as to every `Cτ`-inextensible curve |
| 4.71: Lemma 4.70 and Theorem 4.64 | ✓ composed; `hthroughτ` proved, and `hsplit` derived from the original's `hC₁`; in `_of_isCauchySurfaceOn_`, `harc` replaces `hacausal` |
| 4.82: `u₁` an MGHD, `u` a GHD | ⚠ read: `S` Cauchy in each `dom i` for `cau i` (DEC-162) replaces `hsplit` |

## SCOPE (disclosed)

* **No label is marked.** Every row keeps named inputs that are not proved here:
  `local_uniqueness`, `slice_restart` and `frontier_stays_in` (OQ-57 (b)); GH, tarentin and
  `CompactSlabs` of `U₁`; `causally_arc_connected` of `U₁` in the trade forms; `hfollow` (4.67);
  `inextensible_nested` and `T`'s causality (4.70, 4.71; OQ-41 (b)); 4.82's `OneSidedBoundary`.
  What this module adds is only that `curves_extend` and the through-hypotheses leave every
  row. `SplitBy` and `IsAcausalOn` leave every row through the trade forms.
* **Discharged or traded, per theorem** (kb/0218). Discharged: 4.67's GH form (`hacausal`,
  `hsplit`, `hext`: it already takes `S` Cauchy in `U₁` and `U₁` causally arc-connected) and
  4.71 (`hsplit`, from its `hC₁`). Traded: 4.64 (all three forms), 4.67, 4.68 (both),
  4.67 future and past (`hacausal` only), 4.69 and 4.71 (the `_of_isCauchySurface(On)_` forms),
  and 4.82 (`hsplit` for `S` Cauchy in each `dom i`). The trade needs `harc`: acausality of a
  Cauchy surface needs `≤_{U₁}` realised by causal curves, and a non-local relation leaves causal
  curves and Cauchy surfaces unchanged (kb/0038).
* **Out of scope, unchanged.** `maxDevelopmentIn_eq`, `ers_theorem_4_64_in` and
  `IsLocalDevelopment` (Thm 4.75) keep `hacausal` and `hsplit`. `ers_prop_4_63` keeps
  `hacausal`, its OQ-41 reading. `ers_prop_4_63_of_hasTimeFunction` is subsumed: its
  `HasTimeFunction` served only `CurvesExtendOn U₁`. 4.73 is in `Causal.ErsSecondCountable`.
* **Non-vacuity** (kb/0011). The `…_secondCountable` forms have the originals' hypotheses less
  some binders, so the originals' witnesses still satisfy them (`ℝ` is second countable). Three
  witnesses are added. `timelikeLine_ers_prop_4_63_secondCountable` is the original witness less
  `CurvesExtendOn ⊤`. `timelikeLine_ers_theorem_4_64_of_isCauchySurfaceOn_secondCountable` is a
  proper instance (`U₂ = ]-1, 1[`, `u₂` the clamp) for the trade forms of 4.64 and 4.67 and for
  the GH form of 4.67. `timelikeLine_ers_lemma_4_70_secondCountable` has `U₂ = ]-1, 1[`. They
  use only ETT-layer objects (`Causal.Lines`, `Causal.LinesCurves`, `Causal.ErsUniqueness`). The
  4.68, 4.69, 4.71 and 4.82 forms have no witness of their own.
* **DEC-167** (gluing in `defi:causalite`, a later refactor). Nothing here reads or builds the
  sheaf clause. `AgreementGlues` glues agreement of solutions, not the causality. Every statement
  quantifies over `Causality M`, so a stronger structure leaves them as they are. Only the
  witnesses' `timelikeLine` would need the new field, upstream in `Causal.Lines`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Function

universe u v

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable {C : Causality M} {S : Set M}

/-! ## 1. The union lemmas of Prop 4.63 without `hext` -/

/-- Two points of `S` on a causal curve of `W ≤ B` coincide when `S` is a Cauchy surface of `B`,
in a T1, second countable space: `eq_of_mem_of_curvesExtendOn` without `hext`. -/
theorem eq_of_mem_of_t1_secondCountable [T1Space M] [SecondCountableTopology M] {W B : Opens M}
    (hWB : W ≤ B) (hB : C.IsCauchySurfaceOn B S) {I : Set ℝ} {c : ℝ → M}
    (hc : C.CausalCurveIn W I c) {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) (hsS : c s ∈ S)
    (htS : c t ∈ S) : c s = c t :=
  eq_of_mem_of_curvesExtendOn hWB (curvesExtendOn_of_t1_secondCountable C B) hB hc hs ht hsS htS

/-- A piece `S' ⊆ S` Cauchy in `W ≤ B`, `S` Cauchy in `B`: `S` is Cauchy in `W`, in a T1, second
countable space. `IsCauchySurfaceOn.of_subset_of_curvesExtendOn` without `hext`. -/
theorem IsCauchySurfaceOn.of_subset_of_t1_secondCountable [T1Space M]
    [SecondCountableTopology M] {W B : Opens M} {S' : Set M}
    (hW : C.IsCauchySurfaceOn W S') (hS' : S' ⊆ S) (hWB : W ≤ B)
    (hB : C.IsCauchySurfaceOn B S) : C.IsCauchySurfaceOn W S :=
  hW.of_subset_of_curvesExtendOn hS' hWB (curvesExtendOn_of_t1_secondCountable C B) hB

/-- **ERS Prop 4.63's union, by an ambient Cauchy surface**, on a second countable background:
`isCauchySurfaceOn_sSup_of_curvesExtendOn` without `hext`. -/
theorem isCauchySurfaceOn_sSup_of_secondCountable [T2Space M] [SecondCountableTopology M]
    {B : Opens M} {𝒟 : Set (Opens M)}
    (hanti : ∀ ⦃x y : M⦄, C.le B x y → C.le B y x → x = y)
    (hB : C.IsCauchySurfaceOn B S) (h𝒟B : ∀ D ∈ 𝒟, D ≤ B)
    (h𝒟 : ∀ D ∈ 𝒟, ∃ S' ⊆ S, C.IsCauchySurfaceOn D S') :
    C.IsCauchySurfaceOn (sSup 𝒟) S :=
  isCauchySurfaceOn_sSup_of_curvesExtendOn hanti (curvesExtendOn_of_t1_secondCountable C B) hB
    h𝒟B h𝒟

/-- **The union is globally hyperbolic** (ERS Prop 4.63's last assertion), on a second countable
background: `globallyHyperbolicOn_sSup_of_pieces` without `hext`. -/
theorem globallyHyperbolicOn_sSup_of_pieces_secondCountable [T2Space M]
    [SecondCountableTopology M] {B : Opens M} {𝒟 : Set (Opens M)}
    (hC : C.CausallyArcConnectedOn B) (hG : C.GloballyHyperbolicOn B)
    (hB : C.IsCauchySurfaceOn B S) (h𝒟B : ∀ D ∈ 𝒟, D ≤ B)
    (h𝒟 : ∀ D ∈ 𝒟, ∃ S' ⊆ S, C.IsCauchySurfaceOn D S') (hS : S ⊆ (sSup 𝒟 : Opens M)) :
    C.IsCauchySurfaceOn (sSup 𝒟) S ∧ C.CausallyConvexIn ((sSup 𝒟 : Opens M) : Set M) B ∧
      C.GloballyHyperbolicOn (sSup 𝒟) :=
  globallyHyperbolicOn_sSup_of_pieces hC (curvesExtendOn_of_t1_secondCountable C B) hG hB h𝒟B
    h𝒟 hS

/-! ## 2. Proposition 4.63 and the GH forms without `hext` -/

/-- **A common development inside a GH `U₁` is GH**, on a second countable background:
`IsCommonDevelopment.globallyHyperbolicOn` without `hext`. -/
theorem IsCommonDevelopment.globallyHyperbolicOn_secondCountable [T2Space M]
    [SecondCountableTopology M] {U₁ U₂ V : Opens M}
    {agree : Opens M → Prop} (hV : C.IsCommonDevelopment S U₁ U₂ agree V)
    (hG : C.GloballyHyperbolicOn U₁) (hS : C.IsCauchySurfaceOn U₁ S)
    (hC : C.CausallyArcConnectedOn U₁) :
    C.GloballyHyperbolicOn V ∧ C.CausallyConvexIn (V : Set M) U₁ :=
  hV.globallyHyperbolicOn hG hS hC (curvesExtendOn_of_t1_secondCountable C U₁)

/-- **ERS19 Remark 4.67 with global hyperbolicity, on a second countable background**
(`ersrem:RemTime`, unmarked): `ers_remark_4_67_globallyHyperbolicOn` without `hext`, `hacausal`
and `hsplit`. All three are discharged: the original already takes `hS` (`S` Cauchy in `U₁`) and
`hC` (`U₁` causally arc-connected), from which `hsplit` (`splitBy_of_t1_secondCountable`) and
`hacausal` (`IsCauchySurfaceOn.isAcausalOn_of_t1_secondCountable`) follow. -/
theorem ers_remark_4_67_globallyHyperbolicOn_secondCountable [T2Space M]
    [SecondCountableTopology M] {U₁ U₂ : Opens M}
    {agree : Opens M → Prop} (hglue : AgreementGlues agree)
    (hG : C.GloballyHyperbolicOn U₁) (hT : C.TarentinOn U₁) (hK : C.CompactSlabs U₁ S)
    (hconn : IsPreconnected ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hlocal : ∃ V, C.IsCommonDevelopment S U₁ U₂ agree V)
    (hstay : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.FrontierStaysIn U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hstep : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.SliceRestart U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M)
        (fun _ => ∃ V', C.IsCommonDevelopment S U₁ U₂ agree V' ∧ V < V'))
    (hS : C.IsCauchySurfaceOn U₁ S) (hC : C.CausallyArcConnectedOn U₁) :
    IsGreatest {V | C.IsCommonDevelopment S U₁ U₂ agree V} (U₁ ⊓ U₂) ∧
      C.GloballyHyperbolicOn (U₁ ⊓ U₂) ∧
        C.CausallyConvexIn ((U₁ ⊓ U₂ : Opens M) : Set M) U₁ :=
  ers_remark_4_67_globallyHyperbolicOn hglue hG hT (hS.isAcausalOn_of_t1_secondCountable hC)
    (splitBy_of_t1_secondCountable hS) hK hconn hlocal hstay hstep hS hC
    (curvesExtendOn_of_t1_secondCountable C U₁)

/-- **ERS19 Proposition 4.63, the printed conclusion, on a second countable background**
(`ersprop:PropLocUniqueness`, unmarked): the union of the local developments is a common
development, globally hyperbolic, causally convex in `U₁`. `ers_prop_4_63_globallyHyperbolicOn`
without `hext`. What is left: `u₁` a GHD (`hG`, `hS`), `U₁` causally arc-connected (`hC`, a
Lorentzian fact) and local uniqueness (`hloc`, Sogge). -/
theorem ers_prop_4_63_globallyHyperbolicOn_secondCountable [T2Space M]
    [SecondCountableTopology M] {U₁ U₂ : Opens M}
    {agree : Opens M → Prop} (hglue : AgreementGlues agree) (hG : C.GloballyHyperbolicOn U₁)
    (hS : C.IsCauchySurfaceOn U₁ S) (hC : C.CausallyArcConnectedOn U₁)
    (hloc : C.LocalUniqueness S (U₁ ⊓ U₂) agree) :
    C.IsCommonDevelopment S U₁ U₂ agree (C.localDevelopmentUnion S (U₁ ⊓ U₂) agree) ∧
      C.GloballyHyperbolicOn (C.localDevelopmentUnion S (U₁ ⊓ U₂) agree) ∧
      C.CausallyConvexIn ((C.localDevelopmentUnion S (U₁ ⊓ U₂) agree : Opens M) : Set M) U₁ :=
  ers_prop_4_63_globallyHyperbolicOn hglue hG hS hC (curvesExtendOn_of_t1_secondCountable C U₁) hloc

/-! ## 3. Theorem 4.64, Remark 4.67 and Corollary 4.68 with `S` a Cauchy surface of `U₁` -/

/-- **ERS19 Theorem 4.64, the maximal common development is `U₁ ∩ U₂`, with `u₁` a GHD read as
`S` Cauchy in `U₁`**, on a second countable background (`ersthm:ThmUnique`, unmarked):
`ers_theorem_4_64_maxCommonDevelopment` with `hacausal` and `hsplit` traded for `hC₁` and `harc`
(`U₁` causally arc-connected for `C`). -/
theorem ers_theorem_4_64_maxCommonDevelopment_of_isCauchySurfaceOn_secondCountable [T2Space M]
    [SecondCountableTopology M] {U₁ U₂ : Opens M}
    {agree : Opens M → Prop} (hglue : AgreementGlues agree)
    (hG : C.GloballyHyperbolicOn U₁) (hT : C.TarentinOn U₁) (hC₁ : C.IsCauchySurfaceOn U₁ S)
    (harc : C.CausallyArcConnectedOn U₁) (hK : C.CompactSlabs U₁ S)
    (hconn : IsPreconnected ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hlocal : ∃ V, C.IsCommonDevelopment S U₁ U₂ agree V)
    (hstay : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.FrontierStaysIn U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hstep : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.SliceRestart U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M)
        (fun _ => ∃ V', C.IsCommonDevelopment S U₁ U₂ agree V' ∧ V < V')) :
    C.maxCommonDevelopment S U₁ U₂ agree = U₁ ⊓ U₂ :=
  ers_theorem_4_64_maxCommonDevelopment hglue hG hT (hC₁.isAcausalOn_of_t1_secondCountable harc)
    (splitBy_of_t1_secondCountable hC₁) hK hconn hlocal hstay hstep

/-- **ERS19 Theorem 4.64 with `u₁` a GHD read as `S` Cauchy in `U₁`**, on a second countable
background (`ersthm:ThmUnique`, unmarked): `ers_theorem_4_64` with `hacausal` and `hsplit` traded
for `hC₁ : C.IsCauchySurfaceOn U₁ S` and `harc : C.CausallyArcConnectedOn U₁`. Step 1 uses the
acausality (`IsCauchySurfaceOn.isAcausalOn_of_t1_secondCountable`) and Step 2 the splitting
(`splitBy_of_t1_secondCountable`, ERS's "without loss of generality `q ∈ J⁺(S, U₁)`", `:870`). -/
theorem ers_theorem_4_64_of_isCauchySurfaceOn_secondCountable [T2Space M]
    [SecondCountableTopology M] {U₁ U₂ : Opens M}
    {agree : Opens M → Prop} (hglue : AgreementGlues agree)
    (hG : C.GloballyHyperbolicOn U₁) (hT : C.TarentinOn U₁) (hC₁ : C.IsCauchySurfaceOn U₁ S)
    (harc : C.CausallyArcConnectedOn U₁) (hK : C.CompactSlabs U₁ S)
    (hconn : IsPreconnected ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hlocal : ∃ V, C.IsCommonDevelopment S U₁ U₂ agree V)
    (hstay : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.FrontierStaysIn U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hstep : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.SliceRestart U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M)
        (fun _ => ∃ V', C.IsCommonDevelopment S U₁ U₂ agree V' ∧ V < V')) :
    agree (U₁ ⊓ U₂) :=
  ers_theorem_4_64 hglue hG hT (hC₁.isAcausalOn_of_t1_secondCountable harc)
    (splitBy_of_t1_secondCountable hC₁) hK hconn hlocal hstay hstep

/-- **Theorem 4.64 with Prop 4.63 assembled, with `S` Cauchy in `U₁`**, on a second countable
background (`ersthm:ThmUnique`, unmarked): `ers_theorem_4_64_of_localUniqueness` with `hacausal`
and `hsplit` traded for `hC₁` and `harc`. -/
theorem ers_theorem_4_64_of_localUniqueness_of_isCauchySurfaceOn_secondCountable [T2Space M]
    [SecondCountableTopology M] {U₁ U₂ : Opens M}
    {agree : Opens M → Prop} (hglue : AgreementGlues agree)
    (hG : C.GloballyHyperbolicOn U₁) (hT : C.TarentinOn U₁) (hC₁ : C.IsCauchySurfaceOn U₁ S)
    (harc : C.CausallyArcConnectedOn U₁) (hK : C.CompactSlabs U₁ S)
    (hconn : IsPreconnected ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hloc : C.LocalUniqueness S (U₁ ⊓ U₂) agree)
    (hstay : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.FrontierStaysIn U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hstep : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.SliceRestart U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M)
        (fun _ => ∃ V', C.IsCommonDevelopment S U₁ U₂ agree V' ∧ V < V')) :
    agree (U₁ ⊓ U₂) :=
  ers_theorem_4_64_of_localUniqueness hglue hG hT (hC₁.isAcausalOn_of_t1_secondCountable harc)
    (splitBy_of_t1_secondCountable hC₁) hK hconn hloc hstay hstep

/-- **ERS19 Remark 4.67, first sentence, with `S` Cauchy in `U₁`**, on a second countable
background (`ersrem:RemTime`, unmarked): `ers_remark_4_67` with `hacausal` and `hsplit` traded
for `hC₁` and `harc`. With GH concluded: `ers_remark_4_67_globallyHyperbolicOn_secondCountable`,
which has the same hypotheses. -/
theorem ers_remark_4_67_of_isCauchySurfaceOn_secondCountable [T2Space M]
    [SecondCountableTopology M] {U₁ U₂ : Opens M}
    {agree : Opens M → Prop} (hglue : AgreementGlues agree)
    (hG : C.GloballyHyperbolicOn U₁) (hT : C.TarentinOn U₁) (hC₁ : C.IsCauchySurfaceOn U₁ S)
    (harc : C.CausallyArcConnectedOn U₁) (hK : C.CompactSlabs U₁ S)
    (hconn : IsPreconnected ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hlocal : ∃ V, C.IsCommonDevelopment S U₁ U₂ agree V)
    (hstay : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.FrontierStaysIn U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hstep : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.SliceRestart U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M)
        (fun _ => ∃ V', C.IsCommonDevelopment S U₁ U₂ agree V' ∧ V < V')) :
    IsGreatest {V | C.IsCommonDevelopment S U₁ U₂ agree V} (U₁ ⊓ U₂) :=
  ers_remark_4_67 hglue hG hT (hC₁.isAcausalOn_of_t1_secondCountable harc)
    (splitBy_of_t1_secondCountable hC₁) hK hconn hlocal hstay hstep

/-- **ERS19 Corollary 4.68 with `S` Cauchy in `U₁`**, on a second countable background
(`erscor:CorDisCon`, unmarked): `ers_corollary_4_68` with `hacausal` and `hsplit` traded for
`hC₁` and `harc`. -/
theorem ers_corollary_4_68_of_isCauchySurfaceOn_secondCountable [T2Space M]
    [SecondCountableTopology M] {U₁ U₂ : Opens M}
    {agree : Opens M → Prop} (hglue : AgreementGlues agree)
    (hG : C.GloballyHyperbolicOn U₁) (hT : C.TarentinOn U₁) (hC₁ : C.IsCauchySurfaceOn U₁ S)
    (harc : C.CausallyArcConnectedOn U₁) (hK : C.CompactSlabs U₁ S)
    (hlocal : ∃ V, C.IsCommonDevelopment S U₁ U₂ agree V)
    (hstay : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.FrontierStaysIn U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hstep : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.SliceRestart U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M)
        (fun _ => ∃ V', C.IsCommonDevelopment S U₁ U₂ agree V' ∧ V < V'))
    (hdis : ¬ agree (U₁ ⊓ U₂)) :
    ¬ IsPreconnected ((U₁ ⊓ U₂ : Opens M) : Set M) :=
  ers_corollary_4_68 hglue hG hT (hC₁.isAcausalOn_of_t1_secondCountable harc)
    (splitBy_of_t1_secondCountable hC₁) hK hlocal hstay hstep hdis

/-- **ERS19 Corollary 4.68 for two functions, as printed, with `S` Cauchy in `U₁`**, on a second
countable background (`erscor:CorDisCon`, unmarked): `ers_corollary_4_68_eqOn` with `hacausal`
and `hsplit` traded for `hC₁` and `harc`. -/
theorem ers_corollary_4_68_eqOn_of_isCauchySurfaceOn_secondCountable [T2Space M]
    [SecondCountableTopology M] {β : Type v} {u₁ u₂ : M → β} {U₁ U₂ : Opens M}
    (hG : C.GloballyHyperbolicOn U₁) (hT : C.TarentinOn U₁) (hC₁ : C.IsCauchySurfaceOn U₁ S)
    (harc : C.CausallyArcConnectedOn U₁) (hK : C.CompactSlabs U₁ S)
    (hlocal : ∃ V, C.IsCommonDevelopment S U₁ U₂ (fun V => EqOn u₁ u₂ V) V)
    (hstay : ∀ V, C.IsCommonDevelopment S U₁ U₂ (fun V => EqOn u₁ u₂ V) V →
      C.FrontierStaysIn U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hstep : ∀ V, C.IsCommonDevelopment S U₁ U₂ (fun V => EqOn u₁ u₂ V) V →
      C.SliceRestart U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M)
        (fun _ => ∃ V', C.IsCommonDevelopment S U₁ U₂ (fun V => EqOn u₁ u₂ V) V' ∧ V < V'))
    (hx : ∃ x ∈ U₁ ⊓ U₂, u₁ x ≠ u₂ x) :
    ¬ IsPreconnected ((U₁ ⊓ U₂ : Opens M) : Set M) :=
  ers_corollary_4_68_eqOn hG hT (hC₁.isAcausalOn_of_t1_secondCountable harc)
    (splitBy_of_t1_secondCountable hC₁) hK hlocal hstay hstep hx

/-! ## 4. Remark 4.67's time orientations without `hthrough` -/

/-- **The time orientations agree on a Cauchy development** (the core of Remark 4.67), in a T1,
second countable space: `Jplus_inter_subset_of_isCauchySurfaceOn` without `hthrough`, and with
`[T1Space M]` for `[T2Space M]`. T2 served only to pass `InextensibleThrough` from `U` to `V`
(`InextensibleThrough.of_le`); here `V` splits directly (`splitBy_of_t1_secondCountable`). -/
theorem Jplus_inter_subset_of_isCauchySurfaceOn_of_t1_secondCountable [T1Space M]
    [SecondCountableTopology M] {U V : Opens M} (hVU : V ≤ U)
    (hanti : ∀ ⦃x y : M⦄, C.le U x y → C.le U y x → x = y) (hacausal : C.IsAcausalOn U S)
    (hV : C.IsCauchySurfaceOn V S) :
    C.Jplus U S ∩ V ⊆ C.Jplus V S := by
  rintro x ⟨⟨σ, hσS, hσx⟩, hxV⟩
  rcases splitBy_of_t1_secondCountable hV x hxV with h | h
  · exact h
  · obtain ⟨σ', hσ'S, hxσ'⟩ := h
    have hxσ'U : C.le U x σ' := C.le_mono hVU hxσ'
    have hσσ' : σ = σ' := hacausal σ hσS σ' hσ'S (C.le_trans hσx hxσ'U)
    subst hσσ'
    have hxσ : x = σ := hanti hxσ'U hσx
    subst hxσ
    exact ⟨x, hσS, C.le_refl hxV⟩

/-- The past form of `Jplus_inter_subset_of_isCauchySurfaceOn_of_t1_secondCountable`:
`Jminus_inter_subset_of_isCauchySurfaceOn` without `hthrough`, T1 for T2. -/
theorem Jminus_inter_subset_of_isCauchySurfaceOn_of_t1_secondCountable [T1Space M]
    [SecondCountableTopology M] {U V : Opens M} (hVU : V ≤ U)
    (hanti : ∀ ⦃x y : M⦄, C.le U x y → C.le U y x → x = y) (hacausal : C.IsAcausalOn U S)
    (hV : C.IsCauchySurfaceOn V S) :
    C.Jminus U S ∩ V ⊆ C.Jminus V S := by
  rintro x ⟨⟨σ, hσS, hxσ⟩, hxV⟩
  rcases splitBy_of_t1_secondCountable hV x hxV with h | h
  · obtain ⟨σ', hσ'S, hσ'x⟩ := h
    have hσ'xU : C.le U σ' x := C.le_mono hVU hσ'x
    have hσσ' : σ' = σ := hacausal σ' hσ'S σ hσS (C.le_trans hσ'xU hxσ)
    subst hσσ'
    have hxσ : x = σ' := hanti hxσ hσ'xU
    subst hxσ
    exact ⟨x, hσ'S, C.le_refl hxV⟩
  · exact h

/-- **ERS19 Remark 4.67, second sentence, on a second countable background** (`ersrem:RemTime`,
unmarked): `ers_remark_4_67_future` without `hthrough` (`C.InextensibleThrough U₁`). -/
theorem ers_remark_4_67_future_secondCountable [T2Space M] [SecondCountableTopology M]
    {C₂ : Causality M} {U₁ U₂ : Opens M}
    {agree : Opens M → Prop} (hglue : AgreementGlues agree)
    (hG : C.GloballyHyperbolicOn U₁) (hT : C.TarentinOn U₁) (hacausal : C.IsAcausalOn U₁ S)
    (hC₁ : C.IsCauchySurfaceOn U₁ S)
    (hK : C.CompactSlabs U₁ S)
    (hconn : IsPreconnected ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hlocal : ∃ V, C.IsCommonDevelopment S U₁ U₂ agree V)
    (hstay : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.FrontierStaysIn U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hstep : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.SliceRestart U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M)
        (fun _ => ∃ V', C.IsCommonDevelopment S U₁ U₂ agree V' ∧ V < V'))
    (hfollow : FollowsSolution C C₂ agree (U₁ ⊓ U₂)) :
    ∀ x ∈ U₁ ⊓ U₂, x ∈ C.Jplus U₁ S → x ∈ C₂.Jplus U₂ S :=
  ers_remark_4_67_future hglue hG hT hacausal hC₁ (inextensibleThrough_of_t1_secondCountable C U₁)
    hK hconn hlocal hstay hstep hfollow

/-- **ERS19 Remark 4.67, "Similarly for the past", on a second countable background**
(`ersrem:RemTime`, unmarked): `ers_remark_4_67_past` without `hthrough`. -/
theorem ers_remark_4_67_past_secondCountable [T2Space M] [SecondCountableTopology M]
    {C₂ : Causality M} {U₁ U₂ : Opens M}
    {agree : Opens M → Prop} (hglue : AgreementGlues agree)
    (hG : C.GloballyHyperbolicOn U₁) (hT : C.TarentinOn U₁) (hacausal : C.IsAcausalOn U₁ S)
    (hC₁ : C.IsCauchySurfaceOn U₁ S)
    (hK : C.CompactSlabs U₁ S)
    (hconn : IsPreconnected ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hlocal : ∃ V, C.IsCommonDevelopment S U₁ U₂ agree V)
    (hstay : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.FrontierStaysIn U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hstep : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.SliceRestart U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M)
        (fun _ => ∃ V', C.IsCommonDevelopment S U₁ U₂ agree V' ∧ V < V'))
    (hfollow : FollowsSolution C C₂ agree (U₁ ⊓ U₂)) :
    ∀ x ∈ U₁ ⊓ U₂, x ∈ C.Jminus U₁ S → x ∈ C₂.Jminus U₂ S :=
  ers_remark_4_67_past hglue hG hT hacausal hC₁ (inextensibleThrough_of_t1_secondCountable C U₁)
    hK hconn hlocal hstay hstep hfollow

/-- **ERS19 Remark 4.67, second sentence, with `S` Cauchy in the causally arc-connected `U₁`**
(`ersrem:RemTime`, unmarked): `ers_remark_4_67_future_secondCountable` with `hacausal` traded for
`harc`; the original's `hC₁` is kept, its `hthrough` is not asked. -/
theorem ers_remark_4_67_future_of_isCauchySurfaceOn_secondCountable [T2Space M]
    [SecondCountableTopology M] {C₂ : Causality M} {U₁ U₂ : Opens M}
    {agree : Opens M → Prop} (hglue : AgreementGlues agree)
    (hG : C.GloballyHyperbolicOn U₁) (hT : C.TarentinOn U₁) (hC₁ : C.IsCauchySurfaceOn U₁ S)
    (harc : C.CausallyArcConnectedOn U₁) (hK : C.CompactSlabs U₁ S)
    (hconn : IsPreconnected ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hlocal : ∃ V, C.IsCommonDevelopment S U₁ U₂ agree V)
    (hstay : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.FrontierStaysIn U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hstep : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.SliceRestart U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M)
        (fun _ => ∃ V', C.IsCommonDevelopment S U₁ U₂ agree V' ∧ V < V'))
    (hfollow : FollowsSolution C C₂ agree (U₁ ⊓ U₂)) :
    ∀ x ∈ U₁ ⊓ U₂, x ∈ C.Jplus U₁ S → x ∈ C₂.Jplus U₂ S :=
  ers_remark_4_67_future_secondCountable hglue hG hT (hC₁.isAcausalOn_of_t1_secondCountable harc)
    hC₁ hK hconn hlocal hstay hstep hfollow

/-- The past form of `ers_remark_4_67_future_of_isCauchySurfaceOn_secondCountable`
(`ersrem:RemTime`, unmarked). -/
theorem ers_remark_4_67_past_of_isCauchySurfaceOn_secondCountable [T2Space M]
    [SecondCountableTopology M] {C₂ : Causality M} {U₁ U₂ : Opens M}
    {agree : Opens M → Prop} (hglue : AgreementGlues agree)
    (hG : C.GloballyHyperbolicOn U₁) (hT : C.TarentinOn U₁) (hC₁ : C.IsCauchySurfaceOn U₁ S)
    (harc : C.CausallyArcConnectedOn U₁) (hK : C.CompactSlabs U₁ S)
    (hconn : IsPreconnected ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hlocal : ∃ V, C.IsCommonDevelopment S U₁ U₂ agree V)
    (hstay : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.FrontierStaysIn U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hstep : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.SliceRestart U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M)
        (fun _ => ∃ V', C.IsCommonDevelopment S U₁ U₂ agree V' ∧ V < V'))
    (hfollow : FollowsSolution C C₂ agree (U₁ ⊓ U₂)) :
    ∀ x ∈ U₁ ⊓ U₂, x ∈ C.Jminus U₁ S → x ∈ C₂.Jminus U₂ S :=
  ers_remark_4_67_past_secondCountable hglue hG hT (hC₁.isAcausalOn_of_t1_secondCountable harc)
    hC₁ hK hconn hlocal hstay hstep hfollow

/-! ## 5. Corollary 4.69 without `hthrough₂` -/

/-- **A development is preconnected when `S` is and is a Cauchy surface of it**, for any
causality, in a T1, second countable space: `isPreconnected_of_inextensibleThrough` without
`hthrough`. -/
theorem isPreconnected_of_isCauchySurfaceOn_of_t1_secondCountable [T1Space M]
    [SecondCountableTopology M] {W : Opens M} {D : Causality M} (hS : IsPreconnected S)
    (hSW : S ⊆ W) (hC : D.IsCauchySurfaceOn W S) :
    IsPreconnected (W : Set M) :=
  isPreconnected_of_inextensibleThrough hS hSW hC (inextensibleThrough_of_t1_secondCountable D W)

/-- **ERS19 Corollary 4.69 on a second countable background**
(`erscor:globally_defined_globally_hyperbolic`, unmarked): `ers_corollary_4_69` without
`hthrough₂`; `U₂` is preconnected because `S` is and is Cauchy in `U₂` for `C₂`
(`isPreconnected_of_isCauchySurfaceOn_of_t1_secondCountable`). -/
theorem ers_corollary_4_69_secondCountable [T2Space M] [SecondCountableTopology M]
    {C₂ : Causality M} {U₂ : Opens M}
    {agree : Opens M → Prop} (hglue : AgreementGlues agree)
    (hG : C.GloballyHyperbolic) (hT : C.Tarentin) (hacausal : C.IsAcausal S)
    (hsplit : C.SplitBy ⊤ S) (hK : C.CompactSlabs ⊤ S)
    (hS : IsPreconnected S) (hC₂ : C₂.IsCauchySurfaceOn U₂ S)
    (hlocal : ∃ V, C.IsCommonDevelopment S ⊤ U₂ agree V)
    (hstay : ∀ V, C.IsCommonDevelopment S ⊤ U₂ agree V → C.FrontierStaysIn ⊤ S V U₂)
    (hstep : ∀ V, C.IsCommonDevelopment S ⊤ U₂ agree V →
      C.SliceRestart ⊤ S V U₂ (fun _ => ∃ V', C.IsCommonDevelopment S ⊤ U₂ agree V' ∧ V < V')) :
    agree U₂ :=
  ers_corollary_4_69 hglue hG hT hacausal hsplit hK hS hC₂
    (inextensibleThrough_of_t1_secondCountable C₂ U₂) hlocal hstay hstep

/-- **ERS19 Corollary 4.69 with `u₁` a GHD on `M` read as `S` a Cauchy surface of `M`**
(`erscor:globally_defined_globally_hyperbolic`, unmarked): `ers_corollary_4_69_secondCountable`
with `hacausal` and `hsplit` traded for `hC₁ : C.IsCauchySurface S` and
`harc : C.CausallyArcConnected` (ladder nodes at `M`). -/
theorem ers_corollary_4_69_of_isCauchySurface_secondCountable [T2Space M]
    [SecondCountableTopology M] {C₂ : Causality M} {U₂ : Opens M}
    {agree : Opens M → Prop} (hglue : AgreementGlues agree)
    (hG : C.GloballyHyperbolic) (hT : C.Tarentin) (hC₁ : C.IsCauchySurface S)
    (harc : C.CausallyArcConnected) (hK : C.CompactSlabs ⊤ S)
    (hS : IsPreconnected S) (hC₂ : C₂.IsCauchySurfaceOn U₂ S)
    (hlocal : ∃ V, C.IsCommonDevelopment S ⊤ U₂ agree V)
    (hstay : ∀ V, C.IsCommonDevelopment S ⊤ U₂ agree V → C.FrontierStaysIn ⊤ S V U₂)
    (hstep : ∀ V, C.IsCommonDevelopment S ⊤ U₂ agree V →
      C.SliceRestart ⊤ S V U₂ (fun _ => ∃ V', C.IsCommonDevelopment S ⊤ U₂ agree V' ∧ V < V')) :
    agree U₂ :=
  ers_corollary_4_69_secondCountable hglue hG hT (hC₁.isAcausal_of_t1_secondCountable harc)
    (splitBy_of_t1_secondCountable hC₁) hK hS hC₂ hlocal hstay hstep

/-! ## 6. Lemma 4.70 and Corollary 4.71 without `hthrough` -/

/-- **ERS19 Lemma 4.70 on a second countable background** (`erslem:LemConnected`, unmarked):
`ers_lemma_4_70` without `hthrough` (ERS's maximal integral curve of `T` through each point of
`U₁ ∩ U₂`). An inextensible `Cτ`-causal curve of `M` runs through every point
(`inextensibleThrough_of_t1_secondCountable Cτ ⊤`), and `honce` applies to it as to every
`Cτ`-inextensible curve. -/
theorem ers_lemma_4_70_secondCountable [T2Space M] [SecondCountableTopology M]
    {Cτ C₁ C₂ : Causality M} {U₁ U₂ : Opens M}
    (hS : IsPreconnected S) (hS₁ : S ⊆ U₁) (hS₂ : S ⊆ U₂)
    (hC₁ : C₁.IsCauchySurfaceOn U₁ S) (hC₂ : C₂.IsCauchySurfaceOn U₂ S) (hτ : Cτ.IsCausal)
    (honce : ∀ (I : Set ℝ) (γ : ℝ → M), Cτ.Inextensible ⊤ I γ →
      ∀ y ∈ γ '' I ∩ S, ∀ z ∈ γ '' I ∩ S, y = z)
    (hn₁ : InextensibleNestedOn Cτ C₁ U₁) (hn₂ : InextensibleNestedOn Cτ C₂ U₂) :
    IsPreconnected ((U₁ ⊓ U₂ : Opens M) : Set M) :=
  ers_lemma_4_70 hS hS₁ hS₂ hC₁ hC₂ hτ
    (fun x _ => inextensibleThrough_of_t1_secondCountable Cτ ⊤ x trivial) honce hn₁ hn₂

/-- ERS19 Lemma 4.70 as printed ("connected"), on a second countable background:
`ers_lemma_4_70_isConnected` without `hthrough`. -/
theorem ers_lemma_4_70_isConnected_secondCountable [T2Space M] [SecondCountableTopology M]
    {Cτ C₁ C₂ : Causality M} {U₁ U₂ : Opens M}
    (hS : IsConnected S) (hS₁ : S ⊆ U₁) (hS₂ : S ⊆ U₂)
    (hC₁ : C₁.IsCauchySurfaceOn U₁ S) (hC₂ : C₂.IsCauchySurfaceOn U₂ S) (hτ : Cτ.IsCausal)
    (honce : ∀ (I : Set ℝ) (γ : ℝ → M), Cτ.Inextensible ⊤ I γ →
      ∀ y ∈ γ '' I ∩ S, ∀ z ∈ γ '' I ∩ S, y = z)
    (hn₁ : InextensibleNestedOn Cτ C₁ U₁) (hn₂ : InextensibleNestedOn Cτ C₂ U₂) :
    IsConnected ((U₁ ⊓ U₂ : Opens M) : Set M) :=
  ers_lemma_4_70_isConnected hS hS₁ hS₂ hC₁ hC₂ hτ
    (fun x _ => inextensibleThrough_of_t1_secondCountable Cτ ⊤ x trivial) honce hn₁ hn₂

/-- **ERS19 Corollary 4.71 on a second countable background** (`erscor:CorSupLum`, unmarked):
`ers_corollary_4_71` without `hthroughτ` and `hsplit`. Both are discharged: `hthroughτ` as in
`ers_lemma_4_70_secondCountable`, and `hsplit` from the original's `hC₁` (`S` Cauchy in `U₁` for
`C`, `splitBy_of_t1_secondCountable`). -/
theorem ers_corollary_4_71_secondCountable [T2Space M] [SecondCountableTopology M]
    {Cτ C₂ : Causality M} {U₁ U₂ : Opens M}
    {agree : Opens M → Prop} (hglue : AgreementGlues agree)
    (hG : C.GloballyHyperbolicOn U₁) (hT : C.TarentinOn U₁) (hacausal : C.IsAcausalOn U₁ S)
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
    agree (U₁ ⊓ U₂) :=
  ers_corollary_4_71 hglue hG hT hacausal (splitBy_of_t1_secondCountable hC₁) hK hS hC₁ hC₂ hτ
    (fun x _ => inextensibleThrough_of_t1_secondCountable Cτ ⊤ x trivial) honce hn₁ hn₂ hlocal
    hstay hstep

/-- **ERS19 Corollary 4.71 with `S` Cauchy in the causally arc-connected `U₁`**
(`erscor:CorSupLum`, unmarked): `ers_corollary_4_71_secondCountable` with `hacausal` traded for
`harc : C.CausallyArcConnectedOn U₁`. -/
theorem ers_corollary_4_71_of_isCauchySurfaceOn_secondCountable [T2Space M]
    [SecondCountableTopology M] {Cτ C₂ : Causality M} {U₁ U₂ : Opens M}
    {agree : Opens M → Prop} (hglue : AgreementGlues agree)
    (hG : C.GloballyHyperbolicOn U₁) (hT : C.TarentinOn U₁) (harc : C.CausallyArcConnectedOn U₁)
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
    agree (U₁ ⊓ U₂) :=
  ers_corollary_4_71_secondCountable hglue hG hT (hC₁.isAcausalOn_of_t1_secondCountable harc) hK
    hS hC₁ hC₂ hτ honce hn₁ hn₂ hlocal hstay hstep

/-! ## 7. Theorem 4.82 with `S` a Cauchy surface of each development -/

/-- **ERS19 Theorem 4.82 with `S` a Cauchy surface of each development**, on a second countable
background (`ersthm:ThmNotBlocking`, unmarked; a restatement):
`ers_theorem_4_82_of_globallyHyperbolicOn` with `hsplit` traded for `hcauchy` (`S` Cauchy in
`dom i` for `cau i`, DEC-162), from which `splitBy_of_t1_secondCountable` derives it. -/
theorem ers_theorem_4_82_of_isCauchySurfaceOn_secondCountable [T2Space M]
    [SecondCountableTopology M] [LocallyConnectedSpace M] {ι : Type*}
    (dom : ι → Opens M) (cau : ι → Causality M) {s₀ : M} (hs₀ : s₀ ∈ S) (i₁ : ι)
    (hSU : ∀ i, S ⊆ dom i)
    (hmax : ∀ i, dom i₁ ≤ dom i → dom i = dom i₁)
    (hconn : ∀ i, IsPreconnected (dom i : Set M))
    (hG : ∀ i, (cau i).GloballyHyperbolicOn (dom i)) (hT : ∀ i, (cau i).TarentinOn (dom i))
    (hcauchy : ∀ i, (cau i).IsCauchySurfaceOn (dom i) S)
    (hK : ∀ i, (cau i).CompactSlabs (dom i) S)
    (hSclosed : ∀ i, closure S ∩ dom i ⊆ S)
    (honesided : OneSidedBoundary (dom i₁) (closure S))
    (hstep : ∀ i, (cau i).SliceRestart (dom i) S
      (connectedComponentIn ((dom i₁ : Set M) ∩ dom i) s₀) (dom i)
      (fun p => (∃ V ∈ 𝓝 p, V ⊆ dom i ∧
        V ∩ dom i₁ ⊆ connectedComponentIn ((dom i₁ : Set M) ∩ dom i) s₀) →
        ∃ j, dom i₁ < dom j)) :
    ∀ i, dom i ≤ dom i₁ :=
  ers_theorem_4_82_of_globallyHyperbolicOn dom cau hs₀ i₁ hSU hmax hconn hG hT
    (fun i => splitBy_of_t1_secondCountable (hcauchy i)) hK hSclosed honesided hstep

end Causality

/-! ## 8. Witnesses (kb/0011) -/

open Causality in
/-- **A proper instance of `ers_prop_4_63_globallyHyperbolicOn_secondCountable`**: on the
timelike line, `U₁ = ℝ`, `U₂ = ]-1, 1[`, `S = {0}`, `u₁ = id`, `u₂` the clamp to `[-1, 1]`;
local uniqueness by `DS_0 = ]-1/2, 1/2[`. The original witness `timelikeLine_ers_prop_4_63` less
its `CurvesExtendOn ⊤` argument. -/
theorem timelikeLine_ers_prop_4_63_secondCountable :
    ∃ V : Opens ℝ, timelikeLine.IsCommonDevelopment {0} ⊤ ⟨Ioo (-1) 1, isOpen_Ioo⟩
        (fun V => EqOn (id : ℝ → ℝ) (fun x => max (-1) (min x 1)) V) V ∧
      timelikeLine.GloballyHyperbolicOn V ∧ timelikeLine.CausallyConvexIn (V : Set ℝ) ⊤ := by
  have hloc : timelikeLine.LocalUniqueness ({0} : Set ℝ) (⊤ ⊓ ⟨Ioo (-1) 1, isOpen_Ioo⟩)
      (fun V => EqOn (id : ℝ → ℝ) (fun x => max (-1) (min x 1)) V) := by
    rintro p rfl
    refine ⟨⟨Ioo (-(1 / 2)) (1 / 2), isOpen_Ioo⟩, show (0 : ℝ) ∈ Ioo (-(1 / 2)) (1 / 2) by
      constructor <;> norm_num, fun x hx => Opens.mem_inf.2 ⟨trivial,
      show x ∈ Ioo (-1 : ℝ) 1 from ⟨by linarith [hx.1], by linarith [hx.2]⟩⟩,
      fun x hx => ?_, {0}, subset_rfl, timelikeLine_isCauchySurfaceOn_Ioo one_half_pos rfl⟩
    obtain ⟨h1, h2⟩ := hx
    simp [min_eq_left (by linarith : x ≤ 1), max_eq_right (by linarith : (-1 : ℝ) ≤ x)]
  obtain ⟨h1, h2, h3⟩ := ers_prop_4_63_globallyHyperbolicOn_secondCountable
    (agreementGlues_eqOn _ _) timelikeLine_globallyHyperbolic timelikeLine_isCauchySurface_zero
    timelikeLine_causallyArcConnected hloc
  exact ⟨_, h1, h2, h3⟩

open Causality in
/-- **A proper instance of the Cauchy-surface forms of Theorem 4.64 and Remark 4.67**: on the
timelike line, `U₁ = ℝ`, `U₂ = ]-1, 1[`, `S = {0}`, `u₁ = id`, `u₂` the clamp to `[-1, 1]` (they
agree on an open set iff it lies in `[-1, 1]`), `C₂ = C`. The data of
`timelikeLine_ers_theorem_4_64_Ioo`, with `hacausal`, `hsplit` replaced by `{0}` Cauchy in `ℝ`
and the line causally arc-connected. One set of hypotheses serves
`ers_theorem_4_64_of_isCauchySurfaceOn_secondCountable`,
`ers_remark_4_67_globallyHyperbolicOn_secondCountable` and the two time-orientation forms
(`hfollow` by `FollowsSolution.refl`): `U₁ ∩ U₂` is where the solutions agree, the greatest common
development, globally hyperbolic and causally convex in `ℝ`, and its points to the future (past)
of `0` in `ℝ` are to its future (past) in `]-1, 1[`. -/
theorem timelikeLine_ers_theorem_4_64_of_isCauchySurfaceOn_secondCountable :
    EqOn (id : ℝ → ℝ) (fun x => max (-1) (min x 1))
        (((⊤ : Opens ℝ) ⊓ ⟨Ioo (-1) 1, isOpen_Ioo⟩ : Opens ℝ) : Set ℝ) ∧
      (IsGreatest {V | timelikeLine.IsCommonDevelopment ({0} : Set ℝ) ⊤ ⟨Ioo (-1) 1, isOpen_Ioo⟩
          (fun V : Opens ℝ => EqOn (id : ℝ → ℝ) (fun x => max (-1) (min x 1)) V) V}
          ((⊤ : Opens ℝ) ⊓ ⟨Ioo (-1) 1, isOpen_Ioo⟩) ∧
        timelikeLine.GloballyHyperbolicOn ((⊤ : Opens ℝ) ⊓ ⟨Ioo (-1) 1, isOpen_Ioo⟩) ∧
        timelikeLine.CausallyConvexIn
          (((⊤ : Opens ℝ) ⊓ ⟨Ioo (-1) 1, isOpen_Ioo⟩ : Opens ℝ) : Set ℝ) ⊤) ∧
      (∀ x ∈ ((⊤ : Opens ℝ) ⊓ ⟨Ioo (-1) 1, isOpen_Ioo⟩ : Opens ℝ),
        x ∈ timelikeLine.Jplus ⊤ ({0} : Set ℝ) →
          x ∈ timelikeLine.Jplus ⟨Ioo (-1) 1, isOpen_Ioo⟩ ({0} : Set ℝ)) ∧
      (∀ x ∈ ((⊤ : Opens ℝ) ⊓ ⟨Ioo (-1) 1, isOpen_Ioo⟩ : Opens ℝ),
        x ∈ timelikeLine.Jminus ⊤ ({0} : Set ℝ) →
          x ∈ timelikeLine.Jminus ⟨Ioo (-1) 1, isOpen_Ioo⟩ ({0} : Set ℝ)) := by
  set U₂ : Opens ℝ := ⟨Ioo (-1) 1, isOpen_Ioo⟩ with hU₂
  set agree : Opens ℝ → Prop := fun V => EqOn (id : ℝ → ℝ) (fun x => max (-1) (min x 1)) V
  have hinter : (((⊤ : Opens ℝ) ⊓ U₂ : Opens ℝ) : Set ℝ) = Ioo (-1) 1 := by
    rw [Opens.coe_inf, Opens.coe_top, univ_inter]; rfl
  have hagree : ∀ V : Opens ℝ, (V : Set ℝ) ⊆ Ioo (-1) 1 → agree V := fun V hV x hx => by
    obtain ⟨h1, h2⟩ := hV hx
    simp [min_eq_left h2.le, max_eq_right h1.le]
  have hcdI : ∀ (r : ℝ), 0 < r → r ≤ 1 → ∀ V : Opens ℝ, (V : Set ℝ) = Ioo (-r) r →
      timelikeLine.IsCommonDevelopment ({0} : Set ℝ) ⊤ U₂ agree V := by
    intro r hr hr1 V hV
    have hsub : (V : Set ℝ) ⊆ Ioo (-1) 1 := by
      rw [hV]; exact Ioo_subset_Ioo (by linarith) hr1
    refine ⟨fun x hx => ?_, ?_, hagree V hsub, timelikeLine_isCauchySurfaceOn_Ioo hr hV⟩
    · rw [← SetLike.mem_coe, hinter]; exact hsub hx
    · rw [singleton_subset_iff, hV]; exact ⟨by linarith, hr⟩
  have hcd : timelikeLine.IsCommonDevelopment ({0} : Set ℝ) ⊤ U₂ agree (⊤ ⊓ U₂) :=
    hcdI 1 one_pos le_rfl _ hinter
  have hglue : AgreementGlues agree := agreementGlues_eqOn _ _
  have hG : timelikeLine.GloballyHyperbolicOn ⊤ := timelikeLine_globallyHyperbolic
  have hT : timelikeLine.TarentinOn ⊤ := tarentinOn_top.2 timelikeLine_tarentin
  have hC₁ : timelikeLine.IsCauchySurfaceOn ⊤ ({0} : Set ℝ) := timelikeLine_isCauchySurface_zero
  have harc : timelikeLine.CausallyArcConnectedOn ⊤ := timelikeLine_causallyArcConnected
  have hK : timelikeLine.CompactSlabs ⊤ ({0} : Set ℝ) := by
    intro q
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
  have hconn : IsPreconnected (((⊤ : Opens ℝ) ⊓ U₂ : Opens ℝ) : Set ℝ) := by
    rw [hinter]; exact isPreconnected_Ioo
  have hlocal : ∃ V, timelikeLine.IsCommonDevelopment ({0} : Set ℝ) ⊤ U₂ agree V :=
    ⟨⟨Ioo (-(1 / 2)) (1 / 2), isOpen_Ioo⟩, hcdI (1 / 2) one_half_pos one_half_lt_one.le _ rfl⟩
  -- `FrontierStaysIn`: `J⁻(q) ∩ J⁺(0) = [0, q] ⊆ ]-1, 1[`, and the past form
  have hstay : ∀ V, timelikeLine.IsCommonDevelopment ({0} : Set ℝ) ⊤ U₂ agree V →
      timelikeLine.FrontierStaysIn ⊤ {0} V (((⊤ : Opens ℝ) ⊓ U₂ : Opens ℝ) : Set ℝ) := by
    intro V _ q hq
    rw [hinter] at hq ⊢
    refine ⟨fun _ z hz => ?_, fun _ z hz => ?_⟩
    · obtain ⟨⟨hzq, ⟨_, rfl, h0z⟩⟩, -⟩ := hz
      rw [Precausality.mem_Jminus_singleton, timelikeLine_le_top] at hzq
      rw [timelikeLine_le_top] at h0z
      exact ⟨by linarith, hzq.trans_lt hq.2.2⟩
    · obtain ⟨⟨hqz, ⟨_, rfl, hz0⟩⟩, -⟩ := hz
      rw [Precausality.mem_Jplus_singleton, timelikeLine_le_top] at hqz
      rw [timelikeLine_le_top] at hz0
      exact ⟨hq.2.1.trans_le hqz, by linarith⟩
  -- `SliceRestart`: `V' = ]-1, 1[`; the frontier point `p ∈ ]-1, 1[` is not in `V`
  have hstep : ∀ V, timelikeLine.IsCommonDevelopment ({0} : Set ℝ) ⊤ U₂ agree V →
      timelikeLine.SliceRestart ⊤ {0} V (((⊤ : Opens ℝ) ⊓ U₂ : Opens ℝ) : Set ℝ)
        (fun _ => ∃ V', timelikeLine.IsCommonDevelopment ({0} : Set ℝ) ⊤ U₂ agree V' ∧
          V < V') := by
    intro V hV p hp _
    refine ⟨⊤ ⊓ U₂, hcd, lt_of_le_of_ne hV.le fun hVeq => ?_⟩
    have hpV : p ∈ (V : Set ℝ) := by rw [hVeq]; exact hp.2
    have := hp.1
    rw [V.isOpen.frontier_eq] at this
    exact this.2 hpV
  exact ⟨ers_theorem_4_64_of_isCauchySurfaceOn_secondCountable hglue hG hT hC₁ harc hK hconn
      hlocal hstay hstep,
    ers_remark_4_67_globallyHyperbolicOn_secondCountable hglue hG hT hK hconn hlocal hstay hstep
      hC₁ harc,
    ers_remark_4_67_future_of_isCauchySurfaceOn_secondCountable hglue hG hT hC₁ harc hK hconn
      hlocal hstay hstep (FollowsSolution.refl _ _ _),
    ers_remark_4_67_past_of_isCauchySurfaceOn_secondCountable hglue hG hT hC₁ harc hK hconn
      hlocal hstay hstep (FollowsSolution.refl _ _ _)⟩

/-- **A proper instance of `ers_lemma_4_70_secondCountable`**: on the timelike line, `Cτ = C₁ =
C₂` the line, `S = {0}`, `U₁ = ℝ`, `U₂ = ]-1, 1[`. The original's `hthrough` (an inextensible
`Cτ`-curve of `ℝ` through every point of `U₁ ∩ U₂`) is not asked. -/
theorem timelikeLine_ers_lemma_4_70_secondCountable {U₂ : Opens ℝ}
    (hU₂ : (U₂ : Set ℝ) = Ioo (-1) 1) :
    IsPreconnected (((⊤ : Opens ℝ) ⊓ U₂ : Opens ℝ) : Set ℝ) := by
  have h0 : (0 : ℝ) ∈ (U₂ : Set ℝ) := by rw [hU₂]; norm_num
  exact Causality.ers_lemma_4_70_secondCountable (Cτ := timelikeLine) (C₁ := timelikeLine)
    (C₂ := timelikeLine) (S := {0}) isPreconnected_singleton (fun _ _ => trivial)
    (singleton_subset_iff.2 h0) timelikeLine_isCauchySurface_zero
    (timelikeLine_isCauchySurfaceOn_Ioo one_pos hU₂) timelikeLine_isCausal
    (fun _ _ _ _ hy _ hz => (mem_singleton_iff.1 hy.2).trans (mem_singleton_iff.1 hz.2).symm)
    (fun _ _ h => h) (fun _ _ h => h)

end Causal
