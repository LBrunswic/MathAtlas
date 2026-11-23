import Causal.Ers464SecondCountable
import Causal.ErsSecondCountable
import Causal.ErsUnions

/-!
# ERS19 Theorem 4.75 with "GHD" read "`S` Cauchy", on a T2, second countable background

Programme target `T-abs-ers-4-75-cauchy-form` (`programme/roadmap.toml`; layer 1: ETT-layer
imports only, `Causal.Ers464SecondCountable`, `Causal.ErsSecondCountable`, `Causal.ErsUnions`;
no model; no metric notion in a statement). Source: Eperon–Reall–Sbierski, arXiv 1802.03020,
`papers/ers-predictability` (`legacy/labeled/ghd_02_19.tex`). Causal-topological skeletons;
**no label is marked** (SCOPE):

* `ersthm:ThmEx` — `ghd_02_19.tex:1001` (proof 1011–1022): `ers_theorem_4_75_secondCountable`,
  `ers_theorem_4_75_eqOn_secondCountable`, through
  `ers_theorem_4_64_in_of_isCauchySurfaceOn_secondCountable`,
  `maxDevelopmentIn_eq_of_isCauchySurfaceOn_secondCountable` and
  `isDevelopmentIn_maxDevelopmentIn_of_isCauchySurfaceOn_secondCountable`; the patches are
  `IsCauchyLocalDevelopment` (`IsLocalDevelopment` less `acausal` and `split`), supplied through
  `IsCauchySurfaceOn.of_inter_eq` (ERS's `S_p` to `S`, no acausality).
* `ersprop:PropLocUniqueness` — `ghd_02_19.tex:836` (proof 840–844):
  `ers_prop_4_63_of_isCauchySurfaceOn_secondCountable`, through
  `isDevelopmentIn_localDevelopmentUnion_of_isCauchySurfaceOn_secondCountable`.

Every form stands **beside** its original in `Causal.ErsUnions`, which is unchanged (OQ-98 (b)
open; the precedent of `Causal.Ers464SecondCountable`). Two kinds (kb/0226):

* `…_of_isCauchySurfaceOn_secondCountable` (4.64 in a region, its Step 1, Prop 4.63): the
  original's `hacausal : C.IsAcausalOn W S` and `hsplit : C.SplitBy W S` are **traded** for
  `hcauchy : C.IsCauchySurfaceOn W S` (DEC-162: a GHD read "`S` Cauchy"). A sibling of the
  original, not a strengthening: the original needs neither `hcauchy` nor second countability.
  **No `CausallyArcConnectedOn W` is asked** (SCOPE).
* `…_secondCountable` (4.75 and its claim): the original with `IsLocalDevelopment` replaced by
  `IsCauchyLocalDevelopment`, which `IsLocalDevelopment` implies with no hypothesis
  (`IsLocalDevelopment.isCauchyLocalDevelopment`). On a second countable `M` these forms are
  therefore **at least as strong** as the originals, not siblings: each original (with
  `[SecondCountableTopology M]`) is the new form applied to `fun i => (hdev i).isCauchyLocal…`.
  `IsLocalDevelopment` already carries `cauchy` for the same patch and the same causality, and
  `acausal`, `split` are not needed (SCOPE). Strictness is not witnessed here.

> Theorem 4.75 (Local existence). Given initial data for a quasilinear wave equation (4.61),
> there exists a globally hyperbolic development. (`ghd_02_19.tex:1002`)
> […] there exists a globally hyperbolic development u_p : DS_p → R for (4.61) of the initial
> data on S_p, where DS_p ⊆ W_p. […] We now claim that for all p, q ∈ S we have u_p = u_q on
> DS_p ∩ DS_q. […] let A be a connected component of DS_p ∩ DS_q. […] Theorem 4.64 implies that
> we have u_p = u_q on D_pS_A ∩ D_qS_A. […] We thus conclude that D_pS_A ∩ D_qS_A = A. […]
> Hence, we can finish the proof by constructing a GHD u : U → R of the given initial data on S
> by setting U = ⋃_{p∈S} DS_p and u(x) = u_p(x) for x ∈ DS_p. (`:1012–1021`)

> A globally hyperbolic development (GHD) […] such that U is globally hyperbolic with respect to
> the Lorentzian metric g(u, du) with Cauchy hypersurface S. (`ghd_02_19.tex:814`)

> Proposition 4.63 (Local uniqueness). Let u1 : U1 → R and u2 : U2 → R be two globally
> hyperbolic developments for (4.61) of the same initial data prescribed on a hypersurface
> S ⊆ R^{d+1}. Then there exists a common globally hyperbolic development v : V → R.
> (`ghd_02_19.tex:837`)

## Hypothesis checklist

Against the paper. Rows not listed are the originals', carried unchanged: the abstract solutions
(`agree`, `AgreementGlues`, `EqOn`), `RestartsIn` (Theorem 4.64's inputs located in each
component, `LocalUniqueness`, `FrontierStaysIn`, `SliceRestart`), `hex`, `hagreeC`, `hcaus`, and
in the region forms `hG`, `hT`, `hK`, `hLW`, `hconn`, `hSL`, `hloc`, `hstay`, `hstep`. The
checklist of `Causal.ErsUnions` stands for them.

| paper | here |
|---|---|
| background `R^{d+1}`, `U ⊆ R^{d+1}` open (`:812, 814`) | ✓ abstract `M`, `[T2Space M] [SecondCountableTopology M]` (and `[LocallyConnectedSpace M]` for 4.75, as in the original); all three hold on `R^{d+1}` |
| 4.75: each `u_p : DS_p → R` a GHD of the data on `S_p` (`:1012`) | ⚠ read (DEC-162), named: `IsCauchyLocalDevelopment (D i) S` — `DS_p` GH and tarentin for `g(u_p)`, `S` a Cauchy surface of `DS_p`, compact slabs; from `S_p` Cauchy in `DS_p` when `S ∩ DS_p = S_p ∩ DS_p` (`IsCauchySurfaceOn.of_inter_eq`); the original's `S` acausal in `DS_p` and `S` splitting `DS_p` are not asked (not needed: SCOPE) |
| 4.75: Thm 4.64 in each component `A` of `DS_p ∩ DS_q` | ✓ 4.64's argument in `A` (`ers_theorem_4_64_in_of_isCauchySurfaceOn_secondCountable`, `W = DS_p`); inputs ⚠ named (`RestartsIn`), as in the original |
| 4.63: `u₁` a GHD with Cauchy hypersurface `S` | ⚠ read (DEC-162): `hG` (only `≤_{U₁}` antisymmetric used) and `hcauchy : C.IsCauchySurfaceOn U₁ S`, in place of the original's `hacausal` (OQ-41's reading) |
| 4.63: Sogge's `DS_p` (local uniqueness) | ⚠ named: `LocalUniqueness`, as in the original |
| 4.63: "`V` is globally hyperbolic" (`:843`) | ✗ not concluded here: `ers_prop_4_63_of_isCauchySurfaceOn_secondCountable` gives a common development with `S` Cauchy; the GH form is `ers_prop_4_63_globallyHyperbolicOn_secondCountable` (`Causal.Ers464SecondCountable`), which asks the patch causally arc-connected (unlike `Causal.ErsUnions`' row, which this checklist does not inherit for 4.63) |

## SCOPE (disclosed)

* **No label is marked.** Both rows keep the originals' named analytic inputs (Sogge's local
  existence and uniqueness, Theorem 4.64's restart located in each component, `FrontierStaysIn`;
  OQ-57 (b)) and 4.75 keeps `hcaus`, a part of the printed conclusion assumed (OQ-41 (d)).
* **Why no causal arc-connectedness.** The target's title asks the trade "`S` Cauchy in the
  patch, the patch causally arc-connected" (kb/0218: deriving `IsAcausalOn` from a Cauchy surface
  needs `harc`). The originals use the acausality of `S` in `W` only to show that a union of
  opens `D ≤ W`, each with a Cauchy surface inside `S`, has `S` as Cauchy surface
  (`isCauchySurfaceOn_sSup_of_isAcausalOn`, in `isDevelopmentIn_localDevelopmentUnion` and
  `isDevelopmentIn_maxDevelopmentIn`). On a T2, second countable `M` the same union has `S` as
  Cauchy surface when `S` is a Cauchy surface of `W` (`isCauchySurfaceOn_sSup_of_secondCountable`,
  `Causal.Ers464SecondCountable`), with no arc-connectedness; `SplitBy W S` is
  `splitBy_of_t1_secondCountable`. So `harc` is never needed, and the forms do not ask it.
* **`IsCauchyLocalDevelopment` and `IsLocalDevelopment`.** `IsLocalDevelopment → IsCauchyLocal…`
  with no hypothesis; the converse holds on a T1, second countable `M` when the patch is causally
  arc-connected (`IsCauchyLocalDevelopment.isLocalDevelopment`). The sibling the target describes
  (Cauchy and arc-connectedness fields) is `IsCauchyLocalDevelopment W S ∧ C.CausallyArcConnectedOn
  W`: it implies `IsLocalDevelopment` on a T1, second countable `M`, and nothing here needs it.
* **Non-vacuity** (kb/0011): `timelikeLine_ers_theorem_4_75_secondCountable`, the original
  witness (two patches `ℝ`, `]-1, 1[`, solutions `id` and the clamp) run through the new form.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Function

universe u v

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable {C : Causality M} {S : Set M}

/-! ## 1. A local development read "`S` Cauchy" -/

/-- **A Cauchy surface may be changed outside the open set**: if `S'` is a Cauchy surface of `W`
and `S ∩ W = S' ∩ W`, then `S` is one. No acausality: an inextensible curve of `W` stays in `W`.
ERS Thm 4.75's `S_p` (Cauchy in `DS_p`) and `S`, when `S ∩ DS_p = S_p` (the integral curves of
`N`); the original's supplier route (`IsCauchySurfaceOn.of_subset_of_isAcausalOn`) needs `S`
acausal in `DS_p`. -/
theorem IsCauchySurfaceOn.of_inter_eq {W : Opens M} {S' : Set M}
    (h : C.IsCauchySurfaceOn W S') (hS : S ∩ W = S' ∩ W) : C.IsCauchySurfaceOn W S := by
  intro I c hc
  obtain ⟨x, ⟨hxI, hxS⟩, hu⟩ := h I c hc
  have hW : ∀ y ∈ c '' I, y ∈ (W : Set M) := by
    rintro _ ⟨t, ht, rfl⟩
    exact hc.1.mem ht
  have key : ∀ y ∈ c '' I, y ∈ S ↔ y ∈ S' := fun y hy => by
    have := Set.ext_iff.1 hS y
    simp only [mem_inter_iff] at this
    exact ⟨fun hyS => (this.1 ⟨hyS, hW y hy⟩).1, fun hyS' => (this.2 ⟨hyS', hW y hy⟩).1⟩
  exact ⟨x, ⟨hxI, (key x hxI).2 hxS⟩, fun y ⟨hyI, hyS⟩ => hu y ⟨hyI, (key y hyI).1 hyS⟩⟩

variable (C) in
/-- **A local development, read "`S` Cauchy"** (ERS Thm 4.75: `u_p : DS_p → ℝ`, a GHD of the data
on `S_p`; DEC-162): `W` globally hyperbolic and tarentin, with compact slabs, and `S` a Cauchy
surface of `W`. `IsLocalDevelopment` less its fields `acausal` and `split`
(`IsLocalDevelopment.isCauchyLocalDevelopment`); on a T1, second countable space `split` follows,
and `acausal` too when `W` is causally arc-connected
(`IsCauchyLocalDevelopment.isLocalDevelopment`). Supplier: local existence (Sogge) on a
`{t = 0}` patch, as for `IsLocalDevelopment`; `cauchy` from `S_p` Cauchy in `DS_p` and
`S ∩ DS_p = S_p ∩ DS_p` (`IsCauchySurfaceOn.of_inter_eq`). -/
structure IsCauchyLocalDevelopment (W : Opens M) (S : Set M) : Prop where
  gh : C.GloballyHyperbolicOn W
  tarentin : C.TarentinOn W
  slabs : C.CompactSlabs W S
  cauchy : C.IsCauchySurfaceOn W S

/-- `IsLocalDevelopment` forgets to `IsCauchyLocalDevelopment`, with no hypothesis. -/
theorem IsLocalDevelopment.isCauchyLocalDevelopment {W : Opens M}
    (h : C.IsLocalDevelopment W S) : C.IsCauchyLocalDevelopment W S :=
  ⟨h.gh, h.tarentin, h.slabs, h.cauchy⟩

/-- A Cauchy local development is split by `S`, on a T1, second countable space. -/
theorem IsCauchyLocalDevelopment.splitBy [T1Space M] [SecondCountableTopology M] {W : Opens M}
    (h : C.IsCauchyLocalDevelopment W S) : C.SplitBy W S :=
  splitBy_of_t1_secondCountable h.cauchy

/-- **A Cauchy local development of a causally arc-connected patch is a local development**, on a
T1, second countable space: `split` by `splitBy_of_t1_secondCountable`, `acausal` by
`IsCauchySurfaceOn.isAcausalOn_of_t1_secondCountable`. -/
theorem IsCauchyLocalDevelopment.isLocalDevelopment [T1Space M] [SecondCountableTopology M]
    {W : Opens M} (h : C.IsCauchyLocalDevelopment W S) (harc : C.CausallyArcConnectedOn W) :
    C.IsLocalDevelopment W S :=
  ⟨h.gh, h.tarentin, h.cauchy.isAcausalOn_of_t1_secondCountable harc, h.splitBy, h.slabs,
    h.cauchy⟩

/-- On a causally arc-connected patch of a T1, second countable space, the two readings of a local
development agree. -/
theorem isLocalDevelopment_iff_isCauchyLocalDevelopment [T1Space M] [SecondCountableTopology M]
    {W : Opens M} (harc : C.CausallyArcConnectedOn W) :
    C.IsLocalDevelopment W S ↔ C.IsCauchyLocalDevelopment W S :=
  ⟨IsLocalDevelopment.isCauchyLocalDevelopment, fun h => h.isLocalDevelopment harc⟩

/-! ## 2. Proposition 4.63 and Step 1 in a region, with `S` Cauchy in `W` -/

/-- **ERS19 Proposition 4.63 in a region `L` of an open `W` of which `S` is a Cauchy surface**, on
a T2, second countable background: `isDevelopmentIn_localDevelopmentUnion` with `hacausal`
traded for `hcauchy : C.IsCauchySurfaceOn W S`. The union of the local developments has `S` as
Cauchy surface by `isCauchySurfaceOn_sSup_of_secondCountable` (ambient `W`). -/
theorem isDevelopmentIn_localDevelopmentUnion_of_isCauchySurfaceOn_secondCountable [T2Space M]
    [SecondCountableTopology M] {W L : Opens M}
    {agree : Opens M → Prop} (hglue : AgreementGlues agree)
    (hanti : ∀ ⦃x y : M⦄, C.le W x y → C.le W y x → x = y) (hcauchy : C.IsCauchySurfaceOn W S)
    (hLW : L ≤ W) (hloc : C.LocalUniqueness (S ∩ L) L agree) :
    C.IsDevelopmentIn S L agree (C.localDevelopmentUnion (S ∩ L) L agree) := by
  set 𝒟 := {D : Opens M | D ≤ L ∧ agree D ∧ ∃ Sp ⊆ S ∩ L, C.IsCauchySurfaceOn D Sp}
  have h𝒟L : sSup 𝒟 ≤ L := sSup_le fun D hD => hD.1
  refine ⟨h𝒟L, fun p hp => ?_, hglue _ fun D hD => hD.2.1, ?_⟩
  · obtain ⟨D, hpD, hDL, hagD, hSp⟩ := hloc p hp
    exact le_sSup (show D ∈ 𝒟 from ⟨hDL, hagD, hSp⟩) hpD
  · refine isCauchySurfaceOn_sSup_of_secondCountable hanti hcauchy
      (fun D hD => hD.1.trans hLW) fun D hD => ?_
    obtain ⟨Sp, hSpS, hSp⟩ := hD.2.2
    exact ⟨Sp, hSpS.trans inter_subset_left, hSp⟩

/-- **ERS19 Proposition 4.63 with `u₁` a GHD read as `S` Cauchy in `U₁`**, on a T2, second
countable background (`ersprop:PropLocUniqueness`, unmarked): `ers_prop_4_63` with `hacausal`
(OQ-41's reading) traded for `hcauchy : C.IsCauchySurfaceOn U₁ S`. No arc-connectedness. -/
theorem ers_prop_4_63_of_isCauchySurfaceOn_secondCountable [T2Space M]
    [SecondCountableTopology M] {U₁ U₂ : Opens M} {agree : Opens M → Prop}
    (hglue : AgreementGlues agree) (hG : C.GloballyHyperbolicOn U₁)
    (hcauchy : C.IsCauchySurfaceOn U₁ S) (hloc : C.LocalUniqueness S (U₁ ⊓ U₂) agree) :
    C.IsCommonDevelopment S U₁ U₂ agree (C.localDevelopmentUnion S (U₁ ⊓ U₂) agree) := by
  have hS : S ⊆ ((U₁ ⊓ U₂ : Opens M) : Set M) := fun p hp => by
    obtain ⟨D, hpD, hDL, -⟩ := hloc p hp
    exact hDL hpD
  have h := isDevelopmentIn_localDevelopmentUnion_of_isCauchySurfaceOn_secondCountable
    (L := U₁ ⊓ U₂) hglue hG.1 hcauchy inf_le_left (by rwa [inter_eq_left.2 hS])
  rw [inter_eq_left.2 hS] at h
  exact (isCommonDevelopment_iff_isDevelopmentIn hS).2 h

/-- **Step 1 in a region, with `S` Cauchy in `W`**, on a T2, second countable background:
`isDevelopmentIn_maxDevelopmentIn` with `hacausal` traded for `hcauchy`. -/
theorem isDevelopmentIn_maxDevelopmentIn_of_isCauchySurfaceOn_secondCountable [T2Space M]
    [SecondCountableTopology M] {W L : Opens M} {agree : Opens M → Prop}
    (hglue : AgreementGlues agree) (hanti : ∀ ⦃x y : M⦄, C.le W x y → C.le W y x → x = y)
    (hcauchy : C.IsCauchySurfaceOn W S) (hLW : L ≤ W)
    (hloc : C.LocalUniqueness (S ∩ L) L agree) :
    C.IsDevelopmentIn S L agree (C.maxDevelopmentIn S L agree) := by
  have h₀ := isDevelopmentIn_localDevelopmentUnion_of_isCauchySurfaceOn_secondCountable hglue
    hanti hcauchy hLW hloc
  refine ⟨sSup_le fun V hV => hV.le, fun x hx => ?_, hglue _ fun V hV => hV.agree, ?_⟩
  · exact (le_sSup h₀ : _ ≤ C.maxDevelopmentIn S L agree) (h₀.subset hx)
  · exact isCauchySurfaceOn_sSup_of_secondCountable hanti hcauchy
      (fun V hV => hV.le.trans hLW) fun V hV => ⟨S, subset_rfl, hV.cauchy⟩

/-! ## 3. Theorem 4.64 run in a region, with `S` Cauchy in `W` -/

/-- **ERS19 Theorem 4.64's argument in a region, with `S` Cauchy in `W`** (`ersthm:ThmEx`,
unmarked), on a T2, second countable background: `maxDevelopmentIn_eq` with `hacausal` and
`hsplit` traded for `hcauchy : C.IsCauchySurfaceOn W S`. Step 1 by
`isDevelopmentIn_maxDevelopmentIn_of_isCauchySurfaceOn_secondCountable`, Step 2 with
`splitBy_of_t1_secondCountable`. -/
theorem maxDevelopmentIn_eq_of_isCauchySurfaceOn_secondCountable [T2Space M]
    [SecondCountableTopology M] {W L : Opens M} {agree : Opens M → Prop}
    (hglue : AgreementGlues agree) (hG : C.GloballyHyperbolicOn W) (hT : C.TarentinOn W)
    (hcauchy : C.IsCauchySurfaceOn W S) (hK : C.CompactSlabs W S)
    (hLW : L ≤ W) (hconn : IsPreconnected (L : Set M)) (hSL : (S ∩ L).Nonempty)
    (hloc : C.LocalUniqueness (S ∩ L) L agree)
    (hstay : ∀ V, C.IsDevelopmentIn S L agree V → C.FrontierStaysIn W S V L)
    (hstep : ∀ V, C.IsDevelopmentIn S L agree V →
      C.SliceRestart W S V L (fun _ => ∃ V', C.IsDevelopmentIn S L agree V' ∧ V < V')) :
    C.maxDevelopmentIn S L agree = L := by
  have hV₀ := isDevelopmentIn_maxDevelopmentIn_of_isCauchySurfaceOn_secondCountable hglue hG.1
    hcauchy hLW hloc
  refine le_antisymm hV₀.le ?_
  by_contra hnot
  obtain ⟨s, hs⟩ := hSL
  have hne : ((L : Set M) ∩ C.maxDevelopmentIn S L agree).Nonempty := ⟨s, hs.2, hV₀.subset hs⟩
  -- a frontier point `q` of `V₀` in `L` (`L` connected)
  obtain ⟨q, hq⟩ := exists_mem_frontier_inter hconn (C.maxDevelopmentIn S L agree).isOpen hne
    fun h => hnot h
  -- Step 2: a spacelike frontier point `p` in `L`; `S` splits `W` because it is Cauchy in `W`
  obtain ⟨p, hp, hsp⟩ := exists_isSpacelikeBoundaryPoint hG hT
    (splitBy_of_t1_secondCountable hcauchy) hK (fun x hx => hLW hx) (hstay _ hV₀) hq
  -- Steps 3–5 (the restart): a strictly larger development in `L`, against maximality
  obtain ⟨V', hV', hlt⟩ := hstep _ hV₀ p hp hsp
  exact lt_irrefl _ (hlt.trans_le (le_sSup hV'))

/-- **ERS19 Theorem 4.64 in a region, with `S` Cauchy in `W`** (`ersthm:ThmEx`, unmarked), on a
T2, second countable background: `ers_theorem_4_64_in` with `hacausal` and `hsplit` traded for
`hcauchy : C.IsCauchySurfaceOn W S`. The solutions agree on `L` and `S` is a Cauchy surface of
`L`. -/
theorem ers_theorem_4_64_in_of_isCauchySurfaceOn_secondCountable [T2Space M]
    [SecondCountableTopology M] {W L : Opens M} {agree : Opens M → Prop}
    (hglue : AgreementGlues agree) (hG : C.GloballyHyperbolicOn W) (hT : C.TarentinOn W)
    (hcauchy : C.IsCauchySurfaceOn W S) (hK : C.CompactSlabs W S)
    (hLW : L ≤ W) (hconn : IsPreconnected (L : Set M)) (hSL : (S ∩ L).Nonempty)
    (hloc : C.LocalUniqueness (S ∩ L) L agree)
    (hstay : ∀ V, C.IsDevelopmentIn S L agree V → C.FrontierStaysIn W S V L)
    (hstep : ∀ V, C.IsDevelopmentIn S L agree V →
      C.SliceRestart W S V L (fun _ => ∃ V', C.IsDevelopmentIn S L agree V' ∧ V < V')) :
    agree L ∧ C.IsCauchySurfaceOn L S := by
  have hV₀ := isDevelopmentIn_maxDevelopmentIn_of_isCauchySurfaceOn_secondCountable hglue hG.1
    hcauchy hLW hloc
  rw [maxDevelopmentIn_eq_of_isCauchySurfaceOn_secondCountable hglue hG hT hcauchy hK hLW hconn
    hSL hloc hstay hstep] at hV₀
  exact ⟨hV₀.agree, hV₀.cauchy⟩

/-! ## 4. Theorem 4.75 with the patches read "`S` Cauchy" -/

/-- **ERS19 Theorem 4.75, the claim, with each `u_p` a GHD read as `S` Cauchy in `DS_p`**
(`ersthm:ThmEx`, unmarked), on a T2, second countable background: `ers_theorem_4_75_eqOn` with
`hdev` asking `IsCauchyLocalDevelopment` (no acausality, no splitting) in place of
`IsLocalDevelopment`. `u_p = u_q` on `DS_p ∩ DS_q`, and `S` is a Cauchy surface of
`DS_p ∩ DS_q` for `g(u_p)`. -/
theorem ers_theorem_4_75_eqOn_secondCountable [T2Space M] [SecondCountableTopology M]
    [LocallyConnectedSpace M] {ι : Type*} {β : Type v}
    (cau : ι → Causality M) (D : ι → Opens M) (u : ι → M → β)
    (hdev : ∀ i, (cau i).IsCauchyLocalDevelopment (D i) S)
    (hcomp : ∀ i j, i ≠ j → ∀ x ∈ D i ⊓ D j,
      (cau i).RestartsIn (D i) (componentOpens (D i ⊓ D j) x) S (fun V => EqOn (u i) (u j) V))
    (i j : ι) :
    EqOn (u i) (u j) (D i ⊓ D j : Opens M) ∧ (cau i).IsCauchySurfaceOn (D i ⊓ D j) S := by
  by_cases hij : i = j
  · subst hij
    rw [inf_idem]
    exact ⟨fun _ _ => rfl, (hdev i).cauchy⟩
  have hanti : ∀ ⦃x y : M⦄, (cau i).le (D i ⊓ D j) x y → (cau i).le (D i ⊓ D j) y x → x = y :=
    fun _ _ h h' =>
      (hdev i).gh.1 ((cau i).le_mono inf_le_left h) ((cau i).le_mono inf_le_left h')
  have hA : ∀ x ∈ D i ⊓ D j, EqOn (u i) (u j) (componentOpens (D i ⊓ D j) x : Set M) ∧
      (cau i).IsCauchySurfaceOn (componentOpens (D i ⊓ D j) x) S := by
    intro x hx
    obtain ⟨hmeet, hloc, hstay, hstep⟩ := hcomp i j hij x hx
    exact ers_theorem_4_64_in_of_isCauchySurfaceOn_secondCountable
      (agreementGlues_eqOn (u i) (u j)) (hdev i).gh (hdev i).tarentin (hdev i).cauchy
      (hdev i).slabs ((componentOpens_le _ x).trans inf_le_left)
      isPreconnected_connectedComponentIn hmeet hloc hstay hstep
  exact ⟨fun x hx => (hA x hx).1 (mem_componentOpens hx),
    isCauchySurfaceOn_of_componentOpens hanti fun x hx => (hA x hx).2⟩

/-- **ERS19 Theorem 4.75, causal-topological skeleton, with each `u_p` a GHD read as `S` Cauchy
in `DS_p`** (`ersthm:ThmEx`, unmarked), on a T2, second countable background: `ers_theorem_4_75`
with `hdev` asking `IsCauchyLocalDevelopment` in place of `IsLocalDevelopment`. The local
developments patch to `v`, `S ⊆ ⋃ DS_p`, and `S` is a Cauchy surface of `⋃ DS_p` for every
causality agreeing with each `g(u_p)` on `DS_p` and causal on the union (`hcaus`, as in the
original). -/
theorem ers_theorem_4_75_secondCountable [T2Space M] [SecondCountableTopology M]
    [LocallyConnectedSpace M] {ι : Type*} {β : Type v}
    [Nonempty β] (cau : ι → Causality M) (D : ι → Opens M) (u : ι → M → β)
    (hex : ∀ p ∈ S, ∃ i, p ∈ D i) (hdev : ∀ i, (cau i).IsCauchyLocalDevelopment (D i) S)
    (hcomp : ∀ i j, i ≠ j → ∀ x ∈ D i ⊓ D j,
      (cau i).RestartsIn (D i) (componentOpens (D i ⊓ D j) x) S (fun V => EqOn (u i) (u j) V)) :
    ∃ v : M → β, (∀ i, EqOn v (u i) (D i)) ∧ S ⊆ ((⨆ i, D i : Opens M) : Set M) ∧
      ∀ Cu : Causality M,
        (∀ i, ∀ V : Opens M, V ≤ D i → ∀ x y, (cau i).le V x y ↔ Cu.le V x y) →
        (∀ ⦃x y : M⦄, Cu.le (⨆ i, D i) x y → Cu.le (⨆ i, D i) y x → x = y) →
        Cu.IsCauchySurfaceOn (⨆ i, D i) S := by
  classical
  have hpair := ers_theorem_4_75_eqOn_secondCountable cau D u hdev hcomp
  refine ⟨fun x => if h : ∃ i, x ∈ D i then u h.choose x else Classical.arbitrary β,
    fun i x hx => ?_, fun p hp => ?_, fun Cu hagreeC hcaus => ?_⟩
  · have h : ∃ i, x ∈ D i := ⟨i, hx⟩
    show (if h : ∃ i, x ∈ D i then u h.choose x else Classical.arbitrary β) = u i x
    rw [dif_pos h]
    exact (hpair h.choose i).1 ⟨h.choose_spec, hx⟩
  · obtain ⟨i, hi⟩ := hex p hp
    exact Opens.mem_iSup.2 ⟨i, hi⟩
  · refine isCauchySurfaceOn_iSup_of_inf D hcaus (fun i => ?_) fun i j => ?_
    · exact isCauchySurfaceOn_of_agree (hagreeC i) (hdev i).cauchy
    · exact isCauchySurfaceOn_of_agree (fun V hV => hagreeC i V (hV.trans inf_le_left))
        (hpair i j).2

end Causality

/-! ## 5. Witness (kb/0011) -/

open Causality in
/-- **A proper instance of `ers_theorem_4_75_secondCountable`**: the data of
`timelikeLine_ers_theorem_4_75` (the timelike line, `S = {0}`, patches `ℝ` and `]-1, 1[`,
solutions `id` and the clamp), with each patch a Cauchy local development. -/
theorem timelikeLine_ers_theorem_4_75_secondCountable :
    ∃ v : ℝ → ℝ, (∀ b, EqOn v (ersWitnessSolutions b) (ersWitnessPatches b)) ∧
      ({0} : Set ℝ) ⊆ ((⨆ b, ersWitnessPatches b : Opens ℝ) : Set ℝ) ∧
      ∀ Cu : Causality ℝ,
        (∀ b, ∀ V : Opens ℝ, V ≤ ersWitnessPatches b → ∀ x y,
          timelikeLine.le V x y ↔ Cu.le V x y) →
        (∀ ⦃x y : ℝ⦄, Cu.le (⨆ b, ersWitnessPatches b) x y →
          Cu.le (⨆ b, ersWitnessPatches b) y x → x = y) →
        Cu.IsCauchySurfaceOn (⨆ b, ersWitnessPatches b) {0} := by
  have hclamp : ∀ V : Opens ℝ, (V : Set ℝ) ⊆ Ioo (-1) 1 →
      EqOn (id : ℝ → ℝ) (fun x => max (-1) (min x 1)) V := fun V hV x hx => by
    obtain ⟨h1, h2⟩ := hV hx
    simp [min_eq_left h2.le, max_eq_right h1.le]
  have hinter : ∀ i j : Bool, i ≠ j →
      ((ersWitnessPatches i ⊓ ersWitnessPatches j : Opens ℝ) : Set ℝ) = Ioo (-1) 1 := by
    intro i j hij
    cases i <;> cases j <;> simp_all [ersWitnessPatches, ersWitnessIoo]
  refine Causality.ers_theorem_4_75_secondCountable (fun _ => timelikeLine) ersWitnessPatches
    ersWitnessSolutions (fun _ _ => ⟨true, trivial⟩) (fun b => ?_) fun i j hij x hx => ?_
  · cases b
    · exact timelikeLine_isLocalDevelopment_ersWitnessIoo.isCauchyLocalDevelopment
    · exact timelikeLine_isLocalDevelopment_top.isCauchyLocalDevelopment
  · have hA : componentOpens (ersWitnessPatches i ⊓ ersWitnessPatches j) x = ersWitnessIoo := by
      rw [componentOpens_eq_self (by rw [hinter i j hij]; exact isPreconnected_Ioo) hx]
      exact SetLike.coe_injective (hinter i j hij)
    rw [hA]
    refine timelikeLine_restartsIn_ersWitnessIoo fun V hV => ?_
    cases i <;> cases j
    · exact absurd rfl hij
    · exact (hclamp V hV).symm
    · exact hclamp V hV
    · exact absurd rfl hij

end Causal
