import Causal.CurvesExtendSecondCountable
import Causal.NestedCausalities
import Causal.ErsUniqueness
import Causal.ErsMughd

/-!
# ERS19 §4.4 and §4.8 on a T1, second countable background, without the curve hypotheses

Programme target `T-abs-ers-4-72-second-countable` (`programme/roadmap.toml`; layer 1: ETT-layer
imports only, `Causal.CurvesExtendSecondCountable`, `Causal.NestedCausalities`,
`Causal.ErsUniqueness`, `Causal.ErsMughd`; no model; no metric notion in a statement). Source:
Eperon–Reall–Sbierski, arXiv 1802.03020, `papers/ers-predictability`
(`legacy/labeled/ghd_02_19.tex`). Causal-topological skeletons; **no label is marked** (SCOPE):

* `erslem:two_ghds_subluminal_quasilinear` — `ghd_02_19.tex:976` (proof 980–984):
  `ers_lemma_4_72_secondCountable`, `ers_lemma_4_72_isConnected_secondCountable`.
* `erscor:CorUniqueSub` — `ghd_02_19.tex:988`: `ers_corollary_4_73_secondCountable`,
  `ers_corollary_4_73_of_isCauchySurfaceOn_secondCountable`,
  `IsMDevelopment.isUniqueDevelopment_secondCountable` (`ghd_02_19.tex:1053`).
* `ersrem:us_remark_better_bounds` — `ghd_02_19.tex:993`: no declaration of its own; Lemma 4.72's
  new form holds for any wider causality `Cm`, the bound's included.
* `ersthm:ThmMUGHD` — `ghd_02_19.tex:1055` (proof 1060–1064): `ers_theorem_4_79_secondCountable`.
* `ersthm:consider_subluminal_quasilinear_wave` — `ghd_02_19.tex:1066` (proof 1071–1073):
  `ers_theorem_4_80_secondCountable`.

Each `_secondCountable` theorem is the library's theorem of the same name without the suffix,
with `Cm.CurvesExtend` (`hmext`) and the through-hypotheses (`hthrough`, `hthrough₂`) removed and
`[SecondCountableTopology M]` added (every original is already `[T2Space M]`). They are discharged
by the curves theorem (`Causality.curvesExtend_of_t1_secondCountable`, kb/0142; DEC-190) and its
consequence on a constant curve, stated once here for every causality and every open set:
`Causality.inextensibleThrough_of_t1_secondCountable` (`InextensibleThrough W`),
`Causality.splitBy_of_t1_secondCountable` (`SplitBy W S` for a Cauchy surface `S` of `W`; since
T-abs-sc-open-hoist it is proved from the split `Causality.IsCauchySurfaceOn.mem_Jplus_union_Jminus`
of `Causal.CurvesExtendSecondCountable`, of which `SplitBy` is the statement) and
`Causality.IsCauchySurfaceOn.isAcausalOn_of_t1_secondCountable` (`IsAcausalOn W S` when `W` is
causally arc-connected), which `T-abs-ers-4-64-second-countable` uses too.
`ers_corollary_4_73_of_isCauchySurfaceOn_secondCountable` moreover trades 4.73's `hacausal` and
`hsplit` for `S` a Cauchy surface of `U₁` for `C` (ERS: `u₁` a GHD) and `U₁` causally
arc-connected for `C`.

> where u : R^{d+1} ⊇ U → R, g is a smooth Lorentz metric valued function, […]
> A globally hyperbolic development (GHD) of initial data (f0, α0) on a hypersurface S for (4.61)
> consists of a smooth solution u : U → R of (4.61) (U ⊆ R^{d+1} being open) with S ⊆ U and
> u|S = f0, du|S = α0, and such that U is globally hyperbolic with respect to the Lorentzian
> metric g(u, du) with Cauchy hypersurface S. (`ghd_02_19.tex:812, 814`)

> Lemma 4.72. Let u1 : U1 → R and u2 : U2 → R be two GHDs of a subluminal quasilinear wave
> equation (4.61) arising from the same initial data given on a connected hypersurface S that is
> achronal with respect to the Minkowski metric m. Assume, moreover, that u1 : U1 → R is a
> m-GHD. Then U1 ∩ U2 is connected.

> Let γ be a curve in U2 that starts at x and is timelike, past directed, and past inextendible
> w.r.t. g(u2, du2). It thus intersects S. (proof of Lemma 4.72, `ghd_02_19.tex:983`)

> Corollary 4.73. Let u1 : U1 → R and u2 : U2 → R be two GHDs of a subluminal quasilinear wave
> equation (4.61) arising from the same initial data given on a connected hypersurface S that is
> achronal with respect to the Minkowski metric m. Assume, moreover, that u1 : U1 → R is a
> m-GHD. Then u1 = u2 on U1 ∩ U2.

> Remark 4.74. Let us remark that better bounds on the light cones of g^{μν}(u, du) translate
> into an improvement of the uniqueness results. […]

> We note that any m-GHD is a UGHD by Corollary 4.73.

> Theorem 4.79. Consider a subluminal quasilinear wave equation of the form (4.61). Given
> initial data on a connected hypersurface S that is acausal with respect to the Minkowski metric
> there exists a UGHD u : U → R with the property that the domain of any other UGHD is
> contained in U.

> Theorem 4.80. Consider a subluminal quasilinear wave equation of the form (4.61). Given
> initial data on a connected hypersurface S that is acausal with respect to the Minkowski metric
> there exists a unique m-MGHD, i.e., a m-GHD umax : Umax → R with the property that for any
> other m-GHD u : U → R of the same initial data we have U ⊆ Umax and umax|U = u.

## Hypothesis checklist

Against the paper. The rows not listed (the abstract equation `sol`, `cau`; subluminality as
curve nesting; Theorem 4.64's and 4.75's inputs; `hDm`; `hinext`) are the originals' and are
carried unchanged: the checklists of `Causal.NestedCausalities`, `Causal.ErsUniqueness` and
`Causal.ErsMughd` stand for them.

| paper | here |
|---|---|
| background `R^{d+1}`, `U ⊆ R^{d+1}` open (`:812, 814`) | ✓ abstract `M` with `[T2Space M] [SecondCountableTopology M]`; both hold on `R^{d+1}` and its open sets (the section-1 lemmas: `[T1Space M]` only) |
| Minkowski: an m-causal curve lies on an inextendible one (used, not printed: "cannot leave `U₁` without first intersecting `S`", `:983`) | ✓ proved: `curvesExtend_of_t1_secondCountable Cm` (was the named `hmext`, `curves_extend`) |
| a past directed, past inextendible `g(u₂)`-timelike curve of `U₂` starting at `x` (`:983`; ERS's integral curves of a timelike field) | ✓ replaced by what the proof uses of it: an inextensible causal curve of `U₂` through `x`, `inextensibleThrough_of_t1_secondCountable` (was `hthrough`, `hthrough₂`); this is not ERS's curve (not timelike, not one-ended at `x`), only its role in the argument |
| Minkowski space (causal) | ⚠ named: `hm : Cm.IsCausal` (`is_causal`, a model fact of `m`) |
| 4.72, 4.73: `S` m-achronal | ⚠ strengthened: m-acausal (`Cm.IsAcausal S`; OQ-41 (c), DEC-161) |
| 4.79, 4.80: `S` m-acausal | ✓ `Cm.IsAcausal S` |
| `S` connected | ⚠ weakened: `IsPreconnected S` (`IsConnected S` in `_isConnected`) |
| GHD: GH with Cauchy hypersurface `S` | ⚠ read: `S ⊆ U` and `S` Cauchy in `U` (DEC-162); GH named where 4.64 uses it (`hG`) |
| 4.73: `u₁` a GHD | ⚠ read: in `_of_isCauchySurfaceOn_`, `C.IsCauchySurfaceOn U₁ S` with `harc` (`causally_arc_connected`, named) for `hacausal`; in `ers_corollary_4_73_secondCountable`, the original's `hacausal`, `hsplit` |
| m-GHD (GH for `m` with Cauchy `S`) | ⚠ weakened: `Cm.IsCauchySurfaceOn U₁ S`; m-GH not used |

## SCOPE (disclosed)

* **No label is marked.** What stays is listed label by label in the target's report: in 4.72,
  `Cm` causal (Minkowski's, a model fact), `S` m-acausal where ERS print m-achronal (OQ-41 (c)),
  the GHDs read through the Cauchy property, subluminality as curve nesting (layer 3); in 4.73,
  4.79, 4.80 moreover Thm 4.64's named inputs (`local_uniqueness`, `slice_restart`,
  `frontier_stays_in`; OQ-57 (b)), `GloballyHyperbolicOn`, `TarentinOn`, `CompactSlabs` of each
  m-GHD, and in 4.79, 4.80 `InextensibleNestedOn` (OQ-41 (b)), the Minkowski fact `hDm`, Thm
  4.75's existence, and the readings of OQ-78.
* **4.73's `hsplit` and `hacausal`.** `ers_corollary_4_73_secondCountable` keeps them, as the
  target words it (`SplitBy U₁ S`, `IsAcausalOn U₁ S`, the original's reading of `u₁` a GHD).
  `ers_corollary_4_73_of_isCauchySurfaceOn_secondCountable` derives both from `S` Cauchy in `U₁`
  for `C` (`splitBy_of_t1_secondCountable`; `isAcausalOn_of_t1_secondCountable`, which needs
  `U₁` causally arc-connected for `C`), and `IsMDevelopment.isUniqueDevelopment_secondCountable`
  derives both as the original does. The same trade in 4.64 and 4.67–4.68 is
  `T-abs-ers-4-64-second-countable`.
* **Remark 4.74** is not a statement with a conclusion of its own: its content is that 4.72 and
  4.73 hold with `Cm` replaced by a narrower bound `Cb` (`C₂` curve-nested in `Cb`, `Cb` causal,
  `S` `Cb`-acausal, `U₁` `Cb`-Cauchy), which the new forms give, `Cm` being arbitrary.
* **Non-vacuity** (kb/0011). The hypotheses of each new form are those of the original less
  `hmext` and the through-hypotheses, so the originals' witnesses
  (`timelikeLine_ers_lemma_4_72`, `timelikeLine_ers_theorem_4_79_4_80`) satisfy them (`ℝ` is
  second countable). Two are added: `timelikeLine_ers_lemma_4_72_secondCountable`, `U₁ = ℝ`,
  `U₂ = ]-1, 1[`, where the through-hypothesis would have asked an inextensible causal curve of
  `]-1, 1[` through each point, and now is not asked; and
  `timelikeLine_ers_corollary_4_73_of_isCauchySurfaceOn_secondCountable` (degenerate, `ℝ`), for
  the hypotheses that form adds. Both use only ETT-layer objects (`Causal.Lines`,
  `Causal.LinesCurves`, `Causal.ErsUniqueness`); `causal_ladder` derives the line's causality.
* **DEC-167** (gluing in `defi:causalite`, a future refactor): nothing here reads or builds the
  sheaf clause. `AgreementGlues` and `SolutionsGlue` are gluing of agreement and of solutions,
  not of the causality; every statement quantifies over `Causality M`, so a stronger structure
  leaves the statements as they are; only the witnesses' `timelikeLine` would need the new field,
  upstream in `Causal.Lines`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Function

universe u v

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable {S : Set M}

/-! ## 1. Through every point an inextensible causal curve -/

/-- **Through every point of every open set `W` runs an inextensible causal curve of `W`**, in a
causality on a T1, second countable space, with no other hypothesis: the constant curve at `x`
(`causalCurveOn_const`) lies on an inextensible causal curve of `W`
(`curvesExtendOn_of_t1_secondCountable`). Discharges every `InextensibleThrough` hypothesis of
`Causal.ErsUniqueness`, `Causal.ErsMughd` (and the inline `hthrough` of `ers_lemma_4_72`). -/
theorem inextensibleThrough_of_t1_secondCountable [T1Space M] [SecondCountableTopology M]
    (C : Causality M) (W : Opens M) : C.InextensibleThrough W := by
  intro x hx
  obtain ⟨I, c, hc, hsub⟩ := curvesExtendOn_of_t1_secondCountable C W (fun _ => x) 0 0 le_rfl
    (causalCurveOn_const hx)
  exact ⟨I, c, hc, hsub ⟨0, left_mem_Icc.2 le_rfl, rfl⟩⟩

/-- **A Cauchy surface of an open set splits it**, in a T1, second countable space:
`IsCauchySurfaceOn.mem_Jplus_union_Jminus` (`Causal.CurvesExtendSecondCountable`), whose statement
`SplitBy W S` is. Re-proved from it by T-abs-sc-open-hoist; before, it was
`splitBy_of_inextensibleThrough` with `InextensibleThrough W` discharged. -/
theorem splitBy_of_t1_secondCountable [T1Space M] [SecondCountableTopology M] {C : Causality M}
    {W : Opens M} (hS : C.IsCauchySurfaceOn W S) : C.SplitBy W S :=
  fun _ hq => hS.mem_Jplus_union_Jminus hq

/-- **A Cauchy surface of a causally arc-connected open set `W` is acausal in `W`**, in a T1,
second countable space: `IsCauchySurfaceOn.eq_of_le_of_t1_secondCountable` in the form
`IsAcausalOn` of `Causal.ErsUniqueness`. -/
theorem IsCauchySurfaceOn.isAcausalOn_of_t1_secondCountable [T1Space M]
    [SecondCountableTopology M] {C : Causality M} {W : Opens M} (hS : C.IsCauchySurfaceOn W S)
    (hC : C.CausallyArcConnectedOn W) : C.IsAcausalOn W S :=
  fun _ hx _ hy hxy => hS.eq_of_le_of_t1_secondCountable hC hx hy hxy

/-! ## 2. Lemma 4.72 -/

/-- **ERS19 Lemma 4.72 on a second countable background** (`erslem:two_ghds_subluminal_quasilinear`,
unmarked): `ers_lemma_4_72` without `hmext` (`Cm.CurvesExtend`) and `hthrough` (an inextensible
`C₂`-curve of `U₂` through every point of `U₁ ∩ U₂`). What is left: `Cm` causal (Minkowski), `S`
m-acausal (OQ-41 (c)), `S` Cauchy in `U₁` for `Cm` and in `U₂` for `C₂`, subluminality
(`hnest`). -/
theorem ers_lemma_4_72_secondCountable [T2Space M] [SecondCountableTopology M]
    {Cm C₂ : Causality M} {U₁ U₂ : Opens M}
    (hS : IsPreconnected S) (hS₁ : S ⊆ U₁) (hS₂ : S ⊆ U₂)
    (hm : Cm.IsCausal) (hacausal : Cm.IsAcausal S)
    (hmU₁ : Cm.IsCauchySurfaceOn U₁ S) (hC₂ : C₂.IsCauchySurfaceOn U₂ S)
    (hnest : CurveNestedOn C₂ Cm U₂) :
    IsPreconnected ((U₁ ⊓ U₂ : Opens M) : Set M) :=
  ers_lemma_4_72 hS hS₁ hS₂ hm (curvesExtend_of_t1_secondCountable Cm) hacausal hmU₁ hC₂
    (fun x hx => inextensibleThrough_of_t1_secondCountable C₂ U₂ x hx.2) hnest

/-- ERS19 Lemma 4.72 as printed ("connected"), on a second countable background: `S` non-empty.
`ers_lemma_4_72_isConnected` without `hmext` and `hthrough`. -/
theorem ers_lemma_4_72_isConnected_secondCountable [T2Space M] [SecondCountableTopology M]
    {Cm C₂ : Causality M} {U₁ U₂ : Opens M}
    (hS : IsConnected S) (hS₁ : S ⊆ U₁) (hS₂ : S ⊆ U₂)
    (hm : Cm.IsCausal) (hacausal : Cm.IsAcausal S)
    (hmU₁ : Cm.IsCauchySurfaceOn U₁ S) (hC₂ : C₂.IsCauchySurfaceOn U₂ S)
    (hnest : CurveNestedOn C₂ Cm U₂) :
    IsConnected ((U₁ ⊓ U₂ : Opens M) : Set M) :=
  ers_lemma_4_72_isConnected hS hS₁ hS₂ hm (curvesExtend_of_t1_secondCountable Cm) hacausal hmU₁
    hC₂ (fun x hx => inextensibleThrough_of_t1_secondCountable C₂ U₂ x hx.2) hnest

/-! ## 3. Corollary 4.73 -/

/-- **ERS19 Corollary 4.73 on a second countable background** (`erscor:CorUniqueSub`, unmarked):
`ers_corollary_4_73` without `hmext` and `hthrough₂`; every other hypothesis carried, with the
suppliers named there. `hsplit` follows from `S` Cauchy in `U₁` (`splitBy_of_t1_secondCountable`)
and `hacausal` from it with `U₁` causally arc-connected
(`IsCauchySurfaceOn.isAcausalOn_of_t1_secondCountable`); both are kept, as in the original. -/
theorem ers_corollary_4_73_secondCountable [T2Space M] [SecondCountableTopology M]
    {C Cm C₂ : Causality M} {U₁ U₂ : Opens M}
    {agree : Opens M → Prop} (hglue : AgreementGlues agree)
    (hG : C.GloballyHyperbolicOn U₁) (hT : C.TarentinOn U₁) (hacausal : C.IsAcausalOn U₁ S)
    (hsplit : C.SplitBy U₁ S) (hK : C.CompactSlabs U₁ S)
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
    agree (U₁ ⊓ U₂) :=
  ers_corollary_4_73 hglue hG hT hacausal hsplit hK hS hm (curvesExtend_of_t1_secondCountable Cm)
    hmacausal hmU₁ hC₂ (fun x hx => inextensibleThrough_of_t1_secondCountable C₂ U₂ x hx.2) hnest
    hlocal hstay hstep

/-- **ERS19 Corollary 4.73 with `u₁` a GHD read as `S` Cauchy in `U₁`**, on a second countable
background (`erscor:CorUniqueSub`, unmarked): `ers_corollary_4_73_secondCountable` with `hsplit`
derived from `hC₁` (`splitBy_of_t1_secondCountable`) and `hacausal` from `hC₁` and `U₁` causally
arc-connected for `C` (`IsCauchySurfaceOn.isAcausalOn_of_t1_secondCountable`). -/
theorem ers_corollary_4_73_of_isCauchySurfaceOn_secondCountable [T2Space M]
    [SecondCountableTopology M] {C Cm C₂ : Causality M} {U₁ U₂ : Opens M}
    {agree : Opens M → Prop} (hglue : AgreementGlues agree)
    (hG : C.GloballyHyperbolicOn U₁) (hT : C.TarentinOn U₁) (hC₁ : C.IsCauchySurfaceOn U₁ S)
    (harc : C.CausallyArcConnectedOn U₁) (hK : C.CompactSlabs U₁ S)
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
    agree (U₁ ⊓ U₂) :=
  ers_corollary_4_73_secondCountable hglue hG hT (hC₁.isAcausalOn_of_t1_secondCountable harc)
    (splitBy_of_t1_secondCountable hC₁) hK hS hm hmacausal hmU₁ hC₂ hnest hlocal hstay hstep

end Causality

/-! ## 4. Every m-GHD is a UGHD; Theorems 4.79 and 4.80 -/

section Developments

variable {β : Type v} {sol : Opens M → (M → β) → Prop} {cau : (M → β) → Causality M}
  {Cm : Causality M} {S : Set M}

/-- **"Any m-GHD is a UGHD by Corollary 4.73"** (`ghd_02_19.tex:1053`) on a second countable
background: `IsMDevelopment.isUniqueDevelopment` without `hmext` and `hthrough`. Derived, not
assumed: 4.73's `hacausal`, `hsplit`, `hthrough₂`, `hnest`, and `Cm.CurvesExtend`. -/
theorem IsMDevelopment.isUniqueDevelopment_secondCountable [T2Space M]
    [SecondCountableTopology M]
    (hsub : ∀ U u, sol U u → Causality.CurveNestedOn (cau u) Cm U)
    (harc : ∀ U u, sol U u → (cau u).CausallyArcConnectedOn U)
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
    IsUniqueDevelopment sol cau S U₁ u₁ :=
  h.isUniqueDevelopment hsub harc hm (Causality.curvesExtend_of_t1_secondCountable Cm) hmacausal
    hS (fun U u _ => Causality.inextensibleThrough_of_t1_secondCountable (cau u) U) hG hT hK hlocal
    hstay hstep

/-- **ERS19 Theorem 4.79 on a second countable background** (`ersthm:ThmMUGHD`, unmarked): the
MUGHD exists. `ers_theorem_4_79` without `hmext` and `hthrough`; every other hypothesis carried,
with the suppliers named there. -/
theorem ers_theorem_4_79_secondCountable [T2Space M] [SecondCountableTopology M]
    (hloc : SolutionLocal sol) (hglue : SolutionsGlue sol)
    (hfollow : CausalityFollows cau)
    (hsub : ∀ U u, sol U u → Causality.CurveNestedOn (cau u) Cm U)
    (harc : ∀ U u, sol U u → (cau u).CausallyArcConnectedOn U)
    (hinext : ∀ U u, sol U u → Causality.InextensibleNestedOn (cau u) Cm U)
    (hm : Cm.IsCausal) (hmacausal : Cm.IsAcausal S)
    (hS : IsPreconnected S)
    (hex : ∃ U u, IsDevelopment sol cau S U u)
    (hDm : ∀ U u, IsDevelopment sol cau S U u →
      ∃ W : Opens M, W ≤ U ∧ S ⊆ W ∧ Cm.IsCauchySurfaceOn W S ∧ sol W u)
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
    ∃ U u, IsMaximalUniqueDevelopment sol cau S U u :=
  ers_theorem_4_79 hloc hglue hfollow hsub harc hinext hm
    (Causality.curvesExtend_of_t1_secondCountable Cm) hmacausal hS hex hDm
    (fun U u _ => Causality.inextensibleThrough_of_t1_secondCountable (cau u) U) hG hT hK hlocal
    hstay hstep

/-- **ERS19 Theorem 4.80 on a second countable background**
(`ersthm:consider_subluminal_quasilinear_wave`, unmarked): the m-MGHD exists (unique by
`IsMaximalMDevelopment.unique`). `ers_theorem_4_80` without `hmext` and `hthrough`; every other
hypothesis carried, with the suppliers named there. -/
theorem ers_theorem_4_80_secondCountable [T2Space M] [SecondCountableTopology M]
    (hloc : SolutionLocal sol) (hglue : SolutionsGlue sol)
    (hfollow : CausalityFollows cau)
    (hsub : ∀ U u, sol U u → Causality.CurveNestedOn (cau u) Cm U)
    (harc : ∀ U u, sol U u → (cau u).CausallyArcConnectedOn U)
    (hinext : ∀ U u, sol U u → Causality.InextensibleNestedOn (cau u) Cm U)
    (hm : Cm.IsCausal) (hmacausal : Cm.IsAcausal S)
    (hS : IsPreconnected S)
    (hex : ∃ U u, IsDevelopment sol cau S U u)
    (hDm : ∀ U u, IsDevelopment sol cau S U u →
      ∃ W : Opens M, W ≤ U ∧ S ⊆ W ∧ Cm.IsCauchySurfaceOn W S ∧ sol W u)
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
    ∃ U u, IsMaximalMDevelopment sol cau Cm S U u :=
  ers_theorem_4_80 hloc hglue hfollow hsub harc hinext hm
    (Causality.curvesExtend_of_t1_secondCountable Cm) hmacausal hS hex hDm
    (fun U u _ => Causality.inextensibleThrough_of_t1_secondCountable (cau u) U) hG hT hK hlocal
    hstay hstep

end Developments

/-! ## 5. Witnesses (kb/0011) -/

/-- **A proper instance of Lemma 4.72's new form**: on the timelike line, `Cm = C₂` the timelike
line, `S = {0}`, `U₁ = ℝ`, `U₂ = ]-1, 1[`. The through-hypothesis of the original (an inextensible
causal curve of `]-1, 1[` through every point) is not asked. ETT-layer objects only; the line's
causality by `causal_ladder` from its global hyperbolicity. -/
theorem timelikeLine_ers_lemma_4_72_secondCountable {U₂ : Opens ℝ}
    (hU₂ : (U₂ : Set ℝ) = Ioo (-1) 1) :
    IsPreconnected (((⊤ : Opens ℝ) ⊓ U₂ : Opens ℝ) : Set ℝ) := by
  have h0 : (0 : ℝ) ∈ (U₂ : Set ℝ) := by rw [hU₂]; norm_num
  have hGH := timelikeLine_globallyHyperbolic
  have hm : timelikeLine.IsCausal := by causal_ladder
  exact Causality.ers_lemma_4_72_secondCountable (Cm := timelikeLine) (C₂ := timelikeLine)
    (S := {0}) isPreconnected_singleton (fun _ _ => trivial) (singleton_subset_iff.2 h0) hm
    (fun _ hx _ hy _ => (mem_singleton_iff.1 hx).trans (mem_singleton_iff.1 hy).symm)
    timelikeLine_isCauchySurface_zero
    (timelikeLine_isCauchySurfaceOn_Ioo one_pos hU₂)
    ((Causality.LeNested.refl _).curveNestedOn U₂)

/-- **The hypotheses of `ers_corollary_4_73_of_isCauchySurfaceOn_secondCountable` are jointly
satisfiable** (degenerate): on the timelike line, `C = Cm = C₂` the line, `U₁ = U₂ = ℝ`,
`S = {0}`, `agree = EqOn id id`; `hC₁` is `{0}` Cauchy in `ℝ`, `harc` the line's causal
arc-connectedness, and `hlocal`, `hstay`, `hstep` hold as in `timelikeLine_ers_theorem_4_64`. -/
theorem timelikeLine_ers_corollary_4_73_of_isCauchySurfaceOn_secondCountable :
    EqOn (id : ℝ → ℝ) id (((⊤ : Opens ℝ) ⊓ ⊤ : Opens ℝ) : Set ℝ) := by
  have hGH := timelikeLine_globallyHyperbolic
  have hm : timelikeLine.IsCausal := by causal_ladder
  have hcd : timelikeLine.IsCommonDevelopment ({0} : Set ℝ) ⊤ ⊤
      (fun V : Opens ℝ => EqOn (id : ℝ → ℝ) id V) ⊤ :=
    ⟨le_inf le_rfl le_rfl, fun _ _ => trivial, fun _ _ => rfl,
      timelikeLine_isCauchySurface_zero⟩
  refine Causality.ers_corollary_4_73_of_isCauchySurfaceOn_secondCountable (Cm := timelikeLine)
    (C₂ := timelikeLine) (agreementGlues_eqOn id id) hGH
    (Causality.tarentinOn_top.2 timelikeLine_tarentin) timelikeLine_isCauchySurface_zero
    timelikeLine_causallyArcConnected ?_ isPreconnected_singleton hm
    (fun _ hx _ hy _ => (mem_singleton_iff.1 hx).trans (mem_singleton_iff.1 hy).symm)
    timelikeLine_isCauchySurface_zero timelikeLine_isCauchySurface_zero
    ((Causality.LeNested.refl _).curveNestedOn ⊤) ⟨⊤, hcd⟩ ?_ ?_
  · intro q
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
  · intro V _ q _
    exact ⟨fun _ _ _ => ⟨trivial, trivial⟩, fun _ _ _ => ⟨trivial, trivial⟩⟩
  · intro V _ p hp _
    refine ⟨⊤, hcd, lt_top_iff_ne_top.2 fun hV => ?_⟩
    have : frontier ((V : Opens ℝ) : Set ℝ) = ∅ := by rw [hV, Opens.coe_top, frontier_univ]
    rw [this] at hp
    exact hp.1

end Causal
