import Causal.Ers464WithoutArc
import Causal.Ers464SecondCountable
import Causal.ErsSecondCountable
import Causal.ErsUniqueness
import Causal.ErsUnions
import Causal.LadderLocal
import Causal.NestedCausalities
import Causal.InextensibleNestedBasics
import Causal.CBG.CausalConvex
import Causal.Ladder.Rules

/-!
# Non-vacuity witnesses for ERS19 Corollaries 4.68, 4.69, 4.71 and Theorem 4.82

Programme target `T-abs-ers-witnesses` (`programme/roadmap.toml`; layer 1: ETT-layer imports
only, no model, no metric notion). Source: Eperon–Reall–Sbierski, arXiv 1802.03020,
`papers/ers-predictability` (`legacy/labeled/ghd_02_19.tex`). Witnesses (kb/0011) for forms that
had none; **no label is marked**, and none is certified here:

* `erscor:CorDisCon` — `ghd_02_19.tex:921`: `timelikeLine_ers_corollary_4_68` and its `_eqOn`,
  `_of_isCauchySurfaceOn_secondCountable` (both) and `…_noArc` (both) forms; the finding
  `real_isPreconnected_inf_of_isCauchySurfaceOn`, `real_ers_corollary_4_68_agree`.
* `erscor:globally_defined_globally_hyperbolic` — `ghd_02_19.tex:926`:
  `timelikeLine_ers_corollary_4_69`, `_secondCountable`, `_of_isCauchySurface_secondCountable`.
* `erscor:CorSupLum` — `ghd_02_19.tex:959`: `timelikeLine_ers_corollary_4_71`,
  `_secondCountable`, `_of_isCauchySurfaceOn_secondCountable`.
* `ersthm:ThmNotBlocking` — `ghd_02_19.tex:1100`: `timelikeLine_ers_theorem_4_82`,
  `_of_oneSidedBoundary`, `_of_sliceRestart`, `_of_globallyHyperbolicOn`,
  `_of_isCauchySurfaceOn_secondCountable`; the findings `ers_theorem_4_82_hstep_of_le`,
  `ers_theorem_4_82_hstep_iff`.

Each `timelikeLine_<form>` applies `<form>` to a proof of each of its hypotheses on `ℝ` with the
timelike line and `S = {0}`, and states the form's conclusion on that data.

> Corollary 4.68. Let u1 : U1 → R and u2 : U2 → R be two globally hyperbolic developments of
> (4.61) arising from the same initial data on a connected hypersurface S ⊆ R^{d+1}. If there
> exists an x ∈ U1 ∩ U2 with u1(x) ≠ u2(x), then U1 ∩ U2 is not connected. (`:922`)

> Corollary 4.69. Let u1 : R^{d+1} → R be a globally defined globally hyperbolic development of
> (4.61) arising from some initial data on a connected hypersurface S ⊆ R^{d+1}. Let u2 : U2 → R
> be another globally hyperbolic development of (4.61) of the same initial data. Then
> u1|U2 = u2. (`:927`)

> Corollary 4.71. […] Given two globally hyperbolic developments u1 : U1 → R and u2 : U2 → R,
> we then have u1(x) = u2(x) for all x ∈ U1 ∩ U2. (`:962`)

> Theorem 4.82. Let u1 : U1 → R be a MGHD of given initial data […] and assume that (4.83) […]
> Then u1 : U1 → R is the unique MGHD, i.e., any other GHD u : U → R satisfies U ⊆ U1 and thus
> also u1|U = u. (`:1101, 1106`)

> […] consider a spacelike but not achronal hypersurface that winds up around the x^0-axis in
> R × (B_2^d(0) ∖ B_1^d(0)) ⊆ R^{d+1}. […] Given two globally hyperbolic developments, their
> intersection is in general not connected and global uniqueness does not hold. (`:930`)

## The witnesses (form → data)

| form | data on `ℝ`, timelike line, `S = {0}` |
|---|---|
| 4.68, all six forms | `U₁ = ℝ`, `U₂ = ]-1, 1[ ∪ ]2, 3[`, `u₁ = 0`, `u₂ = 1` on `]2, ∞[`, `0` elsewhere (`ErsWitness.data_4_68`) |
| 4.69, three forms | `U₁ = ℝ`, `U₂ = ]-1, 1[`, `u₁ = id`, `u₂` the clamp (`ErsNoArcWitness.data`) |
| 4.71, three forms | the same, `Cτ = C₂ = C`, `hn₁`, `hn₂` by `InextensibleNestedOn.refl`, `T`'s curve `id` |
| 4.82, five forms | `ι = Bool`, `dom true = ]-1, 1[` (maximal), `dom false = ]-1/2, 1/2[`, `cau` the line (`ErsWitness.data_4_82`) |

The `…_noArc` forms of 4.69 and 4.71 already have witnesses (`ErsNoArcWitness.conclusions`,
`ErsNoArcWitness.corollaries`, `Causal.Ers464WithoutArc`); they are not restated.

## Hypothesis checklist

Witnesses, not certificates: every binder of every form is inhabited, none is added or dropped.

| hypothesis | here |
|---|---|
| 4.68's `hdis` / `hx` (a disagreement on `U₁ ∩ U₂`) | ✓ at `x = 5/2` |
| 4.68's `hlocal`, `hstay`, `hstep` | ✓ non-vacuous: at `]-1/2, 1/2[` the premise is met at `1/2` (`ErsWitness.restart_premise_4_68`) |
| 4.82's `hmax`, `honesided` | ✓ non-vacuous: `dom false < dom true`; the frontier of `dom true` off `closure S` is `{-1, 1}` (`ErsWitness.frontier_dom82_true_diff`) |
| 4.82's `hstep` | ✓ but vacuous, necessarily: `ers_theorem_4_82_hstep_of_le` (SCOPE) |

## SCOPE (disclosed)

* **4.68 on the line, and the binder's argument.** The Lean forms of 4.68 ask nothing of `U₂`
  but `hlocal`, `hstay`, `hstep`: not that `U₂` be a development (`S` Cauchy in `U₂`). So a
  disconnected `U₂` is allowed, and the line witnesses all six forms. In the paper's reading
  (`u₂` a GHD, `S` Cauchy in `U₂` for some causality) no witness exists on `ℝ`:
  `real_isPreconnected_inf_of_isCauchySurfaceOn` (two developments of a preconnected `S` on `ℝ`
  meet in a preconnected set, for any causalities) and `real_ers_corollary_4_68_agree` (so the
  solutions agree, and `hdis` fails). `ErsWitness.not_isCauchySurfaceOn_disU₂` records that the
  witness's `U₂` is a development for no causality. So on `ℝ^{d+1}` with `d = 0` the paper's
  hypotheses exclude a disagreement; the paper's own example (`:930`) winds around an annulus,
  so `d ≥ 2`. A witness in the paper's reading is not given here, and a plane is not enough by
  itself: with one flat causality, 1+1 Minkowski gives none either (argued: a connected spacelike
  curve there is a graph of slope below 1, hence acausal, and Lemma 4.70's argument with `T = ∂ₜ`
  makes the overlap connected); it needs a non-flat causality or two different causalities, as in
  the paper's 2+1 example. The library discloses the forms' weakening at
  `Causal/ErsUniqueness.lean:64` ("u₂ a GHD | ⚠ weakened").
* **4.82's `hstep` is vacuous in every instance.** If `dom i ≤ dom i₁`, the component `Aᵢ` of
  `dom i₁ ∩ dom i` through `s₀` is `dom i`, open, so no frontier point of `Aᵢ` lies in `dom i`
  (`ers_theorem_4_82_hstep_of_le`). Given the other hypotheses, `hstep` is therefore equivalent
  to the conclusion (`ers_theorem_4_82_hstep_iff`). No witness can exercise it; the witness
  exercises the rest. The other 4.82 forms take the same `hstep`.
* `timelikeLine_tarentinOn` (the timelike line is tarentin on every open set) and
  `oneSidedBoundary_of_ordConnected` (an order-connected open of `ℝ` has a one-sided boundary off
  any set) are general helpers.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Function

universe u

/-! ## 1. Helpers on the timelike line -/

/-- **The timelike line is tarentin on every open set** of `ℝ` (the proof of
`timelikeLine_isLocalDevelopment_ersWitnessIoo`'s `tarentin` field, for any open set). -/
theorem timelikeLine_tarentinOn (U : Opens ℝ) : timelikeLine.TarentinOn U := by
  intro x hx N hN
  obtain ⟨l, u, ⟨hl, hu⟩, hlu⟩ :=
    mem_nhds_iff_exists_Ioo_subset.1 (inter_mem hN (U.isOpen.mem_nhds hx))
  refine ⟨(l + x) / 2, (hlu ⟨by linarith, by linarith⟩).1, (x + u) / 2,
    (hlu ⟨by linarith, by linarith⟩).1, ?_⟩
  show x ∈ interior (timelikeLine.diamond U ((l + x) / 2) ((x + u) / 2))
  refine interior_maximal (t := Ioo ((l + x) / 2) ((x + u) / 2)) (fun z hz => ?_) isOpen_Ioo
    ⟨by linarith, by linarith⟩
  rw [Causality.mem_diamond, timelikeLine_le, timelikeLine_le]
  exact ⟨⟨hz.1.le, fun w hw => (hlu ⟨by linarith [hw.1], by linarith [hw.2, hz.2]⟩).2⟩,
    hz.2.le, fun w hw => (hlu ⟨by linarith [hw.1, hz.1], by linarith [hw.2]⟩).2⟩

/-- **An order-connected open set of `ℝ` has a one-sided boundary** off any set `B`: a ball
around a frontier point meets it in an interval. -/
theorem oneSidedBoundary_of_ordConnected {U : Opens ℝ} (hU : OrdConnected (U : Set ℝ))
    (B : Set ℝ) : Causality.OneSidedBoundary U B := by
  intro p _ N hN
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hN
  refine ⟨Metric.ball p ε, Metric.ball_mem_nhds p hε, hball, ?_⟩
  rw [Real.ball_eq_Ioo]
  exact isPreconnected_iff_ordConnected.2 (ordConnected_Ioo.inter hU)

namespace Causality

/-! ## 2. Findings about the statements -/

/-- **Two developments of a preconnected `S` on `ℝ` meet in a preconnected set**, for any two
causalities: each is preconnected (`isPreconnected_of_isCauchySurfaceOn_of_t1_secondCountable`),
so an interval of `ℝ`, and two intervals meet in an interval. -/
theorem real_isPreconnected_inf_of_isCauchySurfaceOn {C₁ C₂ : Causality ℝ} {U₁ U₂ : Opens ℝ}
    {S : Set ℝ} (hS : IsPreconnected S) (hS₁ : S ⊆ U₁) (hS₂ : S ⊆ U₂)
    (hC₁ : C₁.IsCauchySurfaceOn U₁ S) (hC₂ : C₂.IsCauchySurfaceOn U₂ S) :
    IsPreconnected ((U₁ ⊓ U₂ : Opens ℝ) : Set ℝ) := by
  have h₁ := isPreconnected_iff_ordConnected.1
    (isPreconnected_of_isCauchySurfaceOn_of_t1_secondCountable hS hS₁ hC₁)
  have h₂ := isPreconnected_iff_ordConnected.1
    (isPreconnected_of_isCauchySurfaceOn_of_t1_secondCountable hS hS₂ hC₂)
  rw [Opens.coe_inf]
  exact isPreconnected_iff_ordConnected.2 (h₁.inter h₂)

/-- **On `ℝ`, Corollary 4.68 in the paper's reading has no instance**: with the hypotheses of
`ers_corollary_4_68_of_isCauchySurfaceOn_secondCountable_noArc`, `S` preconnected and `u₂` a
development (`S` Cauchy in `U₂` for some causality `C₂`), the solutions agree on `U₁ ∩ U₂`, so the
disagreement `hdis` of 4.68 cannot hold. -/
theorem real_ers_corollary_4_68_agree {C C₂ : Causality ℝ} {U₁ U₂ : Opens ℝ} {S : Set ℝ}
    {agree : Opens ℝ → Prop} (hglue : AgreementGlues agree)
    (hG : C.GloballyHyperbolicOn U₁) (hT : C.TarentinOn U₁) (hC₁ : C.IsCauchySurfaceOn U₁ S)
    (hK : C.CompactSlabs U₁ S)
    (hlocal : ∃ V, C.IsCommonDevelopment S U₁ U₂ agree V)
    (hstay : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.FrontierStaysIn U₁ S V ((U₁ ⊓ U₂ : Opens ℝ) : Set ℝ))
    (hstep : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.SliceRestart U₁ S V ((U₁ ⊓ U₂ : Opens ℝ) : Set ℝ)
        (fun _ => ∃ V', C.IsCommonDevelopment S U₁ U₂ agree V' ∧ V < V'))
    (hS : IsPreconnected S) (hC₂ : C₂.IsCauchySurfaceOn U₂ S) :
    agree (U₁ ⊓ U₂) := by
  have hSU : S ⊆ U₁ ⊓ U₂ := by
    obtain ⟨V, hV⟩ := hlocal
    exact fun s hs => hV.le (hV.subset hs)
  exact ers_theorem_4_64_of_isCauchySurfaceOn_secondCountable_noArc hglue hG hT hC₁ hK
    (real_isPreconnected_inf_of_isCauchySurfaceOn hS (fun s hs => (hSU hs).1)
      (fun s hs => (hSU hs).2) hC₁ hC₂) hlocal hstay hstep

/-- **A slice restart at a development inside `U₁` is vacuous**: if `U ≤ U₁` is preconnected and
contains `s₀`, the component of `U₁ ∩ U` through `s₀` is the open `U`, whose frontier misses
`U`. -/
theorem sliceRestart_connectedComponentIn_of_le {M : Type u} [TopologicalSpace M]
    {D : Causality M} {U₁ U W : Opens M} {S : Set M} {s₀ : M} {Q : M → Prop} (hle : U ≤ U₁)
    (hconn : IsPreconnected (U : Set M)) (hs₀ : s₀ ∈ U) :
    D.SliceRestart W S (connectedComponentIn ((U₁ : Set M) ∩ U) s₀) U Q := by
  rintro p ⟨hpf, hpU⟩ -
  rw [inter_eq_right.2 (show (U : Set M) ⊆ U₁ from hle), hconn.connectedComponentIn hs₀,
    U.isOpen.frontier_eq] at hpf
  exact absurd hpU hpf.2

/-- **Theorem 4.82's `hstep` follows from its conclusion** (with `hSU`, `hconn`, `s₀ ∈ S`): when
every `dom i` lies in `dom i₁`, `hstep` holds, in the shape of `ers_theorem_4_82_of_sliceRestart`
(definitionally that of `ers_theorem_4_82`). So `hstep` is vacuous in every instance. -/
theorem ers_theorem_4_82_hstep_of_le {M : Type u} [TopologicalSpace M] {ι : Type*}
    (dom : ι → Opens M) (cau : ι → Causality M) {S : Set M} {s₀ : M} (hs₀ : s₀ ∈ S) (i₁ : ι)
    (hSU : ∀ i, S ⊆ dom i) (hconn : ∀ i, IsPreconnected (dom i : Set M))
    (hle : ∀ i, dom i ≤ dom i₁) :
    ∀ i, (cau i).SliceRestart (dom i) S
      (connectedComponentIn ((dom i₁ : Set M) ∩ dom i) s₀) (dom i)
      (fun p => (∃ V ∈ 𝓝 p, V ⊆ dom i ∧
        V ∩ dom i₁ ⊆ connectedComponentIn ((dom i₁ : Set M) ∩ dom i) s₀) →
        ∃ j, dom i₁ < dom j) :=
  fun i => sliceRestart_connectedComponentIn_of_le (hle i) (hconn i) (hSU i hs₀)

/-- **Given its other hypotheses, Theorem 4.82's `hstep` is equivalent to its conclusion**:
`ers_theorem_4_82_of_sliceRestart` gives one direction, `ers_theorem_4_82_hstep_of_le` the other.
The binders are those of `ers_theorem_4_82_of_sliceRestart` less `hstep`. -/
theorem ers_theorem_4_82_hstep_iff {M : Type u} [TopologicalSpace M] [T2Space M]
    [LocallyConnectedSpace M] {ι : Type*}
    (dom : ι → Opens M) (cau : ι → Causality M) {S : Set M} {s₀ : M} (hs₀ : s₀ ∈ S) (i₁ : ι)
    (hSU : ∀ i, S ⊆ dom i)
    (hmax : ∀ i, dom i₁ ≤ dom i → dom i = dom i₁)
    (hconn : ∀ i, IsPreconnected (dom i : Set M))
    (hcaus : ∀ i ⦃x y : M⦄, (cau i).le (dom i) x y → (cau i).le (dom i) y x → x = y)
    (hsplit : ∀ i, (cau i).SplitBy (dom i) S)
    (hJm : ∀ i, ∀ x ∈ dom i, closure ((cau i).Jminus (dom i) {x}) ∩ dom i ⊆
      (cau i).Jminus (dom i) {x})
    (hJp : ∀ i, ∀ x ∈ dom i, closure ((cau i).Jplus (dom i) {x}) ∩ dom i ⊆
      (cau i).Jplus (dom i) {x})
    (hK : ∀ i, (cau i).CompactSlabs (dom i) S)
    (hSclosed : ∀ i, closure S ∩ dom i ⊆ S)
    (honesided : OneSidedBoundary (dom i₁) (closure S)) :
    (∀ i, (cau i).SliceRestart (dom i) S
      (connectedComponentIn ((dom i₁ : Set M) ∩ dom i) s₀) (dom i)
      (fun p => (∃ V ∈ 𝓝 p, V ⊆ dom i ∧
        V ∩ dom i₁ ⊆ connectedComponentIn ((dom i₁ : Set M) ∩ dom i) s₀) →
        ∃ j, dom i₁ < dom j)) ↔ ∀ i, dom i ≤ dom i₁ :=
  ⟨ers_theorem_4_82_of_sliceRestart dom cau hs₀ i₁ hSU hmax hconn hcaus hsplit hJm hJp hK hSclosed
    honesided, ers_theorem_4_82_hstep_of_le dom cau hs₀ i₁ hSU hconn⟩

end Causality

/-! ## 3. Corollary 4.68: a disconnected overlap on the line -/

namespace ErsWitness

open Causality

/-- The second domain of the 4.68 witness: `]-1, 1[ ∪ ]2, 3[`. -/
def disU₂ : Opens ℝ := ⟨Ioo (-1) 1 ∪ Ioo 2 3, isOpen_Ioo.union isOpen_Ioo⟩

/-- The second solution of the 4.68 witness: `1` on `]2, ∞[`, `0` elsewhere; the first is `0`. -/
noncomputable def disSol₂ : ℝ → ℝ := fun x => if 2 < x then 1 else 0

/-- The agreement of the 4.68 witness: `u₁ = 0` and `u₂ = disSol₂` agree on `V`. -/
def disAgree : Opens ℝ → Prop := fun V => EqOn (fun _ : ℝ => (0 : ℝ)) disSol₂ V

theorem coe_top_inf_disU₂ :
    (((⊤ : Opens ℝ) ⊓ disU₂ : Opens ℝ) : Set ℝ) = Ioo (-1) 1 ∪ Ioo 2 3 := by
  rw [Opens.coe_inf, Opens.coe_top, univ_inter]; rfl

/-- On an open set where `u₁ = 0` and `u₂ = disSol₂` agree, no point exceeds `2`. -/
theorem not_lt_of_disAgree {V : Opens ℝ} (h : disAgree V) {x : ℝ} (hx : x ∈ V) : ¬ 2 < x :=
  fun h2 => by
    have := h hx
    simp [disSol₂, h2] at this

/-- `u₁ = 0` and `u₂ = disSol₂` agree on every open set in `]-∞, 2]`. -/
theorem disAgree_of_subset {V : Opens ℝ} (hV : (V : Set ℝ) ⊆ Iic 2) : disAgree V :=
  fun x hx => by simp [disSol₂, not_lt.2 (mem_Iic.1 (hV hx))]

/-- **Every common development of the 4.68 witness lies in `]-1, 1[`**: it lies in
`]-1, 1[ ∪ ]2, 3[`, and the solutions disagree on `]2, 3[`. -/
theorem subset_Ioo_of_isCommonDevelopment {V : Opens ℝ}
    (hV : timelikeLine.IsCommonDevelopment ({0} : Set ℝ) ⊤ disU₂ disAgree V) :
    (V : Set ℝ) ⊆ Ioo (-1) 1 := by
  intro x hx
  have hxL : x ∈ Ioo (-1 : ℝ) 1 ∪ Ioo 2 3 := by
    rw [← coe_top_inf_disU₂]; exact hV.le hx
  rcases hxL with h | h
  · exact h
  · exact absurd h.1 (not_lt_of_disAgree hV.agree hx)

/-- A frontier point in `U₁ ∩ U₂` of a common development of the 4.68 witness is in `]-1, 1[`. -/
theorem mem_Ioo_of_mem_frontier {V : Opens ℝ}
    (hV : timelikeLine.IsCommonDevelopment ({0} : Set ℝ) ⊤ disU₂ disAgree V) {p : ℝ}
    (hp : p ∈ frontier (V : Set ℝ) ∩ (((⊤ : Opens ℝ) ⊓ disU₂ : Opens ℝ) : Set ℝ)) :
    p ∈ Ioo (-1 : ℝ) 1 := by
  have hcl : p ∈ Icc (-1 : ℝ) 1 := by
    rw [← closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]
    exact closure_mono (subset_Ioo_of_isCommonDevelopment hV) (frontier_subset_closure hp.1)
  have hpL := hp.2
  rw [coe_top_inf_disU₂] at hpL
  rcases hpL with h | h
  · exact h
  · exact absurd (h.1.trans_le hcl.2) (by norm_num)

/-- The intervals `]-r, r[`, `0 < r ≤ 1`, are common developments of the 4.68 witness. -/
theorem isCommonDevelopment_Ioo {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) {V : Opens ℝ}
    (hV : (V : Set ℝ) = Ioo (-r) r) :
    timelikeLine.IsCommonDevelopment ({0} : Set ℝ) ⊤ disU₂ disAgree V := by
  have hsub : (V : Set ℝ) ⊆ Ioo (-1) 1 := by
    rw [hV]; exact Ioo_subset_Ioo (by linarith) hr1
  refine ⟨fun x hx => ?_, ?_, disAgree_of_subset fun x hx => ?_,
    timelikeLine_isCauchySurfaceOn_Ioo hr hV⟩
  · rw [← SetLike.mem_coe, coe_top_inf_disU₂]; exact Or.inl (hsub hx)
  · rw [singleton_subset_iff, hV]; exact ⟨by linarith, hr⟩
  · exact (show x ≤ 2 by linarith [(hsub hx).2])

/-- **The hypotheses of every form of Corollary 4.68 on the line**: `S = {0}`, `U₁ = ℝ`,
`U₂ = ]-1, 1[ ∪ ]2, 3[`, `u₁ = 0`, `u₂ = disSol₂`. The line is globally hyperbolic, tarentin and
causally arc-connected, `{0}` is acausal, splits `ℝ`, is Cauchy in `ℝ`, the slabs are compact; a
common development exists (`]-1/2, 1/2[`); every common development lies in `]-1, 1[`, so the
frontier hypothesis holds and the restart gives `]-1, 1[`; the solutions disagree at `5/2`. -/
theorem data_4_68 :
    timelikeLine.GloballyHyperbolicOn ⊤ ∧ timelikeLine.TarentinOn ⊤ ∧
      timelikeLine.IsAcausalOn ⊤ ({0} : Set ℝ) ∧ timelikeLine.SplitBy ⊤ ({0} : Set ℝ) ∧
      timelikeLine.CompactSlabs ⊤ ({0} : Set ℝ) ∧
      timelikeLine.IsCauchySurfaceOn ⊤ ({0} : Set ℝ) ∧ timelikeLine.CausallyArcConnectedOn ⊤ ∧
      (∃ V, timelikeLine.IsCommonDevelopment ({0} : Set ℝ) ⊤ disU₂ disAgree V) ∧
      (∀ V, timelikeLine.IsCommonDevelopment ({0} : Set ℝ) ⊤ disU₂ disAgree V →
        timelikeLine.FrontierStaysIn ⊤ {0} V (((⊤ : Opens ℝ) ⊓ disU₂ : Opens ℝ) : Set ℝ)) ∧
      (∀ V, timelikeLine.IsCommonDevelopment ({0} : Set ℝ) ⊤ disU₂ disAgree V →
        timelikeLine.SliceRestart ⊤ {0} V (((⊤ : Opens ℝ) ⊓ disU₂ : Opens ℝ) : Set ℝ)
          (fun _ => ∃ V', timelikeLine.IsCommonDevelopment ({0} : Set ℝ) ⊤ disU₂ disAgree V' ∧
            V < V')) ∧
      ¬ disAgree (⊤ ⊓ disU₂) ∧
      (∃ x ∈ ((⊤ : Opens ℝ) ⊓ disU₂ : Opens ℝ), (fun _ : ℝ => (0 : ℝ)) x ≠ disSol₂ x) := by
  have hmem : (5 / 2 : ℝ) ∈ ((⊤ : Opens ℝ) ⊓ disU₂ : Opens ℝ) := by
    rw [← SetLike.mem_coe, coe_top_inf_disU₂]; right; constructor <;> norm_num
  have hne : (fun _ : ℝ => (0 : ℝ)) (5 / 2) ≠ disSol₂ (5 / 2) := by norm_num [disSol₂]
  refine ⟨timelikeLine_globallyHyperbolic, tarentinOn_top.2 timelikeLine_tarentin, ?_, ?_,
    GloballyHyperbolicOn.compactSlabs_singleton timelikeLine_globallyHyperbolic 0,
    timelikeLine_isCauchySurface_zero, timelikeLine_causallyArcConnected,
    ⟨⟨Ioo (-(1 / 2)) (1 / 2), isOpen_Ioo⟩, isCommonDevelopment_Ioo one_half_pos
      one_half_lt_one.le rfl⟩, ?_, ?_, fun h => hne (h hmem), ⟨5 / 2, hmem, hne⟩⟩
  · intro x hx y hy _
    rw [mem_singleton_iff] at hx hy
    rw [hx, hy]
  · intro q _
    rcases le_total 0 q with h | h
    · exact Or.inl ⟨0, rfl, timelikeLine_le_top.2 h⟩
    · exact Or.inr ⟨0, rfl, timelikeLine_le_top.2 h⟩
  · -- `FrontierStaysIn`: a frontier point `q` in `U₁ ∩ U₂` is in `]-1, 1[`, and `[0, q]`,
    -- `[q, 0]` lie in `]-1, 1[`
    intro V hV q hq
    have hq' := mem_Ioo_of_mem_frontier hV hq
    rw [coe_top_inf_disU₂]
    refine ⟨fun _ z hz => ?_, fun _ z hz => ?_⟩
    · obtain ⟨⟨hzq, ⟨_, rfl, h0z⟩⟩, -⟩ := hz
      rw [Precausality.mem_Jminus_singleton, timelikeLine_le_top] at hzq
      rw [timelikeLine_le_top] at h0z
      exact Or.inl ⟨by linarith, hzq.trans_lt hq'.2⟩
    · obtain ⟨⟨hqz, ⟨_, rfl, hz0⟩⟩, -⟩ := hz
      rw [Precausality.mem_Jplus_singleton, timelikeLine_le_top] at hqz
      rw [timelikeLine_le_top] at hz0
      exact Or.inl ⟨hq'.1.trans_le hqz, by linarith⟩
  · -- `SliceRestart`: `V' = ]-1, 1[`, which contains the frontier point `p` while `V` does not
    intro V hV p hp _
    refine ⟨⟨Ioo (-1) 1, isOpen_Ioo⟩, isCommonDevelopment_Ioo one_pos le_rfl rfl,
      lt_of_le_of_ne (subset_Ioo_of_isCommonDevelopment hV) fun hVeq => ?_⟩
    have hpV : p ∈ (V : Set ℝ) := by rw [hVeq]; exact mem_Ioo_of_mem_frontier hV hp
    have := hp.1
    rw [V.isOpen.frontier_eq] at this
    exact this.2 hpV

/-- **The restart of the 4.68 witness is not vacuous**: at the common development
`]-1/2, 1/2[`, the frontier point `1/2` lies in `U₁ ∩ U₂`, to the future of `0`, and is a spacelike
boundary point (the premise of `hstay` and of `hstep` is met there). -/
theorem restart_premise_4_68 :
    timelikeLine.IsCommonDevelopment ({0} : Set ℝ) ⊤ disU₂ disAgree
        ⟨Ioo (-(1 / 2)) (1 / 2), isOpen_Ioo⟩ ∧
      (1 / 2 : ℝ) ∈ frontier (Ioo (-(1 / 2)) (1 / 2) : Set ℝ) ∩
        (((⊤ : Opens ℝ) ⊓ disU₂ : Opens ℝ) : Set ℝ) ∧
      (1 / 2 : ℝ) ∈ timelikeLine.Jplus ⊤ ({0} : Set ℝ) ∧
      timelikeLine.IsSpacelikeBoundaryPoint ⊤ {0} (frontier (Ioo (-(1 / 2)) (1 / 2) : Set ℝ))
        (1 / 2) := by
  have hfr : frontier (Ioo (-(1 / 2)) (1 / 2) : Set ℝ) = {-(1 / 2), 1 / 2} :=
    frontier_Ioo (by norm_num)
  refine ⟨isCommonDevelopment_Ioo one_half_pos one_half_lt_one.le rfl,
    ⟨by rw [hfr]; exact Or.inr rfl, by rw [coe_top_inf_disU₂]; left; constructor <;> norm_num⟩,
    ⟨0, rfl, timelikeLine_le_top.2 (by norm_num)⟩, Or.inl ?_⟩
  rw [hfr]
  ext z
  simp only [mem_inter_iff, Precausality.mem_Jminus_singleton, Precausality.mem_Jplus,
    mem_singleton_iff, exists_eq_left, timelikeLine_le_top, mem_insert_iff]
  constructor
  · rintro ⟨⟨-, h | h⟩, h0⟩
    · rw [h] at h0; norm_num at h0
    · exact h
  · rintro rfl
    norm_num

/-- **The witness's `U₂` is a development for no causality**: `{0}` is a Cauchy surface of
`]-1, 1[ ∪ ]2, 3[` for no causality of `ℝ` (it would be preconnected). -/
theorem not_isCauchySurfaceOn_disU₂ (C₂ : Causality ℝ) :
    ¬ C₂.IsCauchySurfaceOn disU₂ ({0} : Set ℝ) := by
  intro h
  have h0 : ({0} : Set ℝ) ⊆ disU₂ := by
    rw [singleton_subset_iff]; exact Or.inl ⟨by norm_num, by norm_num⟩
  have hc := isPreconnected_iff_ordConnected.1
    (isPreconnected_of_isCauchySurfaceOn_of_t1_secondCountable isPreconnected_singleton h0 h)
  have h52 : (5 / 2 : ℝ) ∈ (disU₂ : Set ℝ) := Or.inr ⟨by norm_num, by norm_num⟩
  have h32 := hc.out (h0 rfl) h52 (show (3 / 2 : ℝ) ∈ Icc 0 (5 / 2) by constructor <;> norm_num)
  rcases h32 with h | h
  · exact absurd h.2 (by norm_num)
  · exact absurd h.1 (by norm_num)

end ErsWitness

open Causality ErsWitness

/-- **A witness of `ers_corollary_4_68`** on the data of `ErsWitness.data_4_68`. -/
theorem timelikeLine_ers_corollary_4_68 :
    ¬ IsPreconnected (((⊤ : Opens ℝ) ⊓ disU₂ : Opens ℝ) : Set ℝ) := by
  obtain ⟨hG, hT, hac, hsplit, hK, -, -, hlocal, hstay, hstep, hdis, -⟩ := data_4_68
  exact ers_corollary_4_68 (agreementGlues_eqOn _ _) hG hT hac hsplit hK hlocal hstay hstep hdis

/-- **A witness of `ers_corollary_4_68_eqOn`** on the data of `ErsWitness.data_4_68`. -/
theorem timelikeLine_ers_corollary_4_68_eqOn :
    ¬ IsPreconnected (((⊤ : Opens ℝ) ⊓ disU₂ : Opens ℝ) : Set ℝ) := by
  obtain ⟨hG, hT, hac, hsplit, hK, -, -, hlocal, hstay, hstep, -, hx⟩ := data_4_68
  exact ers_corollary_4_68_eqOn (u₁ := fun _ : ℝ => (0 : ℝ)) (u₂ := disSol₂) hG hT hac hsplit hK
    hlocal hstay hstep hx

/-- **A witness of `ers_corollary_4_68_of_isCauchySurfaceOn_secondCountable`** on the data of
`ErsWitness.data_4_68`. -/
theorem timelikeLine_ers_corollary_4_68_of_isCauchySurfaceOn_secondCountable :
    ¬ IsPreconnected (((⊤ : Opens ℝ) ⊓ disU₂ : Opens ℝ) : Set ℝ) := by
  obtain ⟨hG, hT, -, -, hK, hC₁, harc, hlocal, hstay, hstep, hdis, -⟩ := data_4_68
  exact ers_corollary_4_68_of_isCauchySurfaceOn_secondCountable (agreementGlues_eqOn _ _) hG hT
    hC₁ harc hK hlocal hstay hstep hdis

/-- **A witness of `ers_corollary_4_68_eqOn_of_isCauchySurfaceOn_secondCountable`** on the data
of `ErsWitness.data_4_68`. -/
theorem timelikeLine_ers_corollary_4_68_eqOn_of_isCauchySurfaceOn_secondCountable :
    ¬ IsPreconnected (((⊤ : Opens ℝ) ⊓ disU₂ : Opens ℝ) : Set ℝ) := by
  obtain ⟨hG, hT, -, -, hK, hC₁, harc, hlocal, hstay, hstep, -, hx⟩ := data_4_68
  exact ers_corollary_4_68_eqOn_of_isCauchySurfaceOn_secondCountable
    (u₁ := fun _ : ℝ => (0 : ℝ)) (u₂ := disSol₂) hG hT hC₁ harc hK hlocal hstay hstep hx

/-- **A witness of `ers_corollary_4_68_of_isCauchySurfaceOn_secondCountable_noArc`** on the data
of `ErsWitness.data_4_68`. -/
theorem timelikeLine_ers_corollary_4_68_of_isCauchySurfaceOn_secondCountable_noArc :
    ¬ IsPreconnected (((⊤ : Opens ℝ) ⊓ disU₂ : Opens ℝ) : Set ℝ) := by
  obtain ⟨hG, hT, -, -, hK, hC₁, -, hlocal, hstay, hstep, hdis, -⟩ := data_4_68
  exact ers_corollary_4_68_of_isCauchySurfaceOn_secondCountable_noArc (agreementGlues_eqOn _ _)
    hG hT hC₁ hK hlocal hstay hstep hdis

/-- **A witness of `ers_corollary_4_68_eqOn_of_isCauchySurfaceOn_secondCountable_noArc`** on the
data of `ErsWitness.data_4_68`. -/
theorem timelikeLine_ers_corollary_4_68_eqOn_of_isCauchySurfaceOn_secondCountable_noArc :
    ¬ IsPreconnected (((⊤ : Opens ℝ) ⊓ disU₂ : Opens ℝ) : Set ℝ) := by
  obtain ⟨hG, hT, -, -, hK, hC₁, -, hlocal, hstay, hstep, -, hx⟩ := data_4_68
  exact ers_corollary_4_68_eqOn_of_isCauchySurfaceOn_secondCountable_noArc
    (u₁ := fun _ : ℝ => (0 : ℝ)) (u₂ := disSol₂) hG hT hC₁ hK hlocal hstay hstep hx

/-! ## 4. Corollary 4.69 -/

open ErsNoArcWitness

/-- **A witness of `ers_corollary_4_69`**: `U₁ = ℝ`, `U₂ = ]-1, 1[`, `u₁ = id`, `u₂` the clamp,
`C₂ = C` the line (`ErsNoArcWitness.data`); `hthrough₂` by
`inextensibleThrough_of_t1_secondCountable`. The solutions agree on `U₂`. -/
theorem timelikeLine_ers_corollary_4_69 : clampAgree ersWitnessIoo := by
  obtain ⟨hG, hT, hC₁, hC₂, hK, -, hlocal, hstay, hstep⟩ :=
    ErsNoArcWitness.data (D := timelikeLine) (fun h => h.1) fun h => h
  exact ers_corollary_4_69 (C₂ := timelikeLine) agreementGlues_clampAgree hG
    (tarentinOn_top.1 hT) timelikeLine_isAcausal_zero (splitBy_of_t1_secondCountable hC₁) hK
    isPreconnected_singleton hC₂ (inextensibleThrough_of_t1_secondCountable _ _) hlocal
    (by simpa only [top_inf_eq] using hstay) (by simpa only [top_inf_eq] using hstep)

/-- **A witness of `ers_corollary_4_69_secondCountable`** on the same data. -/
theorem timelikeLine_ers_corollary_4_69_secondCountable : clampAgree ersWitnessIoo := by
  obtain ⟨hG, hT, hC₁, hC₂, hK, -, hlocal, hstay, hstep⟩ :=
    ErsNoArcWitness.data (D := timelikeLine) (fun h => h.1) fun h => h
  exact ers_corollary_4_69_secondCountable (C₂ := timelikeLine) agreementGlues_clampAgree hG
    (tarentinOn_top.1 hT) timelikeLine_isAcausal_zero (splitBy_of_t1_secondCountable hC₁) hK
    isPreconnected_singleton hC₂ hlocal (by simpa only [top_inf_eq] using hstay)
    (by simpa only [top_inf_eq] using hstep)

/-- **A witness of `ers_corollary_4_69_of_isCauchySurface_secondCountable`** on the same data. -/
theorem timelikeLine_ers_corollary_4_69_of_isCauchySurface_secondCountable :
    clampAgree ersWitnessIoo := by
  obtain ⟨hG, hT, hC₁, hC₂, hK, -, hlocal, hstay, hstep⟩ :=
    ErsNoArcWitness.data (D := timelikeLine) (fun h => h.1) fun h => h
  exact ers_corollary_4_69_of_isCauchySurface_secondCountable (C₂ := timelikeLine)
    agreementGlues_clampAgree hG (tarentinOn_top.1 hT) hC₁ timelikeLine_causallyArcConnected hK
    isPreconnected_singleton hC₂ hlocal (by simpa only [top_inf_eq] using hstay)
    (by simpa only [top_inf_eq] using hstep)

/-! ## 5. Corollary 4.71 -/

/-- **A witness of `ers_corollary_4_71`**: the data of `ErsNoArcWitness.data`, `Cτ = C₂ = C` the
line (causal), `T`'s curve through `x` the identity of `ℝ`, a curve meets `{0}` at most once, and
the nestings `hn₁`, `hn₂` by `InextensibleNestedOn.refl`. The solutions agree on `U₁ ∩ U₂`. -/
theorem timelikeLine_ers_corollary_4_71 : clampAgree (⊤ ⊓ ersWitnessIoo) := by
  obtain ⟨hG, hT, hC₁, hC₂, hK, -, hlocal, hstay, hstep⟩ :=
    ErsNoArcWitness.data (D := timelikeLine) (fun h => h.1) fun h => h
  have hGH : timelikeLine.GloballyHyperbolic := hG
  have hτ : timelikeLine.IsCausal := by causal_ladder
  have honce : ∀ (I : Set ℝ) (γ : ℝ → ℝ), timelikeLine.Inextensible ⊤ I γ →
      ∀ y ∈ γ '' I ∩ ({0} : Set ℝ), ∀ z ∈ γ '' I ∩ ({0} : Set ℝ), y = z :=
    fun _ _ _ _ hy _ hz => (mem_singleton_iff.1 hy.2).trans (mem_singleton_iff.1 hz.2).symm
  exact ers_corollary_4_71 (Cτ := timelikeLine) (C₂ := timelikeLine) agreementGlues_clampAgree
    hG hT (timelikeLine_isAcausal_zero.isAcausalOn ⊤) (splitBy_of_t1_secondCountable hC₁) hK
    isPreconnected_singleton hC₁ hC₂ hτ
    (fun x _ => ⟨univ, id, timelikeLine_inextensible_id, x, trivial, rfl⟩) honce
    (InextensibleNestedOn.refl _ _) (InextensibleNestedOn.refl _ _) hlocal hstay hstep

/-- **A witness of `ers_corollary_4_71_secondCountable`** on the same data. -/
theorem timelikeLine_ers_corollary_4_71_secondCountable : clampAgree (⊤ ⊓ ersWitnessIoo) := by
  obtain ⟨hG, hT, hC₁, hC₂, hK, -, hlocal, hstay, hstep⟩ :=
    ErsNoArcWitness.data (D := timelikeLine) (fun h => h.1) fun h => h
  have hGH : timelikeLine.GloballyHyperbolic := hG
  have hτ : timelikeLine.IsCausal := by causal_ladder
  have honce : ∀ (I : Set ℝ) (γ : ℝ → ℝ), timelikeLine.Inextensible ⊤ I γ →
      ∀ y ∈ γ '' I ∩ ({0} : Set ℝ), ∀ z ∈ γ '' I ∩ ({0} : Set ℝ), y = z :=
    fun _ _ _ _ hy _ hz => (mem_singleton_iff.1 hy.2).trans (mem_singleton_iff.1 hz.2).symm
  exact ers_corollary_4_71_secondCountable (Cτ := timelikeLine) (C₂ := timelikeLine)
    agreementGlues_clampAgree hG hT (timelikeLine_isAcausal_zero.isAcausalOn ⊤) hK
    isPreconnected_singleton hC₁ hC₂ hτ honce (InextensibleNestedOn.refl _ _)
    (InextensibleNestedOn.refl _ _) hlocal hstay hstep

/-- **A witness of `ers_corollary_4_71_of_isCauchySurfaceOn_secondCountable`** on the same data. -/
theorem timelikeLine_ers_corollary_4_71_of_isCauchySurfaceOn_secondCountable :
    clampAgree (⊤ ⊓ ersWitnessIoo) := by
  obtain ⟨hG, hT, hC₁, hC₂, hK, -, hlocal, hstay, hstep⟩ :=
    ErsNoArcWitness.data (D := timelikeLine) (fun h => h.1) fun h => h
  have hGH : timelikeLine.GloballyHyperbolic := hG
  have hτ : timelikeLine.IsCausal := by causal_ladder
  have honce : ∀ (I : Set ℝ) (γ : ℝ → ℝ), timelikeLine.Inextensible ⊤ I γ →
      ∀ y ∈ γ '' I ∩ ({0} : Set ℝ), ∀ z ∈ γ '' I ∩ ({0} : Set ℝ), y = z :=
    fun _ _ _ _ hy _ hz => (mem_singleton_iff.1 hy.2).trans (mem_singleton_iff.1 hz.2).symm
  exact ers_corollary_4_71_of_isCauchySurfaceOn_secondCountable (Cτ := timelikeLine)
    (C₂ := timelikeLine) agreementGlues_clampAgree hG hT timelikeLine_causallyArcConnected hK
    isPreconnected_singleton hC₁ hC₂ hτ honce (InextensibleNestedOn.refl _ _)
    (InextensibleNestedOn.refl _ _) hlocal hstay hstep

/-! ## 6. Theorem 4.82 -/

namespace ErsWitness

/-- The smaller development of the 4.82 witness: `]-1/2, 1/2[`. -/
def halfIoo : Opens ℝ := ⟨Ioo (-(1 / 2)) (1 / 2), isOpen_Ioo⟩

/-- The two developments of the 4.82 witness: `dom true = ]-1, 1[` (the maximal one, `i₁`) and
`dom false = ]-1/2, 1/2[`. -/
def dom82 : Bool → Opens ℝ := fun b => cond b ersWitnessIoo halfIoo

theorem coe_dom82_true : (dom82 true : Set ℝ) = Ioo (-1) 1 := rfl

theorem coe_dom82_false : (dom82 false : Set ℝ) = Ioo (-(1 / 2)) (1 / 2) := rfl

/-- Both developments of the 4.82 witness lie in `dom true`. -/
theorem dom82_le (i : Bool) : dom82 i ≤ dom82 true := by
  cases i
  · intro x hx
    have hx' : x ∈ Ioo (-(1 / 2) : ℝ) (1 / 2) := hx
    show x ∈ Ioo (-1 : ℝ) 1
    exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
  · exact le_rfl

theorem three_quarters_mem_dom82_true : (3 / 4 : ℝ) ∈ dom82 true :=
  show (3 / 4 : ℝ) ∈ Ioo (-1 : ℝ) 1 by constructor <;> norm_num

theorem three_quarters_not_mem_dom82_false : (3 / 4 : ℝ) ∉ dom82 false := fun h =>
  absurd (show (3 / 4 : ℝ) ∈ Ioo (-(1 / 2) : ℝ) (1 / 2) from h).2 (by norm_num)

/-- **The hypotheses of every form of Theorem 4.82 on the line**: `ι = Bool`, `dom82`, every
`cau i` the timelike line, `S = {0}`, `s₀ = 0`, `i₁ = true`. `dom true` is maximal and strictly
larger than `dom false`; each development is preconnected, globally hyperbolic, tarentin, has
`{0}` as Cauchy surface (so it splits), compact slabs, `J^∓(x)` relatively closed, and
`closure S ∩ dom i ⊆ S`; `dom true` has a one-sided boundary off `closure S`; the restart holds
(vacuously, `ers_theorem_4_82_hstep_of_le`). -/
theorem data_4_82 :
    dom82 false < dom82 true ∧
      (∀ i, ({0} : Set ℝ) ⊆ dom82 i) ∧
      (∀ i, dom82 true ≤ dom82 i → dom82 i = dom82 true) ∧
      (∀ i, IsPreconnected (dom82 i : Set ℝ)) ∧
      (∀ i, timelikeLine.GloballyHyperbolicOn (dom82 i)) ∧
      (∀ i, timelikeLine.TarentinOn (dom82 i)) ∧
      (∀ i, timelikeLine.IsCauchySurfaceOn (dom82 i) ({0} : Set ℝ)) ∧
      (∀ i, timelikeLine.SplitBy (dom82 i) ({0} : Set ℝ)) ∧
      (∀ i, timelikeLine.CompactSlabs (dom82 i) ({0} : Set ℝ)) ∧
      (∀ i, ∀ x ∈ dom82 i, closure (timelikeLine.Jminus (dom82 i) {x}) ∩ dom82 i ⊆
        timelikeLine.Jminus (dom82 i) {x}) ∧
      (∀ i, ∀ x ∈ dom82 i, closure (timelikeLine.Jplus (dom82 i) {x}) ∩ dom82 i ⊆
        timelikeLine.Jplus (dom82 i) {x}) ∧
      (∀ i, closure ({0} : Set ℝ) ∩ dom82 i ⊆ {0}) ∧
      OneSidedBoundary (dom82 true) (closure ({0} : Set ℝ)) ∧
      (∀ i, timelikeLine.SliceRestart (dom82 i) {0}
        (connectedComponentIn ((dom82 true : Set ℝ) ∩ dom82 i) 0) (dom82 i)
        (fun p => (∃ V ∈ 𝓝 p, V ⊆ dom82 i ∧
          V ∩ dom82 true ⊆ connectedComponentIn ((dom82 true : Set ℝ) ∩ dom82 i) 0) →
          ∃ j, dom82 true < dom82 j)) := by
  have hSU : ∀ i, ({0} : Set ℝ) ⊆ dom82 i := by
    intro i
    rw [singleton_subset_iff]
    cases i
    · show (0 : ℝ) ∈ Ioo (-(1 / 2) : ℝ) (1 / 2); constructor <;> norm_num
    · show (0 : ℝ) ∈ Ioo (-1 : ℝ) 1; constructor <;> norm_num
  have hconn : ∀ i, IsPreconnected (dom82 i : Set ℝ) := by
    intro i
    cases i
    · rw [coe_dom82_false]; exact isPreconnected_Ioo
    · rw [coe_dom82_true]; exact isPreconnected_Ioo
  have hG : ∀ i, timelikeLine.GloballyHyperbolicOn (dom82 i) :=
    fun i => timelikeLine_globallyHyperbolicOn _
  have hT : ∀ i, timelikeLine.TarentinOn (dom82 i) := fun i => timelikeLine_tarentinOn _
  have hcauchy : ∀ i, timelikeLine.IsCauchySurfaceOn (dom82 i) ({0} : Set ℝ) := by
    intro i
    cases i
    · exact timelikeLine_isCauchySurfaceOn_Ioo one_half_pos coe_dom82_false
    · exact timelikeLine_isCauchySurfaceOn_Ioo one_pos coe_dom82_true
  refine ⟨lt_of_le_of_ne (dom82_le false) fun h => three_quarters_not_mem_dom82_false
      (h ▸ three_quarters_mem_dom82_true), hSU, ?_, hconn, hG, hT, hcauchy,
    fun i => splitBy_of_t1_secondCountable (hcauchy i),
    fun i => (hG i).compactSlabs_singleton 0,
    fun i => (hG i).closure_Jminus_inter_subset (hT i),
    fun i => (hG i).closure_Jplus_inter_subset (hT i),
    fun i => by rw [closure_singleton]; exact inter_subset_left,
    oneSidedBoundary_of_ordConnected (by rw [coe_dom82_true]; exact ordConnected_Ioo) _,
    ers_theorem_4_82_hstep_of_le dom82 (fun _ => timelikeLine) (mem_singleton 0) true hSU hconn
      dom82_le⟩
  intro i h
  cases i
  · exact absurd (h three_quarters_mem_dom82_true) three_quarters_not_mem_dom82_false
  · rfl

/-- **The one-sided boundary hypothesis of the 4.82 witness is not vacuous**: the frontier of
`dom true` off `closure S` is `{-1, 1}`. -/
theorem frontier_dom82_true_diff :
    frontier (dom82 true : Set ℝ) \ closure ({0} : Set ℝ) = {-1, 1} := by
  rw [coe_dom82_true, frontier_Ioo (by norm_num), closure_singleton]
  ext z
  simp only [Set.mem_sdiff, mem_insert_iff, mem_singleton_iff]
  constructor
  · exact fun h => h.1
  · rintro (rfl | rfl) <;> norm_num

end ErsWitness

/-- **A witness of `ers_theorem_4_82`** (the strict original, `Causal.NestedCausalities`) on the
data of `ErsWitness.data_4_82`: every development lies in the maximal one. -/
theorem timelikeLine_ers_theorem_4_82 : ∀ i, dom82 i ≤ dom82 true := by
  obtain ⟨-, hSU, hmax, hconn, hG, -, -, hsplit, hK, hJm, hJp, hSclosed, honesided, hstep⟩ :=
    data_4_82
  exact ers_theorem_4_82 dom82 (fun _ => timelikeLine) (mem_singleton (0 : ℝ)) true hSU hmax hconn
    (fun i => (hG i).1) hsplit hJm hJp (fun i q => (hK i q).1) (fun i q => (hK i q).2) hSclosed
    honesided hstep

/-- **A witness of `ers_theorem_4_82_of_oneSidedBoundary`** on the data of
`ErsWitness.data_4_82`. -/
theorem timelikeLine_ers_theorem_4_82_of_oneSidedBoundary : ∀ i, dom82 i ≤ dom82 true := by
  obtain ⟨-, hSU, hmax, hconn, hG, -, -, hsplit, hK, hJm, hJp, hSclosed, honesided, hstep⟩ :=
    data_4_82
  exact ers_theorem_4_82_of_oneSidedBoundary dom82 (fun _ => timelikeLine) (mem_singleton (0 : ℝ))
    true hSU hmax hconn (fun i => (hG i).1) hsplit hJm hJp (fun i q => (hK i q).1)
    (fun i q => (hK i q).2) hSclosed honesided hstep

/-- **A witness of `ers_theorem_4_82_of_sliceRestart`** on the data of `ErsWitness.data_4_82`. -/
theorem timelikeLine_ers_theorem_4_82_of_sliceRestart : ∀ i, dom82 i ≤ dom82 true := by
  obtain ⟨-, hSU, hmax, hconn, hG, -, -, hsplit, hK, hJm, hJp, hSclosed, honesided, hstep⟩ :=
    data_4_82
  exact ers_theorem_4_82_of_sliceRestart dom82 (fun _ => timelikeLine) (mem_singleton (0 : ℝ))
    true hSU hmax hconn (fun i => (hG i).1) hsplit hJm hJp hK hSclosed honesided hstep

/-- **A witness of `ers_theorem_4_82_of_globallyHyperbolicOn`** on the data of
`ErsWitness.data_4_82`. -/
theorem timelikeLine_ers_theorem_4_82_of_globallyHyperbolicOn : ∀ i, dom82 i ≤ dom82 true := by
  obtain ⟨-, hSU, hmax, hconn, hG, hT, -, hsplit, hK, -, -, hSclosed, honesided, hstep⟩ :=
    data_4_82
  exact ers_theorem_4_82_of_globallyHyperbolicOn dom82 (fun _ => timelikeLine)
    (mem_singleton (0 : ℝ)) true hSU hmax hconn hG hT hsplit hK hSclosed honesided hstep

/-- **A witness of `ers_theorem_4_82_of_isCauchySurfaceOn_secondCountable`** on the data of
`ErsWitness.data_4_82`. -/
theorem timelikeLine_ers_theorem_4_82_of_isCauchySurfaceOn_secondCountable :
    ∀ i, dom82 i ≤ dom82 true := by
  obtain ⟨-, hSU, hmax, hconn, hG, hT, hcauchy, -, hK, -, -, hSclosed, honesided, hstep⟩ :=
    data_4_82
  exact ers_theorem_4_82_of_isCauchySurfaceOn_secondCountable dom82 (fun _ => timelikeLine)
    (mem_singleton (0 : ℝ)) true hSU hmax hconn hG hT hcauchy hK hSclosed honesided hstep

end Causal
