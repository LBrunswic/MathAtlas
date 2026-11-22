import Causal.GluingModels.Tools
import Causal.CBG.CausalConvex
import Causal.PushUpNotOpen
import Causal.ChronalNeighbourBridge
import Causal.DeuxPushup
import Causal.Morphism
import Causal.LinesReachable
import Causal.MeasureRemarks
import Causal.Chains
import Causal.CausalIsoInvariance
import Causal.LineDevelopment
import Causal.Galileo
import Causal.CBG.SubExtensionAbstract
import Causal.GHWithoutTarentin

/-!
# Gluing inventory (DEC-167), ETT layer: the concrete causalities that do not glue

No paper label is certified by this file. Under DEC-167 every ETT causality is absolutely minimal
(`def:topological_space_causality_absolutely`, `ETT.tex:397`); the objects below are causalities of
the library (no gluing axiom, kb/0014) that are **not absolutely minimal on `M`**, hence not in
the hereditary form either (`not_forall_of_not_absolutelyMinimal`). Under the field of
`T-abs-gluing-field` they stop being causalities; what becomes of them is OQ-96.

* Already refuted in the library, restated in both forms: `gateLine`, `jumpLine`, `globalLine`,
  `deuxPushup`, `timelikeLineTop`, `DensWitness.densCausality`, `DensWitness.bigCausality`.
* **Refuted here**:
  - `galileoOn X` whenever `X` retracts continuously onto `ℝ` (`ℝ` itself, every `ℝⁿ`, `n ≥ 1`):
    **Galileo's spacetime of `ex:causalities_lines` item 4 (`ETT.tex:273`) is not absolutely
    minimal**, so it is no causality under DEC-167 (`galileo_not_minimal`). The witness is an open
    set with a cup-shaped wall: `p ≪_U q` through a detour below the wall, while the cover
    `{t > 1/4, t < 1/2}` traps every chain from `p` in the cup.
  - `pointedLine`, `pointedLineMR` (`rem:K_neq_I`): only `0` has a future, and the cover
    `{t < 1, t > 0}` has no member containing `[0, 2]`.
  - `doubledLine` (ETT time functions, `Causal.CausalIsoInvariance`): the cover by the two
    sheets.
  - the `Causality.ofRelation` objects `puncturedPlane` (`rem:K_plongement_hypotheses`),
    `totalLine`, and `orderLine`, `allRelated` (same shape): a non-local relation is not glued
    (`Tools.not_absolutelyMinimal_of_le_of_ne`).
  - the discrete ones `bowtie`, `fan`, `linearCausality ℕ` (`def:causal_chain`): on a discrete
    space an absolutely minimal `≤` is the diagonal (`AbsolutelyMinimalOn.eq_of_discrete`).
  - `DensWitness.wideCausality`, `DensWitness.far2Causality`: they contain the density
    causality's relation `0 ≤_{gapSet} 1`.
  - `arcCausality γ` for a discontinuous arc (`arcCausality_jumpArc_not_minimal`): the definition
    takes any `γ`, its gluing holds for continuous arcs (`arcCausality_absolutelyMinimalOn`).

## Hypothesis checklist

| hypothesis | here |
|---|---|
| second countable, Hausdorff | ✓ every refuted object lives on such a space (the bowtie and `ℕ` are discrete) |
| Galileo: `ℝ^{n+1}`, `n` unrestricted | ⚠ `n ≥ 1` (a continuous retraction `X → ℝ`); for `n = 0` it glues (`GluingModels.galileo_zero_hereditary`, module `Minimal`) |

## SCOPE (disclosed)

* No definition changes. Whether these objects are restated for precausalities or retired is
  OQ-96, not decided here.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

namespace GluingModels

open Set TopologicalSpace Topology Relation

/-! ### Refuted in the library, restated in both forms -/

theorem gateLine_not_minimal : ¬ gateLine.AbsolutelyMinimal :=
  not_absolutelyMinimal_of_not_top gateLine_not_absolutelyMinimalOn

theorem gateLine_not_hereditary : ¬ ∀ W, gateLine.AbsolutelyMinimalOn W :=
  not_forall_of_not_absolutelyMinimal gateLine_not_minimal

theorem jumpLine_not_hereditary : ¬ ∀ W, jumpLine.AbsolutelyMinimalOn W :=
  not_forall_of_not_absolutelyMinimal jumpLine_not_absolutelyMinimal

theorem globalLine_not_hereditary : ¬ ∀ W, globalLine.AbsolutelyMinimalOn W :=
  not_forall_of_not_absolutelyMinimal globalLine_not_absolutelyMinimal

theorem deuxPushup_not_hereditary : ¬ ∀ W, deuxPushup.AbsolutelyMinimalOn W :=
  not_forall_of_not_absolutelyMinimal deuxPushup_not_absolutelyMinimal

theorem timelikeLineTop_not_hereditary : ¬ ∀ W, timelikeLineTop.AbsolutelyMinimalOn W :=
  not_forall_of_not_absolutelyMinimal timelikeLineTop_not_absolutelyMinimal

theorem densCausality_not_minimal : ¬ DensWitness.densCausality.AbsolutelyMinimal :=
  not_absolutelyMinimal_of_not_top DensWitness.not_absolutelyMinimalOn_witness.1

theorem bigCausality_not_minimal : ¬ DensWitness.bigCausality.AbsolutelyMinimal :=
  not_absolutelyMinimal_of_not_top DensWitness.not_absolutelyMinimalOn_witness.2

/-- The wide causality relates `0` to `1` in `gapSet`, through the density causality. -/
theorem wideCausality_not_minimal : ¬ DensWitness.wideCausality.AbsolutelyMinimal :=
  not_absolutelyMinimal_of_not_top
    (DensWitness.not_absolutelyMinimalOn_of_le_gapSet (Or.inl DensWitness.densCausality_le_gapSet))

/-- The far causality relates `0` to `1` in `gapSet`, through the density causality. -/
theorem far2Causality_not_minimal : ¬ DensWitness.far2Causality.AbsolutelyMinimal :=
  not_absolutelyMinimal_of_not_top
    (DensWitness.not_absolutelyMinimalOn_of_le_gapSet (Or.inl DensWitness.densCausality_le_gapSet))

/-! ### The pointed line -/

section Pointed

/-- The cover `{t < 1, t > 0}` of `ℝ`. -/
theorem pointedCover : ∀ z ∈ (⊤ : Opens ℝ),
    ∃ O ∈ ({⟨Iio 1, isOpen_Iio⟩, ⟨Ioi 0, isOpen_Ioi⟩} : Set (Opens ℝ)), z ∈ O := by
  intro z _
  by_cases hz : z < 1
  · exact ⟨_, Or.inl rfl, hz⟩
  · exact ⟨_, Or.inr rfl, show (0 : ℝ) < z by linarith [not_lt.1 hz]⟩

/-- A relation family with the shape of the pointed line's: only `0` has a non-trivial future,
along a segment `[0, y]` of the open set. Over the cover `{t < 1, t > 0}` a chain from `0`
stays below `1`. -/
theorem pointed_chain_lt_one {r : Opens ℝ → ℝ → ℝ → Prop}
    (hr : ∀ {N : Opens ℝ} {a b : ℝ}, r N a b → (a = b ∧ a ∈ N) ∨ (a = 0 ∧ 0 < b ∧ Icc 0 b ⊆ N))
    {b : ℝ} (h : TransGen (fun a b => ∃ O ∈ ({⟨Iio 1, isOpen_Iio⟩, ⟨Ioi 0, isOpen_Ioi⟩} :
      Set (Opens ℝ)), r (⊤ ⊓ O) a b) 0 b) : b < 1 := by
  have step : ∀ a b, a < 1 → (∃ O ∈ ({⟨Iio 1, isOpen_Iio⟩, ⟨Ioi 0, isOpen_Ioi⟩} :
      Set (Opens ℝ)), r (⊤ ⊓ O) a b) → b < 1 := by
    rintro a b ha ⟨O, hO, hab⟩
    rcases hr hab with ⟨rfl, -⟩ | ⟨rfl, hb, hsub⟩
    · exact ha
    · rcases hO with rfl | hO
      · exact (hsub (right_mem_Icc.2 hb.le)).2
      · rw [mem_singleton_iff] at hO
        subst hO
        exact (lt_irrefl (0 : ℝ) (hsub (left_mem_Icc.2 hb.le)).2).elim
  induction h with
  | single hab => exact step 0 _ (by norm_num) hab
  | tail _ hbc ih => exact step _ _ ih hbc

/-- **The pointed line is not absolutely minimal** (`rem:K_neq_I`): `0 ≤ 2` in `ℝ`, and no
member of the cover `{t < 1, t > 0}` contains `[0, 2]`. -/
theorem pointedLine_not_minimal : ¬ pointedLine.AbsolutelyMinimal := by
  intro h
  have hc := ((Precausality.absolutelyMinimal_iff.1 h) _ pointedCover ⊤ le_rfl 0 2).1
    (Or.inr ⟨rfl, two_pos, fun _ _ => trivial⟩)
  have := pointed_chain_lt_one (r := pointedLine.le) (fun hab => hab) hc
  norm_num at this

theorem pointedLine_not_hereditary : ¬ ∀ W, pointedLine.AbsolutelyMinimalOn W :=
  not_forall_of_not_absolutelyMinimal pointedLine_not_minimal

/-- The pointed line of `Causal.MeasureRemarks` (the same relations, under a distinct name). -/
theorem pointedLineMR_not_minimal : ¬ pointedLineMR.AbsolutelyMinimal := by
  intro h
  have hc := ((Precausality.absolutelyMinimal_iff.1 h) _ pointedCover ⊤ le_rfl 0 2).1
    (Or.inr ⟨rfl, two_pos, fun _ _ => trivial⟩)
  have := pointed_chain_lt_one (r := pointedLineMR.le) (fun hab => hab) hc
  norm_num at this

theorem pointedLineMR_not_hereditary : ¬ ∀ W, pointedLineMR.AbsolutelyMinimalOn W :=
  not_forall_of_not_absolutelyMinimal pointedLineMR_not_minimal

end Pointed

/-! ### Non-local relations: `ofRelation` and its shape -/

/-- **The punctured null plane is not absolutely minimal** (`rem:K_plongement_hypotheses`):
`(1, 1) ≤ (2, 2)` in every open set containing both. -/
theorem puncturedPlane_not_minimal : ¬ puncturedPlane.AbsolutelyMinimal := by
  let p : PuncturedPlane := ⟨(1, 1), by simp⟩
  let q : PuncturedPlane := ⟨(2, 2), by simp⟩
  have hne : p ≠ q := fun h => by
    have := congrArg (fun z : PuncturedPlane => z.1.1) h
    norm_num [p, q] at this
  have hR : PuncturedPlane.R p q := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [p, q]
  refine not_absolutelyMinimal_of_le_of_ne hne fun V hp hq => ?_
  unfold puncturedPlane
  exact ⟨hp, hq, hR⟩

theorem puncturedPlane_not_hereditary : ¬ ∀ W, puncturedPlane.AbsolutelyMinimalOn W :=
  not_forall_of_not_absolutelyMinimal puncturedPlane_not_minimal

/-- The line on which any two points are related (`Causal.Chains`) is not absolutely minimal. -/
theorem totalLine_not_minimal : ¬ totalLine.AbsolutelyMinimal :=
  not_absolutelyMinimal_of_le_of_ne zero_ne_one fun V h0 h1 => by
    unfold totalLine; exact ⟨h0, h1, trivial⟩

theorem totalLine_not_hereditary : ¬ ∀ W, totalLine.AbsolutelyMinimalOn W :=
  not_forall_of_not_absolutelyMinimal totalLine_not_minimal

/-- The order of `ℝ` restricted to each open set (`Causal.Morphism`, reading (b) of time
functions) is not absolutely minimal. -/
theorem orderLine_not_minimal : ¬ orderLine.AbsolutelyMinimal :=
  not_absolutelyMinimal_of_le_of_ne zero_ne_one fun V h0 h1 =>
    (show (0 : ℝ) ≤ 1 ∧ (0 : ℝ) ∈ V ∧ (1 : ℝ) ∈ V from ⟨zero_le_one, h0, h1⟩)

theorem orderLine_not_hereditary : ¬ ∀ W, orderLine.AbsolutelyMinimalOn W :=
  not_forall_of_not_absolutelyMinimal orderLine_not_minimal

/-- The causality relating every two points (`Causal.LineDevelopment`) is not absolutely minimal
on a `T2.5` space with two points. -/
theorem allRelated_not_minimal {X : Type*} [TopologicalSpace X] [T25Space X] {x y : X}
    (hne : x ≠ y) : ¬ (LineDevelopment.allRelated X).AbsolutelyMinimal :=
  not_absolutelyMinimal_of_le_of_ne hne fun _ hx hy => ⟨hx, hy⟩

/-- The causality relating every two points of the circle `ℝ/Pℤ` (`LineDevelopment.circle_line`,
the witness of `lem:past_BTZ`'s line development) is not absolutely minimal. -/
theorem allRelated_circle_not_minimal (P : ℝ) [Fact (0 < P)] :
    ¬ (LineDevelopment.allRelated (AddCircle P)).AbsolutelyMinimal :=
  allRelated_not_minimal (LineDevelopment.circle_half_ne_zero P)

theorem allRelated_real_not_hereditary :
    ¬ ∀ W, (LineDevelopment.allRelated ℝ).AbsolutelyMinimalOn W :=
  not_forall_of_not_absolutelyMinimal (allRelated_not_minimal zero_ne_one)

/-- The jumping arc `t ↦ 0` for `t < 1/2`, `t ↦ 1` after. -/
noncomputable def jumpArc : Unit → ℝ → ℝ := fun _ t => if t < 1 / 2 then 0 else 1

/-- **`arcCausality γ` needs continuous arcs to glue** (`Causal.GHWithoutTarentin`): along the
jumping arc, `0 ≤_V 1` in every open `V` containing `0` and `1`, a non-local relation. The
definition takes any `γ`; its gluing is proved for continuous arcs only
(`arcCausality_absolutelyMinimalOn`). -/
theorem arcCausality_jumpArc_not_minimal : ¬ (arcCausality jumpArc).AbsolutelyMinimal :=
  not_absolutelyMinimal_of_le_of_ne zero_ne_one fun V h0 h1 => Or.inr
    (TransGen.single ⟨(), 0, 1, le_rfl, zero_le_one, le_rfl, by simp [jumpArc],
      by norm_num [jumpArc], fun r _ => by unfold jumpArc; split_ifs <;> assumption⟩)

/-! ### Discrete spaces -/

/-- The bowtie (`def:causal_chain`) is not absolutely minimal: on a discrete space an absolutely
minimal `≤` is the diagonal, and `a₁ ≤ b₁`. -/
theorem bowtie_not_minimal : ¬ bowtie.AbsolutelyMinimal := by
  intro h
  have := (AbsolutelyMinimalOn.eq_of_discrete (Precausality.absolutelyMinimal_iff.1 h)
    (U := ⊤) (x := Bowtie.a₁) (y := Bowtie.b₁)).1
    (bowtie_le.2 ⟨trivial, trivial, Or.inr ⟨trivial, fun h => h⟩⟩)
  exact Bowtie.noConfusion this

theorem bowtie_not_hereditary : ¬ ∀ W, bowtie.AbsolutelyMinimalOn W :=
  not_forall_of_not_absolutelyMinimal bowtie_not_minimal

/-- The fan on `ℕ` is not absolutely minimal: `0 ≤ 2` on a discrete space. -/
theorem fan_not_minimal : ¬ fan.AbsolutelyMinimal := by
  intro h
  have := (AbsolutelyMinimalOn.eq_of_discrete (Precausality.absolutelyMinimal_iff.1 h)
    (U := ⊤) (x := 0) (y := 2)).1 (fan_le.2 ⟨trivial, trivial, Or.inr (Or.inl rfl)⟩)
  norm_num at this

theorem fan_not_hereditary : ¬ ∀ W, fan.AbsolutelyMinimalOn W :=
  not_forall_of_not_absolutelyMinimal fan_not_minimal

/-- The causality of the order of `ℕ` (`def:causal_chain`, reading (a)) is not absolutely
minimal: `ℕ` is discrete and `0 ≤ 1`. -/
theorem linearCausality_nat_not_minimal : ¬ (linearCausality ℕ).AbsolutelyMinimal := by
  intro h
  have := (AbsolutelyMinimalOn.eq_of_discrete (Precausality.absolutelyMinimal_iff.1 h)
    (U := ⊤) (x := 0) (y := 1)).1 (linearCausality_le.2 ⟨zero_le_one, fun _ _ => trivial⟩)
  norm_num at this

/-! ### The doubled line -/

/-- **The doubled line is not absolutely minimal**: `(0, true) ≤ (0, false)` in `ℝ × Bool`, and
over the cover by the two sheets `ℝ × {b}` every step is trivial. -/
theorem doubledLine_not_minimal : ¬ doubledLine.AbsolutelyMinimal := by
  intro h
  let sheet : Bool → Opens (ℝ × Bool) := fun b =>
    ⟨univ ×ˢ {b}, isOpen_univ.prod (isOpen_discrete _)⟩
  have hS : ∀ z ∈ (⊤ : Opens (ℝ × Bool)), ∃ O ∈ range sheet, z ∈ O :=
    fun z _ => ⟨sheet z.2, mem_range_self _, ⟨trivial, rfl⟩⟩
  have hc := ((Precausality.absolutelyMinimal_iff.1 h) _ hS ⊤ le_rfl (0, true) (0, false)).1
    (Or.inr ⟨le_rfl, fun _ _ => trivial⟩)
  have step : ∀ a b, (∃ O ∈ range sheet, doubledLine.le (⊤ ⊓ O) a b) → a = b := by
    rintro a b ⟨_, ⟨c, rfl⟩, hab⟩
    rcases hab with ⟨rfl, -⟩ | ⟨hab, hsub⟩
    · rfl
    · exfalso
      have h1 := (hsub (show ((a.1, true) : ℝ × Bool) ∈ Icc a.1 b.1 ×ˢ (univ : Set Bool) from
        ⟨left_mem_Icc.2 hab, mem_univ _⟩)).2
      have h2 := (hsub (show ((a.1, false) : ℝ × Bool) ∈ Icc a.1 b.1 ×ˢ (univ : Set Bool) from
        ⟨left_mem_Icc.2 hab, mem_univ _⟩)).2
      have e1 : true = c := h1.2
      have e2 : false = c := h2.2
      exact Bool.noConfusion (e1.trans e2.symm)
  have := eq_of_transGen_eq step hc
  exact Bool.noConfusion (congrArg Prod.snd this)

theorem doubledLine_not_hereditary : ¬ ∀ W, doubledLine.AbsolutelyMinimalOn W :=
  not_forall_of_not_absolutelyMinimal doubledLine_not_minimal

/-! ### Galileo's spacetime -/

section Galileo

variable {X : Type*} [TopologicalSpace X]

/-- The cup-shaped wall of the witness: the lid `{t = 1, |f x| ≤ 1}` and the two walls
`{|f x| = 1, 0 ≤ t ≤ 1}`. -/
def galileoCup (f : X → ℝ) : Set (ℝ × X) :=
  {q | q.1 = 1 ∧ |f q.2| ≤ 1} ∪ {q | |f q.2| = 1 ∧ 0 ≤ q.1 ∧ q.1 ≤ 1}

theorem isClosed_galileoCup {f : X → ℝ} (hf : Continuous f) : IsClosed (galileoCup f) := by
  have hφ : Continuous fun q : ℝ × X => |f q.2| := (hf.comp continuous_snd).abs
  refine IsClosed.union ?_ ?_
  · exact (isClosed_eq continuous_fst continuous_const).inter (isClosed_le hφ continuous_const)
  · exact (isClosed_eq hφ continuous_const).inter
      ((isClosed_le continuous_const continuous_fst).inter
        (isClosed_le continuous_fst continuous_const))

/-- A preconnected set inside `F` through a point of the component of `p` in `F` lies in it. -/
theorem mem_connectedComponentIn_of_preconnected {F T : Set (ℝ × X)} {p a b : ℝ × X}
    (hT : IsPreconnected T) (hTF : T ⊆ F) (ha : a ∈ T) (hb : b ∈ T)
    (hpa : a ∈ connectedComponentIn F p) : b ∈ connectedComponentIn F p := by
  rw [connectedComponentIn_eq hpa]
  exact hT.subset_connectedComponentIn ha hTF hb

/-- The open set outside the wall. -/
def galileoCupOpens {f : X → ℝ} (hf : Continuous f) : Opens (ℝ × X) :=
  ⟨(galileoCup f)ᶜ, (isClosed_galileoCup hf).isOpen_compl⟩

variable [LocallyConnectedSpace (ℝ × X)]

/-- **Galileo's spacetime over `ℝ × X` is not absolutely minimal** as soon as `X` retracts
continuously onto `ℝ` (`f ∘ g = id`). Outside the cup-shaped wall, `p = (1/2, g 0)` and
`q = (2, g 0)` lie in one connected component (a detour below the wall), so `p ≪_U q`. Over the
cover `{t > 1/4, t < 1/2}` every chain of localised steps from `p` stays in the cup
`{|f x| < 1, 1/2 ≤ t < 1}`: a step in `{t > 1/4}` stays in a component of `U ∩ {t > 1/4}`, which
the open sets `{|f x| < 1, t < 1}` and `{|f x| > 1} ∪ {t > 1}` split, and a step in `{t < 1/2}`
cannot start at a point with `t ≥ 1/2`. -/
theorem galileoOn_not_minimal (f : X → ℝ) (hf : Continuous f) (g : ℝ → X) (hg : Continuous g)
    (hfg : ∀ s, f (g s) = s) : ¬ (galileoOn X).AbsolutelyMinimal := by
  intro hmin
  set U := galileoCupOpens hf with hU
  have hUmem : ∀ r : ℝ × X, r ∈ U ↔ r ∉ galileoCup f := fun _ => Iff.rfl
  let p : ℝ × X := (1 / 2, g 0)
  let q : ℝ × X := (2, g 0)
  -- the detour
  have hpU : p ∈ U := by
    rw [hUmem]; rintro (⟨h, -⟩ | ⟨h, -⟩)
    · norm_num [p] at h
    · simp [p, hfg] at h
  have hpq : q ∈ connectedComponentIn (U : Set (ℝ × X)) p := by
    have h1 : ((-1 : ℝ), g 0) ∈ connectedComponentIn (U : Set (ℝ × X)) p := by
      refine mem_connectedComponentIn_of_preconnected (T := (fun s => (s, g 0)) '' Icc (-1) (1 / 2))
        (isPreconnected_Icc.image _ (continuous_id.prodMk continuous_const).continuousOn) ?_
        ⟨1 / 2, ⟨by norm_num, le_rfl⟩, rfl⟩ ⟨-1, ⟨le_rfl, by norm_num⟩, rfl⟩
        (mem_connectedComponentIn hpU)
      rintro _ ⟨s, hs, rfl⟩ (⟨h, -⟩ | ⟨h, -⟩)
      · simp only at h; linarith [hs.2]
      · simp [hfg] at h
    have h2 : ((-1 : ℝ), g 2) ∈ connectedComponentIn (U : Set (ℝ × X)) p := by
      refine mem_connectedComponentIn_of_preconnected (T := (fun s => ((-1 : ℝ), g s)) '' Icc 0 2)
        (isPreconnected_Icc.image _ (continuous_const.prodMk hg).continuousOn) ?_
        ⟨0, ⟨le_rfl, by norm_num⟩, rfl⟩ ⟨2, ⟨by norm_num, le_rfl⟩, rfl⟩ h1
      rintro _ ⟨s, hs, rfl⟩ (⟨h, -⟩ | ⟨-, h, -⟩)
      · norm_num at h
      · norm_num at h
    have h3 : ((2 : ℝ), g 2) ∈ connectedComponentIn (U : Set (ℝ × X)) p := by
      refine mem_connectedComponentIn_of_preconnected (T := (fun s => (s, g 2)) '' Icc (-1) 2)
        (isPreconnected_Icc.image _ (continuous_id.prodMk continuous_const).continuousOn) ?_
        ⟨-1, ⟨le_rfl, by norm_num⟩, rfl⟩ ⟨2, ⟨by norm_num, le_rfl⟩, rfl⟩ h2
      rintro _ ⟨s, hs, rfl⟩ (⟨-, h⟩ | ⟨h, -⟩)
      · simp [hfg] at h
      · simp [hfg] at h
    refine mem_connectedComponentIn_of_preconnected (T := (fun s => ((2 : ℝ), g s)) '' Icc 0 2)
      (isPreconnected_Icc.image _ (continuous_const.prodMk hg).continuousOn) ?_
      ⟨2, ⟨by norm_num, le_rfl⟩, rfl⟩ ⟨0, ⟨le_rfl, by norm_num⟩, rfl⟩ h3
    rintro _ ⟨s, hs, rfl⟩ (⟨h, -⟩ | ⟨-, -, h⟩)
    · norm_num at h
    · norm_num at h
  have hlt : (galileoOn X).lt U p q := ⟨hpU, by norm_num [p, q], hpq⟩
  -- the cover and the trap
  let T₁ : Opens (ℝ × X) := ⟨{r | 1 / 4 < r.1}, isOpen_lt continuous_const continuous_fst⟩
  let T₂ : Opens (ℝ × X) := ⟨{r | r.1 < 1 / 2}, isOpen_lt continuous_fst continuous_const⟩
  have hS : ∀ z ∈ (⊤ : Opens (ℝ × X)), ∃ O ∈ ({T₁, T₂} : Set (Opens (ℝ × X))), z ∈ O := by
    intro z _
    by_cases hz : 1 / 4 < z.1
    · exact ⟨T₁, Or.inl rfl, hz⟩
    · exact ⟨T₂, Or.inr rfl, show z.1 < 1 / 2 by linarith [not_lt.1 hz]⟩
  have hc := ((Precausality.absolutelyMinimal_iff.1 hmin) _ hS U le_top p q).2 hlt
  let A : Set (ℝ × X) := {r | |f r.2| < 1 ∧ 1 / 2 ≤ r.1 ∧ r.1 < 1}
  have hφ : Continuous fun r : ℝ × X => |f r.2| := (hf.comp continuous_snd).abs
  let P₁ : Set (ℝ × X) := {r | |f r.2| < 1 ∧ r.1 < 1}
  let P₂ : Set (ℝ × X) := {r | 1 < |f r.2|} ∪ {r | 1 < r.1}
  have hP₁ : IsOpen P₁ :=
    (isOpen_lt hφ continuous_const).inter (isOpen_lt continuous_fst continuous_const)
  have hP₂ : IsOpen P₂ :=
    (isOpen_lt continuous_const hφ).union (isOpen_lt continuous_const continuous_fst)
  have hP : Disjoint P₁ P₂ := by
    rw [Set.disjoint_left]
    rintro r ⟨h1, h2⟩ (h | h)
    · exact absurd h1 (not_lt.2 h.le)
    · exact absurd h2 (not_lt.2 h.le)
  have hsplit : ((U ⊓ T₁ : Opens (ℝ × X)) : Set (ℝ × X)) ⊆ P₁ ∪ P₂ := by
    rintro r ⟨hrU, hrT⟩
    have hrT' : 1 / 4 < r.1 := hrT
    rw [SetLike.mem_coe, hUmem] at hrU
    rcases lt_trichotomy (|f r.2|) 1 with h | h | h
    · rcases lt_trichotomy r.1 1 with h' | h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact absurd (Or.inl ⟨h', h.le⟩) hrU
      · exact Or.inr (Or.inr h')
    · by_cases h' : r.1 ≤ 1
      · exact absurd (Or.inr ⟨h, by linarith, h'⟩) hrU
      · exact Or.inr (Or.inr (not_le.1 h'))
    · exact Or.inr (Or.inl h)
  have step : ∀ a b, a ∈ A → (∃ O ∈ ({T₁, T₂} : Set (Opens (ℝ × X))),
      (galileoOn X).lt (U ⊓ O) a b) → b ∈ A := by
    rintro a b ha ⟨O, hO, hab⟩
    obtain ⟨haUO, hab1, hbc⟩ := hab
    rcases hO with rfl | hO
    · have hcc : connectedComponentIn ((U ⊓ T₁ : Opens (ℝ × X)) : Set (ℝ × X)) a ⊆ P₁ :=
        isPreconnected_connectedComponentIn.subset_left_of_subset_union hP₁ hP₂ hP
          ((connectedComponentIn_subset _ _).trans hsplit)
          ⟨a, mem_connectedComponentIn haUO, ha.1, ha.2.2⟩
      obtain ⟨hb1, hb2⟩ := hcc hbc
      exact ⟨hb1, ha.2.1.trans hab1.le, hb2⟩
    · rw [mem_singleton_iff] at hO
      subst hO
      have : a.1 < 1 / 2 := haUO.2
      exact absurd ha.2.1 (not_le.2 this)
  have hpA : p ∈ A := ⟨by simp [p, hfg], by norm_num [p], by norm_num [p]⟩
  have key : ∀ b, TransGen (fun a b => ∃ O ∈ ({T₁, T₂} : Set (Opens (ℝ × X))),
      (galileoOn X).lt (U ⊓ O) a b) p b → b ∈ A := by
    intro b hb
    induction hb with
    | single hab => exact step _ _ hpA hab
    | tail _ hbc ih => exact step _ _ ih hbc
  have hqA := (key q hc).2.2
  norm_num [q] at hqA

/-- **Galileo's spacetime `ℝ^{n+1}`, `n ≥ 1`, of `ex:causalities_lines` item 4 is not absolutely
minimal**: under DEC-167 it is no causality. -/
theorem galileo_not_minimal (n : ℕ) (hn : 1 ≤ n) : ¬ (galileo n).AbsolutelyMinimal := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  exact galileoOn_not_minimal (X := Fin (m + 1) → ℝ) (fun x => x 0) (continuous_apply 0)
    (fun s _ => s) (continuous_pi fun _ => continuous_id) fun _ => rfl

theorem galileo_not_hereditary (n : ℕ) (hn : 1 ≤ n) :
    ¬ ∀ W, (galileo n).AbsolutelyMinimalOn W :=
  not_forall_of_not_absolutelyMinimal (galileo_not_minimal n hn)

/-- Galileo's spacetime over `ℝ × ℝ` is not absolutely minimal. -/
theorem galileoOn_real_not_minimal : ¬ (galileoOn ℝ).AbsolutelyMinimal :=
  galileoOn_not_minimal id continuous_id id continuous_id fun _ => rfl

end Galileo

end GluingModels

end Causal
