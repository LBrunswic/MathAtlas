import Causal.Minkowski
import Causal.Geroch
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Instances.RatLemmas
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.NumberTheory.Real.Irrational

/-!
# Causal connectedness and causal completeness by inextensible causal curves (DEC-20)

**`def:causally_connected`** — `ETT.tex:337`, as ruled by DEC-20.
`def:causally_complete`, `rem:causal_completeness_slightly_weaker` — `ETT.tex:353`, `356`: DEC-21
reads them on maximal chains of `(M, ≤)`, certified in `Causal.ChainsOrder`. This file
keeps the curve analogue, reading (b) (`CausallyCompleteCurves`), not marked here.
`def:maximal_chain` — `ETT.tex:334`: superseded by DEC-20 (`Causal.Chains` keeps it as written).

> $M$ is causally connected if for all $p,q\in M$ such that $p\leq_M q$ there exists a connected
> maximal causal chain from $p$ to $q$.

> $M$ is causally complete if every maximal causal chain is Dedekind-complete \cite{MR1631533}.

> Causal completeness is slightly weaker than causal compactness.

DEC-20 (2026-10-30): maximal chains are replaced by **inextensible causal curves** (DEC-11,
DEC-13, `Causal.Inextensible`).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| connected maximal causal chain | ✓ DEC-20: an inextensible causal curve over an interval; connected by construction (`CausalCurveIn.isConnected_image`) |
| "from `p` to `q`" | ✓ `p = c s`, `q = c t`, `s ≤ t`; immaterial when causal (`causallyConnectedCurves_iff_of_isCausal`) |
| "Dedekind-complete" | ⚠ reading (b): bounded above **in `M`** ⇒ supremum **on the curve**; and the time-reverse |
| remark, compact ⇒ complete | ⚠ strengthened: `T2`, tarentin, causal, causally arc-connected, `J^±(p) ≠ {p}` (`causallyCompleteCurves_of_causallyCompact`) |
| remark, not conversely | ✓ local, second countable witness `ℝ × C([0,1], ℝ)` (`not_causallyCompleteCurves_imp_causallyCompact`); not locally compact |

## SCOPE (disclosed)

* **(a) Connectedness.** `CausallyConnectedCurves`: for `p ≤_M q`, an inextensible causal curve
  `c` over an interval `I` with `c s = p`, `c t = q`, `s ≤ t`. The timelike line and every static
  spacetime over a geodesic space, Minkowski `ℝ^{1,n}` for every `n` included, are causally
  connected; the literal definition fails for `ℝ^{1,n}`, `n ≥ 1` (`minkowski_not_causallyConnected`).
  Negative example, non-local (kb/0019): `ℚ` with the causality of its order, whose causal curves
  are constant (`rat_not_causallyConnectedCurves`); it is not causally arc-connected
  (`rat_not_causallyArcConnected`) nor absolutely minimal (`rat_not_absolutelyMinimal`). Under
  causal arc-connectedness and causality, connectedness follows from "every causal curve lies on
  an inextensible one" (`CurvesExtend`, `CauchyExtension.lean:82`;
  `causallyConnectedCurves_of_curvesExtend`). OQ-20 (open): should connectedness also read maximal
  chains of `(M, ≤)`, as completeness does under DEC-21?
* **(b) Completeness.** `CausallyCompleteCurves`: along every inextensible causal curve, every
  non-empty part bounded above by a point of `M` has a least upper bound for `≤_M` on the curve,
  and every part bounded below one a greatest lower bound (`AmbientDedekindComplete`). Why:
  - Zaanen's notion (`MR1631533`) with bounds on the curve is `Causal.Chains`' `DedekindComplete`;
    it holds for **every** causal curve of a causal spacetime with closed `J^-(x)`
    (`CausalCurveIn.dedekindComplete_image`), the half-plane included: a property of the
    parameter interval, not of `M`.
  - A supremum of the whole curve never exists: an inextensible curve has no endpoint.
  - (b) is the geometric reading "a curve bounded in a diamond has endpoints": under closed
    `J^±`, strong causality, causal arc-connectedness, causality and `J^±(p) ≠ {p}`, it holds iff
    no inextensible causal curve lies in a `J^-(b)` or a `J^+(a)`
    (`causallyCompleteCurves_iff_unbounded`). It is not vacuous (Minkowski space has it) and not
    trivial: the half-plane `ℝ × ]0,∞[` lacks it (`halfPlane_not_causallyCompleteCurves`).
  - Both halves are asked, being independent with bounds in `M`; the notion is invariant under
    time reversal (`dual_causallyCompleteCurves`).
* **(c) The remark.** Compact ⇒ complete uses `Causal.Geroch`'s extension step; the remark states
  no hypothesis. The converse fails in the static spacetime over `C([0,1], ℝ)` (separable,
  complete, not proper): second countable, causal, tarentin, strongly causal, causally
  arc-connected, absolutely minimal, complete (`staticCausality.causallyCompleteCurves`), not
  compact (`tentStatic_not_causallyCompact`). It is not locally compact; a locally compact witness
  is open. (`ℝ × (ℕ →ᵇ ℝ)`, `bcfStatic_not_causallyCompact`, is not second countable.)
* **(d) Old notions.** The image of an inextensible causal curve over `ℝ` which is an embedding is
  a subset chain (`CausalCurveIn.isCausalChain_range`); in `ℝ^{1,n}`, `n ≥ 1`, it is not maximal
  (`minkowski_curveChain_not_maximal`) because `ℝ^{1,n}` has no maximal chain of `Causal.Chains`
  at all (`minkowski_not_isMaximalChain`), not because of anything about the curve.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter

open scoped BoundedContinuousFunction

universe u

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable (C : Causality M)

/-! ### The definitions -/

/-- **`def:causally_connected`, DEC-20.** For `p ≤_M q` there is an inextensible causal curve
through `p` and then `q`. -/
def CausallyConnectedCurves : Prop :=
  ∀ p q : M, C.le ⊤ p q → ∃ (I : Set ℝ) (c : ℝ → M), C.Inextensible ⊤ I c ∧
    ∃ s ∈ I, ∃ t ∈ I, s ≤ t ∧ c s = p ∧ c t = q

/-- `s` is a least upper bound of `A` **on `S`** for `≤_M`. -/
def IsLUBOn (S A : Set M) (s : M) : Prop :=
  s ∈ S ∧ (∀ a ∈ A, C.le ⊤ a s) ∧ ∀ s' ∈ S, (∀ a ∈ A, C.le ⊤ a s') → C.le ⊤ s s'

/-- Every non-empty `A ⊂ S` bounded above **in `M`** has a least upper bound on `S`. -/
def SupCompleteIn (S : Set M) : Prop :=
  ∀ A ⊆ S, A.Nonempty → (∃ b : M, ∀ a ∈ A, C.le ⊤ a b) → ∃ s, C.IsLUBOn S A s

/-- Reading (b) of "Dedekind-complete": suprema of parts bounded above in `M`, and infima of parts
bounded below in `M` (the suprema for `C.dual`), exist on `S`. -/
def AmbientDedekindComplete (S : Set M) : Prop := C.SupCompleteIn S ∧ C.dual.SupCompleteIn S

/-- **`def:causally_complete`, DEC-20, reading (b).** Every inextensible causal curve is
Dedekind-complete for bounds taken in `M`. -/
def CausallyCompleteCurves : Prop :=
  ∀ (I : Set ℝ) (c : ℝ → M), C.Inextensible ⊤ I c → C.AmbientDedekindComplete (c '' I)

variable {C} {I : Set ℝ} {c : ℝ → M}

/-! ### Time reversal -/

theorem dual_ambientDedekindComplete {S : Set M} :
    C.dual.AmbientDedekindComplete S ↔ C.AmbientDedekindComplete S :=
  ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

omit [TopologicalSpace M] in
/-- Running a curve backwards does not change its image. -/
theorem image_neg_comp (c : ℝ → M) (I : Set ℝ) : (fun t => c (-t)) '' (-I) = c '' I := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨-t, by simpa using ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨-t, by simpa using ht, by simp⟩

theorem CausallyCompleteCurves.dual (h : C.CausallyCompleteCurves) :
    C.dual.CausallyCompleteCurves := by
  intro I c hc
  have := h (-I) (fun t => c (-t)) hc.dual_reverse
  rw [image_neg_comp] at this
  exact dual_ambientDedekindComplete.2 this

theorem dual_causallyCompleteCurves : C.dual.CausallyCompleteCurves ↔ C.CausallyCompleteCurves :=
  ⟨fun h => h.dual, fun h => h.dual⟩

theorem CausallyConnectedCurves.dual (h : C.CausallyConnectedCurves) :
    C.dual.CausallyConnectedCurves := by
  intro p q hpq
  obtain ⟨I, c, hc, s, hs, t, ht, hst, rfl, rfl⟩ := h q p hpq
  exact ⟨-I, fun τ => c (-τ), hc.dual_reverse, -t, by simpa using ht, -s, by simpa using hs,
    neg_le_neg hst, by simp, by simp⟩

theorem dual_causallyConnectedCurves :
    C.dual.CausallyConnectedCurves ↔ C.CausallyConnectedCurves :=
  ⟨fun h => h.dual, fun h => h.dual⟩

/-! ### Connectedness, and the order of `p` and `q` -/

/-- The image of a causal curve over an interval is connected. -/
theorem CausalCurveIn.isConnected_image {W : Opens M} (hc : C.CausalCurveIn W I c) :
    IsConnected (c '' I) := by
  obtain ⟨t₀, ht₀⟩ := hc.nonempty
  have hmin : ∀ b : I, min t₀ b ∈ I := fun b => min_rec' (· ∈ I) ht₀ b.2
  have hmax : ∀ b : I, max t₀ b ∈ I := fun b => max_rec' (· ∈ I) ht₀ b.2
  refine ⟨⟨c t₀, t₀, ht₀, rfl⟩, ?_⟩
  have heq : c '' I = ⋃ b : I, c '' Icc (min t₀ b) (max t₀ b) := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact mem_iUnion.2 ⟨⟨t, ht⟩, t, ⟨min_le_right _ _, le_max_right _ _⟩, rfl⟩
    · intro hx
      obtain ⟨b, t, htI, rfl⟩ := mem_iUnion.1 hx
      exact ⟨t, hc.ordConnected.out (hmin b) (hmax b) htI, rfl⟩
  rw [heq]
  refine isPreconnected_iUnion ⟨c t₀, mem_iInter.2 fun b =>
    ⟨t₀, ⟨min_le_left _ _, le_max_left _ _⟩, rfl⟩⟩ fun b => ?_
  exact isPreconnected_Icc.image _
    ((hc.curve _ (hmin b) _ (hmax b)).continuousOn C.isRelFamily_le)

/-- In a causal spacetime the order in which the curve meets `p` and `q` is immaterial. -/
theorem causallyConnectedCurves_iff_of_isCausal (hcaus : C.IsCausal) :
    C.CausallyConnectedCurves ↔ ∀ p q : M, C.le ⊤ p q → ∃ (I : Set ℝ) (c : ℝ → M),
      C.Inextensible ⊤ I c ∧ p ∈ c '' I ∧ q ∈ c '' I := by
  constructor
  · intro h p q hpq
    obtain ⟨I, c, hc, s, hs, t, ht, -, hcs, hct⟩ := h p q hpq
    exact ⟨I, c, hc, ⟨s, hs, hcs⟩, ⟨t, ht, hct⟩⟩
  · intro h p q hpq
    obtain ⟨I, c, hc, ⟨s, hs, rfl⟩, ⟨t, ht, rfl⟩⟩ := h p q hpq
    rcases le_total s t with hst | hts
    · exact ⟨I, c, hc, s, hs, t, ht, hst, rfl, rfl⟩
    · have heq : c s = c t := hcaus hpq (hc.1.le_of_le ht hs hts)
      exact ⟨I, c, hc, s, hs, s, hs, le_rfl, rfl, heq⟩

/-- Under causal arc-connectedness and causality, causal connectedness follows from the model
fact `CurvesExtend` of `Causal.CauchyExtension` (every causal curve over a segment lies on
an inextensible one), stated here as a hypothesis. -/
theorem causallyConnectedCurves_of_curvesExtend (hC : C.CausallyArcConnected) (hcaus : C.IsCausal)
    (hext : ∀ (c : ℝ → M) (a b : ℝ), a ≤ b → C.CausalCurveOn ⊤ c a b →
      ∃ (I : Set ℝ) (c' : ℝ → M), C.Inextensible ⊤ I c' ∧ c '' Icc a b ⊆ c' '' I) :
    C.CausallyConnectedCurves := by
  rw [causallyConnectedCurves_iff_of_isCausal hcaus]
  intro p q hpq
  obtain ⟨γ, hγ, hγ0, hγ1⟩ := (hC ⊤ le_rfl p q).1.1 hpq
  obtain ⟨I, c', hc', hsub⟩ := hext γ 0 1 zero_le_one hγ
  exact ⟨I, c', hc', hsub ⟨0, ⟨le_rfl, zero_le_one⟩, hγ0⟩, hsub ⟨1, ⟨zero_le_one, le_rfl⟩, hγ1⟩⟩

/-! ### Least upper bounds along a curve -/

/-- **The core.** Along a causal curve, with `J^-(x)` closed, a part `A` of the image whose
parameters are bounded above in `I` has a least upper bound on the curve: the point at the
supremum of the parameters. -/
theorem CausalCurveIn.exists_isLUBOn (hJ : ∀ x, IsClosed (C.Jminus ⊤ {x}))
    (hc : C.CausalCurveIn ⊤ I c) {A : Set M} (hA : A ⊆ c '' I) {t₀ u : ℝ} (ht₀ : t₀ ∈ I)
    (hct₀ : c t₀ ∈ A) (hu : u ∈ I) (hTu : ∀ t ∈ I, c t ∈ A → t ≤ u) :
    ∃ s, C.IsLUBOn (c '' I) A s := by
  set T : Set ℝ := {t | t ∈ I ∧ c t ∈ A} with hT
  have hTne : T.Nonempty := ⟨t₀, ht₀, hct₀⟩
  have hTbdd : BddAbove T := ⟨u, fun t ht => hTu t ht.1 ht.2⟩
  set σ := sSup T with hσ
  have ht₀σ : t₀ ≤ σ := le_csSup hTbdd ⟨ht₀, hct₀⟩
  have hσu : σ ≤ u := csSup_le hTne fun t ht => hTu t ht.1 ht.2
  have hσI : σ ∈ I := hc.ordConnected.out ht₀ hu ⟨ht₀σ, hσu⟩
  refine ⟨c σ, ⟨σ, hσI, rfl⟩, ?_, ?_⟩
  · intro a ha
    obtain ⟨t, ht, rfl⟩ := hA ha
    exact hc.le_of_le ht hσI (le_csSup hTbdd ⟨ht, ha⟩)
  · rintro _ ⟨v, hv, rfl⟩ hub
    rcases le_or_gt σ v with h | h
    · exact hc.le_of_le hσI hv h
    · set P : Set ℝ := Icc v σ ∩ c ⁻¹' (C.Jminus ⊤ {c v}) with hP
      have hPc : IsClosed P := ((hc.curve v hv σ hσI).continuousOn
        C.isRelFamily_le).preimage_isClosed_of_isClosed isClosed_Icc (hJ _)
      have hvP : v ∈ P := ⟨⟨le_rfl, h.le⟩, Precausality.mem_Jminus_singleton.2
        (C.le_refl (show c v ∈ (⊤ : Opens M) from trivial))⟩
      have hPbdd : BddAbove P := ⟨σ, fun t ht => ht.1.2⟩
      have hsup : sSup P = σ := by
        refine le_antisymm (csSup_le ⟨v, hvP⟩ fun t ht => ht.1.2) (csSup_le hTne fun t ht => ?_)
        rcases le_or_gt t v with htv | htv
        · exact htv.trans (le_csSup hPbdd hvP)
        · exact le_csSup hPbdd ⟨⟨htv.le, le_csSup hTbdd ht⟩,
            Precausality.mem_Jminus_singleton.2 (hub _ ht.2)⟩
      have hσP : σ ∈ P := hsup ▸ hPc.csSup_mem ⟨v, hvP⟩ hPbdd
      exact Precausality.mem_Jminus_singleton.1 hσP.2

/-- A causal curve bounded above by no point of `M` has suprema on itself for every part bounded
above in `M`. -/
theorem CausalCurveIn.supCompleteIn_image (hJ : ∀ x, IsClosed (C.Jminus ⊤ {x}))
    (hc : C.CausalCurveIn ⊤ I c) (hnb : ∀ b : M, ¬ ∀ t ∈ I, C.le ⊤ (c t) b) :
    C.SupCompleteIn (c '' I) := by
  rintro A hA ⟨_, ha₀⟩ ⟨b, hb⟩
  obtain ⟨t₀, ht₀, rfl⟩ := hA ha₀
  by_cases hbdd : ∃ u ∈ I, ∀ t ∈ I, c t ∈ A → t ≤ u
  · obtain ⟨u, hu, hTu⟩ := hbdd
    exact hc.exists_isLUBOn hJ hA ht₀ ha₀ hu hTu
  · exfalso
    push Not at hbdd
    refine hnb b fun t ht => ?_
    obtain ⟨t', ht', hA', htt'⟩ := hbdd t ht
    exact C.le_trans (hc.le_of_le ht ht' htt'.le) (hb _ hA')

/-- Both halves. -/
theorem CausalCurveIn.ambientDedekindComplete_image (hJm : ∀ x, IsClosed (C.Jminus ⊤ {x}))
    (hJp : ∀ x, IsClosed (C.Jplus ⊤ {x})) (hc : C.CausalCurveIn ⊤ I c)
    (hup : ∀ b : M, ¬ ∀ t ∈ I, C.le ⊤ (c t) b) (hdown : ∀ b : M, ¬ ∀ t ∈ I, C.le ⊤ b (c t)) :
    C.AmbientDedekindComplete (c '' I) := by
  refine ⟨hc.supCompleteIn_image hJm hup, ?_⟩
  rw [← image_neg_comp c I]
  refine hc.reverse.supCompleteIn_image (C := C.dual) hJp fun b h => hdown b fun t ht => ?_
  have := h (-t) (by simpa using ht)
  simpa using this

/-- **Reading (b) from the geometric reading**: if `J^±(x)` are closed and no inextensible causal
curve lies in a `J^-(b)` or in a `J^+(a)`, the spacetime is causally complete. -/
theorem causallyCompleteCurves_of_unbounded (hJm : ∀ x, IsClosed (C.Jminus ⊤ {x}))
    (hJp : ∀ x, IsClosed (C.Jplus ⊤ {x}))
    (hup : ∀ (I : Set ℝ) (c : ℝ → M) (b : M), C.Inextensible ⊤ I c → ¬ ∀ t ∈ I, C.le ⊤ (c t) b)
    (hdown : ∀ (I : Set ℝ) (c : ℝ → M) (b : M), C.Inextensible ⊤ I c →
      ¬ ∀ t ∈ I, C.le ⊤ b (c t)) :
    C.CausallyCompleteCurves :=
  fun I c hc => hc.1.ambientDedekindComplete_image hJm hJp (fun b => hup I c b hc)
    (fun b => hdown I c b hc)

/-- **Conversely**, a causally complete spacetime (reading (b)) has no inextensible causal curve in
a `J^-(b)`, when the causal futures are closed and `M` is strongly causal, causally arc-connected,
causal, with `J^±(p) ≠ {p}`: the supremum on the curve would be a limit at its future end. -/
theorem CausallyCompleteCurves.not_forall_le (hB : C.CausallyCompleteCurves)
    (hJp : ∀ x, IsClosed (C.Jplus ⊤ {x})) (hSC : C.StronglyCausal) (hC : C.CausallyArcConnected)
    (hcaus : C.IsCausal) (hm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) (hp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p})
    (hc : C.Inextensible ⊤ I c) (b : M) : ¬ ∀ t ∈ I, C.le ⊤ (c t) b := by
  intro hb
  obtain ⟨ψ, -, -, hψr, hd⟩ := hc.reparam hC hcaus hm hp
  have hmem : ∀ s, ψ s ∈ I := fun s => hψr ▸ mem_range_self s
  obtain ⟨_, ⟨σ, -, rfl⟩, hub, -⟩ := (hB univ _ hd).1 _ subset_rfl ⟨_, 0, trivial, rfl⟩
    ⟨b, by rintro _ ⟨s, -, rfl⟩; exact hb _ (hmem s)⟩
  have hconst : ∀ s, σ ≤ s → (c ∘ ψ) s = (c ∘ ψ) σ := fun s hs =>
    hcaus (hub _ ⟨s, trivial, rfl⟩) (hd.1.le_of_le trivial trivial hs)
  have hlim : Tendsto (c ∘ ψ) atTop (𝓝 ((c ∘ ψ) σ)) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [eventually_ge_atTop σ] with s hs
      exact (hconst s hs).symm)
  exact Inextensible.not_tendsto_atTop hJp hSC hC hcaus hp hd _ hlim

/-- **Reading (b) is the geometric reading**: under closed `J^±(x)`, strong causality, causal
arc-connectedness, causality and `J^±(p) ≠ {p}`, a spacetime is causally complete iff no
inextensible causal curve lies in a `J^-(b)` or in a `J^+(a)`. -/
theorem causallyCompleteCurves_iff_unbounded (hJm : ∀ x, IsClosed (C.Jminus ⊤ {x}))
    (hJp : ∀ x, IsClosed (C.Jplus ⊤ {x})) (hSC : C.StronglyCausal) (hC : C.CausallyArcConnected)
    (hcaus : C.IsCausal) (hm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p})
    (hp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) :
    C.CausallyCompleteCurves ↔
      (∀ (I : Set ℝ) (c : ℝ → M) (b : M), C.Inextensible ⊤ I c → ¬ ∀ t ∈ I, C.le ⊤ (c t) b) ∧
      (∀ (I : Set ℝ) (c : ℝ → M) (a : M), C.Inextensible ⊤ I c → ¬ ∀ t ∈ I, C.le ⊤ a (c t)) := by
  refine ⟨fun hB => ⟨fun I c b hc => hB.not_forall_le hJp hSC hC hcaus hm hp hc b,
    fun I c a hc ha => ?_⟩, fun h => causallyCompleteCurves_of_unbounded hJm hJp h.1 h.2⟩
  refine hB.dual.not_forall_le (C := C.dual) hJm (dual_stronglyCausal.2 hSC)
    (dual_causallyArcConnectedOn.2 hC) (dual_isCausal.2 hcaus) hp hm hc.dual_reverse a
    fun t ht => ?_
  have := ha (-t) (by simpa using ht)
  simpa using this

/-! ### Reading (a) is trivial -/

/-- From suprema on `S` to the `DedekindComplete` of `Causal.Chains`, whose bounds are on `S`. -/
theorem dedekindComplete_of_isLUBOn {S : Set M}
    (h : ∀ A ⊆ S, A.Nonempty → (∃ b ∈ S, ∀ a ∈ A, C.le ⊤ a b) → ∃ s, C.IsLUBOn S A s) :
    C.DedekindComplete S := by
  rw [dedekindComplete_iff]
  rintro A ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨s, hsS, h1, h2⟩ := h (Subtype.val '' A) (by rintro _ ⟨x, -, rfl⟩; exact x.2)
    ⟨a.1, a, ha, rfl⟩ ⟨b.1, b.2, by rintro _ ⟨x, hx, rfl⟩; exact hb x hx⟩
  exact ⟨⟨s, hsS⟩, fun x hx => h1 _ ⟨x, hx, rfl⟩,
    fun b' hb' => h2 b'.1 b'.2 (by rintro _ ⟨x, hx, rfl⟩; exact hb' x hx)⟩

/-- Reading (b) implies the reading of `Causal.Chains` on the curve. -/
theorem AmbientDedekindComplete.dedekindComplete {S : Set M} (h : C.AmbientDedekindComplete S) :
    C.DedekindComplete S :=
  dedekindComplete_of_isLUBOn fun A hA hne ⟨b, _, hb⟩ => h.1 A hA hne ⟨b, hb⟩

/-- **Finding: reading (a) holds for every causal curve** of a causal spacetime whose causal pasts
are closed — inextensible or not, causally compact or not. -/
theorem CausalCurveIn.dedekindComplete_image (hcaus : C.IsCausal)
    (hJ : ∀ x, IsClosed (C.Jminus ⊤ {x})) (hc : C.CausalCurveIn ⊤ I c) :
    C.DedekindComplete (c '' I) := by
  apply dedekindComplete_of_isLUBOn
  rintro A hA ⟨_, ha₀⟩ ⟨_, ⟨v, hv, rfl⟩, hb⟩
  obtain ⟨t₀, ht₀, rfl⟩ := hA ha₀
  by_cases hbdd : ∃ u ∈ I, ∀ t ∈ I, c t ∈ A → t ≤ u
  · obtain ⟨u, hu, hTu⟩ := hbdd
    exact hc.exists_isLUBOn hJ hA ht₀ ha₀ hu hTu
  · push Not at hbdd
    obtain ⟨t, ht, htA, hvt⟩ := hbdd v hv
    have hcv : c t = c v := hcaus (hb _ htA) (hc.le_of_le hv ht hvt.le)
    refine ⟨c v, ⟨v, hv, rfl⟩, hb, fun s' _ hs' => ?_⟩
    rw [← hcv]
    exact hs' _ htA

/-! ### `rem:causal_completeness_slightly_weaker`: compact ⇒ complete -/

section Compact

variable [T2Space M]

/-- Under the hypotheses of `theo:geroch`, no inextensible causal curve lies in `J^-(b)`. -/
theorem Inextensible.not_forall_le_of_causallyCompact (hT : C.Tarentin) (hcaus : C.IsCausal)
    (hK : C.CausallyCompact) (hC : C.CausallyArcConnected) (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p})
    (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) (hc : C.Inextensible ⊤ I c) (b : M) :
    ¬ ∀ t ∈ I, C.le ⊤ (c t) b := by
  intro hb
  obtain ⟨ψ, -, -, hψr, hd⟩ := hc.reparam hC hcaus hJm hJp
  have hmem : ∀ s, ψ s ∈ I := fun s => hψr ▸ mem_range_self s
  exact hd.2 (futureExtensible_of_forall_ge hT ⟨hcaus, hK⟩ hC hJp hd.1 (q := b)
    fun s => hb _ (hmem s)).extensible

/-- Under the hypotheses of `theo:geroch`, no inextensible causal curve lies in `J^+(a)`. -/
theorem Inextensible.not_forall_ge_of_causallyCompact (hT : C.Tarentin) (hcaus : C.IsCausal)
    (hK : C.CausallyCompact) (hC : C.CausallyArcConnected) (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p})
    (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) (hc : C.Inextensible ⊤ I c) (a : M) :
    ¬ ∀ t ∈ I, C.le ⊤ a (c t) := by
  intro ha
  obtain ⟨ψ, -, -, hψr, hd⟩ := hc.reparam hC hcaus hJm hJp
  have hmem : ∀ s, ψ s ∈ I := fun s => hψr ▸ mem_range_self s
  exact hd.2 (pastExtensible_of_forall_le hT ⟨hcaus, hK⟩ hC hJm hd.1 (q := a)
    fun s => ha _ (hmem s)).extensible

/-- **`rem:causal_completeness_slightly_weaker`, first half**: a causally compact spacetime is
causally complete, under the hypotheses of `theo:geroch` (`T2`, tarentin, causal, causally
arc-connected, `J^±(p) ≠ {p}`). -/
theorem causallyCompleteCurves_of_causallyCompact (hT : C.Tarentin) (hcaus : C.IsCausal)
    (hK : C.CausallyCompact) (hC : C.CausallyArcConnected) (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p})
    (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) : C.CausallyCompleteCurves := by
  have hG : C.GloballyHyperbolic := ⟨hcaus, hK⟩
  exact causallyCompleteCurves_of_unbounded (hG.isClosed_Jminus_singleton hT)
    (hG.isClosed_Jplus_singleton hT)
    (fun _ _ b hc => hc.not_forall_le_of_causallyCompact hT hcaus hK hC hJm hJp b)
    (fun _ _ a hc => hc.not_forall_ge_of_causallyCompact hT hcaus hK hC hJm hJp a)

end Compact

/-! ### The old notions -/

/-- The image of a causal curve over `ℝ` which is an embedding is a subset causal chain
(`def:causal_chain` (2)). -/
theorem CausalCurveIn.isCausalChain_range (hc : C.CausalCurveIn ⊤ univ c) (he : IsEmbedding c) :
    C.IsCausalChain (range c) :=
  (isCausalChainMap_real_iff.2 ⟨he, fun a b => hc.curve a trivial b trivial⟩).isCausalChain_range

end Causality

/-! ### A negative example for connectedness: the rationals (non-local, kb/0019) -/

/-- On `ℚ` (totally disconnected) every causal curve, of any causality, is constant. -/
theorem rat_causalCurveIn_subsingleton {D : Causality ℚ} {W : Opens ℚ} {I : Set ℝ} {c : ℝ → ℚ}
    (hc : D.CausalCurveIn W I c) : (c '' I).Subsingleton :=
  hc.isConnected_image.isPreconnected.subsingleton

/-- **`ℚ` with the causality of its order is not causally connected**: `0 ≤ 1`, and no causal
curve meets two points. The causality `linearCausality ℚ` is not causally arc-connected and not
absolutely minimal: a non-local witness (kb/0019). -/
theorem rat_not_causallyConnectedCurves : ¬ (linearCausality ℚ).CausallyConnectedCurves := by
  intro h
  obtain ⟨I, c, hc, s, hs, t, ht, -, hcs, hct⟩ := h 0 1 ⟨zero_le_one, fun _ _ => trivial⟩
  have := rat_causalCurveIn_subsingleton hc.1 ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
  rw [hcs, hct] at this
  exact zero_ne_one this

/-- `ℚ` with the causality of its order is **not causally arc-connected**: `0 ≤ 1` and no causal
curve joins them. -/
theorem rat_not_causallyArcConnected : ¬ (linearCausality ℚ).CausallyArcConnected := by
  intro hC
  obtain ⟨γ, hγ, h0, h1⟩ := (hC ⊤ le_rfl 0 1).1.1 ⟨zero_le_one, fun _ _ => trivial⟩
  have hsub := (isPreconnected_Icc.image γ
    (hγ.continuousOn (linearCausality ℚ).isRelFamily_le)).subsingleton
  have := hsub ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩ ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩
  rw [h0, h1] at this
  exact zero_ne_one this

/-- `ℚ` with the causality of its order is **not absolutely minimal**: for the cover by the two
sides of `√2`, the generated relation never crosses `√2`, while `1 ≤ 2`. -/
theorem rat_not_absolutelyMinimal : ¬ (linearCausality ℚ).AbsolutelyMinimal := by
  rw [Precausality.absolutelyMinimal_iff]
  intro h
  let O₁ : Opens ℚ := ⟨{x | (x : ℝ) < √2}, isOpen_lt Rat.continuous_coe_real continuous_const⟩
  let O₂ : Opens ℚ := ⟨{x | √2 < (x : ℝ)}, isOpen_lt continuous_const Rat.continuous_coe_real⟩
  have hne : ∀ x : ℚ, (x : ℝ) ≠ √2 := fun x hx => irrational_sqrt_two.ne_rat x hx.symm
  have hS : ∀ x ∈ (⊤ : Opens ℚ), ∃ O ∈ ({O₁, O₂} : Set (Opens ℚ)), x ∈ O := fun x _ => by
    rcases lt_or_gt_of_ne (hne x) with hx | hx
    · exact ⟨O₁, Or.inl rfl, hx⟩
    · exact ⟨O₂, Or.inr rfl, hx⟩
  have hstep : ∀ a b : ℚ, (∃ O ∈ ({O₁, O₂} : Set (Opens ℚ)), (linearCausality ℚ).le (⊤ ⊓ O) a b) →
      ((a : ℝ) < √2 ↔ (b : ℝ) < √2) := by
    rintro a b ⟨O, hO, hab⟩
    have ha := (linearCausality ℚ).le_mem_left hab
    have hb := (linearCausality ℚ).le_mem_right hab
    rcases hO with rfl | rfl
    · exact ⟨fun _ => hb.2, fun _ => ha.2⟩
    · exact ⟨fun h' => absurd h' (not_lt.2 (le_of_lt ha.2)),
        fun h' => absurd h' (not_lt.2 (le_of_lt hb.2))⟩
  have key : ∀ x y : ℚ, Relation.TransGen
      (fun a b => ∃ O ∈ ({O₁, O₂} : Set (Opens ℚ)), (linearCausality ℚ).le (⊤ ⊓ O) a b) x y →
      ((x : ℝ) < √2 ↔ (y : ℝ) < √2) := by
    intro x y hxy
    induction hxy with
    | single h' => exact hstep _ _ h'
    | tail _ h' ih => exact ih.trans (hstep _ _ h')
  have h12 := key 1 2 ((h _ hS ⊤ le_rfl 1 2).1 ⟨by norm_num, fun _ _ => trivial⟩)
  have h1 : ((1 : ℚ) : ℝ) < √2 := by
    push_cast; rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2 : ¬ ((2 : ℚ) : ℝ) < √2 := by
    push_cast; rw [Real.lt_sqrt (by norm_num)]; norm_num
  exact h2 (h12.1 h1)

/-! ### Static spacetimes -/

namespace staticCausality

variable {X : Type u} [MetricSpace X] [GeodesicSpace X]

/-- Through `p ≤ q` passes the graph of a 1-Lipschitz map over `ℝ`, an inextensible causal curve:
the segment from `p` to `q`, continued by the vertical lines through `p` and `q`. -/
theorem exists_inextensible_graph {p q : ℝ × X} (hpq : (staticCausality X).le ⊤ p q) :
    ∃ Γ : ℝ → X, (staticCausality X).Inextensible ⊤ univ (fun τ => (τ, Γ τ)) ∧
      p.1 ≤ q.1 ∧ Γ p.1 = p.2 ∧ Γ q.1 = q.2 := by
  obtain ⟨hle, γ, hγp, hγq, hγ⟩ := le_iff.1 hpq
  set cl : ℝ → ℝ := fun τ => max p.1 (min τ q.1) with hcl
  have hclI : ∀ τ, cl τ ∈ Icc p.1 q.1 := fun τ =>
    ⟨le_max_left _ _, max_le hle (min_le_right _ _)⟩
  have hcl1 : ∀ τ τ', |cl τ - cl τ'| ≤ |τ - τ'| := fun τ τ' => by
    simp only [hcl]
    rw [max_comm p.1, max_comm p.1]
    refine (abs_max_sub_max_le_abs _ _ _).trans ((abs_min_sub_min_le_max _ _ _ _).trans ?_)
    simp
  set Γ : ℝ → X := fun τ => γ (cl τ) with hΓ
  have hlip : ∀ a b, LipOn 1 Γ a b := fun a b τ _ τ' _ => by
    have := hγ.lip _ (hclI τ) _ (hclI τ')
    simp only [hΓ]
    rw [one_mul] at this ⊢
    exact this.trans (hcl1 τ τ')
  have hcurve : (staticCausality X).CausalCurveIn ⊤ univ (fun τ => (τ, Γ τ)) :=
    ⟨⟨0, trivial⟩, ordConnected_univ, fun a _ b _ =>
      causalCurveOn_graph ⟨hlip a b, fun _ _ => trivial⟩⟩
  refine ⟨Γ, Causality.inextensible_of_unbounded (f := Prod.fst) (fun x y h => by
      have := le_top_iff.1 h; linarith [dist_nonneg (x := x.2) (y := y.2)]) hcurve
      (fun b => ⟨b + 1, by simp⟩) (fun b => ⟨b - 1, by simp⟩), hle, ?_, ?_⟩
  · simp only [hΓ, hcl]
    rw [min_eq_left hle, max_self]
    exact hγp
  · simp only [hΓ, hcl]
    rw [min_self, max_eq_right hle]
    exact hγq

/-- **A static spacetime over a geodesic space is causally connected** (DEC-20). -/
theorem causallyConnectedCurves : (staticCausality X).CausallyConnectedCurves := by
  intro p q hpq
  obtain ⟨Γ, hΓ, hle, hp, hq⟩ := exists_inextensible_graph hpq
  exact ⟨univ, _, hΓ, p.1, trivial, q.1, trivial, hle, Prod.ext rfl hp, Prod.ext rfl hq⟩

/-- Over a complete `X`, no inextensible causal curve lies in a `J^-(b)`: its time tends to `+∞`. -/
theorem Inextensible.not_forall_le [CompleteSpace X] {I : Set ℝ} {c : ℝ → ℝ × X}
    (hc : (staticCausality X).Inextensible ⊤ I c) (b : ℝ × X) :
    ¬ ∀ t ∈ I, (staticCausality X).le ⊤ (c t) b := by
  intro hb
  obtain ⟨ψ, -, -, hψr, hd⟩ := hc.reparam causallyArcConnected isCausal Jminus_ne_singleton
    Jplus_ne_singleton
  have hmem : ∀ s, ψ s ∈ I := fun s => hψr ▸ mem_range_self s
  obtain ⟨s, hs⟩ := ((tendsto_time_atTop hd).eventually_gt_atTop b.1).exists
  have h1 := le_top_iff.1 (hb _ (hmem s))
  simp only [Function.comp] at hs
  linarith [dist_nonneg (x := (c (ψ s)).2) (y := b.2)]

/-- Over a complete `X`, no inextensible causal curve lies in a `J^+(a)`. -/
theorem Inextensible.not_forall_ge [CompleteSpace X] {I : Set ℝ} {c : ℝ → ℝ × X}
    (hc : (staticCausality X).Inextensible ⊤ I c) (a : ℝ × X) :
    ¬ ∀ t ∈ I, (staticCausality X).le ⊤ a (c t) := by
  intro ha
  obtain ⟨ψ, -, -, hψr, hd⟩ := hc.reparam causallyArcConnected isCausal Jminus_ne_singleton
    Jplus_ne_singleton
  have hmem : ∀ s, ψ s ∈ I := fun s => hψr ▸ mem_range_self s
  obtain ⟨s, hs⟩ := ((tendsto_time_atBot hd).eventually_lt_atBot a.1).exists
  have h1 := le_top_iff.1 (ha _ (hmem s))
  simp only [Function.comp] at hs
  linarith [dist_nonneg (x := a.2) (y := (c (ψ s)).2)]

/-- **A static spacetime over a complete geodesic space is causally complete**, proper or not. -/
theorem causallyCompleteCurves [CompleteSpace X] : (staticCausality X).CausallyCompleteCurves :=
  Causality.causallyCompleteCurves_of_unbounded isClosed_Jminus_top isClosed_Jplus_top
    (fun _ _ b hc => Inextensible.not_forall_le hc b) (fun _ _ a hc => Inextensible.not_forall_ge hc a)

end staticCausality

/-! ### The converse fails: a static spacetime over a complete, non-proper space -/

/-- The `n`-th indicator function of `ℕ`, a bounded continuous function. -/
noncomputable def bump (n : ℕ) : ℕ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfDiscrete (fun k => if k = n then 1 else 0) 1 (fun x y => by
    split_ifs <;> norm_num [Real.dist_eq])

@[simp] theorem bump_apply (n k : ℕ) : bump n k = if k = n then 1 else 0 := rfl

/-- **The static spacetime over `ℕ →ᵇ ℝ` is not causally compact**: `J((0,0),(2,0))` contains the
points `(1, bump n)`, pairwise at distance `1`. -/
theorem bcfStatic_not_causallyCompact : ¬ (staticCausality (ℕ →ᵇ ℝ)).CausallyCompact := by
  intro hK
  have hd0 : ∀ n, dist (bump n) 0 ≤ 1 := fun n =>
    (BoundedContinuousFunction.dist_le zero_le_one).2 fun k => by
      rw [bump_apply, BoundedContinuousFunction.coe_zero, Pi.zero_apply]
      split_ifs <;> norm_num [Real.dist_eq]
  have hsep : ∀ m n, m ≠ n → 1 ≤ dist (bump m) (bump n) := fun m n hmn =>
    le_trans (by rw [bump_apply, bump_apply, if_pos rfl, if_neg hmn]; norm_num [Real.dist_eq])
      (BoundedContinuousFunction.dist_coe_le_dist m)
  set x : ℕ → ℝ × (ℕ →ᵇ ℝ) := fun n => (1, bump n) with hx'
  have hx : ∀ n, x n ∈ (staticCausality (ℕ →ᵇ ℝ)).diamond ⊤ (0, 0) (2, 0) := fun n => by
    rw [Causality.mem_diamond, staticCausality.le_top_iff, staticCausality.le_top_iff]
    refine ⟨?_, ?_⟩
    · show dist (0 : ℕ →ᵇ ℝ) (bump n) ≤ 1 - 0
      rw [dist_comm]
      linarith [hd0 n]
    · show dist (bump n) 0 ≤ 2 - 1
      linarith [hd0 n]
  obtain ⟨y, -, φ, hφ, hlim⟩ := (hK (0, 0) (2, 0)).tendsto_subseq hx
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hlim.cauchySeq 1 one_pos
  have h1 := hN (N + 1) (by omega) N le_rfl
  have h2 : 1 ≤ dist (x (φ (N + 1))) (x (φ N)) :=
    (hsep _ _ (hφ (Nat.lt_succ_self N)).ne').trans (by rw [Prod.dist_eq]; exact le_max_right _ _)
  simp only [Function.comp] at h1
  linarith

/-! ### A separable witness: `ℝ × C([0, 1], ℝ)` -/

/-- The tent of height `1` on the dyadic interval `]2^{-(n+1)}, 2^{-n}[` of `[0, 1]`. -/
noncomputable def tent (n : ℕ) : C(Icc (0 : ℝ) 1, ℝ) :=
  ⟨fun x => max 0 (1 - |2 ^ (n + 2) * (x : ℝ) - 3|), continuous_const.max
    (continuous_const.sub ((continuous_const.mul continuous_subtype_val).sub continuous_const).abs)⟩

theorem four_le_two_pow (n : ℕ) : (4 : ℝ) ≤ 2 ^ (n + 2) :=
  calc (4 : ℝ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (n + 2) := pow_le_pow_right₀ (by norm_num) (by omega)

/-- The top of the `n`-th tent, `3 / 2^{n+2}`. -/
noncomputable def tentPt (n : ℕ) : Icc (0 : ℝ) 1 :=
  ⟨3 / 2 ^ (n + 2), by positivity, (div_le_one (by positivity)).2 (by linarith [four_le_two_pow n])⟩

theorem tent_apply (n : ℕ) (x : Icc (0 : ℝ) 1) :
    tent n x = max 0 (1 - |2 ^ (n + 2) * (x : ℝ) - 3|) := rfl

theorem tent_tentPt (n : ℕ) : tent n (tentPt n) = 1 := by
  rw [tent_apply]
  have : (2 : ℝ) ^ (n + 2) * (3 / 2 ^ (n + 2)) - 3 = 0 := by field_simp; ring
  simp [tentPt, this]

theorem tent_tentPt_ne {m n : ℕ} (h : m ≠ n) : tent m (tentPt n) = 0 := by
  rw [tent_apply]
  set a : ℝ := 2 ^ (m + 2) with ha
  set b : ℝ := 2 ^ (n + 2) with hb
  have hb0 : 0 < b := by positivity
  have key : 1 ≤ |a * (3 / b) - 3| := by
    rcases lt_or_gt_of_ne h with h | h
    · have hab : 2 * a ≤ b := by
        rw [ha, hb, ← pow_succ']
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      have : a * (3 / b) ≤ 3 / 2 := by
        rw [mul_div_assoc', div_le_iff₀ hb0]; nlinarith
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
    · have hab : 2 * b ≤ a := by
        rw [ha, hb, ← pow_succ']
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      have : 6 ≤ a * (3 / b) := by
        rw [mul_div_assoc', le_div_iff₀ hb0]; nlinarith
      rw [abs_of_nonneg (by linarith)]; linarith
  exact max_eq_left (by simp only [tentPt]; linarith)

theorem norm_tent_le (n : ℕ) : ‖tent n‖ ≤ 1 :=
  (ContinuousMap.norm_le _ zero_le_one).2 fun x => by
    rw [tent_apply, Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
    exact max_le zero_le_one (by linarith [abs_nonneg (2 ^ (n + 2) * (x : ℝ) - 3)])

theorem one_le_dist_tent {m n : ℕ} (h : m ≠ n) : 1 ≤ dist (tent m) (tent n) := by
  have := ContinuousMap.dist_apply_le_dist (f := tent m) (g := tent n) (tentPt m)
  rwa [tent_tentPt, tent_tentPt_ne (Ne.symm h), dist_comm, dist_zero_left, norm_one] at this

/-- **The static spacetime over `C([0, 1], ℝ)` is not causally compact**: `J((0,0),(2,0))`
contains the points `(1, tent n)`, pairwise at distance `≥ 1`. The space is separable and
complete, not proper. -/
theorem tentStatic_not_causallyCompact :
    ¬ (staticCausality C(Icc (0 : ℝ) 1, ℝ)).CausallyCompact := by
  intro hK
  set x : ℕ → ℝ × C(Icc (0 : ℝ) 1, ℝ) := fun n => (1, tent n) with hx'
  have hx : ∀ n, x n ∈ (staticCausality C(Icc (0 : ℝ) 1, ℝ)).diamond ⊤ (0, 0) (2, 0) := fun n => by
    rw [Causality.mem_diamond, staticCausality.le_top_iff, staticCausality.le_top_iff]
    refine ⟨?_, ?_⟩
    · show dist (0 : C(Icc (0 : ℝ) 1, ℝ)) (tent n) ≤ 1 - 0
      rw [dist_zero_left]
      linarith [norm_tent_le n]
    · show dist (tent n) 0 ≤ 2 - 1
      rw [dist_zero_right]
      linarith [norm_tent_le n]
  obtain ⟨y, -, φ, hφ, hlim⟩ := (hK (0, 0) (2, 0)).tendsto_subseq hx
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hlim.cauchySeq 1 one_pos
  have h1 := hN (N + 1) (by omega) N le_rfl
  have h2 : 1 ≤ dist (x (φ (N + 1))) (x (φ N)) :=
    (one_le_dist_tent (hφ (Nat.lt_succ_self N)).ne').trans
      (by rw [Prod.dist_eq]; exact le_max_right _ _)
  simp only [Function.comp] at h1
  linarith

/-- **`rem:causal_completeness_slightly_weaker` for the curve reading (b), "not conversely"**: a
second countable `T2` causal, tarentin, strongly causal, causally arc-connected, absolutely minimal
spacetime with `J^±(p) ≠ {p}` which is causally complete for curves and not causally compact. -/
theorem not_causallyCompleteCurves_imp_causallyCompact :
    ¬ ∀ (N : Type) [TopologicalSpace N] [T2Space N] [SecondCountableTopology N] (D : Causality N),
      D.IsCausal → D.Tarentin →
      D.StronglyCausal → D.CausallyArcConnected → D.AbsolutelyMinimal →
      (∀ p, D.Jminus ⊤ {p} ≠ {p}) → (∀ p, D.Jplus ⊤ {p} ≠ {p}) → D.CausallyCompleteCurves →
      D.CausallyCompact := fun h =>
  tentStatic_not_causallyCompact (h (ℝ × C(Icc (0 : ℝ) 1, ℝ)) (staticCausality _)
    staticCausality.isCausal
    staticCausality.tarentin staticCausality.stronglyCausal staticCausality.causallyArcConnected
    staticCausality.absolutelyMinimal staticCausality.Jminus_ne_singleton
    staticCausality.Jplus_ne_singleton staticCausality.causallyCompleteCurves)

/-! ### Reading (b) is not trivial: the half-plane -/

/-- The half-line `]0, ∞[` is geodesic, by the affine segments. -/
instance geodesicSpace_Ioi_zero : GeodesicSpace (Ioi (0 : ℝ)) where
  exists_geodesic x y := by
    have hpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < (x : ℝ) + t * ((y : ℝ) - x) := fun t ht => by
      have hx : (0 : ℝ) < x := x.2
      have hy : (0 : ℝ) < y := y.2
      rcases ht.2.lt_or_eq with h1 | h1
      · nlinarith [mul_pos (sub_pos.2 h1) hx, mul_nonneg ht.1 hy.le]
      · subst h1; linarith
    have hcl : ∀ s : ℝ, max 0 (min s 1) ∈ Icc (0 : ℝ) 1 := fun s =>
      ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
    refine ⟨fun s => ⟨(x : ℝ) + max 0 (min s 1) * ((y : ℝ) - x), mem_Ioi.2 (hpos _ (hcl s))⟩,
      Subtype.ext (by simp), Subtype.ext (by simp), fun s hs s' hs' => ?_⟩
    rw [Subtype.dist_eq, Subtype.dist_eq, Real.dist_eq, Real.dist_eq]
    dsimp only
    rw [min_eq_left hs.2,
      min_eq_left hs'.2, max_eq_right hs.1, max_eq_right hs'.1,
      show (x : ℝ) + s * (y - x) - (x + s' * (y - x)) = (s - s') * (y - x) by ring, abs_mul,
      abs_sub_comm (y : ℝ)]

/-- The null ray `τ ↦ (τ, 1 − τ)`, `τ < 1`, of the half-plane `ℝ × ]0, ∞[`, running into its
boundary at time `1`. -/
noncomputable def nullRay (τ : ℝ) : ℝ × Ioi (0 : ℝ) :=
  (τ, if h : τ < 1 then ⟨1 - τ, mem_Ioi.2 (sub_pos.2 h)⟩ else ⟨1, mem_Ioi.2 one_pos⟩)

theorem nullRay_snd {τ : ℝ} (h : τ < 1) : ((nullRay τ).2 : ℝ) = 1 - τ := by
  simp [nullRay, h]

/-- The null ray is a causal curve over `]-∞, 1[`. -/
theorem nullRay_causalCurveIn : (staticCausality (Ioi (0 : ℝ))).CausalCurveIn ⊤ (Iio 1) nullRay := by
  refine ⟨⟨0, by norm_num⟩, ordConnected_Iio, fun a ha b hb => ?_⟩
  refine staticCausality.causalCurveOn_graph (γ := fun τ => (nullRay τ).2)
    ⟨fun τ hτ τ' hτ' => ?_, fun _ _ => trivial⟩
  have h1 : τ < 1 := lt_of_le_of_lt hτ.2 hb
  have h2 : τ' < 1 := lt_of_le_of_lt hτ'.2 hb
  rw [Subtype.dist_eq, Real.dist_eq, nullRay_snd h1, nullRay_snd h2, one_mul,
    show 1 - τ - (1 - τ') = -(τ - τ') by ring, abs_neg]

/-- **The null ray is inextensible**: an extension would be continuous at the supremum of the
reparametrised parameters, where its space coordinate would vanish. -/
theorem nullRay_inextensible : (staticCausality (Ioi (0 : ℝ))).Inextensible ⊤ (Iio 1) nullRay := by
  refine ⟨nullRay_causalCurveIn, ?_⟩
  rintro ⟨I', c', hcurve, ⟨φ, hφ, hφmaps, hφoc, hφeq⟩, ⟨t', ht', hgrow⟩⟩
  have hI0 : (0 : ℝ) ∈ Iio 1 := by norm_num
  have htime : ∀ x y : ℝ × Ioi (0 : ℝ), (staticCausality (Ioi (0 : ℝ))).le ⊤ x y → x.1 ≤ y.1 :=
    fun x y h => by
      have := staticCausality.le_top_iff.1 h
      linarith [dist_nonneg (x := x.2) (y := y.2)]
  -- `t'` lies above the whole reparametrised curve
  have habove : ∀ τ ∈ Iio (1 : ℝ), φ τ < t' := by
    intro τ hτ
    by_contra hle
    push Not at hle
    by_cases hbelow : ∀ σ ∈ Iio (1 : ℝ), t' < φ σ
    · set σ := min ((c' t').1 - 1) 0 with hσ
      have hσI : σ ∈ Iio (1 : ℝ) :=
        show σ < 1 from lt_of_le_of_lt (min_le_right _ _) (by norm_num : (0 : ℝ) < 1)
      have := htime _ _ (hcurve.le_of_le ht' (hφmaps hσI) (hbelow σ hσI).le)
      rw [hφeq σ hσI] at this
      have : (c' t').1 ≤ σ := this
      linarith [min_le_left ((c' t').1 - 1) 0]
    · push Not at hbelow
      obtain ⟨σ, hσ, hσt⟩ := hbelow
      obtain ⟨w, hw, hwt⟩ := hφoc.out (mem_image_of_mem φ hσ) (mem_image_of_mem φ hτ) ⟨hσt, hle⟩
      exact hgrow w hw (by rw [← hwt, hφeq w hw])
  have hne : (φ '' Iio (1 : ℝ)).Nonempty := ⟨φ 0, mem_image_of_mem φ hI0⟩
  have hbdd : BddAbove (φ '' Iio (1 : ℝ)) := ⟨t', by rintro _ ⟨τ, hτ, rfl⟩; exact (habove τ hτ).le⟩
  set m := sSup (φ '' Iio (1 : ℝ)) with hm
  have h0m : φ 0 < m := lt_of_lt_of_le (hφ hI0 (show (1 / 2 : ℝ) ∈ Iio 1 by norm_num)
    (by norm_num)) (le_csSup hbdd (mem_image_of_mem φ (by norm_num)))
  have hmt : m ≤ t' := csSup_le hne fun _ ⟨τ, hτ, h⟩ => h ▸ (habove τ hτ).le
  have hφ0 : φ 0 ∈ I' := hφmaps hI0
  have hmI : m ∈ I' := hcurve.ordConnected.out hφ0 ht' ⟨h0m.le, hmt⟩
  -- every parameter below `m` is reparametrised
  have hIco : Ico (φ 0) m ⊆ φ '' Iio (1 : ℝ) := by
    intro u hu
    obtain ⟨_, ⟨τ, hτ, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup hne hu.2
    exact hφoc.out (mem_image_of_mem φ hI0) (mem_image_of_mem φ hτ) ⟨hu.1, hlt.le⟩
  -- along the null ray, time plus space is `1`, and this passes to the limit `m`
  set g : ℝ → ℝ := fun u => (c' u).1 + ((c' u).2 : ℝ) with hg
  have hco : ContinuousOn c' (Icc (φ 0) m) :=
    (hcurve.curve _ hφ0 _ hmI).continuousOn (staticCausality (Ioi (0 : ℝ))).isRelFamily_le
  have hgc : ContinuousOn g (Icc (φ 0) m) :=
    (continuous_fst.comp_continuousOn hco).add
      (continuous_subtype_val.comp_continuousOn (continuous_snd.comp_continuousOn hco))
  set P : Set ℝ := Icc (φ 0) m ∩ g ⁻¹' {1} with hP
  have hPc : IsClosed P := hgc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hsub : Ico (φ 0) m ⊆ P := by
    intro u hu
    obtain ⟨τ, hτ, rfl⟩ := hIco hu
    refine ⟨Ico_subset_Icc_self hu, ?_⟩
    show (c' (φ τ)).1 + ((c' (φ τ)).2 : ℝ) = 1
    rw [hφeq τ hτ, nullRay_snd hτ]
    simp [nullRay]
  have hmP : m ∈ P := by
    have := closure_minimal hsub hPc
    rw [closure_Ico h0m.ne] at this
    exact this ⟨h0m.le, le_rfl⟩
  have hgm : (c' m).1 + ((c' m).2 : ℝ) = 1 := hmP.2
  -- the time of `c' m` is at least `1`
  have hT : 1 ≤ (c' m).1 := by
    refine le_of_forall_lt fun r hr => ?_
    set τ := (r + 1) / 2 with hτ
    have hτI : τ ∈ Iio (1 : ℝ) := show τ < 1 by rw [hτ]; linarith
    have := htime _ _ (hcurve.le_of_le (hφmaps hτI) hmI (le_csSup hbdd (mem_image_of_mem φ hτI)))
    rw [hφeq τ hτI] at this
    have : τ ≤ (c' m).1 := this
    linarith
  have hpos : (0 : ℝ) < (c' m).2 := (c' m).2.2
  linarith

/-- **Finding: reading (b) is not trivial.** The half-plane `ℝ × ]0, ∞[` — the causality of
curves of an open subset of 1+1 Minkowski space, causal, causally arc-connected, strongly causal,
absolutely minimal — is not causally complete: the null ray running into the boundary is bounded
above by `(5, 1)` and has no supremum on itself. -/
theorem halfPlane_not_causallyCompleteCurves :
    ¬ (staticCausality (Ioi (0 : ℝ))).CausallyCompleteCurves := by
  intro h
  have hb : ∀ a ∈ nullRay '' Iio 1, (staticCausality (Ioi (0 : ℝ))).le ⊤ a (5, ⟨1, mem_Ioi.2 one_pos⟩) := by
    rintro _ ⟨τ, hτ, rfl⟩
    rw [staticCausality.le_top_iff, Subtype.dist_eq, Real.dist_eq, nullRay_snd hτ]
    show |1 - τ - 1| ≤ 5 - τ
    rw [show 1 - τ - 1 = -τ by ring, abs_neg]
    rcases le_total 0 τ with h0 | h0
    · rw [abs_of_nonneg h0]; linarith [show τ < 1 from hτ]
    · rw [abs_of_nonpos h0]; linarith
  obtain ⟨_, ⟨σ, hσ, rfl⟩, hub, -⟩ := (h _ _ nullRay_inextensible).1 _ subset_rfl
    ⟨nullRay 0, 0, by norm_num, rfl⟩ ⟨_, hb⟩
  have hσ1 : σ < 1 := hσ
  have hτI : (σ + 1) / 2 ∈ Iio (1 : ℝ) := show (σ + 1) / 2 < 1 by linarith
  have := staticCausality.le_top_iff.1 (hub _ ⟨_, hτI, rfl⟩)
  have : (nullRay ((σ + 1) / 2)).1 ≤ (nullRay σ).1 := by
    linarith [dist_nonneg (x := (nullRay ((σ + 1) / 2)).2) (y := (nullRay σ).2)]
  have : (σ + 1) / 2 ≤ σ := this
  linarith

/-- The half-plane satisfies every hypothesis of `causallyCompleteCurves_of_causallyCompact` but
causal compactness, which it therefore lacks (kb/0011: those hypotheses do not force
completeness by themselves). -/
theorem halfPlane_hypotheses :
    (staticCausality (Ioi (0 : ℝ))).Tarentin ∧ (staticCausality (Ioi (0 : ℝ))).IsCausal ∧
      (staticCausality (Ioi (0 : ℝ))).CausallyArcConnected ∧
      (staticCausality (Ioi (0 : ℝ))).StronglyCausal ∧
      (staticCausality (Ioi (0 : ℝ))).AbsolutelyMinimal ∧
      ¬ (staticCausality (Ioi (0 : ℝ))).CausallyCompact :=
  ⟨staticCausality.tarentin, staticCausality.isCausal, staticCausality.causallyArcConnected,
    staticCausality.stronglyCausal, staticCausality.absolutelyMinimal, fun hK =>
      halfPlane_not_causallyCompleteCurves (Causality.causallyCompleteCurves_of_causallyCompact
        staticCausality.tarentin staticCausality.isCausal hK staticCausality.causallyArcConnected
        staticCausality.Jminus_ne_singleton staticCausality.Jplus_ne_singleton)⟩

/-- On the same half-plane reading (a) holds: every causal curve is Dedekind-complete for bounds
taken on itself. -/
theorem halfPlane_nullRay_dedekindComplete :
    (staticCausality (Ioi (0 : ℝ))).DedekindComplete (nullRay '' Iio 1) :=
  nullRay_causalCurveIn.dedekindComplete_image staticCausality.isCausal
    staticCausality.isClosed_Jminus_top

/-! ### Sanity: the timelike line and Minkowski space -/

theorem timelikeLine_causallyConnectedCurves : timelikeLine.CausallyConnectedCurves :=
  fun p q hpq => ⟨univ, id, timelikeLine_inextensible_id, p, trivial, q, trivial,
    (timelikeLine_le.1 hpq).1, rfl, rfl⟩

/-- The timelike line is causally complete, through the remark's theorem: its hypotheses are
satisfiable. -/
theorem timelikeLine_causallyCompleteCurves : timelikeLine.CausallyCompleteCurves :=
  Causality.causallyCompleteCurves_of_causallyCompact timelikeLine_tarentin timelikeLine_isCausal
    timelikeLine_globallyHyperbolic.2 timelikeLine_causallyArcConnected timelikeLine_Jminus_ne
    timelikeLine_Jplus_ne

variable {n : ℕ}

/-- **Minkowski space is causally connected** (DEC-20), every `n`; the literal definition fails
for `n ≥ 1` (`minkowski_not_causallyConnected`). -/
theorem minkowski_causallyConnectedCurves : (minkowski n).CausallyConnectedCurves :=
  staticCausality.causallyConnectedCurves

/-- **Minkowski space is causally complete**, every `n`. -/
theorem minkowski_causallyCompleteCurves : (minkowski n).CausallyCompleteCurves :=
  staticCausality.causallyCompleteCurves

/-- Minkowski space satisfies the hypotheses of `causallyCompleteCurves_of_causallyCompact`. -/
theorem minkowski_causallyCompleteCurves' : (minkowski n).CausallyCompleteCurves :=
  Causality.causallyCompleteCurves_of_causallyCompact minkowski_tarentin minkowski_isCausal
    minkowski_globallyHyperbolic.2 minkowski_causallyArcConnected
    staticCausality.Jminus_ne_singleton staticCausality.Jplus_ne_singleton

/-- In `ℝ^{1,n}`, `n ≥ 1`, through `p ≤ q` passes an inextensible causal curve whose image is a
subset causal chain which is not maximal. Non-maximality holds because `ℝ^{1,n}` has no maximal
chain of `Causal.Chains` at all (`minkowski_not_isMaximalChain`), not because of the curve. -/
theorem minkowski_curveChain_not_maximal (hn : 0 < n) {p q : Minkowski n}
    (hpq : (minkowski n).le ⊤ p q) :
    ∃ c : ℝ → Minkowski n, (minkowski n).Inextensible ⊤ univ c ∧ p ∈ range c ∧ q ∈ range c ∧
      (minkowski n).IsCausalChain (range c) ∧ ¬ (minkowski n).IsMaximalChain (range c) := by
  obtain ⟨Γ, hΓ, -, hp, hq⟩ := staticCausality.exists_inextensible_graph hpq
  have he : IsEmbedding (fun τ : ℝ => ((τ, Γ τ) : Minkowski n)) :=
    IsEmbedding.of_leftInverse (f := Prod.fst) (fun _ => rfl) continuous_fst hΓ.1.continuous
  exact ⟨_, hΓ, ⟨p.1, Prod.ext rfl hp⟩, ⟨q.1, Prod.ext rfl hq⟩,
    hΓ.1.isCausalChain_range he, minkowski_not_isMaximalChain hn _⟩

end Causal
