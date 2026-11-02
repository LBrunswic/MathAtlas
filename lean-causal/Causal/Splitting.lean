import Causal.CauchyDiamond
import Causal.Flat.IsomCausal
import Mathlib.Dynamics.Flow
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Geometry.Manifold.IntegralCurve.Transform
import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Topology.ShrinkingLemma
import Mathlib.Topology.MetricSpace.Thickening

/-!
# The splitting `M ≅ S × ℝ` along a Cauchy surface, from a causal flow

`bprop:splitting` — `GHFspace.tex:2459` (labelled; original l.2426), **not marked**: Barbot cites
it (Beem–Ehrlich); the flow it needs exists on every flat spacetime (target 4,
`Flat.flat_hasChronalCausalFlow`, proved, no `sorry` in this file), but the Cauchy slices and the
last sentence are not proved in general (SCOPE). It is proved in full on Minkowski
space (`minkowski_splitting_cauchy_slices`). The "Moreover" of `theo:geroch_sing` —
`ETT.tex:1778` — is the abstract theorem of this file, unmarked (it is ETT's label, and its proof is
replaced, see SCOPE). Barbot's `𝐌ⁿ` is `Minkowski d` with `n = d + 1`.

> $M$ is homeomorphic to $ S \times {\mathbb R}$, where every $S \times \{ \ast \}$ are Cauchy
> hypersurfaces. Any nonspacelike geodesic in $\widetilde{M}$ intersect $\widetilde{S}$.
> (`bprop:splitting`, `GHFspace.tex:2461–2463`; "See \cite{beem}", l.2467)

> Moreover, if $\Sigma$ is a Cauchy surface of $M$, then $M$ is homeomorphic to
> $\Sigma\times \RR$. (`theo:geroch_sing`, `ETT.tex:1778`)

> Since $X$ is non-singular, $\psi$ is a local diffeomorphism. Moreover $X$ is causal, so the curves
> $c_x:t\mapsto \psi(x,t)$, $x\in \Sigma$, are inextensible causal curves. They therefore meet
> $\Sigma$ exactly once. Hence $\psi$ is bijective, and so it is a diffeomorphism.
> (`ETT.tex:1792–1795`)

**Target 1.** `IsCausalFlow C φ`: `φ : Flow ℝ M` (mathlib), orbits inextensible causal curves over
`ℝ`, no stationary point. `IsChronalFlow C φ`: orbits chronal curves.
**Target 2.** `IsCausalFlow.exists_isCauchySplitting`: `C` causal, `S` an acausal Cauchy surface,
`J^±(S)` closed ⟹ `ψ(x, t) = φ t x` is a homeomorphism `S × ℝ ≃ₜ M` with `IsCauchySplitting`.
The closedness is necessary (`isClosed_iff_exists_isCauchySplitting`) and automatic for a chronal
flow (`exists_isCauchySplitting_of_isChronalFlow`); pointwise criteria `isClosed_Jplus_of_nhds`,
`isClosed_Jminus_of_nhds` (flow) and `isClosed_Jplus_of_forall_exists(_lt)`,
`isClosed_Jminus_of_forall_exists(_lt)` (no flow).
**Target 3.** `Jplus_diff_eq_Iplus`, `Jminus_diff_eq_Iminus`, `isOpen_Jplus_diff_and_Jminus_diff`,
`isLocallyCauchyTwoSided_of_threads`: in an open `U`, under push-up, with chronal threads;
pointwise variants `isOpen_Jplus_diff_of_forall`, `isOpen_Jminus_diff_of_forall`,
`isLocallyCauchyTwoSided_of_pointwise` (a thread or a neighbourhood inside the side, point by point).
**Target 4.** `Flat.flat_hasChronalCausalFlow`: a flat spacetime (`T2`, second countable) has a
chronal causal flow — the flow of a smooth future timelike field (glued from the charts' `e₀` by
a smooth partition of unity), rescaled to be complete. Its ODE input, the pure-ODE lemma
`exists_complete_rescaling_continuous` (completeness by rescaling and continuous dependence on a
manifold), is proved (namespace `ODEFlow`); causal inputs: `Causality.inextensible_of_flow` (orbits of a fixed-point-free
flow, causal over `ℝ`, are inextensible), `Flat.FlowField.chronalCurveOn_of_chartVelocity`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `M` globally hyperbolic flat (`bprop:splitting`), singular flat (`theo:geroch_sing`) | ⚠ weakened: any causality, `C.IsCausal` |
| `S`, `Σ` a Cauchy (hyper)surface | ✓ carried: `IsCauchySurface` (DEC-14); ⚠ strengthened: `IsAcausal S` (a consequence under `CurvesExtend`, `IsCauchySurface.isAcausal`) |
| the flow of a causal non-singular `C¹` field (`lem:vecteur`) | ⚠ strengthened (named, kb/0012): `IsCausalFlow` — an abstract continuous flow with inextensible causal orbits, no smoothness |
| "`ψ` is a local diffeomorphism" | ⚠ strengthened (named, kb/0012): `J^±(S)` closed — necessary and sufficient (`isClosed_iff_exists_isCauchySplitting`); derived for a chronal flow; pointwise criteria `isClosed_Jplus_of_forall_exists(_lt)` |
| separation, countability | ⚠ weakened: none for target 2; `T2Space` for the threads of a chronal flow in `U ≠ M` |
| target 3: push-up, `S ∩ U` acausal and Cauchy in `U` | ✓ carried; ⚠ strengthened: chronology on `S ∩ U`, and at each point off `S` a chronal thread (named; false at BTZ points) or, in the pointwise variant, a chronal thread **or** a neighbourhood inside the side |

## SCOPE (disclosed)

* **The slices.** For an arbitrary causal flow `ψ(S × {t}) = φ_t(S)` is **not** a Cauchy surface
  (`minkowski_skew_slice_not_isCauchySurface`): `bprop:splitting`'s Cauchy slices need a chosen
  flow. They are Cauchy when each `φ_t` preserves inextensible curves
  (`isCauchySurface_flow_image`), and on Minkowski space for the time translation.
* **ETT's proof of the "Moreover"** concludes from "`ψ` is a local diffeomorphism", which needs `Σ`
  smooth and transverse to `X`; a topological Cauchy surface is neither. The topological proof here
  is continuity of the hitting time, equivalent to `J^±(Σ)` closed; `lem:Sigma_separe` derives that
  closedness *from* the splitting, so it is an independent obligation where the flow is not chronal
  (BTZ points). **For a non-chronal flow the model must prove `IsClosed (J^±(Σ))` itself**: the
  flow criterion `isClosed_Jplus_of_nhds` needs `J⁻(φ ε p) ∈ 𝓝 p` at every `p ∉ J⁺(Σ)`, which
  fails at a BTZ point (there `J⁻(φ ε p)` is a half-line of the singular line). The flow-free
  criteria `isClosed_Jplus_of_forall_exists` / `isClosed_Jplus_of_forall_exists_lt` only ask, at
  each `p ∉ J⁺(Σ)`, for **some** `r ∉ J⁺(Σ)` with `J⁻(r) ∈ 𝓝 p` (e.g. `p ≪ r`, a regular point
  `r`); that is what a model with BTZ lines can try to discharge.
* **Target 3's equality is false at a point with `I⁻_U(p) = ∅`** above `S` (a BTZ point): on the
  lightlike line, with `{0}` an acausal Cauchy surface, push-up and causality all verified,
  `J⁺({0}) ∖ {0} = ]0, ∞[` and `I⁺({0}) = ∅` (`lightlikeLine_Jplus_diff_ne_Iplus`) — every
  hypothesis of `Jplus_diff_eq_Iplus` but the threads holds. The equality is proved where chronal
  threads exist. **Two-sidedness in a chart containing a BTZ point off `S` is the model's
  obligation**: `isOpen_Jplus_diff_of_forall` / `isLocallyCauchyTwoSided_of_pointwise` take, at
  each point of a side, a chronal thread **or** a neighbourhood inside the side, the latter being
  what the model supplies at BTZ points (on the lightlike line the sides are open).
* `Causal.CompactCauchy` is not imported:
  `isLocallyCauchyTwoSided_of_threads` concludes the unfolded body of `IsLocallyCauchyTwoSided`.
* **Target 4's ODE input is proved here, not in mathlib**: `exists_complete_rescaling_continuous`
  (for a smooth field on a σ-compact Hausdorff manifold, a positive smooth `f` with `f • v`
  complete and its global integral curves continuous in `(t, x)`); mathlib at this pin has neither
  completeness by rescaling nor continuous dependence on a manifold. Route: a locally finite chart
  cover with a uniform inner margin, `f` small on each ball, Picard–Lindelöf on `[-1, 1]` in charts
  (mathlib's local flow, re-proved with its confinement to the ball), uniqueness, doubling.
* Barbot's last sentence (geodesics of `M̃` meet `S̃`) is not treated.
* Non-vacuity: Minkowski time translation (`minkowski_hasChronalCausalFlow`, flat:
  `Flat.flatCausality_self_hasChronalCausalFlow`); `hinv` of `isCauchySurface_flow_image` for it
  (`minkowskiTimeFlow_inextensible`, `minkowski_isCauchySurface_flow_image`); the timelike line for
  target 3 (`timelikeLine_target3`, and `hloc` of `isLocallyCauchyTwoSided_of_threads`:
  `timelikeLine_hloc`).
* `set_option backward.isDefEq.respectTransparency false in` on `hasMFDerivAt_symm_comp` (the
  chart-transport lemma): the strict library's first `set_option`, disclosed at graduation.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Function

universe u

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable (C : Causality M)

/-! ### Target 1: causal flows -/

/-- **A causal flow** of `C`: a continuous `ℝ`-action on `M` (mathlib's `Flow ℝ M`) whose orbits
`t ↦ φ t x` are inextensible future causal curves over `ℝ`, and which has no stationary point. -/
structure IsCausalFlow (φ : Flow ℝ M) : Prop where
  inextensible : ∀ x : M, C.Inextensible ⊤ univ (fun t => φ t x)
  nonstationary : ∀ x : M, ∃ t : ℝ, φ t x ≠ x

/-- **A chronal flow**: every orbit is a future chronal curve over every segment. -/
def IsChronalFlow (φ : Flow ℝ M) : Prop :=
  ∀ (x : M) (a b : ℝ), C.ChronalCurveOn ⊤ (fun t => φ t x) a b

variable {C} {φ : Flow ℝ M} {S : Set M}

theorem IsCausalFlow.le (hφ : C.IsCausalFlow φ) (x : M) {s t : ℝ} (hst : s ≤ t) :
    C.le ⊤ (φ s x) (φ t x) :=
  (hφ.inextensible x).1.le_of_le trivial trivial hst

theorem IsChronalFlow.lt (hφ : C.IsChronalFlow φ) (x : M) {s t : ℝ} (hst : s < t) :
    C.lt ⊤ (φ s x) (φ t x) :=
  (hφ x s t).lt_of_lt le_rfl hst le_rfl

/-- In a causal spacetime a causal flow has no periodic orbit: `φ t x = x` forces `t = 0`. -/
theorem IsCausalFlow.eq_zero_of_apply_eq (hcaus : C.IsCausal) (hφ : C.IsCausalFlow φ) {x : M}
    {t : ℝ} (h : φ t x = x) : t = 0 := by
  -- reduce to a positive period
  have key : ∀ T : ℝ, 0 < T → φ T x = x → False := by
    intro T hT hTx
    -- the orbit is constant on `[0, T]`
    have hIcc : ∀ s ∈ Icc 0 T, φ s x = x := by
      intro s hs
      have h1 : C.le ⊤ x (φ s x) := by
        have := hφ.le x hs.1; rwa [Flow.map_zero_apply] at this
      have h2 : C.le ⊤ (φ s x) x := by
        have := hφ.le x hs.2; rwa [hTx] at this
      exact hcaus h2 h1
    -- and `T`-periodic
    have hper : Periodic (fun s => φ s x) T := fun s => by
      show φ (s + T) x = φ s x
      rw [Flow.map_add, hTx]
    obtain ⟨t', ht'⟩ := hφ.nonstationary x
    obtain ⟨y, hy, hyeq⟩ := hper.exists_mem_Ico₀ hT t'
    exact ht' (hyeq.trans (hIcc y (Ico_subset_Icc_self hy)))
  rcases lt_trichotomy t 0 with ht | ht | ht
  · exfalso
    refine key (-t) (neg_pos.2 ht) ?_
    conv_lhs => rw [← h]
    rw [← Flow.map_add, neg_add_cancel, Flow.map_zero_apply]
  · exact ht
  · exact (key t ht h).elim

/-- In a causal spacetime the orbits of a causal flow are injective. -/
theorem IsCausalFlow.injective (hcaus : C.IsCausal) (hφ : C.IsCausalFlow φ) (x : M) :
    Injective fun t => φ t x := by
  intro s t hst
  simp only at hst
  have : φ (s - t) (φ t x) = φ t x := by
    rw [← Flow.map_add, sub_add_cancel, hst]
  exact sub_eq_zero.1 (hφ.eq_zero_of_apply_eq hcaus this)

/-! ### Target 2: the splitting -/

/-- Every orbit meets a Cauchy surface. -/
theorem IsCausalFlow.exists_apply_mem (hφ : C.IsCausalFlow φ) (hS : C.IsCauchySurface S)
    (p : M) : ∃ t : ℝ, φ t p ∈ S := by
  obtain ⟨_, ⟨⟨t, -, rfl⟩, ht⟩, -⟩ := hS univ _ (hφ.inextensible p)
  exact ⟨t, ht⟩

/-- Every orbit meets a Cauchy surface at exactly one time. -/
theorem IsCausalFlow.existsUnique_apply_mem (hcaus : C.IsCausal) (hφ : C.IsCausalFlow φ)
    (hS : C.IsCauchySurface S) (p : M) : ∃! t : ℝ, φ t p ∈ S := by
  obtain ⟨y, -, huniq⟩ := hS univ _ (hφ.inextensible p)
  obtain ⟨t, ht⟩ := hφ.exists_apply_mem hS p
  refine ⟨t, ht, fun t' ht' => hφ.injective hcaus p ?_⟩
  exact (huniq _ ⟨⟨t', trivial, rfl⟩, ht'⟩).trans (huniq _ ⟨⟨t, trivial, rfl⟩, ht⟩).symm

/-- **The hitting time**: the time at which the orbit of `p` meets `S`. -/
noncomputable def IsCausalFlow.hitTime (hφ : C.IsCausalFlow φ) (hS : C.IsCauchySurface S)
    (p : M) : ℝ :=
  Classical.choose (hφ.exists_apply_mem hS p)

theorem IsCausalFlow.apply_hitTime_mem (hφ : C.IsCausalFlow φ) (hS : C.IsCauchySurface S)
    (p : M) : φ (hφ.hitTime hS p) p ∈ S :=
  Classical.choose_spec (hφ.exists_apply_mem hS p)

theorem IsCausalFlow.hitTime_eq (hcaus : C.IsCausal) (hφ : C.IsCausalFlow φ)
    (hS : C.IsCauchySurface S) {p : M} {t : ℝ} (ht : φ t p ∈ S) : hφ.hitTime hS p = t :=
  (hφ.existsUnique_apply_mem hcaus hS p).unique (hφ.apply_hitTime_mem hS p) ht

/-- Along an orbit, the causal future of an acausal `S` is the half-orbit after the hitting time:
`φ s p ∈ J⁺(S) ↔ t ≤ s`, where `φ t p ∈ S`. -/
theorem IsCausalFlow.apply_mem_Jplus_iff (hcaus : C.IsCausal) (hφ : C.IsCausalFlow φ)
    (hac : C.IsAcausal S) {p : M} {t : ℝ} (ht : φ t p ∈ S) (s : ℝ) :
    φ s p ∈ C.Jplus ⊤ S ↔ t ≤ s := by
  constructor
  · rintro ⟨z, hz, hzs⟩
    by_contra hlt
    push Not at hlt
    have h1 : C.le ⊤ (φ s p) (φ t p) := hφ.le p hlt.le
    have h2 : z = φ t p := hac z hz _ ht (C.le_trans hzs h1)
    subst h2
    have h3 : φ s p = φ t p := hcaus h1 hzs
    exact hlt.ne (hφ.injective hcaus p h3)
  · intro hts
    exact ⟨_, ht, hφ.le p hts⟩

/-- `φ s p ∈ J⁻(S) ↔ s ≤ t`, where `φ t p ∈ S`. -/
theorem IsCausalFlow.apply_mem_Jminus_iff (hcaus : C.IsCausal) (hφ : C.IsCausalFlow φ)
    (hac : C.IsAcausal S) {p : M} {t : ℝ} (ht : φ t p ∈ S) (s : ℝ) :
    φ s p ∈ C.Jminus ⊤ S ↔ s ≤ t := by
  constructor
  · rintro ⟨z, hz, hsz⟩
    by_contra hlt
    push Not at hlt
    have h1 : C.le ⊤ (φ t p) (φ s p) := hφ.le p hlt.le
    have h2 : φ t p = z := hac _ ht z hz (C.le_trans h1 hsz)
    subst h2
    have h3 : φ s p = φ t p := hcaus hsz h1
    exact hlt.ne' (hφ.injective hcaus p h3)
  · intro hst
    exact ⟨_, ht, hφ.le p hst⟩

/-- **The hitting time is continuous** when `J^±(S)` are closed. -/
theorem IsCausalFlow.continuous_hitTime (hcaus : C.IsCausal) (hφ : C.IsCausalFlow φ)
    (hS : C.IsCauchySurface S) (hac : C.IsAcausal S)
    (hJp : IsClosed (C.Jplus ⊤ S)) (hJm : IsClosed (C.Jminus ⊤ S)) :
    Continuous (hφ.hitTime hS) := by
  have hcont : ∀ a : ℝ, Continuous fun q => φ a q := fun a => φ.continuous continuous_const
    continuous_id
  refine continuous_iff_continuousAt.2 fun p => tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · -- `a < τ(q)` iff `φ a q ∉ J⁺(S)`
    have hmem : ∀ q, a < hφ.hitTime hS q ↔ φ a q ∈ (C.Jplus ⊤ S)ᶜ := fun q => by
      rw [mem_compl_iff, hφ.apply_mem_Jplus_iff hcaus hac (hφ.apply_hitTime_mem hS q), not_le]
    have hopen : IsOpen {q | a < hφ.hitTime hS q} := by
      simp_rw [hmem]; exact hJp.isOpen_compl.preimage (hcont a)
    exact hopen.mem_nhds ha
  · have hmem : ∀ q, hφ.hitTime hS q < a ↔ φ a q ∈ (C.Jminus ⊤ S)ᶜ := fun q => by
      rw [mem_compl_iff, hφ.apply_mem_Jminus_iff hcaus hac (hφ.apply_hitTime_mem hS q), not_le]
    have hopen : IsOpen {q | hφ.hitTime hS q < a} := by
      simp_rw [hmem]; exact hJm.isOpen_compl.preimage (hcont a)
    exact hopen.mem_nhds ha

/-- **The splitting of a causal flow along a Cauchy surface**: `ψ (x, t) = φ t x`. -/
noncomputable def IsCausalFlow.splitting (hcaus : C.IsCausal) (hφ : C.IsCausalFlow φ)
    (hS : C.IsCauchySurface S) (hac : C.IsAcausal S)
    (hJp : IsClosed (C.Jplus ⊤ S)) (hJm : IsClosed (C.Jminus ⊤ S)) : S × ℝ ≃ₜ M where
  toFun q := φ q.2 q.1
  invFun p := (⟨φ (hφ.hitTime hS p) p, hφ.apply_hitTime_mem hS p⟩, -hφ.hitTime hS p)
  left_inv := by
    rintro ⟨x, t⟩
    have hx : φ (-t) (φ t x) ∈ S := by
      rw [← Flow.map_add, neg_add_cancel, Flow.map_zero_apply]; exact x.2
    have hτ := hφ.hitTime_eq hcaus hS hx
    simp only [hτ, neg_neg]
    refine Prod.ext (Subtype.ext ?_) rfl
    show φ (-t) (φ t x) = x
    rw [← Flow.map_add, neg_add_cancel, Flow.map_zero_apply]
  right_inv p := by
    show φ (-hφ.hitTime hS p) (φ (hφ.hitTime hS p) p) = p
    rw [← Flow.map_add, neg_add_cancel, Flow.map_zero_apply]
  continuous_toFun := φ.continuous continuous_snd (continuous_subtype_val.comp continuous_fst)
  continuous_invFun := by
    have hτ := hφ.continuous_hitTime hcaus hS hac hJp hJm
    exact (Continuous.subtype_mk (φ.continuous hτ continuous_id) _).prodMk hτ.neg

theorem IsCausalFlow.splitting_apply (hcaus : C.IsCausal) (hφ : C.IsCausalFlow φ)
    (hS : C.IsCauchySurface S) (hac : C.IsAcausal S)
    (hJp : IsClosed (C.Jplus ⊤ S)) (hJm : IsClosed (C.Jminus ⊤ S)) (x : S) (t : ℝ) :
    hφ.splitting hcaus hS hac hJp hJm (x, t) = φ t x := rfl

/-- **Target 2.** The splitting of a causal flow along an acausal Cauchy surface `S` with `J^±(S)`
closed is a Cauchy splitting. -/
theorem IsCausalFlow.isCauchySplitting (hcaus : C.IsCausal) (hφ : C.IsCausalFlow φ)
    (hS : C.IsCauchySurface S) (hac : C.IsAcausal S)
    (hJp : IsClosed (C.Jplus ⊤ S)) (hJm : IsClosed (C.Jminus ⊤ S)) :
    C.IsCauchySplitting S (hφ.splitting hcaus hS hac hJp hJm) where
  zero _ := Flow.map_zero_apply _ _
  mono x _ _ hst := hφ.le x hst

theorem IsCausalFlow.exists_isCauchySplitting (hcaus : C.IsCausal) (hφ : C.IsCausalFlow φ)
    (hS : C.IsCauchySurface S) (hac : C.IsAcausal S)
    (hJp : IsClosed (C.Jplus ⊤ S)) (hJm : IsClosed (C.Jminus ⊤ S)) :
    ∃ ψ : S × ℝ ≃ₜ M, (∀ (x : S) (t : ℝ), ψ (x, t) = φ t x) ∧ C.IsCauchySplitting S ψ :=
  ⟨_, fun _ _ => rfl, hφ.isCauchySplitting hcaus hS hac hJp hJm⟩

/-! ### A chronal flow closes `J^±(S)` -/

/-- **`J⁺(S)` is closed when the flow pushes past cones over neighbourhoods**: if, at every point
`p ∉ J⁺(S)`, `J⁻(φ ε p)` is a neighbourhood of `p` for `ε > 0`, then `J⁺(S)` is closed — a point of
its closure outside it would lie in the causal past of a later point of its orbit still outside
`J⁺(S)`. Pointwise, so that a model can discharge it chart by chart. -/
theorem IsCausalFlow.isClosed_Jplus_of_nhds (hcaus : C.IsCausal) (hφ : C.IsCausalFlow φ)
    (hS : C.IsCauchySurface S) (hac : C.IsAcausal S)
    (hnhds : ∀ p ∉ C.Jplus ⊤ S, ∀ ε : ℝ, 0 < ε → C.Jminus ⊤ {φ ε p} ∈ 𝓝 p) :
    IsClosed (C.Jplus ⊤ S) := by
  refine isClosed_of_closure_subset fun p hp => ?_
  by_contra hpJ
  set t := hφ.hitTime hS p
  have hiff := hφ.apply_mem_Jplus_iff hcaus hac (hφ.apply_hitTime_mem hS p)
  have ht : 0 < t := by
    by_contra h0
    push Not at h0
    exact hpJ (by simpa [Flow.map_zero_apply] using (hiff 0).2 h0)
  have hr : φ (t / 2) p ∉ C.Jplus ⊤ S := fun h => by
    have := (hiff _).1 h; linarith
  obtain ⟨q, hq1, ⟨z, hz, hzq⟩⟩ :=
    mem_closure_iff_nhds.1 hp _ (hnhds p hpJ (t / 2) (by linarith))
  have hq : C.le ⊤ q (φ (t / 2) p) := by simpa using hq1
  exact hr ⟨z, hz, C.le_trans hzq hq⟩

/-- **`J⁻(S)` is closed** when, at every point `p ∉ J⁻(S)`, `J⁺(φ ε p)` is a neighbourhood of `p`
for `ε < 0`. -/
theorem IsCausalFlow.isClosed_Jminus_of_nhds (hcaus : C.IsCausal) (hφ : C.IsCausalFlow φ)
    (hS : C.IsCauchySurface S) (hac : C.IsAcausal S)
    (hnhds : ∀ p ∉ C.Jminus ⊤ S, ∀ ε : ℝ, ε < 0 → C.Jplus ⊤ {φ ε p} ∈ 𝓝 p) :
    IsClosed (C.Jminus ⊤ S) := by
  refine isClosed_of_closure_subset fun p hp => ?_
  by_contra hpJ
  set t := hφ.hitTime hS p
  have hiff := hφ.apply_mem_Jminus_iff hcaus hac (hφ.apply_hitTime_mem hS p)
  have ht : t < 0 := by
    by_contra h0
    push Not at h0
    exact hpJ (by simpa [Flow.map_zero_apply] using (hiff 0).2 h0)
  have hr : φ (t / 2) p ∉ C.Jminus ⊤ S := fun h => by
    have := (hiff _).1 h; linarith
  obtain ⟨q, hq1, ⟨z, hz, hqz⟩⟩ :=
    mem_closure_iff_nhds.1 hp _ (hnhds p hpJ (t / 2) (by linarith))
  have hq : C.le ⊤ (φ (t / 2) p) q := by simpa using hq1
  exact hr ⟨z, hz, C.le_trans hq hqz⟩

/-- **A flow-free pointwise criterion for `J⁺(S)` closed**: if every `p ∉ J⁺(S)` has a
neighbourhood of the form `J⁻(r)` with `r ∉ J⁺(S)`, then `J⁺(S)` is closed (a point of the closure
lies in `J⁻(r)` near a point of `J⁺(S)`, so `r ∈ J⁺(S)`). Unlike `isClosed_Jplus_of_nhds`, `r` need
not lie on the orbit of `p`: at a BTZ point `p`, a regular `r` with `p ≪ r` may serve. -/
theorem isClosed_Jplus_of_forall_exists
    (h : ∀ p ∉ C.Jplus ⊤ S, ∃ r ∉ C.Jplus ⊤ S, C.Jminus ⊤ {r} ∈ 𝓝 p) :
    IsClosed (C.Jplus ⊤ S) := by
  refine isClosed_of_closure_subset fun p hp => ?_
  by_contra hpJ
  obtain ⟨r, hr, hnhds⟩ := h p hpJ
  obtain ⟨q, hq1, ⟨z, hz, hzq⟩⟩ := mem_closure_iff_nhds.1 hp _ hnhds
  have hq : C.le ⊤ q r := by simpa using hq1
  exact hr ⟨z, hz, C.le_trans hzq hq⟩

/-- **`J⁻(S)` closed, flow-free**: every `p ∉ J⁻(S)` has a neighbourhood `J⁺(r)`, `r ∉ J⁻(S)`. -/
theorem isClosed_Jminus_of_forall_exists
    (h : ∀ p ∉ C.Jminus ⊤ S, ∃ r ∉ C.Jminus ⊤ S, C.Jplus ⊤ {r} ∈ 𝓝 p) :
    IsClosed (C.Jminus ⊤ S) := by
  refine isClosed_of_closure_subset fun p hp => ?_
  by_contra hpJ
  obtain ⟨r, hr, hnhds⟩ := h p hpJ
  obtain ⟨q, hq1, ⟨z, hz, hqz⟩⟩ := mem_closure_iff_nhds.1 hp _ hnhds
  have hq : C.le ⊤ r q := by simpa using hq1
  exact hr ⟨z, hz, C.le_trans hq hqz⟩

/-- **`J⁺(S)` closed from chronological witnesses**: every `p ∉ J⁺(S)` is in the chronological
past of some `r ∉ J⁺(S)` (by openness of `I⁻(r)`). -/
theorem isClosed_Jplus_of_forall_exists_lt (h : ∀ p ∉ C.Jplus ⊤ S, ∃ r ∉ C.Jplus ⊤ S, C.lt ⊤ p r) :
    IsClosed (C.Jplus ⊤ S) :=
  isClosed_Jplus_of_forall_exists fun p hp => by
    obtain ⟨r, hr, hpr⟩ := h p hp
    exact ⟨r, hr, mem_of_superset (isOpen_Iminus.mem_nhds (by simpa using hpr))
      Iminus_subset_Jminus⟩

/-- **`J⁻(S)` closed from chronological witnesses**: every `p ∉ J⁻(S)` is in the chronological
future of some `r ∉ J⁻(S)`. -/
theorem isClosed_Jminus_of_forall_exists_lt
    (h : ∀ p ∉ C.Jminus ⊤ S, ∃ r ∉ C.Jminus ⊤ S, C.lt ⊤ r p) : IsClosed (C.Jminus ⊤ S) :=
  isClosed_Jminus_of_forall_exists fun p hp => by
    obtain ⟨r, hr, hrp⟩ := h p hp
    exact ⟨r, hr, mem_of_superset (isOpen_Iplus.mem_nhds (by simpa using hrp))
      Iplus_subset_Jplus⟩

/-- With chronal orbits, `J⁺(S)` is closed. -/
theorem IsCausalFlow.isClosed_Jplus (hcaus : C.IsCausal) (hφ : C.IsCausalFlow φ)
    (hch : C.IsChronalFlow φ) (hS : C.IsCauchySurface S) (hac : C.IsAcausal S) :
    IsClosed (C.Jplus ⊤ S) := by
  refine hφ.isClosed_Jplus_of_nhds hcaus hS hac fun p _ ε hε => ?_
  have hlt : C.lt ⊤ p (φ ε p) := by simpa [Flow.map_zero_apply] using hch.lt p hε
  refine mem_of_superset (isOpen_Iminus.mem_nhds (by simpa using hlt)) Iminus_subset_Jminus

/-- With chronal orbits, `J⁻(S)` is closed. -/
theorem IsCausalFlow.isClosed_Jminus (hcaus : C.IsCausal) (hφ : C.IsCausalFlow φ)
    (hch : C.IsChronalFlow φ) (hS : C.IsCauchySurface S) (hac : C.IsAcausal S) :
    IsClosed (C.Jminus ⊤ S) := by
  refine hφ.isClosed_Jminus_of_nhds hcaus hS hac fun p _ ε hε => ?_
  have hlt : C.lt ⊤ (φ ε p) p := by simpa [Flow.map_zero_apply] using hch.lt p hε
  refine mem_of_superset (isOpen_Iplus.mem_nhds (by simpa using hlt)) Iplus_subset_Jplus

/-- **Target 2 for a chronal flow**: no closedness hypothesis is needed. -/
theorem IsCausalFlow.exists_isCauchySplitting_of_isChronalFlow (hcaus : C.IsCausal)
    (hφ : C.IsCausalFlow φ) (hch : C.IsChronalFlow φ) (hS : C.IsCauchySurface S)
    (hac : C.IsAcausal S) :
    ∃ ψ : S × ℝ ≃ₜ M, (∀ (x : S) (t : ℝ), ψ (x, t) = φ t x) ∧ C.IsCauchySplitting S ψ :=
  hφ.exists_isCauchySplitting hcaus hS hac (hφ.isClosed_Jplus hcaus hch hS hac)
    (hφ.isClosed_Jminus hcaus hch hS hac)

/-- **The closedness hypotheses are necessary**: a Cauchy splitting along an acausal `S` closes
`J^±(S)` (`sigma_separe`). So, for a causal flow, the splitting along `S` exists iff `J^±(S)` are
closed. -/
theorem IsCausalFlow.isClosed_iff_exists_isCauchySplitting (hcaus : C.IsCausal)
    (hφ : C.IsCausalFlow φ) (hS : C.IsCauchySurface S) (hac : C.IsAcausal S) :
    (IsClosed (C.Jplus ⊤ S) ∧ IsClosed (C.Jminus ⊤ S)) ↔
      ∃ ψ : S × ℝ ≃ₜ M, (∀ (x : S) (t : ℝ), ψ (x, t) = φ t x) ∧ C.IsCauchySplitting S ψ := by
  constructor
  · rintro ⟨hJp, hJm⟩; exact hφ.exists_isCauchySplitting hcaus hS hac hJp hJm
  · rintro ⟨ψ, -, hψ⟩
    obtain ⟨-, -, h1, h2, -⟩ := sigma_separe hcaus hac hψ
    exact ⟨h1, h2⟩

/-- **`bprop:splitting`'s first assertion**, `M ≅ S × ℝ`, under a causal flow. -/
theorem IsCausalFlow.nonempty_homeomorph (hcaus : C.IsCausal) (hφ : C.IsCausalFlow φ)
    (hS : C.IsCauchySurface S) (hac : C.IsAcausal S)
    (hJp : IsClosed (C.Jplus ⊤ S)) (hJm : IsClosed (C.Jminus ⊤ S)) : Nonempty (S × ℝ ≃ₜ M) :=
  ⟨hφ.splitting hcaus hS hac hJp hJm⟩

/-! ### The slices -/

/-- The slice `ψ(S × {t})` of the flow splitting is `φ_t(S)`. -/
theorem IsCausalFlow.splitting_image_slice (hcaus : C.IsCausal) (hφ : C.IsCausalFlow φ)
    (hS : C.IsCauchySurface S) (hac : C.IsAcausal S)
    (hJp : IsClosed (C.Jplus ⊤ S)) (hJm : IsClosed (C.Jminus ⊤ S)) (t : ℝ) :
    hφ.splitting hcaus hS hac hJp hJm '' (univ ×ˢ {t}) = φ t '' S := by
  ext p
  constructor
  · rintro ⟨⟨x, s⟩, ⟨-, hs⟩, rfl⟩
    rw [mem_singleton_iff] at hs
    subst hs
    exact ⟨x, x.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(⟨x, hx⟩, t), ⟨trivial, rfl⟩, rfl⟩

/-- **The slices are Cauchy surfaces when the flow maps preserve inextensible causal curves.**
Not true for an arbitrary causal flow (see SCOPE): `φ_t(S)` need not even be acausal. -/
theorem isCauchySurface_flow_image (hS : C.IsCauchySurface S) (t : ℝ)
    (hinv : ∀ (I : Set ℝ) (c : ℝ → M), C.Inextensible ⊤ I c →
      C.Inextensible ⊤ I (fun s => φ (-t) (c s))) :
    C.IsCauchySurface (φ t '' S) := by
  intro I c hc
  obtain ⟨_, ⟨⟨s, hs, rfl⟩, hsS⟩, huniq⟩ := hS I _ (hinv I c hc)
  have hback : ∀ y, φ t (φ (-t) y) = y := fun y => by
    rw [← Flow.map_add, add_neg_cancel, Flow.map_zero_apply]
  refine ⟨c s, ⟨⟨s, hs, rfl⟩, ⟨_, hsS, hback _⟩⟩, ?_⟩
  rintro _ ⟨⟨s', hs', rfl⟩, ⟨x, hx, hxe⟩⟩
  have hx' : φ (-t) (c s') = x := by rw [← hxe, ← Flow.map_add, neg_add_cancel, Flow.map_zero_apply]
  have := huniq _ ⟨⟨s', hs', rfl⟩, show φ (-t) (c s') ∈ S by rw [hx']; exact hx⟩
  simp only at this
  rw [← hback (c s'), this, hback]

/-! ### Target 3: the two sides of `S ∩ U` in a chart -/

variable (C) in
/-- **A chronal thread through `p` in `U`**: an inextensible causal curve of `U` through `p`
(at the parameter `t₀`) all of whose earlier points are in `I⁻_U(p)` and later points in
`I⁺_U(p)`. The orbit of a chronal flow is one (`IsCausalFlow.hasChronalThreadIn`); at a point with
`I⁻_U(p) = ∅` (a BTZ point) there is none. -/
def HasChronalThreadIn (U : Opens M) (p : M) : Prop :=
  ∃ (I : Set ℝ) (c : ℝ → M) (t₀ : ℝ), C.Inextensible U I c ∧ t₀ ∈ I ∧ c t₀ = p ∧
    (∀ t ∈ I, t < t₀ → C.lt U (c t) p) ∧ (∀ t ∈ I, t₀ < t → C.lt U p (c t))

/-- A chronal thread of `C` run backwards is a chronal thread of `C.dual`. -/
theorem HasChronalThreadIn.dual {U : Opens M} {p : M} (h : C.HasChronalThreadIn U p) :
    C.dual.HasChronalThreadIn U p := by
  obtain ⟨I, c, t₀, hc, ht₀, hcp, h1, h2⟩ := h
  refine ⟨-I, fun t => c (-t), -t₀, hc.dual_reverse, by simpa using ht₀, by simpa using hcp,
    fun t ht htt => h2 (-t) ht (by linarith), fun t ht htt => h1 (-t) ht (by linarith)⟩

omit [TopologicalSpace M] in
private theorem image_neg_reverse (c : ℝ → M) (I : Set ℝ) : (fun t => c (-t)) '' (-I) = c '' I := by
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩; exact ⟨-t, ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩; exact ⟨-t, by simpa using ht, by simp⟩

theorem IsCauchySurfaceOn.of_dual {W : Opens M} (h : C.dual.IsCauchySurfaceOn W S) :
    C.IsCauchySurfaceOn W S := by
  intro I c hc
  have := h _ _ hc.dual_reverse
  rwa [image_neg_reverse] at this

/-- Time reversal preserves Cauchy surfaces of an open set. -/
theorem dual_isCauchySurfaceOn {W : Opens M} :
    C.dual.IsCauchySurfaceOn W S ↔ C.IsCauchySurfaceOn W S :=
  ⟨IsCauchySurfaceOn.of_dual, fun h => IsCauchySurfaceOn.of_dual (C := C.dual) h⟩

/-- **Chronology from the hypotheses of `theo:geroch`**: in a causally arc-connected causal T1
spacetime, a point with `J⁻(x) ≠ {x}` is not chronologically related to itself in any open set
(else `J⁺(x)` would be a neighbourhood of `x`, against `Jplus_not_mem_nhds`). -/
theorem not_lt_self_of_Jminus_ne [T1Space M] (hC : C.CausallyArcConnected) (hcaus : C.IsCausal) {x : M}
    (hx : C.Jminus ⊤ {x} ≠ {x}) (U : Opens M) : ¬ C.lt U x x := by
  intro h
  apply Jplus_not_mem_nhds hC hcaus hx
  have hmem : x ∈ C.Iplus U {x} := by simpa using h
  refine mem_of_superset (isOpen_Iplus.mem_nhds hmem) fun y hy => ?_
  have : C.lt U x y := by simpa using hy
  simpa using C.le_mono le_top (C.le_of_lt this)

/-- **Target 3, the inclusion `I⁺_U(S ∩ U) ⊆ J⁺_U(S ∩ U) ∖ S`**, needing neither threads nor the
Cauchy property. -/
theorem Iplus_subset_Jplus_diff {U : Opens M}
    (hacU : ∀ z ∈ S ∩ (U : Set M), ∀ w ∈ S ∩ (U : Set M), C.le U z w → z = w)
    (hchron : ∀ z ∈ S ∩ (U : Set M), ¬ C.lt U z z) :
    C.Iplus U (S ∩ U) ⊆ C.Jplus U (S ∩ U) \ S := by
  rintro q ⟨σ, hσ, hσq⟩
  refine ⟨⟨σ, hσ, C.le_of_lt hσq⟩, fun hqS => ?_⟩
  have hqU : q ∈ U := C.lt_mem_right hσq
  have h4 : σ = q := hacU σ hσ q ⟨hqS, hqU⟩ (C.le_of_lt hσq)
  subst h4
  exact hchron σ hσ hσq

/-- **Target 3, pointwise**: a point of `J⁺_U(S ∩ U) ∖ S` carrying a chronal thread in `U` lies in
`I⁺_U(S ∩ U)`. -/
theorem mem_Iplus_of_hasChronalThreadIn (hP : C.PushUp) {U : Opens M}
    (hacU : ∀ z ∈ S ∩ (U : Set M), ∀ w ∈ S ∩ (U : Set M), C.le U z w → z = w)
    (hchron : ∀ z ∈ S ∩ (U : Set M), ¬ C.lt U z z)
    (hSU : C.IsCauchySurfaceOn U (S ∩ U)) {p : M} (hp : p ∈ C.Jplus U (S ∩ U) \ S)
    (hth : C.HasChronalThreadIn U p) : p ∈ C.Iplus U (S ∩ U) := by
  obtain ⟨hpJ, hpS⟩ := hp
  obtain ⟨I, c, t₀, hc, -, hcp, h1, h2⟩ := hth
  obtain ⟨_, ⟨⟨t, ht, rfl⟩, htS⟩, -⟩ := hSU I c hc
  rcases lt_trichotomy t t₀ with h | h | h
  · exact ⟨c t, htS, h1 t ht h⟩
  · exact absurd (by rw [← hcp, ← h]; exact htS.1) hpS
  · exfalso
    obtain ⟨σ, hσ, hσp⟩ := hpJ
    have h3 : C.lt U σ (c t) := hP.lt_of_le_of_lt hσp (h2 t ht h)
    have h4 : σ = c t := hacU σ hσ (c t) htS (C.le_of_lt h3)
    rw [← h4] at h3
    exact hchron σ hσ h3

/-- **Target 3, future side.** Let `U` be open, `S ∩ U` acausal in `U` (for `≤_U`) and a Cauchy
surface of `U`, `M` push-up, no point of `S ∩ U` chronologically related to itself in `U`. If
every point of `J⁺_U(S ∩ U) ∖ S` carries a chronal thread in `U`, then
`J⁺_U(S ∩ U) ∖ S = I⁺_U(S ∩ U)`. The inclusion `⊇` needs neither the threads nor the Cauchy
property (`Iplus_subset_Jplus_diff`). -/
theorem Jplus_diff_eq_Iplus (hP : C.PushUp) {U : Opens M}
    (hacU : ∀ z ∈ S ∩ (U : Set M), ∀ w ∈ S ∩ (U : Set M), C.le U z w → z = w)
    (hchron : ∀ z ∈ S ∩ (U : Set M), ¬ C.lt U z z)
    (hSU : C.IsCauchySurfaceOn U (S ∩ U))
    (hthread : ∀ p ∈ C.Jplus U (S ∩ U) \ S, C.HasChronalThreadIn U p) :
    C.Jplus U (S ∩ U) \ S = C.Iplus U (S ∩ U) :=
  Subset.antisymm
    (fun p hp => mem_Iplus_of_hasChronalThreadIn hP hacU hchron hSU hp (hthread p hp))
    (Iplus_subset_Jplus_diff hacU hchron)

/-- **Target 3, past side**: `J⁻_U(S ∩ U) ∖ S = I⁻_U(S ∩ U)`, by time reversal. -/
theorem Jminus_diff_eq_Iminus (hP : C.PushUp) {U : Opens M}
    (hacU : ∀ z ∈ S ∩ (U : Set M), ∀ w ∈ S ∩ (U : Set M), C.le U z w → z = w)
    (hchron : ∀ z ∈ S ∩ (U : Set M), ¬ C.lt U z z)
    (hSU : C.IsCauchySurfaceOn U (S ∩ U))
    (hthread : ∀ p ∈ C.Jminus U (S ∩ U) \ S, C.HasChronalThreadIn U p) :
    C.Jminus U (S ∩ U) \ S = C.Iminus U (S ∩ U) :=
  Jplus_diff_eq_Iplus (C := C.dual) (dual_pushUp.2 hP)
    (fun z hz w hw h => (hacU w hw z hz h).symm) hchron (dual_isCauchySurfaceOn.2 hSU)
    fun p hp => (hthread p hp).dual

/-- **Target 3, the two sides are open** (chart by chart): under the hypotheses of
`Jplus_diff_eq_Iplus`, with threads at every point of `U ∖ S`, `J^±_U(S ∩ U) ∖ S = I^±_U(S ∩ U)`
are open. -/
theorem isOpen_Jplus_diff_and_Jminus_diff (hP : C.PushUp) {U : Opens M}
    (hacU : ∀ z ∈ S ∩ (U : Set M), ∀ w ∈ S ∩ (U : Set M), C.le U z w → z = w)
    (hchron : ∀ z ∈ S ∩ (U : Set M), ¬ C.lt U z z)
    (hSU : C.IsCauchySurfaceOn U (S ∩ U))
    (hthread : ∀ p ∈ (U : Set M) \ S, C.HasChronalThreadIn U p) :
    IsOpen (C.Jplus U (S ∩ U) \ S) ∧ IsOpen (C.Jminus U (S ∩ U) \ S) := by
  constructor
  · rw [Jplus_diff_eq_Iplus hP hacU hchron hSU fun p hp => hthread p ⟨C.le_mem_right
      (Classical.choose_spec hp.1).2, hp.2⟩]
    exact isOpen_Iplus
  · rw [Jminus_diff_eq_Iminus hP hacU hchron hSU fun p hp => hthread p ⟨C.le_mem_left
      (Classical.choose_spec hp.1).2, hp.2⟩]
    exact isOpen_Iminus

/-- **Target 3, the future side is open, pointwise**: under the hypotheses of
`Jplus_diff_eq_Iplus`, if each point of `J⁺_U(S ∩ U) ∖ S` carries a chronal thread in `U` **or**
has a neighbourhood inside `J⁺_U(S ∩ U) ∖ S` (the model's witness at a BTZ point), the side is
open. -/
theorem isOpen_Jplus_diff_of_forall (hP : C.PushUp) {U : Opens M}
    (hacU : ∀ z ∈ S ∩ (U : Set M), ∀ w ∈ S ∩ (U : Set M), C.le U z w → z = w)
    (hchron : ∀ z ∈ S ∩ (U : Set M), ¬ C.lt U z z)
    (hSU : C.IsCauchySurfaceOn U (S ∩ U))
    (h : ∀ p ∈ C.Jplus U (S ∩ U) \ S,
      C.HasChronalThreadIn U p ∨ C.Jplus U (S ∩ U) \ S ∈ 𝓝 p) :
    IsOpen (C.Jplus U (S ∩ U) \ S) := by
  refine isOpen_iff_mem_nhds.2 fun p hp => ?_
  rcases h p hp with hth | hn
  · exact mem_of_superset
      (isOpen_Iplus.mem_nhds (mem_Iplus_of_hasChronalThreadIn hP hacU hchron hSU hp hth))
      (Iplus_subset_Jplus_diff hacU hchron)
  · exact hn

/-- **Target 3, the past side is open, pointwise** (time reversal of
`isOpen_Jplus_diff_of_forall`). -/
theorem isOpen_Jminus_diff_of_forall (hP : C.PushUp) {U : Opens M}
    (hacU : ∀ z ∈ S ∩ (U : Set M), ∀ w ∈ S ∩ (U : Set M), C.le U z w → z = w)
    (hchron : ∀ z ∈ S ∩ (U : Set M), ¬ C.lt U z z)
    (hSU : C.IsCauchySurfaceOn U (S ∩ U))
    (h : ∀ p ∈ C.Jminus U (S ∩ U) \ S,
      C.HasChronalThreadIn U p ∨ C.Jminus U (S ∩ U) \ S ∈ 𝓝 p) :
    IsOpen (C.Jminus U (S ∩ U) \ S) :=
  isOpen_Jplus_diff_of_forall (C := C.dual) (dual_pushUp.2 hP)
    (fun z hz w hw h => (hacU w hw z hz h).symm) hchron (dual_isCauchySurfaceOn.2 hSU)
    fun p hp => (h p hp).imp HasChronalThreadIn.dual id

/-- **Target 3, the two-sidedness of `CompactCauchy.IsLocallyCauchyTwoSided`, pointwise**: as
`isLocallyCauchyTwoSided_of_threads`, but each point of each side needs only a chronal thread
**or** a neighbourhood inside that side — so a chart containing BTZ points off `S` is admitted, the
model supplying the neighbourhoods there. Concludes the unfolded body of
`IsLocallyCauchyTwoSided S`. -/
theorem isLocallyCauchyTwoSided_of_pointwise (hP : C.PushUp)
    (hloc : ∀ x ∈ S, ∃ U : Opens M, x ∈ U ∧ C.CausallyConvexIn (U : Set M) ⊤ ∧
      C.IsCauchySurfaceOn U (S ∩ U) ∧
      (∀ z ∈ S ∩ (U : Set M), ∀ w ∈ S ∩ (U : Set M), C.le U z w → z = w) ∧
      (∀ z ∈ S ∩ (U : Set M), ¬ C.lt U z z) ∧
      (∀ p ∈ C.Jplus U (S ∩ U) \ S,
        C.HasChronalThreadIn U p ∨ C.Jplus U (S ∩ U) \ S ∈ 𝓝 p) ∧
      ∀ p ∈ C.Jminus U (S ∩ U) \ S,
        C.HasChronalThreadIn U p ∨ C.Jminus U (S ∩ U) \ S ∈ 𝓝 p) :
    ∀ x ∈ S, ∃ U : Opens M, x ∈ U ∧ C.CausallyConvexIn (U : Set M) ⊤ ∧
      C.IsCauchySurfaceOn U (S ∩ U) ∧ IsOpen (C.Jplus U (S ∩ U) \ S) ∧
        IsOpen (C.Jminus U (S ∩ U) \ S) := by
  intro x hx
  obtain ⟨U, hxU, hconv, hSU, hacU, hchron, hp, hm⟩ := hloc x hx
  exact ⟨U, hxU, hconv, hSU, isOpen_Jplus_diff_of_forall hP hacU hchron hSU hp,
    isOpen_Jminus_diff_of_forall hP hacU hchron hSU hm⟩

/-- **Target 3, the two-sidedness of `CompactCauchy.IsLocallyCauchyTwoSided`**, from chart-wise
threads. The conclusion is the body of `IsLocallyCauchyTwoSided S` (`Causal.CompactCauchy`,
not imported here), so `this` closes `C.IsLocallyCauchyTwoSided S` by
`exact`. -/
theorem isLocallyCauchyTwoSided_of_threads (hP : C.PushUp)
    (hloc : ∀ x ∈ S, ∃ U : Opens M, x ∈ U ∧ C.CausallyConvexIn (U : Set M) ⊤ ∧
      C.IsCauchySurfaceOn U (S ∩ U) ∧
      (∀ z ∈ S ∩ (U : Set M), ∀ w ∈ S ∩ (U : Set M), C.le U z w → z = w) ∧
      (∀ z ∈ S ∩ (U : Set M), ¬ C.lt U z z) ∧ ∀ p ∈ (U : Set M) \ S, C.HasChronalThreadIn U p) :
    ∀ x ∈ S, ∃ U : Opens M, x ∈ U ∧ C.CausallyConvexIn (U : Set M) ⊤ ∧
      C.IsCauchySurfaceOn U (S ∩ U) ∧ IsOpen (C.Jplus U (S ∩ U) \ S) ∧
        IsOpen (C.Jminus U (S ∩ U) \ S) := by
  intro x hx
  obtain ⟨U, hxU, hconv, hSU, hacU, hchron, hthread⟩ := hloc x hx
  exact ⟨U, hxU, hconv, hSU, isOpen_Jplus_diff_and_Jminus_diff hP hacU hchron hSU hthread⟩

/-- The orbits of a chronal flow are chronal threads, in every open set (`M` causal, T2). -/
theorem IsCausalFlow.hasChronalThreadIn [T2Space M] (hcaus : C.IsCausal) (hφ : C.IsCausalFlow φ)
    (hch : C.IsChronalFlow φ) {U : Opens M} {p : M} (hp : p ∈ U) : C.HasChronalThreadIn U p := by
  have hc0 : φ 0 p = p := Flow.map_zero_apply _ _
  have hU0 : (fun t => φ t p) 0 ∈ U := by simpa only [hc0] using hp
  have hJ := inextensible_ordConnectedComponent hcaus (hφ.inextensible p) (mem_univ 0) hU0
  have h0J : (0 : ℝ) ∈ ordConnectedComponent (univ ∩ (fun t => φ t p) ⁻¹' U) 0 :=
    self_mem_ordConnectedComponent.2 ⟨trivial, hU0⟩
  have hseg : ∀ a ∈ ordConnectedComponent (univ ∩ (fun t => φ t p) ⁻¹' U) 0,
      ∀ b ∈ ordConnectedComponent (univ ∩ (fun t => φ t p) ⁻¹' U) 0,
        C.ChronalCurveOn U (fun t => φ t p) a b := fun a ha b hb =>
    CurveOn.restrict (hch p a b) le_rfl le_rfl le_top fun t ht =>
      (ordConnectedComponent_subset (hJ.1.ordConnected.out ha hb ht)).2
  refine ⟨_, _, 0, hJ, h0J, hc0, fun t ht htt => ?_, fun t ht htt => ?_⟩
  · have := (hseg t ht 0 h0J).lt_of_lt le_rfl htt le_rfl
    simpa only [hc0] using this
  · have := (hseg 0 h0J t ht).lt_of_lt le_rfl htt le_rfl
    simpa only [hc0] using this

/-- The orbits of a chronal flow are chronal threads in `M` (no separation needed). -/
theorem IsCausalFlow.hasChronalThreadIn_top (hφ : C.IsCausalFlow φ) (hch : C.IsChronalFlow φ)
    (p : M) : C.HasChronalThreadIn ⊤ p :=
  ⟨univ, fun t => φ t p, 0, hφ.inextensible p, trivial, Flow.map_zero_apply _ _,
    fun t _ ht => by simpa [Flow.map_zero_apply] using hch.lt p ht,
    fun t _ ht => by simpa [Flow.map_zero_apply] using hch.lt p ht⟩

/-- **Target 3 for `U = M` under a chronal flow**: `J^±(S) ∖ S = I^±(S)` for an acausal Cauchy
surface `S` of a push-up spacetime with no point of `S` chronologically related to itself. -/
theorem IsCausalFlow.J_diff_eq_I (hP : C.PushUp) (hφ : C.IsCausalFlow φ)
    (hch : C.IsChronalFlow φ) (hS : C.IsCauchySurface S) (hac : C.IsAcausal S)
    (hchron : ∀ z ∈ S, ¬ C.lt ⊤ z z) :
    C.Jplus ⊤ S \ S = C.Iplus ⊤ S ∧ C.Jminus ⊤ S \ S = C.Iminus ⊤ S := by
  have hSU : S ∩ ((⊤ : Opens M) : Set M) = S := by rw [Opens.coe_top, inter_univ]
  have hac' : ∀ z ∈ S ∩ ((⊤ : Opens M) : Set M), ∀ w ∈ S ∩ ((⊤ : Opens M) : Set M),
      C.le ⊤ z w → z = w := fun z hz w hw h => hac z hz.1 w hw.1 h
  have hchron' : ∀ z ∈ S ∩ ((⊤ : Opens M) : Set M), ¬ C.lt ⊤ z z := fun z hz => hchron z hz.1
  have hS' : C.IsCauchySurfaceOn ⊤ (S ∩ ((⊤ : Opens M) : Set M)) := by rw [hSU]; exact hS
  have h1 := Jplus_diff_eq_Iplus hP hac' hchron' hS' fun p _ => hφ.hasChronalThreadIn_top hch p
  have h2 := Jminus_diff_eq_Iminus hP hac' hchron' hS' fun p _ => hφ.hasChronalThreadIn_top hch p
  rw [hSU] at h1 h2
  exact ⟨h1, h2⟩

/-! ### A named hypothesis: the existence of a chronal causal flow -/

variable (C) in
/-- **A model fact, as a named hypothesis** (kb/0012): `M` carries a causal flow with chronal
orbits. Witnessed on Minkowski space by the time translation (`minkowski_hasChronalCausalFlow`). -/
def HasChronalCausalFlow : Prop := ∃ φ : Flow ℝ M, C.IsCausalFlow φ ∧ C.IsChronalFlow φ

/-- **The splitting from the named hypothesis**: a causal spacetime with a chronal causal flow
splits along every acausal Cauchy surface. -/
theorem HasChronalCausalFlow.nonempty_isCauchySplitting (hcaus : C.IsCausal)
    (h : C.HasChronalCausalFlow) (hS : C.IsCauchySurface S) (hac : C.IsAcausal S) :
    ∃ ψ : S × ℝ ≃ₜ M, C.IsCauchySplitting S ψ := by
  obtain ⟨φ, hφ, hch⟩ := h
  obtain ⟨ψ, -, hψ⟩ := hφ.exists_isCauchySplitting_of_isChronalFlow hcaus hch hS hac
  exact ⟨ψ, hψ⟩

end Causality

/-! ### Target 4/5: Minkowski space and the time translation -/

section Minkowski

variable {d : ℕ}

/-- **The time translation of Minkowski space** `ℝ^{1,d}` (Barbot's `𝐌ⁿ`, `n = d + 1`):
`φ t (s, x) = (s + t, x)`, the flow of the constant field `e₀`. -/
noncomputable def minkowskiTimeFlow (d : ℕ) : Flow ℝ (Minkowski d) where
  toFun t p := (p.1 + t, p.2)
  cont' := by fun_prop
  map_add' t₁ t₂ p := by
    show ((p.1 + (t₁ + t₂), p.2) : Minkowski d) = ((p.1 + t₂) + t₁, p.2)
    rw [add_comm t₁ t₂, add_assoc]
  map_zero' p := by
    show ((p.1 + 0, p.2) : Minkowski d) = p
    rw [add_zero]

theorem minkowskiTimeFlow_apply (t : ℝ) (p : Minkowski d) :
    minkowskiTimeFlow d t p = (p.1 + t, p.2) := rfl

/-- The orbits of the time translation are chronal curves. -/
theorem minkowski_isChronalFlow : (minkowski d).IsChronalFlow (minkowskiTimeFlow d) := by
  intro p a b
  have hg : CurveOn (minkowski d).lt ⊤ (fun τ => (τ, (fun _ : ℝ => p.2) τ))
      (1 * a + p.1) (1 * b + p.1) :=
    staticCausality.chronalCurveOn_graph (L := 0) zero_lt_one
      ⟨fun _ _ _ _ => by simp, fun _ _ => trivial⟩
  refine CurveOn.congr (CurveOn.comp_affine (k := 1) (m := p.1) one_pos hg) fun t _ => ?_
  simp only [one_mul, minkowskiTimeFlow_apply]
  rw [add_comm]

/-- **The time translation is a causal flow of Minkowski space.** -/
theorem minkowski_isCausalFlow : (minkowski d).IsCausalFlow (minkowskiTimeFlow d) where
  inextensible p := Causality.inextensible_of_unbounded (f := Prod.fst)
    (fun x y h => by
      have := minkowski_le_top_iff.1 h; linarith [norm_nonneg (y.2 - x.2)])
    ⟨⟨0, trivial⟩, ordConnected_univ, fun a _ b _ =>
      (minkowski_isChronalFlow p a b).causalCurveOn⟩
    (fun b => ⟨b - p.1 + 1, by simp only [minkowskiTimeFlow_apply]; linarith⟩)
    (fun b => ⟨b - p.1 - 1, by simp only [minkowskiTimeFlow_apply]; linarith⟩)
  nonstationary p := ⟨1, fun h => by
    have := congrArg Prod.fst h
    simp only [minkowskiTimeFlow_apply] at this
    linarith⟩

theorem minkowski_hasChronalCausalFlow : (minkowski d).HasChronalCausalFlow :=
  ⟨_, minkowski_isCausalFlow, minkowski_isChronalFlow⟩

/-- **Minkowski space splits along every acausal Cauchy surface**, by the time translation:
`ψ (x, t) = x + t e₀`. -/
theorem minkowski_exists_isCauchySplitting {S : Set (Minkowski d)}
    (hS : (minkowski d).IsCauchySurface S) (hac : (minkowski d).IsAcausal S) :
    ∃ ψ : S × ℝ ≃ₜ Minkowski d, (∀ (x : S) (t : ℝ), ψ (x, t) = ((x : Minkowski d).1 + t,
      (x : Minkowski d).2)) ∧ (minkowski d).IsCauchySplitting S ψ :=
  minkowski_isCausalFlow.exists_isCauchySplitting_of_isChronalFlow minkowski_isCausal
    minkowski_isChronalFlow hS hac

/-- The time slice `{t = s}` of Minkowski space. -/
def minkowskiSlice (d : ℕ) (s : ℝ) : Set (Minkowski d) := {p | p.1 = s}

/-- **The time slices are Cauchy surfaces**: `theo:geroch` (ii)⇒(iii) for `T = t − s`. -/
theorem minkowski_isCauchySurface_slice (s : ℝ) :
    (minkowski d).IsCauchySurface (minkowskiSlice d s) := by
  have hT : (minkowski d).IsCauchyTimeFunction fun p : Minkowski d => p.1 - (fun _ => s) p.2 :=
    staticCausality.isCauchyTimeFunction_sub (fun _ => s) (fun _ _ => by simp) (B := |s|)
      fun _ => le_rfl
  have := hT.isCauchySurface minkowski_causallyArcConnected minkowski_stronglyCausal
    staticCausality.Jminus_ne_singleton staticCausality.Jplus_ne_singleton fun x y hxy hne => by
      have := minkowski_time_strict.2 x y hxy hne
      simp only; linarith
  have he : (fun p : Minkowski d => p.1 - (fun _ => s) p.2) ⁻¹' {0} = minkowskiSlice d s := by
    ext p
    simp only [mem_preimage, mem_singleton_iff, minkowskiSlice, mem_setOf_eq, sub_eq_zero]
  rwa [he] at this

/-- The time slices are acausal. -/
theorem minkowski_isAcausal_slice (s : ℝ) : (minkowski d).IsAcausal (minkowskiSlice d s) := by
  intro x hx y hy hxy
  by_contra hne
  have := minkowski_time_strict.2 x y hxy hne
  simp only [minkowskiSlice, mem_setOf_eq] at hx hy
  linarith

/-- **Each time translation preserves inextensible causal curves**: it is the isometry
`constVAdd (t, 0)`, an abstract `𝕄≥0`-morphism (`Flat.isom_isEMorphism`), injective with inverse
the translation by `-t`. -/
theorem minkowskiTimeFlow_inextensible (t : ℝ) {I : Set ℝ} {c : ℝ → Minkowski d}
    (hc : (minkowski d).Inextensible ⊤ I c) :
    (minkowski d).Inextensible ⊤ I (fun s => minkowskiTimeFlow d t (c s)) := by
  set g : Flat.isom d := ⟨AffineEquiv.constVAdd ℝ (Minkowski d) ((t, 0) : Minkowski d),
    Flat.constVAdd_mem_isom _⟩
  have hfg : ∀ p, minkowskiTimeFlow d t p = g • p := fun p => by
    rw [Flat.isom_smul_def, minkowskiTimeFlow_apply]
    refine Prod.ext ?_ ?_ <;> simp [g, add_comm]
  have hE : IsEMorphismOn (minkowski d) (minkowski d) ⊤ (minkowskiTimeFlow d t) :=
    (Flat.isom_isEMorphism g).congr fun p _ => (hfg p).symm
  have hback : ∀ x, minkowskiTimeFlow d (-t) (minkowskiTimeFlow d t x) = x := fun x => by
    rw [← Flow.map_add, neg_add_cancel, Flow.map_zero_apply]
  have hfwd : ∀ x, minkowskiTimeFlow d t (minkowskiTimeFlow d (-t) x) = x := fun x => by
    rw [← Flow.map_add, add_neg_cancel, Flow.map_zero_apply]
  have hinj : InjOn (minkowskiTimeFlow d t) ((⊤ : Opens (Minkowski d)) : Set (Minkowski d)) :=
    fun x _ y _ h => by rw [← hback x, h, hback y]
  have hg : LeftInvOn (minkowskiTimeFlow d (-t)) (minkowskiTimeFlow d t)
      ((⊤ : Opens (Minkowski d)) : Set (Minkowski d)) := fun x _ => hback x
  have hU : ((⊤ : Opens (Minkowski d)) : Set (Minkowski d)) =
      minkowskiTimeFlow d t '' ((⊤ : Opens (Minkowski d)) : Set (Minkowski d)) := by
    rw [Opens.coe_top, image_univ_of_surjective fun y => ⟨_, hfwd y⟩]
  exact (hE.inextensible_iff_comp hinj hg le_rfl hU fun _ _ => trivial).1 hc

/-- **Non-vacuity of `hinv` in `isCauchySurface_flow_image`**: the time-translates of the slice
`{t = 0}` are Cauchy surfaces, through the flow-image criterion. -/
theorem minkowski_isCauchySurface_flow_image (t : ℝ) :
    (minkowski d).IsCauchySurface (minkowskiTimeFlow d t '' minkowskiSlice d 0) :=
  Causality.isCauchySurface_flow_image (minkowski_isCauchySurface_slice 0) t
    fun _ _ hc => minkowskiTimeFlow_inextensible (-t) hc

/-- **`bprop:splitting` on Minkowski space, in full**: along the slice `{t = 0}`, the time
translation gives `𝐌ⁿ ≅ S × ℝ` whose every slice `ψ(S × {t}) = {t}` is a Cauchy surface. -/
theorem minkowski_splitting_cauchy_slices :
    ∃ ψ : minkowskiSlice d 0 × ℝ ≃ₜ Minkowski d,
      (∀ (x : minkowskiSlice d 0) (t : ℝ), ψ (x, t) = minkowskiTimeFlow d t x) ∧
      (minkowski d).IsCauchySplitting (minkowskiSlice d 0) ψ ∧
      ∀ t : ℝ, ψ '' (univ ×ˢ {t}) = minkowskiSlice d t ∧
        (minkowski d).IsCauchySurface (ψ '' (univ ×ˢ {t})) := by
  obtain ⟨ψ, hψe, hψ⟩ := minkowski_isCausalFlow.exists_isCauchySplitting_of_isChronalFlow
    minkowski_isCausal minkowski_isChronalFlow (minkowski_isCauchySurface_slice 0)
    (minkowski_isAcausal_slice 0)
  have himg : ∀ t : ℝ, ψ '' (univ ×ˢ {t}) = minkowskiSlice d t := fun t => by
    ext p
    constructor
    · rintro ⟨⟨x, s⟩, ⟨-, hs⟩, rfl⟩
      rw [mem_singleton_iff] at hs
      subst hs
      have hx : (x : Minkowski d).1 = 0 := x.2
      show (ψ (x, s)).1 = s
      rw [hψe, minkowskiTimeFlow_apply, hx, zero_add]
    · intro hp
      have hp' : p.1 = t := hp
      refine ⟨(⟨(0, p.2), rfl⟩, t), ⟨trivial, rfl⟩, ?_⟩
      rw [hψe, minkowskiTimeFlow_apply]
      exact Prod.ext (by simp [hp']) rfl
  exact ⟨ψ, hψe, hψ, fun t => ⟨himg t, by rw [himg]; exact minkowski_isCauchySurface_slice t⟩⟩

/-- A flow of Minkowski space with position-dependent speed: `φ t (s, x) = (s + t(1 + ‖x‖), x)`. -/
noncomputable def minkowskiSkewFlow (d : ℕ) : Flow ℝ (Minkowski d) where
  toFun t p := (p.1 + t * (1 + ‖p.2‖), p.2)
  cont' := by fun_prop
  map_add' t₁ t₂ p := by
    show ((p.1 + (t₁ + t₂) * (1 + ‖p.2‖), p.2) : Minkowski d) =
      ((p.1 + t₂ * (1 + ‖p.2‖)) + t₁ * (1 + ‖p.2‖), p.2)
    congr 1; ring
  map_zero' p := by
    show ((p.1 + 0 * (1 + ‖p.2‖), p.2) : Minkowski d) = p
    rw [zero_mul, add_zero]

theorem minkowskiSkewFlow_apply (t : ℝ) (p : Minkowski d) :
    minkowskiSkewFlow d t p = (p.1 + t * (1 + ‖p.2‖), p.2) := rfl

theorem minkowski_isChronalFlow_skew : (minkowski d).IsChronalFlow (minkowskiSkewFlow d) := by
  intro p a b
  have hk : 0 < 1 + ‖p.2‖ := by positivity
  have hg : CurveOn (minkowski d).lt ⊤ (fun τ => (τ, (fun _ : ℝ => p.2) τ))
      ((1 + ‖p.2‖) * a + p.1) ((1 + ‖p.2‖) * b + p.1) :=
    staticCausality.chronalCurveOn_graph (L := 0) zero_lt_one
      ⟨fun _ _ _ _ => by simp, fun _ _ => trivial⟩
  refine CurveOn.congr (CurveOn.comp_affine (k := 1 + ‖p.2‖) (m := p.1) hk hg) fun t _ => ?_
  simp only [minkowskiSkewFlow_apply]
  congr 1; ring

theorem minkowski_isCausalFlow_skew : (minkowski d).IsCausalFlow (minkowskiSkewFlow d) where
  inextensible p := Causality.inextensible_of_unbounded (f := Prod.fst)
    (fun x y h => by
      have := minkowski_le_top_iff.1 h; linarith [norm_nonneg (y.2 - x.2)])
    ⟨⟨0, trivial⟩, ordConnected_univ, fun a _ b _ =>
      (minkowski_isChronalFlow_skew p a b).causalCurveOn⟩
    (fun b => ⟨|b - p.1| + 1, by
      simp only [minkowskiSkewFlow_apply]
      have h1 := le_abs_self (b - p.1)
      have h2 := norm_nonneg p.2
      have h3 : 0 ≤ |b - p.1| := abs_nonneg _
      nlinarith⟩)
    (fun b => ⟨-(|b - p.1| + 1), by
      simp only [minkowskiSkewFlow_apply]
      have h1 := neg_abs_le (b - p.1)
      have h2 := norm_nonneg p.2
      have h3 : 0 ≤ |b - p.1| := abs_nonneg _
      nlinarith⟩)
  nonstationary p := ⟨1, fun h => by
    have := congrArg Prod.fst h
    simp only [minkowskiSkewFlow_apply] at this
    linarith [norm_nonneg p.2]⟩

/-- **Finding: the slices of a flow splitting need not be Cauchy surfaces.** On `𝐌ⁿ`, `n ≥ 2`,
the chronal causal flow `φ t (s, x) = (s + t(1 + ‖x‖), x)` splits Minkowski space along the Cauchy
surface `{t = 0}` (target 2), and the slice `ψ(S × {1}) = {(1 + ‖x‖, x)}` is not a Cauchy surface:
the null line `τ ↦ (τ, (τ − 1)e)` meets it at `(1, 0)` and at `(2, e)`. So `bprop:splitting`'s
"every `S × {∗}` is Cauchy" is a property of a well-chosen flow, not of every causal flow. -/
theorem minkowski_skew_slice_not_isCauchySurface (hd : 0 < d) :
    ∃ ψ : minkowskiSlice d 0 × ℝ ≃ₜ Minkowski d,
      (∀ (x : minkowskiSlice d 0) (t : ℝ), ψ (x, t) = minkowskiSkewFlow d t x) ∧
      (minkowski d).IsCauchySplitting (minkowskiSlice d 0) ψ ∧
      ¬ (minkowski d).IsCauchySurface (ψ '' (univ ×ˢ {1})) := by
  obtain ⟨ψ, hψe, hψ⟩ := minkowski_isCausalFlow_skew.exists_isCauchySplitting_of_isChronalFlow
    minkowski_isCausal minkowski_isChronalFlow_skew (minkowski_isCauchySurface_slice 0)
    (minkowski_isAcausal_slice 0)
  refine ⟨ψ, hψe, hψ, fun hS => ?_⟩
  set e := unitVec d hd
  have hℓ : ∀ s s' : ℝ, dist ((s - 1) • e) ((s' - 1) • e) = |s - s'| := fun s s' => by
    rw [dist_smul_unitVec hd]; congr 1; ring
  obtain ⟨_, -, huniq⟩ := hS univ _ (staticCausality.inextensible_nullLine hℓ)
  have hmem : ∀ v : EuclideanSpace ℝ (Fin d), (1 + ‖v‖, v) ∈ ψ '' (univ ×ˢ {1}) := fun v =>
    ⟨(⟨(0, v), rfl⟩, 1), ⟨trivial, rfl⟩, by
      rw [hψe, minkowskiSkewFlow_apply]; simp⟩
  have h1 := huniq (1, (1 - 1 : ℝ) • e) ⟨⟨1, trivial, rfl⟩, by
    simpa using hmem 0⟩
  have h2 := huniq (2, (2 - 1 : ℝ) • e) ⟨⟨2, trivial, rfl⟩, by
    have := hmem e
    rw [norm_unitVec] at this
    norm_num at this ⊢
    exact this⟩
  have := congrArg Prod.fst (h1.trans h2.symm)
  norm_num at this

end Minkowski

/-! ### Non-vacuity of target 3 on the lines, and the finding on the lightlike line -/

section Lines

open Causality

/-- On the timelike line, `id` is a chronal thread through every point. -/
theorem timelikeLine_hasChronalThreadIn (p : ℝ) : timelikeLine.HasChronalThreadIn ⊤ p :=
  ⟨univ, id, p, timelikeLine_inextensible_id, trivial, rfl,
    fun t _ ht => by simp only [id, timelikeLine_lt]; exact ⟨ht, fun _ _ => trivial⟩,
    fun t _ ht => by simp only [id, timelikeLine_lt]; exact ⟨ht, fun _ _ => trivial⟩⟩

/-- **The hypotheses of target 3 are jointly satisfiable**: on the timelike line with `S = {0}`
and `U = ℝ`; and its conclusion `J⁺(S) ∖ S = I⁺(S)`, `J⁻(S) ∖ S = I⁻(S)`. -/
theorem timelikeLine_target3 :
    timelikeLine.Jplus ⊤ ({0} ∩ ((⊤ : Opens ℝ) : Set ℝ)) \ {0} =
        timelikeLine.Iplus ⊤ ({0} ∩ ((⊤ : Opens ℝ) : Set ℝ)) ∧
      timelikeLine.Jminus ⊤ ({0} ∩ ((⊤ : Opens ℝ) : Set ℝ)) \ {0} =
        timelikeLine.Iminus ⊤ ({0} ∩ ((⊤ : Opens ℝ) : Set ℝ)) := by
  have hac : ∀ z ∈ ({0} : Set ℝ) ∩ ((⊤ : Opens ℝ) : Set ℝ),
      ∀ w ∈ ({0} : Set ℝ) ∩ ((⊤ : Opens ℝ) : Set ℝ), timelikeLine.le ⊤ z w → z = w :=
    fun z hz w hw _ => hz.1.trans hw.1.symm
  have hchron : ∀ z ∈ ({0} : Set ℝ) ∩ ((⊤ : Opens ℝ) : Set ℝ), ¬ timelikeLine.lt ⊤ z z :=
    fun z _ h => lt_irrefl z (timelikeLine_lt.1 h).1
  have hS : timelikeLine.IsCauchySurfaceOn ⊤ (({0} : Set ℝ) ∩ ((⊤ : Opens ℝ) : Set ℝ)) := by
    rw [Opens.coe_top, inter_univ]; exact timelikeLine_isCauchySurface_zero
  exact ⟨Jplus_diff_eq_Iplus timelikeLine_pushUp hac hchron hS
      fun p _ => timelikeLine_hasChronalThreadIn p,
    Jminus_diff_eq_Iminus timelikeLine_pushUp hac hchron hS
      fun p _ => timelikeLine_hasChronalThreadIn p⟩

/-- **Non-vacuity of `hloc` in `isLocallyCauchyTwoSided_of_threads`**: on the timelike line with
`S = {0}`, the chart `U = ℝ` works. -/
theorem timelikeLine_hloc :
    ∀ x ∈ ({0} : Set ℝ), ∃ U : Opens ℝ, x ∈ U ∧ timelikeLine.CausallyConvexIn (U : Set ℝ) ⊤ ∧
      timelikeLine.IsCauchySurfaceOn U ({0} ∩ U) ∧
      (∀ z ∈ ({0} : Set ℝ) ∩ (U : Set ℝ), ∀ w ∈ ({0} : Set ℝ) ∩ (U : Set ℝ),
        timelikeLine.le U z w → z = w) ∧
      (∀ z ∈ ({0} : Set ℝ) ∩ (U : Set ℝ), ¬ timelikeLine.lt U z z) ∧
      ∀ p ∈ (U : Set ℝ) \ {0}, timelikeLine.HasChronalThreadIn U p := by
  intro x _
  refine ⟨⊤, trivial, ⟨subset_rfl, fun _ _ _ _ => subset_univ _⟩, ?_,
    fun z hz w hw _ => hz.1.trans hw.1.symm, fun z _ h => lt_irrefl z (timelikeLine_lt.1 h).1,
    fun p _ => timelikeLine_hasChronalThreadIn p⟩
  rw [Opens.coe_top, inter_univ]; exact timelikeLine_isCauchySurface_zero

/-- The two-sidedness of `{0}` on the timelike line, through `isLocallyCauchyTwoSided_of_threads`. -/
theorem timelikeLine_twoSided_of_threads :
    ∀ x ∈ ({0} : Set ℝ), ∃ U : Opens ℝ, x ∈ U ∧ timelikeLine.CausallyConvexIn (U : Set ℝ) ⊤ ∧
      timelikeLine.IsCauchySurfaceOn U ({0} ∩ U) ∧
      IsOpen (timelikeLine.Jplus U ({0} ∩ U) \ {0}) ∧
        IsOpen (timelikeLine.Jminus U ({0} ∩ U) \ {0}) :=
  isLocallyCauchyTwoSided_of_threads timelikeLine_pushUp timelikeLine_hloc

/-- `{0}` is a Cauchy surface of the lightlike line: its causal relation `≤` is the timelike
line's, so the two lines have the same causal curves and the same extensions, hence the same
inextensible causal curves (transferred field by field), and `timelikeLine_isCauchySurface_zero`
applies. -/
theorem lightlikeLine_isCauchySurface_zero : lightlikeLine.IsCauchySurface ({0} : Set ℝ) := by
  have hcurve : ∀ {W : Opens ℝ} {I : Set ℝ} {c : ℝ → ℝ},
      lightlikeLine.CausalCurveIn W I c ↔ timelikeLine.CausalCurveIn W I c :=
    ⟨fun h => ⟨h.nonempty, h.ordConnected, h.curve⟩, fun h => ⟨h.nonempty, h.ordConnected, h.curve⟩⟩
  have hext : ∀ {W : Opens ℝ} {I : Set ℝ} {c : ℝ → ℝ},
      lightlikeLine.Extensible W I c ↔ timelikeLine.Extensible W I c :=
    ⟨fun ⟨I', c', h⟩ => ⟨I', c', ⟨hcurve.1 h.curve, h.reparam, h.grows⟩⟩,
      fun ⟨I', c', h⟩ => ⟨I', c', ⟨hcurve.2 h.curve, h.reparam, h.grows⟩⟩⟩
  intro I c hc
  exact timelikeLine_isCauchySurface_zero I c ⟨hcurve.1 hc.1, fun h => hc.2 (hext.2 h)⟩

/-- **Finding: target 3's equality fails without chronal threads.** On the lightlike line (the
library's model of a BTZ line, `lightlikeLine_btzAxioms`) with `S = {0}` and `U = ℝ`, **every
hypothesis of `Jplus_diff_eq_Iplus` but the threads holds** — causality, push-up, acausality of
`S ∩ U` for `≤_U`, chronology on `S ∩ U`, `S ∩ U` a Cauchy surface of `U` — and yet
`1 ∈ J⁺(S) ∖ S` while `I⁺(S) = ∅`: chronological pasts are empty, as at a BTZ point. The two sides
are nevertheless open there (`lightlikeLine_twoSided_of_pointwise`). -/
theorem lightlikeLine_Jplus_diff_ne_Iplus :
    lightlikeLine.IsCausal ∧ lightlikeLine.PushUp ∧ lightlikeLine.IsAcausal ({0} : Set ℝ) ∧
      (∀ z ∈ ({0} : Set ℝ) ∩ ((⊤ : Opens ℝ) : Set ℝ), ∀ w ∈ ({0} : Set ℝ) ∩ ((⊤ : Opens ℝ) : Set ℝ),
        lightlikeLine.le ⊤ z w → z = w) ∧
      (∀ z ∈ ({0} : Set ℝ) ∩ ((⊤ : Opens ℝ) : Set ℝ), ¬ lightlikeLine.lt ⊤ z z) ∧
      lightlikeLine.IsCauchySurfaceOn ⊤ (({0} : Set ℝ) ∩ ((⊤ : Opens ℝ) : Set ℝ)) ∧
      (1 : ℝ) ∈ lightlikeLine.Jplus ⊤ (({0} : Set ℝ) ∩ ((⊤ : Opens ℝ) : Set ℝ)) \ {0} ∧
      lightlikeLine.Iplus ⊤ (({0} : Set ℝ) ∩ ((⊤ : Opens ℝ) : Set ℝ)) = ∅ := by
  refine ⟨lightlikeLine_isCausal, lightlikeLine_pushUp, fun x hx y hy _ => hx.trans hy.symm,
    fun z hz w hw _ => hz.1.trans hw.1.symm, fun _ _ h => (lightlikeLine_lt.1 h).elim, ?_,
    ⟨⟨0, ⟨rfl, trivial⟩, ?_⟩, by norm_num⟩, ?_⟩
  · rw [Opens.coe_top, inter_univ]; exact lightlikeLine_isCauchySurface_zero
  · rw [lightlikeLine_le]; exact ⟨zero_le_one, fun _ _ => trivial⟩
  · ext q
    simp only [Precausality.mem_Iplus, lightlikeLine_lt, and_false, exists_false, mem_empty_iff_false]

theorem lightlikeLine_Jplus_diff_zero :
    lightlikeLine.Jplus ⊤ (({0} : Set ℝ) ∩ ((⊤ : Opens ℝ) : Set ℝ)) \ {0} = Ioi 0 := by
  ext p
  constructor
  · rintro ⟨⟨σ, hσ, hσp⟩, hp0⟩
    have h0 : σ = 0 := hσ.1
    subst h0
    exact lt_of_le_of_ne (lightlikeLine_le.1 hσp).1 (Ne.symm hp0)
  · intro hp
    exact ⟨⟨0, ⟨rfl, trivial⟩, lightlikeLine_le.2 ⟨le_of_lt hp, fun _ _ => trivial⟩⟩,
      ne_of_gt hp⟩

theorem lightlikeLine_Jminus_diff_zero :
    lightlikeLine.Jminus ⊤ (({0} : Set ℝ) ∩ ((⊤ : Opens ℝ) : Set ℝ)) \ {0} = Iio 0 := by
  ext p
  constructor
  · rintro ⟨⟨σ, hσ, hpσ⟩, hp0⟩
    have h0 : σ = 0 := hσ.1
    subst h0
    exact lt_of_le_of_ne (lightlikeLine_le.1 hpσ).1 hp0
  · intro hp
    exact ⟨⟨0, ⟨rfl, trivial⟩, lightlikeLine_le.2 ⟨le_of_lt hp, fun _ _ => trivial⟩⟩,
      ne_of_lt hp⟩

/-- **Non-vacuity of the pointwise variant where threads fail**: on the lightlike line no point
off `{0}` carries a chronal thread, and `isLocallyCauchyTwoSided_of_pointwise` still gives the
two-sidedness of `{0}`, from neighbourhoods inside the sides (`]0, ∞[`, `]-∞, 0[`). -/
theorem lightlikeLine_twoSided_of_pointwise :
    ∀ x ∈ ({0} : Set ℝ), ∃ U : Opens ℝ, x ∈ U ∧ lightlikeLine.CausallyConvexIn (U : Set ℝ) ⊤ ∧
      lightlikeLine.IsCauchySurfaceOn U ({0} ∩ U) ∧
      IsOpen (lightlikeLine.Jplus U ({0} ∩ U) \ {0}) ∧
        IsOpen (lightlikeLine.Jminus U ({0} ∩ U) \ {0}) :=
  isLocallyCauchyTwoSided_of_pointwise lightlikeLine_pushUp fun _ _ =>
    ⟨⊤, trivial, ⟨subset_rfl, fun _ _ _ _ => subset_univ _⟩,
      (by rw [Opens.coe_top, inter_univ]; exact lightlikeLine_isCauchySurface_zero),
      fun z hz w hw _ => hz.1.trans hw.1.symm, fun _ _ h => (lightlikeLine_lt.1 h).elim,
      fun p hp => Or.inr (by
        rw [lightlikeLine_Jplus_diff_zero] at hp ⊢; exact Ioi_mem_nhds hp),
      fun p hp => Or.inr (by
        rw [lightlikeLine_Jminus_diff_zero] at hp ⊢; exact Iio_mem_nhds hp)⟩

end Lines

/-! ### Target 4: the orbits of a fixed-point-free flow are inextensible -/

section FlowInextensible

namespace Causality

variable {C : Causality M} {φ : Flow ℝ M}

/-- **A limit of an orbit is a fixed point**: along a filter invariant under the translations
(`atTop`, `atBot`), in a Hausdorff space. -/
theorem flow_fixed_of_tendsto [T2Space M] {x p : M} {l : Filter ℝ} [l.NeBot]
    (hl : ∀ τ : ℝ, Tendsto (fun s => τ + s) l l)
    (h : Tendsto (fun s => φ s x) l (𝓝 p)) (τ : ℝ) : φ τ p = p := by
  have h1 : Tendsto (fun s => φ τ (φ s x)) l (𝓝 (φ τ p)) :=
    ((φ.continuous continuous_const continuous_id).tendsto p).comp h
  have h2 : Tendsto (fun s => φ τ (φ s x)) l (𝓝 p) := by
    have := h.comp (hl τ)
    refine this.congr fun s => ?_
    simp only [Function.comp, Flow.map_add]
  exact tendsto_nhds_unique h1 h2

/-- **The orbits of a fixed-point-free flow are inextensible** as soon as they are causal curves
over `ℝ` (`M` Hausdorff). An extension `(I', c')` with a new value `c' t'` has `t'` beyond one end
of the reparametrised image `ψ(ℝ)`, say above it; then `ψ s ↑ σ := sup ψ ≤ t'`, `σ ∈ I'`, and
`c'` continuous on `[ψ 0, t']` gives `φ s x = c'(ψ s) → c' σ`, a limit of the orbit, hence a fixed
point (`flow_fixed_of_tendsto`), which `hns` excludes. No causality axiom is used. -/
theorem inextensible_of_flow [T2Space M] (hc : ∀ x, C.CausalCurveIn ⊤ univ (fun t => φ t x))
    (hns : ∀ x, ∃ t, φ t x ≠ x) (x : M) : C.Inextensible ⊤ univ (fun t => φ t x) := by
  refine ⟨hc x, ?_⟩
  rintro ⟨I', c', hcurve, ⟨ψ, hψ, hψmaps, hψoc, hψeq⟩, ⟨t', ht', hgrow⟩⟩
  have hmono : Monotone ψ := (strictMonoOn_univ.1 hψ).monotone
  have hfix : ∀ p : M, (∀ τ : ℝ, φ τ p = p) → False := fun p hp => by
    obtain ⟨t, ht⟩ := hns p; exact ht (hp t)
  by_cases h1 : ∃ s, t' ≤ ψ s
  · by_cases h2 : ∃ s, ψ s ≤ t'
    · obtain ⟨s₁, hs₁⟩ := h1
      obtain ⟨s₂, hs₂⟩ := h2
      obtain ⟨s, -, hs⟩ := hψoc.out (mem_image_of_mem ψ (mem_univ s₂))
        (mem_image_of_mem ψ (mem_univ s₁)) ⟨hs₂, hs₁⟩
      exact hgrow s trivial (by rw [← hs, hψeq s trivial])
    · -- the past end: `ψ` is bounded below by `t'`
      simp only [not_exists, not_le] at h2
      have hbdd : BddBelow (range ψ) := ⟨t', by rintro _ ⟨s, rfl⟩; exact (h2 s).le⟩
      set σ := ⨅ s, ψ s
      have hσ : Tendsto ψ atBot (𝓝 σ) := tendsto_atBot_ciInf hmono hbdd
      have hσt : t' ≤ σ := le_ciInf fun s => (h2 s).le
      have hσ0 : σ ≤ ψ 0 := ciInf_le hbdd 0
      have hcont := (hcurve.curve t' ht' (ψ 0) (hψmaps (mem_univ 0))).continuousOn
        C.isRelFamily_le
      have hσmem : σ ∈ Icc t' (ψ 0) := ⟨hσt, hσ0⟩
      have hev : ∀ᶠ s in atBot, ψ s ∈ Icc t' (ψ 0) :=
        eventually_atBot.2 ⟨0, fun s hs => ⟨(h2 s).le, hmono hs⟩⟩
      have hlim : Tendsto (fun s => φ s x) atBot (𝓝 (c' σ)) := by
        have := (hcont σ hσmem).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hσ, hev⟩)
        exact this.congr fun s => by simp only [Function.comp, hψeq s trivial]
      exact hfix _ (flow_fixed_of_tendsto (fun τ => tendsto_atBot_add_const_left _ τ tendsto_id)
        hlim)
  · -- the future end
    simp only [not_exists, not_le] at h1
    have hbdd : BddAbove (range ψ) := ⟨t', by rintro _ ⟨s, rfl⟩; exact (h1 s).le⟩
    set σ := ⨆ s, ψ s
    have hσ : Tendsto ψ atTop (𝓝 σ) := tendsto_atTop_ciSup hmono hbdd
    have hσt : σ ≤ t' := ciSup_le fun s => (h1 s).le
    have hσ0 : ψ 0 ≤ σ := le_ciSup hbdd 0
    have hcont := (hcurve.curve (ψ 0) (hψmaps (mem_univ 0)) t' ht').continuousOn
      C.isRelFamily_le
    have hσmem : σ ∈ Icc (ψ 0) t' := ⟨hσ0, hσt⟩
    have hev : ∀ᶠ s in atTop, ψ s ∈ Icc (ψ 0) t' :=
      eventually_atTop.2 ⟨0, fun s hs => ⟨hmono hs, (h1 s).le⟩⟩
    have hlim : Tendsto (fun s => φ s x) atTop (𝓝 (c' σ)) := by
      have := (hcont σ hσmem).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hσ, hev⟩)
      exact this.congr fun s => by simp only [Function.comp, hψeq s trivial]
    exact hfix _ (flow_fixed_of_tendsto (fun τ => tendsto_atTop_add_const_left _ τ tendsto_id)
      hlim)

end Causality

end FlowInextensible

universe uN

section ODE

open Manifold Bundle Metric
open scoped ContDiff NNReal

/-! ### The ODE input: completeness by rescaling and continuous dependence

Pure ODE on a manifold, no causality. Mathlib at this pin has local existence and uniqueness of
integral curves on a manifold, the uniform-time globalisation, and Picard–Lindelöf in a Banach space
with a local flow continuous in the initial point; it has neither completeness by rescaling nor
continuous dependence on a manifold. Both are proved here: a locally finite cover by chart balls
with a uniform inner margin (`ODEFlow.exists_chart_cover`), a positive smooth `f` making the
coordinate field of `f • v` small on each ball (`ODEFlow.exists_rescaling_chartBound`), hence
Picard–Lindelöf on `[-1, 1]` about every point with the chart flow transported back
(`ODEFlow.exists_localFlow_of_chartBound`), then global curves and joint continuity by uniqueness
and doubling (`ODEFlow.exists_global_flow_of_local`). -/


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {N : Type uN} [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N]

namespace ODEFlow

/-- The coordinate expression of a vector field `w` in the chart at `c`. -/
noncomputable def chartField (w : (x : N) → TangentSpace 𝓘(ℝ, E) x) (c : N) (z : E) : E :=
  tangentCoordChange 𝓘(ℝ, E) ((extChartAt 𝓘(ℝ, E) c).symm z) c ((extChartAt 𝓘(ℝ, E) c).symm z)
    (w ((extChartAt 𝓘(ℝ, E) c).symm z))

omit [FiniteDimensional ℝ E] in
theorem chartField_smul (g : N → ℝ) (w : (x : N) → TangentSpace 𝓘(ℝ, E) x) (c : N) (z : E) :
    chartField (fun y => g y • w y) c z =
      g ((extChartAt 𝓘(ℝ, E) c).symm z) • chartField w c z := by
  simp only [chartField]
  exact ContinuousLinearMap.map_smul _ _ _

omit [FiniteDimensional ℝ E] in
theorem contDiffOn_chartField {w : (x : N) → TangentSpace 𝓘(ℝ, E) x}
    (hw : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1 (fun x => (⟨x, w x⟩ : TangentBundle 𝓘(ℝ, E) N)))
    (c : N) : ContDiffOn ℝ 1 (chartField w c) (extChartAt 𝓘(ℝ, E) c).target := by
  have h1 : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) 1
      (fun y => (trivializationAt E (TangentSpace 𝓘(ℝ, E)) c ⟨y, w y⟩).2)
      (chartAt E c).source := by
    intro y hy
    exact ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) c).contMDiffWithinAt_section _
      (by simpa using hy)).1 (hw y).contMDiffWithinAt
  have h2 := h1.comp (contMDiffOn_extChartAt_symm (n := 1) c) (fun z hz => by
    simpa using (extChartAt 𝓘(ℝ, E) c).map_target hz)
  rw [contMDiffOn_iff_contDiffOn] at h2
  refine h2.congr fun z hz => ?_
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [FiniteDimensional ℝ E] in
/-- **Transport of a chart solution**: a curve solving the ODE of `chartField w c` inside the chart
target is, read back on the manifold, tangent to `w`. -/
theorem hasMFDerivAt_symm_comp {w : (x : N) → TangentSpace 𝓘(ℝ, E) x} {c : N} {α : ℝ → E}
    {t : ℝ} (hα : HasDerivAt α (chartField w c (α t)) t)
    (ht : α t ∈ (extChartAt 𝓘(ℝ, E) c).target) :
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ((extChartAt 𝓘(ℝ, E) c).symm ∘ α) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (w ((extChartAt 𝓘(ℝ, E) c).symm (α t)))) := by
  let xₜ : N := (extChartAt 𝓘(ℝ, E) c).symm (α t)
  have hft1 : xₜ ∈ (extChartAt 𝓘(ℝ, E) c).source := (extChartAt 𝓘(ℝ, E) c).map_target ht
  have hft2 := mem_extChartAt_source (I := 𝓘(ℝ, E)) xₜ
  refine ⟨(continuousAt_extChartAt_symm'' ht).comp hα.continuousAt,
    HasDerivWithinAt.hasFDerivWithinAt ?_⟩
  simp only [mfld_simps, hasDerivWithinAt_univ]
  change HasDerivAt ((extChartAt 𝓘(ℝ, E) xₜ ∘ (extChartAt 𝓘(ℝ, E) c).symm) ∘ α) (w xₜ) t
  rw [← tangentCoordChange_self (I := 𝓘(ℝ, E)) (x := xₜ) (z := xₜ) (v := w xₜ) hft2,
    ← tangentCoordChange_comp (x := c) ⟨⟨hft2, hft1⟩, hft2⟩]
  apply HasFDerivAt.comp_hasDerivAt _ _ hα
  apply HasFDerivWithinAt.hasFDerivAt (s := range 𝓘(ℝ, E)) _ <|
    mem_nhds_iff.mpr ⟨(extChartAt 𝓘(ℝ, E) c).target,
      extChartAt_target_subset_range .., isOpen_extChartAt_target c, ht⟩
  rw [← (extChartAt 𝓘(ℝ, E) c).right_inv ht]
  exact hasFDerivWithinAt_tangentCoordChange ⟨hft1, hft2⟩

open Classical in
/-- **Picard–Lindelöf, local flow with confinement**: mathlib's continuous local flow, together with
the fact that its curves stay in the ball `closedBall x₀ a` (`FunSpace.compProj_mem_closedBall`). -/
theorem exists_localFlow_mem_closedBall {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {f : ℝ → F → F} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ : F}
    {a r L K : ℝ≥0} (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    ∃ α : F × ℝ → F, (∀ x ∈ closedBall x₀ r, α ⟨x, t₀⟩ = x ∧
      ∀ t ∈ Icc tmin tmax, HasDerivWithinAt (α ⟨x, ·⟩) (f t (α ⟨x, t⟩)) (Icc tmin tmax) t ∧
        α ⟨x, t⟩ ∈ closedBall x₀ a) ∧
      ContinuousOn α (closedBall x₀ r ×ˢ Icc tmin tmax) := by
  have (x) (hx : x ∈ closedBall x₀ r) := ODE.FunSpace.exists_isFixedPt_next hf hx
  choose α hα using this
  set α' := fun (x : F) ↦ if hx : x ∈ closedBall x₀ r then
    α x hx |>.compProj else 0 with hα'
  have hder : ∀ x ∈ closedBall x₀ r, α' x t₀ = x ∧
      ∀ t ∈ Icc tmin tmax, HasDerivWithinAt (α' x) (f t (α' x t)) (Icc tmin tmax) t := by
    intro x hx
    refine ⟨?_, fun t ht => ?_⟩
    · rw [hα']
      beta_reduce
      rw [dif_pos hx, ODE.FunSpace.compProj_val, ← hα, ODE.FunSpace.next_apply₀]
    · rw [hα']
      beta_reduce
      rw [dif_pos hx, ODE.FunSpace.compProj_apply]
      apply ODE.hasDerivWithinAt_picard_Icc t₀.2 hf.continuousOn_uncurry
        (α x hx |>.continuous_compProj.continuousOn)
        (fun _ ht' ↦ α x hx |>.compProj_mem_closedBall hf.mul_max_le)
        x ht |>.congr_of_mem _ ht
      intro t' ht'
      nth_rw 1 [← hα]
      rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]
  obtain ⟨L', h⟩ := ODE.FunSpace.exists_forall_closedBall_funSpace_dist_le_mul hf
  have hlip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith L' (α' · t) (closedBall x₀ r) := by
    refine fun t ht ↦ LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_
    simp_rw [hα']
    rw [dif_pos hx, dif_pos hy, ODE.FunSpace.compProj_apply, ODE.FunSpace.compProj_apply,
      ← ODE.FunSpace.toContinuousMap_apply_eq_apply, ← ODE.FunSpace.toContinuousMap_apply_eq_apply]
    have : Nonempty (Icc tmin tmax) := ⟨t₀⟩
    apply ContinuousMap.dist_le_iff_of_nonempty.mp
    exact h x y hx hy (α x hx) (α y hy) (hα x hx) (hα y hy)
  refine ⟨uncurry α', fun x hx => ⟨(hder x hx).1, fun t ht => ⟨(hder x hx).2 t ht, ?_⟩⟩, ?_⟩
  · simp only [uncurry_apply_pair, hα', dif_pos hx]
    exact (α x hx).compProj_mem_closedBall hf.mul_max_le
  · apply continuousOn_prod_of_continuousOn_lipschitzOnWith _ L' _ hlip
    exact fun x hx ↦ HasDerivWithinAt.continuousOn (hder x hx).2


omit [IsManifold 𝓘(ℝ, E) ∞ N] [FiniteDimensional ℝ E] in
theorem extChartAt_self_facts (x : N) :
    (⇑(extChartAt 𝓘(ℝ, E) x) = chartAt E x) ∧
      (⇑(extChartAt 𝓘(ℝ, E) x).symm = (chartAt E x).symm) ∧
      (extChartAt 𝓘(ℝ, E) x).source = (chartAt E x).source ∧
      (extChartAt 𝓘(ℝ, E) x).target = (chartAt E x).target := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp

omit [IsManifold 𝓘(ℝ, E) ∞ N] in
/-- **A locally finite cover by chart balls, with a uniform inner margin.** Countably-indexed
chart balls `B j = φⱼ⁻¹(ball (φⱼ cⱼ) Rⱼ)` (closed ball inside the chart target), locally finite,
and every point `x` has some `j` with `closedBall (φⱼ x) δⱼ ⊆ ball (φⱼ cⱼ) Rⱼ`. -/
theorem exists_chart_cover [T2Space N] [SigmaCompactSpace N] :
    ∃ (ι : Type uN) (c : ι → N) (R δ : ι → ℝ),
      (∀ j, 0 < δ j ∧
        closedBall (extChartAt 𝓘(ℝ, E) (c j) (c j)) (R j) ⊆ (extChartAt 𝓘(ℝ, E) (c j)).target) ∧
      LocallyFinite (fun j => extChartAt 𝓘(ℝ, E) (c j) ⁻¹'
        ball (extChartAt 𝓘(ℝ, E) (c j) (c j)) (R j) ∩ (extChartAt 𝓘(ℝ, E) (c j)).source) ∧
      ∀ x, ∃ j, x ∈ (extChartAt 𝓘(ℝ, E) (c j)).source ∧
        closedBall (extChartAt 𝓘(ℝ, E) (c j) x) (δ j) ⊆
          ball (extChartAt 𝓘(ℝ, E) (c j) (c j)) (R j) := by
  haveI : LocallyCompactSpace N := ChartedSpace.locallyCompactSpace E N
  simp only [extChartAt_self_facts]
  have hB : ∀ x ∈ (univ : Set N), (𝓝 x).HasBasis
      (fun R : ℝ => 0 < R ∧ closedBall (chartAt E x x) R ⊆ (chartAt E x).target)
      (fun R => chartAt E x ⁻¹' ball (chartAt E x x) R ∩ (chartAt E x).source) := by
    intro x _
    rw [(chartAt E x).nhds_eq_comap_inf_principal (mem_chart_source E x)]
    refine ((nhds_basis_ball.comap (chartAt E x)).inf_principal _).restrict fun R hR => ?_
    obtain ⟨ρ, hρ, hρs⟩ := Metric.isOpen_iff.1 (chartAt E x).open_target _
      ((chartAt E x).map_source (mem_chart_source E x))
    refine ⟨min R (ρ / 2), lt_min hR (half_pos hρ),
      (closedBall_subset_ball (lt_of_le_of_lt (min_le_right _ _) (half_lt_self hρ))).trans hρs,
      inter_subset_inter_left _ (preimage_mono (ball_subset_ball (min_le_left _ _)))⟩
  obtain ⟨ι, c, R, hR, hcov, hlf⟩ :=
    refinement_of_locallyCompact_sigmaCompact_of_nhds_basis_set isClosed_univ hB
  set B : ι → Set N := fun j =>
    chartAt E (c j) ⁻¹' ball (chartAt E (c j) (c j)) (R j) ∩ (chartAt E (c j)).source with hBdef
  have hBo : ∀ j, IsOpen (B j) := fun j => by
    show IsOpen (_ ∩ _)
    rw [inter_comm]; exact (chartAt E (c j)).isOpen_inter_preimage isOpen_ball
  obtain ⟨D, hDcov, hDc, hDB⟩ := exists_subset_iUnion_closed_subset isClosed_univ hBo
    (fun x _ => hlf.point_finite x) hcov
  have hδ : ∀ j, ∃ δ, 0 < δ ∧ ∀ x ∈ D j,
      closedBall (chartAt E (c j) x) δ ⊆ ball (chartAt E (c j) (c j)) (R j) := by
    intro j
    set e := chartAt E (c j)
    have hK : IsCompact (e.symm '' closedBall (e (c j)) (R j)) :=
      (isCompact_closedBall _ _).image_of_continuousOn (e.continuousOn_symm.mono (hR j).2.2)
    have hBK : B j ⊆ e.symm '' closedBall (e (c j)) (R j) := fun y hy =>
      ⟨e y, ball_subset_closedBall hy.1, e.left_inv hy.2⟩
    have hDK : IsCompact (D j) := hK.of_isClosed_subset (hDc j) ((hDB j).trans hBK)
    have hDs : D j ⊆ e.source := (hDB j).trans inter_subset_right
    have hImg : IsCompact (e '' D j) := hDK.image_of_continuousOn (e.continuousOn.mono hDs)
    obtain ⟨δ, hδ, hsub⟩ := hImg.exists_cthickening_subset_open isOpen_ball
      (image_subset_iff.2 fun y hy => ((hDB j) hy).1)
    exact ⟨δ, hδ, fun x hx => (closedBall_subset_cthickening (mem_image_of_mem e hx) δ).trans hsub⟩
  choose δ hδpos hδsub using hδ
  refine ⟨ι, c, R, δ, fun j => ⟨hδpos j, (hR j).2.2⟩, hlf, fun x => ?_⟩
  obtain ⟨j, hj⟩ := mem_iUnion.1 (hDcov (mem_univ x))
  exact ⟨j, ((hDB j) hj).2, hδsub j x hj⟩

/-- **A local flow from a chart bound.** If, in the chart at `c`, the coordinate field of `w` is
bounded by `δ / 2` on `closedBall (φ x₀) δ ⊆ target`, then the integral curves of `w` from the
points near `x₀` exist on `(-1, 1)` and form a map continuous at every `(s, x₀)`, `|s| < 1`
(Picard–Lindelöf with `a = δ`, `r = L = δ / 2`, time interval `[-1, 1]`). -/
theorem exists_localFlow_of_chartBound {w : (x : N) → TangentSpace 𝓘(ℝ, E) x}
    (hw : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1 (fun x => (⟨x, w x⟩ : TangentBundle 𝓘(ℝ, E) N)))
    {c x₀ : N} {δ : ℝ} (hδ : 0 < δ) (hx₀ : x₀ ∈ (extChartAt 𝓘(ℝ, E) c).source)
    (hsub : closedBall (extChartAt 𝓘(ℝ, E) c x₀) δ ⊆ (extChartAt 𝓘(ℝ, E) c).target)
    (hb : ∀ z ∈ closedBall (extChartAt 𝓘(ℝ, E) c x₀) δ, ‖chartField w c z‖ ≤ δ / 2) :
    ∃ U ∈ 𝓝 x₀, ∃ Ψ : ℝ × N → N,
      (∀ x ∈ U, Ψ (0, x) = x ∧ IsMIntegralCurveOn (fun t => Ψ (t, x)) w (Ioo (-1) 1)) ∧
      ∀ s ∈ Ioo (-1 : ℝ) 1, ContinuousAt Ψ (s, x₀) := by
  set φ := extChartAt 𝓘(ℝ, E) c with hφ
  set z₀ := φ x₀ with hz₀
  obtain ⟨K, hK⟩ := ((contDiffOn_chartField hw c).mono hsub).exists_lipschitzOnWith one_ne_zero
    (convex_closedBall _ _) (isCompact_closedBall _ _)
  have hPL : IsPicardLindelof (fun _ => chartField w c) (tmin := -1) (tmax := 1)
      ⟨0, by norm_num⟩ z₀ ⟨δ, hδ.le⟩ ⟨δ / 2, by positivity⟩ ⟨δ / 2, by positivity⟩ K := by
    apply IsPicardLindelof.of_time_independent
    · intro z hz; exact hb z hz
    · exact hK
    · change (δ / 2 : ℝ) * max ((1 : ℝ) - 0) (0 - -1) ≤ δ - δ / 2
      norm_num; linarith
  obtain ⟨α, hα, hαc⟩ := exists_localFlow_mem_closedBall hPL
  change (∀ x ∈ closedBall z₀ (δ / 2), α (x, 0) = x ∧ ∀ t ∈ Icc (-1 : ℝ) 1,
      HasDerivWithinAt (fun t => α (x, t)) (chartField w c (α (x, t))) (Icc (-1) 1) t ∧
        α (x, t) ∈ closedBall z₀ δ) at hα
  change ContinuousOn α (closedBall z₀ (δ / 2) ×ˢ Icc (-1) 1) at hαc
  refine ⟨φ ⁻¹' ball z₀ (δ / 2) ∩ φ.source,
    inter_mem ((continuousAt_extChartAt' hx₀).preimage_mem_nhds (ball_mem_nhds _ (half_pos hδ)))
      (extChartAt_source_mem_nhds' hx₀),
    fun p => φ.symm (α (φ p.2, p.1)), fun x hx => ⟨?_, fun t ht => ?_⟩, fun s hs => ?_⟩
  · have := (hα (φ x) (ball_subset_closedBall hx.1)).1
    simp only at this ⊢
    rw [this, φ.left_inv hx.2]
  · have h := (hα (φ x) (ball_subset_closedBall hx.1)).2 t (Ioo_subset_Icc_self ht)
    have hd : HasDerivAt (fun t => α (φ x, t)) (chartField w c (α (φ x, t))) t :=
      h.1.hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    exact (hasMFDerivAt_symm_comp hd (hsub h.2)).hasMFDerivWithinAt
  · have h1 : ContinuousAt (fun p : ℝ × N => (φ p.2, p.1)) (s, x₀) :=
      ((continuousAt_extChartAt' hx₀).comp continuousAt_snd).prodMk continuousAt_fst
    have h2 : ContinuousAt α (z₀, s) := hαc.continuousAt
      (prod_mem_nhds (closedBall_mem_nhds z₀ (half_pos hδ)) (Icc_mem_nhds hs.1 hs.2))
    have hmem := ((hα z₀ (mem_closedBall_self (half_pos hδ).le)).2 s (Ioo_subset_Icc_self hs)).2
    have h3 : ContinuousAt φ.symm (α (z₀, s)) := continuousAt_extChartAt_symm'' (hsub hmem)
    exact h3.comp (f := fun p : ℝ × N => α (φ p.2, p.1)) (h2.comp (f := fun p : ℝ × N => (φ p.2, p.1)) h1)

omit [FiniteDimensional ℝ E] in
/-- **Local flows of uniform time glue to a global continuous flow.** If every point has local
integral curves on `(-1, 1)` from a neighbourhood, continuous at `(s, x₀)` for `|s| < 1`, then the
global integral curves exist (uniform time, `exists_isMIntegralCurve_of_isMIntegralCurveOn`) and
`(t, x) ↦ Φ t x` is continuous: near `|s| < 1` by uniqueness, then everywhere from
`Φ t = Φ (t / 2) ∘ Φ (t / 2)` by doubling. -/
theorem exists_global_flow_of_local [CompleteSpace E] [T2Space N]
    {w : (x : N) → TangentSpace 𝓘(ℝ, E) x}
    (hw : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1 (fun x => (⟨x, w x⟩ : TangentBundle 𝓘(ℝ, E) N)))
    (hloc : ∀ x₀ : N, ∃ U ∈ 𝓝 x₀, ∃ Ψ : ℝ × N → N,
      (∀ x ∈ U, Ψ (0, x) = x ∧ IsMIntegralCurveOn (fun t => Ψ (t, x)) w (Ioo (-1) 1)) ∧
      ∀ s ∈ Ioo (-1 : ℝ) 1, ContinuousAt Ψ (s, x₀)) :
    ∃ Φ : ℝ → N → N, (∀ x, Φ 0 x = x) ∧ (∀ x, IsMIntegralCurve (fun t => Φ t x) w) ∧
      Continuous (Function.uncurry Φ) := by
  have hex : ∀ x : N, ∃ γ : ℝ → N, γ 0 = x ∧ IsMIntegralCurve γ w :=
    exists_isMIntegralCurve_of_isMIntegralCurveOn hw one_pos fun x => by
      obtain ⟨U, hU, Ψ, hΨ, -⟩ := hloc x
      exact ⟨_, (hΨ x (mem_of_mem_nhds hU)).1, (hΨ x (mem_of_mem_nhds hU)).2⟩
  choose γ hγ0 hγ using hex
  refine ⟨fun t x => γ x t, hγ0, hγ, ?_⟩
  have hadd : ∀ a b x, γ x (a + b) = γ (γ x b) a := fun a b x => by
    have h1 : IsMIntegralCurve (fun t => γ x (t + b)) w := (hγ x).comp_add b
    have h := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0) hw h1 (hγ (γ x b))
      (by simp only [zero_add, hγ0])
    exact congrFun h a
  have h0 : ∀ p : ℝ × N, p.1 ∈ Ioo (-1 : ℝ) 1 →
      ContinuousAt (Function.uncurry fun t x => γ x t) p := by
    rintro ⟨s, x₀⟩ hs
    obtain ⟨U, hU, Ψ, hΨ, hΨc⟩ := hloc x₀
    refine (hΨc s hs).congr_of_eventuallyEq ?_
    filter_upwards [prod_mem_nhds (Ioo_mem_nhds hs.1 hs.2) hU] with p hp
    exact isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless (t₀ := 0) (by norm_num) hw
      ((hγ p.2).isMIntegralCurveOn _) (hΨ p.2 hp.2).2 (by rw [hγ0, (hΨ p.2 hp.2).1]) hp.1
  have hP : ∀ m : ℕ, ∀ p : ℝ × N, |p.1| < 2 ^ m →
      ContinuousAt (Function.uncurry fun t x => γ x t) p := by
    intro m
    induction m with
    | zero =>
      intro p hp
      simp only [pow_zero] at hp
      exact h0 p (abs_lt.1 hp)
    | succ m ih =>
      intro p hp
      have hhalf : |p.1 / 2| < 2 ^ m := by
        rw [abs_div, abs_two, div_lt_iff₀ two_pos, ← pow_succ]; exact hp
      have heq : (Function.uncurry fun t x => γ x t) =
          fun q : ℝ × N => γ (γ q.2 (q.1 / 2)) (q.1 / 2) := by
        funext q
        show γ q.2 q.1 = _
        rw [← hadd]; congr 1; ring
      rw [heq]
      have hin : ContinuousAt (fun q : ℝ × N => (q.1 / 2, γ q.2 (q.1 / 2))) p := by
        refine (continuous_fst.div_const 2).continuousAt.prodMk ?_
        have hc := ih (p.1 / 2, p.2) hhalf
        exact hc.comp (f := fun q : ℝ × N => (q.1 / 2, q.2))
          ((continuous_fst.div_const 2).prodMk continuous_snd).continuousAt
      exact (ih _ hhalf).comp hin
  refine continuous_iff_continuousAt.2 fun p => ?_
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt |p.1| one_lt_two
  exact hP m p hm

/-- **The rescaling.** On a σ-compact Hausdorff manifold, a smooth field `v` has a positive smooth
multiple `f • v` whose coordinate field is, at every point `x₀`, bounded by `δ / 2` on a closed
chart ball of radius `δ` about `x₀` (some chart, some `δ`): on the `j`-th ball of a locally finite
chart cover `f ≤ δⱼ / (2 (Mⱼ + 1))`, `Mⱼ` the bound of the coordinate field of `v` there, glued by
`exists_contMDiffMap_forall_mem_convex_of_local_const`. -/
theorem exists_rescaling_chartBound [T2Space N] [SigmaCompactSpace N]
    (v : Cₛ^∞⟮𝓘(ℝ, E); E, TangentSpace 𝓘(ℝ, E)⟯) :
    ∃ f : C^∞⟮𝓘(ℝ, E), N; 𝓘(ℝ, ℝ), ℝ⟯, (∀ x, 0 < f x) ∧ ∀ x₀ : N, ∃ c : N, ∃ δ : ℝ, 0 < δ ∧
      x₀ ∈ (extChartAt 𝓘(ℝ, E) c).source ∧
      closedBall (extChartAt 𝓘(ℝ, E) c x₀) δ ⊆ (extChartAt 𝓘(ℝ, E) c).target ∧
      ∀ z ∈ closedBall (extChartAt 𝓘(ℝ, E) c x₀) δ,
        ‖chartField (fun y => f y • v y) c z‖ ≤ δ / 2 := by
  obtain ⟨ι, c, R, δ, hRδ, hlf, hcov⟩ := exists_chart_cover (E := E) (N := N)
  have hv1 : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1
      (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) N)) :=
    v.contMDiff.of_le (by norm_cast)
  have hM : ∀ j, ∃ M, ∀ z ∈ closedBall (extChartAt 𝓘(ℝ, E) (c j) (c j)) (R j),
      ‖chartField v (c j) z‖ ≤ M := fun j =>
    (isCompact_closedBall _ _).exists_bound_of_continuousOn
      ((contDiffOn_chartField hv1 (c j)).continuousOn.mono (hRδ j).2)
  choose M hM using hM
  set β : ι → ℝ := fun j => δ j / (2 * (max (M j) 0 + 1)) with hβdef
  have hβ : ∀ j, 0 < β j := fun j => by
    have := (hRδ j).1
    have : 0 ≤ max (M j) 0 := le_max_right _ _
    positivity
  set O : ι → Set N := fun j => extChartAt 𝓘(ℝ, E) (c j) ⁻¹'
    ball (extChartAt 𝓘(ℝ, E) (c j) (c j)) (R j) ∩ (extChartAt 𝓘(ℝ, E) (c j)).source with hOdef
  set t : N → Set ℝ := fun y => {s | 0 < s ∧ ∀ j, y ∈ O j → s ≤ β j} with htdef
  have ht : ∀ y, Convex ℝ (t y) := fun y a ha b hb p q hp hq hpq =>
    ⟨(convex_Ioi (0 : ℝ)) ha.1 hb.1 hp hq hpq,
      fun j hj => (convex_Iic (β j)) (ha.2 j hj) (hb.2 j hj) hp hq hpq⟩
  have hloc : ∀ x : N, ∃ s : ℝ, ∀ᶠ y in 𝓝 x, s ∈ t y := by
    intro x
    obtain ⟨U, hU, hfin⟩ := hlf x
    refine ⟨1 / (1 + ∑ j ∈ hfin.toFinset, 1 / β j), mem_of_superset hU fun y hy => ?_⟩
    have hpos : 0 < 1 + ∑ j ∈ hfin.toFinset, 1 / β j := by
      have : 0 ≤ ∑ j ∈ hfin.toFinset, 1 / β j :=
        Finset.sum_nonneg fun i _ => (one_div_pos.2 (hβ i)).le
      linarith
    refine ⟨one_div_pos.2 hpos, fun j hj => ?_⟩
    have hjS : j ∈ hfin.toFinset := hfin.mem_toFinset.2 ⟨y, hj, hy⟩
    rw [one_div_le hpos (hβ j)]
    have := Finset.single_le_sum (f := fun j => 1 / β j)
      (fun i _ => (one_div_pos.2 (hβ i)).le) hjS
    linarith
  obtain ⟨f, hf⟩ := exists_contMDiffMap_forall_mem_convex_of_local_const 𝓘(ℝ, E) (n := ⊤) ht hloc
  refine ⟨f, fun x => (hf x).1, fun x₀ => ?_⟩
  obtain ⟨j, hj, hball⟩ := hcov x₀
  refine ⟨c j, δ j, (hRδ j).1, hj, hball.trans (ball_subset_closedBall.trans (hRδ j).2),
    fun z hz => ?_⟩
  have hzb := hball hz
  have hzt : z ∈ (extChartAt 𝓘(ℝ, E) (c j)).target := (hRδ j).2 (ball_subset_closedBall hzb)
  have hyO : (extChartAt 𝓘(ℝ, E) (c j)).symm z ∈ O j :=
    ⟨by rw [mem_preimage, (extChartAt 𝓘(ℝ, E) (c j)).right_inv hzt]; exact hzb,
      (extChartAt 𝓘(ℝ, E) (c j)).map_target hzt⟩
  rw [chartField_smul, norm_smul, Real.norm_of_nonneg (hf _).1.le]
  have h1 := (hf _).2 j hyO
  have h2 := hM j z (ball_subset_closedBall hzb)
  calc f ((extChartAt 𝓘(ℝ, E) (c j)).symm z) * ‖chartField v (c j) z‖
      ≤ β j * (max (M j) 0 + 1) :=
        mul_le_mul h1 (by linarith [le_max_left (M j) 0]) (norm_nonneg _) (hβ j).le
    _ = δ j / 2 := by
        have : 0 < max (M j) 0 + 1 := by have := le_max_right (M j) 0; linarith
        rw [hβdef]; field_simp

end ODEFlow

/-- **The ODE input — a pure-ODE statement on a manifold, with no causality in it.** On a
σ-compact Hausdorff smooth manifold modelled on a finite-dimensional space, every smooth vector
field `v` becomes complete after multiplication by a positive smooth function `f`, and the global
integral curves `Φ · x` of `f • v` depend continuously on `(t, x)`. Classical (the fundamental
theorem on flows, with completeness by rescaling); proved from the chart-ball rescaling
(`ODEFlow.exists_rescaling_chartBound`), Picard–Lindelöf in charts
(`ODEFlow.exists_localFlow_of_chartBound`) and the gluing (`ODEFlow.exists_global_flow_of_local`).
The group law of the flow is not part of it (`exists_flow_of_isMIntegralCurve`). -/
theorem exists_complete_rescaling_continuous [T2Space N] [SigmaCompactSpace N]
    (v : Cₛ^∞⟮𝓘(ℝ, E); E, TangentSpace 𝓘(ℝ, E)⟯) :
    ∃ f : C^∞⟮𝓘(ℝ, E), N; 𝓘(ℝ, ℝ), ℝ⟯, (∀ x, 0 < f x) ∧
      ∃ Φ : ℝ → N → N, (∀ x, Φ 0 x = x) ∧
        (∀ x, IsMIntegralCurve (fun t => Φ t x) (fun y => f y • v y)) ∧
        Continuous (Function.uncurry Φ) := by
  obtain ⟨f, hf, hb⟩ := ODEFlow.exists_rescaling_chartBound v
  have hw : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1
      (fun x => (⟨x, f x • v x⟩ : TangentBundle 𝓘(ℝ, E) N)) :=
    (f.contMDiff.smul_section v.contMDiff).of_le (by norm_cast)
  refine ⟨f, hf, ODEFlow.exists_global_flow_of_local hw fun x₀ => ?_⟩
  obtain ⟨c, δ, hδ, hx₀, hsub, hbd⟩ := hb x₀
  exact ODEFlow.exists_localFlow_of_chartBound hw hδ hx₀ hsub hbd

omit [FiniteDimensional ℝ E] in
/-- **Global integral curves depending continuously on the initial point form a flow**: the group
law is the uniqueness of integral curves of a `C¹` field (`isMIntegralCurve_eq_of_contMDiff`,
boundaryless). -/
theorem exists_flow_of_isMIntegralCurve [T2Space N] {w : (x : N) → TangentSpace 𝓘(ℝ, E) x}
    (hw : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1 (fun x => (⟨x, w x⟩ : TangentBundle 𝓘(ℝ, E) N)))
    {Φ : ℝ → N → N} (h0 : ∀ x, Φ 0 x = x) (hΦ : ∀ x, IsMIntegralCurve (fun t => Φ t x) w)
    (hc : Continuous (Function.uncurry Φ)) : ∃ φ : Flow ℝ N, ∀ t x, φ t x = Φ t x := by
  refine ⟨{ toFun := Φ, cont' := hc, map_add' := fun t₁ t₂ x => ?_, map_zero' := h0 },
    fun _ _ => rfl⟩
  have h1 : IsMIntegralCurve (fun t => Φ (t + t₂) x) w := IsMIntegralCurve.comp_add (hΦ x) t₂
  have h := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0) hw h1 (hΦ (Φ t₂ x))
    (by simp only [zero_add, h0])
  exact congrFun h t₁

/-- **The ODE input as a flow**: a smooth vector field, rescaled by a positive smooth function,
has a global flow. -/
theorem exists_flow_isMIntegralCurve_smul [T2Space N] [SigmaCompactSpace N]
    (v : Cₛ^∞⟮𝓘(ℝ, E); E, TangentSpace 𝓘(ℝ, E)⟯) :
    ∃ (f : N → ℝ) (φ : Flow ℝ N), (∀ x, 0 < f x) ∧
      ∀ x, IsMIntegralCurve (fun t => φ t x) (fun y => f y • v y) := by
  obtain ⟨f, hf, Φ, h0, hΦ, hc⟩ := exists_complete_rescaling_continuous v
  have hw : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1
      (fun x => (⟨x, f x • v x⟩ : TangentBundle 𝓘(ℝ, E) N)) :=
    (f.contMDiff.smul_section v.contMDiff).of_le (by norm_cast)
  obtain ⟨φ, hφ⟩ := exists_flow_of_isMIntegralCurve hw h0 hΦ hc
  refine ⟨f, φ, hf, fun x => ?_⟩
  simp only [hφ]
  exact hΦ x


end ODE

/-! ### Target 4: a smooth future timelike field on a flat spacetime, and its orbits -/

section FlowFieldSection

open Manifold Bundle
open scoped ContDiff

namespace Flat

namespace FlowField

variable {d : ℕ}

/-- A future timelike vector has spatial norm below its time component. -/
theorem norm_snd_lt_fst_of_isFutureTimelike {w : Minkowski d} (hw : IsFutureTimelike w) :
    ‖w.2‖ < w.1 := by
  have h := minkQ_lt_zero_iff.1 hw.2
  exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hw.1.le two_ne_zero).1 h

/-- **The chord of a curve with future timelike velocity is future timelike.** If `γ` has, at
every point of `[s, s']`, `s < s'`, a future timelike derivative, then `γ s'` lies in the open
future cone of `γ s`. The functional `ℓ v = v.1 - ⟪u, v.2⟫`, `u` the direction of the spatial
displacement, is positive on future timelike vectors, so `ℓ ∘ γ` is strictly increasing. -/
theorem chord_lt_of_hasDerivAt' {γ : ℝ → Minkowski d} {w : ℝ → Minkowski d} {s s' : ℝ}
    (hss' : s < s') (hγ : ∀ σ ∈ Icc s s', HasDerivAt γ (w σ) σ)
    (hw : ∀ σ ∈ Icc s s', IsFutureTimelike (w σ)) :
    ‖(γ s').2 - (γ s).2‖ < (γ s').1 - (γ s).1 := by
  set Δ := (γ s').2 - (γ s).2
  set u : EuclideanSpace ℝ (Fin d) := (‖Δ‖)⁻¹ • Δ
  have hu : ‖u‖ ≤ 1 := by
    rcases eq_or_ne ‖Δ‖ 0 with h | h
    · simp [u, h]
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ h]
  set ℓ : Minkowski d →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin d)) -
    (innerSL ℝ u).comp (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin d)))
  have hℓ : ∀ v : Minkowski d, ℓ v = v.1 - inner ℝ u v.2 := fun v => rfl
  have hpos : ∀ σ ∈ Icc s s', 0 < ℓ (w σ) := fun σ hσ => by
    rw [hℓ]
    have h1 := norm_snd_lt_fst_of_isFutureTimelike (hw σ hσ)
    have h2 : inner ℝ u (w σ).2 ≤ ‖(w σ).2‖ :=
      (real_inner_le_norm _ _).trans (by nlinarith [norm_nonneg (w σ).2, norm_nonneg u])
    linarith
  have hmono : StrictMonoOn (fun σ => ℓ (γ σ)) (Icc s s') := by
    apply strictMonoOn_of_deriv_pos (convex_Icc s s')
    · exact fun σ hσ => (ℓ.hasFDerivAt.comp_hasDerivAt σ (hγ σ hσ)).continuousAt.continuousWithinAt
    · intro σ hσ
      rw [interior_Icc] at hσ
      have hσ' : σ ∈ Icc s s' := Ioo_subset_Icc_self hσ
      rw [show deriv (fun σ => ℓ (γ σ)) σ = ℓ (w σ) from
        (ℓ.hasFDerivAt.comp_hasDerivAt σ (hγ σ hσ')).deriv]
      exact hpos σ hσ'
  have hlt := hmono (left_mem_Icc.2 hss'.le) (right_mem_Icc.2 hss'.le) hss'
  simp only at hlt
  have hlin : ℓ (γ s') - ℓ (γ s) = ((γ s').1 - (γ s).1) - ‖Δ‖ := by
    rw [← map_sub, hℓ]
    congr 1
    show inner ℝ u Δ = ‖Δ‖
    rcases eq_or_ne ‖Δ‖ 0 with h | h
    · rw [norm_eq_zero.1 h]; simp
    · rw [real_inner_smul_left, real_inner_self_eq_norm_sq]; field_simp
  linarith

/-- `chord_lt_of_hasDerivAt'` with the velocity given pointwise. -/
theorem chord_lt_of_hasDerivAt {γ : ℝ → Minkowski d} {s s' : ℝ} (hss' : s < s')
    (hγ : ∀ σ ∈ Icc s s', ∃ w, IsFutureTimelike w ∧ HasDerivAt γ w σ) :
    ‖(γ s').2 - (γ s).2‖ < (γ s').1 - (γ s).1 := by
  choose! w hw hγ' using hγ
  exact chord_lt_of_hasDerivAt' hss' hγ' hw


variable [ChartedSpace (Minkowski d) M]
  [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))]

variable (d) in
/-- **Future timelike velocity in every chart**: wherever `c` is in the source of the chart at
`p`, the curve read in that chart has a future timelike derivative. -/
def HasFutureTimelikeChartVelocity (c : ℝ → M) : Prop :=
  ∀ (p : M) (s : ℝ), c s ∈ (chartAt (Minkowski d) p).source →
    ∃ w, IsFutureTimelike w ∧ HasDerivAt (fun σ => chartAt (Minkowski d) p (c σ)) w s

/-- **A continuous curve with future timelike velocity in every chart is a chronal curve** of the
flat causality, over every segment. Near `c t`, in the chart at `c t`: a ball around `e (c t)`
inside the chart image of `N`, convex, on which `≪` is the open cone (`lt_iff_of_convex`), and
the chord lemma; the chart is an isomorphism (`flatCausality_chartIso_chartAt`). -/
theorem chronalCurveOn_of_chartVelocity {c : ℝ → M} (hc : Continuous c)
    (hv : HasFutureTimelikeChartVelocity d c) (a b : ℝ) :
    (flatCausality d M).ChronalCurveOn ⊤ c a b := by
  refine ⟨fun _ _ => trivial, fun t _ N _ htN => ?_⟩
  set e := chartAt (Minkowski d) (c t)
  set U : Opens M := N ⊓ chartSource e
  have hU : U ≤ chartSource e := inf_le_right
  have hte : c t ∈ e.source := mem_chart_source _ _
  have htU : c t ∈ U := ⟨htN, hte⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 (chartImage e U).isOpen _
    (mem_chartImage_of_mem hte htU)
  have hO : IsOpen (c ⁻¹' ((e.source ∩ e ⁻¹' Metric.ball (e (c t)) ρ) ∩ U)) :=
    ((e.isOpen_inter_preimage Metric.isOpen_ball).inter U.isOpen).preimage hc
  have htO : t ∈ c ⁻¹' ((e.source ∩ e ⁻¹' Metric.ball (e (c t)) ρ) ∩ U) :=
    ⟨⟨hte, Metric.mem_ball_self hρ⟩, htU⟩
  obtain ⟨l, u, ⟨hl, hu⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1 (hO.mem_nhds htO)
  refine ⟨l, u, hl, hu, fun s _ s' _ h1 h2 h3 => ?_⟩
  have hIcc : ∀ σ ∈ Icc s s', c σ ∈ (e.source ∩ e ⁻¹' Metric.ball (e (c t)) ρ) ∩ U :=
    fun σ hσ => hsub ⟨h1.trans_le hσ.1, hσ.2.trans_lt h3⟩
  have hs := hIcc s (left_mem_Icc.2 h2.le)
  have hs' := hIcc s' (right_mem_Icc.2 h2.le)
  have hchord := chord_lt_of_hasDerivAt (γ := fun σ => e (c σ)) h2
    fun σ hσ => hv (c t) σ (hIcc σ hσ).1.1
  set V : Opens (Minkowski d) := ⟨Metric.ball (e (c t)) ρ, Metric.isOpen_ball⟩
  have hlt : (minkowski d).lt V (e (c s)) (e (c s')) :=
    (lt_iff_of_convex (V := V) (convex_ball _ _)).2 ⟨hs.1.2, hs'.1.2, minkowski_lt_top_iff.2 hchord⟩
  have hlt' : (minkowski d).lt (chartImage e U) (e (c s)) (e (c s')) :=
    (minkowski d).lt_mono (show V ≤ chartImage e U from hball) hlt
  have := ((flatCausality_chartIso_chartAt (c t) U hU (c s) hs.2 (c s') hs'.2).2).2 hlt'
  exact (flatCausality d M).lt_mono inf_le_left this



omit [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))] in
/-- **An integral curve read in the chart at its point**: `HasMFDerivAt` from `ℝ` to a manifold
modelled on `𝓘(ℝ, Minkowski d)` is the derivative of the curve read in the chart at `γ s`. -/
theorem hasDerivAt_chartAt_of_hasMFDerivAt {γ : ℝ → M} {s : ℝ} {v : Minkowski d}
    (h : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Minkowski d) γ s ((1 : ℝ →L[ℝ] ℝ).smulRight v)) :
    HasDerivAt (fun σ => chartAt (Minkowski d) (γ s) (γ σ)) v s := by
  have h2 := h.2
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
    PartialEquiv.refl_symm, modelWithCornersSelf_coe, range_id, hasFDerivWithinAt_univ,
    extChartAt_coe, CompTriple.comp_eq, id_eq] at h2
  rw [hasDerivAt_iff_hasFDerivAt]
  exact h2



/-- An affine automorphism of `Minkowski d` is its linear part plus a translation. -/
theorem affineEquiv_eq_linear_add (g : Minkowski d ≃ᵃ[ℝ] Minkowski d) :
    (fun y => g y) = fun y =>
      (LinearMap.toContinuousLinearMap (g.linear : Minkowski d →ₗ[ℝ] Minkowski d)) y + g 0 := by
  funext y
  have := congrFun g.toAffineMap.decomp y
  simpa using this

/-- An affine automorphism of `Minkowski d` is smooth. -/
theorem affineEquiv_contDiff (g : Minkowski d ≃ᵃ[ℝ] Minkowski d) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun y => g y) := by
  rw [affineEquiv_eq_linear_add]
  exact (ContinuousLinearMap.contDiff _).add contDiff_const

/-- **`gxGroupoid (isom d)` consists of smooth maps**: its elements are, near every point, an
affine isometry. -/
theorem gxGroupoid_le_contDiffGroupoid :
    gxGroupoid (isom d) (Minkowski d) ≤ contDiffGroupoid ∞ 𝓘(ℝ, Minkowski d) := by
  apply groupoid_of_pregroupoid_le
  intro f s hf
  simp only [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    range_id, preimage_id_eq, inter_univ, CompTriple.comp_eq]
  intro x hx
  obtain ⟨g, hg⟩ := hf x hx
  exact ((affineEquiv_contDiff (g : Minkowski d ≃ᵃ[ℝ] Minkowski d)).contDiffAt.congr_of_eventuallyEq
    hg).contDiffWithinAt

/-- **A flat spacetime is a smooth manifold** over `𝓘(ℝ, Minkowski d)` (not an instance: the
charted space is fixed by the `(G,X)`-structure, and the smooth structure is derived). -/
theorem isManifold_of_flat : IsManifold 𝓘(ℝ, Minkowski d) ∞ M where
  toHasGroupoid := hasGroupoid_of_le ‹_› gxGroupoid_le_contDiffGroupoid


/-- The open future timelike cone is `‖x‖ < t`. -/
theorem isFutureTimelike_iff {v : Minkowski d} : IsFutureTimelike v ↔ ‖v.2‖ < v.1 := by
  refine ⟨fun hw => (pow_lt_pow_iff_left₀ (norm_nonneg _) hw.1.le two_ne_zero).1
    (minkQ_lt_zero_iff.1 hw.2), fun h => ⟨(norm_nonneg _).trans_lt h, minkQ_lt_zero_iff.2 ?_⟩⟩
  exact pow_lt_pow_left₀ h (norm_nonneg _) two_ne_zero

/-- The open future timelike cone is convex. -/
theorem convex_isFutureTimelike : Convex ℝ {v : Minkowski d | IsFutureTimelike v} := by
  intro v hv w hw a b ha hb hab
  simp only [mem_setOf_eq, isFutureTimelike_iff] at hv hw ⊢
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  calc ‖a • v.2 + b • w.2‖ ≤ a * ‖v.2‖ + b * ‖w.2‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    _ < a * v.1 + b * w.1 := by
        rcases ha.eq_or_lt with h | h
        · subst h; simp only [zero_add] at hab; subst hab; simp; linarith
        · nlinarith

/-- `e₀ = (1, 0)` is future timelike. -/
theorem isFutureTimelike_e0 : IsFutureTimelike ((1, 0) : Minkowski d) :=
  isFutureTimelike_iff.2 (by simp)


/-- The derivative of an affine automorphism is its linear part. -/
theorem affineEquiv_hasFDerivAt (g : Minkowski d ≃ᵃ[ℝ] Minkowski d) (x : Minkowski d) :
    HasFDerivAt (fun y => g y)
      (LinearMap.toContinuousLinearMap (g.linear : Minkowski d →ₗ[ℝ] Minkowski d)) x := by
  have h : (fun y => g y) = fun y =>
      (LinearMap.toContinuousLinearMap (g.linear : Minkowski d →ₗ[ℝ] Minkowski d)) y + g 0 := by
    funext y
    have := congrFun g.toAffineMap.decomp y
    simpa using this
  rw [h]
  exact (ContinuousLinearMap.hasFDerivAt _).add_const _

/-- Near a point of the overlap of two charts of a flat spacetime, the transition is an isometry. -/
theorem exists_isom_chartAt_of_mem {q p z₀ : M} (hq : z₀ ∈ (chartAt (Minkowski d) q).source)
    (hp : z₀ ∈ (chartAt (Minkowski d) p).source) :
    ∃ g : isom d, ∀ᶠ z in 𝓝 z₀, chartAt (Minkowski d) p z = g • chartAt (Minkowski d) q z := by
  have hc := HasGroupoid.compatible (G := gxGroupoid (isom d) (Minkowski d))
    (chart_mem_atlas (Minkowski d) q) (chart_mem_atlas (Minkowski d) p)
  obtain ⟨g, O, hqO, -, hO⟩ := exists_smul_eq_of_mem_gxGroupoid hc hq hp
  exact ⟨g, Filter.mem_of_superset (O.isOpen.mem_nhds hqO) fun z hz => hO z hz⟩

variable [IsManifold 𝓘(ℝ, Minkowski d) ∞ M]

/-- **The tangent coordinate change of a flat manifold is the linear part of an isometry**, so it
maps future timelike vectors to future timelike vectors. -/
theorem tangentCoordChange_isFutureTimelike {x y z : M}
    (hx : z ∈ (chartAt (Minkowski d) x).source) (hy : z ∈ (chartAt (Minkowski d) y).source)
    {v : Minkowski d} (hv : IsFutureTimelike v) :
    IsFutureTimelike (tangentCoordChange 𝓘(ℝ, Minkowski d) x y z v) := by
  obtain ⟨g, hg⟩ := exists_isom_chartAt_of_mem hx hy
  have h1 := hasFDerivWithinAt_tangentCoordChange (I := 𝓘(ℝ, Minkowski d)) (x := x) (y := y)
    (z := z) ⟨by rwa [extChartAt_source], by rwa [extChartAt_source]⟩
  simp only [modelWithCornersSelf_coe, range_id, hasFDerivWithinAt_univ, extChartAt_coe,
    extChartAt_coe_symm, modelWithCornersSelf_coe_symm, CompTriple.comp_eq] at h1
  have hev : (chartAt (Minkowski d) y ∘ (chartAt (Minkowski d) x).symm) =ᶠ[𝓝 (chartAt (Minkowski d) x z)]
      fun w => (g : Minkowski d ≃ᵃ[ℝ] Minkowski d) w := by
    have hcont := (chartAt (Minkowski d) x).continuousAt_symm ((chartAt (Minkowski d) x).map_source hx)
    rw [ContinuousAt, (chartAt (Minkowski d) x).left_inv hx] at hcont
    filter_upwards [hcont.eventually hg, (chartAt (Minkowski d) x).open_target.mem_nhds
      ((chartAt (Minkowski d) x).map_source hx)] with w hw hwt
    simp only [Function.comp] at hw ⊢
    rw [hw, (chartAt (Minkowski d) x).right_inv hwt]
    rfl
  have h2 := (affineEquiv_hasFDerivAt (g : Minkowski d ≃ᵃ[ℝ] Minkowski d)
    (chartAt (Minkowski d) x z)).congr_of_eventuallyEq hev
  rw [h1.unique h2]
  exact lorentz.isFutureTimelike_apply g.2 hv


/-- **A smooth future timelike vector field.** Near `x₀`, the field equal to `e₀` in the chart at
`x₀` (`y ↦ tangentCoordChange x₀ y y e₀`) is smooth and future timelike; the future timelike cone
is convex, and a smooth partition of unity glues the local fields
(`exists_contMDiffSection_forall_mem_convex_of_local`). -/
theorem exists_contMDiff_futureTimelike_section [T2Space M] [SigmaCompactSpace M] :
    ∃ v : Cₛ^∞⟮𝓘(ℝ, Minkowski d); Minkowski d, TangentSpace 𝓘(ℝ, Minkowski d)⟯,
      ∀ x : M, IsFutureTimelike (v x : Minkowski d) := by
  refine exists_contMDiffSection_forall_mem_convex_of_local 𝓘(ℝ, Minkowski d) (n := ⊤)
    (F_fiber := Minkowski d)
    (TangentSpace 𝓘(ℝ, Minkowski d) : M → Type _) (fun _ => {v : Minkowski d | IsFutureTimelike v})
    (fun _ => convex_isFutureTimelike) fun x₀ => ?_
  refine ⟨(chartAt (Minkowski d) x₀).source,
    (chartAt (Minkowski d) x₀).open_source.mem_nhds (mem_chart_source _ x₀),
    fun y => tangentCoordChange 𝓘(ℝ, Minkowski d) x₀ y y ((1, 0) : Minkowski d), ?_,
    fun y hy => tangentCoordChange_isFutureTimelike hy (mem_chart_source _ y) isFutureTimelike_e0⟩
  intro y₀ hy₀
  rw [(trivializationAt (Minkowski d) (TangentSpace 𝓘(ℝ, Minkowski d)) x₀).contMDiffWithinAt_section
    _ (by simpa using hy₀)]
  have key : ∀ y ∈ (chartAt (Minkowski d) x₀).source,
      (trivializationAt (Minkowski d) (TangentSpace 𝓘(ℝ, Minkowski d)) x₀
        ⟨y, tangentCoordChange 𝓘(ℝ, Minkowski d) x₀ y y ((1, 0) : Minkowski d)⟩).2 =
        ((1, 0) : Minkowski d) := fun y hy => by
    rw [TangentBundle.trivializationAt_apply]
    show tangentCoordChange 𝓘(ℝ, Minkowski d) y x₀ y
      (tangentCoordChange 𝓘(ℝ, Minkowski d) x₀ y y ((1, 0) : Minkowski d)) = _
    have hy' : y ∈ (extChartAt 𝓘(ℝ, Minkowski d) x₀).source := by rwa [extChartAt_source]
    have hyy : y ∈ (extChartAt 𝓘(ℝ, Minkowski d) y).source := mem_extChartAt_source y
    rw [tangentCoordChange_comp ⟨⟨hy', hyy⟩, hy'⟩, tangentCoordChange_self hy']
  exact (contMDiffWithinAt_const (c := ((1, 0) : Minkowski d))).congr key (key y₀ hy₀)

omit [IsManifold 𝓘(ℝ, Minkowski d) ∞ M] in
/-- **An integral curve of a future timelike field has future timelike velocity in every chart.** -/
theorem hasFutureTimelikeChartVelocity_of_isMIntegralCurve
    {w : (x : M) → TangentSpace 𝓘(ℝ, Minkowski d) x} (hw : ∀ x, IsFutureTimelike (w x : Minkowski d))
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ w) : HasFutureTimelikeChartVelocity d γ := by
  intro p s hs
  obtain ⟨g, hg⟩ := exists_isom_chartAt_of_mem (mem_chart_source _ (γ s)) hs
  have h1 := hasDerivAt_chartAt_of_hasMFDerivAt (hγ s)
  have h2 := (affineEquiv_hasFDerivAt (g : Minkowski d ≃ᵃ[ℝ] Minkowski d) _).comp_hasDerivAt s h1
  refine ⟨_, lorentz.isFutureTimelike_apply g.2 (hw (γ s)), ?_⟩
  refine h2.congr_of_eventuallyEq ?_
  have hcont : ContinuousAt γ s := (hγ s).1
  filter_upwards [hcont.eventually hg] with σ hσ
  exact hσ


/-- A positive multiple of a future timelike vector is future timelike. -/
theorem isFutureTimelike_smul {c : ℝ} (hc : 0 < c) {v : Minkowski d} (hv : IsFutureTimelike v) :
    IsFutureTimelike (c • v) := by
  rw [isFutureTimelike_iff] at hv ⊢
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, norm_smul, Real.norm_of_nonneg hc.le]
  exact mul_lt_mul_of_pos_left hv hc

omit [IsManifold 𝓘(ℝ, Minkowski d) ∞ M] [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))] in
/-- A curve with future timelike chart velocity is nowhere locally constant; in particular it
leaves its initial point. -/
theorem exists_ne_of_chartVelocity {c : ℝ → M} (hv : HasFutureTimelikeChartVelocity d c) :
    ∃ t, c t ≠ c 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  obtain ⟨w, hw, hd⟩ := hv (c 0) 0 (mem_chart_source _ _)
  have hconst : (fun σ => chartAt (Minkowski d) (c 0) (c σ)) =
      fun _ => chartAt (Minkowski d) (c 0) (c 0) := funext fun σ => by rw [h σ]
  rw [hconst] at hd
  have := hd.unique (hasDerivAt_const 0 _)
  exact absurd (congrArg Prod.fst this) (by simpa using hw.1.ne')

end FlowField

end Flat

end FlowFieldSection

/-! ### Target 4: flat spacetimes -/

namespace Flat

section FlatFlow

variable {d : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (Minkowski d) M]
  [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))]

open scoped Manifold ContDiff in
/-- **Target 4 — every flat spacetime carries a chronal causal flow.** Proved (no `sorry`), with
the pure-ODE lemma `exists_complete_rescaling_continuous` (no causality in it) as ODE input:
`gxGroupoid (isom d) ≤ contDiffGroupoid ∞` (affine maps), so `M` is smooth
(`isManifold_of_flat`); σ-compact from second countability and local compactness; the fields
equal to `e₀` in a chart are future timelike in every chart (the linear parts of `isom d` preserve
the cone, `tangentCoordChange_isFutureTimelike`) and the cone is convex, so a smooth partition of
unity glues them into a smooth future timelike field `v`
(`exists_contMDiff_futureTimelike_section`); `f • v`, `f > 0`, has a flow
(`exists_flow_isMIntegralCurve_smul`); its orbits have future timelike velocity in every chart,
hence are chronal curves (`chronalCurveOn_of_chartVelocity`, by the chord lemma
`chord_lt_of_hasDerivAt`); they are not constant, and the orbits of a fixed-point-free flow are
inextensible (`Causality.inextensible_of_flow`). Nothing in this file depends on it. -/
theorem flat_hasChronalCausalFlow [T2Space M] [SecondCountableTopology M] :
    (flatCausality d M).HasChronalCausalFlow := by
  haveI : IsManifold 𝓘(ℝ, Minkowski d) ∞ M := FlowField.isManifold_of_flat (d := d)
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (Minkowski d) M
  obtain ⟨v, hv⟩ := FlowField.exists_contMDiff_futureTimelike_section (d := d) (M := M)
  obtain ⟨f, φ, hf, hφ⟩ := exists_flow_isMIntegralCurve_smul v
  have hvel : ∀ x, FlowField.HasFutureTimelikeChartVelocity d (fun t => φ t x) := fun x =>
    FlowField.hasFutureTimelikeChartVelocity_of_isMIntegralCurve
      (fun y => FlowField.isFutureTimelike_smul (hf y) (hv y)) (hφ x)
  have hcont : ∀ x, Continuous (fun t => φ t x) := fun x =>
    φ.continuous continuous_id continuous_const
  have hch : (flatCausality d M).IsChronalFlow φ := fun x a b =>
    FlowField.chronalCurveOn_of_chartVelocity (hcont x) (hvel x) a b
  have hcurve : ∀ x, (flatCausality d M).CausalCurveIn ⊤ univ (fun t => φ t x) := fun x =>
    ⟨⟨0, trivial⟩, ordConnected_univ, fun a _ b _ => (hch x a b).causalCurveOn⟩
  have hns : ∀ x, ∃ t, φ t x ≠ x := fun x => by
    obtain ⟨t, ht⟩ := FlowField.exists_ne_of_chartVelocity (hvel x)
    exact ⟨t, by simpa [Flow.map_zero_apply] using ht⟩
  exact ⟨φ, ⟨Causality.inextensible_of_flow hcurve hns, hns⟩, hch⟩

/-- **A flat spacetime with a chronal causal flow splits along every acausal Cauchy surface**
(target 2 through the named hypothesis; does not use `flat_hasChronalCausalFlow`). -/
theorem flat_exists_isCauchySplitting (hflow : (flatCausality d M).HasChronalCausalFlow)
    (hcaus : (flatCausality d M).IsCausal) {S : Set M}
    (hS : (flatCausality d M).IsCauchySurface S) (hac : (flatCausality d M).IsAcausal S) :
    ∃ ψ : S × ℝ ≃ₜ M, (flatCausality d M).IsCauchySplitting S ψ :=
  hflow.nonempty_isCauchySplitting hcaus hS hac

end FlatFlow

/-- **Non-vacuity of target 4's named hypothesis**: Minkowski space, as a flat spacetime, has a
chronal causal flow. -/
theorem flatCausality_self_hasChronalCausalFlow {d : ℕ} :
    (flatCausality d (Minkowski d)).HasChronalCausalFlow := by
  rw [flatCausality_self]; exact minkowski_hasChronalCausalFlow

end Flat

end Causal
