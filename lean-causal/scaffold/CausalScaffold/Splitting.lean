import Causal.CauchyDiamond
import CausalScaffold.Flat.IsomCausal
import Mathlib.Dynamics.Flow

/-!
# The splitting `M ≅ S × ℝ` along a Cauchy surface, from a causal flow

`bprop:splitting` — `GHFspace.tex:2459` (labelled; original l.2426), **not marked**: Barbot cites
it (Beem–Ehrlich) and it needs a flow the library does not build on a flat spacetime
(target 4, `Flat.flat_hasChronalCausalFlow`, a tagged `sorry`). It is proved in full on Minkowski
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
* `CausalScaffold.CompactCauchy` is not built at this commit and is not imported:
  `isLocallyCauchyTwoSided_of_threads` concludes the unfolded body of `IsLocallyCauchyTwoSided`.
* Barbot's last sentence (geodesics of `M̃` meet `S̃`) is not treated.
* Non-vacuity: Minkowski time translation (`minkowski_hasChronalCausalFlow`, flat:
  `Flat.flatCausality_self_hasChronalCausalFlow`); `hinv` of `isCauchySurface_flow_image` for it
  (`minkowskiTimeFlow_inextensible`, `minkowski_isCauchySurface_flow_image`); the timelike line for
  target 3 (`timelikeLine_target3`, and `hloc` of `isLocallyCauchyTwoSided_of_threads`:
  `timelikeLine_hloc`).

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
threads. The conclusion is the body of `IsLocallyCauchyTwoSided S` (`CausalScaffold/CompactCauchy`,
not imported: it is not built at this commit), so `this` closes `C.IsLocallyCauchyTwoSided S` by
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

/-! ### Target 4: flat spacetimes -/

namespace Flat

section FlatFlow

variable {d : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (Minkowski d) M]
  [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))]

/-- **Target 4 — every flat spacetime carries a chronal causal flow. STATED, tagged `sorry`;
nothing in this file depends on it.** The intended proof: `gxGroupoid (isom d)` is contained in
`contDiffGroupoid ⊤ 𝓘(ℝ, Minkowski d)` (affine maps), so `M` is smooth; `e₀` pulled back by the
charts is future timelike, the future timelike cone is convex and preserved by `lorentz d`, so a
smooth partition of unity glues the local fields into a future timelike field `X`; rescale `X` by
a proper positive function to make it complete; its flow is a `Flow ℝ M`, chronal in charts, and
a maximal integral curve with no limit point is inextensible. -/
theorem flat_hasChronalCausalFlow [T2Space M] [SecondCountableTopology M] :
    (flatCausality d M).HasChronalCausalFlow :=
  sorry -- SORRY(target-4): mathlib at fabf563a has no global flow of a complete vector field on a manifold with joint continuity of (t, x) ↦ φ t x — only local flows on a ball of a Banach space (Mathlib/Analysis/ODE/PicardLindelof.lean, IsPicardLindelof) and manifold integral curves (Mathlib/Geometry/Manifold/IntegralCurve/{ExistUnique,UniformTime}: existence and uniqueness, no continuous dependence on the initial point) — and no completeness-by-rescaling; also unformalized here: gxGroupoid (isom d) ⊆ contDiffGroupoid, the gluing of e₀ by a smooth partition of unity into a future timelike field, and the inextensibility of a maximal integral curve in the library's sense (DEC-13), which needs the absence of limit points at the ends (a limit of φ t x as t → ∞ would be a zero of the field).

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
