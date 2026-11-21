import Causal.Inextensible
import Causal.Cauchy
import Causal.LadderLocal

/-!
# The maximal piece in an open set of a time-parametrised causal curve is inextensible

Programme target `T-abs-hoist-inextensible-piece` (`programme/roadmap.toml`; layer 1, stream
abstract, no label of `ETT.tex`; ETT-layer imports only, no model; no metric on the spacetime).
Nothing is marked: the module proves no statement of the paper. It produces inextensible causal
curves (`Causality.Inextensible`, DEC-11 and DEC-13, `Causal.Inextensible`) from a time that reads
the parameter, and makes a Cauchy surface (`Causality.IsCauchySurfaceOn`, DEC-14) meet them.

> Let $M$ be a topological spacetime. A Cauchy surface in $M$ is a subset $S\subset M$ such that
> every causal curve of $M$ meets $S$ exactly once. (`def:cauchy_surface`, `ETT.tex:999–1000`)

DEC-14 reads "causal curve" there as "inextensible causal curve", and `IsCauchySurfaceOn W S`
asks it of the inextensible causal curves of the open set `W`.

## What is here (no `sorry`)

Hoisted out of `Causal.Model.QuasilinearOneSided` (its section 2, written by
T-loc-quasilinear-one-sided), same full names, same statements, text verbatim (kb/0063), namespace
`Causal.Causality`:

* `futureInextensible_of_isLUB_notMem`: a causal curve `c` of `W` over an open `I`, continuous on
  `ℝ`, whose parameter a continuous `T : M → ℝ` reads on `I` (`T (c τ) = τ`), is
  future-inextensible in `W` if `c β ∉ W` at every least upper bound `β` of `I`;
* `pastInextensible_of_isGLB_notMem`: the past end, by time reversal
  (`dual_futureInextensible_iff`);
* `inextensible_connectedComponentIn`: a continuous `ℓ : ℝ → M` whose parameter a continuous `T`
  reads, every segment of which inside `W` is a causal curve of `W`, is an inextensible causal
  curve of `W` over the connected component through `t` of `ℓ⁻¹(W)`, for any `t` with `ℓ t ∈ W`
  (kb/0081);
* `IsCauchySurfaceOn.exists_mem_connectedComponentIn`: a Cauchy surface of `W` meets `ℓ` on that
  piece.

## Hypothesis checklist (`inextensible_connectedComponentIn`)

| hypothesis | role |
|---|---|
| `[T2Space M]` | ✓ carried: at a finite end `β` of the piece, a strict extension would make `ℓ` tend both to a point of `W` and to `ℓ β ∉ W` |
| `ℓ` continuous on `ℝ`, `T` continuous, `T (ℓ τ) = τ` | ✓ carried: at an infinite end, a strict extension would make `T ∘ ℓ`, the identity, bounded there |
| every segment of `ℓ` inside `W` causal in `W` | ✓ carried (`CausalCurveOn W ℓ a b` when `ℓ '' [a, b] ⊆ W`); nothing about `C` outside `W` |
| curves extend, antisymmetry, other separation, countability | none asked |

## SCOPE (disclosed)

* **A verbatim hoist.** HEAD `73eb9a1` `Causal/Model/QuasilinearOneSided.lean` l.186–340
  (`namespace Causality` … `end Causality`) is l.77–231 here, under the same prelude
  (`namespace Causal`, `open Set TopologicalSpace Topology Filter Metric`). The auxiliary matcher
  `inextensible_connectedComponentIn.match_1_1` moved with its theorem under the same name.
  `Causal.Model.QuasilinearOneSided` imports this module; its section 3
  (`slopeLine_mem_of_curveNestedOn`) is the consumer, and through it ERS Lemma 4.86.
* **Imports.** `Causal.Inextensible` and `Causal.Cauchy` hold every notion used; `Causal.LadderLocal`
  (ETT layer) is imported for one instance path (kb/0083). `IsOpen.connectedComponentIn` needs
  `LocallyConnectedSpace ℝ`, which `Causal.Cauchy`'s closure does not provide. In
  `Causal.Model.QuasilinearOneSided`'s closure it was found through `LocallyConvexSpace` and
  `IsModuleTopology` (mathlib's `Topology.Algebra.Module.ModuleTopology`,
  `Analysis.LocallyConvex.WithSeminorms`, `Analysis.InnerProductSpace.Basic`), which
  `Causal.LadderLocal`'s closure has (through `Causal.MeasureRemarks`); with it every proof term
  is the one it was there (environment dump). The proofs use the metric of `ℝ`
  (`Metric.isOpen_iff`, balls of `ℝ`); no statement mentions a metric.
* **Not here.** The sibling `Causality.inextensible_Iio_of_tendsto_not_mem`
  (`Causal.Model.EAlphaCauchy`, target T-loc-ealpha-tidy).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. The hoisted text was
written by T-loc-quasilinear-one-sided (`9bda56f`).
-/

namespace Causal

open Set TopologicalSpace Topology Filter Metric

/-! ### A maximal piece of a time-parametrised curve is inextensible -/

namespace Causality

variable {M : Type*} [TopologicalSpace M] {C : Causality M}

/-- **A curve running out of `W`, or off to infinite time, is future-inextensible.** `c` is a
causal curve of `W` over an open interval `I`, continuous on `ℝ`, and a continuous `T` reads its
parameter on `I`. If `I` is bounded above, its supremum `β` has `c β ∉ W`. A strict extension at
the future end passes, at the supremum `σ` of the reparametrised domain, through `c' σ ∈ W`, which
would be the limit of `c` at `β` (Hausdorff), or a finite limit of `T ∘ c = id` at `+∞`. -/
theorem futureInextensible_of_isLUB_notMem [T2Space M] {W : Opens M} {I : Set ℝ} {c : ℝ → M}
    (hc : C.CausalCurveIn W I c) (hI : IsOpen I) (hcont : Continuous c) {T : M → ℝ}
    (hT : Continuous T) (hTc : ∀ τ ∈ I, T (c τ) = τ) (hend : ∀ β, IsLUB I β → c β ∉ W) :
    C.FutureInextensible W I c := by
  refine ⟨hc, ?_⟩
  rintro ⟨I', c', hcurve, ⟨φ, hφmono, hφmaps, hφoc, hφeq, hφend⟩, ⟨t', ht', hgrow⟩⟩
  obtain ⟨s₀, hs₀⟩ := hc.nonempty
  -- the new value comes after the whole reparametrised curve
  have hafter : ∀ s ∈ I, φ s < t' := by
    intro s hs
    by_contra h
    obtain ⟨w, hw, hwt⟩ := hφend s hs t' ht' (not_lt.1 h)
    exact hgrow w hw (by rw [← hwt, hφeq w hw])
  have hne : (φ '' I).Nonempty := ⟨_, mem_image_of_mem φ hs₀⟩
  have hbdd : BddAbove (φ '' I) := ⟨t', by rintro _ ⟨s, hs, rfl⟩; exact (hafter s hs).le⟩
  set σ := sSup (φ '' I) with hσdef
  have hle : ∀ s ∈ I, φ s ≤ σ := fun s hs => le_csSup hbdd (mem_image_of_mem φ hs)
  have hσt : σ ≤ t' := csSup_le hne (by rintro _ ⟨s, hs, rfl⟩; exact (hafter s hs).le)
  have hσI : σ ∈ I' := hcurve.ordConnected.out (hφmaps hs₀) ht' ⟨hle s₀ hs₀, hσt⟩
  have hcont' : ContinuousWithinAt c' (Icc (φ s₀) σ) σ :=
    CurveOn.continuousOn C.isRelFamily_le (hcurve.curve _ (hφmaps hs₀) _ hσI) _
      ⟨hle _ hs₀, le_rfl⟩
  have hPW : c' σ ∈ W := hcurve.mem hσI
  by_cases hB : BddAbove I
  · -- the curve runs, at its future end `β = sup I`, into `c β ∉ W`; the extension into `c' σ ∈ W`
    have hβ : IsLUB I (sSup I) := isLUB_csSup hc.nonempty hB
    set β := sSup I
    have hlt : ∀ s ∈ I, s < β := fun s hs => by
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hI s hs
      have hmem : s + r / 2 ∈ I := hball (by
        rw [mem_ball, Real.dist_eq, abs_of_pos (by linarith)]; linarith)
      linarith [hβ.1 hmem]
    have hIoo : ∀ s₁ ∈ I, Ioo s₁ β ⊆ I := fun s₁ hs₁ τ hτ => by
      obtain ⟨s, hs, hτs⟩ := (lt_isLUB_iff hβ).1 hτ.2
      exact hc.ordConnected.out hs₁ hs ⟨hτ.1.le, hτs.le⟩
    have hs₀β : s₀ < β := hlt s₀ hs₀
    have hφlim : Tendsto φ (𝓝[<] β) (𝓝[Icc (φ s₀) σ] σ) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · refine tendsto_order.2 ⟨fun a ha' => ?_, fun a ha' => ?_⟩
        · obtain ⟨_, ⟨s₁, hs₁, rfl⟩, has₁⟩ := exists_lt_of_lt_csSup hne ha'
          filter_upwards [Ioo_mem_nhdsLT (hlt s₁ hs₁)] with s hs
          exact has₁.trans (hφmono hs₁ (hIoo s₁ hs₁ hs) hs.1)
        · filter_upwards [Ioo_mem_nhdsLT hs₀β] with s hs
          exact (hle s (hIoo s₀ hs₀ hs)).trans_lt ha'
      · filter_upwards [Ioo_mem_nhdsLT hs₀β] with s hs
        exact ⟨(hφmono hs₀ (hIoo s₀ hs₀ hs) hs.1).le, hle s (hIoo s₀ hs₀ hs)⟩
    have hlim1 : Tendsto c (𝓝[<] β) (𝓝 (c' σ)) := by
      refine (hcont'.tendsto.comp hφlim).congr' ?_
      filter_upwards [Ioo_mem_nhdsLT hs₀β] with s hs using hφeq s (hIoo s₀ hs₀ hs)
    have hlim2 : Tendsto c (𝓝[<] β) (𝓝 (c β)) :=
      hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have heq := tendsto_nhds_unique hlim1 hlim2
    exact hend β hβ (heq ▸ hPW)
  · -- the curve is unbounded in time at its future end: `T ∘ c' ∘ φ` cannot converge
    have hTc' : ContinuousWithinAt (T ∘ c') (Icc (φ s₀) σ) σ :=
      hT.continuousAt.comp_continuousWithinAt hcont'
    obtain ⟨η, hη, hball⟩ := Metric.continuousWithinAt_iff.1 hTc' 1 one_pos
    obtain ⟨_, ⟨s₁, hs₁, rfl⟩, hs₁σ⟩ := exists_lt_of_lt_csSup hne (show σ - η < σ by linarith)
    obtain ⟨s, hs, hsbig⟩ := not_bddAbove_iff.1 hB (max (max s₀ s₁) (T (c' σ) + 1))
    have h0 : s₀ < s := lt_of_le_of_lt (le_max_left _ _ |>.trans (le_max_left _ _)) hsbig
    have h1 : s₁ < s := lt_of_le_of_lt (le_max_right _ _ |>.trans (le_max_left _ _)) hsbig
    have h2 : T (c' σ) + 1 < s := lt_of_le_of_lt (le_max_right _ _) hsbig
    have hφ0 := hφmono hs₀ hs h0
    have hφ1 := hφmono hs₁ hs h1
    have hmem : φ s ∈ Icc (φ s₀) σ := ⟨hφ0.le, hle s hs⟩
    have hd : dist (φ s) σ < η := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hle s hs]
    have := hball hmem hd
    simp only [Function.comp, hφeq s hs, hTc s hs] at this
    rw [Real.dist_eq, abs_lt] at this
    linarith [this.2]

/-- **The past end**, by time reversal (`dual_futureInextensible_iff`). -/
theorem pastInextensible_of_isGLB_notMem [T2Space M] {W : Opens M} {I : Set ℝ} {c : ℝ → M}
    (hc : C.CausalCurveIn W I c) (hI : IsOpen I) (hcont : Continuous c) {T : M → ℝ}
    (hT : Continuous T) (hTc : ∀ τ ∈ I, T (c τ) = τ) (hend : ∀ β, IsGLB I β → c β ∉ W) :
    C.PastInextensible W I c := by
  have h := futureInextensible_of_isLUB_notMem (C := C.dual) (I := -I) (c := fun t => c (-t))
    hc.reverse hI.neg (hcont.comp continuous_neg) (T := fun x => -T x) hT.neg
    (fun τ hτ => by simp only [hTc (-τ) hτ, neg_neg])
    (fun β hβ => hend (-β) (isLUB_neg.1 hβ))
  exact dual_futureInextensible_iff.1 h

/-- **The maximal piece in `W` of a time-parametrised curve is inextensible in `W`.** `ℓ` is
continuous on `ℝ`, a continuous `T` reads its parameter (`T (ℓ τ) = τ`), and every segment of `ℓ`
inside `W` is a causal curve of `W`. Then over the connected component through `t` of `ℓ⁻¹(W)`
(an open interval) `ℓ` is an inextensible causal curve of `W`: each end is at infinite time, or
at a parameter where `ℓ` leaves `W` (maximality of the component). -/
theorem inextensible_connectedComponentIn [T2Space M] {W : Opens M} {ℓ : ℝ → M}
    (hℓ : Continuous ℓ) {T : M → ℝ} (hT : Continuous T) (hTℓ : ∀ τ, T (ℓ τ) = τ)
    (hcurve : ∀ a b, a ≤ b → (∀ τ ∈ Icc a b, ℓ τ ∈ W) → C.CausalCurveOn W ℓ a b) {t : ℝ}
    (ht : ℓ t ∈ W) : C.Inextensible W (connectedComponentIn (ℓ ⁻¹' W) t) ℓ := by
  set O : Set ℝ := ℓ ⁻¹' W with hOdef
  have hO : IsOpen O := W.isOpen.preimage hℓ
  set I := connectedComponentIn O t with hIdef
  have htI : t ∈ I := mem_connectedComponentIn ht
  have hIO : I ⊆ O := connectedComponentIn_subset O t
  have hIo : IsOpen I := hO.connectedComponentIn
  have hIc : I.OrdConnected := isPreconnected_connectedComponentIn.ordConnected
  have hc : C.CausalCurveIn W I ℓ := by
    refine ⟨⟨t, htI⟩, hIc, fun a ha b hb => ?_⟩
    rcases le_or_gt a b with hab | hab
    · exact hcurve a b hab fun τ hτ => hIO (hIc.out ha hb hτ)
    · exact CurveOn.of_lt hab
  -- a maximal piece of the line ends outside `W`, or not at all
  have hmax : ∀ β r, 0 < r → ball β r ⊆ O → (I ∩ ball β r).Nonempty → ball β r ⊆ I := by
    intro β r _ hsub ⟨s, hsI, hsb⟩
    have hJ : IsPreconnected (I ∪ ball β r) := IsPreconnected.union s hsI hsb
      isPreconnected_connectedComponentIn (by rw [Real.ball_eq_Ioo]; exact isPreconnected_Ioo)
    have := hJ.subset_connectedComponentIn (Or.inl htI) (union_subset hIO hsub)
    exact fun x hx => this (Or.inr hx)
  have hlub : ∀ β, IsLUB I β → ℓ β ∉ W := by
    intro β hβ hβW
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hO β hβW
    obtain ⟨s, hs, hsβ⟩ := (lt_isLUB_iff hβ).1 (show β - r < β by linarith)
    have hsb : s ∈ ball β r := by
      rw [mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hβ.1 hs]
    have hsub := hmax β r hr hball ⟨s, hs, hsb⟩
    have hmem : β + r / 2 ∈ I := hsub (by
      rw [mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
    linarith [hβ.1 hmem]
  have hglb : ∀ β, IsGLB I β → ℓ β ∉ W := by
    intro β hβ hβW
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hO β hβW
    obtain ⟨s, hs, hsβ⟩ := (isGLB_lt_iff hβ).1 (show β < β + r by linarith)
    have hsb : s ∈ ball β r := by
      rw [mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hβ.1 hs]
    have hsub := hmax β r hr hball ⟨s, hs, hsb⟩
    have hmem : β - r / 2 ∈ I := hsub (by
      rw [mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
    linarith [hβ.1 hmem]
  exact inextensible_iff.2
    ⟨pastInextensible_of_isGLB_notMem hc hIo hℓ hT (fun τ _ => hTℓ τ) hglb,
      futureInextensible_of_isLUB_notMem hc hIo hℓ hT (fun τ _ => hTℓ τ) hlub⟩

/-- **A Cauchy surface of `W` meets the maximal piece in `W` of every such curve.** -/
theorem IsCauchySurfaceOn.exists_mem_connectedComponentIn [T2Space M] {W : Opens M} {S : Set M}
    (hS : C.IsCauchySurfaceOn W S) {ℓ : ℝ → M}
    (hℓ : Continuous ℓ) {T : M → ℝ} (hT : Continuous T) (hTℓ : ∀ τ, T (ℓ τ) = τ)
    (hcurve : ∀ a b, a ≤ b → (∀ τ ∈ Icc a b, ℓ τ ∈ W) → C.CausalCurveOn W ℓ a b) {t : ℝ}
    (ht : ℓ t ∈ W) : ∃ s ∈ connectedComponentIn (ℓ ⁻¹' W) t, ℓ s ∈ S := by
  obtain ⟨_, ⟨⟨s, hs, rfl⟩, hxS⟩, -⟩ :=
    hS _ _ (inextensible_connectedComponentIn hℓ hT hTℓ hcurve ht)
  exact ⟨s, hs, hxS⟩

end Causality

end Causal
