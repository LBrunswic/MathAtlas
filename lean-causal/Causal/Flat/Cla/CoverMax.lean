import Causal.Flat.Nonloxodromic
import Causal.Flat.Loxodromic
import Causal.Flat.Cla.CompactComplete

/-!
# `Causal.Flat.Cla.CoverMax` — the developing map of a maximal GH flat spacetime fills `int D(Σ)`, and finite covers of maximal Cauchy-compact GH flat spacetimes are maximal

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257). Line
numbers are those of the labelled `papers/barbot/legacy/labeled/GHFspace.tex`. **No label is
marked**: `cover_maximal_of_isFiniteCover` is finding 2 of `Flat/Cla/CoverMGH.lean` (a statement
the paper uses silently in the proof of Theorem B, `bthm:cauclo`, `GHFspace.tex:353`, at
l.3573–3581), and `cover_range_eq_of_mgh` is the first claim of Rem `defdep` (l.2516–2525, a
remark, prose) in the DEC-35 reading.

* `cover_maximal_of_isFiniteCover` — **no `sorry`**: a finite cover `M'` (Cauchy-compact) of a
  maximal Cauchy-compact GH flat spacetime `M` is maximal: every flat Cauchy embedding
  `g : M' → N`, `N` in any universe, is onto. It closes `Cla.maximal_of_isFiniteCover`
  (CoverMGH, finding 2), Theorem B's last plan-lemma `sorry`.
* `cover_range_eq_of_mgh` — **no `sorry`**: for `M` maximal GH with a developing pair `(𝒟, ρ)` and
  (CC′) for a Cauchy surface `S` (`DevelopsCC`), `𝒟(M̃) = int D(Σ)`, `Σ = 𝒟(S̃)`, `D` the domain
  of dependence in `𝐌ⁿ`. Cauchy-compactness is not used.
* `cover_surjective_of_range_eq` — the lifting argument (l.3586–3611's, for the target):
  `𝒟(M̃) = int D(Σ)` makes every flat Cauchy embedding of a Cauchy-compact finite cover onto.

> Actually, when $M$ is maximal globally hyperbolic, $\mathcal{C}(\widetilde{S})$, the image of
> $\mathcal D$, is the so-called Cauchy domain, or domain of dependence of the spacelike
> hypersurface $S$ (l.2517–2521)

> Now, a globally hyperbolic manifold $M$ is said maximal if any Cauchy embedding of $M$ into some
> globally hyperbolic spacetime $N$ is necessarly surjective. (l.525–527)

> (ii) Any maximal Cauchy-compact GH spacetime is not only embedded in a finite quotient of a
> translation spacetime, a Misner spacetime or the twisted product of a standart spacetime by a
> flat torus, it is actually \emph{isometric} to one of them. (l.3573–3576)

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; `Minkowski d` has `d` spatial
dimensions: Barbot's `n` is `d + 1`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| Rem `defdep`: `M` maximal GH (l.2517) | ✓ carried: `MGH M` (targets in `M`'s universe; the extension `Γ\W` is built in `Type` and lifted by `ULift`, `coverULiftSpacetime`) |
| Rem `defdep`: `S` a spacelike hypersurface, `𝒟(M̃)` "the Cauchy domain" | ⚠ reading (DEC-35): `S` a Cauchy surface with (CC′) (`DevelopsCC`); "Cauchy domain" is `int D(Σ)`, `D` by inextensible causal curves of `𝐌ⁿ` (Barbot: every lightlike geodesic meets `S`; for an entire graph `D(Σ)` is the set of points every causal line through which meets `Σ`, `mem_dependenceDomain_of_meets`) |
| finding 2: `M` maximal Cauchy-compact GH, `M'` a finite cover | ✓ carried: `GH M`, `CauchyCompact M`, `MGH M`, `IsFiniteCover d p`; `CauchyCompact M'` is asked (CoverMGH proves it, `cauchyCompact_of_isFiniteCover`) |
| the target `N` of the Cauchy embedding | ⚠ weakened: any universe (`FlatSpacetime.{w}`), where `MGH M'` asks `Type` |
| universes | `M` in any universe `u`, `M'` in any `v`, `N` in any `w` |

## SCOPE (disclosed)

* **Sorries: none.** `#print axioms Causal.Flat.Cla.cover_maximal_of_isFiniteCover`:
  `[propext, Classical.choice, Quot.sound]`. Inputs: L9 (`isCauchyComplete_of_isCompact_cauchy`,
  CompactComplete, sorry-free), the bridge (`exists_developsCC_of_isCauchyComplete`), Develop's
  Prop 8.12 (`injective_of_developsCC`), Examples' `gh_toFlatSpacetime`, Quotient's descent of
  Cauchy surfaces, Port's rigidity (`developing_unique_of_preconnected`).
* **Route** (not the Galois core of the obstruction CoverMGH recorded): (1) for `M` maximal,
  `W = int D(Σ)` is connected and causally convex, `Γ = ρ(π₁M)` acts on it freely, acausally
  (`W ⊆ U(Γ)`: `γx − x` is spacelike) and properly (through the compact sets `J^±(z) ∩ Σ` and the
  properness of `Γ` on `Σ`), so `Γ\W` is a GH flat spacetime into which `M` Cauchy-embeds; `MGH M`
  gives `𝒟(M̃) = W`. (2) For `g : M' → N`, `N` is Cauchy-compact hence Cauchy-complete; the lift
  `G : M̃ → Ñ` of `g ∘ q` (`q : M̃ → M'` the lift of `M̃ → M` through `p`) satisfies
  `𝒟_N ∘ G = h 𝒟`; the developed lift of `g(p⁻¹S)` is a (CC′) Cauchy surface of `𝒟_N(Ñ)`
  containing the entire graph `hΣ`, hence equal to it, so `𝒟_N(Ñ) ⊆ int D(hΣ) = 𝒟_N(G(M̃))`.
* **Not proved**: the second claim of Rem `defdep` / Rem `dependance` (l.3552–3555),
  `Ω(S̃) = int D(Σ)`; only `int D(Σ) = 𝒟(M̃) ⊆ Ω(S̃)` (`bprop_danom`) follows.
* **Local copies** (this module is imported by CoverMGH, which Classification imports, so it
  cannot import Classification): `cover_isLocalIsometry_of_comp` (=
  `IsLocalIsometry.of_comp_left_of_continuous`), `cover_isLocalIsometry_of_comp_right` (=
  `IsLocalIsometry.of_comp_right`), `cover_gh_of_isIsometricEmbedding_of_surjective` (=
  `globallyHyperbolic_of_isIsometricEmbedding_of_surjective`), `cover_exists_deck_apply_eq` (=
  `UniversalCover.exists_deck_apply_eq`); graduation may deduplicate.
* **The universe transport** `coverULiftSpacetime` (`ULift` with the atlas precomposed by
  `ULift.down`, `coverULift_hasGroupoid`) is the generic one Classification's universes row
  mentions; it is used once, to apply `MGH M` to `Γ\W`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
WP-34e, closer of `Cla.maximal_of_isFiniteCover`.
-/

namespace Causal.Flat.Cla

open Set Function Filter Topology TopologicalSpace
open scoped Pointwise

universe u v w

variable {d : ℕ}

/-! ## §1 The domain of dependence of an entire acausal graph, in `𝐌ⁿ` -/

section Minkowski

/-- **An isometry carries `D(Σ)` into `D(γΣ)`**, for `Σ` satisfying (CC′): `D` of an entire
acausal graph is the set of points every future causal line through which meets it
(`meets_of_mem_dependenceDomain`, `mem_dependenceDomain_of_meets`), and `γ` maps causal lines
to causal lines (`isom_smul_add_smul`, the linear part preserving the future cone). -/
theorem cover_smul_mem_dependenceDomain {St : Set (Minkowski d)} (hcc : CCPrime St) (γ : isom d)
    {z : Minkowski d} (hz : z ∈ dependenceDomain (minkowski d) ⊤ St) : γ • z ∈ dependenceDomain (minkowski d) ⊤ (γ • St) := by
  obtain ⟨f, -, rfl⟩ := isEntireAcausalGraph_iff.1 hcc.entire
  obtain ⟨f', hf', hSt⟩ := isEntireAcausalGraph_iff.1 (ccPrime_smul γ hcc).entire
  rw [hSt]
  refine mem_dependenceDomain_of_meets hf' fun v hv hv0 => ?_
  set w := (linOf γ).symm v with hw
  have hwv : linOf γ w = v := linOf_symm_apply γ v
  have hwc : IsFutureCausal w := by
    rw [← lorentz.isFutureCausal_apply_iff (linOf_mem γ), hwv]; exact hv
  have hw0 : w ≠ 0 := fun h0 => hv0 (by rw [← hwv, h0, map_zero])
  obtain ⟨s, hs⟩ := meets_of_mem_dependenceDomain hz hwc hw0
  refine ⟨s, ?_⟩
  rw [← hSt, ← hwv, ← isom_smul_add_smul]
  exact smul_mem_smul_set hs

/-- **An isometry carries `int D(Σ)` into `int D(γΣ)`** (`cover_smul_mem_dependenceDomain` and
the homeomorphism `γ`). -/
theorem cover_smul_mem_interior_dependenceDomain {St : Set (Minkowski d)} (hcc : CCPrime St)
    (γ : isom d) {z : Minkowski d} (hz : z ∈ interior (dependenceDomain (minkowski d) ⊤ St)) :
    γ • z ∈ interior (dependenceDomain (minkowski d) ⊤ (γ • St)) := by
  have hopen : IsOpen ((fun p => γ • p) '' interior (dependenceDomain (minkowski d) ⊤ St)) :=
    (isom.toHomeomorph γ).isOpenMap _ isOpen_interior
  refine interior_maximal ?_ hopen ⟨z, hz, rfl⟩
  rintro _ ⟨y, hy, rfl⟩
  exact cover_smul_mem_dependenceDomain hcc γ (interior_subset hy)

/-- **Two entire acausal graphs, one inside the other, are equal**: the vertical line through a
point `b` of the larger meets the smaller at `a`, and `a`, `b` are causally related points of the
acausal larger one. -/
theorem cover_eq_of_subset_of_isEntireAcausalGraph {A B : Set (Minkowski d)}
    (hA : IsEntireAcausalGraph A) (hB : IsEntireAcausalGraph B) (hAB : A ⊆ B) : A = B := by
  refine Subset.antisymm hAB fun b hb => ?_
  obtain ⟨s, hs⟩ := hA.meets b ((1, 0) : Minkowski d) isFutureTimelike_vertical
  have hsB := hAB hs
  rcases le_total 0 s with h0 | h0
  · have hle : (minkowski d).le ⊤ b (b + s • ((1, 0) : Minkowski d)) := by
      rw [minkowski_le_top_iff]; simp [h0]
    rw [hB.acausal _ hb _ hsB hle]; exact hs
  · have hle : (minkowski d).le ⊤ (b + s • ((1, 0) : Minkowski d)) b := by
      rw [minkowski_le_top_iff]; simp [h0]
    rw [← hB.acausal _ hsB _ hb hle]; exact hs

variable {f : EuclideanSpace ℝ (Fin d) → ℝ}

/-- The vertical projection of a point to the graph of `f`. -/
def coverVert (f : EuclideanSpace ℝ (Fin d) → ℝ) (z : Minkowski d) : Minkowski d := (f z.2, z.2)

theorem coverVert_mem_graph (z : Minkowski d) : coverVert f z ∈ graph f := rfl

theorem coverVert_le (z : Minkowski d) (hz : 0 ≤ timeSub f z) :
    (minkowski d).le ⊤ (coverVert f z) z := by
  rw [minkowski_le_top_iff]; simpa [coverVert, timeSub] using hz

theorem le_coverVert (z : Minkowski d) (hz : timeSub f z ≤ 0) :
    (minkowski d).le ⊤ z (coverVert f z) := by
  rw [minkowski_le_top_iff]; simpa [coverVert, timeSub] using hz

/-- **Every causal relation `x ≤ y` of `𝐌ⁿ` passes through a point of the graph comparable to
both ends**: the vertical projection of `x` (if `x` is above the graph), of `y` (if `y` is below),
or a point of the segment `[x, y]` on the graph (intermediate value theorem). -/
theorem cover_exists_graph_comparable (hf : IsStrictContraction f) {x y : Minkowski d}
    (hxy : (minkowski d).le ⊤ x y) :
    ∃ σ ∈ graph f, ((minkowski d).le ⊤ σ x ∨ (minkowski d).le ⊤ x σ) ∧
      ((minkowski d).le ⊤ σ y ∨ (minkowski d).le ⊤ y σ) := by
  have hlip := hf.lipschitzWith
  by_cases hx : 0 ≤ timeSub f x
  · exact ⟨_, coverVert_mem_graph x, Or.inl (coverVert_le x hx),
      Or.inl ((minkowski d).le_trans (coverVert_le x hx) hxy)⟩
  by_cases hy : timeSub f y ≤ 0
  · exact ⟨_, coverVert_mem_graph y, Or.inr ((minkowski d).le_trans hxy (le_coverVert y hy)),
      Or.inr (le_coverVert y hy)⟩
  push Not at hx hy
  obtain ⟨σ, hσ, hσ0⟩ := (convex_segment x y).isPreconnected.intermediate_value
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
    (continuous_timeSub hlip).continuousOn ⟨hx.le, hy.le⟩
  obtain ⟨h1, h2⟩ := le_top_of_mem_segment hxy hσ
  exact ⟨σ, mem_graph_iff_timeSub.2 hσ0, Or.inr h1, Or.inl h2⟩

end Minkowski

/-! ## §2 The holonomy group on `int D(Σ)` -/

section Action

variable {f : EuclideanSpace ℝ (Fin d) → ℝ} {Γ : Subgroup (isom d)}

/-- **Finitely many `γ ∈ Γ` relate two points of `D(Σ)`**: `x ≤ γ y` passes through a point
`σ ∈ Σ` comparable to `x` and to `γ y` (`cover_exists_graph_comparable`), so `σ` and `γ⁻¹σ` lie
in the compact `K = (J⁻(x) ∪ J⁺(x) ∪ J⁻(y) ∪ J⁺(y)) ∩ Σ` (`isCompact_Jminus_inter_graph`), and
`Γ` acts properly on `Σ` (`CCAction.proper`). -/
theorem cover_finite_le_smul (hcc : CCAction Γ (graph f)) {x y : Minkowski d}
    (hx : x ∈ dependenceDomain (minkowski d) ⊤ (graph f))
    (hy : y ∈ dependenceDomain (minkowski d) ⊤ (graph f)) :
    {γ : isom d | γ ∈ Γ ∧ (minkowski d).le ⊤ x (γ • y)}.Finite := by
  obtain ⟨f', hf', hff'⟩ := isEntireAcausalGraph_iff.1 hcc.cc.entire
  have hf : IsStrictContraction f := by
    have : f = f' := funext fun z => by
      have h1 : ((f z, z) : Minkowski d) ∈ graph f' := hff' ▸ (rfl : ((f z, z) : Minkowski d) ∈ graph f)
      exact h1
    rw [this]; exact hf'
  set K : Minkowski d → Set (Minkowski d) := fun z =>
    ((minkowski d).Jminus ⊤ {z} ∩ graph f) ∪ ((minkowski d).Jplus ⊤ {z} ∩ graph f) with hKdef
  have hKc : ∀ z ∈ dependenceDomain (minkowski d) ⊤ (graph f), IsCompact (K z) := fun z hz =>
    (isCompact_Jminus_inter_graph hf fun v hv hv0 => meets_of_mem_dependenceDomain hz hv hv0).union
      (isCompact_Jplus_inter_graph hf fun v hv hv0 => meets_of_mem_dependenceDomain hz hv hv0)
  have hKS : ∀ z, K z ⊆ graph f := fun z w hw => by
    rcases hw with hw | hw <;> exact hw.2
  have hmemK : ∀ z σ, σ ∈ graph f → ((minkowski d).le ⊤ σ z ∨ (minkowski d).le ⊤ z σ) →
      σ ∈ K z := by
    rintro z σ hσ (h | h)
    · exact Or.inl ⟨Precausality.mem_Jminus_singleton.2 h, hσ⟩
    · exact Or.inr ⟨Precausality.mem_Jplus_singleton.2 h, hσ⟩
  refine (hcc.proper (K x ∪ K y) (union_subset (hKS x) (hKS y))
    ((hKc x hx).union (hKc y hy))).subset ?_
  rintro γ ⟨hγ, hle⟩
  refine ⟨hγ, ?_⟩
  obtain ⟨σ, hσ, h1, h2⟩ := cover_exists_graph_comparable hf hle
  have hσ' : γ⁻¹ • σ ∈ graph f := hcc.smul_mem (Γ.inv_mem hγ) hσ
  have h2' : (minkowski d).le ⊤ (γ⁻¹ • σ) y ∨ (minkowski d).le ⊤ y (γ⁻¹ • σ) := by
    rcases h2 with h2 | h2
    · left
      rw [← isom_le_top_iff γ, smul_inv_smul]; exact h2
    · right
      rw [← isom_le_top_iff γ, smul_inv_smul]; exact h2
  refine ⟨σ, ⟨γ⁻¹ • σ, Or.inr (hmemK y _ hσ' h2'), smul_inv_smul γ σ⟩, Or.inl (hmemK x σ hσ h1)⟩

/-- **A causal box around a point of an open set**: near `z ∈ W` (open), the points `a = z − ε e₀`
and `b = z + ε e₀` lie in `W` and every point of a neighbourhood of `z` lies between them. -/
theorem cover_exists_box {W : Set (Minkowski d)} (hW : IsOpen W) {z : Minkowski d} (hz : z ∈ W) :
    ∃ a b : Minkowski d, a ∈ W ∧ b ∈ W ∧
      ∀ᶠ q in 𝓝 z, (minkowski d).le ⊤ a q ∧ (minkowski d).le ⊤ q b := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hW z hz
  set ε := r / 2 with hε
  have hε0 : 0 < ε := by positivity
  refine ⟨(z.1 - ε, z.2), (z.1 + ε, z.2), hball ?_, hball ?_, ?_⟩
  · rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, dist_self,
      show z.1 - ε - z.1 = -ε by ring, abs_neg, abs_of_pos hε0, max_eq_left hε0.le]; linarith
  · rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, dist_self,
      show z.1 + ε - z.1 = ε by ring, abs_of_pos hε0, max_eq_left hε0.le]; linarith
  · filter_upwards [Metric.ball_mem_nhds z (half_pos hε0)] with q hq
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, dist_eq_norm] at hq
    obtain ⟨h1, h2⟩ := hq
    rw [abs_lt] at h1
    refine ⟨?_, ?_⟩
    · rw [minkowski_le_top_iff]; simp only; linarith
    · rw [minkowski_le_top_iff]; simp only; rw [norm_sub_rev]; linarith

/-- **`Γ` acts properly discontinuously on `int D(Σ)`**: cover a compact `K` by finitely many
boxes `[aᵢ, bᵢ]` (`cover_exists_box`); `γ K ∩ K ≠ ∅` forces some `aⱼ ≤ γ bᵢ`, and each set of such
`γ` is finite (`cover_finite_le_smul`). -/
theorem cover_finite_smul_inter (hcc : CCAction Γ (graph f)) {K : Set (Minkowski d)}
    (hKW : K ⊆ interior (dependenceDomain (minkowski d) ⊤ (graph f))) (hK : IsCompact K) :
    {γ : isom d | γ ∈ Γ ∧ (γ • K ∩ K).Nonempty}.Finite := by
  set W := interior (dependenceDomain (minkowski d) ⊤ (graph f))
  have hbox : ∀ z ∈ W, ∃ a b : Minkowski d, a ∈ W ∧ b ∈ W ∧
      ∀ᶠ q in 𝓝 z, (minkowski d).le ⊤ a q ∧ (minkowski d).le ⊤ q b :=
    fun z hz => cover_exists_box isOpen_interior hz
  choose! a b ha hb hev using hbox
  obtain ⟨t, htK, hcover⟩ := hK.elim_nhds_subcover
    (fun z => {q | (minkowski d).le ⊤ (a z) q ∧ (minkowski d).le ⊤ q (b z)})
    (fun z hz => hev z (hKW hz))
  refine (t.finite_toSet.biUnion fun i hi => t.finite_toSet.biUnion fun j hj =>
    cover_finite_le_smul (x := a j) (y := b i) hcc (interior_subset (ha j (hKW (htK j hj))))
      (interior_subset (hb i (hKW (htK i hi))))).subset ?_
  rintro γ ⟨hγ, _, ⟨k, hk, rfl⟩, hγk⟩
  obtain ⟨i, hi, hki⟩ := mem_iUnion₂.1 (hcover hk)
  obtain ⟨j, hj, hγkj⟩ := mem_iUnion₂.1 (hcover hγk)
  refine mem_iUnion₂.2 ⟨i, hi, mem_iUnion₂.2 ⟨j, hj, hγ, ?_⟩⟩
  exact (minkowski d).le_trans hγkj.1 ((isom_le_top_iff γ).2 hki.2)

/-- **`int D(Σ)` is causally convex in `𝐌ⁿ`** (`mem_interior_dependenceDomain_of_le_of_nonneg`,
`…_nonpos`, according to the side of `Σ`). -/
theorem cover_causallyConvexIn (hf : IsStrictContraction f) :
    (minkowski d).CausallyConvexIn (interior (dependenceDomain (minkowski d) ⊤ (graph f))) ⊤ := by
  refine ⟨fun _ _ => trivial, fun p hp q hq z hz => ?_⟩
  obtain ⟨h1, h2⟩ := Causality.mem_diamond.1 hz
  rcases le_total 0 (timeSub f z) with h0 | h0
  · exact mem_interior_dependenceDomain_of_le_of_nonneg hf hq h2 h0
  · exact mem_interior_dependenceDomain_of_le_of_nonpos hf hp h1 h0

/-- **`int D(Σ)` is connected**: every point is joined to `Σ` by its vertical segment, which lies
in `int D(Σ)` (`cover_causallyConvexIn`), and `Σ` is connected. -/
theorem cover_isConnected (hf : IsStrictContraction f) :
    IsConnected (interior (dependenceDomain (minkowski d) ⊤ (graph f))) := by
  set W := interior (dependenceDomain (minkowski d) ⊤ (graph f))
  have hSW : graph f ⊆ W := graph_subset_interior_dependenceDomain hf
  have hconv := cover_causallyConvexIn hf
  have hgc : IsPreconnected (graph f) := isPreconnected_graph f hf.lipschitzWith.continuous
  refine ⟨⟨_, hSW (coverVert_mem_graph (f := f) 0)⟩, isPreconnected_of_forall (coverVert f 0)
    fun y hy => ⟨graph f ∪ segment ℝ y (coverVert f y), union_subset hSW ?_,
      Or.inl (coverVert_mem_graph 0), Or.inr (left_mem_segment ℝ _ _),
      hgc.union (coverVert f y) (coverVert_mem_graph y) (right_mem_segment ℝ _ _)
        (convex_segment _ _).isPreconnected⟩⟩
  intro q hq
  have hvW := hSW (coverVert_mem_graph (f := f) y)
  rcases le_total 0 (timeSub f y) with h0 | h0
  · have hle := coverVert_le (f := f) y h0
    rw [segment_symm] at hq
    obtain ⟨h1, h2⟩ := le_top_of_mem_segment hle hq
    exact hconv.2 _ hvW _ hy (Causality.mem_diamond.2 ⟨h1, h2⟩)
  · have hle := le_coverVert (f := f) y h0
    obtain ⟨h1, h2⟩ := le_top_of_mem_segment hle hq
    exact hconv.2 _ hy _ hvW (Causality.mem_diamond.2 ⟨h1, h2⟩)

/-- **`Γ` acts on `D(Σ)` with spacelike displacements**: for `γ ∈ Γ`, `γ ≠ 1`, and `x ∈ D(Σ)`,
`γ x − x` is spacelike (`D(Σ) ⊆ U(Γ) ⊆ Ω_γ`, `dependenceDomain_subset_UGamma`,
`Ug_subset_achronalDomain`): `γ x ≠ x` and `x ≰ γ x`. -/
theorem cover_minkQ_pos (hcc : CCAction Γ (graph f)) {γ : isom d} (hγ : γ ∈ Γ) (h1 : γ ≠ 1)
    {x : Minkowski d} (hx : x ∈ dependenceDomain (minkowski d) ⊤ (graph f)) :
    0 < minkQ (γ • x - x) := by
  have := Ug_subset_achronalDomain γ (hcc.dependenceDomain_subset_UGamma hx γ hγ h1) 1 one_ne_zero
  simpa using this

theorem cover_not_le_smul (hcc : CCAction Γ (graph f)) {γ : isom d} (hγ : γ ∈ Γ) (h1 : γ ≠ 1)
    {x : Minkowski d} (hx : x ∈ dependenceDomain (minkowski d) ⊤ (graph f)) :
    ¬ (minkowski d).le ⊤ x (γ • x) := fun h =>
  absurd (cover_minkQ_pos hcc hγ h1 hx) (not_lt.2 (le_top_iff_minkQ.1 h).2)

theorem cover_smul_ne (hcc : CCAction Γ (graph f)) {γ : isom d} (hγ : γ ∈ Γ) (h1 : γ ≠ 1)
    {x : Minkowski d} (hx : x ∈ dependenceDomain (minkowski d) ⊤ (graph f)) : γ • x ≠ x :=
  fun h => by have := cover_minkQ_pos hcc hγ h1 hx; rw [h, sub_self, minkQ_zero] at this
              exact lt_irrefl _ this

end Action

/-! ## §3 Local isometries, lifts, and the universe transport `ULift` -/

section Generic

variable {X M N : Type*} [TopologicalSpace X] [ChartedSpace (Minkowski d) X]
  [TopologicalSpace M] [ChartedSpace (Minkowski d) M]
  [TopologicalSpace N] [ChartedSpace (Minkowski d) N]

/-- **Cancelling a local isometry on the left, for a continuous map** (a local copy of
Classification's `IsLocalIsometry.of_comp_left_of_continuous`, which this module cannot import). -/
theorem cover_isLocalIsometry_of_comp {f : X → M} {h : M → N} (hh : IsLocalIsometry d h)
    (hfc : Continuous f) (hhf : IsLocalIsometry d (h ∘ f)) : IsLocalIsometry d f := by
  obtain ⟨-, hhf'⟩ := isLocalIsometry_iff_eventually.1 hhf
  obtain ⟨-, hh'⟩ := isLocalIsometry_iff_eventually.1 hh
  refine isLocalIsometry_iff_eventually.2 ⟨hfc, fun x => ?_⟩
  obtain ⟨g₁, hg₁⟩ := hhf' x
  obtain ⟨g₂, hg₂⟩ := hh' (f x)
  refine ⟨g₂⁻¹ * g₁, ?_⟩
  filter_upwards [hg₁, hfc.continuousAt.eventually hg₂] with y h1 h2
  simp only [comp_apply] at h1
  rw [mul_smul, ← h1, h2, inv_smul_smul]

/-- **Descending a local isometry along a surjective local isometry** (a local copy of
Classification's `IsLocalIsometry.of_comp_right`). -/
theorem cover_isLocalIsometry_of_comp_right {q : X → M} {f : M → N} (hq : IsLocalIsometry d q)
    (hqs : Surjective q) (hfq : IsLocalIsometry d (f ∘ q)) : IsLocalIsometry d f := by
  have hfc : Continuous f :=
    (hq.isOpenMap.isQuotientMap hq.continuous hqs).continuous_iff.2 hfq.1
  obtain ⟨-, hfq'⟩ := isLocalIsometry_iff_eventually.1 hfq
  obtain ⟨-, hq'⟩ := isLocalIsometry_iff_eventually.1 hq
  refine isLocalIsometry_iff_eventually.2 ⟨hfc, fun x => ?_⟩
  obtain ⟨z, rfl⟩ := hqs x
  obtain ⟨g₁, hg₁⟩ := hfq' z
  obtain ⟨g₂, hg₂⟩ := hq' z
  refine ⟨g₁ * g₂⁻¹, ?_⟩
  have hA : {w | chartAt (Minkowski d) (f (q z)) (f (q w)) =
      (g₁ * g₂⁻¹) • chartAt (Minkowski d) (q z) (q w)} ∈ 𝓝 z := by
    filter_upwards [hg₁, hg₂] with w h1 h2
    simp only [comp_apply] at h1
    rw [h1, h2, mul_smul, inv_smul_smul]
  filter_upwards [hq.isOpenMap.image_mem_nhds hA] with y hy
  obtain ⟨w, hw, rfl⟩ := hy
  exact hw

/-- **A local isometry from a simply connected space lifts through a covering local isometry**,
as a local isometry (mathlib's `IsCoveringMap.existsUnique_continuousMap_lifts`, then
`cover_isLocalIsometry_of_comp`). -/
theorem cover_exists_lift [SimplyConnectedSpace X] [LocPathConnectedSpace X] {p : M → N}
    (hp : IsCoveringMap p) (hpl : IsLocalIsometry d p) {f : X → N} (hf : IsLocalIsometry d f)
    (a₀ : X) (e₀ : M) (he : p e₀ = f a₀) :
    ∃ F : X → M, IsLocalIsometry d F ∧ p ∘ F = f ∧ F a₀ = e₀ := by
  obtain ⟨F, ⟨hF0, hF⟩, -⟩ := hp.existsUnique_continuousMap_lifts ⟨f, hf.continuous⟩ a₀ e₀ he
  exact ⟨F, cover_isLocalIsometry_of_comp hpl F.continuous (by rw [hF]; exact hf), hF, hF0⟩

end Generic

/-- **GH transports along a surjective isometric embedding** (a local copy of Classification's
`globallyHyperbolic_of_isIsometricEmbedding_of_surjective`). -/
theorem cover_gh_of_isIsometricEmbedding_of_surjective {M N : Type*} [TopologicalSpace M]
    [ChartedSpace (Minkowski d) M] [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))]
    [TopologicalSpace N] [ChartedSpace (Minkowski d) N]
    [HasGroupoid N (gxGroupoid (isom d) (Minkowski d))] {f : M → N}
    (hf : IsIsometricEmbedding d f) (hs : Surjective f)
    (hM : (flatCausality d M).GloballyHyperbolic) : (flatCausality d N).GloballyHyperbolic := by
  have hrel : ∀ x y : M, (flatCausality d M).le ⊤ x y ↔ (flatCausality d N).le ⊤ (f x) (f y) :=
    fun x y => (hf.rel_iff ⊤ ⊤ (by rw [Opens.coe_top, Opens.coe_top, image_univ, hs.range_eq])
      x y).1
  refine ⟨fun x y hxy hyx => ?_, fun p q => ?_⟩
  · obtain ⟨x, rfl⟩ := hs x
    obtain ⟨y, rfl⟩ := hs y
    exact congrArg f (hM.1 ((hrel x y).2 hxy) ((hrel y x).2 hyx))
  · obtain ⟨p, rfl⟩ := hs p
    obtain ⟨q, rfl⟩ := hs q
    have heq : (flatCausality d N).diamond ⊤ (f p) (f q) =
        f '' (flatCausality d M).diamond ⊤ p q := by
      ext z
      obtain ⟨z, rfl⟩ := hs z
      rw [Causality.mem_diamond]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨z, Causality.mem_diamond.2 ⟨(hrel p z).2 h1, (hrel z q).2 h2⟩, rfl⟩
      · rintro ⟨w, hw, hwz⟩
        obtain ⟨h1, h2⟩ := Causality.mem_diamond.1 hw
        rw [← hwz]
        exact ⟨(hrel p w).1 h1, (hrel w q).1 h2⟩
    rw [heq]
    exact (hM.2 p q).image hf.1.continuous

/-- **A flat Cauchy embedding followed by an isometric bijection is a flat Cauchy embedding**:
GH transports (`cover_gh_of_isIsometricEmbedding_of_surjective`) and so do Cauchy surfaces
(`IsEMorphismOn.isCauchySurfaceOn_image_iff` on `⊤`). -/
theorem cover_isFlatCauchyEmbedding_comp {M N N' : Type*} [TopologicalSpace M]
    [ChartedSpace (Minkowski d) M] [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))]
    [TopologicalSpace N] [ChartedSpace (Minkowski d) N]
    [HasGroupoid N (gxGroupoid (isom d) (Minkowski d))]
    [TopologicalSpace N'] [ChartedSpace (Minkowski d) N']
    [HasGroupoid N' (gxGroupoid (isom d) (Minkowski d))] {f : M → N} {φ : N → N'}
    (hf : IsFlatCauchyEmbedding d f) (hφ : IsIsometricEmbedding d φ) (hs : Surjective φ) :
    IsFlatCauchyEmbedding d (φ ∘ f) := by
  obtain ⟨hfi, hM, hN, S, hS, hfS⟩ := isFlatCauchyEmbedding_iff.1 hf
  have hU : ((⊤ : Opens N') : Set N') = φ '' ((⊤ : Opens N) : Set N) := by
    rw [Opens.coe_top, Opens.coe_top, image_univ, hs.range_eq]
  have himg := (hφ.isEMorphism.isCauchySurfaceOn_image_iff hφ.2.injOn le_rfl hU
    (subset_univ (f '' S))).1 hfS
  refine isFlatCauchyEmbedding_iff.2 ⟨hφ.comp hfi, hM,
    cover_gh_of_isIsometricEmbedding_of_surjective hφ hs hN, S, hS, ?_⟩
  rw [image_comp]
  exact himg

section ULiftSpacetime

variable (X : Type v) [TopologicalSpace X] [ChartedSpace (Minkowski d) X]

/-- **The atlas of `ULift X`**: the charts of `X` precomposed with `ULift.down`. -/
@[reducible] noncomputable def coverULiftChartedSpace :
    ChartedSpace (Minkowski d) (ULift.{u} X) where
  atlas := {e | ∃ c ∈ atlas (Minkowski d) X,
    e = (Homeomorph.ulift.{u, v} (X := X)).toOpenPartialHomeomorph.trans c}
  chartAt x := (Homeomorph.ulift.{u, v} (X := X)).toOpenPartialHomeomorph.trans
    (chartAt (Minkowski d) x.down)
  mem_chart_source x := by
    rw [OpenPartialHomeomorph.trans_source]
    exact ⟨by simp, mem_chart_source (Minkowski d) x.down⟩
  chart_mem_atlas x := ⟨_, chart_mem_atlas _ _, rfl⟩

theorem coverULift_hasGroupoid [HasGroupoid X (gxGroupoid (isom d) (Minkowski d))] :
    letI := coverULiftChartedSpace.{u} (d := d) X
    HasGroupoid (ULift.{u} X) (gxGroupoid (isom d) (Minkowski d)) := by
  letI := coverULiftChartedSpace.{u} (d := d) X
  refine ⟨?_⟩
  rintro _ _ ⟨c, hc, rfl⟩ ⟨c', hc', rfl⟩
  have h := HasGroupoid.compatible (G := gxGroupoid (isom d) (Minkowski d)) hc hc'
  convert h using 1
  apply OpenPartialHomeomorph.ext
  · intro x; rfl
  · intro x; rfl
  · ext x; simp [mfld_simps]

/-- `ULift.up` is a local isometry for the atlas `coverULiftChartedSpace`. -/
theorem coverULift_isLocalIsometry_up :
    letI := coverULiftChartedSpace.{u} (d := d) X
    IsLocalIsometry d (ULift.up.{u, v} : X → ULift.{u} X) := by
  letI := coverULiftChartedSpace.{u} (d := d) X
  refine isLocalIsometry_iff_eventually.2 ⟨continuous_uliftUp, fun x =>
    ⟨1, Eventually.of_forall fun y => ?_⟩⟩
  rw [one_smul]; rfl

end ULiftSpacetime

/-- **A flat spacetime in a larger universe**: `ULift.{u} B` with the transported atlas. -/
noncomputable def coverULiftSpacetime (B : FlatSpacetime.{v} d) : FlatSpacetime.{max v u} d :=
  letI := coverULiftChartedSpace.{u} (d := d) B
  haveI := coverULift_hasGroupoid.{u} (d := d) B
  haveI : T2Space (ULift.{u} B) := Topology.IsEmbedding.uliftDown.t2Space
  haveI : ConnectedSpace (ULift.{u} B) :=
    (Homeomorph.ulift.{u, v} (X := B)).symm.surjective.connectedSpace
      (Homeomorph.ulift.{u, v} (X := B)).symm.continuous
  FlatSpacetime.of (ULift.{u} B)

/-- `ULift.up`, as a map into `coverULiftSpacetime B`. -/
def coverULiftUp (B : FlatSpacetime.{v} d) : B → coverULiftSpacetime.{u, v} B := ULift.up

/-- `ULift.up : B → coverULiftSpacetime B` is a bijective isometric embedding. -/
theorem coverULiftSpacetime_up (B : FlatSpacetime.{v} d) :
    IsIsometricEmbedding d (coverULiftUp.{u, v} B) ∧ Surjective (coverULiftUp.{u, v} B) :=
  ⟨⟨coverULift_isLocalIsometry_up.{u} (d := d) B, fun _ _ h => ULift.up_injective h⟩,
    fun y => ⟨y.down, rfl⟩⟩

/-! ## §4 Maximality of `M` forces `𝒟(M̃) = int D(Σ)` -/

/-- **The deck group acts transitively on the fibres** of the universal cover (a local copy of
Classification's `UniversalCover.exists_deck_apply_eq`). -/
theorem cover_exists_deck_apply_eq {Y : Type*} [TopologicalSpace Y] {y₀ : Y}
    (c c' : UniversalCover Y y₀) (h : UniversalCover.proj Y y₀ c = UniversalCover.proj Y y₀ c') :
    ∃ γ : Deck (UniversalCover.proj Y y₀), γ.1 c = c' := by
  obtain ⟨a, ca⟩ := c
  obtain ⟨b, cb⟩ := c'
  change a = b at h
  subst h
  refine ⟨⟨UniversalCover.leftMulHomeomorph (cb.trans ca.symm), rfl⟩, ?_⟩
  change (⟨a, (cb.trans ca.symm).trans ca⟩ : UniversalCover Y y₀) = ⟨a, cb⟩
  rw [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.trans_refl]

/-- **The developing map of a maximal GH flat spacetime with (CC′) fills `int D(Σ)`**
(Rem `dependance`, l.3552–3554 of the labelled file, in the form `𝒟(M̃) = int D(Σ)`). Let
`Σ = 𝒟(S̃)` and `Γ = ρ(π₁M)`. On `W = int D(Σ)`, `Γ` acts freely and acausally (`W ⊆ U(Γ)`,
`cover_minkQ_pos`), properly discontinuously (`cover_finite_smul_inter`), `W` is connected and
causally convex hence GH, `Σ` is a `Γ`-invariant Cauchy surface of `W`
(`isCauchySurfaceOn_interior_dependenceDomain`) and finitely many `γ` relate two points
(`cover_finite_le_smul`): so `B = Γ\W` is a GH flat spacetime (Examples'
`gh_toFlatSpacetime`). `𝒟` is injective with image in `W` (Prop 8.12, `bprop_danom`), so it
descends to an isometric embedding `M → B` carrying `S` onto the Cauchy surface `Γ\Σ`: a flat
Cauchy embedding, which `MGH M` makes onto (after `ULift` to `M`'s universe), and then `𝒟(M̃)`
is the `Γ`-invariant `W`. -/
theorem cover_range_eq_of_mgh (M : FlatSpacetime.{u} d) (hM : MGH M) {x₀ : M}
    {D : UniversalCover M x₀ → Minkowski d} {ρ : Deck (UniversalCover.proj M x₀) →* isom d}
    (hpair : IsDevelopingPair x₀ D ρ) {S : Set M} (h : DevelopsCC x₀ D S) :
    range D = interior (dependenceDomain (minkowski d) ⊤ (D '' (UniversalCover.proj M x₀ ⁻¹' S))) := by
  letI := flatCoverChartedSpace d M x₀
  have hGH := hM.1
  have hcc := ccAction_of_developsCC hpair h
  obtain ⟨gf, hgf, hgfS⟩ := isEntireAcausalGraph_iff.1 h.cc.entire
  have hDW0 := range_subset_dependenceDomain_of_developsCC hpair hGH.1 h
  rw [hgfS] at hcc hDW0 ⊢
  set Γ := ρ.range with hΓ
  set W : Opens (Minkowski d) :=
    ⟨interior (dependenceDomain (minkowski d) ⊤ (graph gf)), isOpen_interior⟩ with hWdef
  have hDW : range D ⊆ W := interior_maximal hDW0 hpair.gx.isOpenMap.isOpen_range
  -- the action of `Γ` on `W`
  haveI : FlatQuotient.Invariant Γ W := ⟨fun γ p hp => by
    have := cover_smul_mem_interior_dependenceDomain hcc.cc γ hp
    rwa [hcc.inv γ γ.2] at this⟩
  haveI : IsCancelSMul Γ W := by
    rw [isCancelSMul_iff_eq_one_of_smul_eq]
    intro γ x hx
    by_contra h1
    exact cover_smul_ne hcc γ.2 (fun e => h1 (Subtype.ext e)) (interior_subset x.2)
      (congrArg Subtype.val hx)
  haveI : ProperlyDiscontinuousSMul Γ W :=
    properlyDiscontinuousSMul_of_finite fun K hK hKc => cover_finite_smul_inter hcc hK hKc
  have hac : FlatQuotient.ActsAcausally Γ W := fun γ h1 x hx => by
    rw [flat_le_top_subtype_iff] at hx
    exact cover_not_le_smul hcc γ.2 (fun e => h1 (Subtype.ext e)) (interior_subset x.2)
      ((minkowski d).le_mono le_top hx)
  have hfin : ∀ x y : W, {γ : Γ | (flatCausality d W).le ⊤ x (γ • y)}.Finite := fun x y =>
    ((cover_finite_le_smul hcc (interior_subset x.2) (interior_subset y.2)).preimage
      Subtype.val_injective.injOn).subset fun γ hγ =>
        ⟨γ.2, (minkowski d).le_mono le_top ((flat_le_top_subtype_iff W _ _).1 hγ)⟩
  have hGHW : (flatCausality d W).GloballyHyperbolic :=
    globallyHyperbolic_subtype W (globallyHyperbolicOn_of_causallyConvexIn (cover_causallyConvexIn hgf))
  have hconn : IsConnected (W : Set (Minkowski d)) := cover_isConnected hgf
  set B := FlatQuotient.toFlatSpacetime Γ W hconn
  have hGHB : GH B := FlatQuotient.gh_toFlatSpacetime Γ W hconn hac hGHW hfin
  -- the descended map `M → B`
  haveI := locPathConnectedSpace_of_flat d M
  haveI : PathConnectedSpace M := pathConnectedSpace_iff_connectedSpace.2 inferInstance
  have hqs : Surjective (UniversalCover.proj M x₀) := UniversalCover.proj_surjective
  have hql : IsLocalIsometry d (UniversalCover.proj M x₀) := isLocalIsometry_flatCover_proj x₀
  set π : W → B := FlatQuotient.proj Γ W
  have hπl : IsLocalIsometry d π := FlatQuotient.isLocalIsometry_proj Γ W
  have hfib : ∀ p q : W, π p = π q ↔ ∃ γ ∈ Γ, γ • (p : Minkowski d) = q := fun _ _ =>
    FlatQuotient.proj_eq_proj_iff'
  set D' : UniversalCover M x₀ → W := fun z => ⟨D z, hDW (mem_range_self z)⟩
  have hDl : IsLocalIsometry d D := isLocalIsometry_iff_eventually.2 ⟨hpair.gx.1, hpair.gx.2⟩
  have hD'l : IsLocalIsometry d D' :=
    cover_isLocalIsometry_of_comp (isIsometricEmbedding_subtype_val W).1
      (hDl.continuous.subtype_mk _) hDl
  set fM : M → B := fun x => π (D' (surjInv hqs x))
  have key : ∀ z, fM (UniversalCover.proj M x₀ z) = π (D' z) := by
    intro z
    set z' := surjInv hqs (UniversalCover.proj M x₀ z)
    obtain ⟨γ, hγ⟩ := cover_exists_deck_apply_eq z z'
      (surjInv_eq hqs (UniversalCover.proj M x₀ z)).symm
    refine ((hfib (D' z) (D' z')).2 ⟨ρ γ, ⟨γ, rfl⟩, ?_⟩).symm
    simp only [D']
    rw [← hpair.equiv, hγ]
  have hfq : fM ∘ (UniversalCover.proj M x₀) = π ∘ D' := funext key
  have hfl : IsLocalIsometry d fM := cover_isLocalIsometry_of_comp_right hql hqs (hfq ▸ hπl.comp hD'l)
  have hinj : Injective D := injective_of_developsCC hpair h
  have hfi : Injective fM := by
    intro x x' hxx'
    obtain ⟨z, rfl⟩ := hqs x
    obtain ⟨z', rfl⟩ := hqs x'
    rw [key, key] at hxx'
    obtain ⟨_, ⟨γ, rfl⟩, hγ⟩ := (hfib _ _).1 hxx'
    have h1 : D (γ.1 z) = D z' := by rw [hpair.equiv]; exact hγ
    rw [← hinj h1]
    exact (proj_deck_apply γ z).symm
  -- `fM` carries `S` onto the Cauchy surface `Γ\Σ` of `B`
  have hSW : graph gf ⊆ W := graph_subset_interior_dependenceDomain hgf
  have himgS : fM '' S = π '' (Subtype.val ⁻¹' graph gf : Set W) := by
    ext b
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨z, rfl⟩ := hqs x
      refine ⟨D' z, ?_, (key z).symm⟩
      show D z ∈ graph gf
      rw [← hgfS]; exact ⟨z, hx, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      have hw' : (w : Minkowski d) ∈ D '' (UniversalCover.proj M x₀ ⁻¹' S) := by
        rw [hgfS]; exact hw
      obtain ⟨z, hz, hzw⟩ := hw'
      refine ⟨UniversalCover.proj M x₀ z, hz, ?_⟩
      rw [key]
      congr 1
      exact Subtype.ext hzw
  have hCB : (flatCausality d B).IsCauchySurface (fM '' S) := by
    rw [himgS]
    exact FlatQuotient.isCauchySurface_image_of_isCauchySurfaceOn Γ W hac hSW
      (fun γ hγ p hp => hcc.smul_mem hγ hp) (isCauchySurfaceOn_interior_dependenceDomain hgf)
  have hfC : IsFlatCauchyEmbedding d fM :=
    isFlatCauchyEmbedding_iff.2 ⟨⟨hfl, hfi⟩, hGH, hGHB, S, h.cauchy, hCB⟩
  -- maximality, after the universe transport
  obtain ⟨hφ, hφs⟩ := coverULiftSpacetime_up.{u, 0} (d := d) B
  have hsurj : Surjective (coverULiftUp.{u, 0} B ∘ fM) :=
    hM.2 (coverULiftSpacetime.{u, 0} B) _ (cover_isFlatCauchyEmbedding_comp hfC hφ hφs)
  have hfs : Surjective fM := fun b => by
    obtain ⟨x, hx⟩ := hsurj (coverULiftUp.{u, 0} B b)
    exact ⟨x, ULift.up_injective hx⟩
  -- the end: `𝒟(M̃) = W`
  refine Subset.antisymm hDW fun p hp => ?_
  obtain ⟨x, hx⟩ := hfs (π ⟨p, hp⟩)
  obtain ⟨z, rfl⟩ := hqs x
  rw [key] at hx
  obtain ⟨_, ⟨γ, rfl⟩, hγ⟩ := (hfib _ _).1 hx
  exact ⟨γ.1 z, by rw [hpair.equiv]; exact hγ⟩

/-! ## §5 Every flat Cauchy embedding of a finite cover is onto -/

/-- **An injective developing map: every Cauchy surface `S` of `X` develops onto a Cauchy surface
of `𝒟(X̃)`, and `𝒟(X̃) ⊆ D(𝒟(S̃))`** (the argument of Nonloxodromic's
`range_subset_dependenceDomain_of_developsCC`, for any Cauchy surface once `𝒟` is injective). -/
theorem cover_isCauchySurfaceOn_range {X : Type*} [TopologicalSpace X]
    [ChartedSpace (Minkowski d) X] [HasGroupoid X (gxGroupoid (isom d) (Minkowski d))] {y₀ : X}
    {D : UniversalCover X y₀ → Minkowski d} {ρ : Deck (UniversalCover.proj X y₀) →* isom d}
    (hpair : IsDevelopingPair y₀ D ρ) (hcaus : (flatCausality d X).IsCausal) (hinj : Injective D)
    {W : Opens (Minkowski d)} (hW : (W : Set (Minkowski d)) = range D) {S : Set X}
    (hS : (flatCausality d X).IsCauchySurface S) :
    (minkowski d).IsCauchySurfaceOn W (D '' (UniversalCover.proj X y₀ ⁻¹' S)) ∧
      range D ⊆ dependenceDomain (minkowski d) ⊤ (D '' (UniversalCover.proj X y₀ ⁻¹' S)) := by
  letI := flatCoverChartedSpace d X y₀
  haveI := hasGroupoid_flatCover (d := d) X y₀
  set Sh := UniversalCover.proj X y₀ ⁻¹' S
  have hiso : IsIsometricEmbedding d D :=
    ⟨isLocalIsometry_iff_eventually.2 ⟨hpair.gx.1, hpair.gx.2⟩, hinj⟩
  have hW' : (W : Set (Minkowski d)) = D '' ((⊤ : Opens (UniversalCover X y₀)) :
      Set (UniversalCover X y₀)) := by
    rw [Opens.coe_top, image_univ, hW]
  have hC : (minkowski d).IsCauchySurfaceOn W (D '' Sh) := by
    have := (hiso.isEMorphism.isCauchySurfaceOn_image_iff hinj.injOn le_rfl hW'
      (subset_univ Sh)).1 (isCauchySurface_liftSet y₀ hcaus hS)
    rwa [flatCausality_self] at this
  refine ⟨hC, fun y hy => ⟨trivial, fun I c hc ⟨t, ht, hct⟩ => ?_⟩⟩
  have hcW : c t ∈ W := by rw [hct]; show y ∈ (W : Set (Minkowski d)); rw [hW]; exact hy
  obtain ⟨_, ⟨⟨r, hr, rfl⟩, hrS⟩, -⟩ := hC _ c
    (Causality.inextensible_ordConnectedComponent minkowski_isCausal hc ht hcW)
  exact ⟨c r, ⟨r, (ordConnectedComponent_subset hr).1, rfl⟩, hrS⟩

/-- **The lifting argument** (l.3586–3611 for the target, read with Rem `dependance`): let `M` be
GH with a developing pair `(𝒟, ρ)` at `x₀` and (CC′) for `S`, and suppose `𝒟(M̃) = int D(Σ)`
(`Σ = 𝒟(S̃)`). Let `p : M' → M` be a finite cover with `M'` Cauchy-compact, and `g : M' → N` a flat
Cauchy embedding. Then `g` is onto. The universal cover `M̃ → M` lifts through `p` to `q : M̃ → M'`
and `g ∘ q` lifts to `G : M̃ → Ñ`; by rigidity `𝒟_N ∘ G = h 𝒟`. `N` is Cauchy-compact (the image
of a compact Cauchy surface of `M'` is a Cauchy surface, acausal under the flat causal flow), hence
Cauchy-complete (L9) with an injective developing map whose image has the (CC′) Cauchy surface
`Σ_N`; the developed lift `Σ₂` of the Cauchy surface `g(p⁻¹ S)` is then (CC′) too
(`ccPrime_of_isCauchySurfaceOn`) and contains the entire graph `hΣ`, so `Σ₂ = hΣ`, and
`𝒟_N(Ñ) ⊆ int D(hΣ) = h 𝒟(M̃) = 𝒟_N(G(M̃))`: `G` is onto, hence so is `g`. -/
theorem cover_surjective_of_range_eq {M : FlatSpacetime.{u} d} (hGH : GH M) {x₀ : M}
    {D : UniversalCover M x₀ → Minkowski d} {ρ : Deck (UniversalCover.proj M x₀) →* isom d}
    (hpair : IsDevelopingPair x₀ D ρ) {S : Set M} (h : DevelopsCC x₀ D S)
    (hrange : range D =
      interior (dependenceDomain (minkowski d) ⊤ (D '' (UniversalCover.proj M x₀ ⁻¹' S))))
    {M' : FlatSpacetime.{v} d} {p : M' → M} (hp : IsFiniteCover d p) (hC' : CauchyCompact M')
    {N : FlatSpacetime.{w} d} {g : M' → N} (hg : IsFlatCauchyEmbedding d g) : Surjective g := by
  obtain ⟨hgi, -, hGHN, -⟩ := isFlatCauchyEmbedding_iff.1 hg
  -- `N` is Cauchy-compact, hence Cauchy-complete
  obtain ⟨Sc, hSc, hScc, -⟩ := hC'
  have hgSc : (flatCausality d N).IsCauchySurface (g '' Sc) := hg.isCauchySurface_image hSc
  have hacN : (flatCausality d N).IsAcausal (g '' Sc) :=
    isAcausal_of_isCauchySurface_of_hasChronalCausalFlow flat_hasChronalCausalFlow hgSc
  have hCCN : IsCauchyComplete d N :=
    isCauchyComplete_of_isCompact_cauchy N hGHN hgSc (hScc.image hgi.continuous) hacN
  -- developing data of `N`
  obtain ⟨m'⟩ : Nonempty M' := inferInstance
  set y₀ := g m'
  obtain ⟨DN, ρN, hpairN⟩ := exists_isDevelopingPair (d := d) y₀
  obtain ⟨SN, hSN⟩ := exists_developsCC_of_isCauchyComplete N hGHN hCCN y₀
  have hdevN : DevelopsCC y₀ DN SN := by
    obtain ⟨h1, h2, h3, h4⟩ := hSN DN hpairN.gx
    exact ⟨h1, h2, ⟨h3, h4⟩⟩
  have hinjN : Injective DN := injective_of_developsCC hpairN hdevN
  letI := flatCoverChartedSpace d M x₀
  haveI := hasGroupoid_flatCover (d := d) M x₀
  letI := flatCoverChartedSpace d N y₀
  haveI := hasGroupoid_flatCover (d := d) N y₀
  haveI := locPathConnectedSpace_of_flat d M
  haveI := locPathConnectedSpace_of_flat d N
  haveI : PathConnectedSpace M := pathConnectedSpace_iff_connectedSpace.2 inferInstance
  haveI : PathConnectedSpace N := pathConnectedSpace_iff_connectedSpace.2 inferInstance
  haveI : SimplyConnectedSpace (UniversalCover M x₀) :=
    UniversalCover.simplyConnectedSpace (semilocallySimplyConnected_of_flat d M)
  have hql : IsLocalIsometry d (UniversalCover.proj M x₀) := isLocalIsometry_flatCover_proj x₀
  have hqlN : IsLocalIsometry d (UniversalCover.proj N y₀) := isLocalIsometry_flatCover_proj y₀
  -- the lifts `q : M̃ → M'` and `G : M̃ → Ñ`
  obtain ⟨a₀, ha₀⟩ := UniversalCover.proj_surjective (y₀ := x₀) (p m')
  obtain ⟨q, hqloc, hq, hq0⟩ := cover_exists_lift hp.isCoveringMap hp.isLocalIsometry hql a₀ m'
    ha₀.symm
  obtain ⟨G, hGl, hG, -⟩ := cover_exists_lift (isCoveringMap_flatCover_proj d N y₀) hqlN
    (hgi.1.comp hqloc) a₀ (UniversalCover.base y₀) (by simp only [comp_apply, hq0]; rfl)
  -- rigidity: `𝒟_N ∘ G = h 𝒟`
  have hDl : IsLocalIsometry d DN := isLocalIsometry_iff_eventually.2 ⟨hpairN.gx.1, hpairN.gx.2⟩
  obtain ⟨hh, hhD, -⟩ := developing_unique_of_preconnected (G := isom d) (X := Minkowski d)
    (N := UniversalCover M x₀) (D := D) (D' := DN ∘ G) hpair.gx
    (isLocalIsometry_iff_eventually.1 (hDl.comp hGl) |> fun h' => ⟨h'.1, h'.2⟩)
  -- the two Cauchy surfaces of `𝒟_N(Ñ)`
  set WN : Opens (Minkowski d) := ⟨range DN, hpairN.gx.isOpenMap.isOpen_range⟩
  have hT : (flatCausality d N).IsCauchySurface (g '' (p ⁻¹' S)) :=
    hg.isCauchySurface_image
      (isCauchySurface_preimage hp.isCoveringMap hp.isLocalIsometry hGH.1 h.cauchy)
  have hRN := cover_isCauchySurfaceOn_range hpairN hGHN.1 hinjN (W := WN) rfl hdevN.cauchy
  have hRT := cover_isCauchySurfaceOn_range hpairN hGHN.1 hinjN (W := WN) rfl hT
  have hS2 : CCPrime (DN '' (UniversalCover.proj N y₀ ⁻¹' (g '' (p ⁻¹' S)))) :=
    ccPrime_of_isCauchySurfaceOn hdevN.cc (image_subset_range _ _) hRN.1 (image_subset_range _ _)
      hRT.1
  have hsub : hh • (D '' (UniversalCover.proj M x₀ ⁻¹' S)) ⊆
      DN '' (UniversalCover.proj N y₀ ⁻¹' (g '' (p ⁻¹' S))) := by
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨G z, ?_, hhD z⟩
    have h1 : UniversalCover.proj N y₀ (G z) = g (q z) := congrFun hG z
    have h2 : p (q z) = UniversalCover.proj M x₀ z := congrFun hq z
    show UniversalCover.proj N y₀ (G z) ∈ g '' (p ⁻¹' S)
    rw [h1]
    exact ⟨q z, by rw [mem_preimage, h2]; exact hz, rfl⟩
  have heq := cover_eq_of_subset_of_isEntireAcausalGraph (ccPrime_smul hh h.cc).entire
    hS2.entire hsub
  have hrN : range DN ⊆ interior (dependenceDomain (minkowski d) ⊤
      (hh • (D '' (UniversalCover.proj M x₀ ⁻¹' S)))) := by
    rw [heq]; exact interior_maximal hRT.2 hpairN.gx.isOpenMap.isOpen_range
  -- `G` is onto
  have hGs : Surjective G := fun n => by
    have h1 := cover_smul_mem_interior_dependenceDomain (ccPrime_smul hh h.cc) hh⁻¹
      (hrN (mem_range_self n))
    rw [inv_smul_smul, ← hrange] at h1
    obtain ⟨z, hz⟩ := h1
    refine ⟨z, hinjN ?_⟩
    have := hhD z
    simp only [comp_apply] at this
    rw [this, hz, smul_inv_smul]
  intro n₀
  obtain ⟨n, rfl⟩ := UniversalCover.proj_surjective (y₀ := y₀) n₀
  obtain ⟨z, rfl⟩ := hGs n
  exact ⟨q z, (congrFun hG z).symm⟩

/-- **A finite cover of a maximal Cauchy-compact GH flat spacetime is maximal** (finding 2; the
paper uses it silently, l.3573–3581): every flat Cauchy embedding of `M'` is onto. `M` is
Cauchy-complete (L9, `isCauchyComplete_of_isCompact_cauchy`), so it has (CC′) for some Cauchy
surface (the bridge); maximality gives `𝒟(M̃) = int D(Σ)` (`cover_range_eq_of_mgh`), and the
lifting argument concludes (`cover_surjective_of_range_eq`). -/
theorem cover_maximal_of_isFiniteCover {M : FlatSpacetime.{u} d} {M' : FlatSpacetime.{v} d}
    {p : M' → M} (hGH : GH M) (hC : CauchyCompact M) (hM : MGH M) (hp : IsFiniteCover d p)
    (hC' : CauchyCompact M') :
    ∀ (N : FlatSpacetime.{w} d) (g : M' → N), IsFlatCauchyEmbedding d g → Surjective g := by
  intro N g hg
  obtain ⟨x₀⟩ : Nonempty M := inferInstance
  obtain ⟨D, ρ, hpair⟩ := exists_isDevelopingPair (d := d) x₀
  obtain ⟨Sc, hSc, hScc, hac⟩ := hC
  have hCC := isCauchyComplete_of_isCompact_cauchy M hGH hSc hScc hac
  obtain ⟨S, hS⟩ := exists_developsCC_of_isCauchyComplete M hGH hCC x₀
  have h : DevelopsCC x₀ D S := by
    obtain ⟨h1, h2, h3, h4⟩ := hS D hpair.gx
    exact ⟨h1, h2, ⟨h3, h4⟩⟩
  exact cover_surjective_of_range_eq hGH hpair h (cover_range_eq_of_mgh M hM hpair h) hp hC' hg

end Causal.Flat.Cla
