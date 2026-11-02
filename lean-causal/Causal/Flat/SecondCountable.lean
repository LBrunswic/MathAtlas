import CausalScaffold.Flat.Developing
import CausalScaffold.Flat.Quotient
import CausalScaffold.Flat.FlatSpacetime
import Mathlib.Topology.Bases
import Mathlib.Topology.SeparatedMap

/-!
# `CausalScaffold.Flat.SecondCountable` — a flat spacetime is second countable (Geroch, flat case)

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §2.1 and
§2.3: a spacetime is a *manifold* (hence second countable), and a flat spacetime is an
`(Isom(𝐌ⁿ), 𝐌ⁿ)`-manifold. DEC-49 (2026-11-01): second countability is **proved, not assumed**.
This module proves it for every connected Hausdorff `(Isom(𝐌ⁿ), 𝐌ⁿ)`-manifold, and in fact for
every connected Hausdorff `(G, E)`-manifold with `E` a separable real normed space and `G` acting
analytically (e.g. faithfully by affine maps) — the flat case of R. Geroch, *Spinor structure of
space-times in general relativity I*, J. Math. Phys. 9 (1968): a connected Hausdorff manifold with
an affine connection is paracompact.

No ledger label: the statement is prose in the paper (no environment), so nothing is marked. It
discharges the hypothesis "M second countable" that `FlatSpacetime` does not carry
(`FlatSpacetime.lean`, SCOPE "No second countability"), and is exactly the input that
`CauchyComplete.exists_splitting_of_isCauchySurface` (tag `bridge-B1`) lacks.

> By spacetime, we mean here in general a (non closed) oriented
> and chronologically oriented lorentzian manifold. (`GHFspace.tex:423`–`424`)

> Truely speaking, every spacetimes considered in this work
> are flat, i.e., locally modeled on the Minkowski space.
> In other words, in the language of geometric structures
> (see e.g. \cite{gold}),
> they are $(G,X)$-manifolds with $X = {\bf M}^{n}$ and
> $G = \mbox{Isom}(M^{n})$. (`GHFspace.tex:485`–`490`)

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; the library's `Minkowski d =
ℝ × EuclideanSpace ℝ (Fin d)` has `d` spatial dimensions, so Barbot's `n` is `d + 1`.

## Main declarations

* `Causal.secondCountableTopology_of_isLocalHomeomorph` — **the core**: a preconnected Hausdorff
  space `N` with a local homeomorphism `D : N → E` into a separable real normed space is second
  countable. Proof without paths: the countable set `S` of points reached from `p₀` by finite
  chains of ball sections of `D` at points of a countable dense `C ⊆ E` has a clopen closure,
  and the images of the balls of radius `1/(n+1)` of sections at points of `S` are a countable
  basis.
* `Causal.IsBallSection` and its API (`exists_isBallSection`, `IsBallSection.eqOn` —
  uniqueness on the common ball, `IsBallSection.isOpen_image`, `IsBallSection.recenter`).
* `Causal.secondCountableTopology_of_gx` — **Geroch's theorem for `(G, E)`-structures**: a
  connected Hausdorff `(G, E)`-manifold, `G` acting analytically on a separable real normed
  space `E`, is second countable (the core on the universal cover `M̃` with its developing map,
  pushed down by the open surjection `proj`).
* `Causal.isRigidAction_of_affine`, `Causal.secondCountableTopology_of_affine` — the affine
  case: `G` acts faithfully by affine maps.
* `Causal.Flat.flat_secondCountableTopology` — **the flat case** (DEC-49): every connected
  Hausdorff `(Isom(𝐌ⁿ), 𝐌ⁿ)`-manifold is second countable;
  `Causal.Flat.FlatSpacetime.secondCountableTopology` (an instance on `FlatSpacetime d`).
* Witnesses: `𝐌ⁿ` itself (`flat_secondCountableTopology_minkowski`) and the quotient
  `ℤ e₁\𝐌ⁿ` (`flat_secondCountableTopology_spaceGroup`).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `M` a manifold: second countable | — not a hypothesis here but the conclusion: proved (DEC-49), not assumed |
| `M` Hausdorff | ✓ carried: `T2Space M` (the line with uncountably many origins, a non-Hausdorff `(ℝ, ℝ)`-manifold, is not second countable) |
| `M` connected | ✓ carried: `ConnectedSpace M` (a disjoint union of uncountably many copies of `𝐌ⁿ` is not second countable) |
| `M` an `(Isom(𝐌ⁿ), 𝐌ⁿ)`-manifold | ⚠ weakened: any `(G, E)`-manifold, `E` a separable real normed space, `G` acting analytically by homeomorphisms (`secondCountableTopology_of_gx`) |
| Geroch: an affine connection | ⚠ weakened: no affine structure is used beyond the developing map; affine actions are one inhabitant (`secondCountableTopology_of_affine`) |

## SCOPE (disclosed)

* **(a)** The paper never states second countability as a result: it is part of "manifold"
  (l.423–424). DEC-49 asks for its proof; the statement proved is the classical one, in the
  generality the route allows. Nothing is marked.
* **(b)** The route is not Geroch's (an auxiliary Riemannian metric on the frame bundle) nor the
  dispatch's "rational broken lines": the developing map `D : M̃ → E` is a local homeomorphism
  from a connected Hausdorff space, and ball sections of `D` with centres in a countable dense
  set already reach a dense countable set (clopen closure), with no path or compactness argument.
  Separability alone of `M` is never used, and does not suffice (Prüfer surface): what is used is
  the global coordinate `D` on `M̃`.
* **(c)** The general form needs the action analytic (faithful and rigid) only because the
  developing theorem (`Causal.developing_theorem`, ported from gx) is stated so.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. The universal cover
and the developing theorem are `CausalScaffold.Port.UniversalCover` / `CausalScaffold.Port.
Developing` (ported from gx, WP-32a). Written by WP-34f-SecondCountable.
-/

namespace Causal

open Set Filter Topology TopologicalSpace Metric

/-! ### Ball sections of a local homeomorphism into a normed space -/

section BallSection

variable {N : Type*} [TopologicalSpace N] {E : Type*} [NormedAddCommGroup E]

/-- **A ball section of `D` at `p` of radius `r`**: a map `s : E → N`, continuous on the ball
`B(D p, r)`, which is a right inverse of `D` there and sends `D p` to `p`. -/
def IsBallSection (D : N → E) (p : N) (r : ℝ) (s : E → N) : Prop :=
  ContinuousOn s (ball (D p) r) ∧ (∀ w ∈ ball (D p) r, D (s w) = w) ∧ s (D p) = p

variable {D : N → E}

theorem IsBallSection.mono {p : N} {r r' : ℝ} {s : E → N} (h : IsBallSection D p r s)
    (hr : r' ≤ r) : IsBallSection D p r' s :=
  ⟨h.1.mono (ball_subset_ball hr), fun w hw => h.2.1 w (ball_subset_ball hr hw), h.2.2⟩

theorem IsBallSection.continuousAt {p : N} {r : ℝ} {s : E → N} (h : IsBallSection D p r s)
    {w : E} (hw : w ∈ ball (D p) r) : ContinuousAt s w :=
  h.1.continuousAt (isOpen_ball.mem_nhds hw)

/-- **Recentring**: a ball section at `p` is a ball section at `s c` of any radius `r'` with
`B(c, r') ⊆ B(D p, r)`. -/
theorem IsBallSection.recenter {p : N} {r r' : ℝ} {s : E → N} (h : IsBallSection D p r s)
    {c : E} (hc : c ∈ ball (D p) r) (hr' : r' + dist c (D p) ≤ r) :
    IsBallSection D (s c) r' s := by
  have hDc : D (s c) = c := h.2.1 c hc
  have hsub : ball (D (s c)) r' ⊆ ball (D p) r := by
    rw [hDc]; exact ball_subset_ball' hr'
  exact ⟨h.1.mono hsub, fun w hw => h.2.1 w (hsub hw), by rw [hDc]⟩

/-- **Existence**: a local homeomorphism has a ball section of positive radius at every point. -/
theorem exists_isBallSection (hD : IsLocalHomeomorph D) (p : N) :
    ∃ r > 0, ∃ s, IsBallSection D p r s := by
  obtain ⟨e, hpe, hDe⟩ := hD p
  have hDp : D p ∈ e.target := by rw [hDe]; exact e.map_source hpe
  obtain ⟨r, hr, hrt⟩ := Metric.isOpen_iff.1 e.open_target (D p) hDp
  refine ⟨r, hr, e.symm, e.continuousOn_symm.mono hrt, fun w hw => ?_, ?_⟩
  · rw [hDe]; exact e.right_inv (hrt hw)
  · rw [hDe]; exact e.left_inv hpe

/-- **Uniqueness**: two ball sections at the same point agree on the smaller ball (`N`
Hausdorff, the ball connected). -/
theorem IsBallSection.eqOn [NormedSpace ℝ E] [T2Space N] (hD : IsLocalHomeomorph D) {p : N} {r r' : ℝ}
    {s s' : E → N} (h : IsBallSection D p r s) (h' : IsBallSection D p r' s') :
    EqOn s s' (ball (D p) (min r r')) := by
  by_cases hpos : 0 < min r r'
  · have hm := h.mono (min_le_left r r')
    have hm' := h'.mono (min_le_right r r')
    refine (T2Space.isSeparatedMap D).eqOn_of_comp_eqOn hD.isLocallyInjective
      (convex_ball _ _).isPreconnected hm.1 hm'.1 (fun w hw => ?_) (mem_ball_self hpos)
      (h.2.2.trans h'.2.2.symm)
    simp only [Function.comp_apply, hm.2.1 w hw, hm'.2.1 w hw]
  · rw [ball_eq_empty.2 (not_lt.1 hpos)]; exact eqOn_empty _ _

/-- **Openness**: a ball section maps open subsets of its ball to open sets. -/
theorem IsBallSection.isOpen_image (hD : IsLocalHomeomorph D) {p : N} {r : ℝ} {s : E → N}
    (h : IsBallSection D p r s) {O : Set E} (hO : IsOpen O) (hOr : O ⊆ ball (D p) r) :
    IsOpen (s '' O) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨e, hxe, hDe⟩ := hD (s w)
  have hA : IsOpen (O ∩ s ⁻¹' e.source) :=
    (h.1.mono hOr).isOpen_inter_preimage hO e.open_source
  have hV : IsOpen (e.source ∩ e ⁻¹' (O ∩ s ⁻¹' e.source)) := e.isOpen_inter_preimage hA
  have hDw : D (s w) = w := h.2.1 w (hOr hw)
  refine Filter.mem_of_superset (hV.mem_nhds ⟨hxe, ?_⟩) ?_
  · show e (s w) ∈ O ∩ s ⁻¹' e.source
    rw [← hDe, hDw]; exact ⟨hw, hxe⟩
  · rintro z ⟨hz, hzO, hzs⟩
    refine ⟨e z, hzO, e.injOn hzs hz ?_⟩
    have := h.2.1 (e z) (hOr hzO)
    rw [hDe] at this
    exact this

end BallSection

/-! ### The core: a local homeomorphism into a separable normed space -/

section Core

variable {N : Type*} [TopologicalSpace N] {E : Type*} [NormedAddCommGroup E] {D : N → E}

/-- One step of the chain construction: the values at points of `C` of the ball sections at `q`. -/
def ballStep (D : N → E) (C : Set E) (q : N) : Set N :=
  {x | ∃ c ∈ C, ∃ r s, IsBallSection D q r s ∧ c ∈ ball (D q) r ∧ x = s c}

theorem countable_ballStep [NormedSpace ℝ E] [T2Space N] (hD : IsLocalHomeomorph D) {C : Set E}
    (hC : C.Countable) (q : N) : (ballStep D C q).Countable := by
  refine (hC.biUnion fun c _ =>
    (?_ : Set.Subsingleton {x | ∃ r s, IsBallSection D q r s ∧ c ∈ ball (D q) r ∧ x = s c}
      ).countable).mono ?_
  · rintro x ⟨r, s, hs, hc, rfl⟩ x' ⟨r', s', hs', hc', rfl⟩
    exact hs.eqOn hD hs' (by rw [mem_ball] at hc hc' ⊢; exact lt_min hc hc')
  · rintro x ⟨c, hcC, r, s, hs, hc, rfl⟩
    exact mem_biUnion hcC ⟨r, s, hs, hc, rfl⟩

/-- The points reached from `p₀` in at most `n` steps. -/
def ballReach (D : N → E) (C : Set E) (p₀ : N) : ℕ → Set N
  | 0 => {p₀}
  | n + 1 => ballReach D C p₀ n ∪ ⋃ q ∈ ballReach D C p₀ n, ballStep D C q

theorem countable_ballReach [NormedSpace ℝ E] [T2Space N] (hD : IsLocalHomeomorph D) {C : Set E}
    (hC : C.Countable) (p₀ : N) : ∀ n, (ballReach D C p₀ n).Countable
  | 0 => countable_singleton p₀
  | n + 1 => (countable_ballReach hD hC p₀ n).union
      ((countable_ballReach hD hC p₀ n).biUnion fun q _ => countable_ballStep hD hC q)

theorem ballStep_subset {C : Set E} {p₀ q : N} (hq : q ∈ ⋃ n, ballReach D C p₀ n) :
    ballStep D C q ⊆ ⋃ n, ballReach D C p₀ n := by
  obtain ⟨n, hn⟩ := mem_iUnion.1 hq
  exact fun x hx => mem_iUnion.2 ⟨n + 1, Or.inr (mem_biUnion hn hx)⟩

/-- **Density of the reached set**: on a preconnected `N`, the closure of the set of points
reached from `p₀` is clopen, hence everything. -/
theorem closure_ballReach_eq_univ [NormedSpace ℝ E] [T2Space N] [PreconnectedSpace N] (hD : IsLocalHomeomorph D)
    {C : Set E} (hC : Dense C) (p₀ : N) : closure (⋃ n, ballReach D C p₀ n) = univ := by
  set S := ⋃ n, ballReach D C p₀ n
  have hp₀ : p₀ ∈ S := mem_iUnion.2 ⟨0, rfl⟩
  refine IsClopen.eq_univ ⟨isClosed_closure, ?_⟩ ⟨p₀, subset_closure hp₀⟩
  rw [isOpen_iff_mem_nhds]
  intro y hy
  obtain ⟨r, hr, s, hs⟩ := exists_isBallSection hD y
  set δ := r / 4 with hδ
  have hδpos : 0 < δ := by positivity
  have hδr : ball (D y) δ ⊆ ball (D y) r := ball_subset_ball (by linarith)
  have hVo : IsOpen (s '' ball (D y) δ) := hs.isOpen_image hD isOpen_ball hδr
  have hyV : y ∈ s '' ball (D y) δ := ⟨D y, mem_ball_self hδpos, hs.2.2⟩
  obtain ⟨_, ⟨c, hc, rfl⟩, hqS⟩ := mem_closure_iff.1 hy _ hVo hyV
  have hcr : c ∈ ball (D y) r := hδr hc
  have hq : IsBallSection D (s c) (3 * δ) s :=
    hs.recenter hcr (by rw [mem_ball] at hc; linarith)
  have hDq : D (s c) = c := hs.2.1 c hcr
  refine Filter.mem_of_superset (hVo.mem_nhds hyV) ?_
  rintro _ ⟨w, hw, rfl⟩
  rw [mem_closure_iff_nhds]
  intro U hU
  have hU' : s ⁻¹' U ∩ ball (D y) δ ∈ 𝓝 w :=
    inter_mem ((hs.continuousAt (hδr hw)).preimage_mem_nhds hU) (isOpen_ball.mem_nhds hw)
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hU'
  obtain ⟨c', hc'C, hc'⟩ := hC.exists_mem_open isOpen_ball ⟨w, mem_ball_self hε⟩
  have hc'U := hεU hc'
  refine ⟨s c', hc'U.1, ballStep_subset hqS ⟨c', hc'C, 3 * δ, s, hq, ?_, rfl⟩⟩
  rw [hDq, mem_ball]
  have h1 := hc'U.2
  rw [mem_ball] at h1 hc
  calc dist c' c ≤ dist c' (D y) + dist (D y) c := dist_triangle _ _ _
    _ < δ + δ := by rw [dist_comm (D y) c]; exact add_lt_add h1 hc
    _ ≤ 3 * δ := by linarith

/-- **The core theorem.** A preconnected Hausdorff space with a local homeomorphism into a
separable real normed space is second countable. -/
theorem secondCountableTopology_of_isLocalHomeomorph [NormedSpace ℝ E] [T2Space N] [PreconnectedSpace N]
    [SeparableSpace E] (hD : IsLocalHomeomorph D) : SecondCountableTopology N := by
  rcases isEmpty_or_nonempty N with hN | ⟨⟨p₀⟩⟩
  · exact ⟨⟨∅, countable_empty, Subsingleton.elim _ _⟩⟩
  obtain ⟨C, hCc, hCd⟩ := exists_countable_dense E
  set S := ⋃ n, ballReach D C p₀ n
  have hSc : S.Countable := countable_iUnion (countable_ballReach hD hCc p₀)
  have hSd : closure S = univ := closure_ballReach_eq_univ hD hCd p₀
  set 𝓑 : Set (Set N) := ⋃ q ∈ S, ⋃ n : ℕ,
    {U | ∃ s, IsBallSection D q (1 / (n + 1)) s ∧ U = s '' ball (D q) (1 / (n + 1))}
  have h𝓑c : 𝓑.Countable := by
    refine hSc.biUnion fun q _ => countable_iUnion fun n => Set.Subsingleton.countable ?_
    rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩
    have := hs.eqOn hD hs'
    rw [min_self] at this
    exact this.image_eq
  have h𝓑o : ∀ U ∈ 𝓑, IsOpen U := by
    intro U hU
    simp only [𝓑, mem_iUnion, mem_setOf_eq] at hU
    obtain ⟨q, -, n, s, hs, rfl⟩ := hU
    exact hs.isOpen_image hD isOpen_ball subset_rfl
  have hB : IsTopologicalBasis 𝓑 := by
    refine isTopologicalBasis_of_isOpen_of_nhds h𝓑o fun y W hyW hW => ?_
    obtain ⟨r, hr, s, hs⟩ := exists_isBallSection hD y
    have hsW : s ⁻¹' W ∈ 𝓝 (D y) :=
      (hs.continuousAt (mem_ball_self hr)).preimage_mem_nhds (by rw [hs.2.2]; exact hW.mem_nhds hyW)
    obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.1 hsW
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < min ε r / 4 by positivity)
    set t : ℝ := 1 / (n + 1) with ht
    have htpos : 0 < t := by positivity
    have htε : 2 * t < ε := by have := min_le_left ε r; linarith
    have htr : 2 * t ≤ r := by have := min_le_right ε r; linarith
    have hδr : ball (D y) t ⊆ ball (D y) r := ball_subset_ball (by linarith)
    have hVo : IsOpen (s '' ball (D y) t) := hs.isOpen_image hD isOpen_ball hδr
    have hyV : y ∈ s '' ball (D y) t := ⟨D y, mem_ball_self htpos, hs.2.2⟩
    have hSV : (s '' ball (D y) t ∩ S).Nonempty := by
      have : y ∈ closure S := by rw [hSd]; trivial
      exact mem_closure_iff.1 this _ hVo hyV
    obtain ⟨_, ⟨c, hc, rfl⟩, hqS⟩ := hSV
    have hcr : c ∈ ball (D y) r := hδr hc
    have hct : dist c (D y) < t := hc
    have hq : IsBallSection D (s c) t s := hs.recenter hcr (by linarith)
    have hDq : D (s c) = c := hs.2.1 c hcr
    refine ⟨s '' ball (D (s c)) t, ?_, ?_, ?_⟩
    · simp only [𝓑, mem_iUnion, mem_setOf_eq]
      exact ⟨s c, hqS, n, s, hq, rfl⟩
    · refine ⟨D y, ?_, hs.2.2⟩
      rw [hDq, mem_ball, dist_comm]; exact hct
    · rintro _ ⟨w, hw, rfl⟩
      apply hεW
      rw [hDq, mem_ball] at hw
      rw [mem_ball]
      calc dist w (D y) ≤ dist w c + dist c (D y) := dist_triangle _ _ _
        _ < t + t := add_lt_add hw hct
        _ < ε := by linarith
  exact hB.secondCountableTopology h𝓑c

end Core

/-! ### Coverings of Hausdorff spaces -/

/-- **The total space of a covering of a Hausdorff space is Hausdorff**: points in one fibre are
separated by the covering (`IsCoveringMap.isSeparatedMap`), points in distinct fibres by
preimages. Private: `Causal.Flat.t2Space_of_isCoveringMap` (`Flat/CauchyComplete.lean`) is the same
statement, and a public copy here would make the name ambiguous inside `Causal.Flat`. -/
private theorem t2Space_of_isCoveringMap' {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] {f : X → Y} (hf : IsCoveringMap f) : T2Space X := by
  refine ⟨fun x₁ x₂ hne => ?_⟩
  by_cases h : f x₁ = f x₂
  · exact hf.isSeparatedMap x₁ x₂ h hne
  · obtain ⟨u, v, hu, hv, hxu, hxv, huv⟩ := t2_separation h
    exact ⟨f ⁻¹' u, f ⁻¹' v, hu.preimage hf.continuous, hv.preimage hf.continuous, hxu, hxv,
      huv.preimage f⟩

/-! ### Geroch's theorem for `(G, E)`-structures -/

section GX

variable {G : Type*} [Group G] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [SeparableSpace E] [MulAction G E] [ContinuousConstSMul G E]

/-- **Geroch's theorem, `(G, E)`-version.** A connected Hausdorff `(G, E)`-manifold, `G` acting
analytically (faithfully and rigidly) by homeomorphisms on a separable real normed space `E`, is
second countable. The universal cover `M̃` is connected and Hausdorff, its developing map
`M̃ → E` is a local homeomorphism, so `M̃` is second countable
(`secondCountableTopology_of_isLocalHomeomorph`), and so is its image `M` under the open
surjection `proj`. -/
theorem secondCountableTopology_of_gx [IsAnalyticAction G E] (M : Type*) [TopologicalSpace M]
    [T2Space M] [ConnectedSpace M] [ChartedSpace E M] [HasGroupoid M (gxGroupoid G E)] :
    SecondCountableTopology M := by
  haveI : LocPathConnectedSpace M := ChartedSpace.locPathConnectedSpace E M
  have hM := semilocallySimplyConnected_of_chartedSpace (E := E) M
  obtain ⟨x₀⟩ := (inferInstance : Nonempty M)
  letI := coverChartedSpace E hM x₀
  obtain ⟨dev, -, -, hdev, -⟩ := developing_theorem (G := G) (X := E) hM x₀
  have hp := UniversalCover.isCoveringMap_proj (y₀ := x₀) hM
  haveI : T2Space (UniversalCover M x₀) := t2Space_of_isCoveringMap' hp
  haveI : SecondCountableTopology (UniversalCover M x₀) :=
    secondCountableTopology_of_isLocalHomeomorph hdev
  haveI : PathConnectedSpace M := pathConnectedSpace_iff_connectedSpace.2 ‹_›
  exact (hp.isQuotientMap UniversalCover.proj_surjective).secondCountableTopology hp.isOpenMap

omit [SeparableSpace E] [ContinuousConstSMul G E] in
/-- An action by affine maps is rigid: two affine maps agreeing on a nonempty open set agree on
its affine span, which is everything (`IsOpen.affineSpan_eq_top`). -/
theorem isRigidAction_of_affine (haff : ∀ g : G, ∃ A : E →ᵃ[ℝ] E, ∀ x, g • x = A x) :
    IsRigidAction G E where
  smul_eq_of_eqOn {g h U} hU hne heq p := by
    obtain ⟨A, hA⟩ := haff g
    obtain ⟨B, hB⟩ := haff h
    have : A = B := AffineMap.ext_on (hU.affineSpan_eq_top hne) fun x hx => by
      rw [← hA, ← hB]; exact heq hx
    rw [hA, hB, this]

/-- **Geroch's theorem, affine case.** A connected Hausdorff `(G, E)`-manifold, `G` acting
faithfully by continuous affine maps on a separable real normed space `E`, is second countable. -/
theorem secondCountableTopology_of_affine [FaithfulSMul G E]
    (haff : ∀ g : G, ∃ A : E →ᵃ[ℝ] E, ∀ x, g • x = A x) (M : Type*) [TopologicalSpace M]
    [T2Space M] [ConnectedSpace M] [ChartedSpace E M] [HasGroupoid M (gxGroupoid G E)] :
    SecondCountableTopology M :=
  haveI : IsRigidAction G E := isRigidAction_of_affine haff
  haveI : IsAnalyticAction G E := {}
  secondCountableTopology_of_gx (G := G) (E := E) M

end GX

end Causal

namespace Causal.Flat

open Set TopologicalSpace

variable {d : ℕ}

/-- **A flat spacetime is second countable** (DEC-49; Geroch 1968, flat case). Every connected
Hausdorff `(Isom(𝐌ⁿ), 𝐌ⁿ)`-manifold `M` is second countable. Barbot's `n` is `d + 1`. -/
theorem flat_secondCountableTopology (M : Type*) [TopologicalSpace M] [T2Space M]
    [ConnectedSpace M] [ChartedSpace (Minkowski d) M]
    [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))] : SecondCountableTopology M :=
  secondCountableTopology_of_gx (G := isom d) (E := Minkowski d) M

/-- Every `FlatSpacetime` is second countable. -/
instance FlatSpacetime.secondCountableTopology (M : FlatSpacetime d) :
    SecondCountableTopology M :=
  flat_secondCountableTopology (d := d) M

/-- Witness: `𝐌ⁿ` itself satisfies every hypothesis of `flat_secondCountableTopology`. -/
theorem flat_secondCountableTopology_minkowski : SecondCountableTopology (Minkowski d) :=
  flat_secondCountableTopology (d := d) (Minkowski d)

/-- Witness: the quotient `ℤ e₁\𝐌ⁿ⁺¹` (`FlatQuotient.spaceGroup`) satisfies every hypothesis of
`flat_secondCountableTopology`. -/
theorem flat_secondCountableTopology_spaceGroup :
    SecondCountableTopology (FlatQuotient (FlatQuotient.spaceGroup d) ⊤) :=
  haveI := FlatQuotient.t2Space (FlatQuotient.spaceGroup d) ⊤
  haveI := FlatQuotient.connectedSpace (FlatQuotient.spaceGroup d) ⊤ FlatQuotient.isConnected_top
  flat_secondCountableTopology (d := d + 1) _

end Causal.Flat
