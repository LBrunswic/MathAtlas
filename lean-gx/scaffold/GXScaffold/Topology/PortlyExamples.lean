import GX.Topology.Portly

/-!
# Examples of skeletal sets

`papers/gx`, Section 2.1: `RamcovGX.tex:367`.

* `ex:following_example_skeletal_itemize` — `RamcovGX.tex:367` — partial: item 1 closed
  (`GX.isSkeletal_of_finite_surface`, via the countable generalisation
  `GX.isSkeletal_of_countable`); item 2 closed in the locally-flat reading
  (`GX.isSkeletal_of_tameKnot`, via `GX.isSkeletal_of_locallyFlat`); item 3 **false as written**
  (`GX.bowtie_counterexample`), corrected form `GX.isSkeletal_skeletonSpace` resting on a tagged
  `sorry` (`GX.isSkeletal_skeletonSpace_codim_two`); item 4 `GX.isSkeletal_of_isTotallyDisconnected`
  resting on a tagged `sorry` (`GX.isPreconnected_compl_of_isTotallyDisconnected`, dimension
  theory).

> The following example of $S$ are skeletal in $X$. $S$ finite and $X$ a surface; $S$ a tame
> knot in a $3$-manifold $X$; $S$ the $k$-skeleton of a pure $n$-dimensional simplicial complex
> $X$ with $k\leq n-2$; $S$ a Cantor wildly embedded into a $n$-manifold $X$.

## SCOPE (disclosed)

* Item 1: a surface is a Hausdorff space charted on `ℝ²`; proved for closed countable
  sets in any manifold modelled on a real normed space of dimension `> 1`.
* Item 2: a tame knot is read as a closed *locally flat* subset (flat charts onto open
  subsets of `ℝ × ℝ²` sending it to `ℝ × {0}`); the circle structure is not used.
* Item 3 is **false as written** (`GX.bowtie_counterexample`: two triangles sharing a
  vertex). Corrected form: add local strong connectivity in codimension `≥ 2`
  (`GX.IsLocallyStronglyConnected`, which the bow-tie fails:
  `GX.not_isLocallyStronglyConnected_bowtie`). The codimension-two case is a tagged `sorry`
  (local structure theory of geometric simplicial complexes); `k < n - 2` is derived from it.
* Item 4: proved for any closed totally disconnected set in a finite-dimensional
  manifold of dimension `≥ 2`, modulo the Euclidean core
  `GX.isPreconnected_compl_of_isTotallyDisconnected` (tagged `sorry`: dimension theory). In
  dimension `1` the item fails (`GX.eq_empty_of_isSkeletal_real`), as "wildly" presupposes.

Split from `GXScaffold.Topology.Portly` at graduation (2026-10-31); the rest graduated to
`GX.Topology.Portly`. Provenance: mathlib `fabf563a` (tag `v4.31.0`).
-/

noncomputable section

open Set Filter Topology

namespace GX

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-! ### Examples of skeletal sets (`ex:following_example_skeletal_itemize`) -/

/-- A local criterion: a closed `S` is skeletal as soon as every point has arbitrarily small open
neighbourhoods `N` with `N \ S` nonempty and preconnected. -/
theorem isSkeletal_of_local {S : Set X} (hS : IsClosed S)
    (hloc : ∀ x, ∀ O ∈ 𝓝 x, ∃ N, IsOpen N ∧ x ∈ N ∧ N ⊆ O ∧ (N ∩ Sᶜ).Nonempty ∧
      IsPreconnected (N ∩ Sᶜ)) :
    IsSkeletal S := by
  have hd : Dense Sᶜ := by
    rw [dense_iff_inter_open]
    rintro O hO ⟨x, hx⟩
    obtain ⟨N, -, -, hNO, hne, -⟩ := hloc x O (hO.mem_nhds hx)
    exact hne.mono (inter_subset_inter_left _ hNO)
  refine ⟨hS.isOpen_compl, hd, fun W hW hWc => ?_⟩
  refine isPreconnected_of_local hWc inter_subset_left
    (fun x hx => hW.inter_closure ⟨hx, hd x⟩) fun x hx => ?_
  obtain ⟨N, hNo, hxN, hNW, -, hNc⟩ := hloc x W (hW.mem_nhds hx)
  refine ⟨N, hNo, hxN, ?_⟩
  rwa [← inter_assoc, inter_eq_left.2 hNW]

/-- The chart form of the local criterion: if, in a chart `e` at `x`, every small ball around
`e x` meets the image of the complement of `S` in a nonempty preconnected set, then `x` has
arbitrarily small open neighbourhoods `N` with `N \ S` nonempty and preconnected. -/
theorem exists_nhds_of_chart {E : Type*} [PseudoMetricSpace E] {S : Set X}
    (e : OpenPartialHomeomorph X E) {x : X} (hx : x ∈ e.source)
    (hball : ∀ r > 0, Metric.ball (e x) r ⊆ e.target →
      (Metric.ball (e x) r ∩ e.symm ⁻¹' Sᶜ).Nonempty ∧
        IsPreconnected (Metric.ball (e x) r ∩ e.symm ⁻¹' Sᶜ)) :
    ∀ O ∈ 𝓝 x, ∃ N, IsOpen N ∧ x ∈ N ∧ N ⊆ O ∧ (N ∩ Sᶜ).Nonempty ∧
      IsPreconnected (N ∩ Sᶜ) := by
  intro O hO
  have hopen : IsOpen (e '' (e.source ∩ interior O)) := e.isOpen_image_source_inter isOpen_interior
  have hmem : e x ∈ e '' (e.source ∩ interior O) :=
    ⟨x, ⟨hx, mem_interior_iff_mem_nhds.2 hO⟩, rfl⟩
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.1 hopen _ hmem
  have hrt : Metric.ball (e x) r ⊆ e.target := hrsub.trans
    ((image_mono inter_subset_left).trans e.image_source_eq_target.subset)
  obtain ⟨hne, hpc⟩ := hball r hr hrt
  set N := e.source ∩ e ⁻¹' Metric.ball (e x) r
  have heq : N ∩ Sᶜ = e.symm '' (Metric.ball (e x) r ∩ e.symm ⁻¹' Sᶜ) := by
    ext y
    constructor
    · rintro ⟨⟨hys, hyb⟩, hyS⟩
      refine ⟨e y, ⟨hyb, ?_⟩, e.left_inv hys⟩
      simp only [mem_preimage, e.left_inv hys]; exact hyS
    · rintro ⟨z, ⟨hzb, hzS⟩, rfl⟩
      exact ⟨⟨e.map_target (hrt hzb), by simp only [mem_preimage, e.right_inv (hrt hzb)]; exact hzb⟩,
        hzS⟩
  refine ⟨N, e.isOpen_inter_preimage Metric.isOpen_ball, ⟨hx, Metric.mem_ball_self hr⟩, ?_, ?_, ?_⟩
  · rintro y ⟨hys, hyb⟩
    obtain ⟨z, ⟨hzs, hzO⟩, hz⟩ := hrsub hyb
    rw [← e.injOn hzs hys hz]
    exact interior_subset hzO
  · rw [heq]; exact hne.image _
  · rw [heq]; exact hpc.image _ (e.continuousOn_symm.mono (inter_subset_left.trans hrt))

/-- In a real normed space of dimension `> 1`, a ball minus a countable set is preconnected. -/
theorem isPreconnected_ball_diff_countable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hE : 1 < Module.rank ℝ E) (c : E) (r : ℝ) {T : Set E} (hT : T.Countable) :
    IsPreconnected (Metric.ball c r \ T) := by
  rcases le_or_gt r 0 with hr | hr
  · rw [Metric.ball_eq_empty.2 hr, empty_sdiff]; exact isPreconnected_empty
  set h := OpenPartialHomeomorph.univBall c r
  have hinj : Function.Injective h := by
    intro y z hyz
    exact h.injOn (by simp [h, OpenPartialHomeomorph.univBall_source])
      (by simp [h, OpenPartialHomeomorph.univBall_source]) hyz
  have hcont : Continuous h := by
    rw [← continuousOn_univ, ← OpenPartialHomeomorph.univBall_source c r]
    exact h.continuousOn
  have hpc := (hT.preimage hinj).isPathConnected_compl_of_one_lt_rank hE
  have himg : h '' (h ⁻¹' T)ᶜ = Metric.ball c r \ T := by
    rw [image_compl_preimage, ← image_univ, ← OpenPartialHomeomorph.univBall_source c r,
      h.image_source_eq_target, OpenPartialHomeomorph.univBall_target c hr]
  rw [← himg]
  exact hpc.isConnected.isPreconnected.image _ hcont.continuousOn

/-- In a nontrivial real normed space, a ball of positive radius minus a countable set is
nonempty. -/
theorem nonempty_ball_diff_countable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nontrivial E] (c : E) {r : ℝ} (hr : 0 < r) {T : Set E} (hT : T.Countable) :
    (Metric.ball c r \ T).Nonempty :=
  (hT.dense_compl ℝ).inter_open_nonempty _ Metric.isOpen_ball ⟨c, Metric.mem_ball_self hr⟩

/-- `ex:following_example_skeletal_itemize`, generalising the first item: a closed countable
subset of a manifold modelled on a real normed space of dimension `> 1` is skeletal. -/
theorem isSkeletal_of_countable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hE : 1 < Module.rank ℝ E) [ChartedSpace E X] {S : Set X} (hS : S.Countable)
    (hSc : IsClosed S) : IsSkeletal S := by
  have : Nontrivial E := (rank_pos_iff_nontrivial (R := ℝ)).1 (zero_lt_one.trans hE)
  refine isSkeletal_of_local hSc fun x => exists_nhds_of_chart (chartAt E x)
    (mem_chart_source E x) fun r hr hrt => ?_
  set e := chartAt E x
  have hT : (Metric.ball (e x) r ∩ e.symm ⁻¹' S).Countable := by
    refine (hS.image e).mono ?_
    rintro z ⟨hzb, hzS⟩
    exact ⟨e.symm z, hzS, e.right_inv (hrt hzb)⟩
  have heq : Metric.ball (e x) r ∩ e.symm ⁻¹' Sᶜ =
      Metric.ball (e x) r \ (Metric.ball (e x) r ∩ e.symm ⁻¹' S) := by
    ext z; simp
  rw [heq]
  exact ⟨nonempty_ball_diff_countable _ hr hT, isPreconnected_ball_diff_countable hE _ _ hT⟩

/-- `ex:following_example_skeletal_itemize`, first item: a finite subset of a surface is
skeletal. A surface is read as a Hausdorff space charted on `ℝ²`. -/
theorem isSkeletal_of_finite_surface [ChartedSpace (EuclideanSpace ℝ (Fin 2)) X] [T2Space X]
    {S : Set X} (hS : S.Finite) : IsSkeletal S :=
  isSkeletal_of_countable (E := EuclideanSpace ℝ (Fin 2))
    (by rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]; norm_num)
    hS.countable hS.isClosed

/-- `ex:following_example_skeletal_itemize`, generalising the second item: a closed subset of a
locally connected space which is *locally flat of codimension `≥ 2`* — every point of `S` has a
chart `e : X → F × G` (`dim G > 1`) in which `S` is `F × {0}` — is skeletal. -/
theorem isSkeletal_of_locallyFlat {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (hG : 1 < Module.rank ℝ G)
    [LocallyConnectedSpace X] {S : Set X} (hSc : IsClosed S)
    (hflat : ∀ x ∈ S, ∃ e : OpenPartialHomeomorph X (F × G), x ∈ e.source ∧
      ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0) :
    IsSkeletal S := by
  have : Nontrivial G := (rank_pos_iff_nontrivial (R := ℝ)).1 (zero_lt_one.trans hG)
  refine isSkeletal_of_local hSc fun x => ?_
  by_cases hx : x ∈ S
  · obtain ⟨e, hxe, he⟩ := hflat x hx
    refine exists_nhds_of_chart e hxe fun r hr hrt => ?_
    have hx2 : (e x).2 = 0 := (he x hxe).1 hx
    have hb : Metric.ball (e x) r = Metric.ball (e x).1 r ×ˢ Metric.ball (0 : G) r := by
      rw [← hx2, ball_prod_same]
    have heq : Metric.ball (e x) r ∩ e.symm ⁻¹' Sᶜ =
        Metric.ball (e x).1 r ×ˢ (Metric.ball (0 : G) r \ {0}) := by
      ext z
      have hiff : ∀ hz : z ∈ e.target, (e.symm z ∈ S ↔ z.2 = 0) := fun hz => by
        rw [he _ (e.map_target hz), e.right_inv hz]
      constructor
      · rintro ⟨hzb, hzS⟩
        have hzb' := hb ▸ hzb
        exact ⟨hzb'.1, hzb'.2, fun h0 => hzS ((hiff (hrt hzb)).2 h0)⟩
      · rintro ⟨hz1, hz2, hz0⟩
        have hzb : z ∈ Metric.ball (e x) r := by rw [hb]; exact ⟨hz1, hz2⟩
        exact ⟨hzb, fun hS => hz0 ((hiff (hrt hzb)).1 hS)⟩
    rw [heq]
    refine ⟨(Metric.nonempty_ball.2 hr).prod
      (nonempty_ball_diff_countable 0 hr (countable_singleton 0)), ?_⟩
    exact (convex_ball _ _).isPreconnected.prod
      (isPreconnected_ball_diff_countable hG 0 r (countable_singleton 0))
  · intro O hO
    set C := connectedComponentIn (interior O ∩ Sᶜ) x
    have hCo : IsOpen C := (isOpen_interior.inter hSc.isOpen_compl).connectedComponentIn
    have hxC : x ∈ C := mem_connectedComponentIn ⟨mem_interior_iff_mem_nhds.2 hO, hx⟩
    have hCsub : C ⊆ interior O ∩ Sᶜ := connectedComponentIn_subset _ _
    have hCS : C ∩ Sᶜ = C := inter_eq_left.2 (hCsub.trans inter_subset_right)
    refine ⟨C, hCo, hxC, hCsub.trans (inter_subset_left.trans interior_subset), ?_, ?_⟩
    · rw [hCS]; exact ⟨x, hxC⟩
    · rw [hCS]; exact isPreconnected_connectedComponentIn

/-- `ex:following_example_skeletal_itemize`, second item: a tame knot in a `3`-manifold is
skeletal. A tame knot is read as a closed *locally flat* subset: every point of `S` has a chart
onto an open subset of `ℝ × ℝ²` carrying `S` to the axis `ℝ × {0}`. -/
theorem isSkeletal_of_tameKnot [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] {S : Set X}
    (hSc : IsClosed S)
    (hflat : ∀ x ∈ S, ∃ e : OpenPartialHomeomorph X (ℝ × EuclideanSpace ℝ (Fin 2)),
      x ∈ e.source ∧ ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0) :
    IsSkeletal S :=
  haveI : LocallyConnectedSpace X :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) X
  isSkeletal_of_locallyFlat (F := ℝ) (G := EuclideanSpace ℝ (Fin 2))
    (by rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]; norm_num) hSc hflat

/-- In `ℝ` the only skeletal subset is `∅`: dimension `> 1` is needed in the examples. -/
theorem eq_empty_of_isSkeletal_real {S : Set ℝ} (hS : IsSkeletal S) : S = ∅ := by
  by_contra hne
  obtain ⟨c, hc⟩ := nonempty_iff_ne_empty.2 hne
  obtain ⟨a, ha, haS⟩ := hS.dense.inter_open_nonempty (Ioo (c - 1) c) isOpen_Ioo
    (nonempty_Ioo.2 (by linarith))
  obtain ⟨b, hb, hbS⟩ := hS.dense.inter_open_nonempty (Ioo c (c + 1)) isOpen_Ioo
    (nonempty_Ioo.2 (by linarith))
  have h := hS.locallyConnectedIn (Ioo (c - 1) (c + 1)) isOpen_Ioo isPreconnected_Ioo
  have hsub := h.Icc_subset (a := a) (b := b) ⟨⟨ha.1, by linarith [ha.2]⟩, haS⟩
    ⟨⟨by linarith [hb.1], hb.2⟩, hbS⟩
  exact (hsub ⟨ha.2.le, hb.1.le⟩).2 hc

/-- The Euclidean core of the fourth item: in a finite-dimensional real normed space of
dimension `≥ 2`, the complement of a closed totally disconnected set is preconnected. -/
theorem isPreconnected_compl_of_isTotallyDisconnected {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (hE : 2 ≤ Module.finrank ℝ E) {K : Set E}
    (hK : IsClosed K) (hKt : IsTotallyDisconnected K) : IsPreconnected Kᶜ := by
  sorry -- SORRY(ex:following_example_skeletal_itemize): dimension theory. A closed totally
  -- disconnected subset of `ℝⁿ` is zero-dimensional (locally compact), and a subset of dimension
  -- `≤ n - 2` does not separate `ℝⁿ` (Hurewicz–Wallman, *Dimension Theory*, Thm IV 4; or
  -- Alexander duality / Borsuk's separation theorem). Neither covering dimension nor
  -- separation theorems are in mathlib at this pin, and mathlib's countable-complement trick
  -- (`Set.Countable.isPathConnected_compl_of_one_lt_rank`) does not reach uncountable `K`.

/-- `ex:following_example_skeletal_itemize`, fourth item (tame or wild): a closed totally
disconnected subset — e.g. a Cantor set, however (wildly) embedded — of a manifold of dimension
`≥ 2` is skeletal. Modulo the Euclidean core `isPreconnected_compl_of_isTotallyDisconnected`. -/
theorem isSkeletal_of_isTotallyDisconnected {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (hE : 2 ≤ Module.finrank ℝ E) [ChartedSpace E X] {S : Set X}
    (hSc : IsClosed S) (hSt : IsTotallyDisconnected S) : IsSkeletal S := by
  have : Nontrivial E := (Module.finrank_pos_iff (R := ℝ)).1 (by omega)
  refine isSkeletal_of_local hSc fun x => exists_nhds_of_chart (chartAt E x)
    (mem_chart_source E x) fun r hr hrt => ?_
  set e := chartAt E x
  set h := OpenPartialHomeomorph.univBall (e x) r
  have hsrc : h.source = univ := OpenPartialHomeomorph.univBall_source _ _
  have htgt : h.target = Metric.ball (e x) r := OpenPartialHomeomorph.univBall_target _ hr
  have hinj : Function.Injective h := fun y z hyz =>
    h.injOn (by rw [hsrc]; trivial) (by rw [hsrc]; trivial) hyz
  have hcont : Continuous h := by
    rw [← continuousOn_univ, ← hsrc]; exact h.continuousOn
  have hmaps : ∀ z, h z ∈ Metric.ball (e x) r := fun z => htgt ▸ h.map_source (hsrc ▸ trivial)
  set g : E → X := fun z => e.symm (h z)
  have hgc : Continuous g :=
    e.continuousOn_symm.comp_continuous hcont fun z => hrt (hmaps z)
  have hginj : Function.Injective g := fun y z hyz =>
    hinj (e.symm.injOn (hrt (hmaps y)) (hrt (hmaps z)) hyz)
  set K := g ⁻¹' S
  have hKc : IsClosed K := hSc.preimage hgc
  have hKt : IsTotallyDisconnected K := fun P hPK hPc =>
    subsingleton_of_image hginj P (hSt _ (image_subset_iff.2 hPK) (hPc.image _ hgc.continuousOn))
  have himg : h '' Kᶜ = Metric.ball (e x) r ∩ e.symm ⁻¹' Sᶜ := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨hmaps y, hy⟩
    · rintro ⟨hzb, hzS⟩
      refine ⟨h.symm z, ?_, h.right_inv (htgt ▸ hzb)⟩
      show g (h.symm z) ∉ S
      simp only [g, h.right_inv (htgt ▸ hzb)]; exact hzS
  rw [← himg]
  refine ⟨Nonempty.image _ ?_, (isPreconnected_compl_of_isTotallyDisconnected hE hKc hKt).image _
    hcont.continuousOn⟩
  by_contra hne
  rw [not_nonempty_iff_eq_empty, compl_empty_iff] at hne
  obtain ⟨y, z, hyz⟩ := exists_pair_ne E
  exact hyz (hKt univ hne.symm.subset isPreconnected_univ (mem_univ y) (mem_univ z))

/-! ### The simplicial item: a counterexample and the corrected statement -/

section Simplicial

open Geometry

/-- A geometric simplicial complex is *pure of dimension `n`* if every face has at most `n + 1`
vertices and lies in a face with exactly `n + 1` vertices. -/
def IsPureOfDim {E : Type*} [AddCommGroup E] [Module ℝ E] (K : SimplicialComplex ℝ E) (n : ℕ) :
    Prop :=
  (∀ s ∈ K.faces, s.card ≤ n + 1) ∧ ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = n + 1

/-- The underlying set of the `k`-skeleton of `K`: the union of its faces of dimension `≤ k`. -/
def skeletonSpace {E : Type*} [AddCommGroup E] [Module ℝ E] (K : SimplicialComplex ℝ E)
    (k : ℕ) : Set E :=
  ⋃ s ∈ K.faces, ⋃ (_ : s.card ≤ k + 1), convexHull ℝ (s : Set E)

open Classical in
/-- The first triangle of the bow-tie, with vertices `0`, `(1,1)`, `(1,-1)`. -/
def bowtieA : Finset (ℝ × ℝ) := {0, (1, 1), (1, -1)}

open Classical in
/-- The second triangle of the bow-tie, with vertices `0`, `(-1,1)`, `(-1,-1)`. -/
def bowtieB : Finset (ℝ × ℝ) := {0, (-1, 1), (-1, -1)}

/-- The right closed cone `{|y| ≤ x}`. -/
def coneR : Set (ℝ × ℝ) := {p | p.2 ≤ p.1 ∧ -p.2 ≤ p.1}

/-- The left closed cone `{|y| ≤ -x}`. -/
def coneL : Set (ℝ × ℝ) := {p | p.2 ≤ -p.1 ∧ -p.2 ≤ -p.1}

theorem convex_coneR : Convex ℝ coneR := by
  intro x hx y hy a b ha hb hab
  simp only [coneR, mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] at *
  constructor <;> nlinarith [hx.1, hx.2, hy.1, hy.2]

theorem convex_coneL : Convex ℝ coneL := by
  intro x hx y hy a b ha hb hab
  simp only [coneL, mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] at *
  constructor <;> nlinarith [hx.1, hx.2, hy.1, hy.2]

theorem convexHull_bowtieA_subset : convexHull ℝ (bowtieA : Set (ℝ × ℝ)) ⊆ coneR := by
  refine convexHull_min ?_ convex_coneR
  intro p hp
  simp only [bowtieA, Finset.coe_insert, Finset.coe_singleton, mem_insert_iff,
    mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl <;> simp [coneR]

theorem convexHull_bowtieB_subset : convexHull ℝ (bowtieB : Set (ℝ × ℝ)) ⊆ coneL := by
  refine convexHull_min ?_ convex_coneL
  intro p hp
  simp only [bowtieB, Finset.coe_insert, Finset.coe_singleton, mem_insert_iff,
    mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl <;> simp [coneL]

theorem convexHull_fst_eq {s : Set (ℝ × ℝ)} {c : ℝ} (h : ∀ p ∈ s, p.1 = c) :
    ∀ x ∈ convexHull ℝ s, x.1 = c := by
  have hconv : Convex ℝ {p : ℝ × ℝ | p.1 = c} := by
    intro x hx y hy a b ha hb hab
    simp only [mem_setOf_eq, Prod.fst_add, Prod.smul_fst, smul_eq_mul] at *
    rw [hx, hy, ← add_mul, hab, one_mul]
  exact fun x hx => convexHull_min h hconv hx

theorem affineIndependent_triangle {a b : ℝ × ℝ}
    (h : ¬ ∃ r : ℝ, b = r • a) (ha : a ≠ 0) :
    AffineIndependent ℝ ((↑) : (({0, a, b} : Set (ℝ × ℝ))) → ℝ × ℝ) := by
  have h3 : AffineIndependent ℝ ![(0 : ℝ × ℝ), a, b] := by
    rw [affineIndependent_iff_not_collinear_set]
    intro hc
    rw [collinear_iff_of_mem (p₀ := (0 : ℝ × ℝ)) (by simp)] at hc
    obtain ⟨v, hv⟩ := hc
    obtain ⟨r, hr⟩ := hv a (by simp)
    obtain ⟨t, ht⟩ := hv b (by simp)
    simp only [vadd_eq_add, add_zero] at hr ht
    have hr0 : r ≠ 0 := by rintro rfl; simp at hr; exact ha hr
    exact h ⟨t / r, by rw [ht, hr, smul_smul, div_mul_cancel₀ t hr0]⟩
  have hr : range ![(0 : ℝ × ℝ), a, b] = {0, a, b} := by
    simp_rw [Matrix.range_cons, Matrix.range_empty, Set.singleton_union, insert_empty_eq]
  have := h3.range
  rw [hr] at this
  exact this

theorem coe_bowtieA : (bowtieA : Set (ℝ × ℝ)) = {0, (1, 1), (1, -1)} := by
  simp [bowtieA]

theorem coe_bowtieB : (bowtieB : Set (ℝ × ℝ)) = {0, (-1, 1), (-1, -1)} := by
  simp [bowtieB]

theorem affineIndependent_bowtieA :
    AffineIndependent ℝ (Subtype.val : ↥(bowtieA : Set (ℝ × ℝ)) → ℝ × ℝ) := by
  rw [coe_bowtieA]
  refine affineIndependent_triangle ?_ (by simp [Prod.ext_iff])
  rintro ⟨r, hr⟩
  simp only [Prod.ext_iff, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_one] at hr
  linarith [hr.1, hr.2]

theorem affineIndependent_bowtieB :
    AffineIndependent ℝ (Subtype.val : ↥(bowtieB : Set (ℝ × ℝ)) → ℝ × ℝ) := by
  rw [coe_bowtieB]
  refine affineIndependent_triangle ?_ (by simp [Prod.ext_iff])
  rintro ⟨r, hr⟩
  simp only [Prod.ext_iff, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_one, mul_neg] at hr
  linarith [hr.1, hr.2]

theorem zero_mem_of_subset_bowtieA {s : Finset (ℝ × ℝ)} (hs : s ⊆ bowtieA)
    (h0 : (0 : ℝ × ℝ) ∈ convexHull ℝ (s : Set (ℝ × ℝ))) : (0 : ℝ × ℝ) ∈ s := by
  by_contra hn
  have h1 : ∀ p ∈ (s : Set (ℝ × ℝ)), p.1 = 1 := by
    intro p hp
    have := hs hp
    simp only [bowtieA, Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with rfl | rfl | rfl
    · exact absurd hp hn
    · rfl
    · rfl
  have := convexHull_fst_eq h1 0 h0
  norm_num at this

theorem zero_mem_of_subset_bowtieB {s : Finset (ℝ × ℝ)} (hs : s ⊆ bowtieB)
    (h0 : (0 : ℝ × ℝ) ∈ convexHull ℝ (s : Set (ℝ × ℝ))) : (0 : ℝ × ℝ) ∈ s := by
  by_contra hn
  have h1 : ∀ p ∈ (s : Set (ℝ × ℝ)), p.1 = -1 := by
    intro p hp
    have := hs hp
    simp only [bowtieB, Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with rfl | rfl | rfl
    · exact absurd hp hn
    · rfl
    · rfl
  have := convexHull_fst_eq h1 0 h0
  norm_num at this

theorem eq_zero_of_mem_coneR_coneL {p : ℝ × ℝ} (h1 : p ∈ coneR) (h2 : p ∈ coneL) : p = 0 := by
  simp only [coneR, coneL, mem_setOf_eq] at h1 h2
  ext <;> simp <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem bowtie_cross {s t : Finset (ℝ × ℝ)} (hs : s ⊆ bowtieA) (ht : t ⊆ bowtieB) :
    convexHull ℝ (s : Set (ℝ × ℝ)) ∩ convexHull ℝ (t : Set (ℝ × ℝ)) ⊆
      convexHull ℝ ((s : Set (ℝ × ℝ)) ∩ t) := by
  rintro x ⟨hx1, hx2⟩
  have hx0 : x = 0 := eq_zero_of_mem_coneR_coneL
    (convexHull_bowtieA_subset (convexHull_mono (Finset.coe_subset.2 hs) hx1))
    (convexHull_bowtieB_subset (convexHull_mono (Finset.coe_subset.2 ht) hx2))
  subst hx0
  exact subset_convexHull ℝ _
    ⟨zero_mem_of_subset_bowtieA hs hx1, zero_mem_of_subset_bowtieB ht hx2⟩

/-- The *bow-tie*: the pure `2`-dimensional simplicial complex of `ℝ²` made of two triangles
meeting at the single vertex `0`. -/
def bowtie : SimplicialComplex ℝ (ℝ × ℝ) where
  faces := {s | s.Nonempty ∧ (s ⊆ bowtieA ∨ s ⊆ bowtieB)}
  isRelLowerSet_faces := fun _ ha => ⟨ha.1, fun _ hba hb =>
    ⟨hb, ha.2.imp (fun h => hba.trans h) (fun h => hba.trans h)⟩⟩
  indep := by
    rintro s ⟨-, hs | hs⟩
    · exact affineIndependent_bowtieA.mono (Finset.coe_subset.2 hs)
    · exact affineIndependent_bowtieB.mono (Finset.coe_subset.2 hs)
  inter_subset_convexHull := by
    rintro s t ⟨-, hs | hs⟩ ⟨-, ht | ht⟩
    · exact (affineIndependent_bowtieA.convexHull_inter hs ht).symm.subset
    · exact bowtie_cross hs ht
    · rw [inter_comm, inter_comm (s : Set (ℝ × ℝ))]; exact bowtie_cross ht hs
    · exact (affineIndependent_bowtieB.convexHull_inter hs ht).symm.subset

theorem card_bowtieA : bowtieA.card = 3 := by
  classical
  rw [bowtieA]
  convert Finset.card_insert_of_notMem (s := {((1 : ℝ), (1 : ℝ)), ((1 : ℝ), (-1 : ℝ))})
    (a := (0 : ℝ × ℝ)) (by simp [Prod.ext_iff]) using 2
  rw [Finset.card_pair (by simp [Prod.ext_iff]; norm_num)]

theorem card_bowtieB : bowtieB.card = 3 := by
  classical
  rw [bowtieB]
  convert Finset.card_insert_of_notMem (s := {((-1 : ℝ), (1 : ℝ)), ((-1 : ℝ), (-1 : ℝ))})
    (a := (0 : ℝ × ℝ)) (by simp [Prod.ext_iff]) using 2
  rw [Finset.card_pair (by simp [Prod.ext_iff]; norm_num)]

theorem bowtieA_mem_faces : bowtieA ∈ bowtie.faces :=
  ⟨⟨0, by simp [bowtieA]⟩, Or.inl subset_rfl⟩

theorem bowtieB_mem_faces : bowtieB ∈ bowtie.faces :=
  ⟨⟨0, by simp [bowtieB]⟩, Or.inr subset_rfl⟩

/-- The bow-tie is pure of dimension `2`. -/
theorem isPureOfDim_bowtie : IsPureOfDim bowtie 2 := by
  refine ⟨?_, ?_⟩
  · rintro s ⟨-, hs | hs⟩
    · exact (Finset.card_le_card hs).trans card_bowtieA.le
    · exact (Finset.card_le_card hs).trans card_bowtieB.le
  · rintro s ⟨-, hs | hs⟩
    · exact ⟨bowtieA, bowtieA_mem_faces, hs, card_bowtieA⟩
    · exact ⟨bowtieB, bowtieB_mem_faces, hs, card_bowtieB⟩

theorem bowtie_faces_finite : bowtie.faces.Finite := by
  classical
  refine (bowtieA.powerset ∪ bowtieB.powerset).finite_toSet.subset ?_
  rintro s ⟨-, hs | hs⟩
  · simp [hs]
  · simp [hs]

theorem bowtie_space : bowtie.space = convexHull ℝ (bowtieA : Set (ℝ × ℝ)) ∪
    convexHull ℝ (bowtieB : Set (ℝ × ℝ)) := by
  ext x
  rw [SimplicialComplex.mem_space_iff]
  constructor
  · rintro ⟨s, ⟨-, hs | hs⟩, hx⟩
    · exact Or.inl (convexHull_mono (Finset.coe_subset.2 hs) hx)
    · exact Or.inr (convexHull_mono (Finset.coe_subset.2 hs) hx)
  · rintro (hx | hx)
    · exact ⟨bowtieA, bowtieA_mem_faces, hx⟩
    · exact ⟨bowtieB, bowtieB_mem_faces, hx⟩

theorem skeletonSpace_bowtie_subset :
    skeletonSpace bowtie 0 ⊆ (bowtieA : Set (ℝ × ℝ)) ∪ bowtieB := by
  intro x hx
  simp only [skeletonSpace, mem_iUnion, exists_prop] at hx
  obtain ⟨s, ⟨hne, hs⟩, hcard, hx⟩ := hx
  obtain ⟨v, rfl⟩ := Finset.card_eq_one.1 (le_antisymm hcard (Finset.card_pos.2 hne))
  rw [Finset.coe_singleton, convexHull_singleton, mem_singleton_iff] at hx
  subst hx
  rcases hs with hs | hs
  · exact Or.inl (Finset.coe_subset.2 hs (by simp))
  · exact Or.inr (Finset.coe_subset.2 hs (by simp))

theorem zero_mem_skeletonSpace_bowtie : (0 : ℝ × ℝ) ∈ skeletonSpace bowtie 0 := by
  simp only [skeletonSpace, mem_iUnion, exists_prop]
  refine ⟨{0}, ⟨⟨0, by simp⟩, Or.inl (by simp [bowtieA])⟩, by simp, by simp⟩

theorem mem_convexHull_bowtieA_of {c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) :
    ((c, 0) : ℝ × ℝ) ∈ convexHull ℝ (bowtieA : Set (ℝ × ℝ)) := by
  have hm : ((1 : ℝ) / 2) • ((1 : ℝ), (1 : ℝ)) + ((1 : ℝ) / 2) • ((1 : ℝ), (-1 : ℝ)) ∈
      convexHull ℝ (bowtieA : Set (ℝ × ℝ)) :=
    convex_convexHull ℝ _ (subset_convexHull ℝ _ (by simp [coe_bowtieA]))
      (subset_convexHull ℝ _ (by simp [coe_bowtieA])) (by norm_num) (by norm_num) (by norm_num)
  have hq := convex_convexHull ℝ (bowtieA : Set (ℝ × ℝ))
    (subset_convexHull ℝ _ (by simp [coe_bowtieA] : (0 : ℝ × ℝ) ∈ (bowtieA : Set (ℝ × ℝ))))
    hm (by linarith : 0 ≤ 1 - c) h0 (by ring)
  convert hq using 1
  ext
  · simp; ring
  · simp

theorem mem_convexHull_bowtieB_of {c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) :
    ((-c, 0) : ℝ × ℝ) ∈ convexHull ℝ (bowtieB : Set (ℝ × ℝ)) := by
  have hm : ((1 : ℝ) / 2) • ((-1 : ℝ), (1 : ℝ)) + ((1 : ℝ) / 2) • ((-1 : ℝ), (-1 : ℝ)) ∈
      convexHull ℝ (bowtieB : Set (ℝ × ℝ)) :=
    convex_convexHull ℝ _ (subset_convexHull ℝ _ (by simp [coe_bowtieB]))
      (subset_convexHull ℝ _ (by simp [coe_bowtieB])) (by norm_num) (by norm_num) (by norm_num)
  have hq := convex_convexHull ℝ (bowtieB : Set (ℝ × ℝ))
    (subset_convexHull ℝ _ (by simp [coe_bowtieB] : (0 : ℝ × ℝ) ∈ (bowtieB : Set (ℝ × ℝ))))
    hm (by linarith : 0 ≤ 1 - c) h0 (by ring)
  convert hq using 1
  ext
  · simp; ring
  · simp

/-- **Counterexample to the third item of `ex:following_example_skeletal_itemize`** as written.
The bow-tie is a (finite) pure `2`-dimensional simplicial complex, and its `0`-skeleton
(`0 ≤ 2 - 2`) is *not* skeletal in it: a small open star of the common vertex is connected, but
removing the vertex disconnects it. -/
theorem bowtie_counterexample :
    IsPureOfDim bowtie 2 ∧ bowtie.faces.Finite ∧
      ¬ IsSkeletal (((↑) : bowtie.space → ℝ × ℝ) ⁻¹' skeletonSpace bowtie 0) := by
  refine ⟨isPureOfDim_bowtie, bowtie_faces_finite, fun h => ?_⟩
  set strip : Set (ℝ × ℝ) := {p | |p.1| < 1 / 2}
  have hstrip_open : IsOpen strip := isOpen_lt (continuous_abs.comp continuous_fst)
    continuous_const
  have hstrip_conv : Convex ℝ strip := by
    have : strip = {p : ℝ × ℝ | -(1 / 2) < p.1} ∩ {p | p.1 < 1 / 2} := by
      ext p; simp [strip, abs_lt]
    rw [this]
    exact (convex_halfSpace_gt (LinearMap.fst ℝ ℝ ℝ).isLinear _).inter
      (convex_halfSpace_lt (LinearMap.fst ℝ ℝ ℝ).isLinear _)
  set W : Set bowtie.space := ((↑) : bowtie.space → ℝ × ℝ) ⁻¹' strip
  have hWo : IsOpen W := hstrip_open.preimage continuous_subtype_val
  have h0s : (0 : ℝ × ℝ) ∈ strip := by simp [strip]
  have hWc : IsPreconnected W := by
    rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, Subtype.image_preimage_coe,
      bowtie_space, union_inter_distrib_right]
    exact IsPreconnected.union 0
      ⟨subset_convexHull ℝ _ (by simp [coe_bowtieA]), h0s⟩
      ⟨subset_convexHull ℝ _ (by simp [coe_bowtieB]), h0s⟩
      ((convex_convexHull ℝ _).inter hstrip_conv).isPreconnected
      ((convex_convexHull ℝ _).inter hstrip_conv).isPreconnected
  have hZ := (h.locallyConnectedIn W hWo hWc).image _ continuous_subtype_val.continuousOn
  set Z := ((↑) : bowtie.space → ℝ × ℝ) '' (W ∩ (((↑) : bowtie.space → ℝ × ℝ) ⁻¹'
    skeletonSpace bowtie 0)ᶜ)
  have hnotvert : ∀ c : ℝ, c ≠ 0 → |c| < 1 / 2 → ((c, 0) : ℝ × ℝ) ∉ skeletonSpace bowtie 0 := by
    intro c hc hc' hmem
    have := skeletonSpace_bowtie_subset hmem
    rw [abs_lt] at hc'
    simp only [coe_bowtieA, coe_bowtieB, mem_union, mem_insert_iff, mem_singleton_iff,
      Prod.ext_iff, Prod.fst_zero, Prod.snd_zero] at this
    rcases this with ((h | h | h) | (h | h | h)) <;>
      first | exact hc h.1 | (linarith [h.1, hc'.1, hc'.2])
  have hp : ((1 / 4 : ℝ), (0 : ℝ)) ∈ Z := by
    have hsp : ((1 / 4 : ℝ), (0 : ℝ)) ∈ bowtie.space := by
      rw [bowtie_space]; exact Or.inl (mem_convexHull_bowtieA_of (by norm_num) (by norm_num))
    refine ⟨⟨_, hsp⟩, ⟨?_, ?_⟩, rfl⟩
    · show |(1 / 4 : ℝ)| < 1 / 2
      rw [abs_of_pos (by norm_num)]; norm_num
    · exact hnotvert _ (by norm_num) (by rw [abs_of_pos (by norm_num)]; norm_num)
  have hq : ((-(1 / 4) : ℝ), (0 : ℝ)) ∈ Z := by
    have hsp : ((-(1 / 4) : ℝ), (0 : ℝ)) ∈ bowtie.space := by
      rw [bowtie_space]; exact Or.inr (mem_convexHull_bowtieB_of (by norm_num) (by norm_num))
    refine ⟨⟨_, hsp⟩, ⟨?_, ?_⟩, rfl⟩
    · show |(-(1 / 4) : ℝ)| < 1 / 2
      rw [abs_neg, abs_of_pos (by norm_num)]; norm_num
    · exact hnotvert _ (by norm_num) (by rw [abs_neg, abs_of_pos (by norm_num)]; norm_num)
  have hsplit : Z ⊆ {p : ℝ × ℝ | 0 < p.1} ∪ {p | p.1 < 0} := by
    rintro _ ⟨⟨z, hz⟩, ⟨-, hzs⟩, rfl⟩
    simp only [mem_union, mem_setOf_eq]
    rcases lt_trichotomy z.1 0 with h1 | h1 | h1
    · exact Or.inr h1
    · exfalso
      have hz0 : z = 0 := by
        rw [bowtie_space] at hz
        rcases hz with hz | hz
        · have := convexHull_bowtieA_subset hz
          simp only [coneR, mem_setOf_eq] at this
          ext
          · exact h1
          · simp only [Prod.snd_zero]; linarith [this.1, this.2]
        · have := convexHull_bowtieB_subset hz
          simp only [coneL, mem_setOf_eq] at this
          ext
          · exact h1
          · simp only [Prod.snd_zero]; linarith [this.1, this.2]
      subst hz0
      exact hzs zero_mem_skeletonSpace_bowtie
    · exact Or.inl h1
  obtain ⟨w, -, hw1, hw2⟩ := hZ _ _ (isOpen_lt continuous_const continuous_fst)
    (isOpen_lt continuous_fst continuous_const) hsplit ⟨_, hp, by norm_num⟩
    ⟨_, hq, by norm_num⟩
  simp only [mem_setOf_eq] at hw1 hw2
  linarith

theorem skeletonSpace_mono {E : Type*} [AddCommGroup E] [Module ℝ E]
    (K : SimplicialComplex ℝ E) {k k' : ℕ} (h : k ≤ k') :
    skeletonSpace K k ⊆ skeletonSpace K k' := by
  intro x hx
  simp only [skeletonSpace, mem_iUnion, exists_prop] at hx ⊢
  obtain ⟨s, hs, hc, hx⟩ := hx
  exact ⟨s, hs, by omega, hx⟩

theorem isClosed_skeletonSpace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : SimplicialComplex ℝ E) (hfin : K.faces.Finite) (k : ℕ) :
    IsClosed (skeletonSpace K k) := by
  have : skeletonSpace K k = ⋃ s ∈ {s ∈ K.faces | s.card ≤ k + 1}, convexHull ℝ (s : Set E) := by
    ext x
    simp only [skeletonSpace, mem_iUnion, exists_prop, mem_sep_iff, and_assoc]
  rw [this]
  exact (hfin.subset (sep_subset _ _)).isClosed_biUnion fun s _ =>
    (Set.Finite.isCompact_convexHull ℝ s.finite_toSet).isClosed

/-- *Local strong connectivity* in codimension `≥ 2`: for every face `σ` of dimension `≤ n - 2`,
any two `n`-faces containing `σ` are joined by a chain of `n`-faces containing `σ`, consecutive
ones sharing an `(n-1)`-face. This is the hypothesis the third item of
`ex:following_example_skeletal_itemize` omits; the bow-tie violates it at its centre. -/
def IsLocallyStronglyConnected {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (n : ℕ) : Prop :=
  ∀ σ ∈ K.faces, σ.card + 1 ≤ n → ∀ τ ∈ K.faces, ∀ τ' ∈ K.faces, σ ⊆ τ → σ ⊆ τ' →
    τ.card = n + 1 → τ'.card = n + 1 →
    Relation.ReflTransGen (fun τ₁ τ₂ : Finset E => τ₁ ∈ K.faces ∧ τ₂ ∈ K.faces ∧
      τ₁.card = n + 1 ∧ τ₂.card = n + 1 ∧ σ ⊆ τ₁ ∩ τ₂ ∧ (τ₁ ∩ τ₂).card = n) τ τ'

/-- Corrected third item of `ex:following_example_skeletal_itemize`, codimension-two case: in a
finite pure `n`-dimensional simplicial complex which is locally strongly connected in codimension
`≥ 2`, the `(n-2)`-skeleton is skeletal. -/
theorem isSkeletal_skeletonSpace_codim_two {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] (K : SimplicialComplex ℝ E) (hfin : K.faces.Finite) {n : ℕ}
    (hpure : IsPureOfDim K n) (hlsc : IsLocallyStronglyConnected K n) (hn : 2 ≤ n) :
    IsSkeletal (((↑) : K.space → E) ⁻¹' skeletonSpace K (n - 2)) := by
  sorry -- SORRY(ex:following_example_skeletal_itemize): needs the local structure theory of
  -- geometric simplicial complexes, absent from mathlib: the carrier (open simplex) of a point,
  -- the open star of a face as a neighbourhood basis in `K.space`, the star of a point as the
  -- cone on its link, connectedness of an open simplex together with its open codimension-one
  -- faces, and the general-position step that a path in the star avoiding the `(n-2)`-skeleton
  -- crosses facets only through open `(n-1)`-faces. With these, local strong connectivity is
  -- exactly connectedness of `star(x) \ skeleton` and `isSkeletal_of_local` concludes.

/-- Corrected third item of `ex:following_example_skeletal_itemize`: for `k ≤ n - 2`, the
`k`-skeleton of a finite pure `n`-dimensional, locally strongly connected simplicial complex is
skeletal. Reduced to the codimension-two case by `IsSkeletal.anti`. -/
theorem isSkeletal_skeletonSpace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] (K : SimplicialComplex ℝ E) (hfin : K.faces.Finite) {n k : ℕ}
    (hpure : IsPureOfDim K n) (hlsc : IsLocallyStronglyConnected K n) (hk : k + 2 ≤ n) :
    IsSkeletal (((↑) : K.space → E) ⁻¹' skeletonSpace K k) :=
  (isSkeletal_skeletonSpace_codim_two K hfin hpure hlsc (by omega)).anti
    (preimage_mono (skeletonSpace_mono K (by omega)))
    ((isClosed_skeletonSpace K hfin k).preimage continuous_subtype_val)

/-- The bow-tie is not locally strongly connected: the two triangles share only the vertex `0`.
So `bowtie_counterexample` is consistent with `isSkeletal_skeletonSpace`. -/
theorem not_isLocallyStronglyConnected_bowtie : ¬ IsLocallyStronglyConnected bowtie 2 := by
  intro h
  have h0 : ({0} : Finset (ℝ × ℝ)) ∈ bowtie.faces := ⟨⟨0, by simp⟩, Or.inl (by simp [bowtieA])⟩
  have hchain := h {0} h0 (by simp) bowtieA bowtieA_mem_faces bowtieB bowtieB_mem_faces
    (by simp [bowtieA]) (by simp [bowtieB]) card_bowtieA card_bowtieB
  -- every face of the chain stays inside `bowtieA`
  have hAB : bowtieA ∩ bowtieB = {0} := by
    ext p
    simp only [bowtieA, bowtieB, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
      Prod.ext_iff, Prod.fst_zero, Prod.snd_zero]
    constructor
    · rintro ⟨h1 | h1 | h1, h2 | h2 | h2⟩ <;> first | exact h1 | exact h2 |
        (exfalso; linarith [h1.1, h2.1])
    · intro hp; exact ⟨Or.inl hp, Or.inl hp⟩
  have key : ∀ τ, Relation.ReflTransGen (fun τ₁ τ₂ : Finset (ℝ × ℝ) => τ₁ ∈ bowtie.faces ∧
      τ₂ ∈ bowtie.faces ∧ τ₁.card = 2 + 1 ∧ τ₂.card = 2 + 1 ∧ {0} ⊆ τ₁ ∩ τ₂ ∧
        (τ₁ ∩ τ₂).card = 2) bowtieA τ → τ ⊆ bowtieA := by
    intro τ hτ
    induction hτ with
    | refl => exact subset_rfl
    | tail _ hstep ih =>
      obtain ⟨-, ⟨-, h2 | h2⟩, -, -, -, hcard⟩ := hstep
      · exact h2
      · exfalso
        have hsub : _ ⊆ bowtieA ∩ bowtieB := Finset.inter_subset_inter ih h2
        rw [hAB] at hsub
        have := Finset.card_le_card hsub
        rw [hcard, Finset.card_singleton] at this
        omega
  have hBA := key _ hchain
  have : ((-1 : ℝ), (1 : ℝ)) ∈ bowtieA := hBA (by simp [bowtieB])
  simp only [bowtieA, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff, Prod.fst_zero,
    Prod.snd_zero] at this
  rcases this with h | h | h <;> linarith [h.1, h.2]

end Simplicial

end GX
