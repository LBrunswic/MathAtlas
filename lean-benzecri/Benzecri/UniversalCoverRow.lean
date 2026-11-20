import Benzecri.Port.UniversalCover
import Benzecri.Structure.Classes
import Benzecri.Structure.Developing
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# `Benzecri.UniversalCoverRow` — the universal cover of a compact locally projective manifold is divisible (p. 238)

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 1 § 1, journal p. 238; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch1.tex`. Roadmap target `T-bz-universal-cover`
(closes the last open row of Chapter 1).

* **`bzthm:c1s1_revetement_universel_divisible`** — `benzecri1960_ch1.tex:431` (l.431–434,
  p. 238): **if `V` is a compact locally projective manifold, its universal cover is divisible**
  (`revetement_universel_divisible_proj`): the universal cover `UniversalCover V v₀` (ported,
  `Benzecri.Port.UniversalCover`) is a simply connected covering of `V`, locally projective
  with the pulled-back charts (`UniversalCover.instChartedSpaceProj`, `instHasGroupoidProj`), the
  projection is a projective morphism, and `IsDivisible (GSR n) (S n) (UniversalCover V v₀)`
  (Déf. 15, strict library): its deck group `deckAut` is a subgroup of the projective automorphisms,
  properly discontinuous, without fixed point, with compact quotient. The affine case (p. 238,
  « en remplaçant $S(n)$ par $\R^n$ »): `revetement_universel_divisible_aff`. For EVERY simply
  connected covering `N → V` (« son revêtement universel » up to isomorphism, see
  `UniversalCover.exists_homeomorph_of_simplyConnected`) with the pulled-back structure:
  `isDivisible_of_isCoveringMap_proj`, `_aff`; for any `(G,X)` and any structure on `N` making the
  covering a morphism: `isDivisible_of_isCoveringMap`; for the universal cover of any compact
  Hausdorff, locally path-connected, semilocally simply connected `(G,X)`-manifold:
  `UniversalCover.isDivisible`.

> Dans la suite, nous étudierons les ouverts étalés $W$ au-dessus de $S(n)$, qui sont homogènes,
> divisibles ou balayables. Si $V$ est une variété localement projective et compacte, son
> revêtement universel est divisible.

(The paper gives no proof. The one formalized is the classical one: `G₁` is the deck group.)

What the proof needs, all proved here (none is a hypothesis):
* **a manifold is semilocally simply connected**: `semilocallySimplyConnected_of_proj`, `_aff`, from
  `semilocallySimplyConnected_of_forall_openPartialHomeomorph` (a chart ball is convex, hence
  contractible; `S(n)` is charted through `S.homeomorphEuclideanSphere` and Mathlib's
  stereographic charts), so the universal cover exists;
* **deck transformations are automorphisms** of the structure (`IsGXMorphism.of_comp_eq`,
  `deckAut.ofHomeomorph`);
* **« sans point fixe »**: `deckAut.eq_of_smul_eq`, `deckAut.isCancelSMul` (uniqueness of lifts);
* **« proprement discontinu »** (Mathlib's sense, DEC-120): `deckAut.properlyDiscontinuousSMul`,
  through the local step `exists_nhds_eq_of_comp_eq` (base Hausdorff and locally connected);
* **« $V/G_1$ compact »**: `deckAut.compactSpace_quotient`, from deck transitivity on the fibres
  (`exists_homeomorph_comp_eq_of_simplyConnected`, `deckAut.comp_eq_iff`: a simply connected
  covering is « galoisien ») and a compact set meeting every fibre
  (`exists_isCompact_forall_exists_eq`, `isClosed_range_of_isCoveringMap`).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `V` « localement projective » | ✓ carried: `[ChartedSpace (S n) V] [HasGroupoid V (projGroupoid n)]` (README conventions); the bare `IsDivisible` forms (`isDivisible_of_isCoveringMap_proj`) do not even need `HasGroupoid` |
| `V` « compacte » | ✓ carried: `[CompactSpace V]` |
| `V` a « variété »: Hausdorff (plan F6) | ✓ carried: `[T2Space V]`, used for proper discontinuity (separating two fibres) and for local compactness of `V` |
| `V` a « variété »: connected (plan F6) | ⚠ weakened: not assumed. `UniversalCover V v₀` is then the universal cover of the path component of `v₀` (the fibres over other components are empty), and it is still divisible |
| `V` a « variété »: second countable (plan F6) | ⚠ weakened: not used |
| « son revêtement universel » | ✓ carried: `UniversalCover V v₀` with the pulled-back structure (the unique structure making the projection a morphism, `existsUnique_pullback`); covering (`isCoveringMap_proj`) and simply connected; any simply connected covering is homeomorphic to it over `V` (`exists_homeomorph_of_simplyConnected`), and is divisible too |
| « divisible » (Déf. 15: a subgroup of the projective automorphisms, properly discontinuous, without fixed point, compact quotient) | ✓ carried: the strict library's `IsDivisible`, witnessed by `deckAut (GSR n) (S n) (UniversalCover.proj V v₀)` |

## SCOPE (disclosed)

* « variété » is read Hausdorff (plan F6), as everywhere in the strict library (§ 3, Theorem A;
  Déf. 16 by DEC-122); connectedness and second countability are not needed. Not a finding: the
  paper's « variété » carries it.
* The universal cover is the ported construction (homotopy classes of paths from `v₀`), at a base
  point `v₀`; for a connected `V` the choice of `v₀` is immaterial up to isomorphism over `V`
  (`exists_homeomorph_of_simplyConnected`).
* `UniversalCover.instChartedSpaceProj` and `instChartedSpaceAff` are global instances on the
  package's own type `UniversalCover` (as `FCone.instChartedSpaceAff`, DEC-128).
* Not formalized (no label): the identification of `deckAut` with `π₁(V, v₀)` (available for the
  underlying homeomorphisms as `UniversalCover.deckEquiv`), and « si $R$ est galoisien, $V$ est le
  quotient de $R$ » beyond the fibres-are-orbits statement `deckAut.comp_eq_iff`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Universal cover ported
from `lean-causal/Causal/Port/UniversalCover.lean` at `82ee40f` (ported from
`lean-gx/GX/Topology/UniversalCover.lean` at `e5a1d46`).
-/
noncomputable section

open Set Filter Topology

namespace Benzecri

universe u v w y

/-! ### Coverings: four facts of general topology -/

section Covering

variable {N : Type*} [TopologicalSpace N] {M : Type*} [TopologicalSpace M] {π : N → M}

/-- **The range of a covering map is closed** (over a point outside the range the evenly covered
neighbourhood has an empty preimage). -/
theorem isClosed_range_of_isCoveringMap (hπ : IsCoveringMap π) : IsClosed (range π) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨-, U, hxU, hU, -, H, -⟩ := hπ x
  refine mem_of_superset (hU.mem_nhds hxU) fun z hz hzr => hx ?_
  obtain ⟨w, rfl⟩ := hzr
  obtain ⟨e, he⟩ := (H ⟨w, hz⟩).2
  exact ⟨e, he⟩

/-- **A compact set meeting every fibre over the range**: for a local homeomorphism `π` with
closed range into a compact Hausdorff space, some compact `K` has `π(K) ⊇ π(N)`. -/
theorem exists_isCompact_forall_exists_eq [CompactSpace M] [T2Space M]
    (hπ : IsLocalHomeomorph π) (hcl : IsClosed (range π)) :
    ∃ K : Set N, IsCompact K ∧ ∀ y : N, ∃ k ∈ K, π k = π y := by
  have hloc : ∀ z : N, ∃ C : Set N, IsCompact C ∧ π '' C ∈ 𝓝 (π z) := by
    intro z
    obtain ⟨e, hz, he⟩ := hπ z
    subst he
    obtain ⟨C', hC'n, hC't, hC'c⟩ := local_compact_nhds (e.open_target.mem_nhds (e.map_source hz))
    refine ⟨e.symm '' C', hC'c.image_of_continuousOn (e.continuousOn_symm.mono hC't),
      mem_of_superset hC'n fun c hc => ⟨e.symm c, ⟨c, hc, rfl⟩, e.right_inv (hC't hc)⟩⟩
  choose C hCc hCn using hloc
  have hcov : range π ⊆ ⋃ z, interior (π '' C z) := by
    rintro _ ⟨z, rfl⟩
    exact mem_iUnion.2 ⟨z, mem_interior_iff_mem_nhds.2 (hCn z)⟩
  obtain ⟨t, ht⟩ := hcl.isCompact.elim_finite_subcover (fun z => interior (π '' C z))
    (fun _ => isOpen_interior) hcov
  refine ⟨⋃ z ∈ t, C z, t.isCompact_biUnion fun z _ => hCc z, fun y => ?_⟩
  obtain ⟨z, hzt, hyz⟩ := mem_iUnion₂.1 (ht (mem_range_self y))
  obtain ⟨k, hk, hky⟩ := interior_subset hyz
  exact ⟨k, mem_iUnion₂.2 ⟨z, hzt, hk⟩, hky⟩

/-- **A simply connected covering is Galois**: any two points of a fibre are exchanged by a deck
homeomorphism (lift `π` through itself). -/
theorem exists_homeomorph_comp_eq_of_simplyConnected [SimplyConnectedSpace N]
    [LocPathConnectedSpace N] (hπ : IsCoveringMap π) {y k : N} (h : π y = π k) :
    ∃ φ : N ≃ₜ N, (∀ x, π (φ x) = π x) ∧ φ y = k := by
  obtain ⟨F, ⟨hF0, hF⟩, -⟩ :=
    hπ.existsUnique_continuousMap_lifts ⟨π, hπ.continuous⟩ y k h.symm
  obtain ⟨F', ⟨hF'0, hF'⟩, -⟩ :=
    hπ.existsUnique_continuousMap_lifts ⟨π, hπ.continuous⟩ k y h
  have hFx : ∀ x, π (F x) = π x := fun x => congrFun hF x
  have hF'x : ∀ x, π (F' x) = π x := fun x => congrFun hF' x
  have h1 : ∀ x, F' (F x) = x := by
    have := hπ.eq_of_comp_eq (F'.comp F).continuous continuous_id
      (funext fun x => (hF'x (F x)).trans (hFx x)) y (by
        change F' (F y) = y
        rw [hF0, hF'0])
    exact fun x => congrFun this x
  have h2 : ∀ x, F (F' x) = x := by
    have := hπ.eq_of_comp_eq (F.comp F').continuous continuous_id
      (funext fun x => (hFx (F' x)).trans (hF'x x)) k (by
        change F (F' k) = k
        rw [hF'0, hF0])
    exact fun x => congrFun this x
  exact ⟨⟨⟨F, F', h1, h2⟩, F.continuous, F'.continuous⟩, hFx, hF0⟩

/-- **The local step of proper discontinuity**: over a Hausdorff, locally connected base, every
pair `(k, l)` of points of a connected covering has a neighbourhood `U` such that at most one
continuous map over `π` sends the first coordinate of a point of `U` to its second. -/
theorem exists_nhds_eq_of_comp_eq [T2Space M] [LocallyConnectedSpace M] [PreconnectedSpace N]
    (hπ : IsCoveringMap π) (p : N × N) :
    ∃ U ∈ 𝓝 p, ∀ φ ψ : N → N, Continuous φ → Continuous ψ → (∀ x, π (φ x) = π x) →
      (∀ x, π (ψ x) = π x) → (∃ z ∈ U, φ z.1 = z.2) → (∃ z ∈ U, ψ z.1 = z.2) → φ = ψ := by
  obtain ⟨k, l⟩ := p
  by_cases hkl : π k = π l
  · -- `k` and `l` in one fibre: a connected neighbourhood `W` of `π k` inside two local sheets
    obtain ⟨ek, hk, hek⟩ := hπ.isLocalHomeomorph k
    obtain ⟨el, hl, hel⟩ := hπ.isLocalHomeomorph l
    have hvk : π k ∈ ek.target := by rw [hek]; exact ek.map_source hk
    have hvl : π k ∈ el.target := by rw [hkl, hel]; exact el.map_source hl
    obtain ⟨W, ⟨hWo, hvW, hWc⟩, hWsub⟩ :=
      (LocallyConnectedSpace.open_connected_basis (π k)).mem_iff.1
      (inter_mem (ek.open_target.mem_nhds hvk) (el.open_target.mem_nhds hvl))
    have hWk : ∀ w ∈ W, w ∈ ek.target := fun w hw => (hWsub hw).1
    have hWl : ∀ w ∈ W, w ∈ el.target := fun w hw => (hWsub hw).2
    set Nk : Set N := ek.source ∩ π ⁻¹' W with hNkdef
    set Nl : Set N := el.source ∩ π ⁻¹' W with hNldef
    have hNk : IsOpen Nk := ek.open_source.inter (hWo.preimage hπ.continuous)
    have hNl : IsOpen Nl := el.open_source.inter (hWo.preimage hπ.continuous)
    have hkN : k ∈ Nk := ⟨hk, hvW⟩
    have hlN : l ∈ Nl := ⟨hl, by rw [mem_preimage, ← hkl]; exact hvW⟩
    have hNkc : IsPreconnected Nk := by
      have : Nk = ek.symm '' W := by
        ext x
        constructor
        · rintro ⟨hx, hxW⟩
          refine ⟨ek x, ?_, ek.left_inv hx⟩
          rw [mem_preimage, hek] at hxW
          exact hxW
        · rintro ⟨w, hw, rfl⟩
          refine ⟨ek.map_target (hWk w hw), ?_⟩
          rw [mem_preimage, hek, ek.right_inv (hWk w hw)]
          exact hw
      rw [this]
      exact hWc.isPreconnected.image _ (ek.continuousOn_symm.mono hWk)
    haveI : PreconnectedSpace Nk := isPreconnected_iff_preconnectedSpace.1 hNkc
    -- a continuous map over `π` sending one point of `Nk` into `Nl` sends `k` to `l`
    have key : ∀ φ : N → N, Continuous φ → (∀ x, π (φ x) = π x) →
        (∃ z ∈ Nk ×ˢ Nl, φ z.1 = z.2) → φ k = l := by
      rintro φ hφc hφπ ⟨z, ⟨hz1, hz2⟩, hφz⟩
      have hσc : Continuous fun x : Nk => el.symm (π x) :=
        el.continuousOn_symm.comp_continuous (hπ.continuous.comp continuous_subtype_val)
          fun x => hWl _ x.2.2
      have hσ : ∀ x : Nk, π (el.symm (π x)) = π x := fun x => by
        have ht : π x ∈ el.target := hWl _ x.2.2
        rw [hel] at ht ⊢
        exact el.right_inv ht
      have hagree : φ z.1 = el.symm (π z.1) := by
        rw [hφz, ← hφπ z.1, hφz, hel, el.left_inv hz2.1]
      have heq := hπ.eq_of_comp_eq (A := Nk) (hφc.comp continuous_subtype_val) hσc
        (funext fun x => (hφπ x).trans (hσ x).symm) ⟨z.1, hz1⟩ hagree
      have hk' := congrFun heq ⟨k, hkN⟩
      change φ k = el.symm (π k) at hk'
      rw [hk', hkl, hel, el.left_inv hl]
    refine ⟨Nk ×ˢ Nl, prod_mem_nhds (hNk.mem_nhds hkN) (hNl.mem_nhds hlN),
      fun φ ψ hφ hψ hφπ hψπ hφz hψz => ?_⟩
    exact hπ.eq_of_comp_eq hφ hψ (funext fun x => (hφπ x).trans (hψπ x).symm) k
      ((key φ hφ hφπ hφz).trans (key ψ hψ hψπ hψz).symm)
  · -- different fibres: separate them
    obtain ⟨O, O', hO, hO', hkO, hlO', hdisj⟩ := t2_separation hkl
    refine ⟨(π ⁻¹' O) ×ˢ (π ⁻¹' O'),
      prod_mem_nhds (hπ.continuous.continuousAt.preimage_mem_nhds (hO.mem_nhds hkO))
        (hπ.continuous.continuousAt.preimage_mem_nhds (hO'.mem_nhds hlO')), ?_⟩
    rintro φ ψ - - hφπ - ⟨z, ⟨hz1, hz2⟩, hφz⟩ -
    exfalso
    have h1 : π z.2 ∈ O := by
      rw [← hφz, hφπ]
      exact hz1
    exact Set.disjoint_left.1 hdisj h1 hz2

end Covering

/-! ### Manifolds are semilocally simply connected -/

section Semilocal

/-- **A space locally homeomorphic to real normed spaces is semilocally simply connected**: a
chart ball is convex, hence contractible, so its preimage is simply connected. -/
theorem semilocallySimplyConnected_of_forall_openPartialHomeomorph {Y : Type*}
    [TopologicalSpace Y] {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (h : ∀ y : Y, ∃ e : OpenPartialHomeomorph Y H, y ∈ e.source) :
    SemilocallySimplyConnected Y := by
  intro y
  obtain ⟨e, hy⟩ := h y
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 e.open_target (e y) (e.map_source hy)
  set B : Set H := Metric.ball (e y) r with hB
  set U : Set Y := e.source ∩ e ⁻¹' B with hU
  have hyU : y ∈ U := ⟨hy, Metric.mem_ball_self hr⟩
  refine ⟨U, (e.isOpen_inter_preimage Metric.isOpen_ball).mem_nhds hyU, fun γ hγ => ?_⟩
  have himg : e '' U = B := by
    ext z
    constructor
    · rintro ⟨w, ⟨-, hw⟩, rfl⟩
      exact hw
    · intro hz
      refine ⟨e.symm z, ⟨e.map_target (hball hz), ?_⟩, e.right_inv (hball hz)⟩
      rw [mem_preimage, e.right_inv (hball hz)]
      exact hz
  haveI : ContractibleSpace B := (convex_ball (e y) r).contractibleSpace (Metric.nonempty_ball.2 hr)
  haveI : ContractibleSpace U :=
    (e.homeomorphOfImageSubsetSource inter_subset_left himg).contractibleSpace
  have hUs : IsSimplyConnected U := (inferInstance : SimplyConnectedSpace U)
  obtain ⟨F, -⟩ := (isSimplyConnected_iff_exists_homotopy_refl_forall_mem.1 hUs).2 y γ hγ
  exact ⟨F⟩

variable {n : ℕ} {V : Type*} [TopologicalSpace V]

/-- A locally affine manifold is semilocally simply connected. -/
theorem semilocallySimplyConnected_of_aff [ChartedSpace (Fin n → ℝ) V] :
    SemilocallySimplyConnected V := by
  exact semilocallySimplyConnected_of_forall_openPartialHomeomorph fun y =>
    ⟨chartAt (Fin n → ℝ) y, mem_chart_source _ y⟩

/-- A locally projective manifold is semilocally simply connected (`S(n)` is homeomorphic to the
Euclidean sphere, charted by stereographic projections). -/
theorem semilocallySimplyConnected_of_proj [ChartedSpace (S n) V] :
    SemilocallySimplyConnected V := by
  refine semilocallySimplyConnected_of_forall_openPartialHomeomorph
    (H := EuclideanSpace ℝ (Fin n)) fun y => ?_
  let h := S.homeomorphEuclideanSphere n
  let c := chartAt (S n) y
  refine ⟨c.trans (h.toOpenPartialHomeomorph.trans
    (chartAt (EuclideanSpace ℝ (Fin n)) (h (c y)))), ?_⟩
  simp only [OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
    Homeomorph.toOpenPartialHomeomorph_apply, univ_inter, mem_inter_iff, mem_preimage]
  exact ⟨mem_chart_source _ y, mem_chart_source _ _⟩

end Semilocal

/-! ### Deck transformations as automorphisms of the structure -/

section Deck

variable {G : Type w} {X : Type v} [TopologicalSpace X] [Group G] [MulAction G X]
  {M : Type u} [TopologicalSpace M] [ChartedSpace X M] {N : Type y} [TopologicalSpace N]
  [ChartedSpace X N]

/-- **A continuous map over a morphism is a morphism**: if `π : N → M` is a `(G,X)`-morphism and
`π ∘ f = π`, then `f` is a `(G,X)`-morphism. -/
theorem IsGXMorphism.of_comp_eq {π : N → M} (hπ : IsGXMorphism G X π) {f : N → N}
    (hf : Continuous f) (hfπ : ∀ x, π (f x) = π x) : IsGXMorphism G X f := by
  refine ⟨hf, fun x => ?_⟩
  obtain ⟨a, ha⟩ := hπ.exists_smul_eq x
  obtain ⟨b, hb⟩ := hπ.exists_smul_eq (f x)
  refine ⟨b⁻¹ * a, ?_⟩
  filter_upwards [ha, hf.continuousAt.eventually hb] with z h1 h2
  rw [hfπ, hfπ] at h2
  rw [mul_smul, ← h1, h2, inv_smul_smul]

variable (G X) in
/-- **The deck group of `π : N → M`, inside the automorphism group of `N`** (Déf. 15's `G`): the
automorphisms `f` of the `(G,X)`-manifold `N` with `π ∘ f = π`. -/
def deckAut (π : N → M) : Subgroup (GXAut G X N) where
  carrier := {f | ∀ x, π (f • x) = π x}
  mul_mem' {f g} hf hg x := by
    show π ((f * g) • x) = π x
    rw [mul_smul, hf, hg]
  one_mem' x := by
    show π ((1 : GXAut G X N) • x) = π x
    rw [one_smul]
  inv_mem' {f} hf x := by
    show π (f⁻¹ • x) = π x
    have := hf (f⁻¹ • x)
    rw [smul_inv_smul] at this
    exact this.symm

variable {π : N → M}

omit [TopologicalSpace M] [ChartedSpace X M] in
theorem mem_deckAut {f : GXAut G X N} : f ∈ deckAut G X π ↔ ∀ x, π (f • x) = π x := Iff.rfl

/-- **Every deck homeomorphism of a morphism `π` is an element of `deckAut`.** -/
def deckAut.ofHomeomorph (hπ : IsGXMorphism G X π) (φ : N ≃ₜ N) (hφ : ∀ x, π (φ x) = π x) :
    deckAut G X π :=
  ⟨show gxAutSubgroup G X N from ⟨φ, hπ.of_comp_eq φ.continuous hφ,
    hπ.of_comp_eq φ.symm.continuous fun x => by rw [← hφ (φ.symm x), φ.apply_symm_apply]⟩, hφ⟩

@[simp] theorem deckAut.ofHomeomorph_smul (hπ : IsGXMorphism G X π) (φ : N ≃ₜ N)
    (hφ : ∀ x, π (φ x) = π x) (x : N) : deckAut.ofHomeomorph hπ φ hφ • x = φ x := rfl

omit [TopologicalSpace M] [ChartedSpace X M] in
/-- A deck automorphism acts continuously. -/
theorem deckAut.continuous_smul (γ : deckAut G X π) : Continuous fun x : N => γ • x :=
  (γ : GXAut G X N).toHomeomorph.continuous

omit [TopologicalSpace M] [ChartedSpace X M] in
/-- A deck automorphism is over `π`. -/
theorem deckAut.comp_smul (γ : deckAut G X π) (x : N) : π (γ • x) = π x := γ.2 x

omit [TopologicalSpace M] [ChartedSpace X M] in
/-- Deck automorphisms are determined by their action. -/
theorem deckAut.ext {γ δ : deckAut G X π} (h : ∀ x : N, γ • x = δ • x) : γ = δ :=
  Subtype.ext (eq_of_smul_eq_smul h)

omit [ChartedSpace X M] in
/-- **No fixed point** (« sans point fixe »): two deck automorphisms of a connected covering
which agree at one point are equal. -/
theorem deckAut.eq_of_smul_eq [PreconnectedSpace N] (hπ : IsCoveringMap π)
    {γ δ : deckAut G X π} {x : N} (h : γ • x = δ • x) : γ = δ := by
  exact deckAut.ext fun z => congrFun (hπ.eq_of_comp_eq (deckAut.continuous_smul γ)
    (deckAut.continuous_smul δ)
    (funext fun z => (deckAut.comp_smul γ z).trans (deckAut.comp_smul δ z).symm) x h) z

omit [ChartedSpace X M] in
/-- The deck group of a connected covering acts freely (`IsCancelSMul`). -/
theorem deckAut.isCancelSMul [PreconnectedSpace N] (hπ : IsCoveringMap π) :
    IsCancelSMul (deckAut G X π) N := by
  refine { left_cancel' := fun a b c h => ?_
           right_cancel' := fun a b c h => deckAut.eq_of_smul_eq hπ h }
  have := congrArg (fun z => a⁻¹ • z) h
  simpa only [inv_smul_smul] using this

omit [ChartedSpace X M] in
/-- **« proprement discontinu »** (Mathlib's sense, DEC-120): the deck group of a connected
covering of a Hausdorff, locally connected space acts properly discontinuously. -/
theorem deckAut.properlyDiscontinuousSMul [T2Space M] [LocallyConnectedSpace M]
    [PreconnectedSpace N] (hπ : IsCoveringMap π) :
    ProperlyDiscontinuousSMul (deckAut G X π) N := by
  refine ⟨fun {K L} hK hL => ?_⟩
  choose U hU huniq using exists_nhds_eq_of_comp_eq hπ
  obtain ⟨t, -, ht⟩ := (hK.prod hL).elim_nhds_subcover U fun p _ => hU p
  have hsub : ∀ p, {γ : deckAut G X π | ∃ z ∈ U p, γ • z.1 = z.2}.Subsingleton := by
    rintro p γ ⟨z, hz, hγz⟩ δ ⟨z', hz', hδz'⟩
    have := huniq p (fun x => γ • x) (fun x => δ • x) (deckAut.continuous_smul γ)
      (deckAut.continuous_smul δ) (deckAut.comp_smul γ) (deckAut.comp_smul δ) ⟨z, hz, hγz⟩
      ⟨z', hz', hδz'⟩
    exact deckAut.ext fun x => congrFun this x
  refine (t.finite_toSet.biUnion fun p _ => (hsub p).finite).subset ?_
  rintro γ ⟨_, ⟨x, hxK, rfl⟩, hxL⟩
  obtain ⟨p, hpt, hxp⟩ := mem_iUnion₂.1 (ht (mk_mem_prod hxK hxL))
  exact mem_iUnion₂.2 ⟨p, hpt, (x, γ • x), hxp, rfl⟩

/-- **A simply connected covering is Galois**: two points are in one fibre iff they are in one
orbit of the deck group. -/
theorem deckAut.comp_eq_iff [SimplyConnectedSpace N] [LocPathConnectedSpace N]
    (hπ : IsCoveringMap π) (hπG : IsGXMorphism G X π) {y k : N} :
    π y = π k ↔ ∃ γ : deckAut G X π, γ • y = k := by
  constructor
  · intro h
    obtain ⟨φ, hφ, hφy⟩ := exists_homeomorph_comp_eq_of_simplyConnected hπ h
    exact ⟨deckAut.ofHomeomorph hπG φ hφ, hφy⟩
  · rintro ⟨γ, rfl⟩
    exact (deckAut.comp_smul γ y).symm

/-- **« $V/G_1$ compact »**: the quotient of a simply connected covering of a compact Hausdorff
space by its deck group is compact. -/
theorem deckAut.compactSpace_quotient [CompactSpace M] [T2Space M] [SimplyConnectedSpace N]
    [LocPathConnectedSpace N] (hπ : IsCoveringMap π) (hπG : IsGXMorphism G X π) :
    CompactSpace (MulAction.orbitRel.Quotient (deckAut G X π) N) := by
  obtain ⟨K, hK, hKπ⟩ := exists_isCompact_forall_exists_eq hπ.isLocalHomeomorph
    (isClosed_range_of_isCoveringMap hπ)
  have himg : Quotient.mk (MulAction.orbitRel (deckAut G X π) N) '' K = univ := by
    refine eq_univ_of_forall fun q => ?_
    obtain ⟨y, rfl⟩ := Quotient.exists_rep q
    obtain ⟨k, hkK, hk⟩ := hKπ y
    obtain ⟨γ, hγ⟩ := (deckAut.comp_eq_iff hπ hπG).1 hk.symm
    refine ⟨k, hkK, ?_⟩
    rw [← hγ]
    exact Quotient.sound (MulAction.mem_orbit y γ)
  refine ⟨?_⟩
  rw [← himg]
  exact hK.image continuous_quotient_mk'

/-- **The theorem of p. 238, for any simply connected covering and any `(G,X)`**: if `M` is
compact and Hausdorff, locally path-connected, and `π : N → M` is a covering with `N` simply
connected, then for every `(G,X)`-structure on `N` for which `π` is a morphism (e.g. the pulled-back
one, `existsUnique_pullback`), `N` is divisible: its deck group `deckAut G X π` is a subgroup of
automorphisms, properly discontinuous, without fixed point, with compact quotient. -/
theorem isDivisible_of_isCoveringMap [CompactSpace M] [T2Space M] [LocPathConnectedSpace M]
    [SimplyConnectedSpace N] (hπ : IsCoveringMap π) (hπG : IsGXMorphism G X π) :
    IsDivisible G X N := by
  haveI : LocPathConnectedSpace N :=
    locPathConnectedSpace_of_isLocalHomeomorph hπ.isLocalHomeomorph
  exact ⟨deckAut G X π, deckAut.properlyDiscontinuousSMul hπ, deckAut.isCancelSMul hπ,
    deckAut.compactSpace_quotient hπ hπG⟩

end Deck

/-! ### The universal cover with its pulled-back structure -/

section UniversalCoverGX

variable {G : Type w} {X : Type v} [TopologicalSpace X] [Group G] [MulAction G X]
  {M : Type u} [TopologicalSpace M] [ChartedSpace X M]

variable (X) in
/-- **The universal cover of a `(G,X)`-manifold, with the pulled-back charts** (p. 238, « tout
revêtement $R$ de $V$ est une variété localement projective »; `pullbackChartedSpace`). -/
@[reducible] def UniversalCover.gxChartedSpace [LocPathConnectedSpace M]
    (hM : SemilocallySimplyConnected M) (m₀ : M) : ChartedSpace X (UniversalCover M m₀) :=
  pullbackChartedSpace (UniversalCover.isCoveringMap_proj (y₀ := m₀) hM).isLocalHomeomorph

/-- **The theorem of p. 238 for any `(G,X)`, on the universal cover**: the universal cover of a
compact Hausdorff, locally path-connected, semilocally simply connected `(G,X)`-manifold, with its
pulled-back structure, is divisible. -/
theorem UniversalCover.isDivisible [CompactSpace M] [T2Space M] [LocPathConnectedSpace M]
    (hM : SemilocallySimplyConnected M) (m₀ : M) :
    letI := UniversalCover.gxChartedSpace X hM m₀
    IsDivisible G X (UniversalCover M m₀) := by
  letI := UniversalCover.gxChartedSpace X hM m₀
  haveI := UniversalCover.simplyConnectedSpace (y₀ := m₀) hM
  exact isDivisible_of_isCoveringMap (UniversalCover.isCoveringMap_proj hM)
    (isGXMorphism_pullback _)

end UniversalCoverGX

/-! ### The paper's two cases -/

section Cases

variable {n : ℕ} {V : Type u} [TopologicalSpace V]

/-- **The universal cover of a locally projective manifold is charted on `S(n)`** by the
pulled-back charts. -/
instance UniversalCover.instChartedSpaceProj [ChartedSpace (S n) V] (v₀ : V) :
    ChartedSpace (S n) (UniversalCover V v₀) :=
  haveI := locPathConnectedSpace_of_proj (n := n) (V := V)
  UniversalCover.gxChartedSpace (S n) (semilocallySimplyConnected_of_proj (n := n)) v₀

/-- **The universal cover of a locally affine manifold is charted on `ℝⁿ`** by the pulled-back
charts. -/
instance UniversalCover.instChartedSpaceAff [ChartedSpace (Fin n → ℝ) V] (v₀ : V) :
    ChartedSpace (Fin n → ℝ) (UniversalCover V v₀) :=
  haveI := locPathConnectedSpace_of_aff (n := n) (V := V)
  UniversalCover.gxChartedSpace (Fin n → ℝ) (semilocallySimplyConnected_of_aff (n := n)) v₀

/-- **The universal cover of a locally projective manifold is locally projective** (p. 238). -/
instance UniversalCover.instHasGroupoidProj [ChartedSpace (S n) V]
    [HasGroupoid V (projGroupoid n)] (v₀ : V) :
    HasGroupoid (UniversalCover V v₀) (projGroupoid n) := by
  exact hasGroupoid_pullback _

/-- **The universal cover of a locally affine manifold is locally affine** (p. 238). -/
instance UniversalCover.instHasGroupoidAff [ChartedSpace (Fin n → ℝ) V]
    [HasGroupoid V (affGroupoid n)] (v₀ : V) :
    HasGroupoid (UniversalCover V v₀) (affGroupoid n) := by
  exact hasGroupoid_pullback _

/-- The covering projection of the universal cover is a projective morphism. -/
theorem UniversalCover.isGXMorphism_proj_proj [ChartedSpace (S n) V] (v₀ : V) :
    IsGXMorphism (GSR n) (S n) (UniversalCover.proj V v₀) := by
  exact isGXMorphism_pullback _

/-- The covering projection of the universal cover is an affine morphism. -/
theorem UniversalCover.isGXMorphism_proj_aff [ChartedSpace (Fin n → ℝ) V] (v₀ : V) :
    IsGXMorphism (GAR n) (Fin n → ℝ) (UniversalCover.proj V v₀) := by
  exact isGXMorphism_pullback _

/-- **The theorem of p. 238** (`bzthm:c1s1_revetement_universel_divisible`): if `V` is a compact
locally projective manifold, its universal cover `Ṽ` (at any base point `v₀`) — a simply connected
covering of `V`, locally projective with the pulled-back structure, for which the projection is a
projective morphism — is divisible. -/
theorem revetement_universel_divisible_proj [ChartedSpace (S n) V]
    [HasGroupoid V (projGroupoid n)] [CompactSpace V] [T2Space V] (v₀ : V) :
    IsCoveringMap (UniversalCover.proj V v₀) ∧ SimplyConnectedSpace (UniversalCover V v₀) ∧
      HasGroupoid (UniversalCover V v₀) (projGroupoid n) ∧
      IsGXMorphism (GSR n) (S n) (UniversalCover.proj V v₀) ∧
      IsDivisible (GSR n) (S n) (UniversalCover V v₀) := by
  haveI := locPathConnectedSpace_of_proj (n := n) (V := V)
  have hV := semilocallySimplyConnected_of_proj (n := n) (V := V)
  exact ⟨UniversalCover.isCoveringMap_proj hV, UniversalCover.simplyConnectedSpace hV,
    inferInstance,
    UniversalCover.isGXMorphism_proj_proj v₀, UniversalCover.isDivisible (G := GSR n) hV v₀⟩

/-- **The theorem of p. 238, affine case** (« les énoncés équivalents du cas affin s'obtiennent en
remplaçant $S(n)$ par $\R^n$ »): the universal cover of a compact locally affine manifold is
divisible. -/
theorem revetement_universel_divisible_aff [ChartedSpace (Fin n → ℝ) V]
    [HasGroupoid V (affGroupoid n)] [CompactSpace V] [T2Space V] (v₀ : V) :
    IsCoveringMap (UniversalCover.proj V v₀) ∧ SimplyConnectedSpace (UniversalCover V v₀) ∧
      HasGroupoid (UniversalCover V v₀) (affGroupoid n) ∧
      IsGXMorphism (GAR n) (Fin n → ℝ) (UniversalCover.proj V v₀) ∧
      IsDivisible (GAR n) (Fin n → ℝ) (UniversalCover V v₀) := by
  haveI := locPathConnectedSpace_of_aff (n := n) (V := V)
  have hV := semilocallySimplyConnected_of_aff (n := n) (V := V)
  exact ⟨UniversalCover.isCoveringMap_proj hV, UniversalCover.simplyConnectedSpace hV,
    inferInstance,
    UniversalCover.isGXMorphism_proj_aff v₀, UniversalCover.isDivisible (G := GAR n) hV v₀⟩

/-- **p. 238 for every simply connected covering, projective case**: a simply connected covering
`N → V` of a compact locally projective manifold, with the pulled-back structure, is divisible. -/
theorem isDivisible_of_isCoveringMap_proj [ChartedSpace (S n) V] [CompactSpace V] [T2Space V]
    {N : Type*} [TopologicalSpace N] [SimplyConnectedSpace N] {π : N → V}
    (hπ : IsCoveringMap π) :
    letI := pullbackChartedSpace (X := S n) hπ.isLocalHomeomorph
    IsDivisible (GSR n) (S n) N := by
  letI := pullbackChartedSpace (X := S n) hπ.isLocalHomeomorph
  haveI := locPathConnectedSpace_of_proj (n := n) (V := V)
  exact isDivisible_of_isCoveringMap hπ (isGXMorphism_pullback _)

/-- **p. 238 for every simply connected covering, affine case.** -/
theorem isDivisible_of_isCoveringMap_aff [ChartedSpace (Fin n → ℝ) V] [CompactSpace V]
    [T2Space V] {N : Type*} [TopologicalSpace N] [SimplyConnectedSpace N] {π : N → V}
    (hπ : IsCoveringMap π) :
    letI := pullbackChartedSpace (X := Fin n → ℝ) hπ.isLocalHomeomorph
    IsDivisible (GAR n) (Fin n → ℝ) N := by
  letI := pullbackChartedSpace (X := Fin n → ℝ) hπ.isLocalHomeomorph
  haveI := locPathConnectedSpace_of_aff (n := n) (V := V)
  exact isDivisible_of_isCoveringMap hπ (isGXMorphism_pullback _)

/-- The hypotheses are satisfiable: `S(n)`, charted on itself, is a compact Hausdorff locally
projective manifold (its universal cover is `S(n)` for `n ≥ 2`, a line for the circle `S(1)`, a
point for `n = 0`). -/
example (n : ℕ) (x : S n) : IsDivisible (GSR n) (S n) (UniversalCover (S n) x) :=
  (revetement_universel_divisible_proj x).2.2.2.2

end Cases

end Benzecri
