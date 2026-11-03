import GX.Suspension.Conic

/-!
# The `(G,X)`-suspension céleste of a singular `(H, L)`-manifold

Package BBS-Celestial (layer L0 of `papers/bbs/REVIEW.md` §B). L0 is NEW THEORY, built under
the author's ruling. Its starting point is draft material commented out in
`papers/gx/sources/thesis/these.tex` (l.3560–3677, here l.3621–3677, "Suspension d'une voûte
céleste"), not part of the thesis: the author discarded it ("It was commented out for a
reason"), so nothing below is a claim of the thesis; the counterexamples below are motivation
for the corrected definitions. Every `these.tex` line cited in l.3560–3677 refers to that
discarded draft; the `these:*` labels are row keys naming the file, not thesis results. The paper
`papers/gx/legacy/labeled/RamcovGX.tex` l.734–740 calls geometric suspension a lift of the
functor `susp : Top → Top` to singular manifolds. **No ledger label is marked**: the draft is
not a ledger source. Rows touched, unmarked:

* `these:defi_suspension_celeste` (`these.tex:3631`) — `GX.ConicChart.coneChart` (the chart
  `φ_p⁻¹ ∘ susp*(φ_i)`, through `GX.Susp.posChart`), `GX.ConicChart.celestialAtlas` (the
  préatlas, over the maximal a.e. atlas of `Σ`), `GX.ConicStructure.celestialStructure` (the
  maximal a.e. `(G,X)`-atlas it generates on `susp(Σ)`).
* `these:prop_suspension_celeste` (`these.tex:3645`: `susp_{(G,X)}(Σ)` is a singular
  `(G,X)`-manifold) — **proved** for a FULL conic STRUCTURE (`GX.ConicStructure`, onto the whole
  cone, radius preserved): `GX.ConicStructure.isAEAtlas_celestialAtlas`,
  `GX.ConicStructure.celestialStructure`; its support is `susp*(Reg Σ)`
  (`GX.ConicStructure.support_celestialAtlas`) and its chart changes lie in `H`
  (`GX.ConicStructure.eventually_coneChart_eq_smul`). The draft's proposition, read literally
  with its ray condition alone, fails; the counterexample motivating the radius hypothesis (a
  design note) is `GX.celestial_counterexample` — `Σ` a point, `X = susp(Bool) ≅ ℝ`,
  `G = Perm Bool = G_p`, every hypothesis of the draft checked in
  `GX.celestial_counterexample_hypotheses`. Radius preservation is SUFFICIENT, NOT NECESSARY (a
  design note): on `(Aff(ℝ), ℝ)` at `0` with `H = G_p`, the sphere chart and `Σ` a point with its
  two charts to `±1`, the cone préatlas is a `(G,X)`-atlas (its chart change is `-id ∈ G`) while
  no radius-preserving conic structure exists (`GX.isEmpty_conicStructure_affine_stabilizer`,
  `GX.Suspension.Affine`; the atlas half is not formalized). The candidate MINIMAL
  hypothesis, which is all the draft's argument at l.3667 uses, is a radial lift: for each
  `h ∈ H` some `g_h ∈ G` with `φ ∘ g_h = susp(h·) ∘ φ`; it is radius preservation (`g_h = h`)
  when `G ⊆ Isom`. This round keeps radius preservation; the generalisation is not attempted.
* Regular and singular rays: `GX.ConicStructure.mk_mem_reg` (**proved**: the ray over a regular
  point of `Σ` is regular), `GX.ConicStructure.mem_reg_of_mk_mem_reg` and
  `GX.ConicStructure.mk_mem_sing` (**proved**, with the ADDED hypothesis `CompactSpace L`: the
  ray over a singular point is singular), `GX.ConicStructure.mk_mem_reg_iff` (both together),
  `GX.ConicStructure.apex_mem_reg_model` (**proved**: the apex is regular when `Σ` is the model
  link `L`, RamcovGX l.740's "regular at `O` if `Σ` is a sphere", the "if" half).
* Witness: `GX.ConicStructure.tautologicalSuspension` (every connected locally connected singular
  `(K, L)`-manifold has a `(K, susp L)`-suspension, `K` rigid on `L`), with
  `GX.Susp.isRigidAction_radialAction`.

> \begin{defi}[$(G,X)$-suspension céleste] Soient $(G,X)$ une structure analytique, $p\in X$
> et $(\U_p,X_p,\V_p,\phi_p)$ une structure conique en $p$ telle que $X_p$ est localement
> connexe. Soit enfin $\Sigma$ une $(G_p,X_p)$-variété singulière connexe. La
> $(G,X)$-suspension céleste de $\Sigma$, notée $\susp_{(G,X)}(\Sigma)$, est la $(G,X)$-variété
> singulière $(M,\G,\B)$ avec $M=\susp(\Sigma)$ et $(\G,\B)$ le $(G,X)$-brouillard opaque plus
> épais que le $(G,X)$-préatlas $\left(\susp^*(\U_i),X,\phi_p^{-1}\circ
> \susp^*(\V_i),\phi_p^{-1}\circ \susp^*(\phi_i)\right)_{i\in I}$ avec
> $(\U_i,X_p,\V_i,\phi_i)_{i\in I}$ le $(G,X)$-atlas de $\reg(\Sigma)$ \end{defi}
> (commented-out draft, these.tex:3631–3643)
>
> \begin{prop}{} … $\susp_{(G,X)}(\Sigma)$ est bien une $(G,X)$-variété singulière.
> \end{prop} (commented-out draft, these.tex:3645–3649)
>
> For these suspensions, the image of regular $(G,X)$-manifolds are regular except possibly at
> $O$ and are regular at $O$ if and only if $\Sigma$ is homeomorphic to a sphere.
> (RamcovGX.tex:740)

## Hypothesis checklist

| draft hypothesis | here |
|---|---|
| `(G,X)` analytic | ⚠ weakened: `ContinuousConstSMul`, `IsRigidAction` (1) |
| (not in « structure analytique ») | ⚠ strengthened: `LocallyConnectedSpace X`, `T2Space X` (2) |
| a conic structure at `p` | ⚠ strengthened: a FULL `ConicStructure`; sufficient, unnecessary (3) |
| `X_p` locally connected | ✓ carried (`LocallyConnectedSpace L`) |
| (none) | ⚠ strengthened, for the singular rays only: `CompactSpace L` (4) |
| `Σ` a connected singular `(G_p, X_p)`-manifold | ✓ carried (5) |
| `H` acts on `X_p` by homeomorphisms | ✓ derived, not assumed: `continuousConstSMul` |

1. Faithfulness and connectedness of `X` are unused.
2. Standing hypotheses of GX's `cor:maximal_atlas`
   (`GX.IsAEAtlas.isMaximalAEAtlas_maximalAEAtlas`), used to form `celestialStructure`; they are
   not part of « structure analytique » (`these.tex:1185`).
3. Radius preserved; FULL is the draft's "homéomorphisme `U → susp(X_p)`". The ray-only
   version, read literally, fails (`celestial_counterexample`, the counterexample motivating the
   hypothesis); radius preservation is not necessary (the `(Aff(ℝ), ℝ)` example above), the
   candidate minimal hypothesis being a radial lift `g_h`.
4. `mem_reg_of_mk_mem_reg`, `mk_mem_sing`, `mk_mem_reg_iff` only: `φ⁻¹(L × [t/2, 2t])` is then
   compact, hence closed, and contains the limits of the regular points of a box around a
   singular ray. Every intended link is compact (`Sⁿ`, `HS² ≅ S²`); the non-compact case is
   open (possibly false).
5. `PreconnectedSpace Σ`, `LocallyConnectedSpace Σ`, `SingularGXStructure H L Σ` (`G_p`
   generalised to `H`, BBS-Q2); Hausdorff and second countable are unused.

## SCOPE (disclosed)

* "Le `(G,X)`-brouillard opaque plus épais que le préatlas" is read as the maximal a.e. atlas
  generated by the préatlas (`maximalAEAtlas`, `cor:maximal_atlas`, DEC-25/DEC-42).
* "le `(G,X)`-atlas de `reg(Σ)`" is read as the maximal a.e. atlas of `Σ` (`aeAtlas H L Σ`).
* The converse "regular at `O` only if `Σ` is the model link" is NOT stated: in this generality
  (arbitrary `(G,X)`, `H`) it is not clear it holds, and BBS's form (BBS-Q4, every
  `HS²`-structure on `S²` is `HS²`) needs the developing map of `Σ`.
* `susp` carries RamcovGX's topology (`GX.Susp`), not the thesis's quotient topology
  (`these.tex:3685`); they agree for compact links (`GX.Susp.eq_quotTop_of_compactSpace`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Filter Topology NNReal

namespace GX

namespace Susp

variable {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]

/-- The radial extension `susp*(e)` of a chart `e`, on `susp*(e.source) → susp*(e.target)`. -/
def posChart (e : OpenPartialHomeomorph S T) : OpenPartialHomeomorph (Susp S) (Susp T) where
  toFun := map e
  invFun := map e.symm
  source := mk '' (e.source ×ˢ Ioi 0)
  target := mk '' (e.target ×ˢ Ioi 0)
  map_source' := by
    rintro _ ⟨q, ⟨hq1, hq2⟩, rfl⟩
    exact ⟨(e q.1, q.2), ⟨e.map_source hq1, hq2⟩, rfl⟩
  map_target' := by
    rintro _ ⟨q, ⟨hq1, hq2⟩, rfl⟩
    exact ⟨(e.symm q.1, q.2), ⟨e.map_target hq1, hq2⟩, rfl⟩
  left_inv' := by
    rintro _ ⟨q, ⟨hq1, -⟩, rfl⟩
    show mk (e.symm (e q.1), q.2) = mk q
    rw [e.left_inv hq1]
  right_inv' := by
    rintro _ ⟨q, ⟨hq1, -⟩, rfl⟩
    show mk (e (e.symm q.1), q.2) = mk q
    rw [e.right_inv hq1]
  open_source := isOpen_image_mk (e.open_source.prod isOpen_Ioi) fun q hq => hq.2
  open_target := isOpen_image_mk (e.open_target.prod isOpen_Ioi) fun q hq => hq.2
  continuousOn_toFun := by
    rintro _ ⟨q, ⟨hq1, hq2⟩, rfl⟩
    exact (continuousAt_map_mk hq2 (e.continuousAt hq1)).continuousWithinAt
  continuousOn_invFun := by
    rintro _ ⟨q, ⟨hq1, hq2⟩, rfl⟩
    exact (continuousAt_map_mk hq2 (e.continuousAt_symm hq1)).continuousWithinAt

theorem posChart_source (e : OpenPartialHomeomorph S T) :
    (posChart e).source = mk '' (e.source ×ˢ Ioi 0) := rfl

theorem posChart_apply (e : OpenPartialHomeomorph S T) (q : S × ℝ≥0) :
    posChart e (mk q) = mk (e q.1, q.2) := rfl

end Susp

variable {G : Type*} {X : Type*} [Group G] [TopologicalSpace X] [MulAction G X]
  {p : X} {L : Type*} [TopologicalSpace L]

namespace ConicChart

variable (c : ConicChart X p L) {S : Type*} [TopologicalSpace S]

/-- The cone chart `φ_p⁻¹ ∘ susp*(e)` of a chart `e : Σ ⇀ L` (`these.tex:3639`). -/
def coneChart (e : OpenPartialHomeomorph S L) : OpenPartialHomeomorph (Susp S) X :=
  (Susp.posChart e).trans c.φ.symm

theorem coneChart_apply (e : OpenPartialHomeomorph S L) (q : S × ℝ≥0) :
    c.coneChart e (Susp.mk q) = c.φ.symm (Susp.mk (e q.1, q.2)) := rfl

theorem coneChart_source_of_isFull (hf : c.IsFull) (e : OpenPartialHomeomorph S L) :
    (c.coneChart e).source = Susp.mk '' (e.source ×ˢ Ioi 0) := by
  rw [coneChart, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    show c.φ.target = univ from hf, preimage_univ, inter_univ, Susp.posChart_source]

/-- **The préatlas of `these:defi_suspension_celeste`** (`these.tex:3638`): the cone charts of the
charts of the maximal a.e. `(H, L)`-atlas of `Σ`. -/
def celestialAtlas (H : Subgroup G) [MulAction H L] (S : Type*) [TopologicalSpace S]
    [SingularGXStructure H L S] : Set (OpenPartialHomeomorph (Susp S) X) :=
  c.coneChart '' aeAtlas H L S

end ConicChart

namespace ConicStructure

variable {H : Subgroup G} [MulAction H L] (c : ConicStructure G p H L)

/-- In a full conic structure, `φ⁻¹` intertwines `susp(h·)` and `h·` on the whole cone. -/
theorem symm_mk_smul [T2Space X] [ContinuousConstSMul G X] (hf : c.IsFull) (h : H) (σ : L)
    (t : ℝ≥0) : c.φ.symm (Susp.mk (h • σ, t)) = (h : G) • c.φ.symm (Susp.mk (σ, t)) := by
  have hmem : ∀ a, a ∈ c.φ.target := fun a => by
    rw [show c.φ.target = univ from hf]; trivial
  obtain ⟨hs, he⟩ := c.map_smul_of_isFull hf h (c.φ.map_target (hmem (Susp.mk (σ, t))))
  rw [c.φ.right_inv (hmem _), Susp.map_mk] at he
  rw [← he, c.φ.left_inv hs]

variable {S : Type*} [TopologicalSpace S] [SingularGXStructure H L S]

/-- **The chart changes of the cone préatlas lie in `H`** (the computation of
`these.tex:3665–3673`, which uses the radial form of the conic condition): near every point of
the overlap of two cone charts, they differ by the element `h ∈ H` by which the two charts of `Σ`
differ. -/
theorem eventually_coneChart_eq_smul [T2Space X] [ContinuousConstSMul G X]
    [LocallyConnectedSpace L] (hf : c.IsFull) {e e' : OpenPartialHomeomorph S L}
    (he : e ∈ aeAtlas H L S) (he' : e' ∈ aeAtlas H L S) {z : Susp S}
    (hz : z ∈ (c.coneChart e).source ∩ (c.coneChart e').source) :
    ∃ h : H, ∀ᶠ y in 𝓝 z, c.coneChart e' y = (h : G) • c.coneChart e y := by
  haveI := c.continuousConstSMul
  rw [c.coneChart_source_of_isFull hf, c.coneChart_source_of_isFull hf] at hz
  obtain ⟨⟨q, ⟨hq1, hq2⟩, rfl⟩, ⟨q', ⟨hq1', hq2'⟩, hqq'⟩⟩ := hz
  obtain rfl := Susp.eq_of_mk_eq_of_pos hqq' hq2'
  obtain ⟨h, hh⟩ := (isMaximalAEAtlas_aeAtlas H L S).1.1.eventually_smul_eq he he' hq1 hq1'
  refine ⟨h, ?_⟩
  rw [Susp.nhds_mk_of_pos hq2, Filter.eventually_map]
  filter_upwards [continuous_fst.continuousAt.eventually hh] with y hy
  rw [c.coneChart_apply, c.coneChart_apply, hy, c.symm_mk_smul hf]

/-- The support of the cone préatlas is `susp*(Reg Σ)`. -/
theorem support_celestialAtlas (hf : c.IsFull) :
    support (c.celestialAtlas H S) = Susp.mk '' (Reg H L S ×ˢ Ioi 0) := by
  ext z
  rw [mem_support]
  constructor
  · rintro ⟨_, ⟨e, he, rfl⟩, hz⟩
    rw [c.coneChart_source_of_isFull hf] at hz
    obtain ⟨q, ⟨hq1, hq2⟩, rfl⟩ := hz
    exact ⟨q, ⟨mem_support.2 ⟨e, he, hq1⟩, hq2⟩, rfl⟩
  · rintro ⟨q, ⟨hq1, hq2⟩, rfl⟩
    obtain ⟨e, he, hqe⟩ := mem_support.1 hq1
    refine ⟨c.coneChart e, ⟨e, he, rfl⟩, ?_⟩
    rw [c.coneChart_source_of_isFull hf]
    exact ⟨q, ⟨hqe, hq2⟩, rfl⟩

/-- The cone préatlas is a `(G,X)`-atlas (the proof of `these:prop_suspension_celeste`,
`these.tex:3658–3676`). -/
theorem isGXAtlas_celestialAtlas [T2Space X] [ContinuousConstSMul G X] [IsRigidAction G X]
    [LocallyConnectedSpace L] (hf : c.IsFull) : IsGXAtlas G (c.celestialAtlas H S) := by
  refine isGXAtlas_of_eventually ?_
  rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩ z hz
  obtain ⟨h, hh⟩ := c.eventually_coneChart_eq_smul hf he he' hz
  exact ⟨(h : G), hh⟩

/-- **The atlas of the suspension céleste, for a full conic STRUCTURE** (row key
`these:prop_suspension_celeste`, the draft's `these.tex:3645`, corrected): the cone préatlas is an
almost everywhere `(G,X)`-atlas on `susp(Σ)` — its support `susp*(Reg Σ)` is portly by
`prop:susp_portly` (`GX.Susp.isPortly_image_mk`), as in the draft's argument (`these.tex:3653`).
-/
theorem isAEAtlas_celestialAtlas [T2Space X] [ContinuousConstSMul G X] [IsRigidAction G X]
    [LocallyConnectedSpace L] [PreconnectedSpace S] [LocallyConnectedSpace S] (hf : c.IsFull) :
    IsAEAtlas G (c.celestialAtlas H S) := by
  refine ⟨c.isGXAtlas_celestialAtlas hf, ?_⟩
  rw [c.support_celestialAtlas hf]
  exact Susp.isPortly_image_mk (isPortly_reg H L S)

variable (S) in
/-- **The `(G,X)`-suspension céleste** `susp_{(G,X)}(Σ)` (`these:defi_suspension_celeste`,
`these.tex:3631`): `susp(Σ)` with the maximal a.e. `(G,X)`-atlas generated by the cone préatlas.
That it is a singular `(G,X)`-structure is `these:prop_suspension_celeste` (`these.tex:3645`). -/
@[reducible] def celestialStructure [T2Space X] [ContinuousConstSMul G X] [IsRigidAction G X]
    [LocallyConnectedSpace X] [LocallyConnectedSpace L] [PreconnectedSpace S]
    [LocallyConnectedSpace S] (hf : c.IsFull) : SingularGXStructure G X (Susp S) :=
  ⟨maximalAEAtlas G (c.celestialAtlas H S),
    (c.isAEAtlas_celestialAtlas hf).isMaximalAEAtlas_maximalAEAtlas⟩

/-- **The ray over a regular point is regular**: `susp*(Reg Σ) ⊆ Reg(susp_{(G,X)}(Σ))`. -/
theorem mk_mem_reg [T2Space X] [ContinuousConstSMul G X] [IsRigidAction G X]
    [LocallyConnectedSpace X] [LocallyConnectedSpace L] [PreconnectedSpace S]
    [LocallyConnectedSpace S] (hf : c.IsFull) {x : S} (hx : x ∈ Reg H L S) {t : ℝ≥0}
    (ht : 0 < t) :
    letI := c.celestialStructure S hf
    Susp.mk (x, t) ∈ Reg G X (Susp S) := by
  letI := c.celestialStructure S hf
  have hA := c.isAEAtlas_celestialAtlas (S := S) hf
  refine support_mono hA.subset_maximalAEAtlas ?_
  rw [c.support_celestialAtlas hf]
  exact ⟨(x, t), ⟨hx, ht⟩, rfl⟩

/-- On the model link `Σ = L` (with its tautological `(H, L)`-structure, `ofHasGroupoid`), every
cone chart is, near each point of its source, `h · φ⁻¹` for some `h ∈ H`. -/
theorem eventually_coneChart_model [T2Space X] [ContinuousConstSMul G X] [T2Space L]
    [LocallyConnectedSpace L] [IsRigidAction H L] [ContinuousConstSMul H L] (hf : c.IsFull)
    {e : OpenPartialHomeomorph L L}
    (he : e ∈ (gxGroupoid H L).maximalAtlas L) {z : Susp L} (hz : z ∈ (c.coneChart e).source) :
    ∃ h : H, ∀ᶠ y in 𝓝 z, c.coneChart e y = (h : G) • c.φ.symm y := by
  rw [c.coneChart_source_of_isFull hf] at hz
  obtain ⟨q, ⟨hq1, hq2⟩, rfl⟩ := hz
  obtain ⟨h, hh⟩ := mem_maximalAtlas_iff_eventually.1 he q.1 hq1
  refine ⟨h, ?_⟩
  rw [Susp.nhds_mk_of_pos hq2, Filter.eventually_map]
  filter_upwards [continuous_fst.continuousAt.eventually hh] with y hy
  rw [c.coneChart_apply, hy, show (chartAt L q.1 : L → L) y.1 = y.1 from rfl, c.symm_mk_smul hf]

/-- **The apex is regular over the model link** (`RamcovGX.tex:740`, "regular at `O` if `Σ` is a
sphere", the "if" half, for the model link `Σ = L` itself): `φ⁻¹ : susp(L) → U` is compatible with
every cone chart, so it is a chart of the maximal atlas and `O ∈ Reg(susp_{(G,X)}(L))`. -/
theorem apex_mem_reg_model [T2Space X] [ContinuousConstSMul G X] [IsRigidAction G X]
    [LocallyConnectedSpace X] [T2Space L] [LocallyConnectedSpace L] [PreconnectedSpace L]
    (hf : c.IsFull) (σ : L) :
    haveI := c.continuousConstSMul
    haveI := c.isRigidAction
    letI : SingularGXStructure H L L := SingularGXStructure.ofHasGroupoid (↥H) L L
    letI := c.celestialStructure L hf
    Susp.mk (σ, 0) ∈ Reg G X (Susp L) := by
  haveI := c.continuousConstSMul
  haveI := c.isRigidAction
  letI : SingularGXStructure H L L := SingularGXStructure.ofHasGroupoid (↥H) L L
  set A := c.celestialAtlas H L with hAdef
  have hA : IsAEAtlas G A := c.isAEAtlas_celestialAtlas hf
  have hmax : aeAtlas H L L = (gxGroupoid H L).maximalAtlas L := rfl
  set Φ : OpenPartialHomeomorph (Susp L) X := c.φ.symm with hΦ
  have hΦs : Φ.source = univ := hf
  -- `insert Φ A` is an a.e. `(G,X)`-atlas
  have hGX : IsGXAtlas G (insert Φ A) := by
    refine isGXAtlas_of_eventually ?_
    rintro e₁ he₁ e₂ he₂ z hz
    rcases he₁ with rfl | ⟨e, he, rfl⟩ <;> rcases he₂ with rfl | ⟨e', he', rfl⟩
    · exact ⟨1, Eventually.of_forall fun y => (one_smul G _).symm⟩
    · rw [hmax] at he'
      obtain ⟨h, hh⟩ := c.eventually_coneChart_model hf he' hz.2
      exact ⟨(h : G), hh⟩
    · rw [hmax] at he
      obtain ⟨h, hh⟩ := c.eventually_coneChart_model hf he hz.1
      refine ⟨(h : G)⁻¹, ?_⟩
      filter_upwards [hh] with y hy
      rw [hy, inv_smul_smul]
    · obtain ⟨h, hh⟩ := c.eventually_coneChart_eq_smul hf he he' hz
      exact ⟨(h : G), hh⟩
  have hA' : IsAEAtlas G (insert Φ A) :=
    ⟨hGX, hA.2.mono (support_mono (subset_insert Φ A)) (isOpen_support _)⟩
  have hle : AELe G A (insert Φ A) := hGX.isThinner_completion_of_subset (subset_insert Φ A)
  have hΦmem : Φ ∈ maximalAEAtlas G A := subset_maximalAEAtlas hA' hle (mem_insert Φ A)
  exact mem_support.2 ⟨Φ, hΦmem, by rw [hΦs]; trivial⟩

/-- **The ray over a point is regular only if the point is**, for a compact link: if `(x, t)`,
`t > 0`, is regular in `susp_{(G,X)}(Σ)`, then `x ∈ Reg Σ`. A chart `ψ` of the maximal atlas
at `(x, t)` is, on the regular part of a box `B × ]l, u[` around it, `g₀ h · φ⁻¹ ∘ susp*(e)` for
ONE `g₀ ∈ G` (the regular part is preconnected, `Reg Σ` being portly) and charts `e` of `Σ`,
`h ∈ H`; so `F = φ ∘ g₀⁻¹ ∘ ψ` preserves the radius there, hence on the whole box by density,
and `g₀⁻¹ψ` lands in `φ⁻¹(L × [t/2, 2t])`, compact by `CompactSpace L`, hence closed and inside
`U`. Then `z ↦ π F(z, t)` is a chart of `Σ` at `x`, compatible with `Σ`'s maximal atlas. No
invariance of domain is needed: `F` is a homeomorphism of the box onto an open set. -/
theorem mem_reg_of_mk_mem_reg [T2Space X] [ContinuousConstSMul G X] [IsRigidAction G X]
    [LocallyConnectedSpace X] [LocallyConnectedSpace L] [CompactSpace L] [PreconnectedSpace S]
    [LocallyConnectedSpace S] (hf : c.IsFull) {x : S} {t : ℝ≥0} (ht : 0 < t)
    (hreg : letI := c.celestialStructure S hf; Susp.mk (x, t) ∈ Reg G X (Susp S)) :
    x ∈ Reg H L S := by
  haveI := c.continuousConstSMul
  haveI : IsRigidAction H L := c.isRigidAction
  set A := c.celestialAtlas H S with hAdef
  have hA : IsAEAtlas G A := c.isAEAtlas_celestialAtlas hf
  have hM : IsMaximalAEAtlas G (maximalAEAtlas G A) := hA.isMaximalAEAtlas_maximalAEAtlas
  have hAM : A ⊆ maximalAEAtlas G A := hA.subset_maximalAEAtlas
  have hSig := isMaximalAEAtlas_aeAtlas H L S
  obtain ⟨ψ, hψ, hxψ⟩ := mem_support.1 hreg
  change ψ ∈ maximalAEAtlas G A at hψ
  have htgt : ∀ a, a ∈ c.φ.target := fun a => by rw [show c.φ.target = univ from hf]; trivial
  have hconesrc : ∀ {e : OpenPartialHomeomorph S L} {q : S × ℝ≥0}, q.1 ∈ e.source → 0 < q.2 →
      Susp.mk q ∈ (c.coneChart e).source := fun {e q} h1 h2 => by
    rw [c.coneChart_source_of_isFull hf]; exact ⟨q, ⟨h1, h2⟩, rfl⟩
  -- a box `B × ]l, u[` around `(x, t)` inside `ψ`'s source, with radii in `]t/2, 2t[`
  have hbox : Susp.mk ⁻¹' ψ.source ∩ (univ ×ˢ Ioo (t / 2) (2 * t)) ∈ 𝓝 (x, t) := by
    refine inter_mem ((ψ.open_source.preimage Susp.continuous_mk).mem_nhds hxψ) ?_
    exact prod_mem_nhds univ_mem (Ioo_mem_nhds (half_lt_self ht.ne')
      (by rw [two_mul]; exact lt_add_of_pos_left t ht))
  obtain ⟨B, l, u, hBo, hBc, hxB, htI, hsub, hpos⟩ := Susp.exists_box ht hbox
  set I : Set ℝ≥0 := Ioo l u with hIdef
  replace htI : t ∈ I := htI
  replace hxB : x ∈ B := hxB
  -- the compact `φ⁻¹(L × [t/2, 2t])`, closed in `X`, inside `U`
  set K : Set (Susp L) := Susp.mk '' (univ ×ˢ Icc (t / 2) (2 * t)) with hKdef
  have hK : IsCompact K := (isCompact_univ.prod isCompact_Icc).image Susp.continuous_mk
  set C : Set X := c.φ.symm '' K with hCdef
  have hC : IsClosed C :=
    (hK.image_of_continuousOn (c.φ.continuousOn_symm.mono fun a _ => htgt a)).isClosed
  have hCU : C ⊆ c.φ.source := by rintro _ ⟨a, -, rfl⟩; exact c.φ.map_target (htgt a)
  -- the regular part of the box, preconnected
  set Ω : Set (S × ℝ≥0) := (B ∩ Reg H L S) ×ˢ I with hΩdef
  have hΩc : IsPreconnected Ω :=
    ((isPortly_reg H L S).locallyConnectedIn B hBo hBc.isPreconnected).prod isPreconnected_Ioo
  -- `Q q g`: near `(q.1, q.2)`, `ψ` is `g h` times a cone chart, for some `h ∈ H`
  let Q : S × ℝ≥0 → G → Prop := fun q g => ∃ e ∈ aeAtlas H L S, ∃ h : H, q.1 ∈ e.source ∧
    ∀ᶠ y in 𝓝 (Susp.mk q), ψ y = (g * (h : G)) • c.coneChart e y
  have hloc : ∀ q ∈ Ω, ∃ k : G, ∀ᶠ q' in 𝓝 q, ∀ g : G,
      Q q' g ↔ ∃ h : H, ∀ z : X, (g * (h : G)) • z = k • z := by
    rintro q ⟨⟨hqB, hqR⟩, hqI⟩
    obtain ⟨e₀, he₀, hqe₀⟩ := mem_support.1 hqR
    have hq2 : 0 < q.2 := hpos ⟨hqB, hqI⟩
    obtain ⟨k, hk⟩ := hM.1.1.eventually_smul_eq (hAM ⟨e₀, he₀, rfl⟩) hψ (hconesrc hqe₀ hq2)
      (hsub ⟨hqB, hqI⟩).1
    refine ⟨k, ?_⟩
    have hk' : ∀ᶠ q' in 𝓝 q, ∀ᶠ y in 𝓝 (Susp.mk q'), ψ y = k • c.coneChart e₀ y :=
      (Susp.continuous_mk.tendsto q).eventually (eventually_eventually_nhds.2 hk)
    filter_upwards [hk', (e₀.open_source.preimage continuous_fst).mem_nhds hqe₀,
      Susp.isOpen_posPart.mem_nhds hq2] with q' hq'k hq'e₀ hq'2 g
    constructor
    · rintro ⟨e, he, h, hq'e, hev⟩
      obtain ⟨h', hh'⟩ := c.eventually_coneChart_eq_smul hf he₀ he
        ⟨hconesrc hq'e₀ hq'2, hconesrc hq'e hq'2⟩
      have hev' : ∀ᶠ y in 𝓝 (Susp.mk q'),
          (g * (h : G) * (h' : G)) • c.coneChart e₀ y = k • c.coneChart e₀ y := by
        filter_upwards [hev, hh', hq'k] with y hy hy' hy''
        rw [mul_smul, ← hy', ← hy, hy'']
      have hev'' : ∀ᶠ z in 𝓝 (c.coneChart e₀ (Susp.mk q')),
          (g * (h : G) * (h' : G)) • z = k • z := by
        rw [← (c.coneChart e₀).map_nhds_eq (hconesrc hq'e₀ hq'2)]; exact hev'
      obtain ⟨W, hWsub, hWo, hzW⟩ := mem_nhds_iff.1 hev''
      refine ⟨h * h', fun z => ?_⟩
      rw [Subgroup.coe_mul, ← mul_assoc]
      exact IsRigidAction.smul_eq_of_eqOn hWo ⟨_, hzW⟩ (fun z hz => hWsub hz) z
    · rintro ⟨h, hh⟩
      refine ⟨e₀, he₀, h, hq'e₀, ?_⟩
      filter_upwards [hq'k] with y hy
      rw [hy, hh]
  -- one `g₀` on all of `Ω`, by connectedness
  obtain ⟨x₀, hx₀B, hx₀R⟩ : (B ∩ Reg H L S).Nonempty := by
    obtain ⟨y, hyB, hyR⟩ := (isPortly_reg H L S).dense.inter_open_nonempty B hBo ⟨x, hxB⟩
    exact ⟨y, hyB, hyR⟩
  have hq₀ : (x₀, t) ∈ Ω := ⟨⟨hx₀B, hx₀R⟩, htI⟩
  obtain ⟨g₀, hg₀⟩ := hloc _ hq₀
  have hQ₀ : Q (x₀, t) g₀ := (hg₀.self_of_nhds g₀).2 ⟨1, fun z => by rw [Subgroup.coe_one, mul_one]⟩
  have hQ : ∀ q ∈ Ω, Q q g₀ := by
    intro q hq
    refine hΩc.induction₂' (fun q q' => ∀ g, Q q g → Q q' g) (fun q hq => ?_)
      (fun _ _ _ _ _ _ h₁ h₂ g hg => h₂ g (h₁ g hg)) hq₀ hq g₀ hQ₀
    obtain ⟨k, hk⟩ := hloc q hq
    have hkq := hk.self_of_nhds
    filter_upwards [mem_nhdsWithin_of_mem_nhds hk] with q' hq'
    exact ⟨fun g hg => (hq' g).2 ((hkq g).1 hg), fun g hg => (hkq g).2 ((hq' g).1 hg)⟩
  -- the map `F = g₀⁻¹ ψ` on the box, read in coordinates
  set Fx : S × ℝ≥0 → X := fun q => g₀⁻¹ • ψ (Susp.mk q) with hFxdef
  have hΩsub : Ω ⊆ B ×ˢ I := fun q hq => ⟨hq.1.1, hq.2⟩
  have hFΩ : ∀ q ∈ Ω, Fx q ∈ C ∧ (c.φ (Fx q)).r = q.2 := by
    intro q hq
    obtain ⟨e, he, h, hqe, hev⟩ := hQ q hq
    have hq2 : 0 < q.2 := hpos (hΩsub hq)
    have e1 : Fx q = c.φ.symm (Susp.mk ((h : H) • e q.1, q.2)) := by
      show g₀⁻¹ • ψ (Susp.mk q) = _
      rw [hev.self_of_nhds, c.coneChart_apply, c.symm_mk_smul hf, mul_smul, inv_smul_smul]
    refine ⟨?_, ?_⟩
    · rw [e1]
      have hI := (hsub (hΩsub hq)).2
      exact ⟨_, ⟨(_, q.2), ⟨mem_univ _, ⟨hI.2.1.le, hI.2.2.le⟩⟩, rfl⟩, rfl⟩
    · rw [e1, c.φ.right_inv (htgt _)]; rfl
  have hBIo : IsOpen (B ×ˢ I) := hBo.prod isOpen_Ioo
  have hFc : ∀ q ∈ B ×ˢ I, ContinuousAt Fx q := fun q hq =>
    (continuous_const_smul g₀⁻¹).continuousAt.comp
      ((ψ.continuousAt (hsub hq).1).comp Susp.continuous_mk.continuousAt)
  have hcl : B ×ˢ I ⊆ closure Ω := by
    have := ((isPortly_reg H L S).dense.prod dense_univ).open_subset_closure_inter hBIo
    rwa [prod_inter_prod, inter_univ] at this
  have hFC : ∀ q ∈ B ×ˢ I, Fx q ∈ C := fun q hq =>
    hC.closure_subset_iff.2 (image_subset_iff.2 fun q' hq' => (hFΩ q' hq').1)
      (mem_closure_image (hFc q hq) (hcl hq))
  have hFr : ∀ q ∈ B ×ˢ I, (c.φ (Fx q)).r = q.2 := by
    intro q hq
    set Φ : S × ℝ≥0 → ℝ≥0 × ℝ≥0 := fun q => ((c.φ (Fx q)).r, q.2)
    have hΦ : ContinuousAt Φ q :=
      (Susp.continuous_r.continuousAt.comp ((c.φ.continuousAt (hCU (hFC q hq))).comp
        (hFc q hq))).prodMk continuous_snd.continuousAt
    have hmem := mem_closure_image hΦ (hcl hq)
    have hsubd : Φ '' Ω ⊆ diagonal ℝ≥0 := by
      rintro _ ⟨q', hq', rfl⟩; exact (hFΩ q' hq').2
    exact isClosed_diagonal.closure_subset_iff.2 hsubd hmem
  -- `F = φ ∘ g₀⁻¹ ∘ ψ` on the box, a radius-preserving open partial homeomorphism
  have hBIo' : IsOpen (Susp.mk '' (B ×ˢ I)) := Susp.isOpen_image_mk hBIo hpos
  set F : OpenPartialHomeomorph (Susp S) (Susp L) :=
    ((ψ.trans (Homeomorph.smul g₀⁻¹).toOpenPartialHomeomorph).trans c.φ).restrOpen
      (Susp.mk '' (B ×ˢ I)) hBIo' with hFdef
  have hFapp : ∀ q, F (Susp.mk q) = c.φ (Fx q) := fun q => rfl
  have hFsrc : ∀ q ∈ B ×ˢ I, Susp.mk q ∈ F.source := fun q hq =>
    ⟨⟨⟨(hsub hq).1, mem_univ _⟩, hCU (hFC q hq)⟩, ⟨q, hq, rfl⟩⟩
  have hFsrc' : ∀ w ∈ F.source, ∃ q ∈ B ×ˢ I, w = Susp.mk q := by
    rintro w ⟨-, ⟨q, hq, rfl⟩⟩; exact ⟨q, hq, rfl⟩
  have hFr' : ∀ z ∈ B, Susp.mk ((F (Susp.mk (z, t))).dir, t) = F (Susp.mk (z, t)) := by
    intro z hz
    conv_rhs => rw [← Susp.mk_dir_r (F (Susp.mk (z, t)))]
    rw [hFapp, hFr (z, t) ⟨hz, htI⟩]
  -- the chart `e'` of `Σ` at `x`: `e'(z) = π F(z, t)`
  let e' : OpenPartialHomeomorph S L :=
    { toFun := fun z => (F (Susp.mk (z, t))).dir
      invFun := fun σ => (F.symm (Susp.mk (σ, t))).dir
      source := B
      target := (fun σ : L => Susp.mk (σ, t)) ⁻¹' F.target
      map_source' := fun z hz => by
        show Susp.mk ((F (Susp.mk (z, t))).dir, t) ∈ F.target
        rw [hFr' z hz]; exact F.map_source (hFsrc _ ⟨hz, htI⟩)
      map_target' := fun σ hσ => by
        obtain ⟨q, hq, hqe⟩ := hFsrc' _ (F.map_target hσ)
        show (F.symm (Susp.mk (σ, t))).dir ∈ B
        rw [hqe, Susp.dir_mk_of_pos (hpos hq)]; exact hq.1
      left_inv' := fun z hz => by
        show (F.symm (Susp.mk ((F (Susp.mk (z, t))).dir, t))).dir = z
        rw [hFr' z hz, F.left_inv (hFsrc _ ⟨hz, htI⟩), Susp.dir_mk_of_pos ht]
      right_inv' := fun σ hσ => by
        have hσ' : Susp.mk (σ, t) ∈ F.target := hσ
        obtain ⟨q, hq, hqe⟩ := hFsrc' _ (F.map_target hσ')
        have hFq : F (Susp.mk q) = Susp.mk (σ, t) := by rw [← hqe]; exact F.right_inv hσ'
        have hq2 : q.2 = t := by
          have := hFr q hq
          rw [← hFapp, hFq, Susp.r_mk] at this
          exact this.symm
        show (F (Susp.mk ((F.symm (Susp.mk (σ, t))).dir, t))).dir = σ
        rw [hqe, Susp.dir_mk_of_pos (hpos hq), ← hq2, hFq, Susp.dir_mk_of_pos ht]
      open_source := hBo
      open_target := F.open_target.preimage (Susp.continuous_mk_left t)
      continuousOn_toFun := fun z hz => by
        refine ContinuousAt.continuousWithinAt ?_
        have h1 : ContinuousAt (fun z : S => F (Susp.mk (z, t))) z :=
          ContinuousAt.comp (g := F) (f := fun z : S => Susp.mk (z, t))
            (F.continuousAt (hFsrc (z, t) ⟨hz, htI⟩)) (Susp.continuous_mk_left t).continuousAt
        refine ContinuousAt.comp (g := Susp.dir) (f := fun z : S => F (Susp.mk (z, t))) ?_ h1
        refine Susp.continuousAt_dir ?_
        show 0 < (F (Susp.mk (z, t))).r
        rw [hFapp, hFr (z, t) ⟨hz, htI⟩]; exact ht
      continuousOn_invFun := fun σ hσ => by
        have hσ' : Susp.mk (σ, t) ∈ F.target := hσ
        refine ContinuousAt.continuousWithinAt ?_
        have h1 : ContinuousAt (fun σ : L => F.symm (Susp.mk (σ, t))) σ :=
          ContinuousAt.comp (g := F.symm) (f := fun σ : L => Susp.mk (σ, t))
            (F.continuousAt_symm hσ') (Susp.continuous_mk_left t).continuousAt
        refine ContinuousAt.comp (g := Susp.dir) (f := fun σ : L => F.symm (Susp.mk (σ, t))) ?_ h1
        obtain ⟨q, hq, hqe⟩ := hFsrc' _ (F.map_target hσ')
        refine Susp.continuousAt_dir ?_
        show 0 < (F.symm (Susp.mk (σ, t))).r
        rw [hqe, Susp.r_mk]; exact hpos hq }
  -- `e'` is compatible with every chart of `Σ`: near `y`, `e' = h · e` for the `e, h` of `Q`
  have he' : e' ∈ aeAtlas H L S := by
    refine hSig.mem_of_compatible fun c' hc' y hy => ?_
    have hyB : y ∈ B := hy.1
    have hyR : y ∈ Reg H L S := mem_support.2 ⟨c', hc', hy.2⟩
    obtain ⟨e, he, h, hye, hev⟩ := hQ (y, t) ⟨⟨hyB, hyR⟩, htI⟩
    obtain ⟨h', hh'⟩ := hSig.1.1.eventually_smul_eq he hc' hye hy.2
    have hev' := ((Susp.continuous_mk_left t).tendsto y).eventually hev
    refine ⟨h' * h⁻¹, ?_⟩
    filter_upwards [hev', hh', e.open_source.mem_nhds hye, hBo.mem_nhds hyB] with z hz hz' hze hzB
    show c' z = (h' * h⁻¹) • (F (Susp.mk (z, t))).dir
    have hFz : F (Susp.mk (z, t)) = Susp.mk (h • e z, t) := by
      rw [hFapp]
      show c.φ (g₀⁻¹ • ψ (Susp.mk (z, t))) = _
      rw [hz, c.coneChart_apply, mul_smul, inv_smul_smul, ← c.symm_mk_smul hf,
        c.φ.right_inv (htgt _)]
    rw [hFz, Susp.dir_mk_of_pos ht, hz', mul_smul, inv_smul_smul]
  exact mem_support.2 ⟨e', he', hxB⟩

/-- **The ray over a singular point is singular** (with the added `CompactSpace L`). -/
theorem mk_mem_sing [T2Space X] [ContinuousConstSMul G X] [IsRigidAction G X]
    [LocallyConnectedSpace X] [LocallyConnectedSpace L] [CompactSpace L] [PreconnectedSpace S]
    [LocallyConnectedSpace S] (hf : c.IsFull) {x : S} (hx : x ∈ Sing H L S) {t : ℝ≥0}
    (ht : 0 < t) :
    letI := c.celestialStructure S hf
    Susp.mk (x, t) ∈ Sing G X (Susp S) :=
  fun h => hx (c.mem_reg_of_mk_mem_reg hf ht h)

/-- **Regular rays are exactly the rays over regular points** (`RamcovGX.tex:740`, "the image of
regular `(G,X)`-manifolds are regular except possibly at `O`", off the apex), for a compact
link. -/
theorem mk_mem_reg_iff [T2Space X] [ContinuousConstSMul G X] [IsRigidAction G X]
    [LocallyConnectedSpace X] [LocallyConnectedSpace L] [CompactSpace L] [PreconnectedSpace S]
    [LocallyConnectedSpace S] (hf : c.IsFull) {x : S} {t : ℝ≥0} (ht : 0 < t) :
    letI := c.celestialStructure S hf
    Susp.mk (x, t) ∈ Reg G X (Susp S) ↔ x ∈ Reg H L S :=
  ⟨c.mem_reg_of_mk_mem_reg hf ht, fun hx => c.mk_mem_reg hf hx ht⟩

end ConicStructure

/-! ### Witness: the suspension over the tautological conic structure -/

/-- The radial extension of a rigid action is rigid. -/
theorem Susp.isRigidAction_radialAction (K L : Type*) [Group K] [TopologicalSpace L]
    [MulAction K L] [IsRigidAction K L] :
    letI := Susp.radialAction K (S := L); IsRigidAction K (Susp L) := by
  letI := Susp.radialAction K (S := L)
  refine ⟨fun {g h U} hU hne heq a => ?_⟩
  obtain ⟨a₀, ha₀⟩ := hne
  obtain ⟨q, hq, hqU⟩ : ∃ q : L × ℝ≥0, 0 < q.2 ∧ Susp.mk q ∈ U := by
    obtain ⟨q₀, rfl⟩ := Susp.mk_surjective a₀
    rcases eq_zero_or_pos q₀.2 with h0 | hpos
    · obtain ⟨ε, hε, hεU⟩ := Susp.exists_ball_subset_of_isOpen hU
        (show Susp.mk q₀ ∈ (Susp.O : Set (Susp L)) from h0) ha₀
      exact ⟨(q₀.1, ε / 2), half_pos hε, hεU (show ε / 2 < ε from half_lt_self hε.ne')⟩
    · exact ⟨q₀, hpos, ha₀⟩
  have hW : IsOpen {σ : L | Susp.mk (σ, q.2) ∈ U} := hU.preimage (Susp.continuous_mk_left _)
  have hall : ∀ σ : L, g • σ = h • σ := IsRigidAction.smul_eq_of_eqOn hW ⟨q.1, hqU⟩
    fun σ hσ => by
      have e : Susp.mk (g • σ, q.2) = Susp.mk (h • σ, q.2) := heq hσ
      exact (Prod.ext_iff.1 (Susp.eq_of_mk_eq_of_pos e hq)).1
  obtain ⟨q', rfl⟩ := Susp.mk_surjective a
  show Susp.mk (g • q'.1, q'.2) = Susp.mk (h • q'.1, q'.2)
  rw [hall]

/-- The radial extension of an action by homeomorphisms is by homeomorphisms. -/
theorem Susp.continuousConstSMul_radialAction (K L : Type*) [Group K] [TopologicalSpace L]
    [MulAction K L] [ContinuousConstSMul K L] :
    letI := Susp.radialAction K (S := L); ContinuousConstSMul K (Susp L) :=
  letI := Susp.radialAction K (S := L)
  ⟨fun k => Susp.continuous_map (continuous_const_smul k)⟩

/-- **Witness** (non-vacuity of `celestialStructure`): for a rigid action of `K` on a Hausdorff
locally connected `L`, every connected, locally connected singular `(K, L)`-manifold `Σ` has a
`(K, susp L)`-suspension céleste, over the tautological conic structure at the apex. -/
@[reducible] def ConicStructure.tautologicalSuspension (K L S : Type*) [Group K]
    [TopologicalSpace L] [MulAction K L] [IsRigidAction K L] [ContinuousConstSMul K L] [T2Space L]
    [LocallyConnectedSpace L] (σ₀ : L) [TopologicalSpace S] [PreconnectedSpace S]
    [LocallyConnectedSpace S] [SingularGXStructure (⊤ : Subgroup K) L S] :
    letI := Susp.radialAction K (S := L); SingularGXStructure K (Susp L) (Susp S) :=
  letI := Susp.radialAction K (S := L)
  haveI := Susp.isRigidAction_radialAction K L
  haveI := Susp.continuousConstSMul_radialAction K L
  (ConicStructure.tautological K L σ₀).celestialStructure S
    (ConicStructure.tautological_isFull K L σ₀)

/-! ### The draft's ray condition does not suffice: a counterexample motivating `ConicStructure` -/

namespace Susp

variable {S : Type*}

/-- Radial rescaling by a function of the direction, `(σ, r) ↦ (σ, ρ(σ) r)`. -/
def scale (ρ : S → ℝ≥0) : Susp S → Susp S :=
  Quotient.lift (fun q : S × ℝ≥0 => mk (q.1, ρ q.1 * q.2)) fun a b h => by
    rcases (h : a = b ∨ (a.2 = 0 ∧ b.2 = 0)) with rfl | ⟨ha, hb⟩
    · rfl
    · exact mk_eq_mk.2 (Or.inr ⟨by simp [ha], by simp [hb]⟩)

theorem scale_mk (ρ : S → ℝ≥0) (q : S × ℝ≥0) : scale ρ (mk q) = mk (q.1, ρ q.1 * q.2) := rfl

theorem scale_scale {ρ ρ' : S → ℝ≥0} (h : ∀ s, ρ' s * ρ s = 1) (a : Susp S) :
    scale ρ' (scale ρ a) = a := by
  obtain ⟨q, rfl⟩ := mk_surjective a
  show mk (q.1, ρ' q.1 * (ρ q.1 * q.2)) = mk q
  rw [← mul_assoc, h, one_mul]

/-- A bounded continuous rescaling is continuous on `susp(Σ)`. -/
theorem continuous_scale [TopologicalSpace S] {ρ : S → ℝ≥0} (hρ : Continuous ρ) {B : ℝ≥0}
    (hB : ∀ s, ρ s ≤ B) : Continuous (scale ρ) := by
  refine continuous_of (fun q _ => ?_) fun x hx V hV => ?_
  · exact (continuous_mk.comp (continuous_fst.prodMk
      ((hρ.comp continuous_fst).mul continuous_snd))).continuousAt
  · obtain ⟨q, rfl⟩ := mk_surjective x
    have hq : q.2 = 0 := hx
    have hO : scale ρ (mk q) ∈ (O : Set (Susp S)) :=
      show ρ q.1 * q.2 = 0 by rw [hq, mul_zero]
    obtain ⟨δ, hδ, hδV⟩ := (hasBasis_nhds_O hO).mem_iff.1 hV
    have hB1 : (0 : ℝ≥0) < B + 1 := add_pos_of_nonneg_of_pos zero_le one_pos
    refine ⟨δ / (B + 1), div_pos hδ hB1, fun y hy => hδV ?_⟩
    obtain ⟨q', rfl⟩ := mk_surjective y
    have hy' : q'.2 < δ / (B + 1) := hy
    show ρ q'.1 * q'.2 < δ
    calc ρ q'.1 * q'.2 ≤ (B + 1) * q'.2 :=
          mul_le_mul_of_nonneg_right ((hB _).trans le_self_add) zero_le
      _ < δ := (lt_div_iff₀' hB1).1 hy'

end Susp

namespace CelestialCex

/-- The rescaling `ρ(true) = 1`, `ρ(false) = 2` of `susp(Bool)`. -/
def boolRho : Bool → ℝ≥0 := fun b => if b then 1 else 2

/-- Its inverse `ρ'(true) = 1`, `ρ'(false) = 1/2`. -/
def boolRho' : Bool → ℝ≥0 := fun b => if b then 1 else 2⁻¹

theorem boolRho'_mul (b : Bool) : boolRho' b * boolRho b = 1 := by
  cases b <;> simp [boolRho, boolRho']

theorem boolRho_mul (b : Bool) : boolRho b * boolRho' b = 1 := by
  cases b <;> simp [boolRho, boolRho']

/-- The non-radial self-homeomorphism `(b, r) ↦ (b, ρ'(b) r)` of `susp(Bool) ≅ ℝ`. -/
def boolScale : Susp Bool ≃ₜ Susp Bool where
  toFun := Susp.scale boolRho'
  invFun := Susp.scale boolRho
  left_inv := Susp.scale_scale boolRho_mul
  right_inv := Susp.scale_scale boolRho'_mul
  continuous_toFun := Susp.continuous_scale continuous_of_discreteTopology (B := 1)
    fun b => by cases b <;> simp [boolRho']
  continuous_invFun := Susp.continuous_scale continuous_of_discreteTopology (B := 2)
    fun b => by cases b <;> simp [boolRho]

theorem perm_bool_not (σ : Equiv.Perm Bool) (b : Bool) : σ (!b) = !(σ b) :=
  Bool.eq_not_of_ne fun h => by
    have := σ.injective h
    cases b <;> simp at this

/-- `Perm Bool` acts rigidly on `Bool`. -/
theorem isRigidAction_perm_bool : IsRigidAction (Equiv.Perm Bool) Bool := by
  refine ⟨fun {g h U} _ hne heq q => ?_⟩
  obtain ⟨b, hb⟩ := hne
  have e : g b = h b := heq hb
  by_cases hq : q = b
  · subst hq; exact e
  · have : q = !b := Bool.eq_not_of_ne hq
    subst this
    show g (!b) = h (!b)
    rw [perm_bool_not, perm_bool_not, e]

/-- A point `Unit` as a singular `(⊤, Bool)`-manifold: its one chart sends the point to `b`. -/
def unitChart (b : Bool) : OpenPartialHomeomorph Unit Bool where
  toFun _ := b
  invFun _ := ()
  source := univ
  target := {b}
  map_source' _ _ := rfl
  map_target' _ _ := trivial
  left_inv' _ _ := rfl
  right_inv' _ hx := hx.symm
  open_source := isOpen_univ
  open_target := isOpen_discrete _
  continuousOn_toFun := continuous_const.continuousOn
  continuousOn_invFun := continuous_const.continuousOn

/-- The point as a `(⊤, Bool)`-manifold (`⊤ = Perm Bool`): one chart, `unitChart true`. -/
@[reducible] def unitStructure :
    SingularGXStructure (⊤ : Subgroup (Equiv.Perm Bool)) Bool Unit :=
  haveI : ContinuousConstSMul (⊤ : Subgroup (Equiv.Perm Bool)) Bool :=
    ⟨fun _ => continuous_of_discreteTopology⟩
  haveI := isRigidAction_perm_bool
  letI : ChartedSpace Bool Unit :=
    { atlas := {unitChart true}
      chartAt := fun _ => unitChart true
      mem_chart_source := fun _ => trivial
      chart_mem_atlas := fun _ => rfl }
  haveI : HasGroupoid Unit (gxGroupoid (⊤ : Subgroup (Equiv.Perm Bool)) Bool) :=
    ⟨fun {e e'} he he' => by
      rw [show e = unitChart true from he, show e' = unitChart true from he']
      exact symm_trans_mem_gxGroupoid fun _ _ => ⟨1, Eventually.of_forall fun _ => rfl⟩⟩
  SingularGXStructure.ofHasGroupoid (⊤ : Subgroup (Equiv.Perm Bool)) Bool Unit

theorem unitChart_mem (b : Bool) :
    unitChart b ∈ @aeAtlas (⊤ : Subgroup (Equiv.Perm Bool)) Bool _ _ _ Unit _ unitStructure := by
  haveI : ContinuousConstSMul (⊤ : Subgroup (Equiv.Perm Bool)) Bool :=
    ⟨fun _ => continuous_of_discreteTopology⟩
  letI : ChartedSpace Bool Unit :=
    { atlas := {unitChart true}
      chartAt := fun _ => unitChart true
      mem_chart_source := fun _ => trivial
      chart_mem_atlas := fun _ => rfl }
  haveI : HasGroupoid Unit (gxGroupoid (⊤ : Subgroup (Equiv.Perm Bool)) Bool) :=
    ⟨fun {e e'} he he' => by
      rw [show e = unitChart true from he, show e' = unitChart true from he']
      exact symm_trans_mem_gxGroupoid fun _ _ => ⟨1, Eventually.of_forall fun _ => rfl⟩⟩
  show unitChart b ∈ (gxGroupoid (⊤ : Subgroup (Equiv.Perm Bool)) Bool).maximalAtlas Unit
  refine mem_maximalAtlas_iff_eventually.2 fun x _ => ?_
  refine ⟨⟨Equiv.swap true b, Subgroup.mem_top _⟩, Eventually.of_forall fun z => ?_⟩
  show b = (Equiv.swap true b) true
  rw [Equiv.swap_apply_left]

end CelestialCex

open CelestialCex in
/-- **The draft's suspension proposition, read literally, fails under its ray condition** (a
counterexample motivating the radius hypothesis of `ConicStructure`; the draft is the
commented-out `these.tex:3569`/`3645`, not part of the thesis). On `X = susp(Bool)` (`≅ ℝ`) with
`G = Perm Bool` acting radially (`Susp.radialAction`), the chart `φ = boolScale` at the apex is
full, satisfies the draft's ray
condition for `⊤ = Stab_G(p)`, and induces the natural action of `Perm Bool` on the link `Bool`;
yet over the point `Σ = Unit` (a connected singular `(⊤, Bool)`-manifold) the cone préatlas
`φ⁻¹ ∘ susp*(φ_i)` is NOT a `(G,X)`-atlas: the cone charts of `unitChart true` and of
`unitChart false` reach radii `1` and `2` at the same point, and `G` preserves radii. -/
theorem celestial_counterexample :
    letI := Susp.radialAction (Equiv.Perm Bool) (S := Bool)
    letI := unitStructure
    ∃ c : ConicChart (Susp Bool) (Susp.mk (true, 0) : Susp Bool) Bool,
      c.IsFull ∧ c.IsRayCompatible (⊤ : Subgroup (Equiv.Perm Bool)) ∧
      (∀ h : (⊤ : Subgroup (Equiv.Perm Bool)), ∀ x ∈ c.φ.source,
        (h : Equiv.Perm Bool) • x ∈ c.φ.source → c.φ x ∉ Susp.O →
          (c.φ ((h : Equiv.Perm Bool) • x)).dir = h • (c.φ x).dir) ∧
      ¬ IsGXAtlas (Equiv.Perm Bool) (c.celestialAtlas (⊤ : Subgroup (Equiv.Perm Bool)) Unit) := by
  letI := Susp.radialAction (Equiv.Perm Bool) (S := Bool)
  letI := unitStructure
  let c : ConicChart (Susp Bool) (Susp.mk (true, 0) : Susp Bool) Bool :=
    { φ := boolScale.toOpenPartialHomeomorph
      mem_source := trivial
      map_mem_O := show boolRho' true * 0 = 0 from mul_zero _ }
  -- `φ` keeps the direction and the vanishing of the radius
  have hr0 : ∀ a : Susp Bool, c.φ a ∉ Susp.O → 0 < a.r := fun a ha => by
    obtain ⟨q, rfl⟩ := Susp.mk_surjective a
    rw [Susp.notMem_O_iff] at ha
    have ha' : 0 < boolRho' q.1 * q.2 := ha
    exact pos_of_mul_pos_right ha' zero_le
  have hdir : ∀ a : Susp Bool, 0 < a.r → (c.φ a).dir = a.dir := fun a ha => by
    obtain ⟨q, rfl⟩ := Susp.mk_surjective a
    have hq : 0 < q.2 := ha
    have hρ : 0 < boolRho' q.1 := by cases q.1 <;> simp [boolRho']
    show (Susp.mk (q.1, boolRho' q.1 * q.2)).dir = (Susp.mk q).dir
    rw [Susp.dir_mk_of_pos (mul_pos hρ hq), Susp.dir_mk_of_pos hq]
  have hsmul : ∀ (g : Equiv.Perm Bool) (a : Susp Bool), g • a = Susp.map (fun b => g • b) a :=
    fun _ _ => rfl
  have hdirsmul : ∀ (h : (⊤ : Subgroup (Equiv.Perm Bool))) (x : Susp Bool), c.φ x ∉ Susp.O →
      (c.φ ((h : Equiv.Perm Bool) • x)).dir = h • (c.φ x).dir := fun h x hx => by
    have hx' := hr0 x hx
    have hhx : 0 < ((h : Equiv.Perm Bool) • x).r := by rw [hsmul, Susp.r_map]; exact hx'
    rw [hdir _ hhx, hdir _ hx', hsmul, Susp.dir_map_of_pos _ hx']
    rfl
  refine ⟨c, Homeomorph.toOpenPartialHomeomorph_target _, ?_, fun h x _ _ hx => hdirsmul h x hx,
    ?_⟩
  · intro h hh x _ y _ _ _ hx hy hxy
    rw [hdirsmul ⟨h, hh⟩ x hx, hdirsmul ⟨h, hh⟩ y hy, hxy]
  · intro hGX
    have hf : c.IsFull := Homeomorph.toOpenPartialHomeomorph_target _
    set z : Susp Unit := Susp.mk ((), 1)
    have hz : ∀ b, z ∈ (c.coneChart (unitChart b)).source := fun b => by
      rw [c.coneChart_source_of_isFull hf]
      exact ⟨((), 1), ⟨trivial, show (0 : ℝ≥0) < 1 from one_pos⟩, rfl⟩
    obtain ⟨g, hg⟩ := hGX _ ⟨_, unitChart_mem true, rfl⟩ _ ⟨_, unitChart_mem false, rfl⟩ z
      ⟨hz true, hz false⟩
    have e := congrArg Susp.r (hg z (mem_connectedComponentIn ⟨hz true, hz false⟩))
    rw [hsmul, Susp.r_map] at e
    change boolRho false * 1 = boolRho true * 1 at e
    simp [boolRho] at e

open CelestialCex in
/-- The hypotheses of the draft hold in `celestial_counterexample`: `Perm Bool` acts on
`susp(Bool)` by homeomorphisms, faithfully and rigidly (an analytic structure, `these.tex:1185`;
`susp(Bool)` is Hausdorff and locally connected by instance), and `⊤` is the full stabiliser
`G_p` of the apex — the draft's own choice of subgroup. -/
theorem celestial_counterexample_hypotheses :
    letI := Susp.radialAction (Equiv.Perm Bool) (S := Bool)
    ContinuousConstSMul (Equiv.Perm Bool) (Susp Bool) ∧
      IsAnalyticAction (Equiv.Perm Bool) (Susp Bool) ∧
      (⊤ : Subgroup (Equiv.Perm Bool)) =
        MulAction.stabilizer (Equiv.Perm Bool) (Susp.mk (true, 0) : Susp Bool) := by
  letI := Susp.radialAction (Equiv.Perm Bool) (S := Bool)
  have hsmul : ∀ (g : Equiv.Perm Bool) (a : Susp Bool), g • a = Susp.map (fun b => g • b) a :=
    fun _ _ => rfl
  have hF : FaithfulSMul (Equiv.Perm Bool) (Susp Bool) := by
    refine ⟨fun {g h} heq => ?_⟩
    ext b
    have := heq (Susp.mk (b, 1))
    rw [hsmul, hsmul, Susp.map_mk, Susp.map_mk] at this
    exact (Prod.ext_iff.1 (Susp.eq_of_mk_eq_of_pos this (by simp))).1
  have hR : IsRigidAction (Equiv.Perm Bool) (Susp Bool) := by
    refine ⟨fun {g h U} hU hne heq a => ?_⟩
    -- `U` contains a point off the apex
    obtain ⟨a₀, ha₀⟩ := hne
    obtain ⟨b, t, ht, hbU⟩ : ∃ b : Bool, ∃ t : ℝ≥0, 0 < t ∧ Susp.mk (b, t) ∈ U := by
      obtain ⟨q, rfl⟩ := Susp.mk_surjective a₀
      rcases eq_zero_or_pos q.2 with h0 | hpos
      · obtain ⟨ε, hε, hεU⟩ := Susp.exists_ball_subset_of_isOpen hU
          (show Susp.mk q ∈ (Susp.O : Set (Susp Bool)) from h0) ha₀
        exact ⟨true, ε / 2, half_pos hε, hεU (show ε / 2 < ε from half_lt_self hε.ne')⟩
      · exact ⟨q.1, q.2, hpos, ha₀⟩
    have e := heq hbU
    simp only [hsmul, Susp.map_mk] at e
    have hgb : g • b = h • b := (Prod.ext_iff.1 (Susp.eq_of_mk_eq_of_pos e ht)).1
    have hall : ∀ c : Bool, g • c = h • c :=
      isRigidAction_perm_bool.smul_eq_of_eqOn (isOpen_discrete {b}) ⟨b, rfl⟩
        (fun c hc => by rw [show c = b from hc]; exact hgb)
    rw [hsmul, hsmul]
    obtain ⟨q, rfl⟩ := Susp.mk_surjective a
    rw [Susp.map_mk, Susp.map_mk, hall]
  refine ⟨⟨fun g => ?_⟩, { toFaithfulSMul := hF, toIsRigidAction := hR }, ?_⟩
  · rw [show (fun x : Susp Bool => g • x) = Susp.map (fun b => g • b) from rfl]
    exact Susp.continuous_map continuous_of_discreteTopology
  · ext g
    simp only [Subgroup.mem_top, true_iff]
    exact MulAction.mem_stabilizer_iff.2 (Susp.mk_zero_eq _ _)

end GX
