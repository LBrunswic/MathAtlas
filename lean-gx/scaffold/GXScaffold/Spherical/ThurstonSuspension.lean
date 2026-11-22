import GXScaffold.Spherical.TroyanovAngles

/-!
# The Thurston suspension of a cone sphere: its singular locus, its centre, `Aut(Σ) ≅ Aut(susp Σ)`

Target `T-gx-troyanov-suspension` (`roadmap/roadmap.toml`; DEC-175, DEC-69). `papers/gx`,
`cex:start_singular_manifold_homeomorphic` (`RamcovGX.tex:1930–1937`). **No label is marked**;
one tagged `sorry`, (iii) below.

* `cex:start_singular_manifold_homeomorphic` — `RamcovGX.tex:1930` — partial. The obligation
  `GX.thurstonSuspensionFacts` (scaffold `GXScaffold.Spherical.TroyanovAngles`) is restated as
  `GX.thurstonSuspensionFacts'`, of type exactly `GX.ThurstonSuspensionFacts`. It rests on one
  `sorry`, (iii) `GX.IsConeSphere.singularAut_eq_bot`: `Aut(Σ) = {Id}` for pairwise distinct
  angles. The obligation is **equivalent** to (iii) (`GX.thurstonSuspensionFacts_iff`, 0 `sorry`).
  Everything else is proved, 0 `sorry`:
  - the singular locus of `susp(Σ)` is the centre `O` and the open rays over the cone points of
    angle `≠ 2π` (`GX.IsConeSphere.thurston_sing_eq`; rays over singular points are singular,
    `GX.thurston_mem_reg_of_mk_mem_reg`, kb 0007); `O` is singular, some other point is
    (`GX.IsConeSphere.thurston_mem_sing_exists_ne`); `susp(Σ)` is connected;
  - (i) a local isomorphism at `O` fixes `O` (`GX.IsConeSphere.thurston_fixes_centre`);
  - (ii) near `O` it is `susp(f)` for some `f ∈ Aut(Σ)`
    (`GX.IsConeSphere.thurston_eq_susp_near_centre`; its chart changes fix the north pole,
    `GX.thurston_reading_fixes_northPole`);
  - **DEC-175 (c)**, the natural map `Aut(Σ) → Aut(M)` is a group isomorphism:
    `GX.thurstonSuspAut`, `GX.thurstonSuspAut_injective`,
    `GX.IsConeSphere.thurstonSuspAut_bijective`, `GX.IsConeSphere.thurstonSuspAutEquiv`;
  - from `Aut(Σ) = {Id}`: rigidity at `O` (`GX.IsConeSphere.thurston_rigid`), `Aut(M) = {Id}`
    (`GX.IsConeSphere.thurston_singularAut_eq_bot`), the local rotations about the singular rays
    and their non-extension (`GX.IsConeSphere.thurston_exists_local_ne_id`, the half-turn
    `GX.SphCone.halfRot` of the cone suspended; `GX.IsConeSphere.thurston_rot`), all of
    `GX.ThurstonCexFacts` (`GX.IsConeSphere.thurstonCexFacts_of_aut`);
  - OQ-92: the proofs use only "three angles `≠ 2π`", which Theorem C's condition also gives
    (`GX.TroyanovAngleConditionC.three_le_card_ne_two_pi`); the C-form
    `GX.ThurstonSuspensionFactsC` follows from (iii) the same way (`GX.thurstonSuspensionFactsC'`).

> An automorphism of $M$ has to fix $O$ since singular locus is homeomorphic to a line except at
> $O$, furthermore it preserves distances and geodesics. By considering the sphere of some radius
> $\varepsilon>0$ centered at $O$ we see that the natural map $\Aut(\Sigma)\rightarrow \Aut(M)$
> is a group isomorphism. As a consequence, except for very particular $\Sigma$, $\Aut(M)$ is
> trivial. For instance, if all the $\theta_i$ are different then $\Aut(M)=\{Id\}$. These remarks
> hold for all neighborhoods of $O$. (l.1933)
>
> For a generic $\Sigma$, since locally we may construct a rotation around any of the axes and
> since those cannot be extended as automorphism of $M$, we conclude that for
> $S\subset \sing(M)$, $(M,S)$ is analytic if and only if $S=\{O\}$. (l.1935)

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `Σ` a cone sphere, `s ≥ 3` cone points of angles `θ_i` (l.1930) | ✓ `IsConeSphere M θ p` |
| Troyanov's condition (l.1930) | ✓ in the statement of record; ⚠ weakened in the lemmas to "three angles `≠ 2π`", all they use |
| the suspension, a singular `(SO(4), 𝕊³)`-manifold (l.1931) | ✓ `thurstonSuspension`, `r ∈ [0, π)` (DEC-175 (a)) |
| "conical singularities" (l.1930) | ✓ `X_θ`-charts (`IsConePoint`, DEC-175 (b)) |
| "generic `Σ`", "all the `θ_i` different" (l.1933–1935) | ✓ pairwise distinct (DEC-69); not used by (i), (ii), the isomorphism |
| "preserves distances and geodesics" (l.1933) | ✓ derived (SCOPE (b)) |

## SCOPE (disclosed)

* **(a)** The paper's statement is l.1933–1937 as `GX.ThurstonCexFacts` (DEC-69's
  `SuspensionCexFacts` at `O`), unchanged; DEC-175 (c), the isomorphism, is carried beside it,
  for every cone sphere with three angles `≠ 2π` (distinct or not).
* **(b)** No metric is formalized: "preserves distances" is read through the charts. Along a ray
  `s ↦ (σ, s)` the vector `q = g⁻¹N` with `c(r ∘ φ) = ⟨κ, q⟩` (`c(t) = (1-t²)/(1+t²)`, the polar
  coordinate of radius `t`) is locally constant; at `s → 0`, `⟨N, q⟩ = c(0) = 1`, so `g` fixes `N`
  and is `1 ⊕ A` (`GX.exists_liftSO_of_smul_northPole`): `φ` keeps the radius.
* **(c)** (i) uses that the singular locus near `O` is a star of `≥ 3` arcs: two points of a
  connected set of `sing(M) ∖ {O}` lie on one ray (their directions are in a finite set).
* **(d)** "A rotation around any of the axes" is the half-turn of `C_θ` read in an `X_θ`-chart
  and suspended (`GX.thurston_isAEMorphism_posChart`); any local isomorphism moving a point serves.
* **(e)** Not proved: (iii). Its obstruction (the tagged `sorry`) is a fixed-point theorem for
  `𝕊²` not at this mathlib pin (Brouwer–Kerékjártó, or Lefschetz–Hopf).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Builds on
`GXScaffold.Spherical.TroyanovAngles`, `GX.Spherical.S3Model`, `GX.Spherical.ConeSurface`,
`GX.Spherical.TroyanovTheoremC`, `GX.Suspension.Celestial` (the argument of
`ConicStructure.mem_reg_of_mk_mem_reg`), `GX.Singular.Quotient` (`isAEMorphismOf_quotientBase`).
-/

noncomputable section

open Set Filter Topology Function TopologicalSpace NNReal

open scoped Real

namespace GX

set_option linter.unusedSectionVars false

/-! ### The rays of Thurston's suspension: singular over singular points -/

section Rays

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  {σ₀ : RaySphere W} {S : Type*} [TopologicalSpace S]
  [SingularGXStructure (SpecialOrth W) (RaySphere W) S]

/-- **The ray over a point is regular only if the point is**, in Thurston's suspension: if
`(x, t)`, `t > 0`, is regular in `susp(Σ)`, then `x ∈ Reg Σ`. The argument of
`GX.ConicStructure.mem_reg_of_mk_mem_reg` (a chart `ψ` of the maximal atlas at `(x, t)` is, on
the regular part of a box, `g₀ (1 ⊕ A) · φ⁻¹ ∘ susp*(e)` for one `g₀`; so `φ ∘ g₀⁻¹ ∘ ψ` preserves
the radius, and its slice at radius `t` is a chart of `Σ` at `x`), transported to the Thurston
atlas, whose chart changes are `1 ⊕ A = liftSO W A` (kb 0007). The link `𝕊(W)` is compact. -/
theorem thurston_mem_reg_of_mk_mem_reg [PreconnectedSpace S] [LocallyConnectedSpace S]
    {x : S} {t : ℝ≥0} (ht : 0 < t)
    (hreg : letI := thurstonStructure σ₀ S
      Susp.mk (x, t) ∈ Reg (SpecialOrth (PolarSum W)) (RaySphere (PolarSum W)) (Susp S)) :
    x ∈ Reg (SpecialOrth W) (RaySphere W) S := by
  set c := sphConic σ₀ with hcdef
  have hf : c.IsFull := sphConic_isFull σ₀
  set A := thurstonAtlas σ₀ S with hAdef
  have hA : IsAEAtlas (SpecialOrth (PolarSum W)) A := isAEAtlas_thurstonAtlas
  have hM : IsMaximalAEAtlas (SpecialOrth (PolarSum W))
      (maximalAEAtlas (SpecialOrth (PolarSum W)) A) := hA.isMaximalAEAtlas_maximalAEAtlas
  have hAM : A ⊆ maximalAEAtlas (SpecialOrth (PolarSum W)) A := hA.subset_maximalAEAtlas
  have hSig := isMaximalAEAtlas_aeAtlas (SpecialOrth W) (RaySphere W) S
  obtain ⟨ψ, hψ, hxψ⟩ := mem_support.1 hreg
  change ψ ∈ maximalAEAtlas (SpecialOrth (PolarSum W)) A at hψ
  have htgt : ∀ a, a ∈ c.φ.target := fun a => by rw [show c.φ.target = univ from hf]; trivial
  have hconesrc : ∀ {e : OpenPartialHomeomorph S (RaySphere W)} {q : S × ℝ≥0},
      q.1 ∈ e.source → 0 < q.2 → Susp.mk q ∈ (c.coneChart e).source := fun {e q} h1 h2 => by
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
  -- the compact `φ⁻¹(𝕊(W) × [t/2, 2t])`, closed in `𝕊(ℝ ⊕ W)`, inside the source of `φ`
  set K : Set (Susp (RaySphere W)) := Susp.mk '' (univ ×ˢ Icc (t / 2) (2 * t)) with hKdef
  have hK : IsCompact K := (isCompact_univ.prod isCompact_Icc).image Susp.continuous_mk
  set C : Set (RaySphere (PolarSum W)) := c.φ.symm '' K with hCdef
  have hC : IsClosed C :=
    (hK.image_of_continuousOn (c.φ.continuousOn_symm.mono fun a _ => htgt a)).isClosed
  have hCU : C ⊆ c.φ.source := by rintro _ ⟨a, -, rfl⟩; exact c.φ.map_target (htgt a)
  -- the regular part of the box, preconnected
  set Ω : Set (S × ℝ≥0) := (B ∩ Reg (SpecialOrth W) (RaySphere W) S) ×ˢ I with hΩdef
  have hΩc : IsPreconnected Ω :=
    ((isPortly_reg (SpecialOrth W) (RaySphere W) S).locallyConnectedIn B hBo
      hBc.isPreconnected).prod isPreconnected_Ioo
  -- `Q q g`: near `(q.1, q.2)`, `ψ` is `g (1 ⊕ h)` times a cone chart, for some `h ∈ SO(W)`
  let Q : S × ℝ≥0 → SpecialOrth (PolarSum W) → Prop := fun q g =>
    ∃ e ∈ aeAtlas (SpecialOrth W) (RaySphere W) S, ∃ h : SpecialOrth W, q.1 ∈ e.source ∧
      ∀ᶠ y in 𝓝 (Susp.mk q), ψ y = (g * liftSO W h) • c.coneChart e y
  have hloc : ∀ q ∈ Ω, ∃ k : SpecialOrth (PolarSum W), ∀ᶠ q' in 𝓝 q,
      ∀ g : SpecialOrth (PolarSum W),
        Q q' g ↔ ∃ h : SpecialOrth W, ∀ z : RaySphere (PolarSum W),
          (g * liftSO W h) • z = k • z := by
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
      obtain ⟨h', hh'⟩ := thurston_eventually_eq_smul (σ₀ := σ₀) he₀ he
        ⟨hconesrc hq'e₀ hq'2, hconesrc hq'e hq'2⟩
      have hev' : ∀ᶠ y in 𝓝 (Susp.mk q'),
          (g * liftSO W h * liftSO W h') • c.coneChart e₀ y = k • c.coneChart e₀ y := by
        filter_upwards [hev, hh', hq'k] with y hy hy' hy''
        rw [mul_smul, ← hy', ← hy, hy'']
      have hev'' : ∀ᶠ z in 𝓝 (c.coneChart e₀ (Susp.mk q')),
          (g * liftSO W h * liftSO W h') • z = k • z := by
        rw [← (c.coneChart e₀).map_nhds_eq (hconesrc hq'e₀ hq'2)]; exact hev'
      obtain ⟨V, hVsub, hVo, hzV⟩ := mem_nhds_iff.1 hev''
      refine ⟨h * h', fun z => ?_⟩
      rw [map_mul, ← mul_assoc]
      exact IsRigidAction.smul_eq_of_eqOn hVo ⟨_, hzV⟩ (fun z hz => hVsub hz) z
    · rintro ⟨h, hh⟩
      refine ⟨e₀, he₀, h, hq'e₀, ?_⟩
      filter_upwards [hq'k] with y hy
      rw [hy, hh]
  -- one `g₀` on all of `Ω`, by connectedness
  obtain ⟨x₀, hx₀B, hx₀R⟩ : (B ∩ Reg (SpecialOrth W) (RaySphere W) S).Nonempty := by
    obtain ⟨y, hyB, hyR⟩ := (isPortly_reg (SpecialOrth W) (RaySphere W) S).dense.inter_open_nonempty
      B hBo ⟨x, hxB⟩
    exact ⟨y, hyB, hyR⟩
  have hq₀ : (x₀, t) ∈ Ω := ⟨⟨hx₀B, hx₀R⟩, htI⟩
  obtain ⟨g₀, hg₀⟩ := hloc _ hq₀
  have hQ₀ : Q (x₀, t) g₀ := (hg₀.self_of_nhds g₀).2 ⟨1, fun z => by rw [map_one, mul_one]⟩
  have hQ : ∀ q ∈ Ω, Q q g₀ := by
    intro q hq
    refine hΩc.induction₂' (fun q q' => ∀ g, Q q g → Q q' g) (fun q hq => ?_)
      (fun _ _ _ _ _ _ h₁ h₂ g hg => h₂ g (h₁ g hg)) hq₀ hq g₀ hQ₀
    obtain ⟨k, hk⟩ := hloc q hq
    have hkq := hk.self_of_nhds
    filter_upwards [mem_nhdsWithin_of_mem_nhds hk] with q' hq'
    exact ⟨fun g hg => (hq' g).2 ((hkq g).1 hg), fun g hg => (hkq g).2 ((hq' g).1 hg)⟩
  -- the map `F = g₀⁻¹ ψ` on the box, read in coordinates
  set Fx : S × ℝ≥0 → RaySphere (PolarSum W) := fun q => g₀⁻¹ • ψ (Susp.mk q) with hFxdef
  have hΩsub : Ω ⊆ B ×ˢ I := fun q hq => ⟨hq.1.1, hq.2⟩
  have hFΩ : ∀ q ∈ Ω, Fx q ∈ C ∧ (c.φ (Fx q)).r = q.2 := by
    intro q hq
    obtain ⟨e, he, h, hqe, hev⟩ := hQ q hq
    have e1 : Fx q = c.φ.symm (Susp.mk (h • e q.1, q.2)) := by
      show g₀⁻¹ • ψ (Susp.mk q) = _
      rw [hev.self_of_nhds, c.coneChart_apply, sphConic_symm_smul, mul_smul, inv_smul_smul]
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
    have := ((isPortly_reg (SpecialOrth W) (RaySphere W) S).dense.prod
      dense_univ).open_subset_closure_inter hBIo
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
  set F : OpenPartialHomeomorph (Susp S) (Susp (RaySphere W)) :=
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
  let e' : OpenPartialHomeomorph S (RaySphere W) :=
    { toFun := fun z => (F (Susp.mk (z, t))).dir
      invFun := fun σ => (F.symm (Susp.mk (σ, t))).dir
      source := B
      target := (fun σ : RaySphere W => Susp.mk (σ, t)) ⁻¹' F.target
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
        have h1 : ContinuousAt (fun σ : RaySphere W => F.symm (Susp.mk (σ, t))) σ :=
          ContinuousAt.comp (g := F.symm) (f := fun σ : RaySphere W => Susp.mk (σ, t))
            (F.continuousAt_symm hσ') (Susp.continuous_mk_left t).continuousAt
        refine ContinuousAt.comp (g := Susp.dir)
          (f := fun σ : RaySphere W => F.symm (Susp.mk (σ, t))) ?_ h1
        obtain ⟨q, hq, hqe⟩ := hFsrc' _ (F.map_target hσ')
        refine Susp.continuousAt_dir ?_
        show 0 < (F.symm (Susp.mk (σ, t))).r
        rw [hqe, Susp.r_mk]; exact hpos hq }
  -- `e'` is compatible with every chart of `Σ`: near `y`, `e' = h · e` for the `e, h` of `Q`
  have he' : e' ∈ aeAtlas (SpecialOrth W) (RaySphere W) S := by
    refine hSig.mem_of_compatible fun c' hc' y hy => ?_
    have hyB : y ∈ B := hy.1
    have hyR : y ∈ Reg (SpecialOrth W) (RaySphere W) S := mem_support.2 ⟨c', hc', hy.2⟩
    obtain ⟨e, he, h, hye, hev⟩ := hQ (y, t) ⟨⟨hyB, hyR⟩, htI⟩
    obtain ⟨h', hh'⟩ := hSig.1.1.eventually_smul_eq he hc' hye hy.2
    have hev' := ((Susp.continuous_mk_left t).tendsto y).eventually hev
    refine ⟨h' * h⁻¹, ?_⟩
    filter_upwards [hev', hh', e.open_source.mem_nhds hye, hBo.mem_nhds hyB] with z hz hz' hze hzB
    show c' z = (h' * h⁻¹) • (F (Susp.mk (z, t))).dir
    have hFz : F (Susp.mk (z, t)) = Susp.mk (h • e z, t) := by
      rw [hFapp]
      show c.φ (g₀⁻¹ • ψ (Susp.mk (z, t))) = _
      rw [hz, c.coneChart_apply, mul_smul, inv_smul_smul, ← sphConic_symm_smul,
        c.φ.right_inv (htgt _)]
    rw [hFz, Susp.dir_mk_of_pos ht, hz', mul_smul, inv_smul_smul]
  exact mem_support.2 ⟨e', he', hxB⟩

/-- **The ray over a singular point is singular** in Thurston's suspension. -/
theorem thurston_mk_mem_sing [PreconnectedSpace S] [LocallyConnectedSpace S] {x : S}
    (hx : x ∈ Sing (SpecialOrth W) (RaySphere W) S) {t : ℝ≥0} (ht : 0 < t) :
    letI := thurstonStructure σ₀ S
    Susp.mk (x, t) ∈ Sing (SpecialOrth (PolarSum W)) (RaySphere (PolarSum W)) (Susp S) :=
  fun h => hx (thurston_mem_reg_of_mk_mem_reg ht h)

/-- **Regular rays are exactly the rays over regular points**, in Thurston's suspension
(`RamcovGX.tex:740`, "the image of regular `(G,X)`-manifolds are regular except possibly at `O`",
off the centre). -/
theorem thurston_mk_mem_reg_iff [PreconnectedSpace S] [LocallyConnectedSpace S] {x : S}
    {t : ℝ≥0} (ht : 0 < t) :
    letI := thurstonStructure σ₀ S
    Susp.mk (x, t) ∈ Reg (SpecialOrth (PolarSum W)) (RaySphere (PolarSum W)) (Susp S) ↔
      x ∈ Reg (SpecialOrth W) (RaySphere W) S :=
  ⟨thurston_mem_reg_of_mk_mem_reg ht, fun hx => thurston_mk_mem_reg hx ht⟩

/-- **The centre is singular as soon as `Σ` has a singular point**: it is the limit of the
singular ray over that point, and the singular locus is closed. -/
theorem thurston_O_subset_sing [PreconnectedSpace S] [LocallyConnectedSpace S]
    (hne : (Sing (SpecialOrth W) (RaySphere W) S).Nonempty) :
    letI := thurstonStructure σ₀ S
    (Susp.O : Set (Susp S)) ⊆
      Sing (SpecialOrth (PolarSum W)) (RaySphere (PolarSum W)) (Susp S) := by
  letI := thurstonStructure σ₀ S
  obtain ⟨x, hx⟩ := hne
  intro O hO
  have hO' : O = Susp.mk (x, 0) := Susp.eq_of_mem_O hO rfl
  have hcont : Continuous fun t : ℝ≥0 => (Susp.mk (x, t) : Susp S) :=
    Susp.continuous_mk.comp (continuous_const.prodMk continuous_id)
  have hlim : Tendsto (fun t : ℝ≥0 => (Susp.mk (x, t) : Susp S)) (𝓝[>] 0) (𝓝 O) := by
    rw [hO']; exact (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  refine (isClosed_sing (SpecialOrth (PolarSum W)) (RaySphere (PolarSum W)) (Susp S)).mem_of_tendsto
    hlim ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact thurston_mk_mem_sing hx ht

/-- **The singular locus of Thurston's suspension** of a `Σ` with a singular point: the centre and
the open rays over the singular points of `Σ`. -/
theorem thurston_sing_eq [PreconnectedSpace S] [LocallyConnectedSpace S]
    (hne : (Sing (SpecialOrth W) (RaySphere W) S).Nonempty) :
    letI := thurstonStructure σ₀ S
    Sing (SpecialOrth (PolarSum W)) (RaySphere (PolarSum W)) (Susp S) =
      Susp.O ∪ Susp.mk '' (Sing (SpecialOrth W) (RaySphere W) S ×ˢ Ioi 0) := by
  letI := thurstonStructure σ₀ S
  ext z
  obtain ⟨⟨x, t⟩, rfl⟩ := Susp.mk_surjective z
  constructor
  · intro hz
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h0 | hpos
    · left; exact h0.symm
    · right
      exact ⟨(x, t), ⟨fun hx => hz ((thurston_mk_mem_reg_iff hpos).2 hx), hpos⟩, rfl⟩
  · rintro (hO | ⟨⟨y, u⟩, ⟨hy, hu⟩, hyu⟩)
    · exact thurston_O_subset_sing hne hO
    · rw [← hyu]; exact thurston_mk_mem_sing hy hu

end Rays

/-- `ℝ≥0` is connected (the image of `ℝ` under `Real.toNNReal`). -/
theorem connectedSpace_nnreal : ConnectedSpace ℝ≥0 :=
  Function.Surjective.connectedSpace (f := Real.toNNReal)
    (fun t => ⟨t, Real.toNNReal_coe⟩) continuous_real_toNNReal

/-- **The suspension of a connected space is connected** (the image of `Σ × ℝ≥0`). -/
theorem Susp.connectedSpace {S : Type*} [TopologicalSpace S] [ConnectedSpace S] :
    ConnectedSpace (Susp S) := by
  haveI := connectedSpace_nnreal
  exact Function.Surjective.connectedSpace Susp.mk_surjective Susp.continuous_mk

/-! ### The natural map `Aut(Σ) → Aut(susp Σ)` (DEC-175 (c)) -/

section AutMap

/-- The suspension `susp(f)` of a homeomorphism `f : Σ ≃ₜ Σ'`, `(σ, r) ↦ (f σ, r)`. -/
def Susp.homeomorph {S T : Type*} [TopologicalSpace S] [TopologicalSpace T] (f : S ≃ₜ T) :
    Susp S ≃ₜ Susp T where
  toFun := Susp.map f
  invFun := Susp.map f.symm
  left_inv a := by
    obtain ⟨q, rfl⟩ := Susp.mk_surjective a
    rw [Susp.map_mk, Susp.map_mk, Homeomorph.symm_apply_apply]
  right_inv a := by
    obtain ⟨q, rfl⟩ := Susp.mk_surjective a
    rw [Susp.map_mk, Susp.map_mk, Homeomorph.apply_symm_apply]
  continuous_toFun := Susp.continuous_map f.continuous
  continuous_invFun := Susp.continuous_map f.symm.continuous

theorem Susp.homeomorph_apply {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
    (f : S ≃ₜ T) (a : Susp S) : Susp.homeomorph f a = Susp.map f a := rfl

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  {σ₀ : RaySphere W} {S : Type*} [TopologicalSpace S]
  [SingularGXStructure (SpecialOrth W) (RaySphere W) S]

/-- **The suspension of an automorphism of `Σ` is an automorphism of `susp(Σ)`**: `susp(f)` reads
each cone chart `φ⁻¹ ∘ susp*(e)` as the cone chart of `e ∘ f⁻¹`, a chart of `Σ` since `f` is an
isomorphism (`IsAEMorphism.aeAtlas_eq_of_homeomorph`), so it is an a.e. morphism of the maximal
atlases (`isAEMorphismOf_maximalAEAtlas_of_forall`, kb 0011). -/
theorem thurston_isAEMorphism_suspHomeomorph [PreconnectedSpace S] [LocallyConnectedSpace S]
    {f : S ≃ₜ S} (hf : IsAEMorphism (SpecialOrth W) (RaySphere W) (f : S → S)) :
    letI := thurstonStructure σ₀ S
    IsAEMorphism (SpecialOrth (PolarSum W)) (RaySphere (PolarSum W))
      (Susp.homeomorph f : Susp S → Susp S) := by
  letI := thurstonStructure σ₀ S
  have hA := isAEAtlas_thurstonAtlas (σ₀ := σ₀) (S := S)
  refine isAEMorphismOf_maximalAEAtlas_of_forall hA hA (Susp.homeomorph f).continuous ?_
  rintro _ ⟨e, he, rfl⟩
  have he' : f.symm.toOpenPartialHomeomorph.trans e ∈ aeAtlas (SpecialOrth W) (RaySphere W) S :=
    (hf.aeAtlas_eq_of_homeomorph.1 e).1 he
  refine ⟨(sphConic σ₀).coneChart (f.symm.toOpenPartialHomeomorph.trans e), ⟨_, he', rfl⟩, ?_, ?_⟩
  · rw [(sphConic σ₀).coneChart_source_of_isFull (sphConic_isFull σ₀),
      (sphConic σ₀).coneChart_source_of_isFull (sphConic_isFull σ₀)]
    rintro _ ⟨q, ⟨hq1, hq2⟩, rfl⟩
    refine ⟨(f q.1, q.2), ⟨?_, hq2⟩, rfl⟩
    show f q.1 ∈ univ ∩ f.symm ⁻¹' e.source
    exact ⟨mem_univ _, by rw [mem_preimage, Homeomorph.symm_apply_apply]; exact hq1⟩
  · rw [(sphConic σ₀).coneChart_source_of_isFull (sphConic_isFull σ₀)]
    rintro _ ⟨q, ⟨-, -⟩, rfl⟩
    rw [Susp.homeomorph_apply, Susp.map_mk, (sphConic σ₀).coneChart_apply,
      (sphConic σ₀).coneChart_apply]
    show (sphConic σ₀).φ.symm (Susp.mk (e (f.symm (f q.1)), q.2)) = _
    rw [Homeomorph.symm_apply_apply]

variable (σ₀ S) in
/-- **The natural map `Aut(Σ) → Aut(susp Σ)`** (`RamcovGX.tex:1933`), `f ↦ susp(f)`, a group
homomorphism. -/
def thurstonSuspAut [PreconnectedSpace S] [LocallyConnectedSpace S] :
    letI := thurstonStructure σ₀ S
    singularAut (SpecialOrth W) (RaySphere W) S →*
      singularAut (SpecialOrth (PolarSum W)) (RaySphere (PolarSum W)) (Susp S) :=
  letI := thurstonStructure σ₀ S
  { toFun := fun f => ⟨Susp.homeomorph (f : S ≃ₜ S), thurston_isAEMorphism_suspHomeomorph f.2⟩
    map_one' := by
      refine Subtype.ext (Homeomorph.ext fun a => ?_)
      obtain ⟨q, rfl⟩ := Susp.mk_surjective a
      rfl
    map_mul' := fun f g => by
      refine Subtype.ext (Homeomorph.ext fun a => ?_)
      obtain ⟨q, rfl⟩ := Susp.mk_surjective a
      rfl }

theorem thurstonSuspAut_apply [PreconnectedSpace S] [LocallyConnectedSpace S]
    (f : singularAut (SpecialOrth W) (RaySphere W) S) (q : S × ℝ≥0) :
    letI := thurstonStructure σ₀ S
    ((thurstonSuspAut σ₀ S f : Susp S ≃ₜ Susp S) (Susp.mk q)) = Susp.mk ((f : S ≃ₜ S) q.1, q.2) :=
  rfl

/-- **`Aut(Σ) → Aut(susp Σ)` is injective**: `f` is read off `susp(f)` on the sphere of radius
`1`. -/
theorem thurstonSuspAut_injective [PreconnectedSpace S] [LocallyConnectedSpace S] :
    letI := thurstonStructure σ₀ S
    Injective (thurstonSuspAut σ₀ S) := by
  letI := thurstonStructure σ₀ S
  intro f g hfg
  refine Subtype.ext (Homeomorph.ext fun σ => ?_)
  have h1 := congrArg (fun F : singularAut _ _ _ => (F : Susp S ≃ₜ Susp S) (Susp.mk (σ, 1))) hfg
  simp only [thurstonSuspAut_apply] at h1
  exact (Prod.ext_iff.1 (Susp.eq_of_mk_eq_of_pos h1 (show (0 : ℝ≥0) < 1 from one_pos))).1

end AutMap

/-- At least three angles `≠ 2π` means at least one angle. -/
theorem pos_of_three_le_card_ne_two_pi {s : ℕ} {θ : Fin s → ℝ}
    (h : 3 ≤ (Finset.univ.filter fun i => θ i ≠ 2 * π).card) : 0 < s := by
  have h1 := (Finset.card_filter_le (Finset.univ : Finset (Fin s)) fun i => θ i ≠ 2 * π)
  rw [Finset.card_univ, Fintype.card_fin] at h1
  omega

/-- **Theorem C's condition forces at least three angles `≠ 2π`** (as the printed one does,
`GX.TroyanovAngleCondition.three_le_card_ne_two_pi`): with `F` the angles `≠ 2π`,
`χ' = ∑_F (θ_i − 2π) + 4π`; `F = ∅` gives `χ' = 4π`, `F = {a}` gives `2π < θ_a < 2π`, `F = {a, b}`
gives `θ_a + θ_b < 2 min(θ_a, θ_b)`. -/
theorem TroyanovAngleConditionC.three_le_card_ne_two_pi {s : ℕ} {θ : Fin s → ℝ}
    (h : TroyanovAngleConditionC θ) : 3 ≤ (Finset.univ.filter fun i => θ i ≠ 2 * π).card := by
  set F := Finset.univ.filter fun i => θ i ≠ 2 * π
  have hsum : ∑ i, (θ i - 2 * π) = ∑ i ∈ F, (θ i - 2 * π) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => θ i ≠ 2 * π)]
    have : ∑ i ∈ Finset.univ.filter (fun i => ¬ θ i ≠ 2 * π), (θ i - 2 * π) = 0 :=
      Finset.sum_eq_zero fun i hi => by
        rw [Finset.mem_filter, not_not] at hi; rw [hi.2, sub_self]
    rw [this, add_zero]
  obtain ⟨h1, h2, h3⟩ := h
  rw [hsum] at h1 h2 h3
  by_contra hlt
  rw [not_le] at hlt
  interval_cases hc : F.card
  · rw [Finset.card_eq_zero] at hc
    rw [hc, Finset.sum_empty, zero_add] at h2
    exact lt_irrefl _ h2
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hc
    rw [ha, Finset.sum_singleton] at h2 h3
    linarith [h3 a]
  · obtain ⟨a, b, hab, hF⟩ := Finset.card_eq_two.1 hc
    rw [hF, Finset.sum_pair hab] at h3
    linarith [h3 a, h3 b]

/-! ### The suspension of a cone sphere: its singular locus, its centre -/

section ConeSphere

variable {M : Type} [TopologicalSpace M] [SingularGXStructure SO3 Sph2 M]

/-- **The singular locus of `susp(Σ)`, tied to the angles** (`RamcovGX.tex:1933`, "singular locus
is homeomorphic to a line except at `O`"): for a cone sphere with a cone point of angle `≠ 2π`
(Troyanov's condition gives three, `TroyanovAngleCondition.three_le_card_ne_two_pi`), it is the
centre and the open rays over the cone points of angle `≠ 2π`. -/
theorem IsConeSphere.thurston_sing_eq {s : ℕ} {θ : Fin s → ℝ} {p : Fin s → M}
    (h : IsConeSphere M θ p) (hθ : 3 ≤ (Finset.univ.filter fun i => θ i ≠ 2 * π).card) :
    haveI := h.connectedSpace
    haveI := h.locallyConnectedSpace
    letI := thurstonSuspension (M := M)
    Sing SO4 Sph3 (Susp M) = Susp.O ∪ Susp.mk '' ((p '' {i | θ i ≠ 2 * π}) ×ˢ Ioi 0) := by
  haveI := h.connectedSpace
  haveI := h.locallyConnectedSpace
  have hne : (Sing SO3 Sph2 M).Nonempty := by
    obtain ⟨i, hi⟩ : (Finset.univ.filter fun i => θ i ≠ 2 * π).Nonempty := by
      rw [← Finset.card_pos]; omega
    rw [h.sing_eq]
    exact ⟨p i, i, (Finset.mem_filter.1 hi).2, rfl⟩
  have := GX.thurston_sing_eq (σ₀ := sph2Base) hne
  rw [h.sing_eq] at this
  exact this

/-- **The centre of `susp(Σ)` is singular, and so is the rest of each singular ray**: for a cone
sphere with a cone point of angle `≠ 2π`, `O` is singular and some other point is
(`RamcovGX.tex:1931–1933`). -/
theorem IsConeSphere.thurston_mem_sing_exists_ne {s : ℕ} {θ : Fin s → ℝ} {p : Fin s → M}
    (h : IsConeSphere M θ p) (hθ : 3 ≤ (Finset.univ.filter fun i => θ i ≠ 2 * π).card) :
    haveI := h.connectedSpace
    haveI := h.locallyConnectedSpace
    letI := thurstonSuspension (M := M)
    ∀ O ∈ (Susp.O : Set (Susp M)), O ∈ Sing SO4 Sph3 (Susp M) ∧
      ∃ y ∈ Sing SO4 Sph3 (Susp M), y ≠ O := by
  haveI := h.connectedSpace
  haveI := h.locallyConnectedSpace
  letI := thurstonSuspension (M := M)
  intro O hO
  have hsing := h.thurston_sing_eq hθ
  obtain ⟨i, hi⟩ : (Finset.univ.filter fun i => θ i ≠ 2 * π).Nonempty := by
    rw [← Finset.card_pos]; omega
  have hi' : θ i ≠ 2 * π := (Finset.mem_filter.1 hi).2
  refine ⟨by rw [hsing]; exact Or.inl hO, Susp.mk (p i, 1), ?_, fun he => ?_⟩
  · rw [hsing]; exact Or.inr ⟨(p i, 1), ⟨⟨i, hi', rfl⟩, show (0 : ℝ≥0) < 1 from one_pos⟩, rfl⟩
  · have h1 : (Susp.mk (p i, 1) : Susp M).r = 0 := by rw [he]; exact hO
    exact one_ne_zero h1

end ConeSphere

/-- A preconnected subset of a finite set of a `T₁` space has at most one point. -/
theorem IsPreconnected.subsingleton_of_subset_finite {Y : Type*} [TopologicalSpace Y] [T1Space Y]
    {T F : Set Y} (hT : IsPreconnected T) (hF : F.Finite) (hTF : T ⊆ F) : T.Subsingleton := by
  intro a ha b hb
  by_contra hab
  have hU : IsOpen (F \ {a})ᶜ := (hF.subset sdiff_subset).isClosed.isOpen_compl
  have hV : IsOpen ({a}ᶜ : Set Y) := isOpen_compl_singleton
  obtain ⟨z, hzT, hzU, hzV⟩ := hT _ _ hU hV (fun z _ => by
      by_cases hza : z = a
      · left; rintro ⟨-, h⟩; exact h hza
      · right; exact hza) ⟨a, ha, fun h => h.2 rfl⟩ ⟨b, hb, fun h => hab h.symm⟩
  exact hzU ⟨hTF hzT, hzV⟩

/-! ### Reading isomorphisms of open subsets in ambient charts -/

section OpensReading

variable {G : Type*} {X : Type*} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
  {M : Type*} [TopologicalSpace M] [SingularGXStructure G X M]
  {N : Type*} [TopologicalSpace N] [SingularGXStructure G X N]

/-- An a.e. morphism is read, near a regular point with a regular image, in any two charts, by one
element of `G` (`lem:regf1`: the point is in the regular locus of the morphism). -/
theorem IsAEMorphism.eventually_smul_eq_of_mem {f : M → N} (hf : IsAEMorphism G X f) {x : M}
    (hx : x ∈ Reg G X M) (hfx : f x ∈ Reg G X N) {e : OpenPartialHomeomorph M X}
    (he : e ∈ aeAtlas G X M) (hxe : x ∈ e.source) {e' : OpenPartialHomeomorph N X}
    (he' : e' ∈ aeAtlas G X N) (hfxe : f x ∈ e'.source) :
    ∃ g : G, ∀ᶠ y in 𝓝 x, e' (f y) = g • e y := by
  have hR : x ∈ regLocusOf G (aeAtlas G X M) (aeAtlas G X N) f := by
    have := hf.regLocus_eq
    rw [regLocus] at this
    rw [this]; exact ⟨hx, hfx⟩
  exact (isRegularOn_regLocusOf (G := G) _ _ f).exists_smul_eq x hR e he e' he' hxe hfxe

/-- **An isomorphism of open subsets, read in ambient charts**: at a regular point `m ∈ U`, a map
`F : M → N` agreeing with `φ` on `U` has a regular image and is read, in any charts of `M` at `m`
and of `N` at `F m`, by one element of `G`. -/
theorem IsAEMorphism.eventually_smul_eq_of_opens {U : Opens M} {V : Opens N} {φ : U ≃ₜ V}
    (hφ : IsAEMorphism G X (φ : U → V)) {F : M → N}
    (hF : ∀ y (hy : y ∈ U), F y = (φ ⟨y, hy⟩ : N)) {m : M} (hm : m ∈ U)
    (hreg : m ∈ Reg G X M) :
    F m ∈ Reg G X N ∧ ∀ e ∈ aeAtlas G X M, m ∈ e.source → ∀ e' ∈ aeAtlas G X N,
      F m ∈ e'.source → ∃ g : G, ∀ᶠ y in 𝓝 m, e' (F y) = g • e y := by
  set u : U := ⟨m, hm⟩
  have hpre := (IsAEMorphism.preimage_reg_sing hφ φ.isLocalHomeomorph).1
  have huU : u ∈ Reg G X U := by rw [reg_opensSingular U]; exact hreg
  have huV : φ u ∈ Reg G X V := by
    have : u ∈ (φ : U → V) ⁻¹' Reg G X V := by rw [hpre]; exact huU
    exact this
  have huV' : (φ u : N) ∈ Reg G X N := by
    have := huV; rw [reg_opensSingular V] at this; exact this
  refine ⟨by rw [hF m hm]; exact huV', fun e he hme e' he' hfe => ?_⟩
  rw [hF m hm] at hfe
  have hvalU := isAEMorphism_opensSingular_val (G := G) (X := X) U
  have hvalV := isAEMorphism_opensSingular_val (G := G) (X := X) V
  obtain ⟨eU, heU, hueU⟩ := mem_support.1 huU
  obtain ⟨eV, heV, hueV⟩ := mem_support.1 huV
  obtain ⟨g, hg⟩ := hφ.eventually_smul_eq_of_mem huU huV heU hueU heV hueV
  obtain ⟨a, ha⟩ := hvalV.eventually_smul_eq_of_mem huV huV' heV hueV he' hfe
  obtain ⟨b, hb⟩ := hvalU.eventually_smul_eq_of_mem huU hreg heU hueU he hme
  refine ⟨a * g * b⁻¹, ?_⟩
  have hmap : map (Subtype.val : U → M) (𝓝 u) = 𝓝 m :=
    U.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq u
  rw [← hmap, eventually_map]
  filter_upwards [hg, φ.continuous.continuousAt.eventually ha, hb] with y h1 h2 h3
  show e' (F y) = (a * g * b⁻¹) • e y
  rw [hF y y.2]
  have h2' : e' ((φ y : V) : N) = a • eV (φ y) := h2
  have h3' : e (y : M) = b • eU y := h3
  rw [h2', h1, h3']
  simp only [smul_smul]
  congr 1
  group

/-- **A map out of an open subset is an a.e. morphism** as soon as, at each of its regular points,
it has a regular image and is read in ambient charts by an element of `G`. -/
theorem isAEMorphism_of_opens_of_eventually (U : Opens M) {f : U → N} (hf : Continuous f)
    (h : ∀ x : U, (x : M) ∈ Reg G X M → f x ∈ Reg G X N ∧ ∃ e ∈ aeAtlas G X M,
      (x : M) ∈ e.source ∧ ∃ e' ∈ aeAtlas G X N, f x ∈ e'.source ∧
        ∃ g : G, ∀ᶠ y in 𝓝 x, e' (f y) = g • e (y : M)) :
    IsAEMorphism G X f := by
  have hBU := isMaximalAEAtlas_aeAtlas G X U
  have hBN := isMaximalAEAtlas_aeAtlas G X N
  have hregU : ∀ x : U, x ∈ Reg G X U ↔ (x : M) ∈ Reg G X M := fun x => by
    rw [reg_opensSingular U]; rfl
  refine (isAEMorphismOf_iff hBN.1).2 ⟨hf, Reg G X U, isPortly_reg G X U,
    IsRegularOn.of_exists hBU.1.1 hBN.1.1 (isOpen_reg G X U) subset_rfl
      (fun x hx => (h x ((hregU x).1 hx)).1) hf.continuousOn fun x hx => ?_⟩
  obtain ⟨-, e, he, hxe, e', he', hfxe, g, hg⟩ := h x ((hregU x).1 hx)
  obtain ⟨b, hb, hxb⟩ := mem_support.1 hx
  have hvalU := isAEMorphism_opensSingular_val (G := G) (X := X) U
  obtain ⟨k, hk⟩ := hvalU.eventually_smul_eq_of_mem hx ((hregU x).1 hx) hb hxb he hxe
  refine ⟨b, hb, e', he', hxb, hfxe, g * k, ?_⟩
  filter_upwards [hg, hk] with y h1 h2
  rw [h1, mul_smul]
  exact congrArg (g • ·) h2

end OpensReading

section OpensOPH

attribute [local instance] Classical.propDecidable

/-- **A homeomorphism of open subsets, as an open partial homeomorphism** of the ambient spaces
(any value off `U`, `V`). -/
def opensOPH {M N : Type*} [TopologicalSpace M] [TopologicalSpace N] [Nonempty M] [Nonempty N]
    {U : Opens M} {V : Opens N} (φ : U ≃ₜ V) : OpenPartialHomeomorph M N where
  toFun m := if h : m ∈ U then (φ ⟨m, h⟩ : N) else Classical.arbitrary N
  invFun n := if h : n ∈ V then (φ.symm ⟨n, h⟩ : M) else Classical.arbitrary M
  source := U
  target := V
  map_source' m hm := by
    have hm' : m ∈ U := hm
    show (if h : m ∈ U then (φ ⟨m, h⟩ : N) else Classical.arbitrary N) ∈ V
    rw [dif_pos hm']; exact (φ ⟨m, hm'⟩).2
  map_target' n hn := by
    have hn' : n ∈ V := hn
    show (if h : n ∈ V then (φ.symm ⟨n, h⟩ : M) else Classical.arbitrary M) ∈ U
    rw [dif_pos hn']; exact (φ.symm ⟨n, hn'⟩).2
  left_inv' m hm := by
    have hm' : m ∈ U := hm
    show (if h : (if h : m ∈ U then (φ ⟨m, h⟩ : N) else Classical.arbitrary N) ∈ V then
      (φ.symm ⟨_, h⟩ : M) else Classical.arbitrary M) = m
    rw [dif_pos hm', dif_pos (φ ⟨m, hm'⟩).2]
    simp only [Subtype.coe_eta, Homeomorph.symm_apply_apply]
  right_inv' n hn := by
    have hn' : n ∈ V := hn
    show (if h : (if h : n ∈ V then (φ.symm ⟨n, h⟩ : M) else Classical.arbitrary M) ∈ U then
      (φ ⟨_, h⟩ : N) else Classical.arbitrary N) = n
    rw [dif_pos hn', dif_pos (φ.symm ⟨n, hn'⟩).2]
    simp only [Subtype.coe_eta, Homeomorph.apply_symm_apply]
  open_source := U.isOpen
  open_target := V.isOpen
  continuousOn_toFun := by
    rw [continuousOn_iff_continuous_restrict]
    have : (U : Set M).restrict (fun m => if h : m ∈ U then (φ ⟨m, h⟩ : N)
        else Classical.arbitrary N) = fun m : U => (φ m : N) := by
      funext m; exact dif_pos m.2
    rw [this]
    exact continuous_subtype_val.comp φ.continuous
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_restrict]
    have : (V : Set N).restrict (fun n => if h : n ∈ V then (φ.symm ⟨n, h⟩ : M)
        else Classical.arbitrary M) = fun n : V => (φ.symm n : M) := by
      funext n; exact dif_pos n.2
    rw [this]
    exact continuous_subtype_val.comp φ.symm.continuous

theorem opensOPH_apply {M N : Type*} [TopologicalSpace M] [TopologicalSpace N] [Nonempty M]
    [Nonempty N] {U : Opens M} {V : Opens N} (φ : U ≃ₜ V) {m : M} (hm : m ∈ U) :
    opensOPH φ m = (φ ⟨m, hm⟩ : N) := dif_pos hm

theorem opensOPH_symm_apply {M N : Type*} [TopologicalSpace M] [TopologicalSpace N] [Nonempty M]
    [Nonempty N] {U : Opens M} {V : Opens N} (φ : U ≃ₜ V) {n : N} (hn : n ∈ V) :
    (opensOPH φ).symm n = (φ.symm ⟨n, hn⟩ : M) := dif_pos hn

end OpensOPH

/-- An open partial homeomorphism, as a homeomorphism of its source onto its target, both as open
subsets. -/
def opensHomeoOf {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    (e : OpenPartialHomeomorph M N) :
    (⟨e.source, e.open_source⟩ : Opens M) ≃ₜ (⟨e.target, e.open_target⟩ : Opens N) :=
  e.toHomeomorphSourceTarget

theorem opensHomeoOf_apply {M N : Type*} [TopologicalSpace M]
    [TopologicalSpace N] (e : OpenPartialHomeomorph M N)
    (x : (⟨e.source, e.open_source⟩ : Opens M)) :
    ((opensHomeoOf e x : (⟨e.target, e.open_target⟩ : Opens N)) : N) = e x := rfl

/-! ### The half-turn of the cone `C_θ` about its apex -/

section HalfTurn

/-- The half-turn `(r, φ) ↦ (r, φ + 1/2)` of the cover `𝔻_∞ × {*}` of the cones. -/
def halfRotCover : DInfty × Unit ≃ₜ DInfty × Unit where
  toFun y := (DInfty.rot (1 / 2) y.1, y.2)
  invFun y := (DInfty.rot (-(1 / 2)) y.1, y.2)
  left_inv y := by simp only [← DInfty.rot_add, neg_add_cancel, DInfty.rot_zero]
  right_inv y := by simp only [← DInfty.rot_add, add_neg_cancel, DInfty.rot_zero]
  continuous_toFun := ((DInfty.continuous_rot _).comp continuous_fst).prodMk continuous_snd
  continuous_invFun := ((DInfty.continuous_rot _).comp continuous_fst).prodMk continuous_snd

theorem halfRotCover_smul (k : GammaA 1) (y : DInfty × Unit) :
    halfRotCover (k • y) = k • halfRotCover y := by
  show (DInfty.rot (1 / 2) (k • y).1, (k • y).2) = k • (DInfty.rot (1 / 2) y.1, y.2)
  simp only [DInfty.smul_prod_def, DInfty.smul_def, ← DInfty.rot_add, add_comm (1 / 2 : ℝ)]

/-- **The half-turn of `C_θ` about its apex**: the rotation by `θ/2` of the spherical cone. -/
def SphCone.halfRot (θ : ConeAngle) : SphCone θ ≃ₜ SphCone θ :=
  orbitsHomeomorph halfRotCover halfRotCover_smul

theorem SphCone.halfRot_mk (θ : ConeAngle) (y : DInfty × Unit) :
    SphCone.halfRot θ (SphCone.mk θ y) = SphCone.mk θ (halfRotCover y) := rfl

theorem SphCone.halfRot_apex (θ : ConeAngle) :
    SphCone.halfRot θ (SphCone.apex θ) = SphCone.apex θ := by
  show SphCone.mk θ (DInfty.rot (1 / 2) DInfty.apex, ()) = SphCone.mk θ (DInfty.apex, ())
  rw [DInfty.rot_apex]

/-- The rotation `φ ↦ φ + t` of the cover is read by the conical developing map as the rotation
of angle `α t`. -/
theorem conicalDev_rot {α : ℝ} (hα : α ≠ 0) (t : ℝ) (p : DInfty) (z : Unit) :
    conicalDev α Unit (DInfty.rot t p, z) =
      (Complex.exp ((α * t : ℝ) * Complex.I) * (conicalDev α Unit (p, z)).1, z) := by
  rcases p.pos_or_eq_apex with hp | rfl
  · obtain ⟨q, rfl⟩ : p ∈ range DInfty.posEmb := by rw [DInfty.range_posEmb]; exact hp
    obtain ⟨⟨r, φ⟩, hr⟩ := q
    have : DInfty.rot t (DInfty.posEmb ⟨(r, φ), hr⟩) = DInfty.posEmb ⟨(r, φ + t), hr⟩ := by
      rw [DInfty.rot_of_pos hr]; rfl
    rw [this, conicalDev_posEmb hα, conicalDev_posEmb hα]
    simp only [Prod.mk.injEq, and_true]
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast; ring
  · simp [conicalDev]

theorem sphConeDev_halfRot (θ : ConeAngle) (y : DInfty × Unit) :
    sphConeDev θ.1 (halfRotCover y) = rotSO3 (Circle.exp (θ.1 / 2)) • sphConeDev θ.1 y := by
  show stereoInv (conicalDev θ.1 Unit (DInfty.rot (1 / 2) y.1, y.2)).1 =
    rotSO3 (Circle.exp (θ.1 / 2)) • stereoInv (conicalDev θ.1 Unit (y.1, y.2)).1
  rw [conicalDev_rot θ.2.ne', rotSO3_smul_stereoInv, Circle.coe_exp]
  show stereoInv (Complex.exp ((θ.1 * (1 / 2) : ℝ) * Complex.I) * _) = _
  rw [show θ.1 * (1 / 2) = θ.1 / 2 by ring]

/-- **The half-turn of `C_θ` is an automorphism** (`isAEMorphismOf_quotientBase`: its lift is read
by the developing map as the rotation of angle `θ/2` about the polar axis). -/
theorem SphCone.isAEMorphism_halfRot (θ : ConeAngle) :
    IsAEMorphism SO3 Sph2 (SphCone.halfRot θ : SphCone θ → SphCone θ) := by
  have hD := isLocalHomeomorphOn_polarConeDev (isOpenEmbedding_stereoInv (W := ℂ)) θ.2.ne'
  exact isAEMorphismOf_quotientBase one_ne_zero one_ne_zero hD hD
    (isMaximalAEAtlas_aeAtlas SO3 Sph2 (SphCone θ)) (sphCone_isAEMorphism_mk θ)
    (isMaximalAEAtlas_aeAtlas SO3 Sph2 (SphCone θ)) (sphCone_isAEMorphism_mk θ)
    (SphCone.halfRot θ).continuous halfRotCover.continuous
    (fun y hy => by show 0 < (DInfty.rot (1 / 2) y.1).r; rw [DInfty.rot_r]; exact hy)
    (fun y => rfl)
    (fun y _ => ⟨rotSO3 (Circle.exp (θ.1 / 2)), Eventually.of_forall fun y' =>
      sphConeDev_halfRot θ y'⟩)

/-- **The half-turn moves every point off the apex** (`1/2 ∉ ℤ`). -/
theorem SphCone.halfRot_ne (θ : ConeAngle) {z : SphCone θ} (hz : z ≠ SphCone.apex θ) :
    SphCone.halfRot θ z ≠ z := by
  obtain ⟨y, rfl⟩ := Quotient.mk_surjective z
  have hy : 0 < y.1.r := by
    by_contra h; exact hz (SphCone.eq_apex_of_not_pos θ y h)
  intro heq
  obtain ⟨k, hk⟩ := exists_smul_eq_of_orbitMk_eq (Γ := GammaA 1) heq
  have h1 := congrArg (fun w : DInfty × Unit => w.1.θ) hk
  simp only [DInfty.smul_prod_def, DInfty.smul_def] at h1
  have hθ : ∀ (t : ℝ) (q : DInfty), 0 < q.r → (DInfty.rot t q).θ = q.θ + t := fun t q hq => by
    rw [DInfty.rot_of_pos hq]
  have hy' : 0 < (halfRotCover y).1.r := by
    show 0 < (DInfty.rot (1 / 2) y.1).r; rw [DInfty.rot_r]; exact hy
  rw [hθ _ _ hy'] at h1
  have h2 : (halfRotCover y).1.θ = y.1.θ + 1 / 2 := hθ _ _ hy
  rw [h2] at h1
  have h3 : (k.toInt : ℝ) = -(1 / 2) := by linarith
  have h4 : (2 : ℝ) * k.toInt = -1 := by rw [h3]; ring
  have h5 : (2 * k.toInt : ℤ) = -1 := by exact_mod_cast h4
  omega

/-- Every open neighbourhood of the apex of `C_θ` has a point off the apex (`C_θ ≅ ℂ`). -/
theorem SphCone.exists_ne_apex_of_isOpen (θ : ConeAngle) {D : Set (SphCone θ)} (hD : IsOpen D)
    (hapex : SphCone.apex θ ∈ D) : ∃ z ∈ D, z ≠ SphCone.apex θ := by
  by_contra hcon
  push Not at hcon
  have hDeq : D = {SphCone.apex θ} :=
    Subset.antisymm (fun z hz => hcon z hz) (singleton_subset_iff.2 hapex)
  have ho : IsOpen ((SphCone.homeoComplex θ) '' D) := (SphCone.homeoComplex θ).isOpenMap D hD
  rw [hDeq, image_singleton] at ho
  exact not_isOpen_singleton _ ho

end HalfTurn

/-! ### The suspension of a locally read open partial homeomorphism -/

section SuspLocal

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  {σ₀ : RaySphere W} {S : Type*} [TopologicalSpace S]
  [SingularGXStructure (SpecialOrth W) (RaySphere W) S]

/-- **The suspension of a local isomorphism of `Σ` is a local isomorphism of `susp(Σ)`**: if an
open partial homeomorphism `F` of `Σ` keeps the regular points regular and is read, at each of
them, by an element of `SO(W)` in charts, then `susp*(F)` (`GX.Susp.posChart`) is an a.e.
isomorphism of `susp*(F.source)` onto `susp*(F.target)`, read in the cone charts by `1 ⊕ A`. -/
theorem thurston_isAEMorphism_posChart [PreconnectedSpace S] [LocallyConnectedSpace S]
    (F : OpenPartialHomeomorph S S)
    (hF : ∀ σ ∈ F.source, σ ∈ Reg (SpecialOrth W) (RaySphere W) S →
      F σ ∈ Reg (SpecialOrth W) (RaySphere W) S ∧
        ∀ e ∈ aeAtlas (SpecialOrth W) (RaySphere W) S, σ ∈ e.source →
          ∀ e' ∈ aeAtlas (SpecialOrth W) (RaySphere W) S, F σ ∈ e'.source →
            ∃ A : SpecialOrth W, ∀ᶠ y in 𝓝 σ, e' (F y) = A • e y) :
    letI := thurstonStructure σ₀ S
    IsAEMorphism (SpecialOrth (PolarSum W)) (RaySphere (PolarSum W))
      (opensHomeoOf (Susp.posChart F) : _ → _) := by
  letI := thurstonStructure σ₀ S
  set P := Susp.posChart F with hPdef
  set U₁ : Opens (Susp S) := ⟨_, P.open_source⟩
  set U₂ : Opens (Susp S) := ⟨_, P.open_target⟩
  have hA := isAEAtlas_thurstonAtlas (σ₀ := σ₀) (S := S)
  refine isAEMorphism_of_val_comp U₂ ?_
  refine isAEMorphism_of_opens_of_eventually U₁
    (continuous_subtype_val.comp (opensHomeoOf P).continuous) fun x hx => ?_
  have hxs : (x : Susp S) ∈ P.source := x.2
  rw [hPdef, Susp.posChart_source] at hxs
  obtain ⟨q, ⟨hq1, hq2⟩, hqx⟩ := hxs
  have hσ : q.1 ∈ Reg (SpecialOrth W) (RaySphere W) S :=
    thurston_mem_reg_of_mk_mem_reg (σ₀ := σ₀) hq2 (by rw [hqx]; exact hx)
  obtain ⟨hFσ, hread⟩ := hF q.1 hq1 hσ
  obtain ⟨e, he, hσe⟩ := mem_support.1 hσ
  obtain ⟨e', he', hFσe'⟩ := mem_support.1 hFσ
  obtain ⟨B, hB⟩ := hread e he hσe e' he' hFσe'
  have hPx : ((opensHomeoOf P x : U₂) : Susp S) = Susp.mk (F q.1, q.2) := by
    show P (x : Susp S) = _
    rw [← hqx]; rfl
  have hmem : ∀ {f : OpenPartialHomeomorph S (RaySphere W)},
      f ∈ aeAtlas (SpecialOrth W) (RaySphere W) S →
      (sphConic σ₀).coneChart f ∈
        aeAtlas (SpecialOrth (PolarSum W)) (RaySphere (PolarSum W)) (Susp S) := fun {f} hf =>
    hA.subset_maximalAEAtlas ⟨f, hf, rfl⟩
  have hsrc : ∀ {f : OpenPartialHomeomorph S (RaySphere W)} {q' : S × ℝ≥0}, q'.1 ∈ f.source →
      0 < q'.2 → Susp.mk q' ∈ ((sphConic σ₀).coneChart f).source := fun {f q'} h1 h2 => by
    rw [(sphConic σ₀).coneChart_source_of_isFull (sphConic_isFull σ₀)]
    exact ⟨q', ⟨h1, h2⟩, rfl⟩
  refine ⟨by
      show ((opensHomeoOf P x : U₂) : Susp S) ∈ _
      rw [hPx]; exact thurston_mk_mem_reg hFσ hq2,
    (sphConic σ₀).coneChart e, hmem he, by rw [← hqx]; exact hsrc hσe hq2,
    (sphConic σ₀).coneChart e', hmem he',
    by
      show ((opensHomeoOf P x : U₂) : Susp S) ∈ _
      rw [hPx]; exact hsrc (q' := (F q.1, q.2)) hFσe' hq2,
    liftSO W B, ?_⟩
  have hev : ∀ᶠ z in 𝓝 (x : Susp S),
      (sphConic σ₀).coneChart e' (P z) = liftSO W B • (sphConic σ₀).coneChart e z := by
    rw [← hqx, Susp.nhds_mk_of_pos hq2, eventually_map]
    filter_upwards [continuous_fst.continuousAt.eventually hB] with q' h1
    show (sphConic σ₀).coneChart e' (Susp.mk (F q'.1, q'.2)) = _
    rw [(sphConic σ₀).coneChart_apply, (sphConic σ₀).coneChart_apply]
    show (sphConic σ₀).φ.symm (Susp.mk (e' (F q'.1), q'.2)) = _
    rw [h1, sphConic_symm_smul]
  exact continuous_subtype_val.continuousAt.eventually hev

end SuspLocal

/-! ### Radial readings: chart changes fixing the north pole -/

instance Susp.instNonempty {S : Type*} [Nonempty S] : Nonempty (Susp S) :=
  ⟨Susp.mk (Classical.arbitrary S, 0)⟩

section Radial

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

/-- **An element of `SO(ℝ ⊕ W)` fixing the north pole is `1 ⊕ A`** for some `A ∈ SO(W)` (the
argument of `GX.exists_rot_of_smul_northPole`, for any `W`). -/
theorem exists_liftSO_of_smul_northPole {g : SpecialOrth (PolarSum W)}
    (hg : g • (northPole : RaySphere (PolarSum W)) = northPole) :
    ∃ A : SpecialOrth W, g = liftSO W A := by
  set L : PolarSum W ≃ₗᵢ[ℝ] PolarSum W := (g : PolarSum W ≃ₗᵢ[ℝ] PolarSum W)
  have hN : L (WithLp.toLp 2 ((1 : ℝ), (0 : W))) = WithLp.toLp 2 (1, 0) :=
    congrArg Subtype.val hg
  have hfst : ∀ w : W, (L (WithLp.toLp 2 ((0 : ℝ), w))).fst = 0 := by
    intro w
    have h := L.inner_map_map (WithLp.toLp 2 ((0 : ℝ), w)) (WithLp.toLp 2 ((1 : ℝ), (0 : W)))
    rw [hN] at h
    simpa using h
  let A₀ : W →ₗ[ℝ] W :=
    { toFun := fun w => (L (WithLp.toLp 2 ((0 : ℝ), w))).snd
      map_add' := fun w w' => by
        rw [show (WithLp.toLp 2 ((0 : ℝ), w + w') : PolarSum W) =
          WithLp.toLp 2 ((0 : ℝ), w) + WithLp.toLp 2 ((0 : ℝ), w') by simp [← WithLp.toLp_add],
          map_add]
        rfl
      map_smul' := fun c w => by
        rw [show (WithLp.toLp 2 ((0 : ℝ), c • w) : PolarSum W) = c • WithLp.toLp 2 ((0 : ℝ), w) by
          simp [← WithLp.toLp_smul], map_smul]
        rfl }
  have hnorm : ∀ w, ‖A₀ w‖ = ‖w‖ := by
    intro w
    have h1 := norm_polarSum_sq (L (WithLp.toLp 2 ((0 : ℝ), w)))
    rw [LinearIsometryEquiv.norm_map, norm_toLp_sq, hfst] at h1
    have h2 : ‖A₀ w‖ ^ 2 = ‖w‖ ^ 2 := by
      show ‖(L (WithLp.toLp 2 ((0 : ℝ), w))).snd‖ ^ 2 = _
      linarith
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2
  let A₁ : W →ₗᵢ[ℝ] W := ⟨A₀, hnorm⟩
  let A : W ≃ₗᵢ[ℝ] W := A₁.toLinearIsometryEquiv rfl
  have hA : ∀ w, A w = (L (WithLp.toLp 2 ((0 : ℝ), w))).snd := fun w => rfl
  have hL : L = liftIsom A := by
    refine LinearIsometryEquiv.ext fun x => ?_
    have hx : x = (x.fst) • WithLp.toLp 2 ((1 : ℝ), (0 : W)) + WithLp.toLp 2 ((0 : ℝ), x.snd) := by
      apply WithLp.ofLp_injective 2
      refine Prod.ext ?_ ?_ <;> simp
    rw [liftIsom_apply, hx, map_add, map_smul, hN]
    apply WithLp.ofLp_injective 2
    refine Prod.ext ?_ ?_
    · simp [hfst]
    · simp [hA]
  have hdet : LinearMap.det (A.toLinearEquiv : W →ₗ[ℝ] W) = 1 := by
    rw [← det_liftIsom, ← hL]; exact g.2
  exact ⟨⟨A, hdet⟩, Subtype.ext hL⟩

/-- The polar coordinate `x₀` of a point of `𝕊(ℝ ⊕ W)` read through an element `g`:
`(g x)₀ = ⟨x, g⁻¹ N⟩`. -/
theorem fst_specialOrth_smul (g : SpecialOrth (PolarSum W)) (x : RaySphere (PolarSum W)) :
    ((g • x : RaySphere (PolarSum W)) : PolarSum W).fst =
      inner ℝ (x : PolarSum W) ((g⁻¹ • northPole : RaySphere (PolarSum W)) : PolarSum W) := by
  have h := (g : PolarSum W ≃ₗᵢ[ℝ] PolarSum W).inner_map_map (x : PolarSum W)
    ((g⁻¹ • northPole : RaySphere (PolarSum W)) : PolarSum W)
  rw [← h]
  have h2 : (g : PolarSum W ≃ₗᵢ[ℝ] PolarSum W)
      ((g⁻¹ • northPole : RaySphere (PolarSum W)) : PolarSum W) =
      ((northPole : RaySphere (PolarSum W)) : PolarSum W) := by
    rw [← coe_specialOrth_smul, smul_inv_smul]
  rw [h2]
  show _ = inner ℝ ((g : PolarSum W ≃ₗᵢ[ℝ] PolarSum W) (x : PolarSum W))
    (WithLp.toLp 2 ((1 : ℝ), (0 : W)))
  simp
  rfl

/-- The polar profile `c(t) = (1 - t²)/(1 + t²)`, the polar coordinate of the point at radius `t`
of a cone chart. -/
def polarProfile (t : ℝ≥0) : ℝ := (1 - (t : ℝ) ^ 2) / (1 + (t : ℝ) ^ 2)

theorem polarProfile_injective : Injective polarProfile := by
  intro t t' h
  unfold polarProfile at h
  have h1 : 0 < 1 + (t : ℝ) ^ 2 := by positivity
  have h2 : 0 < 1 + (t' : ℝ) ^ 2 := by positivity
  rw [div_eq_div_iff h1.ne' h2.ne'] at h
  have h3 : (t : ℝ) ^ 2 = (t' : ℝ) ^ 2 := by nlinarith
  have := (sq_eq_sq₀ t.2 t'.2).1 h3
  exact NNReal.coe_injective this

theorem continuous_polarProfile : Continuous polarProfile := by
  unfold polarProfile
  exact (continuous_const.sub (NNReal.continuous_coe.pow 2)).div
    (continuous_const.add (NNReal.continuous_coe.pow 2)) fun t => by positivity

theorem polarProfile_zero : polarProfile 0 = 1 := by simp [polarProfile]

variable {σ₀ : RaySphere W} {S : Type*} [TopologicalSpace S]

/-- **The polar coordinate of a cone chart is the profile of the radius**: the point `(σ, t)` is
sent to the point at polar coordinate `c(t)`. -/
theorem fst_coneChart (e : OpenPartialHomeomorph S (RaySphere W)) (q : S × ℝ≥0) :
    (((sphConic σ₀).coneChart e (Susp.mk q) : RaySphere (PolarSum W)) : PolarSum W).fst =
      polarProfile q.2 := by
  rw [(sphConic σ₀).coneChart_apply, sphConic_symm_mk, stereoInv_fst, norm_smul, norm_raySphere,
    mul_one, Real.norm_eq_abs]
  simp [polarProfile]

/-- The cone charts are injective on all of `susp(Σ)` off `O`, through the polar chart. -/
theorem coneChart_mk_eq_iff {e e' : OpenPartialHomeomorph S (RaySphere W)} {q q' : S × ℝ≥0} :
    (sphConic σ₀).coneChart e (Susp.mk q) = (sphConic σ₀).coneChart e' (Susp.mk q') ↔
      (Susp.mk (e q.1, q.2) : Susp (RaySphere W)) = Susp.mk (e' q'.1, q'.2) := by
  rw [(sphConic σ₀).coneChart_apply, (sphConic σ₀).coneChart_apply]
  have htgt : ∀ a, a ∈ (sphConic σ₀).φ.target := fun a => by
    rw [show (sphConic σ₀).φ.target = univ from sphConic_isFull σ₀]; trivial
  constructor
  · intro h
    have := congrArg (sphConic σ₀).φ h
    rwa [(sphConic σ₀).φ.right_inv (htgt _), (sphConic σ₀).φ.right_inv (htgt _)] at this
  · intro h; rw [h]

/-- **Two vectors with the same inner products against a nonempty open subset of the unit sphere
are equal** (the cone over it spans: `GX.eq_of_eqOn_sphere` for two rank-one maps). -/
theorem eq_of_inner_eqOn_sphere {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {U : Set (RaySphere V)} (hU : IsOpen U) (hne : U.Nonempty) {q q' : V}
    (h : ∀ σ ∈ U, inner ℝ (σ : V) q = inner ℝ (σ : V) q') : q = q' := by
  by_contra hqq
  have hd : q - q' ≠ 0 := sub_ne_zero.2 hqq
  have hfg := eq_of_eqOn_sphere (f := (innerₛₗ ℝ q).smulRight (q - q'))
    (g := (innerₛₗ ℝ q').smulRight (q - q')) hU hne fun σ hσ => by
      simp only [LinearMap.smulRight_apply, innerₛₗ_apply_apply]
      rw [real_inner_comm, h σ hσ, real_inner_comm]
  have h2 := LinearMap.congr_fun hfg (q - q')
  simp only [LinearMap.smulRight_apply, innerₛₗ_apply_apply] at h2
  have h3 : (inner ℝ (q - q') (q - q')) • (q - q') = 0 := by
    rw [inner_sub_left, sub_smul, h2, sub_self]
  rcases smul_eq_zero.1 h3 with h4 | h4
  · exact hd (inner_self_eq_zero.1 h4)
  · exact hd h4

variable [SingularGXStructure (SpecialOrth W) (RaySphere W) S]

/-- **A local isomorphism fixing the centre is read, near the rays, by elements fixing the north
pole** (`RamcovGX.tex:1933`, "it preserves distances and geodesics"): let `φ : U₁ → U₂` be an
a.e. isomorphism of open subsets of `susp(Σ)` fixing `O`, with the ball `{r < ε}` inside `U₁`; if
near a regular point `(σ, t)`, `t < ε`, the polar coordinate of `φ` is `c(r ∘ φ) = (g κ_e)₀` for a
cone chart `κ_e` (as it is when `φ` reads as `g` from `κ_e` into a cone chart), then `g` fixes the
north pole. Continuation along the ray `s ↦ (σ, s)`, `s ∈ ]0, t]`: the vector `q = g⁻¹ N` with
`c(r ∘ φ) = ⟨κ_e, q⟩` near `(σ, s)` is unique (`eq_of_inner_eqOn_sphere`) and locally constant, and
at `s → 0` the identity becomes `1 = c(0) = ⟨N, q⟩`. -/
theorem thurston_reading_fixes_northPole [PreconnectedSpace S] [LocallyConnectedSpace S]
    [Nonempty S] {U₁ U₂ : Opens (Susp S)} {φ : U₁ ≃ₜ U₂}
    (hφ : letI := thurstonStructure σ₀ S
      IsAEMorphism (SpecialOrth (PolarSum W)) (RaySphere (PolarSum W)) (φ : U₁ → U₂))
    {O : Susp S} (hO : O ∈ (Susp.O : Set (Susp S))) (hOU : O ∈ U₁)
    (hfix : (φ ⟨O, hOU⟩ : Susp S) ∈ (Susp.O : Set (Susp S)))
    {ε : ℝ≥0} (hball : (Susp.ball ε : Set (Susp S)) ⊆ U₁)
    {σ : S} (hσ : σ ∈ Reg (SpecialOrth W) (RaySphere W) S) {t : ℝ≥0} (ht : 0 < t) (htε : t < ε)
    {e : OpenPartialHomeomorph S (RaySphere W)}
    (he : e ∈ aeAtlas (SpecialOrth W) (RaySphere W) S) (hσe : σ ∈ e.source)
    {g : SpecialOrth (PolarSum W)}
    (hg : ∀ᶠ z in 𝓝 (Susp.mk (σ, t)), polarProfile (opensOPH φ z).r =
      ((g • (sphConic σ₀).coneChart e z : RaySphere (PolarSum W)) : PolarSum W).fst) :
    g • (northPole : RaySphere (PolarSum W)) = northPole := by
  letI := thurstonStructure σ₀ S
  have hA := isAEAtlas_thurstonAtlas (σ₀ := σ₀) (S := S)
  set F : Susp S → Susp S := (opensOPH φ : Susp S → Susp S) with hFdef
  set κ := (sphConic σ₀).coneChart e with hκ
  have hκmem : κ ∈ aeAtlas (SpecialOrth (PolarSum W)) (RaySphere (PolarSum W)) (Susp S) :=
    hA.subset_maximalAEAtlas ⟨e, he, rfl⟩
  have hκsrc : ∀ {s : ℝ≥0}, 0 < s → Susp.mk (σ, s) ∈ κ.source := fun {s} hs => by
    rw [hκ, (sphConic σ₀).coneChart_source_of_isFull (sphConic_isFull σ₀)]
    exact ⟨(σ, s), ⟨hσe, hs⟩, rfl⟩
  have hγU : ∀ {s : ℝ≥0}, s < ε → Susp.mk (σ, s) ∈ U₁ := fun {s} hs => hball hs
  have hFO : F O ∈ (Susp.O : Set (Susp S)) := by
    rw [hFdef, opensOPH_apply φ hOU]; exact hfix
  -- `Λ q s`: near `(σ, s)`, `c(r ∘ F) = ⟨κ, q⟩`
  let Λ : PolarSum W → ℝ≥0 → Prop := fun q s => ∀ᶠ z in 𝓝 (Susp.mk (σ, s)),
    polarProfile (F z).r = inner ℝ ((κ z : RaySphere (PolarSum W)) : PolarSum W) q
  have hΛt : Λ (((g⁻¹ • northPole : RaySphere (PolarSum W)) : PolarSum W)) t := by
    filter_upwards [hg] with z hz
    rw [hz, fst_specialOrth_smul]
  -- existence of `q` at each `s ∈ ]0, ε[`
  have hex : ∀ s : ℝ≥0, 0 < s → s < ε → ∃ q, Λ q s := by
    intro s hs hsε
    have hγreg : Susp.mk (σ, s) ∈ Reg (SpecialOrth (PolarSum W)) (RaySphere (PolarSum W))
        (Susp S) := thurston_mk_mem_reg hσ hs
    obtain ⟨hFreg, hread⟩ := hφ.eventually_smul_eq_of_opens (F := F)
      (fun y hy => opensOPH_apply φ hy) (hγU hsε) hγreg
    have hFne : F (Susp.mk (σ, s)) ∉ (Susp.O : Set (Susp S)) := by
      intro hm
      have h1 : F (Susp.mk (σ, s)) = F O := Susp.eq_of_mem_O hm hFO
      rw [hFdef, opensOPH_apply φ (hγU hsε), opensOPH_apply φ hOU] at h1
      have h2 := congrArg Subtype.val (φ.injective (Subtype.ext h1))
      have h3 : (Susp.mk (σ, s) : Susp S).r = 0 := by
        have : (Susp.mk (σ, s) : Susp S) = O := h2
        rw [this]; exact hO
      exact hs.ne' h3
    set w := F (Susp.mk (σ, s)) with hw
    have hwr : 0 < w.r := Susp.notMem_O_iff.1 hFne
    have hwmk : Susp.mk (w.dir, w.r) = w := Susp.mk_dir_r w
    have hτ : w.dir ∈ Reg (SpecialOrth W) (RaySphere W) S :=
      thurston_mem_reg_of_mk_mem_reg (σ₀ := σ₀) hwr (by rw [hwmk]; exact hFreg)
    obtain ⟨e', he', hτe'⟩ := mem_support.1 hτ
    have hκ'mem : (sphConic σ₀).coneChart e' ∈
        aeAtlas (SpecialOrth (PolarSum W)) (RaySphere (PolarSum W)) (Susp S) :=
      hA.subset_maximalAEAtlas ⟨e', he', rfl⟩
    have hwsrc : w ∈ ((sphConic σ₀).coneChart e').source := by
      rw [(sphConic σ₀).coneChart_source_of_isFull (sphConic_isFull σ₀), ← hwmk]
      exact ⟨(w.dir, w.r), ⟨hτe', hwr⟩, rfl⟩
    obtain ⟨gs, hgs⟩ := hread κ hκmem (hκsrc hs) _ hκ'mem hwsrc
    refine ⟨((gs⁻¹ • northPole : RaySphere (PolarSum W)) : PolarSum W), ?_⟩
    filter_upwards [hgs] with z hz
    rw [← fst_specialOrth_smul, ← hz, ← Susp.mk_dir_r (F z), fst_coneChart]
    rfl
  -- uniqueness of `q`
  have huniq : ∀ s : ℝ≥0, 0 < s → ∀ q q', Λ q s → Λ q' s → q = q' := by
    intro s hs q q' h1 h2
    obtain ⟨N', hN'sub, hN'o, hγN'⟩ := mem_nhds_iff.1 (h1.and h2)
    refine eq_of_inner_eqOn_sphere (κ.isOpen_image_source_inter hN'o)
      ⟨_, ⟨_, ⟨hκsrc hs, hγN'⟩, rfl⟩⟩ ?_
    rintro _ ⟨z, ⟨-, hz⟩, rfl⟩
    exact (hN'sub hz).1.symm.trans (hN'sub hz).2
  -- openness
  have hγc : Continuous fun s : ℝ≥0 => (Susp.mk (σ, s) : Susp S) :=
    Susp.continuous_mk.comp (continuous_const.prodMk continuous_id)
  have hopen : ∀ q s, Λ q s → ∀ᶠ s' in 𝓝 s, Λ q s' := fun q s h =>
    (hγc.tendsto s).eventually (eventually_eventually_nhds.2 h)
  -- continuation along `]0, t]`
  have hchain : ∀ s ∈ Ioc 0 t, Λ (((g⁻¹ • northPole : RaySphere (PolarSum W)) : PolarSum W)) s := by
    intro s hs
    have := isPreconnected_Ioc.induction₂' (fun a b => ∀ q, Λ q a → Λ q b) (fun a ha => ?_)
      (fun _ _ _ _ _ _ h₁ h₂ q hq => h₂ q (h₁ q hq)) (show t ∈ Ioc (0 : ℝ≥0) t from ⟨ht, le_rfl⟩)
      hs
    · exact this _ hΛt
    · obtain ⟨qa, hqa⟩ := hex a ha.1 (lt_of_le_of_lt ha.2 htε)
      filter_upwards [mem_nhdsWithin_of_mem_nhds (hopen qa a hqa), self_mem_nhdsWithin]
        with b hb hbI
      exact ⟨fun q hq => by rw [huniq a ha.1 q qa hq hqa]; exact hb,
        fun q hq => by rw [huniq b hbI.1 q qa hq hb]; exact hqa⟩
  -- the limit at `s → 0`
  set q₀ : PolarSum W := ((g⁻¹ • northPole : RaySphere (PolarSum W)) : PolarSum W) with hq₀
  have hpt : ∀ s ∈ Ioc 0 t, polarProfile (F (Susp.mk (σ, s))).r =
      inner ℝ ((κ (Susp.mk (σ, s)) : RaySphere (PolarSum W)) : PolarSum W) q₀ :=
    fun s hs => (hchain s hs).self_of_nhds
  have hO' : (Susp.mk (σ, 0) : Susp S) = O := Susp.eq_of_mem_O rfl hO
  have hFc : ContinuousAt F O := (opensOPH φ).continuousAt (show O ∈ (opensOPH φ).source from hOU)
  have hL : Tendsto (fun s : ℝ≥0 => polarProfile (F (Susp.mk (σ, s))).r) (𝓝[>] 0) (𝓝 1) := by
    have h1 : Tendsto (fun s : ℝ≥0 => (Susp.mk (σ, s) : Susp S)) (𝓝[>] 0) (𝓝 O) := by
      rw [← hO']; exact (hγc.tendsto 0).mono_left nhdsWithin_le_nhds
    have h2 := (continuous_polarProfile.tendsto _).comp
      ((Susp.continuous_r.tendsto _).comp (hFc.tendsto.comp h1))
    rwa [show (F O).r = 0 from hFO, polarProfile_zero] at h2
  have hR : Tendsto (fun s : ℝ≥0 =>
      inner ℝ ((κ (Susp.mk (σ, s)) : RaySphere (PolarSum W)) : PolarSum W) q₀) (𝓝[>] 0)
      (𝓝 (inner ℝ ((northPole : RaySphere (PolarSum W)) : PolarSum W) q₀)) := by
    have hκγ : ∀ s : ℝ≥0, (κ (Susp.mk (σ, s)) : RaySphere (PolarSum W)) =
        stereoInv ((s : ℝ) • (e σ : W)) := fun s => rfl
    have hc : Continuous fun s : ℝ≥0 =>
        inner ℝ ((stereoInv ((s : ℝ) • (e σ : W)) : RaySphere (PolarSum W)) : PolarSum W) q₀ :=
      (continuous_subtype_val.comp (continuous_stereoInv.comp
        (NNReal.continuous_coe.smul continuous_const))).inner continuous_const
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simp only [NNReal.coe_zero, zero_smul, stereoInv_zero] at this
    simp only [hκγ]
    exact this
  have hlim : (1 : ℝ) = inner ℝ ((northPole : RaySphere (PolarSum W)) : PolarSum W) q₀ :=
    tendsto_nhds_unique (hL.congr' (by
      filter_upwards [Ioo_mem_nhdsGT ht] with s hs using hpt s ⟨hs.1, hs.2.le⟩)) hR
  -- `q₀ = N`: two unit vectors with inner product `1`
  have hq₀N : q₀ = ((northPole : RaySphere (PolarSum W)) : PolarSum W) := by
    have hn1 : ‖q₀‖ = 1 := norm_raySphere _
    have hn2 : ‖((northPole : RaySphere (PolarSum W)) : PolarSum W)‖ = 1 := norm_raySphere _
    have h0 : ‖q₀ - ((northPole : RaySphere (PolarSum W)) : PolarSum W)‖ ^ 2 = 0 := by
      rw [@norm_sub_sq_real, hn1, hn2, real_inner_comm, ← hlim]; ring
    exact sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff (n := 2) two_ne_zero |>.1 h0))
  have : g⁻¹ • (northPole : RaySphere (PolarSum W)) = northPole := Subtype.ext hq₀N
  calc g • (northPole : RaySphere (PolarSum W)) = g • (g⁻¹ • northPole) := by rw [this]
    _ = northPole := smul_inv_smul g _

/-- **Near the centre, a local isomorphism fixing it is a suspension** (`RamcovGX.tex:1933`: "it
preserves distances and geodesics. By considering the sphere of some radius `ε > 0` centered at
`O` …"): an a.e. isomorphism `φ : U₁ → U₂` of open subsets of `susp(Σ)` fixing `O ∈ U₁` is, on a
ball `{r < ε} ⊆ U₁`, `susp(f)` for a continuous `f : Σ → Σ` which keeps the regular points
regular and is read at each of them by an element of `SO(W)`. Its chart changes fix the north pole
(`thurston_reading_fixes_northPole`), so are `1 ⊕ A` (`exists_liftSO_of_smul_northPole`): `φ`
keeps the radius and, on the rays over regular points, its direction does not depend on the
radius; density of the regular part does the rest. -/
theorem thurston_eq_map_near_centre [PreconnectedSpace S] [LocallyConnectedSpace S] [Nonempty S]
    [T2Space S] {U₁ U₂ : Opens (Susp S)} {φ : U₁ ≃ₜ U₂}
    (hφ : letI := thurstonStructure σ₀ S
      IsAEMorphism (SpecialOrth (PolarSum W)) (RaySphere (PolarSum W)) (φ : U₁ → U₂))
    {O : Susp S} (hO : O ∈ (Susp.O : Set (Susp S))) (hOU : O ∈ U₁)
    (hfix : (φ ⟨O, hOU⟩ : Susp S) ∈ (Susp.O : Set (Susp S))) :
    ∃ ε : ℝ≥0, 0 < ε ∧ (Susp.ball ε : Set (Susp S)) ⊆ U₁ ∧ ∃ f : S → S, Continuous f ∧
      (∀ z ∈ (Susp.ball ε : Set (Susp S)), (opensOPH φ : Susp S → Susp S) z = Susp.map f z) ∧
      ∀ σ ∈ Reg (SpecialOrth W) (RaySphere W) S, f σ ∈ Reg (SpecialOrth W) (RaySphere W) S ∧
        ∀ e ∈ aeAtlas (SpecialOrth W) (RaySphere W) S, σ ∈ e.source →
          ∀ e' ∈ aeAtlas (SpecialOrth W) (RaySphere W) S, f σ ∈ e'.source →
            ∃ A : SpecialOrth W, ∀ᶠ y in 𝓝 σ, e' (f y) = A • e y := by
  letI := thurstonStructure σ₀ S
  have hA := isAEAtlas_thurstonAtlas (σ₀ := σ₀) (S := S)
  obtain ⟨ε, hε, hball⟩ := Susp.exists_ball_subset_of_isOpen U₁.isOpen hO hOU
  set F : Susp S → Susp S := (opensOPH φ : Susp S → Susp S) with hFdef
  have hFO : F O ∈ (Susp.O : Set (Susp S)) := by
    rw [hFdef, opensOPH_apply φ hOU]; exact hfix
  have hFc : ∀ z ∈ (U₁ : Set (Susp S)), ContinuousAt F z := fun z hz =>
    (opensOPH φ).continuousAt (show z ∈ (opensOPH φ).source from hz)
  have hmem : ∀ {f : OpenPartialHomeomorph S (RaySphere W)},
      f ∈ aeAtlas (SpecialOrth W) (RaySphere W) S →
      (sphConic σ₀).coneChart f ∈
        aeAtlas (SpecialOrth (PolarSum W)) (RaySphere (PolarSum W)) (Susp S) := fun {f} hf =>
    hA.subset_maximalAEAtlas ⟨f, hf, rfl⟩
  have hsrc : ∀ {f : OpenPartialHomeomorph S (RaySphere W)} {q : S × ℝ≥0}, q.1 ∈ f.source →
      0 < q.2 → Susp.mk q ∈ ((sphConic σ₀).coneChart f).source := fun {f q} h1 h2 => by
    rw [(sphConic σ₀).coneChart_source_of_isFull (sphConic_isFull σ₀)]
    exact ⟨q, ⟨h1, h2⟩, rfl⟩
  have hball' : ∀ {q : S × ℝ≥0}, q.2 < ε → Susp.mk q ∈ (U₁ : Set (Susp S)) := fun {q} hq =>
    hball hq
  -- `F` moves no point other than `O` into `O`
  have hFne : ∀ {q : S × ℝ≥0}, 0 < q.2 → q.2 < ε → F (Susp.mk q) ∉ (Susp.O : Set (Susp S)) := by
    intro q hq hqε hm
    have h1 : F (Susp.mk q) = F O := Susp.eq_of_mem_O hm hFO
    rw [hFdef, opensOPH_apply φ (hball' hqε), opensOPH_apply φ hOU] at h1
    have h2 := congrArg Subtype.val (φ.injective (Subtype.ext h1))
    have h3 : (Susp.mk q : Susp S).r = 0 := by
      have : (Susp.mk q : Susp S) = O := h2
      rw [this]; exact hO
    exact hq.ne' h3
  -- the regular rays go to regular rays
  have hDreg : ∀ σ ∈ Reg (SpecialOrth W) (RaySphere W) S, ∀ t : ℝ≥0, 0 < t → t < ε →
      0 < (F (Susp.mk (σ, t))).r ∧
        (F (Susp.mk (σ, t))).dir ∈ Reg (SpecialOrth W) (RaySphere W) S := by
    intro σ hσ t ht htε
    obtain ⟨hFreg, -⟩ := hφ.eventually_smul_eq_of_opens (F := F)
      (fun y hy => opensOPH_apply φ hy) (hball' (q := (σ, t)) htε) (thurston_mk_mem_reg hσ ht)
    have hwr : 0 < (F (Susp.mk (σ, t))).r := Susp.notMem_O_iff.1 (hFne (q := (σ, t)) ht htε)
    exact ⟨hwr, thurston_mem_reg_of_mk_mem_reg (σ₀ := σ₀) hwr
      (by rw [Susp.mk_dir_r]; exact hFreg)⟩
  -- the radial reading at a regular ray
  have hD : ∀ σ ∈ Reg (SpecialOrth W) (RaySphere W) S, ∀ t : ℝ≥0, 0 < t → t < ε →
      ∀ e ∈ aeAtlas (SpecialOrth W) (RaySphere W) S, σ ∈ e.source →
      ∀ e' ∈ aeAtlas (SpecialOrth W) (RaySphere W) S, (F (Susp.mk (σ, t))).dir ∈ e'.source →
        ∃ A : SpecialOrth W, ∀ᶠ q in 𝓝 (σ, t), (F (Susp.mk q)).r = q.2 ∧
          (F (Susp.mk q)).dir ∈ e'.source ∧ e' (F (Susp.mk q)).dir = A • e q.1 := by
    intro σ hσ t ht htε e he hσe e' he' hτe'
    obtain ⟨hwr, -⟩ := hDreg σ hσ t ht htε
    obtain ⟨-, hread⟩ := hφ.eventually_smul_eq_of_opens (F := F)
      (fun y hy => opensOPH_apply φ hy) (hball' (q := (σ, t)) htε) (thurston_mk_mem_reg hσ ht)
    have hwsrc : F (Susp.mk (σ, t)) ∈ ((sphConic σ₀).coneChart e').source := by
      rw [← Susp.mk_dir_r (F (Susp.mk (σ, t)))]
      exact hsrc (q := ((F (Susp.mk (σ, t))).dir, (F (Susp.mk (σ, t))).r)) hτe' hwr
    obtain ⟨g, hg⟩ := hread _ (hmem he) (hsrc (q := (σ, t)) hσe ht) _ (hmem he') hwsrc
    have hgN : g • (northPole : RaySphere (PolarSum W)) = northPole := by
      refine thurston_reading_fixes_northPole hφ hO hOU hfix hball hσ ht htε he hσe ?_
      filter_upwards [hg] with z hz
      rw [← hz, ← Susp.mk_dir_r (F z), fst_coneChart]
    obtain ⟨A, rfl⟩ := exists_liftSO_of_smul_northPole hgN
    refine ⟨A, ?_⟩
    have hcont : ContinuousAt (fun q : S × ℝ≥0 => F (Susp.mk q)) (σ, t) :=
      (hFc _ (hball' (q := (σ, t)) htε)).comp Susp.continuous_mk.continuousAt
    filter_upwards [Susp.continuous_mk.continuousAt.eventually hg,
      hcont.eventually (((sphConic σ₀).coneChart e').open_source.mem_nhds hwsrc),
      (e.open_source.preimage continuous_fst).mem_nhds hσe,
      Susp.isOpen_posPart.mem_nhds ht] with q h1 h2 h3 h4
    rw [(sphConic σ₀).coneChart_source_of_isFull (sphConic_isFull σ₀)] at h2
    obtain ⟨q', ⟨hq'1, hq'2⟩, hq'⟩ := h2
    rw [← hq', (sphConic σ₀).coneChart_apply, (sphConic σ₀).coneChart_apply,
      ← sphConic_symm_smul] at h1
    have h5 := congrArg (sphConic σ₀).φ h1
    have htgt : ∀ a, a ∈ (sphConic σ₀).φ.target := fun a => by
      rw [show (sphConic σ₀).φ.target = univ from sphConic_isFull σ₀]; trivial
    rw [(sphConic σ₀).φ.right_inv (htgt _), (sphConic σ₀).φ.right_inv (htgt _)] at h5
    obtain ⟨h6, h7⟩ := Prod.ext_iff.1 (Susp.eq_of_mk_eq_of_pos h5 hq'2)
    simp only at h6 h7
    rw [← hq', Susp.dir_mk_of_pos hq'2]
    exact ⟨h7, hq'1, h6⟩
  -- (E1) `F` keeps the radius on the ball
  set P : Set (Susp S) := Susp.mk '' (Reg (SpecialOrth W) (RaySphere W) S ×ˢ Ioi 0) with hPdef
  have hP : IsPortly P := Susp.isPortly_image_mk (isPortly_reg (SpecialOrth W) (RaySphere W) S)
  have hrP : EqOn (fun z => (F z).r) Susp.r ((Susp.ball ε : Set (Susp S)) ∩ P) := by
    rintro _ ⟨hz, ⟨⟨σ, t⟩, ⟨hσ, ht⟩, rfl⟩⟩
    have htε : t < ε := hz
    obtain ⟨-, hτ⟩ := hDreg σ hσ t ht htε
    obtain ⟨e, he, hσe⟩ := mem_support.1 hσ
    obtain ⟨e', he', hτe'⟩ := mem_support.1 hτ
    obtain ⟨A, hA'⟩ := hD σ hσ t ht htε e he hσe e' he' hτe'
    exact hA'.self_of_nhds.1
  have hr : ∀ z ∈ (Susp.ball ε : Set (Susp S)), (F z).r = z.r := by
    refine hrP.of_subset_closure (fun z hz => ?_) Susp.continuous_r.continuousOn
      inter_subset_left (hP.dense.open_subset_closure_inter (Susp.isOpen_ball ε) |>.trans
        (closure_mono (by rw [inter_comm])))
    exact (Susp.continuous_r.continuousAt.comp (hFc z (hball hz))).continuousWithinAt
  -- (E2) along a regular ray, the direction of `F` does not depend on the radius
  have hdirc : ∀ σ ∈ Reg (SpecialOrth W) (RaySphere W) S, ∀ s ∈ Ioo (0 : ℝ≥0) ε,
      ∀ s' ∈ Ioo (0 : ℝ≥0) ε, (F (Susp.mk (σ, s))).dir = (F (Susp.mk (σ, s'))).dir := by
    intro σ hσ s hs s' hs'
    refine isPreconnected_Ioo.induction₂' (fun a b => (F (Susp.mk (σ, a))).dir =
      (F (Susp.mk (σ, b))).dir) (fun a ha => ?_) (fun _ _ _ _ _ _ h₁ h₂ => h₁.trans h₂) hs hs'
    obtain ⟨-, hτ⟩ := hDreg σ hσ a ha.1 ha.2
    obtain ⟨e, he, hσe⟩ := mem_support.1 hσ
    obtain ⟨e', he', hτe'⟩ := mem_support.1 hτ
    obtain ⟨A, hA'⟩ := hD σ hσ a ha.1 ha.2 e he hσe e' he' hτe'
    have hev : ∀ᶠ b in 𝓝 a, (F (Susp.mk (σ, b))).dir ∈ e'.source ∧
        e' (F (Susp.mk (σ, b))).dir = A • e σ :=
      ((continuous_const.prodMk continuous_id).tendsto a).eventually
        (hA'.mono fun (q : S × ℝ≥0) hq => (⟨hq.2.1, hq.2.2⟩ :
          (F (Susp.mk q)).dir ∈ e'.source ∧ e' (F (Susp.mk q)).dir = A • e q.1))
    have ha' := hev.self_of_nhds
    filter_upwards [mem_nhdsWithin_of_mem_nhds hev] with b hb
    have heq : (F (Susp.mk (σ, a))).dir = (F (Susp.mk (σ, b))).dir :=
      e'.injOn ha'.1 hb.1 (ha'.2.trans hb.2.symm)
    exact ⟨heq, heq.symm⟩
  -- (E3) the slice map `f`, at radius `ε/2`; every slice is `f`
  have hε2 : ε / 2 ∈ Ioo (0 : ℝ≥0) ε := ⟨half_pos hε, half_lt_self hε.ne'⟩
  set f : S → S := fun σ => (F (Susp.mk (σ, ε / 2))).dir with hfdef
  have hslice_c : ∀ s ∈ Ioo (0 : ℝ≥0) ε, Continuous fun σ : S => (F (Susp.mk (σ, s))).dir := by
    intro s hs
    refine continuous_iff_continuousAt.2 fun σ => ?_
    have h1 : (Susp.mk (σ, s) : Susp S) ∈ (Susp.ball ε : Set (Susp S)) := hs.2
    have hrpos : 0 < (F (Susp.mk (σ, s))).r := by rw [hr _ h1]; exact hs.1
    have h2 : ContinuousAt (fun σ : S => F (Susp.mk (σ, s))) σ :=
      ContinuousAt.comp (g := F) (f := fun σ : S => (Susp.mk (σ, s) : Susp S)) (hFc _ (hball h1))
        (Susp.continuous_mk_left s).continuousAt
    exact ContinuousAt.comp (g := Susp.dir) (f := fun σ : S => F (Susp.mk (σ, s)))
      (Susp.continuousAt_dir hrpos) h2
  have hslice : ∀ s ∈ Ioo (0 : ℝ≥0) ε, (fun σ : S => (F (Susp.mk (σ, s))).dir) = f := by
    intro s hs
    refine Continuous.ext_on (isPortly_reg (SpecialOrth W) (RaySphere W) S).dense
      (hslice_c s hs) (hslice_c _ hε2) fun σ hσ => hdirc σ hσ s hs _ hε2
  have hfc : Continuous f := hslice_c _ hε2
  have hFmap : ∀ z ∈ (Susp.ball ε : Set (Susp S)), F z = Susp.map f z := by
    intro z hz
    obtain ⟨⟨σ, s⟩, rfl⟩ := Susp.mk_surjective z
    have hsε : s < ε := hz
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with h0 | hs
    · subst h0
      have h1 : (Susp.mk (σ, 0) : Susp S) = O := Susp.eq_of_mem_O rfl hO
      rw [Susp.map_mk, h1]
      exact Susp.eq_of_mem_O hFO rfl
    · rw [Susp.map_mk, ← Susp.mk_dir_r (F (Susp.mk (σ, s))), hr _ hz]
      have := congrFun (hslice s ⟨hs, hsε⟩) σ
      rw [show (F (Susp.mk (σ, s))).dir = f σ from this]
      rfl
  refine ⟨ε, hε, hball, f, hfc, hFmap, fun σ hσ => ⟨(hDreg σ hσ _ hε2.1 hε2.2).2,
    fun e he hσe e' he' hfe' => ?_⟩⟩
  obtain ⟨A, hA'⟩ := hD σ hσ _ hε2.1 hε2.2 e he hσe e' he' hfe'
  refine ⟨A, ?_⟩
  have := ((continuous_id.prodMk continuous_const).tendsto σ).eventually
    (hA'.mono fun q hq => hq.2.2)
  exact this

end Radial

/-! ### The facts at the centre: rigidity and the local rotations -/

section Facts

variable {M : Type} [TopologicalSpace M] [SingularGXStructure SO3 Sph2 M]

/-- An automorphism of `susp(Σ)`, as an isomorphism of the open set `⊤` onto itself. -/
def topOpensHomeomorph {N : Type*} [TopologicalSpace N] (ψ : N ≃ₜ N) :
    (⊤ : Opens N) ≃ₜ (⊤ : Opens N) where
  toFun x := ⟨ψ x, trivial⟩
  invFun x := ⟨ψ.symm x, trivial⟩
  left_inv x := Subtype.ext (ψ.symm_apply_apply x)
  right_inv x := Subtype.ext (ψ.apply_symm_apply x)
  continuous_toFun := (ψ.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (ψ.symm.continuous.comp continuous_subtype_val).subtype_mk _

/-- **(i) A local isomorphism at the centre fixes the centre** (`RamcovGX.tex:1933`: "an
automorphism of `M` has to fix `O` since singular locus is homeomorphic to a line except at `O`"):
for a cone sphere with at least three cone points of angle `≠ 2π` (Troyanov's condition gives
them), every a.e. isomorphism `φ : U₁ → U₂` of open subsets of `susp(Σ)` with `O ∈ U₁` sends `O` to
`O`: near `O` the singular locus is a star of `≥ 3` arcs, near any other singular point an arc. -/
theorem IsConeSphere.thurston_fixes_centre {s : ℕ} {θ : Fin s → ℝ} {p : Fin s → M}
    (h : IsConeSphere M θ p) (hθ : 3 ≤ (Finset.univ.filter fun i => θ i ≠ 2 * π).card) :
    haveI := h.connectedSpace
    haveI := h.locallyConnectedSpace
    letI := thurstonSuspension (M := M)
    ∀ O ∈ (Susp.O : Set (Susp M)), ∀ (U₁ U₂ : Opens (Susp M)) (φ : U₁ ≃ₜ U₂),
      IsAEMorphism SO4 Sph3 (φ : U₁ → U₂) → ∀ hO : O ∈ U₁,
        (φ ⟨O, hO⟩ : Susp M) ∈ (Susp.O : Set (Susp M)) := by
  haveI := h.connectedSpace
  haveI := h.locallyConnectedSpace
  haveI := h.t2Space
  letI := thurstonSuspension (M := M)
  intro O hO U₁ U₂ φ hφ hOU
  by_contra hne
  set o : U₁ := ⟨O, hOU⟩ with hodef
  have hsing := h.thurston_sing_eq hθ
  set J : Set (Fin s) := {i | θ i ≠ 2 * π} with hJ
  have hpre := (hφ.preimage_reg_sing φ.isLocalHomeomorph).2
  have hS1 : ∀ x : U₁, (φ x : Susp M) ∈ Sing SO4 Sph3 (Susp M) ↔
      (x : Susp M) ∈ Sing SO4 Sph3 (Susp M) := by
    intro x
    have h1 : (φ x : U₂) ∈ Sing SO4 Sph3 U₂ ↔ (φ x : Susp M) ∈ Sing SO4 Sph3 (Susp M) := by
      rw [sing_opensSingular U₂]; rfl
    have h2 : x ∈ Sing SO4 Sph3 U₁ ↔ (x : Susp M) ∈ Sing SO4 Sph3 (Susp M) := by
      rw [sing_opensSingular U₁]; rfl
    rw [← h1, ← h2, ← hpre]; rfl
  have hOs : O ∈ Sing SO4 Sph3 (Susp M) := by rw [hsing]; exact Or.inl hO
  have hy : (φ o : Susp M) ∈ Sing SO4 Sph3 (Susp M) := (hS1 o).2 hOs
  have hy' := hy
  rw [hsing] at hy'
  rcases hy' with hyO | ⟨⟨σ, t₀⟩, ⟨⟨j, hj, rfl⟩, ht₀⟩, hyeq⟩
  · exact hne hyO
  -- a box `B × I` around `(p j, t₀)` inside `U₂`, `B` avoiding the other cone points
  have hU₂ : Susp.mk ⁻¹' (U₂ : Set (Susp M)) ∈ 𝓝 (p j, t₀) := by
    refine (U₂.isOpen.preimage Susp.continuous_mk).mem_nhds ?_
    show Susp.mk (p j, t₀) ∈ U₂
    rw [hyeq]; exact (φ o).2
  obtain ⟨B', l, u, hB'o, -, hpjB', htI, hsub, hpos⟩ := Susp.exists_box ht₀ hU₂
  set B : Set M := B' ∩ (p '' (J \ {j}))ᶜ with hBdef
  have hBo : IsOpen B := hB'o.inter (Set.toFinite _).isClosed.isOpen_compl
  have hpjB : p j ∈ B := ⟨hpjB', fun ⟨k, hk, hkj⟩ => hk.2 (h.injective hkj)⟩
  set I : Set ℝ≥0 := Ioo l u with hIdef
  set V : Set (Susp M) := Susp.mk '' (B ×ˢ I) with hVdef
  have hVo : IsOpen V :=
    Susp.isOpen_image_mk (hBo.prod isOpen_Ioo) fun q hq => hpos ⟨hq.1.1, hq.2⟩
  have hVU : V ⊆ U₂ := by rintro _ ⟨q, hq, rfl⟩; exact hsub ⟨hq.1.1, hq.2⟩
  have hyV : (φ o : Susp M) ∈ V := by rw [← hyeq]; exact ⟨(p j, t₀), ⟨hpjB, htI⟩, rfl⟩
  -- the singular points of `V` are on the ray over `p j`
  have hSV : ∀ w ∈ Sing SO4 Sph3 (Susp M), w ∈ V → ∃ a ∈ I, w = Susp.mk (p j, a) := by
    rintro w hw ⟨⟨b, a⟩, ⟨hb, ha⟩, rfl⟩
    have ha0 : 0 < a := hpos ⟨hb.1, ha⟩
    rw [hsing] at hw
    rcases hw with hw | ⟨⟨σ', u'⟩, ⟨⟨k, hk, rfl⟩, hu'⟩, hkeq⟩
    · exact absurd (show a = 0 from hw) ha0.ne'
    · obtain ⟨h1, -⟩ := Prod.ext_iff.1 (Susp.eq_of_mk_eq_of_pos hkeq hu')
      simp only at h1
      have hkj : k = j := by
        by_contra hkj
        exact hb.2 ⟨k, ⟨hk, hkj⟩, h1⟩
      refine ⟨a, ha, ?_⟩
      rw [← h1, hkj]
  -- the preimage of `V`, an open neighbourhood of `O`, contains a ball
  set Ω : Set (Susp M) := Subtype.val '' {x : U₁ | (φ x : Susp M) ∈ V} with hΩdef
  have hΩo : IsOpen Ω := U₁.isOpen.isOpenMap_subtype_val _
    ((hVo.preimage continuous_subtype_val).preimage φ.continuous)
  have hOΩ : O ∈ Ω := ⟨o, hyV, rfl⟩
  obtain ⟨ε, hε, hball⟩ := Susp.exists_ball_subset_of_isOpen hΩo hO hOΩ
  -- each singular ray meets the ball at radius `ε/2`, at a point sent to the ray over `p j`
  have hpt : ∀ k ∈ J, ∃ x : U₁, (x : Susp M) = Susp.mk (p k, ε / 2) ∧
      ∃ a ∈ I, a ≠ t₀ ∧ (φ x : Susp M) = Susp.mk (p j, a) := by
    intro k hk
    have hmem : Susp.mk (p k, ε / 2) ∈ (Susp.ball ε : Set (Susp M)) :=
      show ε / 2 < ε from half_lt_self hε.ne'
    obtain ⟨x, hxV, hx⟩ := hball hmem
    have hxs : (x : Susp M) ∈ Sing SO4 Sph3 (Susp M) := by
      rw [hx, hsing]; exact Or.inr ⟨(p k, ε / 2), ⟨⟨k, hk, rfl⟩, half_pos hε⟩, rfl⟩
    obtain ⟨a, ha, hax⟩ := hSV _ ((hS1 x).2 hxs) hxV
    refine ⟨x, hx, a, ha, fun hat => ?_, hax⟩
    have hxo : φ x = φ o := Subtype.ext (by rw [hax, hat, hyeq])
    have hr : (x : Susp M).r = 0 := by rw [φ.injective hxo]; exact hO
    rw [hx] at hr
    exact (half_pos hε).ne' hr
  -- two points of the ball sent to the same side of `φ(O)` on the ray lie on the same ray
  have key : ∀ (x x' : U₁) (a a' : ℝ≥0), (φ x : Susp M) = Susp.mk (p j, a) →
      (φ x' : Susp M) = Susp.mk (p j, a') → a ∈ I → a' ∈ I → a ≠ t₀ → a' ≠ t₀ →
      (a < t₀ ↔ a' < t₀) → (x : Susp M).dir = (x' : Susp M).dir := by
    intro x x' a a' hxa hxa' ha ha' hat hat' hside
    set C : Set (Susp M) := Susp.mk '' ({p j} ×ˢ Icc (min a a') (max a a')) with hCdef
    have hIcc : Icc (min a a') (max a a') ⊆ I := fun r hr =>
      ⟨lt_of_lt_of_le (lt_min ha.1 ha'.1) hr.1, lt_of_le_of_lt hr.2 (max_lt ha.2 ha'.2)⟩
    have hCV : C ⊆ V := by
      rintro _ ⟨q, ⟨hq1, hq2⟩, rfl⟩
      exact ⟨q, ⟨by rw [mem_singleton_iff.1 hq1]; exact hpjB, hIcc hq2⟩, rfl⟩
    have hCs : C ⊆ Sing SO4 Sph3 (Susp M) := by
      rintro _ ⟨q, ⟨hq1, hq2⟩, rfl⟩
      rw [hsing]
      refine Or.inr ⟨q, ⟨⟨j, hj, (mem_singleton_iff.1 hq1).symm⟩, hpos ⟨?_, hIcc hq2⟩⟩, rfl⟩
      rw [mem_singleton_iff.1 hq1]; exact hpjB'
    have hyC : (φ o : Susp M) ∉ C := by
      rintro ⟨q, ⟨hq1, hq2⟩, hq⟩
      rw [← hyeq] at hq
      have hq0 : 0 < q.2 := hpos ⟨by rw [mem_singleton_iff.1 hq1]; exact hpjB', hIcc hq2⟩
      have := (Prod.ext_iff.1 (Susp.eq_of_mk_eq_of_pos hq hq0)).2
      simp only at this
      rw [this] at hq2
      rcases lt_or_gt_of_ne hat with h1 | h1
      · exact absurd hq2.2 (not_le.2 (max_lt h1 (hside.1 h1)))
      · have h2 : t₀ < a' := lt_of_le_of_ne (not_lt.1 fun h' => absurd (hside.2 h')
          (not_lt.2 h1.le)) (Ne.symm hat')
        exact absurd hq2.1 (not_le.2 (lt_min h1 h2))
    have hCc : IsPreconnected C :=
      (isPreconnected_singleton.prod isPreconnected_Icc).image _ Susp.continuous_mk.continuousOn
    set C' : Set U₂ := Subtype.val ⁻¹' C with hC'def
    have hC'c : IsPreconnected C' := by
      rw [← IsInducing.subtypeVal.isPreconnected_image]
      convert hCc using 1
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩; exact hw
      · intro hz; exact ⟨⟨z, hVU (hCV hz)⟩, hz, rfl⟩
    set E : Set (Susp M) := Subtype.val '' (φ.symm '' C') with hEdef
    have hEc : IsPreconnected E :=
      (hC'c.image _ φ.symm.continuous.continuousOn).image _ continuous_subtype_val.continuousOn
    have hEpos : ∀ e ∈ E, 0 < e.r ∧ e.dir ∈ p '' J := by
      rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      have hws : (φ.symm w : Susp M) ∈ Sing SO4 Sph3 (Susp M) := by
        have := (hS1 (φ.symm w)).1
        rw [φ.apply_symm_apply] at this
        exact this (hCs hw)
      have hwo : (φ.symm w : Susp M) ∉ (Susp.O : Set (Susp M)) := by
        intro hO'
        have : φ.symm w = o := Subtype.ext (Susp.eq_of_mem_O hO' hO)
        apply hyC
        rw [← this, φ.apply_symm_apply]; exact hw
      rw [hsing] at hws
      rcases hws with hws | ⟨⟨σ', u'⟩, ⟨⟨k, hk, rfl⟩, hu'⟩, hkeq⟩
      · exact absurd hws hwo
      · rw [← hkeq, Susp.dir_mk_of_pos hu']; exact ⟨hu', k, hk, rfl⟩
    have hdirc : ContinuousOn Susp.dir E := fun e he =>
      (Susp.continuousAt_dir (hEpos e he).1).continuousWithinAt
    have hsub' := IsPreconnected.subsingleton_of_subset_finite (hEc.image _ hdirc)
      ((Set.toFinite J).image p) (by rintro _ ⟨e, he, rfl⟩; exact (hEpos e he).2)
    have hxE : (x : Susp M) ∈ E := ⟨x, ⟨φ x, by
      show (φ x : Susp M) ∈ C
      rw [hxa]; exact ⟨(p j, a), ⟨rfl, min_le_left _ _, le_max_left _ _⟩, rfl⟩,
      φ.symm_apply_apply x⟩, rfl⟩
    have hx'E : (x' : Susp M) ∈ E := ⟨x', ⟨φ x', by
      show (φ x' : Susp M) ∈ C
      rw [hxa']; exact ⟨(p j, a'), ⟨rfl, min_le_right _ _, le_max_right _ _⟩, rfl⟩,
      φ.symm_apply_apply x'⟩, rfl⟩
    exact hsub' ⟨_, hxE, rfl⟩ ⟨_, hx'E, rfl⟩
  -- three singular rays, two of whose points go to the same side: a contradiction
  have hcard := hθ
  obtain ⟨k₁, k₂, k₃, hk₁, hk₂, hk₃, h12, h13, h23⟩ := Finset.two_lt_card_iff.1
    (by omega : 2 < (Finset.univ.filter fun i => θ i ≠ 2 * π).card)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk₁ hk₂ hk₃
  have hpair : ∀ {k k' : Fin s} {x x' : U₁} {a a' : ℝ≥0},
      (x : Susp M) = Susp.mk (p k, ε / 2) → (x' : Susp M) = Susp.mk (p k', ε / 2) →
      (φ x : Susp M) = Susp.mk (p j, a) → (φ x' : Susp M) = Susp.mk (p j, a') → a ∈ I →
      a' ∈ I → a ≠ t₀ → a' ≠ t₀ → (a < t₀ ↔ a' < t₀) → k = k' := by
    intro k k' x x' a a' hx hx' hxa hxa' ha ha' hat hat' hside
    have := key x x' a a' hxa hxa' ha ha' hat hat' hside
    rw [hx, hx', Susp.dir_mk_of_pos (half_pos hε), Susp.dir_mk_of_pos (half_pos hε)] at this
    exact h.injective this
  obtain ⟨x₁, hx₁, a₁, ha₁, hat₁, hφ₁⟩ := hpt k₁ hk₁
  obtain ⟨x₂, hx₂, a₂, ha₂, hat₂, hφ₂⟩ := hpt k₂ hk₂
  obtain ⟨x₃, hx₃, a₃, ha₃, hat₃, hφ₃⟩ := hpt k₃ hk₃
  have htri : (a₁ < t₀ ↔ a₂ < t₀) ∨ (a₁ < t₀ ↔ a₃ < t₀) ∨ (a₂ < t₀ ↔ a₃ < t₀) := by tauto
  rcases htri with h' | h' | h'
  · exact h12 (hpair hx₁ hx₂ hφ₁ hφ₂ ha₁ ha₂ hat₁ hat₂ h')
  · exact h13 (hpair hx₁ hx₃ hφ₁ hφ₃ ha₁ ha₃ hat₁ hat₃ h')
  · exact h23 (hpair hx₂ hx₃ hφ₂ hφ₃ ha₂ ha₃ hat₂ hat₃ h')

/-- **(ii) Near the centre, a local isomorphism fixing it is the suspension of an automorphism of
`Σ`** (`RamcovGX.tex:1933`: "furthermore it preserves distances and geodesics. By considering the
sphere of some radius `ε > 0` centered at `O` we see that the natural map `Aut(Σ) → Aut(M)` is a
group isomorphism … These remarks hold for all neighborhoods of `O`"): if an a.e. isomorphism
`φ : U₁ → U₂` of open subsets of `susp(Σ)` fixes `O ∈ U₁`, then on some ball `{r < ε}` it is
`susp(f)` for an automorphism `f` of `Σ`. -/
theorem IsConeSphere.thurston_eq_susp_near_centre {s : ℕ} {θ : Fin s → ℝ} {p : Fin s → M}
    (h : IsConeSphere M θ p) :
    haveI := h.connectedSpace
    haveI := h.locallyConnectedSpace
    letI := thurstonSuspension (M := M)
    ∀ O ∈ (Susp.O : Set (Susp M)), ∀ (U₁ U₂ : Opens (Susp M)) (φ : U₁ ≃ₜ U₂),
      IsAEMorphism SO4 Sph3 (φ : U₁ → U₂) → ∀ hO : O ∈ U₁,
        (φ ⟨O, hO⟩ : Susp M) ∈ (Susp.O : Set (Susp M)) →
          ∃ ε : ℝ≥0, 0 < ε ∧ ∃ f ∈ singularAut SO3 Sph2 M, ∀ x : U₁, (x : Susp M).r < ε →
            (φ x : Susp M) = Susp.map f x := by
  haveI := h.connectedSpace
  haveI := h.locallyConnectedSpace
  haveI := h.t2Space
  letI := thurstonSuspension (M := M)
  intro O hO U₁ U₂ φ hφ hOU hfix
  have hφO : (φ ⟨O, hOU⟩ : Susp M) = O := Susp.eq_of_mem_O hfix hO
  have hOU₂ : O ∈ U₂ := hφO ▸ (φ ⟨O, hOU⟩).2
  have hφ' : IsAEMorphism SO4 Sph3 (φ.symm : U₂ → U₁) := IsAEMorphism.symm_of_homeomorph hφ
  have hfix' : (φ.symm ⟨O, hOU₂⟩ : Susp M) ∈ (Susp.O : Set (Susp M)) := by
    have : (⟨O, hOU₂⟩ : U₂) = φ ⟨O, hOU⟩ := Subtype.ext hφO.symm
    rw [this, φ.symm_apply_apply]; exact hO
  obtain ⟨ε, hε, hb, f, hfc, hFf, hfreg⟩ :=
    thurston_eq_map_near_centre (σ₀ := sph2Base) hφ hO hOU hfix
  obtain ⟨ε', hε', hb', f', hf'c, hFf', -⟩ :=
    thurston_eq_map_near_centre (σ₀ := sph2Base) hφ' hO hOU₂ hfix'
  set δ : ℝ≥0 := min ε ε' / 2 with hδdef
  have hδ : 0 < δ := half_pos (lt_min hε hε')
  have hδε : δ < ε := (half_lt_self (lt_min hε hε').ne').trans_le (min_le_left _ _)
  have hδε' : δ < ε' := (half_lt_self (lt_min hε hε').ne').trans_le (min_le_right _ _)
  have hleft : ∀ σ, f' (f σ) = σ := by
    intro σ
    have hz : (Susp.mk (σ, δ) : Susp M) ∈ (Susp.ball ε : Set (Susp M)) := hδε
    have hz' : (Susp.mk (f σ, δ) : Susp M) ∈ (Susp.ball ε' : Set (Susp M)) := hδε'
    have h3 : (opensOPH φ.symm : Susp M → Susp M) ((opensOPH φ : Susp M → Susp M)
        (Susp.mk (σ, δ))) = Susp.mk (σ, δ) := by
      rw [opensOPH_apply φ (hb hz), opensOPH_apply φ.symm (φ ⟨_, hb hz⟩).2]
      simp
    rw [hFf _ hz, Susp.map_mk, hFf' _ hz', Susp.map_mk] at h3
    exact (Prod.ext_iff.1 (Susp.eq_of_mk_eq_of_pos h3 hδ)).1
  have hright : ∀ τ, f (f' τ) = τ := by
    intro τ
    have hz : (Susp.mk (τ, δ) : Susp M) ∈ (Susp.ball ε' : Set (Susp M)) := hδε'
    have hz' : (Susp.mk (f' τ, δ) : Susp M) ∈ (Susp.ball ε : Set (Susp M)) := hδε
    have h3 : (opensOPH φ : Susp M → Susp M) ((opensOPH φ.symm : Susp M → Susp M)
        (Susp.mk (τ, δ))) = Susp.mk (τ, δ) := by
      rw [opensOPH_apply φ.symm (hb' hz), opensOPH_apply φ (φ.symm ⟨_, hb' hz⟩).2]
      simp
    rw [hFf' _ hz, Susp.map_mk, hFf _ hz', Susp.map_mk] at h3
    exact (Prod.ext_iff.1 (Susp.eq_of_mk_eq_of_pos h3 hδ)).1
  set fh : M ≃ₜ M :=
    { toFun := f
      invFun := f'
      left_inv := hleft
      right_inv := hright
      continuous_toFun := hfc
      continuous_invFun := hf'c } with hfhdef
  have hfh : IsAEMorphism SO3 Sph2 (fh : M → M) := by
    have hB := isMaximalAEAtlas_aeAtlas SO3 Sph2 M
    refine (isAEMorphismOf_iff hB.1).2 ⟨hfc, Reg SO3 Sph2 M, isPortly_reg SO3 Sph2 M,
      IsRegularOn.of_exists hB.1.1 hB.1.1 (isOpen_reg SO3 Sph2 M) subset_rfl
        (fun σ hσ => (hfreg σ hσ).1) hfc.continuousOn fun σ hσ => ?_⟩
    obtain ⟨e, he, hσe⟩ := mem_support.1 hσ
    obtain ⟨e', he', hfe'⟩ := mem_support.1 (hfreg σ hσ).1
    obtain ⟨A, hA⟩ := (hfreg σ hσ).2 e he hσe e' he' hfe'
    exact ⟨e, he, e', he', hσe, hfe', A, hA⟩
  refine ⟨ε, hε, fh, hfh, fun x hx => ?_⟩
  have h1 := hFf x hx
  rw [opensOPH_apply φ x.2] at h1
  exact h1

/-- **(iii) `Aut(Σ) = {Id}` when the angles are pairwise distinct** (implicit at
`RamcovGX.tex:1933`: "As a consequence, except for very particular `Σ`, `Aut(M)` is trivial. For
instance, if all the `θ_i` are different then `Aut(M)={Id}`", which, through `Aut(Σ) ≅ Aut(M)`
(`IsConeSphere.thurstonSuspAut_bijective`), is the claim that `Aut(Σ)` is trivial): a cone sphere
with at least three cone points of angle `≠ 2π` and pairwise distinct angles has no automorphism
but the identity. The paper gives no argument. It is the only `sorry` of this file, and the
obligation is equivalent to it (`thurstonSuspensionFacts_iff`). -/
theorem IsConeSphere.singularAut_eq_bot {s : ℕ} {θ : Fin s → ℝ} {p : Fin s → M}
    (h : IsConeSphere M θ p) (hθ : 3 ≤ (Finset.univ.filter fun i => θ i ≠ 2 * π).card)
    (hd : Pairwise fun i j => θ i ≠ θ j) :
    haveI := h.locallyConnectedSpace
    singularAut SO3 Sph2 M = ⊥ := by
  sorry -- SORRY(cex:start_singular_manifold_homeomorphic): `Aut(Σ) = {Id}` for a cone sphere
  -- with `≥ 3` cone points of angle `≠ 2π` and pairwise distinct angles. An automorphism `f`
  -- preserves the cone angle (`IsConePoint.angle_eq`), so fixes these `≥ 3` cone points; it is an
  -- orientation-preserving isometry of the cone metric. The missing step is a fixed-point theorem
  -- for `𝕊²`: a non-identity orientation-preserving isometry of a compact cone sphere has finite
  -- order (its isometry group is compact and, fixing `≥ 3` points, has no circle subgroup), and a
  -- non-identity orientation-preserving periodic homeomorphism of `𝕊²` has exactly two fixed
  -- points (Brouwer–Kerékjártó; or Lefschetz–Hopf, every fixed point of index `+1` and
  -- `L(f) = 2`). None of these (Lefschetz, Kerékjártó, the metric of a cone surface) is at this
  -- mathlib pin or in the library.

/-- **Rigidity at the centre** (`RamcovGX.tex:1933–1935`: "an automorphism of `M` has to fix `O`
… the natural map `Aut(Σ) → Aut(M)` is a group isomorphism … if all the `θ_i` are different then
`Aut(M) = {Id}`. These remarks hold for all neighborhoods of `O`"): for a cone sphere with at
least three cone points of angle `≠ 2π`, every a.e. isomorphism `φ : U₁ → U₂` of
connected open subsets of `susp(Σ)` with `O ∈ U₁` is the identity on `U₁`
(`SuspensionCexFacts.rigid`), as soon as `Aut(Σ) = {Id}` (which is (iii),
`IsConeSphere.singularAut_eq_bot`, for pairwise distinct angles). The paper's argument, step by
step: `φ` fixes `O` (i), is `susp(f)` near `O` (ii) with `f ∈ Aut(Σ) = {Id}`, so `φ` is the
identity near `O`, hence on the connected `U₁` (`IsAEMorphism.eq_of_eqOn`,
`rem:morphisms_analytical_two_equal`). -/
theorem IsConeSphere.thurston_rigid {s : ℕ} {θ : Fin s → ℝ} {p : Fin s → M}
    (h : IsConeSphere M θ p) (hθ : 3 ≤ (Finset.univ.filter fun i => θ i ≠ 2 * π).card)
    (hAut : haveI := h.locallyConnectedSpace; singularAut SO3 Sph2 M = ⊥) :
    haveI := h.connectedSpace
    haveI := h.locallyConnectedSpace
    letI := thurstonSuspension (M := M)
    ∀ O ∈ (Susp.O : Set (Susp M)), ∀ (U₁ U₂ : Opens (Susp M)), IsConnected (U₁ : Set (Susp M)) →
      IsConnected (U₂ : Set (Susp M)) → ∀ φ : U₁ ≃ₜ U₂, IsAEMorphism SO4 Sph3 (φ : U₁ → U₂) →
        O ∈ U₁ → ∀ x : U₁, (φ x : Susp M) = x := by
  haveI := h.connectedSpace
  haveI := h.locallyConnectedSpace
  haveI := h.t2Space
  letI := thurstonSuspension (M := M)
  intro O hO U₁ U₂ hU₁ _ φ hφ hOU
  have hfix := h.thurston_fixes_centre hθ O hO U₁ U₂ φ hφ hOU
  obtain ⟨ε, hε, f, hf, hφf⟩ := h.thurston_eq_susp_near_centre O hO U₁ U₂ φ hφ hOU hfix
  have hf1 : f = 1 := by
    have : singularAut SO3 Sph2 M = ⊥ := hAut
    rw [Subgroup.eq_bot_iff_forall] at this
    exact this f hf
  haveI : PreconnectedSpace U₁ := (isConnected_iff_connectedSpace.1 hU₁).toPreconnectedSpace
  have h1 : IsAEMorphism SO4 Sph3 ((Subtype.val : U₂ → Susp M) ∘ (φ : U₁ → U₂)) :=
    (isAEMorphism_opensSingular_val U₂).comp hφ
  have h2 : IsAEMorphism SO4 Sph3 (Subtype.val : U₁ → Susp M) := isAEMorphism_opensSingular_val U₁
  have hWo : IsOpen {x : U₁ | (x : Susp M).r < ε} :=
    (Susp.isOpen_ball ε).preimage continuous_subtype_val
  have heq := IsAEMorphism.eq_of_eqOn h1 h2 hWo ⟨⟨O, hOU⟩, show (O : Susp M).r < ε by
    rw [show (O : Susp M).r = 0 from hO]; exact hε⟩ fun x hx => by
      show (φ x : Susp M) = x
      rw [hφf x hx, hf1]
      obtain ⟨q, hq⟩ := Susp.mk_surjective (x : Susp M)
      rw [← hq]; rfl
  exact fun x => congrFun heq x

/-- **`Aut(Σ) → Aut(susp Σ)` is a group isomorphism** (`RamcovGX.tex:1933`; DEC-175 (c)), for a
cone sphere with at least three cone points of angle `≠ 2π` (distinct angles or not): injective (`thurstonSuspAut_injective`), and onto since an
automorphism `ψ` of `susp(Σ)` fixes `O` (i), is `susp(f)` near `O` (ii), hence everywhere
(`IsAEMorphism.eq_of_eqOn` on the connected `susp(Σ)`). -/
theorem IsConeSphere.thurstonSuspAut_bijective {s : ℕ} {θ : Fin s → ℝ} {p : Fin s → M}
    (h : IsConeSphere M θ p) (hθ : 3 ≤ (Finset.univ.filter fun i => θ i ≠ 2 * π).card) :
    haveI := h.connectedSpace
    haveI := h.locallyConnectedSpace
    Bijective (thurstonSuspAut sph2Base M) := by
  haveI := h.connectedSpace
  haveI := h.locallyConnectedSpace
  haveI := h.t2Space
  letI := thurstonSuspension (M := M)
  refine ⟨thurstonSuspAut_injective, fun ψ => ?_⟩
  haveI : ConnectedSpace (Susp M) := Susp.connectedSpace
  set O : Susp M := Susp.mk (p ⟨0, pos_of_three_le_card_ne_two_pi hθ⟩, 0)
  have hO : O ∈ (Susp.O : Set (Susp M)) := rfl
  have hφ : IsAEMorphism SO4 Sph3
      (topOpensHomeomorph (ψ : Susp M ≃ₜ Susp M) :
        (⊤ : Opens (Susp M)) → (⊤ : Opens (Susp M))) := by
    refine isAEMorphism_of_val_comp ⊤ ?_
    exact ψ.2.comp (isAEMorphism_opensSingular_val (G := SO4) (X := Sph3) (⊤ : Opens (Susp M)))
  have hfix := h.thurston_fixes_centre hθ O hO ⊤ ⊤ (topOpensHomeomorph (ψ : Susp M ≃ₜ Susp M)) hφ
    trivial
  obtain ⟨ε, hε, f, hf, hψf⟩ := h.thurston_eq_susp_near_centre O hO ⊤ ⊤
    (topOpensHomeomorph (ψ : Susp M ≃ₜ Susp M)) hφ trivial hfix
  refine ⟨⟨f, hf⟩, Subtype.ext ?_⟩
  have h1 : IsAEMorphism SO4 Sph3 (Susp.homeomorph f : Susp M → Susp M) :=
    thurston_isAEMorphism_suspHomeomorph (σ₀ := sph2Base) hf
  have heq := IsAEMorphism.eq_of_eqOn h1 ψ.2 (Susp.isOpen_ball ε)
    ⟨O, show (O : Susp M).r < ε by rw [show (O : Susp M).r = 0 from hO]; exact hε⟩
    fun x hx => (hψf ⟨x, trivial⟩ hx).symm
  exact Homeomorph.ext fun x => congrFun heq x

/-- **The group isomorphism `Aut(Σ) ≅ Aut(susp Σ)`** (`RamcovGX.tex:1933`; DEC-175 (c)),
`f ↦ susp(f)`, for a cone sphere with at least three cone points of angle `≠ 2π`. -/
noncomputable def IsConeSphere.thurstonSuspAutEquiv {s : ℕ} {θ : Fin s → ℝ} {p : Fin s → M}
    (h : IsConeSphere M θ p) (hθ : 3 ≤ (Finset.univ.filter fun i => θ i ≠ 2 * π).card) :
    haveI := h.connectedSpace
    haveI := h.locallyConnectedSpace
    letI := thurstonSuspension (M := M)
    singularAut SO3 Sph2 M ≃* singularAut SO4 Sph3 (Susp M) :=
  haveI := h.connectedSpace
  haveI := h.locallyConnectedSpace
  MulEquiv.ofBijective (thurstonSuspAut sph2Base M) (h.thurstonSuspAut_bijective hθ)

/-- **Rigidity at a point kills the automorphisms**: if every a.e. isomorphism of connected open
subsets whose domain contains `O` is the identity, then `Aut(N) = {Id}` (`U₁ = U₂ = N`). -/
theorem singularAut_eq_bot_of_rigid {G : Type*} {X : Type*} [TopologicalSpace X] [Group G]
    [MulAction G X] [ContinuousConstSMul G X] [LocallyConnectedSpace X] [T2Space X]
    [IsRigidAction G X] {N : Type*} [TopologicalSpace N] [ConnectedSpace N]
    [LocallyConnectedSpace N] [SingularGXStructure G X N] {O : N}
    (hrigid : ∀ (U₁ U₂ : Opens N), IsConnected (U₁ : Set N) → IsConnected (U₂ : Set N) →
      ∀ φ : U₁ ≃ₜ U₂, IsAEMorphism G X (φ : U₁ → U₂) → O ∈ U₁ → ∀ x : U₁, (φ x : N) = x) :
    singularAut G X N = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun ψ hψ => Homeomorph.ext fun z => ?_
  have hφ : IsAEMorphism G X
      (topOpensHomeomorph ψ : (⊤ : Opens N) → (⊤ : Opens N)) := by
    refine isAEMorphism_of_val_comp ⊤ ?_
    exact hψ.comp (isAEMorphism_opensSingular_val (G := G) (X := X) (⊤ : Opens N))
  have hc : IsConnected ((⊤ : Opens N) : Set N) := by
    rw [Opens.coe_top]; exact isConnected_univ
  exact hrigid ⊤ ⊤ hc hc (topOpensHomeomorph ψ) hφ trivial ⟨z, trivial⟩

/-- **`Aut(M) = {Id}`** (`RamcovGX.tex:1933`, "if all the `θ_i` are different then
`Aut(M) = {Id}`"), from rigidity at the centre, as soon as `Aut(Σ) = {Id}`. -/
theorem IsConeSphere.thurston_singularAut_eq_bot {s : ℕ} {θ : Fin s → ℝ} {p : Fin s → M}
    (h : IsConeSphere M θ p) (hθ : 3 ≤ (Finset.univ.filter fun i => θ i ≠ 2 * π).card)
    (hAut : haveI := h.locallyConnectedSpace; singularAut SO3 Sph2 M = ⊥) :
    haveI := h.connectedSpace
    haveI := h.locallyConnectedSpace
    letI := thurstonSuspension (M := M)
    singularAut SO4 Sph3 (Susp M) = ⊥ := by
  haveI := h.connectedSpace
  haveI := h.locallyConnectedSpace
  letI := thurstonSuspension (M := M)
  haveI : ConnectedSpace (Susp M) := Susp.connectedSpace
  exact singularAut_eq_bot_of_rigid
    (h.thurston_rigid hθ hAut (Susp.mk (p ⟨0, pos_of_three_le_card_ne_two_pi hθ⟩, 0)) rfl)

/-- **A local isomorphism around each singular ray which is not the identity**
(`RamcovGX.tex:1935`, "locally we may construct a rotation around any of the axes"): every
singular point `y ≠ O` of `susp(Σ)` lies in the domain of an a.e. isomorphism of connected open
sets which moves some point. -/
theorem IsConeSphere.thurston_exists_local_ne_id {s : ℕ} {θ : Fin s → ℝ} {p : Fin s → M}
    (h : IsConeSphere M θ p) (hθ : 3 ≤ (Finset.univ.filter fun i => θ i ≠ 2 * π).card) :
    haveI := h.connectedSpace
    haveI := h.locallyConnectedSpace
    letI := thurstonSuspension (M := M)
    ∀ y ∈ Sing SO4 Sph3 (Susp M), y ∉ (Susp.O : Set (Susp M)) →
      ∃ (U₁ U₂ : Opens (Susp M)), IsConnected (U₁ : Set (Susp M)) ∧
        IsConnected (U₂ : Set (Susp M)) ∧ y ∈ U₁ ∧ ∃ φ : U₁ ≃ₜ U₂,
          IsAEMorphism SO4 Sph3 (φ : U₁ → U₂) ∧ ∃ x : U₁, (φ x : Susp M) ≠ x := by
  haveI := h.connectedSpace
  haveI := h.locallyConnectedSpace
  letI := thurstonSuspension (M := M)
  intro y hy hyO
  rw [h.thurston_sing_eq hθ] at hy
  rcases hy with hyO' | ⟨⟨σ, t⟩, ⟨⟨i, -, rfl⟩, ht⟩, rfl⟩
  · exact absurd hyO' hyO
  -- the `X_θ`-chart `c` at `p i`, read as an open partial homeomorphism `cφ : Σ ⇀ C_θ`
  set θ' : ConeAngle := ⟨θ i, h.pos i⟩ with hθ'
  obtain ⟨c⟩ := h.isConePoint i
  haveI : Nonempty M := ⟨p i⟩
  set R := SphCone.halfRot θ' with hR
  set cφ : OpenPartialHomeomorph M (SphCone θ') := opensOPH c.φ with hcφ
  have hcφsrc : cφ.source = (c.U : Set M) := rfl
  have hcφtgt : cφ.target = (c.V : Set (SphCone θ')) := rfl
  have hcφp : cφ (p i) = SphCone.apex θ' := by
    rw [hcφ, opensOPH_apply c.φ c.mem]; exact c.sphCone_apex
  have hRae := SphCone.isAEMorphism_halfRot θ'
  have hRreg := (hRae.preimage_reg_sing R.isLocalHomeomorph).1
  -- `D`: the component of the apex in `c.V ∩ R⁻¹(c.V)`
  set D₀ : Set (SphCone θ') := (c.V : Set (SphCone θ')) ∩ R ⁻¹' (c.V : Set (SphCone θ'))
  have hD₀o : IsOpen D₀ := c.V.isOpen.inter (c.V.isOpen.preimage R.continuous)
  have hapexV : SphCone.apex θ' ∈ (c.V : Set (SphCone θ')) := by
    rw [← hcφp, ← hcφtgt]; exact cφ.map_source c.mem
  have hapexD₀ : SphCone.apex θ' ∈ D₀ :=
    ⟨hapexV, by
      show R (SphCone.apex θ') ∈ (c.V : Set (SphCone θ'))
      rw [hR, SphCone.halfRot_apex]; exact hapexV⟩
  set D := connectedComponentIn D₀ (SphCone.apex θ') with hDdef
  have hDo : IsOpen D := hD₀o.connectedComponentIn
  have hDc : IsConnected D := isConnected_connectedComponentIn_iff.2 hapexD₀
  have hDsub : D ⊆ D₀ := connectedComponentIn_subset _ _
  have hapexD : SphCone.apex θ' ∈ D := mem_connectedComponentIn hapexD₀
  -- `F = cφ⁻¹ ∘ R ∘ cφ` on `cφ⁻¹(D)`
  set W₀ := cφ.source ∩ cφ ⁻¹' D with hW₀def
  have hW₀ : IsOpen W₀ := cφ.isOpen_inter_preimage hDo
  set F : OpenPartialHomeomorph M M :=
    ((cφ.trans R.toOpenPartialHomeomorph).trans cφ.symm).restrOpen W₀ hW₀ with hFdef
  have hFapp : ∀ m, F m = cφ.symm (R (cφ m)) := fun m => rfl
  have hFsrc : F.source = W₀ := by
    rw [hFdef, OpenPartialHomeomorph.restrOpen_source]
    refine inter_eq_right.2 fun m hm => ?_
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.trans_source]
    exact ⟨⟨hm.1, trivial⟩, (hDsub hm.2).2⟩
  have hW₀eq : W₀ = cφ.symm '' D := by
    ext m
    constructor
    · rintro ⟨hm1, hm2⟩
      exact ⟨cφ m, hm2, cφ.left_inv hm1⟩
    · rintro ⟨z, hz, rfl⟩
      have hzV : z ∈ cφ.target := (hDsub hz).1
      exact ⟨cφ.map_target hzV, by show cφ (cφ.symm z) ∈ D; rw [cφ.right_inv hzV]; exact hz⟩
  have hFc : IsConnected F.source := by
    rw [hFsrc, hW₀eq]
    exact hDc.image _ (cφ.continuousOn_symm.mono fun z hz => (hDsub hz).1)
  have hpF : p i ∈ F.source := by
    rw [hFsrc]; exact ⟨c.mem, by show cφ (p i) ∈ D; rw [hcφp]; exact hapexD⟩
  -- `F` is read, at each regular point, by an element of `SO(3)`
  have hFread : ∀ σ' ∈ F.source, σ' ∈ Reg SO3 Sph2 M → F σ' ∈ Reg SO3 Sph2 M ∧
      ∀ e ∈ aeAtlas SO3 Sph2 M, σ' ∈ e.source → ∀ e' ∈ aeAtlas SO3 Sph2 M, F σ' ∈ e'.source →
        ∃ A : SO3, ∀ᶠ y in 𝓝 σ', e' (F y) = A • e y := by
    intro σ' hσ' hσreg
    rw [hFsrc] at hσ'
    obtain ⟨hσU, hσD⟩ := hσ'
    have hσU' : σ' ∈ c.U := hσU
    obtain ⟨hzreg, hr1⟩ := c.isAEMorphism.eventually_smul_eq_of_opens (F := cφ)
      (fun y hy => opensOPH_apply c.φ hy) hσU' hσreg
    set z := cφ σ' with hz
    have hRzreg : R z ∈ Reg SO3 Sph2 (SphCone θ') := by
      have : z ∈ R ⁻¹' Reg SO3 Sph2 (SphCone θ') := by rw [hRreg]; exact hzreg
      exact this
    have hRzV : R z ∈ c.V := (hDsub hσD).2
    obtain ⟨hFreg, hr3⟩ :=
      (IsAEMorphism.symm_of_homeomorph c.isAEMorphism).eventually_smul_eq_of_opens
        (F := cφ.symm) (fun n hn => opensOPH_symm_apply c.φ hn) hRzV hRzreg
    refine ⟨hFreg, fun e he hσe e' he' hFσe' => ?_⟩
    obtain ⟨a, ha, hza⟩ := mem_support.1 hzreg
    obtain ⟨a', ha', hRza'⟩ := mem_support.1 hRzreg
    obtain ⟨g₁, hg₁⟩ := hr1 e he hσe a ha hza
    obtain ⟨g₂, hg₂⟩ := hRae.eventually_smul_eq_of_mem hzreg hRzreg ha hza ha' hRza'
    obtain ⟨g₃, hg₃⟩ := hr3 a' ha' hRza' e' he' hFσe'
    refine ⟨g₃ * g₂ * g₁, ?_⟩
    have hc1 : ContinuousAt cφ σ' := cφ.continuousAt hσU
    have hc2 : ContinuousAt (fun y => R (cφ y)) σ' := R.continuous.continuousAt.comp hc1
    filter_upwards [hg₁, hc1.eventually hg₂, hc2.eventually hg₃] with y h1 h2 h3
    rw [hFapp, h3, h2, h1, mul_smul, mul_smul]
  -- its suspension
  set P := Susp.posChart F with hPdef
  have hPsrc : P.source = Susp.mk '' (F.source ×ˢ Ioi 0) := rfl
  have hPtgt : P.target = Susp.mk '' (F.target ×ˢ Ioi 0) := rfl
  obtain ⟨z, hzD, hzne⟩ := SphCone.exists_ne_apex_of_isOpen θ' hDo hapexD
  have hzV : z ∈ cφ.target := (hDsub hzD).1
  have hσ'F : cφ.symm z ∈ F.source := by
    rw [hFsrc]
    exact ⟨cφ.map_target hzV, by show cφ (cφ.symm z) ∈ D; rw [cφ.right_inv hzV]; exact hzD⟩
  refine ⟨⟨P.source, P.open_source⟩, ⟨P.target, P.open_target⟩, ?_, ?_, ?_, opensHomeoOf P,
    thurston_isAEMorphism_posChart (σ₀ := sph2Base) F hFread,
    ⟨Susp.mk (cφ.symm z, 1), ⟨(cφ.symm z, 1), ⟨hσ'F, show (0 : ℝ≥0) < 1 from one_pos⟩, rfl⟩⟩, ?_⟩
  · show IsConnected P.source
    rw [hPsrc]
    exact (hFc.prod isConnected_Ioi).image _ Susp.continuous_mk.continuousOn
  · show IsConnected P.target
    rw [hPtgt, ← F.image_source_eq_target]
    exact ((hFc.image _ F.continuousOn).prod isConnected_Ioi).image _
      Susp.continuous_mk.continuousOn
  · show Susp.mk (p i, t) ∈ P.source
    rw [hPsrc]; exact ⟨(p i, t), ⟨hpF, ht⟩, rfl⟩
  · rw [opensHomeoOf_apply]
    show Susp.mk (F (cφ.symm z), 1) ≠ Susp.mk (cφ.symm z, 1)
    intro heq
    have h1 := (Prod.ext_iff.1 (Susp.eq_of_mk_eq_of_pos heq
      (show (0 : ℝ≥0) < 1 from one_pos))).1
    simp only at h1
    rw [hFapp, cφ.right_inv hzV] at h1
    have hRzV : R z ∈ cφ.target := (hDsub hzD).2
    have h2 := congrArg cφ h1
    rw [cφ.right_inv hRzV, cφ.right_inv hzV] at h2
    exact SphCone.halfRot_ne θ' hzne h2

/-- **The local rotations about the singular rays do not extend** (`RamcovGX.tex:1935`: "locally
we may construct a rotation around any of the axes and … those cannot be extended as
automorphism of `M`"; `SuspensionCexFacts.rot`): a local isomorphism moving a point is not the
restriction of an automorphism, since `Aut(M) = {Id}`. -/
theorem IsConeSphere.thurston_rot {s : ℕ} {θ : Fin s → ℝ} {p : Fin s → M}
    (h : IsConeSphere M θ p) (hθ : 3 ≤ (Finset.univ.filter fun i => θ i ≠ 2 * π).card)
    (hAut : haveI := h.locallyConnectedSpace; singularAut SO3 Sph2 M = ⊥) :
    haveI := h.connectedSpace
    haveI := h.locallyConnectedSpace
    letI := thurstonSuspension (M := M)
    ∀ O ∈ (Susp.O : Set (Susp M)), ∀ y ∈ Sing SO4 Sph3 (Susp M), y ≠ O →
      ∃ (U₁ U₂ : Opens (Susp M)), IsConnected (U₁ : Set (Susp M)) ∧
        IsConnected (U₂ : Set (Susp M)) ∧ y ∈ U₁ ∧ ∃ φ : U₁ ≃ₜ U₂,
          IsAEMorphism SO4 Sph3 (φ : U₁ → U₂) ∧
            ¬ ∃ ψ ∈ singularAut SO4 Sph3 (Susp M), ∀ x : U₁, ψ x = (φ x : Susp M) := by
  haveI := h.connectedSpace
  haveI := h.locallyConnectedSpace
  letI := thurstonSuspension (M := M)
  intro O hO y hy hyO
  have hyO' : y ∉ (Susp.O : Set (Susp M)) := fun h' => hyO (Susp.eq_of_mem_O h' hO)
  obtain ⟨U₁, U₂, h₁, h₂, hyU, φ, hφ, x, hx⟩ := h.thurston_exists_local_ne_id hθ y hy hyO'
  refine ⟨U₁, U₂, h₁, h₂, hyU, φ, hφ, ?_⟩
  rintro ⟨ψ, hψ, hψφ⟩
  have hψ1 : ψ = 1 := by
    have := h.thurston_singularAut_eq_bot hθ hAut
    rw [Subgroup.eq_bot_iff_forall] at this
    exact this ψ hψ
  exact hx (by rw [← hψφ x, hψ1]; rfl)

end Facts

/-! ### The obligation -/

/-- **The facts of the cex for a cone sphere with `Aut(Σ) = {Id}`**, sorry-free: the singular locus
(`IsConeSphere.thurston_sing_eq`), the centre (`IsConeSphere.thurston_mem_sing_exists_ne`),
rigidity at the centre (`IsConeSphere.thurston_rigid`) and the local rotations
(`IsConeSphere.thurston_rot`). -/
theorem IsConeSphere.thurstonCexFacts_of_aut {M : Type} [TopologicalSpace M]
    [SingularGXStructure SO3 Sph2 M] {s : ℕ} {θ : Fin s → ℝ} {p : Fin s → M}
    (h : IsConeSphere M θ p) (hθ : 3 ≤ (Finset.univ.filter fun i => θ i ≠ 2 * π).card)
    (hAut : haveI := h.locallyConnectedSpace; singularAut SO3 Sph2 M = ⊥) :
    haveI := h.connectedSpace
    haveI := h.locallyConnectedSpace
    ThurstonCexFacts θ p := by
  haveI := h.connectedSpace
  haveI := h.locallyConnectedSpace
  letI := thurstonSuspension (M := M)
  exact ⟨h.thurston_sing_eq hθ, fun O hO => ⟨Susp.connectedSpace,
    (h.thurston_mem_sing_exists_ne hθ O hO).1, (h.thurston_mem_sing_exists_ne hθ O hO).2,
    h.thurston_rigid hθ hAut O hO, h.thurston_rot hθ hAut O hO⟩⟩

/-- **(iii) for the surfaces of the cex**: every cone sphere whose angles satisfy Troyanov's
condition and are pairwise distinct has no automorphism but the identity. -/
def ConeSphereAutTrivial : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [SingularGXStructure SO3 Sph2 M] {s : ℕ} (θ : Fin s → ℝ)
    (p : Fin s → M) (h : IsConeSphere M θ p), TroyanovAngleCondition θ →
    Pairwise (fun i j => θ i ≠ θ j) →
      haveI := h.locallyConnectedSpace
      singularAut SO3 Sph2 M = ⊥

/-- **The obligation is exactly (iii)**: `GX.ThurstonSuspensionFacts` holds iff every cone sphere of
the cex has a trivial automorphism group. `→`: rigidity at the centre kills `Aut(susp Σ)`
(`singularAut_eq_bot_of_rigid`), into which `Aut(Σ)` injects (`thurstonSuspAut_injective`);
`←`: `IsConeSphere.thurstonCexFacts_of_aut`. Both directions sorry-free. -/
theorem thurstonSuspensionFacts_iff : ThurstonSuspensionFacts ↔ ConeSphereAutTrivial := by
  constructor
  · intro hS M _ _ s θ p h hθ hd
    haveI := h.connectedSpace
    haveI := h.locallyConnectedSpace
    letI := thurstonSuspension (M := M)
    haveI : ConnectedSpace (Susp M) := Susp.connectedSpace
    have hF := hS M θ p h hθ hd
    have hbot : singularAut SO4 Sph3 (Susp M) = ⊥ :=
      singularAut_eq_bot_of_rigid (hF.cexFacts (Susp.mk (p ⟨0, by have := hθ.1; omega⟩, 0))
        rfl).rigid
    refine (Subgroup.eq_bot_iff_forall _).2 fun f hf => ?_
    have h1 : thurstonSuspAut sph2Base M ⟨f, hf⟩ = 1 := by
      have := (Subgroup.eq_bot_iff_forall _).1 hbot _ (thurstonSuspAut sph2Base M ⟨f, hf⟩).2
      exact Subtype.ext this
    have h2 : (⟨f, hf⟩ : singularAut SO3 Sph2 M) = 1 :=
      thurstonSuspAut_injective (σ₀ := sph2Base) (h1.trans (map_one _).symm)
    exact congrArg Subtype.val h2
  · intro hAut M _ _ s θ p h hθ hd
    exact h.thurstonCexFacts_of_aut hθ.three_le_card_ne_two_pi (hAut M θ p h hθ hd)

/-- **The Thurston suspension facts** (`RamcovGX.tex:1931–1937`), the statement of
`GX.ThurstonSuspensionFacts` (the obligation `GX.thurstonSuspensionFacts` of
`GXScaffold.Spherical.TroyanovAngles`), from (iii), `IsConeSphere.singularAut_eq_bot` (its only
`sorry`). -/
theorem thurstonSuspensionFacts' : ThurstonSuspensionFacts :=
  thurstonSuspensionFacts_iff.2 fun _ _ _ _ _ _ h hθ hd =>
    h.singularAut_eq_bot hθ.three_le_card_ne_two_pi hd

example : ThurstonSuspensionFacts := thurstonSuspensionFacts'

/-- The tied statement `GX.TroyanovSuspensionTheoremS3` from Troyanov's theorem
(`GX.troyanovTheorem`, its own obligation `GX.troyanovTheoremC`) and `thurstonSuspensionFacts'`:
the rewiring of `GX.troyanovSuspensionTheoremS3` downstream of this file (it cannot be done inside
`GXScaffold.Spherical.TroyanovAngles`, which this file imports). -/
theorem troyanovSuspensionTheoremS3' : TroyanovSuspensionTheoremS3 :=
  troyanovSuspensionTheoremS3_of troyanovTheorem thurstonSuspensionFacts'

/-- **The Thurston suspension facts under Theorem C's condition** (`GX.TroyanovAngleConditionC`,
DEC-174; for OQ-92, which asks whether the suspension statements move to it). Not the statement of
record: `GX.ThurstonSuspensionFacts` keeps l.1930's printed condition, which implies this one's
(`ThurstonSuspensionFactsC.thurstonSuspensionFacts`). -/
def ThurstonSuspensionFactsC : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [SingularGXStructure SO3 Sph2 M] {s : ℕ} (θ : Fin s → ℝ)
    (p : Fin s → M) (h : IsConeSphere M θ p), TroyanovAngleConditionC θ →
    Pairwise (fun i j => θ i ≠ θ j) →
      haveI := h.connectedSpace
      haveI := h.locallyConnectedSpace
      ThurstonCexFacts θ p

/-- The Theorem-C form implies the printed form. -/
theorem ThurstonSuspensionFactsC.thurstonSuspensionFacts (h : ThurstonSuspensionFactsC) :
    ThurstonSuspensionFacts := fun M _ _ _ θ p hM hθ hd =>
  h M θ p hM hθ.troyanovAngleConditionC hd

/-- **Under Theorem C's condition the facts follow in the same way** (the proofs use only "at least
three angles `≠ 2π`", `TroyanovAngleConditionC.three_le_card_ne_two_pi`), from (iii) for those
tuples, `IsConeSphere.singularAut_eq_bot` (the same `sorry`). -/
theorem thurstonSuspensionFactsC' : ThurstonSuspensionFactsC := fun _ _ _ _ _ _ h hθ hd =>
  h.thurstonCexFacts_of_aut hθ.three_le_card_ne_two_pi
    (h.singularAut_eq_bot hθ.three_le_card_ne_two_pi hd)

end GX
