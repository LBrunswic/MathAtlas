import Causal.GXSingularDEC25
import Causal.Flat.SecondCountable

/-!
# Chart isomorphisms over the maximal a.e. atlas, model-free

The model-free lemma of T-ett-e0-gx-structure, hoisted out of `Causal.Port.E0GXStructure`
(T-ett-maxatlas-hoist; a layer-1 module may not import a model, lean-benzecri kb/0047's discipline
of the programme's hoists): no statement or proof term changes, and every full name is kept.

* `Causal.chartIso_of_mem_maximalAEAtlas_of_agreeOn` and its corollaries
  `chartIso_of_mem_maximalAEAtlas_of_source_subset`, `forall_chartIso_maximalAEAtlas_of_support_subset`,
  `forall_chartIso_aeAtlas_of_reg_subset` (DEC-25's `hreg` form): a chart of the maximal a.e. atlas
  is a chart isomorphism when it agrees with the generating atlas, or when its source stays in the
  generating support.
* `Causal.AESupportCounterexample.counterexample`: without that condition the lemma fails (on `ℂ`
  with the translations).
* `Causal.isPreconnected_ball_diff_zero`, `Causal.isPortly_ne_zero`: gx's
  `GX.isPreconnected_ball_diff_zero` and `GX.isPortly_ne_zero` (`lean-gx/GX/Singular/Quotient.lean`
  l.2260, l.2284), restated (lean-causal never imports gx, DEC-33); formerly `E0GX.*`, kept there as
  deprecated aliases.

Imports: `Causal.GXSingularDEC25`, and `Causal.Flat.SecondCountable` for `isRigidAction_of_affine`
(the counterexample's translations); no model of ETT (`E₀`, `E_κ`) is imported.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set Filter Topology TopologicalSpace Function

universe u v w

/-! ### The model-free lemma: chart isomorphisms over the maximal a.e. atlas -/

section MaximalAEAtlasIso

variable {G : Type w} {X : Type v} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
  {Y : Type u} [TopologicalSpace Y]

/-- **Chart isomorphisms pass to the maximal a.e. atlas, where they are tied to the model.** Let
`A` be an a.e. `(G,X)`-atlas of `Y` whose charts are chart isomorphisms `DY → DX`, `G` acting by
strong morphisms of `DX`, `DX` absolutely minimal on its open sets. A chart `e` of the maximal a.e.
atlas of `A` is a chart isomorphism if `DY` is absolutely minimal on its source and agrees with the
transport of `DX` along `e` near the points of its source outside `supp A`. -/
theorem chartIso_of_mem_maximalAEAtlas_of_agreeOn {DX : Causality X} {DY : Causality Y}
    (hDX : ∀ W : Opens X, DX.AbsolutelyMinimalOn W)
    (hG : ∀ g : G, StrongMorphism DX DX fun p => g • p)
    {A : Set (OpenPartialHomeomorph Y X)} (hA : IsAEAtlas G A)
    (hAiso : ∀ a ∈ A, ChartIso DY DX a) {e : OpenPartialHomeomorph Y X}
    (he : e ∈ maximalAEAtlas G A) (hmin : DY.AbsolutelyMinimalOn (chartSource e))
    (hsing : ∀ x ∈ e.source, x ∉ support A →
      ∃ O : Opens Y, x ∈ O ∧ AgreeOn DY (DX.chartTransport e) O) :
    ChartIso DY DX e := by
  have hM := hA.maximalAEAtlas
  have hCe := DX.chartTransport_chartIso e
  have hloc : ∀ x ∈ chartSource e, ∃ O : Opens Y, x ∈ O ∧ AgreeOn DY (DX.chartTransport e) O := by
    intro x hx
    by_cases hxA : x ∈ support A
    · obtain ⟨a, ha, hxa⟩ := mem_support.1 hxA
      obtain ⟨g, O, hxO, hO, heq⟩ := exists_smul_eq_of_mem_gxGroupoid
        (hM.1.symm_trans_mem (hA.subset_maximalAEAtlas ha) he) hxa hx
      exact ⟨O, hxO, (hAiso a ha).agreeOn_of_smul hG hCe hO heq⟩
    · exact hsing x hx hxA
  have hTmin : (DX.chartTransport e).AbsolutelyMinimalOn (chartSource e) :=
    hCe.absolutelyMinimalOn le_rfl (hDX _)
  have hloc' : ∀ x ∈ chartSource e, ∃ O : Opens Y, x ∈ O ∧ AgreeOn (DX.chartTransport e) DY O :=
    fun x hx => by
      obtain ⟨O, hxO, hO⟩ := hloc x hx
      exact ⟨O, hxO, hO.symm⟩
  refine hCe.congr fun V hV x y => ?_
  have h1 := imp_of_agree_locally hmin hloc hV (x := x) (y := y)
  have h2 := imp_of_agree_locally hTmin hloc' hV (x := x) (y := y)
  exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2, h2.2⟩⟩

/-- The model-free lemma for a chart whose source lies in the support of the generating atlas. -/
theorem chartIso_of_mem_maximalAEAtlas_of_source_subset {DX : Causality X} {DY : Causality Y}
    (hDX : ∀ W : Opens X, DX.AbsolutelyMinimalOn W)
    (hG : ∀ g : G, StrongMorphism DX DX fun p => g • p)
    {A : Set (OpenPartialHomeomorph Y X)} (hA : IsAEAtlas G A)
    (hAiso : ∀ a ∈ A, ChartIso DY DX a) {e : OpenPartialHomeomorph Y X}
    (he : e ∈ maximalAEAtlas G A) (hmin : DY.AbsolutelyMinimalOn (chartSource e))
    (hsub : e.source ⊆ support A) : ChartIso DY DX e :=
  chartIso_of_mem_maximalAEAtlas_of_agreeOn hDX hG hA hAiso he hmin fun _ hx hxA =>
    absurd (hsub hx) hxA

/-- **The model-free lemma, every chart**: if the maximal a.e. atlas has no more support than the
generating one, and `DY` is absolutely minimal on its open sets, every chart of the maximal a.e.
atlas is a chart isomorphism. -/
theorem forall_chartIso_maximalAEAtlas_of_support_subset {DX : Causality X} {DY : Causality Y}
    (hDX : ∀ W : Opens X, DX.AbsolutelyMinimalOn W)
    (hG : ∀ g : G, StrongMorphism DX DX fun p => g • p)
    {A : Set (OpenPartialHomeomorph Y X)} (hA : IsAEAtlas G A)
    (hAiso : ∀ a ∈ A, ChartIso DY DX a) (hmin : ∀ W : Opens Y, DY.AbsolutelyMinimalOn W)
    (hsupp : support (maximalAEAtlas G A) ⊆ support A) :
    ∀ e ∈ maximalAEAtlas G A, ChartIso DY DX e :=
  fun e he => chartIso_of_mem_maximalAEAtlas_of_source_subset hDX hG hA hAiso he (hmin _)
    fun _ hx => hsupp (mem_support.2 ⟨e, he, hx⟩)

/-- **DEC-25's `hreg` from a generating atlas**: for a singular `(G,X)`-manifold `Y` whose maximal
a.e. atlas is that of an a.e. atlas `A` of chart isomorphisms, with `Reg Y ⊆ supp A`, every chart
of the maximal a.e. atlas is a chart isomorphism. -/
theorem forall_chartIso_aeAtlas_of_reg_subset [SingularGXStructure G X Y] {DX : Causality X}
    {DY : Causality Y} (hDX : ∀ W : Opens X, DX.AbsolutelyMinimalOn W)
    (hG : ∀ g : G, StrongMorphism DX DX fun p => g • p)
    {A : Set (OpenPartialHomeomorph Y X)} (hA : IsAEAtlas G A)
    (hAiso : ∀ a ∈ A, ChartIso DY DX a) (hmin : ∀ W : Opens Y, DY.AbsolutelyMinimalOn W)
    (hgen : aeAtlas G X Y = maximalAEAtlas G A) (hreg : Reg G X Y ⊆ support A) :
    ∀ r ∈ aeAtlas G X Y, ChartIso DY DX r := by
  intro r hr
  have hsupp : support (maximalAEAtlas G A) ⊆ support A := by
    have h : Reg G X Y = support (maximalAEAtlas G A) := by rw [Reg, hgen]
    rw [← h]; exact hreg
  rw [hgen] at hr
  exact forall_chartIso_maximalAEAtlas_of_support_subset hDX hG hA hAiso hmin hsupp r hr

end MaximalAEAtlasIso

/-! ### Two topology lemmas (restated from gx) -/

/-- A punctured disc of `ℂ` is preconnected (restated from gx's `GX.isPreconnected_ball_diff_zero`,
`lean-gx/GX/Singular/Quotient.lean` l.2260). -/
theorem isPreconnected_ball_diff_zero (ε : ℝ) :
    IsPreconnected (Metric.ball (0 : ℂ) ε \ {0}) := by
  have hc : Continuous fun q : ℝ × ℝ => (q.1 : ℂ) * Complex.exp (q.2 * Complex.I) :=
    (Complex.continuous_ofReal.comp continuous_fst).mul
      (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp continuous_snd).mul
        continuous_const))
  convert (((convex_Ioo (0 : ℝ) ε).prod (convex_univ : Convex ℝ (univ : Set ℝ))).isPreconnected).image
    _ hc.continuousOn using 1
  ext w
  constructor
  · rintro ⟨hw, hw0⟩
    refine ⟨(‖w‖, Complex.arg w), ⟨⟨norm_pos_iff.2 hw0, by simpa using hw⟩, mem_univ _⟩, ?_⟩
    exact Complex.norm_mul_exp_arg_mul_I w
  · rintro ⟨q, ⟨⟨h1, h2⟩, -⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [mem_ball_zero_iff, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg h1.le]
      exact h2
    · simp only [mem_singleton_iff, mul_eq_zero, Complex.ofReal_eq_zero, Complex.exp_ne_zero,
        or_false]
      exact h1.ne'

/-- `𝔼^n ∖ S` is portly for `S = {0} × Z`, here `Z = ℝ` (restated from gx's
`GX.isPortly_ne_zero`, `lean-gx/GX/Singular/Quotient.lean` l.2284, at `Z = ℝ`: lean-causal has no
instance `LocallyConnectedSpace (ℂ × Z)` for a general locally connected `Z`; the proof is gx's
verbatim, with `Z` the abbreviation below, but for `mem_setOf_eq`, dropped from one `simp only` where
it is unused at `Z = ℝ`). -/
theorem isPortly_ne_zero : IsPortly {x : ℂ × ℝ | x.1 ≠ 0} := by
  let Z := ℝ
  have hP : {x : ℂ × Z | x.1 ≠ 0} = ({0}ᶜ : Set ℂ) ×ˢ univ := by ext x; simp
  have hopen : IsOpen {x : ℂ × Z | x.1 ≠ 0} := isOpen_ne.preimage continuous_fst
  have hd : Dense {x : ℂ × Z | x.1 ≠ 0} := by
    rw [hP]; exact (dense_compl_singleton (0 : ℂ)).prod dense_univ
  refine ⟨hopen, hd, fun W hW hWc => ?_⟩
  refine isPreconnected_of_local hWc inter_subset_left
    (fun x hx => hW.inter_closure ⟨hx, hd x⟩) fun x hx => ?_
  by_cases hx1 : x.1 ≠ 0
  · refine ⟨connectedComponentIn (W ∩ {x : ℂ × Z | x.1 ≠ 0}) x,
      (hW.inter hopen).connectedComponentIn, mem_connectedComponentIn ⟨hx, hx1⟩, ?_⟩
    rw [inter_eq_left.2 (connectedComponentIn_subset _ _)]
    exact isPreconnected_connectedComponentIn
  · rw [not_ne_iff] at hx1
    obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 (hW.mem_nhds hx)
    rw [hx1] at hu
    obtain ⟨ε, hε, hεu⟩ := Metric.mem_nhds_iff.1 hu
    obtain ⟨V, hVv, hVo, hzV, hVc⟩ :=
      locallyConnectedSpace_iff_subsets_isOpen_isConnected.1 inferInstance x.2 v hv
    refine ⟨Metric.ball (0 : ℂ) ε ×ˢ V, Metric.isOpen_ball.prod hVo,
      ⟨by rw [hx1]; exact Metric.mem_ball_self hε, hzV⟩, ?_⟩
    have heq : (Metric.ball (0 : ℂ) ε ×ˢ V) ∩ (W ∩ {x : ℂ × Z | x.1 ≠ 0}) =
        (Metric.ball (0 : ℂ) ε \ {0}) ×ˢ V := by
      ext ⟨w, z⟩
      simp only [mem_inter_iff, mem_prod, Set.mem_sdiff, mem_singleton_iff]
      constructor
      · rintro ⟨⟨h1, h2⟩, -, h3⟩; exact ⟨⟨h1, h3⟩, h2⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨h1, h3⟩, huv ⟨hεu h1, hVv h3⟩, h2⟩
    rw [heq]
    exact (isPreconnected_ball_diff_zero ε).prod hVc.isPreconnected

/-! ### The model-free lemma needs its support condition: a counterexample

On `ℂ` with the translations, `segCausality F` relates `x` to `y` in `U` when `y` is reached from
`x` by a horizontal rightward segment inside `U` avoiding `F` (and every point to itself); its
chronology is empty. With `DX = segCausality ∅` and `DY = segCausality {0}`, the chart
`id` on `ℂ ∖ {0}` is a chart isomorphism, generates an a.e. atlas whose maximal atlas contains
`id` on `ℂ`, and `id` is not a chart isomorphism: `-1 ≤ 1` in `DX`, not in `DY`. -/

namespace AESupportCounterexample

/-- The horizontal segment from `x` rightward to the abscissa of `y`. -/
def hseg (x y : ℂ) : Set ℂ := {z | z.im = x.im ∧ z.re ∈ Icc x.re y.re}

/-- The causal relation of `segCausality F` in `U`. -/
def SegRel (F : Set ℂ) (U : Opens ℂ) (x y : ℂ) : Prop :=
  x ∈ U ∧ y ∈ U ∧
    (x = y ∨ (x.im = y.im ∧ x.re < y.re ∧ hseg x y ⊆ U ∧ Disjoint (hseg x y) F))

/-- **Horizontal causality avoiding `F`**, with empty chronology. -/
def segCausality (F : Set ℂ) : Causality ℂ where
  le := SegRel F
  lt _ _ _ := False
  le_mem_left h := h.1
  le_mem_right h := h.2.1
  lt_mem_left h := h.elim
  lt_mem_right h := h.elim
  le_refl hx := ⟨hx, hx, Or.inl rfl⟩
  le_trans := by
    intro U x y z h₁ h₂
    obtain ⟨hx, -, h₁⟩ := h₁
    obtain ⟨-, hz, h₂⟩ := h₂
    refine ⟨hx, hz, ?_⟩
    rcases h₁ with rfl | ⟨i₁, r₁, s₁, d₁⟩
    · exact h₂
    rcases h₂ with rfl | ⟨i₂, r₂, s₂, d₂⟩
    · exact Or.inr ⟨i₁, r₁, s₁, d₁⟩
    have hsub : hseg x z ⊆ hseg x y ∪ hseg y z := by
      rintro w ⟨hw, hw1, hw2⟩
      by_cases h : w.re ≤ y.re
      · exact Or.inl ⟨hw, hw1, h⟩
      · exact Or.inr ⟨hw.trans i₁, (not_le.1 h).le, hw2⟩
    exact Or.inr ⟨i₁.trans i₂, r₁.trans r₂, hsub.trans (union_subset s₁ s₂),
      Disjoint.mono_left hsub (disjoint_union_left.2 ⟨d₁, d₂⟩)⟩
  lt_trans h _ := h.elim
  le_mono := by
    intro U V hVU x y h
    obtain ⟨hx, hy, h⟩ := h
    exact ⟨hVU hx, hVU hy, h.imp id fun h' => ⟨h'.1, h'.2.1, fun z hz => hVU (h'.2.2.1 hz),
      h'.2.2.2⟩⟩
  lt_mono _ _ _ h := h
  le_of_lt h := h.elim
  isOpen_lt_right _ _ := by simp
  isOpen_lt_left _ _ := by simp

/-- `segCausality F` is absolutely minimal on every open set: a horizontal segment is a chain of
short ones (Lebesgue number, `exists_subdivision_Icc`). -/
theorem absolutelyMinimalOn_segCausality (F : Set ℂ) (W : Opens ℂ) :
    (segCausality F).AbsolutelyMinimalOn W := by
  intro S hS V hV x y
  refine ⟨fun hxy => ?_, fun hxy => hxy.elim⟩
  obtain ⟨hx, hy, h⟩ := hxy
  rcases h with rfl | ⟨hi, hr, hsV, hdF⟩
  · obtain ⟨O, hO, hxO⟩ := hS x (hV hx)
    exact Relation.TransGen.single ⟨O, hO, ⟨hx, hxO⟩, ⟨hx, hxO⟩, Or.inl rfl⟩
  set γ : ℝ → ℂ := fun t => (t : ℂ) + (x.im : ℂ) * Complex.I with hγdef
  have hγre : ∀ t, (γ t).re = t := fun t => by simp [hγdef]
  have hγim : ∀ t, (γ t).im = x.im := fun t => by simp [hγdef]
  have hγ : Continuous γ := Complex.continuous_ofReal.add continuous_const
  have hγeq : ∀ w : ℂ, w.im = x.im → γ w.re = w := fun w hw =>
    Complex.ext (hγre _) (by rw [hγim, hw])
  have hγmem : ∀ t ∈ Icc x.re y.re, γ t ∈ hseg x y := fun t ht =>
    ⟨hγim t, by rw [hγre]; exact ht⟩
  have hcov : Icc x.re y.re ⊆ ⋃ O : S, γ ⁻¹' ((O : Opens ℂ) : Set ℂ) := fun t ht => by
    obtain ⟨O, hO, hO'⟩ := hS (γ t) (hV (hsV (hγmem t ht)))
    exact mem_iUnion.2 ⟨⟨O, hO⟩, hO'⟩
  obtain ⟨τ, hτ0, hτm, ⟨m, hm⟩, hτI, hτO⟩ :=
    exists_subdivision_Icc hr.le (fun O : S => (O.1.isOpen.preimage hγ)) hcov
  have hstep : ∀ n, ∃ O ∈ S, (segCausality F).le (V ⊓ O) (γ (τ n)) (γ (τ (n + 1))) := by
    intro n
    obtain ⟨⟨O, hO⟩, hsub⟩ := hτO n
    refine ⟨O, hO, ?_⟩
    have hn : τ n ≤ τ (n + 1) := hτm (Nat.le_succ n)
    have hI : ∀ t ∈ Icc (τ n) (τ (n + 1)), t ∈ Icc x.re y.re := fun t ht =>
      ⟨(hτI n).1.trans ht.1, ht.2.trans (hτI (n + 1)).2⟩
    have hmem : ∀ t ∈ Icc (τ n) (τ (n + 1)), γ t ∈ V ⊓ O := fun t ht =>
      ⟨hsV (hγmem t (hI t ht)), hsub ht⟩
    refine ⟨hmem _ ⟨le_rfl, hn⟩, hmem _ ⟨hn, le_rfl⟩, ?_⟩
    rcases hn.lt_or_eq with hlt | heq
    · have hseg_sub : hseg (γ (τ n)) (γ (τ (n + 1))) ⊆ γ '' Icc (τ n) (τ (n + 1)) := by
        rintro w ⟨hw1, hw2⟩
        rw [hγim] at hw1
        rw [hγre, hγre] at hw2
        exact ⟨w.re, hw2, hγeq w hw1⟩
      refine Or.inr ⟨by rw [hγim, hγim], by rw [hγre, hγre]; exact hlt, ?_, ?_⟩
      · rintro _ hw
        obtain ⟨t, ht, rfl⟩ := hseg_sub hw
        exact hmem t ht
      · refine Disjoint.mono_left (hseg_sub.trans ?_) hdF
        rintro _ ⟨t, ht, rfl⟩
        exact hγmem t (hI t ht)
    · exact Or.inl (by rw [heq])
  have hchain : ∀ n, Relation.ReflTransGen
      (fun a b => ∃ O ∈ S, (segCausality F).le (V ⊓ O) a b) x (γ (τ n)) := by
    intro n
    induction n with
    | zero => rw [hτ0, hγeq x rfl]
    | succ n ih => exact ih.tail (hstep n)
  have hym : γ (τ m) = y := by rw [hm m le_rfl, hγeq y hi.symm]
  have hc := hchain m
  rw [hym] at hc
  rcases Relation.reflTransGen_iff_eq_or_transGen.1 hc with h | h
  · exact absurd (congrArg Complex.re h) (ne_of_gt hr)
  · exact h

theorem absolutelyMinimal_segCausality (F : Set ℂ) : (segCausality F).AbsolutelyMinimal :=
  Precausality.absolutelyMinimal_iff.2 (absolutelyMinimalOn_segCausality F ⊤)

/-- The translations act by strong morphisms of `segCausality ∅`. -/
theorem strongMorphism_segCausality_empty (g : Multiplicative ℂ) :
    StrongMorphism (segCausality ∅) (segCausality ∅) fun p => g • p := by
  have hφ : ∀ p : ℂ, g • p = Multiplicative.toAdd g + p := fun _ => rfl
  refine ⟨continuous_const_smul g, isOpenMap_smul g, fun U V hV x y h => ?_, fun _ _ _ _ _ h =>
    h.elim⟩
  have hVU : ∀ {z : ℂ}, z ∈ V → g • z ∈ U := fun {z} hz => by
    have : z ∈ (V : Set ℂ) := hz
    rw [hV] at this; exact this
  obtain ⟨hx, hy, h⟩ := h
  refine ⟨hVU hx, hVU hy, ?_⟩
  rcases h with rfl | ⟨i, r, sV, -⟩
  · exact Or.inl rfl
  refine Or.inr ⟨?_, ?_, fun w hw => ?_, disjoint_empty _⟩
  · rw [hφ, hφ, Complex.add_im, Complex.add_im, i]
  · rw [hφ, hφ, Complex.add_re, Complex.add_re]; linarith
  · obtain ⟨hw1, hw2, hw3⟩ := hw
    rw [hφ, Complex.add_im] at hw1
    rw [hφ, Complex.add_re] at hw2
    rw [hφ, Complex.add_re] at hw3
    have hmem : w - Multiplicative.toAdd g ∈ hseg x y :=
      ⟨by rw [Complex.sub_im]; linarith, by rw [Complex.sub_re]; linarith,
        by rw [Complex.sub_re]; linarith⟩
    have := hVU (sV hmem)
    rwa [hφ, add_sub_cancel] at this

/-- The translations of `ℂ` act rigidly (by affine maps). -/
theorem isRigidAction_translation : IsRigidAction (Multiplicative ℂ) ℂ :=
  isRigidAction_of_affine fun g =>
    ⟨(AffineEquiv.constVAdd ℝ ℂ (Multiplicative.toAdd g)).toAffineMap, fun _ => rfl⟩

attribute [local instance] isRigidAction_translation

/-- `ℂ ∖ {0}` is portly in `ℂ`. -/
theorem isPortly_compl_zero : IsPortly ({0}ᶜ : Set ℂ) := by
  have hopen : IsOpen ({0}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hd : Dense ({0}ᶜ : Set ℂ) := dense_compl_singleton 0
  refine ⟨hopen, hd, fun W hW hWc => ?_⟩
  refine isPreconnected_of_local hWc inter_subset_left
    (fun x hx => hW.inter_closure ⟨hx, hd x⟩) fun x hx => ?_
  by_cases hx0 : x = 0
  · subst hx0
    obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.1 hW 0 hx
    refine ⟨Metric.ball 0 ε, Metric.isOpen_ball, Metric.mem_ball_self hε, ?_⟩
    have heq : Metric.ball (0 : ℂ) ε ∩ (W ∩ {0}ᶜ) = Metric.ball 0 ε \ {0} := by
      ext z
      simp only [mem_inter_iff, Set.mem_sdiff, mem_compl_iff]
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hεW h.1, h.2⟩⟩
    rw [heq]
    exact isPreconnected_ball_diff_zero ε
  · refine ⟨connectedComponentIn (W ∩ {0}ᶜ) x, (hW.inter hopen).connectedComponentIn,
      mem_connectedComponentIn ⟨hx, hx0⟩, ?_⟩
    rw [inter_eq_left.2 (connectedComponentIn_subset _ _)]
    exact isPreconnected_connectedComponentIn

/-- The generating chart: the identity of `ℂ ∖ {0}`. -/
noncomputable def puncturedChart : OpenPartialHomeomorph ℂ ℂ :=
  OpenPartialHomeomorph.ofSet {0}ᶜ isOpen_compl_singleton

theorem isAEAtlas_puncturedChart :
    IsAEAtlas (Multiplicative ℂ) ({puncturedChart} : Set (OpenPartialHomeomorph ℂ ℂ)) := by
  have hsupp : support ({puncturedChart} : Set (OpenPartialHomeomorph ℂ ℂ)) = {0}ᶜ := by
    ext x
    rw [mem_support]
    constructor
    · rintro ⟨e, he, hx⟩
      rw [mem_singleton_iff.1 he] at hx; exact hx
    · intro hx; exact ⟨_, mem_singleton _, hx⟩
  refine ⟨isGXAtlas_of_eventually fun e he e' he' x _ => ⟨1, Eventually.of_forall fun z => ?_⟩,
    by rw [hsupp]; exact isPortly_compl_zero⟩
  rw [mem_singleton_iff.1 he, mem_singleton_iff.1 he', one_smul]

theorem chartIso_puncturedChart :
    ChartIso (segCausality {0}) (segCausality ∅) puncturedChart := by
  intro U hU x _ y _
  have hU' : (U : Set ℂ) ⊆ {0}ᶜ := hU
  have himg : chartImage puncturedChart U = U := by
    apply SetLike.coe_injective
    rw [coe_chartImage_of_le hU]
    exact image_id _
  rw [himg]
  refine ⟨?_, Iff.rfl⟩
  show SegRel {0} U x y ↔ SegRel ∅ U x y
  constructor
  · rintro ⟨hx, hy, h⟩
    exact ⟨hx, hy, h.imp id fun h' => ⟨h'.1, h'.2.1, h'.2.2.1, disjoint_empty _⟩⟩
  · rintro ⟨hx, hy, h⟩
    refine ⟨hx, hy, h.imp id fun h' => ⟨h'.1, h'.2.1, h'.2.2.1, ?_⟩⟩
    rw [disjoint_singleton_right]
    intro h0
    exact hU' (h'.2.2.1 h0) rfl

theorem refl_mem_maximalAEAtlas :
    OpenPartialHomeomorph.refl ℂ ∈
      maximalAEAtlas (Multiplicative ℂ) ({puncturedChart} : Set (OpenPartialHomeomorph ℂ ℂ)) := by
  have hid : ∀ e ∈ insert (OpenPartialHomeomorph.refl ℂ)
      ({puncturedChart} : Set (OpenPartialHomeomorph ℂ ℂ)), ∀ z, e z = z := by
    rintro e (rfl | he) z
    · rfl
    · rw [mem_singleton_iff.1 he]; rfl
  have hGX : IsGXAtlas (Multiplicative ℂ) (insert (OpenPartialHomeomorph.refl ℂ)
      ({puncturedChart} : Set (OpenPartialHomeomorph ℂ ℂ))) :=
    isGXAtlas_of_eventually fun e he e' he' _ _ =>
      ⟨1, Eventually.of_forall fun z => by rw [hid e he, hid e' he', one_smul]⟩
  have hB : IsAEAtlas (Multiplicative ℂ) (insert (OpenPartialHomeomorph.refl ℂ)
      ({puncturedChart} : Set (OpenPartialHomeomorph ℂ ℂ))) :=
    ⟨hGX, isAEAtlas_puncturedChart.2.mono (support_mono (subset_insert _ _)) (isOpen_support _)⟩
  exact subset_maximalAEAtlas hB (hGX.isThinner_completion_of_subset (subset_insert _ _))
    (mem_insert _ _)

theorem not_chartIso_refl :
    ¬ ChartIso (segCausality {0}) (segCausality ∅) (OpenPartialHomeomorph.refl ℂ) := by
  intro h
  have hmem : ∀ z : ℂ, z ∈ chartImage (OpenPartialHomeomorph.refl ℂ) ⊤ := fun z =>
    mem_chartImage_of_mem (mem_univ z) trivial
  have hR : (segCausality ∅).le (chartImage (OpenPartialHomeomorph.refl ℂ) ⊤) (-1) 1 :=
    ⟨hmem _, hmem _, Or.inr ⟨by simp, by norm_num, fun z _ => hmem z, disjoint_empty _⟩⟩
  obtain ⟨-, -, h'⟩ := ((h ⊤ (fun z _ => mem_univ z) (-1) trivial 1 trivial).1).2 hR
  rcases h' with h' | ⟨-, -, -, hd⟩
  · have := congrArg Complex.re h'
    norm_num at this
  · have h0 : (0 : ℂ) ∈ hseg (-1) 1 := ⟨by simp, by norm_num, by norm_num⟩
    exact disjoint_left.1 hd h0 (mem_singleton 0)

/-- **The model-free lemma fails without its support condition** (the roadmap's wording): an a.e.
atlas of chart isomorphisms, the group acting by strong morphisms, `DY` absolutely minimal (on
every open set, and `DX` too), and a chart of the maximal a.e. atlas which is not a chart
isomorphism. Its source meets the complement of the generating support, where `DY` is free. -/
theorem counterexample :
    IsAEAtlas (Multiplicative ℂ) ({puncturedChart} : Set (OpenPartialHomeomorph ℂ ℂ)) ∧
    (∀ a ∈ ({puncturedChart} : Set (OpenPartialHomeomorph ℂ ℂ)),
      ChartIso (segCausality {0}) (segCausality ∅) a) ∧
    (∀ g : Multiplicative ℂ, StrongMorphism (segCausality ∅) (segCausality ∅) fun p => g • p) ∧
    (segCausality {0}).AbsolutelyMinimal ∧
    (∀ W : Opens ℂ, (segCausality {0}).AbsolutelyMinimalOn W) ∧
    (∀ W : Opens ℂ, (segCausality ∅).AbsolutelyMinimalOn W) ∧
    OpenPartialHomeomorph.refl ℂ ∈
      maximalAEAtlas (Multiplicative ℂ) ({puncturedChart} : Set (OpenPartialHomeomorph ℂ ℂ)) ∧
    ¬ ChartIso (segCausality {0}) (segCausality ∅) (OpenPartialHomeomorph.refl ℂ) :=
  ⟨isAEAtlas_puncturedChart, fun a ha => by rw [mem_singleton_iff.1 ha]; exact chartIso_puncturedChart,
    strongMorphism_segCausality_empty, absolutelyMinimal_segCausality _,
    absolutelyMinimalOn_segCausality _, absolutelyMinimalOn_segCausality _,
    refl_mem_maximalAEAtlas, not_chartIso_refl⟩

end AESupportCounterexample

end Causal
