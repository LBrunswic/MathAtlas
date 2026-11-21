import Causal.CauchyExtension
import Causal.LadderLocal
import Causal.GXStructure
import Mathlib.CategoryTheory.Iso

/-!
# Causal isomorphisms and what they transport; causality from a function increasing along `≤`

Programme target `T-abs-causal-iso-invariance` (layer 1, `programme/roadmap.toml`): ETT-layer
imports only (`Causal.CauchyExtension`, `Causal.LadderLocal`, `Causal.GXStructure`), no model,
no metric. No label of
`ETT.tex`. Source: Eperon–Reall–Sbierski 1802.03020,
`papers/ers-predictability/legacy/labeled/ghd_02_19.tex` (binder
`papers/ers-predictability/certificate/binder.toml`).

* **`T-abs-causal-iso-invariance/iso`** (ERS Lemma 3.27, `ghd_02_19.tex:335`; proof of 3.31,
  `:372`) — `IsCausalIso` (a homeomorphism with `e`, `e⁻¹` strong morphisms, DEC-10),
  `isCausalIso_iff` (`≤_U`, `≪_U` are `≤_{e(U)}`, `≪_{e(U)}` on every open `U`),
  `Causality.transport`, `isCausalIso_iff_eq_transport`, `isCausalIso_iff_nonempty_iso` (the
  isomorphisms of `def:category_topological_spacetimes`), `isCausalIso_iff_chartIso` (the strict
  `ChartIso` for a global chart), `chartTransport_toOpenPartialHomeomorph`, `refl`, `symm`,
  `trans`, `dual`, `IsCausalIso.isEMorphism`.
* **`T-abs-causal-iso-invariance/causal`** (3.29 `:349`, 3.31 `:367`, `:375`) —
  `IsCausalIso.isCausal_iff`, `LeTopIso.isCausal_iff`.
* **`T-abs-causal-iso-invariance/gh`** (3.31 `:367`, 3.39 `:426`) — `globallyHyperbolic_iff`,
  `causallyCompact_iff`, `globallyHyperbolicOn_iff`, `diamond_image`.
* **`T-abs-causal-iso-invariance/strongly-causal`** (`:375`) — `stronglyCausal_iff`,
  `stronglyCausalOpen_iff`, `causallyConvexIn_image_iff`.
* **`T-abs-causal-iso-invariance/cauchy`** (3.31 `:367`) — `isCauchySurfaceOn_image_iff`,
  `isCauchySurface_image_iff`, `isCauchySurface_preimage_iff`,
  `globallyHyperbolic_and_isCauchySurface_iff` (3.31 as printed), `inextensible_iff`,
  `isAcausal_image_iff`.
* **`T-abs-causal-iso-invariance/ladder`** (`:375`) — every causality-sort node of
  `programme/ladder.toml` (`time_function` is the next item): `tarentin_iff`, `pushUp_iff`,
  `causallyOpen_iff`, `causallyOpenFuture_iff`, `causallyPlain_iff`, `absolutelyMinimal_iff`,
  `causallyArcConnected_iff`, `curvesExtend_iff`; the side conditions of `Causal.LadderLocal`
  (`locallyPushUp_iff`, `locallyCausallyOpenFuture_iff`, `locallyCausallyOpen_iff`,
  `chronalPastNeighbours_iff`, `chronalNeighbours_iff`, `noPastEndpoint_iff`,
  `noCausalEndpoint_iff`); `locallyCausallyArcConnected_iff`, the `…On` forms, `Zplus_image`,
  `causalCurveOn_iff`, `chronalCurveOn_iff`.
* **`T-abs-causal-iso-invariance/time-function`** (3.29 `:349`, 3.39 `:426`) —
  `isTimeFunction_comp_iff` (`defi:fonction_temps`), `isTimeFunctionOrder_comp_iff`,
  `isCauchyTimeFunction_comp_iff`, `exists_timeFunction_iff` (the body of the node
  `time_function`), `strictMono_le_comp_iff`.
* **`T-abs-causal-iso-invariance/strict-causal`** (3.29 `:349`) —
  `Causality.isCausal_of_timeFunction`, `Causality.isCausal_of_exists_timeFunction`,
  `IsCausalIso.isCausal_of_timeFunction`; the separation `exists_isTimeFunction_not_isCausal`.

> Lemma 3.27. Consider a Born-Infeld solution constructed as in Theorem 3.25. In coordinates
> $(\rho,\sigma)$, the metric (3.18) is $g = c(1+\Phi_1'(\rho)\Phi_2'(\sigma))^2 d\rho d\sigma$.
> (`:335`)

> Lemma 3.29. […] In either case the spacetime $(U,g)$ is stably causal. — Proof. In the
> subluminal case ($c=1$) we know […] that $x^0$ is a global time function for the spacetime
> $(U,g)$ so this spacetime is stably causal. […] hence $\rho+\sigma$ is a global time function
> for $(U,g)$ and so $(U,g)$ is stably causal. (`:349`, `:354`, `:360`)

> Lemma 3.31. […] Then $(U,g)$ is globally hyperbolic with Cauchy surface $S$ if, and only if,
> $(V,\hat{m})$ is globally hyperbolic with Cauchy surface $\Sigma=\Psi^{-1}(S)$, where
> $\hat{m} = c\, d\rho d\sigma$. — Proof. This is an immediate consequence of (3.21) which shows
> that $g$ and $\hat{m}$ define causally equivalent metrics on $V$. (`:367`, `:372`)

> Thus global hyperbolicity can be checked using the flat metric $\hat{m}$ on $V$. More
> generally, the causal properties of $(U,g)$ are the same as those of the flat spacetime
> $(V,\hat{m})$. (`:375`)

> Lemma 3.39. The solution of Theorem 3.38 is globally hyperbolic. — Proof. This follows
> immediately from Lemma 3.31 because $(V,\hat{m})=(\mathbb{R}^2,\hat{m})$ […] (`:426`)

## How the rows factor

`(M, C)` is `(V, m̂)`, `(N, D)` is `(U, g)`, `e` is the hodograph map `Ψ`. Layer 3 (Lemma 3.27: a
conformal factor does not change the causal cones) supplies `IsCausalIso C D Ψ`, equivalently
`D = C.transport Ψ`. Then 3.31 is `globallyHyperbolic_and_isCauchySurface_iff`; 3.39 is
`globallyHyperbolic_iff` applied to the GH of `(ℝ², m̂)` (a model fact); `:375` is the ladder
group; 3.29's causality is `Causality.isCausal_of_timeFunction` for `x⁰` on `(U, g)`, or
`IsCausalIso.isCausal_of_timeFunction` for `ρ + σ` on `(V, m̂)`.

## Hypothesis checklist

| ERS hypothesis | here |
|---|---|
| `Ψ : V → U` a diffeomorphism | ⚠ weakened: a homeomorphism `e : M ≃ₜ N` |
| `g`, `m̂` causally equivalent (`:372`) | ✓ carried: `IsCausalIso C D e`, the layer-3 input |
| Lorentzian, time-oriented, smooth | ⚠ weakened: topological spacetimes, any causality |
| second countable, Hausdorff | ⚠ weakened: not used |
| 3.29: `x⁰`, `±(ρ+σ)` "global time functions" | ⚠ reading: a function strictly increasing along `≤_M` (Lorentzian sense), not ETT's `defi:fonction_temps`, which does not suffice (`exists_isTimeFunction_not_isCausal`); continuity and `ℝ` unused |
| 3.29: "stably causal" | ⚠ reading: concluded `IsCausal`; ETT defines no stable causality (`ETT.tex:1017–1018`) |
| 3.31, 3.39: properties reading only `≤_M` | ⚠ weakened: `LeTopIso` (`≤_M` carried onto `≤_N`) suffices for causal, GH, strongly causal, tarentin, acausal |

## SCOPE (disclosed)

* **The notion.** `IsCausalIso C D e` is the target's: `e` and `e⁻¹` strong morphisms. For a
  homeomorphism this is equivalent to the relational form on every open set (`isCausalIso_iff`),
  to `D = C.transport e`, and to an isomorphism of the category `Spacetime`. Cauchy surfaces,
  arc-connectedness, push-up and the time functions read `≤_U`, `≪_U` on every open `U`, so no
  weaker hypothesis serves the whole list; the properties reading `≤_M` alone are proved under
  `LeTopIso`, strictly weaker (`timelikeLine_leTopIso_lightlikeLine`,
  `not_isCausalIso_timelikeLine_lightlikeLine`).
* **Reuse.** Inextensibility is transported by `IsEMorphismOn.inextensible_iff_comp`
  (`Causal.CauchyExtension`) through `IsCausalIso.isEMorphism`. `IsEMorphism.isCauchySurface_image`
  is not used: it asks `N` causal and Hausdorff, which the transport does not need.
* **Not done.** `K^±` and `OneSidedBoundary` (pure topology) are not transported. The named
  wrapper `Causality.HasTimeFunction.isCausal` is in `Causal.CurvesExtend` (T-abs-hoist-time-function);
  `isCausal_of_exists_timeFunction` here takes its body verbatim.
* **`ChartIso`.** `IsCausalIso` is kept as the target's notion; it is `ChartIso` for a chart
  defined on all of `M` (`isCausalIso_iff_chartIso`), and `Causality.transport e` is
  `Causality.chartTransport` along `e⁻¹` (`chartTransport_toOpenPartialHomeomorph`). The transports
  here are proved directly; `curveOn_comp` overlaps `ChartIso.curveOn_symm`
  (`Causal.Remarks.MassiveManifold`, which reaches a model). 3.39's Cauchy surfaces "of constant
  `x⁰`" need a *Cauchy* time function (`IsCauchyTimeFunction.isCauchySurface`, `Causal.Geroch`);
  `isCauchyTimeFunction_comp_iff` carries one across `Ψ`.
* **Non-vacuity.** Translations of the timelike line are causal isomorphisms
  (`timelikeLine_isCausalIso_addRight`); the identity is one for every causality.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Function Relation

universe u v w

variable {M : Type u} {N : Type v} {P : Type w}
  [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]

/-! ### Open sets along a homeomorphism -/

section OpensCongr

variable (e : M ≃ₜ N)

/-- The open set `e.opensCongr U` is the image `e(U)`. -/
theorem coe_opensCongr (U : Opens M) : (e.opensCongr U : Set N) = e '' U := by
  rw [e.image_eq_preimage_symm]; rfl

theorem mem_opensCongr {U : Opens M} {x : M} : e x ∈ e.opensCongr U ↔ x ∈ U := by
  rw [← SetLike.mem_coe, coe_opensCongr, e.injective.mem_set_image]; rfl

theorem opensCongr_top : e.opensCongr ⊤ = ⊤ := e.opensCongr.map_top

theorem symm_opensCongr_opensCongr (U : Opens M) : e.symm.opensCongr (e.opensCongr U) = U := by
  rw [← Homeomorph.opensCongr_symm]; exact e.opensCongr.symm_apply_apply U

theorem opensCongr_symm_opensCongr (V : Opens N) : e.opensCongr (e.symm.opensCongr V) = V := by
  rw [← Homeomorph.opensCongr_symm]; exact e.opensCongr.apply_symm_apply V

theorem homeomorph_symm_image_image (S : Set M) : e.symm '' (e '' S) = S := by
  rw [e.image_symm, e.preimage_image]

/-- **Curves are carried by a homeomorphism** which carries the relations: a curve for `r` in
`W` is mapped to a curve for `r'` in `e(W)`. -/
theorem curveOn_comp {r : Opens M → M → M → Prop} {r' : Opens N → N → N → Prop}
    (hr : ∀ U x y, r U x y → r' (e.opensCongr U) (e x) (e y)) {W : Opens M} {c : ℝ → M}
    {a b : ℝ} (hc : CurveOn r W c a b) : CurveOn r' (e.opensCongr W) (e ∘ c) a b where
  mem t ht := (mem_opensCongr e).2 (hc.mem t ht)
  rel t ht N' hN' htN' := by
    have hN : e.symm.opensCongr N' ≤ W := by
      have := e.symm.opensCongr.monotone hN'
      rwa [symm_opensCongr_opensCongr] at this
    have htN : c t ∈ e.symm.opensCongr N' := by
      rw [← mem_opensCongr e, opensCongr_symm_opensCongr]; exact htN'
    obtain ⟨l, u, hl, hu, hrel⟩ := hc.rel t ht _ hN htN
    refine ⟨l, u, hl, hu, fun s hs s' hs' h1 h2 h3 => ?_⟩
    have := hr _ _ _ (hrel s hs s' hs' h1 h2 h3)
    rwa [opensCongr_symm_opensCongr] at this

end OpensCongr

/-! ### Causal isomorphisms -/

/-- **A causal isomorphism** `(M, C) → (N, D)`: a homeomorphism `e` such that `e` and `e⁻¹` are
strong morphisms (DEC-10), i.e. an isomorphism of `def:category_topological_spacetimes`
(`isCausalIso_iff_nonempty_iso`). Equivalently `≤_U` and `≪_U` correspond to `≤_{e(U)}` and
`≪_{e(U)}` on every open `U` (`isCausalIso_iff`); equivalently `D` is the transport of `C`
(`isCausalIso_iff_eq_transport`). It is the strict library's `ChartIso` (`Causal.GXStructure`) for
a chart defined on all of `M` (`isCausalIso_iff_chartIso`), and `Causality.transport` is
`Causality.chartTransport` along the inverse (`chartTransport_toOpenPartialHomeomorph`). -/
structure IsCausalIso (C : Causality M) (D : Causality N) (e : M ≃ₜ N) : Prop where
  strong : StrongMorphism C D e
  strong_symm : StrongMorphism D C e.symm

/-- The causality `C` transported along the homeomorphism `e`: `a ≤_V b` iff
`e⁻¹ a ≤_{e⁻¹(V)} e⁻¹ b`, and likewise for `≪`. -/
def Causality.transport (C : Causality M) (e : M ≃ₜ N) : Causality N where
  le V a b := C.le (e.symm.opensCongr V) (e.symm a) (e.symm b)
  lt V a b := C.lt (e.symm.opensCongr V) (e.symm a) (e.symm b)
  le_mem_left h := (mem_opensCongr e.symm).1 (C.le_mem_left h)
  le_mem_right h := (mem_opensCongr e.symm).1 (C.le_mem_right h)
  lt_mem_left h := (mem_opensCongr e.symm).1 (C.lt_mem_left h)
  lt_mem_right h := (mem_opensCongr e.symm).1 (C.lt_mem_right h)
  le_refl hx := C.le_refl ((mem_opensCongr e.symm).2 hx)
  le_trans h₁ h₂ := C.le_trans h₁ h₂
  lt_trans h₁ h₂ := C.lt_trans h₁ h₂
  le_mono h _ _ h' := C.le_mono (e.symm.opensCongr.monotone h) h'
  lt_mono h _ _ h' := C.lt_mono (e.symm.opensCongr.monotone h) h'
  le_of_lt h := C.le_of_lt h
  isOpen_lt_right _ a := (C.isOpen_lt_right _ (e.symm a)).preimage e.symm.continuous
  isOpen_lt_left _ a := (C.isOpen_lt_left _ (e.symm a)).preimage e.symm.continuous

variable {C : Causality M} {D : Causality N} {E : Causality P} {e : M ≃ₜ N}

/-- **The relational form**: a homeomorphism is a causal isomorphism iff `≤_U`, `≪_U` correspond
to `≤_{e(U)}`, `≪_{e(U)}` on every open `U`. -/
theorem isCausalIso_iff : IsCausalIso C D e ↔
    ∀ (U : Opens M) (x y : M), (C.le U x y ↔ D.le (e.opensCongr U) (e x) (e y)) ∧
      (C.lt U x y ↔ D.lt (e.opensCongr U) (e x) (e y)) := by
  have hmaps : ∀ U : Opens M, MapsTo e.symm (e.opensCongr U) U := fun U z hz =>
    (mem_opensCongr e).1 (by rw [e.apply_symm_apply]; exact hz)
  constructor
  · intro h U x y
    refine ⟨⟨fun hxy => h.strong.le_of_mapsTo (fun z hz => (mem_opensCongr e).2 hz) hxy,
      fun hxy => ?_⟩, ⟨fun hxy => h.strong.lt_of_mapsTo (fun z hz => (mem_opensCongr e).2 hz) hxy,
      fun hxy => ?_⟩⟩
    · simpa using h.strong_symm.le_of_mapsTo (hmaps U) hxy
    · simpa using h.strong_symm.lt_of_mapsTo (hmaps U) hxy
  · intro H
    have himage : ∀ (U : Opens N) (V : Opens M), (V : Set M) = e ⁻¹' U → e.opensCongr V = U :=
      fun U V hV => SetLike.coe_injective (by rw [coe_opensCongr, hV, e.image_preimage])
    have himage' : ∀ (U : Opens M) (V : Opens N), (V : Set N) = e.symm ⁻¹' U →
        e.opensCongr U = V :=
      fun U V hV => SetLike.coe_injective (by rw [coe_opensCongr, hV, e.image_eq_preimage_symm])
    refine ⟨⟨e.continuous, e.isOpenMap, fun U V hV x y hxy => ?_, fun U V hV x y hxy => ?_⟩,
      ⟨e.symm.continuous, e.symm.isOpenMap, fun U V hV a b hab => ?_, fun U V hV a b hab => ?_⟩⟩
    · rw [← himage U V hV]; exact (H V x y).1.1 hxy
    · rw [← himage U V hV]; exact (H V x y).2.1 hxy
    · refine (H U (e.symm a) (e.symm b)).1.2 ?_
      rw [himage' U V hV, e.apply_symm_apply, e.apply_symm_apply]; exact hab
    · refine (H U (e.symm a) (e.symm b)).2.2 ?_
      rw [himage' U V hV, e.apply_symm_apply, e.apply_symm_apply]; exact hab

namespace IsCausalIso

theorem le_iff (h : IsCausalIso C D e) {U : Opens M} {x y : M} :
    C.le U x y ↔ D.le (e.opensCongr U) (e x) (e y) :=
  (isCausalIso_iff.1 h U x y).1

theorem lt_iff (h : IsCausalIso C D e) {U : Opens M} {x y : M} :
    C.lt U x y ↔ D.lt (e.opensCongr U) (e x) (e y) :=
  (isCausalIso_iff.1 h U x y).2

theorem le_top_iff (h : IsCausalIso C D e) {x y : M} : C.le ⊤ x y ↔ D.le ⊤ (e x) (e y) := by
  rw [h.le_iff, opensCongr_top]

theorem lt_top_iff (h : IsCausalIso C D e) {x y : M} : C.lt ⊤ x y ↔ D.lt ⊤ (e x) (e y) := by
  rw [h.lt_iff, opensCongr_top]

protected theorem refl (C : Causality M) : IsCausalIso C C (Homeomorph.refl M) :=
  ⟨StrongMorphism.id, StrongMorphism.id⟩

protected theorem symm (h : IsCausalIso C D e) : IsCausalIso D C e.symm :=
  ⟨h.strong_symm, by rw [Homeomorph.symm_symm]; exact h.strong⟩

protected theorem trans {f : N ≃ₜ P} (h : IsCausalIso C D e) (h' : IsCausalIso D E f) :
    IsCausalIso C E (e.trans f) :=
  ⟨h'.strong.comp h.strong, h.strong_symm.comp h'.strong_symm⟩

/-- Time reversal (kb/0002). -/
protected theorem dual (h : IsCausalIso C D e) : IsCausalIso C.dual D.dual e :=
  isCausalIso_iff.2 fun _ x y => ⟨h.le_iff (x := y) (y := x), h.lt_iff (x := y) (y := x)⟩

/-- A causal isomorphism is an abstract `𝕄≥0`-morphism (`Causal.CauchyExtension`). -/
theorem isEMorphism (h : IsCausalIso C D e) : IsEMorphism C D e :=
  isEMorphism_iff.2 ⟨h.strong, e.isLocalHomeomorph, fun _ => ⟨⊤, trivial, e.injective.injOn,
    fun V' _ U hU _ _ _ _ => by
      have hU' : U = e.opensCongr V' := SetLike.coe_injective (by rw [hU, coe_opensCongr])
      subst hU'
      exact ⟨h.le_iff, h.lt_iff⟩⟩⟩

/-- `D` is the transport of `C` along a causal isomorphism. -/
theorem eq_transport (h : IsCausalIso C D e) : D = C.transport e :=
  Causality.ext (by funext V a b; exact propext h.symm.le_iff)
    (by funext V a b; exact propext h.symm.lt_iff)

end IsCausalIso

/-- The transport makes the homeomorphism a causal isomorphism. -/
theorem isCausalIso_transport (C : Causality M) (e : M ≃ₜ N) :
    IsCausalIso C (C.transport e) e := by
  refine isCausalIso_iff.2 fun U x y => ⟨?_, ?_⟩
  · show _ ↔ C.le (e.symm.opensCongr (e.opensCongr U)) (e.symm (e x)) (e.symm (e y))
    rw [symm_opensCongr_opensCongr, e.symm_apply_apply, e.symm_apply_apply]
  · show _ ↔ C.lt (e.symm.opensCongr (e.opensCongr U)) (e.symm (e x)) (e.symm (e y))
    rw [symm_opensCongr_opensCongr, e.symm_apply_apply, e.symm_apply_apply]

/-- **ERS Lemma 3.27, its layer-1 content**: a homeomorphism is a causal isomorphism exactly when
the causality of the target is the transport of the causality of the source. -/
theorem isCausalIso_iff_eq_transport : IsCausalIso C D e ↔ D = C.transport e :=
  ⟨IsCausalIso.eq_transport, fun h => h ▸ isCausalIso_transport C e⟩

open CategoryTheory in
/-- The causal isomorphisms are the isomorphisms of `def:category_topological_spacetimes`. -/
theorem isCausalIso_iff_nonempty_iso (X Y : Spacetime.{u}) :
    (∃ e : X.carrier ≃ₜ Y.carrier, IsCausalIso X.causality Y.causality e) ↔ Nonempty (X ≅ Y) := by
  constructor
  · rintro ⟨e, h⟩
    exact ⟨⟨⟨e, h.strong⟩, ⟨e.symm, h.strong_symm⟩, Subtype.ext (funext e.symm_apply_apply),
      Subtype.ext (funext e.apply_symm_apply)⟩⟩
  · rintro ⟨f⟩
    let e : X.carrier ≃ₜ Y.carrier :=
      { toFun := f.hom.1
        invFun := f.inv.1
        left_inv := fun x => congrFun (congrArg Subtype.val f.hom_inv_id) x
        right_inv := fun y => congrFun (congrArg Subtype.val f.inv_hom_id) y
        continuous_toFun := f.hom.2.continuous
        continuous_invFun := f.inv.2.continuous }
    exact ⟨e, f.hom.2, f.inv.2⟩

/-! ### The bridge to `ChartIso`: a causal isomorphism is a global chart isomorphism -/

/-- The image of an open set by the chart of a homeomorphism is its image by the homeomorphism. -/
theorem chartImage_toOpenPartialHomeomorph (e : M ≃ₜ N) (U : Opens M) :
    chartImage e.toOpenPartialHomeomorph U = e.opensCongr U :=
  SetLike.coe_injective (by
    rw [coe_chartImage, coe_opensCongr, Homeomorph.toOpenPartialHomeomorph_source, univ_inter]
    rfl)

/-- **`IsCausalIso` is `ChartIso` (`Causal.GXStructure`) for a global homeomorphism**: the chart
`e`, defined on all of `M`, is an isomorphism of topological spacetimes. -/
theorem isCausalIso_iff_chartIso : IsCausalIso C D e ↔ ChartIso C D e.toOpenPartialHomeomorph := by
  rw [isCausalIso_iff]
  constructor
  · intro H U _ x _ y _
    rw [chartImage_toOpenPartialHomeomorph]
    exact H U x y
  · intro H U x y
    have H' := fun hx hy => H U (by simp [chartSource]) x hx y hy
    simp only [chartImage_toOpenPartialHomeomorph] at H'
    by_cases hx : x ∈ U
    · by_cases hy : y ∈ U
      · exact H' hx hy
      · have hy' : e y ∉ e.opensCongr U := fun h => hy ((mem_opensCongr e).1 h)
        exact ⟨⟨fun h => absurd (C.le_mem_right h) hy, fun h => absurd (D.le_mem_right h) hy'⟩,
          ⟨fun h => absurd (C.lt_mem_right h) hy, fun h => absurd (D.lt_mem_right h) hy'⟩⟩
    · have hx' : e x ∉ e.opensCongr U := fun h => hx ((mem_opensCongr e).1 h)
      exact ⟨⟨fun h => absurd (C.le_mem_left h) hx, fun h => absurd (D.le_mem_left h) hx'⟩,
        ⟨fun h => absurd (C.lt_mem_left h) hx, fun h => absurd (D.lt_mem_left h) hx'⟩⟩

/-- **`Causality.chartTransport` along the chart of a homeomorphism is `Causality.transport` along
its inverse**: pulling `D` back by `e` is pushing it forward by `e⁻¹`. -/
theorem chartTransport_toOpenPartialHomeomorph (D : Causality N) (e : M ≃ₜ N) :
    D.chartTransport e.toOpenPartialHomeomorph = D.transport e.symm :=
  (isCausalIso_iff_chartIso.2
    (D.chartTransport_chartIso e.toOpenPartialHomeomorph)).symm.eq_transport

/-! ### What reads only `≤_M`: a homeomorphism carrying `≤_M` onto `≤_N` -/

/-- `e` carries the causal relation of `M` onto that of `N` (`U = M` only). The properties which
read only `≤_M` (causal, causally compact, globally hyperbolic, strongly causal, tarentin,
acausal sets) are transported by this alone (kb/0007); a causal isomorphism has it
(`IsCausalIso.leTopIso`). -/
def LeTopIso (C : Causality M) (D : Causality N) (e : M ≃ₜ N) : Prop :=
  ∀ x y : M, C.le ⊤ x y ↔ D.le ⊤ (e x) (e y)

theorem IsCausalIso.leTopIso (h : IsCausalIso C D e) : LeTopIso C D e := fun _ _ => h.le_top_iff

namespace LeTopIso

variable (h : LeTopIso C D e)
include h

protected theorem symm : LeTopIso D C e.symm := fun a b => by
  rw [h (e.symm a) (e.symm b), e.apply_symm_apply, e.apply_symm_apply]

theorem diamond_image (p q : M) : D.diamond ⊤ (e p) (e q) = e '' C.diamond ⊤ p q := by
  ext z
  obtain ⟨w, rfl⟩ := e.surjective z
  rw [e.injective.mem_set_image, Causality.mem_diamond, Causality.mem_diamond, ← h, ← h]

theorem openDiamond_image (p q : M) :
    D.openDiamond ⊤ (e p) (e q) = e '' C.openDiamond ⊤ p q := by
  rw [Causality.openDiamond, Causality.openDiamond, h.diamond_image, e.image_interior]

/-- **Causality is invariant** (ERS `:375`; Lemmas 3.29, 3.31). -/
theorem isCausal_iff : C.IsCausal ↔ D.IsCausal := by
  refine ⟨fun hC a b hab hba => ?_, fun hD x y hxy hyx => ?_⟩
  · obtain ⟨x, rfl⟩ := e.surjective a
    obtain ⟨y, rfl⟩ := e.surjective b
    rw [hC ((h x y).2 hab) ((h y x).2 hba)]
  · exact e.injective (hD ((h x y).1 hxy) ((h y x).1 hyx))

theorem causallyCompact_iff : C.CausallyCompact ↔ D.CausallyCompact := by
  constructor
  · intro hC a b
    obtain ⟨x, rfl⟩ := e.surjective a
    obtain ⟨y, rfl⟩ := e.surjective b
    rw [h.diamond_image, e.isCompact_image]
    exact hC x y
  · intro hD x y
    rw [← e.isCompact_image, ← h.diamond_image]
    exact hD _ _

/-- **Global hyperbolicity is invariant** (ERS Lemmas 3.31, 3.39). -/
theorem globallyHyperbolic_iff : C.GloballyHyperbolic ↔ D.GloballyHyperbolic :=
  and_congr h.isCausal_iff h.causallyCompact_iff

theorem causallyConvexIn_image_iff {V : Set M} :
    D.CausallyConvexIn (e '' V) ⊤ ↔ C.CausallyConvexIn V ⊤ := by
  unfold Causality.CausallyConvexIn
  refine and_congr ⟨fun _ _ _ => trivial, fun _ _ _ => trivial⟩ ?_
  simp only [forall_mem_image, h.diamond_image, image_subset_image_iff e.injective]

theorem stronglyCausal (hC : C.StronglyCausal) : D.StronglyCausal := by
  intro a U hU
  obtain ⟨x, rfl⟩ := e.surjective a
  obtain ⟨V, hV, hVU, hconv⟩ :=
    hC x (e ⁻¹' U) (e.continuous.continuousAt.preimage_mem_nhds hU)
  exact ⟨e '' V, e.isOpenMap.image_mem_nhds hV, image_subset_iff.2 hVU,
    h.causallyConvexIn_image_iff.2 hconv⟩

theorem stronglyCausal_iff : C.StronglyCausal ↔ D.StronglyCausal :=
  ⟨h.stronglyCausal, h.symm.stronglyCausal⟩

theorem stronglyCausalOpen (hC : C.StronglyCausalOpen) : D.StronglyCausalOpen := by
  intro a U hU
  obtain ⟨x, rfl⟩ := e.surjective a
  obtain ⟨V, hxV, hVU, hconv⟩ :=
    hC x (e ⁻¹' U) (e.continuous.continuousAt.preimage_mem_nhds hU)
  refine ⟨e.opensCongr V, (mem_opensCongr e).2 hxV, ?_, ?_⟩
  · rw [coe_opensCongr]; exact image_subset_iff.2 hVU
  · rw [coe_opensCongr]; exact h.causallyConvexIn_image_iff.2 hconv

theorem stronglyCausalOpen_iff : C.StronglyCausalOpen ↔ D.StronglyCausalOpen :=
  ⟨h.stronglyCausalOpen, h.symm.stronglyCausalOpen⟩

theorem tarentin (hC : C.Tarentin) : D.Tarentin := by
  intro a U hU
  obtain ⟨x, rfl⟩ := e.surjective a
  obtain ⟨p, hp, q, hq, hx⟩ := hC x (e ⁻¹' U) (e.continuous.continuousAt.preimage_mem_nhds hU)
  refine ⟨e p, hp, e q, hq, ?_⟩
  rw [h.openDiamond_image]
  exact mem_image_of_mem e hx

theorem tarentin_iff : C.Tarentin ↔ D.Tarentin :=
  ⟨h.tarentin, h.symm.tarentin⟩

theorem isAcausal_image_iff {S : Set M} : D.IsAcausal (e '' S) ↔ C.IsAcausal S := by
  have h' : ∀ x y : M, D.le ⊤ (e x) (e y) ↔ C.le ⊤ x y := fun x y => (h x y).symm
  simp only [Causality.IsAcausal, forall_mem_image, h', e.injective.eq_iff]

/-- Strict increase along `≤` corresponds. -/
theorem strictMono_le_comp_iff {α : Type*} [Preorder α] {T : N → α} :
    (∀ x y, C.le ⊤ x y → x ≠ y → T (e x) < T (e y)) ↔
      ∀ a b, D.le ⊤ a b → a ≠ b → T a < T b := by
  constructor
  · intro H a b hab hne
    obtain ⟨x, rfl⟩ := e.surjective a
    obtain ⟨y, rfl⟩ := e.surjective b
    exact H x y ((h x y).2 hab) fun hxy => hne (by rw [hxy])
  · intro H x y hxy hne
    exact H (e x) (e y) ((h x y).1 hxy) (e.injective.ne hne)

/-- A continuous function strictly increasing along `≤` (the body of the ladder node
`time_function`, `Causality.HasTimeFunction`) exists on `M` iff on `N`. -/
theorem exists_timeFunction_iff :
    (∃ T : M → ℝ, Continuous T ∧ ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y) ↔
      ∃ T : N → ℝ, Continuous T ∧ ∀ a b, D.le ⊤ a b → a ≠ b → T a < T b := by
  constructor
  · rintro ⟨T, hTc, hT⟩
    refine ⟨T ∘ e.symm, hTc.comp e.symm.continuous, ?_⟩
    rw [← h.strictMono_le_comp_iff]
    simpa using hT
  · rintro ⟨T, hTc, hT⟩
    exact ⟨T ∘ e, hTc.comp e.continuous, h.strictMono_le_comp_iff.2 hT⟩

end LeTopIso

/-! ### Images of the causal sets -/

namespace IsCausalIso

variable (h : IsCausalIso C D e)
include h

theorem Jplus_image (U : Opens M) (A : Set M) :
    D.Jplus (e.opensCongr U) (e '' A) = e '' C.Jplus U A := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, hxy⟩
    refine ⟨e.symm y, ⟨x, hx, h.le_iff.2 ?_⟩, e.apply_symm_apply y⟩
    rw [e.apply_symm_apply]; exact hxy
  · rintro ⟨z, ⟨x, hx, hxz⟩, rfl⟩
    exact ⟨e x, mem_image_of_mem e hx, h.le_iff.1 hxz⟩

theorem Jminus_image (U : Opens M) (A : Set M) :
    D.Jminus (e.opensCongr U) (e '' A) = e '' C.Jminus U A :=
  h.dual.Jplus_image U A

theorem Iplus_image (U : Opens M) (A : Set M) :
    D.Iplus (e.opensCongr U) (e '' A) = e '' C.Iplus U A := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, hxy⟩
    refine ⟨e.symm y, ⟨x, hx, h.lt_iff.2 ?_⟩, e.apply_symm_apply y⟩
    rw [e.apply_symm_apply]; exact hxy
  · rintro ⟨z, ⟨x, hx, hxz⟩, rfl⟩
    exact ⟨e x, mem_image_of_mem e hx, h.lt_iff.1 hxz⟩

theorem Iminus_image (U : Opens M) (A : Set M) :
    D.Iminus (e.opensCongr U) (e '' A) = e '' C.Iminus U A :=
  h.dual.Iplus_image U A

theorem diamond_image (U : Opens M) (p q : M) :
    D.diamond (e.opensCongr U) (e p) (e q) = e '' C.diamond U p q := by
  rw [Causality.diamond, Causality.diamond, image_inter e.injective, ← h.Jminus_image,
    ← h.Jplus_image, image_singleton, image_singleton]

theorem openDiamond_image (U : Opens M) (p q : M) :
    D.openDiamond (e.opensCongr U) (e p) (e q) = e '' C.openDiamond U p q := by
  rw [Causality.openDiamond, Causality.openDiamond, h.diamond_image, e.image_interior]

theorem Zplus_image : D.Zplus = e '' C.Zplus := by
  ext a
  obtain ⟨x, rfl⟩ := e.surjective a
  have hI : D.Iplus ⊤ {e x} = e '' C.Iplus ⊤ {x} := by
    rw [← opensCongr_top e, ← image_singleton, h.Iplus_image]
  rw [e.injective.mem_set_image, Causality.mem_Zplus, Causality.mem_Zplus, hI]
  constructor
  · intro hD U hU
    obtain ⟨_, ⟨y, hy, rfl⟩, hyU⟩ := hD (e '' U) (e.isOpenMap.image_mem_nhds hU)
    exact ⟨y, hy, (e.injective.mem_set_image).1 hyU⟩
  · intro hC U hU
    obtain ⟨y, hy, hyU⟩ := hC (e ⁻¹' U) (e.continuous.continuousAt.preimage_mem_nhds hU)
    exact ⟨e y, mem_image_of_mem e hy, hyU⟩

theorem Zminus_image : D.Zminus = e '' C.Zminus :=
  h.dual.Zplus_image

/-! ### Causal, globally hyperbolic, strongly causal -/

/-- **Causality is invariant** (ERS `:375`; Lemmas 3.29, 3.31). -/
theorem isCausal_iff : C.IsCausal ↔ D.IsCausal := h.leTopIso.isCausal_iff

theorem causallyCompact_iff : C.CausallyCompact ↔ D.CausallyCompact :=
  h.leTopIso.causallyCompact_iff

/-- **Global hyperbolicity is invariant** (ERS Lemmas 3.31, 3.39). -/
theorem globallyHyperbolic_iff : C.GloballyHyperbolic ↔ D.GloballyHyperbolic :=
  h.leTopIso.globallyHyperbolic_iff

/-- Global hyperbolicity of an open set and of its image. -/
theorem globallyHyperbolicOn_iff {W : Opens M} :
    C.GloballyHyperbolicOn W ↔ D.GloballyHyperbolicOn (e.opensCongr W) := by
  refine and_congr ⟨fun hC a b hab hba => ?_, fun hD x y hxy hyx => ?_⟩ ⟨fun hC a b => ?_,
    fun hD x y => ?_⟩
  · obtain ⟨x, rfl⟩ := e.surjective a
    obtain ⟨y, rfl⟩ := e.surjective b
    rw [hC (h.le_iff.2 hab) (h.le_iff.2 hba)]
  · exact e.injective (hD (h.le_iff.1 hxy) (h.le_iff.1 hyx))
  · obtain ⟨x, rfl⟩ := e.surjective a
    obtain ⟨y, rfl⟩ := e.surjective b
    rw [h.diamond_image, e.isCompact_image]
    exact hC x y
  · rw [← e.isCompact_image, ← h.diamond_image]
    exact hD _ _

theorem causallyConvexIn_image_iff {V : Set M} {U : Opens M} :
    D.CausallyConvexIn (e '' V) (e.opensCongr U) ↔ C.CausallyConvexIn V U := by
  unfold Causality.CausallyConvexIn
  rw [coe_opensCongr, image_subset_image_iff e.injective]
  refine and_congr Iff.rfl ?_
  simp only [forall_mem_image, h.diamond_image, image_subset_image_iff e.injective]

theorem stronglyCausal_iff : C.StronglyCausal ↔ D.StronglyCausal :=
  h.leTopIso.stronglyCausal_iff

theorem stronglyCausalOpen_iff : C.StronglyCausalOpen ↔ D.StronglyCausalOpen :=
  h.leTopIso.stronglyCausalOpen_iff

theorem isAcausal_image_iff {S : Set M} : D.IsAcausal (e '' S) ↔ C.IsAcausal S :=
  h.leTopIso.isAcausal_image_iff

/-! ### The ladder -/

theorem tarentin_iff : C.Tarentin ↔ D.Tarentin := h.leTopIso.tarentin_iff

theorem causallyPlain (hC : C.CausallyPlain) : D.CausallyPlain := by
  intro V B
  obtain ⟨U, rfl⟩ := e.opensCongr.surjective V
  obtain ⟨A, rfl⟩ : ∃ A, e '' A = B := ⟨e ⁻¹' B, e.image_preimage B⟩
  rw [h.Jplus_image, h.Iplus_image, h.Jminus_image, h.Iminus_image, ← e.image_interior,
    ← e.image_closure, ← e.image_interior, ← e.image_closure]
  exact ⟨image_mono (hC U A).1, image_mono (hC U A).2⟩

theorem causallyPlain_iff : C.CausallyPlain ↔ D.CausallyPlain :=
  ⟨h.causallyPlain, h.symm.causallyPlain⟩

theorem pushUpOn {W : Opens M} (hC : C.PushUpOn W) : D.PushUpOn (e.opensCongr W) := by
  intro V hV a b c
  obtain ⟨U, rfl⟩ := e.opensCongr.surjective V
  obtain ⟨x, rfl⟩ := e.surjective a
  obtain ⟨y, rfl⟩ := e.surjective b
  obtain ⟨z, rfl⟩ := e.surjective c
  have hUW : U ≤ W := e.opensCongr.le_iff_le.1 hV
  have H := @hC U hUW x y z
  simpa only [h.le_iff, h.lt_iff] using H

theorem pushUpOn_iff {W : Opens M} : C.PushUpOn W ↔ D.PushUpOn (e.opensCongr W) :=
  ⟨h.pushUpOn, fun hD => by
    have := h.symm.pushUpOn hD; rwa [symm_opensCongr_opensCongr] at this⟩

theorem pushUp_iff : C.PushUp ↔ D.PushUp := by
  rw [← Causality.pushUpOn_top, ← Causality.pushUpOn_top, h.pushUpOn_iff, opensCongr_top]

theorem causallyOpenFutureOn_iff {W : Opens M} :
    C.CausallyOpenFutureOn W ↔ D.CausallyOpenFutureOn (e.opensCongr W) := by
  constructor
  · intro hC U' V' hU' hV'
    obtain ⟨U, rfl⟩ := e.opensCongr.surjective U'
    obtain ⟨V, rfl⟩ := e.opensCongr.surjective V'
    rw [coe_opensCongr, h.Jplus_image, e.isOpen_image]
    exact hC U V (e.opensCongr.le_iff_le.1 hU') (e.opensCongr.le_iff_le.1 hV')
  · intro hD U V hU hV
    have := hD (e.opensCongr U) (e.opensCongr V) (e.opensCongr.le_iff_le.2 hU)
      (e.opensCongr.le_iff_le.2 hV)
    rwa [coe_opensCongr, h.Jplus_image, e.isOpen_image] at this

theorem causallyOpenFuture_iff : C.CausallyOpenFuture ↔ D.CausallyOpenFuture := by
  rw [← Causality.causallyOpenFutureOn_top, ← Causality.causallyOpenFutureOn_top,
    h.causallyOpenFutureOn_iff, opensCongr_top]

theorem causallyOpen_iff : C.CausallyOpen ↔ D.CausallyOpen :=
  and_congr h.causallyOpenFuture_iff h.dual.causallyOpenFuture_iff

theorem absolutelyMinimalOn {W : Opens M} (hC : C.AbsolutelyMinimalOn W) :
    D.AbsolutelyMinimalOn (e.opensCongr W) := by
  intro S' hS' V' hV' a b
  obtain ⟨V, rfl⟩ := e.opensCongr.surjective V'
  obtain ⟨x, rfl⟩ := e.surjective a
  obtain ⟨y, rfl⟩ := e.surjective b
  have hVW : V ≤ W := e.opensCongr.le_iff_le.1 hV'
  have hS : ∀ z ∈ W, ∃ O ∈ e.symm.opensCongr '' S', z ∈ O := fun z hz => by
    obtain ⟨O', hO', hzO'⟩ := hS' (e z) ((mem_opensCongr e).2 hz)
    refine ⟨e.symm.opensCongr O', mem_image_of_mem _ hO', ?_⟩
    rw [← mem_opensCongr e, opensCongr_symm_opensCongr]; exact hzO'
  have hinf : ∀ O' : Opens N,
      e.opensCongr (V ⊓ e.symm.opensCongr O') = e.opensCongr V ⊓ O' := fun O' => by
    rw [OrderIso.map_inf, opensCongr_symm_opensCongr]
  refine ⟨fun hxy => ?_, fun hxy => ?_⟩
  · refine TransGen.lift e (fun p q hpq => ?_) ((hC _ hS V hVW x y).1 (h.le_iff.2 hxy))
    obtain ⟨_, ⟨O', hO', rfl⟩, hpq⟩ := hpq
    exact ⟨O', hO', by rw [← hinf]; exact h.le_iff.1 hpq⟩
  · refine TransGen.lift e (fun p q hpq => ?_) ((hC _ hS V hVW x y).2 (h.lt_iff.2 hxy))
    obtain ⟨_, ⟨O', hO', rfl⟩, hpq⟩ := hpq
    exact ⟨O', hO', by rw [← hinf]; exact h.lt_iff.1 hpq⟩

theorem absolutelyMinimalOn_iff {W : Opens M} :
    C.AbsolutelyMinimalOn W ↔ D.AbsolutelyMinimalOn (e.opensCongr W) :=
  ⟨h.absolutelyMinimalOn, fun hD => by
    have := h.symm.absolutelyMinimalOn hD; rwa [symm_opensCongr_opensCongr] at this⟩

theorem absolutelyMinimal_iff : C.AbsolutelyMinimal ↔ D.AbsolutelyMinimal := by
  rw [Precausality.absolutelyMinimal_iff, Precausality.absolutelyMinimal_iff,
    h.absolutelyMinimalOn_iff, opensCongr_top]

theorem causalCurveOn_iff {W : Opens M} {c : ℝ → M} {a b : ℝ} :
    C.CausalCurveOn W c a b ↔ D.CausalCurveOn (e.opensCongr W) (e ∘ c) a b := by
  refine ⟨fun hc => curveOn_comp e (r := C.le) (r' := D.le) (fun _ _ _ => h.le_iff.1) hc,
    fun hd => ?_⟩
  have := curveOn_comp e.symm (r := D.le) (r' := C.le) (fun _ _ _ => h.symm.le_iff.1) hd
  have hc : e.symm ∘ (e ∘ c) = c := funext fun t => e.symm_apply_apply (c t)
  rwa [symm_opensCongr_opensCongr, hc] at this

theorem chronalCurveOn_iff {W : Opens M} {c : ℝ → M} {a b : ℝ} :
    C.ChronalCurveOn W c a b ↔ D.ChronalCurveOn (e.opensCongr W) (e ∘ c) a b := by
  refine ⟨fun hc => curveOn_comp e (r := C.lt) (r' := D.lt) (fun _ _ _ => h.lt_iff.1) hc,
    fun hd => ?_⟩
  have := curveOn_comp e.symm (r := D.lt) (r' := C.lt) (fun _ _ _ => h.symm.lt_iff.1) hd
  have hc : e.symm ∘ (e ∘ c) = c := funext fun t => e.symm_apply_apply (c t)
  rwa [symm_opensCongr_opensCongr, hc] at this

theorem causallyArcConnectedOn {W : Opens M} (hC : C.CausallyArcConnectedOn W) :
    D.CausallyArcConnectedOn (e.opensCongr W) := by
  rw [Causality.causallyArcConnectedOn_iff] at hC ⊢
  intro V hV a b
  obtain ⟨U, rfl⟩ := e.opensCongr.surjective V
  obtain ⟨x, rfl⟩ := e.surjective a
  obtain ⟨y, rfl⟩ := e.surjective b
  have hUW : U ≤ W := e.opensCongr.le_iff_le.1 hV
  refine ⟨fun hxy => ?_, fun hxy => ?_⟩
  · obtain ⟨c, hc, rfl, rfl⟩ := (hC U hUW x y).1 (h.le_iff.2 hxy)
    exact ⟨e ∘ c, h.causalCurveOn_iff.1 hc, rfl, rfl⟩
  · obtain ⟨c, hc, rfl, rfl⟩ := (hC U hUW x y).2 (h.lt_iff.2 hxy)
    exact ⟨e ∘ c, h.chronalCurveOn_iff.1 hc, rfl, rfl⟩

theorem causallyArcConnectedOn_iff {W : Opens M} :
    C.CausallyArcConnectedOn W ↔ D.CausallyArcConnectedOn (e.opensCongr W) :=
  ⟨h.causallyArcConnectedOn, fun hD => by
    have := h.symm.causallyArcConnectedOn hD; rwa [symm_opensCongr_opensCongr] at this⟩

theorem causallyArcConnected_iff : C.CausallyArcConnected ↔ D.CausallyArcConnected := by
  unfold Causality.CausallyArcConnected
  rw [h.causallyArcConnectedOn_iff, opensCongr_top]

theorem locallyCausallyArcConnected (hC : C.LocallyCausallyArcConnected) :
    D.LocallyCausallyArcConnected := by
  intro a U hU
  obtain ⟨x, rfl⟩ := e.surjective a
  obtain ⟨V, hxV, hVU, hV⟩ :=
    hC x (e ⁻¹' U) (e.continuous.continuousAt.preimage_mem_nhds hU)
  refine ⟨e.opensCongr V, (mem_opensCongr e).2 hxV, ?_, h.causallyArcConnectedOn hV⟩
  rw [coe_opensCongr]; exact image_subset_iff.2 hVU

theorem locallyCausallyArcConnected_iff :
    C.LocallyCausallyArcConnected ↔ D.LocallyCausallyArcConnected :=
  ⟨h.locallyCausallyArcConnected, h.symm.locallyCausallyArcConnected⟩

theorem locallyPushUp (hC : C.LocallyPushUp) : D.LocallyPushUp := by
  intro a
  obtain ⟨x, rfl⟩ := e.surjective a
  obtain ⟨W, hx, hW⟩ := hC x
  exact ⟨e.opensCongr W, (mem_opensCongr e).2 hx, h.pushUpOn hW⟩

theorem locallyPushUp_iff : C.LocallyPushUp ↔ D.LocallyPushUp :=
  ⟨h.locallyPushUp, h.symm.locallyPushUp⟩

theorem locallyCausallyOpenFuture (hC : C.LocallyCausallyOpenFuture) :
    D.LocallyCausallyOpenFuture := by
  intro a
  obtain ⟨x, rfl⟩ := e.surjective a
  obtain ⟨W, hx, hW⟩ := hC x
  exact ⟨e.opensCongr W, (mem_opensCongr e).2 hx, h.causallyOpenFutureOn_iff.1 hW⟩

theorem locallyCausallyOpenFuture_iff :
    C.LocallyCausallyOpenFuture ↔ D.LocallyCausallyOpenFuture :=
  ⟨h.locallyCausallyOpenFuture, h.symm.locallyCausallyOpenFuture⟩

theorem locallyCausallyOpen_iff : C.LocallyCausallyOpen ↔ D.LocallyCausallyOpen :=
  and_congr h.locallyCausallyOpenFuture_iff h.dual.locallyCausallyOpenFuture_iff

theorem chronalPastNeighbours (hC : C.ChronalPastNeighbours) : D.ChronalPastNeighbours := by
  intro V a ha
  obtain ⟨U, rfl⟩ := e.opensCongr.surjective V
  obtain ⟨x, rfl⟩ := e.surjective a
  obtain ⟨p, hp, hpx⟩ := hC U x ((mem_opensCongr e).1 ha)
  exact ⟨e p, (mem_opensCongr e).2 hp, h.lt_iff.1 hpx⟩

theorem chronalPastNeighbours_iff : C.ChronalPastNeighbours ↔ D.ChronalPastNeighbours :=
  ⟨h.chronalPastNeighbours, h.symm.chronalPastNeighbours⟩

theorem chronalNeighbours_iff : C.ChronalNeighbours ↔ D.ChronalNeighbours :=
  and_congr h.chronalPastNeighbours_iff h.dual.chronalPastNeighbours_iff

theorem noPastEndpoint_iff : C.NoPastEndpoint ↔ D.NoPastEndpoint := by
  have key : ∀ x : M, D.Jminus ⊤ {e x} ≠ {e x} ↔ C.Jminus ⊤ {x} ≠ {x} := fun x => by
    rw [← opensCongr_top e, ← image_singleton (f := e) (a := x), h.Jminus_image, Ne, Ne,
      (image_injective.2 e.injective).eq_iff]
  refine ⟨fun hC a => ?_, fun hD x => (key x).1 (hD (e x))⟩
  obtain ⟨x, rfl⟩ := e.surjective a
  exact (key x).2 (hC x)

theorem noCausalEndpoint_iff : C.NoCausalEndpoint ↔ D.NoCausalEndpoint :=
  and_congr h.noPastEndpoint_iff h.dual.noPastEndpoint_iff

/-! ### Inextensible curves and Cauchy surfaces -/

theorem causalCurveIn_iff {W : Opens M} {I : Set ℝ} {c : ℝ → M} :
    C.CausalCurveIn W I c ↔ D.CausalCurveIn (e.opensCongr W) I (e ∘ c) :=
  ⟨fun hc => ⟨hc.nonempty, hc.ordConnected, fun a ha b hb =>
      h.causalCurveOn_iff.1 (hc.curve a ha b hb)⟩,
    fun hd => ⟨hd.nonempty, hd.ordConnected, fun a ha b hb =>
      h.causalCurveOn_iff.2 (hd.curve a ha b hb)⟩⟩

theorem inextensible_iff {W : Opens M} {I : Set ℝ} {c : ℝ → M} :
    C.Inextensible W I c ↔ D.Inextensible (e.opensCongr W) I (e ∘ c) := by
  have hg : LeftInvOn e.symm e ((⊤ : Opens M) : Set M) := fun x _ => e.symm_apply_apply x
  constructor
  · intro hc
    exact (IsEMorphismOn.inextensible_iff_comp h.isEMorphism e.injective.injOn hg le_top
      (coe_opensCongr e W) fun t ht => hc.1.mem ht).1 hc
  · intro hd
    exact (IsEMorphismOn.inextensible_iff_comp h.isEMorphism e.injective.injOn hg le_top
      (coe_opensCongr e W) fun t ht => (mem_opensCongr e).1 (hd.1.mem ht)).2 hd

theorem curvesExtend (hC : C.CurvesExtend) : D.CurvesExtend := by
  intro c a b hab hc
  have hc' : C.CausalCurveOn ⊤ (e.symm ∘ c) a b := by
    have := h.symm.causalCurveOn_iff.1 hc
    rwa [opensCongr_top] at this
  obtain ⟨I, c', hI, hsub⟩ := hC _ a b hab hc'
  refine ⟨I, e ∘ c', by simpa only [opensCongr_top] using h.inextensible_iff.1 hI, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨s, hs, hs'⟩ := hsub ⟨t, ht, rfl⟩
  refine ⟨s, hs, ?_⟩
  simp only [comp_apply] at hs' ⊢
  rw [hs', e.apply_symm_apply]

theorem curvesExtend_iff : C.CurvesExtend ↔ D.CurvesExtend :=
  ⟨h.curvesExtend, h.symm.curvesExtend⟩

/-- **Cauchy surfaces are invariant**: `S` is a Cauchy surface of `W` iff `e(S)` is one of
`e(W)`. -/
theorem isCauchySurfaceOn_image {W : Opens M} {S : Set M} (hS : C.IsCauchySurfaceOn W S) :
    D.IsCauchySurfaceOn (e.opensCongr W) (e '' S) := by
  intro I d hd
  have hcomp : e ∘ (e.symm ∘ d) = d := funext fun t => e.apply_symm_apply (d t)
  have hc : C.Inextensible W I (e.symm ∘ d) := h.inextensible_iff.2 (by rw [hcomp]; exact hd)
  obtain ⟨x, ⟨⟨t, ht, rfl⟩, hxS⟩, huniq⟩ := hS I _ hc
  refine ⟨d t, ⟨⟨t, ht, rfl⟩, ⟨_, hxS, e.apply_symm_apply (d t)⟩⟩, ?_⟩
  rintro y ⟨⟨t', ht', rfl⟩, ⟨s, hs, hse⟩⟩
  have hmem : (e.symm ∘ d) t' ∈ S := by
    simp only [comp_apply]; rw [← hse, e.symm_apply_apply]; exact hs
  have := huniq _ ⟨⟨t', ht', rfl⟩, hmem⟩
  simpa using congrArg e this

/-- **Cauchy surfaces are invariant**: `S` is a Cauchy surface of `W` iff `e(S)` is one of
`e(W)`. -/
theorem isCauchySurfaceOn_image_iff {W : Opens M} {S : Set M} :
    C.IsCauchySurfaceOn W S ↔ D.IsCauchySurfaceOn (e.opensCongr W) (e '' S) :=
  ⟨h.isCauchySurfaceOn_image, fun hD => by
    have := h.symm.isCauchySurfaceOn_image hD
    rwa [symm_opensCongr_opensCongr, homeomorph_symm_image_image] at this⟩

theorem isCauchySurface_image_iff {S : Set M} :
    C.IsCauchySurface S ↔ D.IsCauchySurface (e '' S) := by
  unfold Causality.IsCauchySurface
  rw [h.isCauchySurfaceOn_image_iff, opensCongr_top]

/-- The preimage form, as ERS write it: `S` is a Cauchy surface of `N` iff `e⁻¹(S)` is one
of `M`. -/
theorem isCauchySurface_preimage_iff {S : Set N} :
    D.IsCauchySurface S ↔ C.IsCauchySurface (e ⁻¹' S) := by
  rw [h.symm.isCauchySurface_image_iff, e.image_symm]

/-- **ERS Lemma 3.31, layer 1**: `(N, D)` is globally hyperbolic with Cauchy surface `S` iff
`(M, C)` is globally hyperbolic with Cauchy surface `e⁻¹(S)`. -/
theorem globallyHyperbolic_and_isCauchySurface_iff (S : Set N) :
    D.GloballyHyperbolic ∧ D.IsCauchySurface S ↔
      C.GloballyHyperbolic ∧ C.IsCauchySurface (e ⁻¹' S) :=
  and_congr h.globallyHyperbolic_iff.symm h.isCauchySurface_preimage_iff

/-! ### Time functions -/

/-- **Time functions (`defi:fonction_temps`) correspond**: `T` is a time function of `N` iff
`T ∘ e` is one of `M`. -/
theorem isTimeFunction_comp_iff {T : N → ℝ} :
    C.IsTimeFunction (T ∘ e) ↔ D.IsTimeFunction T := by
  refine ⟨fun hT => ?_, fun hT => hT.comp h.strong⟩
  have := hT.comp h.strong_symm
  have hTe : (T ∘ e) ∘ e.symm = T := funext fun a => by simp
  rwa [hTe] at this

/-- The same for the alternative reading (b) of `defi:fonction_temps` (`IsTimeFunctionOrder`). -/
theorem isTimeFunctionOrder_comp_iff {T : N → ℝ} :
    C.IsTimeFunctionOrder (T ∘ e) ↔ D.IsTimeFunctionOrder T := by
  refine ⟨fun hT => ?_, fun hT => StrongMorphism.comp hT h.strong⟩
  have := StrongMorphism.comp hT h.strong_symm
  have hTe : (T ∘ e) ∘ e.symm = T := funext fun a => by simp
  rwa [hTe] at this

theorem isCauchyTimeFunction_comp_iff {T : N → ℝ} :
    C.IsCauchyTimeFunction (T ∘ e) ↔ D.IsCauchyTimeFunction T := by
  refine ⟨fun hT => ⟨h.isTimeFunction_comp_iff.1 hT.1, fun c hc => ?_⟩,
    fun hT => ⟨h.isTimeFunction_comp_iff.2 hT.1, fun c hc => ?_⟩⟩
  · have hc' : C.Inextensible ⊤ univ (e.symm ∘ c) := by
      have := h.symm.inextensible_iff.1 hc
      rwa [opensCongr_top] at this
    have := hT.2 _ hc'
    have hTe : (T ∘ e) ∘ (e.symm ∘ c) = T ∘ c := funext fun t => by simp
    rwa [hTe] at this
  · have hc' : D.Inextensible ⊤ univ (e ∘ c) := by
      have := h.inextensible_iff.1 hc
      rwa [opensCongr_top] at this
    exact hT.2 _ hc'

theorem strictMono_le_comp_iff {α : Type*} [Preorder α] {T : N → α} :
    (∀ x y, C.le ⊤ x y → x ≠ y → T (e x) < T (e y)) ↔
      ∀ a b, D.le ⊤ a b → a ≠ b → T a < T b :=
  h.leTopIso.strictMono_le_comp_iff

theorem exists_timeFunction_iff :
    (∃ T : M → ℝ, Continuous T ∧ ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y) ↔
      ∃ T : N → ℝ, Continuous T ∧ ∀ a b, D.le ⊤ a b → a ≠ b → T a < T b :=
  h.leTopIso.exists_timeFunction_iff

end IsCausalIso

/-! ### A function strictly increasing along `≤` makes the causality causal -/

namespace Causality

/-- **A function strictly increasing along `≤` makes the causality causal** (ERS Lemma 3.29's
"stably causal", read as the existence of such a function). Neither continuity nor `ℝ` is
used. -/
theorem isCausal_of_timeFunction {C : Causality M} {α : Type*} [Preorder α] {T : M → α}
    (hT : ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y) : C.IsCausal := by
  intro x y hxy hyx
  by_contra hne
  exact lt_asymm (hT x y hxy hne) (hT y x hyx (Ne.symm hne))

/-- The same, with the hypothesis of the ladder node `time_function` (`HasTimeFunction`'s body). -/
theorem isCausal_of_exists_timeFunction {C : Causality M}
    (h : ∃ T : M → ℝ, Continuous T ∧ ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y) : C.IsCausal :=
  let ⟨_, _, hT⟩ := h
  isCausal_of_timeFunction hT

end Causality

/-- **ERS Lemma 3.29, layer 1**: a function on the source strictly increasing along `≤` (ERS:
`ρ + σ` on `(V, m̂)`) makes the target causal. -/
theorem IsCausalIso.isCausal_of_timeFunction {C : Causality M} {D : Causality N} {e : M ≃ₜ N}
    (h : IsCausalIso C D e) {α : Type*} [Preorder α] {T : M → α}
    (hT : ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y) : D.IsCausal :=
  h.isCausal_iff.1 (Causality.isCausal_of_timeFunction hT)

/-! ### ETT's time function does not make the causality causal -/

/-- The doubled line `ℝ × Bool`: `p ≤_U q` iff `p = q ∈ U`, or `p.1 ≤ q.1` and the two fibres
over `[p.1, q.1]` lie in `U`; no chronology. -/
def doubledLine : Causality (ℝ × Bool) where
  le U p q := (p = q ∧ p ∈ U) ∨ (p.1 ≤ q.1 ∧ Icc p.1 q.1 ×ˢ (univ : Set Bool) ⊆ U)
  lt _ _ _ := False
  le_mem_left h := by
    rcases h with ⟨-, hp⟩ | ⟨hpq, hsub⟩
    · exact hp
    · exact hsub ⟨left_mem_Icc.2 hpq, trivial⟩
  le_mem_right h := by
    rcases h with ⟨rfl, hp⟩ | ⟨hpq, hsub⟩
    · exact hp
    · exact hsub ⟨right_mem_Icc.2 hpq, trivial⟩
  lt_mem_left h := h.elim
  lt_mem_right h := h.elim
  le_refl hx := Or.inl ⟨rfl, hx⟩
  le_trans := @fun U p q r h₁ h₂ => by
    rcases h₁ with ⟨rfl, -⟩ | ⟨h1, s1⟩
    · exact h₂
    · rcases h₂ with ⟨rfl, -⟩ | ⟨h2, s2⟩
      · exact Or.inr ⟨h1, s1⟩
      · refine Or.inr ⟨h1.trans h2, fun z hz => ?_⟩
        rcases le_total z.1 q.1 with hz' | hz'
        · exact s1 ⟨⟨hz.1.1, hz'⟩, hz.2⟩
        · exact s2 ⟨⟨hz', hz.1.2⟩, hz.2⟩
  lt_trans h _ := h
  le_mono := @fun U V hVU p q h' => by
    rcases h' with ⟨rfl, hp⟩ | ⟨h1, s1⟩
    · exact Or.inl ⟨rfl, hVU hp⟩
    · exact Or.inr ⟨h1, fun z hz => hVU (s1 hz)⟩
  lt_mono _ _ _ h' := h'
  le_of_lt h := h.elim
  isOpen_lt_right _ _ := by simp
  isOpen_lt_left _ _ := by simp

theorem doubledLine_isTimeFunction_fst : doubledLine.IsTimeFunction Prod.fst := by
  refine (⟨continuous_fst, isOpenMap_fst, ?_, fun _ _ _ _ _ h => h.elim⟩ :
    StrongMorphism doubledLine timelikeLine Prod.fst)
  intro O V hV p q hpq
  rcases hpq with ⟨rfl, hp⟩ | ⟨h1, s1⟩
  · have hp' : p ∈ (V : Set (ℝ × Bool)) := hp
    rw [hV] at hp'
    exact ⟨le_rfl, by simpa using hp'⟩
  · refine ⟨h1, fun z hz => ?_⟩
    have hz' : ((z, true) : ℝ × Bool) ∈ (V : Set (ℝ × Bool)) := s1 ⟨hz, trivial⟩
    rw [hV] at hz'
    exact hz'

theorem doubledLine_not_isCausal : ¬ doubledLine.IsCausal := by
  intro h
  have hle : ∀ b b' : Bool, doubledLine.le ⊤ ((0 : ℝ), b) ((0 : ℝ), b') :=
    fun _ _ => Or.inr ⟨le_rfl, fun _ _ => trivial⟩
  have := h (hle false true) (hle true false)
  simp at this

/-- **A time function in the sense of `defi:fonction_temps` does not make the causality causal**:
it is non-decreasing along `≤`, not strictly increasing. -/
theorem exists_isTimeFunction_not_isCausal :
    ∃ (C : Causality (ℝ × Bool)) (T : ℝ × Bool → ℝ), C.IsTimeFunction T ∧ ¬ C.IsCausal :=
  ⟨doubledLine, Prod.fst, doubledLine_isTimeFunction_fst, doubledLine_not_isCausal⟩

/-! ### Witnesses -/

/-- A translation of the timelike line is a causal isomorphism. -/
theorem timelikeLine_isCausalIso_addRight (t : ℝ) :
    IsCausalIso timelikeLine timelikeLine (Homeomorph.addRight t) := by
  set e := Homeomorph.addRight t
  have he : ∀ x, e x = x + t := fun _ => rfl
  have key : ∀ (U : Opens ℝ) (x y : ℝ),
      Icc (e x) (e y) ⊆ (e.opensCongr U : Set ℝ) ↔ Icc x y ⊆ U := by
    intro U x y
    have : Icc (e x) (e y) = e '' Icc x y := by
      rw [he, he]; exact (Set.image_add_const_Icc t x y).symm
    rw [this, coe_opensCongr, image_subset_image_iff e.injective]
  refine isCausalIso_iff.2 fun U x y => ⟨?_, ?_⟩
  · rw [timelikeLine_le, timelikeLine_le, key, he, he, add_le_add_iff_right]
  · rw [timelikeLine_lt, timelikeLine_lt, key, he, he, add_lt_add_iff_right]

/-- `LeTopIso` is strictly weaker than `IsCausalIso`: the identity of `ℝ` carries the causal
relation of the timelike line onto that of the lightlike line (they have the same `≤`), and is not a
causal isomorphism between them (their `≪` differ). -/
theorem timelikeLine_leTopIso_lightlikeLine :
    LeTopIso timelikeLine lightlikeLine (Homeomorph.refl ℝ) := fun _ _ => Iff.rfl

theorem not_isCausalIso_timelikeLine_lightlikeLine :
    ¬ IsCausalIso timelikeLine lightlikeLine (Homeomorph.refl ℝ) := fun h =>
  h.lt_iff.1 (show timelikeLine.lt ⊤ 0 1 from ⟨zero_lt_one, fun _ _ => trivial⟩)

end Causal
