import Causal.Geroch

/-!
# Cauchy embeddings and Cauchy extensions, abstractly

`def:cauchy_embedding_cauchy_extension` — `ETT.tex:1858`. `lem:Cauchy_plongement_toutes` —
`ETT.tex:1865`. Neither is marked: both are read in an abstraction of the singular flat setting
(below) that the author has not ruled on, and the lemma's (ii)⇒(i) needs a Cauchy surface of `M`.

> A *Cauchy embedding* of $M$ into $N$ is an injective $\mass{\geq0}$-morphism $\phi:M\rightarrow N$
> carrying some Cauchy surface of $M$ onto a Cauchy surface of $N$. We then say that $N$, together
> with $\phi$, is a *Cauchy extension* of $M$.

> The following are equivalent: (i) there exists a Cauchy surface $\Sigma$ of $M$ whose image
> $\phi(\Sigma)$ is a Cauchy surface of $N$; (ii) for every Cauchy surface $\Sigma$ of $M$, the image
> $\phi(\Sigma)$ is a Cauchy surface of $N$.

> such a map is in particular a local homeomorphism and a morphism of topological spacetimes.
> (`ETT.tex:1851`)

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| singular flat spacetimes | ⚠ weakened: topological spacetimes |
| `𝕄≥0`-morphism | ⚠ reading: `IsEMorphism`, a strong morphism which is a local isomorphism (`isEMorphism_iff`) |
| `M`, `N` globally hyperbolic | ✓ in `IsCauchyEmbedding`; ⚠ weakened in the lemma: `N` causal and Hausdorff only |
| `φ` injective | ✓ carried |
| (ii)⇒(i) | ⚠ strengthened: a Cauchy surface of `M` exists (`hex`, from `theo:geroch_sing`) |

## SCOPE (disclosed)

* **The abstraction.** An `𝕄≥0`-morphism becomes `IsEMorphismOn C D W φ`: continuous and open on
  `W`, a strong morphism (`≤`, `≪` of `V ⊆ W` into those of any `U ⊇ φ(V)`), and a local
  isomorphism. It is a reading (`ETT.tex:1851` says local homeomorphism; the local matching of the
  relations is added); rigidity (`rem:CBG_analytique`) is not part of it.
* **(i)⇒(ii) is proved in full under the abstraction** (`IsEMorphism.isCauchySurface_image`), with
  `N` causal and Hausdorff and nothing about `M`. Cauchy surfaces of `M` are those of the open set
  `φ(M)` (`isCauchySurfaceOn_image_iff`); then `IsCauchySurfaceOn.isCauchySurface_of_open`: the
  component of an inextensible curve of `N` in `φ(M)` is inextensible in `φ(M)`
  (`inextensible_ordConnectedComponent`, by splicing at a final segment or by a limit at a
  boundary point), and two components through one point of `φ(Σ₁)` are one, `N` being causal.
* (ii)⇒(i) needs `hex`.
* (ii)⇒(i) and Hausdorffness are not findings about the paper: in its setting a Cauchy surface
  exists (`theo:geroch_sing`), and Hausdorffness is part of a topological spacetime
  (`ETT.tex:124`, `def:category_topological_spacetimes` at `ETT.tex:255`), causality of `N`
  part of its global hyperbolicity. They are what the abstraction makes explicit.
* `IsCauchyInclusion` is the definition for an inclusion of open sets (kb/0001); the inclusion is
  an injective abstract morphism for any `A ≤ B` (`IsCauchyInclusion.isEMorphismOn_id`). `CurvesExtend`,
  a model fact (kb/0012), makes a Cauchy surface acausal (`IsCauchySurface.isAcausal`).
* **Moved in** (T-abs-sc-open-hoist), byte for byte under the same full names:
  `IsEMorphismOn.chronalCurveOn_comp`, the `≪` twin of `IsEMorphismOn.causalCurveOn_comp`, from
  `Causal.Model.FlatSpaceCylinder` (beside its twin); `IsEMorphismOn.pastInextensible_invComp`, the
  one-sided half of `IsEMorphismOn.inextensible_iff_invComp`, from `Causal.FlrwType` (the last
  block, which keeps the binder order of its first home). No import is added.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Function

open scoped Interval

universe u v w

variable {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]

/-! ### Global hyperbolicity of an open set, acausal sets, extension of curves -/

namespace Causality

variable (C : Causality M)

/-- `def:globally_hyperbolic` for the open subset `W` seen as a spacetime (kb/0001): `≤_W` is
antisymmetric and the diamonds `J_W(p, q)` are compact. -/
def GloballyHyperbolicOn (W : Opens M) : Prop :=
  (∀ ⦃x y : M⦄, C.le W x y → C.le W y x → x = y) ∧ ∀ p q : M, IsCompact (C.diamond W p q)

/-- A set no two distinct points of which are causally related in `M`. -/
def IsAcausal (S : Set M) : Prop := ∀ x ∈ S, ∀ y ∈ S, C.le ⊤ x y → x = y

/-- **A model fact, carried as a named hypothesis** (kb/0012): every future causal curve over a
segment lies on an inextensible causal curve. In a Lorentzian manifold this is the existence of
inextensible extensions (Zorn). On every T1, second countable topological space it is a theorem,
for any causality (`Causality.curvesExtend_of_t1_secondCountable`, `Causal.CurvesExtendSecondCountable`). -/
def CurvesExtend : Prop :=
  ∀ (c : ℝ → M) (a b : ℝ), a ≤ b → C.CausalCurveOn ⊤ c a b →
    ∃ (I : Set ℝ) (c' : ℝ → M), C.Inextensible ⊤ I c' ∧ c '' Icc a b ⊆ c' '' I

variable {C}

theorem globallyHyperbolicOn_top : C.GloballyHyperbolicOn ⊤ ↔ C.GloballyHyperbolic := Iff.rfl

theorem dual_globallyHyperbolicOn {W : Opens M} :
    C.dual.GloballyHyperbolicOn W ↔ C.GloballyHyperbolicOn W := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun x y hxy hyx => h1 hyx hxy, fun p q => ?_⟩
    have : C.dual.diamond W q p = C.diamond W p q := by
      ext z; simp [mem_diamond]
    rw [← this]; exact h2 q p
  · rintro ⟨h1, h2⟩
    refine ⟨fun x y hxy hyx => h1 hyx hxy, fun p q => ?_⟩
    have : C.dual.diamond W p q = C.diamond W q p := by
      ext z; simp [mem_diamond]
    rw [this]; exact h2 q p

theorem dual_isAcausal {S : Set M} : C.dual.IsAcausal S ↔ C.IsAcausal S :=
  ⟨fun h x hx y hy hxy => (h y hy x hx hxy).symm, fun h x hx y hy hxy => (h y hy x hx hxy).symm⟩

/-- **A Cauchy surface is acausal** when curves extend (`CurvesExtend`) and `M` is causally
arc-connected: two related points of `S` lie on one inextensible causal curve, which meets `S`
once. -/
theorem IsCauchySurface.isAcausal {S : Set M} (hS : C.IsCauchySurface S)
    (hC : C.CausallyArcConnected) (hext : C.CurvesExtend) : C.IsAcausal S := by
  intro x hx y hy hxy
  obtain ⟨c, hc, hc0, hc1⟩ := (hC ⊤ le_rfl x y).1.1 hxy
  obtain ⟨I, c', hc', hsub⟩ := hext c 0 1 zero_le_one hc
  obtain ⟨z, -, hz⟩ := hS I c' hc'
  have h0 : c 0 ∈ c' '' I := hsub ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
  have h1 : c 1 ∈ c' '' I := hsub ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩
  rw [hc0] at h0; rw [hc1] at h1
  exact (hz x ⟨h0, hx⟩).trans (hz y ⟨h1, hy⟩).symm

/-- `CurvesExtend` for the reversed causality. -/
theorem CurvesExtend.dual (h : C.CurvesExtend) : C.dual.CurvesExtend := by
  intro c a b hab hc
  have hc' : C.CausalCurveOn ⊤ (fun t => c (-t)) (-b) (-a) :=
    CurveOn.neg (r := C.dual.le) (W := ⊤) (c := c) (a := -b) (b := -a)
      (by rw [neg_neg, neg_neg]; exact hc)
  obtain ⟨I, c', hc'i, hsub⟩ := h _ (-b) (-a) (neg_le_neg hab) hc'
  refine ⟨-I, fun t => c' (-t), hc'i.dual_reverse, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨u, hu, hcu⟩ := hsub ⟨-t, ⟨neg_le_neg ht.2, neg_le_neg ht.1⟩, rfl⟩
  exact ⟨-u, by simpa using hu, by simpa using hcu⟩

/-! ### Curves over an interval: congruence and change of open set -/

theorem CausalCurveIn.mono_opens {W W' : Opens M} {I : Set ℝ} {c : ℝ → M}
    (hc : C.CausalCurveIn W I c) (hW : W ≤ W') : C.CausalCurveIn W' I c :=
  ⟨hc.nonempty, hc.ordConnected, fun a ha b hb =>
    CurveOn.mono_opens C.isRelFamily_le (hc.curve a ha b hb) hW⟩

theorem CausalCurveIn.congr {W : Opens M} {I : Set ℝ} {c d : ℝ → M}
    (hc : C.CausalCurveIn W I c) (h : EqOn c d I) : C.CausalCurveIn W I d :=
  ⟨hc.nonempty, hc.ordConnected, fun a ha b hb => by
    rcases le_or_gt a b with hab | hab
    · exact CurveOn.congr (hc.curve a ha b hb) (h.mono (hc.ordConnected.out ha hb))
    · exact CurveOn.of_lt hab⟩

/-- A causal curve over `I` is continuous on every segment of `I`. -/
theorem CausalCurveIn.continuousOn_Icc {W : Opens M} {I : Set ℝ} {c : ℝ → M}
    (hc : C.CausalCurveIn W I c) {a b : ℝ} (ha : a ∈ I) (hb : b ∈ I) :
    ContinuousOn c (Icc a b) :=
  CurveOn.continuousOn C.isRelFamily_le (hc.curve a ha b hb)

theorem Extensible.congr {W : Opens M} {I : Set ℝ} {c d : ℝ → M} (hc : C.Extensible W I c)
    (h : EqOn c d I) : C.Extensible W I d := by
  obtain ⟨I', c', hcurve, ⟨φ, h1, h2, h3, h4⟩, ⟨t', ht', h5⟩⟩ := hc
  exact ⟨I', c', hcurve, ⟨φ, h1, h2, h3, fun t ht => (h4 t ht).trans (h ht)⟩,
    ⟨t', ht', fun t ht => (h ht) ▸ h5 t ht⟩⟩

/-- Only the values on `I` matter for inextensibility. -/
theorem inextensible_congr {W : Opens M} {I : Set ℝ} {c d : ℝ → M} (h : EqOn c d I) :
    C.Inextensible W I c ↔ C.Inextensible W I d :=
  ⟨fun hc => ⟨hc.1.congr h, fun he => hc.2 (he.congr h.symm)⟩,
    fun hd => ⟨hd.1.congr h.symm, fun he => hd.2 (he.congr h)⟩⟩

end Causality

/-! ### Abstract `𝕄≥0`-morphisms -/

/-- **An abstract `𝕄≥0`-morphism defined on the open set `W` of `M`** (reading of
`ETT.tex:1849–1852`: "a local homeomorphism and a morphism of topological spacetimes", made a
local isomorphism). `φ` is continuous on `W`, maps the open subsets of `W` to open sets, maps the
relations of every open `V ⊆ W` into those of every open `U ⊇ φ(V)` (a strong morphism, in the
form `StrongMorphism.le_of_mapsTo`), and every point of `W` has an open neighbourhood on which `φ`
is injective and matches the relations of every smaller open set with those of its image (a local
isomorphism, `LocalIsomorphism`). -/
structure IsEMorphismOn (C : Causality M) (D : Causality N) (W : Opens M) (φ : M → N) :
    Prop where
  continuousOn : ContinuousOn φ W
  isOpen_image : ∀ V : Opens M, V ≤ W → IsOpen (φ '' V)
  map_le : ∀ (V : Opens M) (U : Opens N), V ≤ W → MapsTo φ V U →
    ∀ ⦃x y : M⦄, C.le V x y → D.le U (φ x) (φ y)
  map_lt : ∀ (V : Opens M) (U : Opens N), V ≤ W → MapsTo φ V U →
    ∀ ⦃x y : M⦄, C.lt V x y → D.lt U (φ x) (φ y)
  locally : ∀ x ∈ W, ∃ V : Opens M, V ≤ W ∧ x ∈ V ∧ InjOn φ V ∧
    ∀ V' : Opens M, V' ≤ V → ∀ U : Opens N, (U : Set N) = φ '' V' → ∀ y ∈ V', ∀ z ∈ V',
      (C.le V' y z ↔ D.le U (φ y) (φ z)) ∧ (C.lt V' y z ↔ D.lt U (φ y) (φ z))

/-- **An abstract `𝕄≥0`-morphism** `M → N`: `IsEMorphismOn` on `M` itself. It is exactly a strong
morphism which is a local isomorphism (`isEMorphism_iff`). -/
def IsEMorphism (C : Causality M) (D : Causality N) (φ : M → N) : Prop := IsEMorphismOn C D ⊤ φ

variable {C : Causality M} {D : Causality N} {W : Opens M} {φ : M → N}

namespace IsEMorphismOn

/-- The image of an open subset of `W`, as an open set. -/
def imageOpens (h : IsEMorphismOn C D W φ) (V : Opens M) (hV : V ≤ W) : Opens N :=
  ⟨φ '' V, h.isOpen_image V hV⟩

@[simp] theorem coe_imageOpens (h : IsEMorphismOn C D W φ) (V : Opens M) (hV : V ≤ W) :
    (h.imageOpens V hV : Set N) = φ '' V := rfl

/-- An abstract morphism on `W` is one on every open subset of `W`. -/
theorem mono (h : IsEMorphismOn C D W φ) {W' : Opens M} (hW : W' ≤ W) : IsEMorphismOn C D W' φ where
  continuousOn := h.continuousOn.mono hW
  isOpen_image V hV := h.isOpen_image V (hV.trans hW)
  map_le V U hV := h.map_le V U (hV.trans hW)
  map_lt V U hV := h.map_lt V U (hV.trans hW)
  locally x hx := by
    obtain ⟨V, hVW, hxV, hinj, hmatch⟩ := h.locally x (hW hx)
    refine ⟨V ⊓ W', inf_le_right, ⟨hxV, hx⟩, hinj.mono inf_le_left, fun V' hV' => ?_⟩
    exact hmatch V' (hV'.trans inf_le_left)

/-- Two maps which agree on `W` are morphisms on `W` together. -/
theorem congr (h : IsEMorphismOn C D W φ) {ψ : M → N} (he : EqOn φ ψ W) :
    IsEMorphismOn C D W ψ where
  continuousOn := h.continuousOn.congr he.symm
  isOpen_image V hV := by
    rw [← (he.mono hV).image_eq]; exact h.isOpen_image V hV
  map_le V U hV hmaps x y hxy := by
    have hx := C.le_mem_left hxy; have hy := C.le_mem_right hxy
    rw [← he (hV hx), ← he (hV hy)]
    exact h.map_le V U hV (fun z hz => (he (hV hz)) ▸ hmaps hz) hxy
  map_lt V U hV hmaps x y hxy := by
    have hx := C.lt_mem_left hxy; have hy := C.lt_mem_right hxy
    rw [← he (hV hx), ← he (hV hy)]
    exact h.map_lt V U hV (fun z hz => (he (hV hz)) ▸ hmaps hz) hxy
  locally x hx := by
    obtain ⟨V, hVW, hxV, hinj, hmatch⟩ := h.locally x hx
    refine ⟨V, hVW, hxV, hinj.congr (he.mono hVW), fun V' hV' U hU y hy z hz => ?_⟩
    have hU' : (U : Set N) = φ '' V' := by rw [hU, (he.mono (hV'.trans hVW)).image_eq]
    rw [← he (hVW (hV' hy)), ← he (hVW (hV' hz))]
    exact hmatch V' hV' U hU' y hy z hz

/-- **Push-forward of a causal curve**: the image of a future causal curve of `V ⊆ W` is a future
causal curve of every open `U ⊇ φ(V)`. -/
theorem causalCurveOn_comp (h : IsEMorphismOn C D W φ) {V : Opens M} (hVW : V ≤ W)
    {U : Opens N} (hVU : MapsTo φ V U) {d : ℝ → M} {a b : ℝ} (hd : C.CausalCurveOn V d a b) :
    D.CausalCurveOn U (φ ∘ d) a b where
  mem t ht := hVU (hd.mem t ht)
  rel t ht N' hN' hN't := by
    have hO : IsOpen ((W : Set M) ∩ φ ⁻¹' N') :=
      h.continuousOn.isOpen_inter_preimage W.isOpen N'.isOpen
    let V' : Opens M := V ⊓ ⟨_, hO⟩
    obtain ⟨l, u, hl, hu, hrel⟩ :=
      hd.rel t ht V' inf_le_left ⟨hd.mem t ht, hVW (hd.mem t ht), hN't⟩
    exact ⟨l, u, hl, hu, fun s hs s' hs' h1 h2 h3 =>
      h.map_le V' N' (inf_le_left.trans hVW) (fun z hz => hz.2.2) (hrel s hs s' hs' h1 h2 h3)⟩

/-- The image of a causal curve over an interval. -/
theorem causalCurveIn_comp (h : IsEMorphismOn C D W φ) {V : Opens M} (hVW : V ≤ W)
    {U : Opens N} (hVU : MapsTo φ V U) {I : Set ℝ} {d : ℝ → M} (hd : C.CausalCurveIn V I d) :
    D.CausalCurveIn U I (φ ∘ d) :=
  ⟨hd.nonempty, hd.ordConnected, fun a ha b hb => h.causalCurveOn_comp hVW hVU (hd.curve a ha b hb)⟩

/-- **Push-forward of a chronal curve** by an abstract morphism on `W`: the image of a future
chronal curve of `V ⊆ W` is a future chronal curve of every open `U ⊇ φ(V)` (the `≪` twin of
`IsEMorphismOn.causalCurveOn_comp`). -/
theorem chronalCurveOn_comp {M N : Type*} [TopologicalSpace M]
    [TopologicalSpace N] {C : Causality M} {D : Causality N} {W : Opens M} {φ : M → N}
    (h : IsEMorphismOn C D W φ) {V : Opens M} (hVW : V ≤ W)
    {U : Opens N} (hVU : MapsTo φ V U) {c : ℝ → M} {a b : ℝ} (hc : C.ChronalCurveOn V c a b) :
    D.ChronalCurveOn U (φ ∘ c) a b where
  mem t ht := hVU (hc.mem t ht)
  rel t ht N' hN' hN't := by
    have hO : IsOpen ((W : Set M) ∩ φ ⁻¹' N') :=
      h.continuousOn.isOpen_inter_preimage W.isOpen N'.isOpen
    let V' : Opens M := V ⊓ ⟨_, hO⟩
    obtain ⟨l, u, hl, hu, hrel⟩ :=
      hc.rel t ht V' inf_le_left ⟨hc.mem t ht, hVW (hc.mem t ht), hN't⟩
    exact ⟨l, u, hl, hu, fun s hs s' hs' h1 h2 h3 =>
      h.map_lt V' N' (inf_le_left.trans hVW) (fun z hz => hz.2.2) (hrel s hs s' hs' h1 h2 h3)⟩

/-- A left inverse of `φ` on `W` inverts it on the image of every `V ⊆ W`. -/
theorem leftInvOn_image {g : N → M} (hg : LeftInvOn g φ W) {V : Opens M} (hVW : V ≤ W)
    {U : Opens N} (hU : (U : Set N) = φ '' V) {y : N} (hy : y ∈ U) : g y ∈ V ∧ φ (g y) = y := by
  rw [← SetLike.mem_coe, hU] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  rw [hg (hVW hx)]
  exact ⟨hx, rfl⟩

/-- **Pull-back of a causal curve** along a morphism injective on `W`: a future causal curve of
the image `U = φ(V)` of an open `V ⊆ W`, read through a left inverse of `φ`, is a future causal
curve of `V`. -/
theorem causalCurveOn_invComp (h : IsEMorphismOn C D W φ) {g : N → M} (hg : LeftInvOn g φ W)
    {V : Opens M} (hVW : V ≤ W) {U : Opens N} (hU : (U : Set N) = φ '' V) {e : ℝ → N} {a b : ℝ}
    (he : D.CausalCurveOn U e a b) : C.CausalCurveOn V (g ∘ e) a b where
  mem t ht := (leftInvOn_image hg hVW hU (he.mem t ht)).1
  rel t ht N' hN' hxN' := by
    have hkey := leftInvOn_image hg hVW hU (he.mem t ht)
    obtain ⟨V0, hV0W, hxV0, -, hmatch⟩ := h.locally (g (e t)) (hVW hkey.1)
    let V'' : Opens M := N' ⊓ V0
    let U'' : Opens N := ⟨φ '' V'', h.isOpen_image V'' (inf_le_right.trans hV0W)⟩
    have hetU'' : e t ∈ U'' := ⟨g (e t), ⟨hxN', hxV0⟩, hkey.2⟩
    have hU''U : U'' ≤ U := by
      rintro y ⟨z, hz, rfl⟩
      rw [← SetLike.mem_coe, hU]
      exact ⟨z, hN' hz.1, rfl⟩
    obtain ⟨l, u, hl, hu, hrel⟩ := he.rel t ht U'' hU''U hetU''
    refine ⟨l, u, hl, hu, fun s hs s' hs' h1 h2 h3 => ?_⟩
    have hD := hrel s hs s' hs' h1 h2 h3
    obtain ⟨y, hy, hys⟩ := D.le_mem_left hD
    obtain ⟨y', hy', hys'⟩ := D.le_mem_right hD
    have hgy : g (e s) = y := by rw [← hys, hg (hV0W hy.2)]
    have hgy' : g (e s') = y' := by rw [← hys', hg (hV0W hy'.2)]
    have hC : C.le V'' y y' :=
      ((hmatch V'' inf_le_right U'' rfl y hy y' hy').1).2 (by rw [hys, hys']; exact hD)
    show C.le N' (g (e s)) (g (e s'))
    rw [hgy, hgy']
    exact C.le_mono inf_le_left hC

theorem causalCurveIn_invComp (h : IsEMorphismOn C D W φ) {g : N → M} (hg : LeftInvOn g φ W)
    {V : Opens M} (hVW : V ≤ W) {U : Opens N} (hU : (U : Set N) = φ '' V) {I : Set ℝ}
    {e : ℝ → N} (he : D.CausalCurveIn U I e) : C.CausalCurveIn V I (g ∘ e) :=
  ⟨he.nonempty, he.ordConnected, fun a ha b hb => h.causalCurveOn_invComp hg hVW hU (he.curve a ha b hb)⟩

/-- **Inextensibility is transported** along a morphism injective on `W`, between an open `V ⊆ W`
and its image `U = φ(V)`, each seen as a spacetime. -/
theorem inextensible_iff_invComp (h : IsEMorphismOn C D W φ) (hinj : InjOn φ W) {g : N → M}
    (hg : LeftInvOn g φ W) {V : Opens M} (hVW : V ≤ W) {U : Opens N}
    (hU : (U : Set N) = φ '' V) {I : Set ℝ} {e : ℝ → N} (heU : ∀ t ∈ I, e t ∈ U) :
    D.Inextensible U I e ↔ C.Inextensible V I (g ∘ e) := by
  have hmaps : MapsTo φ V U := fun x hx => by
    show φ x ∈ (U : Set N); rw [hU]; exact mem_image_of_mem φ hx
  have hφg : ∀ t ∈ I, φ (g (e t)) = e t := fun t ht => (leftInvOn_image hg hVW hU (heU t ht)).2
  constructor
  · rintro ⟨hcurve, hnot⟩
    refine ⟨h.causalCurveIn_invComp hg hVW hU hcurve, ?_⟩
    rintro ⟨I', c', hc', ⟨ψ, h1, h2, h3, h4⟩, ⟨t', ht', h5⟩⟩
    refine hnot ⟨I', φ ∘ c', h.causalCurveIn_comp hVW hmaps hc',
      ⟨ψ, h1, h2, h3, fun t ht => ?_⟩, ⟨t', ht', fun t ht heq => h5 t ht ?_⟩⟩
    · simp only [comp_apply]; rw [h4 t ht]; exact hφg t ht
    · refine hinj (hVW (hc'.mem ht')) (hVW (leftInvOn_image hg hVW hU (heU t ht)).1) ?_
      simp only [comp_apply] at heq ⊢
      rw [heq, hφg t ht]
  · rintro ⟨hcurve, hnot⟩
    refine ⟨(h.causalCurveIn_comp hVW hmaps hcurve).congr fun t ht => hφg t ht, ?_⟩
    rintro ⟨I', e', he', ⟨ψ, h1, h2, h3, h4⟩, ⟨t', ht', h5⟩⟩
    refine hnot ⟨I', g ∘ e', h.causalCurveIn_invComp hg hVW hU he',
      ⟨ψ, h1, h2, h3, fun t ht => ?_⟩, ⟨t', ht', fun t ht heq => h5 t ht ?_⟩⟩
    · simp only [comp_apply]; rw [h4 t ht]
    · have h' := congrArg φ heq
      simp only [comp_apply] at h'
      rwa [(leftInvOn_image hg hVW hU (he'.mem ht')).2, hφg t ht] at h'

/-- The same transport, read from `M`: a curve `d` of `V` is inextensible in `V` iff `φ ∘ d` is
inextensible in `φ(V)`. -/
theorem inextensible_iff_comp (h : IsEMorphismOn C D W φ) (hinj : InjOn φ W) {g : N → M}
    (hg : LeftInvOn g φ W) {V : Opens M} (hVW : V ≤ W) {U : Opens N}
    (hU : (U : Set N) = φ '' V) {I : Set ℝ} {d : ℝ → M} (hdV : ∀ t ∈ I, d t ∈ V) :
    C.Inextensible V I d ↔ D.Inextensible U I (φ ∘ d) := by
  have hmaps : MapsTo φ V U := fun x hx => by
    show φ x ∈ (U : Set N); rw [hU]; exact mem_image_of_mem φ hx
  rw [h.inextensible_iff_invComp hinj hg hVW hU (e := φ ∘ d) (fun t ht => hmaps (hdV t ht))]
  exact (Causality.inextensible_congr fun t ht => by
    simp only [comp_apply]; exact hg (hVW (hdV t ht))).symm

/-- **Cauchy surfaces are transported** along a morphism injective on `W`: `S ⊆ V` is a Cauchy
surface of `V` iff `φ(S)` is a Cauchy surface of `φ(V)`. -/
theorem isCauchySurfaceOn_image_iff (h : IsEMorphismOn C D W φ) (hinj : InjOn φ W)
    {V : Opens M} (hVW : V ≤ W) {U : Opens N} (hU : (U : Set N) = φ '' V) {S : Set M}
    (hS : S ⊆ V) : C.IsCauchySurfaceOn V S ↔ D.IsCauchySurfaceOn U (φ '' S) := by
  have hmaps : MapsTo φ V U := fun x hx => by
    show φ x ∈ (U : Set N); rw [hU]; exact mem_image_of_mem φ hx
  constructor
  · intro hC I e he
    obtain ⟨t₀, ht₀⟩ := he.1.nonempty
    have hne : Nonempty M := by
      have := he.1.mem ht₀
      rw [← SetLike.mem_coe, hU] at this
      obtain ⟨x, -, -⟩ := this
      exact ⟨x⟩
    set g := invFunOn φ W
    have hg : LeftInvOn g φ W := hinj.leftInvOn_invFunOn
    have heU : ∀ t ∈ I, e t ∈ U := fun t ht => he.1.mem ht
    obtain ⟨x, ⟨⟨t, ht, rfl⟩, hxS⟩, huniq⟩ :=
      hC I (g ∘ e) ((h.inextensible_iff_invComp hinj hg hVW hU heU).1 he)
    have hφg := (leftInvOn_image hg hVW hU (heU t ht)).2
    refine ⟨e t, ⟨⟨t, ht, rfl⟩, ⟨_, hxS, hφg⟩⟩, ?_⟩
    rintro y ⟨⟨t', ht', rfl⟩, ⟨s, hs, hse⟩⟩
    have hgs : g (e t') = s := by rw [← hse, hg (hVW (hS hs))]
    have := huniq (g (e t')) ⟨⟨t', ht', rfl⟩, hgs ▸ hs⟩
    rw [← (leftInvOn_image hg hVW hU (heU t' ht')).2, this, comp_apply, hφg]
  · intro hD I d hd
    obtain ⟨t₀, ht₀⟩ := hd.1.nonempty
    haveI : Nonempty M := ⟨d t₀⟩
    set g := invFunOn φ W
    have hg : LeftInvOn g φ W := hinj.leftInvOn_invFunOn
    have hdV : ∀ t ∈ I, d t ∈ V := fun t ht => hd.1.mem ht
    obtain ⟨y, ⟨⟨t, ht, rfl⟩, ⟨s, hs, hse⟩⟩, huniq⟩ :=
      hD I (φ ∘ d) ((h.inextensible_iff_comp hinj hg hVW hU hdV).1 hd)
    have hds : d t = s := hinj (hVW (hdV t ht)) (hVW (hS hs)) hse.symm
    refine ⟨d t, ⟨⟨t, ht, rfl⟩, hds ▸ hs⟩, ?_⟩
    rintro x ⟨⟨t', ht', rfl⟩, hx⟩
    have := huniq (φ (d t')) ⟨⟨t', ht', rfl⟩, ⟨d t', hx, rfl⟩⟩
    exact hinj (hVW (hdV t' ht')) (hVW (hdV t ht)) this

end IsEMorphismOn

/-- An abstract morphism is a strong morphism which is a local isomorphism, and conversely. -/
theorem isEMorphism_iff : IsEMorphism C D φ ↔ StrongMorphism C D φ ∧ LocalIsomorphism C D φ := by
  constructor
  · intro h
    have hc : Continuous φ := by
      have := h.continuousOn
      rw [Opens.coe_top, continuousOn_univ] at this
      exact this
    have hmaps : ∀ (U : Opens N) (V : Opens M), (V : Set M) = φ ⁻¹' U → MapsTo φ V U :=
      fun U V hV z hz => by
        have : z ∈ φ ⁻¹' (U : Set N) := hV ▸ hz
        exact this
    refine ⟨⟨hc, fun U hU => h.isOpen_image ⟨U, hU⟩ le_top,
      fun U V hV _ _ hxy => h.map_le V U le_top (hmaps U V hV) hxy,
      fun U V hV _ _ hxy => h.map_lt V U le_top (hmaps U V hV) hxy⟩, ?_, fun x => ?_⟩
    · rw [isLocalHomeomorph_iff_isOpenEmbedding_restrict]
      intro x
      obtain ⟨V, -, hxV, hinj, -⟩ := h.locally x trivial
      refine ⟨V, V.isOpen.mem_nhds hxV,
        IsOpenEmbedding.of_continuous_injective_isOpenMap (hc.continuousOn.restrict)
          hinj.injective ?_⟩
      intro O hO
      obtain ⟨O', hO', rfl⟩ := isOpen_induced_iff.1 hO
      have : (V : Set M).restrict φ '' (Subtype.val ⁻¹' O') =
          φ '' ((V ⊓ ⟨O', hO'⟩ : Opens M) : Set M) := by
        ext y
        constructor
        · rintro ⟨⟨z, hz⟩, hz', rfl⟩
          exact ⟨z, ⟨hz, hz'⟩, rfl⟩
        · rintro ⟨z, ⟨hz, hz'⟩, rfl⟩
          exact ⟨⟨z, hz⟩, hz', rfl⟩
      rw [this]
      exact h.isOpen_image _ le_top
    · obtain ⟨V, -, hxV, hinj, hm⟩ := h.locally x trivial
      exact ⟨V, hxV, hinj, hm⟩
  · rintro ⟨hs, hl⟩
    exact
      { continuousOn := hs.continuous.continuousOn
        isOpen_image := fun V _ => hs.isOpenMap _ V.isOpen
        map_le := fun _ _ _ hmaps _ _ hxy => hs.le_of_mapsTo hmaps hxy
        map_lt := fun _ _ _ hmaps _ _ hxy => hs.lt_of_mapsTo hmaps hxy
        locally := fun x _ => by
          obtain ⟨V, hx, hinj, hm⟩ := hl.2 x
          exact ⟨V, le_top, hx, hinj, hm⟩ }


/-- The identity is an abstract morphism. -/
theorem IsEMorphism.id : IsEMorphism C C id where
  continuousOn := continuous_id.continuousOn
  isOpen_image V _ := by rw [image_id]; exact V.isOpen
  map_le V U _ hmaps _ _ hxy := C.le_mono (show V ≤ U from fun _ hz => hmaps hz) hxy
  map_lt V U _ hmaps _ _ hxy := C.lt_mono (show V ≤ U from fun _ hz => hmaps hz) hxy
  locally x _ := ⟨⊤, le_rfl, trivial, injOn_id _, fun V' _ U hU _ _ _ _ => by
    have : U = V' := SetLike.coe_injective (by rw [hU, image_id])
    subst this
    exact ⟨Iff.rfl, Iff.rfl⟩⟩

/-- Non-triviality: a constant map of the timelike line is not an abstract morphism (it is not
open). -/
theorem not_isEMorphism_const : ¬ IsEMorphism timelikeLine timelikeLine (fun _ => (0 : ℝ)) := by
  intro h
  have := h.isOpen_image ⊤ le_rfl
  rw [Opens.coe_top, image_univ, range_const] at this
  exact not_isOpen_singleton (0 : ℝ) this

/-! ### Splicing a curve at a final segment, and the components of a curve in an open set -/

namespace Causality

variable {C : Causality M}

/-- **Splicing.** If `J` is a final segment of `I` and `c` restricted to `J` has a strict
extension at the future end, so has `c`: keep `c` up to `t₀ ∈ J`, then follow the extension. The
new value is new for all of `c` because `M` is causal. -/
theorem futureExtensible_of_final (hcaus : C.IsCausal) {I J I' : Set ℝ} {c c' : ℝ → M} {t₀ : ℝ}
    (hc : C.CausalCurveIn ⊤ I c) (hJI : J ⊆ I) (ht₀ : t₀ ∈ J)
    (hfin : ∀ t ∈ I, ∀ s ∈ J, s ≤ t → t ∈ J)
    (hc' : C.CausalCurveIn ⊤ I' c') {φ : ℝ → ℝ} (hφ : StrictMonoOn φ J) (hmaps : MapsTo φ J I')
    (hoc : (φ '' J).OrdConnected) (heq : ∀ t ∈ J, c' (φ t) = c t)
    (hinit : ∀ t ∈ J, ∀ t' ∈ I', t' ≤ φ t → t' ∈ φ '' J)
    {t' : ℝ} (ht' : t' ∈ I') (hlt : ∀ t ∈ J, φ t < t') (hnew : ∀ t ∈ J, c' t' ≠ c t) :
    C.FutureExtensible ⊤ I c := by
  set δ := φ t₀ - t₀ with hδ
  set I'' : Set ℝ := {t | (t ∈ I ∧ t ≤ t₀) ∨ (t₀ ≤ t ∧ t + δ ∈ I')} with hI''
  set d : ℝ → M := fun t => if t ≤ t₀ then c t else c' (t + δ) with hd
  set ψ : ℝ → ℝ := fun t => if t ≤ t₀ then t else φ t - δ with hψ
  have ht₀I : t₀ ∈ I := hJI ht₀
  have hφt₀ : φ t₀ = t₀ + δ := by rw [hδ]; ring
  have hI''le : ∀ t ∈ I'', t ≤ t₀ → t ∈ I := by
    rintro t (⟨h, -⟩ | ⟨h1, -⟩) h2
    · exact h
    · rw [le_antisymm h2 h1]; exact ht₀I
  have hI''ge : ∀ t ∈ I'', t₀ ≤ t → t + δ ∈ I' := by
    rintro t (⟨-, h1⟩ | ⟨-, h⟩) h2
    · rw [le_antisymm h1 h2, ← hφt₀]; exact hmaps ht₀
    · exact h
  have ht₀I'' : t₀ ∈ I'' := Or.inl ⟨ht₀I, le_rfl⟩
  have hgtJ : ∀ t ∈ I, t₀ ≤ t → t ∈ J := fun t ht h => hfin t ht t₀ ht₀ h
  have hdle : ∀ t, t ≤ t₀ → d t = c t := fun t h => if_pos h
  have hdgt : ∀ t, t₀ < t → d t = c' (t + δ) := fun t h => if_neg (not_le.2 h)
  have hdt₀ : d t₀ = c' (t₀ + δ) := by rw [hdle t₀ le_rfl, ← hφt₀, heq t₀ ht₀]
  have hshift : ∀ a b : ℝ, a + δ ∈ I' → b + δ ∈ I' →
      CurveOn C.le ⊤ (fun t => c' (t + δ)) a b := fun a b ha hb => by
    have h := CurveOn.comp_affine (r := C.le) (W := ⊤) (c := c') (k := 1) (m := δ) (a' := a)
      (b' := b) one_pos (by rw [one_mul, one_mul]; exact hc'.curve _ ha _ hb)
    exact h.congr fun t _ => by simp only [one_mul]
  -- the new curve
  have hd_curve : C.CausalCurveIn ⊤ I'' d := by
    refine ⟨⟨t₀, ht₀I''⟩, ⟨fun x hx y hy z hz => ?_⟩, fun a ha b hb => ?_⟩
    · rcases le_total z t₀ with hzt | hzt
      · exact Or.inl ⟨hc.ordConnected.out (hI''le x hx (hz.1.trans hzt)) ht₀I ⟨hz.1, hzt⟩, hzt⟩
      · refine Or.inr ⟨hzt, ?_⟩
        rcases le_total y t₀ with hyt | hyt
        · have : z = t₀ := le_antisymm (hz.2.trans hyt) hzt
          rw [this, ← hφt₀]; exact hmaps ht₀
        · exact hc'.ordConnected.out (hmaps ht₀) (hI''ge y hy hyt)
            ⟨by rw [hφt₀]; linarith, by linarith [hz.2]⟩
    · rcases lt_or_ge b a with hba | hab
      · exact CurveOn.of_lt hba
      by_cases hbt : b ≤ t₀
      · exact CurveOn.congr (hc.curve a (hI''le a ha (hab.trans hbt)) b (hI''le b hb hbt))
          fun t ht => (hdle t (ht.2.trans hbt)).symm
      by_cases hta : t₀ ≤ a
      · refine (hshift a b (hI''ge a ha hta) (hI''ge b hb (hta.trans hab))).congr
          fun t ht => ?_
        rcases (hta.trans ht.1).eq_or_lt with h | h
        · rw [← h, hdt₀]
        · rw [hdgt t h]
      · have hbt' : t₀ < b := lt_of_not_ge hbt
        have hta' : a < t₀ := lt_of_not_ge hta
        have h2 := hshift t₀ b (by rw [← hφt₀]; exact hmaps ht₀) (hI''ge b hb hbt'.le)
        have := CurveOn.concat C.isRelFamily_le (hc.curve a (hI''le a ha hta'.le) t₀ ht₀I) h2
          hta'.le hbt'.le (by rw [← hdt₀, hdle t₀ le_rfl])
        exact this
  -- the reparametrisation
  have hψle : ∀ t, t ≤ t₀ → ψ t = t := fun t h => if_pos h
  have hψgt : ∀ t, t₀ < t → ψ t = φ t - δ := fun t h => if_neg (not_le.2 h)
  have hφgt : ∀ t ∈ J, t₀ < t → t₀ < φ t - δ := fun t ht h => by
    have := hφ ht₀ ht h; linarith
  have hφgt' : ∀ t ∈ J, φ t₀ < φ t → t₀ < t := fun t ht h =>
    lt_of_not_ge fun h' => absurd (hφ.monotoneOn ht ht₀ h') (not_le.2 h)
  have hψmono : StrictMonoOn ψ I := by
    intro s hs t ht hst
    rcases le_or_gt t t₀ with htt | htt
    · rw [hψle s (hst.le.trans htt), hψle t htt]; exact hst
    · rw [hψgt t htt]
      rcases le_or_gt s t₀ with hst' | hst'
      · rw [hψle s hst']; linarith [hφgt t (hgtJ t ht htt.le) htt]
      · rw [hψgt s hst']
        have := hφ (hgtJ s hs hst'.le) (hgtJ t ht htt.le) hst
        linarith
  have hψmaps : MapsTo ψ I I'' := by
    intro t ht
    rcases le_or_gt t t₀ with htt | htt
    · rw [hψle t htt]; exact Or.inl ⟨ht, htt⟩
    · rw [hψgt t htt]
      refine Or.inr ⟨(hφgt t (hgtJ t ht htt.le) htt).le, ?_⟩
      rw [sub_add_cancel]; exact hmaps (hgtJ t ht htt.le)
  have hψoc : (ψ '' I).OrdConnected := by
    refine ⟨?_⟩
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ z hz
    rcases le_or_gt z t₀ with hzt | hzt
    · have hat : a ≤ t₀ := le_of_not_gt fun h => by
        have := hφgt a (hgtJ a ha h.le) h
        rw [hψgt a h] at hz; linarith [hz.1]
      rw [hψle a hat] at hz
      exact ⟨z, hc.ordConnected.out ha ht₀I ⟨hz.1, hzt⟩, hψle z hzt⟩
    · have hbt : t₀ < b := lt_of_not_ge fun h => by
        rw [hψle b h] at hz; linarith [hz.2]
      have hbJ := hgtJ b hb hbt.le
      rw [hψgt b hbt] at hz
      obtain ⟨w, hw, hwz⟩ := hoc.out (mem_image_of_mem φ ht₀) (mem_image_of_mem φ hbJ)
        (show z + δ ∈ Icc (φ t₀) (φ b) from ⟨by rw [hφt₀]; linarith, by linarith [hz.2]⟩)
      have hwt : t₀ < w := hφgt' w hw (by rw [hwz, hφt₀]; linarith)
      exact ⟨w, hJI hw, by rw [hψgt w hwt, hwz]; ring⟩
  have hdψ : ∀ t ∈ I, d (ψ t) = c t := by
    intro t ht
    rcases le_or_gt t t₀ with htt | htt
    · rw [hψle t htt, hdle t htt]
    · have htJ := hgtJ t ht htt.le
      rw [hψgt t htt, hdgt _ (hφgt t htJ htt), sub_add_cancel]
      exact heq t htJ
  have hψinit : ∀ t ∈ I, ∀ t'' ∈ I'', t'' ≤ ψ t → t'' ∈ ψ '' I := by
    intro t ht t'' ht'' hle
    rcases le_or_gt t'' t₀ with h | h
    · exact ⟨t'', hI''le t'' ht'' h, hψle t'' h⟩
    · have htt : t₀ < t := lt_of_not_ge fun h' => by rw [hψle t h'] at hle; linarith
      have htJ := hgtJ t ht htt.le
      rw [hψgt t htt] at hle
      obtain ⟨w, hw, hwz⟩ := hinit t htJ (t'' + δ) (hI''ge t'' ht'' h.le) (by linarith)
      have hwt : t₀ < w := hφgt' w hw (by rw [hwz, hφt₀]; linarith)
      exact ⟨w, hJI hw, by rw [hψgt w hwt, hwz]; ring⟩
  -- the new value
  have hφt' : φ t₀ < t' := hlt t₀ ht₀
  have hnewI'' : t' - δ ∈ I'' := Or.inr ⟨by rw [hφt₀] at hφt'; linarith, by
    rw [sub_add_cancel]; exact ht'⟩
  have hdnew : d (t' - δ) = c' t' := by
    rw [hdgt _ (by rw [hφt₀] at hφt'; linarith), sub_add_cancel]
  refine ⟨I'', d, hd_curve, ⟨ψ, hψmono, hψmaps, hψoc, hdψ, hψinit⟩,
    ⟨t' - δ, hnewI'', fun s hs => ?_⟩⟩
  rw [hdnew]
  by_cases hsJ : s ∈ J
  · exact hnew s hsJ
  · intro heqs
    have hst : s < t₀ := lt_of_not_ge fun h => hsJ (hgtJ s hs h)
    have h1 : C.le ⊤ (d s) (d t₀) := hd_curve.le_of_le (Or.inl ⟨hs, hst.le⟩) ht₀I'' hst.le
    have h2 : C.le ⊤ (d t₀) (d (t' - δ)) :=
      hd_curve.le_of_le ht₀I'' hnewI'' (by rw [hφt₀] at hφt'; linarith)
    rw [hdle s hst.le, hdle t₀ le_rfl] at h1
    rw [hdnew, heqs, hdle t₀ le_rfl] at h2
    exact hnew t₀ ht₀ (heqs.trans (hcaus h1 h2))

/-- **A component of a future-inextensible curve in an open set is future-inextensible there.**
`J ⊆ I` is the set of parameters joined to `t₀` inside `c⁻¹(U)`. If `J` is a final segment of
`I`, an extension in `U` splices into an extension of `c` (`futureExtensible_of_final`).
Otherwise `J` ends at a parameter `β ∈ I` with `c β ∉ U`, and an extension in `U` would have to
pass through `c β` (`M` Hausdorff): it is a limit of the extension at an interior parameter. -/
theorem not_futureExtensible_of_component [T2Space M] (hcaus : C.IsCausal) {U : Opens M}
    {I J : Set ℝ} {c : ℝ → M} {t₀ : ℝ} (hc : C.FutureInextensible ⊤ I c) (hJI : J ⊆ I)
    (ht₀ : t₀ ∈ J) (hJoc : J.OrdConnected) (hJU : ∀ t ∈ J, c t ∈ U)
    (hmax : ∀ t ∈ I, [[t₀, t]] ⊆ c ⁻¹' U → t ∈ J) : ¬ C.FutureExtensible U J c := by
  rintro ⟨I', c', hcurve, ⟨φ, hφ, hmaps, hoc, heq, hinit⟩, ⟨t', ht', hnew⟩⟩
  have hlt : ∀ t ∈ J, φ t < t' := fun t ht => lt_of_not_ge fun h => by
    obtain ⟨s, hs, hse⟩ := hinit t ht t' ht' h
    exact hnew s hs (hse ▸ heq s hs)
  by_cases hfin : ∀ t ∈ I, ∀ s ∈ J, s ≤ t → t ∈ J
  · exact hc.2 (futureExtensible_of_final hcaus hc.1 hJI ht₀ hfin (hcurve.mono_opens le_top) hφ
      hmaps hoc heq hinit ht' hlt hnew)
  push Not at hfin
  obtain ⟨T, hT, s, hs, hsT, hTJ⟩ := hfin
  have hJlt : ∀ j ∈ J, j < T := fun j hj =>
    lt_of_not_ge fun h => hTJ (hJoc.out hs hj ⟨hsT, h⟩)
  have hJne : J.Nonempty := ⟨t₀, ht₀⟩
  have hbdd : BddAbove J := ⟨T, fun j hj => (hJlt j hj).le⟩
  set β := sSup J with hβ
  have ht₀β : t₀ ≤ β := le_csSup hbdd ht₀
  have hβT : β ≤ T := csSup_le hJne fun j hj => (hJlt j hj).le
  have ht₀T : t₀ ≤ T := ht₀β.trans hβT
  have hIcc : Icc t₀ T ⊆ I := hc.1.ordConnected.out (hJI ht₀) hT
  have hβI : β ∈ I := hIcc ⟨ht₀β, hβT⟩
  have hcont : ContinuousOn c (Icc t₀ T) := hc.1.continuousOn_Icc (hJI ht₀) hT
  have hbelow : ∀ y, t₀ ≤ y → y < β → y ∈ J := fun y h1 h2 => by
    obtain ⟨j, hj, hyj⟩ := exists_lt_of_lt_csSup hJne h2
    exact hJoc.out ht₀ hj ⟨h1, hyj.le⟩
  have hnbhd : c β ∈ U → ∃ ε > 0, ∀ y ∈ Icc t₀ T, dist y β < ε → c y ∈ U := fun hβU => by
    have h : c ⁻¹' (U : Set M) ∈ 𝓝[Icc t₀ T] β :=
      hcont β ⟨ht₀β, hβT⟩ (U.isOpen.mem_nhds hβU)
    rw [Metric.mem_nhdsWithin_iff] at h
    obtain ⟨ε, hε, hsub⟩ := h
    exact ⟨ε, hε, fun y hy hyd => hsub ⟨hyd, hy⟩⟩
  have hβJ : β ∉ J := fun hβJ => by
    obtain ⟨ε, hε, hU⟩ := hnbhd (hJU β hβJ)
    have hβT' : β < T := hJlt β hβJ
    have hβx : β < min (β + ε / 2) T := lt_min (by linarith) hβT'
    have hxT : min (β + ε / 2) T ≤ T := min_le_right _ _
    have hxJ : min (β + ε / 2) T ∈ J := by
      refine hmax _ (hIcc ⟨ht₀β.trans hβx.le, hxT⟩) ?_
      rw [uIcc_of_le (ht₀β.trans hβx.le)]
      intro y hy
      rcases le_or_gt y β with hyβ | hyβ
      · exact hJU y (hJoc.out ht₀ hβJ ⟨hy.1, hyβ⟩)
      · refine hU y ⟨hy.1, hy.2.trans hxT⟩ ?_
        rw [Real.dist_eq, abs_of_pos (by linarith)]
        linarith [hy.2, min_le_left (β + ε / 2) T]
    exact absurd (le_csSup hbdd hxJ) (not_le.2 hβx)
  have hβt₀ : t₀ < β := lt_of_le_of_ne ht₀β fun h => hβJ (h ▸ ht₀)
  have hβU : c β ∉ U := fun hβU => by
    obtain ⟨ε, hε, hU⟩ := hnbhd hβU
    obtain ⟨j, hj, hjβ⟩ := exists_lt_of_lt_csSup hJne (show β - ε < β by linarith)
    have hmJ : max j t₀ ∈ J := by
      rcases le_total j t₀ with h | h
      · rw [max_eq_right h]; exact ht₀
      · rw [max_eq_left h]; exact hj
    refine hβJ (hmax β hβI ?_)
    rw [uIcc_of_le ht₀β]
    intro y hy
    rcases le_or_gt y (max j t₀) with hyj | hyj
    · exact hJU y (hJoc.out ht₀ hmJ ⟨hy.1, hyj⟩)
    · refine hU y ⟨hy.1, hy.2.trans hβT⟩ ?_
      rw [Real.dist_eq, abs_of_nonpos (by linarith [hy.2])]
      linarith [le_max_left j t₀]
  -- the extension passes through `c β`
  have hmaxJ : ∀ t < β, max t t₀ ∈ J := fun t ht =>
    hbelow _ (le_max_right _ _) (max_lt ht hβt₀)
  set f : ℝ → ℝ := fun t => φ (max t t₀) with hf
  have hfmono : MonotoneOn f (Iio β) := fun a ha b hb hab =>
    hφ.monotoneOn (hmaxJ a ha) (hmaxJ b hb) (max_le_max hab le_rfl)
  have hfmem : ∀ t < β, f t ∈ Icc (φ t₀) t' := fun t ht =>
    ⟨hφ.monotoneOn ht₀ (hmaxJ t ht) (le_max_right _ _), (hlt _ (hmaxJ t ht)).le⟩
  have hfbdd : BddAbove (f '' Iio β) := ⟨t', by
    rintro _ ⟨t, ht, rfl⟩; exact (hfmem t ht).2⟩
  have hlim : Tendsto f (𝓝[<] β) (𝓝 (sSup (f '' Iio β))) := hfmono.tendsto_nhdsLT hfbdd
  have hf₀ : f t₀ = φ t₀ := by simp only [hf, max_self]
  have hsmem : sSup (f '' Iio β) ∈ Icc (φ t₀) t' :=
    ⟨hf₀ ▸ le_csSup hfbdd ⟨t₀, hβt₀, rfl⟩,
      csSup_le ⟨f t₀, t₀, hβt₀, rfl⟩ fun _ ⟨t, ht, h⟩ => h ▸ (hfmem t ht).2⟩
  have hsI' : sSup (f '' Iio β) ∈ I' := hcurve.ordConnected.out (hmaps ht₀) ht' hsmem
  have hcont' : ContinuousOn c' (Icc (φ t₀) t') := hcurve.continuousOn_Icc (hmaps ht₀) ht'
  have h1 : Tendsto (c' ∘ f) (𝓝[<] β) (𝓝 (c' (sSup (f '' Iio β)))) :=
    (hcont' _ hsmem).tendsto.comp (tendsto_nhdsWithin_iff.2
      ⟨hlim, eventually_nhdsWithin_of_forall fun t ht => hfmem t ht⟩)
  have h2 : Tendsto (fun t => c (max t t₀)) (𝓝[<] β) (𝓝 (c β)) := by
    have hg : Tendsto (fun t => max t t₀) (𝓝[<] β) (𝓝[Icc t₀ T] β) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun t ht =>
        ⟨le_max_right _ _, max_le ((show t < β from ht).le.trans hβT) ht₀T⟩⟩
      have h : Tendsto (fun t => max t t₀) (𝓝 β) (𝓝 (max β t₀)) :=
        (continuous_id.max continuous_const).tendsto β
      rw [max_eq_left ht₀β] at h
      exact h.mono_left nhdsWithin_le_nhds
    exact (hcont β ⟨ht₀β, hβT⟩).tendsto.comp hg
  have heq' : (c' ∘ f) =ᶠ[𝓝[<] β] (fun t => c (max t t₀)) :=
    eventually_nhdsWithin_of_forall fun t ht => heq _ (hmaxJ t ht)
  have hlimeq := tendsto_nhds_unique (h1.congr' heq') h2
  exact hβU (hlimeq ▸ hcurve.mem hsI')

/-- **The component of an inextensible curve in an open set `U`, through a parameter whose point
lies in `U`, is an inextensible curve of `U`** (`M` causal and Hausdorff). The past end is the
future end of the reversed causality. -/
theorem inextensible_ordConnectedComponent [T2Space M] (hcaus : C.IsCausal) {U : Opens M}
    {I : Set ℝ} {c : ℝ → M} (hc : C.Inextensible ⊤ I c) {t₀ : ℝ} (ht₀ : t₀ ∈ I)
    (hU : c t₀ ∈ U) : C.Inextensible U (ordConnectedComponent (I ∩ c ⁻¹' U) t₀) c := by
  set J := ordConnectedComponent (I ∩ c ⁻¹' U) t₀
  have ht₀J : t₀ ∈ J := self_mem_ordConnectedComponent.2 ⟨ht₀, hU⟩
  have hJI : J ⊆ I := fun t ht => (ordConnectedComponent_subset ht).1
  have hJU : ∀ t ∈ J, c t ∈ U := fun t ht => (ordConnectedComponent_subset ht).2
  have hJoc : J.OrdConnected := inferInstance
  have hmax : ∀ t ∈ I, [[t₀, t]] ⊆ c ⁻¹' U → t ∈ J := fun t ht h =>
    mem_ordConnectedComponent.2 fun x hx => ⟨hc.1.ordConnected.uIcc_subset ht₀ ht hx, h hx⟩
  have hcurve : C.CausalCurveIn U J c := ⟨⟨t₀, ht₀J⟩, hJoc, fun a ha b hb =>
    CurveOn.restrict (hc.1.curve a (hJI ha) b (hJI hb)) le_rfl le_rfl le_top
      (fun t ht => hJU t (hJoc.out ha hb ht))⟩
  obtain ⟨hpast, hfut⟩ := inextensible_iff.1 hc
  refine inextensible_iff.2 ⟨⟨hcurve, ?_⟩,
    ⟨hcurve, not_futureExtensible_of_component hcaus hfut hJI ht₀J hJoc hJU hmax⟩⟩
  have hd : C.dual.FutureInextensible U (-J) (fun t => c (-t)) := by
    refine ⟨hcurve.reverse, not_futureExtensible_of_component (C := C.dual) (t₀ := -t₀)
      (dual_isCausal.2 hcaus) (dual_futureInextensible_iff.2 hpast) (fun t ht => hJI ht)
      (show - -t₀ ∈ J by rw [neg_neg]; exact ht₀J)
      ⟨fun x hx y hy z hz => show -z ∈ J from hJoc.out hy hx ⟨neg_le_neg hz.2, neg_le_neg hz.1⟩⟩
      (fun t ht => hJU _ ht) fun t ht h => ?_⟩
    refine hmax (-t) ht fun x hx => ?_
    have hx' : -x ∈ [[-t₀, t]] := by
      rcases mem_uIcc.1 hx with h' | h'
      · exact mem_uIcc.2 (Or.inr ⟨by linarith [h'.2], by linarith [h'.1]⟩)
      · exact mem_uIcc.2 (Or.inl ⟨by linarith [h'.2], by linarith [h'.1]⟩)
    have := h hx'
    simpa using this
  exact (dual_futureInextensible_iff.1 hd).2

/-- **The core of `lem:Cauchy_plongement_toutes`**, inside one spacetime. Let `U` be open and
`S₁, S₂ ⊆ U` Cauchy surfaces of `U`. If `S₁` is a Cauchy surface of `M`, so is `S₂`. An
inextensible curve `c` of `M` meets `S₁` at one point; its component through that point is an
inextensible curve of `U`, which meets `S₂`. Any other point of `c` on `S₂` lies on a component
meeting `S₁`, at the same point of `M`; `M` being causal, the curve does not leave `U` in
between, so the two components are one. -/
theorem IsCauchySurfaceOn.isCauchySurface_of_open [T2Space M] (hcaus : C.IsCausal)
    {U : Opens M} {S₁ S₂ : Set M} (hS₁ : S₁ ⊆ U) (hS₂ : S₂ ⊆ U)
    (h₁U : C.IsCauchySurfaceOn U S₁) (h₂U : C.IsCauchySurfaceOn U S₂)
    (h₁ : C.IsCauchySurface S₁) : C.IsCauchySurface S₂ := by
  intro I c hc
  obtain ⟨_, ⟨⟨t₁, ht₁, rfl⟩, hy⟩, huniq₁⟩ := h₁ I c hc
  obtain ⟨_, ⟨⟨t₂, ht₂, rfl⟩, hz⟩, huniq₂⟩ :=
    h₂U _ c (inextensible_ordConnectedComponent hcaus hc ht₁ (hS₁ hy))
  refine ⟨c t₂, ⟨⟨t₂, (ordConnectedComponent_subset ht₂).1, rfl⟩, hz⟩, ?_⟩
  rintro _ ⟨⟨t₃, ht₃, rfl⟩, hz'⟩
  obtain ⟨_, ⟨⟨t₄, ht₄, rfl⟩, hx⟩, -⟩ :=
    h₁U _ c (inextensible_ordConnectedComponent hcaus hc ht₃ (hS₂ hz'))
  have ht₄I : t₄ ∈ I := (ordConnectedComponent_subset ht₄).1
  have h41 : c t₄ = c t₁ := huniq₁ _ ⟨⟨t₄, ht₄I, rfl⟩, hx⟩
  have hseg : [[t₁, t₄]] ⊆ I ∩ c ⁻¹' U := by
    intro b hb
    have hbI : b ∈ I := hc.1.ordConnected.uIcc_subset ht₁ ht₄I hb
    refine ⟨hbI, ?_⟩
    have hcb : c b = c t₁ := by
      rcases mem_uIcc.1 hb with h | h
      · have h1 := hc.1.le_of_le ht₁ hbI h.1
        have h2 := hc.1.le_of_le hbI ht₄I h.2
        rw [h41] at h2
        exact hcaus h2 h1
      · have h1 := hc.1.le_of_le ht₄I hbI h.1
        have h2 := hc.1.le_of_le hbI ht₁ h.2
        rw [h41] at h1
        exact hcaus h2 h1
    rw [mem_preimage, hcb]; exact hS₁ hy
  have ht₃J : t₃ ∈ ordConnectedComponent (I ∩ c ⁻¹' U) t₁ :=
    mem_ordConnectedComponent.2 fun b hb => by
      rcases uIcc_subset_uIcc_union_uIcc hb with hb | hb
      · exact hseg hb
      · exact mem_ordConnectedComponent.1 ht₄ (uIcc_comm t₄ t₃ ▸ hb)
  exact huniq₂ _ ⟨⟨t₃, ht₃J, rfl⟩, hz'⟩

end Causality

/-! ### Cauchy embeddings and Cauchy extensions -/

/-- `def:cauchy_embedding_cauchy_extension`, abstractly: between globally hyperbolic spacetimes, an
injective abstract `𝕄≥0`-morphism carrying some Cauchy surface of `M` onto a Cauchy surface of
`N`. Then `(N, φ)` is a Cauchy extension of `M`. -/
structure IsCauchyEmbedding (C : Causality M) (D : Causality N) (φ : M → N) : Prop where
  globallyHyperbolic_source : C.GloballyHyperbolic
  globallyHyperbolic_target : D.GloballyHyperbolic
  isEMorphism : IsEMorphism C D φ
  injective : Injective φ
  exists_cauchy : ∃ S : Set M, C.IsCauchySurface S ∧ D.IsCauchySurface (φ '' S)

/-- `def:cauchy_embedding_cauchy_extension` for the inclusion of an open set `A` into an open set
`B` of one spacetime, both seen as spacetimes with the restricted causality (kb/0001): both are
globally hyperbolic, and some Cauchy surface of `A` is a Cauchy surface of `B`. That the inclusion
is an injective abstract morphism on `A` with values in `B` is not part of the definition: it holds
for every pair of open sets `A ≤ B` (`IsCauchyInclusion.isEMorphismOn_id`), the relations of the
open subsets of `A` being those of `M` restricted. -/
def IsCauchyInclusion (C : Causality M) (A B : Opens M) : Prop :=
  A ≤ B ∧ C.GloballyHyperbolicOn A ∧ C.GloballyHyperbolicOn B ∧
    ∃ S : Set M, S ⊆ A ∧ C.IsCauchySurfaceOn A S ∧ C.IsCauchySurfaceOn B S

/-- The inclusion of a Cauchy inclusion `A ≤ B` is an injective abstract morphism on `A` mapping
`A` into `B` (the identity of `M`, read on `A`). Only `A ≤ B` is used. -/
theorem IsCauchyInclusion.isEMorphismOn_id {A B : Opens M} (h : IsCauchyInclusion C A B) :
    IsEMorphismOn C C A id ∧ InjOn id (A : Set M) ∧ MapsTo id (A : Set M) B :=
  ⟨IsEMorphismOn.mono IsEMorphism.id le_top, injOn_id _, fun _ hx => h.1 hx⟩

/-- The image of a Cauchy embedding, as an open set. -/
def IsCauchyEmbedding.rangeOpens (h : IsCauchyEmbedding C D φ) : Opens N :=
  h.isEMorphism.imageOpens ⊤ le_rfl

@[simp] theorem IsCauchyEmbedding.coe_rangeOpens (h : IsCauchyEmbedding C D φ) :
    (h.rangeOpens : Set N) = range φ := by
  simp [rangeOpens, IsEMorphismOn.coe_imageOpens, image_univ]

/-- Cauchy surfaces of `M` are the Cauchy surfaces of the open set `φ(M)`, read through an
injective abstract morphism. -/
theorem IsEMorphism.isCauchySurface_iff (hφ : IsEMorphism C D φ) (hinj : Injective φ)
    (S : Set M) :
    C.IsCauchySurface S ↔ D.IsCauchySurfaceOn (hφ.imageOpens ⊤ le_rfl) (φ '' S) :=
  IsEMorphismOn.isCauchySurfaceOn_image_iff hφ hinj.injOn le_rfl rfl (fun _ _ => trivial)

/-- `lem:Cauchy_plongement_toutes`, **(i) ⇒ (ii)**: along an injective abstract morphism into a
causal Hausdorff spacetime, if the image of one Cauchy surface of `M` is a Cauchy surface of `N`,
the image of every Cauchy surface of `M` is. -/
theorem IsEMorphism.isCauchySurface_image [T2Space N] (hφ : IsEMorphism C D φ)
    (hinj : Injective φ) (hD : D.IsCausal) {S₁ S₂ : Set M} (h₁ : C.IsCauchySurface S₁)
    (h₁' : D.IsCauchySurface (φ '' S₁)) (h₂ : C.IsCauchySurface S₂) :
    D.IsCauchySurface (φ '' S₂) :=
  Causality.IsCauchySurfaceOn.isCauchySurface_of_open hD
    (image_mono (fun _ _ => trivial)) (image_mono (fun _ _ => trivial))
    ((hφ.isCauchySurface_iff hinj S₁).1 h₁) ((hφ.isCauchySurface_iff hinj S₂).1 h₂) h₁'

/-- `lem:Cauchy_plongement_toutes`: for an injective abstract morphism `φ : M → N` into a
causal Hausdorff spacetime, (i) some Cauchy surface of `M` has image a Cauchy surface of `N` iff
(ii) every one has. `hex`, the existence of a Cauchy surface of `M`, is what makes (ii) ⇒ (i)
non-vacuous; the paper has it from `theo:geroch_sing`. -/
theorem IsEMorphism.cauchy_plongement_toutes [T2Space N] (hφ : IsEMorphism C D φ)
    (hinj : Injective φ) (hD : D.IsCausal) (hex : ∃ S : Set M, C.IsCauchySurface S) :
    (∃ S : Set M, C.IsCauchySurface S ∧ D.IsCauchySurface (φ '' S)) ↔
      ∀ S : Set M, C.IsCauchySurface S → D.IsCauchySurface (φ '' S) := by
  constructor
  · rintro ⟨S₁, h₁, h₁'⟩ S₂ h₂
    exact hφ.isCauchySurface_image hinj hD h₁ h₁' h₂
  · intro h
    obtain ⟨S, hS⟩ := hex
    exact ⟨S, hS, h S hS⟩

/-- `lem:Cauchy_plongement_toutes` for a Cauchy embedding: the image of every Cauchy surface is a
Cauchy surface. -/
theorem IsCauchyEmbedding.isCauchySurface_image [T2Space N] (h : IsCauchyEmbedding C D φ)
    {S : Set M} (hS : C.IsCauchySurface S) : D.IsCauchySurface (φ '' S) := by
  obtain ⟨S₁, h₁, h₁'⟩ := h.exists_cauchy
  exact h.isEMorphism.isCauchySurface_image h.injective h.globallyHyperbolic_target.1 h₁ h₁' hS

/-! ### Witnesses on the timelike line -/

theorem timelikeLine_isCauchyEmbedding_id : IsCauchyEmbedding timelikeLine timelikeLine id :=
  ⟨timelikeLine_globallyHyperbolic, timelikeLine_globallyHyperbolic, IsEMorphism.id,
    injective_id, ⟨{0}, timelikeLine_isCauchySurface_zero, by
      rw [image_id]; exact timelikeLine_isCauchySurface_zero⟩⟩

/-- Non-triviality of `IsCauchyEmbedding`: the constant map is not one. -/
theorem not_isCauchyEmbedding_const :
    ¬ IsCauchyEmbedding timelikeLine timelikeLine (fun _ => (0 : ℝ)) :=
  fun h => not_isEMorphism_const h.isEMorphism

theorem timelikeLine_isCauchyInclusion_top : IsCauchyInclusion timelikeLine ⊤ ⊤ :=
  ⟨le_rfl, timelikeLine_globallyHyperbolic, timelikeLine_globallyHyperbolic, {0},
    fun _ _ => trivial, timelikeLine_isCauchySurface_zero, timelikeLine_isCauchySurface_zero⟩

/-- Non-triviality of `IsCauchyInclusion`: `ℝ` is not Cauchy-included in the empty set. -/
theorem not_timelikeLine_isCauchyInclusion_bot : ¬ IsCauchyInclusion timelikeLine ⊤ ⊥ :=
  fun h => by simpa using h.1 (show (0 : ℝ) ∈ (⊤ : Opens ℝ) from trivial)

/-- The hypotheses of `cauchy_plongement_toutes` are jointly satisfiable. -/
theorem timelikeLine_cauchy_plongement_toutes :
    ∀ S : Set ℝ, timelikeLine.IsCauchySurface S → timelikeLine.IsCauchySurface (id '' S) :=
  (IsEMorphism.cauchy_plongement_toutes IsEMorphism.id injective_id timelikeLine_isCausal
    ⟨{0}, timelikeLine_isCauchySurface_zero⟩).1
    ⟨{0}, timelikeLine_isCauchySurface_zero, by
      rw [image_id]; exact timelikeLine_isCauchySurface_zero⟩

theorem timelikeLine_curvesExtend : timelikeLine.CurvesExtend := fun _ _ _ _ _ =>
  ⟨univ, id, timelikeLine_inextensible_id, fun x _ => ⟨x, trivial, rfl⟩⟩

theorem timelikeLine_isGloballyHyperbolicOn_not :
    ¬ timelikeLineTop.GloballyHyperbolicOn ⊤ := fun h => timelikeLineTop_not_isCausal h.1

end Causal

/-! ### Past-inextensibility pulled back

Moved here from `Causal.FlrwType` by T-abs-sc-open-hoist, byte for byte under the same full
name. The block reopens the scope it was proved in: there `M` and its topology come before `N`
(`universe u v`, `variable {M : Type u} [TopologicalSpace M]`), and this module's own `variable`
line orders `M`, `N`, then their topologies, which would reorder the binders of the statement
(kb/0255). -/

namespace Causal

open Set Function TopologicalSpace Topology Filter

universe u v

variable {M : Type u} [TopologicalSpace M]

open Causality

namespace IsEMorphismOn

variable {N : Type v} [TopologicalSpace N] {C : Causality M} {D : Causality N} {W : Opens M}
  {φ : M → N}

/-- **Past-inextensibility is pulled back** along a morphism injective on `W`: a past-inextensible
curve of the image `U = φ(V)`, read through a left inverse, is past-inextensible in `V`. The
one-sided half of `inextensible_iff_invComp`, with the same proof. -/
theorem pastInextensible_invComp (h : IsEMorphismOn C D W φ) (hinj : InjOn φ W) {g : N → M}
    (hg : LeftInvOn g φ W) {V : Opens M} (hVW : V ≤ W) {U : Opens N}
    (hU : (U : Set N) = φ '' V) {I : Set ℝ} {e : ℝ → N} (he : D.PastInextensible U I e) :
    C.PastInextensible V I (g ∘ e) := by
  have hmaps : MapsTo φ V U := fun x hx => by
    show φ x ∈ (U : Set N); rw [hU]; exact mem_image_of_mem φ hx
  have hφg : ∀ t ∈ I, φ (g (e t)) = e t := fun t ht => (leftInvOn_image hg hVW hU (he.1.mem ht)).2
  refine ⟨h.causalCurveIn_invComp hg hVW hU he.1, ?_⟩
  rintro ⟨I', c', hc', ⟨ψ, h1, h2, h3, h4, h5⟩, ⟨t', ht', h6⟩⟩
  refine he.2 ⟨I', φ ∘ c', h.causalCurveIn_comp hVW hmaps hc',
    ⟨ψ, h1, h2, h3, fun t ht => ?_, h5⟩, ⟨t', ht', fun t ht heq => h6 t ht ?_⟩⟩
  · simp only [comp_apply]; rw [h4 t ht]; exact hφg t ht
  · refine hinj (hVW (hc'.mem ht')) (hVW (leftInvOn_image hg hVW hU (he.1.mem ht)).1) ?_
    simp only [comp_apply] at heq ⊢
    rw [heq, hφg t ht]

end IsEMorphismOn

end Causal
