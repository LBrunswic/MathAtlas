import Causal.CauchyDiamond
import Causal.Pushout
import Causal.LinesReachable

/-!
# Common sub-extensions and common over-extensions, abstractly

`def:common_sub_extension` — `ETT.tex:1914`. `lem:C_ext_connexe` — `ETT.tex:1932`.
`prop:Cauchy_pgcd` — `ETT.tex:1945`. `def:common_over_extension` — `ETT.tex:1970`. None is marked:
the definitions are read through the abstraction of `Causal.CauchyExtension`, and the
lemma and the proposition each rest on a tagged `sorry`.

> A common sub-extension of $M_1$ and $M_2$ is a singular flat spacetime $M$ equipped with Cauchy
> embeddings $M_0\rightarrow M$, $M\rightarrow M_1$ and $M\rightarrow M_2$ making the diagram
> commute. […] A common sub-extension $M$ is maximal if every morphism of common sub-extensions
> $M\rightarrow M'$ is bijective.

> If $A$ and $B$ are open subsets of $N$ containing $\phi(M)$ and such that the inclusions
> $\phi(M)\rightarrow A$ and $\phi(M)\rightarrow B$ are Cauchy embeddings, then $A\cap B$ is
> connected.

> There exists a common sub-extension $\pgcd$ of $M_1$ and $M_2$ which is maximal, and it is
> unique up to equivalence.

> a common over-extension $M$ is minimal if for every common over-extension $M'$ there is a
> morphism $M\rightarrow M'$.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| singular flat spacetimes, `𝕄≥0`-morphisms | ⚠ reading: topological spacetimes, `IsEMorphism` |
| rigidity (`rem:CBG_analytique`) | ⚠ named: `IsRigid`; not implied by the abstraction (`timelikeLine_not_isRigid`) |
| `M` connected (C_ext_connexe) | ✓ carried |
| `M₀` connected (Cauchy_pgcd): spacetimes are connected, `ETT.tex:1502`, `ETT.tex:1849` | ✓ carried (`[ConnectedSpace M₀]`, part of the setting) |
| carriers of sub- and over-extensions connected, `T2`, second countable (`ETT.tex:255`, `1502`) | ⚠ weakened: not required |
| `Σ ≅` factor of `M ≅ Σ × ℝ` | ⚠ named: a homeomorphism `ψ` |
| every point of `A ∩ B` on an inextensible curve | ⚠ named (model fact) |
| `N` causally arc-connected, curves extend | ⚠ named |

## SCOPE (disclosed)

* `lem:C_ext_connexe` is proved, with no `sorry`, from "`φ(Σ)` is a Cauchy surface of `A ∩ B`"
  carried as a named hypothesis (`c_ext_connexe_of_isCauchySurfaceOn`). `c_ext_connexe` itself
  takes that step from `isCauchySurfaceOn_inf`, whose uniqueness half is proved
  (`eq_of_mem_image_inter`) and whose existence half is the `sorry` `exists_mem_image_inf`. That
  `sorry`'d statement is posed in the abstract setting without the end-point and extension facts
  its obstruction names; its truth there is unestablished and it **may be false**, so
  `c_ext_connexe` is no better than it.
* `prop:Cauchy_pgcd` is stated and rests on a `sorry`; proved: the set `ℰ` (`IsPgcdCandidate`), the
  gluing step (`IsPgcdCandidate.eqOn`, `pgcdMap_eqOn`). Of the obstructions its `sorry` names, two
  are gaps in the paper's argument (φ injective, the Cauchy inclusion into the union) and two are
  obstructions of the abstraction only (no gluing axiom, kb/0014; no transport of global
  hyperbolicity along a local isomorphism without absolute minimality).
* **Rigidity.** `IsRigid` fails on the timelike line (`timelikeLine_not_isRigid`), a fact about the
  abstraction, not about the paper. It holds jointly with the Cauchy embedding and `ℰ`-membership
  hypotheses on the point space (`pointSpace_cauchy_pgcd_hypotheses`).
* **Carriers.** The carriers of `CommonSubExtension` and `CommonOverExtension` are arbitrary
  topological spaces with a causality in the universe of `M₀, M₁, M₂`: they are not required
  connected, Hausdorff or second countable, as the paper's singular flat spacetimes are. For
  sub-extensions the universe is harmless (the carrier injects into `M₁`); `IsMinimal` quantifies
  only over over-extensions in that universe, which are not bounded in size by `M₁` or `M₂`.
* `defi:ppcm`'s gluing (`Causal.Pushout`) closes the square and receives a unique map to every
  common over-extension under rigidity (`gluing_comm`, `exists_unique_desc`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Function

open scoped Interval

universe u v w

/-! ### Composition of abstract morphisms, rigidity -/

section General

variable {M : Type u} {N : Type v} {P : Type w} [TopologicalSpace M] [TopologicalSpace N]
  [TopologicalSpace P] {C : Causality M} {D : Causality N} {E : Causality P}

/-- Abstract morphisms compose. -/
theorem IsEMorphism.comp {f : M → N} {g : N → P} (hg : IsEMorphism D E g)
    (hf : IsEMorphism C D f) : IsEMorphism C E (g ∘ f) := by
  have hfc : Continuous f := by
    have := hf.continuousOn; rw [Opens.coe_top, continuousOn_univ] at this; exact this
  have hgc : Continuous g := by
    have := hg.continuousOn; rw [Opens.coe_top, continuousOn_univ] at this; exact this
  refine
    { continuousOn := (hgc.comp hfc).continuousOn
      isOpen_image := fun V _ => by
        rw [image_comp]; exact hg.isOpen_image (hf.imageOpens V le_top) le_top
      map_le := fun V U _ hmaps x y hxy =>
        hg.map_le (hf.imageOpens V le_top) U le_top
          (fun _ ⟨z, hz, hze⟩ => hze ▸ hmaps hz)
          (hf.map_le V (hf.imageOpens V le_top) le_top (fun z hz => ⟨z, hz, rfl⟩) hxy)
      map_lt := fun V U _ hmaps x y hxy =>
        hg.map_lt (hf.imageOpens V le_top) U le_top
          (fun _ ⟨z, hz, hze⟩ => hze ▸ hmaps hz)
          (hf.map_lt V (hf.imageOpens V le_top) le_top (fun z hz => ⟨z, hz, rfl⟩) hxy)
      locally := fun x _ => ?_ }
  obtain ⟨V₁, -, hx₁, hinj₁, hm₁⟩ := hf.locally x trivial
  obtain ⟨V₂, -, hx₂, hinj₂, hm₂⟩ := hg.locally (f x) trivial
  let V : Opens M := V₁ ⊓ ⟨f ⁻¹' V₂, V₂.isOpen.preimage hfc⟩
  refine ⟨V, le_top, ⟨hx₁, hx₂⟩, fun y hy z hz h => hinj₁ hy.1 hz.1 (hinj₂ hy.2 hz.2 h),
    fun V' hV' U hU y hy z hz => ?_⟩
  let U' : Opens N := hf.imageOpens V' le_top
  have hU'V₂ : U' ≤ V₂ := by rintro _ ⟨w, hw, rfl⟩; exact (hV' hw).2
  have hU' : (U : Set P) = g '' U' := by rw [hU, image_comp]; rfl
  have h1 := hm₁ V' (hV'.trans inf_le_left) U' rfl y hy z hz
  have h2 := hm₂ U' hU'V₂ U hU' (f y) ⟨y, hy, rfl⟩ (f z) ⟨z, hz, rfl⟩
  exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

/-- **Rigidity (`rem:CBG_analytique`), carried as a named hypothesis** (kb/0012): two abstract
morphisms defined on a connected open set and agreeing on a non-empty open subset of it agree on
it. The paper quotes it for `𝕄≥0`-morphisms from the analyticity of `(Isom(𝕄), 𝕄, 𝕄≥0)`; it is not
a consequence of the abstraction (`timelikeLine_not_isRigid`). -/
def IsRigid (C : Causality M) (D : Causality N) : Prop :=
  ∀ V : Opens M, IsConnected (V : Set M) → ∀ f g : M → N, IsEMorphismOn C D V f →
    IsEMorphismOn C D V g → ∀ O : Opens M, O ≤ V → (O : Set M).Nonempty → EqOn f g O →
      EqOn f g V

/-- Rigidity holds trivially into a subsingleton. -/
theorem isRigid_of_subsingleton [Subsingleton N] : IsRigid C D :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ => Subsingleton.elim _ _

end General

/-! ### Rigidity fails for the abstract morphisms of the timelike line -/

/-- An order automorphism of `ℝ` is an abstract morphism of the timelike line. -/
theorem OrderIso.isEMorphism_timelikeLine (e : ℝ ≃o ℝ) :
    IsEMorphism timelikeLine timelikeLine e := by
  have hrange : ∀ {x y : ℝ}, e '' Icc x y = Icc (e x) (e y) := fun {x y} => e.image_Icc x y
  refine
    { continuousOn := e.toHomeomorph.continuous.continuousOn
      isOpen_image := fun V _ => e.toHomeomorph.isOpenMap _ V.isOpen
      map_le := fun V U _ hmaps x y ⟨hxy, hsub⟩ => ⟨e.monotone hxy, by
        rw [← hrange]; exact (image_mono hsub).trans (image_subset_iff.2 hmaps)⟩
      map_lt := fun V U _ hmaps x y ⟨hxy, hsub⟩ => ⟨e.strictMono hxy, by
        rw [← hrange]; exact (image_mono hsub).trans (image_subset_iff.2 hmaps)⟩
      locally := fun x _ => ⟨⊤, le_rfl, trivial, e.injective.injOn, fun V' _ U hU y _ z _ => ?_⟩ }
  have hsub : Icc y z ⊆ (V' : Set ℝ) ↔ Icc (e y) (e z) ⊆ (U : Set ℝ) := by
    rw [hU, ← hrange, image_subset_image_iff e.injective]
  constructor
  · show (y ≤ z ∧ Icc y z ⊆ (V' : Set ℝ)) ↔ (e y ≤ e z ∧ Icc (e y) (e z) ⊆ (U : Set ℝ))
    rw [e.le_iff_le, hsub]
  · show (y < z ∧ Icc y z ⊆ (V' : Set ℝ)) ↔ (e y < e z ∧ Icc (e y) (e z) ⊆ (U : Set ℝ))
    rw [e.lt_iff_lt, hsub]

/-- The piecewise linear automorphism `x ↦ x` for `x ≤ 0`, `x ↦ 2x` for `x > 0`. -/
noncomputable def kinkIso : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective (fun x : ℝ => if x ≤ 0 then x else 2 * x)
    (by
      intro a b hab
      simp only
      split_ifs with ha hb hb <;> linarith)
    (by
      intro y
      rcases le_or_gt y 0 with hy | hy
      · exact ⟨y, by simp [hy]⟩
      · refine ⟨y / 2, ?_⟩
        show (if y / 2 ≤ 0 then y / 2 else 2 * (y / 2)) = y
        rw [if_neg (by intro h; linarith)]
        ring)

theorem kinkIso_apply (x : ℝ) : kinkIso x = if x ≤ 0 then x else 2 * x := rfl

/-- **Non-triviality of `IsRigid`: rigidity is not a consequence of the abstraction.** The
identity and `kinkIso` are abstract morphisms of the timelike line agreeing on `]-∞, 0[` and
differing at `1`. -/
theorem timelikeLine_not_isRigid : ¬ IsRigid timelikeLine timelikeLine := by
  intro h
  have := h ⊤ (by rw [Opens.coe_top]; exact isConnected_univ) id kinkIso IsEMorphism.id
    (OrderIso.isEMorphism_timelikeLine kinkIso) ⟨Iio 0, isOpen_Iio⟩ le_top
    ⟨-1, show (-1 : ℝ) < 0 by norm_num⟩
    (fun x (hx : x < 0) => by
      show x = kinkIso x
      rw [kinkIso_apply, if_pos hx.le])
    (show (1 : ℝ) ∈ ((⊤ : Opens ℝ) : Set ℝ) from trivial)
  have h1 : kinkIso 1 = 2 := by
    rw [kinkIso_apply, if_neg (by norm_num)]; norm_num
  rw [h1] at this
  norm_num at this

/-! ### `def:common_sub_extension` -/

section SubExtension

variable {M₀ M₁ M₂ : Type u} [TopologicalSpace M₀] [TopologicalSpace M₁] [TopologicalSpace M₂]
  {C₀ : Causality M₀} {C₁ : Causality M₁} {C₂ : Causality M₂} {i₁ : M₀ → M₁} {i₂ : M₀ → M₂}

variable (C₀ C₁ C₂ i₁ i₂) in
/-- `def:common_sub_extension`, abstractly: a spacetime `X` with Cauchy embeddings
`a : M₀ → X`, `b : X → M₁`, `c : X → M₂` such that `b ∘ a = i₁` and `c ∘ a = i₂`. The carrier lives
in the universe of `M₀, M₁, M₂` (harmless: it injects into `M₁`), and is **not** required
connected, Hausdorff or second countable, as a singular flat spacetime is (`ETT.tex:255`,
`ETT.tex:1502`). -/
structure CommonSubExtension where
  carrier : Type u
  [top : TopologicalSpace carrier]
  causality : Causality carrier
  a : M₀ → carrier
  b : carrier → M₁
  c : carrier → M₂
  ha : IsCauchyEmbedding C₀ causality a
  hb : IsCauchyEmbedding causality C₁ b
  hc : IsCauchyEmbedding causality C₂ c
  comm₁ : b ∘ a = i₁
  comm₂ : c ∘ a = i₂

attribute [instance] CommonSubExtension.top

namespace CommonSubExtension

/-- `def:common_sub_extension`: a morphism of common sub-extensions, an abstract morphism commuting
with the embeddings into `M₁` and `M₂`. -/
def IsMorphism (X Y : CommonSubExtension C₀ C₁ C₂ i₁ i₂) (f : X.carrier → Y.carrier) : Prop :=
  IsEMorphism X.causality Y.causality f ∧ Y.b ∘ f = X.b ∧ Y.c ∘ f = X.c

/-- `def:common_sub_extension`: equivalent common sub-extensions — a bijective morphism. -/
def Equivalent (X Y : CommonSubExtension C₀ C₁ C₂ i₁ i₂) : Prop :=
  ∃ f, X.IsMorphism Y f ∧ Bijective f

/-- `def:common_sub_extension`: a maximal common sub-extension — every morphism from it is
bijective. -/
def IsMaximal (X : CommonSubExtension C₀ C₁ C₂ i₁ i₂) : Prop :=
  ∀ (Y : CommonSubExtension C₀ C₁ C₂ i₁ i₂) (f : X.carrier → Y.carrier), X.IsMorphism Y f →
    Bijective f

theorem isMorphism_id (X : CommonSubExtension C₀ C₁ C₂ i₁ i₂) : X.IsMorphism X id :=
  ⟨IsEMorphism.id, rfl, rfl⟩

theorem equivalent_refl (X : CommonSubExtension C₀ C₁ C₂ i₁ i₂) : X.Equivalent X :=
  ⟨id, X.isMorphism_id, bijective_id⟩

/-- The identity of `M₀` is a Cauchy embedding as soon as `M₀` has a Cauchy extension. -/
theorem _root_.Causal.IsCauchyEmbedding.isCauchyEmbedding_id {N : Type v} [TopologicalSpace N]
    {D : Causality N} {φ : M₀ → N} (h : IsCauchyEmbedding C₀ D φ) :
    IsCauchyEmbedding C₀ C₀ id := by
  obtain ⟨S, hS, -⟩ := h.exists_cauchy
  exact ⟨h.globallyHyperbolic_source, h.globallyHyperbolic_source, IsEMorphism.id, injective_id,
    ⟨S, hS, by rw [image_id]; exact hS⟩⟩

/-- **Sanity: the trivial common sub-extension `M₀` itself.** -/
def base (h₁ : IsCauchyEmbedding C₀ C₁ i₁) (h₂ : IsCauchyEmbedding C₀ C₂ i₂) :
    CommonSubExtension C₀ C₁ C₂ i₁ i₂ where
  carrier := M₀
  causality := C₀
  a := id
  b := i₁
  c := i₂
  ha := h₁.isCauchyEmbedding_id
  hb := h₁
  hc := h₂
  comm₁ := rfl
  comm₂ := rfl

/-- **Sanity of `IsMaximal`**: when `i₁` is bijective, the trivial common sub-extension is
maximal. -/
theorem base_isMaximal (h₁ : IsCauchyEmbedding C₀ C₁ i₁) (h₂ : IsCauchyEmbedding C₀ C₂ i₂)
    (hbij : Bijective i₁) : (base h₁ h₂).IsMaximal := by
  rintro Y f ⟨-, hb, -⟩
  have hb' : ∀ x, Y.b (f x) = i₁ x := fun x => congrFun hb x
  refine ⟨fun x y hxy => hbij.1 (by rw [← hb', ← hb', hxy]), fun y => ?_⟩
  obtain ⟨x, hx⟩ := hbij.2 (Y.b y)
  exact ⟨x, Y.hb.injective (by rw [hb', hx])⟩

/-- The hypotheses are jointly satisfiable: the timelike line is a maximal common sub-extension
of itself, along the identities. -/
theorem timelikeLine_base_isMaximal :
    (base (C₀ := timelikeLine) timelikeLine_isCauchyEmbedding_id
      timelikeLine_isCauchyEmbedding_id).IsMaximal :=
  base_isMaximal _ _ bijective_id

end CommonSubExtension

/-! ### `lem:C_ext_connexe` -/

variable {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
  {C : Causality M} {D : Causality N} {φ : M → N}

/-- A Cauchy surface is connected when `M` is and the splitting of `theo:geroch_sing` exists. -/
theorem isConnected_of_homeomorph [ConnectedSpace M] {S : Set M}
    (ψ : S × ℝ ≃ₜ M) : IsConnected S := by
  have h : (fun m => ((ψ.symm m).1 : M)) '' univ = S := by
    ext x
    constructor
    · rintro ⟨m, -, rfl⟩; exact (ψ.symm m).1.2
    · intro hx
      refine ⟨ψ (⟨x, hx⟩, 0), trivial, ?_⟩
      simp
  rw [← h]
  exact isConnected_univ.image _
    ((continuous_subtype_val.comp (continuous_fst.comp ψ.symm.continuous)).continuousOn)

/-- **The topological core of `lem:C_ext_connexe`**: if every point of the open set `U` lies on an
inextensible causal curve of `U` meeting the connected set `T ⊆ U`, then `U` is connected. -/
theorem isConnected_of_curves {U : Opens N} {T : Set N} (hT : IsConnected T)
    (hTU : T ⊆ U) (hcurve : ∀ x ∈ U, ∃ (I : Set ℝ) (c : ℝ → N), D.Inextensible U I c ∧
      x ∈ c '' I ∧ (c '' I ∩ T).Nonempty) : IsConnected (U : Set N) := by
  obtain ⟨x₀, hx₀⟩ := hT.nonempty
  refine ⟨⟨x₀, hTU hx₀⟩, isPreconnected_of_forall x₀ fun y hy => ?_⟩
  obtain ⟨I, c, hc, ⟨t₁, ht₁, rfl⟩, ⟨_, ⟨t₂, ht₂, rfl⟩, hT₂⟩⟩ := hcurve y hy
  have hsub : [[t₁, t₂]] ⊆ I := hc.1.ordConnected.uIcc_subset ht₁ ht₂
  have hcont : ContinuousOn c [[t₁, t₂]] := by
    rw [uIcc]
    exact hc.1.continuousOn_Icc (hsub (by simp [uIcc])) (hsub (by simp [uIcc]))
  refine ⟨T ∪ c '' [[t₁, t₂]], union_subset hTU ?_, Or.inl hx₀,
    Or.inr ⟨t₁, left_mem_uIcc, rfl⟩, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩; exact hc.1.mem (hsub ht)
  · exact hT.isPreconnected.union (c t₂) hT₂ ⟨t₂, right_mem_uIcc, rfl⟩
      (isPreconnected_uIcc.image c hcont)

/-- In `lem:C_ext_connexe`, a causal curve of any open set meets `φ(Σ)` at most once: `φ(Σ)` is a
Cauchy surface of `N` (`lem:Cauchy_plongement_toutes`), hence acausal when curves of `N` extend. -/
theorem IsCauchyEmbedding.eq_of_mem_image_inter [T2Space N] (hφ : IsCauchyEmbedding C D φ)
    {S : Set M} (hS : C.IsCauchySurface S) (hDac : D.CausallyArcConnected)
    (hDext : D.CurvesExtend) {W : Opens N} {I : Set ℝ} {c : ℝ → N} (hc : D.CausalCurveIn W I c) :
    ∀ x ∈ c '' I ∩ φ '' S, ∀ y ∈ c '' I ∩ φ '' S, x = y := by
  have hac : D.IsAcausal (φ '' S) := (hφ.isCauchySurface_image hS).isAcausal hDac hDext
  rintro _ ⟨⟨s, hs, rfl⟩, hxS⟩ _ ⟨⟨t, ht, rfl⟩, hyS⟩
  rcases le_total s t with h | h
  · exact hac _ hxS _ hyS (D.le_mono le_top (hc.le_of_le hs ht h))
  · exact (hac _ hyS _ hxS (D.le_mono le_top (hc.le_of_le ht hs h))).symm

/-- **The step of `lem:C_ext_connexe` the paper asserts without proof**, existence half: every
inextensible causal curve of `A ∩ B` meets `φ(Σ)` ("the map `M → A ∩ B` is a Cauchy embedding").
**This abstract statement may be false**: it is posed without the facts (1)–(3) its `sorry`
names, which hold for Lorentzian manifolds but are neither proved nor assumed for topological
spacetimes. Nothing here establishes its truth in the abstract setting. -/
theorem IsCauchyEmbedding.exists_mem_image_inf [T2Space N] (hφ : IsCauchyEmbedding C D φ)
    {A B : Opens N} (hA : IsCauchyInclusion D hφ.rangeOpens A)
    (hB : IsCauchyInclusion D hφ.rangeOpens B) {S : Set M} (hS : C.IsCauchySurface S)
    {I : Set ℝ} {c : ℝ → N} (hc : D.Inextensible (A ⊓ B) I c) : (c '' I ∩ φ '' S).Nonempty := by
  sorry -- SORRY(lem:C_ext_connexe): an inextensible causal curve of `A ∩ B` is in general extensible in `A` and in `B`; that it meets `φ(Σ)` needs (1) every causal curve of `A` (resp. `B`) over an interval to lie on an inextensible one of `A` (`CurvesExtend` relative to an open set, a Zorn-type existence), (2) the two extensions to leave `A ∩ B` through one end point, which needs that end point to exist in `A` and in `B` (a limit along the curve) and to be unique (Hausdorff), and (3) at an end point in `A ∩ B`, a short causal curve inside `A ∩ B` (`J^±_{A∩B}(p) ≠ {p}` with local causal arc-connectedness). None of the three is proved for topological spacetimes nor carried here as a hypothesis, and the paper gives no argument; in this abstract setting the statement may be false (its truth is unestablished), and `c_ext_connexe` rests on it — its sorry-free core is `c_ext_connexe_of_isCauchySurfaceOn`

/-- "`φ(Σ)` is a Cauchy surface of `A ∩ B`" (`ETT.tex:1940–1941`): uniqueness is proved
(`eq_of_mem_image_inter`), existence is the paper's unproved step (`exists_mem_image_inf`). -/
theorem IsCauchyEmbedding.isCauchySurfaceOn_inf [T2Space N] (hφ : IsCauchyEmbedding C D φ)
    {A B : Opens N} (hA : IsCauchyInclusion D hφ.rangeOpens A)
    (hB : IsCauchyInclusion D hφ.rangeOpens B) {S : Set M} (hS : C.IsCauchySurface S)
    (hDac : D.CausallyArcConnected) (hDext : D.CurvesExtend) :
    D.IsCauchySurfaceOn (A ⊓ B) (φ '' S) := by
  intro I c hc
  obtain ⟨x, hx⟩ := hφ.exists_mem_image_inf hA hB hS hc
  exact ⟨x, hx, fun y hy => hφ.eq_of_mem_image_inter hS hDac hDext hc.1 y hy x hx⟩

/-- **`lem:C_ext_connexe` from the paper's unargued step, carried as a named hypothesis**, with no
`sorry`: `M` connected, `φ` a Cauchy extension, `A, B` open sets of `N` into which the inclusions
of `φ(M)` are Cauchy embeddings, and `φ(Σ)` a Cauchy surface of `A ∩ B` (`ETT.tex:1940–1941`,
asserted there without argument); then `A ∩ B` is connected. Further named hypotheses: the
splitting `ψ` of `theo:geroch_sing` (for the connectedness of `Σ`) and, as a model fact, that
every point of `A ∩ B` lies on an inextensible causal curve of `A ∩ B`. -/
theorem IsCauchyEmbedding.c_ext_connexe_of_isCauchySurfaceOn [ConnectedSpace M]
    (hφ : IsCauchyEmbedding C D φ) {A B : Opens N} (hA : IsCauchyInclusion D hφ.rangeOpens A)
    (hB : IsCauchyInclusion D hφ.rangeOpens B) {S : Set M} (ψ : S × ℝ ≃ₜ M)
    (hcauchy : D.IsCauchySurfaceOn (A ⊓ B) (φ '' S))
    (hthrough : ∀ x ∈ A ⊓ B, ∃ (I : Set ℝ) (c : ℝ → N), D.Inextensible (A ⊓ B) I c ∧ x ∈ c '' I) :
    IsConnected ((A ⊓ B : Opens N) : Set N) := by
  have hφc : Continuous φ := by
    have := hφ.isEMorphism.continuousOn; rw [Opens.coe_top, continuousOn_univ] at this
    exact this
  have hT : IsConnected (φ '' S) := (isConnected_of_homeomorph ψ).image φ hφc.continuousOn
  have hTU : φ '' S ⊆ ((A ⊓ B : Opens N) : Set N) := by
    rintro _ ⟨x, -, rfl⟩
    have hx : φ x ∈ hφ.rangeOpens := by
      show φ x ∈ (hφ.rangeOpens : Set N); rw [IsCauchyEmbedding.coe_rangeOpens]; exact ⟨x, rfl⟩
    exact ⟨hA.1 hx, hB.1 hx⟩
  refine isConnected_of_curves (D := D) hT hTU fun x hx => ?_
  obtain ⟨I, c, hc, hxc⟩ := hthrough x hx
  obtain ⟨z, hz, -⟩ := hcauchy I c hc
  exact ⟨I, c, hc, hxc, z, hz⟩

/-- `lem:C_ext_connexe`, abstractly: `M` connected, `φ` a Cauchy extension, `A, B` open sets of
`N` into which the inclusions of `φ(M)` are Cauchy embeddings; then `A ∩ B` is connected. Named
hypotheses: the splitting `ψ` of `theo:geroch_sing` (for the connectedness of `Σ`) and, as a
model fact, that every point of `A ∩ B` lies on an inextensible causal curve of `A ∩ B`. The
proof rests on `isCauchySurfaceOn_inf`, hence on the `sorry` `exists_mem_image_inf`, whose
abstract statement may be false; the sorry-free core is `c_ext_connexe_of_isCauchySurfaceOn`. -/
theorem IsCauchyEmbedding.c_ext_connexe [T2Space N] [ConnectedSpace M]
    (hφ : IsCauchyEmbedding C D φ) {A B : Opens N} (hA : IsCauchyInclusion D hφ.rangeOpens A)
    (hB : IsCauchyInclusion D hφ.rangeOpens B) {S : Set M} (hS : C.IsCauchySurface S)
    (ψ : S × ℝ ≃ₜ M) (hDac : D.CausallyArcConnected) (hDext : D.CurvesExtend)
    (hthrough : ∀ x ∈ A ⊓ B, ∃ (I : Set ℝ) (c : ℝ → N), D.Inextensible (A ⊓ B) I c ∧ x ∈ c '' I) :
    IsConnected ((A ⊓ B : Opens N) : Set N) :=
  hφ.c_ext_connexe_of_isCauchySurfaceOn hA hB ψ (hφ.isCauchySurfaceOn_inf hA hB hS hDac hDext)
    hthrough

/-! ### `prop:Cauchy_pgcd` -/

/-- The set `ℰ` of the proof of `prop:Cauchy_pgcd` (`ETT.tex:1952–1956`), indexed by open sets of
`M₁` (kb/0001): an open `W ⊇ i₁(M₀)` into which the inclusion of `i₁(M₀)` is a Cauchy embedding (a),
with an abstract morphism `f` on `W` such that `f ∘ i₁ = i₂` (b). As printed, (b) does not ask `f`
injective (the WP-4 finding). -/
def IsPgcdCandidate (h₁ : IsCauchyEmbedding C₀ C₁ i₁) (C₂ : Causality M₂) (i₂ : M₀ → M₂)
    (W : Opens M₁) (f : M₁ → M₂) : Prop :=
  IsCauchyInclusion C₁ h₁.rangeOpens W ∧ IsEMorphismOn C₁ C₂ W f ∧ f ∘ i₁ = i₂

/-- **The gluing step of `prop:Cauchy_pgcd`**: two elements of `ℰ` agree on the intersection of
their open sets, by rigidity, as soon as that intersection is connected (which the paper takes
from `lem:C_ext_connexe`). -/
theorem IsPgcdCandidate.eqOn (h₁ : IsCauchyEmbedding C₀ C₁ i₁) (hrig : IsRigid C₁ C₂)
    [Nonempty M₀] {W W' : Opens M₁} {f f' : M₁ → M₂} (h : IsPgcdCandidate h₁ C₂ i₂ W f)
    (h' : IsPgcdCandidate h₁ C₂ i₂ W' f') (hconn : IsConnected ((W ⊓ W' : Opens M₁) : Set M₁)) :
    EqOn f f' (W ⊓ W' : Opens M₁) := by
  refine hrig (W ⊓ W') hconn f f' (h.2.1.mono inf_le_left) (h'.2.1.mono inf_le_right)
    h₁.rangeOpens (le_inf h.1.1 h'.1.1) ?_ ?_
  · obtain ⟨x⟩ := ‹Nonempty M₀›
    exact ⟨i₁ x, by rw [IsCauchyEmbedding.coe_rangeOpens]; exact ⟨x, rfl⟩⟩
  · intro y hy
    rw [IsCauchyEmbedding.coe_rangeOpens] at hy
    obtain ⟨x, rfl⟩ := hy
    exact (congrFun h.2.2 x).trans (congrFun h'.2.2 x).symm

/-- The union `M₁ ∧ M₂ := ⋃_{(M, φ_M) ∈ ℰ} M`. -/
def pgcdOpens (h₁ : IsCauchyEmbedding C₀ C₁ i₁) (C₂ : Causality M₂) (i₂ : M₀ → M₂) : Opens M₁ :=
  ⨆ p : {p : Opens M₁ × (M₁ → M₂) // IsPgcdCandidate h₁ C₂ i₂ p.1 p.2}, p.1.1

/-- The glued map `φ` on `M₁ ∧ M₂`: at `x`, the value of some element of `ℰ` whose open set
contains `x`. -/
noncomputable def pgcdMap [Nonempty M₂] (h₁ : IsCauchyEmbedding C₀ C₁ i₁) (C₂ : Causality M₂)
    (i₂ : M₀ → M₂) (x : M₁) : M₂ := by
  classical
  exact if hx : ∃ p : Opens M₁ × (M₁ → M₂), IsPgcdCandidate h₁ C₂ i₂ p.1 p.2 ∧ x ∈ p.1
    then (Classical.choose hx).2 x else Classical.arbitrary M₂

/-- **`φ` is well defined** (`ETT.tex:1958–1962`): under rigidity, and connectedness of the
pairwise intersections, the glued map agrees with every element of `ℰ` on its open set. -/
theorem pgcdMap_eqOn [Nonempty M₀] [Nonempty M₂] (h₁ : IsCauchyEmbedding C₀ C₁ i₁)
    (hrig : IsRigid C₁ C₂)
    (hconn : ∀ W W' f f', IsPgcdCandidate h₁ C₂ i₂ W f → IsPgcdCandidate h₁ C₂ i₂ W' f' →
      IsConnected ((W ⊓ W' : Opens M₁) : Set M₁))
    {W : Opens M₁} {f : M₁ → M₂} (h : IsPgcdCandidate h₁ C₂ i₂ W f) :
    EqOn (pgcdMap h₁ C₂ i₂) f W := by
  intro x hx
  have hex : ∃ p : Opens M₁ × (M₁ → M₂), IsPgcdCandidate h₁ C₂ i₂ p.1 p.2 ∧ x ∈ p.1 :=
    ⟨(W, f), h, hx⟩
  simp only [pgcdMap, dif_pos hex]
  obtain ⟨hp, hxp⟩ := Classical.choose_spec hex
  exact IsPgcdCandidate.eqOn h₁ hrig hp h (hconn _ _ _ _ hp h) ⟨hxp, hx⟩

theorem subset_pgcdOpens (h₁ : IsCauchyEmbedding C₀ C₁ i₁) {W : Opens M₁} {f : M₁ → M₂}
    (h : IsPgcdCandidate h₁ C₂ i₂ W f) : W ≤ pgcdOpens h₁ C₂ i₂ :=
  le_iSup (fun p : {p : Opens M₁ × (M₁ → M₂) // IsPgcdCandidate h₁ C₂ i₂ p.1 p.2} => p.1.1)
    ⟨(W, f), h⟩

/-- Sanity: on the timelike line, along the identities, `(ℝ, id)` is an element of `ℰ`. -/
theorem timelikeLine_rangeOpens_id : timelikeLine_isCauchyEmbedding_id.rangeOpens = ⊤ :=
  SetLike.coe_injective (by rw [IsCauchyEmbedding.coe_rangeOpens, range_id, Opens.coe_top])

theorem timelikeLine_isPgcdCandidate :
    IsPgcdCandidate timelikeLine_isCauchyEmbedding_id timelikeLine id ⊤ id := by
  refine ⟨?_, IsEMorphism.id, rfl⟩
  rw [timelikeLine_rangeOpens_id]
  exact timelikeLine_isCauchyInclusion_top

/-- The hypotheses of `c_ext_connexe` are jointly satisfiable: the timelike line, `φ = id`,
`A = B = ℝ`, `Σ = {0}` with its splitting. -/
theorem timelikeLine_c_ext_connexe_hypotheses :
    IsCauchyInclusion timelikeLine timelikeLine_isCauchyEmbedding_id.rangeOpens ⊤ ∧
      timelikeLine.IsCauchySurface {0} ∧ timelikeLine.CausallyArcConnected ∧
      timelikeLine.CurvesExtend ∧
      ∀ x ∈ (⊤ ⊓ ⊤ : Opens ℝ), ∃ (I : Set ℝ) (c : ℝ → ℝ),
        timelikeLine.Inextensible (⊤ ⊓ ⊤) I c ∧ x ∈ c '' I := by
  refine ⟨by rw [timelikeLine_rangeOpens_id]; exact timelikeLine_isCauchyInclusion_top,
    timelikeLine_isCauchySurface_zero, timelikeLine_causallyArcConnected,
    timelikeLine_curvesExtend, fun x _ => ⟨univ, id, ?_, x, trivial, rfl⟩⟩
  rw [inf_idem]
  exact timelikeLine_inextensible_id

/-! ### Rigidity is jointly satisfiable with the hypotheses of `prop:Cauchy_pgcd` -/

/-- The point space: `Unit` with the causality whose causal relation on an open `U` relates any
two points of `U`, and whose chronological relation is empty (`Causality.ofRelation`). -/
def pointSpace : Causality Unit :=
  Causality.ofRelation (fun _ _ => True) (fun _ _ => False) (fun _ => trivial)
    (fun _ _ _ _ _ => trivial) (fun _ _ _ h _ => h) (fun _ _ _ => trivial)
    (fun _ => by simp) (fun _ => by simp)

theorem pointSpace_globallyHyperbolic : pointSpace.GloballyHyperbolic :=
  ⟨fun x y _ _ => Subsingleton.elim x y, fun _ _ => (Set.toFinite _).isCompact⟩

theorem pointSpace_isCauchySurface_univ : pointSpace.IsCauchySurface univ := by
  intro I c hc
  obtain ⟨t, ht⟩ := hc.1.nonempty
  exact ⟨c t, ⟨⟨t, ht, rfl⟩, trivial⟩, fun y _ => Subsingleton.elim _ _⟩

theorem pointSpace_isCauchyEmbedding_id : IsCauchyEmbedding pointSpace pointSpace id :=
  ⟨pointSpace_globallyHyperbolic, pointSpace_globallyHyperbolic, IsEMorphism.id, injective_id,
    ⟨univ, pointSpace_isCauchySurface_univ, by
      rw [image_id]; exact pointSpace_isCauchySurface_univ⟩⟩

theorem pointSpace_rangeOpens_id : pointSpace_isCauchyEmbedding_id.rangeOpens = ⊤ :=
  SetLike.coe_injective (by rw [IsCauchyEmbedding.coe_rangeOpens, range_id, Opens.coe_top])

/-- **`IsRigid` is jointly satisfiable with the hypotheses of `cauchy_pgcd` and with membership in
`ℰ`** (kb/0011): on the point space, along the identities, `M₀ = M₁ = M₂ = Unit` is connected and
Hausdorff, `id` is a Cauchy embedding, rigidity holds, and `(⊤, id) ∈ ℰ`. The witness is
degenerate (a point), and rigidity holds there only because the target is a subsingleton; it
shows the hypothesis set is consistent, not that it is rich. -/
theorem pointSpace_cauchy_pgcd_hypotheses :
    ConnectedSpace Unit ∧ T2Space Unit ∧ IsCauchyEmbedding pointSpace pointSpace id ∧
      IsRigid pointSpace pointSpace ∧
      IsPgcdCandidate pointSpace_isCauchyEmbedding_id pointSpace id ⊤ id := by
  refine ⟨inferInstance, inferInstance, pointSpace_isCauchyEmbedding_id, isRigid_of_subsingleton,
    ?_, IsEMorphism.id, rfl⟩
  rw [pointSpace_rangeOpens_id]
  exact ⟨le_rfl, Causality.globallyHyperbolicOn_top.2 pointSpace_globallyHyperbolic,
    Causality.globallyHyperbolicOn_top.2 pointSpace_globallyHyperbolic, univ,
    fun _ _ => trivial, pointSpace_isCauchySurface_univ, pointSpace_isCauchySurface_univ⟩

/-- `prop:Cauchy_pgcd`, abstractly, with rigidity (`rem:CBG_analytique`) as a named
hypothesis: two Cauchy extensions of `M₀` have a maximal common sub-extension, unique up to
equivalence. `M₀` is connected, as every spacetime of the section is (`ETT.tex:1849`,
`def:singular_spacetime` at `ETT.tex:1502`): part of the setting, not a strengthening. -/
theorem cauchy_pgcd [ConnectedSpace M₀] [T2Space M₁] [T2Space M₂] (h₁ : IsCauchyEmbedding C₀ C₁ i₁)
    (h₂ : IsCauchyEmbedding C₀ C₂ i₂) (hrig : IsRigid C₁ C₂) :
    (∃ X : CommonSubExtension C₀ C₁ C₂ i₁ i₂, X.IsMaximal) ∧
      ∀ X Y : CommonSubExtension C₀ C₁ C₂ i₁ i₂, X.IsMaximal → Y.IsMaximal → X.Equivalent Y := by
  sorry -- SORRY(prop:Cauchy_pgcd): the step "(∧, φ) ∈ ℰ, hence ∧ is a common sub-extension" is not argued in the paper on two points: (1) condition (b) of ℰ does not ask φ_M injective and nothing shows φ injective, so ∧ → M₂ is not shown to be a Cauchy embedding (WP-4; a gap in the argument, not a refutation: injectivity is plausibly recoverable); (2) the inclusion of i₁(M₀) into the union ∧ = ⋃ M is not shown to be a Cauchy embedding: neither the global hyperbolicity of ∧ nor that i₁(Σ₀) meets every inextensible curve of ∧ follows from the same facts for each M. Two further obstructions belong to the abstraction, not to the paper's proof: (3) the library's causality has no gluing axiom (kb/0014), so the strong-morphism condition of φ on ∧ does not follow from its restrictions to the M; (4) maximality and uniqueness need (b(N), c ∘ b⁻¹) ∈ ℰ for a common sub-extension (N, a, b, c), i.e. b(N) with the causality restricted from M₁ globally hyperbolic, which a local isomorphism of non-local causalities does not transport without absolute minimality. The gluing step also uses lem:C_ext_connexe, itself resting on the sorry exists_mem_image_inf

end SubExtension

/-! ### `def:common_over_extension` -/

section OverExtension

variable {M₀ M₁ M₂ : Type u} [TopologicalSpace M₀] [TopologicalSpace M₁] [TopologicalSpace M₂]
  {C₀ : Causality M₀} {C₁ : Causality M₁} {C₂ : Causality M₂} {i₁ : M₀ → M₁} {i₂ : M₀ → M₂}

variable (C₁ C₂ i₁ i₂) in
/-- `def:common_over_extension`, abstractly: a spacetime `X` with Cauchy embeddings
`e₁ : M₁ → X`, `e₂ : M₂ → X` such that `e₁ ∘ i₁ = e₂ ∘ i₂`. The carrier lives in the universe of
`M₀, M₁, M₂` and is **not** required connected, Hausdorff or second countable (`ETT.tex:255`,
`ETT.tex:1502`). -/
structure CommonOverExtension where
  carrier : Type u
  [top : TopologicalSpace carrier]
  causality : Causality carrier
  e₁ : M₁ → carrier
  e₂ : M₂ → carrier
  he₁ : IsCauchyEmbedding C₁ causality e₁
  he₂ : IsCauchyEmbedding C₂ causality e₂
  comm : e₁ ∘ i₁ = e₂ ∘ i₂

attribute [instance] CommonOverExtension.top

namespace CommonOverExtension

/-- `def:common_over_extension`: a morphism of common over-extensions, an abstract morphism
commuting with the embeddings of `M₁` and `M₂`. -/
def IsMorphism (X Y : CommonOverExtension C₁ C₂ i₁ i₂) (f : X.carrier → Y.carrier) : Prop :=
  IsEMorphism X.causality Y.causality f ∧ f ∘ X.e₁ = Y.e₁ ∧ f ∘ X.e₂ = Y.e₂

/-- `def:common_over_extension`: equivalence, a bijective morphism. -/
def Equivalent (X Y : CommonOverExtension C₁ C₂ i₁ i₂) : Prop :=
  ∃ f, X.IsMorphism Y f ∧ Bijective f

/-- `def:common_over_extension`: minimality — a morphism to every common over-extension. The
quantifier ranges only over over-extensions whose carrier lives in `Type u`; unlike
sub-extensions, over-extensions are not bounded in size by `M₁` or `M₂`. -/
def IsMinimal (X : CommonOverExtension C₁ C₂ i₁ i₂) : Prop :=
  ∀ Y : CommonOverExtension C₁ C₂ i₁ i₂, ∃ f, X.IsMorphism Y f

omit [TopologicalSpace M₀] in
theorem isMorphism_id (X : CommonOverExtension C₁ C₂ i₁ i₂) : X.IsMorphism X id :=
  ⟨IsEMorphism.id, rfl, rfl⟩

/-- **Sanity**: `M₁` is a common over-extension of itself along `i₁, i₁`. -/
def self (h₁ : IsCauchyEmbedding C₀ C₁ i₁) [T2Space M₁] : CommonOverExtension C₁ C₁ i₁ i₁ where
  carrier := M₁
  causality := C₁
  e₁ := id
  e₂ := id
  he₁ := by
    obtain ⟨S, hS, hS'⟩ := h₁.exists_cauchy
    exact ⟨h₁.globallyHyperbolic_target, h₁.globallyHyperbolic_target, IsEMorphism.id,
      injective_id, ⟨_, hS', by rw [image_id]; exact hS'⟩⟩
  he₂ := by
    obtain ⟨S, hS, hS'⟩ := h₁.exists_cauchy
    exact ⟨h₁.globallyHyperbolic_target, h₁.globallyHyperbolic_target, IsEMorphism.id,
      injective_id, ⟨_, hS', by rw [image_id]; exact hS'⟩⟩
  comm := rfl

/-- `M₁` is minimal among the common over-extensions of `M₁` and `M₁` along `i₁, i₁` once every
over-extension's two embeddings coincide (which rigidity gives). The hypothesis `h` is not
witnessed in this file. -/
theorem self_isMinimal (h₁ : IsCauchyEmbedding C₀ C₁ i₁) [T2Space M₁]
    (h : ∀ Y : CommonOverExtension C₁ C₁ i₁ i₁, Y.e₁ = Y.e₂) : (self h₁).IsMinimal :=
  fun Y => ⟨Y.e₁, Y.he₁.isEMorphism, rfl, h Y⟩

end CommonOverExtension

/-! ### The common over-extension and the gluing of `defi:ppcm` -/

/-- **The gluing of `defi:ppcm` closes the square**: for a common sub-extension `X`, the maps of
`M₁` and `M₂` into `Gluing X.b X.c` satisfy `ι₁ ∘ i₁ = ι₂ ∘ i₂`. -/
theorem CommonSubExtension.gluing_comm (X : CommonSubExtension C₀ C₁ C₂ i₁ i₂) :
    Gluing.ι₁ X.b X.c ∘ i₁ = Gluing.ι₂ X.b X.c ∘ i₂ := by
  funext x
  have h1 := congrFun X.comm₁ x
  have h2 := congrFun X.comm₂ x
  simp only [comp_apply] at h1 h2 ⊢
  rw [← h1, ← h2]
  exact Gluing.ι₁_j₁ (X.a x)

/-- **The universal property behind minimality** (`ETT.tex:1980–1985`): given a common
sub-extension `X` with `X` connected and rigidity of the morphisms `X → Y`, every common
over-extension `Y` receives a unique map from `Gluing X.b X.c` compatible with the embeddings of
`M₁` and `M₂`. Rigidity is what makes `e₁ ∘ b = e₂ ∘ c` on all of `X` from `e₁ ∘ i₁ = e₂ ∘ i₂`
on `a(M₀)`. That the map is a morphism of over-extensions is not stated: the gluing carries no
causality here (`Causal.PushoutCausal` builds one). -/
theorem CommonSubExtension.exists_unique_desc (X : CommonSubExtension C₀ C₁ C₂ i₁ i₂)
    (Y : CommonOverExtension C₁ C₂ i₁ i₂) [ConnectedSpace X.carrier] [Nonempty M₀]
    (hrig : IsRigid X.causality Y.causality) :
    ∃! g : Gluing X.b X.c → Y.carrier,
      g ∘ Gluing.ι₁ X.b X.c = Y.e₁ ∧ g ∘ Gluing.ι₂ X.b X.c = Y.e₂ := by
  have h₁ : IsEMorphism X.causality Y.causality (Y.e₁ ∘ X.b) :=
    Y.he₁.isEMorphism.comp X.hb.isEMorphism
  have h₂ : IsEMorphism X.causality Y.causality (Y.e₂ ∘ X.c) :=
    Y.he₂.isEMorphism.comp X.hc.isEMorphism
  have heq : ∀ w, Y.e₁ (X.b w) = Y.e₂ (X.c w) := by
    have := hrig ⊤ (by rw [Opens.coe_top]; exact isConnected_univ) _ _ h₁ h₂
      X.ha.rangeOpens le_top ?_ ?_
    · exact fun w => this (show w ∈ ((⊤ : Opens X.carrier) : Set X.carrier) from trivial)
    · obtain ⟨x⟩ := ‹Nonempty M₀›
      exact ⟨X.a x, by rw [IsCauchyEmbedding.coe_rangeOpens]; exact ⟨x, rfl⟩⟩
    · intro w hw
      rw [IsCauchyEmbedding.coe_rangeOpens] at hw
      obtain ⟨x, rfl⟩ := hw
      have := congrFun Y.comm x
      have h1 := congrFun X.comm₁ x
      have h2 := congrFun X.comm₂ x
      simp only [comp_apply] at this h1 h2 ⊢
      rw [h1, h2]
      exact this
  refine ⟨Gluing.desc Y.e₁ Y.e₂ heq, ⟨rfl, rfl⟩, fun g ⟨hg₁, hg₂⟩ => ?_⟩
  exact Gluing.eq_desc (fun x => congrFun hg₁ x) (fun y => congrFun hg₂ y)

end OverExtension

end Causal
