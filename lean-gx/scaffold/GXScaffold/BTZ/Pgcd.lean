import GX.BTZ.Embeddings

/-!
# btz § 5.1: the maximal common sub-BTZ-extension `M₁ ∧ M₂` of two BTZ-extensions, for `𝔼₀`-manifolds

Target `T-btz-pgcd` (`roadmap/roadmap.toml`). `papers/btz/legacy/labeled/BTZ_1.tex`. The row is
not marked: it is stated for `𝔼₀`-manifolds only (T-btz-scope), and the paper's construction
(the union of the *globally hyperbolic* extension domains) is shown maximal here only through
one tagged `sorry` (below).

* `btzprop:pgcd` — `BTZ_1.tex:1341` (proof l.1350–1378) — `GX.Pgcd.btz_pgcd` (existence of a
  maximal common sub-BTZ-extension, **no** global hyperbolicity needed: proved, 0 `sorry`),
  `GX.Pgcd.pgcdSub`, `GX.Pgcd.pgcdSub_isMaximal`, `GX.Pgcd.range_pgcdSub_b`; the paper's
  construction `GX.Pgcd.ghDom`, its global hyperbolicity `GX.Pgcd.globallyHyperbolicOn_ghDom`
  (the second bullet, proved), and `GX.Pgcd.btz_pgcd_gh` (the paper's `M₁ ∧ M₂` is maximal and
  globally hyperbolic; rests on `GX.Pgcd.globallyHyperbolicOn_dom`, one tagged `sorry`).

> Let $M_0$ be a $\mass{\geq0}$-manifold and let $M_0\xrightarrow{i} M_1$ and
> $M_0 \xrightarrow{j} M_2$ two BTZ-extensions of $M_0$. If $M_0,M_1$ and $M_2$ are globally
> hyperbolic then there exists a maximal common sub-BTZ-extension to $M_1$ and $M_2$. (l.1341–1346)
>
> Let $\pgcd$ the union of all the globally hyperbolic open subset $M\subset M_1$ containing
> $i(M_0)$ such that there exists a BTZ-embedding $M\xrightarrow{\phi_M} M_2$ which restriction to
> $i(M_0)$ is $j\circ i^{-1}$. […] the map $\phi_M$ is unique since it continuous and equal to
> $j\circ i^{-1}$ on $\reg(M)$ which is dense. (l.1352–1354)
>
> Since $M_1$ is globally hyperbolic, it is strongly causal hence $x=y$, by Proposition
> \ref{prop:FZenon_injectif}. (l.1365) […] Then $M_1\wedge M_2$ is globally hyperbolic. […]
> By construction, $\pgcd$ is maximal. (l.1374–1376)

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `𝔼_{≥0}`-manifolds | ⚠ `𝔼₀` only (T-btz-scope; `GX.BTZ.Embeddings`' vocabulary) |
| `i`, `j` BTZ-extensions | ✓ carried: `IsBTZEmbedding i`, `IsBTZEmbedding j` |
| `M₁`, `M₂` Hausdorff, `M₁` second countable (l.261) | ✓ carried (instances; `M₀` needs neither) |
| `M₀` globally hyperbolic | ⚠ weakened: not used by `btz_pgcd`; carried by `globallyHyperbolicOn_dom` (the `sorry`) and `btz_pgcd_gh` |
| `M₁` globally hyperbolic | ⚠ weakened: not used by `btz_pgcd`; used by the second bullet (`globallyHyperbolicOn_ghDom`) |
| `M₂` globally hyperbolic | ⚠ weakened: not used by `btz_pgcd`; carried by `globallyHyperbolicOn_dom` (the `sorry`) and `btz_pgcd_gh` |
| (none) | ⚠ strengthened, for the `sorry`'d `globallyHyperbolicOn_dom` / `btz_pgcd_gh` only: `M₂` connected and second countable |
| `M₁` connected | ⚠ strengthened, for the second bullet only (`e0_sfa_of_globalBTZ`, Lemma 2.13 at `𝔼₀`): l.261 does not require it |

## SCOPE (disclosed)

**Proved (0 `sorry` beneath `btz_pgcd`, `pgcdSub_isMaximal`, `globallyHyperbolicOn_ghDom`).**
`dom i j` is the union of **all** open `A ⊇ i(M₀)` of `M₁` over which `j ∘ i⁻¹` extends to an
`𝔼₀`-morphism (`IsExtDomain`); the extensions glue by density of `i(M₀)` (l.1354,
`eqOn_of_isExtDomain`), the glued map is an `𝔼₀`-morphism of `dom i j` which is **injective by
Hausdorffness of `M₁` alone** (two BTZ points with one image have disjoint neighbourhoods whose
images share a regular point, and `j ∘ i⁻¹` is injective there: `pgcdMap_injective`), and every
common sub-BTZ-extension `(X, a, b, c)` has `b(X) ⊆ dom i j` with `c ∘ b⁻¹` as its extension.
So `pgcdSub` is a maximal common sub-BTZ-extension with no causal hypothesis at all.
The paper's union over the *globally hyperbolic* domains, `ghDom i j ≤ dom i j`, is globally
hyperbolic when `M₁` is (`globallyHyperbolicOn_ghDom`: each such domain is causally convex by
B21 Lemma 2.13 (b), hence so is the union by Lemma 2.13 (a)).

**Not proved (one `sorry`, `globallyHyperbolicOn_dom`).** The paper's « by construction,
`M₁ ∧ M₂` is maximal » needs every common sub-extension to sit in a *globally hyperbolic*
domain, but common sub-extensions are not required globally hyperbolic (l.1306–1313). This holds
iff `dom i j` is globally hyperbolic (`ghDom_eq_dom_of_globallyHyperbolicOn`), i.e. iff the
extension of `j ∘ i⁻¹` continues along the BTZ line above each BTZ point of `dom i j`.

Readings: « a BTZ-embedding `M → M₂` whose restriction to `i(M₀)` is `j ∘ i⁻¹` » is
`IsBTZEmbedding (fun x : A => f x) ∧ ∀ x, f (i x) = j x` for some `f : M₁ → M₂`;
« globally hyperbolic open subset » is `(CE M₁).GloballyHyperbolicOn A` (kb/0001), equivalent to
the subtype form through `ce_opens_eq`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; lean-causal as pinned
in `lake-manifest.json`.
-/

namespace GX

open Set Filter Topology Function TopologicalSpace
open E0CBG E0Spear

namespace Pgcd

section Dom

variable {M₀ M₁ M₂ : Type} [TopologicalSpace M₀] [TopologicalSpace M₁] [TopologicalSpace M₂]
  [ChartedSpace E0Y M₀] [ChartedSpace E0Y M₁] [ChartedSpace E0Y M₂]

/-- An **extension domain** of `j ∘ i⁻¹`: an open `A ⊆ M₁` containing `i(M₀)` over which
`j ∘ i⁻¹` extends to an `𝔼₀`-morphism `f : A → M₂`. -/
def IsExtDomain (i : M₀ → M₁) (j : M₀ → M₂) (A : Opens M₁) : Prop :=
  range i ⊆ A ∧ ∃ f : M₁ → M₂, IsE0Mor f A ∧ ∀ x, f (i x) = j x

/-- **The paper's domains** (`BTZ_1.tex:1352`): a globally hyperbolic open `A ⊆ M₁` containing
`i(M₀)` with a BTZ-embedding `A → M₂` restricting to `j ∘ i⁻¹`. -/
def IsGHExtDomain (i : M₀ → M₁) (j : M₀ → M₂) (A : Opens M₁) : Prop :=
  (CE M₁).GloballyHyperbolicOn A ∧ range i ⊆ A ∧
    ∃ f : M₁ → M₂, IsBTZEmbedding (fun x : A => f x) ∧ ∀ x, f (i x) = j x

variable (i : M₀ → M₁) (j : M₀ → M₂)

/-- **The maximal extension domain**: the union of all extension domains. -/
def dom : Opens M₁ := sSup {A | IsExtDomain i j A}

/-- **The paper's `M₁ ∧ M₂`** (`BTZ_1.tex:1352`): the union of the globally hyperbolic domains. -/
def ghDom : Opens M₁ := sSup {A | IsGHExtDomain i j A}

end Dom

/-! ### §1 Extensions: existence, uniqueness by density, the subtype form -/

section Ext

variable {X M₁ M₂ : Type} [TopologicalSpace X] [TopologicalSpace M₁] [TopologicalSpace M₂]
  [ChartedSpace E0Y X] [ChartedSpace E0Y M₁] [ChartedSpace E0Y M₂]

/-- An `𝔼₀`-morphism on a set is continuous on it. -/
theorem continuousOn_of_isE0Mor {f : M₁ → M₂} {A : Set M₁} (hf : IsE0Mor f A) :
    ContinuousOn f A :=
  fun y hy => (hf y hy).continuousWithinAt

/-- **`c ∘ b⁻¹` extends**: for a BTZ-embedding `b : X → M₁` and an `𝔼₀`-morphism `c : X → M₂`,
some `f : M₁ → M₂` is an `𝔼₀`-morphism on `b(X)` with `f ∘ b = c`. -/
theorem exists_ext [HasGroupoid M₁ e0Groupoid] {b : X → M₁} {c : X → M₂}
    (hb : IsBTZEmbedding b) (hc : IsE0Mor c univ) :
    ∃ f : M₁ → M₂, IsE0Mor f (range b) ∧ ∀ x, f (b x) = c x := by
  rcases isEmpty_or_nonempty X with hX | hX
  · -- `X = ∅`: then `M₁ ⊆ sing₀(M₁)`, so `M₁ = ∅`
    have hM : IsEmpty M₁ := ⟨fun y => by
      obtain ⟨z, hz⟩ := (E0LM.dense_e0RegM (M := M₁)).nonempty_iff.2 ⟨y⟩
      exact hz (hb.compl_range_subset fun ⟨x, _⟩ => hX.elim x)⟩
    exact ⟨fun y => hM.elim y, fun y => hM.elim y, fun x => hX.elim x⟩
  · refine ⟨c ∘ invFunOn b univ, ?_, fun x => ?_⟩
    · have h := Causal.CBG.liftPropOn_comp hb.isOpen_range isOpen_univ hc hb.isE0Mor_invFunOn
        (mapsTo_univ _ _)
      exact h
    · simp only [comp_apply]
      rw [hb.injective.injOn.leftInvOn_invFunOn (mem_univ x)]

/-- **An `𝔼₀`-morphism of an open set read on the subtype is one on the set.** -/
theorem isE0Mor_of_subtype [HasGroupoid M₁ e0Groupoid] {A : Opens M₁} {f : M₁ → M₂}
    (h : IsE0Mor (fun x : A => f x) univ) : IsE0Mor f A := by
  rcases isEmpty_or_nonempty A with hA | hA
  · exact fun x hx => hA.elim ⟨x, hx⟩
  · have hinv := Causal.CBG.liftPropOn_invFunOn isOpen_univ (isE0Mor_val A)
      Subtype.val_injective.injOn
    rw [image_univ, Subtype.range_coe] at hinv
    have hc := Causal.CBG.liftPropOn_comp A.isOpen isOpen_univ h hinv (mapsTo_univ _ _)
    refine Causal.CBG.liftPropOn_congr_of_eqOn A.isOpen hc fun y hy => ?_
    have : invFunOn (Subtype.val : A → M₁) univ y = ⟨y, hy⟩ :=
      Subtype.ext (invFunOn_eq (f := (Subtype.val : A → M₁)) ⟨⟨y, hy⟩, mem_univ _, rfl⟩)
    simp only [comp_apply, this]

end Ext

section Glue

variable {M₀ M₁ M₂ : Type} [TopologicalSpace M₀] [TopologicalSpace M₁] [TopologicalSpace M₂]
  [ChartedSpace E0Y M₀] [ChartedSpace E0Y M₁] [ChartedSpace E0Y M₂]
  [HasGroupoid M₁ e0Groupoid] [T2Space M₂] {i : M₀ → M₁} {j : M₀ → M₂}

/-- **Uniqueness of the extension** (`BTZ_1.tex:1354`, « unique since it continuous and equal to
`j ∘ i⁻¹` on `reg(M)` which is dense »): two extensions agree where both are defined. -/
theorem eqOn_of_ext (hi : IsBTZEmbedding i) {A B : Opens M₁} {f g : M₁ → M₂}
    (hf : IsE0Mor f A) (hfi : ∀ x, f (i x) = j x) (hg : IsE0Mor g B) (hgi : ∀ x, g (i x) = j x) :
    EqOn f g ((A : Set M₁) ∩ B) := by
  refine Set.EqOn.of_subset_closure (s := ((A : Set M₁) ∩ B) ∩ range i) ?_
    ((continuousOn_of_isE0Mor hf).mono inter_subset_left)
    ((continuousOn_of_isE0Mor hg).mono inter_subset_right) inter_subset_left
    (hi.dense_range.open_subset_closure_inter (A.isOpen.inter B.isOpen))
  rintro _ ⟨-, x, rfl⟩
  rw [hfi, hgi]

omit [TopologicalSpace M₀] [ChartedSpace E0Y M₀] [HasGroupoid M₁ e0Groupoid] [T2Space M₂] in
theorem le_dom {A : Opens M₁} (hA : IsExtDomain i j A) : A ≤ dom i j := le_sSup hA

variable (i j) in
/-- **The glued map `φ : M₁ ∧ M₂ → M₂`** (`BTZ_1.tex:1355`): at `x`, the value of the extension
over some domain containing `x`. -/
noncomputable def pgcdMap (x : dom i j) : M₂ :=
  (Opens.mem_sSup.1 x.2).choose_spec.1.2.choose x.1

/-- `φ` is the extension over every domain. -/
theorem pgcdMap_eq (hi : IsBTZEmbedding i) {A : Opens M₁} {f : M₁ → M₂} (hf : IsE0Mor f A)
    (hfi : ∀ x, f (i x) = j x) (x : dom i j) (hx : x.1 ∈ A) : pgcdMap i j x = f x.1 := by
  have h := Opens.mem_sSup.1 x.2
  have hg := h.choose_spec.1.2.choose_spec
  exact eqOn_of_ext hi hg.1 hg.2 hf hfi ⟨h.choose_spec.2, hx⟩

omit [TopologicalSpace M₀] [ChartedSpace E0Y M₀] [HasGroupoid M₁ e0Groupoid] [T2Space M₂] in
/-- `φ = j ∘ i⁻¹` on `i(M₀)`. -/
theorem pgcdMap_of_eq (x : dom i j) (m : M₀) (hm : x.1 = i m) : pgcdMap i j x = j m := by
  have h := Opens.mem_sSup.1 x.2
  have hg := h.choose_spec.1.2.choose_spec
  show h.choose_spec.1.2.choose x.1 = j m
  have h' := hg.2 m
  rw [← hm] at h'
  exact h'

/-- **`φ` is an `𝔼₀`-morphism.** -/
theorem isE0Mor_pgcdMap (hi : IsBTZEmbedding i) : IsE0Mor (pgcdMap i j) univ := by
  refine Causal.CBG.liftPropOn_of_locally isOpen_univ fun x _ => ?_
  obtain ⟨A, ⟨-, f, hf, hfi⟩, hxA⟩ := Opens.mem_sSup.1 x.2
  have hV : IsOpen ((Subtype.val : dom i j → M₁) ⁻¹' A) := A.isOpen.preimage continuous_subtype_val
  refine ⟨_, hV, subset_univ _, hxA, ?_⟩
  have hval : IsE0Mor (Subtype.val : dom i j → M₁) (Subtype.val ⁻¹' A) :=
    Causal.CBG.liftPropOn_mono_of_le isOpen_univ hV (isE0Mor_val _) (subset_univ _)
  have hc := Causal.CBG.liftPropOn_comp hV A.isOpen hf hval fun y hy => hy
  exact Causal.CBG.liftPropOn_congr_of_eqOn hV hc fun y hy => (pgcdMap_eq hi hf hfi y hy).symm

/-- **`φ` is injective** (`BTZ_1.tex:1359–1366`), by Hausdorffness of `M₁` alone: the paper's
strong causality and `prop:FZenon_injectif` are not needed. -/
theorem pgcdMap_injective [T2Space M₁] [HasGroupoid M₂ e0Groupoid] (hi : IsBTZEmbedding i)
    (hj : IsBTZEmbedding j) : Injective (pgcdMap i j) := by
  have hφ := isE0Mor_pgcdMap (j := j) hi
  -- a regular point of `dom i j` is `i m`, where `φ` is `j`
  have hreg : ∀ u : dom i j, pgcdMap i j u ∉ S0 M₂ → ∃ m, u.1 = i m ∧ pgcdMap i j u = j m := by
    intro u hu
    have hu' : u.1 ∉ S0 M₁ := fun h =>
      hu ((mem_S0_iff_of_isE0Mor hφ u).2 ((mem_S0_iff_of_isE0Mor (isE0Mor_val _) u).1 h))
    obtain ⟨m, hm⟩ : u.1 ∈ range i := by_contra fun h => hu' (hi.compl_range_subset h)
    exact ⟨m, hm.symm, pgcdMap_of_eq u m hm.symm⟩
  intro x y hxy
  by_contra hne
  obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := t2_separation hne
  have hO : IsOpen (pgcdMap i j '' U ∩ pgcdMap i j '' V) :=
    (isOpenMap_of_isE0Mor hφ U hU).inter (isOpenMap_of_isE0Mor hφ V hV)
  have hne' : (pgcdMap i j '' U ∩ pgcdMap i j '' V).Nonempty :=
    ⟨pgcdMap i j x, ⟨x, hxU, rfl⟩, ⟨y, hyV, hxy.symm⟩⟩
  obtain ⟨q, ⟨⟨u, huU, rfl⟩, ⟨v, hvV, hvu⟩⟩, hq⟩ :=
    (E0LM.dense_e0RegM (M := M₂)).inter_open_nonempty _ hO hne'
  obtain ⟨m, hum, hu⟩ := hreg u hq
  obtain ⟨m', hvm, hv⟩ := hreg v (hvu ▸ hq)
  have hmm : m = m' := hj.injective (by rw [← hu, ← hv, hvu])
  have huv : u = v := Subtype.ext (by rw [hum, hvm, hmm])
  exact hUV.ne_of_mem huU hvV huv

omit [T2Space M₂] in
/-- `i(M₀)` is an extension domain (`BTZ_1.tex:1353`, « we can choose `M = i(M₀)` »). -/
theorem isExtDomain_range (hi : IsBTZEmbedding i) (hj : IsBTZEmbedding j) :
    IsExtDomain i j hi.rangeOpens := by
  obtain ⟨f, hf, hfi⟩ := exists_ext hi hj.isE0Mor
  exact ⟨subset_rfl, f, hf, hfi⟩

omit [T2Space M₂] in
theorem range_subset_dom (hi : IsBTZEmbedding i) (hj : IsBTZEmbedding j) :
    range i ⊆ dom i j :=
  le_dom (isExtDomain_range hi hj)

omit [T2Space M₂] in
/-- `(M₁ ∧ M₂)ᶜ` is BTZ. -/
theorem compl_dom_subset (hi : IsBTZEmbedding i) (hj : IsBTZEmbedding j) :
    ((dom i j : Set M₁))ᶜ ⊆ S0 M₁ :=
  fun _ hy => hi.compl_range_subset fun h => hy (range_subset_dom hi hj h)

/-- **`φ` is a BTZ-embedding** (`BTZ_1.tex:1366`). -/
theorem isBTZEmbedding_pgcdMap [T2Space M₁] [HasGroupoid M₂ e0Groupoid] (hi : IsBTZEmbedding i)
    (hj : IsBTZEmbedding j) : IsBTZEmbedding (pgcdMap i j) := by
  refine isBTZEmbedding_iff_injective.2 ⟨pgcdMap_injective hi hj, isE0Mor_pgcdMap hi, ?_⟩
  refine fun q hq => hj.compl_range_subset fun ⟨m, hm⟩ => hq ?_
  exact ⟨⟨i m, range_subset_dom hi hj ⟨m, rfl⟩⟩, (pgcdMap_of_eq _ m rfl).trans hm⟩

end Glue

/-! ### §2 The maximal common sub-BTZ-extension -/

section Sub

variable {M₀ M₁ M₂ : Type} [TopologicalSpace M₀] [TopologicalSpace M₁] [TopologicalSpace M₂]
  [ChartedSpace E0Y M₀] [ChartedSpace E0Y M₁] [ChartedSpace E0Y M₂]
  [T2Space M₁] [SecondCountableTopology M₁] [HasGroupoid M₁ e0Groupoid]
  [T2Space M₂] [HasGroupoid M₂ e0Groupoid] {i : M₀ → M₁} {j : M₀ → M₂}

/-- **`M₁ ∧ M₂` as a common sub-BTZ-extension** (`BTZ_1.tex:1355–1357`): the maximal domain with
`i : M₀ → M₁ ∧ M₂`, the inclusion into `M₁` and `φ` into `M₂`. -/
noncomputable def pgcdSub (hi : IsBTZEmbedding i) (hj : IsBTZEmbedding j) : CommonSubBTZ i j where
  X := E0Mfd.of (dom i j)
  a := fun x => ⟨i x, range_subset_dom hi hj ⟨x, rfl⟩⟩
  b := Subtype.val
  c := pgcdMap i j
  ha := by
    refine isBTZEmbedding_iff_injective.2 ⟨fun x y h => hi.injective (congrArg Subtype.val h),
      (isE0Mor_corestrict_iff _ univ).1 hi.isE0Mor, fun v hv => ?_⟩
    have hv' : v.1 ∉ range i := fun ⟨m, hm⟩ => hv ⟨m, Subtype.ext hm⟩
    exact (mem_S0_iff_of_isE0Mor (isE0Mor_val _) v).1 (hi.compl_range_subset hv')
  hb := (isBTZEmbedding_subtypeVal_iff _).2 (compl_dom_subset hi hj)
  hc := isBTZEmbedding_pgcdMap hi hj
  comm₁ := rfl
  comm₂ := funext fun m => pgcdMap_of_eq _ m rfl

theorem range_pgcdSub_b (hi : IsBTZEmbedding i) (hj : IsBTZEmbedding j) :
    range (pgcdSub hi hj).b = dom i j :=
  Subtype.range_coe

/-- **`M₁ ∧ M₂` is maximal** (`BTZ_1.tex:1376`): every common sub-BTZ-extension `(X, a, b, c)`
has `b(X)` in the maximal domain, with extension `c ∘ b⁻¹`. -/
theorem pgcdSub_isMaximal (hi : IsBTZEmbedding i) (hj : IsBTZEmbedding j) :
    (pgcdSub hi hj).IsMaximal := by
  refine (CommonSubBTZ.isMaximal_iff _).2 fun Y => ?_
  obtain ⟨f, hf, hfc⟩ := exists_ext Y.hb Y.hc.isE0Mor
  have hfi : ∀ x, f (i x) = j x := fun x => by
    have h1 := congrFun Y.comm₁ x
    have h2 := congrFun Y.comm₂ x
    simp only [comp_apply] at h1 h2
    rw [← h1, ← h2, hfc]
  have hA : IsExtDomain i j Y.hb.rangeOpens :=
    ⟨fun _ ⟨x, hx⟩ => ⟨Y.a x, by rw [← hx]; exact congrFun Y.comm₁ x⟩, f, hf, hfi⟩
  have hmem : ∀ y, Y.b y ∈ dom i j := fun y => le_dom hA ⟨y, rfl⟩
  refine ⟨fun y => ⟨Y.b y, hmem y⟩, (isE0Mor_corestrict_iff _ univ).1 Y.hb.isE0Mor, rfl, ?_⟩
  funext y
  show pgcdMap i j ⟨Y.b y, hmem y⟩ = Y.c y
  rw [pgcdMap_eq (A := Y.hb.rangeOpens) hi hf hfi _ (show Y.b y ∈ Y.hb.rangeOpens from ⟨y, rfl⟩),
    hfc]

/-- `btzprop:pgcd` (unmarked: `𝔼₀` only) (`BTZ_1.tex:1341`): two BTZ-extensions `M₀ → M₁`,
`M₀ → M₂` have a maximal common sub-BTZ-extension. **No global hyperbolicity is needed.** -/
theorem btz_pgcd (hi : IsBTZEmbedding i) (hj : IsBTZEmbedding j) :
    ∃ X : CommonSubBTZ i j, X.IsMaximal :=
  ⟨pgcdSub hi hj, pgcdSub_isMaximal hi hj⟩

end Sub

/-! ### §3 The paper's construction: the union of the globally hyperbolic domains -/

section GH

variable {M₀ M₁ M₂ : Type} [TopologicalSpace M₀] [TopologicalSpace M₁] [TopologicalSpace M₂]
  [ChartedSpace E0Y M₀] [ChartedSpace E0Y M₁] [ChartedSpace E0Y M₂]
  [T2Space M₁] [SecondCountableTopology M₁] [HasGroupoid M₁ e0Groupoid]
  [T2Space M₂] [HasGroupoid M₂ e0Groupoid] {i : M₀ → M₁} {j : M₀ → M₂}

omit [TopologicalSpace M₀] [ChartedSpace E0Y M₀] [T2Space M₁] [SecondCountableTopology M₁]
  [T2Space M₂] [HasGroupoid M₂ e0Groupoid] in
/-- The paper's domains are extension domains: `M₁ ∧ M₂ ≤` the maximal domain. -/
theorem ghDom_le_dom : ghDom i j ≤ dom i j := by
  refine sSup_le fun A hA => ?_
  obtain ⟨-, hiA, f, hf, hfi⟩ := hA
  exact le_dom ⟨hiA, f, isE0Mor_of_subtype hf.isE0Mor, hfi⟩

omit [T2Space M₂] [HasGroupoid M₂ e0Groupoid] in
/-- **The second bullet** (`BTZ_1.tex:1368–1374`): the paper's `M₁ ∧ M₂` is globally hyperbolic
when `M₁` is: each globally hyperbolic domain is causally convex (B21 Lemma 2.13 (b)), so their
union is (Lemma 2.13 (a)), and Remark 1. -/
theorem globallyHyperbolicOn_ghDom [ConnectedSpace M₁] (hi : IsBTZEmbedding i)
    (hG₁ : (CE M₁).GloballyHyperbolic) : (CE M₁).GloballyHyperbolicOn (ghDom i j) := by
  by_cases hne : ∃ A, IsGHExtDomain i j A
  · obtain ⟨A₀, hA₀⟩ := hne
    have hcompl : ((ghDom i j : Opens M₁) : Set M₁)ᶜ ⊆ S0 M₁ := fun y hy =>
      hi.compl_range_subset fun h => hy (le_sSup (α := Opens M₁) hA₀ (hA₀.2.1 h))
    have hconv : (CE M₁).CausallyConvexIn ((ghDom i j : Opens M₁) : Set M₁) ⊤ := by
      refine (E0AbsMax.btzExt_causallyConvexIn_iff_e0 hcompl).2 fun x hx hxU y hy hxy => ?_
      obtain ⟨A, hA, hxA⟩ := Opens.mem_sSup.1 hxU
      have hAc : (A : Set M₁)ᶜ ⊆ S0 M₁ := fun z hz =>
        hi.compl_range_subset fun h => hz (hA.2.1 h)
      have hAconv := E0AbsMax.btzExt_causallyConvexIn_of_globallyHyperbolicOn_e0 hAc hA.1
      exact le_sSup (α := Opens M₁) hA
        ((E0AbsMax.btzExt_causallyConvexIn_iff_e0 hAc).1 hAconv x hx hxA y hy hxy)
    exact E0AbsMax.globallyHyperbolicOn_of_causallyConvexIn hG₁ E0LM.e0_causallyArcConnected hconv
  · have hbot : ghDom i j = ⊥ := by
      refine sSup_eq_bot.2 fun A hA => absurd ⟨A, hA⟩ hne
    rw [hbot]
    refine ⟨fun x y hxy _ => absurd ((CE M₁).le_mem_left hxy) (by simp), fun p q => ?_⟩
    rw [E0AbsMax.diamond_eq_empty_of_notMem (Or.inl (by simp))]
    exact isCompact_empty

omit [SecondCountableTopology M₁] in
/-- If the maximal domain is globally hyperbolic, it is the paper's `M₁ ∧ M₂`. -/
theorem ghDom_eq_dom_of_globallyHyperbolicOn (hi : IsBTZEmbedding i) (hj : IsBTZEmbedding j)
    (h : (CE M₁).GloballyHyperbolicOn (dom i j)) : ghDom i j = dom i j := by
  refine le_antisymm ghDom_le_dom (le_sSup ?_)
  obtain ⟨f, -, hfc⟩ := exists_ext ((isBTZEmbedding_subtypeVal_iff _).2 (compl_dom_subset hi hj))
    (isE0Mor_pgcdMap (j := j) hi)
  have hf : (fun x : dom i j => f x) = pgcdMap i j := funext hfc
  refine ⟨h, range_subset_dom hi hj, f, by rw [hf]; exact isBTZEmbedding_pgcdMap hi hj,
    fun m => ?_⟩
  exact (hfc ⟨i m, range_subset_dom hi hj ⟨m, rfl⟩⟩).trans (pgcdMap_of_eq _ m rfl)

/-- **The maximal domain is globally hyperbolic** (the content of « by construction, `M₁ ∧ M₂` is
maximal », `BTZ_1.tex:1376`, for common sub-extensions which are not globally hyperbolic). -/
theorem globallyHyperbolicOn_dom [ConnectedSpace M₁] [ConnectedSpace M₂]
    [SecondCountableTopology M₂] (hi : IsBTZEmbedding i) (hj : IsBTZEmbedding j)
    (hG₀ : (CE M₀).GloballyHyperbolic) (hG₁ : (CE M₁).GloballyHyperbolic)
    (hG₂ : (CE M₂).GloballyHyperbolic) : (CE M₁).GloballyHyperbolicOn (dom i j) := by
  sorry -- SORRY(btzprop:pgcd): `dom i j` causally convex in `M₁` (then Remark 1), i.e. by
  -- Lemma 2.13 (a) the extension `φ` of `j ∘ i⁻¹` continues along the BTZ line of `M₁` above each
  -- BTZ point `x ∈ dom i j`: at the first point `z` of that line outside `dom i j`, the images
  -- under `φ` of the line below `z` lie in a compact diamond `J_{M₂}(φ x, φ q)` (`q ≫ z` regular,
  -- `M₂` globally hyperbolic) and must converge to a BTZ point `w` of `M₂`; one then needs that the
  -- isometry `φ`, defined on the regular part of a neighbourhood of `z`, extends across the axis
  -- to a chart isomorphism sending `z` to `w` (rigidity of `𝔼₀` near the axis, a
  -- τ-translation/holonomy argument as in lean-causal kb/0176). Neither the convergence along BTZ
  -- causal curves nor this axis-extension of an `𝔼₀`-isometry is in the strict libraries.

/-- `btzprop:pgcd` in the form of its proof (unmarked) (`BTZ_1.tex:1341–1378`): the paper's
`M₁ ∧ M₂`, the union of the globally hyperbolic domains, carries a maximal common
sub-BTZ-extension, and is globally hyperbolic. Rests on `globallyHyperbolicOn_dom`. -/
theorem btz_pgcd_gh [ConnectedSpace M₁] [ConnectedSpace M₂] [SecondCountableTopology M₂]
    (hi : IsBTZEmbedding i) (hj : IsBTZEmbedding j) (hG₀ : (CE M₀).GloballyHyperbolic)
    (hG₁ : (CE M₁).GloballyHyperbolic) (hG₂ : (CE M₂).GloballyHyperbolic) :
    ∃ X : CommonSubBTZ i j, X.IsMaximal ∧ range X.b = ghDom i j ∧
      (CE X.X).GloballyHyperbolic := by
  have hGH := globallyHyperbolicOn_dom hi hj hG₀ hG₁ hG₂
  refine ⟨pgcdSub hi hj, pgcdSub_isMaximal hi hj, ?_, ?_⟩
  · rw [range_pgcdSub_b, ghDom_eq_dom_of_globallyHyperbolicOn hi hj hGH]
  · show (CE (dom i j)).GloballyHyperbolic
    rw [E0AbsMax.ce_opens_eq]
    exact Causal.Causality.globallyHyperbolic_toSubtype hGH

end GH

end Pgcd

end GX
