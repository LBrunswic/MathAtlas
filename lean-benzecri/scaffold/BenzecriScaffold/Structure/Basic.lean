import BenzecriScaffold.Projective.Hemisphere
import BenzecriScaffold.Structure.Groupoid
import Mathlib.Order.Filter.Germ.Basic
import Mathlib.Topology.Connected.LocallyConnected

/-!
# `BenzecriScaffold.Structure.Basic` — locally projective and locally affine manifolds (Déf. 12, 13, Remarque, Prop. 1, 3)

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 1 § 1, journal pp. 236–237; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch1.tex`. Package WP-45h (wave 2, layer L3).

A locally projective (resp. affine) `n`-manifold is `[ChartedSpace (S n) V]
[HasGroupoid V (projGroupoid n)]` (resp. `[ChartedSpace (Fin n → ℝ) V]
[HasGroupoid V (affGroupoid n)]`), `projGroupoid n = gxGroupoid (GSR n) (S n)`,
`affGroupoid n = gxGroupoid (GAR n) (Fin n → ℝ)`, over the maximal atlas (plan F2). Everything is
proved for an arbitrary `(G, X)`; the paper's two cases are the instances.

* `bzdef:c1s1d12_variete_localement_projective` — `benzecri1960_ch1.tex:304` (Déf. 12, l.304–317,
  p. 236). Certified in full together with `Structure/Jets` (WP-45j), which carries the mark: jets
  are pairs (point, `Filter.Germ`) (`Benzecri.Jet`, plan F3); `Benzecri.IsJetStructure` is Déf. 12's
  « ensemble ouvert $J(V)$ de jets d'isomorphismes » with 1° and 2°; **the jets `J(V)` of a structure
  form one** (`isJetStructure_jets`), **every jet structure is the `J(V)` of a structure**
  (`exists_hasGroupoid_jets_eq_iff`), and **the structure is determined by `J(V)`**
  (`maximalAtlas_eq_of_jets_eq`). « ouvert » and « revêtement » are topological and are in
  `Structure/Jets`: the étalé topology, `IsEtaleOpen ↔ IsOpen` (`isOpen_iff_isEtaleOpen`) and
  `IsCoveringMap` for `J(V) → V` (`isCoveringMap_jets`), resting on the set-level facts proved here
  (`eq_one_of_jetSMul_eq`, `mem_jets_iff_existsUnique`).
* **`bzrem:c1s1r1_affine_vers_projective`** — `benzecri1960_ch1.tex:319` (Remarque, l.319–329,
  pp. 236–237): `remarque_affine_vers_projective`. For EVERY affine injection `j` of `ℝⁿ` into an
  open hemisphere of `S(n)` (« un isomorphisme, compatible avec la structure affine de $\R^n$ sur un
  hémisphère »), `j` is an open embedding, the charts `j ∘ φ` define a locally projective structure
  whose jets are `J''(V) = GS ∘ j ∘ J(V)` (`jets_transport`), and **it does not depend on `j`**
  (« canoniquement associée »): it has the maximal atlas of the standard chart `y ↦ s(y, 1)`
  (`exists_eq_smul_hemiChart`: `j = σ ∘ s(·, 1)`, `σ ∈ GS(n)`; `maximalAtlas_transport_eq_of_smul`);
  hence two choices `j`, `j'` give the same structure (`maximalAtlas_transport_indep`).
* **`bzdef:c1s1d13_carte_compatible`** — `benzecri1960_ch1.tex:331` (Déf. 13, l.331–338, p. 237):
  `Benzecri.IsCompatibleChart` (all jets in `J(V)`), equivalent to membership in the maximal atlas
  (`isCompatibleChart_iff`).
* **`bzprop:c1s1p1_cartes_compatibles`** — `benzecri1960_ch1.tex:340` (Prop. 1, l.340–355, p. 237),
  in the reading of DEC-120: « ouvert $U$ » is a connected (nonempty) open set, consistent with
  « variété » connected. 1°: `existsUnique_smul_eq_of_isPreconnected`; 2°:
  `existsUnique_compatibleChart_jet` (existence for every `U`: `exists_compatibleChart_jet`).
  **Remark** (not a finding, DEC-120): for a disconnected `U` both 1° and the uniqueness of 2° fail
  (`not_prop1_of_disconnected`, in `ℝ¹` with `U = {y < 1} ∪ {y > 2}`), and for `U = ∅` the
  uniqueness of `g` in 1° fails as soon as `G ≠ 1` (`not_existsUnique_smul_eq_of_empty`).
* **`bzprop:c1s1p3_atlas`** — `benzecri1960_ch1.tex:371` (Prop. 3, l.371–379, p. 237):
  `existsUnique_structure_of_atlas` (transitions only locally in `G`, the strongest form) and
  `existsUnique_structure_of_atlas_printed` (one `g_ij` on each nonempty `U_i ∩ U_j`, as printed).

Also: the action of `GA(n)` on `ℝⁿ` and its rigidity (`affineEquivApplyMulAction`, a SCOPED
instance as in lean-gx, `GAR.eq_one_of_eqOn`, `IsAnalyticAction (GAR n) (Fin n → ℝ)`); the maximal
atlas pointwise, ported from `lean-gx/GX/Structure/Basic.lean:277–322` at lean-gx `4a577c5`
(`mem_maximalAtlas_iff_eventually`, with `chartedSpaceOfAtlas` from l.479 and
`exists_smul_eq_on_connectedComponentIn` from l.405); the `HasGroupoid` form of monotonicity along
an open embedding of models (`hasGroupoid_transport`, deferred from wave 1) and in `G`
(`hasGroupoid_mono`).

> **Déf. 12.** Sur une variété $V$, convexe, de dimension $n$, on définit une structure de *variété
> localement projective* (resp. *affine*), par la donnée d'un ensemble ouvert $J(V)$ de jets
> d'isomorphismes de $V$ dans $S(n)$ (resp. $\R^n$) appelé ensemble de jets projectifs (resp.
> affins) et jouissant des propriétés suivantes :
> 1° L'image de $J(V)$ par la projection source est $V$ tout entier;
> 2° $GS(n, \R)$ [resp. $GA(n, \R)$] opère transitivement sur chaque fibre de $J(V)$, composée des
> jets de source donnée.
> Il est clair que $J(V)$, muni de la projection source sur $V$ est un revêtement de $V$.
>
> **Remarque.** Soit $j$ un isomorphisme, compatible avec la structure affine de $\R^n$ sur un
> hémisphère $\mathring{H}$ de $S(n)$. Soit $V$ une variété localement affine, $J(V)$ l'ensemble des
> jets affins de $V$ dans $\R^n$. Désignons par $J'(V)$ l'ensemble des jets d'isomorphismes de $V$
> dans $S(n)$ obtenus en composant $j$ et un jet de $J(V)$. Désignons par $J''(V)$ l'ensemble des
> jets d'isomorphismes de $V$ sur $S(n)$ obtenus en composant un automorphisme de $GS(n, \R)$ et un
> jet de $J'(V)$. Il est clair que $J''(V)$ définit sur $V$ une structure de variété localement
> projective canoniquement associée à la structure localement affine définie par $J(V)$.
>
> **Déf. 13.** Une *carte* d'un ouvert $U$ d'une variété localement projective (resp. affine) sur
> un ouvert de $S(n)$ (resp. $\R^n$) est dite *compatible avec la structure projective* (resp.
> *affine*) si tous ses jets appartiennent à $J(V)$.
>
> **Prop. 1.** Soit $V$ une variété localement affine (resp. projective); soit $U$ un ouvert de $V$.
> 1° Soient $\varphi_1$, $\varphi_2$ deux cartes compatibles de $U$ : il existe un automorphisme
> unique $g\in GA(n, \R)$ [resp. $GS(n, \R)$] tel que $\varphi_1=g\circ\varphi_2$.
> 2° Soit $\varphi_1$ une carte compatible de $U$; soit $x\in U$; soit $j_x$ un jet de $J(V)$ de
> source $x$ : il existe une carte compatible unique $\varphi_2$ dont le jet en $x$ soit $j_x$.
>
> **Prop. 3.** Soit $\{U_i\}$ un recouvrement d'une variété $V$ par un système d'ouverts; soit
> $\{f_i\}$ un système de cartes des $U_i$ sur des ouverts de $S(n)$ (resp. $\R^n$), tel que, si
> $U_i\cap U_j\neq\emptyset$, on ait sur $U_i\cap U_j$, $f_i=g_{ij}\circ f_j$, avec
> $g_{ij}\in GS(n, \R)$ [Resp. $GA(n, \R)$]; alors il existe sur $V$ une structure localement
> projective (resp. affine) unique, avec laquelle les cartes $f_i$ sont compatibles.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `V` a variété « convexe » (`[sic]`, read « connexe »), Hausdorff, second countable (plan F6) | generalised: none is used; `V` is any topological space |
| `J(V)` an OPEN set of jets of isomorphisms | ✓ carried: `IsEtaleOpen`, proved equivalent to openness in the étalé topology in `Structure/Jets` (`isOpen_iff_isEtaleOpen`), and `IsIsoJet` |
| « $J(V)$ … est un revêtement de $V$ » | ✓ carried in `Structure/Jets` (`isCoveringMap_jets`, `IsJetStructure.isCoveringMap`) |
| 2° « opère transitivement sur chaque fibre » | ✓ carried as two fields: `G` preserves the fibres (`smul_mem`) and is transitive on them (`transitive`) |
| « isomorphisme » = homeomorphism (plan F3) | ✓ carried: germs of `OpenPartialHomeomorph` |
| Remarque: `j` an isomorphism « compatible avec la structure affine » onto a hemisphere | generalised: `j` any affine injection of `ℝⁿ` into an open hemisphere of `S(n)` (`IsAffine` for Déf. 6's structure); that it is an open embedding equivariant through `GA(n) → GS(n)` is derived |
| Remarque: « canoniquement associée » | ✓ carried: independence of `j` (`maximalAtlas_transport_indep`) |
| Prop. 1: « $U$ un ouvert de $V$ » | reading (DEC-120): `U` connected and nonempty (`IsPreconnected`, `Nonempty`); the disconnected and empty cases are remarks (`not_prop1_of_disconnected`, `not_existsUnique_smul_eq_of_empty`) |
| Prop. 1: rigidity of `GA`/`GS` | ✓ carried: `IsAnalyticAction G X` (instances for `GSR n`, wave 1, and `GAR n`, here) |
| Prop. 3: `f_i = g_ij ∘ f_j` on all of `U_i ∩ U_j` | generalised: near each point of `U_i ∩ U_j` suffices; the printed form is the corollary |

## SCOPE (disclosed)

* **Déf. 12.** The jet definition is proved equivalent to the atlas one (both directions, and
  uniqueness) here; the étalé topology, « ouvert » and « revêtement » are in `Structure/Jets`, which
  imports this file and carries the mark. « convexe » (`[sic]`) is read « connexe » and is not needed.
* **Remarque, marked.** « canoniquement associée » is proved in its strongest form, independence of
  the choice of `j`: every admissible `j` is `σ ∘ s(·, 1)` with `σ ∈ GS(n)`
  (`Sphere.exists_eq_smul_hemiChart`), and transporting along `σ ∘ ι` or `ι` gives the same maximal
  atlas (`maximalAtlas_transport_eq_of_smul`). The structure is also determined by its jets
  `GS ∘ j ∘ J(V)` (`jets_transport`, `maximalAtlas_eq_of_jets_eq`). `j` is only assumed injective
  and affine; « isomorphisme » (onto the hemisphere) is not needed.
* **Prop. 1, marked under DEC-120's reading** (`U` connected, nonempty). The counterexample for a
  disconnected `U` is in the paper's own setting (`ℝ¹`), kept as a remark; its auxiliary names live in
  `namespace Benzecri.Prop1Counterexample`. The uniqueness in 2° is up to
  `OpenPartialHomeomorph.EqOnSource` (equal on `U`), since an `OpenPartialHomeomorph` carries values
  outside its source.
* The jets `J(V)`, Déf. 13 and Prop. 1 are stated with `[HasGroupoid]` for an arbitrary `(G, X)`.
* `affineEquivApplyMulAction` (the action of `P ≃ᵃ[k] P` on `P`) and its `FaithfulSMul` are SCOPED
  instances of `namespace Benzecri` (active in every file of the package, which all open it; outside,
  `open scoped Benzecri`), exactly as lean-gx scopes the identical action
  (`GX.affineEquivMulAction`, `lean-gx/GX/Singular/Quotient.lean:2420`, `open scoped GX`); recorded in
  REPORT `upstream_moves` for `Projective/Groups`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Filter Topology

namespace Benzecri

universe u v w w'

/-! ### `GA(n, ℝ)` acting on `ℝⁿ`: the action, continuity, rigidity -/

section AffineAction

variable {k V P : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]

/-- The natural action of the affine automorphisms of `P` on `P`, `f • p = f p`. (Mathlib has the
group `P ≃ᵃ[k] P` and no action of it; candidate for `Projective/Groups`.) A SCOPED instance, as
lean-gx scopes the identical `GX.affineEquivMulAction` (`lean-gx/GX/Singular/Quotient.lean:2420`):
active inside `namespace Benzecri`, elsewhere after `open scoped Benzecri`. -/
scoped instance affineEquivApplyMulAction : MulAction (P ≃ᵃ[k] P) P where
  smul f p := f p
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp] theorem affineEquiv_smul_def (f : P ≃ᵃ[k] P) (p : P) : f • p = f p := rfl

/-- The action of `P ≃ᵃ[k] P` on `P` is faithful (scoped, with the action). -/
scoped instance affineEquivFaithfulSMul : FaithfulSMul (P ≃ᵃ[k] P) P := ⟨fun h => AffineEquiv.ext h⟩

end AffineAction

variable {n : ℕ}

/-- `GA(n, ℝ)` acts on `ℝⁿ` by homeomorphisms. -/
instance : ContinuousConstSMul (GAR n) (Fin n → ℝ) := ⟨fun f => GAR.continuous f⟩

/-- **Rigidity of `GA(n, ℝ)`**: an affine map of `ℝⁿ` fixing every point of a nonempty open set
is the identity. -/
theorem GAR.eq_one_of_eqOn {f : GAR n} {U : Set (Fin n → ℝ)} (hU : IsOpen U) (hne : U.Nonempty)
    (h : EqOn (fun p => f • p) id U) : f = 1 := by
  obtain ⟨x, hx⟩ := hne
  have hlin : ∀ v : Fin n → ℝ, f.linear v = v := by
    intro v
    have hcont : Continuous fun t : ℝ => x + t • v := continuous_const.add (continuous_id.smul continuous_const)
    have hmem : (fun t : ℝ => x + t • v) ⁻¹' U ∈ 𝓝 (0 : ℝ) :=
      hcont.continuousAt.preimage_mem_nhds (by simpa using hU.mem_nhds hx)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hmem
    have ht : x + (ε / 2) • v ∈ U := hball (by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith)
    have h1 : f (x + (ε / 2) • v) = x + (ε / 2) • v := h ht
    have h0 : f x = x := h hx
    have := f.map_vadd x ((ε / 2) • v)
    rw [vadd_eq_add, vadd_eq_add, add_comm ((ε / 2) • v) x, h1, h0, map_smul] at this
    have h2 : (ε / 2) • v = (ε / 2) • f.linear v := by
      have := congrArg (fun w => w - x) this
      simpa using this
    exact (smul_right_injective _ (by positivity : (ε / 2 : ℝ) ≠ 0) h2).symm
  have h0 : f x = x := h hx
  ext y : 1
  have := f.map_vadd x (y - x)
  rw [hlin, vadd_eq_add, vadd_eq_add, sub_add_cancel, h0, sub_add_cancel] at this
  exact this

/-- `GA(n, ℝ)` acts analytically (faithfully and rigidly) on `ℝⁿ`. -/
instance : IsAnalyticAction (GAR n) (Fin n → ℝ) where
  toFaithfulSMul := inferInstance
  smul_eq_of_eqOn {f g U} hU hne heq p := by
    have : g⁻¹ * f = 1 := GAR.eq_one_of_eqOn hU hne fun x hx => by
      have := heq hx
      simp only [affineEquiv_smul_def] at this ⊢
      rw [AffineEquiv.coe_mul, Function.comp_apply, this, id, AffineEquiv.inv_def]
      exact g.symm_apply_apply x
    have h' := congrArg (fun h : GAR n => g • h • p) this
    simp only [mul_smul, smul_inv_smul, one_smul] at h'
    exact h'

/-! ### The groupoids of projective and affine structures -/

variable (n) in
/-- The groupoid of locally projective `n`-manifolds: `gxGroupoid (GS(n, ℝ)) (S(n))`. -/
abbrev projGroupoid : StructureGroupoid (S n) := gxGroupoid (GSR n) (S n)

variable (n) in
/-- The groupoid of locally affine `n`-manifolds: `gxGroupoid (GA(n, ℝ)) (ℝⁿ)`. -/
abbrev affGroupoid : StructureGroupoid (Fin n → ℝ) := gxGroupoid (GAR n) (Fin n → ℝ)

/-! ### The maximal atlas, pointwise (port of `lean-gx/GX/Structure/Basic.lean:277–322`) -/

section MaximalAtlas

variable {G : Type w} {X : Type v} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] {M : Type u} [TopologicalSpace M]

omit [TopologicalSpace X] [ContinuousConstSMul G X] in
/-- Two eventual translations of a common chart give an eventual translation between them. Port
of `GX.eventually_smul_eq_of_eventually_smul_eq` (`lean-gx/GX/Structure/Basic.lean:284`). -/
theorem eventually_smul_eq_of_eventually_smul_eq {e₀ e₁ e₂ : M → X} {x : M} {g h : G}
    (h₁ : ∀ᶠ z in 𝓝 x, e₁ z = g • e₀ z) (h₂ : ∀ᶠ z in 𝓝 x, e₂ z = h • e₀ z) :
    ∀ᶠ z in 𝓝 x, e₂ z = (h * g⁻¹) • e₁ z := by
  filter_upwards [h₁, h₂] with z hz₁ hz₂
  rw [hz₁, hz₂, mul_smul, inv_smul_smul]

variable [ChartedSpace X M]

/-- Two charts of the maximal atlas differ, near every point of their overlap, by an element of
`G`. Port of `GX.eventually_smul_eq_of_mem_maximalAtlas` (`lean-gx/GX/Structure/Basic.lean:294`). -/
theorem eventually_smul_eq_of_mem_maximalAtlas {e e' : OpenPartialHomeomorph M X}
    (he : e ∈ (gxGroupoid G X).maximalAtlas M) (he' : e' ∈ (gxGroupoid G X).maximalAtlas M)
    {x : M} (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    ∃ g : G, ∀ᶠ z in 𝓝 x, e' z = g • e z :=
  eventually_smul_eq_of_mem_gxGroupoid
    ((gxGroupoid G X).compatible_of_mem_maximalAtlas he he') hx hx'

variable [HasGroupoid M (gxGroupoid G X)]

/-- **The maximal atlas, pointwise**: an open partial homeomorphism belongs to the maximal atlas
iff near every point of its source it is a translate of the preferred chart there. Port of
`GX.mem_maximalAtlas_iff_eventually` (`lean-gx/GX/Structure/Basic.lean:305`). -/
theorem mem_maximalAtlas_iff_eventually {e : OpenPartialHomeomorph M X} :
    e ∈ (gxGroupoid G X).maximalAtlas M ↔
      ∀ x ∈ e.source, ∃ g : G, ∀ᶠ z in 𝓝 x, e z = g • chartAt X x z := by
  refine ⟨fun he x hx => eventually_smul_eq_of_mem_maximalAtlas
    ((gxGroupoid G X).chart_mem_maximalAtlas x) he (mem_chart_source X x) hx, fun h => ?_⟩
  intro c hc
  have hcm := (gxGroupoid G X).subset_maximalAtlas hc
  refine ⟨symm_trans_mem_gxGroupoid fun x hx => ?_, symm_trans_mem_gxGroupoid fun x hx => ?_⟩
  · obtain ⟨g, hg⟩ := h x hx.1
    obtain ⟨k, hk⟩ := eventually_smul_eq_of_mem_maximalAtlas
      ((gxGroupoid G X).chart_mem_maximalAtlas x) hcm (mem_chart_source X x) hx.2
    exact ⟨_, eventually_smul_eq_of_eventually_smul_eq hg hk⟩
  · obtain ⟨g, hg⟩ := h x hx.2
    obtain ⟨k, hk⟩ := eventually_smul_eq_of_mem_maximalAtlas
      ((gxGroupoid G X).chart_mem_maximalAtlas x) hcm (mem_chart_source X x) hx.1
    exact ⟨_, eventually_smul_eq_of_eventually_smul_eq hk hg⟩

/-- Membership in the maximal atlas, against any family of maximal-atlas charts covering `M`. -/
theorem mem_maximalAtlas_iff_eventually_of_cover {ι : Type*} {f : ι → OpenPartialHomeomorph M X}
    (hf : ∀ i, f i ∈ (gxGroupoid G X).maximalAtlas M) (hcov : ∀ x, ∃ i, x ∈ (f i).source)
    {e : OpenPartialHomeomorph M X} :
    e ∈ (gxGroupoid G X).maximalAtlas M ↔
      ∀ x ∈ e.source, ∃ i, x ∈ (f i).source ∧ ∃ g : G, ∀ᶠ z in 𝓝 x, e z = g • f i z := by
  constructor
  · intro he x hx
    obtain ⟨i, hi⟩ := hcov x
    exact ⟨i, hi, eventually_smul_eq_of_mem_maximalAtlas (hf i) he hi hx⟩
  · intro h
    rw [mem_maximalAtlas_iff_eventually]
    intro x hx
    obtain ⟨i, hi, g, hg⟩ := h x hx
    obtain ⟨a, ha⟩ := eventually_smul_eq_of_mem_maximalAtlas
      ((gxGroupoid G X).chart_mem_maximalAtlas x) (hf i) (mem_chart_source X x) hi
    refine ⟨g * a, ?_⟩
    filter_upwards [hg, ha] with z h1 h2
    rw [h1, h2, mul_smul]

/-- The maximal atlas is stable under post-composition by an element of `G`. -/
theorem transHomeomorph_smul_mem_maximalAtlas {e : OpenPartialHomeomorph M X}
    (he : e ∈ (gxGroupoid G X).maximalAtlas M) (g : G) :
    e.transHomeomorph (Homeomorph.smul g) ∈ (gxGroupoid G X).maximalAtlas M := by
  rw [mem_maximalAtlas_iff_eventually] at he ⊢
  intro x hx
  obtain ⟨a, ha⟩ := he x hx
  refine ⟨g * a, ?_⟩
  filter_upwards [ha] with z hz
  show g • e z = _
  rw [hz, mul_smul]

end MaximalAtlas

/-! ### Déf. 12 — jets (plan F3) -/

section Jets

variable (M : Type u) [TopologicalSpace M] (X : Type v) [TopologicalSpace X]

/-- **A jet of a map `M → X`** (the paper's « jet », plan F3): a source point `x` and a germ at `x`
(Mathlib's `Filter.Germ (𝓝 x) X`). -/
abbrev Jet : Type _ := Σ x : M, Germ (𝓝 x) X

variable {M X}

/-- The jet of `f` at `x`. -/
def jet (x : M) (f : M → X) : Jet M X := ⟨x, (f : Germ (𝓝 x) X)⟩

omit [TopologicalSpace X] in
theorem jet_eq_jet_iff {x : M} {f f' : M → X} : jet x f = jet x f' ↔ f =ᶠ[𝓝 x] f' := by
  rw [jet, jet, Sigma.mk.injEq]
  simp only [heq_eq_eq, true_and]
  exact Germ.coe_eq

/-- A jet is a *jet of isomorphism* (« jet d'isomorphisme ») when it is the germ of a homeomorphism
between open sets, i.e. of an open partial homeomorphism at a point of its source. -/
def IsIsoJet (j : Jet M X) : Prop :=
  ∃ e : OpenPartialHomeomorph M X, j.1 ∈ e.source ∧ j.2 = ((e : M → X) : Germ (𝓝 j.1) X)

/-- **A set of jets is open** in the étalé topology of germs: with a jet `jet x f` it contains
`jet y f` for every `y` near `x`. (The basic open sets of the étalé topology are the
`{jet y f | y ∈ W}`; plan F3 replaces the space of germs by this property.) -/
def IsEtaleOpen (J : Set (Jet M X)) : Prop :=
  ∀ (x : M) (f : M → X), jet x f ∈ J → ∀ᶠ y in 𝓝 x, jet y f ∈ J

variable {G : Type w} [Group G] [MulAction G X]

/-- The action of `G` on jets, by post-composition. -/
def jetSMul (g : G) (j : Jet M X) : Jet M X := ⟨j.1, j.2.map (g • ·)⟩

omit [TopologicalSpace X] in
theorem jetSMul_jet (g : G) (x : M) (f : M → X) : jetSMul g (jet x f) = jet x fun y => g • f y := by
  rw [jetSMul, jet, jet, Germ.map_coe]
  rfl

variable (G) in
/-- **Déf. 12**: `J` is a set of projective (resp. affine) jets for `(G, X)` — open, made of jets
of isomorphisms, such that 1° every point is a source, 2° `G` operates on each fibre, transitively. -/
structure IsJetStructure (J : Set (Jet M X)) : Prop where
  iso : ∀ j ∈ J, IsIsoJet j
  isEtaleOpen : IsEtaleOpen J
  /-- 1° « L'image de $J(V)$ par la projection source est $V$ tout entier ». -/
  source_surjective : ∀ x : M, ∃ j ∈ J, j.1 = x
  /-- 2° `G` operates on `J`, fibre by fibre. -/
  smul_mem : ∀ (g : G), ∀ j ∈ J, jetSMul g j ∈ J
  /-- 2° « $GS(n, \R)$ [resp. $GA(n, \R)$] opère transitivement sur chaque fibre de $J(V)$ ». -/
  transitive : ∀ x (γ γ' : Germ (𝓝 x) X), ⟨x, γ⟩ ∈ J → ⟨x, γ'⟩ ∈ J →
    ∃ g : G, γ' = γ.map (g • ·)

variable [ContinuousConstSMul G X]

/-- **`J(V)`, the jets of a `(G,X)`-structure**: the jets of the charts of the maximal atlas. -/
def jets (G : Type w) (X : Type v) (M : Type u) [TopologicalSpace X] [Group G] [MulAction G X]
    [ContinuousConstSMul G X] [TopologicalSpace M] [ChartedSpace X M] : Set (Jet M X) :=
  {j | ∃ e ∈ (gxGroupoid G X).maximalAtlas M, j.1 ∈ e.source ∧
    j.2 = ((e : M → X) : Germ (𝓝 j.1) X)}

theorem jet_mem_jets [ChartedSpace X M] {e : OpenPartialHomeomorph M X}
    (he : e ∈ (gxGroupoid G X).maximalAtlas M) {x : M} (hx : x ∈ e.source) :
    jet x e ∈ jets G X M :=
  ⟨e, he, hx, rfl⟩

variable [ChartedSpace X M] [HasGroupoid M (gxGroupoid G X)]

omit [HasGroupoid M (gxGroupoid G X)] in
/-- A jet of `J(V)` at `x` is the jet of a maximal-atlas chart. -/
theorem mem_jets_iff {x : M} {γ : Germ (𝓝 x) X} :
    (⟨x, γ⟩ : Jet M X) ∈ jets G X M ↔
      ∃ e ∈ (gxGroupoid G X).maximalAtlas M, x ∈ e.source ∧ γ = ((e : M → X) : Germ (𝓝 x) X) :=
  Iff.rfl

/-- **A chart belongs to the maximal atlas iff all its jets are in `J(V)`.** -/
theorem mem_maximalAtlas_iff_jets {e : OpenPartialHomeomorph M X} :
    e ∈ (gxGroupoid G X).maximalAtlas M ↔ ∀ x ∈ e.source, jet x e ∈ jets G X M := by
  refine ⟨fun he x hx => jet_mem_jets he hx, fun h => ?_⟩
  rw [mem_maximalAtlas_iff_eventually]
  intro x hx
  obtain ⟨e', he', hx', hγ⟩ := h x hx
  have hev : (e' : M → X) =ᶠ[𝓝 x] e := Germ.coe_eq.1 hγ.symm
  obtain ⟨g, hg⟩ := eventually_smul_eq_of_mem_maximalAtlas
    ((gxGroupoid G X).chart_mem_maximalAtlas x) he' (mem_chart_source X x) hx'
  refine ⟨g, ?_⟩
  filter_upwards [hev, hg] with z h1 h2
  rw [← h1, h2]

/-- **Déf. 12, the jets of a `(G,X)`-structure form a jet structure**: `J(V)` is open, made of
jets of isomorphisms, every point is a source (1°), and `G` operates transitively on each fibre
(2°). -/
theorem isJetStructure_jets : IsJetStructure G (jets G X M) where
  iso := fun _ ⟨e, _, hx, hγ⟩ => ⟨e, hx, hγ⟩
  isEtaleOpen := by
    rintro x f ⟨e, he, hx, hγ⟩
    have hev : (e : M → X) =ᶠ[𝓝 x] f := Germ.coe_eq.1 hγ.symm
    filter_upwards [hev.eventually_nhds, e.open_source.mem_nhds hx] with y hy hys
    exact ⟨e, he, hys, (Germ.coe_eq.2 hy).symm⟩
  source_surjective x := ⟨jet x (chartAt X x),
    jet_mem_jets ((gxGroupoid G X).chart_mem_maximalAtlas x) (mem_chart_source X x), rfl⟩
  smul_mem := by
    rintro g ⟨x, γ⟩ ⟨e, he, hx, hγ⟩
    simp only at hx hγ
    subst hγ
    exact ⟨e.transHomeomorph (Homeomorph.smul g), transHomeomorph_smul_mem_maximalAtlas he g, hx,
      by simp only [jetSMul, Germ.map_coe]; rfl⟩
  transitive := by
    rintro x γ γ' ⟨e, he, hx, hγ⟩ ⟨e', he', hx', hγ'⟩
    simp only at hx hγ hx' hγ'
    subst hγ hγ'
    obtain ⟨g, hg⟩ := eventually_smul_eq_of_mem_maximalAtlas he he' hx hx'
    exact ⟨g, by rw [Germ.map_coe]; exact Germ.coe_eq.2 hg⟩

omit [HasGroupoid M (gxGroupoid G X)] in
/-- **The fibres of `J(V)` are free `G`-orbits** (the discrete fibre of the covering
`J(V) → V` of Déf. 12): for an analytic action, `g` fixes a jet of `J(V)` only if `g = 1`. -/
theorem eq_one_of_jetSMul_eq [IsAnalyticAction G X] {j : Jet M X} (hj : j ∈ jets G X M) {g : G}
    (h : jetSMul g j = j) : g = 1 := by
  obtain ⟨x, γ⟩ := j
  obtain ⟨e, he, hx, hγ⟩ := hj
  simp only at hx hγ
  subst hγ
  have h2 : ((fun y => g • e y : M → X) : Germ (𝓝 x) X) = ((e : M → X) : Germ (𝓝 x) X) := by
    simp only [jetSMul, Sigma.mk.injEq, heq_eq_eq, true_and, Germ.map_coe] at h
    exact h
  have hev : ∀ᶠ y in 𝓝 x, g • e y = e y := Germ.coe_eq.1 h2
  obtain ⟨t, ht, hto, hxt⟩ := mem_nhds_iff.1 (hev.and (e.open_source.mem_nhds hx))
  have hW : IsOpen (e '' t) := e.isOpen_image_of_subset_source hto fun z hz => (ht hz).2
  refine eq_of_eqOn (h := 1) hW ⟨e x, mem_image_of_mem e hxt⟩ ?_
  rintro _ ⟨z, hz, rfl⟩
  simp only [one_smul]
  exact (ht hz).1

/-- **Local triviality of `J(V) → V`, set-theoretically**: over the source of a maximal-atlas chart
`e`, the jets of `J(V)` at `y` are exactly the `g • jet y e`, each for a unique `g` (analytic
action). With `G` discrete this is the trivialisation `π⁻¹(U) ≃ U × G` of the covering of Déf. 12
(the topology of `J(V)` itself is not built, SCOPE). -/
theorem mem_jets_iff_existsUnique [IsAnalyticAction G X] {e : OpenPartialHomeomorph M X}
    (he : e ∈ (gxGroupoid G X).maximalAtlas M) {y : M} (hy : y ∈ e.source)
    (γ : Germ (𝓝 y) X) :
    (⟨y, γ⟩ : Jet M X) ∈ jets G X M ↔
      ∃! g : G, γ = ((e : M → X) : Germ (𝓝 y) X).map (g • ·) := by
  constructor
  · intro hj
    obtain ⟨g, hg⟩ := (isJetStructure_jets (G := G) (X := X) (M := M)).transitive y _ γ (jet_mem_jets he hy) hj
    refine ⟨g, hg, fun g' hg' => ?_⟩
    have h1 : ∀ᶠ z in 𝓝 y, g • e z = g' • e z := by
      rw [hg, Germ.map_coe, Germ.map_coe] at hg'
      exact Germ.coe_eq.1 hg'
    have h2 : jetSMul (g'⁻¹ * g) (jet y e) = jet y e := by
      rw [jetSMul_jet, jet_eq_jet_iff]
      filter_upwards [h1] with z hz
      rw [mul_smul, hz, inv_smul_smul]
    exact (inv_mul_eq_one.1 (eq_one_of_jetSMul_eq (jet_mem_jets he hy) h2))
  · rintro ⟨g, rfl, -⟩
    exact (isJetStructure_jets (G := G) (X := X) (M := M)).smul_mem g _ (jet_mem_jets he hy)

end Jets

/-! #### Déf. 12, conversely: a jet structure defines a `(G,X)`-structure -/

section JetConverse

variable {M : Type u} [TopologicalSpace M] {X : Type v} [TopologicalSpace X]
  {G : Type w} [Group G] [MulAction G X] [ContinuousConstSMul G X]

/-- The charted space of an atlas covering `M`, the preferred chart at `x` chosen among those
whose source contains `x`. Port of `GX.chartedSpaceOfAtlas` (`lean-gx/GX/Structure/Basic.lean:479`). -/
@[reducible] def chartedSpaceOfAtlas (A : Set (OpenPartialHomeomorph M X))
    (hA : ∀ x : M, ∃ e ∈ A, x ∈ e.source) : ChartedSpace X M where
  atlas := A
  chartAt x := (hA x).choose
  mem_chart_source x := (hA x).choose_spec.2
  chart_mem_atlas x := (hA x).choose_spec.1

/-- The charts all of whose jets lie in `J` (the maximal atlas of the structure `J` defines). -/
def goodCharts (J : Set (Jet M X)) : Set (OpenPartialHomeomorph M X) :=
  {e | ∀ x ∈ e.source, jet x e ∈ J}

omit [ContinuousConstSMul G X] in
/-- Restricting a jet of isomorphism of an open `J` gives a chart all of whose jets are in `J`. -/
theorem exists_goodChart_of_mem {J : Set (Jet M X)} (hJ : IsJetStructure G J) {x : M}
    {γ : Germ (𝓝 x) X} (hj : (⟨x, γ⟩ : Jet M X) ∈ J) :
    ∃ e ∈ goodCharts J, x ∈ e.source ∧ γ = ((e : M → X) : Germ (𝓝 x) X) := by
  obtain ⟨e, hx, hγ⟩ := hJ.iso _ hj
  simp only at hx hγ
  subst hγ
  obtain ⟨t, ht, hto, hxt⟩ := mem_nhds_iff.1 (hJ.isEtaleOpen x e hj)
  refine ⟨e.restrOpen t hto, fun y hy => ?_, ⟨hx, hxt⟩, by rw [OpenPartialHomeomorph.coe_restrOpen]⟩
  rw [OpenPartialHomeomorph.restrOpen_source] at hy
  rw [OpenPartialHomeomorph.coe_restrOpen]
  exact ht hy.2

omit [ContinuousConstSMul G X] in
theorem exists_goodChart {J : Set (Jet M X)} (hJ : IsJetStructure G J) (x : M) :
    ∃ e ∈ goodCharts J, x ∈ e.source := by
  obtain ⟨⟨x', γ⟩, hj, rfl⟩ := hJ.source_surjective x
  obtain ⟨e, he, hx, -⟩ := exists_goodChart_of_mem hJ hj
  exact ⟨e, he, hx⟩

/-- The charted space defined by a jet structure: its atlas is `goodCharts J`. -/
@[reducible] def chartedSpaceOfJets {J : Set (Jet M X)} (hJ : IsJetStructure G J) :
    ChartedSpace X M :=
  chartedSpaceOfAtlas (goodCharts J) (exists_goodChart hJ)

/-- The structure defined by a jet structure is a `(G,X)`-structure (2°: transitivity on the
fibres makes the transitions locally elements of `G`). -/
theorem hasGroupoid_chartedSpaceOfJets {J : Set (Jet M X)} (hJ : IsJetStructure G J) :
    @HasGroupoid X _ M _ (chartedSpaceOfJets hJ) (gxGroupoid G X) := by
  refine @HasGroupoid.mk X _ M _ (chartedSpaceOfJets hJ) (gxGroupoid G X) fun {e e'} he he' =>
    symm_trans_mem_gxGroupoid fun x hx => ?_
  obtain ⟨g, hg⟩ := hJ.transitive x _ _ (he x hx.1) (he' x hx.2)
  exact ⟨g, Germ.coe_eq.1 (hg.trans (Germ.map_coe _ _))⟩

/-- The maximal atlas of the structure defined by `J` is `goodCharts J`. -/
theorem maximalAtlas_chartedSpaceOfJets {J : Set (Jet M X)} (hJ : IsJetStructure G J) :
    @StructureGroupoid.maximalAtlas X M _ _ (chartedSpaceOfJets hJ) (gxGroupoid G X) =
      goodCharts J := by
  letI := chartedSpaceOfJets hJ
  haveI := hasGroupoid_chartedSpaceOfJets hJ
  ext e
  rw [mem_maximalAtlas_iff_eventually]
  constructor
  · intro h x hx
    obtain ⟨g, hg⟩ := h x hx
    have hc : jet x (chartAt X x) ∈ J := (chart_mem_atlas X x : chartAt X x ∈ goodCharts J) x
      (mem_chart_source X x)
    have := hJ.smul_mem g _ hc
    rw [jetSMul_jet] at this
    rwa [jet_eq_jet_iff.2 hg]
  · intro h x hx
    have hc : jet x (chartAt X x) ∈ J := (chart_mem_atlas X x : chartAt X x ∈ goodCharts J) x
      (mem_chart_source X x)
    obtain ⟨g, hg⟩ := hJ.transitive x _ _ hc (h x hx)
    exact ⟨g, Germ.coe_eq.1 (hg.trans (Germ.map_coe _ _))⟩

/-- **The jets of the structure defined by `J` are `J`.** -/
theorem jets_chartedSpaceOfJets {J : Set (Jet M X)} (hJ : IsJetStructure G J) :
    @jets G X M _ _ _ _ _ (chartedSpaceOfJets hJ) = J := by
  letI := chartedSpaceOfJets hJ
  ext ⟨x, γ⟩
  constructor
  · rintro ⟨e, he, hx, hγ⟩
    rw [maximalAtlas_chartedSpaceOfJets hJ] at he
    simp only at hx hγ
    subst hγ
    exact he x hx
  · intro hj
    obtain ⟨e, he, hx, hγ⟩ := exists_goodChart_of_mem hJ hj
    exact ⟨e, by rw [maximalAtlas_chartedSpaceOfJets hJ]; exact he, hx, hγ⟩

/-- **Déf. 12 is equivalent to the atlas definition** (plan F2/F3): a set `J` of jets of
isomorphisms of `M` into `X` is the set of jets `J(V)` of some `(G,X)`-structure on `M` iff it is
open, every point of `M` is a source (1°), and `G` operates transitively on each fibre (2°). -/
theorem exists_hasGroupoid_jets_eq_iff (J : Set (Jet M X)) :
    (∃ cs : ChartedSpace X M, @HasGroupoid X _ M _ cs (gxGroupoid G X) ∧
      @jets G X M _ _ _ _ _ cs = J) ↔ IsJetStructure G J := by
  constructor
  · rintro ⟨cs, hcs, rfl⟩
    exact isJetStructure_jets
  · intro hJ
    exact ⟨chartedSpaceOfJets hJ, hasGroupoid_chartedSpaceOfJets hJ, jets_chartedSpaceOfJets hJ⟩

/-- **The structure is determined by its jets**: two `(G,X)`-structures on `M` with the same set of
jets have the same maximal atlas. -/
theorem maximalAtlas_eq_of_jets_eq (cs cs' : ChartedSpace X M)
    [h : @HasGroupoid X _ M _ cs (gxGroupoid G X)] [h' : @HasGroupoid X _ M _ cs' (gxGroupoid G X)]
    (hJ : @jets G X M _ _ _ _ _ cs = @jets G X M _ _ _ _ _ cs') :
    @StructureGroupoid.maximalAtlas X M _ _ cs (gxGroupoid G X) =
      @StructureGroupoid.maximalAtlas X M _ _ cs' (gxGroupoid G X) := by
  ext e
  have k1 := @mem_maximalAtlas_iff_jets M _ X _ G _ _ _ cs h e
  have k2 := @mem_maximalAtlas_iff_jets M _ X _ G _ _ _ cs' h' e
  rw [k1, k2, hJ]

end JetConverse

/-! ### Déf. 13 — compatible charts -/

section Compatible

variable {M : Type u} [TopologicalSpace M] {X : Type v} [TopologicalSpace X]
  {G : Type w} [Group G] [MulAction G X] [ContinuousConstSMul G X] [ChartedSpace X M]

variable (G) in
/-- **Déf. 13** (`bzdef:c1s1d13_carte_compatible`): a chart `e` of the open set `U = e.source` onto
the open set `e.target` of the model is *compatible* if all its jets belong to `J(V)`. -/
def IsCompatibleChart (e : OpenPartialHomeomorph M X) : Prop :=
  ∀ x ∈ e.source, jet x e ∈ jets G X M

/-- **A chart is compatible iff it belongs to the maximal atlas** (plan F2). -/
theorem isCompatibleChart_iff [HasGroupoid M (gxGroupoid G X)] {e : OpenPartialHomeomorph M X} :
    IsCompatibleChart G e ↔ e ∈ (gxGroupoid G X).maximalAtlas M :=
  mem_maximalAtlas_iff_jets.symm

end Compatible

/-! ### Prop. 1 — two compatible charts of a connected open set -/

section Prop1

variable {M : Type u} [TopologicalSpace M] {X : Type v} [TopologicalSpace X]
  {G : Type w} [Group G] [MulAction G X] [ContinuousConstSMul G X]

/-- **The transition of a `gxGroupoid` pair is one element of `G` on each connected component of
the overlap** (rigidity propagates the local translation along the component). Port of
`GX.exists_smul_eq_on_connectedComponentIn` (`lean-gx/GX/Structure/Basic.lean:405`). -/
theorem exists_smul_eq_on_connectedComponentIn [IsRigidAction G X]
    {e e' : OpenPartialHomeomorph M X} (h : e.symm.trans e' ∈ gxGroupoid G X) {x : M}
    (hx : x ∈ e.source ∩ e'.source) :
    ∃ g : G, ∀ y ∈ connectedComponentIn (e.source ∩ e'.source) x, e' y = g • e y := by
  obtain ⟨g₀, hg₀⟩ := eventually_smul_eq_of_mem_gxGroupoid h hx.1 hx.2
  let u : Set M := {y | ∀ᶠ z in 𝓝 y, e' z = g₀ • e z}
  let v : Set M := {y | ∃ g : G, (∀ᶠ z in 𝓝 y, e' z = g • e z) ∧ ∃ p : X, g • p ≠ g₀ • p}
  have hu : IsOpen u := isOpen_setOf_eventually_nhds
  have hv : IsOpen v := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨g, hg, hne⟩
    filter_upwards [hg.eventually_nhds] with y' hy' using ⟨g, hy', hne⟩
  have hcover : e.source ∩ e'.source ⊆ u ∪ v := by
    intro y hy
    obtain ⟨g, hg⟩ := eventually_smul_eq_of_mem_gxGroupoid h hy.1 hy.2
    by_cases hgg : ∀ p : X, g • p = g₀ • p
    · left
      filter_upwards [hg] with z hz
      rw [hz, hgg]
    · right
      obtain ⟨p, hp⟩ := not_forall.1 hgg
      exact ⟨g, hg, p, hp⟩
  have hdisj : (e.source ∩ e'.source) ∩ (u ∩ v) = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun y ⟨hys, hyu, g, hg, p, hp⟩ => hp ?_
    have hev : ∀ᶠ z in 𝓝 y, g • e z = g₀ • e z ∧ z ∈ e.source := by
      filter_upwards [hyu, hg, e.open_source.mem_nhds hys.1] with z h1 h2 h3
      exact ⟨by rw [← h2]; exact h1, h3⟩
    obtain ⟨t, ht, hto, hyt⟩ := mem_nhds_iff.1 hev
    exact IsRigidAction.smul_eq_of_eqOn
      (e.isOpen_image_of_subset_source hto fun z hz => (ht hz).2) ⟨e y, mem_image_of_mem e hyt⟩
      (by rintro _ ⟨z, hz, rfl⟩; exact (ht hz).1) p
  have hxW : x ∈ connectedComponentIn (e.source ∩ e'.source) x := mem_connectedComponentIn hx
  rcases isPreconnected_iff_subset_of_disjoint.1
    (isPreconnected_connectedComponentIn (x := x) (F := e.source ∩ e'.source)) u v hu hv
    ((connectedComponentIn_subset _ _).trans hcover)
    (by rw [← subset_empty_iff, ← hdisj]
        exact inter_subset_inter_left _ (connectedComponentIn_subset _ _)) with hWu | hWv
  · exact ⟨g₀, fun y hy => (hWu hy).self_of_nhds⟩
  · have : x ∈ (e.source ∩ e'.source) ∩ (u ∩ v) := ⟨hx, hg₀, hWv hxW⟩
    rw [hdisj] at this
    exact this.elim

variable [ChartedSpace X M] [HasGroupoid M (gxGroupoid G X)]

/-- **Prop. 1, 1°** (`bzprop:c1s1p1_cartes_compatibles`, « ouvert $U$ » read connected and nonempty,
DEC-120): two compatible charts `φ₁, φ₂` of a CONNECTED nonempty open
set `U` differ by a unique `g ∈ G`: `φ₁ = g ∘ φ₂` on `U` (analytic action). The paper does not say
« connexe »; DEC-120 reads it so (`not_prop1_of_disconnected` is the remark for a disconnected `U`). -/
theorem existsUnique_smul_eq_of_isPreconnected [IsAnalyticAction G X] {U : Set M}
    (hU : IsPreconnected U) (hne : U.Nonempty) {φ₁ φ₂ : OpenPartialHomeomorph M X}
    (h₁ : IsCompatibleChart G φ₁) (h₂ : IsCompatibleChart G φ₂) (hs₁ : φ₁.source = U)
    (hs₂ : φ₂.source = U) : ∃! g : G, ∀ y ∈ U, φ₁ y = g • φ₂ y := by
  rw [isCompatibleChart_iff] at h₁ h₂
  obtain ⟨x, hx⟩ := hne
  have hx' : x ∈ φ₂.source ∩ φ₁.source := ⟨hs₂ ▸ hx, hs₁ ▸ hx⟩
  obtain ⟨g, hg⟩ := exists_smul_eq_on_connectedComponentIn
    ((gxGroupoid G X).compatible_of_mem_maximalAtlas h₂ h₁) hx'
  rw [hs₁, hs₂, inter_self, hU.connectedComponentIn hx] at hg
  refine ⟨g, hg, fun g' hg' => ?_⟩
  refine eq_of_eqOn (φ₂.isOpen_image_of_subset_source φ₂.open_source subset_rfl)
    ⟨φ₂ x, mem_image_of_mem _ (hs₂ ▸ hx)⟩ ?_
  rintro _ ⟨y, hy, rfl⟩
  rw [hs₂] at hy
  exact (hg' y hy).symm.trans (hg y hy)

/-- A compatible chart composed with an element of `G` is compatible. -/
theorem IsCompatibleChart.transHomeomorph_smul
    {φ : OpenPartialHomeomorph M X} (hφ : IsCompatibleChart G φ) (g : G) :
    IsCompatibleChart G (φ.transHomeomorph (Homeomorph.smul g)) := by
  rw [isCompatibleChart_iff] at hφ ⊢
  exact transHomeomorph_smul_mem_maximalAtlas hφ g

/-- **Prop. 1, 2°, existence** (no connectedness needed): given a compatible chart `φ₁` of `U`, a
point `x ∈ U` and a jet `j_x ∈ J(V)` at `x`, there is a compatible chart of `U` whose jet at `x` is
`j_x` (namely `g ∘ φ₁`). -/
theorem exists_compatibleChart_jet {φ₁ : OpenPartialHomeomorph M X} (h₁ : IsCompatibleChart G φ₁)
    {x : M} (hx : x ∈ φ₁.source) {γ : Germ (𝓝 x) X} (hγ : (⟨x, γ⟩ : Jet M X) ∈ jets G X M) :
    ∃ φ₂ : OpenPartialHomeomorph M X, IsCompatibleChart G φ₂ ∧ φ₂.source = φ₁.source ∧
      ((φ₂ : M → X) : Germ (𝓝 x) X) = γ := by
  obtain ⟨g, hg⟩ := (isJetStructure_jets (G := G) (X := X) (M := M)).transitive x _ γ (h₁ x hx) hγ
  refine ⟨φ₁.transHomeomorph (Homeomorph.smul g), h₁.transHomeomorph_smul g, rfl, ?_⟩
  rw [hg, Germ.map_coe]
  rfl

/-- **Prop. 1, 2°** (« ouvert $U$ » read connected, DEC-120): on a CONNECTED open set `U`, the compatible chart of `U` with
a given jet at `x` is unique (up to `EqOnSource`: equal on `U`). -/
theorem existsUnique_compatibleChart_jet [IsAnalyticAction G X] {U : Set M} (hU : IsPreconnected U)
    {φ₁ : OpenPartialHomeomorph M X} (h₁ : IsCompatibleChart G φ₁) (hs₁ : φ₁.source = U)
    {x : M} (hx : x ∈ U) {γ : Germ (𝓝 x) X} (hγ : (⟨x, γ⟩ : Jet M X) ∈ jets G X M) :
    ∃ φ₂ : OpenPartialHomeomorph M X, (IsCompatibleChart G φ₂ ∧ φ₂.source = U ∧
      ((φ₂ : M → X) : Germ (𝓝 x) X) = γ) ∧
      ∀ φ₃ : OpenPartialHomeomorph M X, IsCompatibleChart G φ₃ → φ₃.source = U →
        ((φ₃ : M → X) : Germ (𝓝 x) X) = γ → φ₃.EqOnSource φ₂ := by
  obtain ⟨φ₂, h₂, hs₂, hγ₂⟩ := exists_compatibleChart_jet h₁ (hs₁ ▸ hx) hγ
  rw [hs₁] at hs₂
  refine ⟨φ₂, ⟨h₂, hs₂, hγ₂⟩, fun φ₃ h₃ hs₃ hγ₃ => ⟨hs₃.trans hs₂.symm, ?_⟩⟩
  obtain ⟨g, hg, -⟩ := existsUnique_smul_eq_of_isPreconnected hU ⟨x, hx⟩ h₃ h₂ hs₃ hs₂
  have hev : ∀ᶠ y in 𝓝 x, φ₃ y = φ₂ y := Germ.coe_eq.1 (hγ₃.trans hγ₂.symm)
  have hg1 : g = 1 := by
    obtain ⟨t, ht, hto, hxt⟩ := mem_nhds_iff.1 (hev.and ((hs₂ ▸ φ₂.open_source).mem_nhds hx))
    have hts : t ⊆ φ₂.source := fun z hz => hs₂ ▸ (ht hz).2
    refine eq_of_eqOn (h := 1) (φ₂.isOpen_image_of_subset_source hto hts)
      ⟨φ₂ x, mem_image_of_mem _ hxt⟩ ?_
    rintro _ ⟨z, hz, rfl⟩
    show g • φ₂ z = (1 : G) • φ₂ z
    rw [one_smul, ← hg z (ht hz).2]
    exact (ht hz).1
  intro y hy
  rw [hs₃] at hy
  rw [hg y hy, hg1, one_smul]

end Prop1

/-! ### Prop. 3 — an atlas with transitions in `G` generates a unique structure -/

section Prop3

variable {M : Type u} [TopologicalSpace M] {X : Type v} [TopologicalSpace X]
  {G : Type w} [Group G] [MulAction G X] [ContinuousConstSMul G X]

/-- **Prop. 3** (`bzprop:c1s1p3_atlas`), in its strongest form (the transition `f_i = g_ij ∘ f_j`
needs to hold only near each point of `U_i ∩ U_j`): charts `f_i` covering `M`, with transitions
locally in `G`, define a `(G,X)`-structure for which every `f_i` is compatible, and it is the only
one: any `(G,X)`-structure for which every `f_i` is compatible has the same maximal atlas. -/
theorem existsUnique_structure_of_atlas {ι : Type*} (f : ι → OpenPartialHomeomorph M X)
    (hcov : ∀ x, ∃ i, x ∈ (f i).source)
    (htrans : ∀ i j, ∀ x ∈ (f i).source ∩ (f j).source, ∃ g : G, ∀ᶠ z in 𝓝 x, f i z = g • f j z) :
    ∃ cs : ChartedSpace X M, ∃ _ : @HasGroupoid X _ M _ cs (gxGroupoid G X),
      (∀ i, f i ∈ @StructureGroupoid.maximalAtlas X M _ _ cs (gxGroupoid G X)) ∧
      ∀ (cs' : ChartedSpace X M), @HasGroupoid X _ M _ cs' (gxGroupoid G X) →
        (∀ i, f i ∈ @StructureGroupoid.maximalAtlas X M _ _ cs' (gxGroupoid G X)) →
        @StructureGroupoid.maximalAtlas X M _ _ cs' (gxGroupoid G X) =
          @StructureGroupoid.maximalAtlas X M _ _ cs (gxGroupoid G X) := by
  have hA : ∀ x : M, ∃ e ∈ range f, x ∈ e.source := fun x =>
    let ⟨i, hi⟩ := hcov x; ⟨f i, mem_range_self i, hi⟩
  letI cs := chartedSpaceOfAtlas (range f) hA
  have hcs : HasGroupoid M (gxGroupoid G X) := by
    refine ⟨fun {e e'} he he' => ?_⟩
    obtain ⟨i, rfl⟩ := he
    obtain ⟨j, rfl⟩ := he'
    exact symm_trans_mem_gxGroupoid fun x hx => htrans j i x ⟨hx.2, hx.1⟩
  have hf : ∀ i, f i ∈ (gxGroupoid G X).maximalAtlas M := fun i =>
    (gxGroupoid G X).subset_maximalAtlas (mem_range_self i)
  refine ⟨cs, hcs, hf, fun cs' hcs' hf' => ?_⟩
  ext e
  have k1 := @mem_maximalAtlas_iff_eventually_of_cover G X _ _ _ _ M _ cs' hcs' ι f hf' hcov e
  have k2 := @mem_maximalAtlas_iff_eventually_of_cover G X _ _ _ _ M _ cs hcs ι f hf hcov e
  rw [k1, k2]

/-- **Prop. 3 as printed**: if, whenever `U_i ∩ U_j ≠ ∅`, `f_i = g_ij ∘ f_j` on `U_i ∩ U_j` for one
`g_ij ∈ G`, there is a unique `(G,X)`-structure with which every `f_i` is compatible. -/
theorem existsUnique_structure_of_atlas_printed {ι : Type*} (f : ι → OpenPartialHomeomorph M X)
    (hcov : ∀ x, ∃ i, x ∈ (f i).source)
    (htrans : ∀ i j, ((f i).source ∩ (f j).source).Nonempty →
      ∃ g : G, ∀ x ∈ (f i).source ∩ (f j).source, f i x = g • f j x) :
    ∃ cs : ChartedSpace X M, ∃ _ : @HasGroupoid X _ M _ cs (gxGroupoid G X),
      (∀ i, @IsCompatibleChart M _ X _ G _ _ _ cs (f i)) ∧
      ∀ (cs' : ChartedSpace X M), @HasGroupoid X _ M _ cs' (gxGroupoid G X) →
        (∀ i, @IsCompatibleChart M _ X _ G _ _ _ cs' (f i)) →
        @StructureGroupoid.maximalAtlas X M _ _ cs' (gxGroupoid G X) =
          @StructureGroupoid.maximalAtlas X M _ _ cs (gxGroupoid G X) := by
  obtain ⟨cs, hcs, hf, huniq⟩ := existsUnique_structure_of_atlas (G := G) f hcov
    fun i j x hx => by
      obtain ⟨g, hg⟩ := htrans i j ⟨x, hx⟩
      exact ⟨g, Filter.mem_of_superset (((f i).open_source.inter (f j).open_source).mem_nhds hx) hg⟩
  refine ⟨cs, hcs, fun i => (@isCompatibleChart_iff M _ X _ G _ _ _ cs hcs _).2 (hf i),
    fun cs' hcs' hf' => huniq cs' hcs' fun i => (@isCompatibleChart_iff M _ X _ G _ _ _ cs' hcs' _).1
      (hf' i)⟩

end Prop3

/-! ### Transport along an equivariant open embedding of models; the Remarque -/

section Transport

variable {M : Type u} [TopologicalSpace M] {X : Type v} [TopologicalSpace X]
  {G : Type w} [Group G] [MulAction G X] [ContinuousConstSMul G X]
  {X' : Type*} [TopologicalSpace X'] [Nonempty X'] {G' : Type*} [Group G'] [MulAction G' X']
  [ContinuousConstSMul G' X'] {ι : X' → X}

/-- The charted space over `X` obtained from a charted space over `X'` through an open embedding
`ι : X' → X`: Mathlib's `ChartedSpace.comp` with the one-chart structure of `X'` over `X`; the chart
at `x` is `ι ∘ chartAt X' x`. -/
@[reducible] def transportChartedSpace (hι : IsOpenEmbedding ι) (M : Type u) [TopologicalSpace M]
    [ChartedSpace X' M] : ChartedSpace X M :=
  @ChartedSpace.comp X _ X' _ M _
    ((hι.toOpenPartialHomeomorph ι).singletonChartedSpace hι.toOpenPartialHomeomorph_source) _

variable [ChartedSpace X' M]

theorem transport_chartAt (hι : IsOpenEmbedding ι) (x : M) :
    @chartAt X _ M _ (transportChartedSpace hι M) x =
      (chartAt X' x).trans (hι.toOpenPartialHomeomorph ι) :=
  rfl

theorem mem_transport_atlas (hι : IsOpenEmbedding ι) {e : OpenPartialHomeomorph M X}
    (he : e ∈ @atlas X _ M _ (transportChartedSpace hι M)) :
    ∃ a ∈ atlas X' M, e = a.trans (hι.toOpenPartialHomeomorph ι) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := he
  have : b = hι.toOpenPartialHomeomorph ι :=
    OpenPartialHomeomorph.singletonChartedSpace_mem_atlas_eq _ _ b hb
  exact ⟨a, ha, by rw [this]⟩

/-- **Monotonicity along an open embedding of models, `HasGroupoid` form** (plan F2, deferred from
wave 1; the groupoid-level lemma is `transport_mem_gxGroupoid`): a `(G', X')`-manifold is a
`(G, X)`-manifold through an open embedding `ι : X' → X` equivariant through `φ : G' →* G`. -/
theorem hasGroupoid_transport [HasGroupoid M (gxGroupoid G' X')] (hι : IsOpenEmbedding ι)
    (φ : G' →* G) (hφ : ∀ (g : G') (p : X'), ι (g • p) = φ g • ι p) :
    @HasGroupoid X _ M _ (transportChartedSpace hι M) (gxGroupoid G X) := by
  refine @HasGroupoid.mk X _ M _ (transportChartedSpace hι M) (gxGroupoid G X) fun {e e'} he he' => ?_
  obtain ⟨a, ha, rfl⟩ := mem_transport_atlas hι he
  obtain ⟨a', ha', rfl⟩ := mem_transport_atlas hι he'
  refine symm_trans_mem_gxGroupoid fun x hx => ?_
  have hx1 : x ∈ a.source := by
    have := hx.1; rw [OpenPartialHomeomorph.trans_source] at this; exact this.1
  have hx2 : x ∈ a'.source := by
    have := hx.2; rw [OpenPartialHomeomorph.trans_source] at this; exact this.1
  obtain ⟨g, hg⟩ := eventually_smul_eq_of_mem_gxGroupoid (HasGroupoid.compatible (G := gxGroupoid G' X') ha ha') hx1 hx2
  refine ⟨φ g, ?_⟩
  filter_upwards [hg] with z hz
  simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply,
    IsOpenEmbedding.toOpenPartialHomeomorph_apply, hz, hφ]

/-- In the transported structure, `ι ∘ e` is compatible for every compatible `e` of the
`(G', X')`-structure. -/
theorem trans_mem_maximalAtlas_transport [HasGroupoid M (gxGroupoid G' X')]
    (hι : IsOpenEmbedding ι) (φ : G' →* G) (hφ : ∀ (g : G') (p : X'), ι (g • p) = φ g • ι p)
    {e : OpenPartialHomeomorph M X'} (he : e ∈ (gxGroupoid G' X').maximalAtlas M) :
    e.trans (hι.toOpenPartialHomeomorph ι) ∈
      @StructureGroupoid.maximalAtlas X M _ _ (transportChartedSpace hι M) (gxGroupoid G X) := by
  letI := transportChartedSpace hι M
  haveI := hasGroupoid_transport (G := G) (M := M) hι φ hφ
  rw [mem_maximalAtlas_iff_eventually]
  intro x hx
  rw [OpenPartialHomeomorph.trans_source] at hx
  obtain ⟨g, hg⟩ := eventually_smul_eq_of_mem_maximalAtlas
    ((gxGroupoid G' X').chart_mem_maximalAtlas x) he (mem_chart_source X' x) hx.1
  refine ⟨φ g, ?_⟩
  filter_upwards [hg] with z hz
  rw [transport_chartAt]
  simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply,
    IsOpenEmbedding.toOpenPartialHomeomorph_apply, hz, hφ]

/-- **The jets of the transported structure** (the Remarque's `J''(V)`): they are the
`g • (ι ∘ j)` for `j ∈ J(V)` (the `(G', X')`-jets) and `g ∈ G` — « obtenus en composant un
automorphisme de $GS(n, \R)$ et un jet de $J'(V)$ », `J'(V) = j ∘ J(V)`. -/
theorem jets_transport [HasGroupoid M (gxGroupoid G' X')] (hι : IsOpenEmbedding ι) (φ : G' →* G)
    (hφ : ∀ (g : G') (p : X'), ι (g • p) = φ g • ι p) :
    @jets G X M _ _ _ _ _ (transportChartedSpace hι M) =
      {j | ∃ (g : G) (x : M) (γ : Germ (𝓝 x) X'), (⟨x, γ⟩ : Jet M X') ∈ jets G' X' M ∧
        j = jetSMul g ⟨x, γ.map ι⟩} := by
  letI := transportChartedSpace hι M
  haveI := hasGroupoid_transport (G := G) (M := M) hι φ hφ
  ext ⟨x, γ⟩
  constructor
  · rintro ⟨e, he, hx, hγ⟩
    simp only at hx hγ
    subst hγ
    obtain ⟨g, hg⟩ := eventually_smul_eq_of_mem_maximalAtlas
      ((gxGroupoid G X).chart_mem_maximalAtlas x) he (mem_chart_source X x) hx
    refine ⟨g, x, ((chartAt X' x : M → X') : Germ (𝓝 x) X'),
      jet_mem_jets ((gxGroupoid G' X').chart_mem_maximalAtlas x) (mem_chart_source X' x), ?_⟩
    simp only [jetSMul, Germ.map_coe, Sigma.mk.injEq, heq_eq_eq, true_and]
    refine Germ.coe_eq.2 ?_
    filter_upwards [hg] with z hz
    rw [hz, transport_chartAt]
    rfl
  · rintro ⟨g, x', γ', ⟨e, he, hx, hγ⟩, hj⟩
    simp only at hx hγ
    subst hγ
    simp only [jetSMul, Germ.map_coe, Sigma.mk.injEq] at hj
    obtain ⟨rfl, hj⟩ := hj
    rw [heq_eq_eq] at hj
    subst hj
    refine ⟨(e.trans (hι.toOpenPartialHomeomorph ι)).transHomeomorph (Homeomorph.smul g),
      transHomeomorph_smul_mem_maximalAtlas (trans_mem_maximalAtlas_transport hι φ hφ he) g, ?_, ?_⟩
    · rw [OpenPartialHomeomorph.transHomeomorph_source, OpenPartialHomeomorph.trans_source]
      exact ⟨hx, by simp [IsOpenEmbedding.toOpenPartialHomeomorph_source]⟩
    · rfl

/-- The Remarque (`bzrem:c1s1r1_affine_vers_projective`) for the standard hemisphere chart
`j : ℝⁿ → S(n)`, `y ↦ s(y, 1)` (an affine isomorphism onto `H₀`, `isAffine_hemiChartH`): a locally
affine `n`-manifold is a locally projective one, with charts `j ∘ φ` and jets `GS(n) ∘ j ∘ J(V)`
(`jets_transport`). Every other `j` gives the same structure: `remarque_affine_vers_projective`. -/
theorem hasGroupoid_projGroupoid_of_affine {n : ℕ} {V : Type u} [TopologicalSpace V]
    [ChartedSpace (Fin n → ℝ) V] [HasGroupoid V (affGroupoid n)] :
    @HasGroupoid (S n) _ V _ (transportChartedSpace (Sphere.isOpenEmbedding_hemiChart (n := n)) V)
      (projGroupoid n) :=
  hasGroupoid_transport Sphere.isOpenEmbedding_hemiChart Sphere.affToGS fun f y =>
    Sphere.hemiChart_apply_eq_smul f y

omit [Nonempty X'] [ContinuousConstSMul G' X'] in
/-- Two `(G,X)`-structures on `M` whose preferred charts differ, near every point, by an element of
`G` have the same maximal atlas. -/
theorem maximalAtlas_eq_of_eventually_smul (cs cs' : ChartedSpace X M)
    [h : @HasGroupoid X _ M _ cs (gxGroupoid G X)] [h' : @HasGroupoid X _ M _ cs' (gxGroupoid G X)]
    (hc : ∀ x, ∃ g : G, ∀ᶠ z in 𝓝 x, @chartAt X _ M _ cs' x z = g • @chartAt X _ M _ cs x z) :
    @StructureGroupoid.maximalAtlas X M _ _ cs (gxGroupoid G X) =
      @StructureGroupoid.maximalAtlas X M _ _ cs' (gxGroupoid G X) := by
  ext e
  rw [@mem_maximalAtlas_iff_eventually G X _ _ _ _ M _ cs h e,
    @mem_maximalAtlas_iff_eventually G X _ _ _ _ M _ cs' h' e]
  constructor
  · intro H x hx
    obtain ⟨g, hg⟩ := H x hx
    obtain ⟨k, hk⟩ := hc x
    refine ⟨g * k⁻¹, ?_⟩
    filter_upwards [hg, hk] with z h1 h2
    rw [h1, h2, mul_smul, inv_smul_smul]
  · intro H x hx
    obtain ⟨g, hg⟩ := H x hx
    obtain ⟨k, hk⟩ := hc x
    refine ⟨g * k, ?_⟩
    filter_upwards [hg, hk] with z h1 h2
    rw [h1, h2, mul_smul]

/-- **The transported structure depends on the embedding only up to `G`**: if `ι' = σ • ι` for one
`σ ∈ G` (`ι` an open embedding equivariant through `φ : G' →* G`), the structures transported along
`ι` and `ι'` have the same maximal atlas (and `ι'` is equivariant through `σ φ σ⁻¹`). -/
theorem maximalAtlas_transport_eq_of_smul [HasGroupoid M (gxGroupoid G' X')]
    (hι : IsOpenEmbedding ι) (φ : G' →* G) (hφ : ∀ (g : G') (p : X'), ι (g • p) = φ g • ι p)
    {ι' : X' → X} (hι' : IsOpenEmbedding ι') (σ : G) (hσ : ∀ p, ι' p = σ • ι p) :
    @StructureGroupoid.maximalAtlas X M _ _ (transportChartedSpace hι' M) (gxGroupoid G X) =
      @StructureGroupoid.maximalAtlas X M _ _ (transportChartedSpace hι M) (gxGroupoid G X) := by
  have hφ' : ∀ (g : G') (p : X'), ι' (g • p) = (MulAut.conj σ).toMonoidHom.comp φ g • ι' p := by
    intro g p
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply, hσ, hφ, mul_smul, inv_smul_smul]
  haveI := hasGroupoid_transport (G := G) (M := M) hι φ hφ
  haveI := hasGroupoid_transport (G := G) (M := M) hι' _ hφ'
  refine maximalAtlas_eq_of_eventually_smul (transportChartedSpace hι' M)
    (transportChartedSpace hι M) fun x => ⟨σ⁻¹, Eventually.of_forall fun z => ?_⟩
  rw [transport_chartAt, transport_chartAt]
  simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply,
    IsOpenEmbedding.toOpenPartialHomeomorph_apply, hσ, inv_smul_smul]

/-- **The Remarque** (`bzrem:c1s1r1_affine_vers_projective`, l.319–329), in its strongest form. Let
`j : ℝⁿ → H̊` be « un isomorphisme, compatible avec la structure affine de $\R^n$ sur un hémisphère
$\mathring{H}$ de $S(n)$ » — here any affine injection into the open hemisphere `H̊` of equation
`l ≠ 0`, for its structure of Déf. 6 — and `V` a locally affine manifold with jets `J(V)`. Then `j`
is an open embedding of `ℝⁿ` into `S(n)` equivariant through an embedding `GA(n) →* GS(n)`; the
charts `j ∘ φ` define on `V` a locally projective structure (`HasGroupoid`); its jets are
`J''(V) = {g ∘ j ∘ γ | g ∈ GS(n), γ ∈ J(V)}` (« obtenus en composant un automorphisme de
$GS(n, \R)$ et un jet de $J'(V)$ », `J'(V) = j ∘ J(V)`); and it is **canonical**: it has the same
maximal atlas as for the standard chart `y ↦ s(y, 1)`, whatever `j` (`maximalAtlas_transport_indep`
for two choices). -/
theorem remarque_affine_vers_projective {n : ℕ} {l : Module.Dual ℝ (Fin (n + 1) → ℝ)}
    [Fact (l ≠ 0)] {j : (Fin n → ℝ) → Sphere.openHemisphere l} (hj : IsAffine ℝ j)
    (hinj : Function.Injective j) (V : Type u) [TopologicalSpace V] [ChartedSpace (Fin n → ℝ) V]
    [HasGroupoid V (affGroupoid n)] :
    ∃ (hι : IsOpenEmbedding fun y => (j y : S n)) (φ : GAR n →* GSR n),
      (∀ (f : GAR n) (y : Fin n → ℝ), (j (f y) : S n) = φ f • (j y : S n)) ∧
      @HasGroupoid (S n) _ V _ (transportChartedSpace hι V) (projGroupoid n) ∧
      @jets (GSR n) (S n) V _ _ _ _ _ (transportChartedSpace hι V) =
        {J | ∃ (g : GSR n) (x : V) (γ : Germ (𝓝 x) (Fin n → ℝ)),
          (⟨x, γ⟩ : Jet V (Fin n → ℝ)) ∈ jets (GAR n) (Fin n → ℝ) V ∧
          J = jetSMul g ⟨x, γ.map fun y => (j y : S n)⟩} ∧
      @StructureGroupoid.maximalAtlas (S n) V _ _ (transportChartedSpace hι V) (projGroupoid n) =
        @StructureGroupoid.maximalAtlas (S n) V _ _
          (transportChartedSpace (Sphere.isOpenEmbedding_hemiChart (n := n)) V) (projGroupoid n) := by
  obtain ⟨σ, hσ⟩ := Sphere.exists_eq_smul_hemiChart hj hinj
  have hfun : (fun y => (j y : S n)) = (Homeomorph.smul σ) ∘ Sphere.hemiChart n := funext hσ
  have hι : IsOpenEmbedding fun y => (j y : S n) := by
    rw [hfun]
    exact (Homeomorph.smul σ).isOpenEmbedding.comp Sphere.isOpenEmbedding_hemiChart
  let φ : GAR n →* GSR n := (MulAut.conj σ).toMonoidHom.comp Sphere.affToGS
  have hφ : ∀ (f : GAR n) (y : Fin n → ℝ), (j (f y) : S n) = φ f • (j y : S n) := by
    intro f y
    simp only [φ, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply, hσ, Sphere.hemiChart_apply_eq_smul, mul_smul, inv_smul_smul]
  exact ⟨hι, φ, hφ, hasGroupoid_transport hι φ hφ, jets_transport hι φ hφ,
    maximalAtlas_transport_eq_of_smul Sphere.isOpenEmbedding_hemiChart Sphere.affToGS
      (fun f y => Sphere.hemiChart_apply_eq_smul f y) hι σ hσ⟩

/-- **« canoniquement associée »**: two choices `j`, `j'` in the Remarque (affine injections of `ℝⁿ`
into open hemispheres of `S(n)`, possibly different ones) induce the same locally projective
structure on a locally affine manifold `V`. -/
theorem maximalAtlas_transport_indep {n : ℕ} {l l' : Module.Dual ℝ (Fin (n + 1) → ℝ)}
    [Fact (l ≠ 0)] [Fact (l' ≠ 0)] {j : (Fin n → ℝ) → Sphere.openHemisphere l}
    {j' : (Fin n → ℝ) → Sphere.openHemisphere l'} (V : Type u) [TopologicalSpace V]
    [ChartedSpace (Fin n → ℝ) V] [HasGroupoid V (affGroupoid n)]
    (hι : IsOpenEmbedding fun y => (j y : S n)) (hι' : IsOpenEmbedding fun y => (j' y : S n))
    (hj : IsAffine ℝ j) (hinj : Function.Injective j) (hj' : IsAffine ℝ j')
    (hinj' : Function.Injective j') :
    @StructureGroupoid.maximalAtlas (S n) V _ _ (transportChartedSpace hι V) (projGroupoid n) =
      @StructureGroupoid.maximalAtlas (S n) V _ _ (transportChartedSpace hι' V) (projGroupoid n) := by
  obtain ⟨_, _, _, _, _, h⟩ := remarque_affine_vers_projective hj hinj V
  obtain ⟨_, _, _, _, _, h'⟩ := remarque_affine_vers_projective hj' hinj' V
  exact h.trans h'.symm

/-- **Monotonicity in `G`, `HasGroupoid` form**: a `(G, X)`-structure is a `(G'', X)`-structure
when every element of `G` acts as some element of `G''` (e.g. a subgroup). -/
theorem hasGroupoid_mono {G'' : Type*} [Group G''] [MulAction G'' X] [ContinuousConstSMul G'' X]
    [ChartedSpace X M] [HasGroupoid M (gxGroupoid G X)]
    (h : ∀ g : G, ∃ g' : G'', ∀ p : X, g • p = g' • p) : HasGroupoid M (gxGroupoid G'' X) :=
  hasGroupoid_of_le inferInstance (gxGroupoid_mono h)

end Transport

/-! ### Remarks: Prop. 1 read literally fails on a disconnected or empty open set (DEC-120) -/

section Counterexample

/-- **Prop. 1, 1°, for `U = ∅` (remark)**: the uniqueness of `g` fails on the empty open set as soon
as `G` is nontrivial (every `g` works). Hence DEC-120's reading « ouvert $U$ » nonempty. -/
theorem not_existsUnique_smul_eq_of_empty {M : Type u} {X : Type v} {G : Type w} [Group G]
    [MulAction G X] [Nontrivial G] (φ₁ φ₂ : M → X) :
    ¬ ∃! g : G, ∀ y ∈ (∅ : Set M), φ₁ y = g • φ₂ y := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne G
  rintro ⟨g, -, hg⟩
  exact hab ((hg a fun _ h => h.elim).trans (hg b fun _ h => h.elim).symm)

/-! The auxiliary objects of the disconnected counterexample to the literal Prop. 1 (a remark under
DEC-120), kept out of `namespace Benzecri`. -/

namespace Prop1Counterexample

/-- `{y | y₀ < 1}` in `ℝ¹`. -/
def cxA : Set (Fin 1 → ℝ) := {y | y 0 < 1}

/-- `{y | y₀ > 2}` in `ℝ¹`. -/
def cxB : Set (Fin 1 → ℝ) := {y | 2 < y 0}

/-- The translation vector `10`. -/
def cxv : Fin 1 → ℝ := fun _ => 10

theorem isOpen_cxA : IsOpen cxA := isOpen_lt (continuous_apply 0) continuous_const

theorem isOpen_cxB : IsOpen cxB := isOpen_lt continuous_const (continuous_apply 0)

/-- The translation by `10`, on `cxB`. -/
def cxTrans : OpenPartialHomeomorph (Fin 1 → ℝ) (Fin 1 → ℝ) :=
  (Homeomorph.addRight cxv).toOpenPartialHomeomorph.restrOpen cxB isOpen_cxB

/-- The identity, on `cxA`. -/
def cxId : OpenPartialHomeomorph (Fin 1 → ℝ) (Fin 1 → ℝ) :=
  OpenPartialHomeomorph.ofSet cxA isOpen_cxA

theorem cx_disjoint_source : Disjoint cxId.source cxTrans.source := by
  rw [Set.disjoint_left]
  intro y h1 h2
  simp [cxId, cxTrans, cxA, cxB] at h1 h2
  linarith

theorem cx_disjoint_target : Disjoint cxId.target cxTrans.target := by
  rw [Set.disjoint_left]
  intro y h1 h2
  simp [cxId, cxTrans, cxA, cxB, Homeomorph.addRight_symm, cxv] at h1 h2
  linarith

open scoped Classical in
/-- The chart of `cxA ∪ cxB` which is the identity on `cxA` and the translation by `10` on
`cxB`. -/
def cxChart : OpenPartialHomeomorph (Fin 1 → ℝ) (Fin 1 → ℝ) :=
  cxId.disjointUnion cxTrans cx_disjoint_source cx_disjoint_target

open scoped Classical in
theorem cxChart_apply (y : Fin 1 → ℝ) : cxChart y = if y ∈ cxA then y else y + cxv := rfl

theorem cxChart_source : cxChart.source = cxA ∪ cxB := by
  show cxA ∪ (univ ∩ cxB) = _
  rw [univ_inter]

theorem cx_disjoint : Disjoint cxA cxB := by
  rw [Set.disjoint_left]
  intro y h1 h2
  simp only [cxA, cxB, mem_setOf_eq] at h1 h2
  linarith

end Prop1Counterexample

open Prop1Counterexample in
/-- **Remark (DEC-120): Prop. 1 read literally fails on a disconnected open set**; DEC-120 reads
« ouvert $U$ » connected, so this is not a finding. In the locally affine manifold `ℝ¹`
itself (connected, Hausdorff, second countable), the open set `U = {y < 1} ∪ {y > 2}` carries two
compatible charts — the identity, and the chart equal to the identity on `{y < 1}` and to the
translation by `10` on `{y > 2}` — which (1°) differ by no single `g ∈ GA(1, ℝ)`, and (2°) have the
same jet at `0 ∈ U` without being equal on `U`. So both parts of Prop. 1 need `U` connected (and
1° needs `U ≠ ∅`: `not_existsUnique_smul_eq_of_empty`). -/
theorem not_prop1_of_disconnected :
    ∃ (U : Set (Fin 1 → ℝ)) (φ₁ φ₂ : OpenPartialHomeomorph (Fin 1 → ℝ) (Fin 1 → ℝ)),
      IsOpen U ∧ IsCompatibleChart (GAR 1) φ₁ ∧ IsCompatibleChart (GAR 1) φ₂ ∧
      φ₁.source = U ∧ φ₂.source = U ∧ (¬ ∃ g : GAR 1, ∀ y ∈ U, φ₁ y = g • φ₂ y) ∧
      ∃ x ∈ U, ((φ₁ : _ → _) : Germ (𝓝 x) (Fin 1 → ℝ)) = φ₂ ∧ ¬ φ₁.EqOnSource φ₂ := by
  classical
  set U := cxA ∪ cxB with hU
  have hUo : IsOpen U := isOpen_cxA.union isOpen_cxB
  let φ₂ : OpenPartialHomeomorph (Fin 1 → ℝ) (Fin 1 → ℝ) := OpenPartialHomeomorph.ofSet U hUo
  have hφA : ∀ y ∈ cxA, cxChart y = y := fun y hy => by rw [cxChart_apply, if_pos hy]
  have hφB : ∀ y ∈ cxB, cxChart y = y + cxv := fun y hy => by
    rw [cxChart_apply, if_neg (Set.disjoint_right.1 cx_disjoint hy)]
  have h0A : (0 : Fin 1 → ℝ) ∈ cxA := by simp [cxA]
  have hc : (fun _ => (3 : ℝ)) ∈ cxB := by simp [cxB]; norm_num
  refine ⟨U, cxChart, φ₂, hUo, ?_, ?_, cxChart_source, rfl, ?_, 0, Or.inl h0A, ?_, ?_⟩
  · rw [isCompatibleChart_iff, mem_maximalAtlas_iff_eventually]
    intro x hx
    rw [cxChart_source] at hx
    rcases hx with hx | hx
    · refine ⟨1, Filter.mem_of_superset (isOpen_cxA.mem_nhds hx) fun z hz => ?_⟩
      simp only [mem_setOf_eq, chartAt_self_eq, OpenPartialHomeomorph.refl_apply, id, one_smul]
      exact hφA z hz
    · refine ⟨GAR.translation cxv, Filter.mem_of_superset (isOpen_cxB.mem_nhds hx) fun z hz => ?_⟩
      simp only [mem_setOf_eq, chartAt_self_eq, OpenPartialHomeomorph.refl_apply, id,
        affineEquiv_smul_def, GAR.translation, AffineEquiv.constVAdd_apply, vadd_eq_add]
      rw [hφB z hz, add_comm]
  · rw [isCompatibleChart_iff, mem_maximalAtlas_iff_eventually]
    intro x hx
    exact ⟨1, Filter.Eventually.of_forall fun z => by simp [φ₂]⟩
  · rintro ⟨g, hg⟩
    have hg1 : g = 1 := GAR.eq_one_of_eqOn isOpen_cxA ⟨0, h0A⟩ fun y hy => by
      have := hg y (Or.inl hy)
      simp only [φ₂, OpenPartialHomeomorph.ofSet_apply, id, hφA y hy] at this
      exact this.symm
    have := hg _ (Or.inr hc)
    rw [hφB _ hc, hg1, one_smul] at this
    have := congr_fun this 0
    simp [cxv, φ₂] at this
  · refine Germ.coe_eq.2 (Filter.mem_of_superset (isOpen_cxA.mem_nhds h0A) fun z hz => ?_)
    simp only [mem_setOf_eq, φ₂, OpenPartialHomeomorph.ofSet_apply, id]
    exact hφA z hz
  · rintro ⟨-, h⟩
    have := h (show (fun _ => (3 : ℝ)) ∈ cxChart.source by rw [cxChart_source]; exact Or.inr hc)
    rw [hφB _ hc] at this
    have := congr_fun this 0
    simp [cxv, φ₂] at this

end Counterexample

end Benzecri
