import Benzecri.Cone.Base
import Benzecri.Structure.Jets
import Benzecri.Structure.Developing

/-!
# `BenzecriScaffold.Cone.Lift` — Benzécri's cone `F(B) = FJ(B)/ℛ` over a locally projective manifold (§ 2)

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 1 § 2, journal pp. 241–242; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch1.tex`, checked against the scan (PDF pp. 14–15).
Package WP-45r (wave 4). Indexing: the base `B` has dimension `n` (model `S n = S(ℝⁿ⁺¹)`, group
`GSR n`), the cone `F(B)` dimension `n + 1` (model `RnO (n + 1) = ℝⁿ⁺¹ − {O}`, group
`GUR (n + 1)`), i.e. Benzécri's `n − 1` and `n`.

* `bzthm:c1s2_isomorphisme_fonctoriel` — `benzecri1960_ch1.tex:554` (Énoncé, l.554–558, p. 241;
  proof l.560–650, pp. 241–242). Not marked here: the label is MARKED in `Cone/Functor`, in its
  corrected form (DEC-127), where the equivalence, its status and its finding are; this file is the
  construction of the proof (the functor `F` on objects and on morphisms). What this file proves,
  sentence by sentence of the proof:
  - « Désignons par $FJ(B)$ l'ensemble des couples $(j, m)$ … muni de la topologie induite par
    celle du produit $J(B)\times\R^n$ » (l.564–568): `Benzecri.FJ`, a subtype of
    `jets (GSR n) (S n) B × RnO (n + 1)`, the jets carrying the étalé topology of `Structure/Jets`.
  - the relation ℛ (l.568–577): the action of `GS(n, ℝ)` on `FJ(B)`, `g • (j, m) = (g ∘ j, i(g) m)`
    (`FJ` `MulAction` instance, `i = isoGUR n`), whose orbit relation is ℛ (`FCone.q_eq_q_iff`);
    it acts by homeomorphisms (`continuous_jetSMul`).
  - « Le quotient $F(B)$ de $FJ(B)$ par ℛ » (l.586): `Benzecri.FCone n B`, the orbit space, quotient
    topology; the projection `FCone.proj : F(B) → B` (« la projection source … compatible avec la
    relation »), an open quotient map (`isOpenQuotientMap_proj`).
  - « On appellera carte compatible d'un ouvert $u$ de $F(B)$ … une application composée d'un
    relèvement de $u$ dans $FJ(B)$ et de la projection $(j, m)\to m$ » (l.594–603): over a chart `e`
    of `B`, the lift `y ↦ jet_y e` of `e.source` into `J(B)` gives the cone chart
    `FCone.coneChart`, `[(jet_y e, m)] ↦ m`, an open partial homeomorphism of `π⁻¹(e.source)` onto the
    open cone `s⁻¹(e.target)` (`isConeChart_coneChart`).
  - « deux cartes compatibles d'un même ouvert de $F(B)$ diffèrent l'une de l'autre par une
    transformation de $GU(n, \R)$ » (l.618–626): `coneChart_eventually_eq`; hence `F(B)` is an
    affine conical manifold (`FCone.chartedSpace`, `FCone.hasGroupoid`, `FCone.hasConeCharts`).
  - « $\lambda(j, m)=(j, \lambda m)$ » and « espace fibré principal de base $B$ et de groupe
    structural $\R^+$ » (l.579–590): Déf. 3's action on `F(B)` is `posSMul_mk`; the fibres of `π`
    are the `ℝ₊*`-orbits (`exists_posSMul_eq_of_proj_eq`); the action is free (`Cone/Basic`'s
    `eq_one_of_posSMul_eq`, `F(B)` being Hausdorff with cone charts) and `F(B) → F(B)/ℝ₊*` is locally
    trivial, equivariantly, over every base chart (`Cone/Base`'s `ConeBase.coneTrivialization`,
    `ConeBase.exists_coneTrivialization`); and its base `F(B)/ℝ₊*` is `B` (`baseProj`, a bijection
    here, an isomorphism of locally projective manifolds in `Cone/Functor`'s `counitApp`).
  - DEC-124's object conditions: `F(B)` is Hausdorff (`FCone.t2Space`), connected
    (`FCone.connectedSpace`), its `ℝ₊*`-action is proper (`FCone.properSMul`), and second countable
    when `B` is (`FCone.secondCountableTopology`); its base injects into `B`
    (`baseProj`, `baseProj_injective`, `baseProj_surjective`).
  - « Soient $(j_1, m)$ dans $FJ(B_1)$ … on peut trouver un jet et un seul $j_2$ de $J(B_2)$ tel que
    $\varphi\circ j_2=j_1$. Nous poserons $\varphi'(j_1, m)=(j_2, m)$ » (l.639–644; the printed
    « $\varphi\circ j_2=j_1$ » is a misprint for `j₂ ∘ φ = j₁`, flagged `[sic]`, DEC-127): composition
    of jets `JetCompEq` (`j₂ ∘ φ = j₁`, independent of representatives, `JetCompEq.jet_comp`), « un
    jet et un seul » `existsUnique_pushJet` (the `j₂` is `pushJet`, characterised by `pushJet_eq`;
    uniqueness: the fibres of `J(B₁)` are free orbits, `eq_of_jetSMul_eq`); `φ'` is `pushFJ`;
    `FCone.map` is `F(φ)` (« compatible avec la relation ℛ », `map_q`), a morphism of affine conical
    manifolds (`isGXMorphism_map`; in cone charts it reads as `i(g)` where `φ` reads as `g`,
    `map_eventually_eq_of_eventually_eq`, `map_eventually_eq_of_mem`), functorially (`map_id`,
    `map_comp`).
  - « $FJ(B)$ s'identifiera avec $J_1(F(B))$ » (l.568) / « on peut trouver une carte compatible et
    une seule d'un voisinage convenable de $p$ qui soit composée d'un relèvement de ce voisinage sur
    un voisinage de $(j, m)$ et de la projection … $FJ(B)$ s'identifie donc avec l'espace des jets de
    cartes compatibles de $F(B)$ » (l.598–604): `FCone.fjJetHomeomorph : FJ n B ≃ₜ J₁(F(B))`
    (`jets (GUR (n + 1)) (RnO (n + 1)) (FCone n B)`, étalé topology), `(j, m) ↦` the jet at `[(j, m)]`
    of the compatible chart through `(j, m)` (`fjJet`, chart-independent: `fjJet_eq`); it lies over
    `q` (`fjJet_fst`), has value `m` (`value_fjJet`), carries ℛ to `GU(n+1, ℝ)` acting through `i`
    (`fjJet_smul`), and is natural in `B`: under it `φ'` is composition with `F(φ)`, « $J_1(F(B_2))
    \circ F(\varphi)\subset J_1(F(B_1))$ » (l.635, `jetCompEq_fjJet_pushFJ`).

> **Énoncé.** Nous nous proposons de montrer que la correspondance établie entre une variété conique
> affine et sa base, définit un isomorphisme fonctoriel entre la catégorie des variétés coniques
> affines de dimension $n$, et celle des variétés localement projectives de dimension $n-1$.
>
> *Démonstration.* Étant donnée une variété localement projective $B$ de dimension $(n-1)$, nous
> allons construire une variété conique affine $F(B)$ de dimension $n$ dont la base soit $B$.
> Soit $J(B)$ l'espace des jets projectifs de $B$ dans $S(n-1)$. Désignons par $FJ(B)$ l'ensemble
> des couples $(j, m)$ d'un jet $j$ de $J(B)$ et d'un point $m$ de $\R^n-\{O\}$ dont l'image sur le
> quotient $S(n-1)$ de $\R^n-\{O\}$ soit le but du jet $j$. $FJ(B)$ est muni de la topologie
> induite par celle du produit $J(B)\times\R^n$. Nous allons définir $F(B)$ comme un quotient de
> $FJ(B)$, et $FJ(B)$ s'identifiera avec $J_1(F(B))$. Sur $FJ(B)$, définissons la relation
> d'équivalence ℛ suivante : $(j, m)\approx(j_1, m_1)$ si 1° $j$ et $j_1$ ont la même source : on
> a alors $j=g\circ j_1$, où $g\in GS(n-1, \R)$; 2° $m=i(g)\,m_1$ […]. Définissons de plus le
> produit d'un couple $(j, m)$ de $FJ(B)$ par un nombre $\lambda\in\R^+$. On a
> $\lambda(j, m)=(j, \lambda m)$ […]. Le quotient $F(B)$ de $FJ(B)$ par ℛ est un espace fibré
> principal de base $B$ et de groupe structural $\R^+$. […] On appellera carte compatible d'un
> ouvert $u$ de $F(B)$ dans $\R^n-\{O\}$ une application composée d'un relèvement de $u$ dans
> $FJ(B)$ et de la projection $(j, m)\to m$ de $FJ(B)$ sur $\R^n-\{O\}$. Étant donnés $(j, m)$ dans
> $FJ(B)$, $p$ le projeté de $(j, m)$ dans $F(B)=FJ(B)/ℛ$, on peut trouver une carte compatible et
> une seule d'un voisinage convenable de $p$ qui soit composée d'un relèvement de ce voisinage sur un
> voisnage de $(j, m)$ et de la projection sur $\R^n-\{O\}$. $FJ(B)$ s'identifie donc avec l'espace
> des jets de cartes compatibles de $F(B)$. […] De plus, deux cartes
> compatibles d'un même ouvert de $F(B)$ diffèrent l'une de l'autre par une transformation de
> $GU(n, \R)$. […] Soit $\varphi$ un morphisme de variété projective de source $B_1$, de but
> $B_2$. […] Soient $(j_1, m)$ dans $FJ(B_1)$, $s_1$ la source de $j_1$ dans $B_1$, on peut trouver
> un jet et un seul $j_2$ de $J(B_2)$ tel que $\varphi\circ j_2=j_1$. Nous poserons
> $\varphi'(j_1, m)=(j_2, m)$. L'application $\varphi'$ étant compatible avec la relation ℛ définit
> une application de $F(B_1)$ dans $F(B_2)$. […]

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `B` a locally projective `(n−1)`-manifold (Déf. 12) | ✓ carried: `[ChartedSpace (S n) B] [HasGroupoid B (projGroupoid n)]` |
| `B` a « variété »: Hausdorff | ✓ carried where used (`[T2Space B]`: `F(B)` Hausdorff, Déf. 3's action, properness, `F(φ)` needs none) |
| `B` a « variété »: connected | ✓ carried where used (`[ConnectedSpace B]` for `FCone.connectedSpace`) |
| `B` a « variété »: second countable | generalised: not needed by the construction; `F(B)` second countable when `B` is (`FCone.secondCountableTopology`) |
| `J(B)` « l'espace des jets projectifs », with its topology | ✓ carried: `jets (GSR n) (S n) B` with the étalé topology (`Structure/Jets`, scoped instance) |
| `FJ(B)` « muni de la topologie induite par celle du produit » | ✓ carried: subspace topology of `jets × RnO (n + 1)` |
| `F(B) = FJ(B)/ℛ` with the quotient topology | ✓ carried: `MulAction.orbitRel.Quotient`, quotient topology |
| `φ` « un morphisme de variété projective » | ✓ carried: `IsGXMorphism (GSR n) (S n) φ` (p. 238, `isGXMorphism_iff_jets`) |

## SCOPE (disclosed)

* **The relation ℛ as an action.** `(j, m) ≈ (j₁, m₁)` iff `j = g ∘ j₁` and `m = i(g) m₁` for some
  `g ∈ GS(n, ℝ)` is the orbit relation of `g • (j, m) = (g ∘ j, i(g) m)`; this is the associated
  bundle `J(B) ×_{GS} (ℝⁿ⁺¹ − {O})` cut down to the pairs with `s(m) = j(source)` (the condition is
  `GS`-invariant: `toSphere_isoGUR_smul`). Formalized as printed, through Mathlib's orbit quotient.
* **Jets as germs; l.640 is a misprint of order (DEC-127).** A jet is a pair (point, germ)
  (`Benzecri.Jet`, plan F3). The printed « $\varphi\circ j_2=j_1$ » (l.640, p. 242, confirmed on the
  scan) is a misprint for `j₂ ∘ φ = j₁`, flagged `[sic]` in the transcription: with `φ : B₁ → B₂` and
  `j₂` a jet of `B₂` into `S(n−1)` no other composite is well typed, and every other composition of
  Ch. 1 is written right to left — `φ₁ = g∘φ₂` (l.345), `f_i = g_ij∘f_j` (l.375), « $J(V_2)\circ f$ »
  (p. 238, l.393: the jets `j ∘ f`), `j = g∘j₁` (l.574, l.623), « $J_1(F(B_2))\circ F(\varphi)$ »
  (l.635). By CAMPAIGN.md's rule it is formalized in its evident reading, not as a finding:
  `JetCompEq φ j₂ j₁` is `j₂ = jet_{φ(y)} f`, `j₁ = jet_y (f ∘ φ)`.
* **« s'identifie »** (l.568, l.604) is formalized as a homeomorphism, the strongest form the
  sentences support (`FJ(B)` carries « la topologie induite », `J₁(F(B))` the étalé topology of
  Déf. 12), with its compatibilities (source, value, ℛ, naturality in `B`); it is in-proof material
  with no label of its own, recorded under the Énoncé's row. `ConeBase.unitMap` (`Cone/Functor`) is
  its global counterpart for `B = V/ℝ₊*` (`V ≅ F(V/ℝ₊*)`).
* `t2Space_RnO` (`ℝᵏ − {O}` Hausdorff) is a LOCAL instance of this file and of `Cone/Functor`.
* Generic jet lemmas proved here for an arbitrary `(G, X)` (they belong upstream, REPORT
  `upstream_moves`): `jetSMul_one`, `jetSMul_mul`, `value_jetSMul`, `continuous_jetSMul`,
  `eq_of_jetSMul_eq`, `exists_eventually_smul_of_jet_mem`, `sheetIndex_eventually_eq`,
  `sheetIndex_jetSMul`, `sheetIndex_jetSMul_jet`, `sheetIndex_of_eventually_eq`,
  `exists_eq_jetSMul_of_mem`, `t2Space_of_fibre_charts`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Filter Topology

namespace Benzecri

universe u v w

/-! ### Jets: the action of `G`, sheets, values -/

section JetLemmas

variable {M : Type u} [TopologicalSpace M] {X : Type v} [TopologicalSpace X]
  {G : Type w} [Group G] [MulAction G X]

omit [TopologicalSpace X] in
@[simp] theorem jetSMul_fst (g : G) (j : Jet M X) : (jetSMul g j).1 = j.1 := rfl

omit [TopologicalSpace X] in
@[simp] theorem jetSMul_one (j : Jet M X) : jetSMul (1 : G) j = j := by
  obtain ⟨x, γ⟩ := j
  induction γ using Germ.inductionOn with
  | h f =>
    show (⟨x, (f : Germ (𝓝 x) X).map ((1 : G) • ·)⟩ : Jet M X) = ⟨x, f⟩
    rw [Germ.map_coe]
    congr 2
    funext y
    exact one_smul G (f y)

omit [TopologicalSpace X] in
theorem jetSMul_mul (g h : G) (j : Jet M X) : jetSMul (g * h) j = jetSMul g (jetSMul h j) := by
  obtain ⟨x, γ⟩ := j
  simp only [jetSMul, Germ.map_map]
  congr 2
  funext y
  exact mul_smul g h y

omit [TopologicalSpace X] in
/-- The value of `g • j` is `g` applied to the value of `j`. -/
theorem value_jetSMul (g : G) (j : Jet M X) : Jet.value (jetSMul g j) = g • Jet.value j := by
  obtain ⟨x, γ⟩ := j
  induction γ using Germ.inductionOn with
  | h f => rfl

omit [TopologicalSpace X] in
/-- **The action of `g ∈ G` on jets is continuous for the étalé topology.** -/
theorem continuous_jetSMul (g : G) : Continuous (jetSMul g : Jet M X → Jet M X) := by
  refine continuous_generateFrom_iff.2 ?_
  rintro _ ⟨f, W, hW, rfl⟩
  have : jetSMul g ⁻¹' ((fun y => jet y f) '' W) = (fun y => jet y fun z => g⁻¹ • f z) '' W := by
    ext j
    obtain ⟨h, hh⟩ := exists_jet_eq j
    rw [← hh, mem_preimage, jetSMul_jet, jet_mem_image_jet_iff, jet_mem_image_jet_iff]
    refine and_congr Iff.rfl ⟨fun H => ?_, fun H => ?_⟩
    · filter_upwards [H] with z hz
      rw [hz, inv_smul_smul]
    · filter_upwards [H] with z hz
      rw [← hz, smul_inv_smul]
  rw [this]
  exact isOpen_etaleBasic _ hW

variable [ContinuousConstSMul G X] [ChartedSpace X M]

/-- Two elements of `G` acting identically on a jet of `J(V)` are equal (the fibres of `J(V)` are
free orbits). -/
theorem eq_of_jetSMul_eq [HasGroupoid M (gxGroupoid G X)] [IsAnalyticAction G X] {j : Jet M X}
    (hj : j ∈ jets G X M) {a b : G} (h : jetSMul a j = jetSMul b j) : a = b := by
  have h1 : jetSMul (b⁻¹ * a) j = j := by
    rw [jetSMul_mul, h, ← jetSMul_mul, inv_mul_cancel, jetSMul_one]
  exact (inv_mul_eq_one.1 (eq_one_of_jetSMul_eq hj h1)).symm

/-- Two jets of `J(V)` at the same point differ by an element of `G`, as maps: if `jet x f` and
`jet x f'` are in `J(V)`, then `f' = g • f` near `x`. -/
theorem exists_eventually_smul_of_jet_mem [HasGroupoid M (gxGroupoid G X)] {x : M} {f f' : M → X}
    (hf : jet x f ∈ jets G X M) (hf' : jet x f' ∈ jets G X M) :
    ∃ g : G, ∀ᶠ z in 𝓝 x, f' z = g • f z := by
  obtain ⟨g, hg⟩ := (isJetStructure_jets (G := G) (X := X) (M := M)).transitive x _ _ hf hf'
  refine ⟨g, ?_⟩
  rw [Germ.map_coe] at hg
  exact Germ.coe_eq.1 hg

variable [HasGroupoid M (gxGroupoid G X)] [IsAnalyticAction G X] {e : OpenPartialHomeomorph M X}

/-- **The sheet index is locally constant** on `J(V)` over the source of a chart (the fibre
coordinate of `jetsTrivialization`, discrete). -/
theorem sheetIndex_eventually_eq (he : e ∈ (gxGroupoid G X).maximalAtlas M) {j : jets G X M}
    (hj : j.1.1 ∈ e.source) : ∀ᶠ j' in 𝓝 j, j'.1.1 ∈ e.source ∧ sheetIndex he j' = sheetIndex he j := by
  set g₀ := sheetIndex he j
  have hB : IsOpen (Subtype.val ⁻¹' ((fun y => jet y fun z => g₀ • e z) '' e.source) :
      Set (jets G X M)) :=
    (isOpen_etaleBasic _ e.open_source).preimage continuous_subtype_val
  have hjB : j ∈ Subtype.val ⁻¹' ((fun y => jet y fun z => g₀ • e z) '' e.source) :=
    ⟨(j : Jet M X).1, hj, by
      show jet (j : Jet M X).1 (fun z => g₀ • e z) = j
      rw [← jetSMul_jet, ← val_eq_jetSMul_sheetIndex he hj]⟩
  filter_upwards [hB.mem_nhds hjB] with j' hj'
  obtain ⟨y, hy, hj'⟩ := hj'
  have hy' : (j' : Jet M X).1 = y := by rw [← hj']; rfl
  exact ⟨hy' ▸ hy, sheetIndex_eq_of_val_eq he hy hj'.symm⟩

/-- The sheet index of `g • j` is `g` times the sheet index of `j`. -/
theorem sheetIndex_jetSMul (he : e ∈ (gxGroupoid G X).maximalAtlas M) {j : jets G X M}
    (hj : j.1.1 ∈ e.source) (g : G) (hgj : jetSMul g j.1 ∈ jets G X M) :
    sheetIndex he ⟨jetSMul g j.1, hgj⟩ = g * sheetIndex he j := by
  have h0 := val_eq_jetSMul_sheetIndex he hj
  refine sheetIndex_eq_of_val_eq he hj (g := g * sheetIndex he j) ?_
  show jetSMul g j.1 = _
  rw [h0, ← jetSMul_mul, jetSMul_jet]
  rfl

/-- The sheet index of a jet `g • jet y e` is `g`. -/
theorem sheetIndex_jetSMul_jet (he : e ∈ (gxGroupoid G X).maximalAtlas M) {y : M}
    (hy : y ∈ e.source) (g : G) (hj : jetSMul g (jet y e) ∈ jets G X M) :
    sheetIndex he ⟨jetSMul g (jet y e), hj⟩ = g :=
  sheetIndex_eq_of_val_eq he hy (jetSMul_jet g y e)

/-- Changing chart: if `e' = g • e` near `y`, the sheet index of a jet at `y` for `e'` is its sheet
index for `e` times `g⁻¹`. -/
theorem sheetIndex_of_eventually_eq {e' : OpenPartialHomeomorph M X}
    (he : e ∈ (gxGroupoid G X).maximalAtlas M) (he' : e' ∈ (gxGroupoid G X).maximalAtlas M)
    {j : jets G X M} (hj : j.1.1 ∈ e.source) (hj' : j.1.1 ∈ e'.source) {g : G}
    (hg : ∀ᶠ z in 𝓝 j.1.1, e' z = g • e z) :
    sheetIndex he' j = sheetIndex he j * g⁻¹ := by
  refine sheetIndex_eq_of_val_eq he' hj' ((val_eq_jetSMul_sheetIndex he hj).trans ?_)
  rw [jetSMul_jet, jet_eq_jet_iff]
  filter_upwards [hg] with z hz
  rw [hz, mul_smul, inv_smul_smul]

end JetLemmas

/-! ### `FJ(B)` and `F(B) = FJ(B)/ℛ` -/

section Construction

variable (n : ℕ) (B : Type u) [TopologicalSpace B] [ChartedSpace (S n) B]

/-- **`FJ(B)`** (§ 2, proof of the Énoncé, p. 241): « l'ensemble des couples $(j, m)$ d'un jet $j$
de $J(B)$ et d'un point $m$ de $\R^n-\{O\}$ dont l'image sur le quotient $S(n-1)$ de
$\R^n-\{O\}$ soit le but du jet $j$ », with « la topologie induite par celle du produit
$J(B)\times\R^n$ » (the étalé topology on `J(B)`, `Structure/Jets`). -/
def FJ : Type u :=
  {p : jets (GSR n) (S n) B × RnO (n + 1) // Punctured.toSphere p.2 = Jet.value p.1.1}

instance : TopologicalSpace (FJ n B) := instTopologicalSpaceSubtype

variable {n B}

/-- The jet of a point of `FJ(B)`. -/
def FJ.jet (p : FJ n B) : Jet B (S n) := p.1.1.1

/-- The cone point of a point of `FJ(B)`. -/
def FJ.pt (p : FJ n B) : RnO (n + 1) := p.1.2

theorem FJ.mem_jets (p : FJ n B) : p.jet ∈ jets (GSR n) (S n) B := p.1.1.2

theorem FJ.toSphere_pt (p : FJ n B) : Punctured.toSphere p.pt = Jet.value p.jet := p.2

/-- The source of a point of `FJ(B)` in `B`. -/
def FJ.src (p : FJ n B) : B := p.jet.1

theorem FJ.continuous_jet : Continuous (FJ.jet : FJ n B → Jet B (S n)) :=
  continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)

theorem FJ.continuous_pt : Continuous (FJ.pt : FJ n B → RnO (n + 1)) :=
  continuous_snd.comp continuous_subtype_val

theorem FJ.continuous_src : Continuous (FJ.src : FJ n B → B) :=
  continuous_jetSource.comp FJ.continuous_jet

theorem FJ.continuous_jetSub : Continuous fun p : FJ n B => p.1.1 :=
  continuous_fst.comp continuous_subtype_val

/-- `i(g) ∈ GU(n+1)` acting on `ℝⁿ⁺¹ − {O}` lies over `g ∈ GS(n)` acting on `S(n)`. -/
theorem toSphere_isoGUR_smul (g : GSR n) (m : RnO (n + 1)) :
    Punctured.toSphere (isoGUR n g • m) = g • Punctured.toSphere m := by
  show Punctured.toSphere (((isoGUR n g : GUR (n + 1)) : GLR (n + 1)) • m) = _
  rw [Punctured.toSphere_smul_lin]
  exact isoGU_smul g _

variable [HasGroupoid B (projGroupoid n)]

/-- **The relation ℛ** as an action of `GS(n, ℝ)` on `FJ(B)`: `g • (j, m) = (g ∘ j, i(g) m)`, so
that « $(j, m)\approx(j_1, m_1)$ si $j=g\circ j_1$ … et $m=i(g)\,m_1$ » is the orbit relation. -/
instance : MulAction (GSR n) (FJ n B) where
  smul g p := ⟨(⟨jetSMul g p.jet,
      (isJetStructure_jets (G := GSR n) (X := S n) (M := B)).smul_mem g _ p.mem_jets⟩,
      isoGUR n g • p.pt), by
    show Punctured.toSphere (isoGUR n g • p.pt) = Jet.value (jetSMul g p.jet)
    rw [toSphere_isoGUR_smul, value_jetSMul, p.toSphere_pt]⟩
  one_smul p := by
    refine Subtype.ext (Prod.ext (Subtype.ext ?_) ?_)
    · exact jetSMul_one _
    · show isoGUR n 1 • p.pt = p.pt
      rw [map_one, one_smul]
  mul_smul g h p := by
    refine Subtype.ext (Prod.ext (Subtype.ext ?_) ?_)
    · exact jetSMul_mul g h _
    · show isoGUR n (g * h) • p.pt = isoGUR n g • isoGUR n h • p.pt
      rw [map_mul, mul_smul]

@[simp] theorem FJ.jet_smul (g : GSR n) (p : FJ n B) : (g • p).jet = jetSMul g p.jet := rfl

@[simp] theorem FJ.pt_smul (g : GSR n) (p : FJ n B) : (g • p).pt = isoGUR n g • p.pt := rfl

@[simp] theorem FJ.src_smul (g : GSR n) (p : FJ n B) : (g • p).src = p.src := rfl

instance : ContinuousConstSMul (GSR n) (FJ n B) := by
  refine ⟨fun g => continuous_induced_rng.2 ?_⟩
  refine Continuous.prodMk ?_ ?_
  · exact continuous_induced_rng.2 ((continuous_jetSMul g).comp FJ.continuous_jet)
  · exact (continuous_const_smul (isoGUR n g)).comp FJ.continuous_pt

variable (n B) in
/-- **`F(B) = FJ(B)/ℛ`** (§ 2, p. 241, « Nous allons définir $F(B)$ comme un quotient de
$FJ(B)$ »): the orbit space of the action of `GS(n, ℝ)` on `FJ(B)`, quotient topology. -/
def FCone : Type u := MulAction.orbitRel.Quotient (GSR n) (FJ n B)

instance : TopologicalSpace (FCone n B) := instTopologicalSpaceQuotient

namespace FCone

/-- The projection `FJ(B) → F(B)`. -/
def q (p : FJ n B) : FCone n B := Quotient.mk (MulAction.orbitRel (GSR n) (FJ n B)) p

theorem isOpenQuotientMap_q : IsOpenQuotientMap (q : FJ n B → FCone n B) :=
  MulAction.isOpenQuotientMap_quotientMk

theorem continuous_q : Continuous (q : FJ n B → FCone n B) := isOpenQuotientMap_q.continuous

theorem q_surjective : Function.Surjective (q : FJ n B → FCone n B) := Quotient.mk_surjective

@[simp] theorem q_smul (g : GSR n) (p : FJ n B) : q (g • p) = q p :=
  Quotient.sound ⟨g, rfl⟩

theorem q_eq_q_iff {p p' : FJ n B} : q p = q p' ↔ ∃ g : GSR n, g • p' = p := by
  constructor
  · intro h
    exact MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 (Quotient.exact h))
  · rintro ⟨g, rfl⟩
    exact q_smul g p'

/-- A point of `F(B)` from a jet `j ∈ J(B)` and a cone point `m` over the value of `j`. -/
def mk (j : Jet B (S n)) (hj : j ∈ jets (GSR n) (S n) B) (m : RnO (n + 1))
    (hm : Punctured.toSphere m = Jet.value j) : FCone n B :=
  q ⟨(⟨j, hj⟩, m), hm⟩

theorem mk_congr {j j' : Jet B (S n)} {hj : j ∈ jets (GSR n) (S n) B}
    {hj' : j' ∈ jets (GSR n) (S n) B} {m m' : RnO (n + 1)}
    {hm : Punctured.toSphere m = Jet.value j} {hm' : Punctured.toSphere m' = Jet.value j'}
    (h1 : j = j') (h2 : m = m') : mk j hj m hm = mk j' hj' m' hm' := by
  subst h1 h2
  rfl

/-- **ℛ**: `(g ∘ j, i(g) m) ~ (j, m)`. -/
theorem mk_smul (g : GSR n) {j : Jet B (S n)} (hj : j ∈ jets (GSR n) (S n) B)
    (hgj : jetSMul g j ∈ jets (GSR n) (S n) B) {m : RnO (n + 1)}
    (hm : Punctured.toSphere m = Jet.value j)
    (hgm : Punctured.toSphere (isoGUR n g • m) = Jet.value (jetSMul g j)) :
    mk (jetSMul g j) hgj (isoGUR n g • m) hgm = mk j hj m hm :=
  q_smul g (⟨(⟨j, hj⟩, m), hm⟩ : FJ n B)

theorem q_eq_mk (p : FJ n B) : q p = mk p.jet p.mem_jets p.pt p.toSphere_pt := rfl

@[elab_as_elim]
theorem ind {P : FCone n B → Prop}
    (h : ∀ j hj m hm, P (mk j hj m hm)) (x : FCone n B) : P x := by
  obtain ⟨p, rfl⟩ := q_surjective x
  exact h _ _ _ _

/-- **The projection `F(B) → B`** (« la projection source de $FJ(B)$ sur $B$ … compatible avec la
relation d'équivalence ℛ »). -/
def proj : FCone n B → B :=
  Quotient.lift (fun p : FJ n B => p.src) fun p p' hp => by
    obtain ⟨g, rfl⟩ := MulAction.orbitRel_apply.1 hp
    rfl

@[simp] theorem proj_q (p : FJ n B) : proj (q p) = p.src := rfl

@[simp] theorem proj_mk (j : Jet B (S n)) hj m hm : proj (mk (n := n) j hj m hm) = j.1 := rfl

theorem continuous_proj : Continuous (proj : FCone n B → B) :=
  isOpenQuotientMap_q.isQuotientMap.continuous_iff.2 FJ.continuous_src

end FCone

end Construction

/-! ### The cone charts of `F(B)` -/

namespace FCone

variable {n : ℕ} {B : Type u} [TopologicalSpace B] [ChartedSpace (S n) B]
  [HasGroupoid B (projGroupoid n)] {e : OpenPartialHomeomorph B (S n)}

/-- A point of `F(B)` over `b`: the jet at `b` of the preferred chart, with the unit point over its
value. (Used only as a junk value off the chart domains.) -/
def ofPoint (b : B) : FCone n B :=
  mk (jet b (chartAt (S n) b))
    (jet_mem_jets ((projGroupoid n).chart_mem_maximalAtlas b) (mem_chart_source (S n) b))
    (Sphere.unitRep (chartAt (S n) b b)) (by rw [Jet.value_jet, Sphere.toSphere_unitRep])

theorem toSphere_isoGUR_inv_smul (g : GSR n) (m : RnO (n + 1)) :
    Punctured.toSphere ((isoGUR n g)⁻¹ • m) = g⁻¹ • Punctured.toSphere m := by
  rw [← map_inv, toSphere_isoGUR_smul]

open scoped Classical in
/-- The cone chart over a chart `e` of `B`, as a function: `[(j, m)] ↦ i(g)⁻¹ m`, where `j = g ∘ jet e`
(the sheet of `j` over `e`); a junk value off `π⁻¹(e.source)`. -/
def coneFun (he : e ∈ (projGroupoid n).maximalAtlas B) : FCone n B → RnO (n + 1) :=
  Quotient.lift (fun p : FJ n B => if p.src ∈ e.source then
      (isoGUR n (sheetIndex he p.1.1))⁻¹ • p.pt else Classical.arbitrary (RnO (n + 1)))
    fun p p' hp => by
      obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 hp)
      show (if p'.src ∈ e.source then (isoGUR n (sheetIndex he (g • p').1.1))⁻¹ • (g • p').pt
        else _) = if p'.src ∈ e.source then (isoGUR n (sheetIndex he p'.1.1))⁻¹ • p'.pt else _
      split_ifs with h
      · have : sheetIndex he (g • p').1.1 = g * sheetIndex he p'.1.1 :=
          sheetIndex_jetSMul he h g _
        rw [this, FJ.pt_smul, map_mul, mul_inv_rev, mul_smul, inv_smul_smul]
      · rfl

open scoped Classical in
theorem coneFun_mk (he : e ∈ (projGroupoid n).maximalAtlas B) {j : Jet B (S n)} (hj) {m} (hm)
    (hy : j.1 ∈ e.source) :
    coneFun he (mk j hj m hm) = (isoGUR n (sheetIndex he ⟨j, hj⟩))⁻¹ • m := by
  show (if j.1 ∈ e.source then _ else _) = _
  rw [if_pos hy]
  rfl

theorem coneFun_mk_jetSMul (he : e ∈ (projGroupoid n).maximalAtlas B) {y : B} (hy : y ∈ e.source)
    (g : GSR n) (hj) {m} (hm) :
    coneFun he (mk (jetSMul g (jet y e)) hj m hm) = (isoGUR n g)⁻¹ • m := by
  rw [coneFun_mk he hj hm hy, sheetIndex_jetSMul_jet he hy g hj]

theorem coneFun_mk_jet (he : e ∈ (projGroupoid n).maximalAtlas B) {y : B} (hy : y ∈ e.source)
    (hj) {m} (hm) : coneFun he (mk (jet y e) hj m hm) = m := by
  have h1 : jet y e = jetSMul (1 : GSR n) (jet y e) := (jetSMul_one _).symm
  have hj' : jetSMul (1 : GSR n) (jet y e) ∈ jets (GSR n) (S n) B := h1 ▸ hj
  rw [mk_congr (hj' := hj') (hm' := h1 ▸ hm) h1 rfl, coneFun_mk_jetSMul he hy, map_one, inv_one,
    one_smul]

/-- A point of `F(B)` over the source of `e` is `[(g ∘ jet e, m)]` for its sheet `g`. -/
theorem exists_mk_jetSMul (he : e ∈ (projGroupoid n).maximalAtlas B) {x : FCone n B}
    (hx : proj x ∈ e.source) :
    ∃ (g : GSR n) (hj : jetSMul g (jet (proj x) e) ∈ jets (GSR n) (S n) B) (m : RnO (n + 1))
      (hm : Punctured.toSphere m = Jet.value (jetSMul g (jet (proj x) e))),
      x = mk (jetSMul g (jet (proj x) e)) hj m hm := by
  induction x using FCone.ind with
  | h j hj m hm =>
    have h0 := val_eq_jetSMul_sheetIndex he (j := ⟨j, hj⟩) hx
    exact ⟨sheetIndex he ⟨j, hj⟩, h0 ▸ hj, m, h0 ▸ hm, mk_congr h0 rfl⟩

/-- **The cone chart lies over the chart of `B`**: `s(f(x)) = e(π(x))`. -/
theorem toSphere_coneFun (he : e ∈ (projGroupoid n).maximalAtlas B) {x : FCone n B}
    (hx : proj x ∈ e.source) : Punctured.toSphere (coneFun he x) = e (proj x) := by
  obtain ⟨g, hj, m, hm, hxe⟩ := exists_mk_jetSMul he hx
  conv_lhs => rw [hxe]
  rw [coneFun_mk_jetSMul he hx, toSphere_isoGUR_inv_smul, hm, value_jetSMul, Jet.value_jet,
    inv_smul_smul]

open scoped Classical in
/-- The inverse of the cone chart: `w ↦ [(jet_{e⁻¹(s(w))} e, w)]` for `s(w) ∈ e.target`. -/
def coneInv (he : e ∈ (projGroupoid n).maximalAtlas B) (w : RnO (n + 1)) : FCone n B :=
  if hw : Punctured.toSphere w ∈ e.target then
    mk (jet (e.symm (Punctured.toSphere w)) e) (jet_mem_jets he (e.map_target hw)) w
      (by rw [Jet.value_jet, e.right_inv hw])
  else ofPoint (e.symm (Punctured.toSphere w))

theorem coneInv_of_mem (he : e ∈ (projGroupoid n).maximalAtlas B) {w : RnO (n + 1)}
    (hw : Punctured.toSphere w ∈ e.target) :
    coneInv he w = mk (jet (e.symm (Punctured.toSphere w)) e) (jet_mem_jets he (e.map_target hw)) w
      (by rw [Jet.value_jet, e.right_inv hw]) := by
  rw [coneInv, dif_pos hw]

theorem proj_coneInv (he : e ∈ (projGroupoid n).maximalAtlas B) {w : RnO (n + 1)}
    (hw : Punctured.toSphere w ∈ e.target) : proj (coneInv he w) = e.symm (Punctured.toSphere w) := by
  rw [coneInv_of_mem he hw, proj_mk]
  rfl

open scoped Classical in
theorem continuousAt_coneFun (he : e ∈ (projGroupoid n).maximalAtlas B) {x : FCone n B}
    (hx : proj x ∈ e.source) : ContinuousAt (coneFun he) x := by
  obtain ⟨p, rfl⟩ := q_surjective x
  rw [← isOpenQuotientMap_q.continuousAt_comp_iff]
  have hs := sheetIndex_eventually_eq he (j := p.1.1) hx
  refine ((continuous_const_smul (isoGUR n (sheetIndex he p.1.1))⁻¹).comp
    FJ.continuous_pt).continuousAt.congr ?_
  filter_upwards [FJ.continuous_jetSub.continuousAt.eventually hs] with p' hp'
  show _ = (if p'.src ∈ e.source then _ else _)
  rw [if_pos (show p'.src ∈ e.source from hp'.1), hp'.2]
  rfl

theorem continuousOn_coneInv (he : e ∈ (projGroupoid n).maximalAtlas B) :
    ContinuousOn (coneInv he) (Punctured.toSphere ⁻¹' e.target) := by
  rw [continuousOn_iff_continuous_restrict]
  have hc : Continuous fun w : Punctured.toSphere ⁻¹' e.target =>
      e.symm (Punctured.toSphere (w : RnO (n + 1))) :=
    e.continuousOn_symm.comp_continuous (Punctured.continuous_toSphere.comp continuous_subtype_val)
      fun w => w.2
  have hfun : (Punctured.toSphere ⁻¹' e.target).restrict (coneInv he) =
      fun w : Punctured.toSphere ⁻¹' e.target =>
      q ⟨(⟨jet (e.symm (Punctured.toSphere w.1)) e, jet_mem_jets he (e.map_target w.prop)⟩,
        w.1), by rw [Jet.value_jet, e.right_inv w.prop]⟩ := by
    funext w
    exact coneInv_of_mem he w.prop
  rw [hfun]
  refine continuous_q.comp (continuous_induced_rng.2 (Continuous.prodMk ?_ continuous_subtype_val))
  exact continuous_induced_rng.2 ((continuous_jet e).comp hc)

/-- **The cone chart** of `F(B)` over a chart `e` of `B` (§ 2, p. 241: « On appellera carte
compatible d'un ouvert $u$ de $F(B)$ dans $\R^n-\{O\}$ une application composée d'un relèvement de
$u$ dans $FJ(B)$ et de la projection $(j, m)\to m$ »): over `π⁻¹(e.source)`, the lift `y ↦ jet_y e`
of `e.source` into `J(B)` gives the representative `(jet_y e, m)` of each class, and the chart is
`[(jet_y e, m)] ↦ m`, onto the open cone `s⁻¹(e.target)`. -/
def coneChart (he : e ∈ (projGroupoid n).maximalAtlas B) :
    OpenPartialHomeomorph (FCone n B) (RnO (n + 1)) where
  toFun := coneFun he
  invFun := coneInv he
  source := proj ⁻¹' e.source
  target := Punctured.toSphere ⁻¹' e.target
  map_source' x hx := by
    show Punctured.toSphere (coneFun he x) ∈ e.target
    rw [toSphere_coneFun he hx]
    exact e.map_source hx
  map_target' w hw := by
    show proj (coneInv he w) ∈ e.source
    rw [proj_coneInv he hw]
    exact e.map_target hw
  left_inv' x hx := by
    obtain ⟨g, hj, m, hm, hxe⟩ := exists_mk_jetSMul he hx
    have hw : Punctured.toSphere ((isoGUR n g)⁻¹ • m) ∈ e.target := by
      rw [← coneFun_mk_jetSMul he hx g hj hm, ← hxe, toSphere_coneFun he hx]
      exact e.map_source hx
    show coneInv he (coneFun he x) = x
    conv_lhs => rw [hxe]
    conv_rhs => rw [hxe]
    rw [coneFun_mk_jetSMul he hx, coneInv_of_mem he hw]
    have h1 : e.symm (Punctured.toSphere ((isoGUR n g)⁻¹ • m)) = proj x := by
      rw [← coneFun_mk_jetSMul he hx g hj hm, ← hxe, toSphere_coneFun he hx, e.left_inv hx]
    have hj0 : jet (proj x) e ∈ jets (GSR n) (S n) B := jet_mem_jets he hx
    rw [mk_congr (hj' := hj0) (hm' := by rw [← h1]; exact (by rw [Jet.value_jet, e.right_inv hw]))
      (by rw [h1]) rfl]
    rw [← mk_smul g hj0 hj (by rw [Jet.value_jet, ← h1, e.right_inv hw])]
    · exact mk_congr rfl (smul_inv_smul _ _)
    · rw [smul_inv_smul]
      exact hm
  right_inv' w hw := by
    show coneFun he (coneInv he w) = w
    rw [coneInv_of_mem he hw, coneFun_mk_jet he (e.map_target hw)]
  open_source := e.open_source.preimage continuous_proj
  open_target := e.open_target.preimage Punctured.continuous_toSphere
  continuousOn_toFun x hx := (continuousAt_coneFun he hx).continuousWithinAt
  continuousOn_invFun := continuousOn_coneInv he

theorem coneChart_apply (he : e ∈ (projGroupoid n).maximalAtlas B) (x : FCone n B) :
    coneChart he x = coneFun he x := rfl

theorem coneChart_source (he : e ∈ (projGroupoid n).maximalAtlas B) :
    (coneChart he).source = proj ⁻¹' e.source := rfl

theorem coneChart_target (he : e ∈ (projGroupoid n).maximalAtlas B) :
    (coneChart he).target = Punctured.toSphere ⁻¹' e.target := rfl

theorem coneChart_symm_apply (he : e ∈ (projGroupoid n).maximalAtlas B) (w : RnO (n + 1)) :
    (coneChart he).symm w = coneInv he w := rfl

/-- **Transitions of the cone charts are in `GU(n+1, ℝ)`** (§ 2, p. 242, « deux cartes compatibles
d'un même ouvert de $F(B)$ diffèrent l'une de l'autre par une transformation de $GU(n, \R)$ »):
if `e' = g • e` near `π(x)`, then `f_{e'} = i(g) ∘ f_e` near `x`. -/
theorem coneChart_eventually_eq {e' : OpenPartialHomeomorph B (S n)}
    (he : e ∈ (projGroupoid n).maximalAtlas B) (he' : e' ∈ (projGroupoid n).maximalAtlas B)
    {x : FCone n B} (hx : proj x ∈ e.source) (hx' : proj x ∈ e'.source) :
    ∃ g : GSR n, (∀ᶠ z in 𝓝 (proj x), e' z = g • e z) ∧
      ∀ᶠ z in 𝓝 x, coneChart he' z = isoGUR n g • coneChart he z := by
  obtain ⟨g, hg⟩ := eventually_smul_eq_of_mem_maximalAtlas he he' hx hx'
  refine ⟨g, hg, ?_⟩
  have h1 : ∀ᶠ y in 𝓝 (proj x), y ∈ e.source ∧ y ∈ e'.source ∧
      ∀ᶠ z in 𝓝 y, e' z = g • e z :=
    Filter.Eventually.and (e.open_source.mem_nhds hx)
      (Filter.Eventually.and (e'.open_source.mem_nhds hx') hg.eventually_nhds)
  filter_upwards [continuous_proj.continuousAt.eventually h1] with z hz
  obtain ⟨hz1, hz2, hz3⟩ := hz
  induction z using FCone.ind with
  | h j hj m hm =>
    rw [coneChart_apply, coneChart_apply, coneFun_mk he' hj hm hz2, coneFun_mk he hj hm hz1,
      sheetIndex_of_eventually_eq he he' (j := ⟨j, hj⟩) hz1 hz2 hz3, map_mul, map_inv, mul_inv_rev,
      inv_inv, mul_smul]

variable (n B) in
/-- The atlas of `F(B)`: the cone charts over all the charts of the maximal atlas of `B`. -/
def coneAtlas : Set (OpenPartialHomeomorph (FCone n B) (RnO (n + 1))) :=
  {φ | ∃ (e : OpenPartialHomeomorph B (S n)) (he : e ∈ (projGroupoid n).maximalAtlas B),
    φ = coneChart he}

/-- **`F(B)` is charted over `ℝⁿ⁺¹ − {O}`**, the chart at `x` being the cone chart over the preferred
chart of `B` at `π(x)`. -/
instance chartedSpace : ChartedSpace (RnO (n + 1)) (FCone n B) where
  atlas := coneAtlas n B
  chartAt x := coneChart ((projGroupoid n).chart_mem_maximalAtlas (proj x))
  mem_chart_source x := mem_chart_source (S n) (proj x)
  chart_mem_atlas _ := ⟨_, _, rfl⟩

/-- **`F(B)` is an affine conical manifold**: the transitions are locally in `GU(n+1, ℝ)`. -/
instance hasGroupoid : HasGroupoid (FCone n B) (coneGroupoid (n + 1)) where
  compatible := by
    rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
    refine symm_trans_mem_gxGroupoid fun x hx => ?_
    obtain ⟨g, -, hg⟩ := coneChart_eventually_eq he he' hx.1 hx.2
    exact ⟨isoGUR n g, hg⟩

theorem coneChart_mem_maximalAtlas (he : e ∈ (projGroupoid n).maximalAtlas B) :
    coneChart he ∈ (coneGroupoid (n + 1)).maximalAtlas (FCone n B) :=
  (coneGroupoid (n + 1)).subset_maximalAtlas ⟨e, he, rfl⟩

/-- **Every cone chart of `F(B)` is onto an open cone** (Déf. 2, 3°). -/
theorem isConeChart_coneChart (he : e ∈ (projGroupoid n).maximalAtlas B) :
    IsConeChart (n + 1) (coneChart he) := by
  refine ⟨coneChart_mem_maximalAtlas he, (coneChart he).open_target, fun c v hv => ?_⟩
  show Punctured.toSphere (c • v) ∈ e.target
  rw [Punctured.toSphere_smul_pos]
  exact hv

instance hasConeCharts : HasConeCharts (n + 1) (FCone n B) :=
  ⟨fun x => ⟨_, isConeChart_coneChart ((projGroupoid n).chart_mem_maximalAtlas (proj x)),
    mem_chart_source (S n) (proj x)⟩⟩

end FCone

/-! ### `F(B)` is Hausdorff, connected, with a proper `ℝ₊*`-action -/

/-- **Hausdorffness from charts over a Hausdorff base**: if `π : M → Y` is continuous into a
Hausdorff space and any two points of a fibre of `π` lie in the source of one open partial
homeomorphism into a Hausdorff space, `M` is Hausdorff. -/
theorem t2Space_of_fibre_charts {M X Y : Type*} [TopologicalSpace M] [TopologicalSpace X]
    [T2Space X] [TopologicalSpace Y] [T2Space Y] {π : M → Y} (hπ : Continuous π)
    (h : ∀ x x' : M, π x = π x' → ∃ φ : OpenPartialHomeomorph M X, x ∈ φ.source ∧ x' ∈ φ.source) :
    T2Space M := by
  refine ⟨fun x x' hxx' => ?_⟩
  by_cases hπx : π x = π x'
  · obtain ⟨φ, hx, hx'⟩ := h x x' hπx
    have hne : φ x ≠ φ x' := fun H => hxx' (φ.injOn hx hx' H)
    obtain ⟨u, v, hu, hv, hxu, hxv, huv⟩ := t2_separation hne
    exact ⟨φ.source ∩ φ ⁻¹' u, φ.source ∩ φ ⁻¹' v, φ.isOpen_inter_preimage hu,
      φ.isOpen_inter_preimage hv, ⟨hx, hxu⟩, ⟨hx', hxv⟩,
      Disjoint.mono inter_subset_right inter_subset_right (huv.preimage φ)⟩
  · obtain ⟨u, v, hu, hv, hxu, hxv, huv⟩ := t2_separation hπx
    exact ⟨π ⁻¹' u, π ⁻¹' v, hu.preimage hπ, hv.preimage hπ, hxu, hxv, huv.preimage π⟩

/-- `ℝᵏ − {O}` is Hausdorff (a subspace of `ℝᵏ`). A local instance of this file. -/
theorem t2Space_RnO (k : ℕ) : T2Space (RnO k) := Punctured.isEmbedding_val.t2Space

attribute [local instance] t2Space_RnO

namespace FCone

variable {n : ℕ} {B : Type u} [TopologicalSpace B] [ChartedSpace (S n) B]
  [HasGroupoid B (projGroupoid n)] {e : OpenPartialHomeomorph B (S n)}

/-- The preferred chart of `B` at the projection of `x`, as a member of the maximal atlas. -/
theorem chartAt_mem (x : FCone n B) :
    chartAt (S n) (proj x) ∈ (projGroupoid n).maximalAtlas B :=
  (projGroupoid n).chart_mem_maximalAtlas (proj x)

theorem proj_surjective : Function.Surjective (proj : FCone n B → B) := fun b => ⟨ofPoint b, rfl⟩

/-- **`F(B)` is Hausdorff when `B` is** (two points of one fibre lie in one cone chart). -/
instance t2Space [T2Space B] : T2Space (FCone n B) :=
  t2Space_of_fibre_charts (X := RnO (n + 1)) continuous_proj fun x x' h =>
    ⟨coneChart (chartAt_mem x), mem_chart_source (S n) (proj x),
      show proj x' ∈ (chartAt (S n) (proj x)).source from h ▸ mem_chart_source (S n) (proj x)⟩

/-- **`F(B)` is second countable when `B` is** (countably many chart domains of `B` cover it, and
each cone chart domain is homeomorphic to an open subset of `ℝⁿ⁺¹ − {O}`): second countability is
carried by `F` (plan F6). -/
theorem secondCountableTopology [SecondCountableTopology B] :
    SecondCountableTopology (FCone n B) := by
  haveI : SecondCountableTopology (RnO (n + 1)) :=
    Punctured.isEmbedding_val.isInducing.secondCountableTopology
  obtain ⟨s, hs, hcov⟩ := TopologicalSpace.countable_cover_nhds (fun y : B =>
    (chartAt (S n) y).open_source.mem_nhds (mem_chart_source (S n) y))
  haveI := hs.to_subtype
  let U : s → Set (FCone n B) := fun y =>
    (coneChart ((projGroupoid n).chart_mem_maximalAtlas (y : B))).source
  haveI : ∀ i, SecondCountableTopology (U i) := fun i =>
    (coneChart ((projGroupoid n).chart_mem_maximalAtlas (i : B))).toHomeomorphSourceTarget
      |>.secondCountableTopology
  refine TopologicalSpace.secondCountableTopology_of_countable_cover (U := U)
    (fun i => (coneChart _).open_source) (eq_univ_of_forall fun x => ?_)
  have hx : proj x ∈ ⋃ y ∈ s, (chartAt (S n) y).source := hcov ▸ mem_univ _
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 hx
  exact mem_iUnion.2 ⟨⟨y, hy⟩, hxy⟩

/-- The cone chart is `ℝ₊*`-equivariant on representatives: `f([(j, λm)]) = λ f([(j, m)])`. -/
theorem coneFun_mk_smul (he : e ∈ (projGroupoid n).maximalAtlas B) {j : Jet B (S n)} (hj) {m} (hm)
    (hy : j.1 ∈ e.source) (c : RPos) (hcm) :
    coneFun he (mk j hj (c • m) hcm) = c • coneFun he (mk j hj m hm) := by
  rw [coneFun_mk he hj hcm hy, coneFun_mk he hj hm hy, smul_comm]

variable [T2Space B]

/-- **The positive homotheties of `F(B)`** (« $\lambda(j, m)=(j, \lambda m)$ »): Déf. 3's action
`posSMul` on the affine conical manifold `F(B)` is `λ[(j, m)] = [(j, λm)]`. -/
theorem posSMul_mk (c : RPos) {j : Jet B (S n)} (hj) {m} (hm) :
    posSMul (n + 1) c (mk j hj m hm) =
      mk j hj (c • m) (by rw [Punctured.toSphere_smul_pos]; exact hm) := by
  have he := (projGroupoid n).chart_mem_maximalAtlas j.1
  have hy : j.1 ∈ (chartAt (S n) j.1).source := mem_chart_source (S n) j.1
  rw [posSMul_eq (isConeChart_coneChart he) (show proj (mk j hj m hm) ∈ _ from hy),
    coneChart_apply, ← coneFun_mk_smul he hj hm hy c, ← coneChart_apply]
  exact (coneChart he).left_inv (show proj (mk j hj (c • m) _) ∈ _ from hy)

@[simp] theorem proj_posSMul (c : RPos) (x : FCone n B) : proj (posSMul (n + 1) c x) = proj x := by
  induction x using FCone.ind with
  | h j hj m hm => rw [posSMul_mk]; rfl

/-- **The fibres of `F(B) → B` are the orbits of `ℝ₊*`** (« un espace fibré principal de base $B$
et de groupe structural $\R^+$ »). -/
theorem exists_posSMul_eq_of_proj_eq {x x' : FCone n B} (h : proj x = proj x') :
    ∃ c : RPos, posSMul (n + 1) c x = x' := by
  set he := chartAt_mem x
  have hx : proj x ∈ (chartAt (S n) (proj x)).source := mem_chart_source (S n) (proj x)
  have hx' : proj x' ∈ (chartAt (S n) (proj x)).source := h ▸ hx
  have hs : Punctured.toSphere (coneFun he x) = Punctured.toSphere (coneFun he x') := by
    rw [toSphere_coneFun he hx, toSphere_coneFun he hx', h]
  obtain ⟨c, hc⟩ := Punctured.toSphere_eq_toSphere_iff.1 hs
  refine ⟨c, ?_⟩
  rw [posSMul_eq (isConeChart_coneChart he) (show proj x ∈ _ from hx), coneChart_apply, hc,
    ← coneChart_apply]
  exact (coneChart he).left_inv (show proj x' ∈ _ from hx')

omit [T2Space B] in
/-- **`π : F(B) → B` is an open map**: it has continuous local sections through every point,
`y ↦ f⁻¹(r · u(e(y)))` (`u` the unit representative, `r` the radius of `f(x)`). -/
theorem isOpenMap_proj : IsOpenMap (proj : FCone n B → B) := by
  refine isOpenMap_iff_nhds_le.2 fun x => ?_
  set he := chartAt_mem x
  set e := chartAt (S n) (proj x)
  have hx : proj x ∈ e.source := mem_chart_source (S n) (proj x)
  set w₀ := coneFun he x
  set r := Punctured.radius w₀
  set σ : B → FCone n B := fun y => coneInv he (r • Sphere.unitRep (e y))
  have hw : ∀ y ∈ e.source, Punctured.toSphere (r • Sphere.unitRep (e y)) ∈ e.target := by
    intro y hy
    rw [Punctured.toSphere_smul_pos, Sphere.toSphere_unitRep]
    exact e.map_source hy
  have hw₀ : r • Sphere.unitRep (e (proj x)) = w₀ := by
    rw [← toSphere_coneFun he hx, Sphere.unitRep_toSphere, smul_inv_smul]
  have hσx : σ (proj x) = x := by
    show coneInv he _ = x
    rw [hw₀]
    exact (coneChart he).left_inv (show proj x ∈ _ from hx)
  have hev : proj ∘ σ =ᶠ[𝓝 (proj x)] id := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    show proj (coneInv he _) = y
    rw [proj_coneInv he (hw y hy), Punctured.toSphere_smul_pos, Sphere.toSphere_unitRep,
      e.left_inv hy]
  have hσ : ContinuousAt σ (proj x) := by
    refine ((continuousOn_coneInv he).continuousAt ?_).comp ?_
    · exact (coneChart he).open_target.mem_nhds (hw _ hx)
    · exact (continuous_const_smul r).continuousAt.comp
        (Sphere.continuous_unitRep.continuousAt.comp (e.continuousAt hx))
  have h2 : Tendsto σ (𝓝 (proj x)) (𝓝 x) := by
    have := hσ.tendsto
    rwa [hσx] at this
  have h1 : map proj (map σ (𝓝 (proj x))) ≤ map proj (𝓝 x) := map_mono h2
  rwa [Filter.map_map, map_congr hev, map_id] at h1

omit [T2Space B] in
theorem isOpenQuotientMap_proj : IsOpenQuotientMap (proj : FCone n B → B) :=
  ⟨proj_surjective, continuous_proj, isOpenMap_proj⟩

/-- **`F(B)` is connected when `B` is**: `π` is a quotient map whose fibres, the `ℝ₊*`-orbits, are
connected. -/
theorem connectedSpace [ConnectedSpace B] : ConnectedSpace (FCone n B) := by
  haveI := connectedSpace_RPos
  have hfib : ∀ t : B, IsConnected (proj ⁻¹' {t} : Set (FCone n B)) := by
    intro t
    obtain ⟨x, rfl⟩ := proj_surjective (n := n) t
    have : proj ⁻¹' {proj x} = range fun c : RPos => posSMul (n + 1) c x := by
      ext x'
      simp only [mem_preimage, mem_singleton_iff, mem_range]
      exact ⟨fun h => exists_posSMul_eq_of_proj_eq h.symm, fun ⟨c, hc⟩ => hc ▸ proj_posSMul c x⟩
    rw [this]
    exact isConnected_range (continuous_posSMul.comp (continuous_id.prodMk continuous_const))
  have := isOpenQuotientMap_proj.isQuotientMap.isCoinducing.isConnected_preimage_of_isClosed hfib
    isClosed_univ isConnected_univ
  rw [preimage_univ] at this
  exact connectedSpace_iff_univ.2 this

/-- **The base map `F(B)/ℝ₊* → B`** induced by `π` (« le quotient … de base $B$ »). -/
def baseProj : ConeBase n (FCone n B) → B :=
  Quotient.lift proj fun x x' h => by
    obtain ⟨c, rfl⟩ := ConeBase.rel_iff.1 h
    exact proj_posSMul c x'

@[simp] theorem baseProj_mk (x : FCone n B) : baseProj (ConeBase.mk x) = proj x := rfl

theorem continuous_baseProj : Continuous (baseProj : ConeBase n (FCone n B) → B) :=
  ConeBase.isOpenQuotientMap_mk.isQuotientMap.continuous_iff.2 continuous_proj

theorem baseProj_injective : Function.Injective (baseProj : ConeBase n (FCone n B) → B) := by
  intro b b' h
  obtain ⟨x, rfl⟩ := ConeBase.mk_surjective b
  obtain ⟨x', rfl⟩ := ConeBase.mk_surjective b'
  obtain ⟨c, hc⟩ := exists_posSMul_eq_of_proj_eq (n := n) h.symm
  exact ConeBase.mk_eq_mk_iff.2 ⟨c, hc⟩

theorem baseProj_surjective : Function.Surjective (baseProj : ConeBase n (FCone n B) → B) :=
  fun b => ⟨ConeBase.mk (ofPoint b), rfl⟩

/-- **The base of `F(B)` is Hausdorff** (it injects continuously into `B`). -/
theorem t2Space_coneBase : T2Space (ConeBase n (FCone n B)) :=
  T2Space.of_injective_continuous baseProj_injective continuous_baseProj

/-- **The action of `ℝ₊*` on `F(B)` is proper** (DEC-122's hypothesis, equivalent to the base being
Hausdorff, `ConeBase.t2Space_iff_properSMul`). -/
theorem properSMul : @ProperSMul RPos (FCone n B) _ _ _ (coneMulAction (n + 1) (FCone n B)) :=
  haveI := t2Space_coneBase (n := n) (B := B)
  ConeBase.properSMul_of_t2Space

end FCone

/-! ### `F(φ)`: the image of a morphism -/

section JetComp

variable {M₁ : Type u} [TopologicalSpace M₁] {M₂ : Type v} [TopologicalSpace M₂] {X : Type w}

/-- **`j₂ ∘ φ = j₁` for jets** (§ 2, p. 242, the printed « $\varphi\circ j_2=j_1$ », l.640, a misprint
of order flagged `[sic]`, read `j₂ ∘ φ = j₁`, DEC-127): `j₂` is the jet at `φ(y)` of a map `f` and
`j₁` the jet at `y` of `f ∘ φ`, `y` the source of `j₁`. For `φ` continuous at `y` the composite does
not depend on the map `f` representing `j₂` (`JetCompEq.jet_comp`). -/
def JetCompEq (φ : M₁ → M₂) (j₂ : Jet M₂ X) (j₁ : Jet M₁ X) : Prop :=
  ∃ f : M₂ → X, j₂ = jet (φ j₁.1) f ∧ j₁ = jet j₁.1 (f ∘ φ)

/-- The jet at `y` of `f ∘ φ` depends only on the jet of `f` at `φ(y)`. -/
theorem jet_comp_congr {φ : M₁ → M₂} {y : M₁} (hφ : ContinuousAt φ y) {f f' : M₂ → X}
    (h : jet (φ y) f = jet (φ y) f') : jet y (f ∘ φ) = jet y (f' ∘ φ) :=
  jet_eq_jet_iff.2 ((jet_eq_jet_iff.1 h).comp_tendsto hφ)

/-- **`j₂ ∘ φ = j₁` does not depend on the representative of `j₂`**: if `j₂ ∘ φ = j₁`, every map `f`
with `jet_{φ(y)} f = j₂` has `jet_y (f ∘ φ) = j₁`. -/
theorem JetCompEq.jet_comp {φ : M₁ → M₂} {j₂ : Jet M₂ X} {j₁ : Jet M₁ X} (h : JetCompEq φ j₂ j₁)
    (hφ : ContinuousAt φ j₁.1) {f : M₂ → X} (hf : j₂ = jet (φ j₁.1) f) :
    j₁ = jet j₁.1 (f ∘ φ) := by
  obtain ⟨f₀, h₀, h₁⟩ := h
  exact h₁.trans (jet_comp_congr hφ (h₀.symm.trans hf))

end JetComp

section JetExists

variable {M : Type u} [TopologicalSpace M] {X : Type v} [TopologicalSpace X]
  {G : Type w} [Group G] [MulAction G X] [ContinuousConstSMul G X] [ChartedSpace X M]
  [HasGroupoid M (gxGroupoid G X)]

/-- A jet of `J(V)` at `x` is `g ∘ jet_x f` for any `f` with `jet_x f ∈ J(V)` (2° of Déf. 12). -/
theorem exists_eq_jetSMul_of_mem {j : Jet M X} (hj : j ∈ jets G X M) {f : M → X}
    (hf : jet j.1 f ∈ jets G X M) : ∃ g : G, j = jetSMul g (jet j.1 f) := by
  obtain ⟨x, γ⟩ := j
  obtain ⟨g, hg⟩ := (isJetStructure_jets (G := G) (X := X) (M := M)).transitive x _ γ hf hj
  exact ⟨g, by rw [hg]; rfl⟩

end JetExists

namespace FCone

variable {n : ℕ} {B₁ : Type u} [TopologicalSpace B₁] [ChartedSpace (S n) B₁]
  [HasGroupoid B₁ (projGroupoid n)] {B₂ : Type v} [TopologicalSpace B₂] [ChartedSpace (S n) B₂]
  [HasGroupoid B₂ (projGroupoid n)] {φ : B₁ → B₂}

/-- **`J(B₂) ∘ φ ⊆ J(B₁)`** for a morphism `φ` (p. 238), on jets of maps. -/
theorem jet_comp_mem (hφ : IsGXMorphism (GSR n) (S n) φ) {y : B₁} {f : B₂ → S n}
    (hf : jet (φ y) f ∈ jets (GSR n) (S n) B₂) : jet y (f ∘ φ) ∈ jets (GSR n) (S n) B₁ := by
  have := (isGXMorphism_iff_jets hφ.continuous).1 hφ y _ hf
  rw [Germ.coe_compTendsto] at this
  exact this

theorem jet_chartAt_mem (b : B₂) :
    jet b (chartAt (S n) b) ∈ jets (GSR n) (S n) B₂ :=
  jet_mem_jets ((projGroupoid n).chart_mem_maximalAtlas b) (mem_chart_source (S n) b)

/-- The sheet of a jet `j ∈ J(B₁)` against the preferred chart at `φ(y)` read through `φ`:
`j = g ∘ jet_y (c ∘ φ)`. -/
def pushIndex (hφ : IsGXMorphism (GSR n) (S n) φ) (j : jets (GSR n) (S n) B₁) : GSR n :=
  (exists_eq_jetSMul_of_mem j.2 (jet_comp_mem hφ (jet_chartAt_mem (φ j.1.1)))).choose

theorem pushIndex_spec (hφ : IsGXMorphism (GSR n) (S n) φ) (j : jets (GSR n) (S n) B₁) :
    j.1 = jetSMul (pushIndex hφ j) (jet j.1.1 (chartAt (S n) (φ j.1.1) ∘ φ)) :=
  (exists_eq_jetSMul_of_mem j.2 (jet_comp_mem hφ (jet_chartAt_mem (φ j.1.1)))).choose_spec

/-- **The push-forward of a jet along a local isomorphism** (« on peut trouver un jet et un seul
$j_2$ de $J(B_2)$ tel que $\varphi\circ j_2=j_1$ », l.639–640; the printed « $\varphi\circ j_2$ » is a
misprint of order flagged `[sic]`, read `j₂ ∘ φ = j₁`, DEC-127): for `j₁ = g ∘ jet_y (c ∘ φ)`,
`j₂ = g ∘ jet_{φ(y)} c`, the unique `j₂ ∈ J(B₂)` with `j₂ ∘ φ = j₁` (`existsUnique_pushJet`). -/
def pushJet (hφ : IsGXMorphism (GSR n) (S n) φ) (j : jets (GSR n) (S n) B₁) : Jet B₂ (S n) :=
  jetSMul (pushIndex hφ j) (jet (φ j.1.1) (chartAt (S n) (φ j.1.1)))

theorem pushJet_mem (hφ : IsGXMorphism (GSR n) (S n) φ) (j : jets (GSR n) (S n) B₁) :
    pushJet hφ j ∈ jets (GSR n) (S n) B₂ :=
  (isJetStructure_jets (G := GSR n) (X := S n) (M := B₂)).smul_mem _ _ (jet_chartAt_mem _)

/-- **`j₂` is characterised by `j₂ ∘ φ = j₁`**: whenever `j₁ = g ∘ jet_y (f ∘ φ)` with
`jet_{φ(y)} f ∈ J(B₂)`, the push-forward is `g ∘ jet_{φ(y)} f` (uniqueness: the fibres of `J(B₁)`
are free `GS`-orbits). -/
theorem pushJet_eq (hφ : IsGXMorphism (GSR n) (S n) φ) {j : jets (GSR n) (S n) B₁} {f : B₂ → S n}
    (hf : jet (φ j.1.1) f ∈ jets (GSR n) (S n) B₂) {g : GSR n}
    (hj : j.1 = jetSMul g (jet j.1.1 (f ∘ φ))) : pushJet hφ j = jetSMul g (jet (φ j.1.1) f) := by
  set y := j.1.1
  set c := chartAt (S n) (φ y)
  obtain ⟨h, hh⟩ := exists_eventually_smul_of_jet_mem (jet_chartAt_mem (φ y)) hf
  have h1 : jet (φ y) f = jetSMul h (jet (φ y) c) := by
    rw [jetSMul_jet, jet_eq_jet_iff]
    exact hh
  have h2 : jet y (f ∘ φ) = jetSMul h (jet y (c ∘ φ)) := by
    rw [jetSMul_jet, jet_eq_jet_iff]
    exact hφ.continuous.continuousAt.eventually hh
  have h3 : jetSMul (pushIndex hφ j) (jet y (c ∘ φ)) = jetSMul (g * h) (jet y (c ∘ φ)) := by
    rw [← pushIndex_spec hφ j, hj, h2, jetSMul_mul]
  have h4 := eq_of_jetSMul_eq (jet_comp_mem hφ (jet_chartAt_mem (φ y))) h3
  rw [pushJet, h4, jetSMul_mul, ← h1]

/-- `pushJet hφ j₁ ∘ φ = j₁`. -/
theorem jetCompEq_pushJet (hφ : IsGXMorphism (GSR n) (S n) φ) (j : jets (GSR n) (S n) B₁) :
    JetCompEq φ (pushJet hφ j) j.1 :=
  ⟨fun z => pushIndex hφ j • chartAt (S n) (φ j.1.1) z, jetSMul_jet _ _ _,
    (pushIndex_spec hφ j).trans (jetSMul_jet _ _ _)⟩

/-- **« on peut trouver un jet et un seul $j_2$ de $J(B_2)$ tel que $\varphi\circ j_2=j_1$ »**
(l.639–640, read `j₂ ∘ φ = j₁`, DEC-127): for every `j₁ ∈ J(B₁)` there is exactly one jet
`j₂ ∈ J(B₂)` with `j₂ ∘ φ = j₁` (`JetCompEq`), namely `pushJet hφ j₁`. -/
theorem existsUnique_pushJet (hφ : IsGXMorphism (GSR n) (S n) φ) (j : jets (GSR n) (S n) B₁) :
    ∃! j₂ : Jet B₂ (S n), j₂ ∈ jets (GSR n) (S n) B₂ ∧ JetCompEq φ j₂ j.1 := by
  refine ⟨pushJet hφ j, ⟨pushJet_mem hφ j, jetCompEq_pushJet hφ j⟩, ?_⟩
  rintro j₂ ⟨hm, f, h₁, h₂⟩
  rw [h₁] at hm ⊢
  rw [pushJet_eq hφ (j := j) hm (g := 1) (by rw [jetSMul_one]; exact h₂), jetSMul_one]

theorem value_pushJet (hφ : IsGXMorphism (GSR n) (S n) φ) (j : jets (GSR n) (S n) B₁) :
    Jet.value (pushJet hφ j) = Jet.value j.1 := by
  rw [pushJet, value_jetSMul, pushIndex_spec hφ j, value_jetSMul]
  rfl

theorem pushJet_smul (hφ : IsGXMorphism (GSR n) (S n) φ) (g : GSR n) (j : jets (GSR n) (S n) B₁)
    (hgj : jetSMul g j.1 ∈ jets (GSR n) (S n) B₁) :
    pushJet hφ ⟨jetSMul g j.1, hgj⟩ = jetSMul g (pushJet hφ j) := by
  rw [pushJet_eq hφ (j := ⟨jetSMul g j.1, hgj⟩) (g := g * pushIndex hφ j)
    (jet_chartAt_mem (φ j.1.1)) (by
      show jetSMul g j.1 = jetSMul (g * pushIndex hφ j) (jet j.1.1 (chartAt (S n) (φ j.1.1) ∘ φ))
      rw [jetSMul_mul, ← pushIndex_spec hφ j]), pushJet, jetSMul_mul]
  rfl

/-- **`F(φ)`** (§ 2, p. 242, « $\varphi'(j_1, m)=(j_2, m)$. L'application $\varphi'$ étant compatible
avec la relation ℛ définit une application de $F(B_1)$ dans $F(B_2)$ »). -/
def map (hφ : IsGXMorphism (GSR n) (S n) φ) : FCone n B₁ → FCone n B₂ :=
  Quotient.lift (fun p : FJ n B₁ => mk (pushJet hφ p.1.1) (pushJet_mem hφ _) p.pt
      (by rw [value_pushJet]; exact p.toSphere_pt))
    fun p p' hp => by
      obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 hp)
      exact (mk_congr (hj' := (isJetStructure_jets (G := GSR n) (X := S n) (M := B₂)).smul_mem g _
        (pushJet_mem hφ p'.1.1)) (hm' := by
          rw [FJ.pt_smul, toSphere_isoGUR_smul, value_jetSMul, value_pushJet]
          exact congrArg (g • ·) p'.toSphere_pt)
        (pushJet_smul hφ g p'.1.1 _) rfl).trans (mk_smul g (pushJet_mem hφ _) _ _ _)

theorem map_mk (hφ : IsGXMorphism (GSR n) (S n) φ) {j : Jet B₁ (S n)} (hj) {m} (hm) :
    map hφ (mk j hj m hm) = mk (pushJet hφ ⟨j, hj⟩) (pushJet_mem hφ _) m
      (by rw [value_pushJet]; exact hm) := rfl

/-- **`F(φ)` on a representative**: if `j = g ∘ jet_y (f ∘ φ)` with `jet_{φ(y)} f ∈ J(B₂)`, then
`F(φ)[(j, m)] = [(g ∘ jet_{φ(y)} f, m)]`. -/
theorem map_mk_of_eq (hφ : IsGXMorphism (GSR n) (S n) φ) {j : Jet B₁ (S n)} (hj) {m} (hm)
    {f : B₂ → S n} (hf : jet (φ j.1) f ∈ jets (GSR n) (S n) B₂) {g : GSR n}
    (hjf : j = jetSMul g (jet j.1 (f ∘ φ))) :
    map hφ (mk j hj m hm) = mk (jetSMul g (jet (φ j.1) f))
      ((isJetStructure_jets (G := GSR n) (X := S n) (M := B₂)).smul_mem g _ hf) m
      (by rw [hm, hjf, value_jetSMul, value_jetSMul]; rfl) := by
  rw [map_mk]
  exact mk_congr (pushJet_eq hφ (j := ⟨j, hj⟩) hf hjf) rfl

@[simp] theorem proj_map (hφ : IsGXMorphism (GSR n) (S n) φ) (x : FCone n B₁) :
    proj (map hφ x) = φ (proj x) := by
  induction x using FCone.ind with
  | h j hj m hm => rfl

/-- **`F(φ)` read in cone charts is `i(g)` where `φ` reads as `g`**: if `e₂ ∘ φ = g • e₁` near `π(x)`
(`e₁`, `e₂` charts of the maximal atlases), then `f_{e₂} ∘ F(φ) = i(g) • f_{e₁}` near `x`. -/
theorem map_eventually_eq_of_eventually_eq (hφ : IsGXMorphism (GSR n) (S n) φ)
    {e₁ : OpenPartialHomeomorph B₁ (S n)} {e₂ : OpenPartialHomeomorph B₂ (S n)}
    (he₁ : e₁ ∈ (projGroupoid n).maximalAtlas B₁) (he₂ : e₂ ∈ (projGroupoid n).maximalAtlas B₂)
    {x : FCone n B₁} (hx : proj x ∈ e₁.source) (hx₂ : φ (proj x) ∈ e₂.source) {g : GSR n}
    (hg : ∀ᶠ z in 𝓝 (proj x), e₂ (φ z) = g • e₁ z) :
    ∀ᶠ x' in 𝓝 x, map hφ x' ∈ (coneChart he₂).source ∧
      coneChart he₂ (map hφ x') = isoGUR n g • coneChart he₁ x' := by
  have h1 : ∀ᶠ y in 𝓝 (proj x), y ∈ e₁.source ∧ φ y ∈ e₂.source ∧
      ∀ᶠ z in 𝓝 y, e₂ (φ z) = g • e₁ z :=
    Filter.Eventually.and (e₁.open_source.mem_nhds hx)
      (Filter.Eventually.and (hφ.continuous.continuousAt.preimage_mem_nhds
        (e₂.open_source.mem_nhds hx₂)) hg.eventually_nhds)
  filter_upwards [continuous_proj.continuousAt.eventually h1] with x' hx'
  obtain ⟨hy1, hy2, hy3⟩ := hx'
  refine ⟨show proj (map hφ x') ∈ e₂.source by rw [proj_map]; exact hy2, ?_⟩
  induction x' using FCone.ind with
  | h j hj m hm =>
    have hy1' : j.1 ∈ e₁.source := hy1
    have hy2' : φ j.1 ∈ e₂.source := hy2
    have hy3' : ∀ᶠ z in 𝓝 j.1, e₂ (φ z) = g • e₁ z := hy3
    set s := sheetIndex he₁ ⟨j, hj⟩
    have hjf : j = jetSMul (s * g⁻¹) (jet j.1 (e₂ ∘ φ)) := by
      refine (val_eq_jetSMul_sheetIndex he₁ (j := ⟨j, hj⟩) hy1').trans ?_
      show jetSMul s (jet j.1 e₁) = _
      rw [jetSMul_mul, jetSMul_jet g⁻¹]
      congr 1
      rw [jet_eq_jet_iff]
      filter_upwards [hy3'] with z hz
      simp only [Function.comp_apply, hz, inv_smul_smul]
    rw [map_mk_of_eq hφ hj hm (jet_mem_jets he₂ hy2') hjf, coneChart_apply, coneChart_apply,
      coneFun_mk_jetSMul he₂ hy2', coneFun_mk he₁ hj hm hy1', map_mul, map_inv, mul_inv_rev,
      inv_inv, mul_smul]

/-- **`F(φ)` read in cone charts is an element of `GU(n+1, ℝ)`**: if `φ` reads as `g ∈ GS(n, ℝ)` in
charts `e₁` at `π(x)`, `e₂` at `φ(π(x))` of the maximal atlases, then `F(φ)` reads as `i(g)` in the
cone charts over them. -/
theorem map_eventually_eq_of_mem (hφ : IsGXMorphism (GSR n) (S n) φ)
    {e₁ : OpenPartialHomeomorph B₁ (S n)} {e₂ : OpenPartialHomeomorph B₂ (S n)}
    (he₁ : e₁ ∈ (projGroupoid n).maximalAtlas B₁) (he₂ : e₂ ∈ (projGroupoid n).maximalAtlas B₂)
    {x : FCone n B₁} (hx : proj x ∈ e₁.source) (hx₂ : φ (proj x) ∈ e₂.source) :
    ∃ g : GSR n, ∀ᶠ x' in 𝓝 x, map hφ x' ∈ (coneChart he₂).source ∧
      coneChart he₂ (map hφ x') = isoGUR n g • coneChart he₁ x' := by
  obtain ⟨g, hg⟩ := hφ.exists_smul_eq_of_mem_maximalAtlas he₁ he₂ hx hx₂
  exact ⟨g, map_eventually_eq_of_eventually_eq hφ he₁ he₂ hx hx₂ hg⟩

/-- `F(φ)` in the preferred cone charts. -/
theorem map_eventually_eq (hφ : IsGXMorphism (GSR n) (S n) φ) (x : FCone n B₁) :
    ∃ g : GSR n, ∀ᶠ x' in 𝓝 x, map hφ x' ∈ (coneChart (chartAt_mem (map hφ x))).source ∧
      coneChart (chartAt_mem (map hφ x)) (map hφ x') =
        isoGUR n g • coneChart (chartAt_mem x) x' :=
  map_eventually_eq_of_mem hφ (chartAt_mem x) (chartAt_mem (map hφ x))
    (mem_chart_source (S n) (proj x)) (by rw [← proj_map hφ x]; exact mem_chart_source (S n) _)

theorem continuous_map (hφ : IsGXMorphism (GSR n) (S n) φ) : Continuous (map hφ) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨g, hg⟩ := map_eventually_eq hφ x
  set φ₁ := coneChart (chartAt_mem x)
  set φ₂ := coneChart (chartAt_mem (map hφ x))
  have hx : x ∈ φ₁.source := mem_chart_source (S n) (proj x)
  have hmx : isoGUR n g • φ₁ x ∈ φ₂.target := by
    rw [← (hg.self_of_nhds).2]
    exact φ₂.map_source (hg.self_of_nhds).1
  refine ContinuousAt.congr (f := fun x' => φ₂.symm (isoGUR n g • φ₁ x')) ?_ ?_
  · exact ContinuousAt.comp (f := fun x' => isoGUR n g • φ₁ x') (φ₂.continuousAt_symm hmx)
      ((φ₁.continuousAt hx).const_smul (isoGUR n g))
  · filter_upwards [hg] with x' hx'
    rw [← hx'.2]
    exact φ₂.left_inv hx'.1

/-- **`F(φ)` is a morphism of affine conical manifolds** (« $F(\varphi)$ est aussi un isomorphisme
local de $F(B_1)$ dans $F(B_2)$, d'où l'on déduit facilement qu'il est un morphisme de la catégorie
des variétés coniques affines »). -/
theorem isGXMorphism_map (hφ : IsGXMorphism (GSR n) (S n) φ) :
    IsGXMorphism (GUR (n + 1)) (RnO (n + 1)) (map hφ) := by
  refine isGXMorphism_of_mem_maximalAtlas (continuous_map hφ) fun x => ?_
  obtain ⟨g, hg⟩ := map_eventually_eq hφ x
  exact ⟨_, coneChart_mem_maximalAtlas (chartAt_mem x), _,
    coneChart_mem_maximalAtlas (chartAt_mem (map hφ x)), mem_chart_source (S n) (proj x),
    mem_chart_source (S n) (proj (map hφ x)), isoGUR n g,
    hg.mono fun _ h => h.2⟩

/-- `F(id) = id`. -/
theorem map_id : map (isGXMorphism_id (G := GSR n) (X := S n) (M := B₁)) = id := by
  funext x
  induction x using FCone.ind with
  | h j hj m hm =>
    obtain ⟨g, hg⟩ := exists_eq_jetSMul_of_mem hj (jet_chartAt_mem j.1)
    have hg' : j = jetSMul g (jet j.1 (chartAt (S n) j.1 ∘ id)) := hg
    show map _ (mk j hj m hm) = mk j hj m hm
    rw [map_mk_of_eq (φ := id) isGXMorphism_id hj hm (f := chartAt (S n) j.1)
      (jet_chartAt_mem j.1) hg']
    exact mk_congr hg.symm rfl

/-- `F(ψ ∘ φ) = F(ψ) ∘ F(φ)`. -/
theorem map_comp {B₃ : Type w} [TopologicalSpace B₃] [ChartedSpace (S n) B₃]
    [HasGroupoid B₃ (projGroupoid n)] {ψ : B₂ → B₃}
    (hψ : IsGXMorphism (GSR n) (S n) ψ) (hφ : IsGXMorphism (GSR n) (S n) φ) :
    map (hψ.comp hφ) = map hψ ∘ map hφ := by
  funext x
  induction x using FCone.ind with
  | h j hj m hm =>
    have hc := jet_chartAt_mem (n := n) (ψ (φ j.1))
    obtain ⟨g, hg⟩ := exists_eq_jetSMul_of_mem hj (jet_comp_mem (hψ.comp hφ) hc)
    have hc' : jet (φ j.1) (chartAt (S n) (ψ (φ j.1)) ∘ ψ) ∈ jets (GSR n) (S n) B₂ :=
      jet_comp_mem hψ hc
    rw [Function.comp_apply, map_mk_of_eq _ hj hm hc hg, map_mk_of_eq hφ hj hm hc' hg,
      map_mk_of_eq hψ _ _ hc rfl]
    rfl

end FCone

/-! ### « $FJ(B)$ s'identifie avec $J_1(F(B))$ » (l.568, l.604) -/

namespace FCone

variable {n : ℕ} {B : Type u} [TopologicalSpace B] [ChartedSpace (S n) B]
  [HasGroupoid B (projGroupoid n)] {e : OpenPartialHomeomorph B (S n)}

/-- **The jet of `F(B)` carried by a point of `FJ(B)`** (§ 2, p. 241, « On appellera carte compatible
… une application composée d'un relèvement de $u$ dans $FJ(B)$ et de la projection $(j, m)\to m$ »;
« on peut trouver une carte compatible et une seule d'un voisinage convenable de $p$ qui soit
composée d'un relèvement de ce voisinage sur un voisinage de $(j, m)$ et de la projection »): the
jet at `[(j, m)]` of the compatible chart through `(j, m)`. Over a chart `e` of `B` with
`j = g ∘ jet_y e`, the lift through `(j, m)` is `x' ↦ (g ∘ jet_{π(x')} e, i(g) f_e(x'))`, so that chart
is `i(g) • f_e` (`f_e = coneChart`), and `fjJet (j, m) = i(g) ∘ jet_{[(j, m)]} f_e`; it does not depend
on `e` (`fjJet_eq`). -/
def fjJet (p : FJ n B) : Jet (FCone n B) (RnO (n + 1)) :=
  jetSMul (isoGUR n (sheetIndex (chartAt_mem (q p)) p.1.1)) (jet (q p) (coneChart (chartAt_mem (q p))))

/-- **`fjJet` does not depend on the chart of `B`**: for every chart `e` of the maximal atlas at the
source `y` of `(j, m)`, `fjJet (j, m) = i(g) ∘ jet_{[(j,m)]} f_e`, `g` the sheet of `j` over `e`. -/
theorem fjJet_eq (he : e ∈ (projGroupoid n).maximalAtlas B) {p : FJ n B} (hp : p.src ∈ e.source) :
    fjJet p = jetSMul (isoGUR n (sheetIndex he p.1.1)) (jet (q p) (coneChart he)) := by
  have he₀ := chartAt_mem (q p)
  have hp₀ : proj (q p) ∈ (chartAt (S n) (proj (q p))).source := mem_chart_source (S n) _
  obtain ⟨g, hg, hc⟩ := coneChart_eventually_eq he₀ he (x := q p) hp₀ hp
  have hs : sheetIndex he p.1.1 = sheetIndex he₀ p.1.1 * g⁻¹ :=
    sheetIndex_of_eventually_eq he₀ he (j := p.1.1) hp₀ hp hg
  have hj : jet (q p) (coneChart he) = jetSMul (isoGUR n g) (jet (q p) (coneChart he₀)) := by
    rw [jetSMul_jet, jet_eq_jet_iff]
    exact hc
  rw [hs, hj, ← jetSMul_mul, map_mul, map_inv, inv_mul_cancel_right]
  rfl

/-- `fjJet (j, m)` is a jet of `J₁(F(B))`: the jet of a cone chart of `F(B)`, composed with `i(g)`. -/
theorem fjJet_mem (p : FJ n B) : fjJet p ∈ jets (GUR (n + 1)) (RnO (n + 1)) (FCone n B) :=
  jetSMul_jet_mem_jets (coneChart_mem_maximalAtlas (chartAt_mem (q p)))
    (mem_chart_source (S n) (proj (q p))) _

/-- The source of `fjJet (j, m)` is the class `[(j, m)]`. -/
@[simp] theorem fjJet_fst (p : FJ n B) : (fjJet p).1 = q p := rfl

/-- The value of `fjJet (j, m)` is `m`: « la projection $(j, m)\to m$ ». -/
theorem value_fjJet (p : FJ n B) : Jet.value (fjJet p) = p.pt := by
  have h : coneFun (chartAt_mem (q p)) (q p) =
      (isoGUR n (sheetIndex (chartAt_mem (q p)) p.1.1))⁻¹ • p.pt :=
    coneFun_mk (chartAt_mem (q p)) p.mem_jets p.toSphere_pt (mem_chart_source (S n) p.src)
  rw [fjJet, value_jetSMul, Jet.value_jet, coneChart_apply, h, smul_inv_smul]

/-- **Equivariance**: the relation ℛ on `FJ(B)` is carried to post-composition by `GU(n+1, ℝ)` on
`J₁(F(B))`, through `i`: `fjJet (g ∘ j, i(g) m) = i(g) ∘ fjJet (j, m)`. -/
theorem fjJet_smul (g : GSR n) (p : FJ n B) : fjJet (g • p) = jetSMul (isoGUR n g) (fjJet p) := by
  have he := chartAt_mem (q p)
  have hp : p.src ∈ (chartAt (S n) (proj (q p))).source := mem_chart_source (S n) _
  rw [fjJet_eq he (p := g • p) hp, fjJet_eq he hp, q_smul]
  rw [show sheetIndex he (g • p).1.1 = g * sheetIndex he p.1.1 from
    sheetIndex_jetSMul he hp g _, map_mul, jetSMul_mul]

/-- `fjJet` is injective: two points with the same jet are ℛ-equivalent, `(j, m) = g • (j', m')`,
and then `i(g)` fixes a jet of `J₁(F(B))`, so `g = 1` (the fibres of `J₁(F(B))` are free orbits). -/
theorem fjJet_injective : Function.Injective (fjJet : FJ n B → Jet (FCone n B) (RnO (n + 1))) := by
  intro p p' h
  have hq : q p = q p' := congrArg Sigma.fst h
  obtain ⟨g, rfl⟩ := q_eq_q_iff.1 hq
  rw [fjJet_smul] at h
  have h1 : isoGUR n g = 1 := eq_one_of_jetSMul_eq (fjJet_mem p') h
  rw [(isoGUR n).map_eq_one_iff.1 h1, one_smul]


/-- The inverse construction over a chart `e` of `B`: a jet `J = h ∘ jet_x f_e` of `J₁(F(B))`
(`h` its sheet over the cone chart `f_e`) gives `(i⁻¹(h) ∘ jet_{π(x)} e, h f_e(x)) ∈ FJ(B)`. -/
def fjOfJetAt (he : e ∈ (projGroupoid n).maximalAtlas B)
    (J : jets (GUR (n + 1)) (RnO (n + 1)) (FCone n B)) (hx : proj J.1.1 ∈ e.source) : FJ n B :=
  ⟨(⟨jetSMul ((isoGUR n).symm (sheetIndex (coneChart_mem_maximalAtlas he) J))
      (jet (proj J.1.1) e), jetSMul_jet_mem_jets he hx _⟩,
    sheetIndex (coneChart_mem_maximalAtlas he) J • coneChart he J.1.1), by
    show Punctured.toSphere (sheetIndex (coneChart_mem_maximalAtlas he) J • coneChart he J.1.1) =
      Jet.value (jetSMul ((isoGUR n).symm (sheetIndex (coneChart_mem_maximalAtlas he) J))
        (jet (proj J.1.1) e))
    conv_lhs => rw [← (isoGUR n).apply_symm_apply (sheetIndex (coneChart_mem_maximalAtlas he) J)]
    rw [toSphere_isoGUR_smul, coneChart_apply, toSphere_coneFun he hx, value_jetSMul,
      Jet.value_jet]⟩

/-- `fjOfJetAt` is a right inverse of `fjJet`. -/
theorem fjJet_fjOfJetAt (he : e ∈ (projGroupoid n).maximalAtlas B)
    (J : jets (GUR (n + 1)) (RnO (n + 1)) (FCone n B)) (hx : proj J.1.1 ∈ e.source) :
    fjJet (fjOfJetAt he J hx) = J.1 := by
  have hc := coneChart_mem_maximalAtlas he
  set h := sheetIndex hc J
  set g := (isoGUR n).symm h
  have hgh : isoGUR n g = h := (isoGUR n).apply_symm_apply h
  set p := fjOfJetAt he J hx
  have hp : p.src ∈ e.source := hx
  have hs : sheetIndex he p.1.1 = g := sheetIndex_jetSMul_jet he hx g _
  have hq : q p = J.1.1 := by
    have h1 : coneChart he (q p) = coneChart he J.1.1 := by
      rw [coneChart_apply, q_eq_mk]
      rw [show coneFun he (mk p.jet p.mem_jets p.pt p.toSphere_pt) = (isoGUR n g)⁻¹ • p.pt from
        coneFun_mk_jetSMul he hx g _ _, hgh]
      exact inv_smul_smul h _
    exact (coneChart he).injOn (show q p ∈ (coneChart he).source from hp) hx h1
  rw [fjJet_eq he hp, hs, hgh, hq]
  exact (val_eq_jetSMul_sheetIndex hc (j := J) hx).symm

/-- **The inverse of `fjJet`**: a jet `J = h ∘ jet_x f_e` of `J₁(F(B))` (`f_e` the cone chart over
the preferred chart `e` of `B` at `π(x)`) comes from `(i⁻¹(h) ∘ jet_{π(x)} e, h f_e(x))`. -/
def fjOfJet (J : jets (GUR (n + 1)) (RnO (n + 1)) (FCone n B)) : FJ n B :=
  fjOfJetAt (chartAt_mem J.1.1) J (mem_chart_source (S n) (proj J.1.1))

/-- `fjOfJet` is a right inverse of `fjJet`. -/
theorem fjJet_fjOfJet (J : jets (GUR (n + 1)) (RnO (n + 1)) (FCone n B)) :
    fjJet (fjOfJet J) = J.1 :=
  fjJet_fjOfJetAt _ J _

/-- `fjOfJet` does not depend on the chart of `B`. -/
theorem fjOfJet_eq (he : e ∈ (projGroupoid n).maximalAtlas B)
    (J : jets (GUR (n + 1)) (RnO (n + 1)) (FCone n B)) (hx : proj J.1.1 ∈ e.source) :
    fjOfJet J = fjOfJetAt he J hx :=
  fjJet_injective (by rw [fjJet_fjOfJet, fjJet_fjOfJetAt])

/-- `fjJet` is onto `J₁(F(B))`. -/
theorem fjJet_surjective (J : Jet (FCone n B) (RnO (n + 1)))
    (hJ : J ∈ jets (GUR (n + 1)) (RnO (n + 1)) (FCone n B)) : ∃ p : FJ n B, fjJet p = J :=
  ⟨fjOfJet ⟨J, hJ⟩, fjJet_fjOfJet _⟩

/-- `fjJet` is continuous for the étalé topology on the jets of `F(B)` (on a neighbourhood of
`(j, m)` it is `p' ↦ jet_{q(p')} (i(g) • f_e)`, the sheet `g` being locally constant). -/
theorem continuous_fjJet : Continuous (fjJet : FJ n B → Jet (FCone n B) (RnO (n + 1))) := by
  refine continuous_iff_continuousAt.2 fun p => ?_
  have he := chartAt_mem (q p)
  have hp : p.src ∈ (chartAt (S n) (proj (q p))).source := mem_chart_source (S n) _
  have hs := sheetIndex_eventually_eq he (j := p.1.1) hp
  refine ((continuous_jet fun z => isoGUR n (sheetIndex he p.1.1) • coneChart he z).comp
    continuous_q).continuousAt.congr ?_
  filter_upwards [FJ.continuous_jetSub.continuousAt.eventually hs] with p' hp'
  rw [fjJet_eq he hp'.1, hp'.2, jetSMul_jet]
  rfl

omit [HasGroupoid B (projGroupoid n)] in
/-- The topology of `FJ(B)` is induced by `(j, m) ↦ (j, m) ∈ Jet B (S n) × RnO (n + 1)`. -/
theorem isInducing_jet_pt :
    Topology.IsInducing fun p : FJ n B => (p.jet, p.pt) :=
  (Topology.IsInducing.prodMap Topology.IsInducing.subtypeVal Topology.IsInducing.id).comp
    Topology.IsInducing.subtypeVal

/-- `fjOfJet` is continuous (on a neighbourhood of `J₀` it is `J ↦ (i⁻¹(h) ∘ jet_{π(x)} e, h f_e(x))`,
`x` the source of `J`, the sheet `h` being locally constant). -/
theorem continuous_fjOfJet : Continuous (fjOfJet : jets (GUR (n + 1)) (RnO (n + 1)) (FCone n B) →
    FJ n B) := by
  refine continuous_iff_continuousAt.2 fun J₀ => ?_
  have he := chartAt_mem J₀.1.1
  have hc := coneChart_mem_maximalAtlas he
  have hx₀ : J₀.1.1 ∈ (coneChart he).source := mem_chart_source (S n) (proj J₀.1.1)
  have hs := sheetIndex_eventually_eq hc (j := J₀) hx₀
  have hsrc : Continuous fun J : jets (GUR (n + 1)) (RnO (n + 1)) (FCone n B) => J.1.1 :=
    continuous_jetSource.comp continuous_subtype_val
  rw [isInducing_jet_pt.continuousAt_iff]
  refine ContinuousAt.congr (f := fun J : jets (GUR (n + 1)) (RnO (n + 1)) (FCone n B) =>
      (jet (proj J.1.1) fun z => (isoGUR n).symm (sheetIndex hc J₀) • chartAt (S n) (proj J₀.1.1) z,
        sheetIndex hc J₀ • coneChart he J.1.1)) ?_ ?_
  · refine ContinuousAt.prodMk ?_ ?_
    · exact ((continuous_jet _).comp (continuous_proj.comp hsrc)).continuousAt
    · exact (continuous_const_smul _).continuousAt.comp
        (ContinuousAt.comp (g := coneChart he)
          (f := fun J : jets (GUR (n + 1)) (RnO (n + 1)) (FCone n B) => J.1.1)
          ((coneChart he).continuousAt hx₀) hsrc.continuousAt)
  · filter_upwards [hs] with J hJ
    rw [Function.comp_apply, fjOfJet_eq he J hJ.1]
    simp only [fjOfJetAt, FJ.jet, FJ.pt, hJ.2, jetSMul_jet]

variable (n B) in
/-- **« $FJ(B)$ s'identifiera avec $J_1(F(B))$ »** (§ 2, p. 241, l.568) **/ « $FJ(B)$ s'identifie
donc avec l'espace des jets de cartes compatibles de $F(B)$ »** (l.604): `FJ(B)` with the topology
induced by `J(B) × ℝⁿ⁺¹` is homeomorphic to `J₁(F(B))`, the jets of the affine conical structure of
`F(B)` (`jets` for `coneGroupoid`, the étalé topology), by `(j, m) ↦` the jet at `[(j, m)]` of the
compatible chart through `(j, m)` (`fjJet`). It lies over `q` (`fjJet_fst`), has value `m`
(`value_fjJet`), carries ℛ's `g • (j, m)` to `i(g) ∘ ·` (`fjJet_smul`), and is natural in `B`
(`jetCompEq_fjJet_pushFJ`). -/
def fjJetHomeomorph : FJ n B ≃ₜ jets (GUR (n + 1)) (RnO (n + 1)) (FCone n B) where
  toFun p := ⟨fjJet p, fjJet_mem p⟩
  invFun := fjOfJet
  left_inv p := fjJet_injective (fjJet_fjOfJet ⟨fjJet p, fjJet_mem p⟩)
  right_inv J := Subtype.ext (fjJet_fjOfJet J)
  continuous_toFun := continuous_induced_rng.2 continuous_fjJet
  continuous_invFun := continuous_fjOfJet


section Natural

variable {B₁ : Type u} [TopologicalSpace B₁] [ChartedSpace (S n) B₁]
  [HasGroupoid B₁ (projGroupoid n)] {B₂ : Type v} [TopologicalSpace B₂] [ChartedSpace (S n) B₂]
  [HasGroupoid B₂ (projGroupoid n)] {φ : B₁ → B₂}

/-- **Benzécri's `φ'`** (§ 2, p. 242, « Nous poserons $\varphi'(j_1, m)=(j_2, m)$ »): `FJ(B₁) → FJ(B₂)`,
`(j₁, m) ↦ (j₂, m)`, `j₂` the unique jet of `J(B₂)` with `j₂ ∘ φ = j₁` (`existsUnique_pushJet`). -/
def pushFJ (hφ : IsGXMorphism (GSR n) (S n) φ) (p : FJ n B₁) : FJ n B₂ :=
  ⟨(⟨pushJet hφ p.1.1, pushJet_mem hφ _⟩, p.pt), by rw [value_pushJet]; exact p.toSphere_pt⟩

/-- `F(φ)` is induced by `φ'`: `F(φ)[(j₁, m)] = [φ'(j₁, m)]`. -/
theorem map_q (hφ : IsGXMorphism (GSR n) (S n) φ) (p : FJ n B₁) :
    map hφ (q p) = q (pushFJ hφ p) := rfl

/-- **The identification `FJ(B) ≅ J₁(F(B))` is natural in `B`** (« $J_1(F(B_2))\circ F(\varphi)\subset
J_1(F(B_1))$ », l.635): the jet of `φ'(j₁, m)` composed with `F(φ)` is the jet of `(j₁, m)`, i.e.
`fjJet (φ'(p)) ∘ F(φ) = fjJet p`. -/
theorem jetCompEq_fjJet_pushFJ (hφ : IsGXMorphism (GSR n) (S n) φ) (p : FJ n B₁) :
    JetCompEq (map hφ) (fjJet (pushFJ hφ p)) (fjJet p) := by
  have he₁ : chartAt (S n) p.src ∈ (projGroupoid n).maximalAtlas B₁ :=
    (projGroupoid n).chart_mem_maximalAtlas p.src
  have he₂ : chartAt (S n) (φ p.src) ∈ (projGroupoid n).maximalAtlas B₂ :=
    (projGroupoid n).chart_mem_maximalAtlas (φ p.src)
  have hy : p.src ∈ (chartAt (S n) p.src).source := mem_chart_source (S n) p.src
  have hy₂ : φ p.src ∈ (chartAt (S n) (φ p.src)).source := mem_chart_source (S n) (φ p.src)
  obtain ⟨g, hg⟩ := hφ.exists_smul_eq_of_mem_maximalAtlas he₁ he₂ hy hy₂
  set s₁ := sheetIndex he₁ p.1.1
  have hjf : p.1.1.1 = jetSMul (s₁ * g⁻¹) (jet p.src (chartAt (S n) (φ p.src) ∘ φ)) := by
    refine (val_eq_jetSMul_sheetIndex he₁ (j := p.1.1) hy).trans ?_
    rw [jetSMul_mul, jetSMul_jet g⁻¹]
    congr 1
    show jet p.src (chartAt (S n) p.src) = _
    rw [jet_eq_jet_iff]
    filter_upwards [hg] with z hz
    simp only [Function.comp_apply, hz, inv_smul_smul]
  have hpush : pushJet hφ p.1.1 = jetSMul (s₁ * g⁻¹) (jet (φ p.src) (chartAt (S n) (φ p.src))) :=
    pushJet_eq hφ (jet_mem_jets he₂ hy₂) hjf
  have hs₂ : sheetIndex he₂ (pushFJ hφ p).1.1 = s₁ * g⁻¹ :=
    sheetIndex_eq_of_val_eq he₂ hy₂ (by
      show pushJet hφ p.1.1 = _
      rw [hpush, jetSMul_jet])
  have hcone := map_eventually_eq_of_eventually_eq hφ he₁ he₂ (x := q p) hy hy₂ hg
  refine ⟨fun z => isoGUR n (s₁ * g⁻¹) • coneChart he₂ z, ?_, ?_⟩
  · rw [fjJet_eq he₂ (p := pushFJ hφ p) hy₂, hs₂, jetSMul_jet]
    rfl
  · show fjJet p = jet (q p) _
    rw [fjJet_eq he₁ hy, jetSMul_jet, jet_eq_jet_iff]
    filter_upwards [hcone] with x' hx'
    rw [Function.comp_apply, hx'.2, map_mul, map_inv, mul_smul, inv_smul_smul]

end Natural

end FCone

end Benzecri
