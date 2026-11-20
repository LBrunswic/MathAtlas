import Benzecri.Structure.Classes
import Benzecri.Structure.Developing
import Mathlib.Analysis.Convex.Between

/-!
# Chapter 2 § 1 — pockets, shells and strict shells (Déf. 1, 1′, 2, 3 and the three remarks)

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 2 § 1 « Coques et poches », journal pp. 246–248; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch2.tex`. Target T-bz-c2-poches (DEC-137).

* **`bzdef:c2s1d1_poche_affine`** — `benzecri1960_ch2.tex:95` (Déf. 1, l.95–117):
  `Benzecri.IsPocheAff`. Condition b is well posed: the chart `φ̃` exists and two choices agree on
  the segment (`IsAffSegment.forall_chart_iff_exists`).
* **`bzdef:c2s1d1prime_poche_projective`** — `benzecri1960_ch2.tex:119` (Déf. 1′, l.119–145):
  `Benzecri.IsPocheProj` (`H̊` given by its equation `l ≠ 0`; `IsProjSegment.forall_chart_iff_exists`).
* **`bzrem:c2s1r0_poche_affine_vers_projective`** — `benzecri1960_ch2.tex:147` (Remarque, l.147–153):
  `Benzecri.IsPocheAff.toPocheProj`, for every affine isomorphism `j : ℝⁿ ≃ H̊` onto any open
  hemisphere, `V` with its canonical projective structure `Benzecri.projOfAff` (Ch. 1, Déf. 12,
  Remarque), and with the structure built from `j` (`IsPocheAff.toPocheProj_transport`). Key step:
  `eventually_eq_affineEquiv_of_isPreconnected`. For shells: `IsCoqueAff.toCoqueProj`,
  `IsCoqueStricteAff.toCoqueStricteProj`.
* **`bzdef:c2s1d2_coque`** — `benzecri1960_ch2.tex:188` (Déf. 2, l.188–191): `Benzecri.IsCoqueAff`,
  `Benzecri.IsCoqueProj` (`φ(P)` a convex part of `S(n)`, Déf. 8), equivalently convex in the
  affine space `H̊` (`isCoqueProj_iff_isAffConvex`, from `Sphere.isConvexPart_iff_isAffConvex`).
* **`bzdef:c2s1d3_coque_stricte`** — `benzecri1960_ch2.tex:193` (Déf. 3, l.193–198):
  `Benzecri.IsCoqueStricteAff`, `Benzecri.IsCoqueStricteProj` (no line, `Benzecri.ContainsAffLine`).
* **`bzrem:c2s1r1_droite_hemisphere`** — `benzecri1960_ch2.tex:200` (Remarque 1, l.200–204):
  `Benzecri.isAffLine_hemi_iff` (a part of `H̊` is a line of `H̊` iff it is a half-line of `S(n)`),
  and `Benzecri.IsAffLine.exists_halfLine_hemi` (the portion of a line `D` between `s(v)`, `-s(v)`).
* **`bzrem:c2s1r2_coque_stricte_corps_convexe`** — `benzecri1960_ch2.tex:206` (Remarque 2,
  l.206–209): `Benzecri.IsCoqueProj.isCoqueStricte_iff`.

Also the two unlabelled examples (l.155–179): `exemple_poche_affine`, `exemple_poche_projective`
(with `p` injective on `P`, see SCOPE); non-vacuity: `isPocheAff_model`, `exists_isPocheProj_model`,
and strict shells with a non-constant cote, `exists_isCoqueStricteAff_demiDroite` (`]0, 1[ ⊂ ]0, ∞[`)
and its projective image `exists_isCoqueStricteProj_demiDroite`.

> **Déf. 1 (cas affin).** Soit $V$ une variété localement affine de dimension $n$ : on définit une
> *poche* de $V$ par la donnée : — d'un ouvert connexe $P$ de $V$; — d'une carte $\varphi$ de $P$
> dans $\R^n$ compatible avec la structure affine de $P$; — d'une fonction linéaire $z$ sur $\R^n$
> appelée cote. Le triple $(P, \varphi, z)$ doit satisfaire aux deux conditions suivantes :
> *a*. Sur l'image $\varphi(P)$ la cote $z$ a pour borne inférieure $0$ et est majorée par $1$;
> *b*. Soit $(M, N)$ un segment de $V$ dont l'extrémité $M$ appartienne à $P$. Soit
> $\tilde{\varphi}$ une carte compatible d'un voisinage de $(M, N)$ dans $\R^n$ ayant en $M$ même
> germe que $\varphi$. Alors, si $z(\tilde{\varphi}(N))$ est inférieur à $1$, $N$ appartient à $P$.
>
> **Déf. 1′ (cas projectif).** […] — d'un hémisphère ouvert $\mathring{H}$ de $S(n)$; — d'une carte
> $\varphi$ de $P$ dans $S(n)$ compatible avec la structure projective, et telle que
> $\varphi(P)\subset\mathring{H}$; — d'une fonction linéaire $z$, appelée cote, sur
> $\mathring{H}$ considéré comme espace affin. […] *b*. […] Alors,
> $\tilde{\varphi}(M, N)\subset\mathring{H}$ et, si $z(\tilde{\varphi}(N))$ est inférieur à $1$,
> $N$ appartient à $P$.
>
> **Remarque.** Soient $V$ une variété localement affine de dimension $n$, $(P, \varphi, z)$ une
> poche de $V$, $j$ un isomorphisme compatible avec la structure affine de $\R^n$ sur un hémisphère
> ouvert $\mathring{H}$ de $S(n)$ : le système $(P, \mathring{H}, j\circ\varphi, z\circ j^{-1})$
> définit une poche de $V$ considérée comme variété localement projective.
>
> **Déf. 2.** Une poche $(P, \mathring{H}, \varphi, z)$ [resp. $(P, \varphi, z)$] est appelée
> *coque* si $\varphi(P)$ est un convexe.
>
> **Déf. 3.** Une coque […] est appelée une *coque stricte* si le convexe $\varphi(P)$ de $\R^n$
> [resp. si $\varphi(P)$ considéré comme convexe de l'espace affin $\mathring{H}$] ne contient
> pas de droite.
>
> **Remarque 1.** Il importe de distinguer entre droite de $\mathring{H}$, espace affin, et droite
> de $S(n)$ : une droite de $\mathring{H}$ est une demi-droite de $S(n)$, ou portion de droite
> comprise entre deux points diamétralement opposés.
>
> **Remarque 2.** Dire que la coque $(P, \mathring{H}, \varphi, z)$ est une coque stricte équivaut
> à dire que $\overline{\varphi(P)}$ est un corps convexe de $S(n)$.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `V` a « variété » localement affine (resp. projective) of dimension `n` (plan F6) | ⚠ weakened: any `ChartedSpace` over `ℝⁿ` (resp. `S(n)`); connected, Hausdorff, countable never used; `HasGroupoid` only where the proofs use it |
| « un ouvert connexe $P$ » | ✓ carried: `IsOpen P`, `IsConnected P` (nonempty; forced anyway by *a*) |
| « une carte $\varphi$ de $P$ … compatible » | ✓ carried: `OpenPartialHomeomorph` with `source = P`, `IsCompatibleChart` (Ch. 1, Déf. 13) |
| « un hémisphère ouvert $\mathring{H}$ » | ✓ carried as its equation `l`, `[Fact (l ≠ 0)]` (Déf. 5, DEC-114; `H̊ ≠ ∅` is forced by `φ(P) ⊆ H̊`) |
| « fonction linéaire $z$ » on `ℝⁿ`, on `H̊` | reading: an affine function (`→ᵃ[ℝ] ℝ`), Ch. 1 Déf. 2, Exemple (« fonction linéaire sur $A$ ») |
| *a*: « borne inférieure $0$ », « majorée par $1$ » | ✓ carried: `IsGLB (z '' φ(P)) 0`, `z ≤ 1` on `φ(P)` |
| *b*: « $(M, N)$ un segment de $V$ » | ✓ carried: `IsAffSegment` / `IsProjSegment` (Ch. 1, Déf. 14) |
| *b*: « $\tilde\varphi$ une carte compatible d'un voisinage de $(M, N)$ … même germe » | ✓ carried, for EVERY such `φ̃` (equivalent to SOME: `forall_chart_iff_exists`) |
| Remarque: « $j$ un isomorphisme compatible avec la structure affine … sur $\mathring{H}$ » | ✓ carried: `j : ℝⁿ ≃ᵃ[ℝ] H̊`, any open hemisphere |
| Remarque: « $V$ considérée comme variété localement projective » | ✓ carried: the canonical structure `projOfAff` (independent of the chart `j₀`, Ch. 1) |
| Déf. 2 (projective): « $\varphi(P)$ est un convexe » | ✓ carried: convex part of `S(n)` (Déf. 8, DEC-120), proved the same as convex in `H̊` |
| Remarque 2: `V` locally projective | ⚠ weakened: no `HasGroupoid` needed |

## SCOPE (disclosed)

* **« carte » is injective: the paper's own convention, not an open reading** (it is load-bearing:
  Déf. 1/1′ use « carte » in their data). A « carte » is an `OpenPartialHomeomorph`, as in Ch. 1's
  marked Déf. 13 and 14. Benzécri refuses the name to a local homeomorphism with all its jets in
  `J(V)` until it is shown to be a global homeomorphism (« L'application définie en $a$ … est une
  carte compatible. $\tilde{\varphi}$ est un homéomorphisme local : il faut montrer que
  $\tilde{\varphi}$ est un homéomorphisme global », l.559–562, p. 254); § 3, Prop. 2 concludes
  « $p$ est une carte de $V$ » for a projection already compatible with the structure (l.723); Ch. 1,
  Prop. 2 calls the developing map « une application », not a carte; and the proof of § 3, Théorème
  uses the injectivity (l.552, l.572–573).
* **Content-neutral readings** (REPORT, questions): « fonction linéaire » is an affine function —
  the paper's own term (Ch. 1, Déf. 2, Exemple; « forme linéaire sur $\mathring{H}$ muni de sa
  structure affine », l.172), and a translation of the chart turns an affine cote into a homogeneous
  one; `H̊` is carried by its equation `l` (unique up to `ℝ⁺`; the affine structure is independent of
  it, Ch. 1, Déf. 6, and the pocket conditions read only the values of `z` on `H̊`). Constant cotes are
  allowed (the paper does not exclude them): `(ℝⁿ, id, 0)` is a pocket (`isPocheAff_model`).
* **`[sic]`, not a finding**: « (Le système $P, \mathring{H}, \varphi, z)$ » (l.134, flagged at l.135) is read
  « Le système $(P, \mathring{H}, \varphi, z)$ ».
* **The examples (l.155–179, unlabelled)** are formalized with `p` injective on `P`
  (`exemple_poche_affine`, `exemple_poche_projective`); `p` a developing map (`IsDeveloping`, Ch. 1,
  Prop. 2) is the « projection » of an « ouvert étalé ». Without injectivity `(P, p, z)` is not a
  pocket in the chart reading: `W = ℝ × ]1/10, 1/2[`, `p(θ, r) = (1/2 + r cos θ, r sin θ)` (the
  universal cover of an annulus), `z = x`: `P = W`, `inf z(p(P)) = 0`, `p` not injective (described,
  not formalized; REPORT, findings).
* Remarque 2 is proved for any shell; Remarque 1 for any real vector space `E` (`S(E)`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Filter Topology
open scoped Pointwise

namespace Benzecri

universe u v w

/-! ### Lines of a real affine space -/

section AffLine

variable (W : Type*) {Pt : Type*} [AddCommGroup W] [Module ℝ W] [AddTorsor W Pt]

/-- A *line* (« droite ») of a real affine space `Pt` with translations `W`: a set
`{p + t w | t ∈ ℝ}` with `w ≠ 0`. -/
def IsAffLine (A : Set Pt) : Prop :=
  ∃ (p : Pt) (w : W), w ≠ 0 ∧ A = range fun t : ℝ => t • w +ᵥ p

/-- A part `C` of a real affine space *contains a line*. -/
def ContainsAffLine (C : Set Pt) : Prop :=
  ∃ A : Set Pt, IsAffLine W A ∧ A ⊆ C

/-- A part `C` of a real affine space is *convex*: it contains the affine segment
`{x + t (y - x) | 0 ≤ t ≤ 1}` of any two of its points (Mathlib's `affineSegment`). -/
def IsAffConvex (C : Set Pt) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, affineSegment ℝ x y ⊆ C

/-- On a vector space, `IsAffConvex` is Mathlib's `Convex`. -/
theorem isAffConvex_iff_convex {C : Set W} : IsAffConvex W C ↔ Convex ℝ C := by
  rw [convex_iff_segment_subset]
  simp only [IsAffConvex, affineSegment_eq_segment]

end AffLine

/-! ### Generic facts on compatible charts and segments of a `(G, X)`-manifold -/

section General

variable {M : Type u} [TopologicalSpace M] {X : Type v} [TopologicalSpace X]
  {G : Type w} [Group G] [MulAction G X] [ContinuousConstSMul G X] [ChartedSpace X M]

omit [ContinuousConstSMul G X] [ChartedSpace X M] in
/-- **Rigidity along a preconnected set**: let `ψ` be a chart (an open partial homeomorphism) and
`f'` a map which, near every point of a preconnected `Sg ⊆ ψ.source`, is a translate `g • ψ` of
`ψ`; if `f'` and `ψ` have the same germ at one point of `Sg`, they agree on `Sg`. -/
theorem eqOn_of_eventually_smul [IsRigidAction G X] {ψ : OpenPartialHomeomorph M X} {f' : M → X}
    {Sg : Set M} (hS : IsPreconnected Sg) (hSψ : Sg ⊆ ψ.source)
    (hloc : ∀ y ∈ Sg, ∃ g : G, ∀ᶠ z in 𝓝 y, f' z = g • ψ z) {x : M} (hx : x ∈ Sg)
    (hg : (ψ : M → X) =ᶠ[𝓝 x] f') : EqOn ψ f' Sg := by
  let u : Set M := {y | ∀ᶠ z in 𝓝 y, f' z = ψ z}
  let v : Set M := {y | ∃ g : G, (∃ p : X, g • p ≠ p) ∧ ∀ᶠ z in 𝓝 y, f' z = g • ψ z}
  have hu : IsOpen u := isOpen_setOf_eventually_nhds
  have hv : IsOpen v := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨g, hne, hg⟩
    filter_upwards [hg.eventually_nhds] with y' hy' using ⟨g, hne, hy'⟩
  have hcov : Sg ⊆ u ∪ v := by
    intro y hy
    obtain ⟨g, hg⟩ := hloc y hy
    by_cases hgg : ∀ p : X, g • p = p
    · left
      filter_upwards [hg] with z hz
      rw [hz, hgg]
    · right
      obtain ⟨p, hp⟩ := not_forall.1 hgg
      exact ⟨g, ⟨p, hp⟩, hg⟩
  have hdisj : Sg ∩ (u ∩ v) = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun y ⟨hyS, hyu, g, ⟨p, hp⟩, hg⟩ => hp ?_
    have hev : ∀ᶠ z in 𝓝 y, g • ψ z = ψ z ∧ z ∈ ψ.source := by
      filter_upwards [hyu, hg, ψ.open_source.mem_nhds (hSψ hyS)] with z h1 h2 h3
      exact ⟨by rw [← h2, h1], h3⟩
    obtain ⟨t, ht, hto, hyt⟩ := mem_nhds_iff.1 hev
    have := IsRigidAction.smul_eq_of_eqOn (G := G) (g := g) (h := 1)
      (ψ.isOpen_image_of_subset_source hto fun z hz => (ht hz).2) ⟨ψ y, mem_image_of_mem ψ hyt⟩
      (by rintro _ ⟨z, hz, rfl⟩; simp only [one_smul]; exact (ht hz).1) p
    simpa using this
  rcases isPreconnected_iff_subset_of_disjoint.1 hS u v hu hv hcov hdisj with hU | hV
  · intro y hy
    exact ((hU hy).self_of_nhds).symm
  · have : x ∈ Sg ∩ (u ∩ v) := ⟨hx, hg.symm, hV hx⟩
    rw [hdisj] at this
    exact this.elim

/-- **Two compatible charts with the same germ at a point `x` agree on every preconnected set
containing `x` and contained in both sources** (Prop. 1, 2°, along a connected set). -/
theorem eqOn_of_germ_eq [HasGroupoid M (gxGroupoid G X)] [IsRigidAction G X]
    {ψ ψ' : OpenPartialHomeomorph M X} (hψ : IsCompatibleChart G ψ)
    (hψ' : IsCompatibleChart G ψ') {Sg : Set M} (hS : IsPreconnected Sg) (hSψ : Sg ⊆ ψ.source)
    (hSψ' : Sg ⊆ ψ'.source) {x : M} (hx : x ∈ Sg) (hg : (ψ : M → X) =ᶠ[𝓝 x] ψ') :
    EqOn ψ ψ' Sg :=
  eqOn_of_eventually_smul (G := G) hS hSψ (fun _ hy => eventually_smul_eq_of_mem_maximalAtlas
    (isCompatibleChart_iff.1 hψ) (isCompatibleChart_iff.1 hψ') (hSψ hy) (hSψ' hy)) hx hg

/-- **A compatible chart and a developing map** (a map all of whose jets are in `J(V)`, Ch. 1,
Prop. 2) with the same germ at a point `x` agree on every preconnected set containing `x` and
contained in the source of the chart. -/
theorem eqOn_of_germ_eq_isDeveloping [HasGroupoid M (gxGroupoid G X)] [IsRigidAction G X]
    {ψ : OpenPartialHomeomorph M X} (hψ : IsCompatibleChart G ψ) {p : M → X}
    (hp : IsDeveloping G p) {Sg : Set M} (hS : IsPreconnected Sg) (hSψ : Sg ⊆ ψ.source) {x : M}
    (hx : x ∈ Sg) (hg : (ψ : M → X) =ᶠ[𝓝 x] p) : EqOn ψ p Sg := by
  refine eqOn_of_eventually_smul (G := G) hS hSψ (fun y hy => ?_) hx hg
  obtain ⟨g, hg⟩ := (isJetStructure_jets (G := G) (X := X) (M := M)).transitive y _ _
    (hψ y (hSψ hy)) (hp y)
  refine ⟨g, ?_⟩
  rw [Germ.map_coe] at hg
  exact Germ.coe_eq.1 hg

/-- Given a compatible chart `φ` at `x` and any compatible chart `φ₀` at `x`, there is a
compatible chart with the source of `φ₀` and the germ of `φ` at `x` (namely `g ∘ φ₀`). -/
theorem exists_compatibleChart_germ [HasGroupoid M (gxGroupoid G X)]
    {φ φ₀ : OpenPartialHomeomorph M X} (hφ : IsCompatibleChart G φ)
    (hφ₀ : IsCompatibleChart G φ₀) {x : M} (hx : x ∈ φ.source) (hx₀ : x ∈ φ₀.source) :
    ∃ ψ : OpenPartialHomeomorph M X, IsCompatibleChart G ψ ∧ ψ.source = φ₀.source ∧
      (ψ : M → X) =ᶠ[𝓝 x] φ := by
  obtain ⟨g, hg⟩ := eventually_smul_eq_of_mem_maximalAtlas (isCompatibleChart_iff.1 hφ₀)
    (isCompatibleChart_iff.1 hφ) hx₀ hx
  refine ⟨φ₀.transHomeomorph (Homeomorph.smul g), hφ₀.transHomeomorph_smul g, rfl, ?_⟩
  filter_upwards [hg] with z hz
  rw [hz]
  rfl

/-- **A segment of a manifold is preconnected** (when the model's segments are). -/
theorem IsGXSegment.isPreconnected {adm : X → X → Prop} {seg : X → X → Set X}
    (hseg : ∀ a b, adm a b → IsPreconnected (seg a b)) {Sg : Set M} {P Q : M}
    (h : IsGXSegment G adm seg Sg P Q) : IsPreconnected Sg := by
  obtain ⟨φ, -, hS, -, -, hadm, himg⟩ := h
  have : Sg = φ.symm '' (φ '' Sg) := (φ.toPartialEquiv.symm_image_image_of_subset_source hS).symm
  rw [this, himg]
  refine (hseg _ _ hadm).image _ (φ.continuousOn_symm.mono ?_)
  rw [← himg]
  exact (φ.mapsTo.mono_left hS).image_subset

/-- **A segment is a segment in every compatible chart around it**: if `Sg` is a segment of `M`
with endpoints `P`, `Q` (Déf. 14, defined through SOME compatible chart), and the model's segments
are preconnected, contain their endpoints and are carried to segments by `G`, then every compatible
chart `ψ` defined on a neighbourhood of `Sg` maps `Sg` onto the segment `seg (ψ P) (ψ Q)`. -/
theorem IsGXSegment.image_eq [HasGroupoid M (gxGroupoid G X)] [IsRigidAction G X]
    {adm : X → X → Prop} {seg : X → X → Set X}
    (hseg : ∀ a b, adm a b → IsPreconnected (seg a b))
    (hmem : ∀ a b, adm a b → a ∈ seg a b ∧ b ∈ seg a b)
    (hadm : ∀ (g : G) a b, adm a b → adm (g • a) (g • b))
    (hsmul : ∀ (g : G) a b, adm a b → (g • ·) '' seg a b = seg (g • a) (g • b))
    {Sg : Set M} {P Q : M} (h : IsGXSegment G adm seg Sg P Q) {ψ : OpenPartialHomeomorph M X}
    (hψ : IsCompatibleChart G ψ) (hSψ : Sg ⊆ ψ.source) :
    adm (ψ P) (ψ Q) ∧ ψ '' Sg = seg (ψ P) (ψ Q) := by
  have hpre := h.isPreconnected hseg
  have hP : P ∈ Sg := h.left_mem fun a b hab => (hmem a b hab).1
  have hQ : Q ∈ Sg := h.right_mem fun a b hab => (hmem a b hab).2
  obtain ⟨φ₀, hφ₀, hS₀, hP₀, -, hadm₀, himg₀⟩ := h
  rw [isCompatibleChart_iff] at hφ₀ hψ
  obtain ⟨g, hg⟩ := exists_smul_eq_on_connectedComponentIn
    ((gxGroupoid G X).compatible_of_mem_maximalAtlas hφ₀ hψ) (x := P) ⟨hP₀, hSψ hP⟩
  have hsub : Sg ⊆ connectedComponentIn (φ₀.source ∩ ψ.source) P :=
    hpre.subset_connectedComponentIn hP (subset_inter hS₀ hSψ)
  have hψP : ψ P = g • φ₀ P := hg P (hsub hP)
  have hψQ : ψ Q = g • φ₀ Q := hg Q (hsub hQ)
  refine ⟨hψP ▸ hψQ ▸ hadm g _ _ hadm₀, ?_⟩
  rw [hψP, hψQ, ← hsmul g _ _ hadm₀, ← himg₀, image_image]
  exact image_congr fun y hy => hg y (hsub hy)

/-- **The condition `b` of Déf. 1 and 1′ does not depend on the chart `φ̃`**: for a segment
`(P, Q)` of `M` and a compatible chart `φ` at `P`, a compatible chart `φ̃` of a neighbourhood of the
segment with the germ of `φ` at `P` EXISTS (Prop. 1, 2°), and any two such agree on the segment;
so « for every such `φ̃` » and « for some such `φ̃` » are the same condition, whatever is asked of
`φ̃(P, Q)` and `φ̃(Q)` (the predicate `R`). -/
theorem IsGXSegment.forall_chart_iff_exists [HasGroupoid M (gxGroupoid G X)] [IsRigidAction G X]
    {adm : X → X → Prop} {seg : X → X → Set X}
    (hseg : ∀ a b, adm a b → IsPreconnected (seg a b))
    (hmem : ∀ a b, adm a b → a ∈ seg a b ∧ b ∈ seg a b)
    {Sg : Set M} {P Q : M} (h : IsGXSegment G adm seg Sg P Q) {φ : OpenPartialHomeomorph M X}
    (hφ : IsCompatibleChart G φ) (hP : P ∈ φ.source) (R : Set X → X → Prop) :
    (∀ ψ : OpenPartialHomeomorph M X, IsCompatibleChart G ψ → Sg ⊆ ψ.source →
        (ψ : M → X) =ᶠ[𝓝 P] φ → R (ψ '' Sg) (ψ Q)) ↔
      ∃ ψ : OpenPartialHomeomorph M X, IsCompatibleChart G ψ ∧ Sg ⊆ ψ.source ∧
        (ψ : M → X) =ᶠ[𝓝 P] φ ∧ R (ψ '' Sg) (ψ Q) := by
  have hpre := h.isPreconnected hseg
  have hPS : P ∈ Sg := h.left_mem fun a b hab => (hmem a b hab).1
  have hQS : Q ∈ Sg := h.right_mem fun a b hab => (hmem a b hab).2
  obtain ⟨φ₀, hφ₀, hS₀, hP₀, -⟩ := h
  constructor
  · intro H
    obtain ⟨ψ, hψ, hsrc, hgerm⟩ := exists_compatibleChart_germ hφ hφ₀ hP hP₀
    have hSψ : Sg ⊆ ψ.source := hsrc ▸ hS₀
    exact ⟨ψ, hψ, hSψ, hgerm, H ψ hψ hSψ hgerm⟩
  · rintro ⟨ψ₁, hψ₁, hSψ₁, hgerm₁, hR⟩ ψ hψ hSψ hgerm
    have heq : EqOn ψ ψ₁ Sg := eqOn_of_germ_eq hψ hψ₁ hpre hSψ hSψ₁ hPS (hgerm.trans hgerm₁.symm)
    rw [image_congr heq, heq hQS]
    exact hR

end General

/-! ### The action of `GS(E)` on segments of `S(E)` -/

section SphereSegments

namespace Sphere

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Equal representatives give the same point (a cast helper). -/
theorem mk_eq_mk_of_eq' {v w : E} {hv : v ≠ 0} {hw : w ≠ 0} (h : v = w) : mk v hv = mk w hw := by
  subst h; rfl

/-- `GS(E)` commutes with the antipodal map. -/
theorem GSE.smul_neg (g : GSE E) (x : Sphere E) : g • (-x) = -(g • x) := by
  induction g using QuotientGroup.induction_on with
  | H g =>
    induction x using ind with
    | h v hv =>
      rw [GSE.mk_smul, GSE.mk_smul, neg_mk, smul_mk, smul_mk, neg_mk]
      exact mk_eq_mk_of_eq' (map_neg g v)

/-- A linear automorphism carries the rays of `C` to the rays of `g(C)`. -/
theorem image_smul_ofCone (g : E ≃ₗ[ℝ] E) (C : Set E) :
    (g • ·) '' ofCone C = ofCone (g '' C) := by
  ext x
  constructor
  · rintro ⟨_, hy, rfl⟩
    obtain ⟨v, hv, hvC, rfl⟩ := mem_ofCone.1 hy
    show g • mk v hv ∈ _
    rw [smul_mk]
    exact mk_mem_ofCone _ (mem_image_of_mem g hvC)
  · intro hx
    obtain ⟨_, hw, ⟨v, hvC, rfl⟩, rfl⟩ := mem_ofCone.1 hx
    have hv : v ≠ 0 := fun h => hw (by rw [h, map_zero])
    exact ⟨mk v hv, mk_mem_ofCone hv hvC, by show g • mk v hv = _; rw [smul_mk]⟩

/-- **`GS(E)` carries segments to segments** (Déf. 7): `g · (m, m') = (g m, g m')`. -/
theorem GSE.image_smul_closedSeg (g : GSE E) (a b : Sphere E) :
    (g • ·) '' closedSeg a b = closedSeg (g • a) (g • b) := by
  induction g using QuotientGroup.induction_on with
  | H g =>
    induction a using ind with
    | h M hM =>
      induction b using ind with
      | h M' hM' =>
        simp only [GSE.mk_smul]
        rw [smul_mk, smul_mk, closedSeg_mk, closedSeg_mk, segOf, segOf, image_smul_ofCone]
        congr 1
        exact image_segment ℝ (g : E →ₗ[ℝ] E).toAffineMap M M'

/-- **A segment of `S(E)` between non-antipodal points is preconnected** (the image of the segment
`[M, M']` of `E`, which avoids `O`). -/
theorem isPreconnected_closedSeg [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]
    {a b : Sphere E} (hab : b ≠ -a) : IsPreconnected (closedSeg a b) := by
  induction a using ind with
  | h M hM =>
    induction b using ind with
    | h M' hM' =>
      rw [closedSeg_mk]
      have h0 : ∀ x : segment ℝ M M', (x : E) ≠ 0 := fun x hx =>
        zero_notMem_segment hM hM' hab (hx ▸ x.2)
      haveI : PreconnectedSpace (segment ℝ M M') :=
        isPreconnected_iff_preconnectedSpace.1 (convex_segment M M').isPreconnected
      have hrange : segOf M M' = range fun x : segment ℝ M M' => mk (x : E) (h0 x) := by
        ext y
        constructor
        · intro hy
          obtain ⟨v, hv, hvC, rfl⟩ := mem_ofCone.1 hy
          exact ⟨⟨v, hvC⟩, rfl⟩
        · rintro ⟨x, rfl⟩
          exact mk_mem_ofCone _ x.2
      rw [hrange]
      exact isPreconnected_range (continuous_mk_comp continuous_subtype_val h0)

end Sphere

end SphereSegments

/-! ### Segments and lines of an open hemisphere (Déf. 6's affine structure) -/

section Hemisphere

namespace Sphere

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {l : Module.Dual ℝ E}

/-- Two points of an open hemisphere are never diametrically opposite. -/
theorem ne_neg_of_mem_openHemisphere {x y : Sphere E} (hx : x ∈ openHemisphere l)
    (hy : y ∈ openHemisphere l) : y ≠ -x := by
  rintro rfl
  induction x using ind with
  | h v hv =>
    rw [neg_mk, mk_mem_openHemisphere, map_neg] at hy
    rw [mk_mem_openHemisphere] at hx
    linarith

variable [Fact (l ≠ 0)]

/-- The normalised representative of a point of the affine segment `[m, m']` of `H̊`:
`(m + t(m' - m))/l = M + t (M' - M)`, `M = m/l(m)`, `M' = m'/l(m')`. -/
theorem nrep_lineMap (m m' : openHemisphere l) (t : ℝ) :
    nrep l (AffineMap.lineMap m m' t : openHemisphere l) =
      nrep l m + t • (nrep l m' - nrep l m) := by
  rw [AffineMap.lineMap_apply, nrep_vadd, transl]
  congr 1
  rw [LinearMap.smul_apply, Submodule.coe_smul, vsub_apply_hq, l_nrep m.2, one_smul]

/-- **The affine segments of `H̊` are the segments of `S(E)`** (Déf. 6 against Déf. 7): for
`m, m' ∈ H̊`, the affine segment `[m, m']` of the affine space `H̊` is the segment `(m, m')` of
`S(E)`. -/
theorem coe_image_affineSegment (m m' : openHemisphere l) :
    ((↑) '' affineSegment ℝ m m' : Set (Sphere E)) = closedSeg m m' := by
  have h1 : closedSeg (m : Sphere E) m' = segOf (nrep l m) (nrep l m') := by
    have := closedSeg_mk (nrep_ne_zero m.2) (nrep_ne_zero m'.2)
    rwa [mk_nrep m.2, mk_nrep m'.2] at this
  rw [h1]
  ext x
  constructor
  · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    rw [← mk_nrep (AffineMap.lineMap m m' t : openHemisphere l).2]
    refine mk_mem_ofCone _ ?_
    rw [nrep_lineMap, segment_eq_image_lineMap]
    exact ⟨t, ht, by rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_comm]⟩
  · intro hx
    obtain ⟨v, hv, hvC, rfl⟩ := mem_ofCone.1 hx
    rw [segment_eq_image_lineMap] at hvC
    obtain ⟨t, ht, rfl⟩ := hvC
    refine ⟨AffineMap.lineMap m m' t, ⟨t, ht, rfl⟩, ?_⟩
    rw [← mk_nrep (AffineMap.lineMap m m' t : openHemisphere l).2]
    refine mk_eq_mk_of_eq' ?_
    rw [nrep_lineMap, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_comm]

/-- **Convexity in `S(E)` (Déf. 8) and in the affine space `H̊` (Déf. 6) agree** on the parts of
`H̊`: this is « $\varphi(P)$ considéré comme convexe de l'espace affin $\mathring{H}$ » (Déf. 3). -/
theorem isConvexPart_iff_isAffConvex {k : Set (Sphere E)} (hk : k ⊆ openHemisphere l) :
    IsConvexPart k ↔ IsAffConvex (HemiTrans l) ((↑) ⁻¹' k : Set (openHemisphere l)) := by
  rw [isConvexPart_iff_isSegConvex]
  constructor
  · intro h m hm m' hm' y hy
    have : (y : Sphere E) ∈ (↑) '' affineSegment ℝ m m' := mem_image_of_mem _ hy
    rw [coe_image_affineSegment] at this
    exact h _ hm _ hm' (ne_neg_of_mem_openHemisphere m.2 m'.2) this
  · intro h m hm m' hm' _ y hy
    have hmm : m ∈ openHemisphere l := hk hm
    have hmm' : m' ∈ openHemisphere l := hk hm'
    have h2 := coe_image_affineSegment (⟨m, hmm⟩ : openHemisphere l) ⟨m', hmm'⟩
    dsimp only at h2
    rw [← h2] at hy
    obtain ⟨y', hy', rfl⟩ := hy
    exact h ⟨m, hmm⟩ hm ⟨m', hmm'⟩ hm' hy'

end Sphere

end Hemisphere

/-! ### Segments of locally affine and locally projective manifolds, in any chart -/

section SegmentCharts

variable {n : ℕ} {V : Type u} [TopologicalSpace V]

/-- A segment of a locally affine manifold is preconnected. -/
theorem IsAffSegment.isPreconnected [ChartedSpace (Fin n → ℝ) V] {Sg : Set V} {M N : V}
    (h : IsAffSegment n Sg M N) : IsPreconnected Sg :=
  IsGXSegment.isPreconnected (fun a b _ => (convex_segment a b).isPreconnected) h

/-- A segment of a locally projective manifold is preconnected. -/
theorem IsProjSegment.isPreconnected [ChartedSpace (S n) V] {Sg : Set V} {M N : V}
    (h : IsProjSegment n Sg M N) : IsPreconnected Sg :=
  IsGXSegment.isPreconnected (fun _ _ hab => Sphere.isPreconnected_closedSeg hab) h

/-- **A segment of a locally affine manifold is a segment in every compatible chart around it**:
`ψ(M, N) = [ψ M, ψ N]`. -/
theorem IsAffSegment.image_eq [ChartedSpace (Fin n → ℝ) V] [HasGroupoid V (affGroupoid n)]
    {Sg : Set V} {M N : V} (h : IsAffSegment n Sg M N) {ψ : OpenPartialHomeomorph V (Fin n → ℝ)}
    (hψ : IsCompatibleChart (GAR n) ψ) (hSψ : Sg ⊆ ψ.source) :
    ψ '' Sg = segment ℝ (ψ M) (ψ N) :=
  (IsGXSegment.image_eq (fun a b _ => (convex_segment a b).isPreconnected)
    (fun a b _ => ⟨left_mem_segment ℝ a b, right_mem_segment ℝ a b⟩) (fun _ _ _ _ => trivial)
    (fun g a b _ => image_segment ℝ g.toAffineMap a b) h hψ hSψ).2

/-- **A segment of a locally projective manifold is a segment in every compatible chart around
it**: `ψ(M, N) = (ψ M, ψ N)`, with `ψ M`, `ψ N` not diametrically opposite. -/
theorem IsProjSegment.image_eq [ChartedSpace (S n) V] [HasGroupoid V (projGroupoid n)]
    {Sg : Set V} {M N : V} (h : IsProjSegment n Sg M N) {ψ : OpenPartialHomeomorph V (S n)}
    (hψ : IsCompatibleChart (GSR n) ψ) (hSψ : Sg ⊆ ψ.source) :
    ψ N ≠ -ψ M ∧ ψ '' Sg = Sphere.closedSeg (ψ M) (ψ N) :=
  IsGXSegment.image_eq (fun _ _ hab => Sphere.isPreconnected_closedSeg hab)
    (fun a b _ => ⟨Sphere.left_mem_closedSeg a b, Sphere.right_mem_closedSeg a b⟩)
    (fun g a b hab h' => hab (by
      have := congrArg (g⁻¹ • ·) h'
      simpa [Sphere.GSE.smul_neg] using this))
    (fun g a b _ => Sphere.GSE.image_smul_closedSeg g a b) h hψ hSψ

/-- **Condition `b` of Déf. 1 is well posed**: « every » and « some » compatible chart `φ̃` of a
neighbourhood of the segment with the germ of `φ` at `M` give the same condition. -/
theorem IsAffSegment.forall_chart_iff_exists [ChartedSpace (Fin n → ℝ) V]
    [HasGroupoid V (affGroupoid n)] {Sg : Set V} {M N : V} (h : IsAffSegment n Sg M N)
    {φ : OpenPartialHomeomorph V (Fin n → ℝ)} (hφ : IsCompatibleChart (GAR n) φ)
    (hM : M ∈ φ.source) (R : Set (Fin n → ℝ) → (Fin n → ℝ) → Prop) :
    (∀ ψ : OpenPartialHomeomorph V (Fin n → ℝ), IsCompatibleChart (GAR n) ψ → Sg ⊆ ψ.source →
        (ψ : V → Fin n → ℝ) =ᶠ[𝓝 M] φ → R (ψ '' Sg) (ψ N)) ↔
      ∃ ψ : OpenPartialHomeomorph V (Fin n → ℝ), IsCompatibleChart (GAR n) ψ ∧
        Sg ⊆ ψ.source ∧ (ψ : V → Fin n → ℝ) =ᶠ[𝓝 M] φ ∧ R (ψ '' Sg) (ψ N) :=
  IsGXSegment.forall_chart_iff_exists (fun a b _ => (convex_segment a b).isPreconnected)
    (fun a b _ => ⟨left_mem_segment ℝ a b, right_mem_segment ℝ a b⟩) h hφ hM R

/-- **Condition `b` of Déf. 1′ is well posed** (as `IsAffSegment.forall_chart_iff_exists`). -/
theorem IsProjSegment.forall_chart_iff_exists [ChartedSpace (S n) V]
    [HasGroupoid V (projGroupoid n)] {Sg : Set V} {M N : V} (h : IsProjSegment n Sg M N)
    {φ : OpenPartialHomeomorph V (S n)} (hφ : IsCompatibleChart (GSR n) φ)
    (hM : M ∈ φ.source) (R : Set (S n) → S n → Prop) :
    (∀ ψ : OpenPartialHomeomorph V (S n), IsCompatibleChart (GSR n) ψ → Sg ⊆ ψ.source →
        (ψ : V → S n) =ᶠ[𝓝 M] φ → R (ψ '' Sg) (ψ N)) ↔
      ∃ ψ : OpenPartialHomeomorph V (S n), IsCompatibleChart (GSR n) ψ ∧
        Sg ⊆ ψ.source ∧ (ψ : V → S n) =ᶠ[𝓝 M] φ ∧ R (ψ '' Sg) (ψ N) :=
  IsGXSegment.forall_chart_iff_exists (fun _ _ hab => Sphere.isPreconnected_closedSeg hab)
    (fun a b _ => ⟨Sphere.left_mem_closedSeg a b, Sphere.right_mem_closedSeg a b⟩) h hφ hM R

end SegmentCharts

/-! ### Déf. 1 — pockets of a locally affine manifold -/

section PocheAff

variable {n : ℕ} {V : Type u} [TopologicalSpace V] [ChartedSpace (Fin n → ℝ) V]

/-- **Déf. 1** (`bzdef:c2s1d1_poche_affine`): a *pocket* `(P, φ, z)` of the locally affine
`n`-manifold `V`: `P` a connected open set; `φ` a compatible chart (Ch. 1, Déf. 13) with source `P`;
`z` the « cote », a « fonction linéaire » (affine function, Ch. 1, Déf. 2, Exemple) on `ℝⁿ`;
*a*: on `φ(P)`, `inf z = 0` and `z ≤ 1`; *b*: for every segment `(M, N)` of `V` (Ch. 1, Déf. 14)
with `M ∈ P` and every compatible chart `φ̃` of a neighbourhood of `(M, N)` with the germ of `φ` at
`M`, `z(φ̃ N) < 1` implies `N ∈ P` (« every » = « some »: `IsAffSegment.forall_chart_iff_exists`). -/
structure IsPocheAff (P : Set V) (φ : OpenPartialHomeomorph V (Fin n → ℝ))
    (z : (Fin n → ℝ) →ᵃ[ℝ] ℝ) : Prop where
  isOpen : IsOpen P
  isConnected : IsConnected P
  source_eq : φ.source = P
  compatible : IsCompatibleChart (GAR n) φ
  isGLB : IsGLB (z '' (φ '' P)) 0
  le_one : ∀ x ∈ P, z (φ x) ≤ 1
  mem_of_segment : ∀ (Sg : Set V) (M N : V), IsAffSegment n Sg M N → M ∈ P →
    ∀ ψ : OpenPartialHomeomorph V (Fin n → ℝ), IsCompatibleChart (GAR n) ψ → Sg ⊆ ψ.source →
      (ψ : V → Fin n → ℝ) =ᶠ[𝓝 M] φ → z (ψ N) < 1 → N ∈ P

/-- **Déf. 2, affine case** (`bzdef:c2s1d2_coque`): a pocket is a *shell* if `φ(P)` is convex. -/
def IsCoqueAff (P : Set V) (φ : OpenPartialHomeomorph V (Fin n → ℝ))
    (z : (Fin n → ℝ) →ᵃ[ℝ] ℝ) : Prop :=
  IsPocheAff P φ z ∧ Convex ℝ (φ '' P)

/-- **Déf. 3, affine case** (`bzdef:c2s1d3_coque_stricte`): a shell is *strict* if the convex
`φ(P)` of `ℝⁿ` contains no line. -/
def IsCoqueStricteAff (P : Set V) (φ : OpenPartialHomeomorph V (Fin n → ℝ))
    (z : (Fin n → ℝ) →ᵃ[ℝ] ℝ) : Prop :=
  IsCoqueAff P φ z ∧ ¬ ContainsAffLine (Fin n → ℝ) (φ '' P)

end PocheAff

/-! ### Déf. 1′ — pockets of a locally projective manifold -/

section PocheProj

variable {n : ℕ} {V : Type u} [TopologicalSpace V] [ChartedSpace (S n) V]

/-- **Déf. 1′** (`bzdef:c2s1d1prime_poche_projective`): a *pocket* `(P, H̊, φ, z)` of the locally
projective `n`-manifold `V`, the open hemisphere `H̊ = s(l⁻¹(ℝ⁺))` given by its equation `l ≠ 0`
(Déf. 5): `P` a connected open set; `φ` a compatible chart with source `P` and `φ(P) ⊆ H̊`; `z` a
« fonction linéaire » on the affine space `H̊` (Déf. 6); *a*: on `φ(P)` (read in `H̊`), `inf z = 0`
and `z ≤ 1`; *b*: for every segment `(M, N)` of `V` with `M ∈ P` and every compatible chart `φ̃` of
a neighbourhood of `(M, N)` with the germ of `φ` at `M`, `φ̃(M, N) ⊆ H̊`, and `z(φ̃ N) < 1` implies
`N ∈ P` (« every » = « some »: `IsProjSegment.forall_chart_iff_exists`). -/
structure IsPocheProj (P : Set V) (l : Module.Dual ℝ (Fin (n + 1) → ℝ)) [Fact (l ≠ 0)]
    (φ : OpenPartialHomeomorph V (S n)) (z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ) : Prop where
  isOpen : IsOpen P
  isConnected : IsConnected P
  source_eq : φ.source = P
  compatible : IsCompatibleChart (GSR n) φ
  image_subset : φ '' P ⊆ Sphere.openHemisphere l
  isGLB : IsGLB (z '' ((↑) ⁻¹' (φ '' P))) 0
  le_one : ∀ y : Sphere.openHemisphere l, (y : S n) ∈ φ '' P → z y ≤ 1
  mem_of_segment : ∀ (Sg : Set V) (M N : V), IsProjSegment n Sg M N → M ∈ P →
    ∀ ψ : OpenPartialHomeomorph V (S n), IsCompatibleChart (GSR n) ψ → Sg ⊆ ψ.source →
      (ψ : V → S n) =ᶠ[𝓝 M] φ →
        ψ '' Sg ⊆ Sphere.openHemisphere l ∧
          ∀ hN : ψ N ∈ Sphere.openHemisphere l, z ⟨ψ N, hN⟩ < 1 → N ∈ P

/-- **Déf. 2, projective case** (`bzdef:c2s1d2_coque`): a pocket is a *shell* if `φ(P)` is a
convex part of `S(n)` (Déf. 8). -/
def IsCoqueProj (P : Set V) (l : Module.Dual ℝ (Fin (n + 1) → ℝ)) [Fact (l ≠ 0)]
    (φ : OpenPartialHomeomorph V (S n)) (z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ) : Prop :=
  IsPocheProj P l φ z ∧ Sphere.IsConvexPart (φ '' P)

/-- **Déf. 3, projective case** (`bzdef:c2s1d3_coque_stricte`): a shell is *strict* if `φ(P)`,
as a convex of the affine space `H̊`, contains no line of `H̊`. -/
def IsCoqueStricteProj (P : Set V) (l : Module.Dual ℝ (Fin (n + 1) → ℝ)) [Fact (l ≠ 0)]
    (φ : OpenPartialHomeomorph V (S n)) (z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ) : Prop :=
  IsCoqueProj P l φ z ∧
    ¬ ContainsAffLine (Sphere.HemiTrans l)
      ((↑) ⁻¹' (φ '' P) : Set (Sphere.openHemisphere l))

/-- **Déf. 2 read in the affine space `H̊`**: a projective pocket is a shell iff `φ(P)` is convex
for the affine structure of `H̊` (Déf. 6) — « $\varphi(P)$ considéré comme convexe de l'espace affin
$\mathring{H}$ » of Déf. 3. -/
theorem isCoqueProj_iff_isAffConvex {P : Set V} {l : Module.Dual ℝ (Fin (n + 1) → ℝ)}
    [Fact (l ≠ 0)] {φ : OpenPartialHomeomorph V (S n)} {z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ} :
    IsCoqueProj P l φ z ↔ IsPocheProj P l φ z ∧
      IsAffConvex (Sphere.HemiTrans l) ((↑) ⁻¹' (φ '' P) : Set (Sphere.openHemisphere l)) :=
  ⟨fun h => ⟨h.1, (Sphere.isConvexPart_iff_isAffConvex h.1.image_subset).1 h.2⟩,
    fun h => ⟨h.1, (Sphere.isConvexPart_iff_isAffConvex h.1.image_subset).2 h.2⟩⟩

end PocheProj

/-! ### The Remarque after Déf. 1′ — an affine pocket is a projective pocket -/

section Remarque0

variable {n : ℕ}

/-- An affine isomorphism `j : ℝⁿ ≃ H̊` onto an open hemisphere is an open embedding into `S(n)`. -/
theorem isOpenEmbedding_coe_affineEquiv {l : Module.Dual ℝ (Fin (n + 1) → ℝ)} [Fact (l ≠ 0)]
    (j : (Fin n → ℝ) ≃ᵃ[ℝ] Sphere.openHemisphere l) :
    IsOpenEmbedding fun y => (j y : S n) := by
  obtain ⟨σ, hσ⟩ := Sphere.exists_eq_smul_hemiChart (j := j)
    (isAffine_of_affineMap j.toAffineMap) j.injective
  have hfun : (fun y => (j y : S n)) = (Homeomorph.smul σ) ∘ Sphere.hemiChart n := funext hσ
  rw [hfun]
  exact (Homeomorph.smul σ).isOpenEmbedding.comp Sphere.isOpenEmbedding_hemiChart

variable {V : Type u} [TopologicalSpace V] [ChartedSpace (Fin n → ℝ) V]

variable (n V) in
/-- **The locally projective structure canonically associated with a locally affine one** (Ch. 1,
Déf. 12, Remarque, `bzrem:c1s1r1_affine_vers_projective`): the charts `j₀ ∘ φ`, `j₀ = hemiChart`
the standard affine chart `y ↦ s(y, 1)` of `H₀`. Every other affine injection `j : ℝⁿ → H̊` gives
the same structure (`maximalAtlas_transport_indep`, `remarque_affine_vers_projective`). -/
abbrev projOfAff : ChartedSpace (S n) V :=
  transportChartedSpace (Sphere.isOpenEmbedding_hemiChart (n := n)) V

section Local

attribute [local instance] projOfAff

/-- The canonical projective structure is a locally projective structure. -/
theorem hasGroupoid_projOfAff [HasGroupoid V (affGroupoid n)] :
    HasGroupoid V (projGroupoid n) :=
  hasGroupoid_projGroupoid_of_affine

attribute [local instance] hasGroupoid_projOfAff

/-- **A projective chart of a locally affine manifold is affine on every connected set where it is
affine near one point**: in the canonical projective structure, if a compatible chart `ψ` is
`j ∘ e₀` near a point `x₀` of a preconnected `K ⊆ ψ.source` (`e₀` an affine chart, `j : ℝⁿ ≃ H̊`
affine), then near every point of `K` it is `j ∘ e` for an affine chart `e`. (The open hemisphere
`j(ℝⁿ)` attached to `ψ` is locally constant along `K`.) -/
theorem eventually_eq_affineEquiv_of_isPreconnected [HasGroupoid V (affGroupoid n)]
    {l : Module.Dual ℝ (Fin (n + 1) → ℝ)} [Fact (l ≠ 0)]
    (j : (Fin n → ℝ) ≃ᵃ[ℝ] Sphere.openHemisphere l) {ψ : OpenPartialHomeomorph V (S n)}
    (hψ : IsCompatibleChart (GSR n) ψ) {K : Set V} (hK : IsPreconnected K)
    (hKψ : K ⊆ ψ.source) {x₀ : V} (hx₀ : x₀ ∈ K) {e₀ : OpenPartialHomeomorph V (Fin n → ℝ)}
    (he₀ : IsCompatibleChart (GAR n) e₀) (hx₀e : x₀ ∈ e₀.source)
    (hev : ∀ᶠ y in 𝓝 x₀, ψ y = (j (e₀ y) : S n)) :
    ∀ y ∈ K, ∃ e : OpenPartialHomeomorph V (Fin n → ℝ), IsCompatibleChart (GAR n) e ∧
      y ∈ e.source ∧ ∀ᶠ y' in 𝓝 y, ψ y' = (j (e y') : S n) := by
  obtain ⟨σ, hσ⟩ := Sphere.exists_eq_smul_hemiChart (j := j)
    (isAffine_of_affineMap j.toAffineMap) j.injective
  rw [isCompatibleChart_iff] at hψ
  let W : Set V := {y | ∃ e : OpenPartialHomeomorph V (Fin n → ℝ), IsCompatibleChart (GAR n) e ∧
    y ∈ e.source ∧ ∀ᶠ y' in 𝓝 y, ψ y' = (j (e y') : S n)}
  have hWo : IsOpen W := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨e, he, hy, hev⟩
    filter_upwards [hev.eventually_nhds, e.open_source.mem_nhds hy] with y' h1 h2
    exact ⟨e, he, h2, h1⟩
  refine fun y hy => hK.subset_of_closure_inter_subset hWo ⟨x₀, hx₀, e₀, he₀, hx₀e, hev⟩
    (fun y ⟨hyc, hyK⟩ => ?_) hy
  -- near `y`, `ψ = g • j₀ ∘ c`, `c` the affine chart at `y`
  set c := chartAt (Fin n → ℝ) y with hc
  have hcm : c ∈ (gxGroupoid (GAR n) (Fin n → ℝ)).maximalAtlas V :=
    (gxGroupoid (GAR n) (Fin n → ℝ)).chart_mem_maximalAtlas y
  obtain ⟨g, hg⟩ := eventually_smul_eq_of_mem_maximalAtlas
    ((projGroupoid n).chart_mem_maximalAtlas y) hψ (mem_chart_source (S n) y) (hKψ hyK)
  have hg' : ∀ᶠ z in 𝓝 y, ψ z = g • Sphere.hemiChart n (c z) := by
    filter_upwards [hg] with z hz
    rw [hz, transport_chartAt]
    rfl
  obtain ⟨T, hTsub, hTo, hyT⟩ := mem_nhds_iff.1 (hg'.and (c.open_source.mem_nhds
    (mem_chart_source (Fin n → ℝ) y)))
  obtain ⟨y', hy'T, e', he', hy'e, hev'⟩ := mem_closure_iff.1 hyc T hTo hyT
  -- compare at `y'`: `σ = g * affToGS b`
  obtain ⟨b, hb⟩ := eventually_smul_eq_of_mem_maximalAtlas (isCompatibleChart_iff.1 he') hcm hy'e
    (hTsub hy'T).2
  have hkey : ∀ᶠ z in 𝓝 y', σ • Sphere.hemiChart n (e' z) =
      (g * Sphere.affToGS b) • Sphere.hemiChart n (e' z) := by
    filter_upwards [hev', hb, hTo.mem_nhds hy'T] with z h1 h2 h3
    rw [← hσ, ← h1, (hTsub h3).1, h2, mul_smul, ← Sphere.hemiChart_apply_eq_smul]
    rfl
  obtain ⟨t, ht, hto, hy't⟩ := mem_nhds_iff.1 (hkey.and (e'.open_source.mem_nhds hy'e))
  have hσg : σ = g * Sphere.affToGS b := by
    refine eq_of_eqOn ((Sphere.isOpenMap_hemiChart (n := n)) _
      (e'.isOpen_image_of_subset_source hto fun z hz => (ht hz).2))
      ⟨_, mem_image_of_mem _ (mem_image_of_mem _ hy't)⟩ ?_
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact (ht hz).1
  -- hence near `y`, `ψ = j ∘ (b⁻¹ • c)`
  refine ⟨c.transHomeomorph (Homeomorph.smul b⁻¹),
    (isCompatibleChart_iff.2 hcm).transHomeomorph_smul b⁻¹, mem_chart_source _ y, ?_⟩
  filter_upwards [hg'] with z hz
  rw [hz, hσ, hσg, mul_smul, ← Sphere.hemiChart_apply_eq_smul]
  congr 2
  show c z = b (b⁻¹ (c z))
  exact (congrArg (fun f : GAR n => f (c z)) (mul_inv_cancel b)).symm

/-- **The Remarque after Déf. 1′** (`bzrem:c2s1r0_poche_affine_vers_projective`): if `(P, φ, z)` is
a pocket of the locally affine `V` and `j : ℝⁿ ≃ H̊` an affine isomorphism onto ANY open hemisphere,
then `(P, H̊, j ∘ φ, z ∘ j⁻¹)` is a pocket of `V` with its canonical locally projective structure
(`projOfAff`; for the structure built from `j` itself see `IsPocheAff.toPocheProj_transport`). -/
theorem IsPocheAff.toPocheProj [HasGroupoid V (affGroupoid n)] {P : Set V}
    {φ : OpenPartialHomeomorph V (Fin n → ℝ)} {z : (Fin n → ℝ) →ᵃ[ℝ] ℝ}
    (h : IsPocheAff P φ z) {l : Module.Dual ℝ (Fin (n + 1) → ℝ)} [Fact (l ≠ 0)]
    (j : (Fin n → ℝ) ≃ᵃ[ℝ] Sphere.openHemisphere l) :
    @IsPocheProj n V _ (projOfAff n V) P l _
      (φ.trans ((isOpenEmbedding_coe_affineEquiv j).toOpenPartialHomeomorph _))
      (z.comp j.symm.toAffineMap) := by
  have hι := isOpenEmbedding_coe_affineEquiv j
  set jE := hι.toOpenPartialHomeomorph (fun y => (j y : S n)) with hjE
  have hjE_left : ∀ y, jE.symm (j y : S n) = y := fun y => hι.toOpenPartialHomeomorph_left_inv
  obtain ⟨σ, hσ⟩ := Sphere.exists_eq_smul_hemiChart (j := j)
    (isAffine_of_affineMap j.toAffineMap) j.injective
  have hsrc : (φ.trans jE).source = P := by
    rw [OpenPartialHomeomorph.trans_source, hjE, IsOpenEmbedding.toOpenPartialHomeomorph_source,
      preimage_univ, inter_univ, h.source_eq]
  have hval : ∀ x, (φ.trans jE) x = (j (φ x) : S n) := fun x => rfl
  have hsub : ((↑) ⁻¹' ((φ.trans jE) '' P) : Set (Sphere.openHemisphere l)) = j '' (φ '' P) := by
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      exact ⟨φ x, mem_image_of_mem _ hx, Subtype.ext hxy⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
  have hzimg : (z.comp j.symm.toAffineMap) '' ((↑) ⁻¹' ((φ.trans jE) '' P)) = z '' (φ '' P) := by
    rw [hsub, image_image]
    refine image_congr fun y _ => ?_
    simp
  refine ⟨h.isOpen, h.isConnected, hsrc, ?_, ?_, ?_, ?_, ?_⟩
  · -- the chart `j ∘ φ` is compatible with the canonical projective structure
    rw [isCompatibleChart_iff, mem_maximalAtlas_iff_eventually]
    intro x hx
    rw [hsrc, ← h.source_eq] at hx
    obtain ⟨a, ha⟩ := mem_maximalAtlas_iff_eventually.1 (isCompatibleChart_iff.1 h.compatible) x hx
    refine ⟨σ * Sphere.affToGS a, ?_⟩
    filter_upwards [ha] with y hy
    rw [hval, hσ, hy, transport_chartAt, mul_smul]
    congr 1
    exact Sphere.hemiChart_apply_eq_smul a _
  · rintro _ ⟨x, -, rfl⟩
    exact (j (φ x)).2
  · rw [hzimg]
    exact h.isGLB
  · intro y hy
    have : y ∈ j '' (φ '' P) := hsub ▸ hy
    obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := this
    simpa using h.le_one x hx
  · -- condition `b`
    intro Sg M N hSg hM ψ hψ hSψ hgerm
    haveI : LocallyConnectedSpace V := ChartedSpace.locallyConnectedSpace (Fin n → ℝ) V
    have hMSg : M ∈ Sg := hSg.left_mem
    have hNSg : N ∈ Sg := hSg.right_mem
    set K := connectedComponentIn ψ.source M with hKdef
    have hKo : IsOpen K := ψ.open_source.connectedComponentIn
    have hKp : IsPreconnected K := isPreconnected_connectedComponentIn
    have hKψ : K ⊆ ψ.source := connectedComponentIn_subset _ _
    have hMK : M ∈ K := mem_connectedComponentIn (hSψ hMSg)
    have hSK : Sg ⊆ K := hSg.isPreconnected.subset_connectedComponentIn hMSg hSψ
    have hev₀ : ∀ᶠ y in 𝓝 M, ψ y = (j (φ y) : S n) := hgerm
    have hMφ : M ∈ φ.source := h.source_eq ▸ hM
    have hloc := eventually_eq_affineEquiv_of_isPreconnected j hψ hKp hKψ hMK h.compatible hMφ
      hev₀
    have hrange : ∀ y ∈ K, ψ y = (j (jE.symm (ψ y)) : S n) := by
      intro y hy
      obtain ⟨e, -, -, hev⟩ := hloc y hy
      rw [hev.self_of_nhds, hjE_left]
    -- the affine chart `χ = j⁻¹ ∘ ψ` on `K`
    let χ := (ψ.restrOpen K hKo).trans jE.symm
    have hχ : ∀ y, χ y = jE.symm (ψ y) := fun y => rfl
    have hχsrc : χ.source = K := by
      ext y
      simp only [χ, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.restrOpen_source,
        OpenPartialHomeomorph.symm_source, hjE, IsOpenEmbedding.toOpenPartialHomeomorph_target,
        mem_inter_iff, mem_preimage, OpenPartialHomeomorph.coe_restrOpen]
      constructor
      · rintro ⟨⟨_, hy⟩, _⟩
        exact hy
      · intro hy
        refine ⟨⟨hKψ hy, hy⟩, ?_⟩
        rw [hrange y hy]
        exact mem_range_self _
    have hjχ : ∀ y ∈ K, (j (χ y) : S n) = ψ y := fun y hy => by
      rw [hχ]
      exact (hrange y hy).symm
    have hSχ : Sg ⊆ χ.source := by rw [hχsrc]; exact hSK
    have hχc : IsCompatibleChart (GAR n) χ := by
      rw [isCompatibleChart_iff, mem_maximalAtlas_iff_eventually]
      intro y hy
      rw [hχsrc] at hy
      obtain ⟨e, he, hye, hev⟩ := hloc y hy
      obtain ⟨a, ha⟩ := mem_maximalAtlas_iff_eventually.1 (isCompatibleChart_iff.1 he) y hye
      refine ⟨a, ?_⟩
      filter_upwards [hev, ha] with y' h1 h2
      rw [hχ, h1, hjE_left, h2]
    have hχgerm : (χ : V → Fin n → ℝ) =ᶠ[𝓝 M] φ := by
      filter_upwards [hev₀] with y hy
      rw [hχ, hy, hjE_left]
    obtain ⟨-, hψimg⟩ := hSg.image_eq hψ hSψ
    have hχimg : χ '' Sg = segment ℝ (χ M) (χ N) := by
      apply (Subtype.val_injective.comp j.injective).image_injective
      have e1 : (Subtype.val ∘ j) '' (χ '' Sg) = ψ '' Sg := by
        rw [image_image]
        exact image_congr fun y hy => hjχ y (hSK hy)
      have e2 : (Subtype.val ∘ j) '' segment ℝ (χ M) (χ N) =
          Sphere.closedSeg (j (χ M) : S n) (j (χ N)) := by
        rw [image_comp, ← affineSegment_eq_segment, ← Sphere.coe_image_affineSegment]
        congr 1
        exact affineSegment_image j.toAffineMap (χ M) (χ N)
      rw [e1, e2, hψimg, hjχ M (hSK hMSg), hjχ N (hSK hNSg)]
    refine ⟨?_, fun hN hz => ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      rw [← hjχ y (hSK hy)]
      exact (j (χ y)).2
    · have hseg : IsAffSegment n Sg M N :=
        ⟨χ, hχc, hSχ, hSχ hMSg, hSχ hNSg, trivial, hχimg⟩
      refine h.mem_of_segment Sg M N hseg hM χ hχc hSχ hχgerm ?_
      have : (⟨ψ N, hN⟩ : Sphere.openHemisphere l) = j (χ N) :=
        Subtype.ext (hjχ N (hSK hNSg)).symm
      rw [this] at hz
      simpa using hz

end Local

/-- **Pockets depend on the projective structure only through its maximal atlas**: two charted
spaces over `S(n)` with the same maximal atlas have the same compatible charts, segments and
pockets. -/
theorem IsPocheProj.of_maximalAtlas_eq {W : Type u} [TopologicalSpace W]
    (cs cs' : ChartedSpace (S n) W)
    (hcs : @StructureGroupoid.maximalAtlas (S n) W _ _ cs (projGroupoid n) =
      @StructureGroupoid.maximalAtlas (S n) W _ _ cs' (projGroupoid n))
    {P : Set W} {l : Module.Dual ℝ (Fin (n + 1) → ℝ)} [Fact (l ≠ 0)]
    {φ : OpenPartialHomeomorph W (S n)} {z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ}
    (h : @IsPocheProj n W _ cs P l _ φ z) : @IsPocheProj n W _ cs' P l _ φ z := by
  have hc : ∀ e : OpenPartialHomeomorph W (S n),
      @IsCompatibleChart W _ (S n) _ (GSR n) _ _ _ cs' e →
        @IsCompatibleChart W _ (S n) _ (GSR n) _ _ _ cs e := by
    intro e he
    unfold IsCompatibleChart jets at he ⊢
    rw [hcs]
    exact he
  have hc' : ∀ e : OpenPartialHomeomorph W (S n),
      @IsCompatibleChart W _ (S n) _ (GSR n) _ _ _ cs e →
        @IsCompatibleChart W _ (S n) _ (GSR n) _ _ _ cs' e := by
    intro e he
    unfold IsCompatibleChart jets at he ⊢
    rw [← hcs]
    exact he
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨h1, h2, h3, hc' _ h4, h5, h6, h7, fun Sg M N hS hM ψ hψ hSψ hg => ?_⟩
  obtain ⟨φ₀, hφ₀, hrest⟩ := hS
  exact h8 Sg M N ⟨φ₀, hc _ hφ₀, hrest⟩ hM ψ (hc _ hψ) hSψ hg

section Local

attribute [local instance] projOfAff hasGroupoid_projOfAff

omit [ChartedSpace (Fin n → ℝ) V] in
/-- The image of `P` by `j ∘ φ`, read in `H̊`, is `j(φ(P))`. -/
theorem coe_preimage_image_trans {l : Module.Dual ℝ (Fin (n + 1) → ℝ)} [Fact (l ≠ 0)]
    (j : (Fin n → ℝ) ≃ᵃ[ℝ] Sphere.openHemisphere l) (φ : OpenPartialHomeomorph V (Fin n → ℝ))
    (P : Set V) :
    ((↑) ⁻¹' ((φ.trans ((isOpenEmbedding_coe_affineEquiv j).toOpenPartialHomeomorph _)) '' P) :
      Set (Sphere.openHemisphere l)) = j '' (φ '' P) := by
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    exact ⟨φ x, mem_image_of_mem _ hx, Subtype.ext hxy⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩

/-- The Remarque for shells (Déf. 2): the projective pocket of an affine shell is a shell. -/
theorem IsCoqueAff.toCoqueProj [HasGroupoid V (affGroupoid n)] {P : Set V}
    {φ : OpenPartialHomeomorph V (Fin n → ℝ)} {z : (Fin n → ℝ) →ᵃ[ℝ] ℝ}
    (h : IsCoqueAff P φ z) {l : Module.Dual ℝ (Fin (n + 1) → ℝ)} [Fact (l ≠ 0)]
    (j : (Fin n → ℝ) ≃ᵃ[ℝ] Sphere.openHemisphere l) :
    @IsCoqueProj n V _ (projOfAff n V) P l _
      (φ.trans ((isOpenEmbedding_coe_affineEquiv j).toOpenPartialHomeomorph _))
      (z.comp j.symm.toAffineMap) := by
  have hp := h.1.toPocheProj j
  refine ⟨hp, ?_⟩
  rw [Sphere.isConvexPart_iff_isAffConvex hp.image_subset, coe_preimage_image_trans]
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← AffineEquiv.coe_toAffineMap, ← affineSegment_image, affineSegment_eq_segment]
  exact image_mono (h.2.segment_subset ha hb)

/-- The Remarque for strict shells (Déf. 3): the projective pocket of an affine strict shell is a
strict shell. -/
theorem IsCoqueStricteAff.toCoqueStricteProj [HasGroupoid V (affGroupoid n)] {P : Set V}
    {φ : OpenPartialHomeomorph V (Fin n → ℝ)} {z : (Fin n → ℝ) →ᵃ[ℝ] ℝ}
    (h : IsCoqueStricteAff P φ z) {l : Module.Dual ℝ (Fin (n + 1) → ℝ)} [Fact (l ≠ 0)]
    (j : (Fin n → ℝ) ≃ᵃ[ℝ] Sphere.openHemisphere l) :
    @IsCoqueStricteProj n V _ (projOfAff n V) P l _
      (φ.trans ((isOpenEmbedding_coe_affineEquiv j).toOpenPartialHomeomorph _))
      (z.comp j.symm.toAffineMap) := by
  refine ⟨h.1.toCoqueProj j, ?_⟩
  rintro ⟨A, ⟨m, w, hw, rfl⟩, hA⟩
  rw [coe_preimage_image_trans] at hA
  refine h.2 ⟨range fun t : ℝ => t • j.symm.linear w +ᵥ j.symm m,
    ⟨j.symm m, j.symm.linear w, (LinearEquiv.map_ne_zero_iff _).2 hw, rfl⟩, ?_⟩
  rintro _ ⟨t, rfl⟩
  obtain ⟨x, hx, hxe⟩ := hA ⟨t, rfl⟩
  have hxe' : j x = t • w +ᵥ m := hxe
  have : t • j.symm.linear w +ᵥ j.symm m = x := by
    rw [← map_smul, ← AffineEquiv.map_vadd, ← hxe', AffineEquiv.symm_apply_apply]
  show t • j.symm.linear w +ᵥ j.symm m ∈ φ '' P
  rw [this]
  exact hx

end Local

/-- **The Remarque after Déf. 1′, with the structure built from `j` itself** (Ch. 1, Déf. 12,
Remarque: `J''(V) = GS ∘ j ∘ J(V)`, the structure of the charts `j ∘ ψ`): it has the maximal atlas of
the canonical one (`remarque_affine_vers_projective`), hence the same pockets. -/
theorem IsPocheAff.toPocheProj_transport [HasGroupoid V (affGroupoid n)] {P : Set V}
    {φ : OpenPartialHomeomorph V (Fin n → ℝ)} {z : (Fin n → ℝ) →ᵃ[ℝ] ℝ}
    (h : IsPocheAff P φ z) {l : Module.Dual ℝ (Fin (n + 1) → ℝ)} [Fact (l ≠ 0)]
    (j : (Fin n → ℝ) ≃ᵃ[ℝ] Sphere.openHemisphere l) :
    @IsPocheProj n V _ (transportChartedSpace (isOpenEmbedding_coe_affineEquiv j) V) P l _
      (φ.trans ((isOpenEmbedding_coe_affineEquiv j).toOpenPartialHomeomorph _))
      (z.comp j.symm.toAffineMap) := by
  obtain ⟨_, _, _, _, _, hmax⟩ :=
    remarque_affine_vers_projective (isAffine_of_affineMap j.toAffineMap) j.injective V
  exact IsPocheProj.of_maximalAtlas_eq _ _ hmax.symm (h.toPocheProj j)

end Remarque0

/-! ### Remarque 1 — the lines of an open hemisphere are half-lines of `S(n)` -/

section Remarque1

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

namespace Sphere

/-- For `x, M` independent, `x t + M ≠ 0`. -/
theorem smul_add_ne_zero {x M : E} (hxM : LinearIndependent ℝ ![x, M]) (t : ℝ) :
    t • x + M ≠ 0 := by
  have := ne_zero_of_linearIndependent hxM (a := t) (b := 1) one_ne_zero
  rwa [one_smul] at this

/-- **A half-line as a parametrised curve**: for `x, M` independent,
`s({a x + b M | b > 0}) = {s(M + t x) | t ∈ ℝ}`. -/
theorem halfLine_eq_range {x M : E} (hxM : LinearIndependent ℝ ![x, M]) :
    halfLine x M = range fun t : ℝ => mk (t • x + M) (smul_add_ne_zero hxM t) := by
  ext y
  induction y using ind with
  | h u hu =>
    rw [mk_mem_halfLine]
    constructor
    · rintro ⟨a, b, hb, rfl⟩
      refine ⟨a / b, ?_⟩
      rw [mk_eq_mk_iff_exists_pos]
      exact ⟨b, hb, by rw [smul_add, smul_smul, mul_div_cancel₀ _ hb.ne']⟩
    · rintro ⟨t, ht⟩
      obtain ⟨c, hc, hcu⟩ := (mk_eq_mk_iff_exists_pos _ hu).1 ht
      exact ⟨c * t, c, hc, by rw [← hcu, smul_add, smul_smul]⟩

/-- A half-line does not change when its second vector is multiplied by `c > 0`. -/
theorem halfLine_smul_right (v w : E) {c : ℝ} (hc : 0 < c) : halfLine v (c • w) = halfLine v w := by
  ext y
  induction y using ind with
  | h u hu =>
    rw [mk_mem_halfLine, mk_mem_halfLine]
    constructor
    · rintro ⟨a, b, hb, rfl⟩
      exact ⟨a, b * c, mul_pos hb hc, by rw [smul_smul]⟩
    · rintro ⟨a, b, hb, rfl⟩
      exact ⟨a, b / c, div_pos hb hc, by rw [smul_smul, div_mul_cancel₀ _ hc.ne']⟩

variable {l : Module.Dual ℝ E}

theorem l_smul_add_nrep (u : HemiTrans l) (m : openHemisphere l) (t : ℝ) :
    l (t • (u (hq l (nrep l m)) : E) + nrep l m) = 1 := by
  rw [map_add, map_smul, l_coe_ker, smul_zero, zero_add, l_nrep m.2]

/-- **The points of a line of `H̊`**: `m + t u = s(M + t u(q M))`, `M = m / l(m)`. -/
theorem coe_smul_vadd (u : HemiTrans l) (m : openHemisphere l) (t : ℝ) :
    ((t • u +ᵥ m : openHemisphere l) : Sphere E) =
      mk (t • (u (hq l (nrep l m)) : E) + nrep l m)
        (ne_zero_of_l_pos (by rw [l_smul_add_nrep]; exact one_pos)) := by
  rw [← mk_nrep (t • u +ᵥ m : openHemisphere l).2]
  refine mk_eq_mk_of_eq' ?_
  rw [nrep_vadd, transl, LinearMap.smul_apply, Submodule.coe_smul, add_comm]

/-- A nonzero translation of `H̊` does not vanish on the class of a point of `H̊`. -/
theorem coe_apply_hq_nrep_ne_zero {u : HemiTrans l} (hu : u ≠ 0) (m : openHemisphere l) :
    (u (hq l (nrep l m)) : E) ≠ 0 := by
  intro h
  apply hu
  rw [eq_smulRight (l_nrep m.2) u]
  have : u (hq l (nrep l m)) = 0 := Subtype.ext h
  rw [this, LinearMap.smulRight_zero]

/-- The direction `u(q M)` of a line of `H̊` and the point `M = m / l(m)` are independent. -/
theorem linearIndependent_apply_hq_nrep {u : HemiTrans l} (hu : u ≠ 0) (m : openHemisphere l) :
    LinearIndependent ℝ ![(u (hq l (nrep l m)) : E), nrep l m] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h1 := congrArg l hst
  rw [map_add, map_smul, map_smul, l_coe_ker, l_nrep m.2, smul_zero, zero_add, smul_eq_mul,
    mul_one, map_zero] at h1
  subst h1
  rw [zero_smul, add_zero] at hst
  exact ⟨(smul_eq_zero.1 hst).resolve_right (coe_apply_hq_nrep_ne_zero hu m), rfl⟩

/-- **The image of a line of `H̊` in `S(E)`**: `m + ℝ u = s({a u(q M) + b M | b > 0})`. -/
theorem coe_image_range_smul_vadd {u : HemiTrans l} (hu : u ≠ 0) (m : openHemisphere l) :
    ((↑) '' range (fun t : ℝ => t • u +ᵥ m) : Set (Sphere E)) =
      halfLine (u (hq l (nrep l m)) : E) (nrep l m) := by
  rw [halfLine_eq_range (linearIndependent_apply_hq_nrep hu m), ← range_comp]
  congr 1
  funext t
  exact coe_smul_vadd u m t

end Sphere

/-- **Remarque 1** (`bzrem:c2s1r1_droite_hemisphere`): a part `A` of the open hemisphere `H̊` of
equation `l ≠ 0` is a line of the affine space `H̊` (Déf. 6) iff, as a part of `S(E)`, it is a
half-line `s({a v + b w | b > 0})` of `S(E)`. -/
theorem isAffLine_hemi_iff {l : Module.Dual ℝ E} [Fact (l ≠ 0)]
    (A : Set (Sphere.openHemisphere l)) :
    IsAffLine (Sphere.HemiTrans l) A ↔
      ∃ v w : E, LinearIndependent ℝ ![v, w] ∧ ((↑) '' A : Set (Sphere E)) = Sphere.halfLine v w := by
  open Sphere in
  constructor
  · rintro ⟨m, u, hu, rfl⟩
    exact ⟨_, _, linearIndependent_apply_hq_nrep hu m, coe_image_range_smul_vadd hu m⟩
  · rintro ⟨v, w, hvw, hA⟩
    have hsub : halfLine v w ⊆ openHemisphere l := by
      rw [← hA]
      rintro _ ⟨y, -, rfl⟩
      exact y.2
    have hpos : ∀ a b : ℝ, 0 < b → 0 < a * l v + b * l w := by
      intro a b hb
      have := hsub ((mk_mem_halfLine (ne_zero_of_linearIndependent hvw hb.ne')).2
        ⟨a, b, hb, rfl⟩)
      rw [mk_mem_openHemisphere, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at this
      exact this
    have hlw : 0 < l w := by simpa using hpos 0 1 one_pos
    have hlv : l v = 0 := by
      by_contra hne
      have := hpos (-(2 * l w) / l v) 1 one_pos
      rw [div_mul_cancel₀ _ hne, one_mul] at this
      linarith
    set M : E := (l w)⁻¹ • w with hMdef
    have hlM : l M = 1 := by rw [hMdef, map_smul, smul_eq_mul, inv_mul_cancel₀ hlw.ne']
    have hM0 : M ≠ 0 := ne_zero_of_l_pos (by rw [hlM]; exact one_pos)
    let m : openHemisphere l := ⟨mk M hM0, (mk_mem_openHemisphere hM0).2 (by rw [hlM]; exact one_pos)⟩
    have hnm : nrep l m = M := nrep_mk_of_l_eq_one hlM
    let u : HemiTrans l := (lbar l).smulRight (⟨v, hlv⟩ : LinearMap.ker l)
    have huM : (u (hq l (nrep l m)) : E) = v := by
      simp only [u, LinearMap.smulRight_apply, lbar_hq, hnm, hlM, one_smul]
    have hu : u ≠ 0 := by
      intro h0
      have : (u (hq l (nrep l m)) : E) = 0 := by rw [h0]; rfl
      rw [huM] at this
      exact hvw.ne_zero 0 this
    refine ⟨m, u, hu, Subtype.val_injective.image_injective ?_⟩
    rw [hA, coe_image_range_smul_vadd hu m, huM, hnm, hMdef,
      halfLine_smul_right v w (inv_pos.2 hlw)]

/-- **Remarque 1, « ou portion de droite comprise entre deux points diamétralement opposés »**: a
line of `H̊` is, in `S(E)`, a half-line `s({a v + b w | b > 0})` of the line
`D = s(span{v, w} - {O})` of `S(E)` (Déf. 4), and `D` minus the diametrically opposite points
`s(v)`, `-s(v)` is the union of this half-line and the opposite one. -/
theorem IsAffLine.exists_halfLine_hemi {l : Module.Dual ℝ E} [Fact (l ≠ 0)]
    {A : Set (Sphere.openHemisphere l)} (hA : IsAffLine (Sphere.HemiTrans l) A) :
    ∃ (v w : E) (hvw : LinearIndependent ℝ ![v, w]),
      ((↑) '' A : Set (Sphere E)) = Sphere.halfLine v w ∧
      Sphere.IsLine (Sphere.linearSubvariety (Submodule.span ℝ {v, w})) ∧
      Sphere.halfLine v w ⊆ Sphere.linearSubvariety (Submodule.span ℝ {v, w}) ∧
      Sphere.linearSubvariety (Submodule.span ℝ {v, w}) \
          {Sphere.mk v (hvw.ne_zero 0), -Sphere.mk v (hvw.ne_zero 0)} =
        Sphere.halfLine v w ∪ Sphere.halfLine v (-w) := by
  obtain ⟨v, w, hvw, himg⟩ := (isAffLine_hemi_iff A).1 hA
  refine ⟨v, w, hvw, himg, ⟨_, ?_, rfl⟩, Sphere.halfLine_subset_linearSubvariety v w,
    Sphere.linearSubvariety_pair_diff hvw⟩
  have := finrank_span_eq_card hvw
  rw [Matrix.range_cons_cons_empty] at this
  rw [this]
  simp

end Remarque1

/-! ### Remarque 2 — a shell is strict iff the closure of `φ(P)` is a convex body -/

section Remarque2

namespace Sphere

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- **The cone of the closure**: `F(Ā) = closure F(A) - {O}` (`s` is open and continuous). -/
theorem F_closure [ContinuousConstSMul ℝ E] (A : Set (Sphere E)) :
    F (closure A) = closure (F A) \ {0} := by
  have h1 : s ⁻¹' closure A = closure (s ⁻¹' A) :=
    isOpenMap_s.preimage_closure_eq_closure_preimage continuous_s A
  have h2 : closure (s ⁻¹' A) =
      (Subtype.val : {v : E // v ≠ 0} → E) ⁻¹' closure (Subtype.val '' (s ⁻¹' A)) :=
    Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image _
  rw [F_eq_image, h1, h2, ← F_eq_image, image_preimage_eq_inter_range, Subtype.range_coe_subtype]
  ext v
  simp [and_comm]

omit [TopologicalSpace E] in
/-- In a half-line `s({a v + b w | b > 0})`, `v, w` independent, `a v + b w ≠ 0` for `a ≠ 0`. -/
theorem smul_add_smul_ne_zero {v w : E} (hvw : LinearIndependent ℝ ![v, w]) {a : ℝ} (ha : a ≠ 0)
    (b : ℝ) : a • v + b • w ≠ 0 := fun h => ha (LinearIndependent.pair_iff.1 hvw a b h).1

/-- **The two ends of a half-line are in its closure**: `s(a v)`, `a ≠ 0` (i.e. `s(v)` and
`s(-v)`), is a limit of points of the half-line `s({a v + b w | b > 0})`. -/
theorem mk_smul_mem_closure_halfLine [ContinuousAdd E] [ContinuousSMul ℝ E] {v w : E}
    (hvw : LinearIndependent ℝ ![v, w]) {a : ℝ} (ha : a ≠ 0) :
    mk (a • v) (smul_ne_zero ha (hvw.ne_zero 0)) ∈ closure (halfLine v w) := by
  let f : ℝ → Sphere E := fun b => mk (a • v + b • w) (smul_add_smul_ne_zero hvw ha b)
  have hf : Continuous f := continuous_mk_comp (continuous_const.add
    (continuous_id.smul continuous_const)) _
  have hf0 : f 0 = mk (a • v) (smul_ne_zero ha (hvw.ne_zero 0)) :=
    mk_eq_mk_of_eq' (by rw [zero_smul, add_zero])
  rw [← hf0]
  refine mem_closure_of_tendsto (b := 𝓝[>] (0 : ℝ))
    (tendsto_nhdsWithin_of_tendsto_nhds (hf.tendsto 0)) ?_
  filter_upwards [self_mem_nhdsWithin] with b hb
  exact (mk_mem_halfLine _).2 ⟨a, b, hb, rfl⟩

end Sphere

variable {n : ℕ} {V : Type u} [TopologicalSpace V] [ChartedSpace (S n) V]

/-- **Remarque 2** (`bzrem:c2s1r2_coque_stricte_corps_convexe`): a shell `(P, H̊, φ, z)` is strict
(Déf. 3: `φ(P)` contains no line of the affine space `H̊`) iff the closure of `φ(P)` in `S(n)` is a
convex body of `S(n)` (Ch. 1, Déf. 11: a strict convex part, compact, with nonempty interior). -/
theorem IsCoqueProj.isCoqueStricte_iff {P : Set V} {l : Module.Dual ℝ (Fin (n + 1) → ℝ)}
    [Fact (l ≠ 0)] {φ : OpenPartialHomeomorph V (S n)} {z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ}
    (h : IsCoqueProj P l φ z) :
    IsCoqueStricteProj P l φ z ↔ IsCorpsConvexeS n (closure (φ '' P)) := by
  open Sphere in
  set k := φ '' P with hkdef
  have hksub : k ⊆ openHemisphere l := h.1.image_subset
  have hkopen : IsOpen k := by
    rw [hkdef, ← h.1.source_eq, φ.image_source_eq_target]
    exact φ.open_target
  have hkne : k.Nonempty := h.1.isConnected.nonempty.image _
  have hlc : Continuous l := LinearMap.continuous_of_finiteDimensional l
  refine ⟨fun hs => ?_, fun hb => ⟨h, ?_⟩⟩
  · -- a strict shell: the closure of `φ(P)` is a convex body
    refine ⟨?_, isClosed_closure.isCompact, hkne.mono
      (interior_maximal subset_closure hkopen)⟩
    have hFconv : Convex ℝ (F k) := isStrictConvexPart_iff_convex_F.1
      ⟨h.2, fun m hm hm' => ne_neg_of_mem_openHemisphere (hksub hm) (hksub hm') rfl⟩
    set C := closure (F k) with hCdef
    have hCconv : Convex ℝ C := hFconv.closure
    have hCsmul : ∀ c : ℝ, 0 < c → ∀ x ∈ C, c • x ∈ C := by
      intro c hc x hx
      have : c • x ∈ c • C := smul_mem_smul_set hx
      rw [hCdef, ← closure_smul₀] at this
      refine closure_mono (fun y hy => ?_) this
      obtain ⟨y', hy', rfl⟩ := Set.mem_smul_set.1 hy
      exact smul_mem_F hy' hc
    have hCadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C := by
      intro x hx y hy
      have := hCconv hx hy (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)
      have h2 := hCsmul 2 two_pos _ this
      rwa [smul_add, smul_smul, smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul,
        one_smul] at h2
    have hFpos : F k ⊆ {v | 0 ≤ l v} := by
      intro v hv
      have := F_mono hksub hv
      rw [F_openHemisphere] at this
      exact le_of_lt (show 0 < l v from this)
    have hCpos : C ⊆ {v | 0 ≤ l v} :=
      closure_minimal hFpos (isClosed_le continuous_const hlc)
    -- `±x ∈ C`, `x ≠ 0`, would give a line of `H̊` in `φ(P)`
    have hsal : ∀ x ∈ C, -x ∈ C → x = 0 := by
      intro x hx hnx
      by_contra hx0
      have hlx : l x = 0 := by
        have h1 := hCpos hx
        have h2 := hCpos hnx
        simp only [mem_setOf_eq, map_neg] at h1 h2
        linarith
      obtain ⟨m₀, hm₀⟩ := hkne
      set p := nrep l m₀ with hp
      have hlp : l p = 1 := l_nrep (hksub hm₀)
      have hp0 : p ≠ 0 := nrep_ne_zero (hksub hm₀)
      have hpF : p ∈ F k := ⟨hp0, by
        show mk p hp0 ∈ k
        convert hm₀ using 1
        exact mk_nrep (hksub hm₀)⟩
      have hFopen : IsOpen (F k) := isOpen_iff_F.1 hkopen
      have hline : ∀ t : ℝ, p + t • x ∈ F k := by
        intro t
        have hq : p + (2 * t) • x ∈ C := by
          rcases lt_trichotomy t 0 with ht | rfl | ht
          · have := hCadd p (subset_closure hpF) _ (hCsmul (-(2 * t)) (by linarith) _ hnx)
            rwa [smul_neg, ← neg_smul, neg_neg] at this
          · rw [mul_zero, zero_smul, add_zero]
            exact subset_closure hpF
          · exact hCadd p (subset_closure hpF) _ (hCsmul (2 * t) (by linarith) _ hx)
        have hseg := hFconv.openSegment_interior_closure_subset_interior
          (hFopen.interior_eq.symm ▸ hpF) hq
        rw [hFopen.interior_eq] at hseg
        refine hseg ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
        module
      let m : openHemisphere l := ⟨m₀, hksub hm₀⟩
      let u : HemiTrans l := (lbar l).smulRight (⟨x, hlx⟩ : LinearMap.ker l)
      have hum : (u (hq l (nrep l (m : Sphere (Fin (n + 1) → ℝ)))) : Fin (n + 1) → ℝ) = x := by
        simp only [u, m, LinearMap.smulRight_apply, lbar_hq, ← hp, hlp, one_smul]
      have hu : u ≠ 0 := by
        intro h0
        have : (u (hq l (nrep l (m : Sphere (Fin (n + 1) → ℝ)))) : Fin (n + 1) → ℝ) = 0 := by
          rw [h0]; rfl
        exact hx0 (hum ▸ this)
      refine hs.2 ⟨_, ⟨m, u, hu, rfl⟩, ?_⟩
      rintro _ ⟨t, rfl⟩
      show ((t • u +ᵥ m : openHemisphere l) : Sphere (Fin (n + 1) → ℝ)) ∈ k
      rw [coe_smul_vadd]
      have := hline t
      obtain ⟨_, hmem⟩ := this
      convert hmem using 1
      exact mk_eq_mk_of_eq' (by rw [hum]; exact add_comm _ _)
    rw [isStrictConvexPart_iff_convex_F, F_closure]
    intro x hx y hy a b ha hb hab
    refine ⟨hCconv hx.1 hy.1 ha hb hab, fun h0 => ?_⟩
    have h0 : a • x + b • y = 0 := h0
    rcases ha.lt_or_eq with ha' | rfl
    · rcases hb.lt_or_eq with hb' | rfl
      · -- `y = -(a/b) x`, so `-x ∈ C`
        have hy' : y = -((a / b) • x) := by
          have h1 : b • y = -(a • x) := eq_neg_of_add_eq_zero_right h0
          have h2 : y = b⁻¹ • (b • y) := by rw [smul_smul, inv_mul_cancel₀ hb'.ne', one_smul]
          rw [h2, h1, smul_neg, smul_smul, div_eq_inv_mul]
        have hnx : -x ∈ C := by
          have := hCsmul (b / a) (div_pos hb' ha') _ hy.1
          rwa [hy', smul_neg, smul_smul, div_mul_div_cancel₀ ha'.ne', div_self hb'.ne',
            one_smul] at this
        exact hx.2 (hsal x hx.1 hnx)
      · rw [add_zero] at hab
        rw [hab, one_smul, zero_smul, add_zero] at h0
        exact hx.2 h0
    · rw [zero_add] at hab
      rw [hab, one_smul, zero_smul, zero_add] at h0
      exact hy.2 h0
  · -- conversely: a line of `H̊` in `φ(P)` puts two opposite points in the closure
    rintro ⟨A, hA, hAk⟩
    obtain ⟨v, w, hvw, himg⟩ := (isAffLine_hemi_iff A).1 hA
    have hsub : halfLine v w ⊆ k := by
      rw [← himg]
      rintro _ ⟨y, hy, rfl⟩
      exact hAk hy
    have h1 := closure_mono hsub (mk_smul_mem_closure_halfLine hvw (one_ne_zero))
    have h2 := closure_mono hsub (mk_smul_mem_closure_halfLine hvw (neg_ne_zero.2 one_ne_zero))
    refine hb.1.2 _ h1 ?_
    convert h2 using 1
    rw [neg_mk]
    exact mk_eq_mk_of_eq' (by rw [neg_smul])

end Remarque2

/-! ### The two examples of p. 247–248, and non-vacuity -/

section Exemples

variable {n : ℕ}

/-- **Non-vacuity of Déf. 1**: `(ℝⁿ, id, 0)` is a pocket of the model `ℝⁿ` (the degenerate pocket
of constant cote `0`). -/
theorem isPocheAff_model (n : ℕ) :
    IsPocheAff (univ : Set (Fin n → ℝ)) (OpenPartialHomeomorph.refl _) 0 where
  isOpen := isOpen_univ
  isConnected := isConnected_univ
  source_eq := rfl
  compatible := isCompatibleChart_iff.2 (gxGroupoid _ _).id_mem_maximalAtlas
  isGLB := by
    refine ⟨?_, fun b hb => hb ⟨0, ⟨0, trivial, rfl⟩, rfl⟩⟩
    rintro _ ⟨_, -, rfl⟩
    exact le_refl _
  le_one _ _ := zero_le_one
  mem_of_segment _ _ _ _ _ _ _ _ _ _ := trivial

/-- **Non-vacuity of Déf. 1′** (through the Remarque after it): `ℝⁿ`, with its canonical locally
projective structure, has a pocket over the hemisphere `H₀ = {x_{n+1} > 0}`. -/
theorem exists_isPocheProj_model (n : ℕ) :
    ∃ (φ : OpenPartialHomeomorph (Fin n → ℝ) (S n))
      (z : Sphere.openHemisphere (Sphere.lastForm n) →ᵃ[ℝ] ℝ),
      @IsPocheProj n (Fin n → ℝ) _ (projOfAff n (Fin n → ℝ)) univ (Sphere.lastForm n) _ φ z := by
  obtain ⟨e⟩ := Sphere.nonempty_hemi_affineEquiv (l := Sphere.lastForm n)
    (Module.finrank_fin_fun ℝ)
  exact ⟨_, _, (isPocheAff_model n).toPocheProj e.symm⟩

variable {V : Type u} [TopologicalSpace V]

/-- **« Exemple dans le cas affin »** (p. 247–248): `W` étalé over `ℝⁿ` by `p` (a developing map:
all its jets are in `J(W)`), `z` a linear (affine) function, `P` the connected component of `x₀` in
`p⁻¹(z < 1)`; if `z` has infimum `0` on `p(P)`, then `(P, p, z)` is a pocket of `W` — **provided
`p` is injective on `P`**, which a « carte » requires and the paper does not state (see SCOPE). -/
theorem exemple_poche_affine [ChartedSpace (Fin n → ℝ) V] [HasGroupoid V (affGroupoid n)]
    {p : V → Fin n → ℝ} (hp : IsDeveloping (GAR n) p) (z : (Fin n → ℝ) →ᵃ[ℝ] ℝ) {x₀ : V}
    (hx₀ : z (p x₀) < 1)
    (hinf : IsGLB (z '' (p '' connectedComponentIn (p ⁻¹' {y | z y < 1}) x₀)) 0)
    (hinj : InjOn p (connectedComponentIn (p ⁻¹' {y | z y < 1}) x₀)) :
    ∃ φ : OpenPartialHomeomorph V (Fin n → ℝ),
      EqOn φ p (connectedComponentIn (p ⁻¹' {y | z y < 1}) x₀) ∧
      IsPocheAff (connectedComponentIn (p ⁻¹' {y | z y < 1}) x₀) φ z := by
  set P := connectedComponentIn (p ⁻¹' {y | z y < 1}) x₀ with hPdef
  haveI : LocallyConnectedSpace V := ChartedSpace.locallyConnectedSpace (Fin n → ℝ) V
  haveI : Nonempty V := ⟨x₀⟩
  have hzc : Continuous z := z.continuous_of_finiteDimensional
  have hUo : IsOpen (p ⁻¹' {y | z y < 1}) :=
    (isOpen_lt hzc continuous_const).preimage hp.continuous
  have hPo : IsOpen P := hUo.connectedComponentIn
  have hPU : P ⊆ p ⁻¹' {y | z y < 1} := connectedComponentIn_subset _ _
  let φ : OpenPartialHomeomorph V (Fin n → ℝ) :=
    OpenPartialHomeomorph.ofContinuousOpen (hinj.toPartialEquiv p P) hp.continuous.continuousOn
      hp.isLocalHomeomorph.isOpenMap hPo
  have hφ : (φ : V → Fin n → ℝ) = p := rfl
  refine ⟨φ, fun x _ => rfl, hPo, isConnected_connectedComponentIn_iff.2 hx₀, rfl,
    fun x _ => hp x, by rw [hφ]; exact hinf, fun x hx => le_of_lt (hPU hx), ?_⟩
  intro Sg M N hSg hM ψ hψ hSψ hgerm hzN
  have hpre := hSg.isPreconnected
  have hMS : M ∈ Sg := hSg.left_mem
  have hNS : N ∈ Sg := hSg.right_mem
  have heq : EqOn ψ p Sg := eqOn_of_germ_eq_isDeveloping hψ hp hpre hSψ hMS hgerm
  have himg := hSg.image_eq hψ hSψ
  have hconv : Convex ℝ {y : Fin n → ℝ | z y < 1} := (convex_Iio (1 : ℝ)).affine_preimage z
  have hsegU : segment ℝ (ψ M) (ψ N) ⊆ {y | z y < 1} :=
    hconv.segment_subset (by rw [heq hMS]; exact hPU hM) hzN
  have hSU : Sg ⊆ p ⁻¹' {y | z y < 1} := by
    intro y hy
    have : ψ y ∈ segment ℝ (ψ M) (ψ N) := himg ▸ mem_image_of_mem ψ hy
    show p y ∈ {y | z y < 1}
    rw [← heq hy]
    exact hsegU this
  have hsub : Sg ⊆ connectedComponentIn (p ⁻¹' {y | z y < 1}) M :=
    hpre.subset_connectedComponentIn hMS hSU
  rw [← connectedComponentIn_eq hM] at hsub
  exact hsub hNS

/-- The open half-space `z < 1` of the affine space `H̊` (an open hemisphere of `S(n)`), as a part
of `S(n)`. -/
def demiEspace {l : Module.Dual ℝ (Fin (n + 1) → ℝ)} [Fact (l ≠ 0)]
    (z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ) : Set (S n) :=
  (↑) '' {q : Sphere.openHemisphere l | z q < 1}

/-- The half-space `z < 1` of `H̊` is open in `S(n)`. -/
theorem isOpen_demiEspace {l : Module.Dual ℝ (Fin (n + 1) → ℝ)} [Fact (l ≠ 0)]
    (z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ) : IsOpen (demiEspace z) := by
  obtain ⟨e⟩ := Sphere.nonempty_hemi_affineEquiv (l := l) (Module.finrank_fin_fun ℝ)
  have hj := isOpenEmbedding_coe_affineEquiv e.symm
  have hzc : Continuous (z.comp e.symm.toAffineMap) :=
    (z.comp e.symm.toAffineMap).continuous_of_finiteDimensional
  have : demiEspace z = (fun y => (e.symm y : S n)) '' {y | z (e.symm y) < 1} := by
    ext q
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨e m, by simpa using hm, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨e.symm y, hy, rfl⟩
  rw [this]
  exact hj.isOpenMap _ (isOpen_lt hzc continuous_const)

/-- **« Exemple dans le cas projectif »** (p. 248): `W` étalé over `S(n)` by `p` (developing), `H̊`
an open hemisphere, `z` a linear (affine) function on `H̊`, `P` the connected component of `x₀` in
`p⁻¹(z < 1)` (the half-space of `H̊`); if `z` has infimum `0` on `p(P)` and `p(M, N) ⊆ H̊` for every
segment of `W` with origin in `P`, then `(P, H̊, p, z)` is a pocket of `W` — **provided `p` is
injective on `P`** (see SCOPE). -/
theorem exemple_poche_projective [ChartedSpace (S n) V] [HasGroupoid V (projGroupoid n)]
    {p : V → S n} (hp : IsDeveloping (GSR n) p) {l : Module.Dual ℝ (Fin (n + 1) → ℝ)}
    [Fact (l ≠ 0)] (z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ) {x₀ : V} (hx₀ : p x₀ ∈ demiEspace z)
    (hinf : IsGLB (z '' ((↑) ⁻¹' (p '' connectedComponentIn (p ⁻¹' demiEspace z) x₀))) 0)
    (hseg : ∀ (Sg : Set V) (M N : V), IsProjSegment n Sg M N →
      M ∈ connectedComponentIn (p ⁻¹' demiEspace z) x₀ → p '' Sg ⊆ Sphere.openHemisphere l)
    (hinj : InjOn p (connectedComponentIn (p ⁻¹' demiEspace z) x₀)) :
    ∃ φ : OpenPartialHomeomorph V (S n),
      EqOn φ p (connectedComponentIn (p ⁻¹' demiEspace z) x₀) ∧
      IsPocheProj (connectedComponentIn (p ⁻¹' demiEspace z) x₀) l φ z := by
  set P := connectedComponentIn (p ⁻¹' demiEspace z) x₀ with hPdef
  haveI : LocPathConnectedSpace V := locPathConnectedSpace_of_proj (n := n)
  haveI : Nonempty V := ⟨x₀⟩
  have hUo : IsOpen (p ⁻¹' demiEspace z) := (isOpen_demiEspace z).preimage hp.continuous
  have hPo : IsOpen P := hUo.connectedComponentIn
  have hPU : P ⊆ p ⁻¹' demiEspace z := connectedComponentIn_subset _ _
  have hDH : demiEspace z ⊆ Sphere.openHemisphere l := by
    rintro _ ⟨q, -, rfl⟩
    exact q.2
  let φ : OpenPartialHomeomorph V (S n) :=
    OpenPartialHomeomorph.ofContinuousOpen (hinj.toPartialEquiv p P) hp.continuous.continuousOn
      hp.isLocalHomeomorph.isOpenMap hPo
  have hφ : (φ : V → S n) = p := rfl
  refine ⟨φ, fun x _ => rfl, hPo, isConnected_connectedComponentIn_iff.2 hx₀, rfl,
    fun x _ => hp x, ?_, by rw [hφ]; exact hinf, ?_, ?_⟩
  · rw [hφ]
    rintro _ ⟨x, hx, rfl⟩
    exact hDH (hPU hx)
  · rintro y ⟨x, hx, hxy⟩
    obtain ⟨q, hq, hqx⟩ := hPU hx
    have : q = y := Subtype.ext (hqx.trans hxy)
    exact le_of_lt (this ▸ hq)
  intro Sg M N hSg hM ψ hψ hSψ hgerm
  have hpre := hSg.isPreconnected
  have hMS : M ∈ Sg := hSg.left_mem
  have hNS : N ∈ Sg := hSg.right_mem
  have heq : EqOn ψ p Sg := eqOn_of_germ_eq_isDeveloping hψ hp hpre hSψ hMS hgerm
  have himgeq : ψ '' Sg = p '' Sg := image_congr heq
  refine ⟨himgeq ▸ hseg Sg M N hSg hM, fun hN hzN => ?_⟩
  obtain ⟨-, himg⟩ := hSg.image_eq hψ hSψ
  obtain ⟨m, hm, hmM⟩ := hPU hM
  have hmM' : (m : S n) = ψ M := hmM.trans (heq hMS).symm
  have hseg' : ψ '' Sg = (↑) '' affineSegment ℝ m ⟨ψ N, hN⟩ := by
    rw [himg, Sphere.coe_image_affineSegment, hmM']
  have hzseg : z '' affineSegment ℝ m ⟨ψ N, hN⟩ ⊆ Iio 1 := by
    rw [affineSegment_image, affineSegment_eq_segment]
    exact (convex_Iio 1).segment_subset hm hzN
  have hSU : Sg ⊆ p ⁻¹' demiEspace z := by
    intro y hy
    have : ψ y ∈ (↑) '' affineSegment ℝ m ⟨ψ N, hN⟩ := hseg' ▸ mem_image_of_mem ψ hy
    obtain ⟨q, hq, hqy⟩ := this
    show p y ∈ demiEspace z
    rw [← heq hy, ← hqy]
    exact ⟨q, hzseg (mem_image_of_mem z hq), rfl⟩
  have hsub : Sg ⊆ connectedComponentIn (p ⁻¹' demiEspace z) M :=
    hpre.subset_connectedComponentIn hMS hSU
  rw [← connectedComponentIn_eq hM] at hsub
  exact hsub hNS

/-- The open half-line `{x | x₀ > 0}` of `ℝ¹`, an open set of the model, hence a locally affine
1-manifold (Mathlib's `TopologicalSpace.Opens.instChartedSpace` and `instHasGroupoid`). -/
def demiDroiteOuverte : TopologicalSpace.Opens (Fin 1 → ℝ) :=
  ⟨{x | 0 < x 0}, isOpen_lt continuous_const (continuous_apply 0)⟩

/-- The inclusion `]0, ∞[ → ℝ¹` is a developing map (its jets are the jets of the charts). -/
theorem isDeveloping_val_demiDroiteOuverte :
    IsDeveloping (GAR 1) (Subtype.val : demiDroiteOuverte → Fin 1 → ℝ) := fun x =>
  ⟨chartAt (Fin 1 → ℝ) x, (gxGroupoid _ _).chart_mem_maximalAtlas x, mem_chart_source _ x, rfl⟩

/-- **A non-degenerate strict shell** (non-vacuity of Déf. 1, 2, 3 with a non-constant cote,
through the affine example): in the locally affine manifold `]0, ∞[ ⊂ ℝ¹`, the component
`P = ]0, 1[` of `z < 1`, `z = x₀`, with the inclusion as chart. -/
theorem exists_isCoqueStricteAff_demiDroite :
    ∃ (P : Set demiDroiteOuverte) (φ : OpenPartialHomeomorph demiDroiteOuverte (Fin 1 → ℝ)),
      IsCoqueStricteAff P φ (LinearMap.proj 0 : (Fin 1 → ℝ) →ₗ[ℝ] ℝ).toAffineMap ∧
      φ '' P = {x | 0 < x 0 ∧ x 0 < 1} := by
  set z : (Fin 1 → ℝ) →ᵃ[ℝ] ℝ := (LinearMap.proj 0 : (Fin 1 → ℝ) →ₗ[ℝ] ℝ).toAffineMap with hz
  let x₀ : demiDroiteOuverte := ⟨fun _ => 1 / 2, show (0 : ℝ) < 1 / 2 by norm_num⟩
  set U := (Subtype.val : demiDroiteOuverte → Fin 1 → ℝ) ⁻¹' {y | z y < 1} with hU
  have himgU : (Subtype.val '' U : Set (Fin 1 → ℝ)) = {x | 0 < x 0 ∧ x 0 < 1} := by
    ext y
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.2, hq⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨y, h1⟩, h2, rfl⟩
  have hC : Convex ℝ {x : Fin 1 → ℝ | 0 < x 0 ∧ x 0 < 1} :=
    (convex_Ioo (0 : ℝ) 1).linear_preimage
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)
  have hUconn : IsPreconnected U := by
    rw [← Topology.IsInducing.subtypeVal.isPreconnected_image]
    convert hC.isPreconnected using 1
    ext y
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.2, hq⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨y, h1⟩, h2, rfl⟩
  have hx₀ : z (x₀ : Fin 1 → ℝ) < 1 := show (1 / 2 : ℝ) < 1 by norm_num
  have hP : connectedComponentIn U x₀ = U := hUconn.connectedComponentIn hx₀
  have hinf : IsGLB (z '' (Subtype.val '' connectedComponentIn U x₀)) 0 := by
    rw [hP, himgU]
    have : z '' {x : Fin 1 → ℝ | 0 < x 0 ∧ x 0 < 1} = Ioo 0 1 := by
      ext t
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro ht
        exact ⟨fun _ => t, ht, rfl⟩
    rw [this]
    exact isGLB_Ioo zero_lt_one
  obtain ⟨φ, hφeq, hφ⟩ := exemple_poche_affine isDeveloping_val_demiDroiteOuverte z hx₀ hinf
    Subtype.val_injective.injOn
  have hφimg : φ '' connectedComponentIn U x₀ = {x | 0 < x 0 ∧ x 0 < 1} := by
    rw [image_congr hφeq, hP, himgU]
  refine ⟨_, φ, ⟨⟨hφ, by rw [hφimg]; exact hC⟩, ?_⟩, hφimg⟩
  rintro ⟨A, ⟨p, w, hw, rfl⟩, hA⟩
  rw [hφimg] at hA
  have hw0 : w 0 ≠ 0 := fun h => hw (funext fun i => by rw [Subsingleton.elim i 0]; exact h)
  have h2 := (hA ⟨(2 - p 0) / w 0, rfl⟩).2
  simp only [vadd_eq_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hw0] at h2
  linarith

/-- **A non-degenerate projective strict shell** (non-vacuity of Déf. 1′, 2, 3 in the projective
case, with a non-constant cote): the image, by the Remarque after Déf. 1′, of the affine strict shell
`]0, 1[ ⊂ ]0, ∞[` of `exists_isCoqueStricteAff_demiDroite`, over the hemisphere `H₀ = {x₂ > 0}`. -/
theorem exists_isCoqueStricteProj_demiDroite :
    ∃ (P : Set demiDroiteOuverte) (φ : OpenPartialHomeomorph demiDroiteOuverte (S 1))
      (z : Sphere.openHemisphere (Sphere.lastForm 1) →ᵃ[ℝ] ℝ),
      @IsCoqueStricteProj 1 demiDroiteOuverte _ (projOfAff 1 demiDroiteOuverte) P
        (Sphere.lastForm 1) _ φ z := by
  obtain ⟨P, φ, h, -⟩ := exists_isCoqueStricteAff_demiDroite
  obtain ⟨e⟩ := Sphere.nonempty_hemi_affineEquiv (l := Sphere.lastForm 1) (Module.finrank_fin_fun ℝ)
  exact ⟨P, _, _, h.toCoqueStricteProj e.symm⟩

end Exemples

end Benzecri
