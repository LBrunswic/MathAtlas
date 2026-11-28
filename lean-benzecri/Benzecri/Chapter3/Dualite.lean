import Benzecri.Projective.Convex
import Benzecri.Chapter2.Poches
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.StrongTopology
import Mathlib.Topology.Algebra.Module.PerfectPairing
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# `Benzecri.Chapter3.Dualite` — the duality `D`, `D′` of convex parts of `S(E)`, `S(E′)` (Ch. 3 § 3, Props. 1–5)

J.-P. Benzécri, Bull. SMF 88 (1960), Chapter 3 § 3 « Dualité des corps convexes », journal
pp. 268–270; transcription `papers/benzecri/legacy/labeled/benzecri1960_ch3.tex` (TO BE CHECKED BY
THE AUTHOR, OQ-160). Target T-bz-c3-dualite.

* `bzprop:c3s3p1_dualite_biunivoque` — `benzecri1960_ch3.tex:685` (Prop. 1). Not marked (a
  hypothesis reading, and a finding): `Benzecri.Sphere.prop1` under the hypotheses of (d) (`HypD`:
  claim (c) for `E` and for `E′`), `Benzecri.Sphere.dualiteEquiv`;
  `Benzecri.Sphere.prop1_semiReflexive` for `E` semi-reflexive and `E′ = E′_β` its strong dual;
  `Benzecri.Sphere.prop1_fails_zeroForm` (the degenerate duality). See SCOPE.
* `bzprop:c3s3p2_dual_fermeture` — `benzecri1960_ch3.tex:698` (Prop. 2). Not marked: 1°
  (`D_closure`) is certified under less than (b); 2° (`prop2_2`, through `D'_D_eq_closure`) rests on
  the same unruled reading of « les hypothèses de (d) » as Prop. 1 (`HypD`; only (c) for `E` is
  used). `Benzecri.Sphere.prop2` gathers both. See SCOPE.
* **`bzprop:c3s3p3_hemispheres_points`** — `benzecri1960_ch3.tex:715` (Prop. 3):
  `Benzecri.Sphere.prop3`, for every real topological vector space `E`, closed hemispheres in
  Ch. 1 Déf. 5's sense read under DEC-114 (`IsClosedHemisphere`, the closure of a nonempty open
  hemisphere).
* `bzprop:c3s3p4_dual_geometrique` — `benzecri1960_ch3.tex:734` (Prop. 4). Not marked (a reading:
  the printed « $D(\{M'\})$ » is ill-typed, read `D′({M′})`): `Benzecri.Sphere.prop4`,
  `Benzecri.Sphere.prop4_eq`.
* **`bzprop:c3s3p5_dual_variete_lineaire`** — `benzecri1960_ch3.tex:741` (Prop. 5):
  `Benzecri.Sphere.prop5`, `Benzecri.Sphere.D_linearSubvariety` (`D(s(L - O)) = s(L^⊥ - O)`).
* The claims (a)–(c), no ledger row (OQ-160 (c)), as lemmas: `claim_a_cone`, `claim_a_convexPart`,
  `claim_a_antitone` (l.639–654); `claim_b`, `claim_b'` (l.656–662); `claim_c` (l.664–681), from
  Mathlib's geometric Hahn–Banach (`exists_dual_sep`).
* The instance (l.751–755): `ℝⁿ⁺¹` with the dot product, `dotPairing`, meets every hypothesis
  (`hypD_dotPairing`, `isSemiReflexive_Rn`); on `S(n)`, `D = D′` is an involutive bijection of
  `C(S(n))` (`dotPairing_prop1`), the `D` of a point is a closed hemisphere (`dotPairing_D_point`)
  and the `D` of a closed hemisphere is a point (`dotPairing_D_closedHemisphere`).

> *a*. Soient $E$, $E'$ deux espaces vectoriels. Supposons définie sur $E\times E'$ une forme
> bilinéaire […] $D(W)=s\{m'\mid\langle m, m'\rangle\geqq 0,\ \forall m\in F(W);\ m'\neq 0\}$. […]
> Il est clair que $F\circ D(W)$ est un cône convexe de sommet origine dans $E'$ […]
> Soit $W_1\subset W_2$ deux éléments de $K(S(E))$; on a $D(W_2)\subset D(W_1)$.
>
> *b*. Supposons maintenant que $E$ (resp. $E'$) soit muni d'une topologie localement convexe
> séparée et que la forme bilinéaire […] soit séparément continue en chacune des variables. […]
> $D$ envoie $C(S(E))$ dans $C(S(E'))$ et, de même, $D'$ envoie $C(S(E'))$ dans $C(S(E))$.
>
> *c*. […] supposons de plus que la forme bilinéaire définie sur $E\times E'$ permette
> d'identifier $E'$ à l'ensemble des formes linéaires continues sur l'espace vectoriel topologique
> $E$. Alors $D'\circ D$ induit l'identité sur $C(S(E))$.
>
> **Proposition 1.** Soient $E$, $E'$ deux espaces vectoriels topologiques semi-réflexifs mis en
> dualité par une application bilinéaire notée $\langle m, m'\rangle$, $m\in E$, $m'\in E'$. la
> correspondance $D$ définie en (*a*) est une application biunivoque de $C(S(E))$ sur
> $C(S(E'))$, et $D'$ est l'application réciproque.
>
> **Proposition 2.** 1° Sous les hypothèses de (*b*), on a $D(W)=D(\overline{W})$;
> 2° Sous les hypothèses de (*d*), on a $D'\circ D(W)=\overline{W}$.
>
> **Proposition 3.** Soient $E$ un espace vectoriel topologique, $E'$ l'espace vectoriel des formes
> linéaires continues sur $E$, $\langle M, M'\rangle$ la forme bilinéaire sur $E\times E'$ qui à
> $M'\in E'$, $M\in E$ associe la valeur sur $M$ de la forme linéaire $M'$. $D'$ met en
> correspondance biunivoque les hémisphères fermés de $S(E)$ et les points de $S(E')$.
>
> **Proposition 4.** Supposons vérifiées les hypothèses de (*d*) : soit $W\in C(S(E))$ : $D(W)$
> n'est autre que l'ensemble des points $M'$ de $S(E')$ tels que $W$ soit contenu dans l'hémisphère
> fermé $D(\{M'\})$.
>
> **Proposition 5.** Plaçons-nous sous les hypothèses de (*a*) : Soit $W$ une variété linéaire;
> alors $D$ est une variété linéaire.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| (a) `E`, `E′` real vector spaces, `⟨·,·⟩` bilinear | ✓ carried (`B : E →ₗ[ℝ] E' →ₗ[ℝ] ℝ`); `D`, `D′` defined on every part, not only on `K(S(E))` |
| (a) `W ∈ K(S(E))` in the claims | ⚠ weakened: `claim_a_*` hold for every part `W` |
| (b) `E`, `E′` locally convex Hausdorff, form separately continuous | ⚠ weakened: `claim_b` needs only `m′ ↦ ⟨m, m′⟩` continuous, no other hypothesis on `E`, `E′`; Prop. 2 1° needs only `m ↦ ⟨m, m′⟩` continuous and `E` with continuous homotheties |
| (c) the form identifies `E′` with the continuous dual of `E` | ✓ carried as `IdentifiesDual` (continuity of `⟨·, m′⟩` and `∃!`); `claim_c` assumes (b) only on `E` (locally convex, `T1`, i.e. Hausdorff for a topological group) |
| (d): « les hypothèses de (d) », i.e. Prop. 1's « semi-réflexifs mis en dualité » | ⚠ read (unruled, OQ-160) as `HypD` = (c) for `E` and for `E′`, the dual-pair reading the proofs use; Prop. 2 2° and Prop. 4 use (c) for `E` only |
| Prop. 1: « semi-réflexifs mis en dualité » | ⚠ strengthened (a reading, and a finding): `prop1` under `HypD`; `prop1_semiReflexive` for `E` semi-reflexive (`IsSemiReflexive`, Bourbaki's definition) and `E′` its strong dual; under the reading « separating, separately continuous form between semi-reflexive spaces with their own topologies » it fails (ℓ², SCOPE) |
| Prop. 2: `W ∈ K(S(E))` | ⚠ weakened for 1° (every part `W`); ✓ carried for 2° (`W` convex) |
| Prop. 2 2°: « Sous les hypothèses de (d) » | ⚠ read as `HypD` (row (d) above); under the separating-form reading it fails on the ℓ² example (SCOPE) |
| Prop. 3: `E` a topological vector space | ✓ carried (`IsTopologicalAddGroup`, `ContinuousSMul ℝ`), no separation axiom |
| Prop. 3: « hémisphère fermé » | reading (DEC-114, accepted by DEC-120): the closure of a nonempty open hemisphere of Déf. 5 |
| Prop. 4: (d) and `W ∈ C(S(E))` | ⚠ weakened: the description `prop4_eq` holds for every form and every part; that `D′({M′})` is a closed hemisphere uses (c) for `E` only |
| Prop. 4: « $D(\{M'\})$ » | reading: `D′({M′})` (the printed `D` applies to parts of `S(E)`, `M′ ∈ S(E′)`; scan p. 270 prints `D` without prime) |
| Prop. 5: (a), `W` a linear variety (Déf. 4) | ✓ carried; « alors D » read `D(W)` per the transcription's `[sic]` |

## SCOPE (disclosed)

* **Prop. 1 is not marked.** Its proof (« Cela résulte de la » Prop. 2) uses claim (c) for `E` and
  for `E′`, i.e. each space is the topological dual of the other through the form: `prop1` is
  stated under that dual-pair reading (`HypD`), and `prop1_semiReflexive` proves the reading
  « `E` semi-reflexive, `E′ = E′_β` its strong dual », with semi-reflexivity defined after Bourbaki
  (`IsSemiReflexive`; Mathlib has no such notion), satisfied by every finite-dimensional Hausdorff
  space (`isSemiReflexive_of_finiteDimensional`). Under the other reading, « a separating,
  separately continuous form between semi-reflexive spaces carrying their own topologies », Prop. 1
  fails (argued on paper, not formalized): on `ℓ²` (reflexive), `⟨x, y⟩ = (x | Ty)` with
  `T = diag(1/n)` (injective, self-adjoint, dense non-closed range) is separating and jointly
  continuous; for `z = (1/n) ∉ T(ℓ²)` and `W` the closed hemisphere `{(x | z) ≥ 0}`,
  `D(W) = s{y ≠ 0 | Ty ∈ ℝ₊z} = ∅ = D(S(ℓ²))` with `W ≠ S(ℓ²)`, both in `C(S(ℓ²))`. No
  finite-dimensional counterexample exists (a separating form is then perfect). The zero form
  (`prop1_fails_zeroForm`) refutes only a degenerate « dualité », which Bourbaki's definition
  contemporary with the paper probably excludes: it is a remark, not a refutation of the paper.
* **Prop. 2 is not marked.** 1° (`D_closure`) is certified for every part `W`, under less than (b).
  2° is stated under `HypD`, the same unruled reading of « les hypothèses de (d) » (OQ-160); under
  the separating-form reading it fails on the same ℓ² example: `D′(D(W)) = D′(∅) = S(ℓ²) ≠ W = W̄`.
* **Prop. 4 is not marked**: a reading of an ill-typed printed formula (`D` for `D′`). Under the
  reading it holds for every form and every part `W` (`prop4_eq`); no proof is printed.
* `D′` is `D` of the flipped form (`D'`), so every statement about `D` has its `D′` twin.
* `IsClosedHemisphere`, `continuous_of_isOpen_of_F_eq'`, `closure_openHemisphere'`, `isOpen_ofCone'`
  are general `Projective/Subvariety` facts proved here without `T1Space E` (the strict
  library's versions assume it); they may move upstream at graduation.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Topology Filter

namespace Benzecri

namespace Sphere

variable {E E' : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup E'] [Module ℝ E']

/-! ### (a) — the definition of `D` and `D′` -/

/-- The dual cone `{m′ | ⟨m, m′⟩ ≥ 0, ∀ m ∈ C}` of a part `C ⊆ E` for the form `B`. -/
def dualCone (B : E →ₗ[ℝ] E' →ₗ[ℝ] ℝ) (C : Set E) : Set E' := {m' | ∀ m ∈ C, 0 ≤ B m m'}

/-- **Benzécri's `D`** (§ 3 (a)): `D(W) = s{m′ | ⟨m, m′⟩ ≥ 0, ∀ m ∈ F(W); m′ ≠ 0}`. -/
def D (B : E →ₗ[ℝ] E' →ₗ[ℝ] ℝ) (W : Set (Sphere E)) : Set (Sphere E') :=
  ofCone (dualCone B (F W))

/-- **Benzécri's `D′`** (§ 3 (a)): `D′(W′) = s{m | ⟨m, m′⟩ ≥ 0, ∀ m′ ∈ F(W′); m ≠ 0}`, the `D` of
the flipped form. -/
def D' (B : E →ₗ[ℝ] E' →ₗ[ℝ] ℝ) (W' : Set (Sphere E')) : Set (Sphere E) := D B.flip W'

theorem isPosCone_dualCone (B : E →ₗ[ℝ] E' →ₗ[ℝ] ℝ) (C : Set E) : IsPosCone (dualCone B C) := by
  intro c hc v hv m hm
  have := hv m hm
  simp only [map_smul, smul_eq_mul]
  positivity

theorem zero_mem_dualCone (B : E →ₗ[ℝ] E' →ₗ[ℝ] ℝ) (C : Set E) : (0 : E') ∈ dualCone B C :=
  fun m _ => by simp

theorem convex_dualCone (B : E →ₗ[ℝ] E' →ₗ[ℝ] ℝ) (C : Set E) : Convex ℝ (dualCone B C) := by
  intro x hx y hy a b ha hb _ m hm
  simp only [map_add, map_smul, smul_eq_mul]
  have := hx m hm
  have := hy m hm
  positivity

theorem F_D (B : E →ₗ[ℝ] E' →ₗ[ℝ] ℝ) (W : Set (Sphere E)) :
    F (D B W) = dualCone B (F W) \ {0} :=
  F_ofCone (isPosCone_dualCone B _)

theorem mk_mem_D (B : E →ₗ[ℝ] E' →ₗ[ℝ] ℝ) (W : Set (Sphere E)) {v : E'} (hv : v ≠ 0) :
    mk v hv ∈ D B W ↔ ∀ m ∈ F W, 0 ≤ B m v :=
  mk_mem_ofCone_iff (isPosCone_dualCone B _) hv

theorem mk_mem_D' (B : E →ₗ[ℝ] E' →ₗ[ℝ] ℝ) (W' : Set (Sphere E')) {v : E} (hv : v ≠ 0) :
    mk v hv ∈ D' B W' ↔ ∀ m' ∈ F W', 0 ≤ B v m' :=
  mk_mem_D B.flip W' hv

theorem D_flip_flip (B : E →ₗ[ℝ] E' →ₗ[ℝ] ℝ) : D' B.flip = D B := by
  funext W
  simp only [D', LinearMap.flip_flip]

/-- **Claim (a)**, first sentence (p. 269, « Il est clair que $F\circ D(W)$ est un cône convexe de
sommet origine dans $E'$ »): `F(D(W)) ∪ {O}` is the dual cone of `F(W)`, a convex cone of vertex the
origin. -/
theorem claim_a_cone (B : E →ₗ[ℝ] E' →ₗ[ℝ] ℝ) (W : Set (Sphere E)) :
    insert 0 (F (D B W)) = dualCone B (F W) ∧ Convex ℝ (insert 0 (F (D B W))) ∧
      IsPosCone (insert 0 (F (D B W))) := by
  have h : insert 0 (F (D B W)) = dualCone B (F W) := by
    rw [D, insert_zero_F_ofCone (isPosCone_dualCone B _)]
    exact insert_eq_of_mem (zero_mem_dualCone B _)
  refine ⟨h, ?_, ?_⟩
  · rw [h]; exact convex_dualCone B _
  · rw [h]; exact isPosCone_dualCone B _

/-- **Claim (a)**, second sentence (« l'on a bien défini une application de $K(S(E))$ dans
$K(S(E'))$ »): `D(W)` is a convex part, for every part `W` (not only `W ∈ K(S(E))`). -/
theorem claim_a_convexPart (B : E →ₗ[ℝ] E' →ₗ[ℝ] ℝ) (W : Set (Sphere E)) :
    D B W ∈ KS E' := by
  show IsConvexPart (D B W)
  exact (claim_a_cone B W).2.1

theorem claim_a_mapsTo (B : E →ₗ[ℝ] E' →ₗ[ℝ] ℝ) : MapsTo (D B) (KS E) (KS E') :=
  fun W _ => claim_a_convexPart B W

/-- **Claim (a)**, third sentence (« Soit $W_1\subset W_2$ … on a $D(W_2)\subset D(W_1)$ »). -/
theorem claim_a_antitone (B : E →ₗ[ℝ] E' →ₗ[ℝ] ℝ) {W₁ W₂ : Set (Sphere E)} (h : W₁ ⊆ W₂) :
    D B W₂ ⊆ D B W₁ :=
  ofCone_subset_ofCone fun _ hv m hm => hv m (F_mono h hm)

/-- Every part is contained in its bidual: `W ⊆ D′(D(W))`. -/
theorem subset_D'_D (B : E →ₗ[ℝ] E' →ₗ[ℝ] ℝ) (W : Set (Sphere E)) : W ⊆ D' B (D B W) := by
  intro x hx
  induction x using ind with
  | h v hv =>
    rw [mk_mem_D']
    intro m' hm'
    rw [F_D] at hm'
    exact hm'.1 v ⟨hv, hx⟩

/-! ### (b) — closedness -/

section ClaimB

variable [TopologicalSpace E']

theorem isClosed_iff_F_preimage {A : Set (Sphere E')} :
    IsClosed A ↔ IsClosed (Subtype.val ⁻¹' F A : Set {v : E' // v ≠ 0}) := by
  rw [← s_preimage_eq]
  exact isClosed_coinduced

/-- **Claim (b)** for one part: `D(W)` is closed as soon as each `m′ ↦ ⟨m, m′⟩` is continuous
(no hypothesis on `W`). -/
theorem isClosed_D (B : E →ₗ[ℝ] E' →ₗ[ℝ] ℝ) (hB : ∀ m, Continuous (B m)) (W : Set (Sphere E)) :
    IsClosed (D B W) := by
  rw [isClosed_iff_F_preimage, F_D]
  have hC : IsClosed (dualCone B (F W)) := by
    have : dualCone B (F W) = ⋂ m ∈ F W, {m' | 0 ≤ B m m'} := by
      ext; simp [dualCone]
    rw [this]
    exact isClosed_biInter fun m _ => isClosed_le continuous_const (hB m)
  have : (Subtype.val ⁻¹' (dualCone B (F W) \ {0}) : Set {v : E' // v ≠ 0}) =
      Subtype.val ⁻¹' dualCone B (F W) := by
    ext ⟨v, hv⟩; simp [hv]
  rw [this]
  exact hC.preimage continuous_subtype_val

/-- **Claim (b)** (p. 269, « $D$ envoie $C(S(E))$ dans $C(S(E'))$ »), under separate continuity in
the second variable only. -/
theorem claim_b [TopologicalSpace E] (B : E →ₗ[ℝ] E' →ₗ[ℝ] ℝ) (hB : ∀ m, Continuous (B m)) :
    MapsTo (D B) (CS E) (CS E') :=
  fun W _ => ⟨claim_a_convexPart B W, isClosed_D B hB W⟩

end ClaimB

theorem claim_b' [TopologicalSpace E] [TopologicalSpace E'] (B : E →ₗ[ℝ] E' →ₗ[ℝ] ℝ)
    (hB : ∀ m', Continuous fun m => B m m') : MapsTo (D' B) (CS E') (CS E) :=
  claim_b B.flip hB

/-! ### Closure in `S(E)`: `F(Ā) = closure(F(A)) - {O}` is the strict library's
`Benzecri.Sphere.F_closure` (`Chapter2/Poches`). -/

/-! ### The separation lemma (Bourbaki EVT II § 3, cor. 1 of prop. 4) -/

section Separation

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E]

/-- A closed convex cone `K` (containing `O`) is the intersection of the closed half-spaces
`{f ≥ 0}` limited by a hyperplane through the origin that contain it: a point `v ∉ K` is separated
by a continuous form `f ≥ 0` on `K` with `f v < 0`. From Mathlib's geometric Hahn–Banach
(`geometric_hahn_banach_point_closed`), by the homothety argument of the paper's bracket. -/
theorem exists_dual_sep {K : Set E} (hKc : Convex ℝ K) (hKcl : IsClosed K) (hK0 : (0 : E) ∈ K)
    (hKpos : IsPosCone K) {v : E} (hv : v ∉ K) :
    ∃ f : StrongDual ℝ E, (∀ x ∈ K, 0 ≤ f x) ∧ f v < 0 := by
  obtain ⟨f, u, hfu, hK⟩ := geometric_hahn_banach_point_closed hKc hKcl hv
  have hu : u < 0 := by simpa using hK 0 hK0
  refine ⟨f, fun x hx => ?_, hfu.trans hu⟩
  by_contra! hneg
  have ht : 0 < u / f x := div_pos_of_neg_of_neg hu hneg
  have := hK _ (hKpos _ ht x hx)
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ u hneg.ne] at this
  exact lt_irrefl _ this

end Separation

/-! ### Hypotheses (b), (c), (d) on the form -/

/-- **Hypothesis (c)** on the form (p. 269): `x ↦ ⟨x, m′⟩` is continuous for every `m′` (part of
(b)), and the form identifies `E′` with the continuous linear forms on `E`: every continuous linear
form is `⟨·, m′⟩` for exactly one `m′`. -/
def IdentifiesDual [TopologicalSpace E] (B : E →ₗ[ℝ] E' →ₗ[ℝ] ℝ) : Prop :=
  (∀ m' : E', Continuous fun m : E => B m m') ∧
    ∀ f : StrongDual ℝ E, ∃! m' : E', ∀ m : E, B m m' = f m

/-- **The hypotheses of (d)** on the form: (c) for `E` and for `E′` (« les hypothèses de (d) »,
Prop. 2 2°, Prop. 4). It contains (b)'s separate continuity in both variables. -/
def HypD [TopologicalSpace E] [TopologicalSpace E'] (B : E →ₗ[ℝ] E' →ₗ[ℝ] ℝ) : Prop :=
  IdentifiesDual B ∧ IdentifiesDual B.flip

/-- A continuous perfect pairing (Mathlib's `IsContPerfPair`) satisfies hypothesis (c). -/
theorem identifiesDual_of_isContPerfPair [TopologicalSpace E] [TopologicalSpace E']
    (B : E →ₗ[ℝ] E' →ₗ[ℝ] ℝ) [B.IsContPerfPair] : IdentifiesDual B := by
  have hc : ∀ m', Continuous fun m => B m m' := fun m' =>
    B.continuous_uncurry_of_isContPerfPair.comp (continuous_id.prodMk continuous_const)
  refine ⟨hc, fun f => ?_⟩
  obtain ⟨y, hy⟩ := (LinearMap.IsContPerfPair.bijective_right B).2 f
  refine ⟨y, fun m => congrArg (fun g : StrongDual ℝ E => g m) hy, fun y' hy' => ?_⟩
  apply (LinearMap.IsContPerfPair.bijective_right B).1
  rw [hy]
  ext m
  exact hy' m

/-- Mathlib's continuous perfect pairings satisfy the hypotheses of (d). -/
theorem hypD_of_isContPerfPair [TopologicalSpace E] [TopologicalSpace E']
    (B : E →ₗ[ℝ] E' →ₗ[ℝ] ℝ) [B.IsContPerfPair] : HypD B :=
  ⟨identifiesDual_of_isContPerfPair B, identifiesDual_of_isContPerfPair B.flip⟩

/-! ### Prop. 2 1° and the key bidual identity -/

/-- **Prop. 2, 1°** (`bzprop:c3s3p2_dual_fermeture`, p. 269): `D(W) = D(W̄)`, for every part `W`,
as soon as each `x ↦ ⟨x, m′⟩` is continuous. -/
theorem D_closure [TopologicalSpace E] [ContinuousConstSMul ℝ E] (B : E →ₗ[ℝ] E' →ₗ[ℝ] ℝ)
    (hB : ∀ m', Continuous fun m => B m m') (W : Set (Sphere E)) : D B (closure W) = D B W := by
  apply (claim_a_antitone B subset_closure).antisymm
  intro x hx
  induction x using ind with
  | h v hv =>
    rw [mk_mem_D] at hx ⊢
    intro m hm
    rw [F_closure] at hm
    have hcl : IsClosed {x : E | 0 ≤ B x v} := isClosed_le continuous_const (hB v)
    exact closure_minimal hx hcl hm.1

section Bidual

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T1Space E]

/-- **The bidual of a convex part is its closure** (Prop. 2 2°, through claim (c)): under (c),
`D′(D(W)) = W̄` for every convex part `W ∈ K(S(E))`. -/
theorem D'_D_eq_closure (B : E →ₗ[ℝ] E' →ₗ[ℝ] ℝ) (hB : IdentifiesDual B) {W : Set (Sphere E)}
    (hW : IsConvexPart W) : D' B (D B W) = closure W := by
  apply Subset.antisymm
  · intro x hx
    by_contra hxW
    induction x using ind with
    | h v hv =>
      set K : Set E := closure (insert 0 (F W)) with hKdef
      have hKc : Convex ℝ K := hW.closure
      have hK0 : (0 : E) ∈ K := subset_closure (mem_insert _ _)
      have hKpos : IsPosCone K := by
        intro c hc x hx
        exact map_mem_closure (continuous_const_smul c) hx
          (fun y hy => isPosCone_insert_zero (isPosCone_F W) c hc y hy)
      have hvK : v ∉ K := by
        intro hvK
        rw [hKdef, insert_eq, closure_union, isClosed_singleton.closure_eq] at hvK
        rcases hvK with h0 | hvF
        · exact hv h0
        · apply hxW
          rw [mk_mem_iff_mem_F, F_closure]
          exact ⟨hvF, hv⟩
      obtain ⟨f, hfK, hfv⟩ := exists_dual_sep hKc isClosed_closure hK0 hKpos hvK
      obtain ⟨m', hm', -⟩ := hB.2 f
      have hm'0 : m' ≠ 0 := by
        rintro rfl
        have := hm' v
        simp at this
        linarith
      have hmem : mk m' hm'0 ∈ D B W := by
        rw [mk_mem_D]
        intro m hm
        rw [hm' m]
        exact hfK m (subset_closure (mem_insert_of_mem _ hm))
      rw [mk_mem_D'] at hx
      have := hx m' ((mk_mem_iff_mem_F hm'0).1 hmem)
      rw [hm' v] at this
      linarith
  · exact closure_minimal (subset_D'_D B W) (isClosed_D B.flip hB.1 _)

/-- **Claim (c)** (p. 269, « Alors $D'\circ D$ induit l'identité sur $C(S(E))$ »). -/
theorem claim_c (B : E →ₗ[ℝ] E' →ₗ[ℝ] ℝ) (hB : IdentifiesDual B) {W : Set (Sphere E)}
    (hW : W ∈ CS E) : D' B (D B W) = W := by
  rw [D'_D_eq_closure B hB hW.1, hW.2.closure_eq]

/-- **Prop. 2, 2°** (`bzprop:c3s3p2_dual_fermeture`): under the hypotheses of (d),
`D′∘D(W) = W̄` for `W ∈ K(S(E))`. Only (c) for `E` is used. -/
theorem prop2_2 [TopologicalSpace E'] (B : E →ₗ[ℝ] E' →ₗ[ℝ] ℝ) (hB : HypD B)
    {W : Set (Sphere E)} (hW : W ∈ KS E) : D' B (D B W) = closure W :=
  D'_D_eq_closure B hB.1 hW

end Bidual

/-- **Prop. 2** (`bzprop:c3s3p2_dual_fermeture`), both parts. -/
theorem prop2 [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] [T1Space E] [TopologicalSpace E'] (B : E →ₗ[ℝ] E' →ₗ[ℝ] ℝ) :
    ((∀ m', Continuous fun m => B m m') → ∀ W : Set (Sphere E), D B W = D B (closure W)) ∧
      (HypD B → ∀ W ∈ KS E, D' B (D B W) = closure W) :=
  ⟨fun hB W => (D_closure B hB W).symm, fun hB _ hW => prop2_2 B hB hW⟩

/-! ### Prop. 1 -/

section Prop1

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T1Space E]
  [TopologicalSpace E'] [IsTopologicalAddGroup E'] [ContinuousSMul ℝ E']
  [LocallyConvexSpace ℝ E'] [T1Space E']

/-- **Prop. 1** (`bzprop:c3s3p1_dualite_biunivoque`, p. 269), under the hypotheses of (d): `D` is a
bijection of `C(S(E))` onto `C(S(E′))`, and `D′` is its inverse. -/
theorem prop1 (B : E →ₗ[ℝ] E' →ₗ[ℝ] ℝ) (hB : HypD B) :
    BijOn (D B) (CS E) (CS E') ∧ InvOn (D' B) (D B) (CS E) (CS E') := by
  have hDD' : ∀ W' ∈ CS E', D B (D' B W') = W' := by
    intro W' hW'
    have := claim_c B.flip hB.2 hW'
    rwa [D_flip_flip] at this
  have hinv : InvOn (D' B) (D B) (CS E) (CS E') :=
    ⟨fun W hW => claim_c B hB.1 hW, hDD'⟩
  refine ⟨hinv.bijOn (claim_b B hB.2.1) (claim_b' B hB.1.1), hinv⟩

/-- Prop. 1 as an equivalence `C(S(E)) ≃ C(S(E′))`, `D` forward and `D′` backward. -/
def dualiteEquiv (B : E →ₗ[ℝ] E' →ₗ[ℝ] ℝ) (hB : HypD B) : CS E ≃ CS E' where
  toFun W := ⟨D B W, claim_b B hB.2.1 W.2⟩
  invFun W' := ⟨D' B W', claim_b' B hB.1.1 W'.2⟩
  left_inv W := Subtype.ext ((prop1 B hB).2.1 W.2)
  right_inv W' := Subtype.ext ((prop1 B hB).2.2 W'.2)

end Prop1

/-- **Remark: Prop. 1's conclusion needs a non-degenerate duality.** For the zero form on `ℝ × ℝ`
(`ℝ` is reflexive), `D` is constant on `C(S(ℝ))`, which has two distinct elements `∅` and `S(ℝ)`.
This refutes Prop. 1 only if « mis en dualité » admits a degenerate form, which the Bourbaki of the
period probably excludes; it is not a refutation of the paper (see SCOPE for the ℓ² example). -/
theorem prop1_fails_zeroForm : ¬ InjOn (D (0 : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ)) (CS ℝ) := by
  intro h
  have hD : ∀ W, D (0 : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ) W = univ := by
    intro W
    ext x
    induction x using ind with
    | h v hv => simp [mk_mem_D]
  have h0 : (∅ : Set (Sphere ℝ)) ∈ CS ℝ := by
    refine ⟨?_, isClosed_empty⟩
    show Convex ℝ (insert 0 (F (∅ : Set (Sphere ℝ))))
    simp
  have h1 : (univ : Set (Sphere ℝ)) ∈ CS ℝ := by
    refine ⟨?_, isClosed_univ⟩
    show Convex ℝ (insert 0 (F (univ : Set (Sphere ℝ))))
    have : insert (0 : ℝ) ({0}ᶜ : Set ℝ) = univ := by
      ext x; by_cases hx : x = 0 <;> simp [hx]
    rw [F_univ, this]
    exact convex_univ
  have heq := h h0 h1 (by rw [hD, hD])
  have hm : mk (1 : ℝ) one_ne_zero ∈ (univ : Set (Sphere ℝ)) := trivial
  rw [← heq] at hm
  exact hm

/-! ### Closed hemispheres (Déf. 5, read under DEC-114: nonempty) -/

section Hemisphere

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- A **closed hemisphere** of `S(E)` (Ch. 1 Déf. 5, « La fermeture $H\cup h$ de $H$ est appelée
hémisphère fermé »): the closure of an open hemisphere, nonempty under DEC-114's reading `l ≠ 0`. -/
def IsClosedHemisphere (W : Set (Sphere E)) : Prop :=
  ∃ H : Set (Sphere E), IsOpenHemisphere H ∧ H.Nonempty ∧ closure H = W

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
theorem isOpen_ofCone' {C : Set E} (hC : IsPosCone C) (hCo : IsOpen C) : IsOpen (ofCone C) := by
  rw [isOpen_iff, s_preimage_eq, F_ofCone hC]
  have : (Subtype.val ⁻¹' (C \ {0}) : Set {v : E // v ≠ 0}) = Subtype.val ⁻¹' C := by
    ext ⟨v, hv⟩; simp [hv]
  rw [this]
  exact hCo.preimage continuous_subtype_val

/-- The equation of a nonempty open hemisphere is continuous, without assuming `{O}` closed
(compare `continuous_of_isOpen_of_F_eq`, which assumes `T1Space E`). -/
theorem continuous_of_isOpen_of_F_eq' {H : Set (Sphere E)} (hH : IsOpen H) {l : Module.Dual ℝ E}
    (hF : F H = l ⁻¹' Ioi 0) (hl : l ≠ 0) : Continuous l := by
  have hpre : IsOpen (s ⁻¹' H) := isOpen_iff.1 hH
  obtain ⟨U, hU, hUeq⟩ := isOpen_induced_iff.1 hpre
  have hmem : ∀ v (hv : v ≠ 0), v ∈ U ↔ 0 < l v := by
    intro v hv
    have h1 : v ∈ U ↔ (⟨v, hv⟩ : {v : E // v ≠ 0}) ∈ s ⁻¹' H := by rw [← hUeq]; rfl
    rw [h1, mem_preimage, s_apply, mk_mem_iff_mem_F, hF]
    rfl
  obtain ⟨u, hu⟩ := exists_pos_of_ne_zero hl
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  have h0 : (0 : E) ∉ U := by
    intro h0
    have hcont : Continuous fun t : ℝ => t • (-u) := continuous_id.smul continuous_const
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t • (-u) ∈ U := by
      have : Tendsto (fun t : ℝ => t • (-u)) (𝓝 0) (𝓝 0) := by
        simpa using hcont.tendsto 0
      exact (this.mono_left nhdsWithin_le_nhds).eventually (hU.mem_nhds h0)
    obtain ⟨t, htU, ht⟩ := (hev.and self_mem_nhdsWithin).exists
    have ht' : (0 : ℝ) < t := ht
    have ht0 : t • (-u) ≠ 0 := smul_ne_zero ht'.ne' (neg_ne_zero.2 hu0)
    have := (hmem _ ht0).1 htU
    simp only [map_smul, map_neg, smul_eq_mul, mul_neg] at this
    nlinarith
  refine l.continuous_of_nonzero_on_open U hU ⟨u, (hmem u hu0).2 hu⟩ fun v hv => ?_
  have hv0 : v ≠ 0 := by rintro rfl; exact h0 hv
  exact ((hmem v hv0).1 hv).ne'

theorem closure_openHemisphere' {l : StrongDual ℝ E} (hl : l ≠ 0) :
    closure (openHemisphere (l : Module.Dual ℝ E)) = closedHemisphere (l : Module.Dual ℝ E) := by
  apply F_injective
  rw [F_closure, F_openHemisphere, closedHemisphere, F_ofCone (isPosCone_nonneg _)]
  have := closure_pos_eq_nonneg (E := E) hl
  have h1 : ((l : Module.Dual ℝ E) : E → ℝ) ⁻¹' Ioi 0 = {v | 0 < l v} := rfl
  have h2 : {v | 0 ≤ (l : Module.Dual ℝ E) v} = {v | 0 ≤ l v} := rfl
  rw [h1, h2, this]

theorem isClosedHemisphere_closedHemisphere {l : StrongDual ℝ E} (hl : l ≠ 0) :
    IsClosedHemisphere (closedHemisphere (l : Module.Dual ℝ E)) := by
  refine ⟨openHemisphere (l : Module.Dual ℝ E), ⟨isOpen_ofCone' (isPosCone_pos _) ?_, _,
    F_openHemisphere _⟩, (openHemisphere_nonempty_iff _).2 ?_, closure_openHemisphere' hl⟩
  · exact isOpen_lt continuous_const l.continuous
  · intro h; apply hl; ext v; exact congrArg (· v) h

theorem IsClosedHemisphere.exists_eq {W : Set (Sphere E)} (hW : IsClosedHemisphere W) :
    ∃ l : StrongDual ℝ E, l ≠ 0 ∧ W = closedHemisphere (l : Module.Dual ℝ E) := by
  obtain ⟨H, ⟨hHo, l, hF⟩, hne, rfl⟩ := hW
  have hl : l ≠ 0 := by
    rintro rfl
    obtain ⟨x, hx⟩ := hne
    induction x using ind with
    | h v hv =>
      have := (mk_mem_iff_mem_F hv).1 hx
      rw [hF] at this
      simp at this
  have hc := continuous_of_isOpen_of_F_eq' hHo hF hl
  set L : StrongDual ℝ E := ⟨l, hc⟩
  have hL : L ≠ 0 := by
    intro h; apply hl; ext v; exact congrArg (· v) h
  have hH : H = openHemisphere (L : Module.Dual ℝ E) := by
    apply F_injective; rw [hF, F_openHemisphere]
  exact ⟨L, hL, by rw [hH, closure_openHemisphere' hL]⟩

end Hemisphere

/-- `closedHemisphere l = closedHemisphere l'` forces `l' = c • l`, `c > 0` (no hypothesis). -/
theorem closedHemisphere_eq_iff (l l' : Module.Dual ℝ E) :
    closedHemisphere l = closedHemisphere l' ↔ ∃ c : ℝ, 0 < c ∧ l' = c • l := by
  constructor
  · intro h
    have ho : openHemisphere (-l) = openHemisphere (-l') := by
      ext x
      induction x using ind with
      | h v hv =>
        have := congrArg (mk v hv ∈ ·) h
        simp only [mk_mem_closedHemisphere, eq_iff_iff] at this
        rw [mk_mem_openHemisphere, mk_mem_openHemisphere, LinearMap.neg_apply,
          LinearMap.neg_apply, neg_pos, neg_pos, ← not_le, ← not_le, this]
    obtain ⟨c, hc, hcl⟩ := (openHemisphere_eq_iff _ _).1 ho
    refine ⟨c, hc, ?_⟩
    rw [smul_neg, neg_inj] at hcl
    exact hcl
  · rintro ⟨c, hc, rfl⟩
    ext x
    induction x using ind with
    | h v hv =>
      rw [mk_mem_closedHemisphere, mk_mem_closedHemisphere, LinearMap.smul_apply, smul_eq_mul,
        mul_nonneg_iff_of_pos_left hc]

/-- The `D` of a point: `D({s v}) = s{m′ | ⟨v, m′⟩ ≥ 0}`, the closed hemisphere of `⟨v, ·⟩`. -/
theorem D_singleton (B : E →ₗ[ℝ] E' →ₗ[ℝ] ℝ) {v : E} (hv : v ≠ 0) :
    D B {mk v hv} = closedHemisphere (B v) := by
  ext x
  induction x using ind with
  | h w hw =>
    rw [mk_mem_D, mk_mem_closedHemisphere]
    constructor
    · intro h
      exact h v ⟨hv, rfl⟩
    · intro h m hm
      obtain ⟨hm0, hmv⟩ := hm
      obtain ⟨c, hc, hcm⟩ := (mk_eq_mk_iff_exists_pos hm0 hv).1 (mem_singleton_iff.1 hmv)
      rw [← hcm, map_smul, LinearMap.smul_apply, smul_eq_mul] at h
      exact (mul_nonneg_iff_of_pos_left hc).1 h

theorem D'_singleton (B : E →ₗ[ℝ] E' →ₗ[ℝ] ℝ) {v : E'} (hv : v ≠ 0) :
    D' B {mk v hv} = closedHemisphere (B.flip v) :=
  D_singleton B.flip hv

/-! ### Prop. 3 -/

section Prop3

variable (E) [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- The evaluation form `⟨M, M′⟩ = M′(M)` on `E × E′`, `E′` the continuous linear forms on `E`. -/
def evalPairing : E →ₗ[ℝ] StrongDual ℝ E →ₗ[ℝ] ℝ := (topDualPairing ℝ E).flip

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
@[simp] theorem evalPairing_apply (M : E) (M' : StrongDual ℝ E) : evalPairing E M M' = M' M := rfl

variable {E}

/-- **Prop. 3** (`bzprop:c3s3p3_hemispheres_points`, p. 270): for every real topological vector
space `E`, `m ↦ D′({m})` is a bijection of `S(E′)` onto the closed hemispheres of `S(E)`. -/
theorem prop3 :
    BijOn (fun m : Sphere (StrongDual ℝ E) => D' (evalPairing E) {m}) univ
      {W | IsClosedHemisphere W} := by
  have hD' : ∀ (M : StrongDual ℝ E) (hM : M ≠ 0),
      D' (evalPairing E) {mk M hM} = closedHemisphere (M : Module.Dual ℝ E) := by
    intro M hM
    rw [D'_singleton]
    rfl
  refine ⟨fun x _ => ?_, fun x _ y _ hxy => ?_, fun W hW => ?_⟩
  · induction x using ind with
    | h M hM =>
      show IsClosedHemisphere (D' (evalPairing E) {mk M hM})
      rw [hD']
      exact isClosedHemisphere_closedHemisphere hM
  · induction x using ind with
    | h M hM =>
      induction y using ind with
      | h N hN =>
        simp only [hD'] at hxy
        obtain ⟨c, hc, hcMN⟩ := (closedHemisphere_eq_iff _ _).1 hxy
        rw [mk_eq_mk_iff_exists_pos]
        refine ⟨c, hc, ?_⟩
        ext v
        have := congrArg (fun g : Module.Dual ℝ E => g v) hcMN
        simp only [LinearMap.smul_apply, ContinuousLinearMap.coe_coe] at this
        simp [this]
  · obtain ⟨L, hL, rfl⟩ := IsClosedHemisphere.exists_eq hW
    exact ⟨mk L hL, mem_univ _, hD' L hL⟩

end Prop3

/-! ### Prop. 1 for a semi-reflexive space and its strong dual -/

section SemiReflexive

variable (E) [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- Bourbaki's **semi-reflexivity** (EVT IV § 2): every continuous linear form on the strong dual
`E′_β` (Mathlib's `StrongDual ℝ E`, with the topology of uniform convergence on bounded sets) is the
evaluation at a point of `E`. -/
def IsSemiReflexive : Prop :=
  ∀ φ : StrongDual ℝ (StrongDual ℝ E), ∃ m : E, ∀ f : StrongDual ℝ E, φ f = f m

variable {E}

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- Hypothesis (c) holds for `E` and its dual `E′` with the evaluation form, for every real
topological vector space `E`. -/
theorem identifiesDual_evalPairing : IdentifiesDual (evalPairing E) := by
  refine ⟨fun M' => M'.continuous, fun f => ⟨f, fun m => rfl, fun y hy => ?_⟩⟩
  ext m
  exact hy m

/-- Hypothesis (c) holds for `E′_β` and `E` exactly when `E` is semi-reflexive (Hausdorff locally
convex `E`; uniqueness is Hahn–Banach's separation of points). -/
theorem identifiesDual_flip_evalPairing [LocallyConvexSpace ℝ E] [T1Space E]
    (hE : IsSemiReflexive E) : IdentifiesDual (evalPairing E).flip := by
  refine ⟨fun m => continuous_eval_const m, fun φ => ?_⟩
  obtain ⟨m, hm⟩ := hE φ
  refine ⟨m, fun f => (hm f).symm, fun m' hm' => ?_⟩
  by_contra hne
  obtain ⟨f, hf⟩ := geometric_hahn_banach_point_point hne
  have h1 := hm' f
  have h2 := hm f
  simp only [LinearMap.flip_apply, evalPairing_apply] at h1
  rw [h1, h2] at hf
  exact lt_irrefl _ hf

/-- **Prop. 1 for a semi-reflexive space** (`bzprop:c3s3p1_dualite_biunivoque`, the reading of
« semi-réflexifs mis en dualité » as `E` semi-reflexive and `E′ = E′_β` its strong dual): for every
Hausdorff locally convex semi-reflexive `E`, `D` is a bijection of `C(S(E))` onto `C(S(E′_β))` with
inverse `D′`. -/
theorem prop1_semiReflexive [LocallyConvexSpace ℝ E] [T1Space E] (hE : IsSemiReflexive E) :
    BijOn (D (evalPairing E)) (CS E) (CS (StrongDual ℝ E)) ∧
      InvOn (D' (evalPairing E)) (D (evalPairing E)) (CS E) (CS (StrongDual ℝ E)) :=
  prop1 (evalPairing E) ⟨identifiesDual_evalPairing, identifiesDual_flip_evalPairing hE⟩

/-- Every finite-dimensional Hausdorff real topological vector space is semi-reflexive (so
`prop1_semiReflexive` applies, e.g., to `ℝⁿ⁺¹`). -/
theorem isSemiReflexive_of_finiteDimensional [T2Space E] [FiniteDimensional ℝ E] :
    IsSemiReflexive E := by
  intro φ
  let e : Module.Dual ℝ E ≃ₗ[ℝ] StrongDual ℝ E := LinearMap.toContinuousLinearMap
  let ψ : Module.Dual ℝ (Module.Dual ℝ E) := (φ : StrongDual ℝ E →ₗ[ℝ] ℝ).comp e.toLinearMap
  obtain ⟨m, hm⟩ := (Module.evalEquiv ℝ E).surjective ψ
  refine ⟨m, fun f => ?_⟩
  have h := congrArg (fun g : Module.Dual ℝ (Module.Dual ℝ E) => g (e.symm f)) hm
  simp only [Module.evalEquiv_apply, Module.Dual.eval_apply, ψ, LinearMap.coe_comp,
    Function.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    ContinuousLinearMap.coe_coe] at h
  rw [← h]
  rfl

end SemiReflexive

/-! ### Prop. 4 -/

/-- **Prop. 4** (`bzprop:c3s3p4_dual_geometrique`, p. 270), the description: `D(W)` is the set of the
points `M′` of `S(E′)` such that `W ⊆ D′({M′})` (printed « $D(\{M'\})$ », read `D′`), for every part
`W` and every form. -/
theorem prop4_eq (B : E →ₗ[ℝ] E' →ₗ[ℝ] ℝ) (W : Set (Sphere E)) :
    D B W = {M' | W ⊆ D' B {M'}} := by
  ext x
  induction x using ind with
  | h v hv =>
    rw [mk_mem_D, mem_setOf_eq, D'_singleton]
    constructor
    · intro h y hy
      induction y using ind with
      | h w hw =>
        rw [mk_mem_closedHemisphere]
        exact h w ⟨hw, hy⟩
    · intro h m hm
      obtain ⟨hm0, hmW⟩ := hm
      have := h hmW
      rw [mk_mem_closedHemisphere] at this
      exact this

/-- **Prop. 4** (`bzprop:c3s3p4_dual_geometrique`): under (c) for `E` (contained in the hypotheses
of (d)), every `D′({M′})` is a closed hemisphere of `S(E)`, and `D(W)` is the set of the `M′` with
`W ⊆ D′({M′})`. -/
theorem prop4 [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (B : E →ₗ[ℝ] E' →ₗ[ℝ] ℝ) (hB : IdentifiesDual B) (W : Set (Sphere E)) :
    (∀ M' : Sphere E', IsClosedHemisphere (D' B {M'})) ∧ D B W = {M' | W ⊆ D' B {M'}} := by
  refine ⟨fun x => ?_, prop4_eq B W⟩
  induction x using ind with
  | h v hv =>
    rw [D'_singleton]
    set L : StrongDual ℝ E := ⟨B.flip v, hB.1 v⟩
    have hL : L ≠ 0 := by
      intro h0
      apply hv
      obtain ⟨y, -, huniq⟩ := hB.2 0
      have h1 := huniq v fun m => congrArg (fun g : StrongDual ℝ E => g m) h0
      have h2 := huniq 0 fun m => by simp
      rw [h1, h2]
    exact isClosedHemisphere_closedHemisphere hL

/-! ### Prop. 5 -/

/-- The orthogonal `L^⊥ = {m′ | ⟨m, m′⟩ = 0, ∀ m ∈ L}` of a subspace `L ⊆ E` in `E′`. -/
def orth (B : E →ₗ[ℝ] E' →ₗ[ℝ] ℝ) (L : Submodule ℝ E) : Submodule ℝ E' :=
  L.dualAnnihilator.comap B.flip

theorem mem_orth (B : E →ₗ[ℝ] E' →ₗ[ℝ] ℝ) (L : Submodule ℝ E) {v : E'} :
    v ∈ orth B L ↔ ∀ m ∈ L, B m v = 0 := by
  simp [orth, Submodule.mem_dualAnnihilator]

/-- **Prop. 5** (`bzprop:c3s3p5_dual_variete_lineaire`, p. 270): under (a) alone, the `D` of a
linear subvariety `s(L - {O})` is the linear subvariety `s(L^⊥ - {O})`. -/
theorem D_linearSubvariety (B : E →ₗ[ℝ] E' →ₗ[ℝ] ℝ) (L : Submodule ℝ E) :
    D B (linearSubvariety L) = linearSubvariety (orth B L) := by
  ext x
  induction x using ind with
  | h v hv =>
    rw [mk_mem_D, mk_mem_linearSubvariety, mem_orth, F_linearSubvariety]
    constructor
    · intro h m hm
      by_cases hm0 : m = 0
      · simp [hm0]
      · have h1 := h m ⟨hm, hm0⟩
        have h2 := h (-m) ⟨L.neg_mem hm, neg_ne_zero.2 hm0⟩
        simp only [map_neg, LinearMap.neg_apply] at h2
        linarith
    · intro h m hm
      rw [h m hm.1]

theorem prop5 (B : E →ₗ[ℝ] E' →ₗ[ℝ] ℝ) (L : Submodule ℝ E) :
    ∃ L' : Submodule ℝ E', D B (linearSubvariety L) = linearSubvariety L' :=
  ⟨_, D_linearSubvariety B L⟩

/-! ### Points and closed hemispheres under (d) -/

/-- A point `{s v}` of `S(E)` is a convex part. -/
theorem isConvexPart_singleton {v : E} (hv : v ≠ 0) :
    IsConvexPart ({mk v hv} : Set (Sphere E)) := by
  have hset : insert 0 (F {mk v hv}) = (LinearMap.id.smulRight v : ℝ →ₗ[ℝ] E) '' Ici 0 := by
    ext w
    constructor
    · rintro (rfl | ⟨hw, hwv⟩)
      · exact ⟨0, self_mem_Ici, by simp⟩
      · obtain ⟨c, hc, hcw⟩ := (mk_eq_mk_iff_exists_pos hv hw).1 (mem_singleton_iff.1 hwv).symm
        exact ⟨c, le_of_lt hc, by simpa using hcw⟩
    · rintro ⟨t, ht, rfl⟩
      rcases (mem_Ici.1 ht).eq_or_lt with h | h
      · left; simp [← h]
      · right
        refine ⟨by simpa using smul_ne_zero h.ne' hv, ?_⟩
        simp only [LinearMap.smulRight_apply, LinearMap.id_apply]
        exact mk_smul hv h _
  unfold IsConvexPart
  rw [hset]
  exact (convex_Ici 0).linear_image _

/-- Under the hypotheses of (d), **the `D` of a closed hemisphere is (the closure of) a point**: if
`W` is a closed hemisphere of `S(E)`, then `D(W) = closure {x}` for a point `x` of `S(E′)`. -/
theorem D_isClosedHemisphere [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [TopologicalSpace E'] [IsTopologicalAddGroup E'] [ContinuousSMul ℝ E']
    [LocallyConvexSpace ℝ E'] [T1Space E'] (B : E →ₗ[ℝ] E' →ₗ[ℝ] ℝ) (hB : HypD B)
    {W : Set (Sphere E)} (hW : IsClosedHemisphere W) :
    ∃ x : Sphere E', D B W = closure {x} := by
  obtain ⟨L, hL, rfl⟩ := hW.exists_eq
  obtain ⟨m', hm', -⟩ := hB.1.2 L
  have hm'0 : m' ≠ 0 := by
    rintro rfl
    apply hL
    ext v
    rw [← hm' v]
    simp
  have hW' : closedHemisphere (L : Module.Dual ℝ E) = D' B {mk m' hm'0} := by
    rw [D'_singleton]
    congr 1
    ext v
    exact (hm' v).symm
  refine ⟨mk m' hm'0, ?_⟩
  rw [hW']
  have := D'_D_eq_closure B.flip hB.2 (isConvexPart_singleton hm'0)
  rw [D_flip_flip] at this
  exact this

end Sphere

/-! ### The instance: `ℝⁿ⁺¹` with the dot product -/

namespace Sphere

/-- The dot product `⟨M, N⟩ = ∑ mᵢ nᵢ` on `ℝⁿ⁺¹` (p. 270). -/
def dotPairing (n : ℕ) : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ) →ₗ[ℝ] ℝ :=
  dotProductBilin ℝ ℝ

theorem dotPairing_apply (n : ℕ) (M N : Fin (n + 1) → ℝ) :
    dotPairing n M N = ∑ i, M i * N i := by
  simp [dotPairing, dotProduct]

theorem dotPairing_flip (n : ℕ) : (dotPairing n).flip = dotPairing n := by
  refine LinearMap.ext fun M => LinearMap.ext fun N => ?_
  rw [LinearMap.flip_apply, dotPairing_apply, dotPairing_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem D'_dotPairing (n : ℕ) : D' (dotPairing n) = D (dotPairing n) := by
  funext W
  show D (dotPairing n).flip W = _
  rw [dotPairing_flip]

/-- **Hypothesis (c) for the instance**: the dot product identifies `ℝⁿ⁺¹` with its continuous
dual, `f ↦ (f(e₀), …, f(eₙ))`. -/
theorem identifiesDual_dotPairing (n : ℕ) : IdentifiesDual (dotPairing n) := by
  refine ⟨fun m' => by exact ((dotPairing n).flip m').continuous_of_finiteDimensional,
    fun f => ?_⟩
  let e : Fin (n + 1) → Fin (n + 1) → ℝ := fun i j => if i = j then 1 else 0
  refine ⟨fun i => f (e i), fun m => ?_, fun y hy => ?_⟩
  · rw [dotPairing_apply]
    have := LinearMap.pi_apply_eq_sum_univ (f : (Fin (n + 1) → ℝ) →ₗ[ℝ] ℝ) m
    simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at this
    rw [this]
  · funext i
    have := hy (e i)
    rw [dotPairing_apply] at this
    simpa [e, ite_mul, Finset.sum_ite_eq] using this

/-- **The instance meets every hypothesis**: `ℝⁿ⁺¹` with the dot product satisfies (a)–(d):
(a) the form is bilinear (`dotPairing`); (b) `ℝⁿ⁺¹` is a Hausdorff locally convex space (the
instances used by `prop1` are found by `inferInstance`) and the form is separately continuous;
(c) for `E` and (d) for `E′ = E`, by symmetry. -/
theorem hypD_dotPairing (n : ℕ) : HypD (dotPairing n) :=
  ⟨identifiesDual_dotPairing n, by rw [dotPairing_flip]; exact identifiesDual_dotPairing n⟩

/-- The topological hypotheses of (b) hold on `ℝⁿ⁺¹`, as instances. -/
example (n : ℕ) : IsTopologicalAddGroup (Fin (n + 1) → ℝ) ∧ ContinuousSMul ℝ (Fin (n + 1) → ℝ) ∧
    LocallyConvexSpace ℝ (Fin (n + 1) → ℝ) ∧ T2Space (Fin (n + 1) → ℝ) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- On `S(n)`, `D = D′`, and `D` is an involutive bijection of `C(S(n))`. -/
theorem dotPairing_prop1 (n : ℕ) :
    BijOn (D (dotPairing n)) (CS (Fin (n + 1) → ℝ)) (CS (Fin (n + 1) → ℝ)) ∧
      ∀ W ∈ CS (Fin (n + 1) → ℝ), D (dotPairing n) (D (dotPairing n) W) = W := by
  have h := prop1 (dotPairing n) (hypD_dotPairing n)
  rw [D'_dotPairing] at h
  exact ⟨h.1, fun W hW => h.2.1 hW⟩

/-- On `S(n)`, the `D` of a point is a closed hemisphere. -/
theorem dotPairing_D_point (n : ℕ) (x : S n) : IsClosedHemisphere (D (dotPairing n) {x}) := by
  have h := (prop4 (dotPairing n) (identifiesDual_dotPairing n) ∅).1 x
  rw [D'_dotPairing] at h
  exact h

/-- On `S(n)`, the `D` of a closed hemisphere is a point. -/
theorem dotPairing_D_closedHemisphere (n : ℕ) {W : Set (S n)} (hW : IsClosedHemisphere W) :
    ∃ x : S n, D (dotPairing n) W = {x} := by
  obtain ⟨x, hx⟩ := D_isClosedHemisphere (dotPairing n) (hypD_dotPairing n) hW
  exact ⟨x, by rw [hx, closure_singleton]⟩

/-- `ℝⁿ⁺¹` is semi-reflexive, so `prop1_semiReflexive` applies to it as well. -/
theorem isSemiReflexive_Rn (n : ℕ) : IsSemiReflexive (Fin (n + 1) → ℝ) :=
  isSemiReflexive_of_finiteDimensional

end Sphere

end Benzecri
