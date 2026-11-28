import Benzecri.Projective.Convex
import Benzecri.Chapter2.CrossRatio
import Benzecri.Chapter2.Poches

/-!
# Chapter 3 § 4 — the supporting cone `W_a` (Déf. 1, 1′, 1″) and the contingent (Déf. 2)

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 3 § 4, journal p. 272; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch3.tex` (checked against the scan, PDF p. 45).
Target T-bz-c3-cone-appui. Over an arbitrary real vector space `E` (Déf. 1, 1′, 1″, no topology);
Déf. 2 over a topological vector space.

* **`bzdef:c3s4d1_cone_appui`** — `benzecri1960_ch3.tex:881` (Déf. 1, l.881–885) —
  `Benzecri.Sphere.coneAppui`, the intersection of the convex parts containing `W` and `a′`; it is
  the smallest one (`isLeast_coneAppui`, for every `W` and `a`; convex parts are stable under
  intersection, `isConvexPart_sInter`).
* **`bzdef:c3s4d1primeprime_cone_appui_vecteurs`** — `benzecri1960_ch3.tex:894` (Déf. 1″,
  l.894–899) — proved from Déf. 1 as printed: `F_coneAppui_union_zero`
  (`F(W_a) ∪ {O} = {λA + P | λ ∈ ℝ, P ∈ F(W)}` for `W` convex, `a ∈ W`, `A` any representative
  of `a`).
* `bzdef:c3s4d1prime_cone_appui_demi_droites` — `benzecri1960_ch3.tex:889` (Déf. 1′, l.889–892)
  — NOT marked: imprecise. With closed half-lines (ends `a, a′` included, the reading « distinct
  des extrémités $a$ et $a'$ » implies), `W_a` is the union iff `W ⊄ {a, a′}`
  (`coneAppui_eq_demiDroitesFermeesW_iff`): it fails only in the degenerate cases `W = {a}`,
  `W = {a, a′}`. The degenerate case `W = {a}`: `coneAppui_singleton` (`W_a = {a, a′}`) against
  `demiDroitesFermeesW_singleton`, `demiDroitesW_singleton` (both unions empty); the
  degenerate-case refutation `not_def1prime_closed`. Corrected form, valid with no exception:
  `coneAppui_eq_insert_demiDroitesW` (`W_a = {a, a′} ∪` the union of the open half-lines; also
  `coneAppui_diff_eq_demiDroitesW`). With the library's open `halfLine` the union alone never
  contains `a′` (`coneAppui_ne_demiDroitesW`): a fact about that convention, not about the paper.
* **`bzdef:c3s4d2_contingent`** — `benzecri1960_ch3.tex:901` (Déf. 2, l.901–904) —
  `Benzecri.Sphere.contingent`, the closure of `W_a`; it is closed (`isClosed_contingent`), a convex
  part (`isConvexPart_contingent`), and the smallest closed convex part containing `W` and `a′`
  (`isLeast_contingent`).

> **Définition 1.** Soient $E$ un espace vectoriel, $W\in K(S(E))$, $a\in W$, $a'$ le point
> diamétralement opposé à $a$. On appelle *cône d'appui* en $a$ à $W$ le plus petit convexe de
> $S(E)$ contenant $W$ et $a'$ : on le note $W_a$.
>
> On peut donner de cette définition deux autres énoncés équivalents.
>
> **Définition 1′.** $W_a$ est la réunion des demi-droites de $S(E)$ qui joignent $a$ au point
> diamétralement opposé $a'$ et rencontrent $W$ en un point distinct des extrémités $a$ et $a'$.
>
> **Définition 1″.** Soit $A$ un point de $F(W)$ se projetant sur $W$ suivant $a$ :
> $F(W_a)\cup\{O\}$ est l'ensemble des vecteurs de $E$ qui peuvent s'écrire comme somme d'un
> vecteur de $F(W)$ et d'un vecteur multiple de $A$ par un nombre réel
> $F(W_a)\cup\{O\}=\{M : \exists\lambda\in\R;\ \exists P\in F(W);\ M=\lambda A+P\}.$
>
> **Définition 2.** On appelle contingent à un convexe fermé $W$ en un de ses points $a$ la
> fermeture du cône d'appui $W_a$.

## The proofs formalized

Déf. 1: a convex part (Déf. 8) is a part whose segments between non-antipodal points stay inside
(Chapter 1's `isConvexPart_iff_isSegConvex`), a condition stable under every intersection; so the
intersection of the convex parts containing `W ∪ {a′}` is the smallest one. Déf. 1″: the set
`C = {λA + P}` contains `O = −A + A`, is convex (a combination of `P, Q ∈ F(W) ∪ {O}` lies in
`F(W) ∪ {O}`, and `O` is absorbed by `A`) and stable under `ℝ₊*`; so `s(C − {O})` is a convex
part containing `W` (`λ = 0`) and `a′` (`−2A + A`), and any convex part containing `W` and `a′`
contains it (its cone contains `ℝ₊A`, `ℝ₊(−A)` and `F(W)`, and is closed under sums). Déf. 1′:
a point `s(λA + P)` of `W_a` other than `a, a′` has `P` independent of `A`, so it lies on the
half-line `{αA + βP | β > 0}` through `s(P) ∈ W`; conversely that half-line is in `W_a` by Déf. 1″.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| Déf. 1: « $E$ un espace vectoriel » (real) | ✓ carried: `[AddCommGroup E] [Module ℝ E]`, any dimension, no topology |
| Déf. 1: « $W\in K(S(E))$, $a\in W$ » | generalised: `coneAppui W a` is defined, and is the smallest convex part containing `W` and `a′`, for every `W` and `a`; `IsConvexPart W`, `a ∈ W` are used only where the equivalent forms need them |
| Déf. 1: « le plus petit convexe de $S(E)$ » | ✓ carried: `IsLeast` among `IsConvexPart` (Déf. 8, DEC-120's `∪` reading) parts containing `W` and `-a` |
| Déf. 1″: « $A$ un point de $F(W)$ se projetant sur $W$ suivant $a$ » | ✓ carried: `IsRep A a` with `a ∈ W` (i.e. `A ∈ F(W)`, `s(A) = a`), any such `A` |
| Déf. 1′: « demi-droites de $S(E)$ » | Chapter 1 (Déf. 4, Exemples) only says two antipodal points divide a line into two half-lines; reading (question): closed, ends `a, a′` included (`demiDroitesFermeesW`), as « distinct des extrémités » implies; the library's open `halfLine A w = s({αA + βw | β > 0})` (`demiDroitesW`) is treated too |
| Déf. 1′: « qui joignent $a$ au point $a'$ » | ✓ carried: `IsDemiDroiteJoignant a h`: `h = halfLine A w` for a representative `A` of `a` |
| Déf. 1′: « rencontrent $W$ en un point distinct des extrémités » | ✓ carried: `∃ b ∈ h, b ∈ W ∧ b ≠ a ∧ b ≠ -a` |
| Déf. 2: « un convexe fermé $W$ », « un de ses points $a$ » | generalised: `contingent W a` is defined for every `W`, `a`; closedness of `W` is not used |
| Déf. 2: « la fermeture » | ✓ carried: the closure in the quotient topology of `S(E)`; its properties under `[IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T1Space E]` |

## SCOPE (disclosed)

* **Déf. 1′ is imprecise** (finding): with closed half-lines it holds iff `W ⊄ {a, a′}`, and
  fails only in the degenerate cases `W = {a}`, `W = {a, a′}` (e.g. whenever `dim E = 1`), where
  `W_a = {a, a′}` and the union is empty. It is not marked. What is true always:
  `W_a = {a, a′} ∪ ⋃ open half-lines`.
* The instance (non-vacuity), on `S(1)`: `W` the closed quarter arc from `a = s(e₀)` to
  `s(e₁)`, `a` an endpoint; `W_a` and its contingent are the closed hemisphere
  `{x₁ ≥ 0}` (`coneAppui_arcS1`, `contingent_arcS1`), strictly larger than `W`
  (`arcS1_ne_coneAppui`), and Déf. 1′ in its closed reading holds there (`def1prime_closed_arcS1`).
* General facts proved here (candidates to move upstream at graduation): `isConvexPart_sInter`,
  `isConvexPart_closedSeg` (a closed segment of `S(E)`, antipodal ends included, is a convex
  part), `isConvexPart_singleton_pt`, `IsConvexPart.closure` (the closure of a convex part is a
  convex part), `mk_smul_eq_or`, `linearIndependent_of_mem_F`, `coneAppui_eq_ofCone`,
  `coneAppui_closedSeg`. `isConvexPart_singleton_pt` duplicates the strict
  `Chapter3/Dualite`'s `isConvexPart_singleton` (stated by a vector), not imported here.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Topology

namespace Benzecri

namespace Sphere

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-! ### Déf. 1 — the supporting cone -/

/-- Convex parts of `S(E)` (Déf. 8) are stable under arbitrary intersections. -/
theorem isConvexPart_sInter {S : Set (Set (Sphere E))} (hS : ∀ k ∈ S, IsConvexPart k) :
    IsConvexPart (⋂₀ S) := by
  rw [isConvexPart_iff_isSegConvex]
  intro m hm m' hm' hne x hx k hk
  exact (isConvexPart_iff_isSegConvex.1 (hS k hk)) m (hm k hk) m' (hm' k hk) hne hx

/-- **Déf. 1** (`bzdef:c3s4d1_cone_appui`): the *cône d'appui* `W_a`, the intersection of the
convex parts of `S(E)` containing `W` and `a′ = -a`; it is the smallest such
(`isLeast_coneAppui`). -/
def coneAppui (W : Set (Sphere E)) (a : Sphere E) : Set (Sphere E) :=
  ⋂₀ {k | IsConvexPart k ∧ W ⊆ k ∧ -a ∈ k}

/-- **Déf. 1, « le plus petit convexe de $S(E)$ contenant $W$ et $a'$ »**: `W_a` is the least
convex part containing `W` and `a′`, for every `W` and `a`. -/
theorem isLeast_coneAppui (W : Set (Sphere E)) (a : Sphere E) :
    IsLeast {k | IsConvexPart k ∧ W ⊆ k ∧ -a ∈ k} (coneAppui W a) :=
  ⟨⟨isConvexPart_sInter fun _ hk => hk.1, subset_sInter fun _ hk => hk.2.1,
    mem_sInter.2 fun _ hk => hk.2.2⟩, fun _ hk => sInter_subset_of_mem hk⟩

/-! ### The cone `{λA + P}` -/

/-- The set `{λA + P | λ ∈ ℝ, P ∈ F(W)}` of Déf. 1″. -/
def coneAppuiVec (W : Set (Sphere E)) (A : E) : Set E := {M | ∃ l : ℝ, ∃ P ∈ F W, M = l • A + P}

theorem isPosCone_coneAppuiVec (W : Set (Sphere E)) (A : E) : IsPosCone (coneAppuiVec W A) := by
  rintro c hc _ ⟨l, P, hP, rfl⟩
  exact ⟨c * l, c • P, smul_mem_F hP hc, by rw [smul_add, smul_smul]⟩

theorem self_mem_coneAppuiVec {W : Set (Sphere E)} {A : E} (hA : A ∈ F W) (r : ℝ) :
    r • A ∈ coneAppuiVec W A :=
  ⟨r - 1, A, hA, by rw [sub_smul, one_smul, sub_add_cancel]⟩

theorem convex_coneAppuiVec {W : Set (Sphere E)} (hW : IsConvexPart W) {A : E} (hA : A ∈ F W) :
    Convex ℝ (coneAppuiVec W A) := by
  rintro _ ⟨l, P, hP, rfl⟩ _ ⟨l', Q, hQ, rfl⟩ s t hs ht hst
  have hPQ := hW (mem_insert_of_mem _ hP) (mem_insert_of_mem _ hQ) hs ht hst
  have e : s • (l • A + P) + t • (l' • A + Q) = (s * l + t * l') • A + (s • P + t • Q) := by
    module
  rw [e]
  rcases mem_insert_iff.1 hPQ with h0 | hF
  · rw [h0, add_zero]; exact self_mem_coneAppuiVec hA _
  · exact ⟨_, _, hF, rfl⟩

/-- **`W_a = s(C − {O})`**, `C = {λA + P}`: the heart of Déf. 1″. -/
theorem coneAppui_eq_ofCone {W : Set (Sphere E)} (hW : IsConvexPart W) {a : Sphere E}
    (ha : a ∈ W) {A : E} (hA : IsRep A a) : coneAppui W a = ofCone (coneAppuiVec W A) := by
  obtain ⟨hA0, rfl⟩ := hA
  have hAF : A ∈ F W := ⟨hA0, ha⟩
  have hC := isPosCone_coneAppuiVec W A
  have h0 : (0 : E) ∈ coneAppuiVec W A := by
    simpa using self_mem_coneAppuiVec hAF 0
  have hconv : IsConvexPart (ofCone (coneAppuiVec W A)) := by
    unfold IsConvexPart
    rw [insert_zero_F_ofCone hC, insert_eq_of_mem h0]
    exact convex_coneAppuiVec hW hAF
  have hWsub : W ⊆ ofCone (coneAppuiVec W A) := by
    intro x hx
    induction x using ind with
    | h v hv => exact mk_mem_ofCone hv ⟨0, v, ⟨hv, hx⟩, by rw [zero_smul, zero_add]⟩
  have hneg : -mk A hA0 ∈ ofCone (coneAppuiVec W A) := by
    rw [neg_mk]
    exact mk_mem_ofCone _ (by simpa using self_mem_coneAppuiVec hAF (-1))
  refine Subset.antisymm (sInter_subset_of_mem ⟨hconv, hWsub, hneg⟩) ?_
  obtain ⟨⟨hk, hWk, hak⟩, -⟩ := isLeast_coneAppui W (mk A hA0)
  intro x hx
  obtain ⟨v, hv, ⟨l, P, hP, rfl⟩, rfl⟩ := mem_ofCone.1 hx
  have hAk : A ∈ hk.cone := mem_insert_of_mem _ (F_mono hWk hAF)
  have hnAk : -A ∈ hk.cone := by
    refine mem_insert_of_mem _ ⟨neg_ne_zero.2 hA0, ?_⟩
    rw [← neg_mk]; exact hak
  have hPk : P ∈ hk.cone := mem_insert_of_mem _ (F_mono hWk hP)
  have hlA : l • A ∈ hk.cone := by
    rcases lt_trichotomy l 0 with hl | rfl | hl
    · have := hk.cone.smul_mem (neg_pos.2 hl) hnAk
      rwa [smul_neg, ← neg_smul, neg_neg] at this
    · rw [zero_smul]; exact mem_insert _ _
    · exact hk.cone.smul_mem hl hAk
  have := hk.cone.add_mem hlA hPk
  rw [hk.mem_cone] at this
  exact (mk_mem_iff_mem_F hv).2 ((mem_insert_iff.1 this).resolve_left hv)

/-- The positive cone hull `{sM + tM' | s, t ≥ 0}` of two vectors. -/
def posHull (M M' : E) : Set E := {v | ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ v = s • M + t • M'}

/-- A closed segment of `S(E)` is a convex part (also for antipodal ends: `{m, -m}`). -/
theorem isConvexPart_closedSeg (m m' : Sphere E) : IsConvexPart (closedSeg m m') := by
  induction m using ind with
  | h M hM =>
  induction m' using ind with
  | h M' hM' =>
  rw [closedSeg_mk, segOf]
  have hC : IsPosCone (posHull M M') := by
    rintro c hc _ ⟨s, t, hs, ht, rfl⟩
    exact ⟨c * s, c * t, by positivity, by positivity, by rw [smul_add, smul_smul, smul_smul]⟩
  have heq : ofCone (segment ℝ M M') = ofCone (posHull M M') := by
    refine Subset.antisymm (ofCone_subset_of_forall fun z hz _ => ?_)
      (ofCone_subset_of_forall fun z hz hz0 => ?_)
    · obtain ⟨s, t, hs, ht, -, rfl⟩ := hz
      exact ⟨1, one_pos, _, ⟨s, t, hs, ht, rfl⟩, by rw [one_smul]⟩
    · obtain ⟨s, t, hs, ht, rfl⟩ := hz
      have hst : 0 < s + t := by
        rcases (add_nonneg hs ht).lt_or_eq with h | h
        · exact h
        · exfalso; apply hz0
          have hs0 : s = 0 := by linarith
          have ht0 : t = 0 := by linarith
          rw [hs0, ht0, zero_smul, zero_smul, add_zero]
      refine ⟨s + t, hst, (s / (s + t)) • M + (t / (s + t)) • M',
        ⟨_, _, by positivity, by positivity, by field_simp, rfl⟩, ?_⟩
      rw [smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ hst.ne', mul_div_cancel₀ _ hst.ne']
  rw [heq]
  unfold IsConvexPart
  have h0 : (0 : E) ∈ posHull M M' := ⟨0, 0, le_rfl, le_rfl, by simp⟩
  rw [insert_zero_F_ofCone hC, insert_eq_of_mem h0]
  rintro _ ⟨s, t, hs, ht, rfl⟩ _ ⟨s', t', hs', ht', rfl⟩ p q hp hq _
  exact ⟨p * s + q * s', p * t + q * t', by positivity, by positivity, by module⟩

/-- A point of `S(E)` is a convex part. -/
theorem isConvexPart_singleton_pt (a : Sphere E) : IsConvexPart ({a} : Set (Sphere E)) := by
  rw [isConvexPart_iff_isSegConvex]
  rintro m hm m' hm' -
  rw [mem_singleton_iff] at hm hm'
  subst hm hm'
  induction m' using ind with
  | h M hM =>
  rw [closedSeg_mk, segOf, segment_same]
  intro x hx
  obtain ⟨v, hv, hvM, rfl⟩ := mem_ofCone.1 hx
  obtain rfl := mem_singleton_iff.1 hvM
  rfl

/-! ### Déf. 1″ — the vector description -/

/-- **Déf. 1″** (`bzdef:c3s4d1primeprime_cone_appui_vecteurs`), proved from Déf. 1: for `W` a
convex part, `a ∈ W`, `A` a point of `F(W)` over `a`,
`F(W_a) ∪ {O} = {M | ∃ λ ∈ ℝ, ∃ P ∈ F(W), M = λA + P}`. -/
theorem F_coneAppui_union_zero {W : Set (Sphere E)} (hW : IsConvexPart W) {a : Sphere E}
    (ha : a ∈ W) {A : E} (hA : IsRep A a) :
    F (coneAppui W a) ∪ {0} = {M | ∃ l : ℝ, ∃ P ∈ F W, M = l • A + P} := by
  have hAF : A ∈ F W := by obtain ⟨hA0, rfl⟩ := hA; exact ⟨hA0, ha⟩
  rw [coneAppui_eq_ofCone hW ha hA, F_ofCone (isPosCone_coneAppuiVec W A), sdiff_union_self,
    union_eq_left.2 (singleton_subset_iff.2 (by simpa using self_mem_coneAppuiVec hAF 0))]
  rfl

/-! ### Déf. 1′ — the description by half-lines -/

/-- `h` is a half-line of `S(E)` (Chapter 1, Déf. 4, Exemples; open, in the library's `halfLine`
convention, bounded by two diametrically opposite points) joining `a` to `a′`: `h = s({αA + βw | α ∈ ℝ, β > 0})` for a representative `A`
of `a` and `w` independent of `A`. -/
def IsDemiDroiteJoignant (a : Sphere E) (h : Set (Sphere E)) : Prop :=
  ∃ A w : E, IsRep A a ∧ LinearIndependent ℝ ![A, w] ∧ h = halfLine A w

/-- **Déf. 1′, the union**: the union of the half-lines joining `a` to `a′` which meet `W` at a
point other than `a`, `a′`. -/
def demiDroitesW (W : Set (Sphere E)) (a : Sphere E) : Set (Sphere E) :=
  ⋃₀ {h | IsDemiDroiteJoignant a h ∧ ∃ b ∈ h, b ∈ W ∧ b ≠ a ∧ b ≠ -a}

/-- **Déf. 1′, the closed reading**: the same union of the closed half-lines `h ∪ {a, a′}`. -/
def demiDroitesFermeesW (W : Set (Sphere E)) (a : Sphere E) : Set (Sphere E) :=
  ⋃₀ ((fun h => insert a (insert (-a) h)) ''
    {h | IsDemiDroiteJoignant a h ∧ ∃ b ∈ h, b ∈ W ∧ b ≠ a ∧ b ≠ -a})

/-- A half-line joining `a` to `a′` contains neither `a` nor `a′`. -/
theorem IsDemiDroiteJoignant.notMem {a : Sphere E} {h : Set (Sphere E)}
    (hh : IsDemiDroiteJoignant a h) : a ∉ h ∧ -a ∉ h := by
  obtain ⟨A, w, ⟨hA0, rfl⟩, hAw, rfl⟩ := hh
  constructor
  · intro hm
    obtain ⟨α, β, hβ, e⟩ := (mk_mem_halfLine hA0).1 hm
    have := (LinearIndependent.pair_iff.1 hAw (α - 1) β
      (by linear_combination (norm := module) e)).2
    exact hβ.ne' this
  · intro hm
    rw [neg_mk] at hm
    obtain ⟨α, β, hβ, e⟩ := (mk_mem_halfLine _).1 hm
    have := (LinearIndependent.pair_iff.1 hAw (α + 1) β
      (by linear_combination (norm := module) e)).2
    exact hβ.ne' this

/-- A nonzero multiple of a representative of `a` is a representative of `a` or of `a′`. -/
theorem mk_smul_eq_or {A : E} (hA : A ≠ 0) {r : ℝ} (hr : r • A ≠ 0) :
    mk (r • A) hr = mk A hA ∨ mk (r • A) hr = -mk A hA := by
  rcases lt_trichotomy r 0 with h | rfl | h
  · right
    rw [neg_mk]
    have e : r • A = (-r) • -A := by rw [smul_neg, neg_smul, neg_neg]
    simp only [e]
    exact mk_smul _ (neg_pos.2 h) _
  · exact absurd (zero_smul ℝ A) hr
  · left; exact mk_smul hA h hr

/-- A point of `F(W)` not over `a` nor `a′` is independent of a representative `A` of `a`. -/
theorem linearIndependent_of_mem_F {A P : E} {a : Sphere E} (hA : IsRep A a) (hP : P ≠ 0)
    (h1 : mk P hP ≠ a) (h2 : mk P hP ≠ -a) : LinearIndependent ℝ ![A, P] :=
  linearIndependent_of_ne hA (isRep_mk P hP) h1 h2

/-- **Déf. 1′, true form**: off its two ends `a, a′`, `W_a` is the union of the half-lines from
`a` to `a′` meeting `W` off `a, a′`. -/
theorem coneAppui_diff_eq_demiDroitesW {W : Set (Sphere E)} (hW : IsConvexPart W)
    {a : Sphere E} (ha : a ∈ W) : coneAppui W a \ {a, -a} = demiDroitesW W a := by
  obtain ⟨A, hA⟩ := exists_isRep a
  rw [coneAppui_eq_ofCone hW ha hA]
  ext x
  constructor
  · rintro ⟨hx, hxa⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hxa
    obtain ⟨v, hv, ⟨l, P, ⟨hP0, hPW⟩, rfl⟩, rfl⟩ := mem_ofCone.1 hx
    have hne : ∀ r : ℝ, l • A + P ≠ r • A := by
      intro r e
      have hr : r • A ≠ 0 := e ▸ hv
      rcases mk_smul_eq_or hA.ne_zero hr with h | h
      · exact hxa.1 (by simp only [e]; rw [h]; exact hA.2)
      · exact hxa.2 (by simp only [e]; rw [h]; congr 1; exact hA.2)
    have h1 : mk P hP0 ≠ a := by
      intro h
      obtain ⟨c, -, hc⟩ := hA.exists_pos ⟨hP0, h⟩
      exact hne (l + c) (by rw [hc, add_smul])
    have h2 : mk P hP0 ≠ -a := by
      intro h
      obtain ⟨c, -, hc⟩ := hA.neg.exists_pos ⟨hP0, h⟩
      exact hne (l - c) (by rw [hc, sub_smul, smul_neg, sub_eq_add_neg])
    refine ⟨halfLine A P, ⟨⟨A, P, hA, linearIndependent_of_mem_F hA hP0 h1 h2, rfl⟩,
      mk P hP0, (mk_mem_halfLine hP0).2 ⟨0, 1, one_pos, by simp⟩, hPW, h1, h2⟩, ?_⟩
    exact (mk_mem_halfLine hv).2 ⟨l, 1, one_pos, by rw [one_smul]⟩
  · rintro ⟨h, ⟨hh, b, hbh, hbW, hba, hbna⟩, hxh⟩
    have hnm := hh.notMem
    refine ⟨?_, ?_⟩
    swap
    · simp only [mem_insert_iff, mem_singleton_iff, not_or]
      exact ⟨fun e => hnm.1 (e ▸ hxh), fun e => hnm.2 (e ▸ hxh)⟩
    obtain ⟨A', w, hA', hA'w, rfl⟩ := hh
    obtain ⟨c, hc, hcA⟩ := hA.exists_pos hA'
    induction x using ind with
    | h v hv =>
    induction b using ind with
    | h u hu =>
    obtain ⟨α, β, hβ, ev⟩ := (mk_mem_halfLine hv).1 hxh
    obtain ⟨α', β', hβ', eu⟩ := (mk_mem_halfLine hu).1 hbh
    refine mk_mem_ofCone hv ⟨c * (α - β * α' / β'), (β / β') • u,
      smul_mem_F ⟨hu, hbW⟩ (div_pos hβ hβ'), ?_⟩
    rw [← ev, ← eu, hcA]
    have hβ'0 : β' ≠ 0 := hβ'.ne'
    simp only [smul_add, smul_smul]
    rw [div_mul_cancel₀ β hβ'0]
    module

/-- **Déf. 1′, corrected**: `W_a = {a, a′} ∪ ⋃ half-lines`, for every convex `W ∋ a`. -/
theorem coneAppui_eq_insert_demiDroitesW {W : Set (Sphere E)} (hW : IsConvexPart W)
    {a : Sphere E} (ha : a ∈ W) : coneAppui W a = insert a (insert (-a) (demiDroitesW W a)) := by
  obtain ⟨⟨-, hWk, hak⟩, -⟩ := isLeast_coneAppui W a
  rw [← coneAppui_diff_eq_demiDroitesW hW ha]
  ext x
  by_cases h1 : x = a
  · subst h1; simp [hWk ha]
  by_cases h2 : x = -a
  · subst h2; simp [hak]
  simp [h1, h2]

/-- **With open half-lines the union misses the ends**: `a′ ∈ W_a` lies on no open half-line
joining `a` to `a′` (a fact about the open convention, not a refutation of the paper). -/
theorem coneAppui_ne_demiDroitesW (W : Set (Sphere E)) (a : Sphere E) :
    coneAppui W a ≠ demiDroitesW W a := by
  intro e
  have hak := (isLeast_coneAppui W a).1.2.2
  rw [e] at hak
  obtain ⟨h, ⟨hh, -⟩, hah⟩ := hak
  exact hh.notMem.2 hah

/-- **Déf. 1′ in the closed reading holds exactly when `W ⊄ {a, a′}`.** -/
theorem coneAppui_eq_demiDroitesFermeesW_iff {W : Set (Sphere E)} (hW : IsConvexPart W)
    {a : Sphere E} (ha : a ∈ W) : coneAppui W a = demiDroitesFermeesW W a ↔ ¬ W ⊆ {a, -a} := by
  have hak := (isLeast_coneAppui W a).1.2.2
  constructor
  · intro e hWa
    rw [e] at hak
    obtain ⟨_, ⟨h, ⟨-, b, -, hbW, hba, hbna⟩, -⟩, -⟩ := hak
    rcases hWa hbW with h' | h'
    · exact hba h'
    · exact hbna (mem_singleton_iff.1 h')
  · intro hWa
    obtain ⟨b, hbW, hb⟩ := not_subset.1 hWa
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hb
    obtain ⟨A, hA⟩ := exists_isRep a
    obtain ⟨B, hB0, rfl⟩ := exists_isRep b
    have hAB := linearIndependent_of_mem_F hA hB0 hb.1 hb.2
    have h0 : IsDemiDroiteJoignant a (halfLine A B) ∧
        ∃ b ∈ halfLine A B, b ∈ W ∧ b ≠ a ∧ b ≠ -a :=
      ⟨⟨A, B, hA, hAB, rfl⟩, mk B hB0, (mk_mem_halfLine hB0).2 ⟨0, 1, one_pos, by simp⟩, hbW, hb⟩
    rw [coneAppui_eq_insert_demiDroitesW hW ha]
    ext x
    constructor
    · intro hx
      rcases hx with rfl | rfl | ⟨h, hh, hxh⟩
      · exact ⟨_, ⟨_, h0, rfl⟩, mem_insert _ _⟩
      · exact ⟨_, ⟨_, h0, rfl⟩, mem_insert_of_mem _ (mem_insert _ _)⟩
      · exact ⟨_, ⟨h, hh, rfl⟩, mem_insert_of_mem _ (mem_insert_of_mem _ hxh)⟩
    · rintro ⟨_, ⟨h, hh, rfl⟩, hx⟩
      rcases hx with rfl | rfl | hxh
      · exact mem_insert _ _
      · exact mem_insert_of_mem _ (mem_insert _ _)
      · exact mem_insert_of_mem _ (mem_insert_of_mem _ ⟨h, hh, hxh⟩)

/-- **The degenerate instance `W = {a}`, Déf. 1**: `W_a = {a, a′}`. -/
theorem coneAppui_singleton (a : Sphere E) : coneAppui {a} a = {a, -a} := by
  refine (isLeast_coneAppui {a} a).unique ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [← closedSeg_neg_self]; exact isConvexPart_closedSeg _ _
  · exact singleton_subset_iff.2 (mem_insert _ _)
  · exact mem_insert_of_mem _ rfl
  · rintro k ⟨-, hk, hak⟩
    exact insert_subset (hk rfl) (singleton_subset_iff.2 hak)

/-- **The degenerate instance `W = {a}`, Déf. 1′**: no half-line meets `{a}` off `a, a′`. -/
theorem demiDroitesW_singleton (a : Sphere E) : demiDroitesW {a} a = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun x hx => ?_
  obtain ⟨h, ⟨-, b, -, hbW, hba, -⟩, -⟩ := hx
  exact hba hbW

theorem demiDroitesFermeesW_singleton (a : Sphere E) : demiDroitesFermeesW {a} a = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun x hx => ?_
  obtain ⟨_, ⟨h, ⟨-, b, -, hbW, hba, -⟩, -⟩, -⟩ := hx
  exact hba hbW

/-- **Déf. 1′ (closed half-lines) fails in a degenerate case**: there is a convex `W ∋ a` with
`W_a` not the union (any nonzero `E`; here `W = {a}`). -/
theorem not_def1prime_closed [Nontrivial E] :
    ¬ ∀ (W : Set (Sphere E)) (a : Sphere E), IsConvexPart W → a ∈ W →
      coneAppui W a = demiDroitesFermeesW W a := by
  intro h
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have e := h {mk v hv} (mk v hv) (isConvexPart_singleton_pt _) rfl
  rw [coneAppui_singleton, demiDroitesFermeesW_singleton] at e
  exact (insert_nonempty _ _).ne_empty e

/-! ### Déf. 2 — the contingent -/

section Contingent

variable [TopologicalSpace E]

/-- **Déf. 2** (`bzdef:c3s4d2_contingent`): the *contingent* of `W` at `a`, the closure of the
supporting cone `W_a`. -/
def contingent (W : Set (Sphere E)) (a : Sphere E) : Set (Sphere E) := closure (coneAppui W a)

theorem isClosed_contingent (W : Set (Sphere E)) (a : Sphere E) : IsClosed (contingent W a) :=
  isClosed_closure

theorem coneAppui_subset_contingent (W : Set (Sphere E)) (a : Sphere E) :
    coneAppui W a ⊆ contingent W a :=
  subset_closure

variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T1Space E]

/-- The closure of a convex part is a convex part. -/
theorem IsConvexPart.closure {k : Set (Sphere E)} (hk : IsConvexPart k) :
    IsConvexPart (closure k) := by
  unfold IsConvexPart at hk ⊢
  have e : insert (0 : E) (F (_root_.closure k)) = _root_.closure (insert 0 (F k)) := by
    rw [F_closure, insert_eq, insert_eq, closure_union, closure_singleton, union_sdiff_self]
  rw [e]
  exact hk.closure

/-- The contingent is a convex part. -/
theorem isConvexPart_contingent (W : Set (Sphere E)) (a : Sphere E) :
    IsConvexPart (contingent W a) :=
  (isLeast_coneAppui W a).1.1.closure

/-- **The contingent is the smallest closed convex part containing `W` and `a′`.** -/
theorem isLeast_contingent (W : Set (Sphere E)) (a : Sphere E) :
    IsLeast {k | IsConvexPart k ∧ IsClosed k ∧ W ⊆ k ∧ -a ∈ k} (contingent W a) := by
  obtain ⟨⟨-, hW, ha⟩, hmin⟩ := isLeast_coneAppui W a
  refine ⟨⟨isConvexPart_contingent W a, isClosed_contingent W a,
    hW.trans (coneAppui_subset_contingent W a), coneAppui_subset_contingent W a ha⟩, ?_⟩
  rintro k ⟨hk, hkc, hWk, hak⟩
  exact closure_minimal (hmin ⟨hk, hWk, hak⟩) hkc

end Contingent

/-! ### Closed segments and the instance -/

/-- The supporting cone at an end `a` of a closed arc `[a, b]`, `b ≠ a, a′`: the closed half-line
`s({αA + βB | β ≥ 0} − {O})`. -/
theorem coneAppui_closedSeg {A B : E} (hAB : LinearIndependent ℝ ![A, B]) :
    coneAppui (closedSeg (mk A (hAB.ne_zero 0)) (mk B (hAB.ne_zero 1))) (mk A (hAB.ne_zero 0)) =
      ofCone {M | ∃ α β : ℝ, 0 ≤ β ∧ M = α • A + β • B} := by
  have hA0 := hAB.ne_zero 0
  have hB0 := hAB.ne_zero 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hA0 hB0
  have haW : mk A hA0 ∈ closedSeg (mk A hA0) (mk B hB0) := left_mem_closedSeg _ _
  have hbW : mk B hB0 ∈ closedSeg (mk A hA0) (mk B hB0) := right_mem_closedSeg _ _
  rw [coneAppui_eq_ofCone (isConvexPart_closedSeg _ _) haW (isRep_mk A hA0)]
  congr 1
  ext M
  constructor
  · rintro ⟨l, P, ⟨hP0, hPW⟩, rfl⟩
    rw [closedSeg_mk, segOf] at hPW
    obtain ⟨u, hu, ⟨s, t, hs, ht, -, rfl⟩, hmk⟩ := mem_ofCone.1 hPW
    obtain ⟨c, hc, hcP⟩ := (mk_eq_mk_iff_exists_pos hu hP0).1 hmk
    refine ⟨l + c * s, c * t, by positivity, ?_⟩
    rw [← hcP]
    module
  · rintro ⟨α, β, hβ, rfl⟩
    rcases hβ.lt_or_eq with hβ | rfl
    · exact ⟨α, β • B, smul_mem_F ⟨hB0, hbW⟩ hβ, rfl⟩
    · exact ⟨α - 1, A, ⟨hA0, haW⟩, by module⟩

end Sphere

/-! #### The instance on `S(1)` -/

namespace ConeAppuiInstance

open Sphere

/-- `e₀ = (1, 0)`. -/
def e0 : Fin 2 → ℝ := ![1, 0]

/-- `e₁ = (0, 1)`. -/
def e1 : Fin 2 → ℝ := ![0, 1]

theorem e0_ne_zero : e0 ≠ 0 := by
  intro h; have := congrFun h 0; simp [e0] at this

theorem e1_ne_zero : e1 ≠ 0 := by
  intro h; have := congrFun h 1; simp [e1] at this

theorem linearIndependent_e0_e1 : LinearIndependent ℝ ![e0, e1] := by
  refine LinearIndependent.pair_iff.2 fun s t h => ⟨?_, ?_⟩
  · simpa [e0, e1] using congrFun h 0
  · simpa [e0, e1] using congrFun h 1

/-- The point `a = s(e₀)` of `S(1)`. -/
def a0 : S 1 := mk e0 e0_ne_zero

/-- The closed quarter arc `W = [s(e₀), s(e₁)]` of `S(1)`. -/
def arcS1 : Set (S 1) := closedSeg a0 (mk e1 e1_ne_zero)

/-- The second coordinate, `x ↦ x₁`, a continuous linear form. -/
def l1 : (Fin 2 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 1

theorem isConvexPart_arcS1 : IsConvexPart arcS1 := isConvexPart_closedSeg _ _

theorem a0_mem_arcS1 : a0 ∈ arcS1 := left_mem_closedSeg _ _

/-- **The instance, Déf. 1**: the supporting cone at the end `a` of the arc is the closed
hemisphere `{x₁ ≥ 0}`. -/
theorem coneAppui_arcS1 : coneAppui arcS1 a0 = closedHemisphere (l1 : Module.Dual ℝ (Fin 2 → ℝ)) := by
  have := coneAppui_closedSeg linearIndependent_e0_e1
  rw [arcS1, a0, this, closedHemisphere]
  congr 1
  ext v
  simp only [mem_setOf_eq]
  constructor
  · rintro ⟨α, β, hβ, rfl⟩
    simpa [l1, e0, e1] using hβ
  · intro hv
    refine ⟨v 0, v 1, by simpa [l1] using hv, ?_⟩
    ext i; fin_cases i <;> simp [e0, e1]

/-- **The instance, Déf. 2**: the contingent is the same closed hemisphere. -/
theorem contingent_arcS1 :
    contingent arcS1 a0 = closedHemisphere (l1 : Module.Dual ℝ (Fin 2 → ℝ)) := by
  have hl : l1 ≠ 0 := by
    intro h; have := congrArg (fun f : (Fin 2 → ℝ) →L[ℝ] ℝ => f e1) h; simp [l1, e1] at this
  rw [contingent, coneAppui_arcS1, ← closure_openHemisphere hl, closure_closure]

/-- The instance is not degenerate: `W_a ≠ W`. -/
theorem arcS1_ne_coneAppui : arcS1 ≠ coneAppui arcS1 a0 := by
  intro h
  have hneg : -a0 ∈ arcS1 := h ▸ (isLeast_coneAppui arcS1 a0).1.2.2
  rw [arcS1, a0, neg_mk, closedSeg_mk, segOf] at hneg
  obtain ⟨u, hu, ⟨s, t, hs, ht, -, rfl⟩, hmk⟩ := mem_ofCone.1 hneg
  obtain ⟨c, hc, hcu⟩ := (mk_eq_mk_iff_exists_pos hu _).1 hmk
  have := congrFun hcu 0
  simp [e0, e1] at this
  nlinarith

/-- **The instance, Déf. 1′ (closed reading)**: the arc is not inside `{a, a′}`, so `W_a` is the
union of the closed half-lines. -/
theorem def1prime_closed_arcS1 : coneAppui arcS1 a0 = demiDroitesFermeesW arcS1 a0 := by
  refine (coneAppui_eq_demiDroitesFermeesW_iff isConvexPart_arcS1 a0_mem_arcS1).2 fun hW => ?_
  have hb : mk e1 e1_ne_zero ∈ arcS1 := right_mem_closedSeg _ _
  rcases hW hb with h | h
  · obtain ⟨c, -, hc⟩ := (mk_eq_mk_iff_exists_pos e1_ne_zero e0_ne_zero).1 h
    have := congrFun hc 0
    simp [e0, e1] at this
  · rw [a0, neg_mk] at h
    obtain ⟨c, -, hc⟩ := (mk_eq_mk_iff_exists_pos e1_ne_zero _).1 (mem_singleton_iff.1 h)
    have := congrFun hc 0
    simp [e0, e1] at this

end ConeAppuiInstance

end Benzecri
