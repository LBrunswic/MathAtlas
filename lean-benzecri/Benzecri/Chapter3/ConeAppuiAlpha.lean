import Benzecri.Chapter3.FacettesSphere
import Benzecri.Chapter3.Dualite

/-!
# Chapter 3 § 4 — α(W) through the supporting cone (Props. 1–3) and the orthogonality of points (Déf. 3)

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 3 § 4, journal pp. 273–274; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch3.tex` (TO BE CHECKED BY THE AUTHOR, OQ-160).
Target T-bz-c3-cone-appui-alpha. Props. 1–2 over arbitrary real vector spaces (no topology);
Déf. 3 and Prop. 3 on `S(n)` with the dot product (`dotPairing`).

* `bzprop:c3s4p1_alpha_cone_appui` — `benzecri1960_ch3.tex:907` (Prop. 1, l.907–922; proof
  l.924–939) — NOT marked (a finding, OQ-162 (a)): `Benzecri.Sphere.prop1_coneAppui`, true with
  (2) read « rencontre $W$ en un point distinct de $a$, $a'$ » (half-lines with their ends
  excluded); false with closed half-lines, the reading recorded for Déf. 1′
  (`prop1_instance_end`). See SCOPE. The theorem: for `W` convex, `a, b ∈ W`, if `b ≠ a, a′` the
  four properties (1) `AlphaK W a b`, (2) `DemiDroitesRencontrent W a b`, (3) `-b ∈ coneAppui W a`,
  (4) `coneAppui W b ⊆ coneAppui W a` are equivalent (`List.TFAE`); if `b = a` or `b = a′`,
  (1), (3), (4) are. Steps: `alphaK_iff_halfLine_neg`, `demiDroitesRencontrent_iff`,
  `neg_mem_coneAppui_iff_halfLine_neg`, `neg_mem_coneAppui_iff_subset`.
* **`bzprop:c3s4p2_dual_cone_appui_sature`** — `benzecri1960_ch3.tex:941` (Prop. 2, l.941–949;
  proof l.953–968) — `Benzecri.Sphere.prop2_coneAppui`, for any bilinear form `B` (hypothesis (a)
  of § 3 only); the proof's description of `F∘D(W_a)`: `mk_mem_D_coneAppui_iff`.
* **`bzdef:c3s4d3_orthogonalite_points`** — `benzecri1960_ch3.tex:974` (Déf. 3, l.974–984) —
  `Benzecri.Sphere.OrthPts`; independent of the representatives (`orthPts_iff`), symmetric
  (`orthPts_comm`), and « $\langle m,p\rangle=0$ ssi $D(\{p\})$ contient $m$ et $m'$ »
  (`orthPts_iff_D`).
* **`bzprop:c3s4p3_dual_cone_appui`** — `benzecri1960_ch3.tex:986` (Prop. 3, l.986–989; proof
  l.991–996) — `Benzecri.Sphere.prop3_coneAppui` (with `a ∈ W`, which Déf. 1 presupposes in
  writing `W_a`; see SCOPE, `D_coneAppui_empty_ne`, `D_coneAppui_singleton_ne`).
* Instances on `S(1)`, the closed quarter arc `W = [a, b]`, `a = s(e₀)`, `b = s(e₁)`, `c` its
  midpoint (`Benzecri.ConeAppuiAlphaInstance`): `prop1_instance_mid` ((1) true: `c α a`,
  `a′ ∈ W_c`, `W_a ⊆ W_c`), `prop1_instance_end` ((1) false: `¬ a α b`, `b′ ∉ W_a`, while both
  closed half-lines meet `W`),
  `prop2_instance` (`D(W_a) ⊊ D(W)`), `prop3_instance` (`D(W_a) = {b}`), `def3_instance`.

> **Proposition 1.** Soient $W\in K(S(E))$, $a$, $b\in W$, $a'$, $b'$ les points diamétralement
> opposés à $a$ et $b$. Si $b\neq a$, $b\neq a'$, les quatre propriétés suivantes sont
> équivalentes : (1) $a\,\alpha(W)\,b$; (2) Sur la droite qui joint $a$ et $b$, chacune des deux
> demi-droites délimitées par $a$ et $a'$ rencontre $W$; (3) $b'\in W_a$; (4) $W_b\subset W_a$.
> Si $b=a$ ou $b=a'$, les propriétés (1), (3), (4) sont équivalentes.
>
> **Proposition 2.** Soient $E$, $E'$ deux espaces vectoriels. On suppose définie une forme
> bilinéaire sur le produit $E\times E'$ [*cf.* § 3, *a*)]. Soit $W\subset K(S(E))$, $a\in W$, on a
> $D(W_a)\subset D(W)$, et si $m'_1\in D(W_a)$, $m'_2\in D(W)$ et $m'_1\,\alpha(D(W))\,m'_2$,
> alors $m'_2\in D(W_a)$.
>
> Nous supposerons maintenant que l'espace $E$ est $\R^{n+1}$, canoniquement identifié à son dual
> au moyen de la forme $\sum_i x_iy_i$.
>
> **Définition 3.** Soient $m$, $p$ deux points de $S(n)$; $M$, $P$ deux points de
> $\R^{n+1}-\{O\}$ se projetant sur $m$ et $p$. Si $\langle M, P\rangle=0$, nous écrirons encore
> $\langle m, p\rangle=0$. Il est clair que cette définition ne dépend pas du choix de $M$ et de $P$
> et qu'elle est symétrique en $m$ et $p$. On peut encore l'énoncer : $\langle m, p\rangle=0$ si et
> seulement si $D(\{p\})$ contient $m$ et le point diamétralement opposé à $m$.
>
> **Proposition 3.** Soit $a$ un point de $S(n)$; $W\in K(S(n))$; alors
> $D(W_a)=\{m\mid m\in D(W),\ \langle m, a\rangle=0\}$.

## The proofs formalized

Prop. 1: take representatives `A`, `B` (independent, as `b ≠ a, a′`). The line joining `a`, `b`
is `s(span{A, B} − O)` (`supportK_pair`) and its two half-lines delimited by `a`, `a′` are
`{αA + βB}` and `{αA − βB}`, `β > 0` (`eq_halfLine_of_subset`); the first meets `W` at `b`, so
(2) says the second meets `W`. (1): `A + ε(A − B) = (1+ε)A + ε(−B) ∈ F(W)` for some `ε > 0`
(`alphaW_iff_extend` through `alphaK_iff`), a point of the second half-line; conversely from
`αA − βB ∈ F(W)` the combination `sA + t(αA − βB)` with `t = 1/(|α|+1)` gives `ε = tβ`.
(3): by Déf. 1″ (`coneAppui_eq_ofCone`), `−B = λA + P` with `P ∈ F(W)`, i.e. `P = −λA − B` on the
second half-line. (3) ⇔ (4) is the minimality of Déf. 1 (`isLeast_coneAppui`). If `b = a` or
`b = a′`, (1), (3), (4) all hold. Prop. 2: as printed; `m′ ∈ D(W_a)` iff `m′ ∈ D(W)` and
`⟨A, m′⟩ = 0` (Déf. 1″: `F(W_a) ∪ {O} = {λA + P}`), and from `M′₁ + ε(M′₁ − M′₂) ∈ F∘D(W) ∪ {O}`,
`0 ≤ ⟨A, M′₁ + ε(M′₁ − M′₂)⟩ = −ε⟨A, M′₂⟩ ≤ 0`. Prop. 3: the same description for the dot
product (the printed proof goes through the contingent and Prop. 2 of § 3; the direct route is
shorter and needs no topology).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| Prop. 1: « $W\in K(S(E))$ », `E` a real vector space | ✓ carried: `IsConvexPart W`, any dimension, no topology |
| Prop. 1: « $a$, $b\in W$ » | ✓ carried |
| Prop. 1: « $b\neq a$, $b\neq a'$ » / « $b=a$ ou $b=a'$ » | ✓ carried: the two conjuncts of `prop1_coneAppui` |
| Prop. 1 (1): « $a\,\alpha(W)\,b$ » | ✓ carried: `AlphaK W a b`, α(k) of § 1 Déf. 4 (the printed « cf. § 2 déf. 3 » is flagged `[sic]`) |
| Prop. 1 (2): « la droite qui joint $a$ et $b$ » | reading: `supportK {a, b}`, the least linear subvariety containing `a`, `b` (`= s(span{A,B} − O)`, `supportK_pair`) |
| Prop. 1 (2): « les deux demi-droites délimitées par $a$ et $a'$ », « rencontre $W$ » | ⚠ read (OQ-162 (a)): Ch. 1's half-lines `IsDemiDroiteJoignant a h`, ends excluded, i.e. « rencontre $W$ en un point distinct de $a$, $a'$ »; on closed half-lines (Déf. 1′'s recorded reading) (2) is always true (both contain `a ∈ W`) and (1) ⇔ (2) fails (`prop1_instance_end`) |
| Prop. 1 (3), (4): `W_a`, `W_b` | ✓ carried: `coneAppui` (Déf. 1) |
| Prop. 2: « deux espaces vectoriels », « une forme bilinéaire » (§ 3 (a)) | ✓ carried: `B : E →ₗ[ℝ] E' →ₗ[ℝ] ℝ`, no topology, no hypothesis (b)–(d) |
| Prop. 2: « $W\subset K(S(E))$ » | ✓ carried as `IsConvexPart W` (the `[sic]` reading `W ∈ K(S(E))`) |
| Prop. 2: « $a\in W$ » | ✓ carried |
| Prop. 2: « $m'_1\,\alpha(D(W))\,m'_2$ » | ✓ carried: `AlphaK (D B W) m₁ m₂`, `D(W)` a convex part of `S(E′)` (`claim_a_convexPart`) |
| Déf. 3: `E = ℝⁿ⁺¹`, the form `∑ xᵢyᵢ` | ✓ carried: `dotPairing n` on `S n` |
| Déf. 3: `M`, `P` « se projetant sur $m$ et $p$ » | ✓ carried: defined on `someVector`, any representatives by `orthPts_iff` |
| Prop. 3: « $a$ un point de $S(n)$; $W\in K(S(n))$ » | ✓ carried: `IsConvexPart W`, and `a ∈ W`, the domain of Déf. 1 (« $W\in K(S(E))$, $a\in W$ ») which the notation `W_a` presupposes (question) |

## SCOPE (disclosed)

* Everything is proved; no `sorry`. **Prop. 1 is not marked** (finding): no single convention
  for « demi-droite » makes both Déf. 1′ (l.889) and Prop. 1 (2) (l.913) true as printed. With
  closed half-lines (OQ-162 (a)'s reading of Déf. 1′) (2) is vacuous and (1) ⇔ (2) fails
  (`prop1_instance_end`); with half-lines whose ends are excluded, i.e. (2) as « rencontre $W$
  en un point distinct de $a$, $a'$ », Prop. 1 holds in full (`prop1_coneAppui`), while Déf. 1′
  then misses `a`, `a′` (`coneAppui_ne_demiDroitesW`, strict `Chapter3/ConeAppui`).
* Prop. 3 is read with `a ∈ W` (question), the domain of Déf. 1. The library's `coneAppui` is
  defined for every `a`; outside `a ∈ W` Prop. 3's identity fails (`D_coneAppui_empty_ne`,
  `W = ∅`, every `n`; `D_coneAppui_singleton_ne`, `W = {b}`, `b ≠ a, a′`, on `S(1)`), which is
  outside Déf. 1's domain, not a refutation of the paper.
* The misprints flagged `[sic]` in the transcription are formalized in their evident reading:
  Prop. 1's « cf. § 2 déf. 3 » (α(W) is § 1's; OQ-160 (b) moves only the ledger edge), Prop. 2's
  « $W\subset K(S(E))$ » (read `∈`) and « $\langle AM''_2\rangle$ » (read `M'_2`).
* Prop. 2's « cf. § 3, a) » is the hypothesis of a bilinear form, carried as the argument `B`.
* General lemmas proved here (candidates to move upstream): `supportK_pair`,
  `halfLine_subset_linearSubvariety_of_mem`, `halfLine_smul_add`, `eq_halfLine_of_subset`,
  `mk_mem_D_coneAppui_iff`, `dotPairing_comm`, `dotPairing_self_eq_zero`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open Set

namespace Benzecri

namespace Sphere

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-! ### Prop. 1 — the line joining `a` and `b`, and its two half-lines -/

/-- **Prop. 1 (2)**: « sur la droite qui joint $a$ et $b$, chacune des deux demi-droites
délimitées par $a$ et $a'$ rencontre $W$ ». The line joining `a` and `b` is the least linear
subvariety containing them, `supportK {a, b}`; a half-line delimited by `a`, `a′` is
`IsDemiDroiteJoignant a h` (Chapter 1, Déf. 4, Exemples, ends excluded). -/
def DemiDroitesRencontrent (W : Set (Sphere E)) (a b : Sphere E) : Prop :=
  ∀ h : Set (Sphere E), IsDemiDroiteJoignant a h → h ⊆ supportK {a, b} → (h ∩ W).Nonempty

/-- **(1) ⇔ the half-line on the side of `b′` meets `W`**: for `A`, `B` independent
representatives of `a`, `b ∈ W`, `a α(W) b` iff the half-line `{αA − βB | β > 0}` meets `W`. -/
theorem alphaK_iff_halfLine_neg {W : Set (Sphere E)} (hW : IsConvexPart W) {a b : Sphere E}
    (ha : a ∈ W) (hb : b ∈ W) {A B : E} (hA : IsRep A a) (hB : IsRep B b)
    (hAB : LinearIndependent ℝ ![A, B]) : AlphaK W a b ↔ (halfLine A (-B) ∩ W).Nonempty := by
  rw [alphaK_iff hW hA hB, alphaW_iff_extend (convex_kPrime hW)]
  constructor
  · rintro ⟨-, -, ε, hε, hC⟩
    have hC0 : (1 + ε) • A + ε • (-B) ≠ 0 :=
      ne_zero_of_linearIndependent (linearIndependent_neg_right hAB) hε.ne'
    have e : A + ε • (A - B) = (1 + ε) • A + ε • (-B) := by module
    rw [e] at hC
    exact ⟨mk _ hC0, (mk_mem_halfLine hC0).2 ⟨1 + ε, ε, hε, rfl⟩,
      mem_of_isRep_of_mem_kPrime (isRep_mk _ hC0) hC⟩
  · rintro ⟨x, hxh, hxW⟩
    induction x using ind with
    | h u hu =>
    obtain ⟨α, β, hβ, rfl⟩ := (mk_mem_halfLine hu).1 hxh
    have huk : α • A + β • -B ∈ kPrime W := mem_kPrime_of_isRep (isRep_mk _ hu) hxW
    have hAk : A ∈ kPrime W := mem_kPrime_of_isRep hA ha
    set t : ℝ := 1 / (|α| + 1) with ht_def
    have ht : 0 < t := by positivity
    have htα : t * |α| ≤ 1 := by
      rw [ht_def, div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]; linarith
    have hs : 0 ≤ 1 + t * β - t * α := by
      have : t * α ≤ t * |α| := mul_le_mul_of_nonneg_left (le_abs_self α) ht.le
      nlinarith [mul_pos ht hβ]
    refine ⟨hAk, mem_kPrime_of_isRep hB hb, t * β, mul_pos ht hβ, ?_⟩
    have e : A + (t * β) • (A - B) = (1 + t * β - t * α) • A + t • (α • A + β • -B) := by module
    rw [e]
    exact add_mem_kPrime hW (smul_mem_kPrime hAk hs) (smul_mem_kPrime huk ht.le)

/-- **(3) ⇔ the half-line on the side of `b′` meets `W`** (through Déf. 1″, `coneAppui_eq_ofCone`):
`b′ ∈ W_a` iff `{αA − βB | β > 0}` meets `W`. -/
theorem neg_mem_coneAppui_iff_halfLine_neg {W : Set (Sphere E)} (hW : IsConvexPart W)
    {a b : Sphere E} (ha : a ∈ W) {A B : E} (hA : IsRep A a) (hB : IsRep B b) :
    -b ∈ coneAppui W a ↔ (halfLine A (-B) ∩ W).Nonempty := by
  obtain ⟨hB0, rfl⟩ := hB
  rw [coneAppui_eq_ofCone hW ha hA, neg_mk, mk_mem_ofCone_iff (isPosCone_coneAppuiVec W A)]
  constructor
  · rintro ⟨l, P, hP, e⟩
    refine ⟨mk P hP.1, (mk_mem_halfLine hP.1).2 ⟨-l, 1, one_pos, ?_⟩, hP.2⟩
    rw [one_smul, e]; module
  · rintro ⟨x, hxh, hxW⟩
    induction x using ind with
    | h u hu =>
    obtain ⟨α, β, hβ, rfl⟩ := (mk_mem_halfLine hu).1 hxh
    refine ⟨-α / β, (1 / β) • (α • A + β • -B), smul_mem_F ⟨hu, hxW⟩ (by positivity), ?_⟩
    rw [smul_add, smul_smul, smul_smul, ← add_assoc, ← add_smul]
    have h1 : -α / β + 1 / β * α = 0 := by field_simp; ring
    have h2 : 1 / β * β = 1 := by field_simp
    rw [h1, h2, zero_smul, zero_add, one_smul]

/-- **(3) ⇔ (4)** (through Déf. 1, for every `W`, `a`, `b`): `b′ ∈ W_a` iff `W_b ⊆ W_a`. -/
theorem neg_mem_coneAppui_iff_subset (W : Set (Sphere E)) (a b : Sphere E) :
    -b ∈ coneAppui W a ↔ coneAppui W b ⊆ coneAppui W a := by
  have ha := (isLeast_coneAppui W a).1
  have hb := isLeast_coneAppui W b
  exact ⟨fun h => hb.2 ⟨ha.1, ha.2.1, h⟩, fun h => h hb.1.2.2⟩

/-- The line joining `a` and `b`, `supportK {a, b}`, is `s(span {A, B} − {O})`. -/
theorem supportK_pair {a b : Sphere E} {A B : E} (hA : IsRep A a) (hB : IsRep B b) :
    supportK {a, b} = linearSubvariety (Submodule.span ℝ {A, B}) := by
  unfold supportK
  congr 1
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro v ⟨hv, hvab⟩
    rcases hvab with h | h
    · obtain ⟨c, -, rfl⟩ := hA.exists_pos ⟨hv, h⟩
      exact Submodule.smul_mem _ _ (Submodule.subset_span (mem_insert _ _))
    · obtain ⟨c, -, rfl⟩ := hB.exists_pos ⟨hv, mem_singleton_iff.1 h⟩
      exact Submodule.smul_mem _ _ (Submodule.subset_span (mem_insert_of_mem _ rfl))
  · rw [Submodule.span_le]
    refine insert_subset (Submodule.subset_span ⟨hA.1, Or.inl hA.2⟩) ?_
    exact singleton_subset_iff.2 (Submodule.subset_span ⟨hB.1, Or.inr hB.2⟩)

theorem halfLine_subset_linearSubvariety_of_mem {A w : E} {L : Submodule ℝ E} (hA : A ∈ L)
    (hw : w ∈ L) : halfLine A w ⊆ linearSubvariety L :=
  ofCone_subset_ofCone fun _ ⟨_, _, _, e⟩ => e ▸ L.add_mem (L.smul_mem _ hA) (L.smul_mem _ hw)

/-- Changing the representatives of a half-line. -/
theorem halfLine_smul_add {A C : E} {c x y : ℝ} (hc : c ≠ 0) (hy : 0 < y) :
    halfLine (c • A) (x • A + y • C) = halfLine A C := by
  unfold halfLine
  congr 1
  ext u
  constructor
  · rintro ⟨α, β, hβ, rfl⟩
    exact ⟨α * c + β * x, β * y, mul_pos hβ hy, by module⟩
  · rintro ⟨α, β, hβ, rfl⟩
    refine ⟨(α - β / y * x) / c, β / y, div_pos hβ hy, ?_⟩
    rw [smul_add, smul_smul, smul_smul, smul_smul, ← add_assoc, ← add_smul]
    congr 1
    · congr 1; field_simp; ring
    · congr 1; field_simp

/-- **The two half-lines of the line `ab` delimited by `a`, `a′`**: `{αA + βB}` and `{αA − βB}`
(`β > 0`), and no other. -/
theorem eq_halfLine_of_subset {a : Sphere E} {A B : E} (hA : IsRep A a)
    {h : Set (Sphere E)} (hh : IsDemiDroiteJoignant a h)
    (hsub : h ⊆ linearSubvariety (Submodule.span ℝ {A, B})) :
    h = halfLine A B ∨ h = halfLine A (-B) := by
  obtain ⟨A', w, hA', hA'w, rfl⟩ := hh
  obtain ⟨c, hc, rfl⟩ := hA.exists_pos hA'
  have hw0 : w ≠ 0 := by simpa using hA'w.ne_zero 1
  have hw : w ∈ Submodule.span ℝ {A, B} :=
    (mk_mem_linearSubvariety hw0).1 (hsub ((mk_mem_halfLine hw0).2 ⟨0, 1, one_pos, by simp⟩))
  obtain ⟨x, y, rfl⟩ := Submodule.mem_span_pair.1 hw
  have hy : y ≠ 0 := by
    rintro rfl
    have := (LinearIndependent.pair_iff.1 hA'w x (-c) (by module)).2
    exact hc.ne' (neg_eq_zero.1 this)
  rcases lt_or_gt_of_ne hy with hy | hy
  · right
    have e : x • A + y • B = x • A + (-y) • -B := by module
    rw [e]
    exact halfLine_smul_add hc.ne' (neg_pos.2 hy)
  · left
    exact halfLine_smul_add hc.ne' hy

/-- **(2) ⇔ the half-line on the side of `b′` meets `W`**, for `b ∈ W`. -/
theorem demiDroitesRencontrent_iff {W : Set (Sphere E)} {a b : Sphere E} (hb : b ∈ W) {A B : E}
    (hA : IsRep A a) (hB : IsRep B b) (hAB : LinearIndependent ℝ ![A, B]) :
    DemiDroitesRencontrent W a b ↔ (halfLine A (-B) ∩ W).Nonempty := by
  have hL : ∀ w ∈ Submodule.span ℝ {A, B}, halfLine A w ⊆ supportK {a, b} := fun w hw => by
    rw [supportK_pair hA hB]
    exact halfLine_subset_linearSubvariety_of_mem (Submodule.subset_span (mem_insert _ _)) hw
  constructor
  · intro h
    exact h _ ⟨A, -B, hA, linearIndependent_neg_right hAB, rfl⟩
      (hL _ (Submodule.neg_mem _ (Submodule.subset_span (mem_insert_of_mem _ rfl))))
  · intro hN h hh hsub
    rw [supportK_pair hA hB] at hsub
    rcases eq_halfLine_of_subset hA hh hsub with rfl | rfl
    · obtain ⟨hB0, rfl⟩ := hB
      exact ⟨_, (mk_mem_halfLine hB0).2 ⟨0, 1, one_pos, by simp⟩, hb⟩
    · exact hN

/-- Prop. 1 (`bzprop:c3s4p1_alpha_cone_appui`, not marked): true with (2) read on half-lines whose
ends `a`, `a′` are excluded (`DemiDroitesRencontrent`); false with closed half-lines
(`prop1_instance_end`). -/
theorem prop1_coneAppui {W : Set (Sphere E)} (hW : IsConvexPart W) {a b : Sphere E}
    (ha : a ∈ W) (hb : b ∈ W) :
    (b ≠ a → b ≠ -a →
      [AlphaK W a b, DemiDroitesRencontrent W a b, -b ∈ coneAppui W a,
        coneAppui W b ⊆ coneAppui W a].TFAE) ∧
    (b = a ∨ b = -a →
      [AlphaK W a b, -b ∈ coneAppui W a, coneAppui W b ⊆ coneAppui W a].TFAE) := by
  constructor
  · intro h1 h2
    obtain ⟨A, hA⟩ := exists_isRep a
    obtain ⟨B, hB⟩ := exists_isRep b
    have hAB := linearIndependent_of_ne hA hB h1 h2
    tfae_have 1 ↔ 3 := (alphaK_iff_halfLine_neg hW ha hb hA hB hAB).trans
      (neg_mem_coneAppui_iff_halfLine_neg hW ha hA hB).symm
    tfae_have 2 ↔ 3 := (demiDroitesRencontrent_iff hb hA hB hAB).trans
      (neg_mem_coneAppui_iff_halfLine_neg hW ha hA hB).symm
    tfae_have 3 ↔ 4 := neg_mem_coneAppui_iff_subset W a b
    tfae_finish
  · intro hab
    have h3 : -b ∈ coneAppui W a := by
      rcases hab with rfl | rfl
      · exact (isLeast_coneAppui W b).1.2.2
      · rw [neg_neg]; exact (isLeast_coneAppui W a).1.2.1 ha
    have h1 : AlphaK W a b := by
      rcases hab with rfl | rfl
      · exact alphaK_refl ha
      · exact alphaK_of_eq_or_neg hW ha hb (Or.inr (neg_neg a).symm)
    tfae_have 1 ↔ 2 := iff_of_true h1 h3
    tfae_have 2 ↔ 3 := neg_mem_coneAppui_iff_subset W a b
    tfae_finish

variable {E' : Type*} [AddCommGroup E'] [Module ℝ E']

/-- **The dual of the supporting cone** (the proof of Prop. 2, « $F\circ D(W_a)\cup\{O\} =
\{M' \mid \langle AM'\rangle = 0;\ \langle MM'\rangle \geqq 0,\ \forall M \in F(W)\}$ »), for any
bilinear form: `m′ ∈ D(W_a)` iff `m′ ∈ D(W)` and `⟨A, m′⟩ = 0`. -/
theorem mk_mem_D_coneAppui_iff (B : E →ₗ[ℝ] E' →ₗ[ℝ] ℝ) {W : Set (Sphere E)}
    (hW : IsConvexPart W) {a : Sphere E} (ha : a ∈ W) {A : E} (hA : IsRep A a) {v : E'}
    (hv : v ≠ 0) : mk v hv ∈ D B (coneAppui W a) ↔ mk v hv ∈ D B W ∧ B A v = 0 := by
  have hU := F_coneAppui_union_zero hW ha hA
  have hmem : ∀ M : E, M ≠ 0 → (∃ l : ℝ, ∃ P ∈ F W, M = l • A + P) →
      M ∈ F (coneAppui W a) := by
    intro M hM h
    have : M ∈ F (coneAppui W a) ∪ {0} := by rw [hU]; exact h
    exact this.resolve_right hM
  have hAF : A ∈ F W := by obtain ⟨hA0, rfl⟩ := hA; exact ⟨hA0, ha⟩
  rw [mk_mem_D, mk_mem_D]
  constructor
  · intro h
    refine ⟨fun P hP => h P (hmem P hP.1 ⟨0, P, hP, by simp⟩), ?_⟩
    have h1 := h A (hmem A hA.ne_zero ⟨0, A, hAF, by simp⟩)
    have h2 := h (-A) (hmem (-A) (neg_ne_zero.2 hA.ne_zero) ⟨-2, A, hAF, by module⟩)
    rw [map_neg, LinearMap.neg_apply] at h2
    linarith
  · rintro ⟨h, h0⟩ m hm
    have : m ∈ F (coneAppui W a) ∪ {0} := Or.inl hm
    rw [hU] at this
    obtain ⟨l, P, hP, rfl⟩ := this
    rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, h0, smul_zero, zero_add]
    exact h P hP

/-- **Prop. 2** (`bzprop:c3s4p2_dual_cone_appui_sature`). -/
theorem prop2_coneAppui (B : E →ₗ[ℝ] E' →ₗ[ℝ] ℝ) {W : Set (Sphere E)} (hW : IsConvexPart W)
    {a : Sphere E} (ha : a ∈ W) :
    D B (coneAppui W a) ⊆ D B W ∧
      ∀ m₁ m₂ : Sphere E', m₁ ∈ D B (coneAppui W a) → m₂ ∈ D B W → AlphaK (D B W) m₁ m₂ →
        m₂ ∈ D B (coneAppui W a) := by
  refine ⟨claim_a_antitone B (isLeast_coneAppui W a).1.2.1, ?_⟩
  intro m₁ m₂ h₁ h₂ hα
  obtain ⟨A, hA⟩ := exists_isRep a
  have hAF : A ∈ F W := by obtain ⟨hA0, rfl⟩ := hA; exact ⟨hA0, ha⟩
  induction m₁ using ind with
  | h M₁ hM₁ =>
  induction m₂ using ind with
  | h M₂ hM₂ =>
  rw [mk_mem_D_coneAppui_iff B hW ha hA] at h₁ ⊢
  refine ⟨h₂, ?_⟩
  have hDW := claim_a_convexPart B W
  have hα' := (alphaK_iff hDW (isRep_mk _ hM₁) (isRep_mk _ hM₂)).1 hα
  obtain ⟨-, -, ε, hε, hC⟩ := (alphaW_iff_extend (convex_kPrime hDW)).1 hα'
  have hk : kPrime (D B W) = dualCone B (F W) := (claim_a_cone B W).1
  rw [hk] at hC
  have h3 := hC A hAF
  have h4 := (mk_mem_D B W hM₂).1 h₂ A hAF
  rw [map_add, map_smul, map_sub, h₁.2] at h3
  simp only [smul_eq_mul, zero_sub, mul_neg, zero_add, neg_nonneg] at h3
  have := mul_nonneg hε.le h4
  have h5 : ε * B A M₂ = 0 := le_antisymm h3 this
  exact (mul_eq_zero.1 h5).resolve_left hε.ne'

end Sphere

/-! ### Déf. 3 and Prop. 3 on `S(n)` -/

namespace Sphere

variable {n : ℕ}

theorem dotPairing_comm (M P : Fin (n + 1) → ℝ) : dotPairing n M P = dotPairing n P M := by
  rw [dotPairing_apply, dotPairing_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- **Déf. 3** (`bzdef:c3s4d3_orthogonalite_points`): `⟨m, p⟩ = 0`, read on the chosen
representatives (any representatives give the same relation, `orthPts_iff`). -/
def OrthPts (m p : S n) : Prop :=
  dotPairing n (Module.Ray.someVector m) (Module.Ray.someVector p) = 0

/-- **Déf. 3, « cette définition ne dépend pas du choix de $M$ et de $P$ »**. -/
theorem orthPts_iff {m p : S n} {M P : Fin (n + 1) → ℝ} (hM : IsRep M m) (hP : IsRep P p) :
    OrthPts m p ↔ dotPairing n M P = 0 := by
  obtain ⟨c, hc, rfl⟩ := (exists_isRep_someVector m).exists_pos hM
  obtain ⟨d, hd, rfl⟩ := (exists_isRep_someVector p).exists_pos hP
  unfold OrthPts
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  simp [hc.ne', hd.ne']

/-- **Déf. 3, « elle est symétrique en $m$ et $p$ »**. -/
theorem orthPts_comm {m p : S n} : OrthPts m p ↔ OrthPts p m := by
  unfold OrthPts
  rw [dotPairing_comm]

/-- **Déf. 3, « $\langle m, p\rangle=0$ si et seulement si $D(\{p\})$ contient $m$ et le point
diamétralement opposé à $m$ »**. -/
theorem orthPts_iff_D {m p : S n} :
    OrthPts m p ↔ m ∈ D (dotPairing n) {p} ∧ -m ∈ D (dotPairing n) {p} := by
  induction m using ind with
  | h M hM =>
  induction p using ind with
  | h P hP =>
  rw [orthPts_iff (isRep_mk M hM) (isRep_mk P hP), D_singleton, neg_mk,
    mk_mem_closedHemisphere, mk_mem_closedHemisphere, map_neg, dotPairing_comm]
  constructor
  · intro h; rw [h]; simp
  · rintro ⟨h1, h2⟩; linarith

/-- **Prop. 3** (`bzprop:c3s4p3_dual_cone_appui`). -/
theorem prop3_coneAppui (a : S n) {W : Set (S n)} (hW : IsConvexPart W) (ha : a ∈ W) :
    D (dotPairing n) (coneAppui W a) = {m | m ∈ D (dotPairing n) W ∧ OrthPts m a} := by
  ext m
  induction m using ind with
  | h v hv =>
  rw [mk_mem_D_coneAppui_iff _ hW ha (exists_isRep_someVector a), mem_setOf_eq,
    orthPts_iff (isRep_mk v hv) (exists_isRep_someVector a), dotPairing_comm]

theorem dotPairing_self_eq_zero {A : Fin (n + 1) → ℝ} (h : dotPairing n A A = 0) : A = 0 := by
  rw [dotPairing_apply] at h
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (A j))).1 h i
    (Finset.mem_univ _)
  exact mul_self_eq_zero.1 this

/-- **Prop. 3 needs `a ∈ W`** (which Déf. 1 presupposes in writing `W_a`): with the library's
`coneAppui`, defined for every `a`, the identity fails at `W = ∅` (`W_a = {a′}`). -/
theorem D_coneAppui_empty_ne (a : S n) :
    D (dotPairing n) (coneAppui ∅ a) ≠ {m | m ∈ D (dotPairing n) ∅ ∧ OrthPts m a} := by
  have hc : coneAppui (∅ : Set (S n)) a = {-a} :=
    (isLeast_coneAppui ∅ a).unique ⟨⟨isConvexPart_singleton_pt _, empty_subset _, rfl⟩,
      fun _ hk => singleton_subset_iff.2 hk.2.2⟩
  rw [hc]
  intro e
  induction a using ind with
  | h A hA =>
  have hmem : -mk A hA ∈ D (dotPairing n) {-mk A hA} := by
    rw [neg_mk, D_singleton, mk_mem_closedHemisphere, dotPairing_apply]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  rw [e] at hmem
  have h2 := hmem.2
  rw [neg_mk, orthPts_iff (isRep_mk _ _) (isRep_mk A hA), map_neg, LinearMap.neg_apply,
    neg_eq_zero] at h2
  exact hA (dotPairing_self_eq_zero h2)

end Sphere

/-! ### Instances on `S(1)`: the closed quarter arc -/

namespace ConeAppuiAlphaInstance

open Sphere ConeAppuiInstance FacettesSphereInstance

/-- `v = (1, 1)`. -/
def v11 : Fin 2 → ℝ := ![1, 1]

theorem v11_ne_zero : v11 ≠ 0 := fun h => by simpa [v11] using congrFun h 0

/-- The midpoint `c = s(1, 1)` of the arc. -/
def c1 : S 1 := mk v11 v11_ne_zero

theorem c1_mem_arcS1 : c1 ∈ arcS1 := (mk_mem_arcS1_iff _).2 ⟨by simp [v11], by simp [v11]⟩

theorem b1_mem_arcS1 : b1 ∈ arcS1 := right_mem_closedSeg _ _

theorem a0_ne_c1 : a0 ≠ c1 := fun h => by
  have := (mk_eq_a0_iff v11_ne_zero).1 h.symm
  simp [v11] at this

theorem a0_ne_neg_c1 : a0 ≠ -c1 := fun h => by
  rw [c1, neg_mk] at h
  have := (mk_eq_a0_iff _).1 h.symm
  simp [v11] at this

theorem b1_ne_a0 : b1 ≠ a0 := fun h => by
  have := (mk_eq_a0_iff e1_ne_zero).1 h
  simp [e1] at this

theorem b1_ne_neg_a0 : b1 ≠ -a0 := fun h => by
  rw [a0, neg_mk] at h
  have := (mk_eq_b1_iff _).1 h.symm
  simp [e0] at this

/-- **Instance of Prop. 1, (1) true**: the midpoint `c` of the arc is α-below its end `a`, so
`a′ ∈ W_c` and `W_a ⊆ W_c`. -/
theorem prop1_instance_mid :
    AlphaK arcS1 c1 a0 ∧ -a0 ∈ coneAppui arcS1 c1 ∧ coneAppui arcS1 a0 ⊆ coneAppui arcS1 c1 := by
  have hα : AlphaK arcS1 c1 a0 := by
    rw [alphaK_iff isConvexPart_arcS1 (a := c1) (isRep_mk v11 v11_ne_zero)
      (b := a0) (isRep_mk e0 e0_ne_zero), kPrime_arcS1, alphaW_quadrant_iff]
    simp [v11, e0]
  have h := (prop1_coneAppui isConvexPart_arcS1 c1_mem_arcS1 a0_mem_arcS1).1 a0_ne_c1
    a0_ne_neg_c1
  exact ⟨hα, (h.out 0 2).1 hα, (h.out 0 3).1 hα⟩

/-- **Instance of Prop. 1, (1) false**: the end `a` of the arc is not α-below the other end
`b`, and `b′ ∉ W_a` (`W_a` is the closed hemisphere `{x₁ ≥ 0}`). Both closed half-lines of the
line `ab` delimited by `a`, `a′` meet `W` (at `a`): with closed half-lines, (2) holds while (1)
fails, so Prop. 1's (1) ⇔ (2) is false in that reading (the finding, OQ-162 (a)). -/
theorem prop1_instance_end :
    ¬ AlphaK arcS1 a0 b1 ∧ -b1 ∉ coneAppui arcS1 a0 ∧
      (insert a0 (insert (-a0) (halfLine e0 e1)) ∩ arcS1).Nonempty ∧
      (insert a0 (insert (-a0) (halfLine e0 (-e1))) ∩ arcS1).Nonempty := by
  have hn : -b1 ∉ coneAppui arcS1 a0 := by
    rw [coneAppui_arcS1, b1, neg_mk, mk_mem_closedHemisphere]
    simp [l1, e1]
  have h := (prop1_coneAppui isConvexPart_arcS1 a0_mem_arcS1 b1_mem_arcS1).1 b1_ne_a0
    b1_ne_neg_a0
  exact ⟨fun hα => hn ((h.out 0 2).1 hα), hn, ⟨a0, mem_insert _ _, a0_mem_arcS1⟩,
    ⟨a0, mem_insert _ _, a0_mem_arcS1⟩⟩

theorem mem_F_arcS1_iff {m : Fin 2 → ℝ} : m ∈ F arcS1 ↔ m ≠ 0 ∧ 0 ≤ m 0 ∧ 0 ≤ m 1 :=
  ⟨fun h => ⟨h.1, (mk_mem_arcS1_iff h.1).1 h.2⟩, fun h => ⟨h.1, (mk_mem_arcS1_iff h.1).2 h.2⟩⟩

theorem dotPairing_two (m v : Fin 2 → ℝ) : dotPairing 1 m v = m 0 * v 0 + m 1 * v 1 := by
  rw [dotPairing_apply, Fin.sum_univ_two]

/-- **Instance of Prop. 3**: the dual of the supporting cone at the end `a` of the arc is the
point `b`. -/
theorem prop3_instance : D (dotPairing 1) (coneAppui arcS1 a0) = {b1} := by
  rw [prop3_coneAppui a0 isConvexPart_arcS1 a0_mem_arcS1]
  ext m
  induction m using ind with
  | h v hv =>
  simp only [mem_setOf_eq, mem_singleton_iff]
  rw [mk_mem_D, orthPts_iff (isRep_mk v hv) (p := a0) (isRep_mk e0 e0_ne_zero), mk_eq_b1_iff,
    dotPairing_two]
  simp only [e0, Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, mul_zero, add_zero]
  constructor
  · rintro ⟨h, h0⟩
    refine ⟨h0, lt_of_le_of_ne ?_ fun h1 => hv (eq_zero_of_coords h0 h1.symm)⟩
    have := h e1 (mem_F_arcS1_iff.2 ⟨e1_ne_zero, by simp [e1], by simp [e1]⟩)
    simpa [dotPairing_two, e1] using this
  · rintro ⟨h0, h1⟩
    refine ⟨fun m hm => ?_, h0⟩
    obtain ⟨-, hm0, hm1⟩ := mem_F_arcS1_iff.1 hm
    rw [dotPairing_two, h0]
    nlinarith

/-- **Instance of Prop. 2**: the inclusion `D(W_a) ⊆ D(W)` is strict there (`a ∈ D(W)`). -/
theorem prop2_instance :
    D (dotPairing 1) (coneAppui arcS1 a0) ⊆ D (dotPairing 1) arcS1 ∧
      a0 ∈ D (dotPairing 1) arcS1 ∧ a0 ∉ D (dotPairing 1) (coneAppui arcS1 a0) := by
  refine ⟨(prop2_coneAppui _ isConvexPart_arcS1 a0_mem_arcS1).1, ?_, ?_⟩
  · show mk e0 e0_ne_zero ∈ _
    rw [mk_mem_D]
    intro m hm
    obtain ⟨-, hm0, -⟩ := mem_F_arcS1_iff.1 hm
    simpa [dotPairing_two, e0] using hm0
  · rw [prop3_instance]
    exact fun h => b1_ne_a0 (mem_singleton_iff.1 h).symm

/-- **Prop. 3 needs `a ∈ W`, a non-empty example**: on `S(1)`, `W = {b}` with `b ≠ a, a′`; then
`s(−1, 1)` lies in `D(W_a)` (`W_a ⊆ [b, a′]`) but is not orthogonal to `a`. -/
theorem D_coneAppui_singleton_ne :
    b1 ≠ a0 ∧ b1 ≠ -a0 ∧
      D (dotPairing 1) (coneAppui {b1} a0) ≠ {m | m ∈ D (dotPairing 1) {b1} ∧ OrthPts m a0} := by
  refine ⟨b1_ne_a0, b1_ne_neg_a0, ?_⟩
  have hw : (![-1, 1] : Fin 2 → ℝ) ≠ 0 := fun h => by simpa using congrFun h 0
  have hsub : coneAppui {b1} a0 ⊆ closedSeg b1 (-a0) :=
    (isLeast_coneAppui _ _).2 ⟨isConvexPart_closedSeg _ _,
      singleton_subset_iff.2 (left_mem_closedSeg _ _), right_mem_closedSeg _ _⟩
  have hm : mk _ hw ∈ D (dotPairing 1) (closedSeg b1 (-a0)) := by
    rw [mk_mem_D]
    rintro m ⟨hm0, hmS⟩
    rw [b1, a0, neg_mk, closedSeg_mk, segOf] at hmS
    obtain ⟨z, hz, ⟨s, t, hs, ht, -, rfl⟩, hzm⟩ := mem_ofCone.1 hmS
    obtain ⟨c, hc, rfl⟩ := (mk_eq_mk_iff_exists_pos hz hm0).1 hzm
    rw [dotPairing_two]
    simp [e0, e1]
    positivity
  intro e
  have h := claim_a_antitone _ hsub hm
  rw [e] at h
  have h2 := h.2
  rw [orthPts_iff (isRep_mk _ hw) (p := a0) (isRep_mk e0 e0_ne_zero), dotPairing_two] at h2
  simp [e0] at h2

/-- **Instance of Déf. 3**: the two ends of the arc are orthogonal; no point is orthogonal to
itself. -/
theorem def3_instance : OrthPts a0 b1 ∧ ¬ OrthPts a0 a0 := by
  rw [orthPts_iff (m := a0) (p := b1) (isRep_mk e0 e0_ne_zero) (isRep_mk e1 e1_ne_zero),
    orthPts_iff (m := a0) (p := a0) (isRep_mk e0 e0_ne_zero) (isRep_mk e0 e0_ne_zero),
    dotPairing_two, dotPairing_two]
  simp [e0, e1]

end ConeAppuiAlphaInstance

end Benzecri
