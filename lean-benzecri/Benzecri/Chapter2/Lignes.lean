import Benzecri.Chapter2.Hilbert

/-!
# Chapter 2 § 2, Déf. 5, Props. 4 and 6 — covering numbers, broken lines of majorised segments, broken lines in a pocket (with property 7°)

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 2 § 2, journal pp. 249–252; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch2.tex`. Target T-bz-c2-lignes (DEC-137). No label
is marked: the dimension-0 rows wait on OQ-45, and Prop. 6 is false as printed (SCOPE).

* `bzdef:c2s2d5_nombre_recouvrement` — `benzecri1960_ch2.tex:381` (Déf. 5, l.381–385) — not
  marked (OQ-45). `Benzecri.nombreRecouvrement n k E` (the least `m` with a covering
  `IsRecouvrementMajore n k E O`, `O : Fin m → Set V`); for `n ≥ 1`, `E` compact, `k > 0` it is
  the least element (`nombreRecouvrement_isLeast`). For `n = 0` a part has such a covering iff it
  is empty (`exists_isRecouvrementMajore_dim_zero_iff`).
* `bzprop:c2s2p4_ligne_brisee` — `benzecri1960_ch2.tex:387` (Prop. 4, l.387–391, proof l.393–409)
  — not marked (OQ-45). Proved, sorry-free, for `n ≥ 1`: `Benzecri.ligne_brisee`. In every
  dimension, for any covering of a connected part: `ligne_brisee_of_finset`,
  `ligne_brisee_of_recouvrement`. Printed form: `LigneBriseePrinted n ↔ 0 < n`.
* `bzprop:c2s2p6_ligne_brisee_poche` — `benzecri1960_ch2.tex:437` (Prop. 6, l.437–443, proof
  l.445–449) — not marked: **false as printed** for a pocket of cote `z = 0`, which Déf. 1′
  allows (`ligneBriseePochePrinted_iff`: it holds only for `n = 0`, vacuously). Proved: the
  corrected form `IsPocheProj.ligne_brisee_poche` (`≤` always, `<` when `z(φ(A)) > 0`, any real
  `K`), and the printed conclusion whenever `z ≢ 0` (`ligne_brisee_poche_of_ne_zero`).
* Property 7° of the editorial enonce `bzthm:c2s2_proprietes_pseudo_longueur`
  (`benzecri1960_ch2.tex:229`, l.253–256, proof l.334–357), as a lemma, not marked (row
  T-bz-c2-proprietes): `IsPocheProj.septieme_propriete` (corrected), `septieme_majore` (for a
  segment majorised by `log K`), `septieme_propriete_of_ne_zero` (printed, `z ≢ 0`);
  `SeptiemeProprietePrinted n ↔ n = 0`.

> **Déf. 5.** Soit $E$ une partie compacte d'une variété localement projective $V$; soit $k$ un
> nombre réel strictement positif. On désigne par $n(E, k)$ le plus petit entier $n$, tel qu'il
> existe un recouvrement de $E$, formé de $n$ ouverts majorés par $k$.
>
> **Proposition 4.** Soit $E$ une partie compacte connexe d'une variété localement projective $V$.
> Deux points $M$ et $N$ quelconques de $E$ peuvent être joints par une ligne brisée formée d'au
> plus $n(E, k)$ segments majorés par $k$ dans $V$.
>
> **Proposition 6.** Soit $V$ une variété localement projective, possédant une poche
> $(P, \mathring{H}, \varphi, z)$. Soient $A$ et $B$ deux points de $V$, $L$ une ligne brisée
> joignant $A$ à $B$, et formée de $p$ segments tous majorés dans $V$ par $k=\log K$. Supposons
> que $A\in P$; $z(\varphi(A))<1/K^p$ : alors $B$ est aussi dans $P$, ainsi que $L$, et l'on a
> $z(\varphi(B))<K^p\,z(\varphi(A))$.
> La proposition se démontre par récurrence sur $p$ : pour $p=1$, c'est la septième propriété de
> la pseudo-longueur, le passage de $p$ à $p+1$ est immédiat.
>
> **7°** Soit $(P, \mathring{H}, \varphi, z)$ une poche de $V$; soit $M\in P$ un point de $V$ tel
> que $z(\varphi(M))<\dfrac{1}{K}$ (où $K$ désigne un nombre réel supérieur à $1$); soit $(M, N)$
> un segment de $V$ dont la pseudo-longueur $l_V(M, N)$ soit inférieure à $\log K$; alors,
> $N\in P$ et $z\,\varphi(N)<K\,z(\varphi(M))$.

## The proofs formalized

**Prop. 4** follows the printed induction, run on a covering rather than on `n(E, k)`: for a
preconnected `C` covered by a finite family `𝒪` of open majorised parts, with `M ∈ O_j`, the
component `D` of `N` in the union of the other members is the union of the members it meets
(a majorised part is connected, `IsMajorePart.isPreconnected`), hence open, covered by at most
`card 𝒪 − 1` members; `C` connected forces `O_j ∩ D ≠ ∅`; one segment in `O_j`, then induction in
`D`. **7°** is the printed computation, in coordinates: the cote is `Λ/l` for a linear form `Λ`
(`Sphere.exists_linear_cote`), monotone along a segment of `H̊` (`Sphere.cote_mem_uIcc`); condition
*b* of the pocket, applied to every sub-segment `(M, X)`, puts the part of the segment where
`z < 1` in `P`, where `φ̃ = φ` (same germ, connected: `eqOn_of_germ_eq`); the real inequality is
`septieme_alg`. **Prop. 6** is the printed induction on `p`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `V` a « variété localement projective » (Déf. 5, Props. 4, 6) | ⚠ weakened: `[ChartedSpace (S n) V]`, `[HasGroupoid V (projGroupoid n)]` where used; Hausdorff, connected, second countable never used |
| Déf. 5: `E` compact, `k > 0` | ✓ carried where used (`nombreRecouvrement_isLeast`); the definition itself is stated for every `E`, `k` |
| Déf. 5: « un recouvrement de $E$, formé de $n$ ouverts majorés par $k$ » | ✓ carried (reading, question): `O : Fin m → Set V`, each `O i` open and majorised by `k` in `V` (Déf. 4), `E ⊆ ⋃ O i`; repetitions allowed, which does not change the least `m` |
| Déf. 5: « le plus petit entier » | ✓ carried: `sInf`, the least element for `n ≥ 1` (`IsLeast`); for `n = 0`, `E ≠ ∅` no covering exists and the value `0` is Lean's convention for `sInf ∅` (OQ-45) |
| Prop. 4: `E` compact | ✓ carried in `ligne_brisee` (only to have `n(E, k)`); `ligne_brisee_of_recouvrement` needs none |
| Prop. 4: `E` connexe | ⚠ weakened: `IsPreconnected E` (nonemptiness follows from `M ∈ E`) |
| Prop. 4: `k` (strictly positive, from Déf. 5) | ✓ carried: `0 < k` |
| Prop. 4: the dimension | ⚠ strengthened: `[NeZero n]` in `ligne_brisee` (OQ-45; `ligneBriseePrinted_iff`) |
| Props. 4, 6: « ligne brisée formée de $p$ segments (majorés par $k$) » | ✓ carried (reading, question): `IsLigneBrisee n k p M N L`, `p ≥ 1` consecutive segments majorised by `k`, `L` their union; explicitly, vertices `X 0 = M, …, X p = N` and segments `Sg i` from `X i` to `X (i + 1)` (`isLigneBrisee_iff`) |
| Prop. 6: « une poche $(P, \mathring{H}, \varphi, z)$ » | ✓ carried: `IsPocheProj P l φ z` (Déf. 1′, strict) |
| Prop. 6: « $k=\log K$ » | ⚠ weakened: any real `K` (the hypotheses force `K > 1`, or `K < −1` with `p` even, where `log K = log (−K)`) |
| Prop. 6: `A ∈ P`, `z(φ(A)) < 1/K^p` | ✓ carried |
| Prop. 6: conclusion `z(φ(B)) < K^p z(φ(A))` | ⚠ strengthened (finding): the printed `<` needs `z ≢ 0` (`ligne_brisee_poche_of_ne_zero`); with no added hypothesis: `≤`, and `<` when `z(φ(A)) > 0` (`ligne_brisee_poche`) |
| 7°: `K > 1`, `M ∈ P`, `z(φ(M)) < 1/K`, `l_V(M, N) < log K` | ⚠ weakened: no hypothesis on `K` (forced); `(M, N)` a segment follows from `l_V(M, N) < log K` |
| 7°: conclusion `N ∈ P`, `z φ(N) < K z(φ(M))` | ⚠ strengthened (finding), as for Prop. 6: printed `<` under `z ≢ 0` (`septieme_propriete_of_ne_zero`); `≤` always, plus `(M, N) ⊆ P` (`septieme_propriete`) |

## SCOPE (disclosed)

* **Prop. 6 and 7° are false as printed** (findings, not readings). Déf. 1′ (l.119–145) admits a
  pocket whose cote is identically `0` (condition *a*: inf `0`, bounded by `1`); the strict library
  already notes it (Poches, `isPocheAff_model`). For such a pocket `z(φ(M)) = 0` for every `M ∈ P`,
  and the conclusion `z(φ(N)) < K z(φ(M))` reads `0 < 0`, for every segment, the point segment
  `(M, M)` included (`l_V(M, M) = 0 < log K` for `n ≥ 1`). Witness: `ℝⁿ` (`n ≥ 1`) with its
  canonical projective structure and the pocket `(ℝⁿ, H₀, j, 0)`, the Remarque's image of
  `(ℝⁿ, id, 0)` (`exists_isPocheProj_cote_zero`); `SeptiemeProprietePrinted n ↔ n = 0` and
  `LigneBriseePochePrinted n ↔ n = 0` (for `n = 0` both are vacuous: no pseudo-length is finite, no
  broken line exists). The failure is exactly the cote `0`: if `z ≢ 0`, then `z > 0` on `φ(P)`
  (`IsPocheProj.cote_pos_of_ne_zero`, `φ(P)` open), and both hold as printed
  (`septieme_propriete_of_ne_zero`, `ligne_brisee_poche_of_ne_zero`). For every pocket, `≤` holds.
* **In the printed proof of 7°** (l.334–357, statement unaffected beyond the above): « les quatre
  points $a$, $b$, $f$, $f'$ ont une cote $z$ positive » (l.343) is asserted without argument (it fails for `z ≡ 0` only if
  « positive » means `> 0`; Benzécri writes « strictement positif » for that, and under `≥ 0` it holds
  for every pocket); the case `z(b) > z(a)` only needs `z(f) ≥ 0`, which comes from condition *b*
  applied to every sub-segment `(M, X)`, `X ∈ (M, F)`, together with `φ̃ = φ` on `(M, F) ⊆ P`
  (same germ at `M`, connected) — left implicit. The case `z(b) ≤ z(a)` (l.346–347) concludes
  `B ∈ P` only; `z(b) < K z(a)` needs `z(a) > 0`. The conclusion is about `z(φ(N))` while the
  computation gives `z(φ̃(N))`; they agree because `(M, N) ⊆ P` — left implicit too.
* **In the printed proof of Prop. 4** (l.393–409, statement unaffected): the induction hypothesis
  is applied to `O_Q`, an open set, not compact, for which Déf. 5 defines no `n(O_Q, k)`; the
  induction is run here on the number of open sets covering a connected part (which needs no
  compactness, `ligne_brisee_of_finset`). « un tel ouvert est inclus dans $O_Q$, ou a avec $O_Q$
  une intersection vide » uses that each `O_i` is connected, true because a majorised part is
  (`IsMajorePart.isPreconnected`), and left implicit. The letter `k` names both the bound and an
  index (« $N\in O_k$ », l.399).
* **`[sic]`, not findings**: « $O_a$ » (l.408) is read `O_Q`; « $af\times ff'$ » (l.341) is read
  `af × bf'`; « $z\,\varphi(N)$ » (l.256) is read `z(φ(N))`. The scan (pp. 249–252) agrees with the
  transcription of l.253–256, 334–357 and 381–449; no mistranscription suspected.
* **Dimension 0** (OQ-45). No segment is majorised, so no part containing a point is
  (`not_isMajorePart_dim_zero`): a nonempty `E` has no covering and `n(E, k)` is undefined
  (`exists_isRecouvrementMajore_dim_zero_iff`), and no broken line exists
  (`not_isLigneBrisee_dim_zero`). Prop. 4 fails as printed for `n = 0` (one point of `S(0)`),
  and holds for `n ≥ 1` (`ligneBriseePrinted_iff`); under OQ-45 (a) `ligne_brisee` is its anchor.
  7° and Prop. 6 are vacuous for `n = 0`.
* **7° is a lemma, not marked**: its row is T-bz-c2-proprietes (OQ-38). For Prop. 6 the
  segments are majorised by `log K` while 7° assumes `l_V < log K`; `septieme_majore` takes the
  majorised form, from which 7° follows (`exists_isMajoreSeg_of_pseudoLength_lt`).
* Tools for later targets (T-bz-c2-compact): `ligne_brisee`, `ligne_brisee_of_recouvrement`
  (with the line inside the covering), `IsLigneBrisee.append`, `.mono`, `.left_mem`,
  `.right_mem`; `IsPocheProj.ligne_brisee_poche` gives `B ∈ P` and `L ⊆ P` for every pocket.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Filter Topology

namespace Benzecri

universe u

/-! ### Déf. 5 and broken lines: the definitions -/

section Defs

variable {V : Type u} [TopologicalSpace V]

/-- **A covering of `E` by `m` open sets majorised by `k`** (the object Déf. 5 counts): `m` open
sets of `V`, each majorised by `k` in `V` (Déf. 4, `IsMajorePart`), whose union contains `E`. -/
def IsRecouvrementMajore (n : ℕ) [ChartedSpace (S n) V] (k : ℝ) (E : Set V) {m : ℕ}
    (O : Fin m → Set V) : Prop :=
  (∀ i, IsOpen (O i) ∧ IsMajorePart n k (O i)) ∧ E ⊆ ⋃ i, O i

/-- **Déf. 5, the covering number `n(E, k)`** (`bzdef:c2s2d5_nombre_recouvrement`): the smallest
integer `m` such that `E` has a covering by `m` open sets majorised by `k`. Lean's `sInf` of an
empty set of naturals is `0`: when no such covering exists (`n = 0` and `E ≠ ∅`, see
`exists_isRecouvrementMajore_dim_zero_iff`) the paper's `n(E, k)` is undefined and this value is a
convention; for `n ≥ 1`, `E` compact and `k > 0` it is the least element
(`nombreRecouvrement_isLeast`). -/
def nombreRecouvrement (n : ℕ) [ChartedSpace (S n) V] (k : ℝ) (E : Set V) : ℕ :=
  sInf {m : ℕ | ∃ O : Fin m → Set V, IsRecouvrementMajore n k E O}

/-- **A broken line of `p` segments majorised by `k` in `V`, joining `M` to `N`, with support `L`**
(« ligne brisée formée de $p$ segments majorés par $k$ », Props. 4–6): one segment majorised by
`k` (Déf. 2, `IsMajoreSeg`) is a broken line of `1` segment; a segment from `M` to `X` followed by a
broken line of `p` segments from `X` to `N` is a broken line of `p + 1` segments from `M` to `N`.
The support `L` is the union of the segments. A broken line has at least one segment
(`IsLigneBrisee.one_le`). -/
inductive IsLigneBrisee (n : ℕ) [ChartedSpace (S n) V] (k : ℝ) : ℕ → V → V → Set V → Prop
  | segment {Sg : Set V} {M N : V} : IsMajoreSeg n k Sg M N → IsLigneBrisee n k 1 M N Sg
  | cons {p : ℕ} {Sg L : Set V} {M X N : V} : IsMajoreSeg n k Sg M X →
      IsLigneBrisee n k p X N L → IsLigneBrisee n k (p + 1) M N (Sg ∪ L)

end Defs

/-! ### Elementary facts -/

section Basic

variable {n : ℕ} {V : Type u} [TopologicalSpace V] [ChartedSpace (S n) V]

/-- A majorised part is preconnected: any two of its points lie on a segment inside it. -/
theorem IsMajorePart.isPreconnected {k : ℝ} {C : Set V} (h : IsMajorePart n k C) :
    IsPreconnected C := by
  refine isPreconnected_of_forall_pair fun x hx y hy => ?_
  obtain ⟨Sg, hSg, hmaj⟩ := h x hx y hy
  exact ⟨Sg, hSg, hmaj.1.left_mem, hmaj.1.right_mem, hmaj.1.isPreconnected⟩

/-- A majorising number is positive (a projective measure is `≥ 0`). -/
theorem IsMajoreSeg.pos {k : ℝ} {Sg : Set V} {M N : V} (h : IsMajoreSeg n k Sg M N) : 0 < k := by
  obtain ⟨-, Sg₁, A, B, ⟨φ, hφ, hS, -⟩, -, hall⟩ := h
  exact EReal.coe_pos.1 ((Sphere.projMeasure_nonneg _ _ _ _).trans_lt (hall φ hφ hS))

theorem IsLigneBrisee.one_le {k : ℝ} {p : ℕ} {M N : V} {L : Set V}
    (h : IsLigneBrisee n k p M N L) : 1 ≤ p := by
  cases h with
  | segment _ => exact le_rfl
  | cons _ _ => exact Nat.le_add_left 1 _

theorem IsLigneBrisee.left_mem {k : ℝ} {p : ℕ} {M N : V} {L : Set V}
    (h : IsLigneBrisee n k p M N L) : M ∈ L := by
  cases h with
  | segment hS => exact hS.1.left_mem
  | cons hS _ => exact Or.inl hS.1.left_mem

theorem IsLigneBrisee.right_mem {k : ℝ} {p : ℕ} {M N : V} {L : Set V}
    (h : IsLigneBrisee n k p M N L) : N ∈ L := by
  induction h with
  | segment hS => exact hS.1.right_mem
  | cons _ _ ih => exact Or.inr ih

/-- Concatenation of two broken lines. -/
theorem IsLigneBrisee.append {k : ℝ} {p q : ℕ} {M X N : V} {L L' : Set V}
    (h : IsLigneBrisee n k p M X L) (h' : IsLigneBrisee n k q X N L') :
    IsLigneBrisee n k (p + q) M N (L ∪ L') := by
  induction h with
  | segment hS =>
    rw [add_comm]
    exact IsLigneBrisee.cons hS h'
  | cons hS _ ih =>
    rw [union_assoc, show ∀ a b : ℕ, a + 1 + b = a + b + 1 from fun a b => by omega]
    exact IsLigneBrisee.cons hS (ih h')

theorem IsLigneBrisee.mono {k k' : ℝ} {p : ℕ} {M N : V} {L : Set V}
    (h : IsLigneBrisee n k p M N L) (hk : k ≤ k') : IsLigneBrisee n k' p M N L := by
  induction h with
  | segment hS => exact IsLigneBrisee.segment (hS.mono hk)
  | cons hS _ ih => exact IsLigneBrisee.cons (hS.mono hk) ih

/-- **A broken line is a chain of segments**: `IsLigneBrisee n k p M N L` holds iff `p ≥ 1` and
there are vertices `X 0 = M, …, X p = N` and segments `Sg i` of `V` from `X i` to `X (i + 1)`, each
majorised by `k` in `V`, with `L = ⋃ i, Sg i`. -/
theorem isLigneBrisee_iff {k : ℝ} {p : ℕ} {M N : V} {L : Set V} :
    IsLigneBrisee n k p M N L ↔ 1 ≤ p ∧ ∃ (X : Fin (p + 1) → V) (Sg : Fin p → Set V),
      X 0 = M ∧ X (Fin.last p) = N ∧
      (∀ i : Fin p, IsMajoreSeg n k (Sg i) (X i.castSucc) (X i.succ)) ∧ L = ⋃ i, Sg i := by
  constructor
  · intro h
    refine ⟨h.one_le, ?_⟩
    induction h with
    | @segment Sg M N hS =>
      refine ⟨![M, N], fun _ => Sg, rfl, rfl, fun i => ?_, (iUnion_const Sg).symm⟩
      fin_cases i
      exact hS
    | @cons p Sg L M X N hS _ ih =>
      obtain ⟨X', Sg', h0, hlast, hseg, hL⟩ := ih
      refine ⟨Fin.cons M X', Fin.cons Sg Sg', rfl, ?_, fun i => ?_, ?_⟩
      · rw [← Fin.succ_last, Fin.cons_succ, hlast]
      · refine Fin.cases ?_ (fun j => ?_) i
        · simpa [h0] using hS
        · simpa [← Fin.succ_castSucc] using hseg j
      · rw [hL]
        ext x
        simp
  · rintro ⟨hp, X, Sg, h0, hlast, hseg, hL⟩
    induction p generalizing M L with
    | zero => exact absurd hp (by norm_num)
    | succ p ih =>
      rcases Nat.eq_zero_or_pos p with rfl | hp'
      · have hL1 : L = Sg 0 := by
          rw [hL]
          ext x
          simp [Fin.exists_fin_one]
        rw [hL1, ← h0, ← hlast]
        exact IsLigneBrisee.segment (hseg 0)
      · have htail : IsLigneBrisee n k p (X 1) N (⋃ j : Fin p, Sg j.succ) := by
          refine ih (M := X 1) (L := ⋃ j : Fin p, Sg j.succ) hp' (fun j => X j.succ)
            (fun j => Sg j.succ) rfl ?_ (fun j => ?_) rfl
          · rw [← hlast]
            rfl
          · rw [Fin.succ_castSucc]
            exact hseg j.succ
        have hL' : L = Sg 0 ∪ ⋃ j : Fin p, Sg j.succ := by
          rw [hL]
          ext x
          simp [Fin.exists_fin_succ]
        rw [hL', ← h0]
        exact IsLigneBrisee.cons (hseg 0) htail

/-- A broken line majorised by `k` has `k > 0`. -/
theorem IsLigneBrisee.pos {k : ℝ} {p : ℕ} {M N : V} {L : Set V}
    (h : IsLigneBrisee n k p M N L) : 0 < k := by
  cases h with
  | segment hS => exact hS.pos
  | cons hS _ => exact hS.pos

end Basic

/-- **In dimension `0` there is no broken line of majorised segments** (no segment is majorised,
`not_isMajoreSeg_dim_zero`). -/
theorem not_isLigneBrisee_dim_zero {V : Type u} [TopologicalSpace V] [ChartedSpace (S 0) V]
    {k : ℝ} {p : ℕ} {M N : V} {L : Set V} : ¬ IsLigneBrisee 0 k p M N L := by
  intro h
  cases h with
  | segment hS => exact not_isMajoreSeg_dim_zero _ _ _ _ hS
  | cons hS _ => exact not_isMajoreSeg_dim_zero _ _ _ _ hS

/-! ### Déf. 5 — the covering number -/

section Def5

variable {n : ℕ} {V : Type u} [TopologicalSpace V] [ChartedSpace (S n) V]

theorem nombreRecouvrement_le {k : ℝ} {E : Set V} {m : ℕ} {O : Fin m → Set V}
    (h : IsRecouvrementMajore n k E O) : nombreRecouvrement n k E ≤ m :=
  Nat.sInf_le ⟨O, h⟩

variable [HasGroupoid V (projGroupoid n)]

/-- **Déf. 5 is well posed** (`n ≥ 1`): a compact `E` has a finite covering by open sets majorised
by `k > 0` (Prop. 3, `exists_isOpen_isMajorePart`, and compactness). -/
theorem exists_isRecouvrementMajore [NeZero n] {k : ℝ} (hk : 0 < k) {E : Set V}
    (hE : IsCompact E) : ∃ (m : ℕ) (O : Fin m → Set V), IsRecouvrementMajore n k E O := by
  have hW : ∀ x : V, ∃ W : Set V, IsOpen W ∧ x ∈ W ∧ IsMajorePart n k W := fun x =>
    exists_isOpen_isMajorePart (n := n) hk x
  choose W hWo hxW hWm using hW
  obtain ⟨t, -, ht⟩ := hE.elim_nhds_subcover W fun x _ => (hWo x).mem_nhds (hxW x)
  refine ⟨t.card, fun i => W (t.equivFin.symm i), fun i => ⟨hWo _, hWm _⟩, fun y hy => ?_⟩
  obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.1 (ht hy)
  exact mem_iUnion.2 ⟨t.equivFin ⟨x, hxt⟩, by simpa using hyx⟩

/-- **Déf. 5** (`n ≥ 1`): `n(E, k)` is the least number of open sets majorised by `k` covering the
compact `E` (« le plus petit entier $n$, tel qu'il existe un recouvrement de $E$, formé de $n$
ouverts majorés par $k$ »). -/
theorem nombreRecouvrement_isLeast [NeZero n] {k : ℝ} (hk : 0 < k) {E : Set V}
    (hE : IsCompact E) :
    IsLeast {m : ℕ | ∃ O : Fin m → Set V, IsRecouvrementMajore n k E O}
      (nombreRecouvrement n k E) := by
  obtain ⟨m, O, hO⟩ := exists_isRecouvrementMajore (n := n) hk hE
  exact ⟨Nat.sInf_mem ⟨m, O, hO⟩, fun _ hm => Nat.sInf_le hm⟩

/-- A covering realising `n(E, k)` (`n ≥ 1`). -/
theorem exists_isRecouvrementMajore_nombreRecouvrement [NeZero n] {k : ℝ} (hk : 0 < k)
    {E : Set V} (hE : IsCompact E) :
    ∃ O : Fin (nombreRecouvrement n k E) → Set V, IsRecouvrementMajore n k E O :=
  (nombreRecouvrement_isLeast hk hE).1

end Def5

/-- **Déf. 5 in dimension `0`**: a part has a covering by majorised open sets iff it is empty;
for `E ≠ ∅` the paper's `n(E, k)` is undefined (OQ-45). -/
theorem exists_isRecouvrementMajore_dim_zero_iff {V : Type u} [TopologicalSpace V]
    [ChartedSpace (S 0) V] {k : ℝ} {E : Set V} :
    (∃ (m : ℕ) (O : Fin m → Set V), IsRecouvrementMajore 0 k E O) ↔ E = ∅ := by
  constructor
  · rintro ⟨m, O, hO, hEO⟩
    refine eq_empty_iff_forall_notMem.2 fun x hx => ?_
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hEO hx)
    exact not_isMajorePart_dim_zero k hi (hO i).2
  · rintro rfl
    exact ⟨0, Fin.elim0, fun i => i.elim0, empty_subset _⟩

/-! ### Prop. 4 — broken lines of majorised segments -/

section Prop4

variable {n : ℕ} {V : Type u} [TopologicalSpace V] [ChartedSpace (S n) V]

/-- **Prop. 4, the induction of the printed proof, on a covering** (any dimension, no compactness):
if a preconnected `C` is covered by a finite family `𝒪` of open sets majorised by `k`, any two
points of `C` are joined by a broken line of at most `card 𝒪` segments majorised by `k`, inside
`⋃ 𝒪`. -/
theorem ligne_brisee_of_finset {k : ℝ} (𝒪 : Finset (Set V))
    (h𝒪 : ∀ O ∈ 𝒪, IsOpen O ∧ IsMajorePart n k O) {C : Set V} (hC : IsPreconnected C)
    (hC𝒪 : C ⊆ ⋃₀ (𝒪 : Set (Set V))) {M N : V} (hM : M ∈ C) (hN : N ∈ C) :
    ∃ (p : ℕ) (L : Set V), p ≤ 𝒪.card ∧ L ⊆ ⋃₀ (𝒪 : Set (Set V)) ∧
      IsLigneBrisee n k p M N L := by
  classical
  suffices H : ∀ (p : ℕ) (𝒪 : Finset (Set V)), 𝒪.card ≤ p →
      (∀ O ∈ 𝒪, IsOpen O ∧ IsMajorePart n k O) → ∀ C : Set V, IsPreconnected C →
      C ⊆ ⋃₀ (𝒪 : Set (Set V)) → ∀ M ∈ C, ∀ N ∈ C, ∃ (q : ℕ) (L : Set V), q ≤ p ∧
        L ⊆ ⋃₀ (𝒪 : Set (Set V)) ∧ IsLigneBrisee n k q M N L from
    H 𝒪.card 𝒪 le_rfl h𝒪 C hC hC𝒪 M hM N hN
  intro p
  induction p with
  | zero =>
    intro 𝒪 h0 _ C _ hC𝒪 M hM N _
    have h𝒪0 : 𝒪 = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 h0)
    subst h𝒪0
    simp only [Finset.coe_empty, sUnion_empty, subset_empty_iff] at hC𝒪
    subst hC𝒪
    exact absurd hM (notMem_empty M)
  | succ p ih =>
    intro 𝒪 hcard h𝒪 C hC hC𝒪 M hM N hN
    obtain ⟨Oj, hOj𝒪, hMOj⟩ := mem_sUnion.1 (hC𝒪 hM)
    have hOj𝒪' : Oj ∈ 𝒪 := Finset.mem_coe.1 hOj𝒪
    by_cases hNOj : N ∈ Oj
    · obtain ⟨Sg, hSgO, hmaj⟩ := (h𝒪 Oj hOj𝒪').2 M hMOj N hNOj
      exact ⟨1, Sg, by omega, hSgO.trans (subset_sUnion_of_mem hOj𝒪),
        IsLigneBrisee.segment hmaj⟩
    -- `D`, the component of `N` in the union of the other open sets
    set 𝒪₁ := 𝒪.erase Oj with h𝒪₁
    set U := ⋃₀ (𝒪₁ : Set (Set V)) with hU
    have hNU : N ∈ U := by
      obtain ⟨O, hO, hNO⟩ := mem_sUnion.1 (hC𝒪 hN)
      refine mem_sUnion.2 ⟨O, Finset.mem_coe.2 (Finset.mem_erase.2 ⟨?_, hO⟩), hNO⟩
      rintro rfl
      exact hNOj hNO
    set D := connectedComponentIn U N with hD
    have hsubD : ∀ O ∈ 𝒪₁, ∀ x ∈ O, x ∈ D → O ⊆ D := by
      intro O hO x hxO hxD
      have hOU : O ⊆ U := subset_sUnion_of_mem (Finset.mem_coe.2 hO)
      rw [hD, connectedComponentIn_eq hxD]
      exact (h𝒪 O (Finset.mem_of_mem_erase hO)).2.isPreconnected.subset_connectedComponentIn
        hxO hOU
    set 𝒪₂ := 𝒪₁.filter (· ⊆ D) with h𝒪₂
    have h𝒪₂𝒪 : ∀ O ∈ 𝒪₂, O ∈ 𝒪 := fun O hO =>
      Finset.mem_of_mem_erase (Finset.mem_filter.1 hO).1
    have hD₂ : D = ⋃₀ (𝒪₂ : Set (Set V)) := by
      apply Subset.antisymm
      · intro x hxD
        obtain ⟨O, hO, hxO⟩ := mem_sUnion.1 (connectedComponentIn_subset _ _ hxD)
        have hO' : O ∈ 𝒪₁ := Finset.mem_coe.1 hO
        exact mem_sUnion.2 ⟨O, Finset.mem_coe.2 (Finset.mem_filter.2
          ⟨hO', hsubD O hO' x hxO hxD⟩), hxO⟩
      · intro x hx
        obtain ⟨O, hO, hxO⟩ := mem_sUnion.1 hx
        exact (Finset.mem_filter.1 (Finset.mem_coe.1 hO)).2 hxO
    have hcard₂ : 𝒪₂.card ≤ p := by
      have h1 : 𝒪₂.card ≤ 𝒪₁.card := Finset.card_filter_le _ _
      have h2 : 𝒪₁.card + 1 = 𝒪.card := Finset.card_erase_add_one hOj𝒪'
      omega
    -- `O_j` meets `D`, since `C` is connected
    have hmeet : (Oj ∩ D).Nonempty := by
      by_contra hdisj
      rw [not_nonempty_iff_eq_empty] at hdisj
      set B := ⋃₀ ((𝒪.filter (fun O => Disjoint O D) : Finset (Set V)) : Set (Set V)) with hB
      have hDo : IsOpen D := by
        rw [hD₂]
        exact isOpen_sUnion fun O hO => (h𝒪 O (h𝒪₂𝒪 O (Finset.mem_coe.1 hO))).1
      have hBo : IsOpen B := isOpen_sUnion fun O hO =>
        (h𝒪 O (Finset.mem_filter.1 (Finset.mem_coe.1 hO)).1).1
      have hCDB : C ⊆ D ∪ B := by
        intro x hx
        obtain ⟨O, hO, hxO⟩ := mem_sUnion.1 (hC𝒪 hx)
        have hO' : O ∈ 𝒪 := Finset.mem_coe.1 hO
        by_cases hOD : Disjoint O D
        · exact Or.inr (mem_sUnion.2 ⟨O, Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hO', hOD⟩), hxO⟩)
        · obtain ⟨y, hyO, hyD⟩ := not_disjoint_iff.1 hOD
          have hOne : O ≠ Oj := by
            rintro rfl
            exact (eq_empty_iff_forall_notMem.1 hdisj) y ⟨hyO, hyD⟩
          exact Or.inl (hsubD O (Finset.mem_erase.2 ⟨hOne, hO'⟩) y hyO hyD hxO)
      have hMB : M ∈ B := mem_sUnion.2 ⟨Oj, Finset.mem_coe.2 (Finset.mem_filter.2
        ⟨hOj𝒪', disjoint_iff_inter_eq_empty.2 hdisj⟩), hMOj⟩
      obtain ⟨x, -, hxD, hxB⟩ := hC D B hDo hBo hCDB ⟨N, hN, mem_connectedComponentIn hNU⟩
        ⟨M, hM, hMB⟩
      obtain ⟨O, hO, hxO⟩ := mem_sUnion.1 hxB
      exact (Finset.mem_filter.1 (Finset.mem_coe.1 hO)).2.notMem_of_mem_left hxO hxD
    obtain ⟨X, hXOj, hXD⟩ := hmeet
    obtain ⟨Sg, hSgO, hmaj⟩ := (h𝒪 Oj hOj𝒪').2 M hMOj X hXOj
    obtain ⟨q, L, hq, hL, hline⟩ := ih 𝒪₂ hcard₂ (fun O hO => h𝒪 O (h𝒪₂𝒪 O hO)) D
      isPreconnected_connectedComponentIn hD₂.le X hXD N (mem_connectedComponentIn hNU)
    refine ⟨q + 1, Sg ∪ L, by omega, union_subset (hSgO.trans (subset_sUnion_of_mem hOj𝒪))
      (hL.trans (sUnion_mono fun O hO => Finset.mem_coe.2 (h𝒪₂𝒪 O (Finset.mem_coe.1 hO)))),
      IsLigneBrisee.cons hmaj hline⟩

/-- **Prop. 4 for any covering** (any dimension): a preconnected `E` covered by `m` open sets
majorised by `k`; any two of its points are joined by a broken line of at most `m` segments
majorised by `k`, inside the covering. -/
theorem ligne_brisee_of_recouvrement {k : ℝ} {E : Set V} {m : ℕ} {O : Fin m → Set V}
    (hO : IsRecouvrementMajore n k E O) (hE : IsPreconnected E) {M N : V} (hM : M ∈ E)
    (hN : N ∈ E) :
    ∃ (p : ℕ) (L : Set V), p ≤ m ∧ L ⊆ ⋃ i, O i ∧ IsLigneBrisee n k p M N L := by
  classical
  have hcov : ⋃₀ ((Finset.univ.image O : Finset (Set V)) : Set (Set V)) = ⋃ i, O i := by
    ext x
    simp
  obtain ⟨p, L, hp, hL, hline⟩ := ligne_brisee_of_finset (Finset.univ.image O)
    (fun U hU => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hU
      exact hO.1 i) hE (hcov ▸ hO.2) hM hN
  refine ⟨p, L, hp.trans ?_, hcov ▸ hL, hline⟩
  exact (Finset.card_image_le).trans (by simp)

/-- **Prop. 4** (`bzprop:c2s2p4_ligne_brisee`, for `n ≥ 1`): « Soit $E$ une partie compacte connexe
d'une variété localement projective $V$. Deux points $M$ et $N$ quelconques de $E$ peuvent être
joints par une ligne brisée formée d'au plus $n(E, k)$ segments majorés par $k$ dans $V$. » -/
theorem ligne_brisee [HasGroupoid V (projGroupoid n)] [NeZero n] {E : Set V} (hE : IsCompact E)
    (hEc : IsPreconnected E) {k : ℝ} (hk : 0 < k) {M N : V} (hM : M ∈ E) (hN : N ∈ E) :
    ∃ (p : ℕ) (L : Set V), p ≤ nombreRecouvrement n k E ∧ IsLigneBrisee n k p M N L := by
  obtain ⟨O, hO⟩ := exists_isRecouvrementMajore_nombreRecouvrement (n := n) hk hE
  obtain ⟨p, L, hp, -, hL⟩ := ligne_brisee_of_recouvrement hO hEc hM hN
  exact ⟨p, L, hp, hL⟩

end Prop4

/-- **Prop. 4 as printed**, for the manifolds of dimension `n` (Hausdorff, connected, second
countable; `V : Type`), `k > 0` as in Déf. 5. -/
def LigneBriseePrinted (n : ℕ) : Prop :=
  ∀ (V : Type) [TopologicalSpace V] [ChartedSpace (S n) V] [HasGroupoid V (projGroupoid n)]
    [T2Space V] [ConnectedSpace V] [SecondCountableTopology V] (E : Set V), IsCompact E →
    IsConnected E → ∀ k : ℝ, 0 < k → ∀ M ∈ E, ∀ N ∈ E,
      ∃ (p : ℕ) (L : Set V), p ≤ nombreRecouvrement n k E ∧ IsLigneBrisee n k p M N L

/-- **Prop. 4 holds as printed exactly in dimension `n ≥ 1`.** For `n = 0`, on the one-point open
set `{x}` of `S(0)` (Hausdorff, connected, second countable), no broken line exists
(`not_isLigneBrisee_dim_zero`), whatever value is given to the undefined `n(E, k)`. -/
theorem ligneBriseePrinted_iff {n : ℕ} : LigneBriseePrinted n ↔ 0 < n := by
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exfalso
      obtain ⟨x⟩ : Nonempty (S 0) := inferInstance
      let U : TopologicalSpace.Opens (S 0) := ⟨{x}, isOpen_singleton_S0 x⟩
      haveI : Subsingleton U := ⟨fun a b => Subtype.ext (a.2.trans b.2.symm)⟩
      haveI : ConnectedSpace U := isConnected_iff_connectedSpace.1 isConnected_singleton
      have hxU : x ∈ U := rfl
      obtain ⟨p, L, -, hL⟩ := h U univ isCompact_univ isConnected_univ 1 one_pos ⟨x, hxU⟩
        (mem_univ _) ⟨x, hxU⟩ (mem_univ _)
      exact not_isLigneBrisee_dim_zero hL
    · exact hn
  · intro hn V _ _ _ _ _ _ E hE hEc k hk M hM N hN
    haveI : NeZero n := ⟨hn.ne'⟩
    exact ligne_brisee (n := n) hE hEc.isPreconnected hk hM hN

/-! ### The cote of a pocket on the model: a quotient of two linear forms -/

namespace Sphere

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {l : Module.Dual ℝ E} [Fact (l ≠ 0)]

/-- **An affine function on the open hemisphere `H̊` of equation `l` is a linear form read on the
normalised representative**: `z(m) = Λ(M / l(M))` (`M ∈ F(m)`) for a linear form `Λ` on `E`. -/
theorem exists_linear_cote (z : openHemisphere l →ᵃ[ℝ] ℝ) :
    ∃ Λ : E →ₗ[ℝ] ℝ, ∀ m : openHemisphere l, z m = Λ (nrep l m) := by
  obtain ⟨v₁, hv₁⟩ := exists_l_eq_one (Fact.out : l ≠ 0)
  have hv₁0 : v₁ ≠ 0 := ne_zero_of_l_pos (by rw [hv₁]; exact one_pos)
  let m₀ : openHemisphere l := ⟨mk v₁ hv₁0, (mk_mem_openHemisphere hv₁0).2 (by rw [hv₁]; exact one_pos)⟩
  let π : E →ₗ[ℝ] LinearMap.ker l :=
    LinearMap.codRestrict (LinearMap.ker l) (LinearMap.id - l.smulRight v₁) fun v => by
      simp [hv₁]
  refine ⟨z m₀ • l + z.linear ∘ₗ ((evalTrans hv₁).symm : LinearMap.ker l →ₗ[ℝ] HemiTrans l) ∘ₗ π,
    fun m => ?_⟩
  have h1 : l (nrep l (m : Sphere E)) = 1 := l_nrep m.2
  have hn₀ : nrep l (m₀ : Sphere E) = v₁ := nrep_mk_of_l_eq_one hv₁
  have hvsub : (evalTrans hv₁).symm (π (nrep l m)) = m -ᵥ m₀ := by
    show (lbar l).smulRight _ = (lbar l).smulRight _
    congr 1
    apply Subtype.ext
    simp [π, h1, hn₀]
  have := z.linearMap_vsub m m₀
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    smul_eq_mul, h1, mul_one]
  rw [hvsub, this, vsub_eq_sub]
  ring

/-- `z(s(v)) = Λ(v) / l(v)`. -/
theorem cote_eq_div {z : openHemisphere l →ᵃ[ℝ] ℝ} {Λ : E →ₗ[ℝ] ℝ}
    (hΛ : ∀ m : openHemisphere l, z m = Λ (nrep l m)) {v : E} {x : Sphere E} (hv : IsRep v x)
    (hx : x ∈ openHemisphere l) : z ⟨x, hx⟩ = Λ v / l v := by
  obtain ⟨hv0, rfl⟩ := hv
  rw [hΛ, nrep_mk, map_smul, smul_eq_mul, div_eq_inv_mul]

/-- **Along a segment of `H̊` the cote lies between its values at the endpoints** (the segment
lies in `H̊`). -/
theorem cote_mem_uIcc (z : openHemisphere l →ᵃ[ℝ] ℝ) {x₁ x₂ y : Sphere E}
    (h₁ : x₁ ∈ openHemisphere l) (h₂ : x₂ ∈ openHemisphere l) (hy : y ∈ closedSeg x₁ x₂) :
    ∃ hy' : y ∈ openHemisphere l, z ⟨y, hy'⟩ ∈ uIcc (z ⟨x₁, h₁⟩) (z ⟨x₂, h₂⟩) := by
  obtain ⟨v₁, hv₁⟩ := exists_isRep x₁
  obtain ⟨v₂, hv₂⟩ := exists_isRep x₂
  obtain ⟨s, t, hs, ht, hy⟩ := (mem_closedSeg_iff hv₁ hv₂).1 hy
  have hl₁ : 0 < l v₁ := by
    obtain ⟨h0, rfl⟩ := hv₁
    exact (mk_mem_openHemisphere h0).1 h₁
  have hl₂ : 0 < l v₂ := by
    obtain ⟨h0, rfl⟩ := hv₂
    exact (mk_mem_openHemisphere h0).1 h₂
  have hst : 0 < s * l v₁ + t * l v₂ := by
    rcases hs.eq_or_lt with rfl | hs'
    · rcases ht.eq_or_lt with rfl | ht'
      · exact absurd (by simp : (0 : ℝ) • v₁ + (0 : ℝ) • v₂ = 0) hy.ne_zero
      · nlinarith [mul_pos ht' hl₂]
    · nlinarith [mul_pos hs' hl₁, mul_nonneg ht hl₂.le]
  have hly : 0 < l (s • v₁ + t • v₂) := by
    simpa [map_add, map_smul] using hst
  have hy' : y ∈ openHemisphere l := by
    obtain ⟨h0, rfl⟩ := hy
    exact (mk_mem_openHemisphere h0).2 hly
  refine ⟨hy', ?_⟩
  obtain ⟨Λ, hΛ⟩ := exists_linear_cote z
  rw [cote_eq_div hΛ hy hy', cote_eq_div hΛ hv₁ h₁, cote_eq_div hΛ hv₂ h₂, ← segment_eq_uIcc]
  refine ⟨s * l v₁ / (s * l v₁ + t * l v₂), t * l v₂ / (s * l v₁ + t * l v₂), by positivity,
    by positivity, by field_simp, ?_⟩
  simp only [smul_eq_mul, map_add, map_smul]
  field_simp

end Sphere

/-- **The computation of the proof of 7°** (l.336–356), in coordinates: on the line through
`f = s(α)`, `a = s(α + β)`, `b = s(α + rβ)`, `f' = s(β)` (in this order, `r ≥ 1`), with
`z = Λ / l`, `p = Λ α`, `q = Λ β`, `u = l α > 0`, `w = l β > 0`; the cross-ratio
`(a, b, f', f)` is `r < K`. If `z(a) ≥ 0`, and `z(f) ≥ 0` whenever `z(f) < z(a)`, then
`z(b) ≤ K z(a)`, strictly when `z(a) > 0`. -/
theorem septieme_alg {p q u w r K : ℝ} (hu : 0 < u) (hw : 0 < w) (hr : 1 ≤ r) (hrK : r < K)
    (ha : 0 ≤ (p + q) / (u + w)) (hf : p / u < (p + q) / (u + w) → 0 ≤ p / u) :
    (p + r * q) / (u + r * w) ≤ K * ((p + q) / (u + w)) ∧
      (0 < (p + q) / (u + w) → (p + r * q) / (u + r * w) < K * ((p + q) / (u + w))) := by
  have hK1 : 1 < K := lt_of_le_of_lt hr hrK
  have huw : 0 < u + w := by linarith
  have hurw : 0 < u + r * w := by nlinarith
  by_cases hD : u * q - p * w ≤ 0
  · -- `z(b) ≤ z(a)`
    have hba : (p + r * q) / (u + r * w) ≤ (p + q) / (u + w) := by
      rw [div_le_div_iff₀ hurw huw]
      nlinarith [mul_nonneg (sub_nonneg.2 hr) (neg_nonneg.2 hD)]
    exact ⟨hba.trans (le_mul_of_one_le_left ha hK1.le),
      fun hpos => hba.trans_lt ((lt_mul_iff_one_lt_left hpos).2 hK1)⟩
  · -- `z(f) < z(a) < z(b)`: then `z(f) ≥ 0` and `z(b) ≤ r z(a)`
    push Not at hD
    have hfa : p / u < (p + q) / (u + w) := by
      rw [div_lt_div_iff₀ hu huw]
      nlinarith
    have hp : 0 ≤ p := by
      have := hf hfa
      rwa [le_div_iff₀ hu, zero_mul] at this
    have hq : 0 < q := by nlinarith
    have hza : 0 < (p + q) / (u + w) := div_pos (by linarith) huw
    have hbr : (p + r * q) / (u + r * w) ≤ r * ((p + q) / (u + w)) := by
      rw [mul_div_assoc', div_le_div_iff₀ hurw huw]
      have h0 : 0 ≤ p * u + p * w * (r + 1) + r * q * w := by
        have : 0 ≤ r := by linarith
        positivity
      nlinarith [mul_nonneg (sub_nonneg.2 hr) h0]
    have hlt : (p + r * q) / (u + r * w) < K * ((p + q) / (u + w)) :=
      hbr.trans_lt (mul_lt_mul_of_pos_right hrK hza)
    exact ⟨hlt.le, fun _ => hlt⟩

/-! ### Property 7° -/

section Septieme

variable {n : ℕ} {V : Type u} [TopologicalSpace V] [ChartedSpace (S n) V]
  {P : Set V} {l : Module.Dual ℝ (Fin (n + 1) → ℝ)} [Fact (l ≠ 0)]
  {φ : OpenPartialHomeomorph V (S n)} {z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ}

/-- The chart of a pocket maps `P` into `H̊`. -/
theorem IsPocheProj.mapsTo_hemi (hP : IsPocheProj P l φ z) {M : V} (hM : M ∈ P) :
    φ M ∈ Sphere.openHemisphere l :=
  hP.image_subset (mem_image_of_mem φ hM)

/-- The cote is `≥ 0` on the pocket (condition *a*). -/
theorem IsPocheProj.cote_nonneg (hP : IsPocheProj P l φ z) {M : V} (hM : M ∈ P) :
    0 ≤ z ⟨φ M, hP.mapsTo_hemi hM⟩ :=
  hP.isGLB.1 ⟨⟨φ M, hP.mapsTo_hemi hM⟩, mem_image_of_mem φ hM, rfl⟩

/-- **The cote of a pocket is either identically `0` or `> 0` on `φ(P)`**: `φ(P)` is open, `z ≥ 0`
on it (condition *a*), and an affine function with a minimum `0` at an interior point is `0`. -/
theorem IsPocheProj.cote_pos_of_ne_zero (hP : IsPocheProj P l φ z) (hz : ∃ y, z y ≠ 0) {M : V}
    (hM : M ∈ P) : 0 < z ⟨φ M, hP.mapsTo_hemi hM⟩ := by
  rcases (hP.cote_nonneg hM).lt_or_eq with h | h
  · exact h
  exfalso
  obtain ⟨y, hy⟩ := hz
  apply hy
  set m : Sphere.openHemisphere l := ⟨φ M, hP.mapsTo_hemi hM⟩ with hm
  have hopen : IsOpen (φ '' P) := by
    rw [← hP.source_eq, φ.image_source_eq_target]
    exact φ.open_target
  have hlin : ∀ u : Sphere.HemiTrans l, z.linear u = 0 := by
    intro u
    have hM₀ : l (Sphere.nrep l (m : S n)) = 1 := Sphere.l_nrep m.2
    set M₀ := Sphere.nrep l (m : S n) with hM₀def
    set w : Fin (n + 1) → ℝ := (u (Sphere.hq l M₀) : Fin (n + 1) → ℝ) with hwdef
    have hw : l w = 0 := (u (Sphere.hq l M₀)).2
    have hne : ∀ t : ℝ, M₀ + t • w ≠ 0 := fun t h0 => by
      have := congrArg l h0
      simp [hM₀, hw] at this
    have hfun : (fun t : ℝ => ((t • u +ᵥ m : Sphere.openHemisphere l) : S n)) =
        fun t => Sphere.mk (M₀ + t • w) (hne t) := by
      funext t
      rw [Sphere.coe_vadd_eq (t • u) m (Sphere.nrep_ne_zero m.2) (Sphere.mk_nrep m.2)]
      congr 1
    have hc : Continuous fun t : ℝ => ((t • u +ᵥ m : Sphere.openHemisphere l) : S n) := by
      rw [hfun]
      exact Sphere.continuous_mk_comp (continuous_const.add (continuous_id.smul continuous_const))
        hne
    have h0 : ((0 : ℝ) • u +ᵥ m : Sphere.openHemisphere l) = m := by rw [zero_smul, zero_vadd]
    have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ((t • u +ᵥ m : Sphere.openHemisphere l) : S n) ∈ φ '' P :=
      hc.continuousAt.preimage_mem_nhds (by
        rw [h0]
        exact hopen.mem_nhds ⟨M, hM, rfl⟩)
    have hge : ∀ᶠ t in 𝓝 (0 : ℝ), 0 ≤ t * z.linear u := hev.mono fun t ht => by
      have := hP.isGLB.1 ⟨t • u +ᵥ m, ht, rfl⟩
      rwa [AffineMap.map_vadd, map_smul, smul_eq_mul, vadd_eq_add, ← h, add_zero] at this
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hge
    have h1 := @hball (ε / 2) (by rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith)
    have h2 := @hball (-(ε / 2)) (by
      rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos (by positivity)]; linarith)
    nlinarith
  rw [← vsub_vadd y m, AffineMap.map_vadd, hlin, zero_vadd]
  exact h.symm

variable [HasGroupoid V (projGroupoid n)]

/-- **7°, corrected, for a segment majorised by `log K`** (the form Prop. 6 uses): if `M ∈ P`,
`z(φ(M)) < 1/K` and `(M, N)` is majorised by `log K`, then the segment lies in `P` (so `N ∈ P`)
and `z(φ(N)) ≤ K z(φ(M))`, strictly when `z(φ(M)) > 0`. No hypothesis on `K` (the hypotheses force
`K > 1`). The strict inequality fails for the cote `z = 0` (`septiemeProprietePrinted_iff`). -/
theorem IsPocheProj.septieme_majore (hP : IsPocheProj P l φ z) {Sg : Set V} {M N : V}
    (hM : M ∈ P) {K : ℝ} (hMK : z ⟨φ M, hP.mapsTo_hemi hM⟩ < 1 / K)
    (hmaj : IsMajoreSeg n (Real.log K) Sg M N) :
    Sg ⊆ P ∧ ∃ hN : N ∈ P, z ⟨φ N, hP.mapsTo_hemi hN⟩ ≤ K * z ⟨φ M, hP.mapsTo_hemi hM⟩ ∧
      (0 < z ⟨φ M, hP.mapsTo_hemi hM⟩ →
        z ⟨φ N, hP.mapsTo_hemi hN⟩ < K * z ⟨φ M, hP.mapsTo_hemi hM⟩) := by
  classical
  have hlt1 : ∀ {a b x c : ℝ}, x ∈ uIcc a b → a < c → b < c → x < c := fun hx ha hb =>
    (Set.mem_uIcc.1 hx).elim (fun h => h.2.trans_lt hb) (fun h => h.2.trans_lt ha)
  have hza0 := hP.cote_nonneg hM
  have hK0 : 0 < K := one_div_pos.1 (hza0.trans_lt hMK)
  obtain ⟨hSg, Sg₁, A, B, hSg₁, hsub, hall⟩ := hmaj
  obtain ⟨φ₀, hφ₀, hS₀, -⟩ := id hSg₁
  have hMS : M ∈ Sg := hSg.left_mem
  have hNS : N ∈ Sg := hSg.right_mem
  have hMS₁ : M ∈ Sg₁ := hsub hMS
  have hMφ : M ∈ φ.source := hP.source_eq ▸ hM
  -- `ψ`: a compatible chart of a neighbourhood of `(A, B)` with the germ of `φ` at `M`
  obtain ⟨ψ, hψ, hψsrc, hgerm⟩ := exists_compatibleChart_germ hP.compatible hφ₀ hMφ (hS₀ hMS₁)
  have hS₁ψ : Sg₁ ⊆ ψ.source := hψsrc ▸ hS₀
  have hSψ : Sg ⊆ ψ.source := hsub.trans hS₁ψ
  have hψM : ψ M = φ M := hgerm.eq_of_nhds
  obtain ⟨-, himg₁⟩ := hSg₁.image_eq hψ hS₁ψ
  obtain ⟨-, himg⟩ := hSg.image_eq hψ hSψ
  have htarget : Sphere.closedSeg (ψ A) (ψ B) ⊆ ψ.target := by
    rw [← himg₁]
    rintro _ ⟨x, hx, rfl⟩
    exact ψ.map_source (hS₁ψ hx)
  have hψMseg : ψ M ∈ Sphere.closedSeg (ψ A) (ψ B) := himg₁ ▸ mem_image_of_mem ψ hMS₁
  have hψNseg : ψ N ∈ Sphere.closedSeg (ψ A) (ψ B) := himg₁ ▸ mem_image_of_mem ψ (hsub hNS)
  have hψM_H : ψ M ∈ Sphere.openHemisphere l := hψM ▸ hP.mapsTo_hemi hM
  have hzM_eq : z ⟨ψ M, hψM_H⟩ = z ⟨φ M, hP.mapsTo_hemi hM⟩ := by
    congr 1
    exact Subtype.ext hψM
  have hzM1 : z ⟨ψ M, hψM_H⟩ < 1 := by
    rw [hzM_eq]
    calc _ < 1 / K := hMK
      _ < 1 := by rw [div_lt_one hK0]; exact (Real.log_pos_iff hK0.le).1 (by
          obtain ⟨φ', hφ', hS', -⟩ := id hSg₁
          exact EReal.coe_pos.1 ((Sphere.projMeasure_nonneg _ _ _ _).trans_lt (hall φ' hφ' hS')))
  -- the cross-ratio `(ψ M, ψ N, ψ B, ψ A) = r`, `|log r| < log K`
  have hlt := hall ψ hψ hS₁ψ
  obtain ⟨r, hr⟩ := Sphere.projMeasure_lt_top_iff.1 (hlt.trans (EReal.coe_lt_top _))
  rw [Sphere.projMeasure_eq hr] at hlt
  have hlogr : |Real.log r| < Real.log K := EReal.coe_lt_coe_iff.1 hlt
  have hK1 : 1 < K := (Real.log_pos_iff hK0.le).1 ((abs_nonneg _).trans_lt hlogr)
  obtain ⟨hr0, α, β, hαβ, hα, hβ, hαβM, hαβN⟩ := hr
  -- (H) condition *b* of the pocket on the sub-segments `(M, X)`, `X ∈ (A, B)`
  have hH : ∀ y ∈ Sphere.closedSeg (ψ A) (ψ B), y ≠ -ψ M →
      Sphere.closedSeg (ψ M) y ⊆ Sphere.openHemisphere l ∧
      ∀ hy : y ∈ Sphere.openHemisphere l, z ⟨y, hy⟩ < 1 → ψ.symm y ∈ P := by
    intro y hy hyM
    have hsub' : Sphere.closedSeg (ψ M) y ⊆ ψ.target :=
      (Sphere.closedSeg_subset_closedSeg hψMseg hy).trans htarget
    have hseg := isProjSegment_of_chart hψ hyM hsub'
    rw [ψ.left_inv (hS₁ψ hMS₁)] at hseg
    have hsrc : ψ.symm '' Sphere.closedSeg (ψ M) y ⊆ ψ.source := by
      rintro _ ⟨y', hy', rfl⟩
      exact ψ.map_target (hsub' hy')
    obtain ⟨h1, h2⟩ := hP.mem_of_segment _ M (ψ.symm y) hseg hM ψ hψ hsrc hgerm
    have hyt : y ∈ ψ.target := hsub' (Sphere.right_mem_closedSeg _ _)
    refine ⟨fun x hx => h1 ⟨ψ.symm x, ⟨x, hx, rfl⟩, ψ.right_inv (hsub' hx)⟩, fun hy' hz => ?_⟩
    have hyy : ψ (ψ.symm y) = y := ψ.right_inv hyt
    have hmem : ψ (ψ.symm y) ∈ Sphere.openHemisphere l := by rw [hyy]; exact hy'
    refine h2 hmem ?_
    have : (⟨ψ (ψ.symm y), hmem⟩ : Sphere.openHemisphere l) = ⟨y, hy'⟩ := Subtype.ext hyy
    rw [this]
    exact hz
  -- `ψ A`, `ψ B` lie in `H̊`, hence the whole segment
  have hli1 : LinearIndependent ℝ ![α + β, α] := by
    rw [LinearIndependent.pair_iff] at hαβ ⊢
    intro s t hst
    have := hαβ (s + t) s (by rw [← hst]; module)
    exact ⟨this.2, by linarith [this.1, this.2]⟩
  have hli2 : LinearIndependent ℝ ![α + β, β] := by
    rw [LinearIndependent.pair_iff] at hαβ ⊢
    intro s t hst
    have := hαβ s (s + t) (by rw [← hst]; module)
    exact ⟨this.1, by linarith [this.1, this.2]⟩
  have hψA_H : ψ A ∈ Sphere.openHemisphere l :=
    (hH (ψ A) (Sphere.left_mem_closedSeg _ _)
      (Sphere.ne_of_linearIndependent hαβM hα hli1).2).1 (Sphere.right_mem_closedSeg _ _)
  have hψB_H : ψ B ∈ Sphere.openHemisphere l :=
    (hH (ψ B) (Sphere.right_mem_closedSeg _ _)
      (Sphere.ne_of_linearIndependent hαβM hβ hli2).2).1 (Sphere.right_mem_closedSeg _ _)
  have hseg_H : ∀ y ∈ Sphere.closedSeg (ψ A) (ψ B), y ∈ Sphere.openHemisphere l := fun y hy =>
    (Sphere.cote_mem_uIcc z hψA_H hψB_H hy).1
  -- (F) a sub-segment `(M, y)` on which `z < 1` lies in `P`, where `φ = ψ`
  have hF : ∀ y ∈ Sphere.closedSeg (ψ A) (ψ B), ∀ hy : y ∈ Sphere.openHemisphere l,
      z ⟨y, hy⟩ < 1 → ψ.symm '' Sphere.closedSeg (ψ M) y ⊆ P ∧
        EqOn φ ψ (ψ.symm '' Sphere.closedSeg (ψ M) y) := by
    intro y hy hyH hzy
    have hsub' : Sphere.closedSeg (ψ M) y ⊆ Sphere.closedSeg (ψ A) (ψ B) :=
      Sphere.closedSeg_subset_closedSeg hψMseg hy
    have hsubT := hsub'.trans htarget
    have hPsub : ψ.symm '' Sphere.closedSeg (ψ M) y ⊆ P := by
      rintro _ ⟨y', hy', rfl⟩
      have hy'AB := hsub' hy'
      have hy'H := hseg_H y' hy'AB
      obtain ⟨hy'H', hz'⟩ := Sphere.cote_mem_uIcc z hψM_H hyH hy'
      exact (hH y' hy'AB (Sphere.ne_neg_of_mem_openHemisphere hψM_H hy'H)).2 hy'H'
        (hlt1 hz' hzM1 hzy)
    refine ⟨hPsub, ?_⟩
    have hseg : IsProjSegment n (ψ.symm '' Sphere.closedSeg (ψ M) y) M (ψ.symm y) := by
      have := isProjSegment_of_chart hψ (Sphere.ne_neg_of_mem_openHemisphere hψM_H hyH) hsubT
      rwa [ψ.left_inv (hS₁ψ hMS₁)] at this
    have hsrcψ : ψ.symm '' Sphere.closedSeg (ψ M) y ⊆ ψ.source := by
      rintro _ ⟨y', hy', rfl⟩
      exact ψ.map_target (hsubT hy')
    exact eqOn_of_germ_eq (G := GSR n) hP.compatible hψ hseg.isPreconnected
      (hPsub.trans hP.source_eq.symm.subset) hsrcψ hseg.left_mem hgerm.symm
  -- the computation, for an orientation `f = s(a)`, `a ↦ M`, `b ↦ N` with `ρ ≥ 1`
  obtain ⟨Λ, hΛ⟩ := Sphere.exists_linear_cote z
  have key : ∀ (a b : Fin (n + 1) → ℝ) (ρ : ℝ) (X₁ X₂ : S n),
      X₁ ∈ Sphere.closedSeg (ψ A) (ψ B) → X₂ ∈ Sphere.closedSeg (ψ A) (ψ B) →
      Sphere.IsRep a X₁ → Sphere.IsRep b X₂ → Sphere.IsRep (a + b) (ψ M) →
      Sphere.IsRep (a + ρ • b) (ψ N) → 1 ≤ ρ → ρ < K →
      Sg ⊆ P ∧ ∃ hN : N ∈ P, z ⟨φ N, hP.mapsTo_hemi hN⟩ ≤ K * z ⟨φ M, hP.mapsTo_hemi hM⟩ ∧
        (0 < z ⟨φ M, hP.mapsTo_hemi hM⟩ →
          z ⟨φ N, hP.mapsTo_hemi hN⟩ < K * z ⟨φ M, hP.mapsTo_hemi hM⟩) := by
    intro a b ρ X₁ X₂ hX₁ hX₂ ha hb hab habN hρ hρK
    have hX₁H := hseg_H X₁ hX₁
    have hX₂H := hseg_H X₂ hX₂
    have hla : 0 < l a := by
      obtain ⟨h0, h⟩ := ha
      rw [← h] at hX₁H
      exact (Sphere.mk_mem_openHemisphere h0).1 hX₁H
    have hlb : 0 < l b := by
      obtain ⟨h0, h⟩ := hb
      rw [← h] at hX₂H
      exact (Sphere.mk_mem_openHemisphere h0).1 hX₂H
    have hψN_H := hseg_H _ hψNseg
    have hzM : z ⟨ψ M, hψM_H⟩ = (Λ a + Λ b) / (l a + l b) := by
      rw [Sphere.cote_eq_div hΛ hab hψM_H, map_add, map_add]
    have hzN : z ⟨ψ N, hψN_H⟩ = (Λ a + ρ * Λ b) / (l a + ρ * l b) := by
      rw [Sphere.cote_eq_div hΛ habN hψN_H, map_add, map_add, map_smul, map_smul, smul_eq_mul,
        smul_eq_mul]
    have hzf : z ⟨X₁, hX₁H⟩ = Λ a / l a := Sphere.cote_eq_div hΛ ha hX₁H
    have ha0 : 0 ≤ (Λ a + Λ b) / (l a + l b) := by
      rw [← hzM, hzM_eq]
      exact hza0
    have hf : Λ a / l a < (Λ a + Λ b) / (l a + l b) → 0 ≤ Λ a / l a := by
      intro hlt'
      have hzX₁ : z ⟨X₁, hX₁H⟩ < 1 := by
        rw [hzf]
        exact hlt'.trans (hzM ▸ hzM1)
      obtain ⟨hPX, hEq⟩ := hF X₁ hX₁ hX₁H hzX₁
      have hmem : ψ.symm X₁ ∈ ψ.symm '' Sphere.closedSeg (ψ M) X₁ :=
        mem_image_of_mem _ (Sphere.right_mem_closedSeg _ _)
      have h1 := hP.cote_nonneg (hPX hmem)
      have h2 : φ (ψ.symm X₁) = X₁ := (hEq hmem).trans (ψ.right_inv (htarget hX₁))
      have : (⟨φ (ψ.symm X₁), hP.mapsTo_hemi (hPX hmem)⟩ : Sphere.openHemisphere l) =
          ⟨X₁, hX₁H⟩ := Subtype.ext h2
      rw [this, hzf] at h1
      exact h1
    obtain ⟨hle, hlt'⟩ := septieme_alg hla hlb hρ hρK ha0 hf
    have hzN1 : z ⟨ψ N, hψN_H⟩ < 1 := by
      rw [hzN]
      calc _ ≤ K * ((Λ a + Λ b) / (l a + l b)) := hle
        _ < K * (1 / K) := by
          rw [← hzM, hzM_eq]
          exact mul_lt_mul_of_pos_left hMK hK0
        _ = 1 := by field_simp
    obtain ⟨hPN, hEqN⟩ := hF (ψ N) hψNseg hψN_H hzN1
    have hSg_eq : ψ.symm '' Sphere.closedSeg (ψ M) (ψ N) = Sg := by
      rw [← himg]
      exact ψ.toPartialEquiv.symm_image_image_of_subset_source hSψ
    rw [hSg_eq] at hPN hEqN
    have hN : N ∈ P := hPN hNS
    have hzN_eq : z ⟨φ N, hP.mapsTo_hemi hN⟩ = z ⟨ψ N, hψN_H⟩ := by
      congr 1
      exact Subtype.ext (hEqN hNS)
    refine ⟨hPN, hN, ?_, fun hpos => ?_⟩
    · rw [hzN_eq, hzN, ← hzM_eq, hzM]
      exact hle
    · rw [hzN_eq, hzN, ← hzM_eq, hzM]
      rw [← hzM_eq, hzM] at hpos
      exact hlt' hpos
  -- the two orientations
  have hrK : ∀ {ρ : ℝ}, 0 < ρ → Real.log ρ < Real.log K → ρ < K := fun hρ h =>
    (Real.log_lt_log_iff hρ hK0).1 h
  rcases le_or_gt 1 r with hr1 | hr1
  · exact key α β r (ψ A) (ψ B) (Sphere.left_mem_closedSeg _ _) (Sphere.right_mem_closedSeg _ _)
      hα hβ hαβM hαβN hr1 (hrK hr0 ((le_abs_self _).trans_lt hlogr))
  · refine key β α r⁻¹ (ψ B) (ψ A) (Sphere.right_mem_closedSeg _ _)
      (Sphere.left_mem_closedSeg _ _) hβ hα (by rw [add_comm β α]; exact hαβM) ?_
      ((one_le_inv₀ hr0).2 hr1.le) (hrK (inv_pos.2 hr0) ?_)
    · have := hαβN.smul (inv_pos.2 hr0)
      convert this using 1
      rw [smul_add, smul_smul, inv_mul_cancel₀ hr0.ne', one_smul, add_comm β]
    · rw [Real.log_inv]
      exact (neg_le_abs _).trans_lt hlogr

end Septieme

/-- A pseudo-length below `c` is witnessed by a majorising `k < c`. -/
theorem exists_isMajoreSeg_of_pseudoLength_lt {n : ℕ} {V : Type u} [TopologicalSpace V]
    [ChartedSpace (S n) V] {Sg : Set V} {M N : V} {c : EReal} (h : pseudoLength n Sg M N < c) :
    ∃ k : ℝ, (k : EReal) < c ∧ IsMajoreSeg n k Sg M N := by
  obtain ⟨k, hk⟩ := iInf_lt_iff.1 h
  obtain ⟨hmaj, hk'⟩ := iInf_lt_iff.1 hk
  exact ⟨k, hk', hmaj⟩

section Septieme2

variable {n : ℕ} {V : Type u} [TopologicalSpace V] [ChartedSpace (S n) V]
  [HasGroupoid V (projGroupoid n)]
  {P : Set V} {l : Module.Dual ℝ (Fin (n + 1) → ℝ)} [Fact (l ≠ 0)]
  {φ : OpenPartialHomeomorph V (S n)} {z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ}

/-- **7°, corrected** (an unmarked lemma of the editorial enonce
`bzthm:c2s2_proprietes_pseudo_longueur`, l.253–256): « soit $M\in P$ un point de $V$ tel que
$z(\varphi(M))<\frac{1}{K}$ ; soit $(M, N)$ un segment de $V$ dont la pseudo-longueur
$l_V(M, N)$ soit inférieure à $\log K$ ; alors, $N\in P$ et $z\,\varphi(N)<K\,z(\varphi(M))$ » —
with `≤` in general and `<` when `z(φ(M)) > 0`; moreover `(M, N) ⊆ P`. -/
theorem IsPocheProj.septieme_propriete (hP : IsPocheProj P l φ z) {Sg : Set V} {M N : V}
    (hM : M ∈ P) {K : ℝ} (hMK : z ⟨φ M, hP.mapsTo_hemi hM⟩ < 1 / K)
    (hl : pseudoLength n Sg M N < (Real.log K : EReal)) :
    Sg ⊆ P ∧ ∃ hN : N ∈ P, z ⟨φ N, hP.mapsTo_hemi hN⟩ ≤ K * z ⟨φ M, hP.mapsTo_hemi hM⟩ ∧
      (0 < z ⟨φ M, hP.mapsTo_hemi hM⟩ →
        z ⟨φ N, hP.mapsTo_hemi hN⟩ < K * z ⟨φ M, hP.mapsTo_hemi hM⟩) := by
  obtain ⟨k, hk, hmaj⟩ := exists_isMajoreSeg_of_pseudoLength_lt hl
  exact hP.septieme_majore hM hMK (hmaj.mono (EReal.coe_lt_coe_iff.1 hk).le)

/-- **7° with its printed conclusion, when `z(φ(M)) > 0`.** -/
theorem IsPocheProj.septieme_propriete_of_pos (hP : IsPocheProj P l φ z) {Sg : Set V} {M N : V}
    (hM : M ∈ P) {K : ℝ} (hMK : z ⟨φ M, hP.mapsTo_hemi hM⟩ < 1 / K)
    (hpos : 0 < z ⟨φ M, hP.mapsTo_hemi hM⟩)
    (hl : pseudoLength n Sg M N < (Real.log K : EReal)) :
    ∃ hN : N ∈ P, z ⟨φ N, hP.mapsTo_hemi hN⟩ < K * z ⟨φ M, hP.mapsTo_hemi hM⟩ := by
  obtain ⟨-, hN, -, h⟩ := hP.septieme_propriete hM hMK hl
  exact ⟨hN, h hpos⟩

/-- **7° as printed, for every pocket whose cote is not identically `0`.** -/
theorem IsPocheProj.septieme_propriete_of_ne_zero (hP : IsPocheProj P l φ z) (hz : ∃ y, z y ≠ 0)
    {Sg : Set V} {M N : V} (hM : M ∈ P) {K : ℝ} (hMK : z ⟨φ M, hP.mapsTo_hemi hM⟩ < 1 / K)
    (hl : pseudoLength n Sg M N < (Real.log K : EReal)) :
    ∃ hN : N ∈ P, z ⟨φ N, hP.mapsTo_hemi hN⟩ < K * z ⟨φ M, hP.mapsTo_hemi hM⟩ :=
  hP.septieme_propriete_of_pos hM hMK (hP.cote_pos_of_ne_zero hz hM) hl

end Septieme2

/-! ### Prop. 6 — broken lines in a pocket -/

section Prop6

variable {n : ℕ} {V : Type u} [TopologicalSpace V] [ChartedSpace (S n) V]
  [HasGroupoid V (projGroupoid n)]
  {P : Set V} {l : Module.Dual ℝ (Fin (n + 1) → ℝ)} [Fact (l ≠ 0)]
  {φ : OpenPartialHomeomorph V (S n)} {z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ}

/-- Prop. 6 for `K > 0`, by induction on the broken line (« le passage de $p$ à $p+1$ est
immédiat »). -/
theorem IsPocheProj.ligne_brisee_poche_aux (hP : IsPocheProj P l φ z) {K : ℝ} (hK : 0 < K)
    {A B : V} {L : Set V} {p : ℕ} (hL : IsLigneBrisee n (Real.log K) p A B L) (hA : A ∈ P)
    (hAK : z ⟨φ A, hP.mapsTo_hemi hA⟩ < 1 / K ^ p) :
    L ⊆ P ∧ ∃ hB : B ∈ P, z ⟨φ B, hP.mapsTo_hemi hB⟩ ≤ K ^ p * z ⟨φ A, hP.mapsTo_hemi hA⟩ ∧
      (0 < z ⟨φ A, hP.mapsTo_hemi hA⟩ →
        z ⟨φ B, hP.mapsTo_hemi hB⟩ < K ^ p * z ⟨φ A, hP.mapsTo_hemi hA⟩) := by
  induction hL with
  | segment hmaj =>
    rw [pow_one] at hAK ⊢
    exact hP.septieme_majore hA hAK hmaj
  | @cons p Sg L' A X B hmaj _ ih =>
    have hK1 : 1 < K := (Real.log_pos_iff hK.le).1 hmaj.pos
    have hAK' : z ⟨φ A, hP.mapsTo_hemi hA⟩ < 1 / K := hAK.trans_le
      (one_div_le_one_div_of_le hK (le_self_pow₀ hK1.le (Nat.succ_ne_zero p)))
    obtain ⟨hSgP, hX, hX1, hX2⟩ := hP.septieme_majore hA hAK' hmaj
    have hKp : 0 < K ^ p := pow_pos hK p
    have hXK : z ⟨φ X, hP.mapsTo_hemi hX⟩ < 1 / K ^ p := by
      calc _ ≤ K * z ⟨φ A, hP.mapsTo_hemi hA⟩ := hX1
        _ < K * (1 / K ^ (p + 1)) := mul_lt_mul_of_pos_left hAK hK
        _ = 1 / K ^ p := by rw [pow_succ]; field_simp
    obtain ⟨hL'P, hB, hB1, -⟩ := ih hX hXK
    refine ⟨union_subset hSgP hL'P, hB, ?_, fun hpos => ?_⟩
    · calc _ ≤ K ^ p * z ⟨φ X, hP.mapsTo_hemi hX⟩ := hB1
        _ ≤ K ^ p * (K * z ⟨φ A, hP.mapsTo_hemi hA⟩) := mul_le_mul_of_nonneg_left hX1 hKp.le
        _ = K ^ (p + 1) * z ⟨φ A, hP.mapsTo_hemi hA⟩ := by rw [pow_succ]; ring
    · calc _ ≤ K ^ p * z ⟨φ X, hP.mapsTo_hemi hX⟩ := hB1
        _ < K ^ p * (K * z ⟨φ A, hP.mapsTo_hemi hA⟩) := mul_lt_mul_of_pos_left (hX2 hpos) hKp
        _ = K ^ (p + 1) * z ⟨φ A, hP.mapsTo_hemi hA⟩ := by rw [pow_succ]; ring

/-- **Prop. 6, corrected** (`bzprop:c2s2p6_ligne_brisee_poche`): a broken line `L` of `p` segments
majorised by `log K`, from `A ∈ P` with `z(φ(A)) < 1/K^p` to `B`, lies in `P`, and
`z(φ(B)) ≤ K^p z(φ(A))`, strictly when `z(φ(A)) > 0`. Any real `K`. -/
theorem IsPocheProj.ligne_brisee_poche (hP : IsPocheProj P l φ z) {A B : V} {L : Set V} {p : ℕ}
    {K : ℝ} (hL : IsLigneBrisee n (Real.log K) p A B L) (hA : A ∈ P)
    (hAK : z ⟨φ A, hP.mapsTo_hemi hA⟩ < 1 / K ^ p) :
    L ⊆ P ∧ ∃ hB : B ∈ P, z ⟨φ B, hP.mapsTo_hemi hB⟩ ≤ K ^ p * z ⟨φ A, hP.mapsTo_hemi hA⟩ ∧
      (0 < z ⟨φ A, hP.mapsTo_hemi hA⟩ →
        z ⟨φ B, hP.mapsTo_hemi hB⟩ < K ^ p * z ⟨φ A, hP.mapsTo_hemi hA⟩) := by
  have hA0 := hP.cote_nonneg hA
  rcases lt_trichotomy K 0 with hK | rfl | hK
  · -- `K < 0`: `log K = log (-K)`; for `p` odd the hypothesis is void
    rcases Nat.even_or_odd p with hp | hp
    · have h1 : K ^ p = (-K) ^ p := (hp.neg_pow K).symm
      rw [← Real.log_neg_eq_log] at hL
      rw [h1] at hAK ⊢
      exact hP.ligne_brisee_poche_aux (neg_pos.2 hK) hL hA hAK
    · exfalso
      have h1 : 1 / K ^ p < 0 := one_div_neg.2 (hp.pow_neg_iff.2 hK)
      linarith
  · -- `K = 0`: `log 0 = 0` majorises no segment
    exfalso
    have := hL.pos
    rw [Real.log_zero] at this
    exact lt_irrefl 0 this
  · exact hP.ligne_brisee_poche_aux hK hL hA hAK

/-- **Prop. 6 with its printed conclusion, when `z(φ(A)) > 0`.** -/
theorem IsPocheProj.ligne_brisee_poche_of_pos (hP : IsPocheProj P l φ z) {A B : V} {L : Set V}
    {p : ℕ} {K : ℝ} (hL : IsLigneBrisee n (Real.log K) p A B L) (hA : A ∈ P)
    (hAK : z ⟨φ A, hP.mapsTo_hemi hA⟩ < 1 / K ^ p) (hpos : 0 < z ⟨φ A, hP.mapsTo_hemi hA⟩) :
    L ⊆ P ∧ ∃ hB : B ∈ P, z ⟨φ B, hP.mapsTo_hemi hB⟩ < K ^ p * z ⟨φ A, hP.mapsTo_hemi hA⟩ := by
  obtain ⟨hLP, hB, -, h⟩ := hP.ligne_brisee_poche hL hA hAK
  exact ⟨hLP, hB, h hpos⟩

/-- **Prop. 6 as printed, for every pocket whose cote is not identically `0`.** -/
theorem IsPocheProj.ligne_brisee_poche_of_ne_zero (hP : IsPocheProj P l φ z) (hz : ∃ y, z y ≠ 0)
    {A B : V} {L : Set V} {p : ℕ} {K : ℝ} (hL : IsLigneBrisee n (Real.log K) p A B L)
    (hA : A ∈ P) (hAK : z ⟨φ A, hP.mapsTo_hemi hA⟩ < 1 / K ^ p) :
    L ⊆ P ∧ ∃ hB : B ∈ P, z ⟨φ B, hP.mapsTo_hemi hB⟩ < K ^ p * z ⟨φ A, hP.mapsTo_hemi hA⟩ :=
  hP.ligne_brisee_poche_of_pos hL hA hAK (hP.cote_pos_of_ne_zero hz hA)

end Prop6

/-! ### The printed 7° and Prop. 6 fail for the cote `z = 0` -/

/-- **7° as printed**, for the manifolds of dimension `n` (Hausdorff, connected, second countable). -/
def SeptiemeProprietePrinted (n : ℕ) : Prop :=
  ∀ (V : Type) [TopologicalSpace V] [ChartedSpace (S n) V] [HasGroupoid V (projGroupoid n)]
    [T2Space V] [ConnectedSpace V] [SecondCountableTopology V] (P : Set V)
    (l : Module.Dual ℝ (Fin (n + 1) → ℝ)) [Fact (l ≠ 0)] (φ : OpenPartialHomeomorph V (S n))
    (z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ) (hP : IsPocheProj P l φ z) (M : V) (hM : M ∈ P)
    (K : ℝ), 1 < K → z ⟨φ M, hP.mapsTo_hemi hM⟩ < 1 / K → ∀ (Sg : Set V) (N : V),
      IsProjSegment n Sg M N → pseudoLength n Sg M N < (Real.log K : EReal) →
        ∃ hN : N ∈ P, z ⟨φ N, hP.mapsTo_hemi hN⟩ < K * z ⟨φ M, hP.mapsTo_hemi hM⟩

/-- **Prop. 6 as printed**, for the manifolds of dimension `n`. -/
def LigneBriseePochePrinted (n : ℕ) : Prop :=
  ∀ (V : Type) [TopologicalSpace V] [ChartedSpace (S n) V] [HasGroupoid V (projGroupoid n)]
    [T2Space V] [ConnectedSpace V] [SecondCountableTopology V] (P : Set V)
    (l : Module.Dual ℝ (Fin (n + 1) → ℝ)) [Fact (l ≠ 0)] (φ : OpenPartialHomeomorph V (S n))
    (z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ) (hP : IsPocheProj P l φ z) (A B : V) (L : Set V)
    (p : ℕ) (K : ℝ), IsLigneBrisee n (Real.log K) p A B L → ∀ hA : A ∈ P,
      z ⟨φ A, hP.mapsTo_hemi hA⟩ < 1 / K ^ p →
        L ⊆ P ∧ ∃ hB : B ∈ P, z ⟨φ B, hP.mapsTo_hemi hB⟩ < K ^ p * z ⟨φ A, hP.mapsTo_hemi hA⟩

/-- **A pocket of cote `0`** (Déf. 1′ allows it): `ℝⁿ` with its canonical locally projective
structure, `P = ℝⁿ`, `H̊ = H₀`, `φ = j` an affine isomorphism onto `H₀`, `z = 0` (the image by the
Remarque after Déf. 1′ of the affine pocket `(ℝⁿ, id, 0)`, `isPocheAff_model`). -/
theorem exists_isPocheProj_cote_zero (n : ℕ) :
    ∃ (φ : OpenPartialHomeomorph (Fin n → ℝ) (S n))
      (z : Sphere.openHemisphere (Sphere.lastForm n) →ᵃ[ℝ] ℝ),
      @IsPocheProj n (Fin n → ℝ) _ (projOfAff n (Fin n → ℝ)) univ (Sphere.lastForm n) _ φ z ∧
        ∀ y, z y = 0 := by
  obtain ⟨e⟩ := Sphere.nonempty_hemi_affineEquiv (l := Sphere.lastForm n)
    (Module.finrank_fin_fun ℝ)
  exact ⟨_, _, (isPocheAff_model n).toPocheProj e.symm, fun y => rfl⟩

/-- **7° holds as printed only in dimension `0`, where it is vacuous** (every pseudo-length is
`+∞`). For `n ≥ 1` the pocket of cote `0` on `ℝⁿ` and the point segment `(M, M)` refute it:
`z(φ(M)) < K z(φ(M))` reads `0 < 0`. -/
theorem septiemeProprietePrinted_iff {n : ℕ} : SeptiemeProprietePrinted n ↔ n = 0 := by
  constructor
  · intro h
    by_contra hn
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 hn
    letI : ChartedSpace (S n) (Fin n → ℝ) := projOfAff n (Fin n → ℝ)
    haveI : HasGroupoid (Fin n → ℝ) (projGroupoid n) := hasGroupoid_projOfAff
    obtain ⟨φ, z, hP, hz⟩ := exists_isPocheProj_cote_zero n
    have hseg : IsProjSegment n {(0 : Fin n → ℝ)} 0 0 := isProjSegment_singleton 0
    obtain ⟨hN, hlt⟩ := h (Fin n → ℝ) univ (Sphere.lastForm n) φ z hP 0 (mem_univ 0) 2 one_lt_two
      (by rw [hz]; norm_num) {0} 0 hseg
      (by rw [pseudoLength_self hn1 hseg]; exact EReal.coe_pos.2 (Real.log_pos one_lt_two))
    rw [hz] at hlt
    norm_num at hlt
  · rintro rfl V _ _ _ _ _ _ P l _ φ z hP M hM K _ _ Sg N _ hl
    rw [pseudoLength_eq_top_dim_zero] at hl
    exact absurd hl not_top_lt

/-- **Prop. 6 holds as printed only in dimension `0`, where it is vacuous** (there is no broken
line). For `n ≥ 1`, the pocket of cote `0` and the broken line `{M}` of one segment refute it. -/
theorem ligneBriseePochePrinted_iff {n : ℕ} : LigneBriseePochePrinted n ↔ n = 0 := by
  constructor
  · intro h
    by_contra hn
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 hn
    letI : ChartedSpace (S n) (Fin n → ℝ) := projOfAff n (Fin n → ℝ)
    haveI : HasGroupoid (Fin n → ℝ) (projGroupoid n) := hasGroupoid_projOfAff
    obtain ⟨φ, z, hP, hz⟩ := exists_isPocheProj_cote_zero n
    have hL : IsLigneBrisee n (Real.log 2) 1 (0 : Fin n → ℝ) 0 {0} :=
      IsLigneBrisee.segment (isMajoreSeg_singleton hn1 0 (Real.log_pos one_lt_two))
    obtain ⟨-, hB, hlt⟩ := h (Fin n → ℝ) univ (Sphere.lastForm n) φ z hP 0 0 {0} 1 2 hL
      (mem_univ 0) (by rw [hz]; norm_num)
    rw [hz] at hlt
    norm_num at hlt
  · rintro rfl V _ _ _ _ _ _ P l _ φ z hP A B L p K hL
    exact absurd hL not_isLigneBrisee_dim_zero

end Benzecri
