import Mathlib

/-!
# Chapter 3 § 5 — property I(V, W), convex unions of two convex sets, the contact set

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 3 § 5, journal pp. 276–278; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch3.tex` (checked against the scan, PDF pp. 50–51).
Target T-bz-c3-propriete-i. Over an arbitrary real vector space `E`, no topology on `E` unless a
statement says so.

* **`bzdef:c3s5d1_propriete_I`** — `benzecri1960_ch3.tex:1162` (Déf. 1, l.1162–1166) —
  `Benzecri.ProprieteI`. Instance: `proprieteI_segment_carre` (`[0,1]×{0}` in `[0,1]²`).
* `bzprop:c3s5p1_reunion_convexe_supports` — `benzecri1960_ch3.tex:1169` (Prop. 1,
  l.1169–1175, proof l.1177–1181) — the first sentence `prop1_supports` (closed, under the sole
  hypothesis that `U ∪ V` is convex); the « façon plus précise » holds except when
  `U = V = {p}`: `prop1_precis`; it fails there: `not_prop1_precisPrinted` (imprecise: two
  non-disjoint sets, which § 5's title rules out; `prop1_precis_of_disjoint`).
* **`bzprop:c3s5p5_support_complementaire`** — `benzecri1960_ch3.tex:1224` (Prop. 5,
  l.1224–1227, proof l.1229–1235) — `prop5_support_complementaire` (« V fermé » read as: every
  line meets `V` in a closed set, `FermeLineaire`), `prop5_fort` (no convexity of `V`, no `I`,
  no common support needed), `prop5_topologique` (`V` closed for ANY topology on `E` in which
  lines are continuous). Sharpness: `prop5_sans_ferme`.
* **`bzdef:c3s5d2_ensemble_contact`** — `benzecri1960_ch3.tex:1237` (Déf. 2, l.1237–1242) —
  `Benzecri.ensembleContact`. Instance: `ensembleContact_Ico_Icc` (the contact set of
  `[−1, 0[` and `[0, 1]` in `ℝ` is `{0}`).
* `bzprop:c3s5p6_contact_convexe` — `benzecri1960_ch3.tex:1244` (Prop. 6, l.1244–1246, proof
  l.1248–1256) — FALSE as printed: `not_convex_ensembleContact` (two disjoint convex sets of
  `ℝ³` whose contact set contains `(0,0,0)` and `(2,0,0)` but not `(1,0,0)`), also under the
  reading « `A` entre `B` et `C` » (`not_convex_ensembleContactEntre`). True forms:
  `convex_ensembleContact_of_convex_union`, `convex_ensembleContactEntre_of_convex_union`
  (when `U ∪ V` is convex, the setting of § 5's title and of Prop. 7, where `F` is the contact
  set of `V` and `W − V`) and `convex_contactSansAlignement` (what the printed proof proves:
  the contact set without the alignment condition is convex, for any two convex sets).

> **Définition 1.** Soit $W$ un convexe dans un espace vectoriel; $V\subset W$ : on dit que $V$
> possède relativement à $W$ la propriété $I$ si $V$ et $W-V$ sont tous deux convexes, et l'on
> écrira : $I(V, W)$.
>
> **Proposition 1.** Si la réunion $W$ de deux convexes $U$ et $V$ est convexe, l'une des
> variétés support est contenue dans l'autre.
> D'une façon plus précise : ou bien tout point de $U$ est aligné avec deux points distincts de
> $V$, ou bien tout point de $V$ est aligné avec deux points distincts de $U$.
>
> **Proposition 5.** Soient $V$, $W$ convexes de même support $L$, $V$ fermé, $V\subset W$,
> $I(V, W)$ : alors, ou bien $V=W$, ou bien le support de $W-V$ est $L$.
>
> **Définition 2.** Soient $U$, $V$ deux convexes tels que $U\cap V=\emptyset$. On appelle
> *ensemble de contact* de $U$ et $V$ l'ensemble $F$ des points $A$ tels qu'il existe deux points
> $B$ et $C$ alignés avec $A$, et tels que $)B, A(\subset U$; $)A, C(\subset V$ (comme dans § 1,
> déf. 1, $)A, A($ désigne $\{A\}$).
>
> **Proposition 6.** L'ensemble de contact $F$ de deux convexes est conxexe. [sic: convexe]

## The proofs formalized

Prop. 1 follows the printed proof, which uses only `[a, b] ⊆ U ∪ V`: if `a ∈ U` is not aligned
with two distinct points of `V`, then for `b ∈ V`, `b ≠ a`, no point of `)a, b(` lies in `V`, so
`)a, b( ⊆ U` and `b` is aligned with two of its points; `b = a` forces `V = {a}`. The supports
follow since a point on a line through two points of `V` lies in the support of `V`.
Prop. 5 follows the printed proof: for `C ∈ W − V` and `A ∈ V`, the parameters `t` with
`C + t (A − C) ∈ V` form a closed set missing `0`, so a point `D ≠ C` of `)C, A(` lies in `W − V`
and `A` is on the line `CD`. Prop. 6: the printed proof takes the convex combinations
`B″ = (1−λ)B + λB′`, `C″ = (1−λ)C + λC′` for the point `(1−λ)A + λA′`; they satisfy the two
inclusions, but `B″, A″, C″` need not be aligned, which is where the printed statement fails.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| « dans un espace vectoriel » (real) | ✓ carried: `[AddCommGroup E] [Module ℝ E]`, any dimension, no topology |
| Déf. 1: « $W$ un convexe », « $V\subset W$ » | ✓ carried: `V ⊆ W` is a field of `ProprieteI`; `Convex ℝ W` is a hypothesis wherever used |
| Prop. 1: « deux convexes $U$ et $V$ » | weakened (Lean ≥ paper): not used, only `Convex ℝ (U ∪ V)`; `prop1_supports_printed` carries them |
| Prop. 1: « variétés support » | ✓ `affineSpan ℝ U`, `affineSpan ℝ V` |
| Prop. 1: « aligné avec deux points distincts de $V$ » | ✓ `AligneDeuxPoints V a`: `∃ b c ∈ V, b ≠ c ∧ a ∈ line[ℝ, b, c]` |
| Prop. 5: « $V$, $W$ convexes de même support $L$ », « $I(V, W)$ » | ✓ carried in `prop5_support_complementaire`; `prop5_fort` uses only `Convex ℝ W` |
| Prop. 5: « $V$ fermé » (bare vector space) | ✓ read as `FermeLineaire V` (every line meets `V` in a closed set of `ℝ`), which is what the proof uses, and implied by `IsClosed V` for every topology on `E` in which `t ↦ x + t v` is continuous (`fermeLineaire_of_isClosed`): every vector topology, the finest locally convex one, the finest one making finite-dimensional subspaces' inclusions continuous |
| Déf. 2: « $U\cap V=\emptyset$ » | ✓ carried in the counterexample; not needed by the true forms |
| Déf. 2: « $B$ et $C$ alignés avec $A$ » | ✓ `Collinear ℝ {B, A, C}`; the reading « $A$ entre $B$ et $C$ » is `ensembleContactEntre` (`Wbtw ℝ B A C`), refuted and proved likewise |
| Déf. 2: « $)A, A($ désigne $\{A\}$ » | ✓ Mathlib's `openSegment_same` |

## SCOPE (disclosed)

* Prop. 1 is not marked: its second sentence fails for `U = V = {p}` (`not_prop1_precisPrinted`),
  a degenerate case (imprecise). Its first sentence is proved without exception. The exception
  consists of two non-disjoint sets, which § 5's title (« réunions de deux convexes disjoints »)
  rules out: for disjoint `U`, `V` the precise form holds (`prop1_precis_of_disjoint`). Whether
  the title is a standing hypothesis of Prop. 1 is the author's reading.
* Prop. 5 is marked: `FermeLineaire` is implied by closedness for every topology on `E` in
  which lines are continuous
  (`prop5_topologique`), so the Lean statement is at least the paper's.
* Prop. 6 is not marked: false as printed (`not_convex_ensembleContact`, in `ℝ³`, `U ∩ V = ∅`).
  The counterexample uses degenerate witnesses: `B = A` for `(0,0,0)` and `C = A` for
  `(2,0,0)`, which the printed convention `)A, A( = {A}` of Déf. 2 explicitly allows; under a
  reading demanding `B ≠ A ≠ C` these two points would not be contact points of these sets.
* The proof of Prop. 1 prints « le segment demi-ouvert $]a, b]$ soit contenu dans $U$ »; the
  endpoint `b` need not lie in `U` (`U = [0,1[`, `V = {1}`, `a = 0`); `)a, b(` suffices.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open Set

namespace Benzecri

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-! ### Déf. 1 -/

/-- **Déf. 1.** `I(V, W)`: `V ⊆ W`, and `V` and `W − V` are both convex (`W` convex is the
ambient hypothesis of the definition, carried by each statement that uses it). -/
def ProprieteI (V W : Set E) : Prop :=
  V ⊆ W ∧ Convex ℝ V ∧ Convex ℝ (W \ V)

/-- **Déf. 1, instance.** `[0,1]×{0}` has property `I` relative to the square `[0,1]²`. -/
theorem proprieteI_segment_carre :
    ProprieteI (Icc (0 : ℝ) 1 ×ˢ ({0} : Set ℝ)) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := by
  have hdiff : Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 \ Icc (0 : ℝ) 1 ×ˢ ({0} : Set ℝ) =
      Icc (0 : ℝ) 1 ×ˢ Ioc 0 1 := by
    ext ⟨x, y⟩
    simp only [mem_sdiff, mem_prod, mem_Icc, mem_singleton_iff, mem_Ioc]
    constructor
    · rintro ⟨⟨hx, hy1, hy2⟩, h⟩
      exact ⟨hx, lt_of_le_of_ne hy1 (fun h' => h ⟨hx, h'.symm⟩), hy2⟩
    · rintro ⟨hx, hy1, hy2⟩
      exact ⟨⟨hx, hy1.le, hy2⟩, fun h => hy1.ne' h.2⟩
  refine ⟨prod_mono subset_rfl (singleton_subset_iff.2 ⟨le_rfl, zero_le_one⟩),
    (convex_Icc 0 1).prod (convex_singleton 0), ?_⟩
  rw [hdiff]
  exact (convex_Icc 0 1).prod (convex_Ioc 0 1)

/-! ### Prop. 1 -/

/-- A point given by an explicit affine combination of `x` and `y` lies on the line `xy`. -/
theorem mem_line_of_eq {x y p : E} (r : ℝ) (h : p = (1 - r) • x + r • y) :
    p ∈ line[ℝ, x, y] := by
  rw [h, ← AffineMap.lineMap_apply_module]
  exact AffineMap.lineMap_mem_affineSpan_pair _ _ _

/-- « `a` est aligné avec deux points distincts de `S` ». -/
def AligneDeuxPoints (S : Set E) (a : E) : Prop :=
  ∃ b ∈ S, ∃ c ∈ S, b ≠ c ∧ a ∈ line[ℝ, b, c]

/-- The « façon plus précise » of Prop. 1, as printed. -/
def Prop1PrecisPrinted (U V : Set E) : Prop :=
  (∀ a ∈ U, AligneDeuxPoints V a) ∨ (∀ b ∈ V, AligneDeuxPoints U b)

/-- **Prop. 1, the precise form, strongest true version**: if `U ∪ V` is convex, the printed
dichotomy holds unless `U = V = {p}`. No convexity of `U`, `V` is needed. -/
theorem prop1_precis {U V : Set E} (hW : Convex ℝ (U ∪ V)) :
    Prop1PrecisPrinted U V ∨ ∃ p : E, U = {p} ∧ V = {p} := by
  by_cases h1 : ∀ a ∈ U, AligneDeuxPoints V a
  · exact Or.inl (Or.inl h1)
  obtain ⟨a, haU, ha⟩ : ∃ a ∈ U, ¬ AligneDeuxPoints V a := by
    by_contra h
    exact h1 fun a haU => by_contra fun h' => h ⟨a, haU, h'⟩
  by_cases hV1 : ∀ b ∈ V, b = a
  · by_cases hU1 : ∀ u ∈ U, u = a
    · by_cases hVne : V.Nonempty
      · right
        refine ⟨a, ?_, ?_⟩
        · exact Subset.antisymm (fun u hu => hU1 u hu) (singleton_subset_iff.2 haU)
        · obtain ⟨b, hb⟩ := hVne
          have hba := hV1 b hb
          subst hba
          exact Subset.antisymm (fun u hu => hV1 u hu) (singleton_subset_iff.2 hb)
      · exact Or.inl (Or.inr fun b hb => absurd ⟨b, hb⟩ hVne)
    · obtain ⟨u, huU, hua⟩ : ∃ u ∈ U, u ≠ a :=
        by_contra fun h => hU1 fun u hu => by_contra fun h' => h ⟨u, hu, h'⟩
      refine Or.inl (Or.inr fun b hb => ?_)
      rw [hV1 b hb]
      exact ⟨a, haU, u, huU, Ne.symm hua, left_mem_affineSpan_pair _ _ _⟩
  · obtain ⟨b', hb'V, hb'a⟩ : ∃ b' ∈ V, b' ≠ a :=
      by_contra fun h => hV1 fun u hu => by_contra fun h' => h ⟨u, hu, h'⟩
    refine Or.inl (Or.inr fun b hb => ?_)
    by_cases hba : b = a
    · subst hba
      exact absurd ⟨b, hb, b', hb'V, Ne.symm hb'a, left_mem_affineSpan_pair _ _ _⟩ ha
    -- the points of `)a, b(` lie in `U`
    have key : ∀ t : ℝ, 0 < t → t < 1 → (1 - t) • a + t • b ∈ U := by
      intro t ht0 ht1
      rcases hW (Or.inl haU) (Or.inr hb) (by linarith : (0 : ℝ) ≤ 1 - t) ht0.le (by ring) with
          h | h
      · exact h
      · exfalso
        apply ha
        refine ⟨(1 - t) • a + t • b, h, b, hb, ?_, ?_⟩
        · intro heq
          apply hba
          have h0 : (1 - t) • (b - a) = 0 := by
            have : (1 - t) • (b - a) = b - ((1 - t) • a + t • b) := by module
            rw [this, heq, sub_self]
          rcases smul_eq_zero.1 h0 with h0 | h0
          · exact absurd h0 (by linarith)
          · exact (sub_eq_zero.1 h0)
        · have hne : (1 - t) ≠ 0 := by linarith
          set r : ℝ := -t / (1 - t) with hr
          have e1 : (1 - r) * (1 - t) = 1 := by rw [hr]; field_simp; ring
          have e2 : (1 - r) * t + r = 0 := by rw [hr]; field_simp; ring
          refine mem_line_of_eq r ?_
          calc a = ((1 - r) * (1 - t)) • a + ((1 - r) * t + r) • b := by
                rw [e1, e2, one_smul, zero_smul, add_zero]
            _ = (1 - r) • ((1 - t) • a + t • b) + r • b := by module
    refine ⟨(1 - 1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b, key _ (by norm_num) (by norm_num),
      (1 - 1 / 3 : ℝ) • a + (1 / 3 : ℝ) • b, key _ (by norm_num) (by norm_num), ?_, ?_⟩
    · intro heq
      apply hba
      have h0 : (1 / 6 : ℝ) • (b - a) = 0 := by
        have : (1 / 6 : ℝ) • (b - a) =
            ((1 - 1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b) - ((1 - 1 / 3 : ℝ) • a + (1 / 3 : ℝ) • b) := by
          module
        rw [this, heq, sub_self]
      rcases smul_eq_zero.1 h0 with h0 | h0
      · norm_num at h0
      · exact sub_eq_zero.1 h0
    · exact mem_line_of_eq (-3) (by module)

/-- A set each of whose points is aligned with two distinct points of `V` lies in the
support of `V`. -/
theorem affineSpan_le_of_aligneDeuxPoints {U V : Set E} (h : ∀ a ∈ U, AligneDeuxPoints V a) :
    affineSpan ℝ U ≤ affineSpan ℝ V := by
  rw [affineSpan_le]
  intro a ha
  obtain ⟨b, hb, c, hc, -, hl⟩ := h a ha
  exact affineSpan_mono ℝ (pair_subset hb hc) hl

/-- **Prop. 1, first sentence**: if `U ∪ V` is convex, one support contains the other. -/
theorem prop1_supports {U V : Set E} (hW : Convex ℝ (U ∪ V)) :
    affineSpan ℝ U ≤ affineSpan ℝ V ∨ affineSpan ℝ V ≤ affineSpan ℝ U := by
  rcases prop1_precis hW with (h | h) | ⟨p, rfl, rfl⟩
  · exact Or.inl (affineSpan_le_of_aligneDeuxPoints h)
  · exact Or.inr (affineSpan_le_of_aligneDeuxPoints h)
  · exact Or.inl le_rfl

/-- **Prop. 1, first sentence, with the printed hypotheses.** -/
theorem prop1_supports_printed {U V : Set E} (_hU : Convex ℝ U) (_hV : Convex ℝ V)
    (hW : Convex ℝ (U ∪ V)) :
    affineSpan ℝ U ≤ affineSpan ℝ V ∨ affineSpan ℝ V ≤ affineSpan ℝ U :=
  prop1_supports hW

/-- **Prop. 1, precise form, for disjoint `U`, `V`** (the setting of § 5's title). -/
theorem prop1_precis_of_disjoint {U V : Set E} (hUV : Disjoint U V) (hW : Convex ℝ (U ∪ V)) :
    Prop1PrecisPrinted U V :=
  (prop1_precis hW).resolve_right fun ⟨p, hU, hV⟩ =>
    Set.disjoint_left.1 hUV (hU ▸ rfl : p ∈ U) (hV ▸ rfl : p ∈ V)

/-- **Prop. 1, the precise form is imprecise**: `U = V = {0}` in `ℝ` (two convex sets with a
convex union) satisfy neither alternative. -/
theorem not_prop1_precisPrinted :
    Convex ℝ ({0} : Set ℝ) ∧ Convex ℝ (({0} : Set ℝ) ∪ {0}) ∧
      ¬ Prop1PrecisPrinted ({0} : Set ℝ) {0} := by
  refine ⟨convex_singleton 0, by rw [union_self]; exact convex_singleton 0, ?_⟩
  have h : ¬ AligneDeuxPoints ({0} : Set ℝ) 0 := by
    rintro ⟨b, hb, c, hc, hbc, -⟩
    exact hbc ((mem_singleton_iff.1 hb).trans (mem_singleton_iff.1 hc).symm)
  rintro (h' | h') <;> exact h (h' 0 rfl)

/-! ### Prop. 5 -/

/-- « `V` fermé » in a bare vector space, in the form the proof uses: every line meets `V` in a
closed set of parameters. -/
def FermeLineaire (V : Set E) : Prop :=
  ∀ x v : E, IsClosed {t : ℝ | x + t • v ∈ V}

/-- Closedness for any topology on `E` in which lines are continuous implies `FermeLineaire`. -/
theorem fermeLineaire_of_isClosed [TopologicalSpace E]
    (hline : ∀ x v : E, Continuous fun t : ℝ => x + t • v) {V : Set E} (hV : IsClosed V) :
    FermeLineaire V :=
  fun x v => hV.preimage (hline x v)

/-- In particular for every topology making `E` a topological vector space. -/
theorem fermeLineaire_of_isClosed' [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]
    {V : Set E} (hV : IsClosed V) : FermeLineaire V :=
  fermeLineaire_of_isClosed (fun _ _ => by fun_prop) hV

/-- **Prop. 5, strong form**: `W` convex, `V ⊆ W` with closed traces on lines: either `V = W`
or the support of `W − V` is the support of `W`. -/
theorem prop5_fort {V W : Set E} (hW : Convex ℝ W) (hV : FermeLineaire V) (hVW : V ⊆ W) :
    V = W ∨ affineSpan ℝ (W \ V) = affineSpan ℝ W := by
  by_cases hVW' : V = W
  · exact Or.inl hVW'
  right
  obtain ⟨C, hCW, hCV⟩ : ∃ C, C ∈ W ∧ C ∉ V :=
    by_contra fun h => hVW' (Subset.antisymm hVW fun x hx => by_contra fun h' => h ⟨x, hx, h'⟩)
  refine le_antisymm (affineSpan_mono ℝ sdiff_subset) ?_
  rw [affineSpan_le]
  intro A hA
  by_cases hAV : A ∈ V
  swap
  · exact subset_affineSpan ℝ _ ⟨hA, hAV⟩
  have h0 : (0 : ℝ) ∈ {t : ℝ | C + t • (A - C) ∈ V}ᶜ := by simpa using hCV
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hV C (A - C)).isOpen_compl 0 h0
  set t : ℝ := min (ε / 2) (1 / 2) with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have htε : t < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hD : C + t • (A - C) ∉ V := by
    have : t ∈ Metric.ball (0 : ℝ) ε := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht0]; exact htε
    exact hball this
  have hDW : C + t • (A - C) ∈ W := by
    have := hW hCW hA (by linarith : (0 : ℝ) ≤ 1 - t) ht0.le (by ring)
    convert this using 1
    module
  have hmem : A ∈ line[ℝ, C, C + t • (A - C)] := by
    refine mem_line_of_eq (1 / t) ?_
    have e : (1 / t) * t = 1 := by field_simp
    calc A = C + ((1 / t) * t) • (A - C) := by rw [e, one_smul]; abel
      _ = (1 - 1 / t) • C + (1 / t) • (C + t • (A - C)) := by module
  have hle : line[ℝ, C, C + t • (A - C)] ≤ affineSpan ℝ (W \ V) :=
    affineSpan_mono ℝ (pair_subset ⟨hCW, hCV⟩ ⟨hDW, hD⟩)
  exact hle hmem

/-- **Prop. 5**, with the printed hypotheses (« fermé » read as `FermeLineaire`). -/
theorem prop5_support_complementaire {V W : Set E} (_hVc : Convex ℝ V) (hW : Convex ℝ W)
    (hL : affineSpan ℝ V = affineSpan ℝ W) (hV : FermeLineaire V) (hVW : V ⊆ W)
    (_hI : ProprieteI V W) :
    V = W ∨ affineSpan ℝ (W \ V) = affineSpan ℝ V := by
  rw [hL]; exact prop5_fort hW hV hVW

/-- **Prop. 5**, `V` closed for any topology on `E` in which lines are continuous. -/
theorem prop5_topologique [TopologicalSpace E]
    (hline : ∀ x v : E, Continuous fun t : ℝ => x + t • v) {V W : Set E} (hVc : Convex ℝ V)
    (hW : Convex ℝ W) (hL : affineSpan ℝ V = affineSpan ℝ W) (hV : IsClosed V) (hVW : V ⊆ W)
    (hI : ProprieteI V W) :
    V = W ∨ affineSpan ℝ (W \ V) = affineSpan ℝ V :=
  prop5_support_complementaire hVc hW hL (fermeLineaire_of_isClosed hline hV) hVW hI

/-- **Prop. 5, sharpness**: without « fermé » it fails: `V = ]0, 1]` in `W = [0, 1]`. -/
theorem prop5_sans_ferme :
    Convex ℝ (Ioc (0 : ℝ) 1) ∧ Convex ℝ (Icc (0 : ℝ) 1) ∧
      affineSpan ℝ (Ioc (0 : ℝ) 1) = affineSpan ℝ (Icc (0 : ℝ) 1) ∧
      ProprieteI (Ioc (0 : ℝ) 1) (Icc 0 1) ∧
      ¬ (Ioc (0 : ℝ) 1 = Icc 0 1 ∨
        affineSpan ℝ (Icc (0 : ℝ) 1 \ Ioc 0 1) = affineSpan ℝ (Ioc (0 : ℝ) 1)) := by
  have hdiff : Icc (0 : ℝ) 1 \ Ioc 0 1 = {0} := by
    ext x
    simp only [mem_sdiff, mem_Icc, mem_Ioc, mem_singleton_iff]
    constructor
    · rintro ⟨⟨h0, h1⟩, h⟩
      by_contra hx
      exact h ⟨lt_of_le_of_ne h0 (Ne.symm hx), h1⟩
    · rintro rfl
      exact ⟨⟨le_rfl, zero_le_one⟩, fun h => lt_irrefl _ h.1⟩
  have h0 : (0 : ℝ) ∈ affineSpan ℝ (Ioc (0 : ℝ) 1) := by
    have hl : (0 : ℝ) ∈ line[ℝ, (1 / 2 : ℝ), 1] := mem_line_of_eq (-1) (by norm_num)
    have hs : ({(1 / 2 : ℝ), 1} : Set ℝ) ⊆ Ioc 0 1 :=
      pair_subset (show (1 / 2 : ℝ) ∈ Ioc 0 1 by norm_num) (show (1 : ℝ) ∈ Ioc 0 1 by norm_num)
    exact affineSpan_mono ℝ hs hl
  have hspan : affineSpan ℝ (Ioc (0 : ℝ) 1) = affineSpan ℝ (Icc (0 : ℝ) 1) := by
    refine le_antisymm (affineSpan_mono ℝ Ioc_subset_Icc_self) ?_
    rw [affineSpan_le]
    intro x hx
    rcases eq_or_lt_of_le hx.1 with rfl | hx0
    · exact h0
    · exact subset_affineSpan ℝ _ ⟨hx0, hx.2⟩
  refine ⟨convex_Ioc 0 1, convex_Icc 0 1, hspan,
    ⟨Ioc_subset_Icc_self, convex_Ioc 0 1, by rw [hdiff]; exact convex_singleton 0⟩, ?_⟩
  rintro (h | h)
  · have : (0 : ℝ) ∈ Ioc (0 : ℝ) 1 := by rw [h]; exact ⟨le_rfl, zero_le_one⟩
    exact lt_irrefl _ this.1
  · rw [hdiff] at h
    have h1 : (1 : ℝ) ∈ affineSpan ℝ (Ioc (0 : ℝ) 1) := subset_affineSpan ℝ _ ⟨one_pos, le_rfl⟩
    rw [← h, AffineSubspace.mem_affineSpan_singleton] at h1
    exact one_ne_zero h1

/-! ### Déf. 2 -/

/-- **Déf. 2.** The contact set of `U` and `V`: the points `A` for which there are `B`, `C`
aligned with `A` with `)B, A( ⊆ U` and `)A, C( ⊆ V` (`)A, A( = {A}`: `openSegment_same`).
The hypothesis `U ∩ V = ∅` of the definition is carried by the statements. -/
def ensembleContact (U V : Set E) : Set E :=
  {A | ∃ B C : E, Collinear ℝ ({B, A, C} : Set E) ∧ openSegment ℝ B A ⊆ U ∧
    openSegment ℝ A C ⊆ V}

/-- **Déf. 2, instance**: the contact set of `[−1, 0[` and `[0, 1]` in `ℝ` is `{0}`. -/
theorem ensembleContact_Ico_Icc :
    ensembleContact (Ico (-1 : ℝ) 0) (Icc 0 1) = {0} := by
  ext A
  simp only [mem_singleton_iff]
  constructor
  · rintro ⟨B, C, -, hB, hC⟩
    have h1 : A ∈ Icc (0 : ℝ) 1 := by
      have := closure_minimal hC isClosed_Icc
      rw [closure_openSegment] at this
      exact this (left_mem_segment _ _ _)
    have h2 : A ∈ Iic (0 : ℝ) := by
      have := closure_minimal (hB.trans fun x hx => (show x ∈ Iic (0 : ℝ) from hx.2.le)) isClosed_Iic
      rw [closure_openSegment] at this
      exact this (right_mem_segment _ _ _)
    exact le_antisymm h2 h1.1
  · rintro rfl
    refine ⟨-1, 0, ?_, ?_, ?_⟩
    · exact (collinear_iff_of_mem (p₀ := (0 : ℝ)) (by simp)).2
        ⟨1, fun p _ => ⟨p, by simp⟩⟩
    · rw [openSegment_eq_Ioo (by norm_num)]
      exact Ioo_subset_Ico_self
    · rw [openSegment_same]
      exact singleton_subset_iff.2 ⟨le_rfl, zero_le_one⟩

/-! ### Prop. 6 -/

/-- The contact set without the alignment condition: what the printed proof of Prop. 6 handles. -/
def contactSansAlignement (U V : Set E) : Set E :=
  {A | ∃ B C : E, openSegment ℝ B A ⊆ U ∧ openSegment ℝ A C ⊆ V}

theorem ensembleContact_subset_sansAlignement (U V : Set E) :
    ensembleContact U V ⊆ contactSansAlignement U V := by
  rintro A ⟨B, C, -, hB, hC⟩; exact ⟨B, C, hB, hC⟩

/-- **Prop. 6, what the printed proof proves**: for `U`, `V` convex, the contact set without
the alignment condition is convex. -/
theorem convex_contactSansAlignement {U V : Set E} (hU : Convex ℝ U) (hV : Convex ℝ V) :
    Convex ℝ (contactSansAlignement U V) := by
  intro A hA A' hA' a b ha hb hab
  obtain ⟨B, C, hB, hC⟩ := hA
  obtain ⟨B', C', hB', hC'⟩ := hA'
  refine ⟨a • B + b • B', a • C + b • C', ?_, ?_⟩
  · rintro x ⟨s, s', hs, hs', hss, rfl⟩
    have h1 : s • B + s' • A ∈ U := hB ⟨s, s', hs, hs', hss, rfl⟩
    have h2 : s • B' + s' • A' ∈ U := hB' ⟨s, s', hs, hs', hss, rfl⟩
    convert hU h1 h2 ha hb hab using 1
    module
  · rintro x ⟨s, s', hs, hs', hss, rfl⟩
    have h1 : s • A + s' • C ∈ V := hC ⟨s, s', hs, hs', hss, rfl⟩
    have h2 : s • A' + s' • C' ∈ V := hC' ⟨s, s', hs, hs', hss, rfl⟩
    convert hV h1 h2 ha hb hab using 1
    module

/-- A point of the contact set of two disjoint sets whose union is convex lies in `U ∪ V`. -/
theorem mem_union_of_mem_ensembleContact {U V : Set E} (hUV : Disjoint U V)
    (hW : Convex ℝ (U ∪ V)) {A : E} (hA : A ∈ ensembleContact U V) : A ∈ U ∪ V := by
  obtain ⟨B, C, hcol, hB, hC⟩ := hA
  obtain ⟨v, hv⟩ := (collinear_iff_of_mem (p₀ := A) (by simp)).1 hcol
  obtain ⟨r₁, hr₁⟩ := hv B (by simp)
  obtain ⟨r₂, hr₂⟩ := hv C (by simp)
  rw [vadd_eq_add] at hr₁ hr₂
  by_cases h1 : r₁ = 0
  · left
    rw [h1, zero_smul, zero_add] at hr₁
    rw [hr₁, openSegment_same] at hB
    exact hB rfl
  by_cases h2 : r₂ = 0
  · right
    rw [h2, zero_smul, zero_add] at hr₂
    rw [hr₂, openSegment_same] at hC
    exact hC rfl
  rcases lt_or_gt_of_ne (mul_ne_zero h1 h2) with hneg | hpos
  · -- opposite sides: `A` is a convex combination of a point of `U` and a point of `V`
    have hQ1 : (1 / 2 : ℝ) • B + (1 / 2 : ℝ) • A ∈ U :=
      hB ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
    have hQ2 : (1 / 2 : ℝ) • A + (1 / 2 : ℝ) • C ∈ V :=
      hC ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
    have hd : r₂ - r₁ ≠ 0 := by
      intro h
      have : r₂ = r₁ := by linarith
      rw [this] at hneg
      nlinarith [mul_self_nonneg r₁]
    set α : ℝ := r₂ / (r₂ - r₁) with hα
    set β : ℝ := -r₁ / (r₂ - r₁) with hβ
    have hαβ : α + β = 1 := by rw [hα, hβ]; field_simp; ring
    have hr : α * r₁ + β * r₂ = 0 := by rw [hα, hβ]; field_simp; ring
    have hpos' : 0 ≤ α ∧ 0 ≤ β := by
      rcases lt_or_gt_of_ne h1 with h1' | h1'
      · have : 0 < r₂ := by
          by_contra h; push Not at h; nlinarith
        exact ⟨(div_pos this (by linarith)).le, (div_pos (by linarith) (by linarith)).le⟩
      · have : r₂ < 0 := by
          by_contra h; push Not at h; nlinarith
        exact ⟨(div_pos_of_neg_of_neg this (by linarith)).le,
          (div_pos_of_neg_of_neg (by linarith) (by linarith)).le⟩
    have hmem := hW (Or.inl hQ1) (Or.inr hQ2) hpos'.1 hpos'.2 hαβ
    convert hmem using 1
    rw [hr₁, hr₂]
    calc A = (α + β) • A + ((α * r₁ + β * r₂) / 2) • v := by rw [hαβ, hr]; simp
      _ = _ := by module
  · -- same side: `)B, A(` and `)A, C(` meet, against `U ∩ V = ∅`
    exfalso
    have hs : r₁ + r₂ ≠ 0 := by
      intro h
      have : r₂ = -r₁ := by linarith
      rw [this] at hpos
      nlinarith [mul_self_nonneg r₁]
    have hab : 0 < r₂ / (r₁ + r₂) ∧ 0 < r₁ / (r₁ + r₂) := by
      rcases lt_or_gt_of_ne h1 with h1' | h1'
      · have : r₂ < 0 := by
          by_contra h; push Not at h; nlinarith
        exact ⟨div_pos_of_neg_of_neg this (by linarith), div_pos_of_neg_of_neg h1' (by linarith)⟩
      · have : 0 < r₂ := by
          by_contra h; push Not at h; nlinarith
        exact ⟨div_pos this (by linarith), div_pos h1' (by linarith)⟩
    have hsum : r₂ / (r₁ + r₂) + r₁ / (r₁ + r₂) = 1 := by field_simp; ring
    have hXU : (r₂ / (r₁ + r₂)) • B + (r₁ / (r₁ + r₂)) • A ∈ U :=
      hB ⟨_, _, hab.1, hab.2, hsum, rfl⟩
    have hXV : (r₂ / (r₁ + r₂)) • A + (r₁ / (r₁ + r₂)) • C ∈ V :=
      hC ⟨_, _, hab.1, hab.2, hsum, rfl⟩
    have heq : (r₂ / (r₁ + r₂)) • B + (r₁ / (r₁ + r₂)) • A =
        (r₂ / (r₁ + r₂)) • A + (r₁ / (r₁ + r₂)) • C := by
      rw [hr₁, hr₂]; module
    rw [heq] at hXU
    exact Set.disjoint_left.1 hUV hXU hXV

/-- A point of the alignment-free contact set lying in `U ∪ V` is in the contact set. -/
theorem mem_ensembleContact_of_mem_union {U V : Set E} {A : E}
    (hA : A ∈ contactSansAlignement U V) (hAW : A ∈ U ∪ V) : A ∈ ensembleContact U V := by
  obtain ⟨B, C, hB, hC⟩ := hA
  rcases hAW with hAU | hAV
  · refine ⟨A, C, ?_, by rw [openSegment_same]; exact singleton_subset_iff.2 hAU, hC⟩
    rw [insert_idem]; exact collinear_pair ℝ A C
  · refine ⟨B, A, ?_, hB, by rw [openSegment_same]; exact singleton_subset_iff.2 hAV⟩
    rw [pair_eq_singleton]; exact collinear_pair ℝ B A

/-- **Prop. 6, true in the setting of § 5**: `U`, `V` disjoint convex sets whose union is
convex have a convex contact set. -/
theorem convex_ensembleContact_of_convex_union {U V : Set E} (hU : Convex ℝ U)
    (hV : Convex ℝ V) (hUV : Disjoint U V) (hW : Convex ℝ (U ∪ V)) :
    Convex ℝ (ensembleContact U V) := by
  intro A hA A' hA' a b ha hb hab
  exact mem_ensembleContact_of_mem_union
    (convex_contactSansAlignement hU hV (ensembleContact_subset_sansAlignement U V hA)
      (ensembleContact_subset_sansAlignement U V hA') ha hb hab)
    (hW (mem_union_of_mem_ensembleContact hUV hW hA)
      (mem_union_of_mem_ensembleContact hUV hW hA') ha hb hab)

/-- The two convex sets of the counterexample, in `ℝ × ℝ × ℝ` (coordinates `(x, y, z)`):
`U = {z = 0, y < 0} ∪ {0}`, `V = {y = 0, z > 0} ∪ {(2, 0, 0)}`. -/
def cexU : Set (ℝ × ℝ × ℝ) := {p | p.2.2 = 0 ∧ (p.2.1 < 0 ∨ (p.2.1 = 0 ∧ p.1 = 0))}

def cexV : Set (ℝ × ℝ × ℝ) := {p | p.2.1 = 0 ∧ (0 < p.2.2 ∨ (p.2.2 = 0 ∧ p.1 = 2))}

theorem convex_cexU : Convex ℝ cexU := by
  refine convex_iff_forall_pos.2 ?_
  rintro ⟨x, y, z⟩ ⟨hz, hy⟩ ⟨x', y', z'⟩ ⟨hz', hy'⟩ a b ha hb hab
  simp only at hz hy hz' hy'
  simp only [cexU, mem_setOf_eq, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  refine ⟨by rw [hz, hz']; ring, ?_⟩
  rcases hy with hy | ⟨hy, hx⟩ <;> rcases hy' with hy' | ⟨hy', hx'⟩
  · left; nlinarith [mul_neg_of_pos_of_neg ha hy, mul_neg_of_pos_of_neg hb hy']
  · left; rw [hy']; nlinarith [mul_neg_of_pos_of_neg ha hy]
  · left; rw [hy]; nlinarith [mul_neg_of_pos_of_neg hb hy']
  · right; rw [hy, hy', hx, hx']; constructor <;> ring

theorem convex_cexV : Convex ℝ cexV := by
  refine convex_iff_forall_pos.2 ?_
  rintro ⟨x, y, z⟩ ⟨hy, hz⟩ ⟨x', y', z'⟩ ⟨hy', hz'⟩ a b ha hb hab
  simp only at hz hy hz' hy'
  simp only [cexV, mem_setOf_eq, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  refine ⟨by rw [hy, hy']; ring, ?_⟩
  rcases hz with hz | ⟨hz, hx⟩ <;> rcases hz' with hz' | ⟨hz', hx'⟩
  · left; nlinarith [mul_pos ha hz, mul_pos hb hz']
  · left; rw [hz']; nlinarith [mul_pos ha hz]
  · left; rw [hz]; nlinarith [mul_pos hb hz']
  · right; rw [hz, hz', hx, hx']; constructor
    · ring
    · linear_combination 2 * hab

theorem disjoint_cexU_cexV : Disjoint cexU cexV := by
  refine Set.disjoint_left.2 ?_
  rintro ⟨x, y, z⟩ ⟨hz, hy⟩ ⟨hy', hz'⟩
  simp only at hz hy hy' hz'
  rcases hy with hy | ⟨-, hx⟩
  · linarith
  · rcases hz' with hz' | ⟨-, hx'⟩
    · linarith
    · linarith

theorem zero_mem_ensembleContact_cex :
    ((0, 0, 0) : ℝ × ℝ × ℝ) ∈ ensembleContact cexU cexV := by
  refine ⟨(0, 0, 0), (0, 0, 1), ?_, ?_, ?_⟩
  · rw [insert_idem]; exact collinear_pair ℝ _ _
  · rw [openSegment_same]
    exact singleton_subset_iff.2 ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩
  · rintro p ⟨a, b, ha, hb, hab, rfl⟩
    simp only [cexV, mem_setOf_eq, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
    exact ⟨by ring, Or.inl (by linarith)⟩

theorem two_mem_ensembleContact_cex :
    ((2, 0, 0) : ℝ × ℝ × ℝ) ∈ ensembleContact cexU cexV := by
  refine ⟨(2, -1, 0), (2, 0, 0), ?_, ?_, ?_⟩
  · rw [pair_eq_singleton]; exact collinear_pair ℝ _ _
  · rintro p ⟨a, b, ha, hb, hab, rfl⟩
    simp only [cexU, mem_setOf_eq, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
    exact ⟨by ring, Or.inl (by linarith)⟩
  · rw [openSegment_same]
    exact singleton_subset_iff.2 ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩

theorem one_not_mem_ensembleContact_cex :
    ((1, 0, 0) : ℝ × ℝ × ℝ) ∉ ensembleContact cexU cexV := by
  rintro ⟨B, C, hcol, hB, hC⟩
  obtain ⟨v, hv⟩ := (collinear_iff_of_mem (p₀ := ((1, 0, 0) : ℝ × ℝ × ℝ)) (by simp)).1 hcol
  obtain ⟨r₁, hr₁⟩ := hv B (by simp)
  obtain ⟨r₂, hr₂⟩ := hv C (by simp)
  rw [vadd_eq_add] at hr₁ hr₂
  subst hr₁ hr₂
  obtain ⟨vx, vy, vz⟩ := v
  have hU2 := hB ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
  have hU4 := hB ⟨1 / 4, 3 / 4, by norm_num, by norm_num, by norm_num, rfl⟩
  have hV2 := hC ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
  simp only [cexU, cexV, mem_setOf_eq, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul,
    mul_zero, add_zero, mul_one] at hU2 hU4 hV2
  obtain ⟨-, hy2⟩ := hU2
  obtain ⟨-, hy4⟩ := hU4
  obtain ⟨hvy, hvz⟩ := hV2
  -- `r₂ vy = 0`
  have e2 : r₂ * vy = 0 := by linarith
  rcases hy2 with hy2 | ⟨hy2, hx2⟩
  · -- `r₁ vy < 0`: then `vy ≠ 0`, so `r₂ = 0`, and `V` fails at `(1,0,0)`
    have hr₂ : r₂ = 0 := by
      rcases mul_eq_zero.1 e2 with h | h
      · exact h
      · rw [h] at hy2; linarith
    rw [hr₂] at hvz
    rcases hvz with h | ⟨-, h⟩ <;> linarith
  · rcases hy4 with hy4 | ⟨-, hx4⟩
    · linarith
    · linarith

/-- **Déf. 2, the other reading of « alignés »**: `A` between `B` and `C`. -/
def ensembleContactEntre (U V : Set E) : Set E :=
  {A | ∃ B C : E, Wbtw ℝ B A C ∧ openSegment ℝ B A ⊆ U ∧ openSegment ℝ A C ⊆ V}

theorem ensembleContactEntre_subset (U V : Set E) :
    ensembleContactEntre U V ⊆ ensembleContact U V := by
  rintro A ⟨B, C, hbtw, hB, hC⟩; exact ⟨B, C, hbtw.collinear, hB, hC⟩

/-- **Prop. 6 under the reading « `A` entre `B` et `C` »**, `U ∪ V` convex. -/
theorem convex_ensembleContactEntre_of_convex_union {U V : Set E} (hU : Convex ℝ U)
    (hV : Convex ℝ V) (hUV : Disjoint U V) (hW : Convex ℝ (U ∪ V)) :
    Convex ℝ (ensembleContactEntre U V) := by
  intro A hA A' hA' a b ha hb hab
  have hA1 := ensembleContactEntre_subset U V hA
  have hA1' := ensembleContactEntre_subset U V hA'
  obtain ⟨B, C, hB, hC⟩ := convex_contactSansAlignement hU hV
    (ensembleContact_subset_sansAlignement U V hA1)
    (ensembleContact_subset_sansAlignement U V hA1') ha hb hab
  rcases hW (mem_union_of_mem_ensembleContact hUV hW hA1)
      (mem_union_of_mem_ensembleContact hUV hW hA1') ha hb hab with hPU | hPV
  · exact ⟨_, C, wbtw_self_left _ _ _, by rw [openSegment_same]; exact singleton_subset_iff.2 hPU,
      hC⟩
  · exact ⟨B, _, wbtw_self_right _ _ _, hB,
      by rw [openSegment_same]; exact singleton_subset_iff.2 hPV⟩

/-- **Prop. 6 is false under the reading « entre » too**: same sets. -/
theorem not_convex_ensembleContactEntre :
    ((0, 0, 0) : ℝ × ℝ × ℝ) ∈ ensembleContactEntre cexU cexV ∧
      ((2, 0, 0) : ℝ × ℝ × ℝ) ∈ ensembleContactEntre cexU cexV ∧
      ((1, 0, 0) : ℝ × ℝ × ℝ) ∉ ensembleContactEntre cexU cexV ∧
      ¬ Convex ℝ (ensembleContactEntre cexU cexV) := by
  have h0 : ((0, 0, 0) : ℝ × ℝ × ℝ) ∈ ensembleContactEntre cexU cexV := by
    refine ⟨(0, 0, 0), (0, 0, 1), wbtw_self_left _ _ _, ?_, ?_⟩
    · rw [openSegment_same]
      exact singleton_subset_iff.2 ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩
    · rintro p ⟨a, b, ha, hb, hab, rfl⟩
      simp only [cexV, mem_setOf_eq, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
      exact ⟨by ring, Or.inl (by linarith)⟩
  have h2 : ((2, 0, 0) : ℝ × ℝ × ℝ) ∈ ensembleContactEntre cexU cexV := by
    refine ⟨(2, -1, 0), (2, 0, 0), wbtw_self_right _ _ _, ?_, ?_⟩
    · rintro p ⟨a, b, ha, hb, hab, rfl⟩
      simp only [cexU, mem_setOf_eq, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
      exact ⟨by ring, Or.inl (by linarith)⟩
    · rw [openSegment_same]
      exact singleton_subset_iff.2 ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩
  have h1 : ((1, 0, 0) : ℝ × ℝ × ℝ) ∉ ensembleContactEntre cexU cexV :=
    fun h => one_not_mem_ensembleContact_cex (ensembleContactEntre_subset _ _ h)
  refine ⟨h0, h2, h1, fun h => h1 ?_⟩
  have := h h0 h2 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  convert this using 1
  ext <;> simp

/-- **Prop. 6 is false as printed**: two disjoint convex sets of `ℝ³` whose contact set is not
convex: it contains `(0,0,0)` and `(2,0,0)`, not `(1,0,0)`. -/
theorem not_convex_ensembleContact :
    Convex ℝ cexU ∧ Convex ℝ cexV ∧ Disjoint cexU cexV ∧
      ((0, 0, 0) : ℝ × ℝ × ℝ) ∈ ensembleContact cexU cexV ∧
      ((2, 0, 0) : ℝ × ℝ × ℝ) ∈ ensembleContact cexU cexV ∧
      ((1, 0, 0) : ℝ × ℝ × ℝ) ∉ ensembleContact cexU cexV ∧
      ¬ Convex ℝ (ensembleContact cexU cexV) := by
  refine ⟨convex_cexU, convex_cexV, disjoint_cexU_cexV, zero_mem_ensembleContact_cex,
    two_mem_ensembleContact_cex, one_not_mem_ensembleContact_cex, fun h => ?_⟩
  have := h zero_mem_ensembleContact_cex two_mem_ensembleContact_cex
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  apply one_not_mem_ensembleContact_cex
  convert this using 1
  ext <;> simp

end Benzecri
