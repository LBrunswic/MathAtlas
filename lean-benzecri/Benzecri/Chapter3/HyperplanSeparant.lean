import Benzecri.Chapter3.ProprieteI
import Benzecri.Chapter3.FacetteOuverte

/-!
# Chapter 3 § 5, Prop. 7 — exactly one hyperplane separates `V` from `W − V`

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 3 § 5, journal pp. 278–279; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch3.tex` (to be checked by the author). Target
T-bz-c3-hyperplan-separant. Over an arbitrary real vector space `E`, any dimension.

* **`bzprop:c3s5p7_hyperplan_separant`** — `benzecri1960_ch3.tex:1258` (Prop. 7, l.1258–1262,
  proof l.1264–1321) — `Benzecri.hyperplan_separant_support` (the printed hypotheses: `L` with
  the finest locally convex topology `Benzecri.finestLC` of its direction, `V` closed in `L`),
  `Benzecri.hyperplan_separant_finestLC` (`V` closed in the ambient `finestLC E`),
  `Benzecri.hyperplan_separant` (« fermé » read as `FermeLineaire`, implied by both); the strong
  form of the proof `Benzecri.exists_separe_fort` (`W − V` in the open half-space, `H` the
  support of the contact set `F`, `H ∩ W = F`). « Hyperplan … séparant » is
  `Benzecri.SepareHyperplan`. Instance: `hyperplan_separant_rectangleBas`
  (`V = [0,1] × [0,1/2]`, `W = [0,1]²`, the line `y = 1/2`).

> **Proposition 7.** Soient $V$, $W$ deux convexes non vides de même support $L$, qu'on suppose
> muni de la topologie localement convexe la plus fine; supposons $V$ fermé, $V\neq W$,
> $I(V, W)$. Il existe alors un hyperplan et un seul séparant $V$ de $W-V=U$.
>
> *Démonstration* (extraits). L'ensemble de contact de $V$ et de $(W-V)$ est l'ensemble $F$ des
> points $A$ de $V$ tels qu'il existe un $B\in W$ avec $)A, B(\subset\complement V$; si un
> hyperplan $H$ sépare $V$ de $W-V$, on doit avoir $F\subset H$. Nous allons montrer que le
> support $H$ de $F$ est un hyperplan qui sépare $V$ de $W-V$, et que $H\cap W=F$. […] Or $H$ ne
> peut être tout l'espace $L$ […] : donc $H$ est un hyperplan. […] Pour établir que $H$ est
> effectivement de co-dimension $1$, il suffit de montrer que $U\cap H$ est vide.

## The proof formalized

It follows the printed proof, with its finite-dimensional step done once, by Mathlib's geometric
Hahn–Banach. Let `U = W − V`, `F` the contact set (`pointsContact`), `u₀ ∈ U`.
(1) *Crossing* (`exists_pointsContact`): on `[u₀, v]`, `v ∈ V`, the first point of `V` (the
infimum of a closed set of parameters, « V fermé ») is in `F`. Hence `L` is spanned by `F` and
`u₀` (`mem_affineSpan_insert_pointsContact`: « la codimension de $H$ est au plus 1 »).
(2) *Finite case* (`exists_separe_finset`): in the span `P` of finitely many points of `V`
meeting `U`, `U ∩ P` spans `P` by Prop. 5 (`prop5_fort`), so has interior in `P ≅ ℝⁿ`, and
`geometric_hahn_banach_of_nonempty_interior` separates it weakly from `V ∩ P`.
(3) *Strictness* (`lt_of_separe`): a weak separator not containing `V` has `U` in its open side:
for `u ∈ U ∩ H` and `C ∈ V` off `H`, `)u, C( ⊆ V`, and « V fermé » puts `u` in `V`.
(4) *`U ∩ affineSpan F = ∅`* (`not_mem_affineSpan_pointsContact`): the printed argument of
l.1307–1317, in a slice `P` spanned by points of `V` containing `B`, the `A_i` and points of
`)A_i, B_i(`.
(5) Then `affineSpan F` is a hyperplane of `L` (a linear form vanishing on its direction,
`Submodule.exists_dual_map_eq_bot_of_notMem`), and it separates (`exists_separe_fort`).
(6) *Uniqueness* (`separeHyperplan_unique`): every separator contains `F` (l.1266), hence its
support, and both are hyperplanes of `L`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| « $V$, $W$ deux convexes » | ✓ carried: `Convex ℝ W`; `Convex ℝ V` inside `ProprieteI V W` |
| « non vides » | ✓ carried (`V.Nonempty`, unused: it follows from `V ≠ W` and the common support); `W` non-empty follows |
| « de même support $L$ » | ✓ carried: `affineSpan ℝ V = affineSpan ℝ W` |
| « muni de la topologie localement convexe la plus fine » | ✓ carried: `finestLC` of the direction of `L`, origin `P ∈ L` (`hyperplan_separant_support`); or of `E` (`hyperplan_separant_finestLC`) |
| « $V$ fermé » | ✓ carried: `IsClosed` for that topology; the proof uses only `FermeLineaire V` (`hyperplan_separant`), which both imply |
| « $V\neq W$ », « $I(V, W)$ » | ✓ carried: `V ≠ W`, `ProprieteI V W` (`V ⊆ W`, `V` and `W − V` convex) |
| « un hyperplan … séparant $V$ de $W-V$ » | ✓ `SepareHyperplan L V (W \ V) H`: `H = L ∩ {f = c}`, `f` linear, not constant on `L`, `V ⊆ {f ≤ c}`, `W − V ⊆ {c ≤ f}`; existence also with `W − V ⊆ {c < f}` (`exists_separe_fort`) |
| « et un seul » | ✓ `∃!` over the set `H` |

## SCOPE (disclosed)

* Nothing is omitted, no `sorry`, no hypothesis added. The printed Prop. 6 (refuted,
  `not_convex_ensembleContact`) is not used, nor its true form: the proof needs no convexity of
  `F`. The proof's « $C$ n'appartient donc pas » (l.1317) is read « $B$ » (OQ-160 (a)); the
  statement does not depend on it.
* Readings, both fixed by the printed proof: « hyperplan » is a hyperplane of `L` (l.1275–1276
  « $H$ ne peut être tout l'espace $L$ … donc $H$ est un hyperplan »); the reading « hyperplane of
  the ambient space » fails when `L ≠ E` (`separeHyperplan_ambiant_deux`). « Séparant » is weak
  separation, closed half-spaces (l.1266 « on doit avoir $F\subset H$ », with `F ⊆ V`); the
  statement is proved for it, and existence also with `W − V` in the open half-space, so every
  reading in between holds; the reading with `V` in an open half-space fails
  (`inter_nonempty_of_separeHyperplan`: every separator meets `V`).
* The finite-dimensional case of the proof is not formalized separately with its interiors
  (« $\mathring{U}$ … $\mathring{V}$ … l'intérieur de $F$ »): Hahn–Banach in finite-dimensional
  slices, then the dimension-free steps (1), (3)–(6), covers both cases at once.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open Set Filter Topology

namespace Benzecri

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A linear form equal to `c` on `S` is equal to `c` on the affine span of `S`. -/
theorem linear_eq_of_mem_affineSpan (f : E →ₗ[ℝ] ℝ) {c : ℝ} {S : Set E} (hS : ∀ y ∈ S, f y = c)
    {x : E} (hx : x ∈ affineSpan ℝ S) : f x = c := by
  have h1 : f.toAffineMap x ∈ (affineSpan ℝ S).map f.toAffineMap :=
    AffineSubspace.mem_map.2 ⟨x, hx, rfl⟩
  rw [AffineSubspace.map_span] at h1
  have h2 : affineSpan ℝ (f.toAffineMap '' S) ≤ affineSpan ℝ {c} := by
    apply affineSpan_mono
    rintro _ ⟨y, hy, rfl⟩
    exact hS y hy
  have := h2 h1
  rw [AffineSubspace.mem_affineSpan_singleton] at this
  exact this

/-- If `c ≤ f` on the open segment `)A, B(`, then `c ≤ f A` (`f` linear). -/
theorem le_of_forall_openSegment (f : E →ₗ[ℝ] ℝ) {c : ℝ} {A B : E}
    (h : ∀ t : ℝ, 0 < t → t < 1 → c ≤ f ((1 - t) • A + t • B)) : c ≤ f A := by
  by_contra hlt
  push Not at hlt
  set δ := c - f A with hδ
  set M := |f B - f A| + 1 with hM
  have hδ0 : 0 < δ := by linarith
  have hM0 : 0 < M := by positivity
  set t := min (1 / 2) (δ / (2 * M)) with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have htM : t * M ≤ δ / 2 := by
    have : t ≤ δ / (2 * M) := min_le_right _ _
    calc t * M ≤ δ / (2 * M) * M := by gcongr
      _ = δ / 2 := by field_simp
  have key := h t ht0 ht1
  simp only [map_add, map_smul, smul_eq_mul] at key
  have habs : t * (f B - f A) ≤ t * M := by
    gcongr
    calc f B - f A ≤ |f B - f A| := le_abs_self _
      _ ≤ M := by linarith
  nlinarith

/-- A point of the affine span of `S` lies in the affine span of a finite part of `S`. -/
theorem exists_finset_of_mem_affineSpan {S : Set E} {x : E} (hx : x ∈ affineSpan ℝ S) :
    ∃ T : Finset E, (T : Set E) ⊆ S ∧ x ∈ affineSpan ℝ (T : Set E) := by
  rw [← Set.image_id S] at hx
  obtain ⟨fs, w, hfs, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan_image hx
  refine ⟨fs, hfs, ?_⟩
  have := affineCombination_mem_affineSpan_image (k := ℝ) hw (s' := (fs : Set E))
    (fun i hi hni => absurd hi hni) id
  simpa using this

/-- An affine subspace meets every line in a closed set of parameters (empty, a point or `ℝ`). -/
theorem fermeLineaire_affineSubspace (P : AffineSubspace ℝ E) : FermeLineaire (P : Set E) := by
  intro x v
  by_cases h : ∃ t₁ t₂ : ℝ, t₁ ≠ t₂ ∧ x + t₁ • v ∈ P ∧ x + t₂ • v ∈ P
  · obtain ⟨t₁, t₂, hne, h1, h2⟩ := h
    have hv : v ∈ P.direction := by
      have hd := AffineSubspace.vsub_mem_direction h2 h1
      have e : v = (t₂ - t₁)⁻¹ • ((x + t₂ • v) -ᵥ (x + t₁ • v)) := by
        rw [vsub_eq_sub]
        have : t₂ - t₁ ≠ 0 := sub_ne_zero.2 hne.symm
        rw [show x + t₂ • v - (x + t₁ • v) = (t₂ - t₁) • v by module, smul_smul,
          inv_mul_cancel₀ this, one_smul]
      rw [e]; exact P.direction.smul_mem _ hd
    have : {t : ℝ | x + t • v ∈ (P : Set E)} = univ := by
      ext t
      simp only [mem_setOf_eq, mem_univ, iff_true, SetLike.mem_coe]
      have hm := AffineSubspace.vadd_mem_of_mem_direction (P.direction.smul_mem (t - t₁) hv) h1
      rw [vadd_eq_add] at hm
      convert hm using 1
      module
    rw [this]; exact isClosed_univ
  · push Not at h
    refine Set.Subsingleton.isClosed ?_
    intro t₁ h1 t₂ h2
    by_contra hne
    exact h t₁ t₂ hne h1 h2
/-- The contact set as the proof of Prop. 7 describes it (l.1265): the points `A` of `V` for
which some `B ∈ W` has `)A, B( ⊆ ∁V`. It lies in Benzécri's `ensembleContact (W − V) V` of
Déf. 2 (`pointsContact_subset_ensembleContact`). -/
def pointsContact (V W : Set E) : Set E :=
  {A | A ∈ V ∧ ∃ B ∈ W, openSegment ℝ A B ⊆ Vᶜ}
/-- **« un hyperplan $H$ séparant $V$ de $U$ »**, relative to the support `L`: `H` is a
hyperplane of `L`, `H = L ∩ {f = c}` for a linear form `f` not constantly equal to `c` on `L`,
and `V`, `U` lie in the two opposite closed half-spaces `{f ≤ c}`, `{c ≤ f}` (the other
orientation is `(−f, −c)`). No continuity of `f` is asked: for the finest locally convex
topology every linear form is continuous (`continuous_linearMap_finestLC`). -/
def SepareHyperplan (L V U H : Set E) : Prop :=
  ∃ f : E →ₗ[ℝ] ℝ, ∃ c : ℝ, H = L ∩ {x | f x = c} ∧ (∃ x ∈ L, f x ≠ c) ∧
    (∀ v ∈ V, f v ≤ c) ∧ ∀ u ∈ U, c ≤ f u

variable {V W : Set E}

/-- **Strictness** (l.1283–1286 in the finite case, l.1307–1317 in general). A hyperplane
weakly separating `V` from `W − V`, `V` closed on lines and not contained in it, has `W − V` in
its OPEN half-space. -/
theorem lt_of_separe (hW : Convex ℝ W) (hV : FermeLineaire V) (hVW : V ⊆ W)
    {f : E →ₗ[ℝ] ℝ} {c : ℝ} (hnc : ∃ x ∈ affineSpan ℝ V, f x ≠ c) (hVc : ∀ v ∈ V, f v ≤ c)
    (hUc : ∀ u ∈ W \ V, c ≤ f u) : ∀ u ∈ W \ V, c < f u := by
  obtain ⟨C, hCV, hC⟩ : ∃ C ∈ V, f C < c := by
    by_contra h
    push Not at h
    obtain ⟨x, hx, hfx⟩ := hnc
    exact hfx (linear_eq_of_mem_affineSpan f (fun y hy => le_antisymm (hVc y hy) (h y hy)) hx)
  intro u hu
  refine lt_of_le_of_ne (hUc u hu) fun hcu => hu.2 ?_
  have hsub : Ioc (0 : ℝ) 1 ⊆ {t : ℝ | u + t • (C - u) ∈ V} := by
    rintro t ⟨ht0, ht1⟩
    have hmem : u + t • (C - u) ∈ W := hW.add_smul_sub_mem hu.1 (hVW hCV) ⟨ht0.le, ht1⟩
    by_contra hnV
    have := hUc _ ⟨hmem, hnV⟩
    simp only [map_add, map_smul, map_sub, smul_eq_mul] at this
    nlinarith
  have h0 : (0 : ℝ) ∈ closure (Ioc (0 : ℝ) 1) := by
    rw [closure_Ioc (by norm_num : (0 : ℝ) ≠ 1)]; exact ⟨le_rfl, zero_le_one⟩
  have := (hV u (C - u)).closure_subset_iff.2 hsub h0
  simpa using this

/-- **The crossing point.** On the segment from `u ∈ W − V` to `v ∈ V`, the first point of `V`
is a contact point. -/
theorem exists_pointsContact (hV : FermeLineaire V)
    {u v : E} (hu : u ∈ W \ V) (hv : v ∈ V) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ u + t • (v - u) ∈ pointsContact V W := by
  set S : Set ℝ := {t : ℝ | u + t • (v - u) ∈ V} ∩ Icc 0 1 with hS
  have hSc : IsClosed S := (hV u (v - u)).inter isClosed_Icc
  have h1 : (1 : ℝ) ∈ S := ⟨by simpa using hv, ⟨zero_le_one, le_rfl⟩⟩
  have hbdd : BddBelow S := ⟨0, fun t ht => ht.2.1⟩
  have hmem := hSc.csInf_mem ⟨1, h1⟩ hbdd
  set t := sInf S with ht
  have ht0 : t ≠ 0 := by
    intro h
    have := hmem.1
    rw [h] at this
    exact hu.2 (by simpa using this)
  refine ⟨t, lt_of_le_of_ne hmem.2.1 (Ne.symm ht0), csInf_le hbdd h1, hmem.1, u, hu.1, ?_⟩
  rintro y ⟨a, b, ha, hb, hab, rfl⟩ hy
  have hyt : a • (u + t • (v - u)) + b • u = u + (a * t) • (v - u) := by
    obtain rfl : b = 1 - a := by linarith
    module
  have hlt : a * t < t := by
    have : 0 < t := lt_of_le_of_ne hmem.2.1 (Ne.symm ht0)
    nlinarith
  have hin : a * t ∈ S := by
    refine ⟨by rw [mem_setOf_eq, ← hyt]; exact hy, ?_, ?_⟩
    · exact mul_nonneg ha.le hmem.2.1
    · nlinarith [hmem.2.2]
  exact absurd (csInf_le hbdd hin) (not_le.2 hlt)

/-- A weakly separating hyperplane contains every contact point (« si un hyperplan $H$ sépare
$V$ de $W-V$, on doit avoir $F\subset H$ », l.1266). -/
theorem eq_of_mem_pointsContact (hW : Convex ℝ W) (hVW : V ⊆ W) {f : E →ₗ[ℝ] ℝ} {c : ℝ}
    (hVc : ∀ v ∈ V, f v ≤ c) (hUc : ∀ u ∈ W \ V, c ≤ f u) {A : E}
    (hA : A ∈ pointsContact V W) : f A = c := by
  obtain ⟨hAV, B, hB, hseg⟩ := hA
  refine le_antisymm (hVc A hAV) (le_of_forall_openSegment f (B := B) fun t ht0 ht1 => ?_)
  have hmem : (1 - t) • A + t • B ∈ openSegment ℝ A B :=
    ⟨1 - t, t, by linarith, ht0, by ring, rfl⟩
  exact hUc _ ⟨hW.openSegment_subset (hVW hAV) hB hmem, hseg hmem⟩

/-- **The support of `V` is spanned by the contact set and one point `u₀` of `W − V`**
(« la codimension de $H$ est au plus 1 »): every `x ∈ L` is `r • (u₀ − p₁) + p₀` with
`p₀ ∈ affineSpan F`, for any `p₁ ∈ affineSpan F`. -/
theorem mem_affineSpan_insert_pointsContact (hV : FermeLineaire V)
    {u₀ : E} (hu₀ : u₀ ∈ W \ V) {p₁ : E}
    (hp₁ : p₁ ∈ affineSpan ℝ (pointsContact V W)) {x : E} (hx : x ∈ affineSpan ℝ V) :
    ∃ r : ℝ, ∃ p₀ ∈ affineSpan ℝ (pointsContact V W), x = r • (u₀ - p₁) + p₀ := by
  have hle : affineSpan ℝ V ≤
      affineSpan ℝ (insert u₀ (affineSpan ℝ (pointsContact V W) : Set E)) := by
    rw [affineSpan_le]
    intro v hv
    obtain ⟨t, ht0, -, ha⟩ := exists_pointsContact hV hu₀ hv
    have hl : v ∈ line[ℝ, u₀, u₀ + t • (v - u₀)] := by
      refine mem_line_of_eq (1 / t) ?_
      have e : (1 / t) * t = 1 := by field_simp
      calc v = u₀ + ((1 / t) * t) • (v - u₀) := by rw [e, one_smul]; abel
        _ = (1 - 1 / t) • u₀ + (1 / t) • (u₀ + t • (v - u₀)) := by module
    refine affineSpan_mono ℝ (pair_subset (mem_insert _ _) (mem_insert_of_mem _ ?_)) hl
    exact subset_affineSpan ℝ _ ha
  obtain ⟨r, p₀, hp₀, hx'⟩ := (AffineSubspace.mem_affineSpan_insert_iff hp₁ u₀ x).1 (hle hx)
  exact ⟨r, p₀, hp₀, by rw [hx', vadd_eq_add, vsub_eq_sub]⟩

/-- **Uniqueness, one inclusion**: of two hyperplanes separating `V` from `W − V ≠ ∅`, the
first is contained in the second. -/
theorem separeHyperplan_subset (hW : Convex ℝ W) (hV : FermeLineaire V) (hVW : V ⊆ W)
    (hU : (W \ V).Nonempty) {H H' : Set E}
    (hH : SepareHyperplan (affineSpan ℝ V : Set E) V (W \ V) H)
    (hH' : SepareHyperplan (affineSpan ℝ V : Set E) V (W \ V) H') : H ⊆ H' := by
  obtain ⟨f, c, rfl, hnc, hVc, hUc⟩ := hH
  obtain ⟨g, d, rfl, -, hVd, hUd⟩ := hH'
  obtain ⟨u₀, hu₀⟩ := hU
  obtain ⟨v₀, hv₀⟩ : V.Nonempty := by
    obtain ⟨x, hx, -⟩ := hnc
    exact (affineSpan_nonempty (k := ℝ)).1 ⟨x, hx⟩
  obtain ⟨t, -, -, hp⟩ := exists_pointsContact hV hu₀ hv₀
  have hp₁ := subset_affineSpan ℝ _ hp
  generalize u₀ + t • (v₀ - u₀) = p₁ at hp₁
  have hlt := lt_of_separe hW hV hVW hnc hVc hUc u₀ hu₀
  rintro x ⟨hxL, hfx⟩
  obtain ⟨r, p₀, hp₀, rfl⟩ := mem_affineSpan_insert_pointsContact hV hu₀ hp₁ hxL
  have hf₀ := linear_eq_of_mem_affineSpan f (fun y hy => eq_of_mem_pointsContact hW hVW hVc hUc hy) hp₀
  have hf₁ := linear_eq_of_mem_affineSpan f (fun y hy => eq_of_mem_pointsContact hW hVW hVc hUc hy) hp₁
  simp only [mem_setOf_eq, map_add, map_smul, map_sub, smul_eq_mul] at hfx
  have hr : r = 0 := by
    have : r * (f u₀ - c) = 0 := by rw [hf₀, hf₁] at hfx; linarith
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · linarith
  subst hr
  rw [zero_smul, zero_add]
  exact ⟨by rwa [zero_smul, zero_add] at hxL,
    linear_eq_of_mem_affineSpan g (fun y hy => eq_of_mem_pointsContact hW hVW hVd hUd hy) hp₀⟩
/-- **The finite-dimensional case**, by Mathlib's geometric Hahn–Banach
(`geometric_hahn_banach_of_nonempty_interior`): in the affine span `P` of finitely many points of
`V`, if `P` meets `W − V`, some hyperplane of `P` weakly separates `V ∩ P` from `(W − V) ∩ P`.
The slice `P` is carried to `Fin n → ℝ`, where `W − V` has non-empty interior by Prop. 5
(`prop5_fort`). -/
theorem exists_separe_finset (hW : Convex ℝ W) (hVc : Convex ℝ V) (hUc : Convex ℝ (W \ V))
    (hV : FermeLineaire V) (hVW : V ⊆ W) (T : Finset E) (hT : (T : Set E) ⊆ V)
    (hu : ((W \ V) ∩ affineSpan ℝ (T : Set E)).Nonempty) :
    ∃ f : E →ₗ[ℝ] ℝ, ∃ c : ℝ, (∃ x ∈ affineSpan ℝ (T : Set E), f x ≠ c) ∧
      (∀ v ∈ V ∩ affineSpan ℝ (T : Set E), f v ≤ c) ∧
      ∀ u ∈ (W \ V) ∩ affineSpan ℝ (T : Set E), c ≤ f u := by
  classical
  set P := affineSpan ℝ (T : Set E) with hP
  obtain ⟨u, huU, huP⟩ := hu
  obtain ⟨O, hOT⟩ : (T : Set E).Nonempty := (affineSpan_nonempty (k := ℝ)).1 ⟨u, huP⟩
  have hOP : O ∈ P := subset_affineSpan ℝ _ hOT
  set D := P.direction with hD
  haveI : FiniteDimensional ℝ D :=
    finiteDimensional_direction_affineSpan_of_finite ℝ T.finite_toSet
  set n := Module.finrank ℝ D
  let e : D ≃ₗ[ℝ] (Fin n → ℝ) := (Module.finBasis ℝ D).equivFun
  let φL : (Fin n → ℝ) →ₗ[ℝ] E := D.subtype ∘ₗ e.symm.toLinearMap
  let φ : (Fin n → ℝ) →ᵃ[ℝ] E :=
    ⟨fun y => φL y + O, φL, fun p v => by simp only [vadd_eq_add, map_add]; abel⟩
  have hφ : ∀ y, φ y = φL y + O := fun y => rfl
  have hφinj : Function.Injective φ := by
    intro y y' h
    rw [hφ, hφ, add_left_inj] at h
    exact e.symm.injective (Subtype.val_injective h)
  have hφP : ∀ y, φ y ∈ P := fun y => by
    rw [hφ, ← vadd_eq_add]
    exact AffineSubspace.vadd_mem_of_mem_direction (e.symm y).2 hOP
  have hPφ : ∀ x ∈ P, ∃ y, φ y = x := fun x hx =>
    ⟨e ⟨x - O, AffineSubspace.vsub_mem_direction hx hOP⟩, by simp [hφ, φL]⟩
  set Vg : Set (Fin n → ℝ) := φ ⁻¹' V with hVg_def
  set Wg : Set (Fin n → ℝ) := φ ⁻¹' W with hWg_def
  have hVg : Convex ℝ Vg := hVc.affine_preimage φ
  have hWg : Convex ℝ Wg := hW.affine_preimage φ
  have hUg : Convex ℝ (Wg \ Vg) := hUc.affine_preimage φ
  have hFg : FermeLineaire Vg := fun y w => by
    have : {t : ℝ | y + t • w ∈ Vg} = {t | φ y + t • φL w ∈ V} := by
      ext t
      simp only [hVg_def, mem_preimage, mem_setOf_eq, hφ, map_add, map_smul]
      rw [add_right_comm]
    rw [this]; exact hV _ _
  have hspan : affineSpan ℝ Vg = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    have hm : φ y ∈ (affineSpan ℝ (φ ⁻¹' (T : Set E))).map φ := by
      rw [AffineSubspace.map_span, image_preimage_eq_of_subset]
      · exact hφP y
      · intro x hx
        obtain ⟨y', hy'⟩ := hPφ x (subset_affineSpan ℝ _ hx)
        exact ⟨y', hy'⟩
    obtain ⟨y', hy', hyy⟩ := AffineSubspace.mem_map.1 hm
    rw [← hφinj hyy]
    exact affineSpan_mono ℝ (preimage_mono hT) hy'
  obtain ⟨yu, hyu⟩ := hPφ u huP
  have hUne : (Wg \ Vg).Nonempty := ⟨yu, by
    show φ yu ∈ W ∧ φ yu ∉ V
    rw [hyu]; exact huU⟩
  have hUspan : affineSpan ℝ (Wg \ Vg) = ⊤ := by
    rcases prop5_fort hWg hFg (preimage_mono hVW) with h | h
    · exfalso
      obtain ⟨y, hy1, hy2⟩ := hUne
      rw [← h] at hy1
      exact hy2 hy1
    · rw [h]
      exact eq_top_iff.2 (hspan ▸ affineSpan_mono ℝ (preimage_mono hVW))
  have hint : (interior (Wg \ Vg)).Nonempty :=
    hUg.interior_nonempty_iff_affineSpan_eq_top.2 hUspan
  have hdisj : Disjoint (interior (Wg \ Vg)) Vg :=
    Set.disjoint_left.2 fun y hy hyV => (interior_subset hy).2 hyV
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, φ y₀ = O := hPφ O hOP
  have hVne : Vg.Nonempty := ⟨y₀, show φ y₀ ∈ V by rw [hy₀]; exact hT hOT⟩
  obtain ⟨F0, u0, hF0, hFU, hFV⟩ :=
    geometric_hahn_banach_of_nonempty_interior hUg hVg hdisj hint hVne
  let fD : D →ₗ[ℝ] ℝ := (-(F0 : (Fin n → ℝ) →ₗ[ℝ] ℝ)) ∘ₗ e.toLinearMap
  obtain ⟨g, hg⟩ := LinearMap.exists_extend fD
  have hgφ : ∀ y, g (φ y) = g O - F0 y := by
    intro y
    have := LinearMap.congr_fun hg (e.symm y)
    simp only [fD, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.neg_apply,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, ContinuousLinearMap.coe_coe] at this
    rw [hφ, map_add]
    simp only [φL, LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe, this]
    ring
  refine ⟨g, g O - u0, ?_, ?_, ?_⟩
  · obtain ⟨y, hy⟩ : ∃ y, F0 y ≠ 0 := by
      by_contra h
      push Not at h
      exact hF0 (ContinuousLinearMap.ext h)
    by_cases hu0 : u0 = 0
    · refine ⟨φ y, hφP y, ?_⟩
      rw [hgφ, hu0]
      intro h; apply hy; linarith
    · refine ⟨φ 0, hφP 0, ?_⟩
      rw [hgφ, map_zero]
      intro h; apply hu0; linarith
  · rintro v ⟨hv, hvP⟩
    obtain ⟨y, rfl⟩ := hPφ v hvP
    rw [hgφ]
    linarith [hFV y hv]
  · rintro w ⟨hw, hwP⟩
    obtain ⟨y, rfl⟩ := hPφ w hwP
    rw [hgφ]
    linarith [hFU y hw]

/-- **No point of `W − V` lies in the support of the contact set** (the paragraph
l.1307–1317: a point `B ∈ U ∩ H` lies in a finite-dimensional slice spanned by points of `V`,
where the hyperplane of the finite case contains the `A_i` but not `B`). -/
theorem not_mem_affineSpan_pointsContact (hW : Convex ℝ W) (hVc : Convex ℝ V)
    (hUc : Convex ℝ (W \ V)) (hV : FermeLineaire V) (hVW : V ⊆ W)
    (hWL : W ⊆ affineSpan ℝ V) {u : E} (hu : u ∈ W \ V) :
    u ∉ affineSpan ℝ (pointsContact V W) := by
  classical
  intro huF
  obtain ⟨C0, hC0, huC0⟩ := exists_finset_of_mem_affineSpan huF
  have hwit : ∀ A ∈ C0, ∃ B ∈ W, openSegment ℝ A B ⊆ Vᶜ := fun A hA => (hC0 hA).2
  choose! Bf hBfW hBf using hwit
  let M : E → E := fun A => (1 / 2 : ℝ) • A + (1 / 2 : ℝ) • Bf A
  let Q : Finset E := insert u (C0 ∪ C0.image M)
  have hQL : ∀ q ∈ Q, q ∈ affineSpan ℝ V := by
    intro q hq
    simp only [Q, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hq
    rcases hq with rfl | hq | ⟨a, ha, rfl⟩
    · exact hWL hu.1
    · exact subset_affineSpan ℝ _ (hC0 hq).1
    · exact hWL (hW (hVW (hC0 ha).1) (hBfW a ha) (by norm_num) (by norm_num) (by norm_num))
  have hfin : ∀ q ∈ Q, ∃ T : Finset E, (T : Set E) ⊆ V ∧ q ∈ affineSpan ℝ (T : Set E) :=
    fun q hq => exists_finset_of_mem_affineSpan (hQL q hq)
  choose! Tf hTfV hTf using hfin
  let T : Finset E := Q.biUnion Tf
  have hTV : (T : Set E) ⊆ V := by
    intro x hx
    simp only [T, Finset.coe_biUnion, mem_iUnion, Finset.mem_coe, exists_prop] at hx
    obtain ⟨q, hq, hx⟩ := hx
    exact hTfV q hq hx
  have hQP : ∀ q ∈ Q, q ∈ affineSpan ℝ (T : Set E) := fun q hq =>
    affineSpan_mono ℝ (fun x hx => by
      simp only [T, Finset.coe_biUnion, mem_iUnion, Finset.mem_coe, exists_prop]
      exact ⟨q, hq, hx⟩) (hTf q hq)
  set P := affineSpan ℝ (T : Set E) with hP
  have huP : u ∈ P := hQP u (Finset.mem_insert_self _ _)
  obtain ⟨f, c, hnc, hfV, hfU⟩ := exists_separe_finset hW hVc hUc hV hVW T hTV ⟨u, hu, huP⟩
  have hPle : P ≤ affineSpan ℝ (V ∩ P) :=
    affineSpan_le.2 fun x hx => subset_affineSpan ℝ _ ⟨hTV hx, subset_affineSpan ℝ _ hx⟩
  have hlt := lt_of_separe (V := V ∩ P) (W := W ∩ P) (hW.inter P.convex)
    (fun x v => (hV x v).inter (fermeLineaire_affineSubspace P x v)) (inter_subset_inter_left _ hVW) (f := f) (c := c)
    (let ⟨x, hx, hfx⟩ := hnc; ⟨x, hPle hx, hfx⟩) hfV
    (fun y hy => hfU y ⟨⟨hy.1.1, fun hv => hy.2 ⟨hv, hy.1.2⟩⟩, hy.1.2⟩)
  have hA : ∀ A ∈ (C0 : Set E), f A = c := by
    intro A hA
    have hAQ : A ∈ Q := Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_coe.1 hA))
    have hMQ : M A ∈ Q := by
      simp only [Q, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
      exact Or.inr (Or.inr ⟨A, hA, rfl⟩)
    refine le_antisymm (hfV A ⟨(hC0 hA).1, hQP A hAQ⟩)
      (le_of_forall_openSegment f (B := M A) fun t ht0 ht1 => ?_)
    apply hfU
    have hseg : (1 - t) • A + t • M A ∈ openSegment ℝ A (Bf A) :=
      ⟨1 - t / 2, t / 2, by linarith, by linarith, by ring, by simp only [M]; module⟩
    refine ⟨⟨hW.openSegment_subset (hVW (hC0 hA).1) (hBfW A hA) hseg, hBf A hA hseg⟩, ?_⟩
    exact P.convex (hQP A hAQ) (hQP _ hMQ) (by linarith) ht0.le (by ring)
  have := linear_eq_of_mem_affineSpan f hA huC0
  linarith [hlt u ⟨⟨hu.1, huP⟩, fun h => hu.2 h.1⟩]

/-- **Existence, strong form** (everything the printed proof asserts): a hyperplane
`H = L ∩ {f = c}` of the support `L` with `V ⊆ {f ≤ c}`, `W − V` in the OPEN half-space
`{c < f}`, `H` the support of the contact set `F`, and `H ∩ W = F`. -/
theorem exists_separe_fort (hW : Convex ℝ W) (hVc : Convex ℝ V) (hUc : Convex ℝ (W \ V))
    (hV : FermeLineaire V) (hVW : V ⊆ W) (hWL : W ⊆ affineSpan ℝ V) (hU : (W \ V).Nonempty) :
    ∃ f : E →ₗ[ℝ] ℝ, ∃ c : ℝ, (∃ x ∈ affineSpan ℝ V, f x ≠ c) ∧ (∀ v ∈ V, f v ≤ c) ∧
      (∀ u ∈ W \ V, c < f u) ∧
      (affineSpan ℝ V : Set E) ∩ {x | f x = c} = affineSpan ℝ (pointsContact V W) ∧
      (affineSpan ℝ V : Set E) ∩ {x | f x = c} ∩ W = pointsContact V W := by
  obtain ⟨u₀, hu₀⟩ := hU
  obtain ⟨v₀, hv₀⟩ : V.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    have := hWL hu₀.1
    rw [h, AffineSubspace.span_empty] at this
    exact AffineSubspace.notMem_bot ℝ _ _ this
  obtain ⟨t, -, -, hp⟩ := exists_pointsContact hV hu₀ hv₀
  set S := affineSpan ℝ (pointsContact V W) with hS
  have hp₁ : u₀ + t • (v₀ - u₀) ∈ S := subset_affineSpan ℝ _ hp
  generalize u₀ + t • (v₀ - u₀) = p₁ at hp₁
  have hnot : ∀ u ∈ W \ V, u ∉ S := fun u hu =>
    not_mem_affineSpan_pointsContact hW hVc hUc hV hVW hWL hu
  have hx0 : u₀ - p₁ ∉ S.direction := by
    intro h
    apply hnot _ hu₀
    have := AffineSubspace.vadd_mem_of_mem_direction h hp₁
    rwa [vadd_eq_add, sub_add_cancel] at this
  obtain ⟨f0, hf0x, hf0S⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx0 inferInstance
  set f : E →ₗ[ℝ] ℝ := (f0 (u₀ - p₁))⁻¹ • f0 with hf
  have hfx : f (u₀ - p₁) = 1 := by
    simp only [hf, LinearMap.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ hf0x
  have hfS : ∀ y ∈ S, f y = f p₁ := by
    intro y hy
    have hd : y - p₁ ∈ S.direction := AffineSubspace.vsub_mem_direction hy hp₁
    have h0 : f0 (y - p₁) = 0 := by
      have : f0 (y - p₁) ∈ S.direction.map f0 := Submodule.mem_map_of_mem hd
      rw [hf0S] at this
      simpa using this
    have : f (y - p₁) = 0 := by simp only [hf, LinearMap.smul_apply, h0, smul_zero]
    rw [map_sub] at this
    linarith
  set c := f p₁ with hc
  have hdec : ∀ x ∈ affineSpan ℝ V, f x = c → x ∈ S := by
    intro x hx hfx'
    obtain ⟨r, p₀, hp₀, rfl⟩ := mem_affineSpan_insert_pointsContact hV hu₀ hp₁ hx
    rw [map_add, map_smul, hfx, hfS p₀ hp₀, smul_eq_mul, mul_one] at hfx'
    have : r = 0 := by linarith
    subst this
    simpa using hp₀
  have hfu₀ : f u₀ = c + 1 := by
    have := hfx
    rw [map_sub] at this
    linarith
  have hU' : ∀ u ∈ W \ V, c < f u := by
    intro u hu
    by_contra hle
    push Not at hle
    have hden : 0 < f u₀ - f u := by linarith
    set l := (f u₀ - c) / (f u₀ - f u) with hl
    have hl0 : 0 ≤ l := div_nonneg (by linarith) hden.le
    have hl1 : l ≤ 1 := (div_le_one hden).2 (by linarith)
    have hu' := hUc.add_smul_sub_mem hu₀ hu ⟨hl0, hl1⟩
    have hfu' : f (u₀ + l • (u - u₀)) = c := by
      rw [map_add, map_smul, map_sub, smul_eq_mul, hl]
      field_simp
      ring
    exact hnot _ hu' (hdec _ (hWL hu'.1) hfu')
  have hV' : ∀ v ∈ V, f v ≤ c := by
    intro v hv
    by_contra hlt
    push Not at hlt
    obtain ⟨t, ht0, ht1, ha⟩ := exists_pointsContact hV hu₀ hv
    have := hfS _ (subset_affineSpan ℝ _ ha)
    rw [map_add, map_smul, map_sub, smul_eq_mul, hfu₀] at this
    nlinarith
  refine ⟨f, c, ⟨u₀, hWL hu₀.1, by linarith⟩, hV', hU', ?_, ?_⟩
  · ext x
    refine ⟨fun hx => hdec x hx.1 hx.2, fun hx => ⟨?_, hfS x hx⟩⟩
    exact affineSpan_mono ℝ (fun y hy => hy.1) hx
  ext x
  constructor
  · rintro ⟨⟨-, hfx'⟩, hxW⟩
    have hfx'' : f x = c := hfx'
    have hxV : x ∈ V := by
      by_contra h
      have := hU' x ⟨hxW, h⟩
      linarith
    refine ⟨hxV, u₀, hu₀.1, ?_⟩
    rintro y ⟨a, b, ha, hb, hab, rfl⟩ hyV
    have := hV' _ hyV
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hfx'', hfu₀] at this
    have hac : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
    linarith
  · intro hx
    exact ⟨⟨subset_affineSpan ℝ _ hx.1,
      eq_of_mem_pointsContact hW hVW hV' (fun u hu => (hU' u hu).le) hx⟩, hVW hx.1⟩

/-- **Uniqueness**: two hyperplanes separating `V` from `W − V ≠ ∅` coincide. -/
theorem separeHyperplan_unique (hW : Convex ℝ W) (hV : FermeLineaire V) (hVW : V ⊆ W)
    (hU : (W \ V).Nonempty) {H H' : Set E}
    (hH : SepareHyperplan (affineSpan ℝ V : Set E) V (W \ V) H)
    (hH' : SepareHyperplan (affineSpan ℝ V : Set E) V (W \ V) H') : H = H' :=
  (separeHyperplan_subset hW hV hVW hU hH hH').antisymm
    (separeHyperplan_subset hW hV hVW hU hH' hH)

/-! ### Prop. 7 -/

/-- **Ch. 3 § 5, Prop. 7**, « V fermé » read as `FermeLineaire V` (every line meets `V` in a
closed set; implied by closedness for every topology in which lines are continuous): there is
exactly one hyperplane of the support `L` separating `V` from `U = W − V`. -/
theorem hyperplan_separant {V W : Set E} (hW : Convex ℝ W) (_hne : V.Nonempty)
    (hL : affineSpan ℝ V = affineSpan ℝ W) (hV : FermeLineaire V) (hVW : V ≠ W)
    (hI : ProprieteI V W) :
    ∃! H : Set E, SepareHyperplan (affineSpan ℝ V : Set E) V (W \ V) H := by
  obtain ⟨hsub, hVc, hUc⟩ := hI
  have hWL : W ⊆ affineSpan ℝ V := hL ▸ subset_affineSpan ℝ W
  have hU : (W \ V).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty, sdiff_eq_empty] at h
    exact hVW (hsub.antisymm h)
  obtain ⟨f, c, hnc, hfV, hfU, -, -⟩ := exists_separe_fort hW hVc hUc hV hsub hWL hU
  refine ⟨(affineSpan ℝ V : Set E) ∩ {x | f x = c},
    ⟨f, c, rfl, hnc, hfV, fun u hu => (hfU u hu).le⟩, fun H hH => ?_⟩
  exact separeHyperplan_unique hW hV hsub hU hH ⟨f, c, rfl, hnc, hfV, fun u hu => (hfU u hu).le⟩

/-- The proof's contact set lies in Benzécri's contact set of `W − V` and `V` (Déf. 2). -/
theorem pointsContact_subset_ensembleContact (hW : Convex ℝ W) (hVW : V ⊆ W) :
    pointsContact V W ⊆ ensembleContact (W \ V) V := by
  rintro A ⟨hAV, B, hB, hseg⟩
  refine ⟨B, A, ?_, ?_, ?_⟩
  · rw [pair_eq_singleton]; exact collinear_pair ℝ B A
  · rw [openSegment_symm]
    exact fun y hy => ⟨hW.openSegment_subset (hVW hAV) hB hy, hseg hy⟩
  · rw [openSegment_same]; exact singleton_subset_iff.2 hAV

/-- « $V$ fermé » in `L` with its finest locally convex topology (that of its direction, origin
`P ∈ L`) implies `FermeLineaire V`. -/
theorem fermeLineaire_of_isClosed_support {P : E} (hP : P ∈ affineSpan ℝ V)
    (hV : IsClosed[finestLC (affineSpan ℝ V).direction]
      {v : (affineSpan ℝ V).direction | (v : E) + P ∈ V}) : FermeLineaire V := by
  intro x w
  by_cases h : ∃ t₁ t₂ : ℝ, t₁ ≠ t₂ ∧ x + t₁ • w ∈ V ∧ x + t₂ • w ∈ V
  · obtain ⟨t₁, t₂, hne, h1, h2⟩ := h
    set D := (affineSpan ℝ V).direction with hD
    have h1L := subset_affineSpan ℝ V h1
    have h2L := subset_affineSpan ℝ V h2
    have hw : w ∈ D := by
      have hd := AffineSubspace.vsub_mem_direction h2L h1L
      have e : w = (t₂ - t₁)⁻¹ • ((x + t₂ • w) -ᵥ (x + t₁ • w)) := by
        rw [vsub_eq_sub]
        have : t₂ - t₁ ≠ 0 := sub_ne_zero.2 hne.symm
        rw [show x + t₂ • w - (x + t₁ • w) = (t₂ - t₁) • w by module, smul_smul,
          inv_mul_cancel₀ this, one_smul]
      rw [e]; exact D.smul_mem _ hd
    have hx : x - P ∈ D := by
      have := AffineSubspace.vsub_mem_direction h1L hP
      rw [vsub_eq_sub] at this
      have e : x - P = (x + t₁ • w - P) - t₁ • w := by abel
      rw [e]; exact D.sub_mem this (D.smul_mem _ hw)
    letI := finestLC D
    haveI := isTopologicalAddGroup_finestLC D
    haveI := continuousSMul_finestLC D
    have hc : Continuous fun t : ℝ => (⟨x - P, hx⟩ : D) + t • (⟨w, hw⟩ : D) := by fun_prop
    have := hV.preimage hc
    convert this using 1
    ext t
    simp only [mem_setOf_eq, mem_preimage, Submodule.coe_add, Submodule.coe_smul]
    rw [show x - P + t • w + P = x + t • w by abel]
  · push Not at h
    refine Set.Subsingleton.isClosed ?_
    intro t₁ h1 t₂ h2
    by_contra hne
    exact h t₁ t₂ hne h1 h2

/-- **Ch. 3 § 5, Prop. 7, as printed**: `L = affineSpan V = affineSpan W` with the finest
locally convex topology (of its direction, origin `P ∈ L`), `V` closed in `L`, `V ≠ W`,
`I(V, W)`: there is exactly one hyperplane of `L` separating `V` from `W − V`. -/
theorem hyperplan_separant_support {P : E} (hW : Convex ℝ W) (hne : V.Nonempty)
    (hL : affineSpan ℝ V = affineSpan ℝ W) (hP : P ∈ affineSpan ℝ V)
    (hV : IsClosed[finestLC (affineSpan ℝ V).direction]
      {v : (affineSpan ℝ V).direction | (v : E) + P ∈ V}) (hVW : V ≠ W)
    (hI : ProprieteI V W) :
    ∃! H : Set E, SepareHyperplan (affineSpan ℝ V : Set E) V (W \ V) H :=
  hyperplan_separant hW hne hL (fermeLineaire_of_isClosed_support hP hV) hVW hI

/-- **Prop. 7**, `V` closed for the finest locally convex topology of the ambient space. -/
theorem hyperplan_separant_finestLC (hW : Convex ℝ W) (hne : V.Nonempty)
    (hL : affineSpan ℝ V = affineSpan ℝ W) (hV : IsClosed[finestLC E] V) (hVW : V ≠ W)
    (hI : ProprieteI V W) :
    ∃! H : Set E, SepareHyperplan (affineSpan ℝ V : Set E) V (W \ V) H := by
  letI := finestLC E
  haveI := isTopologicalAddGroup_finestLC E
  haveI := continuousSMul_finestLC E
  exact hyperplan_separant hW hne hL (fermeLineaire_of_isClosed' hV) hVW hI


/-! ### Instance and readings -/

/-- The instance: `V = [0,1] × [0,1/2]`. -/
def rectangleBas : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) (1 / 2)

/-- The instance: `W = [0,1]²`. -/
def carreUnite : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1

/-- `[0,1] × [0,1/2]` spans the plane. -/
theorem affineSpan_rectangleBas : affineSpan ℝ rectangleBas = ⊤ := by
  refine ((convex_Icc 0 1).prod (convex_Icc 0 (1 / 2))).interior_nonempty_iff_affineSpan_eq_top.1
    ⟨(1 / 2, 1 / 4), ?_⟩
  rw [rectangleBas, interior_prod_eq, interior_Icc, interior_Icc]
  exact ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩

/-- `[0,1]²` spans the plane. -/
theorem affineSpan_carreUnite : affineSpan ℝ carreUnite = ⊤ :=
  eq_top_iff.2 (affineSpan_rectangleBas ▸ affineSpan_mono ℝ
    (prod_mono subset_rfl (Icc_subset_Icc le_rfl (by norm_num))))

/-- `W − V = [0,1] × ]1/2, 1]`. -/
theorem carreUnite_diff_rectangleBas :
    carreUnite \ rectangleBas = Icc (0 : ℝ) 1 ×ˢ Ioc (1 / 2 : ℝ) 1 := by
  ext ⟨x, y⟩
  simp only [carreUnite, rectangleBas, Set.mem_sdiff, mem_prod, mem_Icc, mem_Ioc]
  constructor
  · rintro ⟨⟨hx, hy0, hy1⟩, h⟩
    refine ⟨hx, lt_of_not_ge fun h' => h ⟨hx, hy0, h'⟩, hy1⟩
  · rintro ⟨hx, hy0, hy1⟩
    exact ⟨⟨hx, by linarith, hy1⟩, fun h => by linarith [h.2.2]⟩

/-- `I(V, W)` for the instance. -/
theorem proprieteI_rectangleBas : ProprieteI rectangleBas carreUnite := by
  refine ⟨prod_mono subset_rfl (Icc_subset_Icc le_rfl (by norm_num)),
    (convex_Icc 0 1).prod (convex_Icc 0 (1 / 2)), ?_⟩
  rw [carreUnite_diff_rectangleBas]
  exact (convex_Icc 0 1).prod (convex_Ioc _ _)

/-- `V` is closed for the finest locally convex topology of `ℝ × ℝ`. -/
theorem isClosed_rectangleBas : IsClosed[finestLC (ℝ × ℝ)] rectangleBas := by
  rw [finestLC_prod]; exact isClosed_Icc.prod isClosed_Icc

/-- The line `y = 1/2` separates `V` from `W − V`. -/
theorem separeHyperplan_rectangleBas :
    SepareHyperplan (affineSpan ℝ rectangleBas : Set (ℝ × ℝ)) rectangleBas
      (carreUnite \ rectangleBas) {p | p.2 = 1 / 2} := by
  refine ⟨LinearMap.snd ℝ ℝ ℝ, 1 / 2, ?_, ⟨(0, 0), ?_, by norm_num⟩, ?_, ?_⟩
  · rw [affineSpan_rectangleBas, AffineSubspace.top_coe, univ_inter]; rfl
  · rw [affineSpan_rectangleBas]; exact AffineSubspace.mem_top ℝ _ _
  · rintro ⟨x, y⟩ ⟨-, -, hy⟩; exact hy
  · rw [carreUnite_diff_rectangleBas]
    rintro ⟨x, y⟩ ⟨-, hy, -⟩; exact hy.le

/-- **Prop. 7, instance**: `V = [0,1] × [0,1/2]` in `W = [0,1]²` satisfies every hypothesis
(`V` closed for `finestLC (ℝ × ℝ)`, the usual topology), and the unique separating hyperplane is
the line `y = 1/2`. -/
theorem hyperplan_separant_rectangleBas :
    (∃! H : Set (ℝ × ℝ), SepareHyperplan (affineSpan ℝ rectangleBas : Set (ℝ × ℝ))
      rectangleBas (carreUnite \ rectangleBas) H) ∧
    ∀ H : Set (ℝ × ℝ), SepareHyperplan (affineSpan ℝ rectangleBas : Set (ℝ × ℝ))
      rectangleBas (carreUnite \ rectangleBas) H → H = {p | p.2 = 1 / 2} := by
  have hne : rectangleBas.Nonempty := ⟨(0, 0), ⟨le_rfl, zero_le_one⟩, ⟨le_rfl, by norm_num⟩⟩
  have hVW : rectangleBas ≠ carreUnite := by
    intro h
    have : ((0 : ℝ), (1 : ℝ)) ∈ rectangleBas := by
      rw [h]; exact ⟨⟨le_rfl, zero_le_one⟩, ⟨zero_le_one, le_rfl⟩⟩
    linarith [this.2.2]
  have hex := hyperplan_separant_finestLC ((convex_Icc 0 1).prod (convex_Icc 0 1)) hne
    (affineSpan_rectangleBas.trans affineSpan_carreUnite.symm) isClosed_rectangleBas hVW
    proprieteI_rectangleBas
  refine ⟨hex, fun H hH => ?_⟩
  obtain ⟨H₀, -, huniq⟩ := hex
  rw [huniq H hH, huniq _ separeHyperplan_rectangleBas]

/-- The contact set is non-empty as soon as `V` and `W − V` are. -/
theorem pointsContact_nonempty (hV : FermeLineaire V) (hne : V.Nonempty)
    (hU : (W \ V).Nonempty) : (pointsContact V W).Nonempty := by
  obtain ⟨u, hu⟩ := hU
  obtain ⟨v, hv⟩ := hne
  obtain ⟨t, -, -, h⟩ := exists_pointsContact hV hu hv
  exact ⟨_, h⟩

/-- Every hyperplane separating `V` from `W − V` meets `V`: under a reading of « séparant » in
which `V` too lies in an open half-space, Prop. 7 would be false (no such hyperplane exists). -/
theorem inter_nonempty_of_separeHyperplan (hW : Convex ℝ W) (hV : FermeLineaire V)
    (hVW : V ⊆ W) (hne : V.Nonempty) (hU : (W \ V).Nonempty) {L H : Set E}
    (hLV : V ⊆ L) (hH : SepareHyperplan L V (W \ V) H) : (H ∩ V).Nonempty := by
  obtain ⟨f, c, rfl, -, hVc, hUc⟩ := hH
  obtain ⟨A, hA⟩ := pointsContact_nonempty hV hne hU
  exact ⟨A, ⟨hLV hA.1, eq_of_mem_pointsContact hW hVW hVc hUc hA⟩, hA.1⟩

/-- `[0,1] × [0,1/2] × {0}` in `ℝ³`, whose support is the plane `z = 0`. -/
def rectangleBas3 : Set (ℝ × ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) (1 / 2) ×ˢ {0}

/-- `[0,1]² × {0}` in `ℝ³`. -/
def carreUnite3 : Set (ℝ × ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 ×ˢ {0}

/-- **The reading « hyperplan de l'espace ambiant »** is not the paper's: when the support `L`
is not the whole space, two distinct hyperplanes of `ℝ³` (`y = 1/2` and `z = 0`) separate
`V = [0,1] × [0,1/2] × {0}` from `W − V`, `W = [0,1]² × {0}`. -/
theorem separeHyperplan_ambiant_deux :
    SepareHyperplan (univ : Set (ℝ × ℝ × ℝ)) rectangleBas3 (carreUnite3 \ rectangleBas3)
        {p | p.2.1 = 1 / 2} ∧
      SepareHyperplan (univ : Set (ℝ × ℝ × ℝ)) rectangleBas3 (carreUnite3 \ rectangleBas3)
        {p | p.2.2 = 0} ∧
      ({p | p.2.1 = 1 / 2} : Set (ℝ × ℝ × ℝ)) ≠ {p | p.2.2 = 0} := by
  refine ⟨⟨(LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ)), 1 / 2, by ext; simp,
    ⟨0, mem_univ _, by norm_num⟩, ?_, ?_⟩,
    ⟨(LinearMap.snd ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ)), 0, by ext; simp,
    ⟨(0, 0, 1), mem_univ _, by norm_num⟩, ?_, ?_⟩, ?_⟩
  · rintro ⟨x, y, z⟩ ⟨-, ⟨-, hy⟩, -⟩; exact hy
  · rintro ⟨x, y, z⟩ ⟨⟨hx, ⟨hy0, hy1⟩, hz⟩, h⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.snd_apply, LinearMap.fst_apply]
    by_contra hlt
    exact h ⟨hx, ⟨hy0, (not_le.1 hlt).le⟩, hz⟩
  · rintro ⟨x, y, z⟩ ⟨-, -, hz⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.snd_apply]
    exact (mem_singleton_iff.1 hz).le
  · rintro ⟨x, y, z⟩ ⟨⟨-, -, hz⟩, -⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.snd_apply]
    exact (mem_singleton_iff.1 hz).ge
  · intro h
    have : ((0 : ℝ), (1 / 2 : ℝ), (1 : ℝ)) ∈ ({p | p.2.2 = 0} : Set (ℝ × ℝ × ℝ)) := by
      rw [← h]; rfl
    norm_num at this
end Benzecri
