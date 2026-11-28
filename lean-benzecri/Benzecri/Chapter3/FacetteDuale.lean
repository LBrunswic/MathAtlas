import Benzecri.Chapter3.ConeAppuiAlpha
import Benzecri.Chapter3.AppuiSphere

/-!
# Chapter 3 § 4 — orthogonality propagates along α (Props. 4, 5; Déf. 4), the dual facette 𝒟(F) (Prop. 6) and its minimality (Prop. 7)

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 3 § 4, journal pp. 274–275; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch3.tex` (TO BE CHECKED BY THE AUTHOR, OQ-160).
Target T-bz-c3-facette-duale. On `S(n)` with the dot product (`dotPairing n`), `W` any convex part
(`IsConvexPart W`, `W ∈ K(S(n))`; never closed).

* **`bzprop:c3s4p4_orthogonalite_facettes`** — `benzecri1960_ch3.tex:998` (Prop. 4, l.998–1005;
  proof l.1007–1012) — `Benzecri.Sphere.prop4_orthogonalite`; the two halves of « par raison de
  symétrie »: `orthPts_of_alphaK_left`, `orthPts_of_alphaK_right`.
* **`bzdef:c3s4d4_orthogonalite_facettes`** — `benzecri1960_ch3.tex:1020` (Déf. 4, l.1020–1026)
  — `Benzecri.Sphere.OrthFacettes`; the remark l.1028–1029 (« s'il existe $m$ dans $F$ et $m'$ dans
  $F'$ … on a $\langle F, F'\rangle=0$ ») `orthFacettes_of_exists`.
* **`bzprop:c3s4p5_orthogonalite_alpha`** — `benzecri1960_ch3.tex:1032` (Prop. 5, l.1032–1039;
  proof l.1041–1044) — `Benzecri.Sphere.prop5_orthogonalite`.
* `bzprop:c3s4p6_facette_duale` — `benzecri1960_ch3.tex:1046` (Prop. 6, l.1046–1049; proof
  l.1051–1054) — NOT marked (a reading): `Benzecri.Sphere.prop6_facetteDuale`, true with
  « facette » in the extended sense of § 1 l.289–290 (the facette `∅` of dimension `−1` when the
  noyau is empty, strict `IsFacetteKExt`); false for the facettes of Déf. 4, which are nonempty
  (`FacetteDualeInstance.prop6_needs_extended_facette`, the open arc of `S(1)`); with genuine
  facettes exactly when `D(W_a) ≠ ∅` (`prop6_facetteDuale_of_nonempty`). The notation `𝒟(F)`:
  `Benzecri.Sphere.facetteDuale`.
* **`bzprop:c3s4p7_facette_duale_minimale`** — `benzecri1960_ch3.tex:1056` (Prop. 7, l.1056–1061;
  no proof printed) — `Benzecri.Sphere.prop7_facetteDuale`; the commentary l.1063–1066:
  `orthFacettes_facetteDuale` (`⟨F, 𝒟(F)⟩ = 0`, so 𝒟(F) is the α-least of those `F'`) and
  `subset_closure_facetteDuale` (« $\overline{\Dc(F)}$ contient toutes les facettes $F'$ telles que
  $\langle F, F'\rangle=0$ »).
* Instances on `S(1)`, the closed quarter arc `W = [a, b]` (`Benzecri.FacetteDualeInstance`):
  `D_arcS1` (`D(W) = W`), `def4_instance` (`⟨{a}, {b}⟩ = 0`), `facetteDuale_a0` (`𝒟({a}) = {b}`),
  `prop6_needs_extended_facette` (`F` the open arc: `D(W_c) = ∅`, `𝒟(F) = ∅`). The closed
  triangle `T` of `S(2)` (`simplexS 2`, the positive simplex of every `S(n)`): `D_simplexS`
  (`D(T) = T`), `facetteK_vertex0` (a vertex is a facette), `mk_mem_facetteK_oppVec` (the open
  opposite edge is a facette), `facetteDuale_vertex0` (`𝒟(vertex) = opposite edge`, orthogonal).

> **Proposition 4.** Soient $m$, $m'$, $p$, $p'$ quatre points de $S(n)$, entre lesquels on suppose
> vérifiées les relations $m\,\alpha(W)\,m'$; $p\,\alpha(D(W))\,p'$; $\langle m, p\rangle=0$.
> Alors $\langle m', p'\rangle=0$.
>
> *Démonstration.* Par raison de symétrie, il suffit de démontrer $\langle m', p\rangle=0$. Or cela
> résulte immédiatement des propositions 1 et 3.
>
> **Définition 4.** Soient $F$ une facette de $W$, $F'$ une facette de $D(W)$, nous dirons qu'est
> vérifiée la relation $\langle F, F'\rangle=0$ si pour tout point $m$ de $F$ et tout point $m'$ de
> $F'$ on a $\langle m, m'\rangle=0$.
>
> D'après la proposition précédente, s'il existe $m$ dans $F$ et $m'$ dans $F'$ tels que
> $\langle m, m'\rangle=0$, on a $\langle F, F'\rangle=0$.
>
> **Proposition 5.** Soient $F_1$, $F_2$ (resp. $F'_1$, $F'_2$) deux facettes de $W$ [resp. de
> $D(W)$] telles que soient vérifiées les relations $F_1\,\alpha(W)\,F_2$;
> $F'_1\,\alpha(D(W))\,F'_2$; $\langle F_1, F'_1\rangle=0$. Alors, on a
> $\langle F_2, F'_2\rangle=0$.
>
> **Proposition 6.** Soient $W\in K(S(n))$, $F$ une facette de $W$, $a\in F$, $D(W_a)$ est la
> fermeture d'une facette de $D(W)$ qui ne dépend pas du choix de $a$ et que nous noterons
> $\Dc(F)$.
>
> *Démonstration.* En effet, considérons un point $a'$ intérieur au convexe $D(W_a)$ muni de la
> topologie induite par celle de son support, $\Dc(F)$ n'est autre que la facette de $a'$.
>
> **Proposition 7.** Soient $F$ une facette de $W$, $F'$ une facette de $D(W)$ telles que
> $\langle F, F'\rangle=0$. Alors, on a $\Dc(F)\,\alpha(D(W))\,F'$.
>
> Nous dirons que $\Dc(F)$ est la facette minimale (au sens de $\alpha$) parmi celles $F'$ qui
> vérifient $\langle F, F'\rangle=0$. Du point de vue ensembliste, notons que
> $\overline{\Dc(F)}$ contient toutes les facettes $F'$ telles que $\langle F, F'\rangle=0$.

## The proofs formalized

Prop. 4, through the duality inequality only (no closedness, no bidual): from
`M + ε(M − M′) ∈ F(W) ∪ {O}` and `P ∈ F∘D(W)`, `0 ≤ ⟨M + ε(M − M′), P⟩ = −ε⟨M′, P⟩ ≤ 0`, so
`⟨m′, p⟩ = 0` (the printed route: Prop. 1 (1) ⇒ (3) and Prop. 3, which is this computation); the
same with the roles exchanged (`P + ε(P − P′) ∈ F∘D(W) ∪ {O}`, `m′ ∈ W`) gives `⟨m′, p′⟩ = 0`.
Déf. 4's remark and Prop. 5: the points of a facette are pairwise α-related
(`facetteKLE_iff_forall`), then Prop. 4. Prop. 6: `C = D(W_a) = {m ∈ D(W) | ⟨m, a⟩ = 0}`
(Prop. 3) is a closed convex part of `D(W)`, saturated for α(D(W)) (Prop. 2); it does not depend
on `a ∈ F` by Prop. 4. If `C ≠ ∅`, the strict `exists_facette_support_eq` applied to the cone
`C′ = F(C) ∪ {O}` gives a point `a′ ∈ C` with `a′ α(C) b` for every `b ∈ C` (a point « intérieur
au convexe $D(W_a)$ … de son support », `exists_alphaK_least`); its facette `G` in `D(W)` lies in
`C` (saturation), and every `b ∈ C` is the limit of `s((1−t)A′ + tB) ∈ G`, `t → 1⁻`, so
`Ḡ = C`; any facette `G'` with `Ḡ' = C` equals `G` (`C ⊆ Ḡ'` lies in the closed support of
`G'`, strict Prop. 2 for `S(E)`, `alphaK_iff_mem_supportK`). If `C = ∅`, the noyau of `D(W)`,
contained in `C`, is empty, and `∅` is the facette of dimension `−1`. Prop. 7: `F' ⊆ C`, so
`C ≠ ∅` and `a′ α(D(W)) p′` for `p′ ∈ F'`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| § 4 standing: « $E$ est $\R^{n+1}$, canoniquement identifié à son dual au moyen de la forme $\sum_i x_iy_i$ » | ✓ carried: `S n`, `dotPairing n`, `D (dotPairing n)` |
| Props. 4, 5, 7: the convex `W` (« $W\in K(S(n))$ », stated in Prop. 6 and Prop. 3) | ✓ carried: `IsConvexPart W`; no closedness anywhere |
| Prop. 4: « $m\,\alpha(W)\,m'$; $p\,\alpha(D(W))\,p'$; $\langle m, p\rangle=0$ » | ✓ carried: `AlphaK W m m'`, `AlphaK (D W) p p'`, `OrthPts m p` (§ 4 Déf. 3) |
| Déf. 4: « $F$ une facette de $W$, $F'$ une facette de $D(W)$ » | ✓ the definition `OrthFacettes F F'` is stated for all parts; the remark carries `IsFacetteK W F`, `IsFacetteK (D W) F'` |
| Prop. 5: « $F_1\,\alpha(W)\,F_2$ », « $F'_1\,\alpha(D(W))\,F'_2$ » | ✓ carried: `FacetteKLE` (§ 1 Déf. 4 for facettes of `S(E)`) |
| Prop. 6: « $F$ une facette de $W$, $a\in F$ » | ✓ carried: `IsFacetteK W F`, `∀ a ∈ F` |
| Prop. 6: « la fermeture » | ✓ carried: `closure` in the quotient topology of `S(n)` |
| Prop. 6: « une facette de $D(W)$ » | ⚠ reading: the extended sense of l.289–290 (`IsFacetteKExt`); genuine facettes when `D(W_a) ≠ ∅` |
| Prop. 6: « qui ne dépend pas du choix de $a$ » | ✓ carried: one `G` for every `a ∈ F`, `D(W_a) = D(W_b)`, and `G` unique (`∃!`) |
| Prop. 7: « $\Dc(F)\,\alpha(D(W))\,F'$ » | ✓ carried: `FacetteKLE (D W) (facetteDuale W F) F'` (also for every pair of points, `facetteKLE_iff_forall`) |

## SCOPE (disclosed)

* No `sorry`, no axiom beyond the standard three.
* **Prop. 6 is not marked** (a reading): the facettes of Déf. 4 of § 1 (`IsFacetteK`) are
  nonempty, and `D(W_a)` is empty whenever `a` is « interior » in the sense that `W_a = S(n)`
  (`W = S(n)`; or the open arc of `S(1)`, `prop6_needs_extended_facette`, where `D(W) = W ≠ ∅`).
  Under the convention of l.289–290 (« une facette, de $k$ de dimension $(-1)$ » when the noyau is
  empty) Prop. 6 holds in full: `D(W_a) = ∅` forces the noyau of `D(W)` empty
  (`noyau_D_subset_D_coneAppui`), so `∅` is that facette.
* `𝒟(F)` (`facetteDuale`) is defined by choice among the extended facettes `G` of `D(W)` with
  `Ḡ = D(W_a)` for all `a ∈ F` (`∅` if there is none, which never happens for a facette `F`,
  `facetteDuale_spec`); by uniqueness it is the facette of the paper, and it is the k-facette of
  `a′` when `D(W_a) ≠ ∅` (`facetteDuale_eq_facetteK`).
* Prop. 7 is marked: its hypothesis `⟨F, F'⟩ = 0` with `F'` a (nonempty) facette makes
  `D(W_a) ≠ ∅`, so it holds under every reading of « facette » in Prop. 6. `F'` is a genuine
  facette here: under the extended reading, `F' = ∅` makes `⟨F, ∅⟩ = 0` vacuous and « 𝒟(F) α ∅ »
  meaningful only in the lifted sense on `F(D(W)) ∪ {O}`, where it holds trivially.
* General lemmas proved here (candidates to move upstream): `alphaW_mono`, `kPrime_mono`,
  `alphaK_mono`, `isClosed_linearSubvariety_S`, `alphaK_of_mem_closure`, `exists_alphaK_least`,
  `subset_closure_facetteK`, `isClosed_D_dot`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open Set Filter Topology

namespace Benzecri

namespace Sphere

variable {n : ℕ}

/-- A point of `D(W)` pairs nonnegatively with `F(W) ∪ {O}`. -/
theorem dot_nonneg_of_mem_kPrime_D {W : Set (S n)} {X : Fin (n + 1) → ℝ} (hX : X ∈ kPrime W)
    {p : S n} (hp : p ∈ D (dotPairing n) W) : 0 ≤ dotPairing n X (Module.Ray.someVector p) := by
  rcases hX with rfl | hX
  · simp
  · rw [← mk_someVector p, mk_mem_D] at hp
    exact hp X hX

/-- A point of `W` pairs nonnegatively with `F∘D(W) ∪ {O}`. -/
theorem dot_nonneg_of_mem_kPrime_D' {W : Set (S n)} {X : Fin (n + 1) → ℝ}
    (hX : X ∈ kPrime (D (dotPairing n) W)) {m : S n} (hm : m ∈ W) :
    0 ≤ dotPairing n (Module.Ray.someVector m) X := by
  have h := (claim_a_cone (dotPairing n) W).1
  rw [kPrime, h] at hX
  exact hX _ ⟨Module.Ray.someVector_ne_zero m, by rw [mk_someVector]; exact hm⟩

/-- **Prop. 4, the printed half** « $\langle m', p\rangle=0$ »: for `p ∈ D(W)`, `m α(W) m′` and
`⟨m, p⟩ = 0` give `⟨m′, p⟩ = 0`. -/
theorem orthPts_of_alphaK_left {W : Set (S n)} (hW : IsConvexPart W) {m m' p : S n}
    (hm : AlphaK W m m') (hp : p ∈ D (dotPairing n) W) (h : OrthPts m p) : OrthPts m' p := by
  obtain ⟨-, hM', ε, hε, hX⟩ := (alphaW_iff_extend (convex_kPrime hW)).1 hm
  have h1 := dot_nonneg_of_mem_kPrime_D hX hp
  have h2 := dot_nonneg_of_mem_kPrime_D hM' hp
  unfold OrthPts at h ⊢
  rw [map_add, map_smul, map_sub, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.sub_apply, h, smul_eq_mul] at h1
  have : ε * dotPairing n (Module.Ray.someVector m') (Module.Ray.someVector p) ≤ 0 := by linarith
  have h3 : dotPairing n (Module.Ray.someVector m') (Module.Ray.someVector p) ≤ 0 :=
    nonpos_of_mul_nonpos_right this hε
  linarith

/-- **Prop. 4, the half « par raison de symétrie »**: for `m ∈ W`, `p α(D(W)) p′` and
`⟨m, p⟩ = 0` give `⟨m, p′⟩ = 0`. -/
theorem orthPts_of_alphaK_right {W : Set (S n)} {m p p' : S n} (hm : m ∈ W)
    (hp : AlphaK (D (dotPairing n) W) p p') (h : OrthPts m p) : OrthPts m p' := by
  obtain ⟨-, hP', ε, hε, hX⟩ :=
    (alphaW_iff_extend (convex_kPrime (claim_a_convexPart _ W))).1 hp
  have h1 := dot_nonneg_of_mem_kPrime_D' hX hm
  have h2 := dot_nonneg_of_mem_kPrime_D' hP' hm
  unfold OrthPts at h ⊢
  rw [map_add, map_smul, map_sub, h, smul_eq_mul] at h1
  have : ε * dotPairing n (Module.Ray.someVector m) (Module.Ray.someVector p') ≤ 0 := by linarith
  have h3 : dotPairing n (Module.Ray.someVector m) (Module.Ray.someVector p') ≤ 0 :=
    nonpos_of_mul_nonpos_right this hε
  linarith

/-- **Prop. 4** (`bzprop:c3s4p4_orthogonalite_facettes`). -/
theorem prop4_orthogonalite {W : Set (S n)} (hW : IsConvexPart W) {m m' p p' : S n}
    (hm : AlphaK W m m') (hp : AlphaK (D (dotPairing n) W) p p') (h : OrthPts m p) :
    OrthPts m' p' :=
  orthPts_of_alphaK_right hm.mem_right hp (orthPts_of_alphaK_left hW hm hp.mem_left h)

/-- α(W) is monotone in `W`. -/
theorem alphaW_mono {E : Type*} [AddCommGroup E] [Module ℝ E] {W W' : Set E} (h : W ⊆ W')
    {A B : E} (hAB : AlphaW W A B) : AlphaW W' A B := by
  rcases hAB with ⟨A', hs, hA⟩ | ⟨rfl, hA⟩
  · exact Or.inl ⟨A', hs.trans h, hA⟩
  · exact Or.inr ⟨rfl, h hA⟩

theorem kPrime_mono {E : Type*} [AddCommGroup E] [Module ℝ E] {k k' : Set (Sphere E)}
    (h : k ⊆ k') : kPrime k ⊆ kPrime k' := insert_subset_insert (F_mono h)

/-- α(k) is monotone in `k`. -/
theorem alphaK_mono {E : Type*} [AddCommGroup E] [Module ℝ E] {k k' : Set (Sphere E)}
    (h : k ⊆ k') {a b : Sphere E} (hab : AlphaK k a b) : AlphaK k' a b :=
  alphaW_mono (kPrime_mono h) hab

/-- Linear subvarieties of `S(n)` are closed. -/
theorem isClosed_linearSubvariety_S (L : Submodule ℝ (Fin (n + 1) → ℝ)) :
    IsClosed (linearSubvariety L) := by
  rw [isClosed_iff_F_preimage]
  have : (Subtype.val ⁻¹' F (linearSubvariety L) : Set {v : Fin (n + 1) → ℝ // v ≠ 0}) =
      Subtype.val ⁻¹' (L : Set (Fin (n + 1) → ℝ)) := by
    ext ⟨v, hv⟩
    simp only [mem_preimage, mem_F, SetLike.mem_coe]
    exact ⟨fun ⟨_, h⟩ => (mk_mem_linearSubvariety hv).1 h,
      fun h => ⟨hv, (mk_mem_linearSubvariety hv).2 h⟩⟩
  rw [this]
  exact L.closed_of_finiteDimensional.preimage continuous_subtype_val

/-- A point `a` of a facette `f` of `K` is α(K)-below every point of `f̄ ∩ K`. -/
theorem alphaK_of_mem_closure {K f : Set (S n)} (hK : IsConvexPart K) (hf : IsFacetteK K f)
    {a b : S n} (ha : a ∈ f) (hb : b ∈ K) (hbc : b ∈ closure f) : AlphaK K a b :=
  (alphaK_iff_mem_supportK hK hf ha hb).2
    (closure_minimal (subset_supportK f) (isClosed_linearSubvariety_S _) hbc)

/-- **The point `a′` of the proof of Prop. 6**: a nonempty convex part `C` of `S(n)` has a point
`a′` with `a′ α(C) b` for every `b ∈ C` (a point of its relative interior). -/
theorem exists_alphaK_least {C : Set (S n)} (hC : IsConvexPart C) (hne : C.Nonempty) :
    ∃ a ∈ C, ∀ b ∈ C, AlphaK C a b := by
  have hcv := convex_kPrime hC
  obtain ⟨G, hG, hspan⟩ := exists_facette_support_eq hcv ⟨0, zero_mem_kPrime C⟩
    inferInstance
  obtain ⟨A, hA⟩ := hG.nonempty
  have hleast : ∀ B ∈ kPrime C, AlphaW (kPrime C) A B := fun B hB =>
    (alphaW_iff_mem_support hcv hG hA hB).2 (hspan ▸ subset_affineSpan ℝ _ hB)
  obtain ⟨c, hc⟩ := hne
  set Cv := Module.Ray.someVector c
  have hCv : Cv ∈ kPrime C := mem_kPrime_of_isRep (exists_isRep_someVector c) hc
  have hCv0 : AlphaW (kPrime C) Cv A → ∀ B ∈ kPrime C, AlphaW (kPrime C) Cv B :=
    fun h B hB => alphaW_trans hcv h (hleast B hB)
  have key : ∃ A' : Fin (n + 1) → ℝ, A' ≠ 0 ∧ ∀ B ∈ kPrime C, AlphaW (kPrime C) A' B := by
    by_cases hA0 : A = 0
    · refine ⟨Cv, Module.Ray.someVector_ne_zero c, hCv0 ?_⟩
      subst hA0
      refine (alphaW_iff_extend hcv).2 ⟨hCv, zero_mem_kPrime C, 1, one_pos, ?_⟩
      have : Cv + (1 : ℝ) • (Cv - 0) = (2 : ℝ) • Cv := by module
      rw [this]; exact smul_mem_kPrime hCv (by norm_num)
    · exact ⟨A, hA0, hleast⟩
  obtain ⟨A', hA'0, hA'⟩ := key
  refine ⟨mk A' hA'0, mem_of_isRep_of_mem_kPrime (isRep_mk _ hA'0) (hA' Cv hCv).mem_left,
    fun b hb => ?_⟩
  exact (alphaK_iff hC (isRep_mk _ hA'0) (exists_isRep_someVector b)).2
      (hA' _ (mem_kPrime_of_isRep (exists_isRep_someVector b) hb))


/-- If `C ⊆ K` are convex and `a′ ∈ C` is α(C)-least, `C` lies in the closure of the facette of
`a′` in `K`. -/
theorem subset_closure_facetteK {K C : Set (S n)} (hK : IsConvexPart K) (hC : IsConvexPart C)
    (hCK : C ⊆ K) {a : S n} (ha : a ∈ C) (hmin : ∀ b ∈ C, AlphaK C a b) :
    C ⊆ closure (facetteK K a) := by
  intro b hb
  by_cases h1 : b = a
  · subst h1; exact subset_closure (mem_facetteK_self (hCK hb))
  by_cases h2 : b = -a
  · refine subset_closure ⟨alphaK_of_eq_or_neg hK (hCK ha) (hCK hb) (Or.inr ?_),
      alphaK_of_eq_or_neg hK (hCK hb) (hCK ha) (Or.inr h2)⟩
    rw [h2, neg_neg]
  have hA := exists_isRep_someVector a
  have hB := exists_isRep_someVector b
  set A := Module.Ray.someVector a
  set B := Module.Ray.someVector b
  have hAB := linearIndependent_of_ne hA hB h1 h2
  have hcv := convex_kPrime hC
  have hAk : A ∈ kPrime C := mem_kPrime_of_isRep hA ha
  have hBk : B ∈ kPrime C := mem_kPrime_of_isRep hB hb
  let f : ℝ → Fin (n + 1) → ℝ := fun t => (1 - t) • A + t • B
  have hf : ∀ t, f t ≠ 0 := by
    intro t h
    have := LinearIndependent.pair_iff.1 hAB (1 - t) t h
    linarith [this.1, this.2]
  have hfc : Continuous f := by fun_prop
  have hc : Continuous fun t => mk (f t) (hf t) := continuous_mk_comp hfc hf
  have h1b : mk (f 1) (hf 1) = b := by
    have e : f 1 = B := by simp [f]
    obtain ⟨_, hBb⟩ := hB
    rw [← hBb]
    simp only [e]
  have hT : Tendsto (fun t => mk (f t) (hf t)) (𝓝[<] 1) (𝓝 b) := by
    rw [← h1b]
    exact (hc.tendsto 1).mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto hT ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t ht
  obtain ⟨ht0, ht1⟩ := ht
  obtain ⟨-, -, ε, hε, hX⟩ :=
    (alphaW_iff_extend hcv).1 ((alphaK_iff hC hA hB).1 (hmin b hb))
  have hft : f t ∈ kPrime C := hcv hAk hBk (by linarith) ht0.le (by ring)
  have k1 : AlphaW (kPrime C) A (f t) := by
    refine (alphaW_iff_extend hcv).2 ⟨hAk, hft, ε / t, by positivity, ?_⟩
    have e : A + (ε / t) • (A - f t) = A + ε • (A - B) := by
      simp only [f]
      have : A - ((1 - t) • A + t • B) = t • (A - B) := by module
      rw [this, smul_smul, div_mul_cancel₀ _ ht0.ne']
    rw [e]; exact hX
  have k2 : AlphaW (kPrime C) (f t) A := by
    refine (alphaW_iff_extend hcv).2 ⟨hft, hAk, 1 - t, by linarith, ?_⟩
    have e : f t + (1 - t) • (f t - A) = (1 - t * (2 - t)) • A + (t * (2 - t)) • B := by
      simp only [f]; module
    rw [e]
    exact hcv hAk hBk (by nlinarith) (by nlinarith) (by ring)
  exact ⟨(alphaK_iff hK hA (isRep_mk _ (hf t))).2 (alphaW_mono (kPrime_mono hCK) k1),
    (alphaK_iff hK (isRep_mk _ (hf t)) hA).2 (alphaW_mono (kPrime_mono hCK) k2)⟩


/-- **Déf. 4** (`bzdef:c3s4d4_orthogonalite_facettes`): `⟨F, F'⟩ = 0`. -/
def OrthFacettes (F F' : Set (S n)) : Prop :=
  ∀ m ∈ F, ∀ m' ∈ F', OrthPts m m'

/-- **Déf. 4, the remark l.1028–1029**: one orthogonal pair of points suffices. -/
theorem orthFacettes_of_exists {W : Set (S n)} (hW : IsConvexPart W) {F F' : Set (S n)}
    (hF : IsFacetteK W F) (hF' : IsFacetteK (D (dotPairing n) W) F') {m m' : S n}
    (hm : m ∈ F) (hm' : m' ∈ F') (h : OrthPts m m') : OrthFacettes F F' := by
  intro x hx x' hx'
  have h1 : FK W m x := by rw [hF.eq_facetteK hW hm] at hx; exact hx
  have h2 : FK (D (dotPairing n) W) m' x' := by
    rw [hF'.eq_facetteK (claim_a_convexPart _ W) hm'] at hx'; exact hx'
  exact prop4_orthogonalite hW h1.1 h2.1 h

/-- **Prop. 5** (`bzprop:c3s4p5_orthogonalite_alpha`). -/
theorem prop5_orthogonalite {W : Set (S n)} (hW : IsConvexPart W) {F₁ F₂ F₁' F₂' : Set (S n)}
    (hF₁ : IsFacetteK W F₁) (hF₂ : IsFacetteK W F₂)
    (hF₁' : IsFacetteK (D (dotPairing n) W) F₁') (hF₂' : IsFacetteK (D (dotPairing n) W) F₂')
    (h₁ : FacetteKLE W F₁ F₂) (h₂ : FacetteKLE (D (dotPairing n) W) F₁' F₂')
    (h : OrthFacettes F₁ F₁') : OrthFacettes F₂ F₂' := by
  obtain ⟨m, hm⟩ := hF₁.nonempty
  obtain ⟨m', hm'⟩ := hF₁'.nonempty
  intro x hx x' hx'
  exact prop4_orthogonalite hW ((facetteKLE_iff_forall hW hF₁ hF₂).1 h₁ m hm x hx)
    ((facetteKLE_iff_forall (claim_a_convexPart _ W) hF₁' hF₂').1 h₂ m' hm' x' hx')
    (h m hm m' hm')

theorem isClosed_D_dot (V : Set (S n)) : IsClosed (D (dotPairing n) V) :=
  isClosed_D _ (fun m => (dotPairing n m).continuous_of_finiteDimensional) V

/-- The noyau of `D(W)` lies in `D(W_a)`. -/
theorem noyau_D_subset_D_coneAppui {W : Set (S n)} (hW : IsConvexPart W) {a : S n}
    (ha : a ∈ W) : noyau (D (dotPairing n) W) ⊆ D (dotPairing n) (coneAppui W a) := by
  rw [noyau_eq (claim_a_convexPart _ W), prop3_coneAppui a hW ha]
  rintro m ⟨hm, hm'⟩
  refine ⟨hm, ?_⟩
  induction m using ind with
  | h M hM =>
  have hA := exists_isRep_someVector a
  have hAF : Module.Ray.someVector a ∈ F W := ⟨hA.ne_zero, by rw [mk_someVector]; exact ha⟩
  rw [neg_mk, mk_mem_D] at hm'
  rw [mk_mem_D] at hm
  have h1 := hm _ hAF
  have h2 := hm' _ hAF
  rw [map_neg] at h2
  rw [orthPts_iff (isRep_mk M hM) hA, dotPairing_comm]
  linarith

/-- **Prop. 6, « qui ne dépend pas du choix de $a$ »**: `D(W_a) = D(W_b)` for `a`, `b` in one
facette of `W`. -/
theorem D_coneAppui_eq_of_fk {W : Set (S n)} (hW : IsConvexPart W) {a b : S n} (hab : FK W a b) :
    D (dotPairing n) (coneAppui W a) = D (dotPairing n) (coneAppui W b) := by
  rw [prop3_coneAppui a hW hab.1.mem_left, prop3_coneAppui b hW hab.1.mem_right]
  ext m
  simp only [mem_setOf_eq]
  constructor
  · rintro ⟨hm, h⟩
    exact ⟨hm, orthPts_comm.1 (prop4_orthogonalite hW hab.1 (alphaK_refl hm) (orthPts_comm.1 h))⟩
  · rintro ⟨hm, h⟩
    exact ⟨hm, orthPts_comm.1 (prop4_orthogonalite hW hab.2 (alphaK_refl hm) (orthPts_comm.1 h))⟩

/-- **Prop. 6 when `D(W_a) ≠ ∅`**, with the proof's point `a′`: the facette of `a′` in `D(W)` has
closure `D(W_a)`, and is the only extended facette of `D(W)` with that closure. -/
theorem exists_facetteK_closure_eq_D_coneAppui {W : Set (S n)} (hW : IsConvexPart W) {a : S n}
    (ha : a ∈ W) (hne : (D (dotPairing n) (coneAppui W a)).Nonempty) :
    ∃ a' ∈ D (dotPairing n) (coneAppui W a),
      (∀ b ∈ D (dotPairing n) (coneAppui W a), AlphaK (D (dotPairing n) W) a' b) ∧
      IsFacetteK (D (dotPairing n) W) (facetteK (D (dotPairing n) W) a') ∧
      closure (facetteK (D (dotPairing n) W) a') = D (dotPairing n) (coneAppui W a) ∧
      ∀ G, IsFacetteKExt (D (dotPairing n) W) G →
        closure G = D (dotPairing n) (coneAppui W a) → G = facetteK (D (dotPairing n) W) a' := by
  set K := D (dotPairing n) W with hKdef
  set C := D (dotPairing n) (coneAppui W a) with hCdef
  have hK : IsConvexPart K := claim_a_convexPart _ W
  have hC : IsConvexPart C := claim_a_convexPart _ _
  have hCK : C ⊆ K := (prop2_coneAppui _ hW ha).1
  have hsat : ∀ x y, x ∈ C → AlphaK K x y → y ∈ C := fun x y hx hxy =>
    (prop2_coneAppui _ hW ha).2 x y hx hxy.mem_right hxy
  obtain ⟨a', ha', hmin⟩ := exists_alphaK_least hC hne
  have hminK : ∀ b ∈ C, AlphaK K a' b := fun b hb => alphaK_mono hCK (hmin b hb)
  have hcl : closure (facetteK K a') = C := by
    refine Subset.antisymm (closure_minimal (fun x hx => hsat a' x ha' hx.1) (isClosed_D_dot _))
      (subset_closure_facetteK hK hC hCK ha' hmin)
  refine ⟨a', ha', hminK, ⟨a', hCK ha', rfl⟩, hcl, fun G hG hGc => ?_⟩
  rcases (isFacetteKExt_iff hK).1 hG with hG | ⟨rfl, -⟩
  · obtain ⟨g, hg⟩ := hG.nonempty
    have hgC : g ∈ C := hGc ▸ subset_closure hg
    have h1 : AlphaK K g a' := alphaK_of_mem_closure hK hG hg (hCK ha') (hGc ▸ ha')
    rw [hG.eq_facetteK hK hg]
    exact facetteK_eq_of_fk hK ⟨h1, hminK g hgC⟩
  · rw [closure_empty] at hGc
    exact absurd (hGc ▸ ha') (notMem_empty a')

/-- **Prop. 6 at one point `a ∈ W`**: exactly one extended facette of `D(W)` has closure
`D(W_a)`. -/
theorem existsUnique_facetteKExt_closure {W : Set (S n)} (hW : IsConvexPart W) {a : S n}
    (ha : a ∈ W) : ∃! G, IsFacetteKExt (D (dotPairing n) W) G ∧
      closure G = D (dotPairing n) (coneAppui W a) := by
  have hK : IsConvexPart (D (dotPairing n) W) := claim_a_convexPart _ W
  rcases (D (dotPairing n) (coneAppui W a)).eq_empty_or_nonempty with he | hne
  · refine ⟨∅, ⟨(isFacetteKExt_iff hK).2 (Or.inr ⟨rfl, ?_⟩), by rw [closure_empty, he]⟩, ?_⟩
    · exact subset_empty_iff.1 (he ▸ noyau_D_subset_D_coneAppui hW ha)
    · rintro G ⟨-, hG⟩
      rw [he] at hG
      exact subset_empty_iff.1 (hG ▸ subset_closure)
  · obtain ⟨a', -, -, hf, hcl, huniq⟩ := exists_facetteK_closure_eq_D_coneAppui hW ha hne
    exact ⟨_, ⟨(isFacetteKExt_iff hK).2 (Or.inl hf), hcl⟩, fun G ⟨hG, hGc⟩ => huniq G hG hGc⟩

/-- **𝒟(F)** (Prop. 6, `bzprop:c3s4p6_facette_duale`): the extended facette of `D(W)` whose closure
is `D(W_a)` for every `a ∈ F` (`∅` if none, which never happens for a facette `F`). -/
noncomputable def facetteDuale (W F : Set (S n)) : Set (S n) :=
  open Classical in
  if h : ∃ G, IsFacetteKExt (D (dotPairing n) W) G ∧
      ∀ a ∈ F, closure G = D (dotPairing n) (coneAppui W a) then h.choose else ∅

theorem facetteDuale_spec {W : Set (S n)} (hW : IsConvexPart W) {F : Set (S n)}
    (hF : IsFacetteK W F) :
    IsFacetteKExt (D (dotPairing n) W) (facetteDuale W F) ∧
      ∀ a ∈ F, closure (facetteDuale W F) = D (dotPairing n) (coneAppui W a) := by
  have hex : ∃ G, IsFacetteKExt (D (dotPairing n) W) G ∧
      ∀ a ∈ F, closure G = D (dotPairing n) (coneAppui W a) := by
    obtain ⟨a₀, ha₀⟩ := hF.nonempty
    obtain ⟨G, ⟨hG, hGc⟩, -⟩ := existsUnique_facetteKExt_closure hW (hF.subset ha₀)
    refine ⟨G, hG, fun a ha => ?_⟩
    rw [hGc]
    apply D_coneAppui_eq_of_fk hW
    rw [hF.eq_facetteK hW ha₀] at ha
    exact ha
  rw [facetteDuale, dif_pos hex]
  exact hex.choose_spec

/-- **Prop. 6** (`bzprop:c3s4p6_facette_duale`, not marked: « facette » in the extended sense of
l.289–290). -/
theorem prop6_facetteDuale {W : Set (S n)} (hW : IsConvexPart W) {F : Set (S n)}
    (hF : IsFacetteK W F) :
    (∀ a ∈ F, ∀ b ∈ F, D (dotPairing n) (coneAppui W a) = D (dotPairing n) (coneAppui W b)) ∧
    (∀ a ∈ F, ∃! G, IsFacetteKExt (D (dotPairing n) W) G ∧
      closure G = D (dotPairing n) (coneAppui W a)) ∧
    IsFacetteKExt (D (dotPairing n) W) (facetteDuale W F) ∧
    (∀ a ∈ F, closure (facetteDuale W F) = D (dotPairing n) (coneAppui W a)) := by
  refine ⟨fun a ha b hb => ?_, fun a ha => existsUnique_facetteKExt_closure hW (hF.subset ha),
    facetteDuale_spec hW hF⟩
  apply D_coneAppui_eq_of_fk hW
  rw [hF.eq_facetteK hW ha] at hb
  exact hb

/-- **The proof of Prop. 6**: « $\Dc(F)$ n'est autre que la facette de $a'$ ». -/
theorem facetteDuale_eq_facetteK {W : Set (S n)} (hW : IsConvexPart W) {F : Set (S n)}
    (hF : IsFacetteK W F) {a : S n} (ha : a ∈ F)
    (hne : (D (dotPairing n) (coneAppui W a)).Nonempty) :
    ∃ a' ∈ D (dotPairing n) (coneAppui W a),
      (∀ b ∈ D (dotPairing n) (coneAppui W a), AlphaK (D (dotPairing n) W) a' b) ∧
      facetteDuale W F = facetteK (D (dotPairing n) W) a' := by
  obtain ⟨a', ha', hmin, -, -, huniq⟩ :=
    exists_facetteK_closure_eq_D_coneAppui hW (hF.subset ha) hne
  obtain ⟨h1, h2⟩ := facetteDuale_spec hW hF
  exact ⟨a', ha', hmin, huniq _ h1 (h2 a ha)⟩

/-- **Prop. 6 with genuine facettes**, when `D(W_a) ≠ ∅`. -/
theorem prop6_facetteDuale_of_nonempty {W : Set (S n)} (hW : IsConvexPart W) {F : Set (S n)}
    (hF : IsFacetteK W F) {a : S n} (ha : a ∈ F)
    (hne : (D (dotPairing n) (coneAppui W a)).Nonempty) :
    IsFacetteK (D (dotPairing n) W) (facetteDuale W F) ∧
      ∃! G, IsFacetteK (D (dotPairing n) W) G ∧ closure G = D (dotPairing n) (coneAppui W a) := by
  obtain ⟨a', -, -, hf, hcl, huniq⟩ :=
    exists_facetteK_closure_eq_D_coneAppui hW (hF.subset ha) hne
  obtain ⟨h1, h2⟩ := facetteDuale_spec hW hF
  refine ⟨?_, _, ⟨hf, hcl⟩, fun G ⟨hG, hGc⟩ => huniq G ?_ hGc⟩
  · rw [huniq _ h1 (h2 a ha)]; exact hf
  · exact (isFacetteKExt_iff (claim_a_convexPart _ W)).2 (Or.inl hG)

theorem mem_D_coneAppui_of_orthFacettes {W : Set (S n)} (hW : IsConvexPart W) {F F' : Set (S n)}
    (hF : IsFacetteK W F) (hF' : IsFacetteK (D (dotPairing n) W) F')
    (h : OrthFacettes F F') {a : S n} (ha : a ∈ F) :
    F' ⊆ D (dotPairing n) (coneAppui W a) := by
  intro p hp
  rw [prop3_coneAppui a hW (hF.subset ha)]
  exact ⟨hF'.subset hp, orthPts_comm.1 (h a ha p hp)⟩

/-- **Prop. 7** (`bzprop:c3s4p7_facette_duale_minimale`). -/
theorem prop7_facetteDuale {W : Set (S n)} (hW : IsConvexPart W) {F F' : Set (S n)}
    (hF : IsFacetteK W F) (hF' : IsFacetteK (D (dotPairing n) W) F')
    (h : OrthFacettes F F') : FacetteKLE (D (dotPairing n) W) (facetteDuale W F) F' := by
  obtain ⟨a, ha⟩ := hF.nonempty
  obtain ⟨p, hp⟩ := hF'.nonempty
  have hsub := mem_D_coneAppui_of_orthFacettes hW hF hF' h ha
  obtain ⟨a', ha', hmin, he⟩ := facetteDuale_eq_facetteK hW hF ha ⟨p, hsub hp⟩
  rw [he]
  exact ⟨a', mem_facetteK_self ((prop2_coneAppui _ hW (hF.subset ha)).1 ha'), p, hp,
    hmin p (hsub hp)⟩

/-- **l.1065–1066**: « $\overline{\Dc(F)}$ contient toutes les facettes $F'$ telles que
$\langle F, F'\rangle=0$ ». -/
theorem subset_closure_facetteDuale {W : Set (S n)} (hW : IsConvexPart W) {F F' : Set (S n)}
    (hF : IsFacetteK W F) (hF' : IsFacetteK (D (dotPairing n) W) F')
    (h : OrthFacettes F F') : F' ⊆ closure (facetteDuale W F) := by
  obtain ⟨a, ha⟩ := hF.nonempty
  rw [(facetteDuale_spec hW hF).2 a ha]
  exact mem_D_coneAppui_of_orthFacettes hW hF hF' h ha


/-- **l.1063–1064**: `⟨F, 𝒟(F)⟩ = 0`, so with Prop. 7 `𝒟(F)` is the α-least facette `F'` with
`⟨F, F'⟩ = 0`. -/
theorem orthFacettes_facetteDuale {W : Set (S n)} (hW : IsConvexPart W) {F : Set (S n)}
    (hF : IsFacetteK W F) : OrthFacettes F (facetteDuale W F) := by
  intro a ha m hm
  have : m ∈ D (dotPairing n) (coneAppui W a) := (facetteDuale_spec hW hF).2 a ha ▸ subset_closure hm
  rw [prop3_coneAppui a hW (hF.subset ha)] at this
  exact orthPts_comm.1 this.2

end Sphere

namespace FacetteDualeInstance

open Sphere ConeAppuiInstance FacettesSphereInstance ConeAppuiAlphaInstance

/-- The quarter arc is self-dual. -/
theorem D_arcS1 : D (dotPairing 1) arcS1 = arcS1 := by
  ext m
  induction m using ind with
  | h v hv =>
  rw [mk_mem_D, mk_mem_arcS1_iff]
  constructor
  · intro h
    have h0 := h e0 (mem_F_arcS1_iff.2 ⟨e0_ne_zero, by simp [e0], by simp [e0]⟩)
    have h1 := h e1 (mem_F_arcS1_iff.2 ⟨e1_ne_zero, by simp [e1], by simp [e1]⟩)
    simp [dotPairing_two, e0, e1] at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨h0, h1⟩ m hm
    obtain ⟨-, hm0, hm1⟩ := mem_F_arcS1_iff.1 hm
    rw [dotPairing_two]
    positivity

theorem isFacetteK_a0 : IsFacetteK arcS1 {a0} := by
  have : ({a0} : Set (S 1)) ∈ {f | IsFacetteK arcS1 f} := by rw [facettesK_arcS1]; simp
  exact this

theorem isFacetteK_b1 : IsFacetteK arcS1 {b1} := by
  have : ({b1} : Set (S 1)) ∈ {f | IsFacetteK arcS1 f} := by rw [facettesK_arcS1]; simp
  exact this

theorem orthPts_a0_b1 : OrthPts a0 b1 := by
  rw [orthPts_iff (m := a0) (p := b1) (isRep_mk e0 e0_ne_zero) (isRep_mk e1 e1_ne_zero),
    dotPairing_two]
  simp [e0, e1]

/-- **Instance of Déf. 4**: `⟨{a}, {b}⟩ = 0` for the ends of the arc, a facette of `W` and one of
`D(W) = W`. -/
theorem def4_instance :
    IsFacetteK arcS1 {a0} ∧ IsFacetteK (D (dotPairing 1) arcS1) {b1} ∧
      OrthFacettes ({a0} : Set (S 1)) {b1} := by
  refine ⟨isFacetteK_a0, by rw [D_arcS1]; exact isFacetteK_b1, ?_⟩
  rintro m rfl m' rfl
  exact orthPts_a0_b1

/-- **Instance of Prop. 6**: `𝒟({a}) = {b}`. -/
theorem facetteDuale_a0 : facetteDuale arcS1 {a0} = {b1} := by
  have hW := isConvexPart_arcS1
  obtain ⟨h1, h2⟩ := facetteDuale_spec hW isFacetteK_a0
  have hu := existsUnique_facetteKExt_closure hW a0_mem_arcS1
  refine hu.unique ⟨h1, h2 a0 (mem_singleton _)⟩ ⟨?_, ?_⟩
  · rw [isFacetteKExt_iff (claim_a_convexPart _ _), D_arcS1]
    exact Or.inl isFacetteK_b1
  · rw [prop3_instance, closure_singleton]

/-- The facette of the midpoint `c` of the arc is the open arc; `D(W_c) = ∅`. -/
theorem D_coneAppui_c1 : D (dotPairing 1) (coneAppui arcS1 c1) = ∅ := by
  rw [prop3_coneAppui c1 isConvexPart_arcS1 c1_mem_arcS1, eq_empty_iff_forall_notMem]
  rintro m ⟨hm, ho⟩
  induction m using ind with
  | h v hv =>
  rw [D_arcS1, mk_mem_arcS1_iff] at hm
  rw [orthPts_iff (p := c1) (isRep_mk v hv) (isRep_mk v11 v11_ne_zero), dotPairing_two] at ho
  simp only [v11, Matrix.cons_val_zero, Matrix.cons_val_one, mul_one] at ho
  exact hv (eq_zero_of_coords (by linarith [hm.1, hm.2]) (by linarith [hm.1, hm.2]))

/-- **Prop. 6 needs the facette of dimension `−1`** (l.289–290): for the open arc `F` (the facette
of its midpoint `c`), `D(W_c) = ∅` is the closure of no genuine facette of `D(W)` (Déf. 4 facettes
are nonempty); in the extended sense it is the closure of `∅`, and `𝒟(F) = ∅`. -/
theorem prop6_needs_extended_facette :
    IsFacetteK arcS1 (facetteK arcS1 c1) ∧ c1 ∈ facetteK arcS1 c1 ∧
      D (dotPairing 1) (coneAppui arcS1 c1) = ∅ ∧
      (¬ ∃ G, IsFacetteK (D (dotPairing 1) arcS1) G ∧
        closure G = D (dotPairing 1) (coneAppui arcS1 c1)) ∧
      facetteDuale arcS1 (facetteK arcS1 c1) = ∅ := by
  have hF : IsFacetteK arcS1 (facetteK arcS1 c1) := ⟨c1, c1_mem_arcS1, rfl⟩
  have hc := mem_facetteK_self c1_mem_arcS1
  refine ⟨hF, hc, D_coneAppui_c1, ?_, ?_⟩
  · rintro ⟨G, hG, hGc⟩
    obtain ⟨g, hg⟩ := hG.nonempty
    have := hGc ▸ subset_closure hg
    rw [D_coneAppui_c1] at this
    exact this
  · have := (facetteDuale_spec isConvexPart_arcS1 hF).2 c1 hc
    rw [D_coneAppui_c1] at this
    exact subset_empty_iff.1 (this ▸ subset_closure)


/-! ### Triangle — the positive simplex of `S(n + 1)`, the closed triangle of `S(2)` for `n = 1` -/

section Triangle

variable {n : ℕ}

/-- The closed positive orthant of `ℝⁿ⁺¹`. -/
def orthant (n : ℕ) : Set (Fin (n + 1) → ℝ) := {v | ∀ i, 0 ≤ v i}

/-- The closed positive simplex `T = s(orthant − {O})` of `S(n)` (the closed triangle of `S(2)`). -/
def simplexS (n : ℕ) : Set (S n) := ofCone (orthant n)

theorem isPosCone_orthant : IsPosCone (orthant n) := fun c hc v hv i => by
  have := hv i
  simp only [Pi.smul_apply, smul_eq_mul]
  positivity

theorem kPrime_simplexS : kPrime (simplexS n) = orthant n := by
  rw [kPrime, simplexS, F_ofCone isPosCone_orthant, Set.insert_sdiff_singleton,
    Set.insert_eq_of_mem (show (0 : Fin (n + 1) → ℝ) ∈ orthant n from fun i => le_refl 0)]

theorem isConvexPart_simplexS : IsConvexPart (simplexS n) := by
  show Convex ℝ (kPrime (simplexS n))
  rw [kPrime_simplexS]
  intro x hx y hy a b ha hb _ i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have := hx i
  have := hy i
  positivity

theorem mk_mem_simplexS_iff {v : Fin (n + 1) → ℝ} (hv : v ≠ 0) :
    mk v hv ∈ simplexS n ↔ ∀ i, 0 ≤ v i := by
  rw [mk_mem_iff_mem_F, ← mem_kPrime_of_ne hv, kPrime_simplexS]; rfl

theorem dotPairing_single (i : Fin (n + 1)) (v : Fin (n + 1) → ℝ) :
    dotPairing n (Pi.single i 1) v = v i := by
  rw [dotPairing_apply]
  simp [Pi.single_apply]

/-- The simplex is self-dual: `D(T) = T`. -/
theorem D_simplexS : D (dotPairing n) (simplexS n) = simplexS n := by
  ext m
  induction m using ind with
  | h v hv =>
  rw [mk_mem_D, mk_mem_simplexS_iff]
  constructor
  · intro h i
    have hs : (Pi.single i 1 : Fin (n + 1) → ℝ) ≠ 0 := by
      intro h0; simpa using congrFun h0 i
    have := h _ ⟨hs, (mk_mem_simplexS_iff hs).2 fun j => by
      rw [Pi.single_apply]; split_ifs <;> norm_num⟩
    rwa [dotPairing_single] at this
  · intro h m hm
    have hm' := (mk_mem_simplexS_iff hm.1).1 hm.2
    rw [dotPairing_apply]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hm' i) (h i)

/-- α of the orthant: `A α B` iff every coordinate vanishing at `A` vanishes at `B`. -/
theorem alphaW_orthant_iff {A B : Fin (n + 1) → ℝ} :
    AlphaW (orthant n) A B ↔ A ∈ orthant n ∧ B ∈ orthant n ∧ ∀ i, A i = 0 → B i = 0 := by
  have hcv : Convex ℝ (orthant n) := by
    have := isConvexPart_simplexS (n := n)
    rwa [IsConvexPart, ← kPrime, kPrime_simplexS] at this
  rw [alphaW_iff_extend hcv]
  constructor
  · rintro ⟨hA, hB, ε, hε, hX⟩
    refine ⟨hA, hB, fun i hi => ?_⟩
    have h1 := hX i
    have h2 := hB i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hi, zero_sub,
      zero_add, mul_neg] at h1
    have : ε * B i ≤ 0 := by linarith
    have := nonpos_of_mul_nonpos_right this hε
    linarith
  · rintro ⟨hA, hB, h0⟩
    refine ⟨hA, hB, ?_⟩
    have hev : ∀ i, ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 ≤ A i + ε * (A i - B i) := by
      intro i
      rcases (hA i).lt_or_eq with hpos | hzero
      · have hc : Continuous fun ε : ℝ => A i + ε * (A i - B i) := by fun_prop
        have := (hc.tendsto 0).eventually (lt_mem_nhds (show (0 : ℝ) < A i + 0 * (A i - B i) by
          simpa using hpos))
        exact (this.mono fun _ h => h.le).filter_mono nhdsWithin_le_nhds
      · refine Eventually.of_forall fun ε => ?_
        rw [← hzero, h0 i hzero.symm]; simp
    obtain ⟨ε, hε, hpos⟩ := ((Filter.eventually_all.2 hev).and self_mem_nhdsWithin).exists
    refine ⟨ε, hpos, fun i => ?_⟩
    simpa [Pi.add_apply, smul_eq_mul] using hε i

theorem alphaK_simplexS_iff {a b : S n} {A B : Fin (n + 1) → ℝ} (hA : IsRep A a)
    (hB : IsRep B b) :
    AlphaK (simplexS n) a b ↔ A ∈ orthant n ∧ B ∈ orthant n ∧ ∀ i, A i = 0 → B i = 0 := by
  rw [alphaK_iff isConvexPart_simplexS hA hB, kPrime_simplexS, alphaW_orthant_iff]

/-- The vertex `s(e₀)` of the simplex. -/
def vertex0 (n : ℕ) : S n := mk (Pi.single 0 1) (by intro h; simpa using congrFun h 0)

/-- **A vertex is a facette**: the facette of `s(e₀)` in `T` is `{s(e₀)}`. -/
theorem facetteK_vertex0 : facetteK (simplexS n) (vertex0 n) = {vertex0 n} := by
  have he : (Pi.single 0 1 : Fin (n + 1) → ℝ) ≠ 0 := by intro h; simpa using congrFun h 0
  ext x
  constructor
  · rintro ⟨h, -⟩
    induction x using ind with
    | h X hX =>
    obtain ⟨-, hXo, hX0⟩ := (alphaK_simplexS_iff (isRep_mk _ he) (isRep_mk X hX)).1 h
    have hXi : ∀ i, i ≠ 0 → X i = 0 := fun i hi => hX0 i (by simp [hi])
    have hXe : X = X 0 • (Pi.single 0 1 : Fin (n + 1) → ℝ) := by
      funext i
      by_cases hi : i = 0
      · subst hi; simp
      · simp [hi, hXi i hi]
    have hpos : 0 < X 0 := by
      rcases (hXo 0).lt_or_eq with h | h
      · exact h
      · exact absurd (by rw [hXe, ← h, zero_smul]) hX
    show mk X hX = vertex0 n
    have : mk X hX = mk (X 0 • (Pi.single 0 1 : Fin (n + 1) → ℝ)) (hXe ▸ hX) := by
      congr 1
    rw [this, mk_smul he hpos]
    rfl
  · rintro rfl
    exact mem_facetteK_self ((mk_mem_simplexS_iff he).2 fun j => by
      rw [Pi.single_apply]; split_ifs <;> norm_num)

theorem isFacetteK_vertex0 : IsFacetteK (simplexS n) {vertex0 n} := by
  refine ⟨vertex0 n, ?_, facetteK_vertex0.symm⟩
  exact (mk_mem_simplexS_iff _).2 fun j => by rw [Pi.single_apply]; split_ifs <;> norm_num

/-- The vector `(0, 1, …, 1)`. -/
def oppVec (n : ℕ) : Fin (n + 2) → ℝ := fun i => if i = 0 then 0 else 1

theorem oppVec_ne_zero : oppVec n ≠ 0 := by
  intro h
  have := congrFun h 1
  simp [oppVec] at this

/-- **The facette opposite to the vertex `s(e₀)`** (for `n + 1 = 2`: the open edge
`]s(e₁), s(e₂)[`): the facette of `s(0, 1, …, 1)` is `{s(v) | v₀ = 0, vᵢ > 0 for i ≠ 0}`. -/
theorem mk_mem_facetteK_oppVec {v : Fin (n + 2) → ℝ} (hv : v ≠ 0) :
    mk v hv ∈ facetteK (simplexS (n + 1)) (mk (oppVec n) oppVec_ne_zero) ↔
      v 0 = 0 ∧ ∀ i, i ≠ 0 → 0 < v i := by
  have hu : oppVec n ∈ orthant (n + 1) := fun i => by
    simp only [oppVec]; split_ifs <;> norm_num
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨-, hvo, hz⟩ := (alphaK_simplexS_iff (isRep_mk _ _) (isRep_mk v hv)).1 h1
    obtain ⟨-, -, hz'⟩ := (alphaK_simplexS_iff (isRep_mk v hv) (isRep_mk _ _)).1 h2
    refine ⟨hz 0 (by simp [oppVec]), fun i hi => (hvo i).lt_of_ne fun h => ?_⟩
    have := hz' i h.symm
    simp [oppVec, hi] at this
  · rintro ⟨h0, hpos⟩
    have hvo : v ∈ orthant (n + 1) := fun i => by
      by_cases hi : i = 0
      · rw [hi, h0]
      · exact (hpos i hi).le
    refine ⟨(alphaK_simplexS_iff (isRep_mk _ _) (isRep_mk v hv)).2 ⟨hu, hvo, fun i hi => ?_⟩,
      (alphaK_simplexS_iff (isRep_mk v hv) (isRep_mk _ _)).2 ⟨hvo, hu, fun i hi => ?_⟩⟩
    · by_cases hi0 : i = 0
      · rw [hi0, h0]
      · simp [oppVec, hi0] at hi
    · by_cases hi0 : i = 0
      · simp [oppVec, hi0]
      · exact absurd hi (hpos i hi0).ne'

/-- **Instance of Props. 6 and 7 on the triangle** (`n + 1 = 2`, and every `n`): for the vertex
facette `{s(e₀)}` of `T`, `𝒟({s(e₀)})` is the opposite facette of `D(T) = T`, and
`⟨{s(e₀)}, 𝒟({s(e₀)})⟩ = 0`. -/
theorem facetteDuale_vertex0 :
    facetteDuale (simplexS (n + 1)) {vertex0 (n + 1)} =
        facetteK (simplexS (n + 1)) (mk (oppVec n) oppVec_ne_zero) ∧
      IsFacetteK (D (dotPairing (n + 1)) (simplexS (n + 1)))
        (facetteDuale (simplexS (n + 1)) {vertex0 (n + 1)}) ∧
      OrthFacettes {vertex0 (n + 1)} (facetteDuale (simplexS (n + 1)) {vertex0 (n + 1)}) := by
  have hW := isConvexPart_simplexS (n := n + 1)
  have hF := isFacetteK_vertex0 (n := n + 1)
  have he : (Pi.single 0 1 : Fin (n + 2) → ℝ) ≠ 0 := by intro h; simpa using congrFun h 0
  have hrep : IsRep (Pi.single 0 1 : Fin (n + 2) → ℝ) (vertex0 (n + 1)) := isRep_mk _ he
  have hu : oppVec n ∈ orthant (n + 1) := fun i => by
    simp only [oppVec]; split_ifs <;> norm_num
  have hva : vertex0 (n + 1) ∈ simplexS (n + 1) := hF.subset (mem_singleton _)
  have huC : mk (oppVec n) oppVec_ne_zero ∈
      D (dotPairing (n + 1)) (coneAppui (simplexS (n + 1)) (vertex0 (n + 1))) := by
    rw [prop3_coneAppui _ hW hva, mem_setOf_eq, D_simplexS, mk_mem_simplexS_iff,
      orthPts_iff (isRep_mk _ _) hrep, dotPairing_comm, dotPairing_single]
    exact ⟨hu, by simp [oppVec]⟩
  obtain ⟨a', ha', hmin, hE⟩ := facetteDuale_eq_facetteK hW hF (mem_singleton _) ⟨_, huC⟩
  have key : facetteDuale (simplexS (n + 1)) {vertex0 (n + 1)} =
      facetteK (simplexS (n + 1)) (mk (oppVec n) oppVec_ne_zero) := by
    rw [hE, D_simplexS]
    have h1 := hmin _ huC
    rw [D_simplexS] at h1
    refine facetteK_eq_of_fk hW ⟨h1, ?_⟩
    have ha'2 := ha'
    rw [prop3_coneAppui _ hW hva, mem_setOf_eq] at ha'2
    obtain ⟨haK, hao⟩ := ha'2
    rw [D_simplexS] at haK
    have hA := exists_isRep_someVector a'
    rw [orthPts_iff hA hrep, dotPairing_comm, dotPairing_single] at hao
    refine (alphaK_simplexS_iff (isRep_mk _ _) hA).2 ⟨hu, ?_, fun i hi => ?_⟩
    · rw [← kPrime_simplexS]; exact mem_kPrime_of_isRep hA haK
    · by_cases hi0 : i = 0
      · rw [hi0]; exact hao
      · simp [oppVec, hi0] at hi
  refine ⟨key, ?_, orthFacettes_facetteDuale hW hF⟩
  rw [key, D_simplexS]
  exact ⟨_, (mk_mem_simplexS_iff _).2 hu, rfl⟩

end Triangle

end FacetteDualeInstance

end Benzecri
