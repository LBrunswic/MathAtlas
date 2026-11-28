import Benzecri.Chapter3.BooleProjectif

/-!
# Chapter 3 § 2, the Corollary of Prop. 5, its refinement step: the simple distinguished subspaces of a sum are those of its summands

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 3 § 2, journal p. 268; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch3.tex` (TO BE CHECKED BY THE AUTHOR).
Target T-bz-c3-simples-somme.

* `bzcor:c3s2p5c_balayable_somme_quelconque` — `benzecri1960_ch3.tex:623` (the Corollary of
  Prop. 5, l.623–626, proof l.628–632), NOT marked: this file proves only the first sentence of
  the printed proof, the reduction « On se ramène à une décomposition de `w` en somme de convexes
  contenus dans des variétés distinguées simples »; the equivalence « balayable (resp. homogène) »
  is T-bz-c3-balayable-somme-cor. Proved: `Benzecri.Sphere.simplesS_somme` (for `w` a sum of
  convexes `vᵢ ⊆ s(Lᵢ − O)` with `E = ⊕ Lᵢ`: each `Lᵢ` is distinguished, the simple
  distinguished subvarieties of `w` are those of the closed cones `K̄(vᵢ)` read in their own `Lᵢ`
  and pushed into `E`, each lies in exactly one `Lᵢ`, and each `Lᵢ` is the sum of those it
  contains); `Benzecri.Sphere.simplesS_somme_supports` (the same with `Lᵢ = span F(vᵢ)`, the
  supports of the `vᵢ`, whose independence and spanning are proved: `iSupIndep_supports`,
  `iSup_eq_top_of_estSommeS`); `Benzecri.Sphere.closure_kPrime_somme` (`K̄(w) ∩ Lᵢ = K̄(vᵢ)` and
  `(Lᵢ, ⊕_{j≠i} Lⱼ)` is a conjugate pair of `K̄(w)`). The affine form, any real vector space:
  `Benzecri.simples_isSommeConvexes` (Déf. 1: `W = ∑ Vᵢ`, `0 ∈ Vᵢ ⊆ Lᵢ`, `E = ⊕ Lᵢ`),
  `Benzecri.sSup_simples_le_eq`, and under the weaker hypothesis of a conjugate pair
  `Benzecri.simples_eq_iUnion`, `Benzecri.estDistingue_map_iff`, `Benzecri.estSimple_map_iff`
  (distinguished / simple subspaces inside a conjugate `P` are those of `P ∩ W` read in `↥P`),
  `Benzecri.hyps_preimage` (`P ∩ W` read in `↥P` satisfies the hypotheses of Théorème 2).

Instance: the open `3`-simplex of `S(3)` as the sum of its two open edges `s(Q₀₁)`, `s(Q₂₃)`
(`Q₀₁` the open positive quadrant of `⟨e₀, e₁⟩`): `SimplesSommeInstance.simplexO_estSommeS_edges`
(Déf. 5), `edges_subset`, `iSupIndep_Lp` (`ℝ⁴ = ⟨e₀, e₁⟩ ⊕ ⟨e₂, e₃⟩`), with the hypotheses of
`theoreme3` from `simplexO_hyps`; `simplexO_simplesS_somme` (the conclusion on the instance) and
`simplexO_simplesS_somme_ncard` (the two edges contribute four simple ones in all). The affine form: the
cube `[−1, 1]ⁿ = ([−1, 1]ⁿ ∩ ℝ^S) + ([−1, 1]ⁿ ∩ ℝ^{Sᶜ})` (`Benzecri.cube_simples_isSommeConvexes`).

> **Corollaire.** Soit $w$ un ouvert convexe de $S(\R^{n+1})$ de noyau vide, somme de $p$
> convexes $v_1$, …, $v_i$, …, $v_p$. $w$ est balayable (resp. homogène) si et seulement si les
> $v_i$ le sont.
>
> **Démonstration.** — On se ramène à une décomposition de $w$ en somme de convexes contenus dans
> des variétés distinguées simples et l'on applique la proposition précédente.

## The proof formalized

*Affine.* Let `P`, `Q` be supplementary with `W = P ∩ W + Q ∩ W`. A subspace `N ≤ P` is
distinguished for `W` iff it is, read in `↥P`, distinguished for `P ∩ W`: a conjugate `C` of `N`
in `E` gives the conjugate `C ∩ P` in `P` (modularity, `N ≤ P`), and a conjugate `C′` in `P`
gives `C′ + Q` in `E` (a point `n + y`, `y = c + q`, is recomposed through the decomposition of
`y` along `P ⊕ Q`). Minimality transfers since every `M ≤ P` is the image of its preimage
(`estSimple_map_iff`). For `E = ⊕ Lᵢ` with each `(Lᵢ, ⊕_{j≠i} Lⱼ)` a conjugate pair, every `Lᵢ` is
distinguished; a simple `s` meeting every `Lᵢ` at `0` would meet their sum `E` at `0`
(`inf_sSup_eq_bot`, Théorème 2's distributivity), so `s ≤ Lᵢ` for some `i`, a unique one since
`Lᵢ ∩ Lⱼ = 0`. For Déf. 1, `W = ∑ Vᵢ` with `0 ∈ Vᵢ ⊆ Lᵢ`: `Lᵢ ∩ W = Vᵢ` and the conjugate pairs come
from projecting a decomposition (`eq_zero_of_sum_mem_iSup_ne`).
*Sphere.* With `πᵢ` the projection on `Lᵢ` along `⊕_{j≠i} Lⱼ` (continuous, finite dimension),
`πᵢ(∑ yⱼ) = yᵢ`; a partial sum `∑_{j ∈ S} yⱼ` is in `K̄(w)` as the limit of `∑_{S} yⱼ + s ∑_{Sᶜ} yⱼ`
(`sum_subset_mem_closure_kPrime`), so `πᵢ` and `1 − πᵢ` map `K̄(w)` into itself, and
`K̄(w) ∩ Lᵢ = K̄(vᵢ)`. The affine form applies to `K̄(w)` (`not_contientDroite_closure`,
`simplesS_eq`). The supports: in a nonempty convex positive cone, `span C = C − C`
(`exists_sub_of_mem_span_cone`), so Déf. 1's injectivity makes the spans independent.

## Hypothesis checklist

| hypothesis | here |
|---|---|
| `w` ouvert convexe de `S(ℝⁿ⁺¹)` | ✓ `IsOpen w`, `IsConvexPart w`; any finite-dimensional real normed `E` (stronger) |
| `w` de noyau vide | ✓ `noyau w = ∅` |
| (not printed) `F(w)` contains no line | ⚠ strengthened, OQ-168 / OQ-171's corrected hypothesis (`¬ ContientDroite (F w)`), as in `theoreme3`, `prop4_somme` |
| (not printed) support `S(E)` | ⚠ strengthened, `supportK w = univ`, as in `theoreme3` |
| `w` somme de `p` convexes `vᵢ` | ✓ Déf. 5, `EstSommeS w v`, `I` any finite type |
| « convexes contenus dans des variétés distinguées » | ✓ `vᵢ ⊆ s(Lᵢ − O)` with `E = ⊕ Lᵢ` (`iSupIndep L`; `⨆ Lᵢ = ⊤` is proved), or `Lᵢ` the supports (`simplesS_somme_supports`, no hypothesis on `L`) |
| affine form: `W = ∑ Vᵢ` (Déf. 1), `0 ∈ Vᵢ ⊆ Lᵢ`, `E = ⊕ Lᵢ`, `W` spanning, no line | ✓ `IsSommeConvexes W V`, `hV0`, `hVL`, `iSupIndep L`, `span W = ⊤`, `¬ ContientDroite W` (convexity and `0 ∈ W` follow) |

## SCOPE (disclosed)

* **Not marked.** The label is the Corollary « `w` balayable (resp. homogène) ssi les `vᵢ` le
  sont »; this file is the reduction step only (T-bz-c3-simples-somme, « this lemma marks nothing
  alone »). The Corollary is assembled by T-bz-c3-balayable-somme-cor, which also carries its
  readings (OQ-171's line-free hypothesis; « convexes » the nonempty Déf. 5 summands).
* **« pris dans son propre `Lᵢ` ».** The simple subspaces of a summand are read in `↥Lᵢ`, for the
  closed cone `Lᵢ.subtype ⁻¹' K̄(vᵢ)`: read in `E`, a summand that does not span `E` has every
  subspace of a complement of `Lᵢ` among its distinguished subspaces, so `simples` of it in `E`
  is not the right set (argued, not formalized). The transport of `vᵢ` to a sphere `S(↥Lᵢ)` (and to `S(kᵢ)` through a
  basis), needed to apply Prop. 5 to the `vᵢ`, is not here.
* **Refinement, not an enumeration.** The theorem says that the simple ones of `w` are the
  disjoint union, over `i`, of those of the summands; that each summand `vᵢ` is then the sum of
  the `Prop. 4` summands of the simple ones inside `Lᵢ` is `prop4_somme` applied to `vᵢ` in `↥Lᵢ`,
  left to T-bz-c3-balayable-somme-cor with the transport.
* No finding against the paper: the reduction holds under the hypotheses already carried by
  Théorème 3 and Prop. 4 (no line in `F(w)`, support `S(E)`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open Set Function
open scoped Pointwise

namespace Benzecri

section SimplesSommeAffine

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Distinguished subspaces inside a conjugate `P` (with `W = P ∩ W + Q ∩ W`, `P ⊕ Q = E`) are
the distinguished subspaces of `P ∩ W` read in `↥P`. -/
theorem estDistingue_map_iff {W : Set E} {P Q : Submodule ℝ E} (hc : IsCompl P Q)
    (hcj : SontConjugues W P Q) (N : Submodule ℝ P) :
    EstDistingue W (N.map P.subtype) ↔ EstDistingue (P.subtype ⁻¹' W) N := by
  constructor
  · rintro ⟨C, hC, hCW⟩
    refine ⟨C.comap P.subtype, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · rw [Submodule.disjoint_def]
        intro x hxN hxC
        have h1 : (x : E) ∈ N.map P.subtype := ⟨x, hxN, rfl⟩
        have := Submodule.disjoint_def.1 hC.disjoint _ h1 hxC
        exact Subtype.ext this
      · rw [codisjoint_iff, eq_top_iff]
        intro x _
        obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (hC.sup_eq_top ▸ Submodule.mem_top :
          (x : E) ∈ N.map P.subtype ⊔ C)
        obtain ⟨n, hn, rfl⟩ := ha
        have hbP : b ∈ P := by
          have : b = (x : E) - n := eq_sub_of_add_eq' hab
          rw [this]; exact P.sub_mem x.2 n.2
        refine Submodule.mem_sup.2 ⟨n, hn, ⟨b, hbP⟩, hb, Subtype.ext ?_⟩
        simpa using hab
    · ext x
      simp only [Set.mem_preimage, Set.mem_add, Set.mem_inter_iff, SetLike.mem_coe,
        Submodule.mem_comap, Submodule.subtype_apply]
      constructor
      · intro hx
        have hx' := hx
        rw [hCW, Set.mem_add] at hx'
        obtain ⟨a, ⟨ha, haW⟩, b, ⟨hb, hbW⟩, hab⟩ := hx'
        obtain ⟨n, hn, rfl⟩ := ha
        have hbP : b ∈ P := by
          have : b = (x : E) - n := eq_sub_of_add_eq' hab
          rw [this]; exact P.sub_mem x.2 n.2
        exact ⟨n, ⟨hn, haW⟩, ⟨b, hbP⟩, ⟨hb, hbW⟩, Subtype.ext (by simpa using hab)⟩
      · rintro ⟨a, ⟨ha, haW⟩, b, ⟨hb, hbW⟩, rfl⟩
        rw [Submodule.coe_add, hCW]
        exact Set.add_mem_add ⟨⟨a, ha, rfl⟩, haW⟩ ⟨hb, hbW⟩
  · rintro ⟨C', hC', hCW'⟩
    refine ⟨C'.map P.subtype ⊔ Q, ?_, ?_⟩
    · have hNP : N.map P.subtype ≤ P := by
        rintro _ ⟨n, -, rfl⟩; exact n.2
      have hCP : C'.map P.subtype ≤ P := by
        rintro _ ⟨n, -, rfl⟩; exact n.2
      refine ⟨?_, ?_⟩
      · rw [disjoint_iff]
        calc N.map P.subtype ⊓ (C'.map P.subtype ⊔ Q)
            = N.map P.subtype ⊓ (P ⊓ (C'.map P.subtype ⊔ Q)) := by
              rw [← inf_assoc, inf_eq_left.2 hNP]
          _ = N.map P.subtype ⊓ (C'.map P.subtype ⊔ P ⊓ Q) := by
              rw [inf_comm P, sup_inf_assoc_of_le _ hCP, inf_comm Q]
          _ = ⊥ := by
              rw [hc.inf_eq_bot, sup_bot_eq,
                ← Submodule.map_inf _ P.injective_subtype, hC'.inf_eq_bot, Submodule.map_bot]
      · rw [codisjoint_iff, ← sup_assoc, ← Submodule.map_sup, hC'.sup_eq_top,
          Submodule.map_subtype_top, hc.sup_eq_top]
    · ext x
      constructor
      · intro hx
        have hx' := hx
        rw [hcj, Set.mem_add] at hx'
        obtain ⟨a, ⟨haP, haW⟩, b, ⟨hbQ, hbW⟩, rfl⟩ := hx'
        have ha' : (⟨a, haP⟩ : P) ∈ P.subtype ⁻¹' W := haW
        rw [hCW', Set.mem_add] at ha'
        obtain ⟨n, ⟨hn, hnW⟩, c, ⟨hc', hcW⟩, hnc⟩ := ha'
        have hnc' : (n : E) + c = a := by rw [← Submodule.coe_add, hnc]
        refine ⟨n, ⟨⟨n, hn, rfl⟩, hnW⟩, c + b, ⟨?_, ?_⟩, by
          show (n : E) + ((c : E) + b) = a + b
          rw [← add_assoc, hnc']⟩
        · exact Submodule.add_mem_sup ⟨c, hc', rfl⟩ hbQ
        · rw [hcj]
          exact Set.add_mem_add ⟨c.2, hcW⟩ ⟨hbQ, hbW⟩
      · rintro ⟨a, ⟨⟨n, hn, rfl⟩, hnW⟩, y, ⟨hyC, hyW⟩, rfl⟩
        obtain ⟨c, ⟨c', hc', rfl⟩, q, hq, rfl⟩ := Submodule.mem_sup.1 hyC
        have hyW' := hyW
        rw [hcj, Set.mem_add] at hyW'
        obtain ⟨a, ⟨haP, haW⟩, b, ⟨hbQ, hbW⟩, hab⟩ := hyW'
        obtain ⟨e1, e2⟩ := eq_of_add_eq_add hc.disjoint haP c'.2 hbQ hq hab
        subst e1 e2
        have hm : n + c' ∈ P.subtype ⁻¹' W := by
          rw [hCW']; exact Set.add_mem_add ⟨hn, hnW⟩ ⟨hc', haW⟩
        rw [hcj]
        refine ⟨(n : E) + c', ⟨P.add_mem n.2 c'.2, hm⟩, b, ⟨hbQ, hbW⟩, ?_⟩
        simp only [Submodule.subtype_apply]
        abel
/-- A subspace of `P` is the image of its preimage in `↥P`. -/
theorem map_comap_subtype_eq {P M : Submodule ℝ E} (h : M ≤ P) :
    (M.comap P.subtype).map P.subtype = M :=
  Submodule.map_comap_eq_of_le (by rwa [Submodule.range_subtype])

/-- Simple distinguished subspaces inside a conjugate `P` are the simple distinguished
subspaces of `P ∩ W` read in `↥P`. -/
theorem estSimple_map_iff {W : Set E} {P Q : Submodule ℝ E} (hc : IsCompl P Q)
    (hcj : SontConjugues W P Q) (N : Submodule ℝ P) :
    EstSimple W (N.map P.subtype) ↔ EstSimple (P.subtype ⁻¹' W) N := by
  have hinj := Submodule.map_injective_of_injective P.injective_subtype
  constructor
  · rintro ⟨hD, hne, hmin⟩
    refine ⟨(estDistingue_map_iff hc hcj N).1 hD, fun h => hne (by rw [h, Submodule.map_bot]),
      fun M hM hM0 hMN => hinj ?_⟩
    refine hmin _ ((estDistingue_map_iff hc hcj M).2 hM) (fun h => hM0 (hinj ?_))
      (Submodule.map_mono hMN)
    rw [h, Submodule.map_bot]
  · rintro ⟨hD, hne, hmin⟩
    refine ⟨(estDistingue_map_iff hc hcj N).2 hD, fun h => hne (hinj (by rw [h, Submodule.map_bot])),
      fun M hM hM0 hMN => ?_⟩
    have hMP : M ≤ P := hMN.trans (Submodule.map_subtype_le P N)
    rw [← map_comap_subtype_eq hMP] at hM hM0 ⊢
    congr 1
    refine hmin _ ((estDistingue_map_iff hc hcj _).1 hM) (fun h => hM0 (by rw [h, Submodule.map_bot]))
      ?_
    rw [← map_comap_subtype_eq hMP] at hMN
    rwa [← Submodule.map_le_map_iff_of_injective P.injective_subtype]

/-- `P ∩ W`, read in `↥P`, satisfies the hypotheses of Théorème 2 when `W` does and `P` is one
half of a supplementary conjugate pair. -/
theorem hyps_preimage {W : Set E} (hW : Convex ℝ W) (h0 : (0 : E) ∈ W)
    (hspan : Submodule.span ℝ W = ⊤) (hd : ¬ ContientDroite W) {P Q : Submodule ℝ E}
    (hc : IsCompl P Q) (hcj : SontConjugues W P Q) :
    Convex ℝ (P.subtype ⁻¹' W) ∧ (0 : P) ∈ P.subtype ⁻¹' W ∧
      Submodule.span ℝ (P.subtype ⁻¹' W) = ⊤ ∧ ¬ ContientDroite (P.subtype ⁻¹' W) := by
  refine ⟨hW.linear_preimage P.subtype, by simpa using h0, ?_, ?_⟩
  · apply Submodule.map_injective_of_injective P.injective_subtype
    rw [Submodule.map_span, Submodule.map_subtype_top, Set.image_preimage_eq_inter_range]
    have h := span_inter_eq_of_conjugues hc.symm hcj.symm hspan
    have e : W ∩ range P.subtype = (P : Set E) ∩ W := by
      rw [Set.inter_comm]; congr 1; ext x; simp
    rw [e, h]
  · rintro ⟨x, v, hv, h⟩
    exact hd ⟨x, v, fun e => hv (Subtype.ext e), fun t => by simpa using h t⟩

/-- With `E = ⊕ Lᵢ`, `Lᵢ` and `⊕_{j ≠ i} Lⱼ` are supplementary. -/
theorem isCompl_iSup_ne {I : Type*} {L : I → Submodule ℝ E} (hind : iSupIndep L)
    (htop : ⨆ i, L i = ⊤) (i : I) : IsCompl (L i) (⨆ (j) (_ : j ≠ i), L j) :=
  ⟨iSupIndep_def.1 hind i, codisjoint_iff.2 (by rw [← iSup_split_single L i, htop])⟩

/-- If the `Lᵢ` (finitely many) are distinguished and span `E`, every simple distinguished
subspace lies in one of them. -/
theorem exists_le_of_estSimple {I : Type*} [Finite I] {W : Set E} (hW : Convex ℝ W)
    (h0 : (0 : E) ∈ W) (hspan : Submodule.span ℝ W = ⊤) (hd : ¬ ContientDroite W)
    {L : I → Submodule ℝ E} (htop : ⨆ i, L i = ⊤) (hL : ∀ i, EstDistingue W (L i))
    {s : Submodule ℝ E} (hs : EstSimple W s) : ∃ i, s ≤ L i := by
  by_contra hno
  push Not at hno
  have hbot : ∀ t ∈ Set.range L, s ⊓ t = ⊥ := by
    rintro _ ⟨i, rfl⟩
    by_contra hne
    obtain ⟨h1, h2⟩ := estDistingue_inf hW h0 hspan hd hs.1 (hL i)
    have := hs.2.2 _ ⟨_, h1, h2⟩ hne inf_le_left
    exact hno i (this ▸ inf_le_right)
  have := inf_sSup_eq_bot hW h0 hspan hd hs.1 (Set.finite_range L)
    (by rintro _ ⟨i, rfl⟩; exact hL i) hbot
  rw [sSup_range, htop, inf_top_eq] at this
  exact hs.2.1 this

/-- **The refinement, conjugate-pair form.** For `E = ⊕ Lᵢ` with every `(Lᵢ, ⊕_{j≠i} Lⱼ)` a
conjugate pair of `W`, the simple distinguished subspaces of `W` are those of the `Lᵢ ∩ W`, each
read in `↥Lᵢ` and pushed into `E`. -/
theorem simples_eq_iUnion {I : Type*} [Finite I] {W : Set E} (hW : Convex ℝ W)
    (h0 : (0 : E) ∈ W) (hspan : Submodule.span ℝ W = ⊤) (hd : ¬ ContientDroite W)
    {L : I → Submodule ℝ E} (hind : iSupIndep L) (htop : ⨆ i, L i = ⊤)
    (hcj : ∀ i, SontConjugues W (L i) (⨆ (j) (_ : j ≠ i), L j)) :
    simples W = ⋃ i, Submodule.map (L i).subtype '' simples ((L i).subtype ⁻¹' W) := by
  have hc := isCompl_iSup_ne hind htop
  ext s
  simp only [Set.mem_iUnion, Set.mem_image]
  constructor
  · intro hs
    obtain ⟨i, hi⟩ := exists_le_of_estSimple hW h0 hspan hd htop (fun i => ⟨_, hc i, hcj i⟩) hs
    refine ⟨i, s.comap (L i).subtype, ?_, map_comap_subtype_eq hi⟩
    have : EstSimple W ((s.comap (L i).subtype).map (L i).subtype) := by
      rw [map_comap_subtype_eq hi]; exact hs
    exact (estSimple_map_iff (hc i) (hcj i) _).1 this
  · rintro ⟨i, N, hN, rfl⟩
    exact (estSimple_map_iff (hc i) (hcj i) N).2 hN

/-- With `E = ⊕ Lᵢ` (independence), a family `yⱼ ∈ Lⱼ` whose sum lies in `⨆_{j ≠ k} Lⱼ` has
`y_k = 0`. -/
theorem eq_zero_of_sum_mem_iSup_ne {I : Type*} [Fintype I] {L : I → Submodule ℝ E}
    (hind : iSupIndep L) {y : I → E} (hy : ∀ j, y j ∈ L j) {k : I}
    (hk : ∑ j, y j ∈ ⨆ (j) (_ : j ≠ k), L j) : y k = 0 := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)] at hk
  have hrest : ∑ j ∈ Finset.univ.erase k, y j ∈ ⨆ (j) (_ : j ≠ k), L j :=
    Submodule.sum_mem _ fun j hj =>
      (le_iSup₂ (f := fun j (_ : j ≠ k) => L j) j (Finset.ne_of_mem_erase hj)) (hy j)
  have hyk : y k ∈ ⨆ (j) (_ : j ≠ k), L j := by
    have := Submodule.sub_mem _ hk hrest
    rwa [add_sub_cancel_right] at this
  exact (Submodule.disjoint_def.1 (iSupIndep_def.1 hind k)) _ (hy k) hyk

/-- Déf. 1 with `0 ∈ Vᵢ ⊆ Lᵢ` and `(Lᵢ)` independent: `Lᵢ ∩ W = Vᵢ`, and `(Lᵢ, ⊕_{j≠i} Lⱼ)` is
a conjugate pair of `W`. -/
theorem isSommeConvexes_inter_conjugues {I : Type*} [Fintype I] {W : Set E} {V : I → Set E}
    (hsum : IsSommeConvexes W V) {L : I → Submodule ℝ E} (hind : iSupIndep L)
    (hVL : ∀ i, V i ⊆ L i) (hV0 : ∀ i, (0 : E) ∈ V i) (i : I) :
    (L i : Set E) ∩ W = V i ∧ SontConjugues W (L i) (⨆ (j) (_ : j ≠ i), L j) := by
  classical
  obtain ⟨-, hbij⟩ := (isSommeConvexes_iff_bijOn W V).1 hsum
  have hsingle : ∀ v ∈ V i, Pi.single i v ∈ Set.univ.pi V := fun v hv j _ => by
    by_cases hj : j = i
    · subst hj; simpa using hv
    · rw [Pi.single_eq_of_ne hj]; exact hV0 j
  have hsum_single : ∀ v : E, ∑ j, (Pi.single i v : I → E) j = v := fun v => by
    simp
  have hVW : ∀ v ∈ V i, v ∈ W := fun v hv => by
    have := hbij.mapsTo (hsingle v hv)
    simpa only [hsum_single] using this
  have hinter : (L i : Set E) ∩ W = V i := by
    refine Set.Subset.antisymm ?_ fun v hv => ⟨hVL i hv, hVW v hv⟩
    rintro x ⟨hxL, hxW⟩
    obtain ⟨y, hy, rfl⟩ := hbij.surjOn hxW
    have hyL : ∀ j, y j ∈ L j := fun j => hVL j (hy j trivial)
    have hz : ∀ j, j ≠ i → y j = 0 := fun j hji =>
      eq_zero_of_sum_mem_iSup_ne hind hyL
        ((le_iSup₂ (f := fun k (_ : k ≠ j) => L k) i (Ne.symm hji)) hxL)
    show ∑ j, y j ∈ V i
    rw [Finset.sum_eq_single i (fun j _ hji => hz j hji) (by simp)]
    exact hy i trivial
  refine ⟨hinter, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := hbij.surjOn hx
    have hupd : Function.update y i 0 ∈ Set.univ.pi V := fun j _ => by
      by_cases hj : j = i
      · subst hj; simpa using hV0 j
      · rw [Function.update_of_ne hj]; exact hy j trivial
    have hsplit : y = Pi.single i (y i) + Function.update y i 0 := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
    refine ⟨y i, ⟨hVL i (hy i trivial), hVW _ (hy i trivial)⟩, ∑ j, Function.update y i 0 j,
      ⟨?_, hbij.mapsTo hupd⟩, ?_⟩
    · refine Submodule.sum_mem _ fun j _ => ?_
      by_cases hj : j = i
      · subst hj; simp
      · rw [Function.update_of_ne hj]
        exact (le_iSup₂ (f := fun k (_ : k ≠ i) => L k) j hj) (hVL j (hy j trivial))
    · conv_rhs => rw [hsplit]
      simp only [Pi.add_apply, Finset.sum_add_distrib, hsum_single]
  · rintro ⟨a, ha, b, ⟨hbM, hbW⟩, rfl⟩
    have haV : a ∈ V i := hinter ▸ ha
    obtain ⟨z, hz, rfl⟩ := hbij.surjOn hbW
    have hzi : z i = 0 := eq_zero_of_sum_mem_iSup_ne hind (fun j => hVL j (hz j trivial)) hbM
    have hmem : Pi.single i a + z ∈ Set.univ.pi V := fun j _ => by
      by_cases hj : j = i
      · subst hj; simpa [hzi] using haV
      · simpa [Pi.single_eq_of_ne hj] using hz j trivial
    have := hbij.mapsTo hmem
    simpa only [Pi.add_apply, Finset.sum_add_distrib, hsum_single] using this

/-- Under Déf. 1 with `Vᵢ ⊆ Lᵢ` and `W` spanning `E`, the `Lᵢ` span `E`. -/
theorem iSup_eq_top_of_isSommeConvexes {I : Type*} [Fintype I] {W : Set E} {V : I → Set E}
    (hsum : IsSommeConvexes W V) (hspan : Submodule.span ℝ W = ⊤) {L : I → Submodule ℝ E}
    (hVL : ∀ i, V i ⊆ L i) : ⨆ i, L i = ⊤ := by
  obtain ⟨-, hbij⟩ := (isSommeConvexes_iff_bijOn W V).1 hsum
  rw [eq_top_iff, ← hspan, Submodule.span_le]
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hbij.surjOn hx
  exact Submodule.sum_mem _ fun j _ => (le_iSup L j) (hVL j (hy j trivial))

/-- A sum of convexes containing `0` contains `0`. -/
theorem zero_mem_of_isSommeConvexes {I : Type*} [Fintype I] {W : Set E} {V : I → Set E}
    (hsum : IsSommeConvexes W V) (hV0 : ∀ i, (0 : E) ∈ V i) : (0 : E) ∈ W := by
  obtain ⟨-, hbij⟩ := (isSommeConvexes_iff_bijOn W V).1 hsum
  have := hbij.mapsTo (x := fun _ => (0 : E)) fun j _ => hV0 j
  simpa using this

/-- **The refinement, affine form** (Déf. 1). For `W = ∑ Vᵢ` spanning `E`, without line,
`0 ∈ Vᵢ ⊆ Lᵢ`, `(Lᵢ)` independent: every `Lᵢ` is distinguished with conjugate `⊕_{j≠i} Lⱼ`,
each `Vᵢ` read in `↥Lᵢ` satisfies the hypotheses of Théorème 2, the simple distinguished
subspaces of `W` are those of the `Vᵢ` read in `↥Lᵢ` and pushed into `E`, and each lies in exactly
one `Lᵢ`. -/
theorem simples_isSommeConvexes {I : Type*} [Fintype I] {W : Set E} {V : I → Set E}
    (hsum : IsSommeConvexes W V) (hspan : Submodule.span ℝ W = ⊤) (hd : ¬ ContientDroite W)
    {L : I → Submodule ℝ E} (hind : iSupIndep L)
    (hVL : ∀ i, V i ⊆ L i) (hV0 : ∀ i, (0 : E) ∈ V i) :
    (∀ i, EstDistingue W (L i) ∧ conjugue W (L i) = ⨆ (j) (_ : j ≠ i), L j) ∧
      (∀ i, Convex ℝ ((L i).subtype ⁻¹' V i) ∧ (0 : L i) ∈ (L i).subtype ⁻¹' V i ∧
        Submodule.span ℝ ((L i).subtype ⁻¹' V i) = ⊤ ∧
        ¬ ContientDroite ((L i).subtype ⁻¹' V i)) ∧
      simples W = ⋃ i, Submodule.map (L i).subtype '' simples ((L i).subtype ⁻¹' V i) ∧
      (∀ s ∈ simples W, ∃! i, s ≤ L i) := by
  have hW := hsum.1
  have h0 := zero_mem_of_isSommeConvexes hsum hV0
  have htop := iSup_eq_top_of_isSommeConvexes hsum hspan hVL
  have hc := isCompl_iSup_ne hind htop
  have hcj := fun i => (isSommeConvexes_inter_conjugues hsum hind hVL hV0 i).2
  have hpre : ∀ i, (L i).subtype ⁻¹' W = (L i).subtype ⁻¹' V i := fun i => by
    rw [← (isSommeConvexes_inter_conjugues hsum hind hVL hV0 i).1]
    ext x; simp
  have hD : ∀ i, EstDistingue W (L i) := fun i => ⟨_, hc i, hcj i⟩
  refine ⟨fun i => ⟨hD i, conjugue_eq hW h0 hspan hd (hc i) (hcj i)⟩,
    fun i => hpre i ▸ hyps_preimage hW h0 hspan hd (hc i) (hcj i), ?_, fun s hs => ?_⟩
  · rw [simples_eq_iUnion hW h0 hspan hd hind htop hcj]
    simp_rw [hpre]
  · obtain ⟨i, hi⟩ := exists_le_of_estSimple hW h0 hspan hd htop hD hs
    refine ⟨i, hi, fun j hj => ?_⟩
    by_contra hji
    have hle : L j ≤ ⨆ (k) (_ : k ≠ i), L k := le_iSup₂ (f := fun k (_ : k ≠ i) => L k) j hji
    exact hs.2.1 (le_bot_iff.1 ((hc i).disjoint.le_bot.trans' (le_inf hi (hj.trans hle))))

/-- In finite dimension, each `Lᵢ` of the affine refinement is the sum of the simple
distinguished subspaces of `W` it contains. -/
theorem sSup_simples_le_eq {I : Type*} [Fintype I] [FiniteDimensional ℝ E] {W : Set E}
    {V : I → Set E} (hsum : IsSommeConvexes W V) (hspan : Submodule.span ℝ W = ⊤)
    (hd : ¬ ContientDroite W) {L : I → Submodule ℝ E} (hind : iSupIndep L)
    (hVL : ∀ i, V i ⊆ L i) (hV0 : ∀ i, (0 : E) ∈ V i) (i : I) :
    sSup {s | s ∈ simples W ∧ s ≤ L i} = L i :=
  eq_sSup_simples_le hsum.1 (zero_mem_of_isSommeConvexes hsum hV0) hspan hd
    ((simples_isSommeConvexes hsum hspan hd hind hVL hV0).1 i).1

/-! ### Instance of the affine form: the cube `[−1, 1]ⁿ` as the sum of two coordinate faces -/

/-- **The affine refinement on the cube**: every hypothesis of `simples_isSommeConvexes` holds for
`[−1, 1]ⁿ = ([−1, 1]ⁿ ∩ ℝ^S) + ([−1, 1]ⁿ ∩ ℝ^{Sᶜ})`, any `S ⊆ Fin n`, with `ℝⁿ = ℝ^S ⊕ ℝ^{Sᶜ}`. -/
theorem cube_simples_isSommeConvexes {n : ℕ} (S : Set (Fin n)) :
    let L : Fin 2 → Submodule ℝ (Fin n → ℝ) := ![coord S, coord Sᶜ]
    let V : Fin 2 → Set (Fin n → ℝ) := ![(coord S : Set (Fin n → ℝ)) ∩ cube n,
      (coord Sᶜ : Set (Fin n → ℝ)) ∩ cube n]
    (∀ i, EstDistingue (cube n) (L i) ∧ conjugue (cube n) (L i) = ⨆ (j) (_ : j ≠ i), L j) ∧
      (∀ i, Convex ℝ ((L i).subtype ⁻¹' V i) ∧ (0 : L i) ∈ (L i).subtype ⁻¹' V i ∧
        Submodule.span ℝ ((L i).subtype ⁻¹' V i) = ⊤ ∧
        ¬ ContientDroite ((L i).subtype ⁻¹' V i)) ∧
      simples (cube n) = ⋃ i, Submodule.map (L i).subtype '' simples ((L i).subtype ⁻¹' V i) ∧
      (∀ s ∈ simples (cube n), ∃! i, s ≤ L i) := by
  intro L V
  obtain ⟨hW, h0, hspan, hdd⟩ := cube_hyps n
  have hsum : IsSommeConvexes (cube n) V :=
    (sontConjugues_iff_isSommeConvexes hW (isCompl_coord S)).1 (cube_sontConjugues S)
  have hind : iSupIndep L := by
    rw [iSupIndep_pair (i := 0) (j := 1) (by decide) (fun k => by fin_cases k <;> simp)]
    exact (isCompl_coord S).disjoint
  have hVL : ∀ i, V i ⊆ L i := fun i => by
    fin_cases i
    · exact Set.inter_subset_left
    · exact Set.inter_subset_left
  have hV0 : ∀ i, (0 : Fin n → ℝ) ∈ V i := fun i => by
    fin_cases i
    · exact ⟨(coord S).zero_mem, h0⟩
    · exact ⟨(coord Sᶜ).zero_mem, h0⟩
  exact simples_isSommeConvexes hsum hspan (fun h => hdd h.contientDemiDroite) hind hVL hV0

end SimplesSommeAffine

namespace Sphere
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Partial sums of a decomposition `x = ∑ yⱼ` of a point of `F(w)` lie in `K̄`. -/
theorem sum_subset_mem_closure_kPrime {I : Type*} [Fintype I] {w : Set (Sphere E)}
    {v : I → Set (Sphere E)} (hs : EstSommeS w v) {y : I → E} (hy : ∀ j, y j ∈ F (v j))
    (S : Finset I) : ∑ j ∈ S, y j ∈ closure (kPrime w) := by
  classical
  obtain ⟨-, hbij⟩ := (isSommeConvexes_iff_bijOn _ _).1 hs.2
  refine mem_closure_kPrime_of_add (a' := ∑ j ∈ Finset.univ.filter (· ∉ S), y j) fun s hs0 => ?_
  have hmem : (fun j => if j ∈ S then y j else s • y j) ∈ Set.univ.pi fun i => F (v i) :=
    fun j _ => by
      by_cases hj : j ∈ S
      · simpa [hj] using hy j
      · simpa [hj] using smul_mem_F (hy j) hs0
  have := hbij.mapsTo hmem
  rw [Finset.sum_ite, Finset.filter_mem_eq_inter, Finset.univ_inter] at this
  rwa [Finset.smul_sum]

/-- `v ⊆ s(L − O)` gives `F(v) ⊆ L`. -/
theorem F_subset_of_subset_linearSubvariety {L : Submodule ℝ E} {v : Set (Sphere E)}
    (h : v ⊆ linearSubvariety L) : F v ⊆ L := fun x hx => by
  have := F_mono h hx
  rw [F_linearSubvariety] at this
  exact this.1

/-- `v ⊆ s(L − O)` gives `K(v) = F(v) ∪ {O} ⊆ L`. -/
theorem kPrime_subset_of_subset_linearSubvariety {L : Submodule ℝ E} {v : Set (Sphere E)}
    (h : v ⊆ linearSubvariety L) : kPrime v ⊆ L := by
  rintro x (rfl | hx)
  · exact L.zero_mem
  · exact F_subset_of_subset_linearSubvariety h hx

/-- In a nonempty convex positive cone `C`, every vector of `span C` is a difference `a − b` of
two points of `C`. -/
theorem exists_sub_of_mem_span_cone {A : Set E} (hA : Convex ℝ A) (hpos : IsPosCone A)
    (hne : A.Nonempty) {x : E} (hx : x ∈ Submodule.span ℝ A) :
    ∃ a ∈ A, ∃ b ∈ A, x = a - b := by
  obtain ⟨p, hp⟩ := hne
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨y + p, add_mem_of_cone hA hpos hy hp, p, hp, by abel⟩
  | zero => exact ⟨p, hp, p, hp, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hy
    obtain ⟨a', ha', b', hb', rfl⟩ := hz
    exact ⟨a + a', add_mem_of_cone hA hpos ha ha', b + b', add_mem_of_cone hA hpos hb hb',
      by abel⟩
  | smul r y _ hy =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hy
    rcases lt_trichotomy r 0 with hr | rfl | hr
    · refine ⟨(-r) • b, hpos _ (neg_pos.2 hr) _ hb, (-r) • a, hpos _ (neg_pos.2 hr) _ ha, ?_⟩
      rw [smul_sub, neg_smul, neg_smul]; abel
    · exact ⟨p, hp, p, hp, by simp⟩
    · exact ⟨r • a, hpos _ hr _ ha, r • b, hpos _ hr _ hb, smul_sub r a b⟩

/-- **The supports of the summands of a sum are independent.** If `W` is the sum (Déf. 1) of
nonempty convex positive cones `Cᵢ`, the spans `span Cᵢ` are independent. -/
theorem iSupIndep_span_of_isSommeConvexes {I : Type*} [Fintype I] {W : Set E} {C : I → Set E}
    (hsum : IsSommeConvexes W C) (hpos : ∀ i, IsPosCone (C i)) (hne : ∀ i, (C i).Nonempty) :
    iSupIndep fun i => Submodule.span ℝ (C i) := by
  classical
  obtain ⟨hC, hbij⟩ := (isSommeConvexes_iff_bijOn W C).1 hsum
  refine iSupIndep_of_injOn fun f hf g hg hfg => ?_
  have hd : ∀ j, ∃ a ∈ C j, ∃ b ∈ C j, f j - g j = a - b := fun j =>
    exists_sub_of_mem_span_cone (hC j) (hpos j) (hne j)
      (Submodule.sub_mem _ (hf j) (hg j))
  choose a ha b hb hab using hd
  have hfg' : ∑ j, f j = ∑ j, g j := by
    rw [sommeF_apply_fintype, sommeF_apply_fintype] at hfg; exact hfg
  have hsumab : ∑ j, a j = ∑ j, b j := by
    have : ∑ j, (f j - g j) = 0 := by rw [Finset.sum_sub_distrib, hfg', sub_self]
    simp_rw [hab, Finset.sum_sub_distrib] at this
    exact sub_eq_zero.1 this
  have := hbij.injOn (x₁ := a) (x₂ := b) (fun j _ => ha j) (fun j _ => hb j) hsumab
  ext j
  have e := hab j
  rw [this, sub_self, sub_eq_zero] at e
  exact e

variable [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- For a sum `w = ∑ vᵢ` of support `S(E)` with `vᵢ ⊆ s(Lᵢ − O)`, the `Lᵢ` span `E`. -/
theorem iSup_eq_top_of_estSommeS {I : Type*} [Fintype I] {w : Set (Sphere E)}
    {v : I → Set (Sphere E)} (hsupp : supportK w = univ) (hs : EstSommeS w v)
    {L : I → Submodule ℝ E} (hvL : ∀ i, v i ⊆ linearSubvariety (L i)) : ⨆ i, L i = ⊤ :=
  iSup_eq_top_of_isSommeConvexes hs.2 (span_F_eq_top_of_supportK hsupp)
    fun i => F_subset_of_subset_linearSubvariety (hvL i)

/-- For a sum `w = ∑ vᵢ` (Déf. 5) with `vᵢ ⊆ s(Lᵢ − O)`, `(Lᵢ)` independent: the closed cone
`K̄(w)` meets `Lᵢ` in `K̄(vᵢ)`, and `(Lᵢ, ⊕_{j≠i} Lⱼ)` is a conjugate pair of `K̄(w)`. -/
theorem closure_kPrime_somme {I : Type*} [Fintype I] {w : Set (Sphere E)}
    {v : I → Set (Sphere E)} (hw : IsConvexPart w) (hsupp : supportK w = univ)
    (hs : EstSommeS w v) {L : I → Submodule ℝ E} (hind : iSupIndep L)
    (hvL : ∀ i, v i ⊆ linearSubvariety (L i)) (i : I) :
    (L i : Set E) ∩ closure (kPrime w) = closure (kPrime (v i)) ∧
      SontConjugues (closure (kPrime w)) (L i) (⨆ (j) (_ : j ≠ i), L j) := by
  classical
  obtain ⟨-, hbij⟩ := (isSommeConvexes_iff_bijOn _ _).1 hs.2
  have htop := iSup_eq_top_of_estSommeS hsupp hs hvL
  have hc := isCompl_iSup_ne hind htop i
  set M := ⨆ (j) (_ : j ≠ i), L j
  set π := (L i).projection M hc
  have hFL : ∀ j, F (v j) ⊆ L j := fun j => F_subset_of_subset_linearSubvariety (hvL j)
  -- `π (∑ yⱼ) = yᵢ`
  have hπsum : ∀ y : I → E, (∀ j, y j ∈ L j) → π (∑ j, y j) = y i := fun y hy => by
    rw [map_sum, Finset.sum_eq_single i (fun j _ hji => ?_) (by simp),
      Submodule.projection_apply_of_mem_left hc (hy i)]
    exact Submodule.projection_apply_of_mem_right hc
      ((le_iSup₂ (f := fun k (_ : k ≠ i) => L k) j hji) (hy j))
  -- `F(vᵢ) ⊆ K̄`
  have hFvK : F (v i) ⊆ closure (kPrime w) := by
    intro c hcF
    have hFne : (F w).Nonempty := by
      by_contra hne
      rw [Set.not_nonempty_iff_eq_empty] at hne
      have h1 := span_F_eq_top_of_supportK hsupp
      rw [hne, Submodule.span_empty] at h1
      have : c ∈ (⊥ : Submodule ℝ E) := h1 ▸ Submodule.mem_top
      exact zero_notMem_F _ ((Submodule.mem_bot ℝ).1 this ▸ hcF)
    obtain ⟨x, hx⟩ := hFne
    obtain ⟨y, hy, -⟩ := hbij.surjOn hx
    have hy' : ∀ j, Function.update y i c j ∈ F (v j) := fun j => by
      by_cases hj : j = i
      · subst hj; simpa using hcF
      · rw [Function.update_of_ne hj]; exact hy j trivial
    have := sum_subset_mem_closure_kPrime hs hy' {i}
    simpa using this
  have hvK : closure (kPrime (v i)) ⊆ closure (kPrime w) := by
    refine closure_minimal ?_ isClosed_closure
    rintro x (rfl | hx)
    · exact zero_mem_closure_kPrime w
    · exact hFvK hx
  have hπK : ∀ x ∈ kPrime w, π x ∈ closure (kPrime (v i)) := by
    rintro x (rfl | hx)
    · rw [map_zero]; exact zero_mem_closure_kPrime _
    · obtain ⟨y, hy, rfl⟩ := hbij.surjOn hx
      rw [show (fun x : I → E => ∑ j, x j) y = ∑ j, y j from rfl,
        hπsum y fun j => hFL j (hy j trivial)]
      exact subset_closure (subset_insert _ _ (hy i trivial))
  refine ⟨Set.Subset.antisymm ?_ fun x hx => ⟨?_, hvK hx⟩, ?_⟩
  · rintro x ⟨hxL, hxK⟩
    have := map_mem_closure (LinearMap.continuous_of_finiteDimensional π) hxK hπK
    rwa [Submodule.projection_apply_of_mem_left hc hxL, closure_closure] at this
  · have hcl : IsClosed (L i : Set E) := Submodule.closed_of_finiteDimensional _
    exact closure_minimal (kPrime_subset_of_subset_linearSubvariety (hvL i)) hcl hx
  · ext x
    constructor
    · intro hx
      have h1 : π x ∈ closure (kPrime w) :=
        projection_mapsTo_closure hc (fun z hz => hvK (hπK z hz)) hx
      have h2 : M.projection (L i) hc.symm x ∈ closure (kPrime w) := by
        refine projection_mapsTo_closure hc.symm (fun z hz => ?_) hx
        rcases hz with rfl | hz
        · rw [map_zero]; exact zero_mem_closure_kPrime w
        · obtain ⟨y, hy, rfl⟩ := hbij.surjOn hz
          rw [Submodule.projection_eq_self_sub_projection hc,
            show (fun x : I → E => ∑ j, x j) y = ∑ j, y j from rfl,
            hπsum y fun j => hFL j (hy j trivial), ← Finset.sum_erase_eq_sub (Finset.mem_univ i)]
          exact sum_subset_mem_closure_kPrime hs (fun j => hy j trivial) _
      exact ⟨π x, ⟨Submodule.projection_apply_mem _ _, h1⟩, _,
        ⟨Submodule.projection_apply_mem _ _, h2⟩, Submodule.projection_add_projection_eq_self hc x⟩
    · rintro ⟨a, ⟨-, ha⟩, b, ⟨-, hb⟩, rfl⟩
      exact add_mem_closure_kPrime hw ha hb

/-- **The refinement step** of the Corollary of Prop. 5. For `w` open convex, of support `S(E)`,
empty noyau, no line in `F(w)`, the sum (Déf. 5) of convexes `vᵢ ⊆ s(Lᵢ − O)` with `(Lᵢ)`
independent: every `s(Lᵢ − O)` is distinguished, the simple distinguished subvarieties of `w`
are those of the `K̄(vᵢ)` read in `↥Lᵢ` and pushed into `E`, each lies in exactly one `Lᵢ`, and
each `Lᵢ` is the sum of the simple ones it contains. -/
theorem simplesS_somme {I : Type*} [Fintype I] {w : Set (Sphere E)} {v : I → Set (Sphere E)}
    (hw : IsConvexPart w) (hopen : IsOpen w) (hsupp : supportK w = univ) (hn : noyau w = ∅)
    (hd : ¬ ContientDroite (F w)) (hs : EstSommeS w v) {L : I → Submodule ℝ E}
    (hind : iSupIndep L) (hvL : ∀ i, v i ⊆ linearSubvariety (L i)) :
    (∀ i, EstDistingueS w (L i)) ∧
      simplesS w = ⋃ i, Submodule.map (L i).subtype ''
        simples ((L i).subtype ⁻¹' closure (kPrime (v i))) ∧
      (∀ s ∈ simplesS w, ∃! i, s ≤ L i) ∧
      (∀ i, sSup {s | s ∈ simplesS w ∧ s ≤ L i} = L i) := by
  have hdK := not_contientDroite_closure hw hopen hn hd
  have hK := (convex_kPrime hw).closure
  have h0 := zero_mem_closure_kPrime w
  have hspan := span_closure_kPrime hsupp
  have htop := iSup_eq_top_of_estSommeS hsupp hs hvL
  have hc := isCompl_iSup_ne hind htop
  have hcj := fun i => (closure_kPrime_somme hw hsupp hs hind hvL i).2
  have hpre : ∀ i, (L i).subtype ⁻¹' closure (kPrime w) =
      (L i).subtype ⁻¹' closure (kPrime (v i)) := fun i => by
    rw [← (closure_kPrime_somme hw hsupp hs hind hvL i).1]
    ext x; simp
  have hD : ∀ i, EstDistingue (closure (kPrime w)) (L i) := fun i => ⟨_, hc i, hcj i⟩
  have hS := simplesS_eq hw hopen hsupp hdK
  refine ⟨fun i => (estDistingueS_iff_affine hw hopen hsupp hdK).2 (hD i), ?_,
    fun s hs' => ?_, fun i => ?_⟩
  · rw [hS, simples_eq_iUnion hK h0 hspan hdK hind htop hcj]
    simp_rw [hpre]
  · rw [hS] at hs'
    obtain ⟨i, hi⟩ := exists_le_of_estSimple hK h0 hspan hdK htop hD hs'
    refine ⟨i, hi, fun j hj => ?_⟩
    by_contra hji
    have hle : L j ≤ ⨆ (k) (_ : k ≠ i), L k := le_iSup₂ (f := fun k (_ : k ≠ i) => L k) j hji
    exact hs'.2.1 (le_bot_iff.1 ((hc i).disjoint.le_bot.trans' (le_inf hi (hj.trans hle))))
  · rw [hS]
    exact eq_sSup_simples_le hK h0 hspan hdK (hD i)

omit [FiniteDimensional ℝ E] in
/-- The supports `lᵢ = s(span F(vᵢ) − O)` of the summands of a sum `w` (Déf. 5) of support `S(E)`
are independent. -/
theorem iSupIndep_supports {I : Type*} [Fintype I] {w : Set (Sphere E)} {v : I → Set (Sphere E)}
    (hsupp : supportK w = univ) (hs : EstSommeS w v) :
    iSupIndep fun i => Submodule.span ℝ (F (v i)) := by
  obtain ⟨-, hbij⟩ := (isSommeConvexes_iff_bijOn _ _).1 hs.2
  rcases (F w).eq_empty_or_nonempty with hF | ⟨x, hx⟩
  · have h1 := span_F_eq_top_of_supportK hsupp
    rw [hF, Submodule.span_empty] at h1
    intro i
    have : Submodule.span ℝ (F (v i)) = ⊥ := eq_bot_iff.2 (h1 ▸ le_top)
    show Disjoint (Submodule.span ℝ (F (v i))) _
    rw [this]
    exact disjoint_bot_left
  · obtain ⟨y, hy, -⟩ := hbij.surjOn hx
    exact iSupIndep_span_of_isSommeConvexes hs.2 (fun i => isPosCone_F _)
      fun i => ⟨y i, hy i trivial⟩

/-- **The refinement step, intrinsic form** (towards « On se ramène à une décomposition de `w` en
somme de convexes contenus dans des variétés distinguées simples »; this proves the refinement
step only, not that decomposition of `w` into convexes contained in simple distinguished
subvarieties, which is left to T-bz-c3-balayable-somme-cor): for any sum `w = ∑ vᵢ` (Déf. 5),
with `lᵢ = s(Lᵢ − O)` the supports of the `vᵢ`, `Lᵢ = span F(vᵢ)`, every `lᵢ` is distinguished,
`E = ⊕ Lᵢ`, every simple distinguished subvariety of `w` lies in exactly one `lᵢ`, each `Lᵢ` is
the sum of the simple ones it contains, and the simple ones of `w` are those of the `vᵢ` read in
their own `Lᵢ`. -/
theorem simplesS_somme_supports {I : Type*} [Fintype I] {w : Set (Sphere E)}
    {v : I → Set (Sphere E)} (hw : IsConvexPart w) (hopen : IsOpen w)
    (hsupp : supportK w = univ) (hn : noyau w = ∅) (hd : ¬ ContientDroite (F w))
    (hs : EstSommeS w v) :
    iSupIndep (fun i => Submodule.span ℝ (F (v i))) ∧ (⨆ i, Submodule.span ℝ (F (v i)) = ⊤) ∧
      (∀ i, EstDistingueS w (Submodule.span ℝ (F (v i)))) ∧
      simplesS w = ⋃ i, Submodule.map (Submodule.span ℝ (F (v i))).subtype ''
        simples ((Submodule.span ℝ (F (v i))).subtype ⁻¹' closure (kPrime (v i))) ∧
      (∀ s ∈ simplesS w, ∃! i, s ≤ Submodule.span ℝ (F (v i))) ∧
      (∀ i, sSup {s | s ∈ simplesS w ∧ s ≤ Submodule.span ℝ (F (v i))} =
        Submodule.span ℝ (F (v i))) := by
  have hind := iSupIndep_supports hsupp hs
  have hvL : ∀ i, v i ⊆ linearSubvariety (Submodule.span ℝ (F (v i))) := fun i =>
    subset_supportK (v i)
  exact ⟨hind, iSup_eq_top_of_estSommeS hsupp hs hvL,
    simplesS_somme hw hopen hsupp hn hd hs hind hvL⟩

end Sphere

/-! ### Instance: the open `3`-simplex as the sum of two open edges -/

namespace SimplesSommeInstance

open Sphere BooleProjectifInstance

/-- `ℝ⁴`. -/
abbrev V4 : Type := Fin 4 → ℝ

/-- The coordinate plane `{x₂ = x₃ = 0} = ⟨e₀, e₁⟩`. -/
def P01 : Submodule ℝ V4 where
  carrier := {x | x 2 = 0 ∧ x 3 = 0}
  add_mem' hx hy := ⟨by simp [hx.1, hy.1], by simp [hx.2, hy.2]⟩
  zero_mem' := ⟨rfl, rfl⟩
  smul_mem' c x hx := ⟨by simp [hx.1], by simp [hx.2]⟩

/-- The coordinate plane `{x₀ = x₁ = 0} = ⟨e₂, e₃⟩`. -/
def P23 : Submodule ℝ V4 where
  carrier := {x | x 0 = 0 ∧ x 1 = 0}
  add_mem' hx hy := ⟨by simp [hx.1, hy.1], by simp [hx.2, hy.2]⟩
  zero_mem' := ⟨rfl, rfl⟩
  smul_mem' c x hx := ⟨by simp [hx.1], by simp [hx.2]⟩

/-- The open positive quadrant of `⟨e₀, e₁⟩`. -/
def Q01 : Set V4 := {x | 0 < x 0 ∧ 0 < x 1 ∧ x 2 = 0 ∧ x 3 = 0}

/-- The open positive quadrant of `⟨e₂, e₃⟩`. -/
def Q23 : Set V4 := {x | x 0 = 0 ∧ x 1 = 0 ∧ 0 < x 2 ∧ 0 < x 3}

/-- The two planes. -/
def Lp : Fin 2 → Submodule ℝ V4 := ![P01, P23]

/-- The two open edges `s(Q₀₁)`, `s(Q₂₃)` of the open `3`-simplex. -/
def edges : Fin 2 → Set (S 3) := ![ofCone Q01, ofCone Q23]

/-- `Q₀₁` is a positive cone. -/
theorem pos_Q01 : IsPosCone Q01 := fun c hc x hx =>
  ⟨by simpa using mul_pos hc hx.1, by simpa using mul_pos hc hx.2.1, by simp [hx.2.2.1],
    by simp [hx.2.2.2]⟩

/-- `Q₂₃` is a positive cone. -/
theorem pos_Q23 : IsPosCone Q23 := fun c hc x hx =>
  ⟨by simp [hx.1], by simp [hx.2.1], by simpa using mul_pos hc hx.2.2.1,
    by simpa using mul_pos hc hx.2.2.2⟩

/-- `F` of the two edges. -/
theorem F_edges (i : Fin 2) : F (edges i) = ![Q01, Q23] i := by
  fin_cases i
  · exact F_ofCone_of_zero_notMem pos_Q01 fun h => lt_irrefl _ h.1
  · exact F_ofCone_of_zero_notMem pos_Q23 fun h => lt_irrefl _ h.2.2.1

/-- `Q₀₁` is convex. -/
theorem convex_Q01 : Convex ℝ Q01 := fun x hx y hy a b ha hb hab => by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  · rcases ha.lt_or_eq with ha' | rfl
    · nlinarith [hx.1, hy.1]
    · simp at hab; subst hab; simpa using hy.1
  · rcases ha.lt_or_eq with ha' | rfl
    · nlinarith [hx.2.1, hy.2.1]
    · simp at hab; subst hab; simpa using hy.2.1
  · rw [hx.2.2.1, hy.2.2.1]; ring
  · rw [hx.2.2.2, hy.2.2.2]; ring

/-- `Q₂₃` is convex. -/
theorem convex_Q23 : Convex ℝ Q23 := fun x hx y hy a b ha hb hab => by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  · rw [hx.1, hy.1]; ring
  · rw [hx.2.1, hy.2.1]; ring
  · rcases ha.lt_or_eq with ha' | rfl
    · nlinarith [hx.2.2.1, hy.2.2.1]
    · simp at hab; subst hab; simpa using hy.2.2.1
  · rcases ha.lt_or_eq with ha' | rfl
    · nlinarith [hx.2.2.2, hy.2.2.2]
    · simp at hab; subst hab; simpa using hy.2.2.2

/-- **Déf. 5 holds**: the open `3`-simplex is the sum of its two open edges `s(Q₀₁)`, `s(Q₂₃)`. -/
theorem simplexO_estSommeS_edges : EstSommeS (simplexO 3) edges := by
  have hconv : ∀ i, Convex ℝ (F (edges i)) := fun i => by
    rw [F_edges]; fin_cases i
    · exact convex_Q01
    · exact convex_Q23
  refine ⟨hconv, (isSommeConvexes_iff_bijOn _ _).2 ⟨hconv, ?_, ?_, ?_⟩⟩
  · intro x hx
    have h0 : x 0 ∈ Q01 := by simpa [F_edges] using hx 0 trivial
    have h1 : x 1 ∈ Q23 := by simpa [F_edges] using hx 1 trivial
    rw [F_simplexO]
    intro k
    simp only [Fin.sum_univ_two, Pi.add_apply]
    fin_cases k
    · simp [h1.1, h0.1]
    · simp [h1.2.1, h0.2.1]
    · simp [h0.2.2.1, h1.2.2.1]
    · simp [h0.2.2.2, h1.2.2.2]
  · intro x hx y hy hxy
    have hx0 : x 0 ∈ Q01 := by simpa [F_edges] using hx 0 trivial
    have hx1 : x 1 ∈ Q23 := by simpa [F_edges] using hx 1 trivial
    have hy0 : y 0 ∈ Q01 := by simpa [F_edges] using hy 0 trivial
    have hy1 : y 1 ∈ Q23 := by simpa [F_edges] using hy 1 trivial
    simp only [Fin.sum_univ_two] at hxy
    have e : ∀ k, x 0 k + x 1 k = y 0 k + y 1 k := fun k => congrFun hxy k
    funext i k
    fin_cases i <;> fin_cases k
    · have := e 0; simp [hx1.1, hy1.1] at this; simpa using this
    · have := e 1; simp [hx1.2.1, hy1.2.1] at this; simpa using this
    · simp [hx0.2.2.1, hy0.2.2.1]
    · simp [hx0.2.2.2, hy0.2.2.2]
    · simp [hx1.1, hy1.1]
    · simp [hx1.2.1, hy1.2.1]
    · have := e 2; simp [hx0.2.2.1, hy0.2.2.1] at this; simpa using this
    · have := e 3; simp [hx0.2.2.2, hy0.2.2.2] at this; simpa using this
  · intro z hz
    rw [F_simplexO] at hz
    refine ⟨![![z 0, z 1, 0, 0], ![0, 0, z 2, z 3]], fun i _ => ?_, ?_⟩
    · show _ ∈ F (edges i)
      rw [F_edges]
      fin_cases i
      · exact ⟨by simpa using hz 0, by simpa using hz 1, rfl, rfl⟩
      · exact ⟨rfl, rfl, by simpa using hz 2, by simpa using hz 3⟩
    · funext k
      simp only [Fin.sum_univ_two]
      fin_cases k <;> simp

/-- Each edge lies in its plane. -/
theorem edges_subset (i : Fin 2) : edges i ⊆ linearSubvariety (Lp i) := by
  fin_cases i
  · exact ofCone_subset_ofCone fun x hx => ⟨hx.2.2.1, hx.2.2.2⟩
  · exact ofCone_subset_ofCone fun x hx => ⟨hx.1, hx.2.1⟩

/-- `ℝ⁴ = ⟨e₀, e₁⟩ ⊕ ⟨e₂, e₃⟩`: the two planes are independent. -/
theorem iSupIndep_Lp : iSupIndep Lp := by
  rw [iSupIndep_pair (i := 0) (j := 1) (by decide) (fun k => by fin_cases k <;> simp)]
  rw [Submodule.disjoint_def]
  intro x hx hy
  have h1 : x 2 = 0 ∧ x 3 = 0 := hx
  have h2 : x 0 = 0 ∧ x 1 = 0 := hy
  funext k
  fin_cases k
  · exact h2.1
  · exact h2.2
  · exact h1.1
  · exact h1.2

/-- **The refinement step on the instance**: every hypothesis of `simplesS_somme` holds for the
open `3`-simplex and its two open edges, so its simple distinguished subvarieties are those of the
two edges, each read in its plane, every plane is distinguished, and every simple one lies in
exactly one plane. -/
theorem simplexO_simplesS_somme :
    (∀ i, EstDistingueS (simplexO 3) (Lp i)) ∧
      simplesS (simplexO 3) = ⋃ i, Submodule.map (Lp i).subtype ''
        simples ((Lp i).subtype ⁻¹' closure (kPrime (edges i))) ∧
      (∀ s ∈ simplesS (simplexO 3), ∃! i, s ≤ Lp i) ∧
      (∀ i, sSup {s | s ∈ simplesS (simplexO 3) ∧ s ≤ Lp i} = Lp i) := by
  obtain ⟨hw, hopen, hsupp, hn, hd⟩ := simplexO_hyps (n := 3)
  exact simplesS_somme hw hopen hsupp hn hd simplexO_estSommeS_edges iSupIndep_Lp edges_subset

/-- The four simple distinguished subvarieties of the open `3`-simplex split two and two between
the planes: the simple ones read in `⟨e₀, e₁⟩` and in `⟨e₂, e₃⟩` are, pushed into `ℝ⁴`, sets of
total cardinal `4`. -/
theorem simplexO_simplesS_somme_ncard :
    (⋃ i, Submodule.map (Lp i).subtype ''
        simples ((Lp i).subtype ⁻¹' closure (kPrime (edges i)))).ncard = 4 := by
  rw [← simplexO_simplesS_somme.2.1, simplexO_simplesS_ncard]

end SimplesSommeInstance

end Benzecri
