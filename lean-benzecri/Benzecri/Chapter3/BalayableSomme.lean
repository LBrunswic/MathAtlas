import Benzecri.Chapter3.BooleProjectif
import Benzecri.Chapter2.Mesure
import Benzecri.Chapter2.CasAffin

/-!
# Chapter 3 § 2, Proposition 4: an open convex of `S(n)` with empty noyau is the sum of its simple summands, and its projective automorphisms are compatible

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 3 § 2, journal p. 268; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch3.tex` (TO BE CHECKED BY THE AUTHOR).
Target T-bz-c3-balayable-somme.

* `bzprop:c3s2p4_automorphisme_compatible` — `benzecri1960_ch3.tex:599` (Prop. 4, l.599–611),
  NOT marked (partial; see SCOPE). Proved, under the corrected hypotheses of
  `corollaire_algebre_parties_projective` (`¬ ContientDroite (F w)`, OQ-168) and `w` nonempty:
  `Benzecri.Sphere.prop4_somme` (first assertion, intrinsic: the simple distinguished
  subvarieties are finitely many, `1 ≤ p ≤ n + 1`, and for every enumeration `l₁, …, l_p` of them
  `w` is the sum, Déf. 5, of the `vᵢ = composanteS w lᵢ = s(P_{lᵢ}(F(w)))`, each a nonempty
  convex part of support `lᵢ`, open in `lᵢ`, and these are the only convexes of the `lᵢ` of which
  `w` is the sum); `Benzecri.Sphere.prop4_permute` (the printed proof: a linear automorphism
  preserving `w` permutes the simple ones and their summands); `Benzecri.Sphere.prop4_gxAut`
  (« un automorphisme projectif de `w` est un élément de `GP(n, ℝ)` »);
  `Benzecri.Sphere.prop4_automorphisme_compatible` (second assertion in the coordinates of `w`:
  Ch. 1 § 3 Déf. 2's formula `m′ᵢ = φᵢ m_{τ(i)}`, `φᵢ = g`, `t = 1`, without `GU`-normalisation).
  The Chapter 1 form (`w ≅ PiBase`, the transported automorphisms `IsCompatiblePi`) is
  `Benzecri.Sphere.prop4_produit` in the separate scaffold file
  `BenzecriScaffold/Chapter3/BalayableSommeProduit.lean`, stated on one tagged `sorry`; this file
  has none. Refuted as printed:
  `Benzecri.BooleProjectifInstance.not_prop4_simplesS_finite` (the open quarter of `S(2)` has
  infinitely many simple distinguished subvarieties).

Instances: the open `n`-simplex (`simplexO_hyps4`, `p = n + 1`; `simplexO_prop4`, the sum over an
enumeration of its `n + 1` simple ones) and the open round cap (`capS_hyps4`, `p = 1`, the only
simple one `S(2)`) satisfy every hypothesis of `prop4_somme` / `prop4_permute`.

> **Proposition 4.** Soient $w$ un ouvert convexe de $S(\R^{n+1})=S(n)$, de noyau vide, $l_i$
> les $p$ sous-variétés distinguées simples relatives à $w$, $v_i$ les convexes de $l_i$ dont
> $w$ est la somme; on peut écrire avec les notations du chapitre 1, paragraphes 1 et 2
> $$ w=F^{-1}(F(v_1)\times\ldots\times F(v_p)) $$
> tout automorphisme projectif de $w$ est un automorphisme compatible au sens du chapitre 1,
> paragraphe 3, définition 2.
>
> En effet, un automorphisme projectif de $w$ est un élément de $GP(n, \R)$ qui permute entre
> elles les variétés distinguées simples.

## The proof formalized

*The decomposition* (`prop4_somme`). On the closed cone `K̄ = closure (insert O F(w))` the affine
Corollary of Th. 2 applies (`not_contientDroite_closure`, `simplesS_eq`): the simple ones are
finitely many, `∑ S = E`, and for every `T ⊆ S`, `(∑ T, ∑ (S ∖ T))` is a supplementary conjugate
pair of Déf. 6 (`conj_sSup`: the conjugate of `∑ T` contains every simple `s ∉ T` by
distributivity, `inf_sup_le_of_estDistingue`). A conjugate pair mixes: `P_L x + P_{L′} y ∈ F(w)`
for `x, y ∈ F(w)` (`mix_of_conj`, from the cone form `estConjugueS_iff`). With `Pᵢ` the
projection on `lᵢ` along the sum of the others (`projS`), `Q_T = ∑_{i ∈ T} Pᵢ` is the projection
on `∑ T` along `∑ Tᶜ`, and an induction on `T` gives `∑ Pᵢ xᵢ ∈ F(w)` for `xᵢ ∈ F(w)`
(`sum_mem`); with `x = ∑ Pᵢ x` this makes `(xᵢ) ↦ ∑ xᵢ` a bijection of `∏ Pᵢ(F(w))` onto `F(w)`.
`Pᵢ(F(w))` is convex (`F(w)` is: `neg_notMem`, a pair `±x` in the open `F(w)` would make
`insert O F(w)` everything), avoids `O` (`projection_ne_zero`), spans `lᵢ` and is open in `lᵢ`
(`projectionOnto` is an open map). Uniqueness: `Pᵢ(∑ xⱼ) = xᵢ` for `xⱼ ∈ lⱼ` (`projS_sum`).

*The automorphisms* (`prop4_permute`, `prop4_gxAut`). A linear `g` with `g(w) = w` maps `F(w)`
onto itself, hence `ConeDec`s to `ConeDec`s (`estConjugueS_map`), distinguished to
distinguished, simple to simple (`estSimpleS_map`, with `g⁻¹`); `σ(L) = g⁻¹(L)` and
`g ∘ P_{σ(L)} = P_L ∘ g` (checked on each simple). A projective automorphism `f` of `w` is, on the
connected `w` (`isPreconnected`, `F(w)` convex), one element of `GS(n)`
(`exists_smul_eq_on_of_isPreconnected` with the inclusion chart and `trans_aut`); its inverse
too, and rigidity (`GSE.eq_one_of_eqOn`) makes the lift preserve `w`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `w` ouvert de `S(n)` | ✓ `IsOpen w` (`w : Opens (S m)` for the automorphisms) |
| `w` convexe | ✓ `IsConvexPart w` |
| `w` de noyau vide | ✓ `noyau w = ∅` |
| (not printed) `F(w)` contains no line | ⚠ ADDED (OQ-168): `¬ ContientDroite (F w)`; without it the statement is false (`not_prop4_simplesS_finite`) |
| (not printed) `w ≠ ∅` | ⚠ reading: `w.Nonempty` (for `w = ∅`, `p = 0` and `w` is not the empty sum, `simplesS_empty_and_not_estSommeS`) |
| `S(n)` of `ℝ^{n+1}` | ✓ for the decomposition, any finite-dimensional real normed `E` (stronger); `Fin (m + 1) → ℝ` for the automorphisms |
| « les `p` sous-variétés distinguées simples » | ✓ `simplesS w`, finite, `1 ≤ p ≤ n + 1`, any enumeration `Fin p ≃ simplesS w` |
| « `vᵢ` les convexes de `lᵢ` dont `w` est la somme » | ✓ `composanteS w lᵢ`, Déf. 5's `EstSommeS`, and uniqueness among convexes `⊆ lᵢ` |
| « `w = F⁻¹(F(v₁) × … × F(v_p))` » (Ch. 1 notation) | ✗ not here: stated only in `BalayableSommeProduit.lean` (`prop4_produit`, `sorry`); proved intrinsically (`prop4_somme`) |
| « tout automorphisme projectif » | ✓ `GXAut (GSR m) (S m) w` |
| « compatible au sens du ch. 1 § 3 Déf. 2 » | ⚠ reading: in `w`'s coordinates only (`prop4_automorphisme_compatible`: `g` permutes the `lᵢ` and the `F(vᵢ)`; the `φᵢ = g|F(v_{τ(i)})` are linear, not `GU`-normalised, no `PiBase` isomorphism), weaker than Déf. 2; ✗ as `IsCompatiblePi` on `PiBase`, stated only in `BalayableSommeProduit.lean` (`prop4_produit`) |

## SCOPE (disclosed)

* **Not marked.** Two reasons, each sufficient. (1) The printed statement is false
  (`not_prop4_simplesS_finite`: the open quarter `{y > 0, z > 0}` of `S(2)` is a nonempty open
  convex of empty noyau with infinitely many simple distinguished subvarieties, the pairs
  `{±(t e₁ + e₂)}`), so the Lean adds `¬ ContientDroite (F w)`, the hypothesis of
  `corollaire_algebre_parties_projective`; which corrected form is of record is OQ-168 (OPEN),
  so the mark waits on it (the pattern of T-bz-c3-conjugues on OQ-163). (2) The Chapter 1 form
  (`prop4_produit`, in `BalayableSommeProduit.lean`) rests on a tagged `sorry`: the transport to
  `PiBase` (global cone charts of
  `FCone` over open subsets of `S(nᵢ)`, the base chart of the product chart, the cast
  `pdim n = m`, and the normalisation `|det φᵢ| = 1` — the cone groupoid is `GU` — absorbed by the
  torus element `t`).
* **Readings.** « `w = F⁻¹(F(v₁) × … × F(v_p))` » is read (dispatch reading (2)) as a projective
  isomorphism `PiBase n B ≃ₜ w` with `Bᵢ = s(bᵢ(F(vᵢ)))` open in `S(nᵢ)` through bases
  `bᵢ : lᵢ ≅ ℝ^{nᵢ+1}` (`prop4_produit`, `BalayableSommeProduit.lean`); its mathematical content, `F(w) = F(v₁) + … + F(v_p)` as a direct sum, is
  `prop4_somme`. « automorphisme projectif de `w` » is `GXAut (GSR m) (S m) w`. « compatible »
  in `w`'s coordinates is: `g(l_{τ(i)}) = lᵢ` and `g(F(v_{τ(i)})) = F(vᵢ)` (Déf. 2 with
  `φᵢ = g|F(v_{τ(i)})`, `t = 1`, not `GU`-normalised). `w ≠ ∅` is read into
  « ouvert convexe ».
* **`n = 0`** is covered: `w` a point of `S(0)`, `p = 1`, `l₁ = S(0)`.
* The decomposition is proved for every finite-dimensional real normed `E` (stronger than
  `S(ℝ^{n+1})`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open Set Function Filter Topology
open scoped Pointwise

namespace Benzecri

namespace Sphere

section Prop4

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The sum of the simple distinguished subvarieties of `w` other than `L`. -/
noncomputable def autresS (w : Set (Sphere E)) (L : Submodule ℝ E) : Submodule ℝ E :=
  sSup (simplesS w \ {L})

open Classical in
/-- The projection `P_L` on a simple distinguished `L` along the sum of the other simple ones. -/
noncomputable def projS (w : Set (Sphere E)) (L : Submodule ℝ E) : E →ₗ[ℝ] E :=
  if h : IsCompl L (autresS w L) then L.projection (autresS w L) h else 0

/-- The cone `P_L(F(w))` of the summand of `w` in `L`. -/
def sommandeS (w : Set (Sphere E)) (L : Submodule ℝ E) : Set E := projS w L '' F w

/-- **`vᵢ`, the convex of `lᵢ` of which (with the others) `w` is the sum**: `s(P_L(F(w)))`. -/
def composanteS (w : Set (Sphere E)) (L : Submodule ℝ E) : Set (Sphere E) :=
  ofCone (sommandeS w L)


/-- The hypotheses of Prop. 4, as used (`w` nonempty: see SCOPE). -/
structure Hyps4 (w : Set (Sphere E)) : Prop where
  convex : IsConvexPart w
  isOpen : IsOpen w
  nonempty : w.Nonempty
  noyau : noyau w = ∅
  noLine : ¬ ContientDroite (F w)

namespace Hyps4

variable {w : Set (Sphere E)} (H : Hyps4 w)
include H

theorem isOpen_F : IsOpen (F w) := isOpen_iff_F.1 H.isOpen

theorem exists_mem_F : ∃ u, u ∈ F w := by
  obtain ⟨x0, hx0⟩ := H.nonempty
  induction x0 using ind with
  | h u hu => exact ⟨u, hu, hx0⟩

/-- Along `u ∈ F(w)`, small positive moves stay in `F(w)`. -/
theorem exists_pos_add_smul_mem {u : E} (hu : u ∈ F w) (x : E) :
    ∃ t : ℝ, 0 < t ∧ u + t • x ∈ F w := by
  have hc : Continuous fun t : ℝ => u + t • x :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), u + t • x ∈ F w :=
    hc.continuousAt.preimage_mem_nhds (H.isOpen_F.mem_nhds (by simpa using hu))
  obtain ⟨t, ht, htpos⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin (s := Ioi (0 : ℝ)))).exists
  exact ⟨t, htpos, ht⟩

theorem span_F : Submodule.span ℝ (F w) = ⊤ := by
  obtain ⟨u, huF⟩ := H.exists_mem_F
  refine span_eq_top_of_absorbing (isPosCone_F w) huF fun x => ?_
  obtain ⟨t, htpos, ht⟩ := H.exists_pos_add_smul_mem huF x
  refine ⟨t⁻¹, inv_pos.2 htpos, ?_⟩
  have := isPosCone_F w t⁻¹ (inv_pos.2 htpos) _ ht
  rwa [smul_add, smul_smul, inv_mul_cancel₀ htpos.ne', one_smul, add_comm] at this

theorem supportK_eq : supportK w = univ := by
  unfold supportK; rw [H.span_F, linearSubvariety_top_eq]

theorem noLineK : ¬ ContientDroite (closure (kPrime w)) :=
  not_contientDroite_closure H.convex H.isOpen H.noyau H.noLine

/-- `F(w)` does not contain two opposite vectors. -/
theorem neg_notMem {x : E} (hx : x ∈ F w) : -x ∉ F w := by
  intro hnx
  apply H.noLineK
  have huniv : ∀ z : E, z ∈ kPrime w := by
    intro z
    obtain ⟨t, htpos, ht⟩ := H.exists_pos_add_smul_mem hnx z
    have hsum := add_mem_kPrime H.convex (mem_insert_of_mem _ hx) (mem_insert_of_mem _ ht)
    rw [add_neg_cancel_left] at hsum
    by_cases hz : z = 0
    · rw [hz]; exact zero_mem_kPrime w
    · rcases mem_insert_iff.1 hsum with h | h
      · exact absurd h (smul_ne_zero htpos.ne' hz)
      · have := isPosCone_F w t⁻¹ (inv_pos.2 htpos) _ h
        rw [smul_smul, inv_mul_cancel₀ htpos.ne', one_smul] at this
        exact mem_insert_of_mem _ this
  have hx0 : x ≠ 0 := fun h => zero_notMem_F w (h ▸ hx)
  exact ⟨0, x, hx0, fun t => subset_closure (huniv _)⟩

/-- `F(w)` is convex. -/
theorem convex_F : Convex ℝ (F w) := by
  intro x hx y hy a b ha hb hab
  have hm := H.convex (mem_insert_of_mem _ hx) (mem_insert_of_mem _ hy) ha hb hab
  rcases mem_insert_iff.1 hm with h0 | h
  · exfalso
    rcases ha.lt_or_eq with ha' | ha'
    · have hb' : 0 < b := by
        rcases hb.lt_or_eq with hb' | hb'
        · exact hb'
        · subst hb'; rw [add_zero] at hab; subst hab
          rw [one_smul, zero_smul, add_zero] at h0
          exact absurd (h0 ▸ hx) (zero_notMem_F w)
      have : -x = (b / a) • y := by
        have : a • x = -(b • y) := eq_neg_of_add_eq_zero_left h0
        rw [div_eq_mul_inv, mul_comm, ← smul_smul]
        calc -x = a⁻¹ • (-(a • x)) := by rw [smul_neg, smul_smul, inv_mul_cancel₀ ha'.ne', one_smul]
          _ = a⁻¹ • b • y := by rw [this, neg_neg]
      exact H.neg_notMem hx (this ▸ isPosCone_F w _ (div_pos hb' ha') y hy)
    · subst ha'; rw [zero_add] at hab; subst hab
      rw [one_smul, zero_smul, zero_add] at h0
      exact absurd (h0 ▸ hy) (zero_notMem_F w)
  · exact h

theorem isPreconnected : IsPreconnected w := by
  have hpre : IsPreconnected ((Subtype.val : {v : E // v ≠ 0} → E) ⁻¹' F w) := by
    refine (Topology.IsInducing.isPreconnected_image
      (f := (Subtype.val : {v : E // v ≠ 0} → E)) ⟨rfl⟩).1 ?_
    have : (Subtype.val : {v : E // v ≠ 0} → E) '' (Subtype.val ⁻¹' F w) = F w := by
      ext v
      exact ⟨fun ⟨u, hu, e⟩ => e ▸ hu, fun hv => ⟨⟨v, F_subset_compl_zero w hv⟩, hv, rfl⟩⟩
    rw [this]
    exact H.convex_F.isPreconnected
  have heq : s '' ((Subtype.val : {v : E // v ≠ 0} → E) ⁻¹' F w) = w := by
    rw [s_preimage_eq w |>.symm, image_preimage_eq _ s_surjective]
  exact heq ▸ hpre.image _ continuous_s.continuousOn

end Hyps4

variable [FiniteDimensional ℝ E]


namespace Hyps4

variable {w : Set (Sphere E)} (H : Hyps4 w)
include H

omit [FiniteDimensional ℝ E] in
theorem convexK : Convex ℝ (closure (kPrime w)) := (convex_kPrime H.convex).closure

omit [FiniteDimensional ℝ E] in
theorem spanK : Submodule.span ℝ (closure (kPrime w)) = ⊤ := span_closure_kPrime H.supportK_eq

theorem simplesS_eq' : simplesS w = simples (closure (kPrime w)) :=
  simplesS_eq H.convex H.isOpen H.supportK_eq H.noLineK

theorem finite : (simplesS w).Finite :=
  H.simplesS_eq' ▸ (simples_finite_ncard_le H.convexK (zero_mem_closure_kPrime w) H.spanK
    H.noLineK).1

theorem estSimple {L : Submodule ℝ E} (hL : L ∈ simplesS w) : EstSimple (closure (kPrime w)) L := by
  rw [H.simplesS_eq'] at hL; exact hL

theorem sSup_simplesS : sSup (simplesS w) = ⊤ := by
  have := eq_sSup_simples_le H.convexK (zero_mem_closure_kPrime w) H.spanK H.noLineK
    (estDistingue_top (zero_mem_closure_kPrime w))
  simpa [H.simplesS_eq'] using this

/-- For a set `T` of simple distinguished subvarieties, `∑ T` and `∑ (S ∖ T)` are supplementary
and conjugate (Déf. 6). -/
theorem conj_sSup {T : Set (Submodule ℝ E)} (hT : T ⊆ simplesS w) :
    IsCompl (sSup T) (sSup (simplesS w \ T)) ∧ EstConjugueS w (sSup T) (sSup (simplesS w \ T)) := by
  set W := closure (kPrime w)
  have h0 := zero_mem_closure_kPrime w
  have hT' : T ⊆ simples W := H.simplesS_eq' ▸ hT
  have hD := estDistingue_sSup_simples H.convexK h0 H.spanK H.noLineK hT'
  obtain ⟨hc, hsc⟩ := conjugue_spec hD
  have hC := estDistingue_conjugue hD
  have heq : conjugue W (sSup T) = sSup (simplesS w \ T) := by
    rw [← eq_sSup_simples_le H.convexK h0 H.spanK H.noLineK hC]
    congr 1
    ext s
    simp only [mem_setOf_eq, Set.mem_sdiff, H.simplesS_eq']
    constructor
    · rintro ⟨hs, hsC⟩
      refine ⟨hs, fun hsT => hs.2.1 ?_⟩
      exact le_bot_iff.1 (hc.disjoint.le_bot.trans' (le_inf (le_sSup hsT) hsC))
    · rintro ⟨hs, hsT⟩
      refine ⟨hs, ?_⟩
      have hfinT : T.Finite := H.finite.subset hT
      have hbot : s ⊓ sSup T = ⊥ := inf_sSup_eq_bot H.convexK h0 H.spanK H.noLineK hs.1 hfinT
        (fun t ht => (hT' ht).1) fun t ht =>
          inf_eq_bot_of_estSimple H.convexK h0 H.spanK H.noLineK hs (hT' ht) fun e => hsT (e ▸ ht)
      have h := inf_sup_le_of_estDistingue H.convexK h0 H.spanK H.noLineK hs.1 hD hC
      rw [hc.sup_eq_top, inf_top_eq, hbot, bot_sup_eq] at h
      exact h.trans inf_le_right
  rw [← heq]
  exact ⟨hc, (estConjugueS_iff_affine H.convex H.isOpen H.supportK_eq H.noLineK).2 ⟨hc, hsc⟩⟩

omit [FiniteDimensional ℝ E] in
/-- **Mixing along a conjugate pair**: `P_L x + P_{L'} y ∈ F(w)` for `x, y ∈ F(w)`. -/
theorem mix_of_conj {L L' : Submodule ℝ E} (hc : IsCompl L L') (h : EstConjugueS w L L')
    {x y : E} (hx : x ∈ F w) (hy : y ∈ F w) :
    L.projection L' hc x + L'.projection L hc.symm y ∈ F w := by
  rw [estConjugueS_iff H.convex, H.span_F] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨A, A', hA⟩
  · rw [Submodule.projection_apply_of_mem_left hc Submodule.mem_top,
      Submodule.projection_apply_of_mem_right hc.symm Submodule.mem_top, add_zero]
    exact hx
  · rw [Submodule.projection_apply_of_mem_right hc Submodule.mem_top,
      Submodule.projection_apply_of_mem_left hc.symm Submodule.mem_top, zero_add]
    exact hy
  · have h1 := (hA.projection_mem hc hx).1
    have h2 := (hA.projection_mem hc hy).2
    rw [hA.sum]
    exact Set.mem_add.2 ⟨_, h1, _, h2, rfl⟩

theorem isCompl_autres {L : Submodule ℝ E} (hL : L ∈ simplesS w) : IsCompl L (autresS w L) := by
  have := (H.conj_sSup (singleton_subset_iff.2 hL)).1
  rwa [sSup_singleton] at this

theorem projS_eq {L : Submodule ℝ E} (hL : L ∈ simplesS w) :
    projS w L = L.projection (autresS w L) (H.isCompl_autres hL) := by
  unfold projS; rw [dif_pos (H.isCompl_autres hL)]

theorem projS_apply_of_mem {L M : Submodule ℝ E} (hL : L ∈ simplesS w) (hM : M ∈ simplesS w)
    {x : E} (hx : x ∈ M) : projS w L x = if M = L then x else 0 := by
  rw [H.projS_eq hL]
  split_ifs with h
  · subst h; exact Submodule.projection_apply_of_mem_left _ hx
  · exact Submodule.projection_apply_of_mem_right _ (le_sSup (show M ∈ simplesS w \ {L} from ⟨hM, h⟩) hx)

/-- Two linear maps agreeing on every simple distinguished subspace are equal. -/
theorem linearMap_ext {f g : E →ₗ[ℝ] E} (h : ∀ M ∈ simplesS w, ∀ x ∈ M, f x = g x) : f = g := by
  refine LinearMap.ext fun x => ?_
  have hle : sSup (simplesS w) ≤ LinearMap.eqLocus f g := sSup_le fun M hM y hy => h M hM y hy
  exact hle (H.sSup_simplesS ▸ Submodule.mem_top)

end Hyps4


namespace Hyps4

variable {w : Set (Sphere E)} (H : Hyps4 w) {p : ℕ} (l : Fin p ≃ simplesS w)
include H

/-- `Q_T = ∑_{i ∈ T} P_{lᵢ}`. -/
noncomputable def projT (T : Finset (Fin p)) : E →ₗ[ℝ] E := ∑ i ∈ T, projS w (l i)

omit H [FiniteDimensional ℝ E] in
theorem exists_eq (M : Submodule ℝ E) (hM : M ∈ simplesS w) : ∃ k, (l k : Submodule ℝ E) = M :=
  ⟨l.symm ⟨M, hM⟩, by simp⟩

theorem projS_apply_l {i k : Fin p} {x : E} (hx : x ∈ (l k : Submodule ℝ E)) :
    projS w (l i) x = if i = k then x else 0 := by
  rw [H.projS_apply_of_mem (l i).2 (l k).2 hx]
  by_cases h : i = k
  · subst h; simp
  · rw [if_neg, if_neg h]
    intro e
    exact h (l.injective (Subtype.ext e.symm))

theorem projT_apply_l (T : Finset (Fin p)) {k : Fin p} {x : E} (hx : x ∈ (l k : Submodule ℝ E)) :
    projT l T x = if k ∈ T then x else 0 := by
  unfold projT
  rw [LinearMap.sum_apply]
  simp_rw [H.projS_apply_l l hx]
  exact Finset.sum_ite_eq' T k (fun _ => x)

theorem projT_univ : projT l Finset.univ = LinearMap.id := by
  refine H.linearMap_ext fun M hM x hx => ?_
  obtain ⟨k, rfl⟩ := exists_eq l M hM
  rw [H.projT_apply_l l _ hx, if_pos (Finset.mem_univ k), LinearMap.id_apply]

theorem projT_comp_projS (T : Finset (Fin p)) {i : Fin p} (hi : i ∈ T) :
    projT l T ∘ₗ projS w (l i) = projS w (l i) := by
  refine H.linearMap_ext fun M hM x hx => ?_
  obtain ⟨k, rfl⟩ := exists_eq l M hM
  rw [LinearMap.comp_apply, H.projS_apply_l l hx]
  split_ifs with h
  · subst h; rw [H.projT_apply_l l T hx, if_pos hi]
  · exact map_zero _

theorem projT_insert_comp_compl {T : Finset (Fin p)} {a : Fin p} (ha : a ∉ T) :
    projT l (insert a T) ∘ₗ projT l Tᶜ = projS w (l a) := by
  refine H.linearMap_ext fun M hM x hx => ?_
  obtain ⟨k, rfl⟩ := exists_eq l M hM
  rw [LinearMap.comp_apply, H.projT_apply_l l _ hx, H.projS_apply_l l hx]
  by_cases hk : k ∈ Tᶜ
  · rw [if_pos hk, H.projT_apply_l l _ hx]
    rw [Finset.mem_compl] at hk
    by_cases hka : k = a
    · subst hka; simp
    · rw [if_neg (by simp [hka, hk]), if_neg (Ne.symm hka)]
  · rw [if_neg hk, map_zero]
    rw [Finset.mem_compl, not_not] at hk
    rw [if_neg (fun (e : a = k) => ha (e ▸ hk))]

/-- **Mixing along `T`**: `Q_T x + Q_{Tᶜ} y ∈ F(w)` for `x, y ∈ F(w)`. -/
theorem projT_mix (T : Finset (Fin p)) {x y : E} (hx : x ∈ F w) (hy : y ∈ F w) :
    projT l T x + projT l Tᶜ y ∈ F w := by
  set D : Set (Submodule ℝ E) := (fun i => (l i : Submodule ℝ E)) '' (T : Set (Fin p))
  have hDS : D ⊆ simplesS w := by rintro _ ⟨i, -, rfl⟩; exact (l i).2
  obtain ⟨hc, hconj⟩ := H.conj_sSup hDS
  have hmemD : ∀ k, (l k : Submodule ℝ E) ∈ D ↔ k ∈ T := fun k =>
    ⟨fun ⟨i, hi, e⟩ => (l.injective (Subtype.ext e)) ▸ hi, fun hk => ⟨k, hk, rfl⟩⟩
  have h1 : (sSup D).projection (sSup (simplesS w \ D)) hc = projT l T := by
    refine H.linearMap_ext fun M hM z hz => ?_
    obtain ⟨k, rfl⟩ := exists_eq l M hM
    rw [H.projT_apply_l l T hz]
    split_ifs with hk
    · exact Submodule.projection_apply_of_mem_left _ (le_sSup ((hmemD k).2 hk) hz)
    · exact Submodule.projection_apply_of_mem_right _
        (le_sSup (show (l k : Submodule ℝ E) ∈ simplesS w \ D from ⟨(l k).2, mt (hmemD k).1 hk⟩) hz)
  have h2 : (sSup (simplesS w \ D)).projection (sSup D) hc.symm = projT l Tᶜ := by
    refine H.linearMap_ext fun M hM z hz => ?_
    obtain ⟨k, rfl⟩ := exists_eq l M hM
    rw [H.projT_apply_l l _ hz]
    split_ifs with hk
    · rw [Finset.mem_compl] at hk
      exact Submodule.projection_apply_of_mem_left _
        (le_sSup (show (l k : Submodule ℝ E) ∈ simplesS w \ D from ⟨(l k).2, mt (hmemD k).1 hk⟩) hz)
    · rw [Finset.mem_compl, not_not] at hk
      exact Submodule.projection_apply_of_mem_right _ (le_sSup ((hmemD k).2 hk) hz)
  have := H.mix_of_conj hc hconj hx hy
  rwa [h1, h2] at this

/-- **The sum lies in `F(w)`**: `∑_{i ∈ T} P_{lᵢ}(xᵢ) + Q_{Tᶜ} y ∈ F(w)` for `xᵢ, y ∈ F(w)`. -/
theorem sum_mem_aux (T : Finset (Fin p)) {x : Fin p → E} (hx : ∀ i, x i ∈ F w) {y : E}
    (hy : y ∈ F w) : ∑ i ∈ T, projS w (l i) (x i) + projT l Tᶜ y ∈ F w := by
  induction T using Finset.induction_on generalizing y with
  | empty => rw [Finset.sum_empty, zero_add, Finset.compl_empty, H.projT_univ]; exact hy
  | @insert a T ha ih =>
    have hz := ih (hx a)
    have hm := H.projT_mix l (insert a T) hz hy
    have e : projT l (insert a T) (∑ i ∈ T, projS w (l i) (x i) + projT l Tᶜ (x a)) =
        ∑ i ∈ insert a T, projS w (l i) (x i) := by
      rw [map_add, map_sum, Finset.sum_insert ha, add_comm (projS w (l a) (x a))]
      congr 1
      · refine Finset.sum_congr rfl fun i hi => ?_
        exact LinearMap.congr_fun (H.projT_comp_projS l (insert a T) (Finset.mem_insert_of_mem hi))
          (x i)
      · exact LinearMap.congr_fun (H.projT_insert_comp_compl l ha) (x a)
    rwa [e] at hm

theorem sum_mem {x : Fin p → E} (hx : ∀ i, x i ∈ F w) : ∑ i, projS w (l i) (x i) ∈ F w := by
  obtain ⟨y, hy⟩ := H.exists_mem_F
  have := H.sum_mem_aux l Finset.univ hx hy
  have e : projT l (Finset.univ : Finset (Fin p))ᶜ = 0 := by
    rw [Finset.compl_univ]; rfl
  rwa [e, LinearMap.zero_apply, add_zero] at this

theorem sum_projS (x : E) : ∑ i, projS w (l i) x = x := by
  have := LinearMap.congr_fun (H.projT_univ l) x
  rwa [projT, LinearMap.sum_apply] at this

end Hyps4


namespace Hyps4

variable {w : Set (Sphere E)} (H : Hyps4 w)
include H

theorem projS_mem {L : Submodule ℝ E} (hL : L ∈ simplesS w) (x : E) : projS w L x ∈ L := by
  rw [H.projS_eq hL]; exact Submodule.projection_apply_mem _ x

theorem projS_ne_zero {L : Submodule ℝ E} (hL : L ∈ simplesS w) {x : E} (hx : x ∈ F w) :
    projS w L x ≠ 0 := by
  have hconj := (H.conj_sSup (singleton_subset_iff.2 hL)).2
  rw [sSup_singleton] at hconj
  obtain ⟨hc, hsc⟩ := (estConjugueS_iff_affine H.convex H.isOpen H.supportK_eq H.noLineK).1 hconj
  rw [H.projS_eq hL]
  exact projection_ne_zero H.isOpen H.noLineK hc (fun y hy => (projection_mem_inter hc hsc hy).2)
    (H.estSimple hL).2.1 hx

omit H [FiniteDimensional ℝ E] in
theorem isPosCone_sommande (L : Submodule ℝ E) : IsPosCone (sommandeS w L) := by
  rintro c hc _ ⟨x, hx, rfl⟩
  exact ⟨c • x, isPosCone_F w c hc x hx, map_smul _ _ _⟩

theorem zero_notMem_sommande {L : Submodule ℝ E} (hL : L ∈ simplesS w) :
    (0 : E) ∉ sommandeS w L := by
  rintro ⟨x, hx, e⟩
  exact H.projS_ne_zero hL hx e

omit [FiniteDimensional ℝ E] in
theorem convex_sommande (L : Submodule ℝ E) : Convex ℝ (sommandeS w L) :=
  H.convex_F.linear_image _

theorem F_composante {L : Submodule ℝ E} (hL : L ∈ simplesS w) :
    F (composanteS w L) = sommandeS w L :=
  F_ofCone_of_zero_notMem (isPosCone_sommande L) (H.zero_notMem_sommande hL)

theorem sommande_subset {L : Submodule ℝ E} (hL : L ∈ simplesS w) :
    sommandeS w L ⊆ L := by
  rintro _ ⟨x, -, rfl⟩; exact H.projS_mem hL x

theorem span_sommande {L : Submodule ℝ E} (hL : L ∈ simplesS w) :
    Submodule.span ℝ (sommandeS w L) = L := by
  unfold sommandeS
  rw [Submodule.span_image, H.span_F, Submodule.map_top, H.projS_eq hL,
    Submodule.range_projection]

theorem isOpen_sommande {L : Submodule ℝ E} (hL : L ∈ simplesS w) :
    IsOpen ((Subtype.val : ↥L → E) ⁻¹' sommandeS w L) := by
  have hc := H.isCompl_autres hL
  have e : (Subtype.val : ↥L → E) ⁻¹' sommandeS w L = L.projectionOnto (autresS w L) hc '' F w := by
    ext y
    simp only [sommandeS, mem_preimage, mem_image, H.projS_eq hL]
    constructor
    · rintro ⟨x, hx, e⟩
      exact ⟨x, hx, Subtype.ext e⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
  rw [e]
  exact LinearMap.isOpenMap_of_finiteDimensional _ (Submodule.projectionOnto_surjective hc) _
    H.isOpen_F

theorem projS_sum {p : ℕ} (l : Fin p ≃ simplesS w) {x : Fin p → E}
    (hx : ∀ j, x j ∈ (l j : Submodule ℝ E)) (i : Fin p) : projS w (l i) (∑ j, x j) = x i := by
  rw [map_sum]
  simp_rw [fun j => H.projS_apply_l l (i := i) (hx j)]
  exact Finset.sum_ite_eq Finset.univ i x |>.trans (if_pos (Finset.mem_univ i))

end Hyps4


omit [FiniteDimensional ℝ E] in
/-- **The degenerate case `w = ∅`** (excluded by the reading « `w` non vide », see SCOPE): the
empty part has no simple distinguished subvariety (`p = 0`), and it is not the sum of the
empty family (Déf. 5: the empty sum is `{O}`, `F(∅) = ∅`). -/
theorem simplesS_empty_and_not_estSommeS :
    simplesS (∅ : Set (Sphere E)) = ∅ ∧ ¬ EstSommeS (∅ : Set (Sphere E)) (Fin.elim0 : Fin 0 → Set (Sphere E)) := by
  refine ⟨eq_empty_of_forall_notMem fun L hL => ?_, fun h => ?_⟩
  · obtain ⟨⟨L', hc⟩, hne, -⟩ := hL
    rw [estConjugueS_iff (by unfold IsConvexPart; rw [F_empty, insert_empty_eq]; exact convex_singleton 0),
      F_empty, Submodule.span_empty] at hc
    rcases hc with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨A, A', hA⟩
    · exact hne rfl
    · exact hne rfl
    · obtain ⟨a, ha⟩ := hA.ne
      obtain ⟨a', ha'⟩ := hA.ne'
      have : a + a' ∈ (∅ : Set E) := hA.sum ▸ Set.add_mem_add ha ha'
      exact this
  · obtain ⟨-, hbij⟩ := (isSommeConvexes_iff_bijOn _ _).1 h.2
    have := hbij.mapsTo (x := (Fin.elim0 : Fin 0 → E)) (fun i => Fin.elim0 i)
    simp at this

/-- **Prop. 4, first assertion** (`w = F⁻¹(F(v₁) × … × F(v_p))`, intrinsic form): for `w` a
nonempty open convex of `S(E)` with empty noyau and no line in `F(w)`, the simple distinguished
subvarieties `l₁, …, l_p` are finitely many (`1 ≤ p ≤ dim E`); for any enumeration of them,
`w` is the sum (Déf. 5) of the `vᵢ = s(P_{lᵢ}(F(w)))`, each `vᵢ` a nonempty convex part of
support `lᵢ`, open in `lᵢ`; and the `vᵢ` are the only convexes contained in the `lᵢ` of which
`w` is the sum. -/
theorem prop4_somme {w : Set (Sphere E)} (hw : IsConvexPart w) (hopen : IsOpen w)
    (hne : w.Nonempty) (hn : noyau w = ∅) (hd : ¬ ContientDroite (F w)) :
    (simplesS w).Finite ∧ 1 ≤ (simplesS w).ncard ∧
      (simplesS w).ncard ≤ Module.finrank ℝ E ∧
      ∀ {p : ℕ} (l : Fin p ≃ simplesS w),
        EstSommeS w (fun i => composanteS w (l i)) ∧
        (∀ i, IsConvexPart (composanteS w (l i)) ∧ (composanteS w (l i)).Nonempty ∧
          supportK (composanteS w (l i)) = linearSubvariety (l i : Submodule ℝ E) ∧
          F (composanteS w (l i)) = sommandeS w (l i) ∧
          IsOpen ((Subtype.val : ↥(l i : Submodule ℝ E) → E) ⁻¹' sommandeS w (l i))) ∧
        (∀ v : Fin p → Set (Sphere E), EstSommeS w v →
          (∀ i, v i ⊆ linearSubvariety (l i : Submodule ℝ E)) → ∀ i, v i = composanteS w (l i)) := by
  have H : Hyps4 w := ⟨hw, hopen, hne, hn, hd⟩
  have h0 := zero_mem_closure_kPrime w
  obtain ⟨-, hcard, hpos, -⟩ := corollaire_algebre_parties H.convexK h0 H.spanK H.noLineK
  obtain ⟨u, hu⟩ := H.exists_mem_F
  haveI : Nontrivial E := nontrivial_of_ne u 0 fun e => zero_notMem_F w (e ▸ hu)
  refine ⟨H.finite, H.simplesS_eq' ▸ hpos Module.finrank_pos, H.simplesS_eq' ▸ hcard,
    fun {p} l => ?_⟩
  have hF : ∀ i, F (composanteS w (l i)) = sommandeS w (l i) := fun i => H.F_composante (l i).2
  have hmemL : ∀ i, ∀ y ∈ sommandeS w (l i), y ∈ (l i : Submodule ℝ E) := fun i y hy =>
    H.sommande_subset (l i).2 hy
  refine ⟨⟨fun i => (hF i).symm ▸ H.convex_sommande _, ?_⟩, fun i => ?_, fun v hv hvl i => ?_⟩
  · rw [isSommeConvexes_iff_bijOn]
    refine ⟨fun i => (hF i).symm ▸ H.convex_sommande _, ?_, ?_, ?_⟩
    · intro x hx
      have hx' : ∀ i, ∃ y, y ∈ F w ∧ projS w (l i) y = x i := fun i => by
        have : x i ∈ F (composanteS w (l i)) := hx i (mem_univ i)
        rw [hF i] at this; exact this
      choose y hy hyx using hx'
      have := H.sum_mem l hy
      simp_rw [hyx] at this
      exact this
    · intro x hx x' hx' e
      funext i
      have h1 := H.projS_sum l (fun j => hmemL j _ ((hF j) ▸
        (show x j ∈ F (composanteS w (l j)) from hx j (mem_univ j)))) i
      have h2 := H.projS_sum l (fun j => hmemL j _ ((hF j) ▸
        (show x' j ∈ F (composanteS w (l j)) from hx' j (mem_univ j)))) i
      simp only at e
      rw [← h1, ← h2, e]
    · intro z hz
      refine ⟨fun i => projS w (l i) z, fun i _ => ?_, H.sum_projS l z⟩
      show projS w (l i) z ∈ F (composanteS w (l i))
      rw [hF i]; exact ⟨z, hz, rfl⟩
  · refine ⟨isConvexPart_ofCone_of_cone (H.convex_sommande _) (Hyps4.isPosCone_sommande _),
      ⟨_, mk_mem_ofCone (H.projS_ne_zero (l i).2 hu) ⟨u, hu, rfl⟩⟩, ?_, hF i,
      H.isOpen_sommande (l i).2⟩
    rw [composanteS, supportK_ofCone (Hyps4.isPosCone_sommande _) (H.zero_notMem_sommande (l i).2),
      H.span_sommande (l i).2]
  · -- uniqueness
    obtain ⟨hvc, hvs⟩ := hv
    obtain ⟨-, hbij⟩ := (isSommeConvexes_iff_bijOn _ _).1 hvs
    have hvL : ∀ j, ∀ y ∈ F (v j), y ∈ (l j : Submodule ℝ E) := fun j y hy => by
      have := F_mono (hvl j) hy
      rw [linearSubvariety, F_ofCone (fun c _ v hv => Submodule.smul_mem _ c hv)] at this
      exact this.1
    rw [← ofCone_F (v i), composanteS]
    congr 1
    apply Subset.antisymm
    · intro y hy
      obtain ⟨x, hx, -⟩ := hbij.surjOn hu
      have hx' : Function.update x i y ∈ univ.pi fun j => F (v j) := by
        intro j _
        by_cases hj : j = i
        · subst hj; simpa using hy
        · rw [Function.update_of_ne hj]; exact hx j (mem_univ j)
      have hz := hbij.mapsTo hx'
      refine ⟨_, hz, ?_⟩
      rw [H.projS_sum l (fun j => hvL j _ (hx' j (mem_univ j))) i, Function.update_self]
    · rintro _ ⟨z, hz, rfl⟩
      obtain ⟨x, hx, rfl⟩ := hbij.surjOn hz
      rw [H.projS_sum l (fun j => hvL j _ (hx j (mem_univ j))) i]
      exact hx i (mem_univ i)


namespace Hyps4

variable {w : Set (Sphere E)}

omit [FiniteDimensional ℝ E] in
theorem image_F_of_preserves (g : E ≃ₗ[ℝ] E) (hg : ∀ x : Sphere E, g • x ∈ w ↔ x ∈ w) :
    (g : E → E) '' F w = F w := by
  ext v
  constructor
  · rintro ⟨u, ⟨hu, huw⟩, rfl⟩
    exact ⟨g.map_ne_zero_iff.2 hu, (hg (Sphere.mk u hu)).2 huw⟩
  · rintro ⟨hv, hvw⟩
    have hu : g.symm v ≠ 0 := g.symm.map_ne_zero_iff.2 hv
    refine ⟨g.symm v, ⟨hu, (hg _).1 ?_⟩, by simp⟩
    rw [smul_mk]; simpa using hvw

omit [FiniteDimensional ℝ E] in
theorem preserves_symm {g : E ≃ₗ[ℝ] E} (hg : ∀ x : Sphere E, g • x ∈ w ↔ x ∈ w) :
    ∀ x : Sphere E, g.symm • x ∈ w ↔ x ∈ w := fun x => by
  induction x using ind with
  | h v hv =>
    rw [← hg, smul_mk, smul_mk]
    simp only [LinearEquiv.apply_symm_apply]

omit [FiniteDimensional ℝ E] in
/-- A linear automorphism preserving `w` transports conjugate pairs (Déf. 6). -/
theorem estConjugueS_map (hw : IsConvexPart w) (hspan : Submodule.span ℝ (F w) = ⊤)
    (g : E ≃ₗ[ℝ] E) (hg : ∀ x : Sphere E, g • x ∈ w ↔ x ∈ w) {L L' : Submodule ℝ E}
    (h : EstConjugueS w L L') :
    EstConjugueS w (L.map (g : E →ₗ[ℝ] E)) (L'.map (g : E →ₗ[ℝ] E)) := by
  have hgF := image_F_of_preserves g hg
  have hinj : Function.Injective (g : E →ₗ[ℝ] E) := g.injective
  rw [estConjugueS_iff hw, hspan] at h ⊢
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨A, A', hA⟩
  · exact Or.inl ⟨by rw [Submodule.map_top]; exact LinearMap.range_eq_top.2 g.surjective, Submodule.map_bot _⟩
  · exact Or.inr (Or.inl ⟨Submodule.map_bot _, by rw [Submodule.map_top]; exact LinearMap.range_eq_top.2 g.surjective⟩)
  · refine Or.inr (Or.inr ⟨(g : E → E) '' A, (g : E → E) '' A', ⟨hA.convex.linear_image (g : E →ₗ[ℝ] E),
      hA.convex'.linear_image (g : E →ₗ[ℝ] E), ?_, ?_, ?_, ?_, hA.ne.image _, hA.ne'.image _, ?_, ?_,
      ?_, ?_⟩⟩)
    · rintro c hc _ ⟨a, ha, rfl⟩; exact ⟨c • a, hA.pos c hc a ha, map_smul g c a⟩
    · rintro c hc _ ⟨a, ha, rfl⟩; exact ⟨c • a, hA.pos' c hc a ha, map_smul g c a⟩
    · rintro ⟨a, ha, e⟩; exact hA.zero ((g.map_eq_zero_iff.1 e) ▸ ha)
    · rintro ⟨a, ha, e⟩; exact hA.zero' ((g.map_eq_zero_iff.1 e) ▸ ha)
    · rw [← hA.span]; exact Submodule.span_image (g : E →ₗ[ℝ] E)
    · rw [← hA.span']; exact Submodule.span_image (g : E →ₗ[ℝ] E)
    · rw [← Submodule.map_inf _ hinj, hA.disj, Submodule.map_bot]
    · rw [← hgF, hA.sum, Set.image_add g]

end Hyps4


namespace Hyps4

variable {w : Set (Sphere E)} (H : Hyps4 w)
include H

omit [FiniteDimensional ℝ E] in
theorem estDistingueS_map (g : E ≃ₗ[ℝ] E) (hg : ∀ x : Sphere E, g • x ∈ w ↔ x ∈ w)
    {L : Submodule ℝ E} (h : EstDistingueS w L) : EstDistingueS w (L.map (g : E →ₗ[ℝ] E)) := by
  obtain ⟨L', h'⟩ := h
  exact ⟨_, estConjugueS_map H.convex H.span_F g hg h'⟩

omit H [FiniteDimensional ℝ E] in
theorem map_symm_map (g : E ≃ₗ[ℝ] E) (L : Submodule ℝ E) :
    (L.map (g : E →ₗ[ℝ] E)).map (g.symm : E →ₗ[ℝ] E) = L :=
  (Submodule.map_symm_eq_iff g).2 rfl

omit H [FiniteDimensional ℝ E] in
theorem map_map_symm (g : E ≃ₗ[ℝ] E) (L : Submodule ℝ E) :
    (L.map (g.symm : E →ₗ[ℝ] E)).map (g : E →ₗ[ℝ] E) = L := by
  have := map_symm_map g.symm L
  rwa [LinearEquiv.symm_symm] at this

omit [FiniteDimensional ℝ E] in
/-- A linear automorphism preserving `w` maps simple distinguished subvarieties to simple ones. -/
theorem estSimpleS_map (g : E ≃ₗ[ℝ] E) (hg : ∀ x : Sphere E, g • x ∈ w ↔ x ∈ w)
    {L : Submodule ℝ E} (h : EstSimpleS w L) : EstSimpleS w (L.map (g : E →ₗ[ℝ] E)) := by
  obtain ⟨hd, hne, hmin⟩ := h
  refine ⟨H.estDistingueS_map g hg hd, fun e => hne ?_, fun M hM hM0 hle => ?_⟩
  · rw [← Hyps4.map_symm_map g L, e, Submodule.map_bot]
  · have hgs := preserves_symm hg
    have h1 := hmin _ (H.estDistingueS_map g.symm hgs hM)
      (fun e => hM0 (by rw [← Hyps4.map_map_symm g M, e, Submodule.map_bot]))
      (by rw [← Hyps4.map_symm_map g L]; exact Submodule.map_mono hle)
    rw [← h1, Hyps4.map_map_symm]

end Hyps4

/-- **Prop. 4, the proof** (« un automorphisme projectif de `w` est un élément de `GP(n, ℝ)` qui
permute entre elles les variétés distinguées simples »): a linear automorphism `g` of `E`
preserving `w` permutes the simple distinguished subvarieties, `g(l_{σ(L)}) = l_L`, and maps each
summand `F(v_{σ(L)})` onto `F(v_L)`, so that `g(∑ x_M) = ∑_L g(x_{σ(L)})` with
`g(x_{σ(L)}) ∈ F(v_L)`: Ch. 1 § 3 Déf. 2's formula `m′_L = φ_L m_{σ(L)}`, `φ_L = g`, `t = 1`. -/
theorem prop4_permute {w : Set (Sphere E)} (hw : IsConvexPart w) (hopen : IsOpen w)
    (hne : w.Nonempty) (hn : noyau w = ∅) (hd : ¬ ContientDroite (F w)) (g : E ≃ₗ[ℝ] E)
    (hg : ∀ x : Sphere E, g • x ∈ w ↔ x ∈ w) :
    ∃ σ : Equiv.Perm (simplesS w), ∀ L : simplesS w,
      (σ L : Submodule ℝ E).map (g : E →ₗ[ℝ] E) = L ∧
      g '' sommandeS w (σ L) = sommandeS w L := by
  have H : Hyps4 w := ⟨hw, hopen, hne, hn, hd⟩
  have hgs := Hyps4.preserves_symm hg
  let σ : Equiv.Perm (simplesS w) :=
    { toFun := fun L => ⟨(L : Submodule ℝ E).map (g.symm : E →ₗ[ℝ] E), H.estSimpleS_map g.symm hgs L.2⟩
      invFun := fun L => ⟨(L : Submodule ℝ E).map (g : E →ₗ[ℝ] E), H.estSimpleS_map g hg L.2⟩
      left_inv := fun L => Subtype.ext (Hyps4.map_map_symm g L)
      right_inv := fun L => Subtype.ext (Hyps4.map_symm_map g L) }
  refine ⟨σ, fun L => ⟨Hyps4.map_map_symm g L, ?_⟩⟩
  have hσL : (σ L : Submodule ℝ E) ∈ simplesS w := (σ L).2
  have hcomm : (g : E →ₗ[ℝ] E) ∘ₗ projS w (σ L) = projS w L ∘ₗ (g : E →ₗ[ℝ] E) := by
    refine H.linearMap_ext fun M hM x hx => ?_
    have hgM : (M.map (g : E →ₗ[ℝ] E)) ∈ simplesS w := H.estSimpleS_map g hg hM
    have hgx : (g : E →ₗ[ℝ] E) x ∈ M.map (g : E →ₗ[ℝ] E) := Submodule.mem_map_of_mem hx
    rw [LinearMap.comp_apply, LinearMap.comp_apply, H.projS_apply_of_mem hσL hM hx,
      H.projS_apply_of_mem L.2 hgM hgx]
    have : M = (σ L : Submodule ℝ E) ↔ M.map (g : E →ₗ[ℝ] E) = L := by
      show M = (L : Submodule ℝ E).map (g.symm : E →ₗ[ℝ] E) ↔ _
      rw [eq_comm, Submodule.map_symm_eq_iff]
    by_cases hML : M = (σ L : Submodule ℝ E)
    · rw [if_pos hML, if_pos (this.1 hML)]
    · rw [if_neg hML, if_neg (mt this.2 hML), map_zero]
  unfold sommandeS
  conv_rhs => rw [← Hyps4.image_F_of_preserves g hg]
  rw [image_image, image_image]
  exact image_congr fun x _ => LinearMap.congr_fun hcomm x

end Prop4

section Model

variable {m : ℕ}

/-- Every projective automorphism of a nonempty preconnected open `w` of `S(m)` is the
restriction of a linear automorphism of `ℝ^{m+1}` (Ch. 1 Prop. 1 on the connected `w`). -/
theorem exists_linearEquiv_of_gxAut {w : TopologicalSpace.Opens (S m)}
    (hc : IsPreconnected (w : Set (S m))) (hne : (w : Set (S m)).Nonempty)
    (f : GXAut (GSR m) (S m) w) :
    ∃ g : (Fin (m + 1) → ℝ) ≃ₗ[ℝ] (Fin (m + 1) → ℝ), ∀ x : w, ((f • x : w) : S m) = g • (x : S m) := by
  obtain ⟨x₀, hx₀⟩ := hne
  set φ : OpenPartialHomeomorph w (S m) := chartAt (S m) (⟨x₀, hx₀⟩ : w)
  have hφs : φ.source = univ := by
    simp [φ, TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source]
  have hφ : IsCompatibleChart (GSR m) φ :=
    isCompatibleChart_iff.2 ((gxGroupoid _ _).chart_mem_maximalAtlas _)
  have hψ := hφ.trans_aut f
  have hC : IsPreconnected (univ : Set w) := by
    haveI : PreconnectedSpace w := Subtype.preconnectedSpace hc
    exact isPreconnected_univ
  obtain ⟨g, hg⟩ := exists_smul_eq_on_of_isPreconnected hφ hψ hC ⟨⟨x₀, hx₀⟩, trivial⟩
    (by rw [hφs]) (by simp [hφs])
  obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
  refine ⟨g', fun x => ?_⟩
  have := hg x trivial
  have hφx : ∀ y : w, φ y = (y : S m) := fun y => by
    simp [φ, TopologicalSpace.Opens.chartAt_eq]
  simp only [OpenPartialHomeomorph.trans_apply, Homeomorph.toOpenPartialHomeomorph_apply,
    hφx] at this
  rw [GSE.mk_smul] at this
  exact this

/-- **« un automorphisme projectif de `w` est un élément de `GP(n, ℝ)` »**: every projective
automorphism of a nonempty convex open `w` of `S(m)` with no line in `F(w)` is the restriction
of a linear automorphism `g` of `ℝ^{m+1}` preserving `w`. -/
theorem prop4_gxAut {w : TopologicalSpace.Opens (S m)} (hw : IsConvexPart (w : Set (S m)))
    (hne : (w : Set (S m)).Nonempty) (hn : noyau (w : Set (S m)) = ∅)
    (hd : ¬ ContientDroite (F (w : Set (S m)))) (f : GXAut (GSR m) (S m) w) :
    ∃ g : (Fin (m + 1) → ℝ) ≃ₗ[ℝ] (Fin (m + 1) → ℝ), (∀ x : w, ((f • x : w) : S m) = g • (x : S m)) ∧
      ∀ x : S m, g • x ∈ (w : Set (S m)) ↔ x ∈ (w : Set (S m)) := by
  have H : Hyps4 (w : Set (S m)) := ⟨hw, w.isOpen, hne, hn, hd⟩
  obtain ⟨g, hg⟩ := exists_linearEquiv_of_gxAut H.isPreconnected hne f
  obtain ⟨g', hg'⟩ := exists_linearEquiv_of_gxAut H.isPreconnected hne f⁻¹
  have hid : ∀ z ∈ (w : Set (S m)), g' • g • z = z := fun z hz => by
    have e1 := hg ⟨z, hz⟩
    have e2 := hg' (f • ⟨z, hz⟩)
    rw [← e1, ← e2, inv_smul_smul]
  refine ⟨g, hg, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · have e2 := hg' ⟨g • x, hx⟩
    have : g' • g • x = x := by
      have h1 : ((QuotientGroup.mk (g' * g) : GSR m)) = 1 :=
        GSE.eq_one_of_eqOn w.isOpen hne fun z hz => by
          simp only [GSE.mk_smul, id, mul_smul]; exact hid z hz
      have := congrArg (fun k : GSR m => k • x) h1
      simpa [GSE.mk_smul, mul_smul] using this
    rw [← this, ← e2]
    exact (f⁻¹ • (⟨g • x, hx⟩ : w)).2
  · rw [← hg ⟨x, hx⟩]; exact (f • (⟨x, hx⟩ : w)).2


/-- **Prop. 4, second assertion, in the coordinates of `w`** (Ch. 1 § 3 Déf. 2's formula
`m′ᵢ = φᵢ m_{σ(i)}`): for every enumeration `l₁, …, l_p` of the simple distinguished
subvarieties of `w` (as in `prop4_somme`), every projective automorphism `f` of `w` is the
restriction of a linear `g` which maps `l_{τ(i)}` onto `lᵢ` and `F(v_{τ(i)})` onto `F(vᵢ)`
(so `g(x_{τ(i)}) ∈ F(vᵢ)` for every `x` of `∏ F(vⱼ)`): `f` is compatible, associated with the
permutation `τ`, with `φᵢ = g|F(v_{τ(i)})` and `t = 1`, in the coordinates of `w`. This is weaker
than Ch. 1's `IsCompatiblePi`: the `φᵢ` are linear but not normalised to `GU`, and no isomorphism
`w ≅ PiBase` is given here (that form is `prop4_produit`, in `BalayableSommeProduit.lean`). -/
theorem prop4_automorphisme_compatible {w : TopologicalSpace.Opens (S m)}
    (hw : IsConvexPart (w : Set (S m))) (hne : (w : Set (S m)).Nonempty)
    (hn : noyau (w : Set (S m)) = ∅) (hd : ¬ ContientDroite (F (w : Set (S m)))) {p : ℕ}
    (l : Fin p ≃ simplesS (w : Set (S m))) (f : GXAut (GSR m) (S m) w) :
    ∃ g : (Fin (m + 1) → ℝ) ≃ₗ[ℝ] (Fin (m + 1) → ℝ), (∀ x : w, ((f • x : w) : S m) = g • (x : S m)) ∧
      ∃ τ : Equiv.Perm (Fin p), (∀ i, (l (τ i) : Submodule ℝ (Fin (m + 1) → ℝ)).map
          (g : (Fin (m + 1) → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ)) = l i ∧
        g '' sommandeS (w : Set (S m)) (l (τ i)) = sommandeS (w : Set (S m)) (l i)) ∧
        ∀ x : Fin p → (Fin (m + 1) → ℝ), (∀ i, x i ∈ sommandeS (w : Set (S m)) (l i)) →
          ∀ i, g (x (τ i)) ∈ sommandeS (w : Set (S m)) (l i) := by
  obtain ⟨g, hfg, hg⟩ := prop4_gxAut hw hne hn hd f
  obtain ⟨σ, hσ⟩ := prop4_permute hw w.isOpen hne hn hd g hg
  have e : ∀ i, l ((l.trans (σ.trans l.symm)) i) = σ (l i) := fun i => by simp
  have hτ : ∀ i, ((l (l.trans (σ.trans l.symm) i) : Submodule ℝ (Fin (m + 1) → ℝ)).map
        (g : (Fin (m + 1) → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ)) = l i ∧
      g '' sommandeS (w : Set (S m)) (l (l.trans (σ.trans l.symm) i)) =
        sommandeS (w : Set (S m)) (l i)) := fun i => by rw [e]; exact hσ (l i)
  refine ⟨g, hfg, l.trans (σ.trans l.symm), hτ, fun x hx i => ?_⟩
  rw [← (hτ i).2]
  exact mem_image_of_mem _ (hx _)

end Model

end Sphere


namespace BooleProjectifInstance

open Sphere

theorem span_Bt_eq (t : ℝ) : Submodule.span ℝ (Bt t) = Submodule.span ℝ {(![t, 1, 0] : V3)} := by
  refine le_antisymm (Submodule.span_le.2 fun v hv => ?_) (Submodule.span_le.2 ?_)
  · rw [SetLike.mem_coe, Submodule.mem_span_singleton]
    refine ⟨v 1, ?_⟩
    obtain ⟨⟨h2, h0⟩, -⟩ := hv
    simp only [ze, hyp, mem_setOf_eq] at h2 h0
    ext i; fin_cases i <;> simp [h0, h2, mul_comm]
  · rw [singleton_subset_iff]
    exact Submodule.subset_span (by simp [Bt, hyp, ze, po])

/-- Relative to the open quarter, each pair `{±(t e₁ + e₂)}` is a simple distinguished
subvariety. -/
theorem quart_estSimpleS_Bt (t : ℝ) : EstSimpleS quartS (Submodule.span ℝ (Bt t)) := by
  have hne : (![t, 1, 0] : V3) ≠ 0 := fun h => by simpa using congrFun h 1
  refine ⟨quart_distingue_Bt t, fun h => hne ?_, fun M _ hM hle => ?_⟩
  · have : (![t, 1, 0] : V3) ∈ Submodule.span ℝ (Bt t) := Submodule.subset_span (by simp [Bt, hyp, ze, po])
    rwa [h, Submodule.mem_bot] at this
  · rw [span_Bt_eq] at hle ⊢
    refine Submodule.eq_of_le_of_finrank_eq hle ?_
    rw [finrank_span_singleton hne]
    have h1 := Submodule.finrank_mono hle
    rw [finrank_span_singleton hne] at h1
    have h2 : Module.finrank ℝ M ≠ 0 := fun h0 => hM (Submodule.finrank_eq_zero.1 h0)
    omega

/-- **Prop. 4 is false as printed** (the reading of OQ-168): the open quarter `{y > 0, z > 0}`
of `S(2)` is a nonempty convex open part of empty noyau, and it has infinitely many simple
distinguished subvarieties, so « les `p` sous-variétés distinguées simples » and a finite sum
`w = F⁻¹(F(v₁) × … × F(v_p))` over them do not exist. -/
theorem not_prop4_simplesS_finite :
    ∃ w : Set (S 2), IsConvexPart w ∧ IsOpen w ∧ w.Nonempty ∧ noyau w = ∅ ∧ (simplesS w).Infinite :=
  ⟨quartS, isConvexPart_quartS, isOpen_quartS,
    ⟨_, mk_mem_ofCone (v := (![0, 1, 1] : V3)) (fun h => by simpa using congrFun h 1)
      (by simp [quart, po])⟩, noyau_quartS,
    Set.infinite_of_injective_forall_mem span_Bt_injective quart_estSimpleS_Bt⟩

/-- **The instance: the open `n`-simplex** satisfies the hypotheses of Prop. 4 (`p = n + 1`). -/
theorem simplexO_hyps4 {n : ℕ} : IsConvexPart (simplexO n) ∧ IsOpen (simplexO n) ∧
    (simplexO n).Nonempty ∧ noyau (simplexO n) = ∅ ∧ ¬ ContientDroite (F (simplexO n)) ∧
    (simplesS (simplexO n)).ncard = n + 1 := by
  obtain ⟨h1, h2, -, h4, h5⟩ := simplexO_hyps (n := n)
  have hne : (fun _ => (1 : ℝ)) ≠ (0 : Fin (n + 1) → ℝ) := fun h => by simpa using congrFun h 0
  exact ⟨h1, h2, ⟨_, mk_mem_ofCone hne fun i => one_pos⟩, h4, h5, simplexO_simplesS_ncard⟩

/-- **The instance: the open round cap** satisfies the hypotheses of Prop. 4 (`p = 1`). -/
theorem capS_hyps4 : IsConvexPart capS ∧ IsOpen capS ∧ capS.Nonempty ∧ noyau capS = ∅ ∧
    ¬ ContientDroite (F capS) ∧ simplesS capS = {⊤} := by
  obtain ⟨⟨h1, h2, -, h4, h5⟩, h6, -⟩ := capS_simplesS
  have hne : (![0, 0, 1] : V3) ≠ 0 := fun h => by simpa using congrFun h 2
  exact ⟨h1, h2, ⟨_, mk_mem_ofCone hne (by simp [rond])⟩, h4, h5, h6⟩

/-- The open simplex is the sum of its `n + 1` summands (an instance of `prop4_somme`). -/
theorem simplexO_prop4 {n : ℕ} : ∃ l : Fin (n + 1) ≃ simplesS (simplexO n),
    EstSommeS (simplexO n) (fun i => composanteS (simplexO n) (l i)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := simplexO_hyps4 (n := n)
  obtain ⟨hfin, -, -, h⟩ := prop4_somme h1 h2 h3 h4 h5
  haveI := hfin.fintype
  have hc : Fintype.card (simplesS (simplexO n)) = n + 1 := by
    have := Set.ncard_eq_toFinset_card' (simplesS (simplexO n))
    rw [Set.toFinset_card] at this
    omega
  exact ⟨(Fintype.equivFinOfCardEq hc).symm, (h _).1⟩

/-- **The instance of `prop4_permute`'s hypothesis `hg`**: the identity preserves the open
simplex, and the permutation it induces exists. -/
theorem simplexO_permute_id {n : ℕ} : ∃ σ : Equiv.Perm (simplesS (simplexO n)),
    ∀ L : simplesS (simplexO n),
      (σ L : Submodule ℝ (Fin (n + 1) → ℝ)).map
          ((LinearEquiv.refl ℝ (Fin (n + 1) → ℝ)) : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ)) = L ∧
        (LinearEquiv.refl ℝ (Fin (n + 1) → ℝ)) '' sommandeS (simplexO n) (σ L) =
          sommandeS (simplexO n) L := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := simplexO_hyps4 (n := n)
  exact prop4_permute h1 h2 h3 h4 h5 _ fun x => by
    rw [show LinearEquiv.refl ℝ (Fin (n + 1) → ℝ) = 1 from rfl, one_smul]

end BooleProjectifInstance

end Benzecri
