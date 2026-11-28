import Benzecri.Chapter3.BalayableSommeProp5
import Benzecri.Chapter3.SimplesSomme

/-!
# Chapter 3 § 2, the Corollary of Prop. 5: a sum of convexes is sweepable (resp. homogeneous) iff every summand is

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 3 § 2, journal p. 268; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch3.tex` (TO BE CHECKED BY THE AUTHOR).
Target T-bz-c3-balayable-somme-cor.

* `bzcor:c3s2p5c_balayable_somme_quelconque` — `benzecri1960_ch3.tex:623` (statement l.623–626,
  proof l.628–632), NOT marked: it carries Prop. 4's added hypothesis `¬ ContientDroite (F w)`
  (OQ-168, OQ-171) and the reading `w ≠ ∅`, as Prop. 5 does. PROVED with no `sorry`:
  `Benzecri.Sphere.corollaire_balayable_somme`: for `w` open, convex, nonempty, of empty noyau,
  without a line in `F(w)`, the sum (Déf. 5) of any finite family `vᵢ`, and for EVERY choice of
  bases `cᵢ : Lᵢ ≅ ℝ^{kᵢ+1}` of the supports `Lᵢ = span F(vᵢ)`, each `vᵢ` read in `S(kᵢ)` as
  `Vᵢ = s(cᵢ(F(vᵢ)))` is open, and `w` is sweepable (resp. homogeneous) iff every `Vᵢ` is.
  Bases exist (`Benzecri.Sphere.exists_bases_supports`); each `Vᵢ` satisfies Prop. 4's
  hypotheses (`Benzecri.Sphere.hyps4_lecture`).

> **Corollaire.** Soit $w$ un ouvert convexe de $S(\R^{n+1})$ de noyau vide, somme de $p$
> convexes $v_1$, \ldots, $v_i$, \ldots, $v_p$. $w$ est balayable (resp. homogène) si et
> seulement si les $v_i$ le sont.
>
> **Démonstration.** — On se ramène à une décomposition de $w$ en somme de convexes contenus dans
> des variétés distinguées simples et l'on applique la proposition précédente.

## The proof formalized

The printed route, made explicit. (1) *Each summand is a domain of the same kind*
(`hyps4_lecture`): with `πᵢ` the projection on `Lᵢ` along `⊕_{j≠i} Lⱼ` (`isCompl_supports`, from
`simplesS_somme_supports`), `F(vᵢ) = πᵢ(F(w))` (`F_summand_eq`), so `F(Vᵢ) = cᵢ(πᵢ(F(w)))` is open
(a surjective linear map is open); a line in `F(vᵢ)`, translated by points of the other `F(vⱼ)`,
is a line in `F(w)` (`not_contientDroite_summand`); the noyau of `Vᵢ` is empty since
`0 ∉ F(Vᵢ)` convex. (2) *The refinement* (« on se ramène… »): the simple distinguished
subvarieties of `w` are the images `φᵢ(t)`, `φᵢ = Lᵢ ↪ E ∘ cᵢ⁻¹`, of those `t` of the `Vᵢ`
(`simplesS_eq_iUnion_lecture`, from `simplesS_somme_supports`, `K̄(Vᵢ) = cᵢ(K̄(vᵢ) ∩ Lᵢ)`
(`closure_kPrime_lecture`) and the linear transport of simple subspaces `simples_image`); and
the Prop. 4 summands correspond, `P_{φᵢ t}(F(w)) = φᵢ(P_t(F(Vᵢ)))` (`sommandeS_lecture`: the two
projections agree on every simple subspace of `Vᵢ`, and `P_{φᵢ t}` kills every `Lⱼ`, `j ≠ i`).
(3) *Prop. 5 twice*: `prop5_lecture` restates `prop5_balayable_somme` basis-free (`Lecture`: « for
some basis »; the ⇐ direction chooses the bases, which Prop. 5 allows), and applied to `w` and to
every `Vᵢ` the two equivalences compose through (2) (`lecture_congr`).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `w` ouvert convexe de `S(ℝⁿ⁺¹)` | ✓ `IsOpen w`, `IsConvexPart w`, `w : Set (S m)` |
| `w` de noyau vide | ✓ `noyau w = ∅` |
| (not printed) `F(w)` contains no line | ⚠ strengthened (OQ-168, OQ-171), inherited from Prop. 4 / Prop. 5; whether the Corollary itself needs it is not settled here |
| (not printed) `w ≠ ∅` | ⚠ strengthened: `w.Nonempty`, as in Prop. 5 (for `w = ∅`, vacuously sweepable and homogeneous under Déf. 15, a Déf. 5 sum has some `vᵢ = ∅` and the others arbitrary, so the printed ⇒ is degenerate there; argued, not formalized) |
| `w` somme de `p` convexes `vᵢ` | ✓ Déf. 5, `EstSommeS w v`, `v : I → Set (S m)`, `I` any finite type; each `vᵢ` is then nonempty (`nonempty_F_summand`) |
| « les `vᵢ` le sont » | reading: `Vᵢ = s(cᵢ(F(vᵢ))) ⊆ S(kᵢ)`, `vᵢ` read in its support `Lᵢ = span F(vᵢ)` through a basis `cᵢ`, for EVERY bases `cᵢ` (they exist, `exists_bases_supports`); Déf. 15 `IsBalayable`, `IsHomogeneous` |

## SCOPE (disclosed)

* **Not marked.** Every assertion is proved, but under the added line-free hypothesis (OQ-168,
  OQ-171, both OPEN) and the readings above; the row stays partial until the author rules.
* **What is new here.** The transport of each `vᵢ` to `S(kᵢ)`, the correspondence of the simple
  subvarieties and of the Prop. 4 summands of `w` and of the `Vᵢ`, and the basis-free Prop. 5;
  the refinement itself is `simplesS_somme_supports` (T-bz-c3-simples-somme).
* **Instance.** The open `3`-simplex as the sum of its two open edges
  (`SimplesSommeInstance.simplexO_corollaire`: every hypothesis holds, with bases from
  `exists_bases_supports`); the ⇒ direction at work, `edges_isHomogeneous` (each open edge, read
  in `S(kᵢ)`, is homogeneous because the simplex is); the definition `Lecture` is
  inhabited by `simplexO_lecture_isHomogeneous`.
* No finding against the paper beyond the inherited OQ-168 / OQ-171 hypothesis and the `w ≠ ∅`
  reading.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Function
open scoped Pointwise

namespace Benzecri

attribute [local instance] t2Space_RnO

namespace Sphere

/-! ### Reading a cone of a subspace `s` in `S(n)` through a basis -/

section Lecture

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A property `P` of the open `s(b(A ∩ s))` of `S(n)`, read through SOME basis
`b : s ≅ ℝ^{n+1}`. -/
def Lecture (s : Submodule ℝ E) (A : Set E)
    (P : ∀ n : ℕ, TopologicalSpace.Opens (S n) → Prop) : Prop :=
  ∃ (n : ℕ) (b : s ≃ₗ[ℝ] (Fin (n + 1) → ℝ))
    (h : IsOpen (ofCone (b '' (Subtype.val ⁻¹' A)) : Set (S n))), P n ⟨_, h⟩

theorem lecture_congr {E' : Type*} [AddCommGroup E'] [Module ℝ E'] {s : Submodule ℝ E}
    {s' : Submodule ℝ E'} (e : s ≃ₗ[ℝ] s') {A : Set E} {A' : Set E'}
    (hA : (Subtype.val ⁻¹' A' : Set s') = e '' (Subtype.val ⁻¹' A))
    (P : ∀ n : ℕ, TopologicalSpace.Opens (S n) → Prop) :
    Lecture s A P ↔ Lecture s' A' P := by
  constructor
  · rintro ⟨n, b, h, hP⟩
    refine ⟨n, e.symm.trans b, ?_⟩
    have : ((e.symm.trans b : s' ≃ₗ[ℝ] _) : s' → _) '' (Subtype.val ⁻¹' A') =
        b '' (Subtype.val ⁻¹' A) := by
      rw [hA, Set.image_image]
      simp
    rw [this]
    exact ⟨h, hP⟩
  · rintro ⟨n, b, h, hP⟩
    refine ⟨n, e.trans b, ?_⟩
    have : ((e.trans b : s ≃ₗ[ℝ] _) : s → _) '' (Subtype.val ⁻¹' A) =
        b '' (Subtype.val ⁻¹' A') := by
      rw [hA, Set.image_image]
      simp
    rw [this]
    exact ⟨h, hP⟩

end Lecture

/-! ### Prop. 5 read summand by summand -/

section Prop5Lecture

variable {m : ℕ}

/-- **Prop. 5, basis-free**: for `X` satisfying Prop. 4's hypotheses, `X` is sweepable (resp.
homogeneous) iff, for every simple distinguished `s`, the summand `P_s(F(X))` read in `S(n)`
through some basis of `s` is. -/
theorem prop5_lecture {X : Set (S m)} (H : Hyps4 X) :
    (IsBalayable (GSR m) (S m) (⟨X, H.isOpen⟩ : TopologicalSpace.Opens (S m)) ↔
      ∀ s ∈ simplesS X, Lecture s (sommandeS X s) fun n U => IsBalayable (GSR n) (S n) U) ∧
    (IsHomogeneous (GSR m) (S m) (⟨X, H.isOpen⟩ : TopologicalSpace.Opens (S m)) ↔
      ∀ s ∈ simplesS X, Lecture s (sommandeS X s) fun n U => IsHomogeneous (GSR n) (S n) U) := by
  obtain ⟨hfin, hcard, -, -⟩ := prop4_somme H.convex H.isOpen H.nonempty H.noyau H.noLine
  haveI := hfin.to_subtype
  have hN : Nat.card (simplesS X) = (simplesS X).ncard - 1 + 1 := by
    rw [← Nat.card_coe_set_eq] at hcard ⊢; omega
  let l : Fin ((simplesS X).ncard - 1 + 1) ≃ simplesS X :=
    (finCongr hN.symm).trans (Finite.equivFin _).symm
  have hex : ∀ s ∈ simplesS X, ∃ j, ((l j : simplesS X) : Submodule ℝ (Fin (m + 1) → ℝ)) = s :=
    fun s hs => ⟨l.symm ⟨s, hs⟩, by simp⟩
  obtain ⟨n, ⟨b⟩⟩ := exists_bases_simplesS l
  obtain ⟨hB, hbal, hhom⟩ := prop5_balayable_somme H.convex H.isOpen H.nonempty H.noyau H.noLine l n b
  refine ⟨⟨fun hX s hs => ?_, fun h => ?_⟩, ⟨fun hX s hs => ?_, fun h => ?_⟩⟩
  · obtain ⟨j, rfl⟩ := hex s hs
    exact ⟨n j, b j, hB j, hbal.1 hX j⟩
  · choose n' b' hB' hP using fun j => h (l j) (l j).2
    obtain ⟨hB'', hbal', -⟩ :=
      prop5_balayable_somme H.convex H.isOpen H.nonempty H.noyau H.noLine l n' b'
    exact hbal'.2 hP
  · obtain ⟨j, rfl⟩ := hex s hs
    exact ⟨n j, b j, hB j, hhom.1 hX j⟩
  · choose n' b' hB' hP using fun j => h (l j) (l j).2
    obtain ⟨hB'', -, hhom'⟩ :=
      prop5_balayable_somme H.convex H.isOpen H.nonempty H.noyau H.noLine l n' b'
    exact hhom'.2 hP

end Prop5Lecture

/-! ### Linear transport of simple distinguished subspaces -/

section Transport

variable {E E' : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup E'] [Module ℝ E']

theorem estDistingue_map_of (e : E ≃ₗ[ℝ] E') {W : Set E} {N : Submodule ℝ E}
    (h : EstDistingue W N) : EstDistingue (e '' W) (N.map (e : E →ₗ[ℝ] E')) := by
  obtain ⟨N', hc, hW⟩ := h
  refine ⟨N'.map (e : E →ₗ[ℝ] E'), ⟨hc.1.map_orderIso (Submodule.orderIsoMapComap e),
    hc.2.map_orderIso (Submodule.orderIsoMapComap e)⟩, ?_⟩
  show e '' W = ((N.map (e : E →ₗ[ℝ] E') : Submodule ℝ E') : Set E') ∩ e '' W +
    ((N'.map (e : E →ₗ[ℝ] E') : Submodule ℝ E') : Set E') ∩ e '' W
  rw [Submodule.map_coe, Submodule.map_coe, LinearEquiv.coe_coe,
    ← Set.image_inter e.injective, ← Set.image_inter e.injective, ← Set.image_add e]
  exact congrArg _ hW

theorem estDistingue_image (e : E ≃ₗ[ℝ] E') {W : Set E} {N : Submodule ℝ E} :
    EstDistingue (e '' W) (N.map (e : E →ₗ[ℝ] E')) ↔ EstDistingue W N := by
  refine ⟨fun h => ?_, estDistingue_map_of e⟩
  have := estDistingue_map_of e.symm h
  rwa [show (e.symm : E' → E) '' (e '' W) = W from e.toEquiv.symm_image_image W, ← Submodule.map_comp, LinearEquiv.symm_comp,
    Submodule.map_id] at this

theorem estSimple_image (e : E ≃ₗ[ℝ] E') {W : Set E} {N : Submodule ℝ E} :
    EstSimple (e '' W) (N.map (e : E →ₗ[ℝ] E')) ↔ EstSimple W N := by
  have hinj : Injective (e : E →ₗ[ℝ] E') := e.injective
  have hbot : ∀ M : Submodule ℝ E, M.map (e : E →ₗ[ℝ] E') = ⊥ ↔ M = ⊥ := fun _ =>
    Submodule.map_eq_bot_iff
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨(estDistingue_image e).1 h1, fun hN => h2 ((hbot N).2 hN), fun M hM hM0 hle => ?_⟩
    exact Submodule.map_injective_of_injective hinj (h3 _ ((estDistingue_image e).2 hM)
      (fun h => hM0 ((hbot M).1 h)) (Submodule.map_mono hle))
  · rintro ⟨h1, h2, h3⟩
    refine ⟨(estDistingue_image e).2 h1, fun hN => h2 ((hbot N).1 hN), fun M hM hM0 hle => ?_⟩
    obtain ⟨M', rfl⟩ : ∃ M', M'.map (e : E →ₗ[ℝ] E') = M :=
      ⟨M.map (e.symm : E' →ₗ[ℝ] E), by
        rw [← Submodule.map_comp, LinearEquiv.comp_symm, Submodule.map_id]⟩
    rw [h3 M' ((estDistingue_image e).1 hM) (fun h => hM0 ((hbot M').2 h))
      ((Submodule.map_le_map_iff_of_injective hinj _ _).1 hle)]

theorem simples_image (e : E ≃ₗ[ℝ] E') (W : Set E) :
    simples (e '' W) = Submodule.map (e : E →ₗ[ℝ] E') '' simples W := by
  ext M
  constructor
  · intro hM
    refine ⟨M.map (e.symm : E' →ₗ[ℝ] E), ?_, ?_⟩
    · have h : M = (M.map (e.symm : E' →ₗ[ℝ] E)).map (e : E →ₗ[ℝ] E') := by
        rw [← Submodule.map_comp, LinearEquiv.comp_symm, Submodule.map_id]
      have hM' : EstSimple (e '' W) M := hM
      rw [h] at hM'
      exact (estSimple_image e).1 hM'
    · rw [← Submodule.map_comp, LinearEquiv.comp_symm, Submodule.map_id]
  · rintro ⟨N, hN, rfl⟩
    exact (estSimple_image e).2 hN

end Transport

/-! ### The summands of a sum -/

section Summands

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {I : Type*} [Fintype I] {w : Set (Sphere E)} {v : I → Set (Sphere E)}

theorem nonempty_F_summand (H : Hyps4 w) (hs : EstSommeS w v) (i : I) : (F (v i)).Nonempty := by
  obtain ⟨u, hu⟩ := H.exists_mem_F
  obtain ⟨-, hbij⟩ := (isSommeConvexes_iff_bijOn _ _).1 hs.2
  obtain ⟨y, hy, -⟩ := hbij.surjOn hu
  exact ⟨y i, hy i (mem_univ i)⟩

/-- A family `y` of points of the `F(vⱼ)`. -/
theorem exists_family_F (H : Hyps4 w) (hs : EstSommeS w v) : ∃ y : I → E, ∀ j, y j ∈ F (v j) :=
  ⟨fun j => (nonempty_F_summand H hs j).some, fun j => (nonempty_F_summand H hs j).some_mem⟩

theorem isCompl_supports (H : Hyps4 w) (hs : EstSommeS w v) (i : I) :
    IsCompl (Submodule.span ℝ (F (v i))) (⨆ (j) (_ : j ≠ i), Submodule.span ℝ (F (v j))) := by
  exact isCompl_iSup_ne (iSupIndep_supports H.supportK_eq hs)
    (iSup_eq_top_of_estSommeS H.supportK_eq hs fun j => subset_supportK (v j)) i

theorem projection_sum_supports (H : Hyps4 w) (hs : EstSommeS w v) (i : I) (y : I → E)
    (hy : ∀ j, y j ∈ Submodule.span ℝ (F (v j))) :
    (Submodule.span ℝ (F (v i))).projection _ (isCompl_supports H hs i) (∑ j, y j) = y i := by
  rw [map_sum, Finset.sum_eq_single i (fun j _ hji => ?_) (by simp),
    Submodule.projection_apply_of_mem_left _ (hy i)]
  exact Submodule.projection_apply_of_mem_right _
    ((le_iSup₂ (f := fun k (_ : k ≠ i) => Submodule.span ℝ (F (v k))) j hji) (hy j))

/-- `F(vᵢ)` is the projection of `F(w)` on `Lᵢ = span F(vᵢ)` along `⊕_{j≠i} Lⱼ`. -/
theorem F_summand_eq (H : Hyps4 w) (hs : EstSommeS w v) (i : I) :
    F (v i) = (Submodule.span ℝ (F (v i))).projection _ (isCompl_supports H hs i) '' F w := by
  classical
  obtain ⟨-, hbij⟩ := (isSommeConvexes_iff_bijOn _ _).1 hs.2
  obtain ⟨y, hy⟩ := exists_family_F H hs
  ext x
  constructor
  · intro hx
    have hz : Function.update y i x ∈ univ.pi fun j => F (v j) := fun j _ => by
      by_cases hj : j = i
      · subst hj; simpa using hx
      · rw [Function.update_of_ne hj]; exact hy j
    refine ⟨_, hbij.mapsTo hz, ?_⟩
    rw [projection_sum_supports H hs i _ fun j => Submodule.subset_span (hz j (mem_univ j)),
      Function.update_self]
  · rintro ⟨x', hx', rfl⟩
    obtain ⟨z, hz, rfl⟩ := hbij.surjOn hx'
    rw [show (fun x : I → E => ∑ j, x j) z = ∑ j, z j from rfl,
      projection_sum_supports H hs i _ fun j => Submodule.subset_span (hz j (mem_univ j))]
    exact hz i (mem_univ i)

theorem not_contientDroite_summand (H : Hyps4 w) (hs : EstSommeS w v) (i : I) :
    ¬ ContientDroite (F (v i)) := by
  classical
  rintro ⟨x, d, hd0, hline⟩
  obtain ⟨-, hbij⟩ := (isSommeConvexes_iff_bijOn _ _).1 hs.2
  obtain ⟨y, hy⟩ := exists_family_F H hs
  refine H.noLine ⟨∑ j, Function.update y i x j, d, hd0, fun t => ?_⟩
  have hz : Function.update y i (x + t • d) ∈ univ.pi fun j => F (v j) := fun j _ => by
    by_cases hj : j = i
    · subst hj; simpa using hline t
    · rw [Function.update_of_ne hj]; exact hy j
  have := hbij.mapsTo hz
  convert this using 1
  show _ = ∑ j, Function.update y i (x + t • d) j
  rw [Finset.sum_update_of_mem (Finset.mem_univ i), Finset.sum_update_of_mem (Finset.mem_univ i)]
  abel

end Summands

/-! ### Each summand read in `S(kᵢ)` -/

section Read

variable {m : ℕ} {I : Type*} [Fintype I] {w : Set (S m)} {v : I → Set (S m)}

omit [Fintype I] in
theorem isPosCone_lecture (i : I) {k : ℕ}
    (c : Submodule.span ℝ (F (v i)) ≃ₗ[ℝ] (Fin (k + 1) → ℝ)) :
    IsPosCone (c '' (Subtype.val ⁻¹' F (v i))) := by
  refine isPosCone_image c.toLinearMap fun t ht u hu => ?_
  show ((t • u : Submodule.span ℝ (F (v i))) : Fin (m + 1) → ℝ) ∈ F (v i)
  rw [Submodule.coe_smul]
  exact smul_mem_F hu ht

omit [Fintype I] in
theorem zero_notMem_lecture (i : I) {k : ℕ}
    (c : Submodule.span ℝ (F (v i)) ≃ₗ[ℝ] (Fin (k + 1) → ℝ)) :
    (0 : Fin (k + 1) → ℝ) ∉ c '' (Subtype.val ⁻¹' F (v i)) := by
  rintro ⟨u, hu, hu0⟩
  rw [LinearEquiv.map_eq_zero_iff] at hu0
  subst hu0
  exact zero_notMem_F _ hu

omit [Fintype I] in
theorem F_lecture (i : I) {k : ℕ} (c : Submodule.span ℝ (F (v i)) ≃ₗ[ℝ] (Fin (k + 1) → ℝ)) :
    F (ofCone (c '' (Subtype.val ⁻¹' F (v i))) : Set (S k)) = c '' (Subtype.val ⁻¹' F (v i)) :=
  F_ofCone_of_zero_notMem (isPosCone_lecture i c) (zero_notMem_lecture i c)

/-- **Each summand, read through a basis of its support, satisfies Prop. 4's hypotheses.** -/
theorem hyps4_lecture (H : Hyps4 w) (hs : EstSommeS w v) (i : I) {k : ℕ}
    (c : Submodule.span ℝ (F (v i)) ≃ₗ[ℝ] (Fin (k + 1) → ℝ)) :
    Hyps4 (ofCone (c '' (Subtype.val ⁻¹' F (v i))) : Set (S k)) := by
  have hpos := isPosCone_lecture i c
  have h0 := zero_notMem_lecture i c
  have hFV := F_lecture i c
  have hconvD : Convex ℝ (c '' (Subtype.val ⁻¹' F (v i))) :=
    ((hs.1 i).linear_preimage (Submodule.span ℝ (F (v i))).subtype).linear_image c.toLinearMap
  have hconv : IsConvexPart (ofCone (c '' (Subtype.val ⁻¹' F (v i))) : Set (S k)) := isConvexPart_ofCone_of_cone hconvD hpos
  have hc := isCompl_supports H hs i
  have hDeq : (c '' (Subtype.val ⁻¹' F (v i))) = (c.toLinearMap ∘ₗ (Submodule.span ℝ (F (v i))).projectionOnto _ hc) '' F w := by
    have hC : (Subtype.val ⁻¹' F (v i) : Set (Submodule.span ℝ (F (v i)))) = (Submodule.span ℝ (F (v i))).projectionOnto _ hc '' F w := by
      ext u
      rw [mem_preimage, Set.ext_iff.1 (F_summand_eq H hs i) (u : Fin (m + 1) → ℝ)]
      constructor
      · rintro ⟨x, hx, hxu⟩
        exact ⟨x, hx, Subtype.ext hxu⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, rfl⟩
    rw [LinearMap.coe_comp, Set.image_comp, ← hC]
    rfl
  have hDo : IsOpen (c '' (Subtype.val ⁻¹' F (v i))) := by
    rw [hDeq]
    exact LinearMap.isOpenMap_of_finiteDimensional _
      (c.surjective.comp (Submodule.projectionOnto_surjective hc) :) _ H.isOpen_F
  refine ⟨hconv, isOpen_ofCone' hpos hDo, ?_, ?_, ?_⟩
  · obtain ⟨y, hy⟩ := nonempty_F_summand H hs i
    have hu : c ⟨y, Submodule.subset_span hy⟩ ∈ (c '' (Subtype.val ⁻¹' F (v i))) := ⟨_, hy, rfl⟩
    exact ⟨_, mk_mem_ofCone (fun e => h0 (e ▸ hu)) hu⟩
  · rw [noyau_eq hconv]
    refine eq_empty_of_forall_notMem fun x ⟨hx, hnx⟩ => ?_
    obtain ⟨u, hu, huD, rfl⟩ := mem_ofCone.1 hx
    rw [neg_mk, mk_mem_ofCone_iff hpos] at hnx
    apply h0
    have := hconvD huD hnx (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    rwa [smul_neg, add_neg_cancel] at this
  · rw [hFV]
    rintro ⟨x, d, hd0, hl⟩
    refine not_contientDroite_summand H hs i
      ⟨((c.symm x : Submodule.span ℝ (F (v i))) : Fin (m + 1) → ℝ), ((c.symm d : Submodule.span ℝ (F (v i))) : Fin (m + 1) → ℝ), ?_, fun t => ?_⟩
    · intro h
      apply hd0
      have : c.symm d = 0 := Subtype.ext h
      simpa using this
    · obtain ⟨u, hu, hux⟩ := hl t
      have : u = c.symm x + t • c.symm d := by
        rw [← map_smul, ← map_add, ← hux, c.symm_apply_apply]
      rw [this] at hu
      simpa using hu

/-- The supports have bases: `kᵢ + 1 = dim Lᵢ`. -/
theorem exists_bases_supports (H : Hyps4 w) (hs : EstSommeS w v) :
    ∃ k : I → ℕ, Nonempty (∀ i, Submodule.span ℝ (F (v i)) ≃ₗ[ℝ] (Fin (k i + 1) → ℝ)) := by
  have hpos : ∀ i, 0 < Module.finrank ℝ (Submodule.span ℝ (F (v i))) := fun i =>
    Nat.pos_of_ne_zero fun h => by
      obtain ⟨y, hy⟩ := nonempty_F_summand H hs i
      have hbot := Submodule.finrank_eq_zero.1 h
      have : y ∈ (⊥ : Submodule ℝ (Fin (m + 1) → ℝ)) := hbot ▸ Submodule.subset_span hy
      rw [Submodule.mem_bot] at this
      exact zero_notMem_F _ (this ▸ hy)
  refine ⟨fun i => Module.finrank ℝ (Submodule.span ℝ (F (v i))) - 1, ⟨fun i =>
    LinearEquiv.ofFinrankEq _ _ ?_⟩⟩
  rw [Module.finrank_fin_fun]
  have := hpos i
  show _ = Module.finrank ℝ (Submodule.span ℝ (F (v i))) - 1 + 1
  omega

omit [Fintype I] in
theorem closure_kPrime_lecture (i : I) {k : ℕ}
    (c : Submodule.span ℝ (F (v i)) ≃ₗ[ℝ] (Fin (k + 1) → ℝ)) :
    closure (kPrime (ofCone (c '' (Subtype.val ⁻¹' F (v i))) : Set (S k))) =
      c '' ((Submodule.span ℝ (F (v i))).subtype ⁻¹' closure (kPrime (v i))) := by
  have hK : kPrime (ofCone (c '' (Subtype.val ⁻¹' F (v i))) : Set (S k)) =
      c '' ((Submodule.span ℝ (F (v i))).subtype ⁻¹' kPrime (v i)) := by
    rw [kPrime, F_lecture i c]
    ext z
    constructor
    · rintro (rfl | ⟨u, hu, rfl⟩)
      · exact ⟨0, zero_mem_kPrime _, map_zero c⟩
      · exact ⟨u, mem_insert_of_mem _ hu, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      rcases mem_insert_iff.1 hu with hu0 | hu
      · have : u = 0 := Subtype.ext hu0
        subst this
        rw [map_zero]
        exact mem_insert _ _
      · exact mem_insert_of_mem _ ⟨u, hu, rfl⟩
  have hsub : kPrime (v i) ⊆ Set.range (Subtype.val : Submodule.span ℝ (F (v i)) → Fin (m + 1) → ℝ) := fun x hx =>
    ⟨⟨x, kPrime_subset_of_subset_linearSubvariety (subset_supportK (v i)) hx⟩, rfl⟩
  have hcl : closure ((Submodule.span ℝ (F (v i))).subtype ⁻¹' kPrime (v i)) = (Submodule.span ℝ (F (v i))).subtype ⁻¹' closure (kPrime (v i)) := by
    rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
    show _ = Subtype.val ⁻¹' _
    congr 2
    exact Set.image_preimage_eq_of_subset hsub
  rw [hK, ← hcl, ← LinearEquiv.coe_toContinuousLinearEquiv' c,
    ContinuousLinearEquiv.image_closure]

/-- **The simple ones of `w` are those of the summands, read in `S(kᵢ)`.** -/
theorem simplesS_eq_iUnion_lecture (H : Hyps4 w) (hs : EstSommeS w v) (k : I → ℕ)
    (c : ∀ i, Submodule.span ℝ (F (v i)) ≃ₗ[ℝ] (Fin (k i + 1) → ℝ)) :
    simplesS w = ⋃ i, Submodule.map ((Submodule.span ℝ (F (v i))).subtype ∘ₗ
      ((c i).symm : (Fin (k i + 1) → ℝ) →ₗ[ℝ] _)) ''
        simplesS (ofCone (c i '' (Subtype.val ⁻¹' F (v i))) : Set (S (k i))) := by
  rw [(simplesS_somme_supports H.convex H.isOpen H.supportK_eq H.noyau H.noLine hs).2.2.2.1]
  refine congrArg _ (funext fun i => ?_)
  rw [(hyps4_lecture H hs i (c i)).simplesS_eq', closure_kPrime_lecture i (c i), simples_image,
    Set.image_image]
  refine Set.image_congr fun N _ => ?_
  rw [← Submodule.map_comp]
  congr 1
  ext x
  simp

/-- **The summands match**: for a simple `t` of the read summand, `P_{φ t}(F(w)) = φ(P_t(F(Vᵢ)))`. -/
theorem sommandeS_lecture (H : Hyps4 w) (hs : EstSommeS w v) (k : I → ℕ)
    (c : ∀ i, Submodule.span ℝ (F (v i)) ≃ₗ[ℝ] (Fin (k i + 1) → ℝ)) (i : I)
    {t : Submodule ℝ (Fin (k i + 1) → ℝ)}
    (ht : t ∈ simplesS (ofCone (c i '' (Subtype.val ⁻¹' F (v i))) : Set (S (k i)))) :
    sommandeS w (Submodule.map ((Submodule.span ℝ (F (v i))).subtype ∘ₗ
      ((c i).symm : (Fin (k i + 1) → ℝ) →ₗ[ℝ] _)) t) =
      ((Submodule.span ℝ (F (v i))).subtype ∘ₗ ((c i).symm : (Fin (k i + 1) → ℝ) →ₗ[ℝ] _)) ''
        sommandeS (ofCone (c i '' (Subtype.val ⁻¹' F (v i))) : Set (S (k i))) t := by
  classical
  have HV := hyps4_lecture H hs i (c i)
  have hsup := simplesS_somme_supports H.convex H.isOpen H.supportK_eq H.noyau H.noLine hs
  obtain ⟨-, hbij⟩ := (isSommeConvexes_iff_bijOn _ _).1 hs.2
  have hinj : Injective ((Submodule.span ℝ (F (v i))).subtype ∘ₗ
      ((c i).symm : (Fin (k i + 1) → ℝ) →ₗ[ℝ] _)) :=
    Subtype.val_injective.comp (c i).symm.injective
  have hmap : ∀ M ∈ simplesS (ofCone (c i '' (Subtype.val ⁻¹' F (v i))) : Set (S (k i))),
      Submodule.map ((Submodule.span ℝ (F (v i))).subtype ∘ₗ
        ((c i).symm : (Fin (k i + 1) → ℝ) →ₗ[ℝ] _)) M ∈ simplesS w := fun M hM => by
    rw [simplesS_eq_iUnion_lecture H hs k c]
    exact mem_iUnion.2 ⟨i, M, hM, rfl⟩
  have hsS := hmap t ht
  -- the two projections correspond
  have key : ∀ x, projS w (Submodule.map ((Submodule.span ℝ (F (v i))).subtype ∘ₗ
      ((c i).symm : (Fin (k i + 1) → ℝ) →ₗ[ℝ] _)) t)
        (((Submodule.span ℝ (F (v i))).subtype ∘ₗ ((c i).symm : (Fin (k i + 1) → ℝ) →ₗ[ℝ] _)) x) =
      ((Submodule.span ℝ (F (v i))).subtype ∘ₗ ((c i).symm : (Fin (k i + 1) → ℝ) →ₗ[ℝ] _))
        (projS (ofCone (c i '' (Subtype.val ⁻¹' F (v i))) : Set (S (k i))) t x) := by
    intro x
    have hle : sSup (simplesS (ofCone (c i '' (Subtype.val ⁻¹' F (v i))) : Set (S (k i)))) ≤
        LinearMap.eqLocus
          (projS w (Submodule.map ((Submodule.span ℝ (F (v i))).subtype ∘ₗ
            ((c i).symm : (Fin (k i + 1) → ℝ) →ₗ[ℝ] _)) t) ∘ₗ
            ((Submodule.span ℝ (F (v i))).subtype ∘ₗ ((c i).symm : (Fin (k i + 1) → ℝ) →ₗ[ℝ] _)))
          (((Submodule.span ℝ (F (v i))).subtype ∘ₗ ((c i).symm : (Fin (k i + 1) → ℝ) →ₗ[ℝ] _)) ∘ₗ
            projS (ofCone (c i '' (Subtype.val ⁻¹' F (v i))) : Set (S (k i))) t) :=
      sSup_le fun M hM y hy => by
        show projS w _ (_ : Fin (m + 1) → ℝ) = _
        rw [H.projS_apply_of_mem hsS (hmap M hM) (Submodule.mem_map_of_mem hy),
          LinearMap.comp_apply (g := projS (ofCone (c i '' (Subtype.val ⁻¹' F (v i))) : Set (S (k i))) t),
          HV.projS_apply_of_mem ht hM hy]
        by_cases hMt : M = t
        · subst hMt; simp
        · rw [if_neg hMt, if_neg fun h => hMt (Submodule.map_injective_of_injective hinj h),
            map_zero]
    exact hle (HV.sSup_simplesS ▸ Submodule.mem_top)
  -- `φ t` lies in `Lᵢ`, and its projection kills the other supports
  have hsle : Submodule.map ((Submodule.span ℝ (F (v i))).subtype ∘ₗ
      ((c i).symm : (Fin (k i + 1) → ℝ) →ₗ[ℝ] _)) t ≤ Submodule.span ℝ (F (v i)) := by
    rintro _ ⟨x, -, rfl⟩
    exact ((c i).symm x).2
  have hkill : ∀ j, j ≠ i → ∀ y ∈ Submodule.span ℝ (F (v j)),
      projS w (Submodule.map ((Submodule.span ℝ (F (v i))).subtype ∘ₗ
        ((c i).symm : (Fin (k i + 1) → ℝ) →ₗ[ℝ] _)) t) y = 0 := by
    intro j hji y hy
    rw [← hsup.2.2.2.2.2 j] at hy
    refine (sSup_le (fun M hM z hz => ?_) : _ ≤ LinearMap.ker _) hy
    obtain ⟨hM, hMj⟩ := hM
    rw [LinearMap.mem_ker, H.projS_apply_of_mem hsS hM hz, if_neg]
    rintro rfl
    obtain ⟨i', -, hu⟩ := hsup.2.2.2.2.1 _ hsS
    exact hji ((hu j hMj).trans (hu i hsle).symm)
  -- `P_{φ t}(F(w)) = P_{φ t}(F(vᵢ))`
  have hsom : sommandeS w (Submodule.map ((Submodule.span ℝ (F (v i))).subtype ∘ₗ
      ((c i).symm : (Fin (k i + 1) → ℝ) →ₗ[ℝ] _)) t) =
      projS w (Submodule.map ((Submodule.span ℝ (F (v i))).subtype ∘ₗ
        ((c i).symm : (Fin (k i + 1) → ℝ) →ₗ[ℝ] _)) t) '' F (v i) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨y, hy, rfl⟩ := hbij.surjOn hx
      show projS w _ (∑ j, y j) ∈ _
      rw [map_sum, Finset.sum_eq_single i
        (fun j _ hji => hkill j hji (y j) (Submodule.subset_span (hy j (mem_univ j))))
        (by simp)]
      exact ⟨y i, hy i (mem_univ i), rfl⟩
    · rintro ⟨y', hy', rfl⟩
      obtain ⟨y, hy⟩ := exists_family_F H hs
      have hz : Function.update y i y' ∈ univ.pi fun j => F (v j) := fun j _ => by
        by_cases hj : j = i
        · subst hj; simpa using hy'
        · rw [Function.update_of_ne hj]; exact hy j
      refine ⟨_, hbij.mapsTo hz, ?_⟩
      show projS w _ (∑ j, Function.update y i y' j) = _
      rw [map_sum, Finset.sum_eq_single i (fun j _ hji => hkill j hji _
        (Submodule.subset_span (hz j (mem_univ j)))) (by simp), Function.update_self]
  -- `F(vᵢ) = φ(F(Vᵢ))`
  have hFv : F (v i) = ((Submodule.span ℝ (F (v i))).subtype ∘ₗ
      ((c i).symm : (Fin (k i + 1) → ℝ) →ₗ[ℝ] _)) ''
        F (ofCone (c i '' (Subtype.val ⁻¹' F (v i))) : Set (S (k i))) := by
    rw [F_lecture i (c i), Set.image_image]
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.symm_apply_apply, Submodule.coe_subtype]
    exact (Set.image_preimage_eq_of_subset fun x hx =>
      ⟨⟨x, Submodule.subset_span hx⟩, rfl⟩).symm
  rw [hsom, congrArg (fun X => projS w (Submodule.map ((Submodule.span ℝ (F (v i))).subtype ∘ₗ
      ((c i).symm : (Fin (k i + 1) → ℝ) →ₗ[ℝ] _)) t) '' X) hFv]
  rw [Set.image_image, sommandeS, Set.image_image]
  exact Set.image_congr fun x _ => key x

/-- The summands match, read in the subspaces: through `φ : t ≅ φ(t)`. -/
theorem preimage_sommandeS_lecture (H : Hyps4 w) (hs : EstSommeS w v) (k : I → ℕ)
    (c : ∀ i, Submodule.span ℝ (F (v i)) ≃ₗ[ℝ] (Fin (k i + 1) → ℝ)) (i : I)
    {t : Submodule ℝ (Fin (k i + 1) → ℝ)}
    (ht : t ∈ simplesS (ofCone (c i '' (Subtype.val ⁻¹' F (v i))) : Set (S (k i)))) :
    (Subtype.val ⁻¹' sommandeS w (Submodule.map ((Submodule.span ℝ (F (v i))).subtype ∘ₗ
      ((c i).symm : (Fin (k i + 1) → ℝ) →ₗ[ℝ] _)) t) : Set (Submodule.map
        ((Submodule.span ℝ (F (v i))).subtype ∘ₗ ((c i).symm : (Fin (k i + 1) → ℝ) →ₗ[ℝ] _)) t)) =
      (Submodule.equivMapOfInjective _ (Subtype.val_injective.comp (c i).symm.injective) t) ''
        (Subtype.val ⁻¹' sommandeS (ofCone (c i '' (Subtype.val ⁻¹' F (v i))) : Set (S (k i))) t) := by
  have HV := hyps4_lecture H hs i (c i)
  rw [sommandeS_lecture H hs k c i ht]
  ext u
  constructor
  · rintro ⟨x, hx, hxu⟩
    refine ⟨⟨x, HV.sommande_subset ht hx⟩, hx, Subtype.ext ?_⟩
    rw [Submodule.coe_equivMapOfInjective_apply]
    exact hxu
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, (Submodule.coe_equivMapOfInjective_apply _ _ _ _).symm⟩

/-- **The Corollary of Prop. 5** (`bzcor:c3s2p5c_balayable_somme_quelconque`, NOT marked:
OQ-168, OQ-171). -/
theorem corollaire_balayable_somme (hw : IsConvexPart w) (hopen : IsOpen w) (hne : w.Nonempty)
    (hn : noyau w = ∅) (hd : ¬ ContientDroite (F w)) (hs : EstSommeS w v) (k : I → ℕ)
    (c : ∀ i, Submodule.span ℝ (F (v i)) ≃ₗ[ℝ] (Fin (k i + 1) → ℝ)) :
    ∃ hV : ∀ i, IsOpen (ofCone (c i '' (Subtype.val ⁻¹' F (v i))) : Set (S (k i))),
      (IsBalayable (GSR m) (S m) (⟨w, hopen⟩ : TopologicalSpace.Opens (S m)) ↔
        ∀ i, IsBalayable (GSR (k i)) (S (k i)) (⟨_, hV i⟩ : TopologicalSpace.Opens (S (k i)))) ∧
      (IsHomogeneous (GSR m) (S m) (⟨w, hopen⟩ : TopologicalSpace.Opens (S m)) ↔
        ∀ i, IsHomogeneous (GSR (k i)) (S (k i))
          (⟨_, hV i⟩ : TopologicalSpace.Opens (S (k i)))) := by
  have H : Hyps4 w := ⟨hw, hopen, hne, hn, hd⟩
  have HV := fun i => hyps4_lecture H hs i (c i)
  refine ⟨fun i => (HV i).isOpen, ?_⟩
  have chain : ∀ P : ∀ n : ℕ, TopologicalSpace.Opens (S n) → Prop,
      (∀ s ∈ simplesS w, Lecture s (sommandeS w s) P) ↔
        ∀ i, ∀ t ∈ simplesS (ofCone (c i '' (Subtype.val ⁻¹' F (v i))) : Set (S (k i))),
          Lecture t (sommandeS (ofCone (c i '' (Subtype.val ⁻¹' F (v i))) : Set (S (k i))) t) P := by
    intro P
    constructor
    · intro h i t ht
      have h' := h _ (by
        rw [simplesS_eq_iUnion_lecture H hs k c]
        exact mem_iUnion.2 ⟨i, t, ht, rfl⟩)
      exact (lecture_congr _ (preimage_sommandeS_lecture H hs k c i ht) P).2 h'
    · intro h s hs'
      rw [simplesS_eq_iUnion_lecture H hs k c] at hs'
      obtain ⟨i, t, ht, rfl⟩ := mem_iUnion.1 hs'
      exact (lecture_congr _ (preimage_sommandeS_lecture H hs k c i ht) P).1 (h i t ht)
  obtain ⟨hb, hh⟩ := prop5_lecture H
  exact ⟨hb.trans ((chain _).trans (forall_congr' fun i => (prop5_lecture (HV i)).1.symm)),
    hh.trans ((chain _).trans (forall_congr' fun i => (prop5_lecture (HV i)).2.symm))⟩

end Read

end Sphere

/-! ### Instance: the open `3`-simplex as the sum of its two open edges -/

namespace SimplesSommeInstance

open Sphere BooleProjectifInstance

theorem simplexO_corollaire :
    ∃ (k : Fin 2 → ℕ) (c : ∀ i, Submodule.span ℝ (F (edges i)) ≃ₗ[ℝ] (Fin (k i + 1) → ℝ))
      (hV : ∀ i, IsOpen (ofCone (c i '' (Subtype.val ⁻¹' F (edges i))) : Set (S (k i)))),
      (IsBalayable (GSR 3) (S 3)
          (⟨simplexO 3, simplexO_hyps4.2.1⟩ : TopologicalSpace.Opens (S 3)) ↔
        ∀ i, IsBalayable (GSR (k i)) (S (k i)) (⟨_, hV i⟩ : TopologicalSpace.Opens (S (k i)))) ∧
      (IsHomogeneous (GSR 3) (S 3)
          (⟨simplexO 3, simplexO_hyps4.2.1⟩ : TopologicalSpace.Opens (S 3)) ↔
        ∀ i, IsHomogeneous (GSR (k i)) (S (k i)) (⟨_, hV i⟩ : TopologicalSpace.Opens (S (k i)))) := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := simplexO_hyps4 (n := 3)
  obtain ⟨k, ⟨c⟩⟩ := exists_bases_supports ⟨h1, h2, h3, h4, h5⟩ simplexO_estSommeS_edges
  exact ⟨k, c, corollaire_balayable_somme h1 h2 h3 h4 h5 simplexO_estSommeS_edges k c⟩

/-- **An instance of `Lecture`**: the open `n`-simplex has `n + 1` simple distinguished
subvarieties, and each of its Prop. 4 summands, read in `S(kₛ)` through some basis, is
homogeneous (by `prop5_lecture` ⇒ and `simplexO_isHomogeneous`). -/
theorem simplexO_lecture_isHomogeneous {n : ℕ} :
    (simplesS (simplexO n)).ncard = n + 1 ∧ ∀ s ∈ simplesS (simplexO n),
      Lecture s (sommandeS (simplexO n) s) fun k U => IsHomogeneous (GSR k) (S k) U := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := simplexO_hyps4 (n := n)
  exact ⟨simplexO_simplesS_ncard, (prop5_lecture ⟨h1, h2, h3, h4, h5⟩).2.1 simplexO_isHomogeneous⟩

/-- The Corollary ⇒ at work: each open edge of the open `3`-simplex, read in `S(kᵢ)`, is
homogeneous, because the simplex is. -/
theorem edges_isHomogeneous :
    ∃ (k : Fin 2 → ℕ) (c : ∀ i, Submodule.span ℝ (F (edges i)) ≃ₗ[ℝ] (Fin (k i + 1) → ℝ))
      (hV : ∀ i, IsOpen (ofCone (c i '' (Subtype.val ⁻¹' F (edges i))) : Set (S (k i)))),
      ∀ i, IsHomogeneous (GSR (k i)) (S (k i)) (⟨_, hV i⟩ : TopologicalSpace.Opens (S (k i))) := by
  obtain ⟨k, c, hV, -, hh⟩ := simplexO_corollaire
  exact ⟨k, c, hV, hh.1 simplexO_isHomogeneous⟩

end SimplesSommeInstance

end Benzecri
