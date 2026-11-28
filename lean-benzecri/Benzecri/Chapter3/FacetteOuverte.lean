import Benzecri.Chapter3.Facettes
import Benzecri.Chapter3.FinestLocallyConvex

/-!
# Chapter 3 § 1, Prop. 1 — a facette is open in its support, for the finest locally convex topology

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 3 § 1, journal p. 260; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch3.tex`. Target T-bz-c3-facette-ouverte. Over an
arbitrary real vector space `E`, any dimension, no topology on `E`.

* **`bzprop:c3s1p1_facette_ouverte`** — `benzecri1960_ch3.tex:141` (Prop. 1, l.141–144, proof
  l.146–150) — `Benzecri.facette_isOpen` (the support `L` with the finest locally convex topology
  of its direction, transported by any origin), and the second reading
  `Benzecri.facette_isOpen_induced` (`L` with the topology induced by the finest locally convex
  topology of `E`; the two agree, `induced_finestLC_eq_finestLC`). Instance:
  `isFacette_openSquare`, `openSquare_isOpen`.

> **Proposition 1.** Soit $F$ une facette d'un convexe $W$, et soit $L$ la variété linéaire
> support de $F$; $F$ est un ouvert de $L$, supposé muni de sa topologie localement convexe la
> plus fine.
>
> *Démonstration.* Il suffit de démontrer que si $A\in F$, et si $l$ est une sous-variété
> linéaire de dimension finie telle que $A\in l$ et $l\subset L$, alors $A$ est intérieur à
> $l\cap F$ pour la topologie de $l$. Or, cela résulte de la remarque ci-dessus.

## The proof formalized

The finest locally convex topology is `Benzecri.finestLC` (module
`Benzecri.Chapter3.FinestLocallyConvex`): the topology of all seminorms, proved to be the
least locally convex vector topology (`isLeast_finestLC`). Its neighbourhoods of `x` are the sets
containing a seminorm ball at `x`. For `B ∈ F` and `V` the direction of `L`, every `v ∈ V` is a
two-sided direction of `W` at `B` (the subspace `dirW` of `Benzecri.Chapter3.Facettes` contains the
direction of `L`), so `U = {u ∈ V | B + 2u ∈ W ∧ B − 2u ∈ W}` is convex, balanced and absorbent in
`V`; its gauge is a seminorm whose unit ball `U'` satisfies `B + U' ⊆ F`: for `u ∈ U'`,
`B + u` is the midpoint of `B` and `B + 2u`, extends beyond `B + u` to `B + 2u` and beyond `B`
to `B − 2u`, hence is `F_W`-equivalent to `B`. This is the printed argument with the
finite-dimensional `l` taken one-dimensional (the general printed reduction is
`isOpen_finestLC_iff_finiteDimensional`).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| « un convexe $W$ » (in a real vector space) | ✓ carried: `Convex ℝ W`, `[AddCommGroup E] [Module ℝ E]` |
| « $F$ une facette » | ✓ carried: `IsFacette W F` (`Benzecri.Chapter3.Facettes`, Déf. 2) |
| « $L$ la variété linéaire support de $F$ » | ✓ carried: `affineSpan ℝ F` |
| « muni de sa topologie localement convexe la plus fine » | ✓ carried: `finestLC` of the direction of `L`, any origin `P` (the set `{v | v + P ∈ F}`; for `P ∉ L` it is empty) |

## SCOPE (disclosed)

* Nothing is omitted, no `sorry`. The topology of the affine variety `L` is read as the finest
  locally convex topology of its direction `V`, carried to `L` by `v ↦ v + P`; the statement is
  proved for every `P ∈ E` at once, so it does not depend on the origin. The second reading, `L`
  a subspace of `E` with `E`'s own finest locally convex topology, is
  `facette_isOpen_induced`; the two coincide (`induced_finestLC_eq_finestLC`).
* Helper lemmas: `vectorSpan_le_dirW` (the direction of the support of a facette consists of
  two-sided directions of `W` at each of its points; the inclusion is inside the proof of
  Prop. 2 in `Benzecri.Chapter3.Facettes`, restated here as a lemma) and
  `add_mem_facette_of_two`.
* The transfer of Prop. 1 to `S(E)` (l.276–280, the quotient topology of `F(l)`) is not in this
  target.
* Instance (non-vacuity): in `ℝ × ℝ`, the open square `]0,1[²` is a facette of `[0,1]²`
  (`isFacette_openSquare`), its support is the plane, and Prop. 1 makes it open
  (`openSquare_isOpen`); there `finestLC` is the usual topology (`finestLC_prod`), for which
  the open square is open (`openSquare_isOpen_finestLC`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open Set Filter Topology
namespace Benzecri
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The direction of the support of a facette consists of two-sided directions of `W` at each
point of the facette. -/
theorem vectorSpan_le_dirW {W : Set E} (hW : Convex ℝ W) {F : Set E} (hF : IsFacette W F)
    {B : E} (hB : B ∈ F) : vectorSpan ℝ F ≤ dirW hW (hF.subset hB) := by
  rw [vectorSpan_def, Submodule.span_le]
  rintro _ ⟨x, hx, y, hy, rfl⟩
  have hx' : x - B ∈ dirW hW (hF.subset hB) := isDirW_sub_of_alphaW hW
    (by rw [hF.eq_facetteOf hW hB] at hx; exact hx.1)
  have hy' : y - B ∈ dirW hW (hF.subset hB) := isDirW_sub_of_alphaW hW
    (by rw [hF.eq_facetteOf hW hB] at hy; exact hy.1)
  have := sub_mem hx' hy'
  simpa [vsub_eq_sub] using this

/-- If `B ∈ F` and `B ± 2u ∈ W`, then `B + u ∈ F`. -/
theorem add_mem_facette_of_two {W : Set E} (hW : Convex ℝ W) {F : Set E} (hF : IsFacette W F)
    {B u : E} (hB : B ∈ F) (h1 : B + (2 : ℝ) • u ∈ W) (h2 : B - (2 : ℝ) • u ∈ W) :
    B + u ∈ F := by
  have hBW : B ∈ W := hF.subset hB
  have hM : B + u ∈ W := by
    have := hW.add_smul_mem hBW h1 (t := 1 / 2) ⟨by norm_num, by norm_num⟩
    convert this using 2
    rw [smul_smul]; norm_num
  rw [hF.eq_facetteOf hW hB]
  refine ⟨(alphaW_iff_extend hW).2 ⟨hBW, hM, 2, two_pos, ?_⟩,
    (alphaW_iff_extend hW).2 ⟨hM, hBW, 1, one_pos, ?_⟩⟩
  · convert h2 using 1; module
  · convert h1 using 1; module

/-- **Ch. 3 § 1, Prop. 1.** A facette `F` of a convex `W` is open in its support `L`, for the
finest locally convex topology of `L`: for every origin `P`, the set of `v` in the direction of `L`
with `v + P ∈ F` is open for `finestLC`. -/
theorem facette_isOpen {W : Set E} (hW : Convex ℝ W) {F : Set E} (hF : IsFacette W F) (P : E) :
    IsOpen[finestLC (affineSpan ℝ F).direction]
      {v : (affineSpan ℝ F).direction | (v : E) + P ∈ F} := by
  set V := (affineSpan ℝ F).direction with hV
  letI := finestLC V
  haveI := isTopologicalAddGroup_finestLC V
  haveI := continuousSMul_finestLC V
  rw [isOpen_iff_mem_nhds]
  intro y hy
  set B : E := (y : E) + P with hBdef
  have hBF : B ∈ F := hy
  have hBW : B ∈ W := hF.subset hBF
  set C : Set V := {v : V | (v : E) + P ∈ W} with hC
  have hCc : Convex ℝ C := by
    intro a ha b hb s t hs ht hst
    show ((s • a + t • b : V) : E) + P ∈ W
    have := hW ha hb hs ht hst
    convert this using 1
    simp only [Submodule.coe_add, Submodule.coe_smul]
    rw [smul_add, smul_add]
    have : P = s • P + t • P := by rw [← add_smul, hst, one_smul]
    nth_rewrite 1 [this]; abel
  have hcore : ∀ v : V, ∀ᶠ t in 𝓝 (0 : ℝ), y + t • v ∈ C := by
    intro v
    have hv : (v : E) ∈ dirW hW hBW := by
      apply vectorSpan_le_dirW hW hF hBF
      have : (v : E) ∈ (affineSpan ℝ F).direction := v.2
      rwa [direction_affineSpan] at this
    obtain ⟨ε, hε, hδ⟩ := hv
    filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) hε] with t ht
    have ht' : |t| ≤ ε := by simpa [Real.dist_eq] using ht
    show ((y + t • v : V) : E) + P ∈ W
    have := hδ t ht'
    convert this using 1
    simp only [Submodule.coe_add, Submodule.coe_smul, hBdef]; abel
  have hCn : C ∈ 𝓝 y := mem_nhds_finestLC_of_core hCc hcore
  have hc1 : Tendsto (fun v : V => y + (2 : ℝ) • (v - y)) (𝓝 y) (𝓝 y) := by
    have : Continuous (fun v : V => y + (2 : ℝ) • (v - y)) := by fun_prop
    simpa using this.tendsto y
  have hc2 : Tendsto (fun v : V => y - (2 : ℝ) • (v - y)) (𝓝 y) (𝓝 y) := by
    have : Continuous (fun v : V => y - (2 : ℝ) • (v - y)) := by fun_prop
    simpa using this.tendsto y
  filter_upwards [hc1.eventually hCn, hc2.eventually hCn] with v h1 h2
  show (v : E) + P ∈ F
  have key := add_mem_facette_of_two hW hF hBF (u := (v : E) - y) (by
      convert h1 using 1
      simp only [hBdef, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_sub]; abel)
    (by
      convert h2 using 1
      simp only [hBdef, Submodule.coe_sub, Submodule.coe_smul]; abel)
  convert key using 1
  rw [hBdef]; abel
/-- **Prop. 1, second reading**: `L` a subspace of `E`, with the topology induced by the finest
locally convex topology of `E`. -/
theorem facette_isOpen_induced {W : Set E} (hW : Convex ℝ W) {F : Set E} (hF : IsFacette W F) :
    IsOpen[TopologicalSpace.induced (Subtype.val : affineSpan ℝ F → E) (finestLC E)]
      {x : affineSpan ℝ F | (x : E) ∈ F} := by
  obtain ⟨A, hA⟩ := hF.nonempty
  have hAL : A ∈ affineSpan ℝ F := subset_affineSpan ℝ F hA
  set L := affineSpan ℝ F with hL
  set V := L.direction with hV
  letI tE : TopologicalSpace E := finestLC E
  haveI := isTopologicalAddGroup_finestLC E
  letI tL : TopologicalSpace L := TopologicalSpace.induced (Subtype.val : L → E) tE
  let φ : L → V := fun x => ⟨(x : E) -ᵥ A, AffineSubspace.vsub_mem_direction x.2 hAL⟩
  have hφ : Continuous[tL, finestLC V] φ := by
    rw [← induced_finestLC_eq_finestLC]
    apply continuous_induced_rng.2
    show Continuous fun x : L => (x : E) - A
    exact continuous_induced_dom.sub continuous_const
  have hO := facette_isOpen hW hF A
  have := @Continuous.isOpen_preimage _ _ tL (finestLC V) φ hφ _ hO
  convert this using 1
  ext x
  show (x : E) ∈ F ↔ ((x : E) - A) + A ∈ F
  rw [sub_add_cancel]
/-! ### Instance: the open square -/

/-- The closed unit square of `ℝ × ℝ`. -/
def closedSquare : Set (ℝ × ℝ) := Icc 0 1 ×ˢ Icc 0 1
/-- The open unit square of `ℝ × ℝ`. -/
def openSquare : Set (ℝ × ℝ) := Ioo 0 1 ×ˢ Ioo 0 1

theorem convex_closedSquare : Convex ℝ closedSquare :=
  (convex_Icc 0 1).prod (convex_Icc 0 1)

theorem isOpen_openSquare : IsOpen openSquare := isOpen_Ioo.prod isOpen_Ioo

theorem openSquare_subset : openSquare ⊆ closedSquare :=
  prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self

theorem isFacette_openSquare : IsFacette closedSquare openSquare := by
  have hc : ((1 / 2 : ℝ), (1 / 2 : ℝ)) ∈ openSquare := ⟨⟨by norm_num, by norm_num⟩, by norm_num, by norm_num⟩
  refine ⟨_, openSquare_subset hc, ?_⟩
  ext B
  simp only [facetteOf, FW, mem_setOf_eq]
  rw [alphaW_iff_extend convex_closedSquare, alphaW_iff_extend convex_closedSquare]
  constructor
  · intro hB
    refine ⟨⟨openSquare_subset hc, openSquare_subset hB, 1, one_pos, ?_⟩,
      ⟨openSquare_subset hB, openSquare_subset hc, ?_⟩⟩
    · obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hB
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp <;> linarith
    · let f : ℝ → ℝ × ℝ := fun t => B + t • (B - ((1 / 2 : ℝ), (1 / 2 : ℝ)))
      have hf : Continuous f := continuous_const.add (continuous_id.smul continuous_const)
      have h0 : Tendsto f (𝓝 0) (𝓝 B) := by simpa [f] using hf.tendsto 0
      have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), f t ∈ openSquare ∧ t ∈ Ioi 0 :=
        ((h0.eventually (isOpen_openSquare.mem_nhds hB)).filter_mono nhdsWithin_le_nhds).and
          self_mem_nhdsWithin
      obtain ⟨t, ht, htpos⟩ := hev.exists
      exact ⟨t, htpos, openSquare_subset ht⟩
  · rintro ⟨-, ⟨⟨⟨h1, h2⟩, h3, h4⟩, -, ε, hε, ⟨h5, h6⟩, h7, h8⟩⟩
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub,
      Prod.snd_sub, smul_eq_mul] at h5 h6 h7 h8
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith

theorem affineSpan_openSquare : affineSpan ℝ openSquare = ⊤ :=
  isOpen_openSquare.affineSpan_eq_top
    ⟨((1 / 2 : ℝ), (1 / 2 : ℝ)), ⟨⟨by norm_num, by norm_num⟩, by norm_num, by norm_num⟩⟩

/-- Prop. 1 on the instance: the open square is open in its support (the plane) with its finest
locally convex topology. -/
theorem openSquare_isOpen :
    IsOpen[finestLC (affineSpan ℝ openSquare).direction]
      {v : (affineSpan ℝ openSquare).direction | (v : ℝ × ℝ) + 0 ∈ openSquare} :=
  facette_isOpen convex_closedSquare isFacette_openSquare 0

/-- On `ℝ × ℝ` the finest locally convex topology is the usual one. -/
theorem finestLC_prod : finestLC (ℝ × ℝ) = instTopologicalSpaceProd :=
  finestLC_eq_of_finiteDimensional

/-- The open square is open in `ℝ × ℝ` for `finestLC`. -/
theorem openSquare_isOpen_finestLC : IsOpen[finestLC (ℝ × ℝ)] openSquare := by
  rw [finestLC_prod]; exact isOpen_openSquare
end Benzecri
