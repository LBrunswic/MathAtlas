import Benzecri.Chapter3.ProprieteIAppui

/-!
# Chapter 3 § 5, Prop. 8 and its Corollaries 1, 2 — properties I(V, W) and II(V, W)

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 3 § 5, journal pp. 279–280; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch3.tex` (to be checked by the author). Target
T-bz-c3-proprietes-i-ii. `E` is a real topological vector space, locally convex and Hausdorff
(`[IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]`), as
printed; `I(V, W)` is `Benzecri.ProprieteI` (Déf. 1), « le support $L$ de $V$ » is
`affineSpan ℝ V`, « variété d'appui » is `Benzecri.IsVarieteAppui` (Déf. 3).

* `bzprop:c3s5p8_proprietes_I_II` — `benzecri1960_ch3.tex:1323` (Prop. 8, l.1323–1337, proof
  l.1340–1364) — `Benzecri.proprietes_I_II` (with `[Nontrivial E]`), `Benzecri.proprietes_I_II_of_ne`
  (no `Nontrivial`, for `V ≠ W`); the halves `Benzecri.proprieteI_of_proprieteII` (any `T₁`
  topology, no compactness) and `Benzecri.proprieteII_of_proprieteI`. New definitions
  `Benzecri.DemiEspaceOuvert` (instance `demiEspaceOuvert_fst_lt_one`) and
  `Benzecri.ProprieteII` (the printed reformulation; the printed first formulation is
  `Benzecri.proprieteII_iff_systemeFondamental`). Imprecise in dimension 0:
  `Benzecri.proprietes_I_II_dimZero`. Instances: `sommet_carre_proprietes` (a vertex of the
  square: I and II), `centre_carre_proprietes` (its centre: neither), `carre_proprieteII_self`
  (`V = W`).
* **`bzcor:c3s5p8c1_II_appui`** — `benzecri1960_ch3.tex:1366` (Cor. 1, l.1366–1370, no proof
  printed) — `Benzecri.proprieteII_appui`, in every space (dimension 0 included). Instance:
  `bordCarre_proprieteII`.
* `bzcor:c3s5p8c2_II_section_appui` — `benzecri1960_ch3.tex:1373` (Cor. 2, l.1373–1376, no proof
  printed) — `Benzecri.proprieteII_section_appui` (with `[Nontrivial E]`). Imprecise in dimension
  0: `Benzecri.section_appui_dimZero`. Instance: `lineY0_proprieteII`.

> **Proposition 8.** Soit $W$ un convexe compact d'un espace vectoriel topologique $E$ localement
> convexe séparé, $V$ une partie compacte convexe non vide de $W$; alors les deux propriétés
> ci-dessous sont équivalentes :
> $\mathrm{I}(V, W)$ : $(W-V)$ est convexe;
> $\mathrm{II}(V, W)$ : les demi-espaces ouverts contenant $V$ coupent $W$ suivant un système
> fondamental de voisinages de $V$ considéré comme partie de $W$.
> $\mathrm{II}(V, W)$ peut encore s'énoncer : Pour tout voisinage $O$ de $V$ considéré comme
> partie de $E$, il existe un demi-espace ouvert $H$ tel que
> $1^{\circ}\quad V\subset H$; $2^{\circ}\quad H\cap W\subset O\cap W$.
>
> **Corollaire 1.** Soient $W$, $V$ convexes compacts $V\subset W$; si le support $L$ de $V$ est
> une variété d'appui de $W$, il est équivalent d'affirmer $\mathrm{II}(V, W)$ ou
> $\mathrm{II}(V, W\cap L)$ (*cf.* prop. 4).
>
> **Corollaire 2.** Soit $W$ convexe compact, $L$ une variété d'appui fermée de $W$, alors on a
> $\mathrm{II}(L\cap W, W)$.

## The proofs formalized

`II ⇒ I` is the printed proof: for `b, b′ ∈ W − V`, `O = E − {b, b′}` (open, `E` being `T₁`)
gives `H`; `b, b′ ∉ H`, `∁H` is convex, and a point of `[b, b′]` in `V` would be in `H`.
`I ⇒ II` follows the printed proof, with its two steps made explicit. The filter-base step
(« il existe un demi-espace fermé $H_3$ … ») becomes `exists_compact_convex_superset`: finitely
many compact convex parts of the convex `W − V` lie in one, the convex hull of two of them being
compact (`isCompact_convexHull_union`, through `convexJoin`, `isCompact_convexJoin`). The step
« le filtre sera le filtre de voisinages de $V$ » is the compactness of `W − O`: for each
`b ∈ W − O`, Hahn–Banach (Bourbaki EVT II § 3 prop. 4, Mathlib's
`geometric_hahn_banach_compact_closed`) gives `f_b < u_b` on `V`, `f_b(b) > u_b`; finitely many
open sets `{f_b > u_b}` cover `W − O`, and the pieces `W ∩ {f_b ≥ u_b}` are compact convex parts
of `W − V` (`exists_compact_convex_between`). One more separation of `V` from the compact convex
`K ⊇ W − O` gives `H`. When `K = ∅` (`W ⊆ O`), any non-zero continuous form, bounded on `W`,
gives `H`: this is where `E ≠ 0` is used. Cor. 1 (no proof printed): `⇒` is immediate (no
hypothesis used); `⇐` is `II(V, W ∩ L) ⇒ I(V, W ∩ L)` (Prop. 8, `II ⇒ I`), then Prop. 4 `⇐`
(`proprieteI_of_isVarieteAppui`), then Prop. 8 `I ⇒ II` in `W`; `W ∩ L` need not be compact
(`L` need not be closed in infinite dimension) and is never required to be. In `E = 0` both sides
are false. Cor. 2 (no proof printed): `L ∩ W` is compact (`L` closed), non-empty (Déf. 3) and
`I(L ∩ W, W)` holds by Prop. 3 (`W − L ∩ W = W ∩ ∁L` convex); then Prop. 8.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| Prop. 8: « $E$ … localement convexe séparé » | ✓ carried: `[IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]`; `II ⇒ I` uses `T₁` only |
| Prop. 8: « $W$ un convexe compact » | ✓ carried: `IsCompact W`, `Convex ℝ W`; `II ⇒ I` uses convexity only |
| Prop. 8: « $V$ une partie compacte convexe non vide de $W$ » | ✓ carried: `IsCompact V`, `Convex ℝ V`, `V.Nonempty`, `V ⊆ W` |
| Prop. 8: (unprinted) `E ≠ 0` | ⚠ strengthened: `[Nontrivial E]` in `proprietes_I_II`; not needed when `V ≠ W` (`proprietes_I_II_of_ne`); necessary: `proprietes_I_II_dimZero` |
| Prop. 8: « demi-espace ouvert » | `DemiEspaceOuvert`: `{f < c}`, `f` a non-zero continuous linear form |
| Prop. 8: « voisinage $O$ de $V$ … partie de $E$ » | ✓ quantified over open `O ⊇ V` (every neighbourhood contains one, and `H ∩ W ⊆ O ∩ W` is monotone in `O`) |
| Cor. 1: « $W$, $V$ convexes compacts $V\subset W$ » | ✓ carried; non-emptiness of `V` follows from Déf. 3 |
| Cor. 1: « le support $L$ de $V$ est une variété d'appui de $W$ » | ✓ carried: `IsVarieteAppui W (affineSpan ℝ V)` |
| Cor. 1: the space | Prop. 8's setting (Cor. 1 prints none); no `Nontrivial` |
| Cor. 2: « $W$ convexe compact, $L$ une variété d'appui fermée » | ✓ carried: `IsCompact W`, `Convex ℝ W`, `IsClosed (L : Set E)`, `IsVarieteAppui W L` |
| Cor. 2: (unprinted) `E ≠ 0` | ⚠ strengthened: `[Nontrivial E]`; necessary: `section_appui_dimZero` |

## SCOPE (disclosed)

* Cor. 1's « II(V, W ∩ L) » is Prop. 8's property II for the set `W ∩ L`, with open half-spaces
  of `E` (not of `L`): the literal reading, and the only one under which Cor. 1 holds, since `L` can
  be a single point.
* Prop. 8 and Cor. 2 are not marked: both fail in the zero space `E = 0`, where `V = W = {0}`
  (resp. `L = E`) satisfies every printed hypothesis but there is no open half-space at all, so
  `II` fails (`proprietes_I_II_dimZero`, `section_appui_dimZero`). This is a degenerate case
  (imprecise), the only one: Prop. 8 holds without `Nontrivial` as soon as `V ≠ W`. Under a
  reading of « demi-espace ouvert » admitting `E` itself (`f = 0`, `c > 0`), both would hold in
  `E = 0` too; that reading is not formalized.
* Cor. 1 is marked: it holds in every Hausdorff locally convex space, `E = 0` included.
* `ProprieteII` is the printed reformulation (« peut encore s'énoncer »); the first formulation
  (« système fondamental de voisinages de $V$ considéré comme partie de $W$ ») is proved
  equivalent for `V ⊆ W` in the subspace topology of `W` (`proprieteII_iff_systemeFondamental`).
* The proof prints « $(b, b')\in\complement H$ », « $(b, b')\in W-V$ » for segments, read `⊆`
  (the transcription's comment); and « demi-espaces fermés $H_1$, $H_2$ » for the complements
  of the open half-spaces, as formalized.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open Set Filter Topology

namespace Benzecri

section Defs

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- An *open half-space* of `E`: `{x | f x < c}` for a non-zero continuous linear form `f`. -/
def DemiEspaceOuvert (H : Set E) : Prop :=
  ∃ f : StrongDual ℝ E, f ≠ 0 ∧ ∃ c : ℝ, H = {x | f x < c}

/-- **`II(V, W)`**, in the printed reformulation: for every open `O ⊇ V` of `E` there is an
open half-space `H` with `V ⊆ H` and `H ∩ W ⊆ O ∩ W`. -/
def ProprieteII (V W : Set E) : Prop :=
  ∀ O : Set E, IsOpen O → V ⊆ O → ∃ H : Set E, DemiEspaceOuvert H ∧ V ⊆ H ∧ H ∩ W ⊆ O ∩ W

theorem DemiEspaceOuvert.isOpen {H : Set E} (h : DemiEspaceOuvert H) : IsOpen H := by
  obtain ⟨f, -, c, rfl⟩ := h
  exact isOpen_lt f.continuous continuous_const

theorem DemiEspaceOuvert.convex_compl {H : Set E} (h : DemiEspaceOuvert H) : Convex ℝ Hᶜ := by
  obtain ⟨f, -, c, rfl⟩ := h
  have : ({x | f x < c}ᶜ : Set E) = f.toLinearMap ⁻¹' Ici c := by
    ext x; simp
  rw [this]
  exact (convex_Ici c).linear_preimage _

/-- The printed first formulation of `II(V, W)`: the traces on `W` of the open half-spaces
containing `V` form a fundamental system of neighbourhoods of `V` in the subspace `W`. -/
theorem proprieteII_iff_systemeFondamental {V W : Set E} (hVW : V ⊆ W) :
    ProprieteII V W ↔
      (∀ H : Set E, DemiEspaceOuvert H → V ⊆ H →
          ((↑) ⁻¹' H : Set W) ∈ 𝓝ˢ ((↑) ⁻¹' V : Set W)) ∧
        ∀ N ∈ 𝓝ˢ ((↑) ⁻¹' V : Set W),
          ∃ H : Set E, DemiEspaceOuvert H ∧ V ⊆ H ∧ ((↑) ⁻¹' H : Set W) ⊆ N := by
  constructor
  · intro h
    refine ⟨fun H hH hVH => ?_, fun N hN => ?_⟩
    · exact (hH.isOpen.preimage continuous_subtype_val).mem_nhdsSet.2 (fun x hx => hVH hx)
    · obtain ⟨U', hU'o, hVU', hU'N⟩ := mem_nhdsSet_iff_exists.1 hN
      obtain ⟨U, hUo, rfl⟩ := isOpen_induced_iff.1 hU'o
      obtain ⟨H, hH, hVH, hHW⟩ := h U hUo (fun v hv => hVU' (show (⟨v, hVW hv⟩ : W) ∈ _ from hv))
      exact ⟨H, hH, hVH, fun x hx => hU'N (hHW ⟨hx, x.2⟩).1⟩
  · rintro ⟨-, h⟩ O hO hVO
    have hN : ((↑) ⁻¹' O : Set W) ∈ 𝓝ˢ ((↑) ⁻¹' V : Set W) :=
      (hO.preimage continuous_subtype_val).mem_nhdsSet.2 (fun x hx => hVO hx)
    obtain ⟨H, hH, hVH, hHN⟩ := h _ hN
    exact ⟨H, hH, hVH, fun x hx => ⟨(hHN (show (⟨x, hx.2⟩ : W) ∈ ((↑) ⁻¹' H : Set W) from hx.1)), hx.2⟩⟩

/-- **Prop. 8, `II ⇒ I`**, for any `T₁` topology on `E`, no compactness. -/
theorem proprieteI_of_proprieteII [T1Space E] {V W : Set E} (hW : Convex ℝ W)
    (hV : Convex ℝ V) (hVW : V ⊆ W) (h : ProprieteII V W) : ProprieteI V W := by
  refine ⟨hVW, hV, ?_⟩
  intro x hx y hy a b ha hb hab
  have hO : IsOpen ({x, y}ᶜ : Set E) := (Set.toFinite _).isClosed.isOpen_compl
  have hVO : V ⊆ ({x, y}ᶜ : Set E) := by
    intro v hv hv'
    rcases hv' with rfl | rfl
    · exact hx.2 hv
    · exact hy.2 hv
  obtain ⟨H, ⟨f, -, c, rfl⟩, hVH, hHW⟩ := h _ hO hVO
  have hxH : c ≤ f x := by
    by_contra hlt
    exact (hHW ⟨not_le.1 hlt, hx.1⟩).1 (Or.inl rfl)
  have hyH : c ≤ f y := by
    by_contra hlt
    exact (hHW ⟨not_le.1 hlt, hy.1⟩).1 (Or.inr rfl)
  refine ⟨hW hx.1 hy.1 ha hb hab, fun hz => ?_⟩
  have h1 : f (a • x + b • y) < c := hVH hz
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h1
  have h2 : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hxH ha, mul_le_mul_of_nonneg_left hyH hb]

/-- In the zero space, `II(V, W)` fails for every non-empty `V`: there is no open half-space. -/
theorem not_demiEspaceOuvert_of_subsingleton [Subsingleton E] (H : Set E) :
    ¬ DemiEspaceOuvert H := by
  rintro ⟨f, hf, -⟩
  apply hf
  ext x
  rw [Subsingleton.elim x 0, map_zero]; rfl

theorem proprieteII_subsingleton_false [Subsingleton E] (V W : Set E) :
    ¬ ProprieteII V W := by
  intro h
  obtain ⟨H, hH, -⟩ := h univ isOpen_univ (subset_univ _)
  exact not_demiEspaceOuvert_of_subsingleton H hH

end Defs

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- The convex join of two compact sets is compact. -/
theorem isCompact_convexJoin {A B : Set E} (hA : IsCompact A) (hB : IsCompact B) :
    IsCompact (convexJoin ℝ A B) := by
  have : convexJoin ℝ A B =
      (fun p : E × E × ℝ => (1 - p.2.2) • p.1 + p.2.2 • p.2.1) '' (A ×ˢ B ×ˢ Icc (0 : ℝ) 1) := by
    ext x
    simp only [mem_convexJoin, segment_eq_image, mem_image, mem_prod, Prod.exists]
    constructor
    · rintro ⟨a, ha, b, hb, θ, hθ, rfl⟩
      exact ⟨a, b, θ, ⟨ha, hb, hθ⟩, rfl⟩
    · rintro ⟨a, b, θ, ⟨ha, hb, hθ⟩, rfl⟩
      exact ⟨a, ha, b, hb, θ, hθ, rfl⟩
  rw [this]
  exact (hA.prod (hB.prod isCompact_Icc)).image (by fun_prop)

/-- The convex hull of the union of two compact convex sets is compact. -/
theorem isCompact_convexHull_union {A B : Set E} (hA : IsCompact A) (hAc : Convex ℝ A)
    (hB : IsCompact B) (hBc : Convex ℝ B) : IsCompact (convexHull ℝ (A ∪ B)) := by
  rcases A.eq_empty_or_nonempty with rfl | hA0
  · rw [empty_union, hBc.convexHull_eq]; exact hB
  rcases B.eq_empty_or_nonempty with rfl | hB0
  · rw [union_empty, hAc.convexHull_eq]; exact hA
  rw [hAc.convexHull_union hBc hA0 hB0]
  exact isCompact_convexJoin hA hB

/-- The filter-base step of the proof of `I ⇒ II`, for a finite family: finitely many compact
convex parts of a convex `S` lie in one compact convex part of `S`. -/
theorem exists_compact_convex_superset {S : Set E} (hS : Convex ℝ S) {ι : Type*}
    (t : Finset ι) (P : ι → Set E) (hP : ∀ i ∈ t, IsCompact (P i) ∧ Convex ℝ (P i) ∧ P i ⊆ S) :
    ∃ K : Set E, IsCompact K ∧ Convex ℝ K ∧ (⋃ i ∈ t, P i) ⊆ K ∧ K ⊆ S := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨∅, isCompact_empty, convex_empty, by simp, empty_subset _⟩
  | insert j t hj ih =>
    obtain ⟨K, hK, hKc, hPK, hKS⟩ := ih (fun i hi => hP i (Finset.mem_insert_of_mem hi))
    obtain ⟨hPj, hPjc, hPjS⟩ := hP j (Finset.mem_insert_self j t)
    refine ⟨convexHull ℝ (P j ∪ K), isCompact_convexHull_union hPj hPjc hK hKc,
      convex_convexHull ℝ _, ?_, convexHull_min (union_subset hPjS hKS) hS⟩
    rw [Finset.set_biUnion_insert]
    exact (union_subset_union_right _ hPK).trans (subset_convexHull ℝ _)

variable [LocallyConvexSpace ℝ E] [T2Space E]

/-- The compactness step of `I ⇒ II`: for `O ⊇ V` open, `W − O` lies in a compact convex part
of `W − V`. -/
theorem exists_compact_convex_between {V W O : Set E} (hW : IsCompact W) (hWc : Convex ℝ W)
    (hV : IsCompact V) (hVc : Convex ℝ V) (hI : Convex ℝ (W \ V)) (hO : IsOpen O)
    (hVO : V ⊆ O) :
    ∃ K : Set E, IsCompact K ∧ Convex ℝ K ∧ W \ O ⊆ K ∧ K ⊆ W \ V := by
  -- for each `b ∈ W − O`, strict separation of `V` and `{b}`
  have hsep : ∀ b : ↥(W \ O), ∃ (f : StrongDual ℝ E) (u : ℝ),
      (∀ a ∈ V, f a < u) ∧ u < f b := by
    intro b
    obtain ⟨f, u, v, hfu, huv, hfv⟩ := geometric_hahn_banach_compact_closed hVc hV
      (convex_singleton (b : E)) isClosed_singleton
      (disjoint_singleton_right.2 (fun hb => b.2.2 (hVO hb)))
    exact ⟨f, u, hfu, huv.trans (hfv _ rfl)⟩
  choose f u hfu hub using hsep
  obtain ⟨t, ht⟩ := (hW.diff hO).elim_finite_subcover (fun b => {x | u b < f b x})
    (fun b => isOpen_lt continuous_const (f b).continuous)
    (fun b hb => mem_iUnion.2 ⟨⟨b, hb⟩, hub ⟨b, hb⟩⟩)
  obtain ⟨K, hK, hKc, hPK, hKS⟩ := exists_compact_convex_superset hI t
    (fun b => W ∩ {x | u b ≤ f b x}) (fun b _ => ⟨hW.inter_right (isClosed_le continuous_const
      (f b).continuous), hWc.inter (convex_halfSpace_ge (f b).toLinearMap.isLinear (u b)),
      fun x hx => ⟨hx.1, fun hxV => absurd hx.2 (not_le.2 (hfu b x hxV))⟩⟩)
  refine ⟨K, hK, hKc, fun x hx => hPK ?_, hKS⟩
  obtain ⟨b, hb, hxb⟩ := mem_iUnion₂.1 (ht hx)
  exact mem_iUnion₂.2 ⟨b, hb, hx.1, le_of_lt (show u b < f b x from hxb)⟩

/-- A non-zero continuous linear form bounded above on a compact set gives an open half-space
containing it. -/
theorem exists_demiEspaceOuvert_superset [Nontrivial E] {W : Set E} (hW : IsCompact W) :
    ∃ H : Set E, DemiEspaceOuvert H ∧ W ⊆ H := by
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  obtain ⟨f, hf⟩ := geometric_hahn_banach_point_point hx.symm
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at hf
  obtain ⟨M, hM⟩ := hW.bddAbove_image f.continuous.continuousOn
  exact ⟨{y | f y < M + 1}, ⟨f, hf0, M + 1, rfl⟩, fun y hy =>
    lt_of_le_of_lt (hM (mem_image_of_mem _ hy)) (lt_add_one M)⟩

/-- **Prop. 8, `I ⇒ II`**. -/
theorem proprieteII_of_proprieteI [Nontrivial E] {V W : Set E} (hW : IsCompact W)
    (hWc : Convex ℝ W) (hV : IsCompact V) (hne : V.Nonempty) (hI : ProprieteI V W) :
    ProprieteII V W := by
  obtain ⟨hVW, hVc, hD⟩ := hI
  intro O hO hVO
  obtain ⟨K, hK, hKc, hOK, hKD⟩ := exists_compact_convex_between hW hWc hV hVc hD hO hVO
  rcases K.eq_empty_or_nonempty with rfl | hK0
  · obtain ⟨H, hH, hWH⟩ := exists_demiEspaceOuvert_superset hW
    refine ⟨H, hH, hVW.trans hWH, fun x hx => ⟨?_, hx.2⟩⟩
    by_contra hxO
    exact hOK ⟨hx.2, hxO⟩
  obtain ⟨f, u, v, hfu, huv, hfv⟩ := geometric_hahn_banach_compact_closed hVc hV hKc
    hK.isClosed (disjoint_left.2 fun x hxV hxK => (hKD hxK).2 hxV)
  have hf0 : f ≠ 0 := by
    rintro rfl
    obtain ⟨a, ha⟩ := hne
    obtain ⟨k, hk⟩ := hK0
    have h1 : (0 : ℝ) < u := hfu a ha
    have h2 : v < (0 : ℝ) := hfv k hk
    linarith
  refine ⟨{x | f x < u}, ⟨f, hf0, u, rfl⟩, fun a ha => hfu a ha, fun x hx => ⟨?_, hx.2⟩⟩
  by_contra hxO
  have := hfv x (hOK ⟨hx.2, hxO⟩)
  have h' : f x < u := hx.1
  linarith

/-- **Prop. 8.** -/
theorem proprietes_I_II [Nontrivial E] {V W : Set E} (hW : IsCompact W) (hWc : Convex ℝ W)
    (hV : IsCompact V) (hVc : Convex ℝ V) (hne : V.Nonempty) (hVW : V ⊆ W) :
    ProprieteI V W ↔ ProprieteII V W := by
  exact ⟨proprieteII_of_proprieteI hW hWc hV hne, proprieteI_of_proprieteII hWc hVc hVW⟩

/-- **Prop. 8** for `V ≠ W`, in every space (then `E ≠ 0`). -/
theorem proprietes_I_II_of_ne {V W : Set E} (hW : IsCompact W) (hWc : Convex ℝ W)
    (hV : IsCompact V) (hVc : Convex ℝ V) (hne : V.Nonempty) (hVW : V ⊆ W) (hVW' : V ≠ W) :
    ProprieteI V W ↔ ProprieteII V W := by
  have : Nontrivial E := by
    obtain ⟨a, ha⟩ := hne
    obtain ⟨b, hbW, hbV⟩ : ∃ b ∈ W, b ∉ V := by
      by_contra h
      simp only [not_exists, not_and, not_not] at h
      exact hVW' (subset_antisymm hVW h)
    exact ⟨a, b, fun hab => hbV (hab ▸ ha)⟩
  exact proprietes_I_II hW hWc hV hVc hne hVW

/-- **Cor. 1.** -/
theorem proprieteII_appui {V W : Set E} (hW : IsCompact W) (hWc : Convex ℝ W)
    (hV : IsCompact V) (hVc : Convex ℝ V) (hVW : V ⊆ W)
    (hL : IsVarieteAppui W (affineSpan ℝ V)) :
    ProprieteII V W ↔ ProprieteII V (W ∩ (affineSpan ℝ V : Set E)) := by
  have hne : V.Nonempty := by
    obtain ⟨x, hxL, -⟩ := hL.1
    exact (affineSpan_nonempty (k := ℝ)).1 ⟨x, hxL⟩
  constructor
  · intro h O hO hVO
    obtain ⟨H, hH, hVH, hHW⟩ := h O hO hVO
    exact ⟨H, hH, hVH, fun x hx => ⟨(hHW ⟨hx.1, hx.2.1⟩).1, hx.2⟩⟩
  · intro h
    rcases subsingleton_or_nontrivial E with hE | hE
    · exact absurd h (proprieteII_subsingleton_false _ _)
    have hI' : ProprieteI V (W ∩ (affineSpan ℝ V : Set E)) :=
      proprieteI_of_proprieteII (hWc.inter (affineSpan ℝ V).convex) hVc
        (fun x hx => ⟨hVW hx, subset_affineSpan ℝ V hx⟩) h
    have hI'' : ProprieteI V ((affineSpan ℝ V : Set E) ∩ W) := by
      rwa [inter_comm]
    exact proprieteII_of_proprieteI hW hWc hV hne (proprieteI_of_isVarieteAppui hWc hL hI'')

/-- **Cor. 2.** -/
theorem proprieteII_section_appui [Nontrivial E] {W : Set E} (hW : IsCompact W)
    (hWc : Convex ℝ W) {L : AffineSubspace ℝ E} (hLc : IsClosed (L : Set E))
    (hL : IsVarieteAppui W L) : ProprieteII ((L : Set E) ∩ W) W := by
  have hI : ProprieteI ((L : Set E) ∩ W) W := by
    refine ⟨inter_subset_right, L.convex.inter hWc, ?_⟩
    have : W \ ((L : Set E) ∩ W) = W ∩ (L : Set E)ᶜ := by
      ext x; simp only [Set.mem_sdiff, mem_inter_iff, mem_compl_iff]; tauto
    rw [this]
    exact convex_inter_compl_of_isVarieteAppui hWc hL
  exact proprieteII_of_proprieteI hW hWc (hW.inter_left hLc) hL.1 hI

/-! ### Instances -/

/-- **Instance of the definition of an open half-space**: `{p | p.1 < 1}` in `ℝ × ℝ`. -/
theorem demiEspaceOuvert_fst_lt_one : DemiEspaceOuvert {p : ℝ × ℝ | p.1 < 1} := by
  refine ⟨ContinuousLinearMap.fst ℝ ℝ ℝ, fun h => ?_, 1, rfl⟩
  have := congrArg (fun g : StrongDual ℝ (ℝ × ℝ) => g (1, 0)) h
  simp at this

theorem isCompact_square : IsCompact square := isCompact_Icc.prod isCompact_Icc

/-- **Prop. 8, instance**: the vertex `(0, 0)` of the closed square has both properties. -/
theorem sommet_carre_proprietes :
    ProprieteI {((0 : ℝ), (0 : ℝ))} square ∧ ProprieteII {((0 : ℝ), (0 : ℝ))} square := by
  have hI : ProprieteI {((0 : ℝ), (0 : ℝ))} square := by
    refine ⟨singleton_subset_iff.2 (mem_square.2 ⟨⟨le_rfl, zero_le_one⟩, le_rfl, zero_le_one⟩),
      convex_singleton _, ?_⟩
    rintro x ⟨hxW, hx0⟩ y ⟨hyW, hy0⟩ a b ha hb hab
    refine ⟨convex_square hxW hyW ha hb hab, fun hz => ?_⟩
    obtain ⟨⟨hx1, -⟩, hx2, -⟩ := mem_square.1 hxW
    obtain ⟨⟨hy1, -⟩, hy2, -⟩ := mem_square.1 hyW
    have hz' := Prod.ext_iff.1 (mem_singleton_iff.1 hz)
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hz'
    obtain ⟨h1, h2⟩ := hz'
    rcases ha.eq_or_lt with rfl | ha'
    · apply hy0
      have hb1 : b = 1 := by linarith
      subst hb1
      exact mem_singleton_iff.2 (Prod.ext (by linarith) (by linarith))
    · apply hx0
      have e1 : x.1 = 0 := by nlinarith [mul_nonneg hb hy1, mul_nonneg ha hx1]
      have e2 : x.2 = 0 := by nlinarith [mul_nonneg hb hy2, mul_nonneg ha hx2]
      exact mem_singleton_iff.2 (Prod.ext e1 e2)
  exact ⟨hI, proprieteII_of_proprieteI isCompact_square convex_square isCompact_singleton
    (singleton_nonempty _) hI⟩

/-- **Prop. 8, instance**: the centre of the closed square has neither property. -/
theorem centre_carre_proprietes :
    ¬ ProprieteI {((1 / 2 : ℝ), (1 / 2 : ℝ))} square ∧
      ¬ ProprieteII {((1 / 2 : ℝ), (1 / 2 : ℝ))} square := by
  have hI : ¬ ProprieteI {((1 / 2 : ℝ), (1 / 2 : ℝ))} square := by
    rintro ⟨-, -, hD⟩
    have h0 : ((0 : ℝ), (0 : ℝ)) ∈ square \ {((1 / 2 : ℝ), (1 / 2 : ℝ))} := by
      refine ⟨mem_square.2 ⟨⟨le_rfl, zero_le_one⟩, le_rfl, zero_le_one⟩, fun h => ?_⟩
      have := congrArg Prod.fst (mem_singleton_iff.1 h)
      norm_num at this
    have h1 : ((1 : ℝ), (1 : ℝ)) ∈ square \ {((1 / 2 : ℝ), (1 / 2 : ℝ))} := by
      refine ⟨mem_square.2 ⟨⟨zero_le_one, le_rfl⟩, zero_le_one, le_rfl⟩, fun h => ?_⟩
      have := congrArg Prod.fst (mem_singleton_iff.1 h)
      norm_num at this
    have := hD h0 h1 (a := 1 / 2) (b := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
    apply this.2
    rw [mem_singleton_iff]
    ext <;> simp
  exact ⟨hI, fun hII => hI (proprieteI_of_proprieteII convex_square (convex_singleton _)
    (singleton_subset_iff.2 (mem_square.2 ⟨⟨by norm_num, by norm_num⟩, by norm_num,
      by norm_num⟩)) hII)⟩

/-- **Prop. 8, instance**: `V = W`, the whole square: `II(W, W)`. -/
theorem carre_proprieteII_self : ProprieteII square square :=
  proprieteII_of_proprieteI isCompact_square convex_square isCompact_square
    ⟨(0, 0), mem_square.2 ⟨⟨le_rfl, zero_le_one⟩, le_rfl, zero_le_one⟩⟩
    ⟨subset_rfl, convex_square, by rw [sdiff_self]; exact convex_empty⟩

/-- **Cor. 1, instance**: the bottom edge `V = [0,1] × {0}` of the square, whose support is a
variété d'appui: `II(V, W)` and `II(V, W ∩ L)`, both true. -/
theorem bordCarre_proprieteII :
    ProprieteII (Icc (0 : ℝ) 1 ×ˢ ({0} : Set ℝ)) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∧
      ProprieteII (Icc (0 : ℝ) 1 ×ˢ ({0} : Set ℝ))
        ((Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∩
          (affineSpan ℝ (Icc (0 : ℝ) 1 ×ˢ ({0} : Set ℝ)) : Set (ℝ × ℝ))) := by
  have hII := proprieteII_of_proprieteI (isCompact_Icc.prod isCompact_Icc)
    ((convex_Icc 0 1).prod (convex_Icc 0 1)) (isCompact_Icc.prod isCompact_singleton)
    ⟨(0, 0), ⟨le_rfl, zero_le_one⟩, rfl⟩ proprieteI_segment_carre
  exact ⟨hII, (proprieteII_appui (isCompact_Icc.prod isCompact_Icc)
    ((convex_Icc 0 1).prod (convex_Icc 0 1)) (isCompact_Icc.prod isCompact_singleton)
    proprieteI_segment_carre.2.1 proprieteI_segment_carre.1 bordCarre_isVarieteAppui).1 hII⟩

/-- **Cor. 2, instance**: the closed variété d'appui `y = 0` of the square:
`II(L ∩ W, W)`. -/
theorem lineY0_proprieteII : ProprieteII ((lineY0 : Set (ℝ × ℝ)) ∩ square) square :=
  proprieteII_section_appui isCompact_square convex_square
    (AffineSubspace.closed_of_finiteDimensional lineY0) lineY0_isVarieteAppui

/-! ### Dimension zero: the degenerate case where Prop. 8 and Cor. 2 fail -/

/-- In the zero space `ℝ⁰ = Fin 0 → ℝ`, `V = W = {0}` satisfies every hypothesis of Prop. 8 and
`I(V, W)`, but not `II(V, W)` (there is no open half-space). Prop. 8 is imprecise there. -/
theorem proprietes_I_II_dimZero :
    IsCompact (univ : Set (Fin 0 → ℝ)) ∧ Convex ℝ (univ : Set (Fin 0 → ℝ)) ∧
      (univ : Set (Fin 0 → ℝ)).Nonempty ∧
      ProprieteI (univ : Set (Fin 0 → ℝ)) univ ∧ ¬ ProprieteII (univ : Set (Fin 0 → ℝ)) univ :=
  ⟨isCompact_univ, convex_univ, univ_nonempty, ⟨subset_rfl, convex_univ,
    by rw [sdiff_self]; exact convex_empty⟩, proprieteII_subsingleton_false _ _⟩

/-- In `ℝ⁰`, `L = ⊤` is a closed variété d'appui of the compact convex `W = {0}`, but
`II(L ∩ W, W)` fails. Cor. 2 is imprecise there. -/
theorem section_appui_dimZero :
    IsCompact (univ : Set (Fin 0 → ℝ)) ∧ Convex ℝ (univ : Set (Fin 0 → ℝ)) ∧
      IsClosed ((⊤ : AffineSubspace ℝ (Fin 0 → ℝ)) : Set (Fin 0 → ℝ)) ∧
      IsVarieteAppui (univ : Set (Fin 0 → ℝ)) ⊤ ∧
      ¬ ProprieteII (((⊤ : AffineSubspace ℝ (Fin 0 → ℝ)) : Set (Fin 0 → ℝ)) ∩ univ) univ :=
  ⟨isCompact_univ, convex_univ, by rw [AffineSubspace.top_coe]; exact isClosed_univ,
    isVarieteAppui_top_iff.2 univ_nonempty, proprieteII_subsingleton_false _ _⟩

end Benzecri
