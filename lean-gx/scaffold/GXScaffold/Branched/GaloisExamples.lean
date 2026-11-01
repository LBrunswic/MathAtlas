import GXScaffold.Branched.Galois

/-!
# The examples closing §3.4 (l.1560–1583)

Package WP-26h. `papers/gx`, `RamcovGX.tex:1560–1583`.

* `ex:following_situations_semi_locally_simply` — `RamcovGX.tex:1560` (partial, SCOPE (a)–(c)):
  item 1 `GX.following_situations_finite` (an `E`-manifold, `E` any nontrivial real normed space,
  `S` finite; `GX.following_situations_finite_euclidean` for `n ≥ 1`); item 2
  `GX.following_situations_tame` (`S` locally polygonal, `GX.IsLocallyPolygonal`, in dimension
  `≥ 2`), the classical tame knots of `ℝ³` `GX.following_situations_tame_knot`; item 3
  `GX.following_situations_simplicial` (a locally finite complex every face of which lies in a
  face with `≥ n` vertices, `GX.HasFacesOfCardGe`; pure complexes
  `GX.following_situations_simplicial_pure`), its connected counterexample as written
  `GX.following_situations_simplicial_false` (a tetrahedron with a dangling edge). Tools:
  `GX.IsConicalAt`, `GX.isConicalAt_segment`, `GX.isSLSCIn_subtype_compl_of_isConicalAt`,
  `GX.isSLSCIn_compl_of_local_models`.
* `ex:consider_denote_absolute_galois` — `RamcovGX.tex:1570` (partial, SCOPE (d)): `ℂ ∖ S` is NOT
  semi-locally simply connected in `ℂ`, `GX.absGal_not_isSLSCIn` (at `0`,
  `GX.absGal_not_isSLSCAt`, through the winding number and the general criterion
  `GX.not_isSLSCAt_of_essential`); the printed `Γ₂` is all of `Γ`, `GX.printedGamma2_eq_top`;
  for the intended `Γ₂` (normal closure of the squares) the fibre of `Y₂` over `0` is not
  compact, hence not a Cantor set: `GX.absGal_Y₂_fiber_not_compact` (tagged `sorry`),
  `GX.absGal_Y₂_fiber_not_cantor`.
* `ex:wild_cantor_general_antoine` — `RamcovGX.tex:1578` (partial, SCOPE (e)): FALSE for wild
  Cantor sets in general. Positive half: a dense, simply connected, locally non-separating
  complement is semi-locally simply connected, `GX.isSLSCIn_compl_of_simplyConnected`,
  `GX.sphere3_isSLSCIn_compl_of_simplyConnected`; the complement of a Cantor set is dense,
  `GX.dense_compl_of_isCantorSubset`; hence the claim fails as soon as a wild Cantor set with
  simply connected, locally non-separating complement exists,
  `GX.wild_cantor_claim_false_of_exists`, and it does (Kirkor, Skora, Garity–Repovš–Željko:
  `GX.kirkor_wild_cantor_exists`, tagged `sorry`), `GX.wild_cantor_claim_false`. Corrected
  claim, for the cited class: Antoine's necklace is a wild Cantor set whose complement is not
  semi-locally simply connected, `GX.exists_wild_cantor_not_isSLSCIn`, proved from the
  essential-loop criterion (`GX.wild_cantor_not_isSLSCIn`: any `C` with an essential small loop
  at some `x ∈ C`; `GX.sphere3_not_isSLSCIn_of_essential`, the small-loop condition being
  automatic in `S³`, `GX.sphere3_exists_nhds_loops_trivial`) and Antoine's theorem
  `GX.antoine_necklace_essential` (cited, tagged `sorry`).

> In the following situations, $Y\setminus S$ is semi-locally simply connected in $Y$
> (1) $Y$ is a $n$-manifold with $n\geq 2$ and $S$ is a finite subset; (2) $Y$ is a 3-manifold and
> $S$ is a tame knot. (3) $Y$ is a simplicial complex of dimension $n$ and $S$ is a
> $(n-2)$-skeleton.
>
> Consider $Y = \RR^2$ and $S=\{(\frac{1}{n},0)~:~n\in \N^*\cup\{\infty\}\}$ and denote by $\Gamma$
> the absolute Galois group $\Gamma(\widetilde Y^S/Y)$. We see that $Y\setminus S$ is not
> semi-locally simply connected in $Y$. Let $\Gamma_2:=\langle \Gamma[\gamma_n]^2\Gamma~:~ n\in \N
> \rangle$ where $\gamma_n$ is a simple loop around $(1/n,0)$. Consider $Y_2$, the completion of
> the spread $\Gamma_2\backslash\ord(\widetilde Y^S) \rightarrow Y$. The fiber above $(0,0)$ in
> $Y_2$ is a Cantor set.
>
> If $S$ is a wild Cantor embedded into $Y = \SS^3$, then $Y\setminus S$ is not semi-locally
> simply connected in $Y$.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| §3 standing: `Y` Hausdorff, connected, LPC, first countable | ⚠ weakened: not used |
| item 1: `n ≥ 2` | ⚠ weakened: `E` nontrivial (`n ≥ 1`), finding |
| item 1: `Y` an `n`-manifold | ✓ `[ChartedSpace E Y]`, any real normed `E` |
| item 2: `Y` a 3-manifold | ⚠ weakened: local models in any finite-dimensional `E`, `dim ≥ 2` |
| item 2: `S` a tame knot | ⚠ read: locally polygonal up to local homeomorphism (SCOPE (b)) |
| item 3: `Y` a simplicial complex of dimension `n` | ⚠ corrected: every face in a face with `≥ n` vertices (finding: false otherwise, connected counterexample); ⚠ strengthened: LOCALLY FINITE geometric complex, subspace topology (= weak topology there; mathlib has no weak topology); the bound on dimension not used |
| ex. 1570: `Y = ℝ²` | ✓ `ℂ` |
| ex. 1578: `S` a wild Cantor set in `S³` | ⚠ corrected: Antoine's necklace (the cited class; Antoine's theorem a tagged `sorry`); false for wild Cantor sets with simply connected complement (cited existence, tagged `sorry`) (SCOPE (e)) |

## SCOPE (disclosed)

(a) Item 1: the codimension condition `n ≥ 2` is not needed for the notion `GX.IsSLSCIn` (as for
`rem:simple_cases`, WP-26f); `n ≥ 1` is needed for density. (b) Item 2: "tame knot" is read as
LOCALLY POLYGONAL: every point has an open neighbourhood `V` and a homeomorphism of `V` onto an
open subset of `E` carrying `V ∩ S` onto a finite union of segments (`GX.IsLocallyPolygonal`); this
covers the classical tame knots of `ℝ³` (images of polygonal knots by homeomorphisms of `ℝ³`,
`GX.isLocallyPolygonal_homeomorph_image`), and in a 3-manifold it is local tameness (equivalent to
tameness and to local flatness by Bing–Moise, which is NOT formalized). Being a knot (a circle) is
not used. (c) Item 3: `X = |K|` for a locally finite geometric complex of a real normed space,
`S` the union of the closed faces of dimension `≤ n − 2`; the hypothesis "of dimension `n`" is replaced by
"every face lies in a face with `≥ n` vertices" (`GX.HasFacesOfCardGe`, implied by purity,
`GX.IsPureDim`; it is exactly what the density of `Y ∖ S` needs): a complex of dimension `n` with
a maximal face of dimension `≤ n - 2` makes `Y ∖ S` non-dense
(`GX.following_situations_simplicial_false`: a tetrahedron with a dangling edge in `ℝ⁵`, `n = 3`,
connected as the standing hypothesis of l.1451 requires). Local finiteness and the subspace
topology are inherited from `rem:simple_cases` (WP-26f): mathlib has no weak (CW) topology on a
geometric complex, and for a locally finite complex the subspace topology IS the weak topology,
so this restricts the class of complexes, not the topology. (d)
Example 1570: `ℝ²` is `ℂ`, `S` is `GX.fibS`. The printed `Γ₂ = ⟨Γ[γₙ]²Γ⟩` is `Γ` itself (any
`g = (g γₙ⁻²) γₙ² 1`), read as the normal closure `⟨⟨[γₙ]²⟩⟩`; `γₙ` is any family of
deck transformations (the paper's simple loops are not constructed). The paper's claim is then
FALSE (finding): the fibre surjects continuously onto the infinitely many components of the
preimage of a small disc, so it is not compact; the non-compactness is stated with a tagged
`sorry` (the components of `Y₂` over a disc are not computed). `Y₂` is built literally:
`ord(\widetilde Y^S)` is `\widetilde{Y∖S}` (`GX.UniversalCover`), `Γ` acts through
`π₁(Y ∖ S)` (`GX.AbsGamma`), `GX.AbsGalY₂` is the Fox completion (`GX.SpreadEnd`) of
`Γ₂ \ \widetilde{Y∖S} → Y`. The first claim is proved for `GX.IsSLSCIn`, i.e. under the
HOMOTOPY reading of "almost trivial" (WP-26e SCOPE (a), WP-26f SCOPE (b), awaiting a ruling); the
positive results of the first example hold a fortiori in the literal compact-open reading, the
negative one is not proved there (it would need the local constancy of the winding number on the
compact-open `Ω(0,0,ℂ ∖ S)`). (e) Example 1578: a Cantor set of
`S³` is tame if a homeomorphism of `S³` carries it into a great circle, wild otherwise
(`GX.IsWildCantor`). The claim is FALSE for an arbitrary wild Cantor set: there are wild Cantor
sets in `S³` with simply connected complement (Kirkor 1958; Skora, Topology Appl. 24 (1986);
Garity–Repovš–Željko, PAMS 134 (2006)), and for those `S³ ∖ C` IS semi-locally simply connected
(`GX.isSLSCIn_compl_of_simplyConnected`: cut short end arcs off a loop, join their ends inside a
small ball off `C`, conclude by simple connectivity). The density of the complement of a
Cantor set is proved (`GX.dense_compl_of_isCantorSubset`: a Cantor set is totally disconnected,
an open set of `S³` contains a great-circle arc); the existence of such wild sets and the local
non-separation of a `0`-dimensional compactum (dimension theory) are NOT formalized: they are the
tagged `sorry` of `GX.kirkor_wild_cantor_exists`, from which the unconditional refutation
`GX.wild_cantor_claim_false` follows. The positive half holds a fortiori in the literal
compact-open reading of "almost trivial" (`GX.AlmostTrivial.almostTrivialCC`). The corrected
claim is for the cited class `general_antoine`: `GX.exists_wild_cantor_not_isSLSCIn` (Antoine's
necklace is wild with non-semi-locally simply connected complement) is proved from the criterion
`GX.wild_cantor_not_isSLSCIn` (some point of `C` has, in each neighbourhood, a loop off `C`
essential in the complement of a piece of `C` away from it; no Cantor or wildness hypothesis) and
Antoine's theorem, stated precisely as `GX.antoine_necklace_essential` — at every point `x` of
the necklace, inside every neighbourhood, a meridian of a link not containing `x` is essential in
the complement of the sub-necklace in that link. Antoine's theorem (the construction of the
necklace, its homeomorphism with `cantorSet`, the non-abelian `π₁` computation of complements of
solid-torus chains, its wildness) is NOT formalized: it is that declaration's tagged `sorry`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Filter Topology Function unitInterval

namespace GX

attribute [local instance] Classical.propDecidable

set_option linter.unusedSectionVars false

/-! ### Conical sets -/

section Conical

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `T ⊆ E` is *conical at `x`*: near `x`, `T` is stable under the radial dilations
`v ↦ x + μ⁻¹ (v - x)` back from `x + μ (v - x)`, `0 < μ ≤ 1`. -/
def IsConicalAt (T : Set E) (x : E) : Prop :=
  ∃ r > 0, ∀ v, dist v x < r → ∀ μ : ℝ, 0 < μ → μ ≤ 1 → x + μ • (v - x) ∈ T → v ∈ T

theorem isConicalAt_empty (x : E) : IsConicalAt (∅ : Set E) x :=
  ⟨1, one_pos, fun _ _ _ _ _ h => h.elim⟩

theorem IsConicalAt.union {T₁ T₂ : Set E} {x : E} (h₁ : IsConicalAt T₁ x)
    (h₂ : IsConicalAt T₂ x) : IsConicalAt (T₁ ∪ T₂) x := by
  obtain ⟨r₁, hr₁, h₁⟩ := h₁
  obtain ⟨r₂, hr₂, h₂⟩ := h₂
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, fun v hv μ hμ hμ1 hw => ?_⟩
  rcases hw with hw | hw
  · exact Or.inl (h₁ v (lt_of_lt_of_le hv (min_le_left _ _)) μ hμ hμ1 hw)
  · exact Or.inr (h₂ v (lt_of_lt_of_le hv (min_le_right _ _)) μ hμ hμ1 hw)

theorem isConicalAt_biUnion {ι : Type*} {s : Set ι} (hs : s.Finite) {f : ι → Set E} {x : E}
    (h : ∀ i ∈ s, IsConicalAt (f i) x) : IsConicalAt (⋃ i ∈ s, f i) x := by
  induction s, hs using Set.Finite.induction_on with
  | empty => simpa using isConicalAt_empty x
  | @insert a s ha hs ih =>
    rw [biUnion_insert]
    exact (h a (mem_insert a s)).union (ih fun i hi => h i (mem_insert_of_mem a hi))

/-- A segment is conical at every point. -/
theorem isConicalAt_segment (a b x : E) : IsConicalAt (segment ℝ a b) x := by
  by_cases hx : x ∈ segment ℝ a b
  swap
  · have hc : IsClosed (segment ℝ a b) := by
      have := (Set.toFinite ({a, b} : Set E)).isCompact_convexHull (𝕜 := ℝ)
      rw [convexHull_pair] at this
      exact this.isClosed
    obtain ⟨r, hr, hrb⟩ := Metric.isOpen_iff.1 hc.isOpen_compl x hx
    refine ⟨r, hr, fun v hv μ hμ hμ1 hw => (hrb ?_ hw).elim⟩
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hμ.le]
    rw [dist_eq_norm] at hv
    calc μ * ‖v - x‖ ≤ 1 * ‖v - x‖ := by gcongr
      _ < r := by rwa [one_mul]
  rw [segment_eq_image'] at hx ⊢
  obtain ⟨s₀, ⟨hs0, hs1⟩, rfl⟩ := hx
  by_cases hd : b - a = 0
  · refine ⟨1, one_pos, fun v _ μ hμ _ hw => ?_⟩
    obtain ⟨s₁, -, hs⟩ := hw
    simp only [hd, smul_zero, add_zero] at hs ⊢
    have h1 : μ • (v - a) = 0 := by
      have := congrArg (fun z => z - a) hs
      simpa using this.symm
    have h2 : v - a = 0 := (smul_eq_zero.1 h1).resolve_left hμ.ne'
    exact ⟨0, ⟨le_rfl, zero_le_one⟩, by show a = v; exact (sub_eq_zero.1 h2).symm⟩
  have hdn : 0 < ‖b - a‖ := norm_pos_iff.2 hd
  set m : ℝ := min (if s₀ < 1 then 1 - s₀ else 1) (if 0 < s₀ then s₀ else 1) with hmdef
  have hm : 0 < m := by
    refine lt_min ?_ ?_
    · split_ifs with h
      · linarith
      · exact one_pos
    · split_ifs with h
      · exact h
      · exact one_pos
  have hm1 : s₀ < 1 → m ≤ 1 - s₀ := fun h => by
    rw [hmdef, if_pos h]; exact min_le_left _ _
  have hm2 : 0 < s₀ → m ≤ s₀ := fun h => by
    rw [hmdef, if_pos h]; exact min_le_right _ _
  refine ⟨m * ‖b - a‖, mul_pos hm hdn, fun v hv μ hμ _ hw => ?_⟩
  obtain ⟨s₁, ⟨ht0, ht1⟩, hs⟩ := hw
  simp only at hs
  set c : ℝ := μ⁻¹ * (s₁ - s₀) with hcdef
  have hvx : v - (a + s₀ • (b - a)) = c • (b - a) := by
    have h1 : μ • (v - (a + s₀ • (b - a))) = (s₁ - s₀) • (b - a) := by
      rw [sub_smul]
      have := congrArg (fun z => z - (a + s₀ • (b - a))) hs
      simp only [add_sub_cancel_left] at this
      rw [← this]; abel
    rw [hcdef, mul_smul, ← h1, smul_smul, inv_mul_cancel₀ hμ.ne', one_smul]
  have hcs : s₁ = s₀ + μ * c := by
    rw [hcdef, ← mul_assoc, mul_inv_cancel₀ hμ.ne', one_mul]; ring
  have hc : |c| < m := by
    rw [dist_eq_norm, hvx, norm_smul, Real.norm_eq_abs] at hv
    exact lt_of_mul_lt_mul_right hv hdn.le
  refine ⟨s₀ + c, ⟨?_, ?_⟩, ?_⟩
  · rcases le_or_gt 0 c with h | h
    · linarith
    · have h0 : 0 < s₀ := by nlinarith
      have := hm2 h0
      have := neg_abs_le c
      linarith
  · rcases le_or_gt c 0 with h | h
    · linarith
    · have h0 : s₀ < 1 := by nlinarith
      have := hm1 h0
      have := le_abs_self c
      linarith
  · show a + (s₀ + c) • (b - a) = v
    rw [add_smul, ← add_assoc, ← hvx]; abel

/-- The complement of a set conical at every point of an open `O`, with dense complement, is
semi-locally simply connected in `O`. -/
theorem isSLSCIn_subtype_compl_of_isConicalAt {O : Set E} (hO : IsOpen O) {T : Set E}
    (hT : ∀ x ∈ O, IsConicalAt T x) (hd : Dense Tᶜ) :
    IsSLSCIn (((↑) : O → E) ⁻¹' Tᶜ) := by
  refine ⟨hd.preimage hO.isOpenMap_subtype_val, fun x => ?_⟩
  obtain ⟨r, hr, hrT⟩ := hT (x : E) x.2
  obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.1 hO (x : E) x.2
  refine isSLSCAt_of_radial_contraction (M := O) (A := Tᶜ) x (lt_min hr hε)
    (fun v _ hvr μ hμ hμ1 => ?_) (fun v _ hvr hvA μ hμ hμ1 => ?_)
  · apply hεO
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hμ]
    rw [dist_eq_norm] at hvr
    calc μ * ‖v - x‖ ≤ 1 * ‖v - x‖ := by gcongr
      _ < ε := by rw [one_mul]; exact lt_of_lt_of_le hvr (min_le_right _ _)
  · exact fun hw => hvA (hrT v (lt_of_lt_of_le hvr (min_le_left _ _)) μ hμ hμ1 hw)

/-- Local models: if every point of `Y` has an open neighbourhood homeomorphic to an open subset
`O` of `E` by a homeomorphism carrying `S` to a set conical at every point of `O` with dense
complement, then `Y ∖ S` is semi-locally simply connected in `Y`. -/
theorem isSLSCIn_compl_of_local_models {Y : Type*} [TopologicalSpace Y] {S : Set Y}
    (h : ∀ y : Y, ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧ ∃ (O : Set E) (_ : IsOpen O) (φ : V ≃ₜ O)
      (T : Set E), (∀ x ∈ O, IsConicalAt T x) ∧ Dense Tᶜ ∧ ∀ v : V, (v : Y) ∈ S ↔ (φ v : E) ∈ T) :
    IsSLSCIn Sᶜ := by
  refine isSLSCIn_of_local fun y => ?_
  obtain ⟨V, hV, hyV, O, hO, φ, T, hT, hd, hS⟩ := h y
  refine ⟨V, hV, hyV, ?_⟩
  have := (isSLSCIn_subtype_compl_of_isConicalAt hO hT hd).of_homeomorph φ
  convert this using 1
  ext v
  simp [hS v]

/-- A finite set is conical at every point. -/
theorem isConicalAt_of_finite {T : Set E} (hT : T.Finite) (x : E) : IsConicalAt T x := by
  have : T = ⋃ t ∈ T, segment ℝ t t := by simp [segment_same]
  rw [this]
  exact isConicalAt_biUnion hT fun t _ => isConicalAt_segment t t x

/-- A *polygonal set*: the union of the segments `[e.1, e.2]`, `e ∈ P`. -/
def polygonalSet (P : Finset (E × E)) : Set E := ⋃ e ∈ (P : Set (E × E)), segment ℝ e.1 e.2

theorem isConicalAt_polygonalSet (P : Finset (E × E)) (x : E) :
    IsConicalAt (polygonalSet P) x :=
  isConicalAt_biUnion P.finite_toSet fun e _ => isConicalAt_segment e.1 e.2 x

/-- In dimension `≥ 2`, a segment has dense complement. -/
theorem dense_compl_segment [FiniteDimensional ℝ E] (hE : 2 ≤ Module.finrank ℝ E) (a b : E) :
    Dense (segment ℝ a b)ᶜ := by
  rw [← interior_eq_empty_iff_dense_compl, ← convexHull_pair (𝕜 := ℝ)]
  by_contra hne
  have htop := interior_convexHull_nonempty_iff_affineSpan_eq_top.1
    (Set.nonempty_iff_ne_empty.2 hne)
  have hv : vectorSpan ℝ ({a, b} : Set E) = ⊤ := by
    rw [← direction_affineSpan, htop, AffineSubspace.direction_top]
  have h1 := (collinear_iff_finrank_le_one (k := ℝ)).1 (collinear_pair ℝ a b)
  rw [hv, finrank_top] at h1
  omega

/-- In dimension `≥ 2`, a polygonal set has dense complement. -/
theorem dense_compl_polygonalSet [FiniteDimensional ℝ E] (hE : 2 ≤ Module.finrank ℝ E)
    (P : Finset (E × E)) : Dense (polygonalSet P)ᶜ := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  rw [polygonalSet, compl_iUnion₂]
  refine dense_biInter_of_isOpen (fun e _ => ?_) P.countable_toSet
    (fun e _ => dense_compl_segment hE e.1 e.2)
  have := (Set.toFinite ({e.1, e.2} : Set E)).isCompact_convexHull (𝕜 := ℝ)
  rw [convexHull_pair] at this
  exact this.isClosed.isOpen_compl

end Conical

/-! ### `ex:following_situations_semi_locally_simply`, items 1 and 2 -/

section Items

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Y : Type*} [TopologicalSpace Y]

/-- `ex:following_situations_semi_locally_simply`, item 1 (`RamcovGX.tex:1562`): if `Y` is an
`E`-manifold (`E` a nontrivial real normed space) and `S ⊆ Y` is finite, `Y ∖ S` is semi-locally
simply connected in `Y`. -/
theorem following_situations_finite [Nontrivial E] [ChartedSpace E Y] {S : Set Y}
    (hS : S.Finite) : IsSLSCIn Sᶜ := by
  refine isSLSCIn_compl_of_local_models (E := E) fun y => ?_
  set e := chartAt E y
  have hT : (e '' (S ∩ e.source)).Finite := (hS.inter_of_left _).image _
  refine ⟨e.source, e.open_source, mem_chart_source E y, e.target, e.open_target,
    e.toHomeomorphSourceTarget, e '' (S ∩ e.source), fun x _ => isConicalAt_of_finite hT x,
    hT.countable.dense_compl ℝ, fun v => ?_⟩
  show (v : Y) ∈ S ↔ e v ∈ e '' (S ∩ e.source)
  constructor
  · intro h; exact ⟨v, ⟨h, v.2⟩, rfl⟩
  · rintro ⟨w, ⟨hw, hws⟩, heq⟩
    rwa [e.injOn hws v.2 heq] at hw

/-- Item 1 for `n`-manifolds, `n ≥ 1`. -/
theorem following_situations_finite_euclidean {n : ℕ} (hn : 1 ≤ n)
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) Y] {S : Set Y} (hS : S.Finite) : IsSLSCIn Sᶜ := by
  haveI : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
  exact following_situations_finite (E := EuclideanSpace ℝ (Fin n)) hS

variable (E) in
/-- `S ⊆ Y` is *locally polygonal* (modelled on `E`): every point of `Y` has an open neighbourhood
`V` and a homeomorphism of `V` onto an open subset of `E` carrying `V ∩ S` onto a polygonal set
(SCOPE (b): the reading of "tame knot"). -/
def IsLocallyPolygonal (S : Set Y) : Prop :=
  ∀ y : Y, ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧ ∃ (O : Set E) (_ : IsOpen O) (φ : V ≃ₜ O)
    (P : Finset (E × E)), ∀ v : V, (v : Y) ∈ S ↔ (φ v : E) ∈ polygonalSet P

/-- `ex:following_situations_semi_locally_simply`, item 2 (`RamcovGX.tex:1563`), read: if `S` is
locally polygonal in `Y`, modelled on a real space of dimension `≥ 2`, then `Y ∖ S` is
semi-locally simply connected in `Y`. -/
theorem following_situations_tame [FiniteDimensional ℝ E] (hE : 2 ≤ Module.finrank ℝ E)
    {S : Set Y} (hS : IsLocallyPolygonal E S) : IsSLSCIn Sᶜ := by
  refine isSLSCIn_compl_of_local_models (E := E) fun y => ?_
  obtain ⟨V, hV, hyV, O, hO, φ, P, hP⟩ := hS y
  exact ⟨V, hV, hyV, O, hO, φ, polygonalSet P, fun x _ => isConicalAt_polygonalSet P x,
    dense_compl_polygonalSet hE P, hP⟩

/-- The image of a polygonal set by a homeomorphism of `E` (a tame knot of `ℝ³`, classically) is
locally polygonal. -/
theorem isLocallyPolygonal_homeomorph_image (g : E ≃ₜ E) (P : Finset (E × E)) :
    IsLocallyPolygonal E (g '' polygonalSet P) := by
  intro y
  refine ⟨univ, isOpen_univ, mem_univ y, univ, isOpen_univ,
    (Homeomorph.Set.univ E).trans (g.symm.trans (Homeomorph.Set.univ E).symm), P, fun v => ?_⟩
  show (v : E) ∈ g '' polygonalSet P ↔ g.symm v ∈ polygonalSet P
  constructor
  · rintro ⟨w, hw, hwv⟩
    rw [← hwv, g.symm_apply_apply]; exact hw
  · intro h
    exact ⟨g.symm v, h, g.apply_symm_apply v⟩

/-- `ex:following_situations_semi_locally_simply`, item 2, the classical tame knots of `ℝ³`: the
complement of the image of a polygonal set by a homeomorphism of `ℝ³` is semi-locally simply
connected in `ℝ³`. -/
theorem following_situations_tame_knot (g : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3))
    (P : Finset (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))) :
    IsSLSCIn (g '' polygonalSet P)ᶜ :=
  following_situations_tame (by rw [finrank_euclideanSpace_fin]; norm_num)
    (isLocallyPolygonal_homeomorph_image g P)

end Items

/-! ### `ex:following_situations_semi_locally_simply`, item 3 -/

section Simplicial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The faces of dimension `≤ n - 2` (card `≤ n - 1`) of `K`: its `(n-2)`-skeleton. -/
def skeletonFaces (K : Geometry.SimplicialComplex ℝ E) (n : ℕ) : Set (Finset E) :=
  {s | s ∈ K.faces ∧ s.card + 1 ≤ n}

/-- `K` is *pure of dimension `n`*: every face lies in a face with `n + 1` vertices. -/
def IsPureDim (K : Geometry.SimplicialComplex ℝ E) (n : ℕ) : Prop :=
  ∀ s ∈ K.faces, ∃ τ ∈ K.faces, s ⊆ τ ∧ τ.card = n + 1

/-- Every face of `K` lies in a face with at least `n` vertices (of dimension `≥ n - 1`): the
exact condition under which the `(n-2)`-skeleton has dense complement (weaker than purity). -/
def HasFacesOfCardGe (K : Geometry.SimplicialComplex ℝ E) (n : ℕ) : Prop :=
  ∀ s ∈ K.faces, ∃ τ ∈ K.faces, s ⊆ τ ∧ n ≤ τ.card

theorem IsPureDim.hasFacesOfCardGe {K : Geometry.SimplicialComplex ℝ E} {n : ℕ}
    (h : IsPureDim K n) : HasFacesOfCardGe K n := fun s hs => by
  obtain ⟨τ, hτ, hsτ, hc⟩ := h s hs
  exact ⟨τ, hτ, hsτ, by omega⟩

/-- The barycentre of a simplex `τ` lies in no proper face `t ⊂ τ`. -/
theorem barycentre_not_mem_convexHull {τ t : Finset E} (hτ : AffineIndependent ℝ ((↑) : τ → E))
    (ht : t ⊆ τ) (htτ : t ≠ τ) :
    ∑ v ∈ τ, (1 / (τ.card : ℝ)) • v ∉ convexHull ℝ (t : Set E) := by
  intro hb
  obtain ⟨c, -, hc1, hcw⟩ := Finset.mem_convexHull'.1 hb
  obtain ⟨w, hwτ, hwt⟩ : ∃ w ∈ τ, w ∉ t := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    exact htτ (Finset.Subset.antisymm ht h)
  have hpos : 0 < (τ.card : ℝ) := by exact_mod_cast Finset.card_pos.2 ⟨w, hwτ⟩
  set c' : E → ℝ := fun y => if y ∈ t then c y else 0
  have hc'1 : ∑ y ∈ τ, c' y = 1 := by
    rw [← hc1, ← Finset.sum_subset ht (fun y _ hy => by simp [c', hy])]
    exact Finset.sum_congr rfl fun y hy => by simp [c', hy]
  have hc'w : ∑ y ∈ τ, c' y • y = ∑ v ∈ τ, (1 / (τ.card : ℝ)) • v := by
    rw [← hcw, ← Finset.sum_subset ht (fun y _ hy => by simp [c', hy])]
    exact Finset.sum_congr rfl fun y hy => by simp [c', hy]
  have hw1 : ∑ y ∈ τ, (fun _ : E => 1 / (τ.card : ℝ)) y = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul]; field_simp
  have := hτ.eq_of_sum_eq_sum_subtype (w₁ := fun _ => 1 / (τ.card : ℝ)) (w₂ := c')
    (hw1.trans hc'1.symm) hc'w.symm w hwτ
  simp only [c', hwt, if_false] at this
  have : (0 : ℝ) < 1 / τ.card := by positivity
  linarith

/-- If every face lies in a face with `≥ n` vertices (e.g. a pure `n`-dimensional complex), the
complement of the `(n-2)`-skeleton is dense. -/
theorem dense_compl_skeleton (K : Geometry.SimplicialComplex ℝ E) {n : ℕ}
    (hK : HasFacesOfCardGe K n) :
    Dense (((↑) : K.space → E) ⁻¹' (⋃ s ∈ skeletonFaces K n, convexHull ℝ (s : Set E))ᶜ) := by
  intro x
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨σ₀, hσ, hxσ⟩ := Geometry.SimplicialComplex.mem_space_iff.1 x.2
  obtain ⟨τ, hτ, hστ, hτc⟩ := hK σ₀ hσ
  have hxτ : (x : E) ∈ convexHull ℝ (τ : Set E) := convexHull_mono (by exact_mod_cast hστ) hxσ
  set b : E := ∑ v ∈ τ, (1 / (τ.card : ℝ)) • v
  have hbτ : b ∈ convexHull ℝ (τ : Set E) := by
    have hne : (τ.card : ℝ) ≠ 0 := by
      have := (K.nonempty_of_mem_faces hτ).card_pos
      positivity
    refine Finset.mem_convexHull'.2 ⟨fun _ => 1 / (τ.card : ℝ), fun _ _ => by positivity, ?_, rfl⟩
    rw [Finset.sum_const, nsmul_eq_mul]; field_simp
  set μ : ℝ := min 1 (ε / (‖b - x‖ + 1))
  have hμ : 0 < μ := lt_min one_pos (by positivity)
  have hμ1 : μ ≤ 1 := min_le_left _ _
  have hyτ := (convex_convexHull ℝ (τ : Set E)).add_smul_sub_mem hxτ hbτ ⟨hμ.le, hμ1⟩
  refine ⟨⟨_, Geometry.SimplicialComplex.convexHull_subset_space hτ hyτ⟩, ?_, ?_⟩
  · intro hy
    obtain ⟨ρ, ⟨hρ, hρc⟩, hyρ⟩ := mem_iUnion₂.1 hy
    have hint := K.inter_subset_convexHull hρ hτ ⟨hyρ, hyτ⟩
    rw [← Finset.coe_inter] at hint
    have hb := mem_convexHull_face_of_add_smul_sub_mem (K.indep hτ) Finset.inter_subset_right hxτ
      hbτ hμ hμ1 hint
    refine barycentre_not_mem_convexHull (K.indep hτ) Finset.inter_subset_right (fun h => ?_) hb
    have := Finset.card_le_card (Finset.inter_subset_left (s₁ := ρ) (s₂ := τ))
    rw [h] at this
    omega
  · rw [Subtype.dist_eq, dist_eq_norm]
    show ‖(x : E) - ((x : E) + μ • (b - x))‖ < ε
    rw [sub_add_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg hμ.le]
    have h1 : 0 ≤ ‖b - x‖ := norm_nonneg _
    calc μ * ‖b - x‖ ≤ ε / (‖b - x‖ + 1) * ‖b - x‖ := by gcongr; exact min_le_right _ _
      _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith

/-- `ex:following_situations_semi_locally_simply`, item 3 (`RamcovGX.tex:1564`), corrected: for a
locally finite geometric simplicial complex `K` of a real normed space (subspace topology, which
for a locally finite complex is its weak topology) every face of which lies in a face with
`≥ n` vertices, the complement of the `(n-2)`-skeleton is semi-locally simply connected in
`|K|`. -/
theorem following_situations_simplicial (K : Geometry.SimplicialComplex ℝ E)
    (hK : LocallyFinite fun τ : K.faces => convexHull ℝ ((τ : Finset E) : Set E)) {n : ℕ}
    (hfaces : HasFacesOfCardGe K n) :
    IsSLSCIn (((↑) : K.space → E) ⁻¹' (⋃ s ∈ skeletonFaces K n, convexHull ℝ (s : Set E))ᶜ) :=
  isSLSCIn_compl_faces_of_locallyFinite K hK _ (fun _ hs => hs.1) (dense_compl_skeleton K hfaces)

/-- Item 3 for a PURE `n`-dimensional locally finite complex. -/
theorem following_situations_simplicial_pure (K : Geometry.SimplicialComplex ℝ E)
    (hK : LocallyFinite fun τ : K.faces => convexHull ℝ ((τ : Finset E) : Set E)) {n : ℕ}
    (hpure : IsPureDim K n) :
    IsSLSCIn (((↑) : K.space → E) ⁻¹' (⋃ s ∈ skeletonFaces K n, convexHull ℝ (s : Set E))ᶜ) :=
  following_situations_simplicial K hK hpure.hasFacesOfCardGe

end Simplicial

/-! ### Item 3 is false for complexes with a maximal face of low dimension -/

section SimplicialCex

/-- The standard basis vectors of `ℝ⁵`. -/
abbrev cexV (i : Fin 5) : Fin 5 → ℝ := Pi.basisFun ℝ (Fin 5) i

/-- The tetrahedron `{e₀, e₁, e₂, e₃}`. -/
def cexTet : Finset (Fin 5 → ℝ) := Finset.image cexV {0, 1, 2, 3}

/-- The dangling edge `{e₃, e₄}`. -/
def cexEdge : Finset (Fin 5 → ℝ) := Finset.image cexV {3, 4}

/-- The faces of the counterexample: the faces of the tetrahedron and of the dangling edge. -/
def cexFaces : Set (Finset (Fin 5 → ℝ)) :=
  {s | (s ⊆ cexTet ∨ s ⊆ cexEdge) ∧ s.Nonempty}

theorem cexV_injective : Injective cexV := (Pi.basisFun ℝ (Fin 5)).linearIndependent.injective

theorem cexV_apply (i j : Fin 5) : cexV i j = if j = i then 1 else 0 := by
  simp [cexV, Pi.single_apply]

/-- The counterexample: a tetrahedron with a dangling edge in `ℝ⁵`, a connected complex of
dimension `3` whose edge `{e₃, e₄}` is a maximal face of dimension `1 = 3 - 2`. -/
def cexK : Geometry.SimplicialComplex ℝ (Fin 5 → ℝ) :=
  Geometry.SimplicialComplex.ofAffineIndependent
    ⟨cexFaces, by
      have hL : IsLowerSet {s : Finset (Fin 5 → ℝ) | s ⊆ cexTet ∨ s ⊆ cexEdge} := by
        intro a b hba ha
        rcases ha with ha | ha
        · exact Or.inl (hba.trans ha)
        · exact Or.inr (hba.trans ha)
      exact hL.isRelLowerSet_sep Finset.Nonempty⟩
    (by
      refine (Pi.basisFun ℝ (Fin 5)).linearIndependent.affineIndependent.range.mono ?_
      intro x hx
      obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.1 hx
      have hs' : (s : Set (Fin 5 → ℝ)) ⊆ range cexV := by
        rcases hs.1 with h | h
        · intro y hy
          obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (h hy)
          exact mem_range_self i
        · intro y hy
          obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (h hy)
          exact mem_range_self i
      exact hs' hxs)

theorem cexK_faces : cexK.faces = cexFaces := rfl

theorem cexTet_card : cexTet.card = 4 := by
  rw [cexTet, Finset.card_image_of_injective _ cexV_injective]; rfl

theorem cexEdge_card : cexEdge.card = 2 := by
  rw [cexEdge, Finset.card_image_of_injective _ cexV_injective]; rfl

theorem cexTet_mem : cexTet ∈ cexK.faces :=
  ⟨Or.inl subset_rfl, ⟨cexV 0, Finset.mem_image_of_mem _ (by simp)⟩⟩

theorem cexEdge_mem : cexEdge ∈ cexK.faces :=
  ⟨Or.inr subset_rfl, ⟨cexV 3, Finset.mem_image_of_mem _ (by simp)⟩⟩

theorem convexHull_cexTet_subset :
    convexHull ℝ (cexTet : Set (Fin 5 → ℝ)) ⊆ {z | z 4 = 0} := by
  refine convexHull_min (fun y hy => ?_) ?_
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hy
    show cexV i 4 = 0
    rw [cexV_apply]
    fin_cases hi <;> simp
  · intro x hx y hy a b _ _ _
    show (a • x + b • y) 4 = 0
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [show x 4 = 0 from hx, show y 4 = 0 from hy]; ring

/-- `|cexK|` is the tetrahedron union the edge. -/
theorem cexK_space : cexK.space =
    convexHull ℝ (cexTet : Set (Fin 5 → ℝ)) ∪ convexHull ℝ (cexEdge : Set (Fin 5 → ℝ)) := by
  refine Subset.antisymm (fun z hz => ?_) (union_subset
    (Geometry.SimplicialComplex.convexHull_subset_space cexTet_mem)
    (Geometry.SimplicialComplex.convexHull_subset_space cexEdge_mem))
  obtain ⟨s, hs, hzs⟩ := Geometry.SimplicialComplex.mem_space_iff.1 hz
  rcases hs.1 with h | h
  · exact Or.inl (convexHull_mono (by exact_mod_cast h) hzs)
  · exact Or.inr (convexHull_mono (by exact_mod_cast h) hzs)

/-- `|cexK|` is connected (the paper's standing hypothesis, `RamcovGX.tex:1451`). -/
theorem cexK_isConnected : IsConnected cexK.space := by
  have h3t : cexV 3 ∈ (cexTet : Set (Fin 5 → ℝ)) := Finset.mem_image_of_mem _ (by simp)
  have h3e : cexV 3 ∈ (cexEdge : Set (Fin 5 → ℝ)) := Finset.mem_image_of_mem _ (by simp)
  rw [cexK_space]
  exact ((convex_convexHull ℝ _).isConnected ⟨_, subset_convexHull ℝ _ h3t⟩).union
    ⟨cexV 3, subset_convexHull ℝ _ h3t, subset_convexHull ℝ _ h3e⟩
    ((convex_convexHull ℝ _).isConnected ⟨_, subset_convexHull ℝ _ h3e⟩)

/-- `ex:following_situations_semi_locally_simply`, item 3, is FALSE as written: a finite,
connected simplicial complex of dimension `3` (all faces have at most `4` vertices, one has `4`)
whose `1`-skeleton has non-dense complement, which is therefore not semi-locally simply
connected in it (the dangling edge). -/
theorem following_situations_simplicial_false :
    ∃ K : Geometry.SimplicialComplex ℝ (Fin 5 → ℝ), K.faces.Finite ∧ IsConnected K.space ∧
      (∀ s ∈ K.faces, s.card ≤ 3 + 1) ∧ (∃ s ∈ K.faces, s.card = 3 + 1) ∧
      ¬ IsSLSCIn (((↑) : K.space → (Fin 5 → ℝ)) ⁻¹'
        (⋃ s ∈ skeletonFaces K 3, convexHull ℝ (s : Set (Fin 5 → ℝ)))ᶜ) := by
  refine ⟨cexK, ?_, cexK_isConnected, ?_, ⟨cexTet, cexTet_mem, cexTet_card⟩, ?_⟩
  · refine (Finset.univ.image cexV).powerset.finite_toSet.subset fun s hs => ?_
    rw [cexK_faces] at hs
    rw [Finset.coe_powerset, mem_preimage, mem_powerset_iff, Finset.coe_subset]
    rcases hs.1 with h | h
    · exact h.trans (Finset.image_subset_image (Finset.subset_univ _))
    · exact h.trans (Finset.image_subset_image (Finset.subset_univ _))
  · intro s hs
    rw [cexK_faces] at hs
    rcases hs.1 with h | h
    · exact (Finset.card_le_card h).trans cexTet_card.le
    · exact (Finset.card_le_card h).trans (by rw [cexEdge_card]; norm_num)
  · rintro ⟨hd, -⟩
    have hv4 : cexV 4 ∈ cexK.space :=
      Geometry.SimplicialComplex.convexHull_subset_space cexEdge_mem
        (subset_convexHull ℝ _ (Finset.mem_image_of_mem _ (by simp)))
    set W : Set cexK.space := {z | 1 / 2 < (z : Fin 5 → ℝ) 4}
    have hW : IsOpen W :=
      isOpen_lt continuous_const ((continuous_apply 4).comp continuous_subtype_val)
    obtain ⟨z, hzW, hzS⟩ := hd.inter_open_nonempty W hW ⟨⟨_, hv4⟩, by
      show 1 / 2 < cexV 4 4
      rw [cexV_apply]; norm_num⟩
    obtain ⟨s, hs, hzs⟩ := Geometry.SimplicialComplex.mem_space_iff.1 z.2
    have hs' := hs
    rw [cexK_faces] at hs'
    rcases hs'.1 with h | h
    · have hz4 : (z : Fin 5 → ℝ) 4 = 0 :=
        convexHull_cexTet_subset (convexHull_mono (by exact_mod_cast h) hzs)
      have : (1 : ℝ) / 2 < (z : Fin 5 → ℝ) 4 := hzW
      linarith
    · apply hzS
      refine mem_iUnion₂.2 ⟨s, ⟨hs, ?_⟩, hzs⟩
      have := Finset.card_le_card h
      rw [cexEdge_card] at this
      omega

end SimplicialCex

/-! ### A criterion for failure of semi-local simple connectedness -/

section Essential

variable {X : Type*} [TopologicalSpace X]

/-- The argument of `ex:consider_denote_absolute_galois` and `ex:wild_cantor_general_antoine`:
if every neighbourhood `V` of `x` contains a loop `γ` of `Ω(x,x,V ∩ U)` which is essential in the
complement of some `K ⊆ X ∖ U` (`x ∉ K`), while the loops of some neighbourhood `W` of `x` are
trivial there, then `U` is not semi-locally simply connected at `x`. -/
theorem not_isSLSCAt_of_essential {U : Set X} {x : X}
    (h : ∀ V ∈ 𝓝 x, ∃ (K : Set X) (γ : Path x x), x ∉ K ∧ U ⊆ Kᶜ ∧ MemOmega (V ∩ U) γ ∧
      ¬ HomotopicIn Kᶜ γ (Path.refl x) ∧
      ∃ W ∈ 𝓝 x, ∀ δ : Path x x, (∀ t, δ t ∈ W) → HomotopicIn Kᶜ δ (Path.refl x)) :
    ¬ IsSLSCAt U x := by
  rintro ⟨V, hV, -, hxV, hloop⟩
  obtain ⟨K, γ, hxK, hUK, hγ, hne, W, hW, hWtriv⟩ := h V (hV.mem_nhds hxV)
  obtain ⟨-, hat⟩ := hloop γ hγ
  obtain ⟨γ', hγ', F, hF⟩ := hat W hW
  apply hne
  have h1 : HomotopicIn Kᶜ γ γ' := by
    refine ⟨F, fun z => ?_⟩
    obtain ⟨s, t⟩ := z
    rcases eq_or_lt_of_le t.2.1 with h0 | h0
    · have : t = 0 := Subtype.ext h0.symm
      rw [this, F.source]; exact hxK
    rcases eq_or_lt_of_le t.2.2 with h1 | h1
    · have : t = 1 := Subtype.ext h1
      rw [this, F.target]; exact hxK
    exact hUK (hF s t h0 h1)
  have h2 : HomotopicIn Kᶜ γ' (Path.refl x) := by
    refine hWtriv γ' fun t => ?_
    rcases eq_or_lt_of_le t.2.1 with h0 | h0
    · have : t = 0 := Subtype.ext h0.symm
      rw [this, γ'.source]; exact mem_of_mem_nhds hW
    rcases eq_or_lt_of_le t.2.2 with h1 | h1
    · have : t = 1 := Subtype.ext h1
      rw [this, γ'.target]; exact mem_of_mem_nhds hW
    exact (hγ' t h0 h1).1
  exact h1.trans h2

end Essential

/-! ### `ex:consider_denote_absolute_galois` -/

section AbsGal

/-- The loop `t ↦ p - p e^{2iπt}` based at `0`, around `p`. -/
def absGalLoop (p : ℝ) : Path (0 : ℂ) 0 where
  toFun t := (p : ℂ) - p * Complex.exp (((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by
    simp only [Set.Icc.coe_one, mul_one]
    rw [show ((2 * Real.pi : ℝ) : ℂ) * Complex.I = 2 * Real.pi * Complex.I by push_cast; ring,
      Complex.exp_two_pi_mul_I, mul_one, sub_self]

theorem absGalLoop_apply (p : ℝ) (t : I) :
    absGalLoop p t = (p : ℂ) - p * Complex.exp (((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I) :=
  rfl

theorem norm_absGalLoop_le {p : ℝ} (hp : 0 ≤ p) (t : I) : ‖absGalLoop p t‖ ≤ 2 * p := by
  rw [absGalLoop_apply]
  calc ‖(p : ℂ) - p * Complex.exp _‖ ≤ ‖(p : ℂ)‖ + ‖(p : ℂ) * Complex.exp _‖ := norm_sub_le _ _
    _ = 2 * p := by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_of_nonneg hp]
      ring

theorem mem_fibS_im {z : ℂ} (hz : z ∈ fibS) : z.im = 0 := by
  rcases hz with rfl | ⟨n, rfl⟩
  · rfl
  · exact Complex.ofReal_im _

/-- `p = 1/(2k+3)` belongs to `S`. -/
theorem absGalPt_mem (k : ℕ) : (((1 / (2 * (k : ℝ) + 3)) : ℝ) : ℂ) ∈ fibS := by
  refine Or.inr ⟨2 * k + 2, ?_⟩
  simp only
  congr 2
  push_cast; ring

/-- For `p = 1/(2k+3)`, the loop `absGalLoop p` meets `S` only at its ends. -/
theorem absGalLoop_not_mem (k : ℕ) {t : I} (h0 : 0 < (t : ℝ)) (h1 : (t : ℝ) < 1) :
    absGalLoop (1 / (2 * (k : ℝ) + 3)) t ∉ fibS := by
  set p : ℝ := 1 / (2 * (k : ℝ) + 3)
  have hp : 0 < p := by positivity
  intro hmem
  have him := mem_fibS_im hmem
  rw [absGalLoop_apply] at him hmem
  simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, zero_mul, zero_sub, add_zero,
    neg_eq_zero, mul_eq_zero, hp.ne', false_or] at him
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.1 him
  have hn1 : n = 1 := by
    have hπ := Real.pi_pos
    have a : (0 : ℝ) < n := by nlinarith
    have b : (n : ℝ) < 2 := by nlinarith
    have a' : 0 < n := by exact_mod_cast a
    have b' : n < 2 := by exact_mod_cast b
    omega
  subst hn1
  have ht : 2 * Real.pi * (t : ℝ) = Real.pi := by rw [← hn]; simp
  rw [ht] at hmem
  have hval : (p : ℂ) - p * Complex.exp ((Real.pi : ℂ) * Complex.I) = ((2 * p : ℝ) : ℂ) := by
    rw [Complex.exp_pi_mul_I]; push_cast; ring
  rw [hval] at hmem
  rcases hmem with h | ⟨j, hj⟩
  · have := congrArg Complex.re h
    simp only [Complex.ofReal_re, Complex.zero_re] at this
    linarith
  · have hj' : (1 / ((j : ℝ) + 1)) = 2 * p := Complex.ofReal_injective hj
    simp only [p] at hj'
    field_simp at hj'
    have : (2 * (j + 1) : ℕ) = 2 * k + 3 := by exact_mod_cast (by linarith : (2 * ((j : ℝ) + 1)) = 2 * k + 3)
    omega

/-- `z ↦ z - p`, from `ℂ ∖ {p}` to `ℂ ∖ {0}`. -/
def subPt (p : ℂ) : C(({p}ᶜ : Set ℂ), CStar) :=
  ⟨fun z => ⟨(z : ℂ) - p, sub_ne_zero.2 z.2⟩, by fun_prop⟩

/-- `absGalLoop p` is not null-homotopic in `ℂ ∖ {p}` (it winds once around `p`). -/
theorem absGalLoop_not_homotopicIn {p : ℝ} (hp : p ≠ 0) :
    ¬ HomotopicIn ({(p : ℂ)}ᶜ : Set ℂ) (absGalLoop p) (Path.refl 0) := by
  rw [homotopicIn_iff]
  rintro ⟨h1, h2, hom⟩
  have hw := cWinding_homotopic (Path.Homotopic.map hom (subPt (p : ℂ)))
  have hp' : (-(p : ℂ)) ≠ 0 := neg_ne_zero.2 (Complex.ofReal_ne_zero.2 hp)
  have e1 : cWinding ((pathToSub (absGalLoop p) h1).map (subPt (p : ℂ)).continuous) = 1 := by
    refine cWinding_eq _ (Γ := ⟨fun t => Complex.log (-(p : ℂ)) +
      ((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I, by fun_prop⟩) (fun t => ?_) ?_
    · show Complex.exp (Complex.log (-(p : ℂ)) + _) = absGalLoop p t - p
      rw [Complex.exp_add, Complex.exp_log hp', absGalLoop_apply]; ring
    · simp only [ContinuousMap.coe_mk, Set.Icc.coe_one, Set.Icc.coe_zero, mul_one, mul_zero,
        Complex.ofReal_zero, zero_mul, add_zero, Int.cast_one, one_mul]
      push_cast; ring
  have e2 : cWinding ((pathToSub (Path.refl (0 : ℂ)) h2).map (subPt (p : ℂ)).continuous) = 0 := by
    refine cWinding_eq _ (Γ := ContinuousMap.const I (Complex.log (-(p : ℂ)))) (fun t => ?_)
      (by simp)
    show Complex.exp (Complex.log (-(p : ℂ))) = (0 : ℂ) - p
    rw [Complex.exp_log hp', zero_sub]
  rw [e1, e2] at hw
  exact one_ne_zero hw

/-- Loops in a ball around `0` missing `p` are null-homotopic in `ℂ ∖ {p}`. -/
theorem homotopicIn_refl_of_ball {p : ℝ} (hp : 0 < p) (δ : Path (0 : ℂ) 0)
    (hδ : ∀ t, δ t ∈ Metric.ball (0 : ℂ) p) :
    HomotopicIn ({(p : ℂ)}ᶜ : Set ℂ) δ (Path.refl 0) := by
  have := homotopicIn_map_of_convex (U := ({(p : ℂ)}ᶜ : Set ℂ)) δ (Path.refl 0)
    (convex_ball (0 : ℂ) p) hδ (fun _ => Metric.mem_ball_self hp) continuous_id (fun e he => by
      intro hep
      rw [mem_singleton_iff] at hep
      change e = (p : ℂ) at hep
      rw [hep, Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg hp.le]
        at he
      exact lt_irrefl _ he)
  exact this.of_eq (Path.map_id _) (Path.map_id _)

/-- `ex:consider_denote_absolute_galois` (`RamcovGX.tex:1571`), first claim: for
`S = {1/n} ∪ {0}`, `ℂ ∖ S` is not semi-locally simply connected at `0`. -/
theorem absGal_not_isSLSCAt : ¬ IsSLSCAt fibSᶜ (0 : ℂ) := by
  refine not_isSLSCAt_of_essential fun V hV => ?_
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.1 hV
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / r)
  set p : ℝ := 1 / (2 * (k : ℝ) + 3)
  have hp : 0 < p := by positivity
  have h2p : 2 * p < r := by
    have h1 : 1 < r * k := by rwa [div_lt_iff₀ hr, mul_comm] at hk
    simp only [p]
    rw [mul_one_div, div_lt_iff₀ (by positivity)]
    nlinarith
  refine ⟨{(p : ℂ)}, absGalLoop p, ?_, ?_, fun t h0 h1 => ⟨hrV ?_, absGalLoop_not_mem k h0 h1⟩,
    absGalLoop_not_homotopicIn hp.ne', Metric.ball 0 p, Metric.ball_mem_nhds 0 hp,
    fun δ hδ => homotopicIn_refl_of_ball hp δ hδ⟩
  · rw [mem_singleton_iff, eq_comm, Complex.ofReal_eq_zero]; exact hp.ne'
  · intro z hz hzp
    rw [mem_singleton_iff] at hzp
    exact hz (hzp ▸ absGalPt_mem k)
  · rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt (norm_absGalLoop_le hp.le t) h2p

/-- `ex:consider_denote_absolute_galois`, first claim: `ℂ ∖ S` is not semi-locally simply
connected in `ℂ`. -/
theorem absGal_not_isSLSCIn : ¬ IsSLSCIn (fibSᶜ : Set ℂ) := fun h => absGal_not_isSLSCAt (h.2 0)

/-- The printed `Γ₂ = ⟨Γ g² Γ⟩` (`RamcovGX.tex:1571`): the subgroup generated by the double
cosets `Γ gₙ² Γ`. -/
def printedGamma2 {G : Type*} [Group G] {ι : Type*} (g : ι → G) : Subgroup G :=
  Subgroup.closure (⋃ n, {x | ∃ a b : G, x = a * g n ^ 2 * b})

/-- The printed `Γ₂` is the whole group (as soon as one `gₙ` is given): `x = (x gₙ⁻²) gₙ² 1`. -/
theorem printedGamma2_eq_top {G : Type*} [Group G] {ι : Type*} [Nonempty ι] (g : ι → G) :
    printedGamma2 g = ⊤ := by
  refine eq_top_iff.2 fun x _ => Subgroup.subset_closure ?_
  obtain ⟨n⟩ := ‹Nonempty ι›
  exact mem_iUnion.2 ⟨n, x * (g n ^ 2)⁻¹, 1, by group⟩

/-! The space `Y₂` of `RamcovGX.tex:1572`, with the intended `Γ₂`. -/

variable (y₀ : (fibSᶜ : Set ℂ))

/-- `Γ = Γ(\widetilde Y^S/Y)`, through its action on `ord(\widetilde Y^S) = \widetilde{Y∖S}`:
`π₁(ℂ ∖ S, y₀)` (`GX.UniversalCover.deckHom`, `GX.deckOrdEquiv`). -/
abbrev AbsGamma : Type := FundamentalGroup (fibSᶜ : Set ℂ) y₀

/-- The intended `Γ₂`: the normal closure of the squares `[γₙ]²`. -/
def gamma2 (g : ℕ → AbsGamma y₀) : Subgroup (AbsGamma y₀) :=
  Subgroup.normalClosure (range fun n => g n ^ 2)

/-- `Γ₂` as a group of homeomorphisms of `\widetilde{Y∖S}`. -/
def gamma2Homeo (g : ℕ → AbsGamma y₀) :
    Subgroup (UniversalCover (fibSᶜ : Set ℂ) y₀ ≃ₜ UniversalCover (fibSᶜ : Set ℂ) y₀) :=
  ((gamma2 y₀ g).map UniversalCover.deckHom).map
    (deckGroup (UniversalCover.proj (fibSᶜ : Set ℂ) y₀)).subtype

/-- `Γ₂ \ ord(\widetilde Y^S)`. -/
abbrev AbsGalOrdY₂ (g : ℕ → AbsGamma y₀) : Type := HomeoQuotient (gamma2Homeo y₀ g)

/-- The spread `Γ₂ \ ord(\widetilde Y^S) → Y`. -/
def ordY₂Proj (g : ℕ → AbsGamma y₀) : AbsGalOrdY₂ y₀ g → ℂ :=
  Quotient.lift (univCoverProj fibS y₀) fun a b ⟨φ, hφ, h⟩ => by
    obtain ⟨ψ, -, rfl⟩ := Subgroup.mem_map.1 hφ
    rw [← h]
    exact (congrArg Subtype.val (congrFun ψ.2 a)).symm

/-- `Y₂`, the completion of the spread `Γ₂ \ ord(\widetilde Y^S) → Y`. -/
abbrev AbsGalY₂ (g : ℕ → AbsGamma y₀) : Type := SpreadEnd (ordY₂Proj y₀ g)

/-- The fibre of `Y₂` above `0`. -/
def y₂Fiber0 (g : ℕ → AbsGamma y₀) : Set (AbsGalY₂ y₀ g) := SpreadEnd.base ⁻¹' {0}

/-- `z ↦ z - q`, from `ℂ ∖ S` to `ℂ ∖ {0}`, for `q ∈ S`. -/
def subFib (q : ℂ) (hq : q ∈ fibS) : C((fibSᶜ : Set ℂ), CStar) :=
  ⟨fun z => ⟨(z : ℂ) - q, sub_ne_zero.2 fun h => z.2 (h ▸ hq)⟩, by fun_prop⟩

/-- The winding number of a loop of `ℂ ∖ S` around `q ∈ S`. -/
def windAt (q : ℂ) (hq : q ∈ fibS) (γ : Path y₀ y₀) : ℤ := cWinding (γ.map (subFib q hq).continuous)

/-- The point `1/(m+1)` of `S`. -/
theorem fibPt_mem (m : ℕ) : (((1 / ((m : ℝ) + 1)) : ℝ) : ℂ) ∈ fibS := Or.inr ⟨m, rfl⟩

/-- `ex:consider_denote_absolute_galois`, the fibre claim, refuted (finding): for any loops
`γₙ` winding once around `1/(n+1)` and not around the other points of `S` (the paper's simple
loops), the fibre above `0` of `Y₂` (intended `Γ₂`) is NOT compact. -/
theorem absGal_Y₂_fiber_not_compact (γ : ℕ → Path y₀ y₀)
    (hγ : ∀ n m, windAt y₀ _ (fibPt_mem m) (γ n) = if n = m then 1 else 0)
    (hγ0 : ∀ n, windAt y₀ 0 (mem_insert 0 _) (γ n) = 0) :
    ¬ IsCompact (y₂Fiber0 y₀ fun n => FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (γ n))) := by
  sorry -- SORRY(ex:consider_denote_absolute_galois): the fibre maps continuously onto the set of components of the preimage in Y₂ of the disc D₂ (around 0, missing 1), which is Γ/(Γ₂·H₂), H₂ the image of π₁(D₂ ∖ S); showing this coset space infinite needs π₁(ℂ ∖ S) free on the small loops and the loop around S, and a non-abelian quotient Γ → D_∞ (γ₁ ↦ s, γₙ ↦ t) killing Γ₂ and sending H₂ into ⟨t⟩, none of which is available

/-- `ex:consider_denote_absolute_galois`, the fibre claim as printed: the fibre above `0` of `Y₂`
is not a Cantor set (a Cantor set is compact). -/
theorem absGal_Y₂_fiber_not_cantor (γ : ℕ → Path y₀ y₀)
    (hγ : ∀ n m, windAt y₀ _ (fibPt_mem m) (γ n) = if n = m then 1 else 0)
    (hγ0 : ∀ n, windAt y₀ 0 (mem_insert 0 _) (γ n) = 0) :
    IsEmpty ((y₂Fiber0 y₀ fun n => FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (γ n))) ≃ₜ
      cantorSet) := by
  refine ⟨fun e => absGal_Y₂_fiber_not_compact y₀ γ hγ hγ0 ?_⟩
  haveI : CompactSpace cantorSet := isCompact_iff_compactSpace.1 isCompact_cantorSet
  haveI := e.symm.compactSpace
  exact isCompact_iff_compactSpace.2 this

end AbsGal

/-! ### `ex:wild_cantor_general_antoine` -/

section WildCantor

/-- The `3`-sphere `S³ ⊆ ℝ⁴`. -/
abbrev Sphere3 : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

/-- A great circle of `S³`. -/
def greatCircle3 : Set Sphere3 := {x | (x : EuclideanSpace ℝ (Fin 4)) 2 = 0 ∧
  (x : EuclideanSpace ℝ (Fin 4)) 3 = 0}

/-- `C` is a Cantor set: homeomorphic to the middle-third Cantor set. -/
def IsCantorSubset {Z : Type*} [TopologicalSpace Z] (C : Set Z) : Prop := Nonempty (C ≃ₜ cantorSet)

/-- A *wild* Cantor set of `S³`: a Cantor set no homeomorphism of `S³` carries into a great circle
(a Cantor set is tame when it lies on a tame arc; SCOPE (e)). -/
def IsWildCantor (C : Set Sphere3) : Prop :=
  IsCantorSubset C ∧ ¬ ∃ h : Sphere3 ≃ₜ Sphere3, h '' C ⊆ greatCircle3

/-- The criterion `GX.not_isSLSCAt_of_essential`, globally. -/
theorem not_isSLSCIn_of_essential {X : Type*} [TopologicalSpace X] {U : Set X} (x : X)
    (h : ∀ V ∈ 𝓝 x, ∃ (K : Set X) (γ : Path x x), x ∉ K ∧ U ⊆ Kᶜ ∧ MemOmega (V ∩ U) γ ∧
      ¬ HomotopicIn Kᶜ γ (Path.refl x) ∧
      ∃ W ∈ 𝓝 x, ∀ δ : Path x x, (∀ t, δ t ∈ W) → HomotopicIn Kᶜ δ (Path.refl x)) :
    ¬ IsSLSCIn U := fun hU => not_isSLSCAt_of_essential h (hU.2 x)

/-- `C` *does not separate `X` locally*: every neighbourhood `W` of a point `x ∈ C` contains a
neighbourhood `W'` of `x` any two points of which off `C` are joined by a path in `W ∖ C`. (A
closed `0`-dimensional subset of a manifold of dimension `≥ 2` has this property; not formalized,
SCOPE (e).) -/
def IsLocallyNonseparating {X : Type*} [TopologicalSpace X] (C : Set X) : Prop :=
  ∀ x ∈ C, ∀ W ∈ 𝓝 x, ∃ W' ∈ 𝓝 x, ∀ a ∈ W' ∩ Cᶜ, ∀ b ∈ W' ∩ Cᶜ,
    ∃ ω : Path a b, ∀ t, ω t ∈ W ∩ Cᶜ

/-- In a simply connected subspace `U`, two paths with the same ends are homotopic in `U`. -/
theorem homotopicIn_of_simplyConnected {X : Type*} [TopologicalSpace X] {U : Set X}
    [SimplyConnectedSpace U] {a b : X} (γ₁ γ₂ : Path a b) (h₁ : ∀ t, γ₁ t ∈ U)
    (h₂ : ∀ t, γ₂ t ∈ U) : HomotopicIn U γ₁ γ₂ :=
  homotopicIn_iff.2 ⟨h₁, h₂, SimplyConnectedSpace.paths_homotopic _ _⟩

/-- **The positive half of `ex:wild_cantor_general_antoine`'s correction.** In a preconnected
space, if `C` has dense, simply connected complement and does not separate locally, then `X ∖ C`
is semi-locally simply connected in `X`: cut short end arcs off a loop of `Ω(x,x,X ∖ C)`, join
their ends inside a small neighbourhood off `C`, and use simple connectivity on the middle. -/
theorem isSLSCIn_compl_of_simplyConnected {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {C : Set X} (hd : Dense Cᶜ) [SimplyConnectedSpace (Cᶜ : Set X)]
    (hC : IsLocallyNonseparating C) : IsSLSCIn Cᶜ := by
  refine ⟨hd, fun x => ⟨univ, isOpen_univ, isPreconnected_univ, mem_univ x, fun γ hγ => ?_⟩⟩
  have hγU : MemOmega Cᶜ γ := fun t h0 h1 => (hγ t h0 h1).2
  refine ⟨hγU, fun W hW => ?_⟩
  by_cases hx : x ∈ C
  · obtain ⟨W', hW', hpath⟩ := hC x hx W hW
    obtain ⟨t₀, h00, h0c, hhead⟩ := exists_head_mem γ (inter_mem hW' hW) (c := 1 / 2)
      (by norm_num)
    obtain ⟨t₁, h1c, h11, htail⟩ := exists_tail_mem γ (inter_mem hW' hW) (c := 1 / 2)
      (by norm_num)
    have h01 : (t₀ : ℝ) < t₁ := by linarith
    have ha : γ t₀ ∈ W' ∩ Cᶜ := ⟨(hhead t₀ le_rfl).1, hγU t₀ h00 (by linarith)⟩
    have hb : γ t₁ ∈ W' ∩ Cᶜ := ⟨(htail t₁ le_rfl).1, hγU t₁ (by linarith) h11⟩
    obtain ⟨ω, hω⟩ := hpath _ ha _ hb
    have hsub : ∀ t, subpath γ t₀ t₁ t ∈ Cᶜ := fun t => by
      obtain ⟨s, hs1, hs2, hs⟩ := subpath_mem γ t₀ t₁ t
      rw [min_eq_left h01.le] at hs1
      rw [max_eq_right h01.le] at hs2
      rw [hs]
      exact hγU s (by linarith) (by linarith)
    refine ⟨splice γ t₀ t₁ h01 ω, fun t ht0 ht1 => ?_, splice_omegaHomotopic hγU h01 h11
      (homotopicIn_of_simplyConnected _ _ hsub fun t => (hω t).2)⟩
    rcases splice_mem γ h01 ω t with ⟨hle, he⟩ | ⟨hge, he⟩ | ⟨s, hs⟩
    · rw [he]; exact ⟨(hhead t hle).2, hγU t ht0 ht1⟩
    · rw [he]; exact ⟨(htail t hge).2, hγU t ht0 ht1⟩
    · rw [← hs]; exact hω s
  · have hall : ∀ t, γ t ∈ Cᶜ := fun t => by
      rcases eq_or_lt_of_le t.2.1 with h0 | h0
      · rw [show t = 0 from Subtype.ext h0.symm, γ.source]; exact hx
      rcases eq_or_lt_of_le t.2.2 with h1 | h1
      · rw [show t = 1 from Subtype.ext h1, γ.target]; exact hx
      exact hγU t h0 h1
    exact ⟨Path.refl x, fun _ _ _ => ⟨mem_of_mem_nhds hW, hx⟩,
      (homotopicIn_of_simplyConnected γ (Path.refl x) hall fun _ => hx).omegaHomotopic⟩

/-- `S³` is preconnected. -/
theorem preconnectedSpace_sphere3 : PreconnectedSpace Sphere3 := by
  refine Subtype.preconnectedSpace (isPreconnected_sphere ?_ _ _)
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
  norm_num

/-- `ex:wild_cantor_general_antoine` (`RamcovGX.tex:1578`), the positive half: if a subset `C` of
`S³` (wild or not) has dense simply connected complement and does not separate `S³` locally,
then `S³ ∖ C` IS semi-locally simply connected in `S³`. -/
theorem sphere3_isSLSCIn_compl_of_simplyConnected {C : Set Sphere3} (hd : Dense Cᶜ)
    [SimplyConnectedSpace (Cᶜ : Set Sphere3)] (hC : IsLocallyNonseparating C) : IsSLSCIn Cᶜ :=
  haveI := preconnectedSpace_sphere3
  isSLSCIn_compl_of_simplyConnected hd hC

/-- In `S³`, every point `x` off a closed `K` has a neighbourhood (a small spherical cap) all of
whose loops at `x` are null-homotopic in `Kᶜ`: contract them radially onto `x`. -/
theorem sphere3_exists_nhds_loops_trivial {K : Set Sphere3} (hK : IsClosed K) {x : Sphere3}
    (hx : x ∉ K) :
    ∃ W ∈ 𝓝 x, ∀ δ : Path x x, (∀ t, δ t ∈ W) → HomotopicIn Kᶜ δ (Path.refl x) := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hK.isOpen_compl.mem_nhds hx)
  set x₀ : EuclideanSpace ℝ (Fin 4) := (x : EuclideanSpace ℝ (Fin 4)) with hx₀def
  have hx₀ : ‖x₀‖ = 1 := mem_sphere_zero_iff_norm.1 x.2
  have hx₀x₀ : inner ℝ x₀ x₀ = 1 := by rw [real_inner_self_eq_norm_sq, hx₀]; norm_num
  set c : ℝ := max (1 / 2) (1 - ε ^ 2 / 4) with hcdef
  have hc1 : c < 1 := max_lt (by norm_num) (by nlinarith)
  have hc0 : 1 / 2 ≤ c := le_max_left _ _
  have hcε : 2 - 2 * c < ε ^ 2 := by
    have := le_max_right (1 / 2 : ℝ) (1 - ε ^ 2 / 4); nlinarith
  set v : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4) :=
    fun w => w + (max 0 (1 / 2 - inner ℝ w x₀)) • x₀ with hvdef
  have hvin : ∀ w, inner ℝ (v w) x₀ = inner ℝ w x₀ + max 0 (1 / 2 - inner ℝ w x₀) := by
    intro w
    simp only [hvdef, inner_add_left, real_inner_smul_left, hx₀x₀, mul_one]
  have hv : ∀ w, 1 / 2 ≤ inner ℝ (v w) x₀ := fun w => by
    rw [hvin]; linarith [le_max_right 0 (1 / 2 - inner ℝ w x₀)]
  have hvne : ∀ w, v w ≠ 0 := fun w h => by
    have := hv w; rw [h, inner_zero_left] at this; norm_num at this
  have hvc : Continuous v := continuous_id.add
    ((continuous_const.max (continuous_const.sub (continuous_id.inner continuous_const))).smul
      continuous_const)
  have hnorm : ∀ w, ‖‖v w‖⁻¹ • v w‖ = 1 := fun w => by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 (hvne w))]
  let F : EuclideanSpace ℝ (Fin 4) → Sphere3 := fun w =>
    ⟨‖v w‖⁻¹ • v w, mem_sphere_zero_iff_norm.2 (hnorm w)⟩
  have hF : Continuous F := Continuous.subtype_mk
    (((continuous_norm.comp hvc).inv₀ fun w => norm_ne_zero_iff.2 (hvne w)).smul hvc) _
  -- `F` fixes the points of the sphere near `x₀`
  have hvfix : ∀ w, 1 / 2 ≤ inner ℝ w x₀ → v w = w := fun w hw => by
    simp only [hvdef, max_eq_left (by linarith : 1 / 2 - inner ℝ w x₀ ≤ 0), zero_smul,
      add_zero]
  have hFfix : ∀ y : Sphere3, 1 / 2 ≤ inner ℝ (y : EuclideanSpace ℝ (Fin 4)) x₀ →
      F y = y := fun y hy => by
    apply Subtype.ext
    change ‖v y‖⁻¹ • v y = (y : EuclideanSpace ℝ (Fin 4))
    rw [hvfix _ hy, mem_sphere_zero_iff_norm.1 y.2, inv_one, one_smul]
  have hFx : F x₀ = x := hFfix x (by rw [hx₀x₀]; norm_num)
  set A : Set (EuclideanSpace ℝ (Fin 4)) := {w | ‖w‖ ≤ 1 ∧ c ≤ inner ℝ w x₀} with hAdef
  have hA : Convex ℝ A := by
    have h1 : Convex ℝ {w : EuclideanSpace ℝ (Fin 4) | ‖w‖ ≤ 1} := by
      simpa [Metric.closedBall, dist_zero_right] using convex_closedBall (0 :
        EuclideanSpace ℝ (Fin 4)) 1
    have h2 : Convex ℝ {w : EuclideanSpace ℝ (Fin 4) | c ≤ inner ℝ w x₀} :=
      convex_halfSpace_ge
        ⟨fun a b => inner_add_left a b x₀, fun r a => real_inner_smul_left a x₀ r⟩ c
    exact h1.inter h2
  have hFA : ∀ e ∈ A, F e ∈ Kᶜ := fun e he => by
    apply hball
    have hce : 1 / 2 ≤ inner ℝ e x₀ := le_trans hc0 he.2
    have hene : e ≠ 0 := fun h => by rw [h, inner_zero_left] at hce; norm_num at hce
    have hnpos : 0 < ‖e‖ := norm_pos_iff.2 hene
    have hFe : (F e : EuclideanSpace ℝ (Fin 4)) = ‖e‖⁻¹ • e := by
      change ‖v e‖⁻¹ • v e = _; rw [hvfix e hce]
    have hin : c ≤ inner ℝ (F e : EuclideanSpace ℝ (Fin 4)) x₀ := by
      rw [hFe, real_inner_smul_left]
      have : inner ℝ e x₀ ≤ ‖e‖⁻¹ * inner ℝ e x₀ := by
        have h1 : 1 ≤ ‖e‖⁻¹ := (one_le_inv₀ hnpos).2 he.1
        nlinarith
      linarith [he.2]
    rw [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm]
    have hsq : ‖(F e : EuclideanSpace ℝ (Fin 4)) - x₀‖ ^ 2 < ε ^ 2 := by
      rw [norm_sub_sq_real, mem_sphere_zero_iff_norm.1 (F e).2, hx₀]; nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 hε.le hsq
  refine ⟨{y | c < inner ℝ (y : EuclideanSpace ℝ (Fin 4)) x₀}, ?_, fun δ hδ => ?_⟩
  · exact (isOpen_lt continuous_const (continuous_subtype_val.inner continuous_const)).mem_nhds
      (by simp only [mem_setOf_eq]; rw [← hx₀def, hx₀x₀]; exact hc1)
  · have hmemA : ∀ y : Sphere3, c < inner ℝ (y : EuclideanSpace ℝ (Fin 4)) x₀ →
        (y : EuclideanSpace ℝ (Fin 4)) ∈ A := fun y hy =>
      ⟨(mem_sphere_zero_iff_norm.1 y.2).le, hy.le⟩
    have key := homotopicIn_map_of_convex (U := Kᶜ) (δ.map continuous_subtype_val)
      (Path.refl x₀) hA (fun t => hmemA _ (hδ t)) (fun _ => ⟨hx₀.le, by rw [Path.refl_apply, hx₀x₀]; exact hc1.le⟩)
      hF hFA
    refine (key.cast hFx.symm hFx.symm).of_eq ?_ ?_
    · refine Path.ext (funext fun t => ?_)
      simp only [Path.cast_coe, Path.map_coe, Function.comp_apply]
      exact hFfix _ (le_trans hc0 (hδ t).le)
    · refine Path.ext (funext fun t => ?_)
      simp only [Path.cast_coe, Path.map_coe, Function.comp_apply, Path.refl_apply]
      exact hFx

/-- A vector of `ℝ⁴` orthogonal to `w` and of the same norm: `(-w₁, w₀, -w₃, w₂)`. -/
noncomputable def sphere3Perp (w : EuclideanSpace ℝ (Fin 4)) : EuclideanSpace ℝ (Fin 4) :=
  !₂[-w 1, w 0, -w 3, w 2]

theorem inner_sphere3Perp_self (w : EuclideanSpace ℝ (Fin 4)) :
    inner ℝ w (sphere3Perp w) = 0 := by
  simp [sphere3Perp, PiLp.inner_apply, Fin.sum_univ_four]; ring

theorem inner_sphere3Perp_sphere3Perp (w : EuclideanSpace ℝ (Fin 4)) :
    inner ℝ (sphere3Perp w) (sphere3Perp w) = inner ℝ w w := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp [sphere3Perp, Fin.sum_univ_four]; ring

/-- A Cantor set of `S³` has dense complement: it is totally disconnected, while every open
subset of `S³` contains a non-degenerate arc of a great circle. -/
theorem dense_compl_of_isCantorSubset {C : Set Sphere3} (hC : IsCantorSubset C) : Dense Cᶜ := by
  obtain ⟨e⟩ := hC
  haveI : TotallyDisconnectedSpace C := (e.trans cantorSetHomeomorphNatToBool).symm.totallyDisconnectedSpace
  have htd : IsTotallyDisconnected C := totallyDisconnectedSpace_subtype_iff.1 this
  rw [← interior_eq_empty_iff_dense_compl, eq_empty_iff_forall_notMem]
  intro x hx
  set x₀ : EuclideanSpace ℝ (Fin 4) := (x : EuclideanSpace ℝ (Fin 4)) with hx₀def
  have hx₀x₀ : inner ℝ x₀ x₀ = 1 := by
    rw [real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.1 x.2]; norm_num
  set u := sphere3Perp x₀
  have hxu : inner ℝ x₀ u = 0 := inner_sphere3Perp_self x₀
  have huu : inner ℝ u u = 1 := by rw [inner_sphere3Perp_sphere3Perp, hx₀x₀]
  set f : ℝ → EuclideanSpace ℝ (Fin 4) := fun θ => Real.cos θ • x₀ + Real.sin θ • u with hfdef
  have hfu : ∀ θ, inner ℝ (f θ) u = Real.sin θ := fun θ => by
    simp only [hfdef, inner_add_left, real_inner_smul_left, hxu, huu]; ring
  have hff : ∀ θ, inner ℝ (f θ) (f θ) = 1 := fun θ => by
    simp only [hfdef, inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, hxu, huu, hx₀x₀, real_inner_comm x₀ u]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hfn : ∀ θ, ‖f θ‖ = 1 := fun θ => by
    have h := hff θ
    rw [real_inner_self_eq_norm_sq] at h
    have h0 := norm_nonneg (f θ)
    nlinarith
  let g : ℝ → Sphere3 := fun θ => ⟨f θ, mem_sphere_zero_iff_norm.2 (hfn θ)⟩
  have hg : Continuous g := Continuous.subtype_mk
    ((Real.continuous_cos.smul continuous_const).add (Real.continuous_sin.smul continuous_const)) _
  have hg0 : g 0 = x := Subtype.ext (by
    change Real.cos 0 • x₀ + Real.sin 0 • u = x₀
    simp)
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.1
    (hg.continuousAt.preimage_mem_nhds (hg0 ▸ isOpen_interior.mem_nhds hx :
      interior C ∈ 𝓝 (g 0)))
  set s : ℝ := min (r / 2) 1 with hsdef
  have hs0 : 0 < s := lt_min (by linarith) one_pos
  have hsr : s < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hsub : g '' Icc 0 s ⊆ C := by
    rintro _ ⟨θ, hθ, rfl⟩
    refine interior_subset (hrsub ?_)
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    constructor <;> linarith [hθ.1, hθ.2]
  have hss := htd _ hsub (isPreconnected_Icc.image _ hg.continuousOn)
  have heq : g s = g 0 := hss ⟨s, ⟨hs0.le, le_rfl⟩, rfl⟩ ⟨0, ⟨le_rfl, hs0.le⟩, rfl⟩
  have h1 : inner ℝ (f s) u = inner ℝ (f 0) u := by
    have := congrArg (fun y : Sphere3 => inner ℝ (y : EuclideanSpace ℝ (Fin 4)) u) heq
    exact this
  rw [hfu, hfu, Real.sin_zero] at h1
  have : 0 < Real.sin s := Real.sin_pos_of_pos_of_lt_pi hs0
    (lt_of_le_of_lt (min_le_right _ _) (by linarith [Real.pi_gt_three]))
  linarith

/-- `ex:wild_cantor_general_antoine` (`RamcovGX.tex:1578`) is FALSE for wild Cantor sets in
general (finding, DEC-27): as soon as one wild Cantor set of `S³` has simply connected, locally
non-separating complement, the paper's claim fails (the density of the complement is automatic,
`GX.dense_compl_of_isCantorSubset`). -/
theorem wild_cantor_claim_false_of_exists
    (h : ∃ C : Set Sphere3, IsWildCantor C ∧ SimplyConnectedSpace (Cᶜ : Set Sphere3) ∧
      IsLocallyNonseparating C) :
    ¬ ∀ C : Set Sphere3, IsWildCantor C → ¬ IsSLSCIn Cᶜ := by
  obtain ⟨C, hw, hsc, hC⟩ := h
  exact fun hall => hall C hw
    (sphere3_isSLSCIn_compl_of_simplyConnected (dense_compl_of_isCantorSubset hw.1) hC)

/-- **Cited, not built** (the literature behind the finding on `RamcovGX.tex:1578`): a wild
Cantor set of `S³` with simply connected complement (Kirkor, Fund. Math. 45, 1958; Skora,
Topology Appl. 24, 1986; Garity–Repovš–Željko, PAMS 134, 2006, rigid examples), together with
the local non-separation every closed `0`-dimensional subset of a `3`-manifold enjoys. -/
theorem kirkor_wild_cantor_exists : ∃ C : Set Sphere3, IsWildCantor C ∧
    SimplyConnectedSpace (Cᶜ : Set Sphere3) ∧ IsLocallyNonseparating C := by
  sorry -- SORRY(ex:wild_cantor_general_antoine): existence of a wild Cantor set in S³ with simply connected complement (Kirkor 1958, Skora 1986: an explicit nested-tori/ball construction plus a van Kampen limit argument showing π₁(S³ ∖ C) = 1, and its wildness via a non-1-ULC point, Bing's tameness criterion); and IsLocallyNonseparating C, i.e. a closed 0-dimensional set does not separate a small ball of S³ (dimension theory / Alexander duality). None of this geometric topology is in mathlib.

/-- `ex:wild_cantor_general_antoine` (`RamcovGX.tex:1578`) as written is FALSE (finding,
DEC-27): not every wild Cantor set of `S³` has a complement which fails to be semi-locally simply
connected in `S³`. Rests on the cited existence `GX.kirkor_wild_cantor_exists`. -/
theorem wild_cantor_claim_false : ¬ ∀ C : Set Sphere3, IsWildCantor C → ¬ IsSLSCIn Cᶜ :=
  wild_cantor_claim_false_of_exists kirkor_wild_cantor_exists

/-- The essential-loop criterion `GX.not_isSLSCIn_of_essential`, for a complement `Cᶜ`: if some
point `x` has, in each of its neighbourhoods, a loop at `x` off `C` (interior points) which is
essential in the complement of a piece `K ⊆ C` with `x ∉ K`, small loops at `x` being trivial
there, then `Cᶜ` is NOT semi-locally simply connected. No Cantor or wildness hypothesis is used;
this is the property Antoine's theorem gives for the necklaces (`GX.antoine_necklace_essential`). -/
theorem wild_cantor_not_isSLSCIn {C : Set Sphere3} (x : Sphere3)
    (h : ∀ V ∈ 𝓝 x, ∃ (K : Set Sphere3) (γ : Path x x), x ∉ K ∧ K ⊆ C ∧ MemOmega (V ∩ Cᶜ) γ ∧
      ¬ HomotopicIn Kᶜ γ (Path.refl x) ∧
      ∃ W ∈ 𝓝 x, ∀ δ : Path x x, (∀ t, δ t ∈ W) → HomotopicIn Kᶜ δ (Path.refl x)) :
    ¬ IsSLSCIn Cᶜ := by
  refine not_isSLSCIn_of_essential x fun V hV => ?_
  obtain ⟨K, γ, hxK, hKC, hγ, hne, W, hW, hWt⟩ := h V hV
  exact ⟨K, γ, hxK, compl_subset_compl.2 hKC, hγ, hne, W, hW, hWt⟩

/-- In `S³` the small-loop condition of `GX.wild_cantor_not_isSLSCIn` is automatic for a CLOSED
piece `K` (`GX.sphere3_exists_nhds_loops_trivial`): an essential loop at `x ∈ C` off `C`, in every
neighbourhood of `x`, essential in the complement of a closed `K ⊆ C` missing `x`, suffices. -/
theorem sphere3_not_isSLSCIn_of_essential {C : Set Sphere3} (x : Sphere3)
    (h : ∀ V ∈ 𝓝 x, ∃ K : Set Sphere3, K ⊆ C ∧ IsClosed K ∧ x ∉ K ∧ ∃ γ : Path x x,
      MemOmega (V ∩ Cᶜ) γ ∧ ¬ HomotopicIn Kᶜ γ (Path.refl x)) : ¬ IsSLSCIn Cᶜ := by
  refine wild_cantor_not_isSLSCIn x fun V hV => ?_
  obtain ⟨K, hKC, hK, hxK, γ, hγ, hne⟩ := h V hV
  obtain ⟨W, hW, hWt⟩ := sphere3_exists_nhds_loops_trivial hK hxK
  exact ⟨K, γ, hxK, hKC, hγ, hne, W, hW, hWt⟩

/-- **Antoine's theorem** (cited `general_antoine`, not built), in the form the corrected
`RamcovGX.tex:1578` uses: Antoine's necklace `C ⊆ S³` (equally Blankinship's) is a wild Cantor
set, and at every point `x ∈ C`, inside any neighbourhood `V` of `x`, there are a sub-necklace
`K = C ∩ L` (`L` a link of the construction inside `V` not containing `x`, closed, `x ∉ K`) and a
loop at `x` off `C` (a path from `x` to a meridian of `L`, the meridian, the path back) which is
essential in `S³ ∖ K`. -/
theorem antoine_necklace_essential : ∃ C : Set Sphere3, IsWildCantor C ∧ ∀ x ∈ C,
    ∀ V ∈ 𝓝 x, ∃ K : Set Sphere3, K ⊆ C ∧ IsClosed K ∧ x ∉ K ∧ ∃ γ : Path x x,
      MemOmega (V ∩ Cᶜ) γ ∧ ¬ HomotopicIn Kᶜ γ (Path.refl x) := by
  sorry -- SORRY(ex:wild_cantor_general_antoine): Antoine's necklace is not constructed: it needs (1) the construction in S³ of nested chains of linked solid tori with diameters → 0 and the proof that their intersection is homeomorphic to cantorSet; (2) Antoine's π₁ computation, that a meridian of a link L is essential in S³ ∖ (C ∩ L) (no meridian disc of L misses C ∩ L, via the linking of the chain and a van Kampen / Seifert–van Kampen limit argument; mathlib has no π₁ of knot or link complements, no van Kampen); (3) the accessibility of each x ∈ C from S³ ∖ C by an arc meeting C only at x; and (4) wildness, i.e. that a Cantor set lying in a great circle up to homeomorphism has simply connected complement while (2) gives a non-trivial one.

/-- `ex:wild_cantor_general_antoine` (`RamcovGX.tex:1578`), corrected (DEC-27) for the cited
class: there is a wild Cantor set of `S³` — Antoine's necklace — whose complement is NOT
semi-locally simply connected in `S³`. Proved from the essential-loop criterion; the cited
Antoine content is the tagged `sorry` of `GX.antoine_necklace_essential`. -/
theorem exists_wild_cantor_not_isSLSCIn : ∃ C : Set Sphere3, IsWildCantor C ∧ ¬ IsSLSCIn Cᶜ := by
  obtain ⟨C, hw, h⟩ := antoine_necklace_essential
  obtain ⟨e⟩ := hw.1
  let x : Sphere3 := (e.symm ⟨0, zero_mem_cantorSet⟩ : C)
  exact ⟨C, hw, sphere3_not_isSLSCIn_of_essential x (h x (e.symm ⟨0, zero_mem_cantorSet⟩).2)⟩

end WildCantor

end GX
