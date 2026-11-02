import GX.Branched.Galois
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# The examples closing §3.4 (l.1560–1583)

Packages WP-26h, WP-27f. `papers/gx`, `RamcovGX.tex:1560–1583`. Reworked to DEC-55 (literal
compact-open reading of "almost trivial"), DEC-58 (`ex:wild_cantor_general_antoine` is about
Antoine's necklace; in `ex:consider_denote_absolute_galois`, `Γ₂` is the normal closure of the
`[γₙ]²`).

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
  `GX.isSLSCIn_compl_of_local_models`. All positive, so they hold in the literal reading
  (`GX.IsSLSCIn.isSLSCInCC`).
* `ex:consider_denote_absolute_galois` — `RamcovGX.tex:1570` (partial: the fibre claim is FALSE,
  SCOPE (d)): first claim, `ℂ ∖ S` is NOT semi-locally simply connected in `ℂ`, in the literal
  reading `GX.absGal_not_isSLSCInCC` (and the homotopy one `GX.absGal_not_isSLSCIn`, at `0`
  `GX.absGal_not_isSLSCAt`, criterion `GX.not_isSLSCAt_of_essential`); the printed
  `Γ₂ = ⟨Γ[γₙ]²Γ⟩` is all of `Γ`, `GX.printedGamma2_eq_top`; for the ruled `Γ₂` (DEC-58, the
  normal closure `GX.gamma2`) the fibre of `Y₂` over `0` is NOT compact, hence not a Cantor set,
  for the paper's simple loops; the strongest true form proved (DEC-27) is that it is infinite and
  totally disconnected but not compact, `GX.absGal_Y₂_fiber_corrected_simple` (general form
  `GX.absGal_Y₂_fiber_corrected`; total disconnectedness for any `Γ₂`,
  `GX.absGal_Y₂_fiber_totallyDisconnected`, through the spread `GX.absGal_isSpread_ordY₂Proj` and
  the quotient lemma `GX.isSpread_homeoQuotient_lift`) — refuted unconditionally
  `GX.absGal_Y₂_fiber_not_cantor_simple` (explicit
  loops `GX.absGalSimpleLoop`, windings `GX.absGal_windAt_simpleLoop`), and for any loops with
  the simple-loop windings drawn in `GX.absGalR` (`GX.absGal_Y₂_fiber_not_compact_of_simple`,
  `GX.absGal_Y₂_fiber_not_cantor`; the general form `GX.absGal_Y₂_fiber_not_compact`). The proof
  is a dihedral invariant of `\widetilde{ℂ∖S}`: continuous logarithms `GX.absGalℓ` of
  `F = (z-1)/(z-1/2)` and `GX.absGalΛ` of `G ∘ √F`, `G(s) = (s-1)/(s+1)`, on which deck
  transformations act by `(±1, ±Λ + c)` (`GX.absGal_deck_action`); `Γ₂` acts trivially
  (`GX.absGal_gamma2_le`), the loop `GX.absGalωPath` around `{1, 1/2}` translates
  (`GX.absGal_exists_translation`), so the integer `GX.absGalΘ` separates infinitely many
  components of the preimage of `D₅` (`GX.absGalΘbar_eq_of_mem`), each reached by an end over
  `0` (`GX.absGalEnd`).
* `ex:wild_cantor_general_antoine` — `RamcovGX.tex:1578` (stated, SCOPE (e)), read by DEC-58 as
  a claim about Antoine's necklace, which is BUILT: `GX.antoineNecklace ⊆ S³` (the inverse
  stereographic image of `GX.antoineNecklaceR3 = ⋂ₙ GX.antoineStage n`, a chain of `64`
  interlocking square solid rings `GX.antoineLink` repeated by the similarities `GX.antoineMap`),
  proved a Cantor set (`GX.antoineNecklace_isCantorSubset`). The claim for it,
  `GX.antoineNecklace_wild_not_isSLSCInCC` (literal reading; the two readings agree for closed
  `C ⊆ S³`, `GX.sphere3_isSLSCInCC_compl_iff`) and `GX.antoineNecklace_not_isSLSCIn`, is proved
  from the essential-loop criterion (`GX.wild_cantor_not_isSLSCIn`,
  `GX.sphere3_not_isSLSCIn_of_essential`, the small-loop condition automatic in `S³`,
  `GX.sphere3_exists_nhds_loops_trivial`) and Antoine's theorem for this necklace,
  `GX.antoineNecklace_antoine` (cited: wildness and the essential loops, tagged `sorry`, the only
  `sorry` of the file). Side
  remark (not the ruled reading): for arbitrary wild Cantor sets the claim would fail as soon as
  one has simply connected, locally non-separating complement,
  `GX.wild_cantor_claim_false_of_exists`, `GX.isSLSCIn_compl_of_simplyConnected`,
  `GX.dense_compl_of_isCantorSubset`.

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
| ex. 1570: `Γ₂ = ⟨Γ[γₙ]²Γ⟩` | ⚠ read (DEC-58): the normal closure of the `[γₙ]²` (the printed one is `Γ`) |
| ex. 1570: "the fibre is a Cantor set" | ✗ false (DEC-27): not compact; ⚠ corrected: infinite, totally disconnected, not compact (`GX.absGal_Y₂_fiber_corrected_simple`); perfectness not formalized |
| ex. 1570: `γₙ` a simple loop around `(1/n,0)` | ⚠ read: `GX.absGalSimpleLoop` (stem, circle, stem back: homotopic to a based simple loop, not formalized); the general theorem takes any loops with the windings of simple loops, those around `1/(n+1)`, `n ≥ 2`, drawn in `GX.absGalR` (SCOPE (d)) |
| ex. 1578: `S` a wild Cantor set in `S³` | ⚠ read (DEC-58): Antoine's necklace, built explicitly (`GX.antoineNecklace`) and proved a Cantor set; the claim is stated for THIS necklace (not for every wild Cantor set, nor merely for some); its wildness and essential loops are the cited Antoine theorem, a tagged `sorry` (SCOPE (e)) |
| "almost trivial" | ✓ literal compact-open reading (DEC-55) for both negative claims (`IsSLSCInCC`); positive results a fortiori |

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
Example 1570: `ℝ²` is `ℂ`, `S` is `GX.fibS`. The first claim is proved in the literal reading
(DEC-55): `ℂ ∖ S` is open and semilocally simply connected, so `GX.isSLSCInCC_iff` reduces it to
the homotopy form, proved by the winding number. The printed `Γ₂ = ⟨Γ[γₙ]²Γ⟩` is `Γ` itself
(any `g = (g γₙ⁻²) γₙ² 1`); DEC-58 reads it as the normal closure `⟨⟨[γₙ]²⟩⟩`. `Y₂` is built
literally: `ord(\widetilde Y^S)` is `\widetilde{Y∖S}` (`GX.UniversalCover`), `Γ` acts through
`π₁(Y ∖ S)` (`GX.AbsGamma`), `GX.AbsGalY₂` is the Fox completion (`GX.SpreadEnd`) of
`Γ₂ \ \widetilde{Y∖S} → Y`. The paper's claim that the fibre above `0` is a Cantor set is FALSE
(finding, DEC-27): the fibre is not compact. The simple loops are `GX.absGalSimpleLoop n` based at
`y₀ = -i/4`: a segment to `pₙ - iρₙ` (`pₙ = 1/(n+1)`, `ρₙ = 1/(2(n+1)(n+2))`), the circle of
radius `ρₙ` around `pₙ` counterclockwise, the segment back; they wind once around `pₙ` and not
around the other points of `S` (`GX.absGal_windAt_simpleLoop`). They are not injective (the stem
is run twice); a based simple closed curve around `pₙ` is homotopic to them (Schoenflies), so
`Γ₂` is the same, but this identification is not formalized. The general theorem
`GX.absGal_Y₂_fiber_not_compact` uses only that `γ₀`, `γ₁` wind an odd number of times around
`{1, 1/2}` and that the other `γₙ` lie in `GX.absGalR` (which contains the half-plane
`Re z < 1/2`, `GX.absGal_mem_R_of_re`). Mechanism: on `\widetilde{ℂ∖S}`, `sq = exp(ℓ/2)` is a
square root of `F = (z-1)/(z-1/2)` and `Λ` a logarithm of `G(sq)`, `G(s) = (s-1)/(s+1)`; deck
transformations act by `sq ↦ ±sq`, `Λ ↦ ±Λ + c` (an infinite-dihedral action); the squares of the
loops around `1` and `1/2` and the loops in `absGalR` act trivially, so `Γ₂` does, while the loop
`ω = 1/2 - (1-u)²/(8u)`, `u = e^{2iπt}/20`, around `1` and `1/2` translates `Λ` by `±2πi`. Over
`D₅` (radius `2/11`) the integer `Θ = (Λ - (sq/√F)·log G(√F))/(2πi)` is locally constant, hence
constant on the components of the preimage of `D₅` in `Γ₂ \ \widetilde{ℂ∖S}`, and takes the
infinitely many values `Θ₀ + k(±1)` on the points `ψᵏ(w₅)`; ends over `0` through each of these
components (threads along the imaginary axis, `GX.FiberThread.toEnd`) and the open cover of the
fibre by the basic sets over `D₅` give the non-compactness. The strongest true form proved: the
fibre is infinite (the ends `GX.absGalEnd k` are pairwise distinct, `GX.absGalEnd_injective`) and
totally disconnected (`cor:totdiscont`, `GX.isTotallyDisconnected_fiber`, once
`Γ₂ \ \widetilde{ℂ∖S} → ℂ` is known to be a spread, `GX.isSpread_homeoQuotient_lift`), but not
compact; whether it is perfect (no isolated point) is not formalized. A Cantor fibre would be obtained for
the kernel of the mod-2 winding numbers around the `1/n` (an abelian quotient); not formalized.
"Answers positively Problem 10.7 of MR2198590" is bibliographic and not formalized. (e)
Example 1578, read by DEC-58: `S` is Antoine's necklace, and it is built. In `ℝ³` (sup
distance) the link `L = {3/4 ≤ max(|x|,|y|) ≤ 1, |z| ≤ 1/8}` is a square solid torus; the `64`
similarities `GX.antoineMap i` of ratio `7/80` place copies of `L` along its core square
`max(|x|,|y|) = 7/8`, `7/64` apart, alternately in the plane `z = 0` and in the vertical plane
containing the side, so that consecutive copies interlock (each passes through the hole of the
next) and the chain closes up around the hole of `L` (`GX.antoine_adj_succ`). Proved: the copies
lie in `L` (`GX.antoineMap_mem`) and are pairwise disjoint (`GX.antoineMap_disjoint`: all
`64 × 64` pairs are box-separated except the consecutive ones, `GX.antoine_sep_or_adj` by
`decide`, which miss each other by `GX.antoine_link_aux`); hence the pieces of generation `n`
are nested and disjoint, the coding map `GX.antoineCode` is a homeomorphism
`Fin 64 ^ ℕ ≃ₜ GX.antoineNecklaceR3` (`GX.antoineCodeHomeomorph`), and the necklace is a Cantor
set (`GX.antoineNecklaceR3_isCantorSubset`, `64 = 2⁶`), carried into `S³` by the inverse
stereographic projection `GX.antoineStereo` (`GX.antoineNecklace_isCantorSubset`). That the
consecutive links are LINKED (rather than merely non-separated by boxes) is read off the
coordinates and used only inside the citation. The statement is made for this necklace; the
existential forms `GX.exists_wild_cantor_not_isSLSCIn(CC)` are corollaries. A Cantor set of `S³` is tame if a
homeomorphism of `S³` carries it into a great circle, wild otherwise (`GX.IsWildCantor`). The
claim `GX.antoineNecklace_wild_not_isSLSCInCC` (literal reading; for closed `C ⊆ S³` the two
readings agree, `GX.sphere3_isSLSCInCC_compl_iff`, `S³` being locally path-connected and the
complement semilocally simply connected, `GX.sphere3_semilocallySimplyConnected_compl`) is
proved from the criterion `GX.wild_cantor_not_isSLSCIn` (some point of `C` has, in each
neighbourhood, a loop off `C` essential in the complement of a closed piece of `C` away from it)
and Antoine's theorem for the built necklace, stated as `GX.antoineNecklace_antoine` — it is wild,
and at every point `x` of it, inside every neighbourhood, a meridian of a link not containing `x`
is essential in the complement of the sub-necklace in that link. Antoine's theorem is NOT
formalized: it is that declaration's tagged `sorry` (residual obstruction in its comment and in
the report; no abelian invariant can detect the meridian, by Alexander duality). Side
remark, outside the ruled reading: for arbitrary wild Cantor sets the claim fails as soon as one
of them has dense, simply connected, locally non-separating complement
(`GX.wild_cantor_claim_false_of_exists`; the density is proved for every Cantor set,
`GX.dense_compl_of_isCantorSubset`); the cited existence (Kirkor, Skora, Garity–Repovš–Željko) is
no longer stated, DEC-58 having ruled the reading.

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

/-! ### `ex:following_situations_semi_locally_simply` in the literal reading (DEC-55) -/

section ItemsCC

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Y : Type*} [TopologicalSpace Y]

/-- Item 1, literal reading (`GX.IsSLSCInCC`). -/
theorem following_situations_finite_cc [Nontrivial E] [ChartedSpace E Y] {S : Set Y}
    (hS : S.Finite) : IsSLSCInCC Sᶜ :=
  (following_situations_finite (E := E) hS).isSLSCInCC

/-- Item 2, literal reading. -/
theorem following_situations_tame_cc [FiniteDimensional ℝ E] (hE : 2 ≤ Module.finrank ℝ E)
    {S : Set Y} (hS : IsLocallyPolygonal E S) : IsSLSCInCC Sᶜ :=
  (following_situations_tame hE hS).isSLSCInCC

/-- Item 2, tame knots of `ℝ³`, literal reading. -/
theorem following_situations_tame_knot_cc
    (g : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3))
    (P : Finset (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))) :
    IsSLSCInCC (g '' polygonalSet P)ᶜ :=
  (following_situations_tame_knot g P).isSLSCInCC

/-- Item 3, literal reading. -/
theorem following_situations_simplicial_cc (K : Geometry.SimplicialComplex ℝ E)
    (hK : LocallyFinite fun τ : K.faces => convexHull ℝ ((τ : Finset E) : Set E)) {n : ℕ}
    (hfaces : HasFacesOfCardGe K n) :
    IsSLSCInCC (((↑) : K.space → E) ⁻¹' (⋃ s ∈ skeletonFaces K n, convexHull ℝ (s : Set E))ᶜ) :=
  (following_situations_simplicial K hK hfaces).isSLSCInCC

end ItemsCC

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

/-- **`ex:consider_denote_absolute_galois`, first claim, literal reading** (DEC-55): `ℂ ∖ S` is
not semi-locally simply connected in `ℂ` in the compact-open sense of `def:almost_trivial_loop`
(`GX.IsSLSCInCC`); the two readings agree here because `ℂ ∖ S` is open and semilocally simply
connected (`GX.isSLSCInCC_iff`). -/
theorem absGal_not_isSLSCInCC : ¬ IsSLSCInCC (fibSᶜ : Set ℂ) := fun h =>
  absGal_not_isSLSCIn ((isSLSCInCC_iff isClosed_fibS.isOpen_compl semilocallySimplyConnected_fibS).1 h)

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

/-! #### A dihedral invariant of `ℂ ∖ S`

The refutation of the fibre claim rests on an invariant of the universal covering
`\widetilde{ℂ∖S}` with values in the infinite dihedral group `ℤ ⋊ ℤ/2`, built from two continuous
logarithms: `ℓ` with `exp ℓ = F ∘ p`, `F(z) = (z-1)/(z-1/2)` (so `sq = exp(ℓ/2)` is a square root
of `F`, which changes sign along a loop winding an odd number of times around `{1, 1/2}`), and `Λ`
with `exp Λ = G ∘ sq`, `G(s) = (s-1)/(s+1)` (`G(-s) = G(s)⁻¹`). A deck transformation acts on
`(sq, Λ)` by `(sq, Λ) ↦ (±sq, ±Λ + c)`; the squares of the loops around `1` and `1/2`, and the
loops around the other points of `S` (taken in the region `GX.absGalR`), act trivially, while
a loop around both `1` and `1/2` acts by a translation `Λ ↦ Λ ± 2πi`. -/

/-- `1 ∈ S`. -/
theorem absGal_one_mem : (1 : ℂ) ∈ fibS := Or.inr ⟨0, by simp⟩

/-- `1/2 ∈ S`. -/
theorem absGal_half_mem : (1 / 2 : ℂ) ∈ fibS := Or.inr ⟨1, by push_cast; norm_num⟩

/-- `F(z) = (z-1)/(z-1/2)`. -/
def absGalF (z : ℂ) : ℂ := (z - 1) / (z - 1 / 2)

/-- `G(s) = (s-1)/(s+1)`. -/
def absGalG (s : ℂ) : ℂ := (s - 1) / (s + 1)

theorem absGalF_ne_zero {z : ℂ} (hz : z ∉ fibS) : absGalF z ≠ 0 :=
  div_ne_zero (sub_ne_zero.2 fun h => hz (h ▸ absGal_one_mem))
    (sub_ne_zero.2 fun h => hz (h ▸ absGal_half_mem))

theorem absGalF_ne_one (z : ℂ) : absGalF z ≠ 1 := by
  intro h
  by_cases hz : z - 1 / 2 = 0
  · rw [absGalF, hz, div_zero] at h; exact zero_ne_one h
  · rw [absGalF, div_eq_one_iff_eq hz] at h
    have := congrArg (fun w => w - z) h
    norm_num at this

theorem absGal_ne_one_of_sq {s w : ℂ} (hs : s ^ 2 = w) (hw : w ≠ 1) : s ≠ 1 := by
  rintro rfl; exact hw (by rw [← hs]; norm_num)

theorem absGal_ne_neg_one_of_sq {s w : ℂ} (hs : s ^ 2 = w) (hw : w ≠ 1) : s ≠ -1 := by
  rintro rfl; exact hw (by rw [← hs]; norm_num)

theorem absGalG_ne_zero {s : ℂ} (h1 : s ≠ 1) (h2 : s ≠ -1) : absGalG s ≠ 0 :=
  div_ne_zero (sub_ne_zero.2 h1) (fun h => h2 (eq_neg_of_add_eq_zero_left h))

theorem absGalG_neg {s : ℂ} (h1 : s ≠ 1) (h2 : s ≠ -1) : absGalG (-s) = (absGalG s)⁻¹ := by
  have a : s - 1 ≠ 0 := sub_ne_zero.2 h1
  have b : s + 1 ≠ 0 := fun h => h2 (eq_neg_of_add_eq_zero_left h)
  have c : -s + 1 ≠ 0 := fun h => h1 (by linear_combination -h)
  rw [absGalG, absGalG, inv_div]
  field_simp
  ring

/-- Two continuous lifts through `exp` on a preconnected space differ by a constant. -/
theorem absGal_expLift_eq {A : Type*} [TopologicalSpace A] [PreconnectedSpace A] {f g : A → ℂ}
    (hf : Continuous f) (hg : Continuous g) (h : ∀ a, Complex.exp (f a) = Complex.exp (g a))
    (a₀ a : A) : g a = f a + (g a₀ - f a₀) := by
  have hc : Complex.exp (g a₀ - f a₀) = 1 := by
    rw [Complex.exp_sub, ← h a₀, div_self (Complex.exp_ne_zero _)]
  have := isCoveringMap_cExp.eq_of_comp_eq (g₁ := fun a => f a + (g a₀ - f a₀)) (g₂ := g)
    (by fun_prop) hg (funext fun a => Subtype.ext (by
      simp only [comp_apply, cExp_apply, Complex.exp_add, hc, mul_one, h a])) a₀ (by ring)
  exact (congrFun this a).symm

/-- `ℂ ∖ S` is locally path-connected. -/
theorem absGal_locPath : LocPathConnectedSpace (fibSᶜ : Set ℂ) :=
  isClosed_fibS.isOpen_compl.locPathConnectedSpace

attribute [local instance] absGal_locPath

/-- `\widetilde{ℂ∖S}`. -/
abbrev AbsU : Type := UniversalCover (fibSᶜ : Set ℂ) y₀

/-- `\widetilde{ℂ∖S}` is simply connected. -/
theorem absGal_simplyConnected {y₀ : (fibSᶜ : Set ℂ)} : SimplyConnectedSpace (AbsU y₀) :=
  UniversalCover.simplyConnectedSpace semilocallySimplyConnected_fibS

attribute [local instance] absGal_simplyConnected

/-- The projection `\widetilde{ℂ∖S} → ℂ`. -/
def absP (c : AbsU y₀) : ℂ := ((c.pt : (fibSᶜ : Set ℂ)) : ℂ)

theorem continuous_absP : Continuous (absP y₀) :=
  continuous_subtype_val.comp UniversalCover.continuous_proj

theorem absP_not_mem (c : AbsU y₀) : absP y₀ c ∉ fibS := c.pt.2

theorem continuous_absGalF_absP : Continuous fun c => absGalF (absP y₀ c) :=
  ((continuous_absP y₀).sub continuous_const).div ((continuous_absP y₀).sub continuous_const)
    fun c => sub_ne_zero.2 fun h => absP_not_mem y₀ c (h ▸ absGal_half_mem)

/-- `F ∘ p`, into `ℂ ∖ {0}`. -/
def absGalFC : C(AbsU y₀, CStar) :=
  ⟨fun c => ⟨absGalF (absP y₀ c), absGalF_ne_zero (absP_not_mem y₀ c)⟩,
    (continuous_absGalF_absP y₀).subtype_mk _⟩

theorem absGal_exists_ℓ : ∃ ℓ : C(AbsU y₀, ℂ), ∀ c, Complex.exp (ℓ c) = absGalF (absP y₀ c) := by
  obtain ⟨ℓ, ⟨-, hℓ⟩, -⟩ := isCoveringMap_cExp.existsUnique_continuousMap_lifts (absGalFC y₀)
    (UniversalCover.base y₀) (Complex.log (absGalFC y₀ (UniversalCover.base y₀)))
    (Subtype.ext (Complex.exp_log (absGalFC y₀ _).2))
  exact ⟨ℓ, fun c => congrArg Subtype.val (congrFun hℓ c)⟩

/-- A continuous logarithm `ℓ` of `F ∘ p` on `\widetilde{ℂ∖S}`. -/
def absGalℓ : C(AbsU y₀, ℂ) := (absGal_exists_ℓ y₀).choose

theorem absGalℓ_spec (c : AbsU y₀) : Complex.exp (absGalℓ y₀ c) = absGalF (absP y₀ c) :=
  (absGal_exists_ℓ y₀).choose_spec c

/-- The square root `sq = exp(ℓ/2)` of `F ∘ p`. -/
def absGalSq (c : AbsU y₀) : ℂ := Complex.exp (absGalℓ y₀ c / 2)

theorem continuous_absGalSq : Continuous (absGalSq y₀) := by
  unfold absGalSq; fun_prop

theorem absGalSq_sq (c : AbsU y₀) : absGalSq y₀ c ^ 2 = absGalF (absP y₀ c) := by
  rw [absGalSq, sq, ← Complex.exp_add, add_halves, absGalℓ_spec]

theorem absGalSq_ne_one (c : AbsU y₀) : absGalSq y₀ c ≠ 1 :=
  absGal_ne_one_of_sq (absGalSq_sq y₀ c) (absGalF_ne_one _)

theorem absGalSq_ne_neg_one (c : AbsU y₀) : absGalSq y₀ c ≠ -1 :=
  absGal_ne_neg_one_of_sq (absGalSq_sq y₀ c) (absGalF_ne_one _)

/-- `G ∘ sq`, into `ℂ ∖ {0}`. -/
def absGalGC : C(AbsU y₀, CStar) :=
  ⟨fun c => ⟨absGalG (absGalSq y₀ c), absGalG_ne_zero (absGalSq_ne_one y₀ c)
    (absGalSq_ne_neg_one y₀ c)⟩, by
    refine Continuous.subtype_mk ?_ _
    exact ((continuous_absGalSq y₀).sub continuous_const).div
      ((continuous_absGalSq y₀).add continuous_const) fun c h =>
        absGalSq_ne_neg_one y₀ c (eq_neg_of_add_eq_zero_left h)⟩

theorem absGal_exists_Λ : ∃ Λ : C(AbsU y₀, ℂ), ∀ c, Complex.exp (Λ c) = absGalG (absGalSq y₀ c) := by
  obtain ⟨Λ, ⟨-, hΛ⟩, -⟩ := isCoveringMap_cExp.existsUnique_continuousMap_lifts (absGalGC y₀)
    (UniversalCover.base y₀) (Complex.log (absGalGC y₀ (UniversalCover.base y₀)))
    (Subtype.ext (Complex.exp_log (absGalGC y₀ _).2))
  exact ⟨Λ, fun c => congrArg Subtype.val (congrFun hΛ c)⟩

/-- A continuous logarithm `Λ` of `G ∘ sq` on `\widetilde{ℂ∖S}`. -/
def absGalΛ : C(AbsU y₀, ℂ) := (absGal_exists_Λ y₀).choose

theorem absGalΛ_spec (c : AbsU y₀) : Complex.exp (absGalΛ y₀ c) = absGalG (absGalSq y₀ c) :=
  (absGal_exists_Λ y₀).choose_spec c

section Deck

variable {y₀} (φ : AbsU y₀ ≃ₜ AbsU y₀) (hφ : ∀ c, absP y₀ (φ c) = absP y₀ c)

include hφ in
/-- A deck transformation shifts `ℓ` by a constant. -/
theorem absGalℓ_deck (c : AbsU y₀) :
    absGalℓ y₀ (φ c) = absGalℓ y₀ c +
      (absGalℓ y₀ (φ (UniversalCover.base y₀)) - absGalℓ y₀ (UniversalCover.base y₀)) :=
  absGal_expLift_eq (absGalℓ y₀).continuous ((absGalℓ y₀).continuous.comp φ.continuous)
    (fun a => by simp only [comp_apply, absGalℓ_spec, hφ]) _ c

/-- The sign `ε = ±1` by which a deck transformation acts on `sq`. -/
def absGalSign : ℂ :=
  Complex.exp ((absGalℓ y₀ (φ (UniversalCover.base y₀)) - absGalℓ y₀ (UniversalCover.base y₀)) / 2)

include hφ in
theorem absGalSq_deck (c : AbsU y₀) : absGalSq y₀ (φ c) = absGalSign φ * absGalSq y₀ c := by
  rw [absGalSq, absGalℓ_deck φ hφ, add_div, Complex.exp_add, absGalSign, absGalSq, mul_comm]

include hφ in
theorem absGalSign_eq : absGalSign φ = 1 ∨ absGalSign φ = -1 := by
  have h := absGalSq_deck φ hφ (UniversalCover.base y₀)
  have h2 := congrArg (· ^ 2) h
  simp only [mul_pow, absGalSq_sq, hφ] at h2
  have hF := absGalF_ne_zero (absP_not_mem y₀ (UniversalCover.base y₀))
  have : absGalSign φ ^ 2 = 1 := by
    have := h2.symm
    rwa [mul_left_eq_self₀, or_iff_left hF] at this
  rw [sq] at this
  exact mul_self_eq_one_iff.1 this

include hφ in
/-- An even deck transformation (`sq ∘ φ = sq`) shifts `Λ` by a constant. -/
theorem absGalΛ_deck_even (h : absGalSign φ = 1) (c : AbsU y₀) :
    absGalΛ y₀ (φ c) = absGalΛ y₀ c +
      (absGalΛ y₀ (φ (UniversalCover.base y₀)) - absGalΛ y₀ (UniversalCover.base y₀)) :=
  absGal_expLift_eq (absGalΛ y₀).continuous ((absGalΛ y₀).continuous.comp φ.continuous)
    (fun a => by simp only [comp_apply, absGalΛ_spec, absGalSq_deck φ hφ, h, one_mul]) _ c

include hφ in
/-- An odd deck transformation (`sq ∘ φ = -sq`) acts on `Λ` by `Λ ↦ -Λ + c`. -/
theorem absGalΛ_deck_odd (h : absGalSign φ = -1) (c : AbsU y₀) :
    absGalΛ y₀ (φ c) = -absGalΛ y₀ c +
      (absGalΛ y₀ (φ (UniversalCover.base y₀)) + absGalΛ y₀ (UniversalCover.base y₀)) := by
  have := absGal_expLift_eq (f := fun a => -absGalΛ y₀ a) (absGalΛ y₀).continuous.neg
    ((absGalΛ y₀).continuous.comp φ.continuous)
    (fun a => by
      simp only [comp_apply, absGalΛ_spec, absGalSq_deck φ hφ, h, neg_one_mul, Complex.exp_neg]
      rw [absGalG_neg (absGalSq_ne_one y₀ a) (absGalSq_ne_neg_one y₀ a)]) (UniversalCover.base y₀) c
  simp only [comp_apply] at this
  rw [this]; ring

include hφ in
/-- Every deck transformation acts on `(sq, Λ)` through functions of `(sq, Λ)`. -/
theorem absGal_deck_action : ∃ (ε : ℂ) (u : ℂ → ℂ), (∀ c, absGalSq y₀ (φ c) = ε * absGalSq y₀ c) ∧
    ∀ c, absGalΛ y₀ (φ c) = u (absGalΛ y₀ c) := by
  rcases absGalSign_eq φ hφ with h | h
  · exact ⟨_, fun v => v + (absGalΛ y₀ (φ (UniversalCover.base y₀)) -
      absGalΛ y₀ (UniversalCover.base y₀)), absGalSq_deck φ hφ, absGalΛ_deck_even φ hφ h⟩
  · exact ⟨_, fun v => -v + (absGalΛ y₀ (φ (UniversalCover.base y₀)) +
      absGalΛ y₀ (UniversalCover.base y₀)), absGalSq_deck φ hφ, absGalΛ_deck_odd φ hφ h⟩

end Deck

theorem absP_deckHom (g : AbsGamma y₀) (c : AbsU y₀) :
    absP y₀ ((UniversalCover.deckHom g).1 c) = absP y₀ c := rfl

/-- The deck transformations fixing `sq` and `Λ`. -/
def AbsGalFix (φ : AbsU y₀ ≃ₜ AbsU y₀) : Prop :=
  (∀ c, absGalSq y₀ (φ c) = absGalSq y₀ c) ∧ ∀ c, absGalΛ y₀ (φ c) = absGalΛ y₀ c

/-- The subgroup of `Γ = π₁(ℂ ∖ S, y₀)` acting trivially on `(sq, Λ)`. -/
def absGalN : Subgroup (AbsGamma y₀) where
  carrier := {g | AbsGalFix y₀ (UniversalCover.deckHom g).1}
  one_mem' := by
    show AbsGalFix y₀ (UniversalCover.deckHom 1).1
    rw [map_one]
    exact ⟨fun _ => rfl, fun _ => rfl⟩
  mul_mem' := by
    intro a b ha hb
    show AbsGalFix y₀ (UniversalCover.deckHom (a * b)).1
    rw [map_mul]
    exact ⟨fun c => (ha.1 _).trans (hb.1 c), fun c => (ha.2 _).trans (hb.2 c)⟩
  inv_mem' := by
    intro a ha
    show AbsGalFix y₀ (UniversalCover.deckHom a⁻¹).1
    have e : ∀ c, (UniversalCover.deckHom a).1 ((UniversalCover.deckHom a⁻¹).1 c) = c := fun c => by
      rw [← Homeomorph.mul_apply, ← Subgroup.coe_mul, ← map_mul, mul_inv_cancel, map_one]; rfl
    refine ⟨fun c => ?_, fun c => ?_⟩
    · have := ha.1 ((UniversalCover.deckHom a⁻¹).1 c); rw [e] at this; exact this.symm
    · have := ha.2 ((UniversalCover.deckHom a⁻¹).1 c); rw [e] at this; exact this.symm

theorem mem_absGalN {g : AbsGamma y₀} : g ∈ absGalN y₀ ↔ AbsGalFix y₀ (UniversalCover.deckHom g).1 :=
  Iff.rfl

instance absGalN_normal : (absGalN y₀).Normal := by
  refine ⟨fun g hg h => ?_⟩
  rw [mem_absGalN]
  obtain ⟨ε, u, hε, hu⟩ := absGal_deck_action (UniversalCover.deckHom h).1 (absP_deckHom y₀ h)
  have e : ∀ c, (UniversalCover.deckHom h).1 ((UniversalCover.deckHom h⁻¹).1 c) = c := fun c => by
    rw [← Homeomorph.mul_apply, ← Subgroup.coe_mul, ← map_mul, mul_inv_cancel, map_one]; rfl
  have hm : ∀ c, (UniversalCover.deckHom (h * g * h⁻¹)).1 c = (UniversalCover.deckHom h).1
      ((UniversalCover.deckHom g).1 ((UniversalCover.deckHom h⁻¹).1 c)) := fun c => by
    rw [map_mul, map_mul]; rfl
  refine ⟨fun c => ?_, fun c => ?_⟩
  · rw [hm, hε, hg.1, ← hε, e]
  · rw [hm, hu, hg.2, ← hu, e]

/-- The square of an odd deck transformation fixes `sq` and `Λ`. -/
theorem absGal_sq_mem_of_odd {g : AbsGamma y₀}
    (h : absGalSign (UniversalCover.deckHom g).1 = -1) : g ^ 2 ∈ absGalN y₀ := by
  rw [mem_absGalN, pow_two, map_mul]
  set φ := (UniversalCover.deckHom g).1
  have hφ := absP_deckHom y₀ g
  refine ⟨fun c => ?_, fun c => ?_⟩
  · show absGalSq y₀ (φ (φ c)) = _
    rw [absGalSq_deck φ hφ, absGalSq_deck φ hφ, h]; ring
  · show absGalΛ y₀ (φ (φ c)) = _
    rw [absGalΛ_deck_odd φ hφ h, absGalΛ_deck_odd φ hφ h]; ring

/-- The deck transformation of a loop class moves the base point to the end of the canonical lift
of the reversed loop. -/
theorem absGal_deckHom_base (γ : Path y₀ y₀) :
    (UniversalCover.deckHom (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ))).1
      (UniversalCover.base y₀) = UniversalCover.liftFrom (Path.Homotopic.Quotient.refl y₀) γ.symm 1 := by
  rw [Path.target, UniversalCover.deckHom_apply]
  show (⟨y₀, (Path.Homotopic.Quotient.mk γ.symm).trans (Path.Homotopic.Quotient.refl y₀)⟩ :
    AbsU y₀) = ⟨y₀, (Path.Homotopic.Quotient.refl y₀).trans (Path.Homotopic.Quotient.mk γ.symm)⟩
  rw [Path.Homotopic.Quotient.trans_refl, Path.Homotopic.Quotient.refl_trans]

/-- `F`, from `ℂ ∖ S` to `ℂ ∖ {0}`. -/
def absGalFY : C((fibSᶜ : Set ℂ), CStar) :=
  ⟨fun z => ⟨absGalF z, absGalF_ne_zero z.2⟩, by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_subtype_val.sub continuous_const).div
      (continuous_subtype_val.sub continuous_const) fun z => sub_ne_zero.2 fun h =>
        z.2 (h ▸ absGal_half_mem)⟩

/-- Along the canonical lift `L` of a path `δ` from `⟨a, c⟩`, `ℓ ∘ L` lifts `F ∘ δ`. -/
theorem absGalℓ_liftFrom {a b : (fibSᶜ : Set ℂ)} (c : Path.Homotopic.Quotient y₀ a)
    (δ : Path a b) (t : I) :
    Complex.exp (absGalℓ y₀ (UniversalCover.liftFrom c δ t)) = absGalF (δ t) := by
  rw [absGalℓ_spec]; rfl

theorem absGalSq_liftFrom_sq {a b : (fibSᶜ : Set ℂ)} (c : Path.Homotopic.Quotient y₀ a)
    (δ : Path a b) (t : I) :
    absGalSq y₀ (UniversalCover.liftFrom c δ t) ^ 2 = absGalF (δ t) := by
  rw [absGalSq_sq]; rfl

/-- The winding number of a reversed loop. -/
theorem absGal_cWinding_symm {X : Type*} [TopologicalSpace X] {x : X} (δ : Path x x)
    (f : C(X, CStar)) :
    cWinding (δ.symm.map f.continuous) = -cWinding (δ.map f.continuous) := by
  obtain ⟨Γ, hΓ⟩ := exists_expLift (δ.map f.continuous).toContinuousMap
  have e := cWinding_spec _ hΓ
  refine cWinding_eq _ (Γ := Γ.comp ⟨unitInterval.symm, continuous_symm⟩) (fun t => ?_) ?_
  · have := hΓ (unitInterval.symm t)
    simp only [ContinuousMap.coe_comp, ContinuousMap.coe_mk, comp_apply] at this ⊢
    rw [this]; rfl
  · simp only [ContinuousMap.coe_comp, ContinuousMap.coe_mk, comp_apply, unitInterval.symm_one,
      unitInterval.symm_zero, e]
    push_cast; ring

/-- The winding number of `F ∘ δ` is the difference of the winding numbers of `δ` around `1` and
around `1/2`. -/
theorem absGal_cWinding_F (δ : Path y₀ y₀) :
    cWinding (δ.map absGalFY.continuous) =
      windAt y₀ _ (fibPt_mem 0) δ - windAt y₀ _ (fibPt_mem 1) δ := by
  obtain ⟨Γ₁, h₁⟩ := exists_expLift (δ.map (subFib _ (fibPt_mem 0)).continuous).toContinuousMap
  obtain ⟨Γ₂, h₂⟩ := exists_expLift (δ.map (subFib _ (fibPt_mem 1)).continuous).toContinuousMap
  have e₁ := cWinding_spec _ h₁
  have e₂ := cWinding_spec _ h₂
  refine cWinding_eq _ (Γ := Γ₁ - Γ₂) (fun t => ?_) ?_
  · simp only [ContinuousMap.sub_apply, Complex.exp_sub]
    rw [h₁ t, h₂ t]
    show ((δ t : ℂ) - ((1 / (((0 : ℕ) : ℝ) + 1) : ℝ) : ℂ)) /
      ((δ t : ℂ) - ((1 / (((1 : ℕ) : ℝ) + 1) : ℝ) : ℂ)) = absGalF (δ t)
    rw [absGalF]; push_cast; norm_num
  · simp only [ContinuousMap.sub_apply]
    rw [e₁, e₂]; unfold windAt; push_cast; ring

/-- A loop winding once around `1` and not around `1/2` (or the reverse) gives an ODD deck
transformation. -/
theorem absGalSign_of_wind (γ : Path y₀ y₀)
    (h : windAt y₀ _ (fibPt_mem 0) γ - windAt y₀ _ (fibPt_mem 1) γ = 1 ∨
      windAt y₀ _ (fibPt_mem 0) γ - windAt y₀ _ (fibPt_mem 1) γ = -1) :
    absGalSign (UniversalCover.deckHom (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk γ))).1 = -1 := by
  rw [absGalSign, absGal_deckHom_base]
  set L := UniversalCover.liftFrom (Path.Homotopic.Quotient.refl y₀) γ.symm
  have hL : ∀ t, Complex.exp ((absGalℓ y₀).comp ⟨L, L.continuous⟩ t) =
      (γ.symm.map absGalFY.continuous) t := fun t => absGalℓ_liftFrom y₀ _ γ.symm t
  have e := cWinding_spec _ hL
  rw [absGal_cWinding_symm, absGal_cWinding_F] at e
  simp only [ContinuousMap.coe_comp, ContinuousMap.coe_mk, comp_apply] at e
  have e' : absGalℓ y₀ (L 1) - absGalℓ y₀ (UniversalCover.base y₀) =
      -((windAt y₀ _ (fibPt_mem 0) γ - windAt y₀ _ (fibPt_mem 1) γ : ℤ) : ℂ) *
        (2 * Real.pi * Complex.I) := by
    rw [e]
    have : L 0 = UniversalCover.base y₀ := L.source
    rw [this]
    push_cast; ring
  rw [e']
  rcases h with h | h <;> rw [h] <;> push_cast
  · rw [show -(1 : ℂ) * (2 * Real.pi * Complex.I) / 2 = -(Real.pi * Complex.I) by ring,
      Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num
  · rw [show -(-1 : ℂ) * (2 * Real.pi * Complex.I) / 2 = Real.pi * Complex.I by ring,
      Complex.exp_pi_mul_I]

/-- The principal square root `σ(z) = exp(log F(z) / 2)` of `F`. -/
def absGalσ (z : ℂ) : ℂ := Complex.exp (Complex.log (absGalF z) / 2)

/-- The logarithm `g(z) = log G(σ(z))`. -/
def absGalLog (z : ℂ) : ℂ := Complex.log (absGalG (absGalσ z))

/-- The region where `σ` and `g` are continuous: `F(z)` and `G(σ(z))` in the slit plane. It
contains a neighbourhood of every point of `S ∖ {1, 1/2}` and of `0` (it misses only the closed
disc of diameter `[1/2, 1]` and the ray `[1, ∞)`). -/
def absGalR : Set ℂ := {z | absGalF z ∈ Complex.slitPlane ∧ absGalG (absGalσ z) ∈ Complex.slitPlane}

theorem absGalσ_sq {z : ℂ} (hz : absGalF z ≠ 0) : absGalσ z ^ 2 = absGalF z := by
  rw [absGalσ, sq, ← Complex.exp_add, add_halves, Complex.exp_log hz]

theorem absGalσ_ne_zero (z : ℂ) : absGalσ z ≠ 0 := Complex.exp_ne_zero _

theorem absGalσ_ne_one {z : ℂ} (hz : absGalF z ≠ 0) : absGalσ z ≠ 1 :=
  absGal_ne_one_of_sq (absGalσ_sq hz) (absGalF_ne_one z)

theorem absGalσ_ne_neg_one {z : ℂ} (hz : absGalF z ≠ 0) : absGalσ z ≠ -1 :=
  absGal_ne_neg_one_of_sq (absGalσ_sq hz) (absGalF_ne_one z)

theorem absGalF_ne_zero_of_mem {z : ℂ} (hz : z ∈ absGalR) : absGalF z ≠ 0 :=
  Complex.slitPlane_ne_zero hz.1

/-- `exp (r g) = G(r σ)` for `r = ±1`. -/
theorem absGal_exp_mul_log {z : ℂ} (hz : z ∈ absGalR) {r : ℂ} (hr : r = 1 ∨ r = -1) :
    Complex.exp (r * absGalLog z) = absGalG (r * absGalσ z) := by
  have hG : absGalG (absGalσ z) ≠ 0 := Complex.slitPlane_ne_zero hz.2
  rcases hr with rfl | rfl
  · rw [one_mul, one_mul, absGalLog, Complex.exp_log hG]
  · rw [neg_one_mul, neg_one_mul, Complex.exp_neg, absGalLog, Complex.exp_log hG,
      absGalG_neg (absGalσ_ne_one (absGalF_ne_zero_of_mem hz))
        (absGalσ_ne_neg_one (absGalF_ne_zero_of_mem hz))]

theorem continuousAt_absGalF {z : ℂ} (hz : z - 1 / 2 ≠ 0) : ContinuousAt absGalF z :=
  ((continuous_id.sub continuous_const).continuousAt).div
    ((continuous_id.sub continuous_const).continuousAt) hz

theorem absGal_sub_half_ne {z : ℂ} (hz : z ∈ absGalR) : z - 1 / 2 ≠ 0 := fun h => by
  have := hz.1
  rw [absGalF, h, div_zero] at this
  exact Complex.slitPlane_ne_zero this rfl

theorem continuousAt_absGalσ {z : ℂ} (hz : z ∈ absGalR) : ContinuousAt absGalσ z :=
  (((continuousAt_absGalF (absGal_sub_half_ne hz)).clog hz.1).div_const 2).cexp

theorem continuousAt_absGalLog {z : ℂ} (hz : z ∈ absGalR) : ContinuousAt absGalLog z := by
  have h1 : absGalσ z + 1 ≠ 0 := fun h =>
    absGalσ_ne_neg_one (absGalF_ne_zero_of_mem hz) (eq_neg_of_add_eq_zero_left h)
  have hG : ContinuousAt (fun w => absGalG (absGalσ w)) z :=
    ((continuousAt_absGalσ hz).sub continuousAt_const).div
      ((continuousAt_absGalσ hz).add continuousAt_const) h1
  exact hG.clog hz.2

theorem absGal_contAt_comp {f : ℂ → ℂ} {δ : I → ℂ} (hδ : Continuous δ) (t : I)
    (hf : ContinuousAt f (δ t)) : ContinuousAt (fun s => f (δ s)) t :=
  hf.comp hδ.continuousAt

/-- `r = sq / σ ∘ p` satisfies `r² = 1`. -/
theorem absGal_ratio_sq {s z : ℂ} (hs : s ^ 2 = absGalF z) (hz : absGalF z ≠ 0) :
    s / absGalσ z = 1 ∨ s / absGalσ z = -1 := by
  have : (s / absGalσ z) * (s / absGalσ z) = 1 := by
    rw [← sq, div_pow, hs, absGalσ_sq hz, div_self hz]
  exact mul_self_eq_one_iff.1 this

/-- **Loops in `absGalR` act trivially.** A loop of `ℂ ∖ S` at `y₀` lying in `absGalR` gives a
deck transformation fixing `sq` and `Λ`. -/
theorem absGal_mem_N_of_mem_R (γ : Path y₀ y₀) (hγ : ∀ t, ((γ t : (fibSᶜ : Set ℂ)) : ℂ) ∈ absGalR) :
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ) ∈ absGalN y₀ := by
  set g := FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)
  set φ := (UniversalCover.deckHom g).1
  have hφ := absP_deckHom y₀ g
  set L := UniversalCover.liftFrom (Path.Homotopic.Quotient.refl y₀) γ.symm
  have hLb : φ (UniversalCover.base y₀) = L 1 := absGal_deckHom_base y₀ γ
  have hL0 : L 0 = UniversalCover.base y₀ := L.source
  have hδ : ∀ t, ((γ.symm t : (fibSᶜ : Set ℂ)) : ℂ) ∈ absGalR := fun t => hγ _
  have hP : ∀ t, absP y₀ (L t) = ((γ.symm t : (fibSᶜ : Set ℂ)) : ℂ) := fun t => rfl
  have hcδ : Continuous fun t => ((γ.symm t : (fibSᶜ : Set ℂ)) : ℂ) :=
    continuous_subtype_val.comp γ.symm.continuous
  -- the first logarithm returns: `log F` is a lift
  have hℓ : absGalℓ y₀ (L 1) = absGalℓ y₀ (L 0) := by
    have hc : Continuous fun t => Complex.log (absGalF ((γ.symm t : (fibSᶜ : Set ℂ)) : ℂ)) :=
      continuous_iff_continuousAt.2 fun t =>
        (absGal_contAt_comp hcδ t (continuousAt_absGalF (absGal_sub_half_ne (hδ t)))).clog (hδ t).1
    have := absGal_expLift_eq hc ((absGalℓ y₀).continuous.comp L.continuous) (fun t => by
      simp only [comp_apply]
      rw [Complex.exp_log (absGalF_ne_zero_of_mem (hδ t)), absGalℓ_liftFrom]) 0 1
    simp only [comp_apply] at this
    rw [this]
    simp only [Path.source, γ.symm.source, γ.symm.target]
    ring
  have hsign : absGalSign φ = 1 := by
    rw [absGalSign, hLb, ← hL0, hℓ, sub_self, zero_div, Complex.exp_zero]
  have hsqeq : absGalSq y₀ (L 1) = absGalSq y₀ (L 0) := by rw [absGalSq, absGalSq, hℓ]
  -- the second logarithm returns: `r · g` is a lift
  set r : I → ℂ := fun t => absGalSq y₀ (L t) / absGalσ ((γ.symm t : (fibSᶜ : Set ℂ)) : ℂ)
  have hr : ∀ t, r t = 1 ∨ r t = -1 := fun t =>
    absGal_ratio_sq (absGalSq_liftFrom_sq y₀ _ _ t) (absGalF_ne_zero_of_mem (hδ t))
  have hrc : Continuous r := by
    refine ((continuous_absGalSq y₀).comp L.continuous).div ?_ fun t => absGalσ_ne_zero _
    exact continuous_iff_continuousAt.2 fun t => absGal_contAt_comp hcδ t (continuousAt_absGalσ (hδ t))
  have hgc : Continuous fun t => absGalLog ((γ.symm t : (fibSᶜ : Set ℂ)) : ℂ) :=
    continuous_iff_continuousAt.2 fun t => absGal_contAt_comp hcδ t (continuousAt_absGalLog (hδ t))
  have hΛ : absGalΛ y₀ (L 1) = absGalΛ y₀ (L 0) := by
    have := absGal_expLift_eq (hrc.mul hgc) ((absGalΛ y₀).continuous.comp L.continuous)
      (fun t => by
        simp only [comp_apply, Pi.mul_apply]
        rw [absGal_exp_mul_log (hδ t) (hr t), absGalΛ_spec]
        congr 1
        exact (div_mul_cancel₀ _ (absGalσ_ne_zero _))) 0 1
    simp only [comp_apply, Pi.mul_apply] at this
    rw [this]
    have h01 : r 1 = r 0 := by
      simp only [r, hsqeq, γ.symm.source, γ.symm.target]
    simp only [h01, γ.symm.source, γ.symm.target]
    ring
  refine ⟨fun c => ?_, fun c => ?_⟩
  · rw [absGalSq_deck φ hφ, hsign, one_mul]
  · rw [absGalΛ_deck_even φ hφ hsign, hLb, ← hL0, hΛ, sub_self, add_zero]

/-- `exp (r a) = G(r σ)` for `r = ±1` once `exp a = G(σ)`. -/
theorem absGal_exp_mul_of {a s₀ r : ℂ} (ha : Complex.exp a = absGalG s₀) (h1 : s₀ ≠ 1)
    (h2 : s₀ ≠ -1) (hr : r = 1 ∨ r = -1) : Complex.exp (r * a) = absGalG (r * s₀) := by
  rcases hr with rfl | rfl
  · rw [one_mul, one_mul, ha]
  · rw [neg_one_mul, neg_one_mul, Complex.exp_neg, ha, absGalG_neg h1 h2]

/-! The loop `ω` around `1` and `1/2`: with `u = e^{2iπt}/20`, `ω = 1/2 - (1-u)²/(8u)`, so that
`F(ω) = ((1+u)/(1-u))²` and `G((1+u)/(1-u)) = u` winds once around `0`. -/

/-- `u(t) = e^{2iπt}/20`. -/
def absGalU (t : I) : ℂ := (1 / 20 : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ))

theorem continuous_absGalU : Continuous absGalU := by unfold absGalU; fun_prop

theorem norm_absGalU (t : I) : ‖absGalU t‖ = 1 / 20 := by
  have h : ‖Complex.exp (2 * Real.pi * Complex.I * (t : ℝ))‖ = 1 := by
    rw [show (2 * Real.pi * Complex.I * (t : ℝ) : ℂ) = ((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.norm_exp_ofReal_mul_I]
  rw [absGalU, norm_mul, h, mul_one]
  norm_num

theorem absGalU_ne_zero (t : I) : absGalU t ≠ 0 := fun h => by
  have := norm_absGalU t; rw [h, norm_zero] at this; norm_num at this

theorem absGalU_one : absGalU 1 = absGalU 0 := by
  simp only [absGalU, Set.Icc.coe_one, Set.Icc.coe_zero, Complex.ofReal_one, Complex.ofReal_zero,
    mul_one, mul_zero, Complex.exp_zero]
  rw [show 2 * (Real.pi : ℂ) * Complex.I = 2 * Real.pi * Complex.I from rfl, Complex.exp_two_pi_mul_I,
    mul_one]

theorem absGal_re_one_add_pos (t : I) : 0 < (1 + absGalU t).re := by
  have := Complex.abs_re_le_norm (absGalU t); rw [norm_absGalU] at this
  rw [Complex.add_re, Complex.one_re]; linarith [abs_le.1 this]

theorem absGal_re_one_sub_pos (t : I) : 0 < (1 - absGalU t).re := by
  have := Complex.abs_re_le_norm (absGalU t); rw [norm_absGalU] at this
  rw [Complex.sub_re, Complex.one_re]; linarith [abs_le.1 this]

theorem absGal_one_add_ne (t : I) : 1 + absGalU t ≠ 0 := fun h => by
  have := absGal_re_one_add_pos t; rw [h, Complex.zero_re] at this; exact lt_irrefl _ this

theorem absGal_one_sub_ne (t : I) : 1 - absGalU t ≠ 0 := fun h => by
  have := absGal_re_one_sub_pos t; rw [h, Complex.zero_re] at this; exact lt_irrefl _ this

/-- `ω(t) = 1/2 - (1-u)²/(8u)`. -/
def absGalω (t : I) : ℂ := 1 / 2 - (1 - absGalU t) ^ 2 / (8 * absGalU t)

/-- `σ_ω = (1+u)/(1-u)`, a square root of `F ∘ ω`. -/
def absGalσω (t : I) : ℂ := (1 + absGalU t) / (1 - absGalU t)

theorem absGalF_ω (t : I) : absGalF (absGalω t) = absGalσω t ^ 2 := by
  have hu := absGalU_ne_zero t
  have h1 := absGal_one_sub_ne t
  rw [absGalF, absGalω, absGalσω, div_pow]
  rw [show (1 / 2 - (1 - absGalU t) ^ 2 / (8 * absGalU t) - 1 / 2 : ℂ) =
      -((1 - absGalU t) ^ 2 / (8 * absGalU t)) by ring]
  rw [show (1 / 2 - (1 - absGalU t) ^ 2 / (8 * absGalU t) - 1 : ℂ) =
      -((1 + absGalU t) ^ 2 / (8 * absGalU t)) by field_simp; ring]
  rw [neg_div_neg_eq]
  field_simp

theorem absGalG_σω (t : I) : absGalG (absGalσω t) = absGalU t := by
  have h1 := absGal_one_sub_ne t
  rw [absGalG, absGalσω]
  rw [div_sub_one h1, div_add_one h1, div_div_div_cancel_right₀ h1]
  rw [show 1 + absGalU t - (1 - absGalU t) = 2 * absGalU t by ring,
    show 1 + absGalU t + (1 - absGalU t) = 2 by ring]
  field_simp

theorem absGalσω_ne_one (t : I) : absGalσω t ≠ 1 := fun h => by
  have := absGalG_σω t; rw [h, absGalG] at this; simp at this; exact absGalU_ne_zero t this.symm

theorem absGalσω_ne_neg_one (t : I) : absGalσω t ≠ -1 := fun h => by
  rw [absGalσω, div_eq_iff (absGal_one_sub_ne t)] at h
  have := congrArg (· - absGalU t) h
  ring_nf at this; norm_num at this

theorem absGalσω_ne_zero (t : I) : absGalσω t ≠ 0 :=
  div_ne_zero (absGal_one_add_ne t) (absGal_one_sub_ne t)

theorem continuous_absGalσω : Continuous absGalσω :=
  (continuous_const.add continuous_absGalU).div (continuous_const.sub continuous_absGalU)
    absGal_one_sub_ne

theorem continuous_absGalω : Continuous absGalω :=
  continuous_const.sub (((continuous_const.sub continuous_absGalU).pow 2).div
    (continuous_const.mul continuous_absGalU) fun t => mul_ne_zero (by norm_num) (absGalU_ne_zero t))

theorem absGalω_not_mem (t : I) : absGalω t ∉ fibS := by
  intro h
  have hle : ‖absGalω t‖ ≤ 1 := by
    rcases h with h | ⟨n, hn⟩
    · rw [h, norm_zero]; norm_num
    · rw [← hn, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hu := norm_absGalU t
  have h1 : 19 / 20 ≤ ‖1 - absGalU t‖ := by
    have := norm_sub_norm_le (1 : ℂ) (absGalU t)
    rw [norm_one, hu] at this; linarith
  have h2 : ‖(1 - absGalU t) ^ 2 / (8 * absGalU t)‖ ≥ 2 := by
    rw [norm_div, norm_pow, norm_mul, hu, ge_iff_le, le_div_iff₀ (by norm_num)]
    norm_num
    nlinarith
  have h3 := norm_sub_norm_le ((1 - absGalU t) ^ 2 / (8 * absGalU t)) (1 / 2 : ℂ)
  have h4 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by norm_num)]
  have : ‖absGalω t‖ = ‖(1 - absGalU t) ^ 2 / (8 * absGalU t) - 1 / 2‖ := by
    rw [absGalω, ← norm_neg]; congr 1; ring
  rw [this] at hle
  rw [h4] at h3
  linarith

/-- `ω` as a loop of `ℂ ∖ S`. -/
def absGalωPath : Path (⟨absGalω 0, absGalω_not_mem 0⟩ : (fibSᶜ : Set ℂ)) ⟨absGalω 0, absGalω_not_mem 0⟩ where
  toFun t := ⟨absGalω t, absGalω_not_mem t⟩
  continuous_toFun := continuous_absGalω.subtype_mk _
  source' := rfl
  target' := by
    apply Subtype.ext
    show absGalω 1 = absGalω 0
    rw [absGalω, absGalω, absGalU_one]

/-- **The translation.** There is a deck transformation of `\widetilde{ℂ∖S}` fixing `sq` and
translating `Λ` by `± 2πi` (the loop `ω` around `1` and `1/2`). -/
theorem absGal_exists_translation : ∃ ψ : AbsU y₀ ≃ₜ AbsU y₀, (∀ c, absP y₀ (ψ c) = absP y₀ c) ∧
    (∀ c, absGalSq y₀ (ψ c) = absGalSq y₀ c) ∧
    ∃ m : ℂ, (m = 1 ∨ m = -1) ∧ ∀ c, absGalΛ y₀ (ψ c) = absGalΛ y₀ c + m * (2 * Real.pi * Complex.I) := by
  haveI : PathConnectedSpace (fibSᶜ : Set ℂ) :=
    isPathConnected_iff_pathConnectedSpace.1 isPathConnected_fibS_compl
  set ω0 : (fibSᶜ : Set ℂ) := ⟨absGalω 0, absGalω_not_mem 0⟩
  set c := PathConnectedSpace.somePath y₀ ω0
  set C := Path.Homotopic.Quotient.mk c
  set W := Path.Homotopic.Quotient.mk absGalωPath
  set x : AbsU y₀ := ⟨ω0, C⟩
  set L := UniversalCover.liftFrom C absGalωPath
  set g : AbsGamma y₀ := (FundamentalGroup.fromPath ((C.trans W).trans C.symm))⁻¹
  set ψ := (UniversalCover.deckHom g).1
  have hψ : ∀ c, absP y₀ (ψ c) = absP y₀ c := absP_deckHom y₀ g
  have hψx : ψ x = L 1 := by
    rw [Path.target, UniversalCover.deckHom_apply, inv_inv]
    show (⟨ω0, ((C.trans W).trans C.symm).trans C⟩ : AbsU y₀) = ⟨ω0, C.trans W⟩
    rw [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
      Path.Homotopic.Quotient.trans_refl]
  have hL0 : L 0 = x := L.source
  have hP : ∀ t, absP y₀ (L t) = absGalω t := fun t => rfl
  -- `ℓ` returns along `L`
  set A : I → ℂ := fun t => Complex.log (1 + absGalU t)
  set B : I → ℂ := fun t => Complex.log (1 - absGalU t)
  have hA : Continuous A := continuous_iff_continuousAt.2 fun t =>
    (continuous_const.add continuous_absGalU).continuousAt.clog
      (Complex.mem_slitPlane_iff.2 (Or.inl (absGal_re_one_add_pos t)))
  have hB : Continuous B := continuous_iff_continuousAt.2 fun t =>
    (continuous_const.sub continuous_absGalU).continuousAt.clog
      (Complex.mem_slitPlane_iff.2 (Or.inl (absGal_re_one_sub_pos t)))
  have hℓ : absGalℓ y₀ (L 1) = absGalℓ y₀ (L 0) := by
    have := absGal_expLift_eq (((hA.add hA).sub hB).sub hB)
      ((absGalℓ y₀).continuous.comp L.continuous) (fun t => by
        simp only [comp_apply, Pi.add_apply]
        rw [absGalℓ_spec, hP, absGalF_ω, Complex.exp_sub, Complex.exp_sub, Complex.exp_add,
          Complex.exp_log (absGal_one_add_ne t), Complex.exp_log (absGal_one_sub_ne t), absGalσω,
          div_pow]
        have := absGal_one_sub_ne t
        field_simp) 0 1
    simp only [comp_apply, Pi.add_apply, A, B] at this
    rw [this, absGalU_one]; ring
  have hsign : absGalSign ψ = 1 := by
    have e := absGalℓ_deck ψ hψ x
    rw [hψx, ← hL0, hℓ] at e
    rw [absGalSign, show absGalℓ y₀ (ψ (UniversalCover.base y₀)) - absGalℓ y₀ (UniversalCover.base y₀) = 0 by
      linear_combination -e, zero_div, Complex.exp_zero]
  have hsqeq : absGalSq y₀ (L 1) = absGalSq y₀ (L 0) := by rw [absGalSq, absGalSq, hℓ]
  -- `Λ` is translated along `L`
  set r : I → ℂ := fun t => absGalSq y₀ (L t) / absGalσω t
  have hr : ∀ t, r t = 1 ∨ r t = -1 := fun t => by
    have : r t * r t = 1 := by
      simp only [r]
      rw [← sq, div_pow, absGalSq_sq, hP, absGalF_ω, div_self (pow_ne_zero 2 (absGalσω_ne_zero t))]
    exact mul_self_eq_one_iff.1 this
  have hrc : Continuous r :=
    ((continuous_absGalSq y₀).comp L.continuous).div continuous_absGalσω absGalσω_ne_zero
  set a : I → ℂ := fun t => Complex.log (1 / 20) + 2 * Real.pi * Complex.I * (t : ℝ)
  have ha : Continuous a := by fun_prop
  have hea : ∀ t, Complex.exp (a t) = absGalG (absGalσω t) := fun t => by
    rw [absGalG_σω, Complex.exp_add, Complex.exp_log (by norm_num), absGalU]
  have hΛ : absGalΛ y₀ (L 1) = absGalΛ y₀ (L 0) + r 0 * (2 * Real.pi * Complex.I) := by
    have := absGal_expLift_eq (hrc.mul ha) ((absGalΛ y₀).continuous.comp L.continuous)
      (fun t => by
        simp only [comp_apply, Pi.mul_apply]
        rw [absGal_exp_mul_of (hea t) (absGalσω_ne_one t) (absGalσω_ne_neg_one t) (hr t),
          absGalΛ_spec]
        congr 1
        exact div_mul_cancel₀ _ (absGalσω_ne_zero t)) 0 1
    simp only [comp_apply, Pi.mul_apply] at this
    have h01 : r 1 = r 0 := by simp only [r, hsqeq, absGalσω, absGalU_one]
    rw [this, h01]
    simp only [a, Set.Icc.coe_one, Set.Icc.coe_zero, Complex.ofReal_one, Complex.ofReal_zero]
    ring
  refine ⟨ψ, hψ, fun c => by rw [absGalSq_deck ψ hψ, hsign, one_mul], r 0, hr 0, fun c => ?_⟩
  rw [absGalΛ_deck_even ψ hψ hsign]
  have e := absGalΛ_deck_even ψ hψ hsign x
  rw [hψx, ← hL0, hΛ] at e
  linear_combination -e

/-! The disc `D = D₅` around `0` (radius `2/11`) lies in `absGalR`: there `F` is within `3/5` of
`2`. On `p⁻¹(D)` the invariant `Θ = (Λ - (sq/σ)·g)/(2πi)` is a locally constant integer. -/

theorem absGal_norm_lt_of_mem_fibD5 {z : ℂ} (hz : z ∈ fibD 5) : ‖z‖ < 2 / 11 := by
  rw [fibD, Metric.mem_ball, dist_zero_right] at hz
  convert hz using 1; norm_num

theorem absGalF_near_two {z : ℂ} (hz : z ∈ fibD 5) : ‖absGalF z - 2‖ < 3 / 5 := by
  have h := absGal_norm_lt_of_mem_fibD5 hz
  have h4 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by norm_num)]
  have h1 : 7 / 22 < ‖z - 1 / 2‖ := by
    have := norm_sub_norm_le (1 / 2 : ℂ) z
    rw [h4, norm_sub_rev] at this; linarith
  have hne : z - 1 / 2 ≠ 0 := fun h0 => by rw [h0, norm_zero] at h1; norm_num at h1
  have e : absGalF z - 2 = -z / (z - 1 / 2) := by
    rw [absGalF, eq_div_iff hne, sub_mul, div_mul_cancel₀ _ hne]; ring
  rw [e, norm_div, norm_neg, div_lt_iff₀ (by linarith)]
  nlinarith

theorem absGal_re_F_gt {z : ℂ} (hz : z ∈ fibD 5) : 7 / 5 < (absGalF z).re := by
  have h := absGalF_near_two hz
  have := Complex.abs_re_le_norm (absGalF z - 2)
  rw [Complex.sub_re] at this
  norm_num at this
  linarith [abs_lt.1 (this.trans_lt h)]

/-- Where `Re F > 1`, both `F` and `G ∘ σ` lie in the slit plane. -/
theorem absGal_mem_R_of_one_lt_re {z : ℂ} (hre : 1 < (absGalF z).re) : z ∈ absGalR := by
  have hF : absGalF z ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.2 (Or.inl (by linarith))
  refine ⟨hF, ?_⟩
  have hF0 := Complex.slitPlane_ne_zero hF
  rw [Complex.mem_slitPlane_iff]
  by_contra hcon
  push Not at hcon
  obtain ⟨hre', him'⟩ := hcon
  set s := absGalσ z
  set w := absGalG s
  have hs1 := absGalσ_ne_one hF0
  have hs2 := absGalσ_ne_neg_one hF0
  have hsp : s + 1 ≠ 0 := fun h => hs2 (eq_neg_of_add_eq_zero_left h)
  have hw : w = (w.re : ℂ) := Complex.ext (by simp) (by simp [him'])
  have hw1 : (1 : ℂ) - w ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hsw : s = (1 + w) / (1 - w) := by
    rw [eq_div_iff hw1]
    have : w * (s + 1) = s - 1 := by simp only [w, absGalG]; field_simp
    linear_combination -this
  have hsq : s ^ 2 = absGalF z := absGalσ_sq hF0
  rw [hsw, hw] at hsq
  have hden : (1 : ℝ) - w.re ≠ 0 := by linarith
  have hreal : ((1 + (w.re : ℂ)) / (1 - (w.re : ℂ))) ^ 2 = (((1 + w.re) / (1 - w.re)) ^ 2 : ℝ) := by
    push_cast; ring
  rw [hreal] at hsq
  have hle : ((1 + w.re) / (1 - w.re)) ^ 2 ≤ 1 := by
    rw [div_pow, div_le_one (by positivity)]
    nlinarith
  have := congrArg Complex.re hsq
  rw [Complex.ofReal_re] at this
  linarith

/-- `D₅ ⊆ absGalR`. -/
theorem absGal_fibD5_subset {z : ℂ} (hz : z ∈ fibD 5) : z ∈ absGalR :=
  absGal_mem_R_of_one_lt_re (by linarith [absGal_re_F_gt hz])

/-- The invariant `Θ = (Λ - (sq/σ)·g)/(2πi)`, an integer over `D₅`. -/
def absGalΘ (c : AbsU y₀) : ℂ :=
  (absGalΛ y₀ c - absGalSq y₀ c / absGalσ (absP y₀ c) * absGalLog (absP y₀ c)) /
    (2 * Real.pi * Complex.I)

theorem absGal_two_pi_I_ne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
  simp [Real.pi_ne_zero, Complex.I_ne_zero]

theorem absGalΘ_int {c : AbsU y₀} (hc : absP y₀ c ∈ absGalR) : ∃ n : ℤ, absGalΘ y₀ c = n := by
  have hr := absGal_ratio_sq (absGalSq_sq y₀ c) (absGalF_ne_zero_of_mem hc)
  have h := absGal_exp_mul_log hc hr
  rw [div_mul_cancel₀ _ (absGalσ_ne_zero _), ← absGalΛ_spec] at h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 (by rw [Complex.exp_sub, h, div_self (Complex.exp_ne_zero _)] :
    Complex.exp (absGalΛ y₀ c - absGalSq y₀ c / absGalσ (absP y₀ c) * absGalLog (absP y₀ c)) = 1)
  refine ⟨n, ?_⟩
  rw [absGalΘ, hn, mul_div_cancel_right₀ _ absGal_two_pi_I_ne]

theorem absGalΘ_continuousAt {c : AbsU y₀} (hc : absP y₀ c ∈ absGalR) : ContinuousAt (absGalΘ y₀) c := by
  have hσ : ContinuousAt (fun c => absGalσ (absP y₀ c)) c :=
    (continuousAt_absGalσ hc).comp (continuous_absP y₀).continuousAt
  have hg : ContinuousAt (fun c => absGalLog (absP y₀ c)) c :=
    (continuousAt_absGalLog hc).comp (continuous_absP y₀).continuousAt
  exact (((absGalΛ y₀).continuous.continuousAt.sub
    (((continuous_absGalSq y₀).continuousAt.div hσ (absGalσ_ne_zero _)).mul hg))).div_const _

/-- `Θ` is locally constant over `D₅`. -/
theorem absGalΘ_eventually_eq {c₀ : AbsU y₀} (hc₀ : absP y₀ c₀ ∈ fibD 5) :
    ∀ᶠ c in 𝓝 c₀, absP y₀ c ∈ fibD 5 ∧ absGalΘ y₀ c = absGalΘ y₀ c₀ := by
  obtain ⟨n₀, hn₀⟩ := absGalΘ_int y₀ (absGal_fibD5_subset hc₀)
  have hD : ∀ᶠ c in 𝓝 c₀, absP y₀ c ∈ fibD 5 :=
    (continuous_absP y₀).continuousAt.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds hc₀)
  have hcl : ∀ᶠ c in 𝓝 c₀, ‖absGalΘ y₀ c - absGalΘ y₀ c₀‖ < 1 / 2 := by
    have := (absGalΘ_continuousAt y₀ (absGal_fibD5_subset hc₀)).sub
      (continuousAt_const (y := absGalΘ y₀ c₀))
    have h2 := this.tendsto
    simp only [sub_self] at h2
    exact (h2.eventually (Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2))).mono
      fun c hc => by rwa [dist_zero_right] at hc
  filter_upwards [hD, hcl] with c hc hcl
  refine ⟨hc, ?_⟩
  obtain ⟨n, hn⟩ := absGalΘ_int y₀ (absGal_fibD5_subset hc)
  rw [hn, hn₀] at hcl ⊢
  have : ‖((n - n₀ : ℤ) : ℂ)‖ < 1 / 2 := by push_cast; exact hcl
  rw [Complex.norm_intCast] at this
  have h' : |((n - n₀ : ℤ) : ℝ)| < 1 := by linarith
  rw [← Int.cast_abs] at h'
  have : |n - n₀| < 1 := by exact_mod_cast h'
  have : n - n₀ = 0 := Int.abs_lt_one_iff.mp this
  rw [show n = n₀ by omega]

theorem absGalΘ_fix {φ : AbsU y₀ ≃ₜ AbsU y₀} (hφ : ∀ c, absP y₀ (φ c) = absP y₀ c)
    (hfix : AbsGalFix y₀ φ) (c : AbsU y₀) : absGalΘ y₀ (φ c) = absGalΘ y₀ c := by
  rw [absGalΘ, absGalΘ, hfix.1, hfix.2, hφ]

theorem absGalΘ_translate {ψ : AbsU y₀ ≃ₜ AbsU y₀} (hψ : ∀ c, absP y₀ (ψ c) = absP y₀ c)
    (hsq : ∀ c, absGalSq y₀ (ψ c) = absGalSq y₀ c) {m : ℂ}
    (hm : ∀ c, absGalΛ y₀ (ψ c) = absGalΛ y₀ c + m * (2 * Real.pi * Complex.I)) (c : AbsU y₀) :
    absGalΘ y₀ (ψ c) = absGalΘ y₀ c + m := by
  rw [absGalΘ, absGalΘ, hsq, hm, hψ]
  field_simp [absGal_two_pi_I_ne]
  ring

theorem absGalΘ_iterate {ψ : AbsU y₀ ≃ₜ AbsU y₀} (hψ : ∀ c, absP y₀ (ψ c) = absP y₀ c)
    (hsq : ∀ c, absGalSq y₀ (ψ c) = absGalSq y₀ c) {m : ℂ}
    (hm : ∀ c, absGalΛ y₀ (ψ c) = absGalΛ y₀ c + m * (2 * Real.pi * Complex.I)) (k : ℕ)
    (c : AbsU y₀) : absGalΘ y₀ (ψ^[k] c) = absGalΘ y₀ c + k * m := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', absGalΘ_translate y₀ hψ hsq hm, ih]; push_cast; ring

theorem absP_iterate {ψ : AbsU y₀ ≃ₜ AbsU y₀} (hψ : ∀ c, absP y₀ (ψ c) = absP y₀ c) (k : ℕ)
    (c : AbsU y₀) : absP y₀ (ψ^[k] c) = absP y₀ c := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', hψ, ih]

/-- `Γ₂` acts trivially on `(sq, Λ)` when `γ₀`, `γ₁` wind oddly around `{1, 1/2}` (as the simple
loops around `1` and `1/2` do) and the other `γₙ` lie in `absGalR`. -/
theorem absGal_gamma2_le (γ : ℕ → Path y₀ y₀)
    (h0 : windAt y₀ _ (fibPt_mem 0) (γ 0) - windAt y₀ _ (fibPt_mem 1) (γ 0) = 1 ∨
      windAt y₀ _ (fibPt_mem 0) (γ 0) - windAt y₀ _ (fibPt_mem 1) (γ 0) = -1)
    (h1 : windAt y₀ _ (fibPt_mem 0) (γ 1) - windAt y₀ _ (fibPt_mem 1) (γ 1) = 1 ∨
      windAt y₀ _ (fibPt_mem 0) (γ 1) - windAt y₀ _ (fibPt_mem 1) (γ 1) = -1)
    (hR : ∀ n, 2 ≤ n → ∀ t, ((γ n t : (fibSᶜ : Set ℂ)) : ℂ) ∈ absGalR) :
    gamma2 y₀ (fun n => FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (γ n))) ≤
      absGalN y₀ := by
  refine Subgroup.normalClosure_le_normal ?_
  rintro _ ⟨n, rfl⟩
  rcases n with _ | _ | n
  · exact absGal_sq_mem_of_odd y₀ (absGalSign_of_wind y₀ _ h0)
  · exact absGal_sq_mem_of_odd y₀ (absGalSign_of_wind y₀ _ h1)
  · exact pow_mem (absGal_mem_N_of_mem_R y₀ _ (hR _ (by omega))) 2

section Quot

variable {y₀} {g : ℕ → AbsGamma y₀} (hle : gamma2 y₀ g ≤ absGalN y₀)

include hle in
theorem absGal_fix_of_mem {φ : AbsU y₀ ≃ₜ AbsU y₀} (hφ : φ ∈ gamma2Homeo y₀ g) :
    AbsGalFix y₀ φ ∧ ∀ c, absP y₀ (φ c) = absP y₀ c := by
  obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.1 hφ
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hd
  exact ⟨hle hx, absP_deckHom y₀ x⟩

/-- `Θ` on `Γ₂ \ \widetilde{ℂ∖S}`. -/
def absGalΘbar : AbsGalOrdY₂ y₀ g → ℂ :=
  Quotient.lift (absGalΘ y₀) fun a b ⟨_, hφ, h⟩ => by
    obtain ⟨hfix, hP⟩ := absGal_fix_of_mem hle hφ
    rw [← h, absGalΘ_fix y₀ hP hfix]

theorem absGal_ordY₂Proj_mk (c : AbsU y₀) :
    ordY₂Proj y₀ g (homeoQuotientMk _ c) = absP y₀ c := rfl

theorem absGalΘbar_mk (c : AbsU y₀) : absGalΘbar hle (homeoQuotientMk _ c) = absGalΘ y₀ c := rfl

theorem absGal_isOpen_level (n : ℂ) :
    IsOpen {x : AbsGalOrdY₂ y₀ g | ordY₂Proj y₀ g x ∈ fibD 5 ∧ absGalΘbar hle x = n} := by
  rw [← isQuotientMap_quotient_mk'.isOpen_preimage, isOpen_iff_mem_nhds]
  intro c ⟨hc, hn⟩
  filter_upwards [absGalΘ_eventually_eq y₀ hc] with c' ⟨h1, h2⟩
  exact ⟨h1, h2.trans hn⟩

theorem absGalΘbar_int {x : AbsGalOrdY₂ y₀ g} (hx : ordY₂Proj y₀ g x ∈ fibD 5) :
    ∃ n : ℤ, absGalΘbar hle x = n := by
  induction x using Quotient.inductionOn with
  | h c => exact absGalΘ_int y₀ (absGal_fibD5_subset hx)

/-- `Θ` is constant on the components of the preimage of `D₅` in `Γ₂ \ \widetilde{ℂ∖S}`. -/
theorem absGalΘbar_eq_of_mem {x x' : AbsGalOrdY₂ y₀ g} (hx : ordY₂Proj y₀ g x ∈ fibD 5)
    (hx' : x' ∈ connectedComponentIn (ordY₂Proj y₀ g ⁻¹' fibD 5) x) :
    absGalΘbar hle x' = absGalΘbar hle x := by
  obtain ⟨n, hn⟩ := absGalΘbar_int hle hx
  have hsub := GX.IsPreconnected.subset_of_pairwise_disjoint
    (T := fun n : ℤ => {x : AbsGalOrdY₂ y₀ g | ordY₂Proj y₀ g x ∈ fibD 5 ∧ absGalΘbar hle x = n})
    (fun n => absGal_isOpen_level hle _) (fun i j hij => by
      rw [Function.onFun, Set.disjoint_left]
      rintro y ⟨-, hi⟩ ⟨-, hj⟩
      exact hij (Int.cast_injective (hi.symm.trans hj)))
    isPreconnected_connectedComponentIn (fun y hy => by
      have hy' : ordY₂Proj y₀ g y ∈ fibD 5 :=
        (connectedComponentIn_subset (ordY₂Proj y₀ g ⁻¹' fibD 5) x) hy
      obtain ⟨m, hm⟩ := absGalΘbar_int hle hy'
      exact mem_iUnion.2 ⟨m, hy', hm⟩) (j := n)
      ⟨x, mem_connectedComponentIn (show x ∈ ordY₂Proj y₀ g ⁻¹' fibD 5 from hx), hx, hn⟩
  exact (hsub hx').2.trans hn.symm

end Quot

/-! The rays: the points `w j` of `\widetilde{ℂ∖S}` over `fibQ j`, joined by lifts of vertical
segments inside `D_j`. -/

theorem absGal_pathConnected : PathConnectedSpace (fibSᶜ : Set ℂ) :=
  isPathConnected_iff_pathConnectedSpace.1 isPathConnected_fibS_compl

attribute [local instance] absGal_pathConnected

/-- `fibQ j` as a point of `ℂ ∖ S`. -/
def absGalQ (j : ℕ) : (fibSᶜ : Set ℂ) := ⟨fibQ j, (fibQ_mem j).2⟩

/-- The height of `fibQ j`. -/
def absGalA (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1 / 2) / 2

theorem absGalA_pos (j : ℕ) : 0 < absGalA j := by unfold absGalA; positivity

theorem absGalA_succ_le (j : ℕ) : absGalA (j + 1) ≤ absGalA j := by
  unfold absGalA
  gcongr
  linarith

/-- The height along the vertical segment from `fibQ j` to `fibQ (j+1)`. -/
def absGalH (j : ℕ) (t : I) : ℝ := (1 - (t : ℝ)) * absGalA j + (t : ℝ) * absGalA (j + 1)

theorem absGalH_pos (j : ℕ) (t : I) : 0 < absGalH j t := by
  have h := absGalA_succ_le j
  have hb := absGalA_pos (j + 1)
  unfold absGalH
  nlinarith [mul_le_mul_of_nonneg_left h (sub_nonneg.2 t.2.2), t.2.1]

theorem absGalH_le (j : ℕ) (t : I) : absGalH j t ≤ absGalA j := by
  have h := absGalA_succ_le j
  unfold absGalH
  nlinarith [mul_le_mul_of_nonneg_left h t.2.1]

theorem absGalH_mem (j : ℕ) (t : I) : ((absGalH j t : ℝ) : ℂ) * Complex.I ∈ fibD j ∩ fibSᶜ := by
  refine ⟨?_, not_mem_fibS_of_im_ne_zero ?_⟩
  · rw [fibD, Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_of_nonneg (absGalH_pos j t).le]
    have := absGalH_le j t
    have h2 := absGalA_pos j
    unfold absGalA at this h2
    linarith
  · rw [Complex.mul_I_im, Complex.ofReal_re]; exact (absGalH_pos j t).ne'

/-- The vertical segment from `fibQ j` to `fibQ (j+1)`, in `D_j ∖ S`. -/
def absGalSeg (j : ℕ) : Path (absGalQ j) (absGalQ (j + 1)) where
  toFun t := ⟨((absGalH j t : ℝ) : ℂ) * Complex.I, (absGalH_mem j t).2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    unfold absGalH; fun_prop
  source' := by
    apply Subtype.ext
    simp [absGalH, absGalQ, fibQ, absGalA]
  target' := by
    apply Subtype.ext
    simp [absGalH, absGalQ, fibQ, absGalA]

/-- The classes of the points `w j`. -/
def absGalWCls : (j : ℕ) → Path.Homotopic.Quotient y₀ (absGalQ j)
  | 0 => Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath y₀ (absGalQ 0))
  | j + 1 => (absGalWCls j).trans (Path.Homotopic.Quotient.mk (absGalSeg j))

/-- The point `w j` of `\widetilde{ℂ∖S}` over `fibQ j`. -/
def absGalW (j : ℕ) : AbsU y₀ := ⟨absGalQ j, absGalWCls y₀ j⟩

theorem absP_absGalW (j : ℕ) : absP y₀ (absGalW y₀ j) = fibQ j := rfl

section Thread

variable {y₀} {g : ℕ → AbsGamma y₀} (ψ : AbsU y₀ ≃ₜ AbsU y₀) (hψ : ∀ c, absP y₀ (ψ c) = absP y₀ c)

/-- The image in `Γ₂ \ \widetilde{ℂ∖S}` of `ψᵏ (w j)`. -/
def absGalPt (k j : ℕ) : AbsGalOrdY₂ y₀ g := homeoQuotientMk _ (ψ^[k] (absGalW y₀ j))

/-- The component of the preimage of `D_j` containing `ψᵏ (w j)`. -/
def absGalComp (k j : ℕ) : Set (AbsGalOrdY₂ y₀ g) :=
  connectedComponentIn (ordY₂Proj y₀ g ⁻¹' fibD j) (absGalPt (g := g) ψ k j)

include hψ in
theorem absGalPt_mem_fibD (k j : ℕ) : ordY₂Proj y₀ g (absGalPt (g := g) ψ k j) ∈ fibD j := by
  show absP y₀ (ψ^[k] (absGalW y₀ j)) ∈ fibD j
  rw [absP_iterate y₀ hψ]; exact (fibQ_mem j).1

include hψ in
theorem absGalPt_succ_mem (k j : ℕ) : absGalPt (g := g) ψ k (j + 1) ∈ absGalComp (g := g) ψ k j := by
  set L := UniversalCover.liftFrom (absGalWCls y₀ j) (absGalSeg j)
  let f : I → AbsGalOrdY₂ y₀ g := fun t => homeoQuotientMk _ (ψ^[k] (L t))
  have hf : Continuous f := continuous_quotient_mk'.comp ((ψ.continuous.iterate k).comp L.continuous)
  have hrange : range f ⊆ ordY₂Proj y₀ g ⁻¹' fibD j := by
    rintro _ ⟨t, rfl⟩
    show absP y₀ (ψ^[k] (L t)) ∈ fibD j
    rw [absP_iterate y₀ hψ]; exact (absGalH_mem j t).1
  have h0 : f 0 = absGalPt (g := g) ψ k j := by
    show homeoQuotientMk _ (ψ^[k] (L 0)) = _
    rw [L.source]; rfl
  have h1 : f 1 = absGalPt (g := g) ψ k (j + 1) := by
    show homeoQuotientMk _ (ψ^[k] (L 1)) = _
    rw [L.target]; rfl
  have := (isPreconnected_range hf).subset_connectedComponentIn ⟨0, rfl⟩ hrange
  rw [h0] at this
  exact this ⟨1, h1⟩

include hψ in
theorem absGalComp_succ_subset (k j : ℕ) :
    absGalComp (g := g) ψ k (j + 1) ⊆ absGalComp (g := g) ψ k j := by
  unfold absGalComp
  rw [connectedComponentIn_eq (absGalPt_succ_mem ψ hψ k j)]
  exact connectedComponentIn_mono _ (preimage_mono (fibD_succ_subset j))

include hψ in
theorem absGalComp_antitone (k : ℕ) {n m : ℕ} (h : n ≤ m) :
    absGalComp (g := g) ψ k m ⊆ absGalComp (g := g) ψ k n := by
  induction m, h using Nat.le_induction with
  | base => exact subset_rfl
  | succ m _ ih => exact (absGalComp_succ_subset ψ hψ k m).trans ih

/-- The index of a member of the basis `{D_j}`. -/
def absGalIdx (U : range fibD) : ℕ := (Set.mem_range.1 U.2).choose

theorem absGalIdx_spec (U : range fibD) : fibD (absGalIdx U) = U := (Set.mem_range.1 U.2).choose_spec

/-- The thread `j ↦ absGalComp k j` over the basis `{D_j}`. -/
def absGalThread (k : ℕ) : FiberThread (ordY₂Proj y₀ g) (range fibD) where
  toFun U := absGalComp (g := g) ψ k (absGalIdx U)
  isCompOf U := by
    have hU := absGalIdx_spec U
    refine ⟨absGalPt (g := g) ψ k (absGalIdx U), hU ▸ absGalPt_mem_fibD ψ hψ k _, ?_⟩
    simp only [absGalComp]; rw [hU]
  mono U V hUV := by
    have hU := absGalIdx_spec U
    have hV := absGalIdx_spec V
    rw [← hU, ← hV, fibD_subset_iff] at hUV
    exact absGalComp_antitone ψ hψ k hUV

theorem absGal_h𝓤 : ∀ U ∈ range fibD, IsCNbhd (0 : ℂ) U := by
  rintro _ ⟨j, rfl⟩; exact isCNbhd_fibD j

/-- The end over `0` defined by the thread. -/
def absGalEnd (k : ℕ) : SpreadEnd (ordY₂Proj y₀ g) :=
  (absGalThread ψ hψ k).toEnd absGal_h𝓤 fibD_basis

theorem absGalEnd_base (k : ℕ) : (absGalEnd (g := g) ψ hψ k).base = 0 := rfl

theorem absGalEnd_apply (k : ℕ) :
    absGalEnd (g := g) ψ hψ k (fibD 5) = absGalComp (g := g) ψ k 5 := by
  have := FiberThread.toEnd_apply absGal_h𝓤 fibD_basis (absGalThread (g := g) ψ hψ k)
    ⟨fibD 5, 5, rfl⟩
  rw [absGalEnd, this]
  show absGalComp ψ k (absGalIdx ⟨fibD 5, 5, rfl⟩) = _
  rw [fibD_injective (absGalIdx_spec ⟨fibD 5, 5, rfl⟩)]

end Thread

/-- **`ex:consider_denote_absolute_galois`, the fibre claim, refuted** (finding): with `Γ₂` the
normal closure of the `[γₙ]²` (DEC-58), for loops `γ₀`, `γ₁` winding (oddly) around `1` and `1/2`
respectively — as the simple loops around `1` and `1/2` do — and loops `γₙ`, `n ≥ 2`, lying in
the region `absGalR` (the complement of the closed disc of diameter `[1/2, 1]` and of the ray
`[1, ∞)`, where the simple loops around the points `1/(n+1)`, `n ≥ 2`, can be drawn), the fibre
above `0` of `Y₂` is NOT compact. Ends over `0` through the infinitely many components of the
preimage of `D₅` distinguished by the dihedral invariant `Θ`. -/
theorem absGal_Y₂_fiber_not_compact (γ : ℕ → Path y₀ y₀)
    (h0 : windAt y₀ _ (fibPt_mem 0) (γ 0) - windAt y₀ _ (fibPt_mem 1) (γ 0) = 1 ∨
      windAt y₀ _ (fibPt_mem 0) (γ 0) - windAt y₀ _ (fibPt_mem 1) (γ 0) = -1)
    (h1 : windAt y₀ _ (fibPt_mem 0) (γ 1) - windAt y₀ _ (fibPt_mem 1) (γ 1) = 1 ∨
      windAt y₀ _ (fibPt_mem 0) (γ 1) - windAt y₀ _ (fibPt_mem 1) (γ 1) = -1)
    (hR : ∀ n, 2 ≤ n → ∀ t, ((γ n t : (fibSᶜ : Set ℂ)) : ℂ) ∈ absGalR) :
    ¬ IsCompact (y₂Fiber0 y₀ fun n => FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (γ n))) := by
  set g := fun n => FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (γ n))
  have hle := absGal_gamma2_le y₀ γ h0 h1 hR
  obtain ⟨ψ, hψ, hsq, m, hm, hΛ⟩ := absGal_exists_translation y₀
  intro hK
  set q := ordY₂Proj y₀ g
  have hW : IsCNbhd (0 : ℂ) (fibD 5) := isCNbhd_fibD 5
  let ι := {C : Set (AbsGalOrdY₂ y₀ g) // IsCompOf q (fibD 5) C}
  let U : ι → Set (AbsGalY₂ y₀ g) := fun C => SpreadEnd.basicSet q (fibD 5) C.1
  have hUo : ∀ C, IsOpen (U C) := fun C => SpreadEnd.isOpen_basicSet Metric.isOpen_ball _
  have hcov : y₂Fiber0 y₀ g ⊆ ⋃ C, U C := by
    intro e he
    have hb : e.base = 0 := he
    have hW' : IsCNbhd e.base (fibD 5) := hb ▸ hW
    exact mem_iUnion.2 ⟨⟨e (fibD 5), e.isCompOf _ hW'⟩, SpreadEnd.mem_basicSet_self e hW'⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hUo hcov
  have hmem : ∀ k : ℕ, ∃ C ∈ t, absGalEnd (g := g) ψ hψ k ∈ U C := fun k => by
    have := ht (show absGalEnd (g := g) ψ hψ k ∈ y₂Fiber0 y₀ g from absGalEnd_base ψ hψ k)
    simpa using this
  choose f hft hfU using hmem
  have hfeq : ∀ k, absGalComp (g := g) ψ k 5 = (f k).1 := fun k => by
    rw [← absGalEnd_apply ψ hψ k]
    exact (SpreadEnd.mem_basicSet_iff (f k).2 (by rw [absGalEnd_base]; exact hW)).1 (hfU k)
  have hval : ∀ k, absGalΘbar hle (absGalPt (g := g) ψ k 5) =
      absGalΘ y₀ (absGalW y₀ 5) + k * m := fun k =>
    absGalΘ_iterate y₀ hψ hsq hΛ k _
  have hinj : Injective fun k : ℕ => (⟨f k, hft k⟩ : t) := by
    intro k k' hkk
    have hC : absGalComp (g := g) ψ k 5 = absGalComp (g := g) ψ k' 5 := by
      rw [hfeq, hfeq]; exact congrArg (fun C : t => C.1.1) hkk
    have hx' : absGalPt (g := g) ψ k' 5 ∈ absGalComp (g := g) ψ k 5 := by
      rw [hC]; exact mem_connectedComponentIn (absGalPt_mem_fibD ψ hψ k' 5)
    have := absGalΘbar_eq_of_mem hle (absGalPt_mem_fibD ψ hψ k 5) hx'
    rw [hval, hval] at this
    have hm0 : m ≠ 0 := by rcases hm with rfl | rfl <;> norm_num
    have : (k' : ℂ) = k := by
      have := add_left_cancel this
      exact mul_right_cancel₀ hm0 this
    exact_mod_cast this.symm
  haveI := Finite.of_injective _ hinj
  exact not_finite ℕ

/-- `ex:consider_denote_absolute_galois`, the fibre claim, refuted in the paper's terms: if the
`γₙ` wind once around `1/(n+1)` and not around the other points of `S` (the paper's simple loops)
and, for `n ≥ 2`, lie in `absGalR`, the fibre above `0` of `Y₂` is not compact. -/
theorem absGal_Y₂_fiber_not_compact_of_simple (γ : ℕ → Path y₀ y₀)
    (hγ : ∀ n m, windAt y₀ _ (fibPt_mem m) (γ n) = if n = m then 1 else 0)
    (hR : ∀ n, 2 ≤ n → ∀ t, ((γ n t : (fibSᶜ : Set ℂ)) : ℂ) ∈ absGalR) :
    ¬ IsCompact (y₂Fiber0 y₀ fun n => FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (γ n))) :=
  absGal_Y₂_fiber_not_compact y₀ γ (Or.inl (by rw [hγ 0 0, hγ 0 1]; norm_num))
    (Or.inr (by rw [hγ 1 0, hγ 1 1]; norm_num)) hR

/-- `ex:consider_denote_absolute_galois`, the fibre claim as printed: the fibre above `0` of `Y₂`
is not a Cantor set (a Cantor set is compact). -/
theorem absGal_Y₂_fiber_not_cantor (γ : ℕ → Path y₀ y₀)
    (hγ : ∀ n m, windAt y₀ _ (fibPt_mem m) (γ n) = if n = m then 1 else 0)
    (hR : ∀ n, 2 ≤ n → ∀ t, ((γ n t : (fibSᶜ : Set ℂ)) : ℂ) ∈ absGalR) :
    IsEmpty ((y₂Fiber0 y₀ fun n => FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (γ n))) ≃ₜ
      cantorSet) := by
  refine ⟨fun e => absGal_Y₂_fiber_not_compact_of_simple y₀ γ hγ hR ?_⟩
  haveI : CompactSpace cantorSet := isCompact_iff_compactSpace.1 isCompact_cantorSet
  haveI := e.symm.compactSpace
  exact isCompact_iff_compactSpace.2 this

/-! #### The strongest true form of the fibre claim -/

/-- The quotient of a spread by a group of homeomorphisms over the base is a spread. -/
theorem isSpread_homeoQuotient_lift {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [LocallyConnectedSpace X] {H : Subgroup (X ≃ₜ X)} {p : X → Y} (hp : IsSpread p)
    (hH : ∀ φ ∈ H, ∀ x, p (φ x) = p x) :
    IsSpread (Quotient.lift (s := subgroupOrbitSetoid H) p fun a _ ⟨φ, hφ, h⟩ => h ▸ (hH φ hφ a).symm) := by
  set q : HomeoQuotient H → Y := Quotient.lift (s := subgroupOrbitSetoid H) p
    fun a b ⟨φ, hφ, h⟩ => h ▸ (hH φ hφ a).symm with hqdef
  have hπc : Continuous (homeoQuotientMk H) := continuous_quotient_mk'
  have hqc : Continuous q := continuous_quot_lift _ hp.continuous
  have hπo : IsOpenMap (homeoQuotientMk H) := by
    intro O hO
    rw [← isQuotientMap_quotient_mk'.isOpen_preimage]
    show IsOpen (homeoQuotientMk H ⁻¹' (homeoQuotientMk H '' O))
    have : homeoQuotientMk H ⁻¹' (homeoQuotientMk H '' O) =
        ⋃ φ : H, (φ : X ≃ₜ X) '' O := by
      ext x; constructor
      · rintro ⟨y, hy, hxy⟩
        obtain ⟨φ, hφ, h⟩ := Quotient.exact hxy
        exact mem_iUnion.2 ⟨⟨φ, hφ⟩, y, hy, h⟩
      · intro hx
        obtain ⟨⟨φ, hφ⟩, y, hy, rfl⟩ := mem_iUnion.1 hx
        exact ⟨y, hy, Quotient.sound (show ∃ ψ ∈ H, ψ y = φ y from ⟨φ, hφ, rfl⟩)⟩
    rw [this]
    exact isOpen_iUnion fun φ => (φ : X ≃ₜ X).isOpenMap _ hO
  have key : ∀ U : Set Y, IsOpen U → ∀ x : X, p x ∈ U →
      connectedComponentIn (q ⁻¹' U) (homeoQuotientMk H x) =
        homeoQuotientMk H '' connectedComponentIn (p ⁻¹' U) x := by
    intro U hU x hx
    have hpU : IsOpen (p ⁻¹' U) := hU.preimage hp.continuous
    let T : X → Set (HomeoQuotient H) := fun y =>
      homeoQuotientMk H '' connectedComponentIn (p ⁻¹' U) y
    have hT : ∀ y, IsOpen (T y) := fun y => hπo _ hpU.connectedComponentIn
    have hdisj : ∀ y y', (T y ∩ T y').Nonempty → T y' = T y := by
      rintro y y' ⟨z, ⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩
      obtain ⟨φ, hφ, hφb⟩ := Quotient.exact hab
      have hb' : b ∈ p ⁻¹' U := connectedComponentIn_subset _ _ hb
      have himg : (φ : X → X) '' connectedComponentIn (p ⁻¹' U) b =
          connectedComponentIn (p ⁻¹' U) a := by
        rw [φ.image_connectedComponentIn hb', ← φ.preimage_symm, ← hφb]
        congr 1
        ext w
        have := hH φ⁻¹ (H.inv_mem hφ) w
        rw [Homeomorph.inv_apply] at this
        simp only [mem_preimage, this]
      have hya : connectedComponentIn (p ⁻¹' U) y = connectedComponentIn (p ⁻¹' U) a :=
        (connectedComponentIn_eq ha)
      have hy'b : connectedComponentIn (p ⁻¹' U) y' = connectedComponentIn (p ⁻¹' U) b :=
        (connectedComponentIn_eq hb)
      show homeoQuotientMk H '' _ = homeoQuotientMk H '' _
      rw [hya, hy'b, ← himg, image_image]
      congr 1
      funext w
      exact Quotient.sound (show ∃ ψ ∈ H, ψ w = φ w from ⟨φ, hφ, rfl⟩)
    apply Subset.antisymm
    · let B := ⋃ y ∈ {y | T y ≠ T x}, T y
      have hcov : connectedComponentIn (q ⁻¹' U) (homeoQuotientMk H x) ⊆ T x ∪ B := by
        intro z hz
        have hzU : z ∈ q ⁻¹' U := connectedComponentIn_subset _ _ hz
        induction z using Quotient.inductionOn with
        | h w =>
          have hw : w ∈ connectedComponentIn (p ⁻¹' U) w := mem_connectedComponentIn hzU
          by_cases h : T w = T x
          · exact Or.inl (h ▸ ⟨w, hw, rfl⟩)
          · exact Or.inr (mem_biUnion h ⟨w, hw, rfl⟩)
      have hdis : Disjoint (T x) B := by
        rw [Set.disjoint_left]
        intro z hz hzB
        obtain ⟨y, hy, hzy⟩ := mem_iUnion₂.1 hzB
        exact hy (hdisj x y ⟨z, hz, hzy⟩)
      refine isPreconnected_connectedComponentIn.subset_left_of_subset_union (hT x)
        (isOpen_biUnion fun y _ => hT y) hdis hcov
        ⟨homeoQuotientMk H x, mem_connectedComponentIn (show q (homeoQuotientMk H x) ∈ U from hx),
          x, mem_connectedComponentIn (show x ∈ p ⁻¹' U from hx), rfl⟩
    · have hpre : IsPreconnected (homeoQuotientMk H '' connectedComponentIn (p ⁻¹' U) x) :=
        isPreconnected_connectedComponentIn.image _ hπc.continuousOn
      refine hpre.subset_connectedComponentIn
        ⟨x, mem_connectedComponentIn (show x ∈ p ⁻¹' U from hx), rfl⟩ ?_
      rintro _ ⟨z, hz, rfl⟩
      exact (connectedComponentIn_subset _ _ hz : z ∈ p ⁻¹' U)
  refine isSpread_iff.2 ⟨hqc, ?_, ?_⟩
  · rintro V ⟨U, hU, z, hz, rfl⟩
    induction z using Quotient.inductionOn with
    | h x =>
      rw [key U hU x hz]
      exact hπo _ ((hU.preimage hp.continuous).connectedComponentIn)
  · intro z O hO hzO
    induction z using Quotient.inductionOn with
    | h x =>
      obtain ⟨U, hU, hxU, hsub⟩ := (isSpread_iff.1 hp).2.2 x _ (hO.preimage hπc) hzO
      refine ⟨U, hU, hxU, ?_⟩
      rw [key U hU x hxU]
      exact (image_mono hsub).trans (image_preimage_subset _ _)


/-- `\widetilde{ℂ∖S} → ℂ` is a spread. -/
theorem absGal_isSpread_univCoverProj : IsSpread (univCoverProj fibS y₀) :=
  isSpread_coe_comp_of_isCoveringMap isClosed_fibS.isOpen_compl
    (UniversalCover.isCoveringMap_proj semilocallySimplyConnected_fibS)

/-- `Γ₂ \ \widetilde{ℂ∖S} → ℂ` is a spread (for any `g`). -/
theorem absGal_isSpread_ordY₂Proj (g : ℕ → AbsGamma y₀) : IsSpread (ordY₂Proj y₀ g) :=
  isSpread_homeoQuotient_lift (absGal_isSpread_univCoverProj y₀) fun φ hφ x => by
    obtain ⟨ψ, -, rfl⟩ := Subgroup.mem_map.1 hφ
    exact congrArg Subtype.val (congrFun ψ.2 x)

/-- The fibre above `0` of `Y₂` is totally disconnected (`cor:totdiscont`, for any `g`). -/
theorem absGal_Y₂_fiber_totallyDisconnected (g : ℕ → AbsGamma y₀) :
    IsTotallyDisconnected (y₂Fiber0 y₀ g) :=
  isTotallyDisconnected_fiber (SpreadEnd.isSpread_base (absGal_isSpread_ordY₂Proj y₀ g)) 0

/-- The ends `absGalEnd ψ hψ k` over `0` are pairwise distinct when `Γ₂` acts trivially on the
dihedral invariant and `ψ` translates `Λ` by `±2πi`: their components over `D₅` carry distinct
values of `Θ`. -/
theorem absGalEnd_injective {g : ℕ → AbsGamma y₀} (hle : gamma2 y₀ g ≤ absGalN y₀)
    {ψ : AbsU y₀ ≃ₜ AbsU y₀} (hψ : ∀ c, absP y₀ (ψ c) = absP y₀ c)
    (hsq : ∀ c, absGalSq y₀ (ψ c) = absGalSq y₀ c) {m : ℂ} (hm : m = 1 ∨ m = -1)
    (hΛ : ∀ c, absGalΛ y₀ (ψ c) = absGalΛ y₀ c + m * (2 * Real.pi * Complex.I)) :
    Injective (absGalEnd (g := g) ψ hψ) := by
  intro k k' hkk
  have hC : absGalComp (g := g) ψ k 5 = absGalComp (g := g) ψ k' 5 := by
    rw [← absGalEnd_apply ψ hψ k, ← absGalEnd_apply ψ hψ k', hkk]
  have hval : ∀ k, absGalΘbar hle (absGalPt (g := g) ψ k 5) =
      absGalΘ y₀ (absGalW y₀ 5) + k * m := fun k =>
    absGalΘ_iterate y₀ hψ hsq hΛ k _
  have hx' : absGalPt (g := g) ψ k' 5 ∈ absGalComp (g := g) ψ k 5 := by
    rw [hC]; exact mem_connectedComponentIn (absGalPt_mem_fibD ψ hψ k' 5)
  have := absGalΘbar_eq_of_mem hle (absGalPt_mem_fibD ψ hψ k 5) hx'
  rw [hval, hval] at this
  have hm0 : m ≠ 0 := by rcases hm with rfl | rfl <;> norm_num
  have : (k' : ℂ) = k := mul_right_cancel₀ hm0 (add_left_cancel this)
  exact_mod_cast this.symm

/-- **`ex:consider_denote_absolute_galois`, the fibre claim, corrected** (DEC-27, the strongest
form proved): under the hypotheses of `GX.absGal_Y₂_fiber_not_compact`, the fibre above `0` of
`Y₂` is infinite and totally disconnected — as a Cantor set is — but NOT compact. -/
theorem absGal_Y₂_fiber_corrected (γ : ℕ → Path y₀ y₀)
    (h0 : windAt y₀ _ (fibPt_mem 0) (γ 0) - windAt y₀ _ (fibPt_mem 1) (γ 0) = 1 ∨
      windAt y₀ _ (fibPt_mem 0) (γ 0) - windAt y₀ _ (fibPt_mem 1) (γ 0) = -1)
    (h1 : windAt y₀ _ (fibPt_mem 0) (γ 1) - windAt y₀ _ (fibPt_mem 1) (γ 1) = 1 ∨
      windAt y₀ _ (fibPt_mem 0) (γ 1) - windAt y₀ _ (fibPt_mem 1) (γ 1) = -1)
    (hR : ∀ n, 2 ≤ n → ∀ t, ((γ n t : (fibSᶜ : Set ℂ)) : ℂ) ∈ absGalR) :
    (y₂Fiber0 y₀ fun n => FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (γ n))).Infinite ∧
      IsTotallyDisconnected
        (y₂Fiber0 y₀ fun n => FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (γ n))) ∧
      ¬ IsCompact
        (y₂Fiber0 y₀ fun n => FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (γ n))) := by
  have hle := absGal_gamma2_le y₀ γ h0 h1 hR
  obtain ⟨ψ, hψ, hsq, m, hm, hΛ⟩ := absGal_exists_translation y₀
  exact ⟨infinite_of_injective_forall_mem (absGalEnd_injective y₀ hle hψ hsq hm hΛ)
      fun k => absGalEnd_base ψ hψ k,
    absGal_Y₂_fiber_totallyDisconnected y₀ _, absGal_Y₂_fiber_not_compact y₀ γ h0 h1 hR⟩

/-! #### The paper's simple loops exist

Base point `y₀ = -i/4`; `γₙ` goes straight down-right to `pₙ - iρₙ` (`pₙ = 1/(n+1)`,
`ρₙ = 1/(2(n+1)(n+2))`), turns once counterclockwise around `pₙ` on the circle of radius `ρₙ`, and
comes back. It winds once around `pₙ` and not around the other points of `S`, and for `n ≥ 2` it
lies in the half-plane `Re z < 1/2 ⊆ absGalR`. So the refutation is unconditional. -/

/-- The conjugation invariance of the winding number: `w(s · c · s⁻¹) = w(c)`. -/
theorem absGal_cWinding_conj {z w : CStar} (s : Path z w) (c : Path w w) :
    cWinding ((s.trans c).trans s.symm) = cWinding c := by
  obtain ⟨A, hA⟩ := exists_expLift s.toContinuousMap
  obtain ⟨B, hB⟩ := exists_expLift c.toContinuousMap
  have eB := cWinding_spec c hB
  set k := A 1 - B 0
  have hk : Complex.exp k = 1 := by
    rw [Complex.exp_sub, show Complex.exp (A 1) = (s 1 : ℂ) from hA 1,
      show Complex.exp (B 0) = (c 0 : ℂ) from hB 0, s.target, c.source, div_self w.2]
  set d := B 1 + k - A 1
  have hd : Complex.exp d = 1 := by
    rw [Complex.exp_sub, Complex.exp_add, hk, mul_one, show Complex.exp (A 1) = (s 1 : ℂ) from hA 1,
      show Complex.exp (B 1) = (c 1 : ℂ) from hB 1, s.target, c.target, div_self w.2]
  let P₁ : Path (A 0) (A 1) := ⟨A, rfl, rfl⟩
  let P₂ : Path (A 1) (B 1 + k) := ⟨⟨fun t => B t + k, by fun_prop⟩, by simp [k], rfl⟩
  let P₃ : Path (B 1 + k) (A 0 + d) :=
    ⟨⟨fun t => A (unitInterval.symm t) + d, by fun_prop⟩, by simp [d], by simp⟩
  have hP : ∀ t, Complex.exp (((P₁.trans P₂).trans P₃) t) = ((s.trans c).trans s.symm) t := by
    intro t
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs with h1
    · rw [Path.trans_apply, Path.trans_apply]
      split_ifs
      · exact hA _
      · show Complex.exp (B _ + k) = _
        rw [Complex.exp_add, hk, mul_one, hB]; rfl
    · show Complex.exp (A _ + d) = _
      rw [Complex.exp_add, hd, mul_one, hA]; rfl
  refine cWinding_eq _ (Γ := ((P₁.trans P₂).trans P₃).toContinuousMap) hP ?_
  show ((P₁.trans P₂).trans P₃) 1 = ((P₁.trans P₂).trans P₃) 0 + _
  rw [Path.target, Path.source]
  simp only [d, k]
  rw [eB]; ring

/-- The point `pₙ = 1/(n+1)`. -/
def absGalP (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

/-- The radius `ρₙ = 1/(2(n+1)(n+2))`. -/
def absGalρ (n : ℕ) : ℝ := 1 / (2 * ((n : ℝ) + 1) * ((n : ℝ) + 2))

theorem absGalρ_pos (n : ℕ) : 0 < absGalρ n := by unfold absGalρ; positivity

/-- Points of `S` other than `pₙ` are at distance `≥ 2ρₙ` from `pₙ`. -/
theorem absGal_sep {n : ℕ} {q : ℂ} (hq : q ∈ fibS) (hne : q ≠ (absGalP n : ℂ)) :
    2 * absGalρ n ≤ ‖(absGalP n : ℂ) - q‖ := by
  have hρ : 2 * absGalρ n = 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
    unfold absGalρ; field_simp
  rw [hρ]
  rcases hq with rfl | ⟨m, rfl⟩
  · rw [sub_zero, Complex.norm_real, Real.norm_of_nonneg (by unfold absGalP; positivity)]
    unfold absGalP
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · rw [← Complex.ofReal_sub, Complex.norm_real]
    have hmn : m ≠ n := by
      rintro rfl; exact hne rfl
    unfold absGalP
    rcases lt_or_gt_of_ne hmn with h | h
    · -- `m < n`
      have hm : ((m : ℝ) + 1) ≤ n := by exact_mod_cast h
      have e : |1 / ((n : ℝ) + 1) - 1 / ((m : ℝ) + 1)| = 1 / ((m : ℝ) + 1) - 1 / ((n : ℝ) + 1) := by
        rw [abs_sub_comm, abs_of_nonneg]
        rw [sub_nonneg]; gcongr
      rw [Real.norm_eq_abs, e]
      have h1 : 1 / (n : ℝ) ≤ 1 / ((m : ℝ) + 1) := by gcongr
      have hn : (0 : ℝ) < n := by linarith
      have h2 : 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) ≤ 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) := by
        rw [div_sub_div _ _ hn.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      linarith
    · -- `m > n`
      have hm : ((n : ℝ) + 2) ≤ (m : ℝ) + 1 := by
        have : (n : ℝ) + 1 ≤ m := by exact_mod_cast h
        linarith
      have e : |1 / ((n : ℝ) + 1) - 1 / ((m : ℝ) + 1)| = 1 / ((n : ℝ) + 1) - 1 / ((m : ℝ) + 1) := by
        rw [abs_of_nonneg]
        rw [sub_nonneg]; gcongr
      rw [Real.norm_eq_abs, e]
      have h1 : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 2) := by gcongr
      have h2 : 1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 2) = 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
        field_simp; ring
      linarith

/-- `y₀ = -i/4`. -/
def absGalY0 : (fibSᶜ : Set ℂ) :=
  ⟨-(1 / 4 : ℂ) * Complex.I, not_mem_fibS_of_im_ne_zero (by simp)⟩

/-- The start `bₙ = pₙ - iρₙ` of the circle. -/
def absGalB (n : ℕ) : ℂ := (absGalP n : ℂ) - (absGalρ n : ℂ) * Complex.I

/-- The circle `t ↦ pₙ - iρₙ e^{2iπt}`. -/
def absGalCirc (n : ℕ) (t : I) : ℂ :=
  (absGalP n : ℂ) - (absGalρ n : ℂ) * Complex.I * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ))

theorem norm_absGalCirc_sub (n : ℕ) (t : I) : ‖absGalCirc n t - absGalP n‖ = absGalρ n := by
  have h : ‖Complex.exp (2 * Real.pi * Complex.I * (t : ℝ))‖ = 1 := by
    rw [show (2 * Real.pi * Complex.I * (t : ℝ) : ℂ) = ((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.norm_exp_ofReal_mul_I]
  rw [absGalCirc, sub_sub_cancel_left, norm_neg, norm_mul, norm_mul, h, Complex.norm_I,
    Complex.norm_real, Real.norm_of_nonneg (absGalρ_pos n).le]
  ring

theorem absGalCirc_not_mem (n : ℕ) (t : I) : absGalCirc n t ∉ fibS := by
  intro h
  by_cases hq : absGalCirc n t = (absGalP n : ℂ)
  · have := norm_absGalCirc_sub n t
    rw [hq, sub_self, norm_zero] at this
    exact (absGalρ_pos n).ne this
  · have h1 := absGal_sep h hq
    have h2 := norm_absGalCirc_sub n t
    have h3 : ‖(absGalP n : ℂ) - absGalCirc n t‖ = absGalρ n := by rw [norm_sub_rev]; exact h2
    have := absGalρ_pos n
    linarith

theorem continuous_absGalCirc (n : ℕ) : Continuous (absGalCirc n) := by
  unfold absGalCirc; fun_prop

theorem absGalCirc_zero (n : ℕ) : absGalCirc n 0 = absGalB n := by
  simp [absGalCirc, absGalB]

theorem absGalCirc_one (n : ℕ) : absGalCirc n 1 = absGalB n := by
  simp only [absGalCirc, absGalB, Set.Icc.coe_one, Complex.ofReal_one, mul_one]
  rw [Complex.exp_two_pi_mul_I, mul_one]

theorem absGalB_im (n : ℕ) : (absGalB n).im = -absGalρ n := by
  simp [absGalB]

/-- The circle as a loop of `ℂ ∖ S`. -/
def absGalCircPath (n : ℕ) : Path (⟨absGalB n, absGalCirc_zero n ▸ absGalCirc_not_mem n 0⟩ :
    (fibSᶜ : Set ℂ)) ⟨absGalB n, absGalCirc_zero n ▸ absGalCirc_not_mem n 0⟩ where
  toFun t := ⟨absGalCirc n t, absGalCirc_not_mem n t⟩
  continuous_toFun := (continuous_absGalCirc n).subtype_mk _
  source' := Subtype.ext (absGalCirc_zero n)
  target' := Subtype.ext (absGalCirc_one n)

/-- The stem from `y₀` to `bₙ`, in the lower half-plane. -/
def absGalStemFun (n : ℕ) (t : I) : ℂ :=
  (1 - (t : ℝ) : ℂ) * (-(1 / 4 : ℂ) * Complex.I) + ((t : ℝ) : ℂ) * absGalB n

theorem absGalStemFun_im (n : ℕ) (t : I) :
    (absGalStemFun n t).im = -(1 - (t : ℝ)) / 4 - (t : ℝ) * absGalρ n := by
  simp [absGalStemFun, absGalB]; ring

theorem absGalStemFun_im_neg (n : ℕ) (t : I) : (absGalStemFun n t).im < 0 := by
  rw [absGalStemFun_im]
  have := absGalρ_pos n
  have h0 := t.2.1; have h1 := t.2.2
  by_cases ht : (t : ℝ) = 1
  · rw [ht]; nlinarith
  · have : (t : ℝ) < 1 := lt_of_le_of_ne h1 ht
    nlinarith

theorem absGalStemFun_re (n : ℕ) (t : I) : (absGalStemFun n t).re = (t : ℝ) * absGalP n := by
  simp [absGalStemFun, absGalB]

/-- The stem as a path of `ℂ ∖ S`. -/
def absGalStem (n : ℕ) : Path absGalY0 ⟨absGalB n, absGalCirc_zero n ▸ absGalCirc_not_mem n 0⟩ where
  toFun t := ⟨absGalStemFun n t, not_mem_fibS_of_im_ne_zero (absGalStemFun_im_neg n t).ne⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    unfold absGalStemFun; fun_prop
  source' := Subtype.ext (by simp [absGalStemFun, absGalY0])
  target' := Subtype.ext (by simp [absGalStemFun])

/-- **The simple loop `γₙ` around `1/(n+1)`.** -/
def absGalSimpleLoop (n : ℕ) : Path absGalY0 absGalY0 :=
  ((absGalStem n).trans (absGalCircPath n)).trans (absGalStem n).symm

theorem absGal_mem_of_trans {P : (fibSᶜ : Set ℂ) → Prop} (n : ℕ)
    (hs : ∀ t, P (absGalStem n t)) (hc : ∀ t, P (absGalCircPath n t)) (t : I) :
    P (absGalSimpleLoop n t) := by
  unfold absGalSimpleLoop
  rw [Path.trans_apply]
  split_ifs
  · rw [Path.trans_apply]; split_ifs
    · exact hs _
    · exact hc _
  · rw [Path.symm_apply]; exact hs _

/-- Winding numbers of the circle. -/
theorem absGal_cWinding_circ (n : ℕ) {q : ℂ} (hq : q ∈ fibS) :
    cWinding ((absGalCircPath n).map (subFib q hq).continuous) =
      if q = (absGalP n : ℂ) then 1 else 0 := by
  have he : ∀ t : I, Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) =
      Complex.exp (((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I) := fun t => by push_cast; ring_nf
  split_ifs with h
  · subst h
    have hne : -((absGalρ n : ℂ) * Complex.I) ≠ 0 :=
      neg_ne_zero.2 (mul_ne_zero (Complex.ofReal_ne_zero.2 (absGalρ_pos n).ne') Complex.I_ne_zero)
    refine cWinding_eq _ (Γ := ⟨fun t => Complex.log (-((absGalρ n : ℂ) * Complex.I)) +
      2 * Real.pi * Complex.I * (t : ℝ), by fun_prop⟩) (fun t => ?_) ?_
    · show Complex.exp (Complex.log _ + _) = absGalCirc n t - absGalP n
      rw [Complex.exp_add, Complex.exp_log hne, absGalCirc]; ring
    · simp
  · set a : ℂ := (absGalP n : ℂ) - q
    have ha : 2 * absGalρ n ≤ ‖a‖ := absGal_sep hq h
    have ha0 : a ≠ 0 := fun h0 => by
      rw [h0, norm_zero] at ha; linarith [absGalρ_pos n]
    set w : I → ℂ := fun t => -((absGalρ n : ℂ) * Complex.I *
      Complex.exp (2 * Real.pi * Complex.I * (t : ℝ))) / a
    have hw : ∀ t, ‖w t‖ ≤ 1 / 2 := fun t => by
      simp only [w, norm_div, norm_neg, norm_mul, Complex.norm_I, Complex.norm_real,
        Real.norm_of_nonneg (absGalρ_pos n).le, mul_one]
      rw [he t, Complex.norm_exp_ofReal_mul_I, mul_one, div_le_iff₀ (by linarith [absGalρ_pos n])]
      linarith
    have hslit : ∀ t, 1 + w t ∈ Complex.slitPlane := fun t => by
      refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
      have := Complex.abs_re_le_norm (w t)
      rw [Complex.add_re, Complex.one_re]
      linarith [abs_le.1 (this.trans (hw t))]
    have hwc : Continuous w := by simp only [w]; fun_prop
    refine cWinding_eq _ (Γ := ⟨fun t => Complex.log a + Complex.log (1 + w t),
      continuous_const.add (continuous_iff_continuousAt.2 fun t =>
        (continuous_const.add hwc).continuousAt.clog (hslit t))⟩) (fun t => ?_) ?_
    · show Complex.exp (Complex.log a + Complex.log (1 + w t)) = absGalCirc n t - q
      rw [Complex.exp_add, Complex.exp_log ha0,
        Complex.exp_log (Complex.slitPlane_ne_zero (hslit t))]
      simp only [w]
      rw [mul_add, mul_one, ← mul_div_assoc, mul_div_cancel_left₀ _ ha0]
      simp only [absGalCirc, a]
      ring
    · simp only [ContinuousMap.coe_mk, Int.cast_zero, zero_mul, add_zero]
      congr 2
      simp only [w, Set.Icc.coe_one, Set.Icc.coe_zero, Complex.ofReal_one, Complex.ofReal_zero,
        mul_one, mul_zero, Complex.exp_zero, Complex.exp_two_pi_mul_I]

/-- The winding numbers of the simple loops: `γₙ` winds once around `1/(n+1)` and not around
the other points of `S`. -/
theorem absGal_windAt_simpleLoop (n m : ℕ) :
    windAt absGalY0 _ (fibPt_mem m) (absGalSimpleLoop n) = if n = m then 1 else 0 := by
  unfold windAt absGalSimpleLoop
  rw [Path.map_trans, Path.map_trans, ← Path.map_symm, absGal_cWinding_conj, absGal_cWinding_circ]
  have : ((((1 / ((m : ℝ) + 1)) : ℝ) : ℂ) = (absGalP n : ℂ)) ↔ n = m := by
    rw [Complex.ofReal_inj, absGalP]
    constructor
    · intro h
      have : (m : ℝ) + 1 = (n : ℝ) + 1 := by
        have h' := h
        field_simp at h'
        linarith
      exact_mod_cast (by linarith : (n : ℝ) = m)
    · rintro rfl; rfl
  simp only [this]

/-- For `n ≥ 2` the simple loop lies in `Re z < 1/2`, hence in `absGalR`. -/
theorem absGal_mem_R_of_re {z : ℂ} (hz : z.re < 1 / 2) : z ∈ absGalR := by
  refine absGal_mem_R_of_one_lt_re ?_
  have hne : z - 1 / 2 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have e : absGalF z = 1 - (1 / 2) * (z - 1 / 2)⁻¹ := by
    rw [absGalF, show z - 1 = (z - 1 / 2) - 1 / 2 by ring, sub_div, div_self hne, div_eq_mul_inv]
  have hre : z.re - 1 / 2 < 0 := by linarith
  have hns : 0 < Complex.normSq (z - 1 / 2) := Complex.normSq_pos.2 hne
  rw [e, Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.inv_re, Complex.inv_im]
  have : (z.re - 1 / 2) / Complex.normSq (z - 1 / 2) < 0 := div_neg_of_neg_of_pos hre hns
  norm_num
  linarith

theorem absGal_simpleLoop_mem_R (n : ℕ) (hn : 2 ≤ n) (t : I) :
    ((absGalSimpleLoop n t : (fibSᶜ : Set ℂ)) : ℂ) ∈ absGalR := by
  have hp : absGalP n ≤ 1 / 3 := by
    unfold absGalP
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hρ : absGalρ n ≤ 1 / 24 := by
    unfold absGalρ
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  refine absGal_mem_of_trans (P := fun z => (z : ℂ) ∈ absGalR) n (fun t => ?_) (fun t => ?_) t
  · refine absGal_mem_R_of_re ?_
    show (absGalStemFun n t).re < 1 / 2
    rw [absGalStemFun_re]
    have := absGalρ_pos n
    nlinarith [t.2.1, t.2.2, (show 0 < absGalP n by unfold absGalP; positivity)]
  · refine absGal_mem_R_of_re ?_
    show (absGalCirc n t).re < 1 / 2
    have h1 := norm_absGalCirc_sub n t
    have := Complex.abs_re_le_norm (absGalCirc n t - absGalP n)
    rw [h1, Complex.sub_re, Complex.ofReal_re] at this
    linarith [abs_le.1 this]

/-- **`ex:consider_denote_absolute_galois`, the fibre claim, refuted unconditionally**: for the
simple loops `γₙ = absGalSimpleLoop n` at `y₀ = -i/4` and `Γ₂` the normal closure of their
squares (DEC-58), the fibre above `0` of `Y₂` is not compact, hence not a Cantor set. -/
theorem absGal_Y₂_fiber_not_cantor_simple :
    ¬ IsCompact (y₂Fiber0 absGalY0 fun n =>
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (absGalSimpleLoop n))) ∧
      IsEmpty ((y₂Fiber0 absGalY0 fun n =>
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (absGalSimpleLoop n))) ≃ₜ cantorSet) :=
  ⟨absGal_Y₂_fiber_not_compact_of_simple absGalY0 _ absGal_windAt_simpleLoop
      absGal_simpleLoop_mem_R,
    absGal_Y₂_fiber_not_cantor absGalY0 _ absGal_windAt_simpleLoop absGal_simpleLoop_mem_R⟩

/-- **`ex:consider_denote_absolute_galois`, the fibre claim, corrected** (DEC-27), for the simple
loops `γₙ = absGalSimpleLoop n` and `Γ₂` the normal closure of their squares (DEC-58): the fibre
above `0` of `Y₂` is infinite and totally disconnected, but not compact (so not a Cantor set). -/
theorem absGal_Y₂_fiber_corrected_simple :
    (y₂Fiber0 absGalY0 fun n =>
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (absGalSimpleLoop n))).Infinite ∧
      IsTotallyDisconnected (y₂Fiber0 absGalY0 fun n =>
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (absGalSimpleLoop n))) ∧
      ¬ IsCompact (y₂Fiber0 absGalY0 fun n =>
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (absGalSimpleLoop n))) :=
  absGal_Y₂_fiber_corrected absGalY0 _
    (Or.inl (by rw [absGal_windAt_simpleLoop 0 0, absGal_windAt_simpleLoop 0 1]; norm_num))
    (Or.inr (by rw [absGal_windAt_simpleLoop 1 0, absGal_windAt_simpleLoop 1 1]; norm_num))
    absGal_simpleLoop_mem_R

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

/-- Side remark on `RamcovGX.tex:1578` OUTSIDE the ruled reading (DEC-58 reads the example as
being about Antoine's necklace): for arbitrary wild Cantor sets of `S³` the claim would fail as
soon as one of them has simply connected, locally non-separating complement (the density of the
complement is automatic, `GX.dense_compl_of_isCantorSubset`). -/
theorem wild_cantor_claim_false_of_exists
    (h : ∃ C : Set Sphere3, IsWildCantor C ∧ SimplyConnectedSpace (Cᶜ : Set Sphere3) ∧
      IsLocallyNonseparating C) :
    ¬ ∀ C : Set Sphere3, IsWildCantor C → ¬ IsSLSCIn Cᶜ := by
  obtain ⟨C, hw, hsc, hC⟩ := h
  exact fun hall => hall C hw
    (sphere3_isSLSCIn_compl_of_simplyConnected (dense_compl_of_isCantorSubset hw.1) hC)

/-- The essential-loop criterion `GX.not_isSLSCIn_of_essential`, for a complement `Cᶜ`: if some
point `x` has, in each of its neighbourhoods, a loop at `x` off `C` (interior points) which is
essential in the complement of a piece `K ⊆ C` with `x ∉ K`, small loops at `x` being trivial
there, then `Cᶜ` is NOT semi-locally simply connected. No Cantor or wildness hypothesis is used;
this is the property Antoine's theorem gives for the necklace (`GX.antoineNecklace_antoine`). -/
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

/-! ### Antoine's necklace: combinatorial data -/

/-- The centres of the `64` links of the first stage, in units of `1/640`: `16` per side of the
square `max(|x|,|y|) = 7/8` of the plane `z = 0`, `7/64` apart, starting at the corners. -/
def antoineZ (i : Fin 64) : ℤ × ℤ :=
  let j := i.val / 16
  let k : ℤ := (i.val % 16 : ℕ)
  if j = 0 then (-560 + 70 * k, -560) else if j = 1 then (560, -560 + 70 * k)
  else if j = 2 then (560 - 70 * k, 560) else (-560, 560 - 70 * k)

/-- The plane of the `i`-th link: `0` the plane `z = 0` (even positions, the corners included),
`1` the plane `y = const` (odd positions on the sides parallel to the `x`-axis), `2` the plane
`x = const` (odd positions on the sides parallel to the `y`-axis). -/
def antoineT (i : Fin 64) : Fin 3 :=
  if i.val % 16 % 2 = 0 then 0 else if i.val / 16 % 2 = 0 then 1 else 2

/-- Half-extent along `x` of a link of type `t`, in units of `1/640`. -/
def antoineEx : Fin 3 → ℤ
  | 0 => 56
  | 1 => 56
  | 2 => 7

/-- Half-extent along `y` of a link of type `t`, in units of `1/640`. -/
def antoineEy : Fin 3 → ℤ
  | 0 => 56
  | 1 => 7
  | 2 => 56

/-- The bounding boxes of the links `i` and `j` are separated along `x` or `y`. -/
def AntoineSep (i j : Fin 64) : Prop :=
  antoineEx (antoineT i) + antoineEx (antoineT j) < |(antoineZ i).1 - (antoineZ j).1| ∨
  antoineEy (antoineT i) + antoineEy (antoineT j) < |(antoineZ i).2 - (antoineZ j).2|

/-- The links `i` and `j` are consecutive in the chain: centres `7/64` apart along a side, one in
the plane `z = 0`, the other in the perpendicular plane containing that side. -/
def AntoineAdj (i j : Fin 64) : Prop :=
  ((antoineZ i).2 = (antoineZ j).2 ∧ |(antoineZ i).1 - (antoineZ j).1| = 70 ∧
    ((antoineT i = 0 ∧ antoineT j = 1) ∨ (antoineT i = 1 ∧ antoineT j = 0))) ∨
  ((antoineZ i).1 = (antoineZ j).1 ∧ |(antoineZ i).2 - (antoineZ j).2| = 70 ∧
    ((antoineT i = 0 ∧ antoineT j = 2) ∨ (antoineT i = 2 ∧ antoineT j = 0)))

instance antoineSep_decidable (i j : Fin 64) : Decidable (AntoineSep i j) := by
  unfold AntoineSep; infer_instance
instance antoineAdj_decidable (i j : Fin 64) : Decidable (AntoineAdj i j) := by
  unfold AntoineAdj; infer_instance

set_option maxRecDepth 100000 in
/-- Two distinct links of the first stage have separated bounding boxes, unless they are
consecutive in the chain (checked over all `64 × 64` pairs). -/
theorem antoine_sep_or_adj : ∀ i j : Fin 64, i ≠ j → AntoineSep i j ∨ AntoineAdj i j := by
  decide

/-- Every centre lies on the square `max(|x|,|y|) = 7/8`. -/
theorem antoine_centre_mem : ∀ i : Fin 64,
    (|(antoineZ i).1| = 560 ∧ |(antoineZ i).2| ≤ 560) ∨
      (|(antoineZ i).2| = 560 ∧ |(antoineZ i).1| ≤ 560) := by
  decide

/-- Consecutive links (cyclically) — `64` pairs: the chain closes up. -/
theorem antoine_adj_succ : ∀ i : Fin 64, AntoineAdj i (i + 1) := by decide

/-! ### Antoine's necklace: the construction -/

/-- The link: the square solid ring `3/4 ≤ max(|x|,|y|) ≤ 1`, `|z| ≤ 1/8` of `ℝ³` (a solid torus). -/
def antoineLink : Set (ℝ × ℝ × ℝ) :=
  {p | |p.2.2| ≤ 1 / 8 ∧ max |p.1| |p.2.1| ≤ 1 ∧ 3 / 4 ≤ max |p.1| |p.2.1|}

/-- The coordinate permutations putting the link in the planes of type `0`, `1`, `2`. -/
def antoinePerm : Fin 3 → ℝ × ℝ × ℝ → ℝ × ℝ × ℝ
  | 0 => fun p => p
  | 1 => fun p => (p.1, p.2.2, p.2.1)
  | 2 => fun p => (p.2.2, p.2.1, p.1)

/-- The similarity of ratio `7/80` carrying the link onto the `i`-th link of the first stage. -/
def antoineMap (i : Fin 64) (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (((antoineZ i).1 : ℝ) / 640 + 7 / 80 * (antoinePerm (antoineT i) p).1,
    ((antoineZ i).2 : ℝ) / 640 + 7 / 80 * (antoinePerm (antoineT i) p).2.1,
    7 / 80 * (antoinePerm (antoineT i) p).2.2)

theorem antoineT_cases (i : Fin 64) : antoineT i = 0 ∨ antoineT i = 1 ∨ antoineT i = 2 := by
  rcases antoineT i with ⟨t, ht⟩
  interval_cases t <;> simp

/-- The `i`-th link lies within `7/80` of its centre along `x` and `y`, more precisely within the
half-extents `antoineEx`, `antoineEy`, and within `7/80` of the plane `z = 0`. -/
theorem antoineMap_bounds (i : Fin 64) {p : ℝ × ℝ × ℝ} (hp : p ∈ antoineLink) :
    |(antoineMap i p).1 - (antoineZ i).1 / 640| ≤ antoineEx (antoineT i) / 640 ∧
      |(antoineMap i p).2.1 - (antoineZ i).2 / 640| ≤ antoineEy (antoineT i) / 640 ∧
      |(antoineMap i p).2.2| ≤ 56 / 640 := by
  obtain ⟨hz, hm, -⟩ := hp
  have hx : |p.1| ≤ 1 := (le_max_left _ _).trans hm
  have hy : |p.2.1| ≤ 1 := (le_max_right _ _).trans hm
  rcases antoineT_cases i with h | h | h <;>
    simp only [antoineMap, h, antoinePerm, antoineEx, antoineEy, add_sub_cancel_left, abs_mul,
      abs_of_pos (show (0 : ℝ) < 7 / 80 by norm_num)] <;>
    push_cast <;> refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- The first stage lies in the link: `gᵢ(L) ⊆ L`. -/
theorem antoineMap_mem (i : Fin 64) {p : ℝ × ℝ × ℝ} (hp : p ∈ antoineLink) :
    antoineMap i p ∈ antoineLink := by
  obtain ⟨h1, h2, h3⟩ := antoineMap_bounds i hp
  have e1 : (antoineEx (antoineT i) : ℝ) ≤ 56 := by
    rcases antoineT_cases i with h | h | h <;> simp [h, antoineEx]; norm_num
  have e2 : (antoineEy (antoineT i) : ℝ) ≤ 56 := by
    rcases antoineT_cases i with h | h | h <;> simp [h, antoineEy]; norm_num
  set q := antoineMap i p
  have a1 := abs_sub_abs_le_abs_sub q.1 ((antoineZ i).1 / 640)
  have a1' := abs_sub_abs_le_abs_sub (((antoineZ i).1 : ℝ) / 640) q.1
  have a2 := abs_sub_abs_le_abs_sub q.2.1 ((antoineZ i).2 / 640)
  have a2' := abs_sub_abs_le_abs_sub (((antoineZ i).2 : ℝ) / 640) q.2.1
  rw [abs_sub_comm] at a1' a2'
  have d1 : |((antoineZ i).1 : ℝ) / 640| = |((antoineZ i).1 : ℝ)| / 640 := by
    rw [abs_div]; norm_num
  have d2 : |((antoineZ i).2 : ℝ) / 640| = |((antoineZ i).2 : ℝ)| / 640 := by
    rw [abs_div]; norm_num
  rw [d1] at a1 a1'
  rw [d2] at a2 a2'
  refine ⟨by linarith, max_le ?_ ?_, ?_⟩
  · rcases antoine_centre_mem i with ⟨c1, c2⟩ | ⟨c1, c2⟩
    · have : |((antoineZ i).1 : ℝ)| = 560 := by exact_mod_cast c1
      linarith
    · have : |((antoineZ i).1 : ℝ)| ≤ 560 := by exact_mod_cast c2
      linarith
  · rcases antoine_centre_mem i with ⟨c1, c2⟩ | ⟨c1, c2⟩
    · have : |((antoineZ i).2 : ℝ)| ≤ 560 := by exact_mod_cast c2
      linarith
    · have : |((antoineZ i).2 : ℝ)| = 560 := by exact_mod_cast c1
      linarith
  · rcases antoine_centre_mem i with ⟨c1, c2⟩ | ⟨c1, c2⟩
    · have : |((antoineZ i).1 : ℝ)| = 560 := by exact_mod_cast c1
      exact le_max_of_le_left (by linarith)
    · have : |((antoineZ i).2 : ℝ)| = 560 := by exact_mod_cast c1
      exact le_max_of_le_right (by linarith)

/-- Two interlocking links meet nowhere: a link `a² ∨ b²`-ring of the plane of its coordinates
`(a, b)` and thickness coordinate `c`, and a second one whose coordinates `(a', b')`, `c'` satisfy
`a = a' ± 5/4`, `b = c'`, `c = b'`. -/
theorem antoine_link_aux {a b c a' b' c' s : ℝ} (hs : s = 5 / 4 ∨ s = -(5 / 4))
    (h1 : a = a' + s) (h2 : b = c') (h3 : c = b')
    (hp : |c| ≤ 1 / 8 ∧ max |a| |b| ≤ 1 ∧ 3 / 4 ≤ max |a| |b|)
    (hp' : |c'| ≤ 1 / 8 ∧ max |a'| |b'| ≤ 1 ∧ 3 / 4 ≤ max |a'| |b'|) : False := by
  obtain ⟨hc, ha1, ha2⟩ := hp
  obtain ⟨hc', ha1', ha2'⟩ := hp'
  subst h2 h3
  have hA : 3 / 4 ≤ |a| := by
    rcases le_max_iff.1 ha2 with h | h
    · exact h
    · linarith
  have hA' : 3 / 4 ≤ |a'| := by
    rcases le_max_iff.1 ha2' with h | h
    · exact h
    · linarith
  have hx : |a| ≤ 1 := (le_max_left _ _).trans ha1
  have hx' : |a'| ≤ 1 := (le_max_left _ _).trans ha1'
  rw [abs_le] at hx hx'
  rcases le_abs'.1 hA with h | h <;> rcases le_abs'.1 hA' with h' | h' <;>
    rcases hs with rfl | rfl <;> linarith

/-- The `64` links of the first stage are pairwise disjoint. -/
theorem antoineMap_disjoint {i j : Fin 64} (hij : i ≠ j) :
    Disjoint (antoineMap i '' antoineLink) (antoineMap j '' antoineLink) := by
  rw [Set.disjoint_left]
  rintro _ ⟨p, hp, rfl⟩ ⟨p', hp', heq⟩
  rcases antoine_sep_or_adj i j hij with hsep | hadj
  · obtain ⟨b1, b2, -⟩ := antoineMap_bounds i hp
    obtain ⟨b1', b2', -⟩ := antoineMap_bounds j hp'
    rw [heq] at b1' b2'
    rw [abs_le] at b1 b2 b1' b2'
    rcases hsep with h | h
    · have h' : ((antoineEx (antoineT i) + antoineEx (antoineT j) : ℤ) : ℝ) <
          |((antoineZ i).1 : ℝ) - (antoineZ j).1| := by exact_mod_cast h
      push_cast at h'
      rcases lt_abs.1 h' with h'' | h'' <;> linarith
    · have h' : ((antoineEy (antoineT i) + antoineEy (antoineT j) : ℤ) : ℝ) <
          |((antoineZ i).2 : ℝ) - (antoineZ j).2| := by exact_mod_cast h
      push_cast at h'
      rcases lt_abs.1 h' with h'' | h'' <;> linarith
  · rcases hadj with ⟨hy, hx, ht⟩ | ⟨hx, hy, ht⟩
    · have hy' : ((antoineZ i).2 : ℝ) = (antoineZ j).2 := by exact_mod_cast hy
      have hx' : ((antoineZ i).1 : ℝ) - (antoineZ j).1 = 70 ∨
          ((antoineZ i).1 : ℝ) - (antoineZ j).1 = -70 := by
        rcases (abs_eq (by norm_num : (0 : ℤ) ≤ 70)).1 hx with h | h
        · exact Or.inl (by exact_mod_cast h)
        · exact Or.inr (by exact_mod_cast h)
      rcases ht with ⟨ti, tj⟩ | ⟨ti, tj⟩
      · simp only [antoineMap, ti, tj, antoinePerm, Prod.mk.injEq] at heq
        obtain ⟨e1, e2, e3⟩ := heq
        refine antoine_link_aux (a := p.1) (b := p.2.1) (c := p.2.2) (a' := p'.1) (b' := p'.2.1)
          (c' := p'.2.2) (s := if ((antoineZ i).1 : ℝ) - (antoineZ j).1 = 70 then -(5/4) else 5/4)
          ?_ ?_ (by linarith) (by linarith) hp hp'
        · split_ifs <;> simp
        · rcases hx' with h | h
          · rw [if_pos h]; linarith
          · rw [if_neg (by rw [h]; norm_num)]; linarith
      · simp only [antoineMap, ti, tj, antoinePerm, Prod.mk.injEq] at heq
        obtain ⟨e1, e2, e3⟩ := heq
        refine antoine_link_aux (a := p'.1) (b := p'.2.1) (c := p'.2.2) (a' := p.1) (b' := p.2.1)
          (c' := p.2.2) (s := if ((antoineZ i).1 : ℝ) - (antoineZ j).1 = 70 then 5/4 else -(5/4))
          ?_ ?_ (by linarith) (by linarith) hp' hp
        · split_ifs <;> simp
        · rcases hx' with h | h
          · rw [if_pos h]; linarith
          · rw [if_neg (by rw [h]; norm_num)]; linarith
    · have hx' : ((antoineZ i).1 : ℝ) = (antoineZ j).1 := by exact_mod_cast hx
      have hy' : ((antoineZ i).2 : ℝ) - (antoineZ j).2 = 70 ∨
          ((antoineZ i).2 : ℝ) - (antoineZ j).2 = -70 := by
        rcases (abs_eq (by norm_num : (0 : ℤ) ≤ 70)).1 hy with h | h
        · exact Or.inl (by exact_mod_cast h)
        · exact Or.inr (by exact_mod_cast h)
      rcases ht with ⟨ti, tj⟩ | ⟨ti, tj⟩
      · simp only [antoineMap, ti, tj, antoinePerm, Prod.mk.injEq] at heq
        obtain ⟨e1, e2, e3⟩ := heq
        refine antoine_link_aux (a := p.2.1) (b := p.1) (c := p.2.2) (a' := p'.2.1) (b' := p'.1)
          (c' := p'.2.2) (s := if ((antoineZ i).2 : ℝ) - (antoineZ j).2 = 70 then -(5/4) else 5/4)
          ?_ ?_ (by linarith) (by linarith) ⟨hp.1, by rw [max_comm]; exact hp.2.1,
            by rw [max_comm]; exact hp.2.2⟩ ⟨hp'.1, by rw [max_comm]; exact hp'.2.1,
            by rw [max_comm]; exact hp'.2.2⟩
        · split_ifs <;> simp
        · rcases hy' with h | h
          · rw [if_pos h]; linarith
          · rw [if_neg (by rw [h]; norm_num)]; linarith
      · simp only [antoineMap, ti, tj, antoinePerm, Prod.mk.injEq] at heq
        obtain ⟨e1, e2, e3⟩ := heq
        refine antoine_link_aux (a := p'.2.1) (b := p'.1) (c := p'.2.2) (a' := p.2.1) (b' := p.1)
          (c' := p.2.2) (s := if ((antoineZ i).2 : ℝ) - (antoineZ j).2 = 70 then 5/4 else -(5/4))
          ?_ ?_ (by linarith) (by linarith) ⟨hp'.1, by rw [max_comm]; exact hp'.2.1,
            by rw [max_comm]; exact hp'.2.2⟩ ⟨hp.1, by rw [max_comm]; exact hp.2.1,
            by rw [max_comm]; exact hp.2.2⟩
        · split_ifs <;> simp
        · rcases hy' with h | h
          · rw [if_pos h]; linarith
          · rw [if_neg (by rw [h]; norm_num)]; linarith

theorem antoine_abs_fst_le (p q : ℝ × ℝ × ℝ) : |p.1 - q.1| ≤ dist p q := by
  rw [← Real.dist_eq, Prod.dist_eq]; exact le_max_left _ _

theorem antoine_abs_snd_fst_le (p q : ℝ × ℝ × ℝ) : |p.2.1 - q.2.1| ≤ dist p q := by
  rw [← Real.dist_eq, Prod.dist_eq (x := p), Prod.dist_eq]
  exact (le_max_left _ _).trans (le_max_right _ _)

theorem antoine_abs_snd_snd_le (p q : ℝ × ℝ × ℝ) : |p.2.2 - q.2.2| ≤ dist p q := by
  rw [← Real.dist_eq, Prod.dist_eq (x := p), Prod.dist_eq]
  exact (le_max_right _ _).trans (le_max_right _ _)

theorem antoine_dist_le {p q : ℝ × ℝ × ℝ} {r : ℝ} (h1 : |p.1 - q.1| ≤ r) (h2 : |p.2.1 - q.2.1| ≤ r)
    (h3 : |p.2.2 - q.2.2| ≤ r) : dist p q ≤ r := by
  rw [Prod.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq]
  exact max_le h1 (max_le h2 h3)

/-- Each `gᵢ` is a similarity of ratio `7/80` (for the sup distance; `≤` suffices here). -/
theorem antoineMap_dist_le (i : Fin 64) (p q : ℝ × ℝ × ℝ) :
    dist (antoineMap i p) (antoineMap i q) ≤ 7 / 80 * dist p q := by
  have a := antoine_abs_fst_le p q
  have b := antoine_abs_snd_fst_le p q
  have c := antoine_abs_snd_snd_le p q
  have key : ∀ x y : ℝ, |x - y| ≤ dist p q → ∀ z : ℝ,
      |z + 7 / 80 * x - (z + 7 / 80 * y)| ≤ 7 / 80 * dist p q := fun x y h z => by
    rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 7 / 80)]
    exact mul_le_mul_of_nonneg_left h (by norm_num)
  have key0 : ∀ x y : ℝ, |x - y| ≤ dist p q →
      |7 / 80 * x - 7 / 80 * y| ≤ 7 / 80 * dist p q := fun x y h => by
    simpa using key x y h 0
  rcases antoineT_cases i with h | h | h <;>
    exact antoine_dist_le (by simp only [antoineMap, h, antoinePerm]; exact key _ _ (by assumption) _)
      (by simp only [antoineMap, h, antoinePerm]; exact key _ _ (by assumption) _)
      (by simp only [antoineMap, h, antoinePerm]; exact key0 _ _ (by assumption))

theorem continuous_antoineMap (i : Fin 64) : Continuous (antoineMap i) := by
  show Continuous fun p => antoineMap i p
  rcases antoineT_cases i with h | h | h <;> simp only [antoineMap, h, antoinePerm] <;> fun_prop

theorem antoineMap_injective (i : Fin 64) : Injective (antoineMap i) := by
  intro p q hpq
  rcases antoineT_cases i with h | h | h <;>
    simp only [antoineMap, h, antoinePerm, Prod.mk.injEq] at hpq <;>
    obtain ⟨e1, e2, e3⟩ := hpq <;>
    exact Prod.ext (by linarith) (Prod.ext (by linarith) (by linarith))

/-- `g_{w₀} ∘ ⋯ ∘ g_{w_{n-1}}`. -/
def antoineComp (w : ℕ → Fin 64) : ℕ → ℝ × ℝ × ℝ → ℝ × ℝ × ℝ
  | 0 => id
  | n + 1 => antoineComp w n ∘ antoineMap (w n)

theorem antoineComp_dist_le (w : ℕ → Fin 64) (n : ℕ) (p q : ℝ × ℝ × ℝ) :
    dist (antoineComp w n p) (antoineComp w n q) ≤ (7 / 80) ^ n * dist p q := by
  induction n generalizing p q with
  | zero => simp [antoineComp]
  | succ n ih =>
    calc dist (antoineComp w (n + 1) p) (antoineComp w (n + 1) q)
        ≤ (7 / 80) ^ n * dist (antoineMap (w n) p) (antoineMap (w n) q) := ih _ _
      _ ≤ (7 / 80) ^ n * (7 / 80 * dist p q) :=
          mul_le_mul_of_nonneg_left (antoineMap_dist_le _ _ _) (by positivity)
      _ = (7 / 80) ^ (n + 1) * dist p q := by ring

theorem continuous_antoineComp (w : ℕ → Fin 64) (n : ℕ) : Continuous (antoineComp w n) := by
  induction n with
  | zero => exact continuous_id
  | succ n ih => exact ih.comp (continuous_antoineMap _)

theorem antoineComp_injective (w : ℕ → Fin 64) (n : ℕ) : Injective (antoineComp w n) := by
  induction n with
  | zero => exact injective_id
  | succ n ih => exact ih.comp (antoineMap_injective _)

theorem antoineComp_congr {w w' : ℕ → Fin 64} {n : ℕ} (h : ∀ k < n, w k = w' k) :
    antoineComp w n = antoineComp w' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show antoineComp w n ∘ antoineMap (w n) = antoineComp w' n ∘ antoineMap (w' n)
    rw [ih fun k hk => h k (by omega), h n (by omega)]

/-- The `n`-th stage pieces are nested. -/
theorem antoineComp_succ_subset (w : ℕ → Fin 64) (n : ℕ) :
    antoineComp w (n + 1) '' antoineLink ⊆ antoineComp w n '' antoineLink := by
  show (antoineComp w n ∘ antoineMap (w n)) '' antoineLink ⊆ _
  rw [image_comp]
  exact image_mono fun _ ⟨p, hp, e⟩ => e ▸ antoineMap_mem _ hp

theorem antoineComp_antitone (w : ℕ → Fin 64) {n m : ℕ} (h : n ≤ m) :
    antoineComp w m '' antoineLink ⊆ antoineComp w n '' antoineLink := by
  induction m, h using Nat.le_induction with
  | base => exact subset_rfl
  | succ m _ ih => exact (antoineComp_succ_subset w m).trans ih

theorem antoineLink_dist_le {p q : ℝ × ℝ × ℝ} (hp : p ∈ antoineLink) (hq : q ∈ antoineLink) :
    dist p q ≤ 2 := by
  obtain ⟨hz, hm, -⟩ := hp
  obtain ⟨hz', hm', -⟩ := hq
  have h1 := (le_max_left _ _).trans hm
  have h2 := (le_max_right _ _).trans hm
  have h1' := (le_max_left _ _).trans hm'
  have h2' := (le_max_right _ _).trans hm'
  refine antoine_dist_le ?_ ?_ ?_ <;>
    exact (abs_sub _ _).trans (by linarith)

/-- The pieces of the `n`-th stage have diameter `≤ 2 (7/80)ⁿ`. -/
theorem antoineComp_diam {w : ℕ → Fin 64} {n : ℕ} {x y : ℝ × ℝ × ℝ}
    (hx : x ∈ antoineComp w n '' antoineLink) (hy : y ∈ antoineComp w n '' antoineLink) :
    dist x y ≤ 2 * (7 / 80) ^ n := by
  obtain ⟨p, hp, rfl⟩ := hx
  obtain ⟨q, hq, rfl⟩ := hy
  calc _ ≤ (7 / 80) ^ n * dist p q := antoineComp_dist_le w n p q
    _ ≤ (7 / 80) ^ n * 2 := mul_le_mul_of_nonneg_left (antoineLink_dist_le hp hq) (by positivity)
    _ = 2 * (7 / 80) ^ n := by ring

/-- A point of two pieces of the `n`-th stage determines the first `n` letters. -/
theorem antoineComp_prefix {w w' : ℕ → Fin 64} {n : ℕ} {x : ℝ × ℝ × ℝ}
    (hx : x ∈ antoineComp w n '' antoineLink) (hx' : x ∈ antoineComp w' n '' antoineLink) :
    ∀ k < n, w k = w' k := by
  induction n generalizing x with
  | zero => intro k hk; omega
  | succ n ih =>
    have hpre := ih (antoineComp_succ_subset w n hx) (antoineComp_succ_subset w' n hx')
    intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact hpre k hk
    by_contra hne
    obtain ⟨p, hp, rfl⟩ := hx
    obtain ⟨p', hp', he⟩ := hx'
    have he' : antoineComp w k (antoineMap (w k) p) = antoineComp w k (antoineMap (w' k) p') := by
      change antoineComp w' k (antoineMap (w' k) p') = antoineComp w k (antoineMap (w k) p) at he
      rw [← antoineComp_congr hpre] at he
      exact he.symm
    exact Set.disjoint_left.1 (antoineMap_disjoint hne) ⟨p, hp, rfl⟩
      ⟨p', hp', (antoineComp_injective w k he').symm⟩

/-- The `n`-th stage of Antoine's construction: the union of the `64ⁿ` links of generation `n`. -/
def antoineStage (n : ℕ) : Set (ℝ × ℝ × ℝ) := ⋃ w : ℕ → Fin 64, antoineComp w n '' antoineLink

/-- **Antoine's necklace** in `ℝ³`: the intersection of the stages. -/
def antoineNecklaceR3 : Set (ℝ × ℝ × ℝ) := ⋂ n, antoineStage n

/-- The stage `n + 1` lies in the stage `n`, each link of generation `n` containing the `64` links
of generation `n + 1` built in it. -/
theorem antoineStage_succ_subset (n : ℕ) : antoineStage (n + 1) ⊆ antoineStage n :=
  iUnion_mono fun w => antoineComp_succ_subset w n

theorem antoineStage_zero : antoineStage 0 = antoineLink := by
  simp only [antoineStage, antoineComp, image_id]
  exact iUnion_const _

theorem antoineLink_isCompact : IsCompact antoineLink := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · have e : antoineLink = {p : ℝ × ℝ × ℝ | |p.2.2| ≤ 1 / 8} ∩
        ({p | max |p.1| |p.2.1| ≤ 1} ∩ {p | 3 / 4 ≤ max |p.1| |p.2.1|}) := rfl
    have c1 : Continuous fun p : ℝ × ℝ × ℝ => |p.2.2| := continuous_abs.comp (by fun_prop)
    have c2 : Continuous fun p : ℝ × ℝ × ℝ => max |p.1| |p.2.1| :=
      (continuous_abs.comp continuous_fst).max (continuous_abs.comp (by fun_prop))
    rw [e]
    exact (isClosed_le c1 continuous_const).inter
      ((isClosed_le c2 continuous_const).inter (isClosed_le continuous_const c2))
  · refine (Metric.isBounded_closedBall (x := ((7 / 8 : ℝ), (0 : ℝ), (0 : ℝ))) (r := 2)).subset
      fun p hp => ?_
    rw [Metric.mem_closedBall]
    exact antoineLink_dist_le hp ⟨by norm_num, by norm_num, by norm_num⟩

/-- A base point of the link. -/
theorem antoine_base_mem : ((7 / 8 : ℝ), (0 : ℝ), (0 : ℝ)) ∈ antoineLink :=
  ⟨by norm_num, by norm_num, by norm_num⟩

theorem antoine_cauchy (w : ℕ → Fin 64) :
    CauchySeq fun n => antoineComp w n ((7 / 8 : ℝ), (0 : ℝ), (0 : ℝ)) := by
  refine cauchySeq_of_le_geometric (7 / 80) 2 (by norm_num) fun n => ?_
  calc dist (antoineComp w n _) (antoineComp w (n + 1) _)
      ≤ (7 / 80) ^ n * dist ((7 / 8 : ℝ), (0 : ℝ), (0 : ℝ))
          (antoineMap (w n) ((7 / 8 : ℝ), (0 : ℝ), (0 : ℝ))) := antoineComp_dist_le w n _ _
    _ ≤ (7 / 80) ^ n * 2 := mul_le_mul_of_nonneg_left
        (antoineLink_dist_le antoine_base_mem (antoineMap_mem _ antoine_base_mem)) (by positivity)
    _ = 2 * (7 / 80) ^ n := by ring

/-- The coding map `(ℕ → Fin 64) → ℝ³`, `w ↦ lim g_{w₀} ∘ ⋯ ∘ g_{w_{n-1}}(p₀)`. -/
def antoineCode (w : ℕ → Fin 64) : ℝ × ℝ × ℝ :=
  limUnder atTop fun n => antoineComp w n ((7 / 8 : ℝ), (0 : ℝ), (0 : ℝ))

theorem antoineCode_mem (w : ℕ → Fin 64) (n : ℕ) :
    antoineCode w ∈ antoineComp w n '' antoineLink := by
  have hc : IsClosed (antoineComp w n '' antoineLink) :=
    (antoineLink_isCompact.image (continuous_antoineComp w n)).isClosed
  refine hc.mem_of_tendsto (antoine_cauchy w).tendsto_limUnder
    (eventually_atTop.2 ⟨n, fun m hm => antoineComp_antitone w hm ⟨_, antoine_base_mem, rfl⟩⟩)

theorem antoine_eq_of_mem {w : ℕ → Fin 64} {x y : ℝ × ℝ × ℝ}
    (h : ∀ n, x ∈ antoineComp w n '' antoineLink ∧ y ∈ antoineComp w n '' antoineLink) : x = y := by
  refine eq_of_forall_dist_le fun ε hε => ?_
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < ε / 2 by positivity)
    (show (7 / 80 : ℝ) < 1 by norm_num)
  have := antoineComp_diam (h n).1 (h n).2
  linarith

theorem antoineCode_injective : Injective antoineCode := by
  intro w w' h
  funext n
  exact antoineComp_prefix (antoineCode_mem w (n + 1)) (h ▸ antoineCode_mem w' (n + 1)) n
    (Nat.lt_succ_self n)

theorem range_antoineCode : range antoineCode = antoineNecklaceR3 := by
  apply Subset.antisymm
  · rintro _ ⟨w, rfl⟩
    exact mem_iInter.2 fun n => mem_iUnion.2 ⟨w, antoineCode_mem w n⟩
  · intro x hx
    have hW : ∀ n, ∃ w : ℕ → Fin 64, x ∈ antoineComp w n '' antoineLink := fun n =>
      mem_iUnion.1 (mem_iInter.1 hx n)
    choose W hW using hW
    set w : ℕ → Fin 64 := fun k => W (k + 1) k
    have hmem : ∀ n, x ∈ antoineComp w n '' antoineLink := fun n => by
      rw [antoineComp_congr (w' := W n) fun k hk => antoineComp_prefix (hW (k + 1))
        (antoineComp_antitone (W n) hk (hW n)) k (Nat.lt_succ_self k)]
      exact hW n
    exact ⟨w, antoine_eq_of_mem fun n => ⟨antoineCode_mem w n, hmem n⟩⟩

theorem continuous_antoineCode : Continuous antoineCode := by
  refine continuous_iff_continuousAt.2 fun w => Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < ε / 2 by positivity)
    (show (7 / 80 : ℝ) < 1 by norm_num)
  have hcyl : (Set.pi (Finset.range n : Set ℕ) fun k => {w k}) ∈ 𝓝 w :=
    (isOpen_set_pi (Finset.finite_toSet _) fun _ _ => isOpen_discrete _).mem_nhds
      fun k _ => rfl
  filter_upwards [hcyl] with w' hw'
  have hcongr : antoineComp w' n = antoineComp w n := antoineComp_congr fun k hk =>
    hw' k (by simpa using hk)
  have := antoineComp_diam (antoineCode_mem w' n) (hcongr ▸ antoineCode_mem w n)
  linarith

/-- Antoine's necklace in `ℝ³` is homeomorphic to `(ℕ → Fin 64)`, through the coding map. -/
def antoineCodeHomeomorph : (ℕ → Fin 64) ≃ₜ antoineNecklaceR3 :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (fun w => ⟨antoineCode w, range_antoineCode ▸ mem_range_self w⟩)
      ⟨fun w w' h => antoineCode_injective (congrArg Subtype.val h), fun x => by
        have hx : (x : ℝ × ℝ × ℝ) ∈ range antoineCode := by rw [range_antoineCode]; exact x.2
        obtain ⟨w, hw⟩ := hx
        exact ⟨w, Subtype.ext hw⟩⟩)
    (continuous_antoineCode.subtype_mk _)

/-- `(ℕ → Fin 64) ≃ₜ (ℕ → Bool)`: `64 = 2⁶`. -/
def antoineFin64Homeomorph : (ℕ → Fin 64) ≃ₜ (ℕ → Bool) :=
  have e : Fin 64 ≃ (Fin 6 → Bool) := Fintype.equivOfCardEq (by simp)
  (Homeomorph.piCongrRight fun _ : ℕ => Homeomorph.ofDiscrete e).trans
    ((Continuous.homeoOfEquivCompactToT2 (f := (Equiv.curry ℕ (Fin 6) Bool).symm)
      (continuous_pi fun q => (continuous_apply q.2).comp (continuous_apply q.1))).trans
      (Homeomorph.piCongrLeft (Y := fun _ : ℕ => Bool) (Nat.divModEquiv 6).symm))

/-- Antoine's necklace in `ℝ³` is a Cantor set. -/
theorem antoineNecklaceR3_isCantorSubset : IsCantorSubset antoineNecklaceR3 :=
  ⟨antoineCodeHomeomorph.symm.trans
    (antoineFin64Homeomorph.trans cantorSetHomeomorphNatToBool.symm)⟩

theorem isCompact_antoineNecklaceR3 : IsCompact antoineNecklaceR3 :=
  range_antoineCode ▸ isCompact_range continuous_antoineCode

/-- Inverse stereographic projection `ℝ³ → S³`. -/
def antoineStereo (p : ℝ × ℝ × ℝ) : Sphere3 :=
  ⟨!₂[2 * p.1 / (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 + 1), 2 * p.2.1 / (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 + 1),
      2 * p.2.2 / (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 + 1),
      (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 - 1) / (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 + 1)], by
    have hN : 0 < p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 + 1 := by positivity
    rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Real.sqrt_eq_one, Fin.sum_univ_four]
    simp only [Real.norm_eq_abs, sq_abs]
    simp
    field_simp
    ring⟩

theorem continuous_antoineStereo : Continuous antoineStereo := by
  refine Continuous.subtype_mk ((PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)) _
  have hN : ∀ p : ℝ × ℝ × ℝ, p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 + 1 ≠ 0 := fun p => by positivity
  fin_cases i <;> simp <;> fun_prop (disch := exact hN _)

theorem antoineStereo_injective : Injective antoineStereo := by
  intro p q h
  have hc : ∀ k : Fin 4, (antoineStereo p : EuclideanSpace ℝ (Fin 4)) k =
      (antoineStereo q : EuclideanSpace ℝ (Fin 4)) k := fun k => by rw [h]
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  have h3 := hc 3
  simp only [antoineStereo] at h0 h1 h2 h3
  simp at h0 h1 h2 h3
  set Np := p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2
  set Nq := q.1 ^ 2 + q.2.1 ^ 2 + q.2.2 ^ 2
  have hp : 0 < Np + 1 := by positivity
  have hq : 0 < Nq + 1 := by positivity
  rw [div_eq_div_iff hp.ne' hq.ne'] at h0 h1 h2 h3
  have hN : Np = Nq := by linarith
  rw [hN] at h0 h1 h2
  have e1 : p.1 = q.1 := by nlinarith
  have e2 : p.2.1 = q.2.1 := by nlinarith
  have e3 : p.2.2 = q.2.2 := by nlinarith
  exact Prod.ext e1 (Prod.ext e2 e3)

/-- **Antoine's necklace** in `S³`: the image of `GX.antoineNecklaceR3` by the inverse
stereographic projection. -/
def antoineNecklace : Set Sphere3 := antoineStereo '' antoineNecklaceR3

/-- Antoine's necklace is a Cantor set (proved: the coding map is a homeomorphism from
`Fin 64 ^ ℕ ≃ₜ Bool ^ ℕ`). -/
theorem antoineNecklace_isCantorSubset : IsCantorSubset antoineNecklace := by
  haveI : CompactSpace antoineNecklaceR3 :=
    isCompact_iff_compactSpace.1 isCompact_antoineNecklaceR3
  obtain ⟨e⟩ := antoineNecklaceR3_isCantorSubset
  exact ⟨(Continuous.homeoOfEquivCompactToT2
    (f := Equiv.Set.image antoineStereo antoineNecklaceR3 antoineStereo_injective)
    ((continuous_antoineStereo.comp continuous_subtype_val).subtype_mk _)).symm.trans e⟩

theorem antoineNecklace_nonempty : antoineNecklace.Nonempty :=
  ⟨_, _, range_antoineCode ▸ mem_range_self (fun _ => 0), rfl⟩

/-- **Antoine's theorem** (cited `general_antoine`, not built) for the necklace built above,
`GX.antoineNecklace`, in the form the corrected `RamcovGX.tex:1578` uses: it is WILD (no
homeomorphism of `S³` carries it into a great circle), and at every point `x` of it, inside any
neighbourhood `V` of `x`, there are a closed piece `K ⊆ C` missing `x` (`K = C ∩ L`, `L` a link of
the construction inside `V` not containing `x`) and a loop at `x` off `C` (a path from `x` to a
meridian of `L` meeting `C` only at `x`, the meridian, the path back) which is essential in
`S³ ∖ K`. Its Cantor property is NOT part of this citation: it is proved,
`GX.antoineNecklace_isCantorSubset`. -/
theorem antoineNecklace_antoine :
    (¬ ∃ h : Sphere3 ≃ₜ Sphere3, h '' antoineNecklace ⊆ greatCircle3) ∧
      ∀ x ∈ antoineNecklace, ∀ V ∈ 𝓝 x, ∃ K : Set Sphere3, K ⊆ antoineNecklace ∧ IsClosed K ∧
        x ∉ K ∧ ∃ γ : Path x x, MemOmega (V ∩ antoineNecklaceᶜ) γ ∧
          ¬ HomotopicIn Kᶜ γ (Path.refl x) := by
  sorry -- SORRY(ex:wild_cantor_general_antoine): Antoine's theorem for the explicit necklace GX.antoineNecklace (built here; its Cantor property, nesting and the pairwise disjointness of the 64 links of each generation are PROVED). Missing: (1) the essential loop: a meridian of a link L of generation n is not null-homotopic in S³ ∖ (C ∩ L). This cannot go through any ABELIAN invariant (winding or linking numbers, maps to S¹, abelian coverings): H¹ of the complement of a closed subset of a Cantor set vanishes (Alexander duality), so every such invariant of the meridian is 0; by compactness of a null-homotopy it suffices to detect the meridian in the complement of each finite stage C_m ∩ L, m ≥ n (a union of 64^(m-n) solid tori), which needs, for every m, a non-abelian covering or representation of π₁(S³ ∖ (C_m ∩ L)) — an (m-n)-fold iterated lift through explicit coverings (the depth-2 instance of which is the dihedral invariant built for ex:consider_denote_absolute_galois) or Antoine's van Kampen computation of the chain-of-links group — and mathlib has neither van Kampen nor the fundamental group of a solid-torus complement; (2) accessibility: a path from each x ∈ C to the meridian meeting C only at x (an infinite concatenation through the gaps of the nested chains, with the diameter control); (3) wildness: a Cantor set carried into a great circle has a semi-locally simply connected complement (the complement of a closed subset of a tame arc), which with (1)-(2) excludes it — this needs the simple connectivity of S³ minus a compact subset of a circle, again a van Kampen-type argument.

/-- `ex:wild_cantor_general_antoine`, the wildness half: Antoine's necklace is a wild Cantor set
(Cantor: proved; wild: the cited `GX.antoineNecklace_antoine`). -/
theorem isWildCantor_antoineNecklace : IsWildCantor antoineNecklace :=
  ⟨antoineNecklace_isCantorSubset, antoineNecklace_antoine.1⟩

/-- `ex:wild_cantor_general_antoine` (`RamcovGX.tex:1578`), in the reading of DEC-58 (`S` is
Antoine's necklace), homotopy form: the complement of `GX.antoineNecklace` is NOT semi-locally
simply connected in `S³`. Proved from the essential-loop criterion
(`GX.sphere3_not_isSLSCIn_of_essential`); rests on the cited `GX.antoineNecklace_antoine`. -/
theorem antoineNecklace_not_isSLSCIn : ¬ IsSLSCIn antoineNecklaceᶜ := by
  obtain ⟨x, hx⟩ := antoineNecklace_nonempty
  exact sphere3_not_isSLSCIn_of_essential x (antoineNecklace_antoine.2 x hx)

/-- The existential corollary: some wild Cantor set of `S³` (Antoine's necklace) has a complement
that is not semi-locally simply connected. Rests on the cited `GX.antoineNecklace_antoine`. -/
theorem exists_wild_cantor_not_isSLSCIn : ∃ C : Set Sphere3, IsWildCantor C ∧ ¬ IsSLSCIn Cᶜ :=
  ⟨_, isWildCantor_antoineNecklace, antoineNecklace_not_isSLSCIn⟩

/-- `S³ = sphere(0,1) ⊆ ℝ⁴` has dimension `3 + 1` as an ambient space. -/
theorem sphere3_finrank_fact : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) :=
  ⟨by simp⟩

attribute [local instance] sphere3_finrank_fact

/-- `S³` is locally path-connected (a manifold). -/
theorem sphere3_locPathConnected : LocPathConnectedSpace Sphere3 :=
  ChartedSpace.locPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) _

/-- The complement of a closed subset of `S³` is semilocally simply connected (small caps
contract radially, `GX.sphere3_exists_nhds_loops_trivial`). -/
theorem sphere3_semilocallySimplyConnected_compl {C : Set Sphere3} (hC : IsClosed C) :
    SemilocallySimplyConnected (Cᶜ : Set Sphere3) := by
  intro y
  obtain ⟨W, hW, hWt⟩ := sphere3_exists_nhds_loops_trivial hC y.2
  refine ⟨Subtype.val ⁻¹' W, continuous_subtype_val.continuousAt.preimage_mem_nhds hW,
    fun γ hγ => ?_⟩
  obtain ⟨h1, h2, hom⟩ := homotopicIn_iff.1 (hWt (γ.map continuous_subtype_val) hγ)
  have e1 : pathToSub (γ.map continuous_subtype_val) h1 = γ := by ext; rfl
  have e2 : pathToSub (Path.refl (y : Sphere3)) h2 = Path.refl y := by ext; rfl
  rwa [e1, e2] at hom

/-- A Cantor subset of `S³` is closed. -/
theorem IsCantorSubset.isClosed {C : Set Sphere3} (hC : IsCantorSubset C) : IsClosed C := by
  obtain ⟨e⟩ := hC
  haveI : CompactSpace cantorSet := isCompact_iff_compactSpace.1 isCompact_cantorSet
  haveI := e.symm.compactSpace
  exact (isCompact_iff_compactSpace.2 this).isClosed

/-- For a closed `C ⊆ S³`, the literal (DEC-55) and homotopy forms of semi-local simple
connectedness of `S³ ∖ C` in `S³` agree. -/
theorem sphere3_isSLSCInCC_compl_iff {C : Set Sphere3} (hC : IsClosed C) :
    IsSLSCInCC Cᶜ ↔ IsSLSCIn Cᶜ :=
  haveI := sphere3_locPathConnected
  isSLSCInCC_iff hC.isOpen_compl (sphere3_semilocallySimplyConnected_compl hC)

/-- `ex:wild_cantor_general_antoine` (`RamcovGX.tex:1578`, DEC-58: `S` is Antoine's necklace),
literal reading (DEC-55) — stated, rests on the cited Antoine theorem
`GX.antoineNecklace_antoine` (tagged `sorry`): Antoine's necklace `GX.antoineNecklace` is a wild
Cantor set of `S³` whose complement is not semi-locally simply connected in `S³`. -/
theorem antoineNecklace_wild_not_isSLSCInCC :
    IsWildCantor antoineNecklace ∧ ¬ IsSLSCInCC antoineNecklaceᶜ :=
  ⟨isWildCantor_antoineNecklace, fun hcc => antoineNecklace_not_isSLSCIn
    ((sphere3_isSLSCInCC_compl_iff antoineNecklace_isCantorSubset.isClosed).1 hcc)⟩

/-- The existential corollary of `GX.antoineNecklace_wild_not_isSLSCInCC` (literal reading). -/
theorem exists_wild_cantor_not_isSLSCInCC :
    ∃ C : Set Sphere3, IsWildCantor C ∧ ¬ IsSLSCInCC Cᶜ :=
  ⟨_, antoineNecklace_wild_not_isSLSCInCC⟩

end WildCantor

end GX
