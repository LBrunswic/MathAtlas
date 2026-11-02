import GX.Branched.Galois
import GXScaffold.Topology.VanKampen
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# The examples closing §3.4 (l.1560–1583)

Packages WP-26h, WP-27f, WP-35h, WP-40e, WP-41r. `papers/gx`, `RamcovGX.tex:1560–1583`. Reworked to DEC-55
(literal compact-open reading of "almost trivial"), DEC-58 (`ex:wild_cantor_general_antoine` is
about Antoine's necklace), DEC-68 ((c) a tame knot is a locally polygonal set; (d) item 3 of
`ex:following_situations_semi_locally_simply` corrected, locally finite complexes; (e) the `γₙ` are
lollipop loops; (f) Antoine's necklace is one explicit necklace) and DEC-69
(`ex:consider_denote_absolute_galois` corrected to `Γ₂'` = the kernel of the mod-2 windings, whose
fibre is a Cantor set; DEC-58's normal-closure reading is refuted and kept as the record) and
DEC-82 (the necklace's wildness is certified too).

* **`ex:following_situations_semi_locally_simply`** — `RamcovGX.tex:1560` (CLOSED under DEC-68
  (c)(d), SCOPE (a)–(c)): the assembly `GX.following_situations_semi_locally_simply` (literal
  reading). Item 1 `GX.following_situations_finite` (`n ≥ 1` suffices,
  `GX.following_situations_finite_euclidean`); item 2 `GX.following_situations_tame` (`S` locally
  polygonal, `GX.IsLocallyPolygonal`; classical tame knots `GX.following_situations_tame_knot`);
  item 3, corrected, `GX.following_situations_simplicial` (`GX.HasFacesOfCardGe`), the
  counterexample as written `GX.following_situations_simplicial_false`.
* **`ex:consider_denote_absolute_galois`** — `RamcovGX.tex:1570` (CLOSED under DEC-69, SCOPE (d)):
  the assembly `GX.absolute_galois_corrected`: `ℂ ∖ S` is not semi-locally simply connected in
  `ℂ` (`GX.absGal_not_isSLSCInCC`); for `Γ₂' = GX.cantGamma`, the kernel of the mod-2 windings
  (`GX.mem_cantGamma_iff`), `Γ₂' \ ord(\widetilde Y^S) → ℂ` is a spread
  (`GX.cant_isSpread_cantProj`) and the fibre above `0` of its completion `GX.CantY₂` is a Cantor
  set (`GX.absGal_Y₂_fiber_cantor_corrected`). The record (DEC-69): the printed `Γ₂` is `Γ`
  (`GX.printedGamma2_eq_top`); for the normal closure the fibre is not compact
  (`GX.absGal_Y₂_fiber_not_cantor_simple`, `GX.absGal_Y₂_fiber_corrected_simple`).
* `ex:wild_cantor_general_antoine` — `RamcovGX.tex:1578` (stated, SCOPE (e)), for the ONE
  explicit necklace `GX.antoineNecklace` (DEC-58, DEC-68 (f)), built and proved a Cantor set
  (`GX.antoineNecklace_isCantorSubset`) and WILD (DEC-82: `GX.isWildCantor_antoineNecklace_of_res`,
  the tame side `GX.tameCantorSLSC` proved). The claim `GX.antoineNecklace_wild_not_isSLSCInCC`
  is derived sorry-free (`GX.antoineNecklace_wild_not_isSLSCInCC_of_top`) from Antoine's lemma
  for the top link `GX.AntoineMeridianEssentialTop` (the meridian of `L` is essential in
  `S³ ∖ C_k`, `k ≥ 1`), itself derived sorry-free (WP-41r, a van Kampen induction on `k`,
  `GX.antoineMeridianEssentialTop_of_firstGeneration`, on `GX.VanKampen`) from the FIRST
  generation `GX.AntoineFirstGeneration`, whose five collar facts are proved (WP-41r round 1,
  `GX.antoineFirstGeneration_of_chain`); the file's one `sorry` is its non-abelian heart
  `GX.antoineChainEssential` (the meridian of `L` is essential in `S³ ∖ C₁`).

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
| item 1: `n ≥ 2` | ✓ carried in the assembly; weakened to `n ≥ 1` in `GX.following_situations_finite_euclidean` (`E` nontrivial), finding |
| item 1: `Y` an `n`-manifold | ✓ `[ChartedSpace E Y]`, any real normed `E` |
| item 2: `Y` a 3-manifold | ⚠ weakened: local models in any finite-dimensional `E`, `dim ≥ 2` |
| item 2: `S` a tame knot | ✓ ruled (DEC-68 (c)): locally polygonal up to local homeomorphism (SCOPE (b)) |
| item 3: `Y` a simplicial complex of dimension `n` | ✓ corrected and ruled (DEC-68 (d)): every face in a face with `≥ n` vertices (false otherwise, connected counterexample); LOCALLY FINITE geometric complex, subspace topology (= weak topology there; mathlib has no weak topology); the bound on dimension not used |
| ex. 1570: `Y = ℝ²` | ✓ `ℂ` |
| ex. 1570: `Γ₂ = ⟨Γ[γₙ]²Γ⟩` | ✓ corrected and ruled (DEC-69): `Γ₂'` = the kernel of the mod-2 windings around the `1/n` (`GX.cantGamma`, `GX.mem_cantGamma_iff`); the printed one is `Γ`; the normal closure (DEC-58) is refuted, kept as the record |
| ex. 1570: "the fibre is a Cantor set" | ✓ for `Γ₂'` (`GX.absGal_Y₂_fiber_cantor_corrected`); the record: ✗ for the normal closure, not compact, infinite and totally disconnected (`GX.absGal_Y₂_fiber_not_cantor_simple`, `GX.absGal_Y₂_fiber_corrected_simple`) |
| ex. 1570: `γₙ` a simple loop around `(1/n,0)` | ✓ ruled (DEC-68 (e)): the lollipop loops `GX.absGalSimpleLoop` (used only by the recorded counterexample; `Γ₂'` is defined by windings); the general refutation takes any loops with the windings of simple loops, those around `1/(n+1)`, `n ≥ 2`, drawn in `GX.absGalR` (SCOPE (d)) |
| ex. 1570: "answers positively Problem 10.7 of MR2198590" | — bibliographic remark, not a mathematical assertion; not formalized |
| ex. 1578: `S` a wild Cantor set in `S³` | ✓ ruled (DEC-58, DEC-68 (f), DEC-82): one explicit Antoine necklace, built (`GX.antoineNecklace`), proved a Cantor set and proved WILD from the residual (`GX.isWildCantor_antoineNecklace_of_res`; the tame side, `GX.tameCantorSLSC`, sorry-free); the claim is proved for THIS necklace from `GX.AntoineMeridianEssentialTop`, itself reduced (WP-41r, van Kampen) to the first generation `GX.AntoineFirstGeneration`, and that (WP-41r round 1, the five collar facts proved) to its non-abelian heart `GX.AntoineChainEssential` (the file's one tagged `sorry`, SCOPE (e)) |
| "almost trivial" | ✓ literal compact-open reading (DEC-55) for both negative claims (`IsSLSCInCC`); positive results a fortiori |

## SCOPE (disclosed)

(a) Item 1: the codimension condition `n ≥ 2` is not needed for the notion `GX.IsSLSCIn` (as for
`rem:simple_cases`, WP-26f); `n ≥ 1` is needed for density. (b) Item 2: "tame knot" is read as
LOCALLY POLYGONAL (ruled, DEC-68 (c)): every point has an open neighbourhood `V` and a homeomorphism of `V` onto an
open subset of `E` carrying `V ∩ S` onto a finite union of segments (`GX.IsLocallyPolygonal`); this
covers the classical tame knots of `ℝ³` (images of polygonal knots by homeomorphisms of `ℝ³`,
`GX.isLocallyPolygonal_homeomorph_image`), and in a 3-manifold it is local tameness (equivalent to
tameness and to local flatness by Bing–Moise, which is NOT formalized). Being a knot (a circle) is
not used. (c) Item 3: `X = |K|` for a locally finite geometric complex of a real normed space,
`S` the union of the closed faces of dimension `≤ n − 2`; (ruled, DEC-68 (d)) the hypothesis "of dimension `n`" is replaced by
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
compact; whether it is perfect (no isolated point) is not formalized. That is the RECORD (DEC-69).
The CORRECTED example (DEC-69) takes `Γ₂' = GX.cantGamma`, the kernel of the mod-2 winding numbers
around the points `aₙ = 1/(n+1)` (`GX.mem_cantGamma_iff`), and is proved: the fibre above `0` of
`Y₂' = GX.CantY₂` is homeomorphic to `{0,1}^ℕ` (`GX.cantFiberHomeo`), hence a Cantor set
(`GX.cant_fiber_isCantor`). Mechanism: continuous square roots `sₙ` of `p - aₙ` on
`\widetilde{ℂ∖S}` (`GX.cantSq`), on which a deck transformation acts by `εₙ = (-1)^{w(aₙ)}`
(`GX.cantEps_fromPath`); over `D_k` the sign `σₙ = sₙ / i√(aₙ - z)`, `n < k`, is locally constant
(`GX.cantSigma_eventually`); the components of the preimage of `D_k` in `Γ₂' \ \widetilde{ℂ∖S}` are
exactly the sign classes `GX.cantZ k τ` (`GX.cantZ_comp`, `GX.cantZ_nonempty`). The hard half,
`GX.cant_mem_comp_of_sigma`, lifts a path of `D_k ∖ S` (`GX.cant_reach`) and corrects the endpoint
by a deck transformation preserving the component and realising the remaining sign pattern
(`GX.cantReal_of_eps`): that pattern is eventually constant (`GX.cant_eps_eventually`, a loop
stays away from `0`, so it winds equally around the small `aₙ`, `GX.cant_wind_eq_of_small`), and
every such pattern is a product of the patterns of the small circles around the `aₙ`, `n ≥ k`
(`GX.cantReal_flip`) and of the circle of radius `R_k` around `0` (`GX.cantReal_big`,
`GX.cant_cWinding_circ_in`, `GX.cant_cWinding_circ_out`), all inside `D_k`. The ends over `0` are
then the threads `D_k ↦ GX.cantZ k τ` (`GX.cantEnd`), bijectively (`GX.cantEnd_injective`,
`GX.cantEnd_surj`) and continuously (`GX.continuous_cantEnd`), and `{0,1}^ℕ` is compact. The
statement holds for every base point `y₀`. "Answers positively Problem 10.7 of MR2198590" is a
bibliographic remark and is not formalized. (e)
Example 1578, read by DEC-58 and DEC-68 (f): `S` is one explicit Antoine necklace, and it is built. In `ℝ³` (sup
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
coordinates: the longitude of each link winds once around the next (`GX.antoine_succ_wind`). The claim `GX.antoineNecklace_not_isSLSCInCC`
(literal reading; for closed `C ⊆ S³` the two readings agree, `GX.sphere3_isSLSCInCC_compl_iff`)
is proved from the criterion `GX.sphere3_not_isSLSCIn_of_essential` at the point
`x₀ = GX.antoineStereo GX.antoineP0`, `p₀ = (-70/73, -70/73, 0)` the fixed point of `g₀`, by
`GX.antoine_essential_loops`, from ONE residual: `GX.AntoineMeridianEssential`, for `n ≤ m` the
meridian `GX.antoineMeridian` of a link `L` of generation `n` (a circle of radius `3/14` around
the core, `GX.antoineMeridian_not_mem`) is not null-homotopic in `S³ ∖ (C_m ∩ L)`. Built around
it, sorry-free: link selection (in a neighbourhood `V` of `x₀`, `L = g₀ᵏ(g₁(L))` for `k` large,
`GX.antoineComp_diam`, `x₀ ∉ L`, `GX.antoineP0_not_mem_word_link`); accessibility (the vertical
segment above `p₀` meets the necklace only at `p₀`, `GX.antoineVert_not_mem_necklace`, by the
self-similarity `g₀(vert z) = vert(7z/80)` and the transfer `GX.antoine_mem_stage_of_comp`); the
based loop `g₀ᵏ(GX.antoineLoop0)` (up, across above the first stage, the meridian of `g₁(L)`,
back), off the necklace in `V`; conjugation `GX.antoine_homotopicIn_conj`; and the compactness
reduction `GX.antoine_homotopicIn_stage` (a null-homotopy has compact image, which misses some
finite stage, the stages being finite unions of links, `GX.antoineStage_isCompact`). Every
generation reduces to the top link by self-similarity (`GX.antoineMeridianEssentialStrict_of_top`:
the inverse similarity `GX.antoineCompInv`, conjugated by the stereographic chart, extends
continuously over the pole, `GX.continuous_antoinePhi`), and the equal-generation case is proved
(`GX.antoineMeridianEssential_self`: `(ρ - 7/8) + i z`, cut off far away, is a map
`S³ ∖ L → ℂ ∖ 0` under which the meridian winds once, `GX.antoineTheta`). Antoine's lemma
for every generation is PROVED from the first generation (WP-41r):
`GX.antoineMeridianEssentialTop_of_firstGeneration`, by `GX.antoine_pow_essential`, an induction
on `k` over all powers of the meridian: `S³ ∖ C_{k+1}` is `S³ ∖ C₁` with the 64 tubes
`Nⱼ ∖ C_{k+1}` (`GX.antoineN1`, round tubes `(ρ-7/8)²+z² < 1/16`) glued one at a time along
their collars (`GX.antoineA1`) by the injectivity consequence of a topological Seifert–van Kampen
theorem built for the purpose (`GX.VanKampen.homotopicIn_of_homotopicIn_union'`, on an
amalgamated product `Monoid.PushoutI`); on the tube's side the collar injects by self-similarity
(`GX.antoinePhi`) and the statement at `k`, the base `k = 0` being the winding number
(`GX.antoine_pow_essential_zero`). Of the six fixed-level facts about the closed chain `C₁` that
make up the first generation (`GX.AntoineFirstGeneration`), five are PROVED (WP-41r round 1,
`GX.antoineFirstGeneration_of_chain`): the tubes miss the other links (`GX.antoineTube_disjoint`),
the base points are joined off `C₁` (`GX.antoine_joined`), and the collar `Aⱼ = Nⱼ ∖ Lⱼ` is
path-connected and `π₁`-injective into the tube modulo the meridian and into `S³ ∖ C₁`
(`GX.antoine_collar_conn`, `GX.antoine_collar_mer`, `GX.antoine_collar_inj`), by the
classification of the collar's loops by two windings (`GX.antoine_collar_classify`) and the
longitude of `Lⱼ` winding once around `Lⱼ₊₁` (`GX.antoine_succ_wind`). The residual is the sixth,
the non-abelian heart, and is NOT formalized: `GX.antoineChainEssential`'s tagged `sorry`,
`GX.AntoineChainEssential` (no nonzero power of the meridian of `L` is null-homotopic in
`S³ ∖ C₁`; the meridian is null-homologous there, so no map to `ℂ ∖ 0` detects it; a
`D_∞`-representation from a Fox `ℤ`-colouring does, sending it to a translation of infinite
order, and building that flat structure is the obstruction). Wildness (DEC-82): a Cantor set of `S³` is tame if a
homeomorphism of `S³` carries it into a great circle, wild otherwise (`GX.IsWildCantor`). The
complement of a Cantor subset `C` of a great circle `Γ` IS semi-locally simply connected
(`GX.tameCantorSLSC`, proved): near a point of `Γ` two points off `C` are joined through a
midpoint pushed off `Γ` transversally (`GX.gc_join`), and a loop at a point of `Γ ∖ C` is
null-homotopic off `C` by general position (`GX.gc_loop_null`: a fine polygon whose vertices are
pushed off the plane of `Γ` successively transversally, `GX.gcSeq`, meets that plane only at its
base point, and the cone on the base point misses `C`). As this property is carried by
homeomorphisms (`GX.IsSLSCIn.map_homeomorph`) and fails for the necklace, the necklace is wild
(`GX.isWildCantor_antoineNecklace_of_res`); with the claim, `GX.antoineNecklace_wild_not_isSLSCInCC`
and `GX.exists_wild_cantor_not_isSLSCIn(CC)`. Side
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

/-- **`ex:following_situations_semi_locally_simply`** (`RamcovGX.tex:1560`), certified under
DEC-68 (c) (a tame knot is a locally polygonal set) and (d) (item 3 corrected: a locally finite
complex every face of which lies in a face with `≥ n` vertices), in the literal reading of
"almost trivial" (DEC-55): (1) `Y` an `n`-manifold, `n ≥ 2`, `S` finite; (2) `Y` a 3-manifold,
`S` a tame knot; (3) `Y` a simplicial complex of dimension `n` (corrected), `S` its
`(n-2)`-skeleton — in each case `Y ∖ S` is semi-locally simply connected in `Y`. -/
theorem following_situations_semi_locally_simply.{u} :
    (∀ n : ℕ, 2 ≤ n → ∀ (Y : Type u) [TopologicalSpace Y]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) Y] (S : Set Y), S.Finite → IsSLSCInCC Sᶜ) ∧
    (∀ (Y : Type u) [TopologicalSpace Y] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y] (S : Set Y),
      IsLocallyPolygonal (EuclideanSpace ℝ (Fin 3)) S → IsSLSCInCC Sᶜ) ∧
    (∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] (K : Geometry.SimplicialComplex ℝ E),
      LocallyFinite (fun τ : K.faces => convexHull ℝ ((τ : Finset E) : Set E)) → ∀ n : ℕ,
      HasFacesOfCardGe K n →
      IsSLSCInCC (((↑) : K.space → E) ⁻¹' (⋃ s ∈ skeletonFaces K n, convexHull ℝ (s : Set E))ᶜ)) :=
  by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn Y _ _ S hS
    exact (following_situations_finite_euclidean (n := n) (by omega) hS).isSLSCInCC
  · intro Y _ _ S hS
    exact following_situations_tame_cc (by rw [finrank_euclideanSpace_fin]; norm_num) hS
  · intro E _ _ K hK n hf
    exact following_situations_simplicial_cc K hK hf

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
this is the property `GX.antoine_essential_loops` gives for the necklace. -/
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

/-! ### Antoine's theorem: the reduction to the residual `GX.AntoineMeridianEssential` -/

/-- Half-extent along `z` of a link of type `t`, in units of `1/640`. -/
def antoineEz : Fin 3 → ℤ
  | 0 => 7
  | 1 => 56
  | 2 => 56

theorem antoineMap_bounds_z (i : Fin 64) {p : ℝ × ℝ × ℝ} (hp : p ∈ antoineLink) :
    |(antoineMap i p).2.2| ≤ antoineEz (antoineT i) / 640 := by
  obtain ⟨hz, hm, -⟩ := hp
  have hx : |p.1| ≤ 1 := (le_max_left _ _).trans hm
  have hy : |p.2.1| ≤ 1 := (le_max_right _ _).trans hm
  rcases antoineT_cases i with h | h | h <;>
    simp only [antoineMap, h, antoinePerm, antoineEz, abs_mul,
      abs_of_pos (show (0 : ℝ) < 7 / 80 by norm_num)] <;> push_cast <;> linarith

theorem antoineComp_succ' (w : ℕ → Fin 64) (n : ℕ) :
    antoineComp w (n + 1) = antoineMap (w 0) ∘ antoineComp (fun k => w (k + 1)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show antoineComp w (n + 1) ∘ antoineMap (w (n + 1)) = _
    rw [ih]; rfl

theorem antoineComp_mem_link (w : ℕ → Fin 64) (n : ℕ) {p : ℝ × ℝ × ℝ} (hp : p ∈ antoineLink) :
    antoineComp w n p ∈ antoineLink := by
  have := antoineComp_antitone w (Nat.zero_le n) ⟨p, hp, rfl⟩
  simpa [antoineComp] using this

theorem antoine_mem_stage_of_map {i : Fin 64} {q : ℝ × ℝ × ℝ} (hq : q ∈ antoineLink) {j : ℕ}
    (h : antoineMap i q ∈ antoineStage (j + 1)) : q ∈ antoineStage j := by
  obtain ⟨w, hw⟩ := mem_iUnion.1 h
  obtain ⟨r, hr, hrq⟩ := hw
  rw [antoineComp_succ'] at hrq
  have hr' := antoineComp_mem_link (fun k => w (k + 1)) j hr
  by_cases hi : w 0 = i
  · subst hi
    exact mem_iUnion.2 ⟨_, r, hr, antoineMap_injective _ hrq⟩
  · exact absurd (Set.disjoint_left.1 (antoineMap_disjoint hi) ⟨_, hr', hrq⟩ ⟨q, hq, rfl⟩) id

theorem antoine_mem_stage_of_comp (u : ℕ → Fin 64) (k : ℕ) {q : ℝ × ℝ × ℝ}
    (hq : q ∈ antoineLink) {j : ℕ} (h : antoineComp u k q ∈ antoineStage (j + k)) :
    q ∈ antoineStage j := by
  induction k generalizing q j with
  | zero => simpa [antoineComp] using h
  | succ k ih =>
    have h' : antoineComp u k (antoineMap (u k) q) ∈ antoineStage ((j + 1) + k) := by
      rw [show j + 1 + k = j + (k + 1) by omega]; exact h
    exact antoine_mem_stage_of_map hq (ih (antoineMap_mem _ hq) h')

theorem antoine_mem_necklace_of_comp (u : ℕ → Fin 64) (k : ℕ) {q : ℝ × ℝ × ℝ}
    (hq : q ∈ antoineLink) (h : antoineComp u k q ∈ antoineNecklaceR3) : q ∈ antoineNecklaceR3 :=
  mem_iInter.2 fun j => antoine_mem_stage_of_comp u k hq (mem_iInter.1 h (j + k))

theorem antoineNecklaceR3_subset_stage (n : ℕ) : antoineNecklaceR3 ⊆ antoineStage n :=
  iInter_subset _ n

theorem antoine_mem_stage_one {p : ℝ × ℝ × ℝ} (h : p ∈ antoineStage 1) :
    ∃ i : Fin 64, ∃ q ∈ antoineLink, antoineMap i q = p := by
  obtain ⟨w, q, hq, e⟩ := mem_iUnion.1 h
  exact ⟨w 0, q, hq, e⟩

theorem antoineZ_zero : antoineZ 0 = (-560, -560) := by decide
theorem antoineT_zero : antoineT 0 = 0 := by decide
theorem antoineZ_one : antoineZ 1 = (-490, -560) := by decide
theorem antoineT_one : antoineT 1 = 1 := by decide

/-- The fixed point of `g₀`, a point of the necklace. -/
def antoineP0 : ℝ × ℝ × ℝ := (-(70 / 73), -(70 / 73), 0)

theorem antoineMap_zero_p0 : antoineMap 0 antoineP0 = antoineP0 := by
  simp only [antoineMap, antoineZ_zero, antoineT_zero, antoinePerm, antoineP0]
  ext <;> push_cast <;> ring

theorem antoineP0_mem : antoineP0 ∈ antoineLink := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [antoineP0] <;> norm_num

theorem antoineComp_zero_p0 (k : ℕ) : antoineComp (fun _ => 0) k antoineP0 = antoineP0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show antoineComp _ k (antoineMap 0 antoineP0) = _
    rw [antoineMap_zero_p0, ih]

theorem antoineP0_mem_comp (k : ℕ) : antoineP0 ∈ antoineComp (fun _ => 0) k '' antoineLink :=
  ⟨_, antoineP0_mem, antoineComp_zero_p0 k⟩

theorem antoineP0_mem_necklace : antoineP0 ∈ antoineNecklaceR3 :=
  mem_iInter.2 fun k => mem_iUnion.2 ⟨_, antoineP0_mem_comp k⟩


theorem antoine_sep_p0 : ∀ i : Fin 64, i ≠ 0 →
    73 * antoineEx (antoineT i) < |-44800 - 73 * (antoineZ i).1| ∨
      73 * antoineEy (antoineT i) < |-44800 - 73 * (antoineZ i).2| := by decide

theorem antoine_sep_mer : ∀ i : Fin 64, i ≠ 1 →
    antoineEx (antoineT i) < |-490 - (antoineZ i).1| ∨
      antoineEy (antoineT i) + 12 < |-560 - (antoineZ i).2| := by decide

theorem antoineEz_le (t : Fin 3) : antoineEz t ≤ 56 := by fin_cases t <;> decide

/-- Points of the link above the plane `z = 56/640` are off the first stage. -/
theorem antoine_not_mem_stage_one_of_z {p : ℝ × ℝ × ℝ} (hp : 56 / 640 < |p.2.2|) :
    p ∉ antoineStage 1 := by
  intro h
  obtain ⟨i, q, hq, rfl⟩ := antoine_mem_stage_one h
  have := (antoineMap_bounds i hq).2.2
  linarith

/-- The vertical segment above `p₀`. -/
def antoineVert (z : ℝ) : ℝ × ℝ × ℝ := (-(70 / 73), -(70 / 73), z)

theorem antoineVert_zero : antoineVert 0 = antoineP0 := rfl

theorem antoineVert_mem {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ 1 / 8) : antoineVert z ∈ antoineLink := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [antoineVert, abs_neg]
  · rw [abs_of_nonneg h0]; exact h1
  · rw [max_self, abs_of_pos (by norm_num : (0:ℝ) < 70 / 73)]; norm_num
  · rw [max_self, abs_of_pos (by norm_num : (0:ℝ) < 70 / 73)]; norm_num

theorem antoineVert_not_mem_stage_one {z : ℝ} (hz : 7 / 640 < z) : antoineVert z ∉ antoineStage 1 := by
  intro h
  obtain ⟨i, q, hq, hiq⟩ := antoine_mem_stage_one h
  have hb := antoineMap_bounds i hq
  rw [hiq] at hb
  by_cases hi : i = 0
  · subst hi
    have := antoineMap_bounds_z 0 hq
    rw [hiq, antoineT_zero] at this
    simp only [antoineVert, antoineEz] at this
    rw [abs_of_pos (by linarith)] at this
    push_cast at this; linarith
  · simp only [antoineVert] at hb
    rcases antoine_sep_p0 i hi with h | h
    · have e : (-(70 / 73 : ℝ)) - ((antoineZ i).1 : ℝ) / 640 =
          ((-44800 - 73 * (antoineZ i).1 : ℤ) : ℝ) / 46720 := by push_cast; ring
      have h' := (Int.cast_lt (R := ℝ)).2 h
      have hb1 := hb.1
      rw [e, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 46720), div_le_div_iff₀ (by norm_num)
        (by norm_num)] at hb1
      push_cast at h' hb1
      linarith
    · have e : (-(70 / 73 : ℝ)) - ((antoineZ i).2 : ℝ) / 640 =
          ((-44800 - 73 * (antoineZ i).2 : ℤ) : ℝ) / 46720 := by push_cast; ring
      have h' := (Int.cast_lt (R := ℝ)).2 h
      have hb1 := hb.2.1
      rw [e, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 46720), div_le_div_iff₀ (by norm_num)
        (by norm_num)] at hb1
      push_cast at h' hb1
      linarith

theorem antoineMap_zero_vert (z : ℝ) : antoineMap 0 (antoineVert z) = antoineVert (7 / 80 * z) := by
  simp only [antoineMap, antoineZ_zero, antoineT_zero, antoinePerm, antoineVert]
  ext <;> push_cast <;> ring

theorem antoineStage_antitone {n m : ℕ} (h : n ≤ m) : antoineStage m ⊆ antoineStage n := by
  induction m, h using Nat.le_induction with
  | base => exact subset_rfl
  | succ m _ ih => exact (antoineStage_succ_subset m).trans ih

theorem antoineVert_not_mem_stage (k : ℕ) : ∀ z : ℝ, (7 / 80) ^ (k + 1) / 8 < z → z ≤ 1 / 8 →
    antoineVert z ∉ antoineStage (k + 1) := by
  induction k with
  | zero =>
    intro z hz _
    exact antoineVert_not_mem_stage_one (by norm_num at hz; linarith)
  | succ k ih =>
    intro z hz hz1
    by_cases hbig : 7 / 640 < z
    · exact fun h => antoineVert_not_mem_stage_one hbig (antoineStage_antitone (by omega) h)
    · replace hbig := not_lt.1 hbig
      have hz' : (7 / 80) ^ (k + 1) / 8 < 80 / 7 * z := by
        rw [pow_succ] at hz; nlinarith
      have hz'1 : 80 / 7 * z ≤ 1 / 8 := by nlinarith
      have hpos : 0 ≤ 80 / 7 * z := le_trans (by positivity) hz'.le
      intro h
      have e : antoineVert z = antoineMap 0 (antoineVert (80 / 7 * z)) := by
        rw [antoineMap_zero_vert]; congr 1; ring
      rw [e] at h
      exact ih _ hz' hz'1 (antoine_mem_stage_of_map (antoineVert_mem hpos hz'1) h)

theorem antoineVert_not_mem_necklace {z : ℝ} (h0 : 0 < z) (h1 : z ≤ 1 / 8) :
    antoineVert z ∉ antoineNecklaceR3 := by
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show 0 < 8 * z by positivity)
    (show (7 / 80 : ℝ) < 1 by norm_num)
  refine fun h => antoineVert_not_mem_stage k z ?_ h1 (antoineNecklaceR3_subset_stage _ h)
  have : (7 / 80 : ℝ) ^ (k + 1) ≤ (7 / 80) ^ k :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ k)
  linarith

/-- The base point of the meridian of the link `L`. -/
def antoineMerPt : ℝ × ℝ × ℝ := (0, 7 / 8 + 3 / 14, 0)

/-- The meridian of the link `L`: the circle of radius `3/14` around the point `(0, 7/8, 0)` of
the core square, in the plane `x = 0` (it links the core of `L` once). -/
def antoineMeridian : Path antoineMerPt antoineMerPt where
  toFun t := (0, 7 / 8 + 3 / 14 * Real.cos (2 * Real.pi * t), 3 / 14 * Real.sin (2 * Real.pi * t))
  continuous_toFun := by fun_prop
  source' := by simp [antoineMerPt]
  target' := by simp [antoineMerPt]

theorem antoineMeridian_apply (t : unitInterval) : antoineMeridian t =
    (0, 7 / 8 + 3 / 14 * Real.cos (2 * Real.pi * t), 3 / 14 * Real.sin (2 * Real.pi * t)) := rfl

/-- The meridian misses the link. -/
theorem antoineMeridian_not_mem (t : unitInterval) : antoineMeridian t ∉ antoineLink := by
  rintro ⟨hz, hm, hm'⟩
  rw [antoineMeridian_apply] at hz hm hm'
  simp only [abs_zero] at hm hm'
  set c := Real.cos (2 * Real.pi * t)
  set s := Real.sin (2 * Real.pi * t)
  have hcs : s ^ 2 + c ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  have hc1 : -1 ≤ c := Real.neg_one_le_cos _
  have hpos : 0 ≤ 7 / 8 + 3 / 14 * c := by linarith
  rw [max_eq_right (abs_nonneg _), abs_of_nonneg hpos] at hm hm'
  rw [abs_le] at hz
  nlinarith

/-- The meridian of the first link `g₁(L)`, inside `L`. -/
def antoineMer1 : Path (antoineMap 1 antoineMerPt) (antoineMap 1 antoineMerPt) :=
  antoineMeridian.map (continuous_antoineMap 1)

theorem antoineMer1_apply (t : unitInterval) : antoineMer1 t =
    (-(490 / 640), -(560 / 640) + 7 / 80 * (3 / 14 * Real.sin (2 * Real.pi * t)),
      7 / 80 * (7 / 8 + 3 / 14 * Real.cos (2 * Real.pi * t))) := by
  show antoineMap 1 (antoineMeridian t) = _
  simp only [antoineMeridian_apply, antoineMap, antoineZ_one, antoineT_one, antoinePerm]
  ext <;> push_cast <;> ring

theorem antoineMer1_mem (t : unitInterval) : antoineMer1 t ∈ antoineLink := by
  rw [antoineMer1_apply]
  have hs1 := Real.sin_le_one (2 * Real.pi * t)
  have hs2 := Real.neg_one_le_sin (2 * Real.pi * t)
  have hc1 := Real.cos_le_one (2 * Real.pi * t)
  have hc2 := Real.neg_one_le_cos (2 * Real.pi * t)
  refine ⟨?_, ?_, ?_⟩ <;> dsimp only
  · rw [abs_le]; constructor <;> nlinarith
  · rw [max_le_iff, abs_le, abs_le]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith
  · exact le_max_of_le_right (by rw [abs_of_neg (by nlinarith)]; nlinarith)

theorem antoineMer1_not_mem_stage_one (t : unitInterval) : antoineMer1 t ∉ antoineStage 1 := by
  intro h
  obtain ⟨i, q, hq, hiq⟩ := antoine_mem_stage_one h
  by_cases hi : i = 1
  · subst hi
    exact antoineMeridian_not_mem t (antoineMap_injective 1 hiq ▸ hq)
  · have hb := antoineMap_bounds i hq
    rw [hiq, antoineMer1_apply] at hb
    have hs1 := Real.sin_le_one (2 * Real.pi * t)
    have hs2 := Real.neg_one_le_sin (2 * Real.pi * t)
    obtain ⟨hb1, hb2, -⟩ := hb
    dsimp only at hb1 hb2
    rcases antoine_sep_mer i hi with h | h
    · have h' := (Int.cast_lt (R := ℝ)).2 h
      push_cast at h'
      have e : -(490 / 640 : ℝ) - ((antoineZ i).1 : ℝ) / 640 = (-490 - ((antoineZ i).1 : ℝ)) / 640 := by ring
      rw [e, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 640), div_le_div_iff_of_pos_right (by norm_num)] at hb1
      linarith
    · have h' := (Int.cast_lt (R := ℝ)).2 h
      push_cast at h'
      have e : -(560 / 640 : ℝ) + 7 / 80 * (3 / 14 * Real.sin (2 * Real.pi * t)) -
          ((antoineZ i).2 : ℝ) / 640 = ((-560 - ((antoineZ i).2 : ℝ)) + 12 * Real.sin (2 * Real.pi * t)) / 640 := by ring
      rw [e, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 640), div_le_div_iff_of_pos_right (by norm_num)] at hb2
      have := abs_sub_abs_le_abs_sub (-560 - ((antoineZ i).2 : ℝ)) (-(12 * Real.sin (2 * Real.pi * t)))
      rw [sub_neg_eq_add, abs_neg, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 12)] at this
      have hsa : |Real.sin (2 * Real.pi * t)| ≤ 1 := Real.abs_sin_le_one _
      linarith

/-- A straight segment of `ℝ³`. -/
def antoineSeg (a b : ℝ × ℝ × ℝ) : Path a b where
  toFun t := a + (t : ℝ) • (b - a)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

theorem antoineSeg_apply (a b : ℝ × ℝ × ℝ) (t : unitInterval) : antoineSeg a b t =
    (a.1 + t * (b.1 - a.1), a.2.1 + t * (b.2.1 - a.2.1), a.2.2 + t * (b.2.2 - a.2.2)) := by
  simp only [antoineSeg, Path.coe_mk_mk]
  ext <;> simp

/-- The vertical segment from `p₀` up to the top face of `L`. -/
def antoineUp : Path antoineP0 (antoineVert (1 / 8)) where
  toFun t := antoineVert ((t : ℝ) / 8)
  continuous_toFun := by unfold antoineVert; fun_prop
  source' := by simp [antoineVert, antoineP0]
  target' := by simp [antoineVert]

theorem antoineUp_apply (t : unitInterval) : antoineUp t = antoineVert ((t : ℝ) / 8) := rfl

/-- The segment from the top of `antoineUp` to the base point of the meridian of `g₁(L)`, at
heights `> 56/640`, above the first stage. -/
def antoineAcross : Path (antoineVert (1 / 8)) (antoineMap 1 antoineMerPt) :=
  antoineSeg _ _

theorem antoineMap_one_merPt :
    antoineMap 1 antoineMerPt = (-(49 / 64), -(7 / 8), 61 / 640) := by
  simp only [antoineMap, antoineZ_one, antoineT_one, antoinePerm, antoineMerPt]
  ext <;> push_cast <;> ring

theorem antoineAcross_apply (t : unitInterval) : antoineAcross t =
    (-(70 / 73) + (t : ℝ) * (-(49 / 64) + 70 / 73), -(70 / 73) + (t : ℝ) * (-(7 / 8) + 70 / 73),
      1 / 8 + (t : ℝ) * (61 / 640 - 1 / 8)) := by
  rw [antoineAcross, antoineSeg_apply, antoineMap_one_merPt]
  simp only [antoineVert]
  ext <;> ring

theorem antoineAcross_mem (t : unitInterval) :
    antoineAcross t ∈ antoineLink ∧ antoineAcross t ∉ antoineStage 1 := by
  rw [antoineAcross_apply]
  have h0 := t.2.1
  have h1 := t.2.2
  refine ⟨⟨?_, ?_, ?_⟩, antoine_not_mem_stage_one_of_z ?_⟩ <;> dsimp only
  · rw [abs_le]; constructor <;> nlinarith
  · rw [max_le_iff, abs_le, abs_le]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith
  · exact le_max_of_le_right (by rw [abs_of_neg (by nlinarith)]; nlinarith)
  · rw [abs_of_pos (by nlinarith)]; nlinarith

/-- From `p₀` to the base point of the meridian of `g₁(L)`. -/
def antoineTail : Path antoineP0 (antoineMap 1 antoineMerPt) := antoineUp.trans antoineAcross

/-- The based loop at `p₀`: up, across, the meridian of `g₁(L)`, back. -/
def antoineLoop0 : Path antoineP0 antoineP0 := (antoineTail.trans antoineMer1).trans antoineTail.symm

theorem antoine_memOmega_trans {X : Type*} [TopologicalSpace X] {U : Set X} {x y z : X}
    {p : Path x y} {q : Path y z} (hp : MemOmega U p) (hq : MemOmega U q) (hy : y ∈ U) :
    MemOmega U (p.trans q) := by
  intro t h0 h1
  rw [Path.trans_apply]
  split_ifs with h
  · rcases eq_or_lt_of_le h with h' | h'
    · convert hy using 1
      convert p.target using 2
      ext; simp [h']
    · exact hp _ (show (0:ℝ) < 2 * (t:ℝ) by linarith) (show 2 * (t:ℝ) < 1 by linarith)
  · push Not at h
    exact hq _ (show (0:ℝ) < 2 * (t:ℝ) - 1 by linarith) (show 2 * (t:ℝ) - 1 < 1 by linarith)

theorem antoine_memOmega_symm {X : Type*} [TopologicalSpace X] {U : Set X} {x y : X}
    {p : Path x y} (hp : MemOmega U p) : MemOmega U p.symm := fun t h0 h1 => by
  rw [Path.symm_apply]
  exact hp _ (by rw [unitInterval.coe_symm_eq]; linarith) (by rw [unitInterval.coe_symm_eq]; linarith)

theorem antoine_memOmega_of_forall {X : Type*} [TopologicalSpace X] {U : Set X} {x y : X}
    {p : Path x y} (hp : ∀ t, p t ∈ U) : MemOmega U p := fun t _ _ => hp t

/-- Points of `L` off the necklace, and `p₀`. -/
def antoineGood : Set (ℝ × ℝ × ℝ) := {q | q ∈ antoineLink ∧ q ∉ antoineNecklaceR3}

theorem antoineTail_mem (t : unitInterval) :
    antoineTail t ∈ antoineLink ∧ (antoineTail t = antoineP0 ∨ antoineTail t ∉ antoineNecklaceR3) := by
  have hU : ∀ s, antoineUp s ∈ antoineLink ∧ (antoineUp s = antoineP0 ∨
      antoineUp s ∉ antoineNecklaceR3) := fun s => by
    rw [antoineUp_apply]
    have h0 := s.2.1
    have h1 := s.2.2
    refine ⟨antoineVert_mem (by positivity) (by linarith), ?_⟩
    rcases eq_or_lt_of_le h0 with h | h
    · left; rw [← h]; simp [antoineVert, antoineP0]
    · right; exact antoineVert_not_mem_necklace (by positivity) (by linarith)
  have hA : ∀ s, antoineAcross s ∈ antoineLink ∧ (antoineAcross s = antoineP0 ∨
      antoineAcross s ∉ antoineNecklaceR3) := fun s =>
    ⟨(antoineAcross_mem s).1, Or.inr fun h => (antoineAcross_mem s).2
      (antoineNecklaceR3_subset_stage 1 h)⟩
  exact path_trans_mem (W := {q | q ∈ antoineLink ∧ (q = antoineP0 ∨ q ∉ antoineNecklaceR3)})
    hU hA t

theorem antoineTail_memOmega : MemOmega antoineGood antoineTail := by
  refine antoine_memOmega_trans (fun s h0 _ => ?_) (antoine_memOmega_of_forall fun s =>
    ⟨(antoineAcross_mem s).1, fun h => (antoineAcross_mem s).2
      (antoineNecklaceR3_subset_stage 1 h)⟩) ⟨antoineVert_mem (by norm_num) le_rfl,
        antoineVert_not_mem_necklace (by norm_num) le_rfl⟩
  rw [antoineUp_apply]
  exact ⟨antoineVert_mem (by positivity) (by linarith [s.2.2]),
    antoineVert_not_mem_necklace (by positivity) (by linarith [s.2.2])⟩

theorem antoineMer1_good (t : unitInterval) : antoineMer1 t ∈ antoineGood :=
  ⟨antoineMer1_mem t, fun h => antoineMer1_not_mem_stage_one t (antoineNecklaceR3_subset_stage 1 h)⟩

theorem antoineLoop0_memOmega : MemOmega antoineGood antoineLoop0 :=
  antoine_memOmega_trans (antoine_memOmega_trans antoineTail_memOmega
    (antoine_memOmega_of_forall antoineMer1_good) (by simpa using antoineMer1_good 0))
    (antoine_memOmega_symm antoineTail_memOmega) (by simpa using antoineMer1_good 0)

open Path.Homotopic.Quotient in
/-- A conjugate `T M T⁻¹` of a loop `M` null-homotopic in `U` makes `M` null-homotopic in `U`. -/
theorem antoine_homotopicIn_conj {X : Type*} [TopologicalSpace X] {U : Set X} {x y : X}
    {T : Path x y} {M : Path y y} (hT : ∀ t, T t ∈ U) (hM : ∀ t, M t ∈ U)
    (h : HomotopicIn U ((T.trans M).trans T.symm) (Path.refl x)) :
    HomotopicIn U M (Path.refl y) := by
  have hx : x ∈ U := T.source ▸ hT 0
  have hy : y ∈ U := T.target ▸ hT 1
  have hRx : ∀ t, (Path.refl x) t ∈ U := fun _ => hx
  have hRy : ∀ t, (Path.refl y) t ∈ U := fun _ => hy
  rw [homotopicIn_iff_mk (path_trans_mem (path_trans_mem hT hM) (path_symm_mem hT)) hRx,
    pathToSub_trans _ _ (path_trans_mem hT hM) (path_symm_mem hT), pathToSub_trans _ _ hT hM,
    pathToSub_symm _ hT, mk_trans, mk_trans, mk_symm] at h
  rw [homotopicIn_iff_mk hM hRy]
  have e1 : pathToSub (Path.refl x) hRx = Path.refl (⟨x, hx⟩ : U) := by ext; rfl
  have e2 : pathToSub (Path.refl y) hRy = Path.refl (⟨y, hy⟩ : U) := by ext; rfl
  rw [e1, mk_refl] at h
  rw [e2, mk_refl]
  have h2 := congrArg (fun q => trans (symm (mk (pathToSub T hT))) (trans q (mk (pathToSub T hT)))) h
  simp only [trans_assoc, symm_trans, trans_refl, refl_trans] at h2
  rw [← trans_assoc, symm_trans, refl_trans] at h2
  exact h2

/-- Transport of null-homotopy along a pointwise equality of loops. -/
theorem antoine_homotopicIn_refl_congr {X : Type*} [TopologicalSpace X] {U : Set X} {x y : X}
    {P : Path x x} {Q : Path y y} (hxy : x = y) (hPQ : ∀ t, P t = Q t)
    (h : HomotopicIn U P (Path.refl x)) : HomotopicIn U Q (Path.refl y) := by
  subst hxy
  obtain rfl : P = Q := Path.ext (funext hPQ)
  exact h

/-- The stage `n` is a FINITE union of links, hence compact. -/
theorem antoineStage_isCompact (n : ℕ) : IsCompact (antoineStage n) := by
  have e : antoineStage n = ⋃ u : Fin n → Fin 64,
      antoineComp (fun j => if h : j < n then u ⟨j, h⟩ else 0) n '' antoineLink := by
    apply Subset.antisymm
    · refine iUnion_subset fun w => ?_
      refine subset_iUnion_of_subset (fun j => w j) ?_
      rw [antoineComp_congr (w' := fun j => if h : j < n then w j else 0) fun k hk => by
        simp [hk]]
    · exact iUnion_subset fun u => subset_iUnion_of_subset _ subset_rfl
  rw [e]
  exact isCompact_iUnion fun u => antoineLink_isCompact.image (continuous_antoineComp _ n)

/-- **The compactness reduction.** A null-homotopy in the complement of `C ∩ L` (`L` closed) has
compact image, which misses `C_m ∩ L` for some (every large) finite stage `m`. -/
theorem antoine_homotopicIn_stage {L : Set (ℝ × ℝ × ℝ)} (hL : IsClosed L) {x : Sphere3}
    {γ : Path x x} (h : HomotopicIn (antoineStereo '' (antoineNecklaceR3 ∩ L))ᶜ γ (Path.refl x))
    (n : ℕ) : ∃ m, n ≤ m ∧
      HomotopicIn (antoineStereo '' (antoineStage m ∩ L))ᶜ γ (Path.refl x) := by
  obtain ⟨F, hF⟩ := h
  set A := range F
  have hA : IsCompact A := isCompact_range F.continuous
  set t : ℕ → Set Sphere3 := fun i => A ∩ antoineStereo '' (antoineStage (i + n) ∩ L)
  have hK : ∀ i, IsClosed (antoineStereo '' (antoineStage (i + n) ∩ L)) := fun i =>
    (((antoineStage_isCompact _).inter_right hL).image continuous_antoineStereo).isClosed
  have hcl : ∀ i, IsClosed (t i) := fun i => hA.isClosed.inter (hK i)
  have hdec : ∀ i, t (i + 1) ⊆ t i := fun i => inter_subset_inter_right _ (image_mono
    (inter_subset_inter_left _ (by
      rw [show i + 1 + n = i + n + 1 by omega]; exact antoineStage_succ_subset _)))
  by_cases hne : ∀ i, (t i).Nonempty
  · exfalso
    obtain ⟨y, hy⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t hdec
      hne (hA.inter_right (hK 0)) hcl
    have hy' : ∀ i, y ∈ t i := mem_iInter.1 hy
    obtain ⟨z, hz⟩ := (hy' 0).1
    obtain ⟨p, hp, hpy⟩ := (hy' 0).2
    have hpC : p ∈ antoineNecklaceR3 := mem_iInter.2 fun j => by
      obtain ⟨q, hq, hqy⟩ := (hy' j).2
      have : q = p := antoineStereo_injective (hqy.trans hpy.symm)
      exact antoineStage_antitone (Nat.le_add_right j n) (this ▸ hq.1)
    exact hF z (hz ▸ hpy ▸ ⟨p, ⟨hpC, hp.2⟩, rfl⟩)
  · push Not at hne
    obtain ⟨i, hi⟩ := hne
    refine ⟨i + n, Nat.le_add_left n i, F, fun z hz => ?_⟩
    exact (Set.eq_empty_iff_forall_notMem.1 hi) (F z) ⟨mem_range_self z, hz⟩

/-- **The residual of Antoine's theorem**, exactly: for `n ≤ m`, the meridian of a link `L` of
generation `n` (the image of `GX.antoineMeridian` under `g_{v₀} ∘ ⋯ ∘ g_{v_{n-1}}`, carried into
`S³`) is not null-homotopic in the complement in `S³` of the links of generation `m` inside `L`. -/
def AntoineMeridianEssential : Prop :=
  ∀ (v : ℕ → Fin 64) (n m : ℕ), n ≤ m →
    ¬ HomotopicIn (antoineStereo '' (antoineStage m ∩ antoineComp v n '' antoineLink))ᶜ
      ((antoineMeridian.map (continuous_antoineComp v n)).map continuous_antoineStereo)
      (Path.refl _)

/-- The word `0ᵏ 1 0 0 ⋯`: its generation-`(k+1)` link is `g₀ᵏ(g₁(L))`. -/
def antoineWord (k : ℕ) : ℕ → Fin 64 := fun j => if j = k then 1 else 0

theorem antoineComp_word (k : ℕ) :
    antoineComp (antoineWord k) (k + 1) = antoineComp (fun _ => 0) k ∘ antoineMap 1 := by
  show antoineComp (antoineWord k) k ∘ antoineMap (antoineWord k k) = _
  rw [antoineComp_congr (w' := fun _ => 0) fun j hj => by simp [antoineWord, hj.ne]]
  simp [antoineWord]

theorem antoineP0_not_mem_word_link (k : ℕ) :
    antoineP0 ∉ antoineComp (antoineWord k) (k + 1) '' antoineLink := by
  rintro ⟨q, hq, e⟩
  rw [antoineComp_word] at e
  have := antoineComp_injective _ k (e.trans (antoineComp_zero_p0 k).symm)
  exact Set.disjoint_left.1 (antoineMap_disjoint (show (1 : Fin 64) ≠ 0 by decide)) ⟨q, hq, rfl⟩
    ⟨antoineP0, antoineP0_mem, antoineMap_zero_p0.trans this.symm⟩

/-- **Antoine's essential loops, from the residual alone.** At the point `x₀ = antoineStereo p₀`
of the necklace (`p₀` the fixed point of `g₀`), in every neighbourhood `V`: the closed piece
`K = C ∩ L`, `L = g₀ᵏ(g₁(L))` (link selection by `GX.antoineComp_diam`), misses `x₀`, and the
loop `g₀ᵏ(up · across · meridian · across⁻¹ · up⁻¹)` (accessibility: the vertical segment above
`p₀` meets the necklace only at `p₀`, `GX.antoineVert_not_mem_necklace`) lies in `V` off the
necklace and is essential in `S³ ∖ K` (by conjugation, the compactness reduction
`GX.antoine_homotopicIn_stage` and the residual `GX.AntoineMeridianEssential`). -/
theorem antoine_essential_loops (hres : AntoineMeridianEssential) :
    ∀ V ∈ 𝓝 (antoineStereo antoineP0), ∃ K : Set Sphere3, K ⊆ antoineNecklace ∧ IsClosed K ∧
      antoineStereo antoineP0 ∉ K ∧ ∃ γ : Path (antoineStereo antoineP0) (antoineStereo antoineP0),
        MemOmega (V ∩ antoineNecklaceᶜ) γ ∧ ¬ HomotopicIn Kᶜ γ (Path.refl _) := by
  intro V hV
  obtain ⟨ε, hε, hball⟩ :=
    Metric.mem_nhds_iff.1 (continuous_antoineStereo.continuousAt.preimage_mem_nhds hV)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show 0 < ε / 2 by positivity)
    (show (7 / 80 : ℝ) < 1 by norm_num)
  set f := antoineComp (fun _ => (0 : Fin 64)) k with hfdef
  set L := antoineComp (antoineWord k) (k + 1) '' antoineLink with hLdef
  have hfV : ∀ q ∈ antoineLink, antoineStereo (f q) ∈ V := fun q hq => hball (by
    rw [Metric.mem_ball]
    have := antoineComp_diam ⟨q, hq, rfl⟩ (antoineP0_mem_comp k)
    linarith)
  have hLc : IsClosed L := (antoineLink_isCompact.image (continuous_antoineComp _ _)).isClosed
  set K := antoineStereo '' (antoineNecklaceR3 ∩ L) with hKdef
  have hKmem : ∀ q ∈ antoineLink, (q = antoineP0 ∨ q ∉ antoineNecklaceR3) →
      antoineStereo (f q) ∉ K := by
    rintro q hq hq' ⟨p, ⟨hpC, hpL⟩, e⟩
    have hp : p = f q := antoineStereo_injective e
    rcases hq' with rfl | hq'
    · have e' : p = antoineP0 := hp.trans (antoineComp_zero_p0 k)
      exact antoineP0_not_mem_word_link k (e' ▸ hpL)
    · exact hq' (antoine_mem_necklace_of_comp _ k hq (hp ▸ hpC))
  refine ⟨K, image_mono inter_subset_left,
    ((isCompact_antoineNecklaceR3.inter_right hLc).image continuous_antoineStereo).isClosed,
    fun h => hKmem _ antoineP0_mem (Or.inl rfl) (by
      have e : f antoineP0 = antoineP0 := antoineComp_zero_p0 k
      rwa [e]), ?_⟩
  have hF : Continuous (antoineStereo ∘ f) :=
    continuous_antoineStereo.comp (continuous_antoineComp _ k)
  have hFp0 : (antoineStereo ∘ f) antoineP0 = antoineStereo antoineP0 := by
    simp [f, antoineComp_zero_p0]
  refine ⟨(antoineLoop0.map hF).cast hFp0.symm hFp0.symm, fun t h0 h1 => ?_, fun hhom => ?_⟩
  · have hg := antoineLoop0_memOmega t h0 h1
    refine ⟨hfV _ hg.1, ?_⟩
    rintro ⟨p, hp, e⟩
    have : p = f (antoineLoop0 t) := antoineStereo_injective e
    exact hg.2 (antoine_mem_necklace_of_comp _ k hg.1 (this ▸ hp))
  have h1 : HomotopicIn Kᶜ (antoineLoop0.map hF) (Path.refl _) :=
    antoine_homotopicIn_refl_congr hFp0.symm (fun _ => rfl) hhom
  rw [antoineLoop0, Path.map_trans, Path.map_trans, ← Path.map_symm] at h1
  have h2 := antoine_homotopicIn_conj (fun t => hKmem _ (antoineTail_mem t).1 (antoineTail_mem t).2)
    (fun t => hKmem _ (antoineMer1_good t).1 (Or.inr (antoineMer1_good t).2)) h1
  obtain ⟨m, hm, h3⟩ := antoine_homotopicIn_stage hLc h2 (k + 1)
  refine hres (antoineWord k) (k + 1) m hm (antoine_homotopicIn_refl_congr ?_ (fun t => ?_) h3)
  · simp [antoineComp_word, f]
  · simp only [Path.map_coe, Function.comp_apply, antoineComp_word, antoineMer1]
    rfl

section HomeoInvariance

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem antoine_almostTrivial_congr {U : Set X} {x y : X} {P : Path x x} {Q : Path y y}
    (hxy : x = y) (hPQ : ∀ t, P t = Q t) (h : AlmostTrivial U P) : AlmostTrivial U Q := by
  subst hxy
  obtain rfl : P = Q := Path.ext (funext hPQ)
  exact h

/-- Almost triviality is carried by a homeomorphism. -/
theorem AlmostTrivial.map_homeomorph (h : X ≃ₜ Y) {U : Set X} {x : X} {γ : Path x x}
    (hγ : AlmostTrivial U γ) : AlmostTrivial (h '' U) (γ.map h.continuous) := by
  obtain ⟨hm, hW⟩ := hγ
  refine ⟨fun t h0 h1 => ⟨_, hm t h0 h1, rfl⟩, fun W hW' => ?_⟩
  obtain ⟨γ', hγ', F, hF⟩ := hW _ (h.continuous.continuousAt.preimage_mem_nhds hW')
  refine ⟨γ'.map h.continuous, fun t h0 h1 => ⟨(hγ' t h0 h1).1, _, (hγ' t h0 h1).2, rfl⟩,
    F.map ⟨h, h.continuous⟩, fun s t h0 h1 => ⟨_, hF s t h0 h1, rfl⟩⟩

/-- Semi-local simple connectedness (homotopy form) is carried by a homeomorphism. -/
theorem IsSLSCIn.map_homeomorph (h : X ≃ₜ Y) {U : Set X} (hU : IsSLSCIn U) :
    IsSLSCIn (h '' U) := by
  refine ⟨h.surjective.denseRange.dense_image h.continuous hU.1, fun y => ?_⟩
  obtain ⟨V, hV, hVc, hxV, hloop⟩ := hU.2 (h.symm y)
  refine ⟨h '' V, h.isOpenMap V hV, hVc.image _ h.continuous.continuousOn,
    ⟨_, hxV, h.apply_symm_apply y⟩, fun γ hγ => ?_⟩
  have hδ : MemOmega (V ∩ U) (γ.map h.symm.continuous) := fun t h0 h1 => by
    obtain ⟨⟨a, ha, ea⟩, ⟨b, hb, eb⟩⟩ := hγ t h0 h1
    refine ⟨?_, ?_⟩
    · show h.symm (γ t) ∈ V
      rw [← ea, h.symm_apply_apply]; exact ha
    · show h.symm (γ t) ∈ U
      rw [← eb, h.symm_apply_apply]; exact hb
  exact antoine_almostTrivial_congr (h.apply_symm_apply y)
    (fun t => h.apply_symm_apply (γ t)) ((hloop _ hδ).map_homeomorph h)

end HomeoInvariance

/-! ### Antoine's lemma at equal generations (the abelian case, proved)

`GX.antoinePsi = (ρ - 7/8) + i z` near the core square of `L` (cut off to the constant `9/8` far
away) vanishes only on the core, and on the meridian it is exactly `(3/14) e^{2πit}`
(`GX.antoinePsi_meridian`); composed with the inverse similarity `GX.antoineCompInv` and the
stereographic chart `GX.antoineStereoInv`, it is a continuous map `S³ ∖ L_{v,n} → ℂ ∖ 0`
(`GX.antoineTheta`) under which the meridian of `L_{v,n}` has winding number `1`. -/

/-- The inverse of the similarity `GX.antoineMap i`. -/
def antoineMapInv (i : Fin 64) (q : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  antoinePerm (antoineT i) ((q.1 - (antoineZ i).1 / 640) * (80 / 7),
    (q.2.1 - (antoineZ i).2 / 640) * (80 / 7), q.2.2 * (80 / 7))

theorem antoineMapInv_map (i : Fin 64) (p : ℝ × ℝ × ℝ) : antoineMapInv i (antoineMap i p) = p := by
  rcases antoineT_cases i with h | h | h <;>
    simp only [antoineMapInv, antoineMap, h, antoinePerm] <;>
    ext <;> ring

theorem antoineMap_mapInv (i : Fin 64) (q : ℝ × ℝ × ℝ) : antoineMap i (antoineMapInv i q) = q := by
  rcases antoineT_cases i with h | h | h <;>
    simp only [antoineMapInv, antoineMap, h, antoinePerm] <;>
    ext <;> ring

theorem continuous_antoineMapInv (i : Fin 64) : Continuous (antoineMapInv i) := by
  show Continuous fun q => antoineMapInv i q
  rcases antoineT_cases i with h | h | h <;>
    simp only [antoineMapInv, h, antoinePerm] <;> fun_prop

/-- The inverse of `GX.antoineComp w n`. -/
def antoineCompInv (w : ℕ → Fin 64) : ℕ → ℝ × ℝ × ℝ → ℝ × ℝ × ℝ
  | 0 => id
  | n + 1 => antoineMapInv (w n) ∘ antoineCompInv w n

theorem antoineCompInv_comp (w : ℕ → Fin 64) (n : ℕ) (p : ℝ × ℝ × ℝ) :
    antoineCompInv w n (antoineComp w n p) = p := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    show antoineMapInv (w n) (antoineCompInv w n (antoineComp w n (antoineMap (w n) p))) = p
    rw [ih, antoineMapInv_map]

theorem antoineComp_compInv (w : ℕ → Fin 64) (n : ℕ) (q : ℝ × ℝ × ℝ) :
    antoineComp w n (antoineCompInv w n q) = q := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    show antoineComp w n (antoineMap (w n) (antoineMapInv (w n) (antoineCompInv w n q))) = q
    rw [antoineMap_mapInv, ih]

theorem continuous_antoineCompInv (w : ℕ → Fin 64) (n : ℕ) : Continuous (antoineCompInv w n) := by
  induction n with
  | zero => exact continuous_id
  | succ n ih => exact (continuous_antoineMapInv _).comp ih

/-- `ρ² + z²`, `ρ = max(|x|, |y|)`. -/
def antoineSq (p : ℝ × ℝ × ℝ) : ℝ := (max |p.1| |p.2.1|) ^ 2 + p.2.2 ^ 2

theorem continuous_antoineSq : Continuous antoineSq := by unfold antoineSq; fun_prop

theorem antoineMap_sq_lt (i : Fin 64) {p : ℝ × ℝ × ℝ} (hp : antoineSq p < 4) :
    antoineSq (antoineMap i p) < 4 := by
  have hm : max |p.1| |p.2.1| < 2 := by
    unfold antoineSq at hp
    nlinarith [abs_nonneg p.1, le_max_left |p.1| |p.2.1|, sq_nonneg p.2.2]
  have hz : |p.2.2| < 2 := by
    unfold antoineSq at hp
    have : p.2.2 ^ 2 < 4 := by nlinarith [sq_nonneg (max |p.1| |p.2.1|)]
    rw [← sq_abs] at this; nlinarith [abs_nonneg p.2.2]
  have hx : |p.1| < 2 := (le_max_left _ _).trans_lt hm
  have hy : |p.2.1| < 2 := (le_max_right _ _).trans_lt hm
  have hc : |((antoineZ i).1 : ℝ)| ≤ 560 ∧ |((antoineZ i).2 : ℝ)| ≤ 560 := by
    rcases antoine_centre_mem i with ⟨c1, c2⟩ | ⟨c1, c2⟩
    · exact ⟨by exact_mod_cast c1.le, by exact_mod_cast c2⟩
    · exact ⟨by exact_mod_cast c2, by exact_mod_cast c1.le⟩
  rw [abs_lt] at hx hy hz
  obtain ⟨hc1, hc2⟩ := hc
  rw [abs_le] at hc1 hc2
  have key : ∀ a b c : ℝ, |a| < 11 / 10 → |b| < 11 / 10 → |c| < 11 / 10 →
      (max |a| |b|) ^ 2 + c ^ 2 < 4 := by
    intro a b c ha hb hc
    have h1 : max |a| |b| < 11 / 10 := max_lt ha hb
    have h0 : 0 ≤ max |a| |b| := (abs_nonneg a).trans (le_max_left _ _)
    have h2 : c ^ 2 < (11 / 10) ^ 2 := by rw [← sq_abs]; nlinarith [abs_nonneg c]
    nlinarith
  unfold antoineSq
  rcases antoineT_cases i with h | h | h <;>
    simp only [antoineMap, h, antoinePerm] <;>
    refine key _ _ _ ?_ ?_ ?_ <;> rw [abs_lt] <;> constructor <;> linarith

theorem antoineComp_sq_lt (w : ℕ → Fin 64) (n : ℕ) {p : ℝ × ℝ × ℝ} (hp : antoineSq p < 4) :
    antoineSq (antoineComp w n p) < 4 := by
  induction n generalizing p with
  | zero => exact hp
  | succ n ih => exact ih (antoineMap_sq_lt _ hp)

theorem antoineCompInv_sq_ge (w : ℕ → Fin 64) (n : ℕ) {q : ℝ × ℝ × ℝ} (hq : 4 ≤ antoineSq q) :
    4 ≤ antoineSq (antoineCompInv w n q) := by
  by_contra h
  push Not at h
  have := antoineComp_sq_lt w n h
  rw [antoineComp_compInv] at this
  linarith

/-- An invariant of `ℝ³ ∖ L` with values in `ℂ ∖ 0`: `(ρ - 7/8) + i z` near the core square,
cut off to the constant `9/8` where `ρ² + z² ≥ 4`. -/
def antoinePsi (p : ℝ × ℝ × ℝ) : ℂ :=
  ((min 2 (max |p.1| |p.2.1| + max 0 (antoineSq p - 2)) - 7 / 8 : ℝ) : ℂ) +
    ((p.2.2 * max 0 (min 1 (3 - antoineSq p)) : ℝ) : ℂ) * Complex.I

theorem continuous_antoinePsi : Continuous antoinePsi := by
  unfold antoinePsi
  have := continuous_antoineSq
  fun_prop

theorem antoinePsi_eq_of_sq_ge {p : ℝ × ℝ × ℝ} (hp : 4 ≤ antoineSq p) : antoinePsi p = 9 / 8 := by
  have h1 : min 2 (max |p.1| |p.2.1| + max 0 (antoineSq p - 2)) = 2 := by
    refine min_eq_left ?_
    rw [max_eq_right (show (0 : ℝ) ≤ antoineSq p - 2 by linarith)]
    linarith [(abs_nonneg p.1).trans (le_max_left |p.1| |p.2.1|)]
  have h2 : max 0 (min 1 (3 - antoineSq p)) = 0 :=
    max_eq_left ((min_le_right _ _).trans (by linarith))
  simp only [antoinePsi, h1, h2, mul_zero, Complex.ofReal_zero, zero_mul, add_zero]
  push_cast; norm_num

theorem antoinePsi_mem_of_eq_zero {p : ℝ × ℝ × ℝ} (h : antoinePsi p = 0) : p ∈ antoineLink := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [antoinePsi, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_im, Complex.I_im, mul_zero, mul_one, sub_zero, Complex.zero_re,
    Complex.add_im, Complex.mul_im, zero_add, Complex.zero_im, add_zero] at hre him
  set ρ := max |p.1| |p.2.1| with hρ
  have hρ0 : 0 ≤ ρ := (abs_nonneg _).trans (le_max_left _ _)
  have hS : antoineSq p = ρ ^ 2 + p.2.2 ^ 2 := rfl
  have hm : min 2 (ρ + max 0 (antoineSq p - 2)) = 7 / 8 := by linarith
  have hlt : ρ + max 0 (antoineSq p - 2) = 7 / 8 := by
    rcases min_choice 2 (ρ + max 0 (antoineSq p - 2)) with e | e <;> rw [e] at hm
    · norm_num at hm
    · exact hm
  have hmx := le_max_right 0 (antoineSq p - 2)
  have hmx0 := le_max_left 0 (antoineSq p - 2)
  -- the imaginary part: `z = 0` or `S ≥ 3`
  have hz : p.2.2 = 0 := by
    rcases mul_eq_zero.1 him with h' | h'
    · exact h'
    · exfalso
      have h3 : 3 ≤ antoineSq p := by
        by_contra hc
        push Not at hc
        have : 0 < min 1 (3 - antoineSq p) := lt_min one_pos (by linarith)
        have := le_max_right 0 (min 1 (3 - antoineSq p))
        linarith
      linarith
  have hSρ : antoineSq p = ρ ^ 2 := by rw [hS, hz]; ring
  have hρ1 : ρ ≤ 1 := by
    by_contra hc
    push Not at hc
    have : 2 < antoineSq p := by rw [hSρ]; nlinarith
    linarith
  have hS2 : antoineSq p ≤ 2 := by rw [hSρ]; nlinarith
  rw [max_eq_left (by linarith)] at hlt
  refine ⟨by rw [hz]; norm_num, ?_, ?_⟩
  · show ρ ≤ 1; linarith
  · show 3 / 4 ≤ ρ; linarith

/-- On the meridian, `GX.antoinePsi` is exactly the circle `(3/14) e^{2πit}`. -/
theorem antoinePsi_meridian (t : I) :
    antoinePsi (antoineMeridian t) = (3 / 14 : ℂ) * Complex.exp (2 * Real.pi * Complex.I * t) := by
  rw [antoineMeridian_apply]
  set c := Real.cos (2 * Real.pi * t)
  set s := Real.sin (2 * Real.pi * t)
  have hcs : s ^ 2 + c ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  have hc1 : -1 ≤ c := Real.neg_one_le_cos _
  have hc2 : c ≤ 1 := Real.cos_le_one _
  have hpos : 0 ≤ 7 / 8 + 3 / 14 * c := by linarith
  have hρ : max |(0 : ℝ)| |7 / 8 + 3 / 14 * c| = 7 / 8 + 3 / 14 * c := by
    rw [abs_zero, abs_of_nonneg hpos, max_eq_right hpos]
  have hS : antoineSq (0, 7 / 8 + 3 / 14 * c, 3 / 14 * s) =
      (7 / 8 + 3 / 14 * c) ^ 2 + (3 / 14 * s) ^ 2 := by
    simp only [antoineSq, hρ]
  have hS2 : antoineSq (0, 7 / 8 + 3 / 14 * c, 3 / 14 * s) ≤ 2 := by rw [hS]; nlinarith
  have e1 : min 2 (max |(0 : ℝ)| |7 / 8 + 3 / 14 * c| +
      max 0 (antoineSq (0, 7 / 8 + 3 / 14 * c, 3 / 14 * s) - 2)) = 7 / 8 + 3 / 14 * c := by
    rw [hρ, max_eq_left (by linarith), add_zero, min_eq_right (by linarith)]
  have e2 : max 0 (min 1 (3 - antoineSq (0, 7 / 8 + 3 / 14 * c, 3 / 14 * s))) = 1 := by
    rw [min_eq_left (by linarith), max_eq_right zero_le_one]
  simp only [antoinePsi, e1, e2, mul_one]
  have : (2 * Real.pi * Complex.I * (t : ℝ)) = ((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_mul_I]
  apply Complex.ext <;>
    simp [c, s] <;> ring

theorem sphere3_sum_sq (y : Sphere3) :
    (y : EuclideanSpace ℝ (Fin 4)) 0 ^ 2 + (y : EuclideanSpace ℝ (Fin 4)) 1 ^ 2 +
      (y : EuclideanSpace ℝ (Fin 4)) 2 ^ 2 + (y : EuclideanSpace ℝ (Fin 4)) 3 ^ 2 = 1 := by
  have h := real_inner_self_eq_norm_sq (y : EuclideanSpace ℝ (Fin 4))
  rw [mem_sphere_zero_iff_norm.1 y.2] at h
  simp only [PiLp.inner_apply, Fin.sum_univ_four, RCLike.inner_apply, conj_trivial] at h
  nlinarith

/-- Stereographic projection `S³ ∖ {N} → ℝ³`, the inverse of `GX.antoineStereo`. -/
def antoineStereoInv (y : Sphere3) : ℝ × ℝ × ℝ :=
  ((y : EuclideanSpace ℝ (Fin 4)) 0 / (1 - (y : EuclideanSpace ℝ (Fin 4)) 3),
    (y : EuclideanSpace ℝ (Fin 4)) 1 / (1 - (y : EuclideanSpace ℝ (Fin 4)) 3),
    (y : EuclideanSpace ℝ (Fin 4)) 2 / (1 - (y : EuclideanSpace ℝ (Fin 4)) 3))

theorem antoineStereo_apply (p : ℝ × ℝ × ℝ) :
    (antoineStereo p : EuclideanSpace ℝ (Fin 4)) =
      !₂[2 * p.1 / (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 + 1),
        2 * p.2.1 / (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 + 1),
        2 * p.2.2 / (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 + 1),
        (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 - 1) / (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 + 1)] := rfl

theorem antoineStereo_three_lt (p : ℝ × ℝ × ℝ) :
    (antoineStereo p : EuclideanSpace ℝ (Fin 4)) 3 < 1 := by
  rw [antoineStereo_apply]
  have hN : 0 < p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 + 1 := by positivity
  change (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 - 1) / (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 + 1) < 1
  rw [div_lt_one hN]; linarith

theorem antoineStereoInv_stereo (p : ℝ × ℝ × ℝ) : antoineStereoInv (antoineStereo p) = p := by
  have hN : 0 < p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 + 1 := by positivity
  simp only [antoineStereoInv, antoineStereo_apply, PiLp.toLp_apply, Matrix.cons_val_three,
    Matrix.cons_val_two, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.tail_cons,
    Matrix.head_cons]
  have hd : 1 - (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 - 1) / (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 + 1) =
      2 / (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 + 1) := by field_simp; ring
  rw [hd]
  ext <;> simp only <;> field_simp

theorem antoineStereo_stereoInv {y : Sphere3} (hy : (y : EuclideanSpace ℝ (Fin 4)) 3 < 1) :
    antoineStereo (antoineStereoInv y) = y := by
  have hs := sphere3_sum_sq y
  obtain ⟨w, hw⟩ := y
  simp only at hy hs ⊢
  have hd : 0 < 1 - w 3 := by linarith
  have hd' : 1 - w 3 ≠ 0 := hd.ne'
  have hN : (w 0 / (1 - w 3)) ^ 2 + (w 1 / (1 - w 3)) ^ 2 + (w 2 / (1 - w 3)) ^ 2 + 1 =
      2 / (1 - w 3) := by
    field_simp
    nlinarith
  have hN' : (w 0 / (1 - w 3)) ^ 2 + (w 1 / (1 - w 3)) ^ 2 + (w 2 / (1 - w 3)) ^ 2 - 1 =
      2 * w 3 / (1 - w 3) := by
    field_simp
    nlinarith
  apply Subtype.ext
  rw [antoineStereo_apply]
  simp only [antoineStereoInv]
  rw [hN, hN']
  have e0 : 2 * (w 0 / (1 - w 3)) / (2 / (1 - w 3)) = w 0 := by field_simp
  have e1 : 2 * (w 1 / (1 - w 3)) / (2 / (1 - w 3)) = w 1 := by field_simp
  have e2 : 2 * (w 2 / (1 - w 3)) / (2 / (1 - w 3)) = w 2 := by field_simp
  have e3 : 2 * w 3 / (1 - w 3) / (2 / (1 - w 3)) = w 3 := by field_simp
  rw [e0, e1, e2, e3]
  ext i
  fin_cases i <;> rfl

theorem antoineStereoInv_sq_ge {y : Sphere3} (hy : 19 / 20 < (y : EuclideanSpace ℝ (Fin 4)) 3)
    (hy1 : (y : EuclideanSpace ℝ (Fin 4)) 3 < 1) : 4 ≤ antoineSq (antoineStereoInv y) := by
  have hs := sphere3_sum_sq y
  set y0 := (y : EuclideanSpace ℝ (Fin 4)) 0
  set y1 := (y : EuclideanSpace ℝ (Fin 4)) 1
  set y2 := (y : EuclideanSpace ℝ (Fin 4)) 2
  set y3 := (y : EuclideanSpace ℝ (Fin 4)) 3
  have hd : 0 < 1 - y3 := by linarith
  simp only [antoineSq, antoineStereoInv]
  set a := y0 / (1 - y3)
  set b := y1 / (1 - y3)
  set c := y2 / (1 - y3)
  have hsum : a ^ 2 + b ^ 2 + c ^ 2 = (1 + y3) / (1 - y3) := by
    simp only [a, b, c]; field_simp; nlinarith
  have hbig : 39 ≤ (1 + y3) / (1 - y3) := by rw [le_div_iff₀ hd]; linarith
  have ha : a ^ 2 ≤ (max |a| |b|) ^ 2 := by
    rw [← sq_abs a]; exact pow_le_pow_left₀ (abs_nonneg a) (le_max_left _ _) 2
  have hb : b ^ 2 ≤ (max |a| |b|) ^ 2 := by
    rw [← sq_abs b]; exact pow_le_pow_left₀ (abs_nonneg b) (le_max_right _ _) 2
  nlinarith [sq_nonneg c]

/-- The invariant of `S³ ∖ L_{v,n}`, `L_{v,n}` the link of generation `n` with word `v`:
`GX.antoinePsi ∘ (g_v)⁻¹` in the stereographic chart, the constant `9/8` near the pole. -/
def antoineTheta (v : ℕ → Fin 64) (n : ℕ) (y : Sphere3) : ℂ :=
  if (y : EuclideanSpace ℝ (Fin 4)) 3 < 1 then antoinePsi (antoineCompInv v n (antoineStereoInv y))
  else 9 / 8

theorem antoineTheta_stereo (v : ℕ → Fin 64) (n : ℕ) (p : ℝ × ℝ × ℝ) :
    antoineTheta v n (antoineStereo (antoineComp v n p)) = antoinePsi p := by
  rw [antoineTheta, if_pos (antoineStereo_three_lt _), antoineStereoInv_stereo,
    antoineCompInv_comp]

theorem continuousAt_antoineStereoInv {y : Sphere3} (hy : (y : EuclideanSpace ℝ (Fin 4)) 3 < 1) :
    ContinuousAt antoineStereoInv y := by
  have hc : ∀ i : Fin 4, Continuous fun z : Sphere3 => (z : EuclideanSpace ℝ (Fin 4)) i :=
    fun i => (PiLp.continuous_apply 2 _ i).comp continuous_subtype_val
  have hd : (1 - (y : EuclideanSpace ℝ (Fin 4)) 3) ≠ 0 := by linarith
  have hden : ContinuousAt (fun z : Sphere3 => 1 - (z : EuclideanSpace ℝ (Fin 4)) 3) y :=
    (continuous_const.sub (hc 3)).continuousAt
  exact ((hc 0).continuousAt.div hden hd).prodMk
    (((hc 1).continuousAt.div hden hd).prodMk ((hc 2).continuousAt.div hden hd))

theorem continuous_antoineTheta (v : ℕ → Fin 64) (n : ℕ) : Continuous (antoineTheta v n) := by
  have hc3 : Continuous fun z : Sphere3 => (z : EuclideanSpace ℝ (Fin 4)) 3 :=
    (PiLp.continuous_apply 2 _ 3).comp continuous_subtype_val
  refine continuous_iff_continuousAt.2 fun y => ?_
  by_cases hy : (y : EuclideanSpace ℝ (Fin 4)) 3 < 1
  · have hG : ContinuousAt (fun z => antoinePsi (antoineCompInv v n (antoineStereoInv z))) y :=
      (continuous_antoinePsi.comp (continuous_antoineCompInv v n)).continuousAt.comp
        (continuousAt_antoineStereoInv hy)
    refine hG.congr (Filter.eventually_of_mem ((isOpen_lt hc3 continuous_const).mem_nhds hy)
      fun z hz => ?_)
    simp only [antoineTheta, if_pos (show (z : EuclideanSpace ℝ (Fin 4)) 3 < 1 from hz)]
  · push Not at hy
    refine (continuousAt_const (y := (9 / 8 : ℂ))).congr (Filter.eventually_of_mem
      ((isOpen_lt continuous_const hc3).mem_nhds (show (19 / 20 : ℝ) < _ by linarith))
      fun z hz => ?_)
    simp only [antoineTheta]
    split_ifs with h
    · exact (antoinePsi_eq_of_sq_ge (antoineCompInv_sq_ge v n
        (antoineStereoInv_sq_ge hz h))).symm
    · rfl

theorem antoineTheta_ne_zero (v : ℕ → Fin 64) (n : ℕ) {y : Sphere3}
    (hy : y ∉ antoineStereo '' (antoineComp v n '' antoineLink)) : antoineTheta v n y ≠ 0 := by
  intro h
  unfold antoineTheta at h
  split_ifs at h with h3
  · apply hy
    refine ⟨antoineStereoInv y, ⟨antoineCompInv v n (antoineStereoInv y),
      antoinePsi_mem_of_eq_zero h, antoineComp_compInv _ _ _⟩, antoineStereo_stereoInv h3⟩
  · norm_num at h

/-- **Antoine's lemma at equal generations** (the abelian case of the residual, proved): the
meridian of a link `L_{v,n}` of generation `n` is not null-homotopic in `S³ ∖ L_{v,n}` — the
invariant `GX.antoineTheta` carries it to the circle `(3/14) e^{2πit}` of `ℂ ∖ 0`, of winding
number `1`. -/
theorem antoineMeridianEssential_self (v : ℕ → Fin 64) (n : ℕ) :
    ¬ HomotopicIn (antoineStereo '' (antoineStage n ∩ antoineComp v n '' antoineLink))ᶜ
      ((antoineMeridian.map (continuous_antoineComp v n)).map continuous_antoineStereo)
      (Path.refl _) := by
  set K := antoineStereo '' (antoineStage n ∩ antoineComp v n '' antoineLink) with hKdef
  set μ' := (antoineMeridian.map (continuous_antoineComp v n)).map continuous_antoineStereo
  rw [homotopicIn_iff]
  rintro ⟨h1, h2, hom⟩
  have hK : ∀ y : (Kᶜ : Set Sphere3), antoineTheta v n y ≠ 0 := fun y => by
    refine antoineTheta_ne_zero v n fun hy => y.2 ?_
    obtain ⟨q, hq, e⟩ := hy
    exact ⟨q, ⟨mem_iUnion.2 ⟨v, hq⟩, hq⟩, e⟩
  let Θ' : C((Kᶜ : Set Sphere3), CStar) :=
    ⟨fun y => ⟨antoineTheta v n y, hK y⟩,
      ((continuous_antoineTheta v n).comp continuous_subtype_val).subtype_mk _⟩
  have hw := cWinding_homotopic (Path.Homotopic.map hom Θ')
  have e1 : cWinding ((pathToSub μ' h1).map Θ'.continuous) = 1 := by
    refine cWinding_eq _ (Γ := ⟨fun t => Complex.log (3 / 14) +
      2 * Real.pi * Complex.I * (t : ℝ), by fun_prop⟩) (fun t => ?_) ?_
    · show Complex.exp (Complex.log (3 / 14) + _) =
        antoineTheta v n (antoineStereo (antoineComp v n (antoineMeridian t)))
      rw [Complex.exp_add, Complex.exp_log (by norm_num), antoineTheta_stereo,
        antoinePsi_meridian]
    · simp only [ContinuousMap.coe_mk, Set.Icc.coe_one, Set.Icc.coe_zero, Complex.ofReal_one,
        Complex.ofReal_zero, mul_one, mul_zero, add_zero, Int.cast_one, one_mul]
  have e2 : cWinding ((pathToSub (Path.refl (antoineStereo (antoineComp v n antoineMerPt)))
      h2).map Θ'.continuous) = 0 := by
    refine cWinding_eq _ (Γ := ContinuousMap.const I
      (Complex.log (antoineTheta v n (antoineStereo (antoineComp v n antoineMerPt)))))
      (fun t => ?_) (by simp)
    show Complex.exp (Complex.log _) = antoineTheta v n _
    exact Complex.exp_log (hK ⟨_, h2 0⟩)
  rw [e1, e2] at hw
  exact one_ne_zero hw

/-- **The residual of Antoine's theorem**, its non-abelian part: for `n < m` the meridian of a
link of generation `n` is not null-homotopic in the complement of the links of generation `m`
inside it. (The case `n = m` is `GX.antoineMeridianEssential_self`, proved.) -/
def AntoineMeridianEssentialStrict : Prop :=
  ∀ (v : ℕ → Fin 64) (n m : ℕ), n < m →
    ¬ HomotopicIn (antoineStereo '' (antoineStage m ∩ antoineComp v n '' antoineLink))ᶜ
      ((antoineMeridian.map (continuous_antoineComp v n)).map continuous_antoineStereo)
      (Path.refl _)

/-- The residual `GX.AntoineMeridianEssential` from its strict part (the equal-generation case
being `GX.antoineMeridianEssential_self`). -/
theorem antoineMeridianEssential_of_strict (h : AntoineMeridianEssentialStrict) :
    AntoineMeridianEssential := by
  intro v n m hnm
  rcases eq_or_lt_of_le hnm with rfl | hlt
  · exact antoineMeridianEssential_self v n
  · exact h v n m hlt

/-! ### Reduction of the strict residual to the top link (self-similarity) -/

/-- The word `v₀ ⋯ v_{n-1} w₀ w₁ ⋯`. -/
def antoineCat (v : ℕ → Fin 64) (n : ℕ) (w : ℕ → Fin 64) : ℕ → Fin 64 :=
  fun j => if j < n then v j else w (j - n)

theorem antoineComp_cat (v : ℕ → Fin 64) (n : ℕ) (w : ℕ → Fin 64) (k : ℕ) :
    antoineComp (antoineCat v n w) (n + k) = antoineComp v n ∘ antoineComp w k := by
  induction k with
  | zero =>
    rw [Nat.add_zero, antoineComp_congr (w' := v) fun j hj => by simp [antoineCat, hj]]
    rfl
  | succ k ih =>
    show antoineComp (antoineCat v n w) (n + k) ∘ antoineMap (antoineCat v n w (n + k)) = _
    rw [ih]
    simp only [antoineCat, show ¬ (n + k < n) by omega, if_false, Nat.add_sub_cancel_left]
    rfl

/-- The links of generation `k` inside `L`, carried by `g_v`, are links of generation `n + k`
inside `L_{v,n}`. -/
theorem antoineComp_image_stage_subset (v : ℕ → Fin 64) (n k : ℕ) :
    antoineComp v n '' antoineStage k ⊆ antoineStage (n + k) ∩ antoineComp v n '' antoineLink := by
  rintro _ ⟨q, hq, rfl⟩
  obtain ⟨w, hw⟩ := mem_iUnion.1 hq
  obtain ⟨p, hp, rfl⟩ := hw
  have e : antoineComp v n (antoineComp w k p) = antoineComp (antoineCat v n w) (n + k) p := by
    rw [antoineComp_cat]; rfl
  refine ⟨mem_iUnion.2 ⟨antoineCat v n w, e ▸ ⟨p, hp, rfl⟩⟩, ?_⟩
  have h1 := antoineComp_antitone (antoineCat v n w) (Nat.le_add_right n k) ⟨p, hp, e.symm⟩
  rwa [antoineComp_congr (w' := v) fun j hj => by simp [antoineCat, hj]] at h1

theorem antoineCompInv_dist_ge (w : ℕ → Fin 64) (n : ℕ) (p : ℝ × ℝ × ℝ) :
    dist p 0 - 2 ≤ dist (antoineCompInv w n p) 0 := by
  have h0 : antoineSq (antoineComp w n 0) < 4 := antoineComp_sq_lt w n (by simp [antoineSq])
  have hf0 : dist (antoineComp w n 0) 0 < 2 := by
    set a := antoineComp w n 0
    have hm : max |a.1| |a.2.1| < 2 := by
      unfold antoineSq at h0
      nlinarith [abs_nonneg a.1, le_max_left |a.1| |a.2.1|, sq_nonneg a.2.2]
    have hz : |a.2.2| < 2 := by
      unfold antoineSq at h0
      have : a.2.2 ^ 2 < 4 := by nlinarith [sq_nonneg (max |a.1| |a.2.1|)]
      rw [← sq_abs] at this; nlinarith [abs_nonneg a.2.2]
    rw [Prod.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq]
    simp only [Prod.fst_zero, Prod.snd_zero, sub_zero]
    exact max_lt ((le_max_left _ _).trans_lt hm) (max_lt ((le_max_right _ _).trans_lt hm) hz)
  have h1 : dist p (antoineComp w n 0) ≤ dist (antoineCompInv w n p) 0 := by
    have := antoineComp_dist_le w n (antoineCompInv w n p) 0
    rw [antoineComp_compInv] at this
    have hr : (7 / 80 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith [dist_nonneg (x := antoineCompInv w n p) (y := 0)]
  linarith [dist_triangle p (antoineComp w n 0) 0]

theorem antoine_dist_zero_sq_le (q : ℝ × ℝ × ℝ) :
    dist q 0 ^ 2 ≤ q.1 ^ 2 + q.2.1 ^ 2 + q.2.2 ^ 2 := by
  rw [Prod.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq]
  simp only [Prod.fst_zero, Prod.snd_zero, sub_zero]
  rcases max_choice |q.1| (max |q.2.1| |q.2.2|) with h | h <;> rw [h]
  · rw [sq_abs]; nlinarith [sq_nonneg q.2.1, sq_nonneg q.2.2]
  · rcases max_choice |q.2.1| |q.2.2| with h' | h' <;> rw [h', sq_abs] <;>
      nlinarith [sq_nonneg q.1, sq_nonneg q.2.1, sq_nonneg q.2.2]

theorem antoineStereoInv_dist_sq {y : Sphere3} (hy : (y : EuclideanSpace ℝ (Fin 4)) 3 < 1) :
    (1 + (y : EuclideanSpace ℝ (Fin 4)) 3) / (3 * (1 - (y : EuclideanSpace ℝ (Fin 4)) 3)) ≤
      dist (antoineStereoInv y) 0 ^ 2 := by
  have hs := sphere3_sum_sq y
  obtain ⟨w, hw⟩ := y
  simp only at hy hs ⊢
  have hd : 0 < 1 - w 3 := by linarith
  simp only [antoineStereoInv, Prod.dist_eq, Real.dist_eq, Prod.fst_zero, Prod.snd_zero, sub_zero]
  set a := w 0 / (1 - w 3)
  set b := w 1 / (1 - w 3)
  set c := w 2 / (1 - w 3)
  have hsum : a ^ 2 + b ^ 2 + c ^ 2 = (1 + w 3) / (1 - w 3) := by
    simp only [a, b, c]; field_simp; nlinarith
  set M := max |a| (max |b| |c|)
  have ha : a ^ 2 ≤ M ^ 2 := by
    rw [← sq_abs a]; exact pow_le_pow_left₀ (abs_nonneg a) (le_max_left _ _) 2
  have hb : b ^ 2 ≤ M ^ 2 := by
    rw [← sq_abs b]
    exact pow_le_pow_left₀ (abs_nonneg b) ((le_max_left _ _).trans (le_max_right _ _)) 2
  have hc : c ^ 2 ≤ M ^ 2 := by
    rw [← sq_abs c]
    exact pow_le_pow_left₀ (abs_nonneg c) ((le_max_right _ _).trans (le_max_right _ _)) 2
  rw [div_le_iff₀ (by positivity)]
  have : (1 + w 3) / (1 - w 3) * (1 - w 3) = 1 + w 3 := div_mul_cancel₀ _ hd.ne'
  nlinarith

theorem sphere3_eq_north {y : Sphere3} (hy : 1 ≤ (y : EuclideanSpace ℝ (Fin 4)) 3) :
    (y : EuclideanSpace ℝ (Fin 4)) 0 = 0 ∧ (y : EuclideanSpace ℝ (Fin 4)) 1 = 0 ∧
      (y : EuclideanSpace ℝ (Fin 4)) 2 = 0 ∧ (y : EuclideanSpace ℝ (Fin 4)) 3 = 1 := by
  have hs := sphere3_sum_sq y
  have h3 : (y : EuclideanSpace ℝ (Fin 4)) 3 = 1 := by
    nlinarith [sq_nonneg ((y : EuclideanSpace ℝ (Fin 4)) 0),
      sq_nonneg ((y : EuclideanSpace ℝ (Fin 4)) 1), sq_nonneg ((y : EuclideanSpace ℝ (Fin 4)) 2)]
  rw [h3] at hs
  refine ⟨?_, ?_, ?_, h3⟩ <;>
    nlinarith [sq_nonneg ((y : EuclideanSpace ℝ (Fin 4)) 0),
      sq_nonneg ((y : EuclideanSpace ℝ (Fin 4)) 1), sq_nonneg ((y : EuclideanSpace ℝ (Fin 4)) 2)]

theorem sphere3_dist_north_sq {a y : Sphere3} (hy : 1 ≤ (y : EuclideanSpace ℝ (Fin 4)) 3) :
    dist a y ^ 2 = 2 - 2 * (a : EuclideanSpace ℝ (Fin 4)) 3 := by
  obtain ⟨h0, h1, h2, h3⟩ := sphere3_eq_north hy
  rw [Subtype.dist_eq, dist_eq_norm, norm_sub_sq_real, mem_sphere_zero_iff_norm.1 a.2,
    mem_sphere_zero_iff_norm.1 y.2]
  simp only [PiLp.inner_apply, Fin.sum_univ_four, RCLike.inner_apply, conj_trivial, h0, h1, h2, h3]
  ring

/-- The similarity `(g_v)⁻¹`, conjugated by the stereographic chart, fixing the pole. -/
def antoinePhi (v : ℕ → Fin 64) (n : ℕ) (y : Sphere3) : Sphere3 :=
  if (y : EuclideanSpace ℝ (Fin 4)) 3 < 1 then antoineStereo (antoineCompInv v n (antoineStereoInv y))
  else y

theorem antoineStereo_three (q : ℝ × ℝ × ℝ) :
    (antoineStereo q : EuclideanSpace ℝ (Fin 4)) 3 =
      (q.1 ^ 2 + q.2.1 ^ 2 + q.2.2 ^ 2 - 1) / (q.1 ^ 2 + q.2.1 ^ 2 + q.2.2 ^ 2 + 1) := by
  rw [antoineStereo_apply]; rfl

theorem continuous_antoinePhi (v : ℕ → Fin 64) (n : ℕ) : Continuous (antoinePhi v n) := by
  have hc3 : Continuous fun z : Sphere3 => (z : EuclideanSpace ℝ (Fin 4)) 3 :=
    (PiLp.continuous_apply 2 _ 3).comp continuous_subtype_val
  refine continuous_iff_continuousAt.2 fun y => ?_
  by_cases hy : (y : EuclideanSpace ℝ (Fin 4)) 3 < 1
  · have hG : ContinuousAt
        (fun z => antoineStereo (antoineCompInv v n (antoineStereoInv z))) y :=
      (continuous_antoineStereo.comp (continuous_antoineCompInv v n)).continuousAt.comp
        (continuousAt_antoineStereoInv hy)
    refine hG.congr (Filter.eventually_of_mem ((isOpen_lt hc3 continuous_const).mem_nhds hy)
      fun z hz => ?_)
    simp only [antoinePhi, if_pos (show (z : EuclideanSpace ℝ (Fin 4)) 3 < 1 from hz)]
  · push Not at hy
    rw [Metric.continuousAt_iff]
    intro ε hε
    set Λ : ℝ := 4 / ε ^ 2 with hΛ
    have hΛ0 : 0 < Λ := by positivity
    set R : ℝ := Λ + 3 with hR
    set η : ℝ := min (1 / (3 * R ^ 2)) (1 / 2) with hη
    have hη0 : 0 < η := by positivity
    refine ⟨min ε (Real.sqrt (2 * η)), lt_min hε (Real.sqrt_pos.2 (by positivity)), fun z hz => ?_⟩
    have hPy : antoinePhi v n y = y := by simp [antoinePhi, not_lt.2 hy]
    rw [hPy]
    by_cases hz3 : (z : EuclideanSpace ℝ (Fin 4)) 3 < 1
    · simp only [antoinePhi, if_pos hz3]
      have hd := sphere3_dist_north_sq (a := z) hy
      have hzy : dist z y < Real.sqrt (2 * η) := lt_of_lt_of_le hz (min_le_right _ _)
      have hzy2 : dist z y ^ 2 < 2 * η := by
        have := pow_lt_pow_left₀ hzy dist_nonneg (two_ne_zero)
        rwa [Real.sq_sqrt (by positivity)] at this
      have h1z : 1 - (z : EuclideanSpace ℝ (Fin 4)) 3 < η := by linarith
      have hz0 : 1 / 2 < (z : EuclideanSpace ℝ (Fin 4)) 3 := by
        linarith [min_le_right (1 / (3 * R ^ 2)) (1 / 2)]
      -- the chart point is far out
      set p := antoineStereoInv z
      set q := antoineCompInv v n p
      have hp2 := antoineStereoInv_dist_sq hz3
      have hpR : R ^ 2 ≤ dist p 0 ^ 2 := by
        refine le_trans ?_ hp2
        have hpos : 0 < 1 - (z : EuclideanSpace ℝ (Fin 4)) 3 := by linarith
        rw [le_div_iff₀ (by positivity)]
        have : 1 - (z : EuclideanSpace ℝ (Fin 4)) 3 < 1 / (3 * R ^ 2) :=
          lt_of_lt_of_le h1z (min_le_left _ _)
        rw [lt_div_iff₀ (by positivity)] at this
        nlinarith
      have hpR' : R ≤ dist p 0 := by
        have hR0 : 0 ≤ R := by positivity
        nlinarith [dist_nonneg (x := p) (y := 0)]
      have hq := antoineCompInv_dist_ge v n p
      have hqd : Λ + 1 ≤ dist q 0 := by linarith
      have hq2 := antoine_dist_zero_sq_le q
      set N := q.1 ^ 2 + q.2.1 ^ 2 + q.2.2 ^ 2 with hN
      have hNΛ : Λ < N := by nlinarith
      have hN0 : (0 : ℝ) ≤ N := by positivity
      have hN1 : N + 1 ≠ 0 := by positivity
      have hd' : dist (antoineStereo q) y ^ 2 = 4 / (N + 1) := by
        rw [sphere3_dist_north_sq hy, antoineStereo_three, ← hN]
        rw [eq_div_iff hN1]; field_simp; ring
      have hlt : dist (antoineStereo q) y ^ 2 < ε ^ 2 := by
        rw [hd', div_lt_iff₀ (by positivity)]
        rw [hΛ, div_lt_iff₀ (by positivity)] at hNΛ
        nlinarith
      exact lt_of_pow_lt_pow_left₀ 2 hε.le hlt
    · simp only [antoinePhi, if_neg hz3]
      exact lt_of_lt_of_le hz (min_le_left _ _)

theorem antoinePhi_stereo (v : ℕ → Fin 64) (n : ℕ) (p : ℝ × ℝ × ℝ) :
    antoinePhi v n (antoineStereo (antoineComp v n p)) = antoineStereo p := by
  rw [antoinePhi, if_pos (antoineStereo_three_lt _), antoineStereoInv_stereo, antoineCompInv_comp]

theorem antoinePhi_mapsTo (v : ℕ → Fin 64) (n k : ℕ) {y : Sphere3}
    (hy : y ∉ antoineStereo '' (antoineStage (n + k) ∩ antoineComp v n '' antoineLink)) :
    antoinePhi v n y ∉ antoineStereo '' antoineStage k := by
  rintro ⟨q, hq, e⟩
  unfold antoinePhi at e
  split_ifs at e with h3
  · apply hy
    have hq' : antoineCompInv v n (antoineStereoInv y) = q := (antoineStereo_injective e).symm
    refine ⟨antoineStereoInv y, antoineComp_image_stage_subset v n k ⟨q, hq, ?_⟩,
      antoineStereo_stereoInv h3⟩
    rw [← hq', antoineComp_compInv]
  · exact h3 (e ▸ antoineStereo_three_lt q)

/-- A null-homotopy pushed forward by a continuous map carrying `U` into `U'`. -/
theorem antoine_homotopicIn_map {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {U : Set X} {U' : Set Y} {x : X} {γ : Path x x} {f : X → Y} (hf : Continuous f)
    (hfU : ∀ y ∈ U, f y ∈ U') (h : HomotopicIn U γ (Path.refl x)) :
    HomotopicIn U' (γ.map hf) (Path.refl (f x)) := by
  obtain ⟨F, hF⟩ := h
  exact ⟨(F.map ⟨f, hf⟩).cast rfl (by ext; simp), fun z => hfU _ (hF z)⟩

/-- **Antoine's lemma for the top link**, the canonical form of the residual: for `k ≥ 1` the
meridian of `L` is not null-homotopic in `S³ ∖ C_k`, `C_k` the `64^k` links of generation
`k`. -/
def AntoineMeridianEssentialTop : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    ¬ HomotopicIn (antoineStereo '' antoineStage k)ᶜ (antoineMeridian.map continuous_antoineStereo)
      (Path.refl _)

/-- The strict residual from the top-link form, by self-similarity (`GX.antoinePhi`). -/
theorem antoineMeridianEssentialStrict_of_top (h : AntoineMeridianEssentialTop) :
    AntoineMeridianEssentialStrict := by
  intro v n m hnm hhom
  obtain ⟨k, rfl⟩ : ∃ k, m = n + k := ⟨m - n, by omega⟩
  refine h k (by omega) ?_
  have h1 := antoine_homotopicIn_map (U' := (antoineStereo '' antoineStage k)ᶜ)
    (continuous_antoinePhi v n)
    (fun y hy => antoinePhi_mapsTo v n k hy) hhom
  refine antoine_homotopicIn_refl_congr ?_ (fun t => ?_) h1
  · exact antoinePhi_stereo v n _
  · show antoinePhi v n (antoineStereo (antoineComp v n (antoineMeridian t))) =
      antoineStereo (antoineMeridian t)
    exact antoinePhi_stereo v n _

/-! ### Antoine's lemma from its first generation: the van Kampen reduction (WP-41r)

The infinite family `GX.AntoineMeridianEssentialTop` (`k ≥ 1`) is reduced, sorry-free, to ONE
generation: `GX.AntoineFirstGeneration`. The proof is Antoine's: decompose
`S³ ∖ C_{k+1} = (S³ ∖ C₁) ∪ ⋃ⱼ (Nⱼ ∖ C_{k+1})` (`Nⱼ` a tubular neighbourhood of the `j`-th link
`Lⱼ` of the first generation), glue the 64 tubes one at a time by the injectivity consequence of
Seifert–van Kampen (`GX.VanKampen.homotopicIn_of_homotopicIn_union'`), the collar `Nⱼ ∖ Lⱼ`
injecting on both sides — on the side of the tube by the self-similarity `GX.antoinePhi` and the
statement for `C_k` (induction on `k`, all powers of the meridian), on the outer side by the
first generation — so that `π₁(S³ ∖ C₁) → π₁(S³ ∖ C_{k+1})` is injective on the powers of the
meridian; the base `k = 0` is the winding number of `GX.antoineTheta`. -/

section AntoineVK

/-- Natural powers of a loop, by concatenation. -/
def loopNatPow {X : Type*} [TopologicalSpace X] {x : X} (γ : Path x x) : ℕ → Path x x
  | 0 => Path.refl x
  | n + 1 => (loopNatPow γ n).trans γ

/-- Integer powers of a loop (`γ⁻¹` for negative exponents). -/
def loopZPow {X : Type*} [TopologicalSpace X] {x : X} (γ : Path x x) : ℤ → Path x x
  | Int.ofNat n => loopNatPow γ n
  | Int.negSucc n => loopNatPow γ.symm (n + 1)

section Pow

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem loopNatPow_mem {S : Set X} {x : X} {γ : Path x x} (h : ∀ t, γ t ∈ S) :
    ∀ n t, loopNatPow γ n t ∈ S := by
  have hx : x ∈ S := γ.source ▸ h 0
  intro n
  induction n with
  | zero => exact fun _ => hx
  | succ n ih => exact VanKampen.mem_trans ih h

theorem loopZPow_mem {S : Set X} {x : X} {γ : Path x x} (h : ∀ t, γ t ∈ S) :
    ∀ a t, loopZPow γ a t ∈ S
  | Int.ofNat n => loopNatPow_mem h n
  | Int.negSucc n => loopNatPow_mem (VanKampen.mem_symm h) (n + 1)

theorem loopNatPow_map {x : X} (γ : Path x x) {f : X → Y} (hf : Continuous f) :
    ∀ n, (loopNatPow γ n).map hf = loopNatPow (γ.map hf) n
  | 0 => by ext; rfl
  | n + 1 => by rw [loopNatPow, Path.map_trans, loopNatPow_map γ hf n]; rfl

theorem loopZPow_map {x : X} (γ : Path x x) {f : X → Y} (hf : Continuous f) :
    ∀ a, (loopZPow γ a).map hf = loopZPow (γ.map hf) a
  | Int.ofNat n => loopNatPow_map γ hf n
  | Int.negSucc n => by
    show (loopNatPow γ.symm (n + 1)).map hf = loopNatPow (γ.map hf).symm (n + 1)
    rw [loopNatPow_map, Path.map_symm]

theorem loopNatPow_congr {x y : X} {P : Path x x} {Q : Path y y} (h : ∀ t, P t = Q t) :
    ∀ n t, loopNatPow P n t = loopNatPow Q n t := by
  have hxy : x = y := by rw [← P.source, ← Q.source, h]
  intro n
  induction n with
  | zero => exact fun _ => hxy
  | succ n ih =>
    intro t
    simp only [loopNatPow, Path.trans_apply]
    split_ifs
    · exact ih _
    · exact h _

theorem loopZPow_congr {x y : X} {P : Path x x} {Q : Path y y} (h : ∀ t, P t = Q t) :
    ∀ a t, loopZPow P a t = loopZPow Q a t
  | Int.ofNat n => loopNatPow_congr h n
  | Int.negSucc n => loopNatPow_congr (P := P.symm) (Q := Q.symm) (fun _ => h _) (n + 1)

theorem cWinding_pathRefl (z : CStar) : cWinding (Path.refl z) = 0 :=
  cWinding_eq _ (Γ := ContinuousMap.const I (Complex.log z))
    (fun _ => by show Complex.exp (Complex.log z) = z; exact Complex.exp_log z.2) (by simp)

theorem cWinding_pathSymm {z : CStar} (δ : Path z z) : cWinding δ.symm = -cWinding δ := by
  have h := cWinding_trans δ δ.symm
  rw [← cWinding_homotopic ⟨Path.Homotopy.reflTransSymm δ⟩, cWinding_pathRefl] at h
  omega

theorem cWinding_loopNatPow {z : CStar} (δ : Path z z) :
    ∀ n : ℕ, cWinding (loopNatPow δ n) = n * cWinding δ
  | 0 => by simp [loopNatPow, cWinding_pathRefl]
  | n + 1 => by
    rw [loopNatPow, cWinding_trans, cWinding_loopNatPow δ n]; push_cast; ring

theorem cWinding_loopZPow {z : CStar} (δ : Path z z) :
    ∀ a : ℤ, cWinding (loopZPow δ a) = a * cWinding δ
  | Int.ofNat n => by
    show cWinding (loopNatPow δ n) = _
    rw [cWinding_loopNatPow]; rfl
  | Int.negSucc n => by
    show cWinding (loopNatPow δ.symm (n + 1)) = _
    rw [cWinding_loopNatPow, cWinding_pathSymm, Int.negSucc_eq]; push_cast; ring

theorem pathToSub_loopZPow {S : Set X} {x : X} {γ : Path x x} (h : ∀ t, γ t ∈ S) (a : ℤ)
    (h' : ∀ t, loopZPow γ a t ∈ S) :
    pathToSub (loopZPow γ a) h' = loopZPow (pathToSub γ h) a := by
  ext t
  have e : (pathToSub γ h).map continuous_subtype_val = γ := by ext; rfl
  have := congrArg (fun p : Path x x => p t) (loopZPow_map (pathToSub γ h) continuous_subtype_val a)
  simp only [e, Path.map_coe, Function.comp_apply] at this
  exact this.symm

/-- `T · 1 · T⁻¹ ≃ 1`, inside any set containing `T`. -/
theorem homotopicIn_conj_refl {S : Set X} {x y : X} {T : Path x y} (hT : ∀ t, T t ∈ S) :
    HomotopicIn S ((T.trans (Path.refl y)).trans T.symm) (Path.refl x) := by
  have hx : x ∈ S := T.source ▸ hT 0
  have hy : y ∈ S := T.target ▸ hT 1
  refine VanKampen.homotopicIn_of_sub
    (VanKampen.mem_trans (VanKampen.mem_trans hT (VanKampen.mem_refl hy)) (VanKampen.mem_symm hT))
    (VanKampen.mem_refl hx)
    (p' := ((pathToSub T hT).trans (Path.refl (⟨y, hy⟩ : S))).trans (pathToSub T hT).symm)
    (q' := Path.refl (⟨x, hx⟩ : S)) (fun t => ?_) (fun t => rfl) ?_
  · simp only [Path.trans_apply, Path.symm_apply]
    split_ifs <;> rfl
  · rw [← Path.Homotopic.Quotient.eq]
    simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
      Path.Homotopic.Quotient.mk_refl, Path.Homotopic.Quotient.trans_refl,
      Path.Homotopic.Quotient.trans_symm]

/-- A conjugate of a null-homotopic loop is null-homotopic. -/
theorem homotopicIn_conj_of {S : Set X} {x y : X} {T : Path x y} (hT : ∀ t, T t ∈ S)
    {M : Path y y} (hM : HomotopicIn S M (Path.refl y)) :
    HomotopicIn S ((T.trans M).trans T.symm) (Path.refl x) :=
  (((HomotopicIn.refl hT).hcomp hM).hcomp (HomotopicIn.refl (VanKampen.mem_symm hT))).trans
    (homotopicIn_conj_refl hT)

end Pow

/-- The top meridian, in `S³`. -/
abbrev antoineMuS : Path (antoineStereo antoineMerPt) (antoineStereo antoineMerPt) :=
  antoineMeridian.map continuous_antoineStereo

/-- **The base `k = 0`**: no nonzero power of the meridian is null-homotopic in `S³ ∖ L`
(winding number of `GX.antoineTheta`). -/
theorem antoine_pow_essential_zero (a : ℤ) (ha : a ≠ 0) :
    ¬ HomotopicIn (antoineStereo '' antoineStage 0)ᶜ (loopZPow antoineMuS a) (Path.refl _) := by
  set v : ℕ → Fin 64 := fun _ => 0
  set K := antoineStereo '' antoineStage 0 with hKdef
  rw [homotopicIn_iff]
  rintro ⟨h1, h2, hom⟩
  have hμ : ∀ t, antoineMuS t ∈ Kᶜ := fun t => by
    rintro ⟨q, hq, e⟩
    have := antoineStereo_injective e
    rw [antoineStage_zero] at hq
    exact antoineMeridian_not_mem t (this ▸ hq)
  have hK : ∀ y : (Kᶜ : Set Sphere3), antoineTheta v 0 y ≠ 0 := fun y => by
    refine antoineTheta_ne_zero v 0 fun hy => y.2 ?_
    obtain ⟨q, hq, e⟩ := hy
    refine ⟨q, ?_, e⟩
    rw [antoineStage_zero]
    simpa [antoineComp] using hq
  let Θ' : C((Kᶜ : Set Sphere3), CStar) :=
    ⟨fun y => ⟨antoineTheta v 0 y, hK y⟩,
      ((continuous_antoineTheta v 0).comp continuous_subtype_val).subtype_mk _⟩
  have hw := cWinding_homotopic (Path.Homotopic.map hom Θ')
  have e1 : cWinding ((pathToSub antoineMuS hμ).map Θ'.continuous) = 1 := by
    refine cWinding_eq _ (Γ := ⟨fun t => Complex.log (3 / 14) +
      2 * Real.pi * Complex.I * (t : ℝ), by fun_prop⟩) (fun t => ?_) ?_
    · show Complex.exp (Complex.log (3 / 14) + _) =
        antoineTheta v 0 (antoineStereo (antoineComp v 0 (antoineMeridian t)))
      rw [Complex.exp_add, Complex.exp_log (by norm_num), antoineTheta_stereo,
        antoinePsi_meridian]
    · simp only [ContinuousMap.coe_mk, Set.Icc.coe_one, Set.Icc.coe_zero, Complex.ofReal_one,
        Complex.ofReal_zero, mul_one, mul_zero, add_zero, Int.cast_one, one_mul]
  have e2 : cWinding ((pathToSub (Path.refl (antoineStereo antoineMerPt)) h2).map
      Θ'.continuous) = 0 := by
    rw [show (pathToSub (Path.refl (antoineStereo antoineMerPt)) h2).map Θ'.continuous =
      Path.refl _ from by ext; rfl, cWinding_pathRefl]
  rw [pathToSub_loopZPow hμ, loopZPow_map, cWinding_loopZPow, e1, e2, mul_one] at hw
  exact ha hw

/-- The tubular neighbourhood of the link `L`: the round tube `(ρ - 7/8)² + z² < 1/16` around
the core square (`ρ = max(|x|,|y|)`). -/
def antoineNbhd : Set (ℝ × ℝ × ℝ) := {p | (max |p.1| |p.2.1| - 7 / 8) ^ 2 + p.2.2 ^ 2 < 1 / 16}

/-- The `j`-th link of the first generation, in `S³`. -/
def antoineL1 (j : Fin 64) : Set Sphere3 := antoineStereo '' (antoineMap j '' antoineLink)

/-- The tubular neighbourhood of the `j`-th link of the first generation, in `S³`. -/
def antoineN1 (j : Fin 64) : Set Sphere3 := antoineStereo '' (antoineMap j '' antoineNbhd)

/-- The collar `Nⱼ ∖ Lⱼ` of the `j`-th link. -/
def antoineA1 (j : Fin 64) : Set Sphere3 := antoineN1 j \ antoineL1 j

/-- The base point of the meridian of the `j`-th link. -/
def antoineX1 (j : Fin 64) : Sphere3 := antoineStereo (antoineMap j antoineMerPt)

/-- The meridian of the `j`-th link of the first generation, in `S³`. -/
def antoineMu1 (j : Fin 64) : Path (antoineX1 j) (antoineX1 j) :=
  (antoineMeridian.map (continuous_antoineMap j)).map continuous_antoineStereo

/-- **Antoine's lemma at the first generation**, the residual of `GX.AntoineMeridianEssentialTop`
after the van Kampen reduction (`GX.antoineMeridianEssentialTop_of_firstGeneration`): the
non-abelian heart `chain` (no nonzero power of the meridian of `L` is null-homotopic in the
complement of the closed chain `C₁` of 64 links) and the abelian collar facts of the 64 links. -/
structure AntoineFirstGeneration : Prop where
  chain : ∀ a : ℤ, a ≠ 0 →
    ¬ HomotopicIn (antoineStereo '' antoineStage 1)ᶜ (loopZPow antoineMuS a) (Path.refl _)
  disjoint : ∀ i j : Fin 64, i ≠ j →
    Disjoint (antoineMap j '' antoineNbhd) (antoineMap i '' antoineLink)
  collar_conn : ∀ j, IsPathConnected (antoineA1 j)
  collar_mer : ∀ (j : Fin 64) (O : Set Sphere3), O ⊆ antoineN1 j →
    ∀ δ : Path (antoineX1 j) (antoineX1 j), (∀ t, δ t ∈ antoineA1 j) →
      HomotopicIn O δ (Path.refl _) →
        ∃ a : ℤ, HomotopicIn (antoineA1 j) δ (loopZPow (antoineMu1 j) a)
  collar_inj : ∀ (j : Fin 64) (δ : Path (antoineX1 j) (antoineX1 j)), (∀ t, δ t ∈ antoineA1 j) →
    HomotopicIn (antoineStereo '' antoineStage 1)ᶜ δ (Path.refl _) →
      HomotopicIn (antoineA1 j) δ (Path.refl _)
  joined : ∀ j, JoinedIn (antoineStereo '' antoineStage 1)ᶜ (antoineStereo antoineMerPt)
    (antoineX1 j)

theorem antoineStage_one_eq : antoineStage 1 = ⋃ i, antoineMap i '' antoineLink := by
  ext p
  simp only [antoineStage, mem_iUnion]
  constructor
  · rintro ⟨w, hw⟩; exact ⟨w 0, hw⟩
  · rintro ⟨i, hi⟩; exact ⟨fun _ => i, hi⟩

theorem antoineLink_subset_nbhd : antoineLink ⊆ antoineNbhd := by
  rintro p ⟨hz, hm1, hm2⟩
  show (max |p.1| |p.2.1| - 7 / 8) ^ 2 + p.2.2 ^ 2 < 1 / 16
  have h1 : |max |p.1| |p.2.1| - 7 / 8| ≤ 1 / 8 := abs_le.2 ⟨by linarith, by linarith⟩
  have h2 := sq_abs (max |p.1| |p.2.1| - 7 / 8)
  have h3 := sq_abs p.2.2
  nlinarith [abs_nonneg (max |p.1| |p.2.1| - 7 / 8), abs_nonneg p.2.2]

theorem isOpen_antoineNbhd : IsOpen antoineNbhd :=
  isOpen_lt (by fun_prop) continuous_const

theorem antoineMap_image_eq (j : Fin 64) (O : Set (ℝ × ℝ × ℝ)) :
    antoineMap j '' O = antoineMapInv j ⁻¹' O := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩; show antoineMapInv j (antoineMap j p) ∈ O; rwa [antoineMapInv_map]
  · intro hq; exact ⟨_, hq, antoineMap_mapInv j q⟩

theorem antoineStereo_image_eq (O : Set (ℝ × ℝ × ℝ)) :
    antoineStereo '' O = {y : Sphere3 | (y : EuclideanSpace ℝ (Fin 4)) 3 < 1} ∩ antoineStereoInv ⁻¹' O := by
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨antoineStereo_three_lt p, by show antoineStereoInv _ ∈ O; rwa [antoineStereoInv_stereo]⟩
  · rintro ⟨h3, hO⟩
    exact ⟨_, hO, antoineStereo_stereoInv h3⟩

theorem isOpen_antoineStereo_image {O : Set (ℝ × ℝ × ℝ)} (hO : IsOpen O) :
    IsOpen (antoineStereo '' O) := by
  rw [antoineStereo_image_eq]
  have hc3 : Continuous fun z : Sphere3 => (z : EuclideanSpace ℝ (Fin 4)) 3 :=
    (PiLp.continuous_apply 2 _ 3).comp continuous_subtype_val
  refine ContinuousOn.isOpen_inter_preimage (fun y hy => ?_) (isOpen_lt hc3 continuous_const) hO
  exact (continuousAt_antoineStereoInv hy).continuousWithinAt

theorem isOpen_antoineN1 (j : Fin 64) : IsOpen (antoineN1 j) := by
  refine isOpen_antoineStereo_image ?_
  rw [antoineMap_image_eq]
  exact isOpen_antoineNbhd.preimage (continuous_antoineMapInv j)

theorem isClosed_antoineL1 (j : Fin 64) : IsClosed (antoineL1 j) :=
  ((antoineLink_isCompact.image (continuous_antoineMap j)).image continuous_antoineStereo).isClosed

theorem antoineMeridian_mem_nbhd (t : I) : antoineMeridian t ∈ antoineNbhd := by
  show (max |(antoineMeridian t).1| |(antoineMeridian t).2.1| - 7 / 8) ^ 2 +
    (antoineMeridian t).2.2 ^ 2 < 1 / 16
  rw [antoineMeridian_apply]
  set c := Real.cos (2 * Real.pi * t)
  set s := Real.sin (2 * Real.pi * t)
  have hcs : s ^ 2 + c ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  have hc1 : -1 ≤ c := Real.neg_one_le_cos _
  have hpos : 0 ≤ 7 / 8 + 3 / 14 * c := by linarith
  simp only [abs_zero]
  rw [abs_of_nonneg hpos, max_eq_right hpos]
  nlinarith

theorem antoineMu1_mem (j : Fin 64) (t : I) : antoineMu1 j t ∈ antoineA1 j := by
  refine ⟨⟨_, ⟨_, antoineMeridian_mem_nbhd t, rfl⟩, rfl⟩, ?_⟩
  rintro ⟨q, ⟨p, hp, rfl⟩, e⟩
  have e1 := antoineMap_injective j (antoineStereo_injective e)
  exact antoineMeridian_not_mem t (e1 ▸ hp)

theorem antoineMuS_not_mem (t : I) : antoineMuS t ∉ antoineStereo '' antoineStage 1 := by
  rintro ⟨q, hq, e⟩
  have := antoineStereo_injective e
  have hq0 : q ∈ antoineStage 0 := antoineStage_antitone (Nat.zero_le 1) hq
  rw [antoineStage_zero] at hq0
  exact antoineMeridian_not_mem t (this ▸ hq0)

/-- **The van Kampen induction**: under `GX.AntoineFirstGeneration`, no nonzero power of the
meridian of `L` is null-homotopic in `S³ ∖ C_k`, for every `k`. -/
theorem antoine_pow_essential (h : AntoineFirstGeneration) :
    ∀ (k : ℕ) (a : ℤ), a ≠ 0 →
      ¬ HomotopicIn (antoineStereo '' antoineStage k)ᶜ (loopZPow antoineMuS a) (Path.refl _) := by
  haveI : LocPathConnectedSpace Sphere3 :=
    ChartedSpace.locPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) _
  intro k
  induction k with
  | zero => exact antoine_pow_essential_zero
  | succ k ih =>
    intro a ha hnull
    set K := antoineStereo '' antoineStage (k + 1) with hKdef
    set C1 := antoineStereo '' antoineStage 1 with hC1def
    have hC1 : C1 = ⋃ i, antoineL1 i := by rw [hC1def, antoineStage_one_eq, image_iUnion]; rfl
    have hKC1 : K ⊆ C1 := image_mono (antoineStage_antitone (by omega))
    have hKclosed : IsClosed K :=
      ((antoineStage_isCompact _).image continuous_antoineStereo).isClosed
    have hNL : ∀ i j : Fin 64, i ≠ j → Disjoint (antoineN1 j) (antoineL1 i) := fun i j hij =>
      (Set.disjoint_image_iff antoineStereo_injective).2 (h.disjoint i j hij)
    have hLN : ∀ j, antoineL1 j ⊆ antoineN1 j := fun j =>
      image_mono (image_mono antoineLink_subset_nbhd)
    -- points of a collar avoid every first-generation link, hence `C_{k+1}`
    have hA : ∀ j x, x ∈ antoineA1 j → (∀ i, x ∉ antoineL1 i) ∧ x ∉ K := by
      intro j x ⟨hxN, hxL⟩
      have hxL' : ∀ i, x ∉ antoineL1 i := fun i hxi => by
        by_cases e : i = j
        · exact hxL (e ▸ hxi)
        · exact Set.disjoint_left.1 (hNL i j e) hxN hxi
      refine ⟨hxL', fun hxK => ?_⟩
      have := hKC1 hxK
      rw [hC1] at this
      obtain ⟨i, hi⟩ := mem_iUnion.1 this
      exact hxL' i hi
    let M : ℕ → Set Sphere3 := fun m => (K ∪ ⋃ (i : Fin 64) (_ : m ≤ i.val), antoineL1 i)ᶜ
    have memM : ∀ m x, x ∈ M m ↔ x ∉ K ∧ ∀ i : Fin 64, m ≤ i.val → x ∉ antoineL1 i := by
      intro m x
      simp only [M, mem_compl_iff, mem_union, mem_iUnion, not_or, not_exists]
    have hM0 : M 0 = C1ᶜ := by
      ext x
      rw [memM, mem_compl_iff, hC1, mem_iUnion, not_exists]
      constructor
      · rintro ⟨_, h2⟩ i; exact h2 i (Nat.zero_le _)
      · intro h2
        refine ⟨fun hxK => ?_, fun i _ => h2 i⟩
        have := hKC1 hxK
        rw [hC1] at this
        obtain ⟨i, hi⟩ := mem_iUnion.1 this
        exact h2 i hi
    have hM64 : M 64 = Kᶜ := by
      ext x
      rw [memM, mem_compl_iff]
      exact ⟨fun h2 => h2.1, fun h2 => ⟨h2, fun i hi => absurd i.isLt (by omega)⟩⟩
    have hMmono : ∀ m, M 0 ⊆ M m := fun m x hx => by
      rw [memM] at hx ⊢
      exact ⟨hx.1, fun i _ => hx.2 i (Nat.zero_le _)⟩
    have hA0 : ∀ j, antoineA1 j ⊆ M 0 := fun j x hx => by
      rw [memM]
      exact ⟨(hA j x hx).2, fun i _ => (hA j x hx).1 i⟩
    -- gluing the tubes one at a time
    have hQ : ∀ m ≤ 64, ∀ δ : Path (antoineStereo antoineMerPt) (antoineStereo antoineMerPt),
        (∀ t, δ t ∈ M 0) → HomotopicIn (M m) δ (Path.refl _) →
          HomotopicIn (M 0) δ (Path.refl _) := by
      intro m
      induction m with
      | zero => intro _ δ _ hδ; exact hδ
      | succ m ihm =>
        intro hm δ hδ0 hδ
        set j : Fin 64 := ⟨m, by omega⟩ with hjdef
        set U := M m with hUdef
        set V := antoineN1 j \ K with hVdef
        have hjm : j.val = m := rfl
        have hUV : U ∪ V = M (m + 1) := by
          ext x
          constructor
          · rintro (hx | ⟨hxN, hxK⟩)
            · rw [memM] at hx ⊢
              exact ⟨hx.1, fun i hi => hx.2 i (by omega)⟩
            · rw [memM]
              refine ⟨hxK, fun i hi hxi => ?_⟩
              have hij : i ≠ j := fun e => by rw [e] at hi; omega
              exact Set.disjoint_left.1 (hNL i j hij) hxN hxi
          · intro hx
            rw [memM] at hx
            by_cases hxj : x ∈ antoineL1 j
            · exact Or.inr ⟨hLN j hxj, hx.1⟩
            · refine Or.inl ((memM m x).2 ⟨hx.1, fun i hi hxi => ?_⟩)
              rcases Nat.eq_or_lt_of_le hi with e | hlt
              · have : i = j := Fin.ext (by rw [hjm]; omega)
                exact hxj (this ▸ hxi)
              · exact hx.2 i hlt hxi
        have hUiV : U ∩ V = antoineA1 j := by
          ext x
          constructor
          · rintro ⟨hxU, hxN, _⟩
            rw [memM] at hxU
            exact ⟨hxN, hxU.2 j le_rfl⟩
          · intro hx
            exact ⟨hA0 j hx |> hMmono m, hx.1, (hA j x hx).2⟩
        have hUo : IsOpen U := by
          refine (hKclosed.union ?_).isOpen_compl
          exact isClosed_iUnion_of_finite fun i =>
            isClosed_iUnion_of_finite fun _ => isClosed_antoineL1 i
        have hVo : IsOpen V := (isOpen_antoineN1 j).sdiff hKclosed
        have hjoin := h.joined j
        set c := hjoin.somePath with hcdef
        have hc : ∀ t, c t ∈ M 0 := fun t => by rw [hM0]; exact hjoin.somePath_mem t
        have hcU : ∀ t, c t ∈ U := fun t => hMmono m (hc t)
        have hx : antoineX1 j ∈ U ∩ V := by
          rw [hUiV]
          have := antoineMu1_mem j 0
          rwa [Path.source] at this
        -- the collar injects into `U` (by the induction on `m`) and into `V` (on `k`)
        have hinjU : ∀ δ' : Path (antoineX1 j) (antoineX1 j), (∀ t, δ' t ∈ U ∩ V) →
            HomotopicIn U δ' (Path.refl _) → HomotopicIn (U ∩ V) δ' (Path.refl _) := by
          intro δ' hδ' hnU
          have hδ'A : ∀ t, δ' t ∈ antoineA1 j := fun t => hUiV ▸ hδ' t
          have hδ'0 : ∀ t, δ' t ∈ M 0 := fun t => hA0 j (hδ'A t)
          have h1 := homotopicIn_conj_of hcU hnU
          have h2 := ihm (by omega) _ (VanKampen.mem_trans (VanKampen.mem_trans hc hδ'0)
            (VanKampen.mem_symm hc)) h1
          have h3 : HomotopicIn (M 0) δ' (Path.refl _) := antoine_homotopicIn_conj hc hδ'0 h2
          rw [hM0] at h3
          rw [hUiV]
          exact h.collar_inj j δ' hδ'A h3
        have hinjV : ∀ δ' : Path (antoineX1 j) (antoineX1 j), (∀ t, δ' t ∈ U ∩ V) →
            HomotopicIn V δ' (Path.refl _) → HomotopicIn (U ∩ V) δ' (Path.refl _) := by
          intro δ' hδ' hnV
          have hδ'A : ∀ t, δ' t ∈ antoineA1 j := fun t => hUiV ▸ hδ' t
          obtain ⟨b, hb⟩ := h.collar_mer j V (fun _ hx => hx.1) δ' hδ'A hnV
          rcases eq_or_ne b 0 with rfl | hb0
          · rw [hUiV]; exact hb
          · exfalso
            have hAV : antoineA1 j ⊆ V := fun x hx => (hUiV ▸ hx : x ∈ U ∩ V).2
            have hmuV : HomotopicIn V (loopZPow (antoineMu1 j) b) (Path.refl _) :=
              (hb.mono hAV).symm.trans hnV
            set v : ℕ → Fin 64 := fun _ => j
            have hmap := antoine_homotopicIn_map (U' := (antoineStereo '' antoineStage k)ᶜ)
              (continuous_antoinePhi v 1) (fun y hy => antoinePhi_mapsTo v 1 k fun hy' => by
                rw [Nat.add_comm] at hy'
                exact hy.2 (image_mono inter_subset_left hy')) hmuV
            apply ih b hb0
            refine antoine_homotopicIn_refl_congr (antoinePhi_stereo v 1 antoineMerPt) ?_ hmap
            intro t
            rw [loopZPow_map]
            exact loopZPow_congr (fun t => antoinePhi_stereo v 1 (antoineMeridian t)) b t
        -- glue
        have hδU : ∀ t, δ t ∈ U := fun t => hMmono m (hδ0 t)
        have key := VanKampen.homotopicIn_of_homotopicIn_union' hUo hVo
          (hUiV ▸ h.collar_conn j) hx hinjU hinjV
          (γ := (c.symm.trans δ).trans c.symm.symm)
          (VanKampen.mem_trans (VanKampen.mem_trans (VanKampen.mem_symm hcU) hδU)
            (VanKampen.mem_symm (VanKampen.mem_symm hcU)))
          (by rw [hUV]; exact homotopicIn_conj_of (VanKampen.mem_symm fun t => hMmono (m + 1) (hc t)) hδ)
        exact ihm (by omega) δ hδ0 (antoine_homotopicIn_conj (VanKampen.mem_symm hcU) hδU key)
    -- conclude
    have hμ0 : ∀ t, loopZPow antoineMuS a t ∈ M 0 :=
      loopZPow_mem (fun t => by rw [hM0]; exact antoineMuS_not_mem t) a
    rw [← hM64] at hnull
    have := hQ 64 le_rfl _ hμ0 hnull
    rw [hM0] at this
    exact h.chain a ha this

/-- **`GX.AntoineMeridianEssentialTop` from the first generation** (sorry-free): Antoine's
lemma for every generation follows from `GX.AntoineFirstGeneration`. -/
theorem antoineMeridianEssentialTop_of_firstGeneration (h : AntoineFirstGeneration) :
    AntoineMeridianEssentialTop := by
  intro k _ hnull
  refine antoine_pow_essential h k 1 one_ne_zero ?_
  have hμ := hnull.mem_left
  have hx := (Path.refl (antoineStereo antoineMerPt)).source ▸ hnull.mem_right 0
  refine HomotopicIn.trans ?_ hnull
  refine VanKampen.homotopicIn_of_sub (VanKampen.mem_trans (VanKampen.mem_refl hx) hμ) hμ
    (p' := (Path.refl (⟨_, hx⟩ : ↥((antoineStereo '' antoineStage k)ᶜ))).trans (pathToSub _ hμ))
    (q' := pathToSub _ hμ) (fun t => ?_) (fun t => rfl) ?_
  · simp only [loopZPow, loopNatPow, Path.trans_apply]
    split_ifs <;> rfl
  · rw [← Path.Homotopic.Quotient.eq, Path.Homotopic.Quotient.mk_trans,
      Path.Homotopic.Quotient.mk_refl, Path.Homotopic.Quotient.refl_trans]

end AntoineVK

/-! ### The first generation: the five collar facts, proved (WP-41r round 1)

Five of the six fields of `GX.AntoineFirstGeneration` are fixed-level facts about the round tubes
`Nⱼ` and their collars `Aⱼ = Nⱼ ∖ Lⱼ`, proved here: `disjoint` (`GX.antoineTube_disjoint`: the
non-consecutive pairs are box-separated by `decide`, the consecutive ones miss by
`GX.antoine_tube_aux`), `joined` (`GX.antoine_joined`: explicit polygonal paths, certified pair by
pair by `decide`), `collar_conn` (`GX.antoine_collar_conn`: the collar retracts onto the torus
`|W| = 3/14`, the image of `ℝ²` under `GX.antoineE`), `collar_mer` and `collar_inj`
(`GX.antoine_collar_mer`, `GX.antoine_collar_inj`). The last two rest on the classification of
the loops of the collar by two windings (`GX.antoine_collar_classify`: `π₁(T² × I) = ℤ²`, by the
retraction and a straight-line homotopy of the lifted angles), the longitudinal winding being
read in `S³ ∖ C₁` through the next link (`GX.antoine_succ_wind`: the longitude of `Lⱼ` winds
`±1` around `Lⱼ₊₁`, by free homotopies in `ℂ ∖ 0`, `GX.AntoineLiftWind.of_freeHomotopy`). -/

/-! ### Collar facts: disjointness of the tubes -/

/-- The tube bounding boxes of `j` against the link boxes of `i` are separated. -/
def AntoineTubeSep (i j : Fin 64) : Prop :=
  antoineEx (antoineT i) + antoineEx (antoineT j) + 7 ≤ |(antoineZ i).1 - (antoineZ j).1| ∨
  antoineEy (antoineT i) + antoineEy (antoineT j) + 7 ≤ |(antoineZ i).2 - (antoineZ j).2|

instance antoineTubeSep_decidable (i j : Fin 64) : Decidable (AntoineTubeSep i j) := by
  unfold AntoineTubeSep; infer_instance

set_option maxRecDepth 100000 in
theorem antoine_tubeSep_or_adj : ∀ i j : Fin 64, i ≠ j → AntoineTubeSep i j ∨ AntoineAdj i j := by
  decide

theorem antoineNbhd_bounds {p : ℝ × ℝ × ℝ} (hp : p ∈ antoineNbhd) :
    |p.1| < 9 / 8 ∧ |p.2.1| < 9 / 8 ∧ |p.2.2| < 1 / 4 := by
  have hp' : (max |p.1| |p.2.1| - 7 / 8) ^ 2 + p.2.2 ^ 2 < 1 / 16 := hp
  have h1 : (max |p.1| |p.2.1| - 7 / 8) ^ 2 < 1 / 16 := by nlinarith [sq_nonneg p.2.2]
  have h2 : p.2.2 ^ 2 < 1 / 16 := by nlinarith [sq_nonneg (max |p.1| |p.2.1| - 7 / 8)]
  have h1' : max |p.1| |p.2.1| < 9 / 8 := by nlinarith
  refine ⟨(le_max_left _ _).trans_lt h1', (le_max_right _ _).trans_lt h1', ?_⟩
  exact abs_lt_of_sq_lt_sq (by linarith) (by norm_num)

theorem antoineMap_bounds_nbhd (i : Fin 64) {p : ℝ × ℝ × ℝ} (hp : p ∈ antoineNbhd) :
    |(antoineMap i p).1 - (antoineZ i).1 / 640| < (antoineEx (antoineT i) + 7) / 640 ∧
      |(antoineMap i p).2.1 - (antoineZ i).2 / 640| < (antoineEy (antoineT i) + 7) / 640 := by
  obtain ⟨hx, hy, hz⟩ := antoineNbhd_bounds hp
  rcases antoineT_cases i with h | h | h <;>
    simp only [antoineMap, h, antoinePerm, antoineEx, antoineEy, add_sub_cancel_left, abs_mul,
      abs_of_pos (show (0 : ℝ) < 7 / 80 by norm_num)] <;>
    push_cast <;> refine ⟨?_, ?_⟩ <;> linarith

/-- A tube point `(a, b, c)` and a link point `(a', b', c')` of two interlocking links, with
`a = a' + s`, `b = c'`, `c = b'`, `s = ±5/4`, cannot coincide. -/
theorem antoine_tube_aux {a b c a' b' c' s : ℝ} (hs : s = 5 / 4 ∨ s = -(5 / 4))
    (h1 : a = a' + s) (h2 : b = c') (h3 : c = b')
    (hp : (max |a| |b| - 7 / 8) ^ 2 + c ^ 2 < 1 / 16)
    (hp' : |c'| ≤ 1 / 8 ∧ max |a'| |b'| ≤ 1 ∧ 3 / 4 ≤ max |a'| |b'|) : False := by
  obtain ⟨hc', ha1', ha2'⟩ := hp'
  rw [← h2] at hc'
  rw [← h3] at ha1' ha2'
  have hc : c ^ 2 < 1 / 16 := by nlinarith [sq_nonneg (max |a| |b| - 7 / 8)]
  have hc4 : |c| < 1 / 4 := abs_lt_of_sq_lt_sq (by linarith) (by norm_num)
  have hA' : 3 / 4 ≤ |a'| := by
    rcases le_max_iff.1 ha2' with h | h
    · exact h
    · linarith
  have hx' : |a'| ≤ 1 := (le_max_left _ _).trans ha1'
  have hρ : max |a| |b| ≤ 1 / 2 ∨ 2 ≤ max |a| |b| := by
    have hb : |b| ≤ 1 / 2 := by linarith
    rw [abs_le] at hx'
    rcases le_abs'.1 hA' with h | h <;> rcases hs with rfl | rfl <;>
      first
      | (left; refine max_le ?_ hb; rw [abs_le]; constructor <;> linarith)
      | (right; refine le_max_of_le_left ?_; rw [abs_of_neg (by linarith)]; linarith)
      | (right; refine le_max_of_le_left ?_; rw [abs_of_pos (by linarith)]; linarith)
  rcases hρ with h | h <;> nlinarith [sq_nonneg c]

theorem antoineTube_disjoint (i j : Fin 64) (hij : i ≠ j) :
    Disjoint (antoineMap j '' antoineNbhd) (antoineMap i '' antoineLink) := by
  rw [Set.disjoint_left]
  rintro _ ⟨p, hp, rfl⟩ ⟨p', hp', heq⟩
  rcases antoine_tubeSep_or_adj i j hij with hsep | hadj
  · obtain ⟨b1, b2, -⟩ := antoineMap_bounds i hp'
    obtain ⟨b1', b2'⟩ := antoineMap_bounds_nbhd j hp
    rw [← heq] at b1' b2'
    rw [abs_le] at b1 b2
    rw [abs_lt] at b1' b2'
    rcases hsep with h | h
    · have h' : ((antoineEx (antoineT i) + antoineEx (antoineT j) + 7 : ℤ) : ℝ) ≤
          |((antoineZ i).1 : ℝ) - (antoineZ j).1| := by exact_mod_cast h
      push_cast at h'
      rcases le_abs'.1 h' with h'' | h'' <;> linarith
    · have h' : ((antoineEy (antoineT i) + antoineEy (antoineT j) + 7 : ℤ) : ℝ) ≤
          |((antoineZ i).2 : ℝ) - (antoineZ j).2| := by exact_mod_cast h
      push_cast at h'
      rcases le_abs'.1 h' with h'' | h'' <;> linarith
  · have hp1 : (max |p.1| |p.2.1| - 7 / 8) ^ 2 + p.2.2 ^ 2 < 1 / 16 := hp
    rcases hadj with ⟨hy, hx, ht⟩ | ⟨hx, hy, ht⟩
    · have hy' : ((antoineZ i).2 : ℝ) = (antoineZ j).2 := by exact_mod_cast hy
      have hx' : ((antoineZ i).1 : ℝ) - (antoineZ j).1 = 70 ∨
          ((antoineZ i).1 : ℝ) - (antoineZ j).1 = -70 := by
        rcases (abs_eq (by norm_num : (0 : ℤ) ≤ 70)).1 hx with h | h
        · exact Or.inl (by exact_mod_cast h)
        · exact Or.inr (by exact_mod_cast h)
      rcases ht with ⟨ti, tj⟩ | ⟨ti, tj⟩
      · -- link `i` horizontal, tube `j` vertical (`y`-plane)
        simp only [antoineMap, ti, tj, antoinePerm, Prod.mk.injEq] at heq
        obtain ⟨e1, e2, e3⟩ := heq
        refine antoine_tube_aux (a := p.1) (b := p.2.1) (c := p.2.2) (a' := p'.1)
          (b' := p'.2.1) (c' := p'.2.2)
          (s := if ((antoineZ i).1 : ℝ) - (antoineZ j).1 = 70 then 5/4 else -(5/4))
          ?_ ?_ (by linarith) (by linarith) hp1 hp'
        · split_ifs <;> simp
        · rcases hx' with h | h
          · rw [if_pos h]; linarith
          · rw [if_neg (by rw [h]; norm_num)]; linarith
      · simp only [antoineMap, ti, tj, antoinePerm, Prod.mk.injEq] at heq
        obtain ⟨e1, e2, e3⟩ := heq
        refine antoine_tube_aux (a := p.1) (b := p.2.1) (c := p.2.2) (a' := p'.1)
          (b' := p'.2.1) (c' := p'.2.2)
          (s := if ((antoineZ i).1 : ℝ) - (antoineZ j).1 = 70 then 5/4 else -(5/4))
          ?_ ?_ (by linarith) (by linarith) hp1 hp'
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
        refine antoine_tube_aux (a := p.2.1) (b := p.1) (c := p.2.2) (a' := p'.2.1)
          (b' := p'.1) (c' := p'.2.2)
          (s := if ((antoineZ i).2 : ℝ) - (antoineZ j).2 = 70 then 5/4 else -(5/4))
          ?_ ?_ (by linarith) (by linarith) (by rw [max_comm]; exact hp1)
            ⟨hp'.1, by rw [max_comm]; exact hp'.2.1, by rw [max_comm]; exact hp'.2.2⟩
        · split_ifs <;> simp
        · rcases hy' with h | h
          · rw [if_pos h]; linarith
          · rw [if_neg (by rw [h]; norm_num)]; linarith
      · simp only [antoineMap, ti, tj, antoinePerm, Prod.mk.injEq] at heq
        obtain ⟨e1, e2, e3⟩ := heq
        refine antoine_tube_aux (a := p.2.1) (b := p.1) (c := p.2.2) (a' := p'.2.1)
          (b' := p'.1) (c' := p'.2.2)
          (s := if ((antoineZ i).2 : ℝ) - (antoineZ j).2 = 70 then 5/4 else -(5/4))
          ?_ ?_ (by linarith) (by linarith) (by rw [max_comm]; exact hp1)
            ⟨hp'.1, by rw [max_comm]; exact hp'.2.1, by rw [max_comm]; exact hp'.2.2⟩
        · split_ifs <;> simp
        · rcases hy' with h | h
          · rw [if_pos h]; linarith
          · rw [if_neg (by rw [h]; norm_num)]; linarith


/-! ### Collar facts: joining the base points -/

theorem antoine_notMem_link_of_box (i : Fin 64) {p : ℝ × ℝ × ℝ}
    (h : (antoineEx (antoineT i) : ℝ) / 640 < |p.1 - (antoineZ i).1 / 640| ∨
      (antoineEy (antoineT i) : ℝ) / 640 < |p.2.1 - (antoineZ i).2 / 640|) :
    p ∉ antoineMap i '' antoineLink := by
  rintro ⟨q, hq, rfl⟩
  obtain ⟨b1, b2, -⟩ := antoineMap_bounds i hq
  rcases h with h | h <;> linarith

theorem antoine_notMem_link_hole0 (i : Fin 64) (hT : antoineT i = 0) {p : ℝ × ℝ × ℝ}
    (h1 : |p.1 - (antoineZ i).1 / 640| < 42 / 640) (h2 : |p.2.1 - (antoineZ i).2 / 640| < 42 / 640) :
    p ∉ antoineMap i '' antoineLink := by
  rintro ⟨q, ⟨-, -, hq⟩, rfl⟩
  simp only [antoineMap, hT, antoinePerm, add_sub_cancel_left, abs_mul,
    abs_of_pos (show (0 : ℝ) < 7 / 80 by norm_num)] at h1 h2
  have : max |q.1| |q.2.1| < 3 / 4 := max_lt (by linarith) (by linarith)
  linarith

theorem antoine_notMem_link_hole2 (i : Fin 64) (hT : antoineT i = 2) {p : ℝ × ℝ × ℝ}
    (h1 : |p.2.2| < 42 / 640) (h2 : |p.2.1 - (antoineZ i).2 / 640| < 42 / 640) :
    p ∉ antoineMap i '' antoineLink := by
  rintro ⟨q, ⟨-, -, hq⟩, rfl⟩
  simp only [antoineMap, hT, antoinePerm, add_sub_cancel_left, abs_mul,
    abs_of_pos (show (0 : ℝ) < 7 / 80 by norm_num)] at h1 h2
  have : max |q.1| |q.2.1| < 3 / 4 := max_lt (by linarith) (by linarith)
  linarith

theorem antoine_mem_stage_one_bounds {p : ℝ × ℝ × ℝ} (h : p ∈ antoineStage 1) :
    |p.2.1| ≤ 616 / 640 := by
  obtain ⟨i, q, hq, rfl⟩ := antoine_mem_stage_one h
  have hm := antoineMap_mem i hq
  have := (le_max_right _ _).trans hm.2.1
  have hb := (antoineMap_bounds i hq).2.1
  have e2 : (antoineEy (antoineT i) : ℝ) ≤ 56 := by
    rcases antoineT_cases i with h | h | h <;> simp [h, antoineEy]; norm_num
  have hc : |((antoineZ i).2 : ℝ)| ≤ 560 := by
    rcases antoine_centre_mem i with ⟨-, c2⟩ | ⟨c1, -⟩
    · exact_mod_cast c2
    · exact_mod_cast c1.le
  rw [abs_le] at hb hc ⊢
  constructor <;> linarith

theorem antoine_notMem_stage_one_of (p : ℝ × ℝ × ℝ) (h : ∀ i : Fin 64, p ∉ antoineMap i '' antoineLink) :
    p ∉ antoineStage 1 := by
  intro hp
  obtain ⟨i, q, hq, rfl⟩ := antoine_mem_stage_one hp
  exact h i ⟨q, hq, rfl⟩

set_option maxRecDepth 100000 in
theorem antoine_joined_vert_cert : ∀ j i : Fin 64, antoineT j ≠ 1 →
    (antoineEx (antoineT i) < |(antoineZ j).1 + 35 - (antoineZ i).1| ∨
      antoineEy (antoineT i) < |(antoineZ j).2 + 61 - (antoineZ i).2|) ∨
    (antoineT i = 0 ∧ |(antoineZ j).1 + 35 - (antoineZ i).1| < 42 ∧
      |(antoineZ j).2 + 61 - (antoineZ i).2| < 42) := by
  decide

set_option maxRecDepth 100000 in
theorem antoine_joined_shift_cert : ∀ j i : Fin 64, antoineT j ≠ 1 →
    (antoineEx (antoineT i) < (antoineZ j).1 - (antoineZ i).1 ∨
      (antoineZ j).1 + 35 - (antoineZ i).1 < -antoineEx (antoineT i) ∨
      antoineEy (antoineT i) < |(antoineZ j).2 + 61 - (antoineZ i).2|) ∨
    (antoineT i = 0 ∧ |(antoineZ j).1 - (antoineZ i).1| < 42 ∧
      |(antoineZ j).1 + 35 - (antoineZ i).1| < 42 ∧ |(antoineZ j).2 + 61 - (antoineZ i).2| < 42) ∨
    (antoineT i = 2 ∧ |(antoineZ j).2 + 61 - (antoineZ i).2| < 42) := by
  decide

/-- A segment of `ℝ³` all of whose points lie in `F` joins its ends in `F`. -/
theorem antoine_joinedIn_seg {F : Set (ℝ × ℝ × ℝ)} {a b : ℝ × ℝ × ℝ}
    (h : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → a + t • (b - a) ∈ F) : JoinedIn F a b :=
  ⟨antoineSeg a b, fun t => h t t.2.1 t.2.2⟩

theorem antoine_int_abs_cast {a : ℤ} : (|(a : ℝ)|) = ((|a| : ℤ) : ℝ) := by push_cast; rfl

theorem antoine_abs_div640 (a b : ℝ) : |a / 640 - b / 640| = |a - b| / 640 := by
  rw [← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 640)]

theorem antoine_vert_notMem (j : Fin 64) (hT : antoineT j ≠ 1) (z : ℝ) :
    ((((antoineZ j).1 : ℝ) + 35) / 640, (((antoineZ j).2 : ℝ) + 61) / 640, z) ∉ antoineStage 1 := by
  refine antoine_notMem_stage_one_of _ fun i => ?_
  rcases antoine_joined_vert_cert j i hT with (h | h) | ⟨hi, h1, h2⟩
  · refine antoine_notMem_link_of_box i (Or.inl ?_)
    have h' : ((antoineEx (antoineT i) : ℤ) : ℝ) < |((antoineZ j).1 : ℝ) + 35 - (antoineZ i).1| := by
      exact_mod_cast h
    show _ < |(((antoineZ j).1 : ℝ) + 35) / 640 - _|
    rw [antoine_abs_div640]; linarith
  · refine antoine_notMem_link_of_box i (Or.inr ?_)
    have h' : ((antoineEy (antoineT i) : ℤ) : ℝ) < |((antoineZ j).2 : ℝ) + 61 - (antoineZ i).2| := by
      exact_mod_cast h
    show _ < |(((antoineZ j).2 : ℝ) + 61) / 640 - _|
    rw [antoine_abs_div640]; linarith
  · have h1' : |((antoineZ j).1 : ℝ) + 35 - (antoineZ i).1| < 42 := by exact_mod_cast h1
    have h2' : |((antoineZ j).2 : ℝ) + 61 - (antoineZ i).2| < 42 := by exact_mod_cast h2
    refine antoine_notMem_link_hole0 i hi ?_ ?_
    · show |(((antoineZ j).1 : ℝ) + 35) / 640 - _| < _
      rw [antoine_abs_div640]; linarith
    · show |(((antoineZ j).2 : ℝ) + 61) / 640 - _| < _
      rw [antoine_abs_div640]; linarith

theorem antoine_shift_notMem (j : Fin 64) (hT : antoineT j ≠ 1) {d : ℝ} (hd0 : 0 ≤ d)
    (hd1 : d ≤ 35) :
    ((((antoineZ j).1 : ℝ) + d) / 640, (((antoineZ j).2 : ℝ) + 61) / 640, (0 : ℝ)) ∉
      antoineStage 1 := by
  refine antoine_notMem_stage_one_of _ fun i => ?_
  have hE : (0 : ℝ) ≤ (antoineEx (antoineT i) : ℝ) := by
    rcases antoineT_cases i with h | h | h <;> simp [h, antoineEx]
  rcases antoine_joined_shift_cert j i hT with (h | h | h) | ⟨hi, h1, h1', h2⟩ | ⟨hi, h2⟩
  · refine antoine_notMem_link_of_box i (Or.inl ?_)
    have h' : ((antoineEx (antoineT i) : ℤ) : ℝ) < ((antoineZ j).1 : ℝ) - (antoineZ i).1 := by
      exact_mod_cast h
    show _ < |(((antoineZ j).1 : ℝ) + d) / 640 - _|
    rw [antoine_abs_div640, abs_of_pos (by linarith)]; linarith
  · refine antoine_notMem_link_of_box i (Or.inl ?_)
    have h' : ((antoineZ j).1 : ℝ) + 35 - (antoineZ i).1 < -((antoineEx (antoineT i) : ℤ) : ℝ) := by
      exact_mod_cast h
    show _ < |(((antoineZ j).1 : ℝ) + d) / 640 - _|
    rw [antoine_abs_div640, abs_of_neg (by linarith)]; linarith
  · refine antoine_notMem_link_of_box i (Or.inr ?_)
    have h' : ((antoineEy (antoineT i) : ℤ) : ℝ) < |((antoineZ j).2 : ℝ) + 61 - (antoineZ i).2| := by
      exact_mod_cast h
    show _ < |(((antoineZ j).2 : ℝ) + 61) / 640 - _|
    rw [antoine_abs_div640]; linarith
  · have h1a : |((antoineZ j).1 : ℝ) - (antoineZ i).1| < 42 := by exact_mod_cast h1
    have h1b : |((antoineZ j).1 : ℝ) + 35 - (antoineZ i).1| < 42 := by exact_mod_cast h1'
    have h2' : |((antoineZ j).2 : ℝ) + 61 - (antoineZ i).2| < 42 := by exact_mod_cast h2
    refine antoine_notMem_link_hole0 i hi ?_ ?_
    · show |(((antoineZ j).1 : ℝ) + d) / 640 - _| < _
      rw [antoine_abs_div640, div_lt_div_iff_of_pos_right (by norm_num), abs_lt]
      rw [abs_lt] at h1a h1b
      constructor <;> linarith
    · show |(((antoineZ j).2 : ℝ) + 61) / 640 - _| < _
      rw [antoine_abs_div640]; linarith
  · have h2' : |((antoineZ j).2 : ℝ) + 61 - (antoineZ i).2| < 42 := by exact_mod_cast h2
    refine antoine_notMem_link_hole2 i hi (by simp) ?_
    show |(((antoineZ j).2 : ℝ) + 61) / 640 - _| < _
    rw [antoine_abs_div640]; linarith

theorem antoineMap_merPt_of_ne (j : Fin 64) (hT : antoineT j ≠ 1) :
    antoineMap j antoineMerPt =
      (((antoineZ j).1 : ℝ) / 640, (((antoineZ j).2 : ℝ) + 61) / 640, (0 : ℝ)) := by
  rcases antoineT_cases j with h | h | h
  · simp only [antoineMap, h, antoinePerm, antoineMerPt, Prod.mk.injEq]; refine ⟨by ring, by ring, by ring⟩
  · exact absurd h hT
  · simp only [antoineMap, h, antoinePerm, antoineMerPt, Prod.mk.injEq]; refine ⟨by ring, by ring, by ring⟩

theorem antoineMap_merPt_of_eq (j : Fin 64) (hT : antoineT j = 1) :
    antoineMap j antoineMerPt =
      (((antoineZ j).1 : ℝ) / 640, ((antoineZ j).2 : ℝ) / 640, (61 / 640 : ℝ)) := by
  simp only [antoineMap, hT, antoinePerm, antoineMerPt, Prod.mk.injEq]; refine ⟨by ring, by ring, by ring⟩

/-- `S³ ∖ C₁` joins the base point of the top meridian to the base point of the meridian of
every first-generation link (`joined` of `GX.AntoineFirstGeneration`), in `ℝ³`: up to the plane
`z = 1`, across, and down (after a shift of `35/640` along `x` for the links of types `0` and
`2`). -/
theorem antoine_joined_R3 (j : Fin 64) :
    JoinedIn (antoineStage 1)ᶜ antoineMerPt (antoineMap j antoineMerPt) := by
  have hhigh : ∀ p : ℝ × ℝ × ℝ, 56 / 640 < p.2.2 → p ∈ (antoineStage 1)ᶜ := fun p hp =>
    antoine_not_mem_stage_one_of_z (by rw [abs_of_pos (by linarith)]; exact hp)
  have h0 : JoinedIn (antoineStage 1)ᶜ antoineMerPt (0, 61 / 56, 1) := by
    refine antoine_joinedIn_seg fun t _ _ => fun hp => ?_
    have := antoine_mem_stage_one_bounds hp
    simp only [antoineMerPt, Prod.fst_add, Prod.snd_add, Prod.smul_mk, Prod.mk_sub_mk,
      smul_eq_mul] at this
    rw [abs_le] at this
    norm_num at this
  have hacross : ∀ a b : ℝ, JoinedIn (antoineStage 1)ᶜ (0, 61 / 56, 1) (a, b, 1) := fun a b =>
    antoine_joinedIn_seg fun t _ _ => hhigh _ (by
      simp only [Prod.snd_add, Prod.smul_mk, Prod.mk_sub_mk, smul_eq_mul]; norm_num)
  by_cases hT : antoineT j = 1
  · rw [antoineMap_merPt_of_eq j hT]
    refine (h0.trans (hacross (((antoineZ j).1 : ℝ) / 640) (((antoineZ j).2 : ℝ) / 640))).trans
      (antoine_joinedIn_seg fun t _ ht1 => hhigh _ ?_)
    simp only [Prod.snd_add, Prod.smul_mk, Prod.mk_sub_mk, smul_eq_mul]
    nlinarith
  · rw [antoineMap_merPt_of_ne j hT]
    refine ((h0.trans (hacross ((((antoineZ j).1 : ℝ) + 35) / 640)
      ((((antoineZ j).2 : ℝ) + 61) / 640))).trans
      (antoine_joinedIn_seg fun t _ _ => ?_)).trans (antoine_joinedIn_seg fun t ht0 ht1 => ?_)
      (y := ((((antoineZ j).1 : ℝ) + 35) / 640, (((antoineZ j).2 : ℝ) + 61) / 640, (0 : ℝ)))
    · have e : ((((antoineZ j).1 : ℝ) + 35) / 640, (((antoineZ j).2 : ℝ) + 61) / 640, (1 : ℝ)) +
          t • (((((antoineZ j).1 : ℝ) + 35) / 640, (((antoineZ j).2 : ℝ) + 61) / 640, (0 : ℝ)) -
            ((((antoineZ j).1 : ℝ) + 35) / 640, (((antoineZ j).2 : ℝ) + 61) / 640, (1 : ℝ))) =
          ((((antoineZ j).1 : ℝ) + 35) / 640, (((antoineZ j).2 : ℝ) + 61) / 640, 1 - t) := by
        simp only [Prod.smul_mk, Prod.mk_sub_mk, Prod.mk_add_mk, smul_eq_mul, Prod.mk.injEq]
        refine ⟨by ring, by ring, by ring⟩
      rw [e]; exact antoine_vert_notMem j hT _
    · have e : ((((antoineZ j).1 : ℝ) + 35) / 640, (((antoineZ j).2 : ℝ) + 61) / 640, (0 : ℝ)) +
          t • ((((antoineZ j).1 : ℝ) / 640, (((antoineZ j).2 : ℝ) + 61) / 640, (0 : ℝ)) -
            ((((antoineZ j).1 : ℝ) + 35) / 640, (((antoineZ j).2 : ℝ) + 61) / 640, (0 : ℝ))) =
          ((((antoineZ j).1 : ℝ) + 35 * (1 - t)) / 640, (((antoineZ j).2 : ℝ) + 61) / 640,
            (0 : ℝ)) := by
        simp only [Prod.smul_mk, Prod.mk_sub_mk, Prod.mk_add_mk, smul_eq_mul, Prod.mk.injEq]
        refine ⟨by ring, by ring, by ring⟩
      rw [e]; exact antoine_shift_notMem j hT (by nlinarith) (by nlinarith)

/-- `joined` of `GX.AntoineFirstGeneration`, in `S³`. -/
theorem antoine_joined (j : Fin 64) :
    JoinedIn (antoineStereo '' antoineStage 1)ᶜ (antoineStereo antoineMerPt) (antoineX1 j) := by
  refine ((antoine_joined_R3 j).map continuous_antoineStereo).mono ?_
  rintro _ ⟨p, hp, rfl⟩ ⟨q, hq, e⟩
  exact hp (antoineStereo_injective e ▸ hq)


/-! ### The collar of a link: coordinates -/

/-- The square radius `ρ = max(|x|, |y|)`. -/
def antoineRho (p : ℝ × ℝ × ℝ) : ℝ := max |p.1| |p.2.1|

/-- The longitudinal coordinate `x + i y` of the collar. -/
def antoineAng (p : ℝ × ℝ × ℝ) : ℂ := (p.1 : ℂ) + (p.2.1 : ℂ) * Complex.I

/-- The meridional coordinate `(ρ - 7/8) + i z` of the collar. -/
def antoineW (p : ℝ × ℝ × ℝ) : ℂ := ((antoineRho p - 7 / 8 : ℝ) : ℂ) + (p.2.2 : ℂ) * Complex.I

/-- The collar `N ∖ L` of the link, in `ℝ³`. -/
def antoineA0 : Set (ℝ × ℝ × ℝ) := antoineNbhd \ antoineLink

theorem continuous_antoineRho : Continuous antoineRho := by unfold antoineRho; fun_prop
theorem continuous_antoineAng : Continuous antoineAng := by unfold antoineAng; fun_prop
theorem continuous_antoineW : Continuous antoineW := by
  unfold antoineW; have := continuous_antoineRho; fun_prop

theorem antoineW_normSq (p : ℝ × ℝ × ℝ) :
    ‖antoineW p‖ ^ 2 = (antoineRho p - 7 / 8) ^ 2 + p.2.2 ^ 2 := by
  rw [Complex.sq_norm, antoineW, Complex.normSq_add_mul_I]

theorem antoineAng_normSq (p : ℝ × ℝ × ℝ) : ‖antoineAng p‖ ^ 2 = p.1 ^ 2 + p.2.1 ^ 2 := by
  rw [Complex.sq_norm, antoineAng, Complex.normSq_add_mul_I]

theorem mem_antoineNbhd_iff (p : ℝ × ℝ × ℝ) : p ∈ antoineNbhd ↔ ‖antoineW p‖ ^ 2 < 1 / 16 := by
  rw [antoineW_normSq]; rfl

/-- A point of the tube is in the link iff its meridional coordinate is in the square
`[-1/8, 1/8]²`. -/
theorem mem_antoineLink_iff (p : ℝ × ℝ × ℝ) :
    p ∈ antoineLink ↔ |antoineRho p - 7 / 8| ≤ 1 / 8 ∧ |p.2.2| ≤ 1 / 8 := by
  show (|p.2.2| ≤ 1 / 8 ∧ antoineRho p ≤ 1 ∧ 3 / 4 ≤ antoineRho p) ↔ _
  rw [abs_le (a := antoineRho p - 7 / 8)]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨by linarith, by linarith⟩, h1⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h3, by linarith, by linarith⟩

theorem antoineRho_nonneg (p : ℝ × ℝ × ℝ) : 0 ≤ antoineRho p :=
  (abs_nonneg _).trans (le_max_left _ _)

theorem antoineRho_gt_of_mem_nbhd {p : ℝ × ℝ × ℝ} (hp : p ∈ antoineNbhd) : 5 / 8 < antoineRho p := by
  rw [mem_antoineNbhd_iff, antoineW_normSq] at hp
  nlinarith [sq_nonneg p.2.2]

theorem antoineW_norm_gt_of_mem {p : ℝ × ℝ × ℝ} (hp : p ∈ antoineA0) : 1 / 8 < ‖antoineW p‖ := by
  obtain ⟨-, hp⟩ := hp
  rw [mem_antoineLink_iff] at hp
  by_contra hc
  push Not at hc
  have h2 := antoineW_normSq p
  have hn : ‖antoineW p‖ ^ 2 ≤ 1 / 64 := by
    have := norm_nonneg (antoineW p); nlinarith
  have ha : (antoineRho p - 7 / 8) ^ 2 ≤ 1 / 64 := by nlinarith [sq_nonneg p.2.2]
  have hb : p.2.2 ^ 2 ≤ 1 / 64 := by nlinarith [sq_nonneg (antoineRho p - 7 / 8)]
  exact hp ⟨abs_le.2 ⟨by nlinarith, by nlinarith⟩, abs_le.2 ⟨by nlinarith, by nlinarith⟩⟩


/-- `max(|cos α|, |sin α|)`, the square radius of the unit vector of angle `α`. -/
def antoineM (α : ℝ) : ℝ := max |Real.cos α| |Real.sin α|

theorem antoineM_pos (α : ℝ) : 0 < antoineM α := by
  by_contra h
  push Not at h
  have h1 : |Real.cos α| ≤ 0 := (le_max_left _ _).trans h
  have h2 : |Real.sin α| ≤ 0 := (le_max_right _ _).trans h
  have := Real.sin_sq_add_cos_sq α
  have e1 : Real.cos α = 0 := abs_nonpos_iff.1 h1
  have e2 : Real.sin α = 0 := abs_nonpos_iff.1 h2
  rw [e1, e2] at this; norm_num at this

theorem continuous_antoineM : Continuous antoineM := by unfold antoineM; fun_prop

/-- The parametrisation of the torus `|W| = 3/14` of the collar by the two angles. -/
def antoineE (α β : ℝ) : ℝ × ℝ × ℝ :=
  ((7 / 8 + 3 / 14 * Real.cos β) / antoineM α * Real.cos α,
    (7 / 8 + 3 / 14 * Real.cos β) / antoineM α * Real.sin α, 3 / 14 * Real.sin β)

theorem antoineRho_smul (r α : ℝ) (hr : 0 ≤ r) :
    max |r * Real.cos α| |r * Real.sin α| = r * antoineM α := by
  rw [abs_mul, abs_mul, abs_of_nonneg hr, antoineM, mul_max_of_nonneg _ _ hr]

theorem antoineRho_E (α β : ℝ) : antoineRho (antoineE α β) = 7 / 8 + 3 / 14 * Real.cos β := by
  have hm := antoineM_pos α
  have hr : 0 ≤ (7 / 8 + 3 / 14 * Real.cos β) / antoineM α := by
    have := Real.neg_one_le_cos β
    exact div_nonneg (by linarith) hm.le
  show max |_ * Real.cos α| |_ * Real.sin α| = _
  rw [antoineRho_smul _ _ hr, div_mul_cancel₀ _ hm.ne']

theorem antoineW_E (α β : ℝ) :
    antoineW (antoineE α β) = (3 / 14 : ℂ) * Complex.exp (β * Complex.I) := by
  rw [antoineW, antoineRho_E, Complex.exp_mul_I]
  apply Complex.ext <;> simp [antoineE]

theorem antoineE_mem (α β : ℝ) : antoineE α β ∈ antoineA0 := by
  have hW : ‖antoineW (antoineE α β)‖ = 3 / 14 := by
    rw [antoineW_E, norm_mul, Complex.norm_exp_ofReal_mul_I]; norm_num
  refine ⟨?_, fun hL => ?_⟩
  · rw [mem_antoineNbhd_iff, hW]; norm_num
  · rw [mem_antoineLink_iff] at hL
    have h2 := antoineW_normSq (antoineE α β)
    rw [hW] at h2
    obtain ⟨h3, h4⟩ := hL
    have h5 : (antoineRho (antoineE α β) - 7 / 8) ^ 2 ≤ 1 / 64 := by
      rw [← sq_abs]; nlinarith [abs_nonneg (antoineRho (antoineE α β) - 7 / 8)]
    have h6 : (antoineE α β).2.2 ^ 2 ≤ 1 / 64 := by
      rw [← sq_abs]; nlinarith [abs_nonneg (antoineE α β).2.2]
    nlinarith

theorem continuous_antoineE : Continuous fun q : ℝ × ℝ => antoineE q.1 q.2 := by
  have hm : Continuous fun q : ℝ × ℝ => antoineM q.1 := continuous_antoineM.comp continuous_fst
  have hd : Continuous fun q : ℝ × ℝ => (7 / 8 + 3 / 14 * Real.cos q.2) / antoineM q.1 :=
    (by fun_prop : Continuous fun q : ℝ × ℝ => 7 / 8 + 3 / 14 * Real.cos q.2).div hm
      fun q => (antoineM_pos q.1).ne'
  unfold antoineE
  fun_prop

/-- A point with longitudinal polar coordinates `r e^{iα}` (`r > 0`) and meridional coordinate
`(3/14) e^{iβ}` is `antoineE α β`. -/
theorem antoineE_eq_of {q : ℝ × ℝ × ℝ} {r α β : ℝ} (hr : 0 < r) (h1 : q.1 = r * Real.cos α)
    (h2 : q.2.1 = r * Real.sin α) (h3 : antoineRho q = 7 / 8 + 3 / 14 * Real.cos β)
    (h4 : q.2.2 = 3 / 14 * Real.sin β) : antoineE α β = q := by
  have hρ : antoineRho q = r * antoineM α := by
    show max |q.1| |q.2.1| = _
    rw [h1, h2, antoineRho_smul _ _ hr.le]
  have hm := antoineM_pos α
  have e : (7 / 8 + 3 / 14 * Real.cos β) / antoineM α = r := by
    rw [← h3, hρ, mul_div_cancel_right₀ _ hm.ne']
  obtain ⟨q1, q2, q3⟩ := q
  simp only at h1 h2 h4
  simp only [antoineE, e, h1, h2, h4]

/-- Scaling the meridional coordinate by `λ`, keeping the longitudinal direction. -/
def antoineScale (p : ℝ × ℝ × ℝ) (l : ℝ) : ℝ × ℝ × ℝ :=
  (p.1 * ((7 / 8 + l * (antoineRho p - 7 / 8)) / antoineRho p),
    p.2.1 * ((7 / 8 + l * (antoineRho p - 7 / 8)) / antoineRho p), l * p.2.2)

theorem antoineRho_scale {p : ℝ × ℝ × ℝ} (hp : 0 < antoineRho p) {l : ℝ}
    (hl : 0 ≤ 7 / 8 + l * (antoineRho p - 7 / 8)) :
    antoineRho (antoineScale p l) = 7 / 8 + l * (antoineRho p - 7 / 8) := by
  have hσ : 0 ≤ (7 / 8 + l * (antoineRho p - 7 / 8)) / antoineRho p := div_nonneg hl hp.le
  show max |p.1 * _| |p.2.1 * _| = _
  rw [abs_mul, abs_mul, abs_of_nonneg hσ, ← max_mul_of_nonneg _ _ hσ]
  show antoineRho p * _ = _
  field_simp

theorem antoineW_scale {p : ℝ × ℝ × ℝ} (hp : 0 < antoineRho p) {l : ℝ}
    (hl : 0 ≤ 7 / 8 + l * (antoineRho p - 7 / 8)) :
    antoineW (antoineScale p l) = (l : ℂ) * antoineW p := by
  rw [antoineW, antoineRho_scale hp hl, antoineW]
  apply Complex.ext <;> simp [antoineScale]

theorem antoineScale_one {p : ℝ × ℝ × ℝ} (hp : 0 < antoineRho p) : antoineScale p 1 = p := by
  obtain ⟨a, b, c⟩ := p
  simp only [antoineScale, one_mul, add_sub_cancel, div_self hp.ne', mul_one]

theorem antoineScale_mem {p : ℝ × ℝ × ℝ} (hp : p ∈ antoineA0) {l : ℝ} (hl : 0 < l)
    (hl1 : l * ‖antoineW p‖ < 1 / 4) (hl2 : 1 ≤ l ∨ 3 / 14 ≤ l * ‖antoineW p‖) :
    antoineScale p l ∈ antoineA0 := by
  have hρ := antoineRho_gt_of_mem_nbhd hp.1
  have hW := antoineW_norm_gt_of_mem hp
  have hu : |antoineRho p - 7 / 8| ≤ ‖antoineW p‖ := by
    have := antoineW_normSq p
    exact abs_le_of_sq_le_sq' (by nlinarith [sq_nonneg p.2.2]) (norm_nonneg _) |>.elim
      (fun h1 h2 => abs_le.2 ⟨h1, h2⟩)
  have hpos : 0 ≤ 7 / 8 + l * (antoineRho p - 7 / 8) := by
    have : |l * (antoineRho p - 7 / 8)| < 1 / 4 := by
      rw [abs_mul, abs_of_pos hl]
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hu hl.le) hl1
    rw [abs_lt] at this; linarith
  have hWs : ‖antoineW (antoineScale p l)‖ = l * ‖antoineW p‖ := by
    rw [antoineW_scale (by linarith) hpos, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hl]
  refine ⟨?_, fun hL => ?_⟩
  · rw [mem_antoineNbhd_iff, hWs]
    have := mul_nonneg hl.le (norm_nonneg (antoineW p))
    nlinarith
  · rw [mem_antoineLink_iff, antoineRho_scale (by linarith) hpos] at hL
    obtain ⟨h3, h4⟩ := hL
    simp only [antoineScale] at h4
    rw [add_sub_cancel_left] at h3
    rcases hl2 with hl2 | hl2
    · -- `λ ≥ 1`: the unscaled point was in the square already
      refine hp.2 ((mem_antoineLink_iff p).2 ⟨?_, ?_⟩)
      · rw [abs_mul, abs_of_pos hl] at h3
        nlinarith [abs_nonneg (antoineRho p - 7 / 8)]
      · rw [abs_mul, abs_of_pos hl] at h4
        nlinarith [abs_nonneg p.2.2]
    · have h2 := antoineW_normSq (antoineScale p l)
      rw [hWs, antoineRho_scale (by linarith) hpos, add_sub_cancel_left] at h2
      simp only [antoineScale] at h2
      have h5 : (l * (antoineRho p - 7 / 8)) ^ 2 ≤ 1 / 64 := by
        rw [← sq_abs]; nlinarith [abs_nonneg (l * (antoineRho p - 7 / 8))]
      have h6 : (l * p.2.2) ^ 2 ≤ 1 / 64 := by
        rw [← sq_abs]; nlinarith [abs_nonneg (l * p.2.2)]
      nlinarith

/-- The meridional factor `3/14 / |W|` retracting the collar onto the torus `|W| = 3/14`. -/
def antoineK (p : ℝ × ℝ × ℝ) : ℝ := 3 / 14 / ‖antoineW p‖

theorem antoineScale_K_eq {p : ℝ × ℝ × ℝ} (hp : p ∈ antoineA0) :
    antoineE (Complex.arg (antoineAng p)) (Complex.arg (antoineW p)) =
      antoineScale p (antoineK p) := by
  have hρ := antoineRho_gt_of_mem_nbhd hp.1
  have hW := antoineW_norm_gt_of_mem hp
  have hW0 : antoineW p ≠ 0 := fun h => by rw [h, norm_zero] at hW; norm_num at hW
  have hA0 : antoineAng p ≠ 0 := by
    intro h
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp [antoineAng] at h1 h2
    have : antoineRho p = 0 := by simp [antoineRho, h1, h2]
    linarith
  have hk : 0 < antoineK p := div_pos (by norm_num) (by linarith)
  have hkW : antoineK p * ‖antoineW p‖ = 3 / 14 := div_mul_cancel₀ _ (by linarith)
  have hu : |antoineRho p - 7 / 8| ≤ ‖antoineW p‖ := by
    have := antoineW_normSq p
    exact abs_le_of_sq_le_sq' (by nlinarith [sq_nonneg p.2.2]) (norm_nonneg _) |>.elim
      (fun h1 h2 => abs_le.2 ⟨h1, h2⟩)
  have hku : |antoineK p * (antoineRho p - 7 / 8)| ≤ 3 / 14 := by
    rw [abs_mul, abs_of_pos hk, ← hkW]; exact mul_le_mul_of_nonneg_left hu hk.le
  rw [abs_le] at hku
  have hpos : 0 ≤ 7 / 8 + antoineK p * (antoineRho p - 7 / 8) := by linarith
  have hσ : 0 < (7 / 8 + antoineK p * (antoineRho p - 7 / 8)) / antoineRho p :=
    div_pos (by linarith) (by linarith)
  have hWn : 0 < ‖antoineW p‖ := by linarith
  refine antoineE_eq_of (r := ‖antoineAng p‖ * ((7 / 8 + antoineK p * (antoineRho p - 7 / 8)) /
    antoineRho p)) (mul_pos (norm_pos_iff.2 hA0) hσ) ?_ ?_ ?_ ?_
  · show p.1 * _ = _
    rw [mul_comm ‖antoineAng p‖, mul_assoc, Complex.norm_mul_cos_arg]
    simp [antoineAng]; ring
  · show p.2.1 * _ = _
    rw [mul_comm ‖antoineAng p‖, mul_assoc, Complex.norm_mul_sin_arg]
    simp [antoineAng]; ring
  · rw [antoineRho_scale (by linarith) hpos, Complex.cos_arg hW0]
    simp only [antoineW, antoineK, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one, add_zero]
    field_simp
  · rw [Complex.sin_arg]
    simp only [antoineScale, antoineW, antoineK, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add,
      add_zero]
    field_simp


theorem antoineK_pos {p : ℝ × ℝ × ℝ} (hp : p ∈ antoineA0) : 0 < antoineK p :=
  div_pos (by norm_num) ((antoineW_norm_gt_of_mem hp).trans' (by norm_num))

theorem antoineK_mul {p : ℝ × ℝ × ℝ} (hp : p ∈ antoineA0) : antoineK p * ‖antoineW p‖ = 3 / 14 :=
  div_mul_cancel₀ _ ((antoineW_norm_gt_of_mem hp).trans' (by norm_num)).ne'

/-- The interpolation `(1 - s) + s K` between `1` and the retraction factor keeps a point of the
collar in the collar. -/
theorem antoineScale_interp_mem {p : ℝ × ℝ × ℝ} (hp : p ∈ antoineA0) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) : antoineScale p (1 - s + s * antoineK p) ∈ antoineA0 := by
  have hk := antoineK_pos hp
  have hkW := antoineK_mul hp
  have hW := antoineW_norm_gt_of_mem hp
  have hWlt : ‖antoineW p‖ < 1 / 4 := by
    have h := (mem_antoineNbhd_iff p).1 hp.1
    nlinarith [norm_nonneg (antoineW p)]
  have e : (1 - s + s * antoineK p) * ‖antoineW p‖ = (1 - s) * ‖antoineW p‖ + s * (3 / 14) := by
    rw [← hkW]; ring
  refine antoineScale_mem hp (by nlinarith) (by rw [e]; nlinarith) ?_
  rcases le_or_gt 1 (antoineK p) with h | h
  · left; nlinarith
  · right
    rw [e]
    have : 3 / 14 < ‖antoineW p‖ := by
      by_contra hc; push Not at hc
      have : 1 ≤ antoineK p := by
        rw [antoineK, le_div_iff₀ (by linarith)]; linarith
      linarith
    nlinarith

/-- The collar `N ∖ L` is path-connected: every point joins the torus `|W| = 3/14` by scaling
`W`, and the torus is the image of `ℝ²` (`GX.antoineE`). -/
theorem isPathConnected_antoineA0 : IsPathConnected antoineA0 := by
  have hR : IsPathConnected (range fun q : ℝ × ℝ => antoineE q.1 q.2) :=
    isPathConnected_range continuous_antoineE
  have hRA : (range fun q : ℝ × ℝ => antoineE q.1 q.2) ⊆ antoineA0 := by
    rintro _ ⟨q, rfl⟩; exact antoineE_mem _ _
  refine ⟨antoineE 0 0, antoineE_mem 0 0, fun y hy => ?_⟩
  have hρ := antoineRho_gt_of_mem_nbhd hy.1
  let γ : Path y (antoineScale y (antoineK y)) :=
    { toFun := fun s => antoineScale y (1 - (s : ℝ) + (s : ℝ) * antoineK y)
      continuous_toFun := by unfold antoineScale; fun_prop
      source' := by simp only [Icc.coe_zero, sub_zero, zero_mul, add_zero]; exact antoineScale_one (by linarith)
      target' := by simp only [Icc.coe_one, sub_self, one_mul, zero_add] }
  have h1 : JoinedIn antoineA0 y (antoineScale y (antoineK y)) :=
    ⟨γ, fun s => antoineScale_interp_mem hy s.2.1 s.2.2⟩
  have h2 : JoinedIn antoineA0 (antoineE 0 0) (antoineScale y (antoineK y)) := by
    rw [← antoineScale_K_eq hy]
    exact (hR.joinedIn _ ⟨(0, 0), rfl⟩ _ ⟨(_, _), rfl⟩).mono hRA
  exact h2.trans h1.symm

/-- The collar of the `j`-th link is the image of `GX.antoineA0`. -/
theorem antoineA1_eq (j : Fin 64) :
    antoineA1 j = (antoineStereo ∘ antoineMap j) '' antoineA0 := by
  rw [antoineA1, antoineN1, antoineL1, ← image_comp, ← image_comp, antoineA0,
    image_sdiff (antoineStereo_injective.comp (antoineMap_injective j))]

/-- `collar_conn` of `GX.AntoineFirstGeneration`. -/
theorem antoine_collar_conn (j : Fin 64) : IsPathConnected (antoineA1 j) := by
  rw [antoineA1_eq]
  exact isPathConnected_antoineA0.image (continuous_antoineStereo.comp (continuous_antoineMap j))


/-! ### The collar: classification of loops by the two windings -/

/-- `f` has an `exp`-lift whose total increment is `n · 2πi`. -/
def AntoineLiftWind (f : I → ℂ) (n : ℤ) : Prop :=
  ∃ Γ : C(I, ℂ), (∀ t, Complex.exp (Γ t) = f t) ∧ Γ 1 = Γ 0 + n * (2 * Real.pi * Complex.I)

theorem antoineLiftWind_cWinding {z : CStar} (γ : Path z z) :
    AntoineLiftWind (fun t => (γ t : ℂ)) (cWinding γ) := by
  obtain ⟨Γ, hΓ⟩ := exists_expLift γ.toContinuousMap
  exact ⟨Γ, hΓ, cWinding_spec γ hΓ⟩

theorem AntoineLiftWind.congr {f g : I → ℂ} {n : ℤ} (h : AntoineLiftWind f n) (e : ∀ t, f t = g t) :
    AntoineLiftWind g n := by
  obtain ⟨Γ, h1, h2⟩ := h
  exact ⟨Γ, fun t => (h1 t).trans (e t), h2⟩

/-- Two lifts of loops with equal winding, through the same base value, can be chosen with
equal ends. -/
theorem AntoineLiftWind.align {f g : I → ℂ} {n : ℤ} (hf : AntoineLiftWind f n)
    (hg : AntoineLiftWind g n) (h0 : f 0 = g 0) :
    ∃ Γf Γg : C(I, ℂ), (∀ t, Complex.exp (Γf t) = f t) ∧ (∀ t, Complex.exp (Γg t) = g t) ∧
      Γf 0 = Γg 0 ∧ Γf 1 = Γg 1 := by
  obtain ⟨Γ₁, h1, e1⟩ := hf
  obtain ⟨Γ₂, h2, e2⟩ := hg
  refine ⟨Γ₁, ⟨fun t => Γ₂ t + (Γ₁ 0 - Γ₂ 0), by fun_prop⟩, h1, fun t => ?_, ?_, ?_⟩
  · show Complex.exp (Γ₂ t + (Γ₁ 0 - Γ₂ 0)) = g t
    have hne : Complex.exp (Γ₂ 0) ≠ 0 := Complex.exp_ne_zero _
    rw [Complex.exp_add, Complex.exp_sub, h1, h2, h2, h0, div_self (h2 0 ▸ hne), mul_one]
  · show Γ₁ 0 = Γ₂ 0 + (Γ₁ 0 - Γ₂ 0); ring
  · show Γ₁ 1 = Γ₂ 1 + (Γ₁ 0 - Γ₂ 0); rw [e1, e2]; ring

theorem antoineAng_ne_zero {p : ℝ × ℝ × ℝ} (hp : 0 < antoineRho p) : antoineAng p ≠ 0 := by
  intro h
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp [antoineAng] at h1 h2
  have : antoineRho p = 0 := by simp [antoineRho, h1, h2]
  linarith

theorem antoineW_ne_zero {p : ℝ × ℝ × ℝ} (hp : p ∈ antoineA0) : antoineW p ≠ 0 := fun h => by
  have := antoineW_norm_gt_of_mem hp; rw [h, norm_zero] at this; norm_num at this

/-- The retraction of the collar onto the torus, in polar form (any angles). -/
theorem antoineScale_K_eq_of {p : ℝ × ℝ × ℝ} (hp : p ∈ antoineA0) {α β : ℝ}
    (hα1 : p.1 = ‖antoineAng p‖ * Real.cos α) (hα2 : p.2.1 = ‖antoineAng p‖ * Real.sin α)
    (hβ1 : antoineRho p - 7 / 8 = ‖antoineW p‖ * Real.cos β)
    (hβ2 : p.2.2 = ‖antoineW p‖ * Real.sin β) :
    antoineE α β = antoineScale p (antoineK p) := by
  have hρ := antoineRho_gt_of_mem_nbhd hp.1
  have hW := antoineW_norm_gt_of_mem hp
  have hk := antoineK_pos hp
  have hkW := antoineK_mul hp
  have hu : |antoineRho p - 7 / 8| ≤ ‖antoineW p‖ := by
    have := antoineW_normSq p
    exact abs_le_of_sq_le_sq' (by nlinarith [sq_nonneg p.2.2]) (norm_nonneg _) |>.elim
      (fun h1 h2 => abs_le.2 ⟨h1, h2⟩)
  have hku : |antoineK p * (antoineRho p - 7 / 8)| ≤ 3 / 14 := by
    rw [abs_mul, abs_of_pos hk, ← hkW]; exact mul_le_mul_of_nonneg_left hu hk.le
  rw [abs_le] at hku
  have hpos : 0 ≤ 7 / 8 + antoineK p * (antoineRho p - 7 / 8) := by linarith
  have hσ : 0 < (7 / 8 + antoineK p * (antoineRho p - 7 / 8)) / antoineRho p :=
    div_pos (by linarith) (by linarith)
  refine antoineE_eq_of (r := ‖antoineAng p‖ * ((7 / 8 + antoineK p * (antoineRho p - 7 / 8)) /
    antoineRho p)) (mul_pos (norm_pos_iff.2 (antoineAng_ne_zero (by linarith))) hσ) ?_ ?_ ?_ ?_
  · show p.1 * _ = _
    rw [hα1]; ring
  · show p.2.1 * _ = _
    rw [hα2]; ring
  · rw [antoineRho_scale (by linarith) hpos, hβ1, ← mul_assoc, hkW]
  · show antoineK p * p.2.2 = _
    rw [hβ2, ← mul_assoc, hkW]

theorem antoine_polar_of_exp {w : ℂ} {Γ : ℂ} (h : Complex.exp Γ = w) :
    w.re = ‖w‖ * Real.cos Γ.im ∧ w.im = ‖w‖ * Real.sin Γ.im := by
  rw [← h, Complex.norm_exp, Complex.exp_re, Complex.exp_im]
  exact ⟨rfl, rfl⟩

/-- The retracted loop `R ∘ δ` of a loop of the collar based on the torus `|W| = 3/14`. -/
def antoineRetr (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ := antoineScale p (antoineK p)

theorem antoineW_merPt : antoineW antoineMerPt = 3 / 14 := by
  have : antoineRho antoineMerPt = 61 / 56 := by
    simp only [antoineRho, antoineMerPt, abs_zero]
    rw [abs_of_pos (by norm_num), max_eq_right (by norm_num)]; norm_num
  rw [antoineW, this]; simp [antoineMerPt]; norm_num

theorem antoineK_merPt : antoineK antoineMerPt = 1 := by
  rw [antoineK, antoineW_merPt]; norm_num

theorem antoineRho_merPt : antoineRho antoineMerPt = 61 / 56 := by
  simp only [antoineRho, antoineMerPt, abs_zero]
  rw [abs_of_pos (by norm_num), max_eq_right (by norm_num)]; norm_num

theorem antoineMerPt_mem : antoineMerPt ∈ antoineA0 := by
  have := antoineMeridian_mem_nbhd 0
  refine ⟨by simpa using this, fun h => ?_⟩
  have := antoineMeridian_not_mem 0
  simp at this
  exact this h

theorem antoineRetr_merPt : antoineRetr antoineMerPt = antoineMerPt := by
  rw [antoineRetr, antoineK_merPt]; exact antoineScale_one (by rw [antoineRho_merPt]; norm_num)

/-- Continuity of the scaling along a loop of the collar. -/
theorem antoine_continuous_scale_along {δ : C(I, ℝ × ℝ × ℝ)} (hδ : ∀ t, δ t ∈ antoineA0)
    {l : I × I → ℝ} (hl : Continuous l) :
    Continuous fun z : I × I => antoineScale (δ z.2) (l z) := by
  have hρ : Continuous fun z : I × I => antoineRho (δ z.2) :=
    continuous_antoineRho.comp (δ.continuous.comp continuous_snd)
  have hρ0 : ∀ z : I × I, antoineRho (δ z.2) ≠ 0 := fun z =>
    (antoineRho_gt_of_mem_nbhd (hδ z.2).1).trans' (by norm_num) |>.ne'
  have hσ : Continuous fun z : I × I =>
      (7 / 8 + l z * (antoineRho (δ z.2) - 7 / 8)) / antoineRho (δ z.2) :=
    (continuous_const.add (hl.mul (hρ.sub continuous_const))).div hρ hρ0
  have hd : Continuous fun z : I × I => δ z.2 := δ.continuous.comp continuous_snd
  exact ((continuous_fst.comp hd).mul hσ).prodMk
    (((continuous_fst.comp (continuous_snd.comp hd)).mul hσ).prodMk
      (hl.mul (continuous_snd.comp (continuous_snd.comp hd))))

theorem antoine_continuous_K_along {δ : C(I, ℝ × ℝ × ℝ)} (hδ : ∀ t, δ t ∈ antoineA0) :
    Continuous fun t => antoineK (δ t) :=
  continuous_const.div (continuous_norm.comp (continuous_antoineW.comp δ.continuous))
    fun t => ((antoineW_norm_gt_of_mem (hδ t)).trans' (by norm_num)).ne'

theorem antoine_continuous_retr_along {δ : C(I, ℝ × ℝ × ℝ)} (hδ : ∀ t, δ t ∈ antoineA0) :
    Continuous fun t => antoineRetr (δ t) := by
  have hK := antoine_continuous_K_along hδ
  have := antoine_continuous_scale_along hδ (l := fun z => antoineK (δ z.2))
    (hK.comp (continuous_snd : Continuous fun z : I × I => z.2))
  exact this.comp ((continuous_const : Continuous fun _ : I => (0 : I)).prodMk continuous_id)

/-- The retracted loop `R ∘ δ`, on the torus `|W| = 3/14`. -/
def antoineRetrLoop (δ : Path antoineMerPt antoineMerPt) (hδ : ∀ t, δ t ∈ antoineA0) :
    Path antoineMerPt antoineMerPt where
  toFun t := antoineRetr (δ t)
  continuous_toFun := antoine_continuous_retr_along (δ := δ.toContinuousMap) hδ
  source' := by simp [antoineRetr_merPt]
  target' := by simp [antoineRetr_merPt]

/-- `δ ≃ R ∘ δ` in the collar. -/
theorem antoine_homotopicIn_retr {δ : Path antoineMerPt antoineMerPt}
    (hδ : ∀ t, δ t ∈ antoineA0) : HomotopicIn antoineA0 δ (antoineRetrLoop δ hδ) := by
  have hK := antoine_continuous_K_along (δ := δ.toContinuousMap) hδ
  have hc := antoine_continuous_scale_along (δ := δ.toContinuousMap) hδ
    (l := fun z => 1 - (z.1 : ℝ) + (z.1 : ℝ) * antoineK (δ z.2))
    (by have := hK.comp (continuous_snd : Continuous fun z : I × I => z.2); fun_prop)
  refine ⟨{ toFun := fun z => antoineScale (δ z.2) (1 - (z.1 : ℝ) + (z.1 : ℝ) * antoineK (δ z.2))
            continuous_toFun := hc
            map_zero_left := fun t => ?_
            map_one_left := fun t => ?_
            prop' := fun s t ht => ?_ }, fun z => ?_⟩
  · simp only [Icc.coe_zero, sub_zero, zero_mul, add_zero]
    exact antoineScale_one ((antoineRho_gt_of_mem_nbhd (hδ t).1).trans' (by norm_num))
  · simp only [Icc.coe_one, sub_self, one_mul, zero_add]; rfl
  · rcases ht with rfl | rfl
    · show antoineScale (δ 0) _ = δ 0
      rw [δ.source, antoineK_merPt, mul_one, sub_add_cancel]
      exact antoineScale_one (by rw [antoineRho_merPt]; norm_num)
    · show antoineScale (δ 1) _ = δ 1
      rw [δ.target, antoineK_merPt, mul_one, sub_add_cancel]
      exact antoineScale_one (by rw [antoineRho_merPt]; norm_num)
  · exact antoineScale_interp_mem (hδ z.2) z.1.2.1 z.1.2.2

/-- The retracted loop through lifts of its two coordinates. -/
theorem antoineRetrLoop_eq {δ : Path antoineMerPt antoineMerPt} (hδ : ∀ t, δ t ∈ antoineA0)
    {ΓA ΓW : C(I, ℂ)} (hA : ∀ t, Complex.exp (ΓA t) = antoineAng (δ t))
    (hW : ∀ t, Complex.exp (ΓW t) = antoineW (δ t)) (t : I) :
    antoineRetrLoop δ hδ t = antoineE (ΓA t).im (ΓW t).im := by
  obtain ⟨a1, a2⟩ := antoine_polar_of_exp (hA t)
  obtain ⟨b1, b2⟩ := antoine_polar_of_exp (hW t)
  simp only [antoineAng, antoineW, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, sub_zero, Complex.add_im,
    Complex.mul_im, mul_one, zero_add, add_zero] at a1 a2 b1 b2
  exact (antoineScale_K_eq_of (hδ t) a1 a2 b1 b2).symm

/-- **The collar is classified by the two windings**: two loops of the collar `N ∖ L` based at the
meridian's base point, with equal longitudinal and equal meridional windings, are homotopic in
the collar (`π₁(T² × I) = ℤ²`). -/
theorem antoine_collar_classify {δ₁ δ₂ : Path antoineMerPt antoineMerPt}
    (h₁ : ∀ t, δ₁ t ∈ antoineA0) (h₂ : ∀ t, δ₂ t ∈ antoineA0) {a b : ℤ}
    (hA₁ : AntoineLiftWind (fun t => antoineAng (δ₁ t)) a)
    (hA₂ : AntoineLiftWind (fun t => antoineAng (δ₂ t)) a)
    (hW₁ : AntoineLiftWind (fun t => antoineW (δ₁ t)) b)
    (hW₂ : AntoineLiftWind (fun t => antoineW (δ₂ t)) b) : HomotopicIn antoineA0 δ₁ δ₂ := by
  obtain ⟨A₁, A₂, eA₁, eA₂, A0, A1⟩ := hA₁.align hA₂ (by simp)
  obtain ⟨W₁, W₂, eW₁, eW₂, W0, W1⟩ := hW₁.align hW₂ (by simp)
  refine (antoine_homotopicIn_retr h₁).trans (HomotopicIn.trans ?_
    (antoine_homotopicIn_retr h₂).symm)
  have hg : Continuous fun z : I × I =>
      ((1 - (z.1 : ℝ)) * (A₁ z.2).im + (z.1 : ℝ) * (A₂ z.2).im,
        (1 - (z.1 : ℝ)) * (W₁ z.2).im + (z.1 : ℝ) * (W₂ z.2).im) := by fun_prop
  have hc := continuous_antoineE.comp hg
  refine ⟨{ toFun := fun z => antoineE ((1 - (z.1 : ℝ)) * (A₁ z.2).im + (z.1 : ℝ) * (A₂ z.2).im)
              ((1 - (z.1 : ℝ)) * (W₁ z.2).im + (z.1 : ℝ) * (W₂ z.2).im)
            continuous_toFun := hc
            map_zero_left := fun t => ?_
            map_one_left := fun t => ?_
            prop' := fun s t ht => ?_ }, fun z => antoineE_mem _ _⟩
  · simp only [Icc.coe_zero, sub_zero, one_mul, zero_mul, add_zero]
    exact (antoineRetrLoop_eq h₁ eA₁ eW₁ t).symm
  · simp only [Icc.coe_one, sub_self, one_mul, zero_mul, zero_add]
    exact (antoineRetrLoop_eq h₂ eA₂ eW₂ t).symm
  · rcases ht with rfl | rfl
    · show antoineE _ _ = antoineRetrLoop δ₁ h₁ 0
      rw [antoineRetrLoop_eq h₁ eA₁ eW₁, ← A0, ← W0]; congr 1 <;> ring
    · show antoineE _ _ = antoineRetrLoop δ₁ h₁ 1
      rw [antoineRetrLoop_eq h₁ eA₁ eW₁, ← A1, ← W1]; congr 1 <;> ring


/-! ### Windings: uniqueness, existence, homotopy invariance, powers -/

theorem AntoineLiftWind.unique {f : I → ℂ} {n m : ℤ} (hn : AntoineLiftWind f n)
    (hm : AntoineLiftWind f m) : n = m := by
  obtain ⟨Γ, h1, e1⟩ := hn
  obtain ⟨Γ', h2, e2⟩ := hm
  have h := expLift_sub_const (Γ := Γ) (Γ' := Γ') (fun t => by rw [h1, h2]) 1
  rw [e2, e1] at h
  have h' : ((m : ℂ) - n) * (2 * Real.pi * Complex.I) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h' with h'' | h''
  · exact_mod_cast (sub_eq_zero.1 h'').symm
  · exact absurd h'' Complex.two_pi_I_ne_zero

theorem antoine_exists_liftWind {f : I → ℂ} (hf : Continuous f) (h0 : ∀ t, f t ≠ 0)
    (h01 : f 1 = f 0) : ∃ n, AntoineLiftWind f n := by
  obtain ⟨Γ, hΓ⟩ := exists_expLift ⟨fun t => (⟨f t, h0 t⟩ : CStar), hf.subtype_mk _⟩
  have e : Complex.exp (Γ 1) = Complex.exp (Γ 0) := by
    have a := hΓ 1; have b := hΓ 0
    simp only [ContinuousMap.coe_mk] at a b
    rw [a, b, h01]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 e
  exact ⟨n, Γ, fun t => hΓ t, hn⟩

/-- The winding of `F` along a loop null-homotopic in a set where `F` is continuous and nonzero
is `0`. -/
theorem antoineLiftWind_of_homotopicIn_refl {X : Type*} [TopologicalSpace X] {O : Set X} {x : X}
    {δ : Path x x} (h : HomotopicIn O δ (Path.refl x)) {F : X → ℂ} (hF : ContinuousOn F O)
    (hF0 : ∀ y ∈ O, F y ≠ 0) : AntoineLiftWind (fun t => F (δ t)) 0 := by
  rw [homotopicIn_iff] at h
  obtain ⟨h1, h2, hom⟩ := h
  let Θ : C(O, CStar) := ⟨fun y => ⟨F y, hF0 y y.2⟩, hF.restrict.subtype_mk _⟩
  have hw := cWinding_homotopic (Path.Homotopic.map hom Θ)
  have e2 : (pathToSub (Path.refl x) h2).map Θ.continuous = Path.refl _ := by ext; rfl
  rw [e2, cWinding_pathRefl] at hw
  have := antoineLiftWind_cWinding ((pathToSub δ h1).map Θ.continuous)
  rw [hw] at this
  exact this

/-- Windings of powers of a loop. -/
theorem antoineLiftWind_loopZPow {X : Type*} [TopologicalSpace X] {S : Set X} {x : X}
    {γ : Path x x} (hγ : ∀ t, γ t ∈ S) {F : X → ℂ} (hF : ContinuousOn F S)
    (hF0 : ∀ y ∈ S, F y ≠ 0) {n : ℤ} (hn : AntoineLiftWind (fun t => F (γ t)) n) (a : ℤ) :
    AntoineLiftWind (fun t => F (loopZPow γ a t)) (a * n) := by
  let Θ : C(S, CStar) := ⟨fun y => ⟨F y, hF0 y y.2⟩, hF.restrict.subtype_mk _⟩
  have hc := antoineLiftWind_cWinding ((pathToSub γ hγ).map Θ.continuous)
  have e := hc.unique hn
  have hγ' := loopZPow_mem hγ a
  have h2 := antoineLiftWind_cWinding ((pathToSub (loopZPow γ a) hγ').map Θ.continuous)
  rw [pathToSub_loopZPow hγ a hγ', loopZPow_map, cWinding_loopZPow, e] at h2
  refine h2.congr fun t => ?_
  rw [← loopZPow_map, ← pathToSub_loopZPow hγ a hγ']
  rfl

/-! ### The meridian in collar coordinates -/

theorem antoineRho_meridian (t : I) :
    antoineRho (antoineMeridian t) = 7 / 8 + 3 / 14 * Real.cos (2 * Real.pi * t) := by
  have hc1 : -1 ≤ Real.cos (2 * Real.pi * t) := Real.neg_one_le_cos _
  have hpos : 0 ≤ 7 / 8 + 3 / 14 * Real.cos (2 * Real.pi * t) := by linarith
  rw [antoineRho, antoineMeridian_apply]
  simp only [abs_zero]
  rw [abs_of_nonneg hpos, max_eq_right hpos]

theorem antoineW_meridian (t : I) :
    antoineW (antoineMeridian t) = (3 / 14 : ℂ) * Complex.exp (2 * Real.pi * Complex.I * t) := by
  rw [antoineW, antoineRho_meridian]
  have : (2 * Real.pi * Complex.I * (t : ℝ)) = ((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_mul_I]
  apply Complex.ext <;> simp [antoineMeridian_apply] <;> ring

theorem antoineMeridian_mem_A0 (t : I) : antoineMeridian t ∈ antoineA0 :=
  ⟨antoineMeridian_mem_nbhd t, antoineMeridian_not_mem t⟩

theorem antoineAng_ne_zero_of_mem {p : ℝ × ℝ × ℝ} (hp : p ∈ antoineNbhd) : antoineAng p ≠ 0 :=
  antoineAng_ne_zero ((antoineRho_gt_of_mem_nbhd hp).trans' (by norm_num))

theorem antoineLiftWind_meridian_W : AntoineLiftWind (fun t => antoineW (antoineMeridian t)) 1 := by
  refine ⟨⟨fun t => Complex.log (3 / 14) + 2 * Real.pi * Complex.I * (t : ℝ), by fun_prop⟩,
    fun t => ?_, ?_⟩
  · show Complex.exp (Complex.log (3 / 14) + _) = antoineW (antoineMeridian t)
    rw [Complex.exp_add, Complex.exp_log (by norm_num), antoineW_meridian]
  · simp only [ContinuousMap.coe_mk, Set.Icc.coe_one, Set.Icc.coe_zero, Complex.ofReal_one,
      Complex.ofReal_zero, mul_one, mul_zero, add_zero, Int.cast_one, one_mul]

theorem antoineLiftWind_meridian_Ang :
    AntoineLiftWind (fun t => antoineAng (antoineMeridian t)) 0 := by
  have hslit : ∀ t, antoineAng (antoineMeridian t) ∈ Complex.slitPlane := fun t => by
    have hc1 : -1 ≤ Real.cos (2 * Real.pi * t) := Real.neg_one_le_cos _
    refine Or.inr ?_
    simp only [antoineAng, antoineMeridian_apply, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add]
    linarith
  have hc : Continuous fun t => antoineAng (antoineMeridian t) :=
    continuous_antoineAng.comp antoineMeridian.continuous
  refine ⟨⟨fun t => Complex.log (antoineAng (antoineMeridian t)),
    continuous_iff_continuousAt.2 fun t => (hc.continuousAt).clog (hslit t)⟩,
    fun t => Complex.exp_log (antoineAng_ne_zero_of_mem (antoineMeridian_mem_nbhd t)), ?_⟩
  simp only [ContinuousMap.coe_mk, Path.source, Path.target, Int.cast_zero, zero_mul, add_zero]

/-! ### Pulling a collar loop of `S³` back to `ℝ³` -/

/-- The chart of the `j`-th tube, `(stereo ∘ g_j)⁻¹`. -/
def antoineChart (j : Fin 64) (y : Sphere3) : ℝ × ℝ × ℝ := antoineMapInv j (antoineStereoInv y)

theorem antoineChart_of_mem {j : Fin 64} {O : Set (ℝ × ℝ × ℝ)} {y : Sphere3}
    (hy : y ∈ antoineStereo '' (antoineMap j '' O)) :
    antoineChart j y ∈ O ∧ antoineStereo (antoineMap j (antoineChart j y)) = y := by
  obtain ⟨_, ⟨q, hq, rfl⟩, rfl⟩ := hy
  simp only [antoineChart, antoineStereoInv_stereo, antoineMapInv_map]
  exact ⟨hq, trivial⟩

theorem continuousOn_antoineChart (j : Fin 64) (O : Set (ℝ × ℝ × ℝ)) :
    ContinuousOn (antoineChart j) (antoineStereo '' (antoineMap j '' O)) := by
  rintro _ ⟨q, -, rfl⟩
  exact ((continuous_antoineMapInv j).continuousAt.comp
    (continuousAt_antoineStereoInv (antoineStereo_three_lt q))).continuousWithinAt

/-- The pulled-back loop. -/
def antoinePull (j : Fin 64) (δ : Path (antoineX1 j) (antoineX1 j))
    (hδ : ∀ t, δ t ∈ antoineA1 j) : Path antoineMerPt antoineMerPt where
  toFun t := antoineChart j (δ t)
  continuous_toFun := by
    have h : ∀ t, δ t ∈ antoineStereo '' (antoineMap j '' antoineA0) := fun t => by
      rw [image_image]; exact (antoineA1_eq j) ▸ hδ t
    exact (continuousOn_antoineChart j antoineA0).comp_continuous δ.continuous h
  source' := by
    show antoineChart j (δ 0) = _
    rw [δ.source]; simp [antoineChart, antoineX1, antoineStereoInv_stereo, antoineMapInv_map]
  target' := by
    show antoineChart j (δ 1) = _
    rw [δ.target]; simp [antoineChart, antoineX1, antoineStereoInv_stereo, antoineMapInv_map]

theorem antoinePull_spec (j : Fin 64) (δ : Path (antoineX1 j) (antoineX1 j))
    (hδ : ∀ t, δ t ∈ antoineA1 j) (t : I) :
    antoinePull j δ hδ t ∈ antoineA0 ∧
      antoineStereo (antoineMap j (antoinePull j δ hδ t)) = δ t := by
  have h : δ t ∈ antoineStereo '' (antoineMap j '' antoineA0) := by
    rw [image_image]; exact (antoineA1_eq j) ▸ hδ t
  exact antoineChart_of_mem h

theorem antoineMu1_eq (j : Fin 64) :
    antoineMeridian.map (continuous_antoineStereo.comp (continuous_antoineMap j)) = antoineMu1 j := by
  rfl

/-- `collar_mer` of `GX.AntoineFirstGeneration`: a loop of the collar `Aⱼ` which is
null-homotopic in the tube `Nⱼ` is, in `Aⱼ`, a power of the meridian. -/
theorem antoine_collar_mer (j : Fin 64) (O : Set Sphere3) (hO : O ⊆ antoineN1 j)
    (δ : Path (antoineX1 j) (antoineX1 j)) (hδ : ∀ t, δ t ∈ antoineA1 j)
    (hnull : HomotopicIn O δ (Path.refl _)) :
    ∃ a : ℤ, HomotopicIn (antoineA1 j) δ (loopZPow (antoineMu1 j) a) := by
  set δ' := antoinePull j δ hδ
  have hδ' : ∀ t, δ' t ∈ antoineA0 := fun t => (antoinePull_spec j δ hδ t).1
  -- the longitudinal winding vanishes: `δ` is null in the tube
  have hA : AntoineLiftWind (fun t => antoineAng (δ' t)) 0 := by
    refine antoineLiftWind_of_homotopicIn_refl hnull (F := fun y => antoineAng (antoineChart j y))
      ?_ ?_
    · exact (continuous_antoineAng.comp_continuousOn
        (continuousOn_antoineChart j antoineNbhd)).mono hO
    · intro y hy
      exact antoineAng_ne_zero_of_mem (antoineChart_of_mem (hO hy)).1
  obtain ⟨b, hW⟩ := antoine_exists_liftWind (f := fun t => antoineW (δ' t))
    (continuous_antoineW.comp δ'.continuous) (fun t => antoineW_ne_zero (hδ' t))
    (by simp only [Path.source, Path.target])
  have hμ := antoineMeridian_mem_A0
  have hμA := antoineLiftWind_loopZPow hμ continuous_antoineAng.continuousOn
    (fun y hy => antoineAng_ne_zero_of_mem hy.1) antoineLiftWind_meridian_Ang b
  have hμW := antoineLiftWind_loopZPow hμ continuous_antoineW.continuousOn
    (fun y hy => antoineW_ne_zero hy) antoineLiftWind_meridian_W b
  rw [mul_zero] at hμA
  rw [mul_one] at hμW
  have hcl := antoine_collar_classify hδ' (loopZPow_mem hμ b) hA hμA hW hμW
  refine ⟨b, ?_⟩
  have hg := continuous_antoineStereo.comp (continuous_antoineMap j)
  have hmap := hcl.map hg (V := antoineA1 j) (fun q hq => by rw [antoineA1_eq]; exact ⟨q, hq, rfl⟩)
  refine hmap.of_eq ?_ ?_
  · exact Path.ext (funext fun t => (antoinePull_spec j δ hδ t).2)
  · rw [loopZPow_map, antoineMu1_eq]; rfl


/-! ### Windings under free homotopies -/

/-- **Free homotopy invariance** of the winding: a continuous family of loops of `ℂ ∖ 0` (the base
point may move) has constant winding (homotopy lifting through `exp`). -/
theorem AntoineLiftWind.of_freeHomotopy {G : I × I → ℂ} (hG : Continuous G)
    (hG0 : ∀ z, G z ≠ 0) (hloop : ∀ s, G (s, 1) = G (s, 0)) {n : ℤ}
    (h : AntoineLiftWind (fun t => G (0, t)) n) : AntoineLiftWind (fun t => G (1, t)) n := by
  obtain ⟨Γ, hΓ, e⟩ := h
  let H : C(I × I, CStar) := ⟨fun z => ⟨G z, hG0 z⟩, hG.subtype_mk _⟩
  have H_0 : ∀ a, H (0, a) = cExp (Γ a) := fun a => Subtype.ext (by
    show G (0, a) = Complex.exp (Γ a); rw [hΓ a])
  set Λ := isCoveringMap_cExp.liftHomotopy H Γ H_0
  have hΛ : ∀ z, Complex.exp (Λ z) = G z := fun z =>
    congrArg Subtype.val (congrFun (isCoveringMap_cExp.liftHomotopy_lifts H Γ H_0) z)
  have hΛ0 : ∀ a, Λ (0, a) = Γ a := isCoveringMap_cExp.liftHomotopy_zero H Γ H_0
  have hd : (fun s : I => Λ (s, 1) - Λ (s, 0)) = fun _ => Λ (0, 1) - Λ (0, 0) := by
    refine isCoveringMap_cExp.eq_of_comp_eq (by fun_prop) continuous_const ?_ 0 rfl
    funext s
    refine Subtype.ext ?_
    simp only [comp_apply, cExp_apply, Complex.exp_sub, hΛ, hloop]
    rw [div_self (hG0 _), div_self (hG0 _)]
  refine ⟨⟨fun t => Λ (1, t), by fun_prop⟩, fun t => hΛ _, ?_⟩
  have := congrFun hd 1
  simp only [ContinuousMap.coe_mk]
  rw [hΛ0, hΛ0, e] at this
  linear_combination this

/-- Straight-line version: two loops of `ℂ` whose joining segments avoid `0` have equal
windings. -/
theorem AntoineLiftWind.of_segment {f g : I → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hf1 : f 1 = f 0) (hg1 : g 1 = g 0)
    (hne : ∀ t : I, ∀ s : ℝ, 0 ≤ s → s ≤ 1 → (1 - s) * f t + s * g t ≠ 0) {n : ℤ}
    (h : AntoineLiftWind f n) : AntoineLiftWind g n := by
  have := AntoineLiftWind.of_freeHomotopy (G := fun z : I × I => (1 - ((z.1 : ℝ) : ℂ)) * f z.2 +
      ((z.1 : ℝ) : ℂ) * g z.2) (by fun_prop)
    (fun z => by
      exact hne z.2 z.1 z.1.2.1 z.1.2.2)
    (fun s => by simp only [hf1, hg1]) (h.congr fun t => by simp)
  exact this.congr fun t => by simp

/-- Homotopy invariance of windings along a homotopy in a set where `F` is continuous and
nonzero. -/
theorem AntoineLiftWind.of_homotopicIn {X : Type*} [TopologicalSpace X] {O : Set X} {x : X}
    {γ γ' : Path x x} (h : HomotopicIn O γ γ') {F : X → ℂ} (hF : ContinuousOn F O)
    (hF0 : ∀ y ∈ O, F y ≠ 0) {n : ℤ} (hn : AntoineLiftWind (fun t => F (γ t)) n) :
    AntoineLiftWind (fun t => F (γ' t)) n := by
  rw [homotopicIn_iff] at h
  obtain ⟨h1, h2, hom⟩ := h
  let Θ : C(O, CStar) := ⟨fun y => ⟨F y, hF0 y y.2⟩, hF.restrict.subtype_mk _⟩
  have hw := cWinding_homotopic (Path.Homotopic.map hom Θ)
  have e1 := (antoineLiftWind_cWinding ((pathToSub γ h1).map Θ.continuous)).unique hn
  have := antoineLiftWind_cWinding ((pathToSub γ' h2).map Θ.continuous)
  rw [← hw, e1] at this
  exact this

/-! ### `Ψ` and `W` agree near the link -/

theorem antoinePsi_eq_W {p : ℝ × ℝ × ℝ} (hp : antoineSq p ≤ 2) : antoinePsi p = antoineW p := by
  have hρ0 := antoineRho_nonneg p
  have hS : antoineSq p = antoineRho p ^ 2 + p.2.2 ^ 2 := rfl
  have hρ2 : antoineRho p < 2 := by nlinarith [sq_nonneg p.2.2]
  have e1 : min 2 (max |p.1| |p.2.1| + max 0 (antoineSq p - 2)) = antoineRho p := by
    rw [max_eq_left (show antoineSq p - 2 ≤ 0 by linarith), add_zero]
    exact min_eq_right hρ2.le
  have e2 : max 0 (min 1 (3 - antoineSq p)) = 1 := by
    rw [min_eq_left (by linarith), max_eq_right zero_le_one]
  rw [antoinePsi, e1, e2, mul_one, antoineW]

/-- Where `z² ≤ 6/5`, the segment from `Ψ p` to `W p` avoids `0` when `W p ≠ 0`. -/
theorem antoine_segment_Psi_W {p : ℝ × ℝ × ℝ} (hz : p.2.2 ^ 2 ≤ 6 / 5) (hW : antoineW p ≠ 0)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : (1 - s) * antoinePsi p + s * antoineW p ≠ 0 := by
  rcases le_or_gt (antoineSq p) 2 with h | h
  · rw [antoinePsi_eq_W h]
    have : (1 - (s : ℂ)) * antoineW p + s * antoineW p = antoineW p := by ring
    rw [this]; exact hW
  · -- both real parts are positive
    have hS : antoineSq p = antoineRho p ^ 2 + p.2.2 ^ 2 := rfl
    have hρ0 := antoineRho_nonneg p
    have hρ : 7 / 8 < antoineRho p := by nlinarith
    intro h0
    have hre := congrArg Complex.re h0
    have hPre : (antoinePsi p).re =
        min 2 (max |p.1| |p.2.1| + max 0 (antoineSq p - 2)) - 7 / 8 := by simp [antoinePsi]
    have h1 : 0 < (antoinePsi p).re := by
      have : antoineRho p ≤ max |p.1| |p.2.1| + max 0 (antoineSq p - 2) :=
        le_add_of_nonneg_right (le_max_left _ _)
      have h2 : 7 / 8 < min 2 (max |p.1| |p.2.1| + max 0 (antoineSq p - 2)) :=
        lt_min (by norm_num) (by linarith)
      linarith
    have h2 : (antoineW p).re = antoineRho p - 7 / 8 := by simp [antoineW]
    simp only [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.sub_im, Complex.one_im, zero_mul, sub_zero, Complex.zero_re] at hre
    rw [h2] at hre
    have hb : 0 < antoineRho p - 7 / 8 := by linarith
    have hm : 0 < min (antoinePsi p).re (antoineRho p - 7 / 8) := lt_min h1 hb
    have e1 : (1 - s) * min (antoinePsi p).re (antoineRho p - 7 / 8) ≤ (1 - s) * (antoinePsi p).re :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) (by linarith)
    have e2 : s * min (antoinePsi p).re (antoineRho p - 7 / 8) ≤ s * (antoineRho p - 7 / 8) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) hs0
    linarith


/-! ### A longitude of the collar -/

/-- The angle `π/2 - 2πt` of the longitude. -/
def antoineLonAngle (t : I) : ℝ := Real.pi / 2 - 2 * Real.pi * t

theorem antoineM_lonAngle_one : antoineM (antoineLonAngle 1) = antoineM (antoineLonAngle 0) := by
  simp only [antoineM, antoineLonAngle, Icc.coe_one, Icc.coe_zero, mul_one, mul_zero, sub_zero,
    Real.cos_sub_two_pi, Real.sin_sub_two_pi]

theorem continuous_antoineLonAngle : Continuous antoineLonAngle := by
  unfold antoineLonAngle; fun_prop

theorem continuous_antoineE_comp {X : Type*} [TopologicalSpace X] {f g : X → ℝ}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun x => antoineE (f x) (g x) := by
  have h := continuous_antoineE.comp (hf.prodMk hg)
  exact h

theorem antoineE_pi_div_two : antoineE (Real.pi / 2) 0 = antoineMerPt := by
  have hM : antoineM (Real.pi / 2) = 1 := by
    rw [antoineM, Real.cos_pi_div_two, Real.sin_pi_div_two, abs_zero, abs_one]
    exact max_eq_right zero_le_one
  rw [antoineE, hM, Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_zero, Real.sin_zero,
    antoineMerPt]
  simp only [div_one, mul_zero, mul_one]

theorem antoineLonAngle_zero : antoineLonAngle 0 = Real.pi / 2 := by
  simp [antoineLonAngle]

theorem antoineE_lonAngle_one (β : ℝ) : antoineE (antoineLonAngle 1) β = antoineE (Real.pi / 2) β := by
  have e : antoineLonAngle 1 = Real.pi / 2 - 2 * Real.pi := by simp [antoineLonAngle]
  simp only [antoineE, antoineM, e, Real.cos_sub_two_pi, Real.sin_sub_two_pi]

/-- The longitude `t ↦ antoineE (π/2 - 2πt) 0` of the collar, based at the meridian's base point
(Ang-winding `-1`, W-winding `0`). -/
def antoineLon : Path antoineMerPt antoineMerPt where
  toFun t := antoineE (antoineLonAngle t) 0
  continuous_toFun := continuous_antoineE_comp continuous_antoineLonAngle continuous_const
  source' := by rw [antoineLonAngle_zero, antoineE_pi_div_two]
  target' := by rw [antoineE_lonAngle_one, antoineE_pi_div_two]

theorem antoineLon_apply (t : I) : antoineLon t =
    ((7 / 8 + 3 / 14) / antoineM (antoineLonAngle t) * Real.cos (antoineLonAngle t),
      (7 / 8 + 3 / 14) / antoineM (antoineLonAngle t) * Real.sin (antoineLonAngle t), 0) := by
  show antoineE _ 0 = _
  simp only [antoineE, Real.cos_zero, Real.sin_zero, mul_one, mul_zero]

theorem antoineLon_mem (t : I) : antoineLon t ∈ antoineA0 := antoineE_mem _ _

theorem antoine_cM_pos (t : I) : 0 < (7 / 8 + 3 / 14 : ℝ) / antoineM (antoineLonAngle t) :=
  div_pos (by norm_num) (antoineM_pos _)

theorem antoine_cM_ge (t : I) : (7 / 8 + 3 / 14 : ℝ) ≤ (7 / 8 + 3 / 14) / antoineM (antoineLonAngle t) := by
  have hm := antoineM_pos (antoineLonAngle t)
  have hm1 : antoineM (antoineLonAngle t) ≤ 1 :=
    max_le (Real.abs_cos_le_one _) (Real.abs_sin_le_one _)
  rw [le_div_iff₀ hm]; nlinarith

theorem continuous_antoine_cM : Continuous fun t : I =>
    (7 / 8 + 3 / 14 : ℝ) / antoineM (antoineLonAngle t) :=
  continuous_const.div (continuous_antoineM.comp continuous_antoineLonAngle)
    fun _ => (antoineM_pos _).ne'

theorem antoineLiftWind_lon_Ang : AntoineLiftWind (fun t => antoineAng (antoineLon t)) (-1) := by
  have hc := continuous_antoine_cM
  refine ⟨⟨fun t => (Real.log ((7 / 8 + 3 / 14 : ℝ) / antoineM (antoineLonAngle t)) : ℂ) +
      (antoineLonAngle t : ℂ) * Complex.I, ?_⟩, fun t => ?_, ?_⟩
  · have := hc.log fun t => (antoine_cM_pos t).ne'
    have := continuous_antoineLonAngle
    fun_prop
  · show Complex.exp (_ + _) = antoineAng (antoineLon t)
    rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log (antoine_cM_pos t), Complex.exp_mul_I,
      antoineLon_apply, antoineAng]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast; ring
  · simp only [ContinuousMap.coe_mk]
    rw [antoineM_lonAngle_one]
    simp only [antoineLonAngle, Icc.coe_one, Icc.coe_zero, mul_one, mul_zero, sub_zero]
    push_cast; ring

theorem antoineLiftWind_lon_W : AntoineLiftWind (fun t => antoineW (antoineLon t)) 0 := by
  refine ⟨ContinuousMap.const _ (Complex.log (3 / 14)), fun t => ?_, by simp⟩
  show Complex.exp (Complex.log (3 / 14)) = antoineW (antoineE _ 0)
  rw [Complex.exp_log (by norm_num), antoineW_E]; simp


/-! ### The longitude of a link links its successor once -/

/-- The radius factor `c / M(α)` of the longitude. -/
def antoineCM (t : I) : ℝ := (7 / 8 + 3 / 14 : ℝ) / antoineM (antoineLonAngle t)

theorem antoineCM_one : antoineCM 1 = antoineCM 0 := by rw [antoineCM, antoineCM, antoineM_lonAngle_one]

theorem antoineCM_pos (t : I) : 0 < antoineCM t := antoine_cM_pos t

theorem antoineCM_ge (t : I) : (7 / 8 + 3 / 14 : ℝ) ≤ antoineCM t := antoine_cM_ge t

theorem antoineCM_abs_cos_le (t : I) : |antoineCM t * Real.cos (antoineLonAngle t)| ≤ 7 / 8 + 3 / 14 := by
  have hm := antoineM_pos (antoineLonAngle t)
  have h : |Real.cos (antoineLonAngle t)| ≤ antoineM (antoineLonAngle t) := le_max_left _ _
  rw [abs_mul, abs_of_pos (antoineCM_pos t), antoineCM, div_mul_eq_mul_div, div_le_iff₀ hm]
  nlinarith

theorem antoineCM_abs_sin_le (t : I) : |antoineCM t * Real.sin (antoineLonAngle t)| ≤ 7 / 8 + 3 / 14 := by
  have hm := antoineM_pos (antoineLonAngle t)
  have h : |Real.sin (antoineLonAngle t)| ≤ antoineM (antoineLonAngle t) := le_max_right _ _
  rw [abs_mul, abs_of_pos (antoineCM_pos t), antoineCM, div_mul_eq_mul_div, div_le_iff₀ hm]
  nlinarith

/-- The winding of `Ψ` along the image of the longitude under an affine chart change `T`, from the
explicit form `W(T(λ t)) - 3/8 = (c/M) κ e^{i ε α}`. -/
theorem antoine_lon_psi_wind {T : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ} (hT : Continuous T) {κ : ℂ} {θ : ℝ}
    (hκ : Complex.exp ((θ : ℂ) * Complex.I) = κ) {ε : ℤ}
    (hW : ∀ t, antoineW (T (antoineLon t)) - 3 / 8 =
      ((antoineCM t : ℝ) : ℂ) * κ * Complex.exp ((((ε : ℝ) * antoineLonAngle t : ℝ) : ℂ) * Complex.I))
    (hz : ∀ t, (T (antoineLon t)).2.2 ^ 2 ≤ 6 / 5) :
    AntoineLiftWind (fun t => antoinePsi (T (antoineLon t))) (-ε) := by
  have hκ1 : ‖κ‖ = 1 := by rw [← hκ, Complex.norm_exp_ofReal_mul_I]
  have hZn : ∀ t, ‖antoineW (T (antoineLon t)) - 3 / 8‖ = antoineCM t := fun t => by
    rw [hW, norm_mul, norm_mul, hκ1, Complex.norm_exp_ofReal_mul_I, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (antoineCM_pos t)]; ring
  have hCM := antoineCM_ge
  have hc : Continuous fun t => antoineW (T (antoineLon t)) :=
    continuous_antoineW.comp (hT.comp antoineLon.continuous)
  have hcP : Continuous fun t => antoinePsi (T (antoineLon t)) :=
    continuous_antoinePsi.comp (hT.comp antoineLon.continuous)
  have hloop : ∀ {f : ℝ × ℝ × ℝ → ℂ}, f (T (antoineLon 1)) = f (T (antoineLon 0)) := by
    intro f; simp only [Path.source, Path.target]
  -- (A) the explicit lift
  have hA : AntoineLiftWind (fun t => antoineW (T (antoineLon t)) - 3 / 8) (-ε) := by
    have hl := (continuous_antoine_cM.log fun t => (antoine_cM_pos t).ne')
    refine ⟨⟨fun t => (Real.log (antoineCM t) : ℂ) + (θ : ℂ) * Complex.I +
        (((ε : ℝ) * antoineLonAngle t : ℝ) : ℂ) * Complex.I, ?_⟩, fun t => ?_, ?_⟩
    · have := continuous_antoineLonAngle
      unfold antoineCM
      fun_prop
    · show Complex.exp (_ + _ + _) = antoineW (T (antoineLon t)) - 3 / 8
      rw [hW, Complex.exp_add, Complex.exp_add, ← Complex.ofReal_exp,
        Real.exp_log (antoineCM_pos t), hκ]
    · simp only [ContinuousMap.coe_mk]
      rw [antoineCM_one]
      simp only [antoineLonAngle, Icc.coe_one, Icc.coe_zero, mul_one, mul_zero, sub_zero]
      push_cast; ring
  -- (B) add back `3/8`
  have hB : AntoineLiftWind (fun t => antoineW (T (antoineLon t))) (-ε) := by
    refine (AntoineLiftWind.of_segment (hc.sub continuous_const) hc (hloop (f := fun q => antoineW q - 3 / 8))
      hloop ?_ hA)
    intro t s hs0 hs1 h0
    have e : (1 - (s : ℂ)) * (antoineW (T (antoineLon t)) - 3 / 8) + s * antoineW (T (antoineLon t)) =
        (antoineW (T (antoineLon t)) - 3 / 8) + (s * (3 / 8) : ℝ) := by push_cast; ring
    rw [e] at h0
    have h1 := congrArg norm h0
    rw [norm_zero] at h1
    have h2 := norm_add_le (antoineW (T (antoineLon t)) - 3 / 8 + ((s * (3 / 8) : ℝ) : ℂ))
      (-((s * (3 / 8) : ℝ) : ℂ))
    rw [add_neg_cancel_right, h1, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), hZn] at h2
    have := hCM t
    nlinarith
  -- (C) `Ψ` against `W`
  refine AntoineLiftWind.of_segment hc hcP hloop hloop ?_ hB
  intro t s hs0 hs1
  have hWne : antoineW (T (antoineLon t)) ≠ 0 := by
    intro h0
    have := hZn t
    rw [h0, zero_sub, norm_neg] at this
    have := hCM t
    norm_num at *; linarith
  have := antoine_segment_Psi_W (hz t) hWne (s := 1 - s) (by linarith) (by linarith)
  have e : (1 - ((1 - s : ℝ) : ℂ)) * antoinePsi (T (antoineLon t)) +
      ((1 - s : ℝ) : ℂ) * antoineW (T (antoineLon t)) =
      (1 - (s : ℂ)) * antoineW (T (antoineLon t)) + s * antoinePsi (T (antoineLon t)) := by
    push_cast; ring
  rw [e] at this
  exact this

/-- The two shapes of the chart change between consecutive links. -/
def antoineTX (sg : ℝ) (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ := (p.1 - sg * (5 / 4), p.2.2, p.2.1)

def antoineTY (sg : ℝ) (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ := (p.2.2, p.2.1 - sg * (5 / 4), p.1)

theorem continuous_antoineTX (sg : ℝ) : Continuous (antoineTX sg) := by unfold antoineTX; fun_prop
theorem continuous_antoineTY (sg : ℝ) : Continuous (antoineTY sg) := by unfold antoineTY; fun_prop

theorem antoineLon_coords (t : I) : antoineLon t =
    (antoineCM t * Real.cos (antoineLonAngle t), antoineCM t * Real.sin (antoineLonAngle t), 0) := by
  rw [antoineLon_apply]; rfl

theorem antoine_lon_wind_TX (sg : ℝ) (hsg : sg = 1 ∨ sg = -1) : ∃ w : ℤ, w ≠ 0 ∧
    AntoineLiftWind (fun t => antoinePsi (antoineTX sg (antoineLon t))) w := by
  have hb := antoineCM_abs_cos_le
  have hs := antoineCM_abs_sin_le
  have hz : ∀ t, (antoineTX sg (antoineLon t)).2.2 ^ 2 ≤ 6 / 5 := fun t => by
    rw [antoineLon_coords]
    show (antoineCM t * Real.sin (antoineLonAngle t)) ^ 2 ≤ 6 / 5
    have := hs t
    rw [← sq_abs]; nlinarith [abs_nonneg (antoineCM t * Real.sin (antoineLonAngle t))]
  rcases hsg with rfl | rfl
  · refine ⟨1, one_ne_zero, ?_⟩
    have := antoine_lon_psi_wind (continuous_antoineTX 1) (θ := Real.pi) (κ := -1)
      (by rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi,
        Real.sin_pi]; simp) (ε := -1) (fun t => ?_) hz
    · simpa using this
    · rw [antoineLon_coords]
      have hb' := hb t
      rw [abs_le] at hb'
      have hρ : antoineRho (antoineTX 1 (antoineCM t * Real.cos (antoineLonAngle t),
          antoineCM t * Real.sin (antoineLonAngle t), 0)) =
          5 / 4 - antoineCM t * Real.cos (antoineLonAngle t) := by
        simp only [antoineRho, antoineTX, abs_zero, one_mul]
        rw [abs_of_neg (by linarith), max_eq_left (by linarith)]; ring
      rw [antoineW, hρ, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      apply Complex.ext
      · simp [antoineTX, Real.cos_neg, Real.sin_neg]; ring
      · simp [antoineTX, Real.cos_neg, Real.sin_neg]
  · refine ⟨-1, by norm_num, ?_⟩
    have := antoine_lon_psi_wind (continuous_antoineTX (-1)) (θ := 0) (κ := 1)
      (by simp) (ε := 1) (fun t => ?_) hz
    · simpa using this
    · rw [antoineLon_coords]
      have hb' := hb t
      rw [abs_le] at hb'
      have hρ : antoineRho (antoineTX (-1) (antoineCM t * Real.cos (antoineLonAngle t),
          antoineCM t * Real.sin (antoineLonAngle t), 0)) =
          antoineCM t * Real.cos (antoineLonAngle t) + 5 / 4 := by
        simp only [antoineRho, antoineTX, abs_zero]
        rw [abs_of_pos (by linarith), max_eq_left (by linarith)]; ring
      rw [antoineW, hρ, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      apply Complex.ext
      · simp [antoineTX]; ring
      · simp [antoineTX]

theorem antoine_lon_wind_TY (sg : ℝ) (hsg : sg = 1 ∨ sg = -1) : ∃ w : ℤ, w ≠ 0 ∧
    AntoineLiftWind (fun t => antoinePsi (antoineTY sg (antoineLon t))) w := by
  have hb := antoineCM_abs_cos_le
  have hs := antoineCM_abs_sin_le
  have hz : ∀ t, (antoineTY sg (antoineLon t)).2.2 ^ 2 ≤ 6 / 5 := fun t => by
    rw [antoineLon_coords]
    show (antoineCM t * Real.cos (antoineLonAngle t)) ^ 2 ≤ 6 / 5
    have := hb t
    rw [← sq_abs]; nlinarith [abs_nonneg (antoineCM t * Real.cos (antoineLonAngle t))]
  rcases hsg with rfl | rfl
  · refine ⟨-1, by norm_num, ?_⟩
    have := antoine_lon_psi_wind (continuous_antoineTY 1) (θ := Real.pi / 2) (κ := Complex.I)
      (by rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two,
        Real.sin_pi_div_two]; simp) (ε := 1) (fun t => ?_) hz
    · simpa using this
    · rw [antoineLon_coords]
      have hs' := hs t
      rw [abs_le] at hs'
      have hρ : antoineRho (antoineTY 1 (antoineCM t * Real.cos (antoineLonAngle t),
          antoineCM t * Real.sin (antoineLonAngle t), 0)) =
          5 / 4 - antoineCM t * Real.sin (antoineLonAngle t) := by
        simp only [antoineRho, antoineTY, abs_zero, one_mul]
        rw [abs_of_neg (by linarith), max_eq_right (by linarith)]; ring
      rw [antoineW, hρ, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      apply Complex.ext
      · simp [antoineTY]; ring
      · simp [antoineTY]
  · refine ⟨1, one_ne_zero, ?_⟩
    have := antoine_lon_psi_wind (continuous_antoineTY (-1)) (θ := Real.pi / 2) (κ := Complex.I)
      (by rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two,
        Real.sin_pi_div_two]; simp) (ε := -1) (fun t => ?_) hz
    · simpa using this
    · rw [antoineLon_coords]
      have hs' := hs t
      rw [abs_le] at hs'
      have hρ : antoineRho (antoineTY (-1) (antoineCM t * Real.cos (antoineLonAngle t),
          antoineCM t * Real.sin (antoineLonAngle t), 0)) =
          antoineCM t * Real.sin (antoineLonAngle t) + 5 / 4 := by
        simp only [antoineRho, antoineTY, abs_zero]
        rw [abs_of_pos (by linarith), max_eq_right (by linarith)]; ring
      rw [antoineW, hρ, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      apply Complex.ext
      · simp [antoineTY, Real.cos_neg, Real.sin_neg]; ring
      · simp [antoineTY, Real.cos_neg, Real.sin_neg]


/-- The chart change from the `j`-th link to the `(j+1)`-st is one of the four shapes. -/
theorem antoine_succ_form (j : Fin 64) :
    (∃ sg : ℝ, (sg = 1 ∨ sg = -1) ∧ ∀ p, antoineMapInv (j + 1) (antoineMap j p) = antoineTX sg p) ∨
    (∃ sg : ℝ, (sg = 1 ∨ sg = -1) ∧ ∀ p, antoineMapInv (j + 1) (antoineMap j p) = antoineTY sg p) := by
  rcases antoine_adj_succ j with ⟨hy, hx, ht⟩ | ⟨hx, hy, ht⟩
  · left
    have hy' : ((antoineZ j).2 : ℝ) = (antoineZ (j + 1)).2 := by exact_mod_cast hy
    refine ⟨(((antoineZ (j + 1)).1 : ℝ) - (antoineZ j).1) / 70, ?_, fun p => ?_⟩
    · rcases (abs_eq (by norm_num : (0 : ℤ) ≤ 70)).1 hx with h | h
      · right; have : ((antoineZ j).1 : ℝ) - (antoineZ (j + 1)).1 = 70 := by exact_mod_cast h
        linarith [show (((antoineZ (j + 1)).1 : ℝ) - (antoineZ j).1) / 70 = -1 by
          rw [div_eq_iff (by norm_num)]; linarith]
      · left; have : ((antoineZ j).1 : ℝ) - (antoineZ (j + 1)).1 = -70 := by exact_mod_cast h
        rw [div_eq_iff (by norm_num)]; linarith
    · rcases ht with ⟨ti, tj⟩ | ⟨ti, tj⟩ <;>
        simp only [antoineMapInv, antoineMap, ti, tj, antoinePerm, antoineTX, Prod.mk.injEq] <;>
        refine ⟨?_, ?_, ?_⟩ <;> first | ring1 | (rw [hy']; ring1)
  · right
    have hx' : ((antoineZ j).1 : ℝ) = (antoineZ (j + 1)).1 := by exact_mod_cast hx
    refine ⟨(((antoineZ (j + 1)).2 : ℝ) - (antoineZ j).2) / 70, ?_, fun p => ?_⟩
    · rcases (abs_eq (by norm_num : (0 : ℤ) ≤ 70)).1 hy with h | h
      · right; have : ((antoineZ j).2 : ℝ) - (antoineZ (j + 1)).2 = 70 := by exact_mod_cast h
        rw [div_eq_iff (by norm_num)]; linarith
      · left; have : ((antoineZ j).2 : ℝ) - (antoineZ (j + 1)).2 = -70 := by exact_mod_cast h
        rw [div_eq_iff (by norm_num)]; linarith
    · rcases ht with ⟨ti, tj⟩ | ⟨ti, tj⟩ <;>
        simp only [antoineMapInv, antoineMap, ti, tj, antoinePerm, antoineTY, Prod.mk.injEq] <;>
        refine ⟨?_, ?_, ?_⟩ <;> first | ring1 | (rw [hx']; ring1)

/-- The longitude of the `j`-th link has nonzero winding with respect to the `(j+1)`-st. -/
theorem antoine_succ_wind (j : Fin 64) : ∃ w : ℤ, w ≠ 0 ∧
    AntoineLiftWind (fun t => antoinePsi (antoineMapInv (j + 1) (antoineMap j (antoineLon t)))) w := by
  rcases antoine_succ_form j with ⟨sg, hsg, hT⟩ | ⟨sg, hsg, hT⟩
  · obtain ⟨w, hw, h⟩ := antoine_lon_wind_TX sg hsg
    exact ⟨w, hw, h.congr fun t => by rw [hT]⟩
  · obtain ⟨w, hw, h⟩ := antoine_lon_wind_TY sg hsg
    exact ⟨w, hw, h.congr fun t => by rw [hT]⟩

theorem antoineTheta_one_stereo (i : Fin 64) (q : ℝ × ℝ × ℝ) :
    antoineTheta (fun _ => i) 1 (antoineStereo q) = antoinePsi (antoineMapInv i q) := by
  rw [antoineTheta, if_pos (antoineStereo_three_lt _), antoineStereoInv_stereo]; rfl

theorem antoineTheta_ne_zero_of_compl {i : Fin 64} {y : Sphere3}
    (hy : y ∈ (antoineStereo '' antoineStage 1)ᶜ) : antoineTheta (fun _ => i) 1 y ≠ 0 := by
  refine antoineTheta_ne_zero _ _ fun h => hy ?_
  obtain ⟨q, hq, rfl⟩ := h
  refine ⟨q, ?_, rfl⟩
  rw [antoineStage_one_eq]
  exact mem_iUnion.2 ⟨i, hq⟩

/-- Points of the collar `Aⱼ` are off the first stage. -/
theorem antoineA1_subset_compl (j : Fin 64) : antoineA1 j ⊆ (antoineStereo '' antoineStage 1)ᶜ := by
  rintro y ⟨hyN, hyL⟩ ⟨q, hq, rfl⟩
  rw [antoineStage_one_eq] at hq
  obtain ⟨i, hi⟩ := mem_iUnion.1 hq
  by_cases e : i = j
  · exact hyL (e ▸ ⟨q, hi, rfl⟩)
  · obtain ⟨p, hp, hpq⟩ := hyN
    have := antoineStereo_injective hpq
    exact Set.disjoint_left.1 (antoineTube_disjoint i j e) (this ▸ hp) hi

theorem antoineSq_lt_of_mem_nbhd {p : ℝ × ℝ × ℝ} (hp : p ∈ antoineNbhd) : antoineSq p ≤ 2 := by
  obtain ⟨hx, hy, hz⟩ := antoineNbhd_bounds hp
  have hρ : max |p.1| |p.2.1| < 9 / 8 := max_lt hx hy
  have hρ0 : 0 ≤ max |p.1| |p.2.1| := (abs_nonneg _).trans (le_max_left _ _)
  have hz2 : p.2.2 ^ 2 < 1 / 16 := by
    rw [← sq_abs]; nlinarith [abs_nonneg p.2.2]
  show (max |p.1| |p.2.1|) ^ 2 + p.2.2 ^ 2 ≤ 2
  nlinarith

/-- `collar_inj` of `GX.AntoineFirstGeneration`: a loop of the collar `Aⱼ` null-homotopic in
`S³ ∖ C₁` is null-homotopic in `Aⱼ`. Its meridional winding is read by `Θⱼ`, its longitudinal
winding by `Θⱼ₊₁` (the longitude of `Lⱼ` links `Lⱼ₊₁` once, `GX.antoine_succ_wind`), and the
collar is classified by the two windings (`GX.antoine_collar_classify`). -/
theorem antoine_collar_inj (j : Fin 64) (δ : Path (antoineX1 j) (antoineX1 j))
    (hδ : ∀ t, δ t ∈ antoineA1 j)
    (hnull : HomotopicIn (antoineStereo '' antoineStage 1)ᶜ δ (Path.refl _)) :
    HomotopicIn (antoineA1 j) δ (Path.refl _) := by
  set X := (antoineStereo '' antoineStage 1)ᶜ
  set δ' := antoinePull j δ hδ
  have hδ' : ∀ t, δ' t ∈ antoineA0 := fun t => (antoinePull_spec j δ hδ t).1
  have hg := continuous_antoineStereo.comp (continuous_antoineMap j)
  have hgA : MapsTo (antoineStereo ∘ antoineMap j) antoineA0 (antoineA1 j) := fun q hq => by
    rw [antoineA1_eq]; exact ⟨q, hq, rfl⟩
  -- the meridional winding vanishes (`Θⱼ`)
  have hW : AntoineLiftWind (fun t => antoineW (δ' t)) 0 := by
    refine (antoineLiftWind_of_homotopicIn_refl hnull (F := antoineTheta (fun _ => j) 1)
      (continuous_antoineTheta _ _).continuousOn fun y hy => antoineTheta_ne_zero_of_compl hy).congr
      fun t => ?_
    rw [← (antoinePull_spec j δ hδ t).2]
    show antoineTheta (fun _ => j) 1 (antoineStereo (antoineMap j (δ' t))) = _
    rw [antoineTheta_one_stereo, antoineMapInv_map, antoinePsi_eq_W (antoineSq_lt_of_mem_nbhd (hδ' t).1)]
  obtain ⟨a, hA⟩ := antoine_exists_liftWind (f := fun t => antoineAng (δ' t))
    (continuous_antoineAng.comp δ'.continuous) (fun t => antoineAng_ne_zero_of_mem (hδ' t).1)
    (by simp only [Path.source, Path.target])
  -- classification against a power of the longitude
  have hL := antoineLon_mem
  have hLA := antoineLiftWind_loopZPow hL continuous_antoineAng.continuousOn
    (fun y hy => antoineAng_ne_zero_of_mem hy.1) antoineLiftWind_lon_Ang (-a)
  have hLW := antoineLiftWind_loopZPow hL continuous_antoineW.continuousOn
    (fun y hy => antoineW_ne_zero hy) antoineLiftWind_lon_W (-a)
  rw [show -a * -1 = a by ring] at hLA
  rw [mul_zero] at hLW
  have hcl := antoine_collar_classify hδ' (loopZPow_mem hL (-a)) hA hLA hW hLW
  have hmap := hcl.map hg (V := antoineA1 j) hgA
  have hδeq : δ'.map hg = δ := Path.ext (funext fun t => (antoinePull_spec j δ hδ t).2)
  rw [hδeq, loopZPow_map] at hmap
  -- the longitudinal winding vanishes (`Θⱼ₊₁`)
  set Λ := antoineLon.map hg
  have hΛ : ∀ t, Λ t ∈ antoineA1 j := fun t => hgA (hL t)
  obtain ⟨w, hw, hwind⟩ := antoine_succ_wind j
  have hΘ : ContinuousOn (antoineTheta (fun _ => j + 1) 1) (antoineA1 j) :=
    (continuous_antoineTheta _ _).continuousOn
  have hΘ0 : ∀ y ∈ antoineA1 j, antoineTheta (fun _ => j + 1) 1 y ≠ 0 := fun y hy =>
    antoineTheta_ne_zero_of_compl (antoineA1_subset_compl j hy)
  have h1 : AntoineLiftWind (fun t => antoineTheta (fun _ => j + 1) 1 (δ t)) 0 :=
    antoineLiftWind_of_homotopicIn_refl hnull (continuous_antoineTheta _ _).continuousOn
      fun y hy => antoineTheta_ne_zero_of_compl hy
  have h2 := AntoineLiftWind.of_homotopicIn hmap hΘ hΘ0 h1
  have hΛw : AntoineLiftWind (fun t => antoineTheta (fun _ => j + 1) 1 (Λ t)) w :=
    hwind.congr fun t => (antoineTheta_one_stereo _ _).symm
  have h3 := antoineLiftWind_loopZPow hΛ hΘ hΘ0 hΛw (-a)
  have e := h2.unique h3
  have ha : a = 0 := by
    rcases mul_eq_zero.1 e.symm with h | h
    · exact neg_eq_zero.1 h
    · exact absurd h hw
  rw [ha] at hmap
  exact hmap


/-- **The non-abelian heart of Antoine's lemma at the first generation** (the field `chain` of
`GX.AntoineFirstGeneration`): no nonzero power of the meridian of `L` is null-homotopic in the
complement of the closed chain `C₁` of the 64 links of the first generation. -/
def AntoineChainEssential : Prop :=
  ∀ a : ℤ, a ≠ 0 →
    ¬ HomotopicIn (antoineStereo '' antoineStage 1)ᶜ (loopZPow antoineMuS a) (Path.refl _)

/-- `GX.AntoineFirstGeneration` from its non-abelian field alone (sorry-free): the five collar
facts are proved above. -/
theorem antoineFirstGeneration_of_chain (h : AntoineChainEssential) : AntoineFirstGeneration :=
  ⟨h, fun i j hij => antoineTube_disjoint i j hij, antoine_collar_conn, antoine_collar_mer,
    antoine_collar_inj, antoine_joined⟩

/-- **The file's one `sorry`: the non-abelian heart of Antoine's lemma at the first
generation**, `GX.AntoineChainEssential` (WP-41r round 1). Everything else of the row is derived
from it sorry-free: the first generation (`GX.antoineFirstGeneration_of_chain`, the five collar
facts), every generation (`GX.antoineMeridianEssentialTop_of_firstGeneration`, the van Kampen
induction `GX.antoine_pow_essential`), the reduction of every link to the top link
(`GX.antoineMeridianEssentialStrict_of_top`), the equal-generation case
(`GX.antoineMeridianEssential_self`), the compactness reduction (`GX.antoine_homotopicIn_stage`),
link selection, accessibility and the based loop (`GX.antoine_essential_loops`), and the
wildness (`GX.tameCantorSLSC`). -/
theorem antoineChainEssential : AntoineChainEssential := by
  sorry -- SORRY(ex:wild_cantor_general_antoine): the non-abelian heart of Antoine's lemma at the first generation, exactly GX.AntoineChainEssential: no nonzero power of the meridian of L is null-homotopic in S³ ∖ C₁, C₁ the closed chain of the 64 first-generation links (everything else, the five collar facts of GX.AntoineFirstGeneration included, is proved: GX.antoineFirstGeneration_of_chain). The meridian is null-homologous in S³ ∖ C₁ (its disk in the plane x = 0 meets C₁ in two oppositely oriented points of the link 40 and the rest of that plane meets the opposite link 8), so no map to ℂ ∖ 0 detects it, and it is trivial once link 8 is deleted (the plane x = 0 then bounds it off), so the detection must see the closing of the chain; it IS detected by a D_∞-representation (a Fox Z-colouring of the necklace diagram with the vertical links tilted, the meridian going to a translation by ±4). The obstruction is the construction of that flat D_∞-structure on S³ ∖ C₁ (the double cover along all 64 meridians, s² = ∏ᵢ Θᵢ, with an anti-invariant map to ℂ ∖ 0, or a D_∞-valued cocycle glued by GX.VanKampen.Data.exists_extension from pieces whose fundamental groups are known) and the evaluation along the meridian.

/-- **Antoine's lemma at the first generation**, `GX.AntoineFirstGeneration`: from its non-abelian
field `GX.antoineChainEssential` (the file's one `sorry`) and the five collar facts, proved. -/
theorem antoineFirstGeneration : AntoineFirstGeneration :=
  antoineFirstGeneration_of_chain antoineChainEssential

/-- **Antoine's lemma for the top link**, `GX.AntoineMeridianEssentialTop`: derived, sorry-free in
its own body, from the first generation `GX.antoineFirstGeneration` by the van Kampen reduction
`GX.antoineMeridianEssentialTop_of_firstGeneration`; it rests on the file's one `sorry`,
`GX.antoineChainEssential`. -/
theorem antoineMeridianEssentialTop : AntoineMeridianEssentialTop :=
  antoineMeridianEssentialTop_of_firstGeneration antoineFirstGeneration

/-- The strict residual; rests on `GX.antoineChainEssential` (via
`GX.antoineMeridianEssentialTop`). -/
theorem antoineMeridianEssentialStrict : AntoineMeridianEssentialStrict :=
  antoineMeridianEssentialStrict_of_top antoineMeridianEssentialTop

/-- The residual `GX.AntoineMeridianEssential` from Antoine's lemma for the top link
(sorry-free). -/
theorem antoineMeridianEssential_of_top (h : AntoineMeridianEssentialTop) :
    AntoineMeridianEssential :=
  antoineMeridianEssential_of_strict (antoineMeridianEssentialStrict_of_top h)

/-- The residual `GX.AntoineMeridianEssential`; rests on `GX.antoineChainEssential` (via
`GX.antoineMeridianEssentialStrict`). -/
theorem antoineMeridianEssential : AntoineMeridianEssential :=
  antoineMeridianEssential_of_strict antoineMeridianEssentialStrict

/-- `ex:wild_cantor_general_antoine` (`RamcovGX.tex:1578`), homotopy form, FROM THE RESIDUAL ALONE:
the complement of `GX.antoineNecklace` is not semi-locally simply connected in `S³`
(sorry-free). -/
theorem antoineNecklace_not_isSLSCIn_of (hres : AntoineMeridianEssential) :
    ¬ IsSLSCIn antoineNecklaceᶜ :=
  sphere3_not_isSLSCIn_of_essential _ (antoine_essential_loops hres)

/-- `ex:wild_cantor_general_antoine`, homotopy form; rests on `GX.antoineChainEssential` (via
`GX.antoineMeridianEssentialTop`). -/
theorem antoineNecklace_not_isSLSCIn : ¬ IsSLSCIn antoineNecklaceᶜ :=
  antoineNecklace_not_isSLSCIn_of antoineMeridianEssential

/-- The tame-Cantor fact: the complement of a Cantor subset of a great circle of `S³` is
semi-locally simply connected in `S³`. PROVED below (`GX.tameCantorSLSC`, a general-position
argument: `GX.gc_loop_null`). -/
def TameCantorSLSC : Prop :=
  ∀ C : Set Sphere3, C ⊆ greatCircle3 → IsCantorSubset C → IsSLSCIn Cᶜ

/-! ### Tame Cantor sets: general position off a great circle (DEC-82)

In the cap `{⟨·, x⟩ > c}` around a point `x` of the great circle `Γ = {w₂ = w₃ = 0}`, the radial
projection `GX.gcF x` carries segments of `ℝ⁴` to arcs of `S³`, and `GX.gcF x w ∈ Γ` iff
`w₂ = w₃ = 0` (`GX.gcF_mem_iff`): a segment meets the plane of `Γ` only where the planar
projections `(w₂, w₃)` of its ends are dependent (`GX.gc_seg_avoid`). Hence a loop at a point of
`Γ ∖ K` (`K ⊆ Γ` closed) is null-homotopic off `K`: a fine polygon whose vertices are pushed
successively transversally (`GX.gcSeq`) meets the plane of `Γ` only at its base point, and the
cone on the base point misses `K` (`GX.gc_loop_null`). -/

/-- A Cantor subset of `S³` is closed. -/
theorem IsCantorSubset.isClosed {C : Set Sphere3} (hC : IsCantorSubset C) : IsClosed C := by
  obtain ⟨e⟩ := hC
  haveI : CompactSpace cantorSet := isCompact_iff_compactSpace.1 isCompact_cantorSet
  haveI := e.symm.compactSpace
  exact (isCompact_iff_compactSpace.2 this).isClosed

/-- The vector `(0, 0, d₁, d₂)` of `ℝ⁴`. -/
def gcEmb (d : ℝ × ℝ) : EuclideanSpace ℝ (Fin 4) := !₂[0, 0, d.1, d.2]

@[simp] theorem gcEmb_two (d : ℝ × ℝ) : gcEmb d 2 = d.1 := by simp [gcEmb]
@[simp] theorem gcEmb_three (d : ℝ × ℝ) : gcEmb d 3 = d.2 := by simp [gcEmb]

theorem norm_gcEmb_le (d : ℝ × ℝ) : ‖gcEmb d‖ ≤ |d.1| + |d.2| := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  simp [gcEmb, Fin.sum_univ_four]
  nlinarith [abs_nonneg d.1, abs_nonneg d.2, sq_abs d.1, sq_abs d.2, abs_mul_abs_self d.1]

theorem inner_gcEmb_of_mem {x : Sphere3} (hx : x ∈ greatCircle3) (d : ℝ × ℝ) :
    inner ℝ (gcEmb d) (x : EuclideanSpace ℝ (Fin 4)) = 0 := by
  obtain ⟨h2, h3⟩ := hx
  simp [gcEmb, PiLp.inner_apply, Fin.sum_univ_four, h2, h3]

theorem sphere3_inner_self (x : Sphere3) :
    inner ℝ (x : EuclideanSpace ℝ (Fin 4)) (x : EuclideanSpace ℝ (Fin 4)) = 1 := by
  rw [real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.1 x.2]; norm_num

/-- The cap `{y ∈ S³ : c < ⟨y, x⟩}`. -/
def gcCap (x : Sphere3) (c : ℝ) : Set Sphere3 :=
  {y | c < inner ℝ (y : EuclideanSpace ℝ (Fin 4)) (x : EuclideanSpace ℝ (Fin 4))}

/-- Pushing `w` into the half-space `⟨·, x⟩ ≥ 1/2`. -/
def gcLift (x : Sphere3) (w : EuclideanSpace ℝ (Fin 4)) : EuclideanSpace ℝ (Fin 4) :=
  w + (max 0 (1 / 2 - inner ℝ w (x : EuclideanSpace ℝ (Fin 4)))) • (x : EuclideanSpace ℝ (Fin 4))

theorem gcLift_inner (x : Sphere3) (w : EuclideanSpace ℝ (Fin 4)) :
    1 / 2 ≤ inner ℝ (gcLift x w) (x : EuclideanSpace ℝ (Fin 4)) := by
  simp only [gcLift, inner_add_left, real_inner_smul_left, sphere3_inner_self, mul_one]
  linarith [le_max_right 0 (1 / 2 - inner ℝ w (x : EuclideanSpace ℝ (Fin 4)))]

theorem gcLift_ne_zero (x : Sphere3) (w : EuclideanSpace ℝ (Fin 4)) : gcLift x w ≠ 0 := by
  intro h; have := gcLift_inner x w; rw [h, inner_zero_left] at this; norm_num at this

theorem continuous_gcLift (x : Sphere3) : Continuous (gcLift x) :=
  continuous_id.add
    ((continuous_const.max (continuous_const.sub (continuous_id.inner continuous_const))).smul
      continuous_const)

theorem gcLift_of_le {x : Sphere3} {w : EuclideanSpace ℝ (Fin 4)}
    (h : 1 / 2 ≤ inner ℝ w (x : EuclideanSpace ℝ (Fin 4))) : gcLift x w = w := by
  simp only [gcLift, max_eq_left (by linarith : 1 / 2 - inner ℝ w (x : EuclideanSpace ℝ (Fin 4)) ≤ 0),
    zero_smul, add_zero]

theorem norm_gcLift_smul (x : Sphere3) (w : EuclideanSpace ℝ (Fin 4)) :
    ‖‖gcLift x w‖⁻¹ • gcLift x w‖ = 1 := by
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 (gcLift_ne_zero x w))]

/-- The radial projection onto `S³`, centred at `x` (continuous on all of `ℝ⁴`). -/
def gcF (x : Sphere3) (w : EuclideanSpace ℝ (Fin 4)) : Sphere3 :=
  ⟨‖gcLift x w‖⁻¹ • gcLift x w, mem_sphere_zero_iff_norm.2 (norm_gcLift_smul x w)⟩

theorem continuous_gcF (x : Sphere3) : Continuous (gcF x) :=
  Continuous.subtype_mk (((continuous_norm.comp (continuous_gcLift x)).inv₀
    fun w => norm_ne_zero_iff.2 (gcLift_ne_zero x w)).smul (continuous_gcLift x)) _

theorem gcF_coe_of_le {x : Sphere3} {w : EuclideanSpace ℝ (Fin 4)}
    (h : 1 / 2 ≤ inner ℝ w (x : EuclideanSpace ℝ (Fin 4))) :
    (gcF x w : EuclideanSpace ℝ (Fin 4)) = ‖w‖⁻¹ • w := by
  change ‖gcLift x w‖⁻¹ • gcLift x w = _
  rw [gcLift_of_le h]

theorem gcF_sphere {x y : Sphere3}
    (h : 1 / 2 ≤ inner ℝ (y : EuclideanSpace ℝ (Fin 4)) (x : EuclideanSpace ℝ (Fin 4))) :
    gcF x y = y := by
  apply Subtype.ext
  rw [gcF_coe_of_le h, mem_sphere_zero_iff_norm.1 y.2, inv_one, one_smul]

theorem gcF_self (x : Sphere3) : gcF x x = x :=
  gcF_sphere (by rw [sphere3_inner_self]; norm_num)

theorem gc_ne_zero_of_half_le {x : Sphere3} {w : EuclideanSpace ℝ (Fin 4)}
    (h : 1 / 2 ≤ inner ℝ w (x : EuclideanSpace ℝ (Fin 4))) : w ≠ 0 := by
  rintro rfl; rw [inner_zero_left] at h; norm_num at h

/-- `gcF x w` lies on the great circle iff the last two coordinates of `w` vanish. -/
theorem gcF_mem_iff {x : Sphere3} {w : EuclideanSpace ℝ (Fin 4)}
    (h : 1 / 2 ≤ inner ℝ w (x : EuclideanSpace ℝ (Fin 4))) :
    gcF x w ∈ greatCircle3 ↔ w 2 = 0 ∧ w 3 = 0 := by
  have hn : ‖w‖⁻¹ ≠ 0 := inv_ne_zero (norm_ne_zero_iff.2 (gc_ne_zero_of_half_le h))
  change (gcF x w : EuclideanSpace ℝ (Fin 4)) 2 = 0 ∧ (gcF x w : EuclideanSpace ℝ (Fin 4)) 3 = 0 ↔ _
  rw [gcF_coe_of_le h]
  simp [PiLp.smul_apply, hn]

theorem gcF_dist_le {x y : Sphere3} {w : EuclideanSpace ℝ (Fin 4)}
    (h : 1 / 2 ≤ inner ℝ w (x : EuclideanSpace ℝ (Fin 4))) :
    dist (gcF x w) y ≤ 2 * ‖w - (y : EuclideanSpace ℝ (Fin 4))‖ := by
  have hw : w ≠ 0 := gc_ne_zero_of_half_le h
  have hpos : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hy : ‖(y : EuclideanSpace ℝ (Fin 4))‖ = 1 := mem_sphere_zero_iff_norm.1 y.2
  rw [Subtype.dist_eq, dist_eq_norm, gcF_coe_of_le h]
  have e : ‖w‖⁻¹ • w - (y : EuclideanSpace ℝ (Fin 4)) =
      (‖w‖⁻¹ - 1) • w + (w - (y : EuclideanSpace ℝ (Fin 4))) := by
    rw [sub_smul, one_smul]; abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs]
  have h1 : |‖w‖⁻¹ - 1| * ‖w‖ = |1 - ‖w‖| := by
    rw [← abs_of_pos hpos, ← abs_mul, abs_of_pos hpos, sub_mul, inv_mul_cancel₀ hpos.ne', one_mul]
  rw [h1]
  have h2 : |1 - ‖w‖| ≤ ‖w - (y : EuclideanSpace ℝ (Fin 4))‖ := by
    have := abs_norm_sub_norm_le w (y : EuclideanSpace ℝ (Fin 4))
    rw [hy] at this; rwa [abs_sub_comm]
  linarith

theorem isOpen_gcCap (x : Sphere3) (c : ℝ) : IsOpen (gcCap x c) :=
  isOpen_lt continuous_const (continuous_subtype_val.inner continuous_const)

theorem mem_gcCap_self {x : Sphere3} {c : ℝ} (hc : c < 1) : x ∈ gcCap x c := by
  show c < _; rw [sphere3_inner_self]; exact hc

theorem gcCap_mono {x : Sphere3} {c c' : ℝ} (h : c ≤ c') : gcCap x c' ⊆ gcCap x c :=
  fun _ hy => lt_of_le_of_lt h hy

/-- The caps around `x` form a basis of neighbourhoods. -/
theorem exists_gcCap_subset {x : Sphere3} {W : Set Sphere3} (hW : W ∈ 𝓝 x) (c₀ : ℝ) (hc₀ : c₀ < 1) :
    ∃ c, c₀ ≤ c ∧ c < 1 ∧ gcCap x c ⊆ W := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hW
  refine ⟨max c₀ (1 - ε ^ 2 / 4), le_max_left _ _, max_lt hc₀ (by nlinarith), fun y hy => ?_⟩
  apply hball
  have hy' : 1 - ε ^ 2 / 4 < inner ℝ (y : EuclideanSpace ℝ (Fin 4)) (x : EuclideanSpace ℝ (Fin 4)) :=
    lt_of_le_of_lt (le_max_right _ _) hy
  rw [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm]
  have hsq : ‖(y : EuclideanSpace ℝ (Fin 4)) - x‖ ^ 2 < ε ^ 2 := by
    rw [norm_sub_sq_real, mem_sphere_zero_iff_norm.1 y.2, mem_sphere_zero_iff_norm.1 x.2]
    nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 hε.le hsq

/-- The convex body over a cap. -/
def gcBody (x : Sphere3) (c : ℝ) : Set (EuclideanSpace ℝ (Fin 4)) :=
  {w | ‖w‖ ≤ 1 ∧ c < inner ℝ w (x : EuclideanSpace ℝ (Fin 4))}

theorem convex_gcBody (x : Sphere3) (c : ℝ) : Convex ℝ (gcBody x c) := by
  have h1 : Convex ℝ {w : EuclideanSpace ℝ (Fin 4) | ‖w‖ ≤ 1} := by
    simpa [Metric.closedBall, dist_zero_right] using
      convex_closedBall (0 : EuclideanSpace ℝ (Fin 4)) 1
  have h2 : Convex ℝ {w : EuclideanSpace ℝ (Fin 4) | c < inner ℝ w (x : EuclideanSpace ℝ (Fin 4))} :=
    convex_halfSpace_gt
      ⟨fun a b => inner_add_left a b _, fun r a => real_inner_smul_left a _ r⟩ c
  exact h1.inter h2

theorem coe_mem_gcBody {x y : Sphere3} {c : ℝ} (hy : y ∈ gcCap x c) :
    (y : EuclideanSpace ℝ (Fin 4)) ∈ gcBody x c :=
  ⟨(mem_sphere_zero_iff_norm.1 y.2).le, hy⟩

theorem gcF_mem_gcCap {x : Sphere3} {c : ℝ} (hc : 1 / 2 ≤ c) {w : EuclideanSpace ℝ (Fin 4)}
    (hw : w ∈ gcBody x c) : gcF x w ∈ gcCap x c := by
  have h12 : 1 / 2 ≤ inner ℝ w (x : EuclideanSpace ℝ (Fin 4)) := hc.trans hw.2.le
  have hpos : 0 < ‖w‖ := norm_pos_iff.2 (gc_ne_zero_of_half_le h12)
  show c < inner ℝ (gcF x w : EuclideanSpace ℝ (Fin 4)) _
  rw [gcF_coe_of_le h12, real_inner_smul_left]
  have : inner ℝ w (x : EuclideanSpace ℝ (Fin 4)) ≤
      ‖w‖⁻¹ * inner ℝ w (x : EuclideanSpace ℝ (Fin 4)) := by
    have h1 : 1 ≤ ‖w‖⁻¹ := (one_le_inv₀ hpos).2 hw.1
    nlinarith
  linarith [hw.2]

theorem gcCap_eq_image {x : Sphere3} {c : ℝ} (hc : 1 / 2 ≤ c) :
    gcCap x c = gcF x '' gcBody x c := by
  ext y
  refine ⟨fun hy => ⟨_, coe_mem_gcBody hy, gcF_sphere (hc.trans hy.le)⟩, ?_⟩
  rintro ⟨w, hw, rfl⟩
  exact gcF_mem_gcCap hc hw

theorem isPreconnected_gcCap (x : Sphere3) {c : ℝ} (hc : 1 / 2 ≤ c) :
    IsPreconnected (gcCap x c) := by
  rw [gcCap_eq_image hc]
  exact (convex_gcBody x c).isPreconnected.image _ (continuous_gcF x).continuousOn

/-- Two paths of a cap (`c ≥ 1/2`) with the same ends are homotopic in the cap. -/
theorem gcCap_homotopicIn {x : Sphere3} {c : ℝ} (hc : 1 / 2 ≤ c) {a b : Sphere3}
    (ρ₁ ω : Path a b) (hρ₁ : ∀ t, ρ₁ t ∈ gcCap x c) (hω : ∀ t, ω t ∈ gcCap x c) :
    HomotopicIn (gcCap x c) ρ₁ ω := by
  have ha0 : a ∈ gcCap x c := by simpa using hρ₁ 0
  have hb1 : b ∈ gcCap x c := by simpa using hρ₁ 1
  have ha : gcF x a = a := gcF_sphere (hc.trans ha0.le)
  have hb : gcF x b = b := gcF_sphere (hc.trans hb1.le)
  have key := homotopicIn_map_of_convex (U := gcCap x c) (ρ₁.map continuous_subtype_val)
    (ω.map continuous_subtype_val) (convex_gcBody x c) (fun t => coe_mem_gcBody (hρ₁ t))
    (fun t => coe_mem_gcBody (hω t)) (continuous_gcF x) fun e he => gcF_mem_gcCap hc he
  refine (key.cast ha.symm hb.symm).of_eq ?_ ?_
  · refine Path.ext (funext fun t => ?_)
    simp only [Path.cast_coe, Path.map_coe, Function.comp_apply]
    exact gcF_sphere (hc.trans (hρ₁ t).le)
  · refine Path.ext (funext fun t => ?_)
    simp only [Path.cast_coe, Path.map_coe, Function.comp_apply]
    exact gcF_sphere (hc.trans (hω t).le)

/-- `det(u, w)` in `ℝ²`. -/
def gcDet (u w : ℝ × ℝ) : ℝ := u.1 * w.2 - u.2 * w.1

/-- Three directions: any two nonzero vectors of `ℝ²` are both transverse to one of them. -/
theorem gc_exists_dir (u v : ℝ × ℝ) {s : ℝ} (hs : 0 < s) :
    ∃ d : ℝ × ℝ, d ≠ 0 ∧ |d.1| ≤ s ∧ |d.2| ≤ s ∧ (u ≠ 0 → gcDet u d ≠ 0) ∧
      (v ≠ 0 → gcDet v d ≠ 0) := by
  have hs' : s ≠ 0 := hs.ne'
  have habs : |s| = s := abs_of_pos hs
  by_cases h1 : (u = 0 ∨ u.2 ≠ 0) ∧ (v = 0 ∨ v.2 ≠ 0)
  · refine ⟨(s, 0), fun h => hs' (congrArg Prod.fst h), by simp [habs], by simp [hs.le], ?_, ?_⟩
    · intro hu; rcases h1.1 with h | h
      · exact absurd h hu
      · simp [gcDet, h, hs']
    · intro hv; rcases h1.2 with h | h
      · exact absurd h hv
      · simp [gcDet, h, hs']
  by_cases h2 : (u = 0 ∨ u.1 ≠ 0) ∧ (v = 0 ∨ v.1 ≠ 0)
  · refine ⟨(0, s), fun h => hs' (congrArg Prod.snd h), by simp [hs.le], by simp [habs], ?_, ?_⟩
    · intro hu; rcases h2.1 with h | h
      · exact absurd h hu
      · simp [gcDet, h, hs']
    · intro hv; rcases h2.2 with h | h
      · exact absurd h hv
      · simp [gcDet, h, hs']
  refine ⟨(s, s), fun h => hs' (congrArg Prod.fst h), by simp [habs], by simp [habs], ?_, ?_⟩
  · intro hu
    simp only [gcDet]
    intro he
    have he' : u.1 = u.2 := by
      have : (u.1 - u.2) * s = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · exact absurd h hs'
    apply hu
    push Not at h1 h2
    by_cases hu1 : u.1 = 0
    · exact Prod.ext hu1 (he' ▸ hu1)
    · have hv : v ≠ 0 ∧ v.1 = 0 := h2 (Or.inr hu1)
      have hu2 : u.2 ≠ 0 := he' ▸ hu1
      have hv2 : v ≠ 0 ∧ v.2 = 0 := h1 (Or.inr hu2)
      exact absurd (Prod.ext hv.2 hv2.2) hv.1
  · intro hv
    simp only [gcDet]
    intro he
    have he' : v.1 = v.2 := by
      have : (v.1 - v.2) * s = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · exact absurd h hs'
    apply hv
    push Not at h1 h2
    by_cases hv1 : v.1 = 0
    · exact Prod.ext hv1 (he' ▸ hv1)
    · have hv2 : v.2 ≠ 0 := he' ▸ hv1
      have hu : ¬ (u = 0 ∨ u.2 ≠ 0) := fun h => hv2 (h1 h).2
      push Not at hu
      have hu1 : u.1 ≠ 0 := fun h => hu.1 (Prod.ext h hu.2)
      exact absurd (h2 (Or.inr hu1)).2 hv1

/-- The core transversality computation: `(1-r) a + r d = 0` with `d ≠ 0` transverse to `a`
(when `a ≠ 0`) forces `r = 0` and `a = 0`. -/
theorem gc_seg_avoid {a d : ℝ × ℝ} (hd : d ≠ 0) (had : a ≠ 0 → gcDet a d ≠ 0) {r : ℝ}
    (h1 : (1 - r) * a.1 + r * d.1 = 0) (h2 : (1 - r) * a.2 + r * d.2 = 0) : r = 0 ∧ a = 0 := by
  by_cases ha : a = 0
  · subst ha
    simp at h1 h2
    refine ⟨?_, rfl⟩
    by_contra hr
    exact hd (Prod.ext (by simpa [hr] using h1) (by simpa [hr] using h2))
  · have hdet := had ha
    have : r * gcDet a d = 0 := by
      simp only [gcDet]; linear_combination a.1 * h2 - a.2 * h1
    rcases mul_eq_zero.1 this with hr | hr
    · subst hr
      exact absurd (Prod.ext (by simpa using h1) (by simpa using h2)) ha
    · exact absurd hr hdet

/-- A segment of the body over a cap whose only possible points over the great circle are its
ends maps, by the radial projection, into the cap and off any `C ⊆ greatCircle3` missing the
images of its ends. -/
theorem gc_segment_mem {x : Sphere3} {c : ℝ} (hc : 1 / 2 ≤ c) {C : Set Sphere3}
    (hC : C ⊆ greatCircle3) {u w : EuclideanSpace ℝ (Fin 4)} (hu : u ∈ gcBody x c)
    (hw : w ∈ gcBody x c) (huC : gcF x u ∉ C) (hwC : gcF x w ∉ C)
    (H : ∀ r : I, (AffineMap.lineMap u w (r : ℝ) : EuclideanSpace ℝ (Fin 4)) 2 = 0 →
      (AffineMap.lineMap u w (r : ℝ) : EuclideanSpace ℝ (Fin 4)) 3 = 0 →
      AffineMap.lineMap u w (r : ℝ) = u ∨ AffineMap.lineMap u w (r : ℝ) = w) (t : I) :
    gcF x (Path.segment u w t) ∈ gcCap x c ∧ gcF x (Path.segment u w t) ∉ C := by
  have hmem : Path.segment u w t ∈ gcBody x c :=
    (convex_gcBody x c).lineMap_mem hu hw t.2
  refine ⟨gcF_mem_gcCap hc hmem, fun hC' => ?_⟩
  have h12 : 1 / 2 ≤ inner ℝ (Path.segment u w t) (x : EuclideanSpace ℝ (Fin 4)) :=
    hc.trans hmem.2.le
  obtain ⟨e2, e3⟩ := (gcF_mem_iff h12).1 (hC hC')
  rcases H t e2 e3 with h | h
  · exact huC (by rw [← h]; exact hC')
  · exact hwC (by rw [← h]; exact hC')

theorem gc_lineMap_apply (u w : EuclideanSpace ℝ (Fin 4)) (r : ℝ) (i : Fin 4) :
    (AffineMap.lineMap u w r : EuclideanSpace ℝ (Fin 4)) i = (1 - r) * u i + r * w i := by
  simp only [AffineMap.lineMap_apply_module, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]

/-- **Local joining off `C`.** In a cap around a point of the great circle, any two points off a
subset `C` of the great circle are joined by a path of the cap off `C`: through a midpoint pushed
off the great circle in a direction transverse to both. -/
theorem gc_join {x : Sphere3} (hx : x ∈ greatCircle3) {c : ℝ} (hc : 1 / 2 ≤ c) (hc1 : c < 1)
    {C : Set Sphere3} (hC : C ⊆ greatCircle3) {a b : Sphere3} (ha : a ∈ gcCap x c)
    (hb : b ∈ gcCap x c) (haC : a ∉ C) (hbC : b ∉ C) :
    ∃ ω : Path a b, ∀ t, ω t ∈ gcCap x c ∧ ω t ∉ C := by
  set η : ℝ := (1 - c) / 2 with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  have hη1 : η ≤ 1 / 4 := by rw [hη]; linarith
  obtain ⟨d, hd0, hd1, hd2, hda, hdb⟩ := gc_exists_dir ((a : EuclideanSpace ℝ (Fin 4)) 2,
    (a : EuclideanSpace ℝ (Fin 4)) 3) ((b : EuclideanSpace ℝ (Fin 4)) 2,
    (b : EuclideanSpace ℝ (Fin 4)) 3) (show 0 < η / 2 by linarith)
  set m : EuclideanSpace ℝ (Fin 4) := (1 - η) • (x : EuclideanSpace ℝ (Fin 4)) + gcEmb d with hm
  have hx2 : (x : EuclideanSpace ℝ (Fin 4)) 2 = 0 := hx.1
  have hx3 : (x : EuclideanSpace ℝ (Fin 4)) 3 = 0 := hx.2
  have hm2 : m 2 = d.1 := by simp [hm, hx2]
  have hm3 : m 3 = d.2 := by simp [hm, hx3]
  have hmx : inner ℝ m (x : EuclideanSpace ℝ (Fin 4)) = 1 - η := by
    rw [hm, inner_add_left, real_inner_smul_left, sphere3_inner_self, inner_gcEmb_of_mem hx]; ring
  have hmB : m ∈ gcBody x c := by
    refine ⟨?_, by rw [hmx, hη]; linarith⟩
    have he : ‖gcEmb d‖ ≤ η := (norm_gcEmb_le d).trans (by linarith)
    have hsq : ‖m‖ ^ 2 ≤ 1 := by
      rw [hm, norm_add_sq_real, norm_smul, real_inner_smul_left,
        real_inner_comm, inner_gcEmb_of_mem hx, mem_sphere_zero_iff_norm.1 x.2,
        Real.norm_eq_abs, abs_of_pos (by linarith : 0 < 1 - η)]
      have : ‖gcEmb d‖ ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ (norm_nonneg _) he 2
      nlinarith
    nlinarith [norm_nonneg m]
  have hmC : gcF x m ∉ C := fun h => by
    obtain ⟨e2, e3⟩ := (gcF_mem_iff (hc.trans hmB.2.le)).1 (hC h)
    exact hd0 (Prod.ext (hm2 ▸ e2) (hm3 ▸ e3))
  have hFa : gcF x a = a := gcF_sphere (hc.trans ha.le)
  have hFb : gcF x b = b := gcF_sphere (hc.trans hb.le)
  have haC' : gcF x a ∉ C := hFa.symm ▸ haC
  have hbC' : gcF x b ∉ C := hFb.symm ▸ hbC
  have h1 := gc_segment_mem hc hC (coe_mem_gcBody ha) hmB haC' hmC (fun r e2 e3 => by
    rw [gc_lineMap_apply, hm2] at e2
    rw [gc_lineMap_apply, hm3] at e3
    obtain ⟨hr, -⟩ := gc_seg_avoid hd0 hda e2 e3
    left; rw [hr]; simp)
  have h2 := gc_segment_mem hc hC hmB (coe_mem_gcBody hb) hmC hbC' (fun r e2 e3 => by
    rw [gc_lineMap_apply, hm2] at e2
    rw [gc_lineMap_apply, hm3] at e3
    obtain ⟨hr, -⟩ := gc_seg_avoid (r := 1 - r) hd0 hdb (by linarith) (by linarith)
    right; rw [show (r : ℝ) = 1 by linarith]; simp)
  refine ⟨(((Path.segment (a : EuclideanSpace ℝ (Fin 4)) m).map (continuous_gcF x)).cast
    hFa.symm rfl).trans (((Path.segment m (b : EuclideanSpace ℝ (Fin 4))).map
    (continuous_gcF x)).cast rfl hFb.symm), fun t => ?_⟩
  rw [Path.trans_apply]
  split_ifs
  · exact h1 _
  · exact h2 _

/-- The straight-line homotopy, pushed by `F`, with a pointwise membership condition. -/
theorem gc_homotopicIn_map_line {X : Type*} [TopologicalSpace X] {U : Set X}
    {a b : EuclideanSpace ℝ (Fin 4)} (α β : Path a b) {F : EuclideanSpace ℝ (Fin 4) → X}
    (hF : Continuous F) (h : ∀ s t : I, F (AffineMap.lineMap (α t) (β t) (s : ℝ)) ∈ U) :
    HomotopicIn U (α.map hF) (β.map hF) :=
  ⟨(lineHomotopy α β).map ⟨F, hF⟩, fun w => h w.1 w.2⟩

/-- The hat function `max 0 (1 - |u|)`. -/
def gcHat (u : ℝ) : ℝ := max 0 (1 - |u|)

theorem continuous_gcHat : Continuous gcHat := by unfold gcHat; fun_prop

/-- On `[i, i+1]` the hat functions interpolate linearly between `v i` and `v (i+1)`. -/
theorem gc_sum_hat {E : Type*} [AddCommGroup E] [Module ℝ E] (v : ℕ → E) {N i : ℕ} (hi : i < N)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ∑ j ∈ Finset.range (N + 1), gcHat (i + r - j) • v j = (1 - r) • v i + r • v (i + 1) := by
  rw [Finset.sum_eq_add_of_mem i (i + 1) (by simp; omega) (by simp; omega) (by omega)]
  · congr 1
    · simp [gcHat, abs_of_nonneg hr0, max_eq_right (by linarith : 0 ≤ 1 - r)]
    · push_cast
      rw [show (i : ℝ) + r - (i + 1) = r - 1 by ring, gcHat, abs_of_nonpos (by linarith),
        max_eq_right (by linarith)]
      congr 1; ring
  · intro j _ hj
    have h1 : 1 ≤ |(i : ℝ) + r - j| := by
      rcases lt_or_gt_of_ne hj.1 with h | h
      · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
        rw [abs_of_nonneg (by linarith)]; linarith
      · have : (i : ℝ) + 2 ≤ j := by
          have : i + 2 ≤ j := by omega
          exact_mod_cast this
        rw [abs_of_nonpos (by linarith)]; linarith
    simp [gcHat, max_eq_left (by linarith : 1 - |(i : ℝ) + r - j| ≤ 0)]

/-- Every `t ∈ [0,1]` is `(i + r)/N` with `i < N`, `0 ≤ r ≤ 1`. -/
theorem gc_exists_piece {N : ℕ} (hN : 1 ≤ N) (t : I) :
    ∃ i : ℕ, i < N ∧ ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧ (N : ℝ) * t = i + r := by
  have h0 : 0 ≤ (N : ℝ) * t := mul_nonneg (Nat.cast_nonneg _) t.2.1
  have hle : (N : ℝ) * t ≤ N := by
    have := t.2.2; nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  set q := ⌊(N : ℝ) * t⌋₊ with hq
  have hq1 : (q : ℝ) ≤ N * t := Nat.floor_le h0
  have hq2 : (N : ℝ) * t < q + 1 := Nat.lt_floor_add_one _
  by_cases hqN : q < N
  · exact ⟨q, hqN, N * t - q, by linarith, by linarith, by ring⟩
  · refine ⟨N - 1, by omega, 1, zero_le_one, le_rfl, ?_⟩
    have : (N : ℝ) ≤ q := by exact_mod_cast (not_lt.1 hqN)
    rw [Nat.cast_sub hN]; push_cast; linarith

/-- The perturbation step: `κ • u⊥` with `κ` one of two small values, transverse to `u`. -/
def gcPick (u c : ℝ × ℝ) (s : ℝ) : ℝ × ℝ :=
  if gcDet u (c + (s / (|u.1| + |u.2| + 1)) • (-u.2, u.1)) ≠ 0 then
    (s / (|u.1| + |u.2| + 1)) • (-u.2, u.1) else (s / (|u.1| + |u.2| + 1) / 2) • (-u.2, u.1)

theorem gcPick_bound (u c : ℝ × ℝ) {s : ℝ} (hs : 0 ≤ s) :
    |(gcPick u c s).1| ≤ s ∧ |(gcPick u c s).2| ≤ s := by
  have hA : 0 < |u.1| + |u.2| + 1 := by positivity
  set τ := s / (|u.1| + |u.2| + 1) with hτ
  have hτ0 : 0 ≤ τ := div_nonneg hs hA.le
  have hτA : τ * (|u.1| + |u.2| + 1) = s := div_mul_cancel₀ s hA.ne'
  have key : ∀ κ, 0 ≤ κ → κ ≤ τ → |(κ • (-u.2, u.1)).1| ≤ s ∧ |(κ • (-u.2, u.1)).2| ≤ s := by
    intro κ hκ hκτ
    simp only [Prod.smul_mk, smul_eq_mul, abs_mul, abs_neg, abs_of_nonneg hκ]
    constructor <;> nlinarith [abs_nonneg u.1, abs_nonneg u.2]
  unfold gcPick
  split_ifs
  · exact key τ hτ0 le_rfl
  · exact key (τ / 2) (by positivity) (by linarith)

theorem gcDet_add_smul_perp (u c : ℝ × ℝ) (κ : ℝ) :
    gcDet u (c + κ • (-u.2, u.1)) = gcDet u c + κ * (u.1 ^ 2 + u.2 ^ 2) := by
  simp only [gcDet, Prod.fst_add, Prod.snd_add, Prod.smul_mk, smul_eq_mul]; ring

theorem gcPick_det {u : ℝ × ℝ} (hu : u ≠ 0) (c : ℝ × ℝ) {s : ℝ} (hs : 0 < s) :
    gcDet u (c + gcPick u c s) ≠ 0 := by
  have hQ : 0 < u.1 ^ 2 + u.2 ^ 2 := by
    by_contra h
    push Not at h
    have h1 : u.1 = 0 := by nlinarith [sq_nonneg u.1, sq_nonneg u.2]
    have h2 : u.2 = 0 := by nlinarith [sq_nonneg u.1, sq_nonneg u.2]
    exact hu (Prod.ext h1 h2)
  have hA : 0 < |u.1| + |u.2| + 1 := by positivity
  have hτ : 0 < s / (|u.1| + |u.2| + 1) := div_pos hs hA
  unfold gcPick
  split_ifs with h
  · exact h
  · push Not at h
    rw [gcDet_add_smul_perp] at h ⊢
    intro h'
    nlinarith

/-- The projections of the perturbed vertices, chosen successively transverse. -/
def gcSeq (c : ℕ → ℝ × ℝ) (s : ℝ) : ℕ → ℝ × ℝ
  | 0 => (1, 0)
  | j + 1 => c (j + 1) + gcPick (gcSeq c s j) (c (j + 1)) s

theorem gcDet_zero_right (u : ℝ × ℝ) : gcDet u 0 = 0 := by simp [gcDet]

theorem gcSeq_spec (c : ℕ → ℝ × ℝ) {s : ℝ} (hs : 0 < s) (j : ℕ) :
    gcSeq c s j ≠ 0 ∧ gcDet (gcSeq c s j) (gcSeq c s (j + 1)) ≠ 0 := by
  induction j with
  | zero =>
    have h0 : gcSeq c s 0 ≠ 0 := fun h => by simpa [gcSeq] using congrArg Prod.fst h
    exact ⟨h0, gcPick_det h0 _ hs⟩
  | succ j ih =>
    have h0 : gcSeq c s (j + 1) ≠ 0 := fun h => ih.2 (by rw [h, gcDet_zero_right])
    exact ⟨h0, gcPick_det h0 _ hs⟩

/-- **General position, the key lemma of tameness.** If `K` is a closed subset of the great
circle and `x` a point of the great circle off `K`, every loop at `x` in the cap `⟨·, x⟩ > 3/4`
off `K` is null-homotopic in `S³ ∖ K`: approximate it by a polygon whose vertices are pushed off
the great circle successively transversally (`GX.gcSeq`), so that the polygon meets the plane of
the great circle only at `x`; then cone the polygon off to `x`. -/
theorem gc_loop_null {K : Set Sphere3} (hK : IsClosed K) (hKΓ : K ⊆ greatCircle3) {x : Sphere3}
    (hx : x ∈ greatCircle3) (hxK : x ∉ K) (α : Path x x) (hα : ∀ t, α t ∈ gcCap x (3 / 4))
    (hαK : ∀ t, α t ∉ K) : HomotopicIn Kᶜ α (Path.refl x) := by
  -- a uniform distance from `K`
  obtain ⟨d, hd, hdK⟩ : ∃ d > 0, ∀ t k, k ∈ K → d ≤ dist (α t) k := by
    rcases K.eq_empty_or_nonempty with rfl | hne
    · exact ⟨1, one_pos, fun _ _ h => h.elim⟩
    · have hcont : Continuous fun t => Metric.infDist (α t) K :=
        (Metric.continuous_infDist_pt K).comp α.continuous
      obtain ⟨t₀, -, ht₀⟩ := isCompact_univ.exists_isMinOn univ_nonempty hcont.continuousOn
      exact ⟨Metric.infDist (α t₀) K, (hK.notMem_iff_infDist_pos hne).1 (hαK t₀),
        fun t k hk => (ht₀ (mem_univ t)).trans (Metric.infDist_le_dist_of_mem hk)⟩
  set ε : ℝ := min d 1 / 8 with hεdef
  have hε : 0 < ε := by positivity
  have hεd : 4 * ε < d := by
    have := min_le_left d 1; rw [hεdef]; linarith
  have hε1 : ε ≤ 1 / 8 := by
    have := min_le_right d 1; rw [hεdef]; linarith
  obtain ⟨δ, hδ, hδα⟩ := Metric.uniformContinuous_iff.1
    (CompactSpace.uniformContinuous_of_continuous α.continuous) ε hε
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / δ)
  set N : ℕ := M + 2 with hNdef
  have hN2 : 2 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by positivity
  have hNδ : 1 / (N : ℝ) < δ := by
    rw [div_lt_iff₀ hNpos]
    have : (M : ℝ) + 2 = N := by rw [hNdef]; push_cast; ring
    rw [div_lt_iff₀ hδ] at hM
    nlinarith
  -- vertices
  set tN : ℕ → I := fun j => Set.projIcc 0 1 zero_le_one ((j : ℝ) / N) with htN
  have htN_le : ∀ j, j ≤ N → ((tN j : I) : ℝ) = j / N := fun j hj => by
    simp only [htN, Set.coe_projIcc]
    have h1 : (j : ℝ) / N ≤ 1 := by
      rw [div_le_one hNpos]; exact_mod_cast hj
    rw [min_eq_right h1, max_eq_right (by positivity)]
  have htN_ge : ∀ j, N ≤ j → tN j = 1 := fun j hj => by
    apply Subtype.ext
    simp only [htN, Set.coe_projIcc]
    have h1 : 1 ≤ (j : ℝ) / N := by
      rw [le_div_iff₀ hNpos, one_mul]; exact_mod_cast hj
    rw [min_eq_left h1, max_eq_right zero_le_one]; rfl
  have htN0 : tN 0 = 0 := Subtype.ext (by rw [htN_le 0 (by omega)]; simp)
  set cc : ℕ → ℝ × ℝ := fun j =>
    ((α (tN j) : EuclideanSpace ℝ (Fin 4)) 2, (α (tN j) : EuclideanSpace ℝ (Fin 4)) 3) with hcc
  have hs : 0 < ε / 4 := by positivity
  set u : ℕ → ℝ × ℝ := gcSeq cc (ε / 4) with hu
  have hu_spec := gcSeq_spec cc hs
  have hu_succ : ∀ k, u (k + 1) - cc (k + 1) = gcPick (u k) (cc (k + 1)) (ε / 4) := fun k => by
    simp [hu, gcSeq]
  set v : ℕ → EuclideanSpace ℝ (Fin 4) := fun j => if j = 0 ∨ N ≤ j then (x : EuclideanSpace ℝ (Fin 4))
    else (α (tN j) : EuclideanSpace ℝ (Fin 4)) + gcEmb (u j - cc j) with hv
  have hx2 : (x : EuclideanSpace ℝ (Fin 4)) 2 = 0 := hx.1
  have hx3 : (x : EuclideanSpace ℝ (Fin 4)) 3 = 0 := hx.2
  -- vertices are close to the loop
  have hv_close : ∀ j, ‖v j - (α (tN j) : EuclideanSpace ℝ (Fin 4))‖ ≤ ε / 2 := fun j => by
    by_cases hj : j = 0 ∨ N ≤ j
    · have : α (tN j) = x := by
        rcases hj with rfl | hj
        · rw [htN0, α.source]
        · rw [htN_ge j hj, α.target]
      simp only [hv, if_pos hj, this, sub_self, norm_zero]; positivity
    · simp only [hv, if_neg hj, add_sub_cancel_left]
      obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      rw [hu_succ]
      obtain ⟨b1, b2⟩ := gcPick_bound (u k) (cc (k + 1)) hs.le
      exact (norm_gcEmb_le _).trans (by linarith)
  -- projections of the vertices
  have hv_proj_end : ∀ j, (j = 0 ∨ N ≤ j) → v j 2 = 0 ∧ v j 3 = 0 := fun j hj => by
    simp only [hv, if_pos hj]; exact ⟨hx2, hx3⟩
  have hv_proj_mid : ∀ j, ¬ (j = 0 ∨ N ≤ j) → (v j 2, v j 3) = u j := fun j hj => by
    simp only [hv, if_neg hj, PiLp.add_apply, gcEmb_two, gcEmb_three, hcc, Prod.fst_sub,
      Prod.snd_sub]
    ext <;> simp
  -- the polygon
  let P : Path (x : EuclideanSpace ℝ (Fin 4)) (x : EuclideanSpace ℝ (Fin 4)) :=
    { toFun := fun t => ∑ j ∈ Finset.range (N + 1), gcHat (N * (t : ℝ) - j) • v j
      continuous_toFun := by
        refine continuous_finsetSum _ fun j _ => ?_
        exact (continuous_gcHat.comp ((continuous_const.mul continuous_subtype_val).sub
          continuous_const)).smul continuous_const
      source' := by
        have := gc_sum_hat v (N := N) (i := 0) (by omega) le_rfl zero_le_one
        simp only [Nat.cast_zero, zero_add] at this
        simp only [Icc.coe_zero, mul_zero]
        rw [this]; simp [hv]
      target' := by
        have := gc_sum_hat v (N := N) (i := N - 1) (by omega) zero_le_one le_rfl
        rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.sub_add_cancel (by omega : 1 ≤ N)] at this
        simp only [Icc.coe_one, mul_one]
        push_cast at this
        rw [show (N : ℝ) = N - 1 + 1 by ring]
        rw [this]; simp [hv] }
  have hP : ∀ t : I, ∀ i : ℕ, i < N → ∀ r : ℝ, 0 ≤ r → r ≤ 1 → (N : ℝ) * t = i + r →
      P t = (1 - r) • v i + r • v (i + 1) := by
    intro t i hi r hr0 hr1 he
    show ∑ j ∈ Finset.range (N + 1), gcHat (N * (t : ℝ) - j) • v j = _
    rw [he]; exact gc_sum_hat v hi hr0 hr1
  -- the polygon is close to the loop
  have hPclose : ∀ t : I, ‖P t - (α t : EuclideanSpace ℝ (Fin 4))‖ ≤ 2 * ε := by
    intro t
    obtain ⟨i, hi, r, hr0, hr1, he⟩ := gc_exists_piece (by omega : 1 ≤ N) t
    have hvt : ∀ j, (j = i ∨ j = i + 1) →
        ‖v j - (α t : EuclideanSpace ℝ (Fin 4))‖ ≤ 2 * ε := by
      intro j hj
      have hjN : j ≤ N := by omega
      have hdt : dist (tN j) t < δ := by
        rw [Subtype.dist_eq, htN_le j hjN, Real.dist_eq]
        have ht : (t : ℝ) = (i + r) / N := by field_simp; linarith
        rw [ht, ← sub_div, abs_div, abs_of_pos hNpos, div_lt_iff₀ hNpos]
        rw [div_lt_iff₀ hNpos] at hNδ
        rcases hj with rfl | rfl
        · rw [abs_of_nonpos (by linarith)]; nlinarith
        · push_cast; rw [abs_of_nonneg (by linarith)]; nlinarith
      have h1 := hδα hdt
      rw [Subtype.dist_eq, dist_eq_norm] at h1
      calc ‖v j - (α t : EuclideanSpace ℝ (Fin 4))‖
          = ‖(v j - (α (tN j) : EuclideanSpace ℝ (Fin 4))) +
              ((α (tN j) : EuclideanSpace ℝ (Fin 4)) - α t)‖ := by congr 1; abel
        _ ≤ ε / 2 + ε := (norm_add_le _ _).trans (add_le_add (hv_close j) h1.le)
        _ ≤ 2 * ε := by linarith
    rw [hP t i hi r hr0 hr1 he]
    have e : (1 - r) • v i + r • v (i + 1) - (α t : EuclideanSpace ℝ (Fin 4)) =
        (1 - r) • (v i - α t) + r • (v (i + 1) - α t) := by
      rw [smul_sub, smul_sub, sub_add_sub_comm, ← add_smul]; simp
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith),
      abs_of_nonneg hr0]
    nlinarith [hvt i (Or.inl rfl), hvt (i + 1) (Or.inr rfl)]
  -- the polygon meets the plane of the great circle only at `x`
  have hPplane : ∀ t : I, P t 2 = 0 → P t 3 = 0 → P t = x := by
    intro t h2 h3
    obtain ⟨i, hi, r, hr0, hr1, he⟩ := gc_exists_piece (by omega : 1 ≤ N) t
    rw [hP t i hi r hr0 hr1 he] at h2 h3 ⊢
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at h2 h3
    by_cases hi0 : i = 0
    · subst hi0
      have hm : ¬ (1 = 0 ∨ N ≤ 1) := by omega
      have hp := hv_proj_mid 1 hm
      obtain ⟨e2, e3⟩ := hv_proj_end 0 (Or.inl rfl)
      rw [e2] at h2; rw [e3] at h3
      have e2' : v 1 2 = (u 1).1 := congrArg Prod.fst hp
      have e3' : v 1 3 = (u 1).2 := congrArg Prod.snd hp
      rw [e2'] at h2; rw [e3'] at h3
      obtain ⟨hr, -⟩ := gc_seg_avoid (a := 0) (hu_spec 1).1 (fun h => absurd rfl h)
        (by simpa using h2) (by simpa using h3)
      rw [hr]; simp [hv]
    by_cases hiN : i + 1 = N
    · have hm : ¬ (i = 0 ∨ N ≤ i) := by omega
      have hp := hv_proj_mid i hm
      obtain ⟨e2, e3⟩ := hv_proj_end (i + 1) (Or.inr hiN.ge)
      rw [e2] at h2; rw [e3] at h3
      have e2' : v i 2 = (u i).1 := congrArg Prod.fst hp
      have e3' : v i 3 = (u i).2 := congrArg Prod.snd hp
      rw [e2'] at h2; rw [e3'] at h3
      obtain ⟨hr, -⟩ := gc_seg_avoid (a := 0) (r := 1 - r) (hu_spec i).1 (fun h => absurd rfl h)
        (by simp only [Prod.fst_zero, mul_zero, zero_add]; linarith)
        (by simp only [Prod.snd_zero, mul_zero, zero_add]; linarith)
      rw [show r = 1 by linarith]; simp [hv, hiN]
    · have hm : ¬ (i = 0 ∨ N ≤ i) := by omega
      have hm' : ¬ (i + 1 = 0 ∨ N ≤ i + 1) := by omega
      have hp := hv_proj_mid i hm
      have hp' := hv_proj_mid (i + 1) hm'
      rw [show v i 2 = (u i).1 from congrArg Prod.fst hp,
        show v (i + 1) 2 = (u (i + 1)).1 from congrArg Prod.fst hp'] at h2
      rw [show v i 3 = (u i).2 from congrArg Prod.snd hp,
        show v (i + 1) 3 = (u (i + 1)).2 from congrArg Prod.snd hp'] at h3
      obtain ⟨-, h0⟩ := gc_seg_avoid (hu_spec (i + 1)).1 (fun _ => (hu_spec i).2) h2 h3
      exact absurd h0 (hu_spec i).1
  -- inner products
  have hαx : ∀ t, 3 / 4 < inner ℝ (α t : EuclideanSpace ℝ (Fin 4)) (x : EuclideanSpace ℝ (Fin 4)) :=
    fun t => hα t
  have hinner_le : ∀ w : EuclideanSpace ℝ (Fin 4),
      |inner ℝ w (x : EuclideanSpace ℝ (Fin 4))| ≤ ‖w‖ := fun w => by
    have := abs_real_inner_le_norm w (x : EuclideanSpace ℝ (Fin 4))
    rwa [mem_sphere_zero_iff_norm.1 x.2, mul_one] at this
  have hPx : ∀ t : I, 1 / 2 ≤ inner ℝ (P t) (x : EuclideanSpace ℝ (Fin 4)) := fun t => by
    have e : inner ℝ (P t) (x : EuclideanSpace ℝ (Fin 4)) =
        inner ℝ (α t : EuclideanSpace ℝ (Fin 4)) x +
          inner ℝ (P t - (α t : EuclideanSpace ℝ (Fin 4))) x := by
      rw [inner_sub_left]; ring
    have h1 := hinner_le (P t - (α t : EuclideanSpace ℝ (Fin 4)))
    rw [abs_le] at h1
    linarith [hαx t, hPclose t]
  have hFx : gcF x x = x := gcF_self x
  -- first homotopy: the loop to the polygon
  have H1 : HomotopicIn Kᶜ ((α.map continuous_subtype_val).map (continuous_gcF x))
      (P.map (continuous_gcF x)) := by
    refine gc_homotopicIn_map_line _ _ (continuous_gcF x) fun s t hK' => ?_
    set z := AffineMap.lineMap ((α.map continuous_subtype_val) t) (P t) (s : ℝ) with hz
    have hz' : z = (α t : EuclideanSpace ℝ (Fin 4)) +
        (s : ℝ) • (P t - (α t : EuclideanSpace ℝ (Fin 4))) := by
      rw [hz, AffineMap.lineMap_apply_module]
      simp only [Path.map_coe, Function.comp_apply]
      rw [smul_sub, sub_smul, one_smul]; abel
    have hzx : 1 / 2 ≤ inner ℝ z (x : EuclideanSpace ℝ (Fin 4)) := by
      rw [hz', inner_add_left, real_inner_smul_left]
      have h1 := hinner_le (P t - (α t : EuclideanSpace ℝ (Fin 4)))
      rw [abs_le] at h1
      have hs0 := s.2.1; have hs1 := s.2.2
      nlinarith [hαx t, hPclose t]
    have hzα : ‖z - (α t : EuclideanSpace ℝ (Fin 4))‖ ≤ 2 * ε := by
      rw [hz', add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg s.2.1]
      nlinarith [hPclose t, s.2.2, norm_nonneg (P t - (α t : EuclideanSpace ℝ (Fin 4)))]
    have := hdK t _ hK'
    have h2 := gcF_dist_le (y := α t) hzx
    rw [dist_comm] at this
    linarith
  -- second homotopy: the polygon to the constant loop (the cone on `x`)
  have H2 : HomotopicIn Kᶜ (P.map (continuous_gcF x))
      ((Path.refl (x : EuclideanSpace ℝ (Fin 4))).map (continuous_gcF x)) := by
    refine gc_homotopicIn_map_line _ _ (continuous_gcF x) fun s t hK' => ?_
    set z := AffineMap.lineMap (P t) ((Path.refl (x : EuclideanSpace ℝ (Fin 4))) t) (s : ℝ)
      with hz
    have hz2 : ∀ i : Fin 4, z i = (1 - s) * P t i + s * (x : EuclideanSpace ℝ (Fin 4)) i :=
      fun i => by rw [hz, gc_lineMap_apply]; rfl
    have hzx : 1 / 2 ≤ inner ℝ z (x : EuclideanSpace ℝ (Fin 4)) := by
      rw [hz, AffineMap.lineMap_apply_module, inner_add_left, real_inner_smul_left,
        real_inner_smul_left, Path.refl_apply, sphere3_inner_self]
      have := hPx t; have hs0 := s.2.1; have hs1 := s.2.2
      nlinarith
    obtain ⟨e2, e3⟩ := (gcF_mem_iff hzx).1 (hKΓ hK')
    rw [hz2, hx2] at e2; rw [hz2, hx3] at e3
    simp only [mul_zero, add_zero] at e2 e3
    have hzx' : z = x := by
      by_cases hs1 : (s : ℝ) = 1
      · rw [hz, hs1, AffineMap.lineMap_apply_one]; rfl
      · have hs' : (1 - (s : ℝ)) ≠ 0 := sub_ne_zero.2 (Ne.symm hs1)
        have h2 : P t 2 = 0 := (mul_eq_zero.1 e2).resolve_left hs'
        have h3 : P t 3 = 0 := (mul_eq_zero.1 e3).resolve_left hs'
        rw [hz, hPplane t h2 h3, Path.refl_apply, AffineMap.lineMap_same_apply]
    rw [hzx', hFx] at hK'
    exact hxK hK'
  have H := H1.trans H2
  refine (H.cast hFx.symm hFx.symm).of_eq ?_ ?_
  · refine Path.ext (funext fun t => ?_)
    simp only [Path.cast_coe, Path.map_coe, Function.comp_apply]
    exact gcF_sphere (by linarith [hαx t])
  · refine Path.ext (funext fun t => ?_)
    simp only [Path.cast_coe, Path.map_coe, Function.comp_apply, Path.refl_apply]
    exact hFx

/-- A Cantor subset of the great circle misses points of the great circle arbitrarily close to
any point of it. -/
theorem gc_exists_off {C : Set Sphere3} (hC : IsCantorSubset C) {x : Sphere3}
    (hx : x ∈ greatCircle3) {c : ℝ} (hc : c < 1) :
    ∃ p ∈ greatCircle3, p ∈ gcCap x c ∧ p ∉ C := by
  by_cases hxC : x ∉ C
  · exact ⟨x, hx, mem_gcCap_self hc, hxC⟩
  push Not at hxC
  obtain ⟨e⟩ := hC
  haveI : TotallyDisconnectedSpace C :=
    (e.trans cantorSetHomeomorphNatToBool).symm.totallyDisconnectedSpace
  have htd : IsTotallyDisconnected C := totallyDisconnectedSpace_subtype_iff.1 this
  set x₀ : EuclideanSpace ℝ (Fin 4) := (x : EuclideanSpace ℝ (Fin 4)) with hx₀def
  have hx₀x₀ : inner ℝ x₀ x₀ = 1 := sphere3_inner_self x
  set u := sphere3Perp x₀
  have hxu : inner ℝ x₀ u = 0 := inner_sphere3Perp_self x₀
  have huu : inner ℝ u u = 1 := by rw [inner_sphere3Perp_sphere3Perp, hx₀x₀]
  have hx2' : x₀ 2 = 0 := hx.1
  have hx3' : x₀ 3 = 0 := hx.2
  have hu2 : u 2 = 0 := by simp [u, sphere3Perp, hx3']
  have hu3 : u 3 = 0 := by simp [u, sphere3Perp, hx2']
  set f : ℝ → EuclideanSpace ℝ (Fin 4) := fun θ => Real.cos θ • x₀ + Real.sin θ • u with hfdef
  have hfu : ∀ θ, inner ℝ (f θ) u = Real.sin θ := fun θ => by
    simp only [hfdef, inner_add_left, real_inner_smul_left, hxu, huu]; ring
  have hfx : ∀ θ, inner ℝ (f θ) x₀ = Real.cos θ := fun θ => by
    simp only [hfdef, inner_add_left, real_inner_smul_left, hx₀x₀, real_inner_comm x₀ u, hxu]
    ring
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
  have hgΓ : ∀ θ, g θ ∈ greatCircle3 := fun θ => by
    refine ⟨?_, ?_⟩ <;> simp [g, hfdef, hu2, hu3, hx.1, hx.2, x₀]
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.1
    (hg.continuousAt.preimage_mem_nhds (hg0 ▸ (isOpen_gcCap x c).mem_nhds (mem_gcCap_self hc) :
      gcCap x c ∈ 𝓝 (g 0)))
  set s : ℝ := min (r / 2) 1 with hsdef
  have hs0 : 0 < s := lt_min (by linarith) one_pos
  have hsr : s < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hcap : ∀ θ ∈ Icc 0 s, g θ ∈ gcCap x c := fun θ hθ => hrsub (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    constructor <;> linarith [hθ.1, hθ.2])
  by_contra hne
  push Not at hne
  have hsub : g '' Icc 0 s ⊆ C := by
    rintro _ ⟨θ, hθ, rfl⟩
    exact hne _ (hgΓ θ) (hcap θ hθ)
  have hss := htd _ hsub (isPreconnected_Icc.image _ hg.continuousOn)
  have heq : g s = g 0 := hss ⟨s, ⟨hs0.le, le_rfl⟩, rfl⟩ ⟨0, ⟨le_rfl, hs0.le⟩, rfl⟩
  have h1 : inner ℝ (f s) u = inner ℝ (f 0) u := by
    have := congrArg (fun y : Sphere3 => inner ℝ (y : EuclideanSpace ℝ (Fin 4)) u) heq
    exact this
  rw [hfu, hfu, Real.sin_zero] at h1
  have : 0 < Real.sin s := Real.sin_pos_of_pos_of_lt_pi hs0
    (lt_of_le_of_lt (min_le_right _ _) (by linarith [Real.pi_gt_three]))
  linarith

/-- A small cap around `x` lies in the cap `⟨·, p⟩ > 3/4` around any of its points `p`. -/
theorem gcCap_subset_of_mem {x p : Sphere3} (hp : p ∈ gcCap x (999 / 1000)) :
    gcCap x (999 / 1000) ⊆ gcCap p (3 / 4) := by
  intro y hy
  have hsq : ‖(p : EuclideanSpace ℝ (Fin 4)) - x‖ ^ 2 < (1 / 10) ^ 2 := by
    rw [norm_sub_sq_real, mem_sphere_zero_iff_norm.1 p.2, mem_sphere_zero_iff_norm.1 x.2]
    have : (999 / 1000 : ℝ) < inner ℝ (p : EuclideanSpace ℝ (Fin 4)) (x : EuclideanSpace ℝ (Fin 4)) := hp
    nlinarith
  have hn : ‖(p : EuclideanSpace ℝ (Fin 4)) - x‖ < 1 / 10 :=
    lt_of_pow_lt_pow_left₀ 2 (by norm_num) hsq
  have h1 := abs_real_inner_le_norm (y : EuclideanSpace ℝ (Fin 4)) ((p : EuclideanSpace ℝ (Fin 4)) - x)
  rw [mem_sphere_zero_iff_norm.1 y.2, one_mul, abs_le] at h1
  change (3 / 4 : ℝ) < inner ℝ (y : EuclideanSpace ℝ (Fin 4)) (p : EuclideanSpace ℝ (Fin 4))
  have e : inner ℝ (y : EuclideanSpace ℝ (Fin 4)) (p : EuclideanSpace ℝ (Fin 4)) =
      inner ℝ (y : EuclideanSpace ℝ (Fin 4)) (x : EuclideanSpace ℝ (Fin 4)) +
        inner ℝ (y : EuclideanSpace ℝ (Fin 4)) ((p : EuclideanSpace ℝ (Fin 4)) - x) := by
    rw [inner_sub_right]; ring
  have hy' : (999 / 1000 : ℝ) < inner ℝ (y : EuclideanSpace ℝ (Fin 4)) (x : EuclideanSpace ℝ (Fin 4)) := hy
  linarith

theorem gc_homotopicIn_of_trans_symm {X : Type*} [TopologicalSpace X] {U : Set X} {a b : X}
    {ρ₁ ρ₂ : Path a b} (h₁ : ∀ t, ρ₁ t ∈ U) (h₂ : ∀ t, ρ₂ t ∈ U)
    (h : HomotopicIn U (ρ₁.trans ρ₂.symm) (Path.refl a)) : HomotopicIn U ρ₁ ρ₂ := by
  have ha : a ∈ U := ρ₁.source ▸ h₁ 0
  have hRa : ∀ t, (Path.refl a) t ∈ U := fun _ => ha
  rw [homotopicIn_iff_mk (path_trans_mem h₁ (path_symm_mem h₂)) hRa,
    pathToSub_trans _ _ h₁ (path_symm_mem h₂), pathToSub_symm _ h₂,
    Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm] at h
  have e1 : pathToSub (Path.refl a) hRa = Path.refl (⟨a, ha⟩ : U) := by ext; rfl
  rw [e1, Path.Homotopic.Quotient.mk_refl] at h
  rw [homotopicIn_iff_mk h₁ h₂]
  have h2 := congrArg (fun q => Path.Homotopic.Quotient.trans q
    (Path.Homotopic.Quotient.mk (pathToSub ρ₂ h₂))) h
  simp only [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.trans_refl, Path.Homotopic.Quotient.refl_trans] at h2
  exact h2

/-- **Paths in a small cap around a point of the great circle, off a Cantor subset `C` of it, are
homotopic in `S³ ∖ C`** (conjugate to a loop at a point of the great circle off `C`, then
`GX.gc_loop_null`). -/
theorem gc_paths_homotopicIn {C : Set Sphere3} (hC : IsCantorSubset C) (hCΓ : C ⊆ greatCircle3)
    {x : Sphere3} (hx : x ∈ greatCircle3) {a b : Sphere3} (ρ₁ ρ₂ : Path a b)
    (h₁ : ∀ t, ρ₁ t ∈ gcCap x (999 / 1000) ∧ ρ₁ t ∉ C)
    (h₂ : ∀ t, ρ₂ t ∈ gcCap x (999 / 1000) ∧ ρ₂ t ∉ C) : HomotopicIn Cᶜ ρ₁ ρ₂ := by
  obtain ⟨p, hpΓ, hpV, hpC⟩ := gc_exists_off hC hx (show (999 / 1000 : ℝ) < 1 by norm_num)
  have ha : a ∈ gcCap x (999 / 1000) ∧ a ∉ C := by simpa using h₁ 0
  obtain ⟨δ, hδ⟩ := gc_join hx (by norm_num) (by norm_num) hCΓ hpV ha.1 hpC ha.2
  set S : Set Sphere3 := gcCap x (999 / 1000) ∩ Cᶜ
  have hδS : ∀ t, δ t ∈ S := fun t => hδ t
  have h₁S : ∀ t, ρ₁ t ∈ S := fun t => h₁ t
  have h₂S : ∀ t, ρ₂ t ∈ S := fun t => h₂ t
  have hM : ∀ t, (ρ₁.trans ρ₂.symm) t ∈ S := path_trans_mem h₁S (path_symm_mem h₂S)
  have hL : ∀ t, ((δ.trans (ρ₁.trans ρ₂.symm)).trans δ.symm) t ∈ S :=
    path_trans_mem (path_trans_mem hδS hM) (path_symm_mem hδS)
  have hnull := gc_loop_null (IsCantorSubset.isClosed hC) hCΓ hpΓ hpC
    ((δ.trans (ρ₁.trans ρ₂.symm)).trans δ.symm) (fun t => gcCap_subset_of_mem hpV (hL t).1)
    (fun t => (hL t).2)
  have hδC : ∀ t, δ t ∈ Cᶜ := fun t => (hδ t).2
  have hMC : ∀ t, (ρ₁.trans ρ₂.symm) t ∈ Cᶜ := fun t => (hM t).2
  exact gc_homotopicIn_of_trans_symm (fun t => (h₁ t).2) (fun t => (h₂ t).2)
    (antoine_homotopicIn_conj hδC hMC hnull)

/-- **Tame Cantor sets.** The complement of a Cantor subset of a great circle of `S³` is
semi-locally simply connected in `S³`. -/
theorem tameCantorSLSC : TameCantorSLSC := by
  intro C hCΓ hC
  have hCc : IsClosed C := IsCantorSubset.isClosed hC
  refine ⟨dense_compl_of_isCantorSubset hC, fun x => ?_⟩
  by_cases hxC : x ∈ C
  · have hx : x ∈ greatCircle3 := hCΓ hxC
    refine ⟨gcCap x (999 / 1000), isOpen_gcCap x _, isPreconnected_gcCap x (by norm_num),
      mem_gcCap_self (by norm_num), fun γ hγ => ?_⟩
    have hγU : MemOmega Cᶜ γ := fun t h0 h1 => (hγ t h0 h1).2
    refine ⟨hγU, fun W hW => ?_⟩
    obtain ⟨c, hc0, hc1, hcW⟩ := exists_gcCap_subset hW (999 / 1000) (by norm_num)
    have hW' : gcCap x c ∈ 𝓝 x := (isOpen_gcCap x c).mem_nhds (mem_gcCap_self hc1)
    obtain ⟨t₀, h00, h0c, hhead⟩ := exists_head_mem γ hW' (c := 1 / 2) (by norm_num)
    obtain ⟨t₁, h1c, h11, htail⟩ := exists_tail_mem γ hW' (c := 1 / 2) (by norm_num)
    have h01 : (t₀ : ℝ) < t₁ := by linarith
    have ha : γ t₀ ∈ gcCap x c := hhead t₀ le_rfl
    have hb : γ t₁ ∈ gcCap x c := htail t₁ le_rfl
    have haC : γ t₀ ∉ C := hγU t₀ h00 (by linarith)
    have hbC : γ t₁ ∉ C := hγU t₁ (by linarith) h11
    obtain ⟨ω, hω⟩ := gc_join hx (by linarith) hc1 hCΓ ha hb haC hbC
    have hsub : ∀ t, subpath γ t₀ t₁ t ∈ gcCap x (999 / 1000) ∧ subpath γ t₀ t₁ t ∉ C :=
      fun t => by
        obtain ⟨s, hs1, hs2, hs⟩ := subpath_mem γ t₀ t₁ t
        rw [min_eq_left h01.le] at hs1
        rw [max_eq_right h01.le] at hs2
        rw [hs]
        exact hγ s (by linarith) (by linarith)
    have hωV : ∀ t, ω t ∈ gcCap x (999 / 1000) ∧ ω t ∉ C :=
      fun t => ⟨gcCap_mono hc0 (hω t).1, (hω t).2⟩
    refine ⟨splice γ t₀ t₁ h01 ω, fun t ht0 ht1 => ?_, splice_omegaHomotopic hγU h01 h11
      (gc_paths_homotopicIn hC hCΓ hx _ _ hsub hωV)⟩
    rcases splice_mem γ h01 ω t with ⟨hle, he⟩ | ⟨hge, he⟩ | ⟨s, hs⟩
    · rw [he]; exact ⟨hcW (hhead t hle), hγU t ht0 ht1⟩
    · rw [he]; exact ⟨hcW (htail t hge), hγU t ht0 ht1⟩
    · rw [← hs]; exact ⟨hcW (hω s).1, (hω s).2⟩
  · obtain ⟨c, hc0, hc1, hcW⟩ := exists_gcCap_subset (hCc.isOpen_compl.mem_nhds hxC) (1 / 2)
      (by norm_num)
    refine ⟨gcCap x c, isOpen_gcCap x _, isPreconnected_gcCap x hc0, mem_gcCap_self hc1,
      fun γ hγ => ?_⟩
    have hγV : ∀ t, γ t ∈ gcCap x c := fun t => by
      rcases eq_or_lt_of_le t.2.1 with h0 | h0
      · rw [show t = 0 from Subtype.ext h0.symm, γ.source]; exact mem_gcCap_self hc1
      rcases eq_or_lt_of_le t.2.2 with h1 | h1
      · rw [show t = 1 from Subtype.ext h1, γ.target]; exact mem_gcCap_self hc1
      exact (hγ t h0 h1).1
    refine ⟨fun t h0 h1 => (hγ t h0 h1).2, fun W hW => ⟨Path.refl x,
      fun _ _ _ => ⟨mem_of_mem_nhds hW, hxC⟩, ?_⟩⟩
    exact ((gcCap_homotopicIn hc0 γ (Path.refl x) hγV fun _ => mem_gcCap_self hc1).mono
      hcW).omegaHomotopic

/-- Wildness of the necklace from a tame-Cantor fact: it follows from the
non-semi-local-simple-connectedness of its complement, the homeomorphism invariance
`GX.IsSLSCIn.map_homeomorph`, and `GX.TameCantorSLSC` (an argument here; it is proved,
`GX.tameCantorSLSC`, and discharged in `GX.isWildCantor_antoineNecklace_of_res`). -/
theorem isWildCantor_antoineNecklace_of (hres : AntoineMeridianEssential)
    (htame : TameCantorSLSC) : IsWildCantor antoineNecklace := by
  refine ⟨antoineNecklace_isCantorSubset, fun ⟨h, hsub⟩ => antoineNecklace_not_isSLSCIn_of hres ?_⟩
  have hC : IsCantorSubset (h '' antoineNecklace) := by
    obtain ⟨e⟩ := antoineNecklace_isCantorSubset
    exact ⟨(h.image antoineNecklace).symm.trans e⟩
  have := (htame _ hsub hC).map_homeomorph h.symm
  rwa [← image_compl_eq h.bijective, ← image_comp, h.symm_comp_self, image_id] at this

/-- **Antoine's necklace is WILD** (DEC-82), FROM THE RESIDUAL ALONE (sorry-free): no
homeomorphism of `S³` carries it into a great circle, because the complement of a Cantor subset
of a great circle is semi-locally simply connected (`GX.tameCantorSLSC`, proved) while the
necklace's is not (`GX.antoineNecklace_not_isSLSCIn_of`). -/
theorem isWildCantor_antoineNecklace_of_res (hres : AntoineMeridianEssential) :
    IsWildCantor antoineNecklace :=
  isWildCantor_antoineNecklace_of hres tameCantorSLSC

/-- Antoine's necklace is wild; rests on `GX.antoineChainEssential` (via
`GX.antoineMeridianEssentialTop`). -/
theorem isWildCantor_antoineNecklace : IsWildCantor antoineNecklace :=
  isWildCantor_antoineNecklace_of_res antoineMeridianEssential

/-- The point `(cos t, sin t, 0, 0)` of the great circle `GX.greatCircle3`. -/
def standardCirclePt (t : ℝ) : Sphere3 :=
  ⟨!₂[Real.cos t, Real.sin t, 0, 0], by
    rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Real.sqrt_eq_one, Fin.sum_univ_four]
    simp [Real.cos_sq_add_sin_sq]⟩

theorem continuous_standardCirclePt : Continuous standardCirclePt := by
  refine Continuous.subtype_mk ((PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)) _
  fin_cases i <;> simp <;> fun_prop

/-- **The standard (tame) Cantor set of `S³`**: the middle-third Cantor set of `[0, 1]`, wrapped
on the great circle by `t ↦ (cos t, sin t, 0, 0)`. -/
def standardCantor3 : Set Sphere3 := standardCirclePt '' cantorSet

theorem standardCantor3_subset : standardCantor3 ⊆ greatCircle3 := by
  rintro _ ⟨t, -, rfl⟩
  exact ⟨by simp [standardCirclePt], by simp [standardCirclePt]⟩

theorem standardCirclePt_injOn : InjOn standardCirclePt cantorSet := by
  intro a ha b hb h
  have h0 := congrArg (fun y : Sphere3 => (y : EuclideanSpace ℝ (Fin 4)) 0) h
  simp only [standardCirclePt] at h0
  simp at h0
  have hI : ∀ x ∈ cantorSet, x ∈ Icc 0 Real.pi := fun x hx =>
    ⟨(cantorSet_subset_unitInterval hx).1,
      (cantorSet_subset_unitInterval hx).2.trans (by linarith [Real.pi_gt_three])⟩
  exact Real.injOn_cos (hI a ha) (hI b hb) h0

theorem standardCantor3_isCantorSubset : IsCantorSubset standardCantor3 := by
  haveI : CompactSpace cantorSet := isCompact_iff_compactSpace.1 isCompact_cantorSet
  exact ⟨(Continuous.homeoOfEquivCompactToT2
    (f := Equiv.Set.imageOfInjOn standardCirclePt cantorSet standardCirclePt_injOn)
    ((continuous_standardCirclePt.comp continuous_subtype_val).subtype_mk _)).symm⟩

/-- **Antoine's necklace is not tame in the classical sense** (from the residual alone,
sorry-free): no homeomorphism of `S³` carries it onto the standard Cantor set. (Classically tame
means ambiently homeomorphic to `GX.standardCantor3`; `GX.IsWildCantor` is the stronger
"carried INTO no great circle".) -/
theorem antoineNecklace_not_tame_of (hres : AntoineMeridianEssential) :
    ¬ ∃ h : Sphere3 ≃ₜ Sphere3, h '' antoineNecklace = standardCantor3 := by
  rintro ⟨h, e⟩
  exact (isWildCantor_antoineNecklace_of_res hres).2 ⟨h, e ▸ standardCantor3_subset⟩

/-- Antoine's necklace is not tame; rests on `GX.antoineChainEssential` (via
`GX.antoineMeridianEssentialTop`). -/
theorem antoineNecklace_not_tame :
    ¬ ∃ h : Sphere3 ≃ₜ Sphere3, h '' antoineNecklace = standardCantor3 :=
  antoineNecklace_not_tame_of antoineMeridianEssential

/-- The existential corollary: some wild Cantor set of `S³` (Antoine's necklace) has a
complement that is not semi-locally simply connected. -/
theorem exists_wild_cantor_not_isSLSCIn :
    ∃ C : Set Sphere3, IsWildCantor C ∧ ¬ IsSLSCIn Cᶜ :=
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

/-- For a closed `C ⊆ S³`, the literal (DEC-55) and homotopy forms of semi-local simple
connectedness of `S³ ∖ C` in `S³` agree. -/
theorem sphere3_isSLSCInCC_compl_iff {C : Set Sphere3} (hC : IsClosed C) :
    IsSLSCInCC Cᶜ ↔ IsSLSCIn Cᶜ :=
  haveI := sphere3_locPathConnected
  isSLSCInCC_iff hC.isOpen_compl (sphere3_semilocallySimplyConnected_compl hC)

/-- `ex:wild_cantor_general_antoine` (`RamcovGX.tex:1578`, DEC-58 and DEC-68 (f): `S` is
the explicit Antoine necklace), literal reading (DEC-55), FROM THE RESIDUAL ALONE (sorry-free):
the complement of `GX.antoineNecklace` is not semi-locally simply connected in `S³`. -/
theorem antoineNecklace_not_isSLSCInCC_of (hres : AntoineMeridianEssential) :
    ¬ IsSLSCInCC antoineNecklaceᶜ := fun hcc => antoineNecklace_not_isSLSCIn_of hres
  ((sphere3_isSLSCInCC_compl_iff antoineNecklace_isCantorSubset.isClosed).1 hcc)

/-- `ex:wild_cantor_general_antoine`, literal reading; rests on `GX.antoineChainEssential` (via
`GX.antoineMeridianEssentialTop`). -/
theorem antoineNecklace_not_isSLSCInCC : ¬ IsSLSCInCC antoineNecklaceᶜ :=
  antoineNecklace_not_isSLSCInCC_of antoineMeridianEssential

/-- `ex:wild_cantor_general_antoine` with the wildness, FROM THE RESIDUAL ALONE
(sorry-free): Antoine's necklace is a wild Cantor set of `S³` whose complement is not
semi-locally simply connected (literal reading). -/
theorem antoineNecklace_wild_not_isSLSCInCC_of (hres : AntoineMeridianEssential) :
    IsWildCantor antoineNecklace ∧ ¬ IsSLSCInCC antoineNecklaceᶜ :=
  ⟨isWildCantor_antoineNecklace_of_res hres, antoineNecklace_not_isSLSCInCC_of hres⟩

/-- `ex:wild_cantor_general_antoine` with the wildness, from Antoine's lemma for the top link
`GX.AntoineMeridianEssentialTop` alone (sorry-free). -/
theorem antoineNecklace_wild_not_isSLSCInCC_of_top (h : AntoineMeridianEssentialTop) :
    IsWildCantor antoineNecklace ∧ ¬ IsSLSCInCC antoineNecklaceᶜ :=
  antoineNecklace_wild_not_isSLSCInCC_of (antoineMeridianEssential_of_top h)

/-- Antoine's necklace is a wild Cantor set of `S³` whose complement is not semi-locally simply
connected (literal reading); rests on `GX.antoineChainEssential` (via
`GX.antoineMeridianEssentialTop`). -/
theorem antoineNecklace_wild_not_isSLSCInCC :
    IsWildCantor antoineNecklace ∧ ¬ IsSLSCInCC antoineNecklaceᶜ :=
  antoineNecklace_wild_not_isSLSCInCC_of antoineMeridianEssential

/-- The existential corollary of `GX.antoineNecklace_wild_not_isSLSCInCC` (literal reading). -/
theorem exists_wild_cantor_not_isSLSCInCC :
    ∃ C : Set Sphere3, IsWildCantor C ∧ ¬ IsSLSCInCC Cᶜ :=
  ⟨_, antoineNecklace_wild_not_isSLSCInCC⟩

end WildCantor

/-! ### `ex:consider_denote_absolute_galois`, corrected (DEC-69): the Cantor fibre

With `aₙ = 1/(n+1)` and `sₙ` a continuous square root of `p - aₙ` on `\widetilde{ℂ∖S}`, deck
transformations act on `sₙ` by signs `εₙ = (-1)^{winding around aₙ}`; `Γ₂'` is their common kernel.
Over `D_k` the sign `σₙ = sₙ / i√(aₙ - z)`, `n < k`, is locally constant, and two points of
`Γ₂' \ \widetilde{ℂ∖S}` over `D_k` lie in the same component iff they have the same `σₙ`, `n < k`
(`GX.cantZ_comp`; the hard half realises every eventually constant sign pattern by small circles
around the `aₙ`, `n ≥ k`, and the circle of radius `R_k` around `0`, all inside `D_k`). So the ends
over `0` are the sign sequences, `GX.cantFiberHomeo : {0,1}^ℕ ≃ₜ fibre`. -/

section CantorFibre

attribute [local instance] absGal_locPath
attribute [local instance] absGal_simplyConnected

variable (y₀ : (fibSᶜ : Set ℂ))

/-- The point `aₙ = 1/(n+1)` of `S`. -/
def cantPt (n : ℕ) : ℂ := ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)

theorem cantPt_mem (n : ℕ) : cantPt n ∈ fibS := fibPt_mem n

/-- `p - aₙ`, into `ℂ ∖ {0}`. -/
def cantSubC (n : ℕ) : C(AbsU y₀, CStar) :=
  (subFib _ (cantPt_mem n)).comp ⟨UniversalCover.proj _ y₀, UniversalCover.continuous_proj⟩

theorem cant_exists_ℓ (n : ℕ) :
    ∃ ℓ : C(AbsU y₀, ℂ), ∀ c, Complex.exp (ℓ c) = absP y₀ c - cantPt n := by
  obtain ⟨ℓ, ⟨-, hℓ⟩, -⟩ := isCoveringMap_cExp.existsUnique_continuousMap_lifts (cantSubC y₀ n)
    (UniversalCover.base y₀) (Complex.log (cantSubC y₀ n (UniversalCover.base y₀)))
    (Subtype.ext (Complex.exp_log (cantSubC y₀ n _).2))
  exact ⟨ℓ, fun c => congrArg Subtype.val (congrFun hℓ c)⟩

/-- A continuous logarithm of `p - aₙ` on `\widetilde{ℂ∖S}`. -/
def cantℓ (n : ℕ) : C(AbsU y₀, ℂ) := (cant_exists_ℓ y₀ n).choose

theorem cantℓ_spec (n : ℕ) (c : AbsU y₀) : Complex.exp (cantℓ y₀ n c) = absP y₀ c - cantPt n :=
  (cant_exists_ℓ y₀ n).choose_spec c

/-- The continuous square root `sₙ = exp(ℓₙ/2)` of `p - aₙ`. -/
def cantSq (n : ℕ) (c : AbsU y₀) : ℂ := Complex.exp (cantℓ y₀ n c / 2)

theorem continuous_cantSq (n : ℕ) : Continuous (cantSq y₀ n) := by
  unfold cantSq; fun_prop

theorem cantSq_sq (n : ℕ) (c : AbsU y₀) : cantSq y₀ n c ^ 2 = absP y₀ c - cantPt n := by
  rw [cantSq, sq, ← Complex.exp_add, add_halves, cantℓ_spec]

theorem cantSq_ne_zero (n : ℕ) (c : AbsU y₀) : cantSq y₀ n c ≠ 0 := Complex.exp_ne_zero _

section Deck

variable {y₀} (φ : AbsU y₀ ≃ₜ AbsU y₀) (hφ : ∀ c, absP y₀ (φ c) = absP y₀ c)

/-- The sign `±1` by which a deck transformation acts on `sₙ`. -/
def cantSign (n : ℕ) : ℂ :=
  Complex.exp ((cantℓ y₀ n (φ (UniversalCover.base y₀)) - cantℓ y₀ n (UniversalCover.base y₀)) / 2)

include hφ in
theorem cantSq_deck (n : ℕ) (c : AbsU y₀) : cantSq y₀ n (φ c) = cantSign φ n * cantSq y₀ n c := by
  have := absGal_expLift_eq (cantℓ y₀ n).continuous ((cantℓ y₀ n).continuous.comp φ.continuous)
    (fun a => by simp only [comp_apply, cantℓ_spec, hφ]) (UniversalCover.base y₀) c
  simp only [comp_apply] at this
  rw [cantSq, this, add_div, Complex.exp_add, cantSign, cantSq, mul_comm]

end Deck

/-- `εₙ(g)`: the sign by which the deck transformation of `g ∈ π₁(ℂ ∖ S)` acts on `sₙ`. -/
def cantEps (n : ℕ) (g : AbsGamma y₀) : ℂ := cantSign (UniversalCover.deckHom g).1 n

theorem cantSq_deckHom (n : ℕ) (g : AbsGamma y₀) (c : AbsU y₀) :
    cantSq y₀ n ((UniversalCover.deckHom g).1 c) = cantEps y₀ n g * cantSq y₀ n c :=
  cantSq_deck _ (absP_deckHom y₀ g) n c

theorem cantEps_mul (n : ℕ) (a b : AbsGamma y₀) :
    cantEps y₀ n (a * b) = cantEps y₀ n a * cantEps y₀ n b := by
  have h := cantSq_deckHom y₀ n (a * b) (UniversalCover.base y₀)
  rw [map_mul] at h
  have h2 : cantSq y₀ n ((UniversalCover.deckHom a).1 ((UniversalCover.deckHom b).1
      (UniversalCover.base y₀))) = cantEps y₀ n a * (cantEps y₀ n b *
        cantSq y₀ n (UniversalCover.base y₀)) := by
    rw [cantSq_deckHom, cantSq_deckHom]
  have h3 : cantSq y₀ n (((UniversalCover.deckHom a) * (UniversalCover.deckHom b)).1
      (UniversalCover.base y₀)) = cantSq y₀ n ((UniversalCover.deckHom a).1
        ((UniversalCover.deckHom b).1 (UniversalCover.base y₀))) := rfl
  rw [h3, h2] at h
  have hne := cantSq_ne_zero y₀ n (UniversalCover.base y₀)
  have : (cantEps y₀ n (a * b) - cantEps y₀ n a * cantEps y₀ n b) *
      cantSq y₀ n (UniversalCover.base y₀) = 0 := by linear_combination -h
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hne)

theorem cantEps_one (n : ℕ) : cantEps y₀ n 1 = 1 := by
  have h := cantSq_deckHom y₀ n 1 (UniversalCover.base y₀)
  rw [map_one] at h
  change cantSq y₀ n (UniversalCover.base y₀) = _ at h
  have hne := cantSq_ne_zero y₀ n (UniversalCover.base y₀)
  have : (cantEps y₀ n 1 - 1) * cantSq y₀ n (UniversalCover.base y₀) = 0 := by
    linear_combination -h
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hne)

theorem cantEps_sq (n : ℕ) (g : AbsGamma y₀) : cantEps y₀ n g ^ 2 = 1 := by
  have h := cantSq_deckHom y₀ n g (UniversalCover.base y₀)
  have h2 := congrArg (· ^ 2) h
  simp only [mul_pow, cantSq_sq, absP_deckHom] at h2
  have hne : absP y₀ (UniversalCover.base y₀) - cantPt n ≠ 0 :=
    sub_ne_zero.2 fun e => absP_not_mem y₀ _ (e ▸ cantPt_mem n)
  have : (cantEps y₀ n g ^ 2 - 1) * (absP y₀ (UniversalCover.base y₀) - cantPt n) = 0 := by
    linear_combination -h2
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hne)

theorem cantEps_eq (n : ℕ) (g : AbsGamma y₀) : cantEps y₀ n g = 1 ∨ cantEps y₀ n g = -1 := by
  have := cantEps_sq y₀ n g
  rw [sq] at this
  exact mul_self_eq_one_iff.1 this

theorem cantEps_inv (n : ℕ) (g : AbsGamma y₀) : cantEps y₀ n g⁻¹ = cantEps y₀ n g := by
  have h := cantEps_mul y₀ n g g⁻¹
  rw [mul_inv_cancel, cantEps_one] at h
  rcases cantEps_eq y₀ n g with e | e <;> rw [e] at h ⊢
  · simpa using h.symm
  · have : cantEps y₀ n g⁻¹ = -1 := by linear_combination h
    exact this

/-- **`Γ₂'`, the corrected subgroup of `ex:consider_denote_absolute_galois` (DEC-69)**: the kernel
of the mod-2 windings around the points `1/n` (`GX.mem_cantGamma_iff`), i.e. the deck
transformations fixing every square root `sₙ`. -/
def cantGamma : Subgroup (AbsGamma y₀) where
  carrier := {g | ∀ n, cantEps y₀ n g = 1}
  one_mem' := fun n => cantEps_one y₀ n
  mul_mem' := by
    intro a b ha hb n
    show cantEps y₀ n (a * b) = 1
    rw [cantEps_mul, ha n, hb n, one_mul]
  inv_mem' := by
    intro a ha n
    show cantEps y₀ n a⁻¹ = 1
    rw [cantEps_inv]; exact ha n

theorem mem_cantGamma {g : AbsGamma y₀} : g ∈ cantGamma y₀ ↔ ∀ n, cantEps y₀ n g = 1 := Iff.rfl

/-- Along the canonical lift `L` of a loop `δ` of `ℂ ∖ S`, `sₙ` changes by `(-1)^w`, `w` the
winding number of `δ` around `aₙ`. -/
theorem cantSq_liftFrom_loop {b : (fibSᶜ : Set ℂ)} (c : Path.Homotopic.Quotient y₀ b)
    (δ : Path b b) (n : ℕ) :
    cantSq y₀ n (UniversalCover.liftFrom c δ 1) =
      (-1 : ℂ) ^ cWinding (δ.map (subFib _ (cantPt_mem n)).continuous) *
        cantSq y₀ n (UniversalCover.liftFrom c δ 0) := by
  set L := UniversalCover.liftFrom c δ
  have hL : ∀ t, Complex.exp ((cantℓ y₀ n).comp ⟨L, L.continuous⟩ t) =
      (δ.map (subFib _ (cantPt_mem n)).continuous) t := fun t => by
    show Complex.exp (cantℓ y₀ n (L t)) = ((δ t : ℂ) - cantPt n)
    rw [cantℓ_spec]; rfl
  have e := cWinding_spec _ hL
  simp only [ContinuousMap.coe_comp, ContinuousMap.coe_mk, comp_apply] at e
  rw [cantSq, cantSq, e, add_div, Complex.exp_add, mul_comm]
  congr 1
  rw [show (cWinding (δ.map (subFib _ (cantPt_mem n)).continuous) : ℂ) * (2 * Real.pi * Complex.I) / 2
      = (cWinding (δ.map (subFib _ (cantPt_mem n)).continuous) : ℂ) * (Real.pi * Complex.I) by ring,
    Complex.exp_int_mul, Complex.exp_pi_mul_I]

theorem cant_neg_one_zpow_neg (w : ℤ) : (-1 : ℂ) ^ (-w) = (-1 : ℂ) ^ w := by
  rw [zpow_neg]
  rcases Int.even_or_odd w with h | h
  · rw [h.neg_one_zpow, inv_one]
  · rw [h.neg_one_zpow]; norm_num

/-- `εₙ([γ]) = (-1)^{w(γ, aₙ)}`. -/
theorem cantEps_fromPath (n : ℕ) (γ : Path y₀ y₀) :
    cantEps y₀ n (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) =
      (-1 : ℂ) ^ windAt y₀ _ (cantPt_mem n) γ := by
  have h := cantSq_deckHom y₀ n (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ))
    (UniversalCover.base y₀)
  rw [absGal_deckHom_base, cantSq_liftFrom_loop, absGal_cWinding_symm] at h
  have h0 : UniversalCover.liftFrom (Path.Homotopic.Quotient.refl y₀) γ.symm 0 =
      UniversalCover.base y₀ := (UniversalCover.liftFrom _ γ.symm).source
  rw [h0, cant_neg_one_zpow_neg] at h
  have hne := cantSq_ne_zero y₀ n (UniversalCover.base y₀)
  have : ((-1 : ℂ) ^ windAt y₀ _ (cantPt_mem n) γ -
      cantEps y₀ n (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ))) *
      cantSq y₀ n (UniversalCover.base y₀) = 0 := by
    unfold windAt; linear_combination h
  exact (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hne)).symm

theorem cant_neg_one_zpow_eq_one_iff (w : ℤ) : (-1 : ℂ) ^ w = 1 ↔ Even w := by
  rcases Int.even_or_odd w with h | h
  · simp [h.neg_one_zpow, h]
  · rw [h.neg_one_zpow]
    simp only [Int.not_even_iff_odd.2 h, iff_false]
    norm_num

/-- **`Γ₂'` is the kernel of the mod-2 windings**: a loop class lies in `Γ₂'` iff the loop winds
an even number of times around every point `1/n` of `S`. -/
theorem mem_cantGamma_iff (γ : Path y₀ y₀) :
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ) ∈ cantGamma y₀ ↔
      ∀ n, Even (windAt y₀ _ (cantPt_mem n) γ) := by
  simp only [mem_cantGamma, cantEps_fromPath, cant_neg_one_zpow_eq_one_iff]


/-! #### The signs near `0` -/

/-- A branch `rₙ(z) = i·√(aₙ - z)` of the square root of `z - aₙ`, continuous on `Re z < aₙ`. -/
def cantRoot (n : ℕ) (z : ℂ) : ℂ := Complex.I * Complex.exp (Complex.log (cantPt n - z) / 2)

theorem cantPt_re (n : ℕ) : (cantPt n).re = 1 / ((n : ℝ) + 1) := by rw [cantPt, Complex.ofReal_re]

theorem cantRoot_sq {n : ℕ} {z : ℂ} (hz : cantPt n - z ≠ 0) : cantRoot n z ^ 2 = z - cantPt n := by
  rw [cantRoot, mul_pow, Complex.I_sq, sq (Complex.exp _), ← Complex.exp_add, add_halves,
    Complex.exp_log hz]
  ring

theorem cant_slit {n : ℕ} {z : ℂ} (hz : z.re < 1 / ((n : ℝ) + 1)) :
    cantPt n - z ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.2 (Or.inl (by rw [Complex.sub_re, cantPt_re]; linarith))

theorem continuousAt_cantRoot {n : ℕ} {z : ℂ} (hz : z.re < 1 / ((n : ℝ) + 1)) :
    ContinuousAt (cantRoot n) z := by
  unfold cantRoot
  exact continuousAt_const.mul
    (((continuousAt_const.sub continuousAt_id).clog (cant_slit hz)).div_const 2).cexp

/-- The sign `σₙ = sₙ / rₙ(p)`, equal to `±1` over `Re z < aₙ`. -/
def cantSigma (n : ℕ) (c : AbsU y₀) : ℂ := cantSq y₀ n c / cantRoot n (absP y₀ c)

theorem cantSigma_eq {n : ℕ} {c : AbsU y₀} (hc : (absP y₀ c).re < 1 / ((n : ℝ) + 1)) :
    cantSigma y₀ n c = 1 ∨ cantSigma y₀ n c = -1 := by
  have hne : cantPt n - absP y₀ c ≠ 0 := Complex.slitPlane_ne_zero (cant_slit hc)
  have hne' : absP y₀ c - cantPt n ≠ 0 := fun h => hne (by linear_combination -h)
  have hr : cantRoot n (absP y₀ c) ≠ 0 := fun h => by
    have := cantRoot_sq hne; rw [h] at this; exact hne' (by rw [← this]; ring)
  have : cantSigma y₀ n c ^ 2 = 1 := by
    rw [cantSigma, div_pow, cantSq_sq, cantRoot_sq hne, div_self hne']
  rw [sq] at this
  exact mul_self_eq_one_iff.1 this

theorem cantSigma_deckHom (n : ℕ) (g : AbsGamma y₀) (c : AbsU y₀) :
    cantSigma y₀ n ((UniversalCover.deckHom g).1 c) = cantEps y₀ n g * cantSigma y₀ n c := by
  rw [cantSigma, cantSigma, cantSq_deckHom, absP_deckHom, mul_div_assoc]

theorem cantSigma_eventually {n : ℕ} {c₀ : AbsU y₀} (hc : (absP y₀ c₀).re < 1 / ((n : ℝ) + 1)) :
    ∀ᶠ c in 𝓝 c₀, cantSigma y₀ n c = cantSigma y₀ n c₀ := by
  have hne : cantPt n - absP y₀ c₀ ≠ 0 := Complex.slitPlane_ne_zero (cant_slit hc)
  have hne' : absP y₀ c₀ - cantPt n ≠ 0 := fun h => hne (by linear_combination -h)
  have hr : cantRoot n (absP y₀ c₀) ≠ 0 := fun h => by
    have := cantRoot_sq hne; rw [h] at this; exact hne' (by rw [← this]; ring)
  have hcont : ContinuousAt (cantSigma y₀ n) c₀ :=
    (continuous_cantSq y₀ n).continuousAt.div
      ((continuousAt_cantRoot hc).comp (continuous_absP y₀).continuousAt) hr
  have hV : ∀ᶠ c in 𝓝 c₀, (absP y₀ c).re < 1 / ((n : ℝ) + 1) :=
    ((Complex.continuous_re.comp (continuous_absP y₀)).tendsto c₀).eventually (eventually_lt_nhds hc)
  filter_upwards [hV, hcont.eventually (Metric.ball_mem_nhds _ one_pos)] with c hc' hd
  rcases cantSigma_eq y₀ hc with h0 | h0 <;> rcases cantSigma_eq y₀ hc' with h1 | h1 <;>
    simp only [h0, h1] at hd ⊢ <;> norm_num [Complex.dist_eq] at hd

/-- The bit `σₙ = 1`. -/
def cantBit (n : ℕ) (c : AbsU y₀) : Bool := decide (cantSigma y₀ n c = 1)

theorem cant_re_lt_of_mem_fibD {n k : ℕ} (hnk : n < k) {z : ℂ} (hz : z ∈ fibD k) :
    z.re < 1 / ((n : ℝ) + 1) := by
  rw [fibD, Metric.mem_ball, dist_zero_right] at hz
  have h1 : z.re ≤ ‖z‖ := Complex.re_le_norm z
  have h2 : 1 / ((k : ℝ) + 1 / 2) ≤ 1 / ((n : ℝ) + 1) := by
    have : (n : ℝ) + 1 ≤ k := by exact_mod_cast hnk
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  linarith

theorem cant_isOpen_level {n k : ℕ} (hnk : n < k) (b : Bool) :
    IsOpen {c : AbsU y₀ | absP y₀ c ∈ fibD k ∧ cantBit y₀ n c = b} := by
  rw [isOpen_iff_mem_nhds]
  rintro c₀ ⟨hc₀, hb⟩
  filter_upwards [cantSigma_eventually y₀ (cant_re_lt_of_mem_fibD hnk hc₀),
    (continuous_absP y₀).continuousAt.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds hc₀)]
    with c hc hD
  exact ⟨hD, by rw [← hb, cantBit, cantBit, hc]⟩

/-- A `Bool`-valued function with open level sets over an open set is constant on its
preconnected subsets. -/
theorem cant_const_of_isOpen_level {Z : Type*} [TopologicalSpace Z] {A : Set Z} {f : Z → Bool}
    (h : ∀ b, IsOpen {x | x ∈ A ∧ f x = b}) {s : Set Z} (hs : IsPreconnected s) (hsA : s ⊆ A)
    {x y : Z} (hx : x ∈ s) (hy : y ∈ s) : f y = f x := by
  have := GX.IsPreconnected.subset_of_pairwise_disjoint (T := fun b => {x | x ∈ A ∧ f x = b}) h
    (fun i j hij => by
      rw [Function.onFun, Set.disjoint_left]
      rintro z ⟨-, hi⟩ ⟨-, hj⟩
      exact hij (hi.symm.trans hj)) hs (fun z hz => mem_iUnion.2 ⟨f z, hsA hz, rfl⟩)
    (j := f x) ⟨x, hx, hsA hx, rfl⟩
  exact (this hy).2

theorem cantBit_const {n k : ℕ} (hnk : n < k) {s : Set (AbsU y₀)} (hs : IsPreconnected s)
    (hsk : s ⊆ absP y₀ ⁻¹' fibD k) {x y : AbsU y₀} (hx : x ∈ s) (hy : y ∈ s) :
    cantBit y₀ n y = cantBit y₀ n x :=
  cant_const_of_isOpen_level (A := absP y₀ ⁻¹' fibD k) (fun b => cant_isOpen_level y₀ hnk b) hs hsk
    hx hy

theorem cantSigma_eq_of_bit {n : ℕ} {c c' : AbsU y₀} (hc : (absP y₀ c).re < 1 / ((n : ℝ) + 1))
    (hc' : (absP y₀ c').re < 1 / ((n : ℝ) + 1)) (h : cantBit y₀ n c' = cantBit y₀ n c) :
    cantSigma y₀ n c' = cantSigma y₀ n c := by
  unfold cantBit at h
  rcases cantSigma_eq y₀ hc with h0 | h0 <;> rcases cantSigma_eq y₀ hc' with h1 | h1 <;>
    simp only [h0, h1] at h ⊢ <;> norm_num at h

theorem cantSigma_const {n k : ℕ} (hnk : n < k) {s : Set (AbsU y₀)} (hs : IsPreconnected s)
    (hsk : s ⊆ absP y₀ ⁻¹' fibD k) {x y : AbsU y₀} (hx : x ∈ s) (hy : y ∈ s) :
    cantSigma y₀ n y = cantSigma y₀ n x :=
  cantSigma_eq_of_bit y₀ (cant_re_lt_of_mem_fibD hnk (hsk hx)) (cant_re_lt_of_mem_fibD hnk (hsk hy))
    (cantBit_const y₀ hnk hs hsk hx hy)

/-! #### Deck transformations, components, lifts -/

theorem cant_exists_deck {c c' : AbsU y₀} (h : c.pt = c'.pt) :
    ∃ g : AbsGamma y₀, (UniversalCover.deckHom g).1 c = c' := by
  obtain ⟨b, γ⟩ := c
  obtain ⟨b', γ'⟩ := c'
  simp only at h
  subst h
  refine ⟨(FundamentalGroup.fromPath (γ'.trans γ.symm))⁻¹, ?_⟩
  rw [UniversalCover.deckHom_apply, inv_inv]
  show (⟨b, (γ'.trans γ.symm).trans γ⟩ : AbsU y₀) = ⟨b, γ'⟩
  rw [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.trans_refl]

theorem cant_deck_image_comp (g : AbsGamma y₀) {U : Set ℂ} {c : AbsU y₀} (hc : absP y₀ c ∈ U) :
    (UniversalCover.deckHom g).1 '' connectedComponentIn (absP y₀ ⁻¹' U) c =
      connectedComponentIn (absP y₀ ⁻¹' U) ((UniversalCover.deckHom g).1 c) := by
  rw [Homeomorph.image_connectedComponentIn _ (show c ∈ absP y₀ ⁻¹' U from hc)]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    show absP y₀ ((UniversalCover.deckHom g).1 y) ∈ U
    rw [absP_deckHom]; exact hy
  · intro hx
    refine ⟨(UniversalCover.deckHom g).1.symm x, ?_, (UniversalCover.deckHom g).1.apply_symm_apply x⟩
    have := absP_deckHom y₀ g ((UniversalCover.deckHom g).1.symm x)
    rw [Homeomorph.apply_symm_apply] at this
    show absP y₀ _ ∈ U
    rw [← this]; exact hx

/-- `cpt k c`: the component of `c` in the preimage of `D_k`. -/
abbrev cantComp (k : ℕ) (c : AbsU y₀) : Set (AbsU y₀) :=
  connectedComponentIn (absP y₀ ⁻¹' fibD k) c

theorem cant_mem_comp_of_deck {k : ℕ} {c : AbsU y₀} (hc : absP y₀ c ∈ fibD k) {a : AbsGamma y₀}
    (ha : (UniversalCover.deckHom a).1 c ∈ cantComp y₀ k c) {x : AbsU y₀} (hx : x ∈ cantComp y₀ k c) :
    (UniversalCover.deckHom a).1 x ∈ cantComp y₀ k c := by
  have h1 : (UniversalCover.deckHom a).1 x ∈ (UniversalCover.deckHom a).1 '' cantComp y₀ k c :=
    mem_image_of_mem _ hx
  rw [cant_deck_image_comp y₀ a hc, ← connectedComponentIn_eq ha] at h1
  exact h1

theorem cant_stab_mul {k : ℕ} {c : AbsU y₀} (hc : absP y₀ c ∈ fibD k) {a b : AbsGamma y₀}
    (ha : (UniversalCover.deckHom a).1 c ∈ cantComp y₀ k c)
    (hb : (UniversalCover.deckHom b).1 c ∈ cantComp y₀ k c) :
    (UniversalCover.deckHom (a * b)).1 c ∈ cantComp y₀ k c := by
  rw [map_mul]
  exact cant_mem_comp_of_deck y₀ hc ha hb

/-- Every point of `D_k ∖ S` is reached from `c` inside its component. -/
theorem cant_reach {k : ℕ} (c : AbsU y₀) (hc : absP y₀ c ∈ fibD k) (b : (fibSᶜ : Set ℂ))
    (hb : (b : ℂ) ∈ fibD k) : ∃ c₀ ∈ cantComp y₀ k c, c₀.pt = b := by
  have hj := (isPathConnected_fibD_diff k).joinedIn (absP y₀ c) ⟨hc, absP_not_mem y₀ c⟩ b ⟨hb, b.2⟩
  let δ : Path c.pt b :=
    { toFun := fun t => ⟨hj.somePath t, (hj.somePath_mem t).2⟩
      continuous_toFun := hj.somePath.continuous.subtype_mk _
      source' := Subtype.ext hj.somePath.source
      target' := Subtype.ext hj.somePath.target }
  let L := UniversalCover.liftFrom c.cls δ
  refine ⟨L 1, ?_, (UniversalCover.proj_liftFrom _ _ 1).trans δ.target⟩
  have hsub : range L ⊆ absP y₀ ⁻¹' fibD k := by
    rintro _ ⟨t, rfl⟩; exact (hj.somePath_mem t).1
  exact (isPreconnected_range L.continuous).subset_connectedComponentIn ⟨0, L.source⟩ hsub ⟨1, rfl⟩

/-- A loop in `D_k ∖ S` gives a deck transformation preserving the component of `c` and acting on
the `sₘ` by the parities of its windings. -/
theorem cant_loop_realize {k : ℕ} (c : AbsU y₀) (hc : absP y₀ c ∈ fibD k) {b : (fibSᶜ : Set ℂ)}
    (δ : Path b b) (hδ : ∀ t, ((δ t : (fibSᶜ : Set ℂ)) : ℂ) ∈ fibD k) :
    ∃ h : AbsGamma y₀, (∀ m, cantEps y₀ m h =
      (-1 : ℂ) ^ cWinding (δ.map (subFib _ (cantPt_mem m)).continuous)) ∧
      (UniversalCover.deckHom h).1 c ∈ cantComp y₀ k c := by
  obtain ⟨c₀, hc₀, hpt⟩ := cant_reach y₀ c hc b (by simpa using hδ 0)
  obtain ⟨b', cls⟩ := c₀
  simp only at hpt
  subst hpt
  set L := UniversalCover.liftFrom cls δ
  have hsub : range L ⊆ absP y₀ ⁻¹' fibD k := by
    rintro _ ⟨t, rfl⟩; exact hδ t
  have hrange : range L ⊆ cantComp y₀ k ⟨b', cls⟩ :=
    (isPreconnected_range L.continuous).subset_connectedComponentIn ⟨0, L.source⟩ hsub
  have hcc : cantComp y₀ k c = cantComp y₀ k ⟨b', cls⟩ := connectedComponentIn_eq hc₀
  obtain ⟨h, hh⟩ := cant_exists_deck y₀ (c := ⟨b', cls⟩) (c' := L 1)
    ((UniversalCover.proj_liftFrom _ _ 1).trans δ.target).symm
  refine ⟨h, fun m => ?_, ?_⟩
  · have e1 := cantSq_deckHom y₀ m h ⟨b', cls⟩
    rw [hh, cantSq_liftFrom_loop] at e1
    have e0 : L 0 = ⟨b', cls⟩ := L.source
    rw [e0] at e1
    have hne := cantSq_ne_zero y₀ m ⟨b', cls⟩
    have : ((-1 : ℂ) ^ cWinding (δ.map (subFib _ (cantPt_mem m)).continuous) - cantEps y₀ m h) *
        cantSq y₀ m ⟨b', cls⟩ = 0 := by linear_combination e1
    exact (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hne)).symm
  · have hc0 : absP y₀ ⟨b', cls⟩ ∈ fibD k := hsub ⟨0, L.source⟩
    have h1 : (UniversalCover.deckHom h).1 ⟨b', cls⟩ ∈ cantComp y₀ k ⟨b', cls⟩ := by
      rw [hh]; exact hrange ⟨1, rfl⟩
    rw [hcc]
    exact cant_mem_comp_of_deck y₀ hc0 h1 (hcc ▸ mem_connectedComponentIn hc)

/-! #### Realising sign patterns by loops in `D_k` -/

/-- The sign patterns realised by deck transformations preserving the component of `c` over
`D_k`. -/
def CantReal (k : ℕ) (c : AbsU y₀) (τ : ℕ → ℂ) : Prop :=
  ∃ h : AbsGamma y₀, (∀ m, cantEps y₀ m h = τ m) ∧ (UniversalCover.deckHom h).1 c ∈ cantComp y₀ k c

theorem cantReal_one {k : ℕ} {c : AbsU y₀} (hc : absP y₀ c ∈ fibD k) : CantReal y₀ k c fun _ => 1 :=
  ⟨1, fun m => cantEps_one y₀ m, by rw [map_one]; exact mem_connectedComponentIn hc⟩

theorem cantReal_mul {k : ℕ} {c : AbsU y₀} (hc : absP y₀ c ∈ fibD k) {τ τ' : ℕ → ℂ}
    (h : CantReal y₀ k c τ) (h' : CantReal y₀ k c τ') : CantReal y₀ k c fun m => τ m * τ' m := by
  obtain ⟨a, ha, hac⟩ := h
  obtain ⟨b, hb, hbc⟩ := h'
  exact ⟨a * b, fun m => by rw [cantEps_mul, ha, hb], cant_stab_mul y₀ hc hac hbc⟩

theorem cantReal_congr {k : ℕ} {c : AbsU y₀} {τ τ' : ℕ → ℂ} (he : ∀ m, τ m = τ' m)
    (h : CantReal y₀ k c τ) : CantReal y₀ k c τ' := by
  obtain ⟨a, ha, hac⟩ := h
  exact ⟨a, fun m => (ha m).trans (he m), hac⟩

theorem cantPt_eq_absGalP_iff (m n : ℕ) : cantPt m = (absGalP n : ℂ) ↔ m = n := by
  rw [cantPt, Complex.ofReal_inj, absGalP]
  constructor
  · intro h
    have : (m : ℝ) + 1 = (n : ℝ) + 1 := by
      have h' := h
      field_simp at h'
      linarith
    exact_mod_cast (by linarith : (m : ℝ) = n)
  · rintro rfl; rfl

theorem cant_absGalCirc_mem {k n : ℕ} (hkn : k ≤ n) (t : I) : absGalCirc n t ∈ fibD k := by
  rw [fibD, Metric.mem_ball, dist_zero_right]
  have h1 : ‖absGalCirc n t‖ ≤ ‖absGalCirc n t - absGalP n‖ + ‖((absGalP n : ℝ) : ℂ)‖ := by
    calc ‖absGalCirc n t‖ = ‖(absGalCirc n t - absGalP n) + ((absGalP n : ℝ) : ℂ)‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
  rw [norm_absGalCirc_sub, Complex.norm_real, Real.norm_of_nonneg (by unfold absGalP; positivity)]
    at h1
  have h2 : absGalρ n + absGalP n < 1 / ((n : ℝ) + 1 / 2) := by
    unfold absGalρ absGalP
    rw [div_add_div _ _ (by positivity) (by positivity), div_lt_div_iff₀ (by positivity)
      (by positivity)]
    nlinarith
  have h3 : 1 / ((n : ℝ) + 1 / 2) ≤ 1 / ((k : ℝ) + 1 / 2) :=
    one_div_le_one_div_of_le (by positivity) (by have : (k : ℝ) ≤ n := (by exact_mod_cast hkn); linarith)
  linarith

/-- The flip of the single sign `n ≥ k` is realised (the small circle around `aₙ`). -/
theorem cantReal_flip {k : ℕ} {c : AbsU y₀} (hc : absP y₀ c ∈ fibD k) {n : ℕ} (hkn : k ≤ n) :
    CantReal y₀ k c fun m => if m = n then -1 else 1 := by
  obtain ⟨h, hh, hc'⟩ := cant_loop_realize y₀ c hc (absGalCircPath n)
    fun t => cant_absGalCirc_mem hkn t
  refine ⟨h, fun m => ?_, hc'⟩
  beta_reduce
  rw [hh, absGal_cWinding_circ]
  by_cases hm : m = n
  · rw [if_pos ((cantPt_eq_absGalP_iff m n).2 hm), if_pos hm]; norm_num
  · rw [if_neg (fun e => hm ((cantPt_eq_absGalP_iff m n).1 e)), if_neg hm]; norm_num

/-- The circle `t ↦ -R e^{2iπt}` around `0`. -/
def cantCirc (R : ℝ) (t : I) : ℂ := -(R : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ))

theorem cant_norm_exp (t : ℝ) : ‖Complex.exp (2 * Real.pi * Complex.I * t)‖ = 1 := by
  rw [show (2 * Real.pi * Complex.I * t : ℂ) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I by
    push_cast; ring, Complex.norm_exp_ofReal_mul_I]

theorem cant_norm_exp_neg (t : ℝ) : ‖Complex.exp (-(2 * Real.pi * Complex.I * t))‖ = 1 := by
  rw [show (-(2 * Real.pi * Complex.I * t) : ℂ) = ((-(2 * Real.pi * t) : ℝ) : ℂ) * Complex.I by
    push_cast; ring, Complex.norm_exp_ofReal_mul_I]

theorem norm_cantCirc {R : ℝ} (hR : 0 ≤ R) (t : I) : ‖cantCirc R t‖ = R := by
  rw [cantCirc, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hR, cant_norm_exp, mul_one]

theorem cantCirc_zero (R : ℝ) : cantCirc R 0 = -(R : ℂ) := by simp [cantCirc]

theorem cantCirc_one (R : ℝ) : cantCirc R 1 = -(R : ℂ) := by
  simp only [cantCirc, Set.Icc.coe_one, Complex.ofReal_one, mul_one, Complex.exp_two_pi_mul_I]

theorem cantCirc_not_mem {R : ℝ} (hR : 0 ≤ R) (hS : ∀ s ∈ fibS, ‖s‖ ≠ R) (t : I) :
    cantCirc R t ∉ fibS := fun h => hS _ h (norm_cantCirc hR t)

theorem cant_negR_not_mem {R : ℝ} (hR : 0 ≤ R) (hS : ∀ s ∈ fibS, ‖s‖ ≠ R) : -(R : ℂ) ∉ fibS :=
  cantCirc_zero R ▸ cantCirc_not_mem hR hS 0

/-- The circle as a loop of `ℂ ∖ S`. -/
def cantCircPath {R : ℝ} (hR : 0 ≤ R) (hS : ∀ s ∈ fibS, ‖s‖ ≠ R) :
    Path (⟨-(R : ℂ), cant_negR_not_mem hR hS⟩ : (fibSᶜ : Set ℂ)) ⟨-(R : ℂ), cant_negR_not_mem hR hS⟩ where
  toFun t := ⟨cantCirc R t, cantCirc_not_mem hR hS t⟩
  continuous_toFun := by refine Continuous.subtype_mk ?_ _; unfold cantCirc; fun_prop
  source' := Subtype.ext (cantCirc_zero R)
  target' := Subtype.ext (cantCirc_one R)

theorem cant_slit_of_norm {w : ℂ} (hw : ‖w‖ < 1) : 1 + w ∈ Complex.slitPlane := by
  refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
  have := Complex.abs_re_le_norm w
  rw [Complex.add_re, Complex.one_re]
  linarith [abs_lt.1 (this.trans_lt hw)]

/-- The circle of radius `R` winds once around the points of `S` inside it. -/
theorem cant_cWinding_circ_in {R : ℝ} (hR : 0 < R) (hS : ∀ s ∈ fibS, ‖s‖ ≠ R) {q : ℂ}
    (hq : q ∈ fibS) (hqR : ‖q‖ < R) :
    cWinding ((cantCircPath hR.le hS).map (subFib q hq).continuous) = 1 := by
  set w : I → ℂ := fun t => q / (R : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I * (t : ℝ)))
  have hR0 : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR.ne'
  have hw : ∀ t, ‖w t‖ < 1 := fun t => by
    simp only [w, norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le,
      cant_norm_exp_neg, mul_one]
    rwa [div_lt_one hR]
  have hwc : Continuous w := by simp only [w]; fun_prop
  refine cWinding_eq _ (Γ := ⟨fun t => Complex.log (-(R : ℂ)) + 2 * Real.pi * Complex.I * (t : ℝ) +
      Complex.log (1 + w t), (continuous_const.add (by fun_prop)).add
        (continuous_iff_continuousAt.2 fun t =>
          (continuous_const.add hwc).continuousAt.clog (cant_slit_of_norm (hw t)))⟩) (fun t => ?_) ?_
  · show Complex.exp (Complex.log (-(R : ℂ)) + 2 * Real.pi * Complex.I * (t : ℝ) +
      Complex.log (1 + w t)) = cantCirc R t - q
    rw [Complex.exp_add, Complex.exp_add, Complex.exp_log (neg_ne_zero.2 hR0),
      Complex.exp_log (Complex.slitPlane_ne_zero (cant_slit_of_norm (hw t)))]
    simp only [w, cantCirc, Complex.exp_neg]
    have hE := Complex.exp_ne_zero (2 * Real.pi * Complex.I * (t : ℝ))
    field_simp
    ring
  · simp only [ContinuousMap.coe_mk, w, Set.Icc.coe_one, Set.Icc.coe_zero, Complex.ofReal_one,
      Complex.ofReal_zero, mul_one, mul_zero, neg_zero, Complex.exp_zero, Int.cast_one, one_mul]
    rw [Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one, mul_one]
    ring

/-- The circle of radius `R` does not wind around the points of `S` outside it. -/
theorem cant_cWinding_circ_out {R : ℝ} (hR : 0 < R) (hS : ∀ s ∈ fibS, ‖s‖ ≠ R) {q : ℂ}
    (hq : q ∈ fibS) (hqR : R < ‖q‖) :
    cWinding ((cantCircPath hR.le hS).map (subFib q hq).continuous) = 0 := by
  have hq0 : q ≠ 0 := fun h => by rw [h, norm_zero] at hqR; linarith
  set w : I → ℂ := fun t => (R : ℂ) / q * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ))
  have hw : ∀ t, ‖w t‖ < 1 := fun t => by
    simp only [w, norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le,
      cant_norm_exp, mul_one]
    rwa [div_lt_one (by linarith)]
  have hwc : Continuous w := by simp only [w]; fun_prop
  refine cWinding_eq _ (Γ := ⟨fun t => Complex.log (-q) + Complex.log (1 + w t),
      continuous_const.add (continuous_iff_continuousAt.2 fun t =>
          (continuous_const.add hwc).continuousAt.clog (cant_slit_of_norm (hw t)))⟩) (fun t => ?_) ?_
  · show Complex.exp (Complex.log (-q) + Complex.log (1 + w t)) = cantCirc R t - q
    rw [Complex.exp_add, Complex.exp_log (neg_ne_zero.2 hq0),
      Complex.exp_log (Complex.slitPlane_ne_zero (cant_slit_of_norm (hw t)))]
    simp only [w, cantCirc]
    field_simp
    ring
  · simp only [ContinuousMap.coe_mk, w, Set.Icc.coe_one, Set.Icc.coe_zero, Complex.ofReal_one,
      Complex.ofReal_zero, mul_one, mul_zero, Complex.exp_zero, Int.cast_zero, zero_mul, add_zero,
      Complex.exp_two_pi_mul_I]

/-- The radius `R_k` between `a_k` and the radius of `D_k`. -/
def cantR (k : ℕ) : ℝ := (1 / ((k : ℝ) + 1) + 1 / ((k : ℝ) + 1 / 2)) / 2

theorem cantR_pos (k : ℕ) : 0 < cantR k := by unfold cantR; positivity

theorem cantR_gt (k : ℕ) : 1 / ((k : ℝ) + 1) < cantR k := by
  have : 1 / ((k : ℝ) + 1) < 1 / ((k : ℝ) + 1 / 2) :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  unfold cantR; linarith

theorem cantR_lt (k : ℕ) : cantR k < 1 / ((k : ℝ) + 1 / 2) := by
  have : 1 / ((k : ℝ) + 1) < 1 / ((k : ℝ) + 1 / 2) :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  unfold cantR; linarith

theorem norm_cantPt (m : ℕ) : ‖cantPt m‖ = 1 / ((m : ℝ) + 1) := by
  rw [cantPt, Complex.norm_real, Real.norm_of_nonneg (by positivity)]

theorem cant_norm_lt_cantR {k m : ℕ} (h : k ≤ m) : ‖cantPt m‖ < cantR k := by
  rw [norm_cantPt]
  have : 1 / ((m : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by have : (k : ℝ) ≤ m := (by exact_mod_cast h); linarith)
  linarith [cantR_gt k]

theorem cant_cantR_lt_norm {k m : ℕ} (h : m < k) : cantR k < ‖cantPt m‖ := by
  rw [norm_cantPt]
  have : 1 / ((k : ℝ) + 1 / 2) < 1 / ((m : ℝ) + 1) :=
    one_div_lt_one_div_of_lt (by positivity) (by have : (m : ℝ) + 1 ≤ k := (by exact_mod_cast h); linarith)
  linarith [cantR_lt k]

theorem cantR_ne (k : ℕ) : ∀ s ∈ fibS, ‖s‖ ≠ cantR k := by
  rintro s (rfl | ⟨m, rfl⟩)
  · rw [norm_zero]; exact (cantR_pos k).ne
  · show ‖cantPt m‖ ≠ cantR k
    rcases lt_or_ge m k with h | h
    · exact (cant_cantR_lt_norm h).ne'
    · exact (cant_norm_lt_cantR h).ne

/-- The flip of all the signs `m ≥ k` is realised (the circle of radius `R_k` around `0`). -/
theorem cantReal_big {k : ℕ} {c : AbsU y₀} (hc : absP y₀ c ∈ fibD k) :
    CantReal y₀ k c fun m => if k ≤ m then -1 else 1 := by
  obtain ⟨h, hh, hc'⟩ := cant_loop_realize y₀ c hc (cantCircPath (cantR_pos k).le (cantR_ne k))
    fun t => by
      show cantCirc (cantR k) t ∈ fibD k
      rw [fibD, Metric.mem_ball, dist_zero_right, norm_cantCirc (cantR_pos k).le]
      exact cantR_lt k
  refine ⟨h, fun m => ?_, hc'⟩
  beta_reduce
  rw [hh]
  by_cases hm : k ≤ m
  · rw [cant_cWinding_circ_in (cantR_pos k) (cantR_ne k) _ (cant_norm_lt_cantR hm), if_pos hm]
    norm_num
  · rw [cant_cWinding_circ_out (cantR_pos k) (cantR_ne k) _ (cant_cantR_lt_norm (not_le.1 hm)),
      if_neg hm]
    norm_num

/-- Every `±1` pattern supported in `[k, N)` is realised. -/
theorem cantReal_finite {k : ℕ} {c : AbsU y₀} (hc : absP y₀ c ∈ fibD k) :
    ∀ (N : ℕ) (τ : ℕ → ℂ), (∀ m, τ m = 1 ∨ τ m = -1) → (∀ m, m < k ∨ N ≤ m → τ m = 1) →
      CantReal y₀ k c τ := by
  intro N
  induction N with
  | zero =>
    intro τ _ hτ
    exact cantReal_congr y₀ (fun m => (hτ m (Or.inr (Nat.zero_le m))).symm) (cantReal_one y₀ hc)
  | succ N ih =>
    intro τ hpm hτ
    have h' := ih (fun m => if m = N then 1 else τ m)
      (fun m => by split_ifs <;> simp_all) (fun m hm => by
        split_ifs with h
        · rfl
        · refine hτ m ?_
          rcases hm with hm | hm
          · exact Or.inl hm
          · exact Or.inr (by omega))
    rcases hpm N with hN | hN
    · exact cantReal_congr y₀ (fun m => by split_ifs with h <;> simp_all) h'
    · have hkN : k ≤ N := by
        by_contra hlt
        have := hτ N (Or.inl (not_le.1 hlt))
        rw [hN] at this; norm_num at this
      refine cantReal_congr y₀ (fun m => ?_) (cantReal_mul y₀ hc h' (cantReal_flip y₀ hc hkN))
      by_cases h : m = N
      · subst h; simp [hN]
      · simp [h]

/-! #### The signs of a loop class are eventually constant -/

theorem cant_wind_eq_of_small (γ : Path y₀ y₀) {δ : ℝ}
    (hmin : ∀ t, δ ≤ ‖((γ t : (fibSᶜ : Set ℂ)) : ℂ)‖) {n m : ℕ} (hn : ‖cantPt n‖ < δ / 3)
    (hm : ‖cantPt m‖ < δ / 3) :
    windAt y₀ _ (cantPt_mem n) γ = windAt y₀ _ (cantPt_mem m) γ := by
  unfold windAt
  obtain ⟨Γ, hΓ⟩ := exists_expLift (γ.map (subFib _ (cantPt_mem m)).continuous).toContinuousMap
  have e := cWinding_spec _ hΓ
  have hden : ∀ t, ((γ t : (fibSᶜ : Set ℂ)) : ℂ) - cantPt m ≠ 0 := fun t h =>
    (γ t).2 (by rw [sub_eq_zero] at h; rw [h]; exact cantPt_mem m)
  set w : I → ℂ := fun t => (cantPt m - cantPt n) / (((γ t : (fibSᶜ : Set ℂ)) : ℂ) - cantPt m)
  have hw : ∀ t, ‖w t‖ < 1 := fun t => by
    have h1 : ‖cantPt m - cantPt n‖ ≤ ‖cantPt m‖ + ‖cantPt n‖ := norm_sub_le _ _
    have h2 : ‖((γ t : (fibSᶜ : Set ℂ)) : ℂ)‖ - ‖cantPt m‖ ≤
        ‖((γ t : (fibSᶜ : Set ℂ)) : ℂ) - cantPt m‖ := norm_sub_norm_le _ _
    have h3 := hmin t
    have hpos : 0 < ‖((γ t : (fibSᶜ : Set ℂ)) : ℂ) - cantPt m‖ := norm_pos_iff.2 (hden t)
    simp only [w, norm_div]
    rw [div_lt_one hpos]
    linarith [norm_nonneg (cantPt n), norm_nonneg (cantPt m)]
  have hwc : Continuous w := by
    simp only [w]
    exact continuous_const.div ((continuous_subtype_val.comp γ.continuous).sub continuous_const) hden
  have hL : Continuous fun t => Complex.log (1 + w t) :=
    continuous_iff_continuousAt.2 fun t =>
      (continuous_const.add hwc).continuousAt.clog (cant_slit_of_norm (hw t))
  refine cWinding_eq _ (Γ := Γ + ⟨fun t => Complex.log (1 + w t), hL⟩) (fun t => ?_) ?_
  · show Complex.exp (Γ t + Complex.log (1 + w t)) = ((γ t : (fibSᶜ : Set ℂ)) : ℂ) - cantPt n
    rw [Complex.exp_add, Complex.exp_log (Complex.slitPlane_ne_zero (cant_slit_of_norm (hw t))), hΓ t]
    show (((γ t : (fibSᶜ : Set ℂ)) : ℂ) - cantPt m) * (1 + w t) = _
    simp only [w]
    field_simp [hden t]
    ring
  · have hw10 : w 1 = w 0 := by simp only [w, γ.source, γ.target]
    simp only [ContinuousMap.add_apply, ContinuousMap.coe_mk]
    rw [hw10, e]
    ring

theorem cant_wind_eventually (γ : Path y₀ y₀) :
    ∃ N, ∀ n ≥ N, windAt y₀ _ (cantPt_mem n) γ = windAt y₀ _ (cantPt_mem N) γ := by
  obtain ⟨t₀, -, ht₀⟩ := isCompact_univ.exists_isMinOn univ_nonempty
    (f := fun t : I => ‖((γ t : (fibSᶜ : Set ℂ)) : ℂ)‖)
    (continuous_norm.comp (continuous_subtype_val.comp γ.continuous)).continuousOn
  set δ := ‖((γ t₀ : (fibSᶜ : Set ℂ)) : ℂ)‖
  have hδ : 0 < δ := norm_pos_iff.2 fun h => (γ t₀).2 (h ▸ Set.mem_insert 0 _)
  have hmin : ∀ t, δ ≤ ‖((γ t : (fibSᶜ : Set ℂ)) : ℂ)‖ := fun t => ht₀ (mem_univ t)
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (show 0 < δ / 3 by positivity)
  have hsmall : ∀ n ≥ N, ‖cantPt n‖ < δ / 3 := fun n hn => by
    rw [norm_cantPt]
    have : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by have : (N : ℝ) ≤ n := (by exact_mod_cast hn); linarith)
    linarith
  exact ⟨N, fun n hn => cant_wind_eq_of_small y₀ γ hmin (hsmall n hn) (hsmall N le_rfl)⟩

theorem cant_eps_eventually (g : AbsGamma y₀) :
    ∃ N, ∀ n ≥ N, cantEps y₀ n g = cantEps y₀ N g := by
  suffices h : ∀ q : Path.Homotopic.Quotient y₀ y₀, ∃ N, ∀ n ≥ N,
      cantEps y₀ n (FundamentalGroup.fromPath q) = cantEps y₀ N (FundamentalGroup.fromPath q) from
    h (FundamentalGroup.toPath g)
  intro q
  induction q using Path.Homotopic.Quotient.ind with
  | mk γ =>
    obtain ⟨N, hN⟩ := cant_wind_eventually y₀ γ
    exact ⟨N, fun n hn => by rw [cantEps_fromPath, cantEps_fromPath, hN n hn]⟩

/-- Every deck transformation trivial on the signs `m < k` has its pattern realised inside the
component of `c` over `D_k`. -/
theorem cantReal_of_eps {k : ℕ} {c : AbsU y₀} (hc : absP y₀ c ∈ fibD k) (g : AbsGamma y₀)
    (hg : ∀ m < k, cantEps y₀ m g = 1) : CantReal y₀ k c fun m => cantEps y₀ m g := by
  obtain ⟨N₀, hN₀⟩ := cant_eps_eventually y₀ g
  set N := max N₀ k
  have hN : ∀ n ≥ N, cantEps y₀ n g = cantEps y₀ N g := fun n hn =>
    (hN₀ n (le_trans (le_max_left _ _) hn)).trans (hN₀ N (le_max_left _ _)).symm
  rcases cantEps_eq y₀ N g with hE | hE
  · exact cantReal_finite y₀ hc N _ (fun m => cantEps_eq y₀ m g) fun m hm =>
      hm.elim (hg m) fun h => (hN m h).trans hE
  · have h' := cantReal_finite y₀ hc N (fun m => cantEps y₀ m g * if k ≤ m then -1 else 1)
      (fun m => by
        rcases cantEps_eq y₀ m g with e | e <;> rw [e] <;> split_ifs <;> norm_num)
      (fun m hm => by
        rcases hm with hm | hm
        · rw [hg m hm, if_neg (not_le.2 hm)]; ring
        · rw [hN m hm, hE, if_pos (le_trans (le_max_right _ _) hm)]; ring)
    refine cantReal_congr y₀ (fun m => ?_) (cantReal_mul y₀ hc h' (cantReal_big y₀ hc))
    split_ifs <;> ring

/-! #### `Γ₂' \ \widetilde{ℂ∖S}`, its completion `Y₂'`, and the components over `D_k` -/

/-- `Γ₂'` as a group of homeomorphisms of `\widetilde{ℂ∖S}`. -/
def cantHomeo : Subgroup (AbsU y₀ ≃ₜ AbsU y₀) :=
  ((cantGamma y₀).map UniversalCover.deckHom).map
    (deckGroup (UniversalCover.proj (fibSᶜ : Set ℂ) y₀)).subtype

/-- `Γ₂' \ ord(\widetilde Y^S)`. -/
abbrev CantOrd : Type := HomeoQuotient (cantHomeo y₀)

/-- The spread `Γ₂' \ ord(\widetilde Y^S) → Y`. -/
def cantProj : CantOrd y₀ → ℂ :=
  Quotient.lift (univCoverProj fibS y₀) fun a b ⟨φ, hφ, h⟩ => by
    obtain ⟨ψ, -, rfl⟩ := Subgroup.mem_map.1 hφ
    rw [← h]
    exact (congrArg Subtype.val (congrFun ψ.2 a)).symm

/-- **`Y₂'`**, the completion of the spread `Γ₂' \ ord(\widetilde Y^S) → Y` (DEC-69). -/
abbrev CantY₂ : Type := SpreadEnd (cantProj y₀)

/-- The fibre of `Y₂'` above `0`. -/
def cantFiber0 : Set (CantY₂ y₀) := SpreadEnd.base ⁻¹' {0}

theorem cantProj_mk (c : AbsU y₀) : cantProj y₀ (homeoQuotientMk _ c) = absP y₀ c := rfl

theorem cantSigma_inv {φ : AbsU y₀ ≃ₜ AbsU y₀} (hφ : φ ∈ cantHomeo y₀) (n : ℕ) (c : AbsU y₀) :
    cantSigma y₀ n (φ c) = cantSigma y₀ n c := by
  obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.1 hφ
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hd
  show cantSigma y₀ n ((UniversalCover.deckHom g).1 c) = _
  rw [cantSigma_deckHom, hg n, one_mul]

/-- The bit `σₙ = 1` on `Γ₂' \ \widetilde{ℂ∖S}`. -/
def cantBitQ (n : ℕ) : CantOrd y₀ → Bool :=
  Quotient.lift (cantBit y₀ n) fun a b ⟨φ, hφ, h⟩ => by
    rw [← h]; unfold cantBit; rw [cantSigma_inv y₀ hφ]

theorem cant_isOpen_levelQ {n k : ℕ} (hnk : n < k) (b : Bool) :
    IsOpen {x : CantOrd y₀ | cantProj y₀ x ∈ fibD k ∧ cantBitQ y₀ n x = b} := by
  rw [← isQuotientMap_quotient_mk'.isOpen_preimage]
  exact cant_isOpen_level y₀ hnk b

theorem cantBitQ_const {n k : ℕ} (hnk : n < k) {x x' : CantOrd y₀} (hx : cantProj y₀ x ∈ fibD k)
    (hx' : x' ∈ connectedComponentIn (cantProj y₀ ⁻¹' fibD k) x) :
    cantBitQ y₀ n x' = cantBitQ y₀ n x :=
  cant_const_of_isOpen_level (A := cantProj y₀ ⁻¹' fibD k) (fun b => cant_isOpen_levelQ y₀ hnk b)
    isPreconnected_connectedComponentIn (connectedComponentIn_subset _ _)
    (mem_connectedComponentIn hx) hx'

/-- **Points of `Γ₂' \ \widetilde{ℂ∖S}` over `D_k` with the same signs `σₙ`, `n < k`, lie in the
same component of the preimage of `D_k`.** -/
theorem cant_mem_comp_of_sigma {k : ℕ} {c c' : AbsU y₀} (hc : absP y₀ c ∈ fibD k)
    (hc' : absP y₀ c' ∈ fibD k) (hs : ∀ n < k, cantSigma y₀ n c' = cantSigma y₀ n c) :
    homeoQuotientMk _ c' ∈ connectedComponentIn (cantProj y₀ ⁻¹' fibD k) (homeoQuotientMk _ c) := by
  obtain ⟨c'', hc'', hpt⟩ := cant_reach y₀ c hc c'.pt hc'
  obtain ⟨g, hg⟩ := cant_exists_deck y₀ hpt
  have hc''k : absP y₀ c'' ∈ fibD k := connectedComponentIn_subset (absP y₀ ⁻¹' fibD k) c hc''
  have hgk : ∀ m < k, cantEps y₀ m g = 1 := by
    intro m hm
    have e1 := cantSigma_deckHom y₀ m g c''
    rw [hg] at e1
    have e2 : cantSigma y₀ m c'' = cantSigma y₀ m c :=
      cantSigma_const y₀ hm isPreconnected_connectedComponentIn (connectedComponentIn_subset _ _)
        (mem_connectedComponentIn hc) hc''
    rw [hs m hm, e2] at e1
    have hne : cantSigma y₀ m c ≠ 0 := by
      rcases cantSigma_eq y₀ (cant_re_lt_of_mem_fibD hm hc) with e | e <;> rw [e] <;> norm_num
    have : (cantEps y₀ m g - 1) * cantSigma y₀ m c = 0 := by linear_combination -e1
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hne)
  obtain ⟨h, hh, hhc⟩ := cantReal_of_eps y₀ hc''k g hgk
  have hu : g * h⁻¹ ∈ cantGamma y₀ := fun m => by
    show cantEps y₀ m (g * h⁻¹) = 1
    rw [cantEps_mul, cantEps_inv, hh m]
    beta_reduce
    rw [← sq, cantEps_sq]
  have heq : homeoQuotientMk (cantHomeo y₀) ((UniversalCover.deckHom h).1 c'') =
      homeoQuotientMk _ c' := Quotient.sound
    ⟨(UniversalCover.deckHom (g * h⁻¹)).1,
      Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hu), by
        rw [← hg]
        show ((UniversalCover.deckHom (g * h⁻¹)) * (UniversalCover.deckHom h)).1 c'' = _
        rw [← map_mul, inv_mul_cancel_right]⟩
  rw [← heq]
  have hcomp : cantComp y₀ k c'' = cantComp y₀ k c := (connectedComponentIn_eq hc'').symm
  have hmem : (UniversalCover.deckHom h).1 c'' ∈ cantComp y₀ k c := hcomp ▸ hhc
  exact (isPreconnected_connectedComponentIn.image _ continuous_quotient_mk'.continuousOn)
    |>.subset_connectedComponentIn ⟨c, mem_connectedComponentIn hc, rfl⟩
      (image_subset_iff.2 fun x hx => by
        exact (connectedComponentIn_subset (absP y₀ ⁻¹' fibD k) c hx : absP y₀ x ∈ fibD k))
      ⟨_, hmem, rfl⟩

/-- The set of points over `D_k` with signs `τ₀, …, τ_{k-1}`. -/
def cantZ (k : ℕ) (τ : ℕ → Bool) : Set (CantOrd y₀) :=
  {x | cantProj y₀ x ∈ fibD k ∧ ∀ n < k, cantBitQ y₀ n x = τ n}

/-- **The components of the preimage of `D_k` are exactly the sets `cantZ k τ`.** -/
theorem cantZ_comp {k : ℕ} {τ : ℕ → Bool} {x : CantOrd y₀} (hx : x ∈ cantZ y₀ k τ) :
    connectedComponentIn (cantProj y₀ ⁻¹' fibD k) x = cantZ y₀ k τ := by
  ext y
  constructor
  · intro hy
    exact ⟨connectedComponentIn_subset (cantProj y₀ ⁻¹' fibD k) x hy, fun n hn =>
      (cantBitQ_const y₀ hn hx.1 hy).trans (hx.2 n hn)⟩
  · intro hy
    induction x using Quotient.inductionOn with
    | h c =>
      induction y using Quotient.inductionOn with
      | h c' =>
        refine cant_mem_comp_of_sigma y₀ hx.1 hy.1 fun n hn => ?_
        exact cantSigma_eq_of_bit y₀ (cant_re_lt_of_mem_fibD hn hx.1)
          (cant_re_lt_of_mem_fibD hn hy.1) ((hy.2 n hn).trans (hx.2 n hn).symm)

theorem cantZ_nonempty (k : ℕ) (τ : ℕ → Bool) : (cantZ y₀ k τ).Nonempty := by
  set c₀ := absGalW y₀ k
  have hc₀ : absP y₀ c₀ ∈ fibD k := by rw [absP_absGalW]; exact (fibQ_mem k).1
  have hc₀0 : absP y₀ c₀ ∈ fibD 0 := fibD_subset_iff.2 (Nat.zero_le k) hc₀
  set ρ : ℕ → ℂ := fun m => if m < k ∧ cantBit y₀ m c₀ ≠ τ m then -1 else 1
  obtain ⟨h, hh, -⟩ := cantReal_finite y₀ hc₀0 k ρ
    (fun m => by simp only [ρ]; split_ifs <;> simp)
    (fun m hm => by
      simp only [ρ]
      rw [if_neg]
      rintro ⟨h1, -⟩
      omega)
  refine ⟨homeoQuotientMk _ ((UniversalCover.deckHom h).1 c₀), hc₀, fun n hn => ?_⟩
  show cantBit y₀ n ((UniversalCover.deckHom h).1 c₀) = τ n
  have hreg := cant_re_lt_of_mem_fibD hn hc₀
  by_cases hb : cantBit y₀ n c₀ = τ n
  · have hρ : ρ n = 1 := if_neg (fun h' => h'.2 hb)
    unfold cantBit
    simp only [cantSigma_deckHom, hh n, hρ, one_mul]
    exact hb
  · have hρ : ρ n = -1 := if_pos ⟨hn, hb⟩
    unfold cantBit at hb ⊢
    simp only [cantSigma_deckHom, hh n, hρ]
    rcases cantSigma_eq y₀ hreg with e | e <;> simp only [e] at hb ⊢ <;> revert hb <;>
      cases τ n <;> norm_num

/-- The thread `D_k ↦ cantZ k τ`. -/
def cantThread (τ : ℕ → Bool) : FiberThread (cantProj y₀) (range fibD) where
  toFun U := cantZ y₀ (absGalIdx U) τ
  isCompOf U := by
    have hU := absGalIdx_spec U
    obtain ⟨x, hx⟩ := cantZ_nonempty y₀ (absGalIdx U) τ
    refine ⟨x, hU ▸ hx.1, ?_⟩
    rw [← cantZ_comp y₀ hx, hU]
  mono U V hUV := by
    have hU := absGalIdx_spec U
    have hV := absGalIdx_spec V
    rw [← hU, ← hV, fibD_subset_iff] at hUV
    exact fun x hx => ⟨fibD_subset_iff.2 hUV hx.1, fun n hn => hx.2 n (lt_of_lt_of_le hn hUV)⟩

/-- The end of `Y₂'` over `0` with signs `τ`. -/
def cantEnd (τ : ℕ → Bool) : CantY₂ y₀ := (cantThread y₀ τ).toEnd absGal_h𝓤 fibD_basis

theorem cantEnd_base (τ : ℕ → Bool) : (cantEnd y₀ τ).base = 0 := rfl

theorem cantEnd_apply (τ : ℕ → Bool) (k : ℕ) : cantEnd y₀ τ (fibD k) = cantZ y₀ k τ := by
  have := FiberThread.toEnd_apply absGal_h𝓤 fibD_basis (cantThread y₀ τ) ⟨fibD k, k, rfl⟩
  rw [cantEnd, this]
  show cantZ y₀ (absGalIdx ⟨fibD k, k, rfl⟩) τ = _
  rw [fibD_injective (absGalIdx_spec ⟨fibD k, k, rfl⟩)]

theorem cantEnd_injective : Injective (cantEnd y₀) := by
  intro τ τ' h
  funext n
  obtain ⟨x, hx⟩ := cantZ_nonempty y₀ (n + 1) τ
  have hx' : x ∈ cantZ y₀ (n + 1) τ' := by rw [← cantEnd_apply, ← h, cantEnd_apply]; exact hx
  exact (hx.2 n (Nat.lt_succ_self n)).symm.trans (hx'.2 n (Nat.lt_succ_self n))

theorem cantEnd_surj (e : CantY₂ y₀) (he : e.base = 0) : ∃ τ, cantEnd y₀ τ = e := by
  have hD : ∀ k, IsCNbhd e.base (fibD k) := fun k => he ▸ isCNbhd_fibD k
  choose y hy using fun n => e.nonempty (hD (n + 1))
  refine ⟨fun n => cantBitQ y₀ n (y n), ?_⟩
  have hk : ∀ k, e (fibD k) = cantZ y₀ k (fun n => cantBitQ y₀ n (y n)) := by
    intro k
    obtain ⟨x, hx⟩ := e.nonempty (hD k)
    have hxZ : x ∈ cantZ y₀ k (fun n => cantBitQ y₀ n (y n)) := by
      refine ⟨e.subset_preimage (hD k) hx, fun n hn => ?_⟩
      have hsub : e (fibD k) ⊆ e (fibD (n + 1)) :=
        e.mono _ _ (hD k) (hD (n + 1)) (fibD_subset_iff.2 hn)
      have hc := (e.isCompOf _ (hD (n + 1))).eq_of_mem (hy n)
      have hx' : x ∈ connectedComponentIn (cantProj y₀ ⁻¹' fibD (n + 1)) (y n) := hc ▸ hsub hx
      exact cantBitQ_const y₀ (Nat.lt_succ_self n) (e.subset_preimage (hD (n + 1)) (hy n)) hx'
    rw [(e.isCompOf _ (hD k)).eq_of_mem hx, cantZ_comp y₀ hxZ]
  refine SpreadEnd.ext_of_isCNbhd ((cantEnd_base y₀ _).trans he.symm) fun U hU => ?_
  have hU0 : IsCNbhd (0 : ℂ) U := hU
  obtain ⟨_, ⟨k, rfl⟩, hkU⟩ := fibD_basis U (hU0.1.mem_nhds hU0.2.2)
  obtain ⟨x, hx⟩ := cantZ_nonempty y₀ k (fun n => cantBitQ y₀ n (y n))
  have h1 : x ∈ cantEnd y₀ _ U :=
    (cantEnd y₀ _).mono _ _ (isCNbhd_fibD k) hU hkU (by rw [cantEnd_apply]; exact hx)
  have h2 : x ∈ e U := e.mono _ _ (hD k) (he ▸ hU0) hkU (by rw [hk]; exact hx)
  exact ((cantEnd y₀ _).isCompOf U hU).eq_of_meets (e.isCompOf U (he ▸ hU0)) ⟨x, h1, h2⟩

theorem continuous_cantEnd : Continuous (cantEnd y₀) := by
  refine continuous_iff_continuousAt.2 fun τ =>
    ((SpreadEnd.hasBasis_nhds (cantEnd y₀ τ)).tendsto_right_iff).2 fun W hW => ?_
  have hW' : IsCNbhd (0 : ℂ) W := hW
  obtain ⟨_, ⟨k, rfl⟩, hkW⟩ := fibD_basis W (hW'.1.mem_nhds hW'.2.2)
  have hev : ∀ᶠ τ' in 𝓝 τ, ∀ n ∈ Finset.range k, τ' n = τ n :=
    (Filter.eventually_all_finset _).2 fun n _ =>
      ((continuous_apply n).tendsto τ) ((isOpen_discrete {τ n}).mem_nhds rfl)
  filter_upwards [hev] with τ' hτ'
  refine ⟨fibD k, isCNbhd_fibD k, hkW, ?_⟩
  have hZ : cantZ y₀ k τ' = cantZ y₀ k τ := by
    ext x
    simp only [cantZ, mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun n hn => (h2 n hn).trans (hτ' n (Finset.mem_range.2 hn))⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun n hn => (h2 n hn).trans (hτ' n (Finset.mem_range.2 hn)).symm⟩
  rw [cantEnd_apply, hZ, ← cantEnd_apply]
  exact (cantEnd y₀ τ).mono _ _ (isCNbhd_fibD k) hW' hkW

/-- The fibre of `Y₂'` above `0` is homeomorphic to `{0,1}^ℕ`. -/
def cantFiberHomeo : (ℕ → Bool) ≃ₜ cantFiber0 y₀ :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (fun τ => ⟨cantEnd y₀ τ, cantEnd_base y₀ τ⟩)
      ⟨fun _ _ h => cantEnd_injective y₀ (congrArg Subtype.val h), fun e =>
        ⟨(cantEnd_surj y₀ e.1 e.2).choose, Subtype.ext (cantEnd_surj y₀ e.1 e.2).choose_spec⟩⟩)
    ((continuous_cantEnd y₀).subtype_mk _)

/-- **`ex:consider_denote_absolute_galois`, the fibre claim, CORRECTED (DEC-69)**: with
`Γ₂' = ker(π₁(ℂ∖S) → (ℤ/2)^ℕ)` the kernel of the mod-2 windings around the points `1/n`
(`GX.mem_cantGamma_iff`), the fibre above `0` of the completion `Y₂'` of the spread
`Γ₂' \ ord(\widetilde Y^S) → Y` IS a Cantor set. -/
theorem cant_fiber_isCantor : IsCantorSubset (cantFiber0 y₀) :=
  ⟨(cantFiberHomeo y₀).symm.trans cantorSetHomeomorphNatToBool.symm⟩

instance cantGamma_normal : (cantGamma y₀).Normal :=
  ⟨fun g hg h m => by
    show cantEps y₀ m (h * g * h⁻¹) = 1
    rw [cantEps_mul, cantEps_mul, cantEps_inv, hg m, mul_one, ← sq, cantEps_sq]⟩

/-- The refuted reading of DEC-58 sits inside the corrected one: the normal closure `Γ₂` of the
squares `[γₙ]²` is contained in `Γ₂'` (for any `γₙ`). -/
theorem gamma2_le_cantGamma (g : ℕ → AbsGamma y₀) : gamma2 y₀ g ≤ cantGamma y₀ :=
  Subgroup.normalClosure_le_normal (by
    rintro _ ⟨n, rfl⟩ m
    show cantEps y₀ m (g n ^ 2) = 1
    rw [pow_two, cantEps_mul, ← sq, cantEps_sq])

/-- **`ex:consider_denote_absolute_galois`, the fibre claim, corrected (DEC-69)**: `Γ₂'` is the
kernel of the mod-2 windings around the points `1/n` of `S`, and the fibre above `(0,0)` of the
completion `Y₂'` of the spread `Γ₂' \ ord(\widetilde Y^S) → Y` is a Cantor set. -/
theorem absGal_Y₂_fiber_cantor_corrected :
    (∀ γ : Path y₀ y₀, FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ) ∈ cantGamma y₀ ↔
      ∀ n, Even (windAt y₀ _ (cantPt_mem n) γ)) ∧ IsCantorSubset (cantFiber0 y₀) :=
  ⟨mem_cantGamma_iff y₀, cant_fiber_isCantor y₀⟩

/-- `Γ₂' \ ord(\widetilde Y^S) → Y` is a spread (as for `GX.absGal_isSpread_ordY₂Proj`), so `Y₂'`
is the completion of a SPREAD, as the paper says. -/
theorem cant_isSpread_cantProj : IsSpread (cantProj y₀) :=
  isSpread_homeoQuotient_lift (absGal_isSpread_univCoverProj y₀) fun φ hφ x => by
    obtain ⟨ψ, -, rfl⟩ := Subgroup.mem_map.1 hφ
    exact congrArg Subtype.val (congrFun ψ.2 x)

end CantorFibre

/-- **`ex:consider_denote_absolute_galois`** (`RamcovGX.tex:1570`), certified under DEC-69 (the
corrected `Γ₂'`) in the literal reading of "almost trivial" (DEC-55): `ℝ² ∖ S` is NOT
semi-locally simply connected in `ℝ²`; and for every base point, with `Γ₂'` the kernel of the
mod-2 windings around the points `1/n`, `Γ₂' \ ord(\widetilde Y^S) → Y` is a spread and the
fibre above `(0,0)` of its completion `Y₂'` is a Cantor set. -/
theorem absolute_galois_corrected :
    ¬ IsSLSCInCC (fibSᶜ : Set ℂ) ∧ ∀ y₀ : (fibSᶜ : Set ℂ),
      (∀ γ : Path y₀ y₀, FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ) ∈ cantGamma y₀ ↔
        ∀ n, Even (windAt y₀ _ (cantPt_mem n) γ)) ∧ IsSpread (cantProj y₀) ∧
        IsCantorSubset (cantFiber0 y₀) :=
  ⟨absGal_not_isSLSCInCC, fun y₀ => ⟨(absGal_Y₂_fiber_cantor_corrected y₀).1,
    cant_isSpread_cantProj y₀, (absGal_Y₂_fiber_cantor_corrected y₀).2⟩⟩

end GX
