import GX.Branched.Basic
import GX.Topology.UniversalCover
import GX.Singular.Quotient

/-!
# Composition of branched coverings and the maximal branched covering (§3.2, l.1091–1190)

Packages WP-25e, WP-26c, WP-27c (DEC-52, DEC-53). `papers/gx`, `RamcovGX.tex:1091–1190` (and l.684), with the cited results built (DEC-23):
Fox's completion (`GX.Spread.Completion`) and the universal covering
(`GX.Topology.UniversalCover`).

* `prop:branched_covering_composition` — `RamcovGX.tex:1091` — partial, **corrected** (DEC-27):
  `GX.branched_covering_composition` (`q ∘ p` branched ⇔ the *closure* of `q(Y ∖ ord_p(Y))` is
  skeletal, when `q` has finite fibres or `Z₁` is semilocally simply connected); (i) ⇒ (ii):
  `GX.preimage_ordY_comp_subset`, `GX.image_branchingLocus_subset`,
  `GX.isSkeletal_closure_image_branchingLocus`; the printed (i) ⇒ (ii) **refuted** by
  `GX.not_isSkeletal_of_isBranchedCovering_comp`; (ii) ⇒ (i): `GX.isBranchedCovering_comp_of_finite`,
  `GX.isBranchedCovering_comp_of_semilocallySimplyConnected`, the printed (ii)
  `GX.isBranchedCovering_comp_of_isSkeletal`, the gap isolated in
  `GX.isBranchedCovering_comp_of_isCoveringMap`; composition of spreads `GX.IsSpread.comp`.
* **`rem:completion_covering`** — `RamcovGX.tex:1147`: `GX.completion_covering`,
  `GX.completion_covering_unique`, `GX.IsBranchedCovering.isSpreadCompletion_preimage`.
* **`prop:universality`** — `RamcovGX.tex:1158`: `GX.MaxBranchedCover` (`\widetilde Y^S`, the
  Fox completion of `\widetilde{Y∖S} → Y`), `GX.maxBranched_isBranchedCovering`,
  `GX.maxBranched_universal`, `GX.maxBranched_isMaximal` (`GX.IsMaximalPossiblyBranched`),
  `GX.IsMaximalPossiblyBranched.nonempty_homeomorph`, `GX.maxBranched_unique`.
* **`rem:one_could_sum_up`** — `RamcovGX.tex:1164`, read under DEC-46(d) (the equivalence of
  categories is its object and morphism correspondences): objects — the completion of a connected
  covering of a portly `O` is a covering possibly branched over `Y ∖ O`
  (`GX.isBranchedCovering_of_isSpreadCompletion`; a completion exists,
  `GX.isSpreadCompletion_ends_of_isCoveringMap`), and every covering possibly branched over
  `Y ∖ O` restricts to a connected covering of `O` of which it is the completion
  (`GX.IsBranchedCovering.restrict_isCoveringMap`); morphisms — completion is a bijection from the
  covering morphisms over `O` to the morphisms over `Y`, characterised by extension
  `GX.completion_hom_equiv`, functorial (`GX.completion_hom_ext`, `GX.completion_hom_id`,
  `GX.completion_hom_comp`), and such a morphism is itself a branched covering
  `GX.isBranchedCovering_of_comm`.
* **`rem:considering_maximal_covering_possibly`** — `RamcovGX.tex:1176`:
  `GX.sphere2_maxBranched_trivial` (`𝕊²`, `S` a point), from the general
  `GX.maxBranched_trivial_of_simplyConnected`; `GX.isSkeletal_sphere2_singleton`.
* **`cex:proposition_prop_branched_covering`** — `RamcovGX.tex:1181` — closed in the corrected
  form ruled by DEC-53 (with `α = 1`, the reading ruled by DEC-46(e)): the printed "`S` is
  skeletal and `Y ∖ S` is semi-locally simply connected" (l.1184) is false and is corrected to
  `S ∪ {apex}` (the correction recorded as a finding): `GX.cexS_not_isSkeletal` (the paper's
  `S` is not skeletal: the apex is in its closure), `GX.dense_qDisc_image_cexS` (`q(S)` dense),
  `GX.isBranchedCovering_qDisc`
  (`q : 𝔻_∞ → 𝔻` a branched covering), the core `GX.not_isBranchedCovering_qDisc_comp`, and the
  **corrected counterexample** `GX.cex_branched_covering_composition` (`S' = S ∪ {apex}` is skeletal,
  `𝔻_∞ ∖ S'` semilocally simply connected, and for every base point the maximal covering `p`
  possibly branched over `S'` has branching locus **exactly** `S'`, so
  `q(Y ∖ ord_p(Y)) = q(S) ∪ {0} ≠ q(S)` — the printed equality of l.1186 is false and holds only
  with `S ∪ {apex}`, a finding — and `q ∘ p` is not a branched covering), built on
  `GX.exists_branched_over` / `GX.logChart_mem_branchingLocus` (a covering of `𝔻_∞` branched at a
  prescribed discrete set; the loop around a branch point detected by the exponential covering,
  `GX.not_homotopic_refl_of_exp_lift`); `GX.exists_isDenseFamilyY₀` (the paper's data exist).
* **`rem:previous_examples_instances_developing`** — `RamcovGX.tex:684` — closed in the corrected
  form ruled by DEC-52 ("branched over `π{r=0} ⊇ sing(M)`"), its certificate spanning this module
  and `GX.Singular.Quotient`: the assembled statement
  `GX.previous_examples_instances_developing_ruled` (`M` a singular `(G,X)`-manifold with
  `sing(M) ⊆ π{r=0}`, `D` a developing map on `{r > 0}`, the cylinder branched over exactly
  `π{r=0}` — `GX.branchingLocus_orbitMk_cyl` — and the maximal covering of `M` possibly branched
  over `π{r = 0}`, the Fox completion of the universal covering of `π{r > 0}` —
  `GX.previous_examples_foxCompletion`), on `GX.Singular.Quotient`'s `GX.quotientBase_ruled`,
  `GX.previous_examples_developing`, `GX.previous_examples_universalCover` and on
  `GX.previous_examples_maxBranched` (the cylinder `𝔻_∞ × Z → M = Γ_α\(𝔻_∞ × Z)` of
  `ex:quotient_base`, `Z` a real normed space, is the maximal covering of `M` possibly branched
  over `π{r = 0}`, isomorphic over `M` to `\widetilde M^{π{r=0}}`), on
  `GX.isBranchedCovering_orbitMk_cyl` (a branched covering possibly branched over `π{r = 0}`),
  `GX.compl_image_axis`, `GX.cyl_instances`, `GX.previous_examples_universalCover_of_eq`,
  `GX.setOf_r_eq_zero_cyl`; general
  `GX.IsBranchedCovering.comp_homeomorph`, `GX.locPathConnectedSpace_prod_of`.

> Let $X\xrightarrow{p} Y \xrightarrow{q} Z$ be two branched coverings. Then the following are
> equivalent: (i) $X\xrightarrow{q\circ p} Z$ is a branched covering, (ii) $q(Y\setminus
> \ord_p(Y))$ is skeletal in $Z$.
>
> Let $X\xrightarrow{p} Y$ be a branched covering and $\U\subset Y$ some portly subset. The
> spread $X\rightarrow Y$ is isomorphic to the completion of $p^{-1}(\U)\rightarrow Y$.
>
> Let $Y$ be a connected, locally path-connected, Hausdorff topological space. Let $S$ be a
> skeletal subset of $Y$. If $Y\setminus S$ is semi-locally simply connected then there exists a
> covering $\widetilde Y^S$ of $Y$ possibly branched over $S$ which is maximal among such branched
> covering. Furthermore, $\widetilde Y^S$ is unique up to isomorphism and universal in the sense
> that for any covering $X\xrightarrow{p} Y$ possibly branched over $S$, there exists a covering
> $\widetilde Y^S\rightarrow X$ possibly branched over $p^{-1}(S)$.
>
> One could sum up the proof below by saying Fox completion induces a category equivalence
> between the category of covering of $Y\setminus S$ and the category of covering of $Y$ possibly
> branched over $S$.
>
> […] One can consider the example where $Y=\mathbb S^2$ the 2-dimensionnal sphere and $S$ is a
> singleton, since the complement of a point is simply connected, the maximal covering of
> $\mathbb S^2$ possibly branched above $S$ is trivial and the branching locus is empty.
>
> Consider $Z=\DD$, $Y=\DD_\infty$ with $Y\xrightarrow{q} Z$ the quotient map which is a
> branched covering. Consider $Y_0 = \{(r,\theta) ~|~ \theta \in ]0,1[\}$ and choose
> $(r_n,\theta_n)_{n\in \ZZ}$ a countable dense family in $Y_0$. Consider $S :=
> (r_n,\theta_n+n)_{n\in \ZZ}$. We see that $S$ is skeletal and that $Y\setminus S$ is
> semi-locally simply connected. […] Notice that $q(Y\setminus \ord_p(Y)) = q(S)$ is dense in
> $Z$ hence not skeletal, therefore the composition $q\circ p$ is not a branched covering.
>
> The previous examples are instances of developing maps defined on the universal covering of
> some singular space branched over its singular locus. (l.684)

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| §3 standing: spaces Hausdorff, locally path-connected, first countable | ⚠ weakened: each theorem carries what its proof uses |
| `prop:…composition` (i) ⇒ (ii): standing | ⚠ weakened: `Y` T2, LPC, first countable; `Z` T1, LPC, first countable; nothing on `X` |
| `prop:…composition` (ii) ⇒ (i): standing | ✓ carried: `X`, `Y`, `Z` T2, LPC; `Z` first countable (`Y` first countable not used) |
| `prop:…composition` (ii) ⇒ (i): (implicit) composite of coverings is a covering | ⚠ strengthened: `q` finite fibres **or** `Z₁` semilocally simply connected (finding) |
| `prop:…composition`: (ii) "`q(Y∖ord_p(Y))` skeletal" | ⚠ corrected: its closure skeletal (finding); the printed (ii) implies (i) |
| `rem:completion_covering` | ⚠ weakened: none for the completion; `X` T0, `Y` T2 and locally connected for uniqueness |
| `prop:universality`: `Y` connected, LPC, Hausdorff, `S` skeletal, `Y ∖ S` SLSC | ✓ carried; `Y` first countable carried (§3 standing, `RamcovGX.tex:810`; used for the completion's local path-connectedness and `lem:complete_path_carac`) |
| `prop:universality`: competitors `X` | ✓ carried: T2, LPC, first countable |
| `rem:considering…`: `𝕊²`, `S` a singleton | ✓ |
| `cex:…`: "`S` is skeletal", "`Y ∖ S` semilocally simply connected" | ✓ ruled corrected form (DEC-53): `S ∪ {apex}`; the printed first claim is false (`GX.cexS_not_isSkeletal`, a finding); l.1186 "`q(Y∖ord_p(Y)) = q(S)`" is false, it is `q(S) ∪ {0}` (`GX.cex_branched_covering_composition`, a finding) |
| `cex:…`: `α` unspecified | ✓ ruled reading `α = 1` (DEC-46(e)) |
| `rem:one_could_sum_up`: completions of coverings of `O` | ✓ carried: `Y` T2, LPC, first countable; `O` portly; the target covering connected and surjective, completions T2, the target's LPC (the source covering: nothing) |
| `rem:previous_examples…`: `cyl{n} = 𝔻_∞ × ℝ^n`, `Γ_α` | ✓ `𝔻_∞ × Z`, `Z` any real normed space, every `α ≠ 0` |
| `rem:previous_examples…`: `D` a local homeomorphism on `{r > 0}`, `Γ_α` by a.e. morphisms | ✓ carried (`hD`, `hΓ`, as in `ex:quotient_base`); `(G,X)`: `IsRigidAction`, `X` T2 and locally connected |
| `rem:previous_examples…`: "branched over its singular locus" | ✓ ruled corrected form (DEC-52): branched over `π{r=0} ⊇ sing(M)` — branching locus exactly `π{r=0}`, `sing(M) ⊆ π{r=0}`; the printed equality refuted (`quotientBase_counterexample`, a finding) |

## SCOPE (disclosed)

* "Covering" is a surjective covering map (DEC-40); "semilocally simply connected" is DEC-41's
  (`GX.SemilocallySimplyConnected`, loops in `U` null-homotopic in the space).
* `prop:branched_covering_composition`. The paper's (i) ⇒ (ii) proves `q(Y∖ord_p(Y)) ⊆
  Z∖ord_{q∘p}(Z)` (here in full, with the "argumentation alike `lem:spread_partial_covering`"
  replaced by `GX.subset_of_injOn_image_subset`) and then claims a subset of a skeletal set is
  skeletal, which needs it closed; the true conclusion is that the closure is skeletal. The
  (ii) ⇒ (i) step "composition of covering hence a covering" (`RamcovGX.tex:1137`) is false for
  coverings in general; the proof here goes through with either of the two standard hypotheses
  (`GX.isCoveringMap_comp_of_finite`, `GX.isCoveringMap_comp_of_semilocallySimplyConnected`).
  The failure of the printed (i) ⇒ (ii) is formalized (`GX.not_isSkeletal_of_isBranchedCovering_comp`:
  `q(Y ∖ ord_p(Y)) = {(1 + ε) e^{2πiε}}` accumulates at `1`, while its closure is countable, hence
  skeletal, and `q ∘ p` is branched); the necessity of the added hypothesis for (ii) ⇒ (i) is
  **not** formalized.
* `prop:universality`. `\widetilde Y^S` is built from a base point `y₀ ∈ Y ∖ S` (the universal
  cover is based). "Maximal" is `GX.IsMaximalPossiblyBranched`: dominates, by a branched covering
  over `Y`, every covering possibly branched over `S` (Hausdorff, LPC, first countable total
  space, in a fixed universe). Uniqueness is proved in a stronger form: any covering possibly
  branched over `S` admitting a continuous map over `Y` to `\widetilde Y^S` is isomorphic to it.
* `rem:one_could_sum_up` (DEC-46(d)): "category equivalence" is read as its object and morphism
  correspondences, both proved: the category of coverings of `O = Y ∖ S` is that of connected,
  surjective coverings of the portly `O` with continuous maps over `O`, the category of coverings
  possibly branched over `S` that of branched coverings with continuous maps over `Y`. Functoriality
  is proved from the characterisation `Φ F ∘ ι₁ = ι₂ ∘ F` and the density of `range ι₁`:
  `GX.completion_hom_id` (identities) and `GX.completion_hom_comp` (composites), via
  `GX.completion_hom_ext`; no `CategoryTheory.Equivalence` is built.
* `cex:proposition_prop_branched_covering` (closed under DEC-53; `α = 1` ruled by DEC-46(e)):
  `𝔻 = Γ₁\𝔻_∞` is
  identified with `ℂ` by `GX.discHomeomorph`, and `q` is `(r, θ) ↦ r e^{2πiθ}` (`α = 1`, the ruled
  reading, which is what `θ_n + n` needs).
  The paper's `S` accumulates at the apex, so it is not closed, not skeletal, and
  `prop:universality` does not apply to it; the corrected construction uses `S ∪ {apex}`. This is
  a correction of the paper's construction, not a reading; DEC-53 rules it (`S ∪ {apex}`), under
  which the row closes, the correction recorded. The
  core implication (a branching locus with dense image makes `q ∘ p` non-branched) is proved for
  every branched covering `p`. "`Y ∖ S` is semi-locally simply connected" (for the paper's `S`) is
  also false at the apex; this is not formalized (it is not needed once `S ∪ {apex}` is used).
  The printed equality "`q(Y∖ord_p(Y)) = q(S)`" (l.1186) is false as printed: the branching locus is
  closed and contains `S`, hence the apex, so it is exactly `S ∪ {apex}` and
  `q(Y∖ord_p(Y)) = q(S) ∪ {0} ≠ q(S)` (both proved in `cex_branched_covering_composition`); under
  DEC-53's `S ∪ {apex}` the equality holds with `S ∪ {apex}` in place of `S`, and the argument
  (density, hence non-skeletality of the closure) is unaffected. The statement is proved for
  **every** base point `y₀ ∉ S ∪ {apex}` (and the complement is non-empty).
* `rem:previous_examples_instances_developing` (closed under DEC-52): "the universal covering of
  `M` branched over its singular locus" is, in the ruled corrected form, the covering of `M`
  branched over `π{r = 0} ⊇ sing(M)`, read as the maximal covering of `M` possibly branched over
  `π{r = 0}` (`prop:universality`: the Fox completion of the universal covering of `π{r > 0}`),
  and proved for the cylinder in one statement, `previous_examples_instances_developing_ruled`:
  `sing(M) ⊆ π{r = 0}` (from `GX.Singular.Quotient`), `D` a developing map on `{r > 0}`, branching
  locus exactly `π{r = 0}`, `IsMaximalPossiblyBranched`, a completion (`IsSpreadCompletion`) of
  the universal covering of `π{r > 0}`, isomorphic over `M` to `MaxBranchedCover`. "Branched over
  its **singular locus**" as printed is false (`quotientBase_counterexample`: `α = 2π`,
  `sing(M) = ∅`, the covering branched at the apex), a finding. "Instances of developing maps" is
  read for `ex:quotient_base` (`𝔻_∞ × ℝ^{n-2}`, every `D`, `α`), hence for its listed
  specialisations; the tachyon/photon and polyhedral sentences of l.682–683 carry no determinate
  statement (`GX.Singular.Quotient`, SCOPE (c)).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/
noncomputable section

open Set Filter Topology Function unitInterval

namespace GX

attribute [local instance] Classical.propDecidable

set_option linter.unusedSectionVars false

universe u w

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-! ### General lemmas on spreads and coverings -/

/-- A composite of spreads is a spread (`RamcovGX.tex:1100`, "composition of spread is a
spread"). -/
theorem IsSpread.comp {p : X → Y} {q : Y → Z} (hq : IsSpread q) (hp : IsSpread p) :
    IsSpread (q ∘ p) := by
  haveI := hp.locallyConnectedSpace
  refine isSpread_iff_of_locallyConnectedSpace.2 ⟨hq.continuous.comp hp.continuous, ?_⟩
  intro x O hO hxO
  obtain ⟨V, hV, hxV, hsub⟩ := (isSpread_iff.1 hp).2.2 x O hO hxO
  obtain ⟨W, hW, hxW, hsub'⟩ := (isSpread_iff.1 hq).2.2 (p x) V hV hxV
  refine ⟨W, hW, hxW, ?_⟩
  refine Subset.trans ?_ hsub
  refine isPreconnected_connectedComponentIn.subset_connectedComponentIn
    (mem_connectedComponentIn hxW) fun z hz => ?_
  have himg : p '' connectedComponentIn ((q ∘ p) ⁻¹' W) x ⊆ connectedComponentIn (q ⁻¹' W) (p x) :=
    (isPreconnected_connectedComponentIn.image p hp.continuous.continuousOn).subset_connectedComponentIn
      ⟨x, mem_connectedComponentIn hxW, rfl⟩ (image_subset_iff.2 fun z hz =>
        connectedComponentIn_subset ((q ∘ p) ⁻¹' W) x hz)
  exact hsub' (himg ⟨z, hz, rfl⟩)

/-- If `q ∘ Φ` is a spread, `q` and `Φ` continuous, then `Φ` is a spread. -/
theorem IsSpread.of_comp {Φ : X → Y} {q : Y → Z} (h : IsSpread (q ∘ Φ)) (hq : Continuous q)
    (hΦ : Continuous Φ) : IsSpread Φ := by
  haveI := h.locallyConnectedSpace
  refine isSpread_iff_of_locallyConnectedSpace.2 ⟨hΦ, fun x O hO hxO => ?_⟩
  obtain ⟨W, hW, hxW, hsub⟩ := (isSpread_iff.1 h).2.2 x O hO hxO
  exact ⟨q ⁻¹' W, hW.preimage hq, hxW, hsub⟩

/-- A covering map with a locally connected source is a spread. -/
theorem isSpread_of_isCoveringMap [LocallyConnectedSpace X] {f : X → Y}
    (hf : IsCoveringMap f) : IsSpread f := by
  refine isSpread_iff_of_locallyConnectedSpace.2 ⟨hf.continuous, fun x O hO hxO => ?_⟩
  obtain ⟨U, -, hxU, T, hTo, hTi, hTm, -, hTd, hTc⟩ := IsEvenlyCovered.exists_sheets (hf (f x))
  obtain ⟨j, hj⟩ := mem_iUnion.1 (hTc hxU)
  have hx : x ∈ f ⁻¹' (f '' (T j ∩ O)) := ⟨x, ⟨hj, hxO⟩, rfl⟩
  refine ⟨f '' (T j ∩ O), hf.isOpenMap _ ((hTo j).inter hO), hx, ?_⟩
  have hsub : connectedComponentIn (f ⁻¹' (f '' (T j ∩ O))) x ⊆ T j := by
    refine GX.IsPreconnected.subset_of_pairwise_disjoint hTo hTd
      isPreconnected_connectedComponentIn (fun z hz => ?_) ⟨x, mem_connectedComponentIn hx, hj⟩
    apply hTc
    obtain ⟨w, ⟨hwT, -⟩, hwz⟩ := connectedComponentIn_subset _ _ hz
    show f z ∈ U
    rw [← hwz]; exact hTm j hwT
  intro z hz
  obtain ⟨w, ⟨hwT, hwO⟩, hwz⟩ := connectedComponentIn_subset _ _ hz
  have := hTi j hwT (hsub hz) hwz
  rw [← this]; exact hwO

/-- The total space of a covering of a Hausdorff space is Hausdorff. -/
theorem t2Space_of_isCoveringMap [T2Space Y] {f : X → Y} (hf : IsCoveringMap f) :
    T2Space X := by
  refine ⟨fun a b hab => ?_⟩
  by_cases h : f a = f b
  · exact hf.isSeparatedMap a b h hab
  · obtain ⟨u, v, hu, hv, hau, hbv, huv⟩ := t2_separation h
    exact ⟨f ⁻¹' u, f ⁻¹' v, hu.preimage hf.continuous, hv.preimage hf.continuous, hau, hbv,
      huv.preimage f⟩

/-- Two open sets `V`, `V'` of a Hausdorff space, with `q` continuous, open and injective on `V`,
`V'` preconnected meeting `V` and `q(V') ⊆ q(V)`: then `V' ⊆ V`. This replaces the "argumentation
alike the one of Lemma `lem:spread_partial_covering`" of `RamcovGX.tex:1116`. -/
theorem subset_of_injOn_image_subset [T2Space Y] {q : Y → Z} (hqc : Continuous q)
    (hqo : IsOpenMap q) {V V' : Set Y} (hV : IsOpen V) (hV' : IsOpen V')
    (hV'c : IsPreconnected V') (hinj : InjOn q V) (himg : q '' V' ⊆ q '' V)
    (hne : (V' ∩ V).Nonempty) : V' ⊆ V := by
  refine hV'c.subset_of_closure_inter_subset hV hne fun y' ⟨hy'c, hy'V'⟩ => ?_
  obtain ⟨y'', hy''V, hy''⟩ := himg ⟨y', hy'V', rfl⟩
  by_contra hy'V
  have hne' : y' ≠ y'' := fun h => hy'V (h ▸ hy''V)
  obtain ⟨N', N'', hN', hN'', hy'N', hy''N'', hd⟩ := t2_separation hne'
  set N₁ := V' ∩ N' ∩ q ⁻¹' (q '' (N'' ∩ V))
  have hN₁ : IsOpen N₁ := (hV'.inter hN').inter ((hqo _ (hN''.inter hV)).preimage hqc)
  have hy'N₁ : y' ∈ N₁ := ⟨⟨hy'V', hy'N'⟩, ⟨y'', ⟨hy''N'', hy''V⟩, hy''⟩⟩
  obtain ⟨t, ⟨⟨-, htN'⟩, ⟨t'', ⟨ht''N'', ht''V⟩, ht''⟩⟩, htV⟩ :=
    mem_closure_iff.1 hy'c N₁ hN₁ hy'N₁
  have : t'' = t := hinj ht''V htV ht''
  exact disjoint_left.1 hd htN' (this ▸ ht''N'')

/-! ### `prop:branched_covering_composition`, (i) ⇒ (ii) -/

/-- The heart of `prop:branched_covering_composition` (i) ⇒ (ii) (`RamcovGX.tex:1105–1125`):
over an ordinary point of `q ∘ p`, every point of `Y` is ordinary for `p`. No hypothesis on
`q ∘ p` is needed. -/
theorem preimage_ordY_comp_subset [T2Space Y] [LocPathConnectedSpace Y]
    [FirstCountableTopology Y] [LocPathConnectedSpace Z] [FirstCountableTopology Z] [T1Space Z]
    {p : X → Y} {q : Y → Z} (hp : IsBranchedCovering p) (hq : IsBranchedCovering q) :
    q ⁻¹' ordY (q ∘ p) ⊆ ordY p := by
  haveI := hp.isSpread.locallyConnectedSpace
  have hpc := hp.isSpread.continuous
  have hqc := hq.isSpread.continuous
  have hqpc : Continuous (q ∘ p) := hqc.comp hpc
  have hpo := (spread_connected_image hp).1
  have hqo := (spread_connected_image hq).1
  intro y hy
  obtain ⟨U, hU, hzU, -, hcov⟩ := hy
  set U' := connectedComponentIn U (q y)
  have hU'o : IsOpen U' := hU.connectedComponentIn
  have hU'c : IsPreconnected U' := isPreconnected_connectedComponentIn
  have hzU' : q y ∈ U' := mem_connectedComponentIn hzU
  have hcov' : IsEvenlyCoveredSet (q ∘ p) U' :=
    hcov.mono_of_isPreconnected hqpc hU hU'o hU'c (connectedComponentIn_subset _ _)
  -- the image by `p` of a component of `(q ∘ p)⁻¹(U')`
  have hVprop : ∀ a : X, q (p a) ∈ U' →
      IsOpen (p '' connectedComponentIn ((q ∘ p) ⁻¹' U') a) ∧
      IsPreconnected (p '' connectedComponentIn ((q ∘ p) ⁻¹' U') a) ∧
      InjOn q (p '' connectedComponentIn ((q ∘ p) ⁻¹' U') a) ∧
      q '' (p '' connectedComponentIn ((q ∘ p) ⁻¹' U') a) = U' := by
    intro a ha
    refine ⟨hpo _ (hU'o.preimage hqpc).connectedComponentIn,
      isPreconnected_connectedComponentIn.image _ hpc.continuousOn, ?_, ?_⟩
    · rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩ hbc
      rw [hcov'.injOn ha hb hc hbc]
    · rw [image_image]; exact hcov'.image_eq ha
  -- two such images meeting are equal
  have hVeq : ∀ a b : X, q (p a) ∈ U' → q (p b) ∈ U' →
      (p '' connectedComponentIn ((q ∘ p) ⁻¹' U') a ∩
        p '' connectedComponentIn ((q ∘ p) ⁻¹' U') b).Nonempty →
      p '' connectedComponentIn ((q ∘ p) ⁻¹' U') b ⊆ p '' connectedComponentIn ((q ∘ p) ⁻¹' U') a := by
    intro a b ha hb hne
    obtain ⟨hao, -, hai, haim⟩ := hVprop a ha
    obtain ⟨hbo, hbc, -, hbim⟩ := hVprop b hb
    exact subset_of_injOn_image_subset hqc hqo hao hbo hbc hai (by rw [haim, hbim])
      (by rw [inter_comm]; exact hne)
  obtain ⟨x, rfl⟩ := hp.surjective y
  have hx : q (p x) ∈ U' := hzU'
  set V := p '' connectedComponentIn ((q ∘ p) ⁻¹' U') x
  obtain ⟨hVo, -, hVi, hVim⟩ := hVprop x hx
  have hpV : p ⁻¹' V ⊆ (q ∘ p) ⁻¹' U' := fun a ha => by
    show q (p a) ∈ U'
    rw [← hVim]; exact mem_image_of_mem q ha
  -- the components of `p⁻¹(V)` are those of `(q ∘ p)⁻¹(U')`
  have hcc : ∀ a ∈ p ⁻¹' V, connectedComponentIn (p ⁻¹' V) a =
      connectedComponentIn ((q ∘ p) ⁻¹' U') a := by
    intro a ha
    have haU : q (p a) ∈ U' := hpV ha
    have hVa : p '' connectedComponentIn ((q ∘ p) ⁻¹' U') a = V := by
      have h1 := hVeq x a hx haU ⟨p a, ha, a, mem_connectedComponentIn haU, rfl⟩
      obtain ⟨hao, -, hai, haim⟩ := hVprop a haU
      refine Subset.antisymm h1 fun v hv => ?_
      have : q v ∈ q '' p '' connectedComponentIn ((q ∘ p) ⁻¹' U') a := by
        rw [haim, ← hVim]; exact mem_image_of_mem q hv
      obtain ⟨w, hw, hwv⟩ := this
      rwa [hVi (h1 hw) hv hwv] at hw
    refine Subset.antisymm ?_ ?_
    · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn ha) ((connectedComponentIn_subset _ _).trans hpV)
    · refine isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn haU) fun b hb => ?_
      show p b ∈ V
      rw [← hVa]; exact mem_image_of_mem p hb
  refine ⟨V, hVo, ⟨x, mem_connectedComponentIn hx, rfl⟩, ⟨x, ⟨x, mem_connectedComponentIn hx,
    rfl⟩⟩, fun a ha => ?_⟩
  have haU : q (p a) ∈ U' := hpV ha
  rw [hcc a ha]
  refine exists_homeomorph_of_sheet hpc (hU'o.preimage hqpc).connectedComponentIn ?_ ?_
    fun W _ hW => hpo W hW
  · intro b hb c hc hbc
    exact hcov'.injOn haU hb hc (by simp only [comp_apply, hbc])
  · have h1 := hVeq x a hx haU ⟨p a, ha, a, mem_connectedComponentIn haU, rfl⟩
    obtain ⟨-, -, -, haim⟩ := hVprop a haU
    refine Subset.antisymm h1 fun v hv => ?_
    have : q v ∈ q '' p '' connectedComponentIn ((q ∘ p) ⁻¹' U') a := by
      rw [haim, ← hVim]; exact mem_image_of_mem q hv
    obtain ⟨w, hw, hwv⟩ := this
    rwa [hVi (h1 hw) hv hwv] at hw

/-- `prop:branched_covering_composition` (i) ⇒ (ii), the inclusion the paper proves
(`RamcovGX.tex:1129`): `q(Y ∖ ord_p(Y)) ⊆ Z ∖ ord_{q∘p}(Z)`. -/
theorem image_branchingLocus_subset [T2Space Y] [LocPathConnectedSpace Y]
    [FirstCountableTopology Y] [LocPathConnectedSpace Z] [FirstCountableTopology Z] [T1Space Z]
    {p : X → Y} {q : Y → Z} (hp : IsBranchedCovering p) (hq : IsBranchedCovering q) :
    q '' branchingLocus p ⊆ branchingLocus (q ∘ p) := by
  rintro _ ⟨y, hy, rfl⟩ hz
  exact hy (preimage_ordY_comp_subset hp hq hz)

/-- `prop:branched_covering_composition` (i) ⇒ (ii), **corrected** (DEC-27): if `q ∘ p` is a
branched covering, the *closure* of `q(Y ∖ ord_p(Y))` is skeletal. The paper's last step
("the latter is skeletal, thus so is the former", `RamcovGX.tex:1129`) needs the subset to be
closed; a subset of a skeletal set is skeletal only if it is closed. -/
theorem isSkeletal_closure_image_branchingLocus [T2Space Y] [LocPathConnectedSpace Y]
    [FirstCountableTopology Y] [LocPathConnectedSpace Z] [FirstCountableTopology Z] [T1Space Z]
    {p : X → Y} {q : Y → Z} (hp : IsBranchedCovering p) (hq : IsBranchedCovering q)
    (hqp : IsBranchedCovering (q ∘ p)) : IsSkeletal (closure (q '' branchingLocus p)) := by
  have hB : IsSkeletal (branchingLocus (q ∘ p)) := hqp.branching_locii.1
  exact hB.anti (closure_minimal (image_branchingLocus_subset hp hq) hB.isClosed) isClosed_closure

/-! ### `prop:branched_covering_composition`, (ii) ⇒ (i) -/

/-- The portly set `Z₁ = ord_q(Z) ∖ cl(q(Y ∖ ord_p(Y)))` of the proof of (ii) ⇒ (i)
(`RamcovGX.tex:1134`, with the closure of the corrected statement). -/
def compGoodSet (p : X → Y) (q : Y → Z) : Set Z :=
  ordY q ∩ (closure (q '' branchingLocus p))ᶜ

/-- The core of `prop:branched_covering_composition` (ii) ⇒ (i), with the gap of the paper's
proof made a hypothesis: **if** `(q ∘ p)` restricts to a covering over `Z₁` (`hcov`), and the
closure of `q(Y ∖ ord_p(Y))` is skeletal, then `q ∘ p` is a branched covering. The paper's
"composition of covering hence a covering" (`RamcovGX.tex:1137`) is false in general; the two
true forms are `isBranchedCovering_comp_of_finite` and
`isBranchedCovering_comp_of_semilocallySimplyConnected`. -/
theorem isBranchedCovering_comp_of_isCoveringMap [T2Space X] [LocPathConnectedSpace X]
    [T2Space Y] [LocPathConnectedSpace Y] [T2Space Z] [LocPathConnectedSpace Z]
    [FirstCountableTopology Z] {p : X → Y} {q : Y → Z} (hp : IsBranchedCovering p)
    (hq : IsBranchedCovering q) (hB : IsSkeletal (closure (q '' branchingLocus p)))
    (hcov : IsCoveringMap ((compGoodSet p q).restrictPreimage (q ∘ p))) :
    IsBranchedCovering (q ∘ p) := by
  haveI := hp.connectedSpace_source
  have hsp : IsSpread (q ∘ p) := hq.isSpread.comp hp.isSpread
  have hZ₁ : IsPortly (compGoodSet p q) := hq.isPortly_ordY.inter (isSkeletal_iff.1 hB)
  have hY₁ : IsPortly (q ⁻¹' compGoodSet p q) := hq.isPortly_preimage hZ₁
  have hX₁ : IsPortly ((q ∘ p) ⁻¹' compGoodSet p q) := hp.isPortly_preimage hY₁
  have hsurj : Surjective ((compGoodSet p q).restrictPreimage (q ∘ p)) := by
    rintro ⟨z, hz⟩
    obtain ⟨y, rfl⟩ := hq.surjective z
    obtain ⟨x, rfl⟩ := hp.surjective y
    exact ⟨⟨x, hz⟩, rfl⟩
  have hext : PathLiftExtends (q ∘ p) ((q ∘ p) ⁻¹' compGoodSet p q) (compGoodSet p q) := by
    intro γ _ f hf _ hfγ
    obtain ⟨g₁, hg₁, hg₁f⟩ := exists_extend_path_of_isCompleteSpread hq.isSpread hq.isComplete γ
      (p ∘ f) (hp.isSpread.continuous.comp_continuousOn hf) hfγ
    obtain ⟨g, hg, hgf⟩ := exists_extend_path_of_isCompleteSpread hp.isSpread hp.isComplete g₁ f
      hf fun t ht => (hg₁f t ht).symm
    exact ⟨g, fun t => by simp only [comp_apply, hg, hg₁], hgf⟩
  have h := complete_path_carac.{0} hsp hX₁ hZ₁ (mapsTo_preimage _ _) hcov hsurj
  exact (h.out 3 0).1 hext

/-- The preimage of `Z₁` lies in the ordinary locus of `p`. -/
theorem preimage_compGoodSet_subset_ordY {p : X → Y} {q : Y → Z} :
    q ⁻¹' compGoodSet p q ⊆ ordY p := fun y hy => by
  by_contra h
  exact hy.2 (subset_closure ⟨y, h, rfl⟩)

/-- The two coverings `X₁ → Y₁ → Z₁` of the proof of (ii) ⇒ (i). -/
theorem isCoveringMap_restrict_compGoodSet [LocallyConnectedSpace X] [LocallyConnectedSpace Y]
    {p : X → Y} {q : Y → Z} (hpc : Continuous p) (hqc : Continuous q) :
    IsCoveringMap ((compGoodSet p q).restrictPreimage q) ∧
      IsCoveringMap ((q ⁻¹' compGoodSet p q).restrictPreimage p) :=
  ⟨((isCoveringMapOn_ordY hqc).mono inter_subset_left).isCoveringMap_restrictPreimage,
    ((isCoveringMapOn_ordY hpc).mono preimage_compGoodSet_subset_ordY).isCoveringMap_restrictPreimage⟩

/-- **`prop:branched_covering_composition` (ii) ⇒ (i), finite-fibre form.** If `q` has finite
fibres and the closure of `q(Y ∖ ord_p(Y))` is skeletal, `q ∘ p` is a branched covering. -/
theorem isBranchedCovering_comp_of_finite [T2Space X] [LocPathConnectedSpace X]
    [T2Space Y] [LocPathConnectedSpace Y] [T2Space Z] [LocPathConnectedSpace Z]
    [FirstCountableTopology Z] {p : X → Y} {q : Y → Z} (hp : IsBranchedCovering p)
    (hq : IsBranchedCovering q) (hB : IsSkeletal (closure (q '' branchingLocus p)))
    (hfin : ∀ z, (q ⁻¹' {z}).Finite) : IsBranchedCovering (q ∘ p) := by
  obtain ⟨hcq, hcp⟩ := isCoveringMap_restrict_compGoodSet (p := p) (q := q)
    hp.isSpread.continuous hq.isSpread.continuous
  have hfin' : ∀ z, ((compGoodSet p q).restrictPreimage q ⁻¹' {z}).Finite := fun z => by
    refine ((hfin z).preimage Subtype.val_injective.injOn).subset fun y hy => ?_
    show (y : Y) ∈ q ⁻¹' {(z : Z)}
    have := congrArg Subtype.val (show (compGoodSet p q).restrictPreimage q y = z from hy)
    exact this
  have hc := isCoveringMap_comp_of_finite hcq hcp hfin'
  exact isBranchedCovering_comp_of_isCoveringMap hp hq hB hc

/-- **`prop:branched_covering_composition` (ii) ⇒ (i), semilocally simply connected form.** If
`Z₁ = ord_q(Z) ∖ cl(q(Y ∖ ord_p(Y)))` is semilocally simply connected and the closure of
`q(Y ∖ ord_p(Y))` is skeletal, `q ∘ p` is a branched covering. -/
theorem isBranchedCovering_comp_of_semilocallySimplyConnected [T2Space X]
    [LocPathConnectedSpace X] [T2Space Y] [LocPathConnectedSpace Y] [T2Space Z]
    [LocPathConnectedSpace Z] [FirstCountableTopology Z] {p : X → Y} {q : Y → Z}
    (hp : IsBranchedCovering p) (hq : IsBranchedCovering q)
    (hB : IsSkeletal (closure (q '' branchingLocus p)))
    (hZ₁ : SemilocallySimplyConnected (compGoodSet p q)) : IsBranchedCovering (q ∘ p) := by
  obtain ⟨hcq, hcp⟩ := isCoveringMap_restrict_compGoodSet (p := p) (q := q)
    hp.isSpread.continuous hq.isSpread.continuous
  have hZ₁o : IsOpen (compGoodSet p q) := isOpen_ordY.inter isClosed_closure.isOpen_compl
  haveI : LocPathConnectedSpace (compGoodSet p q) := hZ₁o.locPathConnectedSpace
  have hc := isCoveringMap_comp_of_semilocallySimplyConnected hcq hcp hZ₁
  exact isBranchedCovering_comp_of_isCoveringMap hp hq hB hc

/-- **`prop:branched_covering_composition`** (`RamcovGX.tex:1091`), **corrected** (DEC-27).
For branched coverings `p : X → Y`, `q : Y → Z` (Hausdorff, locally path-connected, first
countable), under either `q` has finite fibres or `Z₁` is semilocally simply connected:
`q ∘ p` is a branched covering **iff the closure of** `q(Y ∖ ord_p(Y))` is skeletal. -/
theorem branched_covering_composition [T2Space X] [LocPathConnectedSpace X]
    [T2Space Y] [LocPathConnectedSpace Y] [FirstCountableTopology Y] [T2Space Z]
    [LocPathConnectedSpace Z] [FirstCountableTopology Z] {p : X → Y} {q : Y → Z}
    (hp : IsBranchedCovering p) (hq : IsBranchedCovering q)
    (hcomp : (∀ z, (q ⁻¹' {z}).Finite) ∨ SemilocallySimplyConnected (compGoodSet p q)) :
    IsBranchedCovering (q ∘ p) ↔ IsSkeletal (closure (q '' branchingLocus p)) := by
  refine ⟨isSkeletal_closure_image_branchingLocus hp hq, fun hB => ?_⟩
  rcases hcomp with hfin | hZ₁
  · exact isBranchedCovering_comp_of_finite hp hq hB hfin
  · exact isBranchedCovering_comp_of_semilocallySimplyConnected hp hq hB hZ₁

/-- `prop:branched_covering_composition` (ii) ⇒ (i) **as printed** (with `q(Y ∖ ord_p(Y))`
itself skeletal), under the same alternative. -/
theorem isBranchedCovering_comp_of_isSkeletal [T2Space X] [LocPathConnectedSpace X]
    [T2Space Y] [LocPathConnectedSpace Y] [T2Space Z]
    [LocPathConnectedSpace Z] [FirstCountableTopology Z] {p : X → Y} {q : Y → Z}
    (hp : IsBranchedCovering p) (hq : IsBranchedCovering q)
    (hcomp : (∀ z, (q ⁻¹' {z}).Finite) ∨ SemilocallySimplyConnected (compGoodSet p q))
    (hB : IsSkeletal (q '' branchingLocus p)) : IsBranchedCovering (q ∘ p) := by
  have hB' : IsSkeletal (closure (q '' branchingLocus p)) := by
    rw [hB.isClosed.closure_eq]; exact hB
  rcases hcomp with hfin | hZ₁
  · exact isBranchedCovering_comp_of_finite hp hq hB' hfin
  · exact isBranchedCovering_comp_of_semilocallySimplyConnected hp hq hB' hZ₁

/-! ### `rem:completion_covering` -/

/-- A branched covering is a completion of its restriction over any portly `U ⊆ Y`. -/
theorem IsBranchedCovering.isSpreadCompletion_preimage {p : X → Y} (hp : IsBranchedCovering p)
    {U : Set Y} (hU : IsPortly U) :
    IsSpreadCompletion (p ∘ ((↑) : p ⁻¹' U → X)) p ((↑) : p ⁻¹' U → X) :=
  ⟨hp.isSpread, fun _ => rfl, IsEmbedding.subtypeVal, hp.isComplete, by
    rw [Subtype.range_coe]; exact hp.isPortly_preimage hU⟩

/-- The restriction of a spread to an open subset of the source, as a spread to the base. -/
theorem IsSpread.comp_val {p : X → Y} (hp : IsSpread p) {A : Set X} (hA : IsOpen A) :
    IsSpread (p ∘ ((↑) : A → X)) := by
  haveI := hp.locallyConnectedSpace
  haveI : LocallyConnectedSpace A := hA.locallyConnectedSpace
  exact hp.comp (IsSpread.of_isInducing IsInducing.subtypeVal)

/-- **`rem:completion_covering`** (`RamcovGX.tex:1147`). Let `p : X → Y` be a branched covering
and `U ⊆ Y` portly. Then `p` is a completion of `p⁻¹(U) → Y`, the space of ends of
`p⁻¹(U) → Y` is one too, and `X` is isomorphic to it over `Y` and under `p⁻¹(U)` by a unique
homeomorphism. -/
theorem completion_covering [T0Space X] [T2Space Y] [LocallyConnectedSpace Y] {p : X → Y}
    (hp : IsBranchedCovering p) {U : Set Y} (hU : IsPortly U) :
    IsSpreadCompletion (p ∘ ((↑) : p ⁻¹' U → X)) p ((↑) : p ⁻¹' U → X) ∧
      IsSpreadCompletion (p ∘ ((↑) : p ⁻¹' U → X)) SpreadEnd.base
        (SpreadEnd.ofPoint (p ∘ ((↑) : p ⁻¹' U → X))) ∧
      ∃! φ : X ≃ₜ SpreadEnd (p ∘ ((↑) : p ⁻¹' U → X)),
        (∀ x, (φ x).base = p x) ∧ ∀ x : p ⁻¹' U, φ x = SpreadEnd.ofPoint _ x := by
  have h := hp.isSpreadCompletion_preimage hU
  have hsp := hp.isSpread.comp_val (hU.isOpen.preimage hp.isSpread.continuous)
  have h' := (SpreadEnd.isSpreadCompletion_base_iff hsp).2 h.isOpen_range_ofPoint
  exact ⟨h, h', h.existsUnique_homeomorph h'⟩

/-- `rem:completion_covering`, against every completion: any completion `X'` (T0) of
`p⁻¹(U) → Y` is isomorphic to `X` over `Y` and under `p⁻¹(U)`, by a unique homeomorphism. -/
theorem completion_covering_unique [T0Space X] [T2Space Y] [LocallyConnectedSpace Y]
    {p : X → Y} (hp : IsBranchedCovering p) {U : Set Y} (hU : IsPortly U) {X' : Type*}
    [TopologicalSpace X'] [T0Space X'] {p' : X' → Y} {ι : p ⁻¹' U → X'}
    (h' : IsSpreadCompletion (p ∘ ((↑) : p ⁻¹' U → X)) p' ι) :
    ∃! φ : X ≃ₜ X', (∀ x, p' (φ x) = p x) ∧ ∀ x : p ⁻¹' U, φ x = ι x :=
  (hp.isSpreadCompletion_preimage hU).existsUnique_homeomorph h'

/-! ### Fox completion of coverings of a portly subset (`rem:one_could_sum_up`) -/

/-- A covering of an open `O ⊆ Y` (locally connected), followed by the inclusion, is a spread. -/
theorem isSpread_coe_comp_of_isCoveringMap [LocallyConnectedSpace Y] {O : Set Y} (hO : IsOpen O)
    {E : Type*} [TopologicalSpace E] [LocallyConnectedSpace E] {π : E → O}
    (hπ : IsCoveringMap π) : IsSpread (fun e => (π e : Y)) := by
  haveI : LocallyConnectedSpace O := hO.locallyConnectedSpace
  exact (IsSpread.of_isInducing IsInducing.subtypeVal).comp (isSpread_of_isCoveringMap hπ)

/-- **The completion of a connected covering of a portly `O` is a branched covering possibly
branched over `Y ∖ O`**, and the preimage of `O` is exactly the image of the covering. Any
completion in the paper's sense, Hausdorff and locally path-connected. -/
theorem isBranchedCovering_of_isSpreadCompletion [T2Space Y] [LocPathConnectedSpace Y]
    [FirstCountableTopology Y] {O : Set Y} (hO : IsPortly O) {E : Type*} [TopologicalSpace E]
    [ConnectedSpace E] {π : E → O} (hπ : IsCoveringMap π) (hπs : Surjective π) {X' : Type*}
    [TopologicalSpace X'] [T2Space X'] [LocPathConnectedSpace X'] {p' : X' → Y} {ι : E → X'}
    (h : IsSpreadCompletion (fun e => (π e : Y)) p' ι) :
    IsBranchedCovering p' ∧ IsPossiblyBranchedOver p' Oᶜ ∧ p' ⁻¹' O = range ι := by
  haveI : ConnectedSpace X' := connectedSpace_iff_univ.2 (by
    rw [← h.isPortly.dense.closure_eq]; exact (isConnected_range h.isEmbedding.continuous).closure)
  have hmaps : MapsTo p' (range ι) O := by
    rintro _ ⟨e, rfl⟩
    show p' (ι e) ∈ O
    rw [h.comm]; exact (π e).2
  set φ := h.isEmbedding.toHomeomorph
  have hres : hmaps.restrict p' (range ι) O = π ∘ φ.symm := by
    funext w
    obtain ⟨e, rfl⟩ := φ.surjective w
    rw [comp_apply, φ.symm_apply_apply]
    exact Subtype.ext (h.comm e)
  have hcov : IsCoveringMap (hmaps.restrict p' (range ι) O) := hres ▸ hπ.comp_homeomorph φ.symm
  have hsurj : Surjective (hmaps.restrict p' (range ι) O) := hres ▸ hπs.comp φ.symm.surjective
  obtain ⟨hO1, -, hO3⟩ := spread_partial_covering h.isSpread.continuous h.isPortly hO.isOpen
    hmaps hcov hsurj
  have hbc := ((complete_path_carac.{0} h.isSpread h.isPortly hO hmaps hcov hsurj).out 1 0).1
    h.isComplete
  exact ⟨hbc, compl_subset_compl.2 hO1, hO3⟩

/-- **The space of ends of a covering of a portly `O`** is a completion in the paper's sense. -/
theorem isSpreadCompletion_ends_of_isCoveringMap [T2Space Y] [LocallyConnectedSpace Y]
    {O : Set Y} (hO : IsPortly O) {E : Type*} [TopologicalSpace E] [LocallyConnectedSpace E]
    {π : E → O} (hπ : IsCoveringMap π) (hπs : Surjective π) :
    IsSpreadCompletion (fun e => (π e : Y)) SpreadEnd.base
      (SpreadEnd.ofPoint (fun e => (π e : Y))) := by
  haveI : T2Space E := t2Space_of_isCoveringMap hπ
  have hsp := isSpread_coe_comp_of_isCoveringMap hO.isOpen hπ
  have hmaps : MapsTo (fun e => (π e : Y)) univ O := fun e _ => (π e).2
  have hres : hmaps.restrict _ univ O = π ∘ Homeomorph.Set.univ E := funext fun _ => rfl
  have hcov : IsCoveringMap (hmaps.restrict _ univ O) :=
    hres ▸ hπ.comp_homeomorph (Homeomorph.Set.univ E)
  have hsurj : Surjective (hmaps.restrict _ univ O) :=
    hres ▸ hπs.comp (Homeomorph.Set.univ E).surjective
  refine SpreadEnd.isSpreadCompletion_base_of_subset_ordY hsp hO.isOpen ?_
    (spread_partial_covering hsp.continuous isPortly_univ hO.isOpen hmaps hcov hsurj).1
  rintro _ ⟨e, rfl⟩; exact (π e).2

/-- **A branched covering possibly branched over `Y ∖ O` restricts to a connected covering of
`O` of which it is a completion** (the inverse direction of `rem:one_could_sum_up`). -/
theorem IsBranchedCovering.restrict_isCoveringMap {p : X → Y} (hp : IsBranchedCovering p)
    {O : Set Y} (hO : IsPortly O) (hOp : O ⊆ ordY p) :
    IsCoveringMap (O.restrictPreimage p) ∧ Surjective (O.restrictPreimage p) ∧
      ConnectedSpace (p ⁻¹' O) ∧
      IsSpreadCompletion (fun e => (O.restrictPreimage p e : Y)) p ((↑) : p ⁻¹' O → X) := by
  haveI := hp.isSpread.locallyConnectedSpace
  haveI := hp.connectedSpace_source
  refine ⟨((isCoveringMapOn_ordY hp.isSpread.continuous).mono hOp).isCoveringMap_restrictPreimage,
    fun y => ?_, isConnected_iff_connectedSpace.1 (hp.isPortly_preimage hO).isConnected,
    hp.isSpreadCompletion_preimage hO⟩
  obtain ⟨x, hx⟩ := hp.surjective y
  exact ⟨⟨x, show p x ∈ O by rw [hx]; exact y.2⟩, Subtype.ext hx⟩

/-- **Morphisms** (`rem:one_could_sum_up`, `prop:universality`): a continuous `G : X₁ → X₂` over
`Y` between branched coverings possibly branched over `Y ∖ O`, restricting to a surjective
covering `p₁⁻¹(O) → p₂⁻¹(O)`, is itself a branched covering, possibly branched over
`p₂⁻¹(Y ∖ O)`. -/
theorem isBranchedCovering_of_comm [T2Space X] [LocPathConnectedSpace X] [T2Space Z]
    [LocPathConnectedSpace Z] [FirstCountableTopology Z] [T1Space Y] [LocallyConnectedSpace Y]
    {O : Set Y} (hO : IsPortly O) {p₁ : X → Y} {p₂ : Z → Y} (hp₁ : IsBranchedCovering p₁)
    (hp₂ : IsBranchedCovering p₂) {G : X → Z} (hG : Continuous G) (hcomm : ∀ x, p₂ (G x) = p₁ x)
    (hmaps : MapsTo G (p₁ ⁻¹' O) (p₂ ⁻¹' O))
    (hcov : IsCoveringMap (hmaps.restrict G (p₁ ⁻¹' O) (p₂ ⁻¹' O)))
    (hsurj : Surjective (hmaps.restrict G (p₁ ⁻¹' O) (p₂ ⁻¹' O))) :
    IsBranchedCovering G ∧ IsPossiblyBranchedOver G (p₂ ⁻¹' Oᶜ) := by
  haveI := hp₁.connectedSpace_source
  have hsp : IsSpread G := by
    have : p₂ ∘ G = p₁ := funext hcomm
    exact IsSpread.of_comp (this ▸ hp₁.isSpread) hp₂.isSpread.continuous hG
  have hX₁ := hp₁.isPortly_preimage hO
  have hZ₁ := hp₂.isPortly_preimage hO
  have hext : PathLiftExtends G (p₁ ⁻¹' O) (p₂ ⁻¹' O) := by
    intro γ _ f hf _ hfγ
    obtain ⟨g, hg, hgf⟩ := exists_extend_path_of_isCompleteSpread hp₁.isSpread hp₁.isComplete
      ((⟨p₂, hp₂.isSpread.continuous⟩ : C(Z, Y)).comp γ) f hf fun t ht => by
        show p₁ (f t) = p₂ (γ t)
        rw [← hcomm, hfγ t ht]
    have : (G ∘ g : I → Z) = γ := Continuous.ext_on dense_setOf_lt_one (hG.comp g.continuous)
      γ.continuous fun t ht => by
        show G (g t) = γ t
        rw [hgf t ht, hfγ t ht]
    exact ⟨g, fun t => congrFun this t, hgf⟩
  have hbc := ((complete_path_carac.{0} hsp hX₁ hZ₁ hmaps hcov hsurj).out 3 0).1 hext
  obtain ⟨h1, -, -⟩ := spread_partial_covering hsp.continuous hX₁ hZ₁.isOpen hmaps hcov hsurj
  refine ⟨hbc, fun z hz => ?_⟩
  show p₂ z ∈ Oᶜ
  exact fun hzO => hz (h1 hzO)

/-- **`rem:one_could_sum_up`, the morphism correspondence** (`RamcovGX.tex:1164`, read under
DEC-46(d)): for connected coverings `π₁ : E₁ → O`, `π₂ : E₂ → O` of a portly `O ⊆ Y` with
completions `X₁`, `X₂`, Fox completion is a bijection from the morphisms of coverings
`E₁ → E₂` over `O` to the morphisms `X₁ → X₂` over `Y`; the image of `F` is the unique continuous
map over `Y` extending it (`ι₂ ∘ F = Φ F ∘ ι₁`); by that characterisation the correspondence
preserves identities and composites (`GX.completion_hom_id`, `GX.completion_hom_comp`). -/
theorem completion_hom_equiv [T2Space Y] [LocPathConnectedSpace Y] [FirstCountableTopology Y]
    {O : Set Y} (hO : IsPortly O) {E₁ E₂ : Type*} [TopologicalSpace E₁] [TopologicalSpace E₂]
    [ConnectedSpace E₂] {π₁ : E₁ → O} {π₂ : E₂ → O} (hπ₂ : IsCoveringMap π₂)
    (hπ₂s : Surjective π₂) {X₁ X₂ : Type*} [TopologicalSpace X₁] [TopologicalSpace X₂]
    [T2Space X₁] [T2Space X₂] [LocPathConnectedSpace X₂] {p₁ : X₁ → Y} {p₂ : X₂ → Y}
    {ι₁ : E₁ → X₁} {ι₂ : E₂ → X₂} (h₁ : IsSpreadCompletion (fun e => (π₁ e : Y)) p₁ ι₁)
    (h₂ : IsSpreadCompletion (fun e => (π₂ e : Y)) p₂ ι₂) :
    ∃ Φ : {F : E₁ → E₂ // Continuous F ∧ ∀ e, π₂ (F e) = π₁ e} ≃
        {G : X₁ → X₂ // Continuous G ∧ ∀ x, p₂ (G x) = p₁ x},
      ∀ F e, (Φ F : X₁ → X₂) (ι₁ e) = ι₂ ((F : E₁ → E₂) e) := by
  have hpre := (isBranchedCovering_of_isSpreadCompletion hO hπ₂ hπ₂s h₂).2.2
  have hext : ∀ F : {F : E₁ → E₂ // Continuous F ∧ ∀ e, π₂ (F e) = π₁ e},
      ∃! G : X₁ → X₂, Continuous G ∧ (∀ x, p₂ (G x) = id (p₁ x)) ∧
        ∀ e, G (ι₁ e) = ι₂ (F.1 e) := fun F =>
    h₁.toIsFoxCompletion.existsUnique_extend h₂.toIsFoxCompletion continuous_id F.2.1
      fun e => by simp only [F.2.2, id]
  -- the restriction of a morphism of completions
  have hres : ∀ G : {G : X₁ → X₂ // Continuous G ∧ ∀ x, p₂ (G x) = p₁ x}, ∀ e,
      G.1 (ι₁ e) ∈ range ι₂ := fun G e => by
    rw [← hpre]
    show p₂ (G.1 (ι₁ e)) ∈ O
    rw [G.2.2, h₁.comm]; exact (π₁ e).2
  choose r hr using hres
  have hrc : ∀ G, Continuous (r G) := fun G => by
    rw [h₂.isEmbedding.isInducing.continuous_iff]
    have : ι₂ ∘ r G = G.1 ∘ ι₁ := funext (hr G)
    rw [this]; exact G.2.1.comp h₁.isEmbedding.continuous
  have hrp : ∀ G e, π₂ (r G e) = π₁ e := fun G e => by
    apply Subtype.ext
    have h := congrArg p₂ (hr G e)
    rw [h₂.comm, G.2.2, h₁.comm] at h
    exact h
  refine ⟨{ toFun := fun F => ⟨(hext F).exists.choose, (hext F).exists.choose_spec.1,
                fun x => (hext F).exists.choose_spec.2.1 x⟩
            invFun := fun G => ⟨r G, hrc G, hrp G⟩
            left_inv := fun F => ?_
            right_inv := fun G => ?_ }, fun F e => (hext F).exists.choose_spec.2.2 e⟩
  · apply Subtype.ext
    funext e
    apply h₂.isEmbedding.injective
    rw [hr]
    exact (hext F).exists.choose_spec.2.2 e
  · apply Subtype.ext
    have hG : Continuous G.1 ∧ (∀ x, p₂ (G.1 x) = id (p₁ x)) ∧
        ∀ e, G.1 (ι₁ e) = ι₂ (r G e) := ⟨G.2.1, G.2.2, fun e => (hr G e).symm⟩
    exact ((hext ⟨r G, hrc G, hrp G⟩).unique (hext _).exists.choose_spec hG)

/-- Morphisms of completions are determined by their restriction (`rem:one_could_sum_up`): two
continuous maps `X₁ → X₂` agreeing on the image of `ι₁` are equal (`X₂` Hausdorff, `range ι₁`
dense). This is the uniqueness making `GX.completion_hom_equiv` functorial. -/
theorem completion_hom_ext {E₁ X₁ X₂ : Type*} [TopologicalSpace E₁] [TopologicalSpace X₁]
    [TopologicalSpace X₂] [T2Space X₂] {π₁ : E₁ → Y} {p₁ : X₁ → Y} {ι₁ : E₁ → X₁}
    (h₁ : IsSpreadCompletion π₁ p₁ ι₁) {G G' : X₁ → X₂} (hG : Continuous G)
    (hG' : Continuous G') (h : ∀ e, G (ι₁ e) = G' (ι₁ e)) : G = G' :=
  DenseRange.equalizer h₁.isPortly.dense hG hG' (funext h)

/-- Functoriality of `GX.completion_hom_equiv`, identities: any bijection characterised by
extension (`Φ F ∘ ι = ι ∘ F`) sends the identity of `E` to the identity of `X`. -/
theorem completion_hom_id {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] [T2Space X]
    {O : Set Y} {π : E → O} {p : X → Y} {ι : E → X}
    (h : IsSpreadCompletion (fun e => (π e : Y)) p ι)
    (Φ : {F : E → E // Continuous F ∧ ∀ e, π (F e) = π e} ≃
        {G : X → X // Continuous G ∧ ∀ x, p (G x) = p x})
    (hΦ : ∀ F e, (Φ F : X → X) (ι e) = ι ((F : E → E) e)) :
    (Φ ⟨id, continuous_id, fun _ => rfl⟩ : X → X) = id :=
  completion_hom_ext h (Φ _).2.1 continuous_id fun e => hΦ _ e

/-- Functoriality of `GX.completion_hom_equiv`, composites: for bijections `Φ₁₂`, `Φ₂₃`, `Φ₁₃`
each characterised by extension, `Φ₁₃ (F' ∘ F) = Φ₂₃ F' ∘ Φ₁₂ F`. -/
theorem completion_hom_comp {E₁ E₂ E₃ X₁ X₂ X₃ : Type*} [TopologicalSpace E₁]
    [TopologicalSpace E₂] [TopologicalSpace E₃] [TopologicalSpace X₁] [TopologicalSpace X₂]
    [TopologicalSpace X₃] [T2Space X₃] {O : Set Y} {π₁ : E₁ → O} {π₂ : E₂ → O} {π₃ : E₃ → O}
    {p₁ : X₁ → Y} {p₂ : X₂ → Y} {p₃ : X₃ → Y} {ι₁ : E₁ → X₁} {ι₂ : E₂ → X₂} {ι₃ : E₃ → X₃}
    (h₁ : IsSpreadCompletion (fun e => (π₁ e : Y)) p₁ ι₁)
    (Φ₁₂ : {F : E₁ → E₂ // Continuous F ∧ ∀ e, π₂ (F e) = π₁ e} ≃
        {G : X₁ → X₂ // Continuous G ∧ ∀ x, p₂ (G x) = p₁ x})
    (Φ₂₃ : {F : E₂ → E₃ // Continuous F ∧ ∀ e, π₃ (F e) = π₂ e} ≃
        {G : X₂ → X₃ // Continuous G ∧ ∀ x, p₃ (G x) = p₂ x})
    (Φ₁₃ : {F : E₁ → E₃ // Continuous F ∧ ∀ e, π₃ (F e) = π₁ e} ≃
        {G : X₁ → X₃ // Continuous G ∧ ∀ x, p₃ (G x) = p₁ x})
    (h₁₂ : ∀ F e, (Φ₁₂ F : X₁ → X₂) (ι₁ e) = ι₂ ((F : E₁ → E₂) e))
    (h₂₃ : ∀ F e, (Φ₂₃ F : X₂ → X₃) (ι₂ e) = ι₃ ((F : E₂ → E₃) e))
    (h₁₃ : ∀ F e, (Φ₁₃ F : X₁ → X₃) (ι₁ e) = ι₃ ((F : E₁ → E₃) e))
    (F : {F : E₁ → E₂ // Continuous F ∧ ∀ e, π₂ (F e) = π₁ e})
    (F' : {F : E₂ → E₃ // Continuous F ∧ ∀ e, π₃ (F e) = π₂ e}) :
    (Φ₁₃ ⟨F'.1 ∘ F.1, F'.2.1.comp F.2.1, fun e => by simp only [comp_apply, F'.2.2, F.2.2]⟩ :
        X₁ → X₃) = (Φ₂₃ F' : X₂ → X₃) ∘ (Φ₁₂ F : X₁ → X₂) :=
  completion_hom_ext h₁ (Φ₁₃ _).2.1 ((Φ₂₃ F').2.1.comp (Φ₁₂ F).2.1) fun e => by
    rw [h₁₃, comp_apply, h₁₂, h₂₃]; rfl

/-! ### `prop:universality`: the maximal covering possibly branched over `S` -/

section Universal

variable {Y : Type u} [TopologicalSpace Y]

/-- The universal covering of `Y ∖ S` (based at `y₀`), followed by the inclusion into `Y`: the
spread `\widetilde{Y∖S} → Y` of `RamcovGX.tex:1170`. -/
abbrev univCoverProj (S : Set Y) (y₀ : (Sᶜ : Set Y)) : UniversalCover (Sᶜ : Set Y) y₀ → Y :=
  fun c => (UniversalCover.proj (Sᶜ : Set Y) y₀ c : Y)

/-- **`\widetilde Y^S`** (`RamcovGX.tex:1170`): the Fox completion (space of ends) of
`\widetilde{Y∖S} → Y`, projected to `Y` by `SpreadEnd.base`. -/
abbrev MaxBranchedCover (S : Set Y) (y₀ : (Sᶜ : Set Y)) : Type u :=
  SpreadEnd (univCoverProj S y₀)

variable [T2Space Y] [LocPathConnectedSpace Y] [FirstCountableTopology Y] [ConnectedSpace Y]
  {S : Set Y}

/-- The facts about `\widetilde Y^S` used below: a completion of `\widetilde{Y∖S} → Y`, a
branched covering of `Y` possibly branched over `S`, in which `\widetilde{Y∖S}` is the preimage
of `Y ∖ S`; locally path-connected. -/
theorem maxBranched_basic (hS : IsSkeletal S) (hSc : SemilocallySimplyConnected (Sᶜ : Set Y))
    (y₀ : (Sᶜ : Set Y)) :
    IsSpreadCompletion (univCoverProj S y₀) SpreadEnd.base
        (SpreadEnd.ofPoint (univCoverProj S y₀)) ∧
      IsBranchedCovering (SpreadEnd.base : MaxBranchedCover S y₀ → Y) ∧
      IsPossiblyBranchedOver (SpreadEnd.base : MaxBranchedCover S y₀ → Y) S ∧
      (SpreadEnd.base : MaxBranchedCover S y₀ → Y) ⁻¹' Sᶜ =
        range (SpreadEnd.ofPoint (univCoverProj S y₀)) ∧
      LocPathConnectedSpace (MaxBranchedCover S y₀) ∧ IsSpread (univCoverProj S y₀) := by
  have hO : IsPortly (Sᶜ : Set Y) := isSkeletal_iff.1 hS
  haveI : LocPathConnectedSpace (Sᶜ : Set Y) := hO.isOpen.locPathConnectedSpace
  haveI : PathConnectedSpace (Sᶜ : Set Y) :=
    pathConnectedSpace_iff_connectedSpace.2 (isConnected_iff_connectedSpace.1 hO.isConnected)
  have hπ := UniversalCover.isCoveringMap_proj (y₀ := y₀) hSc
  have hπs : Surjective (UniversalCover.proj (Sᶜ : Set Y) y₀) := UniversalCover.proj_surjective
  have hsp := isSpread_coe_comp_of_isCoveringMap hO.isOpen hπ
  have h := isSpreadCompletion_ends_of_isCoveringMap hO hπ hπs
  haveI hl := SpreadEnd.locPathConnectedSpace hsp
  obtain ⟨hbc, hpb, hpre⟩ := isBranchedCovering_of_isSpreadCompletion hO hπ hπs h
  rw [compl_compl] at hpb
  exact ⟨h, hbc, hpb, hpre, hl, hsp⟩

/-- `Y ∖ S` is non-empty (so a base point `y₀` for `\widetilde Y^S` exists). -/
theorem nonempty_compl_of_isSkeletal (hS : IsSkeletal S) : (Sᶜ : Set Y).Nonempty :=
  (isSkeletal_iff.1 hS).dense.nonempty

/-- **`prop:universality`, existence** (`RamcovGX.tex:1158`): `\widetilde Y^S → Y` is a covering
of `Y` possibly branched over `S`. -/
theorem maxBranched_isBranchedCovering (hS : IsSkeletal S)
    (hSc : SemilocallySimplyConnected (Sᶜ : Set Y)) (y₀ : (Sᶜ : Set Y)) :
    IsBranchedCovering (SpreadEnd.base : MaxBranchedCover S y₀ → Y) ∧
      IsPossiblyBranchedOver (SpreadEnd.base : MaxBranchedCover S y₀ → Y) S :=
  let h := maxBranched_basic hS hSc y₀
  ⟨h.2.1, h.2.2.1⟩

/-- **`prop:universality`, universal property** (`RamcovGX.tex:1162`): for every covering
`p : X → Y` possibly branched over `S` (Hausdorff, locally path-connected, first countable `X`)
there is a covering `\widetilde Y^S → X` over `Y`, possibly branched over `p⁻¹(S)`. -/
theorem maxBranched_universal (hS : IsSkeletal S) (hSc : SemilocallySimplyConnected (Sᶜ : Set Y))
    (y₀ : (Sᶜ : Set Y)) {X : Type*} [TopologicalSpace X] [T2Space X] [LocPathConnectedSpace X]
    [FirstCountableTopology X] {p : X → Y} (hp : IsBranchedCovering p)
    (hpS : IsPossiblyBranchedOver p S) :
    ∃ Φ : MaxBranchedCover S y₀ → X, Continuous Φ ∧ (∀ e, p (Φ e) = e.base) ∧
      IsBranchedCovering Φ ∧ IsPossiblyBranchedOver Φ (p ⁻¹' S) := by
  have hO : IsPortly (Sᶜ : Set Y) := isSkeletal_iff.1 hS
  haveI : LocPathConnectedSpace (Sᶜ : Set Y) := hO.isOpen.locPathConnectedSpace
  obtain ⟨h₁, hbc₁, -, hpre₁, hl, hsp₁⟩ := maxBranched_basic hS hSc y₀
  haveI := hl
  haveI : T2Space (UniversalCover (Sᶜ : Set Y) y₀) :=
    t2Space_of_isCoveringMap (UniversalCover.isCoveringMap_proj (y₀ := y₀) hSc)
  have hOp : (Sᶜ : Set Y) ⊆ ordY p := fun y hy => by
    by_contra h
    exact hy (hpS h)
  obtain ⟨hcovE, hsurjE, hconE, h₂⟩ := hp.restrict_isCoveringMap hO hOp
  haveI : LocPathConnectedSpace (p ⁻¹' Sᶜ) :=
    (hO.isOpen.preimage hp.isSpread.continuous).locPathConnectedSpace
  haveI : ConnectedSpace (p ⁻¹' Sᶜ) := hconE
  haveI : PathConnectedSpace (p ⁻¹' Sᶜ) := pathConnectedSpace_iff_connectedSpace.2 hconE
  obtain ⟨e₀, he₀⟩ := hsurjE y₀
  obtain ⟨F, ⟨hF0, hF⟩, -⟩ := UniversalCover.existsUnique_lift hSc hcovE he₀
  have hFc : IsCoveringMap F := UniversalCover.isCoveringMap_of_comp_eq hSc hcovE F.continuous hF
  have hFs : Surjective F := UniversalCover.lift_surjective hcovE he₀ F hF0 hF
  have hcommF : ∀ c, (((Sᶜ : Set Y).restrictPreimage p (F c) : (Sᶜ : Set Y)) : Y) =
      id (univCoverProj S y₀ c) := fun c => congrArg Subtype.val (congrFun hF c)
  obtain ⟨G, ⟨hGc, hGp, hGι⟩, -⟩ := h₁.toIsFoxCompletion.existsUnique_extend
    h₂.toIsFoxCompletion continuous_id F.continuous hcommF
  have hmaps : MapsTo G (SpreadEnd.base ⁻¹' Sᶜ) (p ⁻¹' Sᶜ) := fun e he => by
    show p (G e) ∈ Sᶜ
    rw [hGp]; exact he
  have hemb₁ := SpreadEnd.isEmbedding_ofPoint hsp₁
  set ψ : UniversalCover (Sᶜ : Set Y) y₀ ≃ₜ (SpreadEnd.base ⁻¹' Sᶜ : Set (MaxBranchedCover S y₀)) :=
    hemb₁.toHomeomorph.trans (Homeomorph.setCongr hpre₁.symm)
  have hψ : ∀ c, (ψ c : MaxBranchedCover S y₀) = SpreadEnd.ofPoint _ c := fun c => by
    rw [Homeomorph.trans_apply]
    exact IsEmbedding.toHomeomorph_apply_coe hemb₁ c
  have hres : hmaps.restrict G _ _ = F ∘ ψ.symm := by
    funext w
    obtain ⟨c, rfl⟩ := ψ.surjective w
    rw [comp_apply, ψ.symm_apply_apply]
    apply Subtype.ext
    show G (ψ c : MaxBranchedCover S y₀) = (F c : X)
    rw [hψ]; exact hGι c
  have hcov : IsCoveringMap (hmaps.restrict G _ _) := hres ▸ hFc.comp_homeomorph ψ.symm
  have hsurj : Surjective (hmaps.restrict G _ _) := hres ▸ hFs.comp ψ.symm.surjective
  obtain ⟨hGbc, hGpb⟩ := isBranchedCovering_of_comm hO hbc₁ hp hGc (fun e => hGp e) hmaps hcov
    hsurj
  rw [compl_compl] at hGpb
  exact ⟨G, hGc, fun e => hGp e, hGbc, hGpb⟩

/-- **`prop:universality`, uniqueness** (`RamcovGX.tex:1185–1186`, in the strong form the proof
gives): a covering `p : X → Y` possibly branched over `S` which admits *any* continuous map
`Ψ : X → \widetilde Y^S` over `Y` is isomorphic to `\widetilde Y^S` over `Y`. -/
theorem maxBranched_unique (hS : IsSkeletal S) (hSc : SemilocallySimplyConnected (Sᶜ : Set Y))
    (y₀ : (Sᶜ : Set Y)) {X : Type*} [TopologicalSpace X] [T2Space X] [LocPathConnectedSpace X]
    [FirstCountableTopology X] {p : X → Y} (hp : IsBranchedCovering p)
    (hpS : IsPossiblyBranchedOver p S) {Ψ : X → MaxBranchedCover S y₀} (hΨ : Continuous Ψ)
    (hΨp : ∀ x, (Ψ x).base = p x) :
    ∃ Φ : MaxBranchedCover S y₀ ≃ₜ X, ∀ e, p (Φ e) = e.base := by
  have hO : IsPortly (Sᶜ : Set Y) := isSkeletal_iff.1 hS
  haveI : LocPathConnectedSpace (Sᶜ : Set Y) := hO.isOpen.locPathConnectedSpace
  obtain ⟨-, -, -, hpre₁, hl, hsp₁⟩ := maxBranched_basic hS hSc y₀
  haveI := hl
  haveI := UniversalCover.simplyConnectedSpace (y₀ := y₀) hSc
  have hπ := UniversalCover.isCoveringMap_proj (y₀ := y₀) hSc
  haveI : T2Space (UniversalCover (Sᶜ : Set Y) y₀) := t2Space_of_isCoveringMap hπ
  obtain ⟨Φ, hΦc, hΦp, hΦbc, -⟩ := maxBranched_universal hS hSc y₀ hp hpS
  set K : MaxBranchedCover S y₀ → MaxBranchedCover S y₀ := Ψ ∘ Φ
  have hKc : Continuous K := hΨ.comp hΦc
  have hKb : ∀ e, (K e).base = e.base := fun e => by
    show (Ψ (Φ e)).base = e.base
    rw [hΨp, hΦp]
  have hKr : ∀ c, ∃ c', SpreadEnd.ofPoint _ c' = K (SpreadEnd.ofPoint (univCoverProj S y₀) c) :=
    fun c => by
      have : K (SpreadEnd.ofPoint (univCoverProj S y₀) c) ∈
          (SpreadEnd.base ⁻¹' Sᶜ : Set (MaxBranchedCover S y₀)) := by
        show (K _).base ∈ Sᶜ
        rw [hKb]; exact (UniversalCover.proj (Sᶜ : Set Y) y₀ c).2
      rw [hpre₁] at this
      exact this
  choose h hh using hKr
  have hemb := SpreadEnd.isEmbedding_ofPoint hsp₁
  have hhc : Continuous h := by
    rw [hemb.isInducing.continuous_iff]
    have : (SpreadEnd.ofPoint (univCoverProj S y₀) ∘ h) = K ∘ SpreadEnd.ofPoint _ := funext hh
    rw [this]; exact hKc.comp (SpreadEnd.continuous_ofPoint hsp₁)
  have hhp : UniversalCover.proj (Sᶜ : Set Y) y₀ ∘ h = UniversalCover.proj (Sᶜ : Set Y) y₀ := by
    funext c
    apply Subtype.ext
    have := congrArg SpreadEnd.base (hh c)
    rw [hKb] at this
    exact this
  obtain ⟨Θ, hΘ0, hΘ⟩ := UniversalCover.exists_homeomorph_of_simplyConnected (y₀ := y₀) hSc hπ
    (e₀ := h (UniversalCover.base y₀)) ((congrFun hhp _).trans rfl)
  have hhΘ : h = Θ := hπ.eq_of_comp_eq hhc Θ.continuous (hhp.trans hΘ.symm) _ hΘ0.symm
  have hcommΘ : ∀ c, univCoverProj S y₀ (Θ c) = id (univCoverProj S y₀ c) := fun c => by
    show ((UniversalCover.proj (Sᶜ : Set Y) y₀ ∘ Θ) c : Y) = _
    rw [hΘ]; rfl
  have hcommΘ' : ∀ c, univCoverProj S y₀ (Θ.symm c) = id (univCoverProj S y₀ c) := fun c => by
    have := hcommΘ (Θ.symm c)
    rw [Θ.apply_symm_apply] at this
    exact this.symm
  set M := SpreadEnd.map continuous_id Θ.continuous hcommΘ
  set M' := SpreadEnd.map continuous_id Θ.symm.continuous hcommΘ'
  have hKM : K = M := SpreadEnd.eq_map continuous_id Θ.continuous hcommΘ hKc fun c => by
    rw [← hh, hhΘ]
  have hM'M : M' ∘ M = id := by
    refine SpreadEnd.denseRange_ofPoint.equalizer
      ((SpreadEnd.continuous_map _ _ _).comp (SpreadEnd.continuous_map _ _ _)) continuous_id
      (funext fun c => ?_)
    simp only [comp_apply, id, M, M', SpreadEnd.map_ofPoint, Homeomorph.symm_apply_apply]
  have hKinj : Injective K := by
    rw [hKM]; exact HasLeftInverse.injective ⟨M', congrFun hM'M⟩
  have hΦinj : Injective Φ := fun a b hab => hKinj (by simp only [K, comp_apply, hab])
  have hΦo : IsOpenMap Φ := (spread_connected_image hΦbc).1
  exact ⟨(Equiv.ofBijective Φ ⟨hΦinj, hΦbc.surjective⟩).toHomeomorphOfContinuousOpen hΦc hΦo,
    hΦp⟩

end Universal

/-- A covering of `Y` possibly branched over `S` that is **maximal**: it dominates, by a branched
covering over `Y`, every covering of `Y` possibly branched over `S` with a Hausdorff, locally
path-connected, first countable total space in the universe `w` (`RamcovGX.tex:1160`). -/
def IsMaximalPossiblyBranched.{w'} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (p : X → Y) (S : Set Y) : Prop :=
  IsBranchedCovering p ∧ IsPossiblyBranchedOver p S ∧
    ∀ (X' : Type w') [TopologicalSpace X'] [T2Space X'] [LocPathConnectedSpace X']
      [FirstCountableTopology X'] (p' : X' → Y), IsBranchedCovering p' →
      IsPossiblyBranchedOver p' S →
      ∃ Φ : X → X', Continuous Φ ∧ (∀ x, p' (Φ x) = p x) ∧ IsBranchedCovering Φ

section Universal'

variable {Y : Type u} [TopologicalSpace Y] [T2Space Y] [LocPathConnectedSpace Y]
  [FirstCountableTopology Y] [ConnectedSpace Y] {S : Set Y}

/-- **`prop:universality`** (`RamcovGX.tex:1158`): `\widetilde Y^S` is maximal among the
coverings of `Y` possibly branched over `S` (in every universe). -/
theorem maxBranched_isMaximal (hS : IsSkeletal S) (hSc : SemilocallySimplyConnected (Sᶜ : Set Y))
    (y₀ : (Sᶜ : Set Y)) :
    IsMaximalPossiblyBranched.{w} (SpreadEnd.base : MaxBranchedCover S y₀ → Y) S := by
  obtain ⟨hbc, hpb⟩ := maxBranched_isBranchedCovering hS hSc y₀
  refine ⟨hbc, hpb, fun X' _ _ _ _ p' hp' hp'S => ?_⟩
  obtain ⟨Φ, hΦc, hΦp, hΦbc, -⟩ := maxBranched_universal hS hSc y₀ hp' hp'S
  exact ⟨Φ, hΦc, hΦp, hΦbc⟩

/-- **`prop:universality`, uniqueness** (`RamcovGX.tex:1185`): a maximal covering of `Y` possibly
branched over `S` (Hausdorff, locally path-connected, first countable; maximality tested in `Y`'s
universe) is isomorphic to `\widetilde Y^S` over `Y`. -/
theorem IsMaximalPossiblyBranched.nonempty_homeomorph (hS : IsSkeletal S)
    (hSc : SemilocallySimplyConnected (Sᶜ : Set Y)) (y₀ : (Sᶜ : Set Y)) {X : Type*}
    [TopologicalSpace X] [T2Space X] [LocPathConnectedSpace X] [FirstCountableTopology X]
    {p : X → Y} (hp : IsMaximalPossiblyBranched.{u} p S) :
    ∃ Φ : MaxBranchedCover S y₀ ≃ₜ X, ∀ e, p (Φ e) = e.base := by
  obtain ⟨-, -, -, -, hl, -⟩ := maxBranched_basic hS hSc y₀
  haveI := hl
  obtain ⟨hbc, hpb⟩ := maxBranched_isBranchedCovering hS hSc y₀
  obtain ⟨Ψ, hΨc, hΨp, -⟩ := hp.2.2 (MaxBranchedCover S y₀) SpreadEnd.base hbc hpb
  exact maxBranched_unique hS hSc y₀ hp.1 hp.2.1 hΨc hΨp

end Universal'

/-! ### `rem:considering_maximal_covering_possibly` -/

/-- The identity of a connected space is ordinary everywhere. -/
theorem ordY_id_eq_univ [PreconnectedSpace Y] : ordY (id : Y → Y) = univ :=
  eq_univ_of_forall fun y => ⟨univ, isOpen_univ, mem_univ y, ⟨y, mem_univ y⟩, fun x _ =>
    ⟨Homeomorph.setCongr (isPreconnected_univ.connectedComponentIn (mem_univ x)), fun _ => rfl⟩⟩

section Trivial

variable {Y : Type u} [TopologicalSpace Y] [T2Space Y] [LocPathConnectedSpace Y]
  [FirstCountableTopology Y] [ConnectedSpace Y] {S : Set Y}

/-- **`rem:considering_maximal_covering_possibly`, the general fact** (`RamcovGX.tex:1177`): if
`Y ∖ S` is simply connected, the maximal covering of `Y` possibly branched over `S` is trivial —
`\widetilde Y^S → Y` is a homeomorphism — and its branching locus is empty, whatever `S`. -/
theorem maxBranched_trivial_of_simplyConnected (hS : IsSkeletal S)
    [SimplyConnectedSpace (Sᶜ : Set Y)] (y₀ : (Sᶜ : Set Y)) :
    (∃ φ : MaxBranchedCover S y₀ ≃ₜ Y, ∀ e, φ e = e.base) ∧
      branchingLocus (SpreadEnd.base : MaxBranchedCover S y₀ → Y) = ∅ := by
  have hO : IsPortly (Sᶜ : Set Y) := isSkeletal_iff.1 hS
  haveI : LocPathConnectedSpace (Sᶜ : Set Y) := hO.isOpen.locPathConnectedSpace
  have hSc : SemilocallySimplyConnected (Sᶜ : Set Y) :=
    SemilocallySimplyConnected.of_simplyConnectedSpace _
  obtain ⟨h₁, -, -, -, -, -⟩ := maxBranched_basic hS hSc y₀
  obtain ⟨Θ, -, hΘ⟩ := UniversalCover.exists_homeomorph_of_simplyConnected (y₀ := y₀) hSc
    (isCoveringMap_of_homeomorph (Homeomorph.refl (Sᶜ : Set Y))) (e₀ := y₀) rfl
  have hp₀ : univCoverProj S y₀ = Subtype.val ∘ Θ := by
    funext c
    have := congrFun hΘ c
    simp only [comp_apply, Homeomorph.refl_apply, id] at this
    simp only [univCoverProj, comp_apply, this]
  have h₂ : IsSpreadCompletion (univCoverProj S y₀) (id : Y → Y) (univCoverProj S y₀) := by
    refine ⟨isSpread_id, fun _ => rfl, ?_, isCompleteSpread_id, ?_⟩
    · rw [hp₀]; exact IsEmbedding.subtypeVal.comp Θ.isEmbedding
    · rw [hp₀, range_comp, Θ.range_coe, image_univ, Subtype.range_coe]; exact hO
  obtain ⟨φ, ⟨hφ, -⟩, -⟩ := h₁.existsUnique_homeomorph h₂
  refine ⟨⟨φ, hφ⟩, ?_⟩
  have h := image_ordY_of_homeomorph (p := (SpreadEnd.base : MaxBranchedCover S y₀ → Y))
    (p' := (id : Y → Y)) φ (Homeomorph.refl Y) (fun e => hφ e)
  rw [ordY_id_eq_univ] at h
  have h' : ordY (SpreadEnd.base : MaxBranchedCover S y₀ → Y) = univ := by
    rw [← h]; ext y; simp
  rw [branchingLocus, h', compl_univ]

end Trivial

/-- A ball minus its centre is preconnected, in a real inner product space of dimension `> 1`. -/
theorem isPreconnected_ball_diff_singleton {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (hE : 1 < Module.rank ℝ E) (c : E) (r : ℝ) :
    IsPreconnected (Metric.ball c r \ {c}) := by
  rcases le_or_gt r 0 with hr | hr
  · rw [Metric.ball_eq_empty.2 hr, empty_sdiff]; exact isPreconnected_empty
  set φ := OpenPartialHomeomorph.univBall c r
  have hsrc : φ.source = univ := OpenPartialHomeomorph.univBall_source c r
  have hφc : Continuous φ := continuousOn_univ.1 (hsrc ▸ φ.continuousOn)
  have hcount : (φ ⁻¹' {c}).Countable :=
    (countable_singleton c).preimage_of_injOn (φ.injOn.mono (by rw [hsrc]; exact subset_univ _))
  have hconn : IsConnected (φ ⁻¹' {c})ᶜ := hcount.isConnected_compl_of_one_lt_rank hE
  have : Metric.ball c r \ {c} = φ '' (φ ⁻¹' {c})ᶜ := by
    rw [image_compl_preimage, ← image_univ, ← hsrc, φ.image_source_eq_target,
      OpenPartialHomeomorph.univBall_target c hr]
  rw [this]
  exact hconn.isPreconnected.image _ hφc.continuousOn

/-- A point with a chart into a real inner product space of dimension `> 1` has a portly
complement (locally connected T1 ambient space). -/
theorem isPortly_compl_singleton_of_chart [T1Space Y] [LocallyConnectedSpace Y] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (hE : 1 < Module.rank ℝ E)
    (e : OpenPartialHomeomorph Y E) {v : Y} (hv : v ∈ e.source) : IsPortly ({v}ᶜ : Set Y) := by
  haveI : Nontrivial E := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    rw [rank_zero_iff.2 inferInstance] at hE
    exact absurd hE (by norm_num)
  have hd : Dense ({v}ᶜ : Set Y) := by
    rw [dense_compl_singleton_iff_not_open]
    intro ho
    have : IsOpen (e '' {v}) := e.isOpen_image_of_subset_source ho (singleton_subset_iff.2 hv)
    rw [image_singleton] at this
    exact not_isOpen_singleton _ this
  refine ⟨isOpen_compl_singleton, hd, fun W hW hWc => ?_⟩
  refine isPreconnected_of_local hWc inter_subset_left (hd.open_subset_closure_inter hW)
    fun x hx => ?_
  by_cases hxv : x = v
  · subst hxv
    have hO : IsOpen (e '' (e.source ∩ W)) := e.isOpen_image_source_inter hW
    obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.1 hO (e x) ⟨x, ⟨hv, hx⟩, rfl⟩
    refine ⟨e.source ∩ e ⁻¹' Metric.ball (e x) r, e.isOpen_inter_preimage Metric.isOpen_ball,
      ⟨hv, Metric.mem_ball_self hr⟩, ?_⟩
    have hball : Metric.ball (e x) r ⊆ e.target := fun z hz => by
      obtain ⟨w, ⟨hw, -⟩, rfl⟩ := hrW hz
      exact e.map_source hw
    have hset : (e.source ∩ e ⁻¹' Metric.ball (e x) r) ∩ (W ∩ {x}ᶜ) =
        e.symm '' (Metric.ball (e x) r \ {e x}) := by
      ext z
      constructor
      · rintro ⟨⟨hzs, hzb⟩, -, hzx⟩
        refine ⟨e z, ⟨hzb, fun h => hzx (e.injOn hzs hv h)⟩, e.left_inv hzs⟩
      · rintro ⟨w, ⟨hwb, hwx⟩, rfl⟩
        have hwt := hball hwb
        refine ⟨⟨e.map_target hwt, by rw [mem_preimage, e.right_inv hwt]; exact hwb⟩, ?_, ?_⟩
        · obtain ⟨u, ⟨hu, huW⟩, hu'⟩ := hrW hwb
          rw [← hu', e.left_inv hu]; exact huW
        · intro h
          apply hwx
          rw [mem_singleton_iff] at h ⊢
          rw [← h, e.right_inv hwt]
    rw [hset]
    exact (isPreconnected_ball_diff_singleton hE _ r).image _
      (e.continuousOn_symm.mono (sdiff_subset.trans hball))
  · have hO : IsOpen (W ∩ {v}ᶜ) := hW.inter isOpen_compl_singleton
    refine ⟨connectedComponentIn (W ∩ {v}ᶜ) x, hO.connectedComponentIn,
      mem_connectedComponentIn ⟨hx, hxv⟩, ?_⟩
    rw [inter_eq_left.2 (connectedComponentIn_subset _ _)]
    exact isPreconnected_connectedComponentIn

/-- The 2-sphere `𝕊² ⊆ ℝ³`. -/
abbrev Sphere2 : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin (2 + 1))) 1

instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 + 1))) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

theorem one_lt_rank_euclideanSpace_two : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 2)) := by
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]; norm_num

instance : LocPathConnectedSpace Sphere2 := ChartedSpace.locPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) _

instance : ConnectedSpace Sphere2 := isConnected_iff_connectedSpace.1
  (isConnected_sphere (by rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]; norm_num)
    0 zero_le_one)

/-- `𝕊²` minus a point is homeomorphic to the plane (stereographic projection). -/
def sphere2ComplHomeomorph (v : Sphere2) : ({v}ᶜ : Set Sphere2) ≃ₜ EuclideanSpace ℝ (Fin 2) :=
  (Homeomorph.setCongr (stereographic'_source (n := 2) v).symm).trans
    ((stereographic' 2 v).toHomeomorphSourceTarget.trans
      ((Homeomorph.setCongr (stereographic'_target (n := 2) v)).trans (Homeomorph.Set.univ _)))

instance (v : Sphere2) : SimplyConnectedSpace ({v}ᶜ : Set Sphere2) := by
  haveI : ContractibleSpace ({v}ᶜ : Set Sphere2) := (sphere2ComplHomeomorph v).contractibleSpace
  infer_instance

/-- `{v}` is skeletal in `𝕊²`. -/
theorem isSkeletal_sphere2_singleton (v : Sphere2) : IsSkeletal ({v} : Set Sphere2) := by
  haveI : LocallyConnectedSpace Sphere2 := inferInstance
  have hne : v ∈ (stereographic' 2 (-v)).source := by
    rw [stereographic'_source, mem_compl_singleton_iff]
    intro h
    have h1 : ((v : EuclideanSpace ℝ (Fin (2 + 1)))) = -((v : EuclideanSpace ℝ (Fin (2 + 1)))) :=
      congrArg Subtype.val h
    have h2 : ‖(v : EuclideanSpace ℝ (Fin (2 + 1)))‖ = 1 := norm_eq_of_mem_sphere v
    have h3 : (v : EuclideanSpace ℝ (Fin (2 + 1))) = 0 := by
      have h4 : (2 : ℝ) • (v : EuclideanSpace ℝ (Fin (2 + 1))) = 0 := by
        rw [two_smul]; nth_rw 2 [h1]; exact add_neg_cancel _
      exact (smul_eq_zero.1 h4).resolve_left two_ne_zero
    rw [h3, norm_zero] at h2
    exact zero_ne_one h2
  exact isPortly_compl_singleton_of_chart one_lt_rank_euclideanSpace_two _ hne

/-- **`rem:considering_maximal_covering_possibly`** (`RamcovGX.tex:1176–1178`): for `Y = 𝕊²` and
`S` a singleton, the maximal covering possibly branched over `S` is trivial and its branching
locus is empty — strictly smaller than `S`. -/
theorem sphere2_maxBranched_trivial (v : Sphere2) (y₀ : ({v}ᶜ : Set Sphere2)) :
    (∃ φ : MaxBranchedCover ({v} : Set Sphere2) y₀ ≃ₜ Sphere2, ∀ e, φ e = e.base) ∧
      branchingLocus (SpreadEnd.base : MaxBranchedCover ({v} : Set Sphere2) y₀ → Sphere2) = ∅ ∧
      branchingLocus (SpreadEnd.base : MaxBranchedCover ({v} : Set Sphere2) y₀ → Sphere2) ≠
        {v} :=
  let h := maxBranched_trivial_of_simplyConnected (isSkeletal_sphere2_singleton v) y₀
  ⟨h.1, h.2, by rw [h.2]; exact (singleton_nonempty v).ne_empty.symm⟩

/-! ### `cex:proposition_prop_branched_covering`: the infinite angle disc -/

/-- The pointwise half of `isSpread_of_isCoveringMap`: at a point over an evenly covered value of
an open map, components of preimages of small open sets lie in any given neighbourhood. -/
theorem exists_cc_subset_of_isEvenlyCovered {f : X → Y} (hfo : IsOpenMap f) {x : X} {ι' : Type*}
    [TopologicalSpace ι'] (h : IsEvenlyCovered f (f x) ι') {O : Set X} (hO : IsOpen O)
    (hxO : x ∈ O) :
    ∃ W : Set Y, IsOpen W ∧ f x ∈ W ∧ connectedComponentIn (f ⁻¹' W) x ⊆ O := by
  obtain ⟨U, -, hxU, T, hTo, hTi, hTm, -, hTd, hTc⟩ := IsEvenlyCovered.exists_sheets h
  obtain ⟨j, hj⟩ := mem_iUnion.1 (hTc hxU)
  have hx : x ∈ f ⁻¹' (f '' (T j ∩ O)) := ⟨x, ⟨hj, hxO⟩, rfl⟩
  refine ⟨f '' (T j ∩ O), hfo _ ((hTo j).inter hO), hx, ?_⟩
  have hsub : connectedComponentIn (f ⁻¹' (f '' (T j ∩ O))) x ⊆ T j := by
    refine GX.IsPreconnected.subset_of_pairwise_disjoint hTo hTd
      isPreconnected_connectedComponentIn (fun z hz => ?_) ⟨x, mem_connectedComponentIn hx, hj⟩
    apply hTc
    obtain ⟨w, ⟨hwT, -⟩, hwz⟩ := connectedComponentIn_subset _ _ hz
    show f z ∈ U
    rw [← hwz]; exact hTm j hwT
  intro z hz
  obtain ⟨w, ⟨hwT, hwO⟩, hwz⟩ := connectedComponentIn_subset _ _ hz
  have := hTi j hwT (hsub hz) hwz
  rw [← this]; exact hwO

namespace DInfty

/-- The radial path from the apex to `p`: `t ↦ (t r, θ)`. -/
def radial (p : DInfty) (t : I) : DInfty :=
  if h : 0 < (t : ℝ) * p.r then ⟨t * p.r, p.θ, Or.inl h⟩ else apex

theorem radial_r (p : DInfty) (t : I) : (radial p t).r = t * p.r := by
  unfold radial
  split_ifs with h
  · rfl
  · exact (le_antisymm (not_lt.1 h) (mul_nonneg t.2.1 p.r_nonneg)).symm

theorem continuous_radial (p : DInfty) : Continuous (radial p) := by
  refine continuous_generateFrom_iff.2 ?_
  rintro s (⟨O, hO, hOp, rfl⟩ | ⟨r₀, -, rfl⟩)
  · have : radial p ⁻¹' {x | (x.r, x.θ) ∈ O} = (fun t : I => ((t : ℝ) * p.r, p.θ)) ⁻¹' O := by
      ext t
      simp only [mem_preimage, mem_setOf_eq]
      unfold radial
      split_ifs with h
      · rfl
      · constructor
        · intro h'; have := hOp h'; simp [apex] at this
        · intro h'; exact absurd (hOp h') h
    rw [this]
    exact hO.preimage ((continuous_subtype_val.mul continuous_const).prodMk continuous_const)
  · have : radial p ⁻¹' {x | x.r < r₀} = {t : I | (t : ℝ) * p.r < r₀} := by
      ext t; simp only [mem_preimage, mem_setOf_eq, radial_r]
    rw [this]
    exact isOpen_lt (continuous_subtype_val.mul continuous_const) continuous_const

theorem radial_zero (p : DInfty) : radial p 0 = apex := by
  unfold radial; rw [dif_neg (by simp)]

theorem radial_one (p : DInfty) : radial p 1 = p := by
  rcases p.pos_or_eq_apex with hp | rfl
  · unfold radial
    rw [dif_pos (by simpa using hp)]
    ext <;> simp
  · unfold radial; split_ifs <;> first | rfl | (ext <;> simp_all)

/-- The radial path from the apex. -/
def radialPath (p : DInfty) : Path apex p where
  toFun := radial p
  continuous_toFun := continuous_radial p
  source' := radial_zero p
  target' := radial_one p

theorem isPathConnected_r_lt {ε : ℝ} (hε : 0 < ε) : IsPathConnected {p : DInfty | p.r < ε} := by
  refine ⟨apex, by simpa using hε, fun p hp => ⟨radialPath p, fun t => ?_⟩⟩
  show (radial p t).r < ε
  rw [radial_r]
  exact lt_of_le_of_lt (mul_le_of_le_one_left p.r_nonneg t.2.2) hp

instance : PathConnectedSpace DInfty :=
  ⟨⟨apex⟩, fun x y => ⟨(radialPath x).symm.trans (radialPath y)⟩⟩

instance : LocPathConnectedSpace DInfty := by
  haveI : LocPathConnectedSpace {q : ℝ × ℝ // 0 < q.1} :=
    (isOpen_lt continuous_const continuous_fst : IsOpen {q : ℝ × ℝ | 0 < q.1}).locPathConnectedSpace
  refine locPathConnectedSpace_iff_pathComponentIn_mem_nhds.2 fun x u hu hxu => ?_
  rcases x.pos_or_eq_apex with hx | rfl
  · obtain ⟨q, rfl⟩ : x ∈ range posEmb := by rw [range_posEmb]; exact hx
    have h1 := pathComponentIn_mem_nhds ((hu.preimage continuous_posEmb).mem_nhds hxu)
    have h2 := isOpenEmbedding_posEmb.image_mem_nhds.2 h1
    refine mem_of_superset h2 ?_
    rintro _ ⟨q', hq', rfl⟩
    have := (hq' : JoinedIn (posEmb ⁻¹' u) q q').map continuous_posEmb
    exact this.mono (image_preimage_subset _ _)
  · obtain ⟨ε, hε, h⟩ := exists_r_lt_subset_of_isOpen hu hxu
    exact mem_of_superset ((isOpen_r_lt ε).mem_nhds (by simpa using hε))
      ((isPathConnected_r_lt hε).subset_pathComponentIn (by simpa using hε) h)

instance : FirstCountableTopology DInfty := by
  refine ⟨fun x => ?_⟩
  rcases x.pos_or_eq_apex with hx | rfl
  · obtain ⟨q, rfl⟩ : x ∈ range posEmb := by rw [range_posEmb]; exact hx
    rw [← isOpenEmbedding_posEmb.map_nhds_eq]
    infer_instance
  · have hb : (𝓝 apex).HasBasis (fun _ : ℕ => True)
        fun n => {p : DInfty | p.r < 1 / ((n : ℝ) + 1)} :=
      hasBasis_nhds_apex.to_hasBasis (fun ε hε => by
          obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
          exact ⟨n, trivial, fun p hp => lt_trans hp hn⟩)
        fun n _ => ⟨1 / ((n : ℝ) + 1), by positivity, subset_rfl⟩
    exact hb.isCountablyGenerated

/-- The positive part `{r > 0}` of `𝔻_∞` is portly. -/
theorem isPortly_pos' : IsPortly {p : DInfty | 0 < p.r} := by
  have h := (DInfty.isPortly_pos PUnit.{1}).preimage_of_isLocalHomeomorph
    (Homeomorph.prodUnique DInfty PUnit.{1}).symm.isLocalHomeomorph
  exact h

end DInfty

/-- The quotient map `q : 𝔻_∞ → 𝔻 ≅ ℂ` of `cex:proposition_prop_branched_covering`, in
cylindrical coordinates with `α = 1`: `(r, θ) ↦ r e^{2πiθ}`. -/
abbrev qDisc : DInfty → ℂ := DInfty.cplx 1

theorem qDisc_eq_zero_iff (p : DInfty) : qDisc p = 0 ↔ p.r = 0 := by
  rw [← norm_eq_zero, DInfty.norm_cplx]

theorem preimage_qDisc_compl_zero : qDisc ⁻¹' ({0}ᶜ : Set ℂ) = {p : DInfty | 0 < p.r} := by
  ext p
  simp only [mem_preimage, mem_compl_iff, mem_singleton_iff, qDisc_eq_zero_iff, mem_setOf_eq]
  exact ⟨fun h => lt_of_le_of_ne p.r_nonneg (Ne.symm h), fun h => h.ne'⟩

theorem preimage_qDisc_ball (ε : ℝ) :
    qDisc ⁻¹' Metric.ball 0 ε = {p : DInfty | p.r < ε} := by
  ext p; simp [DInfty.norm_cplx]

/-- `q` is a covering map over `ℂ ∖ {0}`. -/
theorem isCoveringMapOn_qDisc : IsCoveringMapOn qDisc ({0}ᶜ : Set ℂ) := by
  have h := (isCoveringMapOn_discQuot (α := 1) one_ne_zero).homeomorph_comp
    (discHomeomorph (α := 1) one_ne_zero)
  have hset : (discHomeomorph (α := 1) one_ne_zero).symm ⁻¹'
      (discQuot 1 '' {p : DInfty | 0 < p.r}) = {0}ᶜ := by
    rw [Homeomorph.preimage_symm, discHomeomorph_image_pos]
  rw [hset] at h
  exact h

/-- `{0}ᶜ` is portly in `ℂ`. -/
theorem isPortly_compl_zero_complex : IsPortly ({0}ᶜ : Set ℂ) :=
  isPortly_compl_singleton_of_chart (by rw [Complex.rank_real_complex]; norm_num)
    (Homeomorph.refl ℂ).toOpenPartialHomeomorph (mem_univ _)

/-- **`q : 𝔻_∞ → 𝔻` is a branched covering** (`RamcovGX.tex:1183`, "the quotient map which is a
branched covering"), branched over `{0}` only. -/
theorem isBranchedCovering_qDisc : IsBranchedCovering qDisc ∧ IsPossiblyBranchedOver qDisc {0} := by
  have hc : Continuous qDisc := DInfty.continuous_cplx 1
  have ho : IsOpenMap qDisc := DInfty.isOpenMap_cplx one_ne_zero
  have hsp : IsSpread qDisc := by
    refine isSpread_iff_of_locallyConnectedSpace.2 ⟨hc, fun x O hO hxO => ?_⟩
    rcases x.pos_or_eq_apex with hx | rfl
    · have hx' : qDisc x ∈ ({0}ᶜ : Set ℂ) := by
        rw [← mem_preimage, preimage_qDisc_compl_zero]; exact hx
      exact exists_cc_subset_of_isEvenlyCovered ho (isCoveringMapOn_qDisc _ hx') hO hxO
    · obtain ⟨ε, hε, h⟩ := DInfty.exists_r_lt_subset_of_isOpen hO hxO
      refine ⟨Metric.ball 0 ε, Metric.isOpen_ball, by simpa using hε, ?_⟩
      rw [preimage_qDisc_ball]
      exact (connectedComponentIn_subset _ _).trans h
  have hH := DInfty.isPortly_pos'
  have hmaps : MapsTo qDisc {p : DInfty | 0 < p.r} ({0}ᶜ : Set ℂ) := fun p hp => by
    rw [← mem_preimage, preimage_qDisc_compl_zero]; exact hp
  have hres : hmaps.restrict qDisc _ _ =
      ({0}ᶜ : Set ℂ).restrictPreimage qDisc ∘ Homeomorph.setCongr preimage_qDisc_compl_zero.symm :=
    funext fun _ => rfl
  have hcov : IsCoveringMap (hmaps.restrict qDisc _ _) := hres ▸
    isCoveringMapOn_qDisc.isCoveringMap_restrictPreimage.comp_homeomorph _
  have hsurj : Surjective (hmaps.restrict qDisc _ _) := by
    rintro ⟨w, hw⟩
    refine ⟨⟨DInfty.ofCplx 1 w, ?_⟩, Subtype.ext (DInfty.cplx_ofCplx one_ne_zero w)⟩
    show 0 < (DInfty.ofCplx 1 w).r
    rw [DInfty.ofCplx_r]; exact norm_pos_iff.2 hw
  obtain ⟨hY₁, -, -⟩ := spread_partial_covering hc hH isOpen_compl_singleton hmaps hcov hsurj
  have hcomp : IsCompleteSpread qDisc := by
    rw [isCompleteSpread_iff]
    intro e
    by_cases he : e.base = 0
    · refine ⟨DInfty.apex, fun U hU => ?_⟩
      have hU0 : IsCNbhd 0 U := he ▸ hU
      obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU0.isOpen 0 hU0.mem
      have hV : IsCNbhd e.base (Metric.ball 0 ε) := by
        rw [he]; exact ⟨Metric.isOpen_ball, (convex_ball 0 ε).isPreconnected, Metric.mem_ball_self hε⟩
      obtain ⟨x, hx, hxe⟩ := e.isCompOf _ hV
      have hpre : IsPreconnected (qDisc ⁻¹' Metric.ball 0 ε) := by
        rw [preimage_qDisc_ball]; exact (DInfty.isConnected_r_lt hε).isPreconnected
      have heV : e (Metric.ball 0 ε) = qDisc ⁻¹' Metric.ball 0 ε := by
        rw [hxe, hpre.connectedComponentIn hx]
      refine e.mono _ U hV hU hεU ?_
      rw [heV, preimage_qDisc_ball]; simpa using hε
    · obtain ⟨U, hU, heU, -, hcov⟩ := hY₁ he
      exact e.exists_mem_of_isEvenlyCoveredSet hU heU hcov
  have hbc := ((complete_path_carac.{0} hsp hH isPortly_compl_zero_complex hmaps hcov
    hsurj).out 1 0).1 hcomp
  refine ⟨hbc, fun z hz => ?_⟩
  by_contra h0
  exact hz (hY₁ h0)

/-! ### `cex:proposition_prop_branched_covering`: the paper's data -/

/-- `Y₀ = {(r, θ) | θ ∈ ]0,1[}` in coordinates (`RamcovGX.tex:1183`). -/
def cexY₀ : Set (ℝ × ℝ) := {q | 0 < q.1 ∧ 0 < q.2 ∧ q.2 < 1}

/-- `(r_n, θ_n)_{n ∈ ℤ}` is a countable dense family in `Y₀` (`RamcovGX.tex:1183`). -/
def IsDenseFamilyY₀ (r θ : ℤ → ℝ) : Prop :=
  (∀ n, (r n, θ n) ∈ cexY₀) ∧
    ∀ U : Set (ℝ × ℝ), IsOpen U → (U ∩ cexY₀).Nonempty → ∃ n, (r n, θ n) ∈ U

/-- Such a family exists. -/
theorem exists_isDenseFamilyY₀ : ∃ r θ : ℤ → ℝ, IsDenseFamilyY₀ r θ := by
  obtain ⟨s, hsc, hsd⟩ := TopologicalSpace.exists_countable_dense cexY₀
  haveI : Nonempty cexY₀ := ⟨⟨(1, 1 / 2), by norm_num [cexY₀]⟩⟩
  obtain ⟨f, hf⟩ := hsc.exists_eq_range hsd.nonempty
  refine ⟨fun n => (f n.toNat : ℝ × ℝ).1, fun n => (f n.toNat : ℝ × ℝ).2,
    fun n => (f n.toNat).2, fun U hU ⟨u, huU, huY⟩ => ?_⟩
  obtain ⟨x, hxU, hxs⟩ := hsd.inter_open_nonempty (((↑) : cexY₀ → ℝ × ℝ) ⁻¹' U)
    (hU.preimage continuous_subtype_val) ⟨⟨u, huY⟩, huU⟩
  rw [hf] at hxs
  obtain ⟨m, rfl⟩ := hxs
  refine ⟨(m : ℤ), ?_⟩
  simp only [Int.toNat_natCast]
  exact hxU

/-- The paper's `S = (r_n, θ_n + n)_{n ∈ ℤ} ⊆ 𝔻_∞` (`RamcovGX.tex:1183`). -/
def cexS (r θ : ℤ → ℝ) (hr : ∀ n, 0 < r n) : Set DInfty :=
  range fun n : ℤ => (⟨r n, θ n + n, Or.inl (hr n)⟩ : DInfty)

/-- **The paper's `S` is not skeletal** (`RamcovGX.tex:1184`, "We see that `S` is skeletal" is
false): the apex is in its closure, not in it, so `S` is not even closed. -/
theorem cexS_not_isSkeletal {r θ : ℤ → ℝ} (hd : IsDenseFamilyY₀ r θ) (hr : ∀ n, 0 < r n) :
    DInfty.apex ∈ closure (cexS r θ hr) ∧ DInfty.apex ∉ cexS r θ hr ∧
      ¬ IsClosed (cexS r θ hr) ∧ ¬ IsSkeletal (cexS r θ hr) := by
  have h1 : DInfty.apex ∈ closure (cexS r θ hr) := by
    refine (mem_closure_iff_nhds_basis DInfty.hasBasis_nhds_apex).2 fun ε hε => ?_
    obtain ⟨n, hn⟩ := hd.2 {q | q.1 < ε} (isOpen_lt continuous_fst continuous_const)
      ⟨(ε / 2, 1 / 2), by show ε / 2 < ε; linarith, by
        refine ⟨by positivity, by norm_num, by norm_num⟩⟩
    exact ⟨_, ⟨n, rfl⟩, hn⟩
  have h2 : DInfty.apex ∉ cexS r θ hr := by
    rintro ⟨n, hn⟩
    have := congrArg DInfty.r hn
    simp only [DInfty.apex_r] at this
    exact (hr n).ne' this
  have h3 : ¬ IsClosed (cexS r θ hr) := fun hc => h2 (hc.closure_eq ▸ h1)
  exact ⟨h1, h2, h3, fun hs => h3 hs.isClosed⟩

theorem qDisc_mk (a b : ℝ) (h : 0 < a ∨ (a = 0 ∧ b = 0)) :
    qDisc ⟨a, b, h⟩ = (a : ℂ) * Complex.exp (((2 * Real.pi * b : ℝ) : ℂ) * Complex.I) := by
  simp [qDisc, DInfty.cplx]

/-- A point off the real axis is `r e^{2Real.piiθ}` with `(r, θ) ∈ Y₀`. -/
theorem exists_mem_cexY₀_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) :
    ∃ q ∈ cexY₀, (q.1 : ℂ) * Complex.exp (((2 * Real.pi * q.2 : ℝ) : ℂ) * Complex.I) = z := by
  have hz0 : z ≠ 0 := fun h => hz (by rw [h, Complex.zero_im])
  have hπ := Real.pi_pos
  have hπc : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have harg := Complex.norm_mul_exp_arg_mul_I z
  rcases lt_or_gt_of_ne hz with hneg | hpos
  · have h1 := Complex.neg_pi_lt_arg z
    have h2 := Complex.arg_neg_iff.2 hneg
    refine ⟨(‖z‖, Complex.arg z / (2 * Real.pi) + 1), ⟨norm_pos_iff.2 hz0, ?_, ?_⟩, ?_⟩
    · have : -1 < Complex.arg z / (2 * Real.pi) := by
        rw [lt_div_iff₀ (by positivity)]; linarith
      show 0 < Complex.arg z / (2 * Real.pi) + 1
      linarith
    · have : Complex.arg z / (2 * Real.pi) < 0 := div_neg_of_neg_of_pos h2 (by positivity)
      show Complex.arg z / (2 * Real.pi) + 1 < 1
      linarith
    · have e : Complex.exp (((2 * Real.pi * (Complex.arg z / (2 * Real.pi) + 1) : ℝ) : ℂ) *
          Complex.I) = Complex.exp ((Complex.arg z : ℂ) * Complex.I) := by
        have : ((2 * Real.pi * (Complex.arg z / (2 * Real.pi) + 1) : ℝ) : ℂ) * Complex.I =
            (Complex.arg z : ℂ) * Complex.I + ((1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
          push_cast; field_simp
        rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
      show ((‖z‖ : ℝ) : ℂ) * _ = z
      rw [e]; exact harg
  · have h0 : 0 < Complex.arg z := lt_of_le_of_ne (Complex.arg_nonneg_iff.2 hpos.le)
      (fun h => hz (Complex.arg_eq_zero_iff.1 h.symm).2)
    have hπ' : Complex.arg z < Real.pi := Complex.arg_lt_pi_iff.2 (Or.inr hz)
    refine ⟨(‖z‖, Complex.arg z / (2 * Real.pi)), ⟨norm_pos_iff.2 hz0, ?_, ?_⟩, ?_⟩
    · show 0 < Complex.arg z / (2 * Real.pi); positivity
    · show Complex.arg z / (2 * Real.pi) < 1
      rw [div_lt_one (by positivity)]; linarith
    · have e : Complex.exp (((2 * Real.pi * (Complex.arg z / (2 * Real.pi)) : ℝ) : ℂ) *
          Complex.I) = Complex.exp ((Complex.arg z : ℂ) * Complex.I) := by
        congr 1; push_cast; field_simp
      show ((‖z‖ : ℝ) : ℂ) * _ = z
      rw [e]; exact harg

/-- **`q(S)` is dense in `𝔻`** (`RamcovGX.tex:1186`, with `α = 1`). -/
theorem dense_qDisc_image_cexS {r θ : ℤ → ℝ} (hd : IsDenseFamilyY₀ r θ) (hr : ∀ n, 0 < r n) :
    Dense (qDisc '' cexS r θ hr) := by
  set F : ℝ × ℝ → ℂ := fun q => (q.1 : ℂ) * Complex.exp (((2 * Real.pi * q.2 : ℝ) : ℂ) * Complex.I)
  have hF : Continuous F := by fun_prop
  have hFS : ∀ n, qDisc ⟨r n, θ n + n, Or.inl (hr n)⟩ = F (r n, θ n) := fun n => by
    rw [qDisc_mk]
    show _ = (r n : ℂ) * Complex.exp (((2 * Real.pi * θ n : ℝ) : ℂ) * Complex.I)
    have : ((2 * Real.pi * (θ n + n) : ℝ) : ℂ) * Complex.I =
        ((2 * Real.pi * θ n : ℝ) : ℂ) * Complex.I + (n : ℤ) * (2 * Real.pi * Complex.I) := by
      push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  refine dense_iff_inter_open.2 fun V hV ⟨z₀, hz₀⟩ => ?_
  obtain ⟨δ, hδ, hδV⟩ := Metric.isOpen_iff.1 hV z₀ hz₀
  -- a point of `V` off the real axis
  obtain ⟨z, hzV, hz⟩ : ∃ z ∈ V, z.im ≠ 0 := by
    by_cases h : z₀.im = 0
    · refine ⟨z₀ + ((δ / 2 : ℝ) : ℂ) * Complex.I, hδV ?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I,
          mul_one, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        linarith
      · simp [h, hδ.ne']
    · exact ⟨z₀, hz₀, h⟩
  obtain ⟨q, hqY, hqz⟩ := exists_mem_cexY₀_of_im_ne_zero hz
  obtain ⟨n, hn⟩ := hd.2 (F ⁻¹' V) (hV.preimage hF) ⟨q, by
    show F q ∈ V; rw [show F q = z from hqz]; exact hzV, hqY⟩
  exact ⟨_, (by rw [hFS n]; exact hn : qDisc _ ∈ V), _, ⟨n, rfl⟩, rfl⟩

/-- **`cex:proposition_prop_branched_covering`, the true core** (`RamcovGX.tex:1186–1187`): for
any branched covering `p : X → 𝔻_∞` whose branching locus contains a set `T` with `q(T)` dense
in `𝔻`, the composite `q ∘ p` is **not** a branched covering. -/
theorem not_isBranchedCovering_qDisc_comp {X : Type*} [TopologicalSpace X] [T2Space X]
    [LocPathConnectedSpace X] [FirstCountableTopology X] {p : X → DInfty}
    (hp : IsBranchedCovering p) {T : Set DInfty} (hT : Dense (qDisc '' T))
    (hTB : T ⊆ branchingLocus p) : ¬ IsBranchedCovering (qDisc ∘ p) := by
  intro h
  have hsk := isSkeletal_closure_image_branchingLocus hp isBranchedCovering_qDisc.1 h
  have : closure (qDisc '' branchingLocus p) = univ :=
    eq_univ_of_univ_subset (hT.closure_eq ▸ closure_mono (image_mono hTB))
  rw [this] at hsk
  have := (isSkeletal_iff.1 hsk).dense
  rw [compl_univ] at this
  exact (this.nonempty).ne_empty rfl

/-! ### A covering of `𝔻_∞` branched at a prescribed discrete set -/

/-- Semilocal simple connectedness is invariant under homeomorphisms. -/
theorem SemilocallySimplyConnected.of_homeomorph {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] (e : A ≃ₜ B) (hA : SemilocallySimplyConnected A) :
    SemilocallySimplyConnected B := by
  intro b
  obtain ⟨a, rfl⟩ := e.surjective b
  obtain ⟨U, hU, hUγ⟩ := hA a
  refine ⟨e '' U, e.isOpenMap.image_mem_nhds hU, fun γ hγ => ?_⟩
  let γ' : Path a a :=
    { toFun := fun t => e.symm (γ t)
      continuous_toFun := e.symm.continuous.comp γ.continuous
      source' := by simp
      target' := by simp }
  have hγ' : ∀ t, γ' t ∈ U := fun t => by
    obtain ⟨u, hu, hut⟩ := hγ t
    show e.symm (γ t) ∈ U
    rw [← hut, e.symm_apply_apply]; exact hu
  have h := (hUγ γ' hγ').map (⟨e, e.continuous⟩ : C(A, B))
  have h1 : γ'.map e.continuous = γ := by ext t; simp [γ']
  have h2 : (Path.refl a).map e.continuous = Path.refl (e a) := by ext t; simp
  rw [h1, h2] at h
  exact h

/-- An open subset of a real normed space is semilocally simply connected. -/
theorem semilocallySimplyConnected_of_isOpen {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {O : Set E} (hO : IsOpen O) : SemilocallySimplyConnected O := by
  intro y
  obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.1 hO y y.2
  refine ⟨(↑) ⁻¹' Metric.ball (y : E) ε,
    (Metric.isOpen_ball.preimage continuous_subtype_val).mem_nhds (Metric.mem_ball_self hε),
    fun γ hγ => ?_⟩
  haveI : ContractibleSpace (Metric.ball (y : E) ε) :=
    (convex_ball (y : E) ε).contractibleSpace (Metric.nonempty_ball.2 hε)
  let yb : Metric.ball (y : E) ε := ⟨y, Metric.mem_ball_self hε⟩
  let γb : Path yb yb :=
    { toFun := fun t => ⟨γ t, hγ t⟩
      continuous_toFun := (continuous_subtype_val.comp γ.continuous).subtype_mk _
      source' := Subtype.ext (by simp [yb])
      target' := Subtype.ext (by simp [yb]) }
  let ι : C(Metric.ball (y : E) ε, O) := ⟨fun z => ⟨z, hεO z.2⟩, by fun_prop⟩
  have h := (SimplyConnectedSpace.paths_homotopic γb (Path.refl yb)).map ι
  have h1 : γb.map ι.continuous = γ := by ext t; rfl
  have h2 : (Path.refl yb).map ι.continuous = Path.refl y := by ext t; rfl
  rw [h1, h2] at h
  exact h

/-- A loop of `ℂ ∖ {0}` lifting through `exp` to a path with distinct endpoints is not
null-homotopic. -/
theorem not_homotopic_refl_of_exp_lift {z : {w : ℂ // w ≠ 0}} (δ : Path z z) (Γ : C(I, ℂ))
    (hΓ : ∀ t, Complex.exp (Γ t) = δ t) (hΓ1 : Γ 1 ≠ Γ 0) : ¬ δ.Homotopic (Path.refl z) := by
  intro h
  have cov := Complex.isCoveringMap_exp
  obtain ⟨H⟩ := h
  have hrel : δ.toContinuousMap.HomotopicRel (Path.refl z).toContinuousMap {0, 1} := ⟨H⟩
  have h0 : (z : ℂ) = Complex.exp (Γ 0) := by rw [hΓ 0, δ.source]
  have hδ0 : δ.toContinuousMap 0 = ⟨Complex.exp (Γ 0), Complex.exp_ne_zero _⟩ :=
    Subtype.ext (by simpa using h0)
  have hr0 : (Path.refl z).toContinuousMap 0 = ⟨Complex.exp (Γ 0), Complex.exp_ne_zero _⟩ :=
    Subtype.ext (by simpa using h0)
  have key := cov.liftPath_apply_one_eq_of_homotopicRel hrel (Γ 0) hδ0 hr0
  have hl1 : cov.liftPath δ.toContinuousMap (Γ 0) hδ0 = Γ :=
    ((cov.eq_liftPath_iff' (γ := δ.toContinuousMap) (e := Γ 0) hδ0).2
      ⟨funext fun t => Subtype.ext (by simp [hΓ t]), rfl⟩).symm
  have hl2 : cov.liftPath (Path.refl z).toContinuousMap (Γ 0) hr0 = ContinuousMap.const I (Γ 0) :=
    ((cov.eq_liftPath_iff' (γ := (Path.refl z).toContinuousMap) (e := Γ 0)
      (Γ := ContinuousMap.const I (Γ 0)) hr0).2
      ⟨funext fun t => Subtype.ext (by simpa using h0.symm), rfl⟩).symm
  rw [hl1, hl2] at key
  exact hΓ1 key

namespace DInfty

theorem two_pi_div_one_ne_zero : (2 * Real.pi / 1 : ℝ) ≠ 0 :=
  div_ne_zero (by positivity) one_ne_zero

/-- The log-polar chart `ℂ → 𝔻_∞`, `w ↦ (e^{Re w}, Im w / 2π)`: an open embedding onto
`{r > 0}`, in which `q` is the exponential. -/
def logChart (w : ℂ) : DInfty := posEmb ((logHomeo two_pi_div_one_ne_zero).symm w)

theorem isOpenEmbedding_logChart : IsOpenEmbedding logChart :=
  isOpenEmbedding_posEmb.comp (logHomeo two_pi_div_one_ne_zero).symm.isOpenEmbedding

theorem range_logChart : range logChart = {p : DInfty | 0 < p.r} := by
  rw [← range_posEmb]
  exact (logHomeo two_pi_div_one_ne_zero).symm.surjective.range_comp posEmb

theorem logChart_r_pos (w : ℂ) : 0 < (logChart w).r :=
  ((logHomeo two_pi_div_one_ne_zero).symm w).2

theorem logChart_ne_apex (w : ℂ) : logChart w ≠ apex := fun h => by
  have := logChart_r_pos w
  rw [h, apex_r] at this
  exact lt_irrefl _ this

end DInfty

theorem qDisc_logChart (w : ℂ) : qDisc (DInfty.logChart w) = Complex.exp w := by
  show DInfty.cplx 1 (DInfty.posEmb _) = _
  rw [DInfty.cplx_posEmb 1 one_ne_zero, Homeomorph.apply_symm_apply]

section Branch

open DInfty

/-- The branching set `{apex} ∪ ψ(T)` for `T ⊆ ℂ`. -/
def branchSet (T : Set ℂ) : Set DInfty := insert apex (logChart '' T)

theorem compl_branchSet (T : Set ℂ) : (branchSet T)ᶜ = logChart '' Tᶜ := by
  ext x
  simp only [branchSet, mem_compl_iff, mem_insert_iff, not_or, mem_image]
  constructor
  · rintro ⟨hxa, hxT⟩
    obtain ⟨w, rfl⟩ : x ∈ range logChart := by
      rw [range_logChart]
      exact lt_of_le_of_ne x.r_nonneg fun h => hxa (eq_apex_of_not_pos (by rw [← h]; simp))
    exact ⟨w, fun hw => hxT ⟨w, hw, rfl⟩, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    refine ⟨logChart_ne_apex w, ?_⟩
    rintro ⟨w', hw', h⟩
    exact hw (isOpenEmbedding_logChart.injective h ▸ hw')

/-- `{apex} ∪ ψ(T)` is skeletal for `T` closed and countable. -/
theorem isSkeletal_branchSet {T : Set ℂ} (hTc : IsClosed T) (hT : T.Countable) :
    IsSkeletal (branchSet T) := by
  rw [isSkeletal_iff, compl_branchSet]
  have hemb := isOpenEmbedding_logChart
  have hdr : DenseRange logChart := by
    rw [DenseRange, range_logChart]; exact DInfty.isPortly_pos'.dense
  refine ⟨hemb.isOpenMap _ hTc.isOpen_compl,
    hdr.dense_image hemb.continuous (hT.dense_compl ℂ), fun W hW hWc => ?_⟩
  have h1 : IsPreconnected (W ∩ {p : DInfty | 0 < p.r}) :=
    DInfty.isPortly_pos'.locallyConnectedIn W hW hWc
  rw [← range_logChart, ← image_preimage_eq_inter_range] at h1
  have h2 : IsPreconnected (logChart ⁻¹' W) := hemb.isInducing.isPreconnected_image.1 h1
  have h3 := isPreconnected_diff_countable hT (hW.preimage hemb.continuous) h2
  rw [sdiff_eq] at h3
  rw [inter_comm] at h3
  have := h3.image _ hemb.continuous.continuousOn
  rw [image_inter_preimage] at this
  rwa [inter_comm]

/-- The complement of `{apex} ∪ ψ(T)` is homeomorphic to `ℂ ∖ T`. -/
def branchSetComplHomeo (T : Set ℂ) : (Tᶜ : Set ℂ) ≃ₜ ((branchSet T)ᶜ : Set DInfty) :=
  (isOpenEmbedding_logChart.isEmbedding.comp IsEmbedding.subtypeVal).toHomeomorph.trans
    (Homeomorph.setCongr (s := range (logChart ∘ (Subtype.val : (Tᶜ : Set ℂ) → ℂ)))
      (t := (branchSet T)ᶜ) (by rw [range_comp, Subtype.range_coe, compl_branchSet]))

theorem branchSetComplHomeo_apply (T : Set ℂ) (w : (Tᶜ : Set ℂ)) :
    (branchSetComplHomeo T w : DInfty) = logChart w := by
  rw [branchSetComplHomeo, Homeomorph.trans_apply]
  exact IsEmbedding.toHomeomorph_apply_coe
    (isOpenEmbedding_logChart.isEmbedding.comp IsEmbedding.subtypeVal) w

theorem semilocallySimplyConnected_branchSet {T : Set ℂ} (hTc : IsClosed T) :
    SemilocallySimplyConnected ((branchSet T)ᶜ : Set DInfty) :=
  (semilocallySimplyConnected_of_isOpen hTc.isOpen_compl).of_homeomorph (branchSetComplHomeo T)

/-- **Every isolated point of `T` is a branching point** of the maximal covering of `𝔻_∞` possibly
branched over `{apex} ∪ ψ(T)` (the loop around it is not null-homotopic in `𝔻_∞ ∖ ({apex} ∪ ψ(T))`,
detected by the exponential covering). -/
theorem logChart_mem_branchingLocus {T : Set ℂ} (hTc : IsClosed T) (hT : T.Countable)
    (y₀ : ((branchSet T)ᶜ : Set DInfty)) {t : ℂ} (ht : t ∈ T) {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hiso : Metric.ball t ρ₀ ∩ T = {t}) :
    logChart t ∈ branchingLocus (SpreadEnd.base : MaxBranchedCover (branchSet T) y₀ → DInfty) := by
  have hS := isSkeletal_branchSet hTc hT
  have hSc := semilocallySimplyConnected_branchSet hTc
  have hO : IsPortly ((branchSet T)ᶜ : Set DInfty) := isSkeletal_iff.1 hS
  haveI : LocPathConnectedSpace ((branchSet T)ᶜ : Set DInfty) := hO.isOpen.locPathConnectedSpace
  haveI : PathConnectedSpace ((branchSet T)ᶜ : Set DInfty) :=
    pathConnectedSpace_iff_connectedSpace.2 (isConnected_iff_connectedSpace.1 hO.isConnected)
  obtain ⟨-, -, -, -, hl, hsp⟩ := maxBranched_basic hS hSc y₀
  haveI := hl
  haveI : T2Space (UniversalCover ((branchSet T)ᶜ : Set DInfty) y₀) :=
    t2Space_of_isCoveringMap (UniversalCover.isCoveringMap_proj (y₀ := y₀) hSc)
  have hemb := SpreadEnd.isEmbedding_ofPoint hsp
  intro hs
  obtain ⟨U, hUo, hsU, -, hcov⟩ := hs
  obtain ⟨ρ₁, hρ₁, hρ₁U⟩ := Metric.isOpen_iff.1 (hUo.preimage isOpenEmbedding_logChart.continuous)
    t hsU
  set ρ := min ρ₀ ρ₁
  have hρ : 0 < ρ := lt_min hρ₀ hρ₁
  set D := logChart '' Metric.ball t ρ
  have hDo : IsOpen D := isOpenEmbedding_logChart.isOpenMap _ Metric.isOpen_ball
  have hDc : IsPreconnected D :=
    (convex_ball t ρ).isPreconnected.image _ isOpenEmbedding_logChart.continuous.continuousOn
  have hDU : D ⊆ U := by
    rintro _ ⟨w, hw, rfl⟩
    exact hρ₁U (Metric.ball_subset_ball (min_le_right _ _) hw)
  have hcovD : IsEvenlyCoveredSet (SpreadEnd.base : MaxBranchedCover (branchSet T) y₀ → DInfty) D :=
    hcov.mono_of_isPreconnected SpreadEnd.continuous_base hUo hDo hDc hDU
  -- the loop `t + (ρ/2) e^{2πiτ}`
  set c₀ : C(I, ℂ) := ⟨fun τ => t + ((ρ / 2 : ℝ) : ℂ) *
      Complex.exp (((2 * Real.pi * (τ : ℝ) : ℝ) : ℂ) * Complex.I), by fun_prop⟩
  have hc₀ : ∀ τ, c₀ τ - t = ((ρ / 2 : ℝ) : ℂ) *
      Complex.exp (((2 * Real.pi * (τ : ℝ) : ℝ) : ℂ) * Complex.I) := fun τ => by
    simp [c₀]
  have hc₀d : ∀ τ, dist (c₀ τ) t = ρ / 2 := fun τ => by
    rw [dist_eq_norm, hc₀, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  have hc₀b : ∀ τ, c₀ τ ∈ Metric.ball t ρ := fun τ => by
    rw [Metric.mem_ball, hc₀d]; linarith
  have hc₀T : ∀ τ, c₀ τ ∈ Tᶜ := fun τ hT' => by
    have hmem : c₀ τ ∈ Metric.ball t ρ₀ ∩ T :=
      ⟨Metric.ball_subset_ball (min_le_left _ _) (hc₀b τ), hT'⟩
    rw [hiso, mem_singleton_iff] at hmem
    have := hc₀d τ
    rw [hmem, dist_self] at this
    linarith
  have hc₀0 : c₀ 0 = t + ((ρ / 2 : ℝ) : ℂ) := by simp [c₀]
  have hc₀1 : c₀ 1 = t + ((ρ / 2 : ℝ) : ℂ) := by
    simp only [c₀, ContinuousMap.coe_mk, Set.Icc.coe_one, mul_one]
    rw [show (((2 * Real.pi : ℝ) : ℂ) * Complex.I) = ((1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by
      push_cast; ring, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  set w₁ : (Tᶜ : Set ℂ) := ⟨t + ((ρ / 2 : ℝ) : ℂ), hc₀0 ▸ hc₀T 0⟩
  let γT : Path w₁ w₁ :=
    { toFun := fun τ => ⟨c₀ τ, hc₀T τ⟩
      continuous_toFun := c₀.continuous.subtype_mk _
      source' := Subtype.ext hc₀0
      target' := Subtype.ext hc₀1 }
  set hom := branchSetComplHomeo T
  set y₁ := hom w₁
  let γS : Path y₁ y₁ := γT.map hom.continuous
  have hγS : ∀ τ, (γS τ : DInfty) = logChart (c₀ τ) := fun τ =>
    branchSetComplHomeo_apply T (γT τ)
  -- lift through the universal covering, then to the completion
  let c₁ : UniversalCover ((branchSet T)ᶜ : Set DInfty) y₀ :=
    ⟨y₁, Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath y₀ y₁)⟩
  let Λ := UniversalCover.liftFrom c₁.cls γS
  set ι := SpreadEnd.ofPoint (univCoverProj (branchSet T) y₀)
  have hbase : ∀ c : UniversalCover ((branchSet T)ᶜ : Set DInfty) y₀, (ι c).base = (c.pt : DInfty) :=
    fun _ => rfl
  have hA : ∀ τ, ι (Λ τ) ∈ (SpreadEnd.base ⁻¹' D : Set (MaxBranchedCover (branchSet T) y₀)) := fun τ => by
    show (ι (Λ τ)).base ∈ D
    rw [hbase, UniversalCover.proj_liftFrom, hγS]
    exact ⟨_, hc₀b τ, rfl⟩
  have hrange : range (ι ∘ Λ) ⊆
      connectedComponentIn (SpreadEnd.base ⁻¹' D) (ι (Λ 0)) :=
    (isPreconnected_range ((SpreadEnd.continuous_ofPoint hsp).comp Λ.continuous)).subset_connectedComponentIn
      ⟨0, rfl⟩ (by rintro _ ⟨τ, rfl⟩; exact hA τ)
  have hinj := hcovD.injOn (hA 0)
  have h10 : ι (Λ 1) = ι (Λ 0) := hinj (hrange ⟨1, rfl⟩) (hrange ⟨0, rfl⟩) (by
    show (ι (Λ 1)).base = (ι (Λ 0)).base
    rw [hbase, hbase, UniversalCover.proj_liftFrom, UniversalCover.proj_liftFrom, γS.source,
      γS.target])
  have hΛ := hemb.injective h10
  rw [Λ.source, Λ.target] at hΛ
  have hcls : c₁.cls.trans (Path.Homotopic.Quotient.mk γS) =
      c₁.cls.trans (Path.Homotopic.Quotient.refl y₁) := by
    rw [Path.Homotopic.Quotient.trans_refl]
    exact eq_of_heq (UniversalCover.mk.inj hΛ).2
  have hhom : γS.Homotopic (Path.refl y₁) := by
    rw [← Path.Homotopic.Quotient.eq, Path.Homotopic.Quotient.mk_refl]
    exact quot_trans_left_cancel _ hcls
  -- push to `ℂ ∖ {0}` by `y ↦ ψ⁻¹(y) - t`
  have hne : ∀ y : ((branchSet T)ᶜ : Set DInfty), ((hom.symm y : ℂ) - t) ≠ 0 := fun y h => by
    have := (hom.symm y).2
    rw [sub_eq_zero] at h
    rw [h] at this
    exact this ht
  let Φ : C(((branchSet T)ᶜ : Set DInfty), {w : ℂ // w ≠ 0}) :=
    ⟨fun y => ⟨(hom.symm y : ℂ) - t, hne y⟩, by
      refine Continuous.subtype_mk ?_ _
      exact (continuous_subtype_val.comp hom.symm.continuous).sub continuous_const⟩
  have hh := hhom.map Φ
  have hrefl : (Path.refl y₁).map Φ.continuous = Path.refl (Φ y₁) := by ext; rfl
  rw [hrefl] at hh
  refine not_homotopic_refl_of_exp_lift (γS.map Φ.continuous)
    ⟨fun τ => (Real.log (ρ / 2) : ℂ) + ((2 * Real.pi * (τ : ℝ) : ℝ) : ℂ) * Complex.I,
      by fun_prop⟩ (fun τ => ?_) ?_ hh
  · show Complex.exp ((Real.log (ρ / 2) : ℂ) + ((2 * Real.pi * (τ : ℝ) : ℝ) : ℂ) * Complex.I) =
      ((hom.symm (hom (γT τ)) : ℂ) - t)
    rw [hom.symm_apply_apply]
    show _ = c₀ τ - t
    rw [hc₀, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log (by positivity)]
  · simp only [ContinuousMap.coe_mk, Set.Icc.coe_one, Set.Icc.coe_zero, mul_one, mul_zero,
      Complex.ofReal_zero, zero_mul, add_zero, ne_eq, add_eq_left]
    intro h
    have := congrArg Complex.im h
    simp at this

end Branch

section Branch'

open DInfty

/-- **A covering of `𝔻_∞` branched exactly where prescribed**: for `T ⊆ ℂ` closed, countable and
discrete, the maximal covering possibly branched over `{apex} ∪ ψ(T)` is branched at every point
of `ψ(T)`. -/
theorem exists_branched_over {T : Set ℂ} (hTc : IsClosed T) (hT : T.Countable)
    (hiso : ∀ t ∈ T, ∃ ρ > 0, Metric.ball t ρ ∩ T = {t}) (y₀ : ((branchSet T)ᶜ : Set DInfty)) :
    IsBranchedCovering (SpreadEnd.base : MaxBranchedCover (branchSet T) y₀ → DInfty) ∧
      logChart '' T ⊆ branchingLocus (SpreadEnd.base : MaxBranchedCover (branchSet T) y₀ → DInfty) ∧
      branchingLocus (SpreadEnd.base : MaxBranchedCover (branchSet T) y₀ → DInfty) ⊆
        branchSet T := by
  obtain ⟨hbc, hpb⟩ := maxBranched_isBranchedCovering (isSkeletal_branchSet hTc hT)
    (semilocallySimplyConnected_branchSet hTc) y₀
  refine ⟨hbc, ?_, hpb⟩
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨ρ, hρ, h⟩ := hiso t ht
  exact logChart_mem_branchingLocus hTc hT y₀ ht hρ h

theorem nonempty_compl_branchSet {T : Set ℂ} (hTc : IsClosed T) (hT : T.Countable) :
    ((branchSet T)ᶜ : Set DInfty).Nonempty :=
  (isSkeletal_iff.1 (isSkeletal_branchSet hTc hT)).dense.nonempty

/-- A set of `ℂ` meeting every unit ball in finitely many points is closed and discrete. -/
theorem isClosed_isolated_of_finite_ball {T : Set ℂ} (h : ∀ x, (Metric.ball x 1 ∩ T).Finite) :
    IsClosed T ∧ ∀ t ∈ T, ∃ ρ > 0, Metric.ball t ρ ∩ T = {t} := by
  have key : ∀ x : ℂ, ∃ N : Set ℂ, IsOpen N ∧ x ∈ N ∧ N ∩ T ⊆ {x} := fun x => by
    refine ⟨Metric.ball x 1 ∩ ((Metric.ball x 1 ∩ T) \ {x})ᶜ,
      Metric.isOpen_ball.inter ((h x).sdiff.isClosed.isOpen_compl),
      ⟨Metric.mem_ball_self one_pos, fun hx => hx.2 rfl⟩, ?_⟩
    rintro z ⟨⟨hzb, hzc⟩, hzT⟩
    by_contra hzx
    exact hzc ⟨⟨hzb, hzT⟩, hzx⟩
  refine ⟨isClosed_of_closure_subset fun x hx => ?_, fun t ht => ?_⟩
  · obtain ⟨N, hN, hxN, hNT⟩ := key x
    obtain ⟨z, hzN, hzT⟩ := mem_closure_iff.1 hx N hN hxN
    rw [← mem_singleton_iff.1 (hNT ⟨hzN, hzT⟩)]; exact hzT
  · obtain ⟨N, hN, htN, hNT⟩ := key t
    obtain ⟨ρ, hρ, hρN⟩ := Metric.isOpen_iff.1 hN t htN
    refine ⟨ρ, hρ, Subset.antisymm (fun z hz => hNT ⟨hρN hz.1, hz.2⟩) ?_⟩
    rintro _ rfl; exact ⟨Metric.mem_ball_self hρ, ht⟩

/-- A family with `Im f(n) ∈ (2πn, 2π(n+1))` meets every unit ball in finitely many points. -/
theorem finite_ball_inter_range_of_im {f : ℤ → ℂ}
    (hf : ∀ n, 2 * Real.pi * n < (f n).im ∧ (f n).im < 2 * Real.pi * (n + 1)) (x : ℂ) :
    (Metric.ball x 1 ∩ range f).Finite := by
  have hπ := Real.pi_pos
  refine ((Set.finite_Icc (⌊(x.im - 1) / (2 * Real.pi)⌋ - 1) ⌈(x.im + 1) / (2 * Real.pi)⌉).image
    f).subset ?_
  rintro _ ⟨hz, n, rfl⟩
  have him : |(f n).im - x.im| < 1 := by
    have := Complex.abs_im_le_norm (f n - x)
    rw [Complex.sub_im] at this
    exact lt_of_le_of_lt this (by rw [← dist_eq_norm]; exact hz)
  rw [abs_lt] at him
  obtain ⟨h1, h2⟩ := hf n
  refine ⟨n, ⟨?_, ?_⟩, rfl⟩
  · have : (x.im - 1) / (2 * Real.pi) - 1 < n := by
      rw [sub_lt_iff_lt_add, div_lt_iff₀ (by positivity)]; nlinarith
    have h3 : ((⌊(x.im - 1) / (2 * Real.pi)⌋ : ℤ) : ℝ) - 1 < n := by
      linarith [Int.floor_le ((x.im - 1) / (2 * Real.pi))]
    have : ⌊(x.im - 1) / (2 * Real.pi)⌋ - 1 < n := by exact_mod_cast h3
    omega
  · have : (n : ℝ) < (x.im + 1) / (2 * Real.pi) := by
      rw [lt_div_iff₀ (by positivity)]; nlinarith
    have : (n : ℝ) < ⌈(x.im + 1) / (2 * Real.pi)⌉ := lt_of_lt_of_le this (Int.le_ceil _)
    exact_mod_cast this.le

/-- The paper's `S` in log-polar coordinates. -/
def cexT (r θ : ℤ → ℝ) (hr : ∀ n, 0 < r n) : Set ℂ :=
  range fun n => logHomeo two_pi_div_one_ne_zero ⟨(r n, θ n + n), hr n⟩

theorem logChart_image_cexT (r θ : ℤ → ℝ) (hr : ∀ n, 0 < r n) :
    logChart '' cexT r θ hr = cexS r θ hr := by
  rw [cexT, ← range_comp]
  congr 1
  funext n
  simp only [comp_apply, logChart, Homeomorph.symm_apply_apply]
  rfl

theorem im_logHomeo (q : {q : ℝ × ℝ // 0 < q.1}) :
    (logHomeo two_pi_div_one_ne_zero q).im = 2 * Real.pi / 1 * q.1.2 := by
  simp [logHomeo]

theorem cexT_props {r θ : ℤ → ℝ} (hd : IsDenseFamilyY₀ r θ) (hr : ∀ n, 0 < r n) :
    IsClosed (cexT r θ hr) ∧ (cexT r θ hr).Countable ∧
      ∀ t ∈ cexT r θ hr, ∃ ρ > 0, Metric.ball t ρ ∩ cexT r θ hr = {t} := by
  have hfin := finite_ball_inter_range_of_im (f := fun n =>
    logHomeo two_pi_div_one_ne_zero ⟨(r n, θ n + n), hr n⟩) fun n => by
      rw [im_logHomeo]
      obtain ⟨-, h1, h2⟩ := hd.1 n
      have hπ := Real.pi_pos
      constructor <;> simp only [div_one] <;> nlinarith
  obtain ⟨hc, hi⟩ := isClosed_isolated_of_finite_ball hfin
  exact ⟨hc, countable_range _, hi⟩

/-- **`cex:proposition_prop_branched_covering`, in the corrected form ruled by DEC-53**
(`RamcovGX.tex:1181`; the printed `S` is not skeletal, `cexS_not_isSkeletal`): with
`S` the paper's set and `S' = S ∪ {apex}` (skeletal, with `𝔻_∞ ∖ S'` semilocally simply connected),
for **every** base point `y₀ ∉ S'`, the maximal covering `p : \widetilde{𝔻_∞}^{S'} → 𝔻_∞`
possibly branched over `S'` is a branched covering whose branching locus is **exactly** `S'`
(so `Y ∖ ord_p(Y) = S ∪ {apex}`), hence `q(Y ∖ ord_p(Y)) = q(S) ∪ {0}`, which is **not** the
printed `q(S)` (`RamcovGX.tex:1186`: `0 ∉ q(S)`); `q` is a branched covering, and `q ∘ p` is
**not** a branched covering. -/
theorem cex_branched_covering_composition {r θ : ℤ → ℝ} (hd : IsDenseFamilyY₀ r θ)
    (hr : ∀ n, 0 < r n) :
    IsSkeletal (insert apex (cexS r θ hr)) ∧
      SemilocallySimplyConnected ((insert apex (cexS r θ hr))ᶜ : Set DInfty) ∧
      ((insert apex (cexS r θ hr))ᶜ : Set DInfty).Nonempty ∧
      ∀ y₀ : ((insert apex (cexS r θ hr))ᶜ : Set DInfty),
        IsBranchedCovering
          (SpreadEnd.base : MaxBranchedCover (insert apex (cexS r θ hr)) y₀ → DInfty) ∧
        cexS r θ hr ⊆
          branchingLocus (SpreadEnd.base : MaxBranchedCover (insert apex (cexS r θ hr)) y₀ → DInfty) ∧
        branchingLocus (SpreadEnd.base : MaxBranchedCover (insert apex (cexS r θ hr)) y₀ → DInfty) =
          insert apex (cexS r θ hr) ∧
        qDisc '' branchingLocus
            (SpreadEnd.base : MaxBranchedCover (insert apex (cexS r θ hr)) y₀ → DInfty) =
          insert 0 (qDisc '' cexS r θ hr) ∧
        qDisc '' branchingLocus
            (SpreadEnd.base : MaxBranchedCover (insert apex (cexS r θ hr)) y₀ → DInfty) ≠
          qDisc '' cexS r θ hr ∧
        IsBranchedCovering qDisc ∧
        ¬ IsBranchedCovering
          (qDisc ∘ (SpreadEnd.base : MaxBranchedCover (insert apex (cexS r θ hr)) y₀ → DInfty)) := by
  obtain ⟨hTc, hTcount, hTi⟩ := cexT_props hd hr
  have hS : branchSet (cexT r θ hr) = insert apex (cexS r θ hr) := by
    rw [branchSet, logChart_image_cexT]
  have hsk := isSkeletal_branchSet hTc hTcount
  have hsl := semilocallySimplyConnected_branchSet hTc
  have hne := nonempty_compl_branchSet hTc hTcount
  rw [hS] at hsk hsl hne
  refine ⟨hsk, hsl, hne, fun y₀ => ?_⟩
  have h := exists_branched_over hTc hTcount hTi ⟨y₀.1, by rw [hS]; exact y₀.2⟩
  rw [logChart_image_cexT] at h
  obtain ⟨hbc, hB, hU⟩ := h
  revert hbc hB hU
  generalize hS' : branchSet (cexT r θ hr) = S' at *
  subst hS
  intro hbc hB hU
  obtain ⟨-, -, -, -, hl, -⟩ := maxBranched_basic hsk hsl y₀
  haveI := hl
  -- the branching locus is closed and contains `S`, hence the apex (in the closure of `S`)
  have hEq : branchingLocus (SpreadEnd.base : MaxBranchedCover (insert apex (cexS r θ hr)) y₀ →
      DInfty) = insert apex (cexS r θ hr) := by
    refine Subset.antisymm hU ?_
    rw [insert_subset_iff]
    refine ⟨?_, hB⟩
    have hcl : IsClosed (branchingLocus (SpreadEnd.base :
        MaxBranchedCover (insert apex (cexS r θ hr)) y₀ → DInfty)) :=
      isOpen_ordY.isClosed_compl
    exact hcl.closure_subset_iff.2 hB (cexS_not_isSkeletal hd hr).1
  have h0 : (0 : ℂ) ∉ qDisc '' cexS r θ hr := by
    rintro ⟨_, ⟨n, rfl⟩, hn⟩
    exact (hr n).ne' ((qDisc_eq_zero_iff _).1 hn)
  have hIm : qDisc '' branchingLocus (SpreadEnd.base :
      MaxBranchedCover (insert apex (cexS r θ hr)) y₀ → DInfty) =
        insert 0 (qDisc '' cexS r θ hr) := by
    rw [hEq, image_insert_eq]
    congr 1
    exact (qDisc_eq_zero_iff _).2 rfl
  refine ⟨hbc, hB, hEq, hIm, ?_, isBranchedCovering_qDisc.1,
    not_isBranchedCovering_qDisc_comp hbc (dense_qDisc_image_cexS hd hr) hB⟩
  rw [hIm]
  exact fun h => h0 (h ▸ mem_insert _ _)

end Branch'

/-! ### `prop:branched_covering_composition`: the printed (i) ⇒ (ii) is false -/

section Literal

open DInfty

/-- A closed countable subset of `ℂ` is skeletal. -/
theorem isSkeletal_of_countable_complex {C : Set ℂ} (hc : IsClosed C) (hC : C.Countable) :
    IsSkeletal C := by
  rw [isSkeletal_iff]
  refine ⟨hc.isOpen_compl, hC.dense_compl ℂ, fun W hW hWc => ?_⟩
  rw [← sdiff_eq]
  exact isPreconnected_diff_countable hC hW hWc

/-- `ε_n = 1/(|n| + 2) ∈ (0, 1/2]`. -/
def litε (n : ℤ) : ℝ := 1 / ((n.natAbs : ℝ) + 2)

theorem litε_pos (n : ℤ) : 0 < litε n := by unfold litε; positivity

theorem litε_lt_one (n : ℤ) : litε n < 1 := by
  unfold litε
  rw [div_lt_one (by positivity)]
  have : (0 : ℝ) ≤ n.natAbs := Nat.cast_nonneg _
  linarith

/-- The branching points `b_n = (1 + ε_n, n + ε_n)`, in log-polar coordinates. -/
def litT : Set ℂ :=
  range fun n : ℤ => logHomeo two_pi_div_one_ne_zero
    ⟨(1 + litε n, n + litε n), by linarith [litε_pos n]⟩

/-- Their images in `𝔻 ≅ ℂ`: `(1 + ε) e^{2πiε}`, `ε = 1/(m + 2)`. -/
def litU (m : ℕ) : ℂ :=
  ((1 + 1 / ((m : ℝ) + 2) : ℝ) : ℂ) *
    Complex.exp (((2 * Real.pi * (1 / ((m : ℝ) + 2)) : ℝ) : ℂ) * Complex.I)

theorem exp_period (a : ℝ) (n : ℤ) :
    Complex.exp (((2 * Real.pi / 1 * ((n : ℝ) + a)) : ℝ) * Complex.I) =
      Complex.exp (((2 * Real.pi * a) : ℝ) * Complex.I) := by
  have : (((2 * Real.pi / 1 * ((n : ℝ) + a)) : ℝ) : ℂ) * Complex.I =
      (((2 * Real.pi * a) : ℝ) : ℂ) * Complex.I + (n : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem qDisc_logChart_lit (n : ℤ) :
    qDisc (logChart (logHomeo two_pi_div_one_ne_zero
      ⟨(1 + litε n, n + litε n), by linarith [litε_pos n]⟩)) = litU n.natAbs := by
  rw [qDisc_logChart]
  show Complex.exp ((Real.log (1 + litε n) : ℂ) +
    ((2 * Real.pi / 1 * ((n : ℝ) + litε n) : ℝ) : ℂ) * Complex.I) = _
  rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log (by linarith [litε_pos n]),
    exp_period]
  rfl

theorem qDisc_image_logChart_litT : qDisc '' (logChart '' litT) = range litU := by
  rw [litT, ← range_comp, ← range_comp]
  ext z
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨n.natAbs, (qDisc_logChart_lit n).symm⟩
  · rintro ⟨m, rfl⟩
    refine ⟨(m : ℤ), ?_⟩
    have := qDisc_logChart_lit (m : ℤ)
    rw [Int.natAbs_natCast] at this
    exact this

theorem norm_litU (m : ℕ) : ‖litU m‖ = 1 + 1 / ((m : ℝ) + 2) := by
  rw [litU, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]

theorem tendsto_litU : Tendsto litU atTop (𝓝 1) := by
  have h0 : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 2)) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
    refine this.congr fun m => ?_
    simp only [comp_apply]; push_cast; ring_nf
  have hg : Continuous fun ε : ℝ => ((1 + ε : ℝ) : ℂ) *
      Complex.exp (((2 * Real.pi * ε : ℝ) : ℂ) * Complex.I) := by fun_prop
  have := (hg.tendsto 0).comp h0
  have e : ((1 + 0 : ℝ) : ℂ) * Complex.exp (((2 * Real.pi * 0 : ℝ) : ℂ) * Complex.I) = 1 := by
    simp
  rw [e] at this
  exact this

theorem litT_props : IsClosed litT ∧ litT.Countable ∧
    ∀ t ∈ litT, ∃ ρ > 0, Metric.ball t ρ ∩ litT = {t} := by
  have hfin := finite_ball_inter_range_of_im (f := fun n : ℤ =>
    logHomeo two_pi_div_one_ne_zero ⟨(1 + litε n, n + litε n), by linarith [litε_pos n]⟩)
    fun n => by
      rw [im_logHomeo]
      have h1 := litε_pos n
      have h2 := litε_lt_one n
      have hπ := Real.pi_pos
      constructor <;> simp only [div_one] <;> nlinarith
  obtain ⟨hc, hi⟩ := isClosed_isolated_of_finite_ball hfin
  exact ⟨hc, countable_range _, hi⟩

/-- **The printed (i) ⇒ (ii) of `prop:branched_covering_composition` is false** (DEC-27): there
are branched coverings `p : X → 𝔻_∞` and `q : 𝔻_∞ → 𝔻` with `q ∘ p` a branched covering while
`q(𝔻_∞ ∖ ord_p(𝔻_∞))` is **not** skeletal (it is not closed: its points `(1 + ε) e^{2πiε}`
accumulate at `1`, which it misses). -/
theorem not_isSkeletal_of_isBranchedCovering_comp :
    ∃ y₀ : ((branchSet litT)ᶜ : Set DInfty),
      IsBranchedCovering (SpreadEnd.base : MaxBranchedCover (branchSet litT) y₀ → DInfty) ∧
      IsBranchedCovering qDisc ∧
      IsBranchedCovering
        (qDisc ∘ (SpreadEnd.base : MaxBranchedCover (branchSet litT) y₀ → DInfty)) ∧
      ¬ IsSkeletal (qDisc ''
        branchingLocus (SpreadEnd.base : MaxBranchedCover (branchSet litT) y₀ → DInfty)) := by
  obtain ⟨hTc, hTcount, hTi⟩ := litT_props
  obtain ⟨y₀, hy₀⟩ := nonempty_compl_branchSet hTc hTcount
  refine ⟨⟨y₀, hy₀⟩, ?_⟩
  have hsk := isSkeletal_branchSet hTc hTcount
  have hsl := semilocallySimplyConnected_branchSet hTc
  obtain ⟨-, -, -, -, hl, -⟩ := maxBranched_basic hsk hsl ⟨y₀, hy₀⟩
  haveI := hl
  obtain ⟨hbc, hB1, hB2⟩ := exists_branched_over hTc hTcount hTi ⟨y₀, hy₀⟩
  set B := branchingLocus (SpreadEnd.base : MaxBranchedCover (branchSet litT) ⟨y₀, hy₀⟩ → DInfty)
  have hq := isBranchedCovering_qDisc.1
  -- `q(B)` lies between `range u` and `{0} ∪ range u`
  have hlow : range litU ⊆ qDisc '' B := by
    rw [← qDisc_image_logChart_litT]; exact image_mono hB1
  have hup : qDisc '' B ⊆ insert 0 (range litU) := by
    rw [← qDisc_image_logChart_litT]
    refine (image_mono hB2).trans ?_
    rintro _ ⟨x, hx, rfl⟩
    rcases hx with rfl | hx
    · left; exact DInfty.cplx_apex 1
    · right; exact ⟨x, hx, rfl⟩
  have hK : IsClosed (insert (0 : ℂ) (insert 1 (range litU))) :=
    by rw [insert_eq]; exact isClosed_singleton.union tendsto_litU.isCompact_insert_range.isClosed
  have hKc : (insert (0 : ℂ) (insert 1 (range litU))).Countable :=
    ((countable_range litU).insert 1).insert 0
  have hclK : closure (qDisc '' B) ⊆ insert (0 : ℂ) (insert 1 (range litU)) :=
    closure_minimal (hup.trans (insert_subset_insert (subset_insert _ _))) hK
  have hBsk : IsSkeletal (closure (qDisc '' B)) :=
    isSkeletal_of_countable_complex isClosed_closure (hKc.mono hclK)
  have hZ₁ : SemilocallySimplyConnected (compGoodSet
      (SpreadEnd.base : MaxBranchedCover (branchSet litT) ⟨y₀, hy₀⟩ → DInfty) qDisc) :=
    semilocallySimplyConnected_of_isOpen (isOpen_ordY.inter isClosed_closure.isOpen_compl)
  refine ⟨hbc, hq, isBranchedCovering_comp_of_semilocallySimplyConnected hbc hq hBsk hZ₁, ?_⟩
  intro hsk'
  have h1 : (1 : ℂ) ∈ closure (qDisc '' B) :=
    closure_mono hlow (mem_closure_of_tendsto tendsto_litU (Eventually.of_forall fun m => ⟨m, rfl⟩))
  rw [hsk'.isClosed.closure_eq] at h1
  rcases hup h1 with h | ⟨m, hm⟩
  · exact one_ne_zero h
  · have := norm_litU m
    rw [hm, norm_one] at this
    have : (0 : ℝ) < 1 / ((m : ℝ) + 2) := by positivity
    linarith

end Literal

/-! ### `rem:previous_examples_instances_developing`: the cylinder is the maximal branched covering -/

/-- A product of locally path-connected spaces is locally path-connected. -/
theorem locPathConnectedSpace_prod_of {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [LocPathConnectedSpace A] [LocPathConnectedSpace B] : LocPathConnectedSpace (A × B) := by
  refine locPathConnectedSpace_iff_pathComponentIn_mem_nhds.2 fun x u hu hxu => ?_
  obtain ⟨s, t, hs, ht, hxs, hxt, hst⟩ := isOpen_prod_iff.1 hu x.1 x.2 hxu
  refine mem_of_superset (prod_mem_nhds (pathComponentIn_mem_nhds (hs.mem_nhds hxs))
    (pathComponentIn_mem_nhds (ht.mem_nhds hxt))) ?_
  rintro ⟨a, b⟩ ⟨ha, hb⟩
  obtain ⟨γ₁, hγ₁⟩ := (ha : JoinedIn s x.1 a)
  obtain ⟨γ₂, hγ₂⟩ := (hb : JoinedIn t x.2 b)
  exact ⟨γ₁.prod γ₂, fun τ => hst ⟨hγ₁ τ, hγ₂ τ⟩⟩

/-- Precomposing a branched covering with a homeomorphism gives a branched covering. -/
theorem IsBranchedCovering.comp_homeomorph {A : Type*} [TopologicalSpace A]
    [LocallyConnectedSpace Y] {p : X → Y} (hp : IsBranchedCovering p) (h : A ≃ₜ X) : IsBranchedCovering (p ∘ h) := by
  haveI := hp.isSpread.locallyConnectedSpace
  haveI : LocallyConnectedSpace A := h.isOpenEmbedding.locallyConnectedSpace
  haveI := hp.connectedSpace_source
  haveI := hp.connectedSpace_target
  have hcomm : ∀ a, p (h a) = id ((p ∘ h) a) := fun _ => rfl
  have hcommX : ∀ x, (p ∘ h) (h.symm x) = (Homeomorph.refl Y) (p x) := fun x => by
    simp
  refine ⟨hp.isSpread.comp (IsSpread.of_isInducing h.isInducing), ?_,
    hp.surjective.comp h.surjective, h.symm.surjective.connectedSpace h.symm.continuous,
    inferInstance, ?_, ?_⟩
  · rw [isCompleteSpread_iff]
    intro e
    obtain ⟨x, hx⟩ := isCompleteSpread_iff.1 hp.isComplete
      (SpreadEnd.map continuous_id h.continuous hcomm e)
    refine ⟨h.symm x, fun U hU => ?_⟩
    obtain ⟨a, ha⟩ := e.nonempty hU
    have h1 := hx U hU
    rw [SpreadEnd.map_apply continuous_id h.continuous hcomm e hU hU (fun _ hy => hy) ha] at h1
    obtain ⟨a₀, ha₀, he⟩ := e.isCompOf U hU
    have hU' : e U = connectedComponentIn ((p ∘ h) ⁻¹' U) a := by
      rw [he] at ha ⊢
      exact connectedComponentIn_eq ha
    have himg := h.image_connectedComponentIn (s := (p ∘ h) ⁻¹' U) (x := a) (by
      rw [hU'] at ha; exact connectedComponentIn_subset _ _ ha)
    have hpre : h '' ((p ∘ h) ⁻¹' U) = p ⁻¹' U := by
      rw [h.image_eq_preimage_symm]; ext y; simp
    rw [hpre, ← hU'] at himg
    rw [← himg] at h1
    obtain ⟨a', ha', rfl⟩ := h1
    rw [h.symm_apply_apply]; exact ha'
  · rw [← image_ordX_of_homeomorph h.symm (Homeomorph.refl Y) hcommX, h.image_symm]
    exact hp.isPortly_ordX.preimage_of_isLocalHomeomorph h.isLocalHomeomorph
  · have hid : ⇑(Homeomorph.refl Y) = id := rfl
    rw [← image_ordY_of_homeomorph h.symm (Homeomorph.refl Y) hcommX, hid, image_id]
    exact hp.isPortly_ordY


section CylMax

open scoped Real

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {α : ℝ}


theorem cylBasic_preimage (hα : α ≠ 0) (ε : ℝ) (B : Set V) :
    orbitMk (GammaA α) ⁻¹' (cylHomeomorph hα V ⁻¹' (Metric.ball (0 : ℂ) ε ×ˢ B)) =
      {p : DInfty | p.r < ε} ×ˢ B := by
  ext x
  simp only [mem_preimage, cylHomeomorph_apply, mem_prod, mem_ball_zero_iff, DInfty.norm_cplx,
    mem_setOf_eq]

theorem cylBasic_isPreconnected (ε δ : ℝ) (z : V) (hε : 0 < ε) :
    IsPreconnected ({p : DInfty | p.r < ε} ×ˢ Metric.ball z δ) :=
  (DInfty.isConnected_r_lt hε).isPreconnected.prod (convex_ball z δ).isPreconnected

theorem cylBasic_mem (hα : α ≠ 0) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (z : V) :
    orbitMk (GammaA α) (DInfty.apex, z) ∈ cylHomeomorph hα V ⁻¹' (Metric.ball (0 : ℂ) ε ×ˢ Metric.ball z δ) := by
  rw [mem_preimage, cylHomeomorph_apply]
  exact ⟨by simpa using hε, Metric.mem_ball_self hδ⟩

theorem cylBasic_isCNbhd (hα : α ≠ 0) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (z : V) :
    IsCNbhd (orbitMk (GammaA α) (DInfty.apex, z))
      (cylHomeomorph hα V ⁻¹' (Metric.ball (0 : ℂ) ε ×ˢ Metric.ball z δ)) := by
  refine ⟨(Metric.isOpen_ball.prod Metric.isOpen_ball).preimage (cylHomeomorph hα V).continuous,
    ?_, cylBasic_mem hα hε hδ z⟩
  rw [← Homeomorph.image_symm]
  exact ((convex_ball (0 : ℂ) ε).prod (convex_ball z δ)).isPreconnected.image _
    (cylHomeomorph hα V).symm.continuous.continuousOn

/-- Small basic sets around a point of `π{r = 0}`. -/
theorem cylBasic_subset {z : V} {O : Set (DInfty × V)} (hO : O ∈ 𝓝 (DInfty.apex, z)) :
    ∃ ε > 0, ∃ δ > 0, {p : DInfty | p.r < ε} ×ˢ Metric.ball z δ ⊆ O := by
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 hO
  obtain ⟨ε, hε, hεu⟩ := DInfty.hasBasis_nhds_apex.mem_iff.1 hu
  obtain ⟨δ, hδ, hδv⟩ := Metric.mem_nhds_iff.1 hv
  exact ⟨ε, hε, δ, hδ, (prod_mono hεu hδv).trans huv⟩

/-- The instances `prop:universality` asks of the cylinder and of `M`. -/
theorem cyl_instances (hα : α ≠ 0) :
    T2Space (Orbits (GammaA α) (DInfty × V)) ∧
      LocPathConnectedSpace (Orbits (GammaA α) (DInfty × V)) ∧
      FirstCountableTopology (Orbits (GammaA α) (DInfty × V)) ∧
      ConnectedSpace (Orbits (GammaA α) (DInfty × V)) ∧ LocPathConnectedSpace (DInfty × V) ∧
      ConnectedSpace (DInfty × V) := by
  haveI : LocPathConnectedSpace (DInfty × V) := locPathConnectedSpace_prod_of
  refine ⟨(cylHomeomorph hα V).isEmbedding.t2Space, inferInstance,
    (cylHomeomorph hα V).isInducing.firstCountableTopology, ?_, inferInstance, inferInstance⟩
  exact (Quotient.mk''_surjective (s₁ := MulAction.orbitRel (GammaA α) (DInfty × V))).connectedSpace isQuotientMap_quotient_mk'.continuous

/-- `π{r = 0}`, the image of the axis, is the complement of `π{r > 0}`. -/
theorem compl_image_axis (α : ℝ) :
    ((orbitMk (GammaA α) : DInfty × V → Orbits (GammaA α) (DInfty × V)) '' {x : DInfty × V | x.1 = DInfty.apex})ᶜ = orbitMk (GammaA α) '' cylPos V := by
  ext y
  obtain ⟨x, rfl⟩ := Quotient.mk''_surjective (s₁ := MulAction.orbitRel (GammaA α) (DInfty × V)) y
  have h1 := preimage_image_cylPos (Z := V) α
  constructor
  · intro hy
    refine ⟨x, ?_, rfl⟩
    rcases x.1.pos_or_eq_apex with hx | hx
    · exact hx
    · exact absurd ⟨x, hx, rfl⟩ hy
  · rintro hy ⟨x', hx', hxx'⟩
    have : x ∈ orbitMk (GammaA α) ⁻¹' (orbitMk (GammaA α) '' cylPos V) := hy
    rw [h1] at this
    obtain ⟨k, rfl⟩ := exists_smul_eq_of_orbitMk_eq hxx'
    have h2 : (k • x').1 = DInfty.apex := by
      rw [DInfty.smul_prod_def]
      show (k • x'.1) = DInfty.apex
      rw [hx', DInfty.smul_def, DInfty.rot_apex]
    have h3 : 0 < (k • x').1.r := this
    rw [h2] at h3
    exact lt_irrefl _ h3

/-- **The cylinder `𝔻_∞ × V → M = Γ_α\(𝔻_∞ × V)` is a branched covering, possibly branched over
`π{r = 0}`** (`ex:quotient_base`, `RamcovGX.tex:660`; `V` a real normed space). -/
theorem isBranchedCovering_orbitMk_cyl (hα : α ≠ 0) :
    IsBranchedCovering (orbitMk (GammaA α) : DInfty × V → Orbits (GammaA α) (DInfty × V)) ∧
      IsPossiblyBranchedOver
        (orbitMk (GammaA α) : DInfty × V → Orbits (GammaA α) (DInfty × V))
        (orbitMk (GammaA α) '' {x : DInfty × V | x.1 = DInfty.apex}) := by
  obtain ⟨hT2, hLPC, hFC, -, hLPCX, hCX⟩ := cyl_instances (V := V) hα
  haveI := hT2; haveI := hLPC; haveI := hFC; haveI := hLPCX; haveI := hCX
  set q : DInfty × V → Orbits (GammaA α) (DInfty × V) := orbitMk (GammaA α) with hqdef
  set H := cylHomeomorph hα V
  have hc : Continuous q := isQuotientMap_quotient_mk'.continuous
  have ho : IsOpenMap q := isOpenMap_quotient_mk'_mul
  have hcovOn := isCoveringMapOn_orbitMk_cylPos (Z := V) hα
  have hsp : IsSpread q := by
    refine isSpread_iff_of_locallyConnectedSpace.2 ⟨hc, fun x O hO hxO => ?_⟩
    obtain ⟨p, z⟩ := x
    rcases p.pos_or_eq_apex with hp | rfl
    · exact exists_cc_subset_of_isEvenlyCovered ho (hcovOn _ ⟨(p, z), hp, rfl⟩) hO hxO
    · obtain ⟨ε, hε, δ, hδ, hsub⟩ := cylBasic_subset (hO.mem_nhds hxO)
      refine ⟨H ⁻¹' (Metric.ball (0 : ℂ) ε ×ˢ Metric.ball z δ),
        (Metric.isOpen_ball.prod Metric.isOpen_ball).preimage H.continuous,
        cylBasic_mem hα hε hδ z, ?_⟩
      rw [cylBasic_preimage]
      exact (connectedComponentIn_subset _ _).trans hsub
  have hH := DInfty.isPortly_pos V
  have hY : IsPortly (q '' cylPos V) := hH.image_of_isOpenMap hc ho
    (Quotient.mk''_surjective (s₁ := MulAction.orbitRel (GammaA α) (DInfty × V)))
  have hmaps : MapsTo q (cylPos V) (q '' cylPos V) := fun x hx => ⟨x, hx, rfl⟩
  have hres : hmaps.restrict q _ _ =
      (q '' cylPos V).restrictPreimage q ∘
        Homeomorph.setCongr (preimage_image_cylPos (Z := V) α).symm :=
    funext fun _ => rfl
  have hcov : IsCoveringMap (hmaps.restrict q _ _) := hres ▸
    hcovOn.isCoveringMap_restrictPreimage.comp_homeomorph _
  have hsurj : Surjective (hmaps.restrict q _ _) := by
    rintro ⟨_, ⟨x, hx, rfl⟩⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨hY₁, -, -⟩ := spread_partial_covering hc hH hY.isOpen hmaps hcov hsurj
  have hcomp : IsCompleteSpread q := by
    rw [isCompleteSpread_iff]
    intro e
    by_cases he : e.base ∈ q '' cylPos V
    · obtain ⟨U, hU, heU, -, hcov⟩ := hY₁ he
      exact e.exists_mem_of_isEvenlyCoveredSet hU heU hcov
    · obtain ⟨⟨p, z⟩, hpz⟩ := Quotient.mk''_surjective
        (s₁ := MulAction.orbitRel (GammaA α) (DInfty × V)) e.base
      have hp : p = DInfty.apex := by
        rcases p.pos_or_eq_apex with hp | hp
        · exact absurd ⟨(p, z), hp, hpz⟩ he
        · exact hp
      subst hp
      refine ⟨(DInfty.apex, z), fun U hU => ?_⟩
      have hU' : (q ⁻¹' U) ∈ 𝓝 (DInfty.apex, z) :=
        (hU.isOpen.preimage hc).mem_nhds (by show q _ ∈ U; rw [← hpz] at hU; exact hU.mem)
      obtain ⟨ε, hε, δ, hδ, hsub⟩ := cylBasic_subset hU'
      set Vb := H ⁻¹' (Metric.ball (0 : ℂ) ε ×ˢ Metric.ball z δ)
      have hV : IsCNbhd e.base Vb := by
        have := cylBasic_isCNbhd hα hε hδ z
        rw [← hpz]; exact this
      have hVU : Vb ⊆ U := by
        intro y hy
        obtain ⟨x, rfl⟩ := Quotient.mk''_surjective
          (s₁ := MulAction.orbitRel (GammaA α) (DInfty × V)) y
        have hx : x ∈ q ⁻¹' Vb := hy
        rw [cylBasic_preimage] at hx
        exact hsub hx
      obtain ⟨x, hx, hxe⟩ := e.isCompOf _ hV
      have hpre : IsPreconnected (q ⁻¹' Vb) := by
        rw [cylBasic_preimage]; exact cylBasic_isPreconnected ε δ z hε
      have heV : e Vb = q ⁻¹' Vb := by
        rw [hxe, hpre.connectedComponentIn hx]
      refine e.mono _ U hV hU hVU ?_
      rw [heV, cylBasic_preimage]
      exact ⟨by simpa using hε, Metric.mem_ball_self hδ⟩
  have hbc := ((complete_path_carac.{0} hsp hH hY hmaps hcov hsurj).out 1 0).1 hcomp
  refine ⟨hbc, fun y hy => ?_⟩
  rw [← compl_compl (q '' _), compl_image_axis α]
  exact fun h => hy (hY₁ h)

/-- `previous_examples_universalCover`, for any set equal to `π{r > 0}`. -/
theorem previous_examples_universalCover_of_eq (hα : α ≠ 0)
    {O : Set (Orbits (GammaA α) (DInfty × V))} (hO : O = orbitMk (GammaA α) '' cylPos V) :
    SemilocallySimplyConnected O ∧
    ∀ (y₀ : O) (e₀ : orbitMk (GammaA α) ⁻¹' O), O.restrictPreimage (orbitMk (GammaA α)) e₀ = y₀ →
      ∃ Φ : UniversalCover O y₀ ≃ₜ orbitMk (GammaA α) ⁻¹' O,
        O.restrictPreimage (orbitMk (GammaA α)) ∘ Φ = UniversalCover.proj _ y₀ := by
  subst hO
  obtain ⟨-, -, hY, h⟩ := previous_examples_universalCover (Z := V) hα
  refine ⟨hY, fun y₀ e₀ he => ?_⟩
  obtain ⟨Φ, -, hΦ⟩ := h y₀ e₀ he
  exact ⟨Φ, hΦ⟩

/-- **The cylinder is the maximal covering of `M` possibly branched over `π{r = 0}`**
(`rem:previous_examples_instances_developing`, `RamcovGX.tex:684`, with `prop:universality`):
`π{r = 0}` is skeletal, its complement is semilocally simply connected, `𝔻_∞ × V → M` is a
covering possibly branched over `π{r = 0}`, maximal among such (`IsMaximalPossiblyBranched`), and
isomorphic over `M` to `\widetilde M^{π{r=0}}` (`MaxBranchedCover`) for every base point. -/
theorem previous_examples_maxBranched (hα : α ≠ 0) :
    IsSkeletal (orbitMk (GammaA α) '' {x : DInfty × V | x.1 = DInfty.apex}) ∧
    SemilocallySimplyConnected
      ((orbitMk (GammaA α) '' {x : DInfty × V | x.1 = DInfty.apex})ᶜ :
        Set (Orbits (GammaA α) (DInfty × V))) ∧
    IsMaximalPossiblyBranched.{w}
      (orbitMk (GammaA α) : DInfty × V → Orbits (GammaA α) (DInfty × V))
      (orbitMk (GammaA α) '' {x : DInfty × V | x.1 = DInfty.apex}) ∧
    ∀ y₀ : ((orbitMk (GammaA α) '' {x : DInfty × V | x.1 = DInfty.apex})ᶜ :
        Set (Orbits (GammaA α) (DInfty × V))),
      ∃ Φ : MaxBranchedCover (orbitMk (GammaA α) '' {x : DInfty × V | x.1 = DInfty.apex}) y₀ ≃ₜ
          DInfty × V, ∀ e, orbitMk (GammaA α) (Φ e) = e.base := by
  obtain ⟨hT2, hLPC, hFC, hCM, hLPCX, hCX⟩ := cyl_instances (V := V) hα
  haveI := hT2; haveI := hLPC; haveI := hFC; haveI := hCM; haveI := hLPCX; haveI := hCX
  set S := (orbitMk (GammaA α) : DInfty × V → Orbits (GammaA α) (DInfty × V)) ''
    {x : DInfty × V | x.1 = DInfty.apex} with hSdef
  set q : DInfty × V → Orbits (GammaA α) (DInfty × V) := orbitMk (GammaA α) with hqdef
  have hSc' : Sᶜ = q '' cylPos V := compl_image_axis α
  have hc : Continuous q := isQuotientMap_quotient_mk'.continuous
  have hO : IsPortly (Sᶜ : Set (Orbits (GammaA α) (DInfty × V))) := by
    rw [hSc']
    exact (DInfty.isPortly_pos V).image_of_isOpenMap hc isOpenMap_quotient_mk'_mul
      (Quotient.mk''_surjective (s₁ := MulAction.orbitRel (GammaA α) (DInfty × V)))
  have hS : IsSkeletal S := isSkeletal_iff.2 hO
  obtain ⟨hSc, hU⟩ := previous_examples_universalCover_of_eq (V := V) hα hSc'
  obtain ⟨hbc, hpb⟩ := isBranchedCovering_orbitMk_cyl (V := V) hα
  have hiso : ∀ y₀ : (Sᶜ : Set (Orbits (GammaA α) (DInfty × V))),
      ∃ Φ : MaxBranchedCover S y₀ ≃ₜ DInfty × V, ∀ e, q (Φ e) = e.base := by
    intro y₀
    obtain ⟨x₀, hx₀⟩ := Quotient.mk''_surjective
      (s₁ := MulAction.orbitRel (GammaA α) (DInfty × V)) (y₀ : Orbits (GammaA α) (DInfty × V))
    have hx₀q : q x₀ = y₀ := hx₀
    have hx₀' : x₀ ∈ q ⁻¹' Sᶜ := by show q x₀ ∈ Sᶜ; rw [hx₀q]; exact y₀.2
    obtain ⟨Φu, hΦu⟩ := hU y₀ ⟨x₀, hx₀'⟩ (Subtype.ext hx₀q)
    have h₁ := hbc.isSpreadCompletion_preimage hO
    have h₂ := (maxBranched_basic hS hSc y₀).1
    have hcomm : ∀ a, univCoverProj S y₀ (Φu.symm a) = id ((q ∘ ((↑) : q ⁻¹' Sᶜ → _)) a) :=
      fun a => by
        have := congrFun hΦu (Φu.symm a)
        simp only [comp_apply, Homeomorph.apply_symm_apply] at this
        show ((UniversalCover.proj (Sᶜ : Set (Orbits (GammaA α) (DInfty × V))) y₀ (Φu.symm a) : Orbits (GammaA α) (DInfty × V))) = q a
        rw [← this]; rfl
    obtain ⟨Ψ, ⟨hΨc, hΨp, -⟩, -⟩ := h₁.toIsFoxCompletion.existsUnique_extend
      h₂.toIsFoxCompletion continuous_id Φu.symm.continuous hcomm
    exact maxBranched_unique hS hSc y₀ hbc hpb hΨc hΨp
  refine ⟨hS, hSc, ⟨hbc, hpb, fun X' _ _ _ _ p' hp' hp'S => ?_⟩, hiso⟩
  obtain ⟨Φ, hΦ⟩ := hiso ⟨_, (nonempty_compl_of_isSkeletal hS).some_mem⟩
  obtain ⟨Φ', hΦ'c, hΦ'p, hΦ'bc, -⟩ := maxBranched_universal hS hSc _ hp' hp'S
  haveI : LocallyConnectedSpace X' := hp'.isSpread.locallyConnectedSpace
  refine ⟨Φ' ∘ Φ.symm, hΦ'c.comp Φ.symm.continuous, fun x => ?_, hΦ'bc.comp_homeomorph Φ.symm⟩
  rw [comp_apply, hΦ'p, ← hΦ, Φ.apply_symm_apply]

/-- On the cylinder, `{r = 0}` is the axis `{x.1 = apex}`. -/
theorem setOf_r_eq_zero_cyl :
    {x : DInfty × V | x.1.r = 0} = {x : DInfty × V | x.1 = DInfty.apex} := by
  ext x
  refine ⟨fun h => (x.1.pos_or_eq_apex).resolve_left fun h' => by
    rw [mem_setOf_eq] at h; rw [h] at h'; exact lt_irrefl _ h', fun h => ?_⟩
  rw [mem_setOf_eq] at h ⊢
  rw [h]; rfl

/-- **The branching locus of `𝔻_∞ × V → M` is exactly `π{r = 0}`** (`ex:quotient_base`,
`rem:previous_examples_instances_developing` under DEC-52, "branched over `π{r=0}`"): no point of
`π{r = 0}` is ordinary, since every connected neighbourhood of `(apex, z)` contains a point and
its `Γ_α`-translate. -/
theorem branchingLocus_orbitMk_cyl (hα : α ≠ 0) :
    branchingLocus (orbitMk (GammaA α) : DInfty × V → Orbits (GammaA α) (DInfty × V)) =
      orbitMk (GammaA α) '' {x : DInfty × V | x.1 = DInfty.apex} := by
  refine Subset.antisymm (isBranchedCovering_orbitMk_cyl (V := V) hα).2 ?_
  set q : DInfty × V → Orbits (GammaA α) (DInfty × V) := orbitMk (GammaA α) with hqdef
  have hc : Continuous q := isQuotientMap_quotient_mk'.continuous
  rintro _ ⟨⟨p, z⟩, hp, rfl⟩ hy
  rw [mem_setOf_eq] at hp
  subst hp
  obtain ⟨U, hU, hyU, -, hev⟩ := hy
  obtain ⟨e, he⟩ := hev (DInfty.apex, z) hyU
  obtain ⟨ε, hε, δ, hδ, hsub⟩ := cylBasic_subset ((hU.preimage hc).mem_nhds hyU)
  have hB : {p : DInfty | p.r < ε} ×ˢ Metric.ball z δ ⊆
      connectedComponentIn (q ⁻¹' U) (DInfty.apex, z) :=
    (cylBasic_isPreconnected ε δ z hε).subset_connectedComponentIn
      ⟨by simpa using hε, Metric.mem_ball_self hδ⟩ hsub
  set a : DInfty × V := (⟨ε / 2, 0, Or.inl (half_pos hε)⟩, z) with ha
  set k : GammaA α := GammaA.ofInt 1
  have haB : a ∈ {p : DInfty | p.r < ε} ×ˢ Metric.ball z δ :=
    ⟨show ε / 2 < ε from half_lt_self hε, Metric.mem_ball_self hδ⟩
  have hkaB : k • a ∈ {p : DInfty | p.r < ε} ×ˢ Metric.ball z δ := by
    refine ⟨?_, Metric.mem_ball_self hδ⟩
    show (k • a.1).r < ε
    rw [DInfty.smul_def, DInfty.rot_r]
    exact half_lt_self hε
  have hq : ((e ⟨a, hB haB⟩ : Orbits (GammaA α) (DInfty × V))) = e ⟨k • a, hB hkaB⟩ := by
    rw [he, he]; exact (orbitMk_smul k a).symm
  have hka : k • a = a := by
    have := e.injective (Subtype.ext hq)
    exact (congrArg Subtype.val this).symm
  have h1 := DInfty.free_pos (Z := V) hα a (show 0 < a.1.r from half_pos hε) k hka
  have h2 : k.toInt = (1 : GammaA α).toInt := congrArg GammaA.toInt h1
  simp [k] at h2

/-- **The cylinder is the Fox completion of the universal covering of `π{r > 0}`**
(`rem:previous_examples_instances_developing`, `RamcovGX.tex:684`; `prop:universality`,
`RamcovGX.tex:1170`): for every base point `y₀ ∈ π{r > 0}`, `𝔻_∞ × V → M` is a completion
(`IsSpreadCompletion`) of `\widetilde{π{r>0}} → M`, the universal covering of `π{r > 0}` followed
by the inclusion. -/
theorem previous_examples_foxCompletion (hα : α ≠ 0)
    {S : Set (Orbits (GammaA α) (DInfty × V))}
    (hSdef : S = orbitMk (GammaA α) '' {x : DInfty × V | x.1 = DInfty.apex}) (y₀ : (Sᶜ : Set _)) :
    ∃ ι : UniversalCover (Sᶜ : Set (Orbits (GammaA α) (DInfty × V))) y₀ → DInfty × V,
      IsSpreadCompletion (univCoverProj S y₀) (orbitMk (GammaA α)) ι := by
  obtain ⟨hT2, hLPC, hFC, hCM, hLPCX, hCX⟩ := cyl_instances (V := V) hα
  haveI := hT2; haveI := hLPC; haveI := hFC; haveI := hCM; haveI := hLPCX; haveI := hCX
  have hSc' : Sᶜ = orbitMk (GammaA α) '' cylPos V := hSdef ▸ compl_image_axis α
  have hc : Continuous (orbitMk (GammaA α) : DInfty × V → Orbits (GammaA α) (DInfty × V)) :=
    isQuotientMap_quotient_mk'.continuous
  have hO : IsPortly (Sᶜ : Set (Orbits (GammaA α) (DInfty × V))) := by
    rw [hSc']
    exact (DInfty.isPortly_pos V).image_of_isOpenMap hc isOpenMap_quotient_mk'_mul
      (Quotient.mk''_surjective (s₁ := MulAction.orbitRel (GammaA α) (DInfty × V)))
  obtain ⟨-, hU⟩ := previous_examples_universalCover_of_eq (V := V) hα hSc'
  obtain ⟨hbc, -⟩ := isBranchedCovering_orbitMk_cyl (V := V) hα
  obtain ⟨x₀, hx₀⟩ := Quotient.mk''_surjective
    (s₁ := MulAction.orbitRel (GammaA α) (DInfty × V)) (y₀ : Orbits (GammaA α) (DInfty × V))
  have hx₀q : orbitMk (GammaA α) x₀ = y₀ := hx₀
  have hx₀' : x₀ ∈ orbitMk (GammaA α) ⁻¹' Sᶜ := by
    show orbitMk (GammaA α) x₀ ∈ Sᶜ; rw [hx₀q]; exact y₀.2
  obtain ⟨Φu, hΦu⟩ := hU y₀ ⟨x₀, hx₀'⟩ (Subtype.ext hx₀q)
  have h₁ := hbc.isSpreadCompletion_preimage hO
  refine ⟨((↑) : orbitMk (GammaA α) ⁻¹' Sᶜ → DInfty × V) ∘ Φu, h₁.isSpread,
    fun c => by have := congrArg Subtype.val (congrFun hΦu c); exact this,
    IsEmbedding.subtypeVal.comp Φu.isEmbedding, h₁.isComplete, ?_⟩
  rw [range_comp, Φu.range_coe, image_univ]
  exact h₁.isPortly

/-- **`rem:previous_examples_instances_developing`, certified in the corrected form ruled by
DEC-52** (`RamcovGX.tex:684`, with `ex:quotient_base` l.660–669 and `prop:universality`
l.1158): for the cylinder `𝔻_∞ × V` (`V` a real normed space, `ℝ^{n-2}`) with the a.e.
`(G,X)`-structure pulled back by a local homeomorphism `D : {r > 0} → X` and `Γ_α` (`α ≠ 0`)
acting by a.e. `(G,X)`-morphisms,
* `M = Γ_α\(𝔻_∞ × V)` is a singular `(G,X)`-manifold (its unique maximal a.e. structure making
  `π` an a.e. morphism) whose singular locus lies in `π{r = 0}` (DEC-52: `sing(M) ⊆ π{r=0}`);
* `D` is a developing map: it induces a `(G,X)`-morphism on `{r > 0}`;
* `π{r = 0}` is skeletal, `π{r > 0}` semilocally simply connected, and `𝔻_∞ × V → M` is branched
  over `π{r = 0}` — its branching locus is exactly `π{r = 0}` (DEC-52: "branched over
  `π{r=0} ⊇ sing(M)`");
* it is **the** maximal covering of `M` possibly branched over `π{r = 0}`
  (`IsMaximalPossiblyBranched`), and for every base point it is the Fox completion of the universal
  covering of `π{r > 0}` and is isomorphic over `M` to `\widetilde M^{π{r=0}}`. -/
theorem previous_examples_instances_developing_ruled {G Xm : Type*} [TopologicalSpace Xm]
    [Group G] [MulAction G Xm] [ContinuousConstSMul G Xm] [LocallyConnectedSpace Xm] [T2Space Xm]
    [IsRigidAction G Xm] (hα : α ≠ 0) {D : DInfty × V → Xm} (hD : IsLocalHomeomorphOn D (cylPos V))
    (hΓ : ∀ k : GammaA α, IsAEMorphismOf G (maximalAEAtlas G (devAtlas G D (cylPos V)))
      (maximalAEAtlas G (devAtlas G D (cylPos V))) fun x => k • x) :
    (∃! B : Set (OpenPartialHomeomorph (Orbits (GammaA α) (DInfty × V)) Xm),
      IsMaximalAEAtlas G B ∧
      IsAEMorphismOf G (maximalAEAtlas G (devAtlas G D (cylPos V))) B (orbitMk (GammaA α)) ∧
      (support B)ᶜ ⊆ orbitMk (GammaA α) '' {x : DInfty × V | x.1 = DInfty.apex}) ∧
    IsRegularOn G (maximalAEAtlas G (devAtlas G D (cylPos V)))
      ((gxGroupoid G Xm).maximalAtlas Xm) D (cylPos V) ∧
    IsSkeletal (orbitMk (GammaA α) '' {x : DInfty × V | x.1 = DInfty.apex}) ∧
    SemilocallySimplyConnected
      ((orbitMk (GammaA α) '' {x : DInfty × V | x.1 = DInfty.apex})ᶜ :
        Set (Orbits (GammaA α) (DInfty × V))) ∧
    branchingLocus (orbitMk (GammaA α) : DInfty × V → Orbits (GammaA α) (DInfty × V)) =
      orbitMk (GammaA α) '' {x : DInfty × V | x.1 = DInfty.apex} ∧
    IsMaximalPossiblyBranched.{w}
      (orbitMk (GammaA α) : DInfty × V → Orbits (GammaA α) (DInfty × V))
      (orbitMk (GammaA α) '' {x : DInfty × V | x.1 = DInfty.apex}) ∧
    ∀ y₀ : ((orbitMk (GammaA α) '' {x : DInfty × V | x.1 = DInfty.apex})ᶜ :
        Set (Orbits (GammaA α) (DInfty × V))),
      (∃ ι : UniversalCover ((orbitMk (GammaA α) '' {x : DInfty × V | x.1 = DInfty.apex})ᶜ :
          Set (Orbits (GammaA α) (DInfty × V))) y₀ → DInfty × V,
        IsSpreadCompletion
          (univCoverProj (orbitMk (GammaA α) '' {x : DInfty × V | x.1 = DInfty.apex}) y₀)
          (orbitMk (GammaA α)) ι) ∧
      ∃ Φ : MaxBranchedCover (orbitMk (GammaA α) '' {x : DInfty × V | x.1 = DInfty.apex}) y₀ ≃ₜ
          DInfty × V, ∀ e, orbitMk (GammaA α) (Φ e) = e.base := by
  obtain ⟨hq, -⟩ := quotientBase_ruled (G := G) hα hD hΓ
  rw [setOf_r_eq_zero_cyl] at hq
  obtain ⟨hS, hSc, hmax, hiso⟩ := previous_examples_maxBranched.{w} (V := V) hα
  exact ⟨hq, (previous_examples_developing (G := G) hα hD).2, hS, hSc,
    branchingLocus_orbitMk_cyl hα, hmax, fun y₀ => ⟨previous_examples_foxCompletion hα rfl y₀,
      hiso y₀⟩⟩

end CylMax

end GX
