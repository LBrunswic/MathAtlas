import GX.SingularII.Tame
import GX.Topology.PortlyExamples

/-!
# Singular `(G,X)`-manifolds (II): analytic families of models, virtually tame models

Package WP-27j, piece (2) of `theo:local_virt_tame` by WP-35f (liftable charts; descending charts, `ℓ`
arbitrary, in fix round 1); WP-40c: `rem:theorem_theo_local_tame` certified under DEC-80 (b), and
the general case of `theo:local_virt_tame` pushed (DEC-82) — the necessary condition every
tamifying topology satisfies, and finite local degree forcing naturality. `papers/gx`, `RamcovGX.tex:1889–1983`, §2.5.3 "Analytic family" and §2.5.4
"Virtually tame models" (`(G,X)` analytical, `X` locally unloopable, l.1660; manifolds connected,
l.1712), on WP-27i's `GX.SingularII.Tame`.

* **`def:singular_manifold_automorphisms_group`** — `RamcovGX.tex:1895`: `GX.singularAut`.
* **`def:family_singular_manifolds_endowed`** — `RamcovGX.tex:1899`: `GX.IsAnalyticModelFamily`,
  the printed clause `GX.isAnalyticModelFamily_iff`.
* **`def:atlas`** — `RamcovGX.tex:1905`: `GX.XAChart`, `GX.HasXAType`, `GX.IsXAAtlas`.
* **`def:analytic_family_model_spaces`** — `RamcovGX.tex:1913`, read as ruled (DEC-67 (e): a chart
  centred at every singular point): `GX.IsXAManifold`; the printed form `GX.IsXAManifoldPrinted`,
  `GX.isXAManifoldPrinted_iff`, `GX.isXAManifold_model`.
* **`rem:singular_point_manifold_has`** — `RamcovGX.tex:1921`, under DEC-67 (e):
  `GX.existsUnique_hasXAType` (uniqueness `GX.hasType_unique`, the remark's own argument).
* **`rem:theorem_theo_local_tame`** — `RamcovGX.tex:1924`, read as ruled (DEC-80 (b): the GLOBAL
  equivalence "every `X_A`-manifold is tame iff every model is tame", SCOPE (b)):
  `GX.forall_isTame_iff_printed` (`X_A`-manifolds as printed, l.1913: no further hypothesis), and
  for `X_A`-manifolds as ruled by DEC-67 (e) `GX.forall_isTame_iff` (models `X_A`-manifolds, the
  paper's own presumption l.2086); the direction "models tame ⇒ tame" per manifold:
  `GX.isTame_of_isXAAtlas`, `GX.isTame_of_isXAManifold`, `GX.isTame_of_isXAManifoldPrinted`.
* `cex:start_singular_manifold_homeomorphic` — `RamcovGX.tex:1930` — partial (SCOPE (c), DEC-69):
  Troyanov's theorem with the suspension named, `GX.TroyanovSuspensionTheorem` (on
  `GX.TroyanovAngleCondition`, `GX.SuspensionCexFacts`); the cex from it,
  `GX.cex_start_singular_manifold_homeomorphic`; the inference
  `GX.SuspensionCexFacts.isAnalyticModelFamily_unit_iff`
  (`GX.isAnalyticModelFamily_unit_iff_eq_singleton`,
  `GX.IsAnalyticModelFamily.inter_eq_empty_of_not_extend`); non-vacuity witnesses
  `GX.troyanovAngleCondition_witness`, `GX.exists_suspensionCexFacts` (the Joukowski structure on
  `ℂ`, `sing = {0, ±1}`, every field exercised); the named `Prop` is not tied to `θ`
  (`GX.troyanovSuspensionTheorem_of_subsingleton`); the concrete `M` not built.
* **`def:singular_manifold_virtually_tame`** — `RamcovGX.tex:1960`: `GX.IsTamifyingTopology`,
  `GX.IsVirtuallyTame`; `GX.isTamifyingTopology_natural_iff`, `GX.IsTame.isVirtuallyTame`.
* **`def:singular_manifold_locally_galoisian`** — `RamcovGX.tex:1969`: `GX.IsLocallyGaloisian`.
* `theo:local_virt_tame` — `RamcovGX.tex:1974` — partial (SCOPE (d)), `X_A`-manifolds as ruled
  (DEC-67 (e)). PROVED, 0 `sorry`, under all the theorem's hypotheses, when the singular points
  are centres of charts DESCENDING from the maximal coverings of the models (the case of the proof
  where `T_{U,V,φ}` is the `ℓ`-quotient of `T_α` itself — e.g. `r : Ṽ → V̂` an isomorphism,
  `ℓ : Ũ → Û` arbitrary): `GX.isVirtuallyTame_of_descending`, `GX.local_virt_tame_descending` —
  piece (2) built as the quotient of `T_α` by a descent `V̂ → Û` (`GX.IsChartDescent`,
  `GX.descTop`, `GX.isLocalTamifying_descTop`, naturality `GX.nhds_descTop_le_of_aut`, the
  Galoisianity of the descents `GX.IsChartDescent.exists_deck` from the models' local
  Galoisianity), the gluing (piece (3)) `GX.exists_isTamifyingTopology_of_local`; the condition
  `GX.IsDescendingChartMap` holds for liftable charts (`GX.IsLiftableChartMap.isDescendingChartMap`)
  and is satisfiable at singular points (`GX.isLiftableChartMap_refl`,
  `GX.isLiftableChartMap_modelChartSelf`). The earlier special case `ℓ`, `r` both isomorphisms is
  kept, without local Galoisianity: `GX.isVirtuallyTame_of_liftable`,
  `GX.local_virt_tame_liftable` (`GX.chartTop`, `GX.isLocalTamifying_chartTop`,
  `GX.nhds_chartTop_le_of_aut`). In general stated: `GX.local_virt_tame`,
  `GX.isVirtuallyTame_of_isXAManifold`, on `GX.exists_isLocalTamifying_charts` (tagged `sorry`, a
  mathematical obstruction confined to the non-descending charts, where `r` is not an
  isomorphism: the paper's (D) rests on `lem:spread_top` (c) for `r`, false in general). Proved
  for tame models: `GX.isVirtuallyTame_of_isXAManifold_of_isTame`. WP-40c (DEC-82), for ANY
  tamifying topology, not only the paper's `T_{U,V,φ}`: a deck transformation fixing a point `s` of
  `\widetilde M` is carried by the `D`-small regular part of every neighbourhood of `s`
  (`GX.IsTamifyingTopology.exists_joinedIn_reg_of_fixed`,
  `GX.IsTamifyingTopology.exists_joinedIn_devSmall`), so where it is not, `M` is not virtually
  tame (`GX.not_isTamifyingTopology_of_forall_not_joinedIn`,
  `GX.not_isVirtuallyTame_of_forall_not_joinedIn`); at a point of finite local degree a tamifying
  topology is natural (`GX.IsTamifyingTopology.nhds_eq_of_finite_stab`,
  `GX.IsTamifyingTopology.nhds_eq_of_free`). Neither a proof nor a counterexample of the general
  statement (SCOPE (d), last paragraph).
* **`def:topological_spaces_continuous_map`** — `RamcovGX.tex:1984` (outside the dispatch, needed by
  the proof): `GX.strongPullTop`; `GX.continuous_strongPullTop`, `GX.strongPullTop_self`.
* `lem:spread_top` — `RamcovGX.tex:1990` — certified by WP-27k (`GXScaffold.SingularII.SpreadTop`:
  false as printed, `GX.not_spreadTopPrinted`; corrected, `GX.spread_top_corrected`); here only
  (d), under the Galoisian hypothesis its proof uses, `GX.spread_top_deck` (SCOPE (e)). The false
  statement `GX.spread_top` this module carried is removed (WP-35f).

> The automorphisms group of $M$ denoted $\Aut(M)$ is the group of isomorphisms of singular
> $(G,X)$-manifolds from $M$ to itself. (l.1895)
>
> A family $(X_\alpha)_{\alpha \in A}$ of singular $(G,X)$-manifolds each endowed with a non-empty
> subset $S_\alpha\subset \sing(X_\alpha)$ is an analytic family of model spaces if for all
> $\alpha_1,\alpha_2\in A$ and all a.e. $(G,X)$-isomorphism $\U_1\xrightarrow{\varphi} \U_2$
> where $\U_1,\U_2$ are connected open subsets of $X_{\alpha_1}$ and $X_{\alpha_2}$ respectively
> we have: $\U_1\cap S_{\alpha_1}\neq \emptyset \Rightarrow \alpha_1=\alpha_2$ and
> $\exists \phi \in \mathrm{Aut}(X_{\alpha_1}), \varphi=\phi_{|\U_1}^{|\U_2}$. (l.1899)
>
> For $\alpha\in A$, an $X_\alpha$-chart around $x\in \sing(M)$ is a triplet $(\U,\V,\phi)$ with
> $x\in \U\subset M,\phi(x)\in S_\alpha, \V\subset X_\alpha$ open and connected; and
> $\U\xrightarrow{\phi} \V$ an isomorphism. If such a chart exists, we say that $x$ has type
> $\alpha$. An $X_A$-chart is an $X_\alpha$-chart for some $\alpha\in A$. An $X_A$-atlas is a
> collection of $X_A$-charts covering $M$. (l.1905) A $X_A$-manifold is a singular
> $(G,X)$-manifold $M$ admitting a $X_A$-atlas. (l.1913)
>
> A singular point $x\in \sing(M)$ of a $X_A$-manifold $M$ has exactly one type. (l.1921)
> By Theorem \ref{theo:local_tame}, a $X_A$-manifold is tame if and only if all models are tame.
> (l.1924)
>
> A singular $(G,X)$-manifold $M$ is virtually tame if there exists a first countable locally path
> connected (strong) topology $\T$ on $\widetilde M$ thinner than the natural (weak) topology such
> that: (A) The quotient topology induced by $\T$ on $M$ is the natural one; (B) the developing map
> $\D:\reg(\widetilde M)\rightarrow X$ admits a $\T$-continuous extension; (C) elements
> $\Gamma(\widetilde M/M)$ are $\T$-continuous; (D) the lift of $\reg(M)$ to $\widetilde M$ is
> $\T$-portly in $\widetilde M$. We call such a $\T$ a tamifying topology. (l.1960)
>
> A singular $(G,X)$-manifold $M$ is locally Galoisian if for every $\U\subset \M$ open,
> $\reg(\U)$ is semi-locally simply connected in $\U$. (l.1969)
>
> Let $(X_\alpha)_{\alpha\in A}$ be an analytical family of locally Galoisian model spaces. If for
> every $\alpha\in A$, there exists a tamifying topology $\T_\alpha$ such that the group
> $\Aut(\widetilde X_\alpha)$ acts $\T_\alpha$-continuously, then the following are equivalent:
> (i) every $X_A$-manifold is virtually tame (ii) for every $\alpha \in A$, $X_\alpha$ is
> virtually tame. (l.1974)

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `(G,X)` analytical (l.341, DEC-39) | ✓ carried: `IsRigidAction`, `ContinuousConstSMul`, `X` T2 and locally connected; `FaithfulSMul` where the tameness API of WP-27h/i uses it; `X` connected never used |
| `X` locally unloopable (standing, l.1660) | ✓ carried (`hX`) wherever `\widetilde M` is used; ⚠ weakened to the semilocal simple connectedness of `reg M` in `isTamifyingTopology_natural_iff`, `exists_lift_singularAut`, `IsTamifyingTopology.exists_isOpen_subset` |
| manifolds connected (l.1712) | ✓ carried where tameness is used; models connected (`[∀ a, ConnectedSpace (Xα a)]`) in `rem:theorem_theo_local_tame`, `theo:local_virt_tame` |
| singular manifolds Hausdorff, locally path-connected, first countable (DEC-66 (a), §3's standing l.810), connected where `\widetilde M` is used (DEC-66 (b), (c)) | ✓ carried where `\widetilde M` is used; ⚠ weakened to locally connected in the definitions |
| `def:atlas`: `x ∈ sing(M)` | ⚠ weakened: not a field — it follows (`XAChart.mem_sing`) |
| `def:singular_manifold_virtually_tame` (B): "the developing map" | ✓ read: any map inducing a `(G,X)`-morphism on `p⁻¹(reg M)` (unique up to `G`, `aeMorphism_model_unique`) |
| `theo:local_virt_tame`: models locally Galoisian, analytic family | ✓ carried (`hgal`, `hfam`); local Galoisianity used, as the paper does (l.2093), by the descending form (`isVirtuallyTame_of_descending`: the descents `V̂ → Û` are Galoisian, `IsChartDescent.exists_deck`, through the discrete fibres of `\widetilde X_α → X_α`, `discreteTopology_fiber_of_isLocallyGaloisian`); not used by the liftable special case |
| `theo:local_virt_tame`: `Aut(\widetilde X_α)` acts `T_α`-continuously | ✓ carried (`HasAutContinuousTamifying`: every a.e. isomorphism of `\widetilde X_α`, structure `p^*B`) |
| `cex:start_singular_manifold_homeomorphic`: `Σ` generic, Troyanov, the suspension | ⚠ named external (DEC-69): `TroyanovSuspensionTheorem` — Troyanov's angle condition (`TroyanovAngleCondition`), "generic" read as "all `θ_i` different" (l.1935), and the facts the cex derives (`SuspensionCexFacts`: `M` connected, `O` singular, another singular point, rigidity at `O`, non-extendable local rotations); not tied to the angles (`troyanovSuspensionTheorem_of_subsingleton`); the concrete `M` is not built |
| `lem:spread_top` (d): `M` first countable, connected, LPC, T2; `S` skeletal; "sub-covering" | ✓ carried; ✓ read: `p`, `q` branched coverings, `q ∘ p` the projection; ⚠ strengthened: `M ∖ S` semilocally simply connected as a space (`hSc`, the library's `\widetilde M^S`) |
| `lem:spread_top` (d): (none) | ⚠ added (DEC-27): `N → M` Galoisian, `N` Hausdorff (`spread_top_deck`), what the proof's `γ̄` (l.2071) needs |
| `theo:local_virt_tame`, (ii) ⇒ (i): (none) | ⚠ added (DEC-27), for the proved form: every singular point of `M` is the centre of an `X_A`-chart descending from the maximal covering of its model (`IsDescendingChartMap`: for all `e` over `U` and `f` over `φ(p e)`, a descent `V̂ ∋ f → Û ∋ e` of `φ⁻¹`, i.e. `V̂ → V` dominates `Û → U`; it holds when `r : Ṽ → V̂` is an isomorphism, `ℓ : Ũ → Û` arbitrary — informally by `prop:universality`, not formalized). Only the `r` side is forced: for a non-descending chart `r` is not an isomorphism, and the proof's (D) then needs `lem:spread_top` (c) for `r`, false in general (SCOPE (d)). The `ℓ`-quotient is built (`descTop`) and is no restriction (`isVirtuallyTame_of_descending`). The liftable special case (`IsLiftableChartMap`: `ℓ` and `r` both isomorphisms) is kept; ⚠ weakened there: local Galoisianity is not used (`isVirtuallyTame_of_liftable`); the `X_A`-atlas is used by neither form beyond the charts centred at singular points |
| `theo:local_virt_tame`, `rem:singular_point_manifold_has`: `M` an `X_A`-manifold | ✓ read as ruled (DEC-67 (e)): `IsXAManifold` asks a chart centred at every singular point, what the remark's existence and the proof's gluing (l.2101–2103) use |
| `rem:theorem_theo_local_tame`: "a `X_A`-manifold is tame iff all models are tame" | ✓ read as ruled (DEC-80 (b)): the GLOBAL equivalence over all `X_A`-manifolds; for the printed notion (l.1913) nothing is added (`forall_isTame_iff_printed`); for the DEC-67 (e) notion the models are `X_A`-manifolds (`htype`: every singular point of a model has a type), what the paper presumes at l.2086 ("each `X_α` is an `X_A`-manifold"), used by "only if" only |
| `rem:theorem_theo_local_tame`: models connected, `X` locally unloopable (standing) | ✓ carried; ⚠ weakened: analyticity of the family is not used, only `S_α` non-empty (`hne`) |

## SCOPE (disclosed)

* **(a)** `rem:singular_point_manifold_has`: the remark's argument proves uniqueness of the type
  (`hasType_unique`, the paper's proof verbatim: restriction to the component of `x` in `U₁ ∩ U₂`).
  Existence holds exactly at the centres of `X_A`-charts; under `def:atlas`'s printed "charts
  covering `M`" a singular point need not be a centre (finding; e.g. the singular lines of the
  paper's own `cex`, with `S = {O}`). DEC-67 (e) rules that an `X_A`-manifold has a chart centred
  at every singular point; under it the remark is `existsUnique_hasXAType`, closed.
* **(b)** `rem:theorem_theo_local_tame`: DEC-80 (b) rules the remark to be the GLOBAL equivalence
  (every `X_A`-manifold tame ⇔ every model tame); certified, both directions, with no added
  hypothesis for the printed notion of `X_A`-manifold (`forall_isTame_iff_printed`: "if" by
  `theo:local_tame` along an atlas, `isTame_of_isXAAtlas`; "only if" because each model is an
  `X_A`-manifold, `isXAManifoldPrinted_model`), and for the notion ruled by DEC-67 (e) over models
  which are `X_A`-manifolds — every singular point of a model has a type, the paper's presumption
  at l.2086 (`forall_isTame_iff`; "if" needs nothing, `isTame_of_isXAManifold`). Findings kept:
  read per manifold the "iff" is false (a tame `X_A`-manifold need not use every model); and under
  DEC-67 (e) without that presumption "only if" fails (informal: a model with a non-tame untyped
  singular point; no `X_A`-manifold contains a copy of a neighbourhood of it, by analyticity) — not
  formalized, the library has no non-tame singular manifold.
* **(c)** `cex:start_singular_manifold_homeomorphic`: DEC-69 makes Troyanov's theorem
  (`MR1005085`) a named external result with a non-vacuity witness and keeps the row partial.
  Named: `TroyanovSuspensionTheorem G X` — for `s ≥ 3` pairwise distinct angles satisfying
  Troyanov's condition (`TroyanovAngleCondition`, l.1931), a singular `(G,X)`-manifold (the
  Thurston suspension of the cone surface) with a centre `O` carrying the facts the cex derives
  (`SuspensionCexFacts`: `M` connected; `O` singular; some other singular point, l.1933 "singular
  locus is homeomorphic to a line except at `O`"; rigidity, every a.e. isomorphism of connected
  open subsets whose domain contains `O` is the identity, l.1933–1935; non-extendable local
  rotations around every other singular point, l.1937). The cex follows from it
  (`cex_start_singular_manifold_homeomorphic`, through
  `SuspensionCexFacts.isAnalyticModelFamily_unit_iff`: "analytic iff `S = {O}`", and, `sing M`
  being larger than `{O}`, `(M, sing M)` not analytic). Non-vacuity: the angle condition holds for
  `s = 3` pairwise distinct angles `(9π/10, 19π/20, π)` (`troyanovAngleCondition_witness`), and
  the facts hold jointly, every field exercised, on the **Joukowski structure** — `ℂ` with the
  a.e. structure pulled back by `z ↦ z + z⁻¹` on `ℂ ∖ {0, ±1}`, `G` trivial
  (`exists_suspensionCexFacts`): `sing = {0, 1, -1}` (`sing_joukowskiStructure`; `0` a pole,
  `±1` branch points); `O = 0` rigid (`joukowski_eq_of_isAEMorphism`: `z + z⁻¹` is unbounded and
  injective near `0`, then the identity theorem); at `±1` the flip `z ↦ z⁻¹` of `B(±1, 1/2)`
  (`joukowskiFlip`, `isAEMorphism_joukowskiFlip`) is an a.e. isomorphism which no automorphism
  extends (an automorphism is the identity by rigidity at `0`). **Disclosed (audit round 4):** the
  named facts mention no cone angle — the library has no notion of one — so the named `Prop` is
  not tied to `θ`: over a general `(G,X)` it asserts only that some manifold carries the facts,
  and for a trivial group on `ℂ` it holds outright for every `θ`
  (`troyanovSuspensionTheorem_of_subsingleton`). Its angle-dependent content is the paper's
  instance `(SO(4), 𝕊³)`, which is not stated: spherical cone surfaces, the
  `(SO(4), 𝕊³)`-structure of the suspension (`GX.Singular.Suspension` is topological),
  `Aut(Σ) ≅ Aut(M)` and the `s` singular rays are not in the library or mathlib. The rigidity
  fact is stronger than the paper's sentence (automorphisms of neighbourhoods of `O`); its
  derivation for the suspension is in the docstring of `isAnalyticModelFamily_unit_iff_eq_singleton`.
* **(d)** `theo:local_virt_tame`, (ii) ⇒ (i), `X_A`-manifolds as ruled (DEC-67 (e)): the proof
  (l.2086–2140) has three pieces. (1) `lem:spread_top`, certified by WP-27k (false as printed;
  (c) false even with `p⁻¹(R)` connected). (2) The topologies `T_{U,V,φ}` on `p⁻¹(U)` for each
  `X_A`-chart, with their properties and naturality, on the interface `IsLocalTamifying` (the
  paper's (A)–(D), first countability, local path-connectedness and agreement with the natural
  topology, all over `U`). (3) The gluing, proved: `exists_isTamifyingTopology_of_local` glues
  local tamifying topologies whose neighbourhood filters agree over the overlaps (`glueTop`,
  `nhds_glueTop`) into a tamifying topology — first countability, local path-connectedness, (A),
  (B) (the regular developing map `exists_isRegDevelopingOnReg`, extended by local continuous
  extensions agreeing on the dense `p⁻¹(reg M)`), (C) and (D) (`isPortly_iUnion_of_local`).
  **Piece (2) is built (WP-35f fix round 1) for every chart DESCENDING from the maximal covering
  of its model** (`IsDescendingChartMap`: for all `e` over `U` and `f` over `φ(p e)`, a descent
  `Ψ : V̂ ∋ f → Û ∋ e` of `φ⁻¹`, `IsChartDescent` — continuous on the component `V̂` of `q⁻¹(V)`,
  `φ ∘ p ∘ Ψ = q`). This is the case of the proof where `V̂ → V` dominates `Û → U`, so that
  `T_{U,V,φ}` is the `ℓ`-quotient of `T_α` itself and `r^*T_α` never enters; it contains the case
  `r : Ṽ → V̂` an isomorphism with `ℓ : Ũ → Û` ARBITRARY (then `V̂ → V` is the maximal covering of
  `V ≅ U` and dominates `Û → U`, `prop:universality` — informal, not formalized), and the liftable
  charts (`IsLiftableChartMap.isDescendingChartMap`). Then `T_{U,V,φ}` (`descTop`) has at a point
  `y` over `U` the neighbourhoods `Ψ(𝓝_{T_α}(f))` for a chosen descent `Ψ` with `Ψ f = y` (the
  quotient topology, `descNhds`, `nhds_descTop`), natural off `p⁻¹(U)`. The descents are
  Galoisian: two descents taking the same value differ by an element of `Γ(\widetilde X_α/X_α)`
  (`IsChartDescent.exists_deck`: a regular point near one is moved to a regular point near the
  other with the same image — `IsChartDescent.reg_subset_image`, path lifting through `q` — and
  the discreteness of the fibres of `q`, which is the model's local Galoisianity,
  `discreteTopology_fiber_of_isLocallyGaloisian`, pins the singular point: this is the paper's
  l.2093 "since `X_α` is locally Galoisian … all Galoisian"). So `T_{U,V,φ}` does not depend on the
  descent (`descNhds_eq`), every descent is `T_α → T_{U,V,φ}` continuous and open, and onto `Û`
  (`IsChartDescent.surjOn_cc`). All eight fields of `IsLocalTamifying` hold
  (`isLocalTamifying_descTop`): first countability and local path-connectedness as images; natural
  over `reg U` (a descent is open at regular points); (A) through (A) for `T_α`; (B) by descending
  `g • D_α`, where `D₀ ∘ Ψ = g • D_α` on the connected `reg(V̂)` (`exists_smul_eq_of_isChartDescent`,
  `lem:MtoXG`) and `D_α ∘ δ = D_α` for the deck transformations relating points of a fibre of `Ψ`
  (on `reg(V̂)`, then by `T_α`-density, l.2117–2128); (C) a deck transformation of `\widetilde M`
  composed with a descent is a descent; (D) the image of the `T_α`-portly `reg(V̂)` by the open
  surjective descent (l.2128–2133, `isPreconnected_inter_of_cover_of`). Naturality (l.2104–2107, and
  the restriction to `W ⊆ U` the gluing l.2101 uses without statement) goes through the lift `Λ` of
  `ψ ∈ Aut(X_α)` to `\widetilde X_α` (`exists_lift_singularAut`, `T_α`-continuous by hypothesis):
  `nhds_descTop_le_of_aut`. With the natural topology over `reg M` (`isLocalTamifying_natural_reg`)
  this gives `isVirtuallyTame_of_descending` (0 `sorry`). The earlier special case `ℓ`, `r` both
  isomorphisms (`IsLiftableChartMap`, `chartTop`: `T_α` transported by homeomorphisms,
  `isLocalTamifying_chartTop`, `nhds_chartTop_le_of_aut`, `isVirtuallyTame_of_liftable`) is kept:
  it does not use local Galoisianity. Both hypotheses are met, at every point including singular
  ones, by the chart `(X_α, X_α, id)` of a model whose maximal covering is Galoisian
  (`isLiftableChartMap_refl`), so neither is vacuous at singular points.
  **In general piece (2) is not proved** (`exists_isLocalTamifying_charts`, tagged `sorry`), and
  what is missing is confined to the NON-descending charts: there `V̂ → V` does not dominate
  `Û → U`, so `r : Ṽ → V̂` is not an isomorphism, and the paper's `T_{U,V,φ}` is the `ℓ`-quotient
  of `r^*T_α`; its (D) (l.2128–2133) needs `r⁻¹(R)` portly for `r^*T_α`, which is
  `lem:spread_top` (c) for `r`, false in general (WP-27k's sector counterexample) and equivalent to
  `GX.StrongLocallyConnectedOrd`, not known to follow from the hypotheses on `T_α`; this is a gap
  of the paper's proof (finding). The `ℓ`-quotient itself is not an obstruction (built here). No
  counterexample to the theorem is known. The agreement over the overlaps uses DEC-67 (e): near a
  point which has a type, every chart has that type (`XAChart.eq_of_mem_centre`) and differs from a
  chart centred there by an automorphism (`XAChart.exists_aut_eq`), so naturality gives it. Under
  the printed `def:atlas` the gluing has a gap at singular points which are the centre of no chart
  (finding, no counterexample known); DEC-67 (e) removes it. Further findings: the proof asserts
  without argument that the sub-coverings `\widetilde U → Û`, `\widetilde V → V̂` (l.2093) and
  `\widetilde M^S → N` (l.2025) of Galoisian maximal coverings are Galoisian (proved by WP-27k,
  `GX.isGaloisian_of_comp`; for the descents `V̂ → Û` used here, `IsChartDescent.exists_deck`).
  **The general case, pushed (WP-40c, DEC-82): neither closed nor refuted.** What is now proved is
  that the obstruction is not an artefact of the paper's choice of `T_{U,V,φ}`. For EVERY
  tamifying topology `T` on `\widetilde M` and every deck transformation `f` fixing a point `s`,
  `T`-neighbourhoods `N` of `s` satisfy: `N ∩ f⁻¹N` is a neighbourhood ((C)), its regular part is
  non-empty and lies in the path-connected regular part of a path component of `N` ((D), local
  path-connectedness), so some regular `z ∈ N` is joined to `f z` inside `N ∩ reg`
  (`IsTamifyingTopology.exists_joinedIn_reg_of_fixed`); with (B), inside `W ∩ reg ∩ D⁻¹(E)` for
  every natural neighbourhood `W` of `s` and neighbourhood `E` of `D(s)`
  (`IsTamifyingTopology.exists_joinedIn_devSmall`). Contrapositively
  (`not_isVirtuallyTame_of_forall_not_joinedIn`) `M` is not virtually tame as soon as some
  `f`, fixing some `s`, is carried by no `D`-small regular region near `s`. For a non-descending
  chart the elements of `Γ(\widetilde M/M)` fixing `s ∈ Û` that matter are the loops of `reg U`
  dying in `π₁(reg X_α)` but not in `π₁(reg M)` — loops of `reg(V̂)`, on which the theorem's
  hypotheses on `T_α` ((A)–(D), `Aut`-continuity) say nothing, since they constrain only
  `Γ(\widetilde X_α/X_α)`. Already the `X_A`-manifolds `M = V`, `V ⊆ X_α` open with typed singular
  points, are subject to it (`\widetilde V` is the `Ṽ` of the proof). The second new fact,
  `IsTamifyingTopology.nhds_eq_of_finite_stab` (and `nhds_eq_of_free`): at a point of finite local
  degree (a natural neighbourhood met by its own deck translates only through a finite set of
  transformations fixing the point) a tamifying topology is natural, given `\widetilde M → M`
  Galoisian ((A) and (C) make the image of a `T`-open set open). Together they REFUTE the
  mechanism proposed at WP-35f (two singular planes `P₁`, `P₂` crossing at `s` in dimension 4, the
  meridian `b` of `P₂` dying in `π₁(reg X_α)`): over `P₂ ∖ {s}` the local degree of
  `\widetilde X_α` is `1`, so `T_α` is natural there; every `T_α`-open `O ∋ ŝ` has open image in
  `X_α`, hence meets the lift of `P₂` near `s`, hence contains a natural neighbourhood of such a
  point and the small meridians `b` in it; so `reg O` carries `b`, `r⁻¹(O)` has connected regular
  part, and the paper's construction goes through there (finding, informal: the library has no
  4-dimensional models). More generally the construction goes through wherever the loops of
  `reg V̂` local at `s` are generated by meridians of strata of finite local degree. A
  counterexample to the theorem would need a model with a local loop of `reg V̂` at a singular
  point NOT so generated (e.g. a commutator of meridians of strata of infinite local degree, at the
  vertex of a tripod of singular rays in dimension 3, the model's regular part abelianising the
  local group) that every `D_α`-small regular region near `s` avoids while `T_α` stays tamifying;
  whether such a model exists is open. Building one (a three-dimensional `(G,X)`-structure whose
  maximal branched covering has non-abelian local groups, with a non-natural tamifying topology)
  is beyond the library: it has no non-tame singular manifold at all.
* **(e)** `lem:spread_top` is certified by WP-27k in `GXScaffold.SingularII.SpreadTop` (which
  imports this module): false as printed (`GX.not_spreadTopPrinted`), its strongest true form
  `GX.spread_top_corrected`. Here only `strongPullTop` (`def:topological_spaces_continuous_map`) and
  item (d), split off and proved (`spread_top_deck`) under the hypothesis its proof uses, `N → M`
  Galoisian (and `N` Hausdorff, for the uniqueness of lifts): the paper's `γ̄ ∈ Γ(N/M)` with
  `p ∘ γ = γ̄ ∘ p` (l.2071) exists for every `γ` when `N → M` is Galoisian
  (`exists_deck_semiconj_of_isGaloisian`), and the paper's one application (l.2093) has it. The
  (false) statement `GX.spread_top` with its tagged `sorry` was removed at WP-35f.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Builds on
`GX.SingularII.Tame`, `GX.SingularII.Developing`, `GX.Branched.Galois`,
`GX.Branched.Universality`, `GX.Singular.Atlas`.
-/
noncomputable section
open Set Filter Topology Function TopologicalSpace
open scoped GX
namespace GX

attribute [local instance] Classical.propDecidable

set_option linter.unusedSectionVars false

universe u v

/-! ### `def:singular_manifold_automorphisms_group` -/

section Aut

variable (G : Type*) (X : Type*) [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
  (M : Type*) [TopologicalSpace M] [LocallyConnectedSpace M] [SingularGXStructure G X M]

/-- **`def:singular_manifold_automorphisms_group`** (`RamcovGX.tex:1895`): `Aut(M)`, the group of
isomorphisms of singular `(G,X)`-manifolds `M → M` — the homeomorphisms which are a.e.
`(G,X)`-morphisms (their inverses then are, `IsAEMorphism.symm_of_homeomorph`). -/
def singularAut : Subgroup (M ≃ₜ M) where
  carrier := {φ | IsAEMorphism G X (φ : M → M)}
  one_mem' := isAEMorphism_id
  mul_mem' {a b} ha hb := IsAEMorphism.comp (f := (b : M → M)) (f' := (a : M → M)) ha hb
  inv_mem' {a} ha := IsAEMorphism.symm_of_homeomorph (φ := a) ha

variable {G X M} in
theorem mem_singularAut {φ : M ≃ₜ M} : φ ∈ singularAut G X M ↔ IsAEMorphism G X (φ : M → M) :=
  Iff.rfl

end Aut

/-! ### Maps into an open subset, restrictions of isomorphisms -/

section Restrict

variable {G : Type*} {X : Type*} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
  {P : Type*} [TopologicalSpace P] [SingularGXStructure G X P]
  {N : Type*} [TopologicalSpace N] [SingularGXStructure G X N]

/-- An open subset of a locally connected space is locally connected. -/
instance opensModels_locallyConnectedSpace {M : Type*} [TopologicalSpace M]
    [LocallyConnectedSpace M] (U : Opens M) : LocallyConnectedSpace U :=
  U.isOpen.locallyConnectedSpace

/-- A map into an open subset `V ⊆ N` (with its induced structure) is an a.e. `(G,X)`-morphism as
soon as its composite with the inclusion is. -/
theorem isAEMorphism_of_val_comp (V : Opens N) {f : P → V}
    (hf : IsAEMorphism G X (Subtype.val ∘ f)) : IsAEMorphism G X f := by
  have hBN := isMaximalAEAtlas_aeAtlas G X N
  have hBV := isMaximalAEAtlas_aeAtlas G X V
  have hcont : Continuous f := continuous_induced_rng.2 hf.continuous
  obtain ⟨-, U, hU, hreg⟩ := (isAEMorphismOf_iff hBN.1).1 hf
  have hval := isAEMorphism_opensSingular_val (G := G) (X := X) V
  have hvalreg := isRegularOn_regLocusOf (G := G) (aeAtlas G X V) (aeAtlas G X N)
    (Subtype.val : V → N)
  have hvaleq := IsAEMorphismOf.regLocusOf_eq hBV.1 hBN.1 hval
  have hmaps : MapsTo f U (support (aeAtlas G X V)) := fun x hx => by
    show f x ∈ Reg G X V
    rw [reg_opensSingular]
    exact hreg.mapsTo hx
  refine (isAEMorphismOf_iff hBV.1).2 ⟨hcont, U, hU, ⟨hreg.isOpen, hreg.subset_support, hmaps,
    hcont.continuousOn, fun x hx e he e' he' hxe hfxe' => ?_⟩⟩
  obtain ⟨c, hc, hfc⟩ := mem_support.1 (hreg.mapsTo hx)
  obtain ⟨h, hh⟩ := hreg.exists_smul_eq x hx e he c hc hxe hfc
  have hfxR : f x ∈ regLocusOf G (aeAtlas G X V) (aeAtlas G X N) Subtype.val := by
    rw [hvaleq]; exact ⟨hmaps hx, hreg.mapsTo hx⟩
  obtain ⟨k, hk⟩ := hvalreg.exists_smul_eq (f x) hfxR e' he' c hc hfxe' hfc
  refine ⟨k⁻¹ * h, ?_⟩
  filter_upwards [hh, hcont.continuousAt.eventually hk] with y h1 h2
  rw [mul_smul, ← h1]
  simp only [Function.comp_apply] at h2 ⊢
  rw [h2, inv_smul_smul]

/-- A map into an open subset is an a.e. `(G,X)`-morphism iff its composite with the inclusion
is. -/
theorem isAEMorphism_iff_val_comp [LocallyConnectedSpace P] (V : Opens N) {f : P → V} :
    IsAEMorphism G X f ↔ IsAEMorphism G X (Subtype.val ∘ f) :=
  ⟨fun hf => (isAEMorphism_opensSingular_val V).comp hf, isAEMorphism_of_val_comp V⟩

variable {M : Type*} [TopologicalSpace M]

/-- The image `φ(W)` of an open `W ⊆ U` under a homeomorphism `φ : U ≃ₜ V` of open subsets, as an
open subset of `N`. -/
def opensImageModels {U : Opens M} {V : Opens N} (φ : U ≃ₜ V) (W : Opens M) : Opens N :=
  ⟨Subtype.val '' (φ '' (Subtype.val ⁻¹' (W : Set M))),
    V.isOpen.isOpenMap_subtype_val _ (φ.isOpenMap _ (W.isOpen.preimage continuous_subtype_val))⟩

theorem mem_opensImageModels {U : Opens M} {V : Opens N} (φ : U ≃ₜ V) {W : Opens M}
    (u : U) (hu : (u : M) ∈ W) : ((φ u : V) : N) ∈ opensImageModels φ W :=
  ⟨φ u, ⟨u, hu, rfl⟩, rfl⟩

theorem opensImageModels_le {U : Opens M} {V : Opens N} (φ : U ≃ₜ V) (W : Opens M) :
    opensImageModels φ W ≤ V := by
  rintro _ ⟨v, -, rfl⟩; exact v.2

/-- The restriction `W ≃ₜ φ(W)` of a homeomorphism `φ : U ≃ₜ V` of open subsets to an open
`W ⊆ U`. -/
def opensHomeoRestrict {U : Opens M} {V : Opens N} (φ : U ≃ₜ V) (W : Opens M) (hW : W ≤ U) :
    W ≃ₜ opensImageModels φ W where
  toFun w := ⟨(φ ⟨w, hW w.2⟩ : N), mem_opensImageModels φ _ w.2⟩
  invFun w' := ⟨(φ.symm ⟨w', opensImageModels_le φ W w'.2⟩ : M), by
    obtain ⟨v, ⟨u, hu, rfl⟩, hv⟩ := w'.2
    have : (⟨(w' : N), opensImageModels_le φ W w'.2⟩ : V) = φ u := Subtype.ext hv.symm
    rw [this, φ.symm_apply_apply]; exact hu⟩
  left_inv w := by
    apply Subtype.ext
    simp only [Subtype.coe_eta, Homeomorph.symm_apply_apply]
  right_inv w' := by
    apply Subtype.ext
    simp only [Subtype.coe_eta, Homeomorph.apply_symm_apply]
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val.comp (φ.continuous.comp
      (continuous_subtype_val.subtype_mk _))
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val.comp (φ.symm.continuous.comp
      (continuous_subtype_val.subtype_mk _))

theorem opensHomeoRestrict_apply {U : Opens M} {V : Opens N} (φ : U ≃ₜ V) (W : Opens M)
    (hW : W ≤ U) (w : W) : ((opensHomeoRestrict φ W hW w : opensImageModels φ W) : N) =
      (φ ⟨w, hW w.2⟩ : N) := rfl

/-- The image of a connected open `W ⊆ U` is connected. -/
theorem isConnected_opensImageModels {U : Opens M} {V : Opens N} (φ : U ≃ₜ V) {W : Opens M}
    (hW : W ≤ U) (hWc : IsConnected (W : Set M)) :
    IsConnected (opensImageModels φ W : Set N) := by
  haveI := isConnected_iff_connectedSpace.1 hWc
  have : (opensImageModels φ W : Set N) =
      range (Subtype.val ∘ (opensHomeoRestrict φ W hW : W → opensImageModels φ W)) := by
    rw [range_comp, (opensHomeoRestrict φ W hW).surjective.range_eq, image_univ,
      Subtype.range_coe]
  rw [this]
  exact isConnected_range (continuous_subtype_val.comp (opensHomeoRestrict φ W hW).continuous)

variable [SingularGXStructure G X M] [LocallyConnectedSpace M]

/-- The inclusion `W → U` of open subsets is an a.e. `(G,X)`-morphism. -/
theorem isAEMorphism_opensInclusion {W U : Opens M} (hW : W ≤ U) :
    IsAEMorphism G X (fun w : W => (⟨w, hW w.2⟩ : U)) :=
  isAEMorphism_of_val_comp U (isAEMorphism_opensSingular_val W)

/-- The restriction of an isomorphism of open subsets is an isomorphism. -/
theorem isAEMorphism_opensHomeoRestrict {U : Opens M} {V : Opens N} {φ : U ≃ₜ V}
    (hφ : IsAEMorphism G X (φ : U → V)) (W : Opens M) (hW : W ≤ U) :
    IsAEMorphism G X (opensHomeoRestrict φ W hW : W → opensImageModels φ W) := by
  apply isAEMorphism_of_val_comp
  have h : (Subtype.val ∘ (opensHomeoRestrict φ W hW : W → opensImageModels φ W)) =
      (Subtype.val ∘ (φ : U → V)) ∘ (fun w : W => (⟨w, hW w.2⟩ : U)) := rfl
  rw [h]
  exact ((isAEMorphism_opensSingular_val V).comp hφ).comp (isAEMorphism_opensInclusion hW)

end Restrict

/-! ### Analytic families, `X_A`-charts, `X_A`-manifolds -/

section Family

variable (G : Type*) (X : Type*) [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
  {A : Type*} (Xα : A → Type u) [∀ a, TopologicalSpace (Xα a)]
  [∀ a, LocallyConnectedSpace (Xα a)] [∀ a, SingularGXStructure G X (Xα a)]
  (S : ∀ a, Set (Xα a))

/-- **`def:family_singular_manifolds_endowed`** (`RamcovGX.tex:1899`): a family `(X_α)` of
singular `(G,X)`-manifolds, each endowed with a non-empty `S_α ⊆ sing(X_α)`, is an *analytic
family of model spaces* if every a.e. `(G,X)`-isomorphism `φ : U₁ → U₂` between connected open
subsets of `X_{α₁}` and `X_{α₂}` with `U₁ ∩ S_{α₁} ≠ ∅` has `α₁ = α₂` and is the restriction of an
automorphism of `X_{α₁}`. The two conclusions are the two fields `eq_of_iso`, `exists_aut`; the
printed single clause is `isAnalyticModelFamily_iff`. -/
structure IsAnalyticModelFamily : Prop where
  nonempty : ∀ a, (S a).Nonempty
  subset_sing : ∀ a, S a ⊆ Sing G X (Xα a)
  eq_of_iso : ∀ (a₁ a₂ : A) (U₁ : Opens (Xα a₁)) (U₂ : Opens (Xα a₂)),
    IsConnected (U₁ : Set (Xα a₁)) → IsConnected (U₂ : Set (Xα a₂)) →
    ∀ φ : U₁ ≃ₜ U₂, IsAEMorphism G X (φ : U₁ → U₂) → ((U₁ : Set (Xα a₁)) ∩ S a₁).Nonempty →
      a₁ = a₂
  exists_aut : ∀ (a : A) (U₁ U₂ : Opens (Xα a)),
    IsConnected (U₁ : Set (Xα a)) → IsConnected (U₂ : Set (Xα a)) →
    ∀ φ : U₁ ≃ₜ U₂, IsAEMorphism G X (φ : U₁ → U₂) → ((U₁ : Set (Xα a)) ∩ S a).Nonempty →
      ∃ ψ ∈ singularAut G X (Xα a), ∀ x : U₁, ψ x = (φ x : Xα a)

/-- The paper's clause of `def:family_singular_manifolds_endowed`, verbatim: `α₁ = α₂` and
`∃ ϕ ∈ Aut(X_{α₁}), φ = ϕ|_{U₁}^{U₂}` (the equality read through the cast `X_{α₁} = X_{α₂}`). -/
theorem isAnalyticModelFamily_iff :
    IsAnalyticModelFamily G X Xα S ↔ (∀ a, (S a).Nonempty) ∧ (∀ a, S a ⊆ Sing G X (Xα a)) ∧
      ∀ (a₁ a₂ : A) (U₁ : Opens (Xα a₁)) (U₂ : Opens (Xα a₂)),
        IsConnected (U₁ : Set (Xα a₁)) → IsConnected (U₂ : Set (Xα a₂)) →
        ∀ φ : U₁ ≃ₜ U₂, IsAEMorphism G X (φ : U₁ → U₂) → ((U₁ : Set (Xα a₁)) ∩ S a₁).Nonempty →
          ∃ h : a₁ = a₂, ∃ ψ ∈ singularAut G X (Xα a₁),
            ∀ x : U₁, cast (congrArg Xα h) (ψ x) = (φ x : Xα a₂) := by
  constructor
  · intro h
    refine ⟨h.nonempty, h.subset_sing, fun a₁ a₂ U₁ U₂ h₁ h₂ φ hφ hS => ?_⟩
    obtain rfl := h.eq_of_iso a₁ a₂ U₁ U₂ h₁ h₂ φ hφ hS
    obtain ⟨ψ, hψ, hψφ⟩ := h.exists_aut a₁ U₁ U₂ h₁ h₂ φ hφ hS
    exact ⟨rfl, ψ, hψ, hψφ⟩
  · rintro ⟨hne, hsub, h⟩
    refine ⟨hne, hsub, fun a₁ a₂ U₁ U₂ h₁ h₂ φ hφ hS => (h a₁ a₂ U₁ U₂ h₁ h₂ φ hφ hS).1,
      fun a U₁ U₂ h₁ h₂ φ hφ hS => ?_⟩
    obtain ⟨he, ψ, hψ, hψφ⟩ := h a a U₁ U₂ h₁ h₂ φ hφ hS
    exact ⟨ψ, hψ, fun x => by simpa using hψφ x⟩

variable {M : Type*} [TopologicalSpace M] [SingularGXStructure G X M]

/-- **`def:atlas`** (`RamcovGX.tex:1905`): an *`X_α`-chart around `x`* is a triple `(U, V, φ)`
with `x ∈ U ⊆ M` open, `V ⊆ X_α` open and connected, `φ : U → V` an isomorphism of singular
`(G,X)`-manifolds (a homeomorphism which is an a.e. `(G,X)`-morphism, the open sets with their
induced structures), and `φ(x) ∈ S_α`. (That `x ∈ sing(M)` follows: `XAChart.mem_sing`.) -/
structure XAChart (a : A) (x : M) where
  /-- The domain. -/
  U : Opens M
  /-- The image, in the model. -/
  V : Opens (Xα a)
  /-- The isomorphism. -/
  φ : U ≃ₜ V
  mem : x ∈ U
  isConnected_V : IsConnected (V : Set (Xα a))
  isAEMorphism : IsAEMorphism G X (φ : U → V)
  mem_S : (φ ⟨x, mem⟩ : Xα a) ∈ S a

variable {M : Type*} [TopologicalSpace M] [SingularGXStructure G X M]

variable {G X Xα S} in
/-- `def:atlas`: `x` *has type `α`* if there is an `X_α`-chart around it. -/
def HasXAType (a : A) (x : M) : Prop := Nonempty (XAChart G X Xα S a x)

variable (M) in
/-- **`def:atlas`**: an *`X_A`-atlas* is a collection of `X_A`-charts (an `X_α`-chart for some `α`)
covering `M`. -/
def IsXAAtlas (𝒜 : Set (Σ a : A, Σ x : M, XAChart G X Xα S a x)) : Prop :=
  ∀ y : M, ∃ c ∈ 𝒜, y ∈ c.2.2.U

variable (M) in
/-- `def:analytic_family_model_spaces` as printed (`RamcovGX.tex:1913`): `M` admits an `X_A`-atlas.
Kept as the printed form; the notion of the paper, as ruled (DEC-67 (e)), is `IsXAManifold`. -/
def IsXAManifoldPrinted : Prop :=
  ∃ 𝒜 : Set (Σ a : A, Σ x : M, XAChart G X Xα S a x), IsXAAtlas G X Xα S M 𝒜

variable (M) in
/-- **`def:analytic_family_model_spaces`** (`RamcovGX.tex:1913`), read as ruled by DEC-67 (e): an
*`X_A`-manifold* is a singular `(G,X)`-manifold admitting an `X_A`-atlas (`exists_atlas`) and
having a chart centred at every singular point (`hasType`: every singular point has a type). -/
structure IsXAManifold : Prop where
  exists_atlas : IsXAManifoldPrinted G X Xα S M
  hasType : ∀ y ∈ Sing G X M, ∃ a, HasXAType (G := G) (X := X) (Xα := Xα) (S := S) a y

variable {G X Xα S}

/-- The point a chart is centred at is singular. -/
theorem XAChart.mem_sing (hS : ∀ a, S a ⊆ Sing G X (Xα a)) {a : A} {x : M}
    (c : XAChart G X Xα S a x) : x ∈ Sing G X M := by
  have h := (IsAEMorphism.preimage_reg_sing c.isAEMorphism c.φ.isLocalHomeomorph).2
  have hV : c.φ ⟨x, c.mem⟩ ∈ Sing G X c.V := by
    rw [sing_opensSingular]; exact hS a c.mem_S
  have hU : (⟨x, c.mem⟩ : c.U) ∈ Sing G X c.U := by rw [← h]; exact hV
  rw [sing_opensSingular] at hU
  exact hU

/-- An `X_α`-chart restricts to a connected open `W ∋ x` inside its domain. -/
def XAChart.restrict [LocallyConnectedSpace M] {a : A} {x : M} (c : XAChart G X Xα S a x)
    (W : Opens M) (hxW : x ∈ W) (hWU : W ≤ c.U) (hWc : IsConnected (W : Set M)) :
    XAChart G X Xα S a x where
  U := W
  V := opensImageModels c.φ W
  φ := opensHomeoRestrict c.φ W hWU
  mem := hxW
  isConnected_V := isConnected_opensImageModels c.φ hWU hWc
  isAEMorphism := isAEMorphism_opensHomeoRestrict c.isAEMorphism W hWU
  mem_S := c.mem_S

/-- The uniqueness half of `rem:singular_point_manifold_has` (`RamcovGX.tex:1921`): a point has at
most one type. The paper's proof: restrict both charts to the connected component `W` of `x` in
`U₁ ∩ U₂`; `φ₂ ∘ φ₁⁻¹ : φ₁(W) → φ₂(W)` is an isomorphism of connected open subsets of the models,
and `φ₁(W)` meets `S_{α₁}` at `φ₁(x)`, so `α₁ = α₂` by analyticity. -/
theorem hasType_unique [LocallyConnectedSpace M] (hfam : IsAnalyticModelFamily G X Xα S)
    {a₁ a₂ : A} {x : M} (h₁ : HasXAType (G := G) (X := X) (Xα := Xα) (S := S) a₁ x)
    (h₂ : HasXAType (G := G) (X := X) (Xα := Xα) (S := S) a₂ x) : a₁ = a₂ := by
  obtain ⟨c₁⟩ := h₁
  obtain ⟨c₂⟩ := h₂
  set W : Opens M := ⟨connectedComponentIn ((c₁.U : Set M) ∩ c₂.U) x,
    (c₁.U.isOpen.inter c₂.U.isOpen).connectedComponentIn⟩
  have hxW : x ∈ W := mem_connectedComponentIn ⟨c₁.mem, c₂.mem⟩
  have hW₁ : W ≤ c₁.U := fun y hy => (connectedComponentIn_subset _ _ hy).1
  have hW₂ : W ≤ c₂.U := fun y hy => (connectedComponentIn_subset _ _ hy).2
  have hWc : IsConnected (W : Set M) := isConnected_connectedComponentIn_iff.2 ⟨c₁.mem, c₂.mem⟩
  set d₁ := c₁.restrict W hxW hW₁ hWc
  set d₂ := c₂.restrict W hxW hW₂ hWc
  set ψ : d₁.V ≃ₜ d₂.V := d₁.φ.symm.trans d₂.φ
  have hψ : IsAEMorphism G X (ψ : d₁.V → d₂.V) :=
    d₂.isAEMorphism.comp (IsAEMorphism.symm_of_homeomorph d₁.isAEMorphism)
  exact hfam.eq_of_iso a₁ a₂ d₁.V d₂.V d₁.isConnected_V d₂.isConnected_V ψ hψ
    ⟨_, (d₁.φ ⟨x, hxW⟩).2, d₁.mem_S⟩

/-- **`rem:singular_point_manifold_has`** (`RamcovGX.tex:1921`), under DEC-67 (e): a singular point
of an `X_A`-manifold has exactly one type — existence is DEC-67 (e)'s reading of the notion
(`IsXAManifold.hasType`), uniqueness the remark's argument (`hasType_unique`). -/
theorem existsUnique_hasXAType [LocallyConnectedSpace M] (hfam : IsAnalyticModelFamily G X Xα S)
    (hM : IsXAManifold G X Xα S M) {x : M} (hx : x ∈ Sing G X M) :
    ∃! a, HasXAType (G := G) (X := X) (Xα := Xα) (S := S) a x := by
  obtain ⟨a, ha⟩ := hM.hasType x hx
  exact ⟨a, ha, fun b hb => hasType_unique hfam hb ha⟩

variable (G X S) in
/-- The `X_α`-chart `(X_α, X_α, id)` around a point of `S_α`. -/
def modelChartSelf (a : A) [ConnectedSpace (Xα a)] {s : Xα a} (hs : s ∈ S a) :
    XAChart G X Xα S a s where
  U := ⊤
  V := ⊤
  φ := Homeomorph.refl _
  mem := trivial
  isConnected_V := by rw [Opens.coe_top]; exact isConnected_univ
  isAEMorphism := isAEMorphism_id
  mem_S := hs

/-- A model `X_α` (connected, the standing convention l.1712) admits an `X_A`-atlas, the single
chart `(X_α, X_α, id)` around a point of `S_α ≠ ∅`. -/
theorem isXAManifoldPrinted_model (hne : ∀ a, (S a).Nonempty) (a : A) [ConnectedSpace (Xα a)] :
    IsXAManifoldPrinted G X Xα S (Xα a) := by
  obtain ⟨s, hs⟩ := hne a
  exact ⟨{⟨a, s, modelChartSelf G X S a hs⟩}, fun y => ⟨⟨a, s, modelChartSelf G X S a hs⟩, rfl,
    show y ∈ (⊤ : Opens (Xα a)) from trivial⟩⟩

/-- A model `X_α` (connected) all of whose singular points have a type is an `X_A`-manifold
(DEC-67 (e)). Under DEC-67 (e) a model need not be an `X_A`-manifold: a point of
`sing X_α ∖ S_α` may have no type. -/
theorem isXAManifold_model (hne : ∀ a, (S a).Nonempty) (a : A) [ConnectedSpace (Xα a)]
    (htype : ∀ y ∈ Sing G X (Xα a), ∃ b, HasXAType (G := G) (X := X) (Xα := Xα) (S := S) b y) :
    IsXAManifold G X Xα S (Xα a) :=
  ⟨isXAManifoldPrinted_model hne a, htype⟩

/-- A model with `S_α = sing X_α` (connected) is an `X_A`-manifold: every singular point `s` is the
centre of `(X_α, X_α, id)`. -/
theorem isXAManifold_model_of_sing_subset (hne : ∀ a, (S a).Nonempty) (a : A)
    [ConnectedSpace (Xα a)] (hS : Sing G X (Xα a) ⊆ S a) : IsXAManifold G X Xα S (Xα a) :=
  isXAManifold_model hne a fun _ hy => ⟨a, ⟨modelChartSelf G X S a (hS hy)⟩⟩

/-- `def:analytic_family_model_spaces`: `M` admits an `X_A`-atlas iff every point lies in the domain
of some `X_A`-chart. -/
theorem isXAManifoldPrinted_iff : IsXAManifoldPrinted G X Xα S M ↔
    ∀ y : M, ∃ (a : A) (x : M) (c : XAChart G X Xα S a x), y ∈ c.U := by
  constructor
  · rintro ⟨𝒜, h𝒜⟩ y
    obtain ⟨⟨a, x, c⟩, -, hy⟩ := h𝒜 y
    exact ⟨a, x, c, hy⟩
  · intro h
    refine ⟨univ, fun y => ?_⟩
    obtain ⟨a, x, c, hy⟩ := h y
    exact ⟨⟨a, x, c⟩, trivial, hy⟩

/-- The first step of the proof of `theo:local_virt_tame` (l.2105): two `X_α`-charts agree, on a
connected open `W` inside both domains and containing the centre of the first, up to an
automorphism of `X_α` — `φ₂ ∘ φ₁⁻¹ : φ₁(W) → φ₂(W)` is an isomorphism of connected open subsets
meeting `S_α`, hence (analyticity) the restriction of some `ψ ∈ Aut(X_α)`. -/
theorem XAChart.exists_aut_eq [LocallyConnectedSpace M] (hfam : IsAnalyticModelFamily G X Xα S)
    {a : A} {x₁ x₂ : M} (c₁ : XAChart G X Xα S a x₁) (c₂ : XAChart G X Xα S a x₂)
    (W : Opens M) (h₁ : W ≤ c₁.U) (h₂ : W ≤ c₂.U) (hWc : IsConnected (W : Set M)) (hxW : x₁ ∈ W) :
    ∃ ψ ∈ singularAut G X (Xα a), ∀ w : W,
      ψ (c₁.φ ⟨w, h₁ w.2⟩ : Xα a) = (c₂.φ ⟨w, h₂ w.2⟩ : Xα a) := by
  set ψ₀ := (opensHomeoRestrict c₁.φ W h₁).symm.trans (opensHomeoRestrict c₂.φ W h₂)
  have hψ₀ : IsAEMorphism G X (ψ₀ : opensImageModels c₁.φ W → opensImageModels c₂.φ W) :=
    (isAEMorphism_opensHomeoRestrict c₂.isAEMorphism W h₂).comp
      (IsAEMorphism.symm_of_homeomorph (isAEMorphism_opensHomeoRestrict c₁.isAEMorphism W h₁))
  obtain ⟨ψ, hψ, hψeq⟩ := hfam.exists_aut a _ _ (isConnected_opensImageModels c₁.φ h₁ hWc)
    (isConnected_opensImageModels c₂.φ h₂ hWc) ψ₀ hψ₀
    ⟨_, mem_opensImageModels c₁.φ ⟨x₁, h₁ hxW⟩ hxW, c₁.mem_S⟩
  refine ⟨ψ, hψ, fun w => ?_⟩
  have := hψeq (opensHomeoRestrict c₁.φ W h₁ w)
  simp only [ψ₀, Homeomorph.trans_apply, Homeomorph.symm_apply_apply] at this
  exact this

/-- `def:family_singular_manifolds_endowed`, contrapositive form: an a.e. isomorphism of connected
open subsets of `X_α` which is not the restriction of an automorphism has a domain missing `S_α`
(the reasoning of `cex:start_singular_manifold_homeomorphic`, l.1937). -/
theorem IsAnalyticModelFamily.inter_eq_empty_of_not_extend (hfam : IsAnalyticModelFamily G X Xα S)
    {a : A} {U₁ U₂ : Opens (Xα a)} (h₁ : IsConnected (U₁ : Set (Xα a)))
    (h₂ : IsConnected (U₂ : Set (Xα a))) {φ : U₁ ≃ₜ U₂} (hφ : IsAEMorphism G X (φ : U₁ → U₂))
    (hne : ¬ ∃ ψ ∈ singularAut G X (Xα a), ∀ x : U₁, ψ x = (φ x : Xα a)) :
    (U₁ : Set (Xα a)) ∩ S a = ∅ := by
  by_contra h
  exact hne (hfam.exists_aut a U₁ U₂ h₁ h₂ φ hφ (nonempty_iff_ne_empty.2 h))

/-- An `X_A`-chart `c` meeting, on a connected open `W`, the centre `y` of an `X_b`-chart `c₀` has
type `b`: `φ_c ∘ φ_{c₀}⁻¹ : φ_{c₀}(W) → φ_c(W)` is an isomorphism of connected open subsets of the
models meeting `S_b` at `φ_{c₀}(y)` (analyticity). Near a point which has a type, every chart has
that type. -/
theorem XAChart.eq_of_mem_centre [LocallyConnectedSpace M] (hfam : IsAnalyticModelFamily G X Xα S)
    {b a : A} {y x : M} (c₀ : XAChart G X Xα S b y) (c : XAChart G X Xα S a x) (W : Opens M)
    (h₀ : W ≤ c₀.U) (h : W ≤ c.U) (hWc : IsConnected (W : Set M)) (hyW : y ∈ W) : b = a := by
  set ψ₀ := (opensHomeoRestrict c₀.φ W h₀).symm.trans (opensHomeoRestrict c.φ W h)
  have hψ₀ : IsAEMorphism G X (ψ₀ : opensImageModels c₀.φ W → opensImageModels c.φ W) :=
    (isAEMorphism_opensHomeoRestrict c.isAEMorphism W h).comp
      (IsAEMorphism.symm_of_homeomorph (isAEMorphism_opensHomeoRestrict c₀.isAEMorphism W h₀))
  exact hfam.eq_of_iso b a _ _ (isConnected_opensImageModels c₀.φ h₀ hWc)
    (isConnected_opensImageModels c.φ h hWc) ψ₀ hψ₀
    ⟨_, mem_opensImageModels c₀.φ ⟨y, h₀ hyW⟩ hyW, c₀.mem_S⟩

end Family

/-! ### `cex:start_singular_manifold_homeomorphic`, abstractly -/

section CexAbstract

variable {G : Type*} {X : Type*} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
  {M : Type u} [TopologicalSpace M] [LocallyConnectedSpace M] [SingularGXStructure G X M]

/-- `cex:start_singular_manifold_homeomorphic` (`RamcovGX.tex:1930`), the inference of its last
paragraph, abstracted over the manifold: let `O ∈ sing(M)` be such that
* (rigidity at `O`, l.1933–1935: "an automorphism of `M` has to fix `O`", `Aut` trivial, "these
  remarks hold for all neighborhoods of `O`") every a.e. isomorphism `φ : U₁ → U₂` of connected open
  subsets of `M` with `O ∈ U₁` is the identity on `U₁`;
* (local rotations, l.1937: "locally we may construct a rotation around any of the axes and …
  those cannot be extended") every singular point `s ≠ O` lies in the domain of an a.e.
  isomorphism of connected open subsets which is not the restriction of an automorphism of `M`.

Then for `S ⊆ sing(M)`, `(M, S)` is an analytic family (indexed by a point) iff `S = {O}`.
The first hypothesis is stronger than the paper's sentence (which speaks of automorphisms of
neighbourhoods of `O`); it is derived from it for the suspension: `φ(O) = O` (`O` the only
singular point off the singular lines), `φ` is an isometry so maps an `ε`-ball at `O` onto
itself, `Aut` of that ball is trivial, and rigidity of `(G,X)`-morphisms propagates the identity
over the connected `U₁`. The mathematical content of the cex is establishing both hypotheses for
the concrete suspension.
The facts are packaged as `SuspensionCexFacts`; the existence of such an `M` for a generic
spherical cone surface `Σ` (Troyanov, the Thurston suspension) is the named external result
`TroyanovSuspensionTheorem` (DEC-69, SCOPE (c)). -/
theorem isAnalyticModelFamily_unit_iff_eq_singleton {O : M} (hO : O ∈ Sing G X M)
    (hrigid : ∀ (U₁ U₂ : Opens M), IsConnected (U₁ : Set M) → IsConnected (U₂ : Set M) →
      ∀ φ : U₁ ≃ₜ U₂, IsAEMorphism G X (φ : U₁ → U₂) → O ∈ U₁ → ∀ x : U₁, (φ x : M) = x)
    (hrot : ∀ s ∈ Sing G X M, s ≠ O → ∃ (U₁ U₂ : Opens M), IsConnected (U₁ : Set M) ∧
      IsConnected (U₂ : Set M) ∧ s ∈ U₁ ∧ ∃ φ : U₁ ≃ₜ U₂, IsAEMorphism G X (φ : U₁ → U₂) ∧
        ¬ ∃ ψ ∈ singularAut G X M, ∀ x : U₁, ψ x = (φ x : M))
    {S : Set M} (hS : S ⊆ Sing G X M) :
    IsAnalyticModelFamily G X (fun _ : Unit => M) (fun _ => S) ↔ S = {O} := by
  constructor
  · intro h
    have hsub : ∀ s ∈ S, s = O := fun s hs => by
      by_contra hne
      obtain ⟨U₁, U₂, h₁, h₂, hsU, φ, hφ, hnot⟩ := hrot s (hS hs) hne
      exact hnot (h.exists_aut () U₁ U₂ h₁ h₂ φ hφ ⟨s, hsU, hs⟩)
    obtain ⟨t, ht⟩ := h.nonempty ()
    have htO := hsub t ht
    ext s
    exact ⟨fun hs => hsub s hs, fun hs => by rw [hs, ← htO]; exact ht⟩
  · rintro rfl
    refine ⟨fun _ => singleton_nonempty O, fun _ => singleton_subset_iff.2 hO,
      fun _ _ _ _ _ _ _ _ _ => Subsingleton.elim _ _, fun _ U₁ U₂ h₁ h₂ φ hφ hne => ?_⟩
    obtain ⟨y, hyU, hyO⟩ := hne
    rw [mem_singleton_iff] at hyO
    subst hyO
    exact ⟨1, (singularAut G X M).one_mem, fun x => (hrigid U₁ U₂ h₁ h₂ φ hφ hyU x).symm⟩

variable (G X M) in
/-- `cex:start_singular_manifold_homeomorphic` (`RamcovGX.tex:1930`): the facts the cex derives,
for the Thurston suspension `M` of a generic spherical cone surface `Σ` and its centre `O`, from
Troyanov's theorem and the suspension (l.1933–1937), named (DEC-69):
* `connected`: `M` is connected (the suspension of the connected `Σ`, l.1712's convention);
* `mem_sing`: `O` is singular;
* `exists_ne` (l.1933, "singular locus is homeomorphic to a line except at `O`"): the singular
  locus is not reduced to `O` — in the suspension it is `O` and the `s ≥ 3` open rays over the
  cone points of `Σ`; only "some other singular point" is asked here (audit round 4: without it
  the named facts hold on a manifold with `sing = {O}`, where the conclusion is trivial);
* `rigid` (l.1933–1935, "these remarks hold for all neighborhoods of `O`"): every a.e. isomorphism
  `φ : U₁ → U₂` of connected open subsets of `M` with `O ∈ U₁` is the identity on `U₁`;
* `rot` (l.1937, "locally we may construct a rotation around any of the axes and … those cannot be
  extended"): every singular point `s ≠ O` lies in the domain of an a.e. isomorphism of connected
  open subsets which is not the restriction of an automorphism of `M`.
Nothing here mentions the cone angles `θ_i` (the library has no cone angle): the facts are not
tied to `θ` (SCOPE (c)). They are jointly satisfiable with `rot` non-vacuous
(`exists_suspensionCexFacts`, the Joukowski witness). -/
structure SuspensionCexFacts (O : M) : Prop where
  connected : ConnectedSpace M
  mem_sing : O ∈ Sing G X M
  exists_ne : ∃ s ∈ Sing G X M, s ≠ O
  rigid : ∀ (U₁ U₂ : Opens M), IsConnected (U₁ : Set M) → IsConnected (U₂ : Set M) →
    ∀ φ : U₁ ≃ₜ U₂, IsAEMorphism G X (φ : U₁ → U₂) → O ∈ U₁ → ∀ x : U₁, (φ x : M) = x
  rot : ∀ s ∈ Sing G X M, s ≠ O → ∃ (U₁ U₂ : Opens M), IsConnected (U₁ : Set M) ∧
    IsConnected (U₂ : Set M) ∧ s ∈ U₁ ∧ ∃ φ : U₁ ≃ₜ U₂, IsAEMorphism G X (φ : U₁ → U₂) ∧
      ¬ ∃ ψ ∈ singularAut G X M, ∀ x : U₁, ψ x = (φ x : M)

/-- `cex:start_singular_manifold_homeomorphic`, the inference from the named facts: for
`S ⊆ sing(M)`, `(M, S)` is an analytic family iff `S = {O}`. -/
theorem SuspensionCexFacts.isAnalyticModelFamily_unit_iff {O : M}
    (hO : SuspensionCexFacts G X M O) {S : Set M} (hS : S ⊆ Sing G X M) :
    IsAnalyticModelFamily G X (fun _ : Unit => M) (fun _ => S) ↔ S = {O} :=
  isAnalyticModelFamily_unit_iff_eq_singleton hO.mem_sing hO.rigid hO.rot hS

end CexAbstract

/-! ### `cex:start_singular_manifold_homeomorphic`: Troyanov's theorem, named (DEC-69) -/

section Troyanov

/-- Troyanov's angle condition (`RamcovGX.tex:1931`, `MR1005085`), for `s ≥ 3` cone angles
`θ_1, …, θ_s`: `0 < ∑ (θ_i − 2π) + 4π ≤ min(4π, θ_i : i ∈ ⟦1, s⟧)`. (Positivity of the angles
follows: `TroyanovAngleCondition.pos`.) -/
def TroyanovAngleCondition {s : ℕ} (θ : Fin s → ℝ) : Prop :=
  3 ≤ s ∧ 0 < ∑ i, (θ i - 2 * Real.pi) + 4 * Real.pi ∧
    ∑ i, (θ i - 2 * Real.pi) + 4 * Real.pi ≤ 4 * Real.pi ∧
    ∀ j, ∑ i, (θ i - 2 * Real.pi) + 4 * Real.pi ≤ θ j

theorem TroyanovAngleCondition.pos {s : ℕ} {θ : Fin s → ℝ} (h : TroyanovAngleCondition θ)
    (j : Fin s) : 0 < θ j :=
  h.2.1.trans_le (h.2.2.2 j)

/-- The non-vacuity witness of Troyanov's hypothesis (DEC-69): `s = 3` pairwise distinct angles
`(9π/10, 19π/20, π)` satisfy the angle condition (`∑ (θ_i − 2π) + 4π = 17π/20`). -/
theorem troyanovAngleCondition_witness :
    TroyanovAngleCondition ![9 * Real.pi / 10, 19 * Real.pi / 20, Real.pi] ∧
      Pairwise fun i j => ![9 * Real.pi / 10, 19 * Real.pi / 20, Real.pi] i ≠
        ![9 * Real.pi / 10, 19 * Real.pi / 20, Real.pi] j := by
  have hπ := Real.pi_pos
  refine ⟨⟨le_rfl, ?_, ?_, fun j => ?_⟩, fun i j hij => ?_⟩
  · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    linarith
  · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    linarith
  · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    fin_cases j <;> simp <;> linarith
  · fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> intro h <;> linarith

variable (G : Type*) (X : Type*) [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]

/-- **Troyanov's theorem with the Thurston suspension**, the named external result of
`cex:start_singular_manifold_homeomorphic` (DEC-69, an exception to DEC-23; `MR1005085` for the
surface, `sec:susp` for the suspension, l.1933–1937 for the facts): for `s ≥ 3` pairwise distinct
angles satisfying Troyanov's condition, a spherical cone surface `Σ` with these angles exists, and
its Thurston suspension `M`, a singular `(G,X)`-manifold, has a centre `O` with the facts the cex
derives (`SuspensionCexFacts`). The paper's instance is `(G,X) = (SO(4), 𝕊³)`; spherical cone
surfaces and the `(SO(4), 𝕊³)`-structure are not in the library, so the statement is carried as a
`Prop` over `(G,X)`. "Generic `Σ`" is read through the paper's instance "all the `θ_i` different"
(l.1935). The angle condition is satisfiable (`troyanovAngleCondition_witness`) and the facts
are, every field exercised (`exists_suspensionCexFacts`).

**Not tied to `θ`** (disclosed, audit round 4): `SuspensionCexFacts` mentions no cone angle (the
library has none), so over a general `(G,X)` this `Prop` asserts only that some manifold carries
the facts; for a trivial group on `ℂ` it holds outright for every `θ`
(`troyanovSuspensionTheorem_of_subsingleton`). Its angle-dependent content lives only at the
paper's `(SO(4), 𝕊³)`, which cannot be stated here. -/
def TroyanovSuspensionTheorem : Prop :=
  ∀ {s : ℕ} (θ : Fin s → ℝ), TroyanovAngleCondition θ → Pairwise (fun i j => θ i ≠ θ j) →
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : LocallyConnectedSpace M)
      (_ : SingularGXStructure G X M) (O : M), SuspensionCexFacts G X M O

variable {G X}

/-- `cex:start_singular_manifold_homeomorphic` (`RamcovGX.tex:1930`), from the named external
result (DEC-69): for every `s ≥ 3` pairwise distinct angles satisfying Troyanov's condition there
is a connected singular `(G,X)`-manifold `M` (the suspension) with a singular point `O` and some
other singular point such that, for `S ⊆ sing(M)`, `(M, S)` is analytic iff `S = {O}` — in
particular `(M, sing M)` is not analytic. -/
theorem cex_start_singular_manifold_homeomorphic (hT : TroyanovSuspensionTheorem G X) {s : ℕ}
    (θ : Fin s → ℝ) (hθ : TroyanovAngleCondition θ) (hd : Pairwise fun i j => θ i ≠ θ j) :
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : LocallyConnectedSpace M)
      (_ : SingularGXStructure G X M) (O : M), ConnectedSpace M ∧ O ∈ Sing G X M ∧
        (∃ s ∈ Sing G X M, s ≠ O) ∧ (¬ IsAnalyticModelFamily G X (fun _ : Unit => M)
          (fun _ => Sing G X M)) ∧ ∀ S ⊆ Sing G X M,
            (IsAnalyticModelFamily G X (fun _ : Unit => M) (fun _ => S) ↔ S = {O}) := by
  obtain ⟨M, _, _, _, O, hO⟩ := hT θ hθ hd
  refine ⟨M, _, _, _, O, hO.connected, hO.mem_sing, hO.exists_ne, fun h => ?_,
    fun S hS => hO.isAnalyticModelFamily_unit_iff hS⟩
  obtain ⟨t, ht, htO⟩ := hO.exists_ne
  have hsO := (hO.isAnalyticModelFamily_unit_iff subset_rfl).1 h
  exact htO (by rw [hsO] at ht; exact ht)

/-- For a trivial group, a singular `(G,X)`-manifold `N` with one chart of its maximal a.e. atlas
defined on all of `reg N` admits at most one a.e. `(G,X)`-morphism from any `M`: at a common
regular point both read, in that chart, as the same chart of `M`; the agreement set is closed
and contains a portly set. -/
theorem eq_of_isAEMorphism_of_subsingleton [Subsingleton G] {M : Type*} [TopologicalSpace M]
    [SingularGXStructure G X M] {N : Type*} [TopologicalSpace N] [T2Space N]
    [SingularGXStructure G X N] {e : OpenPartialHomeomorph N X} (he : e ∈ aeAtlas G X N)
    (hsrc : Reg G X N ⊆ e.source) {f₁ f₂ : M → N} (h₁ : IsAEMorphism G X f₁)
    (h₂ : IsAEMorphism G X f₂) : f₁ = f₂ := by
  obtain ⟨U₁, -, hU₁, -, -, -, r₁⟩ := h₁.exists_isRegularOn
  obtain ⟨U₂, -, hU₂, -, -, -, r₂⟩ := h₂.exists_isRegularOn
  have hR : IsPortly (U₁ ∩ U₂) := hU₁.inter hU₂
  have key : ∀ x ∈ U₁ ∩ U₂, f₁ x = f₂ x := by
    rintro x ⟨hx₁, hx₂⟩
    obtain ⟨c, hc, hxc⟩ := mem_support.1 (r₁.subset_support hx₁)
    have hf₁ : f₁ x ∈ e.source := hsrc (r₁.mapsTo hx₁)
    have hf₂ : f₂ x ∈ e.source := hsrc (r₂.mapsTo hx₂)
    obtain ⟨g₁, hg₁⟩ := r₁.exists_smul_eq x hx₁ c hc e he hxc hf₁
    obtain ⟨g₂, hg₂⟩ := r₂.exists_smul_eq x hx₂ c hc e he hxc hf₂
    have e₁ := hg₁.self_of_nhds
    have e₂ := hg₂.self_of_nhds
    rw [Subsingleton.elim g₁ 1, one_smul] at e₁
    rw [Subsingleton.elim g₂ 1, one_smul] at e₂
    exact e.injOn hf₁ hf₂ (e₁.trans e₂.symm)
  have hcl : IsClosed {x | f₁ x = f₂ x} := isClosed_eq h₁.continuous h₂.continuous
  funext x
  exact (hcl.closure_subset_iff.2 key) (hR.dense x)

end Troyanov

/-! ### The non-vacuity witness of `SuspensionCexFacts`: the Joukowski structure on `ℂ` -/

section Joukowski

/-- The Joukowski map `z ↦ z + z⁻¹`. -/
def joukowski (z : ℂ) : ℂ := z + z⁻¹

/-- Its regular set `ℂ ∖ {0, 1, -1}`. -/
def joukowskiReg : Set ℂ := ({0, 1, -1} : Set ℂ)ᶜ

/-- `z + z⁻¹` is invariant under `z ↦ z⁻¹`. -/
theorem joukowski_inv (z : ℂ) : joukowski z⁻¹ = joukowski z := by
  simp [joukowski, add_comm]

/-- Membership in `ℂ ∖ {0, ±1}`. -/
theorem mem_joukowskiReg {z : ℂ} : z ∈ joukowskiReg ↔ z ≠ 0 ∧ z ≠ 1 ∧ z ≠ -1 := by
  simp [joukowskiReg, not_or]

/-- A point of norm `≠ 0, 1` is regular for the Joukowski map. -/
theorem mem_joukowskiReg_of_norm {z : ℂ} (h0 : ‖z‖ ≠ 0) (h1 : ‖z‖ ≠ 1) : z ∈ joukowskiReg := by
  refine mem_joukowskiReg.2 ⟨fun h => h0 (by rw [h, norm_zero]), fun h => h1 (by rw [h, norm_one]),
    fun h => h1 (by rw [h, norm_neg, norm_one])⟩

/-- The regular set is stable under `z ↦ z⁻¹`. -/
theorem inv_mem_joukowskiReg {z : ℂ} (hz : z ∈ joukowskiReg) : z⁻¹ ∈ joukowskiReg := by
  obtain ⟨h0, h1, h2⟩ := mem_joukowskiReg.1 hz
  refine mem_joukowskiReg.2 ⟨inv_ne_zero h0, fun h => h1 (inv_eq_one.1 h), fun h => h2 ?_⟩
  rw [← inv_inv z, h, inv_neg, inv_one]

/-- `ℂ ∖ {0, ±1}` is portly (`isSkeletal_of_countable`). -/
theorem isPortly_joukowskiReg : IsPortly joukowskiReg :=
  isSkeletal_of_countable (E := ℂ) (by rw [Complex.rank_real_complex]; norm_num)
    (Set.toFinite _).countable (Set.toFinite _).isClosed

/-- `(z + z⁻¹)' = 1 − z⁻²`. -/
theorem joukowski_hasStrictDerivAt {z : ℂ} (hz : z ≠ 0) :
    HasStrictDerivAt joukowski (1 - (z ^ 2)⁻¹) z := by
  have := (hasStrictDerivAt_id z).add (hasStrictDerivAt_inv hz)
  rw [show (1 : ℂ) - (z ^ 2)⁻¹ = 1 + -(z ^ 2)⁻¹ by ring]
  exact this

/-- The Joukowski map is a local homeomorphism off `{0, ±1}` (inverse function theorem). -/
theorem isLocalHomeomorphOn_joukowski : IsLocalHomeomorphOn joukowski joukowskiReg := by
  intro z hz
  obtain ⟨h0, h1, h2⟩ := mem_joukowskiReg.1 hz
  have hd : (1 - (z ^ 2)⁻¹ : ℂ) ≠ 0 := by
    intro h
    have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 h0
    have h' : (z - 1) * (z + 1) = 0 := by
      have : (z - 1) * (z + 1) = z ^ 2 * (1 - (z ^ 2)⁻¹) := by field_simp; ring
      rw [this, h, mul_zero]
    rcases mul_eq_zero.1 h' with h' | h'
    · exact h1 (sub_eq_zero.1 h')
    · exact h2 (eq_neg_of_add_eq_zero_left h')
  let hf := (joukowski_hasStrictDerivAt h0).hasStrictFDerivAt_equiv hd
  exact ⟨hf.toOpenPartialHomeomorph joukowski, hf.mem_toOpenPartialHomeomorph_source,
    hf.toOpenPartialHomeomorph_coe.symm⟩

/-- Near `0` the Joukowski map is injective: `z + z⁻¹ = w + w⁻¹` forces `z = w` or `z w = 1`. -/
theorem joukowski_injective_of_norm_lt_one {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) (hz1 : ‖z‖ < 1)
    (hw1 : ‖w‖ < 1) (h : joukowski z = joukowski w) : z = w := by
  by_contra hne
  have h' : (z - w) * (z * w - 1) = 0 := by
    have : (z - w) * (z * w - 1) = z * w * (joukowski z - joukowski w) := by
      unfold joukowski; field_simp; ring
    rw [this, h, sub_self, mul_zero]
  rcases mul_eq_zero.1 h' with h'' | h''
  · exact hne (sub_eq_zero.1 h'')
  · have hn : ‖z * w‖ < 1 := by
      rw [norm_mul]
      nlinarith [norm_nonneg z, norm_nonneg w]
    rw [sub_eq_zero.1 h'', norm_one] at hn
    exact lt_irrefl _ hn

/-- `‖z + z⁻¹‖ ≥ ‖z‖⁻¹ − ‖z‖`: the Joukowski map is unbounded at `0`. -/
theorem norm_joukowski_ge (z : ℂ) : ‖z‖⁻¹ - ‖z‖ ≤ ‖joukowski z‖ := by
  have := norm_sub_le (joukowski z) z
  have h : joukowski z - z = z⁻¹ := by simp [joukowski]
  rw [h, norm_inv] at this
  linarith

/-- The Joukowski map is continuous off `0`. -/
theorem continuousAt_joukowski {w : ℂ} (hw : w ≠ 0) : ContinuousAt joukowski w :=
  continuousAt_id.add (continuousAt_inv₀ hw)

variable {G : Type*} [Group G] [MulAction G ℂ] [ContinuousConstSMul G ℂ] [IsRigidAction G ℂ]

variable (G) in
/-- The singular `(G,ℂ)`-structure on `ℂ` pulled back by the Joukowski map on `ℂ ∖ {0, ±1}`. -/
abbrev joukowskiStructure : SingularGXStructure G ℂ ℂ :=
  devStructure (G := G) isPortly_joukowskiReg isLocalHomeomorphOn_joukowski

/-- At every regular point, a chart of the maximal atlas which is the Joukowski map itself. -/
theorem exists_joukowskiChart {p : ℂ} (hp : p ∈ joukowskiReg) :
    ∃ e ∈ maximalAEAtlas G (devAtlas G joukowski joukowskiReg), p ∈ e.source ∧
      (e : ℂ → ℂ) = joukowski := by
  obtain ⟨ψ, hpψ, hDψ⟩ := isLocalHomeomorphOn_joukowski p hp
  refine ⟨ψ.restrOpen _ isPortly_joukowskiReg.isOpen,
    (isAEAtlas_devAtlas isPortly_joukowskiReg isLocalHomeomorphOn_joukowski).subset_maximalAEAtlas
      ⟨inter_subset_right, fun _ _ => ⟨1, Eventually.of_forall fun y => ?_⟩⟩, ⟨hpψ, hp⟩, ?_⟩
  · rw [one_smul, hDψ]; rfl
  · rw [hDψ]; rfl

/-- For `G` trivial, every chart of the Joukowski structure is the Joukowski map on the regular
set. -/
theorem joukowski_chart_eq [Subsingleton G] {e : OpenPartialHomeomorph ℂ ℂ}
    (he : e ∈ maximalAEAtlas G (devAtlas G joukowski joukowskiReg)) {y : ℂ}
    (hy : y ∈ e.source) (hyP : y ∈ joukowskiReg) : e y = joukowski y := by
  have hB := (isAEAtlas_devAtlas (G := G) isPortly_joukowskiReg
    isLocalHomeomorphOn_joukowski).isMaximalAEAtlas_maximalAEAtlas
  obtain ⟨e', he', hye', he'D⟩ := exists_joukowskiChart (G := G) hyP
  obtain ⟨g, hg⟩ := hB.1.1.eventually_smul_eq he' he hye' hy
  rw [hg.self_of_nhds, Subsingleton.elim g 1, one_smul, he'D]


/-- The regular locus of the Joukowski structure is `ℂ ∖ {0, ±1}`: at `0` a chart would agree with
the unbounded `z + z⁻¹` on a punctured neighbourhood; at `±1` it would identify `z` and `z⁻¹`. -/
theorem support_joukowskiStructure [Subsingleton G] :
    support (maximalAEAtlas G (devAtlas G joukowski joukowskiReg)) = joukowskiReg := by
  refine Subset.antisymm (fun x hx => ?_)
    (subset_support_devStructure isPortly_joukowskiReg isLocalHomeomorphOn_joukowski)
  by_contra hxP
  obtain ⟨e, he, hxe⟩ := mem_support.1 hx
  have hx' : x = 0 ∨ x = 1 ∨ x = -1 := by
    simp only [joukowskiReg, mem_compl_iff, not_not, mem_insert_iff, mem_singleton_iff] at hxP
    exact hxP
  have hev : ∀ᶠ y in 𝓝 x, y ∈ e.source := e.open_source.mem_nhds hxe
  rcases hx' with rfl | hx1
  · have h1 : ∀ᶠ y in 𝓝 (0 : ℂ), ‖e y - e 0‖ < 1 := by
      have := (e.continuousAt hxe).tendsto
      exact (this.eventually (Metric.ball_mem_nhds (e 0) one_pos)).mono fun y hy => by
        rwa [dist_eq_norm] at hy
    have hT : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] 0) (𝓝 0) := by
      have := Complex.continuous_ofReal.tendsto 0
      rw [Complex.ofReal_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    set K := ‖e 0‖
    have hc : (0 : ℝ) < min 1 (1 / (K + 2)) := lt_min one_pos (by positivity)
    obtain ⟨t, ⟨hts, ht1⟩, ht⟩ := ((hT.eventually (hev.and h1)).and
      (Ioo_mem_nhdsGT hc)).exists
    have ht0 : 0 < t := ht.1
    have htlt1 : t < 1 := ht.2.trans_le (min_le_left _ _)
    have htK : t < 1 / (K + 2) := ht.2.trans_le (min_le_right _ _)
    have hnt : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_of_nonneg ht0.le]
    have hP : (t : ℂ) ∈ joukowskiReg := mem_joukowskiReg_of_norm (by rw [hnt]; exact ht0.ne')
      (by rw [hnt]; exact htlt1.ne)
    have heq := joukowski_chart_eq he hts hP
    have hge := norm_joukowski_ge (t : ℂ)
    rw [hnt] at hge
    have hinv : K + 2 < t⁻¹ := by
      rw [lt_inv_comm₀ (by positivity) ht0]; rwa [one_div] at htK
    have hle : ‖e t‖ ≤ K + ‖e t - e 0‖ := by
      have := norm_add_le (e 0) (e t - e 0)
      rwa [add_sub_cancel] at this
    have hJ : ‖joukowski t‖ < K + 1 := by rw [← heq]; linarith
    linarith
  · have hxx : x⁻¹ = x := by rcases hx1 with rfl | rfl <;> norm_num
    have hnx : ‖x‖ = 1 := by rcases hx1 with rfl | rfl <;> simp
    have hx0 : x ≠ 0 := by intro h; rw [h, norm_zero] at hnx; exact zero_ne_one hnx
    have hcz : Continuous fun t : ℝ => x * (1 + (t : ℂ)) := by fun_prop
    have hTz : Tendsto (fun t : ℝ => x * (1 + (t : ℂ))) (𝓝[>] 0) (𝓝 x) := by
      have := hcz.tendsto 0
      simp only [Complex.ofReal_zero, add_zero, mul_one] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hTw : Tendsto (fun t : ℝ => (x * (1 + (t : ℂ)))⁻¹) (𝓝[>] 0) (𝓝 x) := by
      have := hTz.inv₀ hx0
      rwa [hxx] at this
    obtain ⟨t, ⟨hzs, hws⟩, ht⟩ := ((hTz.eventually hev).and (hTw.eventually hev) |>.and
      (Ioo_mem_nhdsGT one_pos)).exists
    have ht0 : 0 < t := ht.1
    set z := x * (1 + (t : ℂ))
    have hnz : ‖z‖ = 1 + t := by
      have h1t : (1 + (t : ℂ)) = ((1 + t : ℝ) : ℂ) := by push_cast; ring
      rw [norm_mul, hnx, one_mul, h1t, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    have hzP : z ∈ joukowskiReg := mem_joukowskiReg_of_norm (by rw [hnz]; linarith)
      (by rw [hnz]; linarith)
    have hwP : z⁻¹ ∈ joukowskiReg := inv_mem_joukowskiReg hzP
    have h := e.injOn hzs hws (by
      rw [joukowski_chart_eq he hzs hzP, joukowski_chart_eq he hws hwP, joukowski_inv])
    have hn := congrArg norm h
    rw [norm_inv, hnz] at hn
    have : (1 + t) * (1 + t) = 1 := by
      calc (1 + t) * (1 + t) = (1 + t)⁻¹ * (1 + t) := by rw [← hn]
        _ = 1 := inv_mul_cancel₀ (by linarith)
    nlinarith

/-- **Rigidity at `0`** of the Joukowski structure (`G` trivial): two a.e. `(G,ℂ)`-morphisms from a
preconnected singular manifold into it, one of which takes the value `0`, are equal. Read in
charts both are `z + z⁻¹`-lifts of the same chart on a portly set, so `D ∘ f₁ = D ∘ f₂` there;
`D` is unbounded at `0`, so `f₁` takes the value `0` at the same point, and `D` is injective on the
punctured unit disc, so `f₁ = f₂` near it; the identity theorem
(`IsAEMorphism.eq_of_eqOn`) concludes. -/
theorem joukowski_eq_of_isAEMorphism [Subsingleton G] {Y : Type*} [TopologicalSpace Y]
    [PreconnectedSpace Y] [SingularGXStructure G ℂ Y] :
    letI : SingularGXStructure G ℂ ℂ := joukowskiStructure G
    ∀ {f₁ f₂ : Y → ℂ}, IsAEMorphism G ℂ f₁ → IsAEMorphism G ℂ f₂ → ∀ y₀, f₂ y₀ = 0 →
      f₁ = f₂ := by
  letI : SingularGXStructure G ℂ ℂ := joukowskiStructure G
  intro f₁ f₂ h₁ h₂ y₀ hy₀
  have hBm := isMaximalAEAtlas_aeAtlas G ℂ ℂ
  have hsupp : support (aeAtlas G ℂ ℂ) = joukowskiReg := support_joukowskiStructure
  obtain ⟨-, R₁, hR₁, r₁⟩ := (isAEMorphismOf_iff hBm.1).1 h₁
  obtain ⟨-, R₂, hR₂, r₂⟩ := (isAEMorphismOf_iff hBm.1).1 h₂
  have hR := hR₁.inter hR₂
  have hmaps₁ : ∀ y ∈ R₁, f₁ y ∈ joukowskiReg := fun y hy => hsupp ▸ r₁.mapsTo hy
  have hmaps₂ : ∀ y ∈ R₂, f₂ y ∈ joukowskiReg := fun y hy => hsupp ▸ r₂.mapsTo hy
  have key : ∀ y ∈ R₁ ∩ R₂, joukowski (f₁ y) = joukowski (f₂ y) := by
    rintro y ⟨hy₁, hy₂⟩
    obtain ⟨c, hc, hyc⟩ := mem_support.1 (r₁.subset_support hy₁)
    obtain ⟨e₁, he₁, hye₁, he₁D⟩ := exists_joukowskiChart (G := G) (hmaps₁ y hy₁)
    obtain ⟨e₂, he₂, hye₂, he₂D⟩ := exists_joukowskiChart (G := G) (hmaps₂ y hy₂)
    obtain ⟨g₁, hg₁⟩ := r₁.exists_smul_eq y hy₁ c hc e₁ he₁ hyc hye₁
    obtain ⟨g₂, hg₂⟩ := r₂.exists_smul_eq y hy₂ c hc e₂ he₂ hyc hye₂
    have k₁ := hg₁.self_of_nhds
    have k₂ := hg₂.self_of_nhds
    rw [Subsingleton.elim g₁ 1, one_smul, he₁D] at k₁
    rw [Subsingleton.elim g₂ 1, one_smul, he₂D] at k₂
    rw [k₁, k₂]
  -- a point of the dense `R₁ ∩ R₂` in every neighbourhood of `y₀`
  have hdense : ∀ U ∈ 𝓝 y₀, ∃ y ∈ U, y ∈ R₁ ∩ R₂ := fun U hU => by
    obtain ⟨V, hVU, hVo, hy₀V⟩ := mem_nhds_iff.1 hU
    obtain ⟨y, hyV, hyR⟩ := hR.dense.inter_open_nonempty V hVo ⟨y₀, hy₀V⟩
    exact ⟨y, hVU hyV, hyR⟩
  have hf₁ : f₁ y₀ = 0 := by
    by_contra hw
    set K := ‖joukowski (f₁ y₀)‖
    have hc : (0 : ℝ) < min 1 (1 / (K + 2)) := lt_min one_pos (by positivity)
    have hJ : ∀ᶠ y in 𝓝 y₀, ‖joukowski (f₁ y) - joukowski (f₁ y₀)‖ < 1 := by
      have := ((continuousAt_joukowski hw).comp h₁.continuous.continuousAt).tendsto
      exact (this.eventually (Metric.ball_mem_nhds _ one_pos)).mono fun y hy => by
        rwa [dist_eq_norm] at hy
    have hS : ∀ᶠ y in 𝓝 y₀, ‖f₂ y‖ < min 1 (1 / (K + 2)) := by
      have := h₂.continuous.continuousAt (x := y₀) |>.tendsto
      rw [hy₀] at this
      exact (this.eventually (Metric.ball_mem_nhds _ hc)).mono fun y hy => by
        rwa [dist_zero_right] at hy
    obtain ⟨y, ⟨hy1, hy2⟩, hyR⟩ := hdense _ (hJ.and hS)
    have hne : f₂ y ≠ 0 := (mem_joukowskiReg.1 (hmaps₂ y hyR.2)).1
    have hu0 : 0 < ‖f₂ y‖ := norm_pos_iff.2 hne
    have hu1 : ‖f₂ y‖ < 1 := hy2.trans_le (min_le_left _ _)
    have huK : ‖f₂ y‖ < 1 / (K + 2) := hy2.trans_le (min_le_right _ _)
    have hinv : K + 2 < ‖f₂ y‖⁻¹ := by
      rw [lt_inv_comm₀ (by positivity) hu0]; rwa [one_div] at huK
    have hge := norm_joukowski_ge (f₂ y)
    have hle : ‖joukowski (f₁ y)‖ ≤ K + ‖joukowski (f₁ y) - joukowski (f₁ y₀)‖ := by
      have := norm_add_le (joukowski (f₁ y₀)) (joukowski (f₁ y) - joukowski (f₁ y₀))
      rwa [add_sub_cancel] at this
    have hJ' : ‖joukowski (f₂ y)‖ < K + 1 := by rw [← key y hyR]; linarith
    linarith
  set W := (f₁ ⁻¹' Metric.ball 0 1 ∩ f₂ ⁻¹' Metric.ball 0 1) ∩ (R₁ ∩ R₂)
  have hWo : IsOpen W := ((Metric.isOpen_ball.preimage h₁.continuous).inter
    (Metric.isOpen_ball.preimage h₂.continuous)).inter hR.isOpen
  have hWne : W.Nonempty := by
    have hU : f₁ ⁻¹' Metric.ball 0 1 ∩ f₂ ⁻¹' Metric.ball 0 1 ∈ 𝓝 y₀ :=
      inter_mem ((Metric.isOpen_ball.preimage h₁.continuous).mem_nhds
        (by simp [hf₁])) ((Metric.isOpen_ball.preimage h₂.continuous).mem_nhds (by simp [hy₀]))
    obtain ⟨y, hyU, hyR⟩ := hdense _ hU
    exact ⟨y, hyU, hyR⟩
  refine h₁.eq_of_eqOn h₂ hWo hWne fun y hy => ?_
  obtain ⟨⟨hb₁, hb₂⟩, hyR⟩ := hy
  rw [mem_preimage, mem_ball_zero_iff] at hb₁ hb₂
  exact joukowski_injective_of_norm_lt_one (mem_joukowskiReg.1 (hmaps₁ y hyR.1)).1
    (mem_joukowskiReg.1 (hmaps₂ y hyR.2)).1 hb₁ hb₂ (key y hyR)

/-- The singular locus of the Joukowski structure is `{0, 1, -1}`. -/
theorem sing_joukowskiStructure [Subsingleton G] :
    letI : SingularGXStructure G ℂ ℂ := joukowskiStructure G
    Sing G ℂ ℂ = {0, 1, -1} := by
  letI : SingularGXStructure G ℂ ℂ := joukowskiStructure G
  show (support (maximalAEAtlas G (devAtlas G joukowski joukowskiReg)))ᶜ = _
  rw [support_joukowskiStructure, joukowskiReg, compl_compl]

/-- `B(s, 1/2)` misses `0` when `‖s‖ = 1`. -/
theorem ne_zero_of_mem_ball_unit {s z : ℂ} (hs : ‖s‖ = 1) (hz : z ∈ Metric.ball s (1 / 2)) :
    z ≠ 0 := by
  rintro rfl
  rw [Metric.mem_ball, dist_zero_left, hs] at hz
  norm_num at hz

/-- The local rotation of `cex:start_singular_manifold_homeomorphic` in the Joukowski witness: at
`s = ±1`, `z ↦ z⁻¹` maps the disc `B(s, 1/2)` onto `{z ≠ 0 | z⁻¹ ∈ B(s, 1/2)}`. -/
def joukowskiFlip {s : ℂ} (hs : ‖s‖ = 1) :
    (⟨Metric.ball s (1 / 2), Metric.isOpen_ball⟩ : Opens ℂ) ≃ₜ
      (⟨{0}ᶜ ∩ (fun z : ℂ => z⁻¹) ⁻¹' Metric.ball s (1 / 2),
        continuousOn_inv₀.isOpen_inter_preimage isOpen_compl_singleton Metric.isOpen_ball⟩ :
        Opens ℂ) where
  toFun z := ⟨(z : ℂ)⁻¹, inv_ne_zero (ne_zero_of_mem_ball_unit hs z.2), by
    show ((z : ℂ)⁻¹)⁻¹ ∈ Metric.ball s (1 / 2)
    rw [inv_inv]; exact z.2⟩
  invFun w := ⟨(w : ℂ)⁻¹, w.2.2⟩
  left_inv z := Subtype.ext (inv_inv (z : ℂ))
  right_inv w := Subtype.ext (inv_inv (w : ℂ))
  continuous_toFun := continuous_induced_rng.2
    (continuous_subtype_val.inv₀ fun z => ne_zero_of_mem_ball_unit hs z.2)
  continuous_invFun := continuous_induced_rng.2
    (continuous_subtype_val.inv₀ fun w => w.2.1)

/-- The flip `z ↦ z⁻¹` of `B(±1, 1/2)` is an a.e. `(G,ℂ)`-morphism (`z + z⁻¹` is invariant). -/
theorem isAEMorphism_joukowskiFlip [Subsingleton G] {s : ℂ} (hs : ‖s‖ = 1) :
    letI : SingularGXStructure G ℂ ℂ := joukowskiStructure G
    IsAEMorphism G ℂ (joukowskiFlip hs : _ → _) := by
  letI : SingularGXStructure G ℂ ℂ := joukowskiStructure G
  set U₁ : Opens ℂ := ⟨Metric.ball s (1 / 2), Metric.isOpen_ball⟩
  apply isAEMorphism_of_val_comp
  have hBm := isMaximalAEAtlas_aeAtlas G ℂ ℂ
  have hBU := isMaximalAEAtlas_aeAtlas G ℂ U₁
  have hsupp : support (aeAtlas G ℂ ℂ) = joukowskiReg := support_joukowskiStructure
  obtain ⟨-, R₀, hR₀, r₀⟩ := (isAEMorphismOf_iff hBm.1).1 (isAEMorphism_opensSingular_val (G := G) (X := ℂ) U₁)
  have hcont : Continuous (Subtype.val ∘ (joukowskiFlip hs : U₁ → _)) :=
    continuous_subtype_val.comp (joukowskiFlip hs).continuous
  refine (isAEMorphismOf_iff hBm.1).2 ⟨hcont, R₀, hR₀, IsRegularOn.of_exists hBU.1.1 hBm.1.1
    hR₀.isOpen r₀.subset_support (fun x hx => ?_) hcont.continuousOn fun x hx => ?_⟩
  · have hp : (x : ℂ) ∈ joukowskiReg := hsupp ▸ r₀.mapsTo hx
    rw [hsupp]; exact inv_mem_joukowskiReg hp
  · have hp : (x : ℂ) ∈ joukowskiReg := hsupp ▸ r₀.mapsTo hx
    obtain ⟨c, hc, hxc⟩ := mem_support.1 (r₀.subset_support hx)
    obtain ⟨e, he, hxe, heD⟩ := exists_joukowskiChart (G := G) hp
    obtain ⟨e', he', hxe', he'D⟩ := exists_joukowskiChart (G := G) (inv_mem_joukowskiReg hp)
    obtain ⟨g, hg⟩ := r₀.exists_smul_eq x hx c hc e he hxc hxe
    refine ⟨c, hc, e', he', hxc, hxe', 1, hg.mono fun y hy => ?_⟩
    rw [Subsingleton.elim g 1, heD, one_smul] at hy
    rw [he'D, one_smul, ← hy]
    exact joukowski_inv (y : ℂ)

/-- The facts of `cex:start_singular_manifold_homeomorphic` hold on the Joukowski structure at
`O = 0`, every field exercised: `0` rigid, `±1` singular with the non-extendable flips. -/
theorem suspensionCexFacts_joukowski [Subsingleton G] :
    letI : SingularGXStructure G ℂ ℂ := joukowskiStructure G
    SuspensionCexFacts G ℂ ℂ 0 := by
  letI : SingularGXStructure G ℂ ℂ := joukowskiStructure G
  have hsing : Sing G ℂ ℂ = {0, 1, -1} := sing_joukowskiStructure
  refine ⟨inferInstance, by rw [hsing]; exact mem_insert _ _,
    ⟨1, by rw [hsing]; simp, one_ne_zero⟩, fun U₁ U₂ hU₁ _ φ hφ hO x => ?_,
    fun s hs hs0 => ?_⟩
  · haveI : PreconnectedSpace U₁ := Subtype.preconnectedSpace hU₁.isPreconnected
    have h₁ : IsAEMorphism G ℂ (Subtype.val ∘ (φ : U₁ → U₂)) :=
      (isAEMorphism_opensSingular_val U₂).comp hφ
    exact congrFun (joukowski_eq_of_isAEMorphism h₁ (isAEMorphism_opensSingular_val U₁)
      ⟨0, hO⟩ rfl) x
  · have hs' : s = 1 ∨ s = -1 := by
      rw [hsing] at hs
      rcases hs with h | h
      · exact absurd h hs0
      · exact h
    have hsn : ‖s‖ = 1 := by rcases hs' with rfl | rfl <;> simp
    have hs0' : s ≠ 0 := by intro h; rw [h, norm_zero] at hsn; exact zero_ne_one hsn
    refine ⟨_, _, (convex_ball s (1 / 2)).isConnected (Metric.nonempty_ball.2 (by norm_num)), ?_,
      Metric.mem_ball_self (by norm_num), joukowskiFlip hsn, isAEMorphism_joukowskiFlip hsn, ?_⟩
    · have heq : (({0}ᶜ ∩ (fun z : ℂ => z⁻¹) ⁻¹' Metric.ball s (1 / 2) : Set ℂ)) =
          (fun z : ℂ => z⁻¹) '' Metric.ball s (1 / 2) := by
        ext z
        refine ⟨fun hz => ⟨z⁻¹, hz.2, inv_inv z⟩, ?_⟩
        rintro ⟨w, hw, rfl⟩
        exact ⟨inv_ne_zero (ne_zero_of_mem_ball_unit hsn hw), by simpa using hw⟩
      show IsConnected ({0}ᶜ ∩ (fun z : ℂ => z⁻¹) ⁻¹' Metric.ball s (1 / 2))
      rw [heq]
      exact ((convex_ball s (1 / 2)).isConnected (Metric.nonempty_ball.2 (by norm_num))).image _
        (continuousOn_inv₀.mono fun z hz => ne_zero_of_mem_ball_unit hsn hz)
    · rintro ⟨ψ, hψ, hψφ⟩
      have hψ' : IsAEMorphism G ℂ (ψ : ℂ → ℂ) := mem_singularAut.1 hψ
      have hid := joukowski_eq_of_isAEMorphism hψ' (isAEMorphism_id (G := G) (X := ℂ)) 0 rfl
      have hmem : s * (5 / 4) ∈ Metric.ball s (1 / 2) := by
        rw [Metric.mem_ball, dist_eq_norm,
          show s * (5 / 4) - s = s * (1 / 4) by ring, norm_mul, hsn]
        norm_num
      have h := hψφ ⟨s * (5 / 4), hmem⟩
      rw [hid] at h
      have h' : s * (5 / 4) = (s * (5 / 4))⁻¹ := h
      have h'' : s * (5 / 4) * (s * (5 / 4)) = 1 := by
        have := mul_inv_cancel₀ (mul_ne_zero hs0' (by norm_num : (5 / 4 : ℂ) ≠ 0))
        rwa [← h'] at this
      have hss : s * s = 1 := by rcases hs' with rfl | rfl <;> norm_num
      have : s * s * (25 / 16) = 1 := by rw [← h'']; ring
      rw [hss] at this
      norm_num at this

/-- The non-vacuity witness of the named facts (DEC-69, the `kb/0012` pattern), with every field
exercised: some connected singular `(G,X)`-manifold (`G` trivial, `X = M = ℂ`, the Joukowski
structure, `sing = {0, 1, -1}`) carries `SuspensionCexFacts` at `O = 0`; `rot` is non-vacuous
there (the local flips `z ↦ z⁻¹` at `±1`, which no automorphism extends). -/
theorem exists_suspensionCexFacts :
    ∃ (G : Type) (_ : Group G) (_ : MulAction G ℂ) (_ : ContinuousConstSMul G ℂ)
      (_ : IsRigidAction G ℂ) (_ : SingularGXStructure G ℂ ℂ),
      Sing G ℂ ℂ = {0, 1, -1} ∧ SuspensionCexFacts G ℂ ℂ 0 := by
  let G := (⊥ : Subgroup (Equiv.Perm ℂ))
  haveI : Subsingleton G := inferInstance
  haveI hc : ContinuousConstSMul G ℂ :=
    ⟨fun g => by rw [Subsingleton.elim g 1]; simp only [one_smul]; exact continuous_id⟩
  haveI hr : IsRigidAction G ℂ :=
    ⟨fun {g h} _ _ _ _ _ => by rw [Subsingleton.elim g h]⟩
  exact ⟨G, inferInstance, inferInstance, hc, hr, joukowskiStructure G,
    sing_joukowskiStructure, suspensionCexFacts_joukowski⟩

/-- **Disclosure** (audit round 4, SCOPE (c)): the named `TroyanovSuspensionTheorem` is not tied to
the angles — for a trivial group acting on `ℂ` it holds outright, for every `θ`, by the Joukowski
witness. Its content is the paper's instance `(SO(4), 𝕊³)`, which the library cannot state; over
a general `(G,X)` it asserts only the existence of a manifold carrying the facts. -/
theorem troyanovSuspensionTheorem_of_subsingleton {G : Type*} [Group G] [MulAction G ℂ]
    [ContinuousConstSMul G ℂ] [IsRigidAction G ℂ] [Subsingleton G] :
    TroyanovSuspensionTheorem G ℂ := fun _ _ _ =>
  ⟨ℂ, inferInstance, inferInstance, joukowskiStructure G, 0, suspensionCexFacts_joukowski⟩

end Joukowski

/-! ### `rem:theorem_theo_local_tame` -/

section TameModels

variable {G : Type*} {X : Type*} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
  [FaithfulSMul G X]
  {A : Type*} {Xα : A → Type u} [∀ a, TopologicalSpace (Xα a)] [∀ a, T2Space (Xα a)]
  [∀ a, LocPathConnectedSpace (Xα a)] [∀ a, FirstCountableTopology (Xα a)]
  [∀ a, SingularGXStructure G X (Xα a)] {S : ∀ a, Set (Xα a)}
  {M : Type v} [TopologicalSpace M] [T2Space M] [LocPathConnectedSpace M]
  [FirstCountableTopology M] [ConnectedSpace M] [SingularGXStructure G X M]

/-- The domain of an `X_α`-chart whose model is tame is tame (`cor:open_subsets_tame_singular`,
then `lem:embedding_tame` along the chart). -/
theorem XAChart.isTame_U (hX : IsLocallyUnloopable X) {a : A} {x : M}
    (c : XAChart G X Xα S a x) [ConnectedSpace (Xα a)] (ha : IsTame G X (Xα a)) :
    IsTame G X c.U := by
  haveI : ConnectedSpace c.V := isConnected_iff_connectedSpace.1 c.isConnected_V
  have hV := isTame_opens hX ha c.V
  haveI : ConnectedSpace c.U := c.φ.symm.surjective.connectedSpace c.φ.symm.continuous
  exact isTame_of_isAEMorphism hX c.isAEMorphism hV

/-- `rem:theorem_theo_local_tame` (`RamcovGX.tex:1924`), the direction "models tame ⇒ tame", in
its strong form: an `X_A`-manifold with an `X_A`-atlas all of whose models are tame is tame
(`theo:local_tame`: every point lies in a chart domain, tame by `XAChart.isTame_U`). -/
theorem isTame_of_isXAAtlas (hX : IsLocallyUnloopable X)
    {𝒜 : Set (Σ a : A, Σ x : M, XAChart G X Xα S a x)} (h𝒜 : IsXAAtlas G X Xα S M 𝒜)
    (hcon : ∀ c ∈ 𝒜, ConnectedSpace (Xα c.1)) (htame : ∀ c ∈ 𝒜, IsTame G X (Xα c.1)) :
    IsTame G X M := by
  refine isTame_of_isLocallyTame hX fun y => ?_
  obtain ⟨⟨a, x, c⟩, hc, hy⟩ := h𝒜 y
  haveI := hcon _ hc
  exact ⟨c.U, hy, c.isTame_U hX (htame _ hc)⟩

/-- `rem:theorem_theo_local_tame`: an `X_A`-manifold over a family of tame (connected) models is
tame (only the atlas is used). -/
theorem isTame_of_isXAManifoldPrinted (hX : IsLocallyUnloopable X) [∀ a, ConnectedSpace (Xα a)]
    (htame : ∀ a, IsTame G X (Xα a)) (hM : IsXAManifoldPrinted G X Xα S M) : IsTame G X M := by
  obtain ⟨𝒜, h𝒜⟩ := hM
  exact isTame_of_isXAAtlas hX h𝒜 (fun c _ => inferInstance) (fun c _ => htame c.1)

/-- `rem:theorem_theo_local_tame`: an `X_A`-manifold (DEC-67 (e)) over a family of tame (connected)
models is tame. -/
theorem isTame_of_isXAManifold (hX : IsLocallyUnloopable X) [∀ a, ConnectedSpace (Xα a)]
    (htame : ∀ a, IsTame G X (Xα a)) (hM : IsXAManifold G X Xα S M) : IsTame G X M :=
  isTame_of_isXAManifoldPrinted hX htame hM.exists_atlas

variable (G X Xα S) in
/-- **`rem:theorem_theo_local_tame`** (`RamcovGX.tex:1924`), as ruled by DEC-80 (b) — the GLOBAL
equivalence — for `X_A`-manifolds as printed (l.1913, an `X_A`-atlas): over a family of (connected)
models, every `X_A`-manifold is tame iff every model is tame. No further hypothesis ("if":
`theo:local_tame` along the atlas; "only if": each model is an `X_A`-manifold). -/
theorem forall_isTame_iff_printed (hX : IsLocallyUnloopable X) [∀ a, ConnectedSpace (Xα a)]
    (hne : ∀ a, (S a).Nonempty) :
    (∀ (N : Type u) [TopologicalSpace N] [T2Space N] [LocPathConnectedSpace N]
        [FirstCountableTopology N] [ConnectedSpace N] [SingularGXStructure G X N],
        IsXAManifoldPrinted G X Xα S N → IsTame G X N) ↔ ∀ a, IsTame G X (Xα a) :=
  ⟨fun h a => h (Xα a) (isXAManifoldPrinted_model hne a), fun h _ _ _ _ _ _ _ hN =>
    isTame_of_isXAManifoldPrinted hX h hN⟩

variable (G X Xα S) in
/-- **`rem:theorem_theo_local_tame`** (`RamcovGX.tex:1924`), as ruled by DEC-80 (b) — the GLOBAL
equivalence — for `X_A`-manifolds as ruled by DEC-67 (e): over a family of (connected) models which
are themselves `X_A`-manifolds — every singular point of a model has a type (`htype`), the paper's
presumption at l.2086, used by "only if" only (`isXAManifold_model`) — every `X_A`-manifold is tame
iff every model is tame. -/
theorem forall_isTame_iff (hX : IsLocallyUnloopable X) [∀ a, ConnectedSpace (Xα a)]
    (hne : ∀ a, (S a).Nonempty)
    (htype : ∀ a, ∀ y ∈ Sing G X (Xα a), ∃ b, HasXAType (G := G) (X := X) (Xα := Xα) (S := S) b y) :
    (∀ (N : Type u) [TopologicalSpace N] [T2Space N] [LocPathConnectedSpace N]
        [FirstCountableTopology N] [ConnectedSpace N] [SingularGXStructure G X N],
        IsXAManifold G X Xα S N → IsTame G X N) ↔ ∀ a, IsTame G X (Xα a) :=
  ⟨fun h a => h (Xα a) (isXAManifold_model hne a (htype a)), fun h _ _ _ _ _ _ _ hN =>
    isTame_of_isXAManifold hX h hN⟩

end TameModels

/-! ### `def:singular_manifold_virtually_tame`, `def:singular_manifold_locally_galoisian` -/

section VirtTame

variable (G : Type*) (X : Type*) [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
  (M : Type u) [TopologicalSpace M] [SingularGXStructure G X M]

/-- The natural (weak) topology of `\widetilde M` (named, so that statements quantifying over a
second topology `T` — a local instance — can refer to it). -/
abbrev weakTopMax (y₀ : ((Sing G X M)ᶜ : Set M)) :
    TopologicalSpace (MaxBranchedCover (Sing G X M) y₀) :=
  SpreadEnd.instTopologicalSpace

/-- `def:singular_manifold_virtually_tame` (B): `D` induces a `(G,X)`-morphism on the lift
`p⁻¹(reg M) = reg(\widetilde M)` of `reg(M)`, for the natural topology and the structure `p^*B` —
`D` restricts to a developing map of `reg(\widetilde M)`. -/
def IsRegDevelopingOnReg (y₀ : ((Sing G X M)ᶜ : Set M))
    (D : MaxBranchedCover (Sing G X M) y₀ → X) : Prop :=
  IsRegularOn G (aePullback G (aeAtlas G X M)
    (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M)) (gxModelAtlas G X) D
    ((SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) ⁻¹' Reg G X M)

/-- The elements of `Γ(\widetilde M/M)`, as maps (homeomorphisms for the natural topology). -/
def deckMapsMax (y₀ : ((Sing G X M)ᶜ : Set M)) :
    Set (MaxBranchedCover (Sing G X M) y₀ → MaxBranchedCover (Sing G X M) y₀) :=
  {f | ∃ γ ∈ deckGroup (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M), ⇑γ = f}

/-- The elements of `Aut(\widetilde M)`, as maps: homeomorphisms of `\widetilde M` (natural
topology) which are a.e. `(G,X)`-morphisms for the structure `p^*B`. -/
def aeAutMapsMax (y₀ : ((Sing G X M)ᶜ : Set M)) :
    Set (MaxBranchedCover (Sing G X M) y₀ → MaxBranchedCover (Sing G X M) y₀) :=
  {f | ∃ φ : MaxBranchedCover (Sing G X M) y₀ ≃ₜ MaxBranchedCover (Sing G X M) y₀, ⇑φ = f ∧
    IsAEMorphismOf G (aePullback G (aeAtlas G X M) SpreadEnd.base)
      (aePullback G (aeAtlas G X M) SpreadEnd.base) φ}

/-- **`def:singular_manifold_virtually_tame`** (`RamcovGX.tex:1960`): a *tamifying topology* on
`\widetilde M = \widetilde M^{sing M}` (based at `y₀`) is a first countable, locally
path-connected (strong) topology `T`, finer ("thinner") than the natural (weak) one, such that
(A) the quotient topology `T` induces on `M` is the natural one; (B) the developing map
`reg(\widetilde M) → X` has a `T`-continuous extension (`IsRegDevelopingOnReg`); (C) the elements
of `Γ(\widetilde M/M)` are `T`-continuous; (D) the lift `p⁻¹(reg M)` of `reg(M)` is `T`-portly. -/
structure IsTamifyingTopology (y₀ : ((Sing G X M)ᶜ : Set M))
    (T : TopologicalSpace (MaxBranchedCover (Sing G X M) y₀)) : Prop where
  le_natural : T ≤ weakTopMax G X M y₀
  firstCountable : @FirstCountableTopology _ T
  locPathConnected : @LocPathConnectedSpace _ T
  /-- (A) -/
  coinduced_eq : TopologicalSpace.coinduced
    (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) T = ‹TopologicalSpace M›
  /-- (B) -/
  exists_extension : ∃ D : MaxBranchedCover (Sing G X M) y₀ → X,
    Continuous[T, ‹TopologicalSpace X›] D ∧ IsRegDevelopingOnReg G X M y₀ D
  /-- (C) -/
  continuous_deck : ∀ f ∈ deckMapsMax G X M y₀, Continuous[T, T] f
  /-- (D) -/
  isPortly : @IsPortly _ T ((SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) ⁻¹' Reg G X M)

/-- **`def:singular_manifold_virtually_tame`**: `M` is *virtually tame* if `\widetilde M` carries a
tamifying topology. -/
def IsVirtuallyTame : Prop :=
  ∃ (y₀ : ((Sing G X M)ᶜ : Set M)) (T : TopologicalSpace (MaxBranchedCover (Sing G X M) y₀)),
    IsTamifyingTopology G X M y₀ T

/-- **`def:singular_manifold_locally_galoisian`** (`RamcovGX.tex:1969`): `M` is *locally
Galoisian* if for every open `U ⊆ M`, `reg(U)` is semi-locally simply connected in `U`
(`def:semi_locally_simple_connectedness` in its literal form, `GX.IsSLSCInCC`, DEC-55), `U` with
its induced structure. -/
def IsLocallyGaloisian : Prop := ∀ U : Opens M, IsSLSCInCC (Reg G X U)

variable {G X M} [T2Space M] [LocPathConnectedSpace M] [FirstCountableTopology M]
  [ConnectedSpace M] [FaithfulSMul G X]

/-- The natural topology of `\widetilde M` is tamifying iff `\widetilde M` has a developing map:
for the natural topology, (A), (C), (D) and the side conditions always hold, and (B) is a
developing map (`def:developing_map`). -/
theorem isTamifyingTopology_natural_iff (hreg : SemilocallySimplyConnected ((Sing G X M)ᶜ : Set M))
    (y₀ : ((Sing G X M)ᶜ : Set M)) :
    IsTamifyingTopology G X M y₀ inferInstance ↔ ∃ D : MaxBranchedCover (Sing G X M) y₀ → X,
      IsDevelopingMapOf G (aeAtlas G X M) SpreadEnd.base D := by
  set B := aeAtlas G X M
  have hBm : IsMaximalAEAtlas G B := isMaximalAEAtlas_aeAtlas G X M
  have hS₀ : IsSkeletal (Sing G X M) := isSkeletal_sing G X M
  obtain ⟨-, hβbc, hβS, -, hβl, -⟩ := maxBranched_basic hS₀ hreg y₀
  set R : Set (MaxBranchedCover (Sing G X M) y₀) := SpreadEnd.base ⁻¹' Reg G X M with hRdef
  have hRp : IsPortly R := by
    have h := hβbc.isPortly_preimage hS₀
    have he : (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) ⁻¹' (Sing G X M)ᶜ = R := by
      rw [hRdef]; ext w; exact not_not
    exact he ▸ h
  have hAt := aePullback_spec_of_isAELocalHomeomorph hBm.1 hβbc.isSpread.continuous
    (hβbc.isAELocalHomeomorph hBm.1)
  have hordβ : Reg G X M ⊆ ordY (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) :=
    fun y hy => by by_contra hn; exact (hβS hn) hy
  have hRsupp : R ⊆ support (aePullback G B
      (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M)) := fun w hw =>
    hAt.2.mem_support_of_isLocalHomeomorphOn' hAt.1 hBm.1 hw
      (hβbc.ordX_subset_isLocalHomeomorphOn (hordβ hw))
  constructor
  · rintro ⟨-, -, -, -, ⟨D, hDc, hDR⟩, -, -⟩
    exact ⟨D, (isAEMorphismOf_iff (isMaximalAEAtlas_gxModelAtlas (G := G) (X := X)).1).2
      ⟨hDc, R, hRp, hDR⟩⟩
  · rintro ⟨D, hD⟩
    have hDreg := hD.regLocusOf_eq hAt.1.1 (isMaximalAEAtlas_gxModelAtlas (G := G) (X := X)).1
    rw [support_gxModelAtlas, preimage_univ, inter_univ] at hDreg
    have hDR := (isRegularOn_regLocusOf (G := G) _ (gxModelAtlas G X) D).mono
      (by rw [hDreg]; exact hRsupp) hRp.isOpen
    have hopen : IsOpenMap (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) :=
      (spread_connected_image hβbc).1
    exact ⟨le_rfl, inferInstance, hβl,
      ((hopen.isQuotientMap hβbc.isSpread.continuous hβbc.surjective).eq_coinduced).symm,
      ⟨D, hD.continuous, hDR⟩, by rintro _ ⟨γ, -, rfl⟩; exact γ.continuous, hRp⟩

/-- A tame singular `(G,X)`-manifold is virtually tame, the natural topology being tamifying. -/
theorem IsTame.isVirtuallyTame (hX : IsLocallyUnloopable X) (h : IsTame G X M) :
    IsVirtuallyTame G X M := by
  obtain ⟨y₀⟩ := (nonempty_compl_of_isSkeletal (isSkeletal_sing G X M)).to_subtype
  have hreg := semilocallySimplyConnected_compl_of_sing_subset (G := G) hX
    (isClosed_sing G X M) subset_rfl
  exact ⟨y₀, inferInstance, (isTamifyingTopology_natural_iff hreg y₀).2 ((isTame_iff hX y₀).1 h)⟩

/-- `M` is tame iff the natural topology of `\widetilde M` is tamifying. -/
theorem isTame_iff_isTamifyingTopology_natural (hX : IsLocallyUnloopable X)
    (y₀ : ((Sing G X M)ᶜ : Set M)) :
    IsTame G X M ↔ IsTamifyingTopology G X M y₀ inferInstance := by
  have hreg := semilocallySimplyConnected_compl_of_sing_subset (G := G) hX
    (isClosed_sing G X M) subset_rfl
  rw [isTamifyingTopology_natural_iff hreg y₀, isTame_iff hX y₀]

end VirtTame

section TamifyingReg

variable {G : Type*} {X : Type*} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
  {M : Type u} [TopologicalSpace M] [T2Space M] [LocPathConnectedSpace M]
  [FirstCountableTopology M] [ConnectedSpace M] [SingularGXStructure G X M]

/-- The engine of `IsTamifyingTopology.exists_isOpen_subset`, stated on a predicate `P` (the
open sets of the strong topology) so that no second topology is in context. -/
theorem exists_isOpen_subset_of_strongPred
    (hreg : SemilocallySimplyConnected ((Sing G X M)ᶜ : Set M)) {y₀ : ((Sing G X M)ᶜ : Set M)}
    (P : Set (MaxBranchedCover (Sing G X M) y₀) → Prop) (hle : ∀ s, IsOpen s → P s)
    (hinter : ∀ s t, P s → P t → P (s ∩ t))
    (hunion : ∀ s : Deck (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) →
      Set (MaxBranchedCover (Sing G X M) y₀), (∀ i, P (s i)) → P (⋃ i, s i))
    (hdeck : ∀ f ∈ deckMapsMax G X M y₀, ∀ s, P s → P (f ⁻¹' s))
    (hco : ∀ O : Set M, P (SpreadEnd.base ⁻¹' O) → IsOpen O)
    {W : Set (MaxBranchedCover (Sing G X M) y₀)} (hW : P W) {r : MaxBranchedCover (Sing G X M) y₀}
    (hrW : r ∈ W) (hr : r.base ∈ Reg G X M) : ∃ U, IsOpen U ∧ r ∈ U ∧ U ⊆ W := by
  have hS₀ := isSkeletal_sing G X M
  obtain ⟨-, hβbc, hβS, -, -, -⟩ := maxBranched_basic hS₀ hreg y₀
  have hordβ : Reg G X M ⊆ ordY (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) :=
    fun y hy => by by_contra hn; exact (hβS hn) hy
  obtain ⟨e, hre, hpe⟩ := hβbc.ordX_subset_isLocalHomeomorphOn (hordβ hr) r rfl
  have hRo : IsOpen ((SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) ⁻¹' Reg G X M) :=
    (isOpen_reg G X M).preimage hβbc.isSpread.continuous
  set W' := W ∩ (e.source ∩ SpreadEnd.base ⁻¹' Reg G X M)
  have hW' : P W' := hinter _ _ hW (hle _ (e.open_source.inter hRo))
  set O : Set M := SpreadEnd.base '' W'
  have hpre : (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) ⁻¹' O =
      ⋃ γ : Deck (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M),
        ((γ⁻¹ : Deck (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M)) :
          MaxBranchedCover (Sing G X M) y₀ ≃ₜ MaxBranchedCover (Sing G X M) y₀) ⁻¹' W' := by
    ext z
    simp only [mem_preimage, mem_iUnion]
    constructor
    · rintro ⟨w, hw, hwz⟩
      obtain ⟨φ, hφ, hφw⟩ := maxBranched_transitive hS₀ hreg y₀ w z hwz
        (fun h => h hw.2.2)
      refine ⟨⟨φ, hφ⟩, ?_⟩
      have : ((⟨φ, hφ⟩⁻¹ : Deck (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M)) :
          MaxBranchedCover (Sing G X M) y₀ ≃ₜ MaxBranchedCover (Sing G X M) y₀) z = w := by
        rw [← hφw]; exact φ.symm_apply_apply w
      rw [this]; exact hw
    · rintro ⟨γ, hz⟩
      refine ⟨_, hz, ?_⟩
      have h1 := congrFun (γ⁻¹).2 z
      exact h1
  have hOP : P ((SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) ⁻¹' O) := by
    rw [hpre]
    exact hunion _ fun γ => hdeck _ ⟨_, (γ⁻¹).2, rfl⟩ _ hW'
  have hO : IsOpen O := hco O hOP
  refine ⟨e.source ∩ SpreadEnd.base ⁻¹' O, e.open_source.inter (hO.preimage hβbc.isSpread.continuous),
    ⟨hre, r, ⟨hrW, hre, hr⟩, rfl⟩, ?_⟩
  rintro z ⟨hz, w, hw, hwz⟩
  have : w = z := e.injOn hw.2.1 hz (by rw [← hpe]; exact hwz)
  exact this ▸ hw.1

/-- A tamifying topology is the natural one over the regular part: every `T`-open set is a
natural neighbourhood of each of its points over `reg(M)`. (On a sheet `U` of the covering
`p⁻¹(reg M) → reg M`, a `T`-open `W ⊆ U` has saturation `⋃_γ γ(W)`, `T`-open by (C), so `p(W)` is
open by (A), and `W = U ∩ p⁻¹(p(W))`.) This is the hypothesis "strong and weak topologies agree on
`R`" under which the proof of `theo:local_virt_tame` (l.2096) applies `lem:spread_top`, and which
the paper does not check. -/
theorem IsTamifyingTopology.exists_isOpen_subset
    (hreg : SemilocallySimplyConnected ((Sing G X M)ᶜ : Set M)) {y₀ : ((Sing G X M)ᶜ : Set M)}
    {T : TopologicalSpace (MaxBranchedCover (Sing G X M) y₀)}
    (hT : IsTamifyingTopology G X M y₀ T) {W : Set (MaxBranchedCover (Sing G X M) y₀)}
    (hW : IsOpen[T] W) {r : MaxBranchedCover (Sing G X M) y₀} (hrW : r ∈ W)
    (hr : r.base ∈ Reg G X M) : ∃ U, IsOpen[weakTopMax G X M y₀] U ∧ r ∈ U ∧ U ⊆ W :=
  exists_isOpen_subset_of_strongPred hreg (fun s => IsOpen[T] s)
    (fun s hs => TopologicalSpace.le_def.1 hT.le_natural s hs)
    (fun _ _ hs ht => hs.inter ht)
    (fun _ hs => isOpen_iUnion hs)
    (fun f hf _ hs => @Continuous.isOpen_preimage _ _ T T f (hT.continuous_deck f hf) _ hs)
    (fun O hO => by
      have h : IsOpen[TopologicalSpace.coinduced SpreadEnd.base T] O := isOpen_coinduced.2 hO
      rwa [hT.coinduced_eq] at h) hW hrW hr

/-- A tamifying topology induces the natural topology on `p⁻¹(reg M)`. -/
theorem IsTamifyingTopology.induced_reg_eq
    (hreg : SemilocallySimplyConnected ((Sing G X M)ᶜ : Set M)) {y₀ : ((Sing G X M)ᶜ : Set M)}
    {T : TopologicalSpace (MaxBranchedCover (Sing G X M) y₀)}
    (hT : IsTamifyingTopology G X M y₀ T) :
    TopologicalSpace.induced (Subtype.val :
        ((SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) ⁻¹' Reg G X M) → _) T =
      TopologicalSpace.induced Subtype.val (weakTopMax G X M y₀) := by
  refine le_antisymm (induced_mono hT.le_natural) ?_
  intro s hs
  obtain ⟨W, hW, rfl⟩ := (isOpen_induced_iff (t := T)).1 hs
  refine (@isOpen_iff_forall_mem_open _ (TopologicalSpace.induced Subtype.val
    (weakTopMax G X M y₀)) _).2 fun r hr => ?_
  obtain ⟨U, hU, hrU, hUW⟩ := hT.exists_isOpen_subset hreg hW hr r.2
  exact ⟨Subtype.val ⁻¹' U, fun z hz => hUW hz,
    (isOpen_induced_iff (t := weakTopMax G X M y₀)).2 ⟨U, hU, rfl⟩, hrU⟩

end TamifyingReg

/-! ### Automorphisms lift to `\widetilde M` -/

section AutLift

variable {G : Type*} {X : Type*} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
  {N : Type u} [TopologicalSpace N] [T2Space N] [LocPathConnectedSpace N]
  [FirstCountableTopology N] [ConnectedSpace N] [SingularGXStructure G X N]

/-- The second step of the proof of `theo:local_virt_tame` (l.2106, "an automorphism of `X_α` …
lifts to an automorphism of `\widetilde X_α`"): every `ψ ∈ Aut(N)` lifts to a homeomorphism `Ψ`
of `\widetilde N = \widetilde N^{sing N}` over `ψ`, an a.e. `(G,X)`-morphism for the structure
`p^*B` (an element of `Aut(\widetilde N)`). `ψ` preserves `reg(N)`, its restriction lifts to the
universal cover of `reg(N)`, and the lift extends to the spaces of ends. -/
theorem exists_lift_singularAut (hreg : SemilocallySimplyConnected ((Sing G X N)ᶜ : Set N))
    (y₀ : ((Sing G X N)ᶜ : Set N)) {ψ : N ≃ₜ N} (hψ : ψ ∈ singularAut G X N) :
    ∃ Ψ : MaxBranchedCover (Sing G X N) y₀ ≃ₜ MaxBranchedCover (Sing G X N) y₀,
      (∀ e, (Ψ e).base = ψ e.base) ∧
      IsAEMorphismOf G (aePullback G (aeAtlas G X N) SpreadEnd.base)
        (aePullback G (aeAtlas G X N) SpreadEnd.base)
        (Ψ : MaxBranchedCover (Sing G X N) y₀ → MaxBranchedCover (Sing G X N) y₀) := by
  have hBm := isMaximalAEAtlas_aeAtlas G X N
  have hS₀ := isSkeletal_sing G X N
  obtain ⟨-, hβbc, -, -, hβl, -⟩ := maxBranched_basic hS₀ hreg y₀
  haveI := hβl
  have hψ' : IsAEMorphism G X (ψ.symm : N → N) := IsAEMorphism.symm_of_homeomorph hψ
  have hSψ := (IsAEMorphism.preimage_reg_sing hψ ψ.isLocalHomeomorph).2
  have hSψ' := (IsAEMorphism.preimage_reg_sing hψ' ψ.symm.isLocalHomeomorph).2
  have hmem : ∀ z : N, z ∈ (Sing G X N)ᶜ → ψ z ∈ (Sing G X N)ᶜ := fun z hz h => by
    have : z ∈ ψ ⁻¹' Sing G X N := h
    rw [hSψ] at this; exact hz this
  have hmem' : ∀ z : N, z ∈ (Sing G X N)ᶜ → ψ.symm z ∈ (Sing G X N)ᶜ := fun z hz h => by
    have : z ∈ ψ.symm ⁻¹' Sing G X N := h
    rw [hSψ'] at this; exact hz this
  haveI : LocPathConnectedSpace ((Sing G X N)ᶜ : Set N) :=
    (isSkeletal_iff.1 hS₀).isOpen.locPathConnectedSpace
  haveI : PathConnectedSpace ((Sing G X N)ᶜ : Set N) :=
    pathConnectedSpace_iff_connectedSpace.2
      (isConnected_iff_connectedSpace.1 (isSkeletal_iff.1 hS₀).isConnected)
  haveI := UniversalCover.simplyConnectedSpace (y₀ := y₀) hreg
  have hπ := UniversalCover.isCoveringMap_proj (y₀ := y₀) hreg
  set π := UniversalCover.proj ((Sing G X N)ᶜ : Set N) y₀
  set f₁ : C(UniversalCover ((Sing G X N)ᶜ : Set N) y₀, ((Sing G X N)ᶜ : Set N)) :=
    ⟨fun c => ⟨ψ (π c), hmem _ (π c).2⟩,
      (ψ.continuous.comp (continuous_subtype_val.comp UniversalCover.continuous_proj)).subtype_mk _⟩
  set f₂ : C(UniversalCover ((Sing G X N)ᶜ : Set N) y₀, ((Sing G X N)ᶜ : Set N)) :=
    ⟨fun c => ⟨ψ.symm (π c), hmem' _ (π c).2⟩,
      (ψ.symm.continuous.comp (continuous_subtype_val.comp UniversalCover.continuous_proj)).subtype_mk
        _⟩
  obtain ⟨e₀, he₀⟩ := UniversalCover.proj_surjective (y₀ := y₀) (f₁ (UniversalCover.base y₀))
  obtain ⟨F, ⟨hF0, hF⟩, -⟩ := hπ.existsUnique_continuousMap_lifts f₁ (UniversalCover.base y₀) e₀ he₀
  have he₀' : π (UniversalCover.base y₀) = f₂ e₀ := by
    apply Subtype.ext
    have h1 : (π e₀ : N) = ψ (y₀ : N) := congrArg Subtype.val he₀
    show (y₀ : N) = ψ.symm (π e₀ : N)
    rw [h1, ψ.symm_apply_apply]
  obtain ⟨F', ⟨hF'0, hF'⟩, -⟩ :=
    hπ.existsUnique_continuousMap_lifts f₂ e₀ (UniversalCover.base y₀) he₀'
  have hcF : ∀ c, (π (F c) : N) = ψ (π c) := fun c => congrArg Subtype.val (congrFun hF c)
  have hcF' : ∀ c, (π (F' c) : N) = ψ.symm (π c) := fun c => congrArg Subtype.val (congrFun hF' c)
  have hFF' : F' ∘ F = id := hπ.eq_of_comp_eq (F'.continuous.comp F.continuous) continuous_id
    (funext fun c => Subtype.ext (by
      show (π (F' (F c)) : N) = (π c : N)
      rw [hcF', hcF, ψ.symm_apply_apply])) (UniversalCover.base y₀)
    (by show F' (F _) = _; rw [hF0, hF'0]; rfl)
  have hF'F : F ∘ F' = id := hπ.eq_of_comp_eq (F.continuous.comp F'.continuous) continuous_id
    (funext fun c => Subtype.ext (by
      show (π (F (F' c)) : N) = (π c : N)
      rw [hcF, hcF', ψ.apply_symm_apply])) e₀
    (by show F (F' _) = _; rw [hF'0, hF0]; rfl)
  have hc : ∀ c, univCoverProj (Sing G X N) y₀ (F c) = ψ (univCoverProj (Sing G X N) y₀ c) := hcF
  have hc' : ∀ c, univCoverProj (Sing G X N) y₀ (F' c) =
      ψ.symm (univCoverProj (Sing G X N) y₀ c) := hcF'
  set Φ := SpreadEnd.map ψ.continuous F.continuous hc
  set Φ' := SpreadEnd.map ψ.symm.continuous F'.continuous hc'
  have hΦ'Φ : Φ' ∘ Φ = id := by
    refine SpreadEnd.denseRange_ofPoint.equalizer
      ((SpreadEnd.continuous_map _ _ _).comp (SpreadEnd.continuous_map _ _ _)) continuous_id
      (funext fun c => ?_)
    simp only [comp_apply, id, Φ, Φ', SpreadEnd.map_ofPoint]
    rw [show F' (F c) = c from congrFun hFF' c]
  have hΦΦ' : Φ ∘ Φ' = id := by
    refine SpreadEnd.denseRange_ofPoint.equalizer
      ((SpreadEnd.continuous_map _ _ _).comp (SpreadEnd.continuous_map _ _ _)) continuous_id
      (funext fun c => ?_)
    simp only [comp_apply, id, Φ, Φ', SpreadEnd.map_ofPoint]
    rw [show F (F' c) = c from congrFun hF'F c]
  let Ψ : MaxBranchedCover (Sing G X N) y₀ ≃ₜ MaxBranchedCover (Sing G X N) y₀ :=
    { toFun := Φ
      invFun := Φ'
      left_inv := congrFun hΦ'Φ
      right_inv := congrFun hΦΦ'
      continuous_toFun := SpreadEnd.continuous_map _ _ _
      continuous_invFun := SpreadEnd.continuous_map _ _ _ }
  have hbase : ∀ e, (Ψ e).base = ψ e.base := fun e =>
    SpreadEnd.base_map ψ.continuous F.continuous hc e
  exact ⟨Ψ, hbase, morphism_singular_manifolds_branched hBm.1 hBm.1 hψ hβbc hβbc Ψ.continuous
    hbase⟩

end AutLift

/-! ### The gluing step of `theo:local_virt_tame` -/

section Glue

variable {E : Type*} {ι : Type*}

/-- The neighbourhood filters of the glued topology: at `e`, those of `T i` for a chosen `i`
with `e ∈ W i`. -/
def glueNhds (W : ι → Set E) (T : ι → TopologicalSpace E) (hcov : ∀ e, ∃ i, e ∈ W i)
    (e : E) : Filter E :=
  @nhds E (T (hcov e).choose) e

/-- Gluing topologies `T i`, each given near the points of `W i`. -/
@[reducible] def glueTop (W : ι → Set E) (T : ι → TopologicalSpace E) (hcov : ∀ e, ∃ i, e ∈ W i) :
    TopologicalSpace E :=
  TopologicalSpace.mkOfNhds (glueNhds W T hcov)

/-- If the `W i` are `T i`-open, cover `E` and the `T i` have the same neighbourhoods at the
points of the overlaps, the glued topology has the neighbourhoods of `T i` at every point of
`W i`. -/
theorem nhds_glueTop {W : ι → Set E} {T : ι → TopologicalSpace E} (hcov : ∀ e, ∃ i, e ∈ W i)
    (hWo : ∀ i, IsOpen[T i] (W i))
    (hcompat : ∀ i j e, e ∈ W i → e ∈ W j → @nhds E (T i) e = @nhds E (T j) e)
    {i : ι} {e : E} (he : e ∈ W i) : @nhds E (glueTop W T hcov) e = @nhds E (T i) e := by
  have key : ∀ x j, x ∈ W j → glueNhds W T hcov x = @nhds E (T j) x := fun x j hx =>
    hcompat _ _ x (hcov x).choose_spec hx
  rw [glueTop, nhds_mkOfNhds _ _ ?_ ?_, key e i he]
  · intro x
    rw [key x _ (hcov x).choose_spec]
    exact @pure_le_nhds E (T _) x
  · intro x s hs
    rw [key x _ (hcov x).choose_spec] at hs ⊢
    letI := T (hcov x).choose
    have h1 : ∀ᶠ y in 𝓝 x, s ∈ 𝓝 y := eventually_eventually_nhds.2 hs
    have h2 : ∀ᶠ y in 𝓝 x, y ∈ W (hcov x).choose :=
      (hWo _).mem_nhds (hcov x).choose_spec
    filter_upwards [h1, h2] with y hy1 hy2
    rw [key y _ hy2]
    exact hy1

/-- Two topologies with the same neighbourhoods at the points of `s` induce the same topology
on `s`. -/
theorem induced_eq_of_nhds_eq {t₁ t₂ : TopologicalSpace E} {s : Set E}
    (h : ∀ e ∈ s, @nhds E t₁ e = @nhds E t₂ e) :
    TopologicalSpace.induced (Subtype.val : s → E) t₁ =
      TopologicalSpace.induced (Subtype.val : s → E) t₂ := by
  refine TopologicalSpace.ext_nhds fun x => ?_
  rw [@nhds_induced _ _ t₁, @nhds_induced _ _ t₂, h x x.2]

/-- Path-connectedness of a subset of `s` transfers between two topologies with the same
neighbourhoods at the points of `s`. -/
theorem isPathConnected_of_nhds_eq {t₁ t₂ : TopologicalSpace E} {s u : Set E} (hus : u ⊆ s)
    (h : ∀ e ∈ s, @nhds E t₁ e = @nhds E t₂ e) (hu : @IsPathConnected E t₁ u) :
    @IsPathConnected E t₂ u := by
  have hi := induced_eq_of_nhds_eq (s := u) fun e he => h e (hus he)
  rw [@isPathConnected_iff_pathConnectedSpace E t₁] at hu
  rw [@isPathConnected_iff_pathConnectedSpace E t₂]
  change @PathConnectedSpace u (TopologicalSpace.induced Subtype.val t₂)
  rw [← hi]
  exact hu

/-- A basis of path-connected neighbourhoods transfers between two topologies with the same
neighbourhoods at the points of an open set. -/
theorem hasBasis_isPathConnected_of_nhds_eq {t₁ t₂ : TopologicalSpace E} {W : Set E}
    (hWo : IsOpen[t₁] W) (h : ∀ e ∈ W, @nhds E t₁ e = @nhds E t₂ e) {e : E} (he : e ∈ W)
    (hb : (@nhds E t₁ e).HasBasis (fun s => s ∈ @nhds E t₁ e ∧ @IsPathConnected E t₁ s) id) :
    (@nhds E t₂ e).HasBasis (fun s => s ∈ @nhds E t₂ e ∧ @IsPathConnected E t₂ s) id := by
  have hb' := hb.restrict_subset (@IsOpen.mem_nhds E t₁ _ _ hWo he)
  rw [← h e he]
  refine hb'.to_hasBasis (fun s hs => ⟨s, ⟨hs.1.1, isPathConnected_of_nhds_eq hs.2 h hs.1.2⟩,
    subset_rfl⟩) (fun s hs => ?_)
  obtain ⟨s', hs', hs's⟩ := hb'.mem_iff.1 hs.1
  exact ⟨s', hs', hs's⟩

end Glue


section RegCongr

variable {G : Type*} {X : Type*} [TopologicalSpace X] [Group G] [MulAction G X]
  {P : Type*} [TopologicalSpace P] {N : Type*} [TopologicalSpace N]

/-- Inducing a `(G,X)`-morphism on an open set depends only on the values there. -/
theorem IsRegularOn.congr_of_eqOn' {A : Set (OpenPartialHomeomorph P X)}
    {B : Set (OpenPartialHomeomorph N X)} {f g : P → N} {U : Set P}
    (h : IsRegularOn G A B f U) (hfg : EqOn f g U) : IsRegularOn G A B g U := by
  refine ⟨h.isOpen, h.subset_support, fun x hx => hfg hx ▸ h.mapsTo hx,
    h.continuousOn.congr hfg.symm, fun x hx e he e' he' hxe hgx => ?_⟩
  obtain ⟨k, hk⟩ := h.exists_smul_eq x hx e he e' he' hxe (by rw [hfg hx]; exact hgx)
  refine ⟨k, ?_⟩
  filter_upwards [hk, h.isOpen.mem_nhds hx] with y hy hyU
  rw [← hfg hyU]; exact hy

end RegCongr

section ChartGlue

variable {G : Type*} {X : Type*} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
  {M : Type v} [TopologicalSpace M] [T2Space M] [LocPathConnectedSpace M]
  [FirstCountableTopology M] [ConnectedSpace M] [SingularGXStructure G X M]

variable (G X M) in
/-- The projection `\widetilde M → M` is continuous for the natural topology. -/
theorem continuous_base_weakTopMax (y₀ : ((Sing G X M)ᶜ : Set M)) :
    Continuous[weakTopMax G X M y₀, _]
      (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) :=
  SpreadEnd.continuous_base

/-- The preimage of an open subset of `M` is open in `\widetilde M` (natural topology). -/
theorem isOpen_preimage_base_weakTopMax (y₀ : ((Sing G X M)ᶜ : Set M)) {U : Set M}
    (hU : IsOpen U) : IsOpen[weakTopMax G X M y₀]
      ((SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) ⁻¹' U) :=
  hU.preimage SpreadEnd.continuous_base

/-- `IsRegDevelopingOnReg` depends only on the values over `reg(M)`. -/
theorem IsRegDevelopingOnReg.congr {y₀ : ((Sing G X M)ᶜ : Set M)}
    {D D' : MaxBranchedCover (Sing G X M) y₀ → X} (h : IsRegDevelopingOnReg G X M y₀ D)
    (hDD' : EqOn D D' ((SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) ⁻¹' Reg G X M)) :
    IsRegDevelopingOnReg G X M y₀ D' :=
  IsRegularOn.congr_of_eqOn' h hDD'

variable (G X M) in
/-- The local data of the proof of `theo:local_virt_tame` (l.2096–2140) over an open `U ⊆ M`:
a topology `T` on `\widetilde M`, finer than the natural one, which at the points of `p⁻¹(U)`
is first countable and locally path-connected, agrees with the natural topology over `reg(M)`,
induces on `U` the natural topology ((A) over `U`), carries a `T`-continuous extension of the
regular developing map `D₀` near every point ((B) over `U`), is preserved by `Γ(\widetilde M/M)`
((C) over `U`) and makes `p⁻¹(reg U)` portly in `p⁻¹(U)` ((D) over `U`). -/
structure IsLocalTamifying (y₀ : ((Sing G X M)ᶜ : Set M))
    (D₀ : MaxBranchedCover (Sing G X M) y₀ → X) (U : Set M)
    (T : TopologicalSpace (MaxBranchedCover (Sing G X M) y₀)) : Prop where
  le_natural : T ≤ weakTopMax G X M y₀
  isCountablyGenerated : ∀ e : MaxBranchedCover (Sing G X M) y₀, e.base ∈ U →
    (@nhds _ T e).IsCountablyGenerated
  pathBasis : ∀ e : MaxBranchedCover (Sing G X M) y₀, e.base ∈ U →
    (@nhds _ T e).HasBasis (fun s => s ∈ @nhds _ T e ∧ @IsPathConnected _ T s) id
  nhds_reg : ∀ e : MaxBranchedCover (Sing G X M) y₀, e.base ∈ U → e.base ∈ Reg G X M →
    @nhds _ T e = @nhds _ (weakTopMax G X M y₀) e
  isOpen_base : ∀ O : Set M,
    IsOpen[T] ((SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) ⁻¹' O ∩
      SpreadEnd.base ⁻¹' U) → IsOpen (O ∩ U)
  extension : ∀ e : MaxBranchedCover (Sing G X M) y₀, e.base ∈ U →
    ∃ W : Set (MaxBranchedCover (Sing G X M) y₀), IsOpen[T] W ∧ e ∈ W ∧
      ∃ D' : MaxBranchedCover (Sing G X M) y₀ → X, @ContinuousOn _ X T _ D' W ∧
        EqOn D' D₀ (W ∩ SpreadEnd.base ⁻¹' Reg G X M)
  continuousAt_deck : ∀ f ∈ deckMapsMax G X M y₀, ∀ e : MaxBranchedCover (Sing G X M) y₀,
    e.base ∈ U → @ContinuousAt _ _ T T f e
  isPortly : @IsPortly ((SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) ⁻¹' U)
    (TopologicalSpace.induced Subtype.val T)
    (Subtype.val ⁻¹' ((SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) ⁻¹' Reg G X M))


/-- The interface is the global notion read locally: a tamifying topology, with the `T`-continuous
developing map `D` of its (B), is a local tamifying topology over every open `U` (for `D₀ = D`) (so `IsLocalTamifying` is not
vacuous, and `exists_isTamifyingTopology_of_local` has the converse direction). -/
theorem IsTamifyingTopology.isLocalTamifying
    (hreg : SemilocallySimplyConnected ((Sing G X M)ᶜ : Set M)) {y₀ : ((Sing G X M)ᶜ : Set M)}
    {D : MaxBranchedCover (Sing G X M) y₀ → X} {U : Set M} (hU : IsOpen U)
    {T : TopologicalSpace (MaxBranchedCover (Sing G X M) y₀)}
    (hT : IsTamifyingTopology G X M y₀ T) (hDc : Continuous[T, _] D) :
    IsLocalTamifying G X M y₀ D U T := by
  have hOU : IsOpen[T] ((SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) ⁻¹' U) :=
    TopologicalSpace.le_def.1 hT.le_natural _ (isOpen_preimage_base_weakTopMax y₀ hU)
  refine ⟨hT.le_natural, fun e _ => @FirstCountableTopology.nhds_generated_countable _ T
    hT.firstCountable e, fun e _ => @path_connected_basis _ T hT.locPathConnected e,
    fun e _ he => ?_, fun O hO => ?_, fun e _ => ⟨univ, @isOpen_univ _ T, mem_univ e, D,
    hDc.continuousOn, fun _ _ => rfl⟩,
    fun f hf e _ => @Continuous.continuousAt _ _ T T f e (hT.continuous_deck f hf), ?_⟩
  · refine le_antisymm (nhds_mono hT.le_natural) fun s hs => ?_
    obtain ⟨W, hWs, hWo, heW⟩ := mem_nhds_iff.1 hs
    obtain ⟨V, hV, heV, hVW⟩ := hT.exists_isOpen_subset hreg hWo heW he
    exact Filter.mem_of_superset (@IsOpen.mem_nhds _ (weakTopMax G X M y₀) _ _ hV heV)
      (hVW.trans hWs)
  · have h : IsOpen[TopologicalSpace.coinduced SpreadEnd.base T] (O ∩ U) :=
      isOpen_coinduced.2 (by rw [preimage_inter]; exact hO)
    rwa [hT.coinduced_eq] at h
  · have hp := hT.isPortly
    have hlc : @LocallyConnectedSpace _ T := by haveI := hT.locPathConnected; infer_instance
    have hpre : (Subtype.val : (SpreadEnd.base ⁻¹' U : Set (MaxBranchedCover (Sing G X M) y₀)) →
        MaxBranchedCover (Sing G X M) y₀) ⁻¹' (SpreadEnd.base ⁻¹' Reg G X M) =
        Subtype.val ⁻¹' (SpreadEnd.base ⁻¹' Reg G X M ∩ SpreadEnd.base ⁻¹' U) := by
      ext z; exact ⟨fun h => ⟨h, z.2⟩, fun h => h.1⟩
    rw [hpre]
    refine (@isPortly_subtype_iff _ T _ _ hOU inter_subset_right).2 ⟨@IsOpen.inter _ T _ _
      hp.isOpen hOU, fun x hx => ?_, fun W hW hWO hWc => ?_⟩
    · have h := @IsOpen.inter_closure _ T _ (SpreadEnd.base ⁻¹' Reg G X M) hOU x
        (mem_inter hx (hp.dense x))
      rwa [inter_comm] at h
    · have heq : W ∩ (SpreadEnd.base ⁻¹' Reg G X M ∩ SpreadEnd.base ⁻¹' U) =
          W ∩ SpreadEnd.base ⁻¹' Reg G X M := by
        ext z; exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hWO h.1⟩⟩
      rw [heq]
      exact hp.locallyConnectedIn W hW hWc

/-- The gluing step of the proof of `theo:local_virt_tame`: a topology `T'` on `\widetilde M`
which, at the points of each `p⁻¹(U i)`, has the neighbourhoods of a local tamifying topology
`T i` over `U i` (the `U i` an open cover of `M`) is tamifying. -/
theorem isTamifyingTopology_of_nhds_eq {y₀ : ((Sing G X M)ᶜ : Set M)}
    {D₀ : MaxBranchedCover (Sing G X M) y₀ → X} (hD₀ : IsRegDevelopingOnReg G X M y₀ D₀)
    {ι : Type*} (U : ι → Set M) (hUo : ∀ i, IsOpen (U i)) (hcov : ∀ y : M, ∃ i, y ∈ U i)
    (T : ι → TopologicalSpace (MaxBranchedCover (Sing G X M) y₀))
    (hT : ∀ i, IsLocalTamifying G X M y₀ D₀ (U i) (T i))
    (T' : TopologicalSpace (MaxBranchedCover (Sing G X M) y₀))
    (hN : ∀ i (e : MaxBranchedCover (Sing G X M) y₀), e.base ∈ U i →
      @nhds _ T' e = @nhds _ (T i) e) :
    IsTamifyingTopology G X M y₀ T' := by
  have hWτ : ∀ i, IsOpen[weakTopMax G X M y₀]
      ((SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) ⁻¹' U i) := fun i =>
    isOpen_preimage_base_weakTopMax y₀ (hUo i)
  have hcovE : ∀ e : MaxBranchedCover (Sing G X M) y₀, ∃ i, e.base ∈ U i := fun e => hcov e.base
  -- `T' ≤` natural
  have hle : T' ≤ weakTopMax G X M y₀ := (le_iff_nhds _ _).2 fun e => by
    obtain ⟨i, hi⟩ := hcovE e
    rw [hN i e hi]
    exact (le_iff_nhds _ _).1 (hT i).le_natural e
  have hWo : ∀ i, IsOpen[T'] ((SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) ⁻¹' U i) :=
    fun i => TopologicalSpace.le_def.1 hle _ (hWτ i)
  have hWoi : ∀ i, IsOpen[T i]
      ((SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) ⁻¹' U i) :=
    fun i => TopologicalSpace.le_def.1 (hT i).le_natural _ (hWτ i)
  -- first countable, locally path-connected
  have hfc : @FirstCountableTopology _ T' := @FirstCountableTopology.mk _ T' fun e => by
    obtain ⟨i, hi⟩ := hcovE e
    rw [hN i e hi]
    exact (hT i).isCountablyGenerated e hi
  have hlpc : @LocPathConnectedSpace _ T' := @LocPathConnectedSpace.mk _ T' fun e => by
    obtain ⟨i, hi⟩ := hcovE e
    exact hasBasis_isPathConnected_of_nhds_eq (hWoi i) (fun e' he' => (hN i e' he').symm) hi
      ((hT i).pathBasis e hi)
  -- (D) portly
  have hlc : @LocallyConnectedSpace _ T' := by haveI := hlpc; infer_instance
  have hportly : @IsPortly _ T'
      ((SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) ⁻¹' Reg G X M) := by
    set R := (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) ⁻¹' Reg G X M with hR
    set W : ι → Set (MaxBranchedCover (Sing G X M) y₀) := fun i => SpreadEnd.base ⁻¹' U i
      with hW
    have hloc := @isPortly_iUnion_of_local _ T' hlc ι W (fun i => R ∩ W i) hWo
      (fun i => inter_subset_right) (fun i => by
        have hind := induced_eq_of_nhds_eq (t₁ := T') (t₂ := T i) (s := W i)
          fun e he => hN i e he
        have hpre : (Subtype.val : W i → MaxBranchedCover (Sing G X M) y₀) ⁻¹' (R ∩ W i) =
            Subtype.val ⁻¹' R := by
          ext z; exact ⟨fun h => h.1, fun h => ⟨h, z.2⟩⟩
        rw [hpre]
        change @IsPortly (W i) (TopologicalSpace.induced Subtype.val T') _
        rw [hind]
        exact (hT i).isPortly)
    have hWu : (⋃ i, W i) = univ := iUnion_eq_univ_iff.2 hcovE
    have hRu : (⋃ i, R ∩ W i) = R := by rw [← inter_iUnion, hWu, inter_univ]
    have hV : @IsPortly _ T' (⋃ i, W i) := by rw [hWu]; exact @isPortly_univ _ T'
    have := @IsPortly.of_subtype _ T' (⋃ i, R ∩ W i) (⋃ i, W i) hloc
      (iUnion_mono fun i => inter_subset_right) hV
    rwa [hRu] at this
  -- (A)
  have hA : TopologicalSpace.coinduced (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) T' =
      ‹TopologicalSpace M› := by
    refine le_antisymm ?_ ?_
    · exact continuous_iff_coinduced_le.1
        (continuous_le_dom hle (continuous_base_weakTopMax G X M y₀))
    · refine TopologicalSpace.le_def.2 fun O hO => ?_
      have hO' : IsOpen[T'] ((SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) ⁻¹' O) :=
        isOpen_coinduced.1 hO
      have hOi : ∀ i, IsOpen (O ∩ U i) := fun i => (hT i).isOpen_base O (by
        refine (@isOpen_iff_mem_nhds _ (T i) _).2 fun e he => ?_
        rw [← hN i e he.2]
        exact Filter.inter_mem (@IsOpen.mem_nhds _ T' _ _ hO' he.1)
          (@IsOpen.mem_nhds _ T' _ _ (hWo i) he.2))
      have hOU : O = ⋃ i, O ∩ U i := by
        ext y
        simp only [mem_iUnion, mem_inter_iff]
        exact ⟨fun hy => let ⟨i, hi⟩ := hcov y; ⟨i, hy, hi⟩, fun ⟨_, hy, _⟩ => hy⟩
      rw [hOU]
      exact isOpen_iUnion hOi
  -- (C)
  have hC : ∀ f ∈ deckMapsMax G X M y₀, Continuous[T', T'] f := by
    rintro f ⟨γ, hγ, rfl⟩
    refine (@continuous_iff_continuousAt _ _ T' T' _).2 fun e => ?_
    obtain ⟨i, hi⟩ := hcovE e
    have hγe : (γ e).base ∈ U i := by
      have := congrFun (show (SpreadEnd.base ∘ ⇑γ) = SpreadEnd.base from hγ) e
      simp only [Function.comp_apply] at this
      rw [this]; exact hi
    have h := (hT i).continuousAt_deck _ ⟨γ, hγ, rfl⟩ e hi
    unfold ContinuousAt at h ⊢
    rw [hN i e hi, hN i (γ e) hγe]
    exact h
  -- (B)
  set R := (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) ⁻¹' Reg G X M with hR
  have hdense : ∀ e, (@nhds _ T' e ⊓ 𝓟 R).NeBot := fun e =>
    (@mem_closure_iff_clusterPt _ T' _ _).1 (hportly.dense e)
  have hext : ∀ e : MaxBranchedCover (Sing G X M) y₀, ∃ (i : ι)
      (W : Set (MaxBranchedCover (Sing G X M) y₀)) (D' : MaxBranchedCover (Sing G X M) y₀ → X),
      e.base ∈ U i ∧ IsOpen[T i] W ∧ e ∈ W ∧ @ContinuousOn _ X (T i) _ D' W ∧
        EqOn D' D₀ (W ∩ R) := fun e => by
    obtain ⟨i, hi⟩ := hcovE e
    obtain ⟨W, hW, heW, D', hD', hEq⟩ := (hT i).extension e hi
    exact ⟨i, W, D', hi, hW, heW, hD', hEq⟩
  choose ie We De hie hWe heWe hDe hEqe using hext
  have hcont : ∀ e e', e' ∈ We e → e'.base ∈ U (ie e) → @ContinuousAt _ X T' _ (De e) e' :=
    fun e e' h1 h2 => by
      have h := @ContinuousOn.continuousAt _ X (T (ie e)) _ _ _ _ (hDe e)
        (@IsOpen.mem_nhds _ (T (ie e)) _ _ (hWe e) h1)
      unfold ContinuousAt at h ⊢
      rw [hN (ie e) e' h2]
      exact h
  have hmem : ∀ e e', e' ∈ We e → e'.base ∈ U (ie e) → We e ∈ @nhds _ T' e' := fun e e' h1 h2 => by
    rw [hN (ie e) e' h2]
    exact @IsOpen.mem_nhds _ (T (ie e)) _ _ (hWe e) h1
  have hagree : ∀ e e', e' ∈ We e → e'.base ∈ U (ie e) → De e' e' = De e e' := fun e e' h1 h2 => by
    haveI := hdense e'
    refine tendsto_nhds_unique (l := @nhds _ T' e' ⊓ 𝓟 R)
      ((hcont e' e' (heWe e') (hie e')).tendsto.mono_left inf_le_left) ?_
    refine ((hcont e e' h1 h2).tendsto.mono_left inf_le_left).congr' ?_
    filter_upwards [inter_mem_inf (inter_mem (hmem e' e' (heWe e') (hie e')) (hmem e e' h1 h2))
      (mem_principal_self R)] with z hz
    rw [hEqe e ⟨hz.1.2, hz.2⟩, hEqe e' ⟨hz.1.1, hz.2⟩]
  have hcontD : Continuous[T', _] (fun e => De e e) := by
    refine (@continuous_iff_continuousAt _ X T' _ _).2 fun e => ?_
    refine (hcont e e (heWe e) (hie e)).congr ?_
    filter_upwards [hmem e e (heWe e) (hie e), @IsOpen.mem_nhds _ T' _ _ (hWo (ie e)) (hie e)]
      with z hz1 hz2
    exact (hagree e z hz1 hz2).symm
  have hregD : IsRegDevelopingOnReg G X M y₀ (fun e => De e e) :=
    IsRegDevelopingOnReg.congr hD₀ fun e he => (hEqe e ⟨heWe e, he⟩).symm
  exact ⟨hle, hfc, hlpc, hA, ⟨_, hcontD, hregD⟩, hC, hportly⟩

/-- The gluing step of the proof of `theo:local_virt_tame`: local tamifying topologies over an open
cover of `M` whose neighbourhood filters agree over the overlaps glue to a tamifying topology
(`glueTop`, `isTamifyingTopology_of_nhds_eq`). -/
theorem exists_isTamifyingTopology_of_local {y₀ : ((Sing G X M)ᶜ : Set M)}
    {D₀ : MaxBranchedCover (Sing G X M) y₀ → X} (hD₀ : IsRegDevelopingOnReg G X M y₀ D₀)
    {ι : Type*} (U : ι → Set M) (hUo : ∀ i, IsOpen (U i)) (hcov : ∀ y : M, ∃ i, y ∈ U i)
    (T : ι → TopologicalSpace (MaxBranchedCover (Sing G X M) y₀))
    (hT : ∀ i, IsLocalTamifying G X M y₀ D₀ (U i) (T i))
    (hcompat : ∀ i j (e : MaxBranchedCover (Sing G X M) y₀), e.base ∈ U i → e.base ∈ U j →
      @nhds _ (T i) e = @nhds _ (T j) e) :
    ∃ T' : TopologicalSpace (MaxBranchedCover (Sing G X M) y₀), IsTamifyingTopology G X M y₀ T' := by
  have hcovE : ∀ e : MaxBranchedCover (Sing G X M) y₀,
      ∃ i, e ∈ (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) ⁻¹' U i :=
    fun e => hcov e.base
  have hWo : ∀ i, IsOpen[T i]
      ((SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) ⁻¹' U i) :=
    fun i => TopologicalSpace.le_def.1 (hT i).le_natural _
      (isOpen_preimage_base_weakTopMax y₀ (hUo i))
  exact ⟨_, isTamifyingTopology_of_nhds_eq hD₀ U hUo hcov T hT _ fun i e he =>
    nhds_glueTop hcovE hWo (fun i j e hi hj => hcompat i j e hi hj) he⟩

end ChartGlue

section RegDev

variable {G : Type*} {X : Type*} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
  [FaithfulSMul G X]
  {M : Type v} [TopologicalSpace M] [T2Space M] [LocPathConnectedSpace M]
  [FirstCountableTopology M] [ConnectedSpace M] [SingularGXStructure G X M]

/-- `\widetilde M` carries a developing map over its regular part: the developing map of the
simply connected `\widetilde{reg M} = p⁻¹(reg M)` (`GX.exists_developing_of_simplyConnected`),
read on `\widetilde M` (`D₀` of the proof of `theo:local_virt_tame`, l.2088). -/
theorem exists_isRegDevelopingOnReg (hreg : SemilocallySimplyConnected ((Sing G X M)ᶜ : Set M))
    (y₀ : ((Sing G X M)ᶜ : Set M)) :
    ∃ D₀ : MaxBranchedCover (Sing G X M) y₀ → X, IsRegDevelopingOnReg G X M y₀ D₀ := by
  set B := aeAtlas G X M
  have hBm : IsMaximalAEAtlas G B := isMaximalAEAtlas_aeAtlas G X M
  have hS₀ : IsSkeletal (Sing G X M) := isSkeletal_sing G X M
  have hRegB : (Sing G X M)ᶜ = support B := compl_compl _
  obtain ⟨-, hβbc, hβS, hβpre, hβl, hβsp⟩ := maxBranched_basic hS₀ hreg y₀
  haveI := hβl
  have hAt := aePullback_spec_of_isAELocalHomeomorph hBm.1 hβbc.isSpread.continuous
    (hβbc.isAELocalHomeomorph hBm.1)
  haveI : LocPathConnectedSpace ((Sing G X M)ᶜ : Set M) :=
    (isSkeletal_iff.1 hS₀).isOpen.locPathConnectedSpace
  have hπcov := UniversalCover.isCoveringMap_proj (y₀ := y₀) hreg
  haveI := UniversalCover.simplyConnectedSpace (y₀ := y₀) hreg
  haveI : T2Space (UniversalCover ((Sing G X M)ᶜ : Set M) y₀) := t2Space_of_isCoveringMap hπcov
  have hπ : IsLocalHomeomorph (Subtype.val ∘ UniversalCover.proj ((Sing G X M)ᶜ : Set M) y₀) :=
    (isSkeletal_iff.1 hS₀).isOpen.isOpenEmbedding_subtypeVal.isLocalHomeomorph.comp
      hπcov.isLocalHomeomorph
  obtain ⟨F, -, hF⟩ := exists_developing_of_simplyConnected (G := G) hBm.1 hπ
    (fun z => by rw [← hRegB]; exact (UniversalCover.proj _ y₀ z).2)
  have hemb := SpreadEnd.isEmbedding_ofPoint hβsp
  have hoe : IsOpenEmbedding (SpreadEnd.ofPoint (univCoverProj (Sing G X M) y₀)) :=
    ⟨hemb, by rw [← hβpre]; exact hS₀.isClosed.isOpen_compl.preimage hβbc.isSpread.continuous⟩
  set F₀ : MaxBranchedCover (Sing G X M) y₀ → X :=
    Function.extend (SpreadEnd.ofPoint (univCoverProj (Sing G X M) y₀)) F
      (fun _ => F (UniversalCover.base y₀))
  have hF₀ : ∀ c : MaxBranchedCover (Sing G X M) y₀, c.base ∈ (Sing G X M)ᶜ →
      ∃ c' ∈ B, c.base ∈ c'.source ∧
      ∃ h : G, ∀ᶠ c'' in 𝓝 c, F₀ c'' = h • c' c''.base := by
    intro c hc
    have hc' : c ∈ range (SpreadEnd.ofPoint (univCoverProj (Sing G X M) y₀)) := by
      rw [← hβpre]; exact hc
    obtain ⟨z, rfl⟩ := hc'
    obtain ⟨c', hc', hzc', h, hh⟩ := hF z
    refine ⟨c', hc', hzc', h, ?_⟩
    rw [← hoe.map_nhds_eq z, eventually_map]
    filter_upwards [hh] with z' hz'
    rw [show F₀ (SpreadEnd.ofPoint _ z') = F z' from hemb.injective.extend_apply _ _ _]
    exact hz'
  set R : Set (MaxBranchedCover (Sing G X M) y₀) := SpreadEnd.base ⁻¹' Reg G X M with hRdef
  have hRo : IsOpen R := (isOpen_reg G X M).preimage hβbc.isSpread.continuous
  have hordβ : Reg G X M ⊆ ordY (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) :=
    fun y hy => by by_contra hn; exact (hβS hn) hy
  have hRsupp : R ⊆ support (aePullback G B
      (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M)) := fun w hw =>
    hAt.2.mem_support_of_isLocalHomeomorphOn' hAt.1 hBm.1 hw
      (hβbc.ordX_subset_isLocalHomeomorphOn (hordβ hw))
  have hregβ := hAt.2.regLocusOf_eq hAt.1.1 hBm.1
  have hβR := (isRegularOn_regLocusOf (G := G) _ B
    (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M)).mono
    (fun w hw => by rw [hregβ]; exact ⟨hRsupp hw, hw⟩) hRo
  exact ⟨F₀, isRegularOn_model_of_eventually_comp hAt.1.1.1 hβR fun w hw => hF₀ w fun h => h hw⟩

end RegDev


/-! ### `def:topological_spaces_continuous_map`, `lem:spread_top` -/

section StrongPull

variable {E : Type*} {N : Type*} [TopologicalSpace E]

/-- **`def:topological_spaces_continuous_map`** (`RamcovGX.tex:1984`): for `p : E → N` and a topology
`T` on `N`, `p^*T` is the topology of `E` generated by the topology of `E` and the connected
components (for the topology of `E`) of the `p⁻¹(O)`, `O ∈ T`. ("Generated by" is the supremum of
open sets, i.e. the infimum `⊓` in mathlib's order, where finer is smaller.) -/
@[reducible] def strongPullTop (p : E → N) (T : TopologicalSpace N) : TopologicalSpace E :=
  ‹TopologicalSpace E› ⊓ TopologicalSpace.generateFrom
    {s | ∃ O : Set N, IsOpen[T] O ∧ ∃ x ∈ p ⁻¹' O, s = connectedComponentIn (p ⁻¹' O) x}

/-- `p^*T` is finer ("thinner") than the topology of `E`. -/
theorem strongPullTop_le (p : E → N) (T : TopologicalSpace N) :
    strongPullTop p T ≤ ‹TopologicalSpace E› :=
  inf_le_left

/-- The generators: a component of `p⁻¹(O)`, `O ∈ T`, is `p^*T`-open. -/
theorem isOpen_strongPullTop_connectedComponentIn (p : E → N) (T : TopologicalSpace N)
    {O : Set N} (hO : IsOpen[T] O) {x : E} (hx : x ∈ p ⁻¹' O) :
    IsOpen[strongPullTop p T] (connectedComponentIn (p ⁻¹' O) x) :=
  (TopologicalSpace.le_def.1 (inf_le_right : strongPullTop p T ≤ _)) _
    (TopologicalSpace.GenerateOpen.basic _ ⟨O, hO, x, hx, rfl⟩)

/-- `p : (E, p^*T) → (N, T)` is continuous (`RamcovGX.tex:2069`, "it follows from the definitions
that `p` is continuous for the strong topologies"): `p⁻¹(O)` is the union of its components. -/
theorem continuous_strongPullTop (p : E → N) (T : TopologicalSpace N) :
    Continuous[strongPullTop p T, T] p := by
  rw [continuous_def]
  intro O hO
  have h : p ⁻¹' O = ⋃ x ∈ p ⁻¹' O, connectedComponentIn (p ⁻¹' O) x := by
    ext z
    simp only [mem_iUnion]
    exact ⟨fun hz => ⟨z, hz, mem_connectedComponentIn hz⟩,
      fun ⟨x, _, hz⟩ => connectedComponentIn_subset _ _ hz⟩
  rw [h]
  exact @isOpen_biUnion _ _ (strongPullTop p T) _ _ fun x hx =>
    isOpen_strongPullTop_connectedComponentIn p T hO hx

/-- For the topology of `N` itself, and `E` locally connected, `p^*` returns the topology of `E`:
the generators are components of open sets. -/
theorem strongPullTop_self [LocallyConnectedSpace E] [tN : TopologicalSpace N] {p : E → N}
    (hp : Continuous p) : strongPullTop p tN = ‹TopologicalSpace E› :=
  le_antisymm inf_le_left (le_inf le_rfl (le_generateFrom
    fun _ ⟨_, hO, _, _, he⟩ => he ▸ (hO.preimage hp).connectedComponentIn))

/-- The preimage of a component under a homeomorphism is a component. -/
theorem Homeomorph.preimage_connectedComponentIn_strongPull (γ : E ≃ₜ E) (F : Set E) (x : E) :
    γ ⁻¹' connectedComponentIn F x = connectedComponentIn (γ ⁻¹' F) (γ.symm x) := by
  by_cases hx : x ∈ F
  · apply Subset.antisymm
    · have h := γ.symm.continuous.image_connectedComponentIn_subset hx
      simpa only [Homeomorph.image_symm] using h
    · have hx' : γ.symm x ∈ γ ⁻¹' F := by simpa using hx
      have h := γ.continuous.image_connectedComponentIn_subset hx'
      rw [image_preimage_eq _ γ.surjective, Homeomorph.apply_symm_apply] at h
      exact image_subset_iff.1 h
  · have hx' : γ.symm x ∉ γ ⁻¹' F := by simpa using hx
    rw [connectedComponentIn_eq_empty hx, connectedComponentIn_eq_empty hx', preimage_empty]

/-- `lem:spread_top` (d), the paper's argument (l.2071–2073): a homeomorphism `γ` of `E` lying over
a `T`-continuous `γ̄` of `N` (`p ∘ γ = γ̄ ∘ p`) is `p^*T`-continuous. -/
theorem continuous_strongPullTop_of_semiconj (p : E → N) (T : TopologicalSpace N) (γ : E ≃ₜ E)
    {γ' : N → N} (hγ' : Continuous[T, T] γ') (h : ∀ e, p (γ e) = γ' (p e)) :
    Continuous[strongPullTop p T, strongPullTop p T] γ := by
  refine continuous_inf_rng.2 ⟨continuous_le_dom (strongPullTop_le p T) γ.continuous, ?_⟩
  refine continuous_generateFrom_iff.2 ?_
  rintro _ ⟨O, hO, x, hx, rfl⟩
  rw [Homeomorph.preimage_connectedComponentIn_strongPull]
  have hpre : γ ⁻¹' (p ⁻¹' O) = p ⁻¹' (γ' ⁻¹' O) := by
    ext e; simp only [mem_preimage, h]
  rw [hpre]
  refine isOpen_strongPullTop_connectedComponentIn p T (hγ'.isOpen_preimage O hO) ?_
  show γ' (p (γ.symm x)) ∈ O
  rw [← h, Homeomorph.apply_symm_apply]; exact hx

end StrongPull

/-- The automorphisms `Γ(N/M)` of `q : N → M`, as maps (named so that statements with a second
topology on `N` in context can refer to the homeomorphisms of the first). -/
def deckMapsOf {N : Type*} {Y : Type*} [TopologicalSpace N] (q : N → Y) : Set (N → N) :=
  {f | ∃ γ ∈ deckGroup q, ⇑γ = f}

/-- `lem:spread_top` (`RamcovGX.tex:1990`), (d) — the existence of `γ̄` in its proof (l.2071): when
`N → M` is Galoisian and `N` Hausdorff, every `γ ∈ Γ(\widetilde M^S/M)` lies over some
`γ̄ ∈ Γ(N/M)` (`p ∘ γ = γ̄ ∘ p`). `Γ(N/M)` is transitive on the fibre of `q` through `p(z₀)` and
`p(γ z₀)`; `p ∘ γ` and `γ̄ ∘ p` are two lifts of the projection through `q` agreeing at `z₀`
over `ord(q)`, hence equal (`GX.eq_of_comp_eq_of_mem_portly`). Without the Galoisian hypothesis
the paper's step has no justification (finding). -/
theorem exists_deck_semiconj_of_isGaloisian {M : Type u} [TopologicalSpace M] [T2Space M]
    [LocPathConnectedSpace M] [FirstCountableTopology M] [ConnectedSpace M] {S : Set M}
    (hS : IsSkeletal S) (hSc : SemilocallySimplyConnected (Sᶜ : Set M)) (y₀ : (Sᶜ : Set M))
    {N : Type v} [tN : TopologicalSpace N] [T2Space N] {p : MaxBranchedCover S y₀ → N}
    {q : N → M} (hp : IsBranchedCovering p) (hq : IsGaloisian q) (hqp : ∀ e, q (p e) = e.base)
    {γ : MaxBranchedCover S y₀ ≃ₜ MaxBranchedCover S y₀}
    (hγ : γ ∈ deckGroup (SpreadEnd.base : MaxBranchedCover S y₀ → M)) :
    ∃ γ' ∈ deckGroup q, ∀ e, p (γ e) = γ' (p e) := by
  obtain ⟨-, hβbc, -, -, -, -⟩ := maxBranched_basic hS hSc y₀
  obtain ⟨y, hy⟩ := hq.1.isPortly_ordY.dense.nonempty
  obtain ⟨z₀, hz₀⟩ := hβbc.surjective y
  have hfib : q (p z₀) = q (p (γ z₀)) := by rw [hqp, hqp, deck_apply _ hγ]
  obtain ⟨γ', hγ', hγ'z⟩ := hq.2 _ _ hfib
  refine ⟨γ', hγ', fun e => ?_⟩
  have := eq_of_comp_eq_of_mem_portly hβbc hq.1 hq.1.isPortly_ordY subset_rfl
    (hp.isSpread.continuous.comp γ.continuous) (γ'.continuous.comp hp.isSpread.continuous)
    (fun z => by simp only [comp_apply]; rw [hqp, deck_apply _ hγ])
    (fun z => by simp only [comp_apply]; rw [deck_apply _ hγ', hqp])
    (z₀ := z₀) (by rw [hz₀]; exact hy) (by simp only [comp_apply]; exact hγ'z.symm)
  exact congrFun this e

/-- `lem:spread_top` (d) (`RamcovGX.tex:1999`, proof l.2071–2073), proved under the hypothesis its
proof uses: if `N → M` is Galoisian (`N` Hausdorff) and `Γ(N/M)` acts `T`-continuously, then
`Γ(\widetilde M^S/M)` acts `p^*T`-continuously. -/
theorem spread_top_deck {M : Type u} [TopologicalSpace M] [T2Space M] [LocPathConnectedSpace M]
    [FirstCountableTopology M] [ConnectedSpace M] {S : Set M} (hS : IsSkeletal S)
    (hSc : SemilocallySimplyConnected (Sᶜ : Set M)) (y₀ : (Sᶜ : Set M))
    {N : Type v} [tN : TopologicalSpace N] [T2Space N] {p : MaxBranchedCover S y₀ → N}
    {q : N → M} (hp : IsBranchedCovering p) (hq : IsGaloisian q) (hqp : ∀ e, q (p e) = e.base)
    (T : TopologicalSpace N) (hTdeck : ∀ f ∈ @deckMapsOf N M tN q, Continuous[T, T] f) :
    ∀ γ ∈ deckGroup (SpreadEnd.base : MaxBranchedCover S y₀ → M),
      Continuous[strongPullTop p T, strongPullTop p T] γ := by
  intro γ hγ
  obtain ⟨γ', hγ', h⟩ := exists_deck_semiconj_of_isGaloisian (tN := tN) hS hSc y₀ hp hq hqp hγ
  exact continuous_strongPullTop_of_semiconj p T γ (hTdeck _ ⟨γ', hγ', rfl⟩) h

/-! `lem:spread_top` (`RamcovGX.tex:1990`), (a), (b), (c), (e), is not stated here: the printed
statement is FALSE (WP-27k, `GX.not_spreadTopPrinted` on `GX.cex_spread_top_halfCut`, in
`GXScaffold.SingularII.SpreadTop`, which imports this module), and (c), (e) remain false with
`p⁻¹(R)` connected (`GX.not_spreadTopConnCE`, `GX.cex_spread_top_sector`); its strongest true form
is `GX.spread_top_corrected` there. The statement this module carried (with a tagged `sorry`) was
removed at WP-35f. (d) is `spread_top_deck` above. -/

/-! ### `theo:local_virt_tame`, piece (2) when the coverings `ℓ`, `r` are trivial (WP-35f) -/

section LiftUnique

variable {G : Type*} {X : Type*} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
  {N : Type u} [TopologicalSpace N] [T2Space N] [LocPathConnectedSpace N]
  [FirstCountableTopology N] [ConnectedSpace N] [SingularGXStructure G X N]

/-- Uniqueness of lifts into `\widetilde N`: two maps `F₁ F₂ : E → \widetilde N`, continuous on an
open `Z`, with the same projection on `Z`, regular over the dense preconnected open `Z' ⊆ Z`, and
agreeing at one point of `Z'`, agree on `Z`. -/
theorem eqOn_maxBranched_of_base_eq (hregN : SemilocallySimplyConnected ((Sing G X N)ᶜ : Set N))
    {yN : ((Sing G X N)ᶜ : Set N)} {E : Type*} [TopologicalSpace E]
    {F₁ F₂ : E → MaxBranchedCover (Sing G X N) yN} {Z Z' : Set E} (hZ : IsOpen Z)
    (hZ'Z : Z' ⊆ Z) (hZ'o : IsOpen Z') (hZ'c : IsPreconnected Z') (hcl : Z ⊆ closure Z')
    (h₁ : ContinuousOn F₁ Z) (h₂ : ContinuousOn F₂ Z) (hb : ∀ z ∈ Z, (F₁ z).base = (F₂ z).base)
    (hreg : ∀ z ∈ Z', (F₁ z).base ∈ Reg G X N) {z₀ : E} (hz₀ : z₀ ∈ Z') (h0 : F₁ z₀ = F₂ z₀) :
    EqOn F₁ F₂ Z := by
  have hS₀ := isSkeletal_sing G X N
  obtain ⟨-, hβbc, hβS, -, -, -⟩ := maxBranched_basic hS₀ hregN yN
  haveI : T2Space (MaxBranchedCover (Sing G X N) yN) := (maxBranched_instances hS₀ hregN yN).2.2
  have hordβ : Reg G X N ⊆ ordY (SpreadEnd.base : MaxBranchedCover (Sing G X N) yN → N) :=
    fun y hy => by by_contra hn; exact (hβS hn) hy
  -- closedness of the equaliser inside `Z`
  have hclosed : ∀ z ∈ Z, ∀ u : Set E, z ∈ closure u → (∀ w ∈ u, F₁ w = F₂ w) → F₁ z = F₂ z := by
    intro z hz u hzu hu
    haveI : (𝓝[u] z).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hzu
    have c₁ := (h₁.continuousAt (hZ.mem_nhds hz)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := u))
    have c₂ := (h₂.continuousAt (hZ.mem_nhds hz)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := u))
    exact tendsto_nhds_unique c₁ (c₂.congr' (eventually_nhdsWithin_of_forall fun w hw =>
      (hu w hw).symm))
  set Eq₀ : Set E := {z | z ∈ Z' ∧ F₁ z = F₂ z} with hEq₀
  have hEo : IsOpen Eq₀ := by
    refine isOpen_iff_mem_nhds.2 fun z hz => ?_
    obtain ⟨hzZ', hzeq⟩ := hz
    have hzZ := hZ'Z hzZ'
    obtain ⟨e, hve, hpe⟩ := hβbc.ordX_subset_isLocalHomeomorphOn (hordβ (hreg z hzZ'))
      (F₁ z) rfl
    have hc₁ := h₁.continuousAt (hZ.mem_nhds hzZ)
    have hc₂ := h₂.continuousAt (hZ.mem_nhds hzZ)
    have hv₂ : F₂ z ∈ e.source := hzeq ▸ hve
    filter_upwards [hc₁.preimage_mem_nhds (e.open_source.mem_nhds hve),
      hc₂.preimage_mem_nhds (e.open_source.mem_nhds hv₂), hZ'o.mem_nhds hzZ'] with w hw₁ hw₂ hw
    refine ⟨hw, e.injOn hw₁ hw₂ ?_⟩
    rw [← hpe]; exact hb w (hZ'Z hw)
  have hsub : Z' ⊆ Eq₀ := by
    refine hZ'c.subset_of_closure_inter_subset hEo ⟨z₀, hz₀, hz₀, h0⟩ ?_
    rintro z ⟨hzc, hzZ'⟩
    exact ⟨hzZ', hclosed z (hZ'Z hzZ') Eq₀ hzc fun w hw => hw.2⟩
  intro z hz
  exact hclosed z hz Z' (hcl hz) fun w hw => (hsub hw).2

/-- Two lifts with the same projection, regular over a dense preconnected open subset, differ by an
element of `Γ(\widetilde N/N)`. -/
theorem exists_deck_eqOn_of_base_eq (hregN : SemilocallySimplyConnected ((Sing G X N)ᶜ : Set N))
    {yN : ((Sing G X N)ᶜ : Set N)} {E : Type*} [TopologicalSpace E]
    {F₁ F₂ : E → MaxBranchedCover (Sing G X N) yN} {Z Z' : Set E} (hZ : IsOpen Z)
    (hZ'Z : Z' ⊆ Z) (hZ'o : IsOpen Z') (hZ'c : IsPreconnected Z') (hcl : Z ⊆ closure Z')
    (hne : Z'.Nonempty)
    (h₁ : ContinuousOn F₁ Z) (h₂ : ContinuousOn F₂ Z) (hb : ∀ z ∈ Z, (F₁ z).base = (F₂ z).base)
    (hreg : ∀ z ∈ Z', (F₁ z).base ∈ Reg G X N) :
    ∃ δ ∈ deckGroup (SpreadEnd.base : MaxBranchedCover (Sing G X N) yN → N),
      EqOn F₂ (fun z => δ (F₁ z)) Z := by
  have hS₀ := isSkeletal_sing G X N
  obtain ⟨z₀, hz₀⟩ := hne
  obtain ⟨δ, hδ, hδz⟩ := maxBranched_transitive hS₀ hregN yN (F₁ z₀) (F₂ z₀)
    (hb z₀ (hZ'Z hz₀)) (fun h => h (hreg z₀ hz₀))
  refine ⟨δ, hδ, eqOn_maxBranched_of_base_eq hregN hZ hZ'Z hZ'o hZ'c hcl h₂
    (δ.continuous.comp_continuousOn h₁) (fun z hz => ?_) (fun z hz => ?_) hz₀ hδz.symm⟩
  · show (F₂ z).base = (δ (F₁ z)).base
    rw [deck_apply _ hδ, hb z hz]
  · rw [← hb z (hZ'Z hz)]; exact hreg z hz

end LiftUnique


/-- A topology carried as data, so that it is never a local instance (statements below mention
both it and the natural topology of the same type). -/
structure WrappedTop (α : Type*) where
  /-- The topology. -/
  top : TopologicalSpace α

theorem mem_of_mem_connectedComponentIn_preimage {E Y : Type*} [TopologicalSpace E] {p : E → Y}
    {U : Set Y} {z y : E} (h : y ∈ connectedComponentIn (p ⁻¹' U) z) : p y ∈ U :=
  connectedComponentIn_subset (p ⁻¹' U) z h


theorem mem_nhds_iff_of {α : Type*} (t : TopologicalSpace α) {x : α} {s : Set α} :
    s ∈ @nhds α t x ↔ ∃ u ⊆ s, IsOpen[t] u ∧ x ∈ u := by
  letI := t; exact mem_nhds_iff

theorem mem_of_mem_nhds_of {α : Type*} (t : TopologicalSpace α) {x : α} {s : Set α}
    (h : s ∈ @nhds α t x) : x ∈ s := by
  letI := t; exact mem_of_mem_nhds h

theorem eventually_mem_nhds_iff_of {α : Type*} (t : TopologicalSpace α) {x : α} {s : Set α} :
    (∀ᶠ y in @nhds α t x, s ∈ @nhds α t y) ↔ s ∈ @nhds α t x := by
  letI := t; exact eventually_mem_nhds_iff

theorem eventually_nhdsWithin_of_forall_of {α : Type*} (t : TopologicalSpace α) {x : α}
    {s : Set α} {p : α → Prop} (h : ∀ y ∈ s, p y) : ∀ᶠ y in @nhdsWithin α t x s, p y := by
  letI := t; exact eventually_nhdsWithin_of_forall h

theorem nhdsWithin_le_nhds_of {α : Type*} (t : TopologicalSpace α) {x : α} {s : Set α} :
    @nhdsWithin α t x s ≤ @nhds α t x := by
  letI := t; exact nhdsWithin_le_nhds


theorem isOpen_iff_mem_nhds_of {α : Type*} (t : TopologicalSpace α) {s : Set α} :
    IsOpen[t] s ↔ ∀ x ∈ s, s ∈ @nhds α t x := by
  letI := t; exact isOpen_iff_mem_nhds

theorem mem_closure_iff_nhds_of {α : Type*} (t : TopologicalSpace α) {x : α} {s : Set α} :
    x ∈ @closure α t s ↔ ∀ u ∈ @nhds α t x, (u ∩ s).Nonempty := by
  letI := t; exact mem_closure_iff_nhds

theorem isPathConnected_image_of {α β : Type*} (t₁ : TopologicalSpace α)
    (t₂ : TopologicalSpace β) {s : Set α} (hs : @IsPathConnected α t₁ s) {f : α → β}
    (hf : @ContinuousOn α β t₁ t₂ f s) : @IsPathConnected β t₂ (f '' s) := by
  letI := t₁; letI := t₂; exact hs.image' hf

theorem isPreconnected_image_of {α β : Type*} (t₁ : TopologicalSpace α)
    (t₂ : TopologicalSpace β) {s : Set α} (hs : @IsPreconnected α t₁ s) {f : α → β}
    (hf : @ContinuousOn α β t₁ t₂ f s) : @IsPreconnected β t₂ (f '' s) := by
  letI := t₁; letI := t₂; exact hs.image f hf


theorem continuousOn_mono_of {α β : Type*} (t₁ : TopologicalSpace α) (t₂ : TopologicalSpace β)
    {f : α → β} {s s' : Set α} (h : @ContinuousOn α β t₁ t₂ f s) (hs : s' ⊆ s) :
    @ContinuousOn α β t₁ t₂ f s' := by
  letI := t₁; letI := t₂; exact h.mono hs


theorem mem_closure_of_dense_of {α : Type*} (t : TopologicalSpace α) {s : Set α}
    (h : @Dense α t s) (x : α) : x ∈ @closure α t s := by
  letI := t; exact h x

theorem isPreconnected_inter_of_isPortly_of {α : Type*} (t : TopologicalSpace α) {U W : Set α}
    (h : @IsPortly α t U) (hW : IsOpen[t] W) (hWc : @IsPreconnected α t W) :
    @IsPreconnected α t (W ∩ U) := by
  letI := t; exact h.locallyConnectedIn W hW hWc

theorem isPreconnected_empty_of {α : Type*} (t : TopologicalSpace α) :
    @IsPreconnected α t ∅ := by
  letI := t; exact isPreconnected_empty


theorem continuousOn_of_continuous_of {α β : Type*} (t₁ : TopologicalSpace α)
    (t₂ : TopologicalSpace β) {f : α → β} (h : @Continuous α β t₁ t₂ f) (s : Set α) :
    @ContinuousOn α β t₁ t₂ f s := by
  letI := t₁; letI := t₂; exact h.continuousOn


theorem continuous_comp_of {α β γ : Type*} (t₁ : TopologicalSpace α) (t₂ : TopologicalSpace β)
    (t₃ : TopologicalSpace γ) {g : β → γ} {f : α → β} (hg : @Continuous β γ t₂ t₃ g)
    (hf : @Continuous α β t₁ t₂ f) : @Continuous α γ t₁ t₃ (fun x => g (f x)) := by
  letI := t₁; letI := t₂; letI := t₃; exact hg.comp hf

/-- `comap f (𝓝 (f x)) = 𝓝 x` for a map continuous with a continuous inverse (explicit
topologies). -/
theorem comap_nhds_eq_of_leftInverse {Y : Type*} {t : TopologicalSpace Y} {f g : Y → Y}
    (hf : Continuous[t, t] f) (hg : Continuous[t, t] g) (hgf : ∀ y, g (f y) = y) (y : Y) :
    Filter.comap f (@nhds Y t (f y)) = @nhds Y t y := by
  refine le_antisymm (fun s hs => ?_) (@Continuous.tendsto Y Y t t f hf y).le_comap
  refine ⟨g ⁻¹' s, ?_, fun z hz => by simpa [hgf] using hz⟩
  have := (@Continuous.tendsto Y Y t t g hg (f y))
  rw [hgf] at this
  exact this hs

/-- Restricting a `comap` to a set on which two maps agree. -/
theorem principal_inf_comap_congr {E Y : Type*} {A : Set E} {f g : E → Y} (h : EqOn f g A)
    (F : Filter Y) : 𝓟 A ⊓ Filter.comap f F = 𝓟 A ⊓ Filter.comap g F := by
  rw [inf_comm, inf_comm (𝓟 A)]
  ext s
  rw [mem_inf_principal, mem_inf_principal, Filter.mem_comap, Filter.mem_comap]
  constructor
  · rintro ⟨t, ht, hts⟩
    exact ⟨t, ht, fun z hz hzA => hts (show f z ∈ t by rw [h hzA]; exact hz) hzA⟩
  · rintro ⟨t, ht, hts⟩
    exact ⟨t, ht, fun z hz hzA => hts (show g z ∈ t by rw [← h hzA]; exact hz) hzA⟩


section ChartLift

variable {G : Type*} {X : Type*} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
  {M : Type v} [TopologicalSpace M] [T2Space M] [LocPathConnectedSpace M]
  [FirstCountableTopology M] [ConnectedSpace M] [SingularGXStructure G X M]
  {N : Type u} [TopologicalSpace N] [T2Space N] [LocPathConnectedSpace N]
  [FirstCountableTopology N] [ConnectedSpace N] [SingularGXStructure G X N]

/-- An isomorphism `φ : U → V` of open subsets, read as a map `M → N` (any value off `U`). -/
def chartExt {U : Opens M} {V : Opens N} (φ : U ≃ₜ V) : M → N := fun m =>
  if h : m ∈ U then (φ ⟨m, h⟩ : N) else Classical.arbitrary N

theorem chartExt_apply {U : Opens M} {V : Opens N} (φ : U ≃ₜ V) {m : M} (hm : m ∈ U) :
    chartExt φ m = (φ ⟨m, hm⟩ : N) := dif_pos hm

theorem continuousOn_chartExt {U : Opens M} {V : Opens N} (φ : U ≃ₜ V) :
    ContinuousOn (chartExt φ) (U : Set M) := by
  rw [continuousOn_iff_continuous_restrict]
  have : (U : Set M).restrict (chartExt φ) = fun m : U => (φ m : N) := by
    funext m; exact chartExt_apply φ m.2
  rw [this]
  exact continuous_subtype_val.comp φ.continuous

theorem chartExt_mem_reg_iff {U : Opens M} {V : Opens N} {φ : U ≃ₜ V}
    (hφ : IsAEMorphism G X (φ : U → V)) {m : M} (hm : m ∈ U) :
    chartExt φ m ∈ Reg G X N ↔ m ∈ Reg G X M := by
  have h := (IsAEMorphism.preimage_reg_sing hφ φ.isLocalHomeomorph).1
  rw [chartExt_apply φ hm]
  have h1 : (φ ⟨m, hm⟩ : N) ∈ Reg G X N ↔ φ ⟨m, hm⟩ ∈ Reg G X V := by
    rw [reg_opensSingular V]; rfl
  have h2 : (⟨m, hm⟩ : U) ∈ Reg G X U ↔ m ∈ Reg G X M := by
    rw [reg_opensSingular U]; rfl
  rw [h1, ← h2, ← h]; rfl

variable (G X) in
/-- An isomorphism `φ : U → V` of open subsets of `M` and of a model `N` *lifts to the maximal
coverings* if, for every pair of points `e ∈ \widetilde M` over `U` and `f ∈ \widetilde N` over
`φ(p e)`, the components `Uh ∋ e` of `p⁻¹(U)` and `Vh ∋ f` of `q⁻¹(V)` are homeomorphic over `φ` by
a homeomorphism sending `e` to `f` (`\widetilde M`, `\widetilde N` for every base point). This is
the case of the proof of `theo:local_virt_tame` where its coverings `Ũ → Uh` and `Ṽ → Vh` are
isomorphisms; the `Ũ → Uh` half is removed by `IsDescendingChartMap` (which it implies,
`IsLiftableChartMap.isDescendingChartMap`, and under which the theorem is proved,
`isVirtuallyTame_of_descending`). -/
def IsLiftableChartMap {U : Opens M} {V : Opens N} (φ : U ≃ₜ V) : Prop :=
  ∀ (y₀ : ((Sing G X M)ᶜ : Set M)) (yN : ((Sing G X N)ᶜ : Set N))
    (e : MaxBranchedCover (Sing G X M) y₀) (f : MaxBranchedCover (Sing G X N) yN)
    (he : e.base ∈ U), f.base = (φ ⟨e.base, he⟩ : N) →
    ∃ Φ : connectedComponentIn
        ((SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) ⁻¹' U) e ≃ₜ
        connectedComponentIn ((SpreadEnd.base : MaxBranchedCover (Sing G X N) yN → N) ⁻¹' V) f,
      (Φ ⟨e, mem_connectedComponentIn he⟩ : MaxBranchedCover (Sing G X N) yN) = f ∧
      ∀ z, (Φ z : MaxBranchedCover (Sing G X N) yN).base =
        (φ ⟨(z : MaxBranchedCover (Sing G X M) y₀).base,
          mem_preimage.1 (connectedComponentIn_subset _ _ z.2)⟩ : N)

/-- A lift of `φ' : M → N` from the component `Uh ∋ e` of `p⁻¹(U)` onto the component `Vh ∋ f` of
`q⁻¹(V)`, as a pair of maps of the whole spaces, mutually inverse continuous on `Uh`, `Vh`. -/
structure IsChartLift {y₀ : ((Sing G X M)ᶜ : Set M)} {yN : ((Sing G X N)ᶜ : Set N)}
    (U : Set M) (V : Set N) (φ' : M → N) (e : MaxBranchedCover (Sing G X M) y₀)
    (f : MaxBranchedCover (Sing G X N) yN)
    (F : MaxBranchedCover (Sing G X M) y₀ → MaxBranchedCover (Sing G X N) yN)
    (F' : MaxBranchedCover (Sing G X N) yN → MaxBranchedCover (Sing G X M) y₀) : Prop where
  apply_self : F e = f
  mapsTo : MapsTo F (connectedComponentIn (SpreadEnd.base ⁻¹' U) e)
    (connectedComponentIn (SpreadEnd.base ⁻¹' V) f)
  mapsTo' : MapsTo F' (connectedComponentIn (SpreadEnd.base ⁻¹' V) f)
    (connectedComponentIn (SpreadEnd.base ⁻¹' U) e)
  left : ∀ z ∈ connectedComponentIn (SpreadEnd.base ⁻¹' U) e, F' (F z) = z
  right : ∀ w ∈ connectedComponentIn (SpreadEnd.base ⁻¹' V) f, F (F' w) = w
  contF : ContinuousOn F (connectedComponentIn (SpreadEnd.base ⁻¹' U) e)
  contF' : ContinuousOn F' (connectedComponentIn (SpreadEnd.base ⁻¹' V) f)
  base : ∀ z ∈ connectedComponentIn (SpreadEnd.base ⁻¹' U) e, (F z).base = φ' z.base

theorem IsLiftableChartMap.exists_isChartLift {U : Opens M} {V : Opens N} {φ : U ≃ₜ V}
    (hφ : IsLiftableChartMap G X φ) {y₀ : ((Sing G X M)ᶜ : Set M)}
    {yN : ((Sing G X N)ᶜ : Set N)} (e : MaxBranchedCover (Sing G X M) y₀)
    (f : MaxBranchedCover (Sing G X N) yN) (he : e.base ∈ U)
    (hf : f.base = (φ ⟨e.base, he⟩ : N)) :
    ∃ F F', IsChartLift (U : Set M) (V : Set N) (chartExt φ) e f F F' := by
  set Uh := connectedComponentIn
    ((SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) ⁻¹' U) e
  set Vh := connectedComponentIn
    ((SpreadEnd.base : MaxBranchedCover (Sing G X N) yN → N) ⁻¹' V) f
  obtain ⟨Φ, hΦe, hΦb⟩ := hφ y₀ yN e f he hf
  let F : MaxBranchedCover (Sing G X M) y₀ → MaxBranchedCover (Sing G X N) yN := fun z =>
    if h : z ∈ Uh then (Φ ⟨z, h⟩ : MaxBranchedCover (Sing G X N) yN) else f
  let F' : MaxBranchedCover (Sing G X N) yN → MaxBranchedCover (Sing G X M) y₀ := fun w =>
    if h : w ∈ Vh then (Φ.symm ⟨w, h⟩ : MaxBranchedCover (Sing G X M) y₀) else e
  have hF : ∀ z (h : z ∈ Uh), F z = Φ ⟨z, h⟩ := fun z h => dif_pos h
  have hF' : ∀ w (h : w ∈ Vh), F' w = Φ.symm ⟨w, h⟩ := fun w h => dif_pos h
  have heUh : e ∈ Uh := mem_connectedComponentIn he
  refine ⟨F, F', ⟨by rw [hF e heUh]; exact hΦe, fun z hz => by rw [hF z hz]; exact (Φ _).2,
    fun w hw => by rw [hF' w hw]; exact (Φ.symm _).2, fun z hz => ?_, fun w hw => ?_, ?_, ?_,
    fun z hz => ?_⟩⟩
  · have h1 : F z ∈ Vh := by rw [hF z hz]; exact (Φ _).2
    rw [hF' _ h1]
    have : (⟨F z, h1⟩ : Vh) = Φ ⟨z, hz⟩ := Subtype.ext (hF z hz)
    rw [this, Homeomorph.symm_apply_apply]
  · have h1 : F' w ∈ Uh := by rw [hF' w hw]; exact (Φ.symm _).2
    rw [hF _ h1]
    have : (⟨F' w, h1⟩ : Uh) = Φ.symm ⟨w, hw⟩ := Subtype.ext (hF' w hw)
    rw [this, Homeomorph.apply_symm_apply]
  · rw [continuousOn_iff_continuous_restrict]
    have : Uh.restrict F = fun z : Uh => (Φ z : MaxBranchedCover (Sing G X N) yN) := by
      funext z; exact hF z z.2
    rw [this]; exact continuous_subtype_val.comp Φ.continuous
  · rw [continuousOn_iff_continuous_restrict]
    have : Vh.restrict F' = fun w : Vh => (Φ.symm w : MaxBranchedCover (Sing G X M) y₀) := by
      funext w; exact hF' w w.2
    rw [this]; exact continuous_subtype_val.comp Φ.symm.continuous
  · rw [hF z hz, hΦb, chartExt_apply φ (mem_preimage.1 (connectedComponentIn_subset _ _ hz))]

/-- The components of `p⁻¹(U)` in `\widetilde M`: open, with a dense preconnected open regular
part. -/
theorem maxBranched_cc_facts (hregM : SemilocallySimplyConnected ((Sing G X M)ᶜ : Set M))
    {y₀ : ((Sing G X M)ᶜ : Set M)} {U : Set M} (hU : IsOpen U)
    {z : MaxBranchedCover (Sing G X M) y₀} (hz : z.base ∈ U) :
    let Z := connectedComponentIn
      ((SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) ⁻¹' U) z
    IsOpen Z ∧ IsOpen (Z ∩ SpreadEnd.base ⁻¹' Reg G X M) ∧
      IsPreconnected (Z ∩ SpreadEnd.base ⁻¹' Reg G X M) ∧
      Z ⊆ closure (Z ∩ SpreadEnd.base ⁻¹' Reg G X M) ∧
      (Z ∩ SpreadEnd.base ⁻¹' Reg G X M).Nonempty := by
  intro Z
  have hS₀ := isSkeletal_sing G X M
  obtain ⟨-, hβbc, -, -, hβl, -⟩ := maxBranched_basic hS₀ hregM y₀
  haveI := hβl
  have hR := hβbc.isPortly_preimage (isPortly_reg G X M)
  have hZo : IsOpen Z := (hU.preimage hβbc.isSpread.continuous).connectedComponentIn
  have hcl : Z ⊆ closure (Z ∩ SpreadEnd.base ⁻¹' Reg G X M) := fun x hx =>
    hZo.inter_closure ⟨hx, hR.dense x⟩
  refine ⟨hZo, hZo.inter hR.isOpen, hR.locallyConnectedIn Z hZo
    isPreconnected_connectedComponentIn, hcl, ?_⟩
  exact closure_nonempty_iff.1 ⟨z, hcl (mem_connectedComponentIn hz)⟩

end ChartLift

section ChartTop

variable {G : Type*} {X : Type*} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
  {M : Type v} [TopologicalSpace M] [T2Space M] [LocPathConnectedSpace M]
  [FirstCountableTopology M] [ConnectedSpace M] [SingularGXStructure G X M]
  {N : Type u} [TopologicalSpace N] [T2Space N] [LocPathConnectedSpace N]
  [FirstCountableTopology N] [ConnectedSpace N] [SingularGXStructure G X N]
  {y₀ : ((Sing G X M)ᶜ : Set M)} {yN : ((Sing G X N)ᶜ : Set N)}

/-- The neighbourhoods of the topology `T_{U,V,φ}` transported from a topology `T_N` of
`\widetilde N` through chosen lifts `Fz z` (one for each `z` over `U`); the natural ones off
`p⁻¹(U)`. -/
def chartNhds (U : Set M)
    (Fz : MaxBranchedCover (Sing G X M) y₀ → MaxBranchedCover (Sing G X M) y₀ →
      MaxBranchedCover (Sing G X N) yN)
    (TN : WrappedTop (MaxBranchedCover (Sing G X N) yN))
    (z : MaxBranchedCover (Sing G X M) y₀) : Filter (MaxBranchedCover (Sing G X M) y₀) :=
  if z.base ∈ U then 𝓟 (connectedComponentIn (SpreadEnd.base ⁻¹' U) z) ⊓
    Filter.comap (Fz z) (@nhds _ TN.top (Fz z z)) else 𝓝 z

/-- The topology `T_{U,V,φ}` (`RamcovGX.tex:2093–2098`), in the case its coverings `ℓ`, `r` are
isomorphisms: on each component `Û` of `p⁻¹(U)`, `T_N` transported by a lift `Û ≅ V̂` of `φ`;
the natural topology off `p⁻¹(U)`. -/
@[reducible] def chartTop (U : Set M)
    (Fz : MaxBranchedCover (Sing G X M) y₀ → MaxBranchedCover (Sing G X M) y₀ →
      MaxBranchedCover (Sing G X N) yN)
    (TN : WrappedTop (MaxBranchedCover (Sing G X N) yN)) :
    TopologicalSpace (MaxBranchedCover (Sing G X M) y₀) :=
  TopologicalSpace.mkOfNhds (chartNhds U Fz TN)

variable {U : Set M} {V : Set N} {φ' : M → N}
  {Fz : MaxBranchedCover (Sing G X M) y₀ → MaxBranchedCover (Sing G X M) y₀ →
      MaxBranchedCover (Sing G X N) yN}
  {TN : WrappedTop (MaxBranchedCover (Sing G X N) yN)}

/-- An element of `Γ(\widetilde N/N)` is a homeomorphism of a tamifying topology. -/
theorem comap_deck_nhds_of_isTamifying (hTN : IsTamifyingTopology G X N yN TN.top)
    {δ : MaxBranchedCover (Sing G X N) yN ≃ₜ MaxBranchedCover (Sing G X N) yN}
    (hδ : δ ∈ deckGroup (SpreadEnd.base : MaxBranchedCover (Sing G X N) yN → N))
    (v : MaxBranchedCover (Sing G X N) yN) :
    Filter.comap δ (@nhds _ TN.top (δ v)) = @nhds _ TN.top v :=
  comap_nhds_eq_of_leftInverse (hTN.continuous_deck _ ⟨δ, hδ, rfl⟩)
    (hTN.continuous_deck _ ⟨δ⁻¹, inv_mem hδ, rfl⟩) (fun y => δ.symm_apply_apply y) v

theorem continuous_deck_of_isTamifying (hTN : IsTamifyingTopology G X N yN TN.top)
    {δ : MaxBranchedCover (Sing G X N) yN ≃ₜ MaxBranchedCover (Sing G X N) yN}
    (hδ : δ ∈ deckGroup (SpreadEnd.base : MaxBranchedCover (Sing G X N) yN → N)) :
    Continuous[TN.top, TN.top] δ :=
  hTN.continuous_deck _ ⟨δ, hδ, rfl⟩

/-- Two chosen lifts over the same component differ by an element of `Γ(\widetilde N/N)`. -/
theorem chartLift_indep (hregM : SemilocallySimplyConnected ((Sing G X M)ᶜ : Set M))
    (hregN : SemilocallySimplyConnected ((Sing G X N)ᶜ : Set N)) (hU : IsOpen U)
    (hF : ∀ z : MaxBranchedCover (Sing G X M) y₀, z.base ∈ U →
      ∃ F', IsChartLift U V φ' z (Fz z z) (Fz z) F')
    (hφreg : ∀ m ∈ U, φ' m ∈ Reg G X N ↔ m ∈ Reg G X M)
    {z y : MaxBranchedCover (Sing G X M) y₀} (hz : z.base ∈ U)
    (hy : y ∈ connectedComponentIn (SpreadEnd.base ⁻¹' U) z) :
    ∃ δ ∈ deckGroup (SpreadEnd.base : MaxBranchedCover (Sing G X N) yN → N),
      EqOn (Fz y) (fun w => δ (Fz z w)) (connectedComponentIn (SpreadEnd.base ⁻¹' U) z) := by
  have hyU : y.base ∈ U := mem_of_mem_connectedComponentIn_preimage hy
  have hyz := connectedComponentIn_eq hy
  obtain ⟨hZo, hZ'o, hZ'c, hcl, hne⟩ := maxBranched_cc_facts hregM hU hz
  obtain ⟨Fz', hFz⟩ := hF z hz
  obtain ⟨Fy', hFy⟩ := hF y hyU
  have hcy : ContinuousOn (Fz y) (connectedComponentIn (SpreadEnd.base ⁻¹' U) z) := by
    rw [hyz]; exact hFy.contF
  refine exists_deck_eqOn_of_base_eq hregN hZo inter_subset_left hZ'o hZ'c hcl hne hFz.contF hcy
    (fun w hw => ?_) (fun w hw => ?_)
  · rw [hFz.base w hw, hFy.base w (hyz ▸ hw)]
  · rw [hFz.base w hw.1]
    exact (hφreg _ (mem_of_mem_connectedComponentIn_preimage hw.1)).2 hw.2

theorem chartNhds_eq (hregM : SemilocallySimplyConnected ((Sing G X M)ᶜ : Set M))
    (hregN : SemilocallySimplyConnected ((Sing G X N)ᶜ : Set N)) (hU : IsOpen U)
    (hF : ∀ z : MaxBranchedCover (Sing G X M) y₀, z.base ∈ U →
      ∃ F', IsChartLift U V φ' z (Fz z z) (Fz z) F')
    (hφreg : ∀ m ∈ U, φ' m ∈ Reg G X N ↔ m ∈ Reg G X M)
    (hTN : IsTamifyingTopology G X N yN TN.top)
    {z y : MaxBranchedCover (Sing G X M) y₀} (hz : z.base ∈ U)
    (hy : y ∈ connectedComponentIn (SpreadEnd.base ⁻¹' U) z) :
    chartNhds U Fz TN y = 𝓟 (connectedComponentIn (SpreadEnd.base ⁻¹' U) z) ⊓
      Filter.comap (Fz z) (@nhds _ TN.top (Fz z y)) := by
  have hyU : y.base ∈ U := mem_of_mem_connectedComponentIn_preimage hy
  have hyz := connectedComponentIn_eq hy
  obtain ⟨δ, hδ, hEq⟩ := chartLift_indep hregM hregN hU hF hφreg hz hy
  rw [chartNhds, if_pos hyU, ← hyz, principal_inf_comap_congr hEq, hEq hy,
    ← comap_deck_nhds_of_isTamifying hTN hδ (Fz z y), Filter.comap_comap]
  rfl

theorem chartNhds_le (hregM : SemilocallySimplyConnected ((Sing G X M)ᶜ : Set M))
    (hregN : SemilocallySimplyConnected ((Sing G X N)ᶜ : Set N)) (hU : IsOpen U) (hV : IsOpen V)
    (hF : ∀ z : MaxBranchedCover (Sing G X M) y₀, z.base ∈ U →
      ∃ F', IsChartLift U V φ' z (Fz z z) (Fz z) F')
    (hTN : IsTamifyingTopology G X N yN TN.top) (y : MaxBranchedCover (Sing G X M) y₀) :
    chartNhds U Fz TN y ≤ 𝓝 y := by
  unfold chartNhds
  split_ifs with hy
  · intro s hs
    obtain ⟨F', hFy⟩ := hF y hy
    have hS₀ := isSkeletal_sing G X N
    obtain ⟨-, hβbc, -, -, hβl, -⟩ := maxBranched_basic hS₀ hregN yN
    haveI := hβl
    obtain ⟨hZo, -⟩ := maxBranched_cc_facts hregM hU hy
    have hyZ : y ∈ connectedComponentIn (SpreadEnd.base ⁻¹' U) y := mem_connectedComponentIn hy
    have hVo : IsOpen (connectedComponentIn
        ((SpreadEnd.base : MaxBranchedCover (Sing G X N) yN → N) ⁻¹' V) (Fz y y)) :=
      (hV.preimage hβbc.isSpread.continuous).connectedComponentIn
    have hFyV := hFy.mapsTo hyZ
    have hc' := hFy.contF'.continuousAt (hVo.mem_nhds hFyV)
    rw [ContinuousAt, hFy.left y hyZ] at hc'
    have ht : F' ⁻¹' (s ∩ connectedComponentIn (SpreadEnd.base ⁻¹' U) y) ∩
        connectedComponentIn (SpreadEnd.base ⁻¹' V) (Fz y y) ∈ @nhds _ TN.top (Fz y y) :=
      nhds_mono hTN.le_natural (Filter.inter_mem (hc' (Filter.inter_mem hs (hZo.mem_nhds hyZ)))
        (hVo.mem_nhds hFyV))
    refine Filter.mem_inf_of_inter (mem_principal_self _) (Filter.preimage_mem_comap ht) ?_
    rintro w ⟨hwZ, hw, -⟩
    have := hw.1
    rwa [hFy.left w hwZ] at this
  · exact le_rfl

/-- A tamifying topology has the natural neighbourhoods at the points over `reg N`. -/
theorem IsTamifyingTopology.nhds_eq_of_reg
    (hregN : SemilocallySimplyConnected ((Sing G X N)ᶜ : Set N)) {T : WrappedTop
      (MaxBranchedCover (Sing G X N) yN)} (hT : IsTamifyingTopology G X N yN T.top)
    {r : MaxBranchedCover (Sing G X N) yN} (hr : r.base ∈ Reg G X N) :
    @nhds _ T.top r = 𝓝 r := by
  refine le_antisymm (nhds_mono hT.le_natural) fun s hs => ?_
  obtain ⟨W, hWs, hWo, heW⟩ := (mem_nhds_iff_of T.top).1 hs
  obtain ⟨V, hV, heV, hVW⟩ := hT.exists_isOpen_subset hregN hWo heW hr
  exact Filter.mem_of_superset (hV.mem_nhds heV) (hVW.trans hWs)

variable (hregM : SemilocallySimplyConnected ((Sing G X M)ᶜ : Set M))
  (hregN : SemilocallySimplyConnected ((Sing G X N)ᶜ : Set N)) (hU : IsOpen U) (hV : IsOpen V)
  (hF : ∀ z : MaxBranchedCover (Sing G X M) y₀, z.base ∈ U →
      ∃ F', IsChartLift U V φ' z (Fz z z) (Fz z) F')
  (hφreg : ∀ m ∈ U, φ' m ∈ Reg G X N ↔ m ∈ Reg G X M)
  (hTN : IsTamifyingTopology G X N yN TN.top)
include hregM hregN hU hV hF hφreg hTN

theorem nhds_chartTop (y : MaxBranchedCover (Sing G X M) y₀) :
    @nhds _ (chartTop U Fz TN) y = chartNhds U Fz TN y := by
  refine nhds_mkOfNhds _ _ (fun z => ?_) (fun z s hs => ?_)
  · unfold chartNhds
    split_ifs with hz
    · exact le_inf ((pure_le_principal _).2 (mem_connectedComponentIn hz))
        (tendsto_pure_left.2 fun s hs => mem_of_mem_nhds_of TN.top hs).le_comap
    · exact pure_le_nhds z
  · by_cases hz : z.base ∈ U
    · have hs' := hs
      rw [chartNhds, if_pos hz] at hs'
      obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := Filter.mem_inf_iff_superset.1 hs'
      obtain ⟨t, ht, htt₂⟩ := Filter.mem_comap.1 ht₂
      have e1 : ∀ᶠ w in chartNhds U Fz TN z, w ∈ connectedComponentIn (SpreadEnd.base ⁻¹' U) z := by
        rw [chartNhds, if_pos hz]; exact Filter.mem_inf_of_left (mem_principal_self _)
      have e2 : ∀ᶠ w in chartNhds U Fz TN z, t ∈ @nhds _ TN.top (Fz z w) := by
        rw [chartNhds, if_pos hz]
        exact Filter.mem_inf_of_right (Filter.preimage_mem_comap
          ((eventually_mem_nhds_iff_of TN.top).2 ht))
      filter_upwards [e1, e2] with w hw1 hw2
      rw [chartNhds_eq hregM hregN hU hF hφreg hTN hz hw1]
      exact Filter.mem_inf_of_inter (mem_principal_self _) (Filter.preimage_mem_comap hw2)
        fun x hx => hsub ⟨mem_principal.1 ht₁ hx.1, htt₂ hx.2⟩
    · rw [chartNhds, if_neg hz] at hs ⊢
      filter_upwards [eventually_mem_nhds_iff.2 hs] with w hw
      exact chartNhds_le hregM hregN hU hV hF hTN w hw

/-- The neighbourhoods of `T_{U,V,φ}` at a point of a component `Û`, read through ANY lift of `φ`
from `Û`. -/
theorem nhds_chartTop_eq_of_isChartLift {z : MaxBranchedCover (Sing G X M) y₀}
    (hz : z.base ∈ U) {f : MaxBranchedCover (Sing G X N) yN}
    {G' : MaxBranchedCover (Sing G X M) y₀ → MaxBranchedCover (Sing G X N) yN}
    {G'' : MaxBranchedCover (Sing G X N) yN → MaxBranchedCover (Sing G X M) y₀}
    (hG : IsChartLift U V φ' z f G' G'') {y : MaxBranchedCover (Sing G X M) y₀}
    (hy : y ∈ connectedComponentIn (SpreadEnd.base ⁻¹' U) z) :
    @nhds _ (chartTop U Fz TN) y = 𝓟 (connectedComponentIn (SpreadEnd.base ⁻¹' U) z) ⊓
      Filter.comap G' (@nhds _ TN.top (G' y)) := by
  rw [nhds_chartTop hregM hregN hU hV hF hφreg hTN, chartNhds_eq hregM hregN hU hF hφreg hTN hz hy]
  obtain ⟨hZo, hZ'o, hZ'c, hcl, hne⟩ := maxBranched_cc_facts hregM hU hz
  obtain ⟨Fz', hFz⟩ := hF z hz
  obtain ⟨δ, hδ, hEq⟩ := exists_deck_eqOn_of_base_eq hregN hZo inter_subset_left hZ'o hZ'c hcl hne
    hFz.contF hG.contF (fun w hw => by rw [hFz.base w hw, hG.base w hw]) (fun w hw => by
      rw [hFz.base w hw.1]
      exact (hφreg _ (mem_of_mem_connectedComponentIn_preimage hw.1)).2 hw.2)
  rw [principal_inf_comap_congr hEq, hEq hy, ← comap_deck_nhds_of_isTamifying hTN hδ (Fz z y),
    Filter.comap_comap]
  rfl

/-- The image by a lift of a `T_{U,V,φ}`-neighbourhood inside `Û` is a `T_N`-neighbourhood. -/
theorem image_mem_nhds_of_isChartLift {z : MaxBranchedCover (Sing G X M) y₀}
    (hz : z.base ∈ U) {f : MaxBranchedCover (Sing G X N) yN}
    {G' : MaxBranchedCover (Sing G X M) y₀ → MaxBranchedCover (Sing G X N) yN}
    {G'' : MaxBranchedCover (Sing G X N) yN → MaxBranchedCover (Sing G X M) y₀}
    (hG : IsChartLift U V φ' z f G' G'') {y : MaxBranchedCover (Sing G X M) y₀}
    (hy : y ∈ connectedComponentIn (SpreadEnd.base ⁻¹' U) z) {A : Set (MaxBranchedCover (Sing G X M) y₀)}
    (hA : A ∈ @nhds _ (chartTop U Fz TN) y) : G' '' A ∈ @nhds _ TN.top (G' y) := by
  rw [nhds_chartTop_eq_of_isChartLift hregM hregN hU hV hF hφreg hTN hz hG hy] at hA
  obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := Filter.mem_inf_iff_superset.1 hA
  obtain ⟨t, ht, htt₂⟩ := Filter.mem_comap.1 ht₂
  have hS₀ := isSkeletal_sing G X N
  obtain ⟨-, hβbc, -, -, hβl, -⟩ := maxBranched_basic hS₀ hregN yN
  haveI := hβl
  have hVo : IsOpen (connectedComponentIn
      ((SpreadEnd.base : MaxBranchedCover (Sing G X N) yN → N) ⁻¹' V) f) :=
    (hV.preimage hβbc.isSpread.continuous).connectedComponentIn
  have hVn : connectedComponentIn (SpreadEnd.base ⁻¹' V) f ∈ @nhds _ TN.top (G' y) :=
    nhds_mono hTN.le_natural (hVo.mem_nhds (hG.mapsTo hy))
  refine Filter.mem_of_superset (Filter.inter_mem ht hVn) fun v hv => ?_
  refine ⟨G'' v, hsub ⟨mem_principal.1 ht₁ (hG.mapsTo' hv.2), htt₂ ?_⟩, hG.right v hv.2⟩
  show G' (G'' v) ∈ t
  rw [hG.right v hv.2]; exact hv.1

theorem tendsto_chartTop_lift {z y : MaxBranchedCover (Sing G X M) y₀} (hz : z.base ∈ U)
    (hy : y ∈ connectedComponentIn (SpreadEnd.base ⁻¹' U) z) :
    Tendsto (Fz z) (@nhds _ (chartTop U Fz TN) y) (@nhds _ TN.top (Fz z y)) := by
  rw [nhds_chartTop hregM hregN hU hV hF hφreg hTN, chartNhds_eq hregM hregN hU hF hφreg hTN hz hy]
  exact tendsto_comap.mono_left inf_le_right

theorem continuousOn_chartTop_inv {z : MaxBranchedCover (Sing G X M) y₀} (hz : z.base ∈ U)
    {F' : MaxBranchedCover (Sing G X N) yN → MaxBranchedCover (Sing G X M) y₀}
    (hFz : IsChartLift U V φ' z (Fz z z) (Fz z) F') :
    @ContinuousOn _ _ TN.top (chartTop U Fz TN) F'
      (connectedComponentIn (SpreadEnd.base ⁻¹' V) (Fz z z)) := by
  intro v hv
  show Tendsto F' (@nhdsWithin _ TN.top v _) (@nhds _ (chartTop U Fz TN) (F' v))
  rw [nhds_chartTop hregM hregN hU hV hF hφreg hTN,
    chartNhds_eq hregM hregN hU hF hφreg hTN hz (hFz.mapsTo' hv), hFz.right v hv]
  refine tendsto_inf.2 ⟨tendsto_principal.2 (eventually_nhdsWithin_of_forall_of TN.top
    fun v' hv' => hFz.mapsTo' hv'), tendsto_comap_iff.2 ?_⟩
  have h1 : Tendsto (fun v' => v') (@nhdsWithin _ TN.top v
      (connectedComponentIn (SpreadEnd.base ⁻¹' V) (Fz z z))) (@nhds _ TN.top v) :=
    nhdsWithin_le_nhds_of TN.top
  exact h1.congr' (eventually_nhdsWithin_of_forall_of TN.top fun v' hv' => (hFz.right v' hv').symm)

theorem continuousOn_chartTop_lift {z : MaxBranchedCover (Sing G X M) y₀} (hz : z.base ∈ U) :
    @ContinuousOn _ _ (chartTop U Fz TN) TN.top (Fz z)
      (connectedComponentIn (SpreadEnd.base ⁻¹' U) z) := fun _ hy =>
  ((tendsto_chartTop_lift hregM hregN hU hV hF hφreg hTN hz hy).mono_left
    (nhdsWithin_le_nhds_of (chartTop U Fz TN)))

/-- The topology `T_{U,V,φ}` is a local tamifying topology over `U` (`RamcovGX.tex:2093–2140`,
the case `ℓ`, `r` isomorphisms): first countable and locally path-connected over `U` (transported
from `T_N`), natural over `reg(U)` (`T_N` is natural over `reg N`), (A) over `U` (a set whose
preimage is open has, through the lifts, a `T_N`-open preimage in `\widetilde N`, hence an open
image in `N` by (A) for `T_N`), (B) over `U` (`g • D_N ∘ F` with `D₀ = g • D_N ∘ F` on the regular
part, `hstr`), (C) over `U` (a deck transformation of `\widetilde M` is read through the lifts as
one of `\widetilde N`) and (D) over `U` ((D) for `T_N`, transported). -/
theorem isLocalTamifying_chartTop
    (hlift' : ∀ (z : MaxBranchedCover (Sing G X M) y₀) (f : MaxBranchedCover (Sing G X N) yN),
      z.base ∈ U → f.base = φ' z.base → ∃ G' G'', IsChartLift U V φ' z f G' G'')
    (hφc : ContinuousOn φ' U) (hφinj : InjOn φ' U)
    {D₀ : MaxBranchedCover (Sing G X M) y₀ → X} {Dₙ : MaxBranchedCover (Sing G X N) yN → X}
    (hDₙ : Continuous[TN.top, _] Dₙ)
    (hstr : ∀ z : MaxBranchedCover (Sing G X M) y₀, z.base ∈ U → ∃ g : G,
      ∀ w ∈ connectedComponentIn (SpreadEnd.base ⁻¹' U) z ∩ SpreadEnd.base ⁻¹' Reg G X M,
        D₀ w = g • Dₙ (Fz z w)) :
    IsLocalTamifying G X M y₀ D₀ U (chartTop U Fz TN) := by
  have hS₀M := isSkeletal_sing G X M
  obtain ⟨-, hβM, -, -, hβlM, -⟩ := maxBranched_basic hS₀M hregM y₀
  have hS₀N := isSkeletal_sing G X N
  obtain ⟨-, hβN, -, -, hβlN, -⟩ := maxBranched_basic hS₀N hregN yN
  haveI := hβlM
  haveI := hβlN
  have hle : chartTop U Fz TN ≤ weakTopMax G X M y₀ := (le_iff_nhds _ _).2 fun y => by
    rw [nhds_chartTop hregM hregN hU hV hF hφreg hTN]
    exact chartNhds_le hregM hregN hU hV hF hTN y
  have hTopen : ∀ s, IsOpen s → IsOpen[chartTop U Fz TN] s := fun s hs =>
    TopologicalSpace.le_def.1 hle s hs
  have hZo : ∀ z : MaxBranchedCover (Sing G X M) y₀, z.base ∈ U →
      IsOpen (connectedComponentIn (SpreadEnd.base ⁻¹' U) z) := fun z hz =>
    (maxBranched_cc_facts hregM hU hz).1
  have hVo : ∀ f : MaxBranchedCover (Sing G X N) yN,
      IsOpen (connectedComponentIn (SpreadEnd.base ⁻¹' V) f) := fun f =>
    (hV.preimage hβN.isSpread.continuous).connectedComponentIn
  refine ⟨hle, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- first countable
    intro e he
    rw [nhds_chartTop hregM hregN hU hV hF hφreg hTN, chartNhds, if_pos he]
    haveI := @FirstCountableTopology.nhds_generated_countable _ TN.top hTN.firstCountable (Fz e e)
    infer_instance
  · -- locally path-connected
    intro e he
    refine Filter.hasBasis_self.2 fun t ht => ?_
    obtain ⟨F', hFe⟩ := hF e he
    have heZ := mem_connectedComponentIn (F := SpreadEnd.base ⁻¹' U) he
    have ht' := ht
    rw [nhds_chartTop hregM hregN hU hV hF hφreg hTN, chartNhds, if_pos he] at ht'
    obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := Filter.mem_inf_iff_superset.1 ht'
    obtain ⟨t', ht', htt₂⟩ := Filter.mem_comap.1 ht₂
    have hVn : connectedComponentIn (SpreadEnd.base ⁻¹' V) (Fz e e) ∈ @nhds _ TN.top (Fz e e) :=
      nhds_mono hTN.le_natural ((hVo _).mem_nhds (hFe.mapsTo heZ))
    obtain ⟨P', ⟨hP'n, hP'c⟩, hP'sub⟩ :=
      (@path_connected_basis _ TN.top hTN.locPathConnected (Fz e e)).mem_iff.1
        (Filter.inter_mem ht' hVn)
    refine ⟨F' '' P', ?_, isPathConnected_image_of TN.top (chartTop U Fz TN) hP'c
      (continuousOn_mono_of TN.top (chartTop U Fz TN)
        (continuousOn_chartTop_inv hregM hregN hU hV hF hφreg hTN he hFe)
        fun v hv => (hP'sub hv).2), ?_⟩
    · rw [nhds_chartTop hregM hregN hU hV hF hφreg hTN, chartNhds, if_pos he]
      exact Filter.mem_inf_of_inter (mem_principal_self _) (Filter.preimage_mem_comap hP'n)
        fun w hw => ⟨Fz e w, hw.2, hFe.left w hw.1⟩
    · rintro _ ⟨v, hv, rfl⟩
      refine hsub ⟨mem_principal.1 ht₁ (hFe.mapsTo' (hP'sub hv).2), htt₂ ?_⟩
      show Fz e (F' v) ∈ t'
      rw [hFe.right v (hP'sub hv).2]; exact (hP'sub hv).1
  · -- natural over `reg`
    intro e he hreg
    obtain ⟨F', hFe⟩ := hF e he
    have heZ := mem_connectedComponentIn (F := SpreadEnd.base ⁻¹' U) he
    rw [nhds_chartTop hregM hregN hU hV hF hφreg hTN]
    refine le_antisymm (chartNhds_le hregM hregN hU hV hF hTN e) ?_
    rw [chartNhds, if_pos he]
    refine le_inf (le_principal_iff.2 ((hZo e he).mem_nhds heZ)) ?_
    have hc := hFe.contF.continuousAt ((hZo e he).mem_nhds heZ)
    have hr : (Fz e e).base ∈ Reg G X N := by
      rw [hFe.base e heZ]; exact (hφreg _ he).2 hreg
    have hc' : Tendsto (Fz e) (𝓝 e) (@nhds _ TN.top (Fz e e)) := by
      rw [IsTamifyingTopology.nhds_eq_of_reg hregN hTN hr]; exact hc
    exact hc'.le_comap
  · -- (A)
    intro O hO
    set Y : Set N := φ' '' (O ∩ U) with hYdef
    have hYq : IsOpen[TN.top] ((SpreadEnd.base : MaxBranchedCover (Sing G X N) yN → N) ⁻¹' Y) := by
      refine (isOpen_iff_mem_nhds_of TN.top).2 fun v hv => ?_
      obtain ⟨u, ⟨huO, huU⟩, hvu⟩ := hv
      obtain ⟨z, hz⟩ := hβM.surjective u
      have hzU : z.base ∈ U := hz ▸ huU
      obtain ⟨G', G'', hG⟩ := hlift' z v hzU (by rw [hz]; exact hvu.symm)
      have hzZ := mem_connectedComponentIn (F := SpreadEnd.base ⁻¹' U) hzU
      have hA : connectedComponentIn (SpreadEnd.base ⁻¹' U) z ∩
          ((SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) ⁻¹' O ∩ SpreadEnd.base ⁻¹' U) ∈
            @nhds _ (chartTop U Fz TN) z :=
        @IsOpen.mem_nhds _ (chartTop U Fz TN) _ _ (@IsOpen.inter _ (chartTop U Fz TN) _ _
          (hTopen _ (hZo z hzU)) hO) ⟨hzZ, show z.base ∈ O from hz ▸ huO, hzU⟩
      have himg := image_mem_nhds_of_isChartLift hregM hregN hU hV hF hφreg hTN hzU hG hzZ hA
      rw [hG.apply_self] at himg
      refine Filter.mem_of_superset himg ?_
      rintro _ ⟨w, ⟨hwZ, hwO, hwU⟩, rfl⟩
      exact ⟨w.base, ⟨hwO, hwU⟩, (hG.base w hwZ).symm⟩
    have hY : IsOpen Y := by
      have h : IsOpen[TopologicalSpace.coinduced SpreadEnd.base TN.top] Y := isOpen_coinduced.2 hYq
      rwa [hTN.coinduced_eq] at h
    have hOU : O ∩ U = U ∩ φ' ⁻¹' Y := by
      ext m
      constructor
      · rintro ⟨hmO, hmU⟩; exact ⟨hmU, m, ⟨hmO, hmU⟩, rfl⟩
      · rintro ⟨hmU, m', hm', heq⟩
        exact ⟨hφinj hm'.2 hmU heq ▸ hm'.1, hmU⟩
    rw [hOU]; exact hφc.isOpen_inter_preimage hU hY
  · -- (B)
    intro e he
    obtain ⟨g, hg⟩ := hstr e he
    refine ⟨connectedComponentIn (SpreadEnd.base ⁻¹' U) e, hTopen _ (hZo e he),
      mem_connectedComponentIn (F := SpreadEnd.base ⁻¹' U) he, fun w => g • Dₙ (Fz e w), ?_,
      fun w hw => (hg w hw).symm⟩
    intro y hy
    exact (((@Continuous.tendsto _ _ TN.top _ Dₙ hDₙ (Fz e y)).comp
      (tendsto_chartTop_lift hregM hregN hU hV hF hφreg hTN he hy)).const_smul g).mono_left
      (nhdsWithin_le_nhds_of (chartTop U Fz TN))
  · -- (C)
    rintro f ⟨γ, hγ, rfl⟩ e he
    have hγb : ∀ w, (γ w).base = w.base := deck_apply _ hγ
    have hγe : (γ e).base ∈ U := by rw [hγb]; exact he
    have hmap : ∀ (γ' : MaxBranchedCover (Sing G X M) y₀ ≃ₜ MaxBranchedCover (Sing G X M) y₀),
        (∀ w, (γ' w).base = w.base) → ∀ a : MaxBranchedCover (Sing G X M) y₀, a.base ∈ U →
        MapsTo γ' (connectedComponentIn (SpreadEnd.base ⁻¹' U) a)
          (connectedComponentIn (SpreadEnd.base ⁻¹' U) (γ' a)) := by
      intro γ' hγ' a ha
      refine image_subset_iff.1 ((isPreconnected_connectedComponentIn.image _
        γ'.continuous.continuousOn).subset_connectedComponentIn
          ⟨a, mem_connectedComponentIn (F := SpreadEnd.base ⁻¹' U) ha, rfl⟩ ?_)
      rintro _ ⟨w, hw, rfl⟩
      show (γ' w).base ∈ U
      rw [hγ']; exact mem_of_mem_connectedComponentIn_preimage hw
    have hγsb : ∀ w, (γ.symm w).base = w.base := fun w => by
      rw [← hγb (γ.symm w), Homeomorph.apply_symm_apply]
    obtain ⟨F₂', hF₂⟩ := hF (γ e) hγe
    have hG : IsChartLift U V φ' e (Fz (γ e) (γ e)) (fun w => Fz (γ e) (γ w))
        (fun v => γ.symm (F₂' v)) := by
      refine ⟨rfl, fun w hw => hF₂.mapsTo (hmap γ hγb e he hw), fun v hv => ?_, fun w hw => ?_,
        fun v hv => ?_, hF₂.contF.comp γ.continuous.continuousOn (hmap γ hγb e he),
        γ.symm.continuous.comp_continuousOn hF₂.contF', fun w hw => ?_⟩
      · have := hmap γ.symm hγsb (γ e) hγe (hF₂.mapsTo' hv)
        rwa [Homeomorph.symm_apply_apply] at this
      · show γ.symm (F₂' (Fz (γ e) (γ w))) = w
        rw [hF₂.left _ (hmap γ hγb e he hw), Homeomorph.symm_apply_apply]
      · show Fz (γ e) (γ (γ.symm (F₂' v))) = v
        rw [Homeomorph.apply_symm_apply, hF₂.right v hv]
      · show (Fz (γ e) (γ w)).base = φ' w.base
        rw [hF₂.base _ (hmap γ hγb e he hw), hγb]
    show Tendsto γ (@nhds _ (chartTop U Fz TN) e) (@nhds _ (chartTop U Fz TN) (γ e))
    rw [nhds_chartTop_eq_of_isChartLift hregM hregN hU hV hF hφreg hTN he hG
      (mem_connectedComponentIn (F := SpreadEnd.base ⁻¹' U) he),
      nhds_chartTop hregM hregN hU hV hF hφreg hTN,
      chartNhds_eq hregM hregN hU hF hφreg hTN hγe
        (mem_connectedComponentIn (F := SpreadEnd.base ⁻¹' U) hγe)]
    refine tendsto_inf.2 ⟨tendsto_principal.2 (Filter.mem_of_superset
      (Filter.mem_inf_of_left (mem_principal_self _)) fun w hw => hmap γ hγb e he hw),
      tendsto_comap_iff.2 (tendsto_comap.mono_left inf_le_right)⟩
  · -- (D)
    have hpre : (Subtype.val : (SpreadEnd.base ⁻¹' U : Set (MaxBranchedCover (Sing G X M) y₀)) →
        MaxBranchedCover (Sing G X M) y₀) ⁻¹' (SpreadEnd.base ⁻¹' Reg G X M) =
        Subtype.val ⁻¹' (SpreadEnd.base ⁻¹' Reg G X M ∩ SpreadEnd.base ⁻¹' U) := by
      ext z; exact ⟨fun h => ⟨h, z.2⟩, fun h => h.1⟩
    rw [hpre]
    have hOU : IsOpen[chartTop U Fz TN]
        ((SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) ⁻¹' U) :=
      hTopen _ (hU.preimage hβM.isSpread.continuous)
    refine (@isPortly_subtype_iff _ (chartTop U Fz TN) _ _ hOU inter_subset_right).2
      ⟨hTopen _ (((isOpen_reg G X M).preimage hβM.isSpread.continuous).inter
        (hU.preimage hβM.isSpread.continuous)), fun y hy => ?_, fun W hWo hWU hWc => ?_⟩
    · obtain ⟨F', hFy⟩ := hF y hy
      have hyZ := mem_connectedComponentIn (F := SpreadEnd.base ⁻¹' U) hy
      refine (mem_closure_iff_nhds_of (chartTop U Fz TN)).2 fun t ht => ?_
      rw [nhds_chartTop hregM hregN hU hV hF hφreg hTN, chartNhds,
        if_pos (show y.base ∈ U from hy)] at ht
      obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := Filter.mem_inf_iff_superset.1 ht
      obtain ⟨t', ht', htt₂⟩ := Filter.mem_comap.1 ht₂
      have hVn : connectedComponentIn (SpreadEnd.base ⁻¹' V) (Fz y y) ∈
          @nhds _ TN.top (Fz y y) :=
        nhds_mono hTN.le_natural ((hVo _).mem_nhds (hFy.mapsTo hyZ))
      have hd := mem_closure_of_dense_of TN.top (@IsPortly.dense _ TN.top _ hTN.isPortly) (Fz y y)
      rw [mem_closure_iff_nhds_of TN.top] at hd
      obtain ⟨v, ⟨hvt', hvV⟩, hvR⟩ := hd _ (Filter.inter_mem ht' hVn)
      have hFv := hFy.mapsTo' hvV
      refine ⟨F' v, hsub ⟨mem_principal.1 ht₁ hFv, htt₂ ?_⟩, ?_,
        mem_of_mem_connectedComponentIn_preimage (p := SpreadEnd.base) hFv⟩
      · show Fz y (F' v) ∈ t'
        rw [hFy.right v hvV]; exact hvt'
      · show (F' v).base ∈ Reg G X M
        refine (hφreg _ (mem_of_mem_connectedComponentIn_preimage (p := SpreadEnd.base) hFv)).1 ?_
        rw [← hFy.base _ hFv, hFy.right v hvV]; exact hvR
    · rcases W.eq_empty_or_nonempty with rfl | ⟨w₀, hw₀⟩
      · rw [empty_inter]; exact isPreconnected_empty_of (chartTop U Fz TN)
      have hw₀U : w₀.base ∈ U := hWU hw₀
      have hWc' : IsPreconnected W := by
        have := isPreconnected_image_of (chartTop U Fz TN) (weakTopMax G X M y₀) hWc
          (continuousOn_of_continuous_of _ _ (continuous_id_of_le hle) W)
        rwa [image_id] at this
      have hWZ : W ⊆ connectedComponentIn (SpreadEnd.base ⁻¹' U) w₀ :=
        hWc'.subset_connectedComponentIn hw₀ hWU
      obtain ⟨F', hFw⟩ := hF w₀ hw₀U
      have hFW : IsOpen[TN.top] (Fz w₀ '' W) := by
        refine (isOpen_iff_mem_nhds_of TN.top).2 ?_
        rintro _ ⟨w, hw, rfl⟩
        exact image_mem_nhds_of_isChartLift hregM hregN hU hV hF hφreg hTN hw₀U hFw (hWZ hw)
          (@IsOpen.mem_nhds _ (chartTop U Fz TN) _ _ hWo hw)
      have hFWc : @IsPreconnected _ TN.top (Fz w₀ '' W) :=
        isPreconnected_image_of (chartTop U Fz TN) TN.top hWc
          (continuousOn_mono_of (chartTop U Fz TN) TN.top
            (continuousOn_chartTop_lift hregM hregN hU hV hF hφreg hTN hw₀U) hWZ)
      have h1 := isPreconnected_inter_of_isPortly_of TN.top hTN.isPortly hFW hFWc
      have h2 := isPreconnected_image_of TN.top (chartTop U Fz TN) h1
        (continuousOn_mono_of TN.top (chartTop U Fz TN)
          (continuousOn_chartTop_inv hregM hregN hU hV hF hφreg hTN hw₀U hFw)
          (by rintro _ ⟨⟨w, hw, rfl⟩, -⟩; exact hFw.mapsTo (hWZ hw)))
      have heq : F' '' (Fz w₀ '' W ∩ SpreadEnd.base ⁻¹' Reg G X N) =
          W ∩ (SpreadEnd.base ⁻¹' Reg G X M ∩ SpreadEnd.base ⁻¹' U) := by
        ext w
        constructor
        · rintro ⟨_, ⟨⟨w', hw', rfl⟩, hreg⟩, rfl⟩
          rw [hFw.left w' (hWZ hw')]
          refine ⟨hw', ?_, hWU hw'⟩
          refine (hφreg _ (hWU hw')).1 ?_
          rw [← hFw.base w' (hWZ hw')]; exact hreg
        · rintro ⟨hw, hreg, -⟩
          refine ⟨Fz w₀ w, ⟨⟨w, hw, rfl⟩, ?_⟩, hFw.left w (hWZ hw)⟩
          show (Fz w₀ w).base ∈ Reg G X N
          rw [hFw.base w (hWZ hw)]; exact (hφreg _ (hWU hw)).2 hreg
      rw [← heq]; exact h2

end ChartTop

section ChartStructure

variable {G : Type*} {X : Type*} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
  {M : Type v} [TopologicalSpace M] [T2Space M] [LocPathConnectedSpace M]
  [FirstCountableTopology M] [ConnectedSpace M] [SingularGXStructure G X M]
  {N : Type u} [TopologicalSpace N] [T2Space N] [LocPathConnectedSpace N]
  [FirstCountableTopology N] [ConnectedSpace N] [SingularGXStructure G X N]

/-- `p : \widetilde M → M` induces a `(G,X)`-morphism on `p⁻¹(reg M)` (for `p^*B`). -/
theorem isRegularOn_base_maxBranched (hregM : SemilocallySimplyConnected ((Sing G X M)ᶜ : Set M))
    (y₀ : ((Sing G X M)ᶜ : Set M)) :
    IsGXAtlas G (aePullback G (aeAtlas G X M)
      (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M)) ∧
    IsRegularOn G (aePullback G (aeAtlas G X M)
      (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M)) (aeAtlas G X M) SpreadEnd.base
      (SpreadEnd.base ⁻¹' Reg G X M) := by
  set B := aeAtlas G X M
  have hBm : IsMaximalAEAtlas G B := isMaximalAEAtlas_aeAtlas G X M
  have hS₀ : IsSkeletal (Sing G X M) := isSkeletal_sing G X M
  obtain ⟨-, hβbc, hβS, -, hβl, -⟩ := maxBranched_basic hS₀ hregM y₀
  haveI := hβl
  have hAt := aePullback_spec_of_isAELocalHomeomorph hBm.1 hβbc.isSpread.continuous
    (hβbc.isAELocalHomeomorph hBm.1)
  have hRo : IsOpen ((SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) ⁻¹' Reg G X M) :=
    (isOpen_reg G X M).preimage hβbc.isSpread.continuous
  have hordβ : Reg G X M ⊆ ordY (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) :=
    fun y hy => by by_contra hn; exact (hβS hn) hy
  have hRsupp : (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) ⁻¹' Reg G X M ⊆
      support (aePullback G B (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M)) :=
    fun w hw => hAt.2.mem_support_of_isLocalHomeomorphOn' hAt.1 hBm.1 hw
      (hβbc.ordX_subset_isLocalHomeomorphOn (hordβ hw))
  have hregβ := hAt.2.regLocusOf_eq hAt.1.1 hBm.1
  exact ⟨hAt.1.1.1, (isRegularOn_regLocusOf (G := G) _ B
    (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M)).mono
    (fun w hw => by rw [hregβ]; exact ⟨hRsupp hw, hw⟩) hRo⟩

/-- A map inducing a `(G,X)`-morphism on `p⁻¹(reg N)` is, near each point of it, a translate of a
chart of `N` read through `p`. -/
theorem IsRegDevelopingOnReg.eventually_eq_smul_chart
    (hregN : SemilocallySimplyConnected ((Sing G X N)ᶜ : Set N)) {yN : ((Sing G X N)ᶜ : Set N)}
    {D : MaxBranchedCover (Sing G X N) yN → X} (hD : IsRegDevelopingOnReg G X N yN D)
    {v : MaxBranchedCover (Sing G X N) yN} (hv : v.base ∈ Reg G X N) :
    ∃ c ∈ aeAtlas G X N, v.base ∈ c.source ∧ ∃ h : G, ∀ᶠ v' in 𝓝 v, D v' = h • c v'.base := by
  obtain ⟨-, hβR⟩ := isRegularOn_base_maxBranched hregN yN
  obtain ⟨e, he, hve⟩ := mem_support.1 (hβR.subset_support hv)
  obtain ⟨c, hc, hvc⟩ := mem_support.1 hv
  obtain ⟨a, ha⟩ := hβR.exists_smul_eq v hv e he c hc hve hvc
  obtain ⟨b, hb⟩ := hD.eventually_eq_smul_model hv he hve
  refine ⟨c, hc, hvc, b * a⁻¹, ?_⟩
  filter_upwards [ha, hb] with y h1 h2
  rw [h2, mul_smul, h1, inv_smul_smul]

/-- An isomorphism `φ : U → V` of open subsets is, near a regular point of `U`, a translate of
charts of `M` and `N` (`φ` induces a `(G,X)`-morphism on `reg U`). -/
theorem eventually_chartExt_eq_smul {U : Opens M} {V : Opens N} {φ : U ≃ₜ V}
    (hφ : IsAEMorphism G X (φ : U → V)) {u : U} (hu : (u : M) ∈ Reg G X M)
    {c : OpenPartialHomeomorph N X} (hc : c ∈ aeAtlas G X N) (huc : (φ u : N) ∈ c.source) :
    ∃ c' ∈ aeAtlas G X M, (u : M) ∈ c'.source ∧ ∃ g : G,
      ∀ᶠ m in 𝓝 (u : M), c (chartExt φ m) = g • c' m := by
  have hpre := (IsAEMorphism.preimage_reg_sing hφ φ.isLocalHomeomorph).1
  have huU : u ∈ Reg G X U := by rw [reg_opensSingular U]; exact hu
  have huV : φ u ∈ Reg G X V := by
    have : u ∈ (φ : U → V) ⁻¹' Reg G X V := by rw [hpre]; exact huU
    exact this
  have huV' : (φ u : N) ∈ Reg G X N := by
    have := huV; rw [reg_opensSingular V] at this; exact this
  -- `φ` regular at `u`
  have hrφ := hφ.regLocusOf_eq (isMaximalAEAtlas_aeAtlas G X U).1
    (isMaximalAEAtlas_aeAtlas G X V).1
  have hRφ := isRegularOn_regLocusOf (G := G) (aeAtlas G X U) (aeAtlas G X V) (φ : U → V)
  have huR : u ∈ regLocusOf G (aeAtlas G X U) (aeAtlas G X V) (φ : U → V) := by
    rw [hrφ]; exact ⟨huU, huV⟩
  obtain ⟨eU, heU, hueU⟩ := mem_support.1 huU
  obtain ⟨eV, heV, hueV⟩ := mem_support.1 huV
  obtain ⟨g, hg⟩ := hRφ.exists_smul_eq u huR eU heU eV heV hueU hueV
  -- the inclusions
  have hvalV := (isAEMorphism_opensSingular_val (G := G) (X := X) V)
  have hrV := hvalV.regLocusOf_eq (isMaximalAEAtlas_aeAtlas G X V).1
    (isMaximalAEAtlas_aeAtlas G X N).1
  have hRV := isRegularOn_regLocusOf (G := G) (aeAtlas G X V) (aeAtlas G X N)
    (Subtype.val : V → N)
  obtain ⟨a, ha⟩ := hRV.exists_smul_eq (φ u) (by rw [hrV]; exact ⟨huV, huV'⟩) eV heV c hc hueV huc
  have hvalU := (isAEMorphism_opensSingular_val (G := G) (X := X) U)
  have hrU := hvalU.regLocusOf_eq (isMaximalAEAtlas_aeAtlas G X U).1
    (isMaximalAEAtlas_aeAtlas G X M).1
  have hRU := isRegularOn_regLocusOf (G := G) (aeAtlas G X U) (aeAtlas G X M)
    (Subtype.val : U → M)
  obtain ⟨c', hc', huc'⟩ := mem_support.1 hu
  obtain ⟨b, hb⟩ := hRU.exists_smul_eq u (by rw [hrU]; exact ⟨huU, hu⟩) eU heU c' hc' hueU huc'
  refine ⟨c', hc', huc', a * g * b⁻¹, ?_⟩
  rw [← U.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq u, Filter.eventually_map]
  filter_upwards [hg, hb, φ.continuous.continuousAt.eventually ha] with y h1 h2 h3
  rw [chartExt_apply φ y.2]
  show c (φ y : N) = (a * g * b⁻¹) • c' (y : M)
  rw [h3, h1, h2, mul_smul, mul_smul, inv_smul_smul, ← mul_smul]

/-- The descent step of (B) (`RamcovGX.tex:2124–2128`): through a lift `F` of `φ` from a component
`Û` of `p⁻¹(U)`, `D_N ∘ F` is a developing map of `reg(Û)`, so it differs from the developing map
`D₀` of `reg(\widetilde M)` by one `g ∈ G` on the connected `reg(Û)`. -/
theorem exists_smul_eq_of_isChartLift (hregM : SemilocallySimplyConnected ((Sing G X M)ᶜ : Set M))
    (hregN : SemilocallySimplyConnected ((Sing G X N)ᶜ : Set N)) {U : Opens M} {V : Opens N}
    {φ : U ≃ₜ V} (hφ : IsAEMorphism G X (φ : U → V)) {y₀ : ((Sing G X M)ᶜ : Set M)}
    {yN : ((Sing G X N)ᶜ : Set N)} {D₀ : MaxBranchedCover (Sing G X M) y₀ → X}
    (hD₀ : IsRegDevelopingOnReg G X M y₀ D₀) {Dₙ : MaxBranchedCover (Sing G X N) yN → X}
    (hDₙ : IsRegDevelopingOnReg G X N yN Dₙ) {z : MaxBranchedCover (Sing G X M) y₀}
    (hz : z.base ∈ U) {f : MaxBranchedCover (Sing G X N) yN}
    {F : MaxBranchedCover (Sing G X M) y₀ → MaxBranchedCover (Sing G X N) yN}
    {F' : MaxBranchedCover (Sing G X N) yN → MaxBranchedCover (Sing G X M) y₀}
    (hF : IsChartLift (U : Set M) (V : Set N) (chartExt φ) z f F F') :
    ∃ g : G, ∀ w ∈ connectedComponentIn (SpreadEnd.base ⁻¹' (U : Set M)) z ∩
      SpreadEnd.base ⁻¹' Reg G X M, D₀ w = g • Dₙ (F w) := by
  obtain ⟨hZo, hZ'o, hZ'c, -, -⟩ := maxBranched_cc_facts hregM U.isOpen hz
  obtain ⟨hA, hβR⟩ := isRegularOn_base_maxBranched hregM y₀
  have hreg : IsRegularOn G (aePullback G (aeAtlas G X M)
      (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M)) (gxModelAtlas G X)
      (fun w => Dₙ (F w)) (connectedComponentIn (SpreadEnd.base ⁻¹' (U : Set M)) z ∩
        SpreadEnd.base ⁻¹' Reg G X M) := by
    refine isRegularOn_model_of_eventually_comp hA (hβR.mono inter_subset_right hZ'o)
      fun w hw => ?_
    have hwU : w.base ∈ U := mem_of_mem_connectedComponentIn_preimage hw.1
    have hFw : (F w).base ∈ Reg G X N := by
      rw [hF.base w hw.1]; exact (chartExt_mem_reg_iff hφ hwU).2 hw.2
    obtain ⟨c, hc, hFc, h, hh⟩ := hDₙ.eventually_eq_smul_chart hregN hFw
    have hφu : (φ ⟨w.base, hwU⟩ : N) ∈ c.source := by
      rw [← chartExt_apply φ hwU, ← hF.base w hw.1]; exact hFc
    obtain ⟨c', hc', hwc', g, hg⟩ := eventually_chartExt_eq_smul hφ (u := ⟨w.base, hwU⟩) hw.2 hc hφu
    refine ⟨c', hc', hwc', h * g, ?_⟩
    have hcF := hF.contF.continuousAt (hZo.mem_nhds hw.1)
    have hcb : Tendsto (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) (𝓝 w)
        (𝓝 w.base) := SpreadEnd.continuous_base.continuousAt
    filter_upwards [hcF.eventually hh, hcb.eventually hg, hZo.mem_nhds hw.1] with y h1 h2 h3
    show Dₙ (F y) = (h * g) • c' y.base
    rw [h1, hF.base y h3, h2, mul_smul]
  obtain ⟨g, hg⟩ := exists_smul_eq_on_of_isRegularOn hZ'c hreg
    (hD₀.mono inter_subset_right hZ'o)
  exact ⟨g, hg⟩

end ChartStructure

section ChartNat

variable {G : Type*} {X : Type*} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
  {M : Type v} [TopologicalSpace M] [T2Space M] [LocPathConnectedSpace M]
  [FirstCountableTopology M] [ConnectedSpace M] [SingularGXStructure G X M]
  {N : Type u} [TopologicalSpace N] [T2Space N] [LocPathConnectedSpace N]
  [FirstCountableTopology N] [ConnectedSpace N] [SingularGXStructure G X N]
  {y₀ : ((Sing G X M)ᶜ : Set M)} {yN : ((Sing G X N)ᶜ : Set N)}

/-- Naturality of `T_{U,V,φ}` (`RamcovGX.tex:2104–2107`, and the restriction the gluing l.2101
uses): two lifted charts which, on an open `W` inside both domains, differ by an automorphism `ψ`
of the model (`ψ ∘ φ₁ = φ₂` on `W`) give comparable neighbourhoods at the points over `W` (equal,
`ψ⁻¹` giving the converse). Through the lift `Ψ` of `ψ` to `\widetilde N`
(`exists_lift_singularAut`), `T_N`-continuous by hypothesis, the two lifts differ on each
component of `p⁻¹(W)` by `δ ∘ Ψ`, `δ ∈ Γ(\widetilde N/N)`. -/
theorem nhds_chartTop_le_of_aut (hregM : SemilocallySimplyConnected ((Sing G X M)ᶜ : Set M))
    (hregN : SemilocallySimplyConnected ((Sing G X N)ᶜ : Set N))
    {U₁ U₂ : Set M} {V₁ V₂ : Set N} {φ₁ φ₂ : M → N}
    {Fz₁ Fz₂ : MaxBranchedCover (Sing G X M) y₀ → MaxBranchedCover (Sing G X M) y₀ →
      MaxBranchedCover (Sing G X N) yN}
    {TN : WrappedTop (MaxBranchedCover (Sing G X N) yN)}
    (hU₁ : IsOpen U₁) (hV₁ : IsOpen V₁)
    (hF₁ : ∀ z : MaxBranchedCover (Sing G X M) y₀, z.base ∈ U₁ →
      ∃ F', IsChartLift U₁ V₁ φ₁ z (Fz₁ z z) (Fz₁ z) F')
    (hφreg₁ : ∀ m ∈ U₁, φ₁ m ∈ Reg G X N ↔ m ∈ Reg G X M)
    (hU₂ : IsOpen U₂) (hV₂ : IsOpen V₂)
    (hF₂ : ∀ z : MaxBranchedCover (Sing G X M) y₀, z.base ∈ U₂ →
      ∃ F', IsChartLift U₂ V₂ φ₂ z (Fz₂ z z) (Fz₂ z) F')
    (hφreg₂ : ∀ m ∈ U₂, φ₂ m ∈ Reg G X N ↔ m ∈ Reg G X M)
    (hTN : IsTamifyingTopology G X N yN TN.top)
    (hAut : ∀ f ∈ aeAutMapsMax G X N yN, Continuous[TN.top, TN.top] f)
    {W : Set M} (hWo : IsOpen W) (hW₁ : W ⊆ U₁) (hW₂ : W ⊆ U₂) {ψ : N ≃ₜ N}
    (hψ : ψ ∈ singularAut G X N) (hψφ : ∀ m ∈ W, ψ (φ₁ m) = φ₂ m)
    {e : MaxBranchedCover (Sing G X M) y₀} (he : e.base ∈ W) :
    @nhds _ (chartTop U₁ Fz₁ TN) e ≤ @nhds _ (chartTop U₂ Fz₂ TN) e := by
  obtain ⟨Ψ, hΨb, hΨ⟩ := exists_lift_singularAut hregN yN hψ
  have hΨc : Continuous[TN.top, TN.top] Ψ := hAut _ ⟨Ψ, rfl, hΨ⟩
  obtain ⟨hZwo, hZw'o, hZw'c, hcl, hne⟩ := maxBranched_cc_facts hregM hWo he
  have hZw₁ : connectedComponentIn ((SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) ⁻¹' W) e ⊆
      connectedComponentIn (SpreadEnd.base ⁻¹' U₁) e :=
    connectedComponentIn_mono _ (preimage_mono hW₁)
  have hZw₂ : connectedComponentIn ((SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) ⁻¹' W) e ⊆
      connectedComponentIn (SpreadEnd.base ⁻¹' U₂) e :=
    connectedComponentIn_mono _ (preimage_mono hW₂)
  obtain ⟨F₁', hF₁e⟩ := hF₁ e (hW₁ he)
  obtain ⟨F₂', hF₂e⟩ := hF₂ e (hW₂ he)
  obtain ⟨δ, hδ, hEq⟩ := exists_deck_eqOn_of_base_eq hregN hZwo inter_subset_left hZw'o hZw'c hcl hne
    (F₁ := fun y => Ψ (Fz₁ e y)) (F₂ := Fz₂ e)
    (Ψ.continuous.comp_continuousOn (hF₁e.contF.mono hZw₁)) (hF₂e.contF.mono hZw₂)
    (fun y hy => by
      show (Ψ (Fz₁ e y)).base = (Fz₂ e y).base
      rw [hΨb, hF₁e.base y (hZw₁ hy), hF₂e.base y (hZw₂ hy),
        hψφ _ (mem_of_mem_connectedComponentIn_preimage hy)])
    (fun y hy => by
      show (Ψ (Fz₁ e y)).base ∈ Reg G X N
      have hyW : y.base ∈ W := mem_of_mem_connectedComponentIn_preimage hy.1
      rw [hΨb, hF₁e.base y (hZw₁ hy.1), hψφ _ hyW]
      exact (hφreg₂ _ (hW₂ hyW)).2 hy.2)
  have hκ : Continuous[TN.top, TN.top] (fun v => δ (Ψ v)) :=
    continuous_comp_of TN.top TN.top TN.top (continuous_deck_of_isTamifying hTN hδ) hΨc
  have hZwmem : connectedComponentIn ((SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) ⁻¹' W) e ∈
      chartNhds U₁ Fz₁ TN e :=
    chartNhds_le hregM hregN hU₁ hV₁ hF₁ hTN e (hZwo.mem_nhds (mem_connectedComponentIn he))
  rw [nhds_chartTop hregM hregN hU₁ hV₁ hF₁ hφreg₁ hTN, nhds_chartTop hregM hregN hU₂ hV₂ hF₂ hφreg₂ hTN]
  have hZwmem' := hZwmem
  rw [chartNhds, if_pos (hW₁ he)] at hZwmem'
  rw [chartNhds, chartNhds, if_pos (hW₁ he), if_pos (hW₂ he)]
  calc 𝓟 (connectedComponentIn (SpreadEnd.base ⁻¹' U₁) e) ⊓
        Filter.comap (Fz₁ e) (@nhds _ TN.top (Fz₁ e e))
      = 𝓟 (connectedComponentIn ((SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) ⁻¹' W) e) ⊓
        (𝓟 (connectedComponentIn (SpreadEnd.base ⁻¹' U₁) e) ⊓
          Filter.comap (Fz₁ e) (@nhds _ TN.top (Fz₁ e e))) :=
        (inf_eq_right.2 (le_principal_iff.2 hZwmem')).symm
    _ ≤ 𝓟 (connectedComponentIn ((SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) ⁻¹' W) e) ⊓
        Filter.comap (Fz₁ e) (Filter.comap (fun v => δ (Ψ v))
          (@nhds _ TN.top (δ (Ψ (Fz₁ e e))))) :=
        inf_le_inf_left _ (inf_le_right.trans (Filter.comap_mono
          (@Continuous.tendsto _ _ TN.top TN.top _ hκ (Fz₁ e e)).le_comap))
    _ = 𝓟 (connectedComponentIn ((SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) ⁻¹' W) e) ⊓
        Filter.comap (Fz₂ e) (@nhds _ TN.top (Fz₂ e e)) := by
        rw [Filter.comap_comap, hEq (mem_connectedComponentIn he)]
        exact (principal_inf_comap_congr hEq _).symm
    _ ≤ 𝓟 (connectedComponentIn (SpreadEnd.base ⁻¹' U₂) e) ⊓
        Filter.comap (Fz₂ e) (@nhds _ TN.top (Fz₂ e e)) :=
        inf_le_inf_right _ (principal_mono.2 hZw₂)

end ChartNat

section NatReg

variable {G : Type*} {X : Type*} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
  {M : Type v} [TopologicalSpace M] [T2Space M] [LocPathConnectedSpace M]
  [FirstCountableTopology M] [ConnectedSpace M] [SingularGXStructure G X M]

/-- Over `reg(M)` the natural topology of `\widetilde M` is a local tamifying topology. -/
theorem isLocalTamifying_natural_reg (hregM : SemilocallySimplyConnected ((Sing G X M)ᶜ : Set M))
    {y₀ : ((Sing G X M)ᶜ : Set M)} {D₀ : MaxBranchedCover (Sing G X M) y₀ → X}
    (hD₀ : IsRegDevelopingOnReg G X M y₀ D₀) :
    IsLocalTamifying G X M y₀ D₀ (Reg G X M) (weakTopMax G X M y₀) := by
  have hS₀ := isSkeletal_sing G X M
  obtain ⟨-, hβbc, -, -, hβl, -⟩ := maxBranched_basic hS₀ hregM y₀
  haveI := hβl
  haveI := (maxBranched_instances hS₀ hregM y₀).2.1
  have hRo : IsOpen ((SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) ⁻¹' Reg G X M) :=
    (isOpen_reg G X M).preimage hβbc.isSpread.continuous
  refine ⟨le_rfl, fun e _ => FirstCountableTopology.nhds_generated_countable e,
    fun e _ => path_connected_basis e, fun e _ _ => rfl, fun O hO => ?_,
    fun e he => ⟨_, hRo, he, D₀, hD₀.continuousOn, fun _ _ => rfl⟩,
    fun f hf e _ => ?_, ?_⟩
  · have h := (spread_connected_image hβbc).1 _ hO
    rwa [← preimage_inter, image_preimage_eq _ hβbc.surjective] at h
  · obtain ⟨γ, -, rfl⟩ := hf
    exact γ.continuous.continuousAt
  · show IsPortly ((Subtype.val : (SpreadEnd.base ⁻¹' Reg G X M : Set _) → _) ⁻¹'
      (SpreadEnd.base ⁻¹' Reg G X M))
    rw [Subtype.coe_preimage_self]
    exact isPortly_univ

end NatReg



section LiftWitness

variable {G : Type*} {X : Type*} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
  {N : Type u} [TopologicalSpace N] [T2Space N] [LocPathConnectedSpace N]
  [FirstCountableTopology N] [ConnectedSpace N] [SingularGXStructure G X N]

/-- A self-map of `\widetilde N` over `N` is, on the whole space, an element of
`Γ(\widetilde N/N)` (uniqueness over the connected dense regular part). -/
theorem exists_deck_eq_of_base_eq_maxBranched
    (hregN : SemilocallySimplyConnected ((Sing G X N)ᶜ : Set N)) {y₁ y₂ : ((Sing G X N)ᶜ : Set N)}
    {F : MaxBranchedCover (Sing G X N) y₁ → MaxBranchedCover (Sing G X N) y₂}
    {F' : MaxBranchedCover (Sing G X N) y₂ → MaxBranchedCover (Sing G X N) y₁}
    (hF : Continuous F) (hF' : Continuous F') (hFb : ∀ x, (F x).base = x.base)
    (hF'b : ∀ x, (F' x).base = x.base) :
    ∃ σ ∈ deckGroup (SpreadEnd.base : MaxBranchedCover (Sing G X N) y₁ → N),
      ∀ x, F' (F x) = σ x := by
  have hS := isSkeletal_sing G X N
  obtain ⟨-, hβ, -, -, -, -⟩ := maxBranched_basic hS hregN y₁
  haveI := hβ.connectedSpace_source
  have hR := hβ.isPortly_preimage (isPortly_reg G X N)
  obtain ⟨σ, hσ, hEq⟩ := exists_deck_eqOn_of_base_eq hregN isOpen_univ (subset_univ _) hR.isOpen
    hR.isPreconnected (fun x _ => hR.dense x) hR.dense.nonempty continuousOn_id
    (hF'.comp hF).continuousOn (fun x _ => by simp [hF'b, hFb]) (fun x hx => hx)
    (F₁ := fun x => x) (F₂ := fun x => F' (F x))
  exact ⟨σ, hσ, fun x => hEq (mem_univ x)⟩

/-- Non-vacuity of `IsLiftableChartMap`: the chart `(N, N, id)` of a model whose maximal
covering is Galoisian (`reg N` semi-locally simply connected in `N`, `prop:Galoisian_semilocal`)
lifts to the maximal coverings, at every point, singular ones included: two maximal coverings of
`N` (two base points) are isomorphic over `N` (`prop:universality`), by an isomorphism sending any
point to any point of its fibre (Galoisian). -/
theorem isLiftableChartMap_refl (hregN : SemilocallySimplyConnected ((Sing G X N)ᶜ : Set N))
    (hgal : IsSLSCInCC ((Sing G X N)ᶜ : Set N)) :
    IsLiftableChartMap G X (M := N) (N := N) (Homeomorph.refl (⊤ : Opens N)) := by
  intro y₀ yN e f he hf
  have hS := isSkeletal_sing G X N
  obtain ⟨-, hβ₀, hβS₀, -, hβl₀, -⟩ := maxBranched_basic hS hregN y₀
  obtain ⟨-, hβ₁, hβS₁, -, hβl₁, -⟩ := maxBranched_basic hS hregN yN
  haveI := hβl₀
  haveI := hβl₁
  haveI := hβ₀.connectedSpace_source
  haveI := hβ₁.connectedSpace_source
  haveI := (maxBranched_instances hS hregN y₀).2.2
  haveI := (maxBranched_instances hS hregN yN).2.2
  obtain ⟨Φ₀, hΦ₀c, hΦ₀b, hΦ₀bc, -⟩ := maxBranched_universal hS hregN y₀ hβ₁ hβS₁
  obtain ⟨Ψ₀, hΨ₀c, hΨ₀b, -, -⟩ := maxBranched_universal hS hregN yN hβ₀ hβS₀
  have hgal₁ := maxBranched_isGaloisian_cc hS hregN yN hgal
  obtain ⟨δ, hδ, hδe⟩ := hgal₁.2 (Φ₀ e) f (by rw [hΦ₀b, hf]; rfl)
  set Φ₁ : MaxBranchedCover (Sing G X N) y₀ → MaxBranchedCover (Sing G X N) yN :=
    fun x => δ (Φ₀ x) with hΦ₁
  have hΦ₁c : Continuous Φ₁ := δ.continuous.comp hΦ₀c
  have hΦ₁b : ∀ x, (Φ₁ x).base = x.base := fun x => by
    show (δ (Φ₀ x)).base = x.base; rw [deck_apply _ hδ, hΦ₀b]
  have hΦ₁s : Surjective Φ₁ := δ.surjective.comp hΦ₀bc.surjective
  obtain ⟨σ, hσ, hσeq⟩ := exists_deck_eq_of_base_eq_maxBranched hregN hΦ₁c hΨ₀c hΦ₁b hΨ₀b
  set Φinv : MaxBranchedCover (Sing G X N) yN → MaxBranchedCover (Sing G X N) y₀ :=
    fun v => σ.symm (Ψ₀ v) with hΦinv
  have hΦinvc : Continuous Φinv := σ.symm.continuous.comp hΨ₀c
  have hΦinvb : ∀ v, (Φinv v).base = v.base := fun v => by
    have h := deck_apply _ (inv_mem hσ) (Ψ₀ v)
    show (σ.symm (Ψ₀ v)).base = v.base
    rw [← hΨ₀b v]; exact h
  have hleft : ∀ x, Φinv (Φ₁ x) = x := fun x => by
    show σ.symm (Ψ₀ (Φ₁ x)) = x
    rw [hσeq x, Homeomorph.symm_apply_apply]
  have hright : ∀ v, Φ₁ (Φinv v) = v := fun v => by
    obtain ⟨x, rfl⟩ := hΦ₁s v
    rw [hleft x]
  have hcc₀ : connectedComponentIn ((SpreadEnd.base : MaxBranchedCover (Sing G X N) y₀ → N) ⁻¹'
      ((⊤ : Opens N) : Set N)) e = univ := by
    rw [Opens.coe_top, preimage_univ, connectedComponentIn_univ,
      PreconnectedSpace.connectedComponent_eq_univ]
  have hcc₁ : connectedComponentIn ((SpreadEnd.base : MaxBranchedCover (Sing G X N) yN → N) ⁻¹'
      ((⊤ : Opens N) : Set N)) f = univ := by
    rw [Opens.coe_top, preimage_univ, connectedComponentIn_univ,
      PreconnectedSpace.connectedComponent_eq_univ]
  refine ⟨{ toFun := fun z => ⟨Φ₁ z, by rw [hcc₁]; trivial⟩
            invFun := fun w => ⟨Φinv w, by rw [hcc₀]; trivial⟩
            left_inv := fun z => Subtype.ext (hleft z)
            right_inv := fun w => Subtype.ext (hright w)
            continuous_toFun := (hΦ₁c.comp continuous_subtype_val).subtype_mk
              fun _ => by rw [hcc₁]; trivial
            continuous_invFun := (hΦinvc.comp continuous_subtype_val).subtype_mk
              fun _ => by rw [hcc₀]; trivial }, ?_, ?_⟩
  · show δ (Φ₀ e) = f
    exact hδe
  · intro z
    show (Φ₁ z).base = _
    rw [hΦ₁b]; rfl

end LiftWitness


/-! ### `theo:local_virt_tame` -/

section LocalVirtTame

variable {G : Type*} {X : Type*} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
  [FaithfulSMul G X]
  {A : Type*} {Xα : A → Type u} [∀ a, TopologicalSpace (Xα a)] [∀ a, T2Space (Xα a)]
  [∀ a, LocPathConnectedSpace (Xα a)] [∀ a, FirstCountableTopology (Xα a)]
  [∀ a, ConnectedSpace (Xα a)] [∀ a, SingularGXStructure G X (Xα a)] {S : ∀ a, Set (Xα a)}

variable (G X) in
/-- The hypothesis of `theo:local_virt_tame` on a model: a tamifying topology `T` on
`\widetilde X_α` for which `Aut(\widetilde X_α)` acts continuously — every isomorphism of
`\widetilde X_α` (with the structure `p^*B` of `prop:singular_manifold_branched_covering`) is
`T`-continuous. -/
def HasAutContinuousTamifying (N : Type u) [TopologicalSpace N] [SingularGXStructure G X N] :
    Prop :=
  ∃ (y₀ : ((Sing G X N)ᶜ : Set N)) (T : TopologicalSpace (MaxBranchedCover (Sing G X N) y₀)),
    IsTamifyingTopology G X N y₀ T ∧ ∀ f ∈ aeAutMapsMax G X N y₀, Continuous[T, T] f

/-- The model of the hypothesis is virtually tame. -/
theorem HasAutContinuousTamifying.isVirtuallyTame {N : Type u} [TopologicalSpace N]
    [SingularGXStructure G X N] (h : HasAutContinuousTamifying G X N) : IsVirtuallyTame G X N := by
  obtain ⟨y₀, T, hT, -⟩ := h
  exact ⟨y₀, T, hT⟩

/-- `theo:local_virt_tame`, piece (2) of the proof (l.2088–2140), stated: the topologies
`T_{U,V,φ}`. For every `X_A`-chart `c = (U, V, φ)` of type `α` there is a local tamifying topology
over `U` (`IsLocalTamifying`: on a component `Û` of `p⁻¹(U)`, the quotient by `ℓ : \widetilde U → Û`
of `φ̃^*(r^*T_α)`, `r : \widetilde V → V̂` and `φ̃ : \widetilde U ≃ \widetilde V` the lift of `φ`),
and these topologies are natural: two `X_α`-charts which, on a connected open `W` inside both
domains, differ by an automorphism `ψ ∈ Aut(X_α)` (`ψ ∘ φ₁ = φ₂` on `W`) give the same
neighbourhoods at every point of `p⁻¹(W)`. The paper proves the independence of `(V, φ)` for a
fixed `U` (l.2104–2107); the naturality under restriction to `W ⊆ U` is used by its gluing
(l.2101, "generated by … all `X_A`-charts") but not stated (finding). STATED in general (tagged
`sorry`, a mathematical obstruction recorded there, confined to the non-descending charts); built
and proved for the charts descending from the maximal coverings of the models (`ℓ` arbitrary):
`descTop`, `isLocalTamifying_descTop`, `nhds_descTop_le_of_aut`, and for the liftable ones
(`chartTop`, `isLocalTamifying_chartTop`, `nhds_chartTop_le_of_aut`). -/
theorem exists_isLocalTamifying_charts (hX : IsLocallyUnloopable X)
    (hfam : IsAnalyticModelFamily G X Xα S) (hgal : ∀ a, IsLocallyGaloisian G X (Xα a))
    (htam : ∀ a, HasAutContinuousTamifying G X (Xα a)) {M : Type v} [TopologicalSpace M]
    [T2Space M] [LocPathConnectedSpace M] [FirstCountableTopology M] [ConnectedSpace M]
    [SingularGXStructure G X M] (y₀ : ((Sing G X M)ᶜ : Set M))
    {D₀ : MaxBranchedCover (Sing G X M) y₀ → X} (hD₀ : IsRegDevelopingOnReg G X M y₀ D₀) :
    ∃ T : (Σ a : A, Σ x : M, XAChart G X Xα S a x) →
        TopologicalSpace (MaxBranchedCover (Sing G X M) y₀),
      (∀ c, IsLocalTamifying G X M y₀ D₀ (c.2.2.U : Set M) (T c)) ∧
      ∀ (a : A) (x₁ x₂ : M) (c₁ : XAChart G X Xα S a x₁) (c₂ : XAChart G X Xα S a x₂)
        (W : Opens M) (h₁ : W ≤ c₁.U) (h₂ : W ≤ c₂.U), IsConnected (W : Set M) →
        ∀ ψ ∈ singularAut G X (Xα a),
          (∀ w : W, ψ (c₁.φ ⟨w, h₁ w.2⟩ : Xα a) = (c₂.φ ⟨w, h₂ w.2⟩ : Xα a)) →
          ∀ e : MaxBranchedCover (Sing G X M) y₀, e.base ∈ W →
            @nhds _ (T ⟨a, x₁, c₁⟩) e = @nhds _ (T ⟨a, x₂, c₂⟩) e := by
  sorry -- SORRY(theo:local_virt_tame): piece (2) IN GENERAL — the charts which do NOT descend
  -- from the maximal covering of their model (`IsDescendingChartMap` fails: `V̂ → V` does not
  -- dominate `Û → U`, so `r : Ṽ → V̂` (l.2088–2098) is not an isomorphism). Built and proved for
  -- every descending chart, with `ℓ : Ũ → Û` ARBITRARY (fix round 1): the `ℓ`-quotient of `T_α`,
  -- `descTop`, `isLocalTamifying_descTop`, `nhds_descTop_le_of_aut`, `isVirtuallyTame_of_descending`,
  -- 0 `sorry` — so the `ℓ`-quotient is NOT what blocks this. What blocks it is a MATHEMATICAL
  -- obstruction on the `r` side: for a non-descending chart the paper's `T_{U,V,φ}` is the
  -- `ℓ`-quotient of `r^*T_α`, and its (D) (l.2128–2133) needs `r⁻¹(R)` portly in `Ṽ` for
  -- `r^*T_α`, i.e. `lem:spread_top` (c) for `r`, and (c) is false in general (WP-27k,
  -- `GX.not_spreadTopConnCE` on `GX.cex_spread_top_sector`): it is equivalent to the local
  -- condition `GX.StrongLocallyConnectedOrd` (`GX.isPortly_strongPullTop_iff_local`), which "`T_α`
  -- tamifying, `Aut(\widetilde X_α)`-continuous, `X_α` locally Galoisian" is not known to imply.
  -- Mechanism (informal, not formalized): when a loop around the singular stratum near a point of
  -- `V` dies in `π₁(reg X_α)` but not in `π₁(reg V)`, a `T_α`-neighbourhood `O` of a singular point
  -- of `V̂` whose regular part carries no such loop has, in `r⁻¹(O)`, a component through the
  -- singular point whose regular part falls into infinitely many sheets. WP-40c: the obstruction is
  -- INTRINSIC — any tamifying topology on `\widetilde M` must carry each deck transformation fixing
  -- a point in the `D`-small regular part of every neighbourhood of it
  -- (`IsTamifyingTopology.exists_joinedIn_devSmall`, `not_isVirtuallyTame_of_forall_not_joinedIn`),
  -- so another topology than `T_{U,V,φ}` cannot escape it; and at finite local degree a tamifying
  -- topology is natural (`IsTamifyingTopology.nhds_eq_of_finite_stab`), which REFUTES WP-35f's
  -- candidate (two crossing singular planes in dimension 4: the dying meridian is a meridian of a
  -- stratum of local degree 1, so by (A) every `T_α`-neighbourhood carries it). A counterexample
  -- would need a local loop of `reg V̂` not generated by meridians of strata of finite local
  -- degree (e.g. a commutator at the vertex of a singular tripod in dimension 3) avoided by every
  -- `D_α`-small region; no such model is known, none is in the library (it has no non-tame
  -- singular manifold), and the theorem is neither proved nor refuted. Besides (D), the
  -- non-descending case would need
  -- the maximal covering `Ṽ` of `V̂` and the pull-back `r^*T_α` (`strongPullTop`) on it, which are
  -- infrastructure; they are not built because their (D) is not known to hold under the theorem's
  -- hypotheses (it fails for `lem:spread_top` in general, WP-27k). Settled inputs: the
  -- Galoisianity of the sub-coverings (l.2025, l.2093) is `GX.isGaloisian_of_comp` (WP-27k) and,
  -- for descents, `IsChartDescent.exists_deck`; restriction-naturality (l.2101) is
  -- `nhds_descTop_le_of_aut`.

/-- `theo:local_virt_tame`, (ii) ⇒ (i) (`RamcovGX.tex:1974`, proof l.2086–2140), in general,
`X_A`-manifolds read as ruled (DEC-67 (e): every singular point has a type), STATED: it rests on
the general piece (2), `exists_isLocalTamifying_charts` (tagged `sorry`, a mathematical obstruction:
the paper's (D) needs `lem:spread_top` (c), false in general). The gluing (l.2101–2103) is proved
(`exists_isTamifyingTopology_of_local`): near a singular point `y` of type `b`, every chart has type
`b` (`XAChart.eq_of_mem_centre`) and differs from a chart centred at `y` by an automorphism of
`X_b` (`XAChart.exists_aut_eq`), so all the local topologies agree there (naturality); over
`reg(M)` they are the natural one. Proved, 0 `sorry`, when the charts descend from the maximal
coverings of the models (`isVirtuallyTame_of_descending`, `ℓ` arbitrary) and, without local
Galoisianity, when they lift (`isVirtuallyTame_of_liftable`). -/
theorem isVirtuallyTame_of_isXAManifold (hX : IsLocallyUnloopable X)
    (hfam : IsAnalyticModelFamily G X Xα S) (hgal : ∀ a, IsLocallyGaloisian G X (Xα a))
    (htam : ∀ a, HasAutContinuousTamifying G X (Xα a)) {M : Type v} [TopologicalSpace M]
    [T2Space M] [LocPathConnectedSpace M] [FirstCountableTopology M] [ConnectedSpace M]
    [SingularGXStructure G X M] (hM : IsXAManifold G X Xα S M) : IsVirtuallyTame G X M := by
  have htype := hM.hasType
  obtain ⟨y₀⟩ := (nonempty_compl_of_isSkeletal (isSkeletal_sing G X M)).to_subtype
  have hreg := semilocallySimplyConnected_compl_of_sing_subset (G := G) hX
    (isClosed_sing G X M) subset_rfl
  obtain ⟨D₀, hD₀⟩ := exists_isRegDevelopingOnReg hreg y₀
  obtain ⟨T, hT, hnat⟩ := exists_isLocalTamifying_charts hX hfam hgal htam y₀ hD₀
  have hcov : ∀ y : M, ∃ c : (Σ a : A, Σ x : M, XAChart G X Xα S a x),
      y ∈ (c.2.2.U : Set M) := fun y => by
    obtain ⟨a, x, c, hy⟩ := isXAManifoldPrinted_iff.1 hM.exists_atlas y
    exact ⟨⟨a, x, c⟩, hy⟩
  -- near a point which has a type, every chart has that type and differs from a chart centred
  -- there by an automorphism of the model: the local topologies agree
  have key : ∀ (b : A) (y : M) (c₀ : XAChart G X Xα S b y)
      (c : Σ a : A, Σ x : M, XAChart G X Xα S a x) (e : MaxBranchedCover (Sing G X M) y₀),
      e.base = y → y ∈ (c.2.2.U : Set M) →
        @nhds _ (T ⟨b, y, c₀⟩) e = @nhds _ (T c) e := by
    rintro b y c₀ ⟨a, x, c⟩ e rfl hy
    set W : Opens M := ⟨connectedComponentIn ((c₀.U : Set M) ∩ c.U) e.base,
      (c₀.U.isOpen.inter c.U.isOpen).connectedComponentIn⟩
    have hyW : e.base ∈ W := mem_connectedComponentIn ⟨c₀.mem, hy⟩
    have hW₀ : W ≤ c₀.U := fun z hz => (connectedComponentIn_subset _ _ hz).1
    have hW : W ≤ c.U := fun z hz => (connectedComponentIn_subset _ _ hz).2
    have hWc : IsConnected (W : Set M) := isConnected_connectedComponentIn_iff.2 ⟨c₀.mem, hy⟩
    obtain rfl := XAChart.eq_of_mem_centre hfam c₀ c W hW₀ hW hWc hyW
    obtain ⟨ψ, hψ, hψeq⟩ := c₀.exists_aut_eq hfam c W hW₀ hW hWc hyW
    exact hnat b _ _ c₀ c W hW₀ hW hWc ψ hψ hψeq e hyW
  have hcompat : ∀ (i j : Σ a : A, Σ x : M, XAChart G X Xα S a x)
      (e : MaxBranchedCover (Sing G X M) y₀), e.base ∈ (i.2.2.U : Set M) →
        e.base ∈ (j.2.2.U : Set M) → @nhds _ (T i) e = @nhds _ (T j) e := by
    intro i j e hi hj
    by_cases hy : e.base ∈ Reg G X M
    · rw [(hT i).nhds_reg e hi hy, (hT j).nhds_reg e hj hy]
    · obtain ⟨b, ⟨c₀⟩⟩ := htype e.base hy
      rw [← key b _ c₀ i e rfl hi, key b _ c₀ j e rfl hj]
  obtain ⟨T', hT'⟩ := exists_isTamifyingTopology_of_local hD₀ (fun c => (c.2.2.U : Set M))
    (fun c => c.2.2.U.isOpen) hcov T hT hcompat
  exact ⟨y₀, T', hT'⟩

/-- `theo:local_virt_tame` (`RamcovGX.tex:1974`), `X_A`-manifolds read as ruled (DEC-67 (e)), in
general (STATED, through `isVirtuallyTame_of_isXAManifold`): under its hypotheses, (i) every
`X_A`-manifold is virtually tame iff (ii) every model `X_α` is virtually tame. (i) ⇒ (ii) does not
go through the models (under DEC-67 (e) a model `X_α` need not be an `X_A`-manifold, a point of
`sing X_α ∖ S_α` may have no type): (ii) holds outright by the hypothesis on the models
(`HasAutContinuousTamifying.isVirtuallyTame`), the degeneracy recorded in the findings. The proved
forms are `local_virt_tame_descending` (charts descending from the models' maximal coverings) and
`local_virt_tame_liftable`. -/
theorem local_virt_tame (hX : IsLocallyUnloopable X) (hfam : IsAnalyticModelFamily G X Xα S)
    (hgal : ∀ a, IsLocallyGaloisian G X (Xα a)) (htam : ∀ a, HasAutContinuousTamifying G X (Xα a)) :
    (∀ (N : Type u) [TopologicalSpace N] [T2Space N] [LocPathConnectedSpace N]
        [FirstCountableTopology N] [ConnectedSpace N] [SingularGXStructure G X N],
        IsXAManifold G X Xα S N → IsVirtuallyTame G X N) ↔ ∀ a, IsVirtuallyTame G X (Xα a) :=
  ⟨fun _ a => (htam a).isVirtuallyTame, fun _ _ _ _ _ _ _ _ hN =>
    isVirtuallyTame_of_isXAManifold hX hfam hgal htam hN⟩

/-- `theo:local_virt_tame`, (ii) ⇒ (i), the case of tame models (the natural topologies tamifying,
`isTame_iff_isTamifyingTopology_natural`), proved: every `X_A`-manifold over tame models is
virtually tame, its natural topology being tamifying. Neither analyticity nor local Galoisianity is
used. -/
theorem isVirtuallyTame_of_isXAManifold_of_isTame (hX : IsLocallyUnloopable X)
    (htame : ∀ a, IsTame G X (Xα a)) {M : Type v} [TopologicalSpace M]
    [T2Space M] [LocPathConnectedSpace M] [FirstCountableTopology M] [ConnectedSpace M]
    [SingularGXStructure G X M] (hM : IsXAManifold G X Xα S M) : IsVirtuallyTame G X M :=
  (isTame_of_isXAManifold hX htame hM).isVirtuallyTame hX

end LocalVirtTame

section LiftedVirtTame

variable {G : Type*} {X : Type*} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
  [FaithfulSMul G X]
  {A : Type*} {Xα : A → Type u} [∀ a, TopologicalSpace (Xα a)] [∀ a, T2Space (Xα a)]
  [∀ a, LocPathConnectedSpace (Xα a)] [∀ a, FirstCountableTopology (Xα a)]
  [∀ a, ConnectedSpace (Xα a)] [∀ a, SingularGXStructure G X (Xα a)] {S : ∀ a, Set (Xα a)}

/-- `theo:local_virt_tame`, (ii) ⇒ (i), proved in the case its proof's coverings are trivial: if
every singular point of `M` is the centre of an `X_A`-chart which lifts to the maximal coverings
(`IsLiftableChartMap`: `ℓ : Ũ → Û` and `r : Ṽ → V̂` isomorphisms), then `M` is virtually tame.
The local topologies are the `T_{U,V,φ}` (`chartTop`, `isLocalTamifying_chartTop`) over the
liftable charts and the natural one over `reg M` (`isLocalTamifying_natural_reg`); they agree over
the overlaps by naturality (`nhds_chartTop_le_of_aut`, the paper's l.2104–2107, through
`XAChart.eq_of_mem_centre` and `XAChart.exists_aut_eq`), and glue
(`exists_isTamifyingTopology_of_local`). Neither local Galoisianity nor the `X_A`-atlas is used
(the liftable charts carry what they give). Superseded, under local Galoisianity, by
`isVirtuallyTame_of_descending` (`ℓ : Ũ → Û` arbitrary). -/
theorem isVirtuallyTame_of_liftable (hX : IsLocallyUnloopable X)
    (hfam : IsAnalyticModelFamily G X Xα S) (htam : ∀ a, HasAutContinuousTamifying G X (Xα a))
    {M : Type v} [TopologicalSpace M] [T2Space M] [LocPathConnectedSpace M]
    [FirstCountableTopology M] [ConnectedSpace M] [SingularGXStructure G X M]
    (hlift : ∀ y ∈ Sing G X M, ∃ (a : A) (c : XAChart G X Xα S a y), IsLiftableChartMap G X c.φ) :
    IsVirtuallyTame G X M := by
  obtain ⟨y₀⟩ := (nonempty_compl_of_isSkeletal (isSkeletal_sing G X M)).to_subtype
  have hregM := semilocallySimplyConnected_compl_of_sing_subset (G := G) hX
    (isClosed_sing G X M) subset_rfl
  have hregN : ∀ a, SemilocallySimplyConnected ((Sing G X (Xα a))ᶜ : Set (Xα a)) := fun a =>
    semilocallySimplyConnected_compl_of_sing_subset (G := G) hX (isClosed_sing G X (Xα a)) subset_rfl
  obtain ⟨D₀, hD₀⟩ := exists_isRegDevelopingOnReg hregM y₀
  have htam' : ∀ a, ∃ (yN : ((Sing G X (Xα a))ᶜ : Set (Xα a)))
      (TN : WrappedTop (MaxBranchedCover (Sing G X (Xα a)) yN)),
      IsTamifyingTopology G X (Xα a) yN TN.top ∧
        ∀ f ∈ aeAutMapsMax G X (Xα a) yN, Continuous[TN.top, TN.top] f := fun a => by
    obtain ⟨y, T, h1, h2⟩ := htam a
    exact ⟨y, ⟨T⟩, h1, h2⟩
  choose yN TN hTN hAut using htam'
  have hDN : ∀ a, ∃ D : MaxBranchedCover (Sing G X (Xα a)) (yN a) → X,
      Continuous[(TN a).top, _] D ∧ IsRegDevelopingOnReg G X (Xα a) (yN a) D :=
    fun a => (hTN a).exists_extension
  choose DN hDNc hDNr using hDN
  have hFam : ∀ c : {c : Σ a : A, Σ x : M, XAChart G X Xα S a x //
        IsLiftableChartMap G X c.2.2.φ},
      ∃ Fz : MaxBranchedCover (Sing G X M) y₀ → MaxBranchedCover (Sing G X M) y₀ →
          MaxBranchedCover (Sing G X (Xα c.1.1)) (yN c.1.1),
        ∀ z : MaxBranchedCover (Sing G X M) y₀, z.base ∈ (c.1.2.2.U : Set M) →
          ∃ F', IsChartLift (c.1.2.2.U : Set M) (c.1.2.2.V : Set (Xα c.1.1))
            (chartExt c.1.2.2.φ) z (Fz z z) (Fz z) F' := by
    rintro ⟨⟨a, x, c⟩, hc⟩
    obtain ⟨-, hβN, -, -, -, -⟩ := maxBranched_basic (isSkeletal_sing G X (Xα a)) (hregN a) (yN a)
    obtain ⟨f₀, -⟩ := hβN.surjective (Classical.arbitrary (Xα a))
    have : ∀ z : MaxBranchedCover (Sing G X M) y₀, ∃ F : MaxBranchedCover (Sing G X M) y₀ →
        MaxBranchedCover (Sing G X (Xα a)) (yN a), z.base ∈ (c.U : Set M) →
          ∃ F', IsChartLift (c.U : Set M) (c.V : Set (Xα a)) (chartExt c.φ) z (F z) F F' := by
      intro z
      by_cases hz : z.base ∈ (c.U : Set M)
      · obtain ⟨f, hf⟩ := hβN.surjective (chartExt c.φ z.base)
        obtain ⟨F, F', hl⟩ := hc.exists_isChartLift z f hz (by rw [hf, chartExt_apply])
        refine ⟨F, fun _ => ⟨F', ?_⟩⟩
        rw [hl.apply_self]; exact hl
      · exact ⟨fun _ => f₀, fun h => absurd h hz⟩
    choose Fz hFz using this
    exact ⟨Fz, fun z hz => hFz z hz⟩
  choose Fz hFz using hFam
  let ι := Option {c : Σ a : A, Σ x : M, XAChart G X Xα S a x // IsLiftableChartMap G X c.2.2.φ}
  let U : ι → Set M := fun i => match i with
    | none => Reg G X M
    | some c => (c.1.2.2.U : Set M)
  let T : ι → TopologicalSpace (MaxBranchedCover (Sing G X M) y₀) := fun i => match i with
    | none => weakTopMax G X M y₀
    | some c => chartTop (c.1.2.2.U : Set M) (Fz c) ⟨(TN c.1.1).top⟩
  have hUo : ∀ i, IsOpen (U i) := by
    rintro (_ | c)
    · exact isOpen_reg G X M
    · exact c.1.2.2.U.isOpen
  have hT : ∀ i, IsLocalTamifying G X M y₀ D₀ (U i) (T i) := by
    rintro (_ | ⟨⟨a, x, c⟩, hc⟩)
    · exact isLocalTamifying_natural_reg hregM hD₀
    · exact isLocalTamifying_chartTop hregM (hregN a) c.U.isOpen c.V.isOpen (hFz ⟨⟨a, x, c⟩, hc⟩)
        (fun m hm => chartExt_mem_reg_iff c.isAEMorphism hm) (hTN a)
        (fun z f hz hf => hc.exists_isChartLift z f hz (by rw [hf, chartExt_apply]))
        (continuousOn_chartExt c.φ)
        (fun m hm m' hm' h => by
          rw [chartExt_apply c.φ hm, chartExt_apply c.φ hm'] at h
          exact congrArg Subtype.val (c.φ.injective (Subtype.ext h)))
        (hDNc a) (fun z hz => exists_smul_eq_of_isChartLift hregM (hregN a) c.isAEMorphism hD₀
          (hDNr a) hz (hFz ⟨⟨a, x, c⟩, hc⟩ z hz).choose_spec)
  have hcov : ∀ y : M, ∃ i, y ∈ U i := fun y => by
    by_cases hy : y ∈ Reg G X M
    · exact ⟨none, hy⟩
    · obtain ⟨a, c, hc⟩ := hlift y hy
      exact ⟨some ⟨⟨a, y, c⟩, hc⟩, c.mem⟩
  -- naturality at a singular point: every liftable chart agrees with one centred there
  have key : ∀ (b : A) (y : M) (c₀ : XAChart G X Xα S b y) (hc₀ : IsLiftableChartMap G X c₀.φ)
      (i : ι) (e : MaxBranchedCover (Sing G X M) y₀), e.base = y → y ∉ Reg G X M →
      e.base ∈ U i → @nhds _ (T (some ⟨⟨b, y, c₀⟩, hc₀⟩)) e = @nhds _ (T i) e := by
    rintro b y c₀ hc₀ (_ | ⟨⟨a, x, c⟩, hc⟩) e rfl hsing hi
    · exact absurd hi hsing
    set W : Opens M := ⟨connectedComponentIn ((c₀.U : Set M) ∩ c.U) e.base,
      (c₀.U.isOpen.inter c.U.isOpen).connectedComponentIn⟩
    have hyW : e.base ∈ W := mem_connectedComponentIn ⟨c₀.mem, hi⟩
    have hW₀ : W ≤ c₀.U := fun z hz => (connectedComponentIn_subset _ _ hz).1
    have hW : W ≤ c.U := fun z hz => (connectedComponentIn_subset _ _ hz).2
    have hWc : IsConnected (W : Set M) := isConnected_connectedComponentIn_iff.2 ⟨c₀.mem, hi⟩
    obtain rfl := XAChart.eq_of_mem_centre hfam c₀ c W hW₀ hW hWc hyW
    obtain ⟨ψ, hψ, hψeq⟩ := c₀.exists_aut_eq hfam c W hW₀ hW hWc hyW
    have hψφ : ∀ m ∈ (W : Set M), ψ (chartExt c₀.φ m) = chartExt c.φ m := fun m hm => by
      rw [chartExt_apply _ (hW₀ hm), chartExt_apply _ (hW hm)]; exact hψeq ⟨m, hm⟩
    have hψφ' : ∀ m ∈ (W : Set M), ψ⁻¹ (chartExt c.φ m) = chartExt c₀.φ m := fun m hm => by
      rw [← hψφ m hm]; exact ψ.symm_apply_apply _
    exact le_antisymm
      (nhds_chartTop_le_of_aut hregM (hregN b) c₀.U.isOpen c₀.V.isOpen
        (hFz ⟨⟨b, e.base, c₀⟩, hc₀⟩) (fun m hm => chartExt_mem_reg_iff c₀.isAEMorphism hm)
        c.U.isOpen c.V.isOpen (hFz ⟨⟨b, x, c⟩, hc⟩)
        (fun m hm => chartExt_mem_reg_iff c.isAEMorphism hm) (hTN b) (hAut b) W.isOpen hW₀ hW
        hψ hψφ hyW)
      (nhds_chartTop_le_of_aut hregM (hregN b) c.U.isOpen c.V.isOpen
        (hFz ⟨⟨b, x, c⟩, hc⟩) (fun m hm => chartExt_mem_reg_iff c.isAEMorphism hm)
        c₀.U.isOpen c₀.V.isOpen (hFz ⟨⟨b, e.base, c₀⟩, hc₀⟩)
        (fun m hm => chartExt_mem_reg_iff c₀.isAEMorphism hm) (hTN b) (hAut b) W.isOpen hW hW₀
        (inv_mem hψ) hψφ' hyW)
  have hcompat : ∀ i j (e : MaxBranchedCover (Sing G X M) y₀), e.base ∈ U i → e.base ∈ U j →
      @nhds _ (T i) e = @nhds _ (T j) e := by
    intro i j e hi hj
    by_cases hy : e.base ∈ Reg G X M
    · rw [(hT i).nhds_reg e hi hy, (hT j).nhds_reg e hj hy]
    · obtain ⟨b, c₀, hc₀⟩ := hlift e.base hy
      rw [← key b _ c₀ hc₀ i e rfl hy hi, key b _ c₀ hc₀ j e rfl hy hj]
  obtain ⟨T', hT'⟩ := exists_isTamifyingTopology_of_local hD₀ U hUo hcov T hT hcompat
  exact ⟨y₀, T', hT'⟩

end LiftedVirtTame

section LiftedVirtTameEquiv

variable {G : Type*} {X : Type*} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
  [FaithfulSMul G X]
  {A : Type*} {Xα : A → Type u} [∀ a, TopologicalSpace (Xα a)] [∀ a, T2Space (Xα a)]
  [∀ a, LocPathConnectedSpace (Xα a)] [∀ a, FirstCountableTopology (Xα a)]
  [∀ a, ConnectedSpace (Xα a)] [∀ a, SingularGXStructure G X (Xα a)] {S : ∀ a, Set (Xα a)}

/-- `theo:local_virt_tame` (`RamcovGX.tex:1974`), proved for the `X_A`-manifolds whose singular
points are centres of charts lifting to the maximal coverings (`IsLiftableChartMap`): under the
theorem's hypotheses (analytic family, a tamifying topology on each `\widetilde X_α` on which
`Aut(\widetilde X_α)` acts continuously), (i) every such `X_A`-manifold is virtually tame iff (ii)
every model is virtually tame. (ii) ⇒ (i) is `isVirtuallyTame_of_liftable`; (i) ⇒ (ii) holds
outright by the hypothesis on the models, as in `local_virt_tame`. Local Galoisianity of the models
is not used. -/
theorem local_virt_tame_liftable (hX : IsLocallyUnloopable X)
    (hfam : IsAnalyticModelFamily G X Xα S) (htam : ∀ a, HasAutContinuousTamifying G X (Xα a)) :
    (∀ (N : Type u) [TopologicalSpace N] [T2Space N] [LocPathConnectedSpace N]
        [FirstCountableTopology N] [ConnectedSpace N] [SingularGXStructure G X N],
        IsXAManifold G X Xα S N →
        (∀ y ∈ Sing G X N, ∃ (a : A) (c : XAChart G X Xα S a y), IsLiftableChartMap G X c.φ) →
        IsVirtuallyTame G X N) ↔ ∀ a, IsVirtuallyTame G X (Xα a) :=
  ⟨fun _ a => (htam a).isVirtuallyTame, fun _ _ _ _ _ _ _ _ _ hlift =>
    isVirtuallyTame_of_liftable hX hfam htam hlift⟩

/-- The liftability hypothesis is met at the points of `S_α` of a model whose maximal covering is
Galoisian (`isLiftableChartMap_refl`): the chart `(X_α, X_α, id)`. -/
theorem isLiftableChartMap_modelChartSelf (a : A)
    (hregN : SemilocallySimplyConnected ((Sing G X (Xα a))ᶜ : Set (Xα a)))
    (hgal : IsSLSCInCC ((Sing G X (Xα a))ᶜ : Set (Xα a))) {s : Xα a} (hs : s ∈ S a) :
    IsLiftableChartMap G X (modelChartSelf G X S a hs).φ :=
  isLiftableChartMap_refl hregN hgal

end LiftedVirtTameEquiv

section Descent

variable {G : Type*} {X : Type*} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
  {M : Type v} [TopologicalSpace M] [T2Space M] [LocPathConnectedSpace M]
  [FirstCountableTopology M] [ConnectedSpace M] [SingularGXStructure G X M]
  {N : Type u} [TopologicalSpace N] [T2Space N] [LocPathConnectedSpace N]
  [FirstCountableTopology N] [ConnectedSpace N] [SingularGXStructure G X N]
  {y₀ : ((Sing G X M)ᶜ : Set M)} {yN : ((Sing G X N)ᶜ : Set N)}

/-- A *descent* of `φ' : M → N` from the component `V̂ ∋ f` of `q⁻¹(V)` in `\widetilde N`: a map
`Ψ` continuous on `V̂`, with values over `U`, and over `φ'⁻¹` (`φ' ∘ p ∘ Ψ = q` on `V̂`). This is
the map `ℓ ∘ φ̃⁻¹ ∘ r⁻¹ : V̂ → Û` of the proof of `theo:local_virt_tame` (l.2088–2098) when `r` is
an isomorphism, and more generally whenever `V̂ → V` dominates `Û → U`. -/
structure IsChartDescent (U : Set M) (V : Set N) (φ' : M → N)
    (f : MaxBranchedCover (Sing G X N) yN)
    (Ψ : MaxBranchedCover (Sing G X N) yN → MaxBranchedCover (Sing G X M) y₀) : Prop where
  base_mem : f.base ∈ V
  contOn : ContinuousOn Ψ (connectedComponentIn (SpreadEnd.base ⁻¹' V) f)
  mem : ∀ w ∈ connectedComponentIn (SpreadEnd.base ⁻¹' V) f, (Ψ w).base ∈ U
  base : ∀ w ∈ connectedComponentIn (SpreadEnd.base ⁻¹' V) f, φ' (Ψ w).base = w.base

/-- A descent restricts to a component of `q⁻¹(B)`, `B ⊆ V` open. -/
theorem IsChartDescent.restrict {U U' : Set M} {V B : Set N} {φ' : M → N}
    {f : MaxBranchedCover (Sing G X N) yN}
    {Ψ : MaxBranchedCover (Sing G X N) yN → MaxBranchedCover (Sing G X M) y₀}
    (h : IsChartDescent U V φ' f Ψ) (hBV : B ⊆ V)
    {v : MaxBranchedCover (Sing G X N) yN} (hv : v ∈ connectedComponentIn (SpreadEnd.base ⁻¹' V) f)
    (hvB : v.base ∈ B) (hUU' : ∀ m ∈ U, φ' m ∈ B → m ∈ U') :
    IsChartDescent U' B φ' v Ψ := by
  have hsub : connectedComponentIn ((SpreadEnd.base : MaxBranchedCover (Sing G X N) yN → N) ⁻¹' B) v ⊆
      connectedComponentIn (SpreadEnd.base ⁻¹' V) f := by
    rw [connectedComponentIn_eq hv]
    exact connectedComponentIn_mono _ (preimage_mono hBV)
  refine ⟨hvB, h.contOn.mono hsub, fun w hw => hUU' _ (h.mem w (hsub hw)) ?_, fun w hw =>
    h.base w (hsub hw)⟩
  rw [h.base w (hsub hw)]
  exact mem_of_mem_connectedComponentIn_preimage hw

/-- The image of a descent is connected, so it lies in one component of `p⁻¹(U)`. -/
theorem IsChartDescent.mapsTo_cc {U : Set M} {V : Set N} {φ' : M → N}
    {f : MaxBranchedCover (Sing G X N) yN}
    {Ψ : MaxBranchedCover (Sing G X N) yN → MaxBranchedCover (Sing G X M) y₀}
    (h : IsChartDescent U V φ' f Ψ) {v : MaxBranchedCover (Sing G X N) yN}
    (hv : v ∈ connectedComponentIn (SpreadEnd.base ⁻¹' V) f) :
    MapsTo Ψ (connectedComponentIn (SpreadEnd.base ⁻¹' V) f)
      (connectedComponentIn (SpreadEnd.base ⁻¹' U) (Ψ v)) := by
  refine image_subset_iff.1 ((isPreconnected_connectedComponentIn.image _ h.contOn).subset_connectedComponentIn
    ⟨v, hv, rfl⟩ ?_)
  rintro _ ⟨w, hw, rfl⟩
  exact h.mem w hw

variable (hregM : SemilocallySimplyConnected ((Sing G X M)ᶜ : Set M))
  (hregN : SemilocallySimplyConnected ((Sing G X N)ᶜ : Set N))
  {U : Set M} {V : Set N} {φ' : M → N} (hU : IsOpen U) (hV : IsOpen V)
  (hφc : ContinuousOn φ' U) (hφinj : InjOn φ' U) (hφV : MapsTo φ' U V)
  (hφreg : ∀ m ∈ U, φ' m ∈ Reg G X N ↔ m ∈ Reg G X M)
include hregM hregN hU hV hφc hφinj hφV hφreg

/-- A descent `Ψ` from `V̂` covers the regular part of the component of `p⁻¹(U)` it lands in
(path lifting: a path in `reg(Û)` is read through `φ'` in `reg(V)`, lifted to `V̂` through `q`,
and pushed back by `Ψ`; uniqueness of lifts through `p` over `reg M`). -/
theorem IsChartDescent.reg_subset_image {f : MaxBranchedCover (Sing G X N) yN}
    {Ψ : MaxBranchedCover (Sing G X N) yN → MaxBranchedCover (Sing G X M) y₀}
    (hΨ : IsChartDescent U V φ' f Ψ) :
    connectedComponentIn (SpreadEnd.base ⁻¹' U) (Ψ f) ∩ SpreadEnd.base ⁻¹' Reg G X M ⊆
      Ψ '' connectedComponentIn (SpreadEnd.base ⁻¹' V) f := by
  rintro c ⟨hcC, hcR⟩
  have hS₀M := isSkeletal_sing G X M
  obtain ⟨-, hβM, -, -, hβlM, -⟩ := maxBranched_basic hS₀M hregM y₀
  have hS₀N := isSkeletal_sing G X N
  obtain ⟨-, hβN, hβSN, -, hβlN, -⟩ := maxBranched_basic hS₀N hregN yN
  haveI := hβlM
  haveI := hβlN
  have hordN : Reg G X N ⊆ ordY (SpreadEnd.base : MaxBranchedCover (Sing G X N) yN → N) :=
    fun y hy => by by_contra hn; exact (hβSN hn) hy
  have hfV := mem_connectedComponentIn (F := SpreadEnd.base ⁻¹' V) hΨ.base_mem
  obtain ⟨-, -, -, -, ⟨u₀, hu₀V, hu₀R⟩⟩ := maxBranched_cc_facts hregN hV hΨ.base_mem
  have hΨfU : (Ψ f).base ∈ U := hΨ.mem f hfV
  obtain ⟨-, hCRo, hCRc, -, -⟩ := maxBranched_cc_facts hregM hU hΨfU
  have hu₀C : Ψ u₀ ∈ connectedComponentIn (SpreadEnd.base ⁻¹' U) (Ψ f) := hΨ.mapsTo_cc hfV hu₀V
  have hu₀R' : (Ψ u₀).base ∈ Reg G X M :=
    (hφreg _ (hΨ.mem u₀ hu₀V)).1 (by rw [hΨ.base u₀ hu₀V]; exact hu₀R)
  have hpc := (hCRo.isConnected_iff_isPathConnected).1 ⟨⟨_, hu₀C, hu₀R'⟩, hCRc⟩
  have hj := hpc.joinedIn _ ⟨hu₀C, hu₀R'⟩ _ ⟨hcC, hcR⟩
  set γ := hj.somePath
  have hγ : ∀ t, γ t ∈ connectedComponentIn (SpreadEnd.base ⁻¹' U) (Ψ f) ∩
      SpreadEnd.base ⁻¹' Reg G X M := hj.somePath_mem
  have hγU : ∀ t, (γ t).base ∈ U := fun t => mem_of_mem_connectedComponentIn_preimage (hγ t).1
  let β : C(unitInterval, N) := ⟨fun t => φ' (γ t).base,
    hφc.comp_continuous (SpreadEnd.continuous_base.comp γ.continuous) hγU⟩
  have hβR : ∀ t, β t ∈ Reg G X N := fun t => (hφreg _ (hγU t)).2 (hγ t).2
  -- lift `β` through `q` from `u₀`
  have he' : u₀.base ∈ ordY (SpreadEnd.base : MaxBranchedCover (Sing G X N) yN → N) :=
    hordN hu₀R
  have h0 : u₀.base = β 0 := by
    show u₀.base = φ' (γ 0).base
    rw [γ.source, hΨ.base u₀ hu₀V]
  obtain ⟨fl, hfl, hfl0, hfls⟩ := exists_partial_lift
    (isCoveringMap_restrict_ordX hβN.isSpread.continuous) β (fun t _ => hordN (hβR t)) he' h0
  obtain ⟨β', hβ', hβ'f⟩ := exists_extend_path_of_isCompleteSpread hβN.isSpread hβN.isComplete β fl
    hfl (fun t ht => (hfls t ht).2)
  have hβ'0 : β' 0 = u₀ := by rw [hβ'f 0 zero_lt_one, hfl0]
  have hβ'V : ∀ t, β' t ∈ connectedComponentIn (SpreadEnd.base ⁻¹' V) f := by
    have hrange : range β' ⊆ connectedComponentIn (SpreadEnd.base ⁻¹' V) u₀ :=
      (isPreconnected_range β'.continuous).subset_connectedComponentIn ⟨0, hβ'0⟩ (by
        rintro _ ⟨t, rfl⟩
        show (β' t).base ∈ V
        rw [hβ' t]; exact hφV (hγU t))
    intro t
    rw [connectedComponentIn_eq hu₀V]
    exact hrange ⟨t, rfl⟩
  have hEq := eqOn_maxBranched_of_base_eq hregM (E := unitInterval) (F₁ := fun t => Ψ (β' t))
    (F₂ := fun t => γ t) isOpen_univ subset_rfl isOpen_univ isPreconnected_univ
    (by rw [closure_univ]) (hΨ.contOn.comp_continuous β'.continuous hβ'V).continuousOn
    γ.continuous.continuousOn (fun t _ => hφinj (hΨ.mem _ (hβ'V t)) (hγU t) (by
      rw [hΨ.base _ (hβ'V t), hβ' t]; rfl))
    (fun t _ => (hφreg _ (hΨ.mem _ (hβ'V t))).1 (by rw [hΨ.base _ (hβ'V t), hβ' t]; exact hβR t))
    (mem_univ 0) (by show Ψ (β' 0) = γ 0; rw [hβ'0, γ.source])
  refine ⟨β' 1, hβ'V 1, ?_⟩
  have := hEq (mem_univ (1 : unitInterval))
  simp only at this
  rw [this, γ.target]

/-- The sub-covering step (`RamcovGX.tex:2093`, "since `X_α` is locally Galoisian, the branched
coverings … are all Galoisian"): two descents `Ψ₁` from `V̂₁`, `Ψ₂` from `V̂₂` (components of
`q⁻¹(V)`) which take the same value at `v₁ ∈ V̂₁`, `v₂ ∈ V̂₂` differ by an element `δ` of
`Γ(\widetilde N/N)`: `δ v₁ = v₂`, `δ(V̂₁) ⊆ V̂₂` and `Ψ₂ ∘ δ = Ψ₁` on `V̂₁`. The fibres of `q` are
discrete (`hdisc`, the model's local Galoisianity); `δ` is the deck transformation moving a regular
point `u₁` near `v₁` to a regular `u₂` near `v₂` with `Ψ₂ u₂ = Ψ₁ u₁` (`reg_subset_image`), and it
sends `v₁` into a neighbourhood of `v₂` meeting the fibre only at `v₂`. -/
theorem IsChartDescent.exists_deck
    (hdisc : ∀ x : N, DiscreteTopology
      ((SpreadEnd.base : MaxBranchedCover (Sing G X N) yN → N) ⁻¹' {x}))
    {f₁ f₂ : MaxBranchedCover (Sing G X N) yN}
    {Ψ₁ Ψ₂ : MaxBranchedCover (Sing G X N) yN → MaxBranchedCover (Sing G X M) y₀}
    (h₁ : IsChartDescent U V φ' f₁ Ψ₁) (h₂ : IsChartDescent U V φ' f₂ Ψ₂)
    {v₁ v₂ : MaxBranchedCover (Sing G X N) yN}
    (hv₁ : v₁ ∈ connectedComponentIn (SpreadEnd.base ⁻¹' V) f₁)
    (hv₂ : v₂ ∈ connectedComponentIn (SpreadEnd.base ⁻¹' V) f₂) (h : Ψ₁ v₁ = Ψ₂ v₂) :
    ∃ δ ∈ deckGroup (SpreadEnd.base : MaxBranchedCover (Sing G X N) yN → N), δ v₁ = v₂ ∧
      MapsTo δ (connectedComponentIn (SpreadEnd.base ⁻¹' V) f₁)
        (connectedComponentIn (SpreadEnd.base ⁻¹' V) f₂) ∧
      EqOn (fun w => Ψ₂ (δ w)) Ψ₁ (connectedComponentIn (SpreadEnd.base ⁻¹' V) f₁) := by
  have hS₀N := isSkeletal_sing G X N
  obtain ⟨-, hβN, -, -, hβlN, -⟩ := maxBranched_basic hS₀N hregN yN
  haveI := hβlN
  set q : MaxBranchedCover (Sing G X N) yN → N := SpreadEnd.base with hq
  have hb₁₂ : v₁.base = v₂.base := by
    rw [← h₁.base v₁ hv₁, ← h₂.base v₂ hv₂, h]
  -- a neighbourhood of `v₂` meeting its fibre only at `v₂`
  obtain ⟨N₂, hN₂o, hN₂e⟩ := isOpen_induced_iff.1
    (@isOpen_discrete _ _ (hdisc v₂.base) {(⟨v₂, rfl⟩ : q ⁻¹' {v₂.base})})
  have hv₂N₂ : v₂ ∈ N₂ := by
    have : (⟨v₂, rfl⟩ : q ⁻¹' {v₂.base}) ∈ Subtype.val ⁻¹' N₂ := by rw [hN₂e]; rfl
    exact this
  have hN₂fib : ∀ w ∈ N₂, q w = v₂.base → w = v₂ := fun w hw hwq => by
    have : (⟨w, hwq⟩ : q ⁻¹' {v₂.base}) ∈ Subtype.val ⁻¹' N₂ := hw
    rw [hN₂e] at this
    exact congrArg Subtype.val this
  obtain ⟨B₀, hB₀, hv₂B₀, hB₀N₂⟩ := (isSpread_iff.1 hβN.isSpread).2.2 v₂ N₂ hN₂o hv₂N₂
  set B := B₀ ∩ V with hBdef
  have hBo : IsOpen B := hB₀.inter hV
  have hv₂B : v₂.base ∈ B := ⟨hv₂B₀, mem_of_mem_connectedComponentIn_preimage hv₂⟩
  have hv₁B : v₁.base ∈ B := hb₁₂ ▸ hv₂B
  set U' := U ∩ φ' ⁻¹' B with hU'def
  have hU'o : IsOpen U' := hφc.isOpen_inter_preimage hU hBo
  have hUU' : ∀ m ∈ U, φ' m ∈ B → m ∈ U' := fun m hm hmB => ⟨hm, hmB⟩
  have R₁ := h₁.restrict inter_subset_right hv₁ hv₁B hUU'
  have R₂ := h₂.restrict inter_subset_right hv₂ hv₂B hUU'
  have hφc' : ContinuousOn φ' U' := hφc.mono inter_subset_left
  have hφinj' : InjOn φ' U' := hφinj.mono inter_subset_left
  have hφB : MapsTo φ' U' B := fun m hm => hm.2
  have hφreg' : ∀ m ∈ U', φ' m ∈ Reg G X N ↔ m ∈ Reg G X M := fun m hm => hφreg m hm.1
  have himg₂ := R₂.reg_subset_image hregM hregN hU'o hBo hφc' hφinj' hφB hφreg'
  -- a regular point `u₁` near `v₁`
  obtain ⟨-, -, -, -, ⟨u₁, hu₁O, hu₁R⟩⟩ := maxBranched_cc_facts hregN hBo hv₁B
  have hv₁O := mem_connectedComponentIn (F := q ⁻¹' B) hv₁B
  have hu₁C : Ψ₁ u₁ ∈ connectedComponentIn (SpreadEnd.base ⁻¹' U') (Ψ₂ v₂) := by
    rw [← h]; exact R₁.mapsTo_cc hv₁O hu₁O
  have hu₁R' : (Ψ₁ u₁).base ∈ Reg G X M :=
    (hφreg' _ (R₁.mem u₁ hu₁O)).1 (by rw [R₁.base u₁ hu₁O]; exact hu₁R)
  obtain ⟨u₂, hu₂O, hu₂⟩ := himg₂ ⟨hu₁C, hu₁R'⟩
  have hbu : u₁.base = u₂.base := by
    rw [← R₁.base u₁ hu₁O, ← R₂.base u₂ hu₂O, hu₂]
  obtain ⟨δ, hδ, hδu⟩ := maxBranched_transitive hS₀N hregN yN u₁ u₂ hbu (show u₁.base ∈ (Sing G X N)ᶜ
    from fun hs => hs hu₁R)
  have hδO : δ '' connectedComponentIn (q ⁻¹' B) v₁ = connectedComponentIn (q ⁻¹' B) v₂ := by
    rw [connectedComponentIn_eq hu₁O, deck_image_connectedComponentIn q hδ (show q u₁ ∈ B from
      mem_of_mem_connectedComponentIn_preimage hu₁O), hδu, ← connectedComponentIn_eq hu₂O]
  have hδv₁ : δ v₁ = v₂ := by
    have hmem : δ v₁ ∈ connectedComponentIn (q ⁻¹' B) v₂ := hδO ▸ mem_image_of_mem δ hv₁O
    refine hN₂fib _ (hB₀N₂ ((connectedComponentIn_mono _ (preimage_mono inter_subset_left)) hmem)) ?_
    rw [deck_apply q hδ]; exact hb₁₂
  have hδV : MapsTo δ (connectedComponentIn (q ⁻¹' V) f₁) (connectedComponentIn (q ⁻¹' V) f₂) := by
    intro w hw
    have h1 : δ '' connectedComponentIn (q ⁻¹' V) v₁ = connectedComponentIn (q ⁻¹' V) (δ v₁) :=
      deck_image_connectedComponentIn q hδ (mem_of_mem_connectedComponentIn_preimage hv₁)
    rw [hδv₁, ← connectedComponentIn_eq hv₂, ← connectedComponentIn_eq hv₁] at h1
    rw [← h1]; exact mem_image_of_mem δ hw
  refine ⟨δ, hδ, hδv₁, hδV, ?_⟩
  obtain ⟨hZo, hZ'o, hZ'c, hcl, -⟩ := maxBranched_cc_facts hregN hV h₁.base_mem
  have hO₁V : connectedComponentIn (q ⁻¹' B) v₁ ⊆ connectedComponentIn (q ⁻¹' V) f₁ := by
    rw [connectedComponentIn_eq hv₁]
    exact connectedComponentIn_mono _ (preimage_mono inter_subset_right)
  refine eqOn_maxBranched_of_base_eq hregM hZo inter_subset_left hZ'o hZ'c hcl
    (h₂.contOn.comp δ.continuous.continuousOn hδV) h₁.contOn (fun w hw => ?_) (fun w hw => ?_)
    ⟨hO₁V hu₁O, hu₁R⟩ (by show Ψ₂ (δ u₁) = Ψ₁ u₁; rw [hδu, hu₂])
  · refine hφinj (h₂.mem _ (hδV hw)) (h₁.mem _ hw) ?_
    rw [h₂.base _ (hδV hw), h₁.base _ hw]; exact deck_apply q hδ w
  · refine (hφreg _ (h₂.mem _ (hδV hw.1))).1 ?_
    rw [h₂.base _ (hδV hw.1)]
    show q (δ w) ∈ Reg G X N
    rw [deck_apply q hδ]; exact hw.2

end Descent

section DescTopHelpers

/-- A preconnected `W`, covered by open subsets `p ⊆ W` each of which meets `R` in a preconnected
set, and such that two of them which meet do so at a point of `R`, has `W ∩ R` preconnected
(explicit topology). -/
theorem isPreconnected_inter_of_cover_of {α : Type*} (t : TopologicalSpace α) {W R : Set α}
    (hWc : @IsPreconnected α t W) (P : Set (Set α)) (hPo : ∀ p ∈ P, IsOpen[t] p)
    (hcov : W ⊆ ⋃₀ P) (hPW : ∀ p ∈ P, p ⊆ W) (hPR : ∀ p ∈ P, @IsPreconnected α t (p ∩ R))
    (hmeet : ∀ p ∈ P, ∀ p' ∈ P, (p ∩ p').Nonempty → (p ∩ p' ∩ R).Nonempty) :
    @IsPreconnected α t (W ∩ R) := by
  letI := t
  intro u v hu hv hsub ⟨a, haWR, hau⟩ ⟨b, hbWR, hbv⟩
  by_contra hne
  have hne' : ∀ x ∈ W ∩ R, x ∈ u → x ∈ v → False := fun x hx hxu hxv =>
    hne ⟨x, hx, hxu, hxv⟩
  -- each `p ∩ R` lies in `u` or in `v`
  have hside : ∀ p ∈ P, ∀ x ∈ p ∩ R, x ∈ u → ∀ y ∈ p ∩ R, y ∈ v → False := by
    intro p hp x hx hxu y hy hyv
    obtain ⟨z, hz, hzu, hzv⟩ := hPR p hp u v hu hv
      (fun w hw => hsub ⟨hPW p hp hw.1, hw.2⟩) ⟨x, hx, hxu⟩ ⟨y, hy, hyv⟩
    exact hne' z ⟨hPW p hp hz.1, hz.2⟩ hzu hzv
  set 𝒰 := ⋃₀ {p ∈ P | ∃ x ∈ p ∩ R, x ∈ u}
  set 𝒱 := ⋃₀ {p ∈ P | ∃ x ∈ p ∩ R, x ∈ v}
  have h𝒰 : IsOpen 𝒰 := isOpen_sUnion fun p hp => hPo p hp.1
  have h𝒱 : IsOpen 𝒱 := isOpen_sUnion fun p hp => hPo p hp.1
  have hcov' : W ⊆ 𝒰 ∪ 𝒱 := by
    intro w hw
    obtain ⟨p, hp, hwp⟩ := hcov hw
    obtain ⟨x, ⟨hxp, -⟩, hxR⟩ := hmeet p hp p hp ⟨w, hwp, hwp⟩
    rcases hsub ⟨hPW p hp hxp, hxR⟩ with hxu | hxv
    · exact Or.inl ⟨p, ⟨hp, x, ⟨hxp, hxR⟩, hxu⟩, hwp⟩
    · exact Or.inr ⟨p, ⟨hp, x, ⟨hxp, hxR⟩, hxv⟩, hwp⟩
  have ha : (W ∩ 𝒰).Nonempty := by
    obtain ⟨p, hp, hap⟩ := hcov haWR.1
    exact ⟨a, haWR.1, p, ⟨hp, a, ⟨hap, haWR.2⟩, hau⟩, hap⟩
  have hb : (W ∩ 𝒱).Nonempty := by
    obtain ⟨p, hp, hbp⟩ := hcov hbWR.1
    exact ⟨b, hbWR.1, p, ⟨hp, b, ⟨hbp, hbWR.2⟩, hbv⟩, hbp⟩
  obtain ⟨w, -, ⟨p, ⟨hp, x, hx, hxu⟩, hwp⟩, ⟨p', ⟨hp', y, hy, hyv⟩, hwp'⟩⟩ :=
    hWc 𝒰 𝒱 h𝒰 h𝒱 hcov' ha hb
  obtain ⟨r, ⟨hrp, hrp'⟩, hrR⟩ := hmeet p hp p' hp' ⟨w, hwp, hwp'⟩
  rcases hsub ⟨hPW p hp hrp, hrR⟩ with hru | hrv
  · exact hside p' hp' r ⟨hrp', hrR⟩ hru y hy hyv
  · exact hside p hp x hx hxu r ⟨hrp, hrR⟩ hrv

/-- In a locally path-connected (explicit) topology, an open set contains an open preconnected
neighbourhood of each of its points. -/
theorem exists_isOpen_isPreconnected_of {α : Type*} (t : TopologicalSpace α)
    (hl : @LocPathConnectedSpace α t) {F : Set α} {x : α} (hF : IsOpen[t] F) (hx : x ∈ F) :
    ∃ K, IsOpen[t] K ∧ x ∈ K ∧ K ⊆ F ∧ @IsPreconnected α t K := by
  letI := t
  haveI := hl
  exact ⟨connectedComponentIn F x, hF.connectedComponentIn, mem_connectedComponentIn hx,
    connectedComponentIn_subset _ _, isPreconnected_connectedComponentIn⟩

/-- Two maps continuous for an explicit topology, agreeing on `s`, agree on `closure s`. -/
theorem eqOn_of_subset_closure_of {α β : Type*} [TopologicalSpace β] [T2Space β]
    (t : TopologicalSpace α) {f g : α → β} (hf : Continuous[t, _] f) (hg : Continuous[t, _] g)
    {s u : Set α} (h : EqOn f g s) (hus : u ⊆ @closure α t s) : EqOn f g u := fun x hx => by
  letI := t
  exact ((isClosed_eq hf hg).closure_subset_iff.2 h) (hus hx)

end DescTopHelpers

section DescTop

variable {G : Type*} {X : Type*} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
  {M : Type v} [TopologicalSpace M] [T2Space M] [LocPathConnectedSpace M]
  [FirstCountableTopology M] [ConnectedSpace M] [SingularGXStructure G X M]
  {N : Type u} [TopologicalSpace N] [T2Space N] [LocPathConnectedSpace N]
  [FirstCountableTopology N] [ConnectedSpace N] [SingularGXStructure G X N]
  {y₀ : ((Sing G X M)ᶜ : Set M)} {yN : ((Sing G X N)ᶜ : Set N)}

/-- The neighbourhoods of `T_{U,V,φ}` read through chosen descents: at a point `y` over `U`, the
image by the descent `Ψz y` of the `T_N`-neighbourhoods of `fz y` (`Ψz y (fz y) = y`); the
natural ones off `p⁻¹(U)`. This is the quotient (`RamcovGX.tex:2096`, "consider the quotient
topology on `Û`") of `T_N` on `V̂` by the descent `V̂ → Û`. -/
def descNhds (U : Set M)
    (fz : MaxBranchedCover (Sing G X M) y₀ → MaxBranchedCover (Sing G X N) yN)
    (Ψz : MaxBranchedCover (Sing G X M) y₀ → MaxBranchedCover (Sing G X N) yN →
      MaxBranchedCover (Sing G X M) y₀)
    (TN : WrappedTop (MaxBranchedCover (Sing G X N) yN))
    (y : MaxBranchedCover (Sing G X M) y₀) : Filter (MaxBranchedCover (Sing G X M) y₀) :=
  if y.base ∈ U then Filter.map (Ψz y) (@nhds _ TN.top (fz y)) else 𝓝 y

/-- The topology `T_{U,V,φ}` (`RamcovGX.tex:2093–2098`) when `V̂ → V` dominates `Û → U` (in
particular when `r : Ṽ → V̂` is an isomorphism, `ℓ` arbitrary): on each component `Û` of
`p⁻¹(U)`, the quotient of `T_N` by a descent `V̂ → Û` of `φ⁻¹`; natural off `p⁻¹(U)`. -/
@[reducible] def descTop (U : Set M)
    (fz : MaxBranchedCover (Sing G X M) y₀ → MaxBranchedCover (Sing G X N) yN)
    (Ψz : MaxBranchedCover (Sing G X M) y₀ → MaxBranchedCover (Sing G X N) yN →
      MaxBranchedCover (Sing G X M) y₀)
    (TN : WrappedTop (MaxBranchedCover (Sing G X N) yN)) :
    TopologicalSpace (MaxBranchedCover (Sing G X M) y₀) :=
  TopologicalSpace.mkOfNhds (descNhds U fz Ψz TN)

/-- An element of `Γ(\widetilde N/N)` maps `T_N`-neighbourhoods onto `T_N`-neighbourhoods. -/
theorem map_deck_nhds_of_isTamifying {TN : WrappedTop (MaxBranchedCover (Sing G X N) yN)}
    (hTN : IsTamifyingTopology G X N yN TN.top)
    {δ : MaxBranchedCover (Sing G X N) yN ≃ₜ MaxBranchedCover (Sing G X N) yN}
    (hδ : δ ∈ deckGroup (SpreadEnd.base : MaxBranchedCover (Sing G X N) yN → N))
    (v : MaxBranchedCover (Sing G X N) yN) :
    Filter.map δ (@nhds _ TN.top v) = @nhds _ TN.top (δ v) := by
  rw [← comap_deck_nhds_of_isTamifying hTN hδ v, Filter.map_comap_of_surjective δ.surjective]

variable {U : Set M} {V : Set N} {φ' : M → N}
  {fz : MaxBranchedCover (Sing G X M) y₀ → MaxBranchedCover (Sing G X N) yN}
  {Ψz : MaxBranchedCover (Sing G X M) y₀ → MaxBranchedCover (Sing G X N) yN →
      MaxBranchedCover (Sing G X M) y₀}
  {TN : WrappedTop (MaxBranchedCover (Sing G X N) yN)}

/-- A component of `q⁻¹(V)` is a `T_N`-neighbourhood of its points. -/
theorem cc_mem_nhds_of_isTamifying (hregN : SemilocallySimplyConnected ((Sing G X N)ᶜ : Set N))
    (hV : IsOpen V) (hTN : IsTamifyingTopology G X N yN TN.top)
    {f w : MaxBranchedCover (Sing G X N) yN}
    (hw : w ∈ connectedComponentIn (SpreadEnd.base ⁻¹' V) f) :
    connectedComponentIn (SpreadEnd.base ⁻¹' V) f ∈ @nhds _ TN.top w := by
  obtain ⟨-, hβN, -, -, hβlN, -⟩ := maxBranched_basic (isSkeletal_sing G X N) hregN yN
  haveI := hβlN
  exact nhds_mono hTN.le_natural
    (((hV.preimage hβN.isSpread.continuous).connectedComponentIn).mem_nhds hw)

variable (hregM : SemilocallySimplyConnected ((Sing G X M)ᶜ : Set M))
  (hregN : SemilocallySimplyConnected ((Sing G X N)ᶜ : Set N))
  (hU : IsOpen U) (hV : IsOpen V)
  (hφc : ContinuousOn φ' U) (hφinj : InjOn φ' U) (hφV : MapsTo φ' U V)
  (hφreg : ∀ m ∈ U, φ' m ∈ Reg G X N ↔ m ∈ Reg G X M)
  (hdisc : ∀ x : N, DiscreteTopology
      ((SpreadEnd.base : MaxBranchedCover (Sing G X N) yN → N) ⁻¹' {x}))
  (hF : ∀ z : MaxBranchedCover (Sing G X M) y₀, z.base ∈ U →
      IsChartDescent U V φ' (fz z) (Ψz z) ∧ Ψz z (fz z) = z)
  (hTN : IsTamifyingTopology G X N yN TN.top)
include hregM hregN hU hV hφc hφinj hφV hφreg hdisc hF hTN

/-- `T_{U,V,φ}` does not depend on the descents: at `Ψ' v`, for ANY descent `Ψ'` and any `v` in
its domain, its neighbourhoods are the images by `Ψ'` of the `T_N`-neighbourhoods of `v`
(two descents differ by an element of `Γ(\widetilde N/N)`, `T_N`-continuous by (C),
`IsChartDescent.exists_deck`). -/
theorem descNhds_eq {f' : MaxBranchedCover (Sing G X N) yN}
    {Ψ' : MaxBranchedCover (Sing G X N) yN → MaxBranchedCover (Sing G X M) y₀}
    (h' : IsChartDescent U V φ' f' Ψ') {v : MaxBranchedCover (Sing G X N) yN}
    (hv : v ∈ connectedComponentIn (SpreadEnd.base ⁻¹' V) f') :
    descNhds U fz Ψz TN (Ψ' v) = Filter.map Ψ' (@nhds _ TN.top v) := by
  have hyU : (Ψ' v).base ∈ U := h'.mem v hv
  obtain ⟨hFy, hFy'⟩ := hF (Ψ' v) hyU
  have hfy := mem_connectedComponentIn (F := SpreadEnd.base ⁻¹' V) hFy.base_mem
  obtain ⟨δ, hδ, hδv, -, hEq⟩ := hFy.exists_deck hregM hregN hU hV hφc hφinj hφV hφreg hdisc h'
    hfy hv hFy'
  rw [descNhds, if_pos hyU]
  calc Filter.map (Ψz (Ψ' v)) (@nhds _ TN.top (fz (Ψ' v)))
      = Filter.map (fun w => Ψ' (δ w)) (@nhds _ TN.top (fz (Ψ' v))) :=
        Filter.map_congr (Filter.mem_of_superset (cc_mem_nhds_of_isTamifying hregN hV hTN hfy)
          fun w hw => (hEq hw).symm)
    _ = Filter.map Ψ' (Filter.map δ (@nhds _ TN.top (fz (Ψ' v)))) := by rw [Filter.map_map]; rfl
    _ = Filter.map Ψ' (@nhds _ TN.top v) := by rw [map_deck_nhds_of_isTamifying hTN hδ, hδv]

theorem descNhds_le (y : MaxBranchedCover (Sing G X M) y₀) : descNhds U fz Ψz TN y ≤ 𝓝 y := by
  unfold descNhds
  split_ifs with hy
  · obtain ⟨hFy, hFy'⟩ := hF y hy
    have hfy := mem_connectedComponentIn (F := SpreadEnd.base ⁻¹' V) hFy.base_mem
    obtain ⟨-, hβN, -, -, hβlN, -⟩ := maxBranched_basic (isSkeletal_sing G X N) hregN yN
    haveI := hβlN
    have hc := (hFy.contOn.continuousAt
      (((hV.preimage hβN.isSpread.continuous).connectedComponentIn).mem_nhds hfy)).tendsto
    rw [hFy'] at hc
    exact (Filter.map_mono (nhds_mono hTN.le_natural)).trans hc
  · exact le_rfl

theorem nhds_descTop (y : MaxBranchedCover (Sing G X M) y₀) :
    @nhds _ (descTop U fz Ψz TN) y = descNhds U fz Ψz TN y := by
  refine nhds_mkOfNhds _ _ (fun z => ?_) (fun z s hs => ?_)
  · unfold descNhds
    split_ifs with hz
    · intro s hs
      have := mem_of_mem_nhds_of TN.top hs
      rw [mem_preimage, (hF z hz).2] at this
      exact this
    · exact pure_le_nhds z
  · by_cases hz : z.base ∈ U
    · obtain ⟨hFz, -⟩ := hF z hz
      have hs' := hs
      rw [descNhds, if_pos hz] at hs'
      have hfz := mem_connectedComponentIn (F := SpreadEnd.base ⁻¹' V) hFz.base_mem
      rw [descNhds, if_pos hz, Filter.eventually_map]
      filter_upwards [(eventually_mem_nhds_iff_of TN.top).2 hs',
        cc_mem_nhds_of_isTamifying hregN hV hTN hfz] with w hw1 hw2
      rw [descNhds_eq hregM hregN hU hV hφc hφinj hφV hφreg hdisc hF hTN hFz hw2]
      exact hw1
    · rw [descNhds, if_neg hz] at hs ⊢
      filter_upwards [eventually_mem_nhds_iff.2 hs] with w hw
      exact descNhds_le hregM hregN hU hV hφc hφinj hφV hφreg hdisc hF hTN w hw

theorem descTop_le : descTop U fz Ψz TN ≤ weakTopMax G X M y₀ := (le_iff_nhds _ _).2 fun y => by
  rw [nhds_descTop hregM hregN hU hV hφc hφinj hφV hφreg hdisc hF hTN]
  exact descNhds_le hregM hregN hU hV hφc hφinj hφV hφreg hdisc hF hTN y

/-- Every descent is continuous from `T_N` to `T_{U,V,φ}` on its domain, with equality of the
neighbourhood filters (a quotient map). -/
theorem nhds_descTop_eq_map {f' : MaxBranchedCover (Sing G X N) yN}
    {Ψ' : MaxBranchedCover (Sing G X N) yN → MaxBranchedCover (Sing G X M) y₀}
    (h' : IsChartDescent U V φ' f' Ψ') {v : MaxBranchedCover (Sing G X N) yN}
    (hv : v ∈ connectedComponentIn (SpreadEnd.base ⁻¹' V) f') :
    @nhds _ (descTop U fz Ψz TN) (Ψ' v) = Filter.map Ψ' (@nhds _ TN.top v) := by
  rw [nhds_descTop hregM hregN hU hV hφc hφinj hφV hφreg hdisc hF hTN,
    descNhds_eq hregM hregN hU hV hφc hφinj hφV hφreg hdisc hF hTN h' hv]

theorem continuousOn_descTop {f' : MaxBranchedCover (Sing G X N) yN}
    {Ψ' : MaxBranchedCover (Sing G X N) yN → MaxBranchedCover (Sing G X M) y₀}
    (h' : IsChartDescent U V φ' f' Ψ') :
    @ContinuousOn _ _ TN.top (descTop U fz Ψz TN) Ψ'
      (connectedComponentIn (SpreadEnd.base ⁻¹' V) f') := fun v hv => by
  show Tendsto Ψ' (@nhdsWithin _ TN.top v _) (@nhds _ (descTop U fz Ψz TN) (Ψ' v))
  rw [nhds_descTop_eq_map hregM hregN hU hV hφc hφinj hφV hφreg hdisc hF hTN h' hv]
  exact tendsto_map.mono_left (Filter.map_mono (nhdsWithin_le_nhds_of TN.top))

/-- A descent is surjective onto the component of `p⁻¹(U)` it lands in. -/
theorem IsChartDescent.surjOn_cc {f : MaxBranchedCover (Sing G X N) yN}
    {Ψ : MaxBranchedCover (Sing G X N) yN → MaxBranchedCover (Sing G X M) y₀}
    (hΨ : IsChartDescent U V φ' f Ψ) :
    SurjOn Ψ (connectedComponentIn (SpreadEnd.base ⁻¹' V) f)
      (connectedComponentIn (SpreadEnd.base ⁻¹' U) (Ψ f)) := by
  intro y hy
  have hyU : y.base ∈ U := mem_of_mem_connectedComponentIn_preimage hy
  obtain ⟨hFy, hFy'⟩ := hF y hyU
  have hfy := mem_connectedComponentIn (F := SpreadEnd.base ⁻¹' V) hFy.base_mem
  obtain ⟨-, -, -, -, ⟨u, huV, huR⟩⟩ := maxBranched_cc_facts hregN hV hFy.base_mem
  have huC : Ψz y u ∈ connectedComponentIn (SpreadEnd.base ⁻¹' U) (Ψ f) := by
    have := hFy.mapsTo_cc hfy huV
    rwa [hFy', ← connectedComponentIn_eq hy] at this
  have huR' : (Ψz y u).base ∈ Reg G X M :=
    (hφreg _ (hFy.mem u huV)).1 (by rw [hFy.base u huV]; exact huR)
  obtain ⟨u₂, hu₂V, hu₂⟩ := hΨ.reg_subset_image hregM hregN hU hV hφc hφinj hφV hφreg ⟨huC, huR'⟩
  obtain ⟨δ, -, -, hδV, hEq⟩ := hFy.exists_deck hregM hregN hU hV hφc hφinj hφV hφreg hdisc hΨ huV
    hu₂V hu₂.symm
  exact ⟨δ (fz y), hδV hfy, (hEq hfy).trans hFy'⟩

/-- The topology `T_{U,V,φ}` built from descents is a local tamifying topology over `U`
(`RamcovGX.tex:2093–2140`, the case where `V̂ → V` dominates `Û → U`, `ℓ` arbitrary): first
countable and locally path-connected (images of those of `T_N`), natural over `reg U` (a descent
is open at regular points, `reg_subset_image`), (A) through (A) for `T_N`, (B) by descending
`g • D_N` (`D_N ∘ δ = D_N` for the deck transformations `δ` relating two points of a fibre of the
descent, by density of the regular part, `RamcovGX.tex:2117–2128`), (C) (a deck transformation
composed with a descent is a descent) and (D) (`RamcovGX.tex:2128–2133`: the image of the portly
`reg(V̂)` by the open surjective descent, `isPreconnected_inter_of_cover_of`). -/
theorem isLocalTamifying_descTop
    (hlift' : ∀ (z : MaxBranchedCover (Sing G X M) y₀) (f : MaxBranchedCover (Sing G X N) yN),
      z.base ∈ U → f.base = φ' z.base →
        ∃ Ψ, IsChartDescent U V φ' f Ψ ∧ Ψ f = z)
    {D₀ : MaxBranchedCover (Sing G X M) y₀ → X} {Dₙ : MaxBranchedCover (Sing G X N) yN → X}
    (hDₙ : Continuous[TN.top, _] Dₙ)
    (hstr : ∀ z : MaxBranchedCover (Sing G X M) y₀, z.base ∈ U → ∃ g : G,
      ∀ w ∈ connectedComponentIn (SpreadEnd.base ⁻¹' V) (fz z) ∩ SpreadEnd.base ⁻¹' Reg G X N,
        D₀ (Ψz z w) = g • Dₙ w) :
    IsLocalTamifying G X M y₀ D₀ U (descTop U fz Ψz TN) := by
  have hS₀M := isSkeletal_sing G X M
  obtain ⟨-, hβM, -, -, hβlM, -⟩ := maxBranched_basic hS₀M hregM y₀
  have hS₀N := isSkeletal_sing G X N
  obtain ⟨-, hβN, -, -, hβlN, -⟩ := maxBranched_basic hS₀N hregN yN
  haveI := hβlM
  haveI := hβlN
  have hnhds := nhds_descTop hregM hregN hU hV hφc hφinj hφV hφreg hdisc hF hTN
  have hmap := fun {f'} {Ψ'} (h' : IsChartDescent U V φ' f' Ψ') {v} hv =>
    nhds_descTop_eq_map (fz := fz) (Ψz := Ψz) hregM hregN hU hV hφc hφinj hφV hφreg hdisc hF hTN
      (f' := f') (Ψ' := Ψ') h' (v := v) hv
  have hle := descTop_le hregM hregN hU hV hφc hφinj hφV hφreg hdisc hF hTN
  have hTopen : ∀ s, IsOpen s → IsOpen[descTop U fz Ψz TN] s := fun s hs =>
    TopologicalSpace.le_def.1 hle s hs
  have hVn := fun {f w : MaxBranchedCover (Sing G X N) yN}
    (hw : w ∈ connectedComponentIn (SpreadEnd.base ⁻¹' V) f) =>
    cc_mem_nhds_of_isTamifying hregN hV hTN hw
  have hZo : ∀ z : MaxBranchedCover (Sing G X M) y₀, z.base ∈ U →
      IsOpen (connectedComponentIn (SpreadEnd.base ⁻¹' U) z) := fun z hz =>
    (maxBranched_cc_facts hregM hU hz).1
  -- density of the regular part, in `T_{U,V,φ}`
  have hdense : ∀ y : MaxBranchedCover (Sing G X M) y₀, y.base ∈ U →
      ∀ t ∈ @nhds _ (descTop U fz Ψz TN) y,
        (t ∩ (SpreadEnd.base ⁻¹' Reg G X M ∩ SpreadEnd.base ⁻¹' U)).Nonempty := by
    intro y hy t ht
    obtain ⟨hFy, hFy'⟩ := hF y hy
    have hfy := mem_connectedComponentIn (F := SpreadEnd.base ⁻¹' V) hFy.base_mem
    rw [hnhds, descNhds, if_pos hy] at ht
    have hd := mem_closure_of_dense_of TN.top (@IsPortly.dense _ TN.top _ hTN.isPortly) (fz y)
    rw [mem_closure_iff_nhds_of TN.top] at hd
    obtain ⟨v, ⟨hvt, hvV⟩, hvR⟩ := hd _ (Filter.inter_mem ht (hVn hfy))
    exact ⟨Ψz y v, hvt, (hφreg _ (hFy.mem v hvV)).1 (by rw [hFy.base v hvV]; exact hvR),
      hFy.mem v hvV⟩
  refine ⟨hle, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- first countable
    intro e he
    rw [hnhds, descNhds, if_pos he]
    haveI := @FirstCountableTopology.nhds_generated_countable _ TN.top hTN.firstCountable (fz e)
    infer_instance
  · -- locally path-connected
    intro e he
    refine Filter.hasBasis_self.2 fun t ht => ?_
    obtain ⟨hFe, hFe'⟩ := hF e he
    have hfe := mem_connectedComponentIn (F := SpreadEnd.base ⁻¹' V) hFe.base_mem
    have ht' := ht
    rw [hnhds, descNhds, if_pos he] at ht'
    obtain ⟨P, ⟨hPn, hPc⟩, hPsub⟩ :=
      (@path_connected_basis _ TN.top hTN.locPathConnected (fz e)).mem_iff.1
        (Filter.inter_mem ht' (hVn hfe))
    refine ⟨Ψz e '' P, ?_, isPathConnected_image_of TN.top (descTop U fz Ψz TN) hPc
      (continuousOn_mono_of TN.top (descTop U fz Ψz TN)
        (continuousOn_descTop hregM hregN hU hV hφc hφinj hφV hφreg hdisc hF hTN hFe)
        fun v hv => (hPsub hv).2), ?_⟩
    · rw [hnhds, descNhds, if_pos he]
      exact Filter.image_mem_map hPn
    · rintro _ ⟨v, hv, rfl⟩
      exact (hPsub hv).1
  · -- natural over `reg`
    intro e he hreg
    obtain ⟨hFe, hFe'⟩ := hF e he
    have hfe := mem_connectedComponentIn (F := SpreadEnd.base ⁻¹' V) hFe.base_mem
    rw [hnhds]
    refine le_antisymm (descNhds_le hregM hregN hU hV hφc hφinj hφV hφreg hdisc hF hTN e) ?_
    have hfR : (fz e).base ∈ Reg G X N := by
      rw [← hFe.base _ hfe, hFe']; exact (hφreg _ he).2 hreg
    rw [descNhds, if_pos he, IsTamifyingTopology.nhds_eq_of_reg hregN hTN hfR]
    intro s hs
    obtain ⟨O, hOs, hOo, hfO⟩ := mem_nhds_iff.1 (show Ψz e ⁻¹' s ∈ 𝓝 (fz e) from hs)
    obtain ⟨B₀, hB₀, hfB₀, hB₀O⟩ := (isSpread_iff.1 hβN.isSpread).2.2 (fz e) O hOo hfO
    have hBo : IsOpen (B₀ ∩ V) := hB₀.inter hV
    have hfB : (fz e).base ∈ B₀ ∩ V := ⟨hfB₀, hFe.base_mem⟩
    have hU'o : IsOpen (U ∩ φ' ⁻¹' (B₀ ∩ V)) := hφc.isOpen_inter_preimage hU hBo
    have R := hFe.restrict inter_subset_right hfe hfB (U' := U ∩ φ' ⁻¹' (B₀ ∩ V))
      fun m hm hmB => ⟨hm, hmB⟩
    have himg := R.reg_subset_image hregM hregN hU'o hBo (hφc.mono inter_subset_left)
      (hφinj.mono inter_subset_left) (fun m hm => hm.2) (fun m hm => hφreg m hm.1)
    rw [hFe'] at himg
    have heU' : e.base ∈ U ∩ φ' ⁻¹' (B₀ ∩ V) := ⟨he, by
      show φ' e.base ∈ B₀ ∩ V
      rw [← hFe', hFe.base _ hfe]; exact hfB⟩
    obtain ⟨-, hCRo, -, -, -⟩ := maxBranched_cc_facts hregM hU'o heU'
    refine Filter.mem_of_superset (hCRo.mem_nhds ⟨mem_connectedComponentIn heU', hreg⟩)
      fun y hy => ?_
    obtain ⟨w, hw, rfl⟩ := himg hy
    exact hOs (hB₀O ((connectedComponentIn_mono _ (preimage_mono inter_subset_left)) hw))
  · -- (A)
    intro O hO
    set Y : Set N := φ' '' (O ∩ U) with hYdef
    have hYq : IsOpen[TN.top] ((SpreadEnd.base : MaxBranchedCover (Sing G X N) yN → N) ⁻¹' Y) := by
      refine (isOpen_iff_mem_nhds_of TN.top).2 fun v hv => ?_
      obtain ⟨u, ⟨huO, huU⟩, hvu⟩ := hv
      obtain ⟨z, hz⟩ := hβM.surjective u
      have hzU : z.base ∈ U := hz ▸ huU
      obtain ⟨Ψ, hΨ, hΨv⟩ := hlift' z v hzU (by rw [hz]; exact hvu.symm)
      have hvV := mem_connectedComponentIn (F := SpreadEnd.base ⁻¹' V) hΨ.base_mem
      have hA : (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) ⁻¹' O ∩
          SpreadEnd.base ⁻¹' U ∈ @nhds _ (descTop U fz Ψz TN) z :=
        @IsOpen.mem_nhds _ (descTop U fz Ψz TN) _ _ hO ⟨show z.base ∈ O from hz ▸ huO, hzU⟩
      rw [← hΨv, hmap hΨ hvV] at hA
      refine Filter.mem_of_superset (Filter.inter_mem hA (hVn hvV)) fun w ⟨hwA, hwV⟩ => ?_
      exact ⟨(Ψ w).base, hwA, hΨ.base w hwV⟩
    have hY : IsOpen Y := by
      have h : IsOpen[TopologicalSpace.coinduced SpreadEnd.base TN.top] Y := isOpen_coinduced.2 hYq
      rwa [hTN.coinduced_eq] at h
    have hOU : O ∩ U = U ∩ φ' ⁻¹' Y := by
      ext m
      constructor
      · rintro ⟨hmO, hmU⟩; exact ⟨hmU, m, ⟨hmO, hmU⟩, rfl⟩
      · rintro ⟨hmU, m', hm', heq⟩
        exact ⟨hφinj hm'.2 hmU heq ▸ hm'.1, hmU⟩
    rw [hOU]; exact hφc.isOpen_inter_preimage hU hY
  · -- (B)
    intro e he
    obtain ⟨hFe, hFe'⟩ := hF e he
    obtain ⟨g, hg⟩ := hstr e he
    set Ψ := Ψz e
    set f := fz e
    set Vh := connectedComponentIn ((SpreadEnd.base : MaxBranchedCover (Sing G X N) yN → N) ⁻¹' V) f
    have hfe : f ∈ Vh := mem_connectedComponentIn hFe.base_mem
    have hsurj := hFe.surjOn_cc hregM hregN hU hV hφc hφinj hφV hφreg hdisc hF hTN
    rw [hFe'] at hsurj
    -- `D_N` is constant on the fibres of the descent
    have hinv : ∀ w ∈ Vh, ∀ w' ∈ Vh, Ψ w = Ψ w' → Dₙ w = Dₙ w' := by
      intro w hw w' hw' hww'
      obtain ⟨δ, hδ, hδw, hδV, hEq⟩ := hFe.exists_deck hregM hregN hU hV hφc hφinj hφV hφreg hdisc
        hFe hw hw' hww'
      have hR : EqOn (fun u => Dₙ (δ u)) Dₙ (Vh ∩ SpreadEnd.base ⁻¹' Reg G X N) := by
        intro u hu
        have hδu : δ u ∈ Vh ∩ SpreadEnd.base ⁻¹' Reg G X N := ⟨hδV hu.1, by
          show (δ u).base ∈ Reg G X N
          rw [show (δ u).base = u.base from deck_apply _ hδ u]; exact hu.2⟩
        have h1 := hg _ hδu
        have h2 := hg u hu
        have h3 : Ψ (δ u) = Ψ u := hEq hu.1
        rw [h3, h2] at h1
        exact (smul_left_cancel g h1).symm
      have hcl : Vh ⊆ @closure _ TN.top (Vh ∩ SpreadEnd.base ⁻¹' Reg G X N) := by
        intro x hx
        rw [mem_closure_iff_nhds_of TN.top]
        intro t ht
        have hd := mem_closure_of_dense_of TN.top (@IsPortly.dense _ TN.top _ hTN.isPortly) x
        rw [mem_closure_iff_nhds_of TN.top] at hd
        obtain ⟨r, ⟨hrt, hrV⟩, hrR⟩ := hd _ (Filter.inter_mem ht (hVn hx))
        exact ⟨r, hrt, hrV, hrR⟩
      have := eqOn_of_subset_closure_of TN.top
        (continuous_comp_of TN.top TN.top _ hDₙ (continuous_deck_of_isTamifying hTN hδ)) hDₙ hR
        hcl hw
      simp only at this
      rw [← hδw, this]
    let σ : MaxBranchedCover (Sing G X M) y₀ → MaxBranchedCover (Sing G X N) yN := fun y =>
      if h : ∃ w ∈ Vh, Ψ w = y then h.choose else f
    have hσ : ∀ y ∈ connectedComponentIn (SpreadEnd.base ⁻¹' U) e, σ y ∈ Vh ∧ Ψ (σ y) = y := by
      intro y hy
      have h : ∃ w ∈ Vh, Ψ w = y := hsurj hy
      have : σ y = h.choose := dif_pos h
      rw [this]; exact h.choose_spec
    have hDΨ : ∀ w ∈ Vh, g • Dₙ (σ (Ψ w)) = g • Dₙ w := by
      intro w hw
      have hΨw : Ψ w ∈ connectedComponentIn (SpreadEnd.base ⁻¹' U) e := by
        have := hFe.mapsTo_cc hfe hw; rwa [hFe'] at this
      rw [hinv _ (hσ _ hΨw).1 w hw (hσ _ hΨw).2]
    refine ⟨connectedComponentIn (SpreadEnd.base ⁻¹' U) e, hTopen _ (hZo e he),
      mem_connectedComponentIn (F := SpreadEnd.base ⁻¹' U) he, fun y => g • Dₙ (σ y), ?_,
      fun y hy => ?_⟩
    · intro y hy
      obtain ⟨hσV, hσy⟩ := hσ y hy
      show Tendsto (fun y => g • Dₙ (σ y)) (@nhdsWithin _ (descTop U fz Ψz TN) y _) (𝓝 _)
      refine Tendsto.mono_left ?_ (nhdsWithin_le_nhds_of (descTop U fz Ψz TN))
      rw [← hσy, hmap hFe hσV, Filter.tendsto_map'_iff]
      have hc : Tendsto (fun w => g • Dₙ w) (@nhds _ TN.top (σ y)) (𝓝 (g • Dₙ (σ y))) :=
        ((@Continuous.tendsto _ _ TN.top _ Dₙ hDₙ (σ y))).const_smul g
      show Tendsto (fun w => g • Dₙ (σ (Ψ w))) (@nhds _ TN.top (σ y))
        (𝓝 (g • Dₙ (σ (Ψ (σ y)))))
      rw [hDΨ _ hσV]
      refine hc.congr' (Filter.mem_of_superset (hVn hσV) fun w hw => ?_)
      exact (hDΨ w hw).symm
    · obtain ⟨hσV, hσy⟩ := hσ y hy.1
      have hσR : (σ y).base ∈ Reg G X N := by
        rw [← hFe.base _ hσV, hσy]; exact (hφreg _ (mem_of_mem_connectedComponentIn_preimage hy.1)).2 hy.2
      have := hg (σ y) ⟨hσV, hσR⟩
      rw [hσy] at this
      exact this.symm
  · -- (C)
    rintro f ⟨γ, hγ, rfl⟩ e he
    obtain ⟨hFe, hFe'⟩ := hF e he
    have hfe := mem_connectedComponentIn (F := SpreadEnd.base ⁻¹' V) hFe.base_mem
    have hγΨ : IsChartDescent U V φ' (fz e) (fun w => γ (Ψz e w)) :=
      ⟨hFe.base_mem, γ.continuous.comp_continuousOn hFe.contOn, fun w hw => by
        show (γ (Ψz e w)).base ∈ U
        rw [show (γ (Ψz e w)).base = (Ψz e w).base from deck_apply _ hγ _]; exact hFe.mem w hw,
        fun w hw => by
        show φ' (γ (Ψz e w)).base = w.base
        rw [show (γ (Ψz e w)).base = (Ψz e w).base from deck_apply _ hγ _]; exact hFe.base w hw⟩
    show Tendsto γ (@nhds _ (descTop U fz Ψz TN) e) (@nhds _ (descTop U fz Ψz TN) (γ e))
    have hγe : γ e = (fun w => γ (Ψz e w)) (fz e) := by simp only [hFe']
    rw [hγe, hmap hγΨ hfe, hnhds, descNhds, if_pos he, Filter.tendsto_map'_iff]
    exact tendsto_map
  · -- (D)
    have hpre : (Subtype.val : (SpreadEnd.base ⁻¹' U : Set (MaxBranchedCover (Sing G X M) y₀)) →
        MaxBranchedCover (Sing G X M) y₀) ⁻¹' (SpreadEnd.base ⁻¹' Reg G X M) =
        Subtype.val ⁻¹' (SpreadEnd.base ⁻¹' Reg G X M ∩ SpreadEnd.base ⁻¹' U) := by
      ext z; exact ⟨fun h => ⟨h, z.2⟩, fun h => h.1⟩
    rw [hpre]
    have hOU : IsOpen[descTop U fz Ψz TN]
        ((SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) ⁻¹' U) :=
      hTopen _ (hU.preimage hβM.isSpread.continuous)
    refine (@isPortly_subtype_iff _ (descTop U fz Ψz TN) _ _ hOU inter_subset_right).2
      ⟨hTopen _ (((isOpen_reg G X M).preimage hβM.isSpread.continuous).inter
        (hU.preimage hβM.isSpread.continuous)), fun y hy => ?_, fun W hWo hWU hWc => ?_⟩
    · exact (mem_closure_iff_nhds_of (descTop U fz Ψz TN)).2 (hdense y hy)
    · rcases W.eq_empty_or_nonempty with rfl | ⟨w₀, hw₀⟩
      · rw [empty_inter]; exact isPreconnected_empty_of (descTop U fz Ψz TN)
      have hw₀U : w₀.base ∈ U := hWU hw₀
      have hWc' : IsPreconnected W := by
        have := isPreconnected_image_of (descTop U fz Ψz TN) (weakTopMax G X M y₀) hWc
          (continuousOn_of_continuous_of _ _ (continuous_id_of_le hle) W)
        rwa [image_id] at this
      have hWZ : W ⊆ connectedComponentIn (SpreadEnd.base ⁻¹' U) w₀ :=
        hWc'.subset_connectedComponentIn hw₀ hWU
      obtain ⟨hFw, hFw'⟩ := hF w₀ hw₀U
      set Ψ := Ψz w₀
      set Vh := connectedComponentIn
        ((SpreadEnd.base : MaxBranchedCover (Sing G X N) yN → N) ⁻¹' V) (fz w₀)
      have hsurj := hFw.surjOn_cc hregM hregN hU hV hφc hφinj hφV hφreg hdisc hF hTN
      rw [hFw'] at hsurj
      have hcont := continuousOn_descTop hregM hregN hU hV hφc hφinj hφV hφreg hdisc hF hTN hFw
      -- the open set `V̂ ∩ Ψ⁻¹ W`
      have hWo' : IsOpen[TN.top] (Vh ∩ Ψ ⁻¹' W) := by
        refine (isOpen_iff_mem_nhds_of TN.top).2 fun x hx => Filter.inter_mem (hVn hx.1) ?_
        have h1 := hmap hFw hx.1
        have h2 : W ∈ @nhds _ (descTop U fz Ψz TN) (Ψ x) :=
          @IsOpen.mem_nhds _ (descTop U fz Ψz TN) _ _ hWo hx.2
        rw [h1] at h2
        exact h2
      set P : Set (Set (MaxBranchedCover (Sing G X M) y₀)) :=
        {p | ∃ K, IsOpen[TN.top] K ∧ K ⊆ Vh ∩ Ψ ⁻¹' W ∧ @IsPreconnected _ TN.top K ∧ p = Ψ '' K}
      refine isPreconnected_inter_of_cover_of (descTop U fz Ψz TN) hWc P ?_ ?_ ?_ ?_ ?_
      · rintro _ ⟨K, hKo, hKs, -, rfl⟩
        refine (isOpen_iff_mem_nhds_of (descTop U fz Ψz TN)).2 ?_
        rintro _ ⟨k, hk, rfl⟩
        rw [hmap hFw (hKs hk).1]
        exact Filter.image_mem_map ((isOpen_iff_mem_nhds_of TN.top).1 hKo k hk)
      · intro y hy
        obtain ⟨w, hwV, rfl⟩ := hsurj (hWZ hy)
        obtain ⟨K, hKo, hwK, hKs, hKc⟩ :=
          exists_isOpen_isPreconnected_of TN.top hTN.locPathConnected hWo' ⟨hwV, hy⟩
        exact ⟨Ψ '' K, ⟨K, hKo, hKs, hKc, rfl⟩, mem_image_of_mem _ hwK⟩
      · rintro _ ⟨K, -, hKs, -, rfl⟩
        rintro _ ⟨k, hk, rfl⟩
        exact (hKs hk).2
      · rintro _ ⟨K, hKo, hKs, hKc, rfl⟩
        have heq : Ψ '' K ∩ (SpreadEnd.base ⁻¹' Reg G X M ∩ SpreadEnd.base ⁻¹' U) =
            Ψ '' (K ∩ SpreadEnd.base ⁻¹' Reg G X N) := by
          ext y
          constructor
          · rintro ⟨⟨k, hk, rfl⟩, hR, -⟩
            refine ⟨k, ⟨hk, ?_⟩, rfl⟩
            show k.base ∈ Reg G X N
            rw [← hFw.base k (hKs hk).1]; exact (hφreg _ (hFw.mem k (hKs hk).1)).2 hR
          · rintro ⟨k, ⟨hk, hR⟩, rfl⟩
            refine ⟨mem_image_of_mem _ hk, (hφreg _ (hFw.mem k (hKs hk).1)).1 ?_,
              hFw.mem k (hKs hk).1⟩
            rw [hFw.base k (hKs hk).1]; exact hR
        rw [heq]
        exact isPreconnected_image_of TN.top (descTop U fz Ψz TN)
          (isPreconnected_inter_of_isPortly_of TN.top hTN.isPortly hKo hKc)
          (continuousOn_mono_of TN.top (descTop U fz Ψz TN) hcont fun k hk => (hKs hk.1).1)
      · rintro p hp p' hp' ⟨y, hyp, hyp'⟩
        have hpo : ∀ p ∈ P, IsOpen[descTop U fz Ψz TN] p := by
          rintro _ ⟨K, hKo, hKs, -, rfl⟩
          refine (isOpen_iff_mem_nhds_of (descTop U fz Ψz TN)).2 ?_
          rintro _ ⟨k, hk, rfl⟩
          rw [hmap hFw (hKs hk).1]
          exact Filter.image_mem_map ((isOpen_iff_mem_nhds_of TN.top).1 hKo k hk)
        have hyU : y.base ∈ U := by
          obtain ⟨K, -, hKs, -, rfl⟩ := hp
          obtain ⟨k, hk, rfl⟩ := hyp
          exact hFw.mem k (hKs hk).1
        obtain ⟨r, hr, hrR⟩ := hdense y hyU (p ∩ p')
          (Filter.inter_mem ((isOpen_iff_mem_nhds_of _).1 (hpo p hp) y hyp)
            ((isOpen_iff_mem_nhds_of _).1 (hpo p' hp') y hyp'))
        exact ⟨r, hr, hrR⟩

end DescTop

section DescStructure

variable {G : Type*} {X : Type*} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
  {M : Type v} [TopologicalSpace M] [T2Space M] [LocPathConnectedSpace M]
  [FirstCountableTopology M] [ConnectedSpace M] [SingularGXStructure G X M]
  {N : Type u} [TopologicalSpace N] [T2Space N] [LocPathConnectedSpace N]
  [FirstCountableTopology N] [ConnectedSpace N] [SingularGXStructure G X N]
  {y₀ : ((Sing G X M)ᶜ : Set M)} {yN : ((Sing G X N)ᶜ : Set N)}

/-- Over `V`, a descent of `φ` reads `p` as `φ⁻¹ ∘ q`. -/
theorem IsChartDescent.base_eq_symm {U : Opens M} {V : Opens N} {φ : U ≃ₜ V}
    {f : MaxBranchedCover (Sing G X N) yN}
    {Ψ : MaxBranchedCover (Sing G X N) yN → MaxBranchedCover (Sing G X M) y₀}
    (hΨ : IsChartDescent (U : Set M) (V : Set N) (chartExt φ) f Ψ) {w : MaxBranchedCover (Sing G X N) yN}
    (hw : w ∈ connectedComponentIn (SpreadEnd.base ⁻¹' (V : Set N)) f) :
    (Ψ w).base = chartExt φ.symm w.base := by
  have hwV : w.base ∈ V := mem_of_mem_connectedComponentIn_preimage hw
  have hm := hΨ.mem w hw
  rw [chartExt_apply φ.symm hwV]
  have h := hΨ.base w hw
  rw [chartExt_apply φ hm] at h
  have : (⟨w.base, hwV⟩ : V) = φ ⟨(Ψ w).base, hm⟩ := Subtype.ext h.symm
  rw [this, Homeomorph.symm_apply_apply]

/-- The descent step of (B) (`RamcovGX.tex:2117–2128`): through a descent `Ψ : V̂ → Û` of `φ⁻¹`,
`D₀ ∘ Ψ` is a developing map of `reg(V̂)`, so it differs from the developing map `D_N` by one
`g ∈ G` on the connected `reg(V̂)`. -/
theorem exists_smul_eq_of_isChartDescent
    (hregM : SemilocallySimplyConnected ((Sing G X M)ᶜ : Set M))
    (hregN : SemilocallySimplyConnected ((Sing G X N)ᶜ : Set N)) {U : Opens M} {V : Opens N}
    {φ : U ≃ₜ V} (hφ : IsAEMorphism G X (φ : U → V)) {D₀ : MaxBranchedCover (Sing G X M) y₀ → X}
    (hD₀ : IsRegDevelopingOnReg G X M y₀ D₀) {Dₙ : MaxBranchedCover (Sing G X N) yN → X}
    (hDₙ : IsRegDevelopingOnReg G X N yN Dₙ) {f : MaxBranchedCover (Sing G X N) yN}
    {Ψ : MaxBranchedCover (Sing G X N) yN → MaxBranchedCover (Sing G X M) y₀}
    (hΨ : IsChartDescent (U : Set M) (V : Set N) (chartExt φ) f Ψ) :
    ∃ g : G, ∀ w ∈ connectedComponentIn (SpreadEnd.base ⁻¹' (V : Set N)) f ∩
      SpreadEnd.base ⁻¹' Reg G X N, D₀ (Ψ w) = g • Dₙ w := by
  obtain ⟨hZo, hZ'o, hZ'c, -, -⟩ := maxBranched_cc_facts hregN V.isOpen hΨ.base_mem
  obtain ⟨hA, hβR⟩ := isRegularOn_base_maxBranched hregN yN
  have hφs : IsAEMorphism G X (φ.symm : V → U) := hφ.symm_of_homeomorph
  have hreg : IsRegularOn G (aePullback G (aeAtlas G X N)
      (SpreadEnd.base : MaxBranchedCover (Sing G X N) yN → N)) (gxModelAtlas G X)
      (fun w => D₀ (Ψ w)) (connectedComponentIn (SpreadEnd.base ⁻¹' (V : Set N)) f ∩
        SpreadEnd.base ⁻¹' Reg G X N) := by
    refine isRegularOn_model_of_eventually_comp hA (hβR.mono inter_subset_right hZ'o)
      fun w hw => ?_
    have hwV : w.base ∈ V := mem_of_mem_connectedComponentIn_preimage hw.1
    have hmU := hΨ.mem w hw.1
    have hΨR : (Ψ w).base ∈ Reg G X M := by
      rw [hΨ.base_eq_symm hw.1, ← chartExt_mem_reg_iff hφ (by rw [← hΨ.base_eq_symm hw.1]; exact hmU)]
      rw [← hΨ.base_eq_symm hw.1, hΨ.base w hw.1]; exact hw.2
    obtain ⟨c', hc', hΨc', h, hh⟩ := hD₀.eventually_eq_smul_chart hregM hΨR
    have hu : (φ.symm ⟨w.base, hwV⟩ : M) ∈ c'.source := by
      rw [← chartExt_apply φ.symm hwV, ← hΨ.base_eq_symm hw.1]; exact hΨc'
    obtain ⟨c, hc, hwc, g, hg⟩ := eventually_chartExt_eq_smul hφs (u := ⟨w.base, hwV⟩) hw.2 hc' hu
    refine ⟨c, hc, hwc, h * g, ?_⟩
    have hcΨ := hΨ.contOn.continuousAt (hZo.mem_nhds hw.1)
    have hcb : Tendsto (SpreadEnd.base : MaxBranchedCover (Sing G X N) yN → N) (𝓝 w)
        (𝓝 w.base) := SpreadEnd.continuous_base.continuousAt
    filter_upwards [hcΨ.eventually hh, hcb.eventually hg, hZo.mem_nhds hw.1] with y h1 h2 h3
    show D₀ (Ψ y) = (h * g) • c y.base
    rw [h1, hΨ.base_eq_symm h3, h2, mul_smul]
  obtain ⟨g, hg⟩ := exists_smul_eq_on_of_isRegularOn hZ'c
    (hDₙ.mono inter_subset_right hZ'o) hreg
  exact ⟨g, hg⟩

end DescStructure

section DescNat

variable {G : Type*} {X : Type*} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
  {M : Type v} [TopologicalSpace M] [T2Space M] [LocPathConnectedSpace M]
  [FirstCountableTopology M] [ConnectedSpace M] [SingularGXStructure G X M]
  {N : Type u} [TopologicalSpace N] [T2Space N] [LocPathConnectedSpace N]
  [FirstCountableTopology N] [ConnectedSpace N] [SingularGXStructure G X N]
  {y₀ : ((Sing G X M)ᶜ : Set M)} {yN : ((Sing G X N)ᶜ : Set N)}

/-- Naturality of `T_{U,V,φ}` built from descents (`RamcovGX.tex:2104–2107`, and the restriction
the gluing l.2101 uses): two charts which, on an open `W` inside both domains, differ by an
automorphism `ψ` of the model (`ψ ∘ φ₁ = φ₂` on `W`) give comparable neighbourhoods at the
points over `W` (equal, `ψ⁻¹` giving the converse). Through the lift `Λ` of `ψ` to
`\widetilde N` (`exists_lift_singularAut`, `T_N`-continuous by hypothesis), the first descent read
through `Λ⁻¹` and the second, restricted near the point, are descents of the same chart; they
differ by `δ ∈ Γ(\widetilde N/N)` (`IsChartDescent.exists_deck`). -/
theorem nhds_descTop_le_of_aut (hregM : SemilocallySimplyConnected ((Sing G X M)ᶜ : Set M))
    (hregN : SemilocallySimplyConnected ((Sing G X N)ᶜ : Set N))
    (hdisc : ∀ x : N, DiscreteTopology
      ((SpreadEnd.base : MaxBranchedCover (Sing G X N) yN → N) ⁻¹' {x}))
    {U₁ U₂ : Set M} {V₁ V₂ : Set N} {φ₁ φ₂ : M → N}
    {fz₁ fz₂ : MaxBranchedCover (Sing G X M) y₀ → MaxBranchedCover (Sing G X N) yN}
    {Ψz₁ Ψz₂ : MaxBranchedCover (Sing G X M) y₀ → MaxBranchedCover (Sing G X N) yN →
      MaxBranchedCover (Sing G X M) y₀}
    {TN : WrappedTop (MaxBranchedCover (Sing G X N) yN)}
    (hU₁ : IsOpen U₁) (hV₁ : IsOpen V₁) (hφc₁ : ContinuousOn φ₁ U₁) (hφinj₁ : InjOn φ₁ U₁)
    (hφV₁ : MapsTo φ₁ U₁ V₁) (hφreg₁ : ∀ m ∈ U₁, φ₁ m ∈ Reg G X N ↔ m ∈ Reg G X M)
    (hF₁ : ∀ z : MaxBranchedCover (Sing G X M) y₀, z.base ∈ U₁ →
      IsChartDescent U₁ V₁ φ₁ (fz₁ z) (Ψz₁ z) ∧ Ψz₁ z (fz₁ z) = z)
    (hU₂ : IsOpen U₂) (hV₂ : IsOpen V₂) (hφc₂ : ContinuousOn φ₂ U₂) (hφinj₂ : InjOn φ₂ U₂)
    (hφV₂ : MapsTo φ₂ U₂ V₂) (hφreg₂ : ∀ m ∈ U₂, φ₂ m ∈ Reg G X N ↔ m ∈ Reg G X M)
    (hF₂ : ∀ z : MaxBranchedCover (Sing G X M) y₀, z.base ∈ U₂ →
      IsChartDescent U₂ V₂ φ₂ (fz₂ z) (Ψz₂ z) ∧ Ψz₂ z (fz₂ z) = z)
    (hTN : IsTamifyingTopology G X N yN TN.top)
    (hAut : ∀ f ∈ aeAutMapsMax G X N yN, Continuous[TN.top, TN.top] f)
    {W : Set M} (hWo : IsOpen W) (hW₂ : W ⊆ U₂) {ψ : N ≃ₜ N}
    (hψ : ψ ∈ singularAut G X N) (hψφ : ∀ m ∈ W, ψ (φ₁ m) = φ₂ m)
    {e : MaxBranchedCover (Sing G X M) y₀} (he : e.base ∈ W) (he₁ : e.base ∈ U₁) :
    @nhds _ (descTop U₁ fz₁ Ψz₁ TN) e ≤ @nhds _ (descTop U₂ fz₂ Ψz₂ TN) e := by
  obtain ⟨Λ, hΛb, hΛ⟩ := exists_lift_singularAut hregN yN hψ
  have hΛc : Continuous[TN.top, TN.top] Λ := hAut _ ⟨Λ, rfl, hΛ⟩
  have hΛsb : ∀ w, (Λ.symm w).base = ψ.symm w.base := fun w => by
    have h := hΛb (Λ.symm w)
    rw [Homeomorph.apply_symm_apply] at h
    rw [h, Homeomorph.symm_apply_apply]
  have hS₀N := isSkeletal_sing G X N
  obtain ⟨-, hβN, -, -, hβlN, -⟩ := maxBranched_basic hS₀N hregN yN
  haveI := hβlN
  obtain ⟨h₁, h₁'⟩ := hF₁ e he₁
  obtain ⟨h₂, h₂'⟩ := hF₂ e (hW₂ he)
  set f₁ := fz₁ e
  set f₂ := fz₂ e
  set Ψ₁ := Ψz₁ e
  set Ψ₂ := Ψz₂ e
  have hf₁ := mem_connectedComponentIn (F := SpreadEnd.base ⁻¹' V₁) h₁.base_mem
  have hf₂ := mem_connectedComponentIn (F := SpreadEnd.base ⁻¹' V₂) h₂.base_mem
  have hV₁o : IsOpen (connectedComponentIn
      ((SpreadEnd.base : MaxBranchedCover (Sing G X N) yN → N) ⁻¹' V₁) f₁) :=
    (hV₁.preimage hβN.isSpread.continuous).connectedComponentIn
  -- a neighbourhood of `f₁` whose points `Ψ₁` sends over `W`
  have hnb : connectedComponentIn (SpreadEnd.base ⁻¹' V₁) f₁ ∩
      Ψ₁ ⁻¹' ((SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) ⁻¹' W) ∈ 𝓝 f₁ := by
    refine Filter.inter_mem (hV₁o.mem_nhds hf₁) ?_
    have hc := h₁.contOn.continuousAt (hV₁o.mem_nhds hf₁)
    refine hc.preimage_mem_nhds ((hWo.preimage SpreadEnd.continuous_base).mem_nhds ?_)
    show (Ψ₁ f₁).base ∈ W
    rw [h₁']; exact he
  obtain ⟨O, hOs, hOo, hfO⟩ := mem_nhds_iff.1 hnb
  obtain ⟨B₀, hB₀, hfB₀, hB₀O⟩ := (isSpread_iff.1 hβN.isSpread).2.2 f₁ O hOo hfO
  set B₁ := B₀ ∩ V₁
  set B₂ := ψ '' B₁ ∩ V₂
  have hB₂o : IsOpen B₂ := (ψ.isOpenMap _ (hB₀.inter hV₁)).inter hV₂
  have hbe : f₂.base = (Λ f₁).base := by
    rw [hΛb, ← h₂.base f₂ hf₂, ← h₁.base f₁ hf₁, h₁', h₂']
    exact (hψφ _ he).symm
  have hgB₂ : (Λ f₁).base ∈ B₂ := ⟨by rw [hΛb]; exact mem_image_of_mem _ ⟨hfB₀, h₁.base_mem⟩,
    hbe ▸ h₂.base_mem⟩
  have hf₂B : f₂.base ∈ B₂ := by rw [hbe]; exact hgB₂
  set U' := U₂ ∩ φ₂ ⁻¹' B₂
  have hU'o : IsOpen U' := hφc₂.isOpen_inter_preimage hU₂ hB₂o
  -- the first descent, read through `Λ⁻¹`
  have hmapsΛ : MapsTo Λ.symm (connectedComponentIn (SpreadEnd.base ⁻¹' B₂) (Λ f₁))
      (connectedComponentIn (SpreadEnd.base ⁻¹' B₁) f₁) := by
    refine image_subset_iff.1 ((isPreconnected_connectedComponentIn.image _
      Λ.symm.continuous.continuousOn).subset_connectedComponentIn
        ⟨Λ f₁, mem_connectedComponentIn hgB₂, Λ.symm_apply_apply f₁⟩ ?_)
    rintro _ ⟨w, hw, rfl⟩
    show (Λ.symm w).base ∈ B₁
    rw [hΛsb]
    obtain ⟨b, hb, hbw⟩ := (mem_of_mem_connectedComponentIn_preimage hw).1
    rw [← hbw, ψ.symm_apply_apply]; exact hb
  have hB₁O : connectedComponentIn ((SpreadEnd.base : MaxBranchedCover (Sing G X N) yN → N) ⁻¹' B₁)
      f₁ ⊆ O := (connectedComponentIn_mono _ (preimage_mono inter_subset_left)).trans hB₀O
  have D₁ : IsChartDescent U' B₂ φ₂ (Λ f₁) (fun w => Ψ₁ (Λ.symm w)) := by
    have hin : ∀ w ∈ connectedComponentIn (SpreadEnd.base ⁻¹' B₂) (Λ f₁),
        Λ.symm w ∈ connectedComponentIn (SpreadEnd.base ⁻¹' V₁) f₁ ∧
          (Ψ₁ (Λ.symm w)).base ∈ W := fun w hw => hOs (hB₁O (hmapsΛ hw))
    have hbase : ∀ w ∈ connectedComponentIn (SpreadEnd.base ⁻¹' B₂) (Λ f₁),
        φ₂ (Ψ₁ (Λ.symm w)).base = w.base := fun w hw => by
      rw [← hψφ _ (hin w hw).2, h₁.base _ (hin w hw).1, hΛsb, ψ.apply_symm_apply]
    refine ⟨hgB₂, h₁.contOn.comp Λ.symm.continuous.continuousOn fun w hw => (hin w hw).1,
      fun w hw => ⟨hW₂ (hin w hw).2, ?_⟩, hbase⟩
    show φ₂ (Ψ₁ (Λ.symm w)).base ∈ B₂
    rw [hbase w hw]; exact mem_of_mem_connectedComponentIn_preimage hw
  have D₂ : IsChartDescent U' B₂ φ₂ f₂ Ψ₂ :=
    h₂.restrict inter_subset_right hf₂ hf₂B fun m hm hmB => ⟨hm, hmB⟩
  obtain ⟨δ, hδ, hδv, -, hEq⟩ := D₁.exists_deck hregM hregN hU'o hB₂o
    (hφc₂.mono inter_subset_left) (hφinj₂.mono inter_subset_left) (fun m hm => hm.2)
    (fun m hm => hφreg₂ m hm.1) hdisc D₂ (mem_connectedComponentIn hgB₂)
    (mem_connectedComponentIn hf₂B)
    (by show Ψ₁ (Λ.symm (Λ f₁)) = Ψ₂ f₂; rw [Λ.symm_apply_apply, h₁', h₂'])
  have hκ : Continuous[TN.top, TN.top] (fun v => δ (Λ v)) :=
    continuous_comp_of TN.top TN.top TN.top (continuous_deck_of_isTamifying hTN hδ) hΛc
  have hev : ∀ᶠ w in @nhds _ TN.top f₁, Ψ₁ w = Ψ₂ (δ (Λ w)) := by
    have hmem : Λ ⁻¹' connectedComponentIn (SpreadEnd.base ⁻¹' B₂) (Λ f₁) ∈ 𝓝 f₁ :=
      Λ.continuous.continuousAt.preimage_mem_nhds
        (((hB₂o.preimage hβN.isSpread.continuous).connectedComponentIn).mem_nhds
          (mem_connectedComponentIn hgB₂))
    filter_upwards [nhds_mono hTN.le_natural hmem] with w hw
    have := hEq hw
    dsimp only at this
    rw [Λ.symm_apply_apply] at this
    exact this.symm
  have hF₁' : ∀ z : MaxBranchedCover (Sing G X M) y₀, z.base ∈ U₁ →
      IsChartDescent U₁ V₁ φ₁ (fz₁ z) (Ψz₁ z) ∧ Ψz₁ z (fz₁ z) = z := hF₁
  rw [nhds_descTop hregM hregN hU₁ hV₁ hφc₁ hφinj₁ hφV₁ hφreg₁ hdisc hF₁' hTN,
    nhds_descTop hregM hregN hU₂ hV₂ hφc₂ hφinj₂ hφV₂ hφreg₂ hdisc hF₂ hTN, descNhds, descNhds,
    if_pos he₁, if_pos (hW₂ he)]
  calc Filter.map Ψ₁ (@nhds _ TN.top f₁)
      = Filter.map (fun w => Ψ₂ (δ (Λ w))) (@nhds _ TN.top f₁) := Filter.map_congr hev
    _ = Filter.map Ψ₂ (Filter.map (fun w => δ (Λ w)) (@nhds _ TN.top f₁)) := by
        rw [Filter.map_map]; rfl
    _ ≤ Filter.map Ψ₂ (@nhds _ TN.top f₂) := by
        refine Filter.map_mono ?_
        have := (@Continuous.tendsto _ _ TN.top TN.top _ hκ f₁)
        rwa [hδv] at this

end DescNat

section DescChart

variable {G : Type*} {X : Type*} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
  {M : Type v} [TopologicalSpace M] [T2Space M] [LocPathConnectedSpace M]
  [FirstCountableTopology M] [ConnectedSpace M] [SingularGXStructure G X M]
  {N : Type u} [TopologicalSpace N] [T2Space N] [LocPathConnectedSpace N]
  [FirstCountableTopology N] [ConnectedSpace N] [SingularGXStructure G X N]

variable (G X) in
/-- An isomorphism `φ : U → V` of open subsets of `M` and of a model `N` *descends from the
maximal covering of the model* if, for every pair of points `e ∈ \widetilde M` over `U` and
`f ∈ \widetilde N` over `φ(p e)`, there is a descent of `φ⁻¹` from the component `V̂ ∋ f` of
`q⁻¹(V)` sending `f` to `e` (`IsChartDescent`: continuous on `V̂`, `φ ∘ p ∘ Ψ = q`), for every
base points. This is the case of the proof of `theo:local_virt_tame` (l.2088–2098) in which the
paper's `T_{U,V,φ}` is the quotient by `V̂ → Û` of `T_α` ITSELF, `r^*T_α` never entering: it holds
when `r : Ṽ → V̂` is an isomorphism (`V̂ → V` is then the maximal covering of `V`, which dominates
`Û → U`, `prop:universality`; informal, not formalized), whatever `ℓ : Ũ → Û`; and when the charts
lift (`IsLiftableChartMap.isDescendingChartMap`). -/
def IsDescendingChartMap {U : Opens M} {V : Opens N} (φ : U ≃ₜ V) : Prop :=
  ∀ (y₀ : ((Sing G X M)ᶜ : Set M)) (yN : ((Sing G X N)ᶜ : Set N))
    (e : MaxBranchedCover (Sing G X M) y₀) (f : MaxBranchedCover (Sing G X N) yN),
    e.base ∈ U → f.base = chartExt φ e.base →
      ∃ Ψ : MaxBranchedCover (Sing G X N) yN → MaxBranchedCover (Sing G X M) y₀,
        IsChartDescent (U : Set M) (V : Set N) (chartExt φ) f Ψ ∧ Ψ f = e

/-- A chart lifting to the maximal coverings (`ℓ`, `r` isomorphisms) descends (the inverse of the
lift is a descent). -/
theorem IsLiftableChartMap.isDescendingChartMap {U : Opens M} {V : Opens N} {φ : U ≃ₜ V}
    (hφ : IsLiftableChartMap G X φ) : IsDescendingChartMap G X φ := by
  intro y₀ yN e f he hf
  obtain ⟨F, F', hl⟩ := hφ.exists_isChartLift e f he (by rw [hf, chartExt_apply])
  have hfV : f ∈ connectedComponentIn (SpreadEnd.base ⁻¹' (V : Set N)) f := by
    have := hl.mapsTo (mem_connectedComponentIn he); rwa [hl.apply_self] at this
  refine ⟨F', ⟨mem_of_mem_connectedComponentIn_preimage hfV, hl.contF', fun w hw =>
    mem_of_mem_connectedComponentIn_preimage (hl.mapsTo' hw), fun w hw => ?_⟩, ?_⟩
  · rw [← hl.base _ (hl.mapsTo' hw), hl.right w hw]
  · rw [← hl.apply_self, hl.left e (mem_connectedComponentIn he)]

/-- `theo:local_virt_tame`'s "locally Galoisian" (`def:singular_manifold_locally_galoisian`) at
`U = N`: `reg N` is semi-locally simply connected at every point of `N` (homotopy form; `X`
locally unloopable). -/
theorem IsLocallyGaloisian.isSLSCAt (hX : IsLocallyUnloopable X) (hgal : IsLocallyGaloisian G X N)
    (x : N) : IsSLSCAt ((Sing G X N)ᶜ : Set N) x := by
  have hT := (hgal ⊤).2 ⟨x, trivial⟩
  have hR : Reg G X (⊤ : Opens N) = ((Sing G X (⊤ : Opens N))ᶜ : Set (⊤ : Opens N)) :=
    (compl_compl _).symm
  rw [hR] at hT
  have hsc := semilocallySimplyConnected_compl_of_sing_subset (G := G) hX
    (isClosed_sing G X (⊤ : Opens N)) subset_rfl
  have hT' := hT.isSLSCAt (isSkeletal_iff.1 (isSkeletal_sing G X (⊤ : Opens N))).isOpen hsc
  have hpre : ((Sing G X (⊤ : Opens N))ᶜ : Set (⊤ : Opens N)) =
      (Subtype.val : (⊤ : Opens N) → N) ⁻¹' (Sing G X N)ᶜ := by
    rw [← hR, reg_opensSingular, show Reg G X N = (Sing G X N)ᶜ from (compl_compl _).symm]
  rw [hpre] at hT'
  exact IsSLSCAt.of_isOpenEmbedding (⊤ : Opens N).isOpen.isOpenEmbedding_subtypeVal hT'

/-- The fibres of `\widetilde N → N` are discrete when `N` is locally Galoisian. -/
theorem discreteTopology_fiber_of_isLocallyGaloisian (hX : IsLocallyUnloopable X)
    (hgal : IsLocallyGaloisian G X N) (yN : ((Sing G X N)ᶜ : Set N)) (x : N) :
    DiscreteTopology ((SpreadEnd.base : MaxBranchedCover (Sing G X N) yN → N) ⁻¹' {x}) := by
  have hS₀ := isSkeletal_sing G X N
  have hreg := semilocallySimplyConnected_compl_of_sing_subset (G := G) hX
    (isClosed_sing G X N) subset_rfl
  obtain ⟨hl, -, -⟩ := maxBranched_instances hS₀ hreg yN
  haveI := hl
  obtain ⟨hbc, hpb⟩ := maxBranched_isBranchedCovering hS₀ hreg yN
  exact discreteTopology_fiber_of_isSLSCAt hbc hS₀ hpb (hgal.isSLSCAt hX x)

theorem mapsTo_chartExt {U : Opens M} {V : Opens N} (φ : U ≃ₜ V) :
    MapsTo (chartExt φ) (U : Set M) (V : Set N) := fun m hm => by
  rw [chartExt_apply φ hm]; exact (φ ⟨m, hm⟩).2

theorem injOn_chartExt {U : Opens M} {V : Opens N} (φ : U ≃ₜ V) :
    InjOn (chartExt φ) (U : Set M) := fun m hm m' hm' h => by
  rw [chartExt_apply φ hm, chartExt_apply φ hm'] at h
  exact congrArg Subtype.val (φ.injective (Subtype.ext h))

end DescChart

section DescVirtTame

variable {G : Type*} {X : Type*} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
  [FaithfulSMul G X]
  {A : Type*} {Xα : A → Type u} [∀ a, TopologicalSpace (Xα a)] [∀ a, T2Space (Xα a)]
  [∀ a, LocPathConnectedSpace (Xα a)] [∀ a, FirstCountableTopology (Xα a)]
  [∀ a, ConnectedSpace (Xα a)] [∀ a, SingularGXStructure G X (Xα a)] {S : ∀ a, Set (Xα a)}

/-- `theo:local_virt_tame`, (ii) ⇒ (i), proved in the case where the proof's `T_{U,V,φ}` is a
quotient of `T_α` itself: if every singular point of `M` is the centre of an `X_A`-chart which
descends from the maximal covering of its model (`IsDescendingChartMap`: `V̂ → V` dominates
`Û → U` — e.g. `r : Ṽ → V̂` an isomorphism, `ℓ : Ũ → Û` ARBITRARY), then `M` is virtually tame.
The local topologies are the `T_{U,V,φ}` (`descTop`, `isLocalTamifying_descTop`: on each `Û` the
quotient of `T_α` by a descent `V̂ → Û`, the paper's ℓ-quotient) over the descending charts and
the natural one over `reg M` (`isLocalTamifying_natural_reg`); they agree over the overlaps by
naturality (`nhds_descTop_le_of_aut`, l.2104–2107, through `XAChart.eq_of_mem_centre` and
`XAChart.exists_aut_eq`), and glue (`exists_isTamifyingTopology_of_local`). The local
Galoisianity of the models is used, as in the paper (l.2093), for the Galoisianity of the
descents (`IsChartDescent.exists_deck`, through the discreteness of the fibres of
`\widetilde X_α → X_α`, `discreteTopology_fiber_of_isLocallyGaloisian`). -/
theorem isVirtuallyTame_of_descending (hX : IsLocallyUnloopable X)
    (hfam : IsAnalyticModelFamily G X Xα S) (hgal : ∀ a, IsLocallyGaloisian G X (Xα a))
    (htam : ∀ a, HasAutContinuousTamifying G X (Xα a))
    {M : Type v} [TopologicalSpace M] [T2Space M] [LocPathConnectedSpace M]
    [FirstCountableTopology M] [ConnectedSpace M] [SingularGXStructure G X M]
    (hdesc : ∀ y ∈ Sing G X M, ∃ (a : A) (c : XAChart G X Xα S a y),
      IsDescendingChartMap G X c.φ) :
    IsVirtuallyTame G X M := by
  obtain ⟨y₀⟩ := (nonempty_compl_of_isSkeletal (isSkeletal_sing G X M)).to_subtype
  have hregM := semilocallySimplyConnected_compl_of_sing_subset (G := G) hX
    (isClosed_sing G X M) subset_rfl
  have hregN : ∀ a, SemilocallySimplyConnected ((Sing G X (Xα a))ᶜ : Set (Xα a)) := fun a =>
    semilocallySimplyConnected_compl_of_sing_subset (G := G) hX (isClosed_sing G X (Xα a)) subset_rfl
  obtain ⟨D₀, hD₀⟩ := exists_isRegDevelopingOnReg hregM y₀
  have htam' : ∀ a, ∃ (yN : ((Sing G X (Xα a))ᶜ : Set (Xα a)))
      (TN : WrappedTop (MaxBranchedCover (Sing G X (Xα a)) yN)),
      IsTamifyingTopology G X (Xα a) yN TN.top ∧
        ∀ f ∈ aeAutMapsMax G X (Xα a) yN, Continuous[TN.top, TN.top] f := fun a => by
    obtain ⟨y, T, h1, h2⟩ := htam a
    exact ⟨y, ⟨T⟩, h1, h2⟩
  choose yN TN hTN hAut using htam'
  have hdisc : ∀ a (x : Xα a), DiscreteTopology
      ((SpreadEnd.base : MaxBranchedCover (Sing G X (Xα a)) (yN a) → Xα a) ⁻¹' {x}) :=
    fun a x => discreteTopology_fiber_of_isLocallyGaloisian hX (hgal a) (yN a) x
  have hDN : ∀ a, ∃ D : MaxBranchedCover (Sing G X (Xα a)) (yN a) → X,
      Continuous[(TN a).top, _] D ∧ IsRegDevelopingOnReg G X (Xα a) (yN a) D :=
    fun a => (hTN a).exists_extension
  choose DN hDNc hDNr using hDN
  have hFam : ∀ c : {c : Σ a : A, Σ x : M, XAChart G X Xα S a x //
        IsDescendingChartMap G X c.2.2.φ},
      ∃ (fz : MaxBranchedCover (Sing G X M) y₀ → MaxBranchedCover (Sing G X (Xα c.1.1)) (yN c.1.1))
        (Ψz : MaxBranchedCover (Sing G X M) y₀ → MaxBranchedCover (Sing G X (Xα c.1.1)) (yN c.1.1) →
          MaxBranchedCover (Sing G X M) y₀),
        ∀ z : MaxBranchedCover (Sing G X M) y₀, z.base ∈ (c.1.2.2.U : Set M) →
          IsChartDescent (c.1.2.2.U : Set M) (c.1.2.2.V : Set (Xα c.1.1)) (chartExt c.1.2.2.φ)
            (fz z) (Ψz z) ∧ Ψz z (fz z) = z := by
    rintro ⟨⟨a, x, c⟩, hc⟩
    obtain ⟨-, hβN, -, -, -, -⟩ := maxBranched_basic (isSkeletal_sing G X (Xα a)) (hregN a) (yN a)
    obtain ⟨f₀, -⟩ := hβN.surjective (Classical.arbitrary (Xα a))
    have : ∀ z : MaxBranchedCover (Sing G X M) y₀, ∃ (f : MaxBranchedCover (Sing G X (Xα a)) (yN a))
        (Ψ : MaxBranchedCover (Sing G X (Xα a)) (yN a) → MaxBranchedCover (Sing G X M) y₀),
        z.base ∈ (c.U : Set M) →
          IsChartDescent (c.U : Set M) (c.V : Set (Xα a)) (chartExt c.φ) f Ψ ∧ Ψ f = z := by
      intro z
      by_cases hz : z.base ∈ (c.U : Set M)
      · obtain ⟨f, hf⟩ := hβN.surjective (chartExt c.φ z.base)
        obtain ⟨Ψ, hΨ, hΨf⟩ := hc y₀ (yN a) z f hz hf
        exact ⟨f, Ψ, fun _ => ⟨hΨ, hΨf⟩⟩
      · exact ⟨f₀, fun _ => z, fun h => absurd h hz⟩
    choose fz Ψz hFz using this
    exact ⟨fz, Ψz, hFz⟩
  choose fz Ψz hFz using hFam
  let ι := Option {c : Σ a : A, Σ x : M, XAChart G X Xα S a x // IsDescendingChartMap G X c.2.2.φ}
  let U : ι → Set M := fun i => match i with
    | none => Reg G X M
    | some c => (c.1.2.2.U : Set M)
  let T : ι → TopologicalSpace (MaxBranchedCover (Sing G X M) y₀) := fun i => match i with
    | none => weakTopMax G X M y₀
    | some c => descTop (c.1.2.2.U : Set M) (fz c) (Ψz c) ⟨(TN c.1.1).top⟩
  have hUo : ∀ i, IsOpen (U i) := by
    rintro (_ | c)
    · exact isOpen_reg G X M
    · exact c.1.2.2.U.isOpen
  have hT : ∀ i, IsLocalTamifying G X M y₀ D₀ (U i) (T i) := by
    rintro (_ | ⟨⟨a, x, c⟩, hc⟩)
    · exact isLocalTamifying_natural_reg hregM hD₀
    · exact isLocalTamifying_descTop hregM (hregN a) c.U.isOpen c.V.isOpen
        (continuousOn_chartExt c.φ) (injOn_chartExt c.φ) (mapsTo_chartExt c.φ)
        (fun m hm => chartExt_mem_reg_iff c.isAEMorphism hm) (hdisc a) (hFz ⟨⟨a, x, c⟩, hc⟩)
        (hTN a) (fun z f hz hf => hc y₀ (yN a) z f hz hf) (hDNc a)
        (fun z hz => exists_smul_eq_of_isChartDescent hregM (hregN a) c.isAEMorphism hD₀
          (hDNr a) (hFz ⟨⟨a, x, c⟩, hc⟩ z hz).1)
  have hcov : ∀ y : M, ∃ i, y ∈ U i := fun y => by
    by_cases hy : y ∈ Reg G X M
    · exact ⟨none, hy⟩
    · obtain ⟨a, c, hc⟩ := hdesc y hy
      exact ⟨some ⟨⟨a, y, c⟩, hc⟩, c.mem⟩
  -- naturality at a singular point: every descending chart agrees with one centred there
  have key : ∀ (b : A) (y : M) (c₀ : XAChart G X Xα S b y) (hc₀ : IsDescendingChartMap G X c₀.φ)
      (i : ι) (e : MaxBranchedCover (Sing G X M) y₀), e.base = y → y ∉ Reg G X M →
      e.base ∈ U i → @nhds _ (T (some ⟨⟨b, y, c₀⟩, hc₀⟩)) e = @nhds _ (T i) e := by
    rintro b y c₀ hc₀ (_ | ⟨⟨a, x, c⟩, hc⟩) e rfl hsing hi
    · exact absurd hi hsing
    set W : Opens M := ⟨connectedComponentIn ((c₀.U : Set M) ∩ c.U) e.base,
      (c₀.U.isOpen.inter c.U.isOpen).connectedComponentIn⟩
    have hyW : e.base ∈ W := mem_connectedComponentIn ⟨c₀.mem, hi⟩
    have hW₀ : W ≤ c₀.U := fun z hz => (connectedComponentIn_subset _ _ hz).1
    have hW : W ≤ c.U := fun z hz => (connectedComponentIn_subset _ _ hz).2
    have hWc : IsConnected (W : Set M) := isConnected_connectedComponentIn_iff.2 ⟨c₀.mem, hi⟩
    obtain rfl := XAChart.eq_of_mem_centre hfam c₀ c W hW₀ hW hWc hyW
    obtain ⟨ψ, hψ, hψeq⟩ := c₀.exists_aut_eq hfam c W hW₀ hW hWc hyW
    have hψφ : ∀ m ∈ (W : Set M), ψ (chartExt c₀.φ m) = chartExt c.φ m := fun m hm => by
      rw [chartExt_apply _ (hW₀ hm), chartExt_apply _ (hW hm)]; exact hψeq ⟨m, hm⟩
    have hψφ' : ∀ m ∈ (W : Set M), ψ⁻¹ (chartExt c.φ m) = chartExt c₀.φ m := fun m hm => by
      rw [← hψφ m hm]; exact ψ.symm_apply_apply _
    exact le_antisymm
      (nhds_descTop_le_of_aut hregM (hregN b) (hdisc b) c₀.U.isOpen c₀.V.isOpen
        (continuousOn_chartExt c₀.φ) (injOn_chartExt c₀.φ) (mapsTo_chartExt c₀.φ)
        (fun m hm => chartExt_mem_reg_iff c₀.isAEMorphism hm) (hFz ⟨⟨b, e.base, c₀⟩, hc₀⟩)
        c.U.isOpen c.V.isOpen (continuousOn_chartExt c.φ) (injOn_chartExt c.φ)
        (mapsTo_chartExt c.φ) (fun m hm => chartExt_mem_reg_iff c.isAEMorphism hm)
        (hFz ⟨⟨b, x, c⟩, hc⟩) (hTN b) (hAut b) W.isOpen hW hψ hψφ hyW (hW₀ hyW))
      (nhds_descTop_le_of_aut hregM (hregN b) (hdisc b) c.U.isOpen c.V.isOpen
        (continuousOn_chartExt c.φ) (injOn_chartExt c.φ) (mapsTo_chartExt c.φ)
        (fun m hm => chartExt_mem_reg_iff c.isAEMorphism hm) (hFz ⟨⟨b, x, c⟩, hc⟩)
        c₀.U.isOpen c₀.V.isOpen (continuousOn_chartExt c₀.φ) (injOn_chartExt c₀.φ)
        (mapsTo_chartExt c₀.φ) (fun m hm => chartExt_mem_reg_iff c₀.isAEMorphism hm)
        (hFz ⟨⟨b, e.base, c₀⟩, hc₀⟩) (hTN b) (hAut b) W.isOpen hW₀ (inv_mem hψ) hψφ' hyW
        (hW hyW))
  have hcompat : ∀ i j (e : MaxBranchedCover (Sing G X M) y₀), e.base ∈ U i → e.base ∈ U j →
      @nhds _ (T i) e = @nhds _ (T j) e := by
    intro i j e hi hj
    by_cases hy : e.base ∈ Reg G X M
    · rw [(hT i).nhds_reg e hi hy, (hT j).nhds_reg e hj hy]
    · obtain ⟨b, c₀, hc₀⟩ := hdesc e.base hy
      rw [← key b _ c₀ hc₀ i e rfl hy hi, key b _ c₀ hc₀ j e rfl hy hj]
  obtain ⟨T', hT'⟩ := exists_isTamifyingTopology_of_local hD₀ U hUo hcov T hT hcompat
  exact ⟨y₀, T', hT'⟩

/-- `theo:local_virt_tame` (`RamcovGX.tex:1974`), proved for the `X_A`-manifolds whose singular
points are centres of charts descending from the maximal coverings of the models
(`IsDescendingChartMap`, which covers `r : Ṽ → V̂` an isomorphism with `ℓ : Ũ → Û` arbitrary, and
the liftable charts): under ALL the theorem's hypotheses (analytic family of locally Galoisian
models, a tamifying topology on each `\widetilde X_α` on which `Aut(\widetilde X_α)` acts
continuously), (i) every such `X_A`-manifold is virtually tame iff (ii) every model is virtually
tame. (ii) ⇒ (i) is `isVirtuallyTame_of_descending`; (i) ⇒ (ii) holds outright by the hypothesis
on the models, as in `local_virt_tame`. -/
theorem local_virt_tame_descending (hX : IsLocallyUnloopable X)
    (hfam : IsAnalyticModelFamily G X Xα S) (hgal : ∀ a, IsLocallyGaloisian G X (Xα a))
    (htam : ∀ a, HasAutContinuousTamifying G X (Xα a)) :
    (∀ (N : Type u) [TopologicalSpace N] [T2Space N] [LocPathConnectedSpace N]
        [FirstCountableTopology N] [ConnectedSpace N] [SingularGXStructure G X N],
        IsXAManifold G X Xα S N →
        (∀ y ∈ Sing G X N, ∃ (a : A) (c : XAChart G X Xα S a y), IsDescendingChartMap G X c.φ) →
        IsVirtuallyTame G X N) ↔ ∀ a, IsVirtuallyTame G X (Xα a) :=
  ⟨fun _ a => (htam a).isVirtuallyTame, fun _ _ _ _ _ _ _ _ _ hdesc =>
    isVirtuallyTame_of_descending hX hfam hgal htam hdesc⟩

end DescVirtTame

/-! ### `theo:local_virt_tame`: what ANY tamifying topology must satisfy (WP-40c)

The tagged `sorry` of `exists_isLocalTamifying_charts` concerns the paper's topologies
`T_{U,V,φ}`. The statements below concern every tamifying topology on `\widetilde M` whatsoever:
a deck transformation fixing a point `s` must be carried by the `D`-small regular part of every
neighbourhood of `s` (`IsTamifyingTopology.exists_joinedIn_devSmall`), so a manifold where it is
not is not virtually tame, by any topology (`not_isVirtuallyTame_of_forall_not_joinedIn`); and at a
point of finite local degree a tamifying topology is the natural one
(`IsTamifyingTopology.nhds_eq_of_finite_stab`). -/

section TamifyingNecessary

/-- A path for a finer topology is a path for a coarser one. -/
theorem joinedIn_of_le_tamNec {α : Type*} {t t' : TopologicalSpace α} (h : t ≤ t') {F : Set α}
    {x y : α} (hj : @JoinedIn α t F x y) : @JoinedIn α t' F x y := by
  obtain ⟨γ, hγ⟩ := hj
  exact ⟨@Path.mk α t' x y (@ContinuousMap.mk unitInterval α _ t' (fun i => γ i)
    (@Continuous.mk unitInterval α _ t' (fun i => γ i) fun s hs =>
      @Continuous.isOpen_preimage unitInterval α _ t _ (@Path.continuous α t x y γ) s
        (TopologicalSpace.le_def.1 h s hs)))
    (@Path.source α t x y γ) (@Path.target α t x y γ), hγ⟩

/-- The topological core of the necessary condition: in a locally path-connected space with a
portly `R`, a continuous self-map `f` preserving `R` and fixing `s` moves some point `z ∈ R`
of any neighbourhood `N` of `s` to a point `f z ∈ N` joined to `z` inside `N ∩ R`. -/
theorem exists_joinedIn_of_isPortly_of_fixed {α : Type*} [TopologicalSpace α]
    [LocPathConnectedSpace α] {R : Set α} (hR : IsPortly R) {f : α → α} (hf : Continuous f)
    (hfR : MapsTo f R R) {s : α} (hfs : f s = s) {N : Set α} (hN : N ∈ 𝓝 s) :
    ∃ z, z ∈ N ∧ f z ∈ N ∧ z ∈ R ∧ JoinedIn (N ∩ R) z (f z) := by
  obtain ⟨O, hON, hO, hsO⟩ := mem_nhds_iff.1 hN
  set W := pathComponentIn O s with hWdef
  have hWo : IsOpen W := hO.pathComponentIn s
  have hWc : IsPathConnected W := isPathConnected_pathComponentIn hsO
  have hsW : s ∈ W := mem_pathComponentIn_self hsO
  have hV : IsOpen (W ∩ f ⁻¹' W) := hWo.inter (hWo.preimage hf)
  obtain ⟨z, hzV, hzR⟩ := hR.dense.inter_open_nonempty _ hV
    ⟨s, hsW, by simp only [mem_preimage, hfs]; exact hsW⟩
  have hWR : IsPreconnected (W ∩ R) :=
    hR.locallyConnectedIn W hWo hWc.isConnected.isPreconnected
  have hpc : IsPathConnected (W ∩ R) :=
    ((hWo.inter hR.isOpen).isConnected_iff_isPathConnected).1 ⟨⟨z, hzV.1, hzR⟩, hWR⟩
  have hj := hpc.joinedIn z ⟨hzV.1, hzR⟩ (f z) ⟨hzV.2, hfR hzR⟩
  exact ⟨z, hON (pathComponentIn_subset hzV.1), hON (pathComponentIn_subset hzV.2), hzR,
    hj.mono fun x hx => ⟨hON (pathComponentIn_subset hx.1), hx.2⟩⟩

variable {G : Type*} {X : Type*} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
  {M : Type v} [TopologicalSpace M] [SingularGXStructure G X M]

/-- A NECESSARY condition for ANY tamifying topology (not only the paper's `T_{U,V,φ}`): if a
deck transformation `f ∈ Γ(\widetilde M/M)` fixes a point `s` of `\widetilde M`, then every
`T`-neighbourhood `N` of `s` contains a regular point `z` with `f z ∈ N`, joined to `z` by a path
in the regular part of `N`. ((C) makes `N ∩ f⁻¹N` a neighbourhood, (D) and local
path-connectedness make its regular part path-connected.) -/
theorem IsTamifyingTopology.exists_joinedIn_reg_of_fixed {y₀ : ((Sing G X M)ᶜ : Set M)}
    {T : TopologicalSpace (MaxBranchedCover (Sing G X M) y₀)}
    (hT : IsTamifyingTopology G X M y₀ T)
    {f : MaxBranchedCover (Sing G X M) y₀ → MaxBranchedCover (Sing G X M) y₀}
    (hf : f ∈ deckMapsMax G X M y₀) {s : MaxBranchedCover (Sing G X M) y₀} (hfs : f s = s)
    {N : Set (MaxBranchedCover (Sing G X M) y₀)} (hN : N ∈ @nhds _ T s) :
    ∃ z, z ∈ N ∧ f z ∈ N ∧ z.base ∈ Reg G X M ∧
      @JoinedIn _ (weakTopMax G X M y₀) (N ∩ SpreadEnd.base ⁻¹' Reg G X M) z (f z) := by
  have hfR : MapsTo f (SpreadEnd.base ⁻¹' Reg G X M) (SpreadEnd.base ⁻¹' Reg G X M) := by
    obtain ⟨γ, hγ, rfl⟩ := hf
    intro x hx
    have h := congrFun (show (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) ∘ γ =
      SpreadEnd.base from hγ) x
    simp only [mem_preimage, Function.comp_apply] at hx h ⊢
    rw [h]; exact hx
  obtain ⟨z, hzN, hfzN, hzR, hj⟩ := @exists_joinedIn_of_isPortly_of_fixed _ T hT.locPathConnected
    _ hT.isPortly f (hT.continuous_deck f hf) hfR s hfs N hN
  exact ⟨z, hzN, hfzN, hzR, joinedIn_of_le_tamNec hT.le_natural hj⟩

/-- The necessary condition read through (B): for a tamifying `T` with a `T`-continuous developing
map `D`, a deck transformation `f` fixing `s` is carried by the `D`-small regular part of every
natural neighbourhood `W` of `s`: some regular `z` is joined to `f z` inside
`W ∩ reg ∩ D⁻¹(E)`, for every neighbourhood `E` of `D(s)`. -/
theorem IsTamifyingTopology.exists_joinedIn_devSmall {y₀ : ((Sing G X M)ᶜ : Set M)}
    {T : TopologicalSpace (MaxBranchedCover (Sing G X M) y₀)}
    (hT : IsTamifyingTopology G X M y₀ T) {D : MaxBranchedCover (Sing G X M) y₀ → X}
    (hDc : Continuous[T, _] D)
    {f : MaxBranchedCover (Sing G X M) y₀ → MaxBranchedCover (Sing G X M) y₀}
    (hf : f ∈ deckMapsMax G X M y₀) {s : MaxBranchedCover (Sing G X M) y₀} (hfs : f s = s)
    {E : Set X} (hE : E ∈ 𝓝 (D s)) {W : Set (MaxBranchedCover (Sing G X M) y₀)}
    (hW : W ∈ @nhds _ (weakTopMax G X M y₀) s) :
    ∃ z, z.base ∈ Reg G X M ∧
      @JoinedIn _ (weakTopMax G X M y₀) (W ∩ (SpreadEnd.base ⁻¹' Reg G X M ∩ D ⁻¹' E)) z (f z) := by
  have hWT : W ∈ @nhds _ T s := nhds_mono hT.le_natural hW
  have hET : D ⁻¹' E ∈ @nhds _ T s :=
    (@Continuous.continuousAt _ _ T _ D s hDc).preimage_mem_nhds hE
  obtain ⟨z, -, -, hzR, hj⟩ := hT.exists_joinedIn_reg_of_fixed hf hfs (Filter.inter_mem hWT hET)
  obtain ⟨γ, hγ⟩ := hj
  exact ⟨z, hzR, γ, fun i => ⟨(hγ i).1.1, (hγ i).2, (hγ i).1.2⟩⟩

/-- The obstruction, as a criterion of NON-virtual-tameness: if a deck transformation `f` fixes a
point `s` of `\widetilde M` and, for every developing map `D` of `reg(\widetilde M)` and every
candidate value `x₀ = D(s)`, there are a neighbourhood `E` of `x₀` and a natural neighbourhood `W`
of `s` such that no regular point `z` of `W` is joined to `f z` inside the `D`-small regular part
`W ∩ reg ∩ D⁻¹(E)`, then NO topology on `\widetilde M` is tamifying. (The `D`-small regular part
near `s` would have to carry the loop of `M` that `f` represents.) -/
theorem not_isTamifyingTopology_of_forall_not_joinedIn {y₀ : ((Sing G X M)ᶜ : Set M)}
    {f : MaxBranchedCover (Sing G X M) y₀ → MaxBranchedCover (Sing G X M) y₀}
    (hf : f ∈ deckMapsMax G X M y₀) {s : MaxBranchedCover (Sing G X M) y₀} (hfs : f s = s)
    (h : ∀ D : MaxBranchedCover (Sing G X M) y₀ → X, IsRegDevelopingOnReg G X M y₀ D →
      ∀ x₀ : X, ∃ E ∈ 𝓝 x₀, ∃ W ∈ @nhds _ (weakTopMax G X M y₀) s, ∀ z,
        ¬ @JoinedIn _ (weakTopMax G X M y₀) (W ∩ (SpreadEnd.base ⁻¹' Reg G X M ∩ D ⁻¹' E))
          z (f z))
    (T : TopologicalSpace (MaxBranchedCover (Sing G X M) y₀)) :
    ¬ IsTamifyingTopology G X M y₀ T := by
  intro hT
  obtain ⟨D, hDc, hDreg⟩ := hT.exists_extension
  obtain ⟨E, hE, W, hW, hno⟩ := h D hDreg (D s)
  obtain ⟨z, -, hj⟩ := hT.exists_joinedIn_devSmall hDc hf hfs hE hW
  exact hno z hj

/-- The obstruction criterion, for every base point: `M` is NOT virtually tame. -/
theorem not_isVirtuallyTame_of_forall_not_joinedIn
    (h : ∀ y₀ : ((Sing G X M)ᶜ : Set M), ∃ f ∈ deckMapsMax G X M y₀,
      ∃ s : MaxBranchedCover (Sing G X M) y₀, f s = s ∧
      ∀ D : MaxBranchedCover (Sing G X M) y₀ → X, IsRegDevelopingOnReg G X M y₀ D →
      ∀ x₀ : X, ∃ E ∈ 𝓝 x₀, ∃ W ∈ @nhds _ (weakTopMax G X M y₀) s, ∀ z,
        ¬ @JoinedIn _ (weakTopMax G X M y₀) (W ∩ (SpreadEnd.base ⁻¹' Reg G X M ∩ D ⁻¹' E))
          z (f z)) :
    ¬ IsVirtuallyTame G X M := by
  rintro ⟨y₀, T, hT⟩
  obtain ⟨f, hf, s, hfs, hs⟩ := h y₀
  exact not_isTamifyingTopology_of_forall_not_joinedIn hf hfs hs T hT

/-- Finite local degree forces naturality: let `e ∈ \widetilde M` have a natural open neighbourhood
`W` such that the deck transformations bringing a point of `W` back into `W` form a FINITE set `F`
of transformations fixing `e` (e.g. `W` a component of `p⁻¹(B)`, `B` small, containing one point of
the fibre of `e`, whose stabiliser is finite; `F = {id}` for a free point). If `\widetilde M → M`
is Galoisian, every tamifying topology has the natural neighbourhoods at `e`. (For a `T`-open
`O ∋ e`, `O₁ = W ∩ ⋂_{f ∈ F} f⁻¹(O)` is `T`-open by (C); by (A) its image `p(O₁)` is open, and
`W ∩ p⁻¹(p O₁) ⊆ O` is a natural neighbourhood of `e`.) -/
theorem IsTamifyingTopology.nhds_eq_of_finite_stab [LocallyConnectedSpace M]
    {y₀ : ((Sing G X M)ᶜ : Set M)}
    (hgal : IsGaloisian (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M))
    {T : TopologicalSpace (MaxBranchedCover (Sing G X M) y₀)}
    (hT : IsTamifyingTopology G X M y₀ T)
    {e : MaxBranchedCover (Sing G X M) y₀} {W : Set (MaxBranchedCover (Sing G X M) y₀)}
    (hWo : IsOpen[weakTopMax G X M y₀] W) (heW : e ∈ W)
    {F : Set (MaxBranchedCover (Sing G X M) y₀ → MaxBranchedCover (Sing G X M) y₀)}
    (hF : F.Finite) (hFd : F ⊆ deckMapsMax G X M y₀) (hFe : ∀ f ∈ F, f e = e)
    (hstab : ∀ f ∈ deckMapsMax G X M y₀, ∀ x ∈ W, f x ∈ W → f ∈ F) :
    @nhds _ T e = @nhds _ (weakTopMax G X M y₀) e := by
  refine le_antisymm (nhds_mono hT.le_natural) fun u hu => ?_
  obtain ⟨O, hOt, hO, heO⟩ := (mem_nhds_iff_of T).1 hu
  have hWT : IsOpen[T] W := TopologicalSpace.le_def.1 hT.le_natural W hWo
  set O₁ := W ∩ ⋂ f ∈ F, f ⁻¹' O with hO₁
  have hO₁o : IsOpen[T] O₁ := @IsOpen.inter _ T _ _ hWT
    (@Set.Finite.isOpen_biInter _ _ T _ _ hF fun f hf =>
      @IsOpen.preimage _ _ T T f (hT.continuous_deck f (hFd hf)) _ hO)
  have heO₁ : e ∈ O₁ := ⟨heW, mem_iInter₂.2 fun f hf => by
    rw [mem_preimage, hFe f hf]; exact heO⟩
  set Q : Set M := SpreadEnd.base '' O₁ with hQ
  have hpre : (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) ⁻¹' Q =
      ⋃ f ∈ deckMapsMax G X M y₀, f ⁻¹' O₁ := by
    ext x
    simp only [hQ, mem_preimage, mem_image, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨o, ho, hox⟩
      obtain ⟨φ, hφ, hφx⟩ := hgal.2 x o hox.symm
      exact ⟨φ, ⟨φ, hφ, rfl⟩, by rw [hφx]; exact ho⟩
    · rintro ⟨f, ⟨φ, hφ, rfl⟩, hfx⟩
      exact ⟨φ x, hfx, congrFun (show (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) ∘ φ =
        SpreadEnd.base from hφ) x⟩
  have hQo : IsOpen Q := by
    have h1 : IsOpen[TopologicalSpace.coinduced SpreadEnd.base T] Q := by
      rw [isOpen_coinduced, hpre]
      exact @isOpen_biUnion _ _ T _ _ fun f hf =>
        @IsOpen.preimage _ _ T T f (hT.continuous_deck f hf) _ hO₁o
    rwa [hT.coinduced_eq] at h1
  have hO'' : IsOpen[weakTopMax G X M y₀] (W ∩ SpreadEnd.base ⁻¹' Q) :=
    @IsOpen.inter _ (weakTopMax G X M y₀) _ _ hWo
      (@IsOpen.preimage _ _ (weakTopMax G X M y₀) _ _ SpreadEnd.continuous_base _ hQo)
  refine Filter.mem_of_superset (@IsOpen.mem_nhds _ (weakTopMax G X M y₀) _ _ hO''
    ⟨heW, e, heO₁, rfl⟩) ?_
  rintro x ⟨hxW, o, ⟨hoW, hoO⟩, hox⟩
  obtain ⟨φ, hφ, hφo⟩ := hgal.2 o x hox
  have hφF := hstab φ ⟨φ, hφ, rfl⟩ o hoW (by rw [hφo]; exact hxW)
  have := mem_iInter₂.1 hoO φ hφF
  rw [mem_preimage, hφo] at this
  exact hOt this

/-- The free case (`F = {id}`): at a point none of whose natural neighbourhood's points is moved back
into it by a non-trivial deck transformation, a tamifying topology is natural. -/
theorem IsTamifyingTopology.nhds_eq_of_free [LocallyConnectedSpace M]
    {y₀ : ((Sing G X M)ᶜ : Set M)}
    (hgal : IsGaloisian (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M))
    {T : TopologicalSpace (MaxBranchedCover (Sing G X M) y₀)}
    (hT : IsTamifyingTopology G X M y₀ T)
    {e : MaxBranchedCover (Sing G X M) y₀} {W : Set (MaxBranchedCover (Sing G X M) y₀)}
    (hWo : IsOpen[weakTopMax G X M y₀] W) (heW : e ∈ W)
    (hfree : ∀ f ∈ deckMapsMax G X M y₀, ∀ x ∈ W, f x ∈ W → f = id) :
    @nhds _ T e = @nhds _ (weakTopMax G X M y₀) e :=
  hT.nhds_eq_of_finite_stab hgal hWo heW (F := {id}) (finite_singleton _)
    (by rintro _ rfl; exact ⟨1, one_mem _, rfl⟩) (by rintro _ rfl; rfl)
    fun f hf x hx hfx => hfree f hf x hx hfx

end TamifyingNecessary

end GX
