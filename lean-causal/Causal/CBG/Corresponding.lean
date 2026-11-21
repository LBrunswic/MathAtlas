import Causal.CBG.Geometry
import Causal.CBG.CausalConvex
import Causal.CorrespondingPoints

/-!
# Corresponding boundary points: `lem:corresponding_K` with `K^±`, `cor:ext_continue`, `C` open

Package 5 (`docs/CBG-DESIGN.md` §3 step 4, first half; §5 row 5). **No label is marked** (DEC-60:
ETT labels are the ETT campaign's; rows stay partial until the singular instance discharges the
model). Cited, unmarked: `lem:corresponding_K` — `ETT.tex:2100`, `cor:ext_continue` —
`ETT.tex:2144`, `cor:model_corresponding` — `ETT.tex:2158`, `rem:non_separe_cas` —
`ETT.tex:2016`, `lem:passe_pgcd` — `ETT.tex:2042`, `lem:Sigma_separe` — `ETT.tex:2062`,
`cor:K_ordre_Sigma` — `ETT.tex:2082`, `prop:K_calcul` — `ETT.tex:1557`, `prop:K_densite_sing` —
`ETT.tex:1634`; Sbierski 1309.7591 Def 3.5, Prop 3.7, Lemma 3.8 (pp. 15–16). No `sorry`.

> Let $p\in \partial j_1(N)\cap J^+(\Sigma_1)$ and $q\in \partial j_2(N)\cap J^+(\Sigma_2)$. The
> following are equivalent:
> \begin{enumerate}[label=(\roman*)]
> \item $(p,q)\in C$;
> \item $f$ induces a bijection
> $$K^-(p)\cap J^+(\Sigma_1)\xrightarrow{\quad f\quad} K^-(q)\cap J^+(\Sigma_2).$$
> \end{enumerate}
> (`ETT.tex:2101–2107`)

> Let $(p,q)\in C$. Then $f$ extends continuously to $p$ by setting $f(p)=q$. (`ETT.tex:2144`)

> A point $p\in \partial j_1(N)$ has at most one corresponding point $q$. Moreover, if $(p,q)\in C$
> and $p\in \sing_\alpha(M_1)$, then $q\in \sing_\alpha(M_2)$. (`ETT.tex:2159–2160`)

> Proposition 3.7. […] i) The points $p\in\partial U$ and $p'\in\partial\psi(U)$ are corresponding
> boundary points. ii) If $\gamma:(-\varepsilon,0)\to U$ is a timelike curve with
> $\lim_{s\nearrow0}\gamma(s)=p$, then $\lim_{s\nearrow0}(\psi\circ\gamma)(s)=p'$. iii) There is a
> timelike curve $\gamma$ […] such that $\lim\psi\circ\gamma(s)=p'$. (Sbierski, p. 15)
> Lemma 3.8. […] Then the set $C$ is open in $\partial U$ […] (Sbierski, p. 16)

## What is proved

* **Model-free core** (any causalities, open sets, kb/0001), **in `Causal.CorrespondingPoints`**
  (ETT layer, imported here; moved there verbatim, same full names, by T-abs-hoist-cbg-cores,
  2026-11-21, together with the namespace `Causality` lemmas on `K⁻` and causal convexity and the
  witnesses): `IsCorrPair` (a bijection `ψ : U → V`,
  `g` its inverse, both continuous, matching `≤`/`≪` of the ambient spacetimes on `U`; `symm`,
  `dual`), `KSide` (the `K⁻`-calculus of `prop:K_calcul`/`prop:K_densite_sing`/`prop:GH_Jferme`
  over a set `Sing` of BTZ points, `lem:Sigma_separe`'s neighbourhood clause, compact
  `J⁺(S) ∩ J⁻(x)`). `IsCorrPair.corresponding_K`: **(i) ⟺ (ii) of `lem:corresponding_K`** in full;
  `corresponding_K_bijOn` (ii) in the paper's literal form (`K⁻(p) ∩ J⁺(S) ⊆ U` and `ψ` a
  `BijOn`); `image_Kminus_eq` (i ⇒ ii), `eq_of_corresponds` (uniqueness on the `J⁺` side),
  `corresponding_K_past`/`_past_bijOn` (`K⁺`, `J⁻`), `corresponds_iff_mem_gluingC` (Def 3.5 =
  ETT's `C`), `corresponds_of_tendsto` (Prop 3.7 iii ⇒ i), `corresponds_iff_eq_of_mem` (the graph
  part of `C`), `Causality.Jplus_mem_nhds_of_isCauchySurface`/`Jminus_mem_nhds_of_isCauchySurface`
  (`lem:Sigma_separe`'s neighbourhood clause from compact diamonds and `K^∓` density, no
  splitting). Witnesses: `timelikeLine_corresponding_hypotheses` (`Sing = ∅`) and
  `lightlikeLine_corresponding_hypotheses` (`Sing = univ`, `p = q` BTZ).
* **Level A** (`CGHDData`, A3's CGHD setting): `CGHDData.corresponding_K`/`_past` and
  `_bijOn`/`_past_bijOn` (the core, every hypothesis derived from A2 and causal convexity,
  `lem:Sigma_separe` included), `ext_continue` (`cor:ext_continue` via A3, both time directions),
  `continuousWithinAt_update` (`p ∈ ∂U`), `continuousWithinAt_update_of_corresponds` (every
  `(p, q) ∈ C`), `tendsto_comp` (Prop 3.7 i ⇒ ii), `eq_of_corresponds`, `mem_sing_iff`
  (`cor:model_corresponding`), `isOpen_correspondingSet` (**`C` is open in `∂U`**).

## Hypothesis checklist (`lem:corresponding_K`, `cor:ext_continue`, Sbierski Prop 3.7 / Lemma 3.8)

| paper | here | note |
|---|---|---|
| `M₀` GH, Cauchy extensions `M₁`, `M₂`, common sub-extension `N`, `f = j₂ ∘ j₁⁻¹` | ✓ carried | in Sbierski's form (a reading of the same setting): `U = j₁(N)` open in `M`, `ψ` injective structure morphism on `U` (`CGHDData`, A3's hypotheses verbatim); model-free: `IsCorrPair` |
| `(p,q) ∈ C`, "not separated" (`ETT.tex:2011–2014`) | ✓ carried | `Corresponds` (Sbierski Def 3.5) `= Gluing.C` of `x ~ ψ x` (`corresponds_iff_mem_gluingC`); no `Cdist` needed (OQ-14) |
| `p ∈ ∂j₁(N) ∩ J⁺(Σ₁)`, `q ∈ ∂j₂(N) ∩ J⁺(Σ₂)` | ✓ carried | |
| (ii) "`f` induces a bijection" | ✓ carried | `corresponding_K_bijOn`: `K⁻(p) ∩ J⁺(S) ⊆ U` and `BijOn ψ (K⁻(p) ∩ J⁺S) (K⁻(q) ∩ J⁺(ψ S))`; equivalently the image equality of `corresponding_K` |
| `prop:K_calcul`, `prop:K_densite_sing`, `J^±(x)` closed, causal | ✓ carried | Level A: derived from A2 (`SingularFlatAxioms`, whose BTZ field is the corrected `Iplus_of_lt`, DEC-64; `kSide_future`/`kSide_past`); model-free core: the model facts as the named hypotheses `KSide` (kb/0012) |
| `lem:Sigma_separe` (through `cor:K_ordre_Sigma`, and silently in "`I⁻(p)` empty iff `I⁻(q)` is") | ✓ carried | Level A: **derived from A2** (`Jplus_mem_nhds_of_isCauchySurface`/`Jminus_…`: `S` acausal by `curvesExtend` + `causallyArcConnected`, `J⁻(S)` closed by `K_densite_sing` + `isCompact_Jminus_inter_Jplus` + T2; past twin with `K⁺` and `isCompact_Jplus_inter_Jminus`), no splitting, no new field; model-free core: named field `KSide.separates` |
| `cor:K_ordre_Sigma` / `cor:K_ordre`, `K_monotone` (`SingularFlatAxioms`) | ⚠ weakened | not assumed: replaced by the model-free `Causality.le_of_Kminus_inter_subset` (`Causal/PushUp.lean:301`) fed by `SingularFlatAxioms.K_densite_sing` (the corrected bundle; never `Iplus_eq`) |
| `M₂` GH: "increasing and bounded above, so it converges" | ⚠ weakened | not assumed: a cluster point in the compact `J⁺(Σ₂) ∩ J⁻(q)` (A2 `isCompact_Jplus_inter_Jminus`) |
| `lem:passe_pgcd`, `lem:image_diamant` | ⚠ weakened | not assumed: replaced by causal convexity of `U` and `ψ(U)` (package 2, `IsCauchyInclusion.causallyConvexIn`), `Kminus_inter_Jplus_subset_of_causallyConvexIn` (the library form for a Cauchy embedding is `IsCauchyEmbedding.passe_pgcd`, `Causal/CauchyDiamond.lean:314`) |
| `lem:cup_cap_sing`, `lem:cup_cap_BTZ` (model computations) | ⚠ weakened | not used: Sbierski's interpolation argument (`le_of_corresponds`/`lt_of_corresponds`) |
| second countable | ⚠ weakened | model-free core: first countable; Level A: carried (`Dev`) |
| `cor:ext_continue` for every `(p,q) ∈ C` | ✓ carried | `continuousWithinAt_update_of_corresponds`: graph pairs (`p ∈ j₁(N)`, `q = ψ p`) by `corresponds_iff_eq_of_mem`, no pair outside `closure U` (`mem_closure_of_corresponds`), boundary pairs below |
| `cor:ext_continue`, `cor:model_corresponding`: the paper's proof via `lem:corresponding_K` | ✓ carried | the statements are proved via A3 (`germExt_future`/`germExt_past`), not via the editorial proof (see SCOPE); no `lem:Sigma_separe` needed |
| past side (`K⁺`, `J⁻(Σ)`) | ✓ carried | `corresponding_K_past`: `K⁺ = I⁺` at every point (BTZ included) — the bundle is not time-symmetric (R4), the core is applied to `.dual` with `Sing = ∅` |

## SCOPE (disclosed)

* **`lem:Sigma_separe` is derived from A2** in `CGHDData.corresponding_K`/`_past` ("`J⁺(S)` is a
  neighbourhood of each point of `J⁺(S) ∖ S`", and its `J⁻` twin, in `M` and in `N`), not from a
  splitting as in the library (`Causality.sigma_separe`): `S` is acausal, `J⁻(S)` is closed (a
  point of its closure has a `K⁻` point `x`, `J⁺(x)` is a neighbourhood of it and
  `J⁻(S) ∩ J⁺(x)` is compact), and `M = J⁺(S) ∪ J⁻(S)`. Both theorems carry no hypothesis
  beyond the CGHD setting. The model-free core keeps it as the named field `KSide.separates`.
* `continuousWithinAt_update`, `ext_continue`, `tendsto_comp`, `mem_sing_iff` ask `p ∈ ∂U`; the
  remaining pairs of the literal `C` (`rem:non_separe_cas`) are graph pairs `(p, ψ p)`, `p ∈ U`
  (`corresponds_iff_eq_of_mem`), handled by `continuousWithinAt_update_of_corresponds`.
* `cor:ext_continue`, uniqueness of the corresponding point, `cor:model_corresponding` (type), Prop
  3.7 (ii) and "`C` open in `∂U`" are proved **from A3** (`germExt_*`, Sbierski Lemma 3.8 taken as
  an axiom of the geometry, design §2). That is the design's route (A3, then `Geometry.isMor_sing`)
  and is not circular here, A3 being a field; it is not the paper's route. Sbierski's own proof of
  Prop 3.7 (ii) (timelike curves, strong causality) is not formalized.
  **Downstream warning (package 11 / gx):** Sbierski proves Lemma 3.8 (= A3) from Prop 3.7 (ii),
  so the A3-derived declarations (`CGHDData.ext_continue`, `continuousWithinAt_update`,
  `continuousWithinAt_update_of_corresponds`, `tendsto_comp`, `eq_of_corresponds`,
  `mem_sing_iff`, `exists_nhds_correspondingSet`, `isOpen_correspondingSet`) **may not be used to
  discharge A3**; the A3-free inputs are the `IsCorrPair` core (`corresponding_K`,
  `corresponding_K_bijOn`, `image_Kminus_eq`, `IsCorrPair.eq_of_corresponds`, the `_past` forms)
  and `CGHDData.corresponding_K`/`_past`/`_bijOn`/`_past_bijOn`, which use A2 only.
* **Interface round 3 (2026-11-02):** A3 (`germExt_*`) now asks `[SecondCountableTopology N]`
  as well as `M`'s, so `ext_continue` and every A3-derived declaration above ask it (a section
  `variable`); `corresponding_K*` asked it already. Package 11's generic A3 at regular points
  (`CBG/FromModel`, `germ_future_reg`) uses none of the A3-derived declarations.
* The editorial proof of `cor:ext_continue` (`ETT.tex:2148–2156`, "[editorial] … verify") is not
  followed. It uses `cor:model_corresponding` (stated after it, `ETT.tex:2158`; its first half
  only, so not circular) and through it `lem:corresponding_K`, which assume `p ∈ J⁺(Σ₁)` and the
  accumulation point `q''` in `J⁺(Σ₂)` — the statement of `cor:ext_continue` assumes neither (a
  point of `J⁻(Σ₁)` needs the `K⁺` form); and "it eventually lies in a compact diamond of `M₂` by
  Lemma `lem:image_diamant`" (`ETT.tex:2155–2156`) is unsupported: the `x_m → p` are not shown
  to lie below one point of `j₁(N)`. Finding.
* The paper's (ii) ⇒ (i) increasing sequence is replaced by a cluster point (no "an increasing
  bounded sequence converges" is needed); `rem:suite_croissante` is not used.
* "`ψ` extends smoothly to `U ∪ C`" (Lemma 3.8, second half) is **not** here: gluing the germs of
  A3 needs A1 on overlaps — package 6. Prop 3.7's "timelike curves" are any filter (`tendsto_comp`,
  `corresponds_of_tendsto`), a strengthening of both (ii) and (iii).
* `continuousWithinAt_update`/`_of_corresponds` carry `[DecidableEq M]` (for `Function.update`),
  harmless.
* Joint satisfiability is witnessed twice, in `Causal.CorrespondingPoints` (section `Witness`,
  moved with the core): the timelike line (`Sing = ∅`, the regular fields) and
  the lightlike line (`Sing = univ`, `KSide.Kminus_sing`/`Iminus_sing` with every other field,
  `p = q = 1` both BTZ). The mixed case (`p` BTZ, `q` regular) is shown impossible in
  `image_Kminus_subset`, so it has no witness to have. At Level A the fields are derived from A2
  (`kSide_future`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set Topology Filter Function TopologicalSpace

universe u v

namespace CBG

/-! ### Level A: the CGHD setting of Sbierski §3.4 -/

section LevelA

variable (𝔊 : Geometry.{u}) {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]

/-- **The setting of Sbierski §3.4 / A3** (`Geometry.germExt_future`'s hypotheses): `U ⊆ M` open,
`ψ` an injective structure morphism on `U`, `M`, `N`, `U`, `ψ(U)` globally hyperbolic, `S ⊆ U` a
Cauchy surface of `M` and of `U` whose image is a Cauchy surface of `N` and of `ψ(U)` — a common
Cauchy development of `M` and `N` with `M₀`'s surface `S` (Sbierski: "`U` a CGHD of `M` and
`M′`"). -/
structure CGHDData (s : 𝔊.Str M) (t : 𝔊.Str N) (U : Opens M) (ψ : M → N) (S : Set M) : Prop where
  isMor : 𝔊.IsMor s t U ψ
  injOn : InjOn ψ U
  gh : (𝔊.causality s).GloballyHyperbolic
  gh' : (𝔊.causality t).GloballyHyperbolic
  ghOn : (𝔊.causality s).GloballyHyperbolicOn U
  ghOn' : (𝔊.causality t).GloballyHyperbolicOn
    ((𝔊.isEMorphismOn_of_isMor isMor).imageOpens U le_rfl)
  subset : S ⊆ U
  cauchy : (𝔊.causality s).IsCauchySurface S
  cauchyOn : (𝔊.causality s).IsCauchySurfaceOn U S
  cauchy' : (𝔊.causality t).IsCauchySurface (ψ '' S)
  cauchyOn' : (𝔊.causality t).IsCauchySurfaceOn
    ((𝔊.isEMorphismOn_of_isMor isMor).imageOpens U le_rfl) (ψ '' S)

variable {𝔊} {s : 𝔊.Str M} {t : 𝔊.Str N} {U : Opens M} {ψ : M → N} {S : Set M}

namespace CGHDData

/-- `ψ(U)`, as an open set. -/
def V (h : CGHDData 𝔊 s t U ψ S) : Opens N :=
  (𝔊.isEMorphismOn_of_isMor h.isMor).imageOpens U le_rfl

@[simp] theorem coe_V (h : CGHDData 𝔊 s t U ψ S) : (h.V : Set N) = ψ '' U := rfl

variable [T2Space M] [ConnectedSpace M] [SecondCountableTopology M]
  [T2Space N] [ConnectedSpace N] [SecondCountableTopology N]

omit [T2Space N] [ConnectedSpace N] [SecondCountableTopology N] in
/-- `U` is causally convex in `M` (design §3 step 3, `IsCauchyInclusion.causallyConvexIn`). -/
theorem causallyConvexIn (h : CGHDData 𝔊 s t U ψ S) :
    (𝔊.causality s).CausallyConvexIn (U : Set M) ⊤ :=
  IsCauchyInclusion.causallyConvexIn ⟨le_top, h.ghOn, h.gh, S, h.subset, h.cauchyOn, h.cauchy⟩
    (𝔊.singularFlatAxioms s).causallyArcConnected
    (Causality.curvesExtendOn_top.2 (𝔊.curvesExtend s h.gh))

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] in
/-- `ψ(U)` is causally convex in `N`. -/
theorem causallyConvexIn' (h : CGHDData 𝔊 s t U ψ S) :
    (𝔊.causality t).CausallyConvexIn (h.V : Set N) ⊤ :=
  IsCauchyInclusion.causallyConvexIn
    ⟨le_top, h.ghOn', h.gh', ψ '' S, image_mono h.subset, h.cauchyOn', h.cauchy'⟩
    (𝔊.singularFlatAxioms t).causallyArcConnected
    (Causality.curvesExtendOn_top.2 (𝔊.curvesExtend t h.gh'))

/-- **The pair `ψ : U → ψ(U)` with its inverse** (`Geometry.isMor_inv`): relations of `M` between
points of `U` are those of `N` between their images — by causal convexity of `U` and `ψ(U)`
(causal arc-connectedness, A2) and the two morphisms. -/
theorem isCorrPair [Nonempty M] (h : CGHDData 𝔊 s t U ψ S) :
    IsCorrPair (𝔊.causality s) (𝔊.causality t) U h.V ψ (invFunOn ψ U) := by
  have hE := 𝔊.isEMorphismOn_of_isMor h.isMor
  have hE' := 𝔊.isEMorphismOn_of_isMor (𝔊.isMor_inv h.isMor h.injOn)
  have hA := 𝔊.singularFlatAxioms s
  have hA' := 𝔊.singularFlatAxioms t
  have hl := h.injOn.leftInvOn_invFunOn
  have hmaps : MapsTo ψ U h.V := fun z hz => ⟨z, hz, rfl⟩
  refine
    { mapsTo := hmaps
      mapsTo_inv := fun y hy => invFunOn_mem hy
      leftInvOn := hl
      rightInvOn := fun y hy => invFunOn_eq hy
      continuousOn := hE.continuousOn
      continuousOn_inv := hE'.continuousOn
      le_iff := fun x hx y hy => ⟨fun hxy => ?_, fun hxy => ?_⟩
      lt_iff := fun x hx y hy => ⟨fun hxy => ?_, fun hxy => ?_⟩ }
  · exact (𝔊.causality t).le_mono le_top (hE.map_le U h.V le_rfl hmaps
      (Causality.le_of_causallyConvexIn_of_le hA.causallyArcConnected h.causallyConvexIn
        subset_rfl le_top hx hy hxy))
  · have hV' := Causality.le_of_causallyConvexIn_of_le hA'.causallyArcConnected
      h.causallyConvexIn' subset_rfl le_top (hmaps hx) (hmaps hy) hxy
    have := hE'.map_le h.V ⊤ le_rfl (fun _ _ => trivial) hV'
    rwa [hl hx, hl hy] at this
  · exact (𝔊.causality t).lt_mono le_top (hE.map_lt U h.V le_rfl hmaps
      (Causality.lt_of_causallyConvexIn hA.causallyArcConnected h.causallyConvexIn hx hy hxy))
  · have hV' := Causality.lt_of_causallyConvexIn hA'.causallyArcConnected
      h.causallyConvexIn' (hmaps hx) (hmaps hy) hxy
    have := hE'.map_lt h.V ⊤ le_rfl (fun _ _ => trivial) hV'
    rwa [hl hx, hl hy] at this

end CGHDData

variable [T2Space M] [ConnectedSpace M] [SecondCountableTopology M]

/-- **The future `K`-calculus of an admissible globally hyperbolic spacetime** (A2, the corrected
bundle: `prop:K_calcul`, `prop:K_densite_sing`, `prop:GH_Jferme`), with `lem:Sigma_separe`'s
neighbourhood clause derived from A2 (`Jplus_mem_nhds_of_isCauchySurface`: `curvesExtend`,
`causallyArcConnected`, `K_densite_sing`, `isCompact_Jminus_inter_Jplus`). -/
theorem kSide_future (s : 𝔊.Str M) (hG : (𝔊.causality s).GloballyHyperbolic) {S : Set M}
    (hS : (𝔊.causality s).IsCauchySurface S) :
    KSide (𝔊.causality s) S (𝔊.sing s 0) := by
  have h := 𝔊.singularFlatAxioms s
  have hsep : ∀ y ∈ (𝔊.causality s).Jplus ⊤ S \ S, (𝔊.causality s).Jplus ⊤ S ∈ 𝓝 y :=
    fun y hy => Causality.Jplus_mem_nhds_of_isCauchySurface hG.1 h.causallyArcConnected
      (𝔊.curvesExtend s hG) hS (fun x => (h.K_densite_sing x).2)
      (𝔊.isCompact_Jminus_inter_Jplus s hG S hS) hy
  exact
    { pushUp := h.pushUp
      causal := hG.1
      isClosed_Jplus := hG.isClosed_Jplus_singleton h.tarentin
      isClosed_Jminus := hG.isClosed_Jminus_singleton h.tarentin
      Kminus_reg := fun x hx => h.pushUp.Kminus_eq_Iminus ((h.mem_Zminus_iff x).2 hx)
      mem_Zminus := fun x hx => (h.mem_Zminus_iff x).2 hx
      Kminus_sing := fun x hx => Causality.Kminus_eq_Jminus_diff hG.1 (h.singularPastAt x hx)
      Iminus_sing := fun x hx => h.Iminus_eq_empty x hx
      dense := fun x => (h.K_densite_sing x).2
      separates := hsep
      isCompact := 𝔊.isCompact_Jplus_inter_Jminus s hG S hS }

/-- **The past `K`-calculus** (no time reversal of the bundle: at every point, BTZ included,
`K⁺ = I⁺` and `p ∈ Z⁺`, `SingularFlatAxioms.mem_Zplus`), read as the future `K`-calculus of
the time-reversed causality with no singular point. `lem:Sigma_separe` for `J⁻` is derived
from A2 (`Jminus_mem_nhds_of_isCauchySurface`, `isCompact_Jplus_inter_Jminus`, `K⁺` density). -/
theorem kSide_past (s : 𝔊.Str M) (hG : (𝔊.causality s).GloballyHyperbolic) {S : Set M}
    (hS : (𝔊.causality s).IsCauchySurface S) :
    KSide (𝔊.causality s).dual S ∅ := by
  have h := 𝔊.singularFlatAxioms s
  have hsep : ∀ y ∈ (𝔊.causality s).Jminus ⊤ S \ S, (𝔊.causality s).Jminus ⊤ S ∈ 𝓝 y :=
    fun y hy => Causality.Jminus_mem_nhds_of_isCauchySurface hG.1 h.causallyArcConnected
      (𝔊.curvesExtend s hG) hS (fun x => (h.K_densite_sing x).1)
      (𝔊.isCompact_Jplus_inter_Jminus s hG S hS) hy
  exact
    { pushUp := Causality.dual_pushUp.2 h.pushUp
      causal := Causality.dual_isCausal.2 hG.1
      isClosed_Jplus := hG.isClosed_Jminus_singleton h.tarentin
      isClosed_Jminus := hG.isClosed_Jplus_singleton h.tarentin
      Kminus_reg := fun x _ => h.pushUp.Kplus_eq_Iplus (h.mem_Zplus x)
      mem_Zminus := fun x _ => h.mem_Zplus x
      Kminus_sing := fun x hx => absurd hx (notMem_empty x)
      Iminus_sing := fun x hx => absurd hx (notMem_empty x)
      dense := fun x => (h.K_densite_sing x).1
      separates := hsep
      isCompact := 𝔊.isCompact_Jminus_inter_Jplus s hG S hS }

variable [T2Space N] [ConnectedSpace N]

namespace CGHDData

/-- `lem:corresponding_K` (`ETT.tex:2100`) **= Sbierski Prop 3.7 with `K⁻`**, future side, in
the CGHD setting of a geometry: for `p ∈ ∂U ∩ J⁺(S)`, `q ∈ ∂ψ(U) ∩ J⁺(ψ S)`, `p` and `q` are
corresponding boundary points iff `ψ` maps `K⁻(p) ∩ J⁺(S)` onto `K⁻(q) ∩ J⁺(ψ S)`. Every
hypothesis of the core, `lem:Sigma_separe` included, is derived from A2 and causal convexity. -/
theorem corresponding_K [SecondCountableTopology N] (h : CGHDData 𝔊 s t U ψ S) {p : M} {q : N} (hp : p ∈ frontier (U : Set M)) (hq : q ∈ frontier (ψ '' U))
    (hpS : p ∈ (𝔊.causality s).Jplus ⊤ S) (hqS : q ∈ (𝔊.causality t).Jplus ⊤ (ψ '' S)) :
    Corresponds (U : Set M) ψ p q ↔
      ψ '' ((𝔊.causality s).Kminus ⊤ {p} ∩ (𝔊.causality s).Jplus ⊤ S) =
        (𝔊.causality t).Kminus ⊤ {q} ∩ (𝔊.causality t).Jplus ⊤ (ψ '' S) := by
  haveI : Nonempty M := ⟨p⟩
  exact h.isCorrPair.corresponding_K (kSide_future s h.gh h.cauchy)
    (kSide_future t h.gh' h.cauchy') h.causallyConvexIn h.causallyConvexIn' h.subset hp hq
    hpS hqS

/-- **`lem:corresponding_K`, past side, `K⁺`** (no duality for `E₀`: the past-side calculus is
`K⁺ = I⁺` at every point, BTZ points included; design R4). -/
theorem corresponding_K_past [SecondCountableTopology N] (h : CGHDData 𝔊 s t U ψ S) {p : M} {q : N} (hp : p ∈ frontier (U : Set M)) (hq : q ∈ frontier (ψ '' U))
    (hpS : p ∈ (𝔊.causality s).Jminus ⊤ S) (hqS : q ∈ (𝔊.causality t).Jminus ⊤ (ψ '' S)) :
    Corresponds (U : Set M) ψ p q ↔
      ψ '' ((𝔊.causality s).Kplus ⊤ {p} ∩ (𝔊.causality s).Jminus ⊤ S) =
        (𝔊.causality t).Kplus ⊤ {q} ∩ (𝔊.causality t).Jminus ⊤ (ψ '' S) := by
  haveI : Nonempty M := ⟨p⟩
  exact h.isCorrPair.corresponding_K_past (kSide_past s h.gh h.cauchy)
    (kSide_past t h.gh' h.cauchy') h.causallyConvexIn h.causallyConvexIn' h.subset hp hq
    hpS hqS

/-- `lem:corresponding_K` (`ETT.tex:2100`), future side, in the CGHD setting, with (ii) in the
paper's literal form: `K⁻(p) ∩ J⁺(S) ⊆ U` and "`f` induces a bijection"
`K⁻(p) ∩ J⁺(S) → K⁻(q) ∩ J⁺(ψ S)`. -/
theorem corresponding_K_bijOn [SecondCountableTopology N] (h : CGHDData 𝔊 s t U ψ S) {p : M}
    {q : N} (hp : p ∈ frontier (U : Set M)) (hq : q ∈ frontier (ψ '' U))
    (hpS : p ∈ (𝔊.causality s).Jplus ⊤ S) (hqS : q ∈ (𝔊.causality t).Jplus ⊤ (ψ '' S)) :
    Corresponds (U : Set M) ψ p q ↔
      (𝔊.causality s).Kminus ⊤ {p} ∩ (𝔊.causality s).Jplus ⊤ S ⊆ U ∧
        BijOn ψ ((𝔊.causality s).Kminus ⊤ {p} ∩ (𝔊.causality s).Jplus ⊤ S)
          ((𝔊.causality t).Kminus ⊤ {q} ∩ (𝔊.causality t).Jplus ⊤ (ψ '' S)) := by
  haveI : Nonempty M := ⟨p⟩
  exact h.isCorrPair.corresponding_K_bijOn (kSide_future s h.gh h.cauchy)
    (kSide_future t h.gh' h.cauchy') h.causallyConvexIn h.causallyConvexIn' h.subset hp hq
    hpS hqS

/-- `lem:corresponding_K`, past side (`K⁺`, `J⁻`), in the CGHD setting, with (ii) in the paper's
literal form. -/
theorem corresponding_K_past_bijOn [SecondCountableTopology N] (h : CGHDData 𝔊 s t U ψ S)
    {p : M} {q : N} (hp : p ∈ frontier (U : Set M)) (hq : q ∈ frontier (ψ '' U))
    (hpS : p ∈ (𝔊.causality s).Jminus ⊤ S) (hqS : q ∈ (𝔊.causality t).Jminus ⊤ (ψ '' S)) :
    Corresponds (U : Set M) ψ p q ↔
      (𝔊.causality s).Kplus ⊤ {p} ∩ (𝔊.causality s).Jminus ⊤ S ⊆ U ∧
        BijOn ψ ((𝔊.causality s).Kplus ⊤ {p} ∩ (𝔊.causality s).Jminus ⊤ S)
          ((𝔊.causality t).Kplus ⊤ {q} ∩ (𝔊.causality t).Jminus ⊤ (ψ '' S)) := by
  haveI : Nonempty M := ⟨p⟩
  exact h.isCorrPair.corresponding_K_past_bijOn (kSide_past s h.gh h.cauchy)
    (kSide_past t h.gh' h.cauchy') h.causallyConvexIn h.causallyConvexIn' h.subset hp hq
    hpS hqS

/- Interface round 3 (design §6, 2026-11-02): A3 (`germExt_*`) asks the second countability of
both carriers, so `ext_continue` and everything derived from it ask `[SecondCountableTopology N]`
(`M`'s is in scope above). -/
variable [SecondCountableTopology N]

/-- `cor:ext_continue` (`ETT.tex:2144`) **via A3**: at a corresponding boundary point, `ψ`
extends to a structure morphism `φ` near `p` with `φ p = q`, and `ψ(x) → q` as `x → p` in `U`.
Both time directions: `p ∈ J⁺(S)` (`germExt_future`) or `p ∈ J⁻(S)` (`germExt_past`), one of
which always holds (`mem_Jplus_union_Jminus_of_isCauchySurface`, curves extending, A2). -/
theorem ext_continue (h : CGHDData 𝔊 s t U ψ S) {p : M} {q : N} (hp : p ∈ frontier (U : Set M))
    (hc : Corresponds (U : Set M) ψ p q) :
    ∃ (O : Opens M) (φ : M → N), p ∈ O ∧ 𝔊.IsMor s t O φ ∧ φ p = q ∧
      EqOn φ ψ (O ⊓ U : Opens M) ∧ Tendsto ψ (𝓝[U] p) (𝓝 q) := by
  have hcl := corresponds_iff_mapClusterPt.1 hc
  obtain ⟨O, φ, hpO, hφ, hφp, heq⟩ : ∃ (O : Opens M) (φ : M → N), p ∈ O ∧ 𝔊.IsMor s t O φ ∧
      φ p = q ∧ EqOn φ ψ (O ⊓ U : Opens M) := by
    rcases Causality.mem_Jplus_union_Jminus_of_isCauchySurface (𝔊.curvesExtend s h.gh)
      h.cauchy p with hpS | hpS
    · exact 𝔊.germExt_future s t U ψ S h.isMor h.injOn h.gh h.gh' h.ghOn h.ghOn' h.subset
        h.cauchy h.cauchyOn h.cauchy' h.cauchyOn' p q hp hpS hcl
    · exact 𝔊.germExt_past s t U ψ S h.isMor h.injOn h.gh h.gh' h.ghOn h.ghOn' h.subset
        h.cauchy h.cauchyOn h.cauchy' h.cauchyOn' p q hp hpS hcl
  refine ⟨O, φ, hpO, hφ, hφp, heq, ?_⟩
  have hφc : ContinuousAt φ p :=
    (𝔊.isEMorphismOn_of_isMor hφ).continuousOn.continuousAt (O.isOpen.mem_nhds hpO)
  have ht : Tendsto φ (𝓝[U] p) (𝓝 q) := by
    rw [← hφp]; exact hφc.tendsto.mono_left nhdsWithin_le_nhds
  refine Tendsto.congr' ?_ ht
  filter_upwards [inter_mem_nhdsWithin (U : Set M) (O.isOpen.mem_nhds hpO)] with x hx
  exact heq ⟨hx.2, hx.1⟩

/-- `cor:ext_continue` in the paper's words: "`f` extends continuously to `p` by setting
`f(p) = q`". -/
theorem continuousWithinAt_update [DecidableEq M] (h : CGHDData 𝔊 s t U ψ S) {p : M} {q : N}
    (hp : p ∈ frontier (U : Set M)) (hc : Corresponds (U : Set M) ψ p q) :
    ContinuousWithinAt (update ψ p q) (insert p (U : Set M)) p := by
  obtain ⟨-, -, -, -, -, -, ht⟩ := h.ext_continue hp hc
  have hpnU : p ∉ (U : Set M) := by rw [U.isOpen.frontier_eq] at hp; exact hp.2
  rw [continuousWithinAt_insert_self, ContinuousWithinAt, update_self]
  refine Tendsto.congr' ?_ ht
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [update_of_ne (ne_of_mem_of_not_mem hx hpnU)]

/-- `cor:ext_continue` (`ETT.tex:2144`) **for every `(p, q) ∈ C`**, the graph part included: a
corresponding `p` is in `closure U` (`mem_closure_of_corresponds`), so either `p ∈ U`, where
`q = ψ p` (`corresponds_iff_eq_of_mem`) and the update is `ψ` itself, or `p ∈ ∂U`
(`continuousWithinAt_update`). -/
theorem continuousWithinAt_update_of_corresponds [DecidableEq M] (h : CGHDData 𝔊 s t U ψ S)
    {p : M} {q : N} (hc : Corresponds (U : Set M) ψ p q) :
    ContinuousWithinAt (update ψ p q) (insert p (U : Set M)) p := by
  by_cases hpU : p ∈ (U : Set M)
  · have hψ := (𝔊.isEMorphismOn_of_isMor h.isMor).continuousOn
    have hq : q = ψ p := (corresponds_iff_eq_of_mem hψ hpU).1 hc
    rw [hq, update_eq_self, insert_eq_of_mem hpU]
    exact hψ p hpU
  · exact h.continuousWithinAt_update ⟨mem_closure_of_corresponds hc, by
      rw [U.isOpen.interior_eq]; exact hpU⟩ hc

/-- **Sbierski Prop 3.7 (i) ⇒ (ii)**, via A3: if `p`, `q` correspond, then `ψ ∘ γ → q` for every
`γ → p` inside `U` (any filter; Sbierski: timelike curves `(−ε, 0) → U`). -/
theorem tendsto_comp (h : CGHDData 𝔊 s t U ψ S) {p : M} {q : N} (hp : p ∈ frontier (U : Set M))
    (hc : Corresponds (U : Set M) ψ p q) {ι : Type*} {F : Filter ι} {γ : ι → M}
    (hγ : Tendsto γ F (𝓝[U] p)) : Tendsto (ψ ∘ γ) F (𝓝 q) := by
  obtain ⟨-, -, -, -, -, -, ht⟩ := h.ext_continue hp hc
  exact ht.comp hγ

/-- **A boundary point has at most one corresponding point** (Sbierski Prop 3.7, "in particular";
`cor:model_corresponding`, first half), via A3, with no hypothesis on the time side of `q`, `q'`. -/
theorem eq_of_corresponds (h : CGHDData 𝔊 s t U ψ S) {p : M} {q q' : N}
    (hp : p ∈ frontier (U : Set M)) (hc : Corresponds (U : Set M) ψ p q)
    (hc' : Corresponds (U : Set M) ψ p q') : q = q' := by
  obtain ⟨-, -, -, -, -, -, ht⟩ := h.ext_continue hp hc
  haveI : NeBot (𝓝[U] p) := mem_closure_iff_nhdsWithin_neBot.1 (frontier_subset_closure hp)
  have hcl : ClusterPt q' (𝓝 q) :=
    ClusterPt.mono (corresponds_iff_mapClusterPt.1 hc' : ClusterPt q' (map ψ (𝓝[U] p))) ht
  exact (eq_of_nhds_neBot hcl).symm

/-- **`cor:model_corresponding`, second half** (`ETT.tex:2158`): corresponding points have the same
type (`p ∈ sing_α(M) ⟺ q ∈ sing_α(N)`), via A3 and `Geometry.isMor_sing`. -/
theorem mem_sing_iff (h : CGHDData 𝔊 s t U ψ S) {p : M} {q : N} (hp : p ∈ frontier (U : Set M))
    (hc : Corresponds (U : Set M) ψ p q) {α : ℝ} (hα : 0 ≤ α) :
    p ∈ 𝔊.sing s α ↔ q ∈ 𝔊.sing t α := by
  obtain ⟨O, φ, hpO, hφ, hφp, -, -⟩ := h.ext_continue hp hc
  rw [← hφp]
  exact 𝔊.isMor_sing hφ hpO hα

end CGHDData

/-- **The set `C` of boundary points with a corresponding point** (Sbierski, before Lemma 3.8). -/
def correspondingSet {M N : Type*} [TopologicalSpace M] [TopologicalSpace N] (U : Set M)
    (ψ : M → N) : Set M :=
  {p | p ∈ frontier U ∧ ∃ q, Corresponds U ψ p q}

namespace CGHDData

variable [SecondCountableTopology N]

/-- Every point of `C` has a neighbourhood `O` with `O ∩ ∂U ⊆ C`: the extension `φ` of A3 is
continuous at every point of `O`, so `φ p'` corresponds to `p' ∈ O ∩ ∂U`. -/
theorem exists_nhds_correspondingSet (h : CGHDData 𝔊 s t U ψ S) {p : M}
    (hp : p ∈ correspondingSet (U : Set M) ψ) :
    ∃ O : Opens M, p ∈ O ∧ (O : Set M) ∩ frontier (U : Set M) ⊆ correspondingSet (U : Set M) ψ := by
  obtain ⟨hpf, q, hc⟩ := hp
  obtain ⟨O, φ, hpO, hφ, -, heq, -⟩ := h.ext_continue hpf hc
  refine ⟨O, hpO, fun p' ⟨hp'O, hp'f⟩ => ⟨hp'f, φ p', ?_⟩⟩
  haveI : NeBot (𝓝[U] p') := mem_closure_iff_nhdsWithin_neBot.1 (frontier_subset_closure hp'f)
  have hφc : ContinuousAt φ p' :=
    (𝔊.isEMorphismOn_of_isMor hφ).continuousOn.continuousAt (O.isOpen.mem_nhds hp'O)
  have ht : Tendsto ψ (𝓝[U] p') (𝓝 (φ p')) := by
    refine Tendsto.congr' ?_ (hφc.tendsto.mono_left nhdsWithin_le_nhds)
    filter_upwards [inter_mem_nhdsWithin (U : Set M) (O.isOpen.mem_nhds hp'O)] with x hx
    exact heq ⟨hx.2, hx.1⟩
  exact corresponds_iff_mapClusterPt.2 ht.mapClusterPt

/-- **"The set `C` is open in `∂U`"** (Sbierski Lemma 3.8, first assertion), via A3:
`C = W ∩ ∂U` for an open `W`. -/
theorem isOpen_correspondingSet (h : CGHDData 𝔊 s t U ψ S) :
    ∃ W : Opens M, correspondingSet (U : Set M) ψ = (W : Set M) ∩ frontier (U : Set M) := by
  refine ⟨sSup {O : Opens M | (O : Set M) ∩ frontier (U : Set M) ⊆
    correspondingSet (U : Set M) ψ}, ?_⟩
  ext p
  constructor
  · intro hp
    obtain ⟨O, hpO, hO⟩ := h.exists_nhds_correspondingSet hp
    exact ⟨Opens.mem_sSup.2 ⟨O, hO, hpO⟩, hp.1⟩
  · rintro ⟨hpW, hpf⟩
    obtain ⟨O, hO, hpO⟩ := Opens.mem_sSup.1 hpW
    exact hO ⟨hpO, hpf⟩

end CGHDData

end LevelA

end CBG

end Causal
