import Causal.CauchyDiamond
import Causal.Pushout

/-!
# Corresponding boundary points, model-free: Sbierski Def 3.5 and `lem:corresponding_K` over `K⁻`

ETT layer (`programme/roadmap.toml` T-abs-hoist-cbg-cores; no paper label): the model-free core of
`Causal.CBG.Corresponding` (package 5, `docs/CBG-DESIGN.md` §3 step 4), moved here verbatim, same
full names and statements, so that a layer-1 module may use it. This module imports
`Causal.CauchyDiamond` and `Causal.Pushout` only: no model (`Causal.Minkowski`, `Causal.Static`,
`Causal.SingularFlat`, `Causal.Flat.*`, `Causal.Model.*`, `Causal.Port.*`), directly or
transitively, and no `Causal.CBG.*` module. `Causal.CBG.Corresponding` imports it and keeps the
Level A (`CGHDData`, A2/A3 of a `CBG.Geometry`). **No label is marked** (DEC-60). Cited, unmarked:
`lem:corresponding_K` — `ETT.tex:2100`, `rem:non_separe_cas` — `ETT.tex:2016`, `lem:passe_pgcd` —
`ETT.tex:2042`, `lem:Sigma_separe` — `ETT.tex:2062`, `cor:K_ordre_Sigma` — `ETT.tex:2082`,
`prop:K_calcul` — `ETT.tex:1557`, `prop:K_densite_sing` — `ETT.tex:1634`; Sbierski 1309.7591
Def 3.5, Prop 3.7 (p. 15). No `sorry`.

> Let $p\in \partial j_1(N)\cap J^+(\Sigma_1)$ and $q\in \partial j_2(N)\cap J^+(\Sigma_2)$. The
> following are equivalent:
> \begin{enumerate}[label=(\roman*)]
> \item $(p,q)\in C$;
> \item $f$ induces a bijection
> $$K^-(p)\cap J^+(\Sigma_1)\xrightarrow{\quad f\quad} K^-(q)\cap J^+(\Sigma_2).$$
> \end{enumerate}
> (`ETT.tex:2101–2107`)

> Proposition 3.7. […] i) The points $p\in\partial U$ and $p'\in\partial\psi(U)$ are corresponding
> boundary points. ii) If $\gamma:(-\varepsilon,0)\to U$ is a timelike curve with
> $\lim_{s\nearrow0}\gamma(s)=p$, then $\lim_{s\nearrow0}(\psi\circ\gamma)(s)=p'$. iii) There is a
> timelike curve $\gamma$ […] such that $\lim\psi\circ\gamma(s)=p'$. (Sbierski, p. 15)

## What is proved

* **`K⁻` and causal convexity** (namespace `Causality`, any causality, open sets, kb/0001):
  `Jplus_mem_nhds_of_mem_Kminus` (a point of `K⁻(p)` has `J⁺` a neighbourhood of `p`),
  `Kminus_inter_Jplus_subset_of_causallyConvexIn` (`lem:passe_pgcd` for a causally convex open
  set), `lt_of_causallyConvexIn`, `mem_Jplus_union_Jminus_of_isCauchySurface` (when curves
  extend), `Jplus_mem_nhds_of_lt`, `exists_lt_lt_of_mem_Zminus`, and `lem:Sigma_separe`'s
  neighbourhood clause from compact diamonds and `K⁻` density, no splitting:
  `Jplus_mem_nhds_of_isAcausal`, `Jplus_mem_nhds_of_isCauchySurface`,
  `Jminus_mem_nhds_of_isCauchySurface`.
* **Sbierski Def 3.5 and the `IsCorrPair` core** (namespace `CBG`): `Corresponds` (the
  neighbourhood condition, in `(U, ψ)` form) with `corresponds_iff_mapClusterPt`,
  `mem_closure_of_corresponds`, `corresponds_iff_eq_of_mem` (the graph part of `C`); `IsCorrPair`
  (a bijection `ψ : U → V`, `g` its inverse, both continuous, matching `≤`/`≪` of the ambient
  spacetimes on `U`; `symm`, `dual`); `KSide` (the `K⁻`-calculus of `prop:K_calcul`/
  `prop:K_densite_sing`/`prop:GH_Jferme` over a set `Sing` of BTZ points, `lem:Sigma_separe`'s
  neighbourhood clause, compact `J⁺(S) ∩ J⁻(x)`). `IsCorrPair.corresponding_K`: (i) ⟺ (ii) of
  `lem:corresponding_K` in full; `corresponding_K_bijOn` (ii) in the paper's literal form;
  `image_Kminus_eq` (i ⇒ ii), `eq_of_corresponds` (uniqueness on the `J⁺` side),
  `corresponding_K_past`/`_past_bijOn` (`K⁺`, `J⁻`), `corresponds_iff_mem_gluingC` (Def 3.5 =
  ETT's `C`), `corresponds_of_tendsto` (Prop 3.7 iii ⇒ i).
* **Witnesses**: `timelikeLine_corresponding_hypotheses` (`Sing = ∅`) and
  `lightlikeLine_corresponding_hypotheses` (`Sing = univ`, `p = q` BTZ), with their parts
  (`iioOne`, `timelikeLine_kSide`, `lightlikeLine_kSide`, …).

## Hypothesis checklist (`lem:corresponding_K`, Sbierski Prop 3.7, model-free)

| paper | here | note |
|---|---|---|
| `M₀` GH, Cauchy extensions `M₁`, `M₂`, common sub-extension `N`, `f = j₂ ∘ j₁⁻¹` | ⚠ replaced | by named hypotheses: `IsCorrPair` (`U` open in `M`, `ψ : U → V` with continuous inverse, matching `≤`/`≪`), `KSide` on each side, `U` and `V` causally convex. The CGHD setting (`CGHDData`, in `Causal.CBG.Corresponding`) supplies all of them (`CGHDData.isCorrPair`, `kSide_future`, `CGHDData.causallyConvexIn`/`causallyConvexIn'`) |
| `(p,q) ∈ C`, "not separated" (`ETT.tex:2011–2014`) | ✓ carried | `Corresponds` (Sbierski Def 3.5) `= Gluing.C` of `x ~ ψ x` (`corresponds_iff_mem_gluingC`); no `Cdist` needed (OQ-14) |
| `p ∈ ∂j₁(N) ∩ J⁺(Σ₁)`, `q ∈ ∂j₂(N) ∩ J⁺(Σ₂)` | ✓ carried | |
| (ii) "`f` induces a bijection" | ✓ carried | `corresponding_K_bijOn`: `K⁻(p) ∩ J⁺(S) ⊆ U` and `BijOn ψ (K⁻(p) ∩ J⁺S) (K⁻(q) ∩ J⁺(ψ S))`; equivalently the image equality of `corresponding_K` |
| `prop:K_calcul`, `prop:K_densite_sing`, `J^±(x)` closed, causal | ✓ carried | the model facts as the named hypotheses `KSide` (kb/0012) |
| `lem:Sigma_separe` (through `cor:K_ordre_Sigma`, and silently in "`I⁻(p)` empty iff `I⁻(q)` is") | ✓ carried | the named field `KSide.separates`; derived from compact diamonds and `K⁻` density in `Jplus_mem_nhds_of_isAcausal`/`_of_isCauchySurface`, no splitting |
| `cor:K_ordre_Sigma` / `cor:K_ordre`, `K_monotone` | ⚠ weakened | not assumed: the model-free `Causality.le_of_Kminus_inter_subset` (`Causal/PushUp.lean`) fed by `KSide.dense` |
| `M₂` GH: "increasing and bounded above, so it converges" | ⚠ weakened | not assumed: a cluster point in the compact `J⁺(ψ S) ∩ J⁻(q)` (`KSide.isCompact`) |
| `lem:passe_pgcd`, `lem:image_diamant` | ⚠ weakened | not assumed: causal convexity of `U` and `V`, `Kminus_inter_Jplus_subset_of_causallyConvexIn` (the library form for a Cauchy embedding is `IsCauchyEmbedding.passe_pgcd`, `Causal/CauchyDiamond.lean`) |
| `lem:cup_cap_sing`, `lem:cup_cap_BTZ` (model computations) | ⚠ weakened | not used: Sbierski's interpolation argument (`le_of_corresponds`/`lt_of_corresponds`) |
| second countable | ⚠ weakened | first countable |
| past side (`K⁺`, `J⁻(Σ)`) | ✓ carried | `corresponding_K_past`/`_past_bijOn`: the future statement for `C.dual`, `D.dual`, under `KSide C.dual S ∅` (`K⁺ = I⁺` at every point) |

## SCOPE (disclosed)

* **Moved, not rewritten** (T-abs-hoist-cbg-cores, 2026-11-21): the namespace `Causality` block
  and the sections `Core` and `Witness` of `Causal.CBG.Corresponding`, byte for byte. Nothing
  here uses `Causal.CBG.Geometry` or `Causal.CBG.CausalConvex`; every declaration here is A3-free
  (Sbierski proves Lemma 3.8 = A3 from Prop 3.7 (ii), so these are the inputs that may be used to
  discharge A3). `Causal.CBG.Corresponding` keeps the Level A: `CGHDData`, `kSide_future`/
  `kSide_past` (the `KSide` fields from A2), `CGHDData.corresponding_K`, `ext_continue`,
  `tendsto_comp` (Prop 3.7 i ⇒ ii, through A3), `correspondingSet`, `isOpen_correspondingSet`.
* `Corresponds U ψ p q` is only the neighbourhood condition, so graph points `(p, ψ p)`,
  `p ∈ U`, satisfy it (`corresponds_iff_eq_of_mem`, `rem:non_separe_cas`); Sbierski's Def 3.5
  for two open embeddings, with both boundary memberships, is `Gluing.IsCorrespondingBoundaryPair`
  (`Causal.GluingHausdorff`, kb/0043). The theorems here ask `p ∈ ∂U`, `q ∈ ∂V` where they need
  them.
* Prop 3.7's "timelike curves" are any filter (`corresponds_of_tendsto`), a strengthening of (iii).
  Prop 3.7 (ii) is not here: Sbierski's own proof (timelike curves, strong causality) is not
  formalized; the library's form is `Causal.CBG.CGHDData.tendsto_comp`, through A3.
* The paper's (ii) ⇒ (i) increasing sequence is replaced by a cluster point (no "an increasing
  bounded sequence converges" is needed); `rem:suite_croissante` is not used.
* Joint satisfiability is witnessed twice: the timelike line (`Sing = ∅`, the regular fields) and
  the lightlike line (`Sing = univ`, `KSide.Kminus_sing`/`Iminus_sing` with every other field,
  `p = q = 1` both BTZ). The mixed case (`p` BTZ, `q` regular) is shown impossible in
  `image_Kminus_subset`, so it has no witness to have.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set Topology Filter Function TopologicalSpace

universe u v

/-! ### Model-free lemmas on `K⁻` and causal convexity -/

namespace Causality

variable {M : Type u} [TopologicalSpace M] {C : Causality M} {p x : M}

/-- A point of `K⁻(p)` has `J⁺` a neighbourhood of `p`. -/
theorem Jplus_mem_nhds_of_mem_Kminus [FirstCountableTopology M] (hx : x ∈ C.Kminus ⊤ {p}) :
    C.Jplus ⊤ {x} ∈ 𝓝 p := by
  by_contra h
  have hcl : p ∈ closure (C.Jplus ⊤ {x})ᶜ := by
    rw [closure_compl, mem_compl_iff, mem_interior_iff_mem_nhds]; exact h
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 hcl
  obtain ⟨N₀, hN₀⟩ := mem_Kminus_singleton.1 hx u hlim
  have hxu : x ∈ C.Jminus ⊤ {u N₀} := mem_iInter₂.1 (interiorWithin_subset hN₀).2 N₀ le_rfl
  rw [Precausality.mem_Jminus_singleton] at hxu
  exact hu N₀ (by rw [Precausality.mem_Jplus_singleton]; exact hxu)

/-- `lem:passe_pgcd` (`ETT.tex:2042`) for a causally convex open set `U` (kb/0001: an open set, not
a Cauchy embedding; the library form is `IsCauchyEmbedding.passe_pgcd`,
`Causal/CauchyDiamond.lean:314`, which needs `image_diamant`'s hypotheses instead of convexity). -/
theorem Kminus_inter_Jplus_subset_of_causallyConvexIn [FirstCountableTopology M] {U : Opens M}
    (hU : C.CausallyConvexIn (U : Set M) ⊤) {S : Set M} (hSU : S ⊆ U)
    (hp : p ∈ closure (U : Set M)) : C.Kminus ⊤ {p} ∩ C.Jplus ⊤ S ⊆ U := by
  rintro y ⟨hyK, σ, hσ, hσy⟩
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 hp
  obtain ⟨N₀, hN₀⟩ := mem_Kminus_singleton.1 hyK u hlim
  have hy : y ∈ C.Jminus ⊤ {u N₀} := mem_iInter₂.1 (interiorWithin_subset hN₀).2 N₀ le_rfl
  rw [Precausality.mem_Jminus_singleton] at hy
  exact hU.2 σ (hSU hσ) (u N₀) (hu N₀) (mem_diamond.2 ⟨hσy, hy⟩)

/-- The chronological half of `le_of_causallyConvexIn_of_le`. -/
theorem lt_of_causallyConvexIn (hC : C.CausallyArcConnected) {V : Opens M}
    (hV : C.CausallyConvexIn (V : Set M) ⊤) {x y : M} (hx : x ∈ V) (hy : y ∈ V)
    (hxy : C.lt ⊤ x y) : C.lt V x y := by
  obtain ⟨γ, hγ, rfl, rfl⟩ := (hC ⊤ le_rfl x y).2.1 hxy
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ V := fun t ht =>
    hV.2 _ hx _ hy (mem_diamond.2 ⟨hγ.causalCurveOn.le_of_le le_rfl ht.1 ht.2,
      hγ.causalCurveOn.le_of_le ht.1 ht.2 le_rfl⟩)
  have hγV : C.ChronalCurveOn V γ 0 1 := CurveOn.restrict hγ le_rfl le_rfl le_top hmem
  exact (hC V le_top _ _).2.2 ⟨γ, hγV, rfl, rfl⟩

/-- Every point lies in `J⁺(S) ∪ J⁻(S)` for a Cauchy surface `S`, when curves extend. -/
theorem mem_Jplus_union_Jminus_of_isCauchySurface (hext : C.CurvesExtend) {S : Set M}
    (hS : C.IsCauchySurface S) (x : M) : x ∈ C.Jplus ⊤ S ∪ C.Jminus ⊤ S := by
  obtain ⟨I, c, hc, hsub⟩ := hext (fun _ => x) 0 1 zero_le_one
    (causalCurveOn_const (show x ∈ (⊤ : Opens M) from trivial))
  obtain ⟨t, ht, hct⟩ := hsub ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
  replace hct : c t = x := hct
  obtain ⟨_, ⟨⟨τ, hτ, rfl⟩, hτS⟩, -⟩ := hS I c hc
  rcases le_total t τ with h | h
  · right
    exact ⟨c τ, hτS, by rw [← hct]; exact hc.1.le_of_le ht hτ h⟩
  · left
    exact ⟨c τ, hτS, by rw [← hct]; exact hc.1.le_of_le hτ ht h⟩

/-- `x ≪ p` makes `J⁺(x)` a neighbourhood of `p`. -/
theorem Jplus_mem_nhds_of_lt {s : M} (hsp : C.lt ⊤ s p) : C.Jplus ⊤ {s} ∈ 𝓝 p :=
  mem_interior_iff_mem_nhds.1 (Iplus_subset_interior_Jplus (by simpa using hsp))

/-- Interpolation at a point strongly tarentin in the past: `x ≪ p`, `p ∈ Z⁻` give `x ≪ s ≪ p`. -/
theorem exists_lt_lt_of_mem_Zminus (hZ : p ∈ C.Zminus) (hxp : C.lt ⊤ x p) :
    ∃ s, C.lt ⊤ x s ∧ C.lt ⊤ s p := by
  obtain ⟨s, hs, hsx⟩ := hZ _ (isOpen_Iplus.mem_nhds (show p ∈ C.Iplus ⊤ {x} by simpa using hxp))
  exact ⟨s, by simpa using hsx, by simpa using hs⟩

/-- **`lem:Sigma_separe`'s neighbourhood clause** (`ETT.tex:2062`), from compact diamonds and `K⁻`
density instead of a splitting: for `S` acausal with `M = J⁺(S) ∪ J⁻(S)`, `J⁻(S)` is closed (a
point `y` of its closure has some `x ∈ K⁻(y)`, `J⁺(x)` is a neighbourhood of `y`, and
`J⁻(S) ∩ J⁺(x)` is compact), `J⁺(S) ∖ S` misses `J⁻(S)` (acausality, causality), so
`M ∖ J⁻(S) ⊆ J⁺(S)` is an open neighbourhood of every point of `J⁺(S) ∖ S`. -/
theorem Jplus_mem_nhds_of_isAcausal [T2Space M] [FirstCountableTopology M] (hcaus : C.IsCausal)
    {S : Set M} (hac : C.IsAcausal S) (hcov : ∀ x, x ∈ C.Jplus ⊤ S ∪ C.Jminus ⊤ S)
    (hdense : ∀ x, C.Jminus ⊤ {x} ⊆ closure (C.Kminus ⊤ {x}))
    (hcpt : ∀ x, IsCompact (C.Jminus ⊤ S ∩ C.Jplus ⊤ {x})) {y : M}
    (hy : y ∈ C.Jplus ⊤ S \ S) : C.Jplus ⊤ S ∈ 𝓝 y := by
  have hcl : IsClosed (C.Jminus ⊤ S) := by
    refine isClosed_of_closure_subset fun z hz => ?_
    have hzK : z ∈ closure (C.Kminus ⊤ {z}) :=
      hdense z (by simpa using C.le_refl (U := ⊤) (x := z) trivial)
    obtain ⟨x, -, hx⟩ := mem_closure_iff_nhds.1 hzK univ univ_mem
    have hJ := Jplus_mem_nhds_of_mem_Kminus hx
    have hz' : z ∈ closure (C.Jminus ⊤ S ∩ C.Jplus ⊤ {x}) := by
      rw [mem_closure_iff_nhds] at hz ⊢
      intro O hO
      obtain ⟨w, ⟨hwO, hwJ⟩, hwS⟩ := hz (O ∩ C.Jplus ⊤ {x}) (inter_mem hO hJ)
      exact ⟨w, hwO, hwS, hwJ⟩
    exact ((hcpt x).isClosed.closure_subset hz').1
  have hyn : y ∉ C.Jminus ⊤ S := by
    rintro ⟨σ', hσ', hyσ'⟩
    obtain ⟨⟨σ, hσ, hσy⟩, hyS⟩ := hy
    have e : σ = σ' := hac σ hσ σ' hσ' (C.le_trans hσy hyσ')
    subst e
    exact hyS (hcaus hyσ' hσy ▸ hσ)
  refine mem_of_superset (hcl.isOpen_compl.mem_nhds hyn) fun z hz => ?_
  rcases hcov z with h | h
  · exact h
  · exact absurd h hz

/-- **`lem:Sigma_separe`, future side, for a Cauchy surface** (`ETT.tex:2062`): `J⁺(S)` is a
neighbourhood of every point of `J⁺(S) ∖ S`, when curves extend, `M` is causal and causally
arc-connected (`S` acausal, `IsCauchySurface.isAcausal`), `J⁻(x) ⊆ closure K⁻(x)`
(`prop:K_densite_sing`) and `J⁻(S) ∩ J⁺(x)` is compact. -/
theorem Jplus_mem_nhds_of_isCauchySurface [T2Space M] [FirstCountableTopology M]
    (hcaus : C.IsCausal) (hC : C.CausallyArcConnected) (hext : C.CurvesExtend) {S : Set M}
    (hS : C.IsCauchySurface S) (hdense : ∀ x, C.Jminus ⊤ {x} ⊆ closure (C.Kminus ⊤ {x}))
    (hcpt : ∀ x, IsCompact (C.Jminus ⊤ S ∩ C.Jplus ⊤ {x})) {y : M}
    (hy : y ∈ C.Jplus ⊤ S \ S) : C.Jplus ⊤ S ∈ 𝓝 y :=
  Jplus_mem_nhds_of_isAcausal hcaus (hS.isAcausal hC hext)
    (mem_Jplus_union_Jminus_of_isCauchySurface hext hS) hdense hcpt hy

/-- **`lem:Sigma_separe`, past side** (`J⁻(S)` a neighbourhood of every point of `J⁻(S) ∖ S`):
the future statement for `C.dual`, fed with `J⁺(x) ⊆ closure K⁺(x)` and compact
`J⁺(S) ∩ J⁻(x)` (stated in `C`'s own terms; only acausality and causality are dualised). -/
theorem Jminus_mem_nhds_of_isCauchySurface [T2Space M] [FirstCountableTopology M]
    (hcaus : C.IsCausal) (hC : C.CausallyArcConnected) (hext : C.CurvesExtend) {S : Set M}
    (hS : C.IsCauchySurface S) (hdense : ∀ x, C.Jplus ⊤ {x} ⊆ closure (C.Kplus ⊤ {x}))
    (hcpt : ∀ x, IsCompact (C.Jplus ⊤ S ∩ C.Jminus ⊤ {x})) {y : M}
    (hy : y ∈ C.Jminus ⊤ S \ S) : C.Jminus ⊤ S ∈ 𝓝 y :=
  Jplus_mem_nhds_of_isAcausal (C := C.dual) (dual_isCausal.2 hcaus)
    (dual_isAcausal.2 (hS.isAcausal hC hext))
    (fun x => (mem_Jplus_union_Jminus_of_isCauchySurface hext hS x).symm) hdense hcpt hy

end Causality

namespace CBG

section Core

variable {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]

/-- Sbierski Def 3.5, the relation. -/
def Corresponds (U : Set M) (ψ : M → N) (p : M) (q : N) : Prop :=
  ∀ O ∈ 𝓝 p, ∀ O' ∈ 𝓝 q, ∃ x ∈ U, x ∈ O ∧ ψ x ∈ O'

theorem corresponds_iff_mapClusterPt {U : Set M} {ψ : M → N} {p : M} {q : N} :
    Corresponds U ψ p q ↔ MapClusterPt q (𝓝[U] p) ψ := by
  constructor
  · intro h
    refine mapClusterPt_iff_frequently.2 fun O' hO' => frequently_iff.2 fun hT => ?_
    obtain ⟨O, hO, hOU⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hT
    obtain ⟨x, hxU, hxO, hψ⟩ := h O hO O' hO'
    exact ⟨x, hOU ⟨hxO, hxU⟩, hψ⟩
  · intro h O hO O' hO'
    obtain ⟨x, ⟨hxU, hxO⟩, hψ⟩ :=
      frequently_iff.1 (mapClusterPt_iff_frequently.1 h O' hO') (inter_mem_nhdsWithin U hO)
    exact ⟨x, hxU, hxO, hψ⟩

/-- A corresponding point lies in `closure U` (the paper's `C` has no point outside
`closure j₁(N)`). -/
theorem mem_closure_of_corresponds {U : Set M} {ψ : M → N} {p : M} {q : N}
    (hc : Corresponds U ψ p q) : p ∈ closure U :=
  mem_closure_iff_nhds.2 fun O hO => by
    obtain ⟨x, hxU, hxO, -⟩ := hc O hO univ univ_mem
    exact ⟨x, hxO, hxU⟩

/-- **The graph part of `C`** (`rem:non_separe_cas`, `ETT.tex:2016`): at a point `p` of `U`, `ψ`
continuous on `U`, `p` and `q` correspond iff `q = ψ p` (`N` Hausdorff). -/
theorem corresponds_iff_eq_of_mem [T2Space N] {U : Set M} {ψ : M → N} {p : M} {q : N}
    (hψ : ContinuousOn ψ U) (hp : p ∈ U) : Corresponds U ψ p q ↔ q = ψ p := by
  constructor
  · intro hc
    have ht : Tendsto ψ (𝓝[U] p) (𝓝 (ψ p)) := hψ p hp
    haveI : NeBot (𝓝[U] p) := mem_closure_iff_nhdsWithin_neBot.1 (subset_closure hp)
    have hcl : ClusterPt q (𝓝 (ψ p)) :=
      ClusterPt.mono (corresponds_iff_mapClusterPt.1 hc : ClusterPt q (map ψ (𝓝[U] p))) ht
    exact eq_of_nhds_neBot hcl
  · rintro rfl O hO O' hO'
    exact ⟨p, hp, mem_of_mem_nhds hO, mem_of_mem_nhds hO'⟩

/-- The pair `ψ : U → V`, `g : V → U`. -/
structure IsCorrPair (C : Causality M) (D : Causality N) (U : Opens M) (V : Opens N) (ψ : M → N)
    (g : N → M) : Prop where
  mapsTo : MapsTo ψ U V
  mapsTo_inv : MapsTo g V U
  leftInvOn : LeftInvOn g ψ U
  rightInvOn : LeftInvOn ψ g V
  continuousOn : ContinuousOn ψ U
  continuousOn_inv : ContinuousOn g V
  le_iff : ∀ x ∈ U, ∀ y ∈ U, C.le ⊤ x y ↔ D.le ⊤ (ψ x) (ψ y)
  lt_iff : ∀ x ∈ U, ∀ y ∈ U, C.lt ⊤ x y ↔ D.lt ⊤ (ψ x) (ψ y)

/-- The K-calculus side. -/
structure KSide (C : Causality M) (S Sing : Set M) : Prop where
  pushUp : C.PushUp
  causal : C.IsCausal
  isClosed_Jplus : ∀ x, IsClosed (C.Jplus ⊤ {x})
  isClosed_Jminus : ∀ x, IsClosed (C.Jminus ⊤ {x})
  Kminus_reg : ∀ x ∉ Sing, C.Kminus ⊤ {x} = C.Iminus ⊤ {x}
  mem_Zminus : ∀ x ∉ Sing, x ∈ C.Zminus
  Kminus_sing : ∀ x ∈ Sing, C.Kminus ⊤ {x} = C.Jminus ⊤ {x} \ {x}
  Iminus_sing : ∀ x ∈ Sing, C.Iminus ⊤ {x} = ∅
  dense : ∀ x, C.Jminus ⊤ {x} ⊆ closure (C.Kminus ⊤ {x})
  separates : ∀ y ∈ C.Jplus ⊤ S \ S, C.Jplus ⊤ S ∈ 𝓝 y
  isCompact : ∀ x, IsCompact (C.Jplus ⊤ S ∩ C.Jminus ⊤ {x})

variable {C : Causality M} {D : Causality N} {U : Opens M} {V : Opens N} {ψ : M → N} {g : N → M}

namespace IsCorrPair

theorem symm (h : IsCorrPair C D U V ψ g) : IsCorrPair D C V U g ψ where
  mapsTo := h.mapsTo_inv
  mapsTo_inv := h.mapsTo
  leftInvOn := h.rightInvOn
  rightInvOn := h.leftInvOn
  continuousOn := h.continuousOn_inv
  continuousOn_inv := h.continuousOn
  le_iff x hx y hy := by
    rw [h.le_iff _ (h.mapsTo_inv hx) _ (h.mapsTo_inv hy), h.rightInvOn hx, h.rightInvOn hy]
  lt_iff x hx y hy := by
    rw [h.lt_iff _ (h.mapsTo_inv hx) _ (h.mapsTo_inv hy), h.rightInvOn hx, h.rightInvOn hy]

theorem dual (h : IsCorrPair C D U V ψ g) : IsCorrPair C.dual D.dual U V ψ g where
  mapsTo := h.mapsTo
  mapsTo_inv := h.mapsTo_inv
  leftInvOn := h.leftInvOn
  rightInvOn := h.rightInvOn
  continuousOn := h.continuousOn
  continuousOn_inv := h.continuousOn_inv
  le_iff x hx y hy := h.le_iff y hy x hx
  lt_iff x hx y hy := h.lt_iff y hy x hx

theorem corresponds_symm (h : IsCorrPair C D U V ψ g) {p : M} {q : N}
    (hc : Corresponds (U : Set M) ψ p q) : Corresponds (V : Set N) g q p := by
  intro O' hO' O hO
  obtain ⟨x, hxU, hxO, hψ⟩ := hc O hO O' hO'
  exact ⟨ψ x, h.mapsTo hxU, hψ, by rw [h.leftInvOn hxU]; exact hxO⟩

theorem mem_frontier_of_corresponds [T2Space M] (h : IsCorrPair C D U V ψ g) {p : M} {q : N}
    (hp : p ∈ frontier (U : Set M)) (hc : Corresponds (U : Set M) ψ p q) :
    q ∈ frontier (V : Set N) := by
  rw [V.isOpen.frontier_eq]
  rw [U.isOpen.frontier_eq] at hp
  refine ⟨mem_closure_iff_nhds.2 fun O' hO' => ?_, fun hqV => ?_⟩
  · obtain ⟨x, hxU, -, hψ⟩ := hc univ univ_mem O' hO'
    exact ⟨ψ x, hψ, h.mapsTo hxU⟩
  · have hu : g q ∈ U := h.mapsTo_inv hqV
    have hgc : ContinuousAt g q := h.continuousOn_inv.continuousAt (V.isOpen.mem_nhds hqV)
    have hpu : p = g q := by
      by_contra hne
      obtain ⟨O, W, hO, hW, hpO, huW, hOW⟩ := t2_separation hne
      obtain ⟨x, hxU, hxO, hψ⟩ := hc O (hO.mem_nhds hpO) (g ⁻¹' W) (hgc (hW.mem_nhds huW))
      rw [mem_preimage, h.leftInvOn hxU] at hψ
      exact Set.disjoint_left.1 hOW hxO hψ
    exact hp.2 (hpu ▸ hu)

/-- **The cluster step** (Sbierski, proof of Prop 3.7: "`ψ(q) ≤ t'₁` … since the relation `≤` is
closed"): if `J⁺(x)` is a neighbourhood of `p` and `q` corresponds to `p`, then `ψ x ≤ q`. -/
theorem le_of_corresponds (h : IsCorrPair C D U V ψ g) {x p : M} {q : N}
    (hcl : IsClosed (D.Jplus ⊤ {ψ x})) (hx : x ∈ U) (hJ : C.Jplus ⊤ {x} ∈ 𝓝 p)
    (hc : Corresponds (U : Set M) ψ p q) : D.le ⊤ (ψ x) q := by
  have hq : q ∈ closure (D.Jplus ⊤ {ψ x}) := mem_closure_iff_nhds.2 fun O' hO' => by
    obtain ⟨y, hyU, hyJ, hψ⟩ := hc _ hJ O' hO'
    rw [Precausality.mem_Jplus_singleton] at hyJ
    exact ⟨ψ y, hψ, by rw [Precausality.mem_Jplus_singleton]; exact (h.le_iff x hx y hyU).1 hyJ⟩
  rw [hcl.closure_eq, Precausality.mem_Jplus_singleton] at hq
  exact hq

/-- **The strict step** (Sbierski: "take an `s ∈ U` with `q ≪ s ≪ p` … `ψ(q) ≪ ψ(s) ≤ p′`"). -/
theorem lt_of_corresponds (h : IsCorrPair C D U V ψ g) (hP : D.PushUp) {x s p : M} {q : N}
    (hcl : IsClosed (D.Jplus ⊤ {ψ s})) (hx : x ∈ U) (hs : s ∈ U) (hxs : C.lt ⊤ x s)
    (hJ : C.Jplus ⊤ {s} ∈ 𝓝 p) (hc : Corresponds (U : Set M) ψ p q) : D.lt ⊤ (ψ x) q :=
  hP.lt_of_lt_of_le ((h.lt_iff x hx s hs).1 hxs) (h.le_of_corresponds hcl hs hJ hc)

/-- **`lem:corresponding_K` (i) ⇒ (ii), one inclusion**: `ψ(K⁻(p) ∩ J⁺(S)) ⊆ K⁻(q) ∩ J⁺(ψ S)`
for corresponding `p`, `q`. The case `p` BTZ, `q` regular is impossible (the paper: "`I⁻(p)` is
empty if and only if `I⁻(q)` is"), by the strict step from `q`'s side. -/
theorem image_Kminus_subset [FirstCountableTopology M] [FirstCountableTopology N]
    (h : IsCorrPair C D U V ψ g) {S SingM : Set M} {SingN : Set N} (hM : KSide C S SingM)
    (hN : KSide D (ψ '' S) SingN) (hcvM : C.CausallyConvexIn (U : Set M) ⊤)
    (hcvN : D.CausallyConvexIn (V : Set N) ⊤) (hSU : S ⊆ U) {p : M} {q : N}
    (hp : p ∈ frontier (U : Set M)) (hq : q ∈ frontier (V : Set N))
    (hqS : q ∈ D.Jplus ⊤ (ψ '' S)) (hc : Corresponds (U : Set M) ψ p q) :
    ψ '' (C.Kminus ⊤ {p} ∩ C.Jplus ⊤ S) ⊆ D.Kminus ⊤ {q} ∩ D.Jplus ⊤ (ψ '' S) := by
  have hpU : p ∈ closure (U : Set M) := frontier_subset_closure hp
  have hqV : q ∈ closure (V : Set N) := frontier_subset_closure hq
  have hqnV : q ∉ (V : Set N) := by rw [V.isOpen.frontier_eq] at hq; exact hq.2
  have hSV : ψ '' S ⊆ V := (h.mapsTo.mono_left hSU).image_subset
  have hpass := Causality.Kminus_inter_Jplus_subset_of_causallyConvexIn hcvM hSU hpU
  have hpassN := Causality.Kminus_inter_Jplus_subset_of_causallyConvexIn hcvN hSV hqV
  rintro _ ⟨x, ⟨hxK, hxJ⟩, rfl⟩
  have hxU : x ∈ U := hpass ⟨hxK, hxJ⟩
  obtain ⟨σ, hσ, hσx⟩ := hxJ
  have hψJ : ψ x ∈ D.Jplus ⊤ (ψ '' S) :=
    ⟨ψ σ, mem_image_of_mem ψ hσ, (h.le_iff σ (hSU hσ) x hxU).1 hσx⟩
  refine ⟨?_, hψJ⟩
  by_cases hqs : q ∈ SingN
  · rw [hN.Kminus_sing q hqs]
    refine ⟨?_, fun he => hqnV ?_⟩
    · rw [Precausality.mem_Jminus_singleton]
      exact h.le_of_corresponds (hN.isClosed_Jplus _) hxU
        (Causality.Jplus_mem_nhds_of_mem_Kminus hxK) hc
    · rw [mem_singleton_iff] at he; rw [← he]; exact h.mapsTo hxU
  · rw [hN.Kminus_reg q hqs, Precausality.mem_Iminus_singleton]
    by_cases hps : p ∈ SingM
    · exfalso
      have hqSN : q ∉ ψ '' S := fun hm => hqnV (hSV hm)
      obtain ⟨y, hyI, hyJ⟩ := hN.mem_Zminus q hqs _ (hN.separates q ⟨hqS, hqSN⟩)
      have hyq : D.lt ⊤ y q := by simpa using hyI
      obtain ⟨s', hys', hs'q⟩ := Causality.exists_lt_lt_of_mem_Zminus (hN.mem_Zminus q hqs) hyq
      have hyV : y ∈ V := hpassN ⟨by rw [hN.Kminus_reg q hqs]; exact hyI, hyJ⟩
      obtain ⟨σ', hσ', hσ'y⟩ := hyJ
      have hs'V : s' ∈ V := hpassN ⟨by rw [hN.Kminus_reg q hqs]; simpa using hs'q,
        σ', hσ', D.le_trans hσ'y (D.le_of_lt hys')⟩
      have hlt := h.symm.lt_of_corresponds hM.pushUp (hM.isClosed_Jplus _) hyV hs'V hys'
        (Causality.Jplus_mem_nhds_of_lt hs'q) (h.corresponds_symm hc)
      have hgy : g y ∈ C.Iminus ⊤ {p} := by simpa using hlt
      rw [hM.Iminus_sing p hps] at hgy
      exact hgy
    · have hxp : C.lt ⊤ x p := by
        rw [hM.Kminus_reg p hps, Precausality.mem_Iminus_singleton] at hxK; exact hxK
      obtain ⟨s, hxs, hsp⟩ := Causality.exists_lt_lt_of_mem_Zminus (hM.mem_Zminus p hps) hxp
      have hsK : s ∈ C.Kminus ⊤ {p} := by
        rw [hM.Kminus_reg p hps, Precausality.mem_Iminus_singleton]; exact hsp
      have hsU : s ∈ U := hpass ⟨hsK, σ, hσ, C.le_trans hσx (C.le_of_lt hxs)⟩
      exact h.lt_of_corresponds hN.pushUp (hN.isClosed_Jplus _) hxU hsU hxs
        (Causality.Jplus_mem_nhds_of_lt hsp) hc

/-- **`lem:corresponding_K` (i) ⇒ (ii)**: corresponding points have `ψ(K⁻(p) ∩ J⁺(S)) =
K⁻(q) ∩ J⁺(ψ S)` (`ψ` injective on `U`, so `ψ` induces the bijection of the paper). -/
theorem image_Kminus_eq [FirstCountableTopology M] [FirstCountableTopology N]
    (h : IsCorrPair C D U V ψ g) {S SingM : Set M} {SingN : Set N} (hM : KSide C S SingM)
    (hN : KSide D (ψ '' S) SingN) (hcvM : C.CausallyConvexIn (U : Set M) ⊤)
    (hcvN : D.CausallyConvexIn (V : Set N) ⊤) (hSU : S ⊆ U) {p : M} {q : N}
    (hp : p ∈ frontier (U : Set M)) (hq : q ∈ frontier (V : Set N))
    (hpS : p ∈ C.Jplus ⊤ S) (hqS : q ∈ D.Jplus ⊤ (ψ '' S))
    (hc : Corresponds (U : Set M) ψ p q) :
    ψ '' (C.Kminus ⊤ {p} ∩ C.Jplus ⊤ S) = D.Kminus ⊤ {q} ∩ D.Jplus ⊤ (ψ '' S) := by
  refine (h.image_Kminus_subset hM hN hcvM hcvN hSU hp hq hqS hc).antisymm ?_
  have hSV : ψ '' S ⊆ V := (h.mapsTo.mono_left hSU).image_subset
  have hgS : g '' (ψ '' S) = S := h.leftInvOn.image_image' hSU
  have hM' : KSide C (g '' (ψ '' S)) SingM := by rw [hgS]; exact hM
  have hpS' : p ∈ C.Jplus ⊤ (g '' (ψ '' S)) := by rw [hgS]; exact hpS
  have hsub := h.symm.image_Kminus_subset hN hM' hcvN hcvM hSV hq hp hpS'
    (h.corresponds_symm hc)
  rw [hgS] at hsub
  have hpassN := Causality.Kminus_inter_Jplus_subset_of_causallyConvexIn hcvN hSV
    (frontier_subset_closure hq)
  rintro y ⟨hyK, hyJ⟩
  have hyV : y ∈ V := hpassN ⟨hyK, hyJ⟩
  exact ⟨g y, hsub ⟨y, ⟨hyK, hyJ⟩, rfl⟩, h.rightInvOn hyV⟩

/-- Two points of `∂V ∩ J⁺(ψ S)` corresponding to the same `p` are equal (Sbierski Prop 3.7, "at
most one corresponding boundary point"; `cor:model_corresponding`, first half), through
`cor:K_ordre_Sigma`. -/
theorem eq_of_corresponds [FirstCountableTopology M] [FirstCountableTopology N]
    (h : IsCorrPair C D U V ψ g) {S SingM : Set M} {SingN : Set N} (hM : KSide C S SingM)
    (hN : KSide D (ψ '' S) SingN) (hcvM : C.CausallyConvexIn (U : Set M) ⊤)
    (hcvN : D.CausallyConvexIn (V : Set N) ⊤) (hSU : S ⊆ U) {p : M} {q q' : N}
    (hp : p ∈ frontier (U : Set M)) (hq : q ∈ frontier (V : Set N))
    (hq' : q' ∈ frontier (V : Set N)) (hpS : p ∈ C.Jplus ⊤ S) (hqS : q ∈ D.Jplus ⊤ (ψ '' S))
    (hq'S : q' ∈ D.Jplus ⊤ (ψ '' S)) (hc : Corresponds (U : Set M) ψ p q)
    (hc' : Corresponds (U : Set M) ψ p q') : q = q' := by
  have e := h.image_Kminus_eq hM hN hcvM hcvN hSU hp hq hpS hqS hc
  have e' := h.image_Kminus_eq hM hN hcvM hcvN hSU hp hq' hpS hq'S hc'
  rw [e] at e'
  have hSV : ψ '' S ⊆ V := (h.mapsTo.mono_left hSU).image_subset
  have hnV : ∀ {r : N}, r ∈ frontier (V : Set N) → r ∉ ψ '' S := fun hr hm => by
    rw [V.isOpen.frontier_eq] at hr; exact hr.2 (hSV hm)
  exact hN.causal
    (Causality.le_of_Kminus_inter_subset hN.isClosed_Jminus hN.dense hN.separates
      ⟨hqS, hnV hq⟩ e'.subset)
    (Causality.le_of_Kminus_inter_subset hN.isClosed_Jminus hN.dense hN.separates
      ⟨hq'S, hnV hq'⟩ e'.symm.subset)

/-- `lem:corresponding_K` (`ETT.tex:2100`), the future side, model-free: for
`p ∈ ∂U ∩ J⁺(S)` and `q ∈ ∂V ∩ J⁺(ψ S)`, `p` and `q` correspond iff `ψ` maps `K⁻(p) ∩ J⁺(S)` onto
`K⁻(q) ∩ J⁺(ψ S)`. (ii) ⇒ (i) by a cluster point `q'` of `ψ` along `K⁻(p) ∩ J⁺(S)` in the compact
`J⁺(ψ S) ∩ J⁻(q)`, then (i) ⇒ (ii) at `q'` and `cor:K_ordre_Sigma` (the paper's route, with a
cluster point in place of its "increasing and bounded above, so it converges"). -/
theorem corresponding_K [FirstCountableTopology M] [FirstCountableTopology N] [T2Space M]
    (h : IsCorrPair C D U V ψ g) {S SingM : Set M} {SingN : Set N} (hM : KSide C S SingM)
    (hN : KSide D (ψ '' S) SingN) (hcvM : C.CausallyConvexIn (U : Set M) ⊤)
    (hcvN : D.CausallyConvexIn (V : Set N) ⊤) (hSU : S ⊆ U) {p : M} {q : N}
    (hp : p ∈ frontier (U : Set M)) (hq : q ∈ frontier (V : Set N))
    (hpS : p ∈ C.Jplus ⊤ S) (hqS : q ∈ D.Jplus ⊤ (ψ '' S)) :
    Corresponds (U : Set M) ψ p q ↔
      ψ '' (C.Kminus ⊤ {p} ∩ C.Jplus ⊤ S) = D.Kminus ⊤ {q} ∩ D.Jplus ⊤ (ψ '' S) := by
  refine ⟨h.image_Kminus_eq hM hN hcvM hcvN hSU hp hq hpS hqS, fun heq => ?_⟩
  have hpnU : p ∉ (U : Set M) := by rw [U.isOpen.frontier_eq] at hp; exact hp.2
  have hpass := Causality.Kminus_inter_Jplus_subset_of_causallyConvexIn hcvM hSU
    (frontier_subset_closure hp)
  have hpA : p ∈ closure (C.Kminus ⊤ {p} ∩ C.Jplus ⊤ S) := by
    have hxN := hM.separates p ⟨hpS, fun hm => hpnU (hSU hm)⟩
    have hxK : p ∈ closure (C.Kminus ⊤ {p}) :=
      hM.dense p (by simpa using C.le_refl (U := ⊤) (x := p) trivial)
    rw [mem_closure_iff_nhds] at hxK ⊢
    intro O hO
    obtain ⟨z, ⟨hzO, hzS⟩, hzK⟩ := hxK (O ∩ C.Jplus ⊤ S) (inter_mem hO hxN)
    exact ⟨z, hzO, hzK, hzS⟩
  haveI : NeBot (𝓝[C.Kminus ⊤ {p} ∩ C.Jplus ⊤ S] p) := mem_closure_iff_nhdsWithin_neBot.1 hpA
  have hle : map ψ (𝓝[C.Kminus ⊤ {p} ∩ C.Jplus ⊤ S] p) ≤
      𝓟 (D.Jplus ⊤ (ψ '' S) ∩ D.Jminus ⊤ {q}) := by
    rw [le_principal_iff, mem_map]
    refine mem_of_superset self_mem_nhdsWithin fun x hx => ?_
    have hx' : ψ x ∈ D.Kminus ⊤ {q} ∩ D.Jplus ⊤ (ψ '' S) := heq ▸ mem_image_of_mem ψ hx
    exact ⟨hx'.2, Causality.Kminus_subset_Jminus hx'.1⟩
  obtain ⟨q', hq'K, hcl⟩ := hN.isCompact q hle
  have hc' : Corresponds (U : Set M) ψ p q' :=
    corresponds_iff_mapClusterPt.2 (MapClusterPt.mono hcl (nhdsWithin_mono p hpass))
  have hq' : q' ∈ frontier (V : Set N) := h.mem_frontier_of_corresponds hp hc'
  have e' := h.image_Kminus_eq hM hN hcvM hcvN hSU hp hq' hpS hq'K.1 hc'
  rw [heq] at e'
  have hSV : ψ '' S ⊆ V := (h.mapsTo.mono_left hSU).image_subset
  have hnV : ∀ {r : N}, r ∈ frontier (V : Set N) → r ∉ ψ '' S := fun hr hm => by
    rw [V.isOpen.frontier_eq] at hr; exact hr.2 (hSV hm)
  have e : q = q' := hN.causal
    (Causality.le_of_Kminus_inter_subset hN.isClosed_Jminus hN.dense hN.separates
      ⟨hqS, hnV hq⟩ e'.subset)
    (Causality.le_of_Kminus_inter_subset hN.isClosed_Jminus hN.dense hN.separates
      ⟨hq'K.1, hnV hq'⟩ e'.symm.subset)
  rw [e]; exact hc'

/-- **`lem:corresponding_K` (`ETT.tex:2100`) with (ii) in the paper's literal form**: "`f`
induces a bijection `K⁻(p) ∩ J⁺(Σ₁) → K⁻(q) ∩ J⁺(Σ₂)`" — the domain lies in `U`, where `f = ψ` is
defined (`lem:passe_pgcd`, `Kminus_inter_Jplus_subset_of_causallyConvexIn`), and `ψ` is a
bijection between the two sets (`InjOn` from the inverse `g`). Equivalent to
`IsCorrPair.corresponding_K`'s image equality. -/
theorem corresponding_K_bijOn [FirstCountableTopology M] [FirstCountableTopology N] [T2Space M]
    (h : IsCorrPair C D U V ψ g) {S SingM : Set M} {SingN : Set N} (hM : KSide C S SingM)
    (hN : KSide D (ψ '' S) SingN) (hcvM : C.CausallyConvexIn (U : Set M) ⊤)
    (hcvN : D.CausallyConvexIn (V : Set N) ⊤) (hSU : S ⊆ U) {p : M} {q : N}
    (hp : p ∈ frontier (U : Set M)) (hq : q ∈ frontier (V : Set N))
    (hpS : p ∈ C.Jplus ⊤ S) (hqS : q ∈ D.Jplus ⊤ (ψ '' S)) :
    Corresponds (U : Set M) ψ p q ↔
      C.Kminus ⊤ {p} ∩ C.Jplus ⊤ S ⊆ U ∧
        BijOn ψ (C.Kminus ⊤ {p} ∩ C.Jplus ⊤ S) (D.Kminus ⊤ {q} ∩ D.Jplus ⊤ (ψ '' S)) := by
  have hpass := Causality.Kminus_inter_Jplus_subset_of_causallyConvexIn hcvM hSU
    (frontier_subset_closure hp)
  rw [h.corresponding_K hM hN hcvM hcvN hSU hp hq hpS hqS]
  constructor
  · intro heq
    refine ⟨hpass, ?_⟩
    rw [← heq]
    exact (h.leftInvOn.injOn.mono hpass).bijOn_image
  · rintro ⟨-, hb⟩
    exact hb.image_eq

/-- `ψ`, read on the subtype `U`, is an open embedding (the bridge to `Gluing`, kb/0001: the
subtype appears in this lemma and in `corresponds_iff_mem_gluingC` only, never in a statement
about the spacetimes). -/
theorem isOpenEmbedding_comp_val (h : IsCorrPair C D U V ψ g) :
    IsOpenEmbedding (ψ ∘ (Subtype.val : U → M)) := by
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap
    (h.continuousOn.comp_continuous continuous_subtype_val fun x => x.2)
    (fun a b hab => Subtype.ext (h.leftInvOn.injOn a.2 b.2 hab)) ?_
  intro W hW
  obtain ⟨W', hW', rfl⟩ := isOpen_induced_iff.1 hW
  have he : (ψ ∘ (Subtype.val : U → M)) '' (Subtype.val ⁻¹' W') = (V : Set N) ∩ g ⁻¹' W' := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨h.mapsTo x.2, ?_⟩
      show g (ψ x.1) ∈ W'
      rw [h.leftInvOn x.2]; exact hx
    · rintro ⟨hyV, hyW⟩
      exact ⟨⟨g y, h.mapsTo_inv hyV⟩, hyW, h.rightInvOn hyV⟩
  rw [he]
  exact h.continuousOn_inv.isOpen_inter_preimage V.isOpen hW'

/-- **ETT's `C` is Sbierski's Def 3.5** (`rem:non_separe_cas`, `ETT.tex:2016`; the set `C` of the
proof of `lem:corresponding_K`): `p`, `q` correspond iff their images in the gluing
`(M ⊔ N)/U` (`Gluing`, identifying `x ∈ U` with `ψ x`) are not separated — the paper's
`(p, q) ∈ C` with `j₁` the inclusion of `U` and `j₂ = ψ` on `U` (`Gluing.C_eq_closure`). -/
theorem corresponds_iff_mem_gluingC (h : IsCorrPair C D U V ψ g) {p : M} {q : N} :
    Corresponds (U : Set M) ψ p q ↔
      (p, q) ∈ Gluing.C (Subtype.val : U → M) (ψ ∘ (Subtype.val : U → M)) := by
  have hC : Gluing.C (Subtype.val : U → M) (ψ ∘ (Subtype.val : U → M)) =
      closure (Gluing.graph (Subtype.val : U → M) (ψ ∘ (Subtype.val : U → M))) :=
    Gluing.C_eq_closure U.isOpen.isOpenEmbedding_subtypeVal h.isOpenEmbedding_comp_val
  rw [hC, mem_closure_iff_nhds]
  constructor
  · intro hc o ho
    obtain ⟨O, hO, O', hO', hsub⟩ := mem_nhds_prod_iff.1 ho
    obtain ⟨x, hxU, hxO, hψ⟩ := hc O hO O' hO'
    exact ⟨(x, ψ x), hsub ⟨hxO, hψ⟩, ⟨x, hxU⟩, rfl⟩
  · intro hc O hO O' hO'
    obtain ⟨_, ⟨hxO, hψ⟩, ⟨x, hxU⟩, rfl⟩ := hc _ (prod_mem_nhds hO hO')
    exact ⟨x, hxU, hxO, hψ⟩

end IsCorrPair

/-- **Sbierski Prop 3.7 (iii) ⇒ (i)**, model-free: if some `γ`, converging to `p` inside `U` along a
non-trivial filter (a curve `(−ε, 0) → U` with `γ(s) → p` as `s ↗ 0`), has `ψ ∘ γ → q`, then `p` and
`q` correspond. -/
theorem corresponds_of_tendsto {U : Set M} {ψ : M → N} {p : M} {q : N} {ι : Type*} {F : Filter ι}
    [NeBot F] {γ : ι → M} (hγ : Tendsto γ F (𝓝[U] p)) (hψγ : Tendsto (ψ ∘ γ) F (𝓝 q)) :
    Corresponds U ψ p q := by
  intro O hO O' hO'
  have h1 : ∀ᶠ i in F, γ i ∈ U ∩ O := hγ (inter_mem_nhdsWithin U hO)
  have h2 : ∀ᶠ i in F, ψ (γ i) ∈ O' := hψγ hO'
  have hev : ∀ᶠ i in F, γ i ∈ U ∩ O ∧ ψ (γ i) ∈ O' := h1.and h2
  obtain ⟨i, ⟨hU, hO⟩, hO'⟩ := hev.exists
  exact ⟨γ i, hU, hO, hO'⟩

/-- **`lem:corresponding_K` (`ETT.tex:2100`), the past side, model-free**: the future statement for
the time-reversed causalities, under the past-side `K`-calculus (`K⁺ = I⁺` everywhere, the
hypotheses of `KSide C.dual S ∅`). For corresponding `p ∈ ∂U ∩ J⁻(S)`, `q ∈ ∂V ∩ J⁻(ψ S)`:
`ψ(K⁺(p) ∩ J⁻(S)) = K⁺(q) ∩ J⁻(ψ S)`, and conversely. -/
theorem IsCorrPair.corresponding_K_past [FirstCountableTopology M] [FirstCountableTopology N]
    [T2Space M] (h : IsCorrPair C D U V ψ g) {S : Set M} (hM : KSide C.dual S ∅)
    (hN : KSide D.dual (ψ '' S) ∅) (hcvM : C.CausallyConvexIn (U : Set M) ⊤)
    (hcvN : D.CausallyConvexIn (V : Set N) ⊤) (hSU : S ⊆ U) {p : M} {q : N}
    (hp : p ∈ frontier (U : Set M)) (hq : q ∈ frontier (V : Set N))
    (hpS : p ∈ C.Jminus ⊤ S) (hqS : q ∈ D.Jminus ⊤ (ψ '' S)) :
    Corresponds (U : Set M) ψ p q ↔
      ψ '' (C.Kplus ⊤ {p} ∩ C.Jminus ⊤ S) = D.Kplus ⊤ {q} ∩ D.Jminus ⊤ (ψ '' S) :=
  h.dual.corresponding_K hM hN (Causality.dual_causallyConvexIn.2 hcvM)
    (Causality.dual_causallyConvexIn.2 hcvN) hSU hp hq hpS hqS

/-- `lem:corresponding_K`, past side, with (ii) in the paper's literal form (`K⁺(p) ∩ J⁻(S) ⊆ U`
and `ψ` a bijection onto `K⁺(q) ∩ J⁻(ψ S)`). -/
theorem IsCorrPair.corresponding_K_past_bijOn [FirstCountableTopology M]
    [FirstCountableTopology N] [T2Space M] (h : IsCorrPair C D U V ψ g) {S : Set M}
    (hM : KSide C.dual S ∅) (hN : KSide D.dual (ψ '' S) ∅)
    (hcvM : C.CausallyConvexIn (U : Set M) ⊤) (hcvN : D.CausallyConvexIn (V : Set N) ⊤)
    (hSU : S ⊆ U) {p : M} {q : N} (hp : p ∈ frontier (U : Set M))
    (hq : q ∈ frontier (V : Set N)) (hpS : p ∈ C.Jminus ⊤ S) (hqS : q ∈ D.Jminus ⊤ (ψ '' S)) :
    Corresponds (U : Set M) ψ p q ↔
      C.Kplus ⊤ {p} ∩ C.Jminus ⊤ S ⊆ U ∧
        BijOn ψ (C.Kplus ⊤ {p} ∩ C.Jminus ⊤ S) (D.Kplus ⊤ {q} ∩ D.Jminus ⊤ (ψ '' S)) :=
  h.dual.corresponding_K_bijOn hM hN (Causality.dual_causallyConvexIn.2 hcvM)
    (Causality.dual_causallyConvexIn.2 hcvN) hSU hp hq hpS hqS

end Core

/-! ### Witness: the hypotheses of the model-free core are jointly satisfiable -/

section Witness

/-- The half-line `]-∞, 1[` as an open set of the timelike line. -/
def iioOne : Opens ℝ := ⟨Iio 1, isOpen_Iio⟩

/-- `I⁻(x) = ]-∞, x[` on the timelike line (the `J^±` forms are `Causal/Geroch.lean:575–578`). -/
theorem timelikeLine_Iminus_singleton (x : ℝ) : timelikeLine.Iminus ⊤ {x} = Iio x := by
  ext y; simp

/-- The future `K`-calculus of the timelike line, with `S = {0}` and no singular point. -/
theorem timelikeLine_kSide : KSide timelikeLine {0} ∅ where
  pushUp := timelikeLine_pushUp
  causal := timelikeLine_isCausal
  isClosed_Jplus x := by rw [timelikeLine_Jplus_top_singleton]; exact isClosed_Ici
  isClosed_Jminus x := by rw [timelikeLine_Jminus_top_singleton]; exact isClosed_Iic
  Kminus_reg x _ := timelikeLine_pushUp.Kminus_eq_Iminus (timelikeLine_mem_Zminus x)
  mem_Zminus x _ := timelikeLine_mem_Zminus x
  Kminus_sing x hx := absurd hx (notMem_empty x)
  Iminus_sing x hx := absurd hx (notMem_empty x)
  dense x := by
    rw [timelikeLine_pushUp.Kminus_eq_Iminus (timelikeLine_mem_Zminus x),
      timelikeLine_Jminus_top_singleton, timelikeLine_Iminus_singleton, closure_Iio]
  separates y hy := by
    rw [timelikeLine_Jplus_top_singleton] at hy ⊢
    exact Ici_mem_nhds (lt_of_le_of_ne hy.1 (Ne.symm hy.2))
  isCompact x := by rw [timelikeLine_Jplus_zero_inter]; exact isCompact_Icc

theorem timelikeLine_isCorrPair_id : IsCorrPair timelikeLine timelikeLine iioOne iioOne id id where
  mapsTo := mapsTo_id _
  mapsTo_inv := mapsTo_id _
  leftInvOn := leftInvOn_id _
  rightInvOn := leftInvOn_id _
  continuousOn := continuousOn_id
  continuousOn_inv := continuousOn_id
  le_iff _ _ _ _ := Iff.rfl
  lt_iff _ _ _ _ := Iff.rfl

theorem timelikeLine_causallyConvexIn_iioOne :
    timelikeLine.CausallyConvexIn (iioOne : Set ℝ) ⊤ := by
  refine ⟨fun _ _ => trivial, fun a _ b hb z hz => ?_⟩
  rw [Causality.mem_diamond, timelikeLine_le, timelikeLine_le] at hz
  exact lt_of_le_of_lt hz.2.1 hb

theorem timelikeLine_corresponds_one : Corresponds (iioOne : Set ℝ) id (1 : ℝ) 1 := by
  haveI : NeBot (𝓝[(iioOne : Set ℝ)] (1 : ℝ)) := (inferInstance : NeBot (𝓝[<] (1 : ℝ)))
  exact corresponds_of_tendsto (γ := id) tendsto_id
    (tendsto_id.mono_left nhdsWithin_le_nhds)

/-- **The hypotheses of `IsCorrPair.corresponding_K` are jointly satisfiable, with a genuine
corresponding pair** (kb/0011): the timelike line, `U = V = ]-∞, 1[`, `ψ = g = id`, `S = {0}`,
`p = q = 1`, no singular point; both sides of the equivalence hold. -/
theorem timelikeLine_corresponding_hypotheses :
    IsCorrPair timelikeLine timelikeLine iioOne iioOne id id ∧
      KSide timelikeLine {0} ∅ ∧ KSide timelikeLine (id '' {0}) ∅ ∧
      timelikeLine.CausallyConvexIn (iioOne : Set ℝ) ⊤ ∧ ({0} : Set ℝ) ⊆ iioOne ∧
      (1 : ℝ) ∈ frontier (iioOne : Set ℝ) ∧ (1 : ℝ) ∈ timelikeLine.Jplus ⊤ {0} ∧
      (1 : ℝ) ∈ timelikeLine.Jplus ⊤ (id '' {0}) ∧ Corresponds (iioOne : Set ℝ) id (1 : ℝ) 1 ∧
      id '' (timelikeLine.Kminus ⊤ {(1 : ℝ)} ∩ timelikeLine.Jplus ⊤ {0}) =
        timelikeLine.Kminus ⊤ {(1 : ℝ)} ∩ timelikeLine.Jplus ⊤ (id '' {0}) := by
  have hK' : KSide timelikeLine (id '' {(0 : ℝ)}) ∅ := by rw [image_id]; exact timelikeLine_kSide
  have hfr : (1 : ℝ) ∈ frontier (iioOne : Set ℝ) := by
    show (1 : ℝ) ∈ frontier (Iio (1 : ℝ)); rw [frontier_Iio]; rfl
  have hsub : ({0} : Set ℝ) ⊆ iioOne := by
    rintro _ rfl; show (0 : ℝ) < 1; norm_num
  have h1 : (1 : ℝ) ∈ timelikeLine.Jplus ⊤ {0} := by
    rw [timelikeLine_Jplus_top_singleton]; norm_num
  have h1' : (1 : ℝ) ∈ timelikeLine.Jplus ⊤ (id '' {0}) := by rw [image_id]; exact h1
  refine ⟨timelikeLine_isCorrPair_id, timelikeLine_kSide, hK', timelikeLine_causallyConvexIn_iioOne,
    hsub, hfr, h1, h1', timelikeLine_corresponds_one, ?_⟩
  exact (timelikeLine_isCorrPair_id.corresponding_K timelikeLine_kSide hK'
    timelikeLine_causallyConvexIn_iioOne timelikeLine_causallyConvexIn_iioOne hsub hfr hfr h1
    h1').1 timelikeLine_corresponds_one

/-! The BTZ branch: the lightlike line, every point singular (`Sing = univ`, `I⁻(x) = ∅`,
`K⁻(x) = J⁻(x) ∖ {x}`, `lightlikeLine_K`), so `KSide.Kminus_sing`/`Iminus_sing` are exercised
together with every other field, at `p = q` both BTZ. -/

theorem lightlikeLine_Jplus_singleton (x : ℝ) : lightlikeLine.Jplus ⊤ {x} = Ici x := by
  ext y; simp

theorem lightlikeLine_Jminus_singleton (x : ℝ) : lightlikeLine.Jminus ⊤ {x} = Iic x := by
  ext y; simp

theorem lightlikeLine_Iminus_singleton (x : ℝ) : lightlikeLine.Iminus ⊤ {x} = ∅ := by
  ext y; simp

/-- The future `K`-calculus of the lightlike line, with `S = {0}` and every point BTZ. -/
theorem lightlikeLine_kSide : KSide lightlikeLine {0} univ where
  pushUp := lightlikeLine_pushUp
  causal := lightlikeLine_isCausal
  isClosed_Jplus x := by rw [lightlikeLine_Jplus_singleton]; exact isClosed_Ici
  isClosed_Jminus x := by rw [lightlikeLine_Jminus_singleton]; exact isClosed_Iic
  Kminus_reg x hx := absurd (mem_univ x) hx
  mem_Zminus x hx := absurd (mem_univ x) hx
  Kminus_sing x _ :=
    Causality.Kminus_eq_Jminus_diff lightlikeLine_isCausal (lightlikeLine_singularPastAt x).1
  Iminus_sing x _ := lightlikeLine_Iminus_singleton x
  dense x := by
    rw [(lightlikeLine_K x).1, lightlikeLine_Jminus_singleton, closure_Iio]
  separates y hy := by
    rw [lightlikeLine_Jplus_singleton] at hy ⊢
    exact Ici_mem_nhds (lt_of_le_of_ne hy.1 (Ne.symm hy.2))
  isCompact x := by
    rw [lightlikeLine_Jplus_singleton, lightlikeLine_Jminus_singleton, Ici_inter_Iic]
    exact isCompact_Icc

theorem lightlikeLine_isCorrPair_id :
    IsCorrPair lightlikeLine lightlikeLine iioOne iioOne id id where
  mapsTo := mapsTo_id _
  mapsTo_inv := mapsTo_id _
  leftInvOn := leftInvOn_id _
  rightInvOn := leftInvOn_id _
  continuousOn := continuousOn_id
  continuousOn_inv := continuousOn_id
  le_iff _ _ _ _ := Iff.rfl
  lt_iff _ _ _ _ := Iff.rfl

theorem lightlikeLine_causallyConvexIn_iioOne :
    lightlikeLine.CausallyConvexIn (iioOne : Set ℝ) ⊤ := by
  refine ⟨fun _ _ => trivial, fun a _ b hb z hz => ?_⟩
  rw [Causality.mem_diamond, lightlikeLine_le_top, lightlikeLine_le_top] at hz
  exact lt_of_le_of_lt hz.2 hb

/-- **The hypotheses of `IsCorrPair.corresponding_K` are jointly satisfiable with a nonempty
singular set** (kb/0011): the lightlike line, `U = V = ]-∞, 1[`, `ψ = g = id`, `S = {0}`,
`Sing = univ`, `p = q = 1` both BTZ (`I⁻(1) = ∅`); both sides of the equivalence hold. -/
theorem lightlikeLine_corresponding_hypotheses :
    IsCorrPair lightlikeLine lightlikeLine iioOne iioOne id id ∧
      KSide lightlikeLine {0} univ ∧ KSide lightlikeLine (id '' {0}) univ ∧
      lightlikeLine.CausallyConvexIn (iioOne : Set ℝ) ⊤ ∧ ({0} : Set ℝ) ⊆ iioOne ∧
      (1 : ℝ) ∈ frontier (iioOne : Set ℝ) ∧ (1 : ℝ) ∈ lightlikeLine.Jplus ⊤ {0} ∧
      (1 : ℝ) ∈ lightlikeLine.Jplus ⊤ (id '' {0}) ∧ lightlikeLine.Iminus ⊤ {(1 : ℝ)} = ∅ ∧
      Corresponds (iioOne : Set ℝ) id (1 : ℝ) 1 ∧
      id '' (lightlikeLine.Kminus ⊤ {(1 : ℝ)} ∩ lightlikeLine.Jplus ⊤ {0}) =
        lightlikeLine.Kminus ⊤ {(1 : ℝ)} ∩ lightlikeLine.Jplus ⊤ (id '' {0}) := by
  have hK' : KSide lightlikeLine (id '' {(0 : ℝ)}) univ := by
    rw [image_id]; exact lightlikeLine_kSide
  have hfr : (1 : ℝ) ∈ frontier (iioOne : Set ℝ) := by
    show (1 : ℝ) ∈ frontier (Iio (1 : ℝ)); rw [frontier_Iio]; rfl
  have hsub : ({0} : Set ℝ) ⊆ iioOne := by
    rintro _ rfl; show (0 : ℝ) < 1; norm_num
  have h1 : (1 : ℝ) ∈ lightlikeLine.Jplus ⊤ {0} := by
    rw [lightlikeLine_Jplus_singleton]; norm_num
  have h1' : (1 : ℝ) ∈ lightlikeLine.Jplus ⊤ (id '' {0}) := by rw [image_id]; exact h1
  refine ⟨lightlikeLine_isCorrPair_id, lightlikeLine_kSide, hK',
    lightlikeLine_causallyConvexIn_iioOne, hsub, hfr, h1, h1', lightlikeLine_Iminus_singleton 1,
    timelikeLine_corresponds_one, ?_⟩
  exact (lightlikeLine_isCorrPair_id.corresponding_K lightlikeLine_kSide hK'
    lightlikeLine_causallyConvexIn_iioOne lightlikeLine_causallyConvexIn_iioOne hsub hfr hfr h1
    h1').1 timelikeLine_corresponds_one

end Witness

end CBG

end Causal
