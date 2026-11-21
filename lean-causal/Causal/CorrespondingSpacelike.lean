import Causal.CorrespondingPoints

/-!
# Spacelike corresponding boundary points, model-free: (3.10), Sbierski Lemma 3.11, Lemma 3.9's core

ETT layer (`programme/roadmap.toml` T-abs-hoist-cbg-cores; no paper label): the model-free core of
`Causal.CBG.NoCorresponding` (package 6, `docs/CBG-DESIGN.md` §3 step 4), moved here verbatim,
same full names and statements, so that a layer-1 module may use it. This module imports
`Causal.CorrespondingPoints` only: no model, directly or transitively, and no `Causal.CBG.*`
module. `Causal.CBG.NoCorresponding` imports it and keeps the Level A and the developments
(`CGHDData`, `IsCGHD`: Lemma 3.9 itself, Lemma 3.8's second half, Thm 3.6, Thm 3.13, the
gluing). **No label is marked** (DEC-60). Cited, unmarked: `prop:Cauchy_point_min` —
`ETT.tex:2270`, `prop:C_connexe` — `ETT.tex:2240`, `lem:passe_pgcd` — `ETT.tex:2042`,
`lem:Sigma_separe` — `ETT.tex:2062`, `prop:K_densite_sing` — `ETT.tex:1634`; Sbierski 1309.7591,
Lemma 3.9 (p. 17), Lemma 3.11 (p. 18).

> Lemma 3.9. Let $U$ be a CGHD of $M$ and $M'$ with isometric embedding $\psi$. Assume that
> $C\cap J^+(\iota(M))$ is non-empty. Then there exists a point $p\in C$ with the property
> $J^-(p)\cap\partial U\cap J^+(\iota(M))=\{p\}$ (3.10). (Sbierski, p. 17)

> Lemma 3.11. Let $U$ be a GHD of some initial data and $M\supseteq U$ an extension of $U$.
> Suppose that there exists a $p\in\partial U$ that satisfies (3.10). Then for every open
> neighbourhood $W$ of $p$ in $M$ there exists a point $q\in I^+(p)\subseteq M$ such that
> $J^-(q)\cap U^c\cap J^+(\iota(M))\subseteq W$. (Sbierski, p. 18)

> If $C\neq \emptyset$, then there exists $(p',q')\in C$ with
> $J_{M_1}(\Sigma_1,p')\setminus\{p'\}\subset j_1(N)$. (`prop:Cauchy_point_min`, `ETT.tex:2270–2273`)

> The set $C_1:=\left\{p\in \partial j_1(N) ~|~ \exists q,~(p,q)\in C\right\}$ is open in $\partial
> j_1(N)$, and $C$ is closed in $\partial j_1(N)\times \partial j_2(N)$. (`prop:C_connexe`,
> `ETT.tex:2241–2242`)

## What is proved (no `sorry` in this file)

* **Model-free** (namespace `Causality`, any causality, open sets, kb/0001):
  `mem_closure_of_mem_Jminus` (a point of `J⁻(p) ∩ J⁺(S)`, `p ∈ closure U`, is in `closure U`:
  `K⁻` density + `lem:passe_pgcd`), `spacelike_iff` (**(3.10) ⟺ ETT's `J(Σ, p) ∖ {p} ⊆ U`**),
  `exists_lt_Jminus_compl_subset` (**Sbierski Lemma 3.11**).
* **Model-free** (namespace `CBG`): `IsCorrPair.exists_corresponds_of_le` (the core of Lemma 3.9: a
  boundary point `q` with `K⁻(q) ⊆ K⁻(p₀)`, `p₀` corresponding, has a corresponding point),
  `isClosed_setOf_corresponds` (`prop:C_connexe`, second half, all corresponding pairs in `M × N`)
  and `isClosed_setOf_corresponds_frontier` (in ETT's `∂ × ∂`).
* **Witnesses**: `timelikeLine_spacelike_hypotheses` (Lemma 3.11), `timelikeLine_corrPair_hypotheses`
  (`exists_corresponds_of_le`, with a genuine corresponding pair).

## Hypothesis checklist

| paper | here |
|---|---|
| Lemma 3.9: `U` a CGHD, `C ∩ J⁺(ι(M)) ≠ ∅` | core only: `IsCorrPair`, `U` causally convex, `p₀` corresponding to `p₀'`, `q ∈ ∂U` with `K⁻(q) ⊆ K⁻(p₀)`, `J⁺(S)` a neighbourhood of `q`, `q ∈ closure K⁻(q)`, closed `J⁺(y)`, compact `J⁺(ψ S) ∩ J⁻(p₀')`. Lemma 3.9 itself (the minimal point, `CGHDData.exists_spacelike_corresponding`) stays in `Causal.CBG.NoCorresponding` |
| Lemma 3.9's proof: null geodesics in `∂U`, `C` open and closed along them, Lemma 3.8's embedding | ⚠ replaced: the `K⁻` cluster argument of `Causal.CorrespondingPoints` (`le_of_corresponds`); no geodesic, no time function, no openness of `C` |
| Lemma 3.11: `U` a GHD, `M ⊇ U`, `p ∈ ∂U` with (3.10), `W` an open neighbourhood | ✓ `W ∈ 𝓝 p` (any neighbourhood, ⚠ weakened); `p ∈ Z⁺`, `J^±(x)` closed, `J⁻(p) ⊆ closure K⁻(p)`, `lem:Sigma_separe`'s clause, compact `J⁺(S) ∩ J⁻(x)`, `U` causally convex; only `⊆` of (3.10) used |
| Lemma 3.11's proof: a timelike curve `γ` from `p`, "the relation `≤` is closed" | ⚠ replaced: the directed family `q ≫ p, q ≤ q₁` (`Z⁺`) and closed `J⁺(r)`; the final contradiction by `K⁻` density + `lem:passe_pgcd` instead of "contradicts the GH of `U`" |
| `prop:Cauchy_point_min`: ETT's form `J(Σ₁, p') ∖ {p'} ⊆ j₁(N)` | `spacelike_iff`: for `p ∈ ∂U`, (3.10) with `⊆ {p}` ⟺ `J⁺(S) ∩ J⁻(p) ∖ {p} ⊆ U`, reading `J(Σ, p) = J⁺(Σ) ∩ J⁻(p)` (the question of the past reading is `Causal.CBG.NoCorresponding`'s) |
| `prop:C_connexe`: "`C` is closed in `∂j₁(N) × ∂j₂(N)`" | ✓ `isClosed_setOf_corresponds_frontier` (the corresponding pairs in `∂U × ∂V`, any `V`) and `isClosed_setOf_corresponds` (reading: all corresponding pairs in `M × N`, the closure of the graph) |
| second countable | ⚠ weakened: first countable |

## SCOPE (disclosed)

* **Moved, not rewritten** (T-abs-hoist-cbg-cores, 2026-11-21): the namespace `Causality` block
  and the sections `Core` and `Witness` of `Causal.CBG.NoCorresponding`, byte for byte. The Level
  A forms stay there: `CGHDData.exists_spacelike_corresponding`/`_past` (Lemma 3.9),
  `exists_lt_Jminus_compl_subset_of_cauchy`/`exists_lt_Jplus_compl_subset_past` (Lemma 3.11 on
  admissible spacetimes, the past side with `p ∉ sing₀`), `correspondingExt`, Thm 3.6, Thm 3.13.
* Lemma 3.11 is stated on the future side, with `p ∈ Z⁺`. The past side is the Level A
  `exists_lt_Jplus_compl_subset_past`, which asks `p ∉ sing₀`: at a BTZ point `I⁻(p) = ∅`, so
  the conclusion `q ∈ I⁻(p)` is unsatisfiable there (`Causal.CBG.NoCorresponding`'s finding, R4).
* The witnesses cover the model-free Lemma 3.11 (`timelikeLine_spacelike_hypotheses`) and the
  core of Lemma 3.9 (`timelikeLine_corrPair_hypotheses`) on the timelike line (`U = ]-∞,1[`,
  `S = {0}`, `p = p₀ = 1`, `ψ = id`), regular case only. The second is **degenerate**
  (`q = p₀`, since `∂U = {1}` on the line): it shows joint satisfiability of the hypotheses but
  never exercises a boundary point `q ≠ p₀`; a 2-D local witness with `q < p₀` both on `∂U` is
  not given (kb/0011 asks a witness only when cheap).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set Topology Filter Function TopologicalSpace

universe u v

/-! ### Model-free lemmas -/

namespace Causality

variable {M : Type u} [TopologicalSpace M] {C : Causality M}

/-- **A point of `J⁻(p) ∩ J⁺(S)` is in `closure U`** for `p ∈ closure U`, `U` causally convex,
`S ⊆ U`: otherwise the open `(closure U)ᶜ ∩ J⁺(S)` around it (`lem:Sigma_separe`'s clause) meets
`K⁻(p)` (`prop:K_densite_sing`), and `K⁻(p) ∩ J⁺(S) ⊆ U` (`lem:passe_pgcd`). Sbierski's "this
contradicts the global hyperbolicity of `U`" (proofs of Lemmas 3.9, 3.11). -/
theorem mem_closure_of_mem_Jminus [FirstCountableTopology M] {U : Opens M}
    (hcvU : C.CausallyConvexIn (U : Set M) ⊤) {S : Set M} (hSU : S ⊆ U) {p : M}
    (hdense : C.Jminus ⊤ {p} ⊆ closure (C.Kminus ⊤ {p}))
    (hsep : ∀ y ∈ C.Jplus ⊤ S \ S, C.Jplus ⊤ S ∈ 𝓝 y) (hp : p ∈ closure (U : Set M)) {x : M}
    (hx : x ∈ C.Jminus ⊤ {p}) (hxS : x ∈ C.Jplus ⊤ S) : x ∈ closure (U : Set M) := by
  by_contra hxc
  have hxnS : x ∉ S := fun hm => hxc (subset_closure (hSU hm))
  have hN : (closure (U : Set M))ᶜ ∩ C.Jplus ⊤ S ∈ 𝓝 x :=
    inter_mem (isClosed_closure.isOpen_compl.mem_nhds hxc) (hsep x ⟨hxS, hxnS⟩)
  obtain ⟨r, ⟨hrc, hrS⟩, hrK⟩ := mem_closure_iff_nhds.1 (hdense hx) _ hN
  exact hrc (subset_closure (Kminus_inter_Jplus_subset_of_causallyConvexIn hcvU hSU hp ⟨hrK, hrS⟩))

/-- **Sbierski (3.10) ⟺ ETT's form** (`prop:Cauchy_point_min`, `ETT.tex:2272`): for `p ∈ ∂U`,
`J⁻(p) ∩ ∂U ∩ J⁺(S) ⊆ {p}` iff `J⁺(S) ∩ J⁻(p) ∖ {p} ⊆ U`. -/
theorem spacelike_iff [FirstCountableTopology M] {U : Opens M}
    (hcvU : C.CausallyConvexIn (U : Set M) ⊤) {S : Set M} (hSU : S ⊆ U) {p : M}
    (hdense : C.Jminus ⊤ {p} ⊆ closure (C.Kminus ⊤ {p}))
    (hsep : ∀ y ∈ C.Jplus ⊤ S \ S, C.Jplus ⊤ S ∈ 𝓝 y) (hp : p ∈ frontier (U : Set M)) :
    C.Jminus ⊤ {p} ∩ frontier (U : Set M) ∩ C.Jplus ⊤ S ⊆ {p} ↔
      (C.Jplus ⊤ S ∩ C.Jminus ⊤ {p}) \ {p} ⊆ U := by
  constructor
  · rintro h x ⟨⟨hxS, hxp⟩, hxne⟩
    by_contra hxU
    have hcl := mem_closure_of_mem_Jminus hcvU hSU hdense hsep (frontier_subset_closure hp) hxp hxS
    exact hxne (h ⟨⟨hxp, hcl, by rwa [U.isOpen.interior_eq]⟩, hxS⟩)
  · rintro h x ⟨⟨hxp, hxf⟩, hxS⟩
    by_contra hxne
    have hxU := h ⟨⟨hxS, hxp⟩, hxne⟩
    rw [U.isOpen.frontier_eq] at hxf
    exact hxf.2 hxU

/-- **Sbierski Lemma 3.11**, model-free: if `p ∈ ∂U` satisfies (3.10) (`⊆` suffices), then every
neighbourhood `W` of `p` contains `J⁻(q) ∩ Uᶜ ∩ J⁺(S)` for some `q ≫ p`. Proof: otherwise the
sets `J⁻(q) ∩ Uᶜ ∩ (interior W)ᶜ ∩ (J⁺(S) ∩ J⁻(q₁))`, `p ≪ q ≤ q₁`, are closed, non-empty,
directed (`p ∈ Z⁺`) in a compact set, so they share a point `r`; `r ≤ p` (`p` is a limit of such
`q`, `J⁺(r)` closed), `r ∉ U`, `r ≠ p`; by (3.10) `r ∉ ∂U`, against `mem_closure_of_mem_Jminus`. -/
theorem exists_lt_Jminus_compl_subset [T2Space M] [FirstCountableTopology M] {U : Opens M}
    (hcvU : C.CausallyConvexIn (U : Set M) ⊤) {S : Set M} (hSU : S ⊆ U) {p : M}
    (hZ : p ∈ C.Zplus) (hclp : ∀ x, IsClosed (C.Jplus ⊤ {x}))
    (hclm : ∀ x, IsClosed (C.Jminus ⊤ {x}))
    (hdense : C.Jminus ⊤ {p} ⊆ closure (C.Kminus ⊤ {p}))
    (hsep : ∀ y ∈ C.Jplus ⊤ S \ S, C.Jplus ⊤ S ∈ 𝓝 y)
    (hcpt : ∀ x, IsCompact (C.Jplus ⊤ S ∩ C.Jminus ⊤ {x})) (hp : p ∈ frontier (U : Set M))
    (h310 : C.Jminus ⊤ {p} ∩ frontier (U : Set M) ∩ C.Jplus ⊤ S ⊆ {p}) {W : Set M}
    (hW : W ∈ 𝓝 p) :
    ∃ q, C.lt ⊤ p q ∧ C.Jminus ⊤ {q} ∩ (U : Set M)ᶜ ∩ C.Jplus ⊤ S ⊆ W := by
  by_contra hne
  simp only [not_exists, not_and] at hne
  obtain ⟨q₁, hq₁, -⟩ := hZ univ univ_mem
  have hpq₁ : C.lt ⊤ p q₁ := by simpa using hq₁
  let ι := {q : M // C.lt ⊤ p q ∧ C.le ⊤ q q₁}
  haveI : Nonempty ι := ⟨⟨q₁, hpq₁, C.le_refl (U := ⊤) (x := q₁) trivial⟩⟩
  let t : ι → Set M := fun i => C.Jminus ⊤ {i.1} ∩ (U : Set M)ᶜ ∩ (interior W)ᶜ ∩
    (C.Jplus ⊤ S ∩ C.Jminus ⊤ {q₁})
  have hpW : p ∈ interior W := mem_interior_iff_mem_nhds.2 hW
  have htn : ∀ i, (t i).Nonempty := by
    intro i
    obtain ⟨r, ⟨⟨hrq, hrU⟩, hrS⟩, hrW⟩ := not_subset.1 (hne i.1 i.2.1)
    have hrq' : C.le ⊤ r i.1 := by simpa using hrq
    exact ⟨r, ⟨⟨hrq, hrU⟩, fun h => hrW (interior_subset h)⟩, hrS,
      by simpa using C.le_trans hrq' i.2.2⟩
  have htc : ∀ i, IsCompact (t i) := fun i =>
    (hcpt q₁).inter_left (((hclm _).inter U.isOpen.isClosed_compl).inter
      isOpen_interior.isClosed_compl)
  have htcl : ∀ i, IsClosed (t i) := fun i => (htc i).isClosed
  have htd : Directed (· ⊇ ·) t := by
    intro i j
    have hN : C.Iminus ⊤ {i.1} ∩ C.Iminus ⊤ {j.1} ∈ 𝓝 p :=
      inter_mem (isOpen_Iminus.mem_nhds (by simpa using i.2.1))
        (isOpen_Iminus.mem_nhds (by simpa using j.2.1))
    obtain ⟨k, hk, hki, hkj⟩ := hZ _ hN
    have hpk : C.lt ⊤ p k := by simpa using hk
    have hki' : C.lt ⊤ k i.1 := by simpa using hki
    have hkj' : C.lt ⊤ k j.1 := by simpa using hkj
    refine ⟨⟨k, hpk, C.le_trans (C.le_of_lt hki') i.2.2⟩, ?_, ?_⟩
    · rintro r ⟨⟨⟨hrk, hrU⟩, hrW⟩, hrS⟩
      have hrk' : C.le ⊤ r k := by simpa using hrk
      exact ⟨⟨⟨by simpa using C.le_trans hrk' (C.le_of_lt hki'), hrU⟩, hrW⟩, hrS⟩
    · rintro r ⟨⟨⟨hrk, hrU⟩, hrW⟩, hrS⟩
      have hrk' : C.le ⊤ r k := by simpa using hrk
      exact ⟨⟨⟨by simpa using C.le_trans hrk' (C.le_of_lt hkj'), hrU⟩, hrW⟩, hrS⟩
  obtain ⟨r, hr⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t htd htn
    htc htcl
  rw [mem_iInter] at hr
  obtain ⟨⟨⟨-, hrU⟩, hrW⟩, hrS, -⟩ := hr ⟨q₁, hpq₁, C.le_refl (U := ⊤) (x := q₁) trivial⟩
  have hrp : r ∈ C.Jminus ⊤ {p} := by
    have hcl : p ∈ closure (C.Jplus ⊤ {r}) := by
      rw [mem_closure_iff_nhds]
      intro N hN
      obtain ⟨k, hk, hkN, hkq₁⟩ := hZ _ (inter_mem hN (isOpen_Iminus.mem_nhds
        (show p ∈ C.Iminus ⊤ {q₁} by simpa using hpq₁)))
      have hpk : C.lt ⊤ p k := by simpa using hk
      have hkq : C.lt ⊤ k q₁ := by simpa using hkq₁
      exact ⟨k, hkN, by simpa using (hr ⟨k, hpk, C.le_of_lt hkq⟩).1.1.1⟩
    rw [(hclp r).closure_eq] at hcl
    simpa using hcl
  have hrne : r ≠ p := fun e => hrW (e ▸ hpW)
  have hrcl := mem_closure_of_mem_Jminus hcvU hSU hdense hsep (frontier_subset_closure hp) hrp hrS
  exact hrne (h310 ⟨⟨hrp, hrcl, by rwa [U.isOpen.interior_eq]⟩, hrS⟩)

end Causality

namespace CBG

/-! ### Model-free: the core of Lemma 3.9, and `C` closed -/

section Core

variable {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
  {C : Causality M} {D : Causality N} {U : Opens M} {V : Opens N} {ψ : M → N} {g : N → M}

/-- **The core of Sbierski Lemma 3.9**: a boundary point `q ∈ ∂U` with `K⁻(q) ⊆ K⁻(p₀)` (e.g.
`q ≤ p₀`, `prop:K_monotone`), `p₀` corresponding to `p₀'`, has a corresponding point `q'`, in
`J⁺(ψ S) ∩ J⁻(p₀')`: a cluster point of `ψ` along `K⁻(q) ∩ J⁺(S) ⊆ U` (`lem:passe_pgcd`), whose
`ψ`-image lies below `p₀'` (package 5's cluster step `le_of_corresponds`) in the compact
`J⁺(ψ S) ∩ J⁻(p₀')`. Replaces Sbierski's walk along a null geodesic of `∂U`. -/
theorem IsCorrPair.exists_corresponds_of_le [FirstCountableTopology M]
    (h : IsCorrPair C D U V ψ g) (hcvM : C.CausallyConvexIn (U : Set M) ⊤) {S : Set M}
    (hSU : S ⊆ U) {q p₀ : M} {p₀' : N} (hq : q ∈ frontier (U : Set M))
    (hsep : C.Jplus ⊤ S ∈ 𝓝 q) (hdense : q ∈ closure (C.Kminus ⊤ {q}))
    (hmono : C.Kminus ⊤ {q} ⊆ C.Kminus ⊤ {p₀}) (hcl : ∀ y, IsClosed (D.Jplus ⊤ {y}))
    (hcpt : IsCompact (D.Jplus ⊤ (ψ '' S) ∩ D.Jminus ⊤ {p₀'}))
    (hc : Corresponds (U : Set M) ψ p₀ p₀') :
    ∃ q', q' ∈ D.Jplus ⊤ (ψ '' S) ∩ D.Jminus ⊤ {p₀'} ∧ Corresponds (U : Set M) ψ q q' := by
  have hpass := Causality.Kminus_inter_Jplus_subset_of_causallyConvexIn hcvM hSU
    (frontier_subset_closure hq)
  have hqA : q ∈ closure (C.Kminus ⊤ {q} ∩ C.Jplus ⊤ S) := by
    rw [mem_closure_iff_nhds] at hdense ⊢
    intro O hO
    obtain ⟨z, ⟨hzO, hzS⟩, hzK⟩ := hdense (O ∩ C.Jplus ⊤ S) (inter_mem hO hsep)
    exact ⟨z, hzO, hzK, hzS⟩
  haveI : NeBot (𝓝[C.Kminus ⊤ {q} ∩ C.Jplus ⊤ S] q) := mem_closure_iff_nhdsWithin_neBot.1 hqA
  have hle : map ψ (𝓝[C.Kminus ⊤ {q} ∩ C.Jplus ⊤ S] q) ≤
      𝓟 (D.Jplus ⊤ (ψ '' S) ∩ D.Jminus ⊤ {p₀'}) := by
    rw [le_principal_iff, mem_map]
    refine mem_of_superset self_mem_nhdsWithin fun x hx => ?_
    have hxU : x ∈ U := hpass hx
    obtain ⟨hxK, σ, hσ, hσx⟩ := hx
    refine ⟨⟨ψ σ, mem_image_of_mem ψ hσ, (h.le_iff σ (hSU hσ) x hxU).1 hσx⟩, ?_⟩
    rw [Precausality.mem_Jminus_singleton]
    exact h.le_of_corresponds (hcl _) hxU
      (Causality.Jplus_mem_nhds_of_mem_Kminus (hmono hxK)) hc
  obtain ⟨q', hq'K, hcl'⟩ := hcpt hle
  exact ⟨q', hq'K,
    corresponds_iff_mapClusterPt.2 (MapClusterPt.mono hcl' (nhdsWithin_mono q hpass))⟩

/-- **The set of corresponding pairs is closed** (`prop:C_connexe`, second half, `ETT.tex:2241–2242`; there in
`∂j₁(N) × ∂j₂(N)`): the corresponding pairs form the closure of the graph of `ψ` on `U`. -/
theorem isClosed_setOf_corresponds (U : Set M) (ψ : M → N) :
    IsClosed {pq : M × N | Corresponds U ψ pq.1 pq.2} := by
  have he : {pq : M × N | Corresponds U ψ pq.1 pq.2} = closure ((fun x => (x, ψ x)) '' U) := by
    ext ⟨p, q⟩
    rw [mem_setOf_eq, mem_closure_iff_nhds]
    constructor
    · intro hc o ho
      obtain ⟨O, hO, O', hO', hsub⟩ := mem_nhds_prod_iff.1 ho
      obtain ⟨x, hxU, hxO, hψ⟩ := hc O hO O' hO'
      exact ⟨(x, ψ x), hsub ⟨hxO, hψ⟩, x, hxU, rfl⟩
    · intro hc O hO O' hO'
      obtain ⟨_, ⟨hxO, hψ⟩, x, hxU, rfl⟩ := hc _ (prod_mem_nhds hO hO')
      exact ⟨x, hxU, hxO, hψ⟩
  rw [he]; exact isClosed_closure

/-- **`prop:C_connexe`, second half, in ETT's ambient** (`ETT.tex:2241–2242`: "`C` is closed in
`∂j₁(N) × ∂j₂(N)`"): the corresponding pairs lying in `∂U × ∂V` form a closed set (for `V = ψ(U)`
every corresponding pair over `∂U` lies there, package 5's `IsCorrPair.mem_frontier_of_corresponds`). -/
theorem isClosed_setOf_corresponds_frontier (U : Set M) (V : Set N) (ψ : M → N) :
    IsClosed ({pq : M × N | Corresponds U ψ pq.1 pq.2} ∩ (frontier U ×ˢ frontier V)) :=
  (isClosed_setOf_corresponds U ψ).inter (isClosed_frontier.prod isClosed_frontier)

end Core

/-! ### Witness: the model-free Lemma 3.11 on the timelike line -/

section Witness

/-- **The hypotheses of `Causality.exists_lt_Jminus_compl_subset` are jointly satisfiable**
(kb/0011): the timelike line, `U = ]-∞, 1[`, `S = {0}`, `p = 1` (regular case; (3.10) holds since
`∂U = {1}`). -/
theorem timelikeLine_spacelike_hypotheses :
    timelikeLine.CausallyConvexIn (iioOne : Set ℝ) ⊤ ∧ ({0} : Set ℝ) ⊆ iioOne ∧
      (1 : ℝ) ∈ timelikeLine.Zplus ∧ (∀ x, IsClosed (timelikeLine.Jplus ⊤ {x})) ∧
      (∀ x, IsClosed (timelikeLine.Jminus ⊤ {x})) ∧
      timelikeLine.Jminus ⊤ {(1 : ℝ)} ⊆ closure (timelikeLine.Kminus ⊤ {(1 : ℝ)}) ∧
      (∀ y ∈ timelikeLine.Jplus ⊤ {0} \ {0}, timelikeLine.Jplus ⊤ {(0 : ℝ)} ∈ 𝓝 y) ∧
      (∀ x, IsCompact (timelikeLine.Jplus ⊤ {0} ∩ timelikeLine.Jminus ⊤ {x})) ∧
      (1 : ℝ) ∈ frontier (iioOne : Set ℝ) ∧
      timelikeLine.Jminus ⊤ {(1 : ℝ)} ∩ frontier (iioOne : Set ℝ) ∩
        timelikeLine.Jplus ⊤ {0} ⊆ {1} := by
  have hfr : frontier (iioOne : Set ℝ) = {1} := by
    show frontier (Iio (1 : ℝ)) = {1}; exact frontier_Iio
  have hK := timelikeLine_kSide
  refine ⟨timelikeLine_causallyConvexIn_iioOne, ?_, timelikeLine_mem_Zplus 1, hK.isClosed_Jplus,
    hK.isClosed_Jminus, hK.dense 1, hK.separates, hK.isCompact, by rw [hfr]; rfl, ?_⟩
  · rintro _ rfl; show (0 : ℝ) < 1; norm_num
  · rw [hfr]; exact fun x hx => hx.1.2

/-- **The hypotheses of `IsCorrPair.exists_corresponds_of_le` are jointly satisfiable, with a
genuine corresponding pair** (kb/0011): the timelike line, `U = V = ]-∞, 1[`, `ψ = g = id`,
`S = {0}`, `q = p₀ = p₀' = 1`. **Degenerate witness**: `q = p₀` (on the line `∂U = {1}`, so no
boundary point `q ≠ p₀` exists), hence `K⁻(q) ⊆ K⁻(p₀)` is `subset_rfl` and the lemma's
conclusion is its hypothesis `Corresponds … 1 1`; it witnesses consistency only, not the cluster
argument at a point strictly below `p₀`. -/
theorem timelikeLine_corrPair_hypotheses :
    IsCorrPair timelikeLine timelikeLine iioOne iioOne id id ∧
      timelikeLine.CausallyConvexIn (iioOne : Set ℝ) ⊤ ∧ ({0} : Set ℝ) ⊆ iioOne ∧
      (1 : ℝ) ∈ frontier (iioOne : Set ℝ) ∧ timelikeLine.Jplus ⊤ {(0 : ℝ)} ∈ 𝓝 (1 : ℝ) ∧
      (1 : ℝ) ∈ closure (timelikeLine.Kminus ⊤ {(1 : ℝ)}) ∧
      (∀ y, IsClosed (timelikeLine.Jplus ⊤ {y})) ∧
      IsCompact (timelikeLine.Jplus ⊤ (id '' {(0 : ℝ)}) ∩ timelikeLine.Jminus ⊤ {(1 : ℝ)}) ∧
      Corresponds (iioOne : Set ℝ) id (1 : ℝ) 1 := by
  have hfr : frontier (iioOne : Set ℝ) = {1} := by
    show frontier (Iio (1 : ℝ)) = {1}; exact frontier_Iio
  have hK := timelikeLine_kSide
  refine ⟨timelikeLine_isCorrPair_id, timelikeLine_causallyConvexIn_iioOne, ?_, by rw [hfr]; rfl,
    hK.separates 1 ⟨?_, ?_⟩, hK.dense 1 ?_, hK.isClosed_Jplus, by rw [image_id]; exact hK.isCompact 1,
    timelikeLine_corresponds_one⟩
  · rintro _ rfl; show (0 : ℝ) < 1; norm_num
  · rw [timelikeLine_Jplus_top_singleton]; norm_num
  · norm_num
  · rw [timelikeLine_Jminus_top_singleton]; exact mem_Iic.2 (le_refl (1 : ℝ))

end Witness

end CBG

end Causal
