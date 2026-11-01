import CausalScaffold.CBG.Pgcd
import CausalScaffold.CBG.Corresponding

/-!
# No corresponding boundary points between a development and the MCGHD (Sbierski §3.2)

Package 6 (`docs/CBG-DESIGN.md` §3 step 4, second half; §5 row 6). **No label is marked**
(DEC-60: ETT labels are the ETT campaign's; rows stay partial until the singular instance
discharges the model). Cited, unmarked: `prop:Cauchy_point_min` — `ETT.tex:2270`,
`prop:Cauchy_non_max` — `ETT.tex:2178`, `prop:C_connexe` — `ETT.tex:2240`, `prop:ppcm_Cauchy` —
`ETT.tex:1994`, `rem:non_separe_cas` — `ETT.tex:2016`, `lem:passe_pgcd` — `ETT.tex:2042`; Sbierski
1309.7591, Lemma 3.8 (second half), **Lemma 3.9**, **Lemma 3.11**, **Thm 3.6**, **Thm 3.13**
(pp. 15–20: Thm 3.6 p. 15, Lemma 3.8 p. 16, Lemma 3.9 p. 17, Lemma 3.11 p. 18, Thm 3.13 p. 20),
and the Hausdorff step of the proof of Thm 2.7 (p. 20).

> Lemma 3.9. Let $U$ be a CGHD of $M$ and $M'$ with isometric embedding $\psi$. Assume that
> $C\cap J^+(\iota(M))$ is non-empty. Then there exists a point $p\in C$ with the property
> $J^-(p)\cap\partial U\cap J^+(\iota(M))=\{p\}$ (3.10). (Sbierski, p. 17)

> Lemma 3.11. Let $U$ be a GHD of some initial data and $M\supseteq U$ an extension of $U$.
> Suppose that there exists a $p\in\partial U$ that satisfies (3.10). Then for every open
> neighbourhood $W$ of $p$ in $M$ there exists a point $q\in I^+(p)\subseteq M$ such that
> $J^-(q)\cap U^c\cap J^+(\iota(M))\subseteq W$. (Sbierski, p. 18)

> Theorem 3.6. Let $M$ and $M'$ be GHDs of the same initial data, and say $U$ is a CGHD of $M$ and
> $M'$. If there are corresponding boundary points of $U$ in $M$ and $M'$, then there exists a
> strictly larger extension of $U$ that is also a CGHD of $M$ and $M'$. In particular, $U$ is not
> the MCGHD of $M$ and $M'$. (Sbierski, p. 15)

> Theorem 3.13. Let $M$ and $M'$ be GHDs of the same initial data, and let $U$ be the MCGHD of $M$
> and $M'$. Then $U$ does not have corresponding boundary points in $M$ and $M'$. (Sbierski, p. 20)

> If $C\neq \emptyset$, then there exists $(p',q')\in C$ with
> $J_{M_1}(\Sigma_1,p')\setminus\{p'\}\subset j_1(N)$. (`prop:Cauchy_point_min`, `ETT.tex:2270–2273`)

> If there exists $(p,q)\in C$ with $J_{M_1}(\Sigma_1,p)\setminus\{p\}\subset j_1(N)$, then $N$ is
> not maximal among the common sub-extensions of $M_1$ and $M_2$. (`prop:Cauchy_non_max`,
> `ETT.tex:2178–2181`)

> Take $N=\pgcd$. If $C$ were non-empty, […] would then contradict the maximality of $\pgcd$
> […]. Hence $C=\emptyset$, so by Remark `rem:non_separe_cas` the quotient $\ppcm$ is Hausdorff.
> (proof of `prop:ppcm_Cauchy`, `ETT.tex:2320–2324`)

## What is proved (no `sorry` in this file)

* **Model-free** (any causality, open sets, kb/0001): `Causality.exists_minimal_of_isCompact` (a
  compact set has a `≤`-minimal point when `M` is causal with closed `J⁻(x)`: Zorn, in place of
  the design's Geroch time), `Causality.mem_closure_of_mem_Jminus` (a point of `J⁻(p) ∩ J⁺(S)`,
  `p ∈ closure U`, is in `closure U`: `K⁻` density + `lem:passe_pgcd`),
  `Causality.spacelike_iff` (**(3.10) ⟺ ETT's `J(Σ, p) ∖ {p} ⊆ U`**),
  `Causality.exists_lt_Jminus_compl_subset` (**Sbierski Lemma 3.11**),
  `IsCorrPair.exists_corresponds_of_le` (the core of Lemma 3.9: a boundary point `q ≤ p₀`, `p₀`
  corresponding, has a corresponding point), `isClosed_setOf_corresponds` (`prop:C_connexe`,
  second half; `isClosed_setOf_corresponds_frontier` in ETT's `∂ × ∂`). Witnesses:
  `timelikeLine_spacelike_hypotheses` (Lemma 3.11), `timelikeLine_corrPair_hypotheses`
  (`exists_corresponds_of_le`, with a genuine corresponding pair).
* **Level A** (`CGHDData`): `exists_spacelike_corresponding` / `_past` (**Lemma 3.9**, both time
  directions), `exists_spacelike` (`prop:Cauchy_point_min`, unmarked; Sbierski's WLOG made explicit),
  `exists_diamond_subset` (`prop:Cauchy_point_min` in ETT's words, from `C ∩ J⁺(S) ≠ ∅`),
  `exists_diamond_subset_of_nonempty` (**ETT's literal `prop:Cauchy_point_min`**, from `C ≠ ∅`,
  reading `J(Σ₁,p') = J⁺(Σ₁) ∩ J⁻(p')`), `exists_diamond_subset_past` / `exists_diamond_subset_symm`
  (the same under the time-symmetric reading `J⁻(Σ₁) ∩ J⁺(p')` at past points),
  `exists_lt_Jminus_compl_subset_of_cauchy` / `exists_lt_Jplus_compl_subset_past` (**Lemma 3.11**
  on admissible spacetimes),
  `correspondingExt` + `exists_isMor_eqOn_correspondingExt` (**Lemma 3.8, second half**: `ψ`
  extends to `U ∪ C`, locally a structure morphism), `exists_extension` (**Thm 3.6**, local form:
  `U < U'`, `ψ'` a morphism on `U'` extending `ψ`, `S` Cauchy in the GH `U'`),
  `t2Space_gluing_iff` (the gluing `(M ⊔ N)/U` is Hausdorff **iff** `C = ∅`).
* **Developments** (`IsCGHD`, package 4): `IsCGHD.cghdData`, `IsCGHD.exists_lt` (**Thm 3.6**:
  a strictly larger common Cauchy development), `correspondingSet_mcghd_eq_empty` (**Thm 3.13**),
  `t2Space_gluing_mcghd` (**the gluing of two developments along their MCGHD is T2**, the
  Hausdorff step of Thm 2.7 and of `prop:ppcm_Cauchy`).

## Hypothesis checklist

| paper | here |
|---|---|
| Lemma 3.9: `U` a CGHD, `C ∩ J⁺(ι(M)) ≠ ∅` | ✓ `CGHDData` (package 5's A3 setting) + `p₀ ∈ C ∩ J⁺(S)`; past twin `_past` (`J⁻`, `K⁺`; R4, no duality of the bundle) |
| Lemma 3.9's proof: null geodesics in `∂U`, `C` open and closed along them, Lemma 3.8's embedding | ⚠ replaced: a `≤`-minimal point of the compact `∂U ∩ J⁺(Σ) ∩ J⁻(p₀)` (A2 `isCompact_*`, Zorn) and the `K⁻` cluster argument of package 5 (`exists_corresponds_of_le`; `K_monotone` of the corrected bundle). No geodesic, no time function, no openness of `C` |
| design §3 step 4: "Lemma 3.9 via a Geroch time minimised on `∂U ∩ J(Σ, p₀)`" | ⚠ replaced: `≤`-minimal point (Zorn; `J⁻(x)` closed, causal). The Geroch time would need a `Geometry` field (the time function Pgcd asks for); minimality needs none |
| Lemma 3.11: `U` a GHD, `M ⊇ U`, `p ∈ ∂U` with (3.10), `W` an open neighbourhood | ✓ `W ∈ 𝓝 p` (any neighbourhood, ⚠ weakened); model-free: `p ∈ Z⁺`, `J^±(x)` closed, `J⁻(p) ⊆ closure K⁻(p)`, `lem:Sigma_separe`'s clause, compact `J⁺(S) ∩ J⁻(x)`, `U` causally convex (all derived from A2 at Level A); only `⊆` of (3.10) used |
| Lemma 3.11's proof: a timelike curve `γ` from `p`, "the relation `≤` is closed" | ⚠ replaced: the directed family `q ≫ p, q ≤ q₁` (`Z⁺`) and closed `J⁺(r)`; the final contradiction by `K⁻` density + `lem:passe_pgcd` instead of "contradicts the GH of `U`" |
| Lemma 3.11, past side | ⚠ strengthened: `p ∉ sing₀` (`exists_lt_Jplus_compl_subset_past`): at a BTZ point `I⁻(p) = ∅`, so the conclusion `q ∈ I⁻(p)` is unsatisfiable there; without `p ∉ sing₀` the lemma would say no BTZ point satisfies its hypotheses (not settled here); finding (R4) |
| Thm 3.6: `M`, `M'` GHDs, `U` a CGHD, corresponding points exist | ✓ `IsCGHD N₁ N₂ W f`, `C ≠ ∅` (any time side: `mem_Jplus_union_Jminus_of_isCauchySurface`) |
| Thm 3.6: `ψ` an isometric **embedding** | ⚠ carried as `InjOn f W` (Pgcd's `IsCGHD` asks a morphism only; injectivity is Lemma 3.3, `IsCGHD.injOn`, which needs a time function) |
| Thm 3.6's proof: `τ_q`, the hyperboloid `S`, Theorem 2.6 (local uniqueness), Lemma 3.1 continuity | ⚠ replaced by the interface: A4 (`slice_future` / `slice_past`, Sbierski (3.12) + Lemma 3.11) and A3 (`germExt_*`, Lemma 3.8, via `CGHDData.ext_continue`); Sbierski's "convex neighbourhood `V` with `V ∩ ∂U ⊆ C`" is not needed (one germ `φ` on `O ∋ p`, `U' ⊆ U ∪ O`) |
| Thm 3.6: "strictly larger", "a CGHD" | ✓ `W < W'`, `IsCGHD N₁ N₂ W' f'`, `f' = f` on `W`; ⚠ injectivity of `f'` (Sbierski's "isometric embedding") **not** delivered — package 4's `IsCGHD` does not ask it; it follows from `IsCGHD.injOn` given a time function (the same interface need as the hypothesis `InjOn f W`) |
| Thm 3.13: `U` the MCGHD | ✓ `mcghdOpens`, `mcghdMap` (package 4); ⚠ `InjOn mcghdMap mcghdOpens` carried (or a time function, `_of_timeFunction`) |
| `prop:Cauchy_point_min`: `C ≠ ∅` | ✓ under either reading of `J_{M_1}(\Sigma_1,p')` (ETT defines `J_M(Σ,p)` only for `p ∈ J⁺(Σ)`; question reported): `J⁺(Σ₁) ∩ J⁻(p')` — `exists_diamond_subset_of_nonempty` (future case by Lemma 3.9 + `spacelike_iff`; past case vacuous under this reading: `J⁺(Σ₁) ∩ J⁻(p₀) ⊆ U` by causal convexity); time-symmetric `J⁻(Σ₁) ∩ J⁺(p')` at past points — `exists_diamond_subset_symm` / `_past` (not vacuous); `exists_spacelike` (the time-oriented (3.10), future or past — what `prop:Cauchy_non_max`'s past-side slice needs) |
| `prop:Cauchy_non_max`: `(p,q) ∈ C` with `J(Σ₁,p) ∖ {p} ⊂ j₁(N)` | ⚠ weakened: `C ≠ ∅` suffices (`IsCGHD.exists_lt`: Lemma 3.9 supplies the point) |
| `prop:Cauchy_non_max`: `N ∈ ℰ` (`ETT.tex:1953–1954`, no injectivity) | ⚠ strengthened: `InjOn f W` carried (discharged by `IsCGHD.injOn` from a time function — Pgcd's interface need) |
| `prop:Cauchy_non_max`: conclusion "`N` not maximal" in `ℰ` | ✓ carried: the larger `(W', f')` is `IsCGHD` (package 4), which, like ETT's `ℰ`, asks no injectivity |
| `prop:ppcm_Cauchy`, Hausdorff half; `rem:non_separe_cas` | ✓ `t2Space_gluing_mcghd` (`Gluing.t2Space_iff_Cdist_eq_empty`, `C_eq_closure`); the structure on the gluing and its minimality are package 7 |
| `prop:ppcm_Cauchy`: `ℰ` without injectivity | ⚠ strengthened: `InjOn mcghdMap mcghdOpens` carried (or a time function, `_of_timeFunction`) |
| `prop:C_connexe`: "`C` is closed in `∂j₁(N) × ∂j₂(N)`" | ✓ `isClosed_setOf_corresponds_frontier` (the corresponding pairs in `∂U × ∂V`, any `V`; `C ⊆ ∂U × ∂ψ(U)` by package 5's `mem_frontier_of_corresponds`) and `isClosed_setOf_corresponds` (reading: all corresponding pairs in `M × N`, the closure of the graph; model-free) |
| second countable | model-free ⚠ weakened: first countable; Level A ✓ carried |

## SCOPE (disclosed)

* **No new `Geometry` field is needed by this package.** Lemma 3.9 uses only A2 (`isCompact_*`,
  `K_monotone`/`K_densite_sing` of the corrected bundle, `tarentin` via `kSide_*`) and A3 (through
  package 5's `CGHDData`, whose `isCorrPair` asks `ψ` injective); Thm 3.6 adds A4. The only
  carried hypothesis is the injectivity of `f` (resp. of `mcghdMap`), which `IsCGHD.injOn`
  (package 4) obtains from `(𝔊.causality N₁.str).HasTimeFunction` — Pgcd's reported interface
  need (a `timeFunction` field), repeated here, not new.
* Thm 3.6 is proved **from A4**, which is Sbierski's slice step (`τ_q`, (3.12), Lemma 3.11, the
  Gauss lemma, Theorem 2.6) taken as an axiom of the geometry (design §2); Lemma 3.11 is proved
  here independently (model-free and Level A) so that whoever discharges A4 at the instance
  (packages 11, 12) has it. It is not used by `exists_extension`, A4 consuming it internally.
* Lemma 3.9's conclusion is Sbierski's (3.10). ETT's form (`prop:Cauchy_point_min`) depends on
  how `J_{M_1}(\Sigma_1,p')` (`ETT.tex:2272`) is read at a past point: ETT defines `J_M(Σ, p)` only
  for `p ∈ J⁺(Σ)` (`lem:image_diamant`, `ETT.tex:2024–2027`), so this is an **ambiguity, reported
  as a question** (kb/0011), and both readings are proved. Reading `J⁺(Σ₁) ∩ J⁻(p')`:
  `exists_diamond_subset_of_nonempty`, and **under this reading** the statement is true but
  vacuous at past points (`p₀ ∈ C ∩ J⁻(Σ₁)` gives `J⁺(Σ₁) ∩ J⁻(p₀) ⊆ U` by causal convexity,
  so `p' = p₀` works), hence too weak to feed `prop:Cauchy_non_max`'s past-side slice. Reading
  `J⁻(Σ₁) ∩ J⁺(p')` at past points (time-symmetric): `exists_diamond_subset_symm` /
  `exists_diamond_subset_past`, not vacuous — this is the past (3.10) in diamond form. The
  time-oriented (3.10) (`exists_spacelike`) is what `exists_extension` uses.
* Lemma 3.8's extension (`correspondingExt`) is local: at every `p ∈ C` some morphism `φ` on an
  open `O ∋ p` agrees with `ψ̂` on `O ∩ (U ∪ C)`. That `ψ̂` is injective ("isometric embedding",
  Sbierski) is not proved; nothing here uses it.
* The gluing statements are topological (`T2Space` of `Gluing`); its structure (`glue`), causality
  (`Gluing.causality`) and global hyperbolicity are package 7 (`Ppcm`).
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

/-- **A compact set has a `≤`-minimal point** (`M` causal, `J⁻(x)` closed, `M` Hausdorff): Zorn on
the non-empty closed down-sets of `K`, chains having non-empty intersection by compactness. This
replaces the design's "minimise a Geroch time" (no time function is needed). -/
theorem exists_minimal_of_isCompact [T2Space M] (hcaus : C.IsCausal)
    (hcl : ∀ x, IsClosed (C.Jminus ⊤ {x})) {K : Set M} (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ p ∈ K, ∀ q ∈ K, C.le ⊤ q p → q = p := by
  set F : Set (Set M) := {A | A ⊆ K ∧ A.Nonempty ∧ IsClosed A ∧
    ∀ a ∈ A, ∀ b ∈ K, C.le ⊤ b a → b ∈ A} with hF
  have hKF : K ∈ F := ⟨subset_rfl, hne, hK.isClosed, fun _ _ _ hb _ => hb⟩
  have hH : ∀ c ⊆ F, IsChain (· ⊆ ·) c → c.Nonempty → ∃ lb ∈ F, ∀ s ∈ c, lb ⊆ s := by
    intro c hcF hc hcne
    refine ⟨⋂₀ c, ⟨?_, ?_, isClosed_sInter fun A hA => (hcF hA).2.2.1, ?_⟩,
      fun _ hs => sInter_subset_of_mem hs⟩
    · obtain ⟨A, hA⟩ := hcne
      exact (sInter_subset_of_mem hA).trans (hcF hA).1
    · haveI : Nonempty c := hcne.to_subtype
      refine IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed ?_
        (fun A hA => (hcF hA).2.1)
        (fun A hA => hK.of_isClosed_subset (hcF hA).2.2.1 (hcF hA).1)
        (fun A hA => (hcF hA).2.2.1)
      intro a ha b hb
      by_cases hab : a = b
      · exact ⟨a, ha, subset_rfl, hab ▸ subset_rfl⟩
      · rcases hc ha hb hab with h | h
        · exact ⟨a, ha, subset_rfl, h⟩
        · exact ⟨b, hb, h, subset_rfl⟩
    · intro a ha b hb hba
      exact mem_sInter.2 fun A hA => (hcF hA).2.2.2 a (ha A hA) b hb hba
  obtain ⟨m, -, hm⟩ := zorn_superset_nonempty F hH K hKF
  · obtain ⟨⟨hmK, ⟨p, hp⟩, -, hmdown⟩, hmin⟩ := hm
    have hlow : ∀ x ∈ m, K ∩ C.Jminus ⊤ {x} ∈ F := fun x hx =>
      ⟨inter_subset_left, ⟨x, hmK hx, by simpa using C.le_refl (U := ⊤) (x := x) trivial⟩,
        hK.isClosed.inter (hcl x), fun a ha b hb hba =>
          ⟨hb, by
            have hax : C.le ⊤ a x := by simpa using ha.2
            simpa using C.le_trans hba hax⟩⟩
    have hsub : ∀ x ∈ m, K ∩ C.Jminus ⊤ {x} ⊆ m := fun x hx b hb =>
      hmdown x hx b hb.1 (by simpa using hb.2)
    refine ⟨p, hmK hp, fun q hq hqp => ?_⟩
    have hqm : q ∈ m := hmdown p hp q hq hqp
    have hpq := (hmin (hlow q hqm) (hsub q hqm) hp).2
    exact hcaus hqp (by simpa using hpq)

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

/-! ### Level A: Lemmas 3.8 (second half), 3.9, 3.11, Thm 3.6, the gluing -/

section LevelA

variable (𝔊 : Geometry.{u}) {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]

/-- **Gluing a germ** (Sbierski, proof of Thm 3.6: "we can extend `ψ` to `Ψ : U ∪ N → M′`"): a
morphism `ψ` on `U` and a morphism `φ` on `O` agreeing on `O ∩ U` give, on any open `U' ⊆ U ∪ O`,
the morphism `ψ` on `U`, `φ` off `U` (locality of morphisms). -/
theorem isMor_piecewise {s : 𝔊.Str M} {t : 𝔊.Str N} {U O U' : Opens M} {ψ φ : M → N}
    [DecidablePred (· ∈ (U : Set M))] (hψ : 𝔊.IsMor s t U ψ) (hφ : 𝔊.IsMor s t O φ)
    (heq : EqOn φ ψ (O ⊓ U : Opens M)) (hU' : (U' : Set M) ⊆ U ∪ O) :
    𝔊.IsMor s t U' ((U : Set M).piecewise ψ φ) := by
  refine 𝔊.isMor_of_locally fun x hx => ?_
  by_cases hxU : x ∈ (U : Set M)
  · exact ⟨U ⊓ U', inf_le_right, ⟨hxU, hx⟩, 𝔊.isMor_congr (𝔊.isMor_mono hψ inf_le_left)
      fun y hy => (piecewise_eq_of_mem _ _ _ hy.1).symm⟩
  · have hxO : x ∈ O := (hU' hx).resolve_left hxU
    refine ⟨O ⊓ U', inf_le_right, ⟨hxO, hx⟩, 𝔊.isMor_congr (𝔊.isMor_mono hφ inf_le_left)
      fun y hy => ?_⟩
    by_cases hyU : y ∈ (U : Set M)
    · rw [piecewise_eq_of_mem _ _ _ hyU]; exact heq ⟨hy.1, hyU⟩
    · rw [piecewise_eq_of_notMem _ _ _ hyU]

variable {𝔊} {s : 𝔊.Str M} {t : 𝔊.Str N} {U : Opens M} {ψ : M → N} {S : Set M}

/-- **Lemma 3.8's extension** `ψ̂` on `U ∪ C`: `ψ` on `U`, the (unique, `eq_of_corresponds`)
corresponding point on `C`. -/
noncomputable def correspondingExt (U : Set M) (ψ : M → N) (x : M) : N := by
  classical
  exact if hx : x ∈ correspondingSet U ψ then Classical.choose hx.2 else ψ x

theorem corresponds_correspondingExt {U : Set M} {ψ : M → N} {x : M}
    (hx : x ∈ correspondingSet U ψ) : Corresponds U ψ x (correspondingExt U ψ x) := by
  classical
  simp only [correspondingExt, dif_pos hx]
  exact Classical.choose_spec hx.2

theorem correspondingExt_eq_of_mem {U : Opens M} {ψ : M → N} {x : M} (hx : x ∈ (U : Set M)) :
    correspondingExt (U : Set M) ψ x = ψ x := by
  classical
  have : x ∉ correspondingSet (U : Set M) ψ := fun h => by
    have := h.1; rw [U.isOpen.frontier_eq] at this; exact this.2 hx
  simp only [correspondingExt, dif_neg this]

variable [T2Space M] [ConnectedSpace M] [SecondCountableTopology M]
  [T2Space N] [ConnectedSpace N] [SecondCountableTopology N]

namespace CGHDData

omit [SecondCountableTopology N] in
/-- **Sbierski Lemma 3.8, second half** ("`ψ` extends smoothly to `ψ : U ∪ C → M′`"), local
form: `ψ̂ = correspondingExt` is `ψ` on `U`, and near every `p ∈ C` it is the restriction to
`U ∪ C` of a structure morphism `φ` (A3's germ: `φ` is continuous, so `φ p'` corresponds to every
`p' ∈ O ∩ ∂U`, and corresponding points are unique). -/
theorem exists_isMor_eqOn_correspondingExt (h : CGHDData 𝔊 s t U ψ S) {p : M}
    (hp : p ∈ correspondingSet (U : Set M) ψ) :
    ∃ (O : Opens M) (φ : M → N), p ∈ O ∧ 𝔊.IsMor s t O φ ∧
      EqOn φ (correspondingExt (U : Set M) ψ)
        ((O : Set M) ∩ ((U : Set M) ∪ correspondingSet (U : Set M) ψ)) := by
  obtain ⟨O, φ, hpO, hφ, -, heq, -⟩ := h.ext_continue hp.1 (corresponds_correspondingExt hp)
  refine ⟨O, φ, hpO, hφ, ?_⟩
  rintro x ⟨hxO, hxU | hxC⟩
  · rw [correspondingExt_eq_of_mem hxU]; exact heq ⟨hxO, hxU⟩
  · haveI : NeBot (𝓝[(U : Set M)] x) :=
      mem_closure_iff_nhdsWithin_neBot.1 (frontier_subset_closure hxC.1)
    have hφc : ContinuousAt φ x :=
      (𝔊.isEMorphismOn_of_isMor hφ).continuousOn.continuousAt (O.isOpen.mem_nhds hxO)
    have ht : Tendsto ψ (𝓝[(U : Set M)] x) (𝓝 (φ x)) := by
      refine Tendsto.congr' ?_ (hφc.tendsto.mono_left nhdsWithin_le_nhds)
      filter_upwards [inter_mem_nhdsWithin (U : Set M) (O.isOpen.mem_nhds hxO)] with y hy
      exact heq ⟨hy.2, hy.1⟩
    exact h.eq_of_corresponds hxC.1 (corresponds_iff_mapClusterPt.2 ht.mapClusterPt)
      (corresponds_correspondingExt hxC)

/-- **Sbierski Lemma 3.9** (future side, `ETT.tex:2270` `prop:Cauchy_point_min`): if
`p₀ ∈ C ∩ J⁺(S)`, some `p ∈ C` has `J⁻(p) ∩ ∂U ∩ J⁺(S) = {p}` (3.10). `p` is a `≤`-minimal
point of the compact `J⁺(S) ∩ J⁻(p₀) ∩ ∂U` (A2, `exists_minimal_of_isCompact`); it corresponds
to some point by `exists_corresponds_of_le` (`K⁻(p) ⊆ K⁻(p₀)`, the corrected `K_monotone`). -/
theorem exists_spacelike_corresponding (h : CGHDData 𝔊 s t U ψ S) {p₀ : M}
    (hp₀ : p₀ ∈ correspondingSet (U : Set M) ψ) (hp₀S : p₀ ∈ (𝔊.causality s).Jplus ⊤ S) :
    ∃ p ∈ correspondingSet (U : Set M) ψ,
      (𝔊.causality s).Jminus ⊤ {p} ∩ frontier (U : Set M) ∩ (𝔊.causality s).Jplus ⊤ S = {p} := by
  haveI : Nonempty M := ⟨p₀⟩
  obtain ⟨hp₀f, q₀, hc₀⟩ := hp₀
  have hA := 𝔊.singularFlatAxioms s
  have kM := kSide_future s h.gh h.cauchy
  have kN := kSide_future t h.gh' h.cauchy'
  have hK : IsCompact (((𝔊.causality s).Jplus ⊤ S ∩ (𝔊.causality s).Jminus ⊤ {p₀}) ∩
      frontier (U : Set M)) :=
    (𝔊.isCompact_Jplus_inter_Jminus s h.gh S h.cauchy p₀).inter_right isClosed_frontier
  obtain ⟨p, hpK, hmin⟩ := Causality.exists_minimal_of_isCompact h.gh.1 kM.isClosed_Jminus hK
    ⟨p₀, ⟨hp₀S, by simpa using (𝔊.causality s).le_refl (U := ⊤) (x := p₀) trivial⟩, hp₀f⟩
  have hpp₀ : (𝔊.causality s).le ⊤ p p₀ := by simpa using hpK.1.2
  have hpnU : p ∉ (U : Set M) := by
    have := hpK.2; rw [U.isOpen.frontier_eq] at this; exact this.2
  obtain ⟨q', -, hc'⟩ := h.isCorrPair.exists_corresponds_of_le h.causallyConvexIn h.subset hpK.2
    (kM.separates p ⟨hpK.1.1, fun hm => hpnU (h.subset hm)⟩)
    (kM.dense p (by simpa using (𝔊.causality s).le_refl (U := ⊤) (x := p) trivial))
    (hA.K_monotone h.gh.1 hpp₀).1 kN.isClosed_Jplus (kN.isCompact q₀) hc₀
  refine ⟨p, ⟨hpK.2, q', hc'⟩, ?_⟩
  ext x
  constructor
  · rintro ⟨⟨hxp, hxf⟩, hxS⟩
    have hxp' : (𝔊.causality s).le ⊤ x p := by simpa using hxp
    exact hmin x ⟨⟨hxS, by simpa using (𝔊.causality s).le_trans hxp' hpp₀⟩, hxf⟩ hxp'
  · rintro rfl
    exact ⟨⟨by simpa using (𝔊.causality s).le_refl (U := ⊤) (x := x) trivial, hpK.2⟩, hpK.1.1⟩

/-- **Sbierski Lemma 3.9, past side** (no time reversal of the bundle, R4: the past `K`-calculus
is `K⁺ = I⁺` everywhere, `kSide_past`): if `p₀ ∈ C ∩ J⁻(S)`, some `p ∈ C` has
`J⁺(p) ∩ ∂U ∩ J⁻(S) = {p}`. -/
theorem exists_spacelike_corresponding_past (h : CGHDData 𝔊 s t U ψ S) {p₀ : M}
    (hp₀ : p₀ ∈ correspondingSet (U : Set M) ψ) (hp₀S : p₀ ∈ (𝔊.causality s).Jminus ⊤ S) :
    ∃ p ∈ correspondingSet (U : Set M) ψ,
      (𝔊.causality s).Jplus ⊤ {p} ∩ frontier (U : Set M) ∩ (𝔊.causality s).Jminus ⊤ S = {p} := by
  haveI : Nonempty M := ⟨p₀⟩
  obtain ⟨hp₀f, q₀, hc₀⟩ := hp₀
  have hA := 𝔊.singularFlatAxioms s
  have kM := kSide_past s h.gh h.cauchy
  have kN := kSide_past t h.gh' h.cauchy'
  have hK : IsCompact (((𝔊.causality s).Jminus ⊤ S ∩ (𝔊.causality s).Jplus ⊤ {p₀}) ∩
      frontier (U : Set M)) :=
    (𝔊.isCompact_Jminus_inter_Jplus s h.gh S h.cauchy p₀).inter_right isClosed_frontier
  obtain ⟨p, hpK, hmin⟩ := Causality.exists_minimal_of_isCompact (C := (𝔊.causality s).dual)
    (Causality.dual_isCausal.2 h.gh.1) kM.isClosed_Jminus hK
    ⟨p₀, ⟨hp₀S, by simpa using (𝔊.causality s).le_refl (U := ⊤) (x := p₀) trivial⟩, hp₀f⟩
  have hp₀p : (𝔊.causality s).le ⊤ p₀ p := by simpa using hpK.1.2
  have hpnU : p ∉ (U : Set M) := by
    have := hpK.2; rw [U.isOpen.frontier_eq] at this; exact this.2
  obtain ⟨q', -, hc'⟩ := h.isCorrPair.dual.exists_corresponds_of_le
    (Causality.dual_causallyConvexIn.2 h.causallyConvexIn) h.subset hpK.2
    (kM.separates p ⟨hpK.1.1, fun hm => hpnU (h.subset hm)⟩)
    (kM.dense p (by simpa using (𝔊.causality s).le_refl (U := ⊤) (x := p) trivial))
    (hA.K_monotone h.gh.1 hp₀p).2 kN.isClosed_Jplus (kN.isCompact q₀) hc₀
  refine ⟨p, ⟨hpK.2, q', hc'⟩, ?_⟩
  ext x
  constructor
  · rintro ⟨⟨hxp, hxf⟩, hxS⟩
    have hxp' : (𝔊.causality s).le ⊤ p x := by simpa using hxp
    exact hmin x ⟨⟨hxS, by simpa using (𝔊.causality s).le_trans hp₀p hxp'⟩, hxf⟩
      (by simpa using hxp')
  · rintro rfl
    exact ⟨⟨by simpa using (𝔊.causality s).le_refl (U := ⊤) (x := x) trivial, hpK.2⟩, hpK.1.1⟩

/-- `prop:Cauchy_point_min` (`ETT.tex:2270`, unmarked) **= Sbierski Lemma 3.9 with its WLOG made
explicit**: if `C ≠ ∅`, some `p ∈ C` satisfies (3.10) in the future or in the past of `S`. -/
theorem exists_spacelike (h : CGHDData 𝔊 s t U ψ S)
    (hC : (correspondingSet (U : Set M) ψ).Nonempty) :
    ∃ p ∈ correspondingSet (U : Set M) ψ,
      (𝔊.causality s).Jminus ⊤ {p} ∩ frontier (U : Set M) ∩ (𝔊.causality s).Jplus ⊤ S = {p} ∨
      (𝔊.causality s).Jplus ⊤ {p} ∩ frontier (U : Set M) ∩ (𝔊.causality s).Jminus ⊤ S = {p} := by
  obtain ⟨p₀, hp₀⟩ := hC
  rcases Causality.mem_Jplus_union_Jminus_of_isCauchySurface (𝔊.curvesExtend s h.gh)
    h.cauchy p₀ with hp₀S | hp₀S
  · obtain ⟨p, hp, e⟩ := h.exists_spacelike_corresponding hp₀ hp₀S
    exact ⟨p, hp, Or.inl e⟩
  · obtain ⟨p, hp, e⟩ := h.exists_spacelike_corresponding_past hp₀ hp₀S
    exact ⟨p, hp, Or.inr e⟩

/-- `prop:Cauchy_point_min` **in ETT's words** (unmarked; future side, `ETT.tex:2270–2273`): if
`C ∩ J⁺(S) ≠ ∅`, some `p ∈ C` has `J(S, p) ∖ {p} = J⁺(S) ∩ J⁻(p) ∖ {p} ⊆ U`
(Lemma 3.9 and `Causality.spacelike_iff`). -/
theorem exists_diamond_subset (h : CGHDData 𝔊 s t U ψ S) {p₀ : M}
    (hp₀ : p₀ ∈ correspondingSet (U : Set M) ψ) (hp₀S : p₀ ∈ (𝔊.causality s).Jplus ⊤ S) :
    ∃ p ∈ correspondingSet (U : Set M) ψ,
      ((𝔊.causality s).Jplus ⊤ S ∩ (𝔊.causality s).Jminus ⊤ {p}) \ {p} ⊆ U := by
  obtain ⟨p, hp, e⟩ := h.exists_spacelike_corresponding hp₀ hp₀S
  have kM := kSide_future s h.gh h.cauchy
  refine ⟨p, hp, (Causality.spacelike_iff h.causallyConvexIn h.subset (kM.dense p)
    kM.separates hp.1).1 e.subset⟩

/-- **`prop:Cauchy_point_min` at ETT's own hypothesis, under the reading
`J_{M_1}(\Sigma_1,p') = J⁺(Σ₁) ∩ J⁻(p')`** (unmarked, `ETT.tex:2270–2273`; ETT defines
`J_M(Σ, p)` only for `p ∈ J⁺(Σ)`, `lem:image_diamant`, so the reading at past points is a
question, see `exists_diamond_subset_symm` for the other one): if `C ≠ ∅`, some `p ∈ C` has
`J⁺(S) ∩ J⁻(p) ∖ {p} ⊆ U`. Future case: Lemma 3.9 (`exists_diamond_subset`). Past case
(`p₀ ∈ C ∩ J⁻(S)`): **vacuous under this reading** — `σ ≤ x ≤ p₀ ≤ σ'` puts `x` in the diamond
of `σ, σ' ∈ S ⊆ U`, so `x ∈ U` by causal convexity, and `p = p₀` works. Under this reading the
statement carries no information at past points; `prop:Cauchy_non_max`'s past-side slice needs
the time-oriented (3.10) of `exists_spacelike` (equivalently `exists_diamond_subset_symm`). -/
theorem exists_diamond_subset_of_nonempty (h : CGHDData 𝔊 s t U ψ S)
    (hC : (correspondingSet (U : Set M) ψ).Nonempty) :
    ∃ p ∈ correspondingSet (U : Set M) ψ,
      ((𝔊.causality s).Jplus ⊤ S ∩ (𝔊.causality s).Jminus ⊤ {p}) \ {p} ⊆ U := by
  obtain ⟨p₀, hp₀⟩ := hC
  rcases Causality.mem_Jplus_union_Jminus_of_isCauchySurface (𝔊.curvesExtend s h.gh)
    h.cauchy p₀ with hp₀S | hp₀S
  · exact h.exists_diamond_subset hp₀ hp₀S
  · refine ⟨p₀, hp₀, ?_⟩
    rintro x ⟨⟨⟨σ, hσ, hσx⟩, hxp⟩, -⟩
    obtain ⟨σ', hσ', hp₀σ'⟩ := hp₀S
    have hxp' : (𝔊.causality s).le ⊤ x p₀ := by simpa using hxp
    exact h.causallyConvexIn.2 σ (h.subset hσ) σ' (h.subset hσ')
      ⟨by simpa using (𝔊.causality s).le_trans hxp' hp₀σ', by simpa using hσx⟩

/-- `prop:Cauchy_point_min` **in diamond form, past side** (unmarked; the time-symmetric
reading of `J_{M_1}(\Sigma_1,p')` at `ETT.tex:2272` as `J⁻(Σ₁) ∩ J⁺(p')` for a past point): if
`C ∩ J⁻(S) ≠ ∅`, some `p ∈ C` has `J⁻(S) ∩ J⁺(p) ∖ {p} ⊆ U`. Lemma 3.9's past twin
(`exists_spacelike_corresponding_past`) and `Causality.spacelike_iff` for the dual causality
(`kSide_past`). -/
theorem exists_diamond_subset_past (h : CGHDData 𝔊 s t U ψ S) {p₀ : M}
    (hp₀ : p₀ ∈ correspondingSet (U : Set M) ψ) (hp₀S : p₀ ∈ (𝔊.causality s).Jminus ⊤ S) :
    ∃ p ∈ correspondingSet (U : Set M) ψ,
      ((𝔊.causality s).Jminus ⊤ S ∩ (𝔊.causality s).Jplus ⊤ {p}) \ {p} ⊆ U := by
  obtain ⟨p, hp, e⟩ := h.exists_spacelike_corresponding_past hp₀ hp₀S
  have kM := kSide_past s h.gh h.cauchy
  exact ⟨p, hp, (Causality.spacelike_iff (C := (𝔊.causality s).dual)
    (Causality.dual_causallyConvexIn.2 h.causallyConvexIn) h.subset (kM.dense p)
    kM.separates hp.1).1 e.subset⟩

/-- **`prop:Cauchy_point_min` under the time-symmetric reading** (unmarked, `ETT.tex:2270–2273`):
if `C ≠ ∅`, some `p ∈ C` lies in `J⁺(S)` with `J⁺(S) ∩ J⁻(p) ∖ {p} ⊆ U`, or in `J⁻(S)` with
`J⁻(S) ∩ J⁺(p) ∖ {p} ⊆ U`. Under this reading ETT's statement is **not** vacuous at past points
(compare `exists_diamond_subset_of_nonempty`, the `J⁺(Σ₁) ∩ J⁻(p')` reading). -/
theorem exists_diamond_subset_symm (h : CGHDData 𝔊 s t U ψ S)
    (hC : (correspondingSet (U : Set M) ψ).Nonempty) :
    ∃ p ∈ correspondingSet (U : Set M) ψ,
      (p ∈ (𝔊.causality s).Jplus ⊤ S ∧
        ((𝔊.causality s).Jplus ⊤ S ∩ (𝔊.causality s).Jminus ⊤ {p}) \ {p} ⊆ U) ∨
      (p ∈ (𝔊.causality s).Jminus ⊤ S ∧
        ((𝔊.causality s).Jminus ⊤ S ∩ (𝔊.causality s).Jplus ⊤ {p}) \ {p} ⊆ U) := by
  obtain ⟨p₀, hp₀⟩ := hC
  rcases Causality.mem_Jplus_union_Jminus_of_isCauchySurface (𝔊.curvesExtend s h.gh)
    h.cauchy p₀ with hp₀S | hp₀S
  · obtain ⟨p, hp, e⟩ := h.exists_spacelike_corresponding hp₀ hp₀S
    have hpS : p ∈ (𝔊.causality s).Jplus ⊤ S := by
      have : p ∈ ({p} : Set M) := rfl
      rw [← e] at this; exact this.2
    have kM := kSide_future s h.gh h.cauchy
    exact ⟨p, hp, Or.inl ⟨hpS, (Causality.spacelike_iff h.causallyConvexIn h.subset (kM.dense p)
      kM.separates hp.1).1 e.subset⟩⟩
  · obtain ⟨p, hp, e⟩ := h.exists_spacelike_corresponding_past hp₀ hp₀S
    have hpS : p ∈ (𝔊.causality s).Jminus ⊤ S := by
      have : p ∈ ({p} : Set M) := rfl
      rw [← e] at this; exact this.2
    have kM := kSide_past s h.gh h.cauchy
    exact ⟨p, hp, Or.inr ⟨hpS, (Causality.spacelike_iff (C := (𝔊.causality s).dual)
      (Causality.dual_causallyConvexIn.2 h.causallyConvexIn) h.subset (kM.dense p)
      kM.separates hp.1).1 e.subset⟩⟩

/-- **Sbierski Theorem 3.6, local form** (`prop:Cauchy_non_max`, `ETT.tex:2178`): if `U` has a
corresponding boundary point, then `U` enlarges to an open `U' > U` carrying a structure morphism
`ψ'` that extends `ψ`, globally hyperbolic with `S` as Cauchy surface. Lemma 3.9 gives `p ∈ C`
with (3.10) (future or past), A3 a germ `φ` of `ψ` at `p` (`ext_continue`), A4 the slice
(`slice_future`/`slice_past`, Sbierski's `τ_q`) inside the germ's domain; `ψ'` is `ψ` on `U`, `φ`
off `U` (`isMor_piecewise`). -/
theorem exists_extension (h : CGHDData 𝔊 s t U ψ S)
    (hC : (correspondingSet (U : Set M) ψ).Nonempty) :
    ∃ (U' : Opens M) (ψ' : M → N), U < U' ∧ 𝔊.IsMor s t U' ψ' ∧ EqOn ψ' ψ U ∧
      (𝔊.causality s).GloballyHyperbolicOn U' ∧ (𝔊.causality s).IsCauchySurfaceOn U' S := by
  classical
  obtain ⟨p, hp, e | e⟩ := h.exists_spacelike hC
  · obtain ⟨q, hc⟩ := hp.2
    obtain ⟨O, φ, hpO, hφ, -, heq, -⟩ := h.ext_continue hp.1 hc
    have hpS : p ∈ (𝔊.causality s).Jplus ⊤ S := by
      have : p ∈ ({p} : Set M) := rfl
      rw [← e] at this; exact this.2
    obtain ⟨U', hUU', hU'sub, hgh, hcy⟩ := 𝔊.slice_future s U S h.gh h.ghOn h.subset h.cauchy
      h.cauchyOn p hp.1 hpS e O hpO
    exact ⟨U', (U : Set M).piecewise ψ φ, hUU', isMor_piecewise 𝔊 h.isMor hφ heq hU'sub,
      fun x hx => piecewise_eq_of_mem _ _ _ hx, hgh, hcy⟩
  · obtain ⟨q, hc⟩ := hp.2
    obtain ⟨O, φ, hpO, hφ, -, heq, -⟩ := h.ext_continue hp.1 hc
    have hpS : p ∈ (𝔊.causality s).Jminus ⊤ S := by
      have : p ∈ ({p} : Set M) := rfl
      rw [← e] at this; exact this.2
    obtain ⟨U', hUU', hU'sub, hgh, hcy⟩ := 𝔊.slice_past s U S h.gh h.ghOn h.subset h.cauchy
      h.cauchyOn p hp.1 hpS e O hpO
    exact ⟨U', (U : Set M).piecewise ψ φ, hUU', isMor_piecewise 𝔊 h.isMor hφ heq hU'sub,
      fun x hx => piecewise_eq_of_mem _ _ _ hx, hgh, hcy⟩

/-- **The gluing `(M ⊔ N)/U` is Hausdorff iff `U` has no corresponding boundary points**
(`rem:non_separe_cas`, `ETT.tex:2016`; Sbierski, proof of Thm 2.7, p. 20): by
`Gluing.t2Space_iff_Cdist_eq_empty` and package 5's `corresponds_iff_mem_gluingC`; a
corresponding pair off the graph has `p ∉ U`, so `p ∈ ∂U`, and conversely. -/
theorem t2Space_gluing_iff [Nonempty M] (h : CGHDData 𝔊 s t U ψ S) :
    T2Space (Gluing (Subtype.val : U → M) (ψ ∘ (Subtype.val : U → M))) ↔
      correspondingSet (U : Set M) ψ = ∅ := by
  have hP := h.isCorrPair
  have hj₁ : IsOpenEmbedding (Subtype.val : U → M) := U.isOpen.isOpenEmbedding_subtypeVal
  have hj₂ : IsOpenEmbedding (ψ ∘ (Subtype.val : U → M)) := hP.isOpenEmbedding_comp_val
  have hC : Gluing.C (Subtype.val : U → M) (ψ ∘ (Subtype.val : U → M)) =
      closure (Gluing.graph (Subtype.val : U → M) (ψ ∘ (Subtype.val : U → M))) :=
    Gluing.C_eq_closure hj₁ hj₂
  refine (Gluing.t2Space_iff_Cdist_eq_empty hj₁ hj₂).trans ?_
  rw [Gluing.Cdist_eq hj₁ hj₂, ← hC]
  constructor
  · intro hemp
    refine eq_empty_iff_forall_notMem.2 fun p hp => ?_
    obtain ⟨hpf, q, hc⟩ := hp
    have hpU : p ∉ (U : Set M) := by
      have := hpf; rw [U.isOpen.frontier_eq] at this; exact this.2
    have hmem : (p, q) ∈ Gluing.C (Subtype.val : U → M) (ψ ∘ (Subtype.val : U → M)) \
        Gluing.graph (Subtype.val : U → M) (ψ ∘ (Subtype.val : U → M)) := by
      refine ⟨hP.corresponds_iff_mem_gluingC.1 hc, ?_⟩
      rintro ⟨w, hw⟩
      exact hpU (by rw [← (Prod.mk.inj hw).1]; exact w.2)
    rw [hemp] at hmem; exact hmem
  · intro hemp
    refine eq_empty_iff_forall_notMem.2 fun ⟨p, q⟩ hpq => ?_
    obtain ⟨hcl, hng⟩ := hpq
    have hc : Corresponds (U : Set M) ψ p q := hP.corresponds_iff_mem_gluingC.2 hcl
    by_cases hpU : p ∈ (U : Set M)
    · have hq : q = ψ p := (corresponds_iff_eq_of_mem hP.continuousOn hpU).1 hc
      exact hng ⟨⟨p, hpU⟩, by rw [hq]; rfl⟩
    · have hmem : p ∈ correspondingSet (U : Set M) ψ :=
        ⟨⟨mem_closure_of_corresponds hc, by rwa [U.isOpen.interior_eq]⟩, q, hc⟩
      rw [hemp] at hmem; exact hmem

end CGHDData

variable (s) in
/-- **Sbierski Lemma 3.11 on an admissible spacetime** (future side): `M` globally hyperbolic,
`U` a globally hyperbolic open set with `S` a Cauchy surface of `U` and of `M`, `p ∈ ∂U`
satisfying (3.10): every neighbourhood `W` of `p` contains `J⁻(q) ∩ Uᶜ ∩ J⁺(S)` for some
`q ≫ p`. Every hypothesis of the model-free lemma is derived from A2 (`kSide_future`,
`mem_Zplus`, causal convexity of the Cauchy inclusion `U ⊆ M`). -/
theorem exists_lt_Jminus_compl_subset_of_cauchy (U : Opens M) (S : Set M)
    (hG : (𝔊.causality s).GloballyHyperbolic) (hGU : (𝔊.causality s).GloballyHyperbolicOn U)
    (hSU : S ⊆ U) (hS : (𝔊.causality s).IsCauchySurface S)
    (hSU' : (𝔊.causality s).IsCauchySurfaceOn U S) {p : M} (hp : p ∈ frontier (U : Set M))
    (h310 : (𝔊.causality s).Jminus ⊤ {p} ∩ frontier (U : Set M) ∩
      (𝔊.causality s).Jplus ⊤ S = {p}) {W : Set M} (hW : W ∈ 𝓝 p) :
    ∃ q, (𝔊.causality s).lt ⊤ p q ∧
      (𝔊.causality s).Jminus ⊤ {q} ∩ (U : Set M)ᶜ ∩ (𝔊.causality s).Jplus ⊤ S ⊆ W := by
  have hA := 𝔊.singularFlatAxioms s
  have kM := kSide_future s hG hS
  have hcv := IsCauchyInclusion.causallyConvexIn ⟨le_top, hGU, hG, S, hSU, hSU', hS⟩
    hA.causallyArcConnected (Causality.curvesExtendOn_top.2 (𝔊.curvesExtend s hG))
  exact Causality.exists_lt_Jminus_compl_subset hcv hSU (hA.mem_Zplus p) kM.isClosed_Jplus
    kM.isClosed_Jminus (kM.dense p) kM.separates kM.isCompact hp h310.subset hW

variable (s) in
/-- **Sbierski Lemma 3.11, past side**, at a **regular** `p` (`p ∉ sing₀`): every neighbourhood
`W` of `p` contains `J⁺(q) ∩ Uᶜ ∩ J⁻(S)` for some `q ≪ p`. At a BTZ point `I⁻(p) = ∅`
(`Iminus_eq_empty`, a field of the corrected bundle), so the conclusion `∃ q ≪ p` is
**unsatisfiable** there: the past lemma without `p ∉ sing₀` would assert that no BTZ boundary
point satisfies its hypotheses (past (3.10), `U` GH) — not settled here; no BTZ configuration
satisfying them is exhibited (R4, finding). -/
theorem exists_lt_Jplus_compl_subset_past (U : Opens M) (S : Set M)
    (hG : (𝔊.causality s).GloballyHyperbolic) (hGU : (𝔊.causality s).GloballyHyperbolicOn U)
    (hSU : S ⊆ U) (hS : (𝔊.causality s).IsCauchySurface S)
    (hSU' : (𝔊.causality s).IsCauchySurfaceOn U S) {p : M} (hp : p ∈ frontier (U : Set M))
    (hreg : p ∉ 𝔊.sing s 0)
    (h310 : (𝔊.causality s).Jplus ⊤ {p} ∩ frontier (U : Set M) ∩
      (𝔊.causality s).Jminus ⊤ S = {p}) {W : Set M} (hW : W ∈ 𝓝 p) :
    ∃ q, (𝔊.causality s).lt ⊤ q p ∧
      (𝔊.causality s).Jplus ⊤ {q} ∩ (U : Set M)ᶜ ∩ (𝔊.causality s).Jminus ⊤ S ⊆ W := by
  have hA := 𝔊.singularFlatAxioms s
  have kM := kSide_past s hG hS
  have hcv := IsCauchyInclusion.causallyConvexIn ⟨le_top, hGU, hG, S, hSU, hSU', hS⟩
    hA.causallyArcConnected (Causality.curvesExtendOn_top.2 (𝔊.curvesExtend s hG))
  exact Causality.exists_lt_Jminus_compl_subset (C := (𝔊.causality s).dual)
    (Causality.dual_causallyConvexIn.2 hcv) hSU ((hA.mem_Zminus_iff p).2 hreg)
    kM.isClosed_Jplus kM.isClosed_Jminus (kM.dense p) kM.separates kM.isCompact hp h310.subset hW

end LevelA

/-! ### Developments: Thm 3.6, Thm 3.13, the gluing along the MCGHD -/

section Dev

variable {𝔊 : Geometry.{u}} {M₀ : Type u} [TopologicalSpace M₀] {s₀ : 𝔊.Str M₀}
  {N₁ N₂ : Dev 𝔊.toPreGeometry s₀}

/-- **A common Cauchy development with injective morphism is in package 5's CGHD setting**, with
`S = ι₁(Σ)` for a Cauchy surface `Σ` of `M₀`. -/
theorem IsCGHD.cghdData {W : Opens N₁.carrier} {f : N₁.carrier → N₂.carrier}
    (h : IsCGHD N₁ N₂ W f) (hinj : InjOn f W) {S : Set M₀}
    (hS : (𝔊.causality s₀).IsCauchySurface S) :
    CGHDData 𝔊 N₁.str N₂.str W f (N₁.emb '' S) := by
  have himg : f '' (N₁.emb '' S) = N₂.emb '' S := by rw [← image_comp, h.2.2]
  have hSsub : N₁.emb '' S ⊆ (W : Set N₁.carrier) :=
    fun _ hx => h.1.1 (N₁.image_subset_range S hx)
  have hSW := N₁.isCauchyEmbedding.isCauchySurfaceOn_of_isCauchyInclusion h.1 hS
  exact
    { isMor := h.2.1
      injOn := hinj
      gh := N₁.causality_globallyHyperbolic
      gh' := N₂.causality_globallyHyperbolic
      ghOn := h.1.2.2.1
      ghOn' := (h.isCauchyInclusion_image hinj).2.2.1
      subset := hSsub
      cauchy := N₁.isCauchyEmbedding.isCauchySurface_image hS
      cauchyOn := hSW
      cauchy' := by rw [himg]; exact N₂.isCauchyEmbedding.isCauchySurface_image hS
      cauchyOn' := ((𝔊.isEMorphismOn_of_isMor h.2.1).isCauchySurfaceOn_image_iff hinj le_rfl rfl
        hSsub).1 hSW }

/-- **Sbierski Theorem 3.6** (`prop:Cauchy_non_max`, `ETT.tex:2178`): a common Cauchy development
`(W, f)` (`f` injective) with corresponding boundary points has a **strictly larger** common
Cauchy development `(W', f')`, `f' = f` on `W`. In particular `W` is not the MCGHD. -/
theorem IsCGHD.exists_lt {W : Opens N₁.carrier} {f : N₁.carrier → N₂.carrier}
    (h : IsCGHD N₁ N₂ W f) (hinj : InjOn f W)
    (hC : (correspondingSet (W : Set N₁.carrier) f).Nonempty) :
    ∃ (W' : Opens N₁.carrier) (f' : N₁.carrier → N₂.carrier), W < W' ∧ IsCGHD N₁ N₂ W' f' ∧
      EqOn f' f W := by
  obtain ⟨S, hS, -⟩ := N₁.isCauchyEmbedding.exists_cauchy
  obtain ⟨W', f', hlt, hmor, heq, hgh, hcy⟩ := (h.cghdData hinj hS).exists_extension hC
  refine ⟨W', f', hlt, ⟨⟨h.1.1.trans hlt.le, h.1.2.1, hgh, N₁.emb '' S, N₁.image_subset_range S,
    N₁.isCauchySurfaceOn_range hS, hcy⟩, hmor, ?_⟩, heq⟩
  funext x
  show f' (N₁.emb x) = N₂.emb x
  rw [heq (h.1.1 (N₁.emb_mem_range x))]
  exact congrFun h.2.2 x

/-- **Sbierski Theorem 3.13**: the MCGHD of two developments has **no corresponding boundary
points** (`prop:ppcm_Cauchy`'s "Hence `C = ∅`", `ETT.tex:2323`), given the injectivity of its
morphism (Lemma 3.3; `correspondingSet_mcghd_eq_empty_of_timeFunction`). -/
theorem correspondingSet_mcghd_eq_empty [ConnectedSpace M₀]
    (hinj : InjOn (mcghdMap N₁ N₂) (mcghdOpens N₁ N₂)) :
    correspondingSet (mcghdOpens N₁ N₂ : Set N₁.carrier) (mcghdMap N₁ N₂) = ∅ := by
  by_contra hne
  obtain ⟨W', f', hlt, hW', -⟩ :=
    (isCGHD_mcghd (N₁ := N₁) (N₂ := N₂)).exists_lt hinj (nonempty_iff_ne_empty.2 hne)
  exact lt_irrefl _ (lt_of_lt_of_le hlt (le_mcghdOpens hW'))

/-- **Theorem 3.13 with a time function on `N₁`** (the hypothesis of package 4's Lemma 3.3). -/
theorem correspondingSet_mcghd_eq_empty_of_timeFunction [ConnectedSpace M₀]
    (hT : (𝔊.causality N₁.str).HasTimeFunction) :
    correspondingSet (mcghdOpens N₁ N₂ : Set N₁.carrier) (mcghdMap N₁ N₂) = ∅ :=
  correspondingSet_mcghd_eq_empty ((isCGHD_mcghd (N₁ := N₁) (N₂ := N₂)).injOn hT)

/-- **The gluing of two developments along their MCGHD is Hausdorff** (Sbierski, proof of Thm 2.7:
"Theorem 3.13 will yield that this space is Hausdorff"; `prop:ppcm_Cauchy`, `ETT.tex:2323–2324`):
`(N₁ ⊔ N₂)/(x ∼ ψ x, x ∈ U)` is `T2`. -/
theorem t2Space_gluing_mcghd [ConnectedSpace M₀]
    (hinj : InjOn (mcghdMap N₁ N₂) (mcghdOpens N₁ N₂)) :
    T2Space (Gluing (Subtype.val : mcghdOpens N₁ N₂ → N₁.carrier)
      (mcghdMap N₁ N₂ ∘ (Subtype.val : mcghdOpens N₁ N₂ → N₁.carrier))) := by
  haveI : Nonempty N₁.carrier := ⟨N₁.emb (Classical.arbitrary M₀)⟩
  obtain ⟨S, hS, -⟩ := N₁.isCauchyEmbedding.exists_cauchy
  exact (((isCGHD_mcghd (N₁ := N₁) (N₂ := N₂)).cghdData hinj hS).t2Space_gluing_iff).2
    (correspondingSet_mcghd_eq_empty hinj)

/-- The gluing along the MCGHD is Hausdorff, with a time function on `N₁`. -/
theorem t2Space_gluing_mcghd_of_timeFunction [ConnectedSpace M₀]
    (hT : (𝔊.causality N₁.str).HasTimeFunction) :
    T2Space (Gluing (Subtype.val : mcghdOpens N₁ N₂ → N₁.carrier)
      (mcghdMap N₁ N₂ ∘ (Subtype.val : mcghdOpens N₁ N₂ → N₁.carrier))) :=
  t2Space_gluing_mcghd ((isCGHD_mcghd (N₁ := N₁) (N₂ := N₂)).injOn hT)

end Dev

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
