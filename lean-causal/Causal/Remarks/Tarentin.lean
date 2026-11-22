import Causal.SingularFlat
import Causal.Model.Massive
import Causal.LinesReachable

/-!
# Remarks on tarentin spacetimes, `K^± = I^±` on Lorentzian manifolds, and two remarks on proofs

Target `T-ett-unanchored` (2026-11-20). No label is marked (SCOPE): Lorentzian manifolds and the
Misner singularity are not in the library; the `E₀` model is (`Causal.E0`), read under OQ-34 and
OQ-35. Cited, unmarked: `rem:tarentin_exemples` — `ETT.tex:688`,
`cexemple:misner_tarentin` — `ETT.tex:1368`, `cor:K_lorentzien` — `ETT.tex:884`,
`rem:manifolds_specialises_brunswic_cauchy` — `ETT.tex:898`, `rem:proof_uses_neither_causal` —
`ETT.tex:1171`, `rem:recursion_these` — `ETT.tex:1140`.
`rem:terminology_borrowed_archytas_tarentum` (`ETT.tex:681`) makes no mathematical assertion
(etymology and a reading of `def:tarentin_spacetime`) and has no declaration of its own (SCOPE).

> Lorentzian manifolds are tarentin, and so is every $\mass{\geq0}$-manifold (Remark
> \ref{rem:sing_tarentin}). The hypothesis is nevertheless not innocent: a singular flat spacetime
> containing a Misner singularity fails it (Counter-example \ref{cexemple:misner_tarentin}).
> (`ETT.tex:689–691`)

> Consider a singular $\mass{}$-manifold $M$ containing a Misner singularity, as constructed in
> \cite{thesis}. The causality extends to all of $M$, but every causal curve issued from a
> singular point is future directed, so a singular point has no past. Hence $M$ is not tarentin.
> (`ETT.tex:1369–1371`)

> Let $M$ be a Lorentzian manifold. Then $\forall p\in M, K^\pm(p)=I^\pm(p).$ [Proof:] A
> Lorentzian manifold is a tarentin topological spacetime whose causality is absolutely minimal,
> and by Remark \ref{rem:lorentz_tarentin} each of its points is strongly tarentin in the future
> and in the past. Proposition \ref{prop:tarentin_fort_K} and its analogue for $K^+$ give the
> conclusion. (`ETT.tex:884–892`)

> For $\mass{\geq0}$-manifolds this specialises to \cite[Prop.~1.10]{brunswic2021cauchy}, which
> states the injectivity of $x\mapsto I^+(x)$ on all of $M$ and of $x\mapsto I^-(x)$ on
> $M\setminus \sing_0(M)$ --- the two domains being exactly $Z^+(M)$ and $Z^-(M)$ in the present
> language. (`ETT.tex:899–900`)

> The proof uses neither causal curves, nor $I^\pm$, nor causal plainness. [...] The classical
> formulation is unavailable here, since $I^+(q)$ may be empty. (`ETT.tex:1172–1175`)

> The argument above uses neither the recursion $K^{-,(0)}(A)=K^-_{\U_1}(A)$,
> $K^{-,(n+1)}(A)=K^{-,(n)}(A)\cup K^-_{\U_{n+1}}\left(K^{-,(n)}(A)\cap \U_{n+1}\right)$ of
> \cite{thesis}, nor the further hypothesis made there. That recursion is in any case mis-seeded:
> if $A\subset \U_5$ and $A\cap\left(\U_1\cup\cdots\cup \U_4\right)=\emptyset$, then every
> $K^{-,(n)}(A)$ is empty, since $A$ enters the recursion only through $\U_1$.
> (`ETT.tex:1141–1145`)

## What is proved (no `sorry` in this file)

* `cexemple:misner_tarentin`, the mechanism: `not_tarentin_of_no_past` (a point with no past near
  it whose causal future is not a neighbourhood of it), `not_tarentin_of_Jminus_eq`, its hypotheses
  witnessed (`sourceLine_no_past`, non-local). **Finding**: "no past" alone does not exclude
  tarentin — proved in Lean for non-local causalities only (`no_past_not_enough`, on `radialLine`);
  for the paper's local causalities by a planar argument, unproved here (SCOPE).
* `rem:tarentin_exemples`: assembly `tarentin_exemples` (Minkowski, `E_α`, the structure, and the
  mechanism above).
* `cor:K_lorentzien`: `K_lorentzien` (absolutely minimal T1, `I^±(p) ≠ ∅`, **causally plain**),
  `K_eq_I_of_pushUp` (push-up in place of plainness), `minkowski_K_lorentzien`.
* `rem:manifolds_specialises_brunswic_cauchy`: `SingularFlatAxioms.FZenon_injectif`.
* `rem:proof_uses_neither_causal`: `lightlikeLine_relation_fermee` (the hypotheses of
  `prop:relation_fermee`, `Causality.isClosed_le`, hold where no `q` is in `closure I^+(q)`).
* `rem:recursion_these`: `thesisRecursion` (the recursion, transcribed), `thesisRecursion_eq_empty`
  (`A ∩ U₁ = ∅` suffices), `recursion_these` (as printed), `recursion_these_misseeded` (with
  `K^-(A) ≠ ∅`).

## Hypothesis checklist

| paper | here |
|---|---|
| Lorentzian manifold (`cor:K_lorentzien`) | ⚠ strengthened: absolutely minimal, T1, first countable, `I^±(p) ≠ ∅` everywhere, and **causally plain** (the proof's `prop:tarentin_fort_K` asks it; the proof does not mention it) or push-up; instance `minkowski n` |
| — tarentin (the proof) | ⚠ weakened: not used |
| Misner singularity (`cexemple:misner_tarentin`) | ⚠ strengthened: a point `x` with no past near it **and** `J^+(x)` not a neighbourhood of `x` (the construction of the thesis is not in the library) |
| `E_{≥0}`-manifold | ⚠ strengthened: `SingularFlatAxioms C sing` (named model facts, kb/0012) |
| `rem:manifolds_specialises…`: injectivity | ✓ under strong causality, as in `prop:FZenon_injectif` |
| `rem:recursion_these`: `A ⊂ U₅`, `A ∩ (U₁ ∪ ⋯ ∪ U₄) = ∅` | ⚠ weakened: `A ∩ U₁ = ∅` suffices (`thesisRecursion_eq_empty`); the printed form is `recursion_these` |

## SCOPE (disclosed)

* `cexemple:misner_tarentin`. The Misner singularity of the thesis is not constructed. What is
  proved is the mechanism the counter-example names, with the hypothesis it needs: tarentin at
  `x` gives `p ≤ x ≤ q` in any neighbourhood with `x ∈ Int J(p,q)`; if `x` has no past near it,
  `p = x`, so `J^+(x)` is a neighbourhood of `x`. The hypotheses of `not_tarentin_of_Jminus_eq`
  are satisfiable (`sourceLine_no_past`, `ℝ` with `y ≤ z ↔ y = z ∨ 0 ≤ y < z`, non-local).
  **Finding:** "a singular point has no past. Hence `M` is not tarentin" (`ETT.tex:1370–1371`) is
  not a valid inference by itself. *In Lean, for non-local causalities only* (kb/0014, kb/0019):
  `radialLine` (on `ℝ`, `y ≤ z ↔ y = z ∨ |y| < |z|`, `y ≪ z ↔ |y| < |z|`, built with
  `Causality.ofRelation`) is causal and tarentin with `J^-(0) = {0}` (`no_past_not_enough`). It is
  tarentin at `0` *because* it is non-local: its relation `-s ≤ t`, `|s| < |t|`, crosses the
  origin, which no curve of `ℝ` does; the local line with the same time `|·|` is not tarentin at
  `0`. *For the paper's local causalities* the finding rests on a planar argument (the auditor's,
  by hand, not formalized): on `ℝ²` let `x ≤_U y` iff `x = y` or a curve in `U` along which `|·|`
  strictly increases joins them, and `x ≪_U y` iff such a curve does. It is causally
  arc-connected, hence absolutely minimal (`cor:causalement_connexe_minimal`), causal, and
  tarentin — at `0` take `p = 0`, `|q| = ε/2`, so that `J(0,q)` contains the open disc of radius
  `ε/2`; at `x ≠ 0` take `p = (1-t)x`, `q = (1+t)x` — with `J^-(0) = {0}` and `J^+(0) = ℝ²`. What
  the counter-example is missing is that the causal future of a Misner singular point is not a
  neighbourhood of it.
* `cor:K_lorentzien`. Lorentzian manifolds are not in the library (`def:maximal_chain`'s
  curation). The proof's chain is formalized abstractly; **finding**: the proof (`ETT.tex:889–891`)
  checks tarentin and absolute minimality, which `prop:tarentin_fort_K` assumes but does not need,
  and omits causal plainness, which it needs. For a smooth Lorentzian manifold plainness (push-up)
  is classical but must be cited; below Lipschitz regularity it can fail (`rem:pas_plat` (i),
  `rem:K_neq_I`), so "Lorentzian manifold" must be read with at least that regularity. Under
  push-up instead of plainness the conclusion holds too (`K_eq_I_of_pushUp`).
* `rem:terminology_borrowed_archytas_tarentum` reads tarentin as "every observer has a future and a
  past" (`ETT.tex:684–685`). Read weakly (`p ≤ x ≤ q` with `p, q` in any neighbourhood, `p = x`
  allowed) this is the definition. Read as `J^-(x) ≠ {x}` and `J^+(x) ≠ {x}` it does not follow
  from tarentin: in Lean for non-local causalities (`no_past_not_enough`, kb/0019), and for local
  ones by the planar argument above (unproved here).
* `rem:tarentin_exemples`. "Lorentzian manifolds are tarentin": instance `minkowski_tarentin`;
  "every `E_{≥0}`-manifold": the field `tarentin` of `SingularFlatAxioms` (`rem:sing_tarentin`,
  partial); the Misner clause: the mechanism above.
* `rem:manifolds_specialises_brunswic_cauchy` is curated `informal`; its assertion is checked
  anyway: under the structure `Z^+ = M`, `Z^- = M ∖ sing_0` (fields), and `prop:FZenon_injectif`
  gives the two injectivities. Prop. 1.10 of the cited paper is not read here.
* `rem:proof_uses_neither_causal` is a statement about a proof. Its formal counterpart: the
  library's `prop:relation_fermee` (`Causality.isClosed_le`) asks only tarentin and closed
  `J^±(x)` — no curve, no `I^±`, no plainness — and the lightlike line satisfies these hypotheses
  while `I^+(q) = ∅`, so `q ∉ closure I^+(q)` for every `q` (the classical hypothesis fails
  everywhere).
* `rem:recursion_these`. `K^-_{U}(A)` for `A ⊄ U` is read as `K^-_U(A ∩ U)` (a point outside
  `U` has empty past in `U`), the reading the remark's "A enters only through `U₁`" takes. The
  first sentence (the proof of `prop:mesure_dieckmann_topo` uses neither the recursion nor the
  thesis's hypothesis) is about a proof: the library's `mesure_dieckmann_topo_past`
  (`Causal.MeasureLocal`) is proved without either. The witness `recursion_these_misseeded`
  is the timelike line with `U₁ = ⋯ = U₄ = ]-∞,0[`, `U₅ = ℝ`, `A = {1}`: every `K^{-,(n)}(A)` is
  empty while `0 ∈ K^-(A)`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter

universe u

namespace Causality

variable {M : Type u} [TopologicalSpace M] {C : Causality M} {x : M}

/-! ### `cexemple:misner_tarentin` -/

/-- `cexemple:misner_tarentin`, the mechanism: a point with no past in some neighbourhood of it,
whose causal future is not a neighbourhood of it, forbids tarentin. -/
theorem not_tarentin_of_no_past (hpast : ∃ N ∈ 𝓝 x, ∀ p ∈ N, C.le ⊤ p x → p = x)
    (hJ : C.Jplus ⊤ {x} ∉ 𝓝 x) : ¬ C.Tarentin := by
  intro hT
  obtain ⟨N, hN, hNx⟩ := hpast
  obtain ⟨p, hpN, q, -, hxpq⟩ := hT x N hN
  have hpx : C.le ⊤ p x := (mem_diamond.1 (openDiamond_subset_diamond hxpq)).1
  have hpeq : p = x := hNx p hpN hpx
  subst hpeq
  exact hJ (mem_of_superset (isOpen_openDiamond.mem_nhds hxpq)
    (openDiamond_subset_diamond.trans diamond_subset_Jplus))

/-- `cexemple:misner_tarentin`, with "no past" read globally: `J^-(x) = {x}`. -/
theorem not_tarentin_of_Jminus_eq (hx : C.Jminus ⊤ {x} = {x}) (hJ : C.Jplus ⊤ {x} ∉ 𝓝 x) :
    ¬ C.Tarentin := by
  refine not_tarentin_of_no_past ⟨univ, univ_mem, fun p _ hp => ?_⟩ hJ
  have hmem : p ∈ C.Jminus ⊤ {x} := by simpa using hp
  rw [hx] at hmem
  exact hmem

end Causality

/-- `ℝ` with `y ≤ z ↔ y = z ∨ 0 ≤ y < z` and `y ≪ z ↔ 0 < y < z` in every open set
(`Causality.ofRelation`, not local: kb/0014). The origin has no past and its causal future is
`[0, ∞[`. -/
def sourceLine : Causality ℝ :=
  Causality.ofRelation (fun y z => y = z ∨ (0 ≤ y ∧ y < z)) (fun y z => 0 < y ∧ y < z)
    (fun _ => Or.inl rfl)
    (fun _ _ _ hxy hyz => by
      rcases hxy with rfl | ⟨h0, hxy⟩
      · exact hyz
      · rcases hyz with rfl | ⟨-, hyz⟩
        · exact Or.inr ⟨h0, hxy⟩
        · exact Or.inr ⟨h0, hxy.trans hyz⟩)
    (fun _ _ _ h₁ h₂ => ⟨h₁.1, h₁.2.trans h₂.2⟩)
    (fun _ _ h => Or.inr ⟨h.1.le, h.2⟩)
    (fun y => by
      by_cases hy : 0 < y
      · have h : {z : ℝ | 0 < y ∧ y < z} = Ioi y := by ext z; simp [hy]
        rw [h]
        exact isOpen_Ioi
      · simp [hy])
    (fun _ => isOpen_Ioo)

theorem sourceLine_le_top {y z : ℝ} : sourceLine.le ⊤ y z ↔ y = z ∨ (0 ≤ y ∧ y < z) :=
  ⟨fun h => h.2.2, fun h => ⟨trivial, trivial, h⟩⟩

/-- **Witness of the hypotheses of `not_tarentin_of_Jminus_eq`** (kb/0011), at `x = 0` on
`sourceLine`: `J^-(0) = {0}` and `J^+(0) = [0, ∞[` is not a neighbourhood of `0`; hence the line is
not tarentin. -/
theorem sourceLine_no_past :
    sourceLine.Jminus ⊤ {0} = {0} ∧ sourceLine.Jplus ⊤ {0} ∉ 𝓝 (0 : ℝ) ∧
      ¬ sourceLine.Tarentin := by
  have hJm : sourceLine.Jminus ⊤ {0} = {0} := by
    ext z
    rw [Precausality.mem_Jminus_singleton, sourceLine_le_top, mem_singleton_iff]
    constructor
    · rintro (h | ⟨h0, h⟩)
      · exact h
      · exact absurd (h0.trans_lt h) (lt_irrefl _)
    · exact Or.inl
  have hJp : sourceLine.Jplus ⊤ {0} ∉ 𝓝 (0 : ℝ) := by
    intro h
    obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.1 h
    have hm : -(ε / 2) ∈ Metric.ball (0 : ℝ) ε := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_neg, abs_of_pos (half_pos hε)]
      exact half_lt_self hε
    have h' := hb hm
    rw [Precausality.mem_Jplus_singleton, sourceLine_le_top] at h'
    rcases h' with h' | ⟨-, h'⟩ <;> linarith
  exact ⟨hJm, hJp, Causality.not_tarentin_of_Jminus_eq hJm hJp⟩

/-! ### "No past" alone does not refute tarentin: the radial line -/

/-- **The radial line**: `ℝ` with `y ≤ z ↔ y = z ∨ |y| < |z|` and `y ≪ z ↔ |y| < |z|` in every open
set (`Causality.ofRelation`, not local: kb/0014, kb/0019). Time is `|·|`, the origin is a source;
no curve of `ℝ` realises `-s ≤ t`, so this is not a topological spacetime in the paper's sheaf
sense. -/
def radialLine : Causality ℝ :=
  Causality.ofRelation (fun y z => y = z ∨ |y| < |z|) (fun y z => |y| < |z|)
    (fun _ => Or.inl rfl)
    (fun _ _ _ hxy hyz => by
      rcases hxy with rfl | hxy
      · exact hyz
      · rcases hyz with rfl | hyz
        · exact Or.inr hxy
        · exact Or.inr (hxy.trans hyz))
    (fun _ _ _ h₁ h₂ => h₁.trans h₂)
    (fun _ _ h => Or.inr h)
    (fun _ => isOpen_lt continuous_const continuous_abs)
    (fun _ => isOpen_lt continuous_abs continuous_const)

theorem radialLine_le_top {y z : ℝ} : radialLine.le ⊤ y z ↔ y = z ∨ |y| < |z| :=
  ⟨fun h => h.2.2, fun h => ⟨trivial, trivial, h⟩⟩

theorem radialLine_isCausal : radialLine.IsCausal := by
  intro y z hyz hzy
  rw [radialLine_le_top] at hyz hzy
  rcases hyz with h | h
  · exact h
  · rcases hzy with h' | h'
    · exact h'.symm
    · exact absurd (h.trans h') (lt_irrefl _)

/-- The origin has no past: `J^-(0) = {0}`. -/
theorem radialLine_Jminus_zero : radialLine.Jminus ⊤ {0} = {0} := by
  ext z
  rw [Precausality.mem_Jminus_singleton, radialLine_le_top, mem_singleton_iff]
  constructor
  · rintro (h | h)
    · exact h
    · simp at h
      exact absurd h (not_lt.2 (abs_nonneg z))
  · intro h
    exact Or.inl h

/-- The causal future of the origin is everything. -/
theorem radialLine_Jplus_zero : radialLine.Jplus ⊤ {0} = univ := by
  refine eq_univ_of_forall fun z => ?_
  rw [Precausality.mem_Jplus_singleton, radialLine_le_top]
  by_cases hz : z = 0
  · exact Or.inl hz.symm
  · exact Or.inr (by simpa using abs_pos.2 hz)

/-- The radial line is tarentin. -/
theorem radialLine_tarentin : radialLine.Tarentin := by
  intro x U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
  by_cases hx : x = 0
  · subst hx
    refine ⟨0, hball (Metric.mem_ball_self hε), ε / 2, hball ?_, ?_⟩
    · rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
      exact half_lt_self hε
    · have hsub : Ioo (-(ε / 2)) (ε / 2) ⊆ radialLine.diamond ⊤ 0 (ε / 2) := by
        intro z hz
        rw [Causality.mem_diamond, radialLine_le_top, radialLine_le_top]
        refine ⟨?_, Or.inr ?_⟩
        · by_cases hz0 : z = 0
          · exact Or.inl hz0.symm
          · exact Or.inr (by simpa using abs_pos.2 hz0)
        · rw [abs_of_pos (half_pos hε)]
          exact abs_lt.2 hz
      exact mem_interior_iff_mem_nhds.2
        (mem_of_superset (Ioo_mem_nhds (by linarith) (by linarith)) hsub)
  · have hx0 : 0 < |x| := abs_pos.2 hx
    set t : ℝ := min (1 / 2) (ε / (2 * |x|)) with ht
    have ht0 : 0 < t := lt_min (by norm_num) (div_pos hε (by positivity))
    have ht1 : t < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    have htε : |x| * t < ε := by
      have hle : t ≤ ε / (2 * |x|) := min_le_right _ _
      calc |x| * t ≤ |x| * (ε / (2 * |x|)) := mul_le_mul_of_nonneg_left hle hx0.le
        _ = ε / 2 := by field_simp
        _ < ε := half_lt_self hε
    have hp : |x * (1 - t)| = |x| * (1 - t) := by
      rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 1 - t)]
    have hq : |x * (1 + t)| = |x| * (1 + t) := by
      rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 1 + t)]
    refine ⟨x * (1 - t), hball ?_, x * (1 + t), hball ?_, ?_⟩
    · rw [Metric.mem_ball, Real.dist_eq, show x * (1 - t) - x = -(x * t) by ring, abs_neg,
        abs_mul, abs_of_pos ht0]
      exact htε
    · rw [Metric.mem_ball, Real.dist_eq, show x * (1 + t) - x = x * t by ring, abs_mul,
        abs_of_pos ht0]
      exact htε
    · have hO : IsOpen {z : ℝ | |x * (1 - t)| < |z| ∧ |z| < |x * (1 + t)|} :=
        (isOpen_lt continuous_const continuous_abs).inter
          (isOpen_lt continuous_abs continuous_const)
      have hsub : {z : ℝ | |x * (1 - t)| < |z| ∧ |z| < |x * (1 + t)|} ⊆
          radialLine.diamond ⊤ (x * (1 - t)) (x * (1 + t)) := by
        intro z hz
        rw [Causality.mem_diamond, radialLine_le_top, radialLine_le_top]
        exact ⟨Or.inr hz.1, Or.inr hz.2⟩
      have hxmem : x ∈ {z : ℝ | |x * (1 - t)| < |z| ∧ |z| < |x * (1 + t)|} := by
        refine ⟨?_, ?_⟩
        · rw [hp]; nlinarith
        · rw [hq]; nlinarith
      exact mem_interior_iff_mem_nhds.2 (mem_of_superset (hO.mem_nhds hxmem) hsub)

/-- **Finding on `cexemple:misner_tarentin`, for non-local causalities** (kb/0014, kb/0019): a
point with no past does not by itself refute tarentin. The radial line is causal and tarentin,
its origin has `J^-(0) = {0}`, and (as `not_tarentin_of_no_past` requires it not to be) `J^+(0)`
is a neighbourhood of `0`. It is tarentin at `0` only because it is not local (its relation crosses
the origin); for local causalities see the planar argument of the module's SCOPE (unproved). -/
theorem no_past_not_enough :
    ∃ C : Causality ℝ, C.Tarentin ∧ C.IsCausal ∧ C.Jminus ⊤ {0} = {0} ∧
      C.Jplus ⊤ {0} ∈ 𝓝 0 :=
  ⟨radialLine, radialLine_tarentin, radialLine_isCausal, radialLine_Jminus_zero,
    radialLine_Jplus_zero ▸ univ_mem⟩

/-! ### `rem:tarentin_exemples` -/

/-- `rem:tarentin_exemples`, assembled: Minkowski space (every dimension) and `E_α`, `α > 0`, are
tarentin; an `E_{≥0}`-manifold is tarentin through the field `tarentin` (`rem:sing_tarentin`); and
the mechanism of `cexemple:misner_tarentin`. -/
theorem tarentin_exemples :
    (∀ n : ℕ, (minkowski n).Tarentin) ∧ (∀ (α : ℝ) [Fact (0 < α)], (massive α).Tarentin) ∧
    (∀ {M : Type u} [TopologicalSpace M] (C : Causality M) (sing : ℝ → Set M),
      C.SingularFlatAxioms sing → C.Tarentin) ∧
    (∀ {M : Type u} [TopologicalSpace M] (C : Causality M) (x : M),
      C.Jminus ⊤ {x} = {x} → C.Jplus ⊤ {x} ∉ 𝓝 x → ¬ C.Tarentin) :=
  ⟨fun _ => minkowski_tarentin, fun _ _ => massive_tarentin, fun _ _ h => h.tarentin,
    fun _ _ hx hJ => Causality.not_tarentin_of_Jminus_eq hx hJ⟩

/-! ### `cor:K_lorentzien` -/

namespace Causality

variable {M : Type u} [TopologicalSpace M] {C : Causality M}

/-- `cor:K_lorentzien`, the proof's chain, abstractly: on a causally plain, absolutely minimal T1
spacetime with a countable basis of neighbourhoods in which every point has a non-empty
chronological future and past, `K^±(p) = I^±(p)` for every `p` (`prop:tarentin_fort_K` both ways,
every point being strongly tarentin both ways by `rem:absolutely_minimal_topological_spacetime`). -/
theorem K_lorentzien [FirstCountableTopology M] [T1Space M] (hA : C.AbsolutelyMinimal)
    (hP : C.CausallyPlain)
    (hI : ∀ p, (C.Iplus ⊤ {p}).Nonempty ∧ (C.Iminus ⊤ {p}).Nonempty) (p : M) :
    C.Kplus ⊤ {p} = C.Iplus ⊤ {p} ∧ C.Kminus ⊤ {p} = C.Iminus ⊤ {p} :=
  ⟨Kplus_eq_Iplus_of_mem_Zplus hP ((AbsolutelyMinimal.mem_Zplus_iff hA).2 (hI p).1),
    Kminus_eq_Iminus_of_mem_Zminus hP ((AbsolutelyMinimal.mem_Zminus_iff hA).2 (hI p).2)⟩

/-- `cor:K_lorentzien` with push-up (`defi:pushup`) in place of causal plainness. -/
theorem K_eq_I_of_pushUp [FirstCountableTopology M] [T1Space M] (hA : C.AbsolutelyMinimal)
    (hP : C.PushUp)
    (hI : ∀ p, (C.Iplus ⊤ {p}).Nonempty ∧ (C.Iminus ⊤ {p}).Nonempty) (p : M) :
    C.Kplus ⊤ {p} = C.Iplus ⊤ {p} ∧ C.Kminus ⊤ {p} = C.Iminus ⊤ {p} :=
  ⟨PushUp.Kplus_eq_Iplus hP ((AbsolutelyMinimal.mem_Zplus_iff hA).2 (hI p).1),
    PushUp.Kminus_eq_Iminus hP ((AbsolutelyMinimal.mem_Zminus_iff hA).2 (hI p).2)⟩

end Causality

/-- `cor:K_lorentzien` on Minkowski space `ℝ^{1,n}`, every `n`. -/
theorem minkowski_K_lorentzien (n : ℕ) (p : Minkowski n) :
    (minkowski n).Kplus ⊤ {p} = (minkowski n).Iplus ⊤ {p} ∧
      (minkowski n).Kminus ⊤ {p} = (minkowski n).Iminus ⊤ {p} :=
  ⟨staticCausality.Kplus_eq_Iplus {p}, staticCausality.Kminus_eq_Iminus {p}⟩

/-! ### `rem:manifolds_specialises_brunswic_cauchy` -/

namespace Causality

variable {M : Type u} [TopologicalSpace M] {C : Causality M} {sing : ℝ → Set M}

/-- `rem:manifolds_specialises_brunswic_cauchy`: on a strongly causal `E_{≥0}`-manifold (the
structure), `Z^+(M) = M`, `Z^-(M) = M ∖ sing_0(M)`, and `prop:FZenon_injectif` reads: `x ↦ I^+(x)`
is injective on `M`, `x ↦ I^-(x)` on `M ∖ sing_0(M)`. -/
theorem SingularFlatAxioms.FZenon_injectif (h : C.SingularFlatAxioms sing)
    (hSC : C.StronglyCausal) :
    C.Zplus = univ ∧ C.Zminus = (sing 0)ᶜ ∧ InjOn (fun x => C.Iplus ⊤ {x}) univ ∧
      InjOn (fun x => C.Iminus ⊤ {x}) (sing 0)ᶜ := by
  haveI := h.t2
  have hZp : C.Zplus = univ := eq_univ_of_forall h.mem_Zplus
  have hZm : C.Zminus = (sing 0)ᶜ := Set.ext h.mem_Zminus_iff
  refine ⟨hZp, hZm, ?_, ?_⟩
  · rw [← hZp]
    exact Iplus_injOn_Zplus hSC
  · rw [← hZm]
    exact Iminus_injOn_Zminus hSC

end Causality

/-! ### `rem:proof_uses_neither_causal` -/

theorem lightlikeLine_Jplus_top (x : ℝ) : lightlikeLine.Jplus ⊤ {x} = Ici x := by
  ext z
  simp

theorem lightlikeLine_Jminus_top (x : ℝ) : lightlikeLine.Jminus ⊤ {x} = Iic x := by
  ext z
  simp

/-- The lightlike line is tarentin (its causal relation is the one of the timelike line). -/
theorem lightlikeLine_tarentin : lightlikeLine.Tarentin := by
  intro x U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
  refine ⟨x - ε / 2, hball ?_, x + ε / 2, hball ?_, ?_⟩
  · rw [Metric.mem_ball, Real.dist_eq, show x - ε / 2 - x = -(ε / 2) by ring, abs_neg,
      abs_of_pos (half_pos hε)]
    exact half_lt_self hε
  · rw [Metric.mem_ball, Real.dist_eq, show x + ε / 2 - x = ε / 2 by ring,
      abs_of_pos (half_pos hε)]
    exact half_lt_self hε
  · have hd : lightlikeLine.diamond ⊤ (x - ε / 2) (x + ε / 2) = Icc (x - ε / 2) (x + ε / 2) := by
      rw [Causality.diamond, lightlikeLine_Jminus_top, lightlikeLine_Jplus_top]
      ext z
      simp [and_comm]
    show x ∈ interior (lightlikeLine.diamond ⊤ (x - ε / 2) (x + ε / 2))
    rw [hd, interior_Icc]
    exact ⟨by linarith, by linarith⟩

/-- `rem:proof_uses_neither_causal`, its formal content: the hypotheses of
`prop:relation_fermee` (`Causality.isClosed_le`: tarentin, `J^±(x)` closed — no curve, no `I^±`,
no plainness) hold on the lightlike line, where `I^+(q) = ∅`, so the classical hypothesis
`q ∈ closure I^+(q)` fails at every `q`; and the conclusion holds there. -/
theorem lightlikeLine_relation_fermee :
    lightlikeLine.Tarentin ∧ (∀ x, IsClosed (lightlikeLine.Jplus ⊤ {x})) ∧
      (∀ x, IsClosed (lightlikeLine.Jminus ⊤ {x})) ∧
      (∀ q : ℝ, q ∉ closure (lightlikeLine.Iplus ⊤ {q})) ∧
      IsClosed {z : ℝ × ℝ | lightlikeLine.le ⊤ z.1 z.2} := by
  have hJp : ∀ x, IsClosed (lightlikeLine.Jplus ⊤ {x}) := fun x => by
    rw [lightlikeLine_Jplus_top]; exact isClosed_Ici
  have hJm : ∀ x, IsClosed (lightlikeLine.Jminus ⊤ {x}) := fun x => by
    rw [lightlikeLine_Jminus_top]; exact isClosed_Iic
  refine ⟨lightlikeLine_tarentin, hJp, hJm, fun q => ?_,
    Causality.isClosed_le lightlikeLine_tarentin hJp hJm⟩
  have hI : lightlikeLine.Iplus ⊤ {q} = ∅ := by
    ext z
    simp
  rw [hI, closure_empty]
  exact notMem_empty q

/-! ### `rem:recursion_these` -/

namespace Causality

variable {M : Type u} [TopologicalSpace M] (C : Causality M)

/-- The recursion of the thesis, transcribed from `ETT.tex:1142–1143`: `U k` is the paper's `U_k`
(`k ≥ 1`; `U 0` is not used), `K^{-,(0)}(A) = K^-_{U₁}(A)` and
`K^{-,(n+1)}(A) = K^{-,(n)}(A) ∪ K^-_{U_{n+1}}(K^{-,(n)}(A) ∩ U_{n+1})`. -/
def thesisRecursion (U : ℕ → Opens M) (A : Set M) : ℕ → Set M
  | 0 => C.Kminus (U 1) A
  | n + 1 => thesisRecursion U A n ∪ C.Kminus (U (n + 1)) (thesisRecursion U A n ∩ U (n + 1))

variable {C}

/-- `K^-_U(A) = ∅` when `A` misses `U`: a point outside `U` has empty past in `U`. -/
theorem Kminus_eq_empty_of_inter_eq_empty {U : Opens M} {A : Set M} (hA : A ∩ U = ∅) :
    C.Kminus U A = ∅ := by
  refine subset_empty_iff.1 (Kminus_subset_Jminus.trans ?_)
  rintro y ⟨x, hxA, hyx⟩
  have hx : x ∈ A ∩ (U : Set M) := ⟨hxA, C.le_mem_right hyx⟩
  rw [hA] at hx
  exact hx

/-- `rem:recursion_these`, the strongest form: as soon as `A ∩ U₁ = ∅`, every `K^{-,(n)}(A)` is
empty. -/
theorem thesisRecursion_eq_empty {U : ℕ → Opens M} {A : Set M} (hA : A ∩ U 1 = ∅) :
    ∀ n, C.thesisRecursion U A n = ∅
  | 0 => Kminus_eq_empty_of_inter_eq_empty hA
  | n + 1 => by
    rw [thesisRecursion, thesisRecursion_eq_empty hA n, empty_inter, empty_union]
    exact Kminus_eq_empty_of_inter_eq_empty (empty_inter _)

/-- `rem:recursion_these`, as printed: if `A ⊂ U₅` and `A ∩ (U₁ ∪ ⋯ ∪ U₄) = ∅`, every
`K^{-,(n)}(A)` is empty. -/
theorem recursion_these {U : ℕ → Opens M} {A : Set M} (_hA5 : A ⊆ U 5)
    (hA : A ∩ ((U 1 : Set M) ∪ U 2 ∪ U 3 ∪ U 4) = ∅) (n : ℕ) :
    C.thesisRecursion U A n = ∅ := by
  refine thesisRecursion_eq_empty (subset_empty_iff.1 ?_) n
  rw [← hA]
  exact inter_subset_inter_right _ (by
    intro z hz
    exact Or.inl (Or.inl (Or.inl hz)))

end Causality

/-- `rem:recursion_these`, mis-seeding witnessed: on the timelike line, with
`U₁ = ⋯ = U₄ = ]-∞, 0[`, `U₅ = ℝ` and `A = {1}`, the hypotheses hold, every `K^{-,(n)}(A)` is
empty, and yet `K^-(A) ≠ ∅` (it contains `0`). -/
theorem recursion_these_misseeded :
    ∃ U : ℕ → Opens ℝ, ∃ A : Set ℝ, A ⊆ U 5 ∧ A ∩ ((U 1 : Set ℝ) ∪ U 2 ∪ U 3 ∪ U 4) = ∅ ∧
      (∀ n, timelikeLine.thesisRecursion U A n = ∅) ∧ (timelikeLine.Kminus ⊤ A).Nonempty := by
  let U : ℕ → Opens ℝ := fun k => if k = 5 then ⊤ else ⟨Iio 0, isOpen_Iio⟩
  have hU5 : U 5 = ⊤ := if_pos rfl
  have hUk : ∀ k, k ≠ 5 → (U k : Set ℝ) = Iio 0 := fun k hk => by
    simp only [U, if_neg hk]
    rfl
  have hA : ({1} : Set ℝ) ∩ ((U 1 : Set ℝ) ∪ U 2 ∪ U 3 ∪ U 4) = ∅ := by
    rw [hUk 1 (by norm_num), hUk 2 (by norm_num), hUk 3 (by norm_num), hUk 4 (by norm_num)]
    ext z
    simp only [mem_inter_iff, mem_singleton_iff, mem_union, mem_Iio, or_self, mem_empty_iff_false,
      iff_false, not_and]
    rintro rfl
    norm_num
  refine ⟨U, {1}, ?_, hA, Causality.recursion_these ?_ hA, ⟨0, ?_⟩⟩
  · rw [hU5]; exact subset_univ _
  · rw [hU5]; exact subset_univ _
  · rw [Causality.PushUp.Kminus_eq_Iminus timelikeLine_pushUp (timelikeLine_mem_Zminus 1)]
    simp

end Causal
