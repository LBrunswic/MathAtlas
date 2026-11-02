import Causal.LemmaKBare

/-!
# Lemma K, the bare form, reduced to two global facts — and why the long ray is not its counterexample

No label is marked. Lemma K is DEC-44's abstraction of a sentence Barbot asserts twice and never
proves (Rem 2.3 `clomax`, label at `GHFspace.tex:572` of the labelled file, the sentence at
l.576–578; §11, l.3537–3540); it carries no paper label. Its bare form is
`isCauchySurface_of_isLocallyCauchy` (`CausalScaffold.CompactCauchy`), a tagged `sorry`. DEC-92
asks it to be settled. **This file does not settle it**; it narrows it (SCOPE).

> Cauchy-compact GH spacetimes are automatically absolutely maximal. Indeed, any spacelike
> hypersurface in a given CGH spacetime is a Cauchy hypersurface. (Rem 2.3, l.576–578)

## What is proved

* **A Cauchy criterion with no curve extension** (`isCauchySurface_of_isAcausal_of_isOpen`): in a
  connected Hausdorff tarentin globally hyperbolic causally arc-connected spacetime with
  `J^±(p) ≠ {p}`, a compact non-empty **acausal** `Σ` with `J^+(Σ) ∪ J^-(Σ)` **open** is a Cauchy
  surface. Neither `CurvesExtend` nor local Cauchy-ness is used: the bare form's last step
  (every inextensible curve meets `Σ` once) costs nothing beyond its own hypotheses.
* **The exact residue, where curves extend** (`isCauchySurface_iff_of_curvesExtend`): under
  `CurvesExtend`, a compact non-empty `Σ` is a Cauchy surface **iff** it is acausal and
  `J^+(Σ) ∪ J^-(Σ) = M`. So the bare form (given `CurvesExtend`) is *equivalent* to: a compact
  connected locally Cauchy set is acausal and its causal future and past cover `M`.
* **The bad curve of a counterexample avoids every chart** (`exists_mem_of_inextensible_of_mem_chart`):
  an inextensible curve of `M` through a causally convex open `U` in which `Σ ∩ U` is Cauchy meets
  `Σ ∩ U`. No `CurvesExtend`. So an inextensible curve missing `Σ` misses every chart of `Σ`.
* **An inextensible curve has no upper bound** (`exists_not_le_of_inextensible`): an
  inextensible curve over `ℝ` leaves `J^-(q)` for every point `q` (the compact-diamond step of `Causal.CompactCauchy`). No
  `CurvesExtend`.
* **No inextensible curve, every set is Cauchy** (`isCauchySurfaceOn_of_forall_not_inextensible`):
  the vacuity behind the SCOPE's long-ray finding.

## Hypothesis checklist

| DEC-44 hypothesis | here |
|---|---|
| `C` a causality on `M`, `M` connected, `T2Space` | ✓ carried |
| `Tarentin`, `CausallyArcConnected`, `J^±(p) ≠ {p}`, `C.GloballyHyperbolic` | ✓ carried |
| `Σ` compact | ✓ carried |
| `Σ` connected, `IsLocallyCauchy` | ⚠ weakened in the criterion: neither is used |
| — | ⚠ strengthened in the criterion: `Σ` non-empty, acausal, `J^+(Σ) ∪ J^-(Σ)` open (not implied by the paper's hypotheses: that implication IS the open question) |
| — | ⚠ strengthened, named (kb/0012), in the characterisation only: `C.CurvesExtend` |
| second countability (`def:category_topological_spacetimes`, `ETT.tex:255`) | not carried, here or in the bare form |

## SCOPE (disclosed)

* **Verdict on DEC-92: not settled.** Neither a proof nor a counterexample of the bare form was
  reached. What remains is exactly two global facts, both proved in `Causal.LemmaKBare` from the
  openness of the strict causal future and past of `Σ` (plus `CurvesExtend`), and open in ETT
  generality: (1) a compact connected locally Cauchy `Σ` is **acausal**; (2) `J^+(Σ) ∪ J^-(Σ)` is
  **open** (it is closed by global hyperbolicity, and by `CurvesExtend` it contains every chart of
  `Σ`). Proving (1) and (2) proves the bare form in full generality (the criterion needs nothing
  else); under `CurvesExtend` the bare form is *equivalent* to (1) and (2). Without
  `CurvesExtend` the criterion is sufficient only: a `Σ` failing (1) or (2) is not by itself a
  counterexample to Lemma K.
* **The bare form does not carry second countability.** ETT's spacetimes are second countable
  Hausdorff (`ETT.tex:255`); the bare Lean statement asks `T2Space` and `ConnectedSpace` only, so a
  non-second-countable witness would refute the Lean statement, not ETT's.
* **The long ray, `CurvesExtend`'s conjectured counterexample (`Causal.CurvesExtend`, SCOPE), is
  not a counterexample to Lemma K** (argument, not formalised: the long ray is not in mathlib);
  that conjecture against `CurvesExtend` stands, and is used here. With its order causality the
  long ray has no inextensible causal curve, so every subset is a Cauchy surface and the bare form holds there
  vacuously (`isCauchySurfaceOn_of_forall_not_inextensible`). A counterexample breaking
  `CurvesExtend` must therefore mix: an open `U` with no `U`-inextensible curve (then any
  `Σ ⊆ U` is locally Cauchy for free) and, elsewhere, an inextensible curve of `M` — which by
  `exists_mem_of_inextensible_of_mem_chart` never enters `U`, and by
  `exists_not_le_of_inextensible` has no point of `M` above it (stated for curves over `ℝ`; any
  inextensible curve after `reparam`; "nor below" is the dual, via
  `exists_not_mem_Jplus_of_isCompact`, not stated here). Every two-dimensional
  null-coordinate design tried (`H × H` with `H = ℝ ∪ long tail`, minus a closed set, or `ℝ²`
  glued to a long quadrant) puts a point of the long region above the inextensible curves, or
  makes a diamond non-compact at a removed set; none satisfies global hyperbolicity. A
  non-metrizable surface in which the long region is causally "beside" the real one is not
  excluded, and was not found.
* **What a second-countable proof of `CurvesExtend` would need** (argument): in a second countable
  space with closed `J^+(x)`, a strictly increasing well-ordered causal chain is countable (the
  closed sets `J^+(e_α)` strictly decrease, and a strictly monotone well-ordered family of closed
  sets is countable). That kills the long-ray mechanism, but `CurvesExtend` would still need a
  Zorn step over curves without a time function, and fact (2) above does not follow from
  `CurvesExtend` alone: the BTZ case (`Z^-` fails, `J^+(Σ) ∖ Σ ≠ I^+(Σ)`) is where it is genuinely
  open (`Causal.LemmaKBare`, SCOPE).
* Non-vacuity: on the timelike line, `Σ = {0}` satisfies the criterion's hypotheses
  (`timelikeLine_reduction_hypotheses`, through the characterisation) and the criterion applies
  (`timelikeLine_isCauchySurface_zero_of_reduction`).
* gx contract (a)–(f): not applicable; no length, metric or Lipschitz graph is defined here.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Function

universe u

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable {C : Causality M}

/-- **No inextensible curve, every set is Cauchy.** If an open `W` carries no inextensible causal
curve, every subset of `W` is a Cauchy surface of `W` (vacuously): the long ray, whose curves all
extend, satisfies the conclusion of Lemma K for every `Σ`. -/
theorem isCauchySurfaceOn_of_forall_not_inextensible {W : Opens M}
    (h : ∀ (I : Set ℝ) (c : ℝ → M), ¬ C.Inextensible W I c) (S : Set M) :
    C.IsCauchySurfaceOn W S := fun I c hc => absurd hc (h I c)

/-- **An inextensible curve has no upper bound**: in a Hausdorff tarentin globally hyperbolic
causally arc-connected spacetime with `J^+(p) ≠ {p}`, an inextensible curve over `ℝ` is not
contained in `J^-(q)`, for any `q`. -/
theorem exists_not_le_of_inextensible [T2Space M] (hT : C.Tarentin) (hG : C.GloballyHyperbolic)
    (hC : C.CausallyArcConnected) (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p})
    {c : ℝ → M} (hc : C.Inextensible ⊤ univ c) (q : M) : ∃ s, ¬ C.le ⊤ (c s) q := by
  obtain ⟨s, hs⟩ := exists_not_mem_Jminus_of_isCompact hT hG hC hJp hc (isCompact_singleton (x := q))
  exact ⟨s, fun h => hs ⟨q, mem_singleton q, h⟩⟩

/-- **An inextensible curve of `M` through a chart of `Σ` meets `Σ` in that chart**: if `U` is open
and `Σ ∩ U` is a Cauchy surface of `U`, an inextensible causal curve of `M` passing through `U`
meets `Σ ∩ U` (its component in `U` is inextensible in `U`). No curve extension is used. -/
theorem exists_mem_of_inextensible_of_mem_chart [T2Space M] (hcaus : C.IsCausal) {S : Set M}
    {U : Opens M} (hSU : C.IsCauchySurfaceOn U (S ∩ U)) {I : Set ℝ} {c : ℝ → M}
    (hc : C.Inextensible ⊤ I c) {t₀ : ℝ} (ht₀ : t₀ ∈ I) (hU : c t₀ ∈ U) :
    ∃ t ∈ I, c t ∈ S ∩ U := by
  obtain ⟨_, ⟨⟨t, htJ, rfl⟩, hS⟩, -⟩ :=
    hSU _ c (inextensible_ordConnectedComponent hcaus hc ht₀ hU)
  exact ⟨t, (ordConnectedComponent_subset htJ).1, hS⟩

/-- **A Cauchy criterion with no curve extension.** In a connected Hausdorff tarentin globally
hyperbolic causally arc-connected spacetime with `J^±(p) ≠ {p}`, a compact non-empty acausal set
`Σ` whose causal future and past together form an open set is a Cauchy surface. -/
theorem isCauchySurface_of_isAcausal_of_isOpen [T2Space M] [ConnectedSpace M]
    (hT : C.Tarentin) (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected)
    (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p})
    {S : Set M} (hSc : IsCompact S) (hSne : S.Nonempty) (hac : C.IsAcausal S)
    (hopen : IsOpen (C.Jplus ⊤ S ∪ C.Jminus ⊤ S)) : C.IsCauchySurface S := by
  have hcaus := hG.1
  have hle := hG.isClosed_le hT
  have hEc : IsClosed (C.Jminus ⊤ S) := isClosed_Jminus_of_isCompact hle hSc
  have hFc : IsClosed (C.Jplus ⊤ S) := isClosed_Jplus_of_isCompact hle hSc
  have hEF : ∀ q, q ∈ C.Jplus ⊤ S → q ∈ C.Jminus ⊤ S → q ∈ S := by
    rintro q ⟨z, hz, hzq⟩ ⟨w, hw, hqw⟩
    have h := hac z hz w hw (C.le_trans hzq hqw)
    subst h
    rw [hcaus hqw hzq]; exact hz
  have hD : ∀ q, q ∈ C.Jplus ⊤ S ∪ C.Jminus ⊤ S := by
    have hne : (C.Jplus ⊤ S ∪ C.Jminus ⊤ S).Nonempty := by
      obtain ⟨s, hs⟩ := hSne
      exact ⟨s, Or.inl ⟨s, hs, C.le_refl trivial⟩⟩
    have huniv := IsClopen.eq_univ ⟨hFc.union hEc, hopen⟩ hne
    intro q
    rw [huniv]; trivial
  intro I c hc
  obtain ⟨φ, -, -, hφr, hcφ⟩ := hc.reparam hC hcaus hJm hJp
  obtain ⟨s₁, hs₁⟩ := exists_not_mem_Jminus_of_isCompact hT hG hC hJp hcφ hSc
  obtain ⟨s₀, hs₀⟩ := exists_not_mem_Jplus_of_isCompact hT hG hC hJm hcφ hSc
  have hF1 : (c ∘ φ) s₁ ∈ C.Jplus ⊤ S := (hD _).resolve_right hs₁
  have hE0 : (c ∘ φ) s₀ ∈ C.Jminus ⊤ S := (hD _).resolve_left hs₀
  have h01 : s₀ ≤ s₁ := by
    by_contra hlt
    push Not at hlt
    obtain ⟨z, hz, hzc⟩ := hF1
    exact hs₀ ⟨z, hz, C.le_trans hzc (hcφ.1.le_of_le trivial trivial hlt.le)⟩
  have hcont : Continuous (c ∘ φ) := hcφ.1.continuous
  obtain ⟨s, -, hsE, hsF⟩ := isPreconnected_closed_iff.1 isPreconnected_Icc _ _
    (hEc.preimage hcont) (hFc.preimage hcont) (fun t _ => (hD ((c ∘ φ) t)).symm)
    ⟨s₀, ⟨le_rfl, h01⟩, hE0⟩ ⟨s₁, ⟨h01, le_rfl⟩, hF1⟩
  have hcS : c (φ s) ∈ S := hEF _ hsF hsE
  have hφs : φ s ∈ I := hφr ▸ mem_range_self s
  refine ⟨c (φ s), ⟨⟨φ s, hφs, rfl⟩, hcS⟩, ?_⟩
  rintro _ ⟨⟨t, ht, rfl⟩, htS⟩
  rcases le_total t (φ s) with hle | hle
  · exact hac _ htS _ hcS (hc.1.le_of_le ht hφs hle)
  · exact (hac _ hcS _ htS (hc.1.le_of_le hφs ht hle)).symm

/-- **The exact residue of the bare form, where curves extend.** Under `CurvesExtend`, a compact
non-empty set is a Cauchy surface if and only if it is acausal and its causal future and past
cover `M`. -/
theorem isCauchySurface_iff_of_curvesExtend [T2Space M] [ConnectedSpace M]
    (hT : C.Tarentin) (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected)
    (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p})
    (hext : C.CurvesExtend) {S : Set M} (hSc : IsCompact S) (hSne : S.Nonempty) :
    C.IsCauchySurface S ↔ C.IsAcausal S ∧ ∀ q, q ∈ C.Jplus ⊤ S ∪ C.Jminus ⊤ S := by
  constructor
  · intro hS
    refine ⟨hS.isAcausal hC hext, fun q => ?_⟩
    obtain ⟨I, c, hc, hsub⟩ := hext (fun _ => q) 0 0 le_rfl
      (causalCurveOn_const (show q ∈ (⊤ : Opens M) from trivial))
    obtain ⟨t₀, ht₀, hct₀⟩ : q ∈ c '' I := hsub ⟨0, ⟨le_rfl, le_rfl⟩, rfl⟩
    obtain ⟨_, ⟨⟨t, ht, rfl⟩, htS⟩, -⟩ := hS I c hc
    rcases le_total t₀ t with h | h
    · refine Or.inr ⟨c t, htS, ?_⟩
      rw [← hct₀]; exact hc.1.le_of_le ht₀ ht h
    · refine Or.inl ⟨c t, htS, ?_⟩
      rw [← hct₀]; exact hc.1.le_of_le ht ht₀ h
  · rintro ⟨hac, hcov⟩
    refine isCauchySurface_of_isAcausal_of_isOpen hT hG hC hJm hJp hSc hSne hac ?_
    rw [eq_univ_of_forall hcov]
    exact isOpen_univ

end Causality

/-! ### Non-vacuity: the timelike line -/

/-- On the timelike line, `Σ = {0}` is acausal and its causal future and past cover `ℝ`: the
hypotheses of `isCauchySurface_of_isAcausal_of_isOpen` hold jointly. -/
theorem timelikeLine_reduction_hypotheses :
    timelikeLine.IsAcausal ({0} : Set ℝ) ∧
      IsOpen (timelikeLine.Jplus ⊤ ({0} : Set ℝ) ∪ timelikeLine.Jminus ⊤ ({0} : Set ℝ)) := by
  obtain ⟨hT, hG, hC, hJm, hJp, hext, -, hSc, -, -⟩ := timelikeLine_lemmaK_hypotheses
  obtain ⟨hac, hcov⟩ := (Causality.isCauchySurface_iff_of_curvesExtend hT hG hC hJm hJp hext hSc
    (singleton_nonempty 0)).1 timelikeLine_isCauchySurface_zero_of_lemmaKBare
  refine ⟨hac, ?_⟩
  rw [eq_univ_of_forall hcov]
  exact isOpen_univ

/-- The Cauchy criterion applied on the timelike line. -/
theorem timelikeLine_isCauchySurface_zero_of_reduction :
    timelikeLine.IsCauchySurface ({0} : Set ℝ) := by
  obtain ⟨hT, hG, hC, hJm, hJp, -, -, hSc, -, -⟩ := timelikeLine_lemmaK_hypotheses
  obtain ⟨hac, hopen⟩ := timelikeLine_reduction_hypotheses
  exact Causality.isCauchySurface_of_isAcausal_of_isOpen hT hG hC hJm hJp hSc
    (singleton_nonempty 0) hac hopen

end Causal
