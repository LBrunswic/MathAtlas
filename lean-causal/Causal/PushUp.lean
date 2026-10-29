import Causal.Lines
import Causal.Reachable
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The order-topological cores of the singular part: `Int J^± ∩ Z^∓ = I^±`, the computation and
the monotonicity of `K^±`, the order recovered above a Cauchy surface

`lem:J_int` — `ETT.tex:1800`. `lem:cup_cap_sing` — `ETT.tex:1812`. `prop:K_calcul` —
`ETT.tex:1557`. `prop:K_monotone` — `ETT.tex:1608`. `cor:K_ordre_Sigma` — `ETT.tex:2082`.

None of the five is marked: each is a statement about `E^{1,2}_{≥0}`-manifolds or singular flat
spacetimes, which the library does not define (and must not: the BTZ model is not defined in the
paper). Each is proved here for an abstract topological spacetime, the facts the paper draws from
the model spaces being explicit hypotheses, listed below with the model fact each stands for.

> `lem:J_int`. Let $M$ be a strongly causal singular flat spacetime. For every $p\in M$,
> $\ring J^\pm(p)\cap Z^\mp(M)=I^\pm(p).$

> `lem:cup_cap_sing`. Let $M$ be a globally hyperbolic singular flat spacetime, let $p\in M$ and
> let $(p_n)$ be a sequence of $M$ converging to $p$. Then
> $I^{\pm}(p)=\mathrm{Int}\left(\bigcup_{N}\bigcap_{n\geq N} I^\pm(p_n)\right).$

> `prop:K_calcul`. Let $M$ be a $\mass{\geq 0}$-manifold and let $p\in M$. (a) $K^\pm(p)=I^\pm(p)$
> if $p\notin \sing_0(M)$; (b) $K^+(p)=I^+(p)$ if $p\in \sing_0(M)$; (c) if $M$ is causal and
> $p\in \sing_0(M)$, then $K^-(p)=J^-(p)\setminus \{p\}$.

> `prop:K_monotone`. Let $M$ be a causal $\mass{\geq0}$-manifold and let $q\leq p$ in $M$. Then
> $K^-(q)\subset K^-(p)$ and $K^+(p)\subset K^+(q).$

> `cor:K_ordre_Sigma`. Let $M$ be a globally hyperbolic singular flat spacetime, let $\Sigma$ be a
> Cauchy surface of $M$ and let $x,y\in J^+(\Sigma)\setminus \Sigma$. If
> $K^-(x)\cap J^+(\Sigma)\subset K^-(y)\cap J^+(\Sigma)$, then $x\leq y$. In particular
> $x\mapsto K^-(x)\cap J^+(\Sigma)$ is injective on $J^+(\Sigma)\setminus \Sigma$.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `lem:J_int`: singular flat spacetime | ⚠ strengthened: `PushUp` (`cor:pushup_sing`), `AbsolutelyMinimal` (`cor:massA_causalite`), `T1Space` (a manifold) |
| — strongly causal | ⚠ weakened: not used; the chart reduction of the proof is not needed |
| `lem:cup_cap_sing`: singular flat spacetime | ⚠ strengthened: as for `lem:J_int`, plus `Tarentin` (`rem:sing_tarentin`), `T2Space` |
| — globally hyperbolic | ✓ carried (`cup_cap_sing`); only `J^∓(x)` closed is used (`…_iUnion_iInter`) |
| `prop:K_calcul`: `E_{≥0}`-manifold | ⚠ strengthened: `PushUp` (`cor:pushup_sing`); `FirstCountableTopology` (a manifold); a set `S` for `sing_0(M)`; `Z^+(M) = M` and `p ∉ S → p ∈ Z^-(M)` (`rem:btz_pas_tarentin`); `SingularPastAt p` for `p ∈ S` (`defi:causal_E0`, `lem:past_BTZ`) |
| — (c) `M` causal | ✓ carried |
| `prop:K_monotone`: causal `E_{≥0}`-manifold | ✓ causal carried; ⚠ strengthened: the hypotheses of `prop:K_calcul`, plus `S` closed under `J^-` (`lem:past_BTZ`) and `x ∈ S, y ∉ S, x ≤ y → x ≪ y` (`defi:causal_E0`, `I^+(x) = J^+(x) ∖ sing_0`) |
| `cor:K_ordre_Sigma`: globally hyperbolic singular flat spacetime | ✓ globally hyperbolic carried; ⚠ strengthened: `Tarentin` (`rem:sing_tarentin`), `T2Space`, `J^-(x) ⊂ closure K^-(x)` (`prop:K_densite_sing`) |
| — `Σ` a Cauchy surface | ⚠ strengthened: replaced by its one consequence used, `J^+(Σ)` a neighbourhood of each point of `J^+(Σ) ∖ Σ` (`lem:Sigma_separe`) |
| — `y ∈ J^+(Σ) ∖ Σ` | ⚠ weakened: not used for the implication (`le_of_Kminus_inter_subset`) |

## SCOPE (disclosed)

* **`SingularPastAt p`** is the model hypothesis for a BTZ point: (i) some sequence `p_n → p`
  has `p_n ≤ p`, `p_n ≠ p`; (ii) every `x ∈ J^-(p) ∖ {p}` admits a sequence `p_n → p`,
  non-decreasing for `≤`, with `p ∈ Int J^+(p_n)` for every `n` and
  `x ∈ Int_{J^-(p)} J^-(p_0)`. On the BTZ line `J^-(p)` is the half-line below `p`
  (`defi:causal_E0`); (ii) is what `lem:K_facile` needs and what the proof of
  `prop:K_calcul` (c) uses of the line.
* **`prop:K_calcul` (a), (b) are proved with push-up instead of causal plainness.** The paper
  derives them from `prop:tarentin_fort_K`, whose hypothesis "causally plain" is not established
  for `E_{≥0}`-manifolds anywhere in the paper; under push-up `lem:passe_coherent` is immediate
  (`PushUp.Jminus_Iminus_eq`, no `Z^-` needed) and the proof of `prop:tarentin_fort_K` goes
  through (`PushUp.Kminus_eq_Iminus`).
* **Satisfiability.** The timelike line with `S = ]-∞, 0]` satisfies every hypothesis of
  `K_calcul` and `K_monotone` (`timelikeLine_K_monotone_hypotheses`); the lightlike line, a model
  of a BTZ line with empty chronological pasts, satisfies `SingularPastAt` at every point in the
  past and in the future, and `K^-(p) = ]-∞, p[`, `K^+(p) = ]p, +∞[` there (`lightlikeLine_K`);
  the timelike line with `Σ = {0}` satisfies the hypotheses of `K_ordre_Sigma`
  (`timelikeLine_K_ordre_Sigma_hypotheses`). The hypotheses of `lem:J_int`/`lem:cup_cap_sing`
  are those of the timelike line (`Causal/Lines.lean`). A model with `S` non-empty and empty
  chronological pasts on `S` *and* `Z^+(M) = M` needs dimension at least 2 and is not built.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter

universe u

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable {C : Causality M} {U : Opens M} {p q x y z : M}

/-! ### Push-up, relational form -/

theorem dual_pushUp : C.dual.PushUp ↔ C.PushUp := by
  rw [pushUp_iff, pushUp_iff]
  constructor
  · intro h U x y z
    exact ⟨fun hxy hyz => (h U (x := z) (y := y) (z := x)).2 hyz hxy,
      fun hxy hyz => (h U (x := z) (y := y) (z := x)).1 hyz hxy⟩
  · intro h U x y z
    exact ⟨fun hxy hyz => (h U (x := z) (y := y) (z := x)).2 hyz hxy,
      fun hxy hyz => (h U (x := z) (y := y) (z := x)).1 hyz hxy⟩

theorem PushUp.lt_of_lt_of_le (h : C.PushUp) (hxy : C.lt U x y) (hyz : C.le U y z) :
    C.lt U x z := by
  exact ((pushUp_iff.1 h) U).1 hxy hyz

theorem PushUp.lt_of_le_of_lt (h : C.PushUp) (hxy : C.le U x y) (hyz : C.lt U y z) :
    C.lt U x z := by
  exact ((pushUp_iff.1 h) U).2 hxy hyz

/-! ### `lem:passe_coherent` and `prop:tarentin_fort_K` under push-up -/

/-- `lem:passe_coherent` under push-up, at every point and in every open set:
`J^-_U(I^-_U(p)) = I^-_U(p)`. -/
theorem PushUp.Jminus_Iminus_eq (h : C.PushUp) : C.Jminus U (C.Iminus U {p}) = C.Iminus U {p} := by
  refine Subset.antisymm ?_ (Precausality.subset_Jminus Precausality.Iminus_subset_carrier)
  rintro q ⟨p', hp', hqp'⟩
  have hp'p : C.lt U p' p := by simpa using hp'
  simpa using h.lt_of_le_of_lt hqp' hp'p

/-- `prop:tarentin_fort_K` with push-up in place of causal plainness: at a point strongly
tarentin in the past, `K^-(p) = I^-(p)`. -/
theorem PushUp.Kminus_eq_Iminus [FirstCountableTopology M] (h : C.PushUp) (hp : p ∈ C.Zminus) :
    C.Kminus ⊤ {p} = C.Iminus ⊤ {p} := by
  -- every increasing sequence converging to `p` computes `K^-(p)`
  have hK : ∀ u : ℕ → M, (∀ n, C.lt ⊤ (u n) p) → Tendsto u atTop (𝓝 p) →
      C.Kminus ⊤ {p} =
        ⋃ N : ℕ, interiorWithin (C.Jminus ⊤ {p}) (⋂ n ≥ N, C.Jminus ⊤ {u n}) := by
    intro u hup hu
    refine Kminus_eq_of_tendsto hu fun n => ?_
    exact Iplus_subset_interior_Jplus (by simpa using hup n)
  refine Subset.antisymm ?_ ?_
  · intro x hx
    obtain ⟨q, hq⟩ := Iminus_nonempty_of_mem_Zminus hp
    have hqp : C.lt ⊤ q p := by simpa using hq
    obtain ⟨u, -, -, hup, hu⟩ := exists_seq_lt_tendsto_of_mem_Zminus hp hqp
    rw [hK u hup hu] at hx
    obtain ⟨N, hN⟩ := mem_iUnion.1 hx
    have hxN : x ∈ ⋂ n ≥ N, C.Jminus ⊤ {u n} := interiorWithin_subset hN
    simp only [mem_iInter] at hxN
    have hxu : C.le ⊤ x (u N) := by simpa using hxN N le_rfl
    rw [← h.Jminus_Iminus_eq]
    exact ⟨u N, by simpa using hup N, hxu⟩
  · intro q hq
    have hqp : C.lt ⊤ q p := by simpa using hq
    obtain ⟨u, hu0, hmono, hup, hu⟩ := exists_seq_lt_tendsto_of_mem_Zminus hp hqp
    rw [hK u hup hu]
    refine mem_iUnion.2 ⟨1, mem_interiorWithin_of_mem_nhds ?_ ?_⟩
    · simpa using C.le_of_lt hqp
    · have hq1 : C.lt ⊤ q (u 1) := by
        have := hmono 0
        rwa [hu0] at this
      have hmem : q ∈ C.Iminus ⊤ {u 1} := by simpa using hq1
      refine mem_of_superset (isOpen_Iminus.mem_nhds hmem) ?_
      intro z hz
      have hz1 : C.lt ⊤ z (u 1) := by simpa using hz
      simp only [mem_iInter]
      intro n hn
      simpa using C.le_trans (C.le_of_lt hz1) (le_of_forall_lt_succ hmono hn)

/-- `prop:tarentin_fort_K`, future, under push-up. -/
theorem PushUp.Kplus_eq_Iplus [FirstCountableTopology M] (h : C.PushUp) (hp : p ∈ C.Zplus) :
    C.Kplus ⊤ {p} = C.Iplus ⊤ {p} := by
  exact PushUp.Kminus_eq_Iminus (C := C.dual) (dual_pushUp.2 h) hp

/-! ### `lem:J_int` -/

/-- `lem:J_int`, `+`: the proof of `lem:IJ_calc`, which is abstract. -/
theorem interior_Jplus_inter_Zminus [T1Space M] (hA : C.AbsolutelyMinimal) (hP : C.PushUp)
    (p : M) : interior (C.Jplus ⊤ {p}) ∩ C.Zminus = C.Iplus ⊤ {p} := by
  ext q
  constructor
  · rintro ⟨hqint, hqZ⟩
    obtain ⟨r, hr, hrJ⟩ := hqZ _ (isOpen_interior.mem_nhds hqint)
    have hrq : C.lt ⊤ r q := by simpa using hr
    have hpr : C.le ⊤ p r := by simpa using interior_subset hrJ
    simpa using hP.lt_of_le_of_lt hpr hrq
  · intro hq
    have hpq : C.lt ⊤ p q := by simpa using hq
    exact ⟨Iplus_subset_interior_Jplus hq,
      (AbsolutelyMinimal.mem_Zminus_iff hA).2 ⟨p, by simpa using hpq⟩⟩

/-- `lem:J_int`, `-`. -/
theorem interior_Jminus_inter_Zplus [T1Space M] (hA : C.AbsolutelyMinimal) (hP : C.PushUp)
    (p : M) : interior (C.Jminus ⊤ {p}) ∩ C.Zplus = C.Iminus ⊤ {p} := by
  exact interior_Jplus_inter_Zminus (C := C.dual) (dual_absolutelyMinimal.2 hA) (dual_pushUp.2 hP) p

/-- `lem:J_int`, both signs. -/
theorem J_int [T1Space M] (hA : C.AbsolutelyMinimal) (hP : C.PushUp) (p : M) :
    interior (C.Jplus ⊤ {p}) ∩ C.Zminus = C.Iplus ⊤ {p} ∧
      interior (C.Jminus ⊤ {p}) ∩ C.Zplus = C.Iminus ⊤ {p} :=
  ⟨interior_Jplus_inter_Zminus hA hP p, interior_Jminus_inter_Zplus hA hP p⟩

/-! ### `lem:cup_cap_sing` -/

/-- `lem:cup_cap_sing`, `-`: `lem:cup_cap` closed by `lem:J_int`. -/
theorem Iminus_eq_interior_iUnion_iInter [T1Space M] (hA : C.AbsolutelyMinimal) (hP : C.PushUp)
    {u : ℕ → M} (hu : Tendsto u atTop (𝓝 p)) (hJ : ∀ x, IsClosed (C.Jplus ⊤ {x})) :
    C.Iminus ⊤ {p} = interior (⋃ N : ℕ, ⋂ n ≥ N, C.Iminus ⊤ {u n}) := by
  obtain ⟨h1, h2⟩ := Iminus_subset_interior_and_subset hA hu hJ
  exact Subset.antisymm h1 (h2.trans (interior_Jminus_inter_Zplus hA hP p).subset)

/-- `lem:cup_cap_sing`, `+`. -/
theorem Iplus_eq_interior_iUnion_iInter [T1Space M] (hA : C.AbsolutelyMinimal) (hP : C.PushUp)
    {u : ℕ → M} (hu : Tendsto u atTop (𝓝 p)) (hJ : ∀ x, IsClosed (C.Jminus ⊤ {x})) :
    C.Iplus ⊤ {p} = interior (⋃ N : ℕ, ⋂ n ≥ N, C.Iplus ⊤ {u n}) := by
  obtain ⟨h1, h2⟩ := Iplus_subset_interior_and_subset hA hu hJ
  exact Subset.antisymm h1 (h2.trans (interior_Jplus_inter_Zminus hA hP p).subset)

/-- `lem:cup_cap_sing`, both signs, on a tarentin globally hyperbolic spacetime. -/
theorem cup_cap_sing [T2Space M] (hA : C.AbsolutelyMinimal) (hP : C.PushUp) (hT : C.Tarentin)
    (hG : C.GloballyHyperbolic) {u : ℕ → M} (hu : Tendsto u atTop (𝓝 p)) :
    C.Iminus ⊤ {p} = interior (⋃ N : ℕ, ⋂ n ≥ N, C.Iminus ⊤ {u n}) ∧
      C.Iplus ⊤ {p} = interior (⋃ N : ℕ, ⋂ n ≥ N, C.Iplus ⊤ {u n}) :=
  ⟨Iminus_eq_interior_iUnion_iInter hA hP hu (hG.isClosed_Jplus_singleton hT),
    Iplus_eq_interior_iUnion_iInter hA hP hu (hG.isClosed_Jminus_singleton hT)⟩

/-! ### `prop:K_calcul` -/

/-- The model hypothesis standing for the past of a BTZ point `p` (`defi:causal_E0`,
`lem:past_BTZ`): (i) a sequence `p_n → p` with `p_n < p`; (ii) every `x < p` lies in the relative
interior in `J^-(p)` of `J^-(p_0)` for some sequence `p_n → p`, non-decreasing, with
`p ∈ Int J^+(p_n)`. -/
def SingularPastAt (C : Causality M) (p : M) : Prop :=
  (∃ u : ℕ → M, Tendsto u atTop (𝓝 p) ∧ ∀ n, C.le ⊤ (u n) p ∧ u n ≠ p) ∧
  ∀ x, C.le ⊤ x p → x ≠ p → ∃ u : ℕ → M, Tendsto u atTop (𝓝 p) ∧
    (∀ m n, m ≤ n → C.le ⊤ (u m) (u n)) ∧ (∀ n, p ∈ interior (C.Jplus ⊤ {u n})) ∧
    x ∈ interiorWithin (C.Jminus ⊤ {p}) (C.Jminus ⊤ {u 0})

/-- `prop:K_calcul` (c): at a point whose past is a BTZ half-line, in a causal spacetime,
`K^-(p) = J^-(p) ∖ {p}`. -/
theorem Kminus_eq_Jminus_diff (hc : C.IsCausal) (h : C.SingularPastAt p) :
    C.Kminus ⊤ {p} = C.Jminus ⊤ {p} \ {p} := by
  ext x
  constructor
  · intro hx
    refine ⟨Kminus_subset_Jminus hx, fun hxp => ?_⟩
    rw [mem_singleton_iff] at hxp
    subst hxp
    obtain ⟨⟨u, hu, hup⟩, -⟩ := h
    obtain ⟨N, hN⟩ := mem_Kminus_singleton.1 hx u hu
    have hxN := (interiorWithin_subset hN).2
    simp only [mem_iInter] at hxN
    have hxu : C.le ⊤ x (u N) := by simpa using hxN N le_rfl
    exact (hup N).2 (hc (hup N).1 hxu)
  · rintro ⟨hxJ, hxne⟩
    obtain ⟨u, hu, hmono, hint, hx0⟩ := h.2 x (by simpa using hxJ) hxne
    rw [Kminus_eq_of_tendsto hu hint]
    refine mem_iUnion.2 ⟨0, interiorWithin_mono ?_ hx0⟩
    intro z hz
    simp only [mem_iInter]
    intro n _
    have hz0 : C.le ⊤ z (u 0) := by simpa using hz
    simpa using C.le_trans hz0 (hmono 0 n (Nat.zero_le n))

/-- `prop:K_calcul`, the three assertions, `S` standing for `sing_0(M)`. -/
theorem K_calcul [FirstCountableTopology M] (hP : C.PushUp) {S : Set M}
    (hZp : ∀ p, p ∈ C.Zplus) (hZm : ∀ p ∉ S, p ∈ C.Zminus) (hS : ∀ p ∈ S, C.SingularPastAt p) :
    (∀ p ∉ S, C.Kplus ⊤ {p} = C.Iplus ⊤ {p} ∧ C.Kminus ⊤ {p} = C.Iminus ⊤ {p}) ∧
    (∀ p ∈ S, C.Kplus ⊤ {p} = C.Iplus ⊤ {p}) ∧
    (C.IsCausal → ∀ p ∈ S, C.Kminus ⊤ {p} = C.Jminus ⊤ {p} \ {p}) := by
  exact ⟨fun p hp => ⟨hP.Kplus_eq_Iplus (hZp p), hP.Kminus_eq_Iminus (hZm p hp)⟩,
    fun p _ => hP.Kplus_eq_Iplus (hZp p),
    fun hc p hp => Kminus_eq_Jminus_diff hc (hS p hp)⟩

/-! ### `prop:K_monotone` -/

/-- `prop:K_monotone`: `q ≤ p` implies `K^-(q) ⊂ K^-(p)` and `K^+(p) ⊂ K^+(q)`. -/
theorem K_monotone [FirstCountableTopology M] (hc : C.IsCausal) (hP : C.PushUp) {S : Set M}
    (hZp : ∀ p, p ∈ C.Zplus) (hZm : ∀ p ∉ S, p ∈ C.Zminus) (hS : ∀ p ∈ S, C.SingularPastAt p)
    (hdown : ∀ p ∈ S, ∀ q, C.le ⊤ q p → q ∈ S)
    (hfut : ∀ x ∈ S, ∀ y ∉ S, C.le ⊤ x y → C.lt ⊤ x y) (hqp : C.le ⊤ q p) :
    C.Kminus ⊤ {q} ⊆ C.Kminus ⊤ {p} ∧ C.Kplus ⊤ {p} ⊆ C.Kplus ⊤ {q} := by
  constructor
  · by_cases hpS : p ∈ S
    · have hqS := hdown p hpS q hqp
      rw [Kminus_eq_Jminus_diff hc (hS q hqS), Kminus_eq_Jminus_diff hc (hS p hpS)]
      rintro x ⟨hxq, hxne⟩
      have hxq' : C.le ⊤ x q := by simpa using hxq
      refine ⟨by simpa using C.le_trans hxq' hqp, fun hxp => hxne ?_⟩
      rw [mem_singleton_iff] at hxp ⊢
      subst hxp
      exact hc hxq' hqp
    · rw [hP.Kminus_eq_Iminus (hZm p hpS)]
      by_cases hqS : q ∈ S
      · rw [Kminus_eq_Jminus_diff hc (hS q hqS)]
        rintro x ⟨hxq, -⟩
        have hxq' : C.le ⊤ x q := by simpa using hxq
        have hxS := hdown q hqS x hxq'
        simpa using hfut x hxS p hpS (C.le_trans hxq' hqp)
      · rw [hP.Kminus_eq_Iminus (hZm q hqS)]
        intro x hx
        have hxq : C.lt ⊤ x q := by simpa using hx
        simpa using hP.lt_of_lt_of_le hxq hqp
  · rw [hP.Kplus_eq_Iplus (hZp p), hP.Kplus_eq_Iplus (hZp q)]
    intro x hx
    have hpx : C.lt ⊤ p x := by simpa using hx
    simpa using hP.lt_of_le_of_lt hqp hpx

/-! ### `cor:K_ordre_Sigma` -/

/-- `cor:K_ordre_Sigma`, the implication, under its weakest hypotheses: `J^-(y)` closed, `K^-`
dense in `J^-`, `J^+(S)` a neighbourhood of `x`. -/
theorem le_of_Kminus_inter_subset (hJ : ∀ y, IsClosed (C.Jminus ⊤ {y}))
    (hK : ∀ x, C.Jminus ⊤ {x} ⊆ closure (C.Kminus ⊤ {x})) {S : Set M}
    (hS : ∀ x ∈ C.Jplus ⊤ S \ S, C.Jplus ⊤ S ∈ 𝓝 x) (hx : x ∈ C.Jplus ⊤ S \ S)
    (h : C.Kminus ⊤ {x} ∩ C.Jplus ⊤ S ⊆ C.Kminus ⊤ {y} ∩ C.Jplus ⊤ S) : C.le ⊤ x y := by
  have hxN : C.Jplus ⊤ S ∈ 𝓝 x := hS x hx
  have hxK : x ∈ closure (C.Kminus ⊤ {x}) :=
    hK x (by simpa using C.le_refl (U := ⊤) (x := x) trivial)
  have hcl : x ∈ closure (C.Kminus ⊤ {x} ∩ C.Jplus ⊤ S) := by
    rw [mem_closure_iff_nhds] at hxK ⊢
    intro N hN
    obtain ⟨z, ⟨hzN, hzS⟩, hzK⟩ := hxK (N ∩ C.Jplus ⊤ S) (inter_mem hN hxN)
    exact ⟨z, hzN, hzK, hzS⟩
  have hxy : x ∈ closure (C.Jminus ⊤ {y}) :=
    closure_mono ((h.trans inter_subset_left).trans Kminus_subset_Jminus) hcl
  rw [(hJ y).closure_eq] at hxy
  simpa using hxy

/-- `cor:K_ordre_Sigma` on a tarentin globally hyperbolic Hausdorff spacetime, `S` standing for
the Cauchy surface `Σ`. -/
theorem K_ordre_Sigma [T2Space M] (hT : C.Tarentin) (hG : C.GloballyHyperbolic)
    (hK : ∀ x, C.Jminus ⊤ {x} ⊆ closure (C.Kminus ⊤ {x})) {S : Set M}
    (hS : ∀ x ∈ C.Jplus ⊤ S \ S, C.Jplus ⊤ S ∈ 𝓝 x) :
    (∀ x ∈ C.Jplus ⊤ S \ S, ∀ y ∈ C.Jplus ⊤ S \ S,
      C.Kminus ⊤ {x} ∩ C.Jplus ⊤ S ⊆ C.Kminus ⊤ {y} ∩ C.Jplus ⊤ S → C.le ⊤ x y) ∧
    InjOn (fun x => C.Kminus ⊤ {x} ∩ C.Jplus ⊤ S) (C.Jplus ⊤ S \ S) := by
  have hJ := hG.isClosed_Jminus_singleton hT
  refine ⟨fun x hx y _ h => le_of_Kminus_inter_subset hJ hK hS hx h, fun x hx y hy hxy => ?_⟩
  have hxy' : C.Kminus ⊤ {x} ∩ C.Jplus ⊤ S = C.Kminus ⊤ {y} ∩ C.Jplus ⊤ S := hxy
  exact hG.1 (le_of_Kminus_inter_subset hJ hK hS hx hxy'.subset)
    (le_of_Kminus_inter_subset hJ hK hS hy hxy'.symm.subset)

end Causality

/-! ### The hypotheses are satisfiable: two lines -/

section Lines

theorem tendsto_sub_div_nat (p d : ℝ) :
    Tendsto (fun n : ℕ => p - d / ((n : ℝ) + 1)) atTop (𝓝 p) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul d
  have h2 := (tendsto_const_nhds : Tendsto (fun _ : ℕ => p) atTop (𝓝 p)).sub h
  rw [mul_zero, sub_zero] at h2
  refine h2.congr fun n => ?_
  ring

theorem tendsto_add_div_nat (p d : ℝ) :
    Tendsto (fun n : ℕ => p + d / ((n : ℝ) + 1)) atTop (𝓝 p) := by
  have h := tendsto_sub_div_nat p (-d)
  refine h.congr fun n => ?_
  ring

theorem div_succ_antitone {d : ℝ} (hd : 0 ≤ d) {m n : ℕ} (hmn : m ≤ n) :
    d / ((n : ℝ) + 1) ≤ d / ((m : ℝ) + 1) := by
  have : (m : ℝ) ≤ n := by exact_mod_cast hmn
  exact div_le_div_of_nonneg_left hd (by positivity) (by linarith)

namespace Causality

/-- A causality on `ℝ` whose causal relation on `ℝ` is the order of `ℝ` satisfies the model
hypothesis `SingularPastAt` at every point: the past of every point is a half-line along which
`K^-` is computed as at a BTZ point. -/
theorem singularPastAt_of_le_iff {C : Causality ℝ} (h : ∀ x y, C.le ⊤ x y ↔ x ≤ y) (p : ℝ) :
    C.SingularPastAt p := by
  refine ⟨⟨fun n => p - 1 / ((n : ℝ) + 1), tendsto_sub_div_nat p 1, fun n => ⟨?_, ?_⟩⟩, ?_⟩
  · rw [h]
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  · have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    intro he
    linarith
  · intro x hxp hxne
    have hxp' : x < p := lt_of_le_of_ne ((h x p).1 hxp) hxne
    set d : ℝ := (p - x) / 2 with hd
    have hd0 : 0 < d := by rw [hd]; linarith
    refine ⟨fun n => p - d / ((n : ℝ) + 1), tendsto_sub_div_nat p d, fun m n hmn => ?_,
      fun n => ?_, ?_⟩
    · rw [h]
      linarith [div_succ_antitone hd0.le hmn]
    · have hpos : 0 < d / ((n : ℝ) + 1) := by positivity
      refine mem_interior_iff_mem_nhds.2 (Filter.mem_of_superset (Ioi_mem_nhds (by linarith :
        p - d / ((n : ℝ) + 1) < p)) fun z hz => ?_)
      rw [Precausality.mem_Jplus_singleton, h]
      exact _root_.le_of_lt hz
    · refine mem_interiorWithin_of_mem_nhds (by simpa using hxp) ?_
      have hu0 : p - d / (((0 : ℕ) : ℝ) + 1) = p - d := by simp
      refine Filter.mem_of_superset (Iio_mem_nhds (by rw [hu0]; linarith :
        x < p - d / (((0 : ℕ) : ℝ) + 1))) fun z hz => ?_
      rw [Precausality.mem_Jminus_singleton, h]
      exact _root_.le_of_lt hz

/-- The mirror statement: a causality on `ℝ` whose causal relation on `ℝ` is the reverse order
satisfies `SingularPastAt` at every point. Applied to `C.dual`, it computes `K^+` of a causality
whose relation is the order of `ℝ`. -/
theorem singularPastAt_of_ge_iff {C : Causality ℝ} (h : ∀ x y, C.le ⊤ x y ↔ y ≤ x) (p : ℝ) :
    C.SingularPastAt p := by
  refine ⟨⟨fun n => p + 1 / ((n : ℝ) + 1), tendsto_add_div_nat p 1, fun n => ⟨?_, ?_⟩⟩, ?_⟩
  · rw [h]
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  · have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    intro he
    linarith
  · intro x hxp hxne
    have hxp' : p < x := lt_of_le_of_ne ((h x p).1 hxp) (Ne.symm hxne)
    set d : ℝ := (x - p) / 2 with hd
    have hd0 : 0 < d := by rw [hd]; linarith
    refine ⟨fun n => p + d / ((n : ℝ) + 1), tendsto_add_div_nat p d, fun m n hmn => ?_,
      fun n => ?_, ?_⟩
    · rw [h]
      linarith [div_succ_antitone hd0.le hmn]
    · have hpos : 0 < d / ((n : ℝ) + 1) := by positivity
      refine mem_interior_iff_mem_nhds.2 (Filter.mem_of_superset (Iio_mem_nhds (by linarith :
        p < p + d / ((n : ℝ) + 1))) fun z hz => ?_)
      rw [Precausality.mem_Jplus_singleton, h]
      exact _root_.le_of_lt hz
    · refine mem_interiorWithin_of_mem_nhds (by simpa using hxp) ?_
      have hu0 : p + d / (((0 : ℕ) : ℝ) + 1) = p + d := by simp
      refine Filter.mem_of_superset (Ioi_mem_nhds (by rw [hu0]; linarith :
        p + d / (((0 : ℕ) : ℝ) + 1) < x)) fun z hz => ?_
      rw [Precausality.mem_Jminus_singleton, h]
      exact _root_.le_of_lt hz

end Causality

open Causality

theorem timelikeLine_le_top {x y : ℝ} : timelikeLine.le ⊤ x y ↔ x ≤ y := by simp

theorem lightlikeLine_le_top {x y : ℝ} : lightlikeLine.le ⊤ x y ↔ x ≤ y := by simp

theorem timelikeLine_mem_Zplus (p : ℝ) : p ∈ timelikeLine.Zplus := by
  intro N hN
  obtain ⟨l, u, ⟨hl, hu⟩, hlu⟩ := mem_nhds_iff_exists_Ioo_subset.1 hN
  refine ⟨(p + u) / 2, ?_, hlu ⟨by linarith, by linarith⟩⟩
  simp only [Precausality.mem_Iplus_singleton, timelikeLine_lt]
  exact ⟨by linarith, by simp⟩

theorem timelikeLine_mem_Zminus (p : ℝ) : p ∈ timelikeLine.Zminus := by
  intro N hN
  obtain ⟨l, u, ⟨hl, hu⟩, hlu⟩ := mem_nhds_iff_exists_Ioo_subset.1 hN
  refine ⟨(l + p) / 2, ?_, hlu ⟨by linarith, by linarith⟩⟩
  simp only [Precausality.mem_Iminus_singleton, timelikeLine_lt]
  exact ⟨by linarith, by simp⟩

/-- The hypotheses of `K_calcul` and `K_monotone` are jointly satisfiable with a non-empty
singular set: the timelike line with `S = ]-∞, 0]`. -/
theorem timelikeLine_K_monotone_hypotheses :
    timelikeLine.IsCausal ∧ timelikeLine.PushUp ∧ (∀ p, p ∈ timelikeLine.Zplus) ∧
    (∀ p ∉ Iic (0 : ℝ), p ∈ timelikeLine.Zminus) ∧
    (∀ p ∈ Iic (0 : ℝ), timelikeLine.SingularPastAt p) ∧
    (∀ p ∈ Iic (0 : ℝ), ∀ q, timelikeLine.le ⊤ q p → q ∈ Iic (0 : ℝ)) ∧
    (∀ x ∈ Iic (0 : ℝ), ∀ y ∉ Iic (0 : ℝ), timelikeLine.le ⊤ x y → timelikeLine.lt ⊤ x y) := by
  refine ⟨timelikeLine_isCausal, timelikeLine_pushUp, timelikeLine_mem_Zplus,
    fun p _ => timelikeLine_mem_Zminus p,
    fun p _ => singularPastAt_of_le_iff (fun _ _ => timelikeLine_le_top) p, ?_, ?_⟩
  · intro p hp q hqp
    exact (timelikeLine_le_top.1 hqp).trans hp
  · intro x hx y hy hxy
    simp only [mem_Iic, not_le] at hx hy
    exact ⟨by linarith, by simp⟩

/-- The model hypothesis of a BTZ line holds on the lightlike line, in the past and, through
`dual`, in the future. -/
theorem lightlikeLine_singularPastAt (p : ℝ) :
    lightlikeLine.SingularPastAt p ∧ lightlikeLine.dual.SingularPastAt p :=
  ⟨singularPastAt_of_le_iff (fun _ _ => lightlikeLine_le_top) p,
    singularPastAt_of_ge_iff (fun _ _ => lightlikeLine_le_top) p⟩

theorem lightlikeLine_isCausal : lightlikeLine.IsCausal :=
  fun _ _ hxy hyx => le_antisymm hxy.1 hyx.1

/-- On the lightlike line, `K^-(p) = ]-∞, p[` and `K^+(p) = ]p, +∞[`. -/
theorem lightlikeLine_K (p : ℝ) :
    lightlikeLine.Kminus ⊤ {p} = Iio p ∧ lightlikeLine.Kplus ⊤ {p} = Ioi p := by
  constructor
  · rw [Kminus_eq_Jminus_diff lightlikeLine_isCausal (lightlikeLine_singularPastAt p).1]
    ext x
    simp only [Set.mem_sdiff, mem_singleton_iff, mem_Iio]
    constructor
    · rintro ⟨h1, h2⟩
      exact lt_of_le_of_ne (by simpa using h1) h2
    · intro h
      exact ⟨by simpa using h.le, h.ne⟩
  · have : lightlikeLine.Kplus ⊤ {p} = lightlikeLine.Jplus ⊤ {p} \ {p} :=
      Kminus_eq_Jminus_diff (C := lightlikeLine.dual)
        ((dual_isCausal).2 lightlikeLine_isCausal) (lightlikeLine_singularPastAt p).2
    rw [this]
    ext x
    simp only [Set.mem_sdiff, mem_singleton_iff, mem_Ioi]
    constructor
    · rintro ⟨h1, h2⟩
      exact lt_of_le_of_ne (by simpa using h1) (Ne.symm h2)
    · intro h
      exact ⟨by simpa using h.le, h.ne'⟩

/-- The hypotheses of `K_ordre_Sigma` are satisfiable: the timelike line, with `S = {0}`. -/
theorem timelikeLine_K_ordre_Sigma_hypotheses :
    (∀ x, timelikeLine.Jminus ⊤ {x} ⊆ closure (timelikeLine.Kminus ⊤ {x})) ∧
    (∀ x ∈ timelikeLine.Jplus ⊤ {0} \ {0}, timelikeLine.Jplus ⊤ {0} ∈ 𝓝 x) := by
  constructor
  · intro x
    rw [PushUp.Kminus_eq_Iminus timelikeLine_pushUp (timelikeLine_mem_Zminus x)]
    have h1 : timelikeLine.Iminus ⊤ {x} = Iio x := by
      ext z; simp
    have h2 : timelikeLine.Jminus ⊤ {x} = Iic x := by
      ext z; simp
    rw [h1, h2, closure_Iio]
  · rintro x ⟨hx, hx0⟩
    have h2 : timelikeLine.Jplus ⊤ {0} = Ici 0 := by
      ext z; simp
    rw [h2] at hx ⊢
    exact Ici_mem_nhds (lt_of_le_of_ne hx (Ne.symm hx0))

end Lines

end Causal
