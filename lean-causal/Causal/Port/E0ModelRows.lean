import Causal.Port.E0SingularFlat
import Causal.CausallyPlainLocZ
import Causal.SingularFlatPlain
import Causal.Remarks.BTZPoints
import Causal.LinesReachable

/-!
# The BTZ sentences of two remarks at the model `E₀`: `≪` is not reflexive, and `K⁻ ≠ I⁻`

Target `T-ett-e0-model-rows` (scaffold, no `sorry`). Cited, **unmarked** (SCOPE (a)):
`rem:relation_not_assumed_reflexive` — `ETT.tex:235`, `rem:K_neq_I` — `ETT.tex:871`.

> The relation $\tlleq$ is \emph{not} assumed reflexive: no point of Minkowski space lies in its
> own chronological future, and a BTZ point has empty chronological past (Definition
> \ref{defi:causal_E0}). (`ETT.tex:235`)

> Causal plainness cannot be dropped from Proposition \ref{prop:tarentin_fort_K}. [...] The same
> separation occurs, in degenerate form, at a BTZ point, where $I^-(p)=\emptyset$ while
> $K^-(p)=J^-(p)\setminus\{p\}\neq \emptyset$ (Proposition \ref{prop:K_calcul}).
> (`ETT.tex:872–877`)

## What is proved (no `sorry` in this file)

* `rem:relation_not_assumed_reflexive` **at `E₀`** (`E0.relation_not_assumed_reflexive`): no point
  of `minkowski d` is `≪_U` itself (every `d`, every open `U`; `Flat.minkowski_not_lt_self`
  reused); the BTZ line `axis` is not empty and at each of its points `I⁻_U(p) = ∅` in every open
  `U` (`Iminus_axis`, strict), so `¬ p ≪_U p`; and `E₀` is chronological, `¬ x ≪_U x` for every
  `x` (`E0.not_lt_self`: `τ` increases strictly along `≪`).
* **The BTZ sentence of `rem:K_neq_I` at `E₀`** (`E0.K_neq_I_btz`): at every point `p` of the
  axis, `I⁻(p) = ∅`, `K⁻(p) = J⁻(p) ∖ {p}` (`E0.Kminus_axis`, `prop:K_calcul` (c) at the model,
  `E₀` causal), `J⁻(p) ∖ {p} ≠ ∅`, `K⁻(p) ≠ I⁻(p)`; explicitly
  `K⁻(p) = {r = 0, τ < τ(p)}` (`E0.Kminus_axis_eq`). Assembled with the first sentence (the
  half-chronological line, `causallyPlain_cannot_be_dropped`, reused): `E0.K_neq_I`.
* **Abstractly**, at a point of `S₀` under `BTZAxioms` (kb/0012): `BTZAxioms.K_neq_I` (`M`
  causal), and `BTZAxioms.Kminus_ne_Iminus`, the separation `K⁻(p) ≠ I⁻(p)` **with no causality**;
  written here by T-ett-e0-model-rows, now in `Causal.SingularFlatPlain` (T-abs-hoist-plain-locz).
* **New: `E₀` is causally plain** (`E0.causallyPlain`, `defi:causalement_plat`), from a model-free
  criterion: push-up, `Z⁺` in every open set and `Z⁻` in every open set off a set with empty
  interior give plainness (`Causality.causallyPlain_of_locZ`); a strongly causal
  `SingularFlatAxioms` spacetime is causally plain (`SingularFlatAxioms.causallyPlain`); both
  written here by T-ett-e0-model-rows, now in `Causal.CausallyPlainLocZ` (ETT layer) and
  `Causal.SingularFlatPlain` (T-abs-hoist-plain-locz). So `E₀`
  carries every hypothesis of `prop:tarentin_fort_K` but `p ∈ Z⁻` at its BTZ points, where the
  conclusion fails (`E0.Zminus_cannot_be_dropped`), and `prop:K_calcul` (a), (b) hold at `E₀` by
  the paper's own route through `prop:tarentin_fort_K` (`E0.K_calcul_paper`).

## Hypothesis checklist

| paper | here |
|---|---|
| Minkowski space (l.235) | ✓ `minkowski d`, every `d`, every open `U` |
| a BTZ point (l.235, l.876; `defi:causal_E0`) | ⚠ read: a point of `axis`, the singular line of the ported `E₀` (OQ-34, OQ-35, SCOPE (a)); abstractly a point of `S₀` under `BTZAxioms` (⚠ strengthened, kb/0012) |
| `prop:K_calcul` (c): `M` causal (l.1561) | ✓ carried: `E₀` is causal (`isCausal`); abstractly `IsCausal` is asked for the equality only, the separation needs none (⚠ weakened) |

## SCOPE (disclosed)

* **(a) Why neither label is marked.** Each BTZ clause is proved at the model of record,
  `Causal.E0`, under the readings of OQ-34 (the flat extreme-BTZ metric `−2dτdr + dr² + r²dθ²`
  through the developing map `D`, DEC-33's causal curves) and OQ-35, both open: under the printed
  metric (l.1330) the singular line is timelike and `I⁻(p) = ∅` fails. `rem:K_neq_I`'s bubble
  sentence (l.873–875) is not proved here; it is open under the hypotheses of
  `prop:tarentin_fort_K` (`bubble_need_not_meet_Kplus` refutes it without them).
* **(b) "A BTZ point".** `defi:causal_E0` introduces it at `sing(E₀)` (l.1346–1347); elsewhere the
  paper uses it in any `E_{≥0}`-manifold. The anchors are the model's; the other reading is the
  `BTZAxioms` form, which asks `M` causal for `K⁻(p) = J⁻(p) ∖ {p}` (`prop:K_calcul` (c) assumes
  it, and so does l.769; the remark does not say so) and nothing for `K⁻(p) ≠ I⁻(p)`.
* **(c) Plainness.** The BTZ separation is the failure of `p ∈ Z⁻`, not of plainness: `E₀` is
  causally plain, absolutely minimal, tarentin, causal, `T2`, second countable. This bears on OQ-16
  and on `rem:pas_plat` (l.290), which this file does not anchor.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Model of record:
`Causal.Port.E0*` (strict, ported from gx `c48aa45`, T-ett-port-e0, T-ett-port-e0-sfa).
-/

namespace Causal

open Set TopologicalSpace Topology Filter

/-! The abstract lemmas once here are elsewhere, same names (T-abs-hoist-plain-locz):
`BTZAxioms.Jminus_diff_nonempty`, `BTZAxioms.Kminus_ne_Iminus`, `BTZAxioms.K_neq_I` and
`SingularFlatAxioms.causallyPlain` in `Causal.SingularFlatPlain`; the model-free criterion
`causallyPlain_of_locZ`, with `Jplus_subset_closure_Iplus_of_locZplus` and
`Jminus_diff_subset_closure_Iminus_of_locZminus`, in `Causal.CausallyPlainLocZ`. -/

/-! ### At the model `E₀` -/

namespace E0

variable {p : E0}

/-- **`E₀` is chronological**: no point is `≪_U` itself, in any open `U`. -/
theorem not_lt_self (U : Opens E0) (x : E0) : ¬ causality.lt U x x := fun h =>
  lt_irrefl _ (calculus_lt h).2.2.1

/-- The BTZ line of `E₀` is not empty. -/
theorem axis_nonempty : axis.Nonempty := ⟨((0 : ℝ), (0 : ℂ)), rfl⟩

/-- `prop:K_calcul` (c) **at `E₀`**: `K⁻(p) = J⁻(p) ∖ {p}` at a BTZ point. -/
theorem Kminus_axis (hp : p ∈ axis) :
    causality.Kminus ⊤ {p} = causality.Jminus ⊤ {p} \ {p} :=
  Causality.Kminus_eq_Jminus_diff isCausal (btzAxioms.singularPastAt p hp)

/-- `K⁻(p) = {r = 0, τ < τ(p)}` at a BTZ point of `E₀`. -/
theorem Kminus_axis_eq (hp : p ∈ axis) :
    causality.Kminus ⊤ {p} = {x | x ∈ axis ∧ x.1 < p.1} := by
  rw [Kminus_axis hp, Jminus_axis hp]
  ext x
  simp only [Set.mem_sdiff, mem_setOf_eq, mem_singleton_iff]
  constructor
  · rintro ⟨⟨hx, hle⟩, hne⟩
    exact ⟨hx, lt_of_le_of_ne hle fun h => hne (axis_eq_of_fst_eq hx hp h)⟩
  · rintro ⟨hx, hlt⟩
    exact ⟨⟨hx, hlt.le⟩, fun h => (lt_irrefl p.1) (h ▸ hlt)⟩

/-- `K⁻(p) ≠ ∅` at a BTZ point of `E₀`. -/
theorem Kminus_axis_nonempty (hp : p ∈ axis) : (causality.Kminus ⊤ {p}).Nonempty := by
  refine ⟨(p.1 - 1, 0), ?_⟩
  rw [Kminus_axis_eq hp]
  exact ⟨rfl, by simp⟩

/-- `K⁻(p) ≠ I⁻(p)` at a BTZ point of `E₀`. -/
theorem Kminus_ne_Iminus_axis (hp : p ∈ axis) :
    causality.Kminus ⊤ {p} ≠ causality.Iminus ⊤ {p} :=
  btzAxioms.Kminus_ne_Iminus hp

/-- **`E₀` is causally plain** (`defi:causalement_plat`). -/
theorem causallyPlain : causality.CausallyPlain :=
  Causality.causallyPlain_of_locZ E0LM.e0_pushUp E0LM.e0_locZplus E0LM.e0_locZminus interior_axis

/-- `prop:tarentin_fort_K` at the regular points of `E₀`, through causal plainness. -/
theorem Kminus_eq_Iminus_of_not_mem_axis (hp : p ∉ axis) :
    causality.Kminus ⊤ {p} = causality.Iminus ⊤ {p} :=
  Causality.Kminus_eq_Iminus_of_mem_Zminus causallyPlain ((mem_Zminus_iff p).2 hp)

/-- `prop:tarentin_fort_K`'s future form (`rem:comparable_property_obviously_holds`) at every point
of `E₀`, through causal plainness: `K⁺(p) = I⁺(p)`. -/
theorem Kplus_eq_Iplus (p : E0) : causality.Kplus ⊤ {p} = causality.Iplus ⊤ {p} :=
  Causality.Kplus_eq_Iplus_of_mem_Zplus causallyPlain (mem_Zplus p)

/-- `prop:K_calcul` **at `E₀` by the paper's route** (`ETT.tex:1565`): (a) and (b) from
`prop:tarentin_fort_K`, whose hypothesis "causally plain" `E₀` satisfies (`causallyPlain`), and
(c) from `E₀` causal. The library's `SingularFlatAxioms.K_calcul` goes through push-up instead
(OQ-16). -/
theorem K_calcul_paper :
    (∀ p ∉ axis, causality.Kplus ⊤ {p} = causality.Iplus ⊤ {p} ∧
      causality.Kminus ⊤ {p} = causality.Iminus ⊤ {p}) ∧
    (∀ p ∈ axis, causality.Kplus ⊤ {p} = causality.Iplus ⊤ {p}) ∧
    (∀ p ∈ axis, causality.Kminus ⊤ {p} = causality.Jminus ⊤ {p} \ {p}) :=
  ⟨fun p hp => ⟨Kplus_eq_Iplus p, Kminus_eq_Iminus_of_not_mem_axis hp⟩,
    fun p _ => Kplus_eq_Iplus p, fun _ hp => Kminus_axis hp⟩

/-- **"Strongly tarentin in the past" cannot be dropped from `prop:tarentin_fort_K`**, witnessed
at `E₀`: it is causally plain, absolutely minimal, tarentin, causal, Hausdorff and second
countable, and at every BTZ point `p ∉ Z⁻` and `K⁻(p) ≠ I⁻(p)`. The separation of `rem:K_neq_I` at a
BTZ point is this one, not a failure of causal plainness (SCOPE (c)). -/
theorem Zminus_cannot_be_dropped :
    causality.CausallyPlain ∧ causality.AbsolutelyMinimal ∧ causality.Tarentin ∧
      causality.IsCausal ∧ T2Space E0 ∧ SecondCountableTopology E0 ∧
      ∀ p ∈ axis, p ∉ causality.Zminus ∧ causality.Kminus ⊤ {p} ≠ causality.Iminus ⊤ {p} :=
  ⟨causallyPlain, causallyArcConnected.absolutelyMinimal, tarentin, isCausal, inferInstance,
    inferInstance, fun _ hp => ⟨(mem_Zplus_not_mem_Zminus hp).2, Kminus_ne_Iminus_axis hp⟩⟩

/-- `rem:relation_not_assumed_reflexive` **at `E₀`, assembled** (`ETT.tex:235`): no point of
Minkowski space is in its own chronological future (every dimension, every open set); the BTZ line
of `E₀` is not empty and its points have empty chronological past in every open set, hence are not
`≪` themselves; and no point of `E₀` is. -/
theorem relation_not_assumed_reflexive :
    (∀ (d : ℕ) (U : Opens (Minkowski d)) (q : Minkowski d), ¬ (minkowski d).lt U q q) ∧
    axis.Nonempty ∧
    (∀ p ∈ axis, ∀ U : Opens E0, causality.Iminus U {p} = ∅ ∧ ¬ causality.lt U p p) ∧
    (∀ (U : Opens E0) (x : E0), ¬ causality.lt U x x) :=
  ⟨fun _ _ q h => Flat.minkowski_not_lt_self q ((minkowski _).lt_mono le_top h), axis_nonempty,
    fun _ hp U => ⟨Iminus_axis hp U, not_lt_self U _⟩, not_lt_self⟩

/-- **The BTZ sentence of `rem:K_neq_I` at `E₀`** (`ETT.tex:875–877`): the BTZ line is not empty,
and at each of its points `I⁻(p) = ∅` while `K⁻(p) = J⁻(p) ∖ {p} ≠ ∅` (`prop:K_calcul` (c), `E₀`
being causal), so `K⁻(p) ≠ I⁻(p)`. -/
theorem K_neq_I_btz :
    axis.Nonempty ∧
    ∀ p ∈ axis, causality.Iminus ⊤ {p} = ∅ ∧
      causality.Kminus ⊤ {p} = causality.Jminus ⊤ {p} \ {p} ∧
      causality.Jminus ⊤ {p} \ {p} ≠ ∅ ∧ causality.Kminus ⊤ {p} ≠ causality.Iminus ⊤ {p} :=
  ⟨axis_nonempty, fun _ hp => btzAxioms.K_neq_I isCausal hp⟩

/-- `rem:K_neq_I` **assembled**: the first sentence (the half-chronological line) and the BTZ
sentence at `E₀`; the bubble sentence is not here. -/
theorem K_neq_I :
    (halfChronoLine.Tarentin ∧ halfChronoLine.AbsolutelyMinimal ∧ halfChronoLine.IsCausal ∧
      (0 : ℝ) ∈ halfChronoLine.Zminus ∧ ¬ halfChronoLine.CausallyPlain ∧
      halfChronoLine.Kminus ⊤ {0} ≠ halfChronoLine.Iminus ⊤ {0}) ∧
    axis.Nonempty ∧
    (∀ p ∈ axis, causality.Iminus ⊤ {p} = ∅ ∧
      causality.Kminus ⊤ {p} = causality.Jminus ⊤ {p} \ {p} ∧
      causality.Jminus ⊤ {p} \ {p} ≠ ∅ ∧ causality.Kminus ⊤ {p} ≠ causality.Iminus ⊤ {p}) :=
  ⟨causallyPlain_cannot_be_dropped, K_neq_I_btz⟩

end E0

end Causal
