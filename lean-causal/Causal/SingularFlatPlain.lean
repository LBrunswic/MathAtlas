import Causal.SingularFlat
import Causal.CausallyPlainLocZ

/-!
# A strongly causal `SingularFlatAxioms` spacetime is causally plain; `K⁻ ≠ I⁻` at a BTZ point under `BTZAxioms`

Programme target `T-abs-hoist-plain-locz` (`programme/roadmap.toml:720`; no label of `ETT.tex`
marked). **Not layer 1**: the statements are over the bundles `SingularFlatAxioms` and `BTZAxioms`
of `Causal.SingularFlat`, a module of the model layer (`tools/ladder.py` `MODEL_LAYER`; kb/0012),
so this module is model-layer by its import of `Causal.SingularFlat`. It imports no `Causal.Port.*`
and no model space: no `E₀`, no Minkowski space. Whether a module over `Causal.SingularFlat`'s
bundles alone may count as layer 1 is T-abs-hoist-cbg-geometry's question (a), not decided here.

> The same separation occurs, in degenerate form, at a BTZ point, where $I^-(p)=\emptyset$ while
> $K^-(p)=J^-(p)\setminus\{p\}\neq \emptyset$ (Proposition \ref{prop:K_calcul}).
> (`rem:K_neq_I`, `ETT.tex:875–877`)

## What is here (no `sorry`)

Moved out of `Causal.Port.E0ModelRows` (T-ett-e0-model-rows), same full names, same statements,
text verbatim (kb/0063), namespace `Causal.Causality`:

* `BTZAxioms.Jminus_diff_nonempty`: at a BTZ point `J⁻(p) ∖ {p} ≠ ∅` (field `singularPastAt`);
* `BTZAxioms.Kminus_ne_Iminus`: `K⁻(p) ≠ I⁻(p)` at a BTZ point, with no causality asked;
* `BTZAxioms.K_neq_I`: the BTZ sentence of `rem:K_neq_I` under `BTZAxioms`, `M` causal as
  `prop:K_calcul` (c) assumes: `I⁻(p) = ∅`, `K⁻(p) = J⁻(p) ∖ {p} ≠ ∅`, `K⁻(p) ≠ I⁻(p)`;
* `SingularFlatAxioms.causallyPlain`: **a strongly causal `SingularFlatAxioms` spacetime is
  causally plain**, by `Causality.causallyPlain_of_locZ` (`Causal.CausallyPlainLocZ`) with
  `S = sing₀`, which has empty interior.

## Hypothesis checklist

| paper | here |
|---|---|
| a BTZ point of an `E_{≥0}`-manifold (`rem:K_neq_I`, l.876) | ⚠ read as a point of `S₀` under `BTZAxioms` (the named model facts, kb/0012) |
| `prop:K_calcul` (c): `M` causal (l.1561) | ✓ carried for the equality (`BTZAxioms.K_neq_I`); the separation needs none (`BTZAxioms.Kminus_ne_Iminus`, ⚠ weakened) |
| an `E_{≥0}`-manifold (for plainness) | ⚠ read as `SingularFlatAxioms`, with strong causality asked (`SingularFlatAxioms.causallyPlain`) |

## SCOPE (disclosed)

* **No label marked.** `rem:K_neq_I`'s BTZ sentence is anchored at the model `E₀`
  (`Causal.E0.K_neq_I_btz`, `Causal.Port.E0ModelRows`), which uses these lemmas; the abstract form
  here reads "a BTZ point" as `BTZAxioms`.
* **Plainness at singular flat spacetimes** bears on OQ-16 and on `rem:pas_plat` (ii) (l.294):
  a BTZ point never witnesses a failure of causal plainness (kb/0029). Recorded, not a ruling.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. The text was written
by T-ett-e0-model-rows in `Causal.Port.E0ModelRows` (HEAD `bd1fafb` l.80–104, l.138–143).
-/

namespace Causal

open Set TopologicalSpace Topology Filter

/-! ### A BTZ point, abstractly (`BTZAxioms`, kb/0012) -/

namespace Causality

variable {M : Type*} [TopologicalSpace M] {C : Causality M} {S₀ : Set M} {p : M}

/-- At a BTZ point the causal past minus the point is not empty (field `singularPastAt`). -/
theorem BTZAxioms.Jminus_diff_nonempty (h : C.BTZAxioms S₀) (hp : p ∈ S₀) :
    (C.Jminus ⊤ {p} \ {p}).Nonempty := by
  obtain ⟨⟨u, -, hu⟩, -⟩ := h.singularPastAt p hp
  exact ⟨u 0, by simpa using (hu 0).1, (hu 0).2⟩

/-- **`K⁻(p) ≠ I⁻(p)` at a BTZ point, with no causality asked**: `J⁻(p) ∖ {p}` lies in `K⁻(p)`
(`SingularPastAt.Jminus_diff_subset_Kminus`) and is not empty, while `I⁻(p) = ∅`. The separation
of `rem:K_neq_I` survives where the equality `K⁻(p) = J⁻(p) ∖ {p}` is not available. -/
theorem BTZAxioms.Kminus_ne_Iminus (h : C.BTZAxioms S₀) (hp : p ∈ S₀) :
    C.Kminus ⊤ {p} ≠ C.Iminus ⊤ {p} := by
  intro hKI
  obtain ⟨x, hx⟩ := h.Jminus_diff_nonempty hp
  have hxK := (h.singularPastAt p hp).Jminus_diff_subset_Kminus hx
  rw [hKI, h.Iminus_eq_empty p hp] at hxK
  exact hxK

/-- **The BTZ sentence of `rem:K_neq_I` under `BTZAxioms`** (`ETT.tex:875–877`, the BTZ point of
an `E_{≥0}`-manifold read as the named model facts, kb/0012), `M` causal as `prop:K_calcul` (c)
assumes: `I⁻(p) = ∅`, `K⁻(p) = J⁻(p) ∖ {p} ≠ ∅`, hence `K⁻(p) ≠ I⁻(p)`. -/
theorem BTZAxioms.K_neq_I (h : C.BTZAxioms S₀) (hc : C.IsCausal) (hp : p ∈ S₀) :
    C.Iminus ⊤ {p} = ∅ ∧ C.Kminus ⊤ {p} = C.Jminus ⊤ {p} \ {p} ∧
      C.Jminus ⊤ {p} \ {p} ≠ ∅ ∧ C.Kminus ⊤ {p} ≠ C.Iminus ⊤ {p} :=
  ⟨h.Iminus_eq_empty p hp, Kminus_eq_Jminus_diff hc (h.singularPastAt p hp),
    (h.Jminus_diff_nonempty hp).ne_empty, h.Kminus_ne_Iminus hp⟩

/-! ### Singular flat spacetimes are causally plain -/

/-- **A strongly causal `SingularFlatAxioms` spacetime is causally plain.** -/
theorem SingularFlatAxioms.causallyPlain {sing : ℝ → Set M} (h : C.SingularFlatAxioms sing)
    (hSC : C.StronglyCausal) : C.CausallyPlain :=
  causallyPlain_of_locZ h.pushUp (E0LM.locZplus_of h.causallyArcConnected hSC h.mem_Zplus)
    (E0LM.locZminus_of h.causallyArcConnected hSC fun y hy => (h.mem_Zminus_iff y).2 hy)
    (h.interior_sing 0 le_rfl)

end Causality

end Causal
