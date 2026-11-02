import Causal.CompactCauchy

/-!
# Lemma K, the bare DEC-44 form — the scaffold half of `Causal.CompactCauchy`

No label is marked. This module holds only the **bare** DEC-44 form of Lemma K,
`isCauchySurface_of_isLocallyCauchy` (locally Cauchy only, no splitting, no two-sidedness), stated
with a tagged `sorry` so that gx has a target declaration. Lemma K's proved form
(`isCauchySurface_of_isLocallyCauchyTwoSided`), its sources in Barbot (Rem 2.3 `clomax`, §11) and
Brunswic (`prop:cauchy_abs_max`), its hypothesis checklist and the obstruction to the bare form
are in the strict module `Causal.CompactCauchy`, which this one imports; the statement below is
the one that module carried until the graduation of 2026-11-02, unchanged.

## Hypothesis checklist

| DEC-44 hypothesis | here |
|---|---|
| `C` a causality on `M`, `M` connected, `C.GloballyHyperbolic` | ✓ carried |
| `Σ` compact, connected, locally Cauchy (`IsLocallyCauchy`) | ✓ carried |
| separation | ⚠ `T2Space M` |
| — | ⚠ added: `C.Tarentin`, `C.CausallyArcConnected`, `J^±(p) ≠ {p}` (the regularity hypotheses of the proved form; fields of `SingularFlatAxioms`, or true at a BTZ point) |

## SCOPE (disclosed)

* **Not proved**: one `sorry -- SORRY(DEC-44)`. Open in ETT generality and possibly false; the
  obstruction (no global projection, no two-sidedness) is `Causal.CompactCauchy`'s SCOPE.
  Nothing may depend on it, and no declaration does.
* `Causal.LemmaKBare` settles it wherever curves extend, `C` has push-up and `Z^± = M`, without
  importing this module.
* **DEC-92 (2026-11-02), attempted, not settled.** `Causal.LemmaKReduction` narrows it: with no
  curve extension, a compact non-empty acausal `Σ` with `J^+(Σ) ∪ J^-(Σ)` open is Cauchy
  (`isCauchySurface_of_isAcausal_of_isOpen`); under `CurvesExtend`, Cauchy ⇔ acausal and
  `J^+(Σ) ∪ J^-(Σ) = M` (`isCauchySurface_iff_of_curvesExtend`). Proving that a compact
  connected locally Cauchy `Σ` is acausal, with `J^+(Σ) ∪ J^-(Σ)` open, proves the bare form;
  under `CurvesExtend` the two are equivalent (without it, refuting either does not refute
  Lemma K). The long ray, `CurvesExtend`'s conjectured counterexample, is not a counterexample
  to Lemma K: the long ray has no inextensible curve, so every set is
  Cauchy there (`isCauchySurfaceOn_of_forall_not_inextensible`); a counterexample must mix a
  region without inextensible curves with inextensible curves that never enter its charts
  (`exists_mem_of_inextensible_of_mem_chart`) and have no point above them
  (`exists_not_le_of_inextensible`). None was found. This statement carries no second
  countability (ETT's spacetimes are second countable, `ETT.tex:255`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Function

universe u

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable {C : Causality M}

/-- **Lemma K, the bare DEC-44 form — OPEN, tagged `sorry`; nothing may depend on it.** On a
connected Hausdorff tarentin globally hyperbolic causally arc-connected spacetime with
`J^±(p) ≠ {p}`, a compact connected locally Cauchy set is a Cauchy surface. This is the target gx
points at; it is proved in `Causal.CompactCauchy`
(`isCauchySurface_of_isLocallyCauchyTwoSided`) only under two more
data, a global splitting with causally monotone lines and two-sidedness in the charts. The
regularity hypotheses kept here are those of the proved form, all dischargeable by gx
(`SingularFlatAxioms.tarentin`, `.causallyArcConnected`, `.t2`; `J^-(p) ≠ {p}` at a BTZ point by
its past half-line); it is not known whether the statement holds in ETT generality. -/
theorem isCauchySurface_of_isLocallyCauchy [T2Space M] [ConnectedSpace M]
    (hT : C.Tarentin) (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected)
    (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p})
    {S : Set M} (hSc : IsCompact S) (hSconn : IsConnected S) (hloc : C.IsLocallyCauchy S) :
    C.IsCauchySurface S :=
  sorry -- SORRY(DEC-44): open in ETT generality, possibly false. (1) No global projection: without a splitting (or a covering map) of M there is nothing to compare Σ with, which is Brunswic's covering step (prop:cauchy_abs_max, BTZ_1.tex:1048-1074, uses N ≃ Σ_N × ℝ). (2) No two-sidedness: in a chart U a point of U near Σ may be related to Σ ∩ U only through points of Σ outside U, so the time window of the box step (exists_box_of_twoSided) is uncontrolled, and excluding it needs global acausality of Σ, which is the conclusion. Proved under both data as isCauchySurface_of_isLocallyCauchyTwoSided.

end Causality

end Causal
