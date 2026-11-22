# places-elimination — status

- **Status:** active. Started 2026-10-29.
- **Lean:** `lean/Syracuse/Approaches/TwoRun.lean` and `lean/Syracuse/Approaches/Vojta.lean`. Both are
  axiom-clean: `scripts/AuditAxioms.lean` reports `propext`, `Classical.choice` and `Quot.sound` only.

| result | status | where |
|---|---|---|
| ρ into Aff₁(ℤ[1/6]); cycle ⟺ res_w[S] = 0 ⟺ ρ(w) scalar mod D | derived (notes) | RATIONALE §1 |
| 3x+k = base change to ℤ[1/6k]; every word is a 3x+k cycle | derived (notes) | §2 |
| dimension criterion: r = 1 ⇒ core, r ≥ 2 ⇒ elimination ideal 0 | verified on 3 families | §3, `elim.py` |
| two-run closed forms, resultant certificate | **proved** | `TwoRun.twoRun_D/S`, `certificate` |
| uniform ceiling D ∣ R*(2^d,2^{e₁},2^{e₂},3) on a cycle | **proved** | `TwoRun.twoRun_ceiling` |
| R* ≠ 0 unless e₁ = e₂ = d | **proved** | `TwoRun.Rstar_ne_zero` |
| exclusion from finitely many checks | **proved** | `TwoRun.noCycle_of_check`, `noCycle_ge_of_check` |
| nine sample families decided | **proved** | `TwoRun.noCycle_1_2_3`, … (emitted by the decider) |
| Levin's gcd theorem (Vojta, S-unit case) | stated (hypothesis) | `Vojta.LevinGcd`, `LevinTheorem` |
| Levin + lower bound ⇒ cycles in exceptional sets or bounded length | **proved (conditional)** | `Vojta.cycles_of_levin` |
| the same for d^a e d^b f (r = 2) | **proved (conditional)** | `Vojta.twoLen_cycles_of_levin` |
| r = 1 is Levin with ε = 0 | **proved** | `Vojta.gcd6_le_of_certificate` |
| general decider (one-parameter, two-run, u^a v^b + rational lines) | script | `decide_family.py` |
| **classification of r = 1 families** (finite cycle set, or constant fixed point = powers of one cycle) | **proved** | `R1.classification`, `R1.const_one_orbit` ([`CLASSIFICATION.md`](CLASSIFICATION.md)) |
| **verified total decision procedure `decideR1`** (kernel-runnable) | **proved** | `R1.decideR1_correct`, `R1.decideR1_iff`; instances in `R1/Examples.lean`; 70-family randomized cross-check vs brute force, 0 mismatches (`r1_lean.py`) |
| uniform classification of `w^a w'` (core `C(w,w')`) | **proved** | `R1.wpow_append_classification` |
| nested `(w^a w')^b w''`: Plücker step, zero set, joint bound, classification | **proved** | `R1.nested_classification` ([`NESTED.md`](NESTED.md)) |
| **towers of any depth meet only finitely many cycles** | **proved** | `R1.tower_cycleStarts_finite` |
| skeleton compiler + seven uniform skeleton theorems (ceiling, finiteness) | **proved** | `R1.Skel.*` ([`SKELETONS.md`](SKELETONS.md), `skeleton.py`) |
| same-side two-exponent families `u^a x v^b y`: linear form, `a` bounded, classification | **proved** | `R1.twoExp_classification` |
| **every two-exponent family `u^a x v^b y` (any sides, incl. straddling class X)**: finite off the loci, explicit bound | **proved (conditional on Matveev)** | `R1.twoExp_cycles_of_matveev`, `R1.twoExp_pow_le_of_polyLB` |
| effective decider for `u^a x v^b y` (continued-fraction reduction of the Matveev bound) | script | `decide_twoexp.py`, `--selftest`: 150 families, 0 mismatches vs brute force |
| scheme formulation reviewed: intersection identity, families as subgroup orbits, partial cores, archimedean tropicalisation | derived | [`SCHEME.md`](SCHEME.md) |
| **tropical budget**: k independent blocks settled off the loci iff `min(A,B) < 1` (rotation cores + Matveev); reproduces m ≤ 2 for m-cycles | derived (k ≤ 2 proved); LP-checked on 12 families | [`SCHEME.md`](SCHEME.md) §2.4, `budget.py` |
| pattern-intersection chart (7 classes, exclusive witnesses) | computed | [`PATTERNS.md`](PATTERNS.md), `patterns/` |

## Next

- Fetch Levin 2019 into `sources/` and pin the exceptional-set statement.
- ~~Lean emission for general r = 1 families~~ — superseded by `R1.decideR1` (2026-10-30).
- Verify the Ridout claim against `PROGRAM.md` §3.
