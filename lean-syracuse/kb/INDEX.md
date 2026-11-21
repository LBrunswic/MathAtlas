# Knowledge base — working in `lean-syracuse`

What working in this library is like: conventions, patterns, pitfalls. Read before you start;
propose an entry when you finish. One fact per entry. `lean-causal/kb/INDEX.md` holds the hub's
older entries (the docstring contract is its `0006`; weakest hypotheses `0007`; no quiet weakening `0011`).

| id | kind | entry |
|---|---|---|
| [0001](entries/0001-wave-0.md) | convention | Wave 0: Mathlib only |
| [0002](entries/0002-z2ring-api.md) | pattern | The ℤ/2ℤ-ring API, and the total maps with a junk value at −1/3 |
| [0003](entries/0003-two-ne-zero.md) | pitfall | ZMod 2 is a ℤ/2ℤ-ring with 2 = 0; Mathlib's multiplicity of 0 is 1 |
| [0004](entries/0004-bold-label-is-a-mark.md) | pitfall | Any bold backticked label in the first 4000 characters is a mark |
| [0005](entries/0005-injectivity-by-krull.md) | pattern | Injectivity of x ↦ (p_n(x)) needs no completion: lem:base twice, then Krull |
| [0006](entries/0006-series-in-z2.md) | pattern | Series in ℤ_[2], and 1/3 as a unit |
| [0007](entries/0007-product-form-over-z.md) | pattern | Over ℤ every bound on p_n log 2 − n log 3 is a sum of log(1 + 1/(3Tᵏx)) |
| [0008](entries/0008-cast-iterate-pitfall.md) | pitfall | `(T^[n] x : ℝ)` iterates T over ℝ: write `((T^[n] x : ℤ) : ℝ)` |
| [0009](entries/0009-limsup-junk.md) | pattern | A real limsup is a junk value when unbounded above: state boundedness beside it |
| [0010](entries/0010-to-z2.md) | pattern | The map A → ℤ₂ of a ℤ/2ℤ-ring with 2 ≠ 0: Syracuse.toZ2 |
| [0011](entries/0011-two-adic-topology.md) | pattern | The 2-adic topology and the completion as ℤ₂ |
| [0012](entries/0012-no-limit-at-minus-third.md) | pattern | T has no limit at −1/3: two integer sequences |
| [0013](entries/0013-section2-sums-and-windows.md) | pattern | § 2 sums are A_u^n sums; windows of a periodic sequence; ν₂, ν₃ by divisibility |
| [0014](entries/0014-two-index-conventions.md) | convention | § 2 has two index conventions for a_i: state both where a display depends on it |
| [0015](entries/0015-two-readings-transfer.md) | pattern | § 3 algebra: two identities carry every statement between the two readings of OQ-43 |
| [0016](entries/0016-explicit-cycles-by-decide.md) | pattern | An explicit cycle in Lean: T_unique per step, then decide on the periodic sequence |
| [0017](entries/0017-periodic-on-z.md) | pattern | Periodic functions on ℤ: reduce mod n, extend from one period, induct both ways |
| [0018](entries/0018-undefined-hypothesis-reading-free.md) | pattern | Refute a statement with an undefined hypothesis without choosing its reading |
| [0019](entries/0019-rec-pushneg-int-casts.md) | pitfall | `rec` is a keyword; `push_neg` is deprecated; `Periodic.int_mul` leaves ((q : ℤ) : ℤ) casts |
