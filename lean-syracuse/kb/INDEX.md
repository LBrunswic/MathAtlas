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
