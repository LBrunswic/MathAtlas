import Syracuse.Approaches.MRunsRhin

/-!
# The run frontier without Hercher's Corollary 29

The frontier theorems (`RunsFrontier`, `MRunsDichotomy`, `MRunsExplicit`, `MRunsRhin`) were proved
from `o, E > 1.375·10^{11}`, which needs Hercher's Corollary 29 on top of Barina's verification. Each
now has a general form over any cycle bounds `CycleLength.CycleBounds No NE` (suffix `_of`), and
`CycleLength.cycle_length_ge` proves `o ≥ 72 057 431 991` and `E ≥ 114 208 327 604` from Barina alone.
Instantiating gives the frontier with one literature input fewer:

| Frontier | with Hercher Cor. 29 | Barina only |
|---|---|---|
| two runs over a tree, root core `≤ 2^K` | `20K ≤ 1.375·10^{11}` | `20K ≤ 1.142·10^{11}` |
| three letter runs `1^a d^b e^c` | `11(d + e + 2) ≤ 1.375·10^{11}` | `11(d + e + 2) ≤ 1.142·10^{11}` |
| `≤ 3` runs, base weight `B` (Ellison) | `B ≤ 10^9` | `B ≤ 9.5·10^8` |
| `≤ 10` runs (Rhin) | `B ≤ 5·10^7` | `B ≤ 5·10^7` (unchanged) |
| `≤ 20` runs (Rhin) | `B ≤ 6·10^5` | `B ≤ 5.5·10^5` |

## Coverage

| Claim | Lean name | Status |
|---|---|---|
| two runs over a tree | `frontier_two_runs_barina` | proved (conditional on Ellison + Barina) |
| three letter runs | `frontier_three_letters_barina` | proved (same) |
| **`≤ 3` runs over base weight `≤ 9.5·10^8`** | `frontier_le_three_barina` | proved (same) |
| two and three long runs over base weight `≤ 9.5·10^8` | `frontier_mruns_barina` | proved (same) |
| **`≤ 10` runs over `≤ 5·10^7`; `≤ 20` runs over `≤ 5.5·10^5`** | `frontier_ten_barina`, `frontier_twenty_barina` | proved (conditional on Lemma 12 + Barina) |
-/

namespace Syracuse.BarinaFrontier

open Finset Syracuse Syracuse.TwoBackground Syracuse.MRuns

/-- **Two runs over a tree, Barina only.** -/
theorem frontier_two_runs_barina (hEl : CycleLiterature.Ellison1971)
    (hB : CycleLiterature.Barina2025) {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) (hx : 0 < x)
    (hx1 : x ≠ 1) {u₀ v₀ : Word} (hu₀ : u₀.Pos) (hv₀ : v₀.Pos) (hu₀0 : u₀ ≠ []) (hv₀0 : v₀ ≠ [])
    (hC : core (2 : ℤ) 3 u₀ v₀ ≠ 0) {K : ℕ} (hK : |core (2 : ℤ) 3 u₀ v₀| ≤ 2 ^ K)
    (hK' : 20 * K ≤ 114208327603) {u v : Word} (hst : Trees.Tree u₀ v₀ u v) {a b : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) : ¬ (gapWord x o ~r bpow u a ++ bpow v b) :=
  RunsFrontier.frontier_two_runs_of hEl (CycleLength.cycleBounds_barina hB) (by norm_num) h hx hx1
    hu₀ hv₀ hu₀0 hv₀0 hC hK hK' hst ha hb

/-- **Three letter runs, Barina only.** -/
theorem frontier_three_letters_barina (hEl : CycleLiterature.Ellison1971)
    (hB : CycleLiterature.Barina2025) {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) (hx : 0 < x)
    (hx1 : x ≠ 1) {d e : ℕ} (hd : 2 ≤ d) (he : 2 ≤ e) (hde : d ≠ e)
    (hsmall : 11 * (d + e + 2) ≤ 114208327603) {a b c : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    ¬ (gapWord x o ~r List.replicate a 1 ++ List.replicate b d ++ List.replicate c e) :=
  RunsFrontier.frontier_three_letters_of hEl (CycleLength.cycleBounds_barina hB) (by norm_num) h hx
    hx1 hd he hde hsmall ha hb hc

/-- **At most three runs, Barina only.** Given Ellison and Barina, no nontrivial positive cycle is a
rotation of `p₀^{a₀} ⋯ p_{m-1}^{a_{m-1}}` (`1 ≤ m ≤ 3`) over positive nonempty base blocks of total
weight `B ≤ 9.5·10^8`. -/
theorem frontier_le_three_barina (hEl : CycleLiterature.Ellison1971)
    (hB : CycleLiterature.Barina2025) {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) (hx : 0 < x)
    (hx1 : x ≠ 1) {p : ℕ → Word} {a : ℕ → ℕ} {m : ℕ} (hm : 1 ≤ m) (hm3 : m ≤ 3)
    (hp : ∀ i, p (i + m) = p i) (ha : ∀ i, a (i + m) = a i) (hpos : ∀ i, (p i).Pos)
    (hne : ∀ i, p i ≠ []) (hne' : ∀ i, bpow (p i) (a i) ≠ [])
    (hsmall : ∑ k ∈ range m, (p k).sum ≤ 950000000) :
    ¬ (gapWord x o ~r cat (fun i => bpow (p i) (a i)) m) :=
  MRunsDichotomy.frontier_le_three_of hEl (CycleLength.cycleBounds_barina hB) h hx hx1 hm hm3 hp ha
    hpos hne hne' (by omega) (by omega)

/-- **Two and three long runs, Barina only.** -/
theorem frontier_mruns_barina (hEl : CycleLiterature.Ellison1971)
    (hB : CycleLiterature.Barina2025) {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) (hx : 0 < x)
    (hx1 : x ≠ 1) {p : ℕ → Word} {a : ℕ → ℕ} {m : ℕ} (hm : 2 ≤ m) (hm3 : m ≤ 3)
    (hp : ∀ i, p (i + m) = p i) (ha : ∀ i, a (i + m) = a i) (hpos : ∀ i, (p i).Pos)
    (hne : ∀ i, p i ≠ []) (hC : ∀ i, core (2 : ℤ) 3 (p i) (p (i + 1)) ≠ 0)
    (hlong : ∀ i, 6 * (∑ k ∈ range m, (p k).sum) + 1 < (bpow (p i) (a i)).sum)
    (hsmall : ∑ k ∈ range m, (p k).sum ≤ 950000000) :
    ¬ (gapWord x o ~r cat (fun i => bpow (p i) (a i)) m) :=
  MRunsExplicit.frontier_mruns_of hEl (CycleLength.cycleBounds_barina hB) h hx hx1 hm hm3 hp ha hpos
    hne hC hlong (by omega)

/-- **At most ten runs, Barina only**: base weight `≤ 5·10^7`, as with Hercher. -/
theorem frontier_ten_barina (hR : CycleLiterature.SimonsDeWegerLemma12)
    (hB : CycleLiterature.Barina2025) {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) (hx : 0 < x)
    (hx1 : x ≠ 1) {p : ℕ → Word} {a : ℕ → ℕ} {m : ℕ} (hm : 1 ≤ m) (hm10 : m ≤ 10)
    (hp : ∀ i, p (i + m) = p i) (ha : ∀ i, a (i + m) = a i) (hpos : ∀ i, (p i).Pos)
    (hne : ∀ i, p i ≠ []) (hne' : ∀ i, bpow (p i) (a i) ≠ [])
    (hsmall : ∑ k ∈ range m, (p k).sum ≤ 50000000) :
    ¬ (gapWord x o ~r cat (fun i => bpow (p i) (a i)) m) :=
  MRunsRhin.frontier_ten_of hR (CycleLength.cycleBounds_barina hB) (by norm_num) h hx hx1 hm hm10 hp
    ha hpos hne hne' hsmall (by norm_num)

/-- **At most twenty runs, Barina only**: base weight `≤ 5.5·10^5`. -/
theorem frontier_twenty_barina (hR : CycleLiterature.SimonsDeWegerLemma12)
    (hB : CycleLiterature.Barina2025) {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) (hx : 0 < x)
    (hx1 : x ≠ 1) {p : ℕ → Word} {a : ℕ → ℕ} {m : ℕ} (hm : 1 ≤ m) (hm20 : m ≤ 20)
    (hp : ∀ i, p (i + m) = p i) (ha : ∀ i, a (i + m) = a i) (hpos : ∀ i, (p i).Pos)
    (hne : ∀ i, p i ≠ []) (hne' : ∀ i, bpow (p i) (a i) ≠ [])
    (hsmall : ∑ k ∈ range m, (p k).sum ≤ 550000) :
    ¬ (gapWord x o ~r cat (fun i => bpow (p i) (a i)) m) :=
  MRunsRhin.frontier_twenty_of hR (CycleLength.cycleBounds_barina hB) (by norm_num) h hx hx1 hm hm20
    hp ha hpos hne hne' hsmall (by norm_num)

end Syracuse.BarinaFrontier
