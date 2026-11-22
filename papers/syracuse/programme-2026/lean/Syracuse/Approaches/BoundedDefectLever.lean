import Syracuse.Basic

/-!
# The bounded-defect lever (`approaches/bounded-defect-lever`)

Formalises `approaches/bounded-defect-lever/{RATIONALE,STATUS}.md` with its incubator notes
`ideas/cocycle-combinatorics/drafts/{bounded-defect-lever,inner-core-extraction,covering-reductions}.md`
and the move calculus of `PROGRAM.md` §4. Every identity is proved for arbitrary `X Y` in an arbitrary
commutative ring (= a `ℤ[X,Y]` identity) and then specialised to `(2,3)`. The cycle input is only
`Follows.D_dvd_S_rotate`: on a genuine cycle `D = 2^E - 3^o` divides every rotation sum.

## Coverage

| Note claim (source) | Lean name | Status |
|---|---|---|
| Shared-frame extraction `S(PMQ)-S(PM'Q) = X^{\|P\|}Y^{len Q}(S M - S M')` for `χ(M)=χ(M')` (RATIONALE; draft "engine") | `S_frame_sub` | proved; both `\|M\|=\|M'\|` and `len M = len M'` are needed (counterexample `example`s) |
| Unbalanced case "carries an extra term `X^{\|P\|}(X^{\|M\|}-X^{\|M'\|})S(Q)`" (draft) | `S_frame_sub_general` | corrected (completed): exact when `len M = len M'`; if the lengths differ too there is a second term `(Y^{len M+len Q}-Y^{len M'+len Q})S(P)` |
| §4 frame strip, prefix (`PROGRAM.md`) | `frame_strip_prefix` | proved |
| §4 frame strip, suffix "peels as `Y^{\|z\|}`" | `frame_strip_suffix` | corrected: the factor is `Y^{len z}` (counterexample `example`: `u=(1,2), v=(2,1), z=(3)`) |
| §4 anchor split at `k` with `e_k(u)=e_k(v)` | `anchor_split` | proved (needs `len u = len v`; `n = len u`) |
| §4 anchored free basis generates all differences | `diffIdeal_eq_anchored` | proved for one anchor; corrected: per-group anchoring (tool `group_by="first"`) has rank `o - #groups` and misses cross-group differences unless anchor-to-anchor differences are added |
| §4 recursion to leaves, combination round, "simplest representative" | — | not formalized (algorithmic) |
| [P1] inner-core identity, `χ`-form | `inner_core_chi` (homogenised: `inner_core`) | proved |
| [P1] structural unit family `S(y)=S(y')`, ratio `χ(x)/χ(y')` | `inner_core_unit_case` | proved |
| [P1] Gen 5: suffix cocycle `Ŝ(ab)=Ŝ(b)+Ŝ(a)/χ(b)`, closed forms A and B | `Shat_append`, `inner_core_hat'`, `inner_core_hat` | proved |
| [P1] literal Move 2 false; 58 sporadic unit cases | — | not formalized (dead end; numerical counts) |
| Lever wedge `S(d^kβd^{L-k})-S(d^{k+1}βd^{L-k-1}) = X^{kd}Y^{L-k-1}(S(βd)-S(dβ))` | `wedge` | proved (`k < L`; exponents as in the note) |
| Periodic background F1 (`covering-reductions`) | `wedge_block` | proved |
| Both wedge terms are rotations of `β d^L` (resp. `β u^L`) | `isRotated_blockPow` | proved |
| Telescoped sliding `S(βd^L)-S(d^Lβ) = S(d^L)(S(βd)-S(dβ))`, `S(d^L)=(X^{Ld}-Y^L)/(X^d-Y)` (L1·8 pointer) | `slide`, `S_replicate_mul`, `slide_block` | proved |
| `o`-independent ceiling `G ≤ sixfree(S(βd)-S(dβ))` (boxed) | `ceiling`; `ceiling_dvd_block`, `ceiling_block` (F1) | proved (`L ≥ 1`, core `≠ 0`) |
| "with a transcendence lower bound this caps `o`" | `ceiling_squeeze`, `ceiling_finite` | proved (conditional on a lower bound `B ≤ \|2^E-3^o\|`, resp. `B → ∞`) |
| `β` a letter recovers structure.md P2: wedge `X^{(o-1)d}(X^{e-d}-1)`, ceiling `sixfree(2^{\|e-d\|}-1)` | `single_defect_core`, `single_defect_wedge`, `sixFree_two_pow_sub_two_pow`, `single_defect_ceiling` | proved |
| Ceiling `= sixfree ∏_{k∣\|e-d\|} Φ_k(2)` | `two_pow_sub_one_eq_prod_cyclotomic` | proved |
| Collapse to `1` iff `\|e-d\| ∈ {1,2}` | `sixFree_two_pow_sub_one_eq_one_iff`, `single_defect_collapse` | proved (cycle consequence: `\|2^E-3^o\| = 1`) |
| "`G ≤ 1`: only the trivial circuit" | `no_positive_cycle_single_defect` | proved for positive cycles; imprecise for negative ones: `-5 → -7` (word `(1,2)`, `e=1, d=2`) lies in the family with `\|D\|=1` |
| Reach: `d e₁ d^B e₂ d` via `β = e₂ d² e₁` | `isRotated_two_defect`, `ceiling_two_defect` | proved |
| Atlas values `5` (`β=(2,3)`), `65` (`(3,4)`), `1103` (`(4,3,4)`), `127` (`(4,1,1,3)`), all `d = 1` | `ceiling_atlas_23_1`, `ceiling_atlas_34_1`, `ceiling_atlas_434_1`, `ceiling_atlas_4113_1` | proved (the note omits `d`; `d = 1` reproduces all four) |
| Genuine 2-defect arcs never collapse, ceilings `≥ 5`; single-defect ceiling tight | — | empirical/not formalized (finite scans) |
| Multi-anchor identity `S(W)-S(W') = Σ X^{Pre_i}Y^{Suf_i}(S(b_i)-S(b_i'))` | `multi_anchor` | proved |
| F2/F3 divergence; covering Parts 2–3 | — | empirical / open |
| `≥ 2` growing-run no-go (open, Gen 4 reduction) | `TwoRunNoGo` (`UniformScheme`, `unitCombo`, `twoRunWord`); control `oneRun_uniformScheme` | stated only. The **family itself is excluded** in `Syracuse.TwoRun` by a non-unit (resultant) certificate: `TwoRun.twoRun_ceiling`, `TwoRun.noCycle_of_check` |
| Gen 4 PART A (`gcd_j S^{(j)}(W_a)=1`), PART C (non-cyclotomic factor), C8 backbone | — | empirical / sibling approach |
-/

namespace Syracuse.BoundedDefectLever

open Syracuse

/-! ## Local arithmetic helpers -/

/-- `sixFree` ignores the sign. -/
@[simp] lemma sixFree_neg (c : ℤ) : sixFree (-c) = sixFree c := by simp [sixFree]

/-- `sixFree` ignores powers of `2` and `3`. -/
lemma sixFree_pow_mul (i j : ℕ) (c : ℤ) : sixFree (2 ^ i * 3 ^ j * c) = sixFree c := by
  have h3 : ordCompl[2] (3 ^ j) = 3 ^ j := by
    rw [Nat.factorization_eq_zero_of_not_dvd, pow_zero, Nat.div_one]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two Nat.prime_three).1
      (Nat.prime_two.dvd_of_dvd_pow h)
    omega
  simp only [sixFree, Int.natAbs_mul, Int.natAbs_pow, Int.reduceAbs]
  rw [mul_assoc, Nat.ordCompl_self_pow_mul _ _ Nat.prime_two, Nat.ordCompl_mul, h3,
    Nat.ordCompl_self_pow_mul _ _ Nat.prime_three]

/-- A nonzero integer has a positive `6`-free part. -/
lemma sixFree_pos {c : ℤ} (hc : c ≠ 0) : 0 < sixFree c :=
  Nat.ordCompl_pos 3 (Nat.ordCompl_pos 2 (Int.natAbs_ne_zero.2 hc)).ne'

/-- The `6`-free part is at most the absolute value. -/
lemma sixFree_le_natAbs (c : ℤ) : sixFree c ≤ c.natAbs :=
  (Nat.ordCompl_le _ 3).trans (Nat.ordCompl_le _ 2)

/-- `D = 2^E - 3^o` is coprime to `6` once `E ≥ 1` and `o ≥ 1`. -/
lemma Dz_coprime_six {w : Word} (hE : 1 ≤ w.sum) (ho : 1 ≤ w.length) :
    Nat.Coprime (Dz w).natAbs 6 := by
  have h2 : ¬ (2 : ℤ) ∣ Dz w := by
    have hodd : Odd (Dz w) := Even.sub_odd ((Int.even_pow).2 ⟨even_two, by omega⟩)
      (Odd.pow (by decide))
    exact fun h => (Int.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h)
  have h3 : ¬ (3 : ℤ) ∣ Dz w := by
    intro h
    have h' : (3 : ℤ) ∣ 2 ^ w.sum := by
      have := dvd_add h (dvd_pow_self (3 : ℤ) (by omega : w.length ≠ 0))
      simpa [D] using this
    have := Int.prime_three.dvd_of_dvd_pow h'
    norm_num at this
  rw [show (6 : ℕ) = 2 * 3 from rfl]
  refine Nat.Coprime.mul_right ?_ ?_
  · exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2
      fun h => h2 (Int.natCast_dvd.2 h))
  · exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2
      fun h => h3 (Int.natCast_dvd.2 h))

/-- `D ≠ 0` once `E ≥ 1` and `o ≥ 1`. -/
lemma Dz_ne_zero {w : Word} (hE : 1 ≤ w.sum) (ho : 1 ≤ w.length) : Dz w ≠ 0 := by
  intro h
  have := Dz_coprime_six hE ho
  rw [h] at this
  norm_num at this

/-! ## Shared-frame extraction (the engine) -/

section Ring

variable {R : Type*} [CommRing R] (X Y : R)

/-- **Shared-frame extraction, general form.** Without any balance hypothesis,
`S(PMQ) - S(PM'Q)` is the frame term `X^{|P|} Y^{len Q} (S M - S M')` plus two correction terms,
one carrying `S(P)` (vanishing iff `len M = len M'`) and one carrying `S(Q)` (vanishing iff
`|M| = |M'|`). -/
theorem S_frame_sub_general (P M M' Q : Word) :
    S X Y (P ++ M ++ Q) - S X Y (P ++ M' ++ Q) =
      (Y ^ (M.length + Q.length) - Y ^ (M'.length + Q.length)) * S X Y P
      + X ^ P.sum * Y ^ Q.length * (S X Y M - S X Y M')
      + X ^ P.sum * (X ^ M.sum - X ^ M'.sum) * S X Y Q := by
  simp only [S_append, List.sum_append, pow_add]
  ring

/-- **Shared-frame extraction** (`bounded-defect-lever` engine, dual of [P1]). When the inner
blocks are `χ`-balanced (`|M| = |M'|` **and** `len M = len M'`), the shared outer frame `P, Q`
extracts as the unit `X^{|P|} Y^{len Q}`. -/
theorem S_frame_sub (P Q : Word) {M M' : Word} (hsum : M.sum = M'.sum)
    (hlen : M.length = M'.length) :
    S X Y (P ++ M ++ Q) - S X Y (P ++ M' ++ Q) = X ^ P.sum * Y ^ Q.length * (S X Y M - S X Y M') := by
  rw [S_frame_sub_general, hsum, hlen]
  ring

/-! ### The move calculus of `PROGRAM.md` §4 -/

/-- **Frame strip, prefix** (§4 move 2). For `len u = len v` a shared prefix `x` peels as
`X^{|x|}`. -/
theorem frame_strip_prefix (x : Word) {u v : Word} (h : u.length = v.length) :
    S X Y (x ++ u) - S X Y (x ++ v) = X ^ x.sum * (S X Y u - S X Y v) := by
  rw [S_append, S_append, h]
  ring

/-- **Frame strip, suffix** (§4 move 2, corrected exponent). For `|u| = |v|` a shared suffix `z`
peels as `Y^{len z}` (the number of letters of `z`, *not* its gap-sum `|z|`). -/
theorem frame_strip_suffix (z : Word) {u v : Word} (h : u.sum = v.sum) :
    S X Y (u ++ z) - S X Y (v ++ z) = Y ^ z.length * (S X Y u - S X Y v) := by
  rw [S_append, S_append, h]
  ring

/-- **Anchor split** (§4 move 3). If `len u = len v = n` and the prefix gap-sums agree at
position `k` (`e_k(u) = e_k(v)`), then
`S(u) - S(v) = Y^{n-k} (S(u_{<k}) - S(v_{<k})) + X^{e_k} (S(u_{≥k}) - S(v_{≥k}))`. -/
theorem anchor_split {u v : Word} (k : ℕ) (hlen : v.length = u.length) (he : e u k = e v k) :
    S X Y u - S X Y v =
      Y ^ (u.length - k) * (S X Y (u.take k) - S X Y (v.take k))
      + X ^ e u k * (S X Y (u.drop k) - S X Y (v.drop k)) := by
  conv_lhs => rw [← List.take_append_drop k u, ← List.take_append_drop k v]
  rw [S_append, S_append]
  simp only [List.length_drop, hlen]
  rw [show (u.take k).sum = e u k from rfl, show (v.take k).sum = e v k from rfl, he]
  ring

end Ring

/-- The suffix strip really carries `Y^{len z}`: with `u = (1,2)`, `v = (2,1)`, `z = (3)` the
difference at `(2,3)` is `-6 = 3^{len z}·(-2)`, not `3^{|z|}·(-2) = -54`. -/
example : Sz ([1, 2] ++ [3]) - Sz ([2, 1] ++ [3]) = 3 ^ 1 * (Sz [1, 2] - Sz [2, 1]) ∧
    Sz ([1, 2] ++ [3]) - Sz ([2, 1] ++ [3]) ≠ 3 ^ 3 * (Sz [1, 2] - Sz [2, 1]) := by
  norm_num [S]

/-- Both balance hypotheses of `S_frame_sub` are needed: equal letter-sum alone fails
(`P = (1)`, `M = (1,1)`, `M' = (2)`), and equal length alone fails (`M = (1)`, `M' = (2)`,
`Q = (1)`). -/
example : Sz ([1] ++ [1, 1] ++ []) - Sz ([1] ++ [2] ++ []) ≠
      2 ^ ([1] : Word).sum * 3 ^ ([] : Word).length * (Sz [1, 1] - Sz [2]) ∧
    Sz ([] ++ [1] ++ [1]) - Sz ([] ++ [2] ++ [1]) ≠
      2 ^ ([] : Word).sum * 3 ^ ([1] : Word).length * (Sz [1] - Sz [2]) := by
  norm_num [S]

/-- The **difference ideal** `J = ⟨S^{(i)} - S^{(j)}⟩` of the rotations of `w` at `(2,3)`. -/
def diffIdeal (w : Word) : Ideal ℤ :=
  Ideal.span {x | ∃ i j, x = Sz (w.rotate i) - Sz (w.rotate j)}

/-- **Anchored basis** (§4): the differences to a *single* anchor `a` generate all differences,
since `w_i - w_j = (w_i - w_a) - (w_j - w_a)`. (With several groups each anchored separately, the
anchor-to-anchor differences must be added: grouped anchoring alone has rank `o - #groups`.) -/
theorem diffIdeal_eq_anchored (w : Word) (a : ℕ) :
    diffIdeal w = Ideal.span (Set.range fun j => Sz (w.rotate j) - Sz (w.rotate a)) := by
  apply le_antisymm
  · refine Ideal.span_le.2 ?_
    rintro _ ⟨i, j, rfl⟩
    rw [show Sz (w.rotate i) - Sz (w.rotate j) =
      (Sz (w.rotate i) - Sz (w.rotate a)) - (Sz (w.rotate j) - Sz (w.rotate a)) by ring]
    exact Ideal.sub_mem _ (Ideal.subset_span ⟨i, rfl⟩) (Ideal.subset_span ⟨j, rfl⟩)
  · refine Ideal.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    exact Ideal.subset_span ⟨j, a, rfl⟩

/-! ## Inner-core extraction [P1] -/

section InnerCore

variable {R : Type*} [CommRing R] (X Y : R)

/-- **Inner-core extraction [P1], homogenised `ℤ[X,Y]` form.** A fixed inner block `u` drops out of
the `χ`-reweighted difference: the `S(u)` terms cancel, leaving an outer boundary term in `x, x'`
and a unit-scaled difference in `y, y'`. -/
theorem inner_core (x x' u y y' : Word) :
    Y ^ y'.length * X ^ x'.sum * S X Y (x ++ u ++ y) - Y ^ y.length * X ^ x.sum * S X Y (x' ++ u ++ y') =
      Y ^ (u.length + y.length + y'.length) * (X ^ x'.sum * S X Y x - X ^ x.sum * S X Y x')
      + X ^ (x.sum + x'.sum + u.sum) * (Y ^ y'.length * S X Y y - Y ^ y.length * S X Y y') := by
  simp only [S_append, List.sum_append, pow_add]
  ring

end InnerCore

section Field

variable {K : Type*} [Field K] (X Y : K)

/-- The character `χ(w) = X^{|w|} / Y^{len w}`. -/
def chi (w : Word) : K := X ^ w.sum / Y ^ w.length

/-- The non-homogenised cocycle of the incubator notes, `S(w)/Y^{len w - 1}` (so `S(n) = 1` for a
single letter and `S([]) = 0`). -/
def Sc (w : Word) : K := Y * S X Y w / Y ^ w.length

/-- `χ` is multiplicative. -/
lemma chi_append (u v : Word) : chi X Y (u ++ v) = chi X Y u * chi X Y v := by
  simp only [chi, List.sum_append, List.length_append, pow_add]
  ring

/-- The cocycle rule of the incubator notes, `S(uv) = S(u) + χ(u) S(v)`. -/
lemma Sc_append (hY : Y ≠ 0) (u v : Word) : Sc X Y (u ++ v) = Sc X Y u + chi X Y u * Sc X Y v := by
  simp only [Sc, chi, S_append, List.length_append, pow_add]
  field_simp

/-- **Inner-core extraction [P1], `χ`-form** (`inner-core-extraction.md`, boxed identity):
`χ(x')S(xuy) - χ(x)S(x'uy') = [χ(x')S(x) - χ(x)S(x')] + χ(x)χ(x')χ(u)[S(y) - S(y')]`. -/
theorem inner_core_chi (hY : Y ≠ 0) (x x' u y y' : Word) :
    chi X Y x' * Sc X Y (x ++ u ++ y) - chi X Y x * Sc X Y (x' ++ u ++ y') =
      (chi X Y x' * Sc X Y x - chi X Y x * Sc X Y x')
      + chi X Y x * chi X Y x' * chi X Y u * (Sc X Y y - Sc X Y y') := by
  simp only [Sc_append X Y hY, chi_append]
  ring

/-- **[P1] structural unit family** (`inner-core-extraction.md`): if `S(y) = S(y')` and the blocks are
`χ`-balanced (`χ(x)χ(y) = χ(x')χ(y')`), the P1 combination is the unit `χ(x)/χ(y')` times
`S(yx) - S(y'x')`: `χ(y')·[χ(x')S(xuy) - χ(x)S(x'uy')] = χ(x)·[S(yx) - S(y'x')]`. -/
theorem inner_core_unit_case (hY : Y ≠ 0) (x x' u y y' : Word) (hS : Sc X Y y = Sc X Y y')
    (hbal : chi X Y x * chi X Y y = chi X Y x' * chi X Y y') :
    chi X Y y' * (chi X Y x' * Sc X Y (x ++ u ++ y) - chi X Y x * Sc X Y (x' ++ u ++ y')) =
      chi X Y x * (Sc X Y (y ++ x) - Sc X Y (y' ++ x')) := by
  rw [inner_core_chi X Y hY, Sc_append X Y hY, Sc_append X Y hY, hS]
  linear_combination (-Sc X Y x) * hbal

/-- `χ(w) ≠ 0` when `X, Y ≠ 0`. -/
lemma chi_ne_zero (hX : X ≠ 0) (hY : Y ≠ 0) (w : Word) : chi X Y w ≠ 0 := by
  unfold chi; exact div_ne_zero (pow_ne_zero _ hX) (pow_ne_zero _ hY)

/-- The suffix-weighted ("reversed") sum `Ŝ(w) = S(w)/χ(w)` (`inner-core-extraction.md`, Gen 5). -/
def Shat (w : Word) : K := Sc X Y w / chi X Y w

/-- The suffix cocycle `Ŝ(ab) = Ŝ(b) + Ŝ(a)/χ(b)`. -/
lemma Shat_append (hX : X ≠ 0) (hY : Y ≠ 0) (a b : Word) :
    Shat X Y (a ++ b) = Shat X Y b + Shat X Y a / chi X Y b := by
  have ha := chi_ne_zero X Y hX hY a
  have hb := chi_ne_zero X Y hX hY b
  simp only [Shat, Sc_append X Y hY, chi_append]
  field_simp
  ring

/-- **[P1] normalised, closed form B** (Gen 5): dividing by `χ(x)χ(x')`, P1 is a suffix extraction
plus a prefix-shared core, `[Ŝ(x) - Ŝ(x')] + [S(uy) - S(uy')]`. -/
theorem inner_core_hat (hX : X ≠ 0) (hY : Y ≠ 0) (x x' u y y' : Word) :
    (chi X Y x' * Sc X Y (x ++ u ++ y) - chi X Y x * Sc X Y (x' ++ u ++ y')) /
        (chi X Y x * chi X Y x') =
      (Shat X Y x - Shat X Y x') + (Sc X Y (u ++ y) - Sc X Y (u ++ y')) := by
  have hx := chi_ne_zero X Y hX hY x
  have hx' := chi_ne_zero X Y hX hY x'
  rw [inner_core_chi X Y hY, Sc_append X Y hY u y, Sc_append X Y hY u y']
  simp only [Shat]
  field_simp
  ring

/-- **[P1] normalised, closed form A** (Gen 5): dividing by `χ(x)χ(x')χ(u)`,
`[Ŝ(xu) - Ŝ(x'u)] + [S(y) - S(y')]`. -/
theorem inner_core_hat' (hX : X ≠ 0) (hY : Y ≠ 0) (x x' u y y' : Word) :
    (chi X Y x' * Sc X Y (x ++ u ++ y) - chi X Y x * Sc X Y (x' ++ u ++ y')) /
        (chi X Y x * chi X Y x' * chi X Y u) =
      (Shat X Y (x ++ u) - Shat X Y (x' ++ u)) + (Sc X Y y - Sc X Y y') := by
  have hx := chi_ne_zero X Y hX hY x
  have hx' := chi_ne_zero X Y hX hY x'
  have hu := chi_ne_zero X Y hX hY u
  rw [inner_core_chi X Y hY, Shat_append X Y hX hY x u, Shat_append X Y hX hY x' u]
  simp only [Shat]
  field_simp
  ring

end Field

/-! ## Block powers and the bounded-defect wedge -/

/-- The block power `u^k` (`k` concatenated copies of `u`). -/
def blockPow (u : Word) (k : ℕ) : Word := (List.replicate k u).flatten

/-- `u^0` is empty. -/
@[simp] lemma blockPow_zero (u : Word) : blockPow u 0 = [] := rfl

/-- `u^{k+1} = u u^k`. -/
lemma blockPow_succ (u : Word) (k : ℕ) : blockPow u (k + 1) = u ++ blockPow u k := by
  simp [blockPow, List.replicate_succ]

/-- `u^{m+n} = u^m u^n`. -/
lemma blockPow_add (u : Word) (m n : ℕ) : blockPow u (m + n) = blockPow u m ++ blockPow u n := by
  simp only [blockPow, List.replicate_add, List.flatten_append]

/-- `u^{k+1} = u^k u`. -/
lemma blockPow_succ' (u : Word) (k : ℕ) : blockPow u (k + 1) = blockPow u k ++ u := by
  rw [blockPow_add]; simp [blockPow]

/-- `|u^k| = k |u|`. -/
@[simp] lemma blockPow_sum (u : Word) (k : ℕ) : (blockPow u k).sum = k * u.sum := by
  induction k with
  | zero => simp
  | succ k ih => rw [blockPow_succ, List.sum_append, ih]; ring

/-- `len u^k = k len u`. -/
@[simp] lemma blockPow_length (u : Word) (k : ℕ) : (blockPow u k).length = k * u.length := by
  induction k with
  | zero => simp
  | succ k ih => rw [blockPow_succ, List.length_append, ih]; ring

/-- A single-letter block power is a run `d^k`. -/
@[simp] lemma blockPow_singleton (d k : ℕ) : blockPow [d] k = List.replicate k d :=
  List.flatten_replicate_singleton

section Ring

variable {R : Type*} [CommRing R] (X Y : R)

/-- **The rotation-pair wedge, periodic background** (`covering-reductions.md` F1; for `u = (d)`
this is the bounded-defect wedge). Sliding the arc `β` one period through the run `u^L`:
`S(u^k β u^{L-k}) - S(u^{k+1} β u^{L-k-1}) = X^{k|u|} Y^{(L-k-1) len u} (S(βu) - S(uβ))`. -/
theorem wedge_block (β u : Word) {k L : ℕ} (hk : k < L) :
    S X Y (blockPow u k ++ β ++ blockPow u (L - k)) -
        S X Y (blockPow u (k + 1) ++ β ++ blockPow u (L - k - 1)) =
      X ^ (k * u.sum) * Y ^ ((L - k - 1) * u.length) * (S X Y (β ++ u) - S X Y (u ++ β)) := by
  obtain ⟨m, hm⟩ : ∃ m, L - k = m + 1 := ⟨L - k - 1, by omega⟩
  rw [show L - k - 1 = m by omega, hm, blockPow_succ, blockPow_succ',
    show blockPow u k ++ β ++ (u ++ blockPow u m) = blockPow u k ++ (β ++ u) ++ blockPow u m by simp,
    show blockPow u k ++ u ++ β ++ blockPow u m = blockPow u k ++ (u ++ β) ++ blockPow u m by simp,
    S_frame_sub X Y _ _ (by simp [add_comm]) (by simp [add_comm])]
  simp

/-- **The bounded-defect wedge** (`bounded-defect-lever` RATIONALE, boxed identity):
`S(d^k β d^{L-k}) - S(d^{k+1} β d^{L-k-1}) = X^{kd} Y^{L-k-1} (S(βd) - S(dβ))` for `k < L`. -/
theorem wedge (β : Word) (d : ℕ) {k L : ℕ} (hk : k < L) :
    S X Y (List.replicate k d ++ β ++ List.replicate (L - k) d) -
        S X Y (List.replicate (k + 1) d ++ β ++ List.replicate (L - k - 1) d) =
      X ^ (k * d) * Y ^ (L - k - 1) * (S X Y (β ++ [d]) - S X Y (d :: β)) := by
  simpa using wedge_block X Y β [d] hk

/-- **Telescoped run-sliding** (`lit-homotopical-completion` pointer): summing the wedges over
`k < L`, `S(β u^L) - S(u^L β) = (Σ_{k<L} X^{k|u|} Y^{(L-k-1) len u}) (S(βu) - S(uβ))`. -/
theorem slide_block (β u : Word) (L : ℕ) :
    S X Y (β ++ blockPow u L) - S X Y (blockPow u L ++ β) =
      (∑ k ∈ Finset.range L, X ^ (k * u.sum) * Y ^ ((L - k - 1) * u.length)) *
        (S X Y (β ++ u) - S X Y (u ++ β)) := by
  have h := Finset.sum_range_sub' (fun k => S X Y (blockPow u k ++ β ++ blockPow u (L - k))) L
  simp only [blockPow_zero, List.nil_append, Nat.sub_zero, Nat.sub_self, List.append_nil] at h
  rw [← h, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [show L - (k + 1) = L - k - 1 by omega, wedge_block X Y β u hk]

/-- The run sum `S(d^L)` satisfies `S(d^L)(X^d - Y) = X^{Ld} - Y^L`, i.e. `S(d^L) = D(d^L)/(X^d - Y)`. -/
theorem S_replicate_mul (d L : ℕ) :
    S X Y (List.replicate L d) * (X ^ d - Y) = X ^ (L * d) - Y ^ L := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [List.replicate_succ, S_cons, List.length_replicate]
    linear_combination X ^ d * ih

/-- **Telescoped run-sliding, single letter**: `S(β d^L) - S(d^L β) = S(d^L) (S(βd) - S(dβ))`, the
completion coefficient being the run sum `S(d^L) = (X^{Ld} - Y^L)/(X^d - Y)`. -/
theorem slide (β : Word) (d L : ℕ) :
    S X Y (β ++ List.replicate L d) - S X Y (List.replicate L d ++ β) =
      S X Y (List.replicate L d) * (S X Y (β ++ [d]) - S X Y (d :: β)) := by
  have h := S_replicate_mul X Y d L
  rw [S_append, S_append, S_append, S_singleton, S_cons]
  simp only [List.length_replicate, List.sum_replicate, smul_eq_mul, List.length_singleton,
    pow_one, mul_one]
  linear_combination (S X Y β) * h

end Ring

/-- Both wedge terms are rotations of the cyclic word `β u^L`: `u^k β u^{L-k}` is a rotation of
`β u^L` for every `k ≤ L`. -/
theorem isRotated_blockPow (β u : Word) {k L : ℕ} (hk : k ≤ L) :
    (β ++ blockPow u L) ~r (blockPow u k ++ β ++ blockPow u (L - k)) := by
  refine ⟨(β ++ blockPow u (L - k)).length, ?_⟩
  rw [show blockPow u L = blockPow u (L - k) ++ blockPow u k by
    rw [← blockPow_add]; congr 1; omega, ← List.append_assoc, List.rotate_append_length_eq]
  simp

/-! ## The `o`-independent ceiling on a genuine cycle -/

/-- On a genuine cycle, every word cyclically equivalent to the gap word carries a closed orbit. -/
lemma cycle_follows {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) {W : Word} (hW : gapWord a o ~r W) :
    ∃ b, Follows (2 : ℤ) 3 W b b := by
  have hf := follows_gapWord a o
  rw [h.2.2] at hf
  obtain ⟨n, rfl⟩ := hW
  exact hf.rotate n

/-- The gap word of a genuine cycle has `E ≥ 1`. -/
lemma one_le_sum_gapWord {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) : 1 ≤ (gapWord a o).sum := by
  obtain ⟨o, rfl⟩ : ∃ o', o = o' + 1 := ⟨o - 1, by have := h.1; omega⟩
  simp only [gapWord, List.sum_cons]
  have := one_le_gap h.2.1
  omega

/-- On a genuine cycle `|2^E - 3^o|` is coprime to `6`. -/
lemma cycle_D_coprime {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) :
    Nat.Coprime (Dz (gapWord a o)).natAbs 6 :=
  Dz_coprime_six (one_le_sum_gapWord h) (by rw [gapWord_length]; exact h.1)

/-- On a genuine cycle, `|2^E - 3^o|` divides the `6`-free part of every rotation-pair wedge
`S^{(i)} - S^{(j)} = 2^p 3^q c` of any word `W` cyclically equal to the gap word. -/
lemma natAbs_D_dvd_sixFree_of_wedge {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) {W : Word}
    (hW : gapWord a o ~r W) {i j p q : ℕ} {c : ℤ}
    (hc : Sz (W.rotate i) - Sz (W.rotate j) = 2 ^ p * 3 ^ q * c) :
    (Dz (gapWord a o)).natAbs ∣ sixFree c := by
  obtain ⟨b, hb⟩ := cycle_follows h hW
  have hD : Dz W = Dz (gapWord a o) := by obtain ⟨n, rfl⟩ := hW; exact D_rotate _ _ _ _
  have hcop := cycle_D_coprime h
  rw [← hD] at hcop ⊢
  rw [← sixFree_pow_mul p q, ← hc]
  exact dvd_sixFree hcop (Int.natAbs_dvd.2
    (dvd_sub (Follows.D_dvd_S_rotate _ _ hb i) (Follows.D_dvd_S_rotate _ _ hb j)))

/-- **The bounded-defect ceiling, periodic background** (divisibility form). If the cyclic gap word
of a genuine cycle is (a rotation of) `β u^L` with `L ≥ 1`, then
`|2^E - 3^o| ∣ sixFree(S(βu) - S(uβ))`. -/
theorem ceiling_dvd_block {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) {β u : Word} {L : ℕ} (hL : 1 ≤ L)
    (hW : gapWord a o ~r (β ++ blockPow u L)) :
    (Dz (gapWord a o)).natAbs ∣ sixFree (Sz (β ++ u) - Sz (u ++ β)) := by
  obtain ⟨m, hm⟩ := isRotated_blockPow β u (k := 1) hL
  refine natAbs_D_dvd_sixFree_of_wedge h hW (i := 0) (j := m) (p := 0)
    (q := (L - 0 - 1) * u.length) ?_
  rw [List.rotate_zero, hm]
  have := wedge_block (2 : ℤ) 3 β u (k := 0) (L := L) (by omega)
  simpa using this

/-- **The `o`-independent ceiling, periodic background** (`covering-reductions.md` F1): on a genuine
cycle whose cyclic gap word is `β u^L` (`L ≥ 1`), `|2^E - 3^o| ≤ sixFree(S(βu) - S(uβ))` whenever
the core is nonzero. The bound does not depend on `L`, hence not on `o`. -/
theorem ceiling_block {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) {β u : Word} {L : ℕ} (hL : 1 ≤ L)
    (hW : gapWord a o ~r (β ++ blockPow u L)) (hc : Sz (β ++ u) - Sz (u ++ β) ≠ 0) :
    ((2 : ℤ) ^ (gapWord a o).sum - 3 ^ o).natAbs ≤ sixFree (Sz (β ++ u) - Sz (u ++ β)) := by
  have := Nat.le_of_dvd (sixFree_pos hc) (ceiling_dvd_block h hL hW)
  simpa [D] using this

/-- **The bounded-defect lever** (`bounded-defect-lever` RATIONALE, boxed): on a genuine cycle whose
cyclic gap word is `β d^L` (`L ≥ 1`), `|2^E - 3^o| ≤ sixFree(S(βd) - S(dβ))` whenever the core is
nonzero — an `o`-independent ceiling. -/
theorem ceiling {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) {β : Word} {d L : ℕ} (hL : 1 ≤ L)
    (hW : gapWord a o ~r (β ++ List.replicate L d)) (hc : Sz (β ++ [d]) - Sz (d :: β) ≠ 0) :
    ((2 : ℤ) ^ (gapWord a o).sum - 3 ^ o).natAbs ≤ sixFree (Sz (β ++ [d]) - Sz (d :: β)) := by
  have := ceiling_block h hL (u := [d]) (by simpa using hW) (by simpa using hc)
  simpa using this

/-- **The lever feeds the squeeze.** For any lower bound `B(o) ≤ |2^E - 3^o|` (e.g. Rhin /
Simons–de Weger, Ellison), a genuine cycle in the bounded-arc family forces
`B(o) ≤ sixFree(S(βd) - S(dβ))`. -/
theorem ceiling_squeeze {B : ℕ → ℝ} (hB : ∀ E o : ℕ, 0 < o → B o ≤ |(2 : ℝ) ^ E - 3 ^ o|)
    {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) {β : Word} {d L : ℕ} (hL : 1 ≤ L)
    (hW : gapWord a o ~r (β ++ List.replicate L d)) (hc : Sz (β ++ [d]) - Sz (d :: β) ≠ 0) :
    B o ≤ sixFree (Sz (β ++ [d]) - Sz (d :: β)) := by
  refine (hB (gapWord a o).sum o h.1).trans ?_
  have := ceiling h hL hW hc
  have h' : (((2 : ℤ) ^ (gapWord a o).sum - 3 ^ o).natAbs : ℝ) = |(2 : ℝ) ^ (gapWord a o).sum - 3 ^ o| := by
    rw [Nat.cast_natAbs]; push_cast; rfl
  rw [← h']
  exact_mod_cast this

/-- **Only finitely many cycle lengths in a bounded-arc family.** If the lower bound `B(o) → ∞`,
there is an `o₀` such that every genuine cycle whose cyclic gap word is `β d^L` (`L ≥ 1`, nonzero
core) has `o < o₀`. -/
theorem ceiling_finite {B : ℕ → ℝ} (hB : ∀ E o : ℕ, 0 < o → B o ≤ |(2 : ℝ) ^ E - 3 ^ o|)
    (hlim : Filter.Tendsto B Filter.atTop Filter.atTop) (β : Word) (d : ℕ)
    (hc : Sz (β ++ [d]) - Sz (d :: β) ≠ 0) :
    ∃ o₀, ∀ (a : ℤ) (o L : ℕ), IsSyrCycle a o → 1 ≤ L →
      gapWord a o ~r (β ++ List.replicate L d) → o < o₀ := by
  obtain ⟨o₀, ho₀⟩ := Filter.eventually_atTop.1
    (hlim.eventually_gt_atTop (sixFree (Sz (β ++ [d]) - Sz (d :: β)) : ℝ))
  refine ⟨o₀, fun a o L h hL hW => ?_⟩
  by_contra hlt
  exact absurd (ceiling_squeeze hB h hL hW hc) (not_le.2 (ho₀ o (not_lt.1 hlt)))

/-! ## The ceiling atlas -/

section Atlas

variable {R : Type*} [CommRing R] (X Y : R)

/-- **Single defect (`β = e`, structure.md P2).** The local core is `S(ed) - S(de) = X^e - X^d`. -/
theorem single_defect_core (e d : ℕ) : S X Y ([e] ++ [d]) - S X Y (d :: [e]) = X ^ e - X ^ d := by
  simp [S]

/-- **structure.md P2 recovered** (`β` a single letter `e ≥ d`): the adjacent-rotation wedge of
`d^{L-1} e d` and `d^L e` is the monomial-times-cyclotomic core
`S(d^{L-1} e d) - S(d^L e) = X^{Ld} (X^{e-d} - 1)` (with `o = L + 1`: `X^{(o-1)d}(X^{e-d} - 1)`). -/
theorem single_defect_wedge {e d L : ℕ} (hde : d ≤ e) (hL : 1 ≤ L) :
    S X Y (List.replicate (L - 1) d ++ [e] ++ [d]) - S X Y (List.replicate L d ++ [e]) =
      X ^ (L * d) * (X ^ (e - d) - 1) := by
  have h := wedge X Y [e] d (k := L - 1) (L := L) (by omega)
  rw [show L - (L - 1) = 1 by omega, show L - 1 + 1 = L by omega, single_defect_core] at h
  simp only [Nat.sub_self, List.replicate_one, List.replicate_zero, List.append_nil, pow_zero,
    mul_one] at h
  rw [h]
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hde
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hL
  simp only [add_tsub_cancel_left, pow_add, add_mul, one_mul]
  ring

end Atlas

/-- The single-defect ceiling: `sixFree(2^e - 2^d) = sixFree(2^{|e-d|} - 1)`. -/
theorem sixFree_two_pow_sub_two_pow (e d : ℕ) :
    sixFree ((2 : ℤ) ^ e - 2 ^ d) = sixFree (2 ^ ((e : ℤ) - d).natAbs - 1) := by
  rcases le_total d e with hde | hed
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hde
    have : ((d + n : ℕ) : ℤ) - d = n := by push_cast; ring
    rw [this, Int.natAbs_natCast,
      show (2 : ℤ) ^ (d + n) - 2 ^ d = 2 ^ d * 3 ^ 0 * (2 ^ n - 1) by ring, sixFree_pow_mul]
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hed
    have : (e : ℤ) - ((e + n : ℕ) : ℤ) = -n := by push_cast; ring
    rw [this, Int.natAbs_neg, Int.natAbs_natCast,
      show (2 : ℤ) ^ e - 2 ^ (e + n) = 2 ^ e * 3 ^ 0 * -(2 ^ n - 1) by ring, sixFree_pow_mul,
      sixFree_neg]

/-- The single-defect core is a product of cyclotomic values: `2^n - 1 = ∏_{k ∣ n} Φ_k(2)`. -/
theorem two_pow_sub_one_eq_prod_cyclotomic {n : ℕ} (hn : 0 < n) :
    (2 : ℤ) ^ n - 1 = ∏ k ∈ n.divisors, (Polynomial.cyclotomic k ℤ).eval 2 := by
  have := congrArg (Polynomial.eval (2 : ℤ)) (Polynomial.prod_cyclotomic_eq_X_pow_sub_one hn ℤ)
  simpa [Polynomial.eval_prod] using this.symm

/-- `3^f mod 8 ∈ {1, 3}`. -/
lemma three_pow_mod_eight (f : ℕ) : 3 ^ f % 8 = 1 ∨ 3 ^ f % 8 = 3 := by
  induction f with
  | zero => left; rfl
  | succ f ih => rw [pow_succ]; omega

/-- `3^f + 1` is never a power of two `≥ 8` (`3^f mod 8 ∈ {1, 3}`). -/
lemma three_pow_add_one_ne_two_pow (f : ℕ) {n : ℕ} (hn : 3 ≤ n) : 3 ^ f + 1 ≠ 2 ^ n := by
  intro h
  have h8 : 2 ^ n % 8 = 0 := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [pow_add]; exact Nat.mul_mod_right _ _
  have := three_pow_mod_eight f
  omega

/-- **The cyclotomic-collapse gate** (`ceiling_atlas.py`): for `n ≥ 1` the single-defect ceiling
`sixFree(2^n - 1)` equals `1` iff `n ∈ {1, 2}`. -/
theorem sixFree_two_pow_sub_one_eq_one_iff {n : ℕ} (hn : 1 ≤ n) :
    sixFree ((2 : ℤ) ^ n - 1) = 1 ↔ n = 1 ∨ n = 2 := by
  constructor
  · intro h
    by_contra hn'
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have hcast : ((2 : ℤ) ^ n - 1) = ((2 ^ n - 1 : ℕ) : ℤ) := by push_cast [h1]; ring
    have hev : 2 ^ n % 2 = 0 := by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
      rw [pow_add]; exact Nat.mul_mod_right _ _
    have hodd : ¬ 2 ∣ 2 ^ n - 1 := by omega
    rw [hcast, sixFree, Int.natAbs_natCast, Nat.factorization_eq_zero_of_not_dvd hodd, pow_zero,
      Nat.div_one] at h
    have h3 := Nat.ordProj_mul_ordCompl_eq_self (2 ^ n - 1) 3
    rw [h, mul_one] at h3
    exact three_pow_add_one_ne_two_pow ((2 ^ n - 1).factorization 3) (n := n) (by omega) (by omega)
  · rintro (rfl | rfl)
    · simp [sixFree]
    · rw [show ((2 : ℤ) ^ 2 - 1) = 2 ^ 0 * 3 ^ 1 * 1 by norm_num, sixFree_pow_mul]
      simp [sixFree]

/-- `S ≥ 0` at `(2, 3)`. -/
lemma Sz_nonneg (w : Word) : 0 ≤ Sz w := by
  induction w with
  | nil => simp
  | cons d w ih =>
    show 0 ≤ S (2 : ℤ) 3 (d :: w)
    rw [S_cons]
    exact add_nonneg (by positivity) (mul_nonneg (by positivity) ih)

/-- `S > 0` at `(2, 3)` for a nonempty word. -/
lemma Sz_pos {w : Word} (hw : w ≠ []) : 0 < Sz w := by
  cases w with
  | nil => exact absurd rfl hw
  | cons d w =>
    show 0 < S (2 : ℤ) 3 (d :: w)
    rw [S_cons]
    exact add_pos_of_pos_of_nonneg (by positivity) (mul_nonneg (by positivity) (Sz_nonneg w))

/-- On a positive cycle `D > 0`, i.e. `2^E > 3^o` (from `D a = S > 0`). -/
lemma Dz_pos_of_pos {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) (ha : 0 < a) : 0 < Dz (gapWord a o) := by
  have hS : 0 < Sz (gapWord a o) := Sz_pos (by
    intro h0; have := congrArg List.length h0; simp at this; exact absurd this h.1.ne')
  have := h.cycle_equation
  by_contra hD
  nlinarith

/-- **Single defect on a cycle.** If the cyclic gap word of a genuine cycle is `e d^L` (`L ≥ 1`,
`e ≠ d`), then `|2^E - 3^o| ≤ sixFree(2^{|e-d|} - 1)`. -/
theorem single_defect_ceiling {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) {e d L : ℕ} (hL : 1 ≤ L)
    (hW : gapWord a o ~r ([e] ++ List.replicate L d)) (hed : e ≠ d) :
    ((2 : ℤ) ^ (gapWord a o).sum - 3 ^ o).natAbs ≤ sixFree (2 ^ ((e : ℤ) - d).natAbs - 1) := by
  have hcore := single_defect_core (2 : ℤ) 3 e d
  have hne : (2 : ℤ) ^ e - 2 ^ d ≠ 0 := fun h0 =>
    hed (Nat.pow_right_injective le_rfl (by exact_mod_cast sub_eq_zero.1 h0))
  rw [← sixFree_two_pow_sub_two_pow, ← hcore]
  exact ceiling h hL hW (hcore ▸ hne)

/-- **Strongest exclusion: `|e - d| ∈ {1, 2}` collapses the ceiling to `1`.** On a genuine cycle
with cyclic gap word `e d^L` (`L ≥ 1`) and `|e - d| ∈ {1, 2}`, `|2^E - 3^o| = 1`. -/
theorem single_defect_collapse {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) {e d L : ℕ} (hL : 1 ≤ L)
    (hW : gapWord a o ~r ([e] ++ List.replicate L d))
    (hed : ((e : ℤ) - d).natAbs = 1 ∨ ((e : ℤ) - d).natAbs = 2) :
    ((2 : ℤ) ^ (gapWord a o).sum - 3 ^ o).natAbs = 1 := by
  have hne : e ≠ d := by rintro rfl; simp at hed
  have h1 := single_defect_ceiling h hL hW hne
  rw [(sixFree_two_pow_sub_one_eq_one_iff (by omega)).2 hed] at h1
  have h0 : Dz (gapWord a o) ≠ 0 :=
    Dz_ne_zero (one_le_sum_gapWord h) (by rw [gapWord_length]; exact h.1)
  have : ((2 : ℤ) ^ (gapWord a o).sum - 3 ^ o).natAbs ≠ 0 := by
    simpa [D] using h0
  omega

/-- **No positive cycle in the collapsed single-defect family.** No positive Syracuse cycle has a
cyclic gap word `e d^L` with `L ≥ 1` and `|e - d| ∈ {1, 2}` (the collapse forces `2^E = 3^o + 1`
with `o ≥ 2`, impossible mod `8`). -/
theorem no_positive_cycle_single_defect {a : ℤ} {o : ℕ} (ha : 0 < a) (h : IsSyrCycle a o)
    {e d L : ℕ} (hL : 1 ≤ L) (hW : gapWord a o ~r ([e] ++ List.replicate L d))
    (hed : ((e : ℤ) - d).natAbs = 1 ∨ ((e : ℤ) - d).natAbs = 2) : False := by
  have h1 := single_defect_collapse h hL hW hed
  have hpos := Dz_pos_of_pos h ha
  simp only [D, gapWord_length] at hpos
  have hD : (2 : ℤ) ^ (gapWord a o).sum = 3 ^ o + 1 := by omega
  have ho : 2 ≤ o := by
    have := hW.perm.length_eq
    simp only [gapWord_length, List.length_append, List.length_singleton,
      List.length_replicate] at this
    omega
  have hN : 2 ^ (gapWord a o).sum = 3 ^ o + 1 := by exact_mod_cast hD
  have h9 : 9 ≤ 3 ^ o := by
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ o := Nat.pow_le_pow_right (by norm_num) ho
  have hE : 3 ≤ (gapWord a o).sum := by
    by_contra hlt
    have : 2 ^ (gapWord a o).sum ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact three_pow_add_one_ne_two_pow o hE hN.symm

/-- `sixFree c = |c|` when `c` is prime to `6`. -/
lemma sixFree_eq_natAbs {c : ℤ} (h2 : ¬ 2 ∣ c.natAbs) (h3 : ¬ 3 ∣ c.natAbs) :
    sixFree c = c.natAbs := by
  simp only [sixFree, Nat.factorization_eq_zero_of_not_dvd h2, pow_zero, Nat.div_one,
    Nat.factorization_eq_zero_of_not_dvd h3]

/-- **Atlas: the smallest genuine two-defect ceiling.** `β = (2,3)`, `d = 1` gives ceiling `5`. -/
theorem ceiling_atlas_23_1 : sixFree (Sz ([2, 3] ++ [1]) - Sz (1 :: [2, 3])) = 5 := by
  rw [show Sz ([2, 3] ++ [1]) - Sz (1 :: [2, 3]) = 2 ^ 1 * 3 ^ 1 * 5 by norm_num [S],
    sixFree_pow_mul, sixFree_eq_natAbs] <;> norm_num

/-- **Atlas (`defect_compose.py` PART B), `d = 1`:** `β = (3,4)` gives ceiling `65`. -/
theorem ceiling_atlas_34_1 : sixFree (Sz ([3, 4] ++ [1]) - Sz (1 :: [3, 4])) = 65 := by
  rw [show Sz ([3, 4] ++ [1]) - Sz (1 :: [3, 4]) = 2 ^ 1 * 3 ^ 0 * 65 by norm_num [S],
    sixFree_pow_mul, sixFree_eq_natAbs] <;> norm_num

/-- **Atlas, `d = 1`:** `β = (4,3,4)` gives ceiling `1103`. -/
theorem ceiling_atlas_434_1 : sixFree (Sz ([4, 3, 4] ++ [1]) - Sz (1 :: [4, 3, 4])) = 1103 := by
  rw [show Sz ([4, 3, 4] ++ [1]) - Sz (1 :: [4, 3, 4]) = 2 ^ 1 * 3 ^ 0 * 1103 by norm_num [S],
    sixFree_pow_mul, sixFree_eq_natAbs] <;> norm_num

/-- **Atlas, `d = 1`:** `β = (4,1,1,3)` gives ceiling `127`. -/
theorem ceiling_atlas_4113_1 :
    sixFree (Sz ([4, 1, 1, 3] ++ [1]) - Sz (1 :: [4, 1, 1, 3])) = 127 := by
  rw [show Sz ([4, 1, 1, 3] ++ [1]) - Sz (1 :: [4, 1, 1, 3]) = 2 ^ 1 * 3 ^ 1 * 127 by norm_num [S],
    sixFree_pow_mul, sixFree_eq_natAbs] <;> norm_num

/-- **Reach: two defects separated by one growing run.** `d e₁ d^B e₂ d` is cyclically
`β d^B` with `β = e₂ d d e₁` (the short-gap side). -/
theorem isRotated_two_defect (d e₁ e₂ B : ℕ) :
    ([d, e₁] ++ List.replicate B d ++ [e₂, d]) ~r ([e₂, d, d, e₁] ++ List.replicate B d) :=
  ⟨([d, e₁] ++ List.replicate B d).length, by rw [List.rotate_append_length_eq]; simp⟩

/-- **Reach corollary.** A genuine cycle with cyclic gap word `d e₁ d^B e₂ d` (`B ≥ 1`) has the
`B`-independent ceiling `|2^E - 3^o| ≤ sixFree(S(e₂dde₁d) - S(de₂dde₁))` when the core is nonzero. -/
theorem ceiling_two_defect {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) {d e₁ e₂ B : ℕ} (hB : 1 ≤ B)
    (hW : gapWord a o ~r ([d, e₁] ++ List.replicate B d ++ [e₂, d]))
    (hc : Sz ([e₂, d, d, e₁] ++ [d]) - Sz (d :: [e₂, d, d, e₁]) ≠ 0) :
    ((2 : ℤ) ^ (gapWord a o).sum - 3 ^ o).natAbs ≤
      sixFree (Sz ([e₂, d, d, e₁] ++ [d]) - Sz (d :: [e₂, d, d, e₁])) :=
  ceiling h hB (hW.trans (isRotated_two_defect d e₁ e₂ B)) hc

/-! ## Multi-anchor shared-frame extraction (`covering-reductions.md`, core primitive) -/

section MultiAnchor

variable {R : Type*} [CommRing R] (X Y : R)

/-- **Multi-anchor extraction** (`covering-reductions.md`, boxed). Cut `W = b₁⋯b_m` and
`W' = b₁'⋯b_m'` into blocks with `χ(b_i) = χ(b_i')` (equal sum and length) for every `i`; then
`S(W) - S(W') = Σ_i X^{Pre_i} Y^{Suf_i} (S(b_i) - S(b_i'))` with `Pre_i = Σ_{j<i} |b_j|` and
`Suf_i = Σ_{j>i} len b_j`. Anchors (`b_i = b_i'`) contribute nothing. -/
theorem multi_anchor (ps : List (Word × Word))
    (h : ∀ p ∈ ps, p.1.sum = p.2.sum ∧ p.1.length = p.2.length) :
    S X Y (ps.map Prod.fst).flatten - S X Y (ps.map Prod.snd).flatten =
      ∑ i : Fin ps.length, X ^ ((ps.take i).map Prod.fst).flatten.sum *
        Y ^ ((ps.drop (i + 1)).map Prod.fst).flatten.length * (S X Y ps[i].1 - S X Y ps[i].2) := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    have hp := h p List.mem_cons_self
    have hrest : ∀ q ∈ ps, q.1.sum = q.2.sum ∧ q.1.length = q.2.length :=
      fun q hq => h q (List.mem_cons_of_mem _ hq)
    have hlen : (ps.map Prod.snd).flatten.length = (ps.map Prod.fst).flatten.length := by
      simp only [List.length_flatten, List.map_map]
      congr 1
      exact List.map_congr_left fun q hq => (hrest q hq).2.symm
    show _ = ∑ i : Fin (ps.length + 1), _
    rw [Fin.sum_univ_succ]
    have ih' := ih hrest
    simp only [Fin.getElem_fin] at ih' ⊢
    simp only [List.map_cons, List.flatten_cons, S_append, hlen, hp.1, Fin.val_zero, List.take_zero,
      List.map_nil, List.flatten_nil, List.sum_nil, pow_zero, one_mul, List.drop_zero,
      List.getElem_cons_zero, Fin.val_succ, List.take_succ_cons, List.drop_succ_cons,
      List.getElem_cons_succ, List.sum_append, pow_add]
    calc _ = Y ^ (ps.map Prod.fst).flatten.length * (S X Y p.1 - S X Y p.2) + X ^ p.2.sum *
          (S X Y (ps.map Prod.fst).flatten - S X Y (ps.map Prod.snd).flatten) := by ring
      _ = _ := by
        rw [ih', Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun x _ => by ring

end MultiAnchor

/-! ## The open `≥ 2` growing-run no-go (stated, not proved) -/

/-- The polynomial ring `ℤ[X,Y]` (variables `X = X 0`, `Y = X 1`). -/
abbrev Poly := MvPolynomial (Fin 2) ℤ

/-- The symmetric two-growing-run family `W_a = d^a e₁ d^a e₂ d^a` (`multigap_nogo.py`). -/
def twoRunWord (d e₁ e₂ a : ℕ) : Word :=
  List.replicate a d ++ [e₁] ++ List.replicate a d ++ [e₂] ++ List.replicate a d

/-- A unit (signed-monomial) combination `Σ ±X^i Y^j S(w.rotate r)` of rotation sums of `w` in
`ℤ[X,Y]`, encoded by a list of `(r, sign, i, j)`. -/
noncomputable def unitCombo (w : Word) (t : List (ℕ × Bool × ℕ × ℕ)) : Poly :=
  (t.map fun q => (if q.2.1 then 1 else -1) * MvPolynomial.X 0 ^ q.2.2.1 *
    MvPolynomial.X 1 ^ q.2.2.2 * S (MvPolynomial.X 0) (MvPolynomial.X 1) (w.rotate q.1)).sum

/-- A **uniform scheme** for a word family `W` (`bounded-defect-lever.md`, Gen 4): one fixed
nonzero reduced polynomial `f` such that, for every large `a`, some unit combination of the rotation
sums of `W a` equals a monomial times `f`. At `(2,3)` its `6`-free part is then `a`-independent. -/
def UniformScheme (W : ℕ → Word) : Prop :=
  ∃ f : Poly, f ≠ 0 ∧ ∃ a₀, ∀ a ≥ a₀, ∃ t i j,
    unitCombo (W a) t = MvPolynomial.X 0 ^ i * MvPolynomial.X 1 ^ j * f

/-- **The `≥ 2`-growing-run no-go — OPEN, stated only** (`bounded-defect-lever` STATUS, Gen 4
reduction): for genuine defects `e₁, e₂ ≠ d`, the two-growing-run family `d^a e₁ d^a e₂ d^a` has
no uniform scheme. The notes reduce it to a cyclotomic-collapse / Lehmer-type question; finite
searches cannot settle it (low-`a` coincidences exist). -/
def TwoRunNoGo : Prop :=
  ∀ d e₁ e₂ : ℕ, e₁ ≠ d → e₂ ≠ d → ¬ UniformScheme (twoRunWord d e₁ e₂)

/-- **Positive control: the one-run family has a uniform scheme.** For `β d^L` the lever wedge is a
unit combination equal to `Y^{L-1} (S(βd) - S(dβ))`, so `UniformScheme` holds with the fixed core
`f = S(βd) - S(dβ)` (when nonzero). This is the sense in which `TwoRunNoGo` is the exact boundary of
the lever. -/
theorem oneRun_uniformScheme (β : Word) (d : ℕ)
    (hf : S (MvPolynomial.X 0 : Poly) (MvPolynomial.X 1) (β ++ [d]) -
      S (MvPolynomial.X 0) (MvPolynomial.X 1) (d :: β) ≠ 0) :
    UniformScheme (fun L => β ++ List.replicate L d) := by
  refine ⟨_, hf, 1, fun L hL => ?_⟩
  obtain ⟨m, hm⟩ := isRotated_blockPow β [d] (k := 1) hL
  simp only [blockPow_singleton] at hm
  refine ⟨[(0, true, 0, 0), (m, false, 0, 0)], 0, L - 1, ?_⟩
  have hw := wedge (MvPolynomial.X 0 : Poly) (MvPolynomial.X 1) β d (k := 0) (L := L) (by omega)
  simp only [List.replicate_zero, List.nil_append, Nat.sub_zero, zero_add, zero_mul, pow_zero,
    one_mul] at hw
  simp only [unitCombo, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.rotate_zero,
    hm, Bool.false_eq_true, ↓reduceIte, pow_zero, mul_one, one_mul, add_zero]
  rw [← hw]
  ring

end Syracuse.BoundedDefectLever
