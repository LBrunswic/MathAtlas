# Theme `words`: combinatorics on words and pigeonhole principles for cocycle simplification

*Literature agent, theme `words`. 67 sources, 46 verified (44 non-dup + 2 dup re-reads). Bibliography lines:
`bib-words.jsonl`. Sections marked **[derived]** are short deductions made here from the program's own
identities (PROGRAM.md §4, covering-reductions.md). They are not literature claims, and each lists a
cheap check.*

---

## Executive summary

**Verdict on the covering hypothesis: false as a statement about words.** What survives is the Layer-2
gcd problem.

1. **Single moves.** A bounded 6-free core needs two rotations w_i and w_{i+s} that agree letter by
   letter outside one bounded window (§0, D1). That is global near-periodicity, not a local pattern.
   - A window of size b forces gcd(s,o) < b, and only O(o²·|A|^{2b}) words satisfy it.
   - For b = 2 these are exactly the Christoffel classes (Pirillo 2000), whose core is a monomial.
   - C-balanced words with C ≥ 2 number at least 2^{n/2} (Lipatov 1982; Heinis 2001).
   - So no finite menu of single moves covers an exponential family.
2. **Local χ-matched patterns are forced but useless.** Over {1,2}, every 4 letters contain a square.
   Over {1,2,3,4}, every 51 letters contain an additive square (Freedman–Brown 2016). But the swap
   uu′ → u′u is not a difference of rotations.
3. **Additive squares** over finite subsets of ℤ: open. They are avoidable over ℤ² (Rao–Rosenfeld
   2018). **Additive cubes** are avoidable over {0,1,3,4} and over every other 4-set except {0,1,2,3},
   which is open (Lietard–Rosenfeld 2020).
4. **Zimin, Shirshov, Ramsey:** tower or iterated-log length control, no χ-matching.

**Strongest hooks.**
- **H1. Pirillo 2000.** wab and wba are conjugate iff w is central: this characterises single-swap
  rotation pairs.
- **H2. Cyclic near-squares u′u [derived].** The core (Y^m − X^F)(S(u′) − S(u)) shares a cyclotomic
  factor with D. A bounded defect forces (2^F + 3^m) | (S(α′) − S(α)): excluded at any slope.
- **H3. Fici et al. 2016; Peltomäki 2020.** Anchor spacings in balanced words are (semi)convergent
  denominators of the slope.
- **H4. Abelian complexity ⇔ C-balance** (Richomme–Saari–Zamboni 2011). This caps the monomials per
  level in the rotation ideal.
- **H5.** The AM–GM estimator G_* is a 2-binomial invariant (Rao–Rigo–Salimov 2015).

---

## 0. Translation layer [derived]: what a "move" asks of a word

Notation: w is cyclic, of length o, over the gap alphabet A ⊂ ℕ. σ_k(i) is the gap-sum of the length-k
factor starting at position i. w_i is the rotation starting at i.

**D1. The δ-walk form of a rotation difference.**
Since S(w_i) = Σ_{k=0}^{o−1} X^{σ_k(i)} Y^{o−1−k},

  S(w_i) − S(w_j) = Σ_{k=1}^{o−1} Y^{o−1−k} (X^{σ_k(i)} − X^{σ_k(j)}).

Put δ_k = σ_k(i) − σ_k(j).
- The anchor split cuts at the zeros of δ, and the frame strip removes zero runs at the two ends.
- Because δ_{k+1} − δ_k = w(i+k) − w(j+k), a core of the form unit × (polynomial of bounded size)
  arises iff {k : δ_k ≠ 0} lies in one window of b positions.
- Equivalently, **w_i and w_j agree letter by letter outside one window of ≤ b letters.**
- Two or more separated windows give a sum of two or more unit-weighted terms. That is the F3/P4
  situation of covering-reductions.md, decided by gcds of S-unit expressions (F1, open problem 3),
  not by word combinatorics.
- *Check:* the identity is a one-line ℤ[X,Y] verification in `word_simplifier.py`.

**D2. Single-window pairs force bounded gcd(s,o).**
Let s = j − i and g = gcd(s,o).
- w(x) = w(x+s) holds except for x in a window W of b consecutive positions.
- The orbits of x ↦ x+s are the g cosets of gℤ/oℤ. Along a cyclic orbit the letter changes an even
  number of times (0 or ≥ 2), and only at points of W.
- A coset meets W in at least 2 points only if g < b. So if g ≥ b, w is exactly g-periodic. It is then
  either non-primitive or s ≡ 0: no move.
- Hence **g < b**. Each of the g tracks, read in steps of s, is a coding of a rotation with at most b
  changes.
- **Count:** at most O(o²·|A|^{2b}) words of length o: polynomial in o.
- Case b = 2, A = {1,2}: the two rotations are xab and xba, the Christoffel classes (Pirillo 2000 [H1]).
  The core is X^{|x|}(X^a − X^b), whose value at (2,3) is ±2^{|x|+1}. So sixfree = 1, hence G = 1:
  no nontrivial cycle has a Christoffel gap word. This is consistent with the dup "Baker-free
  monomial core" of Knight 2023 and Halbeisen–Hungerbühler 1997.

**D3. Counting verdict.**
- 1-balanced words of length n number about n³/π² (Mignosi 1991; Berstel–Pocchiola 1993).
- C-balanced words with C ≥ 2 are exponentially many: ≥ 2^{n/2} (Heinis 2001; Lipatov 1982).
- Critical words number about e^{1.04·o} (F5).
- Single-window moves therefore reach only a polynomial set. **The covering hypothesis in its
  single-move form is false for every exponential family.**

**D4. Two-window cores that still exclude: cyclic near-powers.**
Let the cyclic word be a cyclic additive square: w = u′u, with u, u′ of length m = o/2, both of gap-sum
F = E/2. The rotation by m gives

  S(u′u) − S(uu′) = (Y^m − X^F)(S(u′) − S(u)).

- On a cycle, G = |D| = |2^F − 3^m|·(2^F + 3^m) and G | C, so **(2^F + 3^m) | (S(u′) − S(u))**.
- If u and u′ differ only by a χ-matched rearrangement α → α′ inside a bounded window, the factor
  2^a3^b peels off, and (2^F + 3^m) | (S(α′) − S(α)). That is impossible for large o.
- The same argument works for near-p-th powers u^{p−1}u′, using gcd(a^p − b^p, a^{p−1} − b^{p−1}) = a − b.
- These families have arbitrary slope, so F2 does not already exclude them. They are exponentially
  thin, though: about 2^{o/2} words.
- So the additive-power notion that matters is the cyclic one (the whole word is a power), not the
  local one.
- *Cheapest test:* run `family_scan` on u′u with a bounded swap and confirm the divisibility.
- Round-2 lead: Peltomäki–Whiteland, *Avoiding abelian powers cyclically* (2020).

**D5. Normal form of any combination.**
For any integer combination C = Σ_j c_j S(w_j),

  C = Σ_k Y^{o−1−k} P_k(X), with P_k(X) = Σ_j c_j X^{σ_k(j)}.

- P_k has at most a_w(k) monomials, where a_w is the abelian complexity: the number of distinct sums of
  length-k factors. For C-balanced words, a_w(k) ≤ C + 1.
- For Christoffel words with Σ c_j = 0, P_k = A_k X^{m_k}(1 − X), where A_k is the c-weight of the
  "light" level set.
- So a small core needs most A_k to vanish. A_k vanishing is a discrepancy (bounded-remainder)
  condition on c, and it is the precise multi-move form of the covering question.

**D6. Cycle words are C-balanced with explicit C.**
From 2^{d_i}x_{i+1} = 3x_i(1 + 1/(3x_i)):

  σ_k(i) = k·log₂3 + log₂(x_i/x_{i+k}) + O(k/x_min).

So every cycle word is C-balanced with **C ≤ 2·log₂(x_max/x_min) + 1**. F2's "near-balanced" is
therefore exactly "small spread x_max/x_min". There is no a priori bound on C, so cycle words live in
the exponential C ≥ 2 regime of D3.

---

## 1. Idea → hook map

| # | idea | source(s) | touches | what it would give | verdict | cheapest first test |
|---|---|---|---|---|---|---|
| 1 | Zimin / unavoidable patterns as a covering menu | BEM 1979, Zimin 1984, Cooper–Rorabaugh 2014, Conlon–Fox–Sudakov 2019, Carayol–Göller 2019 | OP2, F5 | Patterns x₁x₂x₁… with arbitrary nonempty blocks; Z_n is forced only for n ≈ log* o (tower bounds, even on 2 letters); no length or χ control | **kill**: confirms F5 | none |
| 2 | Shirshov height: high power or n-divided | Shirshov 1957, Belov–Kharitonov 2012, Kharitonov 2014 | OP2 | Length > l(nd)^{C log(nd)} forces u^d with \|u\| < n, or n lexicographically decreasing blocks; nd ≈ exp(c√log o). u^d is a local run, not a whole background; n-division has no χ meaning | **kill** | none |
| 3 | Local additive squares (χ-matched adjacent swap) | Freedman–Brown 2016; CCSS 2014; Rao–Rosenfeld 2018; Pirillo–Varricchio 1994; Halbeisen–Hungerbühler 2000; Au–Robertson–Shallit 2011; Brown 2012 | F5, OP2 | Forced within 51 letters over {1..4} and within 4 letters over {1,2}. But xuu′y → xu′uy is not a rotation difference, so G need not divide it (D1, D2) | **kill** as covering; status recorded (§2) | none |
| 4 | χ-matched k-trains, k ≥ 3–5 | Dekking 1979; Rao 2015; Andrade–Mol 2024; Néraud 2017 | F5, OP2 | Over {1,2}, χ-matched 4-trains are avoidable, so any menu needing 4 aligned anchors fails on some infinite binary word; triples are unavoidable over {1,2}, but their long-period status is open (Néraud Q1.6.13.8) | **kill** | none |
| 5 | Single-swap rotation pairs = Christoffel | Pirillo 2000; Lothaire ch. 2; BLRS 2008 (dup); Halbeisen–Hungerbühler 1997 (dup) | OP2, F2 | Exact characterisation of b = 2; monomial core gives G = 1 (D2) | **keep** (consistent with known) | check the engine returns core ±2^{\|x\|+1} on Christoffel words |
| 6 | Counting kills single-move covering | Lipatov 1982; Heinis 2001; Berthé–Cecchi Bernales 2018; Mignosi 1991; Berstel–Pocchiola 1993; Bédaride et al. 2010 | OP2, F5 | O(o² \|A\|^{2b}) single-window words vs ≥ 2^{n/2} 2-balanced words vs e^{1.04o} critical words | **keep** (the verdict) | enumerate o ≤ 20: count words having a single-window rotation pair |
| 7 | Cyclic near-powers u′u, u^{p−1}u′ | **[derived]** D4; lead: Peltomäki–Whiteland 2020 | OP3, F1, F3 | New excludable family at arbitrary slope, using the cyclotomic split of D | **open** (verify) | `family_scan` on u′u; test (2^F + 3^m) \| (S(α′) − S(α)) |
| 8 | Abelian powers in Sturmian words; periods = convergent denominators | Fici et al. 2016; Richomme–Saari–Zamboni 2011; Peltomäki 2020 | F2, OP1 | Anchor geometry: in a balanced word the shift by q_k changes about 2o/q_{k+1} letters, and χ-trains have period q_k and exponent ⌊1/‖q_kα‖⌋. Gives explicit anchor counts for f(w) | **keep** | measure d_H(w, σ^{q_k}w) on random critical words vs 2o/q_{k+1} |
| 9 | Abelian complexity bounds monomials per level | Richomme–Saari–Zamboni 2011; Fici–Puzynina 2023 Prop. 3; Vuillon 2003 | OP1, OP4 | Normal form D5; for Christoffel words P_k = A_k X^{m_k}(1 − X) | **keep** | verify D5 on random combinations in the engine |
| 10 | G_* is a 2-binomial invariant | Rao–Rigo–Salimov 2015; Karhumäki–Saarela–Zamboni 2013 | OP4 | Σ_k e_k = const(n, #2) + #scattered "21". So G_* depends only on the Parikh matrix; classes are polynomially many | **open** | check G_* equality on 2-binomially equivalent words |
| 11 | C-balance ↔ x_max/x_min | **[derived]** D6; Vuillon 2003; Berthé–Tijdeman 2002 | F2 | Turns "near-balanced" into a number; shows the C ≥ 2 regime is unavoidable a priori | **keep** (elementary) | none |
| 12 | S-adic / desubstitution along the continued fraction of log₂3 | Arnoux–Rauzy 1991; Berthé–Delecroix 2014; Cassaigne–Ferenczi–Zamboni 2000 | OP1, F2 | Renormalise a balanced cycle word to a shorter word with a cocycle transform; CFZ warn that S-adic does not imply balanced in general | **open** | does S(w) transform under the Sturmian morphisms 1→1, 2→21? |
| 13 | Ramsey (vdW, Hales–Jewett, Brown's lemma, Furstenberg–Weiss) | Shelah 1988; Gowers 2001; Hales–Jewett 1963; Furstenberg–Weiss 1978; Brown 1971 | OP2 | AP length k with W(k,2) ≤ 2^{2^{2^{2^{2^{k+9}}}}}, i.e. k ≈ log₂ five times of o; no χ | **kill** | none |
| 14 | Periodicity tools | Fine–Wilf 1965; Crochemore–Perrin 1991 (CFT); Mignosi–Restivo–Salemi 1998; Duval 1983; Chen–Fox–Lyndon 1958 | OP2, tooling | Fine–Wilf underlies D2; the CFT says local periods cannot all be short; Duval gives a canonical anchor in O(o) | **keep** as tooling | none |
| 15 | Approximate periodicity (k-mismatch dichotomy) | Charalampopoulos–Kociumaka–Wellnitz 2020 (citing Bringmann et al. SODA'19) | OP2 | "Few small-Hamming rotations, or the word is approximately periodic": the multi-window analogue of D2 | **open** | none |
| 16 | Zero-sum (EGZ, Davenport, Olson) | EGZ 1961; Olson 1969; Gao–Geroldinger 2006; Gao–Geroldinger–Grynkiewicz 2008; Geroldinger–Grynkiewicz–Schmid 2010 | F5 | Subsequence sums carry no positional structure; the prefix-sum pigeonhole gives a factor with sum ≡ 0 mod m, invisible on the 6-free axis (F5) | **kill** | none |
| 17 | Littlewood–Offord counting | Tao 2011 (dup) | F5 | Heuristic finiteness only; Tao: "does not directly give any way to prevent" 0 in the sumset | **kill** for proofs | none |

---

## 2. Status of additive and abelian powers (as of the sources read)

Additive equivalence is invariant under affine maps of the alphabet (Lietard–Rosenfeld Lemma 2.1), so
{1,2,3,4} ≅ {0,1,2,3} and {1,2} ≅ {0,1}. Over two letters, additive = abelian = χ-equality.

| alphabet | additive squares | additive cubes | additive 4th powers |
|---|---|---|---|
| {1,2} (binary) | **unavoidable**: every 4 letters contain a square; abelian squares of length 2n are forced by length n² + 6n (EJS 1974, via survey) | **unavoidable** ("impossible to avoid abelian cubes over an alphabet of size 2", Fici–Puzynina) | **avoidable** (Dekking 1979); also additive 5-powers in rich binary words (Andrade–Mol 2024) |
| any 3 integers | **unavoidable** (abelian squares are unavoidable on 3 letters, Freedman–Brown) | **avoidable** for {0,i,j}, i < j coprime, 6 ≤ j ≤ 9 (Rao 2015; "minimal size … is 3"); {0,1,2}, {0,1,3}, {0,1,4}, {0,2,5} not characterised | avoidable (Dekking's binary word on any 2 of the letters) |
| {1,2,3,4} ≅ {0,1,2,3} | **unavoidable, g = 50**: every word of length 51 contains one (Freedman–Brown 2016) | **OPEN** (Lietard–Rosenfeld 2020; Néraud Q1.6.13.10) | avoidable (Dekking's binary word over {1,4}) |
| 4-sets with a+d = b+c, not an AP | unavoidable, g = 60 except listed cases (Freedman–Brown Thm 1) | avoidable (Lietard–Rosenfeld) | avoidable |
| other 4-sets / ≥ 5 letters | **open** (g(T) ≥ 50 for all 4-sets) | avoidable for every 4-set except ≅ {0,1,2,3}, and for every set of size ≥ 5 (Lietard–Rosenfeld) | avoidable |
| arbitrary finite ⊂ ℤ | **OPEN** since 1985/1994 (Brown–Freedman 1987; Pirillo–Varricchio 1994; Halbeisen–Hungerbühler 2000; Fici–Puzynina 2023: "remains open") | see above | ℕ is not uniformly 4-repetitive (Pirillo–Varricchio review) |
| finite ⊂ ℤ² | **avoidable** (Rao–Rosenfeld 2018) | — | — |

**Translation into the program.**
- An adjacent pair uu′ with χ(u) = χ(u′) gives an anchor (equal prefix sums) for comparing the word
  with its own swap xu′uy. It does *not* give anchors between two rotations. Only rotation differences
  lie in the ideal whose gcd is G (F1).
- Unavoidability of short additive squares (true over {1,..,4}) therefore gives nothing.
- Avoidability results (4th powers over {1,2}; cubes over most 4-sets) give *counterexample words*:
  for each, an infinite word in which no χ-matched k-train occurs at all. So any covering menu that
  needs k ≥ 4 aligned χ-matched blocks (k ≥ 3 for alphabets ⊇ {0,1,3,4}) fails on that word.
- The open additive-square question is **not on the critical path**. Its answer, either way, does not
  decide the covering hypothesis, because of D1 and D2.

---

## 3. Quantitative table: what each pigeonhole result guarantees as a function of o

| result | guaranteed pattern | size as a function of o | bounded window? |
|---|---|---|---|
| Zimin / BEM (Conlon–Fox–Sudakov; Carayol–Göller) | Z_n = Z_{n−1}x_nZ_{n−1} | n ≈ log* o (tower lower and upper bounds, even for 2 letters); f(3,q) = Θ(2^q q!) | no |
| Shirshov height (Belov–Kharitonov; Kharitonov) | u^d with \|u\| < n, or n-divided | nd ≈ exp(c·√(log o)) (from Ψ = l(nd)^{C log nd}) | no (local run only) |
| van der Waerden (Gowers; Shelah) | letters constant on an AP i, i+s, …, i+(k−1)s | k ≈ log₂ iterated five times of o (W(k,2) ≤ 2^{2^{2^{2^{2^{k+9}}}}}) | no |
| Entringer–Jackson–Schatz (via survey) | abelian square of length 2n over {1,2} | n ≈ √o | no (long blocks) |
| Brown 2012 | UV with \|U\| = \|V\|, \|ΣU − ΣV\| ≤ C(A) | arbitrarily long, no explicit length | no |
| Halbeisen–Hungerbühler 2000 | l adjacent equal-sum blocks (unequal lengths) | via vdW: l ≈ iterated log | no; lengths differ, so the Y-exponents mismatch |
| Freedman–Brown 2016 | additive square over {1,2,3,4} | within every 51 letters (bounded) | local only; not between rotations |
| Richomme–Saari–Zamboni; Fici et al. 2016 | abelian k-power at every position of a Sturmian word | period m, exponent ⌊1/‖mα‖⌋; for m = q_k, about q_{k+1}/q_k blocks | **yes, for 1-balanced words only**: shift by q_k differs in about 2o/q_{k+1} letters |
| Pirillo 2000 | rotations wab and wba | exactly when w is central | **yes, b = 2, Christoffel words only** |
| prefix-sum pigeonhole mod m | factor with gap-sum ≡ 0 mod m | within m+1 positions | not on the 6-free axis (F5) |
| EGZ / Davenport | zero-sum subsequence (not factor) | 2n−1 → n; D(C_n ⊕ C_n) = 2n−1 | no position control |

Only the Sturmian results (rows 8–9) deliver the "differ in a bounded window" property the program
needs, and only on the polynomially small 1-balanced set, which is already excluded.

---

## 4. Annotated bibliography

Format: **id**: citation · URL/DOI · key statement (verbatim) · note · verdict. "V" = verified
(source page fetched, quote from it); "U" = unverified (reason given). zbMATH reviews were fetched
through api.zbmath.org; their math is transliterated from LaTeX.

### 4.1 Additive powers (priority)

**cassaigne2014avoiding** (V): J. Cassaigne, J. D. Currie, L. Schaeffer, J. Shallit, *Avoiding three
consecutive blocks of the same size and same sum*, J. ACM 61(2) (2014) 10:1–17.
https://arxiv.org/abs/1106.5204 · doi:10.1145/2590775
> "We show that there exists an infinite word over the alphabet {0, 1, 3, 4} containing no three
> consecutive blocks of the same size and the same sum. This answers an open problem of Pirillo and
> Varricchio from 1994."

Over {1,2,4,5} (the affine image) there is an infinite gap word with no χ-matched triple. This is the
F5 fact. Note that {1,2,4,5} is not the cycle alphabet. **Kill** (as covering).

**freedman2016sequences** (V): A. R. Freedman, T. C. Brown, *Sequences on sets of four numbers*,
INTEGERS 16 (2016) #A33. https://ftp6.gwdg.de/pub/EMIS/journals/INTEGERS/papers/q33/q33.pdf
> "We show that the answer is "no" for all 4-element sets {a, b, c, d} where a < b < c < d are real
> numbers satisfying the Sidon equation a + d = b + c." … "g(0, 1, 2, 3) = 50 and g(0, 1, 5, 6) = 60."

Answers sub-question (b): additive squares are **unavoidable over {1,2,3,4}**, within every 51
letters. This is the strongest local forcing available. It still does not help, because the swap is not
a rotation difference (§2). The abstract dates the problem to 1985 (Brown–Freedman 1987). **Keep**
(status).

**rao2018avoiding** (V): M. Rao, M. Rosenfeld, *Avoiding two consecutive blocks of same size and same
sum over ℤ²*, SIAM J. Discrete Math. 32(4) (2018) 2381–2397. https://arxiv.org/abs/1511.05875 ·
doi:10.1137/17M1149377
> "A long standing question asks whether Z is uniformly 2-repetitive [Justin 1972, Pirillo and
> Varricchio, 1994], that is, whether there is an infinite sequence over a finite subset of Z avoiding
> two consecutive blocks of same size and same sum or not. … We show that Z² is not uniformly
> 2-repetitive."

This is the exact status of additive squares: open over ℤ, avoidable over ℤ². A pair-valued gap word
(e.g. (d_i, parity)) would therefore admit no covering by adjacent χ-matched pairs. **Open.**

**lietard2020additive** (V): F. Lietard, M. Rosenfeld, *Avoidability of additive cubes over alphabets of
four numbers*, DLT 2020, LNCS 12086, 192–206 (author PDF: *Additive cubes are avoidable over all but
one set of four numbers*). https://www.lirmm.fr/~mrosenfeld/LieRos.pdf
> "We show that for any set A ⊆ N of size 4 such that A cannot be obtained by applying the same affine
> function to all the elements of {0, 1, 2, 3}, there is an infinite sequence of elements of A that
> contains no 3 consecutive blocs of same size and same sum." … "We leave the case of {0, 1, 2, 3}
> open."

Additive cubes over **{1,2,3,4} are open**; over every other 4-set they are avoidable. Lemma 2.1 (affine
invariance) justifies identifying gap alphabets up to affine maps. **Open.**

**rao2015generalizations** (V, zbMATH review 1330.68242): M. Rao, *On some generalizations of abelian
power avoidability*, Theor. Comput. Sci. 601 (2015) 39–46. doi:10.1016/j.tcs.2015.07.026
> "Existence of infinite additive-cube-free words over a ternary alphabet is shown, thus decreasing the
> least known alphabet size by one."

Minimal alphabet for avoiding additive cubes = 3. Per Lietard–Rosenfeld, Rao's sets are
{0,i,j} with 6 ≤ j ≤ 9. **Kill.**

**pirillo1994uniformly** (V, zbMATH review 0805.20052): G. Pirillo, S. Varricchio, *On uniformly
repetitive semigroups*, Semigroup Forum 49(1) (1994) 125–129. doi:10.1007/BF02573477
> "It is proved that if N^+, (the non-negative integers under addition) is not uniformly k-repetitive
> then any finitely generated and uniformly k-repetitive semigroup is finite. (It is known that N^+ is
> not uniformly 4-repetitive.)"

This is the origin of the additive-square question in semigroup language. The program's χ is the
morphism A⁺ → ℕ×ℕ, (length, sum). **Open.**

**halbeisen2000application** (V): L. Halbeisen, N. Hungerbühler, *An application of Van der Waerden's
theorem in additive number theory*, INTEGERS 0 (2000) #A7.
https://ftp6.gwdg.de/pub/EMIS/journals/INTEGERS/papers/a7/a7.tex
> "The aim of this paper is to show that there is no infinite sequence on a finite set of integers such
> that no two adjacent segments have the same sum." … "Is it possible to construct an infinite sequence
> on a finite set of integers such that no two adjacent segments of the same length have the same sum?"

Equal-sum blocks of unequal length are unavoidable (via vdW), but useless: unequal lengths mean
mismatched Y-exponents, so no anchor. Not the 1997 Collatz paper (that one is a dup, §4.7). **Kill.**

**au2011vanderwaerden** (V): Y.-H. Au, A. Robertson, J. Shallit, *Van der Waerden's theorem and
avoidability in words*, INTEGERS 11 (2011) A7, 61–76. https://arxiv.org/abs/0812.2466 ·
doi:10.1515/INTEG.2011.007
> "Pirillo and Varricchio, and independently, Halbeisen and Hungerbuhler considered the following
> problem, open since 1994: Does there exist an infinite word w over a finite subset of Z such that w
> contains no two consecutive blocks of the same length and sum?"

Confirms the open status (the zbMATH summary says "open since 1992", crediting Freedman). **Open.**

**brown2012approximations** (V): T. C. Brown, *Approximations of additive squares in infinite words*,
INTEGERS 12 (2012) A22. https://arxiv.org/abs/1108.0739 · doi:10.1515/integers-2012-0006
> "We show that every infinite word ω on a finite subset of Z must contain arbitrarily large factors
> B1B2 which are "close" to being additive squares."

Long, nearly χ-matched adjacent blocks with |ΣB₁ − ΣB₂| ≤ C(A) are forced. Long blocks mean a
non-bounded core, so this fails the bounded-window need. **Kill.**

**andrade2024avoiding** (V): J. Andrade, L. Mol, *Avoiding abelian and additive powers in rich words*,
arXiv:2408.15390 (2024).
> "we construct an infinite additive 5-power-free rich word over {0,1} and an infinite additive
> 4-power-free rich word over {0, 1, 2}."

Even palindrome-rich binary words (structurally close to Sturmian) avoid χ-matched 5-trains. **Kill.**

**neraud2017ten** (V): J. Néraud, *Ten Conferences WORDS: Open Problems and Conjectures*,
arXiv:1705.04055 (2017).
> "Question 1.6.13.8: … (2) Can we avoid abelian-cubes of the form uvw, with |u| ≥ 2, over a binary
> alphabet?" … "Question 1.6.13.10: Are there infinite additive-cube-free words on the following
> alphabets: {0, 1, 2, 3}, {0, 1, 4} and {0, 2, 5}?"

Q1.6.13.8(2) is the binary question nearest to the program: are long χ-matched triples forced on
{1,2}? It was open in 2017. **Open.**

### 4.2 Abelian powers

**fici2023abelian** (V): G. Fici, S. Puzynina, *Abelian combinatorics on words: a survey*, Computer
Science Review 47 (2023) 100532. https://arxiv.org/abs/2207.09937 · doi:10.1016/j.cosrev.2022.100532
> "The minimal size of the alphabet to avoid additive cubes has recently been shown to be 3 by M. Rao.
> The question on whether it is possible to avoid additive squares remains open." … "Proposition 3.
> Let x be an infinite word. Then the abelian complexity of x is bounded if and only if x is C-balanced
> for some C > 0."

This is the hub. Proposition 3 is the bridge from F2 (near-balanced) to abelian complexity, which caps
the monomials per level (D5). **Keep.**

**dekking1979strongly** (U: publisher 403, zbMATH metadata only; quote from the survey): F. M. Dekking,
*Strongly non-repetitive sequences and progression-free sets*, J. Combin. Theory A 27 (1979) 181–185.
doi:10.1016/0097-3165(79)90044-X
> [survey, Thm 16] "There exists an infinite ternary word over with no abelian cube factor. … There
> exists an infinite binary word with no abelian 4-power factor."

Over {1,2}, χ-matched 4-trains are avoidable. **Kill.**

**keranen1992abelian** (U: Springer login; zbMATH review withheld): V. Keränen, *Abelian squares are
avoidable on 4 letters*, ICALP 1992, LNCS 623, 41–52. doi:10.1007/3-540-55719-9_62
> [survey] "proved by Keränen in 1992, who improved a previous bound of 5 given by Pleasants and the
> first bound of 25 given by Evdokimov"

Irrelevant on {1,2}; recorded for completeness. **Kill.**

**entringer1974nonrepetitive** (U: publisher 403): R. C. Entringer, D. E. Jackson, J. A. Schatz, *On
nonrepetitive sequences*, J. Combin. Theory A 16 (1974) 159–164. doi:10.1016/0097-3165(74)90041-7
> [survey] "every binary word of length n2 + 6n contains an abelian square of length 2n"

χ-matched adjacent blocks of length about √o are forced on {1,2}: polynomial forcing, but the blocks
are long. **Open** (as a source of long anchors).

**pleasants1970nonrepetitive** (U), **evdokimov1968strongly** (U), **erdos1961unsolved** (U):
history of the abelian-square question. Data come from the survey's reference list and from the
fetched Freedman–Brown introduction: "Evdomikov [8], using 25 symbols, in 1968. P. A. B. Pleasants
constructed an infinite word with no abelian square on 5 symbols in 1970." **Kill.**

**richomme2011abelian** (V): G. Richomme, K. Saari, L. Q. Zamboni, *Abelian complexity of minimal
subshifts*, J. London Math. Soc. 83 (2011) 79–95. https://arxiv.org/abs/0911.2914 ·
doi:10.1112/jlms/jdq063
> "Using van der Waerden's Theorem, we show that any minimal subshift having bounded Abelian complexity
> contains Abelian k-powers for every positive integer k. In the case of Sturmian words we prove
> something stronger: For every Sturmian word w and positive integer k, each sufficiently long factor of
> w begins in an Abelian k-power."

In a balanced word, χ-matched trains start everywhere. Combined with Fici et al. 2016, they have
explicit periods. **Keep.**

**fici2016abelian** (V): G. Fici, A. Langiu, T. Lecroq, A. Lefebvre, F. Mignosi, J. Peltomäki,
É. Prieur-Gaston, *Abelian powers and repetitions in Sturmian words*, Theor. Comput. Sci. 635 (2016)
16–34. https://arxiv.org/abs/1506.02797
> "We give a formula for computing the maximum exponent of an abelian power of abelian period m
> starting at a given position in any Sturmian word of rotation angle α. … We show that A(s_α) equals
> the Lagrange constant of the number α."

Survey Thm 47: an abelian power of period m and exponent k exists iff ‖mα‖ < 1/k. Translation: the
shift by q_k (a convergent denominator of the slope, ~log₂3 − 1) has density about 2‖q_kα‖ of
disagreements. This gives explicit anchor counts for f(w) (open problem 1). **Keep.**

**peltomaki2020abelian** (V): J. Peltomäki, *Abelian periods of factors of Sturmian words*, J. Number
Theory 214 (2020) 251–285. https://arxiv.org/abs/1905.06138 · doi:10.1016/j.jnt.2020.04.007
> "the minimum abelian period of a factor of a Sturmian word of angle α … is either tq_k with
> 1 ≤ t ≤ a_{k+1} … or q_{k,ℓ} (a denominator q_{k,ℓ} of a semiconvergent of α)."

The admissible anchor spacings are (semi)convergent denominators of log₂3: 1, 2, 5, 12, 41, 53, 306,
665, … **Keep.**

**karhumaki2013generalization** (V): J. Karhumäki, A. Saarela, L. Q. Zamboni, *On a generalization of
Abelian equivalence and complexity of infinite words*, J. Combin. Theory A 120 (2013) 2189–2206.
https://arxiv.org/abs/1301.5104
> "We show that the number of k-Abelian equivalence classes of words of length n grows polynomially,
> although the degree is exponential in k."

The estimator (open problem 4) lives on coarse equivalence classes, which are polynomially many.
**Open.**

**rao2015binomial** (V, zbMATH 1325.68173): M. Rao, M. Rigo, P. Salimov, *Avoiding 2-binomial squares
and cubes*, Theor. Comput. Sci. 572 (2015) 83–91. doi:10.1016/j.tcs.2015.01.029
> "the minimal alphabet size to construct a word with no 2-binomial squares is three … for 2-binomial
> cubes, in which case the minimal alphabet size is two"

Hook H5 [derived]: for d ∈ {1,2}, Σ_k e_k = const(n, #2) + #(scattered "21"). So G_* = 2^{ē}/3^{(n−1)/2}
is constant on 2-binomial classes (Parikh matrices). **Open.**

### 4.3 Unavoidable patterns (Zimin)

**bean1979avoidable** (V, PDF): D. R. Bean, A. Ehrenfeucht, G. F. McNulty, *Avoidable patterns in
strings of symbols*, Pacific J. Math. 85 (1979) 261–294. doi:10.2140/pjm.1979.85.261
> "Next we examine avoidable words in general and prove that all words of length at least 2n [OCR of
> 2^n] on an alphabet with n letters are simultaneously avoidable. … We provide an effective
> (recursive) characterization of avoidability."

Patterns substitute arbitrary nonempty words, with no length or sum matching. **Kill.**

**zimin1984blocking** (V, zbMATH 0599.20106): A. I. Zimin, *Blocking sets of terms*, Math. USSR Sb. 47
(1984) 353–364. doi:10.1070/SM1984v047n02ABEH002647
> "A description of the singleton blocking sets, i.e. the blocking terms, is obtained."

Zimin's theorem: unavoidable ⇔ encountered in Z_n. **Kill.**

**cooper2014bounds** (V): J. Cooper, D. Rorabaugh, *Bounds on Zimin word avoidance*, arXiv:1409.3080.
> "Zimin (1982) proved that every unavoidable word is encountered by some word Z_n … Here we explore
> bounds on how long words can be and still avoid the unavoidable Zimin words."

**Kill.**

**conlon2019tower** (V): D. Conlon, J. Fox, B. Sudakov, *Tower-type bounds for unavoidable patterns in
words*, Trans. AMS 372 (2019) 6213–6229. https://arxiv.org/abs/1704.03479 · doi:10.1090/tran/7751
> "obtaining essentially tight tower-type bounds for the function f(n,q) … showing that
> f(3,q) = Θ(2^q q!)."

Confirms F5: tower-type bounds, so only Z_n with n ≈ log* o is forced. **Kill.**

**carayol2019long** (V): A. Carayol, S. Göller, *On long words avoiding Zimin patterns*, STACS 2017 /
Theory Comput. Syst. 63 (2019) 926–955. https://arxiv.org/abs/1902.05540 · doi:10.1007/s00224-019-09914-2
> "f(n,k) is lower-bounded by a tower of n−3 exponentials, even for k=2. … we prove a doubly-exponential
> upper bound for encountering Zimin patterns in the abelian sense."

The abelian Zimin version is also doubly exponential. Even binary words escape quickly. **Kill.**

### 4.4 Shirshov height

**belov2012subexponential** (V): A. Ya. Belov, M. I. Kharitonov, *Subexponential estimates in Shirshov's
theorem on height*, Sb. Math. 203 (2012) 534–553. https://arxiv.org/abs/1207.2987 ·
doi:10.1070/SM2012v203n04ABEH004233
> "all the words over alphabet of cardinality l which length is greater than Psi(n,d,l) are either
> n-divided or contain d-th power of subword … Psi(n,d,l)=2^{18} l (nd)^{3 log_3 (nd)+13}d^2."

The dichotomy "high power or lexicographic decrease" does not give a covering menu. The power is a
local run (F3 trapping), and n-division is lexicographic, with no χ content. Balanced words take the
n-divided branch. **Kill.**

**kharitonov2014estimates** (V): M. Kharitonov, arXiv:1411.7435.
> "Psi(n,d,l)=l (nd)^{C log (nd)} and C is a constant."

Quasi-polynomial version. **Kill.**

**shirshov1957rings** (U: zbMATH metadata only): A. I. Shirshov, *On rings with identical relations*,
Mat. Sb. 43(85) (1957) 277–283. Statement (via Belov–Kharitonov): "the set of non n-divided words …
has bounded height h over the set Y consisting of all the words of degree <n." **Kill.**

### 4.5 Ramsey on words

**brown1971interesting** (V, zbMATH 0211.33504): T. C. Brown, *An interesting combinatorial method in
the theory of locally finite semigroups*, Pacific J. Math. 36 (1971) 285–289.
doi:10.2140/pjm.1971.36.285
> "Let X be a finite set, X^* the free semigroup … let M be a finite semigroup, and let φ be an
> epimorphism of X^* upon M. We give a simple proof of a combinatorial property of the triple (X,φ,M)"

Brown's lemma is the finite-semigroup pigeonhole. χ maps into the infinite semigroup ℕ², which is
exactly why it fails here. **Kill.**

**shelah1988primitive** (V, zbMATH 0649.05010): S. Shelah, *Primitive recursive bounds for van der
Waerden numbers*, JAMS 1 (1988) 683–697. doi:10.2307/1990952
> "exhibiting primitive recursive bounds on the van der Waerden numbers. All earlier proofs gave
> Ackermann-like bounds"

**Kill.**

**gowers2001new** (V, zbMATH 1028.11005): W. T. Gowers, *A new proof of Szemerédi's theorem*, GAFA 11
(2001) 465–588. doi:10.1007/s00039-001-0332-9
> "every subset of {0,1,…,N} of size at least N(log log N)^{−c} with c=2^{−2^{k+9}} contains an
> arithmetic progression of length k"

This is the best length control: a monochromatic AP of length about the five-times-iterated log of o.
**Kill.**

**hales1963regularity** (U: AMS 403; zbMATH metadata only): A. W. Hales, R. I. Jewett, *Regularity and
positional games*, Trans. AMS 106 (1963) 222–229. doi:10.2307/1993764. **Kill.**

**furstenberg1978topological** (U: empty review): H. Furstenberg, B. Weiss, *Topological dynamics and
combinatorial number theory*, J. Analyse Math. 34 (1978) 61–85. doi:10.1007/BF02790008. **Kill.**

### 4.6 Periodicity tools

**fine1965uniqueness** (U: AMS 403): N. J. Fine, H. S. Wilf, *Uniqueness theorems for periodic
functions*, Proc. AMS 16 (1965) 109–114. doi:10.2307/2034009. It underlies D2: two periods on a long
window collapse to the gcd. **Open** (as a tool).

**chen1958free** (U; already in the zero-sum review for a different statement): K. T. Chen, R. H. Fox,
R. C. Lyndon, Ann. Math. 68 (1958) 81–95. doi:10.2307/1970044. The Lyndon factorisation (canonical
rotation). **Kill** (tooling only).

**duval1983factorizing** (V, zbMATH 0532.68061): J.-P. Duval, *Factorizing words over an ordered
alphabet*, J. Algorithms 4 (1983) 363–381. doi:10.1016/0196-6774(83)90017-2
> "Applications of this algorithm are given to the computation of the least suffix of a word and the
> least circular shift of a word."

An O(o) canonical anchor (least rotation) for the anchored basis. **Kill** (tooling).

**crochemore1991twoway** (V, zbMATH 0808.68063): M. Crochemore, D. Perrin, *Two-way string-matching*,
JACM 38 (1991) 651–675. doi:10.1145/116825.116845
> "the Critical Factorization Theorem, which relates the global period of a word to its local
> repetitions of blocks."

The Critical Factorization Theorem (Cesari–Vincent 1978): a primitive word has a position whose local
period equals the global period. So short local repeats cannot sit everywhere. **Open** (minor).

**guibas1981periods** (U), **mignosi1998periodicity** (U), **constantinescu2006fine** (U): metadata
via zbMATH only. They cover autocorrelation counts, the golden-ratio threshold for local repetitions
versus periodicity, and the abelian Fine–Wilf theorem. **Kill / open** (low).

**charalampopoulos2020faster** (V): P. Charalampopoulos, T. Kociumaka, P. Wellnitz, *Faster approximate
pattern matching: a unified approach*, arXiv:2004.08350.
> "Either there are O(k^2) k-mismatch occurrences of P in T, or both P and T are at Hamming distance
> O(k) from strings with a common period O(m/k)."

This is the structural dichotomy for rotations at small Hamming distance, i.e. the multi-window
analogue of D2. Apply it with P = w and T = ww. **Open.**

### 4.7 Balanced, Sturmian and Christoffel words

**lothaire2002sturmian** (V, Cambridge page): M. Lothaire (J. Berstel, P. Séébold), *Sturmian words*,
ch. 2 of *Algebraic Combinatorics on Words*, CUP 2002, 45–110. doi:10.1017/CBO9781107326019.003
> "Sturmian words are infinite words over a binary alphabet that have exactly n + 1 factors of length n
> for each n ≥ 0." … "the Morse–Hedlund theorem stating the equivalence of Sturmian words … the set of
> balanced aperiodic words and the set of mechanical words of irrational slope."

1-balanced = mechanical = codings of rotations. **Keep.**

**morse1940symbolic** (U: JSTOR), **coven1973sequences** (U: Springer; survey quote: "a binary
aperiodic word is 1-balanced if and only if it is Sturmian"). **Keep.**

**vuillon2003balanced** (V, zbMATH 1070.68129): L. Vuillon, *Balanced words*, Bull. Belg. Math. Soc. 10
suppl. (2003) 787–805.
> "said to be balanced if, for any pair of factors (W,W′) with the same length and any element a in A,
> we have ||W|_a − |W′|_a| ≤ 1."

The survey of generalisations (C-balance, Fraenkel). **Keep.**

**berthe2002balance** (U), **tijdeman2000fraenkel** (U): metadata only. C-balance in higher dimension;
Fraenkel's conjecture for gap words using ≥ 3 letters. **Open / kill.**

**mignosi1991number** (V, zbMATH 0728.68093): F. Mignosi, *On the number of factors of Sturmian
words*, TCS 82 (1991) 71–84.
> "He gives and proves an exact estimation of the size of A_m (the set of factors of length m of all the
> Sturmian words)."

**berstel1993geometric** (V, zbMATH 0802.68099): J. Berstel, M. Pocchiola, IJAC 3 (1993) 349–355.
> "The number of factors of length m of Sturmian words is known to be 1 + Σ_{i=1}^m (m − i + 1) φ(i)"

So about m³/π² words: the polynomial count of 1-balanced words (D3). **Keep.**

**bedaride2010number** (V, zbMATH 1280.68145): N. Bédaride, E. Domenjoud, D. Jamet, J.-L. Rémy, *On the
number of balanced words of given length and height over a two-letter alphabet*, DMTCS 12(3) (2010)
41–62.
> "We exhibit a recurrence on the number of discrete line segments … encoded as balanced words of given
> length and height … We give generating functions and study the asymptotic behaviour."

This counts 1-balanced gap words at fixed (o, E). **Keep.**

**heinis2001low** (V, numdam abstract): A. Heinis, *On low-complexity bi-infinite words and their
factors*, J. Théor. Nombres Bordeaux 13 (2001) 421–442.
> "It is well-known that the number of subwords of length n from this class has growth order n^3 if
> k=1. … we show that the number is ≥2^{n/2} when k≥2."

The exponent rendering (2^{n/2}) was inferred from the page. This is the explicit exponential lower
bound that kills single-move covering on 2-balanced words. **Keep.**

**berthe2019balancedness** (V, PDF): V. Berthé, P. Cecchi Bernales, *Balancedness and coboundaries in
symbolic systems*, arXiv:1810.07453.
> "the number of 1-balanced words of length n is polynomial [Lip82, Mig91] while the number of
> C-balanced words of length n for C > 1 is exponential [Lip82] and, therefore, being C-balanced is
> relatively common."

**Keep.** Also **lipatov1982classification** (U): cited through this paper.

**pirillo2000new** (V): G. Pirillo, *A new characteristic property of the palindrome prefixes of a
standard Sturmian word*, Sém. Lothar. Combin. 43 (2000) B43f.
https://www.mat.univie.ac.at/~slc/wpapers/s43pirillo.html
> "We prove that a word w is a palindrome prefix of some standard Sturmian word if and only if wab and
> wba are conjugate."

Hook H1. The cyclic words with two rotations differing by one adjacent swap are exactly the Christoffel
classes, which have a monomial core (D2). **Keep.**

**arnoux1991representation** (V, zbMATH 0789.28011): P. Arnoux, G. Rauzy, Bull. SMF 119 (1991)
199–215. doi:10.24033/bsmf.2164
> "It is shown how all minimal sequences u of complexity p_n(u)= n+1 can be described by infinite
> sequences consisting of two substitutions"

The S-adic (desubstitution) description of balanced words. **Open.**

**cassaigne2000imbalances** (V, zbMATH 1004.37008): J. Cassaigne, S. Ferenczi, L. Q. Zamboni,
*Imbalances in Arnoux–Rauzy sequences*, Ann. Inst. Fourier 50 (2000) 1265–1276. doi:10.5802/aif.1792
> "by showing that these sequences are not necessarily N-balanced"

A caution: renormalisation does not by itself give bounded discrepancy. **Kill** (as a shortcut).

**berthe2014beyond** (V): V. Berthé, V. Delecroix, *Beyond substitutive dynamical systems: S-adic
expansions*, RIMS Kôkyûroku Bessatsu B46 (2014) 81–123. https://arxiv.org/abs/1309.3960
> "A fundamental example of this relation is between Sturmian sequences and regular continued
> fractions."

Lead for renormalising cycle words along the continued fraction of log₂3. **Open.**

**halbeisen1997optimal** (V, zbMATH 0863.11015; **dup**): L. Halbeisen, N. Hungerbühler, *Optimal
bounds for the length of rational Collatz cycles*, Acta Arith. 78 (1997) 227–239.
> "optimal estimates for the length of a cycle in terms of its minimum are proved."

The extremal (Christoffel) cycle words are already in KNOWLEDGE_MAP. New point: D2 shows Christoffel
words are the *only* b = 2 single-move words. **Keep.**

### 4.8 Zero-sum

**gao2006zerosum** (V, zbMATH 1122.11013): W. Gao, A. Geroldinger, *Zero-sum problems in finite
Abelian groups: a survey*, Expo. Math. 24 (2006) 337–369. doi:10.1016/j.exmath.2006.07.002
> "a very useful and comprehensive survey on results and open problems in the area of combinatorial
> zero sum problems in finite abelian groups."

**gao2008inverse** (V): arXiv:0801.3792.
> "The maximal length of a minimal zero-sum subsequence in G is the Davenport constant … For a rank 2
> group G=C_n ⊕ C_n, it is known that D(G)=2n−1."

**geroldinger2010congruence** (V): arXiv:1007.0251.
> "every sequence S over G of length |S| ≥ ℓ has a nonempty zero-sum subsequence T of length
> |T| ≡ 0 mod d."

This is the zero-sum analogue of χ-matching (sum and length condition), but for *subsequences*, which
carry no position. **Kill.**

**erdos1961theorem** (U), **olson1969combinatorial** (U): metadata only. **Kill.**

### 4.9 Counting heuristics

**tao2011collatz** (V; **dup**): T. Tao, blog, 25 Aug 2011.
> "Littlewood-Offord techniques are no longer of much use" … "this does not directly give any way to
> prevent" … "This, of course, is far short of any rigorous proof."

The entropy constant exp(h(log2/log3)) ≈ 1.9318 per halving matches F5's thin budget. No formal
version was found. **Kill** (for proofs).

---

## 5. Leads for round 2

1. **Peltomäki–Whiteland, *Avoiding abelian powers cyclically*** (Adv. Appl. Math. 121, 2020; ref [112]
   of the survey). This is the cyclic version, the one that matters (D4). Which cyclic words are
   cyclic abelian or additive powers, and how many are there?
2. **Lipatov 1982** and **Heinis 2001** (full text). Find the exact entropy h(C) of C-balanced binary
   words and compare it with the 1.04 nats/letter budget (F5). With D6 this turns "cycle words are
   near-balanced" into a count.
3. **Bringmann–Künnemann–Wellnitz, SODA 2019**, "few matches or almost periodicity". Apply it with
   P = w and T = ww to bound how many rotation pairs can have k-window cores.
4. **Adamczewski 2003**, *Balances for fixed points of primitive substitutions* (TCS 307), and
   Berthé–Tijdeman 2002. Balance via eigenvalues, a candidate for relating the C of D6 to x_max/x_min.
5. **Parikh matrices** (Mateescu–Salomaa–Salomaa–Yu 2001) and **Rigo–Salimov 2013** (2-binomial
   equivalence), for open problem 4 (H5).
6. **Justin 1972** (JCTA 12, uniformly repetitive semigroups) and the **Lietard thesis** (2020, the
   70M-letter additive-cube-free word over {0,1,2,3}, mentioned in search results, not verified). For
   any post-2020 change in the status of additive squares and cubes, check Rosenfeld's and Mol's 2024–26
   preprints.
7. **Lothaire ACW ch. 3** (Cassaigne, *Unavoidable patterns*) and **ch. 8** (periodicity): not fetched,
   because the TLS certificate on Berstel's mirror failed.
8. **Fine–Wilf with mismatches** (Blanchet-Sadri et al.) and the **abelian Fine–Wilf theorem**
   (Constantinescu–Ilie 2006), to extend D2 from one window to k windows.
9. **Layer-2 hand-off.** D4 and D5 reduce multi-window cores to gcd(2^E − 3^o, Σ 2^a3^b·B). Pass to the
   S-unit / primitive-divisor theme: Bugeaud–Corvaja–Zannier on gcd(aⁿ − 1, bⁿ − 1), and
   Evertse–Schlickewei–Schmidt (dup).
