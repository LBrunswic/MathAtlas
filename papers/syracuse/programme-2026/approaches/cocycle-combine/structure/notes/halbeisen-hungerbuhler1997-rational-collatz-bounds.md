# Halbeisen–Hungerbühler 1997 — optimal bounds for rational Collatz cycles

- **Source file:** `sources/halbeisen-hungerbuhler1997-rational-collatz-bounds.pdf` (author copy, math.ch; also CC-BY at `matwbn.icm.edu.pl/ksiazki/aa/aa78/aa7833.pdf`)
- **Full citation:** L. Halbeisen, N. Hungerbühler, *Optimal bounds for the length of rational Collatz cycles*, Acta Arith. **78** (1997), no. 3, 227–239.
- **Feeds:** the rigorous backing for **C9** (high cycle = Christoffel rotation), and a-priori range bounds for the combinator search.

## What it says (relevant part only)

For a parity sequence $s$ of length $l$ with $n$ ones, the cycle start is $\phi(s)/(2^l-3^n)$ with
$\phi(s)=\sum_j s_j\,2^{j-1}3^{(\text{ones after }j)}$ — i.e. our $S/D$. **Lemma 4:** $\phi$ is strictly
monotone for the prefix-sum (balance) dominance order on a rotation orbit. **Lemma 5:** the
evenly-spread (Beatty/lower-Christoffel) rotation $\tilde s_i=\lceil in/l\rceil-\lceil(i-1)n/l\rceil$
*minimises* $\phi$ in its orbit and is the orbit that *maximises* that minimum over all weight-$(l,n)$
classes ($M_{l,n}:=\max_s\min_{t\in\sigma(s)}\phi(t)$, value in **Cor. 1**). Range:
$M_{l,n}/(n3^n)\in[\tfrac1{20},\tfrac7{10}]$ (improvable to $[\tfrac16,\tfrac12]$). **Thms 3–4** give an
optimal cycle-length criterion; with verification to $2.1\times10^{14}$, any nontrivial cycle has length
$\ge 102{,}225{,}496$.

## How it connects here

Lemma 5 is the **rigorous dual of C9**: the high cycle (rotation class with the largest minimal member)
is the upper-Christoffel class, exactly the word $1u0$ that C9's monomial-core obstruction targets. So
C9 (Knight, Baker-free, kills that one class) and H–H (which class it is, and how big its minimum must
be) are two faces of the same Christoffel fact. The $M_{l,n}/(n3^n)\in[\tfrac16,\tfrac12]$ sandwich is
directly usable as an **a-priori range filter** in the cocycle search: it bounds how small the minimal
member of any $(l,n)$-cycle can be, pruning $(E,o)$ pairs whose Christoffel minimum is already too large.
All generic; the arithmetic is only the size of $2^l-3^n$ (the Ellison barrier, [[ellison1971-pillai]]).

## Open thread it touches

§5 (generalise C9 beyond the Christoffel seam): H–H's monotonicity (Lemma 4) orders *all* rotations by
$\phi$, not just the extreme pair — a lever for finding other rotation pairs with small/monomial cores.
References to chase: **Crandall 1978** ($k/l$ a convergent of $\log_23$), Lagarias 1990 (*set of rational
cycles*, Acta Arith. 56), Eliahou 1993 ([[eliahou1993-cycle-lengths]]).
