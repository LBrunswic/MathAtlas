# Ellison 1971 — explicit lower bound for $|2^x-3^y|$ (Pillai/Baker)

- **Source file:** `sources/ellison1971-pillai.pdf` (NUMDAM open access, `http://www.numdam.org/item/STNB_1970-1971____A10_0/`)
- **Full citation:** W. J. Ellison, *On a theorem of S. Sivasankaranarayana Pillai*, Sém. Théorie des Nombres de Bordeaux (1970–1971), exp. no. 10, 10 pp.
- **Feeds:** the **§5 "honest size barrier"** — the explicit floor on $|D|=|2^E-3^o|$ that generic compensations can only re-express.

## What it says (relevant part only)

Via Baker's linear-forms-in-logarithms method applied to $|x\log2-y\log3|$, Ellison proves the explicit
bound used by Knight:
$$|2^{x}-3^{y}|\;>\;2^{x}e^{-x/10}\qquad\text{for all }x\notin S,$$
where $S=\{1,2,3,4,5,6,7,8,9,10,11,13,14,16,19,27\}$ is finite (so it holds for all $x>27$). The
extreme near-miss in range is $x=19,y=12$: $|2^{19}-3^{12}|=7153$ (ratio $\approx0.0136$). He also gives
the general effective Pillai bound $|am^x-bn^y|\ge m^{(1-\delta)x}$ for $x>x_0$ effective, and Feldman's
$\min_y|2^x-3^y|\ge 2^x x^{-K}$.

## How it connects here

This is the quantitative content of **§5**'s claim that a *generic* (pure $\mathbb{Z}[X,Y]$)
compensation "can only re-express the size bound $|D|\approx2^E$, matching the honest barrier". Since
$E\approx o\log_23$, $2^E e^{-E/10}$ grows like $\gtrsim 2.56^{\,o}$, so $|D|$ is exponentially large for
all but the finite exceptional $x$. **Consequence for the search:** a generic monomial/polynomial core
$C$ forces $|D|\le|C|$, which by Ellison can only be satisfied by finitely many $(E,o)$ — exactly the
"finitely many words in the family" ceiling. To *beat* transcendence theory one must produce a $|D|$
smaller than this floor, i.e. land on a genuinely **exceptional** $2^a-3^b$ near-miss — confirming why
the exceptional tier is the only place a real improvement can live.

## Open thread it touches

Quantifies the barrier every cheap/generic ceiling runs into; the exceptional tier (small $2^a-3^b$) is
the complement. Chase: **Rhin 1987** (*Progr. Math.* 71, 155–164, sharper $\|x\log2-y\log3\|$, used by
Simons–de Weger), Baker 1975, Matveev 2000, Bennett on $|2^a-3^b|$.
