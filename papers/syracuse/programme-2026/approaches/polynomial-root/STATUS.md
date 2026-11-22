# Status — polynomial-root

## Current state

Report split into a main [`report.tex`](report.tex) (preamble + abstract) plus per-section
sources under [`sections/`](sections/) — `01-construction`, `02-catalogue`, `03-cohomology`;
compiles with `pdflatex` to 9 pp (`report.pdf`). Section 1 is the construction; Section 2 opens
with **the four known cycles** and their explicit polynomials, then the **coprime catalogue**
$\gcd(E,o)=1$, $E+o\le20$ — all
$1233$ cyclic classes across $64$ types, fully computed and cross-checked by
[`gen_table.py`](gen_table.py) (self-test exits 0: cocycle law on every split up to length 6,
worked examples, reparametrisation identities). Per-class data are in
[`coprime_catalogue.csv`](coprime_catalogue.csv); the report holds a per-type summary and the
$24$ smallest-Mahler classes.

## Results

- **Construction certified.** $S=\chi\circ\partial_u$ is a $1$-cocycle (Prop. 1.6); its class
  in $\mathbb{Z}[X^{\pm1},Y^{\pm1}]/(1-\chi(w))$ is a conjugacy invariant up to a monomial unit
  (Prop. 1.8). Unimodular reparametrisation gives the ring iso to
  $R_d=\mathbb{Z}[t^{\pm1},s]/(s^d-1)$, $d=\gcd(E,o)$ (Prop. 1.9). For $\gcd(E,o)=1$ this is
  one-variable: $R_1=\mathbb{Z}[t^{\pm1}]$, via $X\mapsto t^{-(E-o)}$, $Y\mapsto t^{o}$.
- **The four known cycles and their polynomials (featured).** Under the accelerated $T$-map
  ($u:x\mapsto(3x+1)/2$, $v:x\mapsto x/2$) the four known integer cycles are the words
  $\mathtt{u}\,(x{=}-1)$, $\mathtt{uv}\,(x{=}1)$, $\mathtt{uuv}\,(x{=}-5)$,
  $\mathtt{uuuuvuuuvvv}\,(x{=}-17$, the only nontrivial one$)$ — fixed points reproduced exactly
  in `gen_table.py`. Their polynomials: $P_{-1}=P_{1}=1$; $P_{-5}=t+1=\Phi_2$;
  $P_{-17}=t^{17}+t^{13}+t^{9}+t^{8}+t^{5}+t^{4}+1=\Phi_7(t)\,(t^{11}-t^{10}+t^{7}-t^{6}+t^{4}-t+1)$,
  Mahler $1.42747$ (irreducible non-reciprocal degree-$11$ factor, $6$ roots off the circle).
  $D=2^{11}-3^{7}=-139$.
- **The cyclic factor + Littlewood core (Prop. 2.1, proved + machine-checked).** For coprime
  type, $P_w$ is a $0/1$ polynomial with exactly $o$ terms; the *full* cyclotomic factor
  $g_o=(t^o-1)/(t-1)=1+t+\cdots+t^{o-1}=\prod_{d\mid o,\,d>1}\Phi_d$ divides $P_w$ — strictly
  stronger than $\Phi_o\mid P_w$ (they coincide only for prime $o$, e.g. the $-17$ cycle, $o=7$);
  and the quotient $R_w=P_w/g_o$ has all coefficients in $\{-1,0,1\}$ (verified: max $|$coeff$|=1$
  over all $1233$ classes; $P_w/\Phi_o$ alone reaches $2$ for composite $o$). $R_w$ is the genuine
  cycle invariant (e.g. $-17$: $R_w=t^{11}-t^{10}+t^7-t^6+t^4-t+1$). All from $\{e_k\bmod o\}$ being
  a complete residue system; the $\{-1,0,1\}$ bound from
  $R_n=\mathbf1[e((n{-}1)\bmod o)\gt n{-}1]-\mathbf1[e(n\bmod o)\gt n]$.
- **Normalisation tower (Cor. 2.2, proved + checked).** $R_w(1)=1$ (since $P_w(1)=g_o(1)=o$), so
  $R_w=1+(t-1)Q_w$ where $Q_w(t)=\sum_n\mathbf1[e(n\bmod o)\gt n]\,t^{n}$ is *itself* a $0/1$
  polynomial. Hence the tower $P_w=g_o\,(1+(t-1)Q_w)$ with $g_o,Q_w\in\{0,1\}[t]$ and
  $R_w\in\{-1,0,1\}[t]$ — verified, $Q_w$ is $0/1$ on all $1233$ classes. (E.g. $-17$:
  $Q_w=t^{10}+t^{6}+t^{3}+t^{2}+t$.)
- **Explicit polynomials catalogued.** `coprime_catalogue.csv` lists $P_w(t)$, its Littlewood
  core $R_w(t)$, **and $Q_w(t)$** explicitly for all $1233$ classes (plus degree, Mahler,
  cyclotomic flag, factorisation).
- **The map $w\mapsto R_w$ (Prop. 2.5, proved + machine-checked).** Reflection symmetries: both
  $R_{w^R}$ (reverse) and $R_{\bar w}$ (complement $u\!\leftrightarrow\!v$, type
  $(E,o)\!\mapsto\!(E,E{-}o)$) equal the *reciprocal* of $R_w$; hence $R_{\overline{w^R}}=R_w$ — a
  fixed-point-free involution $(E,o)\!\mapsto\!(E,E{-}o)$ that explains the $o\!\leftrightarrow\!E{-}o$
  duality and the all-even fibres. Also $R_w(0)=R_w(1)=1$. **Highly non-injective:** the $4506$
  coprime necklaces with $E\le16$ realise only $1529$ distinct cores ($818$ up to reciprocal; $55$
  cyclotomic). Cyclotomic cores dominate the fibres ($R_w=1$: $80$ necklaces; $\Phi_6$: $50$; mean
  fibre $7.7$ vs $2.8$ for non-cyclotomic). Distinct-core catalogue in `R_cores.csv`; cores of
  degree $\le4$ in the report (Table 4). Splitting: for $\gcd=1$, $R_w=$ cyclotomic $\times$
  Salem/Pisot; for $d>1$ the ring splits $\Q[t^{\pm},s]/(s^d-1)\cong\prod_{e\mid d}\Q(\zeta_e)[t^{\pm}]$.
- **Cohomological frame — $R_w$ is an Alexander polynomial (§3, Thm 3.3, proved + machine-checked).**
  $S=\chi\partial_u$ is a $1$-cocycle, $[S]\in H^1(F_2;\Lambda)$; $P_w$ is its restriction to the
  loop $\langle w\rangle$ (so $P_w\in H^1(\langle w\rangle;\Lambda)=\Lambda/(1-\chi(w))$). For the
  one-relator group $G_w=\langle u,v\mid w\rangle$ (aspherical, Lyndon), with $T=\chi\partial_v$,
  $H^2(G_w;M)=M/(S,T)$, and **$R_w=\gcd(\chi\partial_u w,\chi\partial_v w)$ is the Alexander
  polynomial** of $G_w$: $\Q\otimes H^2\cong\Q[t^{\pm}]/(R_w)$, $\deg R_w=\dim_\Q H^2$. So the
  Mahler/Salem/Lehmer phenomena are Alexander-polynomial phenomena (Lehmer $\leftrightarrow$ the
  $(-2,3,7)$ pretzel knot). Crowell–Fox $(X{-}1)S+(Y{-}1)T=\chi{-}1$ and $R_w=\gcd(S,T)$ certified
  in `gen_table.py`.
- **Deeper structure (§3 closing notes).** §3 records: (a) the **Fox–Lyndon free resolution** and
  the Alexander chain complex $\Lambda_w\xrightarrow{(S,T)}\Lambda_w^2\to\Lambda_w$ ($H_0=\Z$,
  $H_1=A_w$ order $R_w$, $H_2=0$), with **Reidemeister–Milnor torsion** $\tau\doteq R_w/(t-1)$;
  (b) the non-coprime case $H_1(G_w)=\Z^2/\langle(o,E{-}o)\rangle\cong\Z\oplus\Z/d$ — the $s$-variable
  **is** the $\Z/d$ torsion, and $s\mapsto\zeta_e$ is the isotypic decomposition over the
  $\Z/d$-cover; (c) the **reciprocity/duality locus** — cores are generally *not* self-reciprocal
  (corrects an earlier overclaim of $\Delta(t)\doteq\Delta(1/t)$): of $1529$ distinct cores
  ($E\le16$) exactly $107$ are self-reciprocal ($55$ cyclotomic $+$ $52$ reciprocal/Salem incl.
  Lehmer; the $-17$ core lies off), palindromic necklaces sufficing; the Blanchfield-pairing
  existence on that locus is the open question. Self-reciprocal counts machine-verified.
- **Lehmer's number is realised (headline).** Over the $1233$ coprime classes ($E+o\le20$) the
  Mahler measures lie in $[1,\,1.65378]$; $274$ are cyclotomic, $959$ are not. The **smallest
  measure $>1$ is Lehmer's number $1.1762808\ldots$** — the smallest known Mahler measure $>1$
  of any integer polynomial — realised e.g. by $w=\mathtt{uuuvuuvvvuuv}$ of type $(12,7)$, whose
  cocycle factor is exactly Lehmer's degree-$10$ polynomial.
- **Coprime cyclotomic frontier is $E+o=10$.** Every coprime word with $E+o\le9$ is cyclotomic
  (Mahler $1$). The first exception is type $(7,3)$, $w=\mathtt{uuvuvvv}$:
  $P_w=\Phi_3(t)(t^3-t^2+1)$, Mahler $=$ the plastic number $1.324718\ldots$ (smallest Pisot
  number, root of $x^3-x-1$), non-cyclotomic factor with Galois group $S_3$. **This corrects the
  earlier heuristic guess of $(4,3)$** — $\mathtt{uuuv}\mapsto\Phi_3$ is cyclotomic.
- **For any $d$, all $E+o\le6$ classes are cyclotomic** (the original small-word observation,
  subsumed): $S(w)$ has $o$ monomials, and $o\le3$ in that range gives monomial $\times$
  cyclotomic.
- **Salem/Pisot structure.** Small Mahler measures come from Salem factors (reciprocal, one root
  off the circle); the next measures realised after Lehmer are $1.21639,\,1.23526,\,1.25105$.
  Visible $o\leftrightarrow E-o$ duality: types $(E,o)$ and $(E,E-o)$ share all statistics.

## Dead ends

- _(none)_ — the earlier $(4,3)$ "first non-cyclotomic" guess was wrong (it is cyclotomic);
  corrected to the computed frontier $E+o=10$, type $(7,3)$.

## Open questions

- Which words realise each successive small Salem number (Lehmer, then $1.18837$, $1.20002$,
  …)? Lehmer appears already at $E+o\le20$ but the next textbook Salems do not — what is the
  smallest $E+o$ for each?
- Is there a structural reason the coprime frontier sits exactly at $E+o=10$, type $(7,3)$?
- The non-coprime ($d>1$) catalogue: how do the $s$-graded pieces in $R_d$ factor, and do new
  (non-cyclotomic) phenomena appear at smaller $E+o$ there?
- At $(X,Y)=(2,3)$, does a Salem/Lehmer factor of $P_w$ translate into a sharper divisibility
  ceiling for `cocycle-combine` than a generic non-cyclotomic factor?

## Next step under consideration

Work out the **non-coprime ($d>1$) stratum**: the quotient ring splits by CRT into
$\prod_{e\mid d}\mathbb{Z}[\zeta_e][t^{\pm}]$, so $S(w)$ acquires $\zeta_e$-twisted components beyond
the $e=1$ core $R_w$ — what new cores/Mahler measures appear, and is the cycle word special in its
type? Also: extend the core catalogue past $E\le16$ and characterise the *image* of $w\mapsto R_w$
(which Littlewood polynomials with $R(0)=R(1)=1$ actually occur).
