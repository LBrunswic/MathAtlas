# Status — circulant_matrix

## Current state

Active — child of [`cycle-gcd`](../cycle-gcd/STATUS.md). The matrix formula is found, derived,
and numerically verified. The strategic payoff (an a-priori bound on $\gcd_j S^{(j)}$ via the
matrix's integer structure) is identified but not started.

## Results

- **Re-indexed rotation sum (proved).** With $e_0=0\le\dots\le e_o=E$,

  $$S^{(j)}=\sum_{i=0}^{o-1}2^{\,e_i-e_j+E\,\mathbf 1[i \lt j]}\,3^{\,o-1-((i-j)\bmod o)},$$

  so $\vec S=M\mathbf 1$ with $M_{j,i}=2^{\,e_i-e_j+E\,\mathbf 1[i \lt j]}\,3^{\,o-1-((i-j)\bmod o)} \in\mathbb{Z}_{\ge0}$.

- **Circulant factorization (proved).** With $\tilde e_k=e_k-\tfrac{k}{o}E$,
  $\Delta=\operatorname{diag}(2^{\tilde e_k})$, and $C$ circulant with symbol
  $c_r=2^{rE/o}3^{o-1-r}$:

  $$\vec S=\Delta^{-1}C\Delta\,\mathbf 1,\qquad M=\Delta^{-1}C\Delta,\qquad
  M_{j,i}=2^{\tilde e_i-\tilde e_j}c_{(i-j)\bmod o}.$$

  The power-of-2 twist $2^{\tilde e_i-\tilde e_j}=2^{(e_i-e_j)-(i-j)E/o}$ is the seed sketch's
  matrix term; $C$ carries the $3$-powers and the average-gap factor $2^{E/o}$.

- **Spectrum (proved).** Eigenvalues of $C$ are

  $$\hat c_\ell=\dfrac{D}{2^{E/o}\omega^\ell-3},$$

  $\omega=e^{2\pi i/o}$, $\ell=0,\dots,o-1$ — $D$ in every numerator.

- **Determinant (proved).** $\det M=\det C=(-1)^{o+1}D^{\,o-1}$, via
  $\prod_\ell(3-2^{E/o}\omega^\ell)=3^o-2^E=-D$.

- **Determinant factorization + proposed identities** — see [`factorization.md`](factorization.md).
  Three factorizations of $\det M$ (spectral, root-of-unity/resultant, geometric-circulant) all
  give $(-1)^{o+1}D^{o-1}$, plus four identities to mine:
  - **A — factorization of $D$:** $|2^E-3^o|=\prod_\ell|3-2^{E/o}\omega^\ell|$; the only small
    factor is $|3-2^{E/o}|$, vanishing exactly in the critical regime $2^{E/o} \to 3$.
  - **B — word-independence:** $\det M=(-1)^{o+1}D^{o-1}$ for every word of given $(E,o)$ (word
    structure lives only in $\Delta$, invisible to the determinant).
  - **C — cofactor certificate:** $\operatorname{adj}(M)\vec S=(-1)^{o+1}D^{o-1}\mathbf 1$, an
    explicit divisibility-free $\mathbb Z$-combination proving $\gcd_j S^{(j)}\mid D^{o-1}$.
  - **D — Leibniz identity:** signed sum of $o!$ monomials $2^a3^b$ collapses to $\pm D^{o-1}$.

- **Number-field rewriting** — see [`number_field.md`](number_field.md). With $\beta=2^{E/o}$,
  $K=\mathbb Q(\beta)=\mathbb Q(2^{1/b})$, $b=o/\gcd(E,o)$:
  - **$D$ is a norm:** $D=\pm N_{K/\mathbb Q}(\beta-3)$ when $\gcd(E,o)=1$; for $g=\gcd(E,o)\gt 1$,
    $N_{K/\mathbb Q}(\beta-3)=\pm(3^{o/g}-2^{E/g})$ is a proper factor of $D$ (orbit product) — so
    $g$ = field-degree defect = circuit count. Verified $(8,5),(7,4),(5,3),(19,12)$ [norm$=|D|$],
    $(12,4),(6,4)$ [proper factor; $(6,4)$: $\beta-3$ a unit].
  - **$\det M$ is a norm:** eigenvalues are the Galois orbit of the algebraic integer
    $\hat c_0=D/(\beta-3)$, and $\det M=N_{K/\mathbb Q}(\hat c_0)=\pm D^{o-1}$ (the exponent $o-1$
    from $N(\hat c_0)N(\beta-3)=(\pm D)^o$).
  - **Structural payoff:** $C$ = regular representation of mult-by-$\xi$, so word-independence
    (Identity B) = norm is basis-independent. Gcd question $\to$ factorization of the ideal
    $(\beta-3)$ in $\mathbb Z[\beta]$: primes $p\mid D$ ↔ degree-1 primes $(p,\beta-3)$;
    $\gcd_j S^{(j)}=|D|$ on cycles = full ideal, off-cycle = sub-ideal index. This is the answer to
    the old "spectral → integer bridge" question: the integers are **norms**.
  - **Rotation sums are traces (§6 of number_field.md).** $\hat c_0=D/(\beta-3)=\sum_k3^{o-1-k}\beta^k$;
    $S^{(0)}$ is $\hat c_0$ with the uniform monomial $\beta^k$ replaced by the true word value $2^{e_k}$.
    With the word functional $L(\beta^k)=2^{e_k}=\operatorname{Tr}_{K/\mathbb Q}(\gamma_W\cdot)$:
    $$2^{e_j}S^{(j)}=L(\beta^j\hat c_0)=\operatorname{Tr}_{K/\mathbb Q}(\gamma_W\beta^j\hat c_0)
    =D\cdot\operatorname{Tr}_{K/\mathbb Q}\!\big(\tfrac{\gamma_W\beta^j}{\beta-3}\big),$$
    $\gamma_W$ in the codifferent (denominators $o\cdot$2-powers). Verified exactly $(8,5),(7,4),(3,2)$.
    Since $D$ is odd and $\gcd_jS^{(j)}\mid D$, the $2^{e_j}$ rescaling is invisible to the gcd —
    so $\gcd_jS^{(j)}$ = content of the traces of the orbit $\{\beta^j\hat c_0\}$ (a codifferent question).
  - **gcd = shedding trace-denominator primes (§7 of number_field.md, verified 2005 words).** Let
    $T_j=\operatorname{Tr}_{K/\mathbb Q}(\gamma_W\beta^j/(\beta-3))=2^{e_j}S^{(j)}/D$, denominator
    $\delta_j=|D|/\gcd(S^{(j)},D)$. Then $\gcd_jS^{(j)}=|D|/\operatorname{lcm}_j\delta_j$. Per prime
    $p\mid D$: $v_p(\gcd_jS^{(j)})=\min_j v_p(S^{(j)})$, and $p$ is **shed** from the gcd iff some
    trace part has $p$ in its denominator ($v_p(S^{(j)})\lt v_p(D)$). Each prime kept/shed
    independently (e.g. $(3,3)$, $D=55$: $5$ shed, $11$ kept, gcd$=11$). **Cycle $\iff$ all $T_j$
    integral** — no prime in any trace denominator. So the cycle conjecture = "every nontrivial word
    has a non-integral trace part," a **local per-prime** target replacing the global $|D|$ bound.
  - **Rotation collapse + the word element (see [`gamma_w.md`](gamma_w.md), verified 3000+ words).**
    For $p\mid D$ ($p\ge5$) the rotation recursion forces $v_p(S^{(j)})$ independent of $j$ (also:
    $\beta$ is a $p$-unit), so $\delta_j$ is constant and
    $$\gcd_jS^{(j)}=\gcd(S^{(0)},D)=|D|/\delta,\quad \delta=\text{denom of }T_0=\operatorname{Tr}(\gamma_W/(\beta-3)).$$
    Only **one** trace matters. Closed form $\gamma_W=\tfrac1o\sum_k2^{e_k}\beta^{-k}$ (codifferent
    element); universal kernel $\operatorname{Tr}(\beta^{-k}/(\beta-3))=o\,3^{o-1-k}/D$ gives $T_0=S^{(0)}/D$.
    Local: at $\mathfrak p=(p,\beta-3)$, $\hat c_0$ is a unit and $p$ is shed iff
    $v_p(\gamma_W(\beta_{\mathfrak p}))\lt v_p(D)$, $\beta_{\mathfrak p}$ = Hensel lift of $3$.

- **Circuit case $g=\gcd(E,o)\gt1$** — see [`circuits.md`](circuits.md), verified $(6,4),(12,4),(6,3)$.
  The field-only story (which assumed $g=1$, so $K=\mathbb Q(\beta)$ is a degree-$o$ field) was never
  about $K$: everything lives in the **étale algebra** $A=\mathbb Q[x]/(x^o-2^E)$, $\dim_{\mathbb Q}A=o$,
  a field $\iff g=1$ and otherwise a product $A=\prod_iK_i$ of **circuit fields**.
  - **All identities transfer verbatim** with $\operatorname{Tr}_{A/\mathbb Q}$ for $\operatorname{Tr}_{K/\mathbb Q}$:
    $2^{e_j}S^{(j)}=\operatorname{Tr}_{A/\mathbb Q}(\gamma_W\hat x^j\hat c_0)$, $\det M=N_{A/\mathbb Q}(\hat c_0)
    =\pm D^{o-1}$, rotation collapse, per-prime gcd law. The power basis $\{\hat x^k\}$ is genuinely a
    basis of $A$ for all $(E,o)$ (it is over-determined in $K$ once $g\gt1$, which is why the field
    story needed $g=1$); the trace kernel $\operatorname{Tr}_{A/\mathbb Q}(\hat x^n)=o\cdot2^{En/o}\mathbf 1[o\mid n]$
    is irreducibility-independent.
  - **Circuit factorization:** $A\cong\prod_iK_i$ over the $\mathbb Q$-irreducible factors of $x^o-2^E$;
    $D=\prod_{m=0}^{g-1}(2^a-3^b\zeta_g^m)$ ($a=E/g,b=o/g$), the $g$ circuits. Principal real circuit
    $K=\mathbb Q(2^{1/b})$ gives $N_{K/\mathbb Q}(\beta-3)=\pm(2^a-3^b)$ (a proper factor of $D$);
    other circuits carry the rest. Ex. $(6,4)$: $A=\mathbb Q(\sqrt2)\times\mathbb Q(\sqrt{-2})$, real
    circuit a **unit** ($N{=}1$), all of $D{=}{-}17$ in the conjugate circuit.
  - **Localization (sharpens §7):** $\operatorname{Tr}_{A/\mathbb Q}=\sum_i\operatorname{Tr}_{K_i/\mathbb Q}$,
    so each prime $p\mid D$ sits in **exactly one** circuit field, where its keep/shed verdict is decided
    (in degree $\le b=o/g$). Cycle $\iff$ every circuit keeps its prime(s) simultaneously. Verified
    $(12,4)$: $D=5\cdot11\cdot73$, the three circuit trace-contributions carry denominators
    $16\cdot5,\,16\cdot11,\,4\cdot73$ — one prime each.

- **Numerical checks** (run inline): row sums of $M$ equal $S^{(j)}$; $\det M=(-1)^{o+1}D^{o-1}$;
  $\operatorname{adj}(M)\vec S=\det M\cdot\mathbf 1$ with integer cofactors; and
  $\prod_\ell(3-2^{E/o}\omega^\ell)=3^o-2^E$ — all verified for words $(2)$, $(1,2)$, $(E{,}o){=}(8{,}5)$
  [$D{=}13$, $\det{=}13^4$], $(7,4)$ [$D{=}47$, $\det{=}-47^3$].

## Dead ends

- _(none yet)_ — but note the inherited circularity warning: any bound that uses the cycle
  divisibility returns $|D|$ and is worthless. The matrix structure must be exploited a priori.

## Open questions

- **Content of $M\mathbf 1$ vs. SNF of $M$.** $\gcd_j S^{(j)}$ is the content of the row-sum
  vector of an integer matrix with $\det=\pm D^{o-1}$. Can the Smith normal form (or just the
  largest invariant factor $d_o\mid |D|^{o-1}$) of the $\Delta$-twisted circulant $M$ be bounded
  from word structure alone, giving an a-priori ceiling on the gcd?
- **Does the twist matter?** $M$ and $C$ are conjugate over $\mathbb{R}$ but $\Delta$ is
  irrational. Is there an *integer* unimodular/equivalence relating $M$ to a genuinely integer
  circulant, so the rich circulant SNF theory applies directly? If not, what survives?
- **Spectral → integer bridge** — *answered* (see [`number_field.md`](number_field.md)): the
  integers are norms, $D=\pm N_{K/\mathbb Q}(\beta-3)$, $\det M=N_{K/\mathbb Q}(\hat c_0)$. Remaining:
  factor the ideal $(\beta-3)$ in the order $\mathbb Z[\beta]$ vs maximal order $\mathcal O_K$
  (conductor) and read $\gcd_j S^{(j)}$ as a sub-ideal index; does class-group/unit structure of
  $\mathbb Q(2^{1/o})$ beat the elementary $\gcd_j S^{(j)}\mid D$?
- **Restricted word classes.** For bounded-circuit words (where Steiner / Simons–de Weger
  already prove finiteness), does the matrix content bound become provable and match/beat theirs?

## Next step under consideration

**Per-prime exclusion (the sharp target).** The gcd law (§7) reframes the cycle conjecture
locally: a cycle needs *all* $o$ trace parts $T_j=\operatorname{Tr}(\gamma_W\beta^j/(\beta-3))$
integral, so excluding a cycle = exhibiting *one* prime $p\mid D$ and *one* rotation $j$ with
$v_p(T_j)\lt0$ (i.e. $v_p(S^{(j)})\lt v_p(D)$). Concretely: pick small $p\mid D$, study the trace
pole of $\eta_j=\gamma_W\beta^j/(\beta-3)$ at $\mathfrak p=(p,\beta-3)$, and tabulate over $(E,o)$
how many primes a word can keep integral across all rotations (generic = none; cycle = all) —
looking for an a-priori reason it can never be all.
