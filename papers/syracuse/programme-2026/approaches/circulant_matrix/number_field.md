# The number-field rewriting: $D$ is a norm, $M$ is a regular representation

Observation (Léo): $\det M=\pm D^{o-1}$ looks like the **norm of an algebraic integer**, and the
whole circulant framework should be expressible as algebraic relations in a number field. This is
correct. This note makes it precise, flags the one subtlety ($\gcd(E,o)$), and states what the
reframing buys for the [`cycle-gcd`](../cycle-gcd/STATUS.md) gcd program.

## 1. The field

Let $\beta:=2^{E/o}=t$, a root of $X^o-2^E$, and
$$K:=\mathbb Q(\beta)=\mathbb Q\big(2^{E/o}\big).$$
With $g:=\gcd(E,o)$ and $E/o=a/b$ in lowest terms ($b=o/g,\ a=E/g$), the minimal polynomial of
$\beta$ is $X^{b}-2^{a}$, so $[K:\mathbb Q]=b=o/g$ and $K=\mathbb Q(2^{1/b})$ — a **real radical
(Kummer-type) field**. Its $\mathbb C$-conjugates are $\beta\zeta_b^{k}$, $\zeta_b=e^{2\pi i/b}$.

## 2. $D$ as a norm of $\beta-3$


The determinant computation (1b in [`factorization.md`](factorization.md)) *is* a norm:
$$N_{K/\mathbb Q}(\,\beta-3\,)=\prod_{k=0}^{b-1}\big(\beta\zeta_b^{k}-3\big)=(-1)^{b}\big(3^{b}-2^{a}\big).$$

- **Coprime case $\gcd(E,o)=1$** (so $b=o$): $\;\big|N_{K/\mathbb Q}(\beta-3)\big|=\big|3^{o}-2^{E}\big|=|D|$.
  So $\boxed{\,D=\pm\,N_{K/\mathbb Q}(2^{E/o}-3)\,}$ — $D$ is literally the field norm of the algebraic
  integer $\beta-3$. (Verified: $(E,o)=(8,5)\!\to\!13$, $(7,4)\!\to\!47$, $(5,3)\!\to\!5$,
  $(19,12)\!\to\!7153=23\cdot311$.)
- **General case $g\gt 1$:** $N_{K/\mathbb Q}(\beta-3)=\pm(3^{o/g}-2^{E/g})$ is a **proper factor** of
  $D$, and $D=2^E-3^o=(2^{E/g})^{g}-(3^{o/g})^{g}$ is the corresponding orbit product
  $\prod_{\text{$g$ Galois orbits}}$. E.g. $(12,4)$: $N=5$ but $D=5\cdot11\cdot73$; $(6,4)$:
  $\beta-3=2\sqrt2-3$ is a **unit** of $\mathbb Q(\sqrt2)$ ($N=1$) while $D=-17$.

So $g=\gcd(E,o)$ — classically the **number of circuits** of the cycle — is exactly the degree
defect $[\,\mathbb Q(2^{1/o}):K\,]$: $g=1$ is the irreducible / single-orbit case where $D$ is a
clean norm; $g\gt 1$ splits $X^o-2^E$ and factors $D$ further. This pins the Steiner / Simons–de Weger
"bounded circuits" hierarchy to field-degree structure.

## 3. Eigenvalues = a Galois orbit; $\det M$ = a norm

The eigenvalues $\hat c_\ell=\dfrac{D}{\beta\omega^\ell-3}$ ($\omega=e^{2\pi i/o}$) are the
conjugates of
$$\hat c_0=\frac{D}{\beta-3}=\pm\!\!\prod_{\ell\neq 0}\!\big(\beta\omega^\ell-3\big)
\;=\;\pm\,\frac{N_{K/\mathbb Q}(\beta-3)}{\beta-3}\quad(\gcd(E,o)=1).$$
This $\hat c_0$ is an **algebraic integer in $K$** (a product of the algebraic integers
$\beta\omega^\ell-3$, and it lies in $K$ because $\hat c_0=D\cdot(\beta-3)^{-1}$). Its norm is the
determinant:
$$\det M=\det C=N_{K/\mathbb Q}(\hat c_0)=N_{K/\mathbb Q}\!\Big(\tfrac{D}{\beta-3}\Big)
=\frac{D^{o}}{N(\beta-3)}=\pm\,D^{\,o-1}.$$
**The "$o-1$" is not mysterious:** $\det M=N(\hat c_0)$ and $\hat c_0\cdot(\beta-3)=\pm D$, so
$N(\hat c_0)\cdot N(\beta-3)=(\pm D)^{o}\Rightarrow N(\hat c_0)=\pm D^{o-1}$.

## 4. The circulant *is* a regular representation

A circulant of size $o$ is an element of the group algebra
$\mathbb C[\mathbb Z/o]\cong\mathbb C[x]/(x^{o}-1)$, acting by multiplication. Our $C$ corresponds to
$$\xi:=3^{\,o-1}\sum_{r=0}^{o-1}\rho^{r}x^{r}\ \bmod (x^{o}-1),\qquad \rho=\beta/3,$$
i.e. $C$ is **multiplication by $\xi$** in the regular representation; under $x\mapsto\omega^\ell$ the
value is the eigenvalue $\hat c_\ell$, and $\xi$ at $x=\omega^\ell$ equals $\hat c_\ell=D/(\beta\omega^\ell-3)$.
In this language:
- $\det C=\det(\text{mult by }\xi)=\mathrm{Nm}(\xi)$ — determinant = algebra norm, *automatically*.
- **Word-independence (Identity B)** is the statement that a norm is **basis-independent**: the twist
  $M=\Delta^{-1}C\Delta$ is a change of basis, which cannot change $\mathrm{Nm}$. The word lives only
  in the *basis* $\Delta$, never in the norm.

## 5. What this buys for the gcd program

The open core of cycle-gcd — an a-priori bound on $\gcd_j S^{(j)}$ — becomes a question about an
**ideal in the order $\mathbb Z[\beta]\subseteq\mathcal O_K$**:

- **Primes of $D$ ↔ degree-one primes over $(\beta-3)$.** A rational prime $p\mid D=\pm N(\beta-3)$
  means $3^o\equiv2^E\pmod p$, i.e. $3$ is a root of $X^o-2^E\bmod p$, i.e. $(X-3)\mid(X^o-2^E)\bmod p$.
  By Kummer–Dedekind this is exactly a degree-one prime $\mathfrak p=(p,\ \beta-3)$ dividing the
  principal ideal $(\beta-3)$. So the factorization of $|D|$ into rational primes mirrors the
  factorization of the ideal $(\beta-3)$ in $\mathbb Z[\beta]$.

- **The gcd is an ideal-content statement.** Each $S^{(j)}=D\,\theta_j$ with $\theta_j\in\mathbb Q$
  (the [`Fourier formula`](factorization.md), §"eigenvalues vs divisibility"), and on a genuine cycle
  $\gcd_j S^{(j)}=|D|$ — the full norm. Off-cycle, $\gcd_j S^{(j)}=|D|/N$ selects a **sub-ideal** of
  $(\beta-3)$: $N$ measures how much the rotation data fails to be divisible by the whole of
  $(\beta-3)$. Bounding $\gcd_j S^{(j)}$ a priori = bounding which sub-ideal the word can realize.

- **Lower bounds on $|D|$ = norm-form lower bounds.** $|D|=|N_{K/\mathbb Q}(\beta-3)|$ is a value of
  the **norm form** of $K=\mathbb Q(2^{1/o})$ at the integer point $\beta-3$. "Why is $|2^E-3^o|$
  large?" becomes "why is this norm form large?" — governed by the units and regulator of the radical
  field $\mathbb Q(2^{1/o})$ (the unit example $(6,4)$ shows where it can collapse). This is the same
  Baker barrier as before, now packaged as the arithmetic of one explicit family of fields.

## 6. The rotation sums $S^{(j)}$ as traces in $K$

The $S^{(j)}$ do have a clean field expression — they are **traces**. Start from the explicit form
of the eigenvalue/algebraic integer (a geometric sum, $\sum_k 3^{o-1-k}\beta^k=\tfrac{3^o-\beta^o}{3-\beta}$):
$$\hat c_0=\frac{D}{\beta-3}=\sum_{k=0}^{o-1}3^{\,o-1-k}\,\beta^{k}\ \in\ \mathbb Z[\beta].$$

**(a) Each rotation sum is "$\hat c_0$ with the uniform word replaced by the actual word."**
Compare term-by-term:
$$\hat c_0=\sum_{k}3^{\,o-1-k}\,\beta^{k},\qquad S^{(0)}=\sum_{k}3^{\,o-1-k}\,2^{e_k}.$$
$\hat c_0$ is the **uniform-word** element ($\beta^k=2^{kE/o}$); $S^{(0)}$ is obtained by the
substitution $\beta^{k}\mapsto 2^{e_k}$, i.e. replacing the average exponent $kE/o$ by the true
exponent $e_k$. The word's deviation $\tilde e_k=e_k-kE/o$ is exactly this deformation.

**(b) The word is a $\mathbb Q$-linear functional; the rotations are its values on the orbit
$\beta^j\hat c_0$.** When $\gcd(E,o)=1$, $\{1,\beta,\dots,\beta^{o-1}\}$ is a $\mathbb Q$-basis of $K$.
Define the **word functional** $L:K\to\mathbb Q$ by $L(\beta^k)=2^{e_k}$. Then (verified exactly on
$(8,5),(7,4),(3,2)$):
$$\boxed{\;2^{e_j}\,S^{(j)}=L\!\big(\beta^{j}\,\hat c_0\big)=D\cdot L\!\Big(\frac{\beta^{j}}{\beta-3}\Big)\;}$$
(the reduction of $\beta^{j}\hat c_0$ in the power basis mod $\beta^{o}=2^{E}$ produces precisely the
wrap factors $2^{E}\mathbf 1[i\lt j]$). The factor $D$ out front re-derives $D\mid 2^{e_j}S^{(j)}$.

**(c) Hence the rotation sums are traces.** The trace form of a separable extension is
nondegenerate, so $L=\operatorname{Tr}_{K/\mathbb Q}(\gamma_W\,\cdot\,)$ for a unique
$\gamma_W\in K$ (the "word element"), giving
$$2^{e_j}S^{(j)}=\operatorname{Tr}_{K/\mathbb Q}\!\big(\gamma_W\,\beta^{j}\,\hat c_0\big)
=D\cdot\operatorname{Tr}_{K/\mathbb Q}\!\Big(\frac{\gamma_W\,\beta^{j}}{\beta-3}\Big).$$
Verified: for $(7,4)$, $\gamma_W=\tfrac14+\tfrac1{16}\beta+\tfrac1{64}\beta^2+\tfrac1{128}\beta^3$;
for $(8,5)$, $\gamma_W=\tfrac15+\tfrac1{40}\beta+\dots$. The denominators are $o\cdot(\text{powers of }2)$
— i.e. $\gamma_W$ lives in the **codifferent** $\mathfrak d_K^{-1}$ (the different of $\mathbb Q(2^{1/o})$
divides $o\,2^{\bullet}$), exactly the object that governs which traces are integral.

**(d) Caveat / what the gcd sees.** The clean trace identity carries the rescaling
$\bar S^{(j)}:=2^{e_j}S^{(j)}$. Since $D=2^E-3^o$ is **odd** and $\gcd_jS^{(j)}\mid D$, the power-of-2
factors are invisible to the gcd we care about: localizing away from $2$ (work in $\mathbb Z[\tfrac12]$
or take odd parts), $\gcd_jS^{(j)}=\text{odd part of }\gcd_j\operatorname{Tr}(\gamma_W\beta^j\hat c_0)$.
So **the gcd of the rotation sums is the content of the traces of the $\mathbb Z[\beta]$-orbit
$\{\beta^j\hat c_0\}$ against the codifferent element $\gamma_W$** — a different/codifferent
divisibility question, with $\hat c_0=D/(\beta-3)$ making the $D$ explicit.

## 7. The gcd, prime by prime: shedding trace-denominator primes

(Léo) The gcd question is exactly **which primes survive in the denominators of the trace parts** —
and any prime that appears there forces $\gcd_j S^{(j)}\lt|D|$. This is now a precise, verified law.

Define the **trace parts** $\;T_j:=\operatorname{Tr}_{K/\mathbb Q}\!\big(\tfrac{\gamma_W\beta^j}{\beta-3}\big)
=\dfrac{2^{e_j}S^{(j)}}{D}\in\mathbb Q\;$ and let $\delta_j$ be the denominator of $T_j$ in lowest
terms. Because $D$ is odd, $\delta_j=|D|/\gcd(S^{(j)},D)$ (the $2^{e_j}$ is invisible).

**Master identity** (verified on 2005 words, structured + random):
$$\boxed{\;\gcd_{j}S^{(j)}=\frac{|D|}{\operatorname{lcm}_{j}\,\delta_j}\;}$$
So $N:=D/\gcd_jS^{(j)}=\operatorname{lcm}_j\delta_j$ is precisely the lcm of the trace-part
denominators.

**Per-prime law.** For each prime $p\mid D$,
$$v_p\big(\gcd_jS^{(j)}\big)=\min_j v_p\big(S^{(j)}\big)\ \le\ v_p(D),$$
and $p$ divides some trace denominator $\delta_j$ $\iff v_p(S^{(j)})\lt v_p(D)$ for that $j$. Hence
**each prime of $D$ is independently either kept in the gcd (all $o$ trace parts $p$-integral) or
shed (some trace part has $p$ in its denominator).** This is the content of Léo's observation:
*any* prime entering *any* trace denominator drops the gcd below $|D|$ by exactly its valuation
deficit. Worked example $(3,3)$, $D=55=5\cdot11$: trace denominators $\delta_j=5$, so $5$ is shed
and $11$ is kept $\Rightarrow\gcd_jS^{(j)}=11=|D|/5$. ($(4,4)$: $D=247=13\cdot19$, $13$ shed, $19$
kept $\Rightarrow 19$. $(2,4,3)$: $D=485=5\cdot97$, $97$ shed, $5$ kept $\Rightarrow 5$.)

**Cycle condition, restated.** A genuine cycle needs $\gcd_jS^{(j)}=|D|$, i.e.
$$\text{all }o\text{ trace parts }T_0,\dots,T_{o-1}\text{ are integers}\quad(\text{no prime in any denominator}).$$
Equivalently the **3x+1 cycle conjecture** (no nontrivial cycle) becomes: *for every nontrivial
admissible word, at least one trace part $T_j$ is non-integral* — some prime $p\mid D$ with
$v_p(T_j)\lt0$, i.e. $v_p(S^{(j)})\lt v_p(D)$.

**Why this is the right target.** It converts the global, transcendence-flavored "lower-bound
$|D|$" into a **local, per-prime** task: to kill a candidate cycle it suffices to exhibit *one*
prime $p\mid D$ and *one* rotation $j$ with $v_p(T_j)\lt0$. Locally, $T_j=\operatorname{Tr}(\eta_j)$,
$\eta_j=\gamma_W\beta^j/(\beta-3)$ has a pole along the degree-one prime $\mathfrak p=(p,\beta-3)$
above $p$ (where $\beta\equiv3$); $p$-integrality is whether the trace cancels that pole. So the
open problem is now: **bound, a priori, how many primes $p\mid D$ the word can keep $p$-integral
across all $o$ rotations simultaneously.** Generically (2005-case scan) words keep *none*
($\gcd=1$); a cycle must keep *all*.

## 8. Status / open

- **Proved/clean:** $D=\pm N_{K/\mathbb Q}(\beta-3)$ for $\gcd(E,o)=1$; $\det M=N_{K/\mathbb Q}(\hat c_0)
  =\pm D^{o-1}$; circulant = regular representation, word-independence = norm invariance; $g=\gcd(E,o)$
  = field-degree defect = circuit count. **Rotation sums are traces:** $2^{e_j}S^{(j)}
  =\operatorname{Tr}_{K/\mathbb Q}(\gamma_W\beta^j\hat c_0)$, $\hat c_0=\sum_k3^{o-1-k}\beta^k=D/(\beta-3)$,
  $\gamma_W$ the word element in the codifferent (§6, verified $(8,5),(7,4),(3,2)$). **gcd law (§7):**
  $\gcd_jS^{(j)}=|D|/\operatorname{lcm}_j\delta_j$, $\delta_j=$ denominator of the trace part
  $T_j=\operatorname{Tr}(\gamma_W\beta^j/(\beta-3))$; per prime, $p$ is shed from the gcd iff
  $v_p(S^{(j)})\lt v_p(D)$ for some $j$; cycle $\iff$ all $T_j$ integral (verified 2005 words).
- **Open / next:** (i) **per-prime exclusion** — for a candidate $(E,o)$, find one prime $p\mid D$ and
  rotation $j$ forcing $v_p(T_j)\lt0$ a priori; this is the local target replacing the global $|D|$
  bound. (ii) Bound how many primes of $D$ a word can keep integral across all $o$ rotations at once
  (generic = none; cycle = all). (iii) factor the ideal $(\beta-3)$ in $\mathbb Z[\beta]$ vs
  $\mathcal O_K$ (conductor) and read the pole-cancellation of $\eta_j=\gamma_W\beta^j/(\beta-3)$ at
  $\mathfrak p=(p,\beta-3)$; (iv) does class-group/unit structure of $\mathbb Q(2^{1/o})$ give the
  a-priori ceiling?
