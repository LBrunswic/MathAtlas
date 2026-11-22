# The circuit case in the number field: from a field to an étale algebra

The number-field rewriting ([`number_field.md`](number_field.md), [`gamma_w.md`](gamma_w.md))
was developed under the standing assumption $\gcd(E,o)=1$, where $K=\mathbb Q(\beta)$,
$\beta=2^{E/o}$, is a genuine degree-$o$ field and $\{1,\beta,\dots,\beta^{o-1}\}$ is a basis.
The **circuit case** is $g:=\gcd(E,o)\gt1$. Classically $g$ is the number of circuits of the cycle;
in [`number_field.md`](number_field.md) §2 it was identified with the field-degree defect
$[\mathbb Q(2^{1/o}):K]$, since now $[K:\mathbb Q]=b:=o/g\lt o$. This note works out what actually
happens to the whole trace/gcd machinery when $g\gt1$ — and the answer is clean: **nothing was ever
about the field $K$; everything lives in the degree-$o$ étale algebra
$A:=\mathbb Q[x]/(x^o-2^E)$, which is a field exactly when $g=1$ and a product of $g$ circuits
otherwise.**

Notation as elsewhere: $o$ odd steps, $E=e_o$ total even steps, $D=2^E-3^o$ (odd, coprime to $6$),
$g=\gcd(E,o)$, $b=o/g$, $a=E/g$ (so $\gcd(a,b)=1$), $\beta=2^{E/o}=2^{a/b}$.

## 1. The right home is the étale algebra $A=\mathbb Q[x]/(x^o-2^E)$

The polynomial $x^o-2^E$ is **separable** ($\gcd$ with its derivative $ox^{o-1}$ is trivial since
$2^E\neq0$), so $A=\mathbb Q[x]/(x^o-2^E)$ is an **étale $\mathbb Q$-algebra** of dimension $o$.
The class of $x$ plays the role $\beta$ did; write $\hat x$ for it. Two facts make $A$ — not $K$ —
the correct object:

- **The power "basis" is genuinely a basis of $A$, always.** $\{1,\hat x,\dots,\hat x^{o-1}\}$ is a
  $\mathbb Q$-basis of $A$ for every $(E,o)$, whereas in $K$ (dimension $b$) it is over-determined
  once $g\gt1$ (the relation $\hat x^{\,b}=2^a$ collapses it). The word functional $L(\hat x^k)=2^{e_k}$
  is therefore well-defined on $A$ but **not** on $K$ when $g\gt1$ — a non-circuit-periodic word's
  weights $2^{e_k}$ need not respect $\hat x^{\,b}=2^a$. This is exactly why the field-only story
  needed $\gcd(E,o)=1$.

- **The trace on $A$ is computed by the same kernel.** For multiplication-by-$\hat x^{\,n}$ on $A$,
  the companion matrix gives
  $$\operatorname{Tr}_{A/\mathbb Q}(\hat x^{\,n})=\begin{cases}o\cdot 2^{E\cdot n/o}, & o\mid n,\\[2pt]0,&o\nmid n,\end{cases}$$
  **independently of whether $x^o-2^E$ is irreducible.** Every computation in
  [`gamma_w.md`](gamma_w.md) §2 (the universal kernel $\tau_k=\operatorname{Tr}(\hat x^{-k}/(\hat x-3))
  =o\,3^{o-1-k}/D$, hence $T_0=S^{(0)}/D$) used only this, so all of it transfers verbatim.

Consequently the entire frame holds over $A$ with $\operatorname{Tr}_{A/\mathbb Q}$ replacing
$\operatorname{Tr}_{K/\mathbb Q}$. Define in $A$
$$\hat c_0=\frac{D}{\hat x-3}=\sum_{k=0}^{o-1}3^{\,o-1-k}\hat x^{k},\qquad
\gamma_W=\frac1o\sum_{k=0}^{o-1}2^{e_k}\hat x^{-k},\qquad
T_j=\operatorname{Tr}_{A/\mathbb Q}\!\Big(\frac{\gamma_W\hat x^{j}}{\hat x-3}\Big).$$
($\hat x-3$ is a unit of $A$ because $3$ is not a root of $x^o-2^E$, i.e. $3^o\neq2^E$.)

**Verified (sympy, words with $g\gt1$):** $(E,o)=(6,4)$ [two words], $(12,4)$ [two words], $(6,3)$:
$$2^{e_j}S^{(j)}=\operatorname{Tr}_{A/\mathbb Q}\!\big(\gamma_W\hat x^{j}\hat c_0\big)
=D\cdot\operatorname{Tr}_{A/\mathbb Q}\!\Big(\frac{\gamma_W\hat x^{j}}{\hat x-3}\Big),\qquad
\det M=N_{A/\mathbb Q}(\hat c_0)=(-1)^{o+1}D^{\,o-1}.$$
So the trace identity (§6) and "det = algebra norm" (§3–4) are **circuit-independent**; they never
needed $A$ to be a field. The norm $N_{A/\mathbb Q}$ of an étale algebra is the product of the field
norms over its factors — which is precisely how the full $D^{o-1}$ reappears below, where the field
norm $N_{K/\mathbb Q}$ only gave a proper factor.

## 2. $A$ splits into circuits; $D$ factors accordingly

$A$ is a product of number fields, one per $\mathbb Q$-irreducible factor of $x^o-2^E$:
$$A\;\cong\;\prod_{i} K_i,\qquad K_i=\mathbb Q[x]/(f_i),\quad x^o-2^E=\prod_i f_i.$$
$A$ is a field $\iff x^o-2^E$ is irreducible $\iff g=1$, recovering $A=K$. When $g\gt1$ the splitting
is governed by the circuit factorization of $D$. Over $\mathbb Q(\zeta_g)$, with $\hat x^{\,b}=2^a$,
$$x^o-2^E=\prod_{m=0}^{g-1}\big(x^{b}-2^a\zeta_g^m\big),\qquad
\boxed{\,D=2^E-3^o=\prod_{m=0}^{g-1}\big(2^a-3^b\zeta_g^m\big)\,}$$
(both from $u^g-v^g=\prod_m(u-v\zeta_g^m)$). The $g$ factors $2^a-3^b\zeta_g^m$ are the **$g$
circuits**. Over $\mathbb Q$ they regroup by Galois conjugacy into the $r\le g$ factor fields $K_i$;
the principal one is the real circuit $K_0=\mathbb Q(2^{1/b})=K$ with $f_0=x^b-2^a$ and
$$N_{K/\mathbb Q}(\beta-3)=(-1)^{b}\big(3^{b}-2^{a}\big)=\pm(2^a-3^b)\quad(\text{the }m=0\text{ circuit}),$$
the proper factor of $D$ already seen in [`number_field.md`](number_field.md) §2. The other circuits
live in the conjugate factor fields and carry the rest of $D$:
$$\det M=N_{A/\mathbb Q}(\hat c_0)=\prod_i N_{K_i/\mathbb Q}\!\big(\hat c_0^{(i)}\big)=\pm D^{o-1},
\qquad D=\prod_i \pm N_{K_i/\mathbb Q}(\beta_i-3),\ \ \beta_i=\text{root of }f_i.$$

**Worked examples (verified).**

- **$(E,o)=(6,4)$, $g=2$, $b=2$, $a=3$, $D=-17$.** $x^4-64=(x^2-8)(x^2+8)$, so
  $A=\mathbb Q(\sqrt2)\times\mathbb Q(\sqrt{-2})$. Circuits: $2^3-3^2\zeta_2^m=\{-1,\,17\}$. The
  **principal real circuit** $\mathbb Q(\sqrt2)$ has $N(\beta-3)=N(2\sqrt2-3)=1$ — a **unit**, it
  sees none of $D$. The entire prime $17$ lives in the conjugate circuit $\mathbb Q(\sqrt{-2})$:
  $N(2\sqrt{-2}-3)=9+8=17$. This is the structural reason the field norm "lost" $D$ in the
  $g\gt1$ examples of §2: the content moved to a non-real circuit.

- **$(E,o)=(12,4)$, $g=4$, $b=1$, $a=3$, $D=4015=5\cdot11\cdot73$.** $\beta=2^{3}=8$ is rational,
  $K=\mathbb Q$. $x^4-4096=(x-8)(x+8)(x^2+64)$, so $A=\mathbb Q\times\mathbb Q\times\mathbb Q(8i)$.
  Circuits $8-3i^m=\{5,\,8-3i,\,11,\,8+3i\}$ regroup over $\mathbb Q$ as $5$, $11$, and
  $(8-3i)(8+3i)=73$. Norms: $\beta-3=5$ (circuit $x-8$), $-8-3=-11$ (circuit $x+8$),
  $N_{\mathbb Q(i)}(8i-3)=73$ (circuit $x^2+64$). One prime of $D$ per circuit field.

## 3. What this buys the gcd / per-prime program

The §7 per-prime law ($\gcd_jS^{(j)}=|D|/\operatorname{lcm}_j\delta_j$; each prime $p\mid D$
independently kept or shed) survives intact — its proof (rotation recursion
$2^{d_k}S^{(k+1)}=3S^{(k)}+D$ over $\mathbb Z$, [`gamma_w.md`](gamma_w.md) §0) is word-level and
never used $g=1$. So the rotation collapse $\gcd_jS^{(j)}=\gcd(S^{(0)},D)$ holds in the circuit
case too. The circuit decomposition **refines** the law geometrically.

Because $\operatorname{Tr}_{A/\mathbb Q}=\sum_i\operatorname{Tr}_{K_i/\mathbb Q}$, the trace part
splits over circuits,
$$T_0=\operatorname{Tr}_{A/\mathbb Q}\!\Big(\frac{\gamma_W}{\hat x-3}\Big)
=\sum_i\,\underbrace{\operatorname{Tr}_{K_i/\mathbb Q}\!\Big(\frac{\gamma_W^{(i)}}{\beta_i-3}\Big)}_{=:T_0^{(i)}},$$
and each rational prime $p\mid D$ divides $N_{K_i/\mathbb Q}(\beta_i-3)$ for **exactly one** circuit
field $K_i$ (the one whose circuit factor it divides; the degree-one prime $(p,\beta-3)$ sits over
that $K_i$). The local analysis of [`gamma_w.md`](gamma_w.md) §3 — $\hat c_0$ a $\mathfrak p$-unit,
$p$ shed $\iff v_p(\gamma_W(\beta_{\mathfrak p}))\lt v_p(D)$ — therefore takes place **entirely inside
that single circuit field**, of degree $\le b=o/g$ rather than $o$.

**Verified (sympy).** $(12,4)$: the three circuit contributions to $T_0=397/4015$ have denominators
$80=16\cdot5$, $176=16\cdot11$, $292=4\cdot73$ — i.e. each prime $5,11,73$ appears in the
denominator of exactly its own circuit's trace contribution. All three shed $\Rightarrow\gcd=1$.
$(6,4)$: $\mathbb Q(\sqrt2)$ contributes the integer $-5$ ($N=$ unit, no pole), while the
$17$-circuit $\mathbb Q(\sqrt{-2})$ contributes $0$ (integral, $17$ **kept**) $\Rightarrow\gcd=17=|D|$.
$(6,3)$: $D=37$ lives in the degree-2 circuit $x^2+4x+16$, contribution $0$ (kept) $\Rightarrow\gcd=37$.

**Sharpened cycle target.** A cycle needs every prime of $D$ kept, i.e. **every circuit field must
keep its prime(s) integral simultaneously**. Per-prime exclusion (the parent's sharp target) now
reads: exhibit one circuit $K_i$ and one prime $p\mid N_{K_i/\mathbb Q}(\beta_i-3)$ with
$v_p(T_0^{(i)})\lt0$. The question is localized twice over — to a single prime and to a single
low-degree circuit field — at the cost that a multi-circuit word distributes its primes across
several fields, so a cycle imposes one integrality constraint per circuit rather than one global one.

## 4. Status / open

- **Verified / clean.** Trace identity, $\gamma_W$ closed form, universal kernel, $\det M=$ norm,
  rotation collapse, and the per-prime gcd law all hold in the étale algebra $A$ verbatim for $g\gt1$
  (sympy: $(6,4),(12,4),(6,3)$). $A$ is a field iff $g=1$; otherwise $A=\prod_iK_i$ with the circuit
  factorization $D=\prod_m(2^a-3^b\zeta_g^m)$, the principal real circuit $K=\mathbb Q(2^{1/b})$
  contributing $N_{K/\mathbb Q}(\beta-3)=\pm(2^a-3^b)$. Each prime $p\mid D$ localizes to exactly one
  circuit field, where its keep/shed verdict is decided.
- **Open.**
  1. **Does the circuit split help or just bookkeep?** A cycle now needs $r$ simultaneous integrality
     conditions (one per circuit field) instead of one — does the requirement that *all* circuits keep
     their primes give an a-priori obstruction (e.g. a real circuit forced to be a unit, as in
     $(6,4)$, while a conjugate circuit must keep a large prime)?
  2. **Ramification / edge cases.** $b=1$ (all circuits rational or quadratic, $\beta\in\mathbb Q$,
     e.g. $(12,4)$), and primes $p\mid g$ or $p\mid o$ (ramified, excluded in
     [`gamma_w.md`](gamma_w.md) §3) need separate treatment.
  3. **Link to bounded-circuit finiteness.** Steiner / Simons–de Weger prove no nontrivial cycles
     with few circuits. Here "few circuits" = small $g$ = $A$ close to a single field. Does the
     low-degree circuit-field localization make their finiteness reproducible as an integrality
     statement on one $K_i$?
