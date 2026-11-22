# Studying the trace via the word element $\gamma_W$

This note studies the trace parts $T_j=\operatorname{Tr}_{K/\mathbb Q}\!\big(\tfrac{\gamma_W\beta^j}{\beta-3}\big)$
whose denominators $\delta_j$ control the gcd ($\gcd_jS^{(j)}=|D|/\operatorname{lcm}_j\delta_j$, see
[`number_field.md`](number_field.md) §7). Notation: $K=\mathbb Q(\beta)$, $\beta=2^{E/o}$,
$\beta^o=2^E$; $\hat c_0=\tfrac{D}{\beta-3}=\sum_{k=0}^{o-1}3^{o-1-k}\beta^k\in\mathbb Z[\beta]$;
$D=2^E-3^o$ is coprime to $6$ (any prime $p\mid D$ has $p\ge5$).

## 0. The reduction: only $\gamma_W$ matters, not $\beta^j$

(Léo) The factors $\beta^j$ carry no prime content relevant to $D$: $\beta^o=2^E$ is a power of
$2$, coprime to the odd $D$, so $\beta$ is a **$p$-adic unit at every prime $p\mid D$**.
Multiplying by $\beta^j$ cannot move $p$-content. Hence all the trace parts $T_0,\dots,T_{o-1}$
have the **same denominator**, and the gcd is decided by $\gamma_W$ alone.

This is a theorem, with two independent proofs:

- **Elementary (rotation recursion).** The parent identity $2^{d_k}S^{(k+1)}=3S^{(k)}+D$ holds over
  $\mathbb Z$. Fix $p\mid D$ ($p\ge5$, so $2,3$ are units mod $p$) and let $m=v_p(D)$. If some
  $v_p(S^{(k)})\lt m$, then $v_p(3S^{(k)})\lt m=v_p(D)$ forces $v_p(2^{d_k}S^{(k+1)})=v_p(S^{(k)})$,
  i.e. $v_p(S^{(k+1)})=v_p(S^{(k)})$; propagating around the cycle, **all $v_p(S^{(j)})$ are equal**.
  (If instead all $v_p(S^{(j)})\ge m$, $p$ contributes fully and is again uniform.) So
  $\delta_j=|D|/\gcd(S^{(j)},D)$ is independent of $j$.
- **Field-theoretic.** $(\beta)$ is coprime to every $\mathfrak p\mid p$ (its norm is a power of
  $2$), so $\beta^j$ is a unit in each completion $K_{\mathfrak p}$; the $\mathfrak p$-adic valuation
  of $\tfrac{\gamma_W\beta^j}{\beta-3}$ does not depend on $j$.

**Consequence (verified on 3000+ words).** The whole rotation structure collapses:
$$\boxed{\;\gcd_{j}S^{(j)}=\gcd\big(S^{(0)},\,D\big)=\frac{|D|}{\delta},\qquad
\delta:=\text{denominator of }T_0=\operatorname{Tr}_{K/\mathbb Q}\!\Big(\frac{\gamma_W}{\beta-3}\Big).\;}$$
There is only **one** trace to understand: $T_0$. Everything is now about the single element $\gamma_W$.

## 1. Closed form of $\gamma_W$

$\gamma_W$ is the trace-dual combination of the power basis with the word weights. The trace-dual
basis of $\{1,\beta,\dots,\beta^{o-1}\}$ for $f(X)=X^o-2^E$ is $\beta_k^\ast=\tfrac1o\beta^{-k}$
(from $f(X)/(X-\beta)=\sum_k\beta^{o-1-k}X^k$ and $f'(\beta)=o\beta^{o-1}$). Since $L(\beta^k)=2^{e_k}$,
$$\boxed{\;\gamma_W=\frac1o\sum_{k=0}^{o-1}2^{e_k}\,\beta^{-k}
=\frac1{o\,2^{E}}\sum_{k=0}^{o-1}2^{e_k}\,\beta^{\,o-k}\;}$$
(verified: $(7,4)\!\to\!\tfrac14+\tfrac1{16}\beta+\tfrac1{64}\beta^2+\tfrac1{128}\beta^3$). Its
denominator is $o\cdot 2^{\bullet}$ — i.e. $\gamma_W\in\mathfrak d_K^{-1}$, the **codifferent**
(the different of $\mathbb Q(2^{1/o})$ divides $o\,2^{\bullet}$). Both $o$ and $2$ are structural;
they are *not* the primes that matter for $\delta$, which divides $D$.

## 2. The universal trace kernel, and where the word enters

Expand $T_0$ against the word weights. The kernel
$\tau_k:=\operatorname{Tr}_{K/\mathbb Q}\!\big(\tfrac{\beta^{-k}}{\beta-3}\big)$ is **word-independent**
(depends only on $E,o$), and computes cleanly: since $\tfrac1{\beta-3}=\tfrac{\hat c_0}{D}$ and
$\operatorname{Tr}(\beta^{m-k})=o\,\delta_{mk}$ on $0\le m\lt o$,
$$\tau_k=\frac{o\cdot 3^{\,o-1-k}}{D}\qquad(\text{verified}).$$
Therefore
$$T_0=\operatorname{Tr}\!\Big(\frac{\gamma_W}{\beta-3}\Big)=\frac1o\sum_k 2^{e_k}\tau_k
=\frac1D\sum_{k=0}^{o-1}2^{e_k}3^{\,o-1-k}=\frac{S^{(0)}}{D}.$$
So the word enters **only** through the weights $2^{e_k}$ paired against the universal kernel
$3^{o-1-k}$, and $T_0=S^{(0)}/D$ — consistent with §0, and isolating the role of $\gamma_W$ as
"the word's coordinates against a fixed geometric kernel."

## 3. Local picture at a prime $p\mid D$

Fix $p\mid D$, $m=v_p(D)$, and assume $p\nmid o$ (so $3$ is a simple root of $X^o-2^E\bmod p$;
the $p\mid o$ case is ramified — see open questions). Then:

- There is a unique **degree-one prime** $\mathfrak p=(p,\beta-3)$ above $p$ with $\beta\equiv3$;
  at all other $\mathfrak q\mid p$, $\beta\not\equiv3$ so $\beta-3$ is a $\mathfrak q$-unit.
- $v_{\mathfrak p}(\beta-3)=m$ (it carries all of $v_p(N(\beta-3))=m$), hence
  $$v_{\mathfrak p}(\hat c_0)=v_{\mathfrak p}(D)-v_{\mathfrak p}(\beta-3)=0:\quad
  \hat c_0=\tfrac{D}{\beta-3}\text{ is a }\mathfrak p\text{-unit, and }\equiv\!\!\!\pmod{\mathfrak q}0
  \text{ at the other }\mathfrak q\mid p.$$
- The completion $K_{\mathfrak p}=\mathbb Q_p$, with $\beta\mapsto\beta_{\mathfrak p}\in\mathbb Z_p$
  the Hensel lift of $3$ ($\beta_{\mathfrak p}\equiv3\bmod p$, $\beta_{\mathfrak p}^o=2^E$). Modulo
  $p^m$ the trace collapses to the $\mathfrak p$-term (the others vanish to order $\ge m$):
  $$\operatorname{Tr}(\gamma_W\hat c_0)\equiv \gamma_W(\beta_{\mathfrak p})\,\hat c_0(\beta_{\mathfrak p})\pmod{p^m},
  \qquad \hat c_0(\beta_{\mathfrak p})\in\mathbb Z_p^\times.$$

**Conclusion.** $p$ is shed from the gcd $\iff v_p(T_0)\lt0\iff
v_p\!\big(\gamma_W(\beta_{\mathfrak p})\big)\lt m$. So at each prime the entire question is the
$p$-adic size of the **single number** $\gamma_W(\beta_{\mathfrak p})$ — the word element evaluated
at the $p$-adic root $\beta_{\mathfrak p}\equiv3$:
$$\gamma_W(\beta_{\mathfrak p})=\frac1o\sum_{k=0}^{o-1}2^{e_k}\,\beta_{\mathfrak p}^{-k},
\qquad \gamma_W(\beta_{\mathfrak p})\equiv\frac{S^{(0)}}{o\,3^{o-1}}\pmod p .$$

## 4. Honest status and open questions

- **What is genuinely new here:** (i) the rotation collapse $\gcd_jS^{(j)}=\gcd(S^{(0)},D)$, reducing
  $o$ rotation sums to one; (ii) the closed form $\gamma_W=\tfrac1o\sum_k2^{e_k}\beta^{-k}$ in the
  codifferent; (iii) the localization of all $D$-content to the single value
  $\gamma_W(\beta_{\mathfrak p})$ at the degree-one prime $\mathfrak p=(p,\beta-3)$, where $\hat c_0$
  is a unit.
- **Circularity warning (inherited from cycle-gcd).** Mod $p$, $\gamma_W(\beta_{\mathfrak p})\equiv
  S^{(0)}/(o\,3^{o-1})$, so the leading $p$-adic digit just re-encodes $S^{(0)}\bmod p$. New leverage,
  if any, must come from the **higher $p$-adic digits** of $\beta_{\mathfrak p}=3+p(\cdots)$ for
  $m=v_p(D)\gt1$, i.e. from how the Hensel lift of $3$ deviates from $3$ — this is where the field
  structure could add information the bare integer $S^{(0)}$ does not display.
- **Open:** (i) Express $v_p(\gamma_W(\beta_{\mathfrak p}))$ for $m\ge2$ via the $p$-adic expansion
  of $\beta_{\mathfrak p}$ and the word weights — does any word keep $v_p\ge m$ for *all* $p\mid D$
  at once (the cycle requirement)? (ii) The ramified case $p\mid o$. (iii) Whether viewing $\gamma_W$
  as a codifferent element gives a different/discriminant bound on how many primes can be kept.
