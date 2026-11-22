# Two-ended extraction (generalizing the Gen-5 "last combination")

**Promise:** medium — a real, clarifying generalization of the Gen-5 reversal-symmetric P1, but
an **honest negative** against the headline hope: it does **not** tame $\ge2$ simultaneously growing
runs. Its value is that it **sharpens** the bounded-defect-lever no-go to an *exact, Zsygmondy-provable*
picture for the canonical family and pins the obstruction cleanly ("no free lunch": the move converts
the 2-run problem back into bounding a lone run's defect $2^L-3^L$).
**Status:** **RESOLVED (Gen 8) — the two-ended / reversal thread is CLOSED, negative.** The engine
(the two-ended identity) is **proven**; the multi-defect reversal core $S(d^{a+1})K_r$ and its sharp
validity gap are **proven** (Gen 7). **Gen 8 settles the last live question — the validity-gap bridge —
negatively:** the reversal sum $S(W^R)$ (equivalently the clean core $S(W)-S(W^R)$) **genuinely escapes
the rotation lattice** $L=\operatorname{span}\{S^{(j)}(W)\}$ — both the scalar lattice and the looser
Laurent-monomial "valid-combination" lattice — for every genuine 2-defect word; the escaping remainder
is **uncontrollable** (it carries the *entire* divergence — the lattice cancels none of the core's
degree); and even a hypothetical bridge would be **useless** because the core *diverges* (a valid combo
equal to a divergent core gives only the vacuous ceiling $G\le(\text{diverging})$). The structural
reason is exact: **reversal $=$ transpose is not a fixed conjugation**, whereas rotation $=$ conjugation
(structure.md C3), so **no $a$-uniform linear operator** carries the rotation orbit onto $S(W^R)$. Not a
new exclusion lever; not promotion-ready. The $G$-valid no-go for the symmetric family is **untouched**
by this route and remains the open problem of [`approaches/bounded-defect-lever`](../../approaches/bounded-defect-lever/RATIONALE.md).
**Last iterated:** 2026-06-08 (Gen 8)

## The move (one crisp claim)

The Gen-5 normalized P1 exhibits the inner-core combination as a **prefix (left) extraction plus a
suffix (right) extraction at once** ($\hat S=S/\chi$):
$$\frac{\chi(x')S(xuy)-\chi(x)S(x'uy')}{\chi(x)\chi(x')}=\underbrace{[\hat S(x)-\hat S(x')]}_{\text{suffix}}+\underbrace{[S(uy)-S(uy')]}_{\text{prefix-shared }u}.$$
The **two-ended** generalization shares a prefix frame $P$ **and** a suffix frame $Q$ simultaneously
and varies a middle $M\to M'$ (a permutation, $\chi(M)=\chi(M')$). The dual shared-frame identity gives
$$S(PMQ)-S(PM'Q)=X^{|P|}Y^{\operatorname{len}Q}\,\bigl(S(M)-S(M')\bigr),$$
extracting **both** runs $P,Q$ as the single unit $X^{|P|}Y^{\operatorname{len}Q}$. The headline test:
does this leave a **run-independent** core when $P,Q$ are the long growing runs?

## The make-or-break verdict (the headline)

**No — but transparently so.** Applied to the canonical $\ge2$-growing family
$W_a=d^a e_1 d^a e_2 d^a$ (cyclically $C(a,2a)=e_1 d^a e_2 d^{2a}$), written $P\,M\,Q$ with
$P=Q=d^a$ and $M=e_1 d^a e_2$, the two-ended extraction reduces to the **exact** core (proven
identity, [`../checks/two_ended_lever.py`](../checks/two_ended_lever.py) PART A, $a=1..8$ in
$\mathbb{Z}[X,Y]$ via the kernel):
$$\boxed{\,S(M)-S(M')=S(e_1d^ae_2)-S(e_2d^ae_1)=(X^{e_1}-X^{e_2})\,S(d^{a+1})\,}$$
— a **bounded** defect-factor $(X^{e_1}-X^{e_2})$ times the **trapped middle run's own sum**
$S(d^{a+1})=\dfrac{X^{(a+1)d}-Y^{a+1}}{X^d-Y}$. Its 6-free part is
$$\operatorname{sixfree}\bigl((2^{e_1}-2^{e_2})(3^{a+1}-2^{a+1})\bigr)=\operatorname{sixfree}(3^{a+1}-2^{a+1}),$$
which **provably diverges** (Bang–Zsygmondy: $3^{a+1}-2^{a+1}$ carries a primitive prime $\gt a+1$).
Verified: $5,19,65,211,665,2059,6305,19171$ for $a=1..8$, strictly increasing.

**No free lunch — the structural moral.** Extracting the two *outer* runs spends both defects on the
bounded factor $X^{e_1}-X^{e_2}$ and exposes a **lone run's raw defect** $S(d^{a+1})\sim 2^L-3^L$ —
which is the *original transcendence barrier itself*. A lone run is the degenerate $C=0$ circuit
(structure.md P1): it has **no companion defect to wedge against**, so $S(d^{a+1})$ is irreducible and
its 6-free part cannot be brought down. The two-ended move does not create exclusion power; it
relocates the unsolved core.

**Refinement of the Gen-4 no-go reading.** Gen 4 framed the obstruction as "a *non-cyclotomic*
(Mahler$\gt1$) factor of growing degree." The two-ended core is the **complementary** case: it is
**purely cyclotomic** — $S(d^{a+1})=\prod_{k\mid a+1,\,k\gt1}\Phi_k$ (homogenized), Mahler $=1$,
`noncyc-deg`$=0$ — yet still diverges because its cyclotomic **indices** (the divisors of $a+1$) do
**not** collapse into $\{1,2,6\}$ (the only $k$ with $\Phi_k(2)$ 6-smooth). This is exactly the
structure.md-thread-8 cyclotomic-collapse gate, here made concrete and *closed* for this reduced core.

## Why no valid two-ended ceiling exists (the trapped-run obstruction)

1. **The headline swap is not a rotation.** $PM'Q$ (the $M\leftrightarrow M'$ swap) is the **reversal**
   of $W_a$, *not* a rotation (PART A, verified for $a=2..5$). So $G(W_a)$ does **not** divide
   $S(PMQ)-S(PM'Q)$ — the clean core above is the sharpest *illustration* of the obstruction, but is
   itself **not a valid $G$-ceiling**. (It is, however, an exact identity worth keeping.)
2. **Whichever run you slide, the arc swallows the other.** Sliding the $q$-run uses arc
   $\beta_q=e_1d^ae_2$ (contains the $a$-run); sliding the $p$-run uses $\beta_p=e_2d^{2a}e_1$
   (contains the $2a$-run). Either residual core $S(\beta d)-S(d\beta)$ keeps the swallowed run and its
   6-free part grows (PART B: $305,691,1625,3979$ and $823,6127,50023,429727$).
3. **The valid two-ended rotation combo grows.** The only two rotations of $C(a,2a)$ keeping *both*
   runs un-split are $w_1=e_1d^ae_2d^{2a}$ and $w_2=e_2d^{2a}e_1d^a$ (a rotation of $w_1$). Their
   $\chi$-weighted combos have min 6-free part $23,23,1537,26857$ — not a fixed ceiling (PART C).
4. **Iteration does not transfer the small gcd.** Extracting run-$q$ lands on a wedge of the *shorter*
   word $C(a,1)$, but a **non-special** one (6-free $305,691,1625,3979,10145$); the bounded
   arc-through-run wedge of $C(a,1)$ is $a$-independent ($53$) but has length $a+3\ne a+2a+2$, so it is
   **unreachable** as a rotation combo of $C(a,2a)$. Small $G(C(a,1))$ does **not** bound $G(C(a,2a))$
   (PART D).
5. **Reversal/transpose (direction 4) is nil.** For the truly reversal-symmetric $e_1=e_2$, the
   reversal *is* a rotation and the two-ended core $(X^{e_1}-X^{e_2})S(d^{a+1})$ **vanishes** — $\hat S$
   pairing adds nothing beyond ordinary rotation combos (PART E).
6. **No uniform multi-term scheme found** (PART F, consistent with Gen-4 `multigap_nogo.py`): $k=2$
   unit combos grow ($23,23,1537,3979$); $k\ge3$ has the known **non-uniform low-$a$ coincidence**
   (min $=1$ at $a=2$) but no uniform bounded recipe. A finite search **cannot** close the general
   no-go (Gen-4 caveat respected).

## The general principle this exposes

A sub-pattern extracts as a **unit** in a $\chi$-weighted rotation combination **iff** it appears as a
*shared inner core* (P1: identical $u$ in every word, contributing $\chi(u)$) or a *shared boundary
frame* (dual: identical $P,Q$, contributing $X^{|P|}Y^{\operatorname{len}Q}$). A run $d^L$ can be so
shared **only when it sits at the boundary of the varying block** (a prefix/suffix frame) or is the
common inner core. With **two** growing runs separated by defects on both sides, **at most one** can be
presented as a shared frame/core per combination; the other is trapped between defects and survives as
an irreducible run-sum. This is the word-level reading of the C8/Plücker simultaneity obstruction
(two small cores force the third large; rank-2).

## The multi-defect generalization (Gen 7 — certified, conjecture corrected)

Take the $r$-defect equal-run middle $M_r=e_1d^ae_2d^a\cdots e_r$ ($r$ defects, $r-1$ interior runs)
inside the linear word $W=d^a M_r d^a$, and the two-ended swap $M_r\to M_r^{R}$ (reverse). Two exact
identities, **certified symbolically with free symbolic defects $e_i$** over $r=2..7$, $a=1..5$ via the
kernel ([`../checks/multidefect_reversal_core.py`](../checks/multidefect_reversal_core.py) PARTS A–B):

$$S(M_r)=Y^{(r-1)(a+1)}+S(d^{a+1})\sum_{i=1}^{r-1}X^{E_i+(i-1)ad}\,Y^{(r-1-i)(a+1)},\qquad E_i=e_1+\cdots+e_i,$$
$$\boxed{\,S(M_r)-S(M_r^{R})=S(d^{a+1})\cdot K_r,\quad
K_r=\sum_{i=1}^{r-1}X^{(i-1)ad}\bigl(X^{E_i}-X^{E_r-E_{r-i}}\bigr)Y^{(r-1-i)(a+1)}\,}$$

**This corrects the Gen-6 NEXT_FOCUS conjecture.** The reversal core is **not** $(\text{bounded defect
poly})\times\prod(\text{run sums})$:

- There is **exactly one** trapped-run-sum factor $S(d^{a+1})$ — **not** a product over the $r-1$
  interior runs. (All $r-1$ runs do enter, but each as $S(d^{a+1})\times$ a position monomial; the
  common $S(d^{a+1})$ factors out *once*, the monomials collect into $K_r$.)
- $K_r$ is **bounded only for $r=2$** ($K_2=X^{e_1}-X^{e_2}$, recovering Gen 6). For $r\ge3$ it carries
  $Y^{(r-2)(a+1)}$ and $X^{(r-2)ad}$ terms, so $\deg_Y K_r=(r-2)(a+1)$ **grows with $a$** (verified:
  $r{=}3$ gives $\deg_Y=3,5,7$ at $a{=}2,4,6$; $r{=}4$ gives $6,10,14$; …). So "bounded defect $\times$
  run" is a **special feature of $r=2$**, not the general shape.

**The divergence survives — and is cleaner.** Because $\operatorname{sixfree}$ is completely
multiplicative,
$$\operatorname{sixfree}\bigl(S(M_r)-S(M_r^R)\bigr)\big|_{(2,3)}=\operatorname{sixfree}(3^{a+1}-2^{a+1})\cdot\operatorname{sixfree}\bigl(K_r(2,3)\bigr),$$
and the first factor diverges by **Bang–Zsygmondy** (primitive prime $\gt a+1$). So whenever the core
is nonzero ($K_r(2,3)\ne0$) its 6-free part diverges — **for every $r$**, with the divergence carried by
a *single explicit cyclotomic run-sum factor* (PART C, $r=3,4,5$, $a=1..8$ strictly increasing).
**Unequal runs** $e_1d^{a_1}\cdots e_r$: the closed form generalises (PART D, certified), but now each
run $i$ keeps its *own* $S(d^{a_i+1})$ — the core is a **sum** of distinct run sums, so it does **not**
single-factor; numerically its 6-free part still diverges when $\ge2$ runs grow.

## The validity gap (Gen 7 — now sharp)

The clean reversal core is an **exact $\mathbb{Z}[X,Y]$ identity but never a valid nonzero $G$-ceiling**
(PART E):
$$W^{*}:=d^a M_r^{R} d^a \text{ is a rotation of } W=d^a M_r d^a\iff (e_1,\dots,e_r)\text{ is a palindrome}\iff S(W)-S(W^{*})=0.$$
For **distinct** defects $W^{*}$ is the reversal (not a rotation), so $G\nmid$ core; for **palindromic**
defects $M_r^{R}=M_r$ and the core **vanishes**. There is no middle ground — the construction cannot
produce a nonzero $G$-divisible clean core. Moreover the factorization does **not transfer** to the
*valid* both-runs-intact rotation difference of $C(a,2a)$: that carries a **non-cyclotomic** factor of
degree $2a+2$ (Mahler $\gt1$, growing) and has **no** $S(d^{a+1})$ factor (PART E). So the two
divergence mechanisms are **complementary**: the (invalid) reversal core is *cyclotomic of growing
index*; the (valid) rotation core is *non-cyclotomic of growing degree* — both diverge, but only the
invalid one factors through a single clean run-sum.

## The C8 rank-2 link (Gen 7 — precise, and why the symmetric case is open)

All runs of a fixed background $d$ lie on **one line** in $R^2$: $D(d^L)=(X^d-Y)\,S(d^L)$, i.e.
$\mathbf v(d^L)=S(d^L)\,(X^d-Y,\,1)$ (PART F, $L=1..8$) — the rank-1 collapse (structure.md P1 / the
$C=0$ locus). Hence for a 3-cut $u=d^{L_1},\,v=\text{defects},\,w=d^{L_2}$ the wedge $C(u,w)=0$ and
**C8 collapses to the proportionality**
$$D(u)\,C(v,w)=-\,D(w)\,C(u,v),\qquad \frac{C(v,w)}{C(u,v)}=-\frac{X^{L_2 d}-Y^{L_2}}{X^{L_1 d}-Y^{L_1}}.$$
This is the exact word-level rank-2 statement that "the two defect-slide cores are not independent."
But — **honest caveat** — for **unequal** runs the ratio's 6-free part diverges (Zsygmondy on
$2^L-3^L$), while for **equal** runs $L_1=L_2$ the ratio is $-1$ and **C8 imposes no obstruction at
all**. So C8 automatically handles the unequal case but is *silent on the symmetric equal-run family* —
which is exactly why that family is the stubborn reduced-but-open core of the no-go. C8 is the rank-2
backbone, not (by itself) a proof for the symmetric case.

## The validity-gap bridge (Gen 8 — make-or-break SETTLED NEGATIVE, thread closed)

Gen 7 left exactly one live question: the clean reversal core diverges (Zsygmondy) but is not
$G$-valid (palindrome $\iff$ core $=0$); could the *reversal sum* $S(W^R)$ nonetheless be
**expressed within the rotation lattice** $L=\operatorname{span}_{\mathbb{Z}[1/6]}\{S^{(j)}(W)\}$ — so
the divergence transfers to a valid obstruction? Gen 8 tests this directly on
$W=C(a,2a)=e_1d^ae_2d^{2a}$ ([`../checks/reversal_lattice_bridge.py`](../checks/reversal_lattice_bridge.py),
all parts pass, exit 0). **Verdict: no, on every count.**

1. **$S(W^R)$ escapes the lattice (proven non-membership).** For every genuine 2-defect word
   ($e_1,e_2\ne d$; pairs $(3,4),(2,5),(2,3),(3,5)$, $a=2..4$), $S(W^R)$ — and the clean factor
   $C_a=(X^{e_1}-X^{e_2})S(d^{a+1})$, and the full linear reversal core — is **not** in the scalar
   lattice $L$, **nor** in the looser Laurent-**monomial** lattice $L_{\mathrm{mon}}$ (the program's
   "valid rotation combination"). Each non-membership is a *definitive* modular **rank-gap witness**
   confirmed on **two** independent primes (a rank gap $\operatorname{rank}_p[A|b]\gt\operatorname{rank}_p[A]$
   forces $\mathbb{Q}$-non-membership). So the clean reversal core is **never** a valid combination —
   now proven *directly*, strengthening Gen-7's indirect "$W^R$ is not a rotation" argument (PART B).
2. **The remainder is uncontrollable (proven).** Writing core $=V+R$ with $V\in L_{\mathrm{mon}}$
   valid: the **minimal residue degree** of the core modulo $L_{\mathrm{mon}}$ equals the core's *full*
   degree $a+4$ for every $a$ — **the lattice cancels nothing** of the core's divergent structure. And
   for any *fixed* remainder-degree bound $\delta\in\{2,3\}$ the core escapes $L_{\mathrm{mon}}\oplus B_\delta$
   for $a=2..5$, so **no $a$-independent bounded $R$ exists**. $R$ carries the entire divergence (PART C).
3. **Useless even if it bridged (proven).** $\operatorname{sixfree}$ of the reversal core grows
   ($205,6203,147625,3343187,\dots$, Zsygmondy), whereas the bounded-arc valid wedge
   $\operatorname{sixfree}(S(\beta d)-S(d\beta))$ is a *fixed* constant ($5$ for $\beta=(2,3)$). A valid
   combination *equal to* a divergent core gives only the vacuous ceiling $G\le(\text{diverging})$ — no
   cap on $o$. Exclusion needs a **bounded** valid core; the reversal route supplies none (PART D).
4. **The structural reason (proven, exact).** Reversal is the matrix **transpose** ($M(W^R)$ is the
   reverse product). The *only* matrix $P$ with $P\,M(d)\,P^{-1}=M(d)^{\top}$ for all letters $d$ is
   **singular** ($\det=0$). Since rotation $=$ conjugation by word-matrices (structure.md C3), reversal
   is **not** a fixed conjugation — there is **no $a$-uniform linear operator** carrying the rotation
   orbit onto $S(W^R)$. This is *why* the bridge fails uniformly, not by numerical accident (PART E).
5. **The boundary marker (instructive positive).** When a defect equals the background ($e_1=d$), the
   word collapses to a **single-defect** $d^{a+1}e_2d^{2a}$ (the P2 lever case) and there $S(W^R)$ **is**
   a rotation, hence **does** lie in $L_{\mathrm{mon}}$ (PART B2). So the reversal bridges into the lattice
   *exactly* on the already-excludable family and *escapes* it *exactly* on the genuinely-hard $\ge2$
   growing-gap family — the bridge boundary coincides with the lever's reach.
6. **Equal-defect cyclic illustration.** For $e_1=e_2$ the *cyclic* $W=ed^aed^{2a}$ is **not** a
   palindrome (runs $a,2a$ differ), so $W^R$ **is** a rotation — a genuinely **valid** combination whose
   6-free part nonetheless **diverges** ($41405,972895,\dots$). A crisp witness that "valid" $\ne$
   "bounded" — the literal content of the no-go (PART A).

**Net.** The user's "generalize the last combination" idea is now fully exhausted: the reversal sum
cannot be brought inside the valid rotation lattice with any controllable remainder, and would be
useless if it could. The two-ended / reversal thread **cannot produce a $G$-valid exclusion**. Thread
**closed**. The $G$-valid no-go for the symmetric equal-run family is *unaffected* by this result and
stays the open cyclotomic-collapse problem of `approaches/bounded-defect-lever`.

## Open questions

- [x] **(Gen 8 — the validity-gap bridge, SETTLED NEGATIVE)** Can $S(W^R)$ be expressed within the
      rotation lattice (valid combination $+$ controllable remainder)? **No.** It escapes both the
      scalar and monomial lattices (proven, 2-prime rank-gap), the remainder is uncontrollable (residue
      degree $=$ deg core $=a+4$), it would be useless if it bridged (divergent), and the structural
      reason is exact (reversal $=$ transpose $\ne$ conjugation). Certified `reversal_lattice_bridge.py`.
      **The two-ended thread is closed.**
- [ ] **(make-or-break — settled negative)** Does a two-ended combination tame $\ge2$ growing runs?
      **No.** Proven for the canonical reduced core (Zsygmondy on $3^{a+1}-2^{a+1}$); strong structural
      reason + search for the fully general statement (which remains the open cyclotomic-collapse no-go
      in [bounded-defect-lever](bounded-defect-lever.md)).
- [x] **Multi-defect generalization of the exact core.** *Done (Gen 7) — conjecture CORRECTED.* The
      reversal core is $S(d^{a+1})\cdot K_r$: **one** run-sum factor, not $\prod$; and $K_r$ is bounded
      only for $r=2$. Divergence holds for all $r$ (single Zsygmondy factor). Unequal runs give a
      **sum** of distinct run sums. Certified `multidefect_reversal_core.py` PARTS A–D.
- [x] **Does the exact core ever become a valid ceiling?** *Done (Gen 7) — sharp negative.* The clean
      reversal core is a genuine $G$-multiple **iff** the defects are palindromic, and then it is
      **identically $0$**. So it is never a valid *nonzero* $G$-ceiling for this construction. And the
      factorization does **not transfer** to valid combos (those are non-cyclotomic, deg $2a+2$).
      Certified PART E.
- [x] **Sharpen the C8 link.** *Done (Gen 7).* Runs of $d$ are a rank-1 line ($D(d^L)=(X^d-Y)S(d^L)$),
      so a 3-cut with two run-arcs gives $D(u)C(v,w)=-D(w)C(u,v)$. **Caveat:** the ratio obstructs only
      for *unequal* runs; for equal runs it is $-1$ and C8 is silent — so C8 alone does **not** close
      the symmetric equal-run no-go. Certified PART F.
- [ ] **The remaining $G$-valid no-go (still open — but NOT via this thread).** The reduction
      (`multigap_nogo.py`): no *unit-combination of rotations* of the symmetric equal-run family has an
      $a$-independent (cyclotomic-collapsed) reduced polynomial. Gen 7 closed the *invalid* reversal
      route (clean Zsygmondy, cannot bridge to $G$-valid combos); **Gen 8 closed the bridge itself**
      (the reversal sum escapes the lattice, uncontrollable remainder, useless if bridged, structural
      reason exact). So the two routes this thread could offer are **both exhausted**. C8 remains silent
      on the symmetric case. A genuinely new idea — *not* reversal/transpose-based and *not* C8 —
      is needed (e.g. a direct degree/Mahler growth argument forbidding an $a$-independent reduced
      polynomial). This is a **property of the promoted approach**
      [approaches/bounded-defect-lever](../../approaches/bounded-defect-lever/RATIONALE.md), not of this
      (now closed) thread.

## Iteration log
- 2026-06-08 (Gen 6): created. Generalized the Gen-5 two-ended P1 to the dual shared-frame two-ended
  extraction and ran the user's headline make-or-break on $W_a=d^ae_1d^ae_2d^a$. **Proven** the exact
  identity $S(e_1d^ae_2)-S(e_2d^ae_1)=(X^{e_1}-X^{e_2})S(d^{a+1})$ ([`two_ended_lever.py`](../checks/two_ended_lever.py)
  PART A, $a=1..8$): the two-ended core is a bounded defect times the **trapped middle run's sum**,
  6-free part $=\operatorname{sixfree}(3^{a+1}-2^{a+1})$, **provably divergent (Zsygmondy)**. Verified
  the headline swap is the reversal (not a rotation), the trapped-run obstruction for both run choices,
  the valid both-runs-intact combo growth, the non-transferring iteration $C(a,2a)\to C(a,1)$, the
  $e_1=e_2$ reversal=rotation collapse, and the no-uniform-scheme search (all exit 0). **Verdict:
  two-ended extraction sharpens but does not crack the $\ge2$-growing-gap no-go** — "no free lunch",
  it relocates the lone-run defect barrier. Refines Gen-4's "non-cyclotomic" framing: the core here is
  *cyclotomic of growing index*, the complementary cyclotomic-collapse failure.
- 2026-06-08 (Gen 7): **certified the multi-defect generalization and CORRECTED the conjecture.**
  Derived + symbolically verified (free symbolic $e_i$, $r=2..7$, $a=1..5$) the closed form for
  $S(M_r)$ and the reversal core $S(M_r)-S(M_r^R)=S(d^{a+1})K_r$ — exactly **one** run-sum factor (not
  $\prod$), with $K_r$ bounded only for $r=2$. 6-free part diverges by Zsygmondy for all $r$ via the
  single factor (multiplicative split, $r=3,4,5$, $a=1..8$). Unequal-run closed form verified; core is a
  **sum** of distinct run sums there. **Validity gap made sharp:** clean core is a $G$-multiple iff
  defects palindromic iff core $=0$; does not transfer to valid (non-cyclotomic, deg $2a+2$) combos.
  **C8 made precise:** runs of $d$ are a rank-1 line, 3-cut gives $D(u)C(v,w)=-D(w)C(u,v)$, but the
  ratio is $-1$ for equal runs so C8 is silent on the symmetric family — explaining why it is the
  stubborn open case. All in [`../checks/multidefect_reversal_core.py`](../checks/multidefect_reversal_core.py)
  (exit 0). **Net:** the reversal-route no-go is now *exact* (Zsygmondy, all $r$); the $G$-valid no-go
  stays reduced-but-open — Gen 7 proves the clean route cannot be made valid.
- 2026-06-08 (Gen 8): **the validity-gap bridge — make-or-break SETTLED NEGATIVE; thread CLOSED.**
  Tested whether the reversal sum $S(W^R)$ lives in the rotation lattice $L=\operatorname{span}\{S^{(j)}(W)\}$
  ([`../checks/reversal_lattice_bridge.py`](../checks/reversal_lattice_bridge.py), all parts pass, exit 0;
  exploration in [`../checks/reversal_lattice_explore.py`](../checks/reversal_lattice_explore.py)).
  **(B, proven)** for every genuine 2-defect word ($e_i\ne d$) $S(W^R)$, the clean core $C_a$, and the
  full reversal core all **escape** the scalar lattice **and** the Laurent-monomial lattice — definitive
  modular rank-gap witnesses on two primes; the clean core is thus **never** a valid combination (direct
  proof, sharpening Gen-7). **(C, proven)** the remainder is **uncontrollable**: min residue degree mod
  $L_{\mathrm{mon}}=$ deg(core)$=a+4$ for all $a$ (the lattice cancels nothing), and the core escapes
  $L_{\mathrm{mon}}\oplus B_\delta$ for fixed $\delta$ as $a$ grows. **(D, proven)** useless even if it
  bridged — the core diverges (Zsygmondy: $205,6203,147625,\dots$) vs the bounded-arc wedge's fixed $5$,
  so a valid combo equal to it gives only $G\le(\text{diverging})$. **(E, proven, exact symbolic)** the
  structural reason — reversal $=$ transpose, and the only $P$ with $PM(d)P^{-1}=M(d)^{\top}\ \forall d$
  is singular, so reversal is not a fixed conjugation (rotation **is**, C3) ⇒ no $a$-uniform linear
  bridge. **(B2, instructive)** when a defect $=d$ the word collapses to single-defect P2 and $S(W^R)$
  **does** bridge into $L_{\mathrm{mon}}$ — the bridge boundary coincides with the lever's reach.
  **(A)** the equal-defect *cyclic* core is a valid rotation wedge that nonetheless diverges — "valid
  $\ne$ bounded", the no-go's content. **Verdict:** the user's "generalize the last combination" idea
  is exhausted; the two-ended / reversal thread **cannot** yield a $G$-valid exclusion. Status set to
  **resolved**. The $G$-valid no-go for the symmetric family is untouched and stays the open problem of
  the promoted approach.
