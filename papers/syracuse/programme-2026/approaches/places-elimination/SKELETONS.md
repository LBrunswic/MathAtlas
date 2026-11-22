# Skeleton families: uniform-in-the-words ceilings

*2026-10-30. Compiler: [`skeleton.py`](skeleton.py). Lean support:
`lean/Syracuse/Approaches/R1/Skeleton.lean`. Generated library: `lean/Syracuse/Approaches/R1/Skel/*.lean`.
All axiom-clean. Math uses `\lt`/`\gt`.*

## 1. What a skeleton is

A **skeleton** $\sigma$ is a sequence of slots. Each slot is either a spacer `S` or a growing block
`B:k:m:c` (repeated $ma+c$ times, of size $k$ times a common slope vector $(p,q)$). An **instance**
fills the slots with words:
- blocks $\beta_i$ with $|\beta_i|=k_ip$ and $\mathrm{len}\,\beta_i=k_iq$;
- arbitrary positive spacers $\sigma_j$.

Its members are
$$W(a)=\sigma_0\,\beta_1^{m_1a+c_1}\,\sigma_1\cdots .$$

Every skeleton family is r = 1, so [`CLASSIFICATION.md`](CLASSIFICATION.md) applies instance by
instance. The skeleton route adds **uniformity in the words**:
- $D(W(a))$ and $\mu\,S(W(a))$, with $\mu=2^{Lp}-3^{Lq}$ and $L=\mathrm{lcm}(k_i)$, are fixed
  polynomials in the run coordinates $[z:s]=[2^{pa}:3^{qa}]$.
- Their coefficients depend only on the **cocycle data**
  $$S(\beta_i),\quad S(\sigma_j),\ 2^{|\sigma_j|},\ 3^{\mathrm{len}\sigma_j},\quad 2^p,\ 3^q .$$
- So the resultant in $[z:s]$ is a **universal polynomial** $\mathrm{Res}_\sigma$ in that data. With
  its 6-unit factors removed, it is the ceiling $c_\sigma R'_\sigma$.

> **Skeleton theorem (each `Skel/NAME.lean`).** For every instance, every cycle member satisfies
> $$D(W(a))\ \big|\ c_\sigma\,R'_\sigma(\text{data})\qquad(\texttt{ceiling}),$$
> and if $c_\sigma R'_\sigma(\text{data})\ne0$ only finitely many $a$ give cycles (`finite`).

## 2. How a file is proved

The script emits, and Lean checks, five things per skeleton:
1. the word and the universal polynomials `Du`, `Gu`, `Rp`, `Au`, `Bu` (large ones split into chunks);
2. `certificate`: $s^e\cdot(\text{6-unit monomial})\cdot c\,R'=A\,D+B\,G$, an identity in a free
   commutative ring, proved by `ring`;
3. `closedD`, `closedS`: the closed forms over any commutative ring. These use `S_append` and the
   block relation `wpow_rel`, $D(\beta)S(\beta^n)=S(\beta)(X^{n|\beta|}-Y^{n\,\mathrm{len}\beta})$,
   via `linear_combination` with script-supplied coefficients;
4. `ceiling`: the certificate at $(2,3)$, plus coprimality of $D$ with 6 (`dvd_of_isCoprime_six_of_dvd`);
5. `finite`: `finite_of_ceiling`, since $|D(W(a))|\to\infty$ because $2^{pN}\ne3^{qN}$.

Running the compiler:

    skeleton.py show    "B:1:1:0 S B:1:1:0 S"           # D, G, factored resultant and ceiling
    skeleton.py check   "B:1:1:0 S B:1:1:0 S" 150       # random instances: gcd6(D,S) | ceiling
    skeleton.py compile "B:1:1:0 S B:1:1:0 S" TwoBlock out.lean

## 3. The library

| file | skeleton | words | N | ceiling terms | Lean check time |
|---|---|---|---|---|---|
| `OneBlock` | `S B:1:1:0 S` | $x\,\beta^a\,y$ | 1 | 6 | 4 s |
| `TwoBlock` | `B:1:1:0 S B:1:1:0 S` | $\beta^a x\,\gamma^a y$ | 2 | 18 | 5 s |
| `TwoBlockOff` | `B:1:1:1 S B:1:1:0 S` | $\beta^{a+1}x\,\gamma^a y$ | 2 | 20 | 7 s |
| `TwoBlockM2` | `B:1:1:0 S B:1:2:0 S` | $\beta^a x\,\gamma^{2a}y$ | 3 | 38 | 34 s |
| `TwoBlockK21` | `B:2:1:0 S B:1:1:0 S` | $|\beta|=2|\gamma|$, $\mathrm{len}\beta=2\,\mathrm{len}\gamma$ | 3 | 60 | 61 s |
| `ThreeBlock` | `B:1:1:0 S B:1:1:0 S B:1:1:0` | $\beta^a x\,\gamma^a y\,\delta^a$ (contains `twoRunWord`) | 3 | 58 | 40 s |
| `ThreeBlockS` | `B:1:1:0 S B:1:1:0 S B:1:1:0 S` | adds a third spacer | 3 | 96 | 120 s |

**Spot checks.**
- `OneBlock` gives exactly $C(\beta,yx)$: the $w^aw'$ core after rotation.
- `ThreeBlock` specialises to `twoRunWord` ($\beta=\gamma=\delta=[d]$, $x=[e_1]$, $y=[e_2]$). On
  $(d,e_1,e_2)=(1,2,3),(2,1,3),(3,1,2),(1,3,2),(3,2,5)$ its 6-free ceiling equals that of $R^\ast$
  (19, 1, 89, 97, 35). The general $\mu=2^{Lp}-3^{Lq}$ (rather than $\prod D(\beta_i)$) is what makes
  this sharp. With the product, spurious factors $D(\beta)^k$ appear (e.g. $5^6$ at $d=3$).

**The two-block ceiling, explicitly.** For $\beta^a x\,\gamma^a y$ with $|\beta|=|\gamma|$ and
$\mathrm{len}\beta=\mathrm{len}\gamma$, put $D=2^p-3^q$ (so $D(\beta)=D(\gamma)=D$). Then
$$c_\sigma R'_\sigma=P_xQ_x\big[(DS_y-P_yS_\beta)^2+2DQ_yS_\gamma S_y+Q_y^2S_\gamma^2\big]-P_yQ_y\big[(DS_x-P_xS_\gamma)^2+2DQ_xS_\beta S_x+Q_x^2S_\beta^2\big],$$
with $P_x=2^{|x|}$ and $Q_x=3^{\mathrm{len}x}$. This identity is checked symbolically.

**Randomized checks** (`skeleton.py check`, 150 random instances each, $a\le11$): there were 0
violations of $\mathrm{gcd}_6(D,S)\mid$ ceiling over about 10,700 members across the six shapes.

## 4. The degenerate locus $R'_\sigma(\text{data})=0$

Here the uniform ceiling says nothing. The instance is still decided by `decideR1` (finite cycle set
or constant fixed point). The degenerate instances in a random search fall into two kinds:

- **Constant fixed point.** The family is the powers of one word. Examples: $2^a1\,2^a1=(2^a1)^2$ and
  $(1,2)^a1(2,1)^a2=(12)^{2a+1}$, with conjugate blocks.
- **Partial.** Usually the family is a power of a lower-degree family, e.g.
  $1^a42\,1^a42=(1^a42)^2$. There $D$ and $S$ share the factor $2^{|V|}+3^{\mathrm{len}V}$.
  Rarer coincidences also occur, e.g. $2^a1\,2^a32\,2^a$.

| skeleton | degenerate of 3000 random | constant | partial |
|---|---|---|---|
| `B S B S` | 201 | 39 | 162 |
| `B S B S B` | 68 | 48 | 20 |
| `B S B(m=2) S` | 48 | 39 | 9 |
| `B(k=2) S B S` | 41 | 18 | 23 |

A uniform description of the degenerate locus — a factorisation of $\mathrm{Res}_\sigma$ along
"power" and "conjugate" sub-loci — is the natural next question. It is not attempted here.

## 5. Relation to the other results

- **`decideR1`** decides each instance exactly, but needs the words.
- **Skeletons** give one explicit ceiling for all instances at once, outside the degenerate locus.
- **Towers** ([`NESTED.md`](NESTED.md)) cover multiplicative exponents, with qualitative finiteness.
