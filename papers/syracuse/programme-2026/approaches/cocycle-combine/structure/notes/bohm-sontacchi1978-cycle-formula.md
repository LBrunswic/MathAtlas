# Böhm–Sontacchi 1978 — closed form for cycle members

- **Source file:** `sources/bohm-sontacchi1978-cycle-formula.pdf` (BDIM open access, `http://www.bdim.eu/item?fmt=pdf&id=RLINA_1978_8_64_3_260_0`)
- **Full citation:** C. Böhm, G. Sontacchi, *On the existence of cycles of given length in integer sequences like $x_{n+1}=x_n/2$ if $x_n$ even and $x_{n+1}=3x_n+1$ otherwise*, Atti Accad. Naz. Lincei, Cl. Sci. Fis. Mat. Nat., Rend. (8) **64** (1978), no. 3, 260–264.
- **Feeds:** the foundation of the $S/D$ = cycle-member identity behind all of `structure.md`; corroborates **C5/C7/C6**.

## What it says (relevant part only)

For the half-step map $u(x)=x/2$ (even), $(3x+1)/2$ (odd), parametrised by the strictly increasing
exponent sequence $v_0<\dots<v_{m-1}$ (cumulative halving-positions of the $m$ odd steps; $n=v_m$ total
halvings), they prove (**Prop. 4**) the iteration formula
$u^n(x)=\big(3^m x+\sum_{k=0}^{m-1}3^{m-k-1}2^{v_k}\big)/2^n$, hence (**Prop. 5**) $x$ is a cycle
member $\iff$
$$x=\frac{\sum_{k=0}^{m-1}3^{m-k-1}2^{v_k}}{2^{n}-3^{m}}.$$
They also bound $|x|<3^n$ on a cycle (**Prop. 6**), and give the dual basin-of-$1$ characterisation
(**Prop. 7**): $x\in U\iff x=(2^{n}-\sum 3^{m-k-1}2^{v_k})/3^m$.

## How it connects here

This is the **historical origin of $S/D$**. The numerator $\sum_k 3^{m-k-1}2^{v_k}$ is exactly our
$S(w)$ at $(X,Y)=(2,3)$ (set $o=m$, $e_k=v_k$, so each term is $X^{e_k}Y^{o-1-k}$), and the
denominator $2^{n}-3^{m}$ is $D(w)=X^E-Y^o$. So the cycle start number is $x=S/D$ — the object the
whole approach manipulates, here proved necessary **and** sufficient. The composition that produces the
iteration formula (Prop. 4) is the $(2,1)$-recursion of the monoid hom **C1/C5**; the basin formula
(Prop. 7) rearranges to $x\,D+S=2^n$, the **C6** coboundary equation. Everything is generic; the only
arithmetic is $D\ne0$. Prop. 6's $|x|<3^n$ is a crude precursor of the Christoffel range bounds
sharpened later by Halbeisen–Hungerbühler ([[halbeisen-hungerbuhler1997-rational-collatz-bounds]]).

## Open thread it touches

None new — this anchors the others. Further references from its list: **Everett 1977** (independent
contemporaneous iteration formula — worth a parity check that Everett's numerator is $S$ in another
normalisation) and Conway 1972 (*Unpredictable iterations*). Terras 1976
([[terras1976-stopping-time]]) is the parity-vector source the formula rests on.
