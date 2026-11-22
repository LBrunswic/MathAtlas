# Knight 2023 — Collatz High Cycles Do Not Exist

- **Source file:** `sources/knoght.pdf`
- **Full citation:** Kevin Knight, *Collatz High Cycles Do Not Exist*, preprint, HAL ⟨hal-04261183⟩, 2023.
- **Feeds:** `structure.md` claim **C9** (and corroborates C7); pattern leverage for the high-cycle / Christoffel rotation class; threads §5, §6.

## What it says (relevant part only)

For a parity vector $v$ of length $k$ with $x$ ones at $0$-based positions $d_0<\dots<d_{x-1}$, the
Böhm–Sontacchi cycle member is $f(v)=g(v)/(2^k-3^x)$ with numerator
$g(v)=\sum_{i=0}^{x-1}2^{d_i}3^{x-1-i}$. The **high cycle** (innermost, largest minimal member of the
$(k,x)$ family) is realized by the **upper Christoffel word** $v_h$, taken at $k=\lceil x\log_2 3\rceil$;
its reverse $v_h^R$ is *another rotation of the same cyclic word* (Cohn 1972), hence in the same cycle.
Writing $v_h=1u0$ and $v_h^R=0u1$ gives $f(v_h)=(2g(u)+3^{x-1})/D$ and $f(v_h^R)=(6g(u)+2^{k-1})/D$
with $D=2^k-3^x$. Then $3f(v_h)-f(v_h^R)+1 = 2^{k-1}/D$; since $2^{k-1}$ has no odd factor and $D$ is
odd $>1$, it cannot be an integer — contradiction. The variant $f(p01)-f(p10)=2^{k-2}/D$ does the
same with a single adjacent rotation pair. **No lower bound on $|2^k-3^x|$ is used** (unlike Steiner's
no-circuit proof, which needs Ellison/Baker bounds).

## How it connects here

This is a published worked **compensation** in exactly the cocycle-combine sense, and it is the
exemplar for the now-certified **C9**: $g(v)$ *is* our $S$ of the cyclic gap word (verified
numerically — $g(11011010)=S(1,2,1,2,2)=319$), so the integer combination of two rotation sums
collapses to a pure monomial core. Generically (in $\mathbb{Z}[X,Y]$, with $u$ cancelling) the cores are

$$Y\,g(1u0)-g(0u1)+D=X^{E-1}(X-1),\qquad g(p01)-g(p10)=X^{E-2}(X-1),$$

both certified in `verify_structure.py`. The §5 split is textbook: the **generic** layer is the
monomial identity; the **cheap-arithmetic** layer is $X\mapsto2$ (the core becomes the even monomial
$2^{E-1}$, and $G=|D|$ odd forces $|D|=1$). The combinatorics-on-words input — that $v_h$ and $v_h^R$
are one rotation class — is what puts both summands on the same cycle so $G$ divides the combination;
this is *not* generic, it is the Christoffel/Cohn fact. So C9 is the strongest **Baker-free** ceiling:
it kills one rotation class (the high cycle / lexicographic extreme) without transcendence theory.

## Open thread it touches

Thread §5 (generalize C9 beyond the Christoffel seam): which other word/rotation pairs give a monomial
core $X^a(X-1)$? Each such pair is a Baker-free ceiling for its family. Next step: characterize the
locus of pairs $(\rho_i,\rho_j)$ of one cyclic word with $C(\rho_i,\rho_j)$ a monomial — C9 says the
"seam" pair $(1u0,0u1)$ always does; map the rest. References pulled from here: Böhm–Sontacchi 1978
(the $f=g/D$ closed form), Halbeisen–Hungerbühler 1997 (Christoffel = high cycle, $f$-ordering),
Berstel–Lauve–Reutenauer–Saliola 2009 (Christoffel words), Cohn 1972 (reverse = rotation; Markoff
forms ↔ $SL_2$, ties to the C1 transfer matrix), Eliahou 1993 (word/continued-fraction cycle-length
bounds), Ellison 1971 (the $2^k-3^x>2.56^x$ bound), Steiner 1977 (no circuits).
