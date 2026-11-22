# Terras 1976 — the parity/encoding vector (origin of the word coding)

- **Source file:** `sources/terras1976-stopping-time.pdf` (EuDML/IMPAN open access, `http://matwbn.icm.edu.pl/ksiazki/aa/aa30/aa3034.pdf`)
- **Full citation:** R. Terras, *A stopping time problem on the positive integers*, Acta Arith. **30** (1976), 241–252.
- **Feeds:** the historical origin of the project's "word" $w$ and the iterate formula behind **C1**.

## What it says (relevant part only)

For $Tn=(3^{X(n)}n+X(n))/2$ with $X(n)=n\bmod2$, Terras defines the **encoding vector**
$E_k(n)=(X_0,\dots,X_{k-1})\in\{0,1\}^k$, $X_i=X(T^i n)$. With $S_i=\sum_{j<i}X_j$ and
$\lambda_i=3^{S_i}/2^{i}$, the **master iterate formula** is
$$T^k n=\lambda_k(n)\,n+\varrho_k(n),\qquad \varrho_k=\tfrac{\lambda_k}{2}\sum_{j=0}^{k-1}X_j\,\lambda_{j+1}^{-1}.$$
He proves $E_k(n)=E_k(m)\iff n\equiv m\pmod{2^k}$ (the encoding is a complete residue invariant mod
$2^k$, and all $2^k$ patterns occur), and develops the stopping-time density via these vectors.

## How it connects here

This is the **first appearance of the Collatz "word"**. The encoding vector $E_k(n)$ *is* the
project's word (the $1$-positions are the partial gap-sums $e_k$), and the remainder $\varrho_k$, once
the $2^k$ is cleared, is exactly $S(w)$ — i.e. $T^k n=(3^o n+S(w))/2^E$ at $(2,3)$. On a cycle $T^k n=n$
this rearranges to $n=S/D$, recovering Böhm–Sontacchi ([[bohm-sontacchi1978-cycle-formula]]). So the
affine iterate $n\mapsto\lambda n+\varrho$ is the integer shadow of the **C1** transfer matrix
$M(w)=\big(\begin{smallmatrix}Y^o&0\\S&X^E\end{smallmatrix}\big)$ acting on $(1,n)$. The mod-$2^k$
invariance is the arithmetic root of why cyclic words (conjugacy classes, **C3**) are the right objects.

## Open thread it touches

Confirms the word coding is canonical, not an artefact of our normalisation. Further references: Everett
1977 (independent discovery); Lagarias's bibliography ([[lagarias-annotated-bibliography]]) traces the
whole parity-vector lineage (Huang–Wu bijection, Shallit–Wilson automata, López–Stoll Sturmian).
