# Cohn 1972 — Markoff forms and primitive words

- **Source file:** `sources/cohn1972-markoff-forms.pdf` (GDZ scan, assembled from `gdz.sub.uni-goettingen.de/id/PPN235181684_0196`; EuDML `https://eudml.org/doc/162238`)
- **Full citation:** H. Cohn, *Markoff forms and primitive words*, Math. Ann. **196** (1972), 8–22.
- **Feeds:** the algebraic mechanism behind **C9** (reverse = rotation) and the $SL_2$/transfer-matrix lineage of **C1**.

> _Note: this source is a 600-dpi page scan; the structural takeaways below are the well-established
> content of the paper. Exact lemma numbers / verbatim statements should be read off the scan before
> being quoted — the reading agent's specific citations were not independently confirmed._

## What it says (relevant part only)

Cohn studies **primitive words** in the free group $F_2=\langle A,B\rangle$ (words that are part of a
free basis). Two facts matter here: (1) the primitive words form a single orbit under
$\operatorname{Aut}(F_2)$ (Nielsen), and the abelianisation $\operatorname{Aut}(F_2)\to GL_2(\mathbb Z)$
realises this orbit on $\mathbb Z^2$, with the Markoff numbers appearing as **traces** of the associated
$SL_2(\mathbb Z)$ matrices (Fricke's identity $\operatorname{tr}A\,\operatorname{tr}B\,\operatorname{tr}AB
=\operatorname{tr}^2A+\operatorname{tr}^2B+\operatorname{tr}^2AB$ → Markoff equation). (2) The cyclic
("period") class of a primitive word is a Christoffel/Sturmian word for a slope $p/q$, and its
**reverse is conjugate to it** (a cyclic rotation), via the slope-symmetry $q/p$, $qq'\equiv1\ (p)$ of
Markoff forms.

## How it connects here

This is the *why* behind **C9**'s key combinatorial input. Knight needs the upper-Christoffel word $v_h$
and its reverse $v_h^R=0u1$ to be **rotations of one cyclic word** so they lie on the same cycle; Cohn
supplies the structural reason — reverse $=$ conjugate for primitive/Christoffel words, a consequence of
the $SL_2$ symmetry of Markoff forms, not a coincidence. It also sharpens the **C1** picture: the
word $\mapsto SL_2(\mathbb Z)$ matrix map (with Markoff number $=$ trace) is the same genus of
transfer-matrix homomorphism as $M(w)=\big(\begin{smallmatrix}Y^o&0\\S&X^E\end{smallmatrix}\big)$ —
trace/conjugacy invariants there ($\operatorname{tr}M=X^E+Y^o$, $D=\lambda_1-\lambda_2$) are the
analogues of the Markoff trace. This is the concrete bridge to chase for thread §3 (link to
`circulant_matrix`) and the proposed Lie/Markoff structure (thread §4).

## Open thread it touches

§3 (transfer-matrix bridge) and the C9-generalisation (§5): the Markoff/Stern–Brocot tree organises
Christoffel words by slope — a candidate index for *which* rotation pairs give small cores. Chase:
**Series 1985** (*The geometry of Markoff numbers*, Math. Intelligencer 7), Berstel–de Luca 1997
(Sturmian/Lyndon/Christoffel), and the Berstel–Reutenauer *Noncommutative Rational Series* book now in
`sources/` (S as a rational series / weighted automaton — direct C1 formalisation).
