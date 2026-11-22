# Eliahou 1993 — new lower bounds on nontrivial cycle lengths

- **Source file:** _not yet acquired_ — no legitimate free PDF located (UNIGE green-OA record has no
  retrievable file; Elsevier open archive is behind Cloudflare; no arXiv/HAL deposit). Read it via the
  Elsevier open archive in a browser (`sciencedirect.com/science/article/pii/0012365X9390052U`) or
  request from the author (`eliahou@univ-littoral.fr`), then drop the PDF in `sources/`.
- **Full citation:** S. Eliahou, *The 3x+1 problem: new lower bounds on nontrivial cycle lengths*, Discrete Math. **118** (1993), 45–56.
- **Feeds:** the word/continued-fraction backing for the §5 barrier (content via Lagarias's annotation + the Halbeisen–Hungerbühler discussion, pending the PDF).

## What it says (relevant part only)

Any nontrivial $3x+1$ cycle has period $p=301994A+17087915B+85137581C$ with $A,B,C\ge0$, $B\ge1$, at
most one of $A,C$ nonzero — so min period $\ge17{,}087{,}915$ (assuming verification to $2^{40}$). The
mechanism: for a cycle with $k$ total steps, $l$ odd steps, min element $m$, one has
$\log_2 3<k/l<\log_2(3+1/m)$, an extremely tight interval since $m$ is huge; the coefficients
$301994,17087915,85137581$ are numerators of consecutive **convergents of $\log_2 3$**, and the parity
word must satisfy the Beatty/balance constraint $h_j\le\lfloor j\log_2 3\rfloor$ (a lower-Christoffel
condition).

## How it connects here

Same Diophantine core as the approach: $k/l\to\log_2 3$ is exactly $|2^E-3^o|$ small, and the
balance/Christoffel constraint on the parity word is the project's word geometry. The admissible cycle
lengths (convergent numerators of $\log_2 3$) are natural **target lengths $E$ for the combinator
search** — pruning input that complements the Halbeisen–Hungerbühler range filter
([[halbeisen-hungerbuhler1997-rational-collatz-bounds]]) and the Ellison size barrier
([[ellison1971-pillai]]).

## Open thread it touches

Supplies candidate $(E,o)$ for the search. Follow-ups (free PDFs located):
**Martiny 2015** (`mathematics.pitt.edu/.../Martiny 20-min-grad.pdf`, depth-19/21/22 convergents, min
period $>10{,}439{,}860{,}591$) and **Simons–de Weger 2005** (`deweger.net/papers/[35a]…v1.44[2010].pdf`).
