# Status — parity-manipulation

## Current state

Single-block shift fully understood for any sign of $a$, and we have a sharp structural verdict: **any finite-support perturbation only rewrites the past of a fixed downstream trajectory**. Single-block and arbitrary finite multi-block shifts produce trajectories $x'_k$ that agree with $x_k$ for $k$ past the perturbation's support — they re-parametrize the inverse Collatz tree without leaving it. To get genuinely new arithmetic content the perturbation must have **unbounded support**.

## Results

- **General single-block shift** $b'_k = b_k + a\,\mathbf{1}_{k\gt q}$ (see `derivation-general-shift.md`):
  - Tail: $x_0 - x'_0 = (2^a-1)\sum_{k\gt q} 2^{b_k}/3^{k+1}$.
  - Trajectory: $x_0 - x'_0 = -\,(2^a-1)\,2^{b_{q+1}}\,x_{q+1}/3^{q+1}$.
  - Head: $x'_0 - 2^a\,x_0 = (2^a-1)\sum_{k=0}^q 2^{b_k}/3^{k+1}$.
- **$3$-adic lemma (lifting-the-exponent):** $\nu_3(2^a - 1) = 0$ if $a$ odd, $= 1 + \nu_3(a)$ if $a$ even. Equivalently, $\text{ord}_{3^{q+1}}(2) = 2 \cdot 3^q$.
- **Integrality theorem:** for integer trajectories, $x_0 - x'_0 \in \mathbb{Z} \iff 2 \cdot 3^q \mid a$. Minimal admissible shift: $a = 2 \cdot 3^q$.
- **Dynamical meaning:** the family $\{a = 2 \cdot 3^q \cdot m\}$ at depth $q$ enumerates the depth-$(q+1)$ predecessors of $x_{q+1}$ in the Collatz inverse tree. Worked examples: $q=0, a=2$ recovers the $4x+1$ predecessor map; $q=1, a=6$ takes $1 \mapsto 113$ (a depth-2 predecessor).
- **3-adic propagation:** the obstruction is a per-step cost — each backward step from the perturbation point consumes one factor of 3, giving the threshold $\nu_3(2^a - 1) \ge q+1$.
- **Negative shifts $a \lt 0$:** same integrality condition ($|a| \in 2 \cdot 3^q \cdot \mathbb{Z}_{\ge 1}$) plus the validity bound $|a| \le c_{q+1} - 1$. They are the forward (successor) Collatz moves, exactly inverse to positive shifts. Example: $q=0, a=-2$ gives $x \mapsto (x-1)/4$, inverse of $4x+1$; $q=1, a=-6$ takes $113 \mapsto 1$.
- **Finite-support no-go (key structural takeaway):** if $\delta(k) := b'_k - b_k$ vanishes for $k \ge N$, then $x'_k = x_k$ for all $k \ge N$. So all finite-support perturbations — single-block, multi-block, mixed sign — only stitch a new past onto a fixed downstream node $x_N$. They cannot move us to a different trajectory; they enumerate predecessors of an existing one. The framework's content beyond the known Collatz tree must come from **infinite-support** perturbations.

## Dead ends

- $b'_k = b_k + \mathbf{1}_{k\gt q}$ alone ($a=1$): never gives integer differences for integer trajectories — confirmed by the general theorem ($a$ must be even, $a=1$ is not).
- Single-block shifts in general: integer-difference perturbations only generate the Collatz predecessor tree, which is already understood.
- **Any finite-support perturbation** (single- or multi-block, signs arbitrary): cannot escape the inverse Collatz tree of the original trajectory. The "future" $x_N, x_{N+1}, \ldots$ is preserved, only the "past" $x_0, \ldots, x_{N-1}$ is re-routed. So multi-block (which was the previous "next step") is ruled out as a source of new content **before** any computation — it's structurally a composition of single-block predecessor / successor moves.

## Open questions

- **Infinite-support perturbations** are now the only path forward. Three natural families:
  - **Periodic shifts** $\delta(k) = \pi(k)$ with $\pi$ periodic. Mean-zero $\pi$ may preserve eventual periodicity in step sizes (the rationality condition for $x'_0 \in \mathbb{Q}$); non-mean-zero $\pi$ changes the asymptotic density of halvings.
  - **Sub-linear growth** $\delta(k) = \lfloor \alpha k \rfloor$ or similar.
  - **Sparse but unbounded** $\delta$ supported on $\{q_i\}_{i \ge 1}$ with $q_i \to \infty$.
- For each: derive the analog of the trajectory-form identity and the integrality condition on $\delta$. The 3-adic accounting at each support point gives a local condition; the *infinite* combination of conditions is the new feature.
- Does requiring $(b_k)$ to come from a non-trivial cycle, together with an integrality constraint on an infinite-support perturbation, force a contradiction?
- Is there a perturbation that maps a hypothetical non-trivial cycle to the trivial cycle? Such a map would be a *positive* tool against the conjecture.

## Next step under consideration

Pivot to the **periodic-shift** case: $b'_k = b_k + \pi(k)$ with $\pi$ periodic of period $P$ and mean zero. Derive the analog of the trajectory-form identity (the termwise computation now produces an infinite product / sum that does not telescope to a single $x_{q+1}$). Identify the integrality condition. Periodic with $P = 1$ recovers the trivial uniform shift $b'_k = b_k + a$ — work that out as the warm-up, then $P = 2$.
