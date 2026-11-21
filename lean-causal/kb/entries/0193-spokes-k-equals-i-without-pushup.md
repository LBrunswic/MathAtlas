---
id: 0193
title: Spokes: a cheap local witness with K⁻(o) = I⁻(o) while push-up fails at o
kind: pattern
created: 2026-11-22
---
Below the slice t = 0, `spokesCausality`'s ≤ is Minkowski's « = or ≪ » (`Causal.spokes_eq_or_lt_of_le`), so J⁻(u) ⊆ {u} ∪ I⁻(u) for u.1 < 0, and K⁻(o) = I⁻(o) at the origin (`Causal.spokes_Kminus_origin_eq_Iminus`) while push-up fails there in both senses (`spokes_not_plain_at_origin`, `spokes_not_pushUp_at_origin`). `Causal.spokes_bubble_witness` works on ℝ × E for any open cone A with a non-zero point; it meets prop:tarentin_fort_K's topological hypotheses only for E separable (second countability), e.g. ℝ or ℂ (T-ett-bubble-kplus).
