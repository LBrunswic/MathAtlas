---
id: 0144
title: Transfinite recursion inside a proof, and dependent maps φ i j (h : r i j)
kind: pattern
created: 2026-11-21
---
get an opaque sequence with only its equation, obtain ⟨seq, hseq⟩ : ∃ seq : Ordinal.{0} → ι, ∀ α, seq α = F (range fun β : Iio α => seq β.1) := ⟨_, fun α => Ordinal.lt_wf.fix_eq (C := fun _ => ι) _ α⟩; ω₁ is a limit by Cardinal.isSuccLimit_omega 1 (then IsSuccLimit.succ_lt). Do not rewrite seq (succ α) = nx j under φ's dependent type: state the lemma for an arbitrary k with the hypothesis k = nx j and rintro ⟨j, hij, rfl⟩; store transports as ∃ T, ∀ β α h, T β α = φ _ _ h (a dite), so later statements carry no proof terms (T-abs-curves-extend-second-countable).
