---
id: 0194
title: In `obtain ⟨…⟩ := thm isOpen_Ioi …`, give a set argument only the goal fixes explicitly
kind: pitfall
created: 2026-11-22
---
Write `(A := Ioi 0)`. Otherwise elaboration stops on « typeclass instance problem is stuck: Preorder ?m »; under `exact` the expected type supplies it (T-ett-bubble-kplus).
