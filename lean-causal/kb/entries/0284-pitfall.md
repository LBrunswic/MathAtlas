---
id: 0284
title: Pitfall:
kind: pitfall
created: 2026-11-25
---
Found by T-ett-geroch-iii-i (round 2, DEC-148/149). In term-mode `let ⟨…⟩ := e; …` patterns write `_`, not `-`; and a multi-line `fun p => let ⟨…⟩ := …` with the body on the next line does not parse: use `fun p => by obtain …; exact …`. Give map_mem_closure its function explicitly (f := fun w => (w, y)).
