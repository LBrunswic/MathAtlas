# 0056 — push_neg is deprecated at this pin; its warning is an error in the strict library

*Found 2026-11-22 by T-bz-poche-nonconstant; recorded by the master session.*

`push_neg` is deprecated at this pin: it warns, and the strict library turns warnings into errors. Use `push Not`, or Classical.byContradiction (fun h => hc ⟨u, h⟩) for ¬∃ → ∀.
