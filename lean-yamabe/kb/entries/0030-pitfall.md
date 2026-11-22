---
id: 0030
title: Pitfall:
kind: pitfall
created: 2026-11-22
---
Found by T-yamabe-rellich-criterion. Pitfall: Lp.coeFn_zero takes E p μ explicitly (Lp.coeFn_zero F p μ); Lp.coeFn_add, Lp.coeFn_smul, Lp.dist_def and MemLp.toLp need no Fact (1 ≤ p), so a section variable [Fact (1 ≤ p)] must be omitted there (unusedSectionVars, a failure under warningAsError).
