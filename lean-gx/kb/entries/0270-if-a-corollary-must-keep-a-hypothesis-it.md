---
id: 0270
title: If a corollary must keep a hypothesis its general form no longer needs (SurgeryData.isCauc
kind: pattern
created: 2026-11-28
---
Found by T-btz-g3-dedupe. If a corollary must keep a hypothesis its general form no longer needs (SurgeryData.isCauchySurface_sigmaStar's `hrem`), give the general lemma an `_of_arc`-style variant that takes the same binder, so the corollary uses its argument and the unused-variables linter (warningAsError) stays quiet without renaming the binder.
