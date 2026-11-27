---
id: 0241
title: To refute metabelianity of a presented group, surject onto FreeGroup (Fin 2) via Presented
kind: pattern
created: 2026-11-28
---
Found by T-btz-surface-group-nonmetabelian. To refute metabelianity of a presented group, surject onto FreeGroup (Fin 2) via PresentedGroup.toGroup and use the strict GX.freeGroup_not_isMetabelianGroup; no finite group (S4) and no decide is needed. Surjectivity: MonoidHom.range_eq_top + FreeGroup.closure_range_of + Subgroup.closure_le, then fin_cases.
