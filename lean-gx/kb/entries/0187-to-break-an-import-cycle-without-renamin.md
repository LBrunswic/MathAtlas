---
id: 0187
title: To break an import cycle without renaming, move declarations into a base file while keepin
kind: pattern
created: 2026-11-27
---
Found by T-btz-pgcd-dom-gh. To break an import cycle without renaming, move declarations into a base file while keeping their `namespace` (several files may open GX.PpcmHausdorff); every full name and every downstream import keeps working (T-btz-pgcd-dom-gh: ExtChart.lean).
