---
id: 0030
title: A BBS-layer module outside GX/{BTZ,Lorentz}/ may not import Causal.* (scripts/causal_import_gate.py)
kind: pattern
created: 2026-11-22
---
Found by T-bbs-hs-model. A BBS-layer module outside GX/{BTZ,Lorentz}/ may not import Causal.* (scripts/causal_import_gate.py). It gets Causal.Flat.{Form,Isometries,Penrose} through `import GX.Lorentz.Bridge` and qualifies every Causal name.
