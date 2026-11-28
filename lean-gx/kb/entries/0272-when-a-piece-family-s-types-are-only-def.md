---
id: 0272
title: When a piece family's types are only definitionally the Gluing's (pushPiece M N false = Fl
kind: pattern
created: 2026-11-28
---
Found by T-btz-gluing-dedupe. When a piece family's types are only definitionally the Gluing's (pushPiece M N false = FlatE0 N), ascribe the extension map's type ((regExt f y₀ : M → N)) or its implicit M unifies with the piece and instance search fails; rewrite range Subtype.val into the hypothesis (rw [← Subtype.range_coe (s := ...)] at h), not the goal, whose motive is not type-correct at instance transparency.
