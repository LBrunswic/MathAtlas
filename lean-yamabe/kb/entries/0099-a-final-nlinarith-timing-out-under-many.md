---
id: 0099
title: A final nlinarith timing out under many set abbreviations
kind: pitfall
created: 2026-11-27
---
Found by T-yamabe-conformal-gap. In a long proof with many `set` abbreviations, a final nlinarith can time out at whnf on the whole declaration: replace it by an explicit `ring` identity plus linarith.
