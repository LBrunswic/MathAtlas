---
id: 0243
title: To share proofs between a finite and a locally finite family of spears, state them over th
kind: pattern
created: 2026-11-28
---
Found by T-btz-reg-complete-graduate. To share proofs between a finite and a locally finite family of spears, state them over the common structure (E0Surgery.LFSpears: ι, D, disjoint, isClosed, locallyFinite) and give each family a toLFSpears; keep each family's own definitions (sigmaStar, logRad) with identical bodies, so `X.toLFSpears.sigmaStar = X.sigmaStar` is rfl and the old lemmas become one-line terms `Dat.toLFSpears.foo ...` that the elaborator accepts by unfolding, with no rewrite and with downstream `rw [SurgeryData.logRad, if_pos h]` unchanged.
