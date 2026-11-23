---
id: 0104
title: Stating an ℝP¹-isomorphism of two GammaLinkCircles' underlying circles inside an existential
kind: pattern
created: 2026-11-23
---
Found by T-bbs-hs-remark-existence. To state an RP1-isomorphism between the underlying RP1-circles of two GammaLinkCircles inside an existential, put `letI := C.rp1ChartedSpace θ; haveI := C.rp1_hasGroupoid θ` (and the same for C') in the statement itself. IsRP1Iso needs both the ChartedSpace and the HasGroupoid instances. The proof is (rp1Iso_iff_conj ⟨E, D, h.isLiftedDevPair⟩ ⟨E', D', h'.isLiftedDevPair⟩).2 (GX.exists_rp1Iso_not_isIso).
