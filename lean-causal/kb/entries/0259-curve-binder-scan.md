---
id: 0259
title: A grep for CurvesExtend binders misses inline curve hypotheses
kind: pitfall
created: 2026-11-23
---
A grep for `(h… : ….CurvesExtend(On) …)` misses curve hypotheses written out inline (SubExtension's `hthrough`). A `forallTelescope` scan of the elaborated binders over the ETT-layer modules finds them (about 20 s for 108 modules; T-abs-curves-free-cauchy's campaign probes). Its audit found three more inline binders the scan's criterion catches (`ers_lemma_4_70_core`'s `htrans`, `exists_box`'s `hpart`, `Jplus_mem_nhds_of_isAcausal`'s `hcov`): none is a curve-extension hypothesis, so none is owed a form.
