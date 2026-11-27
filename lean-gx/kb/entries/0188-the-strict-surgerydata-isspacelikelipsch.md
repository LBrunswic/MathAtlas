---
id: 0188
title: The strict SurgeryData.isSpacelikeLipschitzAt_cusp_interior/_rim and the logRad stack (abs
kind: pattern
created: 2026-11-27
---
Found by T-btz-reg-complete-length. The strict SurgeryData.isSpacelikeLipschitzAt_cusp_interior/_rim and the logRad stack (abs_deriv_logRad_le ... ofReal_abs_logRad_sub_le_edist) need neither finiteness nor compactness: copied verbatim over LFSurgeryData they compile with one change (the union of the other spears is closed by LocallyFinite.comp_injective ... isClosed_iUnion) and hS.reg in place of IsE0C1SpacelikeCauchy; a strict clean-up could state them once over LFSurgeryData (finite SurgeryData is a case, sigmaStar_toSurgeryData is rfl).
