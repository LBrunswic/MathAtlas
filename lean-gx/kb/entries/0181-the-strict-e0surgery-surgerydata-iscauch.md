---
id: 0181
title: The strict isCauchySurface_sigmaStar asks for more than it needs
kind: pattern
created: 2026-11-27
---
Found by T-btz-reg-complete-cauchy. The strict E0Surgery.SurgeryData.isCauchySurface_sigmaStar's hS : IsE0C1SpacelikeCauchy and hrem are both stronger than needed: IsCauchySurface S suffices, and hrem is SpearSurgeryDatum.isSpearArc_of_inextensible applied spear by spear. A strict cleanup could restate it over LFSurgeryData, of which the finite SurgeryData is a case (sigmaStar_toSurgeryData is rfl).
