---
id: 0152
title: E0Pushout forgets that ι₂ is an E₀-morphism
kind: pitfall
created: 2026-11-27
---
Found by T-btz-reg-complete. E0Pushout forgets that ι₂ : FlatE0 N → M̄ is an E0-morphism, and the curve-level transport needs it (only le_ι₂ on range ι₂ survives). Use GX.E0RegComplete.exists_e0Pushout_mor, which is exists_e0Pushout's construction returning that property as well.
