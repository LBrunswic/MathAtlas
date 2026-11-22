---
id: 0229
title: InextensibleThrough on a smaller open needs only T1 on second countable spaces
kind: pattern
created: 2026-11-22
---
Where an original takes `InextensibleThrough U` only to pass it to an open `V ≤ U` (`InextensibleThrough.of_le`, which needs T2 and `≤_U` antisymmetric), its second countable form needs only T1: `InextensibleThrough V` holds directly (`inextensibleThrough_of_t1_secondCountable C V`). Example: `Jplus_inter_subset_of_isCauchySurfaceOn_of_t1_secondCountable`.
