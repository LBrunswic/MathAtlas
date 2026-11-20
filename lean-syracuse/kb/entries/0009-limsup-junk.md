---
id: 0009
title: A real limsup is a junk value when unbounded above: state boundedness beside it
kind: pattern
created: 2026-11-20
---
Found by T-syr-integer-bounds. State `IsBoundedUnder (· ≤ ·)` beside `limsup … ≤ L`; prove it by `limsup_le_of_le` + `isCoboundedUnder_le_of_le` + `le_of_forall_pos_le_add` from an ε-eventually form. `Filter.Tendsto.cesaro` gives Cesàro means. Also: scaffold modules of one wave do not see each other, so suffix ℤ-specific helpers (`_int`) to avoid a clash at graduation.
