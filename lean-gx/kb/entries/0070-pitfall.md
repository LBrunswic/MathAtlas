---
id: 0070
title: Pitfall:
kind: pitfall
created: 2026-11-23
---
Found by T-3p1-funnel-gtilde. Pitfall: push_cast on a goal containing (l.prod : GTilde) x pushes the Subgroup coercion into the list, giving (List.map Subtype.val l).prod x, and linarith then misses every hypothesis about l.prod x. Rewrite the numeric casts by hand (Nat.cast_succ, Int.cast_sub, Int.cast_natCast).
