---
id: 0101
title: A vector-literal pitfall in finite models
kind: pitfall
created: 2026-11-27
---
Found by T-perf-capacity-remarks. pitfall: norm_num [Matrix.cons_val] does not evaluate ![a,b,c,d] 3 at this pin. simp only [Matrix.cons_val_three, Matrix.cons_val_two, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.tail_cons, Matrix.head_cons] does, and is packaged as CapRemarks.vecLit / vecLit3.
