---
id: 0238
title: A forward rule with instance arguments pays a failing synthesis at every goal
kind: pitfall
created: 2026-11-22
---
An aesop forward rule with instance arguments that matches everywhere (a fact on every causality) pays a failing instance synthesis (about 8 ms for `T1Space M` on a bare space) at every goal of every search: `Causal.Ladder.Test` went from 4.7 s to 16.8 s. Make such a rule goal-directed (safe apply) unless another rule must read it (T-tac-ladder-integration).
