---
id: 0178
title: Inside Causal.X with open SFALocal, isClosed_sing resolves to the root Causal.isClosed_sing
kind: pitfall
created: 2026-11-21
---
The strict root `Causal.isClosed_sing` (every singular (G,X)-manifold, explicit `G X M`) shadows `SFALocal.isClosed_sing` for an unqualified name; the error is « expected Type ». Write `SFALocal.isClosed_sing` (T-ett-sfa-massive-line).
