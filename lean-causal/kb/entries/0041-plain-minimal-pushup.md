---
id: 0041
title: Plainness plus absolute minimality on a T1 space gives push-up
kind: pitfall
created: 2026-11-20
---
`Causality.pushUp_of_causallyPlain_of_absolutelyMinimal` (`CausalScaffold.DeuxPushup`): no local
(absolutely minimal) causality is causally plain without push-up, so do not look for one; a witness
needs a chronological relation with no point between (non-local, `Causal.deuxPushup`). The step:
absolute minimality on a T1 space makes every ≪_U interpolate — apply
`Precausality.AbsolutelyMinimalOn.exists_lt_inf` with O = {z}ᶜ
(`Causality.interpolatesOn_of_absolutelyMinimalOn`) (T-ett-deux-pushup).
