# The /atlas-team journal

One entry per iteration, appended by the loop (`.claude/skills/atlas-team/SKILL.md`, step 6).

## 2026-11-20 13:40 · close · T-ett-cbg-anchor
- result: 10/10 rows stated and anchored (Causal.CBG.ETTSection4, strict), all partial over an abstract Geometry until T-ett-port-e0; ETT 119 stated / 57 closed / 58 partial (was 109 / 57 / 48)
- findings: prop:Cauchy_non_max false with the literal C (counterexample on Minkowski space); prop:Cauchy_point_min vacuous with the literal C; proof gaps at l.2303, cor:ext_continue, theo:CBG's directed limit; rem:CBG_analytique needs A3/A4
- questions: OQ-25 (sing_α reading, model_corresponding scope), OQ-26 (the pgcd of defi:ppcm)
- audit: minor (round 1), folded into the curation
- gates: lean-causal ✓ (196 modules, 11926 decls, 0 strict sorry), roadmap ✓, atlas ✓, hub: no new red
- commits: 8e7e7ee 347e1cb 7c5ef82
- next: close T-ett-unanchored (p2), or set up T-bbs-ledger (p2, master); T-ett-port-e0 (p4) unlocks the 10 rows above

## 2026-11-20 14:27 · close · T-ett-unanchored
- result: 17/17 rows dealt with: 13 stated and partial (Causal.Remarks.BTZPoints, .Tarentin, .MassiveManifold, strict, sorry-free, unmarked), 4 not attempted with the missing infrastructure recorded (rem:terminology_borrowed_archytas_tarentum: no assertion; theo:geroch_mr, prop:GX_sing_dec: smooth structure; lem:vecteur: differentiable structure); ETT 131 stated / 57 closed / 70 partial (was 119 / 57 / 58)
- findings: rem:pas_plat (ii) a BTZ point does not violate causal plainness; cor:K_lorentzien's proof omits plainness; cexemple:misner_tarentin's inference needs J⁺(x) ∉ 𝓝 x; cor:massA_causalite's proof checks the wrong hypotheses; rem:recursion_these's hypotheses beyond A ∩ U₁ = ∅ unnecessary
- questions: OQ-27 (Misner J⁺), OQ-28 (regularity of 'Lorentzian'), OQ-29 (recursion seed), OQ-30 (anchor the informal FZenon remark?), OQ-31 (Archytas gloss)
- audit: minor (round 1: non-local witness overclaimed, hreg undisclosed, smoothness sentence, docstring contract), fixed by the closer, checked by the master
- gates: lean-causal ✓ (199 modules, 12014 decls, 0 strict sorry), roadmap ✓, atlas ✓, hub: no new red
- commits: 5e1b357 b2cbc51 458f216
- note: the lock's pid was a dead Bash subshell's ($$), so the liveness check could not see the previous iteration; this lock held the session process's pid instead
- next: set up T-bbs-ledger (p2, master, rule 4); the builder (T-atlas-lean-dag) comes due the iteration after

## 2026-11-20 14:36 · set up · T-bbs-ledger
- result: papers/bbs counted as an external paper (DEC-132, Barbot's DEC-34 wave 0 as the model): snapshot of colI_v1.tex, 71 bbs-prefixed labels, ledger rooted in lean-gx (71 statements, none Lean-stated), curation (4 rows proved where the argument is not a following proof environment, 2 open with no proof in the paper), a three-fragment reading map
- gaps left: the statement DAG has no edges (the authors' \ref's target secondary labels, unresolved by texgraph, as for Barbot); the atlas does not list bbs yet (extract.py PAPERS and hub.toml's "no ledger" badge are the builder's)
- audit: none (master set-up, no agent)
- gates: roadmap ✓, atlas ✓, papers_check all green, hub make -k check ALL GREEN; [gates] known_red emptied
- commits: 0e44367 6884f56
- next: build T-atlas-lean-dag (rule 3: no builder run in the last three iterations); give the builder the bbs listing too

## 2026-11-20 15:26 · build · T-atlas-lean-dag
- result: atlas: Lean dependency edges between labels, through principals (tools/doubledag.py), each with its witness chain (file:line), drawn on the statement DAG with toggle and legend; ETT 48 both / 1036 lean-only / 120 tex-only, Barbot 0 / 103 / 0, gx 29 / 890 / 26; Benzécri and bbs none yet; facts from lean-causal 5e1b357, lean-gx and lean-benzecri 18d8c16; default build Lean-free (make -C reports/atlas lean refreshes); bbs listed as a ledgered paper (71 rows)
- findings: 37 ETT curation decls carry a prose prefix "(related, curve reading (b), CausalScaffold.ChainsCurves)" and resolve to nothing (def:causally_complete 28, rem:causal_completeness_slightly_weaker 9); the committed GFN Bounds double DAG no longer matches its inputs (1,879 vs 2,344 mapped declarations); Benzécri's ledger maps no label to a declaration (names only in scope_notes)
- audit: builder self-check + master: two forced rebuilds byte-identical, headless Chromium 0 page errors
- gates: roadmap ✓, atlas ✓, hub make -k check all green
- commits: 8afcced aa2c707
- next: close T-ett-geroch-iii-i (rule 4); the planner comes due at the next iteration after (five iterations without one) — the three findings above are for it

## 2026-11-20 16:14 · close · T-ett-geroch-iii-i
- result: blocked on OQ-32: theo:geroch's (iii)⇒(i), and the equivalence, are FALSE as printed (chronological Minkowski space satisfies every hypothesis, (ii) and (iii), not (i); sorry-free, audited); the formalized theo:geroch_sing is false too (OQ-33), the paper's not refuted; Causal.LimitCurves graduated (sorry-free infrastructure); CausalScaffold.GerochCauchy holds the counterexample and a conjectured repair ('≤ closed', one open sorry)
- questions: OQ-32 (which repair, and does the compactness lemma hold), OQ-33 (local closedness in SingularFlatAxioms)
- audit: minor (round 1: repair overstated, a citation, a 'time function' wording), fixed by the closer
- gates: lean-causal ✓ (0 strict sorry in 199 files), roadmap ✓, atlas ✓ (Lean overlay refreshed), hub make -k check all green
- commits: 5cccb12 f2938c6
- note: the author's 1bc58a7 (waves of parallel targets, MAX_PARALLEL 6) landed mid-iteration; this iteration finished under the one-target protocol, the next runs as a wave
- next: plan (rule 2: five iterations without a planner run); the planner gets the atlas builder's findings (37 malformed ETT decls, stale GFN double DAG, Benzécri unmapped decls) and the BBS \ref-edge gap

## 2026-11-20 16:37 · plan · —
- result: planned 20 new targets, re-scoped 4 (24 -> 44), roadmap wave-ready (package / depends / exclusive); the loop's findings are targets (T-ett-curation-decls, T-bz-curation-decls, T-ledger-secondary-labels, T-gfn-doubledag-refresh)
- new needs-ruling: T-gfn-doubledag-refresh (regenerate the GFN double DAG or pin the 09-20 measurement), T-bbs-layer-home (BBS-Q1: lean-gx or a new lean-bbs), T-barbot-terminal (leave bucket T?)
- planner notes: package = "none" for master curation targets counts as one more package (cap 3); nothing promotes a planned target when its dependencies close, so chains (port-e0 -> port-e0-sfa) wait for a planner run; T-ett-minkowski-graduate is a graduation; T-ett-cbg-e0 would port a ~52k-line gx import cone
- gates: roadmap ✓, atlas ✓, hub make -k check all green
- commits: 81cb8fe
- wall time: 15:16–16:12; agents in parallel: 1 (planner, alone)
- next: wave of 6: T-ett-ruled-rows, T-bz-universal-cover, T-egf-package, T-ett-port-e0, T-3p1-theorem-m, T-ledger-secondary-labels

## 2026-11-20 17:39 · wave of 6 · T-ett-ruled-rows, T-ledger-secondary-labels, T-egf-package, T-ett-port-e0, T-bz-universal-cover, T-3p1-theorem-m
- T-ett-ruled-rows (master): closed 3/3 rows as DEC-7/DEC-8 rule (ETT 57 -> 60 closed)
- T-ledger-secondary-labels (master): texgraph resolves refs to a statement's secondary labels; bbs 0 -> 17 edges, ett +1; Barbot still 0 (its \preua proofs are not parsed: a separate gap, for the planner)
- T-egf-package (master): lean-egf created (Mathlib-only wave 0), make check green, EGF ledger rooted in it
- T-ett-port-e0: E₀ ported verbatim from gx (Causal.Port.E0*, Causal.E0.btzAxioms); defi:causal_E0 partial on readings OQ-34, OQ-35; audit minor (round 1)
- T-bz-universal-cover: closed 1/1 (Benzécri 36/38 closed), marked; universal cover ported Mathlib-only; audit minor (fixed at graduation)
- T-3p1-theorem-m: research partial: Theorem M's holonomy half proved (scaffold); Θ₋ = Θ₊ needs an HS²/ℝP¹/G̃ layer (for the planner); the notes' orientation conventions disagree (OQ-36); audit minor (round 1)
- gates: lean-causal ✓ (0 strict sorry, 202 files), lean-benzecri ✓, lean-gx ✓, lean-egf ✓, roadmap ✓, atlas ✓ (overlay refreshed, egf added), hub make -k check all green (papers-check red mid-wave only until the ledgers were regenerated after the work commits, as the protocol orders)
- commits: 25da51a 43c0840 4a0e1d4 0fe9136 2ed332b 7a47172 4f60649 cd18d22
- wall time: 16:39–17:39 (Paris); agents in parallel: 3 closers (+3 auditors), 3 master set-ups
- next: wave: T-ett-subextension,T-gx-spherical-cone,T-ett-minkowski-graduate,T-ett-k-borelien,T-gx-slsc-compact,T-ett-curation-decls
- for the planner: planned targets whose dependencies just closed (T-ett-port-e0-sfa, T-ett-e0-model-rows, T-egf-headline) are not promoted by the loop; a Θ-half target for Theorem M; Barbot's \preua proof parsing

## 2026-11-20 19:05 · wave of 6 · T-ett-curation-decls, T-ett-minkowski-graduate, T-ett-k-borelien, T-ett-subextension, T-gx-spherical-cone, T-gx-slsc-compact
- T-ett-curation-decls (master): the 37 prose-prefixed decls moved to notes (DEC-21); ledger.py check refuses a decl that is not a Lean name (fixture added); the stale registers `references` fixture repaired, so `make selftest` passes again
- T-ett-minkowski-graduate: audit minor (no closer: the file was sorry-free but unaudited); Causal.MinkowskiMeasure graduated, docstrings and 7 stale references fixed, the row explicitly partial (instance only), bucket D
- T-ett-k-borelien: rem:K_borelien FALSE as printed (Minkowski space with spokes, local, from a non-Borel subset of ℝ); strongest true forms proved; audit minor (round 1)
- T-ett-subextension: both rows anchored over the CBG geometry (partial until T-ett-cbg-e0); the abstract cauchy_pgcd refuted for non-local causalities (directional and morphism-requiring symmetric readings; the generated equivalence not refuted); audits minor (2 rounds)
- T-gx-spherical-cone: (SO(4), 𝕊³), spherical cones, cone-angle invariance, Thurston suspension (strict); TroyanovSuspensionTheoremS3 stated (2 tagged sorrys); readings OQ-37; audit minor (round 1)
- T-gx-slsc-compact: the Griffiths twin cone (compact Peano continuum) refutes the iff, sorry-free, self-contained non-null-homotopy; audit minor
- gates: lean-causal ✓ (0 strict sorry, 206 files), lean-gx ✓ (0 strict sorry, 48 files), roadmap ✓, atlas ✓, selftest ✓, hub make -k check all green
- commits: 68ad60e 04ac55f acab730 8ecc33f 491f924 7d7d6fa 24d9429 11f649a b308ecb 5cefc9a
- wall time: 17:41–19:05 (Paris); agents in parallel: 4 closers + 1 auditor-only target, 9 audits (incl. 1 re-audit), 1 master target
- next: wave: T-ett-deux-pushup,T-bz-curation-decls,T-bz-chapter2,T-syracuse-package,T-yamabe-package

## 2026-11-20 19:47 · wave of 5 · T-ett-deux-pushup, T-bz-curation-decls, T-bz-chapter2, T-syracuse-package, T-yamabe-package
- T-ett-deux-pushup: rem:deux_pushup's independence witnessed in the library's reading; the plain-without-push-up witness is NON-local, necessarily (on T1: absolutely minimal + causally plain ⇒ push-up); OQ-39 (with OQ-18); audit minor; kept in the scaffold — graduation deferred because /ett-programme's closers were working in lean-causal (strict library frozen)
- T-bz-curation-decls (master): the 36 closed Benzécri rows name their declarations (checked against the environment)
- T-bz-chapter2 (master; the transcription drafted by an agent from the page images, snapshotted, labelled and ledgered by the master): Chapter 2, pp. 246–259, 28 rows (66 total), TO BE CHECKED BY THE AUTHOR; result B leaves T; editorial choices OQ-38
- T-syracuse-package, T-yamabe-package (master): lean-syracuse, lean-yamabe (Mathlib-only wave 0), make check green, Dropbox-ignored, ledgers rooted in them
- protocol change mid-wave: c6dc0bb (the author's /ett-programme) moved /atlas-team to path leases, `git commit --only` and per-paper ledger rebuilds; applied from 041ae20 on
- gates: lean-syracuse ✓, lean-yamabe ✓, lean-causal: DeuxPushup typechecked (warningAsError), package check deferred (programme closers active); roadmap ✓, atlas ✓; hub: papers-check RED for papers/sbierski-mghd and papers/ers-predictability only — /ett-programme's papers (its lease), stale after my lean-causal commit 286cebe; the programme loop rebuilt them on request (89d49b8): papers_check all green again before the push
- commits: cef20e6 0b6a128 979b864 041ae20 2492979 286cebe 8bd43e5 bed0110 673464a
- wall time: 19:07–20:40 (Paris); agents in parallel: 1 closer + 1 transcriber, 1 audit, 4 master set-ups
- next: wave: T-ett-gxsingular-dec25; owed: graduate CausalScaffold.DeuxPushup at the next lean-causal integration with no programme closer in the package; planned targets with done dependencies await a planner run

## 2026-11-20 20:14 · plan · —
- result: 44 -> 69 targets (18 ready, 18 planned, 6 needs-ruling, 4 blocked); promoted the targets the last waves unblocked; a full Benzécri Chapter 2 plan; first targets for lean-syracuse and lean-yamabe; Theorem M's Θ-half layers; follow-ups as targets (DeuxPushup graduation gated on lean-causal being free, pgcd retirement, Barbot proof macros, hub.toml refresh); nothing duplicating /ett-programme's roadmap
- new needs-ruling: T-yamabe-scope (which §6 analysis is a named external), T-egf-families (the two spectral-gap theorems: externals or proved), T-bz-transcription-check now covering Chapter 2
- gates: roadmap ✓, atlas ✓, hub make -k check all green
- commits: 4d9a2da
- wall time: 19:50–20:40 (Paris); agents: 1 (planner, alone)
- next: wave: T-egf-headline,T-bz-c2-poches,T-bz-c2-mesure,T-gx-cone-football,T-syr-base,T-yamabe-quotient (no lean-causal: /ett-programme's closers are there)

## 2026-11-20 21:25 · wave of 6 · T-syr-base, T-gx-cone-football, T-yamabe-quotient, T-bz-c2-poches, T-bz-c2-mesure, T-egf-headline
- T-syr-base: def:define_n__n_ closed; def:ring_define, def:ring_define_2, lem:base, lem:ring_maps_rhs_n_ partial on findings of the printed text (f_A's cases swapped; T_A undefined at −1/3 when 3 is a unit; Z/2Z is a Z/2Z-ring with 2 = 0), strongest true forms proved, OQ-42; audit major (an accidental bold mark), round 1, AUDIT-2 clean; ledger.py learned `class` and `scoped`
- T-gx-cone-football: the football F_θ, the first IsConeSphere with genuine cone points; cex:start_singular_manifold_homeomorphic stays partial (s = 2 < 3); audit minor
- T-yamabe-quotient: lem:stability and rem:sign proved over an abstract measured model, partial pending T-yamabe-scope and OQ-44; eq:hoelder's boundary line false as printed (exponent 1/(N−1), sharp); audit minor, round 1
- T-bz-c2-poches: closed 7/7 (Ch. 2 § 1); the unlabelled examples need p injective (OQ-46); audit minor, round 1
- T-bz-c2-mesure: closed 5/5 (Ch. 2 § 2, Déf. 1–4, Prop. 1); property 1° fails in dimension 0 (OQ-45), to be passed to the T-bz-c2-proprietes and T-bz-c2-hilbert dispatches; audit minor, round 1; owed: Poches and Mesure both prove the chart change on a projective segment and GS(E)'s action on closed segments (kb 0006), keep one copy in a later target
- T-egf-headline: closed 2/4 — theo:universality_true (Lean ≥ paper; the general form needs only γ₀ < ∞, γₙ → 0) and def:summably_mixing; def:egf, def:universal_family partial on OQ-48–50; both marks rest on the confirmation OQ-47; audits minor (round 1), minor (wording, fixed at graduation)
- gates: lean-syracuse ✓, lean-gx ✓, lean-yamabe ✓, lean-benzecri ✓ (0 sorry, 31 strict files), lean-egf ✓ (0 sorry, 130 strict declarations), roadmap ✓, atlas ✓ (Lean overlay refreshed for the wave's six papers; the four lean-causal papers' overlay left stale for /ett-programme), hub make -k check all green
- commits: 895d501 f382449 e4e12c0 4621f2b 254419e 245693e a3690fd 742a9c5 599595d b62ca3a
- wall time: 20:16–21:25 (Paris); agents in parallel: 6 closers, 8 audits (2 re-audits), 5 fix rounds
- next: wave: T-ett-deux-pushup-graduate (exclusive in lean-causal, coordinated with /ett-programme), T-gx-troyanov-triangle, T-bz-c2-projection, T-bbs-triage, T-barbot-proof-macros (the builder T-atlas-hub-refresh if due)

## 2026-11-20 23:10 · wave of 6 · T-ett-deux-pushup-graduate, T-barbot-proof-macros, T-bbs-triage, T-atlas-hub-refresh, T-bz-c2-projection, T-gx-troyanov-triangle
- T-ett-deux-pushup-graduate (master): Causal.DeuxPushup strict (file move, no statement changed); rem:deux_pushup stays partial (OQ-39); done in a window /ett-programme opened for it, lean-causal leased and handed back
- T-barbot-proof-macros (master): texgraph reads a paper's proof macros (`proof_macros` in ledger.toml); papers/barbot 0 → 17 dependencies, 28/44 statements with a proof; ledger check fails on a macro that opens no proof (fixture); every other ledger byte-identical
- T-bbs-triage (master): 71 rows bucket D, each with its REVIEW §A row, layer and wave; no row needs only L0–L1, so bbs close targets wait on BBS-Q1 (T-bbs-layer-home)
- T-atlas-hub-refresh (builder): hub.toml current; lib cards for every package; two -B rebuilds byte-identical, 0 page errors (re-checked by the master)
- T-bz-c2-projection: Ch. 2 § 3 Prop. 1 proved sorry-free for n ≥ 1, unmarked, partial on OQ-45 (a) (false as printed for n = 0); a slip in the printed 1°; audit minor, fixed at graduation
- T-gx-troyanov-triangle: Troyanov's theorem for s = 3 (GX.troyanovTheorem_three, exactly TroyanovTheorem at s = 3) by doubling a spherical triangle, sorry-free; Troyanov reduced to s ≥ 4; cex row stays partial; audit minor, fixed at graduation; owed to T-gx-troyanov: l.1930's bound against MR1005085
- gates: lean-causal ✓, lean-benzecri ✓, lean-gx ✓, roadmap ✓, atlas ✓ (overlay refreshed for lean-gx, lean-benzecri; lean-causal's stays stale while /ett-programme holds it); hub: papers_check all green, one red not this wave's (gate-tests: /ett-programme's in-flight ladder.toml not re-emitted, its lease)
- commits: c628a74 d2af417 5c3474e a06acc2 dbccb84 6d457b8 d6cd71b 6195fbb 3591466 bd9c8f8
- wall time: 21:23–23:10 (Paris); agents in parallel: 2 closers + 1 builder, 2 audits; 4 master targets
- coordination: shared cap 6 with /ett-programme (3 + 3, then 1 + 5); OQ-id race caught before it landed (the programme's rows renumbered OQ-51, OQ-52)
- next: plan — the only ready closers are in lean-causal (T-ett-port-e0-sfa, T-ett-e0-model-rows, T-ett-gxsingular-dec25), which /ett-programme holds exclusively; planned targets whose dependencies are now all done (T-bz-c2-hilbert, T-syr-rep, T-syr-integer-bounds, T-egf-backward-policy) await promotion; T-bz-c2-lignes, -compact, -theoreme and T-egf-sampling follow in chain

## 2026-11-20 23:40 · plan · —
- why: the only ready closers were in lean-causal, which /ett-programme held exclusively; four planned targets had every dependency done
- result: 69 -> 78 targets (17 ready, 15 planned, 7 needs-ruling, 4 blocked after the master set T-egf-universality blocked on OQ-50); promoted T-bz-c2-hilbert (carries OQ-45), T-egf-backward-policy, T-syr-rep, T-syr-integer-bounds; added T-bz-c2-dedupe (master, exclusive), T-gx-troyanov-two-pi, T-gx-troyanov-polygon, T-gx-troyanov-source (archive MR1005085, check l.1930's bound), T-syr-completion, T-yamabe-kobayashi (part a), T-egf-universality, T-bbs-q1 (needs-ruling: BBS-Q1 as a gate), T-atlas-sweep-refresh; T-gx-troyanov retitled to s ≥ 4; bbs layers now depend on T-bbs-q1
- [r] findings handed to closers, not the author: Syracuse at x = 1 (lem:itemize_furthermore_itemize's second bullet, cor:bounds), −1/3 for the continuous extension, i = j in theo:rep's corollary
- gates: roadmap ✓, atlas ✓
- commits: (this one)
- wall time: 23:15–23:40 (Paris); agents: 1 (planner, alone)
- next: wave: T-egf-backward-policy, T-bz-c2-hilbert, T-gx-troyanov-two-pi, T-syr-rep, T-syr-integer-bounds (5 slots: /ett-programme has 1 lean-causal closer)

## 2026-11-21 00:25 · wave of 5 · T-egf-backward-policy, T-bz-c2-hilbert, T-gx-troyanov-two-pi, T-syr-rep, T-syr-integer-bounds
- T-gx-troyanov-two-pi: a regular point is a cone point of angle 2π (GX.IsConePoint.of_mem_reg); TroyanovTheorem ⇔ its case s ≥ 4 with every θ_i ≠ 2π; cex row stays partial; audit clean
- T-syr-integer-bounds: lem:one_has and cor:corollary_2 closed as printed; lem:itemize_furthermore_itemize and cor:bounds false as printed (x = 1, n = 0), true forms proved unmarked (OQ-54); audit minor
- T-syr-rep: theo:rep proved on RepDomain over ℤ_[2] (false as printed on −1/3's backward orbit, OQ-42 (d)); the first corollary needs integrality (OQ-42 (a): fails in ℤ × ℤ/3ℤ); the second true for i ≠ j (OQ-53); all three partial; audit minor
- T-egf-backward-policy: the backward star policy defined; theo:backward_policy false as printed in the appendix's setting (non-ergodic formal counterexamples, ergodic ones by hand), corrected forms proved (OQ-55); audit minor
- T-bz-c2-hilbert: Props. 2 and 3 proved for n ≥ 1, unmarked (OQ-45; Prop. 2's literal reading holds in every dimension, OQ-56); 5°, 6° as lemmas; audit minor
- gates: lean-gx ✓, lean-syracuse ✓, lean-egf ✓, lean-benzecri ✓, roadmap ✓, atlas ✓ (overlay refreshed for five packages), hub make -k check all green
- commits: d206dd5 dcfcf8c 5ff0a6b 7b5c4d5 56301de b2446d2 eb9357f e6fbc28 30ad559 0c4987c
- wall time: 23:42–00:25 (Paris); agents in parallel: 5 closers (+1 /ett-programme closer, shared cap 6), 5 audits; each target integrated as soon as its audit returned (its package had no other closer)
- coordination: OQ ids raced twice with /ett-programme (OQ-55, OQ-56 taken mid-wave, its next free announced each time)
- next: wave: T-bz-c2-dedupe (master, exclusive), T-yamabe-kobayashi, T-ett-port-e0-sfa (lean-causal: share per-package 3 with /ett-programme), T-gx-troyanov-polygon, T-syr-completion, T-gx-troyanov-source (master)

## 2026-11-21 01:15 · wave of 6 · T-bz-c2-dedupe, T-yamabe-kobayashi, T-gx-troyanov-polygon, T-syr-completion, T-gx-troyanov-source, T-ett-port-e0-sfa (topped up)
- T-bz-c2-dedupe (master): Mesure imports Poches and keeps its five twins as one-line derivations; no statement changed, the five rows stay closed
- T-yamabe-kobayashi: lem:kobayashi (a), its in-particular and the constant-curvature equality over the measured model with curvature (Yamabe.CurvedMetric); partial (T-yamabe-scope, OQ-44); eq:hoelder's \label numbers the false boundary line; audit minor
- T-gx-troyanov-polygon: Troyanov for every s with all angles < 2π (doubling a convex spherical s-gon; the subcritical form too); TroyanovTheorem reduced to s ≥ 4 with some angle > 2π; at s = 4 the printed condition is sufficient, not necessary; audit clean
- T-syr-completion: A₂ ≅ ℤ₂ for integral A with 2 ≠ 0 (UniformSpace.Completion); f_A extends; T_A extends only off −1/3 (false as printed); l.52 false for ℤ/2ℤ; integrality needed (ZMod 4); audit minor (the refutation now negates exactly the printed claim)
- T-ett-port-e0-sfa (topped up when /ett-programme freed lean-causal): E₀ satisfies SingularFlatAxioms with sing₀ = axis, the first witness with sing₀ ≠ ∅; verbatim port of gx (144 constants' elaborated types checked); def:singular_spacetime stays partial (OQ-34/35); audit minor
- T-gx-troyanov-source (master): not done, back to ready: ams.org answers 403 to automated fetches; needs the author's PDF of MR1005085 in papers/gx/sources/MR1005085/
- gates: lean-benzecri ✓, lean-yamabe ✓, lean-gx ✓, lean-syracuse ✓, lean-causal ✓ (223 strict modules), roadmap ✓, atlas ✓ (overlay current for all ten papers), hub make -k check all green
- commits: b587783 b4605cc d36aa9a d676822 bed88aa 76fc80e f06d72d 26bdd27 596352f e4bffd7 4d73d4f
- wall time: 00:27–01:15 (Paris); agents: 4 closers, 4 audits, 1 fetch attempt; 2 master targets
- coordination: lean-causal leased from /ett-programme for the exclusive E₀ port, its four ledgers rebuilt here; binder.toml leases narrowed for its planner
- next: the only ready closers are lean-causal's (T-ett-e0-model-rows, T-ett-gxsingular-dec25); planned targets need promotion — plan, or a lean-causal wave shared with /ett-programme

## 2026-11-21 01:50 · plan · —
- why: rule 2 (fewer than two ready closers outside lean-causal, which /ett-programme held exclusively for T-abs-hoist-cbg-cores)
- result: 78 -> 86 targets; promoted T-bz-c2-lignes (narrowed to Déf. 5, Props. 4, 6, with 7°) and T-egf-sampling (narrowed to the sampling and negative-control theorems; OQ-55 does not enter them); added T-bz-c2-pseudo-boules, T-gx-troyanov-four (s = 4 with an angle > 2π, by a spherical dart, [r]), T-gx-troyanov-reroute (master), T-syr-cycle-gcd, T-yamabe-gluing-algebra, T-egf-sampling-corollaries (planned; Pinsker is not in Mathlib), and two needs-ruling targets: T-syr-cited (named externals for theo:mr, theo:matveev, the computer check of l.201) and T-syr-empty-corollary (cor:corollary is an empty environment); T-gx-troyanov retitled to s ≥ 5 and no longer waits on the source; T-gx-troyanov-source no longer needs the author: the paper is author-hosted (sma.epfl.ch), fetchable once the server's missing DigiCert intermediate is supplied
- gates: roadmap ✓, atlas ✓
- wall time: 01:25–01:50 (Paris); agents: 1 (planner, alone)
- next: wave outside lean-causal: T-egf-sampling, T-bz-c2-lignes, T-gx-troyanov-four, T-bz-c2-pseudo-boules, T-syr-cycle-gcd, T-yamabe-gluing-algebra; master: T-gx-troyanov-source, T-gx-troyanov-reroute, T-atlas-sweep-refresh

## 2026-11-21 02:45 · wave of 6 · T-egf-sampling, T-bz-c2-lignes, T-bz-c2-pseudo-boules, T-gx-troyanov-four, T-gx-troyanov-source, T-ett-e0-model-rows (topped up)
- T-egf-sampling: def:virtual_flows, theo:sampling_theorem, theo:negative_control (+ appendix) closed and marked; the sampler constructed (Ionescu-Tulcea), sharp bound; confirmations OQ-60; audit minor
- T-bz-c2-lignes: Déf. 5, Prop. 4 for n ≥ 1 (OQ-45); Prop. 6 and 7° false as printed for a pocket with cote z ≡ 0 (checked on the scan), ≤ and z ≢ 0 forms proved (OQ-61); audit minor
- T-bz-c2-pseudo-boules: Déf. 6 closed; Prop. 5 for r > 0 (OQ-62: does « positif » mean > 0?); audit major on text (the r ≤ 0 « finding » withdrawn, round 1), AUDIT-2 minor
- T-gx-troyanov-four: Troyanov for every s = 4 datum (a spherical dart); TroyanovTheorem ⇔ its case s ≥ 5 with an angle > 2π; generic StarPolygon double; audit minor
- T-gx-troyanov-source (master): Theorem C (p. 795) transcribed from the author-hosted copy (PDF not committed); the library's subcritical form exact; l.1930's condition stronger (OQ-59)
- T-ett-e0-model-rows (topped up into lean-causal): both BTZ sentences at E₀ (marks wait on OQ-34); E₀ is causally plain, and every strongly causal SingularFlatAxioms spacetime (evidence for OQ-16); model-free theorems flagged for a hoist by /ett-programme; audit minor
- gates: lean-egf ✓, lean-benzecri ✓, lean-gx ✓, lean-causal ✓, roadmap ✓, atlas ✓, hub: papers_check all green; gate-tests red is /ett-programme's in-flight ladder (its lease)
- commits: 8eb3c59 438946d b57e0e6 a66988d 62cf1b9 c54508f 316d051 ebde3f7 942f470 b94633f (+ this)
- wall time: 01:55–02:45 (Paris); agents: 5 closers, 7 audits (1 re-audit), 1 fix round, 1 fetch attempt; shared cap briefly at 7 (/ett-programme's two non-Lean agents)
- new OQ: 59 (Troyanov's condition of record), 60 (EGF sampling confirmations), 61 (Benzécri cote z ≡ 0), 62 (« positif »)
- next: lean-causal goes back to /ett-programme's T-abs-hoist-time-function, then T-ett-gxsingular-dec25 (exclusive); outside lean-causal: T-syr-cycle-gcd, T-yamabe-gluing-algebra, T-gx-troyanov-reroute (master), T-atlas-sweep-refresh (master)

## 2026-11-21 04:05 · wave of 5 · T-syr-cycle-gcd, T-yamabe-gluing-algebra, T-gx-troyanov-reroute, T-atlas-sweep-refresh, T-ett-gxsingular-dec25 (topped up)
- T-syr-cycle-gcd: § 2's three rows proved in true forms, printed forms refuted in Lean (the GCD only up to sign; ν₂ conjunct false even with the minimal period; the literal « (x)_{n∈ℕ} » degenerate); the ν₃ conjunct favours the printed A_u^n against OQ-43's alternative; OQ-63; audit clean
- T-yamabe-gluing-algebra: lem:gluing-estimate's chain and thm:upper-bound's τ → 0 limit as lemmas over the model, the cited inputs carried; finding l.724 (R_g ≤ 0 does not follow from prop:nonpositive; closed via lem:positivity); audit minor; tool gap: texgraph does not link « Proof of Theorem~\ref{…} »
- T-gx-troyanov-reroute (master): the scaffold's GX.troyanovTheorem carries a sorry only for s ≥ 5 with an angle above 2π
- T-ett-gxsingular-dec25 (topped up into lean-causal, exclusive): gx's a.e. atlases ported verbatim (281 constants checked twice); prop:GX_sing_espace_temps_topo under DEC-25 needs the added (b′), shown necessary; rem:hypotheses_proposition_prop_gx reduced to non-regular points; OQ-64; audit minor
- T-atlas-sweep-refresh (master): sweep counts from fresh check logs of all six packages; overlay current for all ten papers
- gates: lean-syracuse ✓, lean-yamabe ✓, lean-gx ✓, lean-causal ✓ (232 strict modules), lean-benzecri ✓, lean-egf ✓, roadmap ✓, atlas ✓, hub make -k check all green
- commits: e113f97 244f341 13ff8f0 3cd2d78 1c83dfc 7aa1e47 933a95d 8b08793 d1cfe91 00d3204
- wall time: 02:48–04:05 (Paris); agents: 3 closers, 3 audits
- new OQ: 63 (Syracuse § 2 readings), 64 (DEC-25's (b′))
- next: plan (rule 2: no ready closer outside lean-causal, where /ett-programme runs 3 closers); candidates: T-bz-c2-compact (its dependency done), the texgraph « Theorem~\ref » proof-title gap, T-egf-sampling-corollaries (Pinsker), Troyanov s ≥ 5

## 2026-11-21 04:30 · plan · —
- why: rule 2 (no ready closer outside lean-causal, where /ett-programme runs three closers)
- result: 86 -> 94 targets (10 ready, 13 planned, 10 needs-ruling, 5 blocked); promoted T-bz-c2-compact (OQ-61 does not reach Prop. 7), T-bz-c2-hemisphere (needs only IsDeveloping.existsUnique_smul_eq, not the Theorem), T-egf-sampling-corollaries (Pinsker copied from GFNBounds' ILBoundFull, same mathlib pin, no require); added T-syr-upper-bounds (§ 3's algebraic rows), T-texgraph-proof-titles (master: five titled proofs given to the wrong row in yamabe and gx), T-bz-c2-prop2-literal, T-bz-c2-dedupe-majore (master, exclusive), T-bz-c2-cas-affin, T-bz-c2-developpement, T-bz-c2-theoreme-affine (planned), and T-yamabe-lower-bound (needs-ruling: thm:lower-bound is proved only in the companion paper); T-gx-troyanov's s ≥ 5 route analysed ([r] numerics; a fan of triangles), still planned
- rulings that would unblock the most (planner): BBS-Q1 (71 rows), T-yamabe-scope, OQ-45 (≈5 Benzécri marks, no Lean change), T-syr-cited, then OQ-38 (a), OQ-37, OQ-59
- gates: roadmap ✓, atlas ✓
- wall time: 04:10–04:30 (Paris); agents: 1 (planner, alone)
- next: wave: T-texgraph-proof-titles (master), T-bz-c2-compact, T-egf-sampling-corollaries (2 closers while /ett-programme runs 4 agents)

## 2026-11-21 05:15 · wave of 3 · T-texgraph-proof-titles, T-bz-c2-compact, T-egf-sampling-corollaries
- T-texgraph-proof-titles (master): texgraph links « Proof of Theorem~\ref », « of Kind \ref » and lone-\ref titles; five proofs reattached (yamabe l.640, 723, 731; gx l.756, 2068); ledger check refuses a title naming no statement (fixture, tests); only yamabe and gx ledgers changed; curation for cor:negative (joint proof), lem:spread_top (its proof after a remark), thm:lower-bound (companion paper)
- T-bz-c2-compact: Prop. 7 and its corollary closed in every dimension (independent of OQ-45 and OQ-61); not vacuous (the audit's ℝⁿ example); audit minor
- T-egf-sampling-corollaries: cor:sampling_error_control closed (on OQ-60); cor:pinsker_negative_control false as printed (δf_init's sign), corrected forms proved, Pinsker ported verbatim with Mathlib's klDiv; OQ-66; audit minor
- gates: lean-benzecri ✓, lean-egf ✓, roadmap ✓, atlas ✓, hub: papers_check all green; gate-tests red is /ett-programme's in-flight ladder (its lease)
- commits: d0488e5 (plan) e9925bb c65e6f0 5c5e6c6 8b6e305 58fdb39 (+ this)
- wall time: 04:35–05:15 (Paris); agents: 2 closers, 2 audits (while /ett-programme ran 3–4 agents)
- new OQ: 66 (the Pinsker δ sign)
- next: wave outside lean-causal: T-bz-c2-hemisphere, T-syr-upper-bounds, T-bz-c2-prop2-literal; master T-bz-c2-dedupe-majore (exclusive, when lean-benzecri is idle)

## 2026-11-21 06:03 · wave of 3 · T-bz-c2-hemisphere, T-bz-c2-prop2-literal, T-syr-upper-bounds
- T-bz-c2-hemisphere: Ch. 2 § 3 Prop. 2 closed as printed, every dimension (« variété » read Hausdorff, DEC-122); label marked; the printed 3° needs a triangle inequality for l_W (supplied); audit minor
- T-bz-c2-prop2-literal: Ch. 2 § 2 Prop. 2 proved under the literal reading, every dimension, with Printed ↔ Literal ∧ 0 < n; unmarked on OQ-56, and either ruling marks it with no Lean change; audit minor
- T-syr-upper-bounds: the four § 3 rows Lean-stated, partial, unmarked; l.277 false for both readings of OQ-43 (one exponent term too many), lem:syracuse_cycle's implication true as printed, the « m = … » clause and the corollary with m = 2^{p_n} − 3^n refuted, « intertwined » not needed; audit clean
- gates: lean-benzecri ✓, lean-syracuse ✓, roadmap ✓, atlas ✓, hub: papers_check all green; gate-tests red is /ett-programme's uncommitted programme/ladder.toml (the committed ladder matches the shipped Rules/Test.lean)
- commits: 3123eab 5232355 6e30171 0fe82db f921030 (+ this)
- wall time: 05:16–06:03 (Paris); agents: 3 closers, 3 audits (while /ett-programme ran a keeper and 2 lean-causal closers)
- new OQ: 68 (a)–(d) (Syracuse § 3 readings)
- next: plan (rule 2: no ready closer; only the master T-bz-c2-dedupe-majore is dispatchable)
