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

## 2026-11-21 06:18 · plan · —
- why: rule 2 (no ready closer after wave 11)
- result: 94 -> 96 targets (7 ready, 11 planned, 10 needs-ruling, 5 blocked); promoted T-bz-c2-cas-affin and T-bz-c2-developpement (T-bz-c2-compact done; neither depends on OQ-45 or OQ-61); added T-syr-steiner (theo:steiner_2) and T-syr-two-descents (theo:syracuse_cycle), the paper's steps with the cited inputs as hypotheses, false over ℤ as printed at the cycles (−5, −7) and (−17) [planner, to be confirmed in Lean]; T-gx-troyanov stays planned: from s = 5 an angle ≥ 4π defeats the polygon double and the fan (θ = (5π, 3π/4, π/10, π/10, π/10), checked numerically), a case split into θ_max ≥ 4π and < 4π
- rulings that would unblock the most (planner): BBS-Q1 (71 rows), T-syr-cited (8), OQ-42 (8), T-yamabe-scope with OQ-44 (≈10), OQ-63 and OQ-43 (6 each), OQ-68 (6), OQ-45 (5)
- gates: roadmap ✓, atlas ✓ (lean-causal overlay flagged stale by /ett-programme's scaffold builds; no lean-causal commit since 1f82940)
- wall time: 06:05–06:18 (Paris); agents: 1 (planner, alone)
- next: wave: T-bz-c2-cas-affin, T-bz-c2-developpement, T-syr-steiner, T-syr-two-descents (4 closers, 2 per package)

## 2026-11-21 07:22 · wave of 4 · T-bz-c2-cas-affin, T-bz-c2-developpement, T-syr-steiner, T-syr-two-descents
- T-bz-c2-cas-affin: closed 2/2 labels: the Remark before Prop. 7′ and Prop. 7′ as printed, every dimension, both marked; « connexe » settled by Ch. 1 Déf. 12 (no OQ); audit minor
- T-bz-c2-developpement: partial: the Theorem's 1° in component form, every dimension; the printed full form ⇔ D ∩ φ̃(V) connected, open for a non-constant cote (OQ-71); unmarked (assembled by T-bz-c2-theoreme); audit minor
- T-syr-steiner: partial: false over ℤ per period ((−5, −7)); exact reduction ⇔ theo:steiner; kernel check for periods ≤ 100; the planner's (a)–(c) confirmed; audit minor
- T-syr-two-descents: partial: false over ℤ (−17); key identity and bound in every configuration, the draft's unfinished case k₂ = k₁ + 1 included; the positive statement from two explicit cited hypotheses; audit minor
- gates: lean-benzecri ✓, lean-syracuse ✓, roadmap ✓, atlas ✓ (lean-causal overlay left at its committed edges: /ett-programme's wave 13 was mid-integration), hub: all gates green
- commits: 01e70c4 dc5b6dc 86eb4ac 64f197e 884dbd2 2eda361 (+ this)
- wall time: 06:21–07:22 (Paris); agents: 4 closers, 4 audits (with /ett-programme's 2 lean-causal closers, cap 6)
- new OQ: 71 (Benzécri 1°c, full or component form), 72 (Syracuse § 3 readings of theo:steiner_2 and theo:syracuse_cycle)
- next: plan (rule 2: no ready closer; only the master T-bz-c2-dedupe-majore). The planner also adds a master target for tools/ledger.py decl_line (it matches the last name component only; agreed with /ett-programme)

## 2026-11-21 07:44 · plan · —
- why: rule 2 (no ready closer after wave 12)
- result: 96 -> 102 targets (10 ready, 10 planned, 10 needs-ruling, 5 blocked); promoted T-bz-c2-theoreme (2°–4° and the assembly, independent of OQ-71; the « demi-droite » fact is to be proved, [r] route via IsCoqueProj.isCoqueStricte_iff); added T-bz-c2-premier-affine (the affine 1°; T-bz-c2-theoreme-affine re-scoped onto it), T-syr-no-circuit (theo:exists_no_circuit_other's own steps), T-syr-cited-steps (the own steps of cor:property_defined_cycles_gcd and prop:proposition, cited inputs as hypotheses), T-yamabe-negative (cor:negative over the measured model), T-ledger-decl-fullname (master: tools/ledger.py decl_line matches the last name component only; two false resolutions measured, ett lem:corresponding_K and benzecri bzdef:c1s1d8_partie_convexe, both confirmed by the master), T-ledger-stale-blockers (master: 17 ETT rows blocked by the done T-ett-port-e0)
- rulings that would unblock the most (planner): BBS-Q1 (63 rows), OQ-63 with OQ-68 and OQ-43 (8), OQ-42 (7), T-syr-cited (up to 7), OQ-45 (5), T-yamabe-scope with OQ-44 (5–7), OQ-71 (the Benzécri headline, 3 with its affine twin and result B)
- gates: roadmap ✓, atlas ✓
- wall time: 07:25–07:44 (Paris); agents: 1 (planner, alone)
- next: wave of 6: T-ledger-decl-fullname (master, after /ett-programme is told), T-bz-c2-theoreme, T-bz-c2-premier-affine, T-syr-no-circuit, T-syr-cited-steps, T-yamabe-negative

## 2026-11-21 08:45 · wave of 7 · T-bz-c2-theoreme, T-bz-c2-premier-affine, T-syr-no-circuit, T-syr-cited-steps, T-yamabe-negative, T-ledger-decl-fullname, T-bz-c2-dedupe-majore
- T-bz-c2-theoreme: 2°–4° proved (every dimension), the demi-droite lemma (new), the Theorem assembled in both forms; the row is closed up to OQ-71 (component form marks with no Lean change); independent of OQ-45; audit minor
- T-bz-c2-premier-affine: the affine 1°, generic in (G, X) (PremierGX); full form ⇔ connectedness, proved for z ≡ 0, star-shaped, n ≤ 1; OQ-75 (affine twin of OQ-71); audit minor
- T-syr-no-circuit: theo:exists_no_circuit_other's steps in true form; period bound for ε > log₃(3/2) under Matveev; the statement not proved (the draft stops at l.244); audit major (a tautological conditional, ∃ B after K), fixed in one round, AUDIT-2 clean; OQ-76
- T-syr-cited-steps: cor:property_defined_cycles_gcd and prop:proposition from the cited inputs as hypotheses; prop:proposition unconditional for x < 0; one Matveev Prop shared with NoCircuit (bridge lemma); audit minor
- T-yamabe-negative: cor:negative and prop:nonpositive's second sentence over the measured model; finding: § 6 never requires n ≥ 1 (OQ-74); audit minor
- T-ledger-decl-fullname (master): ledger check resolves decls by full Lean name; two false resolutions curated (ett by /ett-programme, benzecri here); fixture breakage 5, unit test
- T-bz-c2-dedupe-majore (master): one copy of « majorised by k ⟺ pseudo-length < k », in Mesure.lean
- gates: lean-benzecri ✓, lean-syracuse ✓, lean-yamabe ✓, roadmap ✓, atlas ✓ (lean-causal edges left at their committed state: /ett-programme's wave 15 in flight), hub: all gates green; selftest and unit suite (168) green after the ledger fix
- commits: 7314b34 cfcdb0d fc07e4f 4897d39 5b7ec9e f9b776b 1fd5770 1242ddb cecabab 664c5a3 16514da (+ this)
- wall time: 07:47–08:45 (Paris); agents: 5 closers, 6 audits, 1 fix round (shared cap 6 with /ett-programme)
- new OQ: 74 (Yamabe n ≥ 1), 75 (Benzécri affine twin of OQ-71), 76 (Syracuse « the known ones », η, « ≪ »)
- next: plan (rule 2: no ready closer; only the master T-ledger-stale-blockers, which needs papers/ett with /ett-programme). For the planner: merge exists_isCoqueStricteAff_demiDroite_ne_univ into Poches; T-bz-c2-theoreme-affine is unblocked (premier-affine done)

## 2026-11-21 08:51 · wave of 1 · T-ledger-stale-blockers
- T-ledger-stale-blockers (master): 17 ETT rows re-pointed from the done T-ett-port-e0 to their current blockers; roadmap.py check gains stale_blockers (a ledger row's blocked_on naming a done or dropped target of either roadmap fails), shown to bite on the old ledger (17), with a test case; under brief papers/ett leases, agreed with /ett-programme
- gates: roadmap ✓ (both roadmaps), ledger ett ✓, atlas ✓, selftest ✓; unit suite: one red, LadderEmit, from /ett-programme's uncommitted programme/ladder.toml (its keeper is running; the committed ladder matches the shipped Rules/Test.lean)
- commits: 1ac093f (+ this)
- wall time: 08:50–08:51 (Paris); agents: none (master)
- next: plan (rule 2: no ready closer)

## 2026-11-21 09:09 · plan · —
- why: rule 2 (the wave was empty after T-ledger-stale-blockers)
- result: 102 -> 106 targets (6 ready, 9 planned, 11 needs-ruling, 5 blocked): promoted T-bz-c2-theoreme-affine (the affine 2°–4°; at graduation its row's blocked_on goes to OQ-75 alone); added T-bz-result-b-proj (result B without the affine half of sentence 1, Applications/TheoremB.lean, unmarked), T-bz-c2-premier-full-proj (the projective full form of 1°c for n ≤ 1, star-shaped φ̃(V) ∩ H̊ and shells: narrows OQ-71), T-bz-c2-dedupe-demidroite (master, exclusive: one copy of the demi-droite witness), T-bz-chapter3 (needs-ruling: transcribe Benzécri Ch. 3 next?); T-bz-result-b re-scoped (the affine half and the mark; may need only OQ-45 (a), to be checked); T-ett-singular-instance stays planned (hreg assumed; the existence half needs OQ-64's (b′); a split to coordinate with /ett-programme)
- outside lean-benzecri nothing is closable without a ruling (Syracuse § 1–3 on OQ-42/43/54/63/68/72/76 and T-syr-cited; EGF on OQ-48/49/50/55/66 and T-egf-families; Yamabe on T-yamabe-scope, OQ-44; gx's C rows on DEC-27; bbs on BBS-Q1)
- rulings that would unblock the most (planner): BBS-Q1 (63 rows), OQ-42 (7), OQ-45 (a) (4, no Lean change), T-yamabe-scope with OQ-44 (7), OQ-63 (11 named, 2 alone), OQ-71 (component form marks bzthm:c2s3t1 with no Lean change), OQ-75, OQ-76, OQ-64; new question: T-bz-chapter3
- gates: roadmap ✓, atlas ✓
- wall time: 08:53–09:09 (Paris); agents: 1 (planner, alone)
- next: wave of 3 in lean-benzecri: T-bz-c2-theoreme-affine, T-bz-result-b-proj, T-bz-c2-premier-full-proj

## 2026-11-21 09:52 · wave of 3 · T-bz-c2-theoreme-affine, T-bz-result-b-proj, T-bz-c2-premier-full-proj
- T-bz-c2-theoreme-affine: the affine 2°–4° and the assembly, every dimension; closed up to OQ-75 (component form marks with no Lean change); full form for every affine shell; audit minor
- T-bz-result-b-proj: result B for the universal cover, all but the affine half of sentence 1; sentence 3 false at n = 0 (OQ-45 (a)); proof-term check: the mark needs neither OQ-71 nor OQ-75, only OQ-45 (a) and the affine half; Hopf-circle witness; audit minor
- T-bz-c2-premier-full-proj: the projective full form for every shell and, since there every pocket is a shell, every pocket when n ≤ 1 (the Theorem as printed for n ≤ 1); the open case is exactly ConnexeOuvertPrinted (non-shell, P ≠ V, n ≥ 2): OQ-79; audit minor
- gates: lean-benzecri ✓, roadmap ✓, atlas ✓ (all overlays current, lean-causal facts refreshed to c4e9d26), hub: all gates green
- commits: 3eb3108 08160b0 5c102ef afd3092 (+ this)
- wall time: 09:11–09:52 (Paris); agents: 3 closers, 3 audits (with /ett-programme's 3, cap 6)
- new OQ: 79 (what OQ-71 and OQ-75 now leave open)
- next: T-bz-c2-dedupe-demidroite (master, exclusive; three callers noted), then plan (rule 2); planner notes: split T-ett-singular-instance (atlas-owned, agreed with /ett-programme); T-bz-result-b (the affine half) is now unblocked

## 2026-11-21 10:18 · plan + T-bz-c2-dedupe-demidroite
- plan (rule 2): 106 -> 114 targets (8 ready); promoted T-bz-result-b (the affine half of sentence 1 and the mark; waits on OQ-45 (a), and on OQ-75/79 only if the affine half uses 1°'s second sentence: to check on the proof terms); split T-ett-singular-instance (atlas-owned, agreed with /ett-programme): hreg is a missing construction, not a ruling, and (b′) can be proved at the models → T-ett-massa-dec25, T-ett-ealpha-sectors, T-ett-e0-gx-structure (ready), T-ett-ealpha-gx-structure, T-ett-e-models-bprime, T-ett-singular-sfa (planned); added T-ett-model-rows-e0 (five bucket-D ETT rows whose model exists since 0fe9136) and T-ett-curation-model-blockers (master: six blocked_on texts naming as missing a layer that exists)
- T-bz-c2-dedupe-demidroite (master, run beside the planner, Lean only): one construction of the strict shell ]0, 1[ ⊂ ]0, ∞[ (Poches.exists_isCoqueStricteAff_demiDroite_and_ne_univ), both lemmas now its halves, statements and callers unchanged
- gates: lean-benzecri ✓, roadmap ✓, atlas ✓, hub: all gates green
- commits: 7ea17c9 3102db7 (+ this)
- wall time: 09:55–10:18 (Paris); agents: 1 (planner)
- next: wave in lean-causal (T-ett-massa-dec25, T-ett-ealpha-sectors, T-ett-e0-gx-structure; coordinate the package with /ett-programme: its T-loc-ealpha-tidy lease on EAlphaCauchy.lean, Static.lean), T-bz-result-b in lean-benzecri, master T-ett-curation-model-blockers (papers/ett lease)

## 2026-11-21 10:46 · wave of 2 · T-bz-result-b, T-ett-curation-model-blockers
- T-bz-result-b: result B assembled (Benzecri.theoremB beside theoremA; ResultBPrinted, resultBPrinted_iff ↔ 0 < n); the affine half of sentence 1; proof-term walk clean (67 names), so bzthm:intro_B is closed up to OQ-45 (a) alone; audit minor
- T-ett-curation-model-blockers (master): six ETT blocked_on fields re-pointed from layers that exist (E₀, E0.singularFlatAxioms; three of them my own wording from 1ac093f) to SingularFlatAxioms for every E≥0-manifold (T-ett-singular-sfa) and their named blockers; pushed before /ett-programme's integration
- gates: lean-benzecri ✓, roadmap ✓ (both), ledger ett ✓, atlas ✓, hub: all gates green
- commits: a8e2f66 60ddfc9 3a8b8c0 (+ this)
- wall time: 10:21–10:46 (Paris); agents: 1 closer, 1 audit (lean-causal held by /ett-programme's wave 16)
- next: wave in lean-causal when /ett-programme frees it (T-ett-massa-dec25, T-ett-ealpha-sectors, T-ett-e0-gx-structure; then T-ett-model-rows-e0); outside lean-causal nothing is ready

## 2026-11-21 11:47 · wave of 3 · T-ett-massa-dec25, T-ett-ealpha-sectors, T-ett-e0-gx-structure
- T-ett-massa-dec25: cor:massA_cac, cor:pushup_sing and the uniqueness of the natural causality over DEC-25 atlases with neither hreg nor (b′) (checked on the proof terms); existence ⇔ (b′) given hreg; the E≥0 models' cac and push-up discharged (E₀ included); audit minor
- T-ett-ealpha-sectors: the regular charts of E_κ (κ > 0) as chart isomorphisms (discs in flat sectors, rotations as transitions), hreg discharged, the first massA_positive witness charted into an E_κ; the planner's [r] sector bound refuted (fromPlane_wide_not_isometric); a shadowing name renamed at graduation; audit minor
- T-ett-e0-gx-structure: E₀ as a singular (Isom, E^{1,2})-manifold (E0GX.singularGX, Reg = E₀ ∖ axis by the parabolic holonomy), hreg at κ = 0, the model-free lemma corrected (the roadmap's wording refuted on ℂ); audit minor
- gates: lean-causal ✓ (announced to /ett-programme, which held its ladder build), roadmap ✓ (both), ledgers ett/barbot/sbierski-mghd/ers-predictability ✓, atlas ✓ (lean-causal facts at fa2d000, clean); hub: papers-check papers/egf and gate-tests red from the egf loop's uncommitted lean-egf and curation edits (its lease), nothing of this wave
- commits: cf6dca6 03d7f18 fa2d000 f5f613a (+ this)
- wall time: 10:4x–11:47 (Paris); agents: 3 closers, 3 audits
- new OQ: 82 (Isom(𝔼^{1,2}): SO₀ or O↑)
- next: plan (rule 2); planner notes: T-ett-ealpha-gx-structure is unblocked (hoist the model-free lemma first; use the _of_agreeOn form at α = 2π), T-ett-model-rows-e0 ready, T-ett-e-models-bprime to scope

## 2026-11-21 12:10 · plan · —
- why: rule 2 (one ready closer after wave 16)
- DEC-141 (2026-11-21): EGF is handed to /egf-programme; this loop leaves T-egf-families, T-egf-universality and OQ-50 to its handover target (it removes the two blocks itself, between our iterations)
- result: 114 -> 119 targets (5 ready); added T-ett-maxatlas-hoist (master: the model-free lemma and its counterexample into an ETT-layer module), T-ett-bprime-e0 ((b′) at E₀ singular sources, gx's e0_localUnique_sing route), T-ett-bprime-ealpha, T-ett-massa-models-instance (the missing MassAModel witness), T-ett-sfa-local (split from T-ett-singular-sfa); re-scoped T-ett-ealpha-gx-structure (κ = 2π via _of_agreeOn; κ = 2πn, n ≥ 2), T-ett-e-models-bprime, T-ett-singular-instance, T-ett-singular-sfa
- outside lean-causal nothing is closable without a ruling
- rulings that would unblock the most (planner): OQ-82 (5 ETT rows), BBS-Q1 (63), OQ-18 (6), OQ-34/35, OQ-64, T-yamabe-scope with OQ-44, OQ-63 / OQ-42, OQ-45 (a)
- gates: roadmap ✓, atlas ✓
- wall time: 11:49–12:10 (Paris); agents: 1 (planner)
- next: wave in lean-causal when /ett-programme frees it (T-ett-maxatlas-hoist, T-ett-bprime-e0, T-ett-model-rows-e0)

## 2026-11-21 13:38 · wave of 3 · T-ett-maxatlas-hoist, T-ett-bprime-e0, T-ett-model-rows-e0
- T-ett-maxatlas-hoist (master): the model-free lemma chartIso_of_mem_maximalAEAtlas_of_agreeOn, its corollaries and its counterexample hoisted out of Causal.Port.E0GXStructure into the ETT-layer Causal/MaximalAEAtlasIso.lean (deprecated aliases kept in E0GX)
- T-ett-bprime-e0: (b′) at E₀ → E₀ for every a.e. isomorphism chart (chartIso_of_isAEChart), BTZ_1's prop:isom at α = β = 0 in local form, by its own route over E0GX's sector charts (no covering space); E₀-manifolds carry a unique natural causality with no model hypothesis left (existsUnique_causality_e0); findings: BTZ_1 l.459's « timelike » step has no α = 0 analogue as written (null axis; the paper's own h_ℓ, l.369/l.442, and l.370 repair it), the reflection witnesses OQ-82, the planner's [r] was incomplete (k = μ; injectivity needed); audit minor
- T-ett-model-rows-e0: the five model rows for every κ ≥ 0 at the ported E₀ (cor:model_minimal, rem:pushup, lem:IJ_calc, lem:densite_modele (a)–(c), rem:galileo's model sentence), unmarked on OQ-34/35; findings: rem:pushup's first sentence false at κ = 0 too; densite's cited closure-of-interior fact false for J⁻ at BTZ points (contradicts l.1347), filed with Z^∓ (l.1482) and l.1488–1491 as one proof-level repair; audit minor (the closer ran its own lake build, harmless)
- curation: prop:GH_fortement_causal and prop:GH_Jferme cite /ett-programme's sharpness witnesses (loopFan_separates, fork_separates)
- gates: lean-causal ✓ (announced to /ett-programme), roadmap ✓, ledgers ett/barbot/sbierski-mghd/ers-predictability ✓, atlas ✓ (lean-causal facts at ebfa521, clean); hub: papers-check papers/egf and gate-tests red from the egf loop's uncommitted lean-egf scaffold (its lease), nothing of this wave
- commits: 3263c8f 673479e 0dffb9d ebfa521 c718fb8 (+ this)
- wall time: 12:37–13:38 (Paris); agents: 2 closers, 2 audits
- new OQ: none (OQ-83 went to /egf-programme; next free OQ-84); lean-causal kb 0116–0123
- next: plan (rule 2: no ready closer); lean-causal is held by /ett-programme's wave 20 (3 closers)
