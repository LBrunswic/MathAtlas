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

## 2026-11-21 14:11 · plan · —
- why: rule 2 (no ready closer after wave 17)
- result: 119 -> 123 targets. Promoted T-ett-ealpha-gx-structure (its dependencies done; names refreshed after the hoist; route notes: polar sector charts reach the line, BPrimeE0's slit-box scheme as a second route). Added T-ett-sfa-local-e0 (the E₀ half of T-ett-sfa-local: model-free transfer through isomorphic charts, then every E₀-manifold), T-ett-measures-e0 (λ₃ + λ₁ admissible at E₀: the first measure witnesses with sing₀ ≠ ∅; route [r]), T-ett-measures-ealpha (same label, the wave after) and master T-ett-curation-e0-blockers (eight stale ETT blocked_on fields)
- re-scoped: T-ett-bprime-ealpha's evidence corrected the way the E₀ [r] was (the timelike stabiliser has no boost; k = 1 needs injectivity; κ = 2π a trivial special case; OQ-82 reflections at κ > 0 too); T-ett-e-models-bprime records what (b′) still lacks; T-ett-sfa-local now depends on its E₀ half
- outside lean-causal nothing is closable without a ruling; the rulings that would unblock the most: BBS-Q1 (63 bbs rows), T-syr-cited, T-yamabe-scope with OQ-44, OQ-45 (a); inside ETT the marks wait on OQ-34 (11 rows), OQ-35 (9), OQ-18 (6), OQ-64 (5), OQ-82 (5)
- ids: OQ-84 and OQ-85 went to /egf-programme (a664a93); next free OQ-86
- gates: roadmap ✓, atlas ✓ (lean-causal overlay stale while /ett-programme integrates its wave 20; refreshed at the next clean tree)
- wall time: 13:50–14:11 (Paris); agents: 1 (planner)
- next: wave of T-ett-curation-e0-blockers (master, now) and, when /ett-programme frees lean-causal, T-ett-ealpha-gx-structure, T-ett-sfa-local-e0, T-ett-measures-e0

## 2026-11-21 15:00 · wave of 3 · T-ett-curation-e0-blockers, T-ett-ealpha-gx-structure, T-ett-sfa-local-e0
- T-ett-curation-e0-blockers (master): eight ETT blocked_on fields re-pointed from layers that exist (Galileo and Minkowski; « the model spaces of Section 3 »; « the model facts (SingularFlatAxioms) ») to what is missing (Lorentzian manifolds; prop:K_calcul's blocker; SingularFlatAxioms for every E≥0-manifold), each with OQ-34/35; pushed mid-wave
- T-ett-ealpha-gx-structure: closed in full, no remainder: E_κ (κ > 0) as a singular (Isom, E^{1,2})-manifold (singularGX κ), Sing = the line for κ ≠ 2π and ∅ at 2π, hreg at every κ; the continuation lemma (EAlphaContinuation) gives κ = 2π with no case split; findings: l.1332 « for α ≠ 2π » (the paper reads E_{2π} as regular itself), the cone singularity at 2πn seen only by injectivity; the planner's [r] (b) was wrong (disc charts on a small circle suffice); audit minor
- T-ett-sfa-local-e0: SingularFlatAxioms' chartwise fields at every E₀-manifold (rem:btz_pas_tarentin both halves, rem:sing_tarentin), a model-free ETT-layer transfer (SFATransfer); singularFlatAxioms_iff leaves the three BTZ fields of T-ett-singular-sfa; causallyPlain (evidence for OQ-16); finding (proof-level): « BTZ ∉ Z⁻ » is not a chart fact, it uses absolute minimality (OQ-18); audit minor (finding narrowed; second countability read under DEC-25 / RamcovGX.tex:474, no OQ)
- gates: lean-causal ✓ (announced to /ett-programme), roadmap ✓, ledgers ett/barbot/sbierski-mghd/ers-predictability ✓, atlas ✓ (lean-causal edges not refreshed: the tree carries /ett-programme's scaffold); hub: papers-check papers/egf, gate-tests (test_corrections, test_no_model_in_gates) red from the egf loop's uncommitted corrections.toml and lean-egf scaffold (its lease), nothing of this wave
- commits: 605ddc1 245a447 5bcad0b bae0342 (+ this)
- wall time: 14:17–15:00 (Paris); agents: 2 closers, 2 audits
- new OQ: none (next free OQ-86); lean-causal kb 0133–0141
- for the next planner: T-ett-bprime-ealpha can reuse exists_smul_devPt_of_ringBox, but its box form needs one map into E^{1,2} on all the boxes, which a chart into E_κ′ does not give directly (audit caution)
- next: plan (rule 2: only T-ett-measures-e0 is ready)

## 2026-11-21 15:57 · wave of 1 · T-ett-measures-e0
- T-ett-measures-e0: admissible measures at E₀, the first ModelMeasures with a BTZ point (E0.modelMeasures). The proof's sentence l.1737–1741 holds as printed: λ₃ in the future, λ₃ + λ₁ in the past, each failing exactly one of properties 1., 3., 4. on the other side; every finite measure in the class is admissible. The three rows are instantiated at E₀ (E0.mesure_admissible, E0.geroch_hypotheses, E0.mesure_unilaterale + sharp), with the paper's local form paper_measures_local. Every step of the planner's [r] route checked out. Finding (proof-level): l.1742–1743's restriction_convexe carries property 4 to U_p, not bare property 3; the paper's measures satisfy property 3 through its local form (pos_past_inter / pos_future_inter). Audit minor.
- gates: lean-causal ✓ (re-run after /ett-programme's 7923138 changed Causal.lean meanwhile), roadmap ✓, ledgers ett/barbot/sbierski-mghd/ers-predictability ✓, atlas ✓ (lean-causal facts at 6cf97e4, clean; edges refreshed), hub: no new red
- commits: 6cf97e4 341e642 (+ this)
- wall time: 15:05–15:57 (Paris); agents: 1 closer, 1 audit (T-ett-measures-ealpha shares its label, so it runs next)
- new OQ: none (the λ₃/λ₁ reading is settled by the class lemmas; next free OQ-86); lean-causal kb 0146–0150
- for the next planner: four strict docstrings were already stale before this target and are now plainly so (BTZPoints.lean:88–91, SingularGeroch.lean:107–108, SingularFlat.lean:122–126, MeasureRemarks.lean:309: « no model with sing₀ ≠ ∅ »), a tidy target; the auditor's unchecked observation that the assembly at every E≥0-manifold may need the chart image of U_p causally convex in the model
- next: plan (rule 2: T-ett-measures-ealpha is the only ready closer)

## 2026-11-21 17:50 · plan · —
- why: rule 2 (T-ett-measures-ealpha the only ready closer after wave 19); the planner was cut off once by the account's weekly API limit (no edit made), then resumed and finished
- result: 123 -> 126 targets. Promoted T-ett-massa-models-instance (dependencies done; the family equal to E0GX.singularGX at none by rfl; (b′) at regular sources for every pair) and T-ett-bprime-ealpha (re-scoped after the audit caution: the ring-box form does not apply to a chart into E_κ′; route: BPrimeE0's slit-box scheme with the timelike-line stabiliser; label moved to defi:causal_Ealpha). Re-scoped T-ett-measures-ealpha (restriction through the local form of property 3, Measure.toFinite), T-ett-e-models-bprime (only singular sources left; cross-type case [r] by holonomy traces), T-ett-sfa-local, T-ett-singular-sfa, T-ett-cbg-typeagreement (waits for /ett-programme's T-loc-cbg-curves-default in Causal/CBG/Geometry.lean). Added T-ett-sfa-btz-e0 (planned: the three BTZ fields at E₀-manifolds; the line field is the hard step), T-ett-measures-manifolds (planned: ModelMeasures at every strongly causal E≥0-manifold) and master T-ett-docstrings-sing0 (ready, exclusive: five stale strict docstrings; only when no closer is in lean-causal)
- outside lean-causal nothing is closable without a ruling; most unblocking: BBS-Q1 (63 rows), OQ-63 (11), T-yamabe-scope with OQ-44 (7), OQ-42 (7), OQ-45 (a) (6); inside ETT the marks wait on OQ-34 (22), OQ-35 (20), OQ-18 (7), OQ-82 (7), OQ-64 (5)
- /ett-programme stopped its loop on the weekly API limit (resets 2026-11-27 09:00 UTC), released its leases, and holds no lean-causal file; next free OQ-87, lean-causal kb 0151
- gates: roadmap ✓, atlas ✓
- wall time: 16:02–17:50 (Paris, including the interruption); agents: 1 (planner)
- next: wave of T-ett-massa-models-instance, T-ett-bprime-ealpha, T-ett-measures-ealpha (lean-causal is free), if the API limit lets agents run

## 2026-11-21 18:49 · wave of 3 · T-ett-massa-models-instance, T-ett-bprime-ealpha, T-ett-measures-ealpha
- T-ett-massa-models-instance: the E≥0 models as one family (global instance massAModelSingularGX, rfl to E0GX.singularGX / EAlphaGX.singularGXFamily; the audit found it safe), hreg at every model, (b′) at regular sources and between E₀ and every E_κ (notMem_axis_of_isAEChart, by causality, no holonomy: beyond its scope), the reduction hiso_massAModel_of_sing, E₀-manifolds over the whole family with no hypothesis left; audit minor (« what existence owes is prop:isom » reworded: implied by, not equivalent to)
- T-ett-bprime-ealpha: BTZ_1's prop:isom for α, β > 0 in local form (prop_isom_local: κ′ = κ, a rotation after a time translation near the line), (b′) at every E_κ (chartIso_of_isAEChart, hiso_family), E_{>0}-manifolds (existsUnique_causality_ealpha), the OQ-82 reflection at κ > 0; audit minor; the audit's probe shows hiso_family feeds hiso_massAModel_of_sing, so existence at every E≥0-manifold is now a ten-line assembly (T-ett-e-models-bprime)
- T-ett-measures-ealpha: one finite measure admissible both ways at every E_κ (λ₃ as printed, MeasuresEAlpha.modelMeasures, paper_measures_local), and the static ℝ × X layer (null frontiers for dt ⊗ ν, the class result, restriction through property 3's local form); audit minor
- planner [r] corrections (roadmap, not the paper): the polar-pushed Gaussian charges the apex (it is admissible nonetheless); bprime-ealpha's rotation offset is fixed mod κ′ only by a second connectedness step; massa's « uniqueness at E_π », « E₀'s cross-type case » and « trans_chart_mem_aeAtlas » ([r] superseded or wrong tool: isAEChart_refl); T-ett-e-models-bprime's holonomy route for E₀ ↔ E_κ is superseded
- gates: lean-causal ✓, roadmap ✓, ledgers ett/barbot/sbierski-mghd/ers-predictability ✓, atlas ✓ (lean-causal facts at fd909b6, clean; edges refreshed), hub: no new red
- commits: 263df71 3888285 fd909b6 674276f (+ this)
- wall time: 17:53–18:49 (Paris); agents: 3 closers, 3 audits (/ett-programme stopped on the weekly API limit, so lean-causal was ours)
- new OQ: none (next free OQ-87); lean-causal kb 0151–0158
- for the next planner: T-ett-e-models-bprime is now an assembly only (hiso_massAModel_of_sing fed with hiso_family, then massA_singular_models), then T-ett-singular-instance; optional tidy: stale strict docstrings MassADEC25.lean l.79–83, 98–99, 484–485 and EAlphaGX.lean l.94–96 (« no family / no witness yet »), beside T-ett-docstrings-sing0; hoist candidates isAEChart_restrOpen, the duplicated eq_of_eventuallyEq_of_continuousAt, chartIso_shiftIso and ConeRot
- next: plan (rule 2: only master T-ett-docstrings-sing0 is ready)

## 2026-11-21 19:10 · plan · —
- why: rule 2 (no ready closer after wave 21)
- result: 126 -> 127 targets. Promoted:
  - T-ett-e-models-bprime: re-scoped to the assembly, hiso_massAModel_of_sing fed with hiso_family, then massA_singular_models. It now carries the three corollaries at every E≥0-manifold, with witnesses at E₀ and E_π over the whole family. Labels widened. Its holonomy [r] is marked superseded.
  - T-ett-sfa-local: its dependency on e-models-bprime is replaced by bprime-ealpha (done), since the cross-type and κ′ = κ invariances are already proved.
  - T-ett-measures-manifolds: the model's convex set is chosen first; DEC-7's StronglyCausal is used; a K-transport lemma under ChartIso and a family Borel instance are still to write.
  - T-ett-sfa-btz-e0: split; it keeps singularPastAt and Iplus_of_lt.
- added: T-ett-sfa-line-e0 (planned: the line field and the E₀-manifold assembly; Mathlib at the pin has no classification of 1-manifolds).
- T-ett-singular-instance stays planned: its scope is now folded into e-models-bprime. Close it on that target's commit if the audit confirms, and re-point the two ledger rows that name it (defi:causal_Ealpha, rem:mesure_unilaterale).
- T-ett-docstrings-sing0's scope widened to the newly stale strict docstrings (MassADEC25, EAlphaGX, BPrimeE0; MassAModelsInstance and BPrimeEAlpha if it runs after e-models-bprime).
- Hoist candidates were considered and not added.
- outside lean-causal nothing is closable without a ruling. The rulings that would unblock the most: BBS-Q1 (63 rows), OQ-63 (11), OQ-42 (7), T-yamabe-scope with OQ-44 (7), OQ-45 (a) (6). Inside ETT the marks wait on OQ-34 (22), OQ-35 (20), OQ-18 (8), OQ-82 (7), OQ-64 (6).
- gates: roadmap ✓, atlas ✓
- wall time: 18:52–19:10 (Paris); agents: 1 (planner)
- next: wave of T-ett-e-models-bprime, T-ett-sfa-local, T-ett-measures-manifolds (lean-causal; sfa-local writes under Causal/Port)

## 2026-11-21 20:05 · wave of 3 · T-ett-e-models-bprime, T-ett-sfa-local, T-ett-measures-manifolds (and T-ett-singular-instance)
- T-ett-e-models-bprime: (b′) between every two E≥0 models (hiso_massAModel) and the three corollaries cor:massA_causalite, cor:massA_cac, cor:pushup_sing at every E≥0-manifold with no model hypothesis left (massA_singular_all); the (G,X) sentence of defi:causal_Ealpha at every E≥0-manifold (causal_Ealpha_manifolds); witnesses E₀, E_π; T-ett-singular-instance, folded into it by the 19:10 plan, closes on the same commit; the rows now wait on readings only (OQ-18, OQ-82, OQ-34/35, OQ-64 as a reading); audit minor
- T-ett-sfa-local: SingularFlatAxioms' chartwise fields at every E≥0-manifold, mixed ones included (rem:btz_pas_tarentin, rem:sing_tarentin; sing_α read through the X_A-charts, type invariance = brunswic2021cauchy Cor. 1.5); singularFlatAxioms_iff leaves the four line fields; the closer's cross-type finding was overstated (the paper's every-chart reading gives it from two charts) and is curated as a citation remark (Cor. 1.5, never cited) at defi:causal_Ealpha; sing_{2π}(M) = ∅ settled (DEC-25, DEC-74; the l.2185 convention is OQ-25's); audit minor
- T-ett-measures-manifolds: ModelMeasures at every strongly causal E≥0-manifold; the chart transfer split into the ETT-layer Causal/MeasureTransfer.lean at graduation; finding (proof-level): l.1734–1743's restriction_convexe applied in the model needs φ(U_p) causally convex there (cutDiamond_separates; the audit corrected its « relatively compact » and gave a relatively compact example by hand), merged with T-ett-measures-e0's property-3 finding into one suggested wording; audit minor
- gates: lean-causal ✓, roadmap ✓, ledgers ett/barbot/sbierski-mghd/ers-predictability ✓, atlas ✓ (lean-causal facts at 3afcf7f, clean), hub: no new red
- commits: c0c402c 29883c4 3afcf7f 9a23398 (+ this)
- wall time: 19:13–20:05 (Paris); agents: 3 closers, 3 audits
- new OQ: none (next free OQ-87); lean-causal kb 0159–0166
- not done (noted): lean-causal/README.md's module table lists none of the atlas modules of waves 17–23 (it is /ett-programme's convention); a tidy pass could add them
- next: T-ett-sfa-btz-e0 is the only ready closer (with master T-ett-docstrings-sing0): plan (rule 2) or a wave of one

## 2026-11-21 20:25 · plan · —
- why: rule 2 (only T-ett-sfa-btz-e0 ready after wave 23)
- result: 127 -> 130 targets. The singular-flat tail is split into model-free and per-model targets.
- new and ready:
  - T-ett-line-development: model-free maximal arc through a closed set with a translation structure. It is γ onto the component, inextensible from « no limit at ±∞ », a closed embedding when injective. It avoids any classification of 1-manifolds.
  - master T-ett-readme-modules: 32 strict atlas modules have no README row.
- re-scoped:
  - T-ett-sfa-btz-e0: singularPastAt and Iplus_of_lt at the BTZ points of every E≥0-manifold, now in the SFALocal setting.
  - T-ett-sfa-line-e0: the α = 0 instance of the line development; planned, until T-ett-line-development is done.
  - T-ett-singular-sfa: assembly only, through SFALocal.singularFlatAxioms_iff.
  - T-ett-docstrings-sing0: its scope widened to the docstrings wave 23 made stale.
- new and planned: T-ett-sfa-massive-line (the α > 0 instance, massive_line). The E_κ side has no singularPastAt or Iplus_of_lt fields.
- outside lean-causal: nothing is ready. The rulings that would unblock the most are BBS-Q1 (63 rows), OQ-63 (11), OQ-42 (7), OQ-44 with T-yamabe-scope (7) and OQ-45 (a) (6). Inside ETT the marks wait on OQ-34 (24), OQ-35 (22), OQ-18 (10), OQ-82 (9) and OQ-64 (6).
- gates: roadmap ✓, atlas ✓
- wall time: 20:08–20:25 (Paris); agents: 1 (planner)
- next: a wave of T-ett-line-development and T-ett-sfa-btz-e0 (lean-causal), plus master T-ett-readme-modules

## 2026-11-21 21:15 · wave of 3 · T-ett-line-development, T-ett-sfa-btz-e0, T-ett-readme-modules
- T-ett-line-development: the model-free translation-line development (ETT layer, Causal/LineDevelopment.lean). From a translation atlas of a closed S in a Hausdorff M, every p lies on a line γ onto its component, inextensible from « no limit at ±∞ », a closed embedding when injective; exists_line and exists_chronal_line give the field shapes exactly. No classification of 1-manifolds is used. Witnesses: the timelike line, and the circle with the non-causal allRelated. Findings (proof-level): l.1529–1530 « parametrisable by ℝ » misses a compact component (non-causal M; DEC-6 keeps the lemma); l.1530's classification of 1-manifolds is uncited. Audit minor
- T-ett-sfa-btz-e0: singularPastAt and DEC-64's Iplus_of_lt at every BTZ point of every E≥0-manifold; BTZAxioms from line alone; SingularFlatAxioms ⇔ line ∧ massive_line. Beyond the target, prop:K_calcul and prop:K_monotone hold at every (causal) E≥0-manifold, so their « SingularFlatAxioms » blocker is gone (OQ-16 and the readings remain). Finding (proof-level): l.1344–1356's facts pass to M only through corollaries stated after the definition. Audit minor
- T-ett-readme-modules (master): 32 rows added to lean-causal/README.md's module table, read off the docstrings (3699857). Tell /ett-programme when it resumes (2026-11-27)
- roadmap: T-ett-sfa-line-e0 and T-ett-sfa-massive-line moved to ready by their blocks' own condition (T-ett-line-development done)
- gates: lean-causal ✓, roadmap ✓, ledgers ett/barbot/sbierski-mghd/ers-predictability ✓, atlas ✓ (lean-causal facts at 299cce7, clean), hub: no new red
- commits: 3699857 00fdfd2 299cce7 492ad46 (+ this)
- wall time: 20:28–21:15 (Paris); agents: 2 closers, 2 audits
- new OQ: none (next free OQ-87); lean-causal kb 0167–0174
- next: wave of T-ett-sfa-line-e0 and T-ett-sfa-massive-line (then T-ett-singular-sfa)

## 2026-11-21 21:50 · wave of 2 · T-ett-sfa-line-e0, T-ett-sfa-massive-line
- T-ett-sfa-line-e0: BTZAxioms.line at every Hausdorff E≥0-manifold (SFALine.line: the charts into E₀ make sing₀(M) a translation line, one exists_eqOn_rotE0_tauShift per transition, then LineDevelopment.exists_line; no absolute minimality, no second countability); BTZAxioms there (btzAxioms); SingularFlatAxioms at every T2, second countable E₀-manifold with no field left (singularFlatAxioms_e0); at causal M, J⁻(p) is the half-line (Jminus_eq_image). Findings: the l.1530 finding refined (prop:isom supplies the translations); l.294 (introduction) states the half-line at every E≥0-manifold, true only when M is causal (sentence-level). Audit minor
- T-ett-sfa-massive-line: massive_line at every Hausdorff E≥0-manifold (SFAMassiveLine.massive_line, one prop_isom_local per transition, exists_chronal_line); l.1341 read in M (sing_locallyChronal, component_timelike); SingularFlatAxioms at every E_{>0}-manifold outright; E_π the library's first SingularFlatAxioms witness with a non-empty massive line. Findings appended to existing entries (l.1530 for every α, with the implicit orientation; l.1341). Audit minor
- the four line fields are all proved: SingularFlatAxioms at every Hausdorff, second countable E≥0-manifold with an absolutely minimal causality is one application of SFABTZ.singularFlatAxioms_iff_lines (an audit probe checked it), which is T-ett-singular-sfa (all its dependencies done; for the planner to promote), then T-ett-singular-rows
- roadmap slip, repaired before dispatch: moving the two targets to ready with --evidence (previous iteration) had replaced the planner's scope; restored from adf50ad (memory noted)
- gates: lean-causal ✓, roadmap ✓, ledgers ett/barbot/sbierski-mghd/ers-predictability ✓, atlas ✓ (lean-causal facts at a303a95, clean), hub: no new red
- commits: 7072b90 a303a95 b03a55e (+ this)
- wall time: 20:4x–21:50 (Paris); agents: 2 closers, 2 audits
- new OQ: none (next free OQ-87); lean-causal kb 0175–0179
- next: plan (rule 2): promote T-ett-singular-sfa (and with it the MeasuresManifolds e0 conditionals made unconditional, sfa-line-e0 AUDIT-1 suggestion_review), then T-ett-singular-rows; master T-ett-docstrings-sing0 is ready (exclusive)

## 2026-11-21 22:10 · plan · —
- why: rule 2 (no ready closer after wave 26)
- result: 130 -> 133 targets; every edited evidence keeps its old text as a prefix.
- Promoted T-ett-singular-sfa, re-scoped to:
  - the one-line assembly;
  - SingularFlatSpacetime and the natural-causality form;
  - the MeasuresManifolds conditionals made unconditional;
  - for after its audit, where each of the 14 rows naming it must be re-pointed.
- Re-scoped T-ett-singular-rows (planned) to the Section 3.3 K rows: lem:past_BTZ (b), cor:K_injectif, prop:K_densite_sing, cor:K_ordre, lem:cup_cap_BTZ in DEC-19's form, rem:K_plongement_hypotheses, cor:K_ordre_Sigma.
- Added T-ett-singular-rows-local (ready): lem:J_int, lem:cup_cap_sing, and the E≥0 sentences of rem:tarentin_exemples, rem:lorentz_tarentin and rem:pas_plat (ii). Their hypotheses are all available now.
- Added T-ett-cupcap-btz-cex (ready): DEC-19's by-hand counterexample to CupCapBTZAsPrinted at E₀ ∖ {w}; one step is [r].
- Added T-ett-singular-rows-geroch (planned): rem:mesure_unilaterale, rem:mesure_unilaterale_ptr, theo:geroch_sing (i)⇒(ii)/(iii).
- Widened T-ett-docstrings-sing0. Nothing promotable in the CBG pair.
- outside lean-causal: nothing is closable without a ruling. The rulings that would unblock the most are BBS-Q1 (63 rows), OQ-63 (11), OQ-42 and OQ-44 (7 each), and OQ-45, OQ-43 and OQ-68 (6 each). Inside ETT the marks wait on OQ-34 (26), OQ-35 (24), OQ-18 (15), OQ-82 (14) and OQ-64 (6).
- gates: roadmap ✓, atlas ✓
- wall time: 21:0x–22:10 (Paris); agents: 1 (planner)
- next: a wave of T-ett-singular-sfa, T-ett-singular-rows-local and T-ett-cupcap-btz-cex. After T-ett-singular-sfa graduates, its 14 rows must be re-pointed, or stale_blockers fails.

## 2026-11-21 22:52 · wave of 3 · T-ett-singular-sfa, T-ett-singular-rows-local, T-ett-cupcap-btz-cex
- T-ett-singular-sfa: SingularFlatAxioms at every Hausdorff, second countable E≥0-manifold, as the one-line assembly. SingularFlatSpacetime iff M is connected; existence and uniqueness of the natural causality. prop:mesure_admissible and rem:singular_flat_spacetime_therefore now hold with no hypothesis left. The 14 rows that named it in blocked_on are re-pointed. Audit minor.
- T-ett-singular-rows-local: lem:J_int, lem:cup_cap_sing, the E≥0 sentences of rem:tarentin_exemples and rem:lorentz_tarentin, and rem:pas_plat (ii), at every E≥0-manifold.
  - Finding: every E≥0-manifold is causally plain, so « it fails in the two families » (l.290, and the abstract and introduction) is refuted for the singular family. This is evidence for OQ-16.
  - Audit: AUDIT-1 major, for four unintended docstring marks. One closer fix round removed them, with statements and proofs unchanged; AUDIT-2 minor.
- T-ett-cupcap-btz-cex: CupCapBTZAsPrinted is refuted in Lean at E₀ ∖ {w}. DEC-19's by-hand finding is now formalized with no proviso left. The proof breaks where it needs J⁺(z) closed. Audit minor.
- roadmap:
  - T-ett-singular-rows and T-ett-singular-rows-geroch are moved to ready, by their blocks' own condition.
  - T-ett-docstrings-sing0's evidence gains the three stale « by hand » docstrings.
  - Evidence was appended, never replaced.
- gates: lean-causal ✓, roadmap ✓, ledgers ett/barbot/sbierski-mghd/ers-predictability ✓, atlas ✓ (lean-causal facts at 321436f, clean), hub: no new red
- commits: 1d2e5a5 f823443 321436f b5ef07b (+ this)
- wall time: 22:13–22:52 (Paris); agents: 3 closers, 4 audits (one re-audit), 1 fix round
- new OQ: none (next free OQ-87); lean-causal kb 0180–0186
- next: a wave of T-ett-singular-rows and T-ett-singular-rows-geroch; T-ett-docstrings-sing0 runs between waves

## 2026-11-21 23:38 · wave of 2 · T-ett-singular-rows, T-ett-singular-rows-geroch
- T-ett-singular-rows: the seven Section 3.3 K rows hold at every Hausdorff, second countable E≥0-manifold, through SFAManifolds.singularFlatAxioms. They are lem:past_BTZ (b), cor:K_injectif, prop:K_densite_sing, cor:K_ordre, lem:cup_cap_BTZ in DEC-19's form, rem:K_plongement_hypotheses and cor:K_ordre_Sigma. Weaker-hypothesis forms are kept beside them. This is the first non-vacuous cup_cap_BTZ certificate at a BTZ point. Audit minor.
- T-ett-singular-rows-geroch:
  - rem:mesure_unilaterale and rem:mesure_unilaterale_ptr hold at every E≥0-manifold.
  - theo:geroch_sing: (i)⇒(ii), (i)⇒(iii) and (ii)⇒(iii) hold at M. (iii)⇒(i) and the equivalence stay in the scaffold, in CausalScaffold.SingularRowsGerochEquiv, on one tagged sorry (OQ-32, T-ett-geroch-iii-i).
  - Finding: an admissible measure forces causality.
  - Audit minor.
- roadmap:
  - Appended to T-ett-geroch-iii-i's evidence: where the step at genuine E≥0-manifolds lives, and why OQ-33's witness does not reach it.
  - Appended to T-ett-docstrings-sing0's evidence: four more stale docstrings.
  - Evidence was appended, never replaced.
- gates: lean-causal ✓ (strict 0 sorry in 285 files; scaffold 6 in 7), roadmap ✓, ledgers ett/barbot/sbierski-mghd/ers-predictability ✓, atlas ✓ (lean-causal facts at 73ee7ca, clean), hub: no new red
- commits: 6c46fb8 73ee7ca 0422ede (+ this)
- wall time: 22:55–23:38 (Paris); agents: 2 closers, 2 audits
- new OQ: none (next free OQ-87); lean-causal kb 0187–0191
- next: plan (rule 2). The only ready non-planner target is T-ett-docstrings-sing0 (master, exclusive in lean-causal), which runs between waves. The singular-flat track is complete; the remaining ETT marks wait on OQ-18, OQ-34/35, OQ-64, OQ-82, OQ-16 and OQ-32/33.

## 2026-11-22 00:10 · plan (rule 2: no ready closer target after wave 29)
- result: 133 -> 136 targets.
  - Added T-ett-sigma-separe (ready, p6): lem:Sigma_separe without ψ at every globally hyperbolic, T2, second countable E≥0-manifold; this discharges cor:K_ordre_Sigma's hS and gives both directions of lem:Cauchy_plongement_toutes.
  - Added T-ett-bubble-kplus (ready, p7): rem:K_neq_I's bubble sentence, recorded « open » at Causal/LinesReachable.lean:31, is refuted under prop:tarentin_fort_K's hypotheses by Minkowski space with one spoke. It is to be stated as an AsPrinted-style Prop and refuted, with no mark.
  - Added T-ett-geroch-split-flow (planned, p7, depends on T-ett-sigma-separe): theo:geroch_sing's « Moreover » from any causal flow, with E₀'s τ-translation as a witness.
- rejected: every other open row waits on a ruling, on /ett-programme (CBG pair, Lorentzian rows, lem:C_ext_connexe) or on mathematics DEC-136 leaves open (T-gx-troyanov for s ≥ 5). lem:image_diamant and lem:passe_pgcd need the limit-curve step of CausalScaffold.GerochCauchy.
- research: none. Step 1 gave two ready closers, so T-3p1-funnel-lemma and T-bbs-archive are still ready.
- for the author: programme/roadmap.toml has ready closer targets while /ett-programme is paused until 2026-11-27, e.g. T-abs-ers-4-72-second-countable, T-abs-c-ext-connexe-*, T-abs-galileo-ladder and T-loc-ealpha-tidy. /atlas-team does not run them unless you say so.
- gates: roadmap ✓, atlas ✓
- wall time: 23:41–00:10 (Paris); agents: 1 (planner)
- next: a wave of T-ett-sigma-separe and T-ett-bubble-kplus (both lean-causal). T-ett-docstrings-sing0 (exclusive) runs between waves.

## 2026-11-22 00:47 · wave of 2 · T-ett-sigma-separe, T-ett-bubble-kplus
- T-ett-sigma-separe: lem:Sigma_separe's « In particular » holds with no ψ for every Cauchy surface. Over SingularFlatAxioms it needs causality only (sigma_separe_of_isCausal; global hyperbolicity is not used) and it holds at every causal, T2, second countable E≥0-manifold. Two rows now carry no Lean hypothesis at globally hyperbolic E≥0-manifolds:
  - cor:K_ordre_Sigma, for every Cauchy surface (hS discharged);
  - lem:Cauchy_plongement_toutes, in both directions.
  The E₀ witness exercises the BTZ case. Unmarked (OQ-18, OQ-34, OQ-35, OQ-82). Audit minor: the l.2067–2068 finding is worded as a gain in route, not in class.
- T-ett-bubble-kplus: rem:K_neq_I's bubble sentence (l.872–875) is refuted as printed under prop:tarentin_fort_K's hypotheses without causal plainness. The witness is Minkowski space with one spoke; the K⁺ form follows by time reversal. True form from lem:K_facile: a bubble meets K iff it persists. Findings on l.872–875, with a suggested wording, and on l.140–141. Unmarked. Audit minor: the general ℝ × E witness is second countable only for E separable, and the docstring was fixed at graduation.
- roadmap:
  - T-ett-geroch-split-flow is promoted to ready, by its block's condition (no global hyperbolicity needed).
  - T-ett-docstrings-sing0's evidence gains LinesReachable.lean:31.
  - Evidence was appended, never replaced.
- README: 12 module-table rows, for the three new modules and the nine atlas modules of waves 24–29.
- gates: lean-causal ✓ (strict 0 sorry in 288 files; scaffold 6 in 7), roadmap ✓, registers ✓, ledgers ett/barbot/sbierski-mghd/ers-predictability ✓, atlas ✓ (lean-causal facts at c7fa3bc, clean), hub: no new red
- commits: 13e7bf0 713637d c7fa3bc c841f8b (+ this)
- wall time: 00:11–00:47 (Paris); agents: 2 closers, 2 audits
- new OQ: OQ-87 (the bubble sentence: general implication or a claim about the cited C⁰ examples; l.140–141 pointwise or global). It bears on the wording of findings only. lean-causal kb 0192–0198.
- next: T-ett-geroch-split-flow is the only ready closer. That is fewer than two, so rule 2 calls for a plan; the last planner run was one iteration ago. T-ett-docstrings-sing0 (master) can run between waves.

## 2026-11-22 00:59 · plan (rule 2: one ready closer target after wave 30)
- result: 136 -> 137 targets.
  - Added T-ett-diamant-rows (ready, p6): lem:image_diamant and lem:passe_pgcd at every pair of Hausdorff, second countable E≥0-manifolds, with no Lean hypothesis left. Last run rejected these rows, but the compactness no longer needs the limit-curve step. The library's Zorn route (Causal/Flat/CBGCompact.lean) asks for J⁻ of an open set to be open, which takes a few lines from push-up and Z⁺, and for J^±(S) closed, which wave 30 proved. The time-reversed compactness does not follow by duality (Z⁻ fails at BTZ points), and image_diamant does not need it.
  - Noted on T-ett-cbg-e0 (planned): A2's future-form compactness field is the one T-ett-diamant-rows proves.
  - T-3p1-theorem-g (planned) now also depends on T-bbs-rp1-circles. Its statement needs HS-spheres and « hyperbolic of degree 0 », which wait on BBS-Q1.
- rejected: (iii)⇒(i) (OQ-32/33: the compactness route needs a closed ≤ and a time function); the CBG rows (T-ett-cbg-e0 chain, /ett-programme); lem:C_ext_connexe (/ett-programme); the DEC-17 definitions; rem:non_separe_cas (OQ-14).
- research: none (two ready closers); T-3p1-funnel-lemma and T-bbs-archive stay ready.
- gates: roadmap ✓, atlas ✓
- wall time: 00:48–00:59 (Paris); agents: 1 (planner)
- next: a wave of T-ett-diamant-rows and T-ett-geroch-split-flow (both lean-causal, disjoint new files, strict-bound).

## 2026-11-22 01:31 · wave of 2 · T-ett-diamant-rows, T-ett-geroch-split-flow
- T-ett-diamant-rows: lem:image_diamant and lem:passe_pgcd hold at every pair of Hausdorff, second countable E≥0-manifolds, with no Lean hypothesis left. passe_pgcd comes as printed and for every p ∈ closure(range i).
  - The compactness of J⁺(Σ) ∩ J⁻(p) goes by CBGCompact's Zorn, with no limit curves. Its inputs are J⁻ of open sets open (the new model-free isOpen_Jminus_of_pushUp) and J^±(Σ) closed.
  - The time-reversed compactness is not proved: Z⁻ fails at BTZ points.
  - The witnesses are at the identity, where the inclusions are trivial; this is disclosed on both rows. The library has no Cauchy extension that is not onto.
  - Unmarked. Audit minor.
- T-ett-geroch-split-flow: theo:geroch_sing's « Moreover » holds from any causal flow, with no global hyperbolicity, connectedness or openness hypothesis. VecteurFlow ⇔ IsCausalFlow, with the openness proved.
  - lem:Sigma_separe's equalities hold for that ψ, with a model-free form that needs no closedness.
  - E₀'s τ-flow is causal and null. VecteurFlow is inhabited at E₀, and geroch_sing_split and K_ordre_Sigma_of_splitting are instantiated.
  - No chronal causal flow exists once there is a BTZ point.
  - lem:vecteur at a general M stays a named flow: there is no differentiable structure.
  - Unmarked. Audit minor, with four docstring and finding wordings fixed at graduation. The REPORT's three reading questions are moot, per the audit: no OQ.
- roadmap: T-ett-docstrings-sing0's evidence gains SingularRowsGeroch.lean:115, SingularRowsK.lean:141 and Splitting.lean:76 (appended).
- gates: lean-causal ✓ (strict 0 sorry in 291 files; scaffold 6 in 7), roadmap ✓, ledgers ett/barbot/sbierski-mghd/ers-predictability ✓, atlas ✓ (lean-causal facts at 543ea3a, clean), hub: no new red
- commits: 340902c 543ea3a 3a4401f (+ this)
- wall time: 01:00–01:31 (Paris); agents: 2 closers, 2 audits
- new OQ: none (next free OQ-88); lean-causal kb 0199–0206
- next: plan (rule 2: no ready closer). T-ett-docstrings-sing0 (master, exclusive, p10) has been starved: rule 2 always precedes it, and a closer in lean-causal always excludes it. Raise this with the planner.

## 2026-11-22 01:50 · plan (rule 2: no ready closer target after wave 31)
- result: 137 -> 139 targets.
  - Added T-ett-cauchy-ext-e0 (ready, p6): a Cauchy extension between E≥0-manifolds that is not onto, the open past set {T < 1} of E₀ with its inclusion. With it, image_diamant, passe_pgcd_printed (both branches, at frontier points) and cauchy_plongement_toutes_manifolds get witnesses that are not at the identity, answering T-ett-diamant-rows AUDIT-1.
  - Added T-ett-diamant-past (ready, p7): J⁻(Σ) ∩ J⁺(p) is compact, by a route other than duality: J⁺ of open sets is open, in four cases, at causal SFA spacetimes. This is A2's second compactness field (theo:CBG).
  - T-ett-docstrings-sing0 goes from p10 to p5, so that `wave` picks it alone next. Rule 2 and its exclusivity had starved it, and making it non-exclusive would race closers' builds on shared oleans.
  - Note on T-ett-cbg-e0: after T-ett-diamant-past, all A2 fields but typeAgreement's chain hold at E≥0-manifolds.
- rejected: (iii)⇒(i) (OQ-32: a closed ≤ and a time function); the CBG pair (/ett-programme); lem:C_ext_connexe and prop:Cauchy_pgcd; lem:vecteur (no differentiable structure); the time-reversed forms of image_diamant and passe_pgcd (not in the paper); DEC-8 openness at E≥0-manifolds (no row).
- research: none (two ready closers). The planner notes that T-3p1-funnel-lemma and T-bbs-archive are starved the same way the docstrings target was.
- gates: roadmap ✓, atlas ✓
- wall time: 01:33–01:50 (Paris); agents: 1 (planner)
- next: T-ett-docstrings-sing0 (master, alone in lean-causal), then a wave of T-ett-cauchy-ext-e0 and T-ett-diamant-past.

## 2026-11-22 02:07 · wave of 1 · T-ett-docstrings-sing0 (master)
- T-ett-docstrings-sing0: 25 strict docstrings in lean-causal corrected. Prose only: no statement, proof or mark changes.
  - Each sentence that said the library lacks an object, or that a done target is still to come, now names what exists: E₀ and E_α with the DEC-25 reading; E0.singularFlatAxioms and its BTZ-branch instances; the two by-hand findings, now formalized; nonvacuous_e0_chain; the model packaging and (b′); the SFA field and assembly theorems; the wave 30–31 witnesses.
  - Where a claim still holds, it is kept, narrowed.
  - ETTSection4 is re-pointed at T-ett-cbg-e0.
  - Not touched: /ett-programme's files, and SingularRowsDiamond's SCOPE, which is for the next wave.
- gates: lean-causal ✓ (full rebuild; strict 0 sorry in 291 files; scaffold 6 in 7), roadmap ✓, ledgers ett/barbot/sbierski-mghd/ers-predictability ✓ (stamp only), atlas ✓ (lean-causal facts at 8786718), hub: no new red
- commits: 8786718 662ab55 (+ this)
- wall time: 01:55–02:07 (Paris); agents: none (master)
- next: a wave of T-ett-cauchy-ext-e0 and T-ett-diamant-past. At their graduation, SingularRowsDiamond.lean's SCOPE (:79–86) is re-worded.

## 2026-11-22 02:56 · wave of 2 · T-ett-cauchy-ext-e0, T-ett-diamant-past
- T-ett-diamant-past: A2's time-reversed compactness, J⁻(Σ) ∩ J⁺(p) compact, holds at every globally hyperbolic, Hausdorff, second countable E≥0-manifold with no hypothesis left, verbatim the field's conclusion.
  - The route is not duality: J⁺ of open sets is open at every E≥0-manifold, BTZ points included, with no causality, T2 or second countability.
  - Both A2 compactness fields now hold at E≥0-manifolds.
  - Unmarked. Audit minor (M-level decls only; one docstring narrowed).
- T-ett-cauchy-ext-e0: the first Cauchy extension between E≥0-manifolds that is not onto, {T < a} ⊂ E₀.
  - lem:image_diamant, lem:passe_pgcd (as printed, both branches at frontier points) and lem:Cauchy_plongement_toutes are now witnessed off the identity. It is a past set, so the conclusions there are immediate; this is disclosed.
  - The past-set lemma is ported verbatim from lean-gx. The planner's step (b) failed as cited, since CurvesExtend is image containment only (kb/0212).
  - Unmarked. Audit minor (docstring reworded).
- master: SingularRowsDiamond's SCOPE now names both new modules; kb/0201 updated.
- gates: lean-causal ✓ (strict 0 sorry in 293 files; scaffold 6 in 7), roadmap ✓, ledgers ett/barbot/sbierski-mghd/ers-predictability ✓, atlas ✓ (lean-causal facts at a2924ea, clean), hub: no new red
- commits: 99e9e06 a2924ea 35e1933 (+ this)
- wall time: 02:08–02:56 (Paris); agents: 2 closers, 2 audits
- new OQ: none (next free OQ-88); lean-causal kb 0207–0214
- next: plan (rule 2: no ready closer). The planner research targets T-3p1-funnel-lemma and T-bbs-archive are still waiting.

## 2026-11-22 03:36 · plan + research (rule 2: no ready closer target after wave 34)
- result: 139 -> 140 targets.
  - Added T-ett-sc-cauchy-e0 (ready, p7, lean-causal): A2's last field, secondCountable_of_cauchy, at E≥0-manifolds. A connected, Hausdorff E≥0-manifold with a second countable Cauchy surface is second countable, with no global hyperbolicity used. The route is [r]: Reg M second countable (DEC-49), countably many singular lines each meeting Σ, Lindelöf, then a countable chart cover.
  - Note on T-ett-cbg-e0: after T-ett-sc-cauchy-e0, every A2 field holds at E≥0-manifolds. A1, A3, A4 and LocalModel still need gx.
- rejected:
  - T-ett-cbg-e0 waits on the T-ett-cbg-typeagreement chain (/ett-programme).
  - DEC-8 CausallyOpen has no row (a ladder fact).
  - lem:C_ext_connexe's E≥0 form duplicates /ett-programme's ready T-abs-c-ext-connexe-second-countable, which certifies more.
  - prop:Cauchy_pgcd needs a morphism reading (DEC-17 vs DEC-60).
  - (iii)⇒(i) stays on OQ-32.
- research:
  - T-3p1-funnel-lemma done (3443270): Lemma F holds at the [r] level by the lifted holonomy (NOTES-3+1 N9). N5's minimiser sketch fails once a cone angle is ≥ π; it holds when every angle is < π. N9 §7 reads N5's Theorem G parabolic row differently.
  - T-bbs-archive partial (06760c5): CFGO 1994 and Matschull 1999 archived. Gott, CFG 1992, DJtH and 't Hooft need journal copies. It stays ready.
- new OQ: OQ-88 (Θ₋ as the angle of the lifted holonomy; bears on OQ-36); OQ-89 (Theorem G's parabolic row).
- gates: roadmap ✓, registers ✓, atlas ✓, hub: no new red
- wall time: 02:57–03:36 (Paris); agents: 1 (planner)
- next: T-ett-sc-cauchy-e0 is the only ready closer, which is fewer than two, so rule 2 calls for a plan again. The roadmap is nearly exhausted without rulings.

## 2026-11-22 04:13 · short plan (none) + wave of 1 · T-ett-sc-cauchy-e0
- short plan (rule 2): no second closer target. Every non-ETT row waits on a ruling or a needs-ruling target; the kb/0061 hoists have at most two consumers. No commit. The single ready closer was then dispatched alone, since re-planning could not make progress.
- T-ett-sc-cauchy-e0: A2's last field, secondCountable_of_cauchy, holds in its own form at every Hausdorff, connected E≥0-manifold.
  - The core theorem needs no global hyperbolicity and no absolute minimality.
  - Every A2 field now holds at E≥0-manifolds. The E₀ CBG instance still waits on T-ett-cbg-e0, via /ett-programme.
  - The witnesses are vacuous in spirit, which is disclosed.
  - Finding on rem:CBG_manquant (i).
  - Unmarked. Audit minor.
- gates: lean-causal ✓ (strict 0 sorry in 294 files; scaffold 6 in 7), roadmap ✓, ledgers ett/barbot/sbierski-mghd/ers-predictability ✓, atlas ✓ (lean-causal facts at cf4fa76, clean), hub: no new red
- commits: cf4fa76 291beee (+ this)
- wall time: 03:38–04:13 (Paris); agents: 1 planner, 1 closer, 1 audit
- new OQ: none (next free OQ-90); lean-causal kb 0215–0217
- next: the wave is empty. Rule 5 applies: T-bbs-archive (planner, partial; the six remaining references need journal copies, not on arXiv). If that run cannot archive anything, rule 6 applies: idle, waiting on rulings.

## 2026-11-22 04:29 · research (rule 5: T-bbs-archive), then idle: waiting on rulings
- T-bbs-archive: four more references are archived from legitimate free sources (0e2c51a): DJtH 1984 and 't Hooft 1993 from 't Hooft's Utrecht page, DJtH 1992 from CaltechAUTHORS, 't Hooft 1992 from the Utrecht repository. 't Hooft 1992 is a scan with no text layer and has no quotes yet. NOTES-3+1 N10 records three things:
  - N4's attribution to CFG/DJtH 1992 is wrong as worded; the result is CFGO's.
  - N5's 8πG normalisation checks out against DJtH 1984.
  - 't Hooft's crunch concerns closed universes.
  
  Still missing: Gott 1991 and CFG 1992 (APS paywall), and N5-4's phase-space reference, which is never named. The target is blocked on OQ-90 (new).
- idle: the wave is empty and no planner target is ready. Every open target waits on a ruling:
  - needs-ruling: T-bz-transcription-check, T-yamabe-scope, T-egf-families (/egf-programme), T-gfn-doubledag-refresh, T-bbs-q1 / T-bbs-layer-home (BBS-Q1), T-syr-cited, T-bz-chapter3, T-yamabe-lower-bound, T-syr-empty-corollary, T-barbot-terminal.
  - blocked on an OPEN OQ: T-ett-geroch-iii-i (OQ-32), T-bz-c2-proprietes (OQ-38), T-bbs-archive (OQ-90), T-egf-universality (OQ-50), T-gx-troyanov-suspension (OQ-37), T-3p1-theorem-m-theta (OQ-36).
  - planned, waiting on /ett-programme (stopped until 2026-11-27): T-ett-cbg-typeagreement → T-ett-cbg-e0 (via T-loc-cbg-curves-default). T-gx-troyanov (s ≥ 5, mathematics under DEC-136). T-3p1-theorem-g and T-bbs-hs-model / T-bbs-rp1-circles (BBS-Q1).
  - ETT marks wait on OQ-16, OQ-18, OQ-34, OQ-35, OQ-64, OQ-82 and OQ-87.
- gates: roadmap ✓, registers ✓, atlas ✓, hub: no new red
- wall time: 04:15–04:29 (Paris); agents: 1 (planner)
- the loop stops here (rule 6). The rulings that would unblock the most are BBS-Q1 (63 rows), OQ-63, OQ-42, OQ-44, OQ-34/35, OQ-18 and OQ-82. Also: whether /atlas-team may run /ett-programme's ready targets while it is paused.

## 2026-11-22 06:23 · idle: waiting on rulings
- No DEC row since DEC-141, and every OQ that blocks a target is still OPEN: OQ-16, OQ-18, OQ-32, OQ-34, OQ-35, OQ-36, OQ-37, OQ-38, OQ-50, OQ-82, OQ-87, OQ-88, OQ-89, OQ-90.
- The wave is empty and no planner target is ready. The waiting targets are the ones the 04:29 entry lists: the needs-ruling questions (BBS-Q1, T-yamabe-scope, T-syr-cited, T-bz-chapter3, T-bz-transcription-check, T-barbot-terminal, T-gfn-doubledag-refresh, T-yamabe-lower-bound, T-syr-empty-corollary, T-egf-families), the targets blocked on OPEN OQs, and the CBG pair behind /ett-programme (stopped until 2026-11-27).
- The loop stops (rule 6).

## 2026-11-22 19:03 · idle: waiting on rulings
- New since 06:23: DEC-142 to DEC-146, all EGF's (OQ-83, OQ-84, OQ-85, OQ-47, OQ-48; /egf-programme's, DEC-141). None rules a needs-ruling question or an OQ that an /atlas-team target waits on. OQ-16, OQ-18, OQ-32, OQ-34, OQ-35, OQ-36, OQ-37, OQ-38, OQ-82, OQ-87, OQ-88, OQ-89 and OQ-90 are still OPEN.
- The wave is empty and no planner target is ready; the waiting targets are as listed at 04:29. The loop stops (rule 6).

## 2026-11-22 19:40 · wave of 6 · T-gfn-absorb, T-bz-apply-rulings, T-syr-2026-import, T-gx-troyanov-theorem-c, T-yamabe-analysis (+ T-hub-public-mirror)
- T-gfn-absorb (master): closed. GFNBoundsLean is subtree-merged into lean/ at 2e9865c, with its 160 commits. The submodule is gone, nothing rebuilt, and lib-check is green as a hub package. Its edit of lean-causal/README.md moved the lean-causal ledgers' stamp; those ledgers are left to /ett-programme, which committed into lean-causal at df620bf.
- T-bz-apply-rulings (master): closed. DEC-177–181 and DEC-206 are applied: ten Ch. 2 rows marked (benzecri: 64 closed, 0 partial), with docstring marks only. Prop. 6 is marked in its corrected form (DEC-178). Follow-up: a corrected-definition predicate for Déf. 1/1′ (z non-constant) with its own witness.
- T-syr-2026-import (master): partial, now blocked on OQ-91. hyperlolipop's ~/Syracuse working tree is snapshotted into papers/syracuse/programme-2026 (358 files). How SyracuseLean (v4.34.1, library `Syracuse`) relates to lean-syracuse is OQ-91.
- T-gx-troyanov-theorem-c: closed 1/1 label work. The row stays partial: GX.TroyanovTheoremC (strict, sorry-free), the narrower citation proved as a finding, the obligation rewired. Audit minor (round 1). OQ-92 is new.
- T-yamabe-analysis: partial, back to ready. The externals and the model layer are proved; the six manifold theorems are tagged sorrys. Audit minor (round 1). OQ-93 is new. A planner should split it.
- T-hub-public-mirror (master, added in session): closed. The author created LBrunswic/MathAtlas and answered the scope questions (DEC-207). `make mirror` pushes the filtered history (third-party material stripped, secret scan clean) and the atlas to https://lbrunswic.github.io/MathAtlas/, which loads with 0 page errors.
- Not dispatched: T-ett-gluing-causality (exclusive; the lean-causal lease is held by /ett-programme) and T-ett-apply-rulings (its marks edit strict lean-causal while /ett-programme elaborates there). Both are ready for when lean-causal is idle.
- gates: lean-benzecri ✓, lean-gx ✓, lean-yamabe ✓, lib-check ✓, roadmap ✓, registers ✓, atlas ✓. Hub: papers-check red only for egf (/egf-programme's) and the lean-causal ledgers awaiting /ett-programme's rebuild.
- commits: 24f4c85 773e369 ffcf0e1 636edca 0d786eb 09377ee ab72c4d 3739b4b [+ roadmap/atlas/journal]
- wall time: 18:11–19:40 UTC; agents in parallel: 2 closers, 2 auditors
- next: wave would pick T-ett-gluing-causality (only once lean-causal is free), T-ett-apply-rulings, T-yamabe-analysis (better split by the planner first), T-yamabe-companion, T-nonacyclic-source, T-atlas-overlay-refresh. A planning run is due (rule 2: the Yamabe split, the Déf. 1/1′ follow-up, T-gfn-doubledag-refresh now unblocked).

## 2026-11-22 21:00 · wave of 4 · T-yamabe-analysis (round 2), T-atlas-overlay-refresh, T-yamabe-companion, T-syr-apply-rulings
- T-yamabe-analysis (round 2): partial, back to ready. The manifold Sobolev, trace and finite-energy theorems are proved with their round-1 statements (HalfSpace, Localisation, ManifoldTheorems). Round 1's Mfd.const_of_tendsto is false as stated (no measurability of the limit), and its corrected form is proved. Audit minor. Round 3: rewire, repair ConstLimit, Rellich, trace_compact.
- T-atlas-overlay-refresh (builder, standing): lean-gx and lean-benzecri refreshed; lean-causal, lean-egf and lean-yamabe busy. papers/perforated is on the atlas. The panel shows every principal. Two -B rebuilds byte-identical, 0 page errors.
- T-yamabe-companion (master): closed. BrunswicPerforated is perforated.tex in Void Dynamics (6c57c10), ledgered as papers/perforated (31 statements, Lean root lean-yamabe). Closing yamabe's thm:lower-bound from it awaits the planner.
- T-syr-apply-rulings (master): closed. DEC-183 marks 17 rows in corrected form (Syracuse: 19 closed, 6 partial). cor:corollary is terminal (DEC-194). lem:syracuse_cycle waits on OQ-101 (new; renumbered from a collision with /ett-programme's OQ-94..100). A read-only helper drafted the row map; the master checked and applied it.
- Not run: T-nonacyclic-source. Fetching the Overleaf source with the stored credentials (DEC-200) was blocked by the permission classifier; the author was asked to place the source in Dropbox or allow the access. T-ett-gluing-causality and T-ett-apply-rulings wait while lean-causal is busy. T-yamabe-apply-rulings waits while a closer works in lean-yamabe.
- gates: lean-yamabe ✓, lean-syracuse ✓, roadmap ✓, registers ✓, atlas ✓, papers-check ✓, hub: no new red
- commits: 3af8e6b d80d6ea f49d088 59f3831 07b4c60 1034b2b 7611b07 [+ roadmap/atlas/journal]
- wall time: 19:40–21:00 UTC; agents in parallel: 1 closer, 1 builder, 1 helper, 2 auditors
- next: a planning run (rule 2 is near; the backlog wants cutting: Yamabe round 3 and thm:lower-bound from papers/perforated, the Déf. 1/1′ follow-up, papers/gfnbounds for lean/'s overlay, T-gfn-doubledag-refresh); then T-yamabe-apply-rulings, T-bz-c2-proprietes, T-gx-troyanov-suspension.

## 2026-11-22 21:40 · plan (rule 2: five iterations since the last planner run)
- roadmap-planner: 153 → 169 targets (16 added, 7 changed); `check` passes.
  - T-yamabe-analysis is cut up. The integration of round 2 is a master target (T-yamabe-integrate-r2: rewire the primes, repair ConstLimit). The Rellich criterion is a closer target (T-yamabe-rellich-criterion). The monolith narrows to Rellich's manifold half (planned), with integrate-r3 and trace-compact after it.
  - papers/perforated is cut toward yamabe's thm:lower-bound: T-perf-capacity, T-perf-star3 (ready), then T-perf-main, star-n, upper, poincare, T-yamabe-thm-lower-bound and T-perf-cor-yamabe (planned).
  - T-bz-poche-nonconstant (DEC-178 follow-up) is ready.
  - T-gfn-doubledag-refresh and T-bbs-hs-model are promoted to ready.
- The master gave T-yamabe-apply-rulings `package = "lean-yamabe"`, so the wave tool keeps it apart from the exclusive T-yamabe-integrate-r2.
- New needs-ruling (the author):
  - T-perf-dilute-limit: thm:sharp and prop:theta-examples rest on limits the paper asserts. Formalize them in full, or only what is proved?
  - T-perf-scope: five rows rest on the sharp Euclidean Sobolev constant. Formalize them now?
  - T-gfn-ledger: ledger the GFN Bounds draft as papers/gfnbounds? The public mirror would then publish it before the ICLR decision of 16 Dec.
- next: the wave picks T-yamabe-integrate-r2, T-gfn-doubledag-refresh and the overlay refresh. The lean-causal pair waits on /ett-programme, and T-nonacyclic-source waits on the author's Overleaf source.

## 2026-11-22 23:00 · wave of 6 · T-yamabe-integrate-r2, T-gfn-doubledag-refresh, T-bz-poche-nonconstant, T-bz-c2-proprietes, T-bbs-hs-model, T-gx-troyanov-suspension
- T-yamabe-integrate-r2 (master, by a Lean agent allowed to edit the scaffold): closed. The round-2 proofs carry the round-1 names, and ConstLimit asks MemLp f 2. The Yamabe scaffold is down to 2 sorrys (Rellich, trace_compact). Audit minor. Its curation missed the moved module; the hub gate caught it, fixed at 106399b.
- T-gfn-doubledag-refresh (master): closed. The 2026-09-20 run is pinned as a dated measurement and the DAG regenerated on the in-tree lean/ (733 principals). The nine proposals were re-keyed: all present, same kinds. OQ-5/6 are re-asked as OQ-102/103 (DEC-202).
- T-bz-poche-nonconstant: closed 3/3 in corrected form (DEC-178), strict. Audit minor.
- T-bz-c2-proprietes: closed 1/1 (DEC-206/177/178), strict, and the printed enonce is proved false. Audit major, on a false worked example in the REPORT (round 1), then clean (round 2). Benzécri: 65 of 66 rows closed; the last is terminal.
- T-bbs-hs-model: closed, strict. The row's mark waits on OQ-104 (« topological surface »). Audit minor.
- T-gx-troyanov-suspension: partial, blocked on OQ-105. DEC-175 (c), Aut(Σ) ≅ Aut(M), is proved; the facts reduce to Aut(Σ) = {Id} (Lefschetz–Hopf, not at the pin). Audit minor.
- Not dispatched: the lean-causal pair (/ett-programme), T-nonacyclic-source (needs the author's Overleaf source), and T-hub-paper-attribute (it touches every package's Lean while closers run).
- gates: lean-yamabe ✓, lean-benzecri ✓, lean-gx ✓, roadmap ✓, registers ✓, atlas ✓, hub: no new red (after the 106399b fix)
- commits: af013dc d03b9ba ef66194 dc8dca0 6a3fea0 3689eb0 9821949 106399b [+ roadmap/atlas/journal]
- wall time: 21:40–23:00 UTC; agents in parallel: 4 closers + 1 integration agent, 6 audits
- next: wave: T-yamabe-rellich-criterion, T-perf-capacity, T-perf-star3 (lean-yamabe, now free); T-yamabe-apply-rulings; T-hub-paper-attribute; the builder (overlay refresh for lean-gx, lean-benzecri, lean-yamabe).

## 2026-11-23 00:05 · wave of 4 · T-yamabe-apply-rulings, T-yamabe-rellich-criterion, T-perf-capacity, T-perf-star3
- T-yamabe-apply-rulings (master, done first because its marks edit strict lean-yamabe): closed. DEC-186 makes the measured-frame model of record. lem:stability and rem:sign are marked; OQ-44/74 come off the other § 6 rows, which wait on Rellich.
- T-yamabe-rellich-criterion: closed, strict. The Lp compactness criterion, sharp; its p = 2 form closes Mfd.rellich_kondrachov's goal by exact once the chart assembly lands. Audit minor.
- T-perf-capacity: def:capstar and lem:holder closed and marked, strict; lem:capstar and lem:capacitary partial on carried hypotheses (T-perf-poincare). E-L sign finding, OQ-110. Audit minor.
- T-perf-star3: blocked on OQ-109. thm:star3's proof is wrong at l.635 and in case (ii), proved against the paper. The printed constant is invalid on the model, argued (not proved) for a Riemannian dumbbell. The corrected theorem is proved, strict. Audit minor (headline qualified).
- Not dispatched: the lean-causal pair (/ett-programme), T-nonacyclic-source (the author's Overleaf source), T-hub-paper-attribute (all packages); the builder was not due.
- gates: lean-yamabe ✓, roadmap ✓, registers ✓, atlas ✓, hub: no new red
- commits: fd1141b 3eb9839 388ae54 3712347 [+ roadmap/atlas/journal]
- wall time: 23:05–00:05 UTC; agents in parallel: 3 closers, 3 audits
- next: the builder is due (overlay refresh for lean-gx, lean-benzecri, lean-yamabe); T-perf-main and T-perf-upper (after capacity), T-perf-poincare (after integrate-r2 and star3: star3 is blocked, so it waits); T-hub-paper-attribute; Rellich's manifold half (T-yamabe-analysis, planned).

## 2026-11-23 01:05 · wave of 3 · T-perf-main, T-perf-upper, T-atlas-overlay-refresh
- T-perf-upper: closed. thm:upper and rem:notF1 marked, strict. thm:upper is true but lossy: Hölder removes the (1−ρ)^{-2} and the proviso. Audit minor.
- T-perf-main: blocked on OQ-111. thm:main is proved over the model, strict: under AbsLatticeApprox, and in a signed form needing no lattice property; eq:main-asymp with an explicit O(F²) remainder, uniform in θ. Audit major on a false claim in the REPORT (« C¹ lacks thm:main for N ≥ 4 »), withdrawn in one fix round with the hypothesis weakened; re-audit minor.
- T-atlas-overlay-refresh (builder): lean-gx, lean-benzecri, lean-yamabe and lean-syracuse refreshed; papers/perforated's first edges. Two -B runs byte-identical, 0 page errors.
- OQ-111 (thm:main readings) and OQ-112 (the convention for carried existence hypotheses) are new.
- gates: lean-yamabe ✓, roadmap ✓, registers ✓, atlas ✓. Hub: papers-check red only for papers/ett (plus gate-tests, which reruns it), from /ett-programme's uncommitted lean-causal refactor (lem:Sigma_separe's declarations moved). No atlas commit touches lean-causal or papers/ett.
- commits: ba1db2f 48e5107 68b1e81 [+ roadmap/atlas/journal]
- wall time: 00:10–01:05 UTC; agents in parallel: 2 closers, 1 builder; 3 audits plus 1 re-audit
- next: what stays ready is the lean-causal pair (/ett-programme), T-nonacyclic-source (the author), T-hub-paper-attribute (all packages) and T-bz-chapter3 (a transcription for the author to check). T-perf-poincare and the companion's thm:lower-bound chain wait on OQ-109/111 and T-perf-star3. A planning run is due soon.

## 2026-11-23 02:15 · wave of 3 · T-yamabe-analysis (round 3), T-yamabe-integrate-r3, T-bbs-rp1-circles
- T-yamabe-analysis (round 3): closed. Rellich–Kondrachov is proved on the manifold with the round-1 statement (RellichManifold.lean, sorry-free). Audit minor.
- T-yamabe-integrate-r3 (master, by a Lean agent): closed. Rellich is rewired in place of the round-1 sorry, and the lem:positivity chain rests on the standard axioms ([IsFiniteMeasure μ] dropped, a strengthening). The Yamabe scaffold has one sorry left, trace_compact, unused. The § 6 marks wait only on OQ-93; the chain graduates once trace_compact leaves Trace.lean.
- T-bbs-rp1-circles: closed, strict. bbsdef:circle_data_point_structure marked; G̃ and the real angle built. Readings in OQ-113. Audit major (a false orientation claim in prose), fixed in one round; re-audit minor.
- Promoted from planned (all dependencies done): T-yamabe-analysis, T-bbs-rp1-circles.
- gates: lean-yamabe ✓, lean-gx ✓, roadmap ✓, registers ✓, atlas ✓, hub: no new red
- commits: 0554c47 72dfea8 4d17421 460791d e3220f0 07617c2 [+ roadmap/atlas/journal]
- wall time: 01:10–02:15 UTC; agents in parallel: 2 closers + 1 integration agent, 4 audits
- next: T-yamabe-trace-compact (now unblocked; it frees the scaffold chain to graduate), T-3p1-theorem-m-theta and T-bbs-layer-home (after rp1-circles; the angle waits on OQ-113), T-hub-paper-attribute. A planning run is due (rule 2, five iterations at the next one).

## 2026-11-23 02:45 · plan (rule 2: five iterations since the last planner run)
- roadmap-planner: 170 → 175 targets (6 added, 10 changed), `check` passes.
  - Added:
    - T-yamabe-graduate-analysis (master, exclusive): trace_compact moves to its own scaffold file, and the nine sorry-free modules go to strict;
    - T-bbs-i-pm, T-bbs-photon-circles (§ 5.1, the missing layer for M-theta and OQ-113 (b)), T-3p1-funnel-gtilde (Lemma F's G̃ half; (N) carried) and T-bbs-hs-singularities (planned);
    - T-atlas-tex-text-macros (builder: the benzecri \bzcf raw in the panel).
  - T-perf-star-n is ready (no dependency on the cap that broke thm:star3, [r]). T-perf-poincare now waits on T-yamabe-graduate-analysis, since the strict perforated modules cannot import the scaffold's RellichProp. T-3p1-theorem-m-theta adds bbsrem:causally_regular_hs_sphere_containing and depends on T-bbs-photon-circles. T-bbs-layer-home is re-scoped (several dispatches).
- No new question for the author.
- next: a wave of T-yamabe-graduate-analysis (exclusive in lean-yamabe), T-bbs-i-pm, T-bbs-photon-circles, T-3p1-funnel-gtilde (lean-gx) and the builder's T-atlas-tex-text-macros.

## 2026-11-23 04:10 · wave of 4 · T-yamabe-graduate-analysis, T-bbs-i-pm, T-bbs-photon-circles, T-3p1-funnel-gtilde
- T-yamabe-graduate-analysis (master, by a Lean agent): closed. The nine sorry-free § 6 modules are strict (lean-yamabe: strict 20 files, 0 sorry), and trace_compact sits alone in the scaffold. T-perf-poincare is unblocked.
- T-bbs-i-pm: closed, strict. The developing map of a (Γ_p, ℓ(p))-circle; lies_domain marked; the other two rows partial. Finding: l.828–833's tangent directions (l.835–836, l.844 false as printed). OQ-116. Audit minor.
- T-bbs-photon-circles: closed, strict (research). PSL(2,ℝ) ≃ SO₀(1,2), ℝP¹ ≃ ∂ℍ²₊, photon-circle ℝP¹-structures, ι_L. OQ-117. Audit minor.
- T-3p1-funnel-gtilde: closed (research, kept in the scaffold for the author). Lemma F's G̃ half from N9; (F4) fails at a = 0 under OQ-113 (d). Audit minor.
- gates: lean-yamabe ✓, lean-gx ✓, roadmap ✓, registers ✓, atlas ✓, hub (see the gates line)
- commits: 9fbefdd 117bce5 b5ea22c 7706e0d [+ roadmap/atlas/journal]
- wall time: 02:40–04:10 UTC; agents in parallel: 3 closers + 1 graduation agent, 4 audits
- next: T-perf-poincare, T-perf-star-n, T-yamabe-trace-compact (lean-yamabe); T-3p1-theorem-m-theta (after photon circles); the builder (T-atlas-tex-text-macros, overlay refresh) is due.

## 2026-11-23 05:25 · wave of 6 · T-yamabe-trace-compact, T-perf-poincare, T-perf-star-n, T-atlas-overlay-refresh, T-3p1-theorem-m-theta, T-bbs-hs-singularities
- T-yamabe-trace-compact: closed, strict. No sorry is left in lean-yamabe; the § 6 marks wait on OQ-93. Audit minor.
- T-perf-poincare: closed, strict (λ₁ ∈ (0,∞), MeanPoincare, a finite C_SP). The companion rows blocked on it now name OQ-109–112. Audit minor.
- T-perf-star-n: closed, strict. prop:starN under OQ-118's readings (Ã, c_q); lem:elem marked. Audit minor.
- T-atlas-overlay-refresh (builder, standing): Lean edges refreshed for lean-gx and lean-yamabe (f490811); back to ready.
- T-3p1-theorem-m-theta: closed (research, kept in the scaffold for the author). Θ₋ = Θ₊ for every regular de Sitter annulus with no named hypothesis. bbsrem:causally_regular_hs_sphere_containing is partial: proved under IsIotaPrime for every Θ, and with no hypothesis when Θ₋ > 0. OQ-119. Audit minor (two docstrings fixed; a duplicate lemma left for a cleanup).
- T-bbs-hs-singularities: partial, done for this dispatch. 10 tagged sorrys in the scaffold. bbsrem:previous_section_observed_only is partial and unmarked, its three assertions proved under readings. Finding: l.794–800 need « with non-trivial holonomy ». OQ-120. Audit round 1 major (a false time-like clause in a paper finding), fixed; round 2 minor. Its evidence names the four-part split for the planner.
- Ledger: an unmarked row whose extra_lean_files include a strict file reads as strict/closed. The two partial bbs rows now carry scaffold/partial overrides (4399232).
- gates: lean-yamabe ✓, lean-gx ✓, roadmap ✓, registers ✓, atlas ✓, hub: make -k check rc 0, no new red
- commits: 3b71ab0 c99dc29 106f726 f490811 4211879 59052ae 4399232 [+ roadmap/atlas/journal]
- wall time: 03:53–05:25 UTC; agents in parallel: 5 closers + 1 builder, 7 audits (one fix round)
- New questions for the author: OQ-119 (Θ = 0 without ι'_L as a target? the remark's bucket D scope; « degree included » at Θ = 0) and OQ-120 (« isomorphic » with the same p; « holonomy ⟨g⟩ » in G̃; positive/negative in l.915's form).
- next: only one ready closer target is left (T-ett-gluing-causality, lean-causal, /ett-programme's package), so the next iteration plans: split T-bbs-hs-singularities along its four groups and refill the lean-gx and lean-yamabe queues.

## 2026-11-23 05:55 · plan (rule 2: no dispatchable ready closer target outside lean-causal)
- roadmap-planner: 175 → 192 targets (17 added, 3 changed); roadmap check ✓.
- T-bbs-hs-singularities' 10 sorrys split:
  - wave A, three new upstream files, ready in parallel: T-bbs-psl2-normal-forms, T-bbs-quotient-circle, T-bbs-gammap-elements;
  - then T-bbs-hs-remark-existence (closes bbsrem:previous_section_observed_only modulo OQ-120), then T-bbs-hs-link-types (the file sorry-free);
  - then T-bbs-remark-readings (proves both readings of OQ-120 (a) and (c)) and T-bbs-hs-graduate (master, exclusive).
- The next BBS layer:
  - ready: T-bbs-hs-suspension (bbsdef:singular_hs_surface_oriented_surface, mark on OQ-104);
  - planned: T-bbs-p-p, T-bbs-classising-types, T-bbs-degk, T-bbs-positive-hs-surface, T-bbs-hcausal;
  - T-bbs-layer-home narrowed to the AdS half; T-3p1-theorem-g now depends on positive and causal HS-spheres.
- T-bbs-curation-blockers (master, ready): 57 bbs rows still name BBS-Q1, which DEC-192 ruled.
- lean-yamabe:
  - T-yamabe-thm-lower-bound planned → ready (thm:main's Lean is already strict; the instance waits on OQ-109, 111, 118);
  - T-yamabe-poincare-binder (master cleanup: the redundant [IsFiniteMeasure], confirmed by AUDIT-1 of T-perf-poincare).
- lean-gx cleanup: T-gx-mtheta-dedupe. No photon-circle target is needed: isPhotonCircle_bdMinus/bdPlus and modelAnnulus already show DSAnnulus is not vacuous.
- lean-benzecri: only T-bz-chapter3 is open (bzthm:intro_C waits on it).
- New question for the author: T-bbs-q8 (needs-ruling, BBS-Q8, REVIEW §F item 8). The rows on singular AdS spacetimes in § 3.4–3.6 need a suspension into AdS₃. Build it hard-wired to AdS₃ as printed, or as one κ-family (AdS₃ at κ = −1, flat E^{1,2} at κ = 0)?
- next: a wave of T-bbs-psl2-normal-forms, T-bbs-quotient-circle, T-bbs-gammap-elements (lean-gx) and T-yamabe-thm-lower-bound (lean-yamabe), with the master targets T-ett-apply-rulings (when lean-causal is idle) and T-bbs-curation-blockers. lean-causal waits on /ett-programme.

## 2026-11-23 06:40 · wave of 5 · T-bbs-psl2-normal-forms, T-bbs-quotient-circle, T-bbs-gammap-elements, T-yamabe-thm-lower-bound, T-bbs-curation-blockers
- T-bbs-gammap-elements: closed, strict (GX/BBS/GammaPElements.lean). Single elements of Γ_p: at time-like p, 1, the half-turn or elliptic; at light-like p, parabolic iff ≠ 1. It closes two HSSingularities sorrys once wired. Audit minor (a duplicate of lean-causal's lemma, removed).
- T-bbs-psl2-normal-forms: closed, sorry-free, kept in the scaffold because it imports FunnelGTilde. The hyperbolic, parabolic and elliptic normal forms, which close three HSSingularities sorrys once wired. No paper finding. Audit minor (two docstring points, fixed).
- T-bbs-quotient-circle: closed, strict (GX/BBS/QuotientCircle.lean). J/⟨f⟩ as a (G, X)-circle, with its ℝP¹ and (Γ_p, ℓ(p)) instances; closes exists_rp1Circle_of_ne_one and the construction half of exists_positive_negative once wired. Finding: l.721–722 is false for the trivial subgroup (« non-trivial » is the correction). Audit minor (fixed).
- T-yamabe-thm-lower-bound: closed, strict (Yamabe/LowerBound.lean), thm:lower-bound partial and unmarked. Finding: the theorem needs σ^∂(Σ) ≥ 0, which the companion states and yamabe does not. Audit clean.
- T-bbs-curation-blockers (master): 57 bbs rows re-pointed from the ruled BBS-Q1 (DEC-192) to their current blockers.
- Promoted, their dependencies done: T-bbs-hs-remark-existence and T-perf-cor-yamabe → ready.
- gates: lean-gx ✓ (strict 60 files), lean-yamabe ✓ (strict 25 files), roadmap ✓, registers ✓, atlas ✓, hub: make -k check rc 0, no new red
- commits: 2f27056 2aae116 d7a05bb 7c93c5d 77297c2 a24d992 e392bdc [+ roadmap/atlas/journal]
- wall time: 05:53–06:40 UTC; agents in parallel: 4 closers, 4 audits (no fix round)
- New questions for the author: OQ-121 (yamabe thm:lower-bound: σ^∂ ≥ 0 or T³ only; the weights of the mean; « Yb »), OQ-122 (Γ_p « generated by a parabolic element »; the lift reading of l.748–749), OQ-123 (« translations, i.e. freely and properly discontinuously »; « naturally »).
- next: T-bbs-hs-remark-existence and T-bbs-hs-suspension (lean-gx), T-perf-cor-yamabe (lean-yamabe); the lean-causal targets wait on /ett-programme; the builder (T-atlas-overlay-refresh) is due.

## 2026-11-23 07:45 · wave of 5 · T-bbs-hs-remark-existence, T-bbs-hs-suspension, T-perf-cor-yamabe, T-atlas-tex-text-macros, T-gx-mtheta-dedupe
- T-bbs-hs-remark-existence: closed (scaffold). HSSingularities.lean goes from 10 sorrys to 5, all T-bbs-hs-link-types'. « Does not extend » is proved (exists_positive_negative, exists_rp1Iso_not_isIso). bbsrem:previous_section_observed_only is proved in its readings, with no sorry beneath it, and stays partial and unmarked. OQ-124. Audit minor (orientation disclosed, the question reworded).
- T-bbs-hs-suspension: closed, strict (GX/BBS/HSSuspension.lean, 183 declarations). 𝔢(L) ≃ₜ HS², an HS-surface off its apices, with chart changes in Γ_p via developing data. bbsdef:singular_hs_surface_oriented_surface is partial (OQ-104, OQ-126). Audit minor (fixed at graduation).
- T-perf-cor-yamabe: closed, strict (Yamabe/Perforated/CorYamabe.lean), restated over thm:lower-bound; cor:yamabe partial. Findings: Yb(Σ) = 0 and M are unsupported in either paper. OQ-125. Audit clean.
- T-atlas-tex-text-macros (builder): paper text-mode macros are now expanded outside math (14 statements fixed). New hub gate gate-atlas, with its fixture under tools/fixtures/atlas, wired in by the master.
- T-gx-mtheta-dedupe (master): TheoremMTheta uses the strict eq_of_continuous_intValued.
- Promoted, its dependencies done: T-bbs-hs-link-types → ready.
- gates: lean-gx ✓ (strict 61 files), lean-yamabe ✓ (strict 26 files), roadmap ✓, registers ✓, atlas ✓, hub: make -k check rc 0, gate-atlas green, no new red
- commits: 4cdca6c 361f203 f416687 97ba018 ff939f9 01c849b 0d8a058 [+ roadmap/atlas/journal]
- wall time: 06:38–07:45 UTC; agents in parallel: 3 closers + 1 builder, 4 audits (no fix round)
- New questions for the author: OQ-124 (« same holonomy » in « does not extend »), OQ-125 (cor:yamabe: Yb = 0, M, θ → 1, the O(F) factor), OQ-126 (singular HS-surfaces: « oriented », « HS-isomorphic », independence from the developing data).
- next: T-bbs-hs-link-types (lean-gx; it leaves HSSingularities sorry-free). lean-causal waits on /ett-programme. The lean-gx and lean-yamabe queues are thin after it: a planning run is due soon.

## 2026-11-23 08:25 · wave of 1 · T-bbs-hs-link-types
- T-bbs-hs-link-types: closed. HSSingularities.lean is sorry-free (211 declarations): the arc structure of ℓ(p), the time-like and light-like types through GammaPElements, the degree-0 types at dS² and ∂ℍ²±, and the components of I±. It stays in the scaffold until FunnelGTilde and PSL2NormalForms graduate (T-bbs-hs-graduate). Findings: Misner (l.877–878) is false as printed under OQ-116 (a); the printed closed arc at l.887–888 is never the developed image (OQ-116 (b)). Audit minor (citations, a duplicate, existence marked as argued; fixed).
- Only one target was dispatchable: the other ready closers are in lean-causal, held by /ett-programme. T-hub-paper-attribute was left for the planner, because it adds a LeanLink dependency to every package.
- Promoted, their dependencies done: T-bbs-remark-readings, T-bbs-hs-graduate (master, exclusive), T-bbs-p-p, T-bbs-degk, T-bbs-positive-hs-surface and T-bbs-hcausal → ready.
- gates: lean-gx ✓ (scaffold 3 tagged sorrys, all Troyanov/Thurston), roadmap ✓, atlas ✓, hub: make -k check rc 0, no new red
- commits: 3de13af cbe0e7a [+ roadmap/atlas/journal]
- wall time: 07:44–08:25 UTC; agents: 1 closer, 1 audit
- No new OQ: the findings are evidence for OQ-116 (a) and (b).
- next: a lean-gx wave (T-bbs-p-p, T-bbs-positive-hs-surface, T-bbs-degk or T-bbs-hcausal, at most 3 per package; T-bbs-hs-graduate is exclusive and goes alone). A planning run is due soon (rule 2, five iterations since 05:55): T-hub-paper-attribute's split, and the lean-yamabe and lean-benzecri queues.

## 2026-11-25 10:20 · wave of 4 (resumed) · T-ett-geroch-iii-i, T-bbs-p-p, T-bbs-positive-hs-surface, T-bbs-degk
- Dispatched 2026-11-23 08:26. The author stopped three of its agents at 09:13 (the p_p and degk closers, the Geroch audit), and the loop stopped without integrating. This /atlas-team run resumed the active targets: it re-audited degk and Geroch, had a new closer finish p_p's draft, and integrated all four.
- T-ett-geroch-iii-i (round 2, DEC-148/149): partial.
  - Geroch (iii)⇒(i) needs no quasi-limits. The engine and the causally-open form are sorry-free; the ruled form (DEC-148 alone) rests on one sorry, open (OQ-130 (a)).
  - theo:geroch_sing is sorry-free under DEC-149.
  - Local causal closedness is shown necessary (chronological Minkowski space).
  - AUDIT-2 minor; fixed: the « weakest reading » claim and wording.
- T-bbs-positive-hs-surface: partial (scaffold). IsPositive, SingularHSStructure.IsPositive, coneAngle; a degree-4 circle separates l.915's positivity from l.908–913's. OQ-128. Audit minor.
- T-bbs-degk: partial (scaffold). Degree 2k is the k-sheeted cover of degree 2, and a branched covering of the suspensions, branched at the apices; Γ_p is a one-parameter group. OQ-129. Audit minor.
- T-bbs-p-p: partial (scaffold). The flip 𝔢(L) ≅ 𝔢(L⁻); finding: l.936–937 is false for Misner singularities (opposite chiralities; true under SO(1,2)). OQ-131. Audit minor.
- Seeded for /restate: bbs bbsrem:p_p (its refutation); the restate gate requires the entry (f596d62).
- Rulings applied: DEC-210, T-gfn-ledger → ready. DEC-208 (papers/btz) and DEC-209 (papers/alexandrov, lean-alexandrov) name targets not yet in the roadmap: for the planner. Promoted: T-bbs-classising-types → ready.
- gates: lean-causal ✓, lean-gx ✓ (scaffold 3 tagged sorrys), roadmap ✓, registers ✓, atlas ✓, hub: make -k check rc 0 after the seed
- commits: be0a76e 51f1107 65fbe21 d9791b6 49d0ddb 104b902 f596d62 [+ roadmap/atlas/journal]
- New questions for the author: OQ-128 (positive HS-surfaces: « singularity », the apex, some or every link), OQ-129 (« k-branched cover »), OQ-130 (Geroch: does (iii)⇒(i) hold under DEC-148 alone?), OQ-131 (p_p: moved-p isomorphisms and SO₀(1,2), « the link determines the singularity »).
- next: a planning run is due (rule 2, five iterations since 2026-11-23 05:55). It should create DEC-208's and DEC-209's targets (T-btz-ledger, T-btz-maximal-extension, T-alexandrov-package) and split T-hub-paper-attribute. Ready: T-bbs-classising-types, T-gfn-ledger (master), the BBS hcausal and remark-readings targets, T-bbs-hs-graduate.

## 2026-11-25 · plan · roadmap-planner (rule 2)
- Added 17 targets, changed 3 (roadmap check: 209 targets, all rules hold).
  - DEC-208: T-btz-ledger (master, ready), T-gx-causal-pin-bump (master, ready, exclusive; lean-gx's Causal pin ca2ad78 lacks AbstractDev), T-gx-uniformization-via-btz (planned), T-btz-scope (needs-ruling). The btz close targets wait for the ledger (labels must exist).
  - DEC-209: T-alexandrov-ledger (master, ready), T-alexandrov-package (needs-ruling: DEC-209 vs DEC-211 on a package of its own).
  - T-hub-paper-attribute narrowed to a pilot in lean/; T-hub-paper-attr-curation (planned), T-hub-paper-attr-rollout (needs-ruling).
  - DEC-211/212: T-arch-import-gate, T-arch-multiroot-ledgers (master, ready); T-arch-multiroot-atlas, T-arch-pin-bump-tool (planned).
  - lean-yamabe: T-yamabe-closed-leaves, T-yamabe-boundary-gap, T-yamabe-brown-york (ready), T-yamabe-gap-corollaries (planned). lean-gx: T-bbs-link-remarks (planned).
  - T-bbs-archive → planned (N11 in papers/bbs/NOTES-3+1.md derives N5-4's phase-space claim, [r]; the rest needs journal PDFs from the author). T-bz-chapter3 p9 → p7.
- gates: roadmap ✓, atlas ✓, hub: 2 failures in gate-tests, both papers/gx/certificate/RESTATED.md not rendered — a file held mid-wave by the live /restate lease, not this run's.
- New questions for the author: T-btz-scope (E_{≥0} as printed, or E₀ only), T-alexandrov-package (create lean-alexandrov now, or put it in lean-gx), T-hub-paper-attr-rollout (a lean-paper package outside DEC-211's seven?).
- next: a wave of T-yamabe-closed-leaves, T-yamabe-boundary-gap (lean-yamabe), T-bbs-classising-types, T-bbs-hcausal (lean-gx), with master set-ups T-btz-ledger / T-alexandrov-ledger.

## 2026-11-27 15:20 · wave of 5 · T-ett-gluing-causality, T-yamabe-closed-leaves, T-yamabe-boundary-gap, T-bbs-classising-types, T-gfn-ledger
- Dispatched 2026-11-25 12:52; every closer stopped at the weekly usage limit the same afternoon and was resumed on 2026-11-27 after the reset.
- T-ett-gluing-causality: closed in substance, strict (Causal/GluingCausality.lean), no row marked. DEC-167's GluedCausality = Causality + the hereditary gluing field (OQ-95's reading). prop:GX_espace_temps_topo's uniqueness holds under gluing. Two refutations of the ruling's expectations, audited as faithful: ex:open_subset's first uniqueness is false even under gluing (OQ-107); rem:deux_pushup's « neither implies the other » is false (plain ⇒ push-up on T1). The REPORT carries the strict-refactor plan (for the planner). Audit minor (round 1).
- T-yamabe-closed-leaves: def:yamabe, prop:csc-yamabe partial, strict. Finding: (a)'s uniqueness is false for R ≡ 0 on a disconnected Σ. Audit clean.
- T-yamabe-boundary-gap: def:yamabe-bdry, prop:gap-bdry-nonneg, prop:accel-bdry partial, strict. Findings: EHB undefined for ∂Σ = ∅; σ^∂'s finiteness unstated (standard). Audit minor. Both files defined avgR identically; ClosedLeaves now imports BoundaryGap's.
- T-bbs-classising-types: the link half, sorry-free, scaffold (graduates with HSSingularities). Finding: the printed list of types needs a trivial-holonomy type (degree ≥ 4). Audit minor (line citations).
- T-gfn-ledger (master): papers/gfnbounds, the draft at b83dd0f, 131 statements, closure 96 of 96; curation seeded from the draft's ledger; nine stale decl names in lean/paper-map.json updated.
- Held back: the curation of ett rem:deux_pushup, cexemple:point_transparent and bbs bbsprop:classising. Each becomes a strong restatement candidate, and the ett and bbs registers are held by the live /restate loop. Their Lean is committed; curate them when the registers are free.
- Tooling: the repository crossed git's auto-abbreviation threshold, so every ledger's git_commit grew to 8 digits; tools/ledger.py pins core.abbrev=7 (6e6a83c).
- gates: lean-causal ✓, lean-yamabe ✓, lean-gx ✓, roadmap ✓, registers ✓, atlas ✓, papers-check all green, hub: make -k check rc 0, no new red
- commits: 3f0815d 502be84 3a8e7df 9348fb6 6e6a83c [+ bbs blocker, roadmap/atlas/journal]
- wall time: 2026-11-25 12:51–13:25 and 2026-11-27 14:17–15:20 UTC; agents in parallel: 4 closers, 4 audits (one fix round)
- New questions for the author: OQ-132 (Yamabe § 2: Σ connected? σ(Σ), the uniqueness reading), OQ-133 (Yamabe § 3: the φ class, σ^∂, ∂Σ ≠ ∅ for EHB), OQ-134 (ex:open_subset under the M-only gluing form), OQ-135 (bbsprop:classising: the trivial-holonomy type, line types, occurrence, isomorphism notion).
- next: a planning run should add the strict gluing refactor of lean-causal (after OQ-95/OQ-96). Ready: T-yamabe-brown-york, T-bbs-hcausal, T-bbs-remark-readings, T-ett-plainness-models; master T-btz-ledger, T-alexandrov-ledger, T-gx-causal-pin-bump; the builder T-atlas-overlay-refresh is due.

## 2026-11-27 16:00 · wave of 5 · T-ett-plainness-models, T-yamabe-brown-york, T-bbs-remark-readings, T-bbs-hcausal, T-btz-ledger
- T-ett-plainness-models: prop:K_calcul CERTIFIED (Causal.PlainnessModels.K_calcul, strict): the printed route through causal plainness (DEC-168), every reading ruled. cor:K_lorentzien proved over a new layer-3 model, locally Lipschitz Lorentzian metrics (push-up, plainness, absolute minimality), unmarked: OQ-136. Audit minor.
- T-yamabe-brown-york: def:reference, prop:brown-york partial, strict. Finding: the Schwarzschild clause holds at N = 3 only (Tangherlini: 2m/(N−1)). Audit minor, one fix round: the reference embedding was trivially inhabited; strengthened with an area clause, and SCOPE says it carries area, not shape. OQ-137.
- T-bbs-remark-readings: the remark under both readings of OQ-120 (a)/(c), scaffold, sorry-free; the two positivity forms agree in every degree in the hyperbolic setting (sharpens OQ-128). Audit minor. OQ-138.
- T-bbs-hcausal: partial, scaffold, 3 tagged sorrys (tachyons, trivial holonomy, the degree of an apex link). The Misner CCC and the causal line types are sorry-free. Finding: the « in other words » fails read for non-compact surfaces; recorded as a scope imprecision (audit minor). OQ-139.
- T-btz-ledger (master): papers/btz, 55 statements with btz-prefixed labels; lean-gx's 18 B21 rows anchored, all partial (E₀ only; T-btz-scope). tools/texgraph.py reads « Proofs of Lemmas … » (test added).
- Held back for the restatement register (held by /restate): bbsdef:Hcausal's curation, with the three rows of the previous wave.
- gates: lean-causal ✓, lean-yamabe ✓, lean-gx ✓, roadmap ✓, registers ✓, atlas ✓, papers-check all green, hub: make -k check rc 0, no new red
- commits: b3d3b7c 0b83ff2 5b76222 fe59a20 3270b2a [+ roadmap/atlas/journal]
- wall time: 14:46–16:00 UTC; agents in parallel: 4 closers, 4 audits, one fix round
- New questions for the author: OQ-136 (« Lorentzian manifold » = locally Lipschitz?), OQ-137 (Brown–York readings; Schwarzschild for N ≠ 3), OQ-138 (the remark's readings), OQ-139 (Hcausal readings, the scope of « in other words »).
- next: the builder T-atlas-overlay-refresh (due); planner: DEC-208's btz close targets now that papers/btz exists, and the lean-causal gluing refactor. Ready master: T-alexandrov-ledger, T-gx-causal-pin-bump, T-arch-*.

## 2026-11-27 16:20 · plan · roadmap-planner (rule 2: no ready closer left)
- 22 targets added, 2 promoted, 1 refined (roadmap check: 232 targets, all rules hold).
  - papers/btz (DEC-208), all E₀-scoped: T-btz-curation-existing (master, ready), T-btz-embeddings, T-btz-reg-complete, T-btz-blunt-spear (closers, ready); T-btz-pgcd → T-btz-ppcm-hausdorff → T-btz-ppcm → T-btz-maximal-extension (with T-gx-causal-pin-bump) → T-btz-common-reg, T-btz-cauchy-spear → T-btz-cauchy-conservation, T-btz-headline (planned). T-gx-uniformization-via-btz now depends on T-btz-maximal-extension and T-btz-reg-complete.
  - Gluing refactor: its split lives in programme/roadmap.toml (T-abs-gluing-*, /ett-programme's, behind OQ-95/OQ-96); hub follow-ups T-ett-gluing-curation and T-gx-causal-gluing-bump (blocked on OQ-95).
  - lean-gx: T-bbs-hcausal-tachyons (ready), T-bbs-hcausal-apex-degree (blocked, OQ-139). lean-yamabe: T-yamabe-conformal-gap (ready). Promoted: T-yamabe-gap-corollaries, T-bbs-link-remarks.
  - T-restate-held-curation (master): the four held rows, once /restate frees the ett and bbs registers.
  - Architecture: T-arch-rename-tool, T-arch-package-leases (ready), T-arch-move-window (planned). GFN: T-gfn-appendix-scope (needs-ruling), T-gfn-finit-elementary (planned).
- lean-causal has no ready /atlas-team target: every remaining ETT row waits on an OQ, on the programme's CBG port, or on smooth Lorentzian manifolds.
- New question for the author: T-gfn-appendix-scope (formalize the 23 bucket-B appendix rows of GFN Bounds in lean/, or keep them out of scope as the draft does?).
- gates: roadmap ✓, atlas ✓
- next: a wave of T-btz-embeddings, T-btz-reg-complete, T-bbs-hcausal-tachyons (lean-gx, 3) and T-yamabe-gap-corollaries, T-yamabe-conformal-gap (lean-yamabe), with T-btz-curation-existing (master); the builder T-atlas-overlay-refresh is due.

## 2026-11-27 17:20 · wave of 6 · T-btz-embeddings, T-btz-reg-complete, T-yamabe-gap-corollaries, T-yamabe-conformal-gap, T-atlas-overlay-refresh, T-btz-curation-existing
- T-btz-embeddings: btz § 5's vocabulary, strict and sorry-free (GX.BTZ.Embeddings): BTZ-embeddings and -extensions, the morphism class btzMor in AbstractDev's shape, common sub/over-extensions. Six rows partial (E₀ only). Audit minor (marks, citations; fixed).
- T-btz-reg-complete: Reg M is GH and Cauchy-maximal, sorry-free, without completeness; its Cauchy-completeness is one tagged sorry (infinitely many spears), scaffold. Findings: « applies as is » (l.1571) does not (the compact proof uses finitely many BTZ lines); Σ's acausality in M̄ is not argued. Audit minor.
- T-yamabe-gap-corollaries: cor:gap-nonneg, cor:volume partial, strict; the paper's own chains proved, cited inputs carried. Audit minor (checklist row; fixed). OQ-140.
- T-yamabe-conformal-gap: rem:conformal-gap partial, strict; hypothesis-free on the manifold reading. Its l.423 « finding » is imprecise wording, true in context (audit minor). OQ-141.
- T-atlas-overlay-refresh (builder): overlay refreshed for lean-causal, lean-benzecri and lean/ (gfnbounds' first edges); block titles without raw TeX; blocks in ledger order. Back to ready: lean-gx and lean-yamabe still to refresh.
- T-btz-curation-existing (master): six btz rows anchored on lean-gx's E₀ Lean; the btz ledger now has 31 of 55 rows Lean-stated.
- gates: lean-yamabe ✓, lean-gx ✓, roadmap ✓, registers ✓, atlas ✓ (twice, identical), papers-check all green, hub: make -k check rc 0, no new red
- commits: 2e601b3 f03ec37 749b441 1fac0f5 4c3a0d8 [+ roadmap/atlas/journal]
- wall time: 15:45–17:20 UTC; agents in parallel: 4 closers + 1 builder, 4 audits
- New questions for the author: OQ-140 (gap corollaries' readings), OQ-141 (rem:conformal-gap's scope), OQ-142 (btz § 5: a.e. morphisms, connected carriers, over-extension morphisms, Cauchy-complete).
- next: T-btz-blunt-spear, T-bbs-hcausal-tachyons, T-bbs-link-remarks (lean-gx) and the builder for lean-gx/lean-yamabe; lean-yamabe's queue is empty again, so a planning run follows soon.

## 2026-11-27 18:30 · wave of 4 · T-btz-blunt-spear, T-bbs-hcausal-tachyons, T-bbs-link-remarks, T-atlas-overlay-refresh
- T-btz-blunt-spear: btzdef:blunt_spear_neighborhood sorry-free; the lemma's core sorry-free with two facts the paper uses implicitly (null rays without endpoints), its paper form on two tagged sorrys. Finding: l.721's « essentially the same » does not transfer. Audit minor, one fix round (the chart quantifier). OQ-143.
- T-bbs-hcausal-tachyons: the two HSCausal sorrys closed, both statements true: no CCC for tachyons (every degree) or trivial holonomy, proved on the covering; 𝔢(L) has a CCC iff L is Misner. One sorry left (apex-link degree). Audit clean.
- T-bbs-link-remarks: both remarks sorry-free. AUDIT-1 major: the cuttachyon2 « error » depended on the holonomy sign convention, and an AdS support claim was wrong. After one round the finding is convention-free (the two printed clauses cannot both hold under any single gluing rule); AUDIT-2 minor. OQ-144.
- T-atlas-overlay-refresh (builder): lean-yamabe's overlay (yamabe 31 → 45 edges, perforated 25 → 30). Back to ready for lean-gx.
- Held for the restatement register (/restate): the bbs rows bbsdef:Hcausal, bbsrem:cuttachyon2, bbsrem:however_no_positive_negative (blockers updated); btz's rows curated.
- gates: lean-gx ✓, roadmap ✓, registers ✓, atlas ✓, papers-check all green, hub: make -k check rc 0, no new red
- commits: df63ad2 a1c3971 eb5a115 [+ roadmap/atlas/journal]
- wall time: 16:15–18:30 UTC; agents in parallel: 3 closers + 1 builder, 5 audits, two fix rounds
- New questions for the author: OQ-143 (the blunt-spear readings; an ordering at l.1601–1604), OQ-144 (which holonomy sign convention is of record; it decides cuttachyon2 and may bear on HSPositive's signs).
- next: no ready closer target is left besides the builder: a planning run (rule 2).

## 2026-11-27 18:45 · plan · roadmap-planner (rule 2)
- 9 targets added, 1 promoted, 2 refined (roadmap check: 241 targets, all rules hold).
  - Promoted: T-btz-pgcd → ready (T-btz-embeddings done).
  - From today's tagged sorrys (btz, lean-gx, E₀): T-btz-blunt-vertical-ray (ready; sectorChartBTZ in the a.e. atlas first), T-btz-blunt-infall-ray (planned); T-btz-spear-family (ready) → T-btz-reg-complete-cauchy → T-btz-reg-complete-length (planned), the three steps of RegComplete's sorry.
  - T-gx-btz-cleanup (master, exclusive, p8): E0Pushout's ι₂ field (drop the copied block), one continuous_of_isE0Mor, CutGlue onto DSLe.
  - T-perf-capacity-remarks (lean-yamabe, ready): perforated rem:connected, rem:tight, rem:dichotomy. T-yamabe-perf-triage (master): bucket and blocker for the untriaged yamabe/perforated rows.
  - T-bbs-cheminsing (lean-gx, ready): bbsrem:masspositive, bbsrem:cheminsing, under both holonomy conventions (OQ-144 open).
  - Refined: T-btz-cauchy-conservation now depends on T-btz-reg-complete-length; T-3p1-theorem-g stays planned (OQ-113, wave W4).
- /ett-programme holds lean-causal; nothing here needs it.
- No new question for the author.
- gates: roadmap ✓, atlas ✓
- next: T-btz-pgcd, T-btz-blunt-vertical-ray, T-btz-spear-family (lean-gx), T-perf-capacity-remarks (lean-yamabe), masters T-yamabe-perf-triage; the builder for lean-gx after the wave.

## 2026-11-27 19:30 · wave of 6 · T-btz-pgcd, T-btz-blunt-vertical-ray, T-btz-spear-family, T-perf-capacity-remarks, T-yamabe-perf-triage, T-atlas-overlay-refresh
- T-btz-pgcd: a maximal common sub-BTZ-extension exists (sorry-free, no GH needed); the domain's GH is one tagged sorry. Findings: injectivity needs only Hausdorff; « by construction maximal » (l.1376) needs the open sorry. Audit clean. OQ-146.
- T-btz-blunt-vertical-ray: GX.BTZ.SectorAtlas (strict: sector charts in the maximal a.e. atlas) closes the vertical ray; one blunt-spear sorry left. Audit clean.
- T-btz-spear-family: step (1) of Reg M's completeness, sorry-free: a locally finite disjoint spear family. Finding: the paper asserts it from the compact case. Audit minor (copied strict lemmas, for T-gx-btz-cleanup).
- T-perf-capacity-remarks: rem:connected, rem:tight, rem:dichotomy strict and partial. rem:tight's third clause (l.569–570) holds only when cap* = cap_D, refuted on a three-point model; rem:connected's title is imprecise. Audit minor. OQ-147. rem:connected and rem:tight wait for the perforated restatement register (/restate).
- T-yamabe-perf-triage (master): every yamabe and perforated row bucketed.
- T-atlas-overlay-refresh (builder): lean-gx refreshed, btz's first edges (34 of 55 labels with Lean).
- OQ-145 was taken by /ett-programme during the wave; this wave's btz row is OQ-146.
- gates: lean-gx ✓, lean-yamabe ✓, roadmap ✓, registers ✓, atlas ✓, papers-check green, hub: make -k check rc 0, no new red
- commits: 48cf838 789fe25 f1f3b04 86be42e 98d4ea6 [+ roadmap/atlas/journal]
- wall time: 17:08–19:30 UTC; agents in parallel: 4 closers + 1 builder, 4 audits
- New questions for the author: OQ-146 (btz pgcd: which M₁ ∧ M₂ is of record), OQ-147 (perforated remarks' readings; rem:tight's third clause).
- next: see `roadmap.py wave`.

## 2026-11-27 19:50 · plan · roadmap-planner (rule 2)
- Promoted: T-btz-blunt-infall-ray, T-btz-reg-complete-cauchy, T-btz-ppcm-hausdorff → ready. T-gx-btz-cleanup p8 → p6 (it gains the spear-family copies; three lean-gx closers build on what it changes, so it goes first); T-gx-causal-pin-bump p7 → p8; T-btz-ppcm depends on the cleanup.
- Added: T-btz-pgcd-dom-gh (planned; closing it makes OQ-146 (b) moot), T-btz-isom-e0 (ready), T-bbs-positive-mass (ready), T-bbs-informal-triage (master, waits for /restate's bbs register). roadmap check: 245 targets.
- Exhaustion: lean-yamabe and perforated are exhausted for /atlas-team (everything left waits on OQ-93, OQ-109, OQ-111, T-perf-scope, T-perf-dilute-limit); gx is essentially done; lean-gx continues on the btz chain, but every btz row stays partial until T-btz-scope rules.
- Rulings that block the most rows: T-btz-scope (55 btz rows), T-bbs-q8 (34 bbs), ETT OQ-34/35/18/82 (30–37 each), T-gfn-appendix-scope (23), OQ-93 (21 yamabe/perforated), T-perf-scope (8), OQ-142 (7).
- gates: roadmap ✓, atlas ✓
- next: T-gx-btz-cleanup (exclusive in lean-gx) first, then the lean-gx closers (ppcm-hausdorff, reg-complete-cauchy, infall-ray, cheminsing, isom-e0, positive-mass).

## 2026-11-27 20:40 · wave of 2 · T-gx-btz-cleanup, T-atlas-overlay-refresh
- T-gx-btz-cleanup (master, exclusive, executed by a closer): E0Pushout records its ι₂ E₀-morphism; one continuity lemma for E₀-morphisms; the strict spear-surgery lemmas take IsCauchySurface + RimC1 and their scaffold copies are gone; CutGlue bridged to DSLe by Iff.rfl (merging the definitions is left to graduation, since HSLinkRemarks must not import HSCausal's sorry). −197 scaffold lines, behaviour-preserving. Audit minor (kb/0152, updated).
- T-atlas-overlay-refresh (builder): lean-yamabe's overlay after Yamabe.CapacityRemarks; the perforated hub entry corrected. lean-gx's overlay is due again after the clean-up.
- The closer left a self-matching `pgrep "lake build GX"` wait loop running in lean-gx until its 50-minute timeout; the master's kill was refused by the permission classifier. Harmless, but `pgrep` build checks in lean-gx read busy until it expires.
- gates: lean-gx ✓, roadmap ✓, atlas ✓, papers-check green, hub: make -k check rc 0, no new red
- commits: be9a077 8dc8637 b25dd0d [+ roadmap/atlas/journal]
- next: the lean-gx closers (T-btz-ppcm-hausdorff, T-btz-reg-complete-cauchy, T-btz-blunt-infall-ray, T-bbs-cheminsing, T-btz-isom-e0, T-bbs-positive-mass; three per wave).

## 2026-11-27 22:00 · wave of 3 · T-btz-ppcm-hausdorff, T-btz-reg-complete-cauchy, T-btz-blunt-infall-ray
- T-btz-ppcm-hausdorff: the Hausdorff half of btzprop:ppcm, sorry-free; the maximal domain is GH, so btzprop:pgcd's full form holds sorry-free with fewer hypotheses (T-btz-pgcd-dom-gh is closed in substance; only a file move remains, since PpcmHausdorff imports Pgcd). Findings: two typos (l.1430, l.1439), unproved steps bypassed, pgcd's maximality rests on ppcm's third bullet. Audit clean. OQ-148.
- T-btz-reg-complete-cauchy: step (2) of Reg M's completeness, sorry-free, with infinitely many spears, needing only M GH and S Cauchy. Audit minor.
- T-btz-blunt-infall-ray: the blunt-spear lemma sorry-free in the paper's form; GX.BTZ.BluntSpear graduated to strict. The unrestricted auxiliary was false for R ≤ 0 and is deleted (its refutation kept). Audit minor.
- gates: lean-gx ✓, roadmap ✓, registers ✓, atlas ✓, papers-check green; hub: make -k check rc 2, one new red, gate-tests' test_shipped_rules_and_tests_are_generated: lean-causal/Causal/Ladder/Test.lean is stale against programme/ladder.toml, both uncommitted /ett-programme work in progress under its live lease (lean-causal, programme). This wave touched neither path; the master's script pushed before reading the gate's verdict, and this line corrects the first version of the entry.
- commits: e49f488 f4490bd [+ roadmap/atlas/journal]
- wall time: 18:35–22:00 UTC; agents in parallel: 3 closers, 3 audits
- New question for the author: OQ-148 (ppcm's readings; two typos and two unproved steps of the printed proof).
- next: T-bbs-cheminsing, T-btz-isom-e0, T-bbs-positive-mass (lean-gx), T-btz-reg-complete-length, T-btz-ppcm; T-btz-pgcd-dom-gh can be closed by moving globallyHyperbolicOn_maxDom below Pgcd.

## 2026-11-27 23:30 · wave of 3 · T-btz-ppcm, T-btz-pgcd-dom-gh, T-btz-reg-complete-length
- T-btz-ppcm: btzprop:ppcm proved for E₀-manifolds, sorry-free (GX.BTZ.Ppcm): the glued M₁ ∨ M₂ is an E₀-manifold, globally hyperbolic, minimal among all common over-extensions and unique under both readings of « minimal ». Findings: l.1417–1419 unproved, « minimal » undefined; a needless case split; M₀ GH unused. Audit minor (one round). OQ-149.
- T-btz-pgcd-dom-gh: Pgcd's sorry gone (the chart step moved to GX.BTZ.ExtChart; every declaration keeps name and type). The chain ExtChart → Pgcd → PpcmHausdorff → Ppcm graduated to strict. Audit clean.
- T-btz-reg-complete-length: the import cycle broken; Reg M's completeness down to one sharper sorry (a tail of a Cauchy sequence of Σ* in a compact of M). Findings: « as is » fails exactly across infinitely many spears; summable radii avoid a uniform constant. Audit minor (~950 copied lines to clean up).
- gates: lean-gx ✓, roadmap ✓, registers ✓, atlas ✓, papers-check btz green; hub: make -k check rc 2, new red papers-check papers/ett (cor:massA_cac: Causal.ChartIso.curveOn_symm not found) — lean-causal is held and being edited by /ett-programme (uncommitted), and this wave touched no lean-causal or ett path. Verdict read before the push.
- commits: c1e4234 d6d607c [+ roadmap/atlas/journal]
- wall time: 19:13–23:30 UTC; agents in parallel: 3 closers, 3 audits, one fix round
- New question for the author: OQ-149 (ppcm's « minimal » and « unique »: which reading is of record).
- btz now: pgcd and ppcm proved for E₀; maximal-extension waits on T-gx-causal-pin-bump; every row partial until T-btz-scope.
- next: T-gx-causal-pin-bump (master, exclusive), then T-btz-maximal-extension; T-bbs-cheminsing, T-btz-isom-e0, T-bbs-positive-mass.

## 2026-11-28 00:10 · wave of 1 · T-gx-causal-pin-bump
- T-gx-causal-pin-bump (master, exclusive, executed by a closer): lean-gx's Causal requirement moved from ca2ad78 to 51cbb00 (the last committed lean-causal). Nothing broke; Causal.AbstractDev and the E_α models now import in lean-gx, which opens DEC-208's route for T-btz-maximal-extension.
- gates: lean-gx ✓, roadmap ✓, atlas ✓; hub: the first make -k check failed test_no_model_in_gates because papers/ett was mid-edit by /ett-programme; rerun rc 0, no new red (verdict read before the push).
- commits: c1d9a45 da1354c [+ roadmap/atlas/journal]
- next: T-btz-maximal-extension, then T-bbs-cheminsing, T-btz-isom-e0, T-bbs-positive-mass (lean-gx).

## 2026-11-28 02:00 · wave of 3 · T-btz-maximal-extension, T-btz-isom-e0, T-bbs-cheminsing
- T-btz-maximal-extension: the maximal BTZ-extension for E₀ (btzthm:BTZ_ext and its two restatements), as an instance of Causal.AbstractDev (DEC-208), sorry-free given the named cited input RichardsInput (Richards' theorem and two uncited steps). Maximal, inextensible, universal, unique up to equivalence over M. Audit minor. OQ-150.
- T-btz-isom-e0: btzprop:isom's global form and two corollaries at E₀, strict; e0Groupoid excludes the reflection. The « isometries » and l.459 findings reworded as an imprecise wording and a terse mutatis mutandis (audit minor).
- T-bbs-cheminsing: masspositive and the cheminsing deformation, scaffold; the light-like and space-like members are positive only in the gluing-map convention — evidence for OQ-144 (OQ-151). Curation waits on the bbs register (/restate).
- gates: lean-gx ✓, roadmap ✓, registers ✓, atlas ✓, papers-check green, hub: make -k check rc 0, no new red (verdict read before the push)
- commits: dc54daa a3a3e53 [+ roadmap/atlas/journal]
- wall time: 20:02–02:00 UTC; agents in parallel: 3 closers, 3 audits
- New questions for the author: OQ-150 (btz § 5.3 and § 2 readings: connected M; how to report a row on a named cited input; « isometries »), OQ-151 (bbs: the cheminsing evidence for OQ-144).
- btz now: every row anchored in Lean through § 5 (pgcd, ppcm, the maximal extension), all partial until T-btz-scope.
- next: T-bbs-positive-mass (lean-gx); a planning run for the btz Cauchy-conservation chain and the remaining queues.

## 2026-11-28 02:20 · plan · roadmap-planner (rule 2)
- 14 targets added, 2 promoted, 4 refined (roadmap check: 259 targets).
  - Promoted: T-btz-common-reg, T-btz-cauchy-spear (neither needs RichardsInput).
  - RegCompleteLength's last sorry: T-btz-length-compare (ready) → T-btz-reg-complete-tail (planned).
  - RichardsInput: T-btz-line-structure (ready; sing₀ closed, each line an (ℝ,ℝ)-translation structure, second countable) → T-btz-richards-split (planned; the input shrinks to « countably many lines »).
  - Headline split: T-btz-admissible (ready), T-btz-hol-map, T-btz-surj-develop, T-btz-surj-spear, T-btz-surjective (planned); T-btz-headline keeps the assembly.
  - Clean-ups: T-btz-reg-complete-graduate (planned), T-btz-gluing-dedupe (ready, p10), T-bbs-cheminsing-tidy (ready).
  - Questions as needs-ruling targets: T-btz-headline-repr, T-bbs-w4-externals.
- Outside btz, lean-gx is nearly exhausted for /atlas-team: everything else waits on T-bbs-q8, OQ-139, OQ-144/151 or T-bbs-w4-externals.
- Rulings that block the most rows: T-btz-scope (55 btz), OQ-34 (37 ett), OQ-35 (35), T-bbs-q8 (34 bbs), OQ-18 (31), OQ-82 (30), OQ-93 (21), T-perf-scope (8), OQ-142 (7), OQ-150 (6).
- New questions for the author: T-btz-headline-repr (the Teichmüller and moduli readings of btzthm:princ, with Goldman–Troyanov–Hulin a named cited input), T-bbs-w4-externals (Poincaré–Hopf, Poincaré–Bendixson and the classification of compact surfaces with boundary as named cited inputs for BBS § 5).
- gates: roadmap ✓, atlas ✓
- next: T-btz-length-compare, T-btz-common-reg, T-btz-cauchy-spear (lean-gx), with the builder for lean-gx after the wave.

## 2026-11-28 04:00 · wave of 3 · T-btz-length-compare, T-btz-common-reg, T-btz-cauchy-spear
- T-btz-length-compare: the tool for Reg M's last sorry, sorry-free: the two length systems are the same chart at common points; rim arcs have length exactly R|Δφ|. Audit minor (docstrings). T-btz-reg-complete-tail promoted to ready.
- T-btz-common-reg: btzcor:common_reg sorry-free with no RichardsInput (uniqueness of the maximal extension), stronger than printed. Audit clean.
- T-btz-cauchy-spear: Step 1 of btzthm:BTZ_Cauchy-completness assembled, two tagged sorrys. AUDIT-1 major: a finding (lines of M₁ vs M₂) was wrong; reworded as a notational slip in one round; AUDIT-2 clean. OQ-152.
- gates: lean-gx ✓, roadmap ✓, registers ✓, atlas ✓, papers-check green, hub: make -k check rc 0, no new red (verdict read before the push)
- commits: f48fe4f c50d506 [+ roadmap/atlas/journal]
- wall time: 21:00–04:00 UTC; agents in parallel: 3 closers, 4 audits, one fix round
- New question for the author: OQ-152 (common_reg and Step 1 readings).
- btz: 42 of 55 rows Lean-stated, all partial until T-btz-scope.
- next: T-btz-reg-complete-tail, T-btz-line-structure, T-btz-admissible, T-bbs-positive-mass, T-bbs-cheminsing-tidy (lean-gx); the builder for lean-gx.

## 2026-11-27 22:15 · wave of 3 · T-btz-reg-complete-tail, T-btz-line-structure, T-bbs-positive-mass
- T-btz-reg-complete-tail: the last sorry of btzprop:reg_complete closed (RegCompleteTail; summable radii, spear-by-spear path surgery, completeness of S); prop_reg_complete(') sorry-free for E₀; row partial (T-btz-scope, OQ-142); audit minor (REPORT field, fixed). Stale docstrings in four BTZ scaffold files updated.
- T-btz-line-structure: sing₀ closed with an (ℝ,ℝ)-translation structure, each BTZ line second countable without ambient second countability; RichardsInput ⇔ CountableLinesInput (only Richards and the line-to-puncture injectivity stay cited); btzthm:BTZ_ext and btzcor:manifold_smooth_manifold_singular partial; audit minor (REPORT fields fixed).
- T-bbs-positive-mass: HasPositiveMass defined; for 𝔢(L) the unique simple closed space-like geodesic has length θ, positive mass iff θ < 2π; both rows partial on OQ-153 (new) and T-bbs-q8; audit clean.
- gates: lean-gx ✓, roadmap ✓, atlas ✓, hub: no new red; restate: 0 new candidates (btz, bbs)
- commits: 75532db0 107b21c2 1ea283c6 6cbc6876 (+ statuses)
- wall time: 21:25–22:30; agents in parallel: 3 closers + 3 auditors
- next: T-atlas-overlay-refresh (builder), T-btz-admissible, T-bbs-cheminsing-tidy; T-btz-reg-complete-graduate now unblocked by the tail

## 2026-11-27 23:05 · wave of 3 · T-btz-admissible, T-bbs-cheminsing-tidy, T-atlas-overlay-refresh
- T-btz-admissible: btzdef:tangent_translation_part and btzdef:admissible_representation closed (sorry-free, marked); btzprop:holonomy_globally_hyperbolic_cauchy_compact partial — the holonomy around a BTZ line is parabolic and tangent (sorry-free), the marked form rests on one tagged sorry (Barbot's faithful-and-discrete linear part), T-btz-headline-repr, T-btz-scope; audit minor (2 docstring points, fixed).
- T-bbs-cheminsing-tidy: refutation instances strengthened, elliptic branch inhabited, helpers namespaced; rows stay partial, curation waits on T-restate-held-curation; audit minor (kb names, header; fixed).
- T-atlas-overlay-refresh (builder): lean-gx overlay at 1ea283c (btz 94→124, bbs 37→42 edges), 0 page errors; back to ready, lean-gx due again after this wave.
- gates: lean-gx ✓, roadmap ✓, atlas ✓, hub: one NEW RED gate-tests (test_programme LadderEmit: lean-causal/Causal/Ladder/Test.lean stale against /ett-programme's uncommitted programme/ladder.toml, leased by programme pid 773086; not this wave's)
- commits: 297a3491 52e2d485 c3c98639 ce02aa24 (+ statuses)
- wall time: 22:17–23:05; agents in parallel: 2 closers + builder, 2 auditors
- next: no ready closer target: plan (rule 2); T-btz-reg-complete-graduate (planned, exclusive) awaits the planner

## 2026-11-27 23:20 · plan · roadmap-planner (rule 2)
- added 6 (T-btz-linear-part-faithful, T-btz-surface-group-nonmetabelian, T-btz-spear-union-gh ready; T-btz-cauchy-spear-m0, T-btz-cauchy-step2-surface, T-btz-cauchy-step2-max planned); promoted T-btz-richards-split (re-scoped) and T-btz-reg-complete-graduate (master, exclusive) to ready; refined T-btz-cauchy-conservation (only (ii)⇒(i) unblocked by the tail). No new needs-ruling question.
- gates: roadmap ✓ (265 targets), atlas ✓
- next: T-btz-linear-part-faithful, T-btz-spear-union-gh, T-btz-richards-split (lean-gx)
