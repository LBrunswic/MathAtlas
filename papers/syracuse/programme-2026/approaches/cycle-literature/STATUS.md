# Status — cycle-literature

## Current state

Active — first full pass of [`SURVEY.md`](SURVEY.md) written (§0 closed form, §1 critical
band, §2 excluded shapes, §3 divisibility, §4 bounds, §5 proven/open ledger), synthesized
from four literature threads with primary-source citations.

## Results

- **§1 critical band — the framing is corrected.** $E$ is **not** forced to $\lceil o\log_2
  3\rceil$; rather $E/o$ is provably sandwiched $\log_2 3 \lt E/o \le \log_2(3+1/N_0)$
  (Sinisalo 2003 Lemma 1; Hercher 2023 Thm. 16; Crandall/Eliahou). Our $E(o)=\lceil o\log_2
  3\rceil$ is the rigorous *left edge* of that interval, not an equality theorem. Admissible
  $o$ are pulled toward convergent denominators of $\log_2 3$ ($5,12,41,53,306,665,\ldots$).
- **§2 excluded shapes.** Circuits ($m{=}1$, Steiner 1977); 2-cycles (Simons 2005); $m$-cycles
  for $m\le68$→$75$ (Simons–de Weger 2005) → **$m\le91$ (Hercher 2023, current record)**.
  "$68$ vs $75$" discrepancy resolved (original vs updated $N_0$). No $N_0$-independent shape
  exclusion exists.
- **Exhaustive excluded-pattern table** ([`EXCLUDED_PATTERNS.md`](EXCLUDED_PATTERNS.md)): **33
  papers** catalogued (23 classical via Lagarias's two annotated bibliographies; 8 recent
  2015–2026; 2 related-map context) with the precise cycle pattern each excludes/characterizes,
  plus a 7-item "needs human download" queue, a search log, and honesty caveats. Grown/maintained
  by the new [`/excluded-patterns`](../../.claude/skills/excluded-patterns/SKILL.md) skill;
  PDFs land in [`sources/`](sources/).
- **§3 divisibility.** Böhm–Sontacchi $D\mid S$; $D$ odd, $\gcd(D,6)=1$; Rhin/Baker linear-form
  lower bound on $|2^E-3^o|$ (exponent $\approx13.3$) — this is the provenance of the
  "Matveev zone" in `cycle-gcd`; Terras/Lagarias 2-adic admissibility.
- **§4 bounds.** Verification $N_0\approx2^{71}$ (Barina 2025) ⇒ smallest element $\gt2^{71}$;
  cycle length from $1.7\times10^7$ (Eliahou 1993) to $o\gtrsim1.375\times10^{11}$ odd steps
  (Hercher); finitely many cycles per length (proven), total finiteness open; $3x-1$ has three
  real cycles ($-1,-5,-17$) — a no-cycle proof must use more than the cycle equation.

## Dead ends

- _(none — this is a reference folder, not a proof attempt)_

## Open questions

- Verify the flagged constants against primary sources before quoting in print: Rhin exponent
  $13.3$/constant $0.46$ and de Weger's $2^{-0.158\,o}$; Böhm–Sontacchi exact pages; the
  "$\approx2.18\times10^{11}$ total terms" web figure; SdW printed $m$-bound ($68$ vs $75$).
- Cross-link the load-bearing facts into `CHEATSHEET.md` (pending).
- **7 papers queued for human download** (`EXCLUDED_PATTERNS.md` → "Needs human download"):
  Steiner 1981b, Belaga–Mignotte 2000, Simons 2008a+, Davison 1977, Steiner 1977/78,
  Pagano 2021, Chang 2026. Drop PDFs in `sources/` and run `/excluded-patterns --ingest`.
- Future-mine pass (logged, not yet done): Rozier "Lower Bound Hypothesis", arXiv:2502.00948,
  2306.15284, 1208.2556, 1010.6206, 0907.3086.

## Next step under consideration

Cross-link §3 (Rhin/Baker provenance) into `cycle-gcd/eventually-periodic.tex`'s Matveev
discussion, and add a "Known results on cycles" block to `CHEATSHEET.md`. Run
`/excluded-patterns` periodically (or after downloads) to keep the table growing.
