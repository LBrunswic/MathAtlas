# MR1005085 — Troyanov, *Prescribing curvature on compact surfaces with conical singularities*

Trans. Amer. Math. Soc. 324 (1991), no. 2, 793–821; DOI 10.1090/S0002-9947-1991-1005085-9
(10.2307/2001742). Bib key `MR1005085` (`papers/gx/legacy/labeled/note.bib`). Cited at
`RamcovGX.tex:1930` (`cex:start_singular_manifold_homeomorphic`).

**Copy read.** The author-hosted PDF https://sma.epfl.ch/~troyanov/Papers/Prescribing.pdf, fetched
2026-11-21 (29 pages, 2,345,119 bytes, sha256
`e1f806c58ee288198ccd60934f0a1d00222130ab8f78ab28d5bda280138b5236`). The server omits its
intermediate certificate (`DigiCert Global G2 TLS RSA SHA256 2020 CA1`, from the AIA URI
`http://cacerts.digicert.com/DigiCertGlobalG2TLSRSASHA2562020CA1-1.crt`); curl verifies once that
certificate, in PEM, is appended to the system bundle passed as `--cacert`. ams.org answers 403 to
automated fetches. **The PDF is not committed**: every page reads « License or copyright
restrictions may apply to redistribution; see http://www.ams.org/journal-terms-of-use ». The quote
below was transcribed from the page image (the text layer garbles the formula).

## Theorem C (p. 795), verbatim

> **Theorem C.** Let $S$ be a compact Riemann surface. Let $p_1, p_2, \dots, p_n$ be points of $S$
> and $\theta_1 \le \theta_2 \le \cdots \le \theta_n$ be positive numbers. Assume
> $$0 < 2\pi\chi(S) + \sum_{i=1}^{n} (\theta_i - 2\pi) < \min\{4\pi, 2\theta_1\}.$$
> Then any smooth function on $S$, which is positive at some point is the curvature of a conformal
> metric having at $p_i$ a conical singularity of angle $\theta_i$.

For $S = \mathbb{S}^2$ ($\chi = 2$) and the constant curvature $1$, with
$\chi' := \sum_i (\theta_i - 2\pi) + 4\pi$: a spherical cone metric with angles $\theta_i$ exists
when $0 < \chi' < \min\{4\pi, 2\theta_{\min}\}$.

## Against the hub

- **The library's recollection is exact.** `GX.TroyanovAngleCondition.subcritical`
  (`lean-gx/scaffold/GXScaffold/Spherical/TroyanovAngles.lean`) derives
  $0 < \chi' < 4\pi$ and $\chi' < 2\theta_j$ for every $j$ — Theorem C's hypothesis at
  $S = \mathbb{S}^2$ — from the printed condition, and `GX.exists_isConeSphere_of_subcritical`
  (`GX/Spherical/TroyanovPolygon.lean`) proves existence under it when every $\theta_i < 2\pi$.
- **`RamcovGX.tex:1930` prints a stronger condition than Theorem C:**
  $0 < \chi' \le \min(4\pi, \theta_i : i)$, with $\theta_i$ where Theorem C has $2\theta_1$, and
  $\le$ where it has $<$. The printed condition implies Theorem C's (`subcritical`: $\chi' = 4\pi$ is
  never attained, and $\chi' \le \theta_j < 2\theta_j$), so the cex's use of Troyanov stands; it
  states the theorem for fewer angle tuples than Troyanov proves (e.g. `exists_isConeSphere_four_not_
  troyanovAngleCondition`). Recorded for the author as an OQ row (T-gx-troyanov-source).
- Troyanov's proof is variational (§5), not a construction; the hub's route stays the doubling
  constructions of T-gx-troyanov-triangle, -polygon, -four (DEC-136).
