#!/usr/bin/env python3
"""Write TOP_<o>.md / BOTTOM_<o>.md: the extreme cycle classes by rotation range.

For each requested length o, computes the critical gap-sum E = E_crit(o) and the
top-k / bottom-k cyclic-word classes ranked by the cycle range
R(w) = max_j S^(j) - min_j S^(j), then writes two markdown tables.

    python write_extremes.py                 # o = 10..16, k = 100
    python write_extremes.py --o 12 13 --k 50 --outdir results/extremes
"""

from __future__ import annotations

import argparse
import os

import critical_words as cw


def word_str(w):
    """Compact run-length form, e.g. (1,1,1,9) -> '1^3 9'."""
    out, i, n = [], 0, len(w)
    while i < n:
        j = i
        while j < n and w[j] == w[i]:
            j += 1
        out.append(f"{w[i]}^{j - i}" if j - i > 1 else f"{w[i]}")
        i = j
    return " ".join(out)


def tuple_str(w):
    return "(" + ",".join(map(str, w)) + ")"


def write_md(path, kind, o, res, k):
    rows = res["top"] if kind == "TOP" else res["bottom"]
    E, D = res["E"], res["D"]
    absD = abs(D)
    order = "descending" if kind == "TOP" else "ascending"
    lines = []
    lines.append(f"# {kind} {len(rows)} cycle classes by rotation range — o = {o}\n")
    lines.append(f"- **length** `o = {o}`")
    lines.append(f"- **critical gap-sum** `E = {E}`  (smallest E with `2^E > 3^o`)")
    lines.append(f"- **denominator** `D = 2^{E} - 3^{o} = {D:,}`   (`|D| = {absD:,}`)")
    lines.append(f"- **# words** `C({E-1},{o-1}) = {res['n_words']:,}`")
    enum = "exact" if res["exact"] else f"sampled {res['n_classes']:,}"
    lines.append(f"- **# cycle classes** {res['n_classes']:,} ({enum})")
    lines.append("- **metric** `R(w) = max_j S^(j) - min_j S^(j)`, "
                 "one representative (min rotation) per cyclic class")
    lines.append(f"- **ranked** {order} by `R`\n")
    lines.append(r"| rank | R | R/\|D\| | word | run-length |")
    lines.append("|---:|---:|---:|:---|:---|")
    for idx, (w, R) in enumerate(rows, 1):
        lines.append(f"| {idx} | {R:,} | {R/absD:.2f} | "
                     f"`{tuple_str(w)}` | `{word_str(w)}` |")
    lines.append("")
    with open(path, "w") as fh:
        fh.write("\n".join(lines))


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--o", type=int, nargs="+", default=[10, 11, 12, 13, 14, 15, 16])
    ap.add_argument("--k", type=int, default=100)
    ap.add_argument("--outdir", type=str, default=None)
    ap.add_argument("--max-exact", type=int, default=4_000_000)
    args = ap.parse_args()

    here = os.path.dirname(os.path.abspath(__file__))
    outdir = args.outdir or os.path.join(here, "results", "extremes")
    if not os.path.isabs(outdir):
        outdir = os.path.join(here, outdir)
    os.makedirs(outdir, exist_ok=True)

    print(f"{'o':>3} {'E':>3} {'#words':>12} {'#classes':>10} {'mode':>8} "
          f"{'minR/|D|':>9} {'maxR/|D|':>9}")
    for o in args.o:
        res = cw.critical_extremes_by_range(o, k=args.k, max_exact=args.max_exact)
        absD = abs(res["D"])
        write_md(os.path.join(outdir, f"TOP_{o}.md"), "TOP", o, res, args.k)
        write_md(os.path.join(outdir, f"BOTTOM_{o}.md"), "BOTTOM", o, res, args.k)
        minR = res["bottom"][0][1] if res["bottom"] else 0
        maxR = res["top"][0][1] if res["top"] else 0
        mode = "exact" if res["exact"] else "sampled"
        print(f"{o:>3} {res['E']:>3} {res['n_words']:>12,} {res['n_classes']:>10,} "
              f"{mode:>8} {minR/absD:>9.2f} {maxR/absD:>9.2f}")
    print(f"\nwrote TOP_<o>.md / BOTTOM_<o>.md for o in {args.o}\n  -> {outdir}")


if __name__ == "__main__":
    main()
