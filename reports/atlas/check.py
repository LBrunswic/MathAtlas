#!/usr/bin/env python3
"""The atlas check: no statement of the built page carries a macro of its paper outside math.

    python3 check.py [atlas.html]   # exit 1 listing each use, or if the page has no statement

MathJax expands a paper's macros (DATA[p].macros) inside math only; outside math the panel would show
one raw. extract.py expands the text macros there (textmode.expand), so a macro this finds is a math
or TeX-programming macro used in text, or a text macro the expansion missed. Math is what MathJax
typesets (textmode.spans). The fixture that makes this fail is fixtures/atlas/run.sh.
"""
import json
import os
import re
import sys

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import textmode  # noqa: E402


def main(argv):
    page = argv[1] if len(argv) > 1 else os.path.join(HERE, "atlas.html")
    m = re.search(r"^const DATA = (.*);$", open(page, encoding="utf-8").read(), re.M)
    if not m:
        print("atlas check: FAIL %s carries no DATA" % page)
        return 1
    data = json.loads(m.group(1))
    bad, n = [], 0
    for p in sorted(data):
        mac = data[p].get("macros") or {}
        for node in data[p]["nodes"]:
            n += 1
            used = textmode.outside_math(node["tex"], mac)
            if used:
                bad.append("%s %s: %s" % (p, node["id"], " ".join("\\" + u for u in used)))
    if not n:
        print("atlas check: FAIL %s carries no statement" % page)
        return 1
    for b in bad:
        print("atlas check: macro outside math, shown raw:", b)
    if bad:
        print("atlas check: FAIL %d of %d statements carry a paper macro outside math" % (len(bad), n))
        return 1
    print("atlas check: %d statements of %d papers, no paper macro outside math" % (n, len(data)))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
