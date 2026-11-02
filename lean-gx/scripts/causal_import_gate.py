#!/usr/bin/env python3
"""The DEC-33 import gate: `import Causal.<M>` only in Section 4's directories.

    python3 scripts/causal_import_gate.py      # exit 1 on a violation

Rules (DEC-33, BARBOT-INTERFACE.md): a module of `lean-gx` may import `Causal.*` only if it lives
under `GX/{BTZ,Lorentz}/` or `scaffold/GXScaffold/{BTZ,Lorentz}/`; never `import Causal` (the root,
which re-exports every Causal.Flat declaration) and never `CausalScaffold.*`; and no file opens both
namespaces (`open Causal GX`), whose declarations share names (UniversalCover, Deck, ...).
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ALLOWED = [os.path.join("GX", "BTZ"), os.path.join("GX", "Lorentz"),
           os.path.join("scaffold", "GXScaffold", "BTZ"), os.path.join("scaffold", "GXScaffold", "Lorentz")]


def main():
    bad = []
    for root in ("GX", "scaffold"):
        for dirpath, _dirs, names in os.walk(os.path.join(HERE, root)):
            for name in names:
                if not name.endswith(".lean"):
                    continue
                path = os.path.join(dirpath, name)
                rel = os.path.relpath(path, HERE)
                src = open(path, encoding="utf-8").read()
                imps = re.findall(r"^import\s+(\S+)", src, re.M)
                for m in imps:
                    if m == "Causal":
                        bad.append("%s: imports the Causal root" % rel)
                    elif m.startswith("CausalScaffold"):
                        bad.append("%s: imports %s (a scaffold of another package)" % (rel, m))
                    elif m.startswith("Causal.") and not any(rel.startswith(a + os.sep) for a in ALLOWED):
                        bad.append("%s: imports %s outside Section 4's directories" % (rel, m))
                for line in re.findall(r"^\s*open\s+([^\n]*)", src, re.M):
                    toks = line.split()
                    if "Causal" in toks and "GX" in toks:
                        bad.append("%s: opens both Causal and GX" % rel)
    for b in bad:
        print("causal_import_gate: FAIL " + b)
    if not bad:
        print("causal_import_gate: ok (DEC-33)")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
