#!/usr/bin/env python3
"""Count `sorry` in the code of the two libraries (comments and docstrings stripped).

    python3 scripts/sorry_count.py            # prints the count per library; exit 1 if strict > 0

The strict library is compiled with warningAsError, so a `sorry` there fails the build already;
this is the same fact read off the sources, and the scaffold's count is the number to watch.
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def strip(text):
    out, i, depth, n = [], 0, 0, len(text)
    while i < n:
        if text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j == -1 else j
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def count(root):
    total, files = 0, 0
    for dirpath, _dirs, names in os.walk(os.path.join(HERE, root)):
        for name in sorted(names):
            if name.endswith(".lean"):
                files += 1
                src = open(os.path.join(dirpath, name), encoding="utf-8").read()
                k = len(re.findall(r"(?<![\w'])sorry(?![\w'])", strip(src)))
                if k:
                    print("  %s: %d" % (os.path.relpath(os.path.join(dirpath, name), HERE), k))
                total += k
    return total, files


def main():
    strict, nf = count("Yamabe")
    print("sorry (strict,   Yamabe/):                      %d in %d files" % (strict, nf))
    scaffold, ns = count(os.path.join("scaffold", "YamabeScaffold"))
    print("sorry (scaffold, scaffold/YamabeScaffold/):       %d in %d files" % (scaffold, ns))
    return 1 if strict else 0


if __name__ == "__main__":
    sys.exit(main())
