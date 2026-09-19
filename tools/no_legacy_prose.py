#!/usr/bin/env python3
"""Forget the first writing: no run of N words is shared between the legacy draft and the new text.

    python3 tools/no_legacy_prose.py --paper papers/<slug> [--n 12]   # exit 1 on any shared run

Compares `legacy/orig/**/*.tex` against everything authored for the new paper: `paper/body/**`,
`STORY.md` and `certificate/exposition/*.md`. Text is normalised before shingling (comments
stripped, `\\cmd{x}` reduced to `x`, math and environments dropped, lowercased, punctuation
removed), so a copied sentence with a retouched macro still matches. `paper/generated/**` is
exempt: its text is a function of the Lean, not of the legacy. Exact allowed strings (a
bibliographic title, a standard phrase) go one per line in `ledger/prose-allow.txt`; each must
itself be at least N words, and the allow list is printed with every run so it stays short.
Exit 2 if `legacy/orig` is absent.
"""
import os
import re
import sys

COMMENT = re.compile(r"(?<!\\)%.*")
MATH = re.compile(r"\$\$.*?\$\$|\$[^$]*\$|\\\[.*?\\\]|\\\(.*?\\\)", re.S)
MATHENV = re.compile(r"\\begin\{(equation|align|gather|multline|eqnarray)\*?\}.*?"
                     r"\\end\{\1\*?\}", re.S)
CMD_ARG = re.compile(r"\\[A-Za-z@]+\*?(?:\[[^\]]*\])?\{([^{}]*)\}")
CMD = re.compile(r"\\[A-Za-z@]+\*?")
MD_CODE = re.compile(r"`[^`]*`")
WORD = re.compile(r"[a-z0-9]+(?:'[a-z]+)?")


def normalise(text, md=False):
    if md:
        text = MD_CODE.sub(" ", text)
    else:
        text = COMMENT.sub("", text)
    text = MATHENV.sub(" ", text)
    text = MATH.sub(" ", text)
    for _ in range(3):
        text = CMD_ARG.sub(r" \1 ", text)
    text = CMD.sub(" ", text)
    return WORD.findall(text.lower())


def shingles(words, n):
    out = {}
    for i in range(len(words) - n + 1):
        out.setdefault(tuple(words[i:i + n]), i)
    return out


def files_under(root, exts):
    for dirpath, _d, names in os.walk(root):
        for nm in sorted(names):
            if nm.endswith(exts):
                yield os.path.join(dirpath, nm)


def main():
    if "--paper" not in sys.argv:
        print(__doc__)
        return 2
    paper = sys.argv[sys.argv.index("--paper") + 1]
    n = int(sys.argv[sys.argv.index("--n") + 1]) if "--n" in sys.argv else 12
    orig = os.path.join(paper, "legacy", "orig")
    if not os.path.isdir(orig):
        print("no_legacy_prose: FAIL no legacy/orig under %s" % paper)
        return 2
    allow = set()
    allow_p = os.path.join(paper, "ledger", "prose-allow.txt")
    if os.path.exists(allow_p):
        for line in open(allow_p, encoding="utf-8"):
            w = tuple(normalise(line, md=True))
            if line.strip() and len(w) < n:
                print("no_legacy_prose: FAIL allow line shorter than %d words: %r" % (n, line.strip()))
                return 1
            if w:
                allow.add(w)
                print("no_legacy_prose: allowed: %s" % " ".join(w))
    legacy = {}
    for p in files_under(orig, (".tex",)):
        for sh, i in shingles(normalise(open(p, encoding="utf-8", errors="replace").read()), n).items():
            legacy.setdefault(sh, (os.path.relpath(p, paper), i))
    targets = []
    for sub, exts, md in (("paper/body", (".tex",), False), ("certificate/exposition", (".md",), True)):
        d = os.path.join(paper, sub)
        if os.path.isdir(d):
            targets += [(p, md) for p in files_under(d, exts)]
    story = os.path.join(paper, "STORY.md")
    if os.path.exists(story):
        targets.append((story, True))
    hits = 0
    for p, md in targets:
        words = normalise(open(p, encoding="utf-8", errors="replace").read(), md=md)
        for i in range(len(words) - n + 1):
            sh = tuple(words[i:i + n])
            if sh in legacy and not any(sh in shingles(list(a), n) for a in allow):
                src, j = legacy[sh]
                print("no_legacy_prose: FAIL %s word %d shares %d words with %s (word %d): %s"
                      % (os.path.relpath(p, paper), i, n, src, j, " ".join(sh)))
                hits += 1
    if hits:
        return 1
    print("no_legacy_prose: %s — %d authored files, no %d-word run shared with the legacy"
          % (paper, len(targets), n))
    return 0


if __name__ == "__main__":
    sys.exit(main())
