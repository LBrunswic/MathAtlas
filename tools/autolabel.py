#!/usr/bin/env python3
r"""Give every unlabeled statement environment of a legacy draft a `\label`, in `labeled/` only.

    python3 tools/autolabel.py -c papers/<slug>/ledger/ledger.toml [--dry-run]

The ledger keys on labels, so a statement without one has no row; this inserts
`\label{<prefix>:<slug>}` right after the `\begin{env}` (and its optional title), where the
prefix follows the kind (theo, prop, lem, cor, def, rem, ex, cex, propri, conj, q, fact, claim,
notation) and the slug comes from the optional title when there is one, else from the first
significant words of the statement. Duplicates get `_2`, `_3`. The label is the ONLY edit
(`tools/legacy_check.py` enforces it); the names are mechanical and the author may rename
them, after which the ledger's `reaffirm` accepts the new digest. Prints every insertion as
`file:line label`. Exit 0; 2 on a bad config.
"""
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ledger as lg  # noqa: E402
import texgraph as pg  # noqa: E402

PREFIX = {"theorem": "theo", "proposition": "prop", "lemma": "lem", "corollary": "cor",
          "definition": "def", "remark": "rem", "example": "ex", "counterexample": "cex",
          "property": "propri", "conjecture": "conj", "question": "q", "fact": "fact",
          "claim": "claim", "notation": "notation", "assumption": "assum"}
STOP = set("a an the of on in for and or to is are be let we any some with by from as at its this "
           "that then there where which such given every each if it into over under between".split())


def slug_from(text, n=4):
    text = re.sub(r"\\label\{[^}]*\}", " ", text)
    text = re.sub(r"\$[^$]*\$", " ", text)
    text = re.sub(r"\\[A-Za-z@]+\*?(\[[^\]]*\])?", " ", text)
    words = [w for w in re.findall(r"[A-Za-z][A-Za-z\-]+", text.lower()) if w not in STOP]
    return "_".join(w.replace("-", "_") for w in words[:n])


def main():
    argv = sys.argv[1:]
    dry = "--dry-run" in argv
    if "-c" not in argv:
        print(__doc__)
        return 2
    cfg = lg.Config(argv[argv.index("-c") + 1])
    lg.CFG = cfg
    pg.configure(main=cfg.document, notation=cfg.notation, aux=cfg.aux,
                 env_alias=cfg.env_alias, twins=cfg.twins, statement_envs=cfg.statement_envs)
    pat = lg.statement_env_pattern()
    listed = {f for f, _, _ in cfg.files_or_expand()}
    used = set()
    for rel, path in lg.tex_files_for_coverage():
        if rel not in listed:
            continue
        raw = open(path, encoding="utf-8", errors="replace").read()
        for m in re.finditer(r"\\label\{([^}]*)\}", raw):
            used.add(m.group(1))
    total = 0
    for rel, path in lg.tex_files_for_coverage():
        if rel not in listed:
            continue
        raw = open(path, encoding="utf-8", errors="replace").read()
        stripped = pg.strip_comments(raw)
        assert stripped.count("\n") == raw.count("\n")
        inserts = []      # (offset in raw, label)
        for m in pat.finditer(stripped):
            env = m.group(1)
            end = stripped.find("\\end{%s}" % env, m.end())
            body = stripped[m.end(): end if end != -1 else len(stripped)]
            if re.search(r"\\label\{", body):
                continue
            opt, j = pg.read_optional(stripped, m.end())
            kind = pg.canonical(env) or env
            base = slug_from(opt) if opt.strip() else slug_from(body)
            if not base:
                base = kind
            lab = "%s:%s" % (PREFIX.get(kind, kind[:4]), base)
            k, cand = 2, lab
            while cand in used:
                cand = "%s_%d" % (lab, k)
                k += 1
            used.add(cand)
            inserts.append((j, cand))
            line = stripped.count("\n", 0, m.start()) + 1
            print("%s:%d %s" % (rel, line, cand))
        if not inserts or dry:
            total += len(inserts)
            continue
        # Offsets in `stripped` differ from `raw` only by removed comment text; map through
        # line/column since comment stripping never removes a newline.
        raw_lines = raw.split("\n")
        st_lines = stripped.split("\n")
        for off, lab in sorted(inserts, reverse=True):
            ln = stripped.count("\n", 0, off)
            col = off - (stripped.rfind("\n", 0, off) + 1)
            assert raw_lines[ln][:col] == st_lines[ln][:col], (rel, ln + 1)
            raw_lines[ln] = raw_lines[ln][:col] + "\\label{%s}" % lab + raw_lines[ln][col:]
        open(path, "w", encoding="utf-8").write("\n".join(raw_lines))
        total += len(inserts)
    print("autolabel: %d labels %s" % (total, "would be inserted" if dry else "inserted"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
