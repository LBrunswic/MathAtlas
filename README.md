# LeanArticles

One repository for formalizing the author's research in Lean 4: a **common Lean library**
(`lean/`) and the **papers rebuilt from it** (`papers/<slug>/`). Each paper starts from an old
draft that is a story source only — its statements and their dependencies are extracted into a
ledger and a DAG, its story is rewritten fresh, and its prose is never reused.

    make check      # every gate; FREEZE=1 until 2026-09-25 skips the Lean library's own gate
    make selftest   # every gate shown to fail on its fixture
    make regression # the generalised ledger reproduces the GFN Bounds ledger byte for byte

Read `CLAUDE.md` for the rules and `registers/DECISIONS.md` for the author's rulings. The plan
this implements is `~/.claude/plans/the-objective-of-this-woolly-koala.md` (2026-09-19).
