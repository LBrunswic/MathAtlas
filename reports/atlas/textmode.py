"""Statement text for the panel: a paper's text-mode macros expanded outside math, and math kept whole.

MathJax applies a paper's macros (DATA[p].macros) inside math only, so a macro the draft uses in text
mode (benzecri's \\bzcf{printed}{\\ref{...}}) would reach the panel raw. `expand` substitutes, outside
math, every macro whose body is text: no `$`, `^` or `_`, and only the text-mode commands of TEXT_WORDS
and TEXT_SYMBOLS (the panel's texHTML renders or strips those) or other text macros of the paper. A
macro whose body is math, or TeX programming, is left alone, and `outside_math` reports it: that is the
atlas check (check.py). `cut` shortens a statement without ever splitting a math span.

Math is what MathJax typesets: $...$, $$...$$, \\(...\\), \\[...\\] and the math environments of
MATH_ENVS; `\\\\` and `\\$` are escapes, as under MathJax's processEscapes. texHTML in template.html
splits on the same delimiters.
"""
import re

MATH_ENVS = ("equation", "align", "alignat", "gather", "multline", "flalign", "eqnarray", "displaymath",
             "math", "split", "array", "matrix", "pmatrix", "bmatrix", "Bmatrix", "vmatrix", "Vmatrix",
             "smallmatrix", "cases", "CD")
# Text-mode commands a text macro's body may carry: texHTML renders or strips each of them.
TEXT_WORDS = {"S", "ldots", "dots", "textellipsis", "noindent", "quad", "qquad", "thinspace",
              "textsuperscript", "index", "emph", "textit", "textbf", "ref", "eqref", "cref", "Cref",
              "cite", "item", "begin", "end"}
TEXT_SYMBOLS = set(",\\ -@&%#_{}'\"`^~\n")

BLANKS = re.compile(r"[ \t]*(?:\n[ \t]*)?")
TOKEN = re.compile(r"\\[\\$]|\$\$|\$|\\\(|\\\[|\\begin\{(%s)(\*?)\}|\\([A-Za-z]+)" % "|".join(MATH_ENVS))


def _close_dollar(s, j):
    """The index just past the `$` closing an inline span opened before j, or -1."""
    while j < len(s):
        if s[j] == "\\":
            j += 2
        elif s[j] == "$":
            return j + 1
        else:
            j += 1
    return -1


def _math_end(s, m):
    """If token m opens math, the index just past its closer (-1 if it is never closed); else None."""
    t = m.group(0)
    if t in ("\\\\", "\\$") or m.group(3):
        return None
    if t == "$":
        return _close_dollar(s, m.end())
    close = {"$$": "$$", "\\(": "\\)", "\\[": "\\]"}.get(t) or "\\end{%s%s}" % (m.group(1), m.group(2))
    k = s.find(close, m.end())
    return -1 if k < 0 else k + len(close)


def spans(s):
    """The math spans of s, as (start, end) pairs; an opener never closed is text, as for MathJax."""
    out, i = [], 0
    while True:
        m = TOKEN.search(s, i)
        if not m:
            return out
        e = _math_end(s, m)
        if e is not None and e >= 0:
            out.append((m.start(), e))
            i = e
        else:
            i = m.end()


def _body(spec):
    return (spec[0], spec[1]) if isinstance(spec, list) else (spec, 0)


def text_macros(mac):
    """The macros of `mac` whose body is text, closed under use: a body may call another text macro."""
    safe, grew = set(), True
    while grew:
        grew = False
        for name in sorted(mac):
            if name in safe:
                continue
            body, _ = _body(mac[name])
            body = re.sub(r"#[1-9#]", "", body)
            words = re.findall(r"\\([A-Za-z]+)", body)
            syms = re.findall(r"\\([^A-Za-z])", body)
            bare = re.sub(r"\\[A-Za-z]+|\\[^A-Za-z]", "", body)
            if (not re.search(r"[$^_]", bare) and all(w in TEXT_WORDS or w in safe for w in words)
                    and all(c in TEXT_SYMBOLS for c in syms)):
                safe.add(name)
                grew = True
    return safe


def _arg(s, j):
    """One undelimited TeX argument from s[j:]: (text, end), or None at the end of s."""
    while j < len(s) and s[j] in " \t\n":
        j += 1
    if j >= len(s):
        return None
    if s[j] == "{":
        d, k = 0, j
        while k < len(s):
            if s[k] == "\\":
                k += 2
                continue
            d += {"{": 1, "}": -1}.get(s[k], 0)
            if d == 0:
                return s[j + 1:k], k + 1
            k += 1
        return None
    if s[j] == "\\":
        m = re.match(r"\\(?:[A-Za-z]+|.)", s[j:], re.S)
        return (m.group(0), j + m.end()) if m else None
    return s[j], j + 1


def expand(s, mac, limit=1000):
    """s with every text macro of `mac` used outside math replaced by its body, arguments substituted.
    An expansion is rescanned (a body may call a text macro, or open math, as \\be does); `limit`
    bounds the substitutions, so a self-referent definition cannot loop."""
    safe, i = text_macros(mac), 0
    while limit > 0:
        m = TOKEN.search(s, i)
        if not m:
            break
        e = _math_end(s, m)
        if e is not None:
            i = e if e >= 0 else m.end()
            continue
        name = m.group(3)
        if name not in safe:
            i = m.end()
            continue
        body, n = _body(mac[name])
        args, j = [], m.end()
        for _ in range(n):
            a = _arg(s, j)
            if a is None:
                break
            args.append(a[0])
            j = a[1]
        if len(args) < n:
            i = m.end()
            continue
        if n == 0:   # TeX skips the blanks after a control word, and one end of line
            j = BLANKS.match(s, j).end()
        rep = re.sub(r"#([1-9#])", lambda g: "#" if g.group(1) == "#" else args[int(g.group(1)) - 1], body)
        s = s[:m.start()] + rep + s[j:]
        i = m.start()
        limit -= 1
    return s


def outside_math(s, mac):
    """The macros of `mac` that s uses outside math, in order of use."""
    found, i = [], 0
    while True:
        m = TOKEN.search(s, i)
        if not m:
            return found
        e = _math_end(s, m)
        if e is not None and e >= 0:
            i = e
            continue
        if m.group(3) in mac:
            found.append(m.group(3))
        i = m.end()


def cut(s, n):
    """s shortened to at most n characters, marked with an ellipsis, never inside a math span: a span
    the cut would split is dropped whole."""
    if len(s) <= n:
        return s
    k = next((a for a, b in spans(s) if a < n < b), n)
    return s[:k].rstrip() + " …"
