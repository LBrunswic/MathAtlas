#!/usr/bin/env python3
"""Graph representation of a LaTeX draft: every statement, proof, paragraph and equation is a
node; containment, proof-of, reference, citation and body/appendix twinning are edges.

Generalised from `~/Dropbox/GFN Bounds/paper_graph.py` (2026-09-19). The parsing code is kept
verbatim; what changed is that nothing is a module constant any more -- the main file, the
notation files, the aux file, the statement environments (with per-paper aliases such as
`theo` -> `theorem`) and the body/appendix twins arrive through `configure()`, which
`ledger.py` calls from the paper's `ledger.toml`. The library imports this module; it has no
command line of its own.
"""
import os
import re
from collections import OrderedDict

# The canonical statement kinds. A paper's own environment names are mapped onto these by
# `ALIAS` (configure(env_alias=...)); the node's `subkind` is the canonical kind and the node's
# `env` is the name the .tex actually uses, which is what `\begin`/`\end` counting needs.
CANONICAL_STATEMENT_ENVS = {'theorem', 'proposition', 'lemma', 'corollary', 'definition',
                            'assumption', 'remark', 'conjecture', 'example', 'property',
                            'counterexample', 'fact', 'notation', 'question', 'claim'}
STATEMENT_ENVS = set(CANONICAL_STATEMENT_ENVS)
PROOF_ENVS = {'proof'}
FLOAT_ENVS = {'figure', 'figure*', 'table', 'table*', 'algorithm'}
MATH_ENVS = {'equation', 'equation*', 'eqnarray', 'eqnarray*', 'align', 'align*',
             'multline', 'multline*', 'gather', 'gather*'}
BLOCK_ENVS = STATEMENT_ENVS | PROOF_ENVS | FLOAT_ENVS | MATH_ENVS

ALIAS = {}          # raw env name -> canonical statement kind
TWINS = {}          # body label -> full-form label
MAIN = 'main.tex'   # the document's main file, relative to the root
NOTATION_FILES = ('notation.tex',)
AUX = None          # the .aux of the last build, relative to the root; None = no numbers
PROOF_MACROS = ()   # a paper's proof macros, read as proof environments: (open, close[, title])
PROOF_MACROS_USED = {}  # open macro -> number of proofs it opened since configure()

COMMENT = re.compile(r'(?<!\\)%.*')
INPUT = re.compile(r'\\(?:input|include)\{([^}]*)\}')
TOKEN = None        # built by _rebuild_token()
REF = re.compile(r'\\(ref|eqref|cref|Cref|autoref|pageref)\{([^}]*)\}')
CITE = re.compile(r'\\(cite|citet|citep|citeauthor|citeyear)[a-z]*\*?'
                  r'(?:\[[^\]]*\])*\{([^}]*)\}')
PAPERREF = re.compile(r'\\paperref\{([^}]*)\}')
LABEL = re.compile(r'\\label\{([^}]*)\}')


def _rebuild_token():
    global TOKEN, BLOCK_ENVS
    BLOCK_ENVS = STATEMENT_ENVS | PROOF_ENVS | FLOAT_ENVS | MATH_ENVS | set(ALIAS)
    TOKEN = re.compile(r'\\begin\{([A-Za-z][A-Za-z0-9]*\*?)\}'      # digits: \newtheorem{def1}
                       r'|\\end\{([A-Za-z][A-Za-z0-9]*\*?)\}'
                       r'|\\(subsubsection|subsection|section|appendix)\b(\*?)')


def configure(main='main.tex', notation=('notation.tex',), aux=None, env_alias=None,
              twins=None, statement_envs=None, proof_macros=None):
    """Set the per-paper parameters. Called once per ledger build."""
    global MAIN, NOTATION_FILES, AUX, ALIAS, TWINS, STATEMENT_ENVS, PROOF_MACROS
    MAIN = main
    NOTATION_FILES = tuple(notation)
    AUX = aux
    ALIAS = dict(env_alias or {})
    TWINS = dict(twins or {})
    STATEMENT_ENVS = set(statement_envs) if statement_envs else set(CANONICAL_STATEMENT_ENVS)
    PROOF_MACROS = tuple(tuple(m) for m in (proof_macros or ()))
    PROOF_MACROS_USED.clear()
    NOTATION.clear()
    _rebuild_token()


_rebuild_token()


def canonical(env):
    """The statement kind an environment name denotes, or None if it is not a statement."""
    e = env.rstrip('*')
    if e in ALIAS:
        return ALIAS[e]
    if e in STATEMENT_ENVS:
        return e
    return None


def strip_comments(text):
    return COMMENT.sub('', text)


def read_braced(text, i):
    """text[i] == '{'.  Return (content, index just past the matching '}')."""
    assert text[i] == '{'
    depth, j = 0, i
    while j < len(text):
        if text[j] == '{' and text[j - 1:j] != '\\':
            depth += 1
        elif text[j] == '}' and text[j - 1:j] != '\\':
            depth -= 1
            if depth == 0:
                return text[i + 1:j], j + 1
        j += 1
    return text[i + 1:], len(text)


def read_optional(text, i):
    """If text[i:] opens '[', return (content, index past ']'), else ('', i)."""
    j = i
    while j < len(text) and text[j] in ' \t\n':
        j += 1
    if j >= len(text) or text[j] != '[':
        return '', i
    depth, k, brace = 0, j, 0
    while k < len(text):
        c = text[k]
        if c == '{':
            brace += 1
        elif c == '}':
            brace -= 1
        elif brace == 0 and c == '[':
            depth += 1
        elif brace == 0 and c == ']':
            depth -= 1
            if depth == 0:
                return text[j + 1:k], k + 1
        k += 1
    return '', i


def parse_aux(auxfile):
    """label -> {'number': '12', 'page': '5', 'anchor': 'theorem.12'}"""
    out = {}
    if not auxfile or not os.path.exists(auxfile):
        return out
    text = open(auxfile, encoding='utf-8', errors='replace').read()
    for m in re.finditer(r'\\newlabel\{', text):
        try:
            key, j = read_braced(text, m.end() - 1)
            body, _ = read_braced(text, j)
        except (AssertionError, IndexError):
            continue
        fields, k = [], 0
        while k < len(body):
            if body[k] == '{':
                f, k = read_braced(body, k)
                fields.append(f)
            else:
                k += 1
        if key.endswith('@cref'):
            continue
        out[key] = {'number': fields[0] if fields else '',
                    'page': fields[1] if len(fields) > 1 else '',
                    'anchor': fields[3] if len(fields) > 3 else ''}
    return out


class Graph:
    def __init__(self, doc):
        self.doc = doc
        self.nodes = OrderedDict()
        self.edges = []
        self.order = 0
        self.sec_stack = []        # open section nodes, by level
        self.in_appendix = False

    # -- node bookkeeping ---------------------------------------------------
    def add(self, kind, subkind, file, line, label=None, title='', parent=None):
        nid = label if label else f'{kind}:{file}:{line}'
        base, n = nid, 2
        while nid in self.nodes:
            nid, n = f'{base}#{n}', n + 1
        self.order += 1
        self.nodes[nid] = {
            'id': nid, 'kind': kind, 'subkind': subkind, 'label': label,
            'file': file, 'line': line, 'title': title.strip(),
            'order': self.order, 'parent': parent,
            'appendix': self.in_appendix, 'text': '', 'chars': 0,
            'refs': [], 'cites': [], 'proves': None, 'proved_by': None,
            'section': self.sec_stack[-1]['id'] if self.sec_stack else None,
        }
        if parent:
            self.edges.append((parent, nid, 'contains'))
        elif self.sec_stack:
            self.edges.append((self.sec_stack[-1]['id'], nid, 'contains'))
        return self.nodes[nid]

    def finish(self, node, text):
        node['text'] = re.sub(r'\s+', ' ', text).strip()
        node['chars'] = len(node['text'])
        seen = set()
        for m in REF.finditer(text):
            for t in m.group(2).split(','):
                t = t.strip()
                if t and (m.group(1), t) not in seen:
                    seen.add((m.group(1), t))
                    node['refs'].append({'kind': m.group(1), 'target': t})
        for m in PAPERREF.finditer(text):
            node['refs'].append({'kind': 'paperref',
                                 'target': m.group(1).replace('\\_', '_')})
        for m in CITE.finditer(text):
            for k in m.group(2).split(','):
                k = k.strip()
                if k and k not in node['cites']:
                    node['cites'].append(k)


def parse_document(root='.', doc='paper'):
    """Parse MAIN and its `\\input`s in document order. Used when no explicit file list is
    given; `ledger.py` normally scans an explicit list instead, so that a commented-out
    appendix cannot leave the ledger."""
    load_notation(root, (MAIN,))
    g = Graph(doc)
    for fname, text, line0 in expand(MAIN, root):
        scan(g, fname, text, line0)
    link(g)
    return g


def expand(main, root, _seen=None):
    """Yield (file, text, first-line-number) in document order, recursing into nested
    `\\input`s (a child that inputs statement files, as DynIso's sections do). A file is
    expanded once; the main file's preamble (before `\\begin{document}`) is skipped."""
    seen = set() if _seen is None else _seen
    path = os.path.join(root, main)
    body = strip_comments(open(path, encoding='utf-8', errors='replace').read())
    start = body.find(r'\begin{document}') if _seen is None else -1
    if start != -1:
        head_lines = body.count('\n', 0, start) + 1
        body = body[start:]
    else:
        head_lines = 1
    seen.add(main)
    pos, line = 0, head_lines
    for m in INPUT.finditer(body):
        seg = body[pos:m.start()]
        if seg.strip():
            yield main, seg, line
        line += seg.count('\n')
        child = m.group(1)
        child = child if child.endswith('.tex') else child + '.tex'
        cpath = os.path.join(root, child)
        if os.path.exists(cpath) and child not in seen:
            yield from expand(child, root, seen)
        pos = m.end()
        line += body.count('\n', m.start(), m.end())
    seg = body[pos:]
    if seg.strip():
        yield main, seg, line


def proof_macros_to_env(text):
    """Rewrite a paper's proof macros as proof environments, so that `scan` sees its proofs.

    Barbot writes `\\preua … \\fin` (an open and a close macro, no environment). A macro proof ends
    at its close macro, or else at the next proof macro, statement `\\begin`/`\\end`, section or
    `\\end{document}`, whichever comes first, so that a missing close cannot swallow the statements
    after it. A close macro outside a proof (a QED box ending a statement) is left as text, so the
    statement's text, and its digest, are unchanged. A third entry
    is a title template: the macro takes one braced argument, substituted for #1 (`\\preuda{x}`,
    "Proof of \\ref{x}", which `link` resolves to x). No newline is added or removed, so line
    numbers are unchanged."""
    if not PROOF_MACROS:
        return text
    opens = {m[0]: (m[2] if len(m) > 2 else None) for m in PROOF_MACROS}
    names = sorted(set(opens) | {m[1] for m in PROOF_MACROS}, key=len, reverse=True)
    tok = re.compile(r'(%s)(?![A-Za-z])|\\(begin|end)\{([A-Za-z][A-Za-z0-9]*\*?)\}'
                     r'|\\(?:subsubsection|subsection|section|appendix)\b'
                     % '|'.join(re.escape(n) for n in names))
    out, pos, inside = [], 0, False
    for m in tok.finditer(text):
        out.append(text[pos:m.start()])
        pos = m.end()
        mac = m.group(1)
        if mac is None and m.group(2) and not canonical(m.group(3)) and m.group(3) != 'document':
            out.append(m.group(0))                      # any other environment passes through
            continue
        if mac is not None and mac not in opens and not inside:
            out.append(m.group(0))                      # a QED box outside a proof: kept as text
            continue
        if inside:
            out.append(r'\end{proof}')
            inside = False
        if mac is None:
            out.append(m.group(0))
        elif mac in opens:
            title = ''
            if opens[mac] is not None:
                j = pos
                while j < len(text) and text[j] in ' \t':
                    j += 1
                if j < len(text) and text[j] == '{':
                    arg, pos = read_braced(text, j)
                    title = '[' + opens[mac].replace('#1', arg) + ']'
            out.append(r'\begin{proof}' + title)
            inside = True
            PROOF_MACROS_USED[mac] = PROOF_MACROS_USED.get(mac, 0) + 1
    out.append(text[pos:])
    if inside:
        out.append(r'\end{proof}')
    return ''.join(out)


def scan(g, fname, text, line0):
    text = proof_macros_to_env(text)

    def lineno(i):
        return line0 + text.count('\n', 0, i)

    stack = []          # every open env: (env, node or None)
    blocks = []         # open *node* blocks only
    free_start = 0      # start of the current free-text run
    i = 0

    def flush_free(end):
        """Text not inside any block node becomes prose paragraphs."""
        raw = text[free_start:end]
        if blocks:
            blocks[-1]['_buf'].append(raw)
            return
        off = 0
        for part in re.split(r'\n[ \t]*\n', raw):
            if part.strip() and not re.fullmatch(r'[\s\\{}\[\],.]*', part.strip()):
                n = g.add('prose', 'paragraph', fname,
                          lineno(free_start + off), title=first_words(part))
                g.finish(n, part)
            off += len(part) + 2

    while True:
        m = TOKEN.search(text, i)
        if not m:
            break
        if m.group(1):                                   # \begin{env}
            env = m.group(1)
            j = m.end()
            stmt = canonical(env)
            if env in BLOCK_ENVS or stmt:
                opt, j = read_optional(text, j)
                flush_free(m.start())
                kind = ('statement' if stmt else
                        'proof' if env in PROOF_ENVS else
                        'float' if env in FLOAT_ENVS else 'equation')
                node = g.add(kind, stmt or env.rstrip('*'), fname, lineno(m.start()),
                             title=clean_title(opt),
                             parent=blocks[-1]['id'] if blocks else None)
                node['env'] = env
                node['_buf'] = []
                node['opt'] = opt.strip()
                node['_start'] = j
                stack.append((env, node))
                blocks.append(node)
                free_start = j
            else:
                stack.append((env, None))
            i = j
            continue
        if m.group(2):                                   # \end{env}
            env = m.group(2)
            if stack and stack[-1][0] == env and stack[-1][1] is not None:
                node = stack.pop()[1]
                blocks.pop()
                flush_free_into(node, text[free_start:m.start()])
                body = ''.join(node.pop('_buf'))
                if PROOF_MACROS and node['kind'] == 'proof':
                    node['end_line'] = lineno(m.start())    # a macro proof has no \end in the file
                g.finish(node, body)
                labs = LABEL.findall(body)
                if labs and not node['label']:
                    relabel(g, node, labs[0])
                # A statement's further \label's are aliases of its key: external papers carry
                # the hub's label first and the authors' after it, and the authors \ref their own.
                if node['kind'] == 'statement' and node['label']:
                    node['aliases'] = [l for l in labs if l != node['label']]
                free_start = m.end()
            elif stack and stack[-1][0] == env:
                stack.pop()
            i = m.end()
            continue
        cmd, star = m.group(3), m.group(4)               # sectioning
        if cmd == 'appendix':
            g.in_appendix = True
            i = m.end()
            continue
        j = text.find('{', m.end())
        if j == -1:
            i = m.end()
            continue
        title, j = read_braced(text, j)
        flush_free(m.start())
        level = {'section': 1, 'subsection': 2, 'subsubsection': 3}[cmd]
        while g.sec_stack and g.sec_stack[-1]['level'] >= level:
            g.sec_stack.pop()
        parent = g.sec_stack[-1]['id'] if g.sec_stack else None
        node = g.add('section', cmd, fname, lineno(m.start()),
                     title=clean_title(title), parent=parent)
        node['level'] = level
        node['starred'] = star == '*'
        tail = text[j:j + 200]
        lm = LABEL.match(tail.lstrip())
        # A section's label sits in its first paragraph -- but not past the next `\begin{`:
        # a statement opening right under the heading, with its own `\label` on the next line
        # and no blank line between, must keep that label (EGF's `theo:negative_control_appendix`
        # was captured by its section this way and vanished from the ledger).
        lm = LABEL.search(tail.split('\n\n')[0].split('\\begin{')[0]) if not lm else lm
        if lm:
            relabel(g, node, lm.group(1))
        g.finish(node, title)
        g.sec_stack.append(node)
        free_start = j
        i = j

    flush_free(len(text))


def flush_free_into(node, raw):
    node['_buf'].append(raw)


def relabel(g, node, label):
    if label in g.nodes:
        return
    old = node['id']
    node['label'] = label
    node['id'] = label
    g.nodes[label] = node
    del g.nodes[old]
    g.edges[:] = [(label if a == old else a, label if b == old else b, k)
                  for a, b, k in g.edges]
    for n in g.nodes.values():
        if n.get('parent') == old:
            n['parent'] = label
        if n.get('section') == old:
            n['section'] = label


GREEK = {
    'alpha': 'α', 'beta': 'β', 'gamma': 'γ', 'delta': 'δ', 'Delta': 'Δ',
    'epsilon': 'ε', 'varepsilon': 'ε', 'eta': 'η', 'theta': 'θ', 'kappa': 'κ',
    'lambda': 'λ', 'Lambda': 'Λ', 'mu': 'μ', 'nu': 'ν', 'pi': 'π', 'Pi': 'Π',
    'rho': 'ρ', 'varrho': 'ϱ', 'sigma': 'σ', 'Sigma': 'Σ', 'tau': 'τ',
    'phi': 'φ', 'varphi': 'φ', 'psi': 'ψ', 'omega': 'ω', 'Omega': 'Ω',
    'rightarrow': '→', 'leftarrow': '←', 'to': '→', 'mapsto': '↦',
    'leq': '≤', 'geq': '≥', 'neq': '≠', 'infty': '∞', 'in': '∈',
    'times': '×', 'otimes': '⊗', 'cdot': '·', 'ldots': '…', 'dots': '…',
    'll': '≪', 'sim': '~', 'circ': '∘', 'partial': '∂', 'nabla': '∇',
    'min': 'min', 'max': 'max', 'sup': 'sup', 'inf': 'inf', 'log': 'log',
    'ell': 'ℓ', 'mathbb': '', 'mathcal': '', 'mathrm': '', 'text': '',
    'widehat': '^', 'hat': '^', 'bar': '¯', 'tilde': '~', 'emph': '',
    'textit': '', 'textbf': '', 'left': '', 'right': '', 'frac': '',
    'GFNlambda': 'λ', 'star': '*', 'quad': ' ',
}
NOTATION = {}


def load_notation(root='.', extra=()):
    """\\def\\X{...} and \\newcommand{\\X}{...} from the notation files and the mainfile."""
    text = ''
    for f in tuple(NOTATION_FILES) + tuple(extra):
        path = os.path.join(root, f)
        if os.path.exists(path):
            text += strip_comments(
                open(path, encoding='utf-8', errors='replace').read()) + '\n'
    if not text:
        return
    raw = {}
    for m in re.finditer(r'\\(?:def|newcommand)\s*\{?\\([A-Za-z]+)\}?\s*(?=\{)', text):
        body, _ = read_braced(text, text.index('{', m.end() - 1))
        raw[m.group(1)] = body
    for name, body in raw.items():
        for _ in range(3):
            body = re.sub(r'\\([A-Za-z]+)',
                          lambda x: raw.get(x.group(1), '\\' + x.group(1)), body)
        NOTATION[name] = _plain(body)


def _plain(s):
    s = re.sub(r'\\([A-Za-z]+)', lambda m: GREEK.get(m.group(1), m.group(1)), s)
    return re.sub(r'\s+', ' ', s.replace('{', '').replace('}', ''))


def clean_title(s):
    s = re.sub(r'\\label\{[^}]*\}', '', s)
    s = re.sub(r'\\(?:ref|eqref|cref|Cref)\{([^}]*)\}', r'<<\1>>', s)
    s = re.sub(r'\\cite[a-z]*\*?(?:\[[^\]]*\])*\{([^}]*)\}',
               lambda m: '[' + m.group(1).split(',')[0] + ']', s)
    for _ in range(3):
        s = re.sub(r'\\([A-Za-z]+)',
                   lambda m: NOTATION.get(m.group(1)) or
                   ('\\' + m.group(1) if m.group(1) not in GREEK
                    else GREEK[m.group(1)]), s)
    s = re.sub(r'\\[A-Za-z]+', '', s)
    s = s.replace('{', '').replace('}', '').replace('$', '')
    return re.sub(r'\s+', ' ', s).strip(' .,')


def first_words(s, n=9):
    s = re.sub(r'\\[A-Za-z]+(\{[^}]*\})?', ' ', s)
    s = re.sub(r'\$[^$]*\$', '·', s)
    w = re.sub(r'\s+', ' ', s).strip().split(' ')
    return ' '.join(w[:n]) + ('…' if len(w) > n else '')


# « Proofs of Lemmas \ref{x} and \ref{y} » (a joint proof, btz l.719) proves its first statement; the
# others are curated (nl_status_override).
PROOF_OF = re.compile(r'Proofs? of\s+(?:[A-Za-z.\\ ~]*)\\ref\{([^}]*)\}')
# Titles PROOF_OF misses (T-texgraph-proof-titles): « of Proposition \ref{x} », and a title whose
# only \ref names a statement (« First variation at u = 1 (Remark~\ref{x}) »).
OF_REF = re.compile(r'^\s*of\s+(?:[A-Za-z.\\ ~]*)\\ref\{([^}]*)\}')
TITLE_REF = re.compile(r'\\ref\{([^}]*)\}')


def proof_title_key(g, opt, proof_alias):
    """The statement a proof's optional title names, or None (then the proof proves the most recent
    statement still without one). « Proof of [Kind]~\\ref{x} », « of Kind \\ref{x} », or a title whose
    only \\ref resolves to a statement label (the authors' own labels through `proof_alias`)."""
    def resolve(lab):
        if lab in g.nodes and g.nodes[lab]['kind'] == 'statement':
            return lab
        return proof_alias.get(lab)
    for pat in (PROOF_OF, OF_REF):
        m = pat.search(opt)
        if m:
            k = resolve(m.group(1))
            if k:
                return k
    refs = TITLE_REF.findall(opt)
    if len(refs) == 1:
        return resolve(refs[0])
    return None
FULL_OF = re.compile(r'\\ref\{([^}]*)\}')


def link(g):
    """proves / twin / ref / cite edges."""
    nodes = list(g.nodes.values())
    for n in nodes:
        n.pop('_start', None)

    # proof -> statement; a proof titled by the authors' own (secondary) label proves that statement
    proof_alias = {}
    for n in nodes:
        for a in n.get('aliases', ()):
            proof_alias.setdefault(a, n['id'])
    pending = []      # statements not yet matched to a proof, most recent last
    g.unresolved_proof_titles = []
    for n in nodes:
        if n['kind'] == 'statement':
            pending.append(n)
        elif n['kind'] == 'proof':
            tgt = None
            key = proof_title_key(g, n.get('opt', ''), proof_alias)
            if key is None and '\\ref{' in n.get('opt', ''):
                # a title naming no statement: kept for ledger.py check, never serialized
                g.unresolved_proof_titles.append((n['file'], n['line'], n['opt']))
            if key:
                tgt = g.nodes[key]
            else:
                while pending:
                    cand = pending.pop()
                    if cand['proved_by'] is None:
                        tgt = cand
                        break
            if tgt is not None:
                n['proves'] = tgt['id']
                tgt['proved_by'] = n['id']
                g.edges.append((n['id'], tgt['id'], 'proves'))

    # body statement <-> appendix full form
    for body, full in TWINS.items():
        if body in g.nodes and full in g.nodes:
            g.edges.append((full, body, 'full_form_of'))
            g.nodes[full]['twin_of'] = body
            g.nodes[body]['twin'] = full
    for n in nodes:
        if n['kind'] == 'statement' and 'form of' in n.get('opt', ''):
            m = FULL_OF.search(n['opt'])
            if m and m.group(1) in g.nodes and 'twin_of' not in n:
                g.edges.append((n['id'], m.group(1), 'full_form_of'))
                n['twin_of'] = m.group(1)
                g.nodes[m.group(1)]['twin'] = n['id']

    # reference and citation edges
    labels = {n['label'] for n in nodes if n['label']}
    alias = {}
    for n in nodes:
        for a in n.pop('aliases', ()):
            if a not in labels:
                alias.setdefault(a, n['label'])
    for n in nodes:
        n.pop('opt', None)
        for r in n['refs']:
            kind = 'eqref' if r['kind'] == 'eqref' else r['kind']
            if r['target'] in labels:
                g.edges.append((n['id'], r['target'], kind))
            elif r['target'] in alias:
                r['to'] = alias[r['target']]          # what tools/ledger.py resolves it to
                if alias[r['target']] != n['id']:
                    g.edges.append((n['id'], alias[r['target']], kind))
            else:
                g.edges.append((n['id'], f"?{r['target']}", 'dangling'))
        for c in n['cites']:
            g.edges.append((n['id'], f'cite:{c}', 'cites'))


def enrich(g, root='.'):
    """Numbers from the .aux; section signatures; `<<label>>` in titles resolved."""
    aux = parse_aux(os.path.join(root, AUX) if AUX else None)
    for n in g.nodes.values():
        if n['label'] and n['label'] in aux:
            n.update({'number': aux[n['label']]['number'],
                      'page': aux[n['label']]['page'],
                      'anchor': aux[n['label']]['anchor']})
    body_i, app_i = 0, 0
    for n in g.nodes.values():
        if n['kind'] == 'section' and n.get('level') == 1 and not n.get('starred'):
            if n['appendix']:
                n['signature'] = chr(ord('A') + app_i)
                app_i += 1
            else:
                body_i += 1
                n['signature'] = str(body_i)
            n.setdefault('number', n['signature'])
            if not n['number']:
                n['number'] = n['signature']
    for n in g.nodes.values():
        if '<<' in n['title']:
            n['title'] = re.sub(
                r'<<([^>]*)>>',
                lambda m: aux.get(m.group(1), {}).get('number') or m.group(1),
                n['title'])
    return aux


def to_json(g):
    return {'document': g.doc,
            'nodes': [{k: v for k, v in n.items() if not k.startswith('_')}
                      for n in g.nodes.values()],
            'edges': [{'source': a, 'target': b, 'kind': k} for a, b, k in g.edges]}
