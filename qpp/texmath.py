"""Q++ terms: the formula layer of a Q++ line (the data of a verb, a statement item, a claim).

One syntax tree, two parsers and two printers:

    LaTeX math  --parse_tex-->  tree  --to_qpp-->   Q++ ASCII  (the .qpp files)
    Q++ ASCII   --parse_qpp-->  tree  --to_lean-->  Lean 4 term

The LaTeX parser accepts a formal fragment only: numbers, variables (letters, Greek letters, bold vectors, primes,
subscripts), + - * / ^, juxtaposition, \\frac, |x|, ceilings and floors, sums and products, the relations, chains of
relations, membership in Q, Z, N and their positive parts, implications, and lists of such items. Anything else
(prose, an unknown macro, a set builder) raises Hole, and the caller keeps the LaTeX as a hole ?{...}.

Conventions of the fragment (qpp/README.md, "The LaTeX form", for this layer):
* a subscript of digits is part of a name (kappa_1); a subscript of letters is an index (a_i is a(i), M_{ij} is
  M(i, j)); a subscript + or - is part of a name (e_- is e_minus);
* a letter followed by ( is an application when it is a function letter (F G H P Q R S T f g h phi psi, or declared
  a function by the caller), else a product (k(s+1) is k*(s+1));
* \\sum and \\prod bind the multiplicative term after them (sum_i a_i + b is (sum_i a_i) + b);
* a chain a <= b < c is the conjunction of its links.
"""
import re

GREEK = {"alpha", "beta", "gamma", "delta", "epsilon", "varepsilon", "zeta", "eta", "theta", "vartheta", "iota",
         "kappa", "lambda", "mu", "nu", "xi", "pi", "rho", "varrho", "sigma", "varsigma", "tau", "upsilon", "phi", "varphi",
         "chi", "psi", "omega", "Gamma", "Delta", "Theta", "Lambda", "Xi", "Pi", "Sigma", "Phi", "Psi", "Omega"}
GREEK_LEAN = {"alpha": "\u03b1", "beta": "\u03b2", "gamma": "\u03b3", "delta": "\u03b4", "epsilon": "\u03b5", "varepsilon": "\u03b5", "zeta": "\u03b6",
              "eta": "\u03b7", "theta": "\u03b8", "vartheta": "\u03d1", "iota": "\u03b9", "kappa": "\u03ba", "lambda": "lam", "mu": "\u03bc",
              "nu": "\u03bd", "xi": "\u03be", "pi": "\u03c0", "rho": "\u03c1", "varrho": "\u03f1", "sigma": "\u03c3", "varsigma": "\u03c2", "tau": "\u03c4",
              "upsilon": "\u03c5", "phi": "\u03c6", "varphi": "\u03c6", "chi": "\u03c7", "psi": "\u03c8", "omega": "\u03c9", "Gamma": "\u0393",
              "Delta": "\u0394", "Theta": "\u0398", "Lambda": "\u039b", "Xi": "\u039e", "Pi": "Pi_", "Sigma": "Sigma_", "Phi": "\u03a6",
              "Psi": "\u03a8", "Omega": "\u03a9"}
FUNC_LETTERS = {"F", "G", "H", "P", "Q", "R", "S", "T", "f", "g", "h", "phi", "varphi", "psi"}
# the scope of the result being read (latex2qpp sets it), by keys (t, or t_ for the family t_a): the names that are
# numbers there (a_h\\in\\Q), which a parenthesis multiplies even when they are function letters of the term layer,
# and the names that are both a function and a number there or in the paper (a parenthesis after them is a hole)
SCALARS = set()
ELSEWHERE = set()
SCOPED = [False]  # a name that is neither a function nor a number before a parenthesis is a hole (else a product)
SETS = {"Q": "QQ", "Z": "ZZ", "N": "NN"}
REL_TEX = {"\\le": "<=", "\\leq": "<=", "\\ge": ">=", "\\geq": ">=", "<": "<", ">": ">", "=": "=", "\\ne": "!=",
           "\\neq": "!=", "\\subseteq": "subseteq", "\\subset": "subset", "\\notin": "notin",
           "\\supseteq": "supseteq", "\\supset": "supset", "\\mid": "divides", "\\nmid": "ndivides",
           "\\asymp": "asymp", "\\sim": "sim", "\\simeq": "simeq", "\\preceq": "preceq", "\\succeq": "succeq",
           "\\prec": "prec", "\\succ": "succ", "\\equiv": "equiv"}
# the relation symbols a paper defines by a row (x asymp y :<=> R): no meaning of their own, in Lean or on rows
DEFINED_RELS = {"asymp", "sim", "simeq", "preceq", "succeq", "prec", "succ", "equiv"}
SET_OPS = {"cap": "cap", "cup": "cup", "setminus": "minus"}
PRELUDE = {  # the words every paper may use (A states them; a paper adds its own with rows \text{w}:=S)
    "mass": {"set": ("set", "QQ>0"), "plural": "masses"},
    "integer": {"set": ("set", "ZZ"), "plural": "integers"},
    "finite": {"lean": "Set.Finite", "plural": "finite"},
}
REL_LEAN = {"<=": "\u2264", ">=": "\u2265", "<": "<", ">": ">", "=": "=", "!=": "\u2260", "subseteq": "\u2286",
            "subset": "\u2282", "notin": "\u2209", "supseteq": "\u2287", "supset": "\u2283", "divides": "\u2223",
            "ndivides": "\u2224"}
SKIP = {"textstyle", "displaystyle", "left", "right", "big", "Big", "bigg", "Bigg", "bigl", "bigr", "Bigl", "Bigr",
        "quad", "qquad", "nobreak", "allowbreak", "!", ",", ";", ":", ">", " "}
SUB_DIGITS = str.maketrans("0123456789", "\u2080\u2081\u2082\u2083\u2084\u2085\u2086\u2087\u2088\u2089")
FUNC_CMDS = {"lg", "log", "deg", "sgn", "det", "gcd", "lcm", "trop", "conv", "cont", "spn", "rank", "vol", "Res",
             "disc", "lc", "ord", "dim", "ker", "dist", "tr"}
BOLD_CMDS = {"bxi": "b_xi", "bd": "b_delta", "balpha": "b_alpha", "bbeta": "b_beta", "one": "b_one"}  # \one, the vector of ones; b_1 is b with index 1
# the bold Greek letters \btheta, \btau, ... (a paper's macros for \boldsymbol\theta); a b followed by a Greek name that
# is itself a Greek letter (\beta) is not one
BOLD_CMDS.update({"b" + g: "b_" + g for g in GREEK if "b" + g not in GREEK and "b" + g not in BOLD_CMDS})


QUANT_WORDS = {"for every": "forall", "for all": "forall", "for each": "forall", "for some": "exists"}

DATA_MODE = [False]  # True while the data of a proof word is read: a parenthesized relation is a citation


class Hole(Exception):
    """the LaTeX is outside the formal fragment"""


class PlusMinus(Hole):
    """a clause with \\pm or \\mp: it is read twice, with + and with - (the enclosing list of clauses does so);
    outside a statement it is a hole"""


# ---------------------------------------------------------------------------------------------------------
# LaTeX tokens

TEXT_CMDS = ("text", "textup", "textrm", "textnormal", "mbox")
GAPS = {" ", "quad", "qquad"}


def tex_tokens(s, gaps=None):
    """the tokens of a LaTeX formula; prose \\text{...} is one token ('text', content); if `gaps` is a list, it
    receives one flag per token: True when the token follows a visible space (\\ , \\quad), which ends a term
    before a parenthesized side condition or gloss"""
    out = []
    i, n = 0, len(s)
    while i < n:
        c = s[i]
        if c.isspace() or c == "~" or c == "&":
            i += 1
        elif c == "\\":
            m = re.compile(r"\\([A-Za-z]+)").match(s, i)
            if m and m.group(1) in TEXT_CMDS:
                j = m.end()
                while j < n and s[j].isspace():
                    j += 1
                if j < n and s[j] == "{":
                    depth, k = 0, j
                    while k < n:
                        if s[k] == "{" and s[k - 1] != "\\":
                            depth += 1
                        elif s[k] == "}" and s[k - 1] != "\\":
                            depth -= 1
                            if depth == 0:
                                break
                        k += 1
                    out.append(("text", re.sub(r"\s+", " ", s[j + 1:k]).strip()))
                    i = k + 1
                    continue
            if m:
                out.append(("cmd", m.group(1)))
                i = m.end()
            else:
                out.append(("cmd", s[i + 1:i + 2]))
                i += 2
        elif c.isdigit():
            m = re.compile(r"\d+(?:\.\d+)?").match(s, i)
            out.append(("num", m.group(0)))
            i = m.end()
        elif c.isalpha():
            out.append(("let", c))
            i += 1
        else:
            if s.startswith(":=", i):
                out.append(("sym", ":="))
                i += 2
                continue
            out.append(("sym", c))
            i += 1
    kept, gap = [], False
    for tok in out:
        if tok[0] == "cmd" and tok[1] in SKIP:
            gap = gap or tok[1] in GAPS
            continue
        kept.append(tok)
        if gaps is not None:
            gaps.append(gap)
        gap = False
    return kept


DOTS = (("cmd", "dots"), ("cmd", "ldots"), ("cmd", "cdots"))
# the marks of a name (a superscript that is no power): Y^+, f^*, a^0 (a label: a zeroth power is never written)
MARKS = {("sym", "+"): "_pos", ("sym", "-"): "_neg", ("sym", "*"): "_star", ("cmd", "ast"): "_star",
         ("cmd", "prime"): "'", ("num", "0"): "_nought", ("cmd", "circ"): "_circ"}


def mark_name(v, mark):
    """the name v with a mark: f_star, x_1star (a name with a digit subscript), a', Y_pos"""
    if mark == "'":
        return v + "'"
    prime = ""
    while v.endswith("'"):
        v, prime = v[:-1], prime + "'"
    if mark == "_star" and "_" in v:
        return v + "star" + prime
    return v + mark + prime


def generalize(a, b, i, pairs):
    """the template of the terms a and b: where they differ, the variable i (the pairs (a', b') that differ)"""
    if a == b:
        return a
    if isinstance(a, tuple) and isinstance(b, tuple) and len(a) == len(b) and a and b:
        if isinstance(a[0], str) and a[0] == b[0] and all(
                isinstance(x, tuple) == isinstance(y, tuple) and (isinstance(x, tuple) or x == y)
                for x, y in zip(a[1:], b[1:])):
            return (a[0],) + tuple(generalize(x, y, i, pairs) if isinstance(x, tuple) else x
                                   for x, y in zip(a[1:], b[1:]))
        if not isinstance(a[0], str) and not isinstance(b[0], str):
            return tuple(generalize(x, y, i, pairs) for x, y in zip(a, b))
    pairs.append((a, b))
    return ("var", i)


def indexed(x):
    """x with the names a_1 (a numeric subscript) read as the terms a_(1) of a family"""
    if isinstance(x, tuple) and x:
        if x[0] == "var":
            m = re.fullmatch(r"([A-Za-z]+)_(\d+)", x[1])
            return ("app", ("var", m.group(1)), (("num", m.group(2)),), "idx") if m else x
        return tuple(indexed(y) for y in x)
    return x


def fold(op, first, last):
    """first op \\dots op last as a big operator over i in lo..hi: first and last are one template at i = lo, hi"""
    used = set()

    def names(x):
        if isinstance(x, tuple) and x:
            if x[0] == "var":
                used.add(x[1])
            for y in x:
                names(y)
    names(first)
    names(last)
    i = next(v for v in ("i", "j", "l", "m", "r", "s") if v not in used)
    first, last = indexed(first), indexed(last)
    pairs = []
    body = generalize(first, last, i, pairs)
    if not pairs or any(pq != pairs[0] for pq in pairs):
        raise Hole("\\dots: the first and last terms differ in more than one index")
    lo, hi = pairs[0]
    return ("sum" if op == "+" else op, i, ("range", (lo, hi)), body)


REF_CMDS = (("cmd", "cref"), ("cmd", "eqref"), ("cmd", "Cref"))


def without_labels(inner):
    """the tokens with the label groups of the references taken out (\\cref{lem:x}(2) is \\cref (2))"""
    out, j = [], 0
    while j < len(inner):
        out.append(inner[j])
        if inner[j] in REF_CMDS and j + 1 < len(inner) and inner[j + 1] == ("sym", "{"):
            depth, j = 0, j + 1
            while j < len(inner):
                depth += {("sym", "{"): 1, ("sym", "}"): -1}.get(inner[j], 0)
                j += 1
                if depth == 0:
                    break
            continue
        j += 1
    return out


def shape(x):
    """the shape of a term in a list (a, b >= 0): a name, a term of one family or function, its absolute value"""
    if x[0] == "app":
        return ("app", x[1], x[3], len(x[2]))
    if x[0] in ("abs", "neg"):
        return (x[0], shape(x[1]))
    return ("name",) if is_name(x) else (x[0],)


def definable(x):
    """what a := may define: a name, a member of a family (a_(i)), a function at names (f(x), rho_(a, d)(x)), a
    tuple of names, an operator at names (a par b), a fold of one (par i in 1..N, a_(i)); not a value
    ((k - 3)/(5 + inf) := 0 is a convention, c * K := ... a misreading)"""
    k = x[0]
    if k == "var" or is_name(x):
        return True
    if k == "app" and x[3] == "idx":
        return definable(x[1]) and all(not has_claim(a) for a in x[2])
    if k == "app":
        return definable(x[1]) and all(a[0] == "var" or is_name(a) or a[0] == "tuple" and definable(a) for a in x[2])
    if k == "tuple":
        return all(definable(a) for a in x[1])
    if k == "bin":
        return x[1] not in ("+", "-", "*", "/") and definable(x[2]) and definable(x[3])
    return k in ("par",)


GLOSS_SYMS = (("sym", ","), ("sym", ";"), ("sym", "("), ("sym", ")"))


def is_gloss(inner):
    """the tokens of a parenthesis after a clause are a gloss: prose, references with their items, and the commas
    between them, with no formula outside \\text (a formula there is a hole, math_gloss)"""
    if not inner:
        return True
    if not (inner[0][0] == "text" or inner[0] in REF_CMDS):
        return False
    depth = 0
    for t in without_labels(inner):
        depth += {("sym", "("): 1, ("sym", ")"): -1}.get(t, 0)
        # a letter alone names a name ((\text{the same:}\ j\ \text{free})); numerals only as the item of a
        # reference, \cref{lem:x}(2), (U4)
        if not (t[0] in ("text", "let") or t in REF_CMDS or t in GLOSS_SYMS or (depth > 0 and t[0] == "num")):
            return False
    return True


def math_gloss(inner):
    """a parenthesis that opens as a gloss (prose or a reference) but carries a formula: (\\text{less}\\ \\Sigma_2),
    (\\cref{lem:x}(2):\\ s'\\ge s_0). The compiler drops a gloss, so a formula in it would be lost (a dropped
    hypothesis or case) or read as a side condition (a justification as a premise): a hole"""
    return bool(inner) and (inner[0][0] == "text" or inner[0] in REF_CMDS) and not is_gloss(inner)


def has_claim(x):
    """a relation as an operand inside a term: through the arithmetic (sums, products, powers, absolute values,
    tuples, arguments), not inside a set builder, a quantifier or a condition, which bind their own claims"""
    if not (isinstance(x, tuple) and x):
        return False
    if isinstance(x[0], str):
        if x[0] in ("rel", "cite"):
            return True
        if x[0] in ("bin", "neg", "pow", "abs", "tuple", "app", "interval", "ivl", "ceil", "floor", "norm"):
            return any(has_claim(y) for y in x[1:])
        if x[0] in ("sum", "prod", "par", "max", "min", "union", "inter", "oplus", "comp") and len(x) == 4:
            return has_claim(x[3])  # the body, not the range or the condition
        return False
    return any(has_claim(y) for y in x)


def is_coef(x):
    """a coefficient of a combination: a term without claims, not the number 0 (2, 1/2, \\kappa_1^{-1});
    0\\ (j<k) is a side condition"""
    if x[0] == "num":
        return x[1].strip("0.") != ""
    return not has_claim(x)


def combination_ok(x):
    """claims in a term only in the data of a word, as a combination with coefficients, (x\\le1)+\\kappa(y\\le1)
    (a certificate); 0\\ (j<k), [a,b]\\ (s=1), f((x\\le1)), and any claim in a term elsewhere are not"""
    if not has_claim(x) or x[0] in ("rel", "cite"):
        return True
    if not DATA_MODE[0]:
        return False  # outside the data of a word a claim in a term is a side condition: 2x\ (x\ge-t), t\ (k=3)
    if x[0] == "bin" and x[1] in "+-":
        return combination_ok(x[2]) and combination_ok(x[3])
    if x[0] == "neg":
        return combination_ok(x[1])
    if x[0] == "bin" and x[1] == "*":
        return (is_coef(x[2]) and x[3][0] in ("rel", "cite")) or (is_coef(x[3]) and x[2][0] in ("rel", "cite"))
    return False


def sign_of_side(p, m):
    """p and m, the readings of one side with + and with -, differ only by signs of the side itself: a sign at a
    term of its sums, x=\\pm y+1, x=1\\pm y, at a factor of its products and quotients, R=\\pm a^kb^l (a sign of a
    factor is a sign of the product), or at a component of a tuple, (a_0,b_0)=(\\pm x^2,0). A sign inside an
    argument, a subscript, an exponent or absolute value bars, f(\\pm x), u_\\pm, 2^{\\pm e}, |x\\pm y|, is not a
    sign of the side (syntax)"""
    if p == m or m == ("neg", p) or p == ("neg", m):
        return True
    if p[0] != m[0] or len(p) != len(m):
        return False
    if p[0] == "neg":
        return sign_of_side(p[1], m[1])
    if p[0] == "bin" and (p[1] == m[1] in ("*", "/") or {p[1], m[1]} <= {"+", "-"}):
        return sign_of_side(p[2], m[2]) and sign_of_side(p[3], m[3])
    if p[0] == "tuple" and len(p[1]) == len(m[1]):
        return all(sign_of_side(x, y) for x, y in zip(p[1], m[1]))
    return False


class TexParser:
    def __init__(self, s, functions=(), vocab=None):
        self.g = []
        self.t = tex_tokens(s, self.g)
        self.k = 0
        self.functions = set(FUNC_LETTERS) | set(functions)
        self.vocab = VOCAB if vocab is None else vocab
        self.bars = 0
        self.glosses = []
        self.sign = None  # "+" or "-" while a clause with \pm is read for that sign
        self.pm_local = True  # False: a clause with \pm raises PlusMinus to the enclosing clause

    def pm(self, cmd):
        """the sign that \\pm (or \\mp) stands for in the current reading of the clause"""
        if self.sign is None:
            raise PlusMinus()
        return self.sign if cmd == "pm" else ("-" if self.sign == "+" else "+")

    # helpers
    def peek(self, d=0):
        j = self.k + d
        return self.t[j] if j < len(self.t) else (None, None)

    def eat(self, kind=None, val=None):
        t = self.peek()
        if (kind and t[0] != kind) or (val is not None and t[1] != val):
            raise Hole(f"expected {kind} {val}, got {t}")
        self.k += 1
        return t

    def at(self, kind, val=None):
        t = self.peek()
        return t[0] == kind and (val is None or t[1] == val)

    def group(self):
        """{...} or a single token, as a sub-parser over its tokens"""
        if self.at("sym", "{"):
            depth, j = 0, self.k
            while j < len(self.t):
                if self.t[j] == ("sym", "{"):
                    depth += 1
                elif self.t[j] == ("sym", "}"):
                    depth -= 1
                    if depth == 0:
                        break
                j += 1
            if j >= len(self.t):
                raise Hole("unbalanced {")
            inner = self.t[self.k + 1:j]
            self.k = j + 1
            return inner
        t = self.peek()
        if t[0] is None:
            raise Hole("missing group")
        if t[0] == "num" and len(t[1]) > 1 and "." not in t[1]:
            # c_12^k is c_1 2^k: an unbraced sub- or superscript takes one character
            self.t[self.k] = ("num", t[1][1:])
            return [("num", t[1][0])]
        self.k += 1
        return [t]

    def sub(self, toks):
        p = TexParser("", self.functions, self.vocab)
        p.t = list(toks)
        p.g = [False] * len(p.t)
        p.bars = 0
        p.glosses = self.glosses
        p.sign = self.sign
        return p

    def gap(self):
        """the next token follows a visible space"""
        return self.k < len(self.g) and self.g[self.k]

    def done(self):
        return self.k >= len(self.t)

    # syntax
    def items(self):
        """a list of items separated by top-level commas or semicolons"""
        out = [self.prop()]
        while self.at("sym", ",") or self.at("sym", ";"):
            self.k += 1
            if self.done():
                break
            out.append(self.prop())
        if not self.done():
            raise Hole(f"trailing {self.t[self.k:self.k + 3]}")
        return out

    def whole(self):
        x = self.prop()
        if not self.done():
            raise Hole(f"trailing {self.t[self.k:self.k + 3]}")
        return x

    def prop(self, arrows=True):
        if self.at("cmd", "exists") or self.at("cmd", "forall") or self.quant_word():
            t = self.eat()
            q = t[1] if t[0] == "cmd" else QUANT_WORDS[t[1]]
            groups = []
            while True:
                vs = [self.atom()]
                while self.at("sym", ",") and not (self.k + 1 < len(self.g) and self.g[self.k + 1]):
                    # x,y\in S: one group; a visible space after the comma starts the next group
                    # (\forall\bx,s,\ V\in\mathrm{Pat}(\bx); \exists O_*\subseteq O,\ c,C\ \forall ...)
                    self.k += 1
                    vs.append(self.atom())
                dom = None
                bound = None
                if self.at("cmd", "in"):
                    self.k += 1
                    dom = self.setexpr()
                elif len(vs) == 1 and self.at_relation():
                    # a binder with a condition on it: \forall i\le n, \exists Z\subseteq O, \exists O_*=t\subseteq O
                    # (forall i : i <= n => ..., exists Z : Z subseteq O, ...); \exists Z=Z_{M,L}\subseteq O names the
                    # witness Z_{M,L} (the equation with a member of the family Z is its name, not a condition)
                    ops, terms = [], [vs[0]]
                    while self.at_relation():
                        t = self.eat()
                        op = "in" if t == ("cmd", "in") else REL_TEX[("\\" + t[1]) if t[0] == "cmd" else t[1]]
                        ops.append(op)
                        terms.append(self.setexpr() if op in ("in", "subseteq", "subset") else self.expr())
                    if ops[0] == "=" and is_name(terms[1]) and terms[1][0] == "app" and terms[1][1] == vs[0]:
                        ops, terms = ops[1:], terms[:1] + terms[2:]
                    if ops:
                        bound = ("rel", tuple(ops), tuple(terms))
                if bound is not None and groups and groups[-1][0] == tuple(vs) and groups[-1][2] is None:
                    groups[-1] = (groups[-1][0], groups[-1][1], bound)  # \forall i\in\Z,\ i\le n:
                else:
                    groups.append((tuple(vs), dom, bound))
                if self.at("sym", ",") and (dom is not None or bound is not None or (
                        self.k + 1 < len(self.g) and self.g[self.k + 1])):
                    # the next group: \forall M\in\Z,\ L\ge1;  \exists O_*\subseteq O,\ c,C\ \forall ...
                    self.k += 1
                    continue
                break
            if self.at("sym", ":"):
                self.k += 1
            body = self.part() if self.stmt_mode else self.prop()
            for vs, dom, bound in reversed(groups):
                if bound is not None:
                    body = ("imp", bound, body) if q == "forall" else ("and", (bound, body))
                body = (q, vs, dom, body)
            return body
        if self.at("cmd", "neg") or self.at("cmd", "lnot"):
            # \neg(P): the negation of a proposition (the else case of a condition prints so)
            self.k += 1
            if not self.at("sym", "("):
                raise Hole("a negation without parentheses")
            sp = self.sub(self.paren_tokens())
            sp.stmt_mode = True
            x = sp.part()
            if not sp.done():
                raise Hole("negation")
            return ("not", x)
        left = self.rel()
        if self.at("sym", ":") and self.peek(1) in (("cmd", "iff"), ("cmd", "Leftrightarrow")):
            # a defined relation: L :<=> R (a vocabulary row)
            self.k += 2
            return ("defrel", left, self.part() if self.stmt_mode else self.prop())
        if arrows and (self.at("cmd", "Rightarrow") or self.at("cmd", "implies")):
            self.k += 1
            return ("imp", left, self.prop())
        if arrows and (self.at("cmd", "iff") or self.at("cmd", "Leftrightarrow")):
            # in a clause (arrows=False) the equivalence is the part's: its sides take their postfixes and words
            self.k += 1
            return ("iff", left, self.prop())
        return left

    # statements (conventions v1): item := part (; part)*, part := clauses [(: | =>) part]

    stmt_mode = False

    def stmt(self):
        self.stmt_mode = True
        parts = self.sign_part()
        while self.at("sym", ";"):
            self.k += 1
            if self.done():
                break
            parts += self.sign_part()
        if not self.done():
            raise Hole(f"trailing {self.t[self.k:self.k + 3]}")
        for x in parts:
            bad = prop_term(x)
            if bad is not None:
                raise Hole(f"a term where a clause is expected: {to_qpp(bad)}")
        return parts

    def sign_part(self):
        """a part; a part whose context has \\pm (or \\mp) is two parts, the whole part read with + and with -
        (0<\\pm\\delta\\le s:\\ K=\\kappa_\\pm|\\delta| is the case delta > 0 and the case delta < 0, each with its own
        conclusion: one sign for the whole part, not both signs in the context)"""
        depth, j, sign = 0, self.k, False
        while j < len(self.t):
            tok = self.t[j]
            if tok in (("sym", "("), ("sym", "["), ("sym", "{"), ("cmd", "{")):
                depth += 1
            elif tok in (("sym", ")"), ("sym", "]"), ("sym", "}"), ("cmd", "}")):
                depth -= 1
            elif depth == 0 and (tok == ("sym", ";") or tok in (("sym", ":"), ("cmd", "Rightarrow"), ("cmd", "implies"))):
                break
            elif tok in (("cmd", "pm"), ("cmd", "mp")):
                # the sign of a term (0<\pm\delta, x=\pm y), not a label below or above a name (c_\pm, I_\pm: both)
                before = self.t[j - 1] if j > 0 else None
                label = before in (("sym", "_"), ("sym", "^")) or (
                    before == ("sym", "{") and j > 1 and self.t[j - 2] in (("sym", "_"), ("sym", "^")))
                sign = sign or not label
            j += 1
        if not sign or j >= len(self.t) or self.t[j] == ("sym", ";") or self.sign is not None:
            return [self.part()]
        save, out = self.k, []
        for sgn in ("+", "-"):
            self.k, self.sign = save, sgn
            try:
                out.append(self.part())
            finally:
                self.sign = None
        return out

    def part(self):
        if self.at_word("if"):
            # \text{if}\ H,\ \text{then}\ C: the implication H => C (the prefix form of the postfix C\ \text{if}\ H)
            self.k += 1
            hyp = self.clauses()
            if not self.at_word("then"):
                raise Hole("\\text{if} at the start of a part without \\text{then}")
            self.k += 1
            return ("imp", conj(hyp), self.part())
        xs = self.clauses()
        if self.at("sym", ":") and self.peek(1) in (("cmd", "iff"), ("cmd", "Leftrightarrow")):
            # a defined relational word: x w y :<=> R (a vocabulary row)
            self.k += 2
            return ("defrel", conj(xs), self.part())
        if self.at("sym", ":") and not self.done():
            self.k += 1
            return ("ctx", conj(xs), self.part())
        if self.at("cmd", "Rightarrow") or self.at("cmd", "implies"):
            self.k += 1
            return ("imp", conj(xs), self.part())
        if self.at("cmd", "iff") or self.at("cmd", "Leftrightarrow"):
            # an equivalence of two parts (a claim, not a definition: a definition is :\iff)
            self.k += 1
            return ("iff", conj(xs), self.part())
        return conj(xs)

    def clauses(self):
        """clause (, clause)*: bare names before a declaration are declared with it (x,y\\in S, a,b masses). A list of
        terms of one shape (names, terms of one family or function, their absolute values) is read with the relation
        next to it: before it, the relation for each (|S(a)|,|S(b)|\\ge2\\varepsilon, x,y\\ge0); after it, the
        relation with each as its last operand (M\\ge|U|,|V|), and x=a,b is x in {a, b}. When both readings fit, or
        none (\\mathrm{Band}(Q,c,a,\\varepsilon),1\\le a; (D_u),\\kappa_u=m_0), the list is a hole"""
        out, pending, after = [], [], False

        def fits_left(c):
            return (c[0] == "rel" and not (c[1] == ("in",) and is_name(c[2][0]))
                    and all(shape(y) == shape(c[2][0]) for y in pending))

        def fits_right():
            r = out[-1] if after and out and out[-1][0] == "rel" else None
            return r is not None and r[1][-1] != "in" and all(shape(y) == shape(r[2][-1]) for y in pending)

        def flush_right():
            nonlocal pending
            r = out[-1]
            if r[1] == ("=",):
                out[-1] = ("rel", ("in",), (r[2][0], ("setlist", (r[2][1],) + tuple(pending))))
            else:
                out.extend(("rel", r[1], r[2][:-1] + (y,)) for y in pending)
            pending = []

        def unread():
            if all(is_name(y) for y in pending):
                return Hole("a list of names without a declaration")
            return Hole("a list of terms without a relation that fits them")

        while True:
            for c in self.sign_clause():
                if is_name(c) or (c[0] != "nounpost" and prop_term(c) is c):
                    if not pending:
                        after = bool(out) and out[-1][0] == "rel"
                    pending.append(c)
                    continue
                names = all(is_name(y) for y in pending)
                if c[0] == "rel" and c[1] == ("in",) and is_name(c[2][0]) and names:
                    out.append(("decl", tuple(pending + [c[2][0]]), c[2][1]))
                    pending = []
                elif c[0] == "decl" and c[2][0] == "fun" and names:
                    out.append(("decl", tuple(pending) + c[1], c[2]))
                    pending = []
                elif c[0] == "nounpost" and pending and not names:
                    # terms of one shape before a noun: each is in the word ([a,b],[c,d] boxes)
                    if names_of(c[1]) or any(shape(y) != shape(c[1]) for y in pending):
                        raise unread()
                    out += [("rel", ("in",), (y, ("word", w))) for y in pending + [c[1]] for w in c[2]]
                    pending = []
                elif c[0] == "nounpost":
                    x, ws = c[1], c[2]
                    names = tuple(pending + names_of(x))
                    pending = []
                    if not names:
                        # a noun after a term that declares nothing: the term is in the word ([a,b] a box)
                        out += [("rel", ("in",), (x, ("word", w))) for w in ws]
                    else:
                        out += [("decl", names, ("word", w)) for w in ws]
                        if x[0] != "var" and not is_name(x):
                            out.append(x)
                elif pending:
                    left, right = fits_left(c), fits_right()
                    if left and right:
                        raise Hole("a list between two relations that both fit it")
                    if left:
                        out += [("rel", c[1], (y,) + c[2][1:]) for y in pending] + [c]
                        pending = []
                    elif right:
                        flush_right()
                        out.append(c)
                    else:
                        raise unread()
                else:
                    out.append(c)
            if self.at("sym", ",") or self.at_word("and") or self.at_word("with") or self.at_word("so"):
                # \text{so} is "and so": a conjunction, both claims kept (an arrow would drop the first)
                self.k += 1
                if self.done() or self.at("sym", ";") or self.at_word("then"):
                    break  # \text{if}\ H,\ \text{then}\ C: the clauses of H end at then (part)
                continue
            break
        if pending:
            if not fits_right():
                raise unread()
            flush_right()
        return else_cases(out)

    def sign_clause(self):
        """the next clause; a clause with \\pm or \\mp is two clauses, read with + and with - (I_\\pm\\ne\\varnothing is
        I_+\\ne\\varnothing, I_-\\ne\\varnothing; \\mp is the opposite sign); an equation with the sign on one side only is
        one of the two (x=\\pm y is x = y or x = -y); \\{\\pm c\\} is the set {c, -c} (normalize)"""
        save, glosses = self.k, len(self.glosses)
        try:
            return [self.clause()]
        except PlusMinus:
            if self.sign is not None or not self.pm_local:
                raise
        out = []
        for sgn in ("+", "-"):
            self.k, self.sign = save, sgn
            del self.glosses[glosses:]
            try:
                out.append(self.clause())
            finally:
                self.sign = None
        a, b = out
        ia, ib, wrap = a, b, []
        while ia[0] == ib[0] and ((ia[0] == "forall" and ia[1:3] == ib[1:3]) or (ia[0] == "imp" and ia[1] == ib[1])):
            wrap.append(ia)
            ia, ib = (ia[3], ib[3]) if ia[0] == "forall" else (ia[2], ib[2])
        if wrap and ia[0] == ib[0] == "rel" and ia[1] == ib[1] == ("=",) and ia[2][0] == ib[2][0] \
                and sign_of_side(ia[2][1], ib[2][1]) and ia[2][1] != ib[2][1]:
            # \epsilon_{R,f}=\pm1\ (f\in\mathcal J): for each member one of the two values, in {1, -1}
            x = link("in", ia[2][0], ("setlist", (ia[2][1], ib[2][1])))
            for w in reversed(wrap):
                x = (w[0], w[1], w[2], x) if w[0] == "forall" else ("imp", w[1], x)
            return [x]
        if a[0] == b[0] == "rel" and a[1] == b[1] and set(a[1]) == {"="}:
            diff = [i for i, (u, v) in enumerate(zip(a[2], b[2])) if u != v]
            if len(diff) == 1 and sign_of_side(a[2][diff[0]], b[2][diff[0]]):
                # x = \pm y, N_0 = N_1 = \mp e: the sign of one side only, one of the two values (x = y or x = -y),
                # not both (both would force y = 0). A sign on two sides, (a\pm b)^2 = a^2\pm2ab+b^2, or nested in
                # a side, f(\pm x) = f(x), is read twice
                return [("or", a, b)]
        return out

    def at_word(self, w):
        return self.at("text", w)

    def quant_word(self):
        """\\text{for every} (for all, for each) and \\text{for some} before a binder: the quantifiers in words"""
        t = self.peek()
        return t[0] == "text" and t[1] in QUANT_WORDS

    def at_relation(self):
        """a relation symbol at the cursor (an order, =, a set inclusion, \\in)"""
        t = self.peek()
        if t == ("cmd", "in"):
            return True
        key = ("\\" + t[1]) if t[0] == "cmd" else t[1]
        return key in REL_TEX and not (t[0] == "sym" and t[1] not in "<>=") and REL_TEX[key] not in DEFINED_RELS

    def words(self, text):
        """the vocabulary words of a prose token (a noun or adjectives), or None"""
        ws = []
        for piece in re.split(r",\s*|\s+and\s+", text.strip()):
            w = vocab_word(piece, self.vocab)
            if w is None:
                return None
            ws.append(w)
        return ws or None

    def paren_tokens(self):
        """the tokens inside the parentheses at the cursor (balanced), the cursor after them"""
        depth, j = 0, self.k
        while j < len(self.t):
            if self.t[j] == ("sym", "("):
                depth += 1
            elif self.t[j] == ("sym", ")"):
                depth -= 1
                if depth == 0:
                    break
            j += 1
        if j >= len(self.t):
            raise Hole("unbalanced (")
        inner = self.t[self.k + 1:j]
        self.k = j + 1
        return inner

    PAREN_CLAUSES = ("and", "imp", "ctx", "rel", "exists", "forall", "decl", "or", "on", "iff", "textrel", "at", "near",
                     "attained", "uniform")

    def paren_clause(self):
        """a parenthesized clause at the cursor, (a, b), (\\forall x: P) or (H \\Rightarrow C), read as a part; else None
        and the cursor kept (a parenthesized term)"""
        if not self.at("sym", "("):
            return None
        save = self.k
        sp = self.sub(self.paren_tokens())
        sp.stmt_mode = True
        sp.pm_local = False
        try:
            y = sp.part()
            if sp.done() and y[0] in self.PAREN_CLAUSES:
                return y
        except PlusMinus:
            raise
        except Hole:
            pass
        self.k = save
        return None

    def clause(self):
        while self.at_word("so"):
            self.k += 1
        if self.at_word("attained"):
            # m:=\min S,\ \text{attained}: the clause before is the least of a set, attained
            self.k += 1
            return ("postword", "attained")
        if self.at_word("constants free of") or self.at_word("uniformly in"):
            # X\asymp Y\ \text{on}\ O,\ \text{constants free of}\ \ba,\bd: the constants of the clause before do not
            # depend on these names
            self.k += 1
            ns = [self.atom()]
            while self.at("sym", ",") and not (self.k + 1 < len(self.g) and self.g[self.k + 1]):
                self.k += 1
                ns.append(self.atom())
            if not all(is_name(n) for n in ns):
                raise Hole("constants free of terms that are not names")
            return ("postword", "uniform", tuple(ns))
        if self.at_word("if"):
            return self.part()  # x\in\Q,\ \text{if}\ x>0,\ \text{then}\ C: the implication takes the rest of the part
        x = None
        if self.at("sym", "("):
            # a parenthesized list or implication at the start of a clause: (a, b) or (H => C)
            save = self.k
            sp = self.sub(self.paren_tokens())
            sp.stmt_mode = True
            sp.pm_local = False  # a sign inside the parenthesis is read by this clause: (a\pm b)^2=a^2\pm2ab+b^2
            try:
                y = sp.part()
                if sp.done() and (y[0] in ("and", "imp", "ctx", "rel", "exists", "forall", "decl", "or", "on", "iff",
                                           "textrel", "at", "near", "attained", "uniform")):
                    x = y
            except PlusMinus:
                raise
            except Hole:
                pass
            if x is None:
                self.k = save
        if x is None:
            x = self.prop(arrows=False)
        if is_name(x) and (self.at("sym", ":") or self.at("cmd", "colon")):
            # a function declaration F:S\to T (not the context colon)
            save = self.k
            self.k += 1
            try:
                dom = self.setexpr()
                if self.at("cmd", "to"):
                    self.k += 1
                    x = ("decl", (x,), ("fun", dom, self.setexpr()))
                    while self.at("sym", "(") and self.gap():
                        # a gloss after the declaration: e:\Q_{>0}\to\Z\ (\text{the exponent})
                        save2 = self.k
                        inner = self.paren_tokens()
                        if not is_gloss(inner):
                            self.k = save2
                            break
                        self.glosses.append(inner)
                    save = None  # declared: its postfixes follow (g_l:\Q\to\Q\ \text{for}\ l\le L)
            except PlusMinus:
                raise
            except Hole:
                pass
            if save is not None:
                self.k = save
        while True:
            tok = self.peek()
            if tok[0] == "text":
                w = tok[1]
                head, _, rest = w.partition(" ")
                if w in QUANT_WORDS:
                    # P \text{for every} x\in S (for all, for each): forall; P \text{for some} x\in S: exists
                    self.k += 1
                    x = self.for_binder(x, QUANT_WORDS[w])
                    continue
                if w in ("else", "otherwise"):
                    # x:=t\ \text{otherwise}: the case that the condition of the clause before does not hold
                    self.k += 1
                    x = ("else", x)
                    continue
                if w in ("then",):
                    return x
                if head in ("if", "for", "on", "or") and (rest or head == w):
                    self.k += 1
                    if rest:
                        ws = self.words(rest)
                        if ws is None or len(ws) != 1:
                            raise Hole(f"prose: {w}")
                        arg = ("word", ws[0])
                        if head == "on":
                            x = ("on", arg, x)
                            continue
                        raise Hole(f"prose: {w}")
                    if head == "if":
                        x = ("imp", self.prop(arrows=False), x)
                    elif head == "for":
                        x = self.for_binder(x)
                    elif head == "on":
                        x = ("on", self.setexpr(), x)
                    else:
                        y = self.paren_clause()
                        x = ("or", x, y if y is not None else self.prop(arrows=False))
                    continue
                if w in ("and", "with", "so"):
                    # so: "and so", a conjunction (both are claimed; an arrow would drop the first)
                    return x
                r = self.textrel(x)
                if r is not None:
                    x = r
                    continue
                if w in ("at", "near"):
                    # P \text{at} p: P with its functions at the point p; P \text{near} p: on a box with p in its
                    # interior. A relation with no function to take at p ((\lambda,m)=(\ldots)\ \text{at}\ \bw_0, the
                    # coefficient of K at a point) is no such clause
                    if x[0] not in ("ref", "refat") and not any(
                            y[0] == "var" and (y[1] in self.functions or name_key(y, self.vocab) in self.functions)
                            and y[1] not in SCALARS for y in subterms(x)):
                        raise Hole("the coefficient at a point: bound by a binding, none yet")
                    self.k += 1
                    x = (w, self.expr(), x)
                    continue
                if w == "within" and not is_prop(x):
                    # a \text{within} W \text{of} b: |a - b| <= W
                    self.k += 1
                    width = self.expr()
                    if not self.at_word("of"):
                        raise Hole("\\text{within} without \\text{of}")
                    self.k += 1
                    x = ("rel", ("<=",), (("abs", ("bin", "-", x, self.expr())), width))
                    continue
                if w == "where":
                    # X \text{where} P: X on the set {P}
                    self.k += 1
                    x = ("on", ("setof", self.prop(arrows=False)), x)
                    continue
                ws = self.words(w)
                if ws is not None:
                    self.k += 1
                    return ("nounpost", x, ws)
                raise Hole(f"prose: {w}")
            if tok == ("sym", "(") and self.gap():
                inner = self.paren_tokens()
                if inner in ([("text", "else")], [("text", "otherwise")]):
                    x = ("else", x)  # e_i:=t\ (h_i=0),\ \sigma_i:=u\ (\text{else})
                    continue
                if is_gloss(inner):
                    self.glosses.append(inner)
                    continue
                if math_gloss(inner):
                    raise Hole("a gloss with a formula: write the formula as a hypothesis or a claim, or the gloss "
                               "in words (a gloss is dropped)")
                sp = self.sub(inner)
                sp.stmt_mode = True
                c = sp.part()
                if not sp.done():
                    raise Hole("side condition")
                if x[0] == "rel" and x[1] == ("in",) and is_name(x[2][0]):
                    x = ("decl", (x[2][0],), x[2][1])  # x\in S\ (H): as H => x\in S reads (a declaration)
                if c[0] == "decl":
                    x = ("forall", c[1], c[2], x)
                else:
                    x = ("imp", c, x)
                continue
            return x

    def textrel(self, x):
        """x w1 y1 w2 y2 ... for a relational word of the vocabulary (pattern _ w1 _ w2 _ ...), or None"""
        pats = sorted((p for p in (self.vocab or {}).get("#textrel", []) if p[1] == rel_word(self.peek()[1])),
                      key=len, reverse=True)
        for pat in pats:
            save = self.k
            self.k += 1
            args = [x]
            try:
                for slot in pat[2:]:
                    if slot == "_":
                        args.append(self.expr())
                    elif self.peek()[0] == "text" and rel_word(self.peek()[1]) == slot:
                        self.k += 1
                    else:
                        raise Hole("pattern")
                return ("textrel", tuple(w for w in pat if w != "_"), tuple(args))
            except PlusMinus:
                raise
            except Hole:
                self.k = save
        return None

    def for_binder(self, x, q="forall"):
        """C \\text{for} x,y\\in S  or  C \\text{for} i\\le N (the first name of the chain is bound); with q = exists,
        C \\text{for some} x\\in S: some x of S with C"""
        if x[0] == "rel" and x[1] == ("in",) and is_name(x[2][0]):
            x = ("decl", (x[2][0],), x[2][1])  # k_R\in\Z\ \text{for}\ R\in\Pi: as \forall R\in\Pi:\ k_R\in\Z reads

        def body(cond):
            if cond is None:
                return x
            return ("imp", cond, x) if q == "forall" else ("and", (cond, x))
        names = []
        while True:
            r = self.prop(arrows=False)
            if is_name(r) and self.at("sym", ","):
                names.append(r)
                self.k += 1
                continue
            break
        if r[0] == "rel" and r[1] == ("in",) and is_name(r[2][0]):
            if self.at_word("with"):
                self.k += 1
                return (q, tuple(names + [r[2][0]]), r[2][1], body(self.prop(arrows=False)))
            return (q, tuple(names + [r[2][0]]), r[2][1], x)
        if names:
            raise Hole("for: names without a set")
        if r[0] == "rel":
            vs = [a for a in r[2] if a[0] == "var"]
            if not vs:
                raise Hole("for: no variable")
            return (q, (vs[0],), None, body(r))
        raise Hole("for")

    def rel(self):
        first = self.expr()
        if self.at("sym", ":="):
            self.k += 1
            rhs = self.expr()
            if has_claim(rhs):
                raise Hole("a claim in parentheses inside a definition")  # \xi_h:=1\ (h\ge3): a side condition
            if not definable(first):
                raise Hole(f"a definition of {to_qpp(first)}, which is not a name (a convention needs a row)")
            return ("def", first, rhs)
        ops, terms = [], [first]
        while True:
            t = self.peek()
            key = ("\\" + t[1]) if t[0] == "cmd" else t[1]
            if key == "=" and not ops and self.peek(1) in (("cmd", "pm"), ("cmd", "mp")) and (
                    self.peek(2)[0] in (None, "text") or self.peek(2) in (("sym", ","), ("sym", ";"), ("sym", ")"),
                                                                       ("sym", ":")) or (self.k + 2 < len(self.g) and self.g[self.k + 2])):
                # \sigma_i=\pm: a sign, sigma_i in {1, -1}
                self.k += 2
                return ("rel", ("in",), (first, ("setlist", (("num", "1"), ("neg", ("num", "1"))))))
            if key in REL_TEX and not (t[0] == "sym" and t[1] not in "<>="):
                self.k += 1
                op = REL_TEX[key]
                if self.peek() in DOTS:
                    # W_0<\dots<W_{m+1}, e_2=\dots=e_{k+1}: a chain over a range of indices
                    self.k += 1
                    if self.eat() != t:
                        raise Hole("\\dots between two different relations")
                    op = ("dots", op)
                ops.append(op)
                terms.append(self.setexpr() if op in ("subseteq", "subset") else self.expr())
            elif t[0] == "cmd" and t[1] == "in":
                self.k += 1
                ops.append("in")
                terms.append(self.setexpr())
            else:
                break
        if not ops:
            if not combination_ok(first):
                raise Hole("a claim in parentheses outside a combination of claims")
            return first
        if any(has_claim(t) for t in terms):
            # b_k>0\ (k\ge1): a side condition after a term, not a factor of it
            raise Hole("a claim in parentheses inside a relation")
        if any(isinstance(o, tuple) for o in ops):
            return dots_chain(ops, terms)
        r = ("rel", tuple(ops), tuple(terms))
        if self.at("cmd", "forall"):
            # a postfix quantifier: P  \forall k
            self.k += 1
            vs = [self.atom()]
            while self.at("sym", ","):
                self.k += 1
                vs.append(self.atom())
            return ("forall", tuple(vs), None, r)
        return r

    def setexpr(self):
        """a set after \\in: Q, Z, N and their parts, powers and polynomial rings; an interval; else a term (a set
        builder, a name); then its intersections, unions and differences"""
        x = self.set_atom()
        while self.peek()[0] == "cmd" and self.peek()[1] in SET_OPS:
            op = SET_OPS[self.eat()[1]]
            x = ("bin", op, x, self.set_atom())
        return x

    def set_atom(self):
        t = self.peek()
        if t[0] == "cmd" and t[1] in SETS:
            self.k += 1
            name = SETS[t[1]]
            sup = None
            if self.at("sym", "^") and self.peek(1) == ("cmd", "times"):
                # \Q^\times: the nonzero elements
                self.k += 2
                return ("units", ("set", name))
            if self.at("sym", "^"):
                self.k += 1
                sup = self.sub(self.group()).whole()
            bound = None
            if self.at("sym", "_"):
                self.k += 1
                g = self.sub(self.group())
                op = g.eat()
                key = ("\\" + op[1]) if op[0] == "cmd" else op[1]
                if key not in ("\\ge", "\\geq", ">"):
                    raise Hole("set subscript")
                if g.at("num") and g.k == len(g.t) - 1:
                    name += (">=" if key != ">" else ">") + g.eat("num")[1]
                else:
                    # \Z_{\ge M_0}: the members of Z from a bound that is a term
                    bound = (">=" if key != ">" else ">", g.whole())
            x = ("set", name) if bound is None else ("setfrom", name, bound[0], bound[1])
            if sup is not None:
                return ("pow", x, sup)
            while self.at("sym", "["):
                # a polynomial ring Q[x, y] (or Q[w][y])
                self.k += 1
                vs = [self.expr()]
                while self.at("sym", ","):
                    self.k += 1
                    vs.append(self.expr())
                self.eat("sym", "]")
                x = ("polyring", x, tuple(vs))
            if self.at("sym", "^"):
                self.k += 1
                x = ("pow", x, self.sub(self.group()).whole())
            return x
        if t[0] == "sym" and t[1] == "[":
            # a closed interval [a, b], possibly scaled: [a, b] u; or the half-open [a, b)
            self.k += 1
            a = self.expr()
            self.eat("sym", ",")
            b = self.expr()
            if self.at("sym", ")"):
                self.k += 1
                x = ("ivl", "co", a, b)
            else:
                self.eat("sym", "]")
                x = ("interval", a, b, None)
                if self.starts_atom():
                    return ("interval", a, b, self.term())
            if self.at("sym", "^"):
                self.k += 1
                return ("pow", x, self.sub(self.group()).whole())
            return x
        x = self.expr()
        if self.peek()[0] == "cmd" and self.peek()[1] in SETS:
            # \tfrac1N\Z: a scaled lattice, the multiples of 1/N
            x = ("bin", "*", x, self.set_atom())
        return x

    def expr(self):
        if self.at("sym", "-"):
            self.k += 1
            x = ("neg", self.term())
        elif self.at("cmd", "pm") or self.at("cmd", "mp"):
            x = self.term() if self.pm(self.eat()[1]) == "+" else ("neg", self.term())
        else:
            x = self.term()
        while (self.at("sym", "+") or self.at("sym", "-") or self.at("cmd", "pm") or self.at("cmd", "mp")
               or self.at("cmd", "parallel") or (self.peek()[0] == "cmd" and self.peek()[1] in SET_OPS)):
            t = self.eat()
            if t[1] in ("pm", "mp"):
                t = ("sym", self.pm(t[1]))
            if t[1] in SET_OPS:
                x = ("bin", SET_OPS[t[1]], x, self.term())
                continue
            op = "par" if t[1] == "parallel" else t[1]
            if self.peek() in DOTS:
                # t_1 op \dots op t_N: the fold of op over the terms between (a sum, a parallel sum)
                self.k += 1
                if self.eat() != t or op not in ("+", "par"):
                    raise Hole("\\dots between two operators that are not one + or one \\parallel")
                last = self.term()
                if x[0] == "bin" and x[1] == op:
                    x = ("bin", op, x[2], fold(op, x[3], last))
                elif x[0] == "bin" and PREC.get(x[1]) == PREC[op]:
                    raise Hole("\\dots after another operator")
                else:
                    x = fold(op, x, last)
                continue
            x = ("bin", op, x, self.term())
        return x

    STARTS = {"let", "num"}

    def starts_atom(self):
        t = self.peek()
        if t[0] in ("let", "num"):
            return True
        if t[0] == "sym" and t[1] == "(":
            return not self.gap()  # a gap before ( ends the term: a side condition or a gloss follows
        if t[0] == "sym" and t[1] == "|":
            return self.bars == 0
        if t[0] == "cmd":
            return (t[1] in GREEK or t[1] in ("infty", "frac", "tfrac", "dfrac", "sum", "prod", "lceil", "lfloor", "ell",
                                              "mathbf", "boldsymbol", "mathrm", "operatorname", "max", "min",
                                              "binom", "tbinom", "#") or t[1] in FUNC_CMDS or t[1] in BOLD_CMDS
                    or re.fullmatch(r"b[a-z]", t[1]) is not None)
        return False

    def term(self):
        x = self.power()
        run = [x]  # the factors juxtaposed in a row (a run of letters with no declaration is prose, not a product)
        while True:
            if len(run) >= 3 and SCOPED[0] and all(
                    f[0] == "var" and len(f[1]) == 1 and f[1].isalpha() and f[1] not in SCALARS for f in run[-3:]):
                raise Hole("letters side by side that no declaration makes numbers (prose outside \\text?)")
            if self.at("sym", "*") or self.at("cmd", "cdot"):
                self.k += 1
                run = [self.power()]
                x = ("bin", "*", x, run[0])
            elif self.at("cmd", "times"):
                # the cartesian product of sets (A\times B, [a,b]\times[c,d], \Z^{m\times k}): never a product of numbers
                self.k += 1
                run = [self.power()]
                x = ("bin", "times", x, run[0])
            elif self.at("sym", "/"):
                self.k += 1
                run = [self.power()]
                x = ("bin", "/", x, run[0])
            elif self.at("cmd", "circ"):
                # g\circ\pi: the composition; g_L\circ\dots\circ g_1, the composition of a family
                self.k += 1
                if self.peek() in DOTS:
                    self.k += 1
                    self.eat("cmd", "circ")
                    x = fold("comp", x, self.power())
                    run = [None, None]
                    continue
                run = [self.power()]
                x = ("bin", "comp", x, run[0])
            elif self.at("sym", "[") and x[0] != "interval" and self.bracket_kind() == "interval":
                # 2^{-z}[2^{-D},2]: a number times an interval, as [2^{-D},2]2^{-z}
                iv = self.set_atom()
                if iv[0] != "interval" or iv[3] is not None:
                    raise Hole("a number times a set that is not a closed interval")
                x = ("interval", iv[1], iv[2], x)
            elif self.starts_atom() and not self.at("sym", "(") and maps_at(factors(x)[-1], self.vocab) \
                    and self.peek()[0] in ("let", "cmd") and not self.at("cmd", "frac"):
                # \pi_\phi\bxi: a declared map applied by juxtaposition, never a product
                last = factors(x)[-1]
                y = ("app", last, (self.power(),), "call")
                x = y if x is last else replace_last_factor(x, y)
                run = [y]
            elif self.starts_atom() and factors(x)[-1] in (("var", "d"), ("var", "D")) and "d" not in SCALARS \
                    and "D" not in SCALARS and self.differential_ahead():
                # dR(\bw_0), D\Phi(0): the differential of a declared map, never d times R
                y = self.power()
                f, args = (y[1], y[2]) if y[0] == "app" and y[3] == "call" else (y, None)
                jac = ("app", ("var", "jac"), (f,), "call")
                d = jac if args is None else ("app", jac, args, "call")
                x = d if x == factors(x)[-1] else replace_last_factor(x, d)
                run = [d]
            elif self.at("sym", "(") and not self.gap() and factors(x)[-1][0] == "comp" or (
                    self.at("sym", "(") and not self.gap() and factors(x)[-1][:2] == ("bin", "comp")):
                # (g_L\circ\dots\circ g_1)(y): a composition applied, never a product
                last = factors(x)[-1]
                y = ("app", last, tuple(self.call_args()), "call")
                x = y if x is last else replace_last_factor(x, y)
                run = [y]
            elif self.starts_atom():
                if self.at("sym", "("):
                    # X(E), X^{-1}(E) read as a product: only when X is declared a number here (never a guess;
                    # \pi^{-1}(h) is the inverse map at h; x^2(E) is a product)
                    last = factors(x)[-1]
                    inverse = last[0] == "pow" and last[2] == ("neg", ("num", "1"))
                    key = name_key(last[1] if inverse else last, self.vocab)
                    if key is not None:
                        number = key in SCALARS
                        if SCOPED[0] and not number:
                            raise Hole(f"{to_qpp(last)} before a parenthesis: not declared a number here")
                        JUXT.append((key, number))
                last = factors(x)[-1]
                key = name_key(last, self.vocab)
                form = to_qpp(last) if last[0] in ("var", "app") else None
                if SCOPED[0] and form in MAP_CLASH and key not in SCALARS and not self.at("sym", "("):
                    # \pi_\phi\zeta with pi_ a map and a number in the paper: no reading is safe
                    raise Hole(f"{form} is declared a map and a number in the paper: a name clash")
                if form in MAPS | MAP_CLASH and not self.at("sym", "("):
                    JUXT.append((key, key in SCALARS))  # a map times a term: misread unless a number in scope
                y = self.power()
                if SCOPED[0] and last[0] == "var" and len(last[1]) == 1 and last[1].isupper() and last[1] not in SCALARS \
                        and last[1] not in ELSEWHERE \
                        and (y[0] == "var" and y[1].startswith("b_") or y[0] == "app" and y[1][0] == "var"
                             and y[1][1].startswith("b_")):
                    # \beta J\bs: a capital before a vector is a matrix or a map applied, unless declared a number
                    raise Hole(f"{last[1]} before a vector: a matrix or a map (declare it), not a product")
                head = last[1] if last[0] == "var" else last[1][1] if last[0] == "app" and len(last) > 3 and \
                    last[3] == "idx" and last[1][0] == "var" else None
                if SCOPED[0] and head is not None and len(head) == 1 and head.isupper() and key not in SCALARS \
                        and head not in SCALARS and y[0] == "app" and y[3] == "call" and y[1][0] == "var" \
                        and y[1][1] in FUNC_LETTERS and y[1][1][0].isupper():
                    # D_iP(\bw,\bw'): a capital not declared a number before a polynomial applied is an operator on
                    # it (the divided difference D_iP), not a product of D_i and the value P(\bw,\bw')
                    raise Hole(f"{to_qpp(last)} before {y[1][1]}(...): an operator on {y[1][1]} (declare it), "
                               "not a product")
                x = ("bin", "*", x, y)
                run.append(y)
            else:
                return x

    def differential_ahead(self):
        """the name at the cursor is a map declared in scope (a function, not a number): d before it is a differential"""
        t = self.peek()
        if t[0] == "let":
            name = t[1]
        elif t[0] == "cmd" and t[1] in GREEK:
            name = t[1]
        elif t[0] == "cmd" and t[1] in BOLD_CMDS:
            name = BOLD_CMDS[t[1]]
        else:
            return False
        return SCOPED[0] and name in self.functions and name not in SCALARS and (name in MAPS or name not in FUNC_LETTERS)

    def bracket_kind(self):
        """what the bracket at the cursor holds: "interval" (a comma at its top level), "prop" (a relation), or None"""
        depth, j, comma, rel = 0, self.k, False, False
        while j < len(self.t):
            tok = self.t[j]
            if tok in (("sym", "("), ("sym", "["), ("sym", "{"), ("cmd", "{")):
                depth += 1
            elif tok in (("sym", ")"), ("sym", "]"), ("sym", "}"), ("cmd", "}")):
                depth -= 1
                if depth == 0:
                    break
            elif depth == 1 and tok == ("sym", ","):
                comma = True
            elif depth == 1 and ((("\\" + tok[1]) if tok[0] == "cmd" else tok[1]) in REL_TEX or tok == ("cmd", "in")):
                rel = True
            j += 1
        if j >= len(self.t) or (self.t[j] != ("sym", "]") and not comma):
            return None
        return "interval" if comma else "prop" if rel else None

    def power(self):
        x = self.atom()
        if self.at("sym", "!") and x[0] in ("var", "num", "app", "bin", "neg") and self.peek(1) != ("sym", "="):
            # k!, (k+1)!: the factorial
            self.k += 1
            x = ("app", ("var", "fact"), (x,), "call")
        if self.at("sym", "_") and self.peek(1) == ("sym", "{") and x[0] != "var" and \
                not (x[0] == "app" and x[3] == "call") and \
                self.t[self.k - 1] == ("sym", ")") and any(
                    tok in (("cmd", "in"), ("cmd", "le"), ("cmd", "leq"), ("sym", "<"))
                    for tok in self.t[self.k + 2:self.k + 12]):
            # (|f|)_{f\in\mathcal J}: the tuple of the values over a set; (I_j)_{j\le k}: the list over a range
            self.k += 1
            var, dom = self.big_range(self.sub(self.group()), "tuple")
            if dom is None or dom[0] not in ("in", "le", "lt", "range"):
                raise Hole("a tuple over a range that is neither a set nor an interval of indices")
            return ("famtuple", var, dom, x)
        if self.at("sym", "_") and (x[0] != "var" or self.t[self.k - 1] == ("sym", ")")) and (
                self.peek(1) == ("sym", "+") or (self.peek(1) == ("sym", "{") and self.peek(2) == ("sym", "+")
                                                 and self.peek(3) == ("sym", "}"))):
            # (x-t)_+, (y)_+: the positive part, max(x - t, 0) (a name e_+ is a name, read by name_sub)
            self.k += 2 if self.peek(1) == ("sym", "+") else 4
            x = ("app", ("var", "max"), (x, ("num", "0")), "call")
        while self.at("sym", "^") or self.at("sym", "'"):
            if self.at("sym", "'"):
                self.k += 1
                if x[0] != "var":
                    raise Hole("prime")
                x = ("var", x[1] + "'")
                continue
            self.k += 1
            g = self.group()
            if g in ([("sym", "*")], [("cmd", "ast")]) and x[0] == "var":
                x = ("var", x[1] + "_star" if "_" not in x[1] else x[1] + "star")
                continue
            if g == [("cmd", "prime")] and x[0] == "var":
                x = ("var", x[1] + "'")
                continue
            if g in ([("num", "0")], [("cmd", "circ")]) and x[0] == "var":
                # a^0, w^\circ: a label (a base point), not a power (a zeroth power is never written)
                x = ("var", x[1] + ("_nought" if g[0][0] == "num" else "_circ"))
                if self.at("sym", "_"):
                    x, idx = self.name_sub(x[1])  # a^0_h: the label, then the index
                    if idx is not None:
                        x = ("app", x, idx, "idx")
                continue
            if len(g) >= 3 and g[0] == ("sym", "(") and g[-1] == ("sym", ")"):
                raise Hole("a superscript label ^{(j)} (a member of a family, not a power)")
            if g in ([("sym", "+")], [("sym", "-")]) and x[0] == "var":
                x = ("var", x[1] + ("_pos" if g[0][1] == "+" else "_neg"))
                continue
            if g in ([("cmd", "pm")], [("cmd", "mp")]) and x[0] == "var":
                x = ("var", x[1] + ("_pos" if self.pm(g[0][1]) == "+" else "_neg"))
                continue
            if g == [("cmd", "top")]:
                x = ("app", ("var", "transpose"), (x,), "call")
                continue
            if len(g) == 2 and g[0] == ("cmd", "otimes"):
                # \bv^{\otimes d}: the tensor power, the vector of the degree-d monomials of v
                x = ("app", ("var", "tensor"), (x, self.sub(g[1:]).whole()), "call")
                continue
            if g == [("cmd", "vee")] or g == [("cmd", "top")]:
                raise Hole("superscript mark")
            x = ("pow", x, self.sub(g).whole())
        return x

    def name_sub(self, base):
        """a subscript after a name: digits and +/- join the name, letters are indices; a name the paper declares
        in a row \\sit{names}{...} (n_y, \\kappa_{\\rm new}, s_{\\min}: vocab "#names") is one name"""
        self.k += 1
        g = self.group()
        spelled = spell_sub(g)
        if spelled and f"{base}_{spelled}" in (self.vocab or {}).get("#names", ()):
            return ("var", f"{base}_{spelled}"), None
        if len(g) >= 2 and all(t[0] == "let" for t in g):
            return ("var", base), tuple(("var", t[1]) for t in g)  # M_{ij}: one index per letter
        if all(t[0] == "num" for t in g):
            return ("var", base + "_" + "".join(t[1] for t in g)), None
        if len(g) == 1 and g[0] in (("sym", "+"), ("sym", "-")):
            return ("var", base + ("_plus" if g[0][1] == "+" else "_minus")), None
        if len(g) == 1 and g[0] in (("sym", "*"), ("cmd", "ast")):
            # O_*, \beta_*: a star below is part of the name (O_ast), another name than O^* (O_star)
            return ("var", base + "_ast"), None
        if len(g) == 1 and g[0] in (("cmd", "pm"), ("cmd", "mp")):
            return ("var", base + ("_plus" if self.pm(g[0][1]) == "+" else "_minus")), None
        sp = self.sub(g)
        idx = [sp.expr()]
        while sp.at("sym", ","):
            sp.k += 1
            idx.append(sp.expr())
        if not sp.done():
            # M_{ij}: two letters, two indices
            if all(t[0] == "let" for t in g):
                return ("var", base), tuple(("var", t[1]) for t in g)
            raise Hole("subscript")
        if len(idx) == 1 and not any(t in (("sym", "*"), ("cmd", "cdot"), ("cmd", "times")) for t in g):
            # \sigma_{mm'}, M_{\alpha\beta}: letters side by side in a subscript are one index each, as those of M_{ij}
            # are (never their product; a_{2i} keeps its numeral factor)
            fs = factors(idx[0])
            if len(fs) >= 2 and all(f[0] == "var" and (len(f[1].rstrip("'")) == 1 or f[1].rstrip("'") in GREEK)
                                    for f in fs):
                return ("var", base), tuple(fs)
            if len(fs) >= 2 and all(is_name(f) for f in fs):
                # T_{u_{a-1}mu_a}, V_{\varphi\one_O}: indices or a product, no reading is safe (commas, or \cdot)
                raise Hole("names side by side in a subscript: write the indices with commas, a product with \\cdot")
        return ("var", base), tuple(idx)

    def atom(self):
        t = self.peek()
        if t[0] == "num":
            self.k += 1
            return ("num", t[1])
        if t[0] == "sym" and t[1] == "(":
            self.k += 1
            save = self.k
            x = self.expr()
            r = self.peek()
            if (("\\" + r[1]) if r[0] == "cmd" else r[1]) in REL_TEX and not (r[0] == "sym" and r[1] not in "<>="):
                # a claim in parentheses as a term: in the data of a proof word a citation of a hypothesis by its
                # content, \alpha[(x\preceq y)+2(y\preceq z)]; rel() admits it only in a combination (combination_ok)
                self.k = save
                x = self.rel()
                self.eat("sym", ")")
                return ("cite", x) if DATA_MODE[0] and x[0] == "rel" else x
            if self.at("sym", ","):
                xs = [x]
                while self.at("sym", ","):
                    self.k += 1
                    xs.append(self.expr())
                if len(xs) == 2 and self.at("sym", "]"):
                    self.k += 1
                    return ("ivl", "oc", xs[0], xs[1])  # the half-open interval (a, b]
                self.eat("sym", ")")
                return ("tuple", tuple(xs))
            self.eat("sym", ")")
            if (x[0] == "app" and x[3] == "idx" and x[1][0] == "var" and SCOPED[0]
                    and any(a[0] == "var" and a[1] not in SCALARS for a in x[2])
                    and not self.at("sym", "_") and not self.at("sym", "^")):
                # (I_j): the list of the I_j, whose range the paper must give, not the member at a free j
                raise Hole(f"a list needs its range: ({to_qpp(x)})_{{j<=k}}")
            return x
        if t[0] == "sym" and t[1] == "|":
            self.k += 1
            self.bars += 1
            x = self.expr()
            self.bars -= 1
            self.eat("sym", "|")
            if self.at("sym", "_"):
                self.k += 1
                return ("norm", x, self.norm_sub(), "|")
            return ("abs", x)
        if t[0] == "cmd" and t[1] in ("lceil", "lfloor"):
            self.k += 1
            x = self.expr()
            self.eat("cmd", "rceil" if t[1] == "lceil" else "rfloor")
            return ("ceil" if t[1] == "lceil" else "floor", x)
        if t[0] == "cmd" and t[1] in ("frac", "tfrac", "dfrac"):
            self.k += 1
            a = self.sub(self.group()).whole()
            b = self.sub(self.group()).whole()
            return ("bin", "/", a, b)
        if t[0] == "cmd" and t[1] in ("bigcup", "bigcap"):
            # the union (intersection) of a family of sets: \bigcup_{\bx\in X}Y(\bx), \bigcup\{Y(\bx):\ \bx\in X\},
            # and of a set of sets, \bigcup U
            self.k += 1
            kind = "union" if t[1] == "bigcup" else "inter"
            if self.at("sym", "_"):
                self.k += 1
                var, dom = self.upper(*self.big_range(self.sub(self.group()), kind), kind)
                return (kind, var, dom, self.power_or_term())
            if self.at("cmd", "{"):
                return self.over_builder(kind, self.atom())
            return ("sunion" if kind == "union" else "sinter", self.power())
        if t[0] == "cmd" and t[1] == "bigoplus":
            # \bigoplus_{j\le J}(\lambda_j,m_j), \bigoplus_{\pi,T}: the tropical sum of pairs (the least pair)
            self.k += 1
            if not self.at("sym", "_"):
                raise Hole("\\bigoplus without an index")
            self.k += 1
            g = self.sub(self.group())
            names = self.split_names(g.t)
            if names is not None and len(names) > 1:
                body = self.power_or_term()
                for v in reversed(names):
                    body = ("oplus", v, None, body)
                return body
            var, dom = self.upper(*self.big_range(g, "oplus"), "oplus")
            return ("oplus", var, dom, self.power_or_term())
        if t[0] == "cmd" and t[1] in ("sum", "prod") and self.peek(1) == ("cmd", "{"):
            # \sum\{t(\bx):\ \bx\in X,\ P(\bx)\}: the sum over the set builder, as \sum_{\bx\in X,\ P}t
            self.k += 1
            return self.over_builder(t[1], self.atom())
        if t[0] == "cmd" and t[1] in ("sum", "prod"):
            self.k += 1
            if not self.at("sym", "_"):
                raise Hole("sum without index")
            self.k += 1
            if t[1] == "sum" and self.at("sym", "{") and self.peek(1) == ("cmd", "substack"):
                return self.cell_sum()
            var, dom = self.big_range(self.sub(self.group()), t[1])
            if self.at("sym", "^"):
                if not dom or dom[0] != "from":
                    raise Hole("sum with upper limit")
                self.k += 1
                hi = self.sub(self.group()).whole()
                dom = ("range", (dom[1], hi))
            elif dom and dom[0] == "from":
                raise Hole("sum from without upper limit")
            body = self.power_or_term()
            if dom is None and var not in index_names(body) and ("var", var) not in subterms(body):
                # \sum_{I_+} b_i: the subscript is the set, the index is the one the body uses
                idx = index_names(body)
                if len(idx) != 1:
                    raise Hole("sum over a set without an index")
                var, dom = idx.pop(), ("in", ("var", var))
            return (t[1], var, dom, body)
        if t[0] == "cmd" and t[1] == "qppfam":
            self.k += 1
            nm = self.sub(self.group()).atom()
            lo = self.sub(self.group()).whole()
            hi = self.sub(self.group()).whole()
            if nm[0] != "var":
                raise Hole("family")
            return ("family", nm[1], lo, hi)
        if t[0] == "sym" and t[1] == "[":
            if self.bracket_kind() == "prop":
                # [P]: the Iverson bracket, 1 if P holds and 0 if not, as \mathbf 1[P]
                n = self.bracket_len()
                sp = self.sub(self.t[self.k + 1:self.k + 1 + n])
                self.k += n + 2
                x = sp.prop()
                if not sp.done():
                    raise Hole("the proposition of an Iverson bracket")
                return ("iverson", x)
            # a closed interval as a term: [a, b] (of numbers or of vectors)
            return self.setexpr()
        if t[0] == "cmd" and t[1] == "mathring":
            # \mathring B: the interior of a box or an interval, the product of the open intervals
            self.k += 1
            return ("app", ("var", "interior"), (self.sub(self.group()).setexpr(),), "call")
        if t[0] == "cmd" and t[1] == "{":
            # a set builder \{x\in S:\ P\}, an image \{t:\ D\} (D declares the names of t), or \{P\}; a listing
            # \{a, b\}; the integers \{a,\dots,b\}
            self.k += 1
            body = self.setexpr() if self.at("sym", "[") else self.prop()
            if self.at("sym", ":"):
                self.k += 1
                body = ("such", body, self.part())
            elif self.at("sym", ","):
                elems = [body]
                while self.at("sym", ","):
                    self.k += 1
                    if self.peek() in DOTS:
                        self.k += 1
                        self.eat("sym", ",")
                        hi = self.expr()
                        self.eat("cmd", "}")
                        if len(elems) != 1:
                            raise Hole("a listing with dots after more than one term")
                        return ("intrange", elems[0], hi)
                    elems.append(self.expr())
                self.eat("cmd", "}")
                return ("setlist", tuple(elems))
            self.eat("cmd", "}")
            return ("setof", body)
        if t[0] == "cmd" and t[1] == "#":
            # the number of elements of a set
            self.k += 1
            return ("app", ("var", "card"), (self.atom(),), "call")
        if t[0] == "cmd" and t[1] == "varnothing":
            self.k += 1
            return ("set", "empty")
        if t[0] == "cmd" and t[1] == "top":
            # the top element of the pairs (a superscript \top, the transpose, is read with the superscripts)
            self.k += 1
            return ("var", "top")
        if t[0] == "cmd" and t[1] in ("mathcal", "mathfrak") and self.peek(1)[0] in ("let", "sym"):
            self.k += 1
            g = self.group()
            if len(g) != 1 or g[0][0] != "let":
                raise Hole(t[1])
            self.t.insert(self.k, ("let", "\x00" + ("cal_" if t[1] == "mathcal" else "frak_") + g[0][1]))
            self.g.insert(self.k, False)
            t = self.peek()
        if t[0] == "cmd" and t[1] == "|":
            self.k += 1
            self.bars += 1
            x = self.expr()
            self.bars -= 1
            self.eat("cmd", "|")
            sub = None
            if self.at("sym", "_"):
                self.k += 1
                sub = self.norm_sub()
            return ("norm", x, sub, "||")
        if t[0] == "cmd" and t[1] in ("binom", "tbinom"):
            self.k += 1
            a = self.sub(self.group()).whole()
            b = self.sub(self.group()).whole()
            return ("app", ("var", "choose"), (a, b), "call")
        if t[0] == "cmd" and t[1] in ("bidetP", "bidetM", "bidetPa", "bidetMa"):
            # the halves of the bideterminant, as qpp2latex prints them
            self.k += 1
            args = [self.sub(self.group()).whole()]
            if t[1] in ("bidetP", "bidetM"):
                args.append(self.sub(self.group()).whole())
            return ("app", ("var", t[1][:6]), tuple(args), "call")
        if t[0] == "cmd" and t[1] in ("max", "min"):
            self.k += 1
            if self.at("cmd", "{"):
                # the least (greatest) element of a set: \min\{k:\ P\}
                return ("least", t[1], self.atom())
            if self.at("sym", "_"):
                self.k += 1
                var, dom = self.big_range(self.sub(self.group()), t[1])
                if dom and dom[0] == "from":
                    if not self.at("sym", "^"):
                        raise Hole("max range")
                    self.k += 1
                    dom = ("range", (dom[1], self.sub(self.group()).whole()))
                return (t[1], var, dom, self.term())
            self.eat("sym", "(")
            args = [self.expr()]
            while self.at("sym", ","):
                self.k += 1
                args.append(self.expr())
            self.eat("sym", ")")
            return ("app", ("var", t[1]), tuple(args), "call")
        if t[0] == "cmd" and t[1] in FUNC_CMDS:
            self.k += 1
            head = ("var", t[1])
            if self.at("sym", "_"):
                # \deg_yS, \mathrm{lc}_y(S), \mathrm{Res}_y(S,T): an operator with a variable below, the family
                # of operators deg_(y) applied
                head = ("app", head, self.sub_indices(), "idx")
            if self.at("sym", "("):
                args = self.call_args()
            else:
                args = [self.power()]
            return ("app", head, tuple(args), "call")
        if t[0] == "cmd" and t[1] == "partial":
            return self.derivative()
        if t[0] == "cmd" and t[1] == "int":
            return self.integral()
        if t[0] == "cmd" and t[1] in ("mathrm", "operatorname") and self.peek(1) == ("sym", "{"):
            self.k += 1
            inner = self.group()
            if not all(x[0] == "let" for x in inner):
                raise Hole("mathrm")
            fname = "".join(x[1] for x in inner)
            if fname == "prog" and self.at("sym", "(") and not self.gap():
                # \operatorname{prog}(DECLS, ROWS:\ COST): a linear program, its scales and rows a context
                toks, depth, cut = self.paren_tokens(), 0, None
                for j, tk in enumerate(toks):
                    if tk in (("sym", "("), ("sym", "{"), ("sym", "[")):
                        depth += 1
                    elif tk in (("sym", ")"), ("sym", "}"), ("sym", "]")):
                        depth -= 1
                    elif tk == ("sym", ":") and depth == 0:
                        cut = j
                if cut is None:
                    raise Hole("\\operatorname{prog}: the scales and rows, a colon, the cost")
                left, right = self.sub(toks[:cut]), self.sub(toks[cut + 1:])
                xs = left.clauses()
                cost = right.expr()
                if not left.done() or not right.done():
                    raise Hole("\\operatorname{prog}: the scales and rows, a colon, the cost")
                return ("prog", ("ctx", conj(xs), cost))
            if self.at("sym", ".") and not self.gap():
                # \mathrm{Pr}.P, \mathrm{Pr}.\mathrm{op}: the part of a bundle, one name Pr.P
                tk = self.peek(1)
                part = None
                if tk[0] == "let":
                    part, step = tk[1], 2
                    # the digits that follow with no space are of the name: \mathrm{Cl}.u0, \mathrm{Cl}.K0
                    while self.k + step < len(self.t) and self.t[self.k + step][0] == "num" and \
                            not self.g[self.k + step] and re.fullmatch(r"\d+", self.t[self.k + step][1]):
                        part += self.t[self.k + step][1]
                        step += 1
                elif tk == ("cmd", "mathrm") and self.peek(2) == ("sym", "{"):
                    j, letters = self.k + 3, ""
                    while j < len(self.t) and self.t[j][0] == "let":
                        letters += self.t[j][1]
                        j += 1
                    if letters and j < len(self.t) and self.t[j] == ("sym", "}"):
                        part, step = letters, j + 1 - self.k
                elif tk[0] == "cmd" and tk[1] in GREEK:
                    part, step = tk[1], 2
                if part is None:
                    raise Hole(f"\\mathrm{{{fname}}}. without the name of a part")
                self.k += step
                fname = f"{fname}.{part}"
                if self.at("sym", "_"):
                    # its indices as those of a name: \mathrm{Pr}.N_{mi}, one index per letter (name_sub)
                    v, idx = self.name_sub(fname)
                    head = ("app", v, idx, "idx") if idx else v
                    if not self.at("sym", "(") or self.gap():
                        return head
                    return ("app", head, tuple(self.call_args()), "call")
            head = ("var", fname)
            if self.at("sym", "_"):
                # \mathrm{Pat}_\delta(\bx), \mathrm{lo}_\bx: a named family of the paper at its index (applied when a
                # parenthesis follows); \mathrm{nuP}_{ji} at two indices, one per letter, as M_{ij}
                head = ("app", head, self.named_indices(), "idx")
            if (not self.at("sym", "(") or self.gap()) and fname in NEEDS_ARG:
                # \mathrm{rank}\{...\} takes the term after it; \mathrm{rank} alone has no argument
                if self.gap() or not self.starts_atom() and not self.at("cmd", "{"):
                    raise Hole(f"\\mathrm{{{fname}}} without its argument")
                return ("app", head, (self.power(),), "call")
            if not self.at("sym", "(") or self.gap():
                return head
            x = ("app", head, tuple(self.call_args()), "call")
            if fname in self.functions and self.at("sym", "(") and not self.gap():
                # \mathrm{halve}(n,N)(u): a typed word that the reader declared, applied at a point
                x = ("app", x, tuple(self.call_args()), "call")
                if self.at("sym", "_"):
                    # \mathrm{halve}(n,N)(u)_j: a coordinate of its tuple at that point
                    x = ("app", x, self.sub_indices(), "idx")
            return x
        if t[0] == "cmd" and t[1] in ("eqref", "cref", "Cref", "ref") and self.peek(1) == ("sym", "{"):
            self.k += 1
            inner = self.group()
            lab = "".join(x[1] if x[0] != "cmd" else "\\" + x[1] for x in inner)
            if not re.fullmatch(r"[A-Za-z0-9:_\-]+", lab):
                raise Hole("reference label")
            j = self.k
            if self.at("sym", "(") and not self.gap():
                # \cref{lem:x}(2): the item (2) of the result, not a product
                while j + 1 < len(self.t) and self.t[j + 1][0] in ("num", "let") and j - self.k < 3:
                    j += 1
                if j > self.k and j + 1 < len(self.t) and self.t[j + 1] == ("sym", ")"):
                    item = "".join(str(x[1]) for x in self.t[self.k + 1:j + 1])
                    self.k = j + 2
                    return self.ref_args(f"{lab}({item})")
            return self.ref_args(lab)
        if t[0] == "cmd" and t[1] in SETS:
            return self.setexpr()
        name = None
        if t[0] == "cmd" and t[1] == "mathbf" and (
                (self.peek(1) == ("num", "1") and self.peek(2) == ("sym", "["))
                or (self.peek(1) == ("sym", "{") and self.peek(2) == ("num", "1") and self.peek(3) == ("sym", "}")
                    and self.peek(4) == ("sym", "["))):
            # \mathbf 1[P]: the indicator of the proposition P, 1 if P holds and 0 if not
            self.k += 2 if self.peek(1) == ("num", "1") else 4
            depth, j = 0, self.k
            while j < len(self.t):
                if self.t[j] == ("sym", "["):
                    depth += 1
                elif self.t[j] == ("sym", "]"):
                    depth -= 1
                    if depth == 0:
                        break
                j += 1
            if j >= len(self.t):
                raise Hole("unbalanced [ of an indicator")
            toks = self.t[self.k + 1:j]
            sp = self.sub(toks)
            self.k = j + 1
            try:
                x = sp.prop()
                whole = sp.done()
            except PlusMinus:
                raise
            except Hole:
                x, whole = None, False  # (\forall ...),\ t\le K: clauses, read as a part below
            if not whole:
                # a relation of the vocabulary (s\ \text{feasible}\ \mathrm{Pr}), or a list of clauses: read as
                # a part
                sp = self.sub(toks)
                try:
                    x = sp.part()
                except Hole:
                    x = None
                if x is None or not sp.done():
                    raise Hole("the proposition of an indicator")
            return ("iverson", x)
        if t[0] == "cmd" and t[1] == "mathbf" and (self.peek(1) == ("num", "0") or (
                self.peek(1) == ("sym", "{") and self.peek(2) == ("num", "0") and self.peek(3) == ("sym", "}"))):
            # \mathbf 0: the zero vector
            self.k += 2 if self.peek(1) == ("num", "0") else 4
            return ("var", "b_zero")
        if t[0] == "cmd" and t[1] in ("mathbf", "boldsymbol") and self.peek(1) == ("sym", "{"):
            self.k += 1
            inner = self.group()
            if len(inner) == 1 and inner[0][0] == "let":
                name = "b_" + inner[0][1]
            elif len(inner) == 1 and inner[0][0] == "cmd" and inner[0][1] in GREEK:
                name = "b_" + inner[0][1]
            else:
                raise Hole("bold")
        elif t[0] == "cmd" and t[1] in BOLD_CMDS:
            name = BOLD_CMDS[t[1]]
            self.k += 1
        if name is not None:
            pass
        elif t[0] == "let" and t[1].startswith(("\x00cal_", "\x00frak_")):
            name = t[1][1:]
        elif t[0] == "let":
            name = t[1]
        elif t[0] == "cmd" and t[1] in GREEK:
            name = t[1]
        elif t[0] == "cmd" and t[1] == "ell":
            name = "l"
        elif t[0] == "cmd" and t[1] == "infty":
            raise Hole("\\infty: no infinity in a statement (a flag or a case)")
        elif t[0] == "cmd" and re.fullmatch(r"b[a-z]", t[1]):
            name = "b_" + t[1][1]
            self.k += 1
        if name is None:
            raise Hole(f"token {t}")
        if not name.startswith("b_"):
            self.k += 1
        x, idx = ("var", name), None
        if self.at("sym", "'") and self.peek(1) == ("sym", "_"):
            # beta'_j: a prime before the subscript, the same name as beta_j' (the family beta' at j)
            self.k += 1
            name += "'"
            x = ("var", name)
        base = name  # the letter: a function letter stays one with a prime or a mark (f', f^*)
        mark = self.name_mark()
        if mark is not None:
            # Y^+_R, rho^*_i, a^0_h: a mark before the subscript is part of the name (the family Y^+ at R)
            name = mark_name(name, mark)
            x = ("var", name)
        if self.at("sym", "_"):
            x, idx = self.name_sub(name)
        while self.at("sym", "'"):
            self.k += 1
            x = ("var", x[1] + "'")
        mark = self.name_mark() if mark is None else None
        if mark is not None:
            # Y_R^+, x_1^*: a mark after the subscript, the same name as before it (Y^+_R)
            if idx is not None:
                name = mark_name(name, mark)
                x = ("var", name)
            else:
                same = x[1].rstrip("'") == name
                x = ("var", mark_name(x[1], mark))
                name = x[1] if same else mark_name(name, mark)  # x_1^*: a member of the family x^* (key x_star_)
        if idx is not None:
            x = ("app", x, idx, "idx")
        # X(E): an application if X is a function, a product if X is a number, a hole otherwise; a member of a
        # family (t_a, x_0) is keyed t_, x_, apart from t and x (a family of functions may be indexed by numbers)
        key = name + "_" if idx is not None or x[1].rstrip("'") != name else name
        if idx is None and x[1].endswith("_ast"):
            key = x[1]  # O_*: one name, not a member of a family O
        if idx is None and x[1].rstrip("'") in (self.vocab or {}).get("#names", ()):
            key = x[1].rstrip("'")  # a declared name n_y is not a member of a family n
        number = key in SCALARS
        is_fun = not number and key not in ELSEWHERE and (key in self.functions or name in self.functions
                                                          or base in FUNC_LETTERS & self.functions)
        if self.at("sym", "(") and not self.gap() and x == ("var", "cal_P") and not number:
            # \mathcal P(S): the set of the subsets of S
            self.k += 1
            s = self.setexpr()
            self.eat("sym", ")")
            return ("app", ("var", "powerset"), (s,), "call")
        if self.at("sym", "(") and not self.gap() and x == ("var", "O") and not number and "O" not in MAPS:
            # O(2^n) is the order, also where the paper applies O to a numeral elsewhere (O(1)), which would make it
            # a function of the scope
            raise Hole("O(...): asymptotic notation is no statement; write the constant (the O(...) form stays in the "
                       "sentence before the stmt)")
        if self.at("sym", "(") and not self.gap() and not is_fun and not number and (SCOPED[0] or key in ELSEWHERE):
            raise Hole(f"{to_qpp(x)} before a parenthesis: neither a function nor a number here (declare it)")
        if self.at("sym", "(") and not self.gap() and not is_fun and self.applied_like():
            # rho(0), Delta_P(b_a_0, xi): a letter applied to a number or a tuple is not a product
            raise Hole(f"{to_qpp(x)} applied to a number or a tuple (declare it as a function)")
        if self.at("sym", "(") and not self.gap() and is_fun:
            x = ("app", x, tuple(self.call_args()), "call")
        if self.at("sym", "|") and self.peek(1) == ("sym", "_") and self.bars == 0:
            # h|_F: the restriction of h to F (h|_F=0 is h = 0 on F)
            self.k += 2
            x = ("app", ("var", "restrict"), (x, self.sub(self.group()).setexpr()), "call")
        return x

    def over_builder(self, kind, b):
        """the big operator kind over a set builder {t : x in X, P} (x the first name its condition declares): the
        operator over x in X with P of t"""
        if b[0] != "setof" or b[1][0] != "such":
            raise Hole(f"{kind} over a set that is not a builder")
        head, cond = b[1][1], b[1][2]
        cs = list(cond[1]) if cond[0] == "and" else [cond]
        binders = []
        while cs:
            first = cs[0]
            if first[0] == "decl" and first[1][0][0] == "var" and all(n[0] == "var" for n in first[1]):
                binders += [(n[1], first[2]) for n in first[1]]
            elif first[0] == "rel" and first[1] == ("in",) and first[2][0][0] == "var":
                binders.append((first[2][0][1], first[2][1]))
            else:
                break
            cs = cs[1:]
        if not binders:
            raise Hole(f"{kind} over a builder whose condition does not start with x in X")
        # \bigcup\{Y_R(\bx):\ R\in\Pi,\ \bx\in X_R,\ P\}: one binder per name, the condition on the innermost
        var, S = binders[-1]
        x = (kind, var, ("in", S) if not cs else ("incond", S, conj(cs)), head)
        for var, S in reversed(binders[:-1]):
            x = (kind, var, ("in", S), x)
        return x

    def split_names(self, toks):
        """the names of a subscript that lists names separated by commas (\\pi,T), or None"""
        out, cur = [], []
        for tok in toks + [("sym", ",")]:
            if tok == ("sym", ","):
                if len(cur) != 1 or not (cur[0][0] == "let" or (cur[0][0] == "cmd" and cur[0][1] in GREEK)):
                    return None
                out.append(cur[0][1])
                cur = []
            else:
                cur.append(tok)
        return out

    def ref_args(self, lab):
        """a reference, with the values of the free names of the referenced condition in brackets:
        \\cref{def:law}(H3)[t^*,\\eta] is (H3) of def:law at t = t^*, eta"""
        if not self.at("sym", "[") or self.gap():
            return ("ref", lab)
        self.k += 1
        args = [self.expr()]
        while self.at("sym", ","):
            self.k += 1
            args.append(self.expr())
        self.eat("sym", "]")
        return ("refat", lab, tuple(args))

    def norm_sub(self):
        """the subscript of a norm: |x|_\\infty (the name inf there), |x|_2, |x|_1"""
        g = self.group()
        if g == [("cmd", "infty")]:
            return ("var", "inf")
        return self.sub(g).atom()

    def integral(self):
        """\\int g\\,dq (against the law q), \\int_a^bg\\,d\\mu (in the variable mu), \\int_a^bP (P a polynomial in its
        variable): Q++ int(g, q), int(g, mu, a, b), int(P, dot, a, b)"""
        self.k += 1
        lo = hi = None
        for _ in range(2):
            if self.at("sym", "_") and lo is None:
                self.k += 1
                lo = self.sub(self.group()).whole()
            elif self.at("sym", "^") and hi is None:
                self.k += 1
                hi = self.sub(self.group()).whole()
        if (lo is None) != (hi is None):
            raise Hole("an integral with one bound")
        depth, j, stop = 0, self.k, None
        while j < len(self.t):
            tok = self.t[j]
            if tok in (("sym", "("), ("sym", "["), ("sym", "{"), ("sym", "|")) and not (tok == ("sym", "|") and depth):
                depth += 1
            elif tok in (("sym", ")"), ("sym", "]"), ("sym", "}")) or (tok == ("sym", "|") and depth):
                if depth == 0:
                    break
                depth -= 1
            elif depth == 0 and (tok in (("sym", ","), ("sym", ";"), ("sym", ":")) or tok[0] == "text" or (
                    (("\\" + tok[1]) if tok[0] == "cmd" else tok[1]) in REL_TEX)):
                break
            elif depth == 0 and tok == ("let", "d") and j + 1 < len(self.t) and (
                    self.t[j + 1][0] == "let" or (self.t[j + 1][0] == "cmd" and self.t[j + 1][1] in GREEK)):
                stop = j
            j += 1
        if stop is None:
            if lo is None:
                raise Hole("an integral without its differential (d and the law or the variable)")
            return ("app", ("var", "int"), (self.power_or_term(), ("blank",), lo, hi), "call")
        body = self.sub(self.t[self.k:stop]).whole()
        self.k = stop + 1
        var = self.atom()
        if not is_name(var):
            raise Hole("the differential of an integral")
        return ("app", ("var", "int"), (body, var) if lo is None else (body, var, lo, hi), "call")

    def bracket_len(self):
        """the number of tokens inside the bracket at the cursor"""
        depth, j = 0, self.k
        while j < len(self.t):
            depth += {("sym", "["): 1, ("sym", "]"): -1, ("sym", "("): 1, ("sym", ")"): -1}.get(self.t[j], 0)
            if depth == 0:
                break
            j += 1
        return j - self.k - 1

    def named_indices(self):
        """the indices below a named family at the cursor (the _ included): those of sub_indices, and letters side by
        side are one index each, as those of M_{ij} (name_sub)"""
        save = self.k
        self.k += 1
        g = self.group()
        if len(g) >= 2 and all(t[0] == "let" for t in g):
            return tuple(("var", t[1]) for t in g)
        self.k = save
        return self.sub_indices()

    def sub_indices(self):
        """the indices of a subscript at the cursor (the _ included): y, {R,f}, \\delta"""
        self.k += 1
        sp = self.sub(self.group())
        idx = [sp.expr()]
        while sp.at("sym", ","):
            sp.k += 1
            idx.append(sp.expr())
        if not sp.done():
            raise Hole("subscript of an operator")
        return tuple(idx)

    def call_args(self):
        """the arguments of an application, (a, b, ...) at the cursor; \\cdot as an argument is a blank, S(\\bw,\\cdot)
        the function of the other arguments"""
        self.eat("sym", "(")
        args = []
        while True:
            if self.at("cmd", "cdot") and self.peek(1) in (("sym", ","), ("sym", ")")):
                self.k += 1
                args.append(("blank",))
            else:
                args.append(self.expr())
            if self.at("sym", ","):
                self.k += 1
                continue
            break
        self.eat("sym", ")")
        return args

    def derivative(self):
        """\\partial_yg, \\partial^k_yg, \\partial_y^kg: the k-th derivative of g in the variable y, a function,
        applied when a parenthesis follows (\\partial^l_yg(p,y)); Q++ deriv(g, y, k)"""
        self.k += 1
        var = order = None
        for _ in range(2):
            if self.at("sym", "_") and var is None:
                self.k += 1
                var = self.sub(self.group()).whole()
            elif self.at("sym", "^") and order is None:
                self.k += 1
                order = self.sub(self.group()).whole()
        if var is None:
            raise Hole("\\partial without a variable")
        # the function: a name alone (its parenthesis, if any, applies the derivative)
        j = self.k + 1
        if self.peek()[0] == "cmd" and self.peek()[1] in ("mathbf", "boldsymbol"):
            j += 1 if self.peek(1)[0] != "sym" else 3
        while j < len(self.t) and self.t[j] in (("sym", "'"),):
            j += 1
        if j < len(self.t) and self.t[j] == ("sym", "_"):
            j += 1
            if j < len(self.t) and self.t[j] == ("sym", "{"):
                depth = 0
                while j < len(self.t):
                    depth += {("sym", "{"): 1, ("sym", "}"): -1}.get(self.t[j], 0)
                    j += 1
                    if depth == 0:
                        break
            else:
                j += 1
        sp = self.sub(self.t[self.k:j])
        sp.functions = set()
        f = sp.atom()
        if not sp.done() or not is_name(f):
            raise Hole("\\partial of a term that is not a name")
        self.k = j
        node = ("app", ("var", "deriv"), (f, var) + ((order,) if order is not None else ()), "call")
        if self.at("sym", "(") and not self.gap():
            node = ("app", node, tuple(self.call_args()), "call")
        return node

    def name_mark(self):
        """the mark of a name at the cursor, ^+ ^- ^* ^\\ast ^\\prime ^0 ^\\circ (^\\pm, ^\\mp as the sign read), consumed;
        None (and nothing consumed) for any other superscript, which is a power"""
        if not self.at("sym", "^"):
            return None
        j = self.k + 1
        nxt = self.t[j] if j < len(self.t) else (None, None)
        if nxt == ("sym", "{"):
            inner = self.t[j + 1:j + 3]
            if len(inner) < 2 or inner[1] != ("sym", "}"):
                return None
            tok, width = inner[0], 3
        else:
            tok, width = nxt, 1
        if tok in (("cmd", "pm"), ("cmd", "mp")):
            tok = ("sym", self.pm(tok[1]))
        if tok not in MARKS:
            return None
        self.k = j + width
        return MARKS[tok]

    def applied_like(self):
        """the parenthesis at the cursor holds a number alone, or a list with a comma at its top level and closed by
        ) (not a half-open interval (0,1])"""
        depth, j, comma = 0, self.k, False
        while j < len(self.t):
            tok = self.t[j]
            if tok in (("sym", "("), ("sym", "["), ("sym", "{")):
                depth += 1
            elif tok in (("sym", ")"), ("sym", "]"), ("sym", "}")):
                depth -= 1
                if depth == 0:
                    if tok != ("sym", ")"):
                        return False
                    return comma or (j == self.k + 2 and self.t[self.k + 1][0] == "num")
            elif tok == ("sym", ",") and depth == 1:
                comma = True
            j += 1
        return False

    def power_or_term(self):
        """the body of a sum: a multiplicative term"""
        return self.term()

    def upper(self, var, dom, kind):
        """the range of a big operator with its upper limit: _{j=lo}^{hi} is lo..hi"""
        if not self.at("sym", "^"):
            return var, dom
        if not dom or dom[0] != "from":
            raise Hole(f"{kind} with an upper limit and no lower one")
        self.k += 1
        return var, ("range", (dom[1], self.sub(self.group()).whole()))

    def cell_sum(self):
        """a sum over a cell, \\sum_{\\substack{H\\\\ C_1\\\\ ...}} t: the first row H its index (i), its range
        (a\\le m\\le b) or its tuple type (u\\in T), each further row a clause"""
        g = self.sub(self.group())
        g.k += 1
        rows, cur, depth = [], [], 0
        for tok in g.group():
            depth += {("sym", "{"): 1, ("sym", "}"): -1, ("sym", "("): 1, ("sym", ")"): -1}.get(tok, 0)
            if tok == ("cmd", "\\") and depth == 0:
                rows.append(cur)
                cur = []
            else:
                cur.append(tok)
        rows.append(cur)
        if not g.done() or len(rows) < 2 or not all(rows):
            raise Hole("a sum over a cell: its index and at least one clause under \\substack")
        var, dom = self.big_range(self.sub(rows[0]), "sum")
        if dom is not None and dom[0] not in ("range", "in"):
            raise Hole("a sum over a cell: its range a..b, a tuple type or none")
        clauses = []
        for r in rows[1:]:
            sp = self.sub(r)
            clauses.append(sp.prop())
            if not sp.done():
                raise Hole("a clause of a sum over a cell")
        return ("sum", var, ("cell", dom, tuple(clauses)), self.power_or_term())

    def big_range(self, g, kind):
        """the index and the range of a big operator from its subscript: i, i\\in S, i<N, i\\le N, i=lo (with
        ^{hi} read by the caller), a chain of bounds lo\\le i\\le hi, or a condition on the index (s_r>0, read with
        the index letter it indexes with, or written i:P with the index first): (index, dom)"""
        depth, comma = 0, None
        for j, tok in enumerate(g.t):
            depth += {("sym", "("): 1, ("sym", ")"): -1, ("sym", "{"): 1, ("sym", "}"): -1, ("sym", "["): 1,
                      ("sym", "]"): -1, ("cmd", "{"): 1, ("cmd", "}"): -1}.get(tok, 0)
            if tok == ("sym", ",") and depth == 0:
                comma = j
                break
        if comma is not None and 0 < comma < len(g.t) - 1:
            # \sum_{\bx\in X,\ a(\bx)\ge L}: the members of X with the condition
            var, dom = self.big_range(g.sub(g.t[:comma]), kind)
            if dom is None or dom[0] != "in":
                raise Hole(f"{kind} range with a condition and no set")
            cond = g.sub(g.t[comma + 1:])
            cond.stmt_mode = True
            c = cond.part()
            if not cond.done():
                raise Hole(f"{kind} range")
            return var, ("incond", dom[1], c)
        colon = [j for j, tok in enumerate(g.t) if tok == ("sym", ":")]
        if colon and colon[0] > 0 and colon[0] < len(g.t) - 1:
            # i:P (or i\in S:P) the indices of the range that satisfy P
            head, cond = g.sub(g.t[:colon[0]]), g.sub(g.t[colon[0] + 1:])
            var, dom = self.big_range(head, kind)
            c = cond.rel()
            if not cond.done():
                raise Hole(f"{kind} range")
            if dom is None:
                return var, ("cond", c)
            raise Hole(f"{kind} over a range with a condition")
        r = g.rel()
        if not g.done():
            raise Hole(f"{kind} range")
        if r[0] == "var":
            return r[1], None
        if r[0] != "rel":
            raise Hole(f"{kind} range")
        if len(r[1]) == 1 and r[2][0][0] == "var":
            op, b = r[1][0], r[2][1]
            dom = {"in": "in", "<": "lt", "<=": "le", "=": "from"}.get(op)
            if dom is not None:
                return r[2][0][1], (dom, b)
        if len(r[1]) == 2 and r[2][1][0] == "var" and r[1] == ("<=", "<="):
            return r[2][1][1], ("range", (r[2][0], r[2][2]))
        idx = index_names(r)
        if len(idx) == 1:
            return idx.pop(), ("cond", r)
        raise Hole(f"{kind} range")


def conj(xs):
    return xs[0] if len(xs) == 1 else ("and", tuple(xs))


def link(op, a, b):
    """the clause a op b, a declaration when it is a membership of a name (as a list of clauses reads it)"""
    return ("decl", (a,), b) if op == "in" and is_name(a) else ("rel", (op,), (a, b))


def dots_chain(ops, terms):
    """a chain with \\dots, a_lo op \\dots op a_hi, as the links over the range: forall i : lo <= i < hi => a_i op
    a_(i+1); a link after (before) it with the same relation is one link with its last (first) term, any other
    relation holds for every member (e_2=\\dots=e_{k+1}=1 is e_i = 1 for 2 <= i <= k + 1; I_1<\\dots<I_k\\subseteq
    I_0 is each I_i inside I_0)"""
    js = [j for j, o in enumerate(ops) if isinstance(o, tuple)]
    if len(js) != 1:
        raise Hole("a chain with more than one \\dots")
    j, o = js[0], ops[js[0]][1]
    _, i, (_, (lo, hi)), body = fold("+", terms[j], terms[j + 1])

    def at(t):
        return subst_var(body, i, t)
    iv = ("var", i)
    out = [("forall", (iv,), None, ("imp", ("rel", ("<=", "<"), (lo, iv, hi)),
                                    ("rel", (o,), (at(iv), at(("bin", "+", iv, ("num", "1")))))))]
    every = ("rel", ("<=", "<="), (lo, iv, hi))
    for k, op in enumerate(ops):
        if k == j:
            continue
        a, b = terms[k], terms[k + 1]
        if op == o or (k not in (j - 1, j + 1)):
            out.append(("rel", (op,), (a, b)))
        elif k == j + 1:
            # 1\le W_0<W_1<\dots<W_{k+1}\in\Z: every term of the chain, those before the range too
            out.append(("forall", (iv,), None, ("imp", every, link(op, at(iv), b))))
            out += [link(op, t, b) for t in terms[:j] if t[0] != "num"]
        else:
            out.append(("forall", (iv,), None, ("imp", every, link(op, a, at(iv)))))
            out += [link(op, a, t) for t in terms[j + 2:] if t[0] != "num"]
    return conj(out)


# the operators of sets and matrices that \mathrm{name} writes: without an argument they are no term (\mathrm{rank} alone)
NEEDS_ARG = {"rank", "dim", "ker", "det", "tr", "spn", "span", "relint", "diam", "deg"}
MAPS = set()  # the maps a paper declares, in Q++ with their index as declared (\pi_\phi\colon\Z^k\to\Z^m: pi_(phi))
MAP_CLASH = set()  # the same, of the names a paper declares both as maps and as numbers


def maps_at(x, vocab=None):
    """x is a map as the paper declares it, index included (MAPS: \\pi_\\phi applied by juxtaposition, not \\sigma_i of a
    map \\sigma_\\phi), and not a number in scope"""
    return x[0] in ("var", "app") and to_qpp(x) in MAPS and name_key(x, vocab) not in SCALARS


def replace_last_factor(x, y):
    """the product x with its last factor replaced by y"""
    if x[0] == "bin" and x[1] == "*":
        return ("bin", "*", x[2], replace_last_factor(x[3], y))
    return y


def else_cases(cs):
    """the clauses cs with each else case (x:=t\\ (\\text{else}), x:=t\\ \\text{otherwise}) read as the case that the
    condition of the clause before it does not hold: e_i:=t\\ (H),\\ \\sigma_i:=u\\ (\\text{else}) is H => e_i := t,
    not(H) => sigma_i := u (a case definition). An index of the condition that the case does not use is
    bound by exists inside the negation: a_v:=b_j\\ (v=t_j),\\ a_v:=0\\ \\text{otherwise} is, for the else case,
    not(exists j : v = t_(j)) => a_(v) := 0 (no case before applies)"""
    out = []
    for c in cs:
        if c[0] == "postword":
            if not out:
                raise Hole(f"{c[1]} without a clause before it")
            out[-1] = ("attained", out[-1]) if c[1] == "attained" else ("uniform", c[2], out[-1])
            continue
        if c[0] != "else":
            out.append(c)
            continue
        prev = out[-1] if out else None
        if prev is None or prev[0] != "imp" or prev[2][0] == "imp":
            raise Hole("an else case without a condition in the clause before it")
        cond, case = prev[1], c[1]
        if case[0] == "imp":
            raise Hole("an else case with a condition of its own")
        declared = {n[1] for c in out if c[0] == "decl" for n in c[1] if n[0] == "var"} | SCALARS
        own = sorted(index_names(cond) - {y[1] for y in subterms(case) if y[0] == "var"} - declared)
        if own:
            cond = ("exists", tuple(("var", v) for v in own), None, cond)
        out.append(("imp", ("not", cond), case))
    return out


def factors(x):
    """the factors of a product, left to right"""
    if x[0] == "bin" and x[1] == "*":
        return factors(x[2]) + factors(x[3])
    return [x]


JUXT = []  # (key, declared a number) for every product of a name and a parenthesis read since the caller cleared it


def name_key(x, vocab=None):
    """the key of the scope by which a name before a parenthesis reads (as TexParser.atom keys it): t, t_ for a
    member of the family t_a or x_0, Y_pos_ for Y^+_R; primes are not part of it; None for a term that is no name"""
    if x[0] == "app" and len(x) > 3 and x[3] == "idx" and x[1][0] == "var":
        return x[1][1].rstrip("'") + "_"
    if x[0] != "var":
        return None
    v = x[1].rstrip("'")
    if v in (vocab or {}).get("#names", ()):
        return v
    m = re.fullmatch(r"(.+?)_(\d+)(star|_pos|_neg|_nought|_circ)?", v)
    if not m:
        return v
    mark = m.group(3)
    return (mark_name(m.group(1), "_star" if mark == "star" else mark) if mark else m.group(1)) + "_"


def subterms(x):
    """every node of a tree"""
    if isinstance(x, tuple) and x:
        yield x
        for y in (x[1:] if isinstance(x[0], str) else x):
            yield from subterms(y)


def index_names(x):
    """the names used as indices a_(i) in x"""
    out = set()
    for y in subterms(x):
        if y[0] == "app" and len(y) > 3 and y[3] == "idx":
            out.update(a[1] for a in y[2] if a[0] == "var")
    return out


def is_name(x):
    """a variable, an indexed variable a_i, or a family a_1,...,a_N"""
    return x[0] in ("var", "family") or (x[0] == "app" and x[3] == "idx" and x[1][0] == "var")


def names_of(x):
    """the names a noun after x declares: x itself, or the names in the chain x"""
    if is_name(x):
        return [x]
    if x[0] == "rel" and all(op in ("<=", "<", ">=", ">", "=") for op in x[1]):
        return [a for a in x[2] if is_name(a)]
    if x[0] in ("interval", "app", "bin", "setof", "tuple", "pow", "neg", "abs", "num"):
        return []  # a term: the noun is a membership claim about it
    raise Hole("a noun after a term")


VOCAB = dict(PRELUDE)  # the vocabulary of the paper being read: prelude plus the paper's rows \text{w}:=S (set by latex2qpp)


# the state a paper sets while latex2qpp reads it; latex2qpp.convert restores it afterwards, so one paper's names do
# not change how a later formula reads
PAPER_STATE = ("SCALARS", "ELSEWHERE", "SCOPED", "DATA_MODE", "MAPS", "MAP_CLASH", "JUXT", "VOCAB", "CLAUSE_APPS")


def save_paper_state():
    g = globals()
    return {n: (dict(g[n]) if isinstance(g[n], dict) else list(g[n]) if isinstance(g[n], list) else set(g[n]))
            for n in PAPER_STATE}


def restore_paper_state(saved):
    """the saved state, in the same objects (other modules hold them by reference)"""
    g = globals()
    for n, v in saved.items():
        obj = g[n]
        if isinstance(obj, list):
            obj[:] = v
        else:
            obj.clear()
            obj.update(v)


def rel_word(text):
    """the normal form of the words of a relational word: lower case, single spaces, no leading article or is"""
    w = re.sub(r"\s+", " ", text.strip().lower())
    return re.sub(r"^(?:is\s+)?(?:(?:a|an|the)\s+)?", "", w)


def textrel_pattern(tex):
    """the pattern (_, w1, _, w2, ...) of the left side of a row x w1 y w2 ... :<=> R, or None (no prose in it)"""
    toks = tex_tokens(normalize(tex))
    pat = []
    for t in toks:
        if t[0] == "text":
            w = rel_word(t[1])
            if not w:
                continue
            if pat and pat[-1] != "_":
                pat[-1] = pat[-1] + " " + w
            else:
                pat.append(w)
        elif t[0] == "cmd" and t[1] in (" ", ",", ";", "quad", "qquad"):
            continue
        elif not pat or pat[-1] != "_":
            pat.append("_")
    if not pat or pat[0] != "_" or all(w == "_" for w in pat):
        return None
    return tuple(pat)


SUB_STYLE = {"rm", "mathrm", "text", "textrm", "mathit", "operatorname"}


def spell_sub(g):
    """the spelling of a subscript group as part of a name: letters, digits and command words, the style commands
    (\\rm, \\mathrm, ...) and braces dropped: {\\rm new} is new, \\min is min; None for anything else"""
    out = []
    for t in g:
        if t[0] in ("let", "num"):
            out.append(t[1])
        elif t in (("sym", "{"), ("sym", "}")) or (t[0] == "cmd" and t[1] in SUB_STYLE):
            continue
        elif t[0] == "cmd" and re.fullmatch(r"[A-Za-z]+", t[1]):
            out.append(t[1])
        else:
            return None
    return "".join(out) or None


def name_of(tex):
    """the name that a LaTeX spelling n_y, \\kappa_{\\rm new}, s_{\\min}, \\beta_T declares in a names row, or None"""
    p = TexParser(normalize(tex))
    t = p.peek()
    if t[0] == "let":
        base = t[1]
    elif t[0] == "cmd" and t[1] in GREEK:
        base = t[1]
    else:
        return None
    p.k += 1
    while p.at("sym", "'"):
        base += "'"  # beta'_j
        p.k += 1
    if not p.at("sym", "_"):
        return None
    p.k += 1
    spelled = spell_sub(p.group())
    return f"{base}_{spelled}" if spelled and p.done() else None


def vocab_word(text, vocab):
    if text.startswith("#"):
        return None
    w = text.strip().lower()
    w = re.sub(r"^(a|an)\s+", "", w)
    if w in vocab:
        return w
    for k, v in vocab.items():
        if isinstance(v, dict) and v.get("plural") == w:
            return k
    return None


def normalize(s):
    """named slots and upright names: \\text{slot}{:=}v is the slot assignment slot := v (the alias convention)"""
    s = s.replace("{:=}", ":=")
    s = re.sub(r"\\text\{([A-Za-z]+)\}\s*:=", r"\\mathrm{\1}:=", s)
    s = re.sub(r"\\mathrm\s*([A-Za-z])(?![A-Za-z])", r"\\mathrm{\1}", s)
    s = re.sub(r"\\(mathbf|boldsymbol)\s+([A-Za-z])", r"\\\1{\2}", s)
    s = re.sub(r"\\(mathbf|boldsymbol)\s*(\\[A-Za-z]+)", r"\\\1{\2}", s)  # \boldsymbol\varsigma
    # the set \{\pm c\} of a term and its opposite: a listing {c, -c}
    s = re.sub(r"\\\{\s*\\pm\s*((?:[A-Za-z0-9]|\\[A-Za-z]+)(?:_(?:\{[^{}]*\}|[A-Za-z0-9]))?)\s*\\\}", r"\\{\1,-\1\\}", s)
    # a family x_1,\dots,x_N (or x_0, ..., x_N): one name, a range of indices
    # (primed: k'_1,\dots,k'_U or k_1',\dots,k_U', the family k')
    s = re.sub(r"(\\mathrm\{[A-Za-z]+\}|[A-Za-z]|\\[A-Za-z]+)('*)_(\d)('*),\s*(?:\\\s)*\\[lc]?dots,\s*(?:\\\s)*\1\2_(\{[^{}]*\}|[A-Za-z0-9])\4",
               lambda m: f"\\qppfam{{{m.group(1)}{m.group(2)}{m.group(4)}}}{{{m.group(3)}}}{{{m.group(5).strip('{}')}}}", s)
    # the family of a name with a numeral at its end, Q_{2,1},\dots,Q_{2,N}: the members of Q2 (texmath.member_tex)
    s = re.sub(r"([A-Za-z]|\\[A-Za-z]+)_\{(\d+),(\d)\},\s*(?:\\\s)*\\[lc]?dots,\s*(?:\\\s)*\1_\{\2,([^{}]*)\}",
               lambda m: f"\\qppfam{{{m.group(1)}_{{{m.group(2)}}}}}{{{m.group(3)}}}{{{m.group(4)}}}", s)
    s = re.sub(r"^(?:\s|\\\s|\\,|\\;|\\quad|\\qquad)+", "", s)
    s = re.sub(r"(?::|\\\s|\s)+$", "", s)
    return s


def parse_tex(s, functions=()):
    return TexParser(normalize(s), functions).whole()


def parse_tex_items(s, functions=()):
    return TexParser(normalize(s), functions).items()


# ---------------------------------------------------------------------------------------------------------
# Q++ ASCII printer and parser

PREC = {"imp": 1, "iff": 1, "rel": 2, "+": 3, "-": 3, "par": 3, "cap": 3, "cup": 3, "minus": 3, "*": 4, "/": 4, "times": 4,
        "comp": 4,
        "neg": 5, "^": 6}


BINDERS = ("sum", "prod", "max", "min", "par", "least", "union", "inter", "oplus", "comp", "famtuple")
LIST_MID = 1.25  # the precedence of a clause that is not the last of its list


def qpp_list(xs):
    """terms separated by commas; a binder that is not the last one is parenthesized (its body would seem to take
    the rest): min(0, (min h, delta_(h)), 1)"""
    return ", ".join(to_qpp(a, 1 if a[0] in BINDERS and i < len(xs) - 1 else 0) for i, a in enumerate(xs))


def to_qpp(x, p=0):
    k = x[0]
    if k == "cite":
        return "(" + to_qpp(x[1]) + ")"
    if k == "num":
        return x[1]
    if k == "var":
        return x[1]
    if k == "set":
        return x[1]
    if k == "setfrom":
        return f"{x[1]}_({x[2]} {to_qpp(x[3])})"
    if k == "hole":
        return "?{" + x[1] + "}"
    if k == "ref":
        return "@" + x[1]
    if k == "refat":
        return "@" + x[1] + "[" + qpp_list(x[2]) + "]"
    if k == "blank":
        return "dot"
    if k == "units":
        return "nonzero(" + to_qpp(x[1]) + ")"
    if k == "app":
        mark = "_" if x[3] == "idx" else ""
        return to_qpp(x[1], 9) + mark + "(" + qpp_list(x[2]) + ")"
    if k == "tuple":
        return "(" + qpp_list(x[1]) + ")"
    if k == "family":
        return f"{x[1]}_({to_qpp(x[2])}..{to_qpp(x[3])})"
    if k == "setof":
        b = x[1]
        if b[0] == "such":
            return "{" + to_qpp(b[1]) + " : " + to_qpp(b[2]) + "}"
        return "{" + to_qpp(b) + "}"
    if k == "setlist":
        return "{" + qpp_list(x[1]) + "}"
    if k == "intrange":
        return "{" + to_qpp(x[1], 3) + ".." + to_qpp(x[2], 3) + "}"
    if k == "least":
        s = f"{x[1]} {to_qpp(x[2])}"
        return f"({s})" if p > 0 else s
    if k == "polyring":
        return to_qpp(x[1], 9) + "[" + ", ".join(to_qpp(v) for v in x[2]) + "]"
    if k == "interval":
        s = "[" + to_qpp(x[1]) + ", " + to_qpp(x[2]) + "]"
        return s + ("*" + to_qpp(x[3], 6) if x[3] is not None else "")
    if k == "ivl":
        return ("(" if x[1] == "oc" else "[") + to_qpp(x[2]) + ", " + to_qpp(x[3]) + ("]" if x[1] == "oc" else ")")
    if k == "norm":
        if x[3] == "||":
            return "dnorm(" + to_qpp(x[1]) + (", " + to_qpp(x[2]) if x[2] is not None else "") + ")"
        return "|" + to_qpp(x[1]) + "|_(" + to_qpp(x[2]) + ")"
    if k == "abs":
        return "|" + to_qpp(x[1]) + "|"
    if k == "iverson":
        return "iverson(" + to_qpp(x[1]) + ")"
    if k == "prog":
        return "prog(" + to_qpp(x[1]) + ")"
    if k in ("ceil", "floor"):
        return k + "(" + to_qpp(x[1]) + ")"
    if k == "neg":
        inner = to_qpp(x[1], PREC["neg"])
        s = "-" + (f"({inner})" if inner.startswith("-") else inner)  # --t is a comment in Lean, a dash in TeX
        return f"({s})" if p > PREC["neg"] else s
    if k == "bin":
        op = x[1]
        q = PREC[op]
        s = f"{to_qpp(x[2], q)} {op} {to_qpp(x[3], q + 1)}"
        return f"({s})" if p > q else s
    if k == "pow":
        s = f"{to_qpp(x[1], 7)}^{to_qpp(x[2], 7)}"
        return f"({s})" if p > 6 else s
    if k in ("sunion", "sinter"):
        return f"{k}({to_qpp(x[1])})"
    if k == "famtuple":
        d = x[2]
        dom = (f" in {to_qpp(d[1][0], 3)}..{to_qpp(d[1][1], 3)}" if d[0] == "range" else
               {"in": " in ", "lt": " < ", "le": " <= "}[d[0]] + to_qpp(d[1], 3))
        s = f"tuple {x[1]}{dom}, {to_qpp(x[3], 4)}"
        return f"({s})" if p > 0 else s
    if k == "attained":
        s = f"{to_qpp(x[1], 2)} attained"
        return f"({s})" if p >= 2 else s
    if k == "uniform":
        s = f"{to_qpp(x[2], 2)} uniform_in({', '.join(to_qpp(n) for n in x[1])})"
        return f"({s})" if p >= 2 else s
    if k in ("sum", "prod", "max", "min", "par", "union", "inter", "oplus", "comp"):
        dom = ""
        if x[2] and x[2][0] == "range":
            dom = f" in {to_qpp(x[2][1][0], 3)}..{to_qpp(x[2][1][1], 3)}"
        elif x[2] and x[2][0] == "cond":
            dom = f" with {to_qpp(x[2][1], 2)}"
        elif x[2] and x[2][0] == "incond":
            dom = f" in {to_qpp(x[2][1], 3)} with {to_qpp(x[2][2], 2)}"
        elif x[2] and x[2][0] == "cell":
            # a sum over a cell: its range, then its clauses (a family in brackets), then its body
            b = x[2][1]
            dom = ("" if b is None else f" in {to_qpp(b[1][0], 3)}..{to_qpp(b[1][1], 3)}" if b[0] == "range"
                   else f" in {to_qpp(b[1], 3)}")
            dom += " : " + ", ".join(to_qpp(c, 1.5) for c in x[2][2])
        elif x[2]:
            dom = {"in": " in ", "lt": " < ", "le": " <= "}[x[2][0]] + to_qpp(x[2][1], 3)
        s = f"{k} {x[1]}{dom}, {to_qpp(x[3], 4)}"
        return f"({s})" if p > 0 else s
    if k == "rel":
        parts = [to_qpp(x[2][0], 3)]
        for op, t in zip(x[1], x[2][1:]):
            parts += [op, to_qpp(t, 3)]
        s = " ".join(parts)
        return f"({s})" if p > 2 else s
    if k == "def":
        # a binder that is not last in a list is parenthesized: c_0 := (sum h, a_(h)), s := 1
        return f"{to_qpp(x[1])} := {to_qpp(x[2], 1 if p == LIST_MID and x[2][0] in BINDERS else 0)}"
    if k in ("imp", "ctx"):
        a = x[1]
        # a hypothesis: a quantifier at its end is parenthesized (its body would take the arrow)
        s = f"{to_qpp(a, 0.5 if a[0] == 'and' else 1)} {'=>' if k == 'imp' else ':'} {to_qpp(x[2], 0)}"
        return f"({s})" if p >= 1 else s
    if k == "iff":
        # the right side at 2 too: a relational word there is parenthesized (x #w y binds looser than <=>)
        s = f"{to_qpp(x[1], 2)} <=> {to_qpp(x[2], 2)}"
        return f"({s})" if p > 1 else s
    if k in ("exists", "forall"):
        dom = f" in {to_qpp(x[2], 3)}" if x[2] is not None else ""
        s = f"{k} {', '.join(to_qpp(v) for v in x[1])}{dom} : {to_qpp(x[3], 0)}"
        return f"({s})" if p >= 1 else s
    if k == "defrel":
        s = f"{to_qpp(x[1], 2)} :<=> {to_qpp(x[2], 0)}"
        return f"({s})" if p >= 1 else s
    if k == "word":
        return "#" + x[1].replace(" ", "_")
    if k == "fun":
        return f"({to_qpp(x[1], 3)} -> {to_qpp(x[2], 3)})"
    if k == "decl":
        return ", ".join(to_qpp(n) for n in x[1]) + " in " + to_qpp(x[2], 3)
    if k == "and":
        cs = x[1]
        s = ", ".join(to_qpp(c, (LIST_MID if i < len(cs) - 1 else 0) if c[0] == "def" else
                             0 if (i == len(cs) - 1 and c[0] in ("exists", "forall") and p == 0) else 1)
                      for i, c in enumerate(cs))
        return f"({s})" if p >= 1 else s
    if k in ("on", "at", "near"):
        s = f"{to_qpp(x[2], 2)} {k} {to_qpp(x[1], 3)}"
        return f"({s})" if p >= 2 else s
    if k == "not":
        return "not(" + to_qpp(x[1]) + ")"
    if k == "textrel":
        out = [to_qpp(x[2][0], 3)]
        for w, a in zip(x[1], list(x[2][1:]) + [None] * len(x[1])):
            out.append("#" + w.replace(" ", "_"))
            if a is not None:
                out.append(to_qpp(a, 3))
        s = " ".join(out)
        return f"({s})" if p >= 2 else s
    if k == "or":
        s = f"{to_qpp(x[1], 2)} or {to_qpp(x[2], 2)}"
        return f"({s})" if p >= 2 else s
    raise ValueError(x)


QPP_TOK = re.compile(r"\s*(\?\{(?:[^{}]|\{(?:[^{}]|\{[^{}]*\})*\})*\}|:<=>|<=>|=>|->|<=|>=|!=|:=|(?:QQ|ZZ|NN)(?:>=\d+|>\d+)?|"
                     r"@[A-Za-z0-9:_\-]+(?:\([A-Za-z0-9]+\))?|#[A-Za-z][A-Za-z_\-]*|[A-Za-z](?:[A-Za-z0-9']|_(?=[A-Za-z0-9]))*(?:\.[A-Za-z][A-Za-z0-9']*)?|_\(|\.\.|\d+(?:\.\d+)?|[-+*/^(),;|<>=\[\]{}:])")
WORD_RELS = ("subseteq", "subset", "notin", "supseteq", "supset", "divides", "ndivides", "asymp", "sim", "simeq",
             "preceq", "succeq", "prec", "succ", "equiv")
KEYWORDS = {"sum", "prod", "par", "exists", "forall", "in", "ceil", "floor", "cap", "cup", "minus", "times", "empty", "dnorm",
            "on", "or", "with", "max", "min", "iverson", "not", "at", "near", "dot", "nonzero", "union", "inter", "sunion", "sinter", "comp", "tuple", "attained", "uniform_in", "oplus"} | set(WORD_RELS)
QPP_RELS = ("<=", ">=", "<", ">", "=", "!=", "in") + WORD_RELS


class QppParser:
    """the inverse of to_qpp"""

    def __init__(self, s):
        self.t, i = [], 0
        while i < len(s):
            m = QPP_TOK.match(s, i)
            if not m or m.end() == i:
                if s[i:].strip() == "":
                    break
                raise ValueError(f"Q++ term: cannot read {s[i:i + 20]!r}")
            self.t.append(m.group(1))
            i = m.end()
        self.k = 0

    def peek(self):
        return self.t[self.k] if self.k < len(self.t) else None

    def eat(self, v=None):
        t = self.peek()
        if v is not None and t != v:
            raise ValueError(f"Q++ term: expected {v}, got {t}")
        self.k += 1
        return t

    def whole(self):
        x = self.prop()
        if self.peek() is not None:
            raise ValueError(f"Q++ term: trailing {self.t[self.k:]}")
        return x

    def prop(self, arrows=True):
        if self.peek() in ("exists", "forall"):
            q = self.eat()
            groups = []
            while True:
                vs = [self.atom()]
                while self.peek() == ",":
                    self.eat()
                    vs.append(self.atom())
                dom = None
                if self.peek() == "in":
                    self.eat()
                    dom = self.expr()
                groups.append((tuple(vs), dom))
                if self.peek() == "," and dom is not None:
                    self.eat()
                    continue
                break
            self.eat(":")
            body = self.part()
            for vs, dom in reversed(groups):
                body = (q, vs, dom, body)
            return body
        left = self.rel()
        if self.peek() == ":<=>":
            self.eat()
            return ("defrel", left, self.part())
        if arrows and self.peek() == "=>":
            self.eat()
            return ("imp", left, self.prop())
        if self.peek() == "<=>":
            self.eat()
            return ("iff", left, self.prop())
        return left

    # statements: item := part (; part)*, part := clauses [(: | =>) part], as in the LaTeX conventions v1

    def item(self):
        parts = [self.part()]
        while self.peek() == ";":
            self.eat()
            parts.append(self.part())
        if self.peek() is not None:
            raise ValueError(f"Q++ term: trailing {self.t[self.k:]}")
        for x in parts:
            bad = prop_term(x)
            if bad is not None:
                raise ValueError(f"Q++ item: a term where a clause is expected: {to_qpp(bad)}")
        return parts

    def part(self, lenient=False):
        xs = self.clauses(lenient)
        if self.peek() in (":", "=>"):
            k = "ctx" if self.eat() == ":" else "imp"
            return (k, conj(xs), self.part())
        return conj(xs)

    def clauses(self, lenient=False):
        out, pending = [], []
        while True:
            c = self.clause()
            if is_name(c) and self.peek() == ",":
                pending.append(c)
                self.eat()
                continue
            if c[0] == "rel" and c[1] == ("in",) and is_name(c[2][0]):
                out.append(("decl", tuple(pending + [c[2][0]]), c[2][1]))
                pending = []
            else:
                if pending and not lenient:
                    raise ValueError("Q++ term: names without a declaration")
                out += pending
                pending = []
                out.append(c)
            if self.peek() == ",":
                self.eat()
                continue
            break
        if pending and not lenient:
            raise ValueError("Q++ term: names without a declaration")
        return out + pending

    def clause(self):
        x = self.prop(arrows=False)
        while self.peek() in ("on", "or", "at", "near", "attained", "uniform_in") or (self.peek() or "").startswith("#"):
            if self.peek() == "attained":
                self.eat()
                x = ("attained", x)
                continue
            if self.peek() == "uniform_in":
                self.eat()
                self.eat("(")
                ns = [self.atom()]
                while self.peek() == ",":
                    self.eat()
                    ns.append(self.atom())
                self.eat(")")
                x = ("uniform", tuple(ns), x)
                continue
            if self.peek().startswith("#"):
                # a relational word: x #w1 y1 #w2 y2 ... (an argument follows a word unless a separator does)
                words, args = [], [x]
                while (self.peek() or "").startswith("#"):
                    words.append(self.eat()[1:].replace("_", " "))
                    if self.peek() not in (None, ",", ";", ":", "=>", "<=>", ":<=>", ")", "on", "or", "at", "near") and \
                            not self.peek().startswith("#"):
                        args.append(self.expr())
                x = ("textrel", tuple(words), tuple(args))
            elif self.peek() in ("on", "at", "near"):
                x = (self.eat(), self.expr(), x)
            else:
                self.eat()
                x = ("or", x, self.prop(arrows=False))
        return x

    def rel(self):
        first = self.expr()
        if self.peek() == ":=":
            self.eat()
            if not definable(first):
                raise ValueError(f"Q++ item: a definition of {to_qpp(first)}, which is not a name")
            return ("def", first, self.expr())
        ops, terms = [], [first]
        while self.peek() in QPP_RELS:
            op = self.eat()
            ops.append(op)
            terms.append(self.expr())
        return ("rel", tuple(ops), tuple(terms)) if ops else first

    def cell_clauses(self):
        """the clauses of a cell sum up to its body: comparisons (a chain is one clause per link, read as it is) and
        families `forall j : A(j) rel B(j)` (a bounded family `forall j in NN>=1 : j <= B => A(j) rel B(j)`); the
        item after the last comma that is no clause is the body, left to the caller"""
        out = []
        while True:
            if self.peek() == "forall":
                self.eat()
                vs = [self.atom()]
                while self.peek() == ",":
                    self.eat()
                    vs.append(self.atom())
                dom = None
                if self.peek() == "in":
                    self.eat()
                    dom = self.expr()
                self.eat(":")
                body = self.rel()
                if self.peek() == "=>":
                    self.eat()
                    body = ("imp", body, self.rel())
                out.append(("forall", tuple(vs), dom, body))
                self.eat(",")
                continue
            k = self.k
            c = self.rel()
            if self.peek() == "," and isinstance(c, tuple) and (c[0] == "rel" or c[0] in ("forall", "and")):
                out.append(c)
                self.eat(",")
                continue
            self.k = k
            if not out:
                raise ValueError("Q++ term: a cell sum with no clause (a clause is a comparison by <, <=, =, >=, > or a "
                                 "family of them; no or, not, => in a clause)")
            return tuple(out)

    def expr(self):
        if self.peek() == "-":
            self.eat()
            x = ("neg", self.term())
        else:
            x = self.term()
        while self.peek() in ("+", "-", "par", "cap", "cup", "minus"):
            op = self.eat()
            x = ("bin", op, x, self.term())
        return x

    def term(self):
        x = self.unary()
        while self.peek() in ("*", "/", "times", "comp"):
            op = self.eat()
            x = ("bin", op, x, self.unary())
        return x

    def unary(self):
        if self.peek() == "-":
            self.eat()
            return ("neg", self.unary())
        return self.power()

    def power(self):
        x = self.atom()
        if self.peek() == "^":
            self.eat()
            x = ("pow", x, self.power_arg())
        return x

    def power_arg(self):
        if self.peek() == "-":
            self.eat()
            return ("neg", self.atom())
        return self.atom()

    def atom(self):
        t = self.eat()
        if t is None:
            raise ValueError("Q++ term: unexpected end")
        if t.startswith("?{"):
            return ("hole", t[2:-1])
        if t.startswith("@"):
            if self.peek() == "[":
                self.eat("[")
                args = [self.expr()]
                while self.peek() == ",":
                    self.eat()
                    args.append(self.expr())
                self.eat("]")
                return ("refat", t[1:], tuple(args))
            return ("ref", t[1:])
        if t.startswith("#"):
            return ("word", t[1:].replace("_", " "))
        if t == "not" and self.peek() == "(":
            # not(P): the negation of a proposition (LaTeX \neg(P))
            self.eat("(")
            x = self.part()
            self.eat(")")
            return ("not", x)
        if t == "prog" and self.peek() == "(":
            # prog(DECLS, ROWS : COST): a linear program in its scales, stated by the atom prog(...) = P with P a pair
            #; the scales and rows read as a context, the cost after the colon
            self.eat("(")
            x = self.part(lenient=True)
            self.eat(")")
            if x[0] != "ctx":
                raise ValueError("Q++ term: prog(DECLS, ROWS : COST), the cost after a colon")
            return ("prog", x)
        if t == "iverson" and self.peek() == "(":
            # iverson(P): 1 if P holds, else 0 (LaTeX \mathbf 1[P])
            self.eat("(")
            x = self.part(lenient=True)
            self.eat(")")
            return ("iverson", x)
        if t == "(":
            x = self.part(lenient=True)
            if DATA_MODE[0] and x[0] == "rel" and self.peek() == ")":
                self.eat(")")
                return ("cite", x)  # a hypothesis cited by its content
            if self.peek() == "->":
                self.eat()
                x = ("fun", x, self.expr())
            if self.peek() == "]" and x[0] == "and" and len(x[1]) == 2 and not any(is_prop(c) for c in x[1]):
                self.eat()
                return ("ivl", "oc", x[1][0], x[1][1])
            self.eat(")")
            if x[0] == "and" and not any(is_prop(c) for c in x[1]):
                return ("tuple", x[1])
            if self.peek() == "(" and (x[0] == "comp" or x[:2] == ("bin", "comp")):
                # (g_(L) comp g_(1))(y): a composition applied
                self.eat("(")
                args = [self.expr()]
                while self.peek() == ",":
                    self.eat()
                    args.append(self.expr())
                self.eat(")")
                return ("app", x, tuple(args), "call")
            return x
        if t == "|":
            x = self.expr()
            self.eat("|")
            if self.peek() == "_(":
                self.eat()
                sub = self.expr()
                self.eat(")")
                return ("norm", x, sub, "|")
            return ("abs", x)
        if t == "dnorm":
            self.eat("(")
            x = self.expr()
            sub = None
            if self.peek() == ",":
                self.eat()
                sub = self.expr()
            self.eat(")")
            return ("norm", x, sub, "||")
        if t == "empty":
            return ("set", "empty")
        if t == "dot":
            return ("blank",)
        if t == "nonzero" and self.peek() == "(":
            self.eat("(")
            x = self.expr()
            self.eat(")")
            return ("units", x)
        if t == "{":
            b = self.prop()
            if self.peek() == ":":
                self.eat()
                b = ("such", b, self.part(lenient=True))
            elif self.peek() == "..":
                self.eat()
                hi = self.expr()
                self.eat("}")
                return ("intrange", b, hi)
            elif self.peek() == ",":
                elems = [b]
                while self.peek() == ",":
                    self.eat()
                    elems.append(self.expr())
                self.eat("}")
                return ("setlist", tuple(elems))
            self.eat("}")
            return ("setof", b)
        if t == "[":
            a = self.expr()
            self.eat(",")
            b = self.expr()
            if self.peek() == ")":
                self.eat()
                return ("ivl", "co", a, b)
            self.eat("]")
            scale = None
            if self.peek() == "*":
                self.eat()
                scale = self.power()
            return ("interval", a, b, scale)
        if t in ("ceil", "floor"):
            self.eat("(")
            x = self.expr()
            self.eat(")")
            return (t, x)
        if t in ("max", "min") and self.peek() == "{":
            return ("least", t, self.atom())
        if t in ("max", "min") and self.peek() == "(":
            # min(K, L): the call, as \\min(K,L) reads
            self.eat()
            args = [self.expr()]
            while self.peek() == ",":
                self.eat()
                args.append(self.expr())
            self.eat(")")
            return ("app", ("var", t), tuple(args), "call")
        if t == "tuple":
            v = self.eat()
            op = self.eat()
            b = self.expr()
            if op == "in" and self.peek() == "..":
                self.eat()
                dom = ("range", (b, self.expr()))
            else:
                dom = ({"in": "in", "<": "lt", "<=": "le"}[op], b)
            self.eat(",")
            return ("famtuple", v, dom, self.term())
        if t in ("sunion", "sinter") and self.peek() == "(":
            self.eat("(")
            x = self.expr()
            self.eat(")")
            return (t, x)
        if t in ("sum", "prod", "par", "union", "inter", "oplus", "comp") or t in ("max", "min"):
            v = self.eat()
            dom = None
            if self.peek() in ("in", "<", "<="):
                op = self.eat()
                b = self.expr()
                if op == "in" and self.peek() == "..":
                    self.eat()
                    dom = ("range", (b, self.expr()))
                elif op == "in" and self.peek() == "with":
                    self.eat()
                    dom = ("incond", b, self.rel())
                else:
                    dom = ({"in": "in", "<": "lt", "<=": "le"}[op], b)
            elif self.peek() == "with":
                self.eat()
                dom = ("cond", self.rel())
            if t == "sum" and self.peek() == ":" and (dom is None or dom[0] in ("range", "in")):
                # a sum over a cell: the points of the range (an index range, the coordinates, the lattice) at which
                # every clause holds, `sum u : C_1, ..., C_J, t`; each item before the last is a clause
                self.eat()
                return ("sum", v, ("cell", dom, self.cell_clauses()), self.term())
            self.eat(",")
            return (t, v, dom, self.term())
        if re.fullmatch(r"\d+(?:\.\d+)?", t):
            return ("num", t)
        if re.fullmatch(r"(QQ|ZZ|NN)", t) and self.peek() == "_(":
            # ZZ_(>= M_0): the members from a bound that is a term
            self.eat()
            op = self.eat()
            if op not in (">=", ">"):
                raise ValueError(f"Q++ term: a set from a bound with {op}")
            b = self.expr()
            self.eat(")")
            return ("setfrom", t, op, b)
        if re.fullmatch(r"(QQ|ZZ|NN)(>=\d+|>\d+)?", t):
            x = ("set", t)
            while self.peek() == "[":
                self.eat()
                vs = [self.expr()]
                while self.peek() == ",":
                    self.eat()
                    vs.append(self.expr())
                self.eat("]")
                x = ("polyring", x, tuple(vs))
            return x
        if re.fullmatch(r"[A-Za-z][A-Za-z0-9_']*(?:\.[A-Za-z][A-Za-z0-9']*)?", t) and t not in KEYWORDS:
            # a name; Pr.P is the part P of the bundle Pr (a type row {P, N in X, ...}), read as one name
            x = ("var", t)
            if self.peek() in ("(", "_("):
                kind = "idx" if self.eat() == "_(" else "call"
                first = self.expr()
                if kind == "idx" and self.peek() == "..":
                    self.eat()
                    hi = self.expr()
                    self.eat(")")
                    return ("family", t, first, hi)
                args = [first]
                while self.peek() == ",":
                    self.eat()
                    args.append(self.expr())
                self.eat(")")
                x = ("app", x, tuple(args), kind)
                if kind == "idx" and len(args) == 1 and self.peek() == "_(":
                    # a_(j)_(i): the coordinate i of the member a_(j) of a family of tuples (one level)
                    self.eat()
                    x = ("app", x, (self.expr(),), "idx")
                    self.eat(")")
                if kind == "call" and self.peek() == "(":
                    # deriv(g, y, l)(p, y): a function-valued term, applied (Q++ writes products with *)
                    self.eat()
                    args = [self.expr()]
                    while self.peek() == ",":
                        self.eat()
                        args.append(self.expr())
                    self.eat(")")
                    x = ("app", x, tuple(args), "call")
                if kind == "idx" and self.peek() == "(":
                    # f_(theta_star)(b_x): a member of a family of functions, applied (Q++ writes products with *)
                    self.eat()
                    args = [self.expr()]
                    while self.peek() == ",":
                        self.eat()
                        args.append(self.expr())
                    self.eat(")")
                    x = ("app", x, tuple(args), "call")
                if x[3] == "call" and self.peek() == "_(":
                    # F(u)_(j), idmod(n, N)(u)_(j): the coordinate j of a tuple-valued function at a point
                    self.eat()
                    x = ("app", x, (self.expr(),), "idx")
                    self.eat(")")
            return x
        raise ValueError(f"Q++ term: unexpected {t!r}")


def parse_qpp(s):
    return QppParser(s).whole()


def parse_qpp_item(s):
    """a statement item: its parts (separated by ;)"""
    return QppParser(s).item()


def is_prop(x):
    return x[0] in ("rel", "imp", "ctx", "iff", "exists", "forall", "and", "or", "on", "decl", "def", "defrel", "not",
                    "at", "near", "attained", "uniform")


PROP_LEAVES = ("rel", "decl", "def", "defrel", "textrel", "ref", "refat", "hole")
# the names whose application is a clause: the contexts of the modules (`context coef(...)`, a relation that is a
# parameter), set by the generator and the printers from the vocabulary lines (`% qpp: relations ...` in the LaTeX)
CLAUSE_APPS = set()


def prop_term(x):
    """the first part of the clause x that is a term where a proposition is expected (a bare value, a product, an
    application: (p = 2 => 3/2, 1), l = 1, 2, rho(0) alone), or None"""
    k = x[0]
    if k == "app" and x[1][0] == "var" and x[1][1] in CLAUSE_APPS:
        return None
    if k in ("imp", "ctx", "or", "iff"):
        return prop_term(x[1]) or prop_term(x[2])
    if k == "and":
        return next((y for y in map(prop_term, x[1]) if y is not None), None)
    if k in ("exists", "forall"):
        return prop_term(x[3])
    if k in ("on", "at", "near"):
        return prop_term(x[2])
    if k in ("not", "else", "attained", "postword"):
        return prop_term(x[1]) if k != "postword" else None
    if k == "uniform":
        return prop_term(x[2])
    return None if k in PROP_LEAVES else x


def parse_qpp_list(s):
    """a list of Q++ terms separated by top-level commas (binders consume their own comma)"""
    p = QppParser(s)
    out = [p.prop()]
    while p.peek() == ",":
        p.eat()
        out.append(p.prop())
    if p.peek() is not None:
        raise ValueError(f"Q++ term: trailing {p.t[p.k:]}")
    return out


# The keys of a row decide two things, each by one predicate below that every reader calls:
#   key                                   printed   read
#   (1), (2a), words                      yes       under the given of its item
#   core N, coreN (digits)                yes       alone (is_core)
#   core, core NAME (a letter first)      no        alone (is_core, checks_only)
CORE_KEY = re.compile(r"core(?:\s*\d+|\s+[A-Za-z][A-Za-z0-9]*)?")
CHECKS_KEY = re.compile(r"core(?:\s+[A-Za-z][A-Za-z0-9]*)?")


def is_core(key):
    """a core item (key core, core0, core 1, core NAME): it declares every name it uses before its colon, so it stands
    alone, without the given of its result (the paper's context rows and the result's operator definitions still
    apply)"""
    return bool(key) and CORE_KEY.fullmatch(key.strip()) is not None


def checks_only(key):
    """a row or a proof line that only the checks read, left out of the article: the key core or core NAME (a core
    item with digits, core 1, is printed). Such a row is printed where a printed proof cites it (qpp2latex.cited_cores),
    its proof lines never"""
    return bool(key) and CHECKS_KEY.fullmatch(key.strip()) is not None


def is_claim(x):
    """a proposition (a relation, an implication, a quantifier) rather than a certificate"""
    return x[0] in ("rel", "imp", "iff", "exists", "forall")


# ---------------------------------------------------------------------------------------------------------
# Lean printer

def lean_name(v):
    m = re.fullmatch(r"b_([A-Za-z])_(.+)", v)
    if m:
        return lean_name(m.group(1) + "_" + m.group(2))
    base, _, rest = v.partition("_")
    prime = ""
    while base.endswith("'"):
        base, prime = base[:-1], prime + "'"
    while rest.endswith("'"):
        rest, prime = rest[:-1], prime + "'"
    b = GREEK_LEAN.get(base, base)
    if base.startswith("b") and len(base) == 1 and rest and len(rest) == 1 and rest.isalpha():
        return rest + prime  # bold vector b_w
    if base == "b" and rest in GREEK:
        return GREEK_LEAN[rest] + prime  # bold Greek vector b_varsigma
    if not rest:
        return b + prime
    if rest.isdigit():
        return b + rest.translate(SUB_DIGITS) + prime
    return b + "_" + rest + prime


LEAN_SETS = {"QQ": "\u211a", "ZZ": "\u2124", "NN": "\u2115"}


LEAN_NAMES = {}  # Q++ name -> Lean name, for the statement in scope (set by qpp2lean)
LEAN_INT = set()  # the names of type Z in scope (an integer bound of a sum over N-indexed terms is read by toNat)
LEAN_FAMS = {}  # Q++ name -> (lo, hi): the index range of a family a_lo,...,a_hi in scope
LEAN_ITYP = {}  # Q++ name -> the index type of a family in scope (N, or Z for a family over a set of integers)
LEAN_VECS = {}  # x -> (Lean name, dimension): the vectors b_x in scope, whose components are x_(i)
LEAN_FIN = {}  # i -> dimension d: the indices in scope that run over Fin d (the value of i is i + 1)
LEAN_POLY = set()  # the names in scope that are polynomials in one variable (S in Q[y]: S(t) is S.eval t)
LEAN_RAT = set()  # the names in scope whose values are rational (a scalar, a family a[], a vector b_x, a map F)
LEAN_CLASSICAL = [False]  # a term printed since the caller cleared it needs classical decidability (a filter by a set)
LEAN_PVAR = {}  # the polynomials in scope: name -> (their formal variable, their Lean type)
LEAN_MATS = set()  # the matrices in scope (G in Q^{m x n})


def lin_kind(x):
    """the kind of a term of linear algebra: "mat" (a declared matrix, its transpose or inverse, a product of
    matrices), "vec" (a declared vector, a matrix times a vector), "covec" (a vector transposed, times a matrix), or
    None (a number, or anything else)"""
    k = x[0]
    if k == "var":
        return "mat" if x[1] in LEAN_MATS else "vec" if x[1].startswith("b_") and x[1][2:] in LEAN_VECS else None
    if k == "pow" and x[2] == ("neg", ("num", "1")):
        return "mat" if lin_kind(x[1]) == "mat" else None
    if k == "app" and x[1] == ("var", "transpose") and len(x[2]) == 1:
        inner = lin_kind(x[2][0])
        return {"mat": "mat", "vec": "covec"}.get(inner)
    if k == "bin" and x[1] == "*":
        a, b = lin_kind(x[2]), lin_kind(x[3])
        return {("mat", "mat"): "mat", ("mat", "vec"): "vec", ("covec", "mat"): "covec", ("covec", "vec"): None,
                (None, "vec"): "vec", (None, "mat"): "mat"}.get((a, b))
    return None


def lin_lean(x):
    """a term of linear algebra in Lean (Mathlib's Matrix): products by *v (matrix times vector), v* (vector times
    matrix), dot (a row times a column, a number), transpose and inverse; None if x is no such term"""
    k = x[0]
    if k == "app" and x[1] == ("var", "transpose") and len(x[2]) == 1 and lin_kind(x[2][0]) in ("mat", "vec"):
        inner = lin_lean(x[2][0]) or to_lean(x[2][0], 9)
        return inner if lin_kind(x[2][0]) == "vec" else f"(Matrix.transpose {inner})"
    if k == "bin" and x[1] == "*":
        a, b = lin_kind(x[2]), lin_kind(x[3])
        if a is None and b is None:
            return None
        la = lin_lean(x[2]) or to_lean(x[2], 9)
        lb = lin_lean(x[3]) or to_lean(x[3], 9)
        if (a, b) == ("mat", "mat"):
            return f"({la} * {lb})"
        if (a, b) == ("mat", "vec"):
            return f"(Matrix.mulVec {la} {lb})"
        if (a, b) == ("covec", "mat"):
            return f"(Matrix.vecMul {la} {lb})"
        if (a, b) == ("covec", "vec"):
            return f"(\u2211 \u03b9, {la} \u03b9 * {lb} \u03b9)"  # a row times a column: a number
        if a is None and b in ("vec", "mat"):
            return f"({la} \u2022 {lb})"
        raise Hole(f"{to_qpp(x)}: a product of linear algebra of no type")
    return None
POLY_OPS = {"deg", "lc", "Res", "disc"}  # the operators with the variable below: deg_y S, lc_y(S), Res_y(S, T)


def poly_lean(x):
    """a polynomial term in Lean: a declared polynomial, or deriv(g, y, k) of one: (Lean term, its type), or None"""
    if x[0] == "var" and x[1] in LEAN_PVAR:
        return LEAN_NAMES.get(x[1]) or lean_name(x[1]), LEAN_PVAR[x[1]][1]
    if x[0] == "app" and x[1] == ("var", "deriv") and x[3] == "call" and len(x[2]) in (2, 3):
        g, y = x[2][0], x[2][1]
        if g[0] != "var" or g[1] not in LEAN_PVAR or LEAN_PVAR[g[1]][0] != to_qpp(y):
            raise Hole(f"{to_qpp(x)}: a derivative of a term that is not a declared polynomial in {to_qpp(y)}")
        gl = LEAN_NAMES.get(g[1]) or lean_name(g[1])
        if len(x[2]) == 2:
            return f"(Polynomial.derivative {gl})", LEAN_PVAR[g[1]][1]
        if not nat_term(x[2][2]):
            raise Hole(f"{to_qpp(x)}: a derivative of an order that is not a natural number")
        return f"(Polynomial.derivative^[{to_lean(x[2][2])}] {gl})", LEAN_PVAR[g[1]][1]
    if x[0] == "app" and x[3] == "call" and x[1][0] == "var" and x[1][1] in LEAN_PVAR and len(x[2]) == 2 \
            and x[2][1][0] == "blank" and LEAN_PVAR[x[1][1]][1].startswith("Polynomial (MvPolynomial"):
        # g(p, dot): the polynomial in y with its coefficients at p
        gl = LEAN_NAMES.get(x[1][1]) or lean_name(x[1][1])
        return f"(Polynomial.map (MvPolynomial.eval {to_lean(x[2][0], 9)}) {gl})", "Polynomial \u211a"
    return None


def poly_term(x):
    """deg_y S, lc_y(S), Res_y(S, T) for declared polynomials in y (Mathlib: natDegree, leadingCoeff, resultant, whose
    Sylvester matrix has another order of rows and columns than the paper's, so the resultant is the paper's up to
    sign); a polynomial at a point: S(t) for S in Q[y], S(p, y) for S in Q[w][y] (the coefficients at p, then the value
    at y), S(p, dot) the polynomial in y with its coefficients at p; None for any other term"""
    head, args = x[1], x[2]
    if head[0] == "app" and head[3] == "idx" and head[1][0] == "var" and head[1][1] in POLY_OPS and len(head[2]) == 1:
        op, y = head[1][1], to_qpp(head[2][0])
        ps = [poly_lean(a) for a in args]
        if any(p is None for p in ps) or any(a[0] == "var" and LEAN_PVAR[a[1]][0] != y for a in args):
            raise Hole(f"{to_qpp(x)}: {op}_{y} of a term that is not a declared polynomial in {y}")
        if op == "deg" and len(ps) == 1:
            return f"{ps[0][0]}.natDegree"
        if op == "lc" and len(ps) == 1:
            return f"{ps[0][0]}.leadingCoeff"
        if op == "Res" and len(ps) == 2:
            return f"Polynomial.resultant {ps[0][0]} {ps[1][0]}"
        raise Hole(f"{to_qpp(x)}: no Lean reading of {op}_{y} yet")
    p = poly_lean(head)
    if p is None:
        return None
    s, typ = p
    if typ.startswith("Polynomial \u211a") and len(args) == 1 and args[0][0] != "blank":
        return f"{s}.eval {to_lean(args[0], 9)}"
    if typ.startswith("Polynomial (MvPolynomial") and len(args) == 2:
        pt = to_lean(args[0], 9)
        if args[1][0] == "blank":
            return f"Polynomial.map (MvPolynomial.eval {pt}) {s}"
        return f"Polynomial.eval\u2082 (MvPolynomial.eval {pt}) {to_lean(args[1], 9)} {s}"
    raise Hole(f"{to_qpp(x)}: a polynomial of type {typ} at {len(args)} arguments")


def rational_free(x):
    """no rational name in the term x: Lean would read its division in N or Z (n / 2 truncates), or its power with an
    integer exponent in a type without zpow; Q++'s division is the semifield's, so such a term is printed in Q"""
    for y in subterms(x):
        if y[0] in ("leanraw", "cite"):
            return False  # the data of a word (a hypothesis): left to Lean
        if y[0] == "var" and y[1] in LEAN_RAT:
            return False
        if y[0] == "app" and y[1][0] == "var" and (y[1][1] + "[]" in LEAN_RAT or "b_" + y[1][1] in LEAN_RAT
                                                  or y[1][1] in LEAN_RAT):
            return False
    return True


def _fact(x):
    a = x[2][0]
    if len(x[2]) != 1 or not nat_term(a):
        raise Hole(f"{to_qpp(x)}: a factorial of a term that is not a natural number")
    return f"(Nat.factorial {to_lean(a, 9)} : \u211a)"


def _dist(x):
    # the distance of a number to an interval: max(a - x, x - b, 0)
    if len(x[2]) != 2 or x[2][1][0] != "interval" or x[2][1][3] is not None:
        raise Hole(f"{to_qpp(x)}: a distance to a set that is not a closed interval")
    t, iv = to_lean(x[2][0], 9), x[2][1]
    return f"max (max ({to_lean(iv[1])} - {t}) ({t} - {to_lean(iv[2])})) 0"


def _interior(x):
    # the interior of a closed interval [a, b] (of numbers, or of vectors: every component strict), no topology
    s = x[2][0]
    if s[0] == "interval" and s[3] is None:
        return f"Set.Ioo {to_lean(s[1], 9)} {to_lean(s[2], 9)}"
    raise Hole(f"{to_qpp(x)}: the interior of a set that is not written as a closed interval (a box binds it)")


def _tensor(x):
    # v^{tensor d}: the vector of the degree-d monomials of v, indexed by the maps Fin d -> Fin n
    v, d = x[2]
    if v[0] != "var" or not v[1].startswith("b_") or v[1][2:] not in LEAN_VECS:
        raise Hole(f"{to_qpp(x)}: a tensor power of a term that is not a declared vector")
    vl, n = LEAN_VECS[v[1][2:]]
    return f"(fun \u03c6 : Fin {to_lean(d, 9)} \u2192 Fin {n} => \u220f j, {vl} (\u03c6 j))"


def _dim(x):
    # the dimension of a set of vectors: of its affine hull (the vector span of its differences)
    return f"Module.finrank \u211a (vectorSpan \u211a {to_lean(x[2][0], 9)})"


def _ker(x):
    # the kernel of a map: the points it sends to 0
    return f"{{v | {to_lean(x[2][0], 9)} v = 0}}"


def _powerset(x):
    return f"\U0001d4ab {to_lean(x[2][0], 9)}"


def _no_reading(what):
    def f(x):
        raise Hole(f"{to_qpp(x)}: {what}")
    return f


BUILTIN_LEAN = {"fact": _fact, "dist": _dist, "interior": _interior, "tensor": _tensor, "dim": _dim, "ker": _ker,
                "powerset": _powerset,
                "restrict": _no_reading("a restriction as a term (h|_F = 0 is h = 0 on F)"),
                "int": _no_reading("an integral (bound to the paper's library by a binding; none yet)"),
                "rank": _no_reading("a rank (no Lean reading yet)"), "relint": _no_reading("no Lean reading yet"),
                "diam": _no_reading("no Lean reading yet"), "spn": _no_reading("a span (no Lean reading yet)"),
                "tr": _no_reading("a trace of a term that is not a declared matrix"),
                "jac": _no_reading("the differential of a map (formal partial derivatives at a point, no Lean "
                                   "reading yet)")}


def rational_exponent(e):
    """the exponent e is a rational term: a rational name in its arithmetic (not inside the arguments of an
    application, whose value has the type of the function, nor inside a floor or a ceiling, which are integers)"""
    if not isinstance(e, tuple) or not e:
        return False
    if e[0] == "var":
        return e[1] in LEAN_RAT and e[1] not in LEAN_INT and e[1] not in LEAN_FIN
    if e[0] == "app" and e[1][0] == "var":
        # a value of a function or a term of a family: rational when the function (family) takes rational values
        return e[1][1] in LEAN_RAT or e[1][1] + "[]" in LEAN_RAT
    if e[0] in ("floor", "ceil", "app"):
        return False
    if e[0] == "bin" and e[1] == "/":
        return True
    return any(rational_exponent(y) for y in e[1:] if isinstance(y, tuple))


def nat_term(a):
    """a term of N whose value is the same in N as in Q: names and families of naturals, numerals, sums, products and
    powers with natural exponents (no minus, division, floor, ceiling, integer or rational name)"""
    for y in subterms(a):
        if y[0] in ("neg", "floor", "ceil", "leanraw", "cite", "hole") or (y[0] == "bin" and y[1] in ("-", "/")):
            return False
        if y[0] == "num" and not y[1].isdigit():
            return False
        if y[0] == "var" and (y[1] in LEAN_INT or y[1] in LEAN_RAT or y[1] in LEAN_POLY):
            return False
        if y[0] == "app" and y[1][0] == "var" and (y[1][1] + "[]" in LEAN_RAT or "b_" + y[1][1] in LEAN_RAT
                                                  or y[1][1] in LEAN_RAT or y[1][1] in LEAN_INT):
            return False
        if y[0] not in ("var", "num", "bin", "pow", "app") and not isinstance(y[0], tuple):
            return False
    return True


def int_exponent(e):
    """an exponent that may be negative (zpow): a minus, a difference, a floor, a ceiling or a name of type Z in it"""
    for y in subterms(e):
        if y[0] in ("neg", "floor", "ceil") or (y[0] == "bin" and y[1] == "-") or (y[0] == "var" and y[1] in LEAN_INT):
            return True
    return False


def vector_index_dim(body, v):
    """the dimension of a vector in scope whose component body indexes by the variable v, or None"""
    if isinstance(body, tuple) and body:
        if body[0] == "app" and body[3] == "idx" and body[1][0] == "var" and body[2] == (("var", v),) \
                and body[1][1] in LEAN_VECS:
            return LEAN_VECS[body[1][1]][1]
        for y in (body[1:] if isinstance(body[0], str) else body):
            if isinstance(y, tuple):
                r = vector_index_dim(y, v)
                if r:
                    return r
    return None


def family_of(body, v):
    """the range of a family in scope indexed by the variable v in body"""
    if isinstance(body, tuple) and body:
        if body[0] == "app" and body[3] == "idx" and body[1][0] == "var" and ("var", v) in body[2]:
            if body[1][1] in LEAN_FAMS:
                return LEAN_FAMS[body[1][1]]
        for y in (body[1:] if isinstance(body[0], str) else body):
            if isinstance(y, tuple):
                r = family_of(y, v)
                if r:
                    return r
    return None


def nat_index(a, fam):
    """the index a of the family fam in Lean: a count, so an integer index (a name of type Z, or a term in one) is
    read through toNat, unless the family is indexed by integers (a family over a set of integers)"""
    s = to_lean(a, 9)
    ints = {v for v in var_names(a) if v in LEAN_INT and v not in LEAN_FIN}
    if not ints or LEAN_ITYP.get(fam) == "\u2124":
        return s
    return f"{s}.toNat" if a[0] == "var" else f"({to_lean(a)}).toNat"


def var_names(x):
    return {y[1] for y in subterms(x) if y[0] == "var"}


def to_lean(x, p=0):
    k = x[0]
    if k == "leanraw":
        return x[1]  # a Lean name the generator resolved (a hypothesis cited by its content)
    if k == "cite":
        raise Hole(f"the citation ({to_qpp(x[1])}) outside the data of a word")
    if k == "num":
        return x[1]
    if k == "var" and x[1] == "b_zero":
        return "0"  # the zero vector (its type from the other side)
    if k == "var":
        if x[1] in LEAN_FIN:
            # an index over Fin d: its value is i + 1 (components are numbered from 1)
            return f"(({LEAN_NAMES.get(x[1]) or lean_name(x[1])} : \u2115) + 1)"
        return LEAN_NAMES.get(x[1]) or lean_name(x[1])
    if k == "set":
        return "\u2205" if x[1] == "empty" else LEAN_SETS.get(x[1], x[1])
    if k == "hole":
        raise Hole(x[1])
    if k in ("ref", "refat"):
        raise Hole(f"reference {x[1]} as a hypothesis (the referenced condition as a predicate with its free names is "
                   "not generated yet)")
    if k == "app" and x[1] == ("var", "lg"):
        raise Hole("lg outside a ceiling or a floor (not rational)")
    if k == "app" and x[1] == ("var", "card") and len(x[2]) == 1:
        s = f"Set.ncard {to_lean(x[2][0], 9)}"
        return f"({s})" if p >= 9 else s
    if k == "app" and x[1] in (("var", "min"), ("var", "max")) and x[3] == "call" and len(x[2]) >= 2:
        # min(K, L, M) is min (min K L) M: Lean's min and max take two arguments
        s = to_lean(x[2][0], 9)
        for j, a in enumerate(x[2][1:], 2):
            s = f"{x[1][1]} {s} {to_lean(a, 9)}"
            s = f"({s})" if j < len(x[2]) else s
        return f"({s})" if p >= 9 else s
    if k == "app" and x[3] == "call" and (x[1][0] != "var" or x[1][1] in LEAN_PVAR or x[1][1] == "deriv"):
        r = poly_term(x)
        if r is not None:
            return f"({r})" if p >= 9 else r
    if k == "app" and x[1] == ("var", "deriv"):
        r = poly_lean(x)
        return r[0]
    if k == "app" and x[3] == "call" and x[1] in (("var", "det"), ("var", "tr")) and len(x[2]) == 1 \
            and lin_kind(x[2][0]) == "mat":
        m = lin_lean(x[2][0]) or to_lean(x[2][0], 9)
        s = f"{m}.{'det' if x[1][1] == 'det' else 'trace'}"
        return f"({s})" if p >= 9 else s
    if (k == "app" and x[1] == ("var", "transpose")) or (k == "bin" and x[1] == "*" and (lin_kind(x[2]) or lin_kind(x[3]))):
        r = lin_lean(x)
        if r is not None:
            return r
    if k == "app" and x[3] == "call" and x[1][0] == "var" and x[1][1] in BUILTIN_LEAN:
        s = BUILTIN_LEAN[x[1][1]](x)
        return f"({s})" if p >= 9 and " " in s and not s.startswith("(") else s
    if k == "famtuple":
        raise Hole("a tuple of values over a set (no Lean form yet)")
    if k == "blank":
        raise Hole("a blank argument (dot) outside the arguments of a polynomial")
    if k == "units":
        raise Hole("the set of nonzero elements in a formula")
    if k == "app" and x[3] == "call" and x[1][0] == "var" and x[1][1] in LEAN_POLY and len(x[2]) == 1:
        # S(t) for a polynomial S in one variable: its value at t
        s = f"{to_lean(x[1], 9)}.eval {to_lean(x[2][0], 9)}"
        return f"({s})" if p >= 9 else s
    if k == "app" and x[1] == ("var", "deg") and len(x[2]) == 1 and x[2][0][0] == "var" and x[2][0][1] in LEAN_POLY:
        # deg S: the degree of a polynomial in one variable, a natural number (deg 0 = 0 in Lean's natDegree)
        s = f"{to_lean(x[2][0], 9)}.natDegree"
        return f"({s})" if p >= 9 else s
    if k == "app" and x[1] == ("var", "choose") and x[3] == "call" and len(x[2]) == 2:
        # \binom pi: Nat.choose of two naturals, a rational as the papers' terms
        if not all(nat_term(a) for a in x[2]):
            raise Hole(f"{to_qpp(x)}: a binomial coefficient of a term that is not a natural number")
        return f"(Nat.choose {to_lean(x[2][0], 9)} {to_lean(x[2][1], 9)} : \u211a)"
    if k == "app" and x[1] == ("var", "deg"):
        raise Hole(f"{to_qpp(x)}: a degree of a term that is not a polynomial in one variable (no Lean term yet)")
    if k == "app":
        f = to_lean(x[1], 9)
        if x[3] == "idx" and x[1][0] == "var" and x[1][1] in LEAN_VECS:
            # the component x_(i) of the vector b_x: i runs over Fin d
            vl, d = LEAN_VECS[x[1][1]]
            a = x[2][0] if len(x[2]) == 1 else None
            if a is None or a[0] != "var" or LEAN_FIN.get(a[1]) != d:
                raise Hole(f"the component {to_qpp(x)} of a vector at an index that does not run over its dimension")
            s = f"{vl} {LEAN_NAMES.get(a[1]) or lean_name(a[1])}"
            return f"({s})" if p >= 9 else s
        if x[3] == "idx" and x[1][0] == "var":
            f = LEAN_NAMES.get(x[1][1] + "[]") or lean_name(x[1][1])
            s = f + " " + " ".join(nat_index(a, x[1][1]) for a in x[2])
            return f"({s})" if p >= 9 else s
        s = f + " " + " ".join(to_lean(a, 9) for a in x[2])
        return f"({s})" if p >= 9 else s
    if k == "tuple":
        return "(" + ", ".join(to_lean(a) for a in x[1]) + ")"
    if k == "abs":
        return "|" + to_lean(x[1]) + "|"
    if k == "iverson":
        return f"(if {to_lean(x[1])} then (1 : \u211a) else 0)"  # an indicator is rational, as the papers' terms
    if k in ("ceil", "floor") and x[1][0] == "app" and x[1][1] == ("var", "lg") and len(x[1][2]) == 1:
        # the ceiling (floor) of lg t, t a natural number >= 1: the integer Nat.clog 2 t (Nat.log 2 t)
        a = x[1][2][0]
        if a[0] not in ("var", "num"):
            if nat_term(a):
                # a term of N (n_y + 1): Nat.clog 2 t (Nat.log 2 t), as for a name
                return f"(Nat.{'clog' if k == 'ceil' else 'log'} 2 {to_lean(a, 9)} : \u2124)"
            # a term of Q (kappa/rho, 8M/(c c')): Int.clog 2 t is the least k with t <= 2^k, Int.log 2 t the
            # greatest k with 2^k <= t, for t > 0 (both are 0 at t <= 0, where lg is not defined)
            return f"(Int.{'clog' if k == 'ceil' else 'log'} 2 ({to_lean(a)} : \u211a))"
        t = to_lean(a, 9) + (".toNat" if a[0] == "var" and a[1] in LEAN_INT else "")
        return f"(Nat.{'clog' if k == 'ceil' else 'log'} 2 {t} : \u2124)"
    if k in ("ceil", "floor"):
        # Int.floor (Int.ceil) of the rational t: t is read in Q, so kq/p is a quotient of rationals and not an
        # integer division, and a negative t keeps its sign (Nat.floor would give 0)
        t = to_lean(x[1])
        t = t if t.endswith(" : \u211a)") and t.startswith("(") else f"({t} : \u211a)"
        return ("\u2308" if k == "ceil" else "\u230a") + t + ("\u2309" if k == "ceil" else "\u230b")
    if k == "neg":
        inner = to_lean(x[1], PREC["neg"])
        s = "-" + (f"({inner})" if inner.startswith("-") else inner)  # --t is a comment in Lean, a dash in TeX
        return f"({s})" if p > PREC["neg"] else s
    if k == "interval" and x[3] is None:
        s = f"Set.Icc {to_lean(x[1], 9)} {to_lean(x[2], 9)}"
        return f"({s})" if p > 0 else s
    if k == "ivl":
        s = f"Set.{'Ioc' if x[1] == 'oc' else 'Ico'} {to_lean(x[2], 9)} {to_lean(x[3], 9)}"
        return f"({s})" if p > 0 else s
    if k == "intrange":
        s = f"Set.Icc {to_lean(x[1], 9)} {to_lean(x[2], 9)}"
        return f"({s})" if p > 0 else s
    if k == "setlist":
        return "{" + ", ".join(to_lean(a) for a in x[1]) + "}"
    if k == "setof" and x[1][0] == "such" and x[1][1][0] == "var":
        # {k : P}: an index of a family has the family's index type and runs over its range (an integer bound is
        # read through toNat); else the type of k is inferred from P
        v, fam = x[1][1], family_of(x[1][2], x[1][1][1])
        fams = [y[1][1] for y in subterms(x[1][2]) if y[0] == "app" and len(y) > 3 and y[3] == "idx"
                and y[1][0] == "var" and v in y[2]]
        typ = f" : {LEAN_ITYP[fams[0]]}" if fams and fams[0] in LEAN_ITYP else ""
        rng = ""
        if fam:
            lo, hi = to_lean(fam[0], 3), nat_index(fam[1], fams[0] if fams else None)
            rng = f"{lo} \u2264 {to_lean(v)} \u2227 {to_lean(v)} \u2264 {hi} \u2227 "
        return "{" + to_lean(v) + typ + " | " + rng + to_lean(x[1][2]) + "}"
    if k == "setof" and x[1][0] == "such" and x[1][1][0] == "rel" and x[1][1][1] == ("in",) \
            and x[1][1][2][0][0] == "var" and x[1][1][2][1][0] == "set" and x[1][1][2][1][1] in LEAN_SETS:
        # {k in Z : P}
        return "{" + to_lean(x[1][1][2][0]) + " : " + LEAN_SETS[x[1][1][2][1][1]] + " | " + to_lean(x[1][2]) + "}"
    if k == "setof" and x[1][0] != "such" and not is_prop(x[1]):
        return "{" + to_lean(x[1]) + "}"  # a singleton {t}
    if k == "least":
        raise Hole(f"the {'least' if x[1] == 'min' else 'greatest'} element of a set (Q++ reads it in a definition"
                   f" m := {x[1]} {to_qpp(x[2])})")
    if k == "interval" and x[3] is not None:
        # s[a, b]: the image of [a, b] under t -> s t
        s = f"(fun t => {to_lean(x[3], 4)} * t) '' Set.Icc {to_lean(x[1], 9)} {to_lean(x[2], 9)}"
        return f"({s})" if p > 0 else s
    if k in ("family", "setof", "polyring", "interval", "norm"):
        raise Hole(f"{k} in a formula (no Lean printer yet)")
    if k == "bin":
        op = x[1]
        q = PREC[op]
        s = f"{to_lean(x[2], q)} {OPS_LEAN.get(op, op)} {to_lean(x[3], q + 1)}"
        if op == "/" and rational_free(x):
            return f"({s} : \u211a)"  # n / 2 with n in Z is the rational n / 2, not Lean's integer division
        return f"({s})" if p > q else s
    if k == "pow":
        e = x[2]
        if e == ("neg", ("num", "1")):
            s = f"{to_lean(x[1], 9)}\u207b\u00b9"  # postfix: an application is parenthesized
            return f"({s})" if p >= 9 else s
        # 2^(-k), 2^(floor t), n^k with k in Z: an exponent that may be negative needs a rational base (zpow)
        if rational_exponent(e):
            raise Hole(f"{to_qpp(x)}: a power with a rational exponent (declare the exponent in Z or N)")
        base = to_lean(x[1], 8)
        if int_exponent(e) and rational_free(x[1]) and not base.endswith(" : \u211a)"):
            base = f"({to_lean(x[1])} : \u211a)"
        ex = to_lean(e, 8)
        if int_exponent(e) and not (e[0] in ("floor", "ceil") or (e[0] == "var" and e[1] in LEAN_INT)
                                    or (e[0] == "neg" and e[1][0] == "var" and e[1][1] in LEAN_INT)):
            ex = f"({to_lean(e)} : \u2124)"  # 2^(-(2 C_H) - b), b in N: the exponent is read in Z (no Neg on N)
        s = f"{base} ^ {ex}"
        return f"({s})" if p > 6 else s
    if k in ("max", "min"):
        raise Hole("max/min over an index")
    if k == "oplus":
        raise Hole("the tropical sum of pairs (bound to the paper's library by a binding; none yet)")
    if k == "comp":
        # g_L o ... o g_1 (range (L, 1)): fold over [1, ..., L], each new map after the others; g_1 o ... o g_L before
        lo, hi = x[2][1] if x[2] and x[2][0] == "range" else (None, None)
        v = lean_name(x[1])
        if lo is None or ("num", "1") not in (lo, hi) or not nat_term(hi if lo == ("num", "1") else lo):
            raise Hole(f"{to_qpp(x)}: a composition over a range that does not start at 1")
        n = to_lean(hi if lo == ("num", "1") else lo, 9)
        g = to_lean(x[3], 9)
        step = f"{g} \u2218 acc" if lo != ("num", "1") else f"acc \u2218 {g}"
        s = f"(List.range' 1 {n}).foldl (fun acc {v} => {step}) id"
        return f"({s})" if p > 0 else s
    if k in ("sunion", "sinter"):
        s = ("\u22c3\u2080 " if k == "sunion" else "\u22c2\u2080 ") + to_lean(x[1], 9)
        return f"({s})" if p > 0 else s
    if k in ("union", "inter") or (k in ("sum", "prod") and x[2] is not None and x[2][0] == "incond"):
        # a union (intersection) over a set, with a condition: Set.iUnion over the members; a sum over a set with a
        # condition: finsum (its value is the sum when the set is finite, a hypothesis the paper states where needed)
        sym = {"union": "\u22c3", "inter": "\u22c2", "sum": "\u2211\u1da0", "prod": "\u220f\u1da0"}[k]
        v = lean_name(x[1])
        dom = x[2]
        if dom is None:
            s = f"{sym} {v}, {to_lean(x[3], 4)}"
        elif dom[0] == "in" and k in ("union", "inter"):
            s = f"{sym} {v} \u2208 {to_lean(dom[1], 9)}, {to_lean(x[3], 4)}"
        elif dom[0] in ("in", "incond"):
            cond = f" (_ : {to_lean(dom[2])})" if dom[0] == "incond" else ""
            s = f"{sym} ({v}) (_ : {v} \u2208 {to_lean(dom[1], 9)}){cond}, {to_lean(x[3], 4)}"
        else:
            raise Hole(f"a {k} over a range of the kind {dom[0]} (no Lean form yet)")
        return f"({s})" if p > 0 else s
    if k == "sum" and x[2] is not None and x[2][0] == "cell":
        raise Hole("a sum over a cell (read by qpp/kernel.py)")
    if k in ("sum", "prod"):
        sym = "\u2211" if k == "sum" else "\u220f"
        v = lean_name(x[1])
        d = vector_index_dim(x[3], x[1])
        if d is not None:
            # a sum over the components of a vector: over Fin d (the range is all of 1..d)
            def is_dim(b):
                return to_lean(b, 9) in (d, d.removesuffix(".toNat"))
            cond = x[2] is not None and x[2][0] == "cond"
            # over a set S of indices (\sum_{h\in S}, S\subseteq\{1,\dots,k\} bound or declared): the components whose
            # index is in S, a filter by membership in a set (decidable classically: the statement opens Classical)
            within = x[2] is not None and x[2][0] == "in" and x[2][1][0] == "var"
            if not (x[2] is None or cond or within or (x[2][0] == "le" and is_dim(x[2][1]))
                    or (x[2][0] == "range" and x[2][1][0] == ("num", "1") and is_dim(x[2][1][1]))):
                raise Hole(f"a sum over part of the components of a vector ({to_qpp(x)})")
            saved = LEAN_FIN.get(x[1])
            LEAN_FIN[x[1]] = d
            try:
                body = to_lean(x[3], 4)
                # the components that satisfy a condition: a sum over the filter of Finset.univ
                test = to_lean(x[2][1]) if cond else None
                if within:
                    test = f"{to_lean(('var', x[1]))} \u2208 {to_lean(x[2][1], 9)}"
                    LEAN_CLASSICAL[0] = True
                    cond = True
            finally:
                if saved is None:
                    LEAN_FIN.pop(x[1])
                else:
                    LEAN_FIN[x[1]] = saved
            s = (f"{sym} {v} \u2208 Finset.univ.filter (fun {v} : Fin {d} => {test}), {body}" if cond
                 else f"{sym} {v} : Fin {d}, {body}")
            return f"({s})" if p > 0 else s
        fam = family_of(x[3], x[1]) or (family_of(x[2][1], x[1]) if x[2] and x[2][0] == "cond" else None)
        lo = to_lean(fam[0], 9) if fam else "1"

        def hi(b):
            s = to_lean(b, 9)
            return f"{s}.toNat" if b[0] == "var" and b[1] in LEAN_INT else s
        if x[2] is None:
            if not fam:
                raise Hole(f"sum over {x[1]} without a range (no family in scope)")
            dom = f" \u2208 Finset.Icc {to_lean(fam[0], 9)} {hi(fam[1])}"
        elif x[2][0] == "cond":
            # a sum over the indices of a family that satisfy a condition
            if not fam:
                raise Hole(f"sum over {x[1]} with a condition and no family in scope")
            dom = (f" \u2208 Finset.filter (fun {v} => {to_lean(x[2][1])}) "
                   f"(Finset.Icc {to_lean(fam[0], 9)} {hi(fam[1])})")
        elif x[2][0] == "range":
            dom = f" \u2208 Finset.Icc {hi(x[2][1][0])} {hi(x[2][1][1])}"
        elif x[2][0] == "in":
            dom = f" \u2208 {to_lean(x[2][1], 9)}"
        elif x[2][0] == "lt":
            dom = f" \u2208 Finset.Ico {lo} {hi(x[2][1])}"
        else:
            dom = f" \u2208 Finset.Icc {lo} {hi(x[2][1])}"
        s = f"{sym} {v}{dom}, {to_lean(x[3], 4)}"
        return f"({s})" if p > 0 else s
    if k == "rel":
        links = []
        for op, a, b in zip(x[1], x[2], x[2][1:]):
            if op == "in":
                raise Hole("membership in a formula")
            if op not in REL_LEAN:
                raise Hole(f"the relation {op} has no meaning of its own (a row x {op} y :<=> R defines it)")
            if op in ("divides", "ndivides"):
                # divisibility is a relation of integers: both sides read in Z (a count is cast up; a term of Q
                # does not typecheck, rather than reading a | b in a field, where it always holds)
                d = f"({to_lean(a, 0)} : \u2124) \u2223 ({to_lean(b, 0)} : \u2124)"
                links.append(d if op == "divides" else f"\u00ac({d})")
                continue
            links.append(f"{to_lean(a, 3)} {REL_LEAN[op]} {to_lean(b, 3)}")
        s = " \u2227 ".join(links)
        return f"({s})" if (p > 2 or (len(links) > 1 and p > 0)) else s
    if k in ("imp", "iff"):
        arrow = "\u2192" if k == "imp" else "\u2194"
        s = f"{to_lean(x[1], 2)} {arrow} {to_lean(x[2], 1)}"
        return f"({s})" if p > 1 else s
    if k == "and":
        # a conjunction inside a term (the condition of a set builder); a statement's own conjunctions are qpp2lean's
        s = " \u2227 ".join(to_lean(c, 3) for c in x[1])
        return f"({s})" if p > 0 and len(x[1]) > 1 else s
    if k == "not":
        return f"\u00ac({to_lean(x[1])})"
    if k == "or":
        s = f"{to_lean(x[1], 3)} \u2228 {to_lean(x[2], 3)}"
        return f"({s})" if p > 0 else s
    if k in ("exists", "forall"):
        sym = "\u2203" if k == "exists" else "\u2200"
        vs = " ".join(to_lean(v) for v in x[1])
        dom = f" \u2208 {to_lean(x[2], 9)}" if x[2] is not None else ""
        s = f"{sym} {vs}{dom}, {to_lean(x[3])}"
        return f"({s})" if p > 0 else s
    if k == "def":
        raise Hole("definition")
    raise ValueError(x)


# ---------------------------------------------------------------------------------------------------------
# LaTeX printer (canonical spelling) and the round trip

REL_TEX_OUT = {"<=": "\\le", ">=": "\\ge", "<": "<", ">": ">", "=": "=", "!=": "\\ne", "in": "\\in",
               "subseteq": "\\subseteq", "subset": "\\subset", "notin": "\\notin", "supseteq": "\\supseteq",
               "supset": "\\supset", "divides": "\\mid", "ndivides": "\\nmid", "asymp": "\\asymp", "sim": "\\sim",
               "simeq": "\\simeq", "preceq": "\\preceq", "succeq": "\\succeq", "prec": "\\prec", "succ": "\\succ",
               "equiv": "\\equiv"}
OPS_TEX = {"cap": "\\cap ", "cup": "\\cup ", "minus": "\\setminus ", "par": "\\parallel ", "times": "\\times ",
           "comp": "\\circ "}
OPS_LEAN = {"cap": "\u2229", "cup": "\u222a", "minus": "\\", "times": "\u00d7\u02e2", "comp": "\u2218"}
SETS_TEX = {"QQ": "\\Q", "ZZ": "\\Z", "NN": "\\N"}


def subst_var(x, v, t):
    """x with the variable v replaced by the term t"""
    if isinstance(x, tuple) and x:
        if x == ("var", v):
            return t
        return tuple(subst_var(y, v, t) for y in x)
    return x


def tex_name(v):
    prime = ""
    while v.endswith("'"):
        v, prime = v[:-1], prime + "'"
    for suf, mark in (("_pos", "^+"), ("_neg", "^-"), ("_nought", "^0"), ("_circ", "^\\circ")):
        if v.endswith(suf):
            return tex_name(v[:-len(suf)]) + mark + prime
    if v.startswith("cal_") and len(v) >= 5:
        return "\\mathcal " + v[4] + (("_" + _sub(v[6:])) if v[5:6] == "_" else "") + prime
    if v.startswith("frak_") and len(v) >= 6:
        return "\\mathfrak " + v[5] + (("_" + _sub(v[7:])) if v[6:7] == "_" else "") + prime
    if v.endswith("_star") or (v.endswith("star") and "_" in v):
        return tex_name(v[:-5] if v.endswith("_star") else v[:-4]) + "^*" + prime
    if v == "b_zero":
        return "\\mathbf 0" + prime
    rev = {}
    for c, b in BOLD_CMDS.items():
        rev.setdefault(b, c)  # the first spelling: \bd, not \bdelta
    if v in rev:
        return "\\" + rev[v] + prime
    m = re.fullmatch(r"b_([A-Za-z])_(.+)", v)
    if m:
        return "\\b" + m.group(1) + "_" + _sub(m.group(2)) + prime
    m = re.fullmatch(r"(b_[A-Za-z]+)_(.+)", v)
    if m and m.group(1) in rev:
        return "\\" + rev[m.group(1)] + "_" + _sub(m.group(2)) + prime  # \btheta_0, \bd_1
    base, _, rest = v.partition("_")
    if base == "b" and len(rest) == 1 and rest.isalpha():  # bold \bw; b_0 is b with index 0
        return "\\b" + rest + prime
    if base == "b" and rest in GREEK:
        return "\\boldsymbol{\\" + rest + "}" + prime
    b = ("\\" + base) if base in GREEK else ("\\infty" if base == "inf" else base)
    if not rest:
        return b + prime
    if rest in ("plus", "minus"):
        return b + "_" + ("+" if rest == "plus" else "-") + prime
    if rest == "ast":
        return b + "_*" + prime
    if rest in GREEK:
        return b + "_{\\" + rest + "}" + prime  # v_alpha: v with alpha below, never the letters a, l, p, h, a
    return b + "_" + (rest if len(rest) == 1 else "{" + rest + "}") + prime


NUMBERED = re.compile(r"([A-Za-z]+?)(\d+)")  # a name with a numeral at its end: u0, K1, lambda2


def numbered(v):
    """(base, numeral) of a name with a numeral at its end, printed as the base with the numeral below (u0 as u_0,
    lambda2 as lambda_2), or None"""
    m = NUMBERED.fullmatch(v) if isinstance(v, str) else None
    return (m.group(1), m.group(2)) if m else None


def member_tex(name, index):
    """the member of the family name at an index (LaTeX): a_i; u0 at i is u_{0,i}, one index list below u"""
    nb = numbered(name)
    if nb:
        return to_tex(("var", nb[0]), 9) + "_{" + nb[1] + "," + index + "}"
    return to_tex(("var", name), 9) + "_" + _sub(index)


def _sub(s):
    return s if len(s) == 1 else "{" + s + "}"


def _base(b):
    """the base of a power: in parentheses when it carries a superscript of its own, (2^C)^4 and never 2^C^4"""
    depth = 0
    for i, c in enumerate(b):
        if c == "\\":
            continue
        if c in "{([" and (i == 0 or b[i - 1] != "\\"):
            depth += 1
        elif c in "})]" and (i == 0 or b[i - 1] != "\\"):
            depth -= 1
        elif c == "^" and depth == 0:
            return f"({b})"
    return b


def edge(x, right):
    """the name at the right (or the left) end of a factor as it prints: the last (or the first) factor of a product,
    the name of a member of a family (a_i, a_{ji}), of an application at its left (K(w); an operator \\max(...) is
    ("op", "max")) and of a power at its left"""
    while True:
        if x[0] == "bin" and x[1] == "*":
            x = x[3] if right else x[2]
        elif x[0] == "app" and (x[3] == "idx" or not right):
            if x[3] != "idx" and x[1][0] == "var" and (x[1][1] in FUNC_CMDS or x[1][1] in ("max", "min")):
                return ("op", x[1][1])  # \max(...), \log(...): an operator, which TeX spaces from its neighbours
            x = x[1]
        elif x[0] == "pow" and not right:
            x = x[1]
        else:
            return x


# the names of the item being printed, of two or more letters, whose letters are each a one-letter name of it (Tc beside
# T and c): a product of two names whose letters run into one of them is written with \cdot (joined_names)
JOINED = frozenset()
BOUND_NAMES = re.compile(r"((?:[A-Za-z][A-Za-z0-9_]*\s*,\s*)*[A-Za-z][A-Za-z0-9_]*)\s+in\s+(?:QQ|NN|ZZ)")


def joined_names(texts):
    """the names bound in the rows texts of an item that read as a product of its one-letter names"""
    names = {v.strip() for t in texts for b in BOUND_NAMES.findall(t) for v in b.split(",")}
    singles = {v for v in names if len(v) == 1}
    return frozenset(v for v in names if len(v) > 1 and v.isalpha() and v not in GREEK and all(c in singles for c in v))


def runs_into(a, b):
    """two names side by side whose letters read as part of a name of JOINED"""
    if a[0] != "var" or b[0] != "var" or not isinstance(a[1], str) or not isinstance(b[1], str):
        return False
    return any(a[1] + b[1] in v for v in JOINED)


def long_name(x):
    """a name printed upright with two or more letters (\\mathrm{pa}), or the part of a bundle (\\mathrm{Pr}.N)"""
    if x[0] != "var" or not isinstance(x[1], str):
        return False
    v = x[1]
    return "." in v or (len(v) > 1 and v.isalpha() and v not in GREEK and not v.startswith("b_"))


def to_tex(x, p=0):
    k = x[0]
    if k == "cite":
        return "(" + to_tex(x[1]) + ")"
    if k == "blank":
        return "\\cdot"
    if k == "units":
        return _base(to_tex(x[1], 9)) + "^\\times"
    if k == "num":
        return x[1]
    if k == "var":
        v = x[1]
        if v == "top":
            return "\\top"  # the top element of the pairs, as the hole text writes it
        if "." in v:
            # the part P of a bundle Pr: \mathrm{Pr}.P, the bundle upright whatever its length
            base, part = v.split(".", 1)
            return "\\mathrm{" + base + "}." + to_tex(("var", part))
        if len(v) > 1 and v.isalpha() and v not in GREEK and not v.startswith("b_"):
            return "\\mathrm{" + v + "}"
        if numbered(v):
            base, num = numbered(v)
            return to_tex(("var", base), 9) + "_" + _sub(num)  # u0 as u_0, lambda2 as lambda_2, K1 as K_1
        return tex_name(v)
    if k == "setfrom":
        return SETS_TEX[x[1]] + "_{" + ("\\ge " if x[2] == ">=" else ">") + to_tex(x[3]) + "}"
    if k == "set":
        name = x[1]
        if name == "empty":
            return "\\varnothing"
        for q, t in SETS_TEX.items():
            if name.startswith(q):
                rest = name[len(q):]
                if not rest:
                    return t
                if rest == "empty":
                    return "\\varnothing"
                m = re.fullmatch(r"(>=|>)(\d+)", rest)
                return t + "_{" + ("\\ge" if m.group(1) == ">=" else ">") + m.group(2) + "}"
        return name
    if k == "hole":
        return x[1]
    if k in ("ref", "refat"):
        lab, _, item = x[1].partition("(")
        s = ("\\eqref{" if lab.startswith("eq:") else "\\cref{") + lab + "}" + ("(" + item if item else "")
        return s + ("[" + ",".join(to_tex(a) for a in x[2]) + "]" if k == "refat" else "")
    if k == "app":
        if x[3] == "idx" and x[1][0] == "app" and x[1][3] == "idx" and x[1][1][0] == "var":
            # a_(j)_(i), the coordinate i of the member a_(j) of a family of tuples: a_{ji}, as an entry of a matrix
            return to_tex(("app", x[1][1], x[1][2] + x[2], "idx"), p)
        if x[3] == "idx" and x[1][0] == "var" and numbered(x[1][1]):
            # u0_(i), the coordinate i of u0: u_{0,i}, the numeral and the index in one list below u
            base, num = numbered(x[1][1])
            return to_tex(("app", ("var", base), (("num", num),) + tuple(x[2]), "idx"), p)
        if x[3] == "idx":
            parts = [to_tex(a) for a in x[2]]
            if all(len(q) == 1 and q.isalpha() for q in parts):  # M_{ij}; N_{j,0} keeps its comma (j0 is j * 0)
                return to_tex(x[1], 9) + "_" + _sub("".join(parts))
            return to_tex(x[1], 9) + "_{" + ",".join(parts) + "}"
        f = x[1][1] if x[1][0] == "var" else None
        args = ",".join(to_tex(a) for a in x[2])
        if f == "int" and len(x[2]) in (2, 4):
            body = to_tex(x[2][0], 4)
            if len(x[2]) == 2:
                return "\\int " + body + "\\,d" + to_tex(x[2][1], 9)
            bounds = "_" + _sub(to_tex(x[2][2])) + "^" + _sub(to_tex(x[2][3]))
            if x[2][1][0] == "blank":
                return "\\int" + bounds + body
            return "\\int" + bounds + body + "\\,d" + to_tex(x[2][1], 9)
        if f == "jac" and len(x[2]) == 1:
            return "d" + to_tex(x[2][0], 9)
        if f == "restrict" and len(x[2]) == 2:
            return to_tex(x[2][0], 9) + "|_" + _sub(to_tex(x[2][1]))
        if f == "interior" and len(x[2]) == 1:
            return "\\mathring{" + to_tex(x[2][0]) + "}"
        if f == "powerset" and len(x[2]) == 1:
            return "\\mathcal P(" + to_tex(x[2][0]) + ")"
        if f == "fact" and len(x[2]) == 1:
            a = to_tex(x[2][0], 9)
            return (a if x[2][0][0] in ("var", "num") else f"({to_tex(x[2][0])})") + "!"
        if f == "tensor" and len(x[2]) == 2:
            return _base(to_tex(x[2][0], 9)) + "^{\\otimes " + to_tex(x[2][1]) + "}"
        if f == "deriv" and len(x[2]) in (2, 3):
            # the k-th derivative in y: \partial^k_y g
            order = "^" + _sub(to_tex(x[2][2])) if len(x[2]) == 3 else ""
            return "\\partial" + order + "_" + _sub(to_tex(x[2][1])) + to_tex(x[2][0], 9)
        if f in ("choose", "binom") and len(x[2]) == 2:
            # binom(n, k) of the primitives and \binom of the papers: the binomial coefficient
            return "\\tbinom{" + to_tex(x[2][0]) + "}{" + to_tex(x[2][1]) + "}"
        if f in ("bidetP", "bidetM") and len(x[2]) in (1, 2):
            # the halves of the bideterminant: |(T,U)|^+, |(T,U)|^- of a couple, |A|^+, |A|^- of one table
            # (the macros of modules/macros.tex)
            return "\\" + f + ("a" if len(x[2]) == 1 else "") + "".join("{" + to_tex(a) + "}" for a in x[2])
        if f == "transpose" and len(x[2]) == 1:
            return _base(to_tex(x[2][0], 9)) + "^\\top"
        if f == "card" and len(x[2]) == 1:
            return "\\#" + to_tex(x[2][0], 9)
        if f in FUNC_CMDS or f in ("max", "min"):
            return "\\" + f + "(" + args + ")"
        if f and len(f) > 1 and f.isalpha() and f not in GREEK:
            return "\\mathrm{" + f + "}(" + args + ")"
        return to_tex(x[1], 9) + "(" + args + ")"
    if k == "tuple":
        return "(" + ",".join(to_tex(a) for a in x[1]) + ")"
    if k == "family":
        return member_tex(x[1], to_tex(x[2])) + ",\\dots," + member_tex(x[1], to_tex(x[3]))
    if k == "setof":
        b = x[1]
        inner = (to_tex(b[1]) + ":\\ " + to_tex(b[2])) if b[0] == "such" else to_tex(b)
        return "\\{" + inner + "\\}"
    if k == "setlist":
        return "\\{" + ",".join(to_tex(a) for a in x[1]) + "\\}"
    if k == "intrange":
        return "\\{" + to_tex(x[1]) + ",\\dots," + to_tex(x[2]) + "\\}"
    if k == "least":
        return "\\" + x[1] + to_tex(x[2])
    if k == "polyring":
        return to_tex(x[1], 9) + "[" + ",".join(to_tex(v) for v in x[2]) + "]"
    if k == "interval":
        return "[" + to_tex(x[1]) + "," + to_tex(x[2]) + "]" + (to_tex(x[3], 6) if x[3] is not None else "")
    if k == "ivl":
        return ("(" if x[1] == "oc" else "[") + to_tex(x[2]) + "," + to_tex(x[3]) + ("]" if x[1] == "oc" else ")")
    if k == "norm":
        bar = "|" if x[3] == "|" else "\\|"
        return bar + to_tex(x[1]) + bar + ("_" + _sub(to_tex(x[2])) if x[2] is not None else "")
    if k == "abs":
        return "|" + to_tex(x[1]) + "|"
    if k == "iverson":
        return "\\mathbf 1[" + to_tex(x[1]) + "]"
    if k == "prog":
        return "\\operatorname{prog}(" + to_tex(x[1]) + ")"
    if k in ("ceil", "floor"):
        return ("\\lceil " if k == "ceil" else "\\lfloor ") + to_tex(x[1]) + ("\\rceil" if k == "ceil" else "\\rfloor")
    if k == "neg":
        inner = to_tex(x[1], PREC["neg"])
        s = "-" + (f"({inner})" if inner.startswith("-") else inner)  # --t is a comment in Lean, a dash in TeX
        return f"({s})" if p > PREC["neg"] else s
    if k == "bin":
        op = x[1]
        q = PREC[op]
        a, b = to_tex(x[2], q), to_tex(x[3], q + 1)
        if op == "*":
            # a parenthesis after a name is read by its scope, and an upright name of two or more letters next to
            # another name runs into it (pa pb reads papb): the product is written with \cdot
            sep = "\\cdot " if b[:1].isdigit() or b.startswith("-") or b.startswith("(") or \
                (long_name(edge(x[2], True)) and edge(x[3], False)[0] == "var") or \
                (edge(x[2], True)[0] == "var" and long_name(edge(x[3], False))) or \
                runs_into(edge(x[2], True), edge(x[3], False)) else " "
            s = a + sep + b
        elif op in OPS_TEX:
            s = a + OPS_TEX[op] + b
        else:
            s = f"{a}{op}({b})" if op in "+-" and b.startswith("-") else f"{a}{op}{b}"  # a--b is a dash
        return f"({s})" if p > q else s
    if k == "pow":
        return f"{_base(to_tex(x[1], 8))}^{_sub(to_tex(x[2]))}"
    if k in ("par", "comp") and x[2] and x[2][0] == "range":
        def at(t):
            return to_tex(subst_var(x[3], x[1], t), 4)
        sep = "\\parallel" if k == "par" else "\\circ"
        s = f"{at(x[2][1][0])}{sep}\\dots{sep} {at(x[2][1][1])}"
        return f"({s})" if p > 3 else s
    if k in ("sunion", "sinter"):
        s = ("\\bigcup " if k == "sunion" else "\\bigcap ") + to_tex(x[1], 9)
        return f"({s})" if p > 3 else s
    if k == "famtuple":
        d, v = x[2], tex_name(x[1])
        dom = (to_tex(d[1][0], 3) + "\\le " + v + "\\le " + to_tex(d[1][1], 3) if d[0] == "range" else
               v + {"in": "\\in ", "lt": "<", "le": "\\le "}[d[0]] + to_tex(d[1], 3))
        return "(" + to_tex(x[3]) + ")_{" + dom + "}"
    if k == "attained":
        s = f"{to_tex(x[1], 1)},\\ \\text{{attained}}"
        return f"({s})" if p >= 2 else s
    if k == "uniform":
        s = f"{to_tex(x[2], 1)},\\ \\text{{constants free of}}\\ " + ",".join(to_tex(n) for n in x[1])
        return f"({s})" if p >= 2 else s
    if k in ("sum", "prod", "max", "min", "par", "union", "inter", "oplus"):
        dom, hi = "", ""
        if x[2] and x[2][0] == "range":
            dom, hi = "=" + to_tex(x[2][1][0], 3), "^" + _sub(to_tex(x[2][1][1], 3))
        elif x[2] and x[2][0] == "cond":
            dom = to_tex(x[2][1], 2)
        elif x[2] and x[2][0] == "incond":
            dom = "\\in " + to_tex(x[2][1], 3) + ",\\ " + to_tex(x[2][2], 1)
        elif x[2] and x[2][0] == "cell":
            # a sum over a cell: its range and its clauses under the sign, one per line
            b, v = x[2][1], tex_name(x[1])
            head = (v if b is None else to_tex(b[1][0], 3) + "\\le " + v + "\\le " + to_tex(b[1][1], 3)
                    if b[0] == "range" else v + "\\in " + to_tex(b[1], 3))
            rows = "\\\\ ".join([head] + [to_tex(c, 0) for c in x[2][2]])
            s = f"\\textstyle\\sum_{{\\substack{{{rows}}}}} {to_tex(x[3], 4)}"
            return f"({s})" if p > 3 else s
        elif x[2]:
            dom = {"in": "\\in ", "lt": "<", "le": "\\le "}[x[2][0]] + to_tex(x[2][1], 3)
        idx = (to_tex(("var", x[1])) + dom) if not (x[2] and x[2][0] == "cond") else dom  # its index as a name
        pre = "\\textstyle" if k in ("sum", "prod", "union", "inter") else ""
        cmd = {"union": "bigcup", "inter": "bigcap", "oplus": "bigoplus"}.get(k, k)
        s = f"{pre}\\{cmd}_{_sub(idx)}{hi} {to_tex(x[3], 4)}"
        return f"({s})" if p > 3 else s
    if k == "rel":
        parts = [to_tex(x[2][0], 3)]
        for op, t in zip(x[1], x[2][1:]):
            parts += [REL_TEX_OUT[op], to_tex(t, 3)]
        s = " ".join(parts)
        return f"({s})" if p > 2 else s
    if k == "def":
        return f"{to_tex(x[1])}:={to_tex(x[2])}"
    if k in ("imp", "ctx"):
        a = x[1]
        sep = "\\Rightarrow " if k == "imp" else ":\\ "
        s = f"{to_tex(a, 0.5 if a[0] == 'and' else 1)}{sep}{to_tex(x[2], 0)}"
        return f"({s})" if p >= 1 else s
    if k == "iff":
        s = f"{to_tex(x[1], 2)}\\iff {to_tex(x[2], 1)}"
        return f"({s})" if p >= 1 else s  # in a list of clauses too: A,\ B\iff C reads (A, B) <=> C
    if k in ("exists", "forall"):
        dom = f"\\in {to_tex(x[2], 3)}" if x[2] is not None else ""
        s = f"\\{k} {','.join(to_tex(v) for v in x[1])}{dom}:\\ {to_tex(x[3], 0)}"
        return f"({s})" if p >= 1 else s
    if k == "defrel":
        s = f"{to_tex(x[1], 2)}:\\iff {to_tex(x[2], 0)}"
        return f"({s})" if p >= 1 else s
    if k == "word":
        return "\\text{" + x[1] + "}"
    if k == "fun":
        return f"{to_tex(x[1], 3)}\\to {to_tex(x[2], 3)}"
    if k == "decl":
        names = ",".join(to_tex(n) for n in x[1])
        if x[2][0] == "fun":
            return names + ":" + to_tex(x[2], 3)
        if x[2][0] == "word":
            w = x[2][1]
            pl = VOCAB.get(w, {}).get("plural", w) if len(x[1]) > 1 or x[1][0][0] == "family" else w
            return names + "\\ \\text{" + pl + "}"
        return names + "\\in " + to_tex(x[2], 3)
    if k == "and":
        cs = x[1]
        s = ",\\ ".join(to_tex(c, 0 if (i == len(cs) - 1 and c[0] in ("exists", "forall") and p == 0) else 1)
                         for i, c in enumerate(cs))
        return f"({s})" if p >= 1 else s
    if k == "textrel":
        out = [to_tex(x[2][0], 3)]
        for w, a in zip(x[1], list(x[2][1:]) + [None] * len(x[1])):
            out.append("\\text{" + w + "}")
            if a is not None:
                out.append(to_tex(a, 3))
        s = "\\ ".join(out)
        return f"({s})" if p >= 2 else s
    if k == "on":
        where = ("\\text{on a " + x[1][1] + "}") if x[1][0] == "word" else ("\\text{on}\\ " + to_tex(x[1], 3))
        s = f"{to_tex(x[2], 2)}\\ {where}"
        return f"({s})" if p >= 2 else s
    if k in ("at", "near"):
        s = f"{to_tex(x[2], 2)}\\ \\text{{{k}}}\\ {to_tex(x[1], 3)}"
        return f"({s})" if p >= 2 else s
    if k == "not":
        return "\\neg(" + to_tex(x[1]) + ")"
    if k == "or":
        s = f"{to_tex(x[1], 2)}\\ \\text{{or}}\\ {to_tex(x[2], 2)}"
        return f"({s})" if p >= 2 else s
    raise ValueError(x)


def tex_signature(s):
    """the tokens of a LaTeX formula without layout (spaces, braces, \\textstyle and the like)"""
    return [t for t in tex_tokens(s) if t not in (("sym", "{"), ("sym", "}"))]


def round_trip(s, functions=()):
    """(formal, same meaning, same spelling) for a LaTeX formula: parse it, print it back canonically, compare"""
    try:
        tree = parse_tex(s, functions)
    except Hole:
        return False, False, False
    back = to_tex(tree)
    try:
        same_meaning = parse_tex(back, functions) == tree
    except Hole:
        same_meaning = False
    return True, same_meaning, tex_signature(back) == tex_signature(s)


def parse_stmt(s, functions=(), vocab=None):
    """a statement item (conventions v1): (parts, glosses); raises Hole outside the fragment"""
    p = TexParser(normalize(s), functions, vocab)
    parts = p.stmt()
    clash = defined_numbers(parts) & applied_names(parts)
    if clash:
        # j:=j(\bx_0): the item makes j a number and applies j as a function, one name for two objects
        raise Hole(f"{', '.join(sorted(clash))} defined as a number and applied as a function in one item")
    idle = idle_binders(parts)
    if idle:
        # \{\btheta:\ (c,(a_hw_h)_h)\in B\}: the condition does not name theta, so the set is all or nothing; the
        # paper means theta's components (c, a, w, b), which no declaration gives
        raise Hole(f"the set builder of {', '.join(sorted(idle))}: its condition does not use it (name its components)")
    if FREE_DATA[0]:
        bare = [x for x in parts if is_data_condition(x, FREE_DATA[0])]
        if bare:
            # \beta\ge n_e+2 under a given that only declares beta, n_e in N: false for some values of data that
            # nothing constrains, so it is a condition the paper lists among the conclusions (of an admissible
            # choice), not a conclusion of the given
            raise Hole(f"false for some values of {', '.join(sorted(data_atoms(bare[0])))}, which the given only "
                       "declares: a condition (a hypothesis of the given or a definition), not a conclusion")
    return parts, p.glosses


FREE_DATA = [{}]  # {name: NN, ZZ or QQ}: the data the given of the conclusion read declares and nothing constrains


def data_atoms(x):
    """the names of a term as the given declares them: a plain name, or an indexed name with plain indices (n_e,
    j_1) as one name (its Q++ form)"""
    if not isinstance(x, (tuple, list)):
        return set()
    if isinstance(x, tuple) and len(x) >= 2 and x[0] == "var" and isinstance(x[1], str):
        return {x[1]}
    if is_index_atom(x):
        return {to_qpp(x)}
    return set().union(*(data_atoms(y) for y in x)) if x else set()


def is_index_atom(x):
    return isinstance(x, tuple) and len(x) > 3 and x[0] == "app" and x[3] == "idx" and x[1][:1] == ("var",) and \
        all(isinstance(a, tuple) and a[:1] in (("var",), ("num",)) for a in x[2])


def linear_form(x):
    """a term as {name: coefficient} with its constant under None, over Q; None if it is not linear"""
    from fractions import Fraction
    if not isinstance(x, tuple) or not x:
        return None
    if x[0] == "num":
        try:
            return {None: Fraction(x[1])}
        except (ValueError, ZeroDivisionError):
            return None
    if x[0] == "var" and isinstance(x[1], str):
        return {x[1]: Fraction(1)}
    if is_index_atom(x):
        return {to_qpp(x): Fraction(1)}
    if x[0] == "neg":
        a = linear_form(x[1])
        return None if a is None else {k: -v for k, v in a.items()}
    if x[0] == "bin" and x[1] in ("+", "-", "*", "/"):
        a, b = linear_form(x[2]), linear_form(x[3])
        if a is None or b is None:
            return None
        if x[1] in ("+", "-"):
            out = dict(a)
            for k, v in b.items():
                out[k] = out.get(k, 0) + (v if x[1] == "+" else -v)
            return out
        const = lambda f: set(f) <= {None}  # noqa: E731
        if x[1] == "*" and (const(a) or const(b)):
            c, f = (a.get(None, 0), b) if const(a) else (b.get(None, 0), a)
            return {k: c * v for k, v in f.items()}
        if x[1] == "/" and const(b) and b.get(None, 0) != 0:
            return {k: v / b[None] for k, v in a.items()}
    return None


def linear_valid(op, e, types):
    """whether e op 0 holds for every value of its names (types: NN, ZZ or QQ): True, False, or None (unknown)"""
    if op in ("<=", "<"):
        e, op = {k: -v for k, v in e.items()}, {"<=": ">=", "<": ">"}[op]
    const = e.get(None, 0)
    coeffs = {k: v for k, v in e.items() if k is not None and v != 0}
    if op == "=":
        return not coeffs and const == 0
    if op not in (">=", ">"):
        return None
    if any(not (types.get(k) == "NN" and v > 0) for k, v in coeffs.items()):
        return False  # a negative coefficient of a natural, or any coefficient of an integer or a rational
    return const >= 0 if op == ">=" else const > 0


def is_data_condition(x, free):
    """a relation on the names of free alone (a conjunct of the item) that is linear and false for some of their
    values: a conclusion no proof can give, so a condition"""
    if not isinstance(x, tuple) or not x:
        return False
    if x[0] == "and":
        return any(is_data_condition(y, free) for y in x[1])
    if x[0] != "rel":
        return False
    names = data_atoms(x)
    if not names or not names <= set(free):
        return False
    ops, terms = x[1], x[2]
    for op, a, b in zip(ops, terms, terms[1:]):
        fa, fb = linear_form(a), linear_form(b)
        if fa is None or fb is None:
            return False
        e = dict(fa)
        for k, v in fb.items():
            e[k] = e.get(k, 0) - v
        if linear_valid(op, e, free) is False:
            return True
    return False


def names_in(x):
    """the plain names of a term, with the bases of its indexed names (a_h gives a)"""
    if not isinstance(x, (tuple, list)):
        return set()
    if isinstance(x, tuple) and len(x) >= 2 and x[0] == "var" and isinstance(x[1], str):
        return {x[1]}
    out = set()
    if isinstance(x, tuple) and len(x) > 3 and x[0] == "app" and x[3] == "idx" and x[1][:1] == ("var",):
        out.add(x[1][1])
    return out.union(*(names_in(y) for y in x)) if x else out


def idle_binders(x):
    """the names bound by a set builder \\{x:\\ P\\} or \\{x\\in S:\\ P\\} that P does not use (a vector b_v counts
    as used where a component v_i occurs)"""
    if not isinstance(x, (tuple, list)):
        return set()
    out = set()
    if isinstance(x, tuple) and len(x) == 2 and x[0] == "setof" and isinstance(x[1], tuple) and x[1][:1] == ("such",):
        binder, cond = x[1][1], x[1][2]
        if binder[0] == "rel" and binder[1] == ("in",):
            binder = binder[2][0]
        bound = [b[1] for b in (binder[1] if binder[0] == "tuple" else (binder,)) if b[0] == "var"]
        used = names_in(cond)
        for b in bound:
            if b not in used and not (b.startswith("b_") and b[2:] in used):
                out.add(b)
    return out.union(*(idle_binders(y) for y in x)) if x else out


def defined_numbers(x):
    """the plain names an item defines by := (j:=t), not the functions it defines (\\psi(x'):=t)"""
    if not isinstance(x, (tuple, list)):
        return set()
    if isinstance(x, tuple) and x and x[0] == "def" and isinstance(x[1], tuple) and x[1][:1] == ("var",):
        return {x[1][1]} | defined_numbers(x[2])
    return set().union(*(defined_numbers(y) for y in x)) if x else set()


def applied_names(x):
    """the plain names an item applies to arguments (j(\\bx_0))"""
    if not isinstance(x, (tuple, list)):
        return set()
    out = set()
    if isinstance(x, tuple) and len(x) > 3 and x[0] == "app" and x[3] == "call" and isinstance(x[1], tuple) \
            and x[1][:1] == ("var",):
        out.add(x[1][1])
    return out.union(*(applied_names(y) for y in x)) if x else out


def stmt_print(parts, printer):
    return (";\\ " if printer is to_tex else "; ").join(printer(x, 0) for x in parts)


def stmt_round_trip(s, functions=(), vocab=None):
    """(formal, same, spelled, Q++) for one statement item; per part, holes ?{...} where a part is outside"""
    try:
        parts, _ = parse_stmt(s, functions, vocab)
    except Hole:
        return False, False, False, None
    back = stmt_print(parts, to_tex)
    try:
        same = parse_stmt(back, functions, vocab)[0] == parts
    except Hole:
        same = False
    try:
        q_same = parse_qpp_item(stmt_print(parts, to_qpp)) == parts
    except ValueError:
        q_same = False
    return True, same and q_same, tex_signature(back) == tex_signature(s), stmt_print(parts, to_qpp)


def tex_to_qpp(s, functions=()):
    """the Q++ form of a LaTeX formula, or a hole ?{...}"""
    try:
        return to_qpp(parse_tex(s, functions))
    except Hole:
        return "?{" + s.strip() + "}"


def is_formal(q):
    return "?{" not in q


def lattice_in(x):
    """whether a Q++ tree binds an index over the coordinates of a tuple (`sum i, t`, `forall i : P`: no range) or a
    point of a box (`sum u <= b, t`)"""
    if not isinstance(x, tuple) or not x:
        return False
    if x[0] in ("sum", "prod") and len(x) == 4 and (x[2] is None or (isinstance(x[2], tuple) and x[2][0] == "le")):
        return True
    if x[0] in ("forall", "exists") and len(x) == 4 and x[2] is None:
        return True
    return any(lattice_in(y) for y in x)
