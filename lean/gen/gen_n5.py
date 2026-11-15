#!/opt/homebrew/bin/uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy", "scipy"]
# ///
"""Emit Packing/Cube5Cert.lean: the polynomial inequalities of Schaer's N = 5 proof.

Each inequality  T >= 0  on a polytope {g_1 >= 0, ..., g_n >= 0} is proved from an identity
    T = c_0 + sum_k c_k * (product of at most DEG of the g_i),   c_k >= 0 rational.
The support comes from a floating-point LP; the coefficients are then made rational and the
identity is checked exactly with fractions before the lemma is written. The Lean proof is
`linarith [products]`, so Lean finds its own coefficients; the exact check here only
guarantees that some exist.

usage: gen_n5.py <output .lean>      (Linux only, 2 GB address-space cap)
"""
import itertools
import resource
import sys
from fractions import Fraction as F

import numpy as np
from scipy.optimize import linprog

assert sys.platform == 'linux', 'the memory cap below needs Linux'
resource.setrlimit(resource.RLIMIT_AS, (2 << 30, 2 << 30))


# ---- exact polynomials: dict monomial(tuple of variable indices, sorted) -> Fraction ----

def padd(p, q, s=1):
    r = dict(p)
    for m, c in q.items():
        r[m] = r.get(m, 0) + s * c
        if r[m] == 0:
            del r[m]
    return r


def pmul(p, q):
    r = {}
    for m1, c1 in p.items():
        for m2, c2 in q.items():
            m = tuple(sorted(m1 + m2))
            r[m] = r.get(m, 0) + c1 * c2
    return {m: c for m, c in r.items() if c != 0}


def linpoly(const, co):
    """const + sum co[v] * v, with co a dict variable index -> number."""
    p = {}
    if const:
        p[()] = F(const)
    for v, c in co.items():
        if c:
            p[(v,)] = F(c)
    return p


def lean_lin(p, names):
    """Lean text of a linear polynomial."""
    out = ''
    items = sorted(p.items(), key=lambda t: (len(t[0]) == 0, t[0]))
    items = [t for t in items if t[0] == ()] + [t for t in items if t[0] != ()]
    for m, c in items:
        mag = abs(c)
        body = str(mag) if m == () else (names[m[0]] if mag == 1 else '%s * %s' % (mag, names[m[0]]))
        if out == '':
            out = body if c > 0 else '-' + body
        else:
            out += (' + ' if c > 0 else ' - ') + body
    return out or '0'


# ---- certificate search ----

def monos(nv, deg):
    ms = []
    for d in range(deg + 1):
        ms += list(itertools.combinations_with_replacement(range(nv), d))
    return ms


def gauss_solve(M, b, guess):
    """Exact solution of M x = b (lists of Fractions), free variables set from `guess`."""
    rows, n = len(M), len(M[0])
    aug = [list(M[i]) + [b[i]] for i in range(rows)]
    piv, r = [], 0
    for c in range(n):
        p = next((i for i in range(r, rows) if aug[i][c] != 0), None)
        if p is None:
            continue
        aug[r], aug[p] = aug[p], aug[r]
        inv = 1 / aug[r][c]
        aug[r] = [x * inv for x in aug[r]]
        for i in range(rows):
            if i != r and aug[i][c] != 0:
                f = aug[i][c]
                aug[i] = [x - f * y for x, y in zip(aug[i], aug[r])]
        piv.append(c)
        r += 1
    if any(row[n] != 0 for row in aug[r:]):
        return None
    x = [None] * n
    free = [c for c in range(n) if c not in piv]
    for c in free:
        x[c] = guess[c]
    for i, c in enumerate(piv):
        x[c] = aug[i][n] - sum(aug[i][f] * x[f] for f in free)
    return x


def certificate(nv, cons, tgt, degs):
    """cons: list of exact linear polys; tgt: exact poly. Returns (deg, [(combo, coeff)])."""
    for deg in degs:
        ms = monos(nv, deg)
        idx = {m: k for k, m in enumerate(ms)}
        combos, cols = [()], [{(): F(1)}]
        for d in range(1, deg + 1):
            for combo in itertools.combinations_with_replacement(range(len(cons)), d):
                p = {(): F(1)}
                for k in combo:
                    p = pmul(p, cons[k])
                combos.append(combo)
                cols.append(p)
        M = np.zeros((len(ms), len(cols)))
        for j, p in enumerate(cols):
            for m, c in p.items():
                M[idx[m], j] = float(c)
        b = np.zeros(len(ms))
        for m, c in tgt.items():
            b[idx[m]] = float(c)
        res = linprog(np.ones(len(cols)), A_eq=M, b_eq=b, bounds=(0, None), method='highs')
        if res.status != 0:
            continue
        sup = [j for j in range(len(cols)) if res.x[j] > 1e-9]
        Mx = [[cols[j].get(m, F(0)) for j in sup] for m in ms]
        bx = [tgt.get(m, F(0)) for m in ms]
        for den in (1, 2, 4, 8, 16, 48, 240, 5040, 10 ** 6):
            guess = [F(float(res.x[j])).limit_denominator(den) for j in sup]
            x = gauss_solve(Mx, bx, guess)
            if x is not None and all(v >= 0 for v in x):
                # exact check of the identity
                tot = {}
                for j, v in zip(sup, x):
                    tot = padd(tot, {m: c * v for m, c in cols[j].items()})
                assert padd(tot, tgt, -1) == {}, 'identity check failed'
                return deg, [(combos[j], v) for j, v in zip(sup, x) if v != 0]
        raise SystemExit('LP support found but no exact nonnegative solution on it')
    return None


def lean_lemma(name, varnames, cons, goal, cert):
    """A Lean theorem with hypotheses `0 <= g_i` and conclusion `goal`."""
    lines = ['theorem %s (%s : ℝ)' % (name, ' '.join(varnames))]
    for i, g in enumerate(cons):
        lines.append('    (h%d : 0 ≤ %s)' % (i, lean_lin(g, varnames)))
    lines[-1] += ' :'
    lines.append('    %s := by' % goal)
    hints = []
    for combo, _ in cert:
        if len(combo) < 2:
            continue
        t = 'h%d' % combo[0]
        for k in combo[1:]:
            t = 'mul_nonneg (%s) h%d' % (t, k) if t.startswith('mul') else 'mul_nonneg %s h%d' % (t, k)
        hints.append(t)
    body = '  linarith [' + ',\n    '.join(hints) + ']'
    return '\n'.join(lines) + '\n' + body + '\n'


# ---- claim 1: variables y1 y2 y3 a ----

def claim1():
    V = ['y1', 'y2', 'y3', 'a']
    y1, y2, y3, a = range(4)
    base = [linpoly(0, {a: 1}), linpoly(F(1, 2), {a: -1}),
            linpoly(0, {y1: 1}), linpoly(1, {y1: -1}), linpoly(0, {y2: 1}), linpoly(1, {y2: -1}),
            linpoly(0, {y3: 1}), linpoly(1, {y3: -1}),
            linpoly(F(3, 2), {y1: -1, y2: -1, y3: -1}), linpoly(F(3, 2), {a: -1, y1: -1, y2: -1})]
    W = {'A': linpoly(1, {a: -1, y1: -1}),   # y1 <= 1 - a   (escape of corner 100)
         'B': linpoly(0, {a: -1, y2: 1}),    # y2 >= a       (escape of corner 100)
         'C': linpoly(0, {a: -1, y3: 1}),    # y3 >= a       (escape of both)
         'D': linpoly(0, {a: -1, y1: 1}),    # y1 >= a       (escape of corner 010)
         'E': linpoly(1, {a: -1, y2: -1})}   # y2 <= 1 - a   (escape of corner 010)
    pieces = ['AD', 'AE', 'AC', 'BD', 'BE', 'BC', 'C']
    out = []
    for pc in pieces:
        cons = base + [W[c] for c in pc]
        for e1, e2 in itertools.product((0, 1), repeat=2):
            d = [linpoly(0, {y1: 1, a: -e1}), linpoly(0, {y2: 1, a: -e2}), linpoly(0, {y3: 1, a: -1})]
            tgt = {(): F(5, 4)}
            for g in d:
                tgt = padd(tgt, pmul(g, g), -1)
            found = certificate(4, cons, tgt, (2, 3, 4))
            assert found, ('claim 1', pc, e1, e2)
            goal = '(%s) ^ 2 + (%s) ^ 2 + (y3 - a) ^ 2 ≤ 5 / 4' % (
                'y1 - a' if e1 else 'y1', 'y2 - a' if e2 else 'y2')
            name = 'c1_%s_%d%d' % (pc, e1, e2)
            print('%s: degree %d, %d terms' % (name, found[0], len(found[1])), flush=True)
            out.append(lean_lemma(name, V, cons, goal, found[1]))
    return out


# ---- claim 2: variables y1 y2 y3 z1 z2 z3 a ----

def claim2():
    V = ['y1', 'y2', 'y3', 'z1', 'z2', 'z3', 'a']
    A = 6

    def piece(off, kind):
        x1, x2, x3 = off, off + 1, off + 2
        cube = [linpoly(0, {x1: 1}), linpoly(1, {x1: -1}), linpoly(0, {x2: 1}), linpoly(1, {x2: -1}),
                linpoly(0, {x3: 1}), linpoly(1, {x3: -1})]
        ssum = linpoly(F(-3, 2), {x1: 1, x2: 1, x3: 1})
        if kind == 'p1':   # x1 least, sum >= 3/2, x3 >= a
            return cube + [linpoly(0, {x1: -1, x2: 1}), linpoly(0, {x1: -1, x3: 1}), ssum,
                           linpoly(0, {A: -1, x3: 1})]
        if kind == 'p2':   # x2 least, sum >= 3/2, x3 >= a
            return cube + [linpoly(0, {x2: -1, x1: 1}), linpoly(0, {x2: -1, x3: 1}), ssum,
                           linpoly(0, {A: -1, x3: 1})]
        esc = [linpoly(0, {x3: -1, x1: 1}), linpoly(0, {x3: -1, x2: 1}),
               linpoly(0, {A: -1, x1: 1}), linpoly(0, {A: -1, x2: 1}), linpoly(1, {A: -1, x3: -1})]
        if kind == 'p3s':  # x3 least, x1 >= a, x2 >= a, x3 <= 1 - a, sum >= 3/2
            return cube + esc + [ssum]
        return cube + esc + [linpoly(F(-3, 2), {A: 1, x1: 1, x2: 1})]  # p3t: x1 + x2 >= 3/2 - a

    tgt = {(): F(5, 4)}
    for i in range(3):
        g = linpoly(0, {i: 1, 3 + i: -1})
        tgt = padd(tgt, pmul(g, g), -1)
    goal = '(y1 - z1) ^ 2 + (y2 - z2) ^ 2 + (y3 - z3) ^ 2 ≤ 5 / 4'
    out = []
    for name, ky, kz in (('c2_p1', 'p1', 'p1'), ('c2_p2', 'p2', 'p2'), ('c2_p3_ss', 'p3s', 'p3s'),
                         ('c2_p3_st', 'p3s', 'p3t'), ('c2_p3_tt', 'p3t', 'p3t')):
        cons = [linpoly(0, {A: 1}), linpoly(F(1, 2), {A: -1})] + piece(0, ky) + piece(3, kz)
        found = certificate(7, cons, tgt, (2, 3))
        assert found, name
        print('%s: degree %d, %d terms' % (name, found[0], len(found[1])), flush=True)
        out.append(lean_lemma(name, V, cons, goal, found[1]))
    return out


HEADER = '''/-
Polynomial inequalities for five points in the unit cube (Schaer 1966, pp. 271-274).

Generated by gen_n5.py. Each lemma bounds a squared distance by 5/4 on a polytope given by its
hypotheses, and is proved from products of those hypotheses.
-/
import Mathlib

set_option linter.unusedVariables false
set_option maxRecDepth 10000

namespace Packing.Cube5

'''

if __name__ == '__main__':
    lemmas = claim1() + claim2()
    open(sys.argv[1], 'w').write(HEADER + '\n'.join(lemmas) + '\nend Packing.Cube5\n')
    print('wrote %d lemmas to %s' % (len(lemmas), sys.argv[1]))
