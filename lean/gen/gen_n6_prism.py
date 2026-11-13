#!/opt/homebrew/bin/python3
"""Emit the Lean lemma for Schaer's Proposition 1 (N = 6), quadrant case, strict form.

Reads the support found by n6_prism_search.py (n6_prism_support.json), solves for exact rational coefficients on
that support, checks the identity
    sum_p lam_p * (9/8 - d_p^2) = sum_k c_k * (product of constraints)
with fractions, and writes the lemma. Standard library only.

usage: gen_n6_prism.py gen/n6_prism_support.json Packing/Cube6Prism.lean
"""
import json
import sys
from fractions import Fraction as F

NAMES = ['x0', 'y0', 'z0', 'x1', 'y1', 'z1', 'x2', 'y2', 'z2']
PAIRS = [(0, 1), (0, 2), (1, 2)]


def pmul(p, q):
    r = {}
    for m1, c1 in p.items():
        for m2, c2 in q.items():
            m = tuple(sorted(m1 + m2))
            r[m] = r.get(m, 0) + c1 * c2
    return {m: c for m, c in r.items() if c != 0}


def padd(p, q, s=1):
    r = dict(p)
    for m, c in q.items():
        r[m] = r.get(m, 0) + s * c
        if r[m] == 0:
            del r[m]
    return r


def constraints():
    """Same order as n6_prism_search.py: the prism, then the quadrants 00, 10, 01."""
    cons = []
    for i in range(3):
        for c, hi in ((0, F(1)), (1, F(1)), (2, F(1, 4))):
            v = 3 * i + c
            cons.append({(v,): F(1)})
            cons.append({(): hi, (v,): F(-1)})
    for i, qx, qy in ((0, 0, 0), (1, 1, 0), (2, 0, 1)):
        for c, q in ((0, qx), (1, qy)):
            v = 3 * i + c
            lo = {(v,): F(1)}
            if q:
                lo[()] = F(-q, 2)
            cons.append(lo)
            cons.append({(): F(q + 1, 2), (v,): F(-1)})
    return cons


def gap(i, j):
    p = {(): F(9, 8)}
    for c in range(3):
        g = {(3 * i + c,): F(1), (3 * j + c,): F(-1)}
        p = padd(p, pmul(g, g), -1)
    return p


def prod(cons, combo):
    p = {(): F(1)}
    for k in combo:
        p = pmul(p, cons[k])
    return p


def gauss_solve(M, b, guess):
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


def lean_lin(p):
    items = [(m, c) for m, c in p.items() if m == ()] + sorted((m, c) for m, c in p.items() if m != ())
    out = ''
    for m, c in items:
        mag = abs(c)
        body = str(mag) if m == () else (NAMES[m[0]] if mag == 1 else '%s * %s' % (mag, NAMES[m[0]]))
        out = (body if c > 0 else '-' + body) if out == '' else out + (' + ' if c > 0 else ' - ') + body
    return out


def nonneg(hyps, combo):
    t = hyps[combo[0]]
    for k in combo[1:]:
        t = 'mul_nonneg (%s) %s' % (t, hyps[k]) if ' ' in t else 'mul_nonneg %s %s' % (t, hyps[k])
    return t


def main():
    r = json.load(open(sys.argv[1]))
    cons = constraints()
    assert r['ncons'] == len(cons)
    mult = [(tuple(p), tuple(n), x) for p, n, x in r['multipliers']]
    prods = [(tuple(n), x) for n, x in r['products']]
    cols = [pmul(prod(cons, n), gap(*p)) for p, n, _ in mult]
    cols += [{m: -c for m, c in prod(cons, n).items()} for n, _ in prods]
    monos = sorted({m for p in cols for m in p})
    M = [[p.get(m, F(0)) for p in cols] for m in monos]
    M.append([F(1)] * len(mult) + [F(0)] * len(prods))  # the normalization of n6_prism_search.py
    b = [F(0)] * len(monos) + [F(1)]
    floats = [x for _, _, x in mult] + [x for _, x in prods]
    x = None
    for den in (10 ** 4, 10 ** 6, 10 ** 8):
        guess = [F(v).limit_denominator(den) for v in floats]
        x = gauss_solve(M, b, guess)
        if x is not None and all(v >= 0 for v in x):
            break
        x = None
    assert x is not None, 'no exact nonnegative solution on the support'
    tot = {}
    for p, v in zip(cols, x):
        tot = padd(tot, {m: c * v for m, c in p.items()})
    assert tot == {}, 'identity check failed'
    lam = {(p, n): v for (p, n, _), v in zip(mult, x) if v != 0}
    y1sq, hy1sq = ((0, 2), (8, 8)), ((0, 1), (25, 25))  # y1^2 on pair (0,2), (1/2 - y1)^2 on pair (0,1)
    assert lam.get(y1sq, 0) > 0 and lam.get(hy1sq, 0) > 0, 'strictness terms missing'
    print('exact certificate: %d multiplier terms, %d product terms, max denominator %d'
          % (len(lam), sum(1 for v in x[len(mult):] if v != 0), max(v.denominator for v in x)))

    canon = {}
    hyps, hyp_lines = {}, []
    for k, g in enumerate(cons):
        key = tuple(sorted(g.items()))
        if key not in canon:
            canon[key] = 'g%d' % len(canon)
            hyp_lines.append('    (%s : 0 ≤ %s)' % (canon[key], lean_lin(g)))
        hyps[k] = canon[key]
    dist = {p: '(x%d - x%d) ^ 2 + (y%d - y%d) ^ 2 + (z%d - z%d) ^ 2' % (p[0], p[1], p[0], p[1], p[0], p[1])
            for p in PAIRS}
    hp = {p: 'h%d%d' % p for p in PAIRS}
    hints = []
    for (p, n), v in lam.items():
        hints.append('mul_nonneg (%s) (sub_nonneg.mpr %s.le)' % (nonneg(hyps, n), hp[p]))
    for (n, _), v in zip(prods, x[len(mult):]):
        if v != 0 and len(n) >= 2:
            hints.append(nonneg(hyps, n))
    body = ',\n      '.join(hints)
    y1 = hyps[8]
    out = '''/-
Three points of the prism `[0,1] x [0,1] x [0,1/4]` in three given quadrants of the square are
not pairwise at squared distance more than `9/8` (Schaer 1966, pp. 275-280, Proposition 1).

Generated by gen/gen_n6_prism.py. The proof multiplies each `d^2 - 9/8` by a nonnegative polynomial
and compares the sum with a nonnegative combination of products of the constraints.
-/
import Mathlib

set_option linter.unusedVariables false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Packing.Cube6

theorem prism_quadrants (%s : ℝ)
%s
    (h01 : 9 / 8 < %s)
    (h02 : 9 / 8 < %s)
    (h12 : 9 / 8 < %s) : False := by
  by_cases hy : 0 < y1
  · have s := mul_pos (mul_pos hy hy) (sub_pos.mpr h02)
    linarith [s,
      %s]
  · have hy0 : (0 : ℝ) < 1 / 2 - y1 := by linarith
    have s := mul_pos (mul_pos hy0 hy0) (sub_pos.mpr h01)
    linarith [s,
      %s]

end Packing.Cube6
''' % (' '.join(NAMES), '\n'.join(hyp_lines), dist[(0, 1)], dist[(0, 2)], dist[(1, 2)], body, body)
    open(sys.argv[2], 'w').write(out)
    print('wrote', sys.argv[2], '(%d hints)' % len(hints))


main()
