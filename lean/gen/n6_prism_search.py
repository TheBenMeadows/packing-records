#!/opt/homebrew/bin/uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy", "scipy"]
# ///
"""Schaer's Proposition 1 for N = 6, strict form: three points of the prism
[0,1] x [0,1] x [0,1/4] are not pairwise at squared distance > 9/8.

Looks for a multiplier certificate with the three points in the quadrants 00, 10 and 01 of the
square (none exists on the whole prism at these degrees):
    sum_p lam_p * (9/8 - d_p^2) = c_0 + sum_k c_k * (product of constraints),
with lam_p = nonnegative combination of products of at most D1 constraints, c_k >= 0, and the
coefficients of the lam_p summing to 1. Float LP only. Writes the support of the solution to n6_prism_support.json, which
gen_n6_prism.py turns into exact coefficients and a Lean lemma. About 40 minutes.
Linux only, 2 GB address-space cap.
"""
import itertools
import resource
import sys

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix

assert sys.platform == 'linux', 'the memory cap below needs Linux'
resource.setrlimit(resource.RLIMIT_AS, (2 << 30, 2 << 30))

NV = 9  # x1 y1 z1 x2 y2 z2 x3 y3 z3
PAIRS = [(0, 1), (0, 2), (1, 2)]


def pmul(p, q):
    r = {}
    for m1, c1 in p.items():
        for m2, c2 in q.items():
            m = tuple(sorted(m1 + m2))
            r[m] = r.get(m, 0.0) + c1 * c2
    return r


def padd(p, q, s=1.0):
    r = dict(p)
    for m, c in q.items():
        r[m] = r.get(m, 0.0) + s * c
    return r


def constraints():
    cons = []
    for i in range(3):
        for c, hi in ((0, 1.0), (1, 1.0), (2, 0.25)):
            v = 3 * i + c
            cons.append({(v,): 1.0})
            cons.append({(): hi, (v,): -1.0})
    return cons


def gap(i, j):
    """9/8 - d(P_i, P_j)^2."""
    p = {(): 9 / 8}
    for c in range(3):
        g = {(3 * i + c,): 1.0, (3 * j + c,): -1.0}
        p = padd(p, pmul(g, g), -1.0)
    return p


def products(cons, deg):
    out, names = [{(): 1.0}], [()]
    for d in range(1, deg + 1):
        for combo in itertools.combinations_with_replacement(range(len(cons)), d):
            p = {(): 1.0}
            for k in combo:
                p = pmul(p, cons[k])
            out.append(p)
            names.append(combo)
    return out, names


def search(d1, d2, extra=(), dump=None):
    cons = constraints() + list(extra)
    lam, lnames = products(cons, d1)
    rhs, rnames = products(cons, d2)
    cols = []
    for (i, j) in PAIRS:
        g = gap(i, j)
        cols += [pmul(l, g) for l in lam]
    nl = len(cols)
    cols += [{m: -c for m, c in p.items()} for p in rhs]
    idx = {}
    for p in cols:
        for m in p:
            idx.setdefault(m, len(idx))
    M = lil_matrix((len(idx) + 1, len(cols)))
    for j, p in enumerate(cols):
        for m, c in p.items():
            M[idx[m], j] = c
    for k in range(nl):  # normalization: the multiplier coefficients sum to 1
        M[len(idx), k] = 1.0
    b = np.zeros(len(idx) + 1)
    b[len(idx)] = 1.0
    res = linprog(np.ones(len(cols)), A_eq=M.tocsr(), b_eq=b, bounds=(0, None), method='highs')
    if res.status == 0 and dump:
        import json
        mult = [(PAIRS[k // len(lam)], lnames[k % len(lam)], float(res.x[k]))
                for k in range(nl) if res.x[k] > 1e-9]
        prod = [(rnames[k - nl], float(res.x[k])) for k in range(nl, len(cols)) if res.x[k] > 1e-9]
        json.dump({'d1': d1, 'd2': d2, 'ncons': len(cons), 'multipliers': mult, 'products': prod},
                  open(dump, 'w'))
        print('   support: %d multiplier terms, %d product terms' % (len(mult), len(prod)), flush=True)
        for pr, nm, x in mult:
            print('   pair %s  %.6f  %s' % (pr, x, nm), flush=True)
    return res.status == 0, len(idx), len(cols), nl


def quadrant(i, qx, qy):
    """Point i has x in [qx/2, (qx+1)/2] and y in [qy/2, (qy+1)/2]."""
    out = []
    for c, q in ((0, qx), (1, qy)):
        v = 3 * i + c
        out.append({(): -q / 2, (v,): 1.0})
        out.append({(): (q + 1) / 2, (v,): -1.0})
    return out


if __name__ == '__main__':
    # points 0, 1, 2 in quadrants (0,0), (1,0), (0,1); quadrant (1,1) empty
    extra = quadrant(0, 0, 0) + quadrant(1, 1, 0) + quadrant(2, 0, 1)
    for d1, d2 in ((2, 4),):
        ok, rows, ncols, nl = search(d1, d2, extra, 'n6_prism_support.json')
        print('quadrants 00/10/01, multipliers degree %d, products degree %d: %s  (%d rows, %d columns)'
              % (d1, d2, 'FEASIBLE' if ok else 'infeasible', rows, ncols), flush=True)
        if ok:
            break
