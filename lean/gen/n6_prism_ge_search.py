#!/opt/homebrew/bin/uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy", "scipy"]
# ///
"""The prism lemma of the six-point proof with non-strict distances.

Three points of [0,1] x [0,1] x [0,1/4] in the quadrants 00, 10, 01 of the square, pairwise at
squared distance at least 9/8, do not all have third coordinate below 1/4. Looks for
    sum_p lam_p * (9/8 - d_p^2) = sum_k c_k * (product of constraints) + G,
    G = (1/4 - z0) (1/4 - z1) (1/4 - z2),
with lam_p a nonnegative combination of products of at most 2 constraints and c_k >= 0.
Float LP only. Writes the support to n6_prism_ge_support.json for gen_n6_prism_ge.py.
Run from lean/gen (imports n6_prism_search.py). Linux only, 2 GB cap.
"""
import json

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix

from n6_prism_search import PAIRS, constraints, gap, pmul, products, quadrant


def search(d1, d2, extra, dump):
    cons = constraints() + list(extra)
    lam, lnames = products(cons, d1)
    rhs, rnames = products(cons, d2)
    cols = []
    for (i, j) in PAIRS:
        g = gap(i, j)
        cols += [pmul(l, g) for l in lam]
    nl = len(cols)
    cols += [{m: -c for m, c in p.items()} for p in rhs]
    G = {(): 1.0}
    for v in (2, 5, 8):
        G = pmul(G, {(): 0.25, (v,): -1.0})
    idx = {}
    for p in cols + [G]:
        for m in p:
            idx.setdefault(m, len(idx))
    M = lil_matrix((len(idx), len(cols)))
    for j, p in enumerate(cols):
        for m, c in p.items():
            M[idx[m], j] = c
    b = np.zeros(len(idx))
    for m, c in G.items():
        b[idx[m]] = c
    res = linprog(np.ones(len(cols)), A_eq=M.tocsr(), b_eq=b, bounds=(0, None), method='highs')
    print('multipliers degree %d, products degree %d: %s (%d rows, %d columns)'
          % (d1, d2, 'FEASIBLE' if res.status == 0 else 'infeasible', len(idx), len(cols)), flush=True)
    if res.status != 0:
        return False
    mult = [(PAIRS[k // len(lam)], lnames[k % len(lam)], float(res.x[k]))
            for k in range(nl) if res.x[k] > 1e-9]
    prod = [(rnames[k - nl], float(res.x[k])) for k in range(nl, len(cols)) if res.x[k] > 1e-9]
    json.dump({'d1': d1, 'd2': d2, 'ncons': len(cons), 'multipliers': mult, 'products': prod},
              open(dump, 'w'))
    print('support: %d multiplier terms, %d product terms' % (len(mult), len(prod)), flush=True)
    return True


if __name__ == '__main__':
    extra = quadrant(0, 0, 0) + quadrant(1, 1, 0) + quadrant(2, 0, 1)
    for d1, d2 in ((1, 3), (2, 4)):
        if search(d1, d2, extra, 'n6_prism_ge_support.json'):
            break
