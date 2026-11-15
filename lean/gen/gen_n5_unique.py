#!/opt/homebrew/bin/uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy", "scipy"]
# ///
"""Emit Packing/Cube5EqCert.lean: where the inequalities of the five-point proof are tight.

Every lemma has a polytope {g_i >= 0} and a squared distance d2 with d2 <= 5/4 on it, and
comes from an identity
    5/4 - d2 - G = c_0 + sum_k c_k * (product of constraints),   c_k >= 0,
where G >= 0 on the polytope. The hypothesis 5/4 <= d2 then gives G <= 0:
  * G = eps * (sum of the constraints tight at the one point where d2 = 5/4): that point;
  * G = a (1 - 2a) / 2 or G = a / 8: a statement about the parameter a;
  * G = a positive constant: no such point.
The support comes from a floating-point LP and the identity is checked in exact arithmetic
(functions of gen_n5.py).

usage: gen_n5_unique.py <output .lean>      (run from lean/gen; Linux only, 2 GB cap)
"""
import itertools
import sys
from fractions import Fraction as F

from gen_n5 import certificate, lean_lin, linpoly, padd, pmul


def sqdist_gap(terms):
    """5/4 - sum g^2 over the linear polynomials g."""
    t = {(): F(5, 4)}
    for g in terms:
        t = padd(t, pmul(g, g), -1)
    return t


def hints_of(cert):
    out = []
    for combo, _ in cert:
        if len(combo) < 2:
            continue
        t = 'h%d' % combo[0]
        for k in combo[1:]:
            t = 'mul_nonneg (%s) h%d' % (t, k) if t.startswith('mul') else 'mul_nonneg %s h%d' % (t, k)
        out.append(t)
    return ',\n      '.join(out)


def head(name, doc, V, cons, d2):
    lines = ['/-- %s -/' % doc, 'theorem %s (%s : ℝ)' % (name, ' '.join(V))]
    lines += ['    (h%d : 0 ≤ %s)' % (i, lean_lin(g, V)) for i, g in enumerate(cons)]
    lines.append('    (hd : 5 / 4 ≤ %s) :' % d2)
    return lines


def point_lemma(name, doc, V, cons, sq, active, d2, degs=(2, 3, 4)):
    """5/4 <= d2 forces the constraints `active` to be equalities."""
    L = {}
    for k in active:
        L = padd(L, cons[k])
    for eps in (F(1, 2), F(1, 4), F(1, 8), F(1, 16), F(1, 64), F(1, 256)):
        found = certificate(len(V), cons, padd(sqdist_gap(sq), {m: c * eps for m, c in L.items()}, -1), degs)
        if found:
            break
    assert found, name
    print('%s: point, eps %s, degree %d, %d terms' % (name, eps, found[0], len(found[1])), flush=True)
    lines = head(name, doc, V, cons, d2)
    lines.append('    %s := by' % ' ∧ '.join('%s = 0' % lean_lin(cons[k], V) for k in active))
    lines.append('  have hL : %s ≤ 0 := by' % lean_lin(L, V))
    lines.append('    linarith [' + hints_of(found[1]) + ']')
    lines.append('  exact ⟨%s⟩' % ', '.join(['by linarith'] * len(active)))
    return '\n'.join(lines) + '\n'


def bound_lemma(name, doc, V, cons, sq, G, concl, d2, degs=(2, 3, 4)):
    """5/4 <= d2 gives `concl`, which is G <= 0 written out (or False for a constant G)."""
    found = certificate(len(V), cons, padd(sqdist_gap(sq), G, -1), degs)
    if not found:
        return None
    print('%s: %s, degree %d, %d terms' % (name, concl, found[0], len(found[1])), flush=True)
    lines = head(name, doc, V, cons, d2)
    lines.append('    %s := by' % concl)
    lines.append('  linarith [' + hints_of(found[1]) + ']')
    return '\n'.join(lines) + '\n'


# ---- a = 0 ----

def hexagon():
    V = ['u', 'v', 'w']
    u, v, w = range(3)
    cons = [linpoly(0, {w: 1}), linpoly(0, {v: 1, w: -1}), linpoly(0, {u: 1, v: -1}),
            linpoly(1, {u: -1}), linpoly(F(3, 2), {u: -1, v: -1, w: -1})]
    return point_lemma('hexagon_gap',
                       'A point `(u, v, w)` of the cube with `u ≥ v ≥ w`, `u + v + w ≤ 3/2` and '
                       'squared norm at least `5/4` is `(1, 1/2, 0)`.',
                       V, cons, [linpoly(0, {u: 1}), linpoly(0, {v: 1}), linpoly(0, {w: 1})],
                       [0, 3, 4], 'u ^ 2 + v ^ 2 + w ^ 2')


def same_part():
    V = ['y1', 'y2', 'y3', 'z1', 'z2', 'z3']
    y1, y2, y3, z1, z2, z3 = range(6)

    def point(a, b, c):
        return [linpoly(0, {a: 1}), linpoly(1, {a: -1}), linpoly(0, {b: 1}), linpoly(1, {b: -1}),
                linpoly(0, {c: 1}), linpoly(1, {c: -1}),
                linpoly(0, {a: -1, b: 1}), linpoly(0, {a: -1, c: 1}),
                linpoly(F(-3, 2), {a: 1, b: 1, c: 1})]

    cons = point(y1, y2, y3) + point(z1, z2, z3) + [
        linpoly(0, {y1: 1, y2: 1, y3: 1, z1: -1, z2: -1, z3: -1}), linpoly(0, {z2: -1, z3: 1})]
    return point_lemma('same_part_gap',
                       'Two points of the cube with least coordinate the first, coordinate sums at '
                       'least `3/2`, the first point with the larger sum, at squared distance at least '
                       '`5/4`: the first point is `(1, 1, 1)`.',
                       V, cons, [linpoly(0, {y1 + i: 1, z1 + i: -1}) for i in range(3)], [1, 3, 5],
                       '(y1 - z1) ^ 2 + (y2 - z2) ^ 2 + (y3 - z3) ^ 2')


# ---- claim 1 with the parameter a ----

PIECES = ['AD', 'AE', 'AC', 'BD', 'BE', 'BC', 'C']


def claim1_param():
    V = ['y1', 'y2', 'y3', 'a']
    y1, y2, y3, a = range(4)
    base = [linpoly(0, {a: 1}), linpoly(F(1, 2), {a: -1}),
            linpoly(0, {y1: 1}), linpoly(1, {y1: -1}), linpoly(0, {y2: 1}), linpoly(1, {y2: -1}),
            linpoly(0, {y3: 1}), linpoly(1, {y3: -1}),
            linpoly(F(3, 2), {y1: -1, y2: -1, y3: -1}), linpoly(F(3, 2), {a: -1, y1: -1, y2: -1})]
    W = {'A': linpoly(1, {a: -1, y1: -1}), 'B': linpoly(0, {a: -1, y2: 1}),
         'C': linpoly(0, {a: -1, y3: 1}), 'D': linpoly(0, {a: -1, y1: 1}),
         'E': linpoly(1, {a: -1, y2: -1})}
    G = {(a,): F(1, 2), (a, a): F(-1)}  # a (1 - 2a) / 2
    out = []
    for pc in PIECES:
        cons = base + [W[c] for c in pc]
        for e1, e2 in itertools.product((0, 1), repeat=2):
            sq = [linpoly(0, {y1: 1, a: -e1}), linpoly(0, {y2: 1, a: -e2}), linpoly(0, {y3: 1, a: -1})]
            d2 = '(%s) ^ 2 + (%s) ^ 2 + (y3 - a) ^ 2' % ('y1 - a' if e1 else 'y1', 'y2 - a' if e2 else 'y2')
            lem = bound_lemma('c1a_%s_%d%d' % (pc, e1, e2),
                              'On this piece of the region of the first claim, a point at squared '
                              'distance at least `5/4` from the corner of the square forces `a = 0` or '
                              '`a = 1/2`.', V, cons, sq, G, 'a * (1 - 2 * a) ≤ 0', d2)
            assert lem, (pc, e1, e2)
            out.append(lem)
    return out


# ---- claim 1 at a = 1/2 ----

def claim1_half():
    V = ['y1', 'y2', 'y3']
    y1, y2, y3 = range(3)
    base = [linpoly(0, {y1: 1}), linpoly(1, {y1: -1}), linpoly(0, {y2: 1}), linpoly(1, {y2: -1}),
            linpoly(0, {y3: 1}), linpoly(1, {y3: -1}),
            linpoly(F(3, 2), {y1: -1, y2: -1, y3: -1}), linpoly(1, {y1: -1, y2: -1})]
    h = F(1, 2)
    W = {'A': linpoly(h, {y1: -1}), 'B': linpoly(-h, {y2: 1}), 'C': linpoly(-h, {y3: 1}),
         'D': linpoly(-h, {y1: 1}), 'E': linpoly(h, {y2: -1})}
    out = []
    for pc in PIECES:
        cons = base + [W[c] for c in pc]
        for e1, e2 in itertools.product((0, 1), repeat=2):
            sq = [linpoly(-h * e1, {y1: 1}), linpoly(-h * e2, {y2: 1}), linpoly(-h, {y3: 1})]
            d2 = '(%s) ^ 2 + (%s) ^ 2 + (y3 - 1 / 2) ^ 2' % ('y1 - 1 / 2' if e1 else 'y1',
                                                           'y2 - 1 / 2' if e2 else 'y2')
            name = 'c1h_%s_%d%d' % (pc, e1, e2)
            doc = ('The first claim at `a = 1/2` on this piece: no point at squared distance at least '
                   '`5/4` from the corner of the square.')
            lem = bound_lemma(name, doc, V, cons, sq, {(): F(1, 64)}, 'False', d2)
            if lem is None:
                # the one tight point: (1, 0, 1/2) for e = 01, (0, 1, 1/2) for e = 10
                assert e1 != e2 and 'C' in pc, (pc, e1, e2)
                tight = {y1: F(1), y2: F(0), y3: h} if (e1, e2) == (0, 1) else {y1: F(0), y2: F(1), y3: h}
                val = [g.get((), F(0)) + sum(c * tight[m[0]] for m, c in g.items() if m) for g in cons]
                assert all(v >= 0 for v in val), (pc, e1, e2)
                act = ([1, 2] if (e1, e2) == (0, 1) else [0, 3]) + [6, cons.index(W['C'])]
                assert all(val[k] == 0 for k in act)
                lem = point_lemma(name, 'The first claim at `a = 1/2` is tight at one point of this '
                                  'piece.', V, cons, sq, act, d2)
            out.append(lem)
    return out


# ---- the third part with the parameter a ----

def part3_param():
    V = ['y1', 'y2', 'y3', 'z1', 'z2', 'z3', 'a']
    A = 6

    def piece(off, kind):
        x1, x2, x3 = off, off + 1, off + 2
        cube = [linpoly(0, {x1: 1}), linpoly(1, {x1: -1}), linpoly(0, {x2: 1}), linpoly(1, {x2: -1}),
                linpoly(0, {x3: 1}), linpoly(1, {x3: -1})]
        esc = [linpoly(0, {x3: -1, x1: 1}), linpoly(0, {x3: -1, x2: 1}),
               linpoly(0, {A: -1, x1: 1}), linpoly(0, {A: -1, x2: 1}), linpoly(1, {A: -1, x3: -1})]
        last = linpoly(F(-3, 2), {x1: 1, x2: 1, x3: 1}) if kind == 's' else linpoly(F(-3, 2), {A: 1, x1: 1, x2: 1})
        return cube + esc + [last]

    sq = [linpoly(0, {i: 1, 3 + i: -1}) for i in range(3)]
    out = []
    for ky, kz in (('s', 's'), ('s', 't'), ('t', 't')):
        cons = [linpoly(0, {A: 1}), linpoly(F(1, 2), {A: -1})] + piece(0, ky) + piece(3, kz)
        lem = None
        for kappa in (F(1, 8), F(1, 16), F(1, 32)):
            lem = bound_lemma('c3a_%s%s' % (ky, kz),
                              'Two points of the third part at squared distance at least `5/4` force '
                              '`a = 0`.', V, cons, sq, {(A,): kappa}, 'a ≤ 0',
                              '(y1 - z1) ^ 2 + (y2 - z2) ^ 2 + (y3 - z3) ^ 2', degs=(2, 3))
            if lem:
                break
        assert lem, (ky, kz)
        out.append(lem)
    return out


HEADER = '''/-
Where the inequalities of the five-point proof are tight (Schaer 1966, pp. 271-274).

Generated by gen/gen_n5_unique.py. Each lemma takes a squared distance of at least `5/4` on a
polytope and concludes that the point is the one extremal point of the polytope, or that the
parameter `a` is at an end of its range, or that there is no such point.
-/
import Mathlib

set_option linter.unusedVariables false
set_option maxRecDepth 10000

namespace Packing.Cube5

'''

if __name__ == '__main__':
    lemmas = [hexagon(), same_part()] + claim1_param() + claim1_half() + part3_param()
    open(sys.argv[1], 'w').write(HEADER + '\n'.join(lemmas) + '\nend Packing.Cube5\n')
    print('wrote %d lemmas to %s' % (len(lemmas), sys.argv[1]))
