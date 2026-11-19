"""Search for Cube10 case-analysis trees (integer coordinates scaled by S = 1024).

A tree closes a state of ten boxes. Emitted nodes (preorder), matching Packing.Cube10Check:
  ('sp', slot, m)      split slot at m: left [lo, m], right [m, hi]
  ('pr', i, j)         pair leaf
  ('lp', w, ks)        weighted vertex-bound leaf
"""
import sys, math, itertools
S = 1024
MINCUT = 0
T16 = 9 * S * S  # 16 * md^2 sums must be <= this

def tr(v):
    return v if v > 0 else 0

def md(B, s, t):
    return max(tr(B[s][1] - B[t][0]), tr(B[t][1] - B[s][0]))

def pair_ok(B, i, j):
    return 16 * sum(md(B, 3 * i + c, 3 * j + c) ** 2 for c in range(3)) <= T16

class Ctx:
    def __init__(self):
        self.cuts = []      # each cut: dict(deps=[ids], needed=False)
        self.nodes = 0
        self.lpfail = 0

def dyadic_split(lo, hi):
    step = 1024
    while step >= 1:
        m = ((lo // step) + 1) * step
        if m < hi:
            # choose the multiple of step closest to the midpoint
            mid = (lo + hi) / 2
            cands = [c * step for c in range(lo // step + 1, (hi - 1) // step + 1)]
            return min(cands, key=lambda c: abs(c - mid))
        step //= 2
    return (lo + hi) // 2

def isqrt(n):
    return math.isqrt(n) if n >= 0 else -1

# ---- vertex bound (exact, mirrors Lean vmax) ----
def vmax_exact(B, c, w, ks):
    best = -1
    vals = []
    for k in ks:
        vals.append((B[3 * k + c][0], B[3 * k + c][1]))
    for choice in itertools.product((0, 1), repeat=len(ks)):
        y = {k: vals[n][choice[n]] for n, k in enumerate(ks)}
        tot = 0
        for (i, j, l) in w:
            d = y[i] - y[j]
            tot += l * d * d
        if tot > best:
            best = tot
    return best

def lp_exact_ok(B, w, ks):
    ws = sum(l for _, _, l in w)
    if ws <= 0:
        return False
    tot = sum(vmax_exact(B, c, w, ks) for c in range(3))
    return 16 * tot <= 9 * S * S * ws

def mind2(B, i, j):
    t = 0
    for c in range(3):
        a0, a1 = B[3 * i + c]; b0, b1 = B[3 * j + c]
        g = max(0, a0 - b1, b0 - a1)
        t += g * g
    return t

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

def exact_lam(r, Ds, V, pairs, pts, loc, B, P):
    from fractions import Fraction as Fr
    import numpy as np
    lam = r.x[:P]; t = r.x[P:P + 3]
    sup = [e for e in range(P) if lam[e] > 1e-11]
    if not sup:
        return None
    rowsM, rowsb = [], []
    for c in range(3):
        q = Ds[c] @ lam
        act = np.where(q > t[c] - 1e-10)[0]
        for k in act[:400]:
            v = V[k]
            row = []
            for e in sup:
                i, j = pairs[e]
                xi = Fr(B[3 * i + c][1] if v[loc[i]] else B[3 * i + c][0], S)
                xj = Fr(B[3 * j + c][1] if v[loc[j]] else B[3 * j + c][0], S)
                row.append((xi - xj) ** 2)
            row += [Fr(-1) if cc == c else Fr(0) for cc in range(3)]
            rowsM.append(row); rowsb.append(Fr(0))
    rowsM.append([Fr(1)] * len(sup) + [Fr(0)] * 3); rowsb.append(Fr(1))
    if r.fun > 9 / 16 - 1e-9:
        rowsM.append([Fr(0)] * len(sup) + [Fr(1)] * 3); rowsb.append(Fr(9, 16))
    guess = [Fr(float(lam[e])).limit_denominator(10 ** 6) for e in sup] + \
        [Fr(float(x)).limit_denominator(10 ** 6) for x in t]
    x = gauss_solve(rowsM, rowsb, guess)
    if x is None or any(v < 0 for v in x[:len(sup)]):
        return None
    import math
    den = 1
    for v in x[:len(sup)]:
        den = den * v.denominator // math.gcd(den, v.denominator)
    w = [(pairs[e][0], pairs[e][1], int(v * den)) for e, v in zip(sup, x[:len(sup)]) if v > 0]
    if not w:
        return None
    ks = sorted(set([i for i, _, _ in w] + [j for _, j, _ in w]))
    if lp_exact_ok(B, w, ks):
        return ('lp', w, ks)
    return None

def lp_find(B, n=10):
    import numpy as np
    from scipy.optimize import linprog
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n) if 16 * mind2(B, i, j) < T16 * 1.3]
    if not pairs:
        return None
    pts = sorted(set([i for i, _ in pairs] + [j for _, j in pairs]))
    n = len(pts)
    loc = {k: a for a, k in enumerate(pts)}
    P = len(pairs)
    V = np.array(list(itertools.product((0, 1), repeat=n)), float)
    Ds = []
    for c in range(3):
        lo = np.array([B[3 * k + c][0] for k in pts], float) / S
        hi = np.array([B[3 * k + c][1] for k in pts], float) / S
        X = lo + V * (hi - lo)
        Ds.append(np.stack([(X[:, loc[i]] - X[:, loc[j]]) ** 2 for (i, j) in pairs], axis=1))
    nv = V.shape[0]
    A_ub = []
    for c in range(3):
        A = np.zeros((nv, P + 3)); A[:, :P] = Ds[c]; A[:, P + c] = -1
        A_ub.append(A)
    A_ub = np.vstack(A_ub)
    A_eq = np.zeros((1, P + 3)); A_eq[0, :P] = 1
    cobj = np.zeros(P + 3); cobj[P:] = 1
    r = linprog(cobj, A_ub=A_ub, b_ub=np.zeros(A_ub.shape[0]), A_eq=A_eq, b_eq=[1],
                bounds=[(0, None)] * P + [(None, None)] * 3, method='highs')
    if r.status != 0 or r.fun > 9 / 16 + 1e-9:
        return None
    cands = [r.x[:P]]
    if r.fun > 9 / 16 - 1e-4:
        # robust phase: maximize delta with Q_c(v) + delta * hamming(v, v0_c) <= t_c
        lam = r.x[:P]
        A2 = []
        for c in range(3):
            q = Ds[c] @ lam
            v0 = V[int(np.argmax(q))]
            h = np.abs(V - v0).sum(axis=1)
            A = np.zeros((nv, P + 4)); A[:, :P] = Ds[c]; A[:, P + c] = -1; A[:, P + 3] = h
            A2.append(A)
        A2 = np.vstack(A2)
        row = np.zeros((1, P + 4)); row[0, :P] = -9 / 16; row[0, P:P + 3] = 1
        A2 = np.vstack([A2, row])
        Aeq2 = np.zeros((1, P + 4)); Aeq2[0, :P] = 1
        c2 = np.zeros(P + 4); c2[P + 3] = -1
        r2 = linprog(c2, A_ub=A2, b_ub=np.zeros(A2.shape[0]), A_eq=Aeq2, b_eq=[1],
                     bounds=[(0, None)] * P + [(None, None)] * 3 + [(0, 1)], method='highs')
        if r2.status == 0 and r2.x[P + 3] > 1e-12:
            cands.insert(0, r2.x[:P])
    ex = exact_lam(r, Ds, V, pairs, pts, loc, B, P)
    if ex is not None:
        return ex
    for lam in cands:
        for scale in (1024, 1 << 14, 1 << 20, 1 << 26):
            w = []
            for (i, j), v in zip(pairs, lam):
                l = int(round(v * scale))
                if l > 0:
                    w.append((i, j, l))
            if not w:
                continue
            ks = sorted(set([i for i, _, _ in w] + [j for _, j, _ in w]))
            if lp_exact_ok(B, w, ks):
                return ('lp', w, ks)
    return None
    lam = r.x[:P]
    for scale in (64, 256, 1024, 4096, 16384):
        w = []
        for (i, j), v in zip(pairs, lam):
            l = int(round(v * scale))
            if l > 0:
                w.append((i, j, l))
        if not w:
            continue
        ks = sorted(set([i for i, _, _ in w] + [j for _, j, _ in w]))
        if lp_exact_ok(B, w, ks):
            return ('lp', w, ks)
    return None

# ---- search ----
class Fail(Exception):
    pass

def search(B, prov, ctx, use_lp, limit, depth=0):
    """B: list of 30 [lo,hi]; prov: list of 30 [plo, phi] provenance cut ids (or None).
    Returns a tree: ('sp', slot, m, L, R) | ('pr', i, j, deps) | ('lp', w, ks, deps) |
    ('cut', slot, t, side, i, j, cutid, child)."""
    ctx.nodes += 1
    if ctx.nodes > limit:
        raise Fail('limit')
    n = 10
    def deps_of(pts, skip=None):
        d = []
        for p in pts:
            for c in range(3):
                for side in (0, 1):
                    if skip == (3 * p + c, side):
                        continue
                    v = prov[3 * p + c][side]
                    if v is not None:
                        d.append(v)
        return d
    for i in range(n):
        for j in range(i + 1, n):
            if pair_ok(B, i, j):
                return ('pr', i, j, deps_of([i, j]))
    # propagation, one cut at a time (recursive so that provenance is tracked)
    for j in range(n):
        for i in range(n):
            if i == j:
                continue
            for c in range(3):
                sj, si = 3 * j + c, 3 * i + c
                other = sum(md(B, 3 * i + d, 3 * j + d) ** 2 for d in range(3) if d != c)
                rem = T16 - 16 * other
                if rem < 0:
                    continue
                r = isqrt(rem // 16)
                lo, hi = B[sj]
                if B[si][1] - lo <= r:
                    t = B[si][0] + r
                    if t > lo + MINCUT and t < hi:
                        cid = len(ctx.cuts)
                        ctx.cuts.append({'deps': deps_of([i, j]), 'needed': False})
                        B2 = [list(b) for b in B]; P2 = [list(p) for p in prov]
                        B2[sj][0] = t; P2[sj][0] = cid
                        child = search(B2, P2, ctx, use_lp, limit, depth + 1)
                        return ('cut', sj, t, 0, i, j, cid, child)
                if hi - B[si][0] <= r:
                    t = B[si][1] - r
                    if t < hi - MINCUT and t > lo:
                        cid = len(ctx.cuts)
                        ctx.cuts.append({'deps': deps_of([i, j]), 'needed': False})
                        B2 = [list(b) for b in B]; P2 = [list(p) for p in prov]
                        B2[sj][1] = t; P2[sj][1] = cid
                        child = search(B2, P2, ctx, use_lp, limit, depth + 1)
                        return ('cut', sj, t, 1, i, j, cid, child)
    if use_lp:
        wmax = max(B[s][1] - B[s][0] for s in range(30))
        if wmax <= use_lp:
            res = lp_find(B)
            if res is not None:
                return ('lp', res[1], res[2], deps_of(res[2]))
            ctx.lpfail += 1
    # branch on the widest slot
    wd, s = max((B[s][1] - B[s][0], s) for s in range(30))
    if wd <= 2:
        raise Fail(('small', B))
    m = dyadic_split(B[s][0], B[s][1])
    B1 = [list(b) for b in B]; B1[s][1] = m
    B2 = [list(b) for b in B]; B2[s][0] = m
    L = search(B1, [list(p) for p in prov], ctx, use_lp, limit, depth + 1)
    R = search(B2, [list(p) for p in prov], ctx, use_lp, limit, depth + 1)
    return ('sp', s, m, L, R)

def mark(tree, ctx):
    stack = [tree]
    need = []
    while stack:
        t = stack.pop()
        if t[0] == 'sp':
            stack += [t[3], t[4]]
        elif t[0] == 'cut':
            stack.append(t[7])
        else:
            need += t[-1]
    while need:
        c = need.pop()
        if not ctx.cuts[c]['needed']:
            ctx.cuts[c]['needed'] = True
            need += ctx.cuts[c]['deps']

def emit(tree, ctx, out):
    stack = [tree]
    while stack:
        t = stack.pop()
        if t[0] == 'sp':
            out.append(('sp', t[1], t[2]))
            stack.append(t[4]); stack.append(t[3])
        elif t[0] == 'pr':
            out.append(('pr', t[1], t[2]))
        elif t[0] == 'lp':
            out.append(('lp', t[1], t[2]))
        else:
            _, slot, tt, side, i, j, cid, child = t
            if not ctx.cuts[cid]['needed']:
                stack.append(child)
                continue
            out.append(('ct', slot, tt, i, j, side))
            stack.append(child)

# ---- exact replay of the Lean checker ----
def replay(nodes, B0):
    stk = [B0]
    for nd in nodes:
        if not stk:
            return False
        B = stk.pop()
        if nd[0] == 'sp':
            _, s, m = nd
            L = [list(b) for b in B]; L[s][1] = m
            R = [list(b) for b in B]; R[s][0] = m
            stk.append(R); stk.append(L)
        elif nd[0] == 'pr':
            if not (nd[1] != nd[2] and pair_ok(B, nd[1], nd[2])):
                return False
        elif nd[0] == 'ct':
            _, s, m, i, j, side = nd
            L = [list(b) for b in B]; L[s][1] = m
            R = [list(b) for b in B]; R[s][0] = m
            kill, keep = (L, R) if side == 0 else (R, L)
            if not (i != j and pair_ok(kill, i, j)):
                return False
            stk.append(keep)
        else:
            if not lp_exact_ok(B, nd[1], nd[2]):
                return False
    return not stk

def keybox(g):
    qx, qy, k = g % 2, (g // 2) % 2, g // 4
    return [[qx * 512, qx * 512 + 512], [qy * 512, qy * 512 + 512], [k * 256, k * 256 + 256]]

def root(pat):
    B = []
    for g in pat:
        B += keybox(g)
    return B

def solve(pat, use_lp=0, limit=200000):
    sys.setrecursionlimit(100000)
    ctx = Ctx()
    B = root(pat)
    tree = search(B, [[None, None] for _ in range(30)], ctx, use_lp, limit)
    mark(tree, ctx)
    out = []
    emit(tree, ctx, out)
    assert replay(out, root(pat)), 'replay failed'
    return out, ctx

if __name__ == '__main__':
    import random, time
    random.seed(1)
    MINCUT = int(sys.argv[2])
    pats = list(itertools.combinations(range(16), 10))
    tot = 0
    for pat in random.sample(pats, int(sys.argv[1])):
        t0 = time.time()
        try:
            out, ctx = solve(list(pat))
            tot += len(out)
            print(pat, 'nodes', len(out), 'searched', ctx.nodes, 'cuts', len(ctx.cuts),
                  'needed', sum(c['needed'] for c in ctx.cuts), '%.1fs' % (time.time() - t0), flush=True)
        except Fail as e:
            print(pat, 'FAIL', e, flush=True)
    print('total', tot)

def lean_nodes(out):
    parts = []
    for nd in out:
        if nd[0] == 'sp':
            parts.append('.sp %d %d' % (nd[1], nd[2]))
        elif nd[0] == 'pr':
            parts.append('.pr %d %d' % (nd[1], nd[2]))
        elif nd[0] == 'ct':
            parts.append('.ct %d %d %d %d %s' % (nd[1], nd[2], nd[3], nd[4], 'true' if nd[5] else 'false'))
        else:
            parts.append('.lp [%s] [%s]' % (', '.join('(%d, %d, %d)' % e for e in nd[1]),
                                            ', '.join(str(k) for k in nd[2])))
    return '[' + ', '.join(parts) + ']'

def lean_root(pat):
    return '[' + ', '.join('(%d, %d)' % tuple(b) for b in root(pat)) + ']'


def encode(out):
    code = 0
    lps = []
    for k, nd in enumerate(out):
        if nd[0] == 'sp':
            v = 0 | (nd[1] << 3) | (nd[2] << 8)
        elif nd[0] == 'pr':
            v = 1 | (nd[1] << 19) | (nd[2] << 23)
        elif nd[0] == 'ct':
            _, s_, m, i, j, side = nd
            v = (3 if side else 2) | (s_ << 3) | (m << 8) | (i << 19) | (j << 23)
        else:
            v = 4 | (len(lps) << 8)
            lps.append(nd)
        assert v < (1 << 27)
        code |= v << (27 * k)
    assert len(lps) < 2048
    return code, len(out), lps

def lean_ent(pat, out):
    code, fuel, lps = encode(out)
    lpl = lean_nodes(lps)
    return '⟨[%s], 0x%x, %d, %s⟩' % (', '.join(map(str, pat)), code, fuel, lpl)
