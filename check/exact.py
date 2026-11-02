"""Exact evaluation of the four objectives (Python standard library only).

Every coordinate in a submission file is a finite decimal string, so it is an
exact rational. Each file is read into integer vectors at one common power of
ten; all distances, inner products and norms are then exact integers, and every
comparison against a threshold is made between exact rationals (squared where
the definition has a square root). Decimal arithmetic at 60 digits is used only
to print the value.

Definitions:
  grassmannian  d2 = min_{i<j} n - ||U_i^T U_j||_F^2 with U_i an orthonormal
                basis of the span of block i; computed exactly as
                n - tr(P_i P_j), P_i = A_i^T (A_i A_i^T)^{-1} A_i.  (max)
  sloanes       mu = max_{j<k} |<phi_j, phi_k>| / (|phi_j| |phi_k|).    (min)
  hsp4          r* = min( min_{i<j} |c_i - c_j| / 2, 1 - max_i |c_i| ),
                unit ball centred at the origin.                         (max)
  scu           r* = min( min_{i<j} |c_i - c_j| / 2,
                          1/2 - max_i max_k |c_ik| ), cube [-1/2,1/2]^3. (max)
"""
from decimal import Decimal, getcontext
from fractions import Fraction

getcontext().prec = 60


# ---------------------------------------------------------------- parsing

def to_fraction(s):
    return Fraction(Decimal(s))


def scale_rows(rows):
    """rows of decimal strings -> (integer rows, scale) with value = int / scale."""
    exps = []
    for r in rows:
        for s in r:
            e = Decimal(s).as_tuple().exponent
            exps.append(-e if e < 0 else 0)
    k = max(exps) if exps else 0
    scale = 10 ** k
    out = []
    for r in rows:
        out.append([int(Decimal(s).scaleb(k)) for s in r])
        for s, v in zip(r, out[-1]):
            assert Decimal(v) == Decimal(s).scaleb(k), 'non-exact scaling'
    return out, scale


def read_grassmannian(path, m, n, N):
    head, rows = [], []
    for line in open(path):
        s = line.strip()
        if not s:
            continue
        if s.startswith('#'):
            head.append(s)
            continue
        f = s.split(',')
        if len(f) != m:
            raise ValueError('row with %d entries, expected m = %d' % (len(f), m))
        rows.append([x.strip() for x in f])
    if len(rows) != n * N:
        raise ValueError('%d rows, expected n*N = %d' % (len(rows), n * N))
    return head, rows


def read_sloanes(path, d, n):
    vals = []
    for line in open(path):
        s = line.strip()
        if not s:
            raise ValueError('blank line')
        if len(s.split()) != 1:
            raise ValueError('more than one number on a line')
        vals.append(s)
    if len(vals) != 2 * d * n:
        raise ValueError('%d numbers, expected 2dn = %d' % (len(vals), 2 * d * n))
    return vals


def read_packomania(path, dim, N, radius_column):
    """First line: radius. Then '#' lines (optional). Then N rows: index, dim coords[, radius]."""
    lines = [l.rstrip('\n') for l in open(path)]
    first = lines[0].strip()
    rows, comments = [], []
    for l in lines[1:]:
        s = l.strip()
        if not s:
            continue
        if s.startswith('#'):
            comments.append(s)
            continue
        f = s.split()
        want = 1 + dim + (1 if radius_column else 0)
        if len(f) != want:
            raise ValueError('row with %d fields, expected %d' % (len(f), want))
        if int(f[0]) != len(rows) + 1:
            raise ValueError('index %s out of sequence' % f[0])
        rows.append(f[1:1 + dim])
    if len(rows) != N:
        raise ValueError('%d centre rows, expected N = %d' % (len(rows), N))
    return first, comments, rows


# ---------------------------------------------------------------- objectives

def _inv_adj(G):
    """Exact inverse of a symmetric positive definite integer matrix as
    (adjugate integer matrix H, determinant g), G^{-1} = H / g."""
    n = len(G)
    M = [[Fraction(G[i][j]) for j in range(n)] + [Fraction(int(i == j)) for j in range(n)] for i in range(n)]
    det = Fraction(1)
    for c in range(n):
        p = next(r for r in range(c, n) if M[r][c] != 0)
        if p != c:
            M[c], M[p] = M[p], M[c]
            det = -det
        piv = M[c][c]
        det *= piv
        M[c] = [x / piv for x in M[c]]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c]
                M[r] = [a - f * b for a, b in zip(M[r], M[c])]
    assert det.denominator == 1 and det > 0
    g = det.numerator
    H = [[M[i][n + j] * g for j in range(n)] for i in range(n)]
    for row in H:
        for x in row:
            assert x.denominator == 1
    return [[x.numerator for x in row] for row in H], g


def grassmannian(rows, m, n, N):
    """Exact minimum squared chordal distance (Fraction) and the attaining pair."""
    A, _ = scale_rows(rows)            # common scale cancels in projections
    blocks = [A[i * n:(i + 1) * n] for i in range(N)]
    best, arg = None, None
    if n == 1:
        v = [b[0] for b in blocks]
        nn = [sum(x * x for x in a) for a in v]
        assert all(x > 0 for x in nn)
        # d2 = 1 - (a.b)^2/(|a|^2|b|^2); minimise d2 = maximise the ratio
        bp, bq = -1, 1
        for i in range(N):
            a = v[i]
            for j in range(i + 1, N):
                b = v[j]
                ip = sum(x * y for x, y in zip(a, b))
                p, q = ip * ip, nn[i] * nn[j]
                if p * bq > bp * q:
                    bp, bq, arg = p, q, (i + 1, j + 1)
        return 1 - Fraction(bp, bq), arg
    G = [[[sum(x * y for x, y in zip(b[r], b[c])) for c in range(n)] for r in range(n)] for b in blocks]
    HG = [_inv_adj(g) for g in G]
    for i in range(N):
        Ai, (Hi, gi) = blocks[i], HG[i]
        for j in range(i + 1, N):
            Aj, (Hj, gj) = blocks[j], HG[j]
            C = [[sum(x * y for x, y in zip(Ai[r], Aj[c])) for c in range(n)] for r in range(n)]
            X = [[sum(Hi[r][k] * C[k][c] for k in range(n)) for c in range(n)] for r in range(n)]
            Y = [[sum(X[r][k] * Hj[k][c] for k in range(n)) for c in range(n)] for r in range(n)]
            # tr(Y C^T) = sum_{r,c} Y[r][c] C[r][c]
            t = sum(Y[r][c] * C[r][c] for r in range(n) for c in range(n))
            val = n - Fraction(t, gi * gj)
            if best is None or val < best:
                best, arg = val, (i + 1, j + 1)
    return best, arg


def sloanes_mu2(vals, d, n):
    """Exact mu^2 (Fraction) and the attaining pair; vectors are read as
    re = vals[j*d:(j+1)*d], im = vals[d*n + j*d : d*n + (j+1)*d]."""
    X, _ = scale_rows([vals])
    X = X[0]
    re = [X[j * d:(j + 1) * d] for j in range(n)]
    im = [X[d * n + j * d:d * n + (j + 1) * d] for j in range(n)]
    nn = [sum(a * a for a in re[j]) + sum(b * b for b in im[j]) for j in range(n)]
    assert all(x > 0 for x in nn)
    bp, bq, arg = -1, 1, None
    for j in range(n):
        for k in range(j + 1, n):
            R = sum(a * c + b * e for a, b, c, e in zip(re[j], im[j], re[k], im[k]))
            I = sum(a * e - b * c for a, b, c, e in zip(re[j], im[j], re[k], im[k]))
            p, q = R * R + I * I, nn[j] * nn[k]
            if p * bq > bp * q:
                bp, bq, arg = p, q, (j + 1, k + 1)
    return Fraction(bp, bq), arg


def _min_sq_dist(P):
    best, arg = None, None
    N = len(P)
    for i in range(N):
        a = P[i]
        for j in range(i + 1, N):
            s = sum((x - y) * (x - y) for x, y in zip(a, P[j]))
            if best is None or s < best:
                best, arg = s, (i + 1, j + 1)
    return best, arg


def hsp4(rows):
    """Exact parts: (D, M) with min squared distance D and max squared norm M (Fractions)."""
    P, sc = scale_rows(rows)
    D, arg = _min_sq_dist(P)
    M = max(sum(x * x for x in p) for p in P)
    return Fraction(D, sc * sc), Fraction(M, sc * sc), arg


def scu(rows):
    """Exact parts: (D, A) with min squared distance D and max |coordinate| A (Fractions)."""
    P, sc = scale_rows(rows)
    D, arg = _min_sq_dist(P)
    A = max(abs(x) for p in P for x in p)
    return Fraction(D, sc * sc), Fraction(A, sc), arg


# ---------------------------------------------------------------- printing

def dec(fr):
    return Decimal(fr.numerator) / Decimal(fr.denominator)


def dsqrt(fr):
    return dec(fr).sqrt()


def hsp4_value(D, M):
    return min(dsqrt(D) / 2, 1 - dsqrt(M))


def scu_value(D, A):
    return min(dsqrt(D) / 2, Decimal('0.5') - dec(A))


# exact threshold tests -------------------------------------------------------

def hsp4_at_least(D, M, T):
    """r* >= T exactly (0 < T < 1)."""
    return D >= 4 * T * T and M <= (1 - T) * (1 - T)


def scu_at_least(D, A, T):
    """r* >= T exactly (0 < T < 1/2)."""
    return D >= 4 * T * T and A <= Fraction(1, 2) - T


def hsp4_at_most(D, M, T):
    """r* <= T exactly."""
    return D <= 4 * T * T or M >= (1 - T) * (1 - T)


def scu_at_most(D, A, T):
    return D <= 4 * T * T or A >= Fraction(1, 2) - T
