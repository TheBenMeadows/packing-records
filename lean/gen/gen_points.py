#!/opt/homebrew/bin/python3
"""Write the Lean certificate files for the point tables.

Usage: gen_points.py [--lists] [--split] [TABLE[:CELL] ...]

Tables: spherical-codes, game-of-sloanes, packomania-hsp4, packomania-hsp5,
packomania-hsp6, packomania-scu. Reads cells.csv and the data files from the
repository root and writes, under lean/:

  Packing/Cert/Cells/<P>_<cell>.lean   one per cell: the points of the file as
                                       integer data and one theorem,
                                       `check... = true`, closed by kernel
                                       evaluation (P = S, G, H4, H5, H6, U)
  Packing/Cert/AllPoints.lean          two theorems per cell: a configuration
                                       exists, and the data (the stated number
                                       of vectors, each with the stated number
                                       of entries) are one
  points_manifest.tsv                  table, cell, module, t, table value t,
                                       sha256 of the data file, cost

With no argument every cell of the six tables is written. With arguments only
the named tables or cells are written, and AllPoints.lean and the manifest are
left as they are. With --lists alone, AllPoints.lean and the manifest are
written and the cell files are left as they are.

The Lean data of a cell are the numbers of its file multiplied by one power of
ten. Each data file must have the sha256 that cells.csv records.

A threshold is an integer t that stands for t / 10^12. For the spherical codes
and the Game of Sloanes it is the smallest t the Lean checker accepts (largest
cosine, coherence); for the Packomania tables the largest (radius). It must
agree with the cell's `our_value` to within one unit and must beat the table
value.
"""
import csv
import hashlib
import os
import sys
from decimal import Decimal
from fractions import Fraction
from math import isqrt

sys.dont_write_bytecode = True  # check/__pycache__ is tracked; leave it alone
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen_cert import LEAN, ROOT, exact  # noqa: E402

Q = 10 ** 12
BALL_DIM = {'packomania-hsp4': 4, 'packomania-hsp5': 5, 'packomania-hsp6': 6}
PREFIX = {'spherical-codes': 'S', 'game-of-sloanes': 'G', 'packomania-hsp4': 'H4',
          'packomania-hsp5': 'H5', 'packomania-hsp6': 'H6', 'packomania-scu': 'U'}


def lean_vec(w):
    """A Packing.Cert.Vec: entries shifted by `off` to be nonnegative."""
    off = 10 ** len(str(max(abs(x) for x in w)))
    e = [x + off for x in w]
    return '⟨[%s], %d, %d, %d⟩' % (', '.join(str(x) for x in e), off, sum(e),
                                   sum(x * x for x in w))


def lean_list(items):
    return '[\n' + ',\n'.join('  ' + x for x in items) + ']'


def pinned_sha(row):
    with open(os.path.join(ROOT, row['file']), 'rb') as f:
        digest = hashlib.sha256(f.read()).hexdigest()
    if digest != row['file_sha256']:
        raise SystemExit('%s: sha256 differs from cells.csv' % row['file'])
    return digest


def smallest_t(p, q):
    """The smallest t >= 0 with p * 10^24 <= t^2 * q (p >= 0, q > 0)."""
    t = isqrt(p * Q * Q // q)
    while t * t * q < p * Q * Q:
        t += 1
    return t


def largest_t(start, accepts):
    t = start
    while not accepts(Fraction(t, Q)):
        t -= 1
    return t


# A spherical code with N^2 d above SPLIT_COST is checked in blocks (CheckBlocks.lean): the
# kernel's memory grows with the number of pairs it evaluates in one theorem. The count of
# blocks keeps each block near BLOCK_COST.
SPLIT_COST = 12_500_000
BLOCK_COST = 2_500_000
FORCE_SPLIT = set()


def split_spherical(name, d, N, t, P):
    k = max(2, -(-isqrt(2 * N * N * d * 10000 // BLOCK_COST) // 100))
    size = -(-N // k)
    chunks = [P[i:i + size] for i in range(0, N, size)]
    if [p for ch in chunks for p in ch] != list(P) or not all(chunks):
        raise SystemExit('%s: the blocks do not concatenate to the data' % name)
    k = len(chunks)
    rel = '(cosB %d (Nat.mul %d %d) (Nat.pow 10 24))' % (d, t, t)
    out = []
    for i, ch in enumerate(chunks, 1):
        out.append('%sdef s_%s_%d : List Vec := %s\n'
                   % ('' if i == 1 else 'set_option maxRecDepth 100000 in\nnoncomputable ',
                      name, i, lean_list(lean_vec(p) for p in ch)))
    whole = ' ++ ('.join('s_%s_%d' % (name, i) for i in range(1, k + 1)) + ')' * (k - 1)
    out.append('noncomputable def s_%s : List Vec := %s\n' % (name, whole))
    out.append('theorem ok_sph_%s_v : andB (Nat.beq (sumMap (fun _ => 1) s_%s) %d) '
               '(allB (okVec %d) s_%s) = true := by decide +kernel\n' % (name, name, N, d, name))
    for i in range(1, k + 1):
        out.append('theorem ok_sph_%s_p%d : pairwiseB %s s_%s_%d = true := by decide +kernel\n'
                   % (name, i, rel, name, i))
        for j in range(i + 1, k + 1):
            out.append('theorem ok_sph_%s_c%d_%d : crossB %s s_%s_%d s_%s_%d = true := by '
                       'decide +kernel\n' % (name, i, j, rel, name, i, name, j))

    def cross(i, js):
        head = 'ok_sph_%s_c%d_%d' % (name, i, js[0])
        return head if len(js) == 1 else 'crossB_append %s (%s)' % (head, cross(i, js[1:]))

    def pairs(i):
        if i == k:
            return 'ok_sph_%s_p%d' % (name, i)
        return 'pairwiseB_append ok_sph_%s_p%d (%s) (%s)' % (
            name, i, cross(i, list(range(i + 1, k + 1))), pairs(i + 1))

    out.append('set_option maxRecDepth 100000 in\n'
               'theorem ok_sph_%s : checkSph %d %d %d s_%s = true :=\n'
               '  checkSph_of_blocks ok_sph_%s_v (%s)\n' % (name, d, N, t, name, name, pairs(1)))
    return '\n'.join(out)


def spherical(row, path):
    d, N = (int(x) for x in row['cell'].split('-'))
    rows = exact.read_spherical(path, d, N)
    P, _ = exact.scale_rows(rows)
    s, q, _, _ = exact.spherical_max_cos(rows)
    if s <= 0:
        raise SystemExit('%s: the largest cosine is not positive' % row['cell'])
    t = smallest_t(s * s, q)
    name = '%d_%d' % (d, N)
    lean = ('def s_%s : List Vec := %s\n\n'
            'theorem ok_sph_%s : checkSph %d %d %d s_%s = true := by decide +kernel\n'
            % (name, lean_list(lean_vec(p) for p in P), name, d, N, t, name))
    if N * N * d > SPLIT_COST or row['cell'] in FORCE_SPLIT:
        lean = split_spherical(name, d, N, t, P)
    thms = [('sph_%s' % name, 'HasSphericalCode %d %d (%d / 10 ^ 12)' % (d, N, t),
             'hasSphericalCode_of_check Cells.ok_sph_%s' % name),
            ('sph_file_%s' % name,
             'SphericalData %d %d (%d / 10 ^ 12) Cells.s_%s' % (d, N, t, name),
             'sphericalData_of_check Cells.ok_sph_%s' % name)]
    return name, lean, thms, t, N * N * d


def sloanes(row, path):
    d, N = (int(x) for x in row['cell'].split('-'))
    vals = exact.read_sloanes(path, d, N)
    X = exact.scale_rows([vals])[0][0]
    mu2, _ = exact.sloanes_mu2(vals, d, N)
    t = smallest_t(mu2.numerator, mu2.denominator)
    name = '%d_%d' % (d, N)
    items = ['⟨%s, %s⟩' % (lean_vec(X[j * d:(j + 1) * d]),
                         lean_vec(X[d * N + j * d:d * N + (j + 1) * d])) for j in range(N)]
    lean = ('def g_%s : List CVec := %s\n\n'
            'theorem ok_gos_%s : checkCoh %d %d %d g_%s = true := by decide +kernel\n'
            % (name, lean_list(items), name, d, N, t, name))
    thms = [('gos_%s' % name, 'HasCoherence %d %d (%d / 10 ^ 12)' % (d, N, t),
             'hasCoherence_of_check Cells.ok_gos_%s' % name),
            ('gos_file_%s' % name,
             'CoherenceData %d %d (%d / 10 ^ 12) Cells.g_%s' % (d, N, t, name),
             'coherenceData_of_check Cells.ok_gos_%s' % name)]
    return name, lean, thms, t, 4 * N * N * d


def ball(row, path):
    dim, N = BALL_DIM[row['table']], int(row['cell'])
    _, _, rows = exact.read_packomania(path, dim, N, radius_column=False)
    P, S = exact.scale_rows(rows)
    D, M, _ = exact.hsp4(rows)
    t = largest_t(floor_scaled_q(row['our_value']) + 1, lambda T: exact.hsp4_at_least(D, M, T))
    name, tag = str(N), 'hsp%d' % dim
    lean = ('def h%d_%s : List Vec := %s\n\n'
            'theorem ok_%s_%s : checkBall %d %d %d %d h%d_%s = true := by decide +kernel\n'
            % (dim, name, lean_list(lean_vec(p) for p in P), tag, name, dim, N, t, S, dim, name))
    thms = [('%s_%s' % (tag, name), 'HasBallPackingInBall %d %d (%d / 10 ^ 12)' % (dim, N, t),
             'hasBallPackingInBall_of_check Cells.ok_%s_%s' % (tag, name)),
            ('%s_file_%s' % (tag, name),
             'BallData %d %d %d (%d / 10 ^ 12) Cells.h%d_%s' % (dim, N, S, t, dim, name),
             'ballData_of_check Cells.ok_%s_%s' % (tag, name))]
    return name, lean, thms, t, N * N * dim


def cube(row, path):
    N = int(row['cell'])
    _, _, rows = exact.read_packomania(path, 3, N, radius_column=True)
    P, S = exact.scale_rows(rows)
    D, A, _ = exact.scu(rows)
    t = largest_t(floor_scaled_q(row['our_value']) + 1, lambda T: exact.scu_at_least(D, A, T))
    name = str(N)
    lean = ('def u_%s : List Vec := %s\n\n'
            'theorem ok_scu_%s : checkCube %d %d %d u_%s = true := by decide +kernel\n'
            % (name, lean_list(lean_vec(p) for p in P), name, N, t, S, name))
    thms = [('scu_%s' % name, 'HasBallPackingInCube %d (%d / 10 ^ 12)' % (N, t),
             'hasBallPackingInCube_of_check Cells.ok_scu_%s' % name),
            ('scu_file_%s' % name, 'CubeData %d %d (%d / 10 ^ 12) Cells.u_%s' % (N, S, t, name),
             'cubeData_of_check Cells.ok_scu_%s' % name)]
    return name, lean, thms, t, N * N * 3


HANDLER = {'spherical-codes': spherical, 'game-of-sloanes': sloanes, 'packomania-hsp4': ball,
           'packomania-hsp5': ball, 'packomania-hsp6': ball, 'packomania-scu': cube}
SMALLER_IS_BETTER = ('spherical-codes', 'game-of-sloanes')


def check_row(row, t):
    """t agrees with our_value to one unit and beats the table value."""
    ours, listed = floor_scaled_q(row['our_value']), floor_scaled_q(row['table_value'])
    if row['table'] in SMALLER_IS_BETTER:
        ok, beats = t - ours in (0, 1), t < listed
    else:
        ok, beats = ours - t in (0, 1), t > listed
    if not ok:
        raise SystemExit('%s %s: t = %d disagrees with our_value %d'
                         % (row['table'], row['cell'], t, ours))
    if not beats:
        raise SystemExit('%s %s: t = %d does not beat the table value %d'
                         % (row['table'], row['cell'], t, listed))
    return listed


def floor_scaled_q(s):
    """floor(s * 10^12) for a decimal string."""
    return int((Decimal(s) * Q).to_integral_value(rounding='ROUND_FLOOR'))


def write_cell(outdir, row, write=True):
    sha = pinned_sha(row)
    name, lean, thms, t, cost = HANDLER[row['table']](row, os.path.join(ROOT, row['file']))
    imp = 'CheckBlocks' if 'crossB' in lean else 'CheckPoints'
    module = '%s_%s' % (PREFIX[row['table']], name)
    text = ('-- Generated by gen/gen_points.py from %s. Do not edit.\n'
            'import Packing.Cert.%s\n\n'
            'namespace Packing.Cert.Cells\n\n' % (row['file'], imp)) + (
            '-- The list literal nests deeper than the default limit of the elaborator.\n'
            '-- `noncomputable`: no executable code is generated for the data, which keeps the\n'
            '-- compiled file about nine times smaller. The kernel evaluates it all the same.\n'
            'set_option maxRecDepth 100000 in\n'
            'noncomputable %s\n'
            'end Packing.Cert.Cells\n' % lean)
    if write:
        with open(os.path.join(outdir, module + '.lean'), 'w') as f:
            f.write(text)
    return module, thms, t, check_row(row, t), sha, cost


def write_all(done):
    lines = ['-- Generated by gen/gen_points.py. Do not edit.', 'import Packing.Cert.SoundCoh']
    lines += ['import Packing.Cert.Cells.%s' % module for _, module, _, _, _, _, _ in done]
    lines += ['', 'namespace Packing.Cert', '']
    for _, _, thms, _, _, _, _ in done:
        for name, statement, proof in thms:
            lines += ['theorem %s : %s := by' % (name, statement),
                      '  simpa only [Nat.cast_ofNat] using %s' % proof, '']
    lines += ['end Packing.Cert', '']
    with open(os.path.join(LEAN, 'Packing', 'Cert', 'AllPoints.lean'), 'w') as f:
        f.write('\n'.join(lines))


def scope():
    """The cells named in cells_scope.txt (lines `table:cell`), or None when there is no such file.

    While the file exists, a run without arguments covers these cells only."""
    path = os.path.join(LEAN, 'cells_scope.txt')
    if not os.path.exists(path):
        return None
    return {l.strip() for l in open(path) if l.strip() and not l.startswith('#')}


def selected(rows, argv):
    if not argv:
        sc = scope()
        return [r for r in rows if r['table'] in HANDLER
                and (sc is None or '%s:%s' % (r['table'], r['cell']) in sc)]
    want = [a.split(':') for a in argv]
    return [r for r in rows
            if any(r['table'] == w[0] and (len(w) == 1 or r['cell'] == w[1]) for w in want)]


def main(argv):
    if argv[:1] == ['--split']:  # check the named cells in blocks whatever their size
        FORCE_SPLIT.update(a.split(':')[1] for a in argv[1:])
        argv = argv[1:]
    lists_only = argv == ['--lists']
    argv = [] if lists_only else argv
    rows = list(csv.DictReader(open(os.path.join(ROOT, 'cells.csv'))))
    outdir = os.path.join(LEAN, 'Packing', 'Cert', 'Cells')
    os.makedirs(outdir, exist_ok=True)
    done = []
    for row in selected(rows, argv):
        module, thms, t, listed, sha, cost = write_cell(outdir, row, write=not lists_only)
        done.append(('%s\t%s' % (row['table'], row['cell']), module, thms, t, listed, sha, cost))
    if argv:
        return 0
    write_all(done)
    with open(os.path.join(LEAN, 'points_manifest.tsv'), 'w') as f:
        f.write('table\tcell\tmodule\tt\ttable_t\tsha256\tcost\n')
        f.write(''.join('%s\t%s\t%d\t%d\t%s\t%d\n' % (key, module, t, listed, sha, cost)
                        for key, module, _, t, listed, sha, cost in done))
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
