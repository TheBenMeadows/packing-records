"""Re-check every file listed in ../cells.csv (Python standard library only).

For each row: the file exists, its sha256 matches, it parses in its table's own
layout, its value recomputed exactly (exact.py) equals the recorded value, and
the keep rules hold on exact rationals:
  grassmannian     row not starred and not noted optimal; value >= table + 1e-7
                   + 1e-10 (the table rounds values down to 10 decimals);
                   value < bound - 1e-8 when a bound is listed; every stored
                   basis is orthonormal to within 1e-20
  game-of-sloanes  row not provably optimal; mu <= table - 1e-7; mu >= lower
                   bound; every stored vector has unit norm to within 1e-15
  packomania-hsp4  r* >= max over listed N' >= N of r(N') + 1e-7, and
                   r* >= recorded polish floor + 1e-7
  packomania-scu   r* >= B(N) + 1e-7 with B(N) = max over listed N' >= N of
                   r(N'), r* >= recorded polish floor + 1e-7, and every row's
                   radius column equals the first-line radius
Table facts are read from tables/ and must equal the cells.csv columns. Each
(table, cell) appears once, every file in the four output folders is listed,
and the per-table counts match EXPECTED. The polish floor is a recorded number:
this script checks the margin over it, and floor/polish.py recomputes it from
the posted Packomania files. The last line printed is PASS or FAIL.
"""
import csv, hashlib, os, sys
from decimal import Decimal
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
FINAL = os.path.dirname(HERE)
DATA = os.path.join(FINAL, 'tables')
sys.path.insert(0, HERE)
import exact  # noqa: E402

E7, E8, E10 = Fraction(1, 10 ** 7), Fraction(1, 10 ** 8), Fraction(1, 10 ** 10)
TOL = Decimal('1e-35')
EXPECTED = {'grassmannian': 731, 'game-of-sloanes': 52, 'packomania-hsp4': 108, 'packomania-scu': 159}
FOLDERS = ('grassmannian', 'game-of-sloanes', 'packomania-hsp4', 'packomania-scu')


def tsv(fn):
    rows = []
    with open(os.path.join(DATA, fn), encoding='utf-8') as fh:
        lines = [l.rstrip('\n') for l in fh if l.strip() and not l.startswith('#')]
    head = lines[0].split('\t')
    for l in lines[1:]:
        rows.append(dict(zip(head, l.split('\t'))))
    return rows


def cohn():
    return {(int(r['m']), int(r['n']), int(r['N'])): r for r in tsv('cohn_grassmannian.tsv')}


def sloanes():
    return {(int(r['d']), int(r['n'])): r for r in tsv('game_of_sloanes.tsv')}


def radius_table(fn):
    t = {}
    with open(os.path.join(DATA, fn)) as fh:
        for line in fh:
            f = line.split()
            if len(f) >= 2 and f[0].isdigit():
                t[int(f[0])] = f[1]
    return t


def suffix_max(table):
    out, best = {}, Fraction(0)
    for N in sorted(table, reverse=True):
        best = max(best, Fraction(Decimal(table[N])))
        out[N] = best
    return out


def check_grassmannian(r, full, C):
    msg = []
    m, n, N = map(int, r['cell'].split('-'))
    if r['file'] != 'grassmannian/%d-%d-%d.txt' % (m, n, N):
        msg.append('file name does not match the cell')
    row = C[(m, n, N)]
    if row['starred'] == 'yes' or row['noted_optimal'] == 'yes':
        msg.append('row starred or noted optimal')
    if row['value'] != r['table_value']:
        msg.append('table value differs from tables/')
    head, data = exact.read_grassmannian(full, m, n, N)
    if exact.orthonormal_defect(data, n, N) > Fraction(1, 10 ** 20):
        msg.append('a stored basis is not orthonormal')
    val, _ = exact.grassmannian(data, m, n, N)
    vd = exact.dec(val)
    if not val >= Fraction(Decimal(row['value'])) + E7 + E10:
        msg.append('does not beat table by 1e-7')
    if row['bound'] and not val < Fraction(Decimal(row['bound'])) - E8:
        msg.append('within 1e-8 of bound (or above it)')
    return msg, vd


def check_sloanes(r, full, T):
    msg = []
    d, n = map(int, r['cell'].split('-'))
    if r['file'] != 'game-of-sloanes/%dx%d.txt' % (d, n):
        msg.append('file name does not match the cell')
    row = T[(d, n)]
    if row['provably_optimal'] == 'yes':
        msg.append('row provably optimal')
    if row['coherence'] != r['table_value'] or row['lower_bound'] != r['bound']:
        msg.append('table value or lower bound differs from tables/')
    vals = exact.read_sloanes(full, d, n)
    if exact.unit_norm_defect(vals, d, n) > Fraction(1, 10 ** 15):
        msg.append('a stored vector is not unit length')
    mu2, _ = exact.sloanes_mu2(vals, d, n)
    vd = exact.dec(mu2).sqrt()
    target = Fraction(Decimal(row['coherence'])) - E7
    if target <= 0 or not mu2 <= target ** 2:
        msg.append('does not beat table by 1e-7')
    if not mu2 >= Fraction(Decimal(row['lower_bound'])) ** 2:
        msg.append('below the listed lower bound')
    return msg, vd


def check_packomania(r, full, tab, tables):
    msg = []
    N = int(r['cell'])
    hs = tab == 'packomania-hsp4'
    if r['file'] != ('packomania-hsp4/hsp4-%d.txt' % N if hs else 'packomania-scu/scu%d.txt' % N):
        msg.append('file name does not match the cell')
    radii, bmax = tables[tab]
    first, _, data = exact.read_packomania(full, 4 if hs else 3, N, radius_column=not hs)
    if radii[N] != r['table_value']:
        msg.append('table value differs from tables/')
    if hs:
        D, M, _ = exact.hsp4(data)
        vd = exact.hsp4_value(D, M)
        ge = lambda x: x < 1 and exact.hsp4_at_least(D, M, x)
    else:
        D, A, _ = exact.scu(data)
        vd = exact.scu_value(D, A)
        ge = lambda x: x < Fraction(1, 2) and exact.scu_at_least(D, A, x)
        if Decimal(r['bound']) != exact.dec(bmax[N]):
            msg.append('B(N) column differs')
    hv = Decimal(first)
    if not (hv <= vd and vd - hv < Decimal('1e-29')):
        msg.append('first-line radius inconsistent with the coordinates')
    if not ge(bmax[N] + E7):
        msg.append('does not beat max over N\' >= N of the table by 1e-7')
    if not r['floor']:
        msg.append('no polish floor')
    elif not ge(Fraction(Decimal(r['floor'])) + E7):
        msg.append('does not beat polish floor by 1e-7')
    return msg, vd


def main():
    C, T = cohn(), sloanes()
    tables = {}
    for tab, fn in (('packomania-hsp4', 'packomania_hsp4_radius.txt'), ('packomania-scu', 'packomania_scu_radius.txt')):
        radii = radius_table(fn)
        tables[tab] = (radii, suffix_max(radii))
    with open(os.path.join(FINAL, 'cells.csv')) as fh:
        rows = list(csv.DictReader(fh))
    fails, listed, seen, count = [], set(), set(), {}
    for r in rows:
        tab, cell, path = r['table'], r['cell'], r['file']
        msg = []
        if (tab, cell) in seen or path in listed:
            msg.append('duplicate row')
        seen.add((tab, cell))
        listed.add(path)
        full = os.path.join(FINAL, path)
        try:
            with open(full, 'rb') as fh:
                if hashlib.sha256(fh.read()).hexdigest() != r['file_sha256']:
                    msg.append('sha256 mismatch')
            if tab == 'grassmannian':
                m2, vd = check_grassmannian(r, full, C)
            elif tab == 'game-of-sloanes':
                m2, vd = check_sloanes(r, full, T)
            elif tab in tables:
                m2, vd = check_packomania(r, full, tab, tables)
            else:
                raise ValueError('unknown table %r' % tab)
            msg += m2
            if abs(vd - Decimal(r['our_value'])) > TOL:
                msg.append('recorded value %s, recomputed %s' % (r['our_value'], vd))
        except Exception as e:  # malformed file or table row
            msg.append('error: %r' % (e,))
        count[tab] = count.get(tab, 0) + 1
        if msg:
            fails.append((tab, cell, msg))
            print('FAIL', tab, cell, '; '.join(msg))
        else:
            print('ok', tab, cell, r['our_value'])
    for sub in FOLDERS:
        for fn in sorted(os.listdir(os.path.join(FINAL, sub))):
            if fn.startswith('.'):
                continue
            if '%s/%s' % (sub, fn) not in listed:
                fails.append((sub, fn, ['not listed']))
                print('FAIL', sub, fn, 'not listed in cells.csv')
    if count != EXPECTED:
        fails.append(('counts', '', ['%r != %r' % (count, EXPECTED)]))
        print('FAIL counts', count, 'expected', EXPECTED)
    print('rows', len(rows), ' '.join('%s=%d' % kv for kv in sorted(count.items())), 'failures', len(fails))
    print('PASS' if not fails else 'FAIL')
    return 0 if not fails else 1


if __name__ == '__main__':
    try:
        sys.exit(main())
    except Exception as e:  # unreadable tables/ or cells.csv
        print('FAIL error: %r' % (e,))
        print('FAIL')
        sys.exit(1)
