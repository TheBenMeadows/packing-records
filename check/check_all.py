"""Re-check every file listed in ../cells.csv (Python standard library only).

For each row: the file exists, its sha256 matches, it parses in its table's own
layout, its value recomputed exactly (exact.py) equals the recorded value, and
the keep rules hold on exact rationals:
  grassmannian     row not starred and not noted optimal; value >= table + 1e-10
                   (the table rounds values down to 10 decimals, so this beats
                   the true table value and changes its printed last digit);
                   value < bound when a bound is listed (bounds are rounded
                   up); every stored basis is orthonormal to within 1e-20
  game-of-sloanes  row not provably optimal; mu <= table - 1e-7; mu >= lower
                   bound; every stored vector has unit norm to within 1e-15
  packomania-hsp4, packomania-hsp5, packomania-hsp6
                   (balls in the unit ball of dimension 4, 5, 6)
                   r* >= max over listed N' >= N of r(N') + 1e-7, and
                   r* >= recorded floor + 1e-7. A row with a table_read date is
                   checked against tables/packomania_<shelf>_radius_<date>.txt,
                   the table as it read on that day; a blank table_read means
                   the original snapshot (hsp4 only)
  packomania-scu   r* >= B(N) + 1e-7 with B(N) = max over listed N' >= N of
                   r(N'), r* >= recorded polish floor + 1e-7, and every row's
                   radius column equals the first-line radius
  cohn-harmonic    row not a simplex (N = n+1), cross polytope (N = 2n) or
                   listed universal optimum; every stored vector has unit norm
                   (|norm^2 - 1| <= 1e-20) and every coordinate has at least 25
                   significant digits; with bar = min(table energy, 2021 data-set
                   energy) and m = max(1e-9, 1e-12 E): E <= bar - m and the
                   recorded floor (the polished posted 2021 configuration)
                   >= E + m; the file header names the cell and its energy.
                   Squared distances are exact rationals; the energy is a
                   60-digit decimal evaluation from them (see exact.py), so every
                   harmonic comparison carries a 1e-40 safety margin. A row with
                   a table_read date is checked against
                   tables/cohn_harmonic_<date>.tsv; blank means the 2026-11-03 read
Every row's status is accepted, pending or not listed (at the table's keeper).
Rows are checked in parallel, one process per CPU; CHECK_WORKERS=<n> sets the
number of processes (1 = no subprocesses).
Table facts are read from tables/ and must equal the cells.csv columns. Each
(table, cell) appears once, every file in the five output folders is listed,
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
HSAFE = Decimal('1e-40')
EXPECTED = {'grassmannian': 1658, 'game-of-sloanes': 52, 'packomania-hsp4': 152, 'packomania-hsp5': 198,
            'packomania-hsp6': 161, 'packomania-scu': 239, 'cohn-harmonic': 44, 'spherical-codes': 4369, 'thomson': 1}
FOLDERS = ('grassmannian', 'game-of-sloanes', 'packomania-hsp4', 'packomania-hsp5', 'packomania-hsp6',
           'packomania-scu', 'cohn-harmonic',
           'spherical-codes', 'thomson')
E11, E6 = Fraction(1, 10 ** 11), Fraction(1, 10 ** 6)
BALL_DIM = {'hsp4': 4, 'hsp5': 5, 'hsp6': 6}
PACKOMANIA = ('packomania-hsp4', 'packomania-hsp5', 'packomania-hsp6', 'packomania-scu')
STATUSES = ('accepted', 'pending', 'not listed')


def tsv(fn):
    rows = []
    with open(os.path.join(DATA, fn), encoding='utf-8') as fh:
        lines = [l.rstrip('\n') for l in fh if l.strip() and not l.startswith('#')]
    head = lines[0].split('\t')
    for l in lines[1:]:
        rows.append(dict(zip(head, l.split('\t'))))
    return rows


def cohn(read=''):
    """The Grassmannian table as read on `read` (a cells.csv table_read date; blank = the 2026-11-01 snapshot)."""
    fn = 'cohn_grassmannian_%s.tsv' % read if read else 'cohn_grassmannian.tsv'
    return {(int(r['m']), int(r['n']), int(r['N'])): r for r in tsv(fn)}


def spherical_table(read):
    fn = os.path.join(DATA, 'spherical_codes_%s.csv' % read)
    with open(fn, encoding='utf-8') as fh:
        return {(int(r['d']), int(r['N'])): r for r in csv.DictReader(l for l in fh if not l.startswith('#'))}


def thomson_table(read):
    fn = os.path.join(DATA, 'thomson_%s.csv' % read)
    with open(fn, encoding='utf-8') as fh:
        return {int(r['N']): r for r in csv.DictReader(l for l in fh if not l.startswith('#'))}


def sloanes():
    return {(int(r['d']), int(r['n'])): r for r in tsv('game_of_sloanes.tsv')}


def harmonic_table(read=''):
    """The harmonic table as read on `read` (a cells.csv table_read date; blank = the 2026-11-03 snapshot)."""
    fn = 'cohn_harmonic_%s.tsv' % read if read else 'cohn_harmonic.tsv'
    # a tree without the harmonic table can still check the other tables;
    # any cohn-harmonic row then fails with a KeyError
    if not os.path.exists(os.path.join(DATA, fn)):
        return {}
    return {(int(r['N']), int(r['n'])): r for r in tsv(fn)}


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
    if not val >= Fraction(Decimal(row['value'])) + E10:
        msg.append('does not beat the table in its last printed digit')
    if row['bound'] and not val < Fraction(Decimal(row['bound'])):
        msg.append('not below the listed bound')
    return msg, vd


def check_spherical(r, full, S):
    msg = []
    d, N = map(int, r['cell'].split('-'))
    if r['file'] != 'spherical-codes/%d-%d.txt' % (d, N):
        msg.append('file name does not match the cell')
    row = S[(d, N)]
    if row['proven_optimal'] == 'yes':
        msg.append('row proven optimal')
    if row['cos'] != r['table_value']:
        msg.append('table value differs from tables/')
    rows = exact.read_spherical(full, d, N)
    if min(len(x.lower().split('e')[0].lstrip('+-').replace('.', '').lstrip('0')) for t in rows for x in t) < 20:
        msg.append('a coordinate has fewer than 20 significant digits')
    s, q, _, _ = exact.spherical_max_cos(rows)
    if not exact.spherical_at_most(s, q, Fraction(Decimal(row['cos'])) - E11):
        msg.append('does not beat the table cosine by 1e-11')
    return msg, exact.spherical_value(s, q)


def check_thomson(r, full, TH):
    msg = []
    N = int(r['cell'])
    if r['file'] != 'thomson/%d.txt' % N:
        msg.append('file name does not match the cell')
    row = TH[N]
    if row['bar'] != r['table_value']:
        msg.append('table value differs from tables/')
    rows = exact.read_spherical(full, 3, N)
    if exact.thomson_norm_defect(rows) > Fraction(1, 10 ** 25):
        msg.append('a stored point is not unit length to 1e-25')
    E = exact.thomson_energy(rows)
    if not Fraction(E) <= Fraction(Decimal(row['bar'])) - E6:
        msg.append('does not beat the minimum over the live tables by 1e-6')
    return msg, E


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
    shelf = tab.split('-', 1)[1]
    hs = shelf in BALL_DIM
    if r['file'] != ('%s/%s-%d.txt' % (tab, shelf, N) if hs else 'packomania-scu/scu%d.txt' % N):
        msg.append('file name does not match the cell')
    radii, bmax = tables(tab, r.get('table_read', ''))
    first, _, data = exact.read_packomania(full, BALL_DIM[shelf] if hs else 3, N, radius_column=not hs)
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


def check_harmonic(r, full, H):
    msg = []
    N, n = map(int, r['cell'].split('-'))
    if r['file'] != 'cohn-harmonic/%d-%d.txt' % (N, n):
        msg.append('file name does not match the cell')
    row = H[(N, n)]
    if N == n + 1 or N == 2 * n:
        msg.append('row is a simplex or cross polytope')
    if row['universal'] != 'no':
        msg.append('row is a universal optimum')
    if row['table_energy'] != r['table_value'] or row['energy_2021'] != r['bound']:
        msg.append('table energy or 2021 energy differs from tables/')
    head, rows = exact.read_harmonic(full, N, n)
    if exact.harmonic_norm_defect(rows) > Fraction(1, 10 ** 20):
        msg.append('a stored vector is not unit length')
    if min(exact.significant_digits(x) or 99 for row_ in rows for x in row_) < 25:
        msg.append('a coordinate has fewer than 25 significant digits')
    d2, s2 = exact.harmonic_d2(rows)
    E = exact.harmonic_energy(d2, s2, n)
    m = max(Decimal('1e-9'), Decimal('1e-12') * E)
    bar = min(Decimal(row['table_energy']), Decimal(row['energy_2021']))
    if not E + m + HSAFE <= bar:
        msg.append('does not beat min(table, 2021) by max(1e-9, 1e-12 E)')
    if not r['floor']:
        msg.append('no polish floor')
    elif not Decimal(r['floor']) >= E + m + HSAFE:
        msg.append('polished posted configuration is not above E + margin')
    hf = head[0].split() if head else []
    if len(hf) < 5 or hf[:3] != ['#', 'cell', '%d-%d' % (N, n)] or hf[3] != 'energy' \
            or abs(Decimal(hf[4]) - E) > Decimal('1e-30'):
        msg.append('header line does not state the cell and its energy')
    return msg, E


_SNAP = {}  # (table, table_read) -> table snapshot, loaded on first use in each process


def table_for(tab, read):
    if (tab, read) not in _SNAP:
        _SNAP[(tab, read)] = {'grassmannian': cohn, 'spherical-codes': spherical_table, 'thomson': thomson_table,
                              'cohn-harmonic': harmonic_table, 'game-of-sloanes': lambda _: sloanes()}[tab](read)
    return _SNAP[(tab, read)]


def tables(tab, read):
    """(radii, suffix maxima) of a Packomania table snapshot."""
    if ('packomania', tab, read) not in _SNAP:
        radii = radius_table('packomania_%s_radius%s.txt' % (tab.split('-', 1)[1], '_' + read if read else ''))
        _SNAP[('packomania', tab, read)] = (radii, suffix_max(radii))
    return _SNAP[('packomania', tab, read)]


def check_row(r):
    """All per-file checks for one cells.csv row; returns the list of failure messages."""
    tab, msg = r['table'], []
    full = os.path.join(FINAL, r['file'])
    if r.get('status') not in STATUSES:
        msg.append('status %r is not one of %s' % (r.get('status'), ', '.join(STATUSES)))
    try:
        with open(full, 'rb') as fh:
            if hashlib.sha256(fh.read()).hexdigest() != r['file_sha256']:
                msg.append('sha256 mismatch')
        read = r.get('table_read', '')
        if tab == 'grassmannian':
            m2, vd = check_grassmannian(r, full, table_for(tab, read))
        elif tab == 'spherical-codes':
            m2, vd = check_spherical(r, full, table_for(tab, read))
        elif tab == 'thomson':
            m2, vd = check_thomson(r, full, table_for(tab, read))
        elif tab == 'game-of-sloanes':
            m2, vd = check_sloanes(r, full, table_for(tab, ''))
        elif tab in PACKOMANIA:
            m2, vd = check_packomania(r, full, tab, tables)
        elif tab == 'cohn-harmonic':
            m2, vd = check_harmonic(r, full, table_for(tab, read))
        else:
            raise ValueError('unknown table %r' % tab)
        msg += m2
        if abs(vd - Decimal(r['our_value'])) > TOL:
            msg.append('recorded value %s, recomputed %s' % (r['our_value'], vd))
    except Exception as e:  # malformed file or table row
        msg.append('error: %r' % (e,))
    return msg


def main():
    with open(os.path.join(FINAL, 'cells.csv')) as fh:
        rows = list(csv.DictReader(fh))
    workers = int(os.environ.get('CHECK_WORKERS') or os.cpu_count() or 1)
    if workers > 1:
        from concurrent.futures import ProcessPoolExecutor
        with ProcessPoolExecutor(workers) as ex:
            results = list(ex.map(check_row, rows, chunksize=8))
    else:
        results = [check_row(r) for r in rows]
    fails, listed, seen, count = [], set(), set(), {}
    for r, m2 in zip(rows, results):
        tab, cell, path = r['table'], r['cell'], r['file']
        msg = []
        if (tab, cell) in seen or path in listed:
            msg.append('duplicate row')
        seen.add((tab, cell))
        listed.add(path)
        msg += m2
        count[tab] = count.get(tab, 0) + 1
        if msg:
            fails.append((tab, cell, msg))
            print('FAIL', tab, cell, '; '.join(msg))
        else:
            print('ok', tab, cell, r['our_value'])
    for sub in FOLDERS:
        if not os.path.isdir(os.path.join(FINAL, sub)):
            if EXPECTED.get(sub):
                fails.append((sub, '', ['folder missing']))
                print('FAIL', sub, 'folder missing')
            continue
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
