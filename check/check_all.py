"""Re-check every file listed in ../cells.csv (Python standard library only).

For each row: the file exists, its sha256 matches, it parses in its table's own
layout, its value recomputed exactly (exact.py) equals the recorded value, and
the keep rules hold on exact rationals:
  grassmannian     row unstarred and not noted optimal; value >= table + 1e-7;
                   value <= bound - 1e-8 when a bound is listed
  game-of-sloanes  row not provably optimal; mu <= table - 1e-7; mu >= lower bound
  packomania-hsp4  r* >= table + 1e-7 and r* >= floor + 1e-7
  packomania-scu   r* >= max(table, B(N)) + 1e-7 and r* >= floor + 1e-7,
                   B(N) = max over listed N' >= N of r(N')
Table values are re-read from the dated snapshots in tables/ and must
equal the cells.csv column. Every file under the four output folders must be
listed. The last line printed is PASS or FAIL.
"""
import csv, hashlib, os, re, sys
from decimal import Decimal
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
FINAL = os.path.dirname(HERE)
DATA = os.path.join(FINAL, 'tables')
sys.path.insert(0, HERE)
import exact  # noqa: E402

E7, E8 = Fraction(1, 10 ** 7), Fraction(1, 10 ** 8)
TOL = Decimal('1e-35')


def cohn():
    rows = {}
    for line in open(os.path.join(DATA, 'cohn_grassmannian.md'), encoding='utf-8'):
        f = line.rstrip('\n').split('\t')
        if len(f) != 6 or f[0].strip() == 'm':
            continue
        star = f[0].startswith('∗')
        m = int(f[0].replace('∗', '').strip())
        rows[(m, int(f[1]), int(f[2]))] = (f[3], f[4].strip(), star,
                                           'optimal packing' in f[5] or 'proof of optimality' in f[5])
    return rows


def sloanes():
    rows = {}
    pat = re.compile(r'<tr><td>(\d+)</td><td>(\d+)</td><td>([0-9.]+)</td><td>([0-9.]+)</td><td>[^<]*</td>'
                     r'<td><a href="[^"]*">File</a></td><td>([^<]*)</td></tr>')
    for line in open(os.path.join(DATA, 'gameofsloanes_README.md'), encoding='utf-8'):
        for mt in pat.finditer(line):
            rows[(int(mt.group(1)), int(mt.group(2)))] = (mt.group(3), mt.group(4), '&#9675;' in mt.group(5))
    return rows


def radius_table(fn):
    t = {}
    for line in open(os.path.join(DATA, fn)):
        f = line.split()
        if len(f) >= 2 and f[0].isdigit():
            t[int(f[0])] = f[1]
    return t


def main():
    C, T = cohn(), sloanes()
    H = radius_table('live_hsp4.txt')
    S = radius_table('packomania.com_scu_txt_radius.txt')
    Bn, best = {}, Fraction(0)
    for N in sorted(S, reverse=True):
        best = max(best, Fraction(Decimal(S[N])))
        Bn[N] = best
    rows = list(csv.DictReader(open(os.path.join(FINAL, 'cells.csv'))))
    fails, listed = [], set()
    count = {}
    for r in rows:
        tab, cell, path = r['table'], r['cell'], r['file']
        listed.add(path)
        full = os.path.join(FINAL, path)
        msg = []
        try:
            if hashlib.sha256(open(full, 'rb').read()).hexdigest() != r['file_sha256']:
                msg.append('sha256 mismatch')
            ours = Decimal(r['our_value'])
            if tab == 'grassmannian':
                m, n, N = map(int, cell.split('-'))
                assert path == 'grassmannian/%d-%d-%d.txt' % (m, n, N)
                tv, bd, star, opt = C[(m, n, N)]
                if star or opt:
                    msg.append('row starred or noted optimal')
                if tv != r['table_value']:
                    msg.append('table value differs from staged table')
                head, data = exact.read_grassmannian(full, m, n, N)
                if len(head) != 1:
                    msg.append('expected exactly one header line')
                val, arg = exact.grassmannian(data, m, n, N)
                vd = exact.dec(val)
                hv = Decimal(re.search(r' value (\S+)', head[0]).group(1))
                if not (hv <= vd and vd - hv < Decimal('1e-29')):
                    msg.append('header value inconsistent')
                if not val >= Fraction(Decimal(tv)) + E7:
                    msg.append('does not beat table by 1e-7')
                if bd and not val <= Fraction(Decimal(bd)) - E8:
                    msg.append('within 1e-8 of bound (or above it)')
            elif tab == 'game-of-sloanes':
                d, n = map(int, cell.split('-'))
                assert path == 'game-of-sloanes/%dx%d.txt' % (d, n)
                tv, lb, prov = T[(d, n)]
                if prov:
                    msg.append('row provably optimal')
                if tv != r['table_value'] or lb != r['bound']:
                    msg.append('table value or lower bound differs from staged table')
                vals = exact.read_sloanes(full, d, n)
                mu2, arg = exact.sloanes_mu2(vals, d, n)
                vd = exact.dec(mu2).sqrt()
                t = Fraction(Decimal(tv))
                if not mu2 <= (t - E7) ** 2:
                    msg.append('does not beat table by 1e-7')
                if not mu2 >= Fraction(Decimal(lb)) ** 2:
                    msg.append('below the listed lower bound')
            else:
                N = int(cell)
                hs = tab == 'packomania-hsp4'
                assert path == ('packomania-hsp4/hsp4-%d.txt' % N if hs else 'packomania-scu/scu%d.txt' % N)
                first, comments, data = exact.read_packomania(full, 4 if hs else 3, N, radius_column=not hs)
                tv = H[N] if hs else S[N]
                if tv != r['table_value']:
                    msg.append('table value differs from staged table')
                if hs:
                    D, M, arg = exact.hsp4(data)
                    vd = exact.hsp4_value(D, M)
                    ge = lambda x: exact.hsp4_at_least(D, M, x)
                    bar = Fraction(Decimal(tv))
                else:
                    D, A, arg = exact.scu(data)
                    vd = exact.scu_value(D, A)
                    ge = lambda x: exact.scu_at_least(D, A, x)
                    bar = max(Fraction(Decimal(tv)), Bn[N])
                    if Decimal(r['bound']) != Decimal(Bn[N].numerator) / Bn[N].denominator:
                        msg.append('B(N) column differs')
                hv = Decimal(first)
                if not (hv <= vd and vd - hv < Decimal('1e-29')):
                    msg.append('header radius inconsistent')
                if not ge(bar + E7):
                    msg.append('does not beat table%s by 1e-7' % ('' if hs else '/B(N)'))
                if not r['floor']:
                    msg.append('no polish floor')
                elif not ge(Fraction(Decimal(r['floor'])) + E7):
                    msg.append('does not beat polish floor by 1e-7')
            if abs(vd - ours) > TOL:
                msg.append('recorded value %s, recomputed %s' % (ours, vd))
        except Exception as e:  # malformed file
            msg.append('error: %r' % (e,))
        count[tab] = count.get(tab, 0) + 1
        if msg:
            fails.append((tab, cell, msg))
            print('FAIL', tab, cell, '; '.join(msg))
        else:
            print('ok', tab, cell, r['our_value'])
    for sub in ('grassmannian', 'game-of-sloanes', 'packomania-hsp4', 'packomania-scu'):
        for fn in sorted(os.listdir(os.path.join(FINAL, sub))):
            if '%s/%s' % (sub, fn) not in listed:
                fails.append((sub, fn, ['file not listed in cells.csv']))
                print('FAIL', sub, fn, 'not listed in cells.csv')
    print('rows', len(rows), ' '.join('%s=%d' % kv for kv in sorted(count.items())), 'failures', len(fails))
    print('PASS' if not fails else 'FAIL')
    return 0 if not fails else 1


if __name__ == '__main__':
    sys.exit(main())
