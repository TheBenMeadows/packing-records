"""Mutation check for the v1.5 additions to check_all.py (status column, dated harmonic snapshots, spherical rows
checked against the 2026-11-11/12/13 snapshots, Grassmannian rows checked against the 2026-11-13 snapshot, padded
spherical coordinates): each planted defect must make the relevant check fail, and each genuine row must pass.
usage (from the check/ directory): python3 mutate_v15.py   -> last line PASS or FAIL"""
import csv, hashlib, os, shutil, sys, tempfile
from decimal import Decimal
sys.path.insert(0, os.getcwd())
import check_all as C

rows = list(csv.DictReader(open('../cells.csv')))
h_old = next(r for r in rows if r['table'] == 'cohn-harmonic' and r['table_read'] and r['notes'].find('replaces') >= 0)
sph = {d: next(r for r in rows if r['table'] == 'spherical-codes' and r['table_read'] == d)
       for d in ('2026-11-11', '2026-11-12', '2026-11-13')}
S07 = C.spherical_table('2026-11-07')
# a 2026-11-12 row whose table cosine changed after 2026-11-07
moved = next(r for r in rows if r['table'] == 'spherical-codes' and r['table_read'] == '2026-11-12'
             and tuple(map(int, r['cell'].split('-'))) in S07 and S07[tuple(map(int, r['cell'].split('-')))]['cos'] != r['table_value'])
pad = next(r for r in rows if r['table'] == 'spherical-codes' and 'padded' in r['notes'])
gr = next(r for r in rows if r['table'] == 'grassmannian' and r['table_read'] == '2026-11-13')
tmp = tempfile.mkdtemp()
results = []


def run(name, fn):
    try:
        out = fn()
        msg = out[0] if isinstance(out, tuple) else out
    except Exception as e:
        msg = ['error %r' % (e,)]
    results.append((name, bool(msg)))
    label = ('clean   ' if not msg else 'FLAGGED ') if name.startswith('control') else ('caught  ' if msg else 'MISSED  ')
    print(label + name, '|', '; '.join(msg)[:150])


def copy_edit(src, fn):
    lines = open(src).read().splitlines()
    fn(lines)
    dst = os.path.join(tmp, os.path.basename(src))
    open(dst, 'w').write('\n'.join(lines) + '\n')
    return dst


def sig(x):
    return len(x.lower().split('e')[0].lstrip('+-').replace('.', '').lstrip('0'))


def unpad(lines):
    """Strip the trailing zeros of the coordinate that has the fewest significant digits once they are stripped."""
    best = None
    for k, l in enumerate(lines):
        if l.startswith('#'):
            continue
        for c, x in enumerate(l.split(',')):
            if 'e' not in x.lower() and x.endswith('0'):
                n = sig(x.rstrip('0'))
                if best is None or n < best[0]:
                    best = (n, k, c)
    assert best and best[0] < 20, 'no padded coordinate found'
    n, k, c = best
    f = lines[k].split(',')
    f[c] = f[c].rstrip('0')
    lines[k] = ','.join(f)


def bump_pair(lines):
    """Change the last digit of the first coordinate of the first vector of the attaining pair named in the header."""
    i = int(lines[0].split('(pair ')[1].split(',')[0])
    data = [k for k, l in enumerate(lines) if l and not l.startswith('#')]
    k = data[i - 1]
    f = lines[k].split(',')
    mant, e, ex = f[0].lower().partition('e')
    mant = mant[:-1] + ('1' if mant[-1] != '1' else '2')
    f[0] = mant + (e + ex if e else '')
    lines[k] = ','.join(f)


# status column
for r in (h_old, sph['2026-11-12'], gr):
    run('control: status %s %s genuine (should NOT be caught)' % (r['table'], r['cell']),
        lambda r=r: [m for m in C.check_row(r)])
run('status: unknown value', lambda: C.check_row(dict(gr, status='listed')))
run('status: blank', lambda: C.check_row(dict(gr, status='')))

# dated harmonic snapshot
H = C.harmonic_table(h_old['table_read'])
hk = tuple(map(int, h_old['cell'].split('-')))
run('control: harmonic dated row genuine (should NOT be caught)', lambda: C.check_harmonic(h_old, '../' + h_old['file'], H))
run('harmonic: dated row checked against the 2026-11-03 snapshot',
    lambda: C.check_row(dict(h_old, table_read='')))
H2 = {k: dict(v) for k, v in H.items()}
low = str(Decimal(h_old['our_value']) - Decimal('1e-6'))
H2[hk]['table_energy'] = low
run('harmonic: dated snapshot energy below ours', lambda: C.check_harmonic(dict(h_old, table_value=low), '../' + h_old['file'], H2))
run('harmonic: dated snapshot file missing', lambda: C.check_row(dict(h_old, table_read='2026-01-01')))

# spherical rows on the new snapshots
for d, r in sph.items():
    S = C.spherical_table(d)
    k = tuple(map(int, r['cell'].split('-')))
    run('control: spherical %s genuine (should NOT be caught)' % d, lambda r=r, S=S: C.check_spherical(r, '../' + r['file'], S))
    S2 = {kk: dict(v) for kk, v in S.items()}
    below = '%.12f' % (float(r['our_value']) - 5e-12)
    S2[k]['cos'] = below
    run('spherical %s: snapshot cosine within 1e-11 of ours' % d,
        lambda r=r, S2=S2, below=below: C.check_spherical(dict(r, table_value=below), '../' + r['file'], S2))
run('spherical: 2026-11-12 row checked against the 2026-11-07 snapshot',
    lambda: C.check_row(dict(moved, table_read='2026-11-07')))
S = C.spherical_table(pad['table_read'])
run('control: padded spherical file genuine (should NOT be caught)', lambda: C.check_spherical(pad, '../' + pad['file'], S))
run('spherical: padding removed from one coordinate', lambda: C.check_spherical(pad, copy_edit('../' + pad['file'], unpad), S))


def bumped():
    """check_row on a copy of the padded file with one digit of an attaining vector changed and its sha256 updated, placed under a
    temporary root at the same relative path, so that only the recomputed value can differ from cells.csv."""
    p = copy_edit('../' + pad['file'], bump_pair)
    os.makedirs(os.path.join(tmp, 'spherical-codes'), exist_ok=True)
    q = os.path.join(tmp, pad['file'])
    os.replace(p, q)
    final = C.FINAL
    C.FINAL = tmp
    try:
        return C.check_row(dict(pad, file_sha256=hashlib.sha256(open(q, 'rb').read()).hexdigest()))
    finally:
        C.FINAL = final


run('spherical: one digit of an attaining vector changed, sha256 updated', bumped)

# Grassmannian on the 2026-11-13 snapshot
G = C.cohn(gr['table_read'])
gk = tuple(map(int, gr['cell'].split('-')))
run('control: grassmannian 2026-11-13 genuine (should NOT be caught)', lambda: C.check_grassmannian(gr, '../' + gr['file'], G))
G2 = {kk: dict(v) for kk, v in G.items()}
G2[gk]['value'] = '%.10f' % (float(gr['our_value']) + 1e-6)
run('grassmannian: 2026-11-13 snapshot value above ours',
    lambda: C.check_grassmannian(dict(gr, table_value=G2[gk]['value']), '../' + gr['file'], G2))

shutil.rmtree(tmp)
controls_ok = all(not c for n, c in results if n.startswith('control'))
mutants_ok = all(c for n, c in results if not n.startswith('control'))
print('PASS' if controls_ok and mutants_ok else 'FAIL')
sys.exit(0 if controls_ok and mutants_ok else 1)
