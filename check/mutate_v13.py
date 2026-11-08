"""Mutation check for the v1.3 additions to check_all.py: each planted defect must make the relevant check fail.
usage (from a v1.3 checkout's check/ dir): python3 mutate_v13.py"""
import csv, os, shutil, sys, tempfile
sys.path.insert(0, os.getcwd())
import check_all as C
import exact

rows = list(csv.DictReader(open('../cells.csv')))
sp = next(r for r in rows if r['table'] == 'spherical-codes')
th = next(r for r in rows if r['table'] == 'thomson')
gr = next(r for r in rows if r['table'] == 'grassmannian' and r['table_read'])
tmp = tempfile.mkdtemp()
results = []


def bump_first_coord(src, sep, delta):
    lines = open(src).read().splitlines()
    for k, l in enumerate(lines):
        if l and not l.startswith('#'):
            f = l.split(sep)
            f[0] = repr(float(f[0]) + delta)
            lines[k] = sep.join(f)
            break
    dst = os.path.join(tmp, os.path.basename(src))
    open(dst, 'w').write('\n'.join(lines) + '\n')
    return dst


def run(name, fn):
    try:
        msg, _ = fn()
    except Exception as e:
        msg = ['error %r' % (e,)]
    results.append((name, bool(msg)))
    print(('caught ' if msg else 'MISSED ') + name, '|', '; '.join(msg)[:150])


S = C.spherical_table(sp['table_read']); T = C.thomson_table(th['table_read']); G = C.cohn(gr['table_read'])
# 1. spherical: the genuine file passes
run('control: spherical genuine (should NOT be caught)', lambda: C.check_spherical(sp, '../' + sp['file'], S))
# 2. spherical: table cosine lowered below our value
S2 = {k: dict(v) for k, v in S.items()}; key = tuple(map(int, sp['cell'].split('-')))
S2[key]['cos'] = str(float(sp['our_value']) - 1e-6); sp2 = dict(sp, table_value=S2[key]['cos'])
run('spherical: table cosine below ours', lambda: C.check_spherical(sp2, '../' + sp['file'], S2))
# 3. spherical: a coordinate moved (raises some cosine)
run('spherical: coordinate moved by 0.05', lambda: C.check_spherical(sp, bump_first_coord('../' + sp['file'], ',', 0.05), S))
# 4. spherical: row marked proven optimal
S3 = {k: dict(v) for k, v in S.items()}; S3[key]['proven_optimal'] = 'yes'
run('spherical: proven-optimal row', lambda: C.check_spherical(sp, '../' + sp['file'], S3))
# 5. thomson: genuine passes
run('control: thomson genuine (should NOT be caught)', lambda: C.check_thomson(th, '../' + th['file'], T))
# 6. thomson: bar lowered below ours
T2 = {k: dict(v) for k, v in T.items()}; T2[436]['bar'] = str(float(th['our_value']) - 1e-3); th2 = dict(th, table_value=T2[436]['bar'])
run('thomson: bar below ours', lambda: C.check_thomson(th2, '../' + th['file'], T2))
# 7. thomson: a point moved off the sphere
run('thomson: point not unit length', lambda: C.check_thomson(th, bump_first_coord('../' + th['file'], ',', 1e-6), T))
# 8. grassmannian with table_read: today's snapshot row raised above ours
G2 = {k: dict(v) for k, v in G.items()}; gk = tuple(map(int, gr['cell'].split('-')))
G2[gk]['value'] = str(float(gr['our_value']) + 1e-6); gr2 = dict(gr, table_value=G2[gk]['value'])
run('grassmannian: dated snapshot value above ours', lambda: C.check_grassmannian(gr2, '../' + gr['file'], G2))
shutil.rmtree(tmp)
controls_ok = not results[0][1] and not results[4][1]
mutants_ok = all(c for n, c in results if not n.startswith('control'))
print('PASS' if controls_ok and mutants_ok else 'FAIL')
