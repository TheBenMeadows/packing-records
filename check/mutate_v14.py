"""Mutation check for the v1.4 additions to check_all.py (hsp5, hsp6 and dated Packomania snapshots): each planted
defect must make check_packomania fail, and each genuine row must pass.
usage (from the check/ directory): python3 mutate_v14.py   -> last line PASS or FAIL"""
import csv, os, shutil, sys, tempfile
from decimal import Decimal
sys.path.insert(0, os.getcwd())
import check_all as C

rows = list(csv.DictReader(open('../cells.csv')))
h5 = next(r for r in rows if r['table'] == 'packomania-hsp5')
h6 = next(r for r in rows if r['table'] == 'packomania-hsp6')
old4 = C.radius_table('packomania_hsp4_radius.txt')
# a dated hsp4 row whose table value changed between the original snapshot and its own
h4 = next(r for r in rows if r['table'] == 'packomania-hsp4' and r['table_read'] and old4[int(r['cell'])] != r['table_value'])
tmp = tempfile.mkdtemp()
results = []


def snap(tab, read, change=None):
    radii = C.radius_table('packomania_%s_radius%s.txt' % (tab.split('-', 1)[1], '_' + read if read else ''))
    if change:
        radii = dict(radii); radii.update(change)
    return radii, C.suffix_max(radii)


def tables(change=None):
    return lambda tab, read: snap(tab, read, change)


def edit(src, fn):
    lines = open(src).read().splitlines()
    fn(lines)
    dst = os.path.join(tmp, os.path.basename(src))
    open(dst, 'w').write('\n'.join(lines) + '\n')
    return dst


def move_point(lines):
    k = next(i for i, l in enumerate(lines) if i and l.strip() and not l.startswith('#'))
    f = lines[k].split()
    f[1] = repr(float(f[1]) + 0.05)
    lines[k] = '  '.join(f)


def raise_radius_line(lines):
    lines[0] = str(Decimal(lines[0]) + Decimal('1e-9'))


def run(name, fn):
    try:
        msg, _ = fn()
    except Exception as e:
        msg = ['error %r' % (e,)]
    results.append((name, bool(msg)))
    label = ('clean  ' if not msg else 'FLAGGED ') if name.startswith('control') else ('caught ' if msg else 'MISSED ')
    print(label + name, '|', '; '.join(msg)[:150])


for r, tab in ((h5, 'packomania-hsp5'), (h6, 'packomania-hsp6'), (h4, 'packomania-hsp4')):
    N = int(r['cell']); f = '../' + r['file']; over = str(Decimal(r['our_value']) + Decimal('1e-6'))
    run('control: %s genuine (should NOT be caught)' % tab, lambda: C.check_packomania(r, f, tab, tables()))
    run('%s: table value for N raised above ours' % tab,
        lambda: C.check_packomania(dict(r, table_value=over), f, tab, tables({N: over})))
    bigger = max(n for n in snap(tab, r['table_read'])[0])
    run('%s: a larger N in the table raised above ours' % tab,
        lambda: C.check_packomania(r, f, tab, tables({bigger: over})))
    run('%s: floor raised above ours' % tab, lambda: C.check_packomania(dict(r, floor=over), f, tab, tables()))
    run('%s: one centre moved by 0.05' % tab, lambda: C.check_packomania(r, edit(f, move_point), tab, tables()))
    run('%s: first-line radius raised by 1e-9' % tab, lambda: C.check_packomania(r, edit(f, raise_radius_line), tab, tables()))
run('packomania-hsp4: dated row checked against the original snapshot',
    lambda: C.check_packomania(dict(h4, table_read=''), '../' + h4['file'], 'packomania-hsp4', tables()))
shutil.rmtree(tmp)
controls_ok = all(not c for n, c in results if n.startswith('control'))
mutants_ok = all(c for n, c in results if not n.startswith('control'))
print('PASS' if controls_ok and mutants_ok else 'FAIL')
sys.exit(0 if controls_ok and mutants_ok else 1)
