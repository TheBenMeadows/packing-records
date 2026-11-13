"""Plant defects in a copy of the record set and confirm that check_all.py fails on each.

usage: python3 mutate.py ROOT

ROOT is a full record-set tree (cells.csv, tables/, check/, and the five data
folders), for example packing-records with this patch set applied. ROOT itself
is never modified: each mutation works on its own temporary copy. For every
mutation the script runs check/check_all.py in the copy and requires that the
last line is FAIL and that a FAIL line names the planted defect. It prints one
line per mutation and, last, PASS if every defect was caught, else FAIL.

Mutations (all on the first cohn-harmonic row of cells.csv):
  bad_energy        recorded our_value raised by 1e-20
  energy_above_bar  2021 energy (tables/ and the bound column) set to E + 1e-10,
                    so E no longer beats min(table, 2021) by the margin
  non_unit_vector   first coordinate row scaled by (1 + 1e-15); sha256 updated
  universal_row     the row marked universal = yes in its harmonic snapshot
                    (tables/cohn_harmonic.tsv, or the one dated by table_read)
  duplicate_cell    the cells.csv row appended a second time
  floor_too_low     recorded floor set to the recorded energy
"""
import csv, hashlib, io, os, shutil, subprocess, sys, tempfile
from decimal import Decimal, getcontext

getcontext().prec = 80


def read_csv(root):
    with open(os.path.join(root, 'cells.csv'), newline='') as fh:
        r = csv.DictReader(fh)
        return r.fieldnames, list(r)


def write_csv(root, cols, rows):
    with open(os.path.join(root, 'cells.csv'), 'w', newline='') as fh:
        w = csv.DictWriter(fh, cols, lineterminator='\n')
        w.writeheader()
        for r in rows:
            w.writerow(r)


def target(rows):
    for i, r in enumerate(rows):
        if r['table'] == 'cohn-harmonic':
            return i
    raise SystemExit('no cohn-harmonic row in cells.csv')


def edit_tsv(root, N, n, col, value, read=''):
    """Set one column of row (N, n) in the harmonic snapshot dated `read` (blank = tables/cohn_harmonic.tsv)."""
    p = os.path.join(root, 'tables', 'cohn_harmonic_%s.tsv' % read if read else 'cohn_harmonic.tsv')
    lines = open(p).read().split('\n')
    head = None
    for k, l in enumerate(lines):
        if l.startswith('#') or not l:
            continue
        f = l.split('\t')
        if head is None:
            head = f
            continue
        if f[0] == str(N) and f[1] == str(n):
            f[head.index(col)] = value
            lines[k] = '\t'.join(f)
    open(p, 'w').write('\n'.join(lines))


def m_bad_energy(root):
    cols, rows = read_csv(root)
    i = target(rows)
    rows[i]['our_value'] = str(Decimal(rows[i]['our_value']) + Decimal('1e-20'))
    write_csv(root, cols, rows)
    return rows[i]['cell'], 'recorded value'


def m_energy_above_bar(root):
    cols, rows = read_csv(root)
    i = target(rows)
    N, n = rows[i]['cell'].split('-')
    v = str(Decimal(rows[i]['our_value']) + Decimal('1e-10'))
    rows[i]['bound'] = v
    edit_tsv(root, N, n, 'energy_2021', v, rows[i].get('table_read', ''))
    write_csv(root, cols, rows)
    return rows[i]['cell'], 'does not beat min(table, 2021)'


def m_non_unit(root):
    cols, rows = read_csv(root)
    i = target(rows)
    p = os.path.join(root, rows[i]['file'])
    lines = open(p).read().split('\n')
    k = next(j for j, l in enumerate(lines) if l and not l.startswith('#'))
    lines[k] = ','.join(str(Decimal(x) * (1 + Decimal('1e-15'))) for x in lines[k].split(','))
    open(p, 'w').write('\n'.join(lines))
    rows[i]['file_sha256'] = hashlib.sha256(open(p, 'rb').read()).hexdigest()
    write_csv(root, cols, rows)
    return rows[i]['cell'], 'not unit length'


def m_universal(root):
    cols, rows = read_csv(root)
    i = target(rows)
    N, n = rows[i]['cell'].split('-')
    edit_tsv(root, N, n, 'universal', 'yes', rows[i].get('table_read', ''))
    return rows[i]['cell'], 'universal optimum'


def m_duplicate(root):
    cols, rows = read_csv(root)
    i = target(rows)
    rows.append(dict(rows[i]))
    write_csv(root, cols, rows)
    return rows[i]['cell'], 'duplicate row'


def m_floor(root):
    cols, rows = read_csv(root)
    i = target(rows)
    rows[i]['floor'] = rows[i]['our_value']
    write_csv(root, cols, rows)
    return rows[i]['cell'], 'polished posted configuration is not above'


MUTATIONS = [('bad_energy', m_bad_energy), ('energy_above_bar', m_energy_above_bar),
             ('non_unit_vector', m_non_unit), ('universal_row', m_universal),
             ('duplicate_cell', m_duplicate), ('floor_too_low', m_floor)]


def main():
    root = os.path.abspath(sys.argv[1])
    tmp = tempfile.mkdtemp(prefix='mutate-')
    procs = []
    try:
        for name, fn in MUTATIONS:
            d = os.path.join(tmp, name)
            shutil.copytree(root, d, ignore=shutil.ignore_patterns('__pycache__', '.git'))
            cell, want = fn(d)
            p = subprocess.Popen([sys.executable, os.path.join(d, 'check', 'check_all.py')],
                                 stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            procs.append((name, cell, want, p))
        ok = True
        for name, cell, want, p in procs:
            out = p.communicate()[0].strip().split('\n')
            hit = [l for l in out if l.startswith('FAIL') and want in l and (cell in l or name == 'duplicate_cell')]
            caught = out[-1] == 'FAIL' and bool(hit)
            ok &= caught
            print('%-17s cell %-7s last line %s; %s' % (name, cell, out[-1],
                  ('caught: ' + hit[0][:150]) if caught else 'NOT CAUGHT'))
        print('PASS' if ok else 'FAIL')
        return 0 if ok else 1
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


if __name__ == '__main__':
    sys.exit(main())
