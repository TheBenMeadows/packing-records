"""Clean-clone gate for the Lean certificates of packing-records.

Clones the public repository at a pinned commit, lays the lean/ directory of the
unpushed branch over it (from the private dataset), installs the pinned Lean
toolchain, builds the library, runs the axiom audit, regenerates the certificate
files of this slice and checks them, then derives the per-cell theorems of the
slice. Everything it reports is in /kaggle/working/out.

It runs as a Kaggle script kernel with one dataset attached that holds lean.tar.gz, an archive
of the lean/ directory. SLICE and NSLICES choose a share of the cells (every NSLICES-th cell in
order of cost), ONLY names cells directly, and PAR is the number of Lean processes. The
summaries of the runs are in gate/summaries/.
"""
import csv
import hashlib
import json
import os
import re
import subprocess
import time

SLICE = 0
NSLICES = 5
LIMIT = 0
CHECK_LISTS = False
PIN = 'fc877b65265d665880f9345933d6e0bfa76d700a'
PAR = 4
ONLY = []  # module names such as 'S_25_971': check these cells instead of a slice

W = '/kaggle/working'
REPO = W + '/repo'
LEAN = REPO + '/lean'
OUT = W + '/out'
ELAN = W + '/elan'
ENV = dict(os.environ, ELAN_HOME=ELAN, PATH=ELAN + '/bin:' + os.environ['PATH'])
T0 = time.time()


def sh(cmd, check=True, cwd=None):
    print('+ %s  [t=%.0fs]' % (cmd[:200], time.time() - T0), flush=True)
    return subprocess.run(cmd, shell=True, check=check, cwd=cwd, env=ENV, executable='/bin/bash')


def out(cmd, cwd=None):
    return subprocess.run(cmd, shell=True, check=True, cwd=cwd, env=ENV, executable='/bin/bash',
                          capture_output=True, text=True).stdout.strip()


def tree_sha(root):
    """One sha256 over the relative path and content hash of every file under `root`."""
    h = hashlib.sha256()
    for d, dirs, fs in os.walk(root):
        dirs.sort()
        for f in sorted(fs):
            p = os.path.join(d, f)
            h.update(os.path.relpath(p, root).encode() + b'\0')
            h.update(hashlib.sha256(open(p, 'rb').read()).digest())
    return h.hexdigest()


def setup():
    os.makedirs(OUT, exist_ok=True)
    sh('git init -q %s && cd %s && git remote add origin https://github.com/TheBenMeadows/'
       'packing-records && git fetch -q --depth 1 origin %s && git checkout -q FETCH_HEAD'
       % (REPO, REPO, PIN))
    sh('find /kaggle/input -maxdepth 4 | head -40')
    tars = [os.path.join(d, f) for d, _, fs in os.walk('/kaggle/input') for f in fs
            if f == 'lean.tar.gz']
    if tars:
        sh('tar -xzf %s -C %s' % (tars[0], REPO))
    else:  # Kaggle unpacked the archive: find the directory that holds the lakefile
        src = [d for d, _, fs in os.walk('/kaggle/input') if 'lakefile.toml' in fs][0]
        sh('cp -r %s %s' % (src, LEAN))
    sha = tree_sha(LEAN)
    sh('curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o '
       '%s/elan-init.sh && sh %s/elan-init.sh -y --no-modify-path --default-toolchain none '
       '> /dev/null' % (W, W))
    sh('lake exe cache get > %s/cache.log 2>&1; tail -2 %s/cache.log' % (OUT, OUT), cwd=LEAN)
    return sha


def units():
    u = []
    for r in csv.DictReader(open(LEAN + '/cells_manifest.tsv'), delimiter='\t'):
        m, n, N = int(r['m']), int(r['n']), int(r['N'])
        u.append((N * N * n * n * m, 'g', '%d_%d_%d' % (m, n, N), r['cell']))
    for r in csv.DictReader(open(LEAN + '/points_manifest.tsv'), delimiter='\t'):
        u.append((int(r['cost']), 'p', r['module'], '%s:%s' % (r['table'], r['cell'])))
    u.sort()
    if LIMIT:
        u = u[:LIMIT]
    if ONLY:
        return [x for x in u if x[2] in ONLY]
    return u[SLICE::NSLICES]


def generate(mine):
    g = [x[3] for x in mine if x[1] == 'g']
    p = [x[3] for x in mine if x[1] == 'p']
    for script, args in (('gen_cert.py', g), ('gen_links.py', g), ('gen_points.py', p)):
        if args:
            open(W + '/args.txt', 'w').write('\n'.join(args) + '\n')
            sh('xargs python3 -I gen/%s < %s/args.txt' % (script, W), cwd=LEAN)


def check_cells(mine):
    jobs = []
    for _, kind, name, _ in mine:
        jobs.append('C_%s L_%s' % (name, name) if kind == 'g' else name)
    open(W + '/jobs.txt', 'w').write('\n'.join(jobs) + '\n')
    driver = r'''
cd %(lean)s
export LP=$(lake env printenv LEAN_PATH)
export LEANBIN=$(lake env which lean)
export OLE=.lake/build/lib/lean/Packing/Cert/Cells
mkdir -p $OLE %(out)s/logs
one() {
  for name in "$@"; do
    s=$(date +%%s%%N)
    LEAN_PATH=$LP $LEANBIN -o $OLE/$name.olean Packing/Cert/Cells/$name.lean > %(out)s/logs/$name.log 2>&1
    rc=$?
    ms=$(( ($(date +%%s%%N) - s) / 1000000 ))
    if [ $rc -eq 0 ] && [ ! -s %(out)s/logs/$name.log ]; then st=ok; rm -f %(out)s/logs/$name.log; else st=FAIL; fi
    printf '%%s\t%%s\t%%s\t%%s\n' "$name" "$st" "$rc" "$ms" >> %(out)s/results.tsv
    [ $st = ok ] || return 0
  done
}
export -f one
xargs -P %(par)d -L 1 bash -c 'one "$@"' _ < %(w)s/jobs.txt
''' % dict(lean=LEAN, out=OUT, par=PAR, w=W)
    open(W + '/driver.sh', 'w').write(driver)
    sh('bash %s/driver.sh' % W)


MODULE_OF = [(r'ok_sph_(\w+)', 'S_'), (r'ok_gos_(\w+)', 'G_'), (r'ok_hsp4_(\w+)', 'H4_'),
             (r'ok_hsp5_(\w+)', 'H5_'), (r'ok_hsp6_(\w+)', 'H6_'), (r'ok_scu_(\w+)', 'U_'),
             (r'link_(\w+)', 'L_'), (r'ok_(\d+_\d+_\d+)', 'C_')]


def modules_of(block):
    found = set()
    for ident in re.findall(r'Cells\.(\w+)', block):
        for pat, prefix in MODULE_OF:
            mt = re.fullmatch(pat, ident)
            if mt:
                found.add(prefix + mt.group(1))
                break
    return found


def slice_list(src, dst, have):
    """Keep the imports and theorems of `src` whose cell modules are all in `have`."""
    text = open(os.path.join(LEAN, 'Packing', 'Cert', src)).read()
    head, body = text.split('namespace Packing.Cert', 1)
    lines = [l for l in head.split('\n')
             if not l.startswith('import Packing.Cert.Cells.') or l.rsplit('.', 1)[1] in have]
    blocks = [b for b in body.split('\n\n') if b.strip()]
    kept = [b for b in blocks if not modules_of(b) or modules_of(b) <= have]
    kept = [b for b in kept if 'theorem' in b or 'end Packing.Cert' in b]
    n = sum(b.count('theorem ') for b in kept)
    open(os.path.join(LEAN, 'Packing', 'Cert', dst), 'w').write(
        '\n'.join(lines) + 'namespace Packing.Cert\n\n' + '\n\n'.join(kept) + '\n')
    return n


def derive(ok):
    res = {}
    for src in ('All.lean', 'AllLinks.lean', 'AllPoints.lean'):
        dst = 'Slice' + src
        n = slice_list(src, dst, ok)
        if n == 0:
            res[src] = {'theorems': 0, 'rc': None}
            continue
        r = sh('LEAN_PATH=$(lake env printenv LEAN_PATH) $(lake env which lean) Packing/Cert/%s '
               '> %s/%s.log 2>&1' % (dst, OUT, dst), check=False, cwd=LEAN)
        res[src] = {'theorems': n, 'rc': r.returncode,
                    'log_bytes': os.path.getsize('%s/%s.log' % (OUT, dst))}
    return res


def check_lists():
    keep = ['Packing/Cert/All.lean', 'Packing/Cert/AllLinks.lean', 'Packing/Cert/AllPoints.lean',
            'cells_manifest.tsv', 'links_manifest.tsv', 'points_manifest.tsv']
    before = {f: hashlib.sha256(open(os.path.join(LEAN, f), 'rb').read()).hexdigest() for f in keep}
    for script in ('gen_cert.py', 'gen_links.py', 'gen_points.py'):
        sh('python3 -I gen/%s' % script, cwd=LEAN)
    after = {f: hashlib.sha256(open(os.path.join(LEAN, f), 'rb').read()).hexdigest() for f in keep}
    return {f: before[f] == after[f] for f in keep}


def main():
    summary = {'slice': SLICE, 'nslices': NSLICES, 'limit': LIMIT, 'pin': PIN,
               'only': len(ONLY), 'par': PAR}
    summary['lean_tree_sha256'] = setup()
    summary['repo_head'] = out('git rev-parse HEAD', cwd=REPO)
    summary['lean_version'] = out('lake env lean --version', cwd=LEAN)
    summary['cpu'] = out("grep -m1 'model name' /proc/cpuinfo | cut -d: -f2") + ' x' + out('nproc')
    b = sh('lake build Packing > %s/build.log 2>&1' % OUT, check=False, cwd=LEAN)
    summary['build_rc'] = b.returncode
    sh('lake env lean Audit.lean > %s/audit.txt 2>&1' % OUT, check=False, cwd=LEAN)
    audit = open(OUT + '/audit.txt').read().strip().split('\n')
    summary['audit_lines'] = len(audit)
    summary['audit_bad'] = [l for l in audit
                            if not l.endswith('[propext, Classical.choice, Quot.sound]')]
    if CHECK_LISTS:
        summary['lists_identical'] = check_lists()
    mine = units()
    summary['units'] = len(mine)
    if not CHECK_LISTS:
        generate(mine)
    check_cells(mine)
    rows = [l.split('\t') for l in open(OUT + '/results.tsv').read().strip().split('\n')]
    ok = {r[0] for r in rows if r[1] == 'ok'}
    summary['modules_checked'] = len(rows)
    summary['modules_ok'] = len(ok)
    summary['failures'] = [r[0] for r in rows if r[1] != 'ok']
    summary['check_seconds'] = round(sum(int(r[3]) for r in rows) / 1000)
    summary['derived'] = derive(ok)
    summary['wall_seconds'] = round(time.time() - T0)
    json.dump(summary, open(OUT + '/summary.json', 'w'), indent=1)
    print(json.dumps(summary, indent=1), flush=True)
    sh('rm -rf %s %s %s/elan-init.sh' % (REPO, ELAN, W))


main()
