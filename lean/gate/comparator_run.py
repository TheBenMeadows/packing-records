"""Judge the library against Challenge.lean with `lake comparator`, from a clean clone.

Clones the public repository at PIN, lays lean/ from the attached dataset over it (lean.tar.gz),
installs the pinned toolchain, writes the cell files of the seven sampled cells that Solution.lean
imports, builds Challenge and Solution, and runs:

  1. `lake comparator`             Lean's kernel, every name in comparator.json
  2. `lake comparator --paranoid`  the same plus every external checker shipped with Lean
  3. a planted mutation            one definition in Challenge changed; comparator must reject it

The sandbox is bubblewrap. Where bubblewrap cannot create a namespace (Kaggle containers do not
allow it), the step is repeated with --inadvisably-no-sandbox and the summary records both runs. Everything it reports is in /kaggle/working/out.
"""
import json
import os
import subprocess
import time

PIN = 'beb5b9f'  # resolved to a full sha by the fetch below
CELLS_G = ['3-1-43']
CELLS_P = ['game-of-sloanes:3-24', 'spherical-codes:6-138', 'packomania-hsp4:30',
           'packomania-hsp5:39', 'packomania-hsp6:16', 'packomania-scu:135']
MUTATION = ('Challenge/Cube.lean', 'i ≠ j → d ≤ dist (p i) (p j)', 'i ≠ j → d < dist (p i) (p j)')

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


def setup():
    os.makedirs(OUT, exist_ok=True)
    sh('git clone -q https://github.com/TheBenMeadows/packing-records %s && cd %s && '
       'git checkout -q %s' % (REPO, REPO, PIN))
    sh('du -sh %s; ls %s | head' % (REPO, REPO), check=False)
    tars = [os.path.join(d, f) for d, _, fs in os.walk('/kaggle/input') for f in fs
            if f == 'lean.tar.gz']
    if tars:
        sh('tar -xzf %s -C %s' % (tars[0], REPO))
    else:  # Kaggle unpacked the archive: copy the directory that holds the lakefile over lean/
        src = [d for d, _, fs in os.walk('/kaggle/input') if 'lakefile.toml' in fs][0]
        sh('mkdir -p %s && cp -r %s/. %s/' % (LEAN, src, LEAN))
    sh('ls %s/Challenge.lean %s/Solution.lean %s/comparator.json' % (LEAN, LEAN, LEAN))
    sh('curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o '
       '%s/elan-init.sh && sh %s/elan-init.sh -y --no-modify-path --default-toolchain none '
       '> /dev/null' % (W, W))
    sh('lake exe cache get > %s/cache.log 2>&1; tail -2 %s/cache.log' % (OUT, OUT), cwd=LEAN)
    sh('(apt-get install -y bubblewrap || (apt-get update && apt-get install -y bubblewrap)) '
       '> %s/apt.log 2>&1' % OUT, check=False)


def comparator(tag, flags, cwd=LEAN):
    """Run lake comparator. Where bubblewrap cannot create a namespace (Kaggle containers), run
    again with --inadvisably-no-sandbox: the container is then the only isolation."""
    res = {}
    for extra in ('', ' --inadvisably-no-sandbox'):
        key = '_nosandbox' if extra else ''
        log = '%s/comparator_%s%s.log' % (OUT, tag, key)
        s = time.time()
        r = sh('lake comparator%s%s > %s 2>&1' % (flags, extra, log), check=False, cwd=cwd)
        res['rc' + key] = r.returncode
        res['seconds' + key] = round(time.time() - s)
        res['tail' + key] = out('tail -8 %s' % log)
        print('== comparator %s%s rc=%d\n%s' % (tag, key, r.returncode, res['tail' + key]), flush=True)
        if 'create new namespace' not in open(log).read():
            break
    return res


STEPS = {}


def step(name, cmd, cwd=None):
    """Run one shell step without aborting; record its exit code and the tail of its log."""
    log = '%s/%s.log' % (OUT, name)
    r = sh('(%s) > %s 2>&1' % (cmd, log), check=False, cwd=cwd)
    STEPS[name] = {'rc': r.returncode, 'tail': out('tail -15 %s' % log)}
    print('== %s rc=%d\n%s' % (name, r.returncode, STEPS[name]['tail']), flush=True)
    return r.returncode == 0


def main():
    summary = {'pin': PIN, 'steps': STEPS}
    try:
        run(summary)
    finally:
        summary['wall_seconds'] = round(time.time() - T0)
        json.dump(summary, open(OUT + '/summary.json', 'w'), indent=1)
        print(json.dumps(summary, indent=1), flush=True)
        sh('rm -rf %s %s %s/elan-init.sh' % (REPO, ELAN, W), check=False)


def run(summary):
    setup()
    summary['repo_head'] = out('git rev-parse HEAD', cwd=REPO)
    if not step('lean_version', 'lake env lean --version', cwd=LEAN):
        return
    summary['cpu'] = out("grep -m1 'model name' /proc/cpuinfo | cut -d: -f2") + ' x' + out('nproc')
    summary['bwrap'] = out('command -v bwrap || echo none')
    if not (step('gen_cert', 'python3 -I gen/gen_cert.py %s' % ' '.join(CELLS_G), cwd=LEAN)
            and step('gen_points', 'python3 -I gen/gen_points.py %s' % ' '.join(CELLS_P), cwd=LEAN)):
        return
    if not (step('build_Challenge', 'lake build Challenge', cwd=LEAN)
            and step('build_Solution', 'lake build Solution', cwd=LEAN)):
        return
    step('disk', 'df -h /kaggle/working; du -sh %s/.lake' % LEAN)
    diagnose(summary)
    summary['default'] = comparator('default', '')
    summary['paranoid'] = comparator('paranoid', ' --paranoid')
    path, old, new = MUTATION
    f = os.path.join(LEAN, path)
    text = open(f).read()
    summary['mutation_applied'] = old in text
    open(f, 'w').write(text.replace(old, new, 1))
    try:
        summary['mutation'] = comparator('mutation', '')
    finally:
        open(f, 'w').write(text)


def diagnose(summary):
    """Compare every challenge constant with the library's: one line each from both environments,
    then the pp.all values of those that differ. Output in out/diag_*.txt."""
    body = open(os.path.join(LEAN, 'gate', 'diag', 'CInfo.lean')).read().replace('import Lean\n', '')
    def run_lean(name, head, cmd):
        open(os.path.join(LEAN, name + '.lean'), 'w').write(head + '\n' + body + '\n' + cmd + '\n')
        step(name, 'lake env lean %s.lean > %s/%s.txt 2>&1' % (name, OUT, name), cwd=LEAN)
        return open('%s/%s.txt' % (OUT, name)).read()
    def lines(txt):
        return {l.split('\t')[0]: l for l in txt.splitlines() if '\t' in l}
    c = lines(run_lean('DiagC', 'import Challenge', '#cinfo_mods Challenge'))
    names = sorted(n for n in c if n.split('.')[0] in ('Packing',))
    s = lines(run_lean('DiagS', 'import Solution', '#cinfo_lines ' + ' '.join(names)))
    diff = [n for n in names if c.get(n) != s.get(n)]
    summary['diag_compared'] = len(names)
    summary['diag_differ'] = diff
    if diff:
        run_lean('DiagC2', 'import Challenge', '#cinfo ' + ' '.join(diff[:6]))
        run_lean('DiagS2', 'import Solution', '#cinfo ' + ' '.join(diff[:6]))


main()
