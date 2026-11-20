"""Judge the ten-point theorem against ChallengeCube10.lean with `lake comparator`, from a clean clone.

Runs as a Kaggle script kernel with one dataset attached that holds the lean/ directory.

Clones the public repository at a pinned commit, lays the lean/ directory of the working tree over
it (from the private dataset), installs the pinned toolchain, builds PackingCube10 with
gate/build_cube10.sh and ChallengeCube10, and runs `lake comparator --config comparator_cube10.json`
with Lean's kernel only, timed, and then once more with the value in the challenge changed (the
comparator must reject that). Where bubblewrap cannot create a namespace (Kaggle containers), a
step is repeated with --inadvisably-no-sandbox. Everything it reports is in /kaggle/working/out.
"""
import json, os, subprocess, time

PIN = '10bb9a04563a7818852710dfb24cda45631d3470'
W = '/kaggle/working'
REPO = W + '/repo'
LEAN = REPO + '/lean'
OUT = W + '/out'
ELAN = W + '/elan'
ENV = dict(os.environ, ELAN_HOME=ELAN, PATH=ELAN + '/bin:' + os.environ['PATH'])
T0 = time.time()
S = {'pin': PIN}


def sh(cmd, check=True, cwd=None):
    print('+ %s  [t=%.0fs]' % (cmd[:200], time.time() - T0), flush=True)
    return subprocess.run(cmd, shell=True, check=check, cwd=cwd, env=ENV, executable='/bin/bash')


def save():
    S['wall_seconds'] = round(time.time() - T0)
    json.dump(S, open(OUT + '/summary.json', 'w'), indent=1)
    print(json.dumps(S, indent=1), flush=True)


def setup():
    os.makedirs(OUT, exist_ok=True)
    sh('git init -q %s && cd %s && git remote add origin https://github.com/TheBenMeadows/'
       'packing-records && git fetch -q --depth 1 origin %s && git checkout -q FETCH_HEAD'
       % (REPO, REPO, PIN))
    # The pinned commit may hold generated Cube10 files that the tree no longer has.
    sh('rm -f %s/Packing/Cube10*.lean' % LEAN)
    tars = [os.path.join(d, f) for d, _, fs in os.walk('/kaggle/input') for f in fs
            if f == 'lean.tar.gz']
    if tars:
        sh('tar -xzf %s -C %s' % (tars[0], REPO))
    else:
        src = [d for d, _, fs in os.walk('/kaggle/input') if 'lakefile.toml' in fs][0]
        sh('mkdir -p %s && cp -r %s/. %s/' % (LEAN, src, LEAN))
    sh('ls %s/ChallengeCube10.lean %s/comparator_cube10.json' % (LEAN, LEAN))
    sh('curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o '
       '%s/elan-init.sh && sh %s/elan-init.sh -y --no-modify-path --default-toolchain none '
       '> /dev/null' % (W, W))
    sh('lake exe cache get > %s/cache.log 2>&1; tail -2 %s/cache.log' % (OUT, OUT), cwd=LEAN)
    sh('(apt-get install -y bubblewrap || (apt-get update && apt-get install -y bubblewrap)) '
       '> %s/apt.log 2>&1' % OUT, check=False)


def step(name, cmd):
    t = time.time()
    r = sh('(%s) > %s/%s.log 2>&1' % (cmd, OUT, name), check=False, cwd=LEAN)
    S[name] = {'rc': r.returncode, 'seconds': round(time.time() - t)}
    sh('tail -8 %s/%s.log' % (OUT, name), check=False)
    save()
    return r.returncode == 0


def comparator(tag):
    res = {}
    for extra in ('', ' --inadvisably-no-sandbox'):
        key = 'nosandbox' if extra else 'sandbox'
        log = '%s/comparator_%s_%s.log' % (OUT, tag, key)
        t = time.time()
        r = sh('python3 %s/rss.py %s.time lake comparator --config comparator_cube10.json%s '
               '> %s 2>&1' % (W, log, extra, log), check=False, cwd=LEAN)
        tail = subprocess.run('tail -15 %s' % log, shell=True, capture_output=True, text=True).stdout
        rss = open(log + '.time').read().strip() if os.path.exists(log + '.time') else ''
        res[key] = {'rc': r.returncode, 'seconds': round(time.time() - t),
                    'max_rss_kb': rss, 'tail': tail[-1500:]}
        print('== comparator %s %s rc=%d\n%s' % (tag, key, r.returncode, tail), flush=True)
        S[tag] = res
        save()
        if not extra and r.returncode == 0:
            break
        if not extra and 'bwrap' not in tail and 'namespace' not in tail and 'sandbox' not in tail:
            break
    return res


RSS = """import resource, subprocess, sys
rc = subprocess.call(sys.argv[2:])
open(sys.argv[1], 'w').write(str(resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss))
sys.exit(rc)
"""


def main():
    setup()
    open(W + '/rss.py', 'w').write(RSS)
    S['cpu'] = subprocess.run("grep -m1 'model name' /proc/cpuinfo | cut -d: -f2; nproc; grep MemTotal /proc/meminfo",
                              shell=True, capture_output=True, text=True).stdout.split('\n')
    if not (step('build_PackingCube10', 'bash gate/build_cube10.sh')
            and step('build_ChallengeCube10', 'lake build ChallengeCube10')):
        return
    comparator('default')
    sh("sed -i 's#IsMaxMinDist 10 (3 / 4)#IsMaxMinDist 10 (2 / 3)#' ChallengeCube10.lean && "
       "grep -n 'IsMaxMinDist 10' ChallengeCube10.lean", cwd=LEAN)
    step('build_ChallengeCube10_mutated', 'lake build ChallengeCube10')
    comparator('mutation')
    save()
    sh('rm -rf %s %s %s/elan-init.sh' % (REPO, ELAN, W), check=False)


main()
