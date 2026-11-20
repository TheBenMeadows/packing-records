"""Clean-clone gate for the ten-point theorem of packing-records.

Runs as a Kaggle script kernel with one dataset attached that holds the lean/ directory.
Clones the public repository at a pinned commit, lays the lean/ directory of the unpushed branch
over it (from the private dataset), installs the pinned Lean toolchain, checks that Challenge/
matches a fresh run of gen_challenge.py, builds PackingCube10 with gate/build_cube10.sh (one data file at a time) and prints the axioms of
Packing.Cube.isMaxMinDist_ten. Everything it reports is in /kaggle/working/out.
"""
import hashlib, json, os, subprocess, time

PIN = '10bb9a04563a7818852710dfb24cda45631d3470'
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
    # The pinned commit may hold generated Cube10 files that the tree no longer has.
    sh('rm -f %s/Packing/Cube10*.lean' % LEAN)
    tars = [os.path.join(d, f) for d, _, fs in os.walk('/kaggle/input') for f in fs
            if f == 'lean.tar.gz']
    if tars:
        sh('tar -xzf %s -C %s' % (tars[0], REPO))
    else:  # Kaggle unpacked the archive: find the directory that holds the lakefile
        src = [d for d, _, fs in os.walk('/kaggle/input') if 'lakefile.toml' in fs][0]
        sh('mkdir -p %s && cp -r %s/. %s/' % (LEAN, src, LEAN))
    sha = tree_sha(LEAN)
    sh('curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o '
       '%s/elan-init.sh && sh %s/elan-init.sh -y --no-modify-path --default-toolchain none '
       '> /dev/null' % (W, W))
    sh('lake exe cache get > %s/cache.log 2>&1; tail -2 %s/cache.log' % (OUT, OUT), cwd=LEAN)
    return sha


def main():
    s = {'pin': PIN}
    s['lean_tree_sha256'] = setup()
    s['repo_head'] = out('git rev-parse HEAD', cwd=REPO)
    s['lean_version'] = out('lake env lean --version', cwd=LEAN)
    s['cpu'] = out("grep -m1 'model name' /proc/cpuinfo | cut -d: -f2") + ' x' + out('nproc')
    s['cube10_files'] = int(out('ls Packing/Cube10*.lean | wc -l', cwd=LEAN))
    s['challenge_check_rc'] = sh('python3 -I gen/gen_challenge.py --check', check=False, cwd=LEAN).returncode
    s['sorry_or_native_decide'] = out("grep -l -E '\\bsorry\\b|native_decide' Packing/Cube10*.lean | wc -l", cwd=LEAN)
    t = time.time()
    b = sh('bash gate/build_cube10.sh > %s/build.log 2>&1' % OUT, check=False, cwd=LEAN)
    s['build_rc'] = b.returncode
    s['build_seconds'] = round(time.time() - t)
    sh('cat %s/build.log | tail -60' % OUT, check=False)
    s['mem_total_kb'] = out("grep MemTotal /proc/meminfo | tr -s ' ' | cut -d' ' -f2")
    sh('lake env lean AuditCube10.lean > %s/audit.txt 2>&1' % OUT, check=False, cwd=LEAN)
    s['audit'] = open(OUT + '/audit.txt').read().strip().split('\n')
    s['wall_seconds'] = round(time.time() - T0)
    json.dump(s, open(OUT + '/summary.json', 'w'), indent=1)
    print(json.dumps(s, indent=1), flush=True)
    sh('rm -rf %s %s %s/elan-init.sh' % (REPO, ELAN, W))


main()
