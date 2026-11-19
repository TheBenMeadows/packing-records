#!/opt/homebrew/bin/uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy==2.5.5", "scipy==1.18.1"]
# ///
"""Driver: symmetry classes of the 8008 key patterns under the 8 reflections, one tree per class.
usage: gen_n10_run.py part nparts outdir mincut lpw
Writes outdir/rNNNN.json for every class NNNN of this part that has no file yet."""
import sys, os, json, itertools, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_n10 as g

def keyT(t, k):
    a, b, c = t & 1, (t >> 1) & 1, (t >> 2) & 1
    qx, qy, z = k % 2, (k // 2) % 2, k // 4
    if a: qx = 1 - qx
    if b: qy = 1 - qy
    if c: z = 3 - z
    return qx + 2 * qy + 4 * z

def classes():
    pats = list(itertools.combinations(range(16), 10))
    rep_of = {}
    for p in pats:
        imgs = [(tuple(sorted(keyT(t, k) for k in p)), t) for t in range(8)]
        rep_of[p] = min(imgs)
    reps = sorted(set(v[0] for v in rep_of.values()))
    return pats, rep_of, reps

if __name__ == '__main__':
    part, nparts, outdir = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    g.MINCUT = int(sys.argv[4]); lpw = int(sys.argv[5])
    pats, rep_of, reps = classes()
    if part == 0:
        print('classes', len(reps), flush=True)
    todo = {i for i in range(len(reps))
            if i % nparts == part and not os.path.exists('%s/r%04d.json' % (outdir, i))}
    for idx, rep in enumerate(reps):
        if idx not in todo:
            continue
        t0 = time.time()
        try:
            out, ctx = g.solve(list(rep), use_lp=lpw, limit=400000)
            res = {'rep': rep, 'nodes': out}
            st = 'ok'
        except g.Fail as e:
            res = {'rep': rep, 'fail': True}
            st = 'FAIL'
        json.dump(res, open('%s/r%04d.json' % (outdir, idx), 'w'))
        print(idx, rep, st, len(res.get('nodes', [])), '%.1fs' % (time.time() - t0), flush=True)
