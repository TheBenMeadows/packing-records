"""Posted-file polish floor: sequential LP with an L-infinity trust region on the
near-active contacts, written for the final verification pass. For each largest step s0 in
(1e-2, 1e-3, 1e-4) the trust radius starts at s0, a step is accepted only if the
true feasible radius (recomputed from the moved centres) increases, otherwise
the radius is halved; the run stops when the radius falls below 1e-13 (it has
stopped improving) or after 3000 LPs.

usage: python3 polish.py jobs.json out.jsonl   (jobs: [{table, N, src, s0}])
"""
import io, json, math, os, sys, tarfile, time
import numpy as np
from multiprocessing import Pool
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
from scipy.spatial import cKDTree

DATA = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'tables') + '/'


def load_posted(table, N):
    tf = DATA + ('hsp4_coords.tar.gz' if table == 'hsp4' else 'scu_coords.tar.gz')
    name = ('hsp4-%d.txt' if table == 'hsp4' else 'scu%d.txt') % N
    with tarfile.open(tf) as t:
        txt = t.extractfile(name).read().decode()
    d = 4 if table == 'hsp4' else 3
    rows = []
    for i, line in enumerate(txt.splitlines()):
        s = line.strip()
        if i == 0 or not s or s.startswith('#'):
            continue
        f = s.split()
        rows.append([float(x) for x in f[1:1 + d]])
    P = np.array(rows)
    assert P.shape == (N, d), (table, N, P.shape)
    return P


def true_r(P, table):
    tree = cKDTree(P)
    dd, _ = tree.query(P, k=2)
    half = dd[:, 1].min() / 2
    if table == 'hsp4':
        wall = 1 - np.sqrt((P ** 2).sum(1)).max()
    else:
        wall = 0.5 - np.abs(P).max()
    return min(half, wall)


def lp_step(P, r0, s, table):
    N, d = P.shape
    nv = N * d + 1
    rows, cols, vals, rhs = [], [], [], []
    k = 0
    tree = cKDTree(P)
    cut = 2 * r0 + 4 * math.sqrt(d) * s + 1e-9
    pairs = np.array(sorted(tree.query_pairs(cut)), dtype=int).reshape(-1, 2)
    if len(pairs):
        diff = P[pairs[:, 0]] - P[pairs[:, 1]]
        dist = np.sqrt((diff ** 2).sum(1))
        u = diff / dist[:, None]
        for (i, j), uu, dij in zip(pairs, u, dist):
            # 2 r - u.(di - dj) <= dij
            for a in range(d):
                rows += [k, k]; cols += [i * d + a, j * d + a]; vals += [-uu[a], uu[a]]
            rows.append(k); cols.append(nv - 1); vals.append(2.0); rhs.append(dij); k += 1
    if table == 'hsp4':
        nrm = np.sqrt((P ** 2).sum(1))
        for i in np.where(1 - nrm <= r0 + 2 * math.sqrt(d) * s + 1e-9)[0]:
            uu = P[i] / nrm[i]
            for a in range(d):
                rows.append(k); cols.append(i * d + a); vals.append(uu[a])
            rows.append(k); cols.append(nv - 1); vals.append(1.0); rhs.append(1 - nrm[i]); k += 1
    else:
        A = np.abs(P)
        for i, a in zip(*np.where(0.5 - A <= r0 + s + 1e-9)):
            sg = 1.0 if P[i, a] >= 0 else -1.0
            rows += [k, k]; cols += [i * d + a, nv - 1]; vals += [sg, 1.0]; rhs.append(0.5 - A[i, a]); k += 1
    Aub = coo_matrix((vals, (rows, cols)), shape=(k, nv)).tocsr()
    c = np.zeros(nv); c[-1] = -1.0
    bounds = [(-s, s)] * (N * d) + [(None, None)]
    res = linprog(c, A_ub=Aub, b_ub=np.array(rhs), bounds=bounds, method='highs',
                  options={'time_limit': 120})
    if res.status != 0 or res.x is None:
        return None
    return P + res.x[:-1].reshape(N, d)


def polish(P, table, s0, max_lp=3000, s_min=1e-13):
    r = true_r(P, table)
    r_start = r
    s = s0
    n = 0
    acc = 0
    while s >= s_min and n < max_lp:
        n += 1
        Q = lp_step(P, r, s, table)
        if Q is not None:
            rq = true_r(Q, table)
            if rq > r:
                P, r = Q, rq
                acc += 1
                continue
        s *= 0.5
    return r_start, r, n, acc, s


def job(j):
    t0 = time.time()
    P = load_posted(j['table'], j['src'])
    r_start, r, n, acc, s = polish(P, j['table'], j['s0'])
    return dict(j, posted_r=r_start, polished_r=r, lps=n, accepted=acc, final_s=s, secs=round(time.time() - t0, 1))


if __name__ == '__main__':
    jobs = json.load(open(sys.argv[1]))
    with Pool(4) as pool, open(sys.argv[2], 'a') as out:
        for res in pool.imap_unordered(job, jobs):
            out.write(json.dumps(res) + '\n'); out.flush()
            print(json.dumps(res), flush=True)
