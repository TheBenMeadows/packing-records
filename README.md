# packing-records

Explicit configurations that improve entries in four public record tables for packing problems. Every file in this repository gives coordinates that a reader can check with the included standard-library checker.

| Table | Folder | Candidate improvements | Record keeper |
|---|---|---|---|
| Grassmannian packings (N subspaces of R^m) | `grassmannian/` | 731 | Henry Cohn, https://cohn.mit.edu/grassmannian |
| Game of Sloanes (complex line packings) | `game-of-sloanes/` | 52 | https://github.com/gnikylime/GameofSloanes |
| Equal 4-D spheres in a 4-D sphere (hsp4) | `packomania-hsp4/` | 108 | Eckard Specht, https://packomania.com/hsp4/hsp4.html |
| Equal spheres in a cube (scu) | `packomania-scu/` | 159 | Eckard Specht, https://packomania.com/scu/scu.html |

The tables were read on 2026-10-31 and 2026-11-01. The record keepers have not reviewed these results yet. A result becomes a record only when its keeper lists it.

## What counts as an improvement

Each file beats its table entry by at least 1e-7 in the table's own measure:

- Grassmannian: the minimum squared chordal distance, n - ||U_i^T U_j||_F^2 over all pairs of orthonormal bases, is at least 1e-7 larger than the table value. The table rounds values down to 10 decimals, so the checker adds 1e-10 to the table value before the comparison. Starred rows and rows noted as proven optimal are excluded. Cells within 1e-8 of the listed upper bound are excluded, because there the gain can be an artifact of the table's rounding.
- Game of Sloanes: the coherence, max |<phi_j, phi_k>| over unit vectors, is at least 1e-7 smaller than the leaderboard value and is not below the listed lower bound. Rows marked provably optimal are excluded.
- hsp4: the feasible radius, min(half the minimum centre distance, 1 - the largest centre norm), is at least 1e-7 larger than the table value for N and for every larger N in the table. (Removing balls from a packing for a larger N gives a packing for N, so a larger-N value is also a valid bound for N.)
- scu: the feasible radius, min(half the minimum centre distance, 1/2 - the largest absolute coordinate), is at least 1e-7 larger than B(N), the largest table value for N or any larger N.
- hsp4 and scu also: the radius is at least 1e-7 larger than the recorded polish floor for that N (see below).

## The polish floor

For each Packomania cell, we took the configuration posted on Packomania and improved it by sequential linear programming on its near-contacts until the step size fell below 1e-13, with three starting trust radii (1e-2, 1e-3 and 1e-4). The best radius reached is the polish floor, recorded in the `floor` column of `cells.csv`. A result that beats the floor by at least 1e-7 is not a local polish of the posted configuration.

The floor is a recorded number. `check/check_all.py` checks the margin over it but does not recompute it. To recompute it, run `floor/polish.py`, which needs numpy, scipy and the posted coordinate archives `hsp4_coords.tar.gz` and `scu_coords.tar.gz` from Packomania placed in `tables/`. The floor shows that one local method does not reach our value from the posted configuration. It does not prove that the contact graph differs.

## Check the results

Run this command from the repository root. It needs Python 3 and no other packages:

    sh check/check_all.sh

The checker reads every file, recomputes its value with exact rational arithmetic, compares it with `cells.csv` and with the table facts in `tables/`, and checks the rules above. It also confirms that every stored Grassmannian basis is orthonormal to within 1e-20, that every stored Game of Sloanes vector has unit length to within 1e-15, that each cell appears once, and that the per-table counts match this README. The last line of its output is `PASS` or `FAIL`. A full run takes about 80 seconds on a laptop.

`cells.csv` lists every cell with our value, the table value, the margin, the polish floor where one applies, the sha256 of the file, whether the search started from the posted Packomania configuration, and the author Packomania lists for that configuration.

## File formats

- `grassmannian/<m>-<n>-<N>.txt`: line 1 is a comment that starts with `#` and states the cell, our value and the table value. Each following line is one vector of m comma-separated reals. The first n vectors span the first subspace, the next n the second, and so on. The vectors in each subspace are orthonormal.
- `game-of-sloanes/<d>x<n>.txt`: one number per line and no comments, as in the `CurrentBestPackings/` folder of the Game of Sloanes repository. The real parts of all n vectors come first, vector by vector, then the imaginary parts. Every vector has unit length.
- `packomania-hsp4/hsp4-<N>.txt`: line 1 is the radius. Each following line is one centre: index, then 4 coordinates.
- `packomania-scu/scu<N>.txt`: line 1 is the radius, then comment lines that start with `#`. Each following line is one centre: index, 3 coordinates, then the radius.

## Search methods

The searches were designed and run with AI coding assistants. They were numerical optimization runs: smoothed-maximum (log-sum-exp) descent and Riesz-energy relaxation from random starts, basin hopping, large-neighborhood search that removes and reinserts parts of a configuration, and a final sequential linear-programming polish of the active contacts. For the Packomania tables, 87 of the 108 hsp4 cells and all 159 scu cells started from the configuration posted on Packomania for that N, or for a nearby N. `cells.csv` marks each one in `started_from_posted` and names that configuration's author in `seed_author`.

## Credit and license

Found by Benjamin Meadows, 2026. Where a search started from a posted Packomania configuration, the author of that configuration is credited in `cells.csv`.

The coordinate files, the checker, the floor code and `cells.csv` are released under CC0 1.0 (see `LICENSE`). The files in `tables/` hold only facts extracted from the four public tables (dimensions, values, bounds and optimality marks), each with its source URL and the date read, so that the checker can run offline. The original tables remain the work of their keepers.
