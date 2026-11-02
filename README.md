# packing-records

Explicit configurations that improve entries in four public record tables for packing problems. Every file in this repository gives coordinates that a reader can check with the included standard-library checker.

| Table | Folder | Cells improved | Record keeper |
|---|---|---|---|
| Grassmannian packings (N subspaces of R^m) | `grassmannian/` | 731 | Henry Cohn, https://cohn.mit.edu/grassmannian |
| Game of Sloanes (complex line packings) | `game-of-sloanes/` | 52 | https://github.com/gnikylime/GameofSloanes |
| Equal 4-D spheres in a 4-D sphere (hsp4) | `packomania-hsp4/` | 108 | Eckard Specht, https://packomania.com/hsp4/hsp4.html |
| Equal spheres in a cube (scu) | `packomania-scu/` | 159 | Eckard Specht, https://packomania.com/scu/scu.html |

The tables were read on 2026-10-31 and 2026-11-01. Dated copies of the table rows used for comparison are in `tables/`. The record keepers have not yet reviewed these results. A cell counts as improved here only after its keeper lists it.

## What counts as an improvement

Each file beats its table entry by at least 1e-7 in the table's own measure:

- Grassmannian: the minimum squared chordal distance, n - ||U_i^T U_j||_F^2 over all pairs, is larger than the table value. Cells within 1e-8 of the listed upper bound are excluded, because the table rounds values down.
- Game of Sloanes: the coherence, max |<phi_j, phi_k>| over normalized vectors, is smaller than the leaderboard value and is not below the listed lower bound.
- hsp4 and scu: the feasible radius, min(half the minimum centre distance, distance from the nearest centre to the container boundary), is larger than the table value. It is also at least 1e-7 larger than the best radius that a local LP polish of the posted Packomania configuration reaches (`floor/`).

## Check the results

Run this command from the repository root. It needs Python 3 and no other packages:

    sh check/check_all.sh

The checker reads every file, recomputes its value with exact rational arithmetic, compares it with `cells.csv` and with the table snapshots in `tables/`, and checks the rules above. The last line of its output is `PASS` or `FAIL`. A full run takes about 80 seconds on a laptop.

`cells.csv` lists every cell with our value, the table value, the margin, the polish floor where one applies, the sha256 of the file, and whether the search started from the posted Packomania configuration.

## File formats

Each file uses the format of its record table:

- `grassmannian/<m>-<n>-<N>.txt`: one vector per line, m comma-separated reals. Lines 1 to n span the first subspace, lines n+1 to 2n the second, and so on.
- `game-of-sloanes/<d>x<n>.txt`: one number per line, the real parts of all vectors followed by the imaginary parts, as in the `CurrentBestPackings/` folder of the Game of Sloanes repository.
- `packomania-hsp4/hsp4-<N>.txt` and `packomania-scu/scu<N>.txt`: one centre per row (index, coordinates, radius), as in the posted Packomania files.

Lines that start with `#` are comments. The first comment line of each file states the cell, our value and the table value.

## Search methods

The searches were numerical optimization runs: smoothed-maximum (log-sum-exp) descent and Riesz-energy relaxation from random starts, basin hopping, large-neighborhood search that removes and reinserts parts of a configuration, and a final sequential linear-programming polish of the active contacts. For the Packomania tables, 87 of the 108 hsp4 cells and all 159 scu cells started from the posted configuration and then moved to a different arrangement. `cells.csv` marks each one.

`floor/polish.py` recomputes the posted-file polish floor. It needs numpy and scipy, and the posted coordinate archives `hsp4_coords.tar.gz` and `scu_coords.tar.gz` from Packomania placed in `tables/`.

## Credit and license

Found by Ben Meadows, 2026. The coordinate files, the checker and `cells.csv` are released under CC0 1.0 (see `LICENSE`). The table snapshots in `tables/` belong to their record keepers and are included only so the checker can run offline.
