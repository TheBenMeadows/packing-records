# packing-records

Explicit configurations that improve entries in five public record tables: four for packing problems and one for the harmonic energy of points on a sphere. Every file in this repository gives coordinates that a reader can check with the included standard-library checker.

| Table | Folder | Candidate improvements | Record keeper |
|---|---|---|---|
| Grassmannian packings (N subspaces of R^m) | `grassmannian/` | 747 | Henry Cohn, https://cohn.mit.edu/grassmannian |
| Game of Sloanes (complex line packings) | `game-of-sloanes/` | 52 | https://github.com/gnikylime/GameofSloanes |
| Equal 4-D spheres in a 4-D sphere (hsp4) | `packomania-hsp4/` | 108 | Eckard Specht, https://packomania.com/hsp4/hsp4.html |
| Equal spheres in a cube (scu) | `packomania-scu/` | 216 | Eckard Specht, https://packomania.com/scu/scu.html |
| Harmonic energy (N points on the unit sphere in R^n) | `cohn-harmonic/` | 31 | Henry Cohn, https://cohn.mit.edu/harmonic-energy |

The tables were read on 2026-10-31 and 2026-11-01. The 16 Grassmannian cells added in version 1.1 were checked against the table as it read on 2026-11-03. Version 1.2 adds 57 scu cells, checked against the Packomania scu table as it read on 2026-11-04, and the harmonic-energy table, read on 2026-11-03. A result becomes a record only when its keeper lists it. Henry Cohn added the 731 Grassmannian files of version 1.0.0 to his table by 2026-11-03 (reference [24] there). The other keepers have not listed these results yet.

## What counts as an improvement

Each file beats its table entry in the table's own measure, by at least 1e-7 except where stated:

- Grassmannian: the minimum squared chordal distance, n - ||U_i^T U_j||_F^2 over all pairs of orthonormal bases, is at least 1e-10 larger than the table value. The table rounds values down to 10 decimals, so a file that clears this bar beats the true table value and changes its last printed digit. The table's keeper asks for improvements of any size. The value is below the listed upper bound where one is listed (bounds are rounded up). Starred rows and rows noted as proven optimal are excluded. Version 1.0.0 used a stricter bar (a gain of at least 1e-7, and at least 1e-8 below the bound). Its 731 files meet both.
- Game of Sloanes: the coherence, max |<phi_j, phi_k>| over unit vectors, is at least 1e-7 smaller than the leaderboard value and is not below the listed lower bound. Rows marked provably optimal are excluded.
- hsp4: the feasible radius, min(half the minimum centre distance, 1 - the largest centre norm), is at least 1e-7 larger than the table value for N and for every larger N in the table. (Removing balls from a packing for a larger N gives a packing for N, so a larger-N value is also a valid bound for N.)
- scu: the feasible radius, min(half the minimum centre distance, 1/2 - the largest absolute coordinate), is at least 1e-7 larger than B(N), the largest table value for N or any larger N.
- hsp4 and scu also: the radius is at least 1e-7 larger than the recorded polish floor for that N (see below).
- scu, from version 1.2: the floor is the largest of three numbers. The first is the polish floor. The second is the radius reached by adding one sphere at the largest hole of the posted configuration for N - 1 and polishing the result the same way. The third is the largest radius for N or any larger N in the public collection of Moki & Julio (https://github.com/Hashirama1337s/moki-julio-circle-packing, MANIFEST.csv). A cell is kept only when its radius beats that floor by at least 1e-7. `notes` in `cells.csv` records the second and third numbers where they apply.
- Harmonic energy: N unit vectors in R^n with energy E = sum_{i<j} |x_i - x_j|^-(n-2), where the exponent n - 2 depends on the dimension. Henry Cohn's table lists the lowest energies known for 4 <= n <= 32 and n+1 <= N <= 64, plus larger cases, from Ballinger, Blekherman, Cohn, Giansiracusa, Kelly and Schurmann (Experiment. Math. 18 (2009)). Their 2021 data set (https://hdl.handle.net/1721.1/130937) gives coordinates and 50-digit energies. A file counts when E is below the smaller of the table energy and the 2021 energy by at least max(1e-9, 1e-12 E). The pair (N, n) must not be a simplex (N = n+1), a cross polytope (N = 2n) or a universal optimum listed at https://cohn.mit.edu/harmonic-optima. In addition, the posted 2021 configuration, polished by L-BFGS and Newton steps, must stay above E plus the same margin. That polished energy is the row's floor in `cells.csv`, and it shows that the file is a different local minimum, not a polish of the posted one. Every stored vector has unit norm to within 1e-20 and at least 25 significant digits per coordinate.

## The polish floor

For each Packomania cell, we took the configuration posted on Packomania and improved it by sequential linear programming on its near-contacts until the step size fell below 1e-13, with three starting trust radii (1e-2, 1e-3 and 1e-4). The best radius reached is the polish floor, recorded in the `floor` column of `cells.csv`. A result that beats the floor by at least 1e-7 is not a local polish of the posted configuration.

The floor is a recorded number. `check/check_all.py` checks the margin over it but does not recompute it. To recompute it, run `floor/polish.py`, which needs numpy, scipy and the posted coordinate archives `hsp4_coords.tar.gz` and `scu_coords.tar.gz` from Packomania placed in `tables/`. The floor shows that one local method does not reach our value from the posted configuration. It does not prove that the contact graph differs.

## Check the results

Run this command from the repository root. It needs Python 3 and no other packages:

    sh check/check_all.sh

The checker reads every file, recomputes its value with exact rational arithmetic, compares it with `cells.csv` and with the table facts in `tables/`, and checks the rules above. For the harmonic table the squared distances are exact rationals. The energy needs a real power when n is odd, so it is evaluated in decimal at 60 significant digits from the exact squared distances (error below 1e-50), and every harmonic comparison uses a 1e-40 safety margin. It also confirms that every stored Grassmannian basis is orthonormal to within 1e-20, that every stored Game of Sloanes vector has unit length to within 1e-15, that every stored harmonic vector has unit norm to within 1e-20, that each cell appears once, and that the per-table counts match this README. The last line of its output is `PASS` or `FAIL`. A full run takes about 90 seconds on a laptop. `check/mutate.py ROOT` plants six defects in copies of the tree and confirms that the checker fails on each.

`cells.csv` lists every cell with our value, the table value, the margin, the polish floor where one applies, the sha256 of the file, whether the search started from the posted Packomania configuration, and the author Packomania lists for that configuration.

## File formats

- `grassmannian/<m>-<n>-<N>.txt`: line 1 is a comment that starts with `#` and states the cell, our value and the table value. Each following line is one vector of m comma-separated reals. The first n vectors span the first subspace, the next n the second, and so on. The vectors in each subspace are orthonormal.
- `game-of-sloanes/<d>x<n>.txt`: one number per line and no comments, as in the `CurrentBestPackings/` folder of the Game of Sloanes repository. The real parts of all n vectors come first, vector by vector, then the imaginary parts. Every vector has unit length.
- `packomania-hsp4/hsp4-<N>.txt`: line 1 is the radius. Each following line is one centre: index, then 4 coordinates.
- `packomania-scu/scu<N>.txt`: line 1 is the radius, then comment lines that start with `#`. Each following line is one centre: index, 3 coordinates, then the radius.
- `cohn-harmonic/<N>-<n>.txt`: line 1 is a comment that starts with `#` and states the cell, our energy, the bar and the polished energy of the posted 2021 configuration. Each following line is one unit vector of n comma-separated reals with at least 25 significant digits.

## Search methods

The searches were designed and run with AI coding assistants. They were numerical optimization runs: smoothed-maximum (log-sum-exp) descent and Riesz-energy relaxation from random starts, basin hopping, large-neighborhood search that removes and reinserts parts of a configuration, and a final sequential linear-programming polish of the active contacts. For the Packomania tables, 87 of the 108 hsp4 cells and all 216 scu cells started from the configuration posted on Packomania for that N, or for a nearby N. `cells.csv` marks each one in `started_from_posted` and names that configuration's author in `seed_author`. The harmonic configurations came from L-BFGS with a Newton finish, basin hopping from the posted 2021 configuration (perturb, or remove and reinsert 1 to 5 points), and deletion of points from larger configurations in the same dimension.

## Credit and license

Found by Benjamin Meadows, 2026. Where a search started from a posted Packomania configuration, the author of that configuration is credited in `cells.csv`.

The coordinate files, the checker, the floor code and `cells.csv` are released under CC0 1.0 (see `LICENSE`). The files in `tables/` hold only facts extracted from the five public tables and the 2021 harmonic-energy data set (dimensions, values, bounds and optimality marks), each with its source URL and the date read, so that the checker can run offline. The original tables remain the work of their keepers.
