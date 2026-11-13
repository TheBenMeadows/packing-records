# Lean formalization

Proofs checked by Lean 4 with Mathlib (both at v4.35.0) for three things in this repository: the simplex and orthoplex bounds that the Grassmannian and spherical-code tables print as upper bounds, a lower bound for each of the 1,486 Grassmannian cells in `cells.csv`, and the best arrangement of 2, 3, 4, 8 and 9 points in a cube. Every theorem named below depends only on Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`). No file uses `sorry` or `native_decide`.

## Theorems

| File | Theorem | Statement |
|---|---|---|
| `Packing/Rankin.lean` | `rankin_simplex` | Among N >= 2 points on a sphere of squared radius rho in a real inner product space, two are at squared distance at most 2 rho N/(N-1). |
| | `rankin_orthoplex` | Among more than d + 1 points on that sphere in dimension d, two are at squared distance at most 2 rho. |
| `Packing/Obtuse.lean` | `card_le_two_mul_finrank_of_mem` | Nonzero vectors with pairwise nonpositive inner products in a subspace of dimension d number at most 2d. |
| | `rankin_orthoplex_strict` | Among more than 2d points on that sphere, with rho > 0, two are at squared distance less than 2 rho. |
| | `chs_orthoplex_strict`, `chs_orthoplex_strict_subspace` | Among more than (m-1)(m+2) subspaces of dimension n in R^m, with 0 < n < m, two are at squared chordal distance less than n(m-n)/m. |
| `Packing/Grassmannian.lean` | `chs_simplex` | Among N >= 2 projectors of rank n on R^m, two are at squared chordal distance at most n(m-n)/m * N/(N-1). |
| | `chs_orthoplex` | Among more than m(m+1)/2 projectors of rank n on R^m, two are at squared chordal distance at most n(m-n)/m. |
| `Packing/Subspace.lean` | `chs_simplex_subspace`, `chs_orthoplex_subspace` | The same two bounds for subspaces of R^m of dimension n. |
| `Packing/Cert/Sound.lean` | `hasPacking_of_check` | If `check m n N k c` evaluates to `true`, there are N subspaces of dimension n in R^m that are pairwise at squared chordal distance at least k/10^10. |
| `Packing/Cert/All.lean` | `packing_<m>_<n>_<N>` | `HasPacking m n N (k / 10^10)` for each Grassmannian cell, 1,486 theorems. |
| `Packing/Cube.lean` | `isMaxMinDist_two`, `_three`, `_four`, `_eight`, `_nine` | The largest minimum distance among N points of the unit cube is sqrt(3), sqrt(2), sqrt(2), 1 and sqrt(3)/2 for N = 2, 3, 4, 8 and 9. |
| `Packing/CubeBalls.lean` | `maxRadius_of_maxMinDist` | If d is that largest minimum distance for N points, the largest radius of N equal balls packed in the unit cube is d/(2(1+d)). |

`Audit.lean` prints the axioms behind each of these.

## Definitions behind the statements

- `IsProjector P n`: the m x m real matrix P is symmetric, idempotent and has trace n.
- `chordalSq P Q`: `tr((P-Q)^T (P-Q)) / 2`. For two projectors of rank n this is `n - tr(PQ)` (`chordalSq_eq`), the value the repository's checker computes as `n - ||U_i^T U_j||_F^2`.
- `projMatrix U`: the matrix, in the standard basis, of Mathlib's orthogonal projection onto the subspace U of `EuclideanSpace ℝ (Fin m)`. `isProjector_projMatrix` proves that it is a projector whose trace is the dimension of U.
- `subspaceChordalSq U V`: `chordalSq (projMatrix U) (projMatrix V)`.
- `HasPacking m n N t`: there is a family of N subspaces of `EuclideanSpace ℝ (Fin m)`, each of dimension n, with `t <= subspaceChordalSq (U i) (U j)` for all `i != j`.
- `IsMaxMinDist N d`: some N points of `[0,1]^3` are pairwise at distance at least d, and any N points of `[0,1]^3` include two at distance at most d.
- `IsMaxRadius N r`: some N balls of radius r fit in the unit cube with disjoint interiors, and no larger radius does. A packing is given by its centres: every coordinate of a centre is in `[r, 1-r]`, and two centres are at distance at least 2r.

## Limits of what is proved

- The simplex and orthoplex theorems are inequalities. The configurations that attain them are not characterized. The condition N <= m(m+1)/2 for equality in the simplex bound is not formalized. The condition N <= (m-1)(m+2) for equality in the orthoplex bound is `chs_orthoplex_strict`.
- A cell theorem states that a packing with that minimum distance exists. It does not state that the packing is optimal.
- Lean does not prove that the subspaces it uses are the spans of the vectors in `grassmannian/<cell>.txt`. The generator derives the Lean data from that file (step 1 of the next section), and the theorem holds for the data.
- The other tables of the repository (spherical codes, Game of Sloanes, Packomania, harmonic energy, Thomson) have no Lean certificates.
- For points in a cube, N = 5, 6, 10 and 14 are solved in the literature and are not formalized here. `IsMaxRadius` takes the description of a ball packing by its centres as a definition. It is not derived from `Metric.ball`.

## Cell certificates

1. `gen/gen_cert.py` reads `grassmannian/<m>-<n>-<N>.txt` with the parser of `check/exact.py`, scales the decimals to integers, and runs exact integer Gram-Schmidt on the n vectors of each subspace. It writes the orthogonal vectors as data. A vector is stored as a list of natural numbers `e` and an offset `off`, which stand for the integer vector `e - off`, with the sum of `e` and the squared norm of the vector.
2. `Packing.Cert.check` verifies the data. There are N frames of n vectors of length m. Every stored sum and squared norm is correct, and every squared norm is positive. The vectors of each frame are pairwise orthogonal. For every two frames F and G, the sum over u in F and v in G of `floor(10^40 (u.v)^2 / (|u|^2 |v|^2)) + 1` is at most `(n 10^10 - k) 10^30`.
3. `hasPacking_of_check` proves that these checks give the bound. The orthogonal projector onto the span of an orthogonal frame is the sum of `w w^T / |w|^2` over its vectors, so `tr(P_F P_G)` is the sum of `(u.v)^2 / (|u|^2 |v|^2)`, and the squared chordal distance is n minus that trace.
4. Each cell file states `check m n N k data = true` and closes it with `decide +kernel`. The Lean kernel evaluates the checker on the data. The compiler is not trusted.

Step 2 checks everything step 3 needs, so an error in the generator cannot produce a false theorem. It can make a check fail, or produce a bound for subspaces other than the file's.

The bound of a cell is k/10^10, where k is the largest integer the checker accepts. The generator stops if k differs from the cell's `our_value` rounded down to 10 decimals, or if k does not exceed the table value. For all 1,486 cells k equals `our_value` rounded down to 10 decimals. `cells_manifest.tsv` lists k and the table value for each cell.

The `+ 1` in step 2 makes the bound strict. A pair of lines at squared chordal distance exactly 1/2 is accepted at k = 4999999999 and rejected at k = 5000000000. `Packing/Cert/Test.lean` holds 13 cases with known answers, among them this one, a wrong norm, a wrong sum and a frame that is not orthogonal.

## Build

Requirements: `elan`, and 11 GB of disk for the toolchain, Mathlib and its cache.

```
cd lean
lake exe cache get
lake build
lake env lean Audit.lean
```

`lake build` compiles the bounds, the cube theorems, the checker, its soundness proof and the tests. Every line that `Audit.lean` prints must end with `[propext, Classical.choice, Quot.sound]`.

To check the cells:

```
python3 gen/gen_cert.py
lake build PackingCells
```

The generator writes one file per cell under `Packing/Cert/Cells/` (1,486 files, 264 MB, ignored by git), then `Packing/Cert/All.lean` and `cells_manifest.tsv`. `lake build PackingCells` starts one Lean process per core. To check one cell, run `python3 gen/gen_cert.py 6-2-15` and then `lake build Packing.Cert.Cells.C_6_2_15`.

## Run record

The check of all 1,486 cells, one Lean process at a time on a shared 2013 Xeon E5-1650 v2, was still running when this file was committed. `cells_results.tsv` is added when it finishes. Earlier partial passes, on earlier forms of the cell files, checked 876 and then 1,038 cells. The only failure was cell 15-2-60: its data literal exceeded the recursion limit of the elaborator, and the cell files now set `maxRecDepth`.

## Notes on kernel speed

These measurements on cell 11-2-60 decided the shape of `Check.lean`.

- Recursion written with `List.rec` took 5.1 s. The same checker written with pattern matching took 11.8 s.
- Natural-number arithmetic took 5.1 s. Integer arithmetic took 18.5 s. The kernel evaluates `Nat.add`, `Nat.mul`, `Nat.div` and `Nat.sub` on literals natively and unfolds everything on `Int`, so signed entries are stored as a natural number minus an offset.
- A data literal with negative integers written as `-5` did not elaborate within the default heartbeat limit for 1,320 entries. Natural-number literals inside a structure elaborate in about one second.
- The data of a cell is a `noncomputable def`. For cell 15-2-60 the compiled file is 0.54 MB that way and 5.0 MB when Lean also generates code for the data.

## References

- R. A. Rankin, "The closest packing of spherical caps in n dimensions", Proc. Glasgow Math. Assoc. 2 (1955), 139-144.
- J. H. Conway, R. H. Hardin and N. J. A. Sloane, "Packing lines, planes, etc.: packings in Grassmannian spaces", Experimental Mathematics 5 (1996), 139-159.
- J. Schaer, "On the densest packing of spheres in a cube", Canad. Math. Bull. 9 (1966), 265-270.

The Lean files and the generator were written with AI coding assistants. The Lean kernel checks every proof.
