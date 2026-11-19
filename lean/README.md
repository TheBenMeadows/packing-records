# Lean formalization

Proofs checked by Lean 4 with Mathlib (both at v4.35.0) for three things in this repository: the simplex and orthoplex bounds that the Grassmannian and spherical-code tables print as upper bounds, a certificate for 2,489 of the 6,829 cells of the seven distance tables in `cells.csv`, and the best arrangement of 2, 3, 4, 5, 6, 8, 9 and 10 points in a cube, with its uniqueness for each of those N except 10. Every theorem named below depends only on Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`). No file of the library uses `sorry` or `native_decide`. The statements in `Challenge/` end in `sorry` on purpose (see "Statements checked with `lake comparator`").

## Coverage of the tables

The cell certificates were generated and checked for the files of version 1.4 of this repository: all 2,817 cells of its seven distance tables. Version 1.5 replaced 1,837 of those files, removed 63 cells and added 4,075. A certificate is tied to its data file through the sha256 in `cells.csv`, so only the certificates of the 917 cells whose file is the same in both versions carried over. The 1,572 other Grassmannian cells of version 1.5 were generated and checked again on 2026-11-15. `cells_scope.txt` lists the 2,489 cells with a certificate, and the generators, the three lists, the manifests and the result files cover these cells only.

| Table | Cells in version 1.5 | With a certificate |
|---|---|---|
| Grassmannian | 1,658 | 1,658 |
| Spherical codes | 4,369 | 29 |
| Game of Sloanes | 52 | 52 |
| Packomania hsp4, hsp5, hsp6 | 511 | 511 |
| Packomania scu | 239 | 239 |

The other 4,340 cells, all spherical codes, have no Lean certificate yet. To add cells, list them in `cells_scope.txt` and run the generators and the checks of "Build" again.

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
| `Packing/Cube.lean` | `isMaxMinDist_two`, `_three`, `_four`, `_eight`, `_nine` | The largest minimum distance among N points of the unit cube is sqrt(3), sqrt(2), sqrt(2), 1 and sqrt(3)/2 for N = 2, 3, 4, 8 and 9. |
| `Packing/Cube5.lean` | `isMaxMinDist_five` | The largest minimum distance among 5 points of the unit cube is sqrt(5)/2. |
| | `isMaxRadius_five` | The largest radius of 5 equal balls packed in the unit cube is (5 - 2 sqrt(5))/2. |
| `Packing/Cube5Unique.lean` | `isUniqueMaxMinDist_five` | Every arrangement of 5 points of the unit cube with pairwise distances at least sqrt(5)/2 is the image of Schaer's arrangement, in some order, under a symmetry of the cube. |
| | `isUniqueUpToIsometry_five` | Every such arrangement is congruent to Schaer's. |
| `Packing/CubeUnique.lean` | `isUniqueMaxMinDist_two` | Two points of the unit cube at distance at least sqrt(3) are two opposite corners. |
| `Packing/CubeUniqueSmall.lean` | `isUniqueMaxMinDist_three`, `isUniqueMaxMinDist_four` | Three or four points of the unit cube pairwise at distance at least sqrt(2) are corners of a regular tetrahedron inscribed in the cube. |
| `Packing/Cube8Unique.lean` | `isUniqueMaxMinDist_eight` | Eight points of the unit cube pairwise at distance at least 1 are the eight corners. |
| `Packing/Cube9Unique.lean` | `isUniqueMaxMinDist_nine` | Nine points of the unit cube pairwise at distance at least sqrt(3)/2 are the centre and the eight corners. |
| `Packing/Cube10.lean` | `isMaxMinDist_ten` | The largest minimum distance among 10 points of the unit cube is 3/4. Built by `lake build PackingCube10`, not by `lake build`. |
| `Packing/Cube6.lean` | `isMaxMinDist_six` | The largest minimum distance among 6 points of the unit cube is 3 sqrt(2)/4. |
| | `isMaxRadius_six` | The largest radius of 6 equal balls packed in the unit cube is (9 - 6 sqrt(2))/2. |
| `Packing/Cube6Unique.lean` | `isUniqueMaxMinDist_six` | Every arrangement of 6 points of the unit cube with pairwise distances at least 3 sqrt(2)/4 is the image of Schaer's octahedron, in some order, under a symmetry of the cube. |
| | `isUniqueUpToIsometry_six` | Every such arrangement is congruent to Schaer's. |
| `Packing/CubeBalls.lean` | `maxRadius_of_maxMinDist` | If d is that largest minimum distance for N points, the largest radius of N equal balls packed in the unit cube is d/(2(1+d)). |
| `Packing/Cert/Sound.lean` | `hasPacking_of_check` | If `check m n N k c` evaluates to `true`, there are N subspaces of dimension n in R^m that are pairwise at squared chordal distance at least k/10^10. |
| `Packing/Cert/SoundLink.lean` | `spansPack_of_link` | If `checkLink m n R c K` also evaluates to `true`, those subspaces are the spans of the vectors in R, the vectors of the data file. |
| `Packing/Cert/SoundPoints.lean` | `hasSphericalCode_of_check` | If `checkSph d N t c` evaluates to `true`, there are N unit vectors in R^d with pairwise inner products at most t/10^12. |
| | `hasBallPackingInBall_of_check` | If `checkBall d N t S c` evaluates to `true`, N balls of radius t/10^12 fit in the unit ball of R^d with disjoint interiors. |
| | `hasBallPackingInCube_of_check` | If `checkCube N t S c` evaluates to `true`, N balls of radius t/10^12 fit in the unit cube with disjoint interiors. |
| `Packing/Cert/SoundCoh.lean` | `hasCoherence_of_check` | If `checkCoh d N t c` evaluates to `true`, there are N unit vectors in C^d whose pairwise Hermitian products have absolute value at most t/10^12. |

The generated files hold two instances of these theorems per cell.

| Generated file | Cells | Theorems per cell |
|---|---|---|
| `Packing/Cert/All.lean` | 1,658 Grassmannian | `packing_<m>_<n>_<N> : HasPacking m n N (k / 10^10)` |
| `Packing/Cert/AllLinks.lean` | 1,658 Grassmannian | `packing_file_<m>_<n>_<N> : SpansPack m n N (k / 10^10) <vectors of the file>` |
| `Packing/Cert/AllPoints.lean` | 29 spherical codes | `sph_<d>_<N> : HasSphericalCode d N (t / 10^12)` and `sph_file_<d>_<N>` |
| | 52 Game of Sloanes | `gos_<d>_<N> : HasCoherence d N (t / 10^12)` and `gos_file_<d>_<N>` |
| | 511 Packomania hsp4, hsp5, hsp6 | `hsp4_<N> : HasBallPackingInBall 4 N (t / 10^12)` and `hsp4_file_<N>`; the same for hsp5 and hsp6 |
| | 239 Packomania scu | `scu_<N> : HasBallPackingInCube N (t / 10^12)` and `scu_file_<N>` |

A `_file_` theorem states the property for the data of the cell, which are the numbers of the data file multiplied by one power of ten. It includes the number of vectors and the number of entries of each vector. The other theorem states that a configuration with the property exists.

`Audit.lean` prints the axioms behind the theorems of the first table.

## Definitions behind the statements

- `IsProjector P n`: the m x m real matrix P is symmetric, idempotent and has trace n.
- `chordalSq P Q`: `tr((P-Q)^T (P-Q)) / 2`. For two projectors of rank n this is `n - tr(PQ)` (`chordalSq_eq`), the value the repository's checker computes as `n - ||U_i^T U_j||_F^2`.
- `projMatrix U`: the matrix, in the standard basis, of Mathlib's orthogonal projection onto the subspace U of `EuclideanSpace ℝ (Fin m)`. `isProjector_projMatrix` proves that it is a projector whose trace is the dimension of U.
- `subspaceChordalSq U V`: `chordalSq (projMatrix U) (projMatrix V)`.
- `HasPacking m n N t`: there is a family of N subspaces of `EuclideanSpace ℝ (Fin m)`, each of dimension n, with `t <= subspaceChordalSq (U i) (U j)` for all `i != j`.
- `SpansPack m n N t R`: R holds N lists of n vectors with m entries each, each span has dimension n, and every two spans are at squared chordal distance at least t.
- `HasSphericalCode d N t`: there are N vectors of norm 1 in `EuclideanSpace ℝ (Fin d)` with pairwise inner products at most t.
- `HasCoherence d N t`: there are N vectors of norm 1 in `EuclideanSpace ℂ (Fin d)` with `|<x i, x j>| <= t` for all `i != j`.
- `HasBallPackingInBall d N r`: r is nonnegative and there are N centres in `EuclideanSpace ℝ (Fin d)`, each of norm at most `1 - r`, pairwise at distance at least 2r.
- `HasBallPackingInCube N r`: r is nonnegative and there are N centres whose coordinates lie in `[r, 1 - r]`, pairwise at distance at least 2r.
- `SphericalData d N t c`, `CoherenceData d N t c`, `BallData d N S r c`, `CubeData N S r c`: the data c hold N vectors with d entries each (3 for the cube), and those vectors have the property after normalization (the two code tables), after division by the positive scale S (the two ball tables) and after the move to `[0, 1]^3` (the cube).
- `IsMaxMinDist N d`: some N points of `[0,1]^3` are pairwise at distance at least d, and any N points of `[0,1]^3` include two at distance at most d.
- `IsMaxRadius N r`: `HasBallPackingInCube N r` holds and no larger radius has that property.
- `cubeSymm v σ`: the map of `[0,1]^3` to itself that permutes the coordinates by σ and then replaces x by 1 - x in the coordinates where v is true. These are the 48 symmetries of the cube.
- `IsUniqueUpToCubeSymm N d q`: every family of N points of `[0,1]^3` with pairwise distances at least d is `cubeSymm v σ` applied to q, with the points in some order. `IsUniqueUpToIsometry N d q` is the same with any isometry of space. The first implies the second. Both hold for every q when no family is feasible.
- `IsUniqueMaxMinDist N d q`: q lies in `[0,1]^3` with pairwise distances at least d, any N points of `[0,1]^3` include two at distance at most d, and `IsUniqueUpToCubeSymm N d q` holds. It implies `IsMaxMinDist N d`.

The families in these definitions are indexed, so two members can coincide. They cannot coincide when t > 0 for subspaces, when t < 1 for unit vectors and lines, or when r > 0 for centres. Outside those ranges, and for N <= 1, the existence statements hold for trivial reasons. `IsMaxMinDist N d` is false for every d when N <= 1, and `IsMaxRadius 0 r` is false for every r. In the 917 cells N is at least 6, every Grassmannian bound is at least 0.07, every cosine and coherence bound is between 0.13 and 0.81, and every radius is at least 0.05.

## Limits of what is proved

- The simplex and orthoplex theorems are inequalities. The configurations that attain them are not characterized. The condition N <= m(m+1)/2 for equality in the simplex bound is not formalized. The condition N <= (m-1)(m+2) for equality in the orthoplex bound is `chs_orthoplex_strict`.
- A cell theorem states that a configuration with that value exists. It does not state that the configuration is optimal, and it does not compare the value with the table. The generators make that comparison, and `check/check_all.sh` makes it independently.
- The Lean data of a cell are written by a generator from the data file. Lean does not read the data file. Each generator stops unless the file has the sha256 recorded in `cells.csv`, and the manifests record that sha256.
- `HasBallPackingInBall` and `HasBallPackingInCube` describe a packing by its centres. They are not derived from `Metric.ball`.
- The harmonic-energy and Thomson tables have no Lean certificates. Their values need square roots and real powers.
- For points in a cube, N = 14 is solved in the literature and is not formalized here. Uniqueness of the configuration is proved for N = 2, 3, 4, 5, 6, 8 and 9. For N = 10 only the value is proved; Schaer's paper also proves that the arrangement is unique.
- The proof for N = 10 is a case analysis found by a search and checked by the kernel. It is not a formalization of Schaer's proof, which we have not read. `isMaxMinDist_ten` is not among the theorems of `comparator.json`, and `Audit.lean` does not print its axioms; `AuditCube10.lean` does.

## Five points in a cube

`Packing/Cube5.lean` follows Schaer's proof with strict inequalities. Take five points of the cube that are pairwise further apart than sqrt(5)/2. Among all points and all corners, take the pair with the least coordinatewise distance a. A reflection and a swap of coordinates move that corner to the origin and that point to (p1, p2, a) with p1, p2 <= a <= 1/2, and then every point has a coordinate at distance at least a from every corner. The proof then needs:

1. No other point y has y1 + y2 + y3 <= 3/2 and y1 + y2 <= 3/2 - a, because such a point is within sqrt(5)/2 of (p1, p2, a).
2. Two of the other four points have the same least coordinate, and two such points are within sqrt(5)/2 of each other.

Both facts are polynomial inequalities on polytopes: 28 of degree 4 in four variables for the first, 5 of degree 3 in seven variables for the second. `gen/gen_n5.py` finds, for each one, nonnegative rational coefficients that write the difference of the two sides as a combination of products of the constraints. It checks that identity in exact arithmetic and writes the lemma to `Packing/Cube5Cert.lean` with the products as hints. Lean's `linarith` then proves the lemma from the hints and finds its own coefficients. The generated file is in the repository, so the build does not run the generator, which needs `numpy` and `scipy`.

### Uniqueness

`Packing/Cube5Unique.lean` runs the same argument with the distances at least sqrt(5)/2 and follows where each inequality is tight. If a = 0, one point is a corner, the opposite corner is forced, and the other three points are alternate vertices of the hexagon cut from the cube by the plane through its centre; the two choices are mirror images. If a > 0, the first fact can be tight only at a = 1/2, and the second forces a = 0.

Schaer's text takes 0 < a <= 1/2 in one step, with strict inequality in the first fact. At a = 1/2 the points (0, 1/2, 1/2) and (1, 0, 1/2) satisfy its hypotheses at distance exactly sqrt(5)/2, so the formal proof treats a = 1/2 separately: the two points are then determined, and two of the remaining three points are too close to each other.

`gen/gen_n5_unique.py` writes the 61 lemmas of `Packing/Cube5EqCert.lean` that locate the tight cases. Each comes from an identity of the same kind as before, with one more term subtracted from the gap: a multiple of the constraints that vanish at the extremal point, or of a(1 - 2a), or of a.

## Six points in a cube

`Packing/Cube6.lean` follows Schaer's proof with strict inequalities. Take six points of the cube that are pairwise further apart than 3 sqrt(2)/4, so at squared distance more than 9/8.

1. A half-cube of side 1/2 has squared diameter 3/4, so the six points lie in six different half-cubes and two half-cubes are empty.
2. `push`: two points in half-cubes that share a face are more than 3/4 apart across that face. Each is then within 1/4 of the opposite face of the cube.
3. `prism_three`: a slab `[0,1] x [0,1] x [0,1/4]` does not hold three of the points.
4. `layer_full`: the four half-cubes of one layer do not all hold a point. Steps 2 and 3 would confine the other two points to a box of side 1/2. So every layer has an empty half-cube, and the two empty half-cubes are opposite.
5. `six_normal`: with the empty half-cubes at (0,0,0) and (1,1,1), steps 2 and 3 put the three points nearest the origin in the cube `[0, 3/4]^3`, where two of three points are at squared distance at most 9/8.

Step 3 is the one inequality here that is not a bound on a diameter. For three points in three given quadrants of the square, `gen/n6_prism_search.py` finds by linear programming three nonnegative polynomials of degree 2, one per pair of points, and a nonnegative combination of products of the constraints, such that the sum of the polynomials times `9/8 - d^2` equals that combination. `gen/gen_n6_prism.py` solves for exact rational coefficients on the support the search found, checks the identity in exact arithmetic and writes `Packing/Cube6Prism.lean`. Two of the three polynomials contain the squares of `y` and of `1/2 - y` for the same coordinate y, so they do not vanish together, and the three strict inequalities give a contradiction. The other quadrant assignments follow by the reflections `x -> 1 - x` and `y -> 1 - y` (`Packing/Cube6Cases.lean`).

`Packing/Cube6Cases.lean`, `Packing/Cube6Core.lean` and `Packing/Cube6.lean` are case analyses written by `gen/gen_n6_cases.py`, `gen/gen_n6_core.py` and `gen/gen_n6_glue.py`. All four generated files are in the repository. The four files take about half an hour to compile on one core.

### Uniqueness

`Packing/Cube6Unique.lean` runs the argument with distances at least 3 sqrt(2)/4. Steps 1, 2 and 4 hold as before, because the bounds they use have room to spare. Step 3 becomes: three of the points in a slab `[0,1] x [0,1] x [0,1/4]` do not all have third coordinate below 1/4 (`prism_three_ge`). Its certificate has one more term on the right, the product of the three numbers 1/4 - z (`gen/n6_prism_ge_search.py`, `gen/gen_n6_prism_ge.py`, `Packing/Cube6PrismGe.lean`). In step 5 the three points nearest the origin then lie in `[0, 3/4]^3` with every pair at squared distance exactly 9/8, which makes them (3/4, 0, 0), (0, 3/4, 0) and (0, 0, 3/4) (`six_normal_ge`). The same statement for the arrangement reflected in all three coordinates gives the other three points.

The generators of the case analyses write the files for this argument when called with `--ge`: `Packing/Cube6CasesGe.lean`, `Packing/Cube6CoreGe.lean` and `Packing/Cube6Opposite.lean`. These three files and `Cube6PrismGe.lean` take about half an hour to compile on one core.

## Ten points in a cube

Schaer (1994) proved that ten points of the unit cube can be pairwise at distance 3/4 and no more. `Packing/Cube10.lean` checks his arrangement pair by pair: the four corners of the bottom face, the same four corners at height 3/4, and the points (1/2, 1/2, 1/4) and (1/2, 1/2, 1).

The upper bound is proved another way.

1. Each point gets a key from 0 to 15: the halves of [0, 1] that hold its first two coordinates and the quarter that holds its third (`key` in `Packing/Cube10Main.lean`). The box of a key measures 1/2 by 1/2 by 1/4, so two points with the same key are at squared distance at most 1/4 + 1/4 + 1/16 = 9/16. Ten points pairwise further apart than 3/4 therefore have ten different keys.
2. Sorted, the ten keys are one of the 8,008 sublists of length 10 of 0, ..., 15. The eight reflections of the cube in its three coordinates permute these patterns (`keyT`, `reflPt`), and 1,050 patterns represent them all.
3. For each of the 1,050 patterns, the data hold a proof that no ten points, one in each box of the pattern, are pairwise further apart than 3/4. A proof is a tree. An inner node splits the interval of one coordinate of one point. A leaf names two points that are at squared distance at most 9/16 wherever they lie in their intervals, or gives nonnegative weights for which the weighted sum of the squared distances minus 9/16 is at most 0. The checker bounds that sum at the vertices of the boxes, which is enough because a sum of squares is convex in each coordinate.

`Packing/Cube10Check.lean` holds the checker `check`, the proof that a state it accepts contains no ten points pairwise further apart than 3/4 (`check_sound`), and a second version `checkK` written with `Nat` operations and recursors, which the kernel evaluates quickly and which is proved equal to the first. Coordinates are integers out of 1,024. `exists_dist_le_ten_of_data` in `Packing/Cube10Main.lean` derives the bound from any list of accepted proofs that covers the 1,050 patterns.

The data are generated. `gen/gen_n10_run.py` searches for the trees with `gen/gen_n10.py`: a branch and bound that splits intervals, with the weights of a leaf taken from a linear program in floating point and then rounded to integers. The search is not trusted; the kernel checks every tree. `gen/gen_n10_emit.py` writes the trees to `Packing/Cube10D00.lean` to `Cube10D41.lean`, the table that sends each of the 8,008 patterns to its representative to `Packing/Cube10SymBase.lean`, `Cube10S00.lean` to `Cube10S08.lean` and `Cube10Sym.lean`, and the assembly to `Packing/Cube10Data.lean`. All 54 generated files are in the repository (4.9 MB), so the build does not run the generators, which need `numpy` and `scipy`. Another run of the search can return different trees; the files here are those of the run in the run record.

```
cd gen
uv run --script gen_n10_run.py 0 1 <dir> 64 256
uv run --script gen_n10_emit.py <dir> ../Packing 15000
```

The first command takes a part number and a number of parts, so that several processes can share the work.

## Cell certificates

### Grassmannian

1. `gen/gen_cert.py` reads `grassmannian/<m>-<n>-<N>.txt` with the parser of `check/exact.py`, scales the decimals to integers, and runs exact integer Gram-Schmidt on the n vectors of each subspace. It writes the orthogonal vectors as data. A vector is stored as a list of natural numbers `e` and an offset `off`, which stand for the integer vector `e - off`, with the sum of `e` and the squared norm of the vector.
2. `Packing.Cert.check` verifies the data. There are N frames of n vectors of length m. Every stored sum and squared norm is correct, and every squared norm is positive. The vectors of each frame are pairwise orthogonal. For every two frames F and G, the sum over u in F and v in G of `floor(10^40 (u.v)^2 / (|u|^2 |v|^2)) + 1` is at most `(n 10^10 - k) 10^30`.
3. `hasPacking_of_check` proves that these checks give the bound. The orthogonal projector onto the span of an orthogonal frame is the sum of `w w^T / |w|^2` over its vectors, so `tr(P_F P_G)` is the sum of `(u.v)^2 / (|u|^2 |v|^2)`, and the squared chordal distance is n minus that trace.
4. `gen/gen_links.py` writes a second file per cell with the vectors of the data file and, for every frame vector w, integers g >= 1 and coefficients with `g w` equal to that integer combination of the file's vectors of the same subspace. `Packing.Cert.checkLink` verifies these equations entry by entry. A frame of n orthogonal nonzero vectors inside the span of n vectors spans the same subspace, which is `spansPack_of_link`.
5. Each generated file states that its checker returns `true` and closes the statement with `decide +kernel`. The Lean kernel evaluates the checker on the data. The compiler is not trusted.

Steps 2 and 4 check everything the proofs need, so an error in a generator cannot produce a false theorem. It can make a check fail.

The bound of a cell is k/10^10, where k is the largest integer the checker accepts. The generator stops if k differs from the cell's `our_value` rounded down to 10 decimals, or if k does not exceed the table value. For all 1,658 cells k equals `our_value` rounded down to 10 decimals. `cells_manifest.tsv` lists k and the table value for each cell.

The `+ 1` in step 2 makes the bound strict. A pair of lines at squared chordal distance exactly 1/2 is accepted at k = 4999999999 and rejected at k = 5000000000.

### Point tables

`gen/gen_points.py` writes the points of a data file, multiplied by one power of ten S, as integer vectors in the same stored form. The checkers of `Packing/Cert/CheckPoints.lean` compare integers, with a threshold t that stands for t/10^12.

- Spherical codes, `checkSph`: every vector is nonzero, and for every two vectors u and v either `u.v <= 0` or `(u.v)^2 10^24 <= t^2 |u|^2 |v|^2`.
- Game of Sloanes, `checkCoh`: a vector has a real and an imaginary part. Every vector is nonzero, and for every two vectors `|<u, v>|^2 10^24 <= t^2 |u|^2 |v|^2`, with the real and the imaginary part of the Hermitian product computed from four real dot products.
- Packomania hsp4, hsp5 and hsp6, `checkBall`: every centre c satisfies `|c|^2 10^24 <= (10^12 - t)^2 S^2`, and every two centres satisfy `|c - c'|^2 10^24 >= 4 t^2 S^2`.
- Packomania scu, `checkCube`: every coordinate x of a centre satisfies `2 10^12 |x| <= (10^12 - 2t) S`, and every two centres satisfy the same distance condition. The file uses the cube `[-1/2, 1/2]^3`. The theorem moves it to `[0, 1]^3`.

The kernel's memory grows with the number of pairs it evaluates in one theorem: cell 25-971 of the version 1.4 spherical codes passed 48 GB. For spherical codes with N^2 d above 12.5 million (89 of the version 1.4 cells, 5 of the 29 here), the generator cuts the points into 4 or 5 consecutive blocks and states one kernel-evaluated theorem for the count and the vectors, one for the pairs inside each block, and one for the pairs between every two blocks. `Packing/Cert/CheckBlocks.lean` joins these into the same statement `checkSph d N t c = true` that the other cells prove in one evaluation, so the theorems of `AllPoints.lean` are the same for all cells. Checked in blocks, that cell took 14 minutes and 5 GB.

For the spherical codes and the Game of Sloanes t is the smallest integer the checker accepts. For the Packomania tables it is the largest. The generator stops unless t agrees with the cell's `our_value` to within one unit of 10^-12 and beats the table value. `points_manifest.tsv` lists t and the table value for each cell.

### Tests

`Packing/Cert/Test.lean`, `TestPoints.lean`, `TestLink.lean` and `TestBlocks.lean` hold 103 cases with known answers. Each checker is run at the last threshold it must accept and at the next one, which it must reject, and on data that break one condition at a time: the count, the length of a vector, a stored sum, a stored norm, a zero vector, orthogonality, the container, the separation, a coefficient. For the block check the failing pair is placed at the end of either block, between two blocks that each pass, and between the first and the third of three blocks.

## Build

Requirements: `elan`, and 11 GB of disk for the toolchain, Mathlib and its cache.

```
cd lean
lake exe cache get
lake build
lake env lean Audit.lean
```

`lake build` compiles the bounds, the cube theorems for up to nine points, the checkers, their soundness proofs and the tests. Every line that `Audit.lean` prints must end with `[propext, Classical.choice, Quot.sound]`.

To check the theorem for ten points:

```
lake build PackingCube10
lake env lean AuditCube10.lean
```

This starts one Lean process per core for the 42 data files, which take about four hours of process time in all.

To check the cells:

```
python3 gen/gen_cert.py
python3 gen/gen_links.py
python3 gen/gen_points.py
lake build PackingCells
```

The generators write 4,147 files under `Packing/Cert/Cells/` (ignored by git), the three generated lists and three manifests. `lake build PackingCells` starts one Lean process per core. To check one cell, run `python3 gen/gen_cert.py 6-2-15` and then `lake build Packing.Cert.Cells.C_6_2_15`.

## Statements checked with `lake comparator`

`Audit.lean` shows which axioms the theorems use, but the theorems and the definitions they mention sit in the same library as the proofs. `Challenge.lean` and `Challenge/` separate them. They import only Mathlib, copy every definition that a statement mentions from `Packing/` (the structures, the checkers, the points such as `five` and `nine`), and state the 46 theorems of `Audit.lean` and one cell of each of the seven tables (`Challenge/Cert/Cells.lean`) with `sorry` in place of the proof. They are about 900 lines. To check what is proved, read these files next to the tables under "Theorems" and "Definitions behind the statements". The proofs do not need to be read.

`lake comparator` (Lean 4.35) builds `Solution.lean`, which imports the library and the seven sampled cell files, exports it, and accepts only if every theorem named in `comparator.json` has the same statement as in the challenge, every constant of the challenge (definitions included) is identical in the library, the proofs use only `propext`, `Classical.choice` and `Quot.sound`, and Lean's kernel replays them. `--paranoid` also requires the external kernels shipped with Lean to accept.

```
python3 -I gen/gen_cert.py 3-1-43
python3 -I gen/gen_points.py game-of-sloanes:3-24 spherical-codes:6-138 packomania-hsp4:30 packomania-hsp5:39 packomania-hsp6:16 packomania-scu:135
lake comparator --paranoid
```

The sandbox needs `bwrap` on Linux. `gen/gen_challenge.py` writes `Challenge/` from the library and `gen/gen_challenge.py --check` fails if the files differ from a fresh run. `Challenge/Cert/Cells.lean` is written by hand. One definition is copied without being named by a statement: Lean gave `Packing.Cube5.T` an auxiliary proof that the value of `five` reuses, so `cd` and `T` precede `five` in `Challenge/Cube5.lean`.

When to run it again: before a pull request that changes a file under `Packing/` other than the generated cell files, or that adds a theorem to `Audit.lean`, run `python3 -I gen/gen_challenge.py` (and commit what it writes), then `lake comparator --paranoid`, or `gate/comparator_run.py` on a Kaggle CPU kernel. A pull request that only adds or replaces cells does not need it, because the cell statements use the definitions the challenge already fixes.

## Run record

The runs below were made from 2026-11-12 to 2026-11-14 with Lean 4.35.0 and Mathlib v4.35.0, on the version 1.4 data. They cover all 2,817 cells of that version, of which the 917 of this tree are a part; the result files here keep the lines of those 917. A tree hash is the sha256 that `gate/gate.py` computes over the paths and contents of `lean/`.

**One machine** (Xeon E5-1650 v2, 12 threads, 64 GB).

| Step | Result | Process time |
|---|---|---|
| Grassmannian cells (`cells_results.tsv`) | 1,486 of 1,486 | 5.0 h |
| Links to the data files (`links_results.tsv`) | 1,486 of 1,486 | 2.1 h |
| Point tables (`points_results.tsv`) | 1,331 of 1,331 | 43.7 h |
| `All.lean`, `AllLinks.lean`, `AllPoints.lean` | compile, no output | |
| `lake build` and `Audit.lean` | 45 lines, each ending with the three standard axioms | |

That is every one of the 2,817 cells of version 1.4. Unsplit, the 13 largest spherical codes did not finish on this machine, and one of them passed 48 GB. They pass in blocks.

**From a clean clone** (Kaggle CPU kernels, 4 cores, about 30 GB). `gate/gate.py` clones this repository at a pinned commit (version 1.4 for these runs), lays `lean/` over it, installs the toolchain, builds the library, runs the audit, writes the cell files of its share from the data files, checks them, and compiles the theorems of `All.lean`, `AllLinks.lean` and `AllPoints.lean` for its share. `gate/summaries/` holds the summary of each kernel.

| Kernels | Tree hash | Modules | Passed |
|---|---|---|---|
| `s0` to `s4`, a fifth of the cells each, 4 processes | `c4880c63` | 4,303 | 3,919 |
| `r0a` to `r4b`, the 384 others one at a time | `c4880c63` | 384 | 295 |
| `giants`, the 89 others, checked in blocks | `319479da` | 89 | 89 |
| `final`, build and audit and one cell | `d28fb11d` | 1 | 1 |

The 384 modules that did not pass in the first row were stopped by the memory limit with four processes running. The 89 that did not pass alone are the spherical codes that are now checked in blocks. So each of the 4,303 cell modules passed from a clean clone: 4,214 at the first tree and 89 at the second. Build and audit were clean in every kernel. The third tree is the second plus the proofs for eight points.

The files that the cells import, the three lists and the three manifests are the same in the three trees. `gen/gen_points.py` differs between the first tree and the others. Run again on the first machine, the later version wrote all 1,331 point files byte for byte as they were checked, and left `AllPoints.lean` and the manifest unchanged.

**Replay.** `leanchecker` replayed 96 modules in the kernel on the first machine, each in its own process: the 37 modules of the library, the three lists, and 56 cell modules (`gate/replay_modules.txt`). The cells are seven per table, the smallest, the largest and five spaced evenly between them by cost, with both modules of each Grassmannian cell. All 96 ended with exit code 0 and no output (`gate/replay_results.tsv`). The root module `Packing`, which holds only imports, was also on the list: the checker ran out of memory on it, at 40 GB when run alone.

**After the merge with version 1.5** (2026-11-15, first machine). The generators were run on the version 1.5 data for the 917 cells of `cells_scope.txt`. All 1,003 files came out byte for byte as they were checked, so their results above stand. The three lists for the 917 cells compile with no output, `lake build` succeeds, and `Audit.lean` prints 45 lines that each end with the three standard axioms. From a clean clone at the version 1.5 commit (kernel `v15`, tree hash `c871590d`), the library builds, the audit prints the same 45 lines, and one cell of each of the seven tables passes with its theorems from the three lists.

**Nine points, uniqueness** (2026-11-15). On the first machine `Packing/Cube9Unique.lean` builds and `isUniqueMaxMinDist_nine` depends on the three standard axioms; the full library was not rebuilt there. From a clean clone at the merge commit `abc1eed` with this tree laid over it (kernel `cube9`), `lake build` succeeds, `Audit.lean` prints 46 lines that each end with the three standard axioms, and one cell of each of the seven tables passes. An earlier run of that kernel copied the tree into a subdirectory and so built the tree of the merge commit; `gate/gate.py` now copies over an existing `lean/`.

**Grassmannian cells of version 1.5** (2026-11-15, first machine, three Lean processes). The generators were run for all 6,829 cells of version 1.5. The 1,572 Grassmannian cells whose file is new or changed pass: 1,572 of 1,572 cell modules in 5.4 h of process time and 1,572 of 1,572 links to the data files in 2.4 h, the slowest module in 141 s. Their lines are appended to `cells_results.tsv` and `links_results.tsv`; the lines of the 86 earlier cells carry the module names of the version 1.4 run, without the `C_` prefix. `All.lean` and `AllLinks.lean`, now with 1,658 theorems each, compile with no output. The library is unchanged from the merge commit, so `lake build` and the audit were not run again. From a clean clone at the merge commit `abc1eed` with this tree laid over it (kernel `v15g`), the library builds, the audit prints 45 lines, and all 1,572 of these cells pass again with their links, together with one cell of each table: 3,152 of 3,152 modules, and the two lists for them compile with no output.

**Comparator** (2026-11-16, Kaggle CPU kernel `packing-lean-comparator`, 4 cores, summary in `gate/summaries/comparator.json`). `gate/comparator_run.py` clones this repository at `beb5b9f`, lays this tree over it, writes the seven sampled cell files, builds `Challenge` and `Solution` and runs `lake comparator` on the 53 theorems of `comparator.json`. Kaggle containers do not allow the namespaces `bwrap` needs, so each run was repeated with `--inadvisably-no-sandbox` and the container was the only isolation. `lake comparator` accepted (Lean's kernel, 287 s). `lake comparator --paranoid` accepted: Lean's paranoid and default kernels, lean4lean, nanoda, con-leche and con-ron (con-leche and con-ron report 35,817 declarations, `--verified`), 702 s. As a control, the same run with `d ≤ dist` changed to `d < dist` in the challenge's `IsMaxMinDist` was rejected: `Const does not match between challenge and target 'Packing.Cube.IsMaxMinDist'`. A comparison of the 195 constants of the challenge with the library's (level parameters, reducibility hints, safety and hashes of type and value) found no difference.

**Ten points** (2026-11-19, a 12-core x86-64 machine, clean clone at `238da19` with the three hand-written files and the three generators laid over it). The search ran in six processes with Python 3.12.14, numpy 2.5.5 and scipy 1.18.1 and returned a tree for each of the 1,050 patterns in 15 minutes. `gen_n10_emit.py` wrote the 54 files that are in this tree. Built three modules at a time, the 42 data files, the nine table files, `Cube10Data` and `Cube10` passed in 87 minutes of wall time, the slowest three data files in 572 s. `isMaxMinDist_ten` depends on the three standard axioms. An earlier emission of the same trees into 1,051 smaller files also passed.

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
- J. Schaer, "The densest packing of five spheres in a cube", Canad. Math. Bull. 9 (1966), 271-274.
- J. Schaer, "The densest packing of six spheres in a cube", Canad. Math. Bull. 9 (1966), 275-280.
- J. Schaer, "The densest packing of ten congruent spheres in a cube", in Intuitive Geometry (Szeged, 1991), Colloq. Math. Soc. János Bolyai 63, North-Holland (1994), 403-424.

The Lean files and the generators were written with AI coding assistants. The Lean kernel checks every proof.
