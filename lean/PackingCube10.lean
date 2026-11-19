import Packing.Cube10

/-!
The best arrangement of ten points in a cube: `Packing.Cube.isMaxMinDist_ten`.

`Packing/Cube10Check.lean` and `Packing/Cube10Main.lean` hold the checker, its soundness proof
and the reduction to data, and they build with the library. This module adds the generated data
(`Packing/Cube10D*.lean`, `Packing/Cube10S*.lean`, `Packing/Cube10Sym*.lean`,
`Packing/Cube10Data.lean`), which the kernel checks in about five CPU hours.
-/
