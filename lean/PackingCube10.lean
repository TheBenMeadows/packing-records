import Packing.Cube10

/-!
The best arrangement of ten points in a cube: `Packing.Cube.isMaxMinDist_ten`.

`Packing.lean` does not import any of the `Packing/Cube10*.lean` files, so `lake build` does not
compile them. This module does: the checker and its soundness proof (`Cube10Check`), the
reduction to data (`Cube10Main`), and the generated data (`Cube10D*`, `Cube10S*`, `Cube10Sym*`,
`Cube10Data`), which need up to 16 GB of memory for one file (see `gate/build_cube10.sh`).
-/
