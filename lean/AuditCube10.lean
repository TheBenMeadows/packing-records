/-
Prints the axioms behind the ten-point theorem. Run after `lake build PackingCube10`:
  lake env lean AuditCube10.lean
The line must list only `propext`, `Classical.choice` and `Quot.sound`.
-/
import PackingCube10

#print axioms Packing.Cube.isMaxMinDist_ten
