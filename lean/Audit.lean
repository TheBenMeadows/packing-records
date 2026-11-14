/-
Prints the axioms each headline theorem depends on. Run after `lake build`:
  lake env lean Audit.lean
Every line must list only `propext`, `Classical.choice` and `Quot.sound`.
-/
import Packing

#print axioms Packing.rankin_simplex
#print axioms Packing.rankin_orthoplex
#print axioms Packing.rankin_simplex_unit
#print axioms Packing.rankin_orthoplex_unit
#print axioms Packing.chordalSq_eq
#print axioms Packing.chs_simplex
#print axioms Packing.chs_orthoplex
#print axioms Packing.isProjector_projMatrix
#print axioms Packing.chs_simplex_subspace
#print axioms Packing.chs_orthoplex_subspace
#print axioms Packing.subspaceChordalSq_span_frames
#print axioms Packing.Cert.hasPacking_of_check
#print axioms Packing.Cube.isMaxMinDist_two
#print axioms Packing.Cube.isMaxMinDist_three
#print axioms Packing.Cube.isMaxMinDist_four
#print axioms Packing.Cube.isMaxMinDist_eight
#print axioms Packing.Cube.isMaxMinDist_nine
#print axioms Packing.Cube.maxRadius_of_maxMinDist
#print axioms Packing.Cube.isMaxRadius_eight
#print axioms Packing.Cube.isUniqueMaxMinDist_two
#print axioms Packing.Cube5.isMaxMinDist_five
#print axioms Packing.Cube5.isMaxRadius_five
#print axioms Packing.Cube5.isUniqueMaxMinDist_five
#print axioms Packing.Cube5.isUniqueUpToIsometry_five
#print axioms Packing.Cube6.isMaxMinDist_six
#print axioms Packing.Cube6.isMaxRadius_six
#print axioms Packing.card_le_two_mul_finrank_of_mem
#print axioms Packing.rankin_orthoplex_strict
#print axioms Packing.chs_orthoplex_strict
#print axioms Packing.chs_orthoplex_strict_subspace
#print axioms Packing.Cert.spansPack_of_check
#print axioms Packing.Cert.spansPack_of_link
#print axioms Packing.Cert.hasSphericalCode_of_check
#print axioms Packing.Cert.sphericalData_of_check
#print axioms Packing.Cert.hasCoherence_of_check
#print axioms Packing.Cert.coherenceData_of_check
#print axioms Packing.Cert.hasBallPackingInBall_of_check
#print axioms Packing.Cert.ballData_of_check
#print axioms Packing.Cert.hasBallPackingInCube_of_check
#print axioms Packing.Cert.cubeData_of_check
