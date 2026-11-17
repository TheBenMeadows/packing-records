import Challenge.CubeUnique
import Challenge.Cube5UniqueLemmas
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000
namespace Packing.Cube5
open Packing.Cube
theorem isUniqueMaxMinDist_five : IsUniqueMaxMinDist 5 (Real.sqrt 5 / 2) five := by
  sorry

theorem isUniqueUpToIsometry_five : IsUniqueUpToIsometry 5 (Real.sqrt 5 / 2) five := by
  sorry

end Packing.Cube5
