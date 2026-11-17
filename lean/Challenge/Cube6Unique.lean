import Challenge.CubeUnique
import Challenge.Cube6Opposite
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
namespace Packing.Cube6
open Packing.Cube
theorem isUniqueMaxMinDist_six : IsUniqueMaxMinDist 6 (3 * Real.sqrt 2 / 4) six := by
  sorry

theorem isUniqueUpToIsometry_six : IsUniqueUpToIsometry 6 (3 * Real.sqrt 2 / 4) six := by
  sorry

end Packing.Cube6
