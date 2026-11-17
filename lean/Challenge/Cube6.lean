import Challenge.CubeBalls
import Challenge.Cube6Core
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
namespace Packing.Cube6
open Packing.Cube
noncomputable def six : Fin 6 → Pt := fun i =>
  WithLp.toLp 2 (![![3 / 4, 0, 0], ![0, 3 / 4, 0], ![0, 0, 3 / 4], ![1 / 4, 1, 1], ![1, 1 / 4, 1],
    ![1, 1, 1 / 4]] i)

theorem isMaxMinDist_six : IsMaxMinDist 6 (3 * Real.sqrt 2 / 4) := by
  sorry

theorem isMaxRadius_six : IsMaxRadius 6 ((9 - 6 * Real.sqrt 2) / 2) := by
  sorry

end Packing.Cube6
