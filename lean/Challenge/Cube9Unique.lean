import Challenge.Cube8Unique
set_option linter.unusedVariables false
namespace Packing.Cube9
open Packing.Cube
noncomputable def idx : Fin 8 ≃ (Fin 3 → Bool) := Fintype.equivOfCardEq (by simp)

/-- The centre and the eight corners of the cube. -/
noncomputable def nine : Fin 9 → Pt := Fin.cases centre fun i => corner (idx i)

theorem isUniqueMaxMinDist_nine : IsUniqueMaxMinDist 9 (Real.sqrt 3 / 2) nine := by
  sorry

end Packing.Cube9
