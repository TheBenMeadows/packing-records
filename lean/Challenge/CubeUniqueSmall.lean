import Challenge.CubeUnique
set_option linter.unusedVariables false
namespace Packing.Cube
noncomputable def four : Fin 4 → Pt := fun i => corner (evenCorner i)

theorem isUniqueMaxMinDist_four : IsUniqueMaxMinDist 4 (Real.sqrt 2) four := by
  sorry

noncomputable def three : Fin 3 → Pt := fun i => corner (evenCorner (Fin.castSucc i))

theorem isUniqueMaxMinDist_three : IsUniqueMaxMinDist 3 (Real.sqrt 2) three := by
  sorry

end Packing.Cube
