import Challenge.CubeUniqueSmall
import Challenge.Cube8Cert
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
namespace Packing.Cube8
open Packing.Cube
noncomputable def eight : Fin 8 → Pt :=
  fun i => corner ((Fintype.equivOfCardEq (by simp) : Fin 8 ≃ (Fin 3 → Bool)) i)

theorem isUniqueMaxMinDist_eight : IsUniqueMaxMinDist 8 1 eight := by
  sorry

end Packing.Cube8
