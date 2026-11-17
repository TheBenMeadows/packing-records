import Challenge.CubeBalls
import Challenge.Cube5Cert
set_option linter.unusedVariables false
namespace Packing.Cube5
open Packing.Cube
-- Not named by any statement: the value of `five` reuses an auxiliary proof that
-- the elaborator generated for `T`, so `cd` and `T` must precede `five` here.
noncomputable def cd (v : Fin 3 → Bool) (x : Pt) (c : Fin 3) : ℝ := if v c then 1 - x c else x c

noncomputable def T (v : Fin 3 → Bool) (σ : Equiv.Perm (Fin 3)) (x : Pt) : Pt :=
  WithLp.toLp 2 fun c => cd v x (σ c)

noncomputable def five : Fin 5 → Pt := fun i =>
  WithLp.toLp 2 (![![0, 0, 0], ![1, 1, 1], ![0, 1 / 2, 1], ![1 / 2, 1, 0], ![1, 0, 1 / 2]] i)

theorem isMaxMinDist_five : IsMaxMinDist 5 (Real.sqrt 5 / 2) := by
  sorry

theorem isMaxRadius_five : IsMaxRadius 5 ((5 - 2 * Real.sqrt 5) / 2) := by
  sorry

end Packing.Cube5
