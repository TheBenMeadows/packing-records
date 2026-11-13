/-
Known-answer tests for the checker. The lines through `(1, 0)` and `(1, 1)` in `ℝ^2` are at
squared chordal distance exactly `1/2`. The checker's integer bound is strict, so it accepts
`k = 4999999999` and must reject every `k` from `5000000000` up. It must also reject a wrong
squared norm, a wrong entry sum, a wrong length and a frame that is not orthogonal.
-/
import Packing.Cert.Check

namespace Packing.Cert.Test

/-- `(1, 0)` and `(1, 1)`, entries shifted by 10. -/
def lines : List Frame := [[⟨[11, 10], 10, 21, 1⟩], [⟨[11, 11], 10, 22, 2⟩]]

example : check 2 1 2 4999999999 lines = true := by decide +kernel
example : check 2 1 2 5000000000 lines = false := by decide +kernel
example : check 2 1 2 5000000001 lines = false := by decide +kernel
example : check 2 1 3 4999999999 lines = false := by decide +kernel
example : check 3 1 2 4999999999 lines = false := by decide +kernel
example : check 2 2 2 4999999999 lines = false := by decide +kernel

/-- A wrong squared norm for the second line. -/
example : check 2 1 2 4999999999 [[⟨[11, 10], 10, 21, 1⟩], [⟨[11, 11], 10, 22, 3⟩]] = false := by
  decide +kernel

/-- A wrong entry sum for the first line. -/
example : check 2 1 2 4999999999 [[⟨[11, 10], 10, 20, 1⟩], [⟨[11, 11], 10, 22, 2⟩]] = false := by
  decide +kernel

/-- Signs matter: `(1, 0)` and `(-1, 1)` are also at `1/2`, and `(1, 1)`, `(-1, 1)` at `1`. -/
example : check 2 1 2 4999999999 [[⟨[11, 10], 10, 21, 1⟩], [⟨[9, 11], 10, 20, 2⟩]] = true := by
  decide +kernel
example : check 2 1 2 9999999999 [[⟨[11, 11], 10, 22, 2⟩], [⟨[9, 11], 10, 20, 2⟩]] = true := by
  decide +kernel

/-- The planes spanned by `(1,0,0),(0,1,0)` and by `(1,0,0),(0,0,1)` in `ℝ^3` share a line:
squared chordal distance `2 - 1 = 1`. -/
def planes : List Frame :=
  [[⟨[1, 0, 0], 0, 1, 1⟩, ⟨[0, 1, 0], 0, 1, 1⟩], [⟨[1, 0, 0], 0, 1, 1⟩, ⟨[0, 0, 1], 0, 1, 1⟩]]

example : check 3 2 2 9999999999 planes = true := by decide +kernel
example : check 3 2 2 10000000000 planes = false := by decide +kernel

/-- A frame whose two vectors are not orthogonal is rejected. -/
example : check 3 2 2 1
    [[⟨[1, 0, 0], 0, 1, 1⟩, ⟨[1, 1, 0], 0, 2, 2⟩], [⟨[1, 0, 0], 0, 1, 1⟩, ⟨[0, 0, 1], 0, 1, 1⟩]]
    = false := by
  decide +kernel

end Packing.Cert.Test
