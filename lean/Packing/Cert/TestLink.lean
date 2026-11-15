/-
Known-answer tests for `Packing.Cert.checkLink`. The file vectors are `b₁ = (1, 0)` and
`b₂ = (1, 1)`; the frame is `w₁ = (1, 0) = b₁` and `w₂ = (0, 1) = b₂ - b₁`. The other cases
break one condition at a time. Entries are shifted by 10, as in `Test.lean`.
-/
import Packing.Cert.CheckLink

namespace Packing.Cert.Test

def rows : List Vec := [⟨[11, 10], 10, 21, 1⟩, ⟨[11, 11], 10, 22, 2⟩]
def frame : List Vec := [⟨[11, 10], 10, 21, 1⟩, ⟨[10, 11], 10, 21, 1⟩]
def coefs : List Coef := [⟨1, [(1, 0), (0, 0)]⟩, ⟨1, [(0, 1), (1, 0)]⟩]

example : checkLink 2 2 [rows] [frame] [coefs] = true := by decide +kernel
/-- The same equations multiplied by 3. -/
example : checkLink 2 2 [rows] [frame] [[⟨3, [(3, 0), (0, 0)]⟩, ⟨3, [(0, 3), (3, 0)]⟩]] = true := by
  decide +kernel
/-- A wrong coefficient for the second frame vector. -/
example : checkLink 2 2 [rows] [frame] [[⟨1, [(1, 0), (0, 0)]⟩, ⟨1, [(0, 0), (1, 0)]⟩]] = false := by
  decide +kernel
/-- `g = 0` would make every equation with zero coefficients true. -/
example : checkLink 2 2 [rows] [frame] [[⟨0, [(0, 0), (0, 0)]⟩, ⟨0, [(0, 0), (0, 0)]⟩]] = false := by
  decide +kernel
/-- A frame vector without coefficients. -/
example : checkLink 2 2 [rows] [frame] [[⟨1, [(1, 0), (0, 0)]⟩]] = false := by decide +kernel
/-- Fewer file vectors than the dimension. -/
example : checkLink 2 2 [[⟨[11, 10], 10, 21, 1⟩]] [frame] [coefs] = false := by decide +kernel
/-- A file vector with a wrong stored sum. -/
example : checkLink 2 2 [[⟨[11, 10], 10, 20, 1⟩, ⟨[11, 11], 10, 22, 2⟩]] [frame] [coefs] = false := by
  decide +kernel
/-- Lists of different lengths. -/
example : checkLink 2 2 [rows, rows] [frame] [coefs] = false := by decide +kernel
example : checkLink 2 2 [rows] [frame, frame] [coefs] = false := by decide +kernel
example : checkLink 2 2 [rows] [frame] [coefs, coefs] = false := by decide +kernel

/-- In `ℝ^3`, `(0, 0, 1)` is not in the span of `(1, 0, 0)` and `(0, 1, 0)`: the third coordinate
fails for any coefficients. -/
example : checkLink 3 2 [[⟨[11, 10, 10], 10, 31, 1⟩, ⟨[10, 11, 10], 10, 31, 1⟩]]
    [[⟨[11, 10, 10], 10, 31, 1⟩, ⟨[10, 10, 11], 10, 31, 1⟩]]
    [[⟨1, [(1, 0), (0, 0)]⟩, ⟨1, [(0, 0), (1, 0)]⟩]] = false := by
  decide +kernel
/-- With the frame vector `(0, 1, 0)` instead, the link holds. -/
example : checkLink 3 2 [[⟨[11, 10, 10], 10, 31, 1⟩, ⟨[10, 11, 10], 10, 31, 1⟩]]
    [[⟨[11, 10, 10], 10, 31, 1⟩, ⟨[10, 11, 10], 10, 31, 1⟩]]
    [[⟨1, [(1, 0), (0, 0)]⟩, ⟨1, [(0, 0), (1, 0)]⟩]] = true := by
  decide +kernel

end Packing.Cert.Test
