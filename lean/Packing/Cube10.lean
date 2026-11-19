/-
The largest minimum distance among ten points of the unit cube is `3/4`.

Reference: J. Schaer, "The densest packing of ten congruent spheres in a cube", Intuitive
Geometry (Szeged, 1991), Colloq. Math. Soc. János Bolyai 63 (1994), 403-424. The arrangement
below is Schaer's. The upper bound is a computer-checked case analysis, not Schaer's argument:
`Packing.Cube.exists_dist_le_ten_of_data` reduces it to the proofs in `Packing.Cube10Data`,
which the kernel checks with `Packing.Cube10.checkK`.
-/
import Packing.Cube10Data

namespace Packing.Cube

/-- A point of `ℝ^3` from its coordinates. -/
noncomputable def mk3 (a b c : ℝ) : Pt := WithLp.toLp 2 ![a, b, c]

theorem mk3_0 (a b c : ℝ) : mk3 a b c 0 = a := rfl
theorem mk3_1 (a b c : ℝ) : mk3 a b c 1 = b := rfl
theorem mk3_2 (a b c : ℝ) : mk3 a b c 2 = c := rfl

/-- Schaer's ten points: two layers of four corners at heights `0` and `3/4`, and the points
`(1/2, 1/2, 1/4)` and `(1/2, 1/2, 1)`. -/
noncomputable def schaer10 : Fin 10 → Pt :=
  ![mk3 0 0 0, mk3 1 0 0, mk3 0 1 0, mk3 1 1 0, mk3 (1 / 2) (1 / 2) (1 / 4),
    mk3 0 0 (3 / 4), mk3 1 0 (3 / 4), mk3 0 1 (3 / 4), mk3 1 1 (3 / 4), mk3 (1 / 2) (1 / 2) 1]

theorem inCube_schaer10 (i : Fin 10) : InCube (schaer10 i) := by
  intro c
  fin_cases i <;> fin_cases c <;> simp [schaer10, mk3_0, mk3_1, mk3_2] <;> norm_num

theorem sep_schaer10 (i j : Fin 10) (hij : i ≠ j) : 3 / 4 ≤ dist (schaer10 i) (schaer10 j) := by
  apply le_dist
  rw [dist_sq]
  fin_cases i <;> fin_cases j <;> simp [schaer10, mk3_0, mk3_1, mk3_2] at hij ⊢ <;> norm_num

theorem isMaxMinDist_ten : IsMaxMinDist 10 (3 / 4) :=
  ⟨⟨schaer10, inCube_schaer10, sep_schaer10⟩,
    exists_dist_le_ten_of_data reps10 reps10_ok reps10_cover⟩

end Packing.Cube
