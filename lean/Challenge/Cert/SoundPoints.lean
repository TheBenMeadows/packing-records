import Challenge.Cert.Sound
import Challenge.Cert.CheckPoints
import Challenge.CubeBalls
open Module
open scoped InnerProductSpace
namespace Packing
def HasSphericalCode (d N : ℕ) (t : ℝ) : Prop :=
  ∃ x : Fin N → EuclideanSpace ℝ (Fin d),
    (∀ i, ‖x i‖ = 1) ∧ ∀ i j, i ≠ j → ⟪x i, x j⟫_ℝ ≤ t

/-- There are `N` balls of radius `r ≥ 0` inside the unit ball of `ℝ^d` with pairwise disjoint
interiors, described by their centres: every centre has norm at most `1 - r` and every two
centres are at distance at least `2r`. -/
def HasBallPackingInBall (d N : ℕ) (r : ℝ) : Prop :=
  0 ≤ r ∧ ∃ c : Fin N → EuclideanSpace ℝ (Fin d),
    (∀ i, ‖c i‖ ≤ 1 - r) ∧ ∀ i j, i ≠ j → 2 * r ≤ dist (c i) (c j)

/-- There are `N` balls of radius `r` inside the unit cube with pairwise disjoint interiors,
described by their centres as in `Cube.IsBallPacking`. -/
def HasBallPackingInCube (N : ℕ) (r : ℝ) : Prop :=
  ∃ c, Cube.IsBallPacking N r c

namespace Cert
section Vectors
variable {m : ℕ} {u v : Vec}
end Vectors
def SphericalData (m N : ℕ) (t : ℝ) (c : List Vec) : Prop :=
  c.length = N ∧ (∀ v ∈ c, v.e.length = m) ∧
    (∀ i : Fin c.length, toVec m (c.get i) ≠ 0) ∧
    ∀ i j : Fin c.length, i ≠ j →
      ⟪toVec m (c.get i), toVec m (c.get j)⟫_ℝ
        ≤ t * (‖toVec m (c.get i)‖ * ‖toVec m (c.get j)‖)

theorem sphericalData_of_check {m N t : ℕ} {c : List Vec} (h : checkSph m N t c = true) :
    SphericalData m N ((t : ℝ) / 10 ^ 12) c := by
  sorry

theorem hasSphericalCode_of_check {m N t : ℕ} {c : List Vec} (h : checkSph m N t c = true) :
    HasSphericalCode m N ((t : ℝ) / 10 ^ 12) := by
  sorry

noncomputable def toPt (m S : ℕ) (v : Vec) : EuclideanSpace ℝ (Fin m) :=
  ((S : ℝ)⁻¹) • toVec m v

/-- `c` holds `N` vectors with `m` entries each and the scale `S` is positive; divided by `S`,
they are centres of balls of radius `r ≥ 0` inside the unit ball with pairwise disjoint
interiors. -/
def BallData (m N S : ℕ) (r : ℝ) (c : List Vec) : Prop :=
  c.length = N ∧ 0 < S ∧ 0 ≤ r ∧ (∀ v ∈ c, v.e.length = m) ∧
    (∀ i : Fin c.length, ‖toPt m S (c.get i)‖ ≤ 1 - r) ∧
    ∀ i j : Fin c.length, i ≠ j → 2 * r ≤ dist (toPt m S (c.get i)) (toPt m S (c.get j))

theorem ballData_of_check {m N t S : ℕ} {c : List Vec} (h : checkBall m N t S c = true) :
    BallData m N S ((t : ℝ) / 10 ^ 12) c := by
  sorry

theorem hasBallPackingInBall_of_check {m N t S : ℕ} {c : List Vec}
    (h : checkBall m N t S c = true) : HasBallPackingInBall m N ((t : ℝ) / 10 ^ 12) := by
  sorry

noncomputable def toCubePt (S : ℕ) (v : Vec) : Cube.Pt :=
  Cube.affine (1 / (S : ℝ)) (1 / 2) (toVec 3 v)

/-- `c` holds `N` vectors with 3 entries each and the scale `S` is positive; divided by `S` and
moved to the unit cube, they are centres of balls of radius `r ≥ 0` inside the unit cube with
pairwise disjoint interiors. -/
def CubeData (N S : ℕ) (r : ℝ) (c : List Vec) : Prop :=
  c.length = N ∧ 0 < S ∧ (∀ v ∈ c, v.e.length = 3) ∧
    Cube.IsBallPacking c.length r (fun i => toCubePt S (c.get i))

theorem cubeData_of_check {N t S : ℕ} {c : List Vec} (h : checkCube N t S c = true) :
    CubeData N S ((t : ℝ) / 10 ^ 12) c := by
  sorry

theorem hasBallPackingInCube_of_check {N t S : ℕ} {c : List Vec}
    (h : checkCube N t S c = true) : HasBallPackingInCube N ((t : ℝ) / 10 ^ 12) := by
  sorry

end Cert
end Packing
