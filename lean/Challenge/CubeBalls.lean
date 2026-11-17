import Challenge.Cube
namespace Packing.Cube
def IsBallPacking (N : ℕ) (r : ℝ) (c : Fin N → Pt) : Prop :=
  0 ≤ r ∧ (∀ i k, r ≤ c i k ∧ c i k ≤ 1 - r) ∧ ∀ i j, i ≠ j → 2 * r ≤ dist (c i) (c j)

/-- `r` is the largest radius of `N` equal balls packed in the unit cube. -/
def IsMaxRadius (N : ℕ) (r : ℝ) : Prop :=
  (∃ c, IsBallPacking N r c) ∧ ∀ r' c, IsBallPacking N r' c → r' ≤ r

/-- The map `x ↦ a x + b` in each coordinate. -/
noncomputable def affine (a b : ℝ) (x : Pt) : Pt := WithLp.toLp 2 fun k => a * x k + b

theorem maxRadius_of_maxMinDist {N : ℕ} {d : ℝ} (hd : 0 < d) (h : IsMaxMinDist N d) :
    IsMaxRadius N (d / (2 * (1 + d))) := by
  sorry

theorem isMaxRadius_eight : IsMaxRadius 8 (1 / 4) := by
  sorry

end Packing.Cube
