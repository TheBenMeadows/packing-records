import Mathlib
namespace Packing.Cube
abbrev Pt := EuclideanSpace ℝ (Fin 3)

/-- `x` lies in the unit cube `[0,1]^3`. -/
def InCube (x : Pt) : Prop := ∀ c, 0 ≤ x c ∧ x c ≤ 1

/-- `d` is the largest minimum distance among `N` points of the unit cube: some `N` points are
pairwise at distance at least `d`, and any `N` points include two at distance at most `d`. -/
def IsMaxMinDist (N : ℕ) (d : ℝ) : Prop :=
  (∃ p : Fin N → Pt, (∀ i, InCube (p i)) ∧ ∀ i j, i ≠ j → d ≤ dist (p i) (p j)) ∧
    ∀ p : Fin N → Pt, (∀ i, InCube (p i)) → ∃ i j, i ≠ j ∧ dist (p i) (p j) ≤ d

/-! ### Distances -/

noncomputable def corner (v : Fin 3 → Bool) : Pt :=
  WithLp.toLp 2 fun c => if v c then 1 else 0

noncomputable def centre : Pt := WithLp.toLp 2 fun _ => 1 / 2

theorem isMaxMinDist_two : IsMaxMinDist 2 (Real.sqrt 3) := by
  sorry

def evenCorner : Fin 4 → Fin 3 → Bool :=
  ![![false, false, false], ![true, true, false], ![true, false, true], ![false, true, true]]

theorem isMaxMinDist_four : IsMaxMinDist 4 (Real.sqrt 2) := by
  sorry

theorem isMaxMinDist_three : IsMaxMinDist 3 (Real.sqrt 2) := by
  sorry

theorem isMaxMinDist_nine : IsMaxMinDist 9 (Real.sqrt 3 / 2) := by
  sorry

theorem isMaxMinDist_eight : IsMaxMinDist 8 1 := by
  sorry

end Packing.Cube
