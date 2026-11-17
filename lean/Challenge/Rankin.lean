import Mathlib
open Finset Module
open scoped InnerProductSpace
namespace Packing
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι]
theorem rankin_simplex (x : ι → E) (ρ : ℝ) (hx : ∀ i, ‖x i‖ ^ 2 = ρ)
    (hN : 2 ≤ Fintype.card ι) :
    ∃ i j, i ≠ j ∧
      ‖x i - x j‖ ^ 2 ≤ 2 * ρ * ((Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) - 1)) := by
  sorry

theorem rankin_orthoplex [FiniteDimensional ℝ E] (x : ι → E) (ρ : ℝ)
    (hx : ∀ i, ‖x i‖ ^ 2 = ρ) (hN : finrank ℝ E + 1 < Fintype.card ι) :
    ∃ i j, i ≠ j ∧ ‖x i - x j‖ ^ 2 ≤ 2 * ρ := by
  sorry

theorem rankin_simplex_unit {d N : ℕ} (hN : 2 ≤ N) (x : Fin N → EuclideanSpace ℝ (Fin d))
    (hx : ∀ i, ‖x i‖ = 1) :
    ∃ i j, i ≠ j ∧ ‖x i - x j‖ ^ 2 ≤ 2 * (N : ℝ) / ((N : ℝ) - 1) := by
  sorry

theorem rankin_orthoplex_unit {d N : ℕ} (hN : d + 1 < N) (x : Fin N → EuclideanSpace ℝ (Fin d))
    (hx : ∀ i, ‖x i‖ = 1) :
    ∃ i j, i ≠ j ∧ ‖x i - x j‖ ^ 2 ≤ 2 := by
  sorry

end Packing
