import Challenge.Subspace
open Finset Module Matrix
open scoped InnerProductSpace
namespace Packing
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι]
theorem card_le_two_mul_finrank_of_mem (W : Submodule ℝ E) [FiniteDimensional ℝ W] (x : ι → E)
    (hW : ∀ i, x i ∈ W) (h0 : ∀ i, x i ≠ 0) (h : ∀ i j, i ≠ j → ⟪x i, x j⟫_ℝ ≤ 0) :
    Fintype.card ι ≤ 2 * finrank ℝ W := by
  sorry

theorem rankin_orthoplex_strict [FiniteDimensional ℝ E] (x : ι → E) (ρ : ℝ) (hρ : 0 < ρ)
    (hx : ∀ i, ‖x i‖ ^ 2 = ρ) (hN : 2 * finrank ℝ E < Fintype.card ι) :
    ∃ i j, i ≠ j ∧ ‖x i - x j‖ ^ 2 < 2 * ρ := by
  sorry

theorem chs_orthoplex_strict {m : ℕ} (n : ℕ) (hn : 0 < n) (hnm : n < m)
    (P : ι → Matrix (Fin m) (Fin m) ℝ) (hP : ∀ i, IsProjector (P i) n)
    (hN : 2 * ((m + 1).choose 2 - 1) < Fintype.card ι) :
    ∃ i j, i ≠ j ∧ chordalSq (P i) (P j) < (n : ℝ) * (m - n) / m := by
  sorry

theorem chs_orthoplex_strict_subspace {m : ℕ} (n : ℕ) (hn : 0 < n) (hnm : n < m)
    (U : ι → Submodule ℝ (EuclideanSpace ℝ (Fin m))) (hU : ∀ i, finrank ℝ (U i) = n)
    (hN : 2 * ((m + 1).choose 2 - 1) < Fintype.card ι) :
    ∃ i j, i ≠ j ∧ subspaceChordalSq (U i) (U j) < (n : ℝ) * (m - n) / m := by
  sorry

end Packing
