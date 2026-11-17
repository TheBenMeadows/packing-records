import Challenge.Grassmannian
open Module Matrix
namespace Packing
variable {m : ℕ}
noncomputable def projMatrix (U : Submodule ℝ (EuclideanSpace ℝ (Fin m))) :
    Matrix (Fin m) (Fin m) ℝ :=
  (Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ)).symm U.starProjection

theorem isProjector_projMatrix (U : Submodule ℝ (EuclideanSpace ℝ (Fin m))) :
    IsProjector (projMatrix U) (finrank ℝ U) := by
  sorry

noncomputable def subspaceChordalSq (U V : Submodule ℝ (EuclideanSpace ℝ (Fin m))) : ℝ :=
  chordalSq (projMatrix U) (projMatrix V)

variable {ι : Type*} [Fintype ι]
theorem chs_simplex_subspace (hm : 0 < m) (n : ℕ)
    (U : ι → Submodule ℝ (EuclideanSpace ℝ (Fin m))) (hU : ∀ i, finrank ℝ (U i) = n)
    (hN : 2 ≤ Fintype.card ι) :
    ∃ i j, i ≠ j ∧ subspaceChordalSq (U i) (U j)
      ≤ (n : ℝ) * (m - n) / m * ((Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) - 1)) := by
  sorry

theorem chs_orthoplex_subspace (hm : 0 < m) (n : ℕ)
    (U : ι → Submodule ℝ (EuclideanSpace ℝ (Fin m))) (hU : ∀ i, finrank ℝ (U i) = n)
    (hN : (m + 1).choose 2 < Fintype.card ι) :
    ∃ i j, i ≠ j ∧ subspaceChordalSq (U i) (U j) ≤ (n : ℝ) * (m - n) / m := by
  sorry

end Packing
