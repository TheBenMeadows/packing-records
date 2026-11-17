import Challenge.Rankin
open Finset Module Matrix
open scoped InnerProductSpace
namespace Packing
variable {m : ℕ}
structure IsProjector (P : Matrix (Fin m) (Fin m) ℝ) (n : ℕ) : Prop where
  symm : Pᵀ = P
  idem : P * P = P
  trace_eq : P.trace = n

/-- The squared chordal distance between two subspaces given by their projectors:
half the squared Frobenius norm of `P - Q`. -/
noncomputable def chordalSq (P Q : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  ((P - Q)ᵀ * (P - Q)).trace / 2

/-- For projectors of the same rank `n`, the squared chordal distance is `n - tr(PQ)`. -/
theorem chordalSq_eq {P Q : Matrix (Fin m) (Fin m) ℝ} {n : ℕ}
    (hP : IsProjector P n) (hQ : IsProjector Q n) :
    chordalSq P Q = n - (P * Q).trace := by
  sorry

variable {ι : Type*} [Fintype ι]
theorem chs_simplex (hm : 0 < m) (n : ℕ) (P : ι → Matrix (Fin m) (Fin m) ℝ)
    (hP : ∀ i, IsProjector (P i) n) (hN : 2 ≤ Fintype.card ι) :
    ∃ i j, i ≠ j ∧ chordalSq (P i) (P j)
      ≤ (n : ℝ) * (m - n) / m * ((Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) - 1)) := by
  sorry

theorem chs_orthoplex (hm : 0 < m) (n : ℕ) (P : ι → Matrix (Fin m) (Fin m) ℝ)
    (hP : ∀ i, IsProjector (P i) n) (hN : (m + 1).choose 2 < Fintype.card ι) :
    ∃ i j, i ≠ j ∧ chordalSq (P i) (P j) ≤ (n : ℝ) * (m - n) / m := by
  sorry

end Packing
