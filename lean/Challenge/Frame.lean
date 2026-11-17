import Challenge.Subspace
open Module Matrix
open scoped InnerProductSpace
namespace Packing
variable {m : ℕ}
variable {p q : ℕ}
theorem subspaceChordalSq_span_frames (w : Fin p → EuclideanSpace ℝ (Fin m))
    (w' : Fin q → EuclideanSpace ℝ (Fin m))
    (horth : Pairwise fun a b => ⟪w a, w b⟫_ℝ = 0) (hpos : ∀ a, 0 < ⟪w a, w a⟫_ℝ)
    (horth' : Pairwise fun a b => ⟪w' a, w' b⟫_ℝ = 0) (hpos' : ∀ a, 0 < ⟪w' a, w' a⟫_ℝ) :
    subspaceChordalSq (Submodule.span ℝ (Set.range w)) (Submodule.span ℝ (Set.range w'))
      = ((p : ℝ) + q) / 2
        - ∑ a, ∑ b, ⟪w a, w' b⟫_ℝ ^ 2 / (⟪w a, w a⟫_ℝ * ⟪w' b, w' b⟫_ℝ) := by
  sorry

end Packing
