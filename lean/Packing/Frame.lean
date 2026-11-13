/-
The orthogonal projector onto the span of pairwise orthogonal nonzero vectors, and the chordal
distance between two such spans in terms of inner products of the vectors.
-/
import Packing.Subspace

open Module Matrix
open scoped InnerProductSpace

namespace Packing

variable {m : ℕ}

/-- A matrix that maps into `U` and whose defect is orthogonal to `U` is the projection matrix
of `U`. -/
theorem projMatrix_eq_of {U : Submodule ℝ (EuclideanSpace ℝ (Fin m))}
    {M : Matrix (Fin m) (Fin m) ℝ}
    (h1 : ∀ x, Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ) M x ∈ U)
    (h2 : ∀ x, x - Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ) M x ∈ Uᗮ) :
    projMatrix U = M := by
  have h : U.starProjection = Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ) M :=
    ContinuousLinearMap.ext fun x =>
      Submodule.eq_starProjection_of_mem_orthogonal (h1 x) (h2 x)
  unfold projMatrix
  rw [h]
  simp

theorem inner_eq_dotProduct (x y : EuclideanSpace ℝ (Fin m)) :
    ⟪x, y⟫_ℝ = WithLp.ofLp x ⬝ᵥ WithLp.ofLp y := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct_comm]

/-- The matrix `∑ a, (1/|w a|²) · (w a)(w a)ᵀ`. -/
noncomputable def frameMatrix {p : ℕ} (w : Fin p → EuclideanSpace ℝ (Fin m)) :
    Matrix (Fin m) (Fin m) ℝ :=
  ∑ a, (1 / ⟪w a, w a⟫_ℝ) • vecMulVec (WithLp.ofLp (w a)) (WithLp.ofLp (w a))

theorem toEuclideanCLM_frameMatrix {p : ℕ} (w : Fin p → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin m)) :
    Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ) (frameMatrix w) x
      = ∑ a, (⟪w a, x⟫_ℝ / ⟪w a, w a⟫_ℝ) • w a := by
  have key : WithLp.ofLp (Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ) (frameMatrix w) x)
      = WithLp.ofLp (∑ a, (⟪w a, x⟫_ℝ / ⟪w a, w a⟫_ℝ) • w a) := by
    rw [Matrix.ofLp_toEuclideanCLM]
    unfold frameMatrix
    rw [Matrix.sum_mulVec]
    funext i
    simp only [Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, inner_eq_dotProduct,
      WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  exact WithLp.ofLp_injective 2 key

variable {p q : ℕ}

/-- Pairwise orthogonal nonzero vectors span a subspace whose dimension is their number. -/
theorem finrank_span_frame (w : Fin p → EuclideanSpace ℝ (Fin m))
    (horth : Pairwise fun a b => ⟪w a, w b⟫_ℝ = 0) (hpos : ∀ a, 0 < ⟪w a, w a⟫_ℝ) :
    finrank ℝ (Submodule.span ℝ (Set.range w)) = p := by
  have hne : ∀ a, w a ≠ 0 := fun a h => by
    have := hpos a
    simp [h] at this
  have hli := linearIndependent_of_ne_zero_of_inner_eq_zero hne horth
  simpa using finrank_span_eq_card hli

/-- The projection matrix of the span of pairwise orthogonal nonzero vectors. -/
theorem projMatrix_span_frame (w : Fin p → EuclideanSpace ℝ (Fin m))
    (horth : Pairwise fun a b => ⟪w a, w b⟫_ℝ = 0) (hpos : ∀ a, 0 < ⟪w a, w a⟫_ℝ) :
    projMatrix (Submodule.span ℝ (Set.range w)) = frameMatrix w := by
  apply projMatrix_eq_of
  · intro x
    rw [toEuclideanCLM_frameMatrix]
    exact Submodule.sum_mem _ fun a _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · intro x
    rw [toEuclideanCLM_frameMatrix, Submodule.mem_orthogonal]
    intro u hu
    have hle : Submodule.span ℝ (Set.range w)
        ≤ (ℝ ∙ (x - ∑ a, (⟪w a, x⟫_ℝ / ⟪w a, w a⟫_ℝ) • w a))ᗮ := by
      rw [Submodule.span_le]
      rintro _ ⟨b, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left, inner_sub_right,
        inner_sum]
      simp only [real_inner_smul_right]
      rw [Finset.sum_eq_single b]
      · have := (hpos b).ne'
        field_simp
        ring
      · intro a _ hab
        rw [horth (Ne.symm hab), mul_zero]
      · simp
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp (hle hu)

theorem trace_smul_vecMulVec_mul (c d : ℝ) (u v : Fin m → ℝ) :
    ((c • vecMulVec u u) * (d • vecMulVec v v)).trace = c * d * (u ⬝ᵥ v) ^ 2 := by
  rw [smul_mul_assoc, mul_smul_comm, Matrix.vecMulVec_mul_vecMulVec, Matrix.trace_smul,
    Matrix.trace_smul, Matrix.trace_vecMulVec, dotProduct_smul]
  simp only [smul_eq_mul]
  ring

theorem trace_frameMatrix_mul (w : Fin p → EuclideanSpace ℝ (Fin m))
    (w' : Fin q → EuclideanSpace ℝ (Fin m)) :
    (frameMatrix w * frameMatrix w').trace
      = ∑ a, ∑ b, ⟪w a, w' b⟫_ℝ ^ 2 / (⟪w a, w a⟫_ℝ * ⟪w' b, w' b⟫_ℝ) := by
  unfold frameMatrix
  rw [Finset.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [trace_smul_vecMulVec_mul]
  simp only [inner_eq_dotProduct]
  ring

/-- The squared chordal distance between projectors of ranks `p` and `q`. -/
theorem chordalSq_eq' {P Q : Matrix (Fin m) (Fin m) ℝ} (hP : IsProjector P p)
    (hQ : IsProjector Q q) : chordalSq P Q = ((p : ℝ) + q) / 2 - (P * Q).trace := by
  unfold chordalSq
  rw [transpose_sub, hP.symm, hQ.symm]
  have h : (P - Q) * (P - Q) = P * P - P * Q - Q * P + Q * Q := by noncomm_ring
  rw [h, hP.idem, hQ.idem]
  simp only [trace_add, trace_sub]
  rw [trace_mul_comm Q P, hP.trace_eq, hQ.trace_eq]; ring

/-- The squared chordal distance between the spans of two frames of pairwise orthogonal nonzero
vectors, in terms of the inner products between the frames. -/
theorem subspaceChordalSq_span_frames (w : Fin p → EuclideanSpace ℝ (Fin m))
    (w' : Fin q → EuclideanSpace ℝ (Fin m))
    (horth : Pairwise fun a b => ⟪w a, w b⟫_ℝ = 0) (hpos : ∀ a, 0 < ⟪w a, w a⟫_ℝ)
    (horth' : Pairwise fun a b => ⟪w' a, w' b⟫_ℝ = 0) (hpos' : ∀ a, 0 < ⟪w' a, w' a⟫_ℝ) :
    subspaceChordalSq (Submodule.span ℝ (Set.range w)) (Submodule.span ℝ (Set.range w'))
      = ((p : ℝ) + q) / 2
        - ∑ a, ∑ b, ⟪w a, w' b⟫_ℝ ^ 2 / (⟪w a, w a⟫_ℝ * ⟪w' b, w' b⟫_ℝ) := by
  have hP := isProjector_projMatrix (Submodule.span ℝ (Set.range w))
  have hQ := isProjector_projMatrix (Submodule.span ℝ (Set.range w'))
  rw [finrank_span_frame w horth hpos] at hP
  rw [finrank_span_frame w' horth' hpos'] at hQ
  unfold subspaceChordalSq
  rw [chordalSq_eq' hP hQ, projMatrix_span_frame w horth hpos,
    projMatrix_span_frame w' horth' hpos', trace_frameMatrix_mul]

end Packing
