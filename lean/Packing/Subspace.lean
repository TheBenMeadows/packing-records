/-
Subspaces of `ℝ^m` as points of the Grassmannian: the matrix of the orthogonal projection onto a
subspace of dimension `n` is a projector of trace `n`, so the bounds of `Packing.Grassmannian`
hold for families of subspaces.
-/
import Packing.Grassmannian

open Module Matrix

namespace Packing

variable {m : ℕ}

/-- The matrix, in the standard basis, of the orthogonal projection of `ℝ^m` onto `U`. -/
noncomputable def projMatrix (U : Submodule ℝ (EuclideanSpace ℝ (Fin m))) :
    Matrix (Fin m) (Fin m) ℝ :=
  (Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ)).symm U.starProjection

theorem toEuclideanCLM_projMatrix (U : Submodule ℝ (EuclideanSpace ℝ (Fin m))) :
    Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ) (projMatrix U) = U.starProjection := by
  simp [projMatrix]

/-- The projection matrix of a subspace is a projector whose trace is the dimension. -/
theorem isProjector_projMatrix (U : Submodule ℝ (EuclideanSpace ℝ (Fin m))) :
    IsProjector (projMatrix U) (finrank ℝ U) := by
  refine ⟨?_, ?_, ?_⟩
  · have h1 := (Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ)).map_star' (projMatrix U)
    have h2 : Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ) (star (projMatrix U))
        = Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ) (projMatrix U) := by
      refine h1.trans ?_
      show star (Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ) (projMatrix U)) = _
      rw [toEuclideanCLM_projMatrix]
      exact isSelfAdjoint_starProjection U
    have h : star (projMatrix U) = projMatrix U := EquivLike.injective _ h2
    rw [Matrix.star_eq_conjTranspose] at h
    simpa using h
  · unfold projMatrix
    rw [← map_mul]
    congr 1
    exact U.isIdempotentElem_starProjection.eq
  · have h2 : (U.starProjection : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
        = Matrix.toLin (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
            (EuclideanSpace.basisFun (Fin m) ℝ).toBasis (projMatrix U) := by
      rw [← Matrix.toEuclideanLin_eq_toLin_orthonormal,
        ← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, toEuclideanCLM_projMatrix]
    have hproj : LinearMap.IsProj U
        (U.starProjection : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) :=
      ⟨fun x => U.starProjection_apply_mem x,
        fun x hx => U.starProjection_eq_self_iff.mpr hx⟩
    rw [← hproj.trace,
      LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin m) ℝ).toBasis, h2,
      LinearMap.toMatrix_toLin]

/-- The squared chordal distance between two subspaces of `ℝ^m`. -/
noncomputable def subspaceChordalSq (U V : Submodule ℝ (EuclideanSpace ℝ (Fin m))) : ℝ :=
  chordalSq (projMatrix U) (projMatrix V)

variable {ι : Type*} [Fintype ι]

/-- The simplex bound for `N ≥ 2` subspaces of dimension `n` in `ℝ^m`. -/
theorem chs_simplex_subspace (hm : 0 < m) (n : ℕ)
    (U : ι → Submodule ℝ (EuclideanSpace ℝ (Fin m))) (hU : ∀ i, finrank ℝ (U i) = n)
    (hN : 2 ≤ Fintype.card ι) :
    ∃ i j, i ≠ j ∧ subspaceChordalSq (U i) (U j)
      ≤ (n : ℝ) * (m - n) / m * ((Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) - 1)) :=
  chs_simplex hm n (fun i => projMatrix (U i))
    (fun i => hU i ▸ isProjector_projMatrix (U i)) hN

/-- The orthoplex bound for `N > m(m+1)/2` subspaces of dimension `n` in `ℝ^m`. -/
theorem chs_orthoplex_subspace (hm : 0 < m) (n : ℕ)
    (U : ι → Submodule ℝ (EuclideanSpace ℝ (Fin m))) (hU : ∀ i, finrank ℝ (U i) = n)
    (hN : (m + 1).choose 2 < Fintype.card ι) :
    ∃ i j, i ≠ j ∧ subspaceChordalSq (U i) (U j) ≤ (n : ℝ) * (m - n) / m :=
  chs_orthoplex hm n (fun i => projMatrix (U i))
    (fun i => hU i ▸ isProjector_projMatrix (U i)) hN

end Packing
