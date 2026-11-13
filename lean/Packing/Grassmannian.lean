/-
The simplex and orthoplex bounds for packings in Grassmannian spaces with the chordal distance.

Reference: J. H. Conway, R. H. Hardin and N. J. A. Sloane, "Packing lines, planes, etc.:
packings in Grassmannian spaces", Experimental Mathematics 5 (1996), 139-159, Section 5.

A point of the Grassmannian of `n`-dimensional subspaces of `ℝ^m` is represented by its
orthogonal projector, an `m × m` real matrix that is symmetric, idempotent and of trace `n`.
-/
import Packing.Rankin

open Finset Module Matrix
open scoped InnerProductSpace

namespace Packing

variable {m : ℕ}

/-- `P` is the orthogonal projector onto an `n`-dimensional subspace of `ℝ^m`: a symmetric
idempotent matrix of trace `n`. -/
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
  unfold chordalSq
  rw [transpose_sub, hP.symm, hQ.symm]
  have h : (P - Q) * (P - Q) = P * P - P * Q - Q * P + Q * Q := by noncomm_ring
  rw [h, hP.idem, hQ.idem]
  simp only [trace_add, trace_sub]
  rw [trace_mul_comm Q P, hP.trace_eq, hQ.trace_eq]; ring

/-- A square matrix read as a vector of `ℝ^(m × m)`. -/
noncomputable def vec : Matrix (Fin m) (Fin m) ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin m × Fin m) where
  toFun A := WithLp.toLp 2 (fun p : Fin m × Fin m => A p.1 p.2)
  map_add' A B := by ext p; simp
  map_smul' c A := by ext p; simp

/-- The Euclidean inner product of two matrices read as vectors is `tr(AᵀB)`. -/
theorem inner_vec (A B : Matrix (Fin m) (Fin m) ℝ) : ⟪vec A, vec B⟫_ℝ = (Aᵀ * B).trace := by
  simp only [vec, LinearMap.coe_mk, AddHom.coe_mk, PiLp.inner_apply, Matrix.trace,
    Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp [mul_comm]

theorem norm_sq_vec_sub (A B : Matrix (Fin m) (Fin m) ℝ) :
    ‖vec A - vec B‖ ^ 2 = 2 * chordalSq A B := by
  rw [← map_sub, ← real_inner_self_eq_norm_sq, inner_vec]
  unfold chordalSq; ring

/-- The symmetric `m × m` matrices. -/
def symSubmodule (m : ℕ) : Submodule ℝ (Matrix (Fin m) (Fin m) ℝ) where
  carrier := {A | Aᵀ = A}
  add_mem' := by
    intro A B hA hB
    simp only [Set.mem_ofPred_eq] at *
    rw [transpose_add, hA, hB]
  zero_mem' := by simp
  smul_mem' := by
    intro c A hA
    simp only [Set.mem_ofPred_eq] at *
    rw [transpose_smul, hA]

/-- The symmetric `m × m` matrices of trace zero. -/
def symTraceless (m : ℕ) : Submodule ℝ (Matrix (Fin m) (Fin m) ℝ) :=
  symSubmodule m ⊓ LinearMap.ker (Matrix.traceLinearMap (Fin m) ℝ ℝ)

/-- Reads a matrix on unordered index pairs: the pair `{i, j}` goes to `A i j + A j i`. -/
def symReadout : Matrix (Fin m) (Fin m) ℝ →ₗ[ℝ] (Sym2 (Fin m) → ℝ) where
  toFun A := Sym2.lift ⟨fun i j => A i j + A j i, fun i j => add_comm _ _⟩
  map_add' A B := by
    ext z
    induction z using Sym2.ind
    simp [add_add_add_comm]
  map_smul' c A := by
    ext z
    induction z using Sym2.ind
    simp [mul_add]

theorem finrank_symSubmodule_le : finrank ℝ (symSubmodule m) ≤ (m + 1).choose 2 := by
  have hinj : Function.Injective ((symReadout (m := m)).domRestrict (symSubmodule m)) := by
    intro A B hAB
    apply Subtype.ext
    ext i j
    have h := congrFun hAB s(i, j)
    simp only [LinearMap.domRestrict_apply, symReadout, LinearMap.coe_mk, AddHom.coe_mk,
      Sym2.lift_mk] at h
    have hA : A.1 j i = A.1 i j := by
      have := congrFun (congrFun A.2 i) j
      simpa [transpose_apply] using this
    have hB : B.1 j i = B.1 i j := by
      have := congrFun (congrFun B.2 i) j
      simpa [transpose_apply] using this
    rw [hA, hB] at h
    linarith
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  simpa [Sym2.card] using h

theorem finrank_symTraceless_add_one_le (hm : 0 < m) :
    finrank ℝ (symTraceless m) + 1 ≤ (m + 1).choose 2 := by
  have hlt : symTraceless m < symSubmodule m := by
    refine IsConcreteLE.lt_iff_le_and_exists.mpr ⟨inf_le_left, 1, ?_, ?_⟩
    · show (1 : Matrix (Fin m) (Fin m) ℝ)ᵀ = 1
      exact transpose_one
    · intro h1
      have h2 : (1 : Matrix (Fin m) (Fin m) ℝ).trace = 0 := by
        simpa using h1.2
      rw [Matrix.trace_one] at h2
      have : (m : ℝ) = 0 := by simpa using h2
      have : m = 0 := by exact_mod_cast this
      omega
  have h1 := Submodule.finrank_lt_finrank_of_lt hlt
  have h2 := finrank_symSubmodule_le (m := m)
  omega

/-- The projector onto an `n`-dimensional subspace of `ℝ^m`, shifted by `(n/m)·1`, lies on the
sphere of squared radius `n(m-n)/m` in the space of symmetric traceless matrices. -/
theorem norm_sq_vec_shift (hm : 0 < m) {P : Matrix (Fin m) (Fin m) ℝ} {n : ℕ}
    (hP : IsProjector P n) :
    ‖vec (P - ((n : ℝ) / m) • (1 : Matrix (Fin m) (Fin m) ℝ))‖ ^ 2 = (n : ℝ) * (m - n) / m := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [← real_inner_self_eq_norm_sq, inner_vec, transpose_sub, transpose_smul, transpose_one,
    hP.symm]
  have h : (P - ((n : ℝ) / m) • (1 : Matrix (Fin m) (Fin m) ℝ))
        * (P - ((n : ℝ) / m) • (1 : Matrix (Fin m) (Fin m) ℝ))
      = P * P - (2 * ((n : ℝ) / m)) • P + (((n : ℝ) / m) ^ 2) • (1 : Matrix (Fin m) (Fin m) ℝ) := by
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_sub,
      smul_smul]
    rw [two_mul, add_smul, sq]
    abel
  rw [h, hP.idem]
  simp only [trace_add, trace_sub, trace_smul, trace_one, hP.trace_eq, Fintype.card_fin,
    smul_eq_mul]
  field_simp
  ring

theorem shift_mem_symTraceless (hm : 0 < m) {P : Matrix (Fin m) (Fin m) ℝ} {n : ℕ}
    (hP : IsProjector P n) :
    P - ((n : ℝ) / m) • (1 : Matrix (Fin m) (Fin m) ℝ) ∈ symTraceless m := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  refine ⟨?_, ?_⟩
  · show (P - ((n : ℝ) / m) • (1 : Matrix (Fin m) (Fin m) ℝ))ᵀ = _
    rw [transpose_sub, transpose_smul, transpose_one, hP.symm]
  · refine LinearMap.mem_ker.mpr ?_
    rw [Matrix.traceLinearMap_apply]
    simp only [trace_sub, trace_smul, trace_one, hP.trace_eq, Fintype.card_fin, smul_eq_mul]
    field_simp
    ring

variable {ι : Type*} [Fintype ι]

/-- **The simplex bound for Grassmannian packings** (Conway, Hardin and Sloane 1996,
Corollary 5.2). Among `N ≥ 2` subspaces of dimension `n` in `ℝ^m`, some two distinct ones are at
squared chordal distance at most `n(m-n)/m · N/(N-1)`. -/
theorem chs_simplex (hm : 0 < m) (n : ℕ) (P : ι → Matrix (Fin m) (Fin m) ℝ)
    (hP : ∀ i, IsProjector (P i) n) (hN : 2 ≤ Fintype.card ι) :
    ∃ i j, i ≠ j ∧ chordalSq (P i) (P j)
      ≤ (n : ℝ) * (m - n) / m * ((Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) - 1)) := by
  obtain ⟨i, j, hij, h⟩ :=
    rankin_simplex (fun i => vec (P i - ((n : ℝ) / m) • (1 : Matrix (Fin m) (Fin m) ℝ)))
      ((n : ℝ) * (m - n) / m) (fun i => norm_sq_vec_shift hm (hP i)) hN
  refine ⟨i, j, hij, ?_⟩
  rw [norm_sq_vec_sub] at h
  have e : chordalSq (P i - ((n : ℝ) / m) • (1 : Matrix (Fin m) (Fin m) ℝ))
      (P j - ((n : ℝ) / m) • (1 : Matrix (Fin m) (Fin m) ℝ)) = chordalSq (P i) (P j) := by
    unfold chordalSq; rw [sub_sub_sub_cancel_right]
  rw [e] at h
  linarith

/-- **The orthoplex bound for Grassmannian packings** (Conway, Hardin and Sloane 1996,
Corollary 5.2). Among `N > m(m+1)/2` subspaces of dimension `n` in `ℝ^m`, some two distinct ones
are at squared chordal distance at most `n(m-n)/m`. -/
theorem chs_orthoplex (hm : 0 < m) (n : ℕ) (P : ι → Matrix (Fin m) (Fin m) ℝ)
    (hP : ∀ i, IsProjector (P i) n) (hN : (m + 1).choose 2 < Fintype.card ι) :
    ∃ i j, i ≠ j ∧ chordalSq (P i) (P j) ≤ (n : ℝ) * (m - n) / m := by
  let W : Submodule ℝ (EuclideanSpace ℝ (Fin m × Fin m)) := (symTraceless m).map vec
  have hW : finrank ℝ W + 1 < Fintype.card ι := by
    have h1 : finrank ℝ W ≤ finrank ℝ (symTraceless m) := Submodule.finrank_map_le _ _
    have h2 := finrank_symTraceless_add_one_le hm
    omega
  obtain ⟨i, j, hij, h⟩ :=
    rankin_orthoplex_of_mem W
      (fun i => vec (P i - ((n : ℝ) / m) • (1 : Matrix (Fin m) (Fin m) ℝ)))
      ((n : ℝ) * (m - n) / m)
      (fun i => Submodule.mem_map_of_mem (shift_mem_symTraceless hm (hP i)))
      (fun i => norm_sq_vec_shift hm (hP i)) hW
  refine ⟨i, j, hij, ?_⟩
  rw [norm_sq_vec_sub] at h
  have e : chordalSq (P i - ((n : ℝ) / m) • (1 : Matrix (Fin m) (Fin m) ℝ))
      (P j - ((n : ℝ) / m) • (1 : Matrix (Fin m) (Fin m) ℝ)) = chordalSq (P i) (P j) := by
    unfold chordalSq; rw [sub_sub_sub_cancel_right]
  rw [e] at h
  linarith

end Packing
