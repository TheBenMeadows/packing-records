/-
Rankin's simplex and orthoplex bounds for points on a sphere in a real inner product space.

Reference: R. A. Rankin, "The closest packing of spherical caps in n dimensions",
Proc. Glasgow Math. Assoc. 2 (1955), 139-144.
-/
import Mathlib

open Finset Module
open scoped InnerProductSpace

namespace Packing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι]

/-- The sum of all pairwise inner products of a finite family is the squared norm of its sum. -/
theorem sum_sum_inner_eq (x : ι → E) :
    ∑ i, ∑ j, ⟪x i, x j⟫_ℝ = ‖∑ i, x i‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  simp_rw [inner_sum]

/-- For a family on the sphere of squared radius `ρ`, the sum of all squared pairwise distances
is `2ρN² - 2‖∑ x‖²`. -/
theorem sum_sum_norm_sub_sq (x : ι → E) (ρ : ℝ) (hx : ∀ i, ‖x i‖ ^ 2 = ρ) :
    ∑ i, ∑ j, ‖x i - x j‖ ^ 2
      = 2 * ρ * (Fintype.card ι : ℝ) ^ 2 - 2 * ‖∑ i, x i‖ ^ 2 := by
  have h : ∀ i j, ‖x i - x j‖ ^ 2 = 2 * ρ - 2 * ⟪x i, x j⟫_ℝ := by
    intro i j
    rw [norm_sub_sq_real, hx i, hx j]; ring
  simp_rw [h, sum_sub_distrib, ← mul_sum, sum_sum_inner_eq]
  simp only [sum_const, card_univ, nsmul_eq_mul]
  ring

/-- **Rankin's simplex bound.** Among `N ≥ 2` points on the sphere of squared radius `ρ` in a
real inner product space (of any dimension), some two distinct points are at squared distance at
most `2ρ · N/(N-1)`. -/
theorem rankin_simplex (x : ι → E) (ρ : ℝ) (hx : ∀ i, ‖x i‖ ^ 2 = ρ)
    (hN : 2 ≤ Fintype.card ι) :
    ∃ i j, i ≠ j ∧
      ‖x i - x j‖ ^ 2 ≤ 2 * ρ * ((Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) - 1)) := by
  classical
  set N : ℝ := (Fintype.card ι : ℝ) with hNdef
  have hN2 : (2 : ℝ) ≤ N := by rw [hNdef]; exact_mod_cast hN
  have hne : N - 1 ≠ 0 := by linarith
  let s : Finset (ι × ι) := (univ : Finset ι).offDiag
  have hcardNat : s.card = Fintype.card ι * Fintype.card ι - Fintype.card ι := by
    simp [s, Finset.offDiag_card]
  have hle : Fintype.card ι ≤ Fintype.card ι * Fintype.card ι := Nat.le_mul_self _
  have hs : s.Nonempty := by
    rw [← Finset.card_pos, hcardNat]
    have : Fintype.card ι < Fintype.card ι * Fintype.card ι := by nlinarith
    omega
  have hcard : (s.card : ℝ) = N * (N - 1) := by
    rw [hcardNat, Nat.cast_sub hle]; push_cast; ring
  have h1 : ∑ p ∈ s, ‖x p.1 - x p.2‖ ^ 2 = ∑ i, ∑ j, ‖x i - x j‖ ^ 2 := by
    rw [← Fintype.sum_prod_type' (fun i j => ‖x i - x j‖ ^ 2)]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro p _ hp
    have hpp : p.1 = p.2 := by simpa [s, Finset.mem_offDiag] using hp
    simp [hpp]
  have hsum : ∑ p ∈ s, ‖x p.1 - x p.2‖ ^ 2 ≤ ∑ _p ∈ s, 2 * ρ * (N / (N - 1)) := by
    rw [h1, sum_sum_norm_sub_sq x ρ hx, Finset.sum_const, nsmul_eq_mul, hcard]
    have e : N * (N - 1) * (2 * ρ * (N / (N - 1))) = 2 * ρ * N ^ 2 := by
      field_simp
    rw [e]
    nlinarith [sq_nonneg ‖∑ i, x i‖]
  obtain ⟨p, hp, hpl⟩ := Finset.exists_le_of_sum_le hs hsum
  exact ⟨p.1, p.2, (Finset.mem_offDiag.mp hp).2.2, hpl⟩

/-- A family of vectors with pairwise negative inner products in a space of dimension `d` has at
most `d + 1` members. -/
theorem card_le_finrank_add_one_of_inner_neg [FiniteDimensional ℝ E] (x : ι → E)
    (h : ∀ i j, i ≠ j → ⟪x i, x j⟫_ℝ < 0) :
    Fintype.card ι ≤ finrank ℝ E + 1 := by
  classical
  by_contra hcard
  push Not at hcard
  have hpos : 0 < Fintype.card ι := by omega
  obtain ⟨k⟩ := Fintype.card_pos_iff.mp hpos
  -- the members other than `x k` are too many to be linearly independent
  have hdep : ¬ LinearIndependent ℝ (fun i : {i // i ≠ k} => x i.1) := by
    intro hli
    have h1 := hli.fintype_card_le_finrank
    have h2 : Fintype.card {i // i ≠ k} = Fintype.card ι - 1 := by
      simp
    omega
  obtain ⟨g, hg, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.mp hdep
  -- replacing the coefficients by their absolute values still gives the zero vector
  have key : ∀ i j : {i // i ≠ k},
      ⟪|g i| • x i.1, |g j| • x j.1⟫_ℝ ≤ ⟪g i • x i.1, g j • x j.1⟫_ℝ := by
    intro i j
    simp only [real_inner_smul_left, real_inner_smul_right]
    by_cases hij : i = j
    · subst hij
      have e : |g i| * (|g i| * ⟪x i.1, x i.1⟫_ℝ) = g i * (g i * ⟪x i.1, x i.1⟫_ℝ) := by
        rw [← mul_assoc, ← mul_assoc, abs_mul_abs_self]
      exact e.le
    · have hneg := h i.1 j.1 (fun e => hij (Subtype.ext e))
      have h2 : g i * g j ≤ |g i| * |g j| := by
        rw [← abs_mul]; exact le_abs_self _
      nlinarith
  have hz : ∑ i, |g i| • x i.1 = 0 := by
    have hle : ‖∑ i, |g i| • x i.1‖ ^ 2 ≤ ‖∑ i, g i • x i.1‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
      simp only [sum_inner, inner_sum]
      exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => key j i
    have hzero : ‖∑ i, |g i| • x i.1‖ ^ 2 ≤ 0 := by
      have h0 : ‖∑ i, g i • x i.1‖ ^ 2 = 0 := by rw [hg]; simp
      exact hle.trans h0.le
    exact norm_eq_zero.mp
      ((pow_eq_zero_iff two_ne_zero).mp (le_antisymm hzero (sq_nonneg _)))
  -- pairing with `x k` forces every coefficient to vanish
  have hk : ∑ i : {i // i ≠ k}, |g i| * ⟪x i.1, x k⟫_ℝ = 0 := by
    have := congrArg (fun v => ⟪v, x k⟫_ℝ) hz
    simpa [sum_inner, real_inner_smul_left] using this
  have hterm : ∀ i ∈ (univ : Finset {i // i ≠ k}), |g i| * ⟪x i.1, x k⟫_ℝ ≤ 0 := by
    intro i _
    exact mul_nonpos_of_nonneg_of_nonpos (abs_nonneg _) (h i.1 k i.2).le
  have hall := (Finset.sum_eq_zero_iff_of_nonpos hterm).mp hk
  have h0 := hall i₀ (Finset.mem_univ _)
  have hlt := h i₀.1 k i₀.2
  have habs : 0 < |g i₀| := abs_pos.mpr hi₀
  nlinarith

/-- More than `d + 1` vectors in a space of dimension `d` include two distinct ones with
nonnegative inner product. -/
theorem exists_inner_nonneg_of_finrank_lt [FiniteDimensional ℝ E] (x : ι → E)
    (hN : finrank ℝ E + 1 < Fintype.card ι) :
    ∃ i j, i ≠ j ∧ 0 ≤ ⟪x i, x j⟫_ℝ := by
  by_contra hcon
  push Not at hcon
  have := card_le_finrank_add_one_of_inner_neg x hcon
  omega

/-- **Rankin's orthoplex bound.** Among more than `d + 1` points on the sphere of squared radius
`ρ` in a real inner product space of dimension `d`, some two distinct points are at squared
distance at most `2ρ`. -/
theorem rankin_orthoplex [FiniteDimensional ℝ E] (x : ι → E) (ρ : ℝ)
    (hx : ∀ i, ‖x i‖ ^ 2 = ρ) (hN : finrank ℝ E + 1 < Fintype.card ι) :
    ∃ i j, i ≠ j ∧ ‖x i - x j‖ ^ 2 ≤ 2 * ρ := by
  obtain ⟨i, j, hij, hnn⟩ := exists_inner_nonneg_of_finrank_lt x hN
  refine ⟨i, j, hij, ?_⟩
  rw [norm_sub_sq_real, hx i, hx j]; linarith

/-- The orthoplex bound for points that lie in a finite-dimensional subspace `W` of a possibly
larger space: the dimension that counts is that of `W`. -/
theorem rankin_orthoplex_of_mem (W : Submodule ℝ E) [FiniteDimensional ℝ W] (x : ι → E)
    (ρ : ℝ) (hW : ∀ i, x i ∈ W) (hx : ∀ i, ‖x i‖ ^ 2 = ρ)
    (hN : finrank ℝ W + 1 < Fintype.card ι) :
    ∃ i j, i ≠ j ∧ ‖x i - x j‖ ^ 2 ≤ 2 * ρ := by
  obtain ⟨i, j, hij, h⟩ :=
    rankin_orthoplex (fun i => (⟨x i, hW i⟩ : W)) ρ (fun i => by simpa using hx i) hN
  exact ⟨i, j, hij, by simpa using h⟩

/-- Rankin's simplex bound for `N ≥ 2` unit vectors in `ℝ^d`. -/
theorem rankin_simplex_unit {d N : ℕ} (hN : 2 ≤ N) (x : Fin N → EuclideanSpace ℝ (Fin d))
    (hx : ∀ i, ‖x i‖ = 1) :
    ∃ i j, i ≠ j ∧ ‖x i - x j‖ ^ 2 ≤ 2 * (N : ℝ) / ((N : ℝ) - 1) := by
  obtain ⟨i, j, hij, h⟩ :=
    rankin_simplex x 1 (fun i => by rw [hx i]; norm_num) (by simpa using hN)
  refine ⟨i, j, hij, ?_⟩
  simp only [Fintype.card_fin] at h
  calc ‖x i - x j‖ ^ 2 ≤ 2 * 1 * ((N : ℝ) / ((N : ℝ) - 1)) := h
    _ = 2 * (N : ℝ) / ((N : ℝ) - 1) := by ring

/-- Rankin's orthoplex bound for `N > d + 1` unit vectors in `ℝ^d`. -/
theorem rankin_orthoplex_unit {d N : ℕ} (hN : d + 1 < N) (x : Fin N → EuclideanSpace ℝ (Fin d))
    (hx : ∀ i, ‖x i‖ = 1) :
    ∃ i j, i ≠ j ∧ ‖x i - x j‖ ^ 2 ≤ 2 := by
  obtain ⟨i, j, hij, h⟩ :=
    rankin_orthoplex x 1 (fun i => by rw [hx i]; norm_num) (by simpa using hN)
  exact ⟨i, j, hij, by simpa using h⟩

end Packing
