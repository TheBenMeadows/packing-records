/-
Soundness of `Packing.Cert.checkCoh`: if it returns `true`, the vectors of the data, normalized,
are `N` unit vectors of `ℂ^d` whose pairwise Hermitian products have absolute value at most
`t / 10^12`.
-/
import Packing.Cert.SoundPoints

open Module
open scoped InnerProductSpace

namespace Packing

/-- There are `N` unit vectors in `ℂ^d` whose pairwise Hermitian products have absolute value
at most `t`: `N` lines of `ℂ^d` with coherence at most `t`. -/
def HasCoherence (d N : ℕ) (t : ℝ) : Prop :=
  ∃ x : Fin N → EuclideanSpace ℂ (Fin d),
    (∀ i, ‖x i‖ = 1) ∧ ∀ i j, i ≠ j → ‖⟪x i, x j⟫_ℂ‖ ≤ t

namespace Cert

theorem absSub_cast_sq (a b : ℕ) : ((absSub a b : ℕ) : ℝ) ^ 2 = ((a : ℝ) - b) ^ 2 := by
  have e : absSub a b = (a - b) + (b - a) := rfl
  rw [e]
  rcases le_total a b with h | h
  · rw [Nat.sub_eq_zero_of_le h, zero_add, Nat.cast_sub h]
    ring
  · rw [Nat.sub_eq_zero_of_le h, add_zero, Nat.cast_sub h]

theorem cnsq_eq (u : CVec) : cnsq u = u.re.nsq + u.im.nsq := rfl

theorem okCVec_iff {m : ℕ} {u : CVec} :
    okCVec m u = true ↔ OkVec m u.re ∧ OkVec m u.im ∧ 1 ≤ cnsq u := by
  unfold okCVec
  simp only [andB_eq_true, okVec0_iff, Nat.ble_eq]

theorem cohB_iff {m t2 q2 : ℕ} {u v : CVec} :
    cohB m t2 q2 u v = true ↔
      (absRe m u v * absRe m u v + absIm m u v * absIm m u v) * q2
        ≤ t2 * (cnsq u * cnsq v) := by
  unfold cohB
  simp only [Nat.ble_eq]
  exact Iff.rfl

theorem checkCoh_iff {m N t : ℕ} {c : List CVec} :
    checkCoh m N t c = true ↔ c.length = N ∧ (∀ v ∈ c, okCVec m v = true) ∧
      c.Pairwise fun u v => cohB m (t * t) (10 ^ 24) u v = true := by
  unfold checkCoh
  simp only [andB_eq_true, allB_eq_true, pairwiseB_eq_true, beq_iff, sumMap_one]
  exact Iff.rfl

/-- The vector of `ℂ^m` that `u` stands for. -/
noncomputable def toCVec (m : ℕ) (u : CVec) : EuclideanSpace ℂ (Fin m) :=
  WithLp.toLp 2 fun k => ((toVec m u.re k : ℝ) : ℂ) + ((toVec m u.im k : ℝ) : ℂ) * Complex.I

/-- The Hermitian product in terms of the four real inner products of the parts. -/
theorem inner_toCVec (m : ℕ) (u v : CVec) :
    ⟪toCVec m u, toCVec m v⟫_ℂ
      = ((⟪toVec m u.re, toVec m v.re⟫_ℝ + ⟪toVec m u.im, toVec m v.im⟫_ℝ : ℝ) : ℂ)
        + ((⟪toVec m u.re, toVec m v.im⟫_ℝ - ⟪toVec m u.im, toVec m v.re⟫_ℝ : ℝ) : ℂ)
          * Complex.I := by
  have term : ∀ a b c e : ℝ,
      ((c : ℂ) + (e : ℂ) * Complex.I) * (starRingEnd ℂ) ((a : ℂ) + (b : ℂ) * Complex.I)
        = ((a * c + b * e : ℝ) : ℂ) + ((a * e - b * c : ℝ) : ℂ) * Complex.I := by
    intro a b c e
    apply Complex.ext <;> simp <;> ring
  rw [EuclideanSpace.inner_eq_star_dotProduct, inner_eq_dotProduct, inner_eq_dotProduct,
    inner_eq_dotProduct, inner_eq_dotProduct]
  show ∑ k, (((toVec m v.re k : ℝ) : ℂ) + ((toVec m v.im k : ℝ) : ℂ) * Complex.I)
        * (starRingEnd ℂ) (((toVec m u.re k : ℝ) : ℂ) + ((toVec m u.im k : ℝ) : ℂ) * Complex.I)
      = ((∑ k, toVec m u.re k * toVec m v.re k + ∑ k, toVec m u.im k * toVec m v.im k : ℝ) : ℂ)
        + ((∑ k, toVec m u.re k * toVec m v.im k - ∑ k, toVec m u.im k * toVec m v.re k : ℝ) : ℂ)
          * Complex.I
  simp only [term]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Complex.ofReal_sum, ← Complex.ofReal_sum,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]

theorem norm_sq_inner_toCVec (m : ℕ) (u v : CVec) :
    ‖⟪toCVec m u, toCVec m v⟫_ℂ‖ ^ 2
      = (⟪toVec m u.re, toVec m v.re⟫_ℝ + ⟪toVec m u.im, toVec m v.im⟫_ℝ) ^ 2
        + (⟪toVec m u.re, toVec m v.im⟫_ℝ - ⟪toVec m u.im, toVec m v.re⟫_ℝ) ^ 2 := by
  rw [inner_toCVec, Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

theorem norm_sq_toCVec (m : ℕ) (u : CVec) :
    ‖toCVec m u‖ ^ 2 = ‖toVec m u.re‖ ^ 2 + ‖toVec m u.im‖ ^ 2 := by
  have h := inner_self_eq_norm_sq (𝕜 := ℂ) (toCVec m u)
  rw [inner_toCVec] at h
  simp at h
  have h3 : ∀ x : ℝ, ((x : ℂ) ^ 2).re = x ^ 2 := fun x => by
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  rw [← h, h3, h3]

section Pairs

variable {m : ℕ} {u v : CVec}

theorem norm_sq_toCVec_eq (hu : OkVec m u.re) (hu' : OkVec m u.im) :
    ‖toCVec m u‖ ^ 2 = (cnsq u : ℝ) := by
  rw [norm_sq_toCVec, norm_sq_toVec hu, norm_sq_toVec hu', cnsq_eq]
  push_cast
  ring

theorem norm_inner_le_of_cohB (hu : OkVec m u.re) (hu' : OkVec m u.im) (hv : OkVec m v.re)
    (hv' : OkVec m v.im) {t : ℕ} (h : cohB m (t * t) (10 ^ 24) u v = true) :
    ‖⟪toCVec m u, toCVec m v⟫_ℂ‖ ≤ (t : ℝ) / 10 ^ 12 * (‖toCVec m u‖ * ‖toCVec m v‖) := by
  apply le_of_sq_le_sq' (by positivity)
  have h' := (Nat.cast_le (α := ℝ)).mpr (cohB_iff.mp h)
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat] at h'
  have eR : ((absRe m u v : ℕ) : ℝ) * (absRe m u v : ℕ)
      = (⟪toVec m u.re, toVec m v.re⟫_ℝ + ⟪toVec m u.im, toVec m v.im⟫_ℝ) ^ 2 := by
    have e : absRe m u v = absSub (dotX m u.re v.re + dotX m u.im v.im)
        (dotY u.re v.re + dotY u.im v.im) := rfl
    rw [← sq, e, absSub_cast_sq, inner_toVec' hu hv, inner_toVec' hu' hv']
    push_cast
    ring
  have eI : ((absIm m u v : ℕ) : ℝ) * (absIm m u v : ℕ)
      = (⟪toVec m u.re, toVec m v.im⟫_ℝ - ⟪toVec m u.im, toVec m v.re⟫_ℝ) ^ 2 := by
    have e : absIm m u v = absSub (dotX m u.re v.im + dotY u.im v.re)
        (dotY u.re v.im + dotX m u.im v.re) := rfl
    rw [← sq, e, absSub_cast_sq, inner_toVec' hu hv', inner_toVec' hu' hv]
    push_cast
    ring
  rw [eR, eI, ← sq] at h'
  have e : ((10 : ℝ) ^ 12) ^ 2 = 10 ^ 24 := by norm_num
  rw [norm_sq_inner_toCVec, mul_pow, mul_pow, norm_sq_toCVec_eq hu hu',
    norm_sq_toCVec_eq hv hv', div_pow, e, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  exact h'

end Pairs

/-- `c` holds `N` vectors whose real and imaginary parts have `m` entries each; they are nonzero
and their pairwise normalized Hermitian products have absolute value at most `t`. -/
def CoherenceData (m N : ℕ) (t : ℝ) (c : List CVec) : Prop :=
  c.length = N ∧ (∀ u ∈ c, u.re.e.length = m ∧ u.im.e.length = m) ∧
    (∀ i : Fin c.length, toCVec m (c.get i) ≠ 0) ∧
    ∀ i j : Fin c.length, i ≠ j →
      ‖⟪toCVec m (c.get i), toCVec m (c.get j)⟫_ℂ‖
        ≤ t * (‖toCVec m (c.get i)‖ * ‖toCVec m (c.get j)‖)

theorem coherenceData_of_check {m N t : ℕ} {c : List CVec} (h : checkCoh m N t c = true) :
    CoherenceData m N ((t : ℝ) / 10 ^ 12) c := by
  obtain ⟨hN, hok, hpair⟩ := checkCoh_iff.mp h
  have hok' : ∀ i : Fin c.length,
      OkVec m (c.get i).re ∧ OkVec m (c.get i).im ∧ 1 ≤ cnsq (c.get i) :=
    fun i => okCVec_iff.mp (hok _ (List.get_mem c i))
  have key : ∀ i j : Fin c.length, i < j →
      ‖⟪toCVec m (c.get i), toCVec m (c.get j)⟫_ℂ‖
        ≤ (t : ℝ) / 10 ^ 12 * (‖toCVec m (c.get i)‖ * ‖toCVec m (c.get j)‖) :=
    fun i j hij => norm_inner_le_of_cohB (hok' i).1 (hok' i).2.1 (hok' j).1 (hok' j).2.1
      (List.pairwise_iff_get.mp hpair i j hij)
  refine ⟨hN, fun u hu => ⟨(okCVec_iff.mp (hok u hu)).1.len, (okCVec_iff.mp (hok u hu)).2.1.len⟩,
    fun i hz => ?_, fun i j hij => ?_⟩
  · have h1 := norm_sq_toCVec_eq (hok' i).1 (hok' i).2.1
    rw [hz, norm_zero] at h1
    have h2 : (1 : ℝ) ≤ cnsq (c.get i) := by exact_mod_cast (hok' i).2.2
    have h3 : (0 : ℝ) ^ 2 = 0 := by norm_num
    rw [h3] at h1
    linarith
  · rcases lt_or_gt_of_ne hij with h1 | h1
    · exact key i j h1
    · rw [norm_inner_symm, mul_comm ‖toCVec m (c.get i)‖]
      exact key j i h1

theorem hasCoherence_of_data {m N : ℕ} {t : ℝ} {c : List CVec} (h : CoherenceData m N t c) :
    HasCoherence m N t := by
  obtain ⟨hN, -, h0, hle⟩ := h
  subst hN
  refine ⟨fun i => ((‖toCVec m (c.get i)‖⁻¹ : ℝ) : ℂ) • toCVec m (c.get i),
    fun i => ?_, fun i j hij => ?_⟩
  · rw [norm_smul, Complex.norm_real, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (h0 i))]
  · have hi : ‖toCVec m (c.get i)‖⁻¹ * ‖toCVec m (c.get i)‖ = 1 :=
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (h0 i))
    have hj : ‖toCVec m (c.get j)‖⁻¹ * ‖toCVec m (c.get j)‖ = 1 :=
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (h0 j))
    have hi0 : 0 ≤ ‖toCVec m (c.get i)‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
    have hj0 : 0 ≤ ‖toCVec m (c.get j)‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
    rw [inner_smul_left, inner_smul_right, norm_mul, norm_mul, RCLike.norm_conj,
      Complex.norm_real, Complex.norm_real, norm_inv, norm_inv, norm_norm, norm_norm]
    calc ‖toCVec m (c.get i)‖⁻¹
          * (‖toCVec m (c.get j)‖⁻¹ * ‖⟪toCVec m (c.get i), toCVec m (c.get j)⟫_ℂ‖)
        ≤ ‖toCVec m (c.get i)‖⁻¹ * (‖toCVec m (c.get j)‖⁻¹
            * (t * (‖toCVec m (c.get i)‖ * ‖toCVec m (c.get j)‖))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hle i j hij) hj0) hi0
      _ = t * ((‖toCVec m (c.get i)‖⁻¹ * ‖toCVec m (c.get i)‖)
            * (‖toCVec m (c.get j)‖⁻¹ * ‖toCVec m (c.get j)‖)) := by ring
      _ = t := by rw [hi, hj]; ring

/-- **Soundness of `checkCoh`.** -/
theorem hasCoherence_of_check {m N t : ℕ} {c : List CVec} (h : checkCoh m N t c = true) :
    HasCoherence m N ((t : ℝ) / 10 ^ 12) :=
  hasCoherence_of_data (coherenceData_of_check h)

end Cert

end Packing
