/-
From points to balls: a largest minimum distance `d` among `N` points of the unit cube gives the
largest radius `d / (2 (1 + d))` of `N` equal balls packed in the unit cube.

A packing is described by its centres: a ball of radius `r` lies in the unit cube when every
coordinate of its centre is in `[r, 1 - r]`, and two balls of radius `r` have disjoint interiors
when their centres are at distance at least `2r`. These two descriptions are taken as the
definition here and are not derived from `Metric.ball`.
-/
import Packing.Cube

namespace Packing.Cube

/-- `c` gives the centres of `N` balls of radius `r` that lie in the unit cube and have pairwise
disjoint interiors. -/
def IsBallPacking (N : ℕ) (r : ℝ) (c : Fin N → Pt) : Prop :=
  0 ≤ r ∧ (∀ i k, r ≤ c i k ∧ c i k ≤ 1 - r) ∧ ∀ i j, i ≠ j → 2 * r ≤ dist (c i) (c j)

/-- `r` is the largest radius of `N` equal balls packed in the unit cube. -/
def IsMaxRadius (N : ℕ) (r : ℝ) : Prop :=
  (∃ c, IsBallPacking N r c) ∧ ∀ r' c, IsBallPacking N r' c → r' ≤ r

/-- The map `x ↦ a x + b` in each coordinate. -/
noncomputable def affine (a b : ℝ) (x : Pt) : Pt := WithLp.toLp 2 fun k => a * x k + b

theorem affine_apply (a b : ℝ) (x : Pt) (k : Fin 3) : affine a b x k = a * x k + b := rfl

theorem dist_sq_affine (a b : ℝ) (x y : Pt) :
    dist (affine a b x) (affine a b y) ^ 2 = a ^ 2 * dist x y ^ 2 := by
  rw [dist_sq, dist_sq]
  simp only [affine_apply]
  ring

theorem sq_le_sq_of_le {a b : ℝ} (ha : 0 ≤ a) (h : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  nlinarith

theorem maxRadius_of_maxMinDist {N : ℕ} {d : ℝ} (hd : 0 < d) (h : IsMaxMinDist N d) :
    IsMaxRadius N (d / (2 * (1 + d))) := by
  obtain ⟨⟨p, hp, hsep⟩, hub⟩ := h
  have hd1 : 0 < 1 + d := by linarith
  have hr0 : 0 < d / (2 * (1 + d)) := by positivity
  have h12 : 1 - 2 * (d / (2 * (1 + d))) = 1 / (1 + d) := by
    field_simp
    ring
  have ha : 0 < 1 - 2 * (d / (2 * (1 + d))) := by
    rw [h12]
    positivity
  refine ⟨⟨fun i => affine (1 - 2 * (d / (2 * (1 + d)))) (d / (2 * (1 + d))) (p i),
    hr0.le, fun i k => ?_, fun i j hij => ?_⟩, fun r' c hc => ?_⟩
  · rw [affine_apply]
    have hpk := hp i k
    constructor
    · nlinarith [mul_nonneg ha.le hpk.1]
    · nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hpk.2)]
  · apply le_dist
    rw [dist_sq_affine]
    have h2 : d ^ 2 ≤ dist (p i) (p j) ^ 2 := sq_le_sq_of_le hd.le (hsep i j hij)
    calc (2 * (d / (2 * (1 + d)))) ^ 2
        = (1 - 2 * (d / (2 * (1 + d)))) ^ 2 * d ^ 2 := by
          rw [h12]
          field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  · by_cases hr' : r' ≤ 0
    · linarith
    push Not at hr'
    obtain ⟨-, hbox, hsep'⟩ := hc
    obtain ⟨i₀, j₀, hij₀, -⟩ := hub p hp
    by_cases hhalf : 1 / 2 ≤ r'
    · -- then every centre is the centre of the cube, and two balls coincide
      exfalso
      have hsame : ∀ k, c i₀ k = c j₀ k := fun k => by
        have a := hbox i₀ k
        have b := hbox j₀ k
        linarith [a.1, a.2, b.1, b.2]
      have hz : dist (c i₀) (c j₀) ^ 2 = 0 := by
        rw [dist_sq]
        simp [hsame]
      have h1 := hsep' i₀ j₀ hij₀
      nlinarith [dist_nonneg (x := c i₀) (y := c j₀)]
    push Not at hhalf
    have ha' : 0 < 1 - 2 * r' := by linarith
    -- rescale the centres to the unit cube and use the bound for points
    obtain ⟨i, j, hij, hle⟩ :=
      hub (fun i => affine (1 / (1 - 2 * r')) (-r' / (1 - 2 * r')) (c i)) (fun i k => by
        rw [affine_apply]
        have hb := hbox i k
        have e : 1 / (1 - 2 * r') * c i k + -r' / (1 - 2 * r') = (c i k - r') / (1 - 2 * r') := by
          ring
        rw [e]
        exact ⟨div_nonneg (by linarith) ha'.le, (div_le_one ha').mpr (by linarith)⟩)
    have h1 := sq_le_sq_of_le dist_nonneg hle
    rw [dist_sq_affine] at h1
    have h3 : (2 * r') ^ 2 ≤ dist (c i) (c j) ^ 2 :=
      sq_le_sq_of_le (by linarith) (hsep' i j hij)
    have hpos : 0 < (1 - 2 * r') ^ 2 := by positivity
    have h4 : dist (c i) (c j) ^ 2 ≤ d ^ 2 * (1 - 2 * r') ^ 2 := by
      have e : dist (c i) (c j) ^ 2
          = (1 - 2 * r') ^ 2 * ((1 / (1 - 2 * r')) ^ 2 * dist (c i) (c j) ^ 2) := by
        field_simp
      rw [e, mul_comm (d ^ 2)]
      exact mul_le_mul_of_nonneg_left h1 hpos.le
    have h5 : 2 * r' ≤ d * (1 - 2 * r') := by
      by_contra hlt
      push Not at hlt
      nlinarith [mul_pos (sub_pos.mpr hlt)
        (add_pos (mul_pos hd ha') (by linarith : (0 : ℝ) < 2 * r'))]
    rw [le_div_iff₀ (by positivity)]
    nlinarith

/-- Eight equal balls in the unit cube have radius at most `1/4`, and `1/4` is attained. -/
theorem isMaxRadius_eight : IsMaxRadius 8 (1 / 4) := by
  have h := maxRadius_of_maxMinDist one_pos isMaxMinDist_eight
  norm_num at h
  exact h

end Packing.Cube
