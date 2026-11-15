/-
Real-coordinate lemmas for the uniqueness of the best arrangement of five points in the unit
cube (Schaer 1966, pp. 271-274). They turn the certificates of `Cube5EqCert.lean` into
statements about points:

* `claim1_tight`: a point of the region of the first claim at squared distance at least `5/4`
  from `(p1, p2, a)` forces `a = 0` or `a = 1/2`;
* `claim1_half`: at `a = 1/2` the two points are `(0, 1/2, 1/2)` and `(1, 0, 1/2)`, or their
  images under the swap of the first two coordinates;
* `thin_box`: no two further points are far from those two and from each other;
* `same_part_corner`: of two far points with the same least coordinate and coordinate sums at
  least `3/2`, one is `(1, 1, 1)`;
* `hexagon_vertex`: a point with coordinate sum at most `3/2` and squared norm at least `5/4`
  is a permutation of `(0, 1/2, 1)`;
* `hex_triple`: three such points, pairwise far, are `(0, 1/2, 1)`, `(1/2, 1, 0)`, `(1, 0, 1/2)`
  in some order, or the images of these under the swap of the first two coordinates.
-/
import Packing.Cube5
import Packing.Cube5EqCert

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Packing.Cube5

/-! ### The first claim -/

theorem claim1_tight {y1 y2 y3 p1 p2 a : ℝ} (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2)
    (hp1 : 0 ≤ p1) (hp1a : p1 ≤ a) (hp2 : 0 ≤ p2) (hp2a : p2 ≤ a)
    (hy1 : 0 ≤ y1 ∧ y1 ≤ 1) (hy2 : 0 ≤ y2 ∧ y2 ≤ 1) (hy3 : 0 ≤ y3 ∧ y3 ≤ 1)
    (hs : y1 + y2 + y3 ≤ 3 / 2) (ht : y1 + y2 ≤ 3 / 2 - a)
    (hQ2 : y1 ≤ 1 - a ∨ a ≤ y2 ∨ a ≤ y3) (hQ3 : a ≤ y1 ∨ y2 ≤ 1 - a ∨ a ≤ y3)
    (hd : 5 / 4 ≤ (y1 - p1) ^ 2 + (y2 - p2) ^ 2 + (y3 - a) ^ 2) : a * (1 - 2 * a) ≤ 0 := by
  have h0 : 0 ≤ a := ha
  have h1 : 0 ≤ 1 / 2 - a := by linarith
  have h2 : 0 ≤ y1 := hy1.1
  have h3 : 0 ≤ 1 - y1 := by linarith [hy1.2]
  have h4 : 0 ≤ y2 := hy2.1
  have h5 : 0 ≤ 1 - y2 := by linarith [hy2.2]
  have h6 : 0 ≤ y3 := hy3.1
  have h7 : 0 ≤ 1 - y3 := by linarith [hy3.2]
  have h8 : 0 ≤ 3 / 2 - y1 - y2 - y3 := by linarith
  have h9 : 0 ≤ 3 / 2 - y1 - y2 - a := by linarith
  rcases sq_sub_le_endpoint (y := y1) hp1 hp1a with e1 | e1 <;>
    rcases sq_sub_le_endpoint (y := y2) hp2 hp2a with e2 | e2
  · have hd' : 5 / 4 ≤ y1 ^ 2 + y2 ^ 2 + (y3 - a) ^ 2 := by linarith
    rcases hQ2 with hA | hB | hC
    · rcases hQ3 with hD | hE | hC
      · exact c1a_AD_00 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) (by linarith) hd'
      · exact c1a_AE_00 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) (by linarith) hd'
      · exact c1a_AC_00 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) (by linarith) hd'
    · rcases hQ3 with hD | hE | hC
      · exact c1a_BD_00 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) (by linarith) hd'
      · exact c1a_BE_00 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) (by linarith) hd'
      · exact c1a_BC_00 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) (by linarith) hd'
    · exact c1a_C_00 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) hd'
  · have hd' : 5 / 4 ≤ y1 ^ 2 + (y2 - a) ^ 2 + (y3 - a) ^ 2 := by linarith
    rcases hQ2 with hA | hB | hC
    · rcases hQ3 with hD | hE | hC
      · exact c1a_AD_01 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) (by linarith) hd'
      · exact c1a_AE_01 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) (by linarith) hd'
      · exact c1a_AC_01 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) (by linarith) hd'
    · rcases hQ3 with hD | hE | hC
      · exact c1a_BD_01 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) (by linarith) hd'
      · exact c1a_BE_01 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) (by linarith) hd'
      · exact c1a_BC_01 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) (by linarith) hd'
    · exact c1a_C_01 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) hd'
  · have hd' : 5 / 4 ≤ (y1 - a) ^ 2 + y2 ^ 2 + (y3 - a) ^ 2 := by linarith
    rcases hQ2 with hA | hB | hC
    · rcases hQ3 with hD | hE | hC
      · exact c1a_AD_10 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) (by linarith) hd'
      · exact c1a_AE_10 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) (by linarith) hd'
      · exact c1a_AC_10 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) (by linarith) hd'
    · rcases hQ3 with hD | hE | hC
      · exact c1a_BD_10 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) (by linarith) hd'
      · exact c1a_BE_10 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) (by linarith) hd'
      · exact c1a_BC_10 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) (by linarith) hd'
    · exact c1a_C_10 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) hd'
  · have hd' : 5 / 4 ≤ (y1 - a) ^ 2 + (y2 - a) ^ 2 + (y3 - a) ^ 2 := by linarith
    rcases hQ2 with hA | hB | hC
    · rcases hQ3 with hD | hE | hC
      · exact c1a_AD_11 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) (by linarith) hd'
      · exact c1a_AE_11 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) (by linarith) hd'
      · exact c1a_AC_11 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) (by linarith) hd'
    · rcases hQ3 with hD | hE | hC
      · exact c1a_BD_11 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) (by linarith) hd'
      · exact c1a_BE_11 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) (by linarith) hd'
      · exact c1a_BC_11 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) (by linarith) hd'
    · exact c1a_C_11 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) hd'

theorem half_fin_01 {y1 y2 y3 p1 p2 : ℝ} (hp1 : 0 ≤ p1) (hp1a : p1 ≤ 1 / 2) (hp2 : 0 ≤ p2)
    (hp2a : p2 ≤ 1 / 2) (e1 : y1 = 1) (e2 : y2 = 0) (e3 : y3 = 1 / 2)
    (hd : 5 / 4 ≤ (y1 - p1) ^ 2 + (y2 - p2) ^ 2 + (y3 - 1 / 2) ^ 2) :
    y1 = 1 ∧ y2 = 0 ∧ y3 = 1 / 2 ∧ p1 = 0 ∧ p2 = 1 / 2 := by
  rw [e1, e2, e3] at hd
  have t1 := mul_nonneg hp1 (sub_nonneg.mpr hp1a)
  have t3 := mul_nonneg (sub_nonneg.mpr hp2a) hp2
  have hp1z : p1 ≤ 0 := by nlinarith [t1, t3]
  have hp1e : p1 = 0 := le_antisymm hp1z hp1
  rw [hp1e] at hd
  have hp2e : 1 / 2 ≤ p2 := by nlinarith [t3]
  exact ⟨e1, e2, e3, hp1e, le_antisymm hp2a hp2e⟩

theorem half_fin_10 {y1 y2 y3 p1 p2 : ℝ} (hp1 : 0 ≤ p1) (hp1a : p1 ≤ 1 / 2) (hp2 : 0 ≤ p2)
    (hp2a : p2 ≤ 1 / 2) (e1 : y1 = 0) (e2 : y2 = 1) (e3 : y3 = 1 / 2)
    (hd : 5 / 4 ≤ (y1 - p1) ^ 2 + (y2 - p2) ^ 2 + (y3 - 1 / 2) ^ 2) :
    y1 = 0 ∧ y2 = 1 ∧ y3 = 1 / 2 ∧ p1 = 1 / 2 ∧ p2 = 0 := by
  rw [e1, e2, e3] at hd
  have t1 := mul_nonneg hp2 (sub_nonneg.mpr hp2a)
  have t3 := mul_nonneg (sub_nonneg.mpr hp1a) hp1
  have hp2z : p2 ≤ 0 := by nlinarith [t1, t3]
  have hp2e : p2 = 0 := le_antisymm hp2z hp2
  rw [hp2e] at hd
  have hp1e : 1 / 2 ≤ p1 := by nlinarith [t3]
  exact ⟨e1, e2, e3, le_antisymm hp1a hp1e, hp2e⟩

/-- The first claim at `a = 1/2`: the two points are determined. -/
theorem claim1_half {y1 y2 y3 p1 p2 : ℝ}
    (hp1 : 0 ≤ p1) (hp1a : p1 ≤ 1 / 2) (hp2 : 0 ≤ p2) (hp2a : p2 ≤ 1 / 2)
    (hy1 : 0 ≤ y1 ∧ y1 ≤ 1) (hy2 : 0 ≤ y2 ∧ y2 ≤ 1) (hy3 : 0 ≤ y3 ∧ y3 ≤ 1)
    (hs : y1 + y2 + y3 ≤ 3 / 2) (ht : y1 + y2 ≤ 1)
    (hQ2 : y1 ≤ 1 / 2 ∨ 1 / 2 ≤ y2 ∨ 1 / 2 ≤ y3) (hQ3 : 1 / 2 ≤ y1 ∨ y2 ≤ 1 / 2 ∨ 1 / 2 ≤ y3)
    (hd : 5 / 4 ≤ (y1 - p1) ^ 2 + (y2 - p2) ^ 2 + (y3 - 1 / 2) ^ 2) :
    (y1 = 1 ∧ y2 = 0 ∧ y3 = 1 / 2 ∧ p1 = 0 ∧ p2 = 1 / 2) ∨
      (y1 = 0 ∧ y2 = 1 ∧ y3 = 1 / 2 ∧ p1 = 1 / 2 ∧ p2 = 0) := by
  have h0 : 0 ≤ y1 := hy1.1
  have h1 : 0 ≤ 1 - y1 := by linarith [hy1.2]
  have h2 : 0 ≤ y2 := hy2.1
  have h3 : 0 ≤ 1 - y2 := by linarith [hy2.2]
  have h4 : 0 ≤ y3 := hy3.1
  have h5 : 0 ≤ 1 - y3 := by linarith [hy3.2]
  have h6 : 0 ≤ 3 / 2 - y1 - y2 - y3 := by linarith
  have h7 : 0 ≤ 1 - y1 - y2 := by linarith
  rcases sq_sub_le_endpoint (y := y1) hp1 hp1a with e1 | e1 <;>
    rcases sq_sub_le_endpoint (y := y2) hp2 hp2a with e2 | e2
  · have hd' : 5 / 4 ≤ y1 ^ 2 + y2 ^ 2 + (y3 - 1 / 2) ^ 2 := by linarith
    rcases hQ2 with hA | hB | hC
    · rcases hQ3 with hD | hE | hC
      · exact (c1h_AD_00 y1 y2 y3 h0 h1 h2 h3 h4 h5 h6 h7 (by linarith) (by linarith) hd').elim
      · exact (c1h_AE_00 y1 y2 y3 h0 h1 h2 h3 h4 h5 h6 h7 (by linarith) (by linarith) hd').elim
      · exact (c1h_AC_00 y1 y2 y3 h0 h1 h2 h3 h4 h5 h6 h7 (by linarith) (by linarith) hd').elim
    · rcases hQ3 with hD | hE | hC
      · exact (c1h_BD_00 y1 y2 y3 h0 h1 h2 h3 h4 h5 h6 h7 (by linarith) (by linarith) hd').elim
      · exact (c1h_BE_00 y1 y2 y3 h0 h1 h2 h3 h4 h5 h6 h7 (by linarith) (by linarith) hd').elim
      · exact (c1h_BC_00 y1 y2 y3 h0 h1 h2 h3 h4 h5 h6 h7 (by linarith) (by linarith) hd').elim
    · exact (c1h_C_00 y1 y2 y3 h0 h1 h2 h3 h4 h5 h6 h7 (by linarith) hd').elim
  · have hd' : 5 / 4 ≤ y1 ^ 2 + (y2 - 1 / 2) ^ 2 + (y3 - 1 / 2) ^ 2 := by linarith
    rcases hQ2 with hA | hB | hC
    · rcases hQ3 with hD | hE | hC
      · exact (c1h_AD_01 y1 y2 y3 h0 h1 h2 h3 h4 h5 h6 h7 (by linarith) (by linarith) hd').elim
      · exact (c1h_AE_01 y1 y2 y3 h0 h1 h2 h3 h4 h5 h6 h7 (by linarith) (by linarith) hd').elim
      · exact (c1h_AC_01 y1 y2 y3 h0 h1 h2 h3 h4 h5 h6 h7 (by linarith) (by linarith) hd').elim
    · rcases hQ3 with hD | hE | hC
      · exact (c1h_BD_01 y1 y2 y3 h0 h1 h2 h3 h4 h5 h6 h7 (by linarith) (by linarith) hd').elim
      · exact (c1h_BE_01 y1 y2 y3 h0 h1 h2 h3 h4 h5 h6 h7 (by linarith) (by linarith) hd').elim
      · exact (c1h_BC_01 y1 y2 y3 h0 h1 h2 h3 h4 h5 h6 h7 (by linarith) (by linarith) hd').elim
    · obtain ⟨g1, g2, g3, g4⟩ := c1h_C_01 y1 y2 y3 h0 h1 h2 h3 h4 h5 h6 h7 (by linarith) hd'
      exact Or.inl (half_fin_01 hp1 hp1a hp2 hp2a (by linarith) (by linarith) (by linarith) hd)
  · have hd' : 5 / 4 ≤ (y1 - 1 / 2) ^ 2 + y2 ^ 2 + (y3 - 1 / 2) ^ 2 := by linarith
    rcases hQ2 with hA | hB | hC
    · rcases hQ3 with hD | hE | hC
      · exact (c1h_AD_10 y1 y2 y3 h0 h1 h2 h3 h4 h5 h6 h7 (by linarith) (by linarith) hd').elim
      · exact (c1h_AE_10 y1 y2 y3 h0 h1 h2 h3 h4 h5 h6 h7 (by linarith) (by linarith) hd').elim
      · obtain ⟨g1, g2, g3, g4⟩ := c1h_AC_10 y1 y2 y3 h0 h1 h2 h3 h4 h5 h6 h7 (by linarith) (by linarith) hd'
        exact Or.inr (half_fin_10 hp1 hp1a hp2 hp2a (by linarith) (by linarith) (by linarith) hd)
    · rcases hQ3 with hD | hE | hC
      · exact (c1h_BD_10 y1 y2 y3 h0 h1 h2 h3 h4 h5 h6 h7 (by linarith) (by linarith) hd').elim
      · exact (c1h_BE_10 y1 y2 y3 h0 h1 h2 h3 h4 h5 h6 h7 (by linarith) (by linarith) hd').elim
      · obtain ⟨g1, g2, g3, g4⟩ := c1h_BC_10 y1 y2 y3 h0 h1 h2 h3 h4 h5 h6 h7 (by linarith) (by linarith) hd'
        exact Or.inr (half_fin_10 hp1 hp1a hp2 hp2a (by linarith) (by linarith) (by linarith) hd)
    · obtain ⟨g1, g2, g3, g4⟩ := c1h_C_10 y1 y2 y3 h0 h1 h2 h3 h4 h5 h6 h7 (by linarith) hd'
      exact Or.inr (half_fin_10 hp1 hp1a hp2 hp2a (by linarith) (by linarith) (by linarith) hd)
  · have hd' : 5 / 4 ≤ (y1 - 1 / 2) ^ 2 + (y2 - 1 / 2) ^ 2 + (y3 - 1 / 2) ^ 2 := by linarith
    rcases hQ2 with hA | hB | hC
    · rcases hQ3 with hD | hE | hC
      · exact (c1h_AD_11 y1 y2 y3 h0 h1 h2 h3 h4 h5 h6 h7 (by linarith) (by linarith) hd').elim
      · exact (c1h_AE_11 y1 y2 y3 h0 h1 h2 h3 h4 h5 h6 h7 (by linarith) (by linarith) hd').elim
      · exact (c1h_AC_11 y1 y2 y3 h0 h1 h2 h3 h4 h5 h6 h7 (by linarith) (by linarith) hd').elim
    · rcases hQ3 with hD | hE | hC
      · exact (c1h_BD_11 y1 y2 y3 h0 h1 h2 h3 h4 h5 h6 h7 (by linarith) (by linarith) hd').elim
      · exact (c1h_BE_11 y1 y2 y3 h0 h1 h2 h3 h4 h5 h6 h7 (by linarith) (by linarith) hd').elim
      · exact (c1h_BC_11 y1 y2 y3 h0 h1 h2 h3 h4 h5 h6 h7 (by linarith) (by linarith) hd').elim
    · exact (c1h_C_11 y1 y2 y3 h0 h1 h2 h3 h4 h5 h6 h7 (by linarith) hd').elim

/-! ### After the first claim at `a = 1/2` -/

theorem sq_half_le {x : ℝ} (h : 0 ≤ x ∧ x ≤ 1) : (x - 1 / 2) ^ 2 ≤ 1 / 4 := by
  nlinarith [mul_nonneg h.1 (sub_nonneg.mpr h.2)]

/-- A point of the cube far from `(0, 1/2, 1/2)` and from `(1, 0, 1/2)` has first coordinate
at least `4/5` and second at least `9/10`. -/
theorem thin_box_bounds {z1 z2 z3 : ℝ} (hz1 : 0 ≤ z1 ∧ z1 ≤ 1) (hz2 : 0 ≤ z2 ∧ z2 ≤ 1)
    (hz3 : 0 ≤ z3 ∧ z3 ≤ 1)
    (hP : 5 / 4 ≤ z1 ^ 2 + (z2 - 1 / 2) ^ 2 + (z3 - 1 / 2) ^ 2)
    (hY : 5 / 4 ≤ (z1 - 1) ^ 2 + z2 ^ 2 + (z3 - 1 / 2) ^ 2) : 4 / 5 ≤ z1 ∧ 9 / 10 ≤ z2 := by
  have s2 := sq_half_le hz2
  have s3 := sq_half_le hz3
  have b1 : 4 / 5 ≤ z1 := by
    by_contra hn
    push Not at hn
    nlinarith [mul_nonneg hz1.1 (by linarith : (0 : ℝ) ≤ 4 / 5 - z1)]
  refine ⟨b1, ?_⟩
  by_contra hn
  push Not at hn
  have c1 : (z1 - 1) ^ 2 ≤ (1 / 5) ^ 2 := sq_le_sq' (by linarith) (by linarith [hz1.2])
  nlinarith [mul_nonneg hz2.1 (by linarith : (0 : ℝ) ≤ 9 / 10 - z2)]

/-- Two points of the cube far from `(0, 1/2, 1/2)` and from `(1, 0, 1/2)` are close to each
other. -/
theorem thin_box {z1 z2 z3 w1 w2 w3 : ℝ} (hz1 : 0 ≤ z1 ∧ z1 ≤ 1) (hz2 : 0 ≤ z2 ∧ z2 ≤ 1)
    (hz3 : 0 ≤ z3 ∧ z3 ≤ 1) (hw1 : 0 ≤ w1 ∧ w1 ≤ 1) (hw2 : 0 ≤ w2 ∧ w2 ≤ 1)
    (hw3 : 0 ≤ w3 ∧ w3 ≤ 1)
    (hzP : 5 / 4 ≤ z1 ^ 2 + (z2 - 1 / 2) ^ 2 + (z3 - 1 / 2) ^ 2)
    (hzY : 5 / 4 ≤ (z1 - 1) ^ 2 + z2 ^ 2 + (z3 - 1 / 2) ^ 2)
    (hwP : 5 / 4 ≤ w1 ^ 2 + (w2 - 1 / 2) ^ 2 + (w3 - 1 / 2) ^ 2)
    (hwY : 5 / 4 ≤ (w1 - 1) ^ 2 + w2 ^ 2 + (w3 - 1 / 2) ^ 2)
    (hzw : 5 / 4 ≤ (z1 - w1) ^ 2 + (z2 - w2) ^ 2 + (z3 - w3) ^ 2) : False := by
  obtain ⟨a1, a2⟩ := thin_box_bounds hz1 hz2 hz3 hzP hzY
  obtain ⟨b1, b2⟩ := thin_box_bounds hw1 hw2 hw3 hwP hwY
  have c1 : (z1 - w1) ^ 2 ≤ (1 / 5) ^ 2 :=
    sq_le_sq' (by linarith [hz1.2, hw1.2]) (by linarith [hz1.2, hw1.2])
  have c2 : (z2 - w2) ^ 2 ≤ (1 / 10) ^ 2 :=
    sq_le_sq' (by linarith [hz2.2, hw2.2]) (by linarith [hz2.2, hw2.2])
  have c3 : (z3 - w3) ^ 2 ≤ 1 ^ 2 :=
    sq_le_sq' (by linarith [hz3.1, hz3.2, hw3.1, hw3.2]) (by linarith [hz3.1, hz3.2, hw3.1, hw3.2])
  linarith

/-! ### Two points in the same part -/

/-- Of two far points of the cube with least coordinate the first and coordinate sums at least
`3/2`, one is `(1, 1, 1)`. -/
theorem same_part_corner {y1 y2 y3 z1 z2 z3 : ℝ}
    (hy1 : 0 ≤ y1 ∧ y1 ≤ 1) (hy2 : 0 ≤ y2 ∧ y2 ≤ 1) (hy3 : 0 ≤ y3 ∧ y3 ≤ 1)
    (hz1 : 0 ≤ z1 ∧ z1 ≤ 1) (hz2 : 0 ≤ z2 ∧ z2 ≤ 1) (hz3 : 0 ≤ z3 ∧ z3 ≤ 1)
    (y12 : y1 ≤ y2) (y13 : y1 ≤ y3) (z12 : z1 ≤ z2) (z13 : z1 ≤ z3)
    (ys : 3 / 2 ≤ y1 + y2 + y3) (zs : 3 / 2 ≤ z1 + z2 + z3)
    (hd : 5 / 4 ≤ (y1 - z1) ^ 2 + (y2 - z2) ^ 2 + (y3 - z3) ^ 2) :
    (y1 = 1 ∧ y2 = 1 ∧ y3 = 1) ∨ (z1 = 1 ∧ z2 = 1 ∧ z3 = 1) := by
  rcases le_total (z1 + z2 + z3) (y1 + y2 + y3) with hs | hs
  · left
    rcases le_total z2 z3 with hz | hz
    · obtain ⟨g1, g2, g3⟩ := same_part_gap y1 y2 y3 z1 z2 z3 hy1.1 (by linarith [hy1.2]) hy2.1
        (by linarith [hy2.2]) hy3.1 (by linarith [hy3.2]) (by linarith) (by linarith)
        (by linarith) hz1.1 (by linarith [hz1.2]) hz2.1 (by linarith [hz2.2]) hz3.1
        (by linarith [hz3.2]) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) hd
      exact ⟨by linarith, by linarith, by linarith⟩
    · obtain ⟨g1, g2, g3⟩ := same_part_gap y1 y3 y2 z1 z3 z2 hy1.1 (by linarith [hy1.2]) hy3.1
        (by linarith [hy3.2]) hy2.1 (by linarith [hy2.2]) (by linarith) (by linarith)
        (by linarith) hz1.1 (by linarith [hz1.2]) hz3.1 (by linarith [hz3.2]) hz2.1
        (by linarith [hz2.2]) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith only [hd])
      exact ⟨by linarith, by linarith, by linarith⟩
  · right
    rcases le_total y2 y3 with hy | hy
    · obtain ⟨g1, g2, g3⟩ := same_part_gap z1 z2 z3 y1 y2 y3 hz1.1 (by linarith [hz1.2]) hz2.1
        (by linarith [hz2.2]) hz3.1 (by linarith [hz3.2]) (by linarith) (by linarith)
        (by linarith) hy1.1 (by linarith [hy1.2]) hy2.1 (by linarith [hy2.2]) hy3.1
        (by linarith [hy3.2]) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith only [hd])
      exact ⟨by linarith, by linarith, by linarith⟩
    · obtain ⟨g1, g2, g3⟩ := same_part_gap z1 z3 z2 y1 y3 y2 hz1.1 (by linarith [hz1.2]) hz3.1
        (by linarith [hz3.2]) hz2.1 (by linarith [hz2.2]) (by linarith) (by linarith)
        (by linarith) hy1.1 (by linarith [hy1.2]) hy3.1 (by linarith [hy3.2]) hy2.1
        (by linarith [hy2.2]) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith only [hd])
      exact ⟨by linarith, by linarith, by linarith⟩

/-! ### The hexagon -/

/-- One of `(0, 1/2, 1)`, `(1/2, 1, 0)`, `(1, 0, 1/2)`. -/
def IsE (x0 x1 x2 : ℝ) : Prop :=
  (x0 = 0 ∧ x1 = 1 / 2 ∧ x2 = 1) ∨ (x0 = 1 / 2 ∧ x1 = 1 ∧ x2 = 0) ∨ (x0 = 1 ∧ x1 = 0 ∧ x2 = 1 / 2)

/-- A point of the cube with coordinate sum at most `3/2` and squared norm at least `5/4` is a
permutation of `(0, 1/2, 1)`. -/
theorem hexagon_vertex {x0 x1 x2 : ℝ} (h0 : 0 ≤ x0 ∧ x0 ≤ 1) (h1 : 0 ≤ x1 ∧ x1 ≤ 1)
    (h2 : 0 ≤ x2 ∧ x2 ≤ 1) (hs : x0 + x1 + x2 ≤ 3 / 2) (hd : 5 / 4 ≤ x0 ^ 2 + x1 ^ 2 + x2 ^ 2) :
    IsE x0 x1 x2 ∨ IsE x1 x0 x2 := by
  unfold IsE
  obtain ⟨l0, u0⟩ := h0
  obtain ⟨l1, u1⟩ := h1
  obtain ⟨l2, u2⟩ := h2
  rcases le_total x0 x1 with a01 | a01 <;> rcases le_total x1 x2 with a12 | a12 <;>
    rcases le_total x0 x2 with a02 | a02
  · obtain ⟨g1, g2, g3⟩ := hexagon_gap x2 x1 x0 (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith only [hd])
    exact Or.inl (Or.inl ⟨by linarith, by linarith, by linarith⟩)
  · obtain ⟨g1, g2, g3⟩ := hexagon_gap x2 x1 x0 (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith only [hd])
    exact Or.inl (Or.inl ⟨by linarith, by linarith, by linarith⟩)
  · obtain ⟨g1, g2, g3⟩ := hexagon_gap x1 x2 x0 (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith only [hd])
    exact Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith, by linarith⟩))
  · obtain ⟨g1, g2, g3⟩ := hexagon_gap x1 x0 x2 (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith only [hd])
    exact Or.inl (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩))
  · obtain ⟨g1, g2, g3⟩ := hexagon_gap x2 x0 x1 (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith only [hd])
    exact Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩)
  · obtain ⟨g1, g2, g3⟩ := hexagon_gap x0 x2 x1 (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith only [hd])
    exact Or.inl (Or.inr (Or.inr ⟨by linarith, by linarith, by linarith⟩))
  · obtain ⟨g1, g2, g3⟩ := hexagon_gap x0 x1 x2 (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith only [hd])
    exact Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩))
  · obtain ⟨g1, g2, g3⟩ := hexagon_gap x0 x1 x2 (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith only [hd])
    exact Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩))

/-- Three hexagon vertices that are pairwise far are all of the first kind or all of the
second. -/
theorem hex_triple {x0 x1 x2 y0 y1 y2 z0 z1 z2 : ℝ}
    (hx : IsE x0 x1 x2 ∨ IsE x1 x0 x2) (hy : IsE y0 y1 y2 ∨ IsE y1 y0 y2)
    (hz : IsE z0 z1 z2 ∨ IsE z1 z0 z2)
    (hxy : 5 / 4 ≤ (x0 - y0) ^ 2 + (x1 - y1) ^ 2 + (x2 - y2) ^ 2)
    (hxz : 5 / 4 ≤ (x0 - z0) ^ 2 + (x1 - z1) ^ 2 + (x2 - z2) ^ 2)
    (hyz : 5 / 4 ≤ (y0 - z0) ^ 2 + (y1 - z1) ^ 2 + (y2 - z2) ^ 2) :
    (IsE x0 x1 x2 ∧ IsE y0 y1 y2 ∧ IsE z0 z1 z2) ∨ (IsE x1 x0 x2 ∧ IsE y1 y0 y2 ∧ IsE z1 z0 z2) := by
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rcases hz with hz | hz
  · exact Or.inl ⟨hx, hy, hz⟩
  · exfalso
    rcases hx with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hy with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hz with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      linarith
  · exfalso
    rcases hx with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hy with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hz with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      linarith
  · exfalso
    rcases hx with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hy with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hz with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      linarith
  · exfalso
    rcases hx with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hy with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hz with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      linarith
  · exfalso
    rcases hx with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hy with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hz with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      linarith
  · exfalso
    rcases hx with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hy with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hz with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      linarith
  · exact Or.inr ⟨hx, hy, hz⟩

end Packing.Cube5
