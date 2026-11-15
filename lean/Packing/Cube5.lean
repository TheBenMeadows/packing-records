/-
The largest minimum distance among five points of the unit cube `[0,1]^3` is `sqrt 5 / 2`.

Reference: J. Schaer, "The densest packing of five spheres in a cube", Canad. Math. Bull. 9
(1966), 271-274. Only the value is proved here, not the uniqueness of the configuration, so
the argument runs with strict inequalities and Schaer's cases (A) and (B) merge.

Take five points pairwise further apart than `sqrt 5 / 2`. Among all points and all corners
pick the pair with the least coordinatewise distance `a`; after a reflection and a swap of
coordinates the corner is the origin and the point is `(p1, p2, a)` with `p1, p2 ≤ a ≤ 1/2`,
and every point has a coordinate at distance at least `a` from every corner. Then
* no other point `y` has `y1 + y2 + y3 ≤ 3/2` and `y1 + y2 ≤ 3/2 - a` (`claim1`), and
* two of the other four points have the same least coordinate, and two such points are at
  squared distance at most `5/4` (`pair_le`).
The polynomial inequalities behind both steps are in `Packing/Cube5Cert.lean`.
-/
import Packing.CubeBalls
import Packing.Cube5Cert

-- Several hypotheses below reach `linarith` through the context and are never named.
set_option linter.unusedVariables false

namespace Packing.Cube5

open Packing.Cube

/-! ### Real inequalities -/

/-- For `p` between `0` and `a`, the point `y` is no further from `p` than from `0` or `a`. -/
theorem sq_sub_le_endpoint {y p a : ℝ} (hp : 0 ≤ p) (hpa : p ≤ a) :
    (y - p) ^ 2 ≤ y ^ 2 ∨ (y - p) ^ 2 ≤ (y - a) ^ 2 := by
  by_cases h : p ≤ 2 * y
  · left
    nlinarith [mul_nonneg hp (sub_nonneg.mpr h)]
  · right
    push Not at h
    nlinarith [mul_nonneg (sub_nonneg.mpr hpa) (by linarith : (0 : ℝ) ≤ a + p - 2 * y)]

/-- Schaer's first claim: a point of the cube outside the corner cubes at `(1,0,0)` and
`(0,1,0)`, with `y1 + y2 + y3 ≤ 3/2` and `y1 + y2 ≤ 3/2 - a`, is within `sqrt 5 / 2` of
`(p1, p2, a)`. -/
theorem claim1 {y1 y2 y3 p1 p2 a : ℝ} (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2)
    (hp1 : 0 ≤ p1) (hp1a : p1 ≤ a) (hp2 : 0 ≤ p2) (hp2a : p2 ≤ a)
    (hy1 : 0 ≤ y1 ∧ y1 ≤ 1) (hy2 : 0 ≤ y2 ∧ y2 ≤ 1) (hy3 : 0 ≤ y3 ∧ y3 ≤ 1)
    (hs : y1 + y2 + y3 ≤ 3 / 2) (ht : y1 + y2 ≤ 3 / 2 - a)
    (hQ2 : y1 ≤ 1 - a ∨ a ≤ y2 ∨ a ≤ y3) (hQ3 : a ≤ y1 ∨ y2 ≤ 1 - a ∨ a ≤ y3) :
    (y1 - p1) ^ 2 + (y2 - p2) ^ 2 + (y3 - a) ^ 2 ≤ 5 / 4 := by
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
  have k00 : y1 ^ 2 + y2 ^ 2 + (y3 - a) ^ 2 ≤ 5 / 4 := by
    rcases hQ2 with hA | hB | hC
    · rcases hQ3 with hD | hE | hC
      · exact c1_AD_00 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) (by linarith)
      · exact c1_AE_00 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) (by linarith)
      · exact c1_AC_00 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) (by linarith)
    · rcases hQ3 with hD | hE | hC
      · exact c1_BD_00 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) (by linarith)
      · exact c1_BE_00 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) (by linarith)
      · exact c1_BC_00 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) (by linarith)
    · exact c1_C_00 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith)
  have k01 : y1 ^ 2 + (y2 - a) ^ 2 + (y3 - a) ^ 2 ≤ 5 / 4 := by
    rcases hQ2 with hA | hB | hC
    · rcases hQ3 with hD | hE | hC
      · exact c1_AD_01 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) (by linarith)
      · exact c1_AE_01 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) (by linarith)
      · exact c1_AC_01 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) (by linarith)
    · rcases hQ3 with hD | hE | hC
      · exact c1_BD_01 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) (by linarith)
      · exact c1_BE_01 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) (by linarith)
      · exact c1_BC_01 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) (by linarith)
    · exact c1_C_01 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith)
  have k10 : (y1 - a) ^ 2 + y2 ^ 2 + (y3 - a) ^ 2 ≤ 5 / 4 := by
    rcases hQ2 with hA | hB | hC
    · rcases hQ3 with hD | hE | hC
      · exact c1_AD_10 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) (by linarith)
      · exact c1_AE_10 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) (by linarith)
      · exact c1_AC_10 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) (by linarith)
    · rcases hQ3 with hD | hE | hC
      · exact c1_BD_10 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) (by linarith)
      · exact c1_BE_10 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) (by linarith)
      · exact c1_BC_10 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) (by linarith)
    · exact c1_C_10 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith)
  have k11 : (y1 - a) ^ 2 + (y2 - a) ^ 2 + (y3 - a) ^ 2 ≤ 5 / 4 := by
    rcases hQ2 with hA | hB | hC
    · rcases hQ3 with hD | hE | hC
      · exact c1_AD_11 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) (by linarith)
      · exact c1_AE_11 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) (by linarith)
      · exact c1_AC_11 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) (by linarith)
    · rcases hQ3 with hD | hE | hC
      · exact c1_BD_11 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) (by linarith)
      · exact c1_BE_11 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) (by linarith)
      · exact c1_BC_11 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith) (by linarith)
    · exact c1_C_11 y1 y2 y3 a h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by linarith)
  rcases sq_sub_le_endpoint (y := y1) hp1 hp1a with e1 | e1 <;>
    rcases sq_sub_le_endpoint (y := y2) hp2 hp2a with e2 | e2 <;> linarith

/-- A point with least coordinate `y1`, outside the region of `claim1` and outside the corner
cube at `(0,1,0)`, has `y1 + y2 + y3 ≥ 3/2` and `y3 ≥ a`. -/
theorem part1_facts {y1 y2 y3 a : ℝ} (ha2 : a ≤ 1 / 2) (h12 : y1 ≤ y2) (h13 : y1 ≤ y3)
    (hy2 : y2 ≤ 1) (hS : 3 / 2 < y1 + y2 + y3 ∨ 3 / 2 - a < y1 + y2)
    (hQ : a ≤ y1 ∨ y2 ≤ 1 - a ∨ a ≤ y3) : 3 / 2 ≤ y1 + y2 + y3 ∧ a ≤ y3 := by
  rcases hS with h | h <;> rcases hQ with q | q | q <;> exact ⟨by linarith, by linarith⟩

/-- The mirror image of `part1_facts`, for least coordinate `y2` and the corner cube at
`(1,0,0)`. -/
theorem part2_facts {y1 y2 y3 a : ℝ} (ha2 : a ≤ 1 / 2) (h21 : y2 ≤ y1) (h23 : y2 ≤ y3)
    (hy1 : y1 ≤ 1) (hS : 3 / 2 < y1 + y2 + y3 ∨ 3 / 2 - a < y1 + y2)
    (hQ : y1 ≤ 1 - a ∨ a ≤ y2 ∨ a ≤ y3) : 3 / 2 ≤ y1 + y2 + y3 ∧ a ≤ y3 := by
  rcases hS with h | h <;> rcases hQ with q | q | q <;> exact ⟨by linarith, by linarith⟩

/-- A point with least coordinate `y3`, outside the region of `claim1` and outside the corner
cubes at `(1,0,0)`, `(0,1,0)` and `(1,1,1)`, has `y1 ≥ a`, `y2 ≥ a` and `y3 ≤ 1 - a`. -/
theorem part3_facts {y1 y2 y3 a : ℝ} (ha2 : a ≤ 1 / 2) (h31 : y3 ≤ y1) (h32 : y3 ≤ y2)
    (hy1 : y1 ≤ 1) (hy2 : y2 ≤ 1) (hS : 3 / 2 < y1 + y2 + y3 ∨ 3 / 2 - a < y1 + y2)
    (hQ2 : y1 ≤ 1 - a ∨ a ≤ y2 ∨ a ≤ y3) (hQ3 : a ≤ y1 ∨ y2 ≤ 1 - a ∨ a ≤ y3)
    (hQ8 : y1 ≤ 1 - a ∨ y2 ≤ 1 - a ∨ y3 ≤ 1 - a) : a ≤ y1 ∧ a ≤ y2 ∧ y3 ≤ 1 - a := by
  refine ⟨?_, ?_, ?_⟩
  · rcases hS with h | h <;> rcases hQ3 with q | q | q <;> linarith
  · rcases hS with h | h <;> rcases hQ2 with q | q | q <;> linarith
  · rcases hQ8 with q | q | q <;> linarith

/-! ### Two points with the same least coordinate -/

/-- The hypotheses on one point that the second step uses. -/
structure Far (a : ℝ) (y : Pt) : Prop where
  cube : InCube y
  out : 3 / 2 < y 0 + y 1 + y 2 ∨ 3 / 2 - a < y 0 + y 1
  q2 : y 0 ≤ 1 - a ∨ a ≤ y 1 ∨ a ≤ y 2
  q3 : a ≤ y 0 ∨ y 1 ≤ 1 - a ∨ a ≤ y 2
  q8 : y 0 ≤ 1 - a ∨ y 1 ≤ 1 - a ∨ y 2 ≤ 1 - a

/-- Schaer's second claim: two such points with the same least coordinate are within
`sqrt 5 / 2` of each other. -/
theorem pair_le {a : ℝ} (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) {y z : Pt} (hy : Far a y) (hz : Far a z)
    {k : Fin 3} (hyk : ∀ c, y k ≤ y c) (hzk : ∀ c, z k ≤ z c) : dist y z ^ 2 ≤ 5 / 4 := by
  rw [dist_sq]
  have y0 := hy.cube 0
  have y1 := hy.cube 1
  have y2 := hy.cube 2
  have z0 := hz.cube 0
  have z1 := hz.cube 1
  have z2 := hz.cube 2
  have k3 : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  rcases k3 with rfl | rfl | rfl
  · obtain ⟨ys, ya⟩ := part1_facts ha2 (hyk 1) (hyk 2) y1.2 hy.out hy.q3
    obtain ⟨zs, za⟩ := part1_facts ha2 (hzk 1) (hzk 2) z1.2 hz.out hz.q3
    have y01 := hyk 1
    have y02 := hyk 2
    have z01 := hzk 1
    have z02 := hzk 2
    exact c2_p1 (y 0) (y 1) (y 2) (z 0) (z 1) (z 2) a ha (by linarith)
      y0.1 (by linarith) y1.1 (by linarith) y2.1 (by linarith)
      (by linarith) (by linarith) (by linarith) (by linarith)
      z0.1 (by linarith) z1.1 (by linarith) z2.1 (by linarith)
      (by linarith) (by linarith) (by linarith) (by linarith)
  · obtain ⟨ys, ya⟩ := part2_facts ha2 (hyk 0) (hyk 2) y0.2 hy.out hy.q2
    obtain ⟨zs, za⟩ := part2_facts ha2 (hzk 0) (hzk 2) z0.2 hz.out hz.q2
    have y10 := hyk 0
    have y12 := hyk 2
    have z10 := hzk 0
    have z12 := hzk 2
    exact c2_p2 (y 0) (y 1) (y 2) (z 0) (z 1) (z 2) a ha (by linarith)
      y0.1 (by linarith) y1.1 (by linarith) y2.1 (by linarith)
      (by linarith) (by linarith) (by linarith) (by linarith)
      z0.1 (by linarith) z1.1 (by linarith) z2.1 (by linarith)
      (by linarith) (by linarith) (by linarith) (by linarith)
  · obtain ⟨ya1, ya2, ya3⟩ :=
      part3_facts ha2 (hyk 0) (hyk 1) y0.2 y1.2 hy.out hy.q2 hy.q3 hy.q8
    obtain ⟨za1, za2, za3⟩ :=
      part3_facts ha2 (hzk 0) (hzk 1) z0.2 z1.2 hz.out hz.q2 hz.q3 hz.q8
    have y20 := hyk 0
    have y21 := hyk 1
    have z20 := hzk 0
    have z21 := hzk 1
    rcases hy.out with ho | ho <;> rcases hz.out with go | go
    · exact c2_p3_ss (y 0) (y 1) (y 2) (z 0) (z 1) (z 2) a ha (by linarith)
        y0.1 (by linarith) y1.1 (by linarith) y2.1 (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        z0.1 (by linarith) z1.1 (by linarith) z2.1 (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    · exact c2_p3_st (y 0) (y 1) (y 2) (z 0) (z 1) (z 2) a ha (by linarith)
        y0.1 (by linarith) y1.1 (by linarith) y2.1 (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        z0.1 (by linarith) z1.1 (by linarith) z2.1 (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    · have h := c2_p3_st (z 0) (z 1) (z 2) (y 0) (y 1) (y 2) a ha (by linarith)
        z0.1 (by linarith) z1.1 (by linarith) z2.1 (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        y0.1 (by linarith) y1.1 (by linarith) y2.1 (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
      have e : (y 0 - z 0) ^ 2 + (y 1 - z 1) ^ 2 + (y 2 - z 2) ^ 2 =
          (z 0 - y 0) ^ 2 + (z 1 - y 1) ^ 2 + (z 2 - y 2) ^ 2 := by ring
      rw [e]
      exact h
    · exact c2_p3_tt (y 0) (y 1) (y 2) (z 0) (z 1) (z 2) a ha (by linarith)
        y0.1 (by linarith) y1.1 (by linarith) y2.1 (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        z0.1 (by linarith) z1.1 (by linarith) z2.1 (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)

/-! ### Distance to a corner, and the symmetries of the cube -/

/-- The distance from `x` to the corner `v` along coordinate `c`, for `x` in the cube. -/
noncomputable def cd (v : Fin 3 → Bool) (x : Pt) (c : Fin 3) : ℝ := if v c then 1 - x c else x c

theorem cd_nonneg {x : Pt} (hx : InCube x) (v : Fin 3 → Bool) (c : Fin 3) : 0 ≤ cd v x c := by
  have h := hx c
  unfold cd
  split_ifs <;> linarith

theorem cd_le_one {x : Pt} (hx : InCube x) (v : Fin 3 → Bool) (c : Fin 3) : cd v x c ≤ 1 := by
  have h := hx c
  unfold cd
  split_ifs <;> linarith

/-- The largest coordinate distance from `x` to the corner `v`. -/
noncomputable def cdist (v : Fin 3 → Bool) (x : Pt) : ℝ :=
  max (max (cd v x 0) (cd v x 1)) (cd v x 2)

theorem cd_le_cdist (v : Fin 3 → Bool) (x : Pt) (c : Fin 3) : cd v x c ≤ cdist v x := by
  have k3 : c = 0 ∨ c = 1 ∨ c = 2 := by fin_cases c <;> simp
  rcases k3 with rfl | rfl | rfl
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  · exact le_trans (le_max_right _ _) (le_max_left _ _)
  · exact le_max_right _ _

theorem exists_cd_eq_cdist (v : Fin 3 → Bool) (x : Pt) : ∃ c, cdist v x = cd v x c := by
  unfold cdist
  rcases max_choice (max (cd v x 0) (cd v x 1)) (cd v x 2) with h | h
  · rcases max_choice (cd v x 0) (cd v x 1) with h' | h'
    · exact ⟨0, by rw [h, h']⟩
    · exact ⟨1, by rw [h, h']⟩
  · exact ⟨2, h⟩

/-- Reflect the coordinates where `v` is `true`, then permute the coordinates by `σ`. This
maps the corner `v` to the origin. -/
noncomputable def T (v : Fin 3 → Bool) (σ : Equiv.Perm (Fin 3)) (x : Pt) : Pt :=
  WithLp.toLp 2 fun c => cd v x (σ c)

theorem T_apply (v : Fin 3 → Bool) (σ : Equiv.Perm (Fin 3)) (x : Pt) (c : Fin 3) :
    T v σ x c = cd v x (σ c) := rfl

theorem inCube_T (v : Fin 3 → Bool) (σ : Equiv.Perm (Fin 3)) {x : Pt} (hx : InCube x) :
    InCube (T v σ x) := fun c => ⟨cd_nonneg hx v (σ c), cd_le_one hx v (σ c)⟩

theorem dist_sq_sum (x y : Pt) : dist x y ^ 2 = ∑ c, (x c - y c) ^ 2 := by
  rw [dist_sq, Fin.sum_univ_three]

theorem dist_T (v : Fin 3 → Bool) (σ : Equiv.Perm (Fin 3)) (x y : Pt) :
    dist (T v σ x) (T v σ y) ^ 2 = dist x y ^ 2 := by
  rw [dist_sq_sum, dist_sq_sum, ← Equiv.sum_comp σ fun c => (x c - y c) ^ 2]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [T_apply, cd]
  split_ifs <;> ring

/-- The coordinate distances of `T v σ x` to a corner `w` are those of `x` to another corner. -/
theorem cd_T (v w : Fin 3 → Bool) (σ : Equiv.Perm (Fin 3)) (x : Pt) (c : Fin 3) :
    cd w (T v σ x) (σ.symm c) = cd (fun c => xor (w (σ.symm c)) (v c)) x c := by
  simp only [cd, T_apply, Equiv.apply_symm_apply]
  rcases Bool.eq_false_or_eq_true (w (σ.symm c)) with h | h <;>
    rcases Bool.eq_false_or_eq_true (v c) with h' | h' <;> simp [h, h']

/-! ### Five points -/

theorem exists_min_coord (x : Pt) : ∃ k : Fin 3, ∀ c, x k ≤ x c := by
  obtain ⟨k, -, hk⟩ := Finset.exists_min_image Finset.univ (fun c => x c) ⟨0, Finset.mem_univ _⟩
  exact ⟨k, fun c => hk c (Finset.mem_univ c)⟩

/-- Five points of the cube in normal position: `q i0 = (p1, p2, a)` with `p1, p2 ≤ a ≤ 1/2`,
and every point has a coordinate at distance at least `a` from every corner. -/
theorem exists_dist_sq_le_of_normal (q : Fin 5 → Pt) (hq : ∀ i, InCube (q i)) (i0 : Fin 5)
    {a : ℝ} (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) (h0 : q i0 0 ≤ a) (h1 : q i0 1 ≤ a)
    (h2 : q i0 2 = a) (hQ : ∀ i (w : Fin 3 → Bool), ∃ c, a ≤ cd w (q i) c) :
    ∃ i j, i ≠ j ∧ dist (q i) (q j) ^ 2 ≤ 5 / 4 := by
  have hQ2 : ∀ i, q i 0 ≤ 1 - a ∨ a ≤ q i 1 ∨ a ≤ q i 2 := by
    intro i
    obtain ⟨c, hc⟩ := hQ i ![true, false, false]
    have k3 : c = 0 ∨ c = 1 ∨ c = 2 := by fin_cases c <;> simp
    rcases k3 with rfl | rfl | rfl <;> simp [cd] at hc
    · left; linarith
    · right; left; linarith
    · right; right; linarith
  have hQ3 : ∀ i, a ≤ q i 0 ∨ q i 1 ≤ 1 - a ∨ a ≤ q i 2 := by
    intro i
    obtain ⟨c, hc⟩ := hQ i ![false, true, false]
    have k3 : c = 0 ∨ c = 1 ∨ c = 2 := by fin_cases c <;> simp
    rcases k3 with rfl | rfl | rfl <;> simp [cd] at hc
    · left; linarith
    · right; left; linarith
    · right; right; linarith
  have hQ8 : ∀ i, q i 0 ≤ 1 - a ∨ q i 1 ≤ 1 - a ∨ q i 2 ≤ 1 - a := by
    intro i
    obtain ⟨c, hc⟩ := hQ i ![true, true, true]
    have k3 : c = 0 ∨ c = 1 ∨ c = 2 := by fin_cases c <;> simp
    rcases k3 with rfl | rfl | rfl <;> simp [cd] at hc
    · left; linarith
    · right; left; linarith
    · right; right; linarith
  by_contra hcon
  push Not at hcon
  have hfar : ∀ i, i ≠ i0 → Far a (q i) := by
    intro i hi
    refine ⟨hq i, ?_, hQ2 i, hQ3 i, hQ8 i⟩
    by_contra hn
    push Not at hn
    have hc := claim1 ha ha2 (hq i0 0).1 h0 (hq i0 1).1 h1 (hq i 0) (hq i 1) (hq i 2)
      hn.1 hn.2 (hQ2 i) (hQ3 i)
    have hd := hcon i i0 hi
    rw [dist_sq, h2] at hd
    linarith
  choose k hk using fun i => exists_min_coord (q i)
  obtain ⟨j, j', hjj, hkk⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun j : Fin 4 => k (i0.succAbove j)) (by simp)
  have hne : i0.succAbove j ≠ i0.succAbove j' := fun h => hjj (Fin.succAbove_right_injective h)
  have hle := pair_le ha ha2 (hfar _ (Fin.succAbove_ne i0 j)) (hfar _ (Fin.succAbove_ne i0 j'))
    (hk (i0.succAbove j)) (by simpa only [hkk] using hk (i0.succAbove j'))
  exact absurd hle (not_le.mpr (hcon _ _ hne))

theorem sqrt_five_div_two_sq : (Real.sqrt 5 / 2) ^ 2 = 5 / 4 := by
  rw [div_pow, Real.sq_sqrt (by norm_num)]
  norm_num

/-- Any five points of the unit cube include two at distance at most `sqrt 5 / 2`. -/
theorem exists_dist_le_five (p : Fin 5 → Pt) (hp : ∀ i, InCube (p i)) :
    ∃ i j, i ≠ j ∧ dist (p i) (p j) ≤ Real.sqrt 5 / 2 := by
  obtain ⟨⟨i0, v0⟩, -, hmin⟩ := Finset.exists_min_image
    (Finset.univ : Finset (Fin 5 × (Fin 3 → Bool))) (fun iv => cdist iv.2 (p iv.1))
    ⟨(0, fun _ => false), Finset.mem_univ _⟩
  obtain ⟨c0, hc0⟩ := exists_cd_eq_cdist v0 (p i0)
  have ha : 0 ≤ cdist v0 (p i0) := by
    rw [hc0]
    exact cd_nonneg (hp i0) v0 c0
  have ha2 : cdist v0 (p i0) ≤ 1 / 2 := by
    refine le_trans (hmin (i0, fun c => decide (1 / 2 < p i0 c)) (Finset.mem_univ _)) ?_
    have hc : ∀ c, cd (fun c => decide (1 / 2 < p i0 c)) (p i0) c ≤ 1 / 2 := by
      intro c
      unfold cd
      by_cases h : 1 / 2 < p i0 c
      · simp only [h, decide_true, ite_true]
        linarith
      · simp only [h, decide_false, Bool.false_eq_true, ite_false]
        linarith
    exact max_le (max_le (hc 0) (hc 1)) (hc 2)
  let σ : Equiv.Perm (Fin 3) := Equiv.swap 2 c0
  have hσ : σ 2 = c0 := Equiv.swap_apply_left 2 c0
  have hnorm := exists_dist_sq_le_of_normal (fun i => T v0 σ (p i))
    (fun i => inCube_T v0 σ (hp i)) i0 ha ha2 (cd_le_cdist v0 (p i0) (σ 0))
    (cd_le_cdist v0 (p i0) (σ 1)) (by rw [T_apply, hσ, hc0]) (by
      intro i w
      obtain ⟨c, hc⟩ := exists_cd_eq_cdist (fun c => xor (w (σ.symm c)) (v0 c)) (p i)
      refine ⟨σ.symm c, ?_⟩
      rw [cd_T, ← hc]
      exact hmin (i, fun c => xor (w (σ.symm c)) (v0 c)) (Finset.mem_univ _))
  obtain ⟨i, j, hij, hd⟩ := hnorm
  rw [dist_T] at hd
  exact ⟨i, j, hij, dist_le (by positivity) (by rw [sqrt_five_div_two_sq]; exact hd)⟩

/-- Schaer's configuration: two opposite corners and three edge midpoints. -/
noncomputable def five : Fin 5 → Pt := fun i =>
  WithLp.toLp 2 (![![0, 0, 0], ![1, 1, 1], ![0, 1 / 2, 1], ![1 / 2, 1, 0], ![1, 0, 1 / 2]] i)

theorem five_apply (i : Fin 5) (c : Fin 3) :
    five i c = (![![0, 0, 0], ![1, 1, 1], ![0, 1 / 2, 1], ![1 / 2, 1, 0], ![1, 0, 1 / 2]] :
      Fin 5 → Fin 3 → ℝ) i c := rfl

theorem inCube_five (i : Fin 5) : InCube (five i) := by
  intro c
  rw [five_apply]
  fin_cases i <;> fin_cases c <;> norm_num

theorem dist_five {i j : Fin 5} (h : i ≠ j) : Real.sqrt 5 / 2 ≤ dist (five i) (five j) := by
  apply le_dist
  rw [sqrt_five_div_two_sq, dist_sq]
  simp only [five_apply]
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl h | norm_num

/-- The largest minimum distance among five points of the unit cube is `sqrt 5 / 2`. -/
theorem isMaxMinDist_five : IsMaxMinDist 5 (Real.sqrt 5 / 2) :=
  ⟨⟨five, inCube_five, fun _ _ h => dist_five h⟩, exists_dist_le_five⟩

/-- Five equal balls in the unit cube have radius at most `(5 - 2 sqrt 5) / 2`, and that radius
is attained. -/
theorem isMaxRadius_five : IsMaxRadius 5 ((5 - 2 * Real.sqrt 5) / 2) := by
  have h := maxRadius_of_maxMinDist (div_pos (Real.sqrt_pos.mpr (by norm_num)) two_pos)
    isMaxMinDist_five
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have e : Real.sqrt 5 / 2 / (2 * (1 + Real.sqrt 5 / 2)) = (5 - 2 * Real.sqrt 5) / 2 := by
    rw [div_eq_iff (by positivity)]
    linear_combination h5
  rwa [e] at h

end Packing.Cube5
