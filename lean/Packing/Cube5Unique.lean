/-
The best arrangement of five points in the unit cube is unique.

Reference: J. Schaer, "The densest packing of five spheres in a cube", Canad. Math. Bull. 9
(1966), 271-274. Every arrangement of five points of the cube with pairwise distances at least
`sqrt 5 / 2` is the image of `five`, in some order, under a symmetry of the cube
(`isUniqueMaxMinDist_five`).

The proof normalizes as `Cube5.lean` does: `a` is the least coordinatewise distance from a point
to a corner, the corner is moved to the origin and the point to `(p1, p2, a)`.

* `a = 0`. The point is the origin. Every other point has coordinate sum at least `3/2`
  (`hexagon_vertex`). Two of the other four have the same least coordinate, so one of them is
  `(1, 1, 1)` (`same_part_corner`). The remaining three are then vertices of the hexagon
  `x0 + x1 + x2 = 3/2`, pairwise far, which leaves `five` or its mirror image (`hex_triple`).
* `a > 0`. If another point lies in the region of the first claim then `a = 1/2`
  (`claim1_tight`), both points are determined (`claim1_half`), and two of the remaining three
  points are close (`thin_box`). Otherwise two of the other four points have the same least
  coordinate, which forces `a = 0` (`pair_tight`).

Schaer's text treats `0 < a ≤ 1/2` in one step, with strict inequality in the first claim. At
`a = 1/2` the points `(0, 1/2, 1/2)` and `(1, 0, 1/2)` satisfy the hypotheses of that claim at
distance exactly `sqrt 5 / 2`, so this case is handled separately here.
-/
import Packing.CubeUnique
import Packing.Cube5UniqueLemmas

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Packing.Cube5

open Packing.Cube

/-! ### Points and their coordinates -/

theorem pt_ext {x y : Pt} (h0 : x 0 = y 0) (h1 : x 1 = y 1) (h2 : x 2 = y 2) : x = y := by
  ext c
  fin_cases c
  · exact h0
  · exact h1
  · exact h2

theorem five_val (m : Fin 5) (c : Fin 3) :
    five m c = if m = 0 then 0 else if m = 1 then 1 else
      if m = 2 then (if c = 0 then 0 else if c = 1 then 1 / 2 else 1)
      else if m = 3 then (if c = 0 then 1 / 2 else if c = 1 then 1 else 0)
      else (if c = 0 then 1 else if c = 1 then 0 else 1 / 2) := by
  rw [five_apply]
  fin_cases m <;> fin_cases c <;> simp

theorem eq_five_of {x : Pt}
    (h : (x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0) ∨ (x 0 = 1 ∧ x 1 = 1 ∧ x 2 = 1) ∨ IsE (x 0) (x 1) (x 2)) :
    ∃ m, x = five m := by
  rcases h with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩
  · exact ⟨0, pt_ext (by rw [a, five_val]; simp) (by rw [b, five_val]; simp)
      (by rw [c, five_val]; simp)⟩
  · exact ⟨1, pt_ext (by rw [a, five_val]; simp) (by rw [b, five_val]; simp)
      (by rw [c, five_val]; simp)⟩
  · exact ⟨2, pt_ext (by rw [a, five_val]; simp) (by rw [b, five_val]; simp)
      (by rw [c, five_val]; simp)⟩
  · exact ⟨3, pt_ext (by rw [a, five_val]; simp) (by rw [b, five_val]; simp)
      (by rw [c, five_val]; simp)⟩
  · exact ⟨4, pt_ext (by rw [a, five_val]; simp) (by rw [b, five_val]; simp)
      (by rw [c, five_val]; simp)⟩

/-- The swap of the first two coordinates. -/
noncomputable def mirror (x : Pt) : Pt := cubeSymm (fun _ => false) (Equiv.swap 0 1) x

theorem mirror_apply (x : Pt) (c : Fin 3) : mirror x c = x (Equiv.swap 0 1 c) := by
  unfold mirror
  rw [cubeSymm_apply]
  simp

theorem mirror_zero (x : Pt) : mirror x 0 = x 1 := by
  rw [mirror_apply, Equiv.swap_apply_left]

theorem mirror_one (x : Pt) : mirror x 1 = x 0 := by
  rw [mirror_apply, Equiv.swap_apply_right]

theorem mirror_two (x : Pt) : mirror x 2 = x 2 := by
  rw [mirror_apply, Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]

theorem mirror_mirror (x : Pt) : mirror (mirror x) = x :=
  pt_ext (by rw [mirror_zero, mirror_one]) (by rw [mirror_one, mirror_zero])
    (by rw [mirror_two, mirror_two])

theorem cubeSymm_mirror (v : Fin 3 → Bool) (σ : Equiv.Perm (Fin 3)) (x : Pt) :
    cubeSymm v σ (mirror x) = cubeSymm v (σ.trans (Equiv.swap 0 1)) x := by
  ext c
  simp only [cubeSymm_apply, mirror_apply, Equiv.trans_apply]

theorem eq_five_of_mirror {x : Pt}
    (h : (x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0) ∨ (x 0 = 1 ∧ x 1 = 1 ∧ x 2 = 1) ∨ IsE (x 1) (x 0) (x 2)) :
    ∃ m, mirror x = five m := by
  apply eq_five_of
  rw [mirror_zero, mirror_one, mirror_two]
  rcases h with ⟨a, b, c⟩ | ⟨a, b, c⟩ | h
  · exact Or.inl ⟨b, a, c⟩
  · exact Or.inr (Or.inl ⟨b, a, c⟩)
  · exact Or.inr (Or.inr h)

theorem reflect_IsE {x0 x1 x2 : ℝ} (h : IsE (1 - x0) (1 - x1) (1 - x2)) : IsE x1 x0 x2 := by
  unfold IsE at h ⊢
  rcases h with ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩
  · exact Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩)
  · exact Or.inl ⟨by linarith, by linarith, by linarith⟩
  · exact Or.inr (Or.inr ⟨by linarith, by linarith, by linarith⟩)

/-! ### Indices -/

theorem two_more : ∀ a b : Fin 5, ∃ j k, j ≠ a ∧ j ≠ b ∧ k ≠ a ∧ k ≠ b ∧ j ≠ k := by decide

theorem three_more : ∀ a b : Fin 5, a ≠ b → ∃ j k l,
    (∀ i, i = a ∨ i = b ∨ i = j ∨ i = k ∨ i = l) ∧ j ≠ a ∧ j ≠ b ∧ k ≠ a ∧ k ≠ b ∧ l ≠ a ∧ l ≠ b ∧
      j ≠ k ∧ j ≠ l ∧ k ≠ l := by decide

/-! ### Normal position -/

theorem escapes {a : ℝ} {x : Pt} (hQ : ∀ w : Fin 3 → Bool, ∃ c, a ≤ cd w x c) :
    (x 0 ≤ 1 - a ∨ a ≤ x 1 ∨ a ≤ x 2) ∧ (a ≤ x 0 ∨ x 1 ≤ 1 - a ∨ a ≤ x 2) ∧
      (x 0 ≤ 1 - a ∨ x 1 ≤ 1 - a ∨ x 2 ≤ 1 - a) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨c, hc⟩ := hQ ![true, false, false]
    have k3 : c = 0 ∨ c = 1 ∨ c = 2 := by fin_cases c <;> simp
    rcases k3 with rfl | rfl | rfl <;> simp [cd] at hc
    · left; linarith
    · right; left; linarith
    · right; right; linarith
  · obtain ⟨c, hc⟩ := hQ ![false, true, false]
    have k3 : c = 0 ∨ c = 1 ∨ c = 2 := by fin_cases c <;> simp
    rcases k3 with rfl | rfl | rfl <;> simp [cd] at hc
    · left; linarith
    · right; left; linarith
    · right; right; linarith
  · obtain ⟨c, hc⟩ := hQ ![true, true, true]
    have k3 : c = 0 ∨ c = 1 ∨ c = 2 := by fin_cases c <;> simp
    rcases k3 with rfl | rfl | rfl <;> simp [cd] at hc
    · left; linarith
    · right; left; linarith
    · right; right; linarith

/-- Of two far points of the cube with the same least coordinate and coordinate sums at least
`3/2`, one is `(1, 1, 1)`. -/
theorem corner_of_same_least {y z : Pt} (hy : InCube y) (hz : InCube z) {k : Fin 3}
    (hyk : ∀ c, y k ≤ y c) (hzk : ∀ c, z k ≤ z c) (ys : 3 / 2 ≤ y 0 + y 1 + y 2)
    (zs : 3 / 2 ≤ z 0 + z 1 + z 2)
    (hd : 5 / 4 ≤ (y 0 - z 0) ^ 2 + (y 1 - z 1) ^ 2 + (y 2 - z 2) ^ 2) :
    (y 0 = 1 ∧ y 1 = 1 ∧ y 2 = 1) ∨ (z 0 = 1 ∧ z 1 = 1 ∧ z 2 = 1) := by
  have k3 : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  rcases k3 with rfl | rfl | rfl
  · exact same_part_corner (hy 0) (hy 1) (hy 2) (hz 0) (hz 1) (hz 2) (hyk 1) (hyk 2) (hzk 1)
      (hzk 2) ys zs hd
  · rcases same_part_corner (hy 1) (hy 0) (hy 2) (hz 1) (hz 0) (hz 2) (hyk 0) (hyk 2) (hzk 0)
      (hzk 2) (by linarith) (by linarith) (by linarith only [hd]) with ⟨e1, e0, e2⟩ | ⟨e1, e0, e2⟩
    · exact Or.inl ⟨e0, e1, e2⟩
    · exact Or.inr ⟨e0, e1, e2⟩
  · rcases same_part_corner (hy 2) (hy 0) (hy 1) (hz 2) (hz 0) (hz 1) (hyk 0) (hyk 1) (hzk 0)
      (hzk 1) (by linarith) (by linarith) (by linarith only [hd]) with ⟨e2, e0, e1⟩ | ⟨e2, e0, e1⟩
    · exact Or.inl ⟨e0, e1, e2⟩
    · exact Or.inr ⟨e0, e1, e2⟩

/-- Two points outside the region of the first claim with the same least coordinate, at
squared distance at least `5/4`, force `a = 0`. -/
theorem pair_tight {a : ℝ} (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) {y z : Pt} (hy : Far a y)
    (hz : Far a z) {k : Fin 3} (hyk : ∀ c, y k ≤ y c) (hzk : ∀ c, z k ≤ z c)
    (hd : 5 / 4 ≤ dist y z ^ 2) : a ≤ 0 := by
  rw [dist_sq] at hd
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
    rcases corner_of_same_least hy.cube hz.cube hyk hzk ys zs hd with ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩
    · rcases hy.q8 with h | h | h <;> linarith
    · rcases hz.q8 with h | h | h <;> linarith
  · obtain ⟨ys, ya⟩ := part2_facts ha2 (hyk 0) (hyk 2) y0.2 hy.out hy.q2
    obtain ⟨zs, za⟩ := part2_facts ha2 (hzk 0) (hzk 2) z0.2 hz.out hz.q2
    rcases corner_of_same_least hy.cube hz.cube hyk hzk ys zs hd with ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩
    · rcases hy.q8 with h | h | h <;> linarith
    · rcases hz.q8 with h | h | h <;> linarith
  · obtain ⟨ya1, ya2, ya3⟩ :=
      part3_facts ha2 (hyk 0) (hyk 1) y0.2 y1.2 hy.out hy.q2 hy.q3 hy.q8
    obtain ⟨za1, za2, za3⟩ :=
      part3_facts ha2 (hzk 0) (hzk 1) z0.2 z1.2 hz.out hz.q2 hz.q3 hz.q8
    have y20 := hyk 0
    have y21 := hyk 1
    have z20 := hzk 0
    have z21 := hzk 1
    rcases hy.out with ho | ho <;> rcases hz.out with go | go
    · exact c3a_ss (y 0) (y 1) (y 2) (z 0) (z 1) (z 2) a ha (by linarith)
        y0.1 (by linarith) y1.1 (by linarith) y2.1 (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        z0.1 (by linarith) z1.1 (by linarith) z2.1 (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
    · exact c3a_st (y 0) (y 1) (y 2) (z 0) (z 1) (z 2) a ha (by linarith)
        y0.1 (by linarith) y1.1 (by linarith) y2.1 (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        z0.1 (by linarith) z1.1 (by linarith) z2.1 (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
    · exact c3a_st (z 0) (z 1) (z 2) (y 0) (y 1) (y 2) a ha (by linarith)
        z0.1 (by linarith) z1.1 (by linarith) z2.1 (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        y0.1 (by linarith) y1.1 (by linarith) y2.1 (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith only [hd])
    · exact c3a_tt (y 0) (y 1) (y 2) (z 0) (z 1) (z 2) a ha (by linarith)
        y0.1 (by linarith) y1.1 (by linarith) y2.1 (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        z0.1 (by linarith) z1.1 (by linarith) z2.1 (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd

/-- Five points of the cube in normal position, pairwise at squared distance at least `5/4`,
are `five` or its mirror image. -/
theorem normal_unique (q : Fin 5 → Pt) (hq : ∀ i, InCube (q i)) (i0 : Fin 5) {a : ℝ}
    (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) (h0 : q i0 0 ≤ a) (h1 : q i0 1 ≤ a) (h2 : q i0 2 = a)
    (hQ : ∀ i (w : Fin 3 → Bool), ∃ c, a ≤ cd w (q i) c)
    (hsq : ∀ i j, i ≠ j → 5 / 4 ≤ dist (q i) (q j) ^ 2) :
    (∀ i, ∃ m, q i = five m) ∨ (∀ i, ∃ m, mirror (q i) = five m) := by
  have hE := fun i => escapes (hQ i)
  have hbase : ∀ i, i ≠ i0 →
      5 / 4 ≤ (q i 0 - q i0 0) ^ 2 + (q i 1 - q i0 1) ^ 2 + (q i 2 - a) ^ 2 := by
    intro i hi
    have h := hsq i i0 hi
    rw [dist_sq, h2] at h
    exact h
  rcases eq_or_lt_of_le ha with ha0 | hapos
  · -- `a = 0`
    have ha0' : a = 0 := ha0.symm
    have b0 : q i0 0 = 0 := le_antisymm (by linarith) (hq i0 0).1
    have b1 : q i0 1 = 0 := le_antisymm (by linarith) (hq i0 1).1
    have b2 : q i0 2 = 0 := by rw [h2, ha0']
    have hnorm : ∀ i, i ≠ i0 → 5 / 4 ≤ q i 0 ^ 2 + q i 1 ^ 2 + q i 2 ^ 2 := by
      intro i hi
      have h := hbase i hi
      rw [b0, b1, ha0'] at h
      linarith only [h]
    have hsum : ∀ i, i ≠ i0 → 3 / 2 ≤ q i 0 + q i 1 + q i 2 := by
      intro i hi
      by_contra hn
      push Not at hn
      rcases hexagon_vertex (hq i 0) (hq i 1) (hq i 2) hn.le (hnorm i hi) with h | h
      · rcases h with ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ <;> linarith
      · rcases h with ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ <;> linarith
    choose k hk using fun i => exists_min_coord (q i)
    obtain ⟨j, j', hjj, hkk⟩ :=
      Fintype.exists_ne_map_eq_of_card_lt (fun j : Fin 4 => k (i0.succAbove j)) (by simp)
    have hne : i0.succAbove j ≠ i0.succAbove j' := fun h => hjj (Fin.succAbove_right_injective h)
    have hcorner : ∃ i1, i1 ≠ i0 ∧ q i1 0 = 1 ∧ q i1 1 = 1 ∧ q i1 2 = 1 := by
      have hd := hsq _ _ hne
      rw [dist_sq] at hd
      rcases corner_of_same_least (hq (i0.succAbove j)) (hq (i0.succAbove j')) (hk _)
        (by simpa only [hkk] using hk (i0.succAbove j')) (hsum _ (Fin.succAbove_ne i0 j))
        (hsum _ (Fin.succAbove_ne i0 j')) hd with h | h
      · exact ⟨_, Fin.succAbove_ne i0 j, h⟩
      · exact ⟨_, Fin.succAbove_ne i0 j', h⟩
    obtain ⟨i1, hi1, c0, c1, c2⟩ := hcorner
    have hhex : ∀ i, i ≠ i0 → i ≠ i1 →
        IsE (q i 0) (q i 1) (q i 2) ∨ IsE (q i 1) (q i 0) (q i 2) := by
      intro i hi hi'
      have h := hsq i i1 hi'
      rw [dist_sq, c0, c1, c2] at h
      have b := hq i
      rcases hexagon_vertex (x0 := 1 - q i 0) (x1 := 1 - q i 1) (x2 := 1 - q i 2)
        ⟨by linarith [(b 0).2], by linarith [(b 0).1]⟩ ⟨by linarith [(b 1).2], by linarith [(b 1).1]⟩
        ⟨by linarith [(b 2).2], by linarith [(b 2).1]⟩ (by linarith [hsum i hi])
        (by linarith only [h]) with hv | hv
      · exact Or.inr (reflect_IsE hv)
      · exact Or.inl (reflect_IsE hv)
    obtain ⟨j3, k3, l3, hall, hj0, hj1, hk0, hk1, hl0, hl1, hjk, hjl, hkl⟩ :=
      three_more i0 i1 (Ne.symm hi1)
    have djk := hsq j3 k3 hjk
    have djl := hsq j3 l3 hjl
    have dkl := hsq k3 l3 hkl
    rw [dist_sq] at djk djl dkl
    rcases hex_triple (hhex j3 hj0 hj1) (hhex k3 hk0 hk1) (hhex l3 hl0 hl1) djk djl dkl with
      ⟨ej, ek, el⟩ | ⟨ej, ek, el⟩
    · left
      intro i
      rcases hall i with h | h | h | h | h
      · rw [h]; exact eq_five_of (Or.inl ⟨b0, b1, b2⟩)
      · rw [h]; exact eq_five_of (Or.inr (Or.inl ⟨c0, c1, c2⟩))
      · rw [h]; exact eq_five_of (Or.inr (Or.inr ej))
      · rw [h]; exact eq_five_of (Or.inr (Or.inr ek))
      · rw [h]; exact eq_five_of (Or.inr (Or.inr el))
    · right
      intro i
      rcases hall i with h | h | h | h | h
      · rw [h]; exact eq_five_of_mirror (Or.inl ⟨b0, b1, b2⟩)
      · rw [h]; exact eq_five_of_mirror (Or.inr (Or.inl ⟨c0, c1, c2⟩))
      · rw [h]; exact eq_five_of_mirror (Or.inr (Or.inr ej))
      · rw [h]; exact eq_five_of_mirror (Or.inr (Or.inr ek))
      · rw [h]; exact eq_five_of_mirror (Or.inr (Or.inr el))
  · -- `a > 0` is impossible
    exfalso
    by_cases hex : ∃ i, i ≠ i0 ∧ q i 0 + q i 1 + q i 2 ≤ 3 / 2 ∧ q i 0 + q i 1 ≤ 3 / 2 - a
    · obtain ⟨i, hi, hs, ht⟩ := hex
      have hprod := claim1_tight ha ha2 (hq i0 0).1 h0 (hq i0 1).1 h1 (hq i 0) (hq i 1) (hq i 2)
        hs ht (hE i).1 (hE i).2.1 (hbase i hi)
      have hhalf : a = 1 / 2 := by
        have h12 : 1 - 2 * a ≤ 0 := by
          by_contra hn
          push Not at hn
          nlinarith [mul_pos hapos hn]
        linarith
      have hb := hbase i hi
      rw [hhalf] at hb
      have hE2 : q i 0 ≤ 1 / 2 ∨ 1 / 2 ≤ q i 1 ∨ 1 / 2 ≤ q i 2 := by
        rcases (hE i).1 with h | h | h
        · left; linarith
        · right; left; linarith
        · right; right; linarith
      have hE3 : 1 / 2 ≤ q i 0 ∨ q i 1 ≤ 1 / 2 ∨ 1 / 2 ≤ q i 2 := by
        rcases (hE i).2.1 with h | h | h
        · left; linarith
        · right; left; linarith
        · right; right; linarith
      obtain ⟨j, k, hj0, hji, hk0, hki, hjk⟩ := two_more i0 i
      have dj0 := hsq j i0 hj0
      have dji := hsq j i hji
      have dk0 := hsq k i0 hk0
      have dki := hsq k i hki
      have djk := hsq j k hjk
      rw [dist_sq] at dj0 dji dk0 dki djk
      rw [h2, hhalf] at dj0 dk0
      rcases claim1_half (hq i0 0).1 (by linarith) (hq i0 1).1 (by linarith) (hq i 0) (hq i 1)
        (hq i 2) hs (by linarith) hE2 hE3 hb with ⟨y1, y2, y3, p1, p2⟩ | ⟨y1, y2, y3, p1, p2⟩
      · rw [p1, p2] at dj0 dk0
        rw [y1, y2, y3] at dji dki
        exact thin_box (hq j 0) (hq j 1) (hq j 2) (hq k 0) (hq k 1) (hq k 2)
          (by linarith only [dj0]) (by linarith only [dji]) (by linarith only [dk0])
          (by linarith only [dki]) djk
      · rw [p1, p2] at dj0 dk0
        rw [y1, y2, y3] at dji dki
        exact thin_box (hq j 1) (hq j 0) (hq j 2) (hq k 1) (hq k 0) (hq k 2)
          (by linarith only [dj0]) (by linarith only [dji]) (by linarith only [dk0])
          (by linarith only [dki]) (by linarith only [djk])
    · push Not at hex
      have hfar : ∀ i, i ≠ i0 → Far a (q i) := by
        intro i hi
        refine ⟨hq i, ?_, (hE i).1, (hE i).2.1, (hE i).2.2⟩
        by_cases hs : q i 0 + q i 1 + q i 2 ≤ 3 / 2
        · exact Or.inr (hex i hi hs)
        · exact Or.inl (not_le.mp hs)
      choose k hk using fun i => exists_min_coord (q i)
      obtain ⟨j, j', hjj, hkk⟩ :=
        Fintype.exists_ne_map_eq_of_card_lt (fun j : Fin 4 => k (i0.succAbove j)) (by simp)
      have hne : i0.succAbove j ≠ i0.succAbove j' :=
        fun h => hjj (Fin.succAbove_right_injective h)
      have hle := pair_tight ha ha2 (hfar _ (Fin.succAbove_ne i0 j))
        (hfar _ (Fin.succAbove_ne i0 j')) (hk (i0.succAbove j))
        (by simpa only [hkk] using hk (i0.succAbove j')) (hsq _ _ hne)
      linarith

/-! ### The theorem -/

/-- Every arrangement of five points of the unit cube with pairwise distances at least
`sqrt 5 / 2` is the image of `five`, in some order, under a symmetry of the cube. -/
theorem isUniqueUpToCubeSymm_five : IsUniqueUpToCubeSymm 5 (Real.sqrt 5 / 2) five := by
  intro p hp hd
  have hsq : ∀ i j, i ≠ j → 5 / 4 ≤ dist (p i) (p j) ^ 2 := by
    intro i j hij
    have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ Real.sqrt 5 / 2) (hd i j hij) 2
    rwa [sqrt_five_div_two_sq] at h
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
  have hN := normal_unique (fun i => T v0 σ (p i)) (fun i => inCube_T v0 σ (hp i)) i0 ha ha2
    (cd_le_cdist v0 (p i0) (σ 0)) (cd_le_cdist v0 (p i0) (σ 1)) (by rw [T_apply, hσ, hc0])
    (by
      intro i w
      obtain ⟨c, hc⟩ := exists_cd_eq_cdist (fun c => xor (w (σ.symm c)) (v0 c)) (p i)
      refine ⟨σ.symm c, ?_⟩
      rw [cd_T, ← hc]
      exact hmin (i, fun c => xor (w (σ.symm c)) (v0 c)) (Finset.mem_univ _))
    (fun i j hij => by rw [dist_T]; exact hsq i j hij)
  have hback : ∀ i, p i = cubeSymm v0 σ (T v0 σ (p i)) := by
    intro i
    ext c
    have hσσ : σ (σ c) = c := Equiv.swap_apply_self 2 c0 c
    simp only [cubeSymm_apply, T_apply, hσσ]
    unfold cd
    split_ifs <;> ring
  have hall : ∃ (v : Fin 3 → Bool) (τ : Equiv.Perm (Fin 3)),
      ∀ i, ∃ m, p i = cubeSymm v τ (five m) := by
    rcases hN with h | h
    · refine ⟨v0, σ, fun i => ?_⟩
      obtain ⟨m, hm⟩ := h i
      exact ⟨m, by rw [← hm]; exact hback i⟩
    · refine ⟨v0, σ.trans (Equiv.swap 0 1), fun i => ?_⟩
      obtain ⟨m, hm⟩ := h i
      refine ⟨m, ?_⟩
      rw [← cubeSymm_mirror, ← hm, mirror_mirror]
      exact hback i
  obtain ⟨v, τ, hm⟩ := hall
  choose e he using hm
  have hinj : Function.Injective e := by
    intro i j hij
    by_contra hne
    have h := hsq i j hne
    rw [he i, he j, hij, dist_self] at h
    norm_num at h
  exact ⟨v, τ, Equiv.ofBijective e (Finite.injective_iff_bijective.mp hinj), he⟩

/-- `five` is the unique best arrangement of five points in the unit cube, up to the
symmetries of the cube. -/
theorem isUniqueMaxMinDist_five : IsUniqueMaxMinDist 5 (Real.sqrt 5 / 2) five :=
  ⟨inCube_five, fun _ _ h => dist_five h, exists_dist_le_five, isUniqueUpToCubeSymm_five⟩

/-- Every best arrangement of five points in the unit cube is congruent to `five`. -/
theorem isUniqueUpToIsometry_five : IsUniqueUpToIsometry 5 (Real.sqrt 5 / 2) five :=
  isUniqueMaxMinDist_five.toIsometry

end Packing.Cube5
