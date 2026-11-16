/-
The best arrangement of nine points in the unit cube is unique: nine points pairwise at
distance at least `sqrt 3 / 2` are the centre and the eight corners
(`isUniqueMaxMinDist_nine`).

Two of nine points have the same half-cube. At squared distance at least `3/4` they differ by
`1/2` in every coordinate, and because a half-cube takes the value `1/2` on its lower side
only, the two points are opposite corners of the half-cube at the origin (`pair_low`).
Reflecting the cube gives such a pair at every corner (`pair_at`). If no point is the centre,
one point of each pair is the centre of a face (`face_at`). Centres of two adjacent faces are
too close. Centres of two opposite faces leave the other seven points only the midpoints of the
four edges between those faces, so two of the seven coincide (`no_two_faces`). Hence one point
is the centre (`exists_centre`), and the other eight, at squared distance at least `3/4` from
it, are corners.
-/
import Packing.Cube8Unique

set_option linter.unusedVariables false

namespace Packing.Cube9

open Packing.Cube

/-! ### One coordinate -/

/-- Two numbers of the unit interval on the same side of `1/2` differ by at most `1/2`. -/
theorem sq_le_of_side {s t : ℝ} (hs : 0 ≤ s ∧ s ≤ 1) (ht : 0 ≤ t ∧ t ≤ 1)
    (h : 1 / 2 < s ↔ 1 / 2 < t) : (s - t) ^ 2 ≤ 1 / 4 := by
  have key : -(1 / 2) ≤ s - t ∧ s - t ≤ 1 / 2 := by
    by_cases h1 : 1 / 2 < s
    · have h2 := h.mp h1
      constructor <;> linarith [hs.2, ht.2]
    · have h2 : ¬ 1 / 2 < t := fun k => h1 (h.mpr k)
      have h1' := not_lt.mp h1
      have h2' := not_lt.mp h2
      constructor <;> linarith [hs.1, ht.1]
  calc (s - t) ^ 2 ≤ (1 / 2) ^ 2 := sq_le_sq' key.1 key.2
    _ = 1 / 4 := by norm_num

theorem half_le_of_sq {u : ℝ} (h0 : 0 ≤ u) (h : 1 / 4 ≤ u ^ 2) : 1 / 2 ≤ u := by
  by_contra hc
  have hc' := not_le.mp hc
  nlinarith [mul_pos (sub_pos.mpr hc') (show (0 : ℝ) < 1 / 2 + u by linarith)]

/-- Two numbers of the unit interval on the same side of `1/2` that differ by at least `1/2`
are `0` and `1/2`. -/
theorem ends_of_side {s t : ℝ} (hs : 0 ≤ s ∧ s ≤ 1) (ht : 0 ≤ t ∧ t ≤ 1)
    (h : 1 / 2 < s ↔ 1 / 2 < t) (hd : 1 / 4 ≤ (s - t) ^ 2) :
    (s = 0 ∧ t = 1 / 2) ∨ (s = 1 / 2 ∧ t = 0) := by
  by_cases h1 : 1 / 2 < s
  · have h2 := h.mp h1
    exfalso
    nlinarith [mul_pos (show (0 : ℝ) < 1 / 2 - s + t by linarith [hs.2])
      (show (0 : ℝ) < 1 / 2 + s - t by linarith [ht.2])]
  · have h2 : ¬ 1 / 2 < t := fun k => h1 (h.mpr k)
    have h1' := not_lt.mp h1
    have h2' := not_lt.mp h2
    rcases le_total t s with hts | hst
    · have k := half_le_of_sq (sub_nonneg.mpr hts) hd
      exact Or.inr ⟨by linarith [ht.1], by linarith [ht.1]⟩
    · have k := half_le_of_sq (sub_nonneg.mpr hst) (by nlinarith)
      exact Or.inl ⟨by linarith [hs.1], by linarith [hs.1]⟩

theorem quarter_le {x : ℝ} (h : 0 ≤ x ∧ x ≤ 1) : (x - 1 / 2) ^ 2 ≤ 1 / 4 := by
  nlinarith [mul_nonneg h.1 (sub_nonneg.mpr h.2)]

theorem binary_of_quarter {x : ℝ} (h : (x - 1 / 2) ^ 2 = 1 / 4) : x = 0 ∨ x = 1 :=
  zero_or_one (by linear_combination (-1 : ℝ) * h)

/-- `1 - x` if `a`, else `x`. -/
noncomputable def fl (a : Bool) (x : ℝ) : ℝ := if a then 1 - x else x

/-- The end of the unit interval: `1` if `a`, else `0`. -/
noncomputable def en (a : Bool) : ℝ := if a then 1 else 0

theorem fl_bounds (a : Bool) {x : ℝ} (h : 0 ≤ x ∧ x ≤ 1) : 0 ≤ fl a x ∧ fl a x ≤ 1 := by
  cases a
  · simpa [fl] using h
  · simp only [fl, ↓reduceIte]
    constructor <;> linarith [h.1, h.2]

theorem fl_sub_sq (a : Bool) (x y : ℝ) : (fl a x - fl a y) ^ 2 = (x - y) ^ 2 := by
  cases a
  · simp [fl]
  · simp only [fl, ↓reduceIte]
    ring

theorem fl_eq_zero {a : Bool} {x : ℝ} (h : fl a x = 0) : x = en a := by
  cases a
  · simpa [fl, en] using h
  · simp only [fl, ↓reduceIte] at h
    simp only [en, ↓reduceIte]
    linarith

theorem fl_eq_half {a : Bool} {x : ℝ} (h : fl a x = 1 / 2) : x = 1 / 2 := by
  cases a
  · simpa [fl] using h
  · simp only [fl, ↓reduceIte] at h
    linarith

/-! ### Nine points by coordinates -/

/-- The coordinates of nine points of the unit cube, pairwise at squared distance at least
`3/4`. -/
def Sep (X Y Z : Fin 9 → ℝ) : Prop :=
  (∀ i, 0 ≤ X i ∧ X i ≤ 1) ∧ (∀ i, 0 ≤ Y i ∧ Y i ≤ 1) ∧ (∀ i, 0 ≤ Z i ∧ Z i ≤ 1) ∧
    ∀ i j, i ≠ j → 3 / 4 ≤ (X i - X j) ^ 2 + (Y i - Y j) ^ 2 + (Z i - Z j) ^ 2

theorem sep_fl {X Y Z : Fin 9 → ℝ} (h : Sep X Y Z) (a b c : Bool) :
    Sep (fun i => fl a (X i)) (fun i => fl b (Y i)) (fun i => fl c (Z i)) := by
  obtain ⟨hX, hY, hZ, hS⟩ := h
  refine ⟨fun i => fl_bounds a (hX i), fun i => fl_bounds b (hY i), fun i => fl_bounds c (hZ i),
    fun i j hij => ?_⟩
  show 3 / 4 ≤ (fl a (X i) - fl a (X j)) ^ 2 + (fl b (Y i) - fl b (Y j)) ^ 2
    + (fl c (Z i) - fl c (Z j)) ^ 2
  rw [fl_sub_sq, fl_sub_sq, fl_sub_sq]
  exact hS i j hij

theorem sep_perm1 {X Y Z : Fin 9 → ℝ} (h : Sep X Y Z) : Sep Y X Z := by
  obtain ⟨hX, hY, hZ, hS⟩ := h
  exact ⟨hY, hX, hZ, fun i j hij => by linarith [hS i j hij]⟩

theorem sep_perm2 {X Y Z : Fin 9 → ℝ} (h : Sep X Y Z) : Sep Z X Y := by
  obtain ⟨hX, hY, hZ, hS⟩ := h
  exact ⟨hZ, hX, hY, fun i j hij => by linarith [hS i j hij]⟩

/-- Two of the nine points are opposite corners of the half-cube at the origin. -/
theorem pair_low {X Y Z : Fin 9 → ℝ} (h : Sep X Y Z) :
    ∃ i j, i ≠ j ∧ ((X i = 0 ∧ X j = 1 / 2) ∨ (X i = 1 / 2 ∧ X j = 0))
      ∧ ((Y i = 0 ∧ Y j = 1 / 2) ∨ (Y i = 1 / 2 ∧ Y j = 0))
      ∧ ((Z i = 0 ∧ Z j = 1 / 2) ∨ (Z i = 1 / 2 ∧ Z j = 0)) := by
  obtain ⟨hX, hY, hZ, hS⟩ := h
  obtain ⟨i, j, hij, hc⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i => (decide (1 / 2 < X i), decide (1 / 2 < Y i), decide (1 / 2 < Z i))) (by simp)
  simp only [Prod.mk.injEq, decide_eq_decide] at hc
  obtain ⟨cx, cy, cz⟩ := hc
  have ex := sq_le_of_side (hX i) (hX j) cx
  have ey := sq_le_of_side (hY i) (hY j) cy
  have ez := sq_le_of_side (hZ i) (hZ j) cz
  have hs := hS i j hij
  exact ⟨i, j, hij, ends_of_side (hX i) (hX j) cx (by linarith),
    ends_of_side (hY i) (hY j) cy (by linarith), ends_of_side (hZ i) (hZ j) cz (by linarith)⟩

/-- Two of the nine points are opposite corners of the half-cube at the corner `(a, b, c)`. -/
theorem pair_at {X Y Z : Fin 9 → ℝ} (h : Sep X Y Z) (a b c : Bool) :
    ∃ i j, i ≠ j ∧ ((X i = en a ∧ X j = 1 / 2) ∨ (X i = 1 / 2 ∧ X j = en a))
      ∧ ((Y i = en b ∧ Y j = 1 / 2) ∨ (Y i = 1 / 2 ∧ Y j = en b))
      ∧ ((Z i = en c ∧ Z j = 1 / 2) ∨ (Z i = 1 / 2 ∧ Z j = en c)) := by
  obtain ⟨i, j, hij, hx, hy, hz⟩ := pair_low (sep_fl h a b c)
  exact ⟨i, j, hij,
    hx.imp (fun k => ⟨fl_eq_zero k.1, fl_eq_half k.2⟩) (fun k => ⟨fl_eq_half k.1, fl_eq_zero k.2⟩),
    hy.imp (fun k => ⟨fl_eq_zero k.1, fl_eq_half k.2⟩) (fun k => ⟨fl_eq_half k.1, fl_eq_zero k.2⟩),
    hz.imp (fun k => ⟨fl_eq_zero k.1, fl_eq_half k.2⟩) (fun k => ⟨fl_eq_half k.1, fl_eq_zero k.2⟩)⟩

/-- If no point is the centre, one of the nine points is the centre of a face at the corner
`(a, b, c)`. -/
theorem face_at {X Y Z : Fin 9 → ℝ} (h : Sep X Y Z)
    (hno : ¬ ∃ k, X k = 1 / 2 ∧ Y k = 1 / 2 ∧ Z k = 1 / 2) (a b c : Bool) :
    ∃ u, (X u = en a ∧ Y u = 1 / 2 ∧ Z u = 1 / 2) ∨ (X u = 1 / 2 ∧ Y u = en b ∧ Z u = 1 / 2)
      ∨ (X u = 1 / 2 ∧ Y u = 1 / 2 ∧ Z u = en c) := by
  obtain ⟨i, j, hij, hx, hy, hz⟩ := pair_at h a b c
  rcases hx with ⟨x1, x2⟩ | ⟨x1, x2⟩ <;> rcases hy with ⟨y1, y2⟩ | ⟨y1, y2⟩ <;>
    rcases hz with ⟨z1, z2⟩ | ⟨z1, z2⟩
  · exact (hno ⟨j, x2, y2, z2⟩).elim
  · exact ⟨j, Or.inr (Or.inr ⟨x2, y2, z2⟩)⟩
  · exact ⟨j, Or.inr (Or.inl ⟨x2, y2, z2⟩)⟩
  · exact ⟨i, Or.inl ⟨x1, y1, z1⟩⟩
  · exact ⟨j, Or.inl ⟨x2, y2, z2⟩⟩
  · exact ⟨i, Or.inr (Or.inl ⟨x1, y1, z1⟩)⟩
  · exact ⟨i, Or.inr (Or.inr ⟨x1, y1, z1⟩)⟩
  · exact (hno ⟨i, x1, y1, z1⟩).elim

/-- The nine points do not include the centre of the face `x = 0` and the centre of a face
through the corner `(1, 1, 1)`. -/
theorem no_two_faces {X Y Z : Fin 9 → ℝ} (h : Sep X Y Z) {u w : Fin 9}
    (hu : X u = 0 ∧ Y u = 1 / 2 ∧ Z u = 1 / 2)
    (hw : (X w = 1 ∧ Y w = 1 / 2 ∧ Z w = 1 / 2) ∨ (X w = 1 / 2 ∧ Y w = 1 ∧ Z w = 1 / 2)
      ∨ (X w = 1 / 2 ∧ Y w = 1 / 2 ∧ Z w = 1)) : False := by
  obtain ⟨hX, hY, hZ, hS⟩ := h
  obtain ⟨u0, u1, u2⟩ := hu
  have huw : u ≠ w := by
    intro e
    rw [← e] at hw
    rcases hw with ⟨w0, _, _⟩ | ⟨w0, _, _⟩ | ⟨w0, _, _⟩ <;> rw [u0] at w0 <;> norm_num at w0
  rcases hw with ⟨w0, w1, w2⟩ | ⟨w0, w1, w2⟩ | ⟨w0, w1, w2⟩
  · -- opposite faces: every other point is the midpoint of an edge between them
    have key : ∀ i, i ≠ u → i ≠ w →
        X i = 1 / 2 ∧ (Y i = 0 ∨ Y i = 1) ∧ (Z i = 0 ∨ Z i = 1) := by
      intro i hiu hiw
      have s1 := hS i u hiu
      have s2 := hS i w hiw
      rw [u0, u1, u2] at s1
      rw [w0, w1, w2] at s2
      have qy := quarter_le (hY i)
      have qz := quarter_le (hZ i)
      have a1 : 1 / 2 ≤ X i := half_le_of_sq (hX i).1 (by nlinarith)
      have a2 : 1 / 2 ≤ 1 - X i := half_le_of_sq (by linarith [(hX i).2]) (by nlinarith)
      have hx : X i = 1 / 2 := by linarith
      rw [hx] at s1
      exact ⟨hx, binary_of_quarter (le_antisymm qy (by nlinarith)),
        binary_of_quarter (le_antisymm qz (by nlinarith))⟩
    have hcard : (Finset.univ : Finset (Bool × Bool)).card
        < ((Finset.univ : Finset (Fin 9)).erase u |>.erase w).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨huw.symm, Finset.mem_univ w⟩),
        Finset.card_erase_of_mem (Finset.mem_univ u)]
      simp
    obtain ⟨x, hx, y, hy, hxy, he⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (f := fun i => (decide (Y i = 1), decide (Z i = 1))) hcard (fun _ _ => Finset.mem_univ _)
    simp only [Prod.mk.injEq, decide_eq_decide] at he
    have mx := Finset.mem_erase.mp hx
    have my := Finset.mem_erase.mp hy
    have kx := key x (Finset.mem_erase.mp mx.2).1 mx.1
    have ky := key y (Finset.mem_erase.mp my.2).1 my.1
    have eqY : Y x = Y y := by
      rcases kx.2.1 with a | a <;> rcases ky.2.1 with b | b
      · rw [a, b]
      · have t := he.1.mpr b
        rw [a] at t
        norm_num at t
      · have t := he.1.mp a
        rw [b] at t
        norm_num at t
      · rw [a, b]
    have eqZ : Z x = Z y := by
      rcases kx.2.2 with a | a <;> rcases ky.2.2 with b | b
      · rw [a, b]
      · have t := he.2.mpr b
        rw [a] at t
        norm_num at t
      · have t := he.2.mp a
        rw [b] at t
        norm_num at t
      · rw [a, b]
    have t := hS x y hxy
    rw [kx.1, ky.1, eqY, eqZ] at t
    norm_num at t
  · have t := hS u w huw
    rw [u0, u1, u2, w0, w1, w2] at t
    norm_num at t
  · have t := hS u w huw
    rw [u0, u1, u2, w0, w1, w2] at t
    norm_num at t

/-- One of the nine points is the centre of the cube. -/
theorem exists_centre {X Y Z : Fin 9 → ℝ} (h : Sep X Y Z) :
    ∃ k, X k = 1 / 2 ∧ Y k = 1 / 2 ∧ Z k = 1 / 2 := by
  by_contra hno
  obtain ⟨u, hu⟩ := face_at h hno false false false
  obtain ⟨w, hw⟩ := face_at h hno true true true
  simp only [en, Bool.false_eq_true, ↓reduceIte] at hu hw
  rcases hu with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩
  · exact no_two_faces h ⟨a, b, c⟩ hw
  · refine no_two_faces (sep_perm1 h) (w := w) ⟨b, a, c⟩ ?_
    rcases hw with ⟨a', b', c'⟩ | ⟨a', b', c'⟩ | ⟨a', b', c'⟩
    · exact Or.inr (Or.inl ⟨b', a', c'⟩)
    · exact Or.inl ⟨b', a', c'⟩
    · exact Or.inr (Or.inr ⟨b', a', c'⟩)
  · refine no_two_faces (sep_perm2 h) (w := w) ⟨c, a, b⟩ ?_
    rcases hw with ⟨a', b', c'⟩ | ⟨a', b', c'⟩ | ⟨a', b', c'⟩
    · exact Or.inr (Or.inl ⟨c', a', b'⟩)
    · exact Or.inr (Or.inr ⟨c', a', b'⟩)
    · exact Or.inl ⟨c', a', b'⟩

/-! ### The theorem -/

/-- A numbering of the corners of the cube. -/
noncomputable def idx : Fin 8 ≃ (Fin 3 → Bool) := Fintype.equivOfCardEq (by simp)

/-- The centre and the eight corners of the cube. -/
noncomputable def nine : Fin 9 → Pt := Fin.cases centre fun i => corner (idx i)

theorem nine_zero : nine 0 = centre := rfl

theorem nine_succ (i : Fin 8) : nine i.succ = corner (idx i) := rfl

theorem sqrt_three_half_sq : (Real.sqrt 3 / 2) ^ 2 = 3 / 4 := by
  rw [div_pow, Real.sq_sqrt (by norm_num)]
  norm_num

theorem isUniqueUpToCubeSymm_nine : IsUniqueUpToCubeSymm 9 (Real.sqrt 3 / 2) nine := by
  apply isUniqueUpToCubeSymm_of_exists (div_pos (Real.sqrt_pos.mpr (by norm_num)) (by norm_num))
  intro p hp hd
  have hsq : ∀ i j, i ≠ j → 3 / 4 ≤ dist (p i) (p j) ^ 2 := by
    intro i j hij
    have h := pow_le_pow_left₀ (by positivity) (hd i j hij) 2
    rwa [sqrt_three_half_sq] at h
  have hsep : Sep (fun i => p i 0) (fun i => p i 1) (fun i => p i 2) := by
    refine ⟨fun i => hp i 0, fun i => hp i 1, fun i => hp i 2, fun i j hij => ?_⟩
    have t := hsq i j hij
    rw [dist_sq] at t
    exact t
  obtain ⟨k, k0, k1, k2⟩ := exists_centre hsep
  have hk : p k = centre := pt_ext k0 k1 k2
  have hbin : ∀ i, i ≠ k → ∀ c, p i c = 0 ∨ p i c = 1 := by
    intro i hik
    have t := hsq i k hik
    rw [dist_sq, hk] at t
    simp only [centre_apply] at t
    have q0 := quarter_le (hp i 0)
    have q1 := quarter_le (hp i 1)
    have q2 := quarter_le (hp i 2)
    intro c
    have k3 : c = 0 ∨ c = 1 ∨ c = 2 := by fin_cases c <;> simp
    rcases k3 with rfl | rfl | rfl
    · exact binary_of_quarter (le_antisymm q0 (by linarith))
    · exact binary_of_quarter (le_antisymm q1 (by linarith))
    · exact binary_of_quarter (le_antisymm q2 (by linarith))
  refine ⟨fun _ => false, 1, fun i => ?_⟩
  by_cases hik : i = k
  · exact ⟨0, by rw [Packing.Cube8.cubeSymm_false_one, hik, hk, nine_zero]⟩
  · have hb := hbin i hik
    refine ⟨Fin.succ (idx.symm fun c => decide (p i c = 1)), ?_⟩
    rw [Packing.Cube8.cubeSymm_false_one, nine_succ, Equiv.apply_symm_apply]
    refine pt_ext ?_ ?_ ?_ <;> rw [corner_apply]
    · rcases hb 0 with e | e <;> simp [e]
    · rcases hb 1 with e | e <;> simp [e]
    · rcases hb 2 with e | e <;> simp [e]

theorem inCube_nine (i : Fin 9) : InCube (nine i) := by
  refine Fin.cases ?_ (fun i => ?_) i
  · rw [nine_zero]
    exact inCube_centre
  · rw [nine_succ]
    exact inCube_corner _

theorem dist_nine : ∀ i j : Fin 9, i ≠ j → Real.sqrt 3 / 2 ≤ dist (nine i) (nine j) := by
  have hle : Real.sqrt 3 / 2 ≤ 1 := by
    have : Real.sqrt 3 ≤ 2 := by
      rw [show (2 : ℝ) = Real.sqrt 4 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num)
    linarith
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · intro h
    exact absurd rfl h
  · intro _
    rw [nine_zero, nine_succ]
    exact le_dist (by rw [sqrt_three_half_sq, dist_sq_centre_corner])
  · intro _
    rw [nine_zero, nine_succ, dist_comm]
    exact le_dist (by rw [sqrt_three_half_sq, dist_sq_centre_corner])
  · intro h
    rw [nine_succ, nine_succ]
    exact hle.trans (one_le_dist_corner fun h' => h (congrArg Fin.succ (idx.injective h')))

/-- The centre and the eight corners are the unique best arrangement of nine points in the
unit cube. -/
theorem isUniqueMaxMinDist_nine : IsUniqueMaxMinDist 9 (Real.sqrt 3 / 2) nine :=
  ⟨inCube_nine, dist_nine, exists_dist_le_nine, isUniqueUpToCubeSymm_nine⟩

end Packing.Cube9
