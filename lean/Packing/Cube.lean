/-
The largest minimum distance among `N` points of the unit cube `[0,1]^3`, for `N = 2, 3, 4, 8, 9`.

This is the point form of packing `N` equal spheres in a cube: `N` spheres of radius `r` fit in
the unit cube exactly when `N` points of the unit cube are pairwise at distance at least
`2r / (1 - 2r)`, so a largest minimum distance `d` gives the largest radius `d / (2 (1 + d))`.
That translation is not formalized here.

Reference: J. Schaer, "On the densest packing of spheres in a cube", Canad. Math. Bull. 9 (1966),
265-270. The proofs below are the pigeonhole and averaging arguments; for `N = 8` the averaging
is over the twelve pairs of points that lie in adjacent half-cubes.
-/
import Mathlib

namespace Packing.Cube

/-- A point of `ℝ^3`. -/
abbrev Pt := EuclideanSpace ℝ (Fin 3)

/-- `x` lies in the unit cube `[0,1]^3`. -/
def InCube (x : Pt) : Prop := ∀ c, 0 ≤ x c ∧ x c ≤ 1

/-- `d` is the largest minimum distance among `N` points of the unit cube: some `N` points are
pairwise at distance at least `d`, and any `N` points include two at distance at most `d`. -/
def IsMaxMinDist (N : ℕ) (d : ℝ) : Prop :=
  (∃ p : Fin N → Pt, (∀ i, InCube (p i)) ∧ ∀ i j, i ≠ j → d ≤ dist (p i) (p j)) ∧
    ∀ p : Fin N → Pt, (∀ i, InCube (p i)) → ∃ i j, i ≠ j ∧ dist (p i) (p j) ≤ d

/-! ### Distances -/

theorem dist_sq (x y : Pt) :
    dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 + (x 2 - y 2) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _),
    Fin.sum_univ_three]
  simp only [Real.dist_eq, sq_abs]

theorem le_dist {x y : Pt} {d : ℝ} (h : d ^ 2 ≤ dist x y ^ 2) : d ≤ dist x y := by
  by_contra hlt
  push Not at hlt
  nlinarith [dist_nonneg (x := x) (y := y)]

theorem dist_le {x y : Pt} {d : ℝ} (hd : 0 ≤ d) (h : dist x y ^ 2 ≤ d ^ 2) : dist x y ≤ d := by
  by_contra hlt
  push Not at hlt
  nlinarith [dist_nonneg (x := x) (y := y)]

theorem one_lt_dist_sq {x y : Pt} (h : 1 < dist x y) : 1 < dist x y ^ 2 := by
  nlinarith [dist_nonneg (x := x) (y := y)]

theorem coord_sq_le_one {x y : Pt} (hx : InCube x) (hy : InCube y) (c : Fin 3) :
    (x c - y c) ^ 2 ≤ 1 := by
  have h1 := hx c
  have h2 := hy c
  calc (x c - y c) ^ 2 ≤ 1 ^ 2 := sq_le_sq' (by linarith) (by linarith)
    _ = 1 := by norm_num

/-! ### Corners and the centre -/

/-- The corner of the unit cube with coordinate `1` where `v` is `true`. -/
noncomputable def corner (v : Fin 3 → Bool) : Pt :=
  WithLp.toLp 2 fun c => if v c then 1 else 0

theorem corner_apply (v : Fin 3 → Bool) (c : Fin 3) : corner v c = if v c then 1 else 0 := rfl

theorem inCube_corner (v : Fin 3 → Bool) : InCube (corner v) := by
  intro c
  rw [corner_apply]
  split_ifs <;> norm_num

/-- The centre of the unit cube. -/
noncomputable def centre : Pt := WithLp.toLp 2 fun _ => 1 / 2

theorem centre_apply (c : Fin 3) : centre c = 1 / 2 := rfl

theorem inCube_centre : InCube centre := by
  intro c
  rw [centre_apply]
  norm_num

theorem corner_sub_sq (v w : Fin 3 → Bool) (c : Fin 3) :
    (corner v c - corner w c) ^ 2 = if v c = w c then 0 else 1 := by
  rw [corner_apply, corner_apply]
  cases v c <;> cases w c <;> simp

theorem dist_sq_corner (v w : Fin 3 → Bool) :
    dist (corner v) (corner w) ^ 2
      = (if v 0 = w 0 then 0 else 1) + (if v 1 = w 1 then 0 else 1)
        + (if v 2 = w 2 then 0 else 1) := by
  rw [dist_sq, corner_sub_sq, corner_sub_sq, corner_sub_sq]

/-- Distinct corners are at distance at least `1`. -/
theorem one_le_dist_corner {v w : Fin 3 → Bool} (h : v ≠ w) :
    1 ≤ dist (corner v) (corner w) := by
  apply le_dist
  rw [dist_sq_corner]
  obtain ⟨c, hc⟩ := Function.ne_iff.mp h
  have h0 : (0 : ℝ) ≤ if v 0 = w 0 then 0 else 1 := by split_ifs <;> norm_num
  have h1 : (0 : ℝ) ≤ if v 1 = w 1 then 0 else 1 := by split_ifs <;> norm_num
  have h2 : (0 : ℝ) ≤ if v 2 = w 2 then 0 else 1 := by split_ifs <;> norm_num
  fin_cases c
  · have hc' : ¬ v 0 = w 0 := hc
    have : (if v 0 = w 0 then (0 : ℝ) else 1) = 1 := by simp [hc']
    linarith
  · have hc' : ¬ v 1 = w 1 := hc
    have : (if v 1 = w 1 then (0 : ℝ) else 1) = 1 := by simp [hc']
    linarith
  · have hc' : ¬ v 2 = w 2 := hc
    have : (if v 2 = w 2 then (0 : ℝ) else 1) = 1 := by simp [hc']
    linarith

theorem dist_sq_centre_corner (v : Fin 3 → Bool) : dist centre (corner v) ^ 2 = 3 / 4 := by
  rw [dist_sq]
  simp only [centre_apply, corner_apply]
  cases v 0 <;> cases v 1 <;> cases v 2 <;> norm_num

/-! ### Two points -/

theorem isMaxMinDist_two : IsMaxMinDist 2 (Real.sqrt 3) := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hd : dist (corner fun _ => false) (corner fun _ => true) ^ 2 = 3 := by
    rw [dist_sq_corner]
    norm_num
  refine ⟨⟨Fin.cases (corner fun _ => false) fun _ => corner fun _ => true, ?_, ?_⟩, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact inCube_corner _
    · exact inCube_corner _
  · intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · intro h
      exact absurd rfl h
    · intro _
      exact le_dist (by simp only [Fin.cases_zero, Fin.cases_succ]; rw [h3, hd])
    · intro _
      exact le_dist (by simp only [Fin.cases_zero, Fin.cases_succ]; rw [h3, dist_comm, hd])
    · intro h
      exact absurd (congrArg Fin.succ (Subsingleton.elim i j)) h
  · intro p hp
    refine ⟨0, 1, by decide, dist_le (Real.sqrt_nonneg 3) ?_⟩
    rw [h3, dist_sq]
    have h0 := coord_sq_le_one (hp 0) (hp 1) 0
    have h1 := coord_sq_le_one (hp 0) (hp 1) 1
    have h2 := coord_sq_le_one (hp 0) (hp 1) 2
    linarith

/-! ### Three and four points -/

/-- Three numbers in `[0,1]` have squared differences summing to at most `2`. -/
theorem three_sq_le {a b c : ℝ} (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) (hc : 0 ≤ c ∧ c ≤ 1) :
    (a - b) ^ 2 + (a - c) ^ 2 + (b - c) ^ 2 ≤ 2 := by
  nlinarith [mul_nonneg ha.1 (sub_nonneg.mpr ha.2), mul_nonneg hb.1 (sub_nonneg.mpr hb.2),
    mul_nonneg hc.1 (sub_nonneg.mpr hc.2),
    mul_nonneg (mul_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr hb.2)) (sub_nonneg.mpr hc.2),
    mul_nonneg (mul_nonneg ha.1 hb.1) hc.1]

/-- Four numbers in `[0,1]` have squared differences summing to at most `4`. -/
theorem four_sq_le {a b c d : ℝ} (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1)
    (hc : 0 ≤ c ∧ c ≤ 1) (hd : 0 ≤ d ∧ d ≤ 1) :
    (a - b) ^ 2 + (a - c) ^ 2 + (a - d) ^ 2 + (b - c) ^ 2 + (b - d) ^ 2 + (c - d) ^ 2 ≤ 4 := by
  nlinarith [mul_nonneg ha.1 (sub_nonneg.mpr ha.2), mul_nonneg hb.1 (sub_nonneg.mpr hb.2),
    mul_nonneg hc.1 (sub_nonneg.mpr hc.2), mul_nonneg hd.1 (sub_nonneg.mpr hd.2),
    sq_nonneg (a + b + c + d - 2)]

/-- The four corners with an even number of coordinates equal to `1`. -/
def evenCorner : Fin 4 → Fin 3 → Bool :=
  ![![false, false, false], ![true, true, false], ![true, false, true], ![false, true, true]]

theorem dist_sq_evenCorner {i j : Fin 4} (h : i ≠ j) :
    dist (corner (evenCorner i)) (corner (evenCorner j)) ^ 2 = 2 := by
  rw [dist_sq_corner]
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl h | (simp [evenCorner]; try norm_num)

theorem exists_dist_le_three (p : Fin 3 → Pt) (hp : ∀ i, InCube (p i)) :
    ∃ i j, i ≠ j ∧ dist (p i) (p j) ≤ Real.sqrt 2 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsum : dist (p 0) (p 1) ^ 2 + dist (p 0) (p 2) ^ 2 + dist (p 1) (p 2) ^ 2 ≤ 6 := by
    rw [dist_sq, dist_sq, dist_sq]
    have e0 := three_sq_le (hp 0 0) (hp 1 0) (hp 2 0)
    have e1 := three_sq_le (hp 0 1) (hp 1 1) (hp 2 1)
    have e2 := three_sq_le (hp 0 2) (hp 1 2) (hp 2 2)
    linarith
  by_cases h01 : dist (p 0) (p 1) ^ 2 ≤ 2
  · exact ⟨0, 1, by decide, dist_le (Real.sqrt_nonneg 2) (by rw [h2]; exact h01)⟩
  by_cases h02 : dist (p 0) (p 2) ^ 2 ≤ 2
  · exact ⟨0, 2, by decide, dist_le (Real.sqrt_nonneg 2) (by rw [h2]; exact h02)⟩
  exact ⟨1, 2, by decide, dist_le (Real.sqrt_nonneg 2) (by rw [h2]; linarith)⟩

theorem exists_dist_le_four (p : Fin 4 → Pt) (hp : ∀ i, InCube (p i)) :
    ∃ i j, i ≠ j ∧ dist (p i) (p j) ≤ Real.sqrt 2 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsum : dist (p 0) (p 1) ^ 2 + dist (p 0) (p 2) ^ 2 + dist (p 0) (p 3) ^ 2
      + dist (p 1) (p 2) ^ 2 + dist (p 1) (p 3) ^ 2 + dist (p 2) (p 3) ^ 2 ≤ 12 := by
    rw [dist_sq, dist_sq, dist_sq, dist_sq, dist_sq, dist_sq]
    have e0 := four_sq_le (hp 0 0) (hp 1 0) (hp 2 0) (hp 3 0)
    have e1 := four_sq_le (hp 0 1) (hp 1 1) (hp 2 1) (hp 3 1)
    have e2 := four_sq_le (hp 0 2) (hp 1 2) (hp 2 2) (hp 3 2)
    linarith
  by_cases h01 : dist (p 0) (p 1) ^ 2 ≤ 2
  · exact ⟨0, 1, by decide, dist_le (Real.sqrt_nonneg 2) (by rw [h2]; exact h01)⟩
  by_cases h02 : dist (p 0) (p 2) ^ 2 ≤ 2
  · exact ⟨0, 2, by decide, dist_le (Real.sqrt_nonneg 2) (by rw [h2]; exact h02)⟩
  by_cases h03 : dist (p 0) (p 3) ^ 2 ≤ 2
  · exact ⟨0, 3, by decide, dist_le (Real.sqrt_nonneg 2) (by rw [h2]; exact h03)⟩
  by_cases h12 : dist (p 1) (p 2) ^ 2 ≤ 2
  · exact ⟨1, 2, by decide, dist_le (Real.sqrt_nonneg 2) (by rw [h2]; exact h12)⟩
  by_cases h13 : dist (p 1) (p 3) ^ 2 ≤ 2
  · exact ⟨1, 3, by decide, dist_le (Real.sqrt_nonneg 2) (by rw [h2]; exact h13)⟩
  exact ⟨2, 3, by decide, dist_le (Real.sqrt_nonneg 2) (by rw [h2]; linarith)⟩

theorem isMaxMinDist_four : IsMaxMinDist 4 (Real.sqrt 2) := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  refine ⟨⟨fun i => corner (evenCorner i), fun i => inCube_corner _, fun i j hij => ?_⟩,
    exists_dist_le_four⟩
  exact le_dist (by rw [h2, dist_sq_evenCorner hij])

theorem isMaxMinDist_three : IsMaxMinDist 3 (Real.sqrt 2) := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  refine ⟨⟨fun i => corner (evenCorner (Fin.castSucc i)), fun i => inCube_corner _,
    fun i j hij => ?_⟩, exists_dist_le_three⟩
  have hne : Fin.castSucc i ≠ Fin.castSucc j := fun h => hij (Fin.castSucc_injective 3 h)
  exact le_dist (by rw [h2, dist_sq_evenCorner hne])

/-! ### Half-cubes -/

/-- The half-cube of a point: for each coordinate, whether it exceeds `1/2`. -/
noncomputable def cell (x : Pt) : Bool × Bool × Bool :=
  (decide (1 / 2 < x 0), decide (1 / 2 < x 1), decide (1 / 2 < x 2))

/-- The lower end of the half `[0,1/2]` (`false`) or `[1/2,1]` (`true`) of the unit interval. -/
noncomputable def lo (b : Bool) : ℝ := if b then 1 / 2 else 0

/-- The upper end of the half `[0,1/2]` (`false`) or `[1/2,1]` (`true`) of the unit interval. -/
noncomputable def hi (b : Bool) : ℝ := if b then 1 else 1 / 2

theorem coord_bounds {x : Pt} (hx : InCube x) (c : Fin 3) {b : Bool}
    (h : decide (1 / 2 < x c) = b) : lo b ≤ x c ∧ x c ≤ hi b := by
  cases b
  · have : ¬ 1 / 2 < x c := of_decide_eq_false h
    simp only [lo, hi, Bool.false_eq_true, ↓reduceIte]
    exact ⟨(hx c).1, not_lt.mp this⟩
  · have : 1 / 2 < x c := of_decide_eq_true h
    simp only [lo, hi, ↓reduceIte]
    exact ⟨this.le, (hx c).2⟩

theorem cell_bounds {x : Pt} (hx : InCube x) {a b c : Bool} (h : cell x = (a, b, c)) :
    (lo a ≤ x 0 ∧ x 0 ≤ hi a) ∧ (lo b ≤ x 1 ∧ x 1 ≤ hi b) ∧ (lo c ≤ x 2 ∧ x 2 ≤ hi c) := by
  simp only [cell, Prod.mk.injEq] at h
  exact ⟨coord_bounds hx 0 h.1, coord_bounds hx 1 h.2.1, coord_bounds hx 2 h.2.2⟩

theorem half_sq_le {b : Bool} {s t : ℝ} (hs : lo b ≤ s ∧ s ≤ hi b) (ht : lo b ≤ t ∧ t ≤ hi b) :
    (s - t) ^ 2 ≤ 1 / 4 := by
  have hw : hi b - lo b = 1 / 2 := by cases b <;> norm_num [lo, hi]
  calc (s - t) ^ 2 ≤ (1 / 2) ^ 2 := sq_le_sq' (by linarith [hs.1, hs.2, ht.1, ht.2])
        (by linarith [hs.1, hs.2, ht.1, ht.2])
    _ = 1 / 4 := by norm_num

/-- Two points in the same half-cube are at squared distance at most `3/4`. -/
theorem dist_sq_le_of_cell_eq {x y : Pt} (hx : InCube x) (hy : InCube y) (h : cell x = cell y) :
    dist x y ^ 2 ≤ 3 / 4 := by
  have hc : cell y = ((cell y).1, (cell y).2.1, (cell y).2.2) := rfl
  have bx := cell_bounds hx (h.trans hc)
  have by' := cell_bounds hy hc
  rw [dist_sq]
  have h0 := half_sq_le bx.1 by'.1
  have h1 := half_sq_le bx.2.1 by'.2.1
  have h2 := half_sq_le bx.2.2 by'.2.2
  linarith

/-! ### Nine points -/

theorem exists_dist_le_nine (p : Fin 9 → Pt) (hp : ∀ i, InCube (p i)) :
    ∃ i j, i ≠ j ∧ dist (p i) (p j) ≤ Real.sqrt 3 / 2 := by
  obtain ⟨i, j, hij, h⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun i => cell (p i)) (by simp)
  refine ⟨i, j, hij, dist_le (by positivity) ?_⟩
  have h3 : (Real.sqrt 3 / 2) ^ 2 = 3 / 4 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [h3]
  exact dist_sq_le_of_cell_eq (hp i) (hp j) h

theorem isMaxMinDist_nine : IsMaxMinDist 9 (Real.sqrt 3 / 2) := by
  have h3 : (Real.sqrt 3 / 2) ^ 2 = 3 / 4 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hle : Real.sqrt 3 / 2 ≤ 1 := by
    have : Real.sqrt 3 ≤ 2 := by
      rw [show (2 : ℝ) = Real.sqrt 4 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num)
    linarith
  let e : Fin 8 ≃ (Fin 3 → Bool) := Fintype.equivOfCardEq (by simp)
  refine ⟨⟨Fin.cases centre fun i => corner (e i), ?_, ?_⟩, exists_dist_le_nine⟩
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact inCube_centre
    · exact inCube_corner _
  · intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · intro h
      exact absurd rfl h
    · intro _
      exact le_dist (by
        simp only [Fin.cases_zero, Fin.cases_succ]
        rw [h3, dist_sq_centre_corner])
    · intro _
      exact le_dist (by
        simp only [Fin.cases_zero, Fin.cases_succ]
        rw [h3, dist_comm, dist_sq_centre_corner])
    · intro h
      simp only [Fin.cases_succ]
      have hne : e i ≠ e j := fun h' => h (congrArg Fin.succ (e.injective h'))
      exact hle.trans (one_le_dist_corner hne)

/-! ### Eight points -/

/-- The inequality behind `N = 8`, for one coordinate. The numbers `s i` lie in one half of the
unit interval and the `t i` in the other; the twelve squared differences along the edges of the
cube graph (four between the halves, four around each half) sum to at most `4`. -/
theorem edge_sum_le {s0 s1 s2 s3 t0 t1 t2 t3 : ℝ}
    (hs0 : lo false ≤ s0 ∧ s0 ≤ hi false) (hs1 : lo false ≤ s1 ∧ s1 ≤ hi false)
    (hs2 : lo false ≤ s2 ∧ s2 ≤ hi false) (hs3 : lo false ≤ s3 ∧ s3 ≤ hi false)
    (ht0 : lo true ≤ t0 ∧ t0 ≤ hi true) (ht1 : lo true ≤ t1 ∧ t1 ≤ hi true)
    (ht2 : lo true ≤ t2 ∧ t2 ≤ hi true) (ht3 : lo true ≤ t3 ∧ t3 ≤ hi true) :
    (t0 - s0) ^ 2 + (t1 - s1) ^ 2 + (t2 - s2) ^ 2 + (t3 - s3) ^ 2
      + (s0 - s1) ^ 2 + (s1 - s2) ^ 2 + (s2 - s3) ^ 2 + (s3 - s0) ^ 2
      + (t0 - t1) ^ 2 + (t1 - t2) ^ 2 + (t2 - t3) ^ 2 + (t3 - t0) ^ 2 ≤ 4 := by
  simp only [lo, hi, Bool.false_eq_true, ↓reduceIte] at hs0 hs1 hs2 hs3 ht0 ht1 ht2 ht3
  -- `a i = 1 - 2 s i` and `b i = 2 t i - 1` lie in `[0,1]`
  have a0 : 0 ≤ 1 - 2 * s0 := by linarith [hs0.2]
  have a1 : 0 ≤ 1 - 2 * s1 := by linarith [hs1.2]
  have a2 : 0 ≤ 1 - 2 * s2 := by linarith [hs2.2]
  have a3 : 0 ≤ 1 - 2 * s3 := by linarith [hs3.2]
  have a0' : 0 ≤ 2 * s0 := by linarith [hs0.1]
  have a1' : 0 ≤ 2 * s1 := by linarith [hs1.1]
  have a2' : 0 ≤ 2 * s2 := by linarith [hs2.1]
  have a3' : 0 ≤ 2 * s3 := by linarith [hs3.1]
  have b0 : 0 ≤ 2 * t0 - 1 := by linarith [ht0.1]
  have b1 : 0 ≤ 2 * t1 - 1 := by linarith [ht1.1]
  have b2 : 0 ≤ 2 * t2 - 1 := by linarith [ht2.1]
  have b3 : 0 ≤ 2 * t3 - 1 := by linarith [ht3.1]
  have b0' : 0 ≤ 2 - 2 * t0 := by linarith [ht0.2]
  have b1' : 0 ≤ 2 - 2 * t1 := by linarith [ht1.2]
  have b2' : 0 ≤ 2 - 2 * t2 := by linarith [ht2.2]
  have b3' : 0 ≤ 2 - 2 * t3 := by linarith [ht3.2]
  nlinarith [mul_nonneg a0 a0', mul_nonneg a1 a1', mul_nonneg a2 a2', mul_nonneg a3 a3',
    mul_nonneg b0 b0', mul_nonneg b1 b1', mul_nonneg b2 b2', mul_nonneg b3 b3',
    mul_nonneg a0' a1', mul_nonneg a1' a2', mul_nonneg a2' a3', mul_nonneg a3' a0',
    mul_nonneg b0' b1', mul_nonneg b1' b2', mul_nonneg b2' b3', mul_nonneg b3' b0',
    mul_nonneg a0 b0', mul_nonneg a1 b1', mul_nonneg a2 b2', mul_nonneg a3 b3',
    mul_nonneg b0 a0', mul_nonneg b1 a1', mul_nonneg b2 a2', mul_nonneg b3 a3']

/-- Eight points, one in each half-cube, cannot all be at distance more than `1`: the twelve
pairs in half-cubes that share a face have squared distances summing to at most `12`. -/
theorem no_separated_cells (q : Bool × Bool × Bool → Pt)
    (B : ∀ a b c, (lo a ≤ q (a, b, c) 0 ∧ q (a, b, c) 0 ≤ hi a)
      ∧ (lo b ≤ q (a, b, c) 1 ∧ q (a, b, c) 1 ≤ hi b)
      ∧ (lo c ≤ q (a, b, c) 2 ∧ q (a, b, c) 2 ≤ hi c))
    (S : ∀ v w, v ≠ w →
      1 < (q v 0 - q w 0) ^ 2 + (q v 1 - q w 1) ^ 2 + (q v 2 - q w 2) ^ 2) : False := by
  have x1 := S (false, false, false) (true, false, false) (by simp)
  have x2 := S (false, false, true) (true, false, true) (by simp)
  have x3 := S (false, true, true) (true, true, true) (by simp)
  have x4 := S (false, true, false) (true, true, false) (by simp)
  have y1 := S (false, false, false) (false, true, false) (by simp)
  have y2 := S (false, false, true) (false, true, true) (by simp)
  have y3 := S (true, false, true) (true, true, true) (by simp)
  have y4 := S (true, false, false) (true, true, false) (by simp)
  have z1 := S (false, false, false) (false, false, true) (by simp)
  have z2 := S (false, true, false) (false, true, true) (by simp)
  have z3 := S (true, true, false) (true, true, true) (by simp)
  have z4 := S (true, false, false) (true, false, true) (by simp)
  have E0 := edge_sum_le (B false false false).1 (B false false true).1 (B false true true).1
    (B false true false).1 (B true false false).1 (B true false true).1 (B true true true).1
    (B true true false).1
  have E1 := edge_sum_le (B false false false).2.1 (B false false true).2.1
    (B true false true).2.1 (B true false false).2.1 (B false true false).2.1
    (B false true true).2.1 (B true true true).2.1 (B true true false).2.1
  have E2 := edge_sum_le (B false false false).2.2 (B false true false).2.2
    (B true true false).2.2 (B true false false).2.2 (B false false true).2.2
    (B false true true).2.2 (B true true true).2.2 (B true false true).2.2
  linarith

theorem exists_dist_le_eight (p : Fin 8 → Pt) (hp : ∀ i, InCube (p i)) :
    ∃ i j, i ≠ j ∧ dist (p i) (p j) ≤ 1 := by
  by_contra hcon
  push Not at hcon
  -- no two points share a half-cube, so each of the eight half-cubes holds exactly one point
  have hinj : Function.Injective fun i => cell (p i) := by
    intro i j h
    by_contra hij
    have h1 := one_lt_dist_sq (hcon i j hij)
    have h2 := dist_sq_le_of_cell_eq (hp i) (hp j) h
    linarith
  have hbij : Function.Bijective fun i => cell (p i) :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, by simp⟩
  let e := Equiv.ofBijective _ hbij
  refine no_separated_cells (fun v => p (e.symm v))
    (fun a b c => cell_bounds (hp _) (e.apply_symm_apply (a, b, c))) fun v w hvw => ?_
  rw [← dist_sq]
  exact one_lt_dist_sq (hcon _ _ fun h => hvw (e.symm.injective h))

theorem isMaxMinDist_eight : IsMaxMinDist 8 1 := by
  let e : Fin 8 ≃ (Fin 3 → Bool) := Fintype.equivOfCardEq (by simp)
  refine ⟨⟨fun i => corner (e i), fun i => inCube_corner _, fun i j hij => ?_⟩,
    exists_dist_le_eight⟩
  exact one_le_dist_corner fun h => hij (e.injective h)

end Packing.Cube
