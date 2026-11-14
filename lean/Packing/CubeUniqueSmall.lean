/-
The best arrangements of three and of four points in the unit cube are unique.

Four points pairwise at distance at least `sqrt 2` are the corners of one of the two regular
tetrahedra inscribed in the cube (`isUniqueMaxMinDist_four`), and three such points are three
corners of one of them (`isUniqueMaxMinDist_three`).

The value proofs bound the sum of the squared differences in each coordinate. Here the bound
is attained in every coordinate, which forces every coordinate of every point to be `0` or `1`
(`three_sq_eq`, `four_sq_eq`). Reflecting the cube so that the first point is the origin, the
other points are corners at squared distance `2` from it, that is, corners with two
coordinates equal to `1`.
-/
import Packing.CubeUnique

set_option linter.unusedVariables false

namespace Packing.Cube

/-! ### From a pointwise match to a permutation -/

/-- If every arrangement with pairwise distances at least `d > 0` consists of images of points
of `q` under one symmetry of the cube, it is the image of `q` in some order. -/
theorem isUniqueUpToCubeSymm_of_exists {N : ℕ} {d : ℝ} {q : Fin N → Pt} (hd : 0 < d)
    (h : ∀ p : Fin N → Pt, (∀ i, InCube (p i)) → (∀ i j, i ≠ j → d ≤ dist (p i) (p j)) →
      ∃ (v : Fin 3 → Bool) (σ : Equiv.Perm (Fin 3)), ∀ i, ∃ m, p i = cubeSymm v σ (q m)) :
    IsUniqueUpToCubeSymm N d q := by
  intro p hp hpd
  obtain ⟨v, σ, hm⟩ := h p hp hpd
  choose e he using hm
  have hinj : Function.Injective e := by
    intro i j hij
    by_contra hne
    have h1 := hpd i j hne
    rw [he i, he j, hij, dist_self] at h1
    linarith
  exact ⟨v, σ, Equiv.ofBijective e (Finite.injective_iff_bijective.mp hinj), he⟩

/-! ### Where the coordinate bounds are attained -/

theorem zero_or_one {a : ℝ} (h : a * (1 - a) = 0) : a = 0 ∨ a = 1 := by
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (by linarith)

/-- Three numbers in `[0,1]` whose squared differences sum to at least `2` are `0` or `1`. -/
theorem three_sq_eq {a b c : ℝ} (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) (hc : 0 ≤ c ∧ c ≤ 1)
    (h : 2 ≤ (a - b) ^ 2 + (a - c) ^ 2 + (b - c) ^ 2) :
    (a = 0 ∨ a = 1) ∧ (b = 0 ∨ b = 1) ∧ (c = 0 ∨ c = 1) := by
  have ta := mul_nonneg ha.1 (sub_nonneg.mpr ha.2)
  have tb := mul_nonneg hb.1 (sub_nonneg.mpr hb.2)
  have tc := mul_nonneg hc.1 (sub_nonneg.mpr hc.2)
  have t4 := mul_nonneg (mul_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr hb.2))
    (sub_nonneg.mpr hc.2)
  have t5 := mul_nonneg (mul_nonneg ha.1 hb.1) hc.1
  exact ⟨zero_or_one (le_antisymm (by linarith) ta), zero_or_one (le_antisymm (by linarith) tb),
    zero_or_one (le_antisymm (by linarith) tc)⟩

/-- Four numbers in `[0,1]` whose squared differences sum to at least `4` are `0` or `1`. -/
theorem four_sq_eq {a b c d : ℝ} (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1)
    (hc : 0 ≤ c ∧ c ≤ 1) (hd : 0 ≤ d ∧ d ≤ 1)
    (h : 4 ≤ (a - b) ^ 2 + (a - c) ^ 2 + (a - d) ^ 2 + (b - c) ^ 2 + (b - d) ^ 2 + (c - d) ^ 2) :
    (a = 0 ∨ a = 1) ∧ (b = 0 ∨ b = 1) ∧ (c = 0 ∨ c = 1) ∧ (d = 0 ∨ d = 1) := by
  have ta := mul_nonneg ha.1 (sub_nonneg.mpr ha.2)
  have tb := mul_nonneg hb.1 (sub_nonneg.mpr hb.2)
  have tc := mul_nonneg hc.1 (sub_nonneg.mpr hc.2)
  have td := mul_nonneg hd.1 (sub_nonneg.mpr hd.2)
  have ts := sq_nonneg (a + b + c + d - 2)
  exact ⟨zero_or_one (le_antisymm (by linarith) ta), zero_or_one (le_antisymm (by linarith) tb),
    zero_or_one (le_antisymm (by linarith) tc), zero_or_one (le_antisymm (by linarith) td)⟩

/-! ### Points with coordinates `0` and `1` -/

theorem pt_ext {x y : Pt} (h0 : x 0 = y 0) (h1 : x 1 = y 1) (h2 : x 2 = y 2) : x = y := by
  ext c
  fin_cases c
  · exact h0
  · exact h1
  · exact h2

/-- Every coordinate of `x` is `0` or `1`. -/
def Binary (x : Pt) : Prop := ∀ c, x c = 0 ∨ x c = 1

/-- The reflections that move the corner `y` to the origin. -/
noncomputable def refl (y : Pt) : Fin 3 → Bool := fun c => decide (y c = 1)

theorem refl_apply (y x : Pt) (c : Fin 3) :
    cubeSymm (refl y) 1 x c = if y c = 1 then 1 - x c else x c := by
  rw [cubeSymm_apply]
  simp [refl]

theorem binary_refl {x : Pt} (y : Pt) (hx : Binary x) : Binary (cubeSymm (refl y) 1 x) := by
  intro c
  rw [refl_apply]
  rcases hx c with h | h <;> split_ifs <;> simp [h]

theorem sq_sub_eq_refl {x y : Pt} (hx : Binary x) (hy : Binary y) (c : Fin 3) :
    (x c - y c) ^ 2 = cubeSymm (refl y) 1 x c := by
  rw [refl_apply]
  rcases hx c with h | h <;> rcases hy c with h' | h' <;> simp [h, h']

/-- After the reflection the coordinates of `x` sum to its squared distance from `y`. -/
theorem sum_refl {x y : Pt} (hx : Binary x) (hy : Binary y) :
    cubeSymm (refl y) 1 x 0 + cubeSymm (refl y) 1 x 1 + cubeSymm (refl y) 1 x 2
      = dist x y ^ 2 := by
  rw [dist_sq, sq_sub_eq_refl hx hy 0, sq_sub_eq_refl hx hy 1, sq_sub_eq_refl hx hy 2]

theorem cubeSymm_one_one (v : Fin 3 → Bool) (x : Pt) : cubeSymm v 1 (cubeSymm v 1 x) = x := by
  ext c
  simp only [cubeSymm_apply, Equiv.Perm.one_apply]
  split_ifs <;> ring

theorem cubeSymm_one_false (v : Fin 3 → Bool) (σ : Equiv.Perm (Fin 3)) (x : Pt) :
    cubeSymm v 1 (cubeSymm (fun _ => false) σ x) = cubeSymm v σ x := by
  ext c
  simp [cubeSymm_apply]

theorem cubeSymm_false_corner (σ : Equiv.Perm (Fin 3)) (w : Fin 3 → Bool) :
    cubeSymm (fun _ => false) σ (corner w) = corner (w ∘ σ) := by
  ext c
  simp [cubeSymm_apply, corner_apply]

/-- If the reflected point is the image of `y` under a permutation of the coordinates, the
point is the image of `y` under a symmetry of the cube. -/
theorem eq_cubeSymm_of_refl {v : Fin 3 → Bool} {σ : Equiv.Perm (Fin 3)} {x y : Pt}
    (h : cubeSymm v 1 x = cubeSymm (fun _ => false) σ y) : x = cubeSymm v σ y := by
  rw [← cubeSymm_one_false, ← h, cubeSymm_one_one]

/-- A point with coordinates `0` and `1` that sum to `0` is the origin. -/
theorem even_zero {z : Pt} (hz : Binary z) (hs : z 0 + z 1 + z 2 = 0) :
    z = corner (evenCorner 0) := by
  rcases hz 0 with h0 | h0 <;> rcases hz 1 with h1 | h1 <;> rcases hz 2 with h2 | h2
  · exact pt_ext (by rw [h0, corner_apply]; simp [evenCorner])
      (by rw [h1, corner_apply]; simp [evenCorner]) (by rw [h2, corner_apply]; simp [evenCorner])
  · exfalso; linarith
  · exfalso; linarith
  · exfalso; linarith
  · exfalso; linarith
  · exfalso; linarith
  · exfalso; linarith
  · exfalso; linarith

/-- A point with coordinates `0` and `1` that sum to `2` is one of the three corners with two
coordinates equal to `1`. -/
theorem even_two {z : Pt} (hz : Binary z) (hs : z 0 + z 1 + z 2 = 2) :
    z = corner (evenCorner 1) ∨ z = corner (evenCorner 2) ∨ z = corner (evenCorner 3) := by
  rcases hz 0 with h0 | h0 <;> rcases hz 1 with h1 | h1 <;> rcases hz 2 with h2 | h2
  · exfalso; linarith
  · exfalso; linarith
  · exfalso; linarith
  · exact Or.inr (Or.inr (pt_ext (by rw [h0, corner_apply]; simp [evenCorner])
      (by rw [h1, corner_apply]; simp [evenCorner]) (by rw [h2, corner_apply]; simp [evenCorner])))
  · exfalso; linarith
  · exact Or.inr (Or.inl (pt_ext (by rw [h0, corner_apply]; simp [evenCorner])
      (by rw [h1, corner_apply]; simp [evenCorner]) (by rw [h2, corner_apply]; simp [evenCorner])))
  · exact Or.inl (pt_ext (by rw [h0, corner_apply]; simp [evenCorner])
      (by rw [h1, corner_apply]; simp [evenCorner]) (by rw [h2, corner_apply]; simp [evenCorner]))
  · exfalso; linarith

/-! ### Four points -/

/-- The corners of a regular tetrahedron inscribed in the cube. -/
noncomputable def four : Fin 4 → Pt := fun i => corner (evenCorner i)

theorem fin_four : ∀ i : Fin 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide

theorem isUniqueUpToCubeSymm_four : IsUniqueUpToCubeSymm 4 (Real.sqrt 2) four := by
  apply isUniqueUpToCubeSymm_of_exists (Real.sqrt_pos.mpr (by norm_num))
  intro p hp hd
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsq : ∀ i j, i ≠ j → 2 ≤ dist (p i) (p j) ^ 2 := by
    intro i j hij
    have h := pow_le_pow_left₀ (Real.sqrt_nonneg 2) (hd i j hij) 2
    rwa [h2] at h
  have d01 := hsq 0 1 (by decide)
  have d02 := hsq 0 2 (by decide)
  have d03 := hsq 0 3 (by decide)
  have d12 := hsq 1 2 (by decide)
  have d13 := hsq 1 3 (by decide)
  have d23 := hsq 2 3 (by decide)
  rw [dist_sq] at d01 d02 d03 d12 d13 d23
  have e0 := four_sq_le (hp 0 0) (hp 1 0) (hp 2 0) (hp 3 0)
  have e1 := four_sq_le (hp 0 1) (hp 1 1) (hp 2 1) (hp 3 1)
  have e2 := four_sq_le (hp 0 2) (hp 1 2) (hp 2 2) (hp 3 2)
  have b0 := four_sq_eq (hp 0 0) (hp 1 0) (hp 2 0) (hp 3 0) (by linarith)
  have b1 := four_sq_eq (hp 0 1) (hp 1 1) (hp 2 1) (hp 3 1) (by linarith)
  have b2 := four_sq_eq (hp 0 2) (hp 1 2) (hp 2 2) (hp 3 2) (by linarith)
  have k3 : ∀ c : Fin 3, c = 0 ∨ c = 1 ∨ c = 2 := by decide
  have hbin : ∀ i, Binary (p i) := by
    intro i c
    rcases fin_four i with rfl | rfl | rfl | rfl <;> rcases k3 c with rfl | rfl | rfl
    · exact b0.1
    · exact b1.1
    · exact b2.1
    · exact b0.2.1
    · exact b1.2.1
    · exact b2.2.1
    · exact b0.2.2.1
    · exact b1.2.2.1
    · exact b2.2.2.1
    · exact b0.2.2.2
    · exact b1.2.2.2
    · exact b2.2.2.2
  have t1 : dist (p 1) (p 0) ^ 2 = 2 := by
    rw [dist_sq]
    linarith
  have t2 : dist (p 2) (p 0) ^ 2 = 2 := by
    rw [dist_sq]
    linarith
  have t3 : dist (p 3) (p 0) ^ 2 = 2 := by
    rw [dist_sq]
    linarith
  refine ⟨refl (p 0), 1, fun i => ?_⟩
  have hz := binary_refl (p 0) (hbin i)
  have hs := sum_refl (hbin i) (hbin 0)
  have hm : ∃ m, cubeSymm (refl (p 0)) 1 (p i) = four m := by
    rcases fin_four i with rfl | rfl | rfl | rfl
    · rw [dist_self] at hs
      exact ⟨0, even_zero hz (by rw [hs]; norm_num)⟩
    · rw [t1] at hs
      rcases even_two hz hs with h | h | h
      · exact ⟨1, h⟩
      · exact ⟨2, h⟩
      · exact ⟨3, h⟩
    · rw [t2] at hs
      rcases even_two hz hs with h | h | h
      · exact ⟨1, h⟩
      · exact ⟨2, h⟩
      · exact ⟨3, h⟩
    · rw [t3] at hs
      rcases even_two hz hs with h | h | h
      · exact ⟨1, h⟩
      · exact ⟨2, h⟩
      · exact ⟨3, h⟩
  obtain ⟨m, hm⟩ := hm
  exact ⟨m, by rw [← hm, cubeSymm_one_one]⟩

theorem inCube_four (i : Fin 4) : InCube (four i) := inCube_corner _

theorem dist_four {i j : Fin 4} (h : i ≠ j) : Real.sqrt 2 ≤ dist (four i) (four j) := by
  apply le_dist
  rw [Real.sq_sqrt (by norm_num)]
  exact (dist_sq_evenCorner h).ge

/-- The corners of an inscribed regular tetrahedron are the unique best arrangement of four
points in the unit cube, up to the symmetries of the cube. -/
theorem isUniqueMaxMinDist_four : IsUniqueMaxMinDist 4 (Real.sqrt 2) four :=
  ⟨inCube_four, fun _ _ h => dist_four h, exists_dist_le_four, isUniqueUpToCubeSymm_four⟩

/-! ### Three points -/

/-- Three corners of a regular tetrahedron inscribed in the cube. -/
noncomputable def three : Fin 3 → Pt := fun i => corner (evenCorner (Fin.castSucc i))

theorem three_perm (σ : Equiv.Perm (Fin 3)) (m : Fin 3) (k : Fin 4)
    (h : evenCorner (Fin.castSucc m) ∘ σ = evenCorner k) :
    cubeSymm (fun _ => false) σ (three m) = corner (evenCorner k) := by
  unfold three
  rw [cubeSymm_false_corner, h]

theorem fin_three : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide

theorem isUniqueUpToCubeSymm_three : IsUniqueUpToCubeSymm 3 (Real.sqrt 2) three := by
  apply isUniqueUpToCubeSymm_of_exists (Real.sqrt_pos.mpr (by norm_num))
  intro p hp hd
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsq : ∀ i j, i ≠ j → 2 ≤ dist (p i) (p j) ^ 2 := by
    intro i j hij
    have h := pow_le_pow_left₀ (Real.sqrt_nonneg 2) (hd i j hij) 2
    rwa [h2] at h
  have d01 := hsq 0 1 (by decide)
  have d02 := hsq 0 2 (by decide)
  have d12 := hsq 1 2 (by decide)
  have g12 := d12
  rw [dist_sq] at d01 d02 d12
  have e0 := three_sq_le (hp 0 0) (hp 1 0) (hp 2 0)
  have e1 := three_sq_le (hp 0 1) (hp 1 1) (hp 2 1)
  have e2 := three_sq_le (hp 0 2) (hp 1 2) (hp 2 2)
  have b0 := three_sq_eq (hp 0 0) (hp 1 0) (hp 2 0) (by linarith)
  have b1 := three_sq_eq (hp 0 1) (hp 1 1) (hp 2 1) (by linarith)
  have b2 := three_sq_eq (hp 0 2) (hp 1 2) (hp 2 2) (by linarith)
  have hbin : ∀ i, Binary (p i) := by
    intro i c
    rcases fin_three i with rfl | rfl | rfl <;> rcases fin_three c with rfl | rfl | rfl
    · exact b0.1
    · exact b1.1
    · exact b2.1
    · exact b0.2.1
    · exact b1.2.1
    · exact b2.2.1
    · exact b0.2.2
    · exact b1.2.2
    · exact b2.2.2
  have t1 : dist (p 1) (p 0) ^ 2 = 2 := by
    rw [dist_sq]
    linarith
  have t2 : dist (p 2) (p 0) ^ 2 = 2 := by
    rw [dist_sq]
    linarith
  -- the reflected points
  have z0 : cubeSymm (refl (p 0)) 1 (p 0) = corner (evenCorner 0) := by
    have hs := sum_refl (hbin 0) (hbin 0)
    rw [dist_self] at hs
    exact even_zero (binary_refl (p 0) (hbin 0)) (by rw [hs]; norm_num)
  have z1 := even_two (binary_refl (p 0) (hbin 1)) (by rw [sum_refl (hbin 1) (hbin 0), t1])
  have z2 := even_two (binary_refl (p 0) (hbin 2)) (by rw [sum_refl (hbin 2) (hbin 0), t2])
  have hne : cubeSymm (refl (p 0)) 1 (p 1) ≠ cubeSymm (refl (p 0)) 1 (p 2) := by
    intro h
    have hd' := dist_cubeSymm (refl (p 0)) 1 (p 1) (p 2)
    rw [h, dist_self] at hd'
    rw [← hd'] at g12
    norm_num at g12
  have c0 : ∀ σ : Equiv.Perm (Fin 3), cubeSymm (fun _ => false) σ (three 0)
      = corner (evenCorner 0) := by
    intro σ
    have h : evenCorner 0 = fun _ => false := by decide
    exact three_perm σ 0 0 (by
      show evenCorner 0 ∘ σ = evenCorner 0
      rw [h]
      rfl)
  -- which two of the three corners occur decides the permutation of the coordinates
  rcases z1 with z1 | z1 | z1 <;> rcases z2 with z2 | z2 | z2
  · exact absurd (z1.trans z2.symm) hne
  · refine ⟨refl (p 0), 1, fun i => ?_⟩
    rcases fin_three i with rfl | rfl | rfl
    · exact ⟨0, eq_cubeSymm_of_refl (z0.trans (c0 1).symm)⟩
    · exact ⟨1, eq_cubeSymm_of_refl (z1.trans (three_perm 1 1 1 (by decide)).symm)⟩
    · exact ⟨2, eq_cubeSymm_of_refl (z2.trans (three_perm 1 2 2 (by decide)).symm)⟩
  · refine ⟨refl (p 0), Equiv.swap 0 1, fun i => ?_⟩
    rcases fin_three i with rfl | rfl | rfl
    · exact ⟨0, eq_cubeSymm_of_refl (z0.trans (c0 _).symm)⟩
    · exact ⟨1, eq_cubeSymm_of_refl (z1.trans (three_perm _ 1 1 (by decide)).symm)⟩
    · exact ⟨2, eq_cubeSymm_of_refl (z2.trans (three_perm _ 2 3 (by decide)).symm)⟩
  · refine ⟨refl (p 0), 1, fun i => ?_⟩
    rcases fin_three i with rfl | rfl | rfl
    · exact ⟨0, eq_cubeSymm_of_refl (z0.trans (c0 1).symm)⟩
    · exact ⟨2, eq_cubeSymm_of_refl (z1.trans (three_perm 1 2 2 (by decide)).symm)⟩
    · exact ⟨1, eq_cubeSymm_of_refl (z2.trans (three_perm 1 1 1 (by decide)).symm)⟩
  · exact absurd (z1.trans z2.symm) hne
  · refine ⟨refl (p 0), Equiv.swap 0 2, fun i => ?_⟩
    rcases fin_three i with rfl | rfl | rfl
    · exact ⟨0, eq_cubeSymm_of_refl (z0.trans (c0 _).symm)⟩
    · exact ⟨2, eq_cubeSymm_of_refl (z1.trans (three_perm _ 2 2 (by decide)).symm)⟩
    · exact ⟨1, eq_cubeSymm_of_refl (z2.trans (three_perm _ 1 3 (by decide)).symm)⟩
  · refine ⟨refl (p 0), Equiv.swap 0 1, fun i => ?_⟩
    rcases fin_three i with rfl | rfl | rfl
    · exact ⟨0, eq_cubeSymm_of_refl (z0.trans (c0 _).symm)⟩
    · exact ⟨2, eq_cubeSymm_of_refl (z1.trans (three_perm _ 2 3 (by decide)).symm)⟩
    · exact ⟨1, eq_cubeSymm_of_refl (z2.trans (three_perm _ 1 1 (by decide)).symm)⟩
  · refine ⟨refl (p 0), Equiv.swap 0 2, fun i => ?_⟩
    rcases fin_three i with rfl | rfl | rfl
    · exact ⟨0, eq_cubeSymm_of_refl (z0.trans (c0 _).symm)⟩
    · exact ⟨1, eq_cubeSymm_of_refl (z1.trans (three_perm _ 1 3 (by decide)).symm)⟩
    · exact ⟨2, eq_cubeSymm_of_refl (z2.trans (three_perm _ 2 2 (by decide)).symm)⟩
  · exact absurd (z1.trans z2.symm) hne

theorem inCube_three (i : Fin 3) : InCube (three i) := inCube_corner _

theorem dist_three {i j : Fin 3} (h : i ≠ j) : Real.sqrt 2 ≤ dist (three i) (three j) := by
  apply le_dist
  rw [Real.sq_sqrt (by norm_num)]
  have hne : Fin.castSucc i ≠ Fin.castSucc j := fun h' => h (Fin.castSucc_injective 3 h')
  exact (dist_sq_evenCorner hne).ge

/-- Three corners of an inscribed regular tetrahedron are the unique best arrangement of three
points in the unit cube, up to the symmetries of the cube. -/
theorem isUniqueMaxMinDist_three : IsUniqueMaxMinDist 3 (Real.sqrt 2) three :=
  ⟨inCube_three, fun _ _ h => dist_three h, exists_dist_le_three, isUniqueUpToCubeSymm_three⟩

end Packing.Cube
