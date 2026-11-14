/-
Two ways to say that an optimal arrangement of `N` points in the unit cube is unique.

`IsUniqueUpToCubeSymm N d q`: every arrangement of `N` points of the cube with pairwise
distances at least `d` is the image of `q` under one of the 48 symmetries of the cube, with
the points taken in some order.

`IsUniqueUpToIsometry N d q`: the same with any isometry of space in place of a symmetry of
the cube.

The first is the stronger statement: it implies the second
(`IsUniqueUpToCubeSymm.toIsometry`), because every symmetry of the cube is an isometry.
-/
import Packing.Cube

namespace Packing.Cube

/-- The symmetry of the unit cube that permutes the coordinates by `σ` and then reflects the
coordinates where `v` is `true`. -/
noncomputable def cubeSymm (v : Fin 3 → Bool) (σ : Equiv.Perm (Fin 3)) (x : Pt) : Pt :=
  WithLp.toLp 2 fun c => if v c then 1 - x (σ c) else x (σ c)

theorem cubeSymm_apply (v : Fin 3 → Bool) (σ : Equiv.Perm (Fin 3)) (x : Pt) (c : Fin 3) :
    cubeSymm v σ x c = if v c then 1 - x (σ c) else x (σ c) := rfl

theorem inCube_cubeSymm (v : Fin 3 → Bool) (σ : Equiv.Perm (Fin 3)) {x : Pt} (hx : InCube x) :
    InCube (cubeSymm v σ x) := by
  intro c
  have h := hx (σ c)
  rw [cubeSymm_apply]
  split_ifs <;> constructor <;> linarith [h.1, h.2]

theorem dist_cubeSymm (v : Fin 3 → Bool) (σ : Equiv.Perm (Fin 3)) (x y : Pt) :
    dist (cubeSymm v σ x) (cubeSymm v σ y) = dist x y := by
  have h : dist (cubeSymm v σ x) (cubeSymm v σ y) ^ 2 = dist x y ^ 2 := by
    rw [dist_sq, dist_sq, ← Fin.sum_univ_three fun c => (cubeSymm v σ x c - cubeSymm v σ y c) ^ 2,
      ← Fin.sum_univ_three fun c => (x c - y c) ^ 2, ← Equiv.sum_comp σ fun c => (x c - y c) ^ 2]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [cubeSymm_apply]
    split_ifs <;> ring
  exact (sq_eq_sq₀ dist_nonneg dist_nonneg).mp h

theorem isometry_cubeSymm (v : Fin 3 → Bool) (σ : Equiv.Perm (Fin 3)) :
    Isometry (cubeSymm v σ) :=
  Isometry.of_dist_eq (dist_cubeSymm v σ)

/-- Every arrangement of `N` points of the unit cube with pairwise distances at least `d` is
the image of `q`, in some order, under a symmetry of the cube. -/
def IsUniqueUpToCubeSymm (N : ℕ) (d : ℝ) (q : Fin N → Pt) : Prop :=
  ∀ p : Fin N → Pt, (∀ i, InCube (p i)) → (∀ i j, i ≠ j → d ≤ dist (p i) (p j)) →
    ∃ (v : Fin 3 → Bool) (σ : Equiv.Perm (Fin 3)) (e : Equiv.Perm (Fin N)),
      ∀ i, p i = cubeSymm v σ (q (e i))

/-- Every arrangement of `N` points of the unit cube with pairwise distances at least `d` is
the image of `q`, in some order, under an isometry of space. -/
def IsUniqueUpToIsometry (N : ℕ) (d : ℝ) (q : Fin N → Pt) : Prop :=
  ∀ p : Fin N → Pt, (∀ i, InCube (p i)) → (∀ i j, i ≠ j → d ≤ dist (p i) (p j)) →
    ∃ (f : Pt → Pt) (e : Equiv.Perm (Fin N)), Isometry f ∧ ∀ i, p i = f (q (e i))

theorem IsUniqueUpToCubeSymm.toIsometry {N : ℕ} {d : ℝ} {q : Fin N → Pt}
    (h : IsUniqueUpToCubeSymm N d q) : IsUniqueUpToIsometry N d q := by
  intro p hp hd
  obtain ⟨v, σ, e, he⟩ := h p hp hd
  exact ⟨cubeSymm v σ, e, isometry_cubeSymm v σ, he⟩

/-- Both statements hold for every `q` when no arrangement is feasible, so on their own they
do not say that `d` is attained. `IsUniqueMaxMinDist` adds that. -/
theorem isUniqueUpToCubeSymm_of_infeasible {N : ℕ} {d : ℝ} (q : Fin N → Pt)
    (h : ∀ p : Fin N → Pt, (∀ i, InCube (p i)) → ¬ ∀ i j, i ≠ j → d ≤ dist (p i) (p j)) :
    IsUniqueUpToCubeSymm N d q :=
  fun p hp hd => absurd hd (h p hp)

/-- `q` is an arrangement of `N` points of the unit cube with pairwise distances at least `d`,
any `N` points of the cube include two at distance at most `d`, and every arrangement with
pairwise distances at least `d` is the image of `q`, in some order, under a symmetry of the
cube. -/
def IsUniqueMaxMinDist (N : ℕ) (d : ℝ) (q : Fin N → Pt) : Prop :=
  (∀ i, InCube (q i)) ∧ (∀ i j, i ≠ j → d ≤ dist (q i) (q j)) ∧
    (∀ p : Fin N → Pt, (∀ i, InCube (p i)) → ∃ i j, i ≠ j ∧ dist (p i) (p j) ≤ d) ∧
    IsUniqueUpToCubeSymm N d q

theorem IsUniqueMaxMinDist.isMaxMinDist {N : ℕ} {d : ℝ} {q : Fin N → Pt}
    (h : IsUniqueMaxMinDist N d q) : IsMaxMinDist N d :=
  ⟨⟨q, h.1, h.2.1⟩, h.2.2.1⟩

/-- The congruence form: every optimal arrangement is the image of `q` under an isometry of
space. -/
theorem IsUniqueMaxMinDist.toIsometry {N : ℕ} {d : ℝ} {q : Fin N → Pt}
    (h : IsUniqueMaxMinDist N d q) : IsUniqueUpToIsometry N d q :=
  h.2.2.2.toIsometry

/-! ### Checks of the definitions on two points -/

/-- Two opposite corners of the cube. -/
noncomputable def oppositeCorners : Fin 2 → Pt := fun i => corner fun _ => decide (i = 1)

/-- The definitions are not vacuous: at `d = 0` two points of the cube can coincide, and then
they are not an image of two opposite corners. -/
theorem not_isUniqueUpToIsometry_zero : ¬ IsUniqueUpToIsometry 2 0 oppositeCorners := by
  intro h
  obtain ⟨f, e, hf, he⟩ := h (fun _ => centre) (fun _ => inCube_centre) (fun _ _ _ => dist_nonneg)
  have hd : dist (f (oppositeCorners (e 0))) (f (oppositeCorners (e 1))) = 0 := by
    rw [← he 0, ← he 1, dist_self]
  rw [hf.dist_eq] at hd
  have key : ∀ a b : Fin 2, a ≠ b →
      (fun _ : Fin 3 => decide (a = 1)) ≠ fun _ => decide (b = 1) := by decide
  have hne : e 0 ≠ e 1 := fun h => absurd (e.injective h) (by decide)
  have h1 := one_le_dist_corner (key (e 0) (e 1) hne)
  unfold oppositeCorners at hd
  linarith

theorem not_isUniqueUpToCubeSymm_zero : ¬ IsUniqueUpToCubeSymm 2 0 oppositeCorners :=
  fun h => not_isUniqueUpToIsometry_zero h.toIsometry

theorem inCube_oppositeCorners (i : Fin 2) : InCube (oppositeCorners i) := inCube_corner _

theorem dist_oppositeCorners {i j : Fin 2} (h : i ≠ j) :
    Real.sqrt 3 ≤ dist (oppositeCorners i) (oppositeCorners j) := by
  apply le_dist
  rw [Real.sq_sqrt (by norm_num)]
  unfold oppositeCorners
  rw [dist_sq_corner]
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl h | norm_num

/-- Two points of the cube at distance at least `sqrt 3` are two opposite corners. -/
theorem isUniqueUpToCubeSymm_two : IsUniqueUpToCubeSymm 2 (Real.sqrt 3) oppositeCorners := by
  intro p hp hd
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsq : 3 ≤ dist (p 0) (p 1) ^ 2 := by
    have h := pow_le_pow_left₀ (Real.sqrt_nonneg 3) (hd 0 1 (by decide)) 2
    rwa [h3] at h
  rw [dist_sq] at hsq
  have b0 := coord_sq_le_one (hp 0) (hp 1) 0
  have b1 := coord_sq_le_one (hp 0) (hp 1) 1
  have b2 := coord_sq_le_one (hp 0) (hp 1) 2
  have e : ∀ c, (p 0 c - p 1 c) ^ 2 = 1 := by
    intro c
    have k3 : c = 0 ∨ c = 1 ∨ c = 2 := by fin_cases c <;> simp
    rcases k3 with rfl | rfl | rfl <;> linarith
  have key : ∀ c, (p 0 c = 0 ∧ p 1 c = 1) ∨ (p 0 c = 1 ∧ p 1 c = 0) := by
    intro c
    have ha := hp 0 c
    have hb := hp 1 c
    have hf : (p 0 c - p 1 c - 1) * (p 0 c - p 1 c + 1) = 0 := by
      have hr : (p 0 c - p 1 c - 1) * (p 0 c - p 1 c + 1) = (p 0 c - p 1 c) ^ 2 - 1 := by ring
      rw [hr, e c]
      norm_num
    rcases mul_eq_zero.mp hf with h | h
    · exact Or.inr ⟨by linarith [ha.2, hb.1], by linarith [ha.2, hb.1]⟩
    · exact Or.inl ⟨by linarith [ha.1, hb.2], by linarith [ha.1, hb.2]⟩
  refine ⟨fun c => decide (p 0 c = 1), 1, 1, fun i => ?_⟩
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  ext c
  rw [cubeSymm_apply]
  simp only [Equiv.Perm.one_apply]
  rcases hi with rfl | rfl
  · have hq : oppositeCorners 0 c = 0 := by simp [oppositeCorners, corner_apply]
    rw [hq]
    rcases key c with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]
  · have hq : oppositeCorners 1 c = 1 := by simp [oppositeCorners, corner_apply]
    rw [hq]
    rcases key c with ⟨h, h'⟩ | ⟨h, h'⟩ <;> simp [h, h']

/-- The two opposite corners are the unique optimal arrangement of two points. -/
theorem isUniqueMaxMinDist_two : IsUniqueMaxMinDist 2 (Real.sqrt 3) oppositeCorners :=
  ⟨inCube_oppositeCorners, fun _ _ h => dist_oppositeCorners h, isMaxMinDist_two.2,
    isUniqueUpToCubeSymm_two⟩

end Packing.Cube
