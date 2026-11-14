/-
The best arrangement of six points in the unit cube is unique.

Reference: J. Schaer, "The densest packing of six spheres in a cube", Canad. Math. Bull. 9
(1966), 275-280. Every arrangement of six points of the cube with pairwise distances at least
`3 sqrt 2 / 4` is the image of `six`, in some order, under a symmetry of the cube
(`isUniqueMaxMinDist_six`).

The six points lie in six different half-cubes, and the two empty half-cubes are opposite
(`empties_opposite`). After a reflection the empty ones are `(0,0,0)` and `(1,1,1)`. Then
`six_normal_ge` determines the three points nearest the origin, and the same lemma applied to
the arrangement reflected in all three coordinates determines the other three
(`six_unique_normal`).
-/
import Packing.CubeUnique
import Packing.Cube6Opposite

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Packing.Cube6

open Packing.Cube

theorem pt_ext {x y : Pt} (h0 : x 0 = y 0) (h1 : x 1 = y 1) (h2 : x 2 = y 2) : x = y := by
  ext c
  fin_cases c
  · exact h0
  · exact h1
  · exact h2

theorem six_val (m : Fin 6) (c : Fin 3) :
    six m c = if m = 0 then (if c = 0 then 3 / 4 else 0)
      else if m = 1 then (if c = 1 then 3 / 4 else 0)
      else if m = 2 then (if c = 2 then 3 / 4 else 0)
      else if m = 3 then (if c = 0 then 1 / 4 else 1)
      else if m = 4 then (if c = 1 then 1 / 4 else 1)
      else (if c = 2 then 1 / 4 else 1) := by
  rw [six_apply]
  fin_cases m <;> fin_cases c <;> simp

/-- Six points, one in each half-cube other than `(0,0,0)` and `(1,1,1)`, pairwise at squared
distance at least `9/8`, are the points of `six`. -/
theorem six_unique_normal (q : Fin 6 → Pt) (f : Fin 6 → Bool × Bool × Bool)
    (hf : Function.Injective f)
    (hb : ∀ i, (lo (f i).1 ≤ q i 0 ∧ q i 0 ≤ hi (f i).1) ∧
      (lo (f i).2.1 ≤ q i 1 ∧ q i 1 ≤ hi (f i).2.1) ∧
      (lo (f i).2.2 ≤ q i 2 ∧ q i 2 ≤ hi (f i).2.2))
    (h000 : ∀ i, f i ≠ (false, false, false)) (h111 : ∀ i, f i ≠ (true, true, true))
    (hsq : ∀ i j, i ≠ j → 9 / 8 ≤ dist (q i) (q j) ^ 2) : ∀ i, ∃ m, q i = six m := by
  have hcard : ((Finset.univ.image f)ᶜ).card = 2 := by
    rw [Finset.card_compl, Finset.card_image_of_injective _ hf]
    simp
  have hsub : ({(false, false, false), (true, true, true)} : Finset (Bool × Bool × Bool)) ⊆
      (Finset.univ.image f)ᶜ := by
    intro v hv
    rw [Finset.mem_compl, Finset.mem_image]
    rintro ⟨i, -, hi⟩
    rw [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact h000 i hi
    · exact h111 i hi
  have heq := Finset.eq_of_subset_of_card_le hsub
    (by rw [hcard]; exact (Finset.card_pair (by decide)).ge)
  have hocc : ∀ v, v ≠ (false, false, false) → v ≠ (true, true, true) → ∃ i, f i = v := by
    intro v h1 h2
    have hv : v ∉ (Finset.univ.image f)ᶜ := by
      rw [← heq, Finset.mem_insert, Finset.mem_singleton]
      exact fun h => h.elim h1 h2
    rw [Finset.mem_compl, not_not, Finset.mem_image] at hv
    obtain ⟨i, -, hi⟩ := hv
    exact ⟨i, hi⟩
  obtain ⟨iP, hP⟩ := hocc (true, false, false) (by decide) (by decide)
  have bP := hb iP
  simp only [hP, lo_false, lo_true, hi_false, hi_true] at bP
  obtain ⟨⟨lP0, uP0⟩, ⟨lP1, uP1⟩, ⟨lP2, uP2⟩⟩ := bP
  obtain ⟨iQ, hQ⟩ := hocc (false, true, false) (by decide) (by decide)
  have bQ := hb iQ
  simp only [hQ, lo_false, lo_true, hi_false, hi_true] at bQ
  obtain ⟨⟨lQ0, uQ0⟩, ⟨lQ1, uQ1⟩, ⟨lQ2, uQ2⟩⟩ := bQ
  obtain ⟨iR, hR⟩ := hocc (false, false, true) (by decide) (by decide)
  have bR := hb iR
  simp only [hR, lo_false, lo_true, hi_false, hi_true] at bR
  obtain ⟨⟨lR0, uR0⟩, ⟨lR1, uR1⟩, ⟨lR2, uR2⟩⟩ := bR
  obtain ⟨iS, hS⟩ := hocc (true, true, false) (by decide) (by decide)
  have bS := hb iS
  simp only [hS, lo_false, lo_true, hi_false, hi_true] at bS
  obtain ⟨⟨lS0, uS0⟩, ⟨lS1, uS1⟩, ⟨lS2, uS2⟩⟩ := bS
  obtain ⟨iU, hU⟩ := hocc (true, false, true) (by decide) (by decide)
  have bU := hb iU
  simp only [hU, lo_false, lo_true, hi_false, hi_true] at bU
  obtain ⟨⟨lU0, uU0⟩, ⟨lU1, uU1⟩, ⟨lU2, uU2⟩⟩ := bU
  obtain ⟨iV, hV⟩ := hocc (false, true, true) (by decide) (by decide)
  have bV := hb iV
  simp only [hV, lo_false, lo_true, hi_false, hi_true] at bV
  obtain ⟨⟨lV0, uV0⟩, ⟨lV1, uV1⟩, ⟨lV2, uV2⟩⟩ := bV
  have dPQ := hsq iP iQ (by intro h; rw [h] at hP; exact absurd (hP.symm.trans hQ) (by decide))
  rw [dist_sq] at dPQ
  have dPR := hsq iP iR (by intro h; rw [h] at hP; exact absurd (hP.symm.trans hR) (by decide))
  rw [dist_sq] at dPR
  have dPS := hsq iP iS (by intro h; rw [h] at hP; exact absurd (hP.symm.trans hS) (by decide))
  rw [dist_sq] at dPS
  have dPU := hsq iP iU (by intro h; rw [h] at hP; exact absurd (hP.symm.trans hU) (by decide))
  rw [dist_sq] at dPU
  have dQR := hsq iQ iR (by intro h; rw [h] at hQ; exact absurd (hQ.symm.trans hR) (by decide))
  rw [dist_sq] at dQR
  have dQS := hsq iQ iS (by intro h; rw [h] at hQ; exact absurd (hQ.symm.trans hS) (by decide))
  rw [dist_sq] at dQS
  have dQV := hsq iQ iV (by intro h; rw [h] at hQ; exact absurd (hQ.symm.trans hV) (by decide))
  rw [dist_sq] at dQV
  have dRU := hsq iR iU (by intro h; rw [h] at hR; exact absurd (hR.symm.trans hU) (by decide))
  rw [dist_sq] at dRU
  have dRV := hsq iR iV (by intro h; rw [h] at hR; exact absurd (hR.symm.trans hV) (by decide))
  rw [dist_sq] at dRV
  have dSU := hsq iS iU (by intro h; rw [h] at hS; exact absurd (hS.symm.trans hU) (by decide))
  rw [dist_sq] at dSU
  have dSV := hsq iS iV (by intro h; rw [h] at hS; exact absurd (hS.symm.trans hV) (by decide))
  rw [dist_sq] at dSV
  have dUV := hsq iU iV (by intro h; rw [h] at hU; exact absurd (hU.symm.trans hV) (by decide))
  rw [dist_sq] at dUV
  obtain ⟨p0e, p1e, p2e, q0e, q1e, q2e, r0e, r1e, r2e⟩ := @six_normal_ge (q iP 0) (q iP 1) (q iP 2) (q iQ 0) (q iQ 1) (q iQ 2) (q iR 0) (q iR 1) (q iR 2) (q iS 0) (q iS 1) (q iS 2) (q iU 0) (q iU 1) (q iU 2) (q iV 0) (q iV 1) (q iV 2)
    ⟨by linarith only [lP0, uP0], by linarith only [lP0, uP0]⟩ ⟨by linarith only [lP1, uP1], by linarith only [lP1, uP1]⟩ ⟨by linarith only [lP2, uP2], by linarith only [lP2, uP2]⟩ ⟨by linarith only [lQ0, uQ0], by linarith only [lQ0, uQ0]⟩ ⟨by linarith only [lQ1, uQ1], by linarith only [lQ1, uQ1]⟩ ⟨by linarith only [lQ2, uQ2], by linarith only [lQ2, uQ2]⟩ ⟨by linarith only [lR0, uR0], by linarith only [lR0, uR0]⟩ ⟨by linarith only [lR1, uR1], by linarith only [lR1, uR1]⟩ ⟨by linarith only [lR2, uR2], by linarith only [lR2, uR2]⟩ ⟨by linarith only [lS0, uS0], by linarith only [lS0, uS0]⟩ ⟨by linarith only [lS1, uS1], by linarith only [lS1, uS1]⟩ ⟨by linarith only [lS2, uS2], by linarith only [lS2, uS2]⟩ ⟨by linarith only [lU0, uU0], by linarith only [lU0, uU0]⟩ ⟨by linarith only [lU1, uU1], by linarith only [lU1, uU1]⟩ ⟨by linarith only [lU2, uU2], by linarith only [lU2, uU2]⟩ ⟨by linarith only [lV0, uV0], by linarith only [lV0, uV0]⟩ ⟨by linarith only [lV1, uV1], by linarith only [lV1, uV1]⟩ ⟨by linarith only [lV2, uV2], by linarith only [lV2, uV2]⟩
    dPQ dPR dPS dPU dQR dQS dQV dRU dRV dSU dSV dUV
  obtain ⟨v0e, v1e, v2e, u0e, u1e, u2e, s0e, s1e, s2e⟩ := @six_normal_ge (1 - q iV 0) (1 - q iV 1) (1 - q iV 2) (1 - q iU 0) (1 - q iU 1) (1 - q iU 2) (1 - q iS 0) (1 - q iS 1) (1 - q iS 2) (1 - q iR 0) (1 - q iR 1) (1 - q iR 2) (1 - q iQ 0) (1 - q iQ 1) (1 - q iQ 2) (1 - q iP 0) (1 - q iP 1) (1 - q iP 2)
    ⟨by linarith only [lV0, uV0], by linarith only [lV0, uV0]⟩ ⟨by linarith only [lV1, uV1], by linarith only [lV1, uV1]⟩ ⟨by linarith only [lV2, uV2], by linarith only [lV2, uV2]⟩ ⟨by linarith only [lU0, uU0], by linarith only [lU0, uU0]⟩ ⟨by linarith only [lU1, uU1], by linarith only [lU1, uU1]⟩ ⟨by linarith only [lU2, uU2], by linarith only [lU2, uU2]⟩ ⟨by linarith only [lS0, uS0], by linarith only [lS0, uS0]⟩ ⟨by linarith only [lS1, uS1], by linarith only [lS1, uS1]⟩ ⟨by linarith only [lS2, uS2], by linarith only [lS2, uS2]⟩ ⟨by linarith only [lR0, uR0], by linarith only [lR0, uR0]⟩ ⟨by linarith only [lR1, uR1], by linarith only [lR1, uR1]⟩ ⟨by linarith only [lR2, uR2], by linarith only [lR2, uR2]⟩ ⟨by linarith only [lQ0, uQ0], by linarith only [lQ0, uQ0]⟩ ⟨by linarith only [lQ1, uQ1], by linarith only [lQ1, uQ1]⟩ ⟨by linarith only [lQ2, uQ2], by linarith only [lQ2, uQ2]⟩ ⟨by linarith only [lP0, uP0], by linarith only [lP0, uP0]⟩ ⟨by linarith only [lP1, uP1], by linarith only [lP1, uP1]⟩ ⟨by linarith only [lP2, uP2], by linarith only [lP2, uP2]⟩
    (by linarith only [dUV]) (by linarith only [dSV]) (by linarith only [dRV]) (by linarith only [dQV]) (by linarith only [dSU]) (by linarith only [dRU]) (by linarith only [dPU]) (by linarith only [dQS]) (by linarith only [dPS]) (by linarith only [dQR]) (by linarith only [dPR]) (by linarith only [dPQ])
  intro i
  have a0 := h000 i
  have a1 := h111 i
  rcases hfi : f i with ⟨a, b, c⟩
  rw [hfi] at a0 a1
  cases a <;> cases b <;> cases c
  · exact absurd rfl a0
  · have hi : i = iR := hf (hfi.trans hR.symm)
    rw [hi]
    exact ⟨2, pt_ext (by rw [r0e, six_val]; simp)
      (by rw [r1e, six_val]; simp) (by rw [r2e, six_val]; simp)⟩
  · have hi : i = iQ := hf (hfi.trans hQ.symm)
    rw [hi]
    exact ⟨1, pt_ext (by rw [q0e, six_val]; simp)
      (by rw [q1e, six_val]; simp) (by rw [q2e, six_val]; simp)⟩
  · have hi : i = iV := hf (hfi.trans hV.symm)
    rw [hi]
    exact ⟨3, pt_ext (by rw [show q iV 0 = 1 / 4 by linarith only [v0e], six_val]; simp)
      (by rw [show q iV 1 = 1 by linarith only [v1e], six_val]; simp) (by rw [show q iV 2 = 1 by linarith only [v2e], six_val]; simp)⟩
  · have hi : i = iP := hf (hfi.trans hP.symm)
    rw [hi]
    exact ⟨0, pt_ext (by rw [p0e, six_val]; simp)
      (by rw [p1e, six_val]; simp) (by rw [p2e, six_val]; simp)⟩
  · have hi : i = iU := hf (hfi.trans hU.symm)
    rw [hi]
    exact ⟨4, pt_ext (by rw [show q iU 0 = 1 by linarith only [u0e], six_val]; simp)
      (by rw [show q iU 1 = 1 / 4 by linarith only [u1e], six_val]; simp) (by rw [show q iU 2 = 1 by linarith only [u2e], six_val]; simp)⟩
  · have hi : i = iS := hf (hfi.trans hS.symm)
    rw [hi]
    exact ⟨5, pt_ext (by rw [show q iS 0 = 1 by linarith only [s0e], six_val]; simp)
      (by rw [show q iS 1 = 1 by linarith only [s1e], six_val]; simp) (by rw [show q iS 2 = 1 / 4 by linarith only [s2e], six_val]; simp)⟩
  · exact absurd rfl a1

/-! ### Reflections -/

theorem cubeSymm_one_invol (v : Fin 3 → Bool) (x : Pt) : cubeSymm v 1 (cubeSymm v 1 x) = x := by
  ext c
  simp only [cubeSymm_apply, Equiv.Perm.one_apply]
  split_ifs <;> ring

theorem refl_bounds {b e : Bool} {x : ℝ} (h : lo b ≤ x ∧ x ≤ hi b) :
    lo (xor b e) ≤ (if e then 1 - x else x) ∧ (if e then 1 - x else x) ≤ hi (xor b e) := by
  obtain ⟨h1, h2⟩ := h
  cases b <;> cases e <;> simp [lo, hi] at h1 h2 ⊢ <;> (constructor <;> linarith)

theorem xor_cancel {x y a : Bool} (h : xor x a = xor y a) : x = y := by
  cases x <;> cases y <;> cases a <;> simp_all

theorem xor_eq_false' {x a : Bool} (h : xor x a = false) : x = a := by
  cases x <;> cases a <;> simp_all

theorem xor_eq_true' {x a : Bool} (h : xor x a = true) : x = !a := by
  cases x <;> cases a <;> simp_all

/-! ### The theorem -/

/-- Every arrangement of six points of the unit cube with pairwise distances at least
`3 sqrt 2 / 4` is the image of `six`, in some order, under a symmetry of the cube. -/
theorem isUniqueUpToCubeSymm_six : IsUniqueUpToCubeSymm 6 (3 * Real.sqrt 2 / 4) six := by
  intro p hp hd
  have hsq : ∀ i j, i ≠ j → 9 / 8 ≤ dist (p i) (p j) ^ 2 := by
    intro i j hij
    have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 3 * Real.sqrt 2 / 4) (hd i j hij) 2
    rwa [sqrt_two_sq] at h
  have hinj : Function.Injective fun i => cell (p i) := by
    intro i j h
    by_contra hij
    have h1 := hsq i j hij
    have h2 := dist_sq_le_of_cell_eq (hp i) (hp j) h
    linarith
  have hcard : ((Finset.univ.image fun i => cell (p i))ᶜ).card = 2 := by
    rw [Finset.card_compl, Finset.card_image_of_injective _ hinj]
    simp
  obtain ⟨e1, e2, hne, hE⟩ := Finset.card_eq_two.mp hcard
  have hocc : ∀ v, v ≠ e1 → v ≠ e2 → ∃ i, cell (p i) = v := by
    intro v h1 h2
    have hv : v ∉ (Finset.univ.image fun i => cell (p i))ᶜ := by
      rw [hE]
      simp [h1, h2]
    rw [Finset.mem_compl, not_not, Finset.mem_image] at hv
    obtain ⟨i, -, hi⟩ := hv
    exact ⟨i, hi⟩
  have hopp := empties_opposite p hp hsq e1 e2 hne hocc
  have hemp1 : ∀ i, cell (p i) ≠ e1 := by
    intro i hi
    have hmem : e1 ∈ (Finset.univ.image fun i => cell (p i))ᶜ := by
      rw [hE]
      simp
    rw [Finset.mem_compl, Finset.mem_image] at hmem
    exact hmem ⟨i, Finset.mem_univ _, hi⟩
  have hemp2 : ∀ i, cell (p i) ≠ e2 := by
    intro i hi
    have hmem : e2 ∈ (Finset.univ.image fun i => cell (p i))ᶜ := by
      rw [hE]
      simp
    rw [Finset.mem_compl, Finset.mem_image] at hmem
    exact hmem ⟨i, Finset.mem_univ _, hi⟩
  obtain ⟨a, b, c⟩ := e1
  let v : Fin 3 → Bool := ![a, b, c]
  have hc0 : ∀ x : Pt, cubeSymm v 1 x 0 = if a then 1 - x 0 else x 0 := by
    intro x
    rfl
  have hc1 : ∀ x : Pt, cubeSymm v 1 x 1 = if b then 1 - x 1 else x 1 := by
    intro x
    rfl
  have hc2 : ∀ x : Pt, cubeSymm v 1 x 2 = if c then 1 - x 2 else x 2 := by
    intro x
    rfl
  have hN : ∀ i, ∃ m, cubeSymm v 1 (p i) = six m := by
    apply six_unique_normal (fun i => cubeSymm v 1 (p i))
      (fun i => (xor (cell (p i)).1 a, xor (cell (p i)).2.1 b, xor (cell (p i)).2.2 c))
    · intro i j h
      simp only [Prod.mk.injEq] at h
      exact hinj (Prod.ext (xor_cancel h.1) (Prod.ext (xor_cancel h.2.1) (xor_cancel h.2.2)))
    · intro i
      have B := cell_bounds (hp i)
        (rfl : cell (p i) = ((cell (p i)).1, (cell (p i)).2.1, (cell (p i)).2.2))
      have g0 := refl_bounds (e := a) B.1
      have g1 := refl_bounds (e := b) B.2.1
      have g2 := refl_bounds (e := c) B.2.2
      rw [← hc0] at g0
      rw [← hc1] at g1
      rw [← hc2] at g2
      exact ⟨g0, g1, g2⟩
    · intro i h
      simp only [Prod.mk.injEq] at h
      exact hemp1 i (Prod.ext (xor_eq_false' h.1)
        (Prod.ext (xor_eq_false' h.2.1) (xor_eq_false' h.2.2)))
    · intro i h
      simp only [Prod.mk.injEq] at h
      apply hemp2 i
      rw [hopp]
      exact Prod.ext (xor_eq_true' h.1) (Prod.ext (xor_eq_true' h.2.1) (xor_eq_true' h.2.2))
    · intro i j hij
      show 9 / 8 ≤ dist (cubeSymm v 1 (p i)) (cubeSymm v 1 (p j)) ^ 2
      rw [dist_cubeSymm]
      exact hsq i j hij
  have hm : ∀ i, ∃ m, p i = cubeSymm v 1 (six m) := by
    intro i
    obtain ⟨m, hm⟩ := hN i
    exact ⟨m, by rw [← hm, cubeSymm_one_invol]⟩
  choose e he using hm
  have hinj' : Function.Injective e := by
    intro i j hij
    by_contra hne'
    have h := hsq i j hne'
    rw [he i, he j, hij, dist_self] at h
    norm_num at h
  exact ⟨v, 1, Equiv.ofBijective e (Finite.injective_iff_bijective.mp hinj'), he⟩

/-- `six` is the unique best arrangement of six points in the unit cube, up to the symmetries
of the cube. -/
theorem isUniqueMaxMinDist_six : IsUniqueMaxMinDist 6 (3 * Real.sqrt 2 / 4) six :=
  ⟨inCube_six, fun _ _ h => dist_six h, exists_dist_le_six, isUniqueUpToCubeSymm_six⟩

/-- Every best arrangement of six points in the unit cube is congruent to `six`. -/
theorem isUniqueUpToIsometry_six : IsUniqueUpToIsometry 6 (3 * Real.sqrt 2 / 4) six :=
  isUniqueMaxMinDist_six.toIsometry

end Packing.Cube6
