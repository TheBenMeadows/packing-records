/-
The best arrangement of eight points in the unit cube is unique: eight points pairwise at
distance at least `1` are the eight corners (`isUniqueMaxMinDist_eight`).

Each point lies in its own half-cube, and the twelve pairs in half-cubes that share a face are
at squared distance at least `1`. Two points of such a pair differ by at most `1/2` in the two
coordinates along the face, so they are at least `7/10` apart across it (`axis_gap`). The edge
inequality of the value proof is attained in every coordinate, and with that separation it is
attained only at the corners (`edge_sum_eq`).
-/
import Packing.CubeUniqueSmall
import Packing.Cube8Cert

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Packing.Cube8

open Packing.Cube

theorem lo_false : lo false = 0 := by simp [lo]

theorem lo_true : lo true = 1 / 2 := by simp [lo]

theorem hi_false : hi false = 1 / 2 := by simp [hi]

theorem hi_true : hi true = 1 := by simp [hi]

/-- Two points in half-cubes that share a face, at squared distance at least `1`, are at least
`7/10` apart across the face. -/
theorem axis_gap {s t u u' w w' : ℝ} {b b' : Bool} (hs : lo false ≤ s ∧ s ≤ hi false)
    (ht : lo true ≤ t ∧ t ≤ hi true) (hu : lo b ≤ u ∧ u ≤ hi b) (hu' : lo b ≤ u' ∧ u' ≤ hi b)
    (hw : lo b' ≤ w ∧ w ≤ hi b') (hw' : lo b' ≤ w' ∧ w' ≤ hi b')
    (h : 1 ≤ (s - t) ^ 2 + (u - u') ^ 2 + (w - w') ^ 2) : 0 ≤ -7 / 10 + t - s := by
  have e1 := half_sq_le hu hu'
  have e2 := half_sq_le hw hw'
  rw [lo_false, hi_false] at hs
  rw [lo_true, hi_true] at ht
  by_contra hn
  push Not at hn
  have e3 : (t - s) ^ 2 ≤ (7 / 10) ^ 2 := sq_le_sq' (by linarith [hs.2, ht.1]) (by linarith)
  linarith

/-- Eight points, one in each half-cube, pairwise at squared distance at least `1`, are the
corners of their half-cubes. -/
theorem corners_of_eight (q : Bool × Bool × Bool → Pt)
    (B : ∀ a b c, (lo a ≤ q (a, b, c) 0 ∧ q (a, b, c) 0 ≤ hi a)
      ∧ (lo b ≤ q (a, b, c) 1 ∧ q (a, b, c) 1 ≤ hi b)
      ∧ (lo c ≤ q (a, b, c) 2 ∧ q (a, b, c) 2 ≤ hi c))
    (S : ∀ v w, v ≠ w →
      1 ≤ (q v 0 - q w 0) ^ 2 + (q v 1 - q w 1) ^ 2 + (q v 2 - q w 2) ^ 2) :
    ∀ a b c, q (a, b, c) 0 = (if a then 1 else 0) ∧ q (a, b, c) 1 = (if b then 1 else 0)
      ∧ q (a, b, c) 2 = (if c then 1 else 0) := by
  have d00 := S (false, false, false) (true, false, false) (by simp)
  have d01 := S (false, false, true) (true, false, true) (by simp)
  have d02 := S (false, true, true) (true, true, true) (by simp)
  have d03 := S (false, true, false) (true, true, false) (by simp)
  have d10 := S (false, false, false) (false, true, false) (by simp)
  have d11 := S (false, false, true) (false, true, true) (by simp)
  have d12 := S (true, false, true) (true, true, true) (by simp)
  have d13 := S (true, false, false) (true, true, false) (by simp)
  have d20 := S (false, false, false) (false, false, true) (by simp)
  have d21 := S (false, true, false) (false, true, true) (by simp)
  have d22 := S (true, true, false) (true, true, true) (by simp)
  have d23 := S (true, false, false) (true, false, true) (by simp)
  have g00 := axis_gap (B false false false).1 (B true false false).1 (B false false false).2.1 (B true false false).2.1 (B false false false).2.2 (B true false false).2.2 (by linarith only [d00])
  have g01 := axis_gap (B false false true).1 (B true false true).1 (B false false true).2.1 (B true false true).2.1 (B false false true).2.2 (B true false true).2.2 (by linarith only [d01])
  have g02 := axis_gap (B false true true).1 (B true true true).1 (B false true true).2.1 (B true true true).2.1 (B false true true).2.2 (B true true true).2.2 (by linarith only [d02])
  have g03 := axis_gap (B false true false).1 (B true true false).1 (B false true false).2.1 (B true true false).2.1 (B false true false).2.2 (B true true false).2.2 (by linarith only [d03])
  have g10 := axis_gap (B false false false).2.1 (B false true false).2.1 (B false false false).1 (B false true false).1 (B false false false).2.2 (B false true false).2.2 (by linarith only [d10])
  have g11 := axis_gap (B false false true).2.1 (B false true true).2.1 (B false false true).1 (B false true true).1 (B false false true).2.2 (B false true true).2.2 (by linarith only [d11])
  have g12 := axis_gap (B true false true).2.1 (B true true true).2.1 (B true false true).1 (B true true true).1 (B true false true).2.2 (B true true true).2.2 (by linarith only [d12])
  have g13 := axis_gap (B true false false).2.1 (B true true false).2.1 (B true false false).1 (B true true false).1 (B true false false).2.2 (B true true false).2.2 (by linarith only [d13])
  have g20 := axis_gap (B false false false).2.2 (B false false true).2.2 (B false false false).1 (B false false true).1 (B false false false).2.1 (B false false true).2.1 (by linarith only [d20])
  have g21 := axis_gap (B false true false).2.2 (B false true true).2.2 (B false true false).1 (B false true true).1 (B false true false).2.1 (B false true true).2.1 (by linarith only [d21])
  have g22 := axis_gap (B true true false).2.2 (B true true true).2.2 (B true true false).1 (B true true true).1 (B true true false).2.1 (B true true true).2.1 (by linarith only [d22])
  have g23 := axis_gap (B true false false).2.2 (B true false true).2.2 (B true false false).1 (B true false true).1 (B true false false).2.1 (B true false true).2.1 (by linarith only [d23])
  have bfff := B false false false
  simp only [lo_false, hi_false] at bfff
  obtain ⟨⟨lfff0, ufff0⟩, ⟨lfff1, ufff1⟩, ⟨lfff2, ufff2⟩⟩ := bfff
  have bfft := B false false true
  simp only [lo_false, hi_false, lo_true, hi_true] at bfft
  obtain ⟨⟨lfft0, ufft0⟩, ⟨lfft1, ufft1⟩, ⟨lfft2, ufft2⟩⟩ := bfft
  have bftf := B false true false
  simp only [lo_false, hi_false, lo_true, hi_true] at bftf
  obtain ⟨⟨lftf0, uftf0⟩, ⟨lftf1, uftf1⟩, ⟨lftf2, uftf2⟩⟩ := bftf
  have bftt := B false true true
  simp only [lo_false, hi_false, lo_true, hi_true] at bftt
  obtain ⟨⟨lftt0, uftt0⟩, ⟨lftt1, uftt1⟩, ⟨lftt2, uftt2⟩⟩ := bftt
  have btff := B true false false
  simp only [lo_false, hi_false, lo_true, hi_true] at btff
  obtain ⟨⟨ltff0, utff0⟩, ⟨ltff1, utff1⟩, ⟨ltff2, utff2⟩⟩ := btff
  have btft := B true false true
  simp only [lo_false, hi_false, lo_true, hi_true] at btft
  obtain ⟨⟨ltft0, utft0⟩, ⟨ltft1, utft1⟩, ⟨ltft2, utft2⟩⟩ := btft
  have bttf := B true true false
  simp only [lo_false, hi_false, lo_true, hi_true] at bttf
  obtain ⟨⟨lttf0, uttf0⟩, ⟨lttf1, uttf1⟩, ⟨lttf2, uttf2⟩⟩ := bttf
  have bttt := B true true true
  simp only [lo_true, hi_true] at bttt
  obtain ⟨⟨lttt0, uttt0⟩, ⟨lttt1, uttt1⟩, ⟨lttt2, uttt2⟩⟩ := bttt
  have E0 := edge_sum_le (B false false false).1 (B false false true).1 (B false true true).1 (B false true false).1 (B true false false).1 (B true false true).1 (B true true true).1 (B true true false).1
  have E1 := edge_sum_le (B false false false).2.1 (B false false true).2.1 (B true false true).2.1 (B true false false).2.1 (B false true false).2.1 (B false true true).2.1 (B true true true).2.1 (B true true false).2.1
  have E2 := edge_sum_le (B false false false).2.2 (B false true false).2.2 (B true true false).2.2 (B true false false).2.2 (B false false true).2.2 (B false true true).2.2 (B true true true).2.2 (B true false true).2.2
  obtain ⟨s00, s01, s02, s03, t00, t01, t02, t03⟩ := Packing.Cube8.edge_sum_eq (q (false, false, false) 0) (q (false, false, true) 0) (q (false, true, true) 0) (q (false, true, false) 0) (q (true, false, false) 0) (q (true, false, true) 0) (q (true, true, true) 0) (q (true, true, false) 0)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith)
  obtain ⟨s10, s11, s12, s13, t10, t11, t12, t13⟩ := Packing.Cube8.edge_sum_eq (q (false, false, false) 1) (q (false, false, true) 1) (q (true, false, true) 1) (q (true, false, false) 1) (q (false, true, false) 1) (q (false, true, true) 1) (q (true, true, true) 1) (q (true, true, false) 1)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith)
  obtain ⟨s20, s21, s22, s23, t20, t21, t22, t23⟩ := Packing.Cube8.edge_sum_eq (q (false, false, false) 2) (q (false, true, false) 2) (q (true, true, false) 2) (q (true, false, false) 2) (q (false, false, true) 2) (q (false, true, true) 2) (q (true, true, true) 2) (q (true, false, true) 2)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith)
  intro a b c
  cases a <;> cases b <;> cases c
  · exact ⟨by rw [s00]; rfl, by rw [s10]; rfl, by rw [s20]; rfl⟩
  · exact ⟨by rw [s01]; rfl, by rw [s11]; rfl, by rw [t20]; rfl⟩
  · exact ⟨by rw [s03]; rfl, by rw [t10]; rfl, by rw [s21]; rfl⟩
  · exact ⟨by rw [s02]; rfl, by rw [t11]; rfl, by rw [t21]; rfl⟩
  · exact ⟨by rw [t00]; rfl, by rw [s13]; rfl, by rw [s23]; rfl⟩
  · exact ⟨by rw [t01]; rfl, by rw [s12]; rfl, by rw [t23]; rfl⟩
  · exact ⟨by rw [t03]; rfl, by rw [t13]; rfl, by rw [s22]; rfl⟩
  · exact ⟨by rw [t02]; rfl, by rw [t12]; rfl, by rw [t22]; rfl⟩

/-! ### The theorem -/

/-- The eight corners of the cube. -/
noncomputable def eight : Fin 8 → Pt :=
  fun i => corner ((Fintype.equivOfCardEq (by simp) : Fin 8 ≃ (Fin 3 → Bool)) i)

theorem cubeSymm_false_one (x : Pt) : cubeSymm (fun _ => false) 1 x = x := by
  ext c
  simp [cubeSymm_apply]

theorem isUniqueUpToCubeSymm_eight : IsUniqueUpToCubeSymm 8 1 eight := by
  apply isUniqueUpToCubeSymm_of_exists one_pos
  intro p hp hd
  have hsq : ∀ i j, i ≠ j → 1 ≤ dist (p i) (p j) ^ 2 := by
    intro i j hij
    have h := hd i j hij
    nlinarith [dist_nonneg (x := p i) (y := p j)]
  have hinj : Function.Injective fun i => cell (p i) := by
    intro i j h
    by_contra hij
    have h1 := hsq i j hij
    have h2 := dist_sq_le_of_cell_eq (hp i) (hp j) h
    linarith
  have hbij : Function.Bijective fun i => cell (p i) :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, by simp⟩
  let e := Equiv.ofBijective _ hbij
  have hcorn := corners_of_eight (fun v => p (e.symm v))
    (fun a b c => cell_bounds (hp _) (e.apply_symm_apply (a, b, c)))
    (fun v w hvw => by
      rw [← dist_sq]
      exact hsq _ _ fun h => hvw (e.symm.injective h))
  refine ⟨fun _ => false, 1, fun i => ?_⟩
  obtain ⟨c0, c1, c2⟩ := hcorn (e i).1 (e i).2.1 (e i).2.2
  rw [show ((e i).1, (e i).2.1, (e i).2.2) = e i from rfl, e.symm_apply_apply] at c0 c1 c2
  refine ⟨(Fintype.equivOfCardEq (by simp) : Fin 8 ≃ (Fin 3 → Bool)).symm
    ![(e i).1, (e i).2.1, (e i).2.2], ?_⟩
  rw [cubeSymm_false_one]
  unfold eight
  rw [Equiv.apply_symm_apply]
  exact pt_ext (by rw [c0, corner_apply]; rfl) (by rw [c1, corner_apply]; rfl)
    (by rw [c2, corner_apply]; rfl)

theorem inCube_eight (i : Fin 8) : InCube (eight i) := inCube_corner _

theorem dist_eight {i j : Fin 8} (h : i ≠ j) : 1 ≤ dist (eight i) (eight j) :=
  one_le_dist_corner fun h' => h ((Fintype.equivOfCardEq (by simp) :
    Fin 8 ≃ (Fin 3 → Bool)).injective h')

/-- The eight corners are the unique best arrangement of eight points in the unit cube. -/
theorem isUniqueMaxMinDist_eight : IsUniqueMaxMinDist 8 1 eight :=
  ⟨inCube_eight, fun _ _ h => dist_eight h, exists_dist_le_eight, isUniqueUpToCubeSymm_eight⟩

end Packing.Cube8
