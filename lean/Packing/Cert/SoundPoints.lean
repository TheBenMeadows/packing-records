/-
Soundness of the checkers of `Packing.Cert.CheckPoints` for spherical codes, balls in the unit
ball and balls in the unit cube. Each theorem has two forms: one about the data itself (the
vectors of the file) and one that only asserts that a configuration exists.
-/
import Packing.Cert.Sound
import Packing.Cert.CheckPoints
import Packing.CubeBalls

open Module
open scoped InnerProductSpace

namespace Packing

/-- There are `N` unit vectors in `ℝ^d` with pairwise inner products at most `t`. -/
def HasSphericalCode (d N : ℕ) (t : ℝ) : Prop :=
  ∃ x : Fin N → EuclideanSpace ℝ (Fin d),
    (∀ i, ‖x i‖ = 1) ∧ ∀ i j, i ≠ j → ⟪x i, x j⟫_ℝ ≤ t

/-- There are `N` balls of radius `r` inside the unit ball of `ℝ^d` with pairwise disjoint
interiors, described by their centres: every centre has norm at most `1 - r` and every two
centres are at distance at least `2r`. -/
def HasBallPackingInBall (d N : ℕ) (r : ℝ) : Prop :=
  ∃ c : Fin N → EuclideanSpace ℝ (Fin d),
    (∀ i, ‖c i‖ ≤ 1 - r) ∧ ∀ i j, i ≠ j → 2 * r ≤ dist (c i) (c j)

/-- There are `N` balls of radius `r` inside the unit cube with pairwise disjoint interiors,
described by their centres as in `Cube.IsBallPacking`. -/
def HasBallPackingInCube (N : ℕ) (r : ℝ) : Prop :=
  ∃ c, Cube.IsBallPacking N r c

namespace Cert

theorem le_of_sq_le_sq' {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  by_contra hlt
  push Not at hlt
  nlinarith [mul_pos (sub_pos.mpr hlt) (by linarith : (0 : ℝ) < a + b)]

/-! ### The definitions in ordinary notation -/

theorem orB_eq_true {a b : Bool} : orB a b = true ↔ a = true ∨ b = true := by
  cases a
  · exact ⟨fun h => Or.inr h, fun h => h.elim (fun h' => Bool.noConfusion h') id⟩
  · exact ⟨fun _ => Or.inl rfl, fun _ => rfl⟩

/-- What `okVec0` establishes. -/
structure OkVec (m : ℕ) (v : Vec) : Prop where
  len : v.e.length = m
  sum : sumMap (fun x => x) v.e = v.sum
  nsq : v.nsq + dotY v v = dotX m v v

theorem okVec0_iff {m : ℕ} {v : Vec} : okVec0 m v = true ↔ OkVec m v := by
  unfold okVec0
  simp only [andB_eq_true, beq_iff, sumMap_one]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.len, h.sum, h.nsq⟩⟩

theorem okVec_iff {m : ℕ} {v : Vec} : okVec m v = true ↔ OkVec m v ∧ 1 ≤ v.nsq := by
  unfold okVec
  simp only [andB_eq_true, beq_iff, Nat.ble_eq, sumMap_one]
  exact ⟨fun h => ⟨⟨h.1, h.2.1, h.2.2.1⟩, h.2.2.2⟩,
    fun h => ⟨h.1.len, h.1.sum, h.1.nsq, h.2⟩⟩

theorem cosB_iff {m t2 q2 : ℕ} {u v : Vec} :
    cosB m t2 q2 u v = true ↔ dotX m u v ≤ dotY u v ∨
      absDot m u v * absDot m u v * q2 ≤ t2 * (u.nsq * v.nsq) := by
  unfold cosB
  simp only [orB_eq_true, Nat.ble_eq]
  exact Iff.rfl

theorem farB_iff {m q2 c : ℕ} {u v : Vec} :
    farB m q2 c u v = true ↔
      c + 2 * dotX m u v * q2 ≤ (u.nsq + v.nsq + 2 * dotY u v) * q2 := by
  unfold farB
  simp only [Nat.ble_eq]
  exact Iff.rfl

theorem boxB_iff {w : ℕ} {v : Vec} :
    boxB w v = true ↔ ∀ x ∈ v.e,
      2 * 10 ^ 12 * x ≤ 2 * 10 ^ 12 * v.off + w ∧ 2 * 10 ^ 12 * v.off ≤ 2 * 10 ^ 12 * x + w := by
  unfold boxB
  simp only [allB_eq_true, andB_eq_true, Nat.ble_eq]
  exact Iff.rfl

theorem checkSph_iff {m N t : ℕ} {c : List Vec} :
    checkSph m N t c = true ↔ c.length = N ∧ (∀ v ∈ c, okVec m v = true) ∧
      c.Pairwise fun u v => cosB m (t * t) (10 ^ 24) u v = true := by
  unfold checkSph
  simp only [andB_eq_true, allB_eq_true, pairwiseB_eq_true, beq_iff, sumMap_one]
  exact Iff.rfl

theorem checkBall_iff {m N t S : ℕ} {c : List Vec} :
    checkBall m N t S c = true ↔ c.length = N ∧ 1 ≤ S ∧ t ≤ 10 ^ 12 ∧
      (∀ v ∈ c, okVec0 m v = true) ∧
      (∀ v ∈ c, v.nsq * 10 ^ 24 ≤ (10 ^ 12 - t) * (10 ^ 12 - t) * (S * S)) ∧
      c.Pairwise fun u v => farB m (10 ^ 24) (4 * (t * t) * (S * S)) u v = true := by
  unfold checkBall
  simp only [andB_eq_true, allB_eq_true, pairwiseB_eq_true, beq_iff, Nat.ble_eq, sumMap_one]
  exact Iff.rfl

theorem checkCube_iff {N t S : ℕ} {c : List Vec} :
    checkCube N t S c = true ↔ c.length = N ∧ 1 ≤ S ∧ 2 * t ≤ 10 ^ 12 ∧
      (∀ v ∈ c, okVec0 3 v = true) ∧
      (∀ v ∈ c, boxB ((10 ^ 12 - 2 * t) * S) v = true) ∧
      c.Pairwise fun u v => farB 3 (10 ^ 24) (4 * (t * t) * (S * S)) u v = true := by
  unfold checkCube
  simp only [andB_eq_true, allB_eq_true, pairwiseB_eq_true, beq_iff, Nat.ble_eq, sumMap_one]
  exact Iff.rfl

/-! ### Vectors -/

section Vectors

variable {m : ℕ} {u v : Vec}

theorem toVec_apply (m : ℕ) (v : Vec) (k : Fin m) :
    toVec m v k = ((v.e.getD k 0 : ℕ) : ℝ) - v.off := rfl

theorem inner_toVec' (hu : OkVec m u) (hv : OkVec m v) :
    ⟪toVec m u, toVec m v⟫_ℝ = (dotX m u v : ℝ) - (dotY u v : ℝ) :=
  inner_toVec hu.len hv.len hu.sum hv.sum

theorem norm_sq_toVec (hv : OkVec m v) : ‖toVec m v‖ ^ 2 = (v.nsq : ℝ) := by
  rw [← real_inner_self_eq_norm_sq, inner_toVec' hv hv, ← hv.nsq]
  push_cast
  ring

theorem norm_sub_sq_toVec (hu : OkVec m u) (hv : OkVec m v) :
    ‖toVec m u - toVec m v‖ ^ 2
      = (u.nsq : ℝ) + v.nsq - 2 * ((dotX m u v : ℝ) - (dotY u v : ℝ)) := by
  rw [norm_sub_sq_real, norm_sq_toVec hu, norm_sq_toVec hv, inner_toVec' hu hv]
  ring

theorem toVec_ne_zero (hv : OkVec m v) (hpos : 1 ≤ v.nsq) : toVec m v ≠ 0 := by
  intro h
  have h1 := norm_sq_toVec hv
  rw [h, norm_zero] at h1
  have h2 : (1 : ℝ) ≤ v.nsq := by exact_mod_cast hpos
  norm_num at h1
  linarith

/-- The cosine check, in the reals. -/
theorem inner_le_of_cosB (hu : OkVec m u) (hv : OkVec m v) {t : ℕ}
    (h : cosB m (t * t) (10 ^ 24) u v = true) :
    ⟪toVec m u, toVec m v⟫_ℝ ≤ (t : ℝ) / 10 ^ 12 * (‖toVec m u‖ * ‖toVec m v‖) := by
  have hB : 0 ≤ (t : ℝ) / 10 ^ 12 * (‖toVec m u‖ * ‖toVec m v‖) := by positivity
  rcases cosB_iff.mp h with h1 | h2
  · rw [inner_toVec' hu hv]
    have : (dotX m u v : ℝ) ≤ dotY u v := by exact_mod_cast h1
    linarith
  · apply le_of_sq_le_sq' hB
    have h2' := (Nat.cast_le (α := ℝ)).mpr h2
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at h2'
    have e : ((10 : ℝ) ^ 12) ^ 2 = 10 ^ 24 := by norm_num
    rw [inner_toVec' hu hv, ← absDot_cast_sq, mul_pow, mul_pow, norm_sq_toVec hu,
      norm_sq_toVec hv, div_pow, e, div_mul_eq_mul_div, le_div_iff₀ (by positivity), sq, sq]
    exact h2'

/-- The distance check, in the reals: `2 (t/10^12) S ≤ |u - v|`. -/
theorem le_norm_sub_of_farB (hu : OkVec m u) (hv : OkVec m v) {t S : ℕ}
    (h : farB m (10 ^ 24) (4 * (t * t) * (S * S)) u v = true) :
    2 * ((t : ℝ) / 10 ^ 12) * S ≤ ‖toVec m u - toVec m v‖ := by
  apply le_of_sq_le_sq' (norm_nonneg _)
  have h' := (Nat.cast_le (α := ℝ)).mpr (farB_iff.mp h)
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat] at h'
  rw [norm_sub_sq_toVec hu hv]
  have e : (2 * ((t : ℝ) / 10 ^ 12) * S) ^ 2 * 10 ^ 24 = 4 * ((t : ℝ) * t) * ((S : ℝ) * S) := by
    ring
  have key : (2 * ((t : ℝ) / 10 ^ 12) * S) ^ 2 * 10 ^ 24
      ≤ ((u.nsq : ℝ) + v.nsq - 2 * ((dotX m u v : ℝ) - (dotY u v : ℝ))) * 10 ^ 24 := by
    rw [e]
    linarith
  exact le_of_mul_le_mul_right key (by positivity)

end Vectors

/-! ### Spherical codes -/

/-- The vectors of `c` are nonzero and their pairwise cosines are at most `t`. -/
def SphericalData (m : ℕ) (t : ℝ) (c : List Vec) : Prop :=
  (∀ i : Fin c.length, toVec m (c.get i) ≠ 0) ∧
    ∀ i j : Fin c.length, i ≠ j →
      ⟪toVec m (c.get i), toVec m (c.get j)⟫_ℝ
        ≤ t * (‖toVec m (c.get i)‖ * ‖toVec m (c.get j)‖)

theorem sphericalData_of_check {m N t : ℕ} {c : List Vec} (h : checkSph m N t c = true) :
    c.length = N ∧ SphericalData m ((t : ℝ) / 10 ^ 12) c := by
  obtain ⟨hN, hok, hpair⟩ := checkSph_iff.mp h
  have hok' : ∀ i : Fin c.length, OkVec m (c.get i) ∧ 1 ≤ (c.get i).nsq :=
    fun i => okVec_iff.mp (hok _ (List.get_mem c i))
  have key : ∀ i j : Fin c.length, i < j →
      ⟪toVec m (c.get i), toVec m (c.get j)⟫_ℝ
        ≤ (t : ℝ) / 10 ^ 12 * (‖toVec m (c.get i)‖ * ‖toVec m (c.get j)‖) :=
    fun i j hij => inner_le_of_cosB (hok' i).1 (hok' j).1 (List.pairwise_iff_get.mp hpair i j hij)
  refine ⟨hN, fun i => toVec_ne_zero (hok' i).1 (hok' i).2, fun i j hij => ?_⟩
  rcases lt_or_gt_of_ne hij with h1 | h1
  · exact key i j h1
  · rw [real_inner_comm, mul_comm ‖toVec m (c.get i)‖]
    exact key j i h1

theorem hasSphericalCode_of_data {m : ℕ} {t : ℝ} {c : List Vec} (h : SphericalData m t c) :
    HasSphericalCode m c.length t := by
  obtain ⟨h0, hle⟩ := h
  refine ⟨fun i => ‖toVec m (c.get i)‖⁻¹ • toVec m (c.get i), fun i => ?_, fun i j hij => ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr (h0 i))]
  · have hi : ‖toVec m (c.get i)‖⁻¹ * ‖toVec m (c.get i)‖ = 1 :=
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (h0 i))
    have hj : ‖toVec m (c.get j)‖⁻¹ * ‖toVec m (c.get j)‖ = 1 :=
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (h0 j))
    have hi0 : 0 ≤ ‖toVec m (c.get i)‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
    have hj0 : 0 ≤ ‖toVec m (c.get j)‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
    rw [real_inner_smul_left, real_inner_smul_right]
    calc ‖toVec m (c.get i)‖⁻¹ * (‖toVec m (c.get j)‖⁻¹ * ⟪toVec m (c.get i), toVec m (c.get j)⟫_ℝ)
        ≤ ‖toVec m (c.get i)‖⁻¹ * (‖toVec m (c.get j)‖⁻¹
            * (t * (‖toVec m (c.get i)‖ * ‖toVec m (c.get j)‖))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hle i j hij) hj0) hi0
      _ = t * ((‖toVec m (c.get i)‖⁻¹ * ‖toVec m (c.get i)‖)
            * (‖toVec m (c.get j)‖⁻¹ * ‖toVec m (c.get j)‖)) := by ring
      _ = t := by rw [hi, hj]; ring

/-- **Soundness of `checkSph`.** -/
theorem hasSphericalCode_of_check {m N t : ℕ} {c : List Vec} (h : checkSph m N t c = true) :
    HasSphericalCode m N ((t : ℝ) / 10 ^ 12) := by
  obtain ⟨hN, hd⟩ := sphericalData_of_check h
  subst hN
  exact hasSphericalCode_of_data hd

/-! ### Balls in the unit ball -/

/-- The point of the file that `v` stands for: the integer vector divided by the scale `S`. -/
noncomputable def toPt (m S : ℕ) (v : Vec) : EuclideanSpace ℝ (Fin m) :=
  ((S : ℝ)⁻¹) • toVec m v

/-- The points of `c` are centres of balls of radius `r` inside the unit ball with pairwise
disjoint interiors. -/
def BallData (m S : ℕ) (r : ℝ) (c : List Vec) : Prop :=
  (∀ i : Fin c.length, ‖toPt m S (c.get i)‖ ≤ 1 - r) ∧
    ∀ i j : Fin c.length, i ≠ j → 2 * r ≤ dist (toPt m S (c.get i)) (toPt m S (c.get j))

theorem ballData_of_check {m N t S : ℕ} {c : List Vec} (h : checkBall m N t S c = true) :
    c.length = N ∧ BallData m S ((t : ℝ) / 10 ^ 12) c := by
  obtain ⟨hN, hS, ht, hok, hnorm, hpair⟩ := checkBall_iff.mp h
  have hSR : (0 : ℝ) < S := by exact_mod_cast hS
  have htR : (t : ℝ) / 10 ^ 12 ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact_mod_cast ht
  have hok' : ∀ i : Fin c.length, OkVec m (c.get i) :=
    fun i => okVec0_iff.mp (hok _ (List.get_mem c i))
  have key : ∀ i j : Fin c.length, i < j →
      2 * ((t : ℝ) / 10 ^ 12) ≤ dist (toPt m S (c.get i)) (toPt m S (c.get j)) := by
    intro i j hij
    have hfar := le_norm_sub_of_farB (hok' i) (hok' j) (List.pairwise_iff_get.mp hpair i j hij)
    rw [toPt, toPt, dist_eq_norm, ← smul_sub, norm_smul, norm_inv, Real.norm_natCast,
      le_inv_mul_iff₀ hSR]
    linarith
  refine ⟨hN, fun i => ?_, fun i j hij => ?_⟩
  · have hn := (Nat.cast_le (α := ℝ)).mpr (hnorm _ (List.get_mem c i))
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub ht] at hn
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hn
    have hP : ‖toVec m (c.get i)‖ ≤ (1 - (t : ℝ) / 10 ^ 12) * S := by
      apply le_of_sq_le_sq' (mul_nonneg (by linarith) hSR.le)
      rw [norm_sq_toVec (hok' i)]
      have e : ((1 - (t : ℝ) / 10 ^ 12) * S) ^ 2 * 10 ^ 24
          = ((10 : ℝ) ^ 12 - t) * ((10 : ℝ) ^ 12 - t) * ((S : ℝ) * S) := by ring
      have key2 : ((c.get i).nsq : ℝ) * 10 ^ 24 ≤ ((1 - (t : ℝ) / 10 ^ 12) * S) ^ 2 * 10 ^ 24 := by
        rw [e]
        exact hn
      exact le_of_mul_le_mul_right key2 (by positivity)
    rw [toPt, norm_smul, norm_inv, Real.norm_natCast, inv_mul_le_iff₀ hSR]
    linarith
  · rcases lt_or_gt_of_ne hij with h1 | h1
    · exact key i j h1
    · rw [dist_comm]
      exact key j i h1

theorem hasBallPackingInBall_of_data {m S : ℕ} {r : ℝ} {c : List Vec} (h : BallData m S r c) :
    HasBallPackingInBall m c.length r :=
  ⟨fun i => toPt m S (c.get i), h.1, h.2⟩

/-- **Soundness of `checkBall`.** -/
theorem hasBallPackingInBall_of_check {m N t S : ℕ} {c : List Vec}
    (h : checkBall m N t S c = true) : HasBallPackingInBall m N ((t : ℝ) / 10 ^ 12) := by
  obtain ⟨hN, hd⟩ := ballData_of_check h
  subst hN
  exact hasBallPackingInBall_of_data hd

/-! ### Balls in the unit cube -/

/-- The centre in the unit cube `[0,1]^3` that `v` stands for: the integer vector divided by the
scale `S`, moved from the cube `[-1/2,1/2]^3` of the file by `1/2` in each coordinate. -/
noncomputable def toCubePt (S : ℕ) (v : Vec) : Cube.Pt :=
  Cube.affine (1 / (S : ℝ)) (1 / 2) (toVec 3 v)

theorem cubeData_of_check {N t S : ℕ} {c : List Vec} (h : checkCube N t S c = true) :
    c.length = N ∧
      Cube.IsBallPacking c.length ((t : ℝ) / 10 ^ 12) (fun i => toCubePt S (c.get i)) := by
  obtain ⟨hN, hS, ht, hok, hbox, hpair⟩ := checkCube_iff.mp h
  have hSR : (0 : ℝ) < S := by exact_mod_cast hS
  have hok' : ∀ i : Fin c.length, OkVec 3 (c.get i) :=
    fun i => okVec0_iff.mp (hok _ (List.get_mem c i))
  have key : ∀ i j : Fin c.length, i < j →
      2 * ((t : ℝ) / 10 ^ 12) ≤ dist (toCubePt S (c.get i)) (toCubePt S (c.get j)) := by
    intro i j hij
    have hfar := le_norm_sub_of_farB (hok' i) (hok' j) (List.pairwise_iff_get.mp hpair i j hij)
    apply Cube.le_dist
    rw [toCubePt, toCubePt, Cube.dist_sq_affine, dist_eq_norm, one_div, inv_pow,
      le_inv_mul_iff₀ (by positivity)]
    calc (S : ℝ) ^ 2 * (2 * ((t : ℝ) / 10 ^ 12)) ^ 2 = (2 * ((t : ℝ) / 10 ^ 12) * S) ^ 2 := by
          ring
      _ ≤ ‖toVec 3 (c.get i) - toVec 3 (c.get j)‖ ^ 2 :=
          pow_le_pow_left₀ (by positivity) hfar 2
  refine ⟨hN, fun i k => ?_, fun i j hij => ?_⟩
  · have hlen : (k : ℕ) < (c.get i).e.length := by
      rw [(hok' i).len]
      exact k.isLt
    have hmem : (c.get i).e.getD k 0 ∈ (c.get i).e := by
      rw [List.getD_eq_getElem _ _ hlen]
      exact List.getElem_mem hlen
    obtain ⟨b1, b2⟩ := boxB_iff.mp (hbox _ (List.get_mem c i)) _ hmem
    have c1 := (Nat.cast_le (α := ℝ)).mpr b1
    have c2 := (Nat.cast_le (α := ℝ)).mpr b2
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul,
      Nat.cast_sub ht] at c1 c2
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at c1 c2
    have e : toCubePt S (c.get i) k
        = ((((c.get i).e.getD k 0 : ℕ) : ℝ) - (c.get i).off) / S + 1 / 2 := by
      rw [toCubePt, Cube.affine_apply, toVec_apply]
      ring
    rw [e]
    have hlo : -((1 / 2 - (t : ℝ) / 10 ^ 12)) ≤
        ((((c.get i).e.getD k 0 : ℕ) : ℝ) - (c.get i).off) / S := by
      rw [le_div_iff₀ hSR]
      nlinarith
    have hhi : ((((c.get i).e.getD k 0 : ℕ) : ℝ) - (c.get i).off) / S ≤
        1 / 2 - (t : ℝ) / 10 ^ 12 := by
      rw [div_le_iff₀ hSR]
      nlinarith
    constructor <;> linarith
  · rcases lt_or_gt_of_ne hij with h1 | h1
    · exact key i j h1
    · rw [dist_comm]
      exact key j i h1

/-- **Soundness of `checkCube`.** -/
theorem hasBallPackingInCube_of_check {N t S : ℕ} {c : List Vec}
    (h : checkCube N t S c = true) : HasBallPackingInCube N ((t : ℝ) / 10 ^ 12) := by
  obtain ⟨hN, hd⟩ := cubeData_of_check h
  subst hN
  exact ⟨_, hd⟩

end Cert

end Packing
