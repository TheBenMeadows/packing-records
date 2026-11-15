/-
Soundness of the checker `Packing.Cert.check`: if it returns `true`, there are `N` subspaces of
dimension `n` in `ℝ^m` that are pairwise at squared chordal distance at least `k / 10^10`.
-/
import Packing.Frame
import Packing.Cert.Check

open Module Matrix
open scoped InnerProductSpace

namespace Packing

/-- There are `N` subspaces of dimension `n` in `ℝ^m` that are pairwise at squared chordal
distance at least `t`. -/
def HasPacking (m n N : ℕ) (t : ℝ) : Prop :=
  ∃ U : Fin N → Submodule ℝ (EuclideanSpace ℝ (Fin m)),
    (∀ i, finrank ℝ (U i) = n) ∧ ∀ i j, i ≠ j → t ≤ subspaceChordalSq (U i) (U j)

theorem subspaceChordalSq_comm {m : ℕ} (U V : Submodule ℝ (EuclideanSpace ℝ (Fin m))) :
    subspaceChordalSq U V = subspaceChordalSq V U := by
  unfold subspaceChordalSq chordalSq
  have h : projMatrix U - projMatrix V = -(projMatrix V - projMatrix U) := (neg_sub _ _).symm
  rw [h, transpose_neg, neg_mul_neg]

namespace Cert

/-! ### The definitions in ordinary notation -/

section Unfold

variable {α : Type}

theorem dotN_nil (ys : List ℕ) : dotN [] ys = 0 := rfl
theorem dotN_cons_cons (a : ℕ) (as : List ℕ) (b : ℕ) (bs : List ℕ) :
    dotN (a :: as) (b :: bs) = a * b + dotN as bs := rfl
theorem sumMap_nil (f : α → ℕ) : sumMap f [] = 0 := rfl
theorem sumMap_cons (f : α → ℕ) (a : α) (l : List α) :
    sumMap f (a :: l) = f a + sumMap f l := rfl
theorem dotX_eq (m : ℕ) (u v : Vec) : dotX m u v = dotN u.e v.e + m * (u.off * v.off) := rfl
theorem dotY_eq (u v : Vec) : dotY u v = v.off * u.sum + u.off * v.sum := rfl
theorem absDot_eq (m : ℕ) (u v : Vec) :
    absDot m u v = (dotX m u v - dotY u v) + (dotY u v - dotX m u v) := rfl
theorem term_eq (m D : ℕ) (u v : Vec) :
    term m D u v = absDot m u v * absDot m u v * D / (u.nsq * v.nsq) + 1 := rfl

theorem beq_iff {a b : ℕ} : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

theorem andB_eq_true {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a
  · exact ⟨fun h => Bool.noConfusion (h : false = true), fun h => Bool.noConfusion h.1⟩
  · exact ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩

theorem allB_eq_true {f : α → Bool} {l : List α} :
    allB f l = true ↔ ∀ x ∈ l, f x = true := by
  induction l with
  | nil => exact ⟨fun _ x hx => by simp at hx, fun _ => rfl⟩
  | cons a l ih =>
    have h : allB f (a :: l) = andB (f a) (allB f l) := rfl
    rw [h, andB_eq_true, ih]
    simp

theorem pairwiseB_eq_true {r : α → α → Bool} {l : List α} :
    pairwiseB r l = true ↔ l.Pairwise (fun a b => r a b = true) := by
  induction l with
  | nil => exact ⟨fun _ => List.Pairwise.nil, fun _ => rfl⟩
  | cons a l ih =>
    have h : pairwiseB r (a :: l) = andB (allB (r a) l) (pairwiseB r l) := rfl
    rw [h, andB_eq_true, allB_eq_true, ih, List.pairwise_cons]

theorem sumMap_one (l : List α) : sumMap (fun _ => 1) l = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [sumMap_cons, ih, List.length_cons, Nat.add_comm]

theorem sumMap_cast (f : α → ℕ) (l : List α) :
    ((sumMap f l : ℕ) : ℝ) = ∑ a : Fin l.length, (f (l.get a) : ℝ) := by
  induction l with
  | nil => simp [sumMap_nil]
  | cons x l ih =>
    rw [sumMap_cons, Nat.cast_add, ih]
    show _ = ∑ a : Fin (l.length + 1), (f ((x :: l).get a) : ℝ)
    rw [Fin.sum_univ_succ]
    simp

end Unfold

/-! ### What the checks mean -/

/-- The vector of `ℝ^m` that `v` stands for. -/
noncomputable def toVec (m : ℕ) (v : Vec) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 fun i => ((v.e.getD i 0 : ℕ) : ℝ) - v.off

theorem sum_mul_getD (B C : ℝ) : ∀ (m : ℕ) (xs ys : List ℕ), xs.length = m → ys.length = m →
    ∑ i : Fin m, (((xs.getD i 0 : ℕ) : ℝ) - B) * (((ys.getD i 0 : ℕ) : ℝ) - C)
      = (dotN xs ys : ℝ) + m * B * C - C * (sumMap (fun x => x) xs : ℕ)
        - B * (sumMap (fun x => x) ys : ℕ)
  | 0, xs, ys, hx, hy => by
    have hx' : xs = [] := List.eq_nil_of_length_eq_zero hx
    have hy' : ys = [] := List.eq_nil_of_length_eq_zero hy
    subst hx' hy'
    simp [dotN_nil, sumMap_nil]
  | m + 1, [], _, hx, _ => by simp at hx
  | m + 1, _ :: _, [], _, hy => by simp at hy
  | m + 1, x :: xs, y :: ys, hx, hy => by
    have ih := sum_mul_getD B C m xs ys (by simpa using hx) (by simpa using hy)
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, List.getD_cons_zero, List.getD_cons_succ,
      dotN_cons_cons, sumMap_cons]
    rw [ih]
    push_cast
    ring

theorem inner_toVec {m : ℕ} {u v : Vec} (hu : u.e.length = m) (hv : v.e.length = m)
    (hus : sumMap (fun x => x) u.e = u.sum) (hvs : sumMap (fun x => x) v.e = v.sum) :
    ⟪toVec m u, toVec m v⟫_ℝ = (dotX m u v : ℝ) - (dotY u v : ℝ) := by
  rw [inner_eq_dotProduct]
  simp only [toVec, dotProduct]
  rw [sum_mul_getD _ _ m u.e v.e hu hv, hus, hvs, dotX_eq, dotY_eq]
  push_cast
  ring

/-- What `okVec` and the orthogonality check establish for a frame. -/
structure OkFrame (m : ℕ) (F : Frame) : Prop where
  len : ∀ v ∈ F, v.e.length = m
  sum : ∀ v ∈ F, sumMap (fun x => x) v.e = v.sum
  nsq : ∀ v ∈ F, v.nsq + dotY v v = dotX m v v
  pos : ∀ v ∈ F, 1 ≤ v.nsq
  orth : F.Pairwise fun u v => dotX m u v = dotY u v

theorem okFrame_iff {m n : ℕ} {F : Frame} :
    okFrame m n F = true ↔ F.length = n ∧ OkFrame m F := by
  unfold okFrame
  simp only [andB_eq_true, allB_eq_true, pairwiseB_eq_true, beq_iff, sumMap_one]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, ?_, ?_, ?_, h3⟩
    all_goals
      intro v hv
      have := h2 v hv
      unfold okVec at this
      simp only [andB_eq_true, beq_iff, Nat.ble_eq, sumMap_one] at this
    · exact this.1
    · exact this.2.1
    · exact this.2.2.1
    · exact this.2.2.2
  · rintro ⟨h1, h⟩
    refine ⟨h1, fun v hv => ?_, h.orth⟩
    unfold okVec
    simp only [andB_eq_true, beq_iff, Nat.ble_eq, sumMap_one]
    exact ⟨h.len v hv, h.sum v hv, h.nsq v hv, h.pos v hv⟩

/-- The vectors of `ℝ^m` that the members of a frame stand for. -/
noncomputable def fam (m : ℕ) (F : Frame) : Fin F.length → EuclideanSpace ℝ (Fin m) :=
  fun a => toVec m (F.get a)

/-- The subspace of `ℝ^m` spanned by a frame. -/
noncomputable def frameSpan (m : ℕ) (F : Frame) : Submodule ℝ (EuclideanSpace ℝ (Fin m)) :=
  Submodule.span ℝ (Set.range (fam m F))

section Frames

variable {m : ℕ} {F G : Frame}

theorem inner_fam (hF : OkFrame m F) (hG : OkFrame m G) (a : Fin F.length) (b : Fin G.length) :
    ⟪fam m F a, fam m G b⟫_ℝ
      = (dotX m (F.get a) (G.get b) : ℝ) - (dotY (F.get a) (G.get b) : ℝ) :=
  inner_toVec (hF.len _ (List.get_mem F a)) (hG.len _ (List.get_mem G b))
    (hF.sum _ (List.get_mem F a)) (hG.sum _ (List.get_mem G b))

theorem inner_fam_self (hF : OkFrame m F) (a : Fin F.length) :
    ⟪fam m F a, fam m F a⟫_ℝ = ((F.get a).nsq : ℝ) := by
  rw [inner_fam hF hF, ← hF.nsq _ (List.get_mem F a)]
  push_cast
  ring

theorem fam_pos (hF : OkFrame m F) (a : Fin F.length) : 0 < ⟪fam m F a, fam m F a⟫_ℝ := by
  rw [inner_fam_self hF]
  exact_mod_cast hF.pos _ (List.get_mem F a)

theorem fam_orth (hF : OkFrame m F) : Pairwise fun a b => ⟪fam m F a, fam m F b⟫_ℝ = 0 := by
  have key : ∀ a b : Fin F.length, a < b → ⟪fam m F a, fam m F b⟫_ℝ = 0 := by
    intro a b hab
    have h := List.pairwise_iff_get.mp hF.orth a b hab
    rw [inner_fam hF hF, h, sub_self]
  intro a b hab
  rcases lt_or_gt_of_ne hab with h | h
  · exact key a b h
  · rw [real_inner_comm]
    exact key b a h

theorem finrank_frameSpan (hF : OkFrame m F) : finrank ℝ (frameSpan m F) = F.length :=
  finrank_span_frame (fam m F) (fam_orth hF) (fam_pos hF)

theorem absDot_cast_sq (u v : Vec) :
    ((absDot m u v : ℕ) : ℝ) ^ 2 = ((dotX m u v : ℝ) - (dotY u v : ℝ)) ^ 2 := by
  rw [absDot_eq]
  rcases le_total (dotX m u v) (dotY u v) with h | h
  · rw [Nat.sub_eq_zero_of_le h, zero_add, Nat.cast_sub h]
    ring
  · rw [Nat.sub_eq_zero_of_le h, add_zero, Nat.cast_sub h]

theorem term_bound {D : ℕ} (hD : 0 < D) {u v : Vec} (hu : 1 ≤ u.nsq) (hv : 1 ≤ v.nsq) :
    ((dotX m u v : ℝ) - (dotY u v : ℝ)) ^ 2 / ((u.nsq : ℝ) * v.nsq)
      ≤ (term m D u v : ℝ) / D := by
  have hb : 0 < u.nsq * v.nsq := Nat.mul_pos hu hv
  have h1 : absDot m u v * absDot m u v * D
      < (absDot m u v * absDot m u v * D / (u.nsq * v.nsq) + 1) * (u.nsq * v.nsq) := by
    calc absDot m u v * absDot m u v * D
        = u.nsq * v.nsq * (absDot m u v * absDot m u v * D / (u.nsq * v.nsq))
          + absDot m u v * absDot m u v * D % (u.nsq * v.nsq) := (Nat.div_add_mod _ _).symm
      _ < u.nsq * v.nsq * (absDot m u v * absDot m u v * D / (u.nsq * v.nsq))
          + u.nsq * v.nsq := Nat.add_lt_add_left (Nat.mod_lt _ hb) _
      _ = _ := by ring
  have h2 : ((absDot m u v : ℕ) : ℝ) ^ 2 * D < (term m D u v : ℝ) * ((u.nsq : ℝ) * v.nsq) := by
    rw [term_eq]
    have := (Nat.cast_lt (α := ℝ)).mpr h1
    push_cast at this ⊢
    nlinarith [this]
  have hbR : (0 : ℝ) < (u.nsq : ℝ) * v.nsq := by exact_mod_cast hb
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  rw [← absDot_cast_sq, div_le_div_iff₀ hbR hDR]
  exact h2.le

/-- The trace term of two frames is bounded by the integer the checker computes. -/
theorem sum_le_pairSum (hF : OkFrame m F) (hG : OkFrame m G) {D : ℕ} (hD : 0 < D) :
    ∑ a, ∑ b, ⟪fam m F a, fam m G b⟫_ℝ ^ 2
        / (⟪fam m F a, fam m F a⟫_ℝ * ⟪fam m G b, fam m G b⟫_ℝ)
      ≤ (pairSum m D F G : ℝ) / D := by
  unfold pairSum
  rw [sumMap_cast, Finset.sum_div]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [sumMap_cast, Finset.sum_div]
  refine Finset.sum_le_sum fun b _ => ?_
  rw [inner_fam hF hG, inner_fam_self hF, inner_fam_self hG]
  exact term_bound hD (hF.pos _ (List.get_mem F a)) (hG.pos _ (List.get_mem G b))

/-- The squared chordal distance between the spans of two frames of `n` vectors is at least
`n - pairSum / D`. -/
theorem le_subspaceChordalSq (hF : OkFrame m F) (hG : OkFrame m G) {n D : ℕ} (hD : 0 < D)
    (hFn : F.length = n) (hGn : G.length = n) :
    (n : ℝ) - (pairSum m D F G : ℝ) / D ≤ subspaceChordalSq (frameSpan m F) (frameSpan m G) := by
  unfold frameSpan
  rw [subspaceChordalSq_span_frames (fam m F) (fam m G) (fam_orth hF) (fam_pos hF)
    (fam_orth hG) (fam_pos hG)]
  have e1 : ((F.length : ℕ) : ℝ) = n := by exact_mod_cast hFn
  have e2 : ((G.length : ℕ) : ℝ) = n := by exact_mod_cast hGn
  have := sum_le_pairSum hF hG hD
  linarith

end Frames

theorem check_iff {m n N k : ℕ} {c : List Frame} :
    check m n N k c = true ↔ c.length = N ∧ k ≤ n * 10 ^ 10 ∧
      (∀ F ∈ c, okFrame m n F = true) ∧
      c.Pairwise fun F G => pairSum m (10 ^ 40) F G ≤ (n * 10 ^ 10 - k) * 10 ^ 30 := by
  unfold check
  simp only [andB_eq_true, allB_eq_true, pairwiseB_eq_true, beq_iff, Nat.ble_eq,
    sumMap_one]
  exact Iff.rfl

/-- `R` holds `N` lists of `n` vectors with `m` entries each; the span of each list has
dimension `n`, and every two spans are at squared chordal distance at least `t`. -/
def SpansPack (m n N : ℕ) (t : ℝ) (R : List Frame) : Prop :=
  R.length = N ∧
    (∀ i : Fin R.length, (R.get i).length = n ∧ ∀ v ∈ R.get i, v.e.length = m) ∧
    (∀ i : Fin R.length, finrank ℝ (frameSpan m (R.get i)) = n) ∧
    ∀ i j : Fin R.length, i ≠ j →
      t ≤ subspaceChordalSq (frameSpan m (R.get i)) (frameSpan m (R.get j))

/-- What a passing check says about the data: `N` frames of `n` pairwise orthogonal nonzero
vectors whose spans have dimension `n` and are pairwise at squared chordal distance at least
`k / 10^10`. -/
theorem spansPack_of_check {m n N k : ℕ} {c : List Frame} (h : check m n N k c = true) :
    (∀ i : Fin c.length, (c.get i).length = n ∧ OkFrame m (c.get i)) ∧
      SpansPack m n N ((k : ℝ) / 10 ^ 10) c := by
  obtain ⟨hN, hk, hok, hpair⟩ := check_iff.mp h
  have hok' : ∀ i : Fin c.length, (c.get i).length = n ∧ OkFrame m (c.get i) :=
    fun i => okFrame_iff.mp (hok _ (List.get_mem c i))
  have key : ∀ i j : Fin c.length, i < j →
      (k : ℝ) / 10 ^ 10 ≤ subspaceChordalSq (frameSpan m (c.get i)) (frameSpan m (c.get j)) := by
    intro i j hij
    have hp := List.pairwise_iff_get.mp hpair i j hij
    have hle := le_subspaceChordalSq (hok' i).2 (hok' j).2 (D := 10 ^ 40) (by positivity)
      (hok' i).1 (hok' j).1
    refine le_trans ?_ hle
    have hp' : (pairSum m (10 ^ 40) (c.get i) (c.get j) : ℝ)
        ≤ ((n : ℝ) * 10 ^ 10 - k) * 10 ^ 30 := by
      have := (Nat.cast_le (α := ℝ)).mpr hp
      rw [Nat.cast_mul, Nat.cast_sub hk, Nat.cast_mul] at this
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using this
    have h40 : ((10 ^ 40 : ℕ) : ℝ) = 10 ^ 40 := by
      simp only [Nat.cast_pow, Nat.cast_ofNat]
    rw [h40]
    have : (pairSum m (10 ^ 40) (c.get i) (c.get j) : ℝ) / 10 ^ 40
        ≤ ((n : ℝ) * 10 ^ 10 - k) * 10 ^ 30 / 10 ^ 40 :=
      div_le_div_of_nonneg_right hp' (by positivity)
    have e : ((n : ℝ) * 10 ^ 10 - k) * 10 ^ 30 / 10 ^ 40 = n - (k : ℝ) / 10 ^ 10 := by
      ring
    linarith
  refine ⟨hok', hN, fun i => ⟨(hok' i).1, (hok' i).2.len⟩, fun i => ?_, fun i j hij => ?_⟩
  · rw [finrank_frameSpan (hok' i).2, (hok' i).1]
  · rcases lt_or_gt_of_ne hij with h | h
    · exact key i j h
    · rw [subspaceChordalSq_comm]
      exact key j i h

/-- **Soundness of the checker.** If `check m n N k c` evaluates to `true`, there are `N`
subspaces of dimension `n` in `ℝ^m` that are pairwise at squared chordal distance at least
`k / 10^10`. -/
theorem hasPacking_of_check {m n N k : ℕ} {c : List Frame} (h : check m n N k c = true) :
    HasPacking m n N ((k : ℝ) / 10 ^ 10) := by
  obtain ⟨-, hN, -, h1, h2⟩ := spansPack_of_check h
  subst hN
  exact ⟨fun i => frameSpan m (c.get i), h1, h2⟩

end Cert

end Packing
