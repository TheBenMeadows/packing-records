/-
Soundness of `Packing.Cert.checkLink`: together with a passing `check` on the frames, a passing
link check shows that the spans of the file's own vectors have dimension `n` and are pairwise at
squared chordal distance at least `k / 10^10`.
-/
import Packing.Cert.SoundPoints
import Packing.Cert.CheckLink

open Module
open scoped InnerProductSpace

namespace Packing.Cert

/-! ### Lists taken in step -/

section Lists

variable {α β γ : Type}

theorem all2_forall₂ {f : α → β → Bool} :
    ∀ {xs : List α} {ys : List β}, all2 f xs ys = true →
      List.Forall₂ (fun a b => f a b = true) xs ys
  | [], [], _ => List.Forall₂.nil
  | [], _ :: _, h => Bool.noConfusion (h : false = true)
  | _ :: _, [], h => Bool.noConfusion (h : false = true)
  | a :: as, b :: bs, h => by
    have h' : andB (f a b) (all2 f as bs) = true := h
    rw [andB_eq_true] at h'
    exact List.Forall₂.cons h'.1 (all2_forall₂ h'.2)

theorem all3_forall₂ {f : α → β → γ → Bool} {P : α → β → Prop}
    (hP : ∀ a b c, f a b c = true → P a b) :
    ∀ {xs : List α} {ys : List β} {zs : List γ}, all3 f xs ys zs = true → List.Forall₂ P xs ys
  | [], [], [], _ => List.Forall₂.nil
  | [], [], _ :: _, h => Bool.noConfusion (h : false = true)
  | [], _ :: _, _, h => Bool.noConfusion (h : false = true)
  | _ :: _, [], _, h => Bool.noConfusion (h : false = true)
  | _ :: _, _ :: _, [], h => Bool.noConfusion (h : false = true)
  | a :: as, b :: bs, c :: cs, h => by
    have h' : andB (f a b c) (all3 f as bs cs) = true := h
    rw [andB_eq_true] at h'
    exact List.Forall₂.cons (hP a b c h'.1) (all3_forall₂ hP h'.2)

theorem exists_of_forall₂ {P : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ P xs ys) : ∀ x ∈ xs, ∃ y, P x y := by
  induction h with
  | nil =>
    intro x hx
    simp at hx
  | cons hab _ ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact ⟨_, hab⟩
    · exact ih x hx'

end Lists

/-! ### One frame vector -/

section Link

variable {m : ℕ}

theorem colSum_nil (c : ℕ) (sel : ℕ × ℕ → ℕ) (rows : List Vec) : colSum c sel [] rows = 0 := rfl
theorem colSum_cons_nil (c : ℕ) (sel : ℕ × ℕ → ℕ) (x : ℕ × ℕ) (xs : List (ℕ × ℕ)) :
    colSum c sel (x :: xs) [] = 0 := rfl
theorem colSum_cons_cons (c : ℕ) (sel : ℕ × ℕ → ℕ) (x : ℕ × ℕ) (xs : List (ℕ × ℕ)) (b : Vec)
    (bs : List Vec) :
    colSum c sel (x :: xs) (b :: bs) = sel x * b.e.getD c 0 + colSum c sel xs bs := rfl
theorem offSum_nil (sel : ℕ × ℕ → ℕ) (rows : List Vec) : offSum sel [] rows = 0 := rfl
theorem offSum_cons_nil (sel : ℕ × ℕ → ℕ) (x : ℕ × ℕ) (xs : List (ℕ × ℕ)) :
    offSum sel (x :: xs) [] = 0 := rfl
theorem offSum_cons_cons (sel : ℕ × ℕ → ℕ) (x : ℕ × ℕ) (xs : List (ℕ × ℕ)) (b : Vec)
    (bs : List Vec) : offSum sel (x :: xs) (b :: bs) = sel x * b.off + offSum sel xs bs := rfl

theorem linkVec_iff {rows : List Vec} {w : Vec} {k : Coef} :
    linkVec m rows w k = true ↔ 1 ≤ k.g ∧ ∀ c ∈ List.range m,
      k.g * w.e.getD c 0 + colSum c Prod.snd k.pq rows + offSum Prod.fst k.pq rows
        = k.g * w.off + colSum c Prod.fst k.pq rows + offSum Prod.snd k.pq rows := by
  unfold linkVec
  simp only [andB_eq_true, allB_eq_true, beq_iff, Nat.ble_eq]
  exact Iff.rfl

/-- The real combination `∑ (pₖ - qₖ) · bₖ`. -/
noncomputable def comb (m : ℕ) : List (ℕ × ℕ) → List Vec → EuclideanSpace ℝ (Fin m)
  | x :: xs, b :: bs => ((x.1 : ℝ) - x.2) • toVec m b + comb m xs bs
  | [], _ => 0
  | _ :: _, [] => 0

theorem comb_mem (W : Submodule ℝ (EuclideanSpace ℝ (Fin m))) :
    ∀ (pq : List (ℕ × ℕ)) (rows : List Vec), (∀ b ∈ rows, toVec m b ∈ W) → comb m pq rows ∈ W
  | [], _, _ => by
    rw [comb]
    exact W.zero_mem
  | _ :: _, [], _ => by
    rw [comb]
    exact W.zero_mem
  | x :: xs, b :: bs, h => by
    rw [comb]
    exact W.add_mem (W.smul_mem _ (h b (by simp)))
      (comb_mem W xs bs fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))

theorem comb_apply (c : Fin m) : ∀ (pq : List (ℕ × ℕ)) (rows : List Vec),
    comb m pq rows c
      = ((colSum c Prod.fst pq rows : ℕ) : ℝ) + (offSum Prod.snd pq rows : ℕ)
        - (((colSum c Prod.snd pq rows : ℕ) : ℝ) + (offSum Prod.fst pq rows : ℕ))
  | [], rows => by
    rw [comb, colSum_nil, colSum_nil, offSum_nil, offSum_nil]
    simp
  | x :: xs, [] => by
    rw [comb, colSum_cons_nil, colSum_cons_nil, offSum_cons_nil, offSum_cons_nil]
    simp
  | x :: xs, b :: bs => by
    have ih := comb_apply c xs bs
    rw [comb, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, toVec_apply, ih, colSum_cons_cons,
      colSum_cons_cons, offSum_cons_cons, offSum_cons_cons]
    push_cast
    ring

/-- A linked frame vector lies in every subspace that contains the file's vectors. -/
theorem toVec_mem_of_linkVec {rows : List Vec} {w : Vec} {k : Coef}
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin m))) (hW : ∀ b ∈ rows, toVec m b ∈ W)
    (h : linkVec m rows w k = true) : toVec m w ∈ W := by
  obtain ⟨hg, hc⟩ := linkVec_iff.mp h
  have hgR : (0 : ℝ) < k.g := by exact_mod_cast hg
  have e : (k.g : ℝ) • toVec m w = comb m k.pq rows := by
    ext c
    have h' := congrArg (Nat.cast (R := ℝ)) (hc c (List.mem_range.mpr c.isLt))
    push_cast at h'
    rw [PiLp.smul_apply, smul_eq_mul, toVec_apply, comb_apply]
    linarith
  have e2 : toVec m w = (k.g : ℝ)⁻¹ • comb m k.pq rows := by
    rw [← e, smul_smul, inv_mul_cancel₀ hgR.ne', one_smul]
  rw [e2]
  exact W.smul_mem _ (comb_mem W _ _ hW)

/-! ### Frames -/

theorem mem_frameSpan {F : Frame} {v : Vec} (hv : v ∈ F) : toVec m v ∈ frameSpan m F := by
  obtain ⟨i, h, rfl⟩ := List.mem_iff_getElem.mp hv
  exact Submodule.subset_span ⟨⟨i, h⟩, rfl⟩

theorem frameSpan_le {F : Frame} {W : Submodule ℝ (EuclideanSpace ℝ (Fin m))}
    (h : ∀ v ∈ F, toVec m v ∈ W) : frameSpan m F ≤ W := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨a, rfl⟩
  exact h _ (List.get_mem F a)

theorem finrank_frameSpan_le (F : Frame) : finrank ℝ (frameSpan m F) ≤ F.length := by
  exact (finrank_range_le_card (R := ℝ) (fam m F)).trans (Fintype.card_fin _).le

theorem linkFrame_iff {n : ℕ} {rows frame : List Vec} {ks : List Coef} :
    linkFrame m n rows frame ks = true ↔ rows.length = n ∧ (∀ b ∈ rows, okVec0 m b = true) ∧
      all2 (linkVec m rows) frame ks = true := by
  unfold linkFrame
  simp only [andB_eq_true, allB_eq_true, beq_iff, sumMap_one]

/-- A frame of `n` orthogonal nonzero vectors that is linked to `n` file vectors spans the same
subspace as they do. -/
theorem frameSpan_eq_of_link {n : ℕ} {rows frame : List Vec} {ks : List Coef}
    (hF : OkFrame m frame) (hFn : frame.length = n) (h : linkFrame m n rows frame ks = true) :
    frameSpan m rows = frameSpan m frame := by
  obtain ⟨hn, -, h2⟩ := linkFrame_iff.mp h
  have hle : frameSpan m frame ≤ frameSpan m rows := by
    apply frameSpan_le
    intro w hw
    obtain ⟨k, hk⟩ := exists_of_forall₂ (all2_forall₂ h2) w hw
    exact toVec_mem_of_linkVec _ (fun b hb => mem_frameSpan hb) hk
  symm
  apply Submodule.eq_of_le_of_finrank_le hle
  rw [finrank_frameSpan hF, hFn, ← hn]
  exact finrank_frameSpan_le rows

end Link

/-- **Soundness of `checkLink`.** If `check m n N k c` and `checkLink m n R c K` both evaluate
to `true`, then `R` holds `N` lists of vectors whose spans have dimension `n` and are pairwise at
squared chordal distance at least `k / 10^10`. -/
theorem spansPack_of_link {m n N k : ℕ} {R c : List Frame} {K : List (List Coef)}
    (hc : check m n N k c = true) (hl : checkLink m n R c K = true) :
    R.length = N ∧ SpansPack m n ((k : ℝ) / 10 ^ 10) R := by
  obtain ⟨hN, hok, hfin, hpair⟩ := spansPack_of_check hc
  have hF₂ : List.Forall₂ (fun rows frame => ∃ ks, linkFrame m n rows frame ks = true) R c :=
    all3_forall₂ (fun _ _ ks h => ⟨ks, h⟩) hl
  obtain ⟨hlen, hget⟩ := List.forall₂_iff_get.mp hF₂
  have heq : ∀ i : Fin R.length,
      frameSpan m (R.get i) = frameSpan m (c.get ⟨i, hlen ▸ i.isLt⟩) := by
    intro i
    obtain ⟨ks, hks⟩ := hget i i.isLt (hlen ▸ i.isLt)
    exact frameSpan_eq_of_link (hok _).2 (hok _).1 hks
  refine ⟨hlen.trans hN, fun i => ?_, fun i j hij => ?_⟩
  · rw [heq i]
    exact hfin _
  · rw [heq i, heq j]
    exact hpair _ _ fun h => hij (Fin.ext (by simpa using congrArg Fin.val h))

end Packing.Cert
