/-
The second half of Rankin's orthoplex statement: nonzero vectors with pairwise nonpositive inner
products in a space of dimension `d` number at most `2d`. Hence more than `2d` points on a sphere
include two at squared distance strictly below `2ρ`, and the orthoplex bound for Grassmannian
packings is strict for more than `(m-1)(m+2)` subspaces.
-/
import Packing.Subspace

open Finset Module Matrix
open scoped InnerProductSpace

namespace Packing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `u` with its component along `v` removed. -/
noncomputable def reject (v u : E) : E := u - (⟪v, u⟫_ℝ / ⟪v, v⟫_ℝ) • v

theorem inner_reject_left {v : E} (hv : v ≠ 0) (u : E) : ⟪v, reject v u⟫_ℝ = 0 := by
  have hvv : ⟪v, v⟫_ℝ ≠ 0 := (real_inner_self_pos.mpr hv).ne'
  rw [reject, inner_sub_right, real_inner_smul_right]
  field_simp
  ring

theorem inner_reject_reject {v : E} (hv : v ≠ 0) (u w : E) :
    ⟪reject v u, reject v w⟫_ℝ = ⟪u, w⟫_ℝ - ⟪v, u⟫_ℝ * ⟪v, w⟫_ℝ / ⟪v, v⟫_ℝ := by
  have hvv : ⟪v, v⟫_ℝ ≠ 0 := (real_inner_self_pos.mpr hv).ne'
  simp only [reject, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm v u]
  field_simp
  ring

theorem card_le_two_mul_finrank_aux (d : ℕ) :
    ∀ (W : Submodule ℝ E) [FiniteDimensional ℝ W], finrank ℝ W = d →
      ∀ s : Finset E, (∀ u ∈ s, u ∈ W) → (∀ u ∈ s, u ≠ 0) →
        (∀ u ∈ s, ∀ w ∈ s, u ≠ w → ⟪u, w⟫_ℝ ≤ 0) → s.card ≤ 2 * d := by
  classical
  induction d with
  | zero =>
    intro W _ hW s hsW hs0 _
    have hbot : W = ⊥ := Submodule.finrank_eq_zero.mp hW
    have hs : s = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro u hu
      have h := hsW u hu
      rw [hbot, Submodule.mem_bot] at h
      exact hs0 u hu h
    simp [hs]
  | succ d ih =>
    intro W _ hW s hsW hs0 hneg
    rcases s.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
    · simp
    have hv0 := hs0 v hv
    have hvW := hsW v hv
    have hvv : 0 < ⟪v, v⟫_ℝ := real_inner_self_pos.mpr hv0
    -- the part of `W` orthogonal to `v` has dimension `d`
    have hW' : finrank ℝ ((ℝ ∙ v)ᗮ ⊓ W : Submodule ℝ E) = d := by
      have h := Submodule.finrank_add_inf_finrank_orthogonal (K₁ := ℝ ∙ v) (K₂ := W)
        ((Submodule.span_singleton_le_iff_mem v W).mpr hvW)
      rw [finrank_span_singleton hv0, hW] at h
      omega
    have hrest : ∀ u ∈ s.erase v, u ∈ s ∧ u ≠ v := fun u hu =>
      ⟨Finset.mem_of_mem_erase hu, Finset.ne_of_mem_erase hu⟩
    have hvu : ∀ u ∈ s.erase v, ⟪v, u⟫_ℝ ≤ 0 := fun u hu =>
      hneg v hv u (hrest u hu).1 (hrest u hu).2.symm
    -- removing the component along `v` keeps the inner products nonpositive
    have hrr : ∀ u ∈ s.erase v, ∀ w ∈ s.erase v, u ≠ w →
        ⟪reject v u, reject v w⟫_ℝ ≤ 0 := by
      intro u hu w hw huw
      rw [inner_reject_reject hv0]
      have h1 := hneg u (hrest u hu).1 w (hrest w hw).1 huw
      have h2 : 0 ≤ ⟪v, u⟫_ℝ * ⟪v, w⟫_ℝ / ⟪v, v⟫_ℝ :=
        div_nonneg (mul_nonneg_of_nonpos_of_nonpos (hvu u hu) (hvu w hw)) hvv.le
      linarith
    -- at most one other vector is a multiple of `v`
    have hZ : ((s.erase v).filter fun u => reject v u = 0).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro u hu w hw
      by_contra huw
      rw [Finset.mem_filter] at hu hw
      have key : ∀ z ∈ s.erase v, reject v z = 0 →
          z = (⟪v, z⟫_ℝ / ⟪v, v⟫_ℝ) • v ∧ ⟪v, z⟫_ℝ < 0 := by
        intro z hz hz0
        have ez : z = (⟪v, z⟫_ℝ / ⟪v, v⟫_ℝ) • v := sub_eq_zero.mp hz0
        refine ⟨ez, lt_of_le_of_ne (hvu z hz) fun h0 => ?_⟩
        apply hs0 z (hrest z hz).1
        rw [ez, h0]
        simp
      obtain ⟨eu, hcu⟩ := key u hu.1 hu.2
      obtain ⟨ew, hcw⟩ := key w hw.1 hw.2
      have hpos : 0 < ⟪u, w⟫_ℝ := by
        have e : ⟪u, w⟫_ℝ
            = (⟪v, u⟫_ℝ / ⟪v, v⟫_ℝ) * ((⟪v, w⟫_ℝ / ⟪v, v⟫_ℝ) * ⟪v, v⟫_ℝ) := by
          conv_lhs => rw [eu, ew]
          rw [real_inner_smul_left, real_inner_smul_right]
        rw [e]
        have a := div_neg_of_neg_of_pos hcu hvv
        have b := div_neg_of_neg_of_pos hcw hvv
        have c := mul_pos_of_neg_of_neg a b
        nlinarith
      have := hneg u (hrest u hu.1).1 w (hrest w hw.1).1 huw
      linarith
    -- the others stay distinct after removing the component along `v`
    have hinj : Set.InjOn (reject v) ((s.erase v).filter fun u => ¬ reject v u = 0) := by
      intro u hu w hw h
      by_contra huw
      have hu' := Finset.mem_filter.mp hu
      have hw' := Finset.mem_filter.mp hw
      have hle := hrr u hu'.1 w hw'.1 huw
      rw [h] at hle
      exact hw'.2 (inner_self_eq_zero.mp (le_antisymm hle real_inner_self_nonneg))
    have hcardT := Finset.card_image_of_injOn hinj
    have hsplit := Finset.card_filter_add_card_filter_not (s := s.erase v)
      (fun u => reject v u = 0)
    have hcards := Finset.card_erase_add_one hv
    have hIH := ih ((ℝ ∙ v)ᗮ ⊓ W) hW'
      (((s.erase v).filter fun u => ¬ reject v u = 0).image (reject v)) ?_ ?_ ?_
    · omega
    · intro y hy
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy
      have hu' := Finset.mem_filter.mp hu
      refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
      · exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (inner_reject_left hv0 u)
      · exact W.sub_mem (hsW u (hrest u hu'.1).1) (W.smul_mem _ hvW)
    · intro y hy
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy
      exact (Finset.mem_filter.mp hu).2
    · intro y hy z hz hyz
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
      exact hrr u (Finset.mem_filter.mp hu).1 w (Finset.mem_filter.mp hw).1
        fun h => hyz (h ▸ rfl)

variable {ι : Type*} [Fintype ι]

/-- Nonzero vectors with pairwise nonpositive inner products in a subspace of dimension `d`
number at most `2d`. -/
theorem card_le_two_mul_finrank_of_mem (W : Submodule ℝ E) [FiniteDimensional ℝ W] (x : ι → E)
    (hW : ∀ i, x i ∈ W) (h0 : ∀ i, x i ≠ 0) (h : ∀ i j, i ≠ j → ⟪x i, x j⟫_ℝ ≤ 0) :
    Fintype.card ι ≤ 2 * finrank ℝ W := by
  classical
  have hinj : Function.Injective x := by
    intro i j hij
    by_contra hne
    have hle := h i j hne
    rw [hij] at hle
    exact h0 j (inner_self_eq_zero.mp (le_antisymm hle real_inner_self_nonneg))
  have key := card_le_two_mul_finrank_aux (finrank ℝ W) W rfl (Finset.univ.image x)
    (fun u hu => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hu
      exact hW i)
    (fun u hu => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hu
      exact h0 i)
    (fun u hu w hw huw => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hw
      exact h i j fun hij => huw (hij ▸ rfl))
  rwa [Finset.card_image_of_injective _ hinj, Finset.card_univ] at key

/-- **Rankin's orthoplex bound, strict part.** Among more than `2d` points on the sphere of
squared radius `ρ > 0` in a subspace of dimension `d`, some two distinct points are at squared
distance strictly less than `2ρ`. -/
theorem rankin_orthoplex_strict_of_mem (W : Submodule ℝ E) [FiniteDimensional ℝ W] (x : ι → E)
    (ρ : ℝ) (hρ : 0 < ρ) (hW : ∀ i, x i ∈ W) (hx : ∀ i, ‖x i‖ ^ 2 = ρ)
    (hN : 2 * finrank ℝ W < Fintype.card ι) :
    ∃ i j, i ≠ j ∧ ‖x i - x j‖ ^ 2 < 2 * ρ := by
  by_contra hcon
  push Not at hcon
  have h : ∀ i j, i ≠ j → ⟪x i, x j⟫_ℝ ≤ 0 := by
    intro i j hij
    have := hcon i j hij
    rw [norm_sub_sq_real, hx i, hx j] at this
    linarith
  have h0 : ∀ i, x i ≠ 0 := by
    intro i hi
    have := hx i
    rw [hi] at this
    simp at this
    linarith
  have := card_le_two_mul_finrank_of_mem W x hW h0 h
  omega

/-- The strict part for points of a finite-dimensional space. -/
theorem rankin_orthoplex_strict [FiniteDimensional ℝ E] (x : ι → E) (ρ : ℝ) (hρ : 0 < ρ)
    (hx : ∀ i, ‖x i‖ ^ 2 = ρ) (hN : 2 * finrank ℝ E < Fintype.card ι) :
    ∃ i j, i ≠ j ∧ ‖x i - x j‖ ^ 2 < 2 * ρ :=
  rankin_orthoplex_strict_of_mem ⊤ x ρ hρ (fun _ => Submodule.mem_top) hx
    (by rwa [finrank_top])

/-- **The orthoplex bound for Grassmannian packings, strict part** (Conway, Hardin and Sloane
1996, Corollary 5.2). Among more than `(m-1)(m+2)` subspaces of dimension `n` in `ℝ^m`, with
`0 < n < m`, some two distinct ones are at squared chordal distance strictly less than
`n(m-n)/m`. Here `(m-1)(m+2)` is written `2 (m(m+1)/2 - 1)`. -/
theorem chs_orthoplex_strict {m : ℕ} (n : ℕ) (hn : 0 < n) (hnm : n < m)
    (P : ι → Matrix (Fin m) (Fin m) ℝ) (hP : ∀ i, IsProjector (P i) n)
    (hN : 2 * ((m + 1).choose 2 - 1) < Fintype.card ι) :
    ∃ i j, i ≠ j ∧ chordalSq (P i) (P j) < (n : ℝ) * (m - n) / m := by
  have hm : 0 < m := by omega
  have hρ : (0 : ℝ) < (n : ℝ) * (m - n) / m := by
    have h1 : (0 : ℝ) < n := by exact_mod_cast hn
    have h2 : (n : ℝ) < m := by exact_mod_cast hnm
    have h3 : (0 : ℝ) < m := by exact_mod_cast hm
    exact div_pos (mul_pos h1 (by linarith)) h3
  let W : Submodule ℝ (EuclideanSpace ℝ (Fin m × Fin m)) := (symTraceless m).map vec
  have hW : 2 * finrank ℝ W < Fintype.card ι := by
    have h1 : finrank ℝ W ≤ finrank ℝ (symTraceless m) := Submodule.finrank_map_le _ _
    have h2 := finrank_symTraceless_add_one_le hm
    omega
  obtain ⟨i, j, hij, h⟩ :=
    rankin_orthoplex_strict_of_mem W
      (fun i => vec (P i - ((n : ℝ) / m) • (1 : Matrix (Fin m) (Fin m) ℝ)))
      ((n : ℝ) * (m - n) / m) hρ
      (fun i => Submodule.mem_map_of_mem (shift_mem_symTraceless hm (hP i)))
      (fun i => norm_sq_vec_shift hm (hP i)) hW
  refine ⟨i, j, hij, ?_⟩
  rw [norm_sq_vec_sub] at h
  have e : chordalSq (P i - ((n : ℝ) / m) • (1 : Matrix (Fin m) (Fin m) ℝ))
      (P j - ((n : ℝ) / m) • (1 : Matrix (Fin m) (Fin m) ℝ)) = chordalSq (P i) (P j) := by
    unfold chordalSq; rw [sub_sub_sub_cancel_right]
  rw [e] at h
  linarith

/-- The strict part of the orthoplex bound for subspaces of `ℝ^m` of dimension `n`. -/
theorem chs_orthoplex_strict_subspace {m : ℕ} (n : ℕ) (hn : 0 < n) (hnm : n < m)
    (U : ι → Submodule ℝ (EuclideanSpace ℝ (Fin m))) (hU : ∀ i, finrank ℝ (U i) = n)
    (hN : 2 * ((m + 1).choose 2 - 1) < Fintype.card ι) :
    ∃ i j, i ≠ j ∧ subspaceChordalSq (U i) (U j) < (n : ℝ) * (m - n) / m :=
  chs_orthoplex_strict n hn hnm (fun i => projMatrix (U i))
    (fun i => hU i ▸ isProjector_projMatrix (U i)) hN

end Packing
