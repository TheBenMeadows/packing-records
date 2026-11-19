/-
Ten points in the unit cube: from the checked case analysis to the bound `3/4`.

Each point gets a key in `0..15`: the halves of `[0,1]` holding its first two coordinates and
the quarter holding its third. The box of a key has squared diameter `1/4 + 1/4 + 1/16 = 9/16`,
so ten points pairwise further apart than `3/4` have ten different keys. Sorted, the keys form a
10-element sublist of `[0, 16)`; for each such sublist `pat` the data hold a proof, accepted by
`Packing.Cube10.checkK`, that no ten points in the boxes of `pat` are pairwise further apart than
`3/4`.
-/
import Packing.Cube
import Packing.Cube10Check

namespace Packing.Cube

open Packing.Cube10

/-- The half of `[0,1]` holding `t`. -/
noncomputable def hb (t : ℝ) : ℕ := if t < 1 / 2 then 0 else 1

/-- The quarter of `[0,1]` holding `t`. -/
noncomputable def zq (t : ℝ) : ℕ :=
  if t < 1 / 4 then 0 else if t < 1 / 2 then 1 else if t < 3 / 4 then 2 else 3

/-- The key of a point. -/
noncomputable def key (v : Pt) : ℕ := hb (v 0) + 2 * hb (v 1) + 4 * zq (v 2)

theorem hb_lt (t : ℝ) : hb t < 2 := by unfold hb; split_ifs <;> norm_num

theorem zq_lt (t : ℝ) : zq t < 4 := by unfold zq; split_ifs <;> norm_num

theorem hb_bounds {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    (512 * hb t : ℝ) ≤ 1024 * t ∧ 1024 * t ≤ 512 * hb t + 512 := by
  unfold hb
  split_ifs with h
  · constructor <;> push_cast <;> linarith
  · push Not at h
    constructor <;> push_cast <;> linarith

theorem zq_bounds {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    (256 * zq t : ℝ) ≤ 1024 * t ∧ 1024 * t ≤ 256 * zq t + 256 := by
  unfold zq
  split_ifs with ha hb hc
  · constructor <;> push_cast <;> linarith
  · push Not at ha
    constructor <;> push_cast <;> linarith
  · push Not at ha hb
    constructor <;> push_cast <;> linarith
  · push Not at ha hb hc
    constructor <;> push_cast <;> linarith

theorem key_lt (v : Pt) : key v < 16 := by
  have := hb_lt (v 0); have := hb_lt (v 1); have := zq_lt (v 2)
  unfold key; omega

theorem key_mod (v : Pt) : key v % 2 = hb (v 0) := by
  have := hb_lt (v 0); have := hb_lt (v 1); have := zq_lt (v 2)
  unfold key; omega

theorem key_div_mod (v : Pt) : key v / 2 % 2 = hb (v 1) := by
  have := hb_lt (v 0); have := hb_lt (v 1); have := zq_lt (v 2)
  unfold key; omega

theorem key_div (v : Pt) : key v / 4 = zq (v 2) := by
  have := hb_lt (v 0); have := hb_lt (v 1); have := zq_lt (v 2)
  unfold key; omega

theorem boxK_bounds {v : Pt} (hv : InCube v) (c : Fin 3) :
    ((boxK (key v) c).1 : ℝ) ≤ (S : ℝ) * v c ∧ (S : ℝ) * v c ≤ (boxK (key v) c).2 := by
  have hS : (S : ℝ) = 1024 := by norm_num [S]
  rw [hS]
  fin_cases c
  · have := hb_bounds (hv 0).1 (hv 0).2
    simp only [boxK, key_mod]
    simpa using this
  · have := hb_bounds (hv 1).1 (hv 1).2
    simp only [boxK, key_div_mod]
    simpa using this
  · have := zq_bounds (hv 2).1 (hv 2).2
    simp only [boxK, key_div]
    simpa using this

/-- Two points with the same key are at squared distance at most `9/16`. -/
theorem dist_sq_le_of_key_eq {v w : Pt} (hv : InCube v) (hw : InCube w) (h : key v = key w) :
    dist v w ^ 2 ≤ 9 / 16 := by
  rw [dist_sq]
  have e0 : hb (v 0) = hb (w 0) := by rw [← key_mod, ← key_mod, h]
  have e1 : hb (v 1) = hb (w 1) := by rw [← key_div_mod, ← key_div_mod, h]
  have e2 : zq (v 2) = zq (w 2) := by rw [← key_div, ← key_div, h]
  have a0 := hb_bounds (hv 0).1 (hv 0).2
  have b0 := hb_bounds (hw 0).1 (hw 0).2
  have a1 := hb_bounds (hv 1).1 (hv 1).2
  have b1 := hb_bounds (hw 1).1 (hw 1).2
  have a2 := zq_bounds (hv 2).1 (hv 2).2
  have b2 := zq_bounds (hw 2).1 (hw 2).2
  rw [e0] at a0; rw [e1] at a1; rw [e2] at a2
  have s0 : (v 0 - w 0) ^ 2 ≤ 1 / 4 := by nlinarith
  have s1 : (v 1 - w 1) ^ 2 ≤ 1 / 4 := by nlinarith
  have s2 : (v 2 - w 2) ^ 2 ≤ 1 / 16 := by nlinarith
  linarith

theorem getB_rootK (l : List ℕ) (i c : ℕ) (hc : c < 3) :
    getB (rootK l) (3 * i + c) = if i < l.length then boxK (l.getD i 0) c else (0, 0) := by
  induction l generalizing i with
  | nil => simp [rootK, getB]
  | cons g l ih =>
    have hr : rootK (g :: l) = (boxK g 0) :: (boxK g 1) :: (boxK g 2) :: rootK l := rfl
    rw [hr]
    cases i with
    | zero =>
      interval_cases c <;> simp [getB]
    | succ n =>
      have e : 3 * (n + 1) + c = (3 * n + c) + 3 := by ring
      rw [e]
      have := ih n
      simp only [getB] at this ⊢
      simp only [List.getD_cons_succ]
      rw [this]
      simp

theorem getB_rootK_ge (l : List ℕ) (s : ℕ) (h : 3 * l.length ≤ s) : getB (rootK l) s = (0, 0) := by
  induction l generalizing s with
  | nil => simp [rootK, getB]
  | cons g l ih =>
    have hr : rootK (g :: l) = (boxK g 0) :: (boxK g 1) :: (boxK g 2) :: rootK l := rfl
    rw [hr]
    simp only [List.length_cons] at h
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 3 := ⟨s - 3, by omega⟩
    have := ih t (by omega)
    simp only [getB] at this ⊢
    simpa using this

/-! ### Reflections

`τ < 8` encodes the reflections `x ↦ 1 - x` of the three coordinates by its three bits. -/

def bA (τ : ℕ) : Bool := τ % 2 == 1
def bB (τ : ℕ) : Bool := τ / 2 % 2 == 1
def bC (τ : ℕ) : Bool := τ / 4 % 2 == 1

def fq (b : Bool) (q : ℕ) : ℕ := if b then 1 - q else q
def fk (b : Bool) (k : ℕ) : ℕ := if b then 3 - k else k

/-- The key of the reflected box. -/
def keyT (τ g : ℕ) : ℕ := fq (bA τ) (g % 2) + 2 * fq (bB τ) (g / 2 % 2) + 4 * fk (bC τ) (g / 4)

noncomputable def fl (b : Bool) (t : ℝ) : ℝ := if b then 1 - t else t

noncomputable def reflPt (τ : ℕ) (v : Pt) : Pt :=
  WithLp.toLp 2 ![fl (bA τ) (v 0), fl (bB τ) (v 1), fl (bC τ) (v 2)]

theorem reflPt_0 (τ : ℕ) (v : Pt) : reflPt τ v 0 = fl (bA τ) (v 0) := rfl
theorem reflPt_1 (τ : ℕ) (v : Pt) : reflPt τ v 1 = fl (bB τ) (v 1) := rfl
theorem reflPt_2 (τ : ℕ) (v : Pt) : reflPt τ v 2 = fl (bC τ) (v 2) := rfl

theorem fl_sub_sq (b : Bool) (s t : ℝ) : (fl b s - fl b t) ^ 2 = (s - t) ^ 2 := by
  cases b <;> simp [fl] <;> ring

theorem dist_sq_reflPt (τ : ℕ) (v w : Pt) : dist (reflPt τ v) (reflPt τ w) ^ 2 = dist v w ^ 2 := by
  rw [dist_sq, dist_sq, reflPt_0, reflPt_0, reflPt_1, reflPt_1, reflPt_2, reflPt_2, fl_sub_sq,
    fl_sub_sq, fl_sub_sq]

theorem keyT_mod (τ g : ℕ) : keyT τ g % 2 = fq (bA τ) (g % 2) := by
  unfold keyT fq fk; split_ifs <;> omega

theorem keyT_div_mod (τ g : ℕ) : keyT τ g / 2 % 2 = fq (bB τ) (g / 2 % 2) := by
  unfold keyT fq fk; split_ifs <;> omega

theorem keyT_div (τ g : ℕ) (hg : g < 16) : keyT τ g / 4 = fk (bC τ) (g / 4) := by
  unfold keyT fq fk; split_ifs <;> omega

theorem keyT_inj (τ g g' : ℕ) (hg : g < 16) (hg' : g' < 16) (h : keyT τ g = keyT τ g') : g = g' := by
  unfold keyT fq fk at h; split_ifs at h <;> omega

theorem fl_half {b : Bool} {q : ℕ} {t : ℝ} (hq : q ≤ 1)
    (h : (512 * q : ℝ) ≤ 1024 * t ∧ 1024 * t ≤ 512 * q + 512) :
    (512 * fq b q : ℝ) ≤ 1024 * fl b t ∧ 1024 * fl b t ≤ 512 * fq b q + 512 := by
  cases b
  · simpa [fq, fl] using h
  · simp only [fq, fl, if_true]
    rw [Nat.cast_sub hq]
    push_cast
    constructor <;> linarith [h.1, h.2]

theorem fl_quarter {b : Bool} {k : ℕ} {t : ℝ} (hk : k ≤ 3)
    (h : (256 * k : ℝ) ≤ 1024 * t ∧ 1024 * t ≤ 256 * k + 256) :
    (256 * fk b k : ℝ) ≤ 1024 * fl b t ∧ 1024 * fl b t ≤ 256 * fk b k + 256 := by
  cases b
  · simpa [fk, fl] using h
  · simp only [fk, fl, if_true]
    rw [Nat.cast_sub hk]
    push_cast
    constructor <;> linarith [h.1, h.2]

theorem boxK_reflPt {v : Pt} (hv : InCube v) (τ : ℕ) (c : Fin 3) :
    ((boxK (keyT τ (key v)) c).1 : ℝ) ≤ (S : ℝ) * reflPt τ v c ∧
      (S : ℝ) * reflPt τ v c ≤ (boxK (keyT τ (key v)) c).2 := by
  have hS : (S : ℝ) = 1024 := by norm_num [S]
  rw [hS]
  have hk := key_lt v
  fin_cases c
  · have := hb_bounds (hv 0).1 (hv 0).2
    have h2 := hb_lt (v 0)
    simp only [boxK, keyT_mod, key_mod]
    have := fl_half (b := bA τ) (by omega) this
    simpa [reflPt_0] using this
  · have := hb_bounds (hv 1).1 (hv 1).2
    have h2 := hb_lt (v 1)
    simp only [boxK, keyT_div_mod, key_div_mod]
    have := fl_half (b := bB τ) (by omega) this
    simpa [reflPt_1] using this
  · have := zq_bounds (hv 2).1 (hv 2).2
    have h2 := zq_lt (v 2)
    simp only [boxK, keyT_div τ _ hk, key_div]
    have := fl_quarter (b := bC τ) (by omega) this
    simpa [reflPt_2] using this

/-- The bound for ten points, from the data: `R` holds checked proofs, and every pattern is a
reflection of one of their patterns. -/
theorem exists_dist_le_ten_of_data (R : List Ent)
    (hR : ∀ e ∈ R, okEnt e = true)
    (hS : ∀ pat ∈ List.sublistsLen 10 (List.range 16), ∃ e ∈ R, ∃ τ : ℕ,
      List.insertionSort (· ≤ ·) (pat.map (keyT τ)) = e.pat)
    (p : Fin 10 → Pt) (hp : ∀ i, InCube (p i)) :
    ∃ i j, i ≠ j ∧ dist (p i) (p j) ≤ 3 / 4 := by
  by_contra hcon
  push Not at hcon
  have hsq : ∀ i j, i ≠ j → 9 / 16 < dist (p i) (p j) ^ 2 := by
    intro i j hij
    have := hcon i j hij
    nlinarith [dist_nonneg (x := p i) (y := p j)]
  let f : Fin 10 → ℕ := fun i => key (p i)
  have hinj : Function.Injective f := by
    intro i j h
    by_contra hij
    have h1 := hsq i j hij
    have h2 := dist_sq_le_of_key_eq (hp i) (hp j) h
    linarith
  let σ := Tuple.sort f
  have hmono : Monotone (f ∘ σ) := Tuple.monotone_sort f
  have hstrict : StrictMono (f ∘ σ) := hmono.strictMono_of_injective (hinj.comp σ.injective)
  let pat := List.ofFn (f ∘ σ)
  have hpw : pat.Pairwise (· < ·) := List.pairwise_ofFn.2 (fun i j h => hstrict h)
  have hsub : List.Sublist pat (List.range 16) := by
    apply List.sublist_of_subperm_of_pairwise (r := (· ≤ ·))
    · apply List.subperm_of_subset (hpw.imp ne_of_lt)
      intro a ha
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
      exact List.mem_range.2 (key_lt _)
    · exact hpw.imp le_of_lt
    · exact List.pairwise_lt_range.imp le_of_lt
  have hmem : pat ∈ List.sublistsLen 10 (List.range 16) :=
    List.mem_sublistsLen.2 ⟨hsub, by simp [pat]⟩
  obtain ⟨e, he, τ, hτ⟩ := hS pat hmem
  -- reflected keys, sorted again
  let h : Fin 10 → ℕ := fun j => keyT τ (f (σ j))
  have hinjh : Function.Injective h := by
    intro i j hij
    exact (hinj.comp σ.injective) (keyT_inj τ _ _ (key_lt _) (key_lt _) hij)
  let π := Tuple.sort h
  have hmono' : Monotone (h ∘ π) := Tuple.monotone_sort h
  have hpat : List.ofFn (h ∘ π) = e.pat := by
    rw [← hτ]
    have e1 : pat.map (keyT τ) = List.ofFn h := by simp [pat, h]
    rw [e1]
    apply List.Perm.eq_of_sortedLE (hmono'.sortedLE_ofFn) (List.sortedLE_insertionSort)
    exact (π.ofFn_comp_perm h).trans (List.perm_insertionSort _ _).symm
  have hchk := checkK_spec _ _ (hR e he)
  rw [← hpat] at hchk
  let y : Fin 10 → Pt := fun k => reflPt τ (p (σ (π k)))
  let x : ℕ → ℝ := fun s =>
    if s / 3 < 10 then y ⟨s / 3 % 10, Nat.mod_lt _ (by norm_num)⟩ ⟨s % 3, Nat.mod_lt _ (by norm_num)⟩
    else 0
  have xv : ∀ (i : Fin 10) (c : Fin 3), x (3 * i + c) = y i c := by
    intro i c
    have h0 : (3 * (i : ℕ) + c) / 3 < 10 := by omega
    have e1 : (⟨(3 * (i : ℕ) + c) / 3 % 10, Nat.mod_lt _ (by norm_num)⟩ : Fin 10) = i :=
      Fin.ext (by simp only; omega)
    have e2 : (⟨(3 * (i : ℕ) + c) % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3) = c :=
      Fin.ext (by simp only; omega)
    simp only [x, if_pos h0, e1, e2]
  have hsep : Sep x := by
    intro i j hi hj hij
    have hne : σ (π ⟨i, hi⟩) ≠ σ (π ⟨j, hj⟩) := fun hh => hij (by
      have := π.injective (σ.injective hh)
      simpa using this)
    have := hsq _ _ hne
    rw [← dist_sq_reflPt τ, dist_sq] at this
    have e0 := xv ⟨i, hi⟩ 0
    have e1 := xv ⟨i, hi⟩ 1
    have e2 := xv ⟨i, hi⟩ 2
    have f0 := xv ⟨j, hj⟩ 0
    have f1 := xv ⟨j, hj⟩ 1
    have f2 := xv ⟨j, hj⟩ 2
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, add_zero] at e0 e1 e2 f0 f1 f2
    unfold d2
    rw [e0, e1, e2, f0, f1, f2]
    exact this
  have hlen : (List.ofFn (h ∘ π)).length = 10 := by simp
  have hin : InSt x (rootK (List.ofFn (h ∘ π))) := by
    intro s
    by_cases hi : s / 3 < 10
    · have hc : s % 3 < 3 := Nat.mod_lt _ (by norm_num)
      let I : Fin 10 := ⟨s / 3, hi⟩
      let C : Fin 3 := ⟨s % 3, hc⟩
      have hs : s = 3 * (I : ℕ) + C := by simp only [I, C]; omega
      have hg : (List.ofFn (h ∘ π)).getD (s / 3) 0 = keyT τ (key (p (σ (π I)))) := by
        rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hi)]
        simp only [List.getElem_ofFn]
        rfl
      have hb := boxK_reflPt (hp (σ (π I))) τ C
      rw [hs, getB_rootK _ I C C.isLt, if_pos (by rw [hlen]; exact I.isLt), xv I C]
      have hI : (I : ℕ) = s / 3 := rfl
      rw [hI, hg]
      exact hb
    · rw [getB_rootK_ge _ s (by rw [hlen]; omega)]
      have : x s = 0 := by simp only [x, if_neg hi]
      rw [this]
      simp
  exact check_sound hsep _ _ hchk _ List.mem_cons_self hin

end Packing.Cube
