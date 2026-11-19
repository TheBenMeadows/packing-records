/-
A checker for case analyses of ten points in the unit cube.

A state lists, for each of the 30 coordinates of ten points (slot `3 i + c` is coordinate `c` of
point `i`), a closed interval `[lo / S, hi / S]` with `S = 1024`. A proof is a list of nodes in
preorder: `sp s m` splits the interval of slot `s` at `m / S`; `pr i j` closes a state in which
points `i` and `j` are at squared distance at most `9/16` wherever they lie; `lp w ks` closes a
state with the weighted bound `∑ l (|x_i - x_j|^2 - 9/16) ≤ 0` over the triples `(i, j, l)` of
`w`, which `vmax` checks at the vertices of the boxes of the points listed in `ks` (the sum of
squares is convex in each coordinate, so its maximum on a box is attained at a vertex).
`check_sound` shows that a state accepted by `check` contains no ten points pairwise at squared
distance more than `9/16`.
-/
import Mathlib

namespace Packing.Cube10

/-- Intervals of the 30 coordinates, scaled by `S`. -/
abbrev St := List (ℕ × ℕ)

/-- The scale of the intervals. -/
def S : ℕ := 1024

def getB (B : St) (s : ℕ) : ℕ × ℕ := B.getD s (0, 0)

def setLo (B : St) (s m : ℕ) : St := B.set s (m, (getB B s).2)

def setHi (B : St) (s m : ℕ) : St := B.set s ((getB B s).1, m)

/-- An upper bound for `S |x_s - x_t|`. -/
def md (B : St) (s t : ℕ) : ℕ := max ((getB B s).2 - (getB B t).1) ((getB B t).2 - (getB B s).1)

def pairOK (B : St) (i j : ℕ) : Bool :=
  decide (i < 10) && decide (j < 10) && (i != j) &&
    decide (16 * (md B (3 * i) (3 * j) ^ 2 + md B (3 * i + 1) (3 * j + 1) ^ 2
      + md B (3 * i + 2) (3 * j + 2) ^ 2) ≤ 9 * S ^ 2)

/-- `|a - b|` in `ℕ`. -/
def ad (a b : ℕ) : ℕ := (a - b) + (b - a)

/-- `∑ l |y_i - y_j|^2` over the triples `(i, j, l)`. -/
def evalQ (w : List (ℕ × ℕ × ℕ)) (y : ℕ → ℕ) : ℕ :=
  (w.map fun e => e.2.2 * ad (y e.1) (y e.2.1) ^ 2).sum

/-- The largest value of `evalQ w` over the vertices of the boxes, in coordinate `c`, of the
points in `ks`. -/
def vmax (B : St) (c : ℕ) (w : List (ℕ × ℕ × ℕ)) : List ℕ → (ℕ → ℕ) → ℕ
  | [], y => evalQ w y
  | k :: ks, y => max (vmax B c w ks (Function.update y k (getB B (3 * k + c)).1))
      (vmax B c w ks (Function.update y k (getB B (3 * k + c)).2))

def wsum (w : List (ℕ × ℕ × ℕ)) : ℕ := (w.map fun e => e.2.2).sum

def lpOK (B : St) (w : List (ℕ × ℕ × ℕ)) (ks : List ℕ) : Bool :=
  w.all (fun e => decide (e.1 < 10) && decide (e.2.1 < 10) && (e.1 != e.2.1)
    && decide (e.1 ∈ ks) && decide (e.2.1 ∈ ks)) &&
    decide (0 < wsum w) &&
    decide (16 * (vmax B 0 w ks (fun _ => 0) + vmax B 1 w ks (fun _ => 0)
      + vmax B 2 w ks (fun _ => 0)) ≤ 9 * S ^ 2 * wsum w)

inductive Nd
  | sp (s m : ℕ)
  | pr (i j : ℕ)
  | lp (w : List (ℕ × ℕ × ℕ)) (ks : List ℕ)
  | ct (s m i j : ℕ) (up : Bool)

def check : List Nd → List St → Bool
  | [], [] => true
  | Nd.sp s m :: r, B :: stk => check r (setHi B s m :: setLo B s m :: stk)
  | Nd.ct s m i j false :: r, B :: stk => pairOK (setHi B s m) i j && check r (setLo B s m :: stk)
  | Nd.ct s m i j true :: r, B :: stk => pairOK (setLo B s m) i j && check r (setHi B s m :: stk)
  | Nd.pr i j :: r, B :: stk => pairOK B i j && check r stk
  | Nd.lp w ks :: r, B :: stk => lpOK B w ks && check r stk
  | _, _ => false

/-! ### Semantics -/

/-- `x` lies in the boxes of `B`: `lo ≤ S x_s ≤ hi` for every slot. -/
def InSt (x : ℕ → ℝ) (B : St) : Prop :=
  ∀ s, ((getB B s).1 : ℝ) ≤ S * x s ∧ S * x s ≤ (getB B s).2

/-- Squared distance of points `i` and `j`. -/
def d2 (x : ℕ → ℝ) (i j : ℕ) : ℝ :=
  (x (3 * i) - x (3 * j)) ^ 2 + (x (3 * i + 1) - x (3 * j + 1)) ^ 2
    + (x (3 * i + 2) - x (3 * j + 2)) ^ 2

/-- The ten points are pairwise at squared distance more than `9/16`. -/
def Sep (x : ℕ → ℝ) : Prop := ∀ i j, i < 10 → j < 10 → i ≠ j → 9 / 16 < d2 x i j

theorem S_pos : (0 : ℝ) < S := by norm_num [S]

theorem getB_set (B : St) (s t : ℕ) (v : ℕ × ℕ) (h : s < B.length) :
    getB (B.set s v) t = if s = t then v else getB B t := by
  unfold getB
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h1 : s = t
  · subst h1; simp [h]
  · simp [h1]

theorem getB_set_of_le (B : St) (s : ℕ) (v : ℕ × ℕ) (h : B.length ≤ s) :
    B.set s v = B := List.set_eq_of_length_le h

theorem inSt_setHi {x : ℕ → ℝ} {B : St} {s m : ℕ} (hB : InSt x B) (hm : S * x s ≤ m) :
    InSt x (setHi B s m) := by
  intro t
  unfold setHi
  by_cases hl : s < B.length
  · rw [getB_set _ _ _ _ hl]
    split_ifs with h
    · subst h; exact ⟨(hB s).1, hm⟩
    · exact hB t
  · rw [getB_set_of_le _ _ _ (not_lt.mp hl)]
    exact hB t

theorem inSt_setLo {x : ℕ → ℝ} {B : St} {s m : ℕ} (hB : InSt x B) (hm : (m : ℝ) ≤ S * x s) :
    InSt x (setLo B s m) := by
  intro t
  unfold setLo
  by_cases hl : s < B.length
  · rw [getB_set _ _ _ _ hl]
    split_ifs with h
    · subst h; exact ⟨hm, (hB s).2⟩
    · exact hB t
  · rw [getB_set_of_le _ _ _ (not_lt.mp hl)]
    exact hB t

theorem sq_le_md {x : ℕ → ℝ} {B : St} (hB : InSt x B) (s t : ℕ) :
    (S * x s - S * x t) ^ 2 ≤ (md B s t : ℝ) ^ 2 := by
  have h1 := hB s
  have h2 := hB t
  have e1 : ((getB B s).2 : ℝ) - (getB B t).1 ≤ (((getB B s).2 - (getB B t).1 : ℕ) : ℝ) := by
    rcases le_total (getB B t).1 (getB B s).2 with h | h
    · rw [Nat.cast_sub h]
    · rw [Nat.sub_eq_zero_of_le h]; push_cast; linarith [(Nat.cast_le (α := ℝ)).mpr h]
  have e2 : ((getB B t).2 : ℝ) - (getB B s).1 ≤ (((getB B t).2 - (getB B s).1 : ℕ) : ℝ) := by
    rcases le_total (getB B s).1 (getB B t).2 with h | h
    · rw [Nat.cast_sub h]
    · rw [Nat.sub_eq_zero_of_le h]; push_cast; linarith [(Nat.cast_le (α := ℝ)).mpr h]
  have m1 : (((getB B s).2 - (getB B t).1 : ℕ) : ℝ) ≤ md B s t := by
    unfold md; exact_mod_cast le_max_left _ _
  have m2 : (((getB B t).2 - (getB B s).1 : ℕ) : ℝ) ≤ md B s t := by
    unfold md; exact_mod_cast le_max_right _ _
  have hab : |S * x s - S * x t| ≤ md B s t := by
    rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  calc (S * x s - S * x t) ^ 2 = |S * x s - S * x t| ^ 2 := (sq_abs _).symm
    _ ≤ (md B s t : ℝ) ^ 2 := by
      apply pow_le_pow_left₀ (abs_nonneg _) hab

theorem pairOK_sound {x : ℕ → ℝ} {B : St} {i j : ℕ} (hB : InSt x B) (hx : Sep x)
    (h : pairOK B i j = true) : False := by
  simp only [pairOK, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨hi, hj⟩, hij⟩, hle⟩ := h
  have hs := hx i j hi hj hij
  have a0 := sq_le_md hB (3 * i) (3 * j)
  have a1 := sq_le_md hB (3 * i + 1) (3 * j + 1)
  have a2 := sq_le_md hB (3 * i + 2) (3 * j + 2)
  have hle' : (16 : ℝ) * ((md B (3 * i) (3 * j) : ℝ) ^ 2 + (md B (3 * i + 1) (3 * j + 1) : ℝ) ^ 2
      + (md B (3 * i + 2) (3 * j + 2) : ℝ) ^ 2) ≤ 9 * (S : ℝ) ^ 2 := by exact_mod_cast hle
  have hS := S_pos
  unfold d2 at hs
  have key : (S : ℝ) ^ 2 * ((x (3 * i) - x (3 * j)) ^ 2 + (x (3 * i + 1) - x (3 * j + 1)) ^ 2
      + (x (3 * i + 2) - x (3 * j + 2)) ^ 2) ≤ 9 / 16 * (S : ℝ) ^ 2 := by
    have : (S : ℝ) ^ 2 * ((x (3 * i) - x (3 * j)) ^ 2 + (x (3 * i + 1) - x (3 * j + 1)) ^ 2
      + (x (3 * i + 2) - x (3 * j + 2)) ^ 2) = (S * x (3 * i) - S * x (3 * j)) ^ 2
        + (S * x (3 * i + 1) - S * x (3 * j + 1)) ^ 2
        + (S * x (3 * i + 2) - S * x (3 * j + 2)) ^ 2 := by ring
    rw [this]; linarith
  have hS2 : 0 < (S : ℝ) ^ 2 := by positivity
  nlinarith

/-! ### The vertex bound -/

/-- `∑ l (z_i - z_j)^2` over the triples `(i, j, l)`. -/
noncomputable def evalR (w : List (ℕ × ℕ × ℕ)) (z : ℕ → ℝ) : ℝ :=
  (w.map fun e => (e.2.2 : ℝ) * (z e.1 - z e.2.1) ^ 2).sum

noncomputable def vmaxR (B : St) (c : ℕ) (w : List (ℕ × ℕ × ℕ)) : List ℕ → (ℕ → ℝ) → ℝ
  | [], z => evalR w z
  | k :: ks, z => max (vmaxR B c w ks (Function.update z k ((getB B (3 * k + c)).1 / S)))
      (vmaxR B c w ks (Function.update z k ((getB B (3 * k + c)).2 / S)))

theorem ad_cast_sq (a b : ℕ) : ((ad a b : ℕ) : ℝ) ^ 2 = ((a : ℝ) - b) ^ 2 := by
  unfold ad
  rcases le_total a b with h | h
  · rw [Nat.sub_eq_zero_of_le h, zero_add, Nat.cast_sub h]; ring
  · rw [Nat.sub_eq_zero_of_le h, add_zero, Nat.cast_sub h]

theorem evalQ_cast (w : List (ℕ × ℕ × ℕ)) (y : ℕ → ℕ) :
    ((evalQ w y : ℕ) : ℝ) = (S : ℝ) ^ 2 * evalR w (fun k => (y k : ℝ) / S) := by
  have hS := S_pos.ne'
  unfold evalQ evalR
  induction w with
  | nil => simp
  | cons e w ih =>
    simp only [List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, ih]
    rw [ad_cast_sq]
    have hS : (S : ℝ) ≠ 0 := S_pos.ne'
    field_simp

theorem update_div (y : ℕ → ℕ) (k v : ℕ) :
    (fun t => ((Function.update y k v t : ℕ) : ℝ) / S)
      = Function.update (fun t => (y t : ℝ) / S) k ((v : ℝ) / S) := by
  funext t
  by_cases h : t = k
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem vmax_cast (B : St) (c : ℕ) (w : List (ℕ × ℕ × ℕ)) (ks : List ℕ) (y : ℕ → ℕ) :
    ((vmax B c w ks y : ℕ) : ℝ) = (S : ℝ) ^ 2 * vmaxR B c w ks (fun k => (y k : ℝ) / S) := by
  induction ks generalizing y with
  | nil => exact evalQ_cast w y
  | cons k ks ih =>
    simp only [vmax, vmaxR, Nat.cast_max, ih, update_div]
    rw [mul_max_of_nonneg _ _ (by positivity)]

/-- One term of `evalR` is convex in each variable: the chord inequality. -/
theorem term_chord (l : ℝ) (hl : 0 ≤ l) (z : ℕ → ℝ) (k i j : ℕ) {a b t : ℝ} (ha : a ≤ t)
    (hb : t ≤ b) :
    (b - a) * (l * (Function.update z k t i - Function.update z k t j) ^ 2)
      ≤ (b - t) * (l * (Function.update z k a i - Function.update z k a j) ^ 2)
        + (t - a) * (l * (Function.update z k b i - Function.update z k b j) ^ 2) := by
  have h1 : 0 ≤ (t - a) * (b - t) := mul_nonneg (by linarith) (by linarith)
  by_cases hi : i = k <;> by_cases hj : j = k
  · subst hi; subst hj; simp
  · subst hi
    simp only [Function.update_self, Function.update_of_ne hj]
    have : (b - t) * (a - z j) ^ 2 + (t - a) * (b - z j) ^ 2 - (b - a) * (t - z j) ^ 2
      = (t - a) * (b - t) * (b - a) := by ring
    nlinarith [mul_nonneg h1 (show (0 : ℝ) ≤ b - a by linarith), mul_nonneg hl h1]
  · subst hj
    simp only [Function.update_self, Function.update_of_ne hi]
    have : (b - t) * (z i - a) ^ 2 + (t - a) * (z i - b) ^ 2 - (b - a) * (z i - t) ^ 2
      = (t - a) * (b - t) * (b - a) := by ring
    nlinarith [mul_nonneg h1 (show (0 : ℝ) ≤ b - a by linarith), mul_nonneg hl h1]
  · simp only [Function.update_of_ne hi, Function.update_of_ne hj]
    ring_nf
    linarith

theorem evalR_chord (w : List (ℕ × ℕ × ℕ)) (z : ℕ → ℝ) (k : ℕ) {a b t : ℝ} (ha : a ≤ t)
    (hb : t ≤ b) :
    (b - a) * evalR w (Function.update z k t)
      ≤ (b - t) * evalR w (Function.update z k a) + (t - a) * evalR w (Function.update z k b) := by
  unfold evalR
  induction w with
  | nil => simp
  | cons e w ih =>
    simp only [List.map_cons, List.sum_cons]
    have := term_chord (e.2.2 : ℝ) (Nat.cast_nonneg _) z k e.1 e.2.1 ha hb
    nlinarith

theorem evalR_le_max (w : List (ℕ × ℕ × ℕ)) (z : ℕ → ℝ) (k : ℕ) {a b : ℝ} (ha : a ≤ z k)
    (hb : z k ≤ b) :
    evalR w z ≤ max (evalR w (Function.update z k a)) (evalR w (Function.update z k b)) := by
  have hz : z = Function.update z k (z k) := (Function.update_eq_self k z).symm
  have hc := evalR_chord w z k ha hb
  rw [← hz] at hc
  rcases eq_or_lt_of_le (ha.trans hb) with h | h
  · subst h
    have : z k = a := le_antisymm hb ha
    rw [← this, ← hz]
    exact le_max_left _ _
  · have m1 := le_max_left (evalR w (Function.update z k a)) (evalR w (Function.update z k b))
    have m2 := le_max_right (evalR w (Function.update z k a)) (evalR w (Function.update z k b))
    have e1 : (b - z k) * evalR w (Function.update z k a)
        ≤ (b - z k) * max (evalR w (Function.update z k a)) (evalR w (Function.update z k b)) :=
      mul_le_mul_of_nonneg_left m1 (by linarith)
    have e2 : (z k - a) * evalR w (Function.update z k b)
        ≤ (z k - a) * max (evalR w (Function.update z k a)) (evalR w (Function.update z k b)) :=
      mul_le_mul_of_nonneg_left m2 (by linarith)
    by_contra hcon
    push Not at hcon
    nlinarith

theorem evalR_le_vmaxR (B : St) (c : ℕ) (w : List (ℕ × ℕ × ℕ)) (ks : List ℕ) (z : ℕ → ℝ)
    (hz : ∀ k, ((getB B (3 * k + c)).1 : ℝ) / S ≤ z k ∧ z k ≤ ((getB B (3 * k + c)).2 : ℝ) / S) :
    evalR w z ≤ vmaxR B c w ks z := by
  induction ks generalizing z with
  | nil => exact le_refl _
  | cons k ks ih =>
    simp only [vmaxR]
    have hle : ((getB B (3 * k + c)).1 : ℝ) / S ≤ ((getB B (3 * k + c)).2 : ℝ) / S :=
      (hz k).1.trans (hz k).2
    have hbound : ∀ v : ℝ, ((getB B (3 * k + c)).1 : ℝ) / S ≤ v →
        v ≤ ((getB B (3 * k + c)).2 : ℝ) / S → ∀ k', ((getB B (3 * k' + c)).1 : ℝ) / S
          ≤ Function.update z k v k' ∧ Function.update z k v k' ≤ ((getB B (3 * k' + c)).2 : ℝ) / S := by
      intro v hv1 hv2 k'
      by_cases h : k' = k
      · subst h; simp [hv1, hv2]
      · simp only [Function.update_of_ne h]; exact hz k'
    calc evalR w z ≤ max (evalR w (Function.update z k (((getB B (3 * k + c)).1 : ℝ) / S)))
          (evalR w (Function.update z k (((getB B (3 * k + c)).2 : ℝ) / S))) :=
            evalR_le_max w z k (hz k).1 (hz k).2
      _ ≤ _ := max_le_max (ih _ (hbound _ le_rfl hle)) (ih _ (hbound _ hle le_rfl))

theorem evalR_congr (w : List (ℕ × ℕ × ℕ)) (z z' : ℕ → ℝ)
    (h : ∀ e ∈ w, z e.1 = z' e.1 ∧ z e.2.1 = z' e.2.1) : evalR w z = evalR w z' := by
  unfold evalR
  induction w with
  | nil => rfl
  | cons e w ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [(h e List.mem_cons_self).1, (h e List.mem_cons_self).2,
      ih (fun e' he' => h e' (List.mem_cons_of_mem _ he'))]

theorem vmaxR_congr (B : St) (c : ℕ) (w : List (ℕ × ℕ × ℕ)) (ks : List ℕ) (z z' : ℕ → ℝ)
    (h : ∀ e ∈ w, (e.1 ∈ ks ∨ z e.1 = z' e.1) ∧ (e.2.1 ∈ ks ∨ z e.2.1 = z' e.2.1)) :
    vmaxR B c w ks z = vmaxR B c w ks z' := by
  induction ks generalizing z z' with
  | nil =>
    simp only [List.not_mem_nil, false_or] at h
    exact evalR_congr w z z' h
  | cons k ks ih =>
    simp only [vmaxR]
    have key : ∀ v : ℝ, ∀ e ∈ w, (e.1 ∈ ks ∨ Function.update z k v e.1 = Function.update z' k v e.1)
        ∧ (e.2.1 ∈ ks ∨ Function.update z k v e.2.1 = Function.update z' k v e.2.1) := by
      intro v e he
      have h1 := h e he
      constructor
      · rcases h1.1 with h2 | h2
        · rcases List.mem_cons.mp h2 with h3 | h3
          · right; rw [h3]; simp
          · left; exact h3
        · right
          by_cases h4 : e.1 = k
          · rw [h4]; simp
          · simp [Function.update_of_ne h4, h2]
      · rcases h1.2 with h2 | h2
        · rcases List.mem_cons.mp h2 with h3 | h3
          · right; rw [h3]; simp
          · left; exact h3
        · right
          by_cases h4 : e.2.1 = k
          · rw [h4]; simp
          · simp [Function.update_of_ne h4, h2]
    rw [ih _ _ (key _), ih _ _ (key _)]

theorem inSt_coord {x : ℕ → ℝ} {B : St} (hB : InSt x B) (c : ℕ) (k : ℕ) :
    ((getB B (3 * k + c)).1 : ℝ) / S ≤ x (3 * k + c) ∧ x (3 * k + c) ≤ ((getB B (3 * k + c)).2 : ℝ) / S := by
  have h := hB (3 * k + c)
  have hS := S_pos
  constructor
  · rw [div_le_iff₀ hS]; linarith [h.1]
  · rw [le_div_iff₀ hS]; linarith [h.2]

theorem sum_d2 (x : ℕ → ℝ) (w : List (ℕ × ℕ × ℕ)) :
    (w.map fun e => (e.2.2 : ℝ) * d2 x e.1 e.2.1).sum
      = evalR w (fun k => x (3 * k)) + evalR w (fun k => x (3 * k + 1))
        + evalR w (fun k => x (3 * k + 2)) := by
  unfold evalR d2
  induction w with
  | nil => simp
  | cons e w ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

theorem lpOK_sound {x : ℕ → ℝ} {B : St} {w : List (ℕ × ℕ × ℕ)} {ks : List ℕ} (hB : InSt x B)
    (hx : Sep x) (h : lpOK B w ks = true) : False := by
  simp only [lpOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, bne_iff_ne,
    ne_eq] at h
  obtain ⟨⟨hw0, hpos⟩, hle⟩ := h
  have hw : ∀ e ∈ w, (e.1 < 10 ∧ e.2.1 < 10) ∧ ¬ e.1 = e.2.1 := fun e he => (hw0 e he).1.1
  have hks : ∀ e ∈ w, e.1 ∈ ks ∧ e.2.1 ∈ ks := fun e he => ⟨(hw0 e he).1.2, (hw0 e he).2⟩
  have hS := S_pos
  have hS2 : (0 : ℝ) < (S : ℝ) ^ 2 := by positivity
  -- the weighted sum of squared distances exceeds `9/16` times the total weight
  have hlow : ∀ w' : List (ℕ × ℕ × ℕ), (∀ e ∈ w', (e.1 < 10 ∧ e.2.1 < 10) ∧ ¬ e.1 = e.2.1) →
      9 / 16 * ((wsum w' : ℕ) : ℝ) ≤ (w'.map fun e => (e.2.2 : ℝ) * d2 x e.1 e.2.1).sum ∧
      (0 < wsum w' → 9 / 16 * ((wsum w' : ℕ) : ℝ)
        < (w'.map fun e => (e.2.2 : ℝ) * d2 x e.1 e.2.1).sum) := by
    intro w' hw'
    induction w' with
    | nil => simp [wsum]
    | cons e w' ih =>
      have he := hw' e (List.mem_cons_self)
      have ih' := ih (fun e' he' => hw' e' (List.mem_cons_of_mem _ he'))
      have hd := hx e.1 e.2.1 he.1.1 he.1.2 he.2
      simp only [wsum, List.map_cons, List.sum_cons, Nat.cast_add] at ih' ⊢
      have hl : (0 : ℝ) ≤ e.2.2 := Nat.cast_nonneg _
      constructor
      · nlinarith [ih'.1]
      · intro hp
        have h3 := mul_le_mul_of_nonneg_left hd.le hl
        rcases Nat.eq_zero_or_pos e.2.2 with h0 | h0
        · have hp' : 0 < (List.map (fun e => e.2.2) w').sum := by simpa [h0] using hp
          have := ih'.2 hp'
          linarith
        · have hl' : (0 : ℝ) < e.2.2 := by exact_mod_cast h0
          have h4 := mul_lt_mul_of_pos_left hd hl'
          linarith [ih'.1]
  have hl := (hlow w hw).2 hpos
  rw [sum_d2] at hl
  have v0 := evalR_le_vmaxR B 0 w ks (fun k => x (3 * k)) (fun k => by
    simpa using inSt_coord hB 0 k)
  have v1 := evalR_le_vmaxR B 1 w ks (fun k => x (3 * k + 1)) (fun k => inSt_coord hB 1 k)
  have v2 := evalR_le_vmaxR B 2 w ks (fun k => x (3 * k + 2)) (fun k => inSt_coord hB 2 k)
  have c0 := vmax_cast B 0 w ks (fun _ => 0)
  have c1 := vmax_cast B 1 w ks (fun _ => 0)
  have c2 := vmax_cast B 2 w ks (fun _ => 0)
  have hle' : (16 : ℝ) * ((vmax B 0 w ks (fun _ => 0) : ℝ) + vmax B 1 w ks (fun _ => 0)
      + vmax B 2 w ks (fun _ => 0)) ≤ 9 * (S : ℝ) ^ 2 * (wsum w : ℝ) := by exact_mod_cast hle
  have e0 := vmaxR_congr B 0 w ks (fun k => x (3 * k)) (fun k => ((0 : ℕ) : ℝ) / S)
    (fun e he => ⟨Or.inl (hks e he).1, Or.inl (hks e he).2⟩)
  have e1 := vmaxR_congr B 1 w ks (fun k => x (3 * k + 1)) (fun k => ((0 : ℕ) : ℝ) / S)
    (fun e he => ⟨Or.inl (hks e he).1, Or.inl (hks e he).2⟩)
  have e2 := vmaxR_congr B 2 w ks (fun k => x (3 * k + 2)) (fun k => ((0 : ℕ) : ℝ) / S)
    (fun e he => ⟨Or.inl (hks e he).1, Or.inl (hks e he).2⟩)
  rw [e0] at v0
  rw [e1] at v1
  rw [e2] at v2
  have hwpos : (0 : ℝ) < wsum w := by exact_mod_cast hpos
  nlinarith

/-- Soundness of `check`. -/
theorem check_sound {x : ℕ → ℝ} (hx : Sep x) :
    ∀ (nodes : List Nd) (stk : List St), check nodes stk = true → ∀ B ∈ stk, ¬ InSt x B := by
  intro nodes
  induction nodes with
  | nil =>
    intro stk h B hB
    cases stk with
    | nil => simp at hB
    | cons _ _ => simp [check] at h
  | cons nd r ih =>
    intro stk h B hB hin
    cases stk with
    | nil => cases nd <;> simp [check] at h
    | cons B0 stk =>
      cases nd with
      | sp s m =>
        simp only [check] at h
        rcases List.mem_cons.mp hB with rfl | hB'
        · rcases le_total (S * x s) m with hm | hm
          · exact ih _ h _ List.mem_cons_self (inSt_setHi hin hm)
          · exact ih _ h _ (List.mem_cons_of_mem _ List.mem_cons_self) (inSt_setLo hin hm)
        · exact ih _ h B (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hB')) hin
      | pr i j =>
        simp only [check, Bool.and_eq_true] at h
        rcases List.mem_cons.mp hB with rfl | hB'
        · exact pairOK_sound hin hx h.1
        · exact ih _ h.2 B hB' hin
      | lp w ks =>
        simp only [check, Bool.and_eq_true] at h
        rcases List.mem_cons.mp hB with rfl | hB'
        · exact lpOK_sound hin hx h.1
        · exact ih _ h.2 B hB' hin
      | ct s m i j up =>
        cases up with
        | false =>
          simp only [check, Bool.and_eq_true] at h
          rcases List.mem_cons.mp hB with rfl | hB'
          · rcases le_total (S * x s) m with hm | hm
            · exact pairOK_sound (inSt_setHi hin hm) hx h.1
            · exact ih _ h.2 _ List.mem_cons_self (inSt_setLo hin hm)
          · exact ih _ h.2 B (List.mem_cons_of_mem _ hB') hin
        | true =>
          simp only [check, Bool.and_eq_true] at h
          rcases List.mem_cons.mp hB with rfl | hB'
          · rcases le_total (S * x s) m with hm | hm
            · exact ih _ h.2 _ List.mem_cons_self (inSt_setHi hin hm)
            · exact pairOK_sound (inSt_setLo hin hm) hx h.1
          · exact ih _ h.2 B (List.mem_cons_of_mem _ hB') hin


/-! ### The same checker in a form the kernel evaluates quickly

Natural-number primitives only, and recursion through `List.rec`, `Nat.rec`, `Bool.rec` and
`Nd.rec` directly (see `Packing.Cert.Check`). `checkK_spec` reduces it to `check`. -/

noncomputable def andB (a b : Bool) : Bool := Bool.rec false b a

noncomputable def notB (a : Bool) : Bool := Bool.rec true false a

noncomputable def maxN (a b : ℕ) : ℕ := Bool.rec a b (Nat.ble a b)

noncomputable def sumMapK {α : Type} (f : α → ℕ) (l : List α) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun a _ ih => Nat.add (f a) ih) l

noncomputable def allK {α : Type} (f : α → Bool) (l : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => andB (f a) ih) l

noncomputable def memK (k : ℕ) (l : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ ih => Bool.rec ih true (Nat.beq k a)) l

noncomputable def getK (B : St) : ℕ → ℕ × ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ × ℕ) (fun _ => (0, 0))
    (fun a _ ih s => Nat.rec (motive := fun _ => ℕ × ℕ) a (fun n _ => ih n) s) B

noncomputable def setK (v : ℕ × ℕ) (B : St) : ℕ → St :=
  List.rec (motive := fun _ => ℕ → St) (fun _ => [])
    (fun a t ih s => Nat.rec (motive := fun _ => St) (v :: t) (fun n _ => a :: ih n) s) B

noncomputable def setHiK (B : St) (s m : ℕ) : St := setK ((getK B s).1, m) B s

noncomputable def setLoK (B : St) (s m : ℕ) : St := setK (m, (getK B s).2) B s

noncomputable def mdK (B : St) (s t : ℕ) : ℕ :=
  maxN (Nat.sub (getK B s).2 (getK B t).1) (Nat.sub (getK B t).2 (getK B s).1)

noncomputable def sqK (a : ℕ) : ℕ := Nat.mul a a

noncomputable def pairOKK (B : St) (i j : ℕ) : Bool :=
  andB (Nat.ble (Nat.succ i) 10) (andB (Nat.ble (Nat.succ j) 10) (andB (notB (Nat.beq i j))
    (Nat.ble (Nat.mul 16 (Nat.add (Nat.add (sqK (mdK B (Nat.mul 3 i) (Nat.mul 3 j)))
      (sqK (mdK B (Nat.add (Nat.mul 3 i) 1) (Nat.add (Nat.mul 3 j) 1))))
      (sqK (mdK B (Nat.add (Nat.mul 3 i) 2) (Nat.add (Nat.mul 3 j) 2))))) 9437184)))

noncomputable def adK (a b : ℕ) : ℕ := Nat.add (Nat.sub a b) (Nat.sub b a)

noncomputable def evalQK (w : List (ℕ × ℕ × ℕ)) (y : ℕ → ℕ) : ℕ :=
  sumMapK (fun e => Nat.mul e.2.2 (sqK (adK (y e.1) (y e.2.1)))) w

noncomputable def updK (y : ℕ → ℕ) (k v : ℕ) : ℕ → ℕ := fun t => Bool.rec (y t) v (Nat.beq t k)

noncomputable def vmaxK (B : St) (c : ℕ) (w : List (ℕ × ℕ × ℕ)) (ks : List ℕ) : (ℕ → ℕ) → ℕ :=
  List.rec (motive := fun _ => (ℕ → ℕ) → ℕ) (fun y => evalQK w y)
    (fun k _ ih y => maxN (ih (updK y k (getK B (Nat.add (Nat.mul 3 k) c)).1))
      (ih (updK y k (getK B (Nat.add (Nat.mul 3 k) c)).2))) ks

noncomputable def lpOKK (B : St) (w : List (ℕ × ℕ × ℕ)) (ks : List ℕ) : Bool :=
  andB (allK (fun e => andB (Nat.ble (Nat.succ e.1) 10) (andB (Nat.ble (Nat.succ e.2.1) 10)
      (andB (notB (Nat.beq e.1 e.2.1)) (andB (memK e.1 ks) (memK e.2.1 ks))))) w)
    (andB (Nat.ble 1 (sumMapK (fun e => e.2.2) w))
      (Nat.ble (Nat.mul 16 (Nat.add (Nat.add (vmaxK B 0 w ks (fun _ => 0))
        (vmaxK B 1 w ks (fun _ => 0))) (vmaxK B 2 w ks (fun _ => 0))))
        (Nat.mul 9437184 (sumMapK (fun e => e.2.2) w))))

/-- Empty stack test. -/
noncomputable def nilK (stk : List St) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) stk

/-- `k a`, after reducing `a` to a numeral: the kernel substitutes arguments unevaluated, and
states built by repeated updates would otherwise be recomputed at every use. -/
noncomputable def forceN {α : Sort _} (a : ℕ) (k : ℕ → α) : α :=
  Nat.rec (motive := fun _ => α) (k 0) (fun n _ => k (Nat.succ n)) a

noncomputable def forceSt {α : Sort _} (B : St) : (St → α) → α :=
  List.rec (motive := fun _ => (St → α) → α) (fun k => k [])
    (fun p _ ih k => forceN p.1 (fun a => forceN p.2 (fun b => ih (fun t => k ((a, b) :: t))))) B

noncomputable def checkK (nodes : List Nd) : List St → Bool :=
  List.rec (motive := fun _ => List St → Bool) nilK
    (fun nd _ ih stk => List.rec (motive := fun _ => Bool) false
      (fun B stk' _ => Nd.rec (motive := fun _ => Bool)
        (fun s m => ih (setHiK B s m :: setLoK B s m :: stk'))
        (fun i j => andB (pairOKK B i j) (ih stk'))
        (fun w ks => andB (lpOKK B w ks) (ih stk'))
        (fun s m i j up => Bool.rec
          (andB (pairOKK (setHiK B s m) i j) (ih (setLoK B s m :: stk')))
          (andB (pairOKK (setLoK B s m) i j) (ih (setHiK B s m :: stk')))
          up) nd) stk) nodes

/-! ### Bridge -/

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem notB_eq (a : Bool) : notB a = !a := by cases a <;> rfl

theorem ble_true {a b : ℕ} (h : Nat.ble a b = true) : a ≤ b := Nat.le_of_ble_eq_true h

theorem ble_false {a b : ℕ} (h : Nat.ble a b = false) : b < a :=
  Nat.gt_of_not_le (Nat.not_le_of_not_ble_eq_true (by rw [h]; decide))

theorem maxN_eq (a b : ℕ) : maxN a b = max a b := by
  unfold maxN
  cases h : Nat.ble a b
  · have := ble_false h
    show a = max a b
    omega
  · have := ble_true h
    show b = max a b
    omega

theorem getK_eq (B : St) (s : ℕ) : getK B s = getB B s := by
  induction B generalizing s with
  | nil => rfl
  | cons a t ih =>
    cases s with
    | zero => rfl
    | succ n => exact (ih n).trans (by simp [getB])

theorem setK_eq (v : ℕ × ℕ) (B : St) (s : ℕ) : setK v B s = B.set s v := by
  induction B generalizing s with
  | nil => rfl
  | cons a t ih =>
    cases s with
    | zero => rfl
    | succ n => exact congrArg (a :: ·) (ih n)

theorem setHiK_eq (B : St) (s m : ℕ) : setHiK B s m = setHi B s m := by
  simp [setHiK, setHi, setK_eq, getK_eq]

theorem setLoK_eq (B : St) (s m : ℕ) : setLoK B s m = setLo B s m := by
  simp [setLoK, setLo, setK_eq, getK_eq]

theorem sumMapK_eq {α : Type} (f : α → ℕ) (l : List α) : sumMapK f l = (l.map f).sum := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    show Nat.add (f a) (sumMapK f t) = _
    rw [ih, List.map_cons, List.sum_cons]
    rfl

theorem allK_eq {α : Type} (f : α → Bool) (l : List α) : allK f l = l.all f := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    show andB (f a) (allK f t) = _
    rw [ih, List.all_cons, andB_eq]

theorem memK_eq (k : ℕ) (l : List ℕ) : memK k l = decide (k ∈ l) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    have e : memK k (a :: t) = Bool.rec (memK k t) true (Nat.beq k a) := rfl
    rw [e, ih]
    rcases Bool.eq_false_or_eq_true (Nat.beq k a) with hb | hb
    · rw [hb]
      have : k = a := Nat.eq_of_beq_eq_true hb
      show true = _
      simp [this]
    · rw [hb]
      have : k ≠ a := Nat.ne_of_beq_eq_false hb
      show decide (k ∈ t) = _
      simp [this]

theorem mdK_eq (B : St) (s t : ℕ) : mdK B s t = md B s t := by
  simp only [mdK, md, maxN_eq, getK_eq]
  rfl

theorem pairOKK_spec (B : St) (i j : ℕ) (h : pairOKK B i j = true) : pairOK B i j = true := by
  simp only [pairOKK, andB_eq, notB_eq, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have h1' := ble_true h1
  have h2' := ble_true h2
  have h3' := Nat.ne_of_beq_eq_false h3
  have h4' := ble_true h4
  simp only [sqK, mdK_eq] at h4'
  have h5 : 16 * (md B (3 * i) (3 * j) * md B (3 * i) (3 * j)
      + md B (3 * i + 1) (3 * j + 1) * md B (3 * i + 1) (3 * j + 1)
      + md B (3 * i + 2) (3 * j + 2) * md B (3 * i + 2) (3 * j + 2)) ≤ 9437184 := h4'
  simp only [pairOK, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
  refine ⟨⟨⟨by omega, by omega⟩, h3'⟩, ?_⟩
  have e : 9 * S ^ 2 = 9437184 := by norm_num [S]
  rw [e]
  simpa only [sq] using h5

theorem adK_eq (a b : ℕ) : adK a b = ad a b := rfl

theorem updK_eq (y : ℕ → ℕ) (k v : ℕ) : updK y k v = Function.update y k v := by
  funext t
  unfold updK
  cases h : Nat.beq t k
  · have : t ≠ k := Nat.ne_of_beq_eq_false h
    show y t = _
    simp [Function.update_of_ne this]
  · have : t = k := Nat.eq_of_beq_eq_true h
    subst this
    show v = _
    simp

theorem evalQK_eq (w : List (ℕ × ℕ × ℕ)) (y : ℕ → ℕ) : evalQK w y = evalQ w y := by
  simp only [evalQK, evalQ, sumMapK_eq, sqK, adK_eq]
  congr 1
  apply List.map_congr_left
  intro e _
  show e.2.2 * (ad (y e.1) (y e.2.1) * ad (y e.1) (y e.2.1)) = _
  ring

theorem vmaxK_eq (B : St) (c : ℕ) (w : List (ℕ × ℕ × ℕ)) (ks : List ℕ) (y : ℕ → ℕ) :
    vmaxK B c w ks y = vmax B c w ks y := by
  induction ks generalizing y with
  | nil => exact evalQK_eq w y
  | cons k ks ih =>
    show maxN (vmaxK B c w ks (updK y k (getK B (Nat.add (Nat.mul 3 k) c)).1))
      (vmaxK B c w ks (updK y k (getK B (Nat.add (Nat.mul 3 k) c)).2)) = _
    rw [ih, ih, maxN_eq, updK_eq, updK_eq, getK_eq]
    rfl

theorem lpOKK_spec (B : St) (w : List (ℕ × ℕ × ℕ)) (ks : List ℕ) (h : lpOKK B w ks = true) :
    lpOK B w ks = true := by
  simp only [lpOKK, andB_eq, notB_eq, Bool.and_eq_true, allK_eq, memK_eq, sumMapK_eq,
    vmaxK_eq, List.all_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨h1, h2, h3⟩ := h
  have h2' := ble_true h2
  have h3' := ble_true h3
  have h3'' : 16 * (vmax B 0 w ks (fun _ => 0) + vmax B 1 w ks (fun _ => 0)
      + vmax B 2 w ks (fun _ => 0)) ≤ 9437184 * (w.map fun e => e.2.2).sum := h3'
  have eS : 9 * S ^ 2 = 9437184 := by norm_num [S]
  simp only [lpOK, Bool.and_eq_true, List.all_eq_true, wsum]
  refine ⟨⟨fun e he => ?_, decide_eq_true h2'⟩, ?_⟩
  · obtain ⟨a, b, c, d, f⟩ := h1 e he
    have a' := ble_true a
    have b' := ble_true b
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
    exact ⟨⟨⟨⟨by omega, by omega⟩, Nat.ne_of_beq_eq_false c⟩, d⟩, f⟩
  · apply decide_eq_true
    rw [eS]
    exact h3''

theorem forceN_eq {α : Sort _} (a : ℕ) (k : ℕ → α) : forceN a k = k a := by
  cases a <;> rfl

theorem forceSt_eq {α : Sort _} (B : St) (k : St → α) : forceSt B k = k B := by
  induction B generalizing k with
  | nil => rfl
  | cons p t ih =>
    show forceN p.1 (fun a => forceN p.2 (fun b => forceSt t (fun t' => k ((a, b) :: t')))) = _
    rw [forceN_eq, forceN_eq, ih]

theorem checkK_spec : ∀ (nodes : List Nd) (stk : List St), checkK nodes stk = true →
    check nodes stk = true := by
  intro nodes
  induction nodes with
  | nil =>
    intro stk h
    cases stk with
    | nil => rfl
    | cons _ _ => exact (Bool.false_ne_true h).elim
  | cons nd r ih =>
    intro stk h
    cases stk with
    | nil => cases nd <;> exact (Bool.false_ne_true h).elim
    | cons B stk =>
      cases nd with
      | sp s m =>
        have h' : checkK r (setHiK B s m :: setLoK B s m :: stk) = true := h
        rw [setHiK_eq, setLoK_eq] at h'
        exact ih _ h'
      | pr i j =>
        have h' : andB (pairOKK B i j) (checkK r stk) = true := h
        rw [andB_eq, Bool.and_eq_true] at h'
        simp only [check, Bool.and_eq_true]
        exact ⟨pairOKK_spec _ _ _ h'.1, ih _ h'.2⟩
      | lp w ks =>
        have h' : andB (lpOKK B w ks) (checkK r stk) = true := h
        rw [andB_eq, Bool.and_eq_true] at h'
        simp only [check, Bool.and_eq_true]
        exact ⟨lpOKK_spec _ _ _ h'.1, ih _ h'.2⟩
      | ct s m i j up =>
        cases up with
        | false =>
          have h' : andB (pairOKK (setHiK B s m) i j) (checkK r (setLoK B s m :: stk)) = true := h
          rw [andB_eq, Bool.and_eq_true, setHiK_eq, setLoK_eq] at h'
          simp only [check, Bool.and_eq_true]
          exact ⟨pairOKK_spec _ _ _ h'.1, ih _ h'.2⟩
        | true =>
          have h' : andB (pairOKK (setLoK B s m) i j) (checkK r (setHiK B s m :: stk)) = true := h
          rw [andB_eq, Bool.and_eq_true, setHiK_eq, setLoK_eq] at h'
          simp only [check, Bool.and_eq_true]
          exact ⟨pairOKK_spec _ _ _ h'.1, ih _ h'.2⟩

/-! ### Compact data

A proof is stored as one natural number: node `k` occupies bits `27 k` to `27 k + 26`, with a
tag in the lowest three bits (`0` split, `1` pair, `2` and `3` cuts, `4` a vertex-bound leaf
taken from a separate list by index). `streamK` unpacks it; `check_sound` holds for any list of
nodes, so nothing about the unpacking needs proof. -/

noncomputable def ndAt (lps : List Nd) : ℕ → Nd :=
  List.rec (motive := fun _ => ℕ → Nd) (fun _ => Nd.pr 0 0)
    (fun a _ ih k => Nat.rec (motive := fun _ => Nd) a (fun n _ => ih n) k) lps

noncomputable def decK (lps : List Nd) (n : ℕ) : Nd :=
  Bool.rec
    (Bool.rec
      (Bool.rec
        (Bool.rec
          (Bool.rec (Nd.pr 0 0) (ndAt lps (Nat.mod (Nat.div n 256) 2048))
            (Nat.beq (Nat.mod n 8) 4))
          (Nd.ct (Nat.mod (Nat.div n 8) 32) (Nat.mod (Nat.div n 256) 2048)
            (Nat.mod (Nat.div n 524288) 16) (Nat.mod (Nat.div n 8388608) 16) true)
          (Nat.beq (Nat.mod n 8) 3))
        (Nd.ct (Nat.mod (Nat.div n 8) 32) (Nat.mod (Nat.div n 256) 2048)
          (Nat.mod (Nat.div n 524288) 16) (Nat.mod (Nat.div n 8388608) 16) false)
        (Nat.beq (Nat.mod n 8) 2))
      (Nd.pr (Nat.mod (Nat.div n 524288) 16) (Nat.mod (Nat.div n 8388608) 16))
      (Nat.beq (Nat.mod n 8) 1))
    (Nd.sp (Nat.mod (Nat.div n 8) 32) (Nat.mod (Nat.div n 256) 2048))
    (Nat.beq (Nat.mod n 8) 0)

noncomputable def streamK (lps : List Nd) (fuel : ℕ) : ℕ → List Nd :=
  Nat.rec (motive := fun _ => ℕ → List Nd) (fun _ => [])
    (fun _ ih n => forceN (Nat.div n 134217728) (fun n' => decK lps n :: ih n')) fuel

/-- The box of key `g` in coordinate `c` (`c = 0, 1`: halves; `c = 2`: quarters), scaled by
`S`. -/
def boxK (g c : ℕ) : ℕ × ℕ :=
  if c = 0 then (512 * (g % 2), 512 * (g % 2) + 512)
  else if c = 1 then (512 * (g / 2 % 2), 512 * (g / 2 % 2) + 512)
  else (256 * (g / 4), 256 * (g / 4) + 256)

noncomputable def rootK (pat : List ℕ) : St :=
  List.rec (motive := fun _ => St) []
    (fun g _ ih =>
      (Nat.mul 512 (Nat.mod g 2), Nat.add (Nat.mul 512 (Nat.mod g 2)) 512) ::
      (Nat.mul 512 (Nat.mod (Nat.div g 2) 2), Nat.add (Nat.mul 512 (Nat.mod (Nat.div g 2) 2)) 512) ::
      (Nat.mul 256 (Nat.div g 4), Nat.add (Nat.mul 256 (Nat.div g 4)) 256) :: ih) pat

structure Ent where
  pat : List ℕ
  code : ℕ
  fuel : ℕ
  lps : List Nd

noncomputable def okEnt (e : Ent) : Bool := checkK (streamK e.lps e.fuel e.code) [rootK e.pat]

end Packing.Cube10
