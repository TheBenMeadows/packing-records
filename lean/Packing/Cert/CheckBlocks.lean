/-
Checking a long list of points in blocks.

`pairwiseB r (xs ++ ys)` holds when `r` holds within `xs`, within `ys`, and between every member
of `xs` and every member of `ys` (`crossB`). The generator of the point tables cuts the data of
a large cell into consecutive blocks and states one kernel-evaluated theorem for each block and
for each pair of blocks, so that no single evaluation has to hold all pairs of the cell. The
lemmas below join those theorems into the statement `checkSph ... = true` that every other cell
proves in one evaluation.

Like `Check.lean`, this file does not import Mathlib.
-/
import Packing.Cert.CheckPoints

namespace Packing.Cert

/-- `r a b` holds for every `a` in `xs` and every `b` in `ys`. -/
noncomputable def crossB {α : Type} (r : α → α → Bool) (xs ys : List α) : Bool :=
  allB (fun a => allB (r a) ys) xs

theorem andB_intro {a b : Bool} (ha : a = true) (hb : b = true) : andB a b = true := by
  subst ha
  exact hb

theorem andB_left {a b : Bool} (h : andB a b = true) : a = true := by
  cases a
  · exact h
  · rfl

theorem andB_right {a b : Bool} (h : andB a b = true) : b = true := by
  cases a
  · exact Bool.noConfusion h
  · exact h

theorem allB_append {α : Type} (f : α → Bool) (xs ys : List α) (h1 : allB f xs = true)
    (h2 : allB f ys = true) : allB f (xs ++ ys) = true := by
  induction xs with
  | nil => exact h2
  | cons a l ih => exact andB_intro (andB_left h1) (ih (andB_right h1))

theorem crossB_append {α : Type} {r : α → α → Bool} {xs ys zs : List α}
    (h1 : crossB r xs ys = true) (h2 : crossB r xs zs = true) :
    crossB r xs (ys ++ zs) = true := by
  induction xs with
  | nil => rfl
  | cons a l ih =>
    exact andB_intro (allB_append _ _ _ (andB_left h1) (andB_left h2))
      (ih (andB_right h1) (andB_right h2))

theorem pairwiseB_append {α : Type} {r : α → α → Bool} {xs ys : List α}
    (h1 : pairwiseB r xs = true) (h2 : crossB r xs ys = true) (h3 : pairwiseB r ys = true) :
    pairwiseB r (xs ++ ys) = true := by
  induction xs with
  | nil => exact h3
  | cons a l ih =>
    exact andB_intro (allB_append _ _ _ (andB_left h1) (andB_left h2))
      (ih (andB_right h1) (andB_right h2))

/-- `checkSph` from its two parts: the count and the vectors, and the pairs. -/
theorem checkSph_of_blocks {m N t : Nat} {c : List Vec}
    (h1 : andB (Nat.beq (sumMap (fun _ => 1) c) N) (allB (okVec m) c) = true)
    (h2 : pairwiseB (cosB m (Nat.mul t t) (Nat.pow 10 24)) c = true) :
    checkSph m N t c = true :=
  andB_intro (andB_left h1) (andB_intro (andB_right h1) h2)

end Packing.Cert
