/-
A Boolean checker that ties the frames used by `Packing.Cert.check` to the vectors of the data
file: every frame vector, multiplied by a positive integer, is an integer combination of the
file's vectors of the same subspace. Together with the orthogonality that `check` verifies, this
makes the span of each frame equal to the span of the file's vectors
(`Packing.Cert.spansPack_of_link`).

Written for evaluation by the Lean kernel, natural numbers only. The cost is small next to
`check`, so the entries are read with `List.getD`.
-/
import Packing.Cert.CheckPoints

namespace Packing.Cert

/-- How one frame vector `w` is made from the file's vectors `b₁, …, bₙ` of its subspace:
`g · w = ∑ (pₖ - qₖ) · bₖ`. -/
structure Coef where
  g : Nat
  pq : List (Nat × Nat)

/-- `∑ₖ sel(pqₖ) · (entry c of the stored list of bₖ)`. -/
noncomputable def colSum (c : Nat) (sel : Nat × Nat → Nat) (pq : List (Nat × Nat)) :
    List Vec → Nat :=
  List.rec (motive := fun _ => List Vec → Nat) (fun _ => 0)
    (fun x _ ih rows =>
      List.rec (motive := fun _ => Nat) 0
        (fun b bs _ => Nat.add (Nat.mul (sel x) (List.getD b.e c 0)) (ih bs)) rows) pq

/-- `∑ₖ sel(pqₖ) · (offset of bₖ)`. -/
noncomputable def offSum (sel : Nat × Nat → Nat) (pq : List (Nat × Nat)) : List Vec → Nat :=
  List.rec (motive := fun _ => List Vec → Nat) (fun _ => 0)
    (fun x _ ih rows =>
      List.rec (motive := fun _ => Nat) 0
        (fun b bs _ => Nat.add (Nat.mul (sel x) b.off) (ih bs)) rows) pq

/-- `g · w = ∑ (pₖ - qₖ) · bₖ` in every one of the `m` coordinates, with `g ≥ 1`. Written
without subtraction: the entries stand for `e - off`, so the equation is
`g e_w + ∑ q e_b + ∑ p off_b = g off_w + ∑ p e_b + ∑ q off_b`. -/
noncomputable def linkVec (m : Nat) (rows : List Vec) (w : Vec) (k : Coef) : Bool :=
  andB (Nat.ble 1 k.g)
    (allB (fun c =>
        Nat.beq
          (Nat.add (Nat.add (Nat.mul k.g (List.getD w.e c 0)) (colSum c Prod.snd k.pq rows))
            (offSum Prod.fst k.pq rows))
          (Nat.add (Nat.add (Nat.mul k.g w.off) (colSum c Prod.fst k.pq rows))
            (offSum Prod.snd k.pq rows)))
      (List.range m))

/-- `f` holds for the members of two lists of the same length, taken in step. -/
noncomputable def all2 {α β : Type} (f : α → β → Bool) (xs : List α) : List β → Bool :=
  List.rec (motive := fun _ => List β → Bool)
    (fun ys => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) ys)
    (fun a _ ih ys =>
      List.rec (motive := fun _ => Bool) false (fun b bs _ => andB (f a b) (ih bs)) ys) xs

/-- `f` holds for the members of three lists of the same length, taken in step. -/
noncomputable def all3 {α β γ : Type} (f : α → β → γ → Bool) (xs : List α) :
    List β → List γ → Bool :=
  List.rec (motive := fun _ => List β → List γ → Bool)
    (fun ys zs =>
      List.rec (motive := fun _ => Bool)
        (List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) zs) (fun _ _ _ => false) ys)
    (fun a _ ih ys zs =>
      List.rec (motive := fun _ => Bool) false
        (fun b bs _ =>
          List.rec (motive := fun _ => Bool) false (fun c cs _ => andB (f a b c) (ih bs cs)) zs)
        ys) xs

/-- The `n` file vectors `rows` of one subspace have `m` entries each with correct stored sums
and norms, and every vector of `frame` is linked to them by its entry of `ks`. -/
noncomputable def linkFrame (m n : Nat) (rows frame : List Vec) (ks : List Coef) : Bool :=
  andB (Nat.beq (sumMap (fun _ => 1) rows) n)
    (andB (allB (okVec0 m) rows) (all2 (linkVec m rows) frame ks))

/-- Every frame of `c` is linked to the file vectors of the same position in `R`. -/
noncomputable def checkLink (m n : Nat) (R c : List Frame) (K : List (List Coef)) : Bool :=
  all3 (linkFrame m n) R c K

end Packing.Cert
