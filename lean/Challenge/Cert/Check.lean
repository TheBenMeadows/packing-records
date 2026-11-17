namespace Packing.Cert
structure Vec where
  e : List Nat
  off : Nat
  sum : Nat
  nsq : Nat

/-- A frame: the vectors spanning one subspace. -/
abbrev Frame := List Vec

/-- `∑ i, xs i * ys i`. -/
noncomputable def dotN (xs : List Nat) : List Nat → Nat :=
  List.rec (motive := fun _ => List Nat → Nat) (fun _ => 0)
    (fun a _ ih ys =>
      List.rec (motive := fun _ => Nat) 0 (fun b bs _ => Nat.add (Nat.mul a b) (ih bs)) ys) xs

/-- `∑ a ∈ l, f a`. -/
noncomputable def sumMap {α : Type} (f : α → Nat) (l : List α) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun a _ ih => Nat.add (f a) ih) l

/-- Boolean conjunction that does not look at `b` when `a` is `false`. -/
noncomputable def andB (a b : Bool) : Bool := Bool.rec false b a

/-- `f` holds for every member of `l`. -/
noncomputable def allB {α : Type} (f : α → Bool) (l : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => andB (f a) ih) l

/-- `r a b` holds whenever `a` comes before `b` in `l`. -/
noncomputable def pairwiseB {α : Type} (r : α → α → Bool) (l : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a rest ih => andB (allB (r a) rest) ih) l

/-- With `dotY`, the dot product of the vectors meant by `u` and `v` is `dotX - dotY`. -/
noncomputable def dotX (m : Nat) (u v : Vec) : Nat :=
  Nat.add (dotN u.e v.e) (Nat.mul m (Nat.mul u.off v.off))

noncomputable def dotY (u v : Vec) : Nat :=
  Nat.add (Nat.mul v.off u.sum) (Nat.mul u.off v.sum)

/-- The absolute value of the dot product of the vectors meant by `u` and `v`. -/
noncomputable def absDot (m : Nat) (u v : Vec) : Nat :=
  Nat.add (Nat.sub (dotX m u v) (dotY u v)) (Nat.sub (dotY u v) (dotX m u v))

/-- `v` has `m` entries, its stored sum and squared norm are correct, and it is not zero. -/
noncomputable def okVec (m : Nat) (v : Vec) : Bool :=
  andB (Nat.beq (sumMap (fun _ => 1) v.e) m)
    (andB (Nat.beq (sumMap (fun x => x) v.e) v.sum)
      (andB (Nat.beq (Nat.add v.nsq (dotY v v)) (dotX m v v)) (Nat.ble 1 v.nsq)))

/-- `F` holds `n` pairwise orthogonal nonzero vectors of `ℤ^m`. -/
noncomputable def okFrame (m n : Nat) (F : Frame) : Bool :=
  andB (Nat.beq (sumMap (fun _ => 1) F) n)
    (andB (allB (okVec m) F) (pairwiseB (fun u v => Nat.beq (dotX m u v) (dotY u v)) F))

/-- An integer upper bound for `D · (u·v)² / (|u|² |v|²)`. -/
noncomputable def term (m D : Nat) (u v : Vec) : Nat :=
  Nat.add (Nat.div (Nat.mul (Nat.mul (absDot m u v) (absDot m u v)) D) (Nat.mul u.nsq v.nsq)) 1

/-- An integer upper bound for `D · tr(P_F P_G)`, where `P_F` and `P_G` are the orthogonal
projectors onto the spans of `F` and `G`. -/
noncomputable def pairSum (m D : Nat) (F G : Frame) : Nat :=
  sumMap (fun u => sumMap (fun v => term m D u v) G) F

/-- `c` holds `N` frames of `n` pairwise orthogonal nonzero vectors of `ℤ^m`, and the spans of
every two frames are at squared chordal distance at least `k / 10^10`. -/
noncomputable def check (m n N k : Nat) (c : List Frame) : Bool :=
  andB (Nat.beq (sumMap (fun _ => 1) c) N)
    (andB (Nat.ble k (Nat.mul n (Nat.pow 10 10)))
      (andB (allB (okFrame m n) c)
        (pairwiseB (fun F G => Nat.ble (pairSum m (Nat.pow 10 40) F G)
          (Nat.mul (Nat.sub (Nat.mul n (Nat.pow 10 10)) k) (Nat.pow 10 30))) c)))

end Packing.Cert
