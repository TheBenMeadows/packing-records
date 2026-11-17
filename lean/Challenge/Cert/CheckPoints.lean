import Challenge.Cert.Check
namespace Packing.Cert
noncomputable def orB (a b : Bool) : Bool := Bool.rec b true a

/-- `|a - b|` for natural numbers. -/
noncomputable def absSub (a b : Nat) : Nat := Nat.add (Nat.sub a b) (Nat.sub b a)

/-- `v` has `m` entries and its stored sum and squared norm are correct. The vector may be
zero. -/
noncomputable def okVec0 (m : Nat) (v : Vec) : Bool :=
  andB (Nat.beq (sumMap (fun _ => 1) v.e) m)
    (andB (Nat.beq (sumMap (fun x => x) v.e) v.sum)
      (Nat.beq (Nat.add v.nsq (dotY v v)) (dotX m v v)))

/-! ### Spherical codes -/

/-- The cosine of the angle between the vectors meant by `u` and `v` is at most `t / q`, given
as `t2 = t^2` and `q2 = q^2`: the dot product is not positive, or its square times `q2` is at
most `t2 |u|² |v|²`. -/
noncomputable def cosB (m t2 q2 : Nat) (u v : Vec) : Bool :=
  orB (Nat.ble (dotX m u v) (dotY u v))
    (Nat.ble (Nat.mul (Nat.mul (absDot m u v) (absDot m u v)) q2)
      (Nat.mul t2 (Nat.mul u.nsq v.nsq)))

/-- `c` holds `N` nonzero vectors of `ℤ^m` whose pairwise cosines are at most `t / 10^12`. -/
noncomputable def checkSph (m N t : Nat) (c : List Vec) : Bool :=
  andB (Nat.beq (sumMap (fun _ => 1) c) N)
    (andB (allB (okVec m) c)
      (pairwiseB (cosB m (Nat.mul t t) (Nat.pow 10 24)) c))

/-! ### Complex line packings -/

/-- A vector of `ℤ[i]^m`: real parts and imaginary parts. -/
structure CVec where
  re : Vec
  im : Vec

/-- The squared norm of a complex vector. -/
noncomputable def cnsq (u : CVec) : Nat := Nat.add u.re.nsq u.im.nsq

/-- Both parts have `m` entries with correct stored sums and norms, and the vector is not zero. -/
noncomputable def okCVec (m : Nat) (u : CVec) : Bool :=
  andB (okVec0 m u.re) (andB (okVec0 m u.im) (Nat.ble 1 (cnsq u)))

/-- The absolute value of the real part of the Hermitian product of `u` and `v`. -/
noncomputable def absRe (m : Nat) (u v : CVec) : Nat :=
  absSub (Nat.add (dotX m u.re v.re) (dotX m u.im v.im))
    (Nat.add (dotY u.re v.re) (dotY u.im v.im))

/-- The absolute value of the imaginary part of the Hermitian product of `u` and `v`. -/
noncomputable def absIm (m : Nat) (u v : CVec) : Nat :=
  absSub (Nat.add (dotX m u.re v.im) (dotY u.im v.re))
    (Nat.add (dotY u.re v.im) (dotX m u.im v.re))

/-- `|<u, v>|² q2 ≤ t2 |u|² |v|²`. -/
noncomputable def cohB (m t2 q2 : Nat) (u v : CVec) : Bool :=
  Nat.ble
    (Nat.mul (Nat.add (Nat.mul (absRe m u v) (absRe m u v)) (Nat.mul (absIm m u v) (absIm m u v)))
      q2)
    (Nat.mul t2 (Nat.mul (cnsq u) (cnsq v)))

/-- `c` holds `N` nonzero vectors of `ℤ[i]^m` whose pairwise normalized Hermitian products have
absolute value at most `t / 10^12`. -/
noncomputable def checkCoh (m N t : Nat) (c : List CVec) : Bool :=
  andB (Nat.beq (sumMap (fun _ => 1) c) N)
    (andB (allB (okCVec m) c)
      (pairwiseB (cohB m (Nat.mul t t) (Nat.pow 10 24)) c))

/-! ### Balls in the unit ball and in the unit cube -/

/-- `|u - v|² q2 ≥ c`, written without subtraction:
`(|u|² + |v|² + 2 dotY) q2 ≥ c + 2 dotX q2`. -/
noncomputable def farB (m q2 c : Nat) (u v : Vec) : Bool :=
  Nat.ble (Nat.add c (Nat.mul (Nat.mul 2 (dotX m u v)) q2))
    (Nat.mul (Nat.add (Nat.add u.nsq v.nsq) (Nat.mul 2 (dotY u v))) q2)

/-- `c` holds `N` points of `ℤ^m` which, divided by `S`, are the centres of balls of radius
`t / 10^12` inside the unit ball with pairwise disjoint interiors: every norm is at most
`(1 - t/10^12) S` and every two points are at distance at least `2 (t/10^12) S`. -/
noncomputable def checkBall (m N t S : Nat) (c : List Vec) : Bool :=
  andB (Nat.beq (sumMap (fun _ => 1) c) N)
    (andB (Nat.ble 1 S)
      (andB (Nat.ble t (Nat.pow 10 12))
        (andB (allB (okVec0 m) c)
          (andB
            (allB (fun v => Nat.ble (Nat.mul v.nsq (Nat.pow 10 24))
              (Nat.mul (Nat.mul (Nat.sub (Nat.pow 10 12) t) (Nat.sub (Nat.pow 10 12) t))
                (Nat.mul S S))) c)
            (pairwiseB (farB m (Nat.pow 10 24) (Nat.mul (Nat.mul 4 (Nat.mul t t)) (Nat.mul S S)))
              c)))))

/-- Every entry of `v` is within `w / (2 · 10^12)` of zero:
`2 · 10^12 · |e - off| ≤ w`, written without subtraction. -/
noncomputable def boxB (w : Nat) (v : Vec) : Bool :=
  allB (fun x =>
    andB (Nat.ble (Nat.mul (Nat.mul 2 (Nat.pow 10 12)) x)
        (Nat.add (Nat.mul (Nat.mul 2 (Nat.pow 10 12)) v.off) w))
      (Nat.ble (Nat.mul (Nat.mul 2 (Nat.pow 10 12)) v.off)
        (Nat.add (Nat.mul (Nat.mul 2 (Nat.pow 10 12)) x) w))) v.e

/-- `c` holds `N` points of `ℤ^3` which, divided by `S`, are the centres of balls of radius
`t / 10^12` inside the cube `[-1/2, 1/2]^3` with pairwise disjoint interiors: every coordinate is
at most `(1/2 - t/10^12) S` in absolute value and every two points are at distance at least
`2 (t/10^12) S`. -/
noncomputable def checkCube (N t S : Nat) (c : List Vec) : Bool :=
  andB (Nat.beq (sumMap (fun _ => 1) c) N)
    (andB (Nat.ble 1 S)
      (andB (Nat.ble (Nat.mul 2 t) (Nat.pow 10 12))
        (andB (allB (okVec0 3) c)
          (andB (allB (boxB (Nat.mul (Nat.sub (Nat.pow 10 12) (Nat.mul 2 t)) S)) c)
            (pairwiseB (farB 3 (Nat.pow 10 24) (Nat.mul (Nat.mul 4 (Nat.mul t t)) (Nat.mul S S)))
              c)))))

end Packing.Cert
