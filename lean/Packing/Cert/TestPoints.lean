/-
Known-answer tests for the checkers of `Packing.Cert.CheckPoints`. Each checker is run on a
small configuration whose exact value is known, at the largest or smallest threshold it must
accept and at the next one, which it must reject. The remaining cases break one condition at a
time: the count, the length of a vector, a stored sum, a stored squared norm, a zero vector, the
container, the separation, the scale.

A vector is written with its entries shifted by 10: `⟨[11, 10], 10, 21, 1⟩` is `(1, 0)`.
-/
import Packing.Cert.CheckPoints

namespace Packing.Cert.Test

/-! ### Spherical codes: `(1, 0)` and `(1, 1)` have cosine `1/√2 = 0.70710678118654...` -/

def sph : List Vec := [⟨[11, 10], 10, 21, 1⟩, ⟨[11, 11], 10, 22, 2⟩]

example : checkSph 2 2 707106781187 sph = true := by decide +kernel
example : checkSph 2 2 707106781186 sph = false := by decide +kernel
example : checkSph 2 3 707106781187 sph = false := by decide +kernel
example : checkSph 3 2 707106781187 sph = false := by decide +kernel
/-- A wrong stored sum. -/
example : checkSph 2 2 707106781187 [⟨[11, 10], 10, 20, 1⟩, ⟨[11, 11], 10, 22, 2⟩] = false := by
  decide +kernel
/-- A wrong stored squared norm. -/
example : checkSph 2 2 707106781187 [⟨[11, 10], 10, 21, 1⟩, ⟨[11, 11], 10, 22, 3⟩] = false := by
  decide +kernel
/-- A zero vector has no direction. -/
example : checkSph 2 2 707106781187 [⟨[10, 10], 10, 20, 0⟩, ⟨[11, 11], 10, 22, 2⟩] = false := by
  decide +kernel
/-- `(1, 0)` and `(-1, 1)` have a negative cosine, accepted at threshold 0. -/
example : checkSph 2 2 0 [⟨[11, 10], 10, 21, 1⟩, ⟨[9, 11], 10, 20, 2⟩] = true := by decide +kernel
/-- `(1, 0)` and `(0, 1)` have cosine 0; `(1, 0)` and `(1, 1)` are rejected at threshold 0. -/
example : checkSph 2 2 0 [⟨[11, 10], 10, 21, 1⟩, ⟨[10, 11], 10, 21, 1⟩] = true := by decide +kernel
example : checkSph 2 2 0 sph = false := by decide +kernel

/-! ### Complex lines -/

/-- `(1, i)` and `(i, -1) = i (1, i)` span the same line: coherence exactly 1, all of it in the
imaginary part of the Hermitian product. -/
def sameLine : List CVec :=
  [⟨⟨[11, 10], 10, 21, 1⟩, ⟨[10, 11], 10, 21, 1⟩⟩, ⟨⟨[10, 9], 10, 19, 1⟩, ⟨[11, 10], 10, 21, 1⟩⟩]

example : checkCoh 2 2 1000000000000 sameLine = true := by decide +kernel
example : checkCoh 2 2 999999999999 sameLine = false := by decide +kernel
example : checkCoh 2 2 0 sameLine = false := by decide +kernel

/-- `(1, i)` and `(1, -i)` are orthogonal: coherence 0. -/
def orthLines : List CVec :=
  [⟨⟨[11, 10], 10, 21, 1⟩, ⟨[10, 11], 10, 21, 1⟩⟩, ⟨⟨[11, 10], 10, 21, 1⟩, ⟨[10, 9], 10, 19, 1⟩⟩]

example : checkCoh 2 2 0 orthLines = true := by decide +kernel

/-- `(1, 0)` and `(1, i)` have coherence `1/√2`. -/
def halfLines : List CVec :=
  [⟨⟨[11, 10], 10, 21, 1⟩, ⟨[10, 10], 10, 20, 0⟩⟩, ⟨⟨[11, 10], 10, 21, 1⟩, ⟨[10, 11], 10, 21, 1⟩⟩]

example : checkCoh 2 2 707106781187 halfLines = true := by decide +kernel
example : checkCoh 2 2 707106781186 halfLines = false := by decide +kernel
example : checkCoh 2 3 707106781187 halfLines = false := by decide +kernel
example : checkCoh 3 2 707106781187 halfLines = false := by decide +kernel
/-- A wrong stored squared norm in an imaginary part. -/
example : checkCoh 2 2 707106781187
    [⟨⟨[11, 10], 10, 21, 1⟩, ⟨[10, 10], 10, 20, 0⟩⟩, ⟨⟨[11, 10], 10, 21, 1⟩, ⟨[10, 11], 10, 21, 2⟩⟩]
    = false := by
  decide +kernel
/-- The zero vector. -/
example : checkCoh 2 2 1000000000000
    [⟨⟨[10, 10], 10, 20, 0⟩, ⟨[10, 10], 10, 20, 0⟩⟩, ⟨⟨[11, 10], 10, 21, 1⟩, ⟨[10, 11], 10, 21, 1⟩⟩]
    = false := by
  decide +kernel

/-! ### Balls in the unit ball: two discs of radius `1/2` centred at `(±1/2, 0)` fill the unit
disc exactly. The data are the centres times `S = 2`. -/

def twoDiscs : List Vec := [⟨[11, 10], 10, 21, 1⟩, ⟨[9, 10], 10, 19, 1⟩]

example : checkBall 2 2 500000000000 2 twoDiscs = true := by decide +kernel
example : checkBall 2 2 500000000001 2 twoDiscs = false := by decide +kernel
example : checkBall 2 3 500000000000 2 twoDiscs = false := by decide +kernel
example : checkBall 3 2 500000000000 2 twoDiscs = false := by decide +kernel
/-- Scale 0 is rejected. -/
example : checkBall 2 2 0 0 twoDiscs = false := by decide +kernel
/-- Centres `(±1, 0)`: far enough apart for radius `1/2`, but outside the container. -/
example : checkBall 2 2 500000000000 2 [⟨[12, 10], 10, 22, 4⟩, ⟨[8, 10], 10, 18, 4⟩] = false := by
  decide +kernel
/-- Centres `(±1/10, 0)` with radius `1/5`: inside the container, but overlapping. -/
example : checkBall 2 2 200000000000 10 twoDiscs = false := by decide +kernel
/-- The same centres with radius `1/10` touch. -/
example : checkBall 2 2 100000000000 10 twoDiscs = true := by decide +kernel
example : checkBall 2 2 100000000001 10 twoDiscs = false := by decide +kernel
/-- A wrong stored squared norm. -/
example : checkBall 2 2 100000000000 10 [⟨[11, 10], 10, 21, 2⟩, ⟨[9, 10], 10, 19, 1⟩] = false := by
  decide +kernel
/-- A radius above 1. -/
example : checkBall 2 1 1000000000001 2 [⟨[10, 10], 10, 20, 0⟩] = false := by decide +kernel
/-- One ball of radius 1 centred at the origin. -/
example : checkBall 2 1 1000000000000 2 [⟨[10, 10], 10, 20, 0⟩] = true := by decide +kernel

/-! ### Balls in the cube `[-1/2, 1/2]^3`: eight balls of radius `1/4` centred at
`(±1/4, ±1/4, ±1/4)`. The data are the centres times `S = 4`. -/

def eightBalls : List Vec :=
  [⟨[11, 11, 11], 10, 33, 3⟩, ⟨[11, 11, 9], 10, 31, 3⟩, ⟨[11, 9, 11], 10, 31, 3⟩,
    ⟨[11, 9, 9], 10, 29, 3⟩, ⟨[9, 11, 11], 10, 31, 3⟩, ⟨[9, 11, 9], 10, 29, 3⟩,
    ⟨[9, 9, 11], 10, 29, 3⟩, ⟨[9, 9, 9], 10, 27, 3⟩]

example : checkCube 8 250000000000 4 eightBalls = true := by decide +kernel
example : checkCube 8 250000000001 4 eightBalls = false := by decide +kernel
example : checkCube 9 250000000000 4 eightBalls = false := by decide +kernel
example : checkCube 8 250000000000 0 eightBalls = false := by decide +kernel

/-- Centres `(±2/5, 0, 0)`, data times `S = 10`. Radius `1/10` fits; radius `1/5` is far enough
apart but leaves the cube. -/
def twoBalls : List Vec := [⟨[14, 10, 10], 10, 34, 16⟩, ⟨[6, 10, 10], 10, 26, 16⟩]

example : checkCube 2 100000000000 10 twoBalls = true := by decide +kernel
example : checkCube 2 100000000001 10 twoBalls = false := by decide +kernel
example : checkCube 2 200000000000 10 twoBalls = false := by decide +kernel
/-- Centres `(±1/10, 0, 0)` with radius `1/5`: inside the cube, but overlapping. -/
example : checkCube 2 200000000000 10 [⟨[11, 10, 10], 10, 31, 1⟩, ⟨[9, 10, 10], 10, 29, 1⟩]
    = false := by
  decide +kernel
/-- A vector with two entries is not a point of the cube. -/
example : checkCube 2 100000000000 10 [⟨[14, 10], 10, 24, 16⟩, ⟨[6, 10, 10], 10, 26, 16⟩]
    = false := by
  decide +kernel
/-- A wrong stored sum. -/
example : checkCube 2 100000000000 10 [⟨[14, 10, 10], 10, 33, 16⟩, ⟨[6, 10, 10], 10, 26, 16⟩]
    = false := by
  decide +kernel
/-- A radius above `1/2`. -/
example : checkCube 1 500000000001 10 [⟨[10, 10, 10], 10, 30, 0⟩] = false := by decide +kernel
/-- One ball of radius `1/2` centred in the cube. -/
example : checkCube 1 500000000000 10 [⟨[10, 10, 10], 10, 30, 0⟩] = true := by decide +kernel

end Packing.Cert.Test
