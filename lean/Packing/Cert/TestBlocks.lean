/-
Known-answer tests for `Packing.Cert.CheckBlocks`: the check between two blocks, and a small
code checked in two blocks and in one evaluation.

The vectors are `(1, 0)`, `(1, 1)` and `(0, 1)`, with entries shifted by 10. The cosines are
`1/√2 = 0.70710678118654...` between `(1, 1)` and each of the others, and `0` between `(1, 0)`
and `(0, 1)`.
-/
import Packing.Cert.CheckBlocks

namespace Packing.Cert.Test

def blkA : List Vec := [⟨[11, 10], 10, 21, 1⟩]

def blkB : List Vec := [⟨[11, 11], 10, 22, 2⟩, ⟨[10, 11], 10, 21, 1⟩]

/-- The relation of `checkSph` at threshold `t / 10^12` in dimension 2. -/
noncomputable def rel (t : Nat) : Vec → Vec → Bool := cosB 2 (Nat.mul t t) (Nat.pow 10 24)

/-! ### Between two blocks

`(-1, 0)` is `⟨[9, 10], 10, 19, 1⟩`. At threshold 0 a pair passes when its dot product is not
positive: `(1, 0)` and `(-1, 0)` pass against `(0, 1)`, `(-1, 0)` passes against `(1, 1)`, and
`(1, 0)` fails against `(1, 1)`. -/

example : crossB (rel 707106781187) blkA blkB = true := by decide +kernel
/-- One step below the cosine of `(1, 0)` and `(1, 1)`, a pair that lies in different blocks. -/
example : crossB (rel 707106781186) blkA blkB = false := by decide +kernel
/-- Nothing to compare. -/
example : crossB (rel 0) [] blkB = true := by decide +kernel
example : crossB (rel 0) blkA [] = true := by decide +kernel
/-- The only failing pair has the last member of the first block: `(-1, 0)` passes against
`(1, 1)` and `(1, 0)` does not. -/
example : crossB (rel 0) [⟨[9, 10], 10, 19, 1⟩] [⟨[11, 11], 10, 22, 2⟩] = true := by
  decide +kernel
example : crossB (rel 0) [⟨[9, 10], 10, 19, 1⟩, ⟨[11, 10], 10, 21, 1⟩] [⟨[11, 11], 10, 22, 2⟩]
    = false := by decide +kernel
/-- The only failing pair has the last member of the second block. -/
example : crossB (rel 0) blkA [⟨[10, 11], 10, 21, 1⟩] = true := by decide +kernel
example : crossB (rel 0) blkA [⟨[10, 11], 10, 21, 1⟩, ⟨[11, 11], 10, 22, 2⟩] = false := by
  decide +kernel
/-- The only failing pair is the first member of one block with the second of the other, so
comparing the blocks member by member in step would miss it. -/
example : crossB (rel 0) [⟨[11, 10], 10, 21, 1⟩, ⟨[9, 10], 10, 19, 1⟩]
    [⟨[10, 11], 10, 21, 1⟩, ⟨[11, 11], 10, 22, 2⟩] = false := by decide +kernel
/-- `crossB` does not compare the members of one block with each other: `blkB` holds the pair
`(1, 1)`, `(0, 1)`, which fails at threshold 0. -/
example : crossB (rel 0) [⟨[9, 10], 10, 19, 1⟩] blkB = true := by decide +kernel
example : pairwiseB (rel 0) blkB = false := by decide +kernel

/-! ### A code in two blocks -/

theorem blk_v : andB (Nat.beq (sumMap (fun _ => 1) (blkA ++ blkB)) 3)
    (allB (okVec 2) (blkA ++ blkB)) = true := by decide +kernel

theorem blk_p1 : pairwiseB (rel 707106781187) blkA = true := by decide +kernel

theorem blk_c : crossB (rel 707106781187) blkA blkB = true := by decide +kernel

theorem blk_p2 : pairwiseB (rel 707106781187) blkB = true := by decide +kernel

/-- The joined statement, from the four evaluations above. -/
theorem blk_joined : checkSph 2 3 707106781187 (blkA ++ blkB) = true :=
  checkSph_of_blocks blk_v (pairwiseB_append blk_p1 blk_c blk_p2)

/-- The same statement in one evaluation, and its failure one step below. -/
example : checkSph 2 3 707106781187 (blkA ++ blkB) = true := by decide +kernel
example : checkSph 2 3 707106781186 (blkA ++ blkB) = false := by decide +kernel

/-- Each block passes on its own and only the pair across the blocks fails. -/
example : pairwiseB (rel 0) [⟨[11, 10], 10, 21, 1⟩] = true := by decide +kernel
example : pairwiseB (rel 0) [⟨[11, 11], 10, 22, 2⟩] = true := by decide +kernel
example : crossB (rel 0) [⟨[11, 10], 10, 21, 1⟩] [⟨[11, 11], 10, 22, 2⟩] = false := by
  decide +kernel
example : pairwiseB (rel 0) ([⟨[11, 10], 10, 21, 1⟩] ++ [⟨[11, 11], 10, 22, 2⟩]) = false := by
  decide +kernel

/-! ### A code in three blocks, joined as the generator joins them

`(1, 0)`, `(-1, 0)` and `(0, 1)` have pairwise dot products `-1`, `0` and `0`. -/

def triX : List Vec := [⟨[11, 10], 10, 21, 1⟩]

def triY : List Vec := [⟨[9, 10], 10, 19, 1⟩]

def triZ : List Vec := [⟨[10, 11], 10, 21, 1⟩]

theorem tri_v : andB (Nat.beq (sumMap (fun _ => 1) (triX ++ (triY ++ triZ))) 3)
    (allB (okVec 2) (triX ++ (triY ++ triZ))) = true := by decide +kernel

theorem tri_p1 : pairwiseB (rel 0) triX = true := by decide +kernel

theorem tri_p2 : pairwiseB (rel 0) triY = true := by decide +kernel

theorem tri_p3 : pairwiseB (rel 0) triZ = true := by decide +kernel

theorem tri_c12 : crossB (rel 0) triX triY = true := by decide +kernel

theorem tri_c13 : crossB (rel 0) triX triZ = true := by decide +kernel

theorem tri_c23 : crossB (rel 0) triY triZ = true := by decide +kernel

theorem tri_joined : checkSph 2 3 0 (triX ++ (triY ++ triZ)) = true :=
  checkSph_of_blocks tri_v
    (pairwiseB_append tri_p1 (crossB_append tri_c12 tri_c13) (pairwiseB_append tri_p2 tri_c23 tri_p3))

example : checkSph 2 3 0 (triX ++ (triY ++ triZ)) = true := by decide +kernel

/-- With `(1, 1)` as the third block the only failing pair is between the first block and the
third: every block and the other two pairs of blocks pass, and the whole list fails. -/
example : crossB (rel 0) triX [⟨[11, 11], 10, 22, 2⟩] = false := by decide +kernel
example : crossB (rel 0) triY [⟨[11, 11], 10, 22, 2⟩] = true := by decide +kernel
example : pairwiseB (rel 0) (triX ++ (triY ++ [⟨[11, 11], 10, 22, 2⟩])) = false := by
  decide +kernel

end Packing.Cert.Test
