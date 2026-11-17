import Challenge.Frame
import Challenge.Cert.Check
open Module Matrix
open scoped InnerProductSpace
namespace Packing
def HasPacking (m n N : ℕ) (t : ℝ) : Prop :=
  ∃ U : Fin N → Submodule ℝ (EuclideanSpace ℝ (Fin m)),
    (∀ i, finrank ℝ (U i) = n) ∧ ∀ i j, i ≠ j → t ≤ subspaceChordalSq (U i) (U j)

namespace Cert
section Unfold
variable {α : Type}
end Unfold
noncomputable def toVec (m : ℕ) (v : Vec) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 fun i => ((v.e.getD i 0 : ℕ) : ℝ) - v.off

structure OkFrame (m : ℕ) (F : Frame) : Prop where
  len : ∀ v ∈ F, v.e.length = m
  sum : ∀ v ∈ F, sumMap (fun x => x) v.e = v.sum
  nsq : ∀ v ∈ F, v.nsq + dotY v v = dotX m v v
  pos : ∀ v ∈ F, 1 ≤ v.nsq
  orth : F.Pairwise fun u v => dotX m u v = dotY u v

noncomputable def fam (m : ℕ) (F : Frame) : Fin F.length → EuclideanSpace ℝ (Fin m) :=
  fun a => toVec m (F.get a)

/-- The subspace of `ℝ^m` spanned by a frame. -/
noncomputable def frameSpan (m : ℕ) (F : Frame) : Submodule ℝ (EuclideanSpace ℝ (Fin m)) :=
  Submodule.span ℝ (Set.range (fam m F))

section Frames
variable {m : ℕ} {F G : Frame}
end Frames
def SpansPack (m n N : ℕ) (t : ℝ) (R : List Frame) : Prop :=
  R.length = N ∧
    (∀ i : Fin R.length, (R.get i).length = n ∧ ∀ v ∈ R.get i, v.e.length = m) ∧
    (∀ i : Fin R.length, finrank ℝ (frameSpan m (R.get i)) = n) ∧
    ∀ i j : Fin R.length, i ≠ j →
      t ≤ subspaceChordalSq (frameSpan m (R.get i)) (frameSpan m (R.get j))

/-- What a passing check says about the data: `N` frames of `n` pairwise orthogonal nonzero
vectors whose spans have dimension `n` and are pairwise at squared chordal distance at least
`k / 10^10`. -/
theorem spansPack_of_check {m n N k : ℕ} {c : List Frame} (h : check m n N k c = true) :
    (∀ i : Fin c.length, (c.get i).length = n ∧ OkFrame m (c.get i)) ∧
      SpansPack m n N ((k : ℝ) / 10 ^ 10) c := by
  sorry

theorem hasPacking_of_check {m n N k : ℕ} {c : List Frame} (h : check m n N k c = true) :
    HasPacking m n N ((k : ℝ) / 10 ^ 10) := by
  sorry

end Cert
end Packing
