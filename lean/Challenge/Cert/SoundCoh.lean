import Challenge.Cert.SoundPoints
open Module
open scoped InnerProductSpace
namespace Packing
def HasCoherence (d N : ℕ) (t : ℝ) : Prop :=
  ∃ x : Fin N → EuclideanSpace ℂ (Fin d),
    (∀ i, ‖x i‖ = 1) ∧ ∀ i j, i ≠ j → ‖⟪x i, x j⟫_ℂ‖ ≤ t

namespace Cert
noncomputable def toCVec (m : ℕ) (u : CVec) : EuclideanSpace ℂ (Fin m) :=
  WithLp.toLp 2 fun k => ((toVec m u.re k : ℝ) : ℂ) + ((toVec m u.im k : ℝ) : ℂ) * Complex.I

section Pairs
variable {m : ℕ} {u v : CVec}
end Pairs
def CoherenceData (m N : ℕ) (t : ℝ) (c : List CVec) : Prop :=
  c.length = N ∧ (∀ u ∈ c, u.re.e.length = m ∧ u.im.e.length = m) ∧
    (∀ i : Fin c.length, toCVec m (c.get i) ≠ 0) ∧
    ∀ i j : Fin c.length, i ≠ j →
      ‖⟪toCVec m (c.get i), toCVec m (c.get j)⟫_ℂ‖
        ≤ t * (‖toCVec m (c.get i)‖ * ‖toCVec m (c.get j)‖)

theorem coherenceData_of_check {m N t : ℕ} {c : List CVec} (h : checkCoh m N t c = true) :
    CoherenceData m N ((t : ℝ) / 10 ^ 12) c := by
  sorry

theorem hasCoherence_of_check {m N t : ℕ} {c : List CVec} (h : checkCoh m N t c = true) :
    HasCoherence m N ((t : ℝ) / 10 ^ 12) := by
  sorry

end Cert
end Packing
