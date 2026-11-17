import Challenge.Cert.SoundPoints
import Challenge.Cert.CheckLink
open Module
open scoped InnerProductSpace
namespace Packing.Cert
section Lists
variable {α β γ : Type}
end Lists
section Link
variable {m : ℕ}
end Link
theorem spansPack_of_link {m n N k : ℕ} {R c : List Frame} {K : List (List Coef)}
    (hc : check m n N k c = true) (hl : checkLink m n R c K = true) :
    SpansPack m n N ((k : ℝ) / 10 ^ 10) R := by
  sorry

end Packing.Cert
