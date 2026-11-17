import Challenge.Cert.Sound
import Challenge.Cert.SoundPoints
import Challenge.Cert.SoundCoh

/-!
One record cell from each of the seven tables, stated as in `Packing/Cert/All.lean` and
`Packing/Cert/AllPoints.lean`. `Solution.lean` proves the same statements from the cell files.
-/

namespace Packing.Cert

theorem packing_3_1_43 : HasPacking 3 1 43 (1469199245 / 10 ^ 10) := by
  sorry

theorem gos_3_24 : HasCoherence 3 24 (719064770738 / 10 ^ 12) := by
  sorry

theorem sph_6_138 : HasSphericalCode 6 138 (633669770336 / 10 ^ 12) := by
  sorry

theorem hsp4_30 : HasBallPackingInBall 4 30 (315996223410 / 10 ^ 12) := by
  sorry

theorem hsp5_39 : HasBallPackingInBall 5 39 (333339360904 / 10 ^ 12) := by
  sorry

theorem hsp6_16 : HasBallPackingInBall 6 16 (391649418582 / 10 ^ 12) := by
  sorry

theorem scu_135 : HasBallPackingInCube 135 (100073715194 / 10 ^ 12) := by
  sorry

end Packing.Cert
