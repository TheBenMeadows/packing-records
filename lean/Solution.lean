import Packing
import Packing.Cert.Cells.C_3_1_43
import Packing.Cert.Cells.G_3_24
import Packing.Cert.Cells.S_6_138
import Packing.Cert.Cells.H4_30
import Packing.Cert.Cells.H5_39
import Packing.Cert.Cells.H6_16
import Packing.Cert.Cells.U_135

/-!
The module that `lake comparator` judges against `Challenge.lean`. It imports the library and
the seven sampled cell files, and proves each sampled cell as `Packing/Cert/All.lean` and
`Packing/Cert/AllPoints.lean` do.
-/

namespace Packing.Cert

theorem packing_3_1_43 : HasPacking 3 1 43 (1469199245 / 10 ^ 10) := by
  simpa only [Nat.cast_ofNat] using hasPacking_of_check Cells.ok_3_1_43

theorem gos_3_24 : HasCoherence 3 24 (719064770738 / 10 ^ 12) := by
  simpa only [Nat.cast_ofNat] using hasCoherence_of_check Cells.ok_gos_3_24

theorem sph_6_138 : HasSphericalCode 6 138 (633669770336 / 10 ^ 12) := by
  simpa only [Nat.cast_ofNat] using hasSphericalCode_of_check Cells.ok_sph_6_138

theorem hsp4_30 : HasBallPackingInBall 4 30 (315996223410 / 10 ^ 12) := by
  simpa only [Nat.cast_ofNat] using hasBallPackingInBall_of_check Cells.ok_hsp4_30

theorem hsp5_39 : HasBallPackingInBall 5 39 (333339360904 / 10 ^ 12) := by
  simpa only [Nat.cast_ofNat] using hasBallPackingInBall_of_check Cells.ok_hsp5_39

theorem hsp6_16 : HasBallPackingInBall 6 16 (391649418582 / 10 ^ 12) := by
  simpa only [Nat.cast_ofNat] using hasBallPackingInBall_of_check Cells.ok_hsp6_16

theorem scu_135 : HasBallPackingInCube 135 (100073715194 / 10 ^ 12) := by
  simpa only [Nat.cast_ofNat] using hasBallPackingInCube_of_check Cells.ok_scu_135

end Packing.Cert
