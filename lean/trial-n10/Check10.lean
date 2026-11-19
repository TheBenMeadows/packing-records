/-
Locked statement for the N = 10 trial. Written before either lane runs; lanes never edit it.
Compile from a lane's lean/ directory: lake env lean <path>/Check10.lean
The axiom line must list only propext, Classical.choice and Quot.sound.
-/
import Packing.Cube
import Packing.Cube10

open Packing.Cube

example : IsMaxMinDist 10 (3 / 4) := Packing.Cube.isMaxMinDist_ten

#print axioms Packing.Cube.isMaxMinDist_ten
