import Case5Hom0
import Case5Hom1
import Case5Hom2
import Case5Hom3
import Case5Hom4
import Case5Hom5
import Case5Hom6
import Case5Hom7
import Case5Hom8
import Case5Hom9
import Case5Hom10
import Case5Hom11
import Case5Hom12
import Case5Hom13
import Case5Hom14
import Case5Hom15
import Case5Hom16
import Case5Hom17
import Case5Coordinates
import N5Computations

noncomputable section
namespace UniserialComputations.Uniform.Case5
set_option maxHeartbeats 50000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
variable {R k : Type*} [CommRing R] [Field k] (π : R) (ρ : R →+* k)
variable (h : RingParameters 5 R k π ρ)
include h in
theorem image_mem (f : Data.objects5.EndRepresentatives π) : coordinates.reduce π ρ f ∈ N5.endAlgebra k := by
  constructor
  · intro a b hab
    fin_cases a <;> fin_cases b
    · exact (hab (by decide)).elim
    · exact zero_0_1_0_0 π ρ h (f 0 1)
    · exact zero_0_2_0_0 π ρ h (f 0 2)
    · exact zero_0_3_0_0 π ρ h (f 0 3)
    · exact zero_0_4_0_0 π ρ h (f 0 4)
    · exact zero_0_5_0_0 π ρ h (f 0 5)
    · exact zero_0_6_0_0 π ρ h (f 0 6)
    · exact zero_0_7_0_0 π ρ h (f 0 7)
    · exact zero_0_8_0_0 π ρ h (f 0 8)
    · exact zero_0_9_0_0 π ρ h (f 0 9)
    · exact zero_0_10_0_0 π ρ h (f 0 10)
    · exact zero_0_11_0_0 π ρ h (f 0 11)
    · exact zero_0_12_0_0 π ρ h (f 0 12)
    · exact zero_0_13_0_0 π ρ h (f 0 13)
    · exact zero_0_14_0_0 π ρ h (f 0 14)
    · exact zero_0_15_0_0 π ρ h (f 0 15)
    · exact zero_0_16_0_0 π ρ h (f 0 16)
    · exact zero_0_17_0_0 π ρ h (f 0 17)
    · exact zero_0_17_0_1 π ρ h (f 0 17)
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact zero_1_2_0_0 π ρ h (f 1 2)
    · exact zero_1_3_0_0 π ρ h (f 1 3)
    · exact zero_1_4_0_0 π ρ h (f 1 4)
    · exact zero_1_5_0_0 π ρ h (f 1 5)
    · exact zero_1_6_0_0 π ρ h (f 1 6)
    · exact zero_1_7_0_0 π ρ h (f 1 7)
    · exact zero_1_8_0_0 π ρ h (f 1 8)
    · exact zero_1_9_0_0 π ρ h (f 1 9)
    · exact zero_1_10_0_0 π ρ h (f 1 10)
    · exact zero_1_11_0_0 π ρ h (f 1 11)
    · exact zero_1_12_0_0 π ρ h (f 1 12)
    · exact zero_1_13_0_0 π ρ h (f 1 13)
    · exact zero_1_14_0_0 π ρ h (f 1 14)
    · exact zero_1_15_0_0 π ρ h (f 1 15)
    · exact zero_1_16_0_0 π ρ h (f 1 16)
    · exact zero_1_17_0_0 π ρ h (f 1 17)
    · exact zero_1_17_0_1 π ρ h (f 1 17)
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact zero_2_3_0_0 π ρ h (f 2 3)
    · exact zero_2_4_0_0 π ρ h (f 2 4)
    · exact zero_2_5_0_0 π ρ h (f 2 5)
    · exact (hab (by decide)).elim
    · exact zero_2_7_0_0 π ρ h (f 2 7)
    · exact zero_2_8_0_0 π ρ h (f 2 8)
    · exact (hab (by decide)).elim
    · exact zero_2_10_0_0 π ρ h (f 2 10)
    · exact zero_2_11_0_0 π ρ h (f 2 11)
    · exact zero_2_12_0_0 π ρ h (f 2 12)
    · exact (hab (by decide)).elim
    · exact zero_2_14_0_0 π ρ h (f 2 14)
    · exact zero_2_15_0_0 π ρ h (f 2 15)
    · exact zero_2_16_0_0 π ρ h (f 2 16)
    · exact (hab (by decide)).elim
    · exact zero_2_17_0_1 π ρ h (f 2 17)
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact zero_3_4_0_0 π ρ h (f 3 4)
    · exact zero_3_5_0_0 π ρ h (f 3 5)
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact zero_3_8_0_0 π ρ h (f 3 8)
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact zero_3_12_0_0 π ρ h (f 3 12)
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact zero_3_15_0_0 π ρ h (f 3 15)
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact zero_3_17_0_1 π ρ h (f 3 17)
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact zero_4_5_0_0 π ρ h (f 4 5)
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact zero_6_2_0_0 π ρ h (f 6 2)
    · exact zero_6_3_0_0 π ρ h (f 6 3)
    · exact zero_6_4_0_0 π ρ h (f 6 4)
    · exact zero_6_5_0_0 π ρ h (f 6 5)
    · exact (hab (by decide)).elim
    · exact zero_6_7_0_0 π ρ h (f 6 7)
    · exact zero_6_8_0_0 π ρ h (f 6 8)
    · exact zero_6_9_0_0 π ρ h (f 6 9)
    · exact zero_6_10_0_0 π ρ h (f 6 10)
    · exact zero_6_11_0_0 π ρ h (f 6 11)
    · exact zero_6_12_0_0 π ρ h (f 6 12)
    · exact zero_6_13_0_0 π ρ h (f 6 13)
    · exact zero_6_14_0_0 π ρ h (f 6 14)
    · exact zero_6_15_0_0 π ρ h (f 6 15)
    · exact zero_6_16_0_0 π ρ h (f 6 16)
    · exact zero_6_17_0_0 π ρ h (f 6 17)
    · exact zero_6_17_0_1 π ρ h (f 6 17)
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact zero_7_3_0_0 π ρ h (f 7 3)
    · exact zero_7_4_0_0 π ρ h (f 7 4)
    · exact zero_7_5_0_0 π ρ h (f 7 5)
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact zero_7_8_0_0 π ρ h (f 7 8)
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact zero_7_11_0_0 π ρ h (f 7 11)
    · exact zero_7_12_0_0 π ρ h (f 7 12)
    · exact (hab (by decide)).elim
    · exact zero_7_14_0_0 π ρ h (f 7 14)
    · exact zero_7_15_0_0 π ρ h (f 7 15)
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact zero_7_17_0_1 π ρ h (f 7 17)
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact zero_8_4_0_0 π ρ h (f 8 4)
    · exact zero_8_5_0_0 π ρ h (f 8 5)
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact zero_9_2_0_0 π ρ h (f 9 2)
    · exact zero_9_3_0_0 π ρ h (f 9 3)
    · exact zero_9_4_0_0 π ρ h (f 9 4)
    · exact zero_9_5_0_0 π ρ h (f 9 5)
    · exact (hab (by decide)).elim
    · exact zero_9_7_0_0 π ρ h (f 9 7)
    · exact zero_9_8_0_0 π ρ h (f 9 8)
    · exact (hab (by decide)).elim
    · exact zero_9_10_0_0 π ρ h (f 9 10)
    · exact zero_9_11_0_0 π ρ h (f 9 11)
    · exact zero_9_12_0_0 π ρ h (f 9 12)
    · exact zero_9_13_0_0 π ρ h (f 9 13)
    · exact zero_9_14_0_0 π ρ h (f 9 14)
    · exact zero_9_15_0_0 π ρ h (f 9 15)
    · exact zero_9_16_0_0 π ρ h (f 9 16)
    · exact zero_9_17_0_0 π ρ h (f 9 17)
    · exact zero_9_17_0_1 π ρ h (f 9 17)
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact zero_10_2_0_0 π ρ h (f 10 2)
    · exact zero_10_3_0_0 π ρ h (f 10 3)
    · exact zero_10_4_0_0 π ρ h (f 10 4)
    · exact zero_10_5_0_0 π ρ h (f 10 5)
    · exact (hab (by decide)).elim
    · exact zero_10_7_0_0 π ρ h (f 10 7)
    · exact zero_10_8_0_0 π ρ h (f 10 8)
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact zero_10_11_0_0 π ρ h (f 10 11)
    · exact zero_10_12_0_0 π ρ h (f 10 12)
    · exact zero_10_13_0_0 π ρ h (f 10 13)
    · exact zero_10_14_0_0 π ρ h (f 10 14)
    · exact zero_10_15_0_0 π ρ h (f 10 15)
    · exact zero_10_16_0_0 π ρ h (f 10 16)
    · exact (hab (by decide)).elim
    · exact zero_10_17_0_1 π ρ h (f 10 17)
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact zero_11_3_0_0 π ρ h (f 11 3)
    · exact zero_11_4_0_0 π ρ h (f 11 4)
    · exact zero_11_5_0_0 π ρ h (f 11 5)
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact zero_11_8_0_0 π ρ h (f 11 8)
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact zero_11_12_0_0 π ρ h (f 11 12)
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact zero_11_15_0_0 π ρ h (f 11 15)
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact zero_11_17_0_1 π ρ h (f 11 17)
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact zero_12_3_0_0 π ρ h (f 12 3)
    · exact zero_12_4_0_0 π ρ h (f 12 4)
    · exact zero_12_5_0_0 π ρ h (f 12 5)
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact zero_12_8_0_0 π ρ h (f 12 8)
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact zero_12_17_0_1 π ρ h (f 12 17)
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact zero_13_2_0_0 π ρ h (f 13 2)
    · exact zero_13_3_0_0 π ρ h (f 13 3)
    · exact zero_13_4_0_0 π ρ h (f 13 4)
    · exact zero_13_5_0_0 π ρ h (f 13 5)
    · exact (hab (by decide)).elim
    · exact zero_13_7_0_0 π ρ h (f 13 7)
    · exact zero_13_8_0_0 π ρ h (f 13 8)
    · exact (hab (by decide)).elim
    · exact zero_13_10_0_0 π ρ h (f 13 10)
    · exact zero_13_11_0_0 π ρ h (f 13 11)
    · exact zero_13_12_0_0 π ρ h (f 13 12)
    · exact (hab (by decide)).elim
    · exact zero_13_14_0_0 π ρ h (f 13 14)
    · exact zero_13_15_0_0 π ρ h (f 13 15)
    · exact zero_13_16_0_0 π ρ h (f 13 16)
    · exact (hab (by decide)).elim
    · exact zero_13_17_0_1 π ρ h (f 13 17)
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact zero_14_2_0_0 π ρ h (f 14 2)
    · exact zero_14_3_0_0 π ρ h (f 14 3)
    · exact zero_14_4_0_0 π ρ h (f 14 4)
    · exact zero_14_5_0_0 π ρ h (f 14 5)
    · exact (hab (by decide)).elim
    · exact zero_14_7_0_0 π ρ h (f 14 7)
    · exact zero_14_8_0_0 π ρ h (f 14 8)
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact zero_14_11_0_0 π ρ h (f 14 11)
    · exact zero_14_12_0_0 π ρ h (f 14 12)
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact zero_14_15_0_0 π ρ h (f 14 15)
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact zero_14_17_0_1 π ρ h (f 14 17)
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact zero_15_2_0_0 π ρ h (f 15 2)
    · exact zero_15_3_0_0 π ρ h (f 15 3)
    · exact zero_15_4_0_0 π ρ h (f 15 4)
    · exact zero_15_5_0_0 π ρ h (f 15 5)
    · exact (hab (by decide)).elim
    · exact zero_15_7_0_0 π ρ h (f 15 7)
    · exact zero_15_8_0_0 π ρ h (f 15 8)
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact zero_15_11_0_0 π ρ h (f 15 11)
    · exact zero_15_12_0_0 π ρ h (f 15 12)
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact zero_15_17_0_1 π ρ h (f 15 17)
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact zero_16_2_0_0 π ρ h (f 16 2)
    · exact zero_16_3_0_0 π ρ h (f 16 3)
    · exact zero_16_4_0_0 π ρ h (f 16 4)
    · exact zero_16_5_0_0 π ρ h (f 16 5)
    · exact (hab (by decide)).elim
    · exact zero_16_7_0_0 π ρ h (f 16 7)
    · exact zero_16_8_0_0 π ρ h (f 16 8)
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact zero_16_11_0_0 π ρ h (f 16 11)
    · exact zero_16_12_0_0 π ρ h (f 16 12)
    · exact (hab (by decide)).elim
    · exact zero_16_14_0_0 π ρ h (f 16 14)
    · exact zero_16_15_0_0 π ρ h (f 16 15)
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact zero_16_17_0_1 π ρ h (f 16 17)
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact zero_17_2_0_0 π ρ h (f 17 2)
    · exact zero_17_3_0_0 π ρ h (f 17 3)
    · exact zero_17_4_0_0 π ρ h (f 17 4)
    · exact zero_17_5_0_0 π ρ h (f 17 5)
    · exact (hab (by decide)).elim
    · exact zero_17_7_0_0 π ρ h (f 17 7)
    · exact zero_17_8_0_0 π ρ h (f 17 8)
    · exact (hab (by decide)).elim
    · exact zero_17_10_0_0 π ρ h (f 17 10)
    · exact zero_17_11_0_0 π ρ h (f 17 11)
    · exact zero_17_12_0_0 π ρ h (f 17 12)
    · exact zero_17_13_0_0 π ρ h (f 17 13)
    · exact zero_17_14_0_0 π ρ h (f 17 14)
    · exact zero_17_15_0_0 π ρ h (f 17 15)
    · exact zero_17_16_0_0 π ρ h (f 17 16)
    · exact (hab (by decide)).elim
    · exact zero_17_17_0_1 π ρ h (f 17 17)
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact zero_17_4_1_0 π ρ h (f 17 4)
    · exact zero_17_5_1_0 π ρ h (f 17 5)
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact zero_17_8_1_0 π ρ h (f 17 8)
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
    · exact (hab (by decide)).elim
  · exact diagonal_17 π ρ h (f 17 17)

def liftValues (v : Matrix (Fin 19) (Fin 19) R) : Data.objects5.EndRepresentatives π :=
  Fin.cases (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 0 0) (lift_0_0_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 0 1) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 0 2) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 0 3) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 0 4) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 0 5) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 0 6) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 0 7) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 0 8) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 0 9) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 0 10) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 0 11) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 0 12) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 0 13) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 0 14) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 0 15) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 0 16) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 0 17) (fun i => Fin.elim0 i))))))))))))))))))) (Fin.cases (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 1 0) (lift_1_0_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 1 1) (lift_1_1_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 1 2) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 1 3) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 1 4) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 1 5) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 1 6) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 1 7) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 1 8) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 1 9) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 1 10) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 1 11) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 1 12) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 1 13) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 1 14) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 1 15) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 1 16) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 1 17) (fun i => Fin.elim0 i))))))))))))))))))) (Fin.cases (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 2 0) (lift_2_0_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 2 1) (lift_2_1_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 2 2) (lift_2_2_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 2 3) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 2 4) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 2 5) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 2 6) (lift_2_6_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 2 7) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 2 8) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 2 9) (lift_2_9_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 2 10) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 2 11) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 2 12) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 2 13) (lift_2_13_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 2 14) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 2 15) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 2 16) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 2 17) (lift_2_17_0_0 π ρ h)) (fun i => Fin.elim0 i))))))))))))))))))) (Fin.cases (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 3 0) (lift_3_0_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 3 1) (lift_3_1_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 3 2) (lift_3_2_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 3 3) (lift_3_3_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 3 4) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 3 5) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 3 6) (lift_3_6_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 3 7) (lift_3_7_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 3 8) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 3 9) (lift_3_9_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 3 10) (lift_3_10_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 3 11) (lift_3_11_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 3 12) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 3 13) (lift_3_13_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 3 14) (lift_3_14_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 3 15) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 3 16) (lift_3_16_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 3 17) (lift_3_17_0_0 π ρ h)) (fun i => Fin.elim0 i))))))))))))))))))) (Fin.cases (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 4 0) (lift_4_0_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 4 1) (lift_4_1_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 4 2) (lift_4_2_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 4 3) (lift_4_3_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 4 4) (lift_4_4_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 4 5) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 4 6) (lift_4_6_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 4 7) (lift_4_7_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 4 8) (lift_4_8_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 4 9) (lift_4_9_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 4 10) (lift_4_10_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 4 11) (lift_4_11_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 4 12) (lift_4_12_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 4 13) (lift_4_13_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 4 14) (lift_4_14_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 4 15) (lift_4_15_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 4 16) (lift_4_16_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.add Data.objects5 π (ObjectFamily.Hom.scale Data.objects5 π (v 4 17) (lift_4_17_0_0 π ρ h)) (ObjectFamily.Hom.scale Data.objects5 π (v 4 18) (lift_4_17_0_1 π ρ h))) (fun i => Fin.elim0 i))))))))))))))))))) (Fin.cases (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 5 0) (lift_5_0_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 5 1) (lift_5_1_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 5 2) (lift_5_2_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 5 3) (lift_5_3_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 5 4) (lift_5_4_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 5 5) (lift_5_5_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 5 6) (lift_5_6_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 5 7) (lift_5_7_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 5 8) (lift_5_8_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 5 9) (lift_5_9_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 5 10) (lift_5_10_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 5 11) (lift_5_11_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 5 12) (lift_5_12_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 5 13) (lift_5_13_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 5 14) (lift_5_14_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 5 15) (lift_5_15_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 5 16) (lift_5_16_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.add Data.objects5 π (ObjectFamily.Hom.scale Data.objects5 π (v 5 17) (lift_5_17_0_0 π ρ h)) (ObjectFamily.Hom.scale Data.objects5 π (v 5 18) (lift_5_17_0_1 π ρ h))) (fun i => Fin.elim0 i))))))))))))))))))) (Fin.cases (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 6 0) (lift_6_0_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 6 1) (lift_6_1_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 6 2) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 6 3) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 6 4) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 6 5) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 6 6) (lift_6_6_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 6 7) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 6 8) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 6 9) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 6 10) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 6 11) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 6 12) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 6 13) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 6 14) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 6 15) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 6 16) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 6 17) (fun i => Fin.elim0 i))))))))))))))))))) (Fin.cases (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 7 0) (lift_7_0_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 7 1) (lift_7_1_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 7 2) (lift_7_2_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 7 3) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 7 4) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 7 5) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 7 6) (lift_7_6_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 7 7) (lift_7_7_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 7 8) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 7 9) (lift_7_9_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 7 10) (lift_7_10_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 7 11) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 7 12) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 7 13) (lift_7_13_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 7 14) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 7 15) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 7 16) (lift_7_16_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 7 17) (lift_7_17_0_0 π ρ h)) (fun i => Fin.elim0 i))))))))))))))))))) (Fin.cases (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 8 0) (lift_8_0_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 8 1) (lift_8_1_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 8 2) (lift_8_2_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 8 3) (lift_8_3_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 8 4) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 8 5) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 8 6) (lift_8_6_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 8 7) (lift_8_7_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 8 8) (lift_8_8_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 8 9) (lift_8_9_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 8 10) (lift_8_10_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 8 11) (lift_8_11_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 8 12) (lift_8_12_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 8 13) (lift_8_13_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 8 14) (lift_8_14_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 8 15) (lift_8_15_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 8 16) (lift_8_16_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.add Data.objects5 π (ObjectFamily.Hom.scale Data.objects5 π (v 8 17) (lift_8_17_0_0 π ρ h)) (ObjectFamily.Hom.scale Data.objects5 π (v 8 18) (lift_8_17_0_1 π ρ h))) (fun i => Fin.elim0 i))))))))))))))))))) (Fin.cases (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 9 0) (lift_9_0_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 9 1) (lift_9_1_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 9 2) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 9 3) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 9 4) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 9 5) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 9 6) (lift_9_6_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 9 7) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 9 8) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 9 9) (lift_9_9_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 9 10) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 9 11) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 9 12) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 9 13) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 9 14) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 9 15) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 9 16) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 9 17) (fun i => Fin.elim0 i))))))))))))))))))) (Fin.cases (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 10 0) (lift_10_0_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 10 1) (lift_10_1_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 10 2) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 10 3) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 10 4) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 10 5) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 10 6) (lift_10_6_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 10 7) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 10 8) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 10 9) (lift_10_9_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 10 10) (lift_10_10_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 10 11) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 10 12) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 10 13) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 10 14) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 10 15) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 10 16) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 10 17) (lift_10_17_0_0 π ρ h)) (fun i => Fin.elim0 i))))))))))))))))))) (Fin.cases (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 11 0) (lift_11_0_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 11 1) (lift_11_1_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 11 2) (lift_11_2_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 11 3) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 11 4) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 11 5) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 11 6) (lift_11_6_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 11 7) (lift_11_7_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 11 8) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 11 9) (lift_11_9_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 11 10) (lift_11_10_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 11 11) (lift_11_11_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 11 12) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 11 13) (lift_11_13_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 11 14) (lift_11_14_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 11 15) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 11 16) (lift_11_16_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 11 17) (lift_11_17_0_0 π ρ h)) (fun i => Fin.elim0 i))))))))))))))))))) (Fin.cases (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 12 0) (lift_12_0_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 12 1) (lift_12_1_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 12 2) (lift_12_2_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 12 3) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 12 4) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 12 5) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 12 6) (lift_12_6_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 12 7) (lift_12_7_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 12 8) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 12 9) (lift_12_9_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 12 10) (lift_12_10_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 12 11) (lift_12_11_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 12 12) (lift_12_12_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 12 13) (lift_12_13_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 12 14) (lift_12_14_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 12 15) (lift_12_15_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 12 16) (lift_12_16_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 12 17) (lift_12_17_0_0 π ρ h)) (fun i => Fin.elim0 i))))))))))))))))))) (Fin.cases (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 13 0) (lift_13_0_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 13 1) (lift_13_1_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 13 2) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 13 3) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 13 4) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 13 5) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 13 6) (lift_13_6_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 13 7) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 13 8) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 13 9) (lift_13_9_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 13 10) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 13 11) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 13 12) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 13 13) (lift_13_13_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 13 14) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 13 15) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 13 16) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 13 17) (lift_13_17_0_0 π ρ h)) (fun i => Fin.elim0 i))))))))))))))))))) (Fin.cases (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 14 0) (lift_14_0_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 14 1) (lift_14_1_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 14 2) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 14 3) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 14 4) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 14 5) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 14 6) (lift_14_6_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 14 7) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 14 8) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 14 9) (lift_14_9_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 14 10) (lift_14_10_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 14 11) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 14 12) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 14 13) (lift_14_13_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 14 14) (lift_14_14_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 14 15) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 14 16) (lift_14_16_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 14 17) (lift_14_17_0_0 π ρ h)) (fun i => Fin.elim0 i))))))))))))))))))) (Fin.cases (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 15 0) (lift_15_0_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 15 1) (lift_15_1_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 15 2) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 15 3) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 15 4) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 15 5) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 15 6) (lift_15_6_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 15 7) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 15 8) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 15 9) (lift_15_9_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 15 10) (lift_15_10_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 15 11) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 15 12) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 15 13) (lift_15_13_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 15 14) (lift_15_14_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 15 15) (lift_15_15_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 15 16) (lift_15_16_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 15 17) (lift_15_17_0_0 π ρ h)) (fun i => Fin.elim0 i))))))))))))))))))) (Fin.cases (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 16 0) (lift_16_0_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 16 1) (lift_16_1_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 16 2) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 16 3) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 16 4) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 16 5) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 16 6) (lift_16_6_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 16 7) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 16 8) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 16 9) (lift_16_9_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 16 10) (lift_16_10_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 16 11) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 16 12) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 16 13) (lift_16_13_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 16 14) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 16 15) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 16 16) (lift_16_16_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 16 17) (lift_16_17_0_0 π ρ h)) (fun i => Fin.elim0 i))))))))))))))))))) (Fin.cases (Fin.cases (ObjectFamily.Hom.add Data.objects5 π (ObjectFamily.Hom.scale Data.objects5 π (v 17 0) (lift_17_0_0_0 π ρ h)) (ObjectFamily.Hom.scale Data.objects5 π (v 18 0) (lift_17_0_1_0 π ρ h))) (Fin.cases (ObjectFamily.Hom.add Data.objects5 π (ObjectFamily.Hom.scale Data.objects5 π (v 17 1) (lift_17_1_0_0 π ρ h)) (ObjectFamily.Hom.scale Data.objects5 π (v 18 1) (lift_17_1_1_0 π ρ h))) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 18 2) (lift_17_2_1_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 18 3) (lift_17_3_1_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 17 4) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 17 5) (Fin.cases (ObjectFamily.Hom.add Data.objects5 π (ObjectFamily.Hom.scale Data.objects5 π (v 17 6) (lift_17_6_0_0 π ρ h)) (ObjectFamily.Hom.scale Data.objects5 π (v 18 6) (lift_17_6_1_0 π ρ h))) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 18 7) (lift_17_7_1_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.zero Data.objects5 π 17 8) (Fin.cases (ObjectFamily.Hom.add Data.objects5 π (ObjectFamily.Hom.scale Data.objects5 π (v 17 9) (lift_17_9_0_0 π ρ h)) (ObjectFamily.Hom.scale Data.objects5 π (v 18 9) (lift_17_9_1_0 π ρ h))) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 18 10) (lift_17_10_1_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 18 11) (lift_17_11_1_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 18 12) (lift_17_12_1_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 18 13) (lift_17_13_1_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 18 14) (lift_17_14_1_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 18 15) (lift_17_15_1_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects5 π (v 18 16) (lift_17_16_1_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.add Data.objects5 π (ObjectFamily.Hom.scale Data.objects5 π (v 17 17) (lift_17_17_0_0 π ρ h)) (ObjectFamily.Hom.scale Data.objects5 π (v 18 17) (lift_17_17_1_0 π ρ h))) (fun i => Fin.elim0 i))))))))))))))))))) (fun i => Fin.elim0 i))))))))))))))))))

end UniserialComputations.Uniform.Case5
