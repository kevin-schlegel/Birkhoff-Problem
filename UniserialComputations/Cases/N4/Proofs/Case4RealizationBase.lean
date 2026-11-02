import Case4Hom0
import Case4Hom1
import Case4Hom2
import Case4Hom3
import Case4Hom4
import Case4Hom5
import Case4Hom6
import Case4Hom7
import Case4Hom8
import Case4Coordinates
import Final

noncomputable section
namespace UniserialComputations.Uniform.Case4
set_option maxHeartbeats 50000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
variable {R k : Type*} [CommRing R] [Field k] (π : R) (ρ : R →+* k)
variable (h : RingParameters 4 R k π ρ)
include h in
theorem image_mem (f : Data.objects4.EndRepresentatives π) : coordinates.reduce π ρ f ∈ N4.endAlgebra k := by
  intro a b hab
  fin_cases a <;> fin_cases b
  · exact (hab (by decide)).elim
  · exact (hab (by decide)).elim
  · exact (hab (by decide)).elim
  · exact (hab (by decide)).elim
  · exact (hab (by decide)).elim
  · exact (hab (by decide)).elim
  · exact (hab (by decide)).elim
  · exact (hab (by decide)).elim
  · exact (hab (by decide)).elim
  · exact zero_1_0_0_0 π ρ h (f 1 0)
  · exact (hab (by decide)).elim
  · exact (hab (by decide)).elim
  · exact (hab (by decide)).elim
  · exact (hab (by decide)).elim
  · exact (hab (by decide)).elim
  · exact (hab (by decide)).elim
  · exact (hab (by decide)).elim
  · exact (hab (by decide)).elim
  · exact zero_2_0_0_0 π ρ h (f 2 0)
  · exact zero_2_1_0_0 π ρ h (f 2 1)
  · exact (hab (by decide)).elim
  · exact (hab (by decide)).elim
  · exact (hab (by decide)).elim
  · exact (hab (by decide)).elim
  · exact (hab (by decide)).elim
  · exact (hab (by decide)).elim
  · exact (hab (by decide)).elim
  · exact zero_3_0_0_0 π ρ h (f 3 0)
  · exact zero_3_1_0_0 π ρ h (f 3 1)
  · exact zero_3_2_0_0 π ρ h (f 3 2)
  · exact (hab (by decide)).elim
  · exact zero_3_4_0_0 π ρ h (f 3 4)
  · exact (hab (by decide)).elim
  · exact (hab (by decide)).elim
  · exact (hab (by decide)).elim
  · exact (hab (by decide)).elim
  · exact zero_4_0_0_0 π ρ h (f 4 0)
  · exact zero_4_1_0_0 π ρ h (f 4 1)
  · exact zero_4_2_0_0 π ρ h (f 4 2)
  · exact zero_4_3_0_0 π ρ h (f 4 3)
  · exact (hab (by decide)).elim
  · exact (hab (by decide)).elim
  · exact (hab (by decide)).elim
  · exact (hab (by decide)).elim
  · exact (hab (by decide)).elim
  · exact zero_5_0_0_0 π ρ h (f 5 0)
  · exact zero_5_1_0_0 π ρ h (f 5 1)
  · exact zero_5_2_0_0 π ρ h (f 5 2)
  · exact zero_5_3_0_0 π ρ h (f 5 3)
  · exact zero_5_4_0_0 π ρ h (f 5 4)
  · exact (hab (by decide)).elim
  · exact (hab (by decide)).elim
  · exact (hab (by decide)).elim
  · exact (hab (by decide)).elim
  · exact zero_6_0_0_0 π ρ h (f 6 0)
  · exact zero_6_1_0_0 π ρ h (f 6 1)
  · exact zero_6_2_0_0 π ρ h (f 6 2)
  · exact zero_6_3_0_0 π ρ h (f 6 3)
  · exact zero_6_4_0_0 π ρ h (f 6 4)
  · exact zero_6_5_0_0 π ρ h (f 6 5)
  · exact (hab (by decide)).elim
  · exact (hab (by decide)).elim
  · exact (hab (by decide)).elim
  · exact zero_7_0_0_0 π ρ h (f 7 0)
  · exact zero_7_1_0_0 π ρ h (f 7 1)
  · exact zero_7_2_0_0 π ρ h (f 7 2)
  · exact zero_7_3_0_0 π ρ h (f 7 3)
  · exact zero_7_4_0_0 π ρ h (f 7 4)
  · exact zero_7_5_0_0 π ρ h (f 7 5)
  · exact zero_7_6_0_0 π ρ h (f 7 6)
  · exact (hab (by decide)).elim
  · exact (hab (by decide)).elim
  · exact zero_8_0_0_0 π ρ h (f 8 0)
  · exact zero_8_1_0_0 π ρ h (f 8 1)
  · exact zero_8_2_0_0 π ρ h (f 8 2)
  · exact zero_8_3_0_0 π ρ h (f 8 3)
  · exact zero_8_4_0_0 π ρ h (f 8 4)
  · exact zero_8_5_0_0 π ρ h (f 8 5)
  · exact zero_8_6_0_0 π ρ h (f 8 6)
  · exact zero_8_7_0_0 π ρ h (f 8 7)
  · exact (hab (by decide)).elim

def liftValues (v : Matrix (Fin 9) (Fin 9) R) : Data.objects4.EndRepresentatives π :=
  Fin.cases (Fin.cases (ObjectFamily.Hom.scale Data.objects4 π (v 0 0) (lift_0_0_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects4 π (v 0 1) (lift_0_1_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects4 π (v 0 2) (lift_0_2_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects4 π (v 0 3) (lift_0_3_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects4 π (v 0 4) (lift_0_4_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects4 π (v 0 5) (lift_0_5_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects4 π (v 0 6) (lift_0_6_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects4 π (v 0 7) (lift_0_7_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects4 π (v 0 8) (lift_0_8_0_0 π ρ h)) (fun i => Fin.elim0 i)))))))))) (Fin.cases (Fin.cases (ObjectFamily.Hom.zero Data.objects4 π 1 0) (Fin.cases (ObjectFamily.Hom.scale Data.objects4 π (v 1 1) (lift_1_1_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects4 π (v 1 2) (lift_1_2_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects4 π (v 1 3) (lift_1_3_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects4 π (v 1 4) (lift_1_4_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects4 π (v 1 5) (lift_1_5_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects4 π (v 1 6) (lift_1_6_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects4 π (v 1 7) (lift_1_7_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects4 π (v 1 8) (lift_1_8_0_0 π ρ h)) (fun i => Fin.elim0 i)))))))))) (Fin.cases (Fin.cases (ObjectFamily.Hom.zero Data.objects4 π 2 0) (Fin.cases (ObjectFamily.Hom.zero Data.objects4 π 2 1) (Fin.cases (ObjectFamily.Hom.scale Data.objects4 π (v 2 2) (lift_2_2_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects4 π (v 2 3) (lift_2_3_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects4 π (v 2 4) (lift_2_4_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects4 π (v 2 5) (lift_2_5_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects4 π (v 2 6) (lift_2_6_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects4 π (v 2 7) (lift_2_7_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects4 π (v 2 8) (lift_2_8_0_0 π ρ h)) (fun i => Fin.elim0 i)))))))))) (Fin.cases (Fin.cases (ObjectFamily.Hom.zero Data.objects4 π 3 0) (Fin.cases (ObjectFamily.Hom.zero Data.objects4 π 3 1) (Fin.cases (ObjectFamily.Hom.zero Data.objects4 π 3 2) (Fin.cases (ObjectFamily.Hom.scale Data.objects4 π (v 3 3) (lift_3_3_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.zero Data.objects4 π 3 4) (Fin.cases (ObjectFamily.Hom.scale Data.objects4 π (v 3 5) (lift_3_5_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects4 π (v 3 6) (lift_3_6_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects4 π (v 3 7) (lift_3_7_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects4 π (v 3 8) (lift_3_8_0_0 π ρ h)) (fun i => Fin.elim0 i)))))))))) (Fin.cases (Fin.cases (ObjectFamily.Hom.zero Data.objects4 π 4 0) (Fin.cases (ObjectFamily.Hom.zero Data.objects4 π 4 1) (Fin.cases (ObjectFamily.Hom.zero Data.objects4 π 4 2) (Fin.cases (ObjectFamily.Hom.zero Data.objects4 π 4 3) (Fin.cases (ObjectFamily.Hom.scale Data.objects4 π (v 4 4) (lift_4_4_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects4 π (v 4 5) (lift_4_5_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects4 π (v 4 6) (lift_4_6_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects4 π (v 4 7) (lift_4_7_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects4 π (v 4 8) (lift_4_8_0_0 π ρ h)) (fun i => Fin.elim0 i)))))))))) (Fin.cases (Fin.cases (ObjectFamily.Hom.zero Data.objects4 π 5 0) (Fin.cases (ObjectFamily.Hom.zero Data.objects4 π 5 1) (Fin.cases (ObjectFamily.Hom.zero Data.objects4 π 5 2) (Fin.cases (ObjectFamily.Hom.zero Data.objects4 π 5 3) (Fin.cases (ObjectFamily.Hom.zero Data.objects4 π 5 4) (Fin.cases (ObjectFamily.Hom.scale Data.objects4 π (v 5 5) (lift_5_5_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects4 π (v 5 6) (lift_5_6_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects4 π (v 5 7) (lift_5_7_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects4 π (v 5 8) (lift_5_8_0_0 π ρ h)) (fun i => Fin.elim0 i)))))))))) (Fin.cases (Fin.cases (ObjectFamily.Hom.zero Data.objects4 π 6 0) (Fin.cases (ObjectFamily.Hom.zero Data.objects4 π 6 1) (Fin.cases (ObjectFamily.Hom.zero Data.objects4 π 6 2) (Fin.cases (ObjectFamily.Hom.zero Data.objects4 π 6 3) (Fin.cases (ObjectFamily.Hom.zero Data.objects4 π 6 4) (Fin.cases (ObjectFamily.Hom.zero Data.objects4 π 6 5) (Fin.cases (ObjectFamily.Hom.scale Data.objects4 π (v 6 6) (lift_6_6_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects4 π (v 6 7) (lift_6_7_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects4 π (v 6 8) (lift_6_8_0_0 π ρ h)) (fun i => Fin.elim0 i)))))))))) (Fin.cases (Fin.cases (ObjectFamily.Hom.zero Data.objects4 π 7 0) (Fin.cases (ObjectFamily.Hom.zero Data.objects4 π 7 1) (Fin.cases (ObjectFamily.Hom.zero Data.objects4 π 7 2) (Fin.cases (ObjectFamily.Hom.zero Data.objects4 π 7 3) (Fin.cases (ObjectFamily.Hom.zero Data.objects4 π 7 4) (Fin.cases (ObjectFamily.Hom.zero Data.objects4 π 7 5) (Fin.cases (ObjectFamily.Hom.zero Data.objects4 π 7 6) (Fin.cases (ObjectFamily.Hom.scale Data.objects4 π (v 7 7) (lift_7_7_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects4 π (v 7 8) (lift_7_8_0_0 π ρ h)) (fun i => Fin.elim0 i)))))))))) (Fin.cases (Fin.cases (ObjectFamily.Hom.zero Data.objects4 π 8 0) (Fin.cases (ObjectFamily.Hom.zero Data.objects4 π 8 1) (Fin.cases (ObjectFamily.Hom.zero Data.objects4 π 8 2) (Fin.cases (ObjectFamily.Hom.zero Data.objects4 π 8 3) (Fin.cases (ObjectFamily.Hom.zero Data.objects4 π 8 4) (Fin.cases (ObjectFamily.Hom.zero Data.objects4 π 8 5) (Fin.cases (ObjectFamily.Hom.zero Data.objects4 π 8 6) (Fin.cases (ObjectFamily.Hom.zero Data.objects4 π 8 7) (Fin.cases (ObjectFamily.Hom.scale Data.objects4 π (v 8 8) (lift_8_8_0_0 π ρ h)) (fun i => Fin.elim0 i)))))))))) (fun i => Fin.elim0 i)))))))))

end UniserialComputations.Uniform.Case4
