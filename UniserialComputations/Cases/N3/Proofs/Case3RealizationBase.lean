import Case3Hom0
import Case3Hom1
import Case3Hom2
import Case3Hom3
import Case3Hom4
import Case3Coordinates
import Final

noncomputable section
namespace UniserialComputations.Uniform.Case3
set_option maxHeartbeats 50000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
variable {R k : Type*} [CommRing R] [Field k] (π : R) (ρ : R →+* k)
variable (h : RingParameters 3 R k π ρ)
include h in
theorem image_mem (f : Data.objects3.EndRepresentatives π) : coordinates.reduce π ρ f ∈ Chain.endAlgebra k 5 := by
  intro a b hab
  fin_cases a <;> fin_cases b
  · norm_num at hab
  · norm_num at hab
  · norm_num at hab
  · norm_num at hab
  · norm_num at hab
  · exact zero_1_0_0_0 π ρ h (f 1 0)
  · norm_num at hab
  · norm_num at hab
  · norm_num at hab
  · norm_num at hab
  · exact zero_2_0_0_0 π ρ h (f 2 0)
  · exact zero_2_1_0_0 π ρ h (f 2 1)
  · norm_num at hab
  · norm_num at hab
  · norm_num at hab
  · exact zero_3_0_0_0 π ρ h (f 3 0)
  · exact zero_3_1_0_0 π ρ h (f 3 1)
  · exact zero_3_2_0_0 π ρ h (f 3 2)
  · norm_num at hab
  · norm_num at hab
  · exact zero_4_0_0_0 π ρ h (f 4 0)
  · exact zero_4_1_0_0 π ρ h (f 4 1)
  · exact zero_4_2_0_0 π ρ h (f 4 2)
  · exact zero_4_3_0_0 π ρ h (f 4 3)
  · norm_num at hab

def liftValues (v : Matrix (Fin 5) (Fin 5) R) : Data.objects3.EndRepresentatives π :=
  Fin.cases (Fin.cases (ObjectFamily.Hom.scale Data.objects3 π (v 0 0) (lift_0_0_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects3 π (v 0 1) (lift_0_1_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects3 π (v 0 2) (lift_0_2_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects3 π (v 0 3) (lift_0_3_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects3 π (v 0 4) (lift_0_4_0_0 π ρ h)) (fun i => Fin.elim0 i)))))) (Fin.cases (Fin.cases (ObjectFamily.Hom.zero Data.objects3 π 1 0) (Fin.cases (ObjectFamily.Hom.scale Data.objects3 π (v 1 1) (lift_1_1_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects3 π (v 1 2) (lift_1_2_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects3 π (v 1 3) (lift_1_3_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects3 π (v 1 4) (lift_1_4_0_0 π ρ h)) (fun i => Fin.elim0 i)))))) (Fin.cases (Fin.cases (ObjectFamily.Hom.zero Data.objects3 π 2 0) (Fin.cases (ObjectFamily.Hom.zero Data.objects3 π 2 1) (Fin.cases (ObjectFamily.Hom.scale Data.objects3 π (v 2 2) (lift_2_2_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects3 π (v 2 3) (lift_2_3_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects3 π (v 2 4) (lift_2_4_0_0 π ρ h)) (fun i => Fin.elim0 i)))))) (Fin.cases (Fin.cases (ObjectFamily.Hom.zero Data.objects3 π 3 0) (Fin.cases (ObjectFamily.Hom.zero Data.objects3 π 3 1) (Fin.cases (ObjectFamily.Hom.zero Data.objects3 π 3 2) (Fin.cases (ObjectFamily.Hom.scale Data.objects3 π (v 3 3) (lift_3_3_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects3 π (v 3 4) (lift_3_4_0_0 π ρ h)) (fun i => Fin.elim0 i)))))) (Fin.cases (Fin.cases (ObjectFamily.Hom.zero Data.objects3 π 4 0) (Fin.cases (ObjectFamily.Hom.zero Data.objects3 π 4 1) (Fin.cases (ObjectFamily.Hom.zero Data.objects3 π 4 2) (Fin.cases (ObjectFamily.Hom.zero Data.objects3 π 4 3) (Fin.cases (ObjectFamily.Hom.scale Data.objects3 π (v 4 4) (lift_4_4_0_0 π ρ h)) (fun i => Fin.elim0 i)))))) (fun i => Fin.elim0 i)))))

end UniserialComputations.Uniform.Case3
