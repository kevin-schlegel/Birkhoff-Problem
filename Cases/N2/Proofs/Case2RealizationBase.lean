import Case2Hom0
import Case2Hom1
import Case2Hom2
import Case2Coordinates
import Final

noncomputable section
namespace UniserialComputations.Uniform.Case2
set_option maxHeartbeats 50000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
variable {R k : Type*} [CommRing R] [Field k] (π : R) (ρ : R →+* k)
variable (h : RingParameters 2 R k π ρ)
include h in
theorem image_mem (f : Data.objects2.EndRepresentatives π) : coordinates.reduce π ρ f ∈ N2.endAlgebra k := by
  intro a b hab
  fin_cases a <;> fin_cases b
  · norm_num at hab
  · norm_num at hab
  · norm_num at hab
  · exact zero_1_0_0_0 π ρ h (f 1 0)
  · norm_num at hab
  · norm_num at hab
  · exact zero_2_0_0_0 π ρ h (f 2 0)
  · exact zero_2_1_0_0 π ρ h (f 2 1)
  · norm_num at hab

def liftValues (v : Matrix (Fin 3) (Fin 3) R) : Data.objects2.EndRepresentatives π :=
  Fin.cases (Fin.cases (ObjectFamily.Hom.scale Data.objects2 π (v 0 0) (lift_0_0_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects2 π (v 0 1) (lift_0_1_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects2 π (v 0 2) (lift_0_2_0_0 π ρ h)) (fun i => Fin.elim0 i)))) (Fin.cases (Fin.cases (ObjectFamily.Hom.zero Data.objects2 π 1 0) (Fin.cases (ObjectFamily.Hom.scale Data.objects2 π (v 1 1) (lift_1_1_0_0 π ρ h)) (Fin.cases (ObjectFamily.Hom.scale Data.objects2 π (v 1 2) (lift_1_2_0_0 π ρ h)) (fun i => Fin.elim0 i)))) (Fin.cases (Fin.cases (ObjectFamily.Hom.zero Data.objects2 π 2 0) (Fin.cases (ObjectFamily.Hom.zero Data.objects2 π 2 1) (Fin.cases (ObjectFamily.Hom.scale Data.objects2 π (v 2 2) (lift_2_2_0_0 π ρ h)) (fun i => Fin.elim0 i)))) (fun i => Fin.elim0 i)))

end UniserialComputations.Uniform.Case2
