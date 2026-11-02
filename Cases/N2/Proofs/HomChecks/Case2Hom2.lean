import Case2Data

noncomputable section
namespace UniserialComputations.Uniform.Case2
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
variable {R k : Type*} [CommRing R] [Field k] (π : R) (ρ : R →+* k)
variable (h : RingParameters 2 R k π ρ)

include h in
theorem zero_2_0_0_0 (f : Data.objects2.Hom π 2 0) : ρ (f.ambient 0 0) = 0 := by
  apply (h.top_annihilator _).mp
  have e2 := f.commutes 0 0
  norm_num [Data.objects2, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at e2
  linear_combination ((1)*π)*e2

include h in
theorem zero_2_1_0_0 (f : Data.objects2.Hom π 2 1) : ρ (f.ambient 0 0) = 0 := by
  apply (h.top_annihilator _).mp
  have e2 := f.commutes 0 0
  norm_num [Data.objects2, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at e2
  linear_combination ((1)*1)*e2

include h in
def lift_2_2_0_0 : Data.objects2.Hom π 2 2 where
  ambient := !![(1)*1]
  source := !![0]
  ambient_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects2, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^2=0 from by rw [show 2=2+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^3=0 from by rw [show 3=2+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^4=0 from by rw [show 4=2+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^5=0 from by rw [show 5=2+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=2+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=2+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  source_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects2, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^2=0 from by rw [show 2=2+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^3=0 from by rw [show 3=2+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^4=0 from by rw [show 4=2+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^5=0 from by rw [show 5=2+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=2+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=2+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  commutes := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects2, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^2=0 from by rw [show 2=2+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^3=0 from by rw [show 3=2+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^4=0 from by rw [show 4=2+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^5=0 from by rw [show 5=2+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=2+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=2+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring

end UniserialComputations.Uniform.Case2
