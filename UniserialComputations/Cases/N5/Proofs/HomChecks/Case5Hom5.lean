import Case5Data

noncomputable section
namespace UniserialComputations.Uniform.Case5
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
variable {R k : Type*} [CommRing R] [Field k] (π : R) (ρ : R →+* k)
variable (h : RingParameters 5 R k π ρ)

include h in
def lift_5_0_0_0 : Data.objects5.Hom π 5 0 where
  ambient := !![(1)*1,0,0;0,0,0;0,0,0]
  source := !![0,0;0,0]
  ambient_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  source_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  commutes := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring

include h in
def lift_5_1_0_0 : Data.objects5.Hom π 5 1 where
  ambient := !![(1)*1,0,0;0,0,0;0,0,0]
  source := !![(1)*π^4,0;0,0]
  ambient_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  source_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  commutes := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring

include h in
def lift_5_2_0_0 : Data.objects5.Hom π 5 2 where
  ambient := !![(1)*1,0,0;0,0,0;0,0,0]
  source := !![(1)*π^3,0;0,0]
  ambient_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  source_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  commutes := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring

include h in
def lift_5_3_0_0 : Data.objects5.Hom π 5 3 where
  ambient := !![(1)*1,0,0;0,0,0;0,0,0]
  source := !![(1)*π^2,0;0,0]
  ambient_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  source_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  commutes := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring

include h in
def lift_5_4_0_0 : Data.objects5.Hom π 5 4 where
  ambient := !![(1)*1,0,0;0,0,0;0,0,0]
  source := !![(1)*π,0;0,0]
  ambient_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  source_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  commutes := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring

include h in
def lift_5_5_0_0 : Data.objects5.Hom π 5 5 where
  ambient := !![(1)*1,0,0;0,0,0;0,0,0]
  source := !![(1)*1,0;0,0]
  ambient_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  source_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  commutes := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring

include h in
def lift_5_6_0_0 : Data.objects5.Hom π 5 6 where
  ambient := !![(1)*1,0,0;0,0,0;0,0,0]
  source := !![(1)*π^3,0;0,0]
  ambient_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  source_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  commutes := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring

include h in
def lift_5_7_0_0 : Data.objects5.Hom π 5 7 where
  ambient := !![(1)*1,0,0;0,0,0;0,0,0]
  source := !![(1)*π^2,0;0,0]
  ambient_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  source_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  commutes := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring

include h in
def lift_5_8_0_0 : Data.objects5.Hom π 5 8 where
  ambient := !![(1)*1,0,0;0,0,0;0,0,0]
  source := !![(1)*π,0;0,0]
  ambient_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  source_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  commutes := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring

include h in
def lift_5_9_0_0 : Data.objects5.Hom π 5 9 where
  ambient := !![(1)*1,0,0;0,0,0;0,0,0]
  source := !![(1)*π^3,0;0,0]
  ambient_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  source_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  commutes := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring

include h in
def lift_5_10_0_0 : Data.objects5.Hom π 5 10 where
  ambient := !![(1)*1,0,0;0,0,0;0,0,0]
  source := !![(1)*π^2,0;0,0]
  ambient_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  source_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  commutes := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring

include h in
def lift_5_11_0_0 : Data.objects5.Hom π 5 11 where
  ambient := !![(1)*1,0,0;0,0,0;0,0,0]
  source := !![(1)*π^2,0;0,0]
  ambient_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  source_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  commutes := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring

include h in
def lift_5_12_0_0 : Data.objects5.Hom π 5 12 where
  ambient := !![(1)*1,0,0;0,0,0;0,0,0]
  source := !![(1)*π,0;0,0]
  ambient_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  source_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  commutes := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring

include h in
def lift_5_13_0_0 : Data.objects5.Hom π 5 13 where
  ambient := !![(1)*1,0,0;0,0,0;0,0,0]
  source := !![(1)*π^3,0;0,0]
  ambient_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  source_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  commutes := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring

include h in
def lift_5_14_0_0 : Data.objects5.Hom π 5 14 where
  ambient := !![(1)*1,0,0;0,0,0;0,0,0]
  source := !![(1)*π^2,0;0,0]
  ambient_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  source_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  commutes := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring

include h in
def lift_5_15_0_0 : Data.objects5.Hom π 5 15 where
  ambient := !![(1)*1,0,0;0,0,0;0,0,0]
  source := !![(1)*π,0;0,0]
  ambient_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  source_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  commutes := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring

include h in
def lift_5_16_0_0 : Data.objects5.Hom π 5 16 where
  ambient := !![(1)*1,0,0;0,0,0;0,0,0]
  source := !![(1)*π^2,0;0,0]
  ambient_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  source_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  commutes := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring

include h in
def lift_5_17_0_0 : Data.objects5.Hom π 5 17 where
  ambient := !![(1)*1,0,0;0,0,0;0,0,0]
  source := !![0,(1)*π^3;0,0]
  ambient_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  source_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  commutes := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring

include h in
def lift_5_17_0_1 : Data.objects5.Hom π 5 17 where
  ambient := !![0,(1)*1,0;0,0,0;0,0,0]
  source := !![(1)*π,0;0,0]
  ambient_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  source_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  commutes := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^5=0 from by rw [show 5=5+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=5+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=5+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=5+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=5+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=5+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=5+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=5+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=5+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^14=0 from by rw [show 14=5+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^15=0 from by rw [show 15=5+10 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^16=0 from by rw [show 16=5+11 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring

end UniserialComputations.Uniform.Case5
