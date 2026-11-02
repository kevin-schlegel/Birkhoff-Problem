import Case4Data

noncomputable section
namespace UniserialComputations.Uniform.Case4
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
variable {R k : Type*} [CommRing R] [Field k] (π : R) (ρ : R →+* k)
variable (h : RingParameters 4 R k π ρ)

include h in
def lift_0_0_0_0 : Data.objects4.Hom π 0 0 where
  ambient := !![(1)*1,0;0,0]
  source := !![(1)*1]
  ambient_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects4, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^4=0 from by rw [show 4=4+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^5=0 from by rw [show 5=4+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=4+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=4+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=4+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=4+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=4+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=4+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=4+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=4+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  source_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects4, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^4=0 from by rw [show 4=4+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^5=0 from by rw [show 5=4+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=4+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=4+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=4+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=4+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=4+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=4+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=4+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=4+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  commutes := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects4, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^4=0 from by rw [show 4=4+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^5=0 from by rw [show 5=4+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=4+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=4+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=4+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=4+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=4+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=4+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=4+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=4+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring

include h in
def lift_0_1_0_0 : Data.objects4.Hom π 0 1 where
  ambient := !![(1)*1,0;0,0]
  source := !![(1)*π]
  ambient_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects4, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^4=0 from by rw [show 4=4+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^5=0 from by rw [show 5=4+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=4+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=4+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=4+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=4+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=4+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=4+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=4+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=4+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  source_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects4, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^4=0 from by rw [show 4=4+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^5=0 from by rw [show 5=4+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=4+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=4+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=4+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=4+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=4+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=4+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=4+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=4+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  commutes := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects4, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^4=0 from by rw [show 4=4+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^5=0 from by rw [show 5=4+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=4+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=4+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=4+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=4+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=4+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=4+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=4+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=4+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring

include h in
def lift_0_2_0_0 : Data.objects4.Hom π 0 2 where
  ambient := !![(1)*1,0;0,0]
  source := !![(1)*π]
  ambient_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects4, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^4=0 from by rw [show 4=4+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^5=0 from by rw [show 5=4+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=4+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=4+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=4+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=4+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=4+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=4+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=4+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=4+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  source_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects4, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^4=0 from by rw [show 4=4+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^5=0 from by rw [show 5=4+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=4+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=4+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=4+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=4+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=4+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=4+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=4+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=4+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  commutes := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects4, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^4=0 from by rw [show 4=4+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^5=0 from by rw [show 5=4+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=4+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=4+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=4+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=4+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=4+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=4+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=4+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=4+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring

include h in
def lift_0_3_0_0 : Data.objects4.Hom π 0 3 where
  ambient := !![(1)*1,0;0,0]
  source := !![(1)*π^2]
  ambient_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects4, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^4=0 from by rw [show 4=4+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^5=0 from by rw [show 5=4+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=4+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=4+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=4+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=4+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=4+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=4+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=4+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=4+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  source_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects4, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^4=0 from by rw [show 4=4+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^5=0 from by rw [show 5=4+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=4+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=4+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=4+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=4+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=4+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=4+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=4+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=4+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  commutes := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects4, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^4=0 from by rw [show 4=4+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^5=0 from by rw [show 5=4+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=4+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=4+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=4+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=4+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=4+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=4+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=4+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=4+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring

include h in
def lift_0_4_0_0 : Data.objects4.Hom π 0 4 where
  ambient := !![(1)*1,0;0,0]
  source := !![(1)*π]
  ambient_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects4, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^4=0 from by rw [show 4=4+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^5=0 from by rw [show 5=4+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=4+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=4+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=4+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=4+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=4+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=4+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=4+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=4+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  source_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects4, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^4=0 from by rw [show 4=4+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^5=0 from by rw [show 5=4+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=4+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=4+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=4+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=4+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=4+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=4+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=4+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=4+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  commutes := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects4, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^4=0 from by rw [show 4=4+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^5=0 from by rw [show 5=4+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=4+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=4+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=4+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=4+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=4+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=4+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=4+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=4+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring

include h in
def lift_0_5_0_0 : Data.objects4.Hom π 0 5 where
  ambient := !![(1)*1,0;0,0]
  source := !![(1)*π^2]
  ambient_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects4, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^4=0 from by rw [show 4=4+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^5=0 from by rw [show 5=4+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=4+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=4+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=4+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=4+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=4+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=4+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=4+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=4+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  source_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects4, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^4=0 from by rw [show 4=4+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^5=0 from by rw [show 5=4+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=4+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=4+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=4+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=4+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=4+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=4+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=4+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=4+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  commutes := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects4, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^4=0 from by rw [show 4=4+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^5=0 from by rw [show 5=4+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=4+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=4+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=4+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=4+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=4+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=4+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=4+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=4+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring

include h in
def lift_0_6_0_0 : Data.objects4.Hom π 0 6 where
  ambient := !![(1)*1,0;0,0]
  source := !![(1)*π^2]
  ambient_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects4, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^4=0 from by rw [show 4=4+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^5=0 from by rw [show 5=4+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=4+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=4+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=4+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=4+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=4+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=4+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=4+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=4+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  source_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects4, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^4=0 from by rw [show 4=4+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^5=0 from by rw [show 5=4+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=4+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=4+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=4+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=4+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=4+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=4+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=4+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=4+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  commutes := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects4, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^4=0 from by rw [show 4=4+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^5=0 from by rw [show 5=4+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=4+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=4+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=4+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=4+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=4+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=4+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=4+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=4+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring

include h in
def lift_0_7_0_0 : Data.objects4.Hom π 0 7 where
  ambient := !![(1)*1,0;0,0]
  source := !![(1)*π^3]
  ambient_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects4, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^4=0 from by rw [show 4=4+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^5=0 from by rw [show 5=4+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=4+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=4+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=4+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=4+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=4+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=4+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=4+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=4+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  source_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects4, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^4=0 from by rw [show 4=4+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^5=0 from by rw [show 5=4+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=4+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=4+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=4+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=4+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=4+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=4+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=4+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=4+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  commutes := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects4, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^4=0 from by rw [show 4=4+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^5=0 from by rw [show 5=4+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=4+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=4+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=4+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=4+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=4+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=4+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=4+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=4+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring

include h in
def lift_0_8_0_0 : Data.objects4.Hom π 0 8 where
  ambient := !![(1)*1,0;0,0]
  source := !![0]
  ambient_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects4, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^4=0 from by rw [show 4=4+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^5=0 from by rw [show 5=4+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=4+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=4+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=4+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=4+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=4+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=4+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=4+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=4+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  source_descent := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects4, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^4=0 from by rw [show 4=4+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^5=0 from by rw [show 5=4+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=4+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=4+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=4+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=4+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=4+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=4+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=4+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=4+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring
  commutes := by
    intro r c
    fin_cases r <;> fin_cases c
    all_goals norm_num [Data.objects4, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals try ring_nf
    all_goals try rw [show π^4=0 from by rw [show 4=4+0 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^5=0 from by rw [show 5=4+1 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^6=0 from by rw [show 6=4+2 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^7=0 from by rw [show 7=4+3 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^8=0 from by rw [show 8=4+4 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^9=0 from by rw [show 9=4+5 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^10=0 from by rw [show 10=4+6 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^11=0 from by rw [show 11=4+7 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^12=0 from by rw [show 12=4+8 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals try rw [show π^13=0 from by rw [show 13=4+9 by decide, pow_add, h.nilpotent, zero_mul]]
    all_goals ring

end UniserialComputations.Uniform.Case4
