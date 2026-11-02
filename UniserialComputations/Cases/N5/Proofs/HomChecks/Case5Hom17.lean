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
def lift_17_0_0_0 : Data.objects5.Hom π 17 0 where
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
def lift_17_0_1_0 : Data.objects5.Hom π 17 0 where
  ambient := !![0,0,0;(1)*1,0,0;0,0,0]
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
def lift_17_1_0_0 : Data.objects5.Hom π 17 1 where
  ambient := !![(1)*1,0,0;0,0,0;0,0,0]
  source := !![0,0;(1)*π,0]
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
def lift_17_1_1_0 : Data.objects5.Hom π 17 1 where
  ambient := !![0,0,0;(1)*1,0,0;0,0,0]
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
theorem zero_17_2_0_0 (f : Data.objects5.Hom π 17 2) : ρ (f.ambient 0 0) = 0 := by
  apply (h.top_annihilator _).mp
  have e13 := f.commutes 0 0
  have e17 := f.commutes 2 0
  have e9 := f.source_descent 0 0
  norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at e13 e17 e9
  linear_combination ((1)*π)*e13 + ((-1)*1)*e17 + ((-1)*1)*e9 + ((-1)*π*(f.ambient 0 1) + (-1)*π*(f.ambient 0 2) + (1)*π*(f.ambient 2 0) + (1)*π^3*(f.ambient 2 1) + (1)*π^3*(f.ambient 2 2) + (1)*π*(f.source 0 0))*h.nilpotent

include h in
def lift_17_2_1_0 : Data.objects5.Hom π 17 2 where
  ambient := !![0,0,0;(1)*1,0,0;0,0,0]
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
theorem zero_17_3_0_0 (f : Data.objects5.Hom π 17 3) : ρ (f.ambient 0 0) = 0 := by
  apply (h.top_annihilator _).mp
  have e13 := f.commutes 0 0
  norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at e13
  linear_combination ((1)*π^2)*e13 + ((-1)*π^2*(f.ambient 0 1) + (-1)*π^2*(f.ambient 0 2) + (1)*π^2*(f.source 0 0) + (1)*1*(f.source 1 0))*h.nilpotent

include h in
def lift_17_3_1_0 : Data.objects5.Hom π 17 3 where
  ambient := !![(-1)*π,0,0;(1)*1,0,0;0,0,0]
  source := !![(1)*π,0;(-1)*1,0]
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
theorem zero_17_4_0_0 (f : Data.objects5.Hom π 17 4) : ρ (f.ambient 0 0) = 0 := by
  apply (h.top_annihilator _).mp
  have e13 := f.commutes 0 0
  norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at e13
  linear_combination ((1)*π^3)*e13 + ((-1)*π^3*(f.ambient 0 1) + (-1)*π^3*(f.ambient 0 2) + (1)*π^3*(f.source 0 0) + (1)*π*(f.source 1 0))*h.nilpotent

include h in
theorem zero_17_4_1_0 (f : Data.objects5.Hom π 17 4) : ρ (f.ambient 1 0) = 0 := by
  apply (h.top_annihilator _).mp
  have e15 := f.commutes 1 0
  have e17 := f.commutes 2 0
  norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at e15 e17
  linear_combination ((1)*π^3)*e15 + ((-1)*π)*e17 + ((-1)*π^3*(f.ambient 1 1) + (-1)*π^3*(f.ambient 1 2) + (1)*1*(f.ambient 2 0) + (1)*π^4*(f.ambient 2 1) + (1)*π^4*(f.ambient 2 2) + (-1)*1*(f.source 1 0) + (1)*π^3*(f.source 1 0))*h.nilpotent

include h in
theorem zero_17_5_0_0 (f : Data.objects5.Hom π 17 5) : ρ (f.ambient 0 0) = 0 := by
  apply (h.top_annihilator _).mp
  have e13 := f.commutes 0 0
  norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at e13
  linear_combination ((1)*π^4)*e13 + ((-1)*π^4*(f.ambient 0 1) + (-1)*π^4*(f.ambient 0 2) + (1)*π^4*(f.source 0 0) + (1)*π^2*(f.source 1 0))*h.nilpotent

include h in
theorem zero_17_5_1_0 (f : Data.objects5.Hom π 17 5) : ρ (f.ambient 1 0) = 0 := by
  apply (h.top_annihilator _).mp
  have e15 := f.commutes 1 0
  norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at e15
  linear_combination ((1)*π^4)*e15 + ((-1)*π^4*(f.ambient 1 1) + (-1)*π^4*(f.ambient 1 2) + (1)*1*(f.source 0 0) + (1)*π^4*(f.source 1 0))*h.nilpotent

include h in
def lift_17_6_0_0 : Data.objects5.Hom π 17 6 where
  ambient := !![(1)*1,0,0;0,0,0;0,(1)*π,0]
  source := !![0,0;(1)*1,0]
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
def lift_17_6_1_0 : Data.objects5.Hom π 17 6 where
  ambient := !![0,0,0;(1)*1,0,0;0,0,0]
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
theorem zero_17_7_0_0 (f : Data.objects5.Hom π 17 7) : ρ (f.ambient 0 0) = 0 := by
  apply (h.top_annihilator _).mp
  have e13 := f.commutes 0 0
  have e1 := f.ambient_descent 0 1
  norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at e13 e1
  linear_combination ((1)*π^2)*e13 + ((-1)*π)*e1 + ((-1)*π^2*(f.ambient 0 2) + (1)*π^2*(f.source 0 0) + (1)*1*(f.source 1 0))*h.nilpotent

include h in
def lift_17_7_1_0 : Data.objects5.Hom π 17 7 where
  ambient := !![0,0,0;(1)*1,0,0;0,(1)*π,0]
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
theorem zero_17_8_0_0 (f : Data.objects5.Hom π 17 8) : ρ (f.ambient 0 0) = 0 := by
  apply (h.top_annihilator _).mp
  have e13 := f.commutes 0 0
  have e1 := f.ambient_descent 0 1
  norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at e13 e1
  linear_combination ((1)*π^3)*e13 + ((-1)*π^2)*e1 + ((-1)*π^3*(f.ambient 0 2) + (1)*π^3*(f.source 0 0) + (1)*π*(f.source 1 0))*h.nilpotent

include h in
theorem zero_17_8_1_0 (f : Data.objects5.Hom π 17 8) : ρ (f.ambient 1 0) = 0 := by
  apply (h.top_annihilator _).mp
  have e15 := f.commutes 1 0
  have e4 := f.ambient_descent 1 1
  have e17 := f.commutes 2 0
  have e7 := f.ambient_descent 2 1
  norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at e15 e4 e17 e7
  linear_combination ((1)*π^3)*e15 + ((-1)*π^2)*e4 + ((-1)*π)*e17 + ((1)*1)*e7 + ((-1)*π^3*(f.ambient 1 2) + (1)*1*(f.ambient 2 0) + (1)*π^4*(f.ambient 2 2) + (-1)*1*(f.source 1 0) + (1)*π^3*(f.source 1 0))*h.nilpotent

include h in
def lift_17_9_0_0 : Data.objects5.Hom π 17 9 where
  ambient := !![(1)*1,0,0;0,0,0;0,(1)*1,0]
  source := !![0,0;(1)*1,0]
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
def lift_17_9_1_0 : Data.objects5.Hom π 17 9 where
  ambient := !![0,0,0;(1)*1,0,0;0,0,0]
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
theorem zero_17_10_0_0 (f : Data.objects5.Hom π 17 10) : ρ (f.ambient 0 0) = 0 := by
  apply (h.top_annihilator _).mp
  have e13 := f.commutes 0 0
  have e1 := f.ambient_descent 0 1
  norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at e13 e1
  linear_combination ((1)*π^2)*e13 + ((-1)*1)*e1 + ((-1)*π^2*(f.ambient 0 2) + (1)*π^2*(f.source 0 0) + (1)*1*(f.source 1 0))*h.nilpotent

include h in
def lift_17_10_1_0 : Data.objects5.Hom π 17 10 where
  ambient := !![0,0,0;(1)*1,0,0;0,(1)*π,0]
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
theorem zero_17_11_0_0 (f : Data.objects5.Hom π 17 11) : ρ (f.ambient 0 0) = 0 := by
  apply (h.top_annihilator _).mp
  have e13 := f.commutes 0 0
  have e1 := f.ambient_descent 0 1
  norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at e13 e1
  linear_combination ((1)*π^2)*e13 + ((-1)*π)*e1 + ((-1)*π^2*(f.ambient 0 2) + (1)*π^2*(f.source 0 0) + (1)*1*(f.source 1 0))*h.nilpotent

include h in
def lift_17_11_1_0 : Data.objects5.Hom π 17 11 where
  ambient := !![0,0,0;(1)*1,0,0;0,(1)*1,0]
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
theorem zero_17_12_0_0 (f : Data.objects5.Hom π 17 12) : ρ (f.ambient 0 0) = 0 := by
  apply (h.top_annihilator _).mp
  have e13 := f.commutes 0 0
  have e1 := f.ambient_descent 0 1
  norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at e13 e1
  linear_combination ((1)*π^3)*e13 + ((-1)*π)*e1 + ((-1)*π^3*(f.ambient 0 2) + (1)*π^3*(f.source 0 0) + (1)*π*(f.source 1 0))*h.nilpotent

include h in
def lift_17_12_1_0 : Data.objects5.Hom π 17 12 where
  ambient := !![0,0,0;(1)*1,0,0;0,(1)*1,0]
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
theorem zero_17_13_0_0 (f : Data.objects5.Hom π 17 13) : ρ (f.ambient 0 0) = 0 := by
  apply (h.top_annihilator _).mp
  have e13 := f.commutes 0 0
  have e1 := f.ambient_descent 0 1
  have e17 := f.commutes 2 0
  have e9 := f.source_descent 0 0
  norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at e13 e1 e17 e9
  linear_combination ((1)*π)*e13 + ((-1)*1)*e1 + ((-1)*1)*e17 + ((-1)*1)*e9 + ((-1)*π*(f.ambient 0 2) + (1)*π*(f.ambient 2 0) + (1)*1*(f.ambient 2 1) + (1)*π^3*(f.ambient 2 2) + (1)*π*(f.source 0 0))*h.nilpotent

include h in
def lift_17_13_1_0 : Data.objects5.Hom π 17 13 where
  ambient := !![0,0,0;(1)*1,0,0;0,0,0]
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
theorem zero_17_14_0_0 (f : Data.objects5.Hom π 17 14) : ρ (f.ambient 0 0) = 0 := by
  apply (h.top_annihilator _).mp
  have e13 := f.commutes 0 0
  have e1 := f.ambient_descent 0 1
  norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at e13 e1
  linear_combination ((1)*π^2)*e13 + ((-1)*1)*e1 + ((-1)*π^2*(f.ambient 0 2) + (1)*π^2*(f.source 0 0) + (1)*1*(f.source 1 0))*h.nilpotent

include h in
def lift_17_14_1_0 : Data.objects5.Hom π 17 14 where
  ambient := !![0,0,0;(1)*1,0,0;0,(1)*1,0]
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
theorem zero_17_15_0_0 (f : Data.objects5.Hom π 17 15) : ρ (f.ambient 0 0) = 0 := by
  apply (h.top_annihilator _).mp
  have e13 := f.commutes 0 0
  have e1 := f.ambient_descent 0 1
  norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at e13 e1
  linear_combination ((1)*π^3)*e13 + ((-1)*1)*e1 + ((-1)*π^3*(f.ambient 0 2) + (1)*π^3*(f.source 0 0) + (1)*π*(f.source 1 0))*h.nilpotent

include h in
def lift_17_15_1_0 : Data.objects5.Hom π 17 15 where
  ambient := !![0,0,0;(1)*1,0,0;0,(1)*1,0]
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
theorem zero_17_16_0_0 (f : Data.objects5.Hom π 17 16) : ρ (f.ambient 0 0) = 0 := by
  apply (h.top_annihilator _).mp
  have e13 := f.commutes 0 0
  have e1 := f.ambient_descent 0 1
  have e2 := f.ambient_descent 0 2
  norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at e13 e1 e2
  linear_combination ((1)*π^2)*e13 + ((-1)*1)*e1 + ((-1)*π)*e2 + ((1)*π^2*(f.source 0 0) + (1)*1*(f.source 1 0))*h.nilpotent

include h in
def lift_17_16_1_0 : Data.objects5.Hom π 17 16 where
  ambient := !![0,0,0;(1)*1,0,0;0,(1)*1,0]
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
theorem zero_17_17_0_1 (f : Data.objects5.Hom π 17 17) : ρ (f.ambient 0 1) = 0 := by
  apply (h.top_annihilator _).mp
  have e13 := f.commutes 0 0
  have e2 := f.ambient_descent 0 2
  norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at e13 e2
  linear_combination ((1)*π^3)*e13 + ((-1)*π)*e2 + ((-1)*π^3*(f.ambient 0 0) + (1)*π^3*(f.source 0 0) + (1)*π*(f.source 1 0))*h.nilpotent

include h in
theorem diagonal_17 (f : Data.objects5.Hom π 17 17) : ρ (f.ambient 0 0) = ρ (f.ambient 1 1) := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (h.top_annihilator _).mp
  have e14 := f.commutes 0 1
  have e2 := f.ambient_descent 0 2
  have e15 := f.commutes 1 0
  have e5 := f.ambient_descent 1 2
  have e18 := f.commutes 2 1
  have e17 := f.commutes 2 0
  have e10 := f.source_descent 0 1
  norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at e14 e2 e15 e5 e18 e17 e10
  linear_combination ((1)*π)*e14 + ((-1)*1)*e2 + ((-1)*π^3)*e15 + ((1)*π)*e5 + ((-1)*1)*e18 + ((1)*π)*e17 + ((-1)*1)*e10 + ((-1)*π*(f.ambient 0 1) + (1)*π^3*(f.ambient 1 0) + (1)*π*(f.ambient 2 0) + (-1)*π^4*(f.ambient 2 0) + (-1)*1*(f.ambient 2 1) + (1)*π^3*(f.ambient 2 1) + (1)*π*(f.source 0 1) + (1)*1*(f.source 1 0) + (-1)*π^3*(f.source 1 0))*h.nilpotent

include h in
def lift_17_17_0_0 : Data.objects5.Hom π 17 17 where
  ambient := !![(1)*1,0,0;0,(1)*1,0;0,0,(1)*1]
  source := !![(1)*1,0;0,(1)*1]
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
def lift_17_17_1_0 : Data.objects5.Hom π 17 17 where
  ambient := !![0,0,0;(1)*1,0,0;0,0,0]
  source := !![0,(1)*π^2;0,0]
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
