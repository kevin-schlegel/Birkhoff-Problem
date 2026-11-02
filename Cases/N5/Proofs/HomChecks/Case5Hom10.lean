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
def lift_10_0_0_0 : Data.objects5.Hom π 10 0 where
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
def lift_10_1_0_0 : Data.objects5.Hom π 10 1 where
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
theorem zero_10_2_0_0 (f : Data.objects5.Hom π 10 2) : ρ (f.ambient 0 0) = 0 := by
  apply (h.top_annihilator _).mp
  have e13 := f.commutes 0 0
  have e15 := f.commutes 1 0
  norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at e13 e15
  linear_combination ((1)*π)*e13 + ((-1)*1)*e15 + ((-1)*π*(f.ambient 0 1) + (-1)*π*(f.ambient 0 2) + (1)*π*(f.ambient 1 0) + (1)*π^3*(f.ambient 1 1) + (1)*π^3*(f.ambient 1 2) + (1)*π*(f.source 1 0) + (-1)*π^3*(f.source 1 0))*h.nilpotent

include h in
theorem zero_10_3_0_0 (f : Data.objects5.Hom π 10 3) : ρ (f.ambient 0 0) = 0 := by
  apply (h.top_annihilator _).mp
  have e13 := f.commutes 0 0
  have e15 := f.commutes 1 0
  norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at e13 e15
  linear_combination ((1)*π^2)*e13 + ((-1)*π)*e15 + ((-1)*π^2*(f.ambient 0 1) + (-1)*π^2*(f.ambient 0 2) + (1)*π*(f.ambient 1 0) + (1)*π^4*(f.ambient 1 1) + (1)*π^4*(f.ambient 1 2) + (1)*π^2*(f.source 1 0) + (-1)*π^4*(f.source 1 0))*h.nilpotent

include h in
theorem zero_10_4_0_0 (f : Data.objects5.Hom π 10 4) : ρ (f.ambient 0 0) = 0 := by
  apply (h.top_annihilator _).mp
  have e13 := f.commutes 0 0
  norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at e13
  linear_combination ((1)*π^3)*e13 + ((-1)*π^3*(f.ambient 0 1) + (-1)*π^3*(f.ambient 0 2) + (1)*1*(f.source 0 0) + (1)*π^3*(f.source 1 0))*h.nilpotent

include h in
theorem zero_10_5_0_0 (f : Data.objects5.Hom π 10 5) : ρ (f.ambient 0 0) = 0 := by
  apply (h.top_annihilator _).mp
  have e13 := f.commutes 0 0
  norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at e13
  linear_combination ((1)*π^4)*e13 + ((-1)*π^4*(f.ambient 0 1) + (-1)*π^4*(f.ambient 0 2) + (1)*π*(f.source 0 0) + (1)*π^4*(f.source 1 0))*h.nilpotent

include h in
def lift_10_6_0_0 : Data.objects5.Hom π 10 6 where
  ambient := !![(1)*1,0,0;0,(1)*π,0;0,0,0]
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
theorem zero_10_7_0_0 (f : Data.objects5.Hom π 10 7) : ρ (f.ambient 0 0) = 0 := by
  apply (h.top_annihilator _).mp
  have e13 := f.commutes 0 0
  have e1 := f.ambient_descent 0 1
  have e15 := f.commutes 1 0
  have e4 := f.ambient_descent 1 1
  norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at e13 e1 e15 e4
  linear_combination ((1)*π^2)*e13 + ((-1)*π)*e1 + ((-1)*π)*e15 + ((1)*1)*e4 + ((-1)*π^2*(f.ambient 0 2) + (1)*π*(f.ambient 1 0) + (1)*π^4*(f.ambient 1 2) + (1)*π^2*(f.source 1 0) + (-1)*π^4*(f.source 1 0))*h.nilpotent

include h in
theorem zero_10_8_0_0 (f : Data.objects5.Hom π 10 8) : ρ (f.ambient 0 0) = 0 := by
  apply (h.top_annihilator _).mp
  have e13 := f.commutes 0 0
  have e1 := f.ambient_descent 0 1
  norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at e13 e1
  linear_combination ((1)*π^3)*e13 + ((-1)*π^2)*e1 + ((-1)*π^3*(f.ambient 0 2) + (1)*1*(f.source 0 0) + (1)*π^3*(f.source 1 0))*h.nilpotent

include h in
def lift_10_9_0_0 : Data.objects5.Hom π 10 9 where
  ambient := !![(1)*1,0,0;0,(1)*1,0;0,0,0]
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
def lift_10_10_0_0 : Data.objects5.Hom π 10 10 where
  ambient := !![(1)*1,0,0;0,(1)*1,0;0,0,0]
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
theorem zero_10_11_0_0 (f : Data.objects5.Hom π 10 11) : ρ (f.ambient 0 0) = 0 := by
  apply (h.top_annihilator _).mp
  have e13 := f.commutes 0 0
  have e1 := f.ambient_descent 0 1
  have e15 := f.commutes 1 0
  norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at e13 e1 e15
  linear_combination ((1)*π^2)*e13 + ((-1)*π)*e1 + ((-1)*π)*e15 + ((-1)*π^2*(f.ambient 0 2) + (1)*π*(f.ambient 1 0) + (1)*1*(f.ambient 1 1) + (1)*π^4*(f.ambient 1 2) + (1)*π^2*(f.source 1 0) + (-1)*π^4*(f.source 1 0))*h.nilpotent

include h in
theorem zero_10_12_0_0 (f : Data.objects5.Hom π 10 12) : ρ (f.ambient 0 0) = 0 := by
  apply (h.top_annihilator _).mp
  have e13 := f.commutes 0 0
  have e1 := f.ambient_descent 0 1
  norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at e13 e1
  linear_combination ((1)*π^3)*e13 + ((-1)*π)*e1 + ((-1)*π^3*(f.ambient 0 2) + (1)*1*(f.source 0 0) + (1)*π^3*(f.source 1 0))*h.nilpotent

include h in
theorem zero_10_13_0_0 (f : Data.objects5.Hom π 10 13) : ρ (f.ambient 0 0) = 0 := by
  apply (h.top_annihilator _).mp
  have e13 := f.commutes 0 0
  have e1 := f.ambient_descent 0 1
  have e15 := f.commutes 1 0
  norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at e13 e1 e15
  linear_combination ((1)*π)*e13 + ((-1)*1)*e1 + ((-1)*1)*e15 + ((-1)*π*(f.ambient 0 2) + (1)*π*(f.ambient 1 0) + (1)*1*(f.ambient 1 1) + (1)*π^3*(f.ambient 1 2) + (1)*π*(f.source 1 0) + (-1)*π^3*(f.source 1 0))*h.nilpotent

include h in
theorem zero_10_14_0_0 (f : Data.objects5.Hom π 10 14) : ρ (f.ambient 0 0) = 0 := by
  apply (h.top_annihilator _).mp
  have e13 := f.commutes 0 0
  have e1 := f.ambient_descent 0 1
  have e15 := f.commutes 1 0
  norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at e13 e1 e15
  linear_combination ((1)*π^2)*e13 + ((-1)*1)*e1 + ((-1)*π)*e15 + ((-1)*π^2*(f.ambient 0 2) + (1)*π*(f.ambient 1 0) + (1)*1*(f.ambient 1 1) + (1)*π^4*(f.ambient 1 2) + (1)*π^2*(f.source 1 0) + (-1)*π^4*(f.source 1 0))*h.nilpotent

include h in
theorem zero_10_15_0_0 (f : Data.objects5.Hom π 10 15) : ρ (f.ambient 0 0) = 0 := by
  apply (h.top_annihilator _).mp
  have e13 := f.commutes 0 0
  have e1 := f.ambient_descent 0 1
  norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at e13 e1
  linear_combination ((1)*π^3)*e13 + ((-1)*1)*e1 + ((-1)*π^3*(f.ambient 0 2) + (1)*1*(f.source 0 0) + (1)*π^3*(f.source 1 0))*h.nilpotent

include h in
theorem zero_10_16_0_0 (f : Data.objects5.Hom π 10 16) : ρ (f.ambient 0 0) = 0 := by
  apply (h.top_annihilator _).mp
  have e13 := f.commutes 0 0
  have e1 := f.ambient_descent 0 1
  have e2 := f.ambient_descent 0 2
  have e15 := f.commutes 1 0
  have e5 := f.ambient_descent 1 2
  norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at e13 e1 e2 e15 e5
  linear_combination ((1)*π^2)*e13 + ((-1)*1)*e1 + ((-1)*π)*e2 + ((-1)*π)*e15 + ((1)*1)*e5 + ((1)*π*(f.ambient 1 0) + (1)*1*(f.ambient 1 1) + (1)*π^2*(f.source 1 0) + (-1)*π^4*(f.source 1 0))*h.nilpotent

include h in
theorem zero_10_17_0_1 (f : Data.objects5.Hom π 10 17) : ρ (f.ambient 0 1) = 0 := by
  apply (h.top_annihilator _).mp
  have e13 := f.commutes 0 0
  have e2 := f.ambient_descent 0 2
  norm_num [Data.objects5, ObjectFamily.embedding, Matrix.mul_apply, Fin.sum_univ_succ] at e13 e2
  linear_combination ((1)*π^3)*e13 + ((-1)*π)*e2 + ((-1)*π^3*(f.ambient 0 0) + (1)*1*(f.source 0 0) + (1)*π^3*(f.source 1 0))*h.nilpotent

include h in
def lift_10_17_0_0 : Data.objects5.Hom π 10 17 where
  ambient := !![(1)*1,(1)*π,0;0,0,(1)*1;0,0,0]
  source := !![(1)*1,(1)*π;0,0]
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
