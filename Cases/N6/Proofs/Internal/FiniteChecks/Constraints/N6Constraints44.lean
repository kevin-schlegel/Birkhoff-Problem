import N6Matrix
noncomputable section
namespace UniserialComputations.N6
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
variable {R k : Type*} [CommRing R] [Field k] (π : R) (ρ : R →+* k)
variable (h6 : π^6=0) (ann : ∀ r, π^5*r=0 ↔ ρ r=0)
include h6 ann in
theorem constraint_44_0_0_0 (f : HomData π 44 0) : ρ ((f.M 2 0))=0 := by
  apply (ann _).mp
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h24
  norm_num at h24
  linear_combination (π^4)*h24 + (π^2*(f.U 0 0))*h6
include h6 ann in
theorem constraint_44_0_1_0 (f : HomData π 44 0) : ρ ((f.M 3 0))=0 := by
  apply (ann _).mp
  have h26 := f.commutes 3 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h26
  norm_num at h26
  linear_combination (π^4)*h26 + ((f.U 1 0))*h6
include h6 ann in
theorem constraint_44_1_0_0 (f : HomData π 44 1) : ρ ((f.M 2 0))=0 := by
  apply (ann _).mp
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h24
  norm_num at h24
  linear_combination (π^3)*h24 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_44_1_1_0 (f : HomData π 44 1) : ρ ((f.M 3 0))=0 := by
  apply (ann _).mp
  have h20 := f.commutes 0 0
  have h26 := f.commutes 3 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h20 h26
  norm_num at h20 h26
  linear_combination (π^2)*h20 + (π^3)*h26 + ((-1)*(f.M 0 0))*h6
include h6 ann in
theorem constraint_44_2_0_0 (f : HomData π 44 2) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (π^3)*h8 + (π^4)*h24 + (π^2*(f.U 0 0))*h6
include h6 ann in
theorem constraint_44_2_1_0 (f : HomData π 44 2) : ρ ((f.M 3 1))=0 := by
  apply (ann _).mp
  have h12 := f.ambient_descent 3 0
  have h26 := f.commutes 3 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h12 h26
  norm_num at h12 h26
  linear_combination (π^3)*h12 + (π^4)*h26 + ((f.U 1 0))*h6
include h6 ann in
theorem constraint_44_3_0_0 (f : HomData π 44 3) : ρ ((f.M 2 0))=0 := by
  apply (ann _).mp
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h24
  norm_num at h24
  linear_combination (π^2)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_44_3_1_0 (f : HomData π 44 3) : ρ ((f.M 3 0))=0 := by
  apply (ann _).mp
  have h20 := f.commutes 0 0
  have h26 := f.commutes 3 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h20 h26
  norm_num at h20 h26
  linear_combination (π)*h20 + (π^2)*h26 + ((-1)*(f.M 0 0))*h6
include h6 ann in
theorem constraint_44_4_0_0 (f : HomData π 44 4) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (π^2)*h8 + (π^3)*h24 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_44_4_1_0 (f : HomData π 44 4) : ρ ((f.M 3 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h12 := f.ambient_descent 3 0
  have h20 := f.commutes 0 0
  have h26 := f.commutes 3 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h12 h20 h26
  norm_num at h0 h12 h20 h26
  linear_combination (π)*h0 + (π^2)*h12 + (π^2)*h20 + (π^3)*h26 + ((-1)*(f.M 0 1))*h6
include h6 ann in
theorem constraint_44_5_0_0 (f : HomData π 44 5) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (π^2)*h8 + (π^4)*h24 + (π^2*(f.U 0 0))*h6
include h6 ann in
theorem constraint_44_5_1_0 (f : HomData π 44 5) : ρ ((f.M 3 1))=0 := by
  apply (ann _).mp
  have h12 := f.ambient_descent 3 0
  have h26 := f.commutes 3 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h12 h26
  norm_num at h12 h26
  linear_combination (π^2)*h12 + (π^4)*h26 + ((f.U 1 0))*h6
include h6 ann in
theorem constraint_44_6_0_0 (f : HomData π 44 6) : ρ ((f.M 2 0))=0 := by
  apply (ann _).mp
  have h18 := f.source_descent 1 0
  have h22 := f.commutes 1 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h18 h22 h24
  norm_num at h18 h22 h24
  linear_combination (1)*h18 + (1)*h22 + (π)*h24 + ((-1)*π^2*(f.M 1 0))*h6
include h6 ann in
theorem constraint_44_6_1_0 (f : HomData π 44 6) : ρ ((f.M 3 0))=0 := by
  apply (ann _).mp
  have h20 := f.commutes 0 0
  have h26 := f.commutes 3 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h20 h26
  norm_num at h20 h26
  linear_combination (1)*h20 + (π)*h26 + ((-1)*(f.M 0 0))*h6
include h6 ann in
theorem constraint_44_7_0_0 (f : HomData π 44 7) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (π)*h8 + (π^2)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_44_7_1_0 (f : HomData π 44 7) : ρ ((f.M 3 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h12 := f.ambient_descent 3 0
  have h20 := f.commutes 0 0
  have h26 := f.commutes 3 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h12 h20 h26
  norm_num at h0 h12 h20 h26
  linear_combination (1)*h0 + (π)*h12 + (π)*h20 + (π^2)*h26 + ((-1)*(f.M 0 1))*h6
include h6 ann in
theorem constraint_44_8_0_0 (f : HomData π 44 8) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (π)*h8 + (π^3)*h24 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_44_8_1_0 (f : HomData π 44 8) : ρ ((f.M 3 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h12 := f.ambient_descent 3 0
  have h20 := f.commutes 0 0
  have h26 := f.commutes 3 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h12 h20 h26
  norm_num at h0 h12 h20 h26
  linear_combination (1)*h0 + (π)*h12 + (π^2)*h20 + (π^3)*h26 + ((-1)*(f.M 0 1))*h6
include h6 ann in
theorem constraint_44_9_0_0 (f : HomData π 44 9) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (π)*h8 + (π^4)*h24 + (π^2*(f.U 0 0))*h6
include h6 ann in
theorem constraint_44_9_1_0 (f : HomData π 44 9) : ρ ((f.M 3 1))=0 := by
  apply (ann _).mp
  have h12 := f.ambient_descent 3 0
  have h26 := f.commutes 3 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h12 h26
  norm_num at h12 h26
  linear_combination (π)*h12 + (π^4)*h26 + ((f.U 1 0))*h6
include h6 ann in
theorem constraint_44_12_0_0 (f : HomData π 44 12) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (1)*h8 + (π^2)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_44_13_0_0 (f : HomData π 44 13) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (1)*h8 + (π^3)*h24 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_44_14_0_0 (f : HomData π 44 14) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (1)*h8 + (π^4)*h24 + (π^2*(f.U 0 0))*h6
include h6 ann in
theorem constraint_44_14_1_0 (f : HomData π 44 14) : ρ ((f.M 3 1))=0 := by
  apply (ann _).mp
  have h12 := f.ambient_descent 3 0
  have h26 := f.commutes 3 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h12 h26
  norm_num at h12 h26
  linear_combination (1)*h12 + (π^4)*h26 + ((f.U 1 0))*h6
include h6 ann in
theorem constraint_44_15_0_0 (f : HomData π 44 15) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (π^2)*h8 + (π^3)*h24 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_44_15_1_0 (f : HomData π 44 15) : ρ ((f.M 3 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h12 := f.ambient_descent 3 0
  have h20 := f.commutes 0 0
  have h26 := f.commutes 3 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h12 h20 h26
  norm_num at h0 h12 h20 h26
  linear_combination (π)*h0 + (π^2)*h12 + (π^2)*h20 + (π^3)*h26 + ((-1)*(f.M 0 1))*h6
include h6 ann in
theorem constraint_44_16_0_0 (f : HomData π 44 16) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (π)*h8 + (π^2)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_44_16_1_0 (f : HomData π 44 16) : ρ ((f.M 3 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h12 := f.ambient_descent 3 0
  have h20 := f.commutes 0 0
  have h26 := f.commutes 3 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h12 h20 h26
  norm_num at h0 h12 h20 h26
  linear_combination (1)*h0 + (π)*h12 + (π)*h20 + (π^2)*h26 + ((-1)*(f.M 0 1))*h6
include h6 ann in
theorem constraint_44_17_0_0 (f : HomData π 44 17) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (π)*h8 + (π^3)*h24 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_44_17_1_0 (f : HomData π 44 17) : ρ ((f.M 3 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h12 := f.ambient_descent 3 0
  have h20 := f.commutes 0 0
  have h26 := f.commutes 3 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h12 h20 h26
  norm_num at h0 h12 h20 h26
  linear_combination (1)*h0 + (π)*h12 + (π^2)*h20 + (π^3)*h26 + ((-1)*(f.M 0 1))*h6
include h6 ann in
theorem constraint_44_18_0_0 (f : HomData π 44 18) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (π)*h8 + (π^2)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_44_18_0_1 (f : HomData π 44 18) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π^2)*h8 + (π^4)*h25 + (π^2*(f.U 0 1))*h6
include h6 ann in
theorem constraint_44_18_1_0 (f : HomData π 44 18) : ρ ((f.M 3 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h12 := f.ambient_descent 3 0
  have h20 := f.commutes 0 0
  have h26 := f.commutes 3 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h12 h20 h26
  norm_num at h0 h12 h20 h26
  linear_combination (1)*h0 + (π)*h12 + (π)*h20 + (π^2)*h26 + ((-1)*(f.M 0 1))*h6
include h6 ann in
theorem constraint_44_18_1_1 (f : HomData π 44 18) : ρ ((f.M 3 2))=0 := by
  apply (ann _).mp
  have h12 := f.ambient_descent 3 0
  have h27 := f.commutes 3 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h12 h27
  norm_num at h12 h27
  linear_combination (π^2)*h12 + (π^4)*h27 + ((f.U 1 1))*h6
include h6 ann in
theorem constraint_44_19_0_0 (f : HomData π 44 19) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (π)*h8 + (π^2)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_44_19_1_0 (f : HomData π 44 19) : ρ ((f.M 3 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h12 := f.ambient_descent 3 0
  have h20 := f.commutes 0 0
  have h26 := f.commutes 3 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h12 h20 h26
  norm_num at h0 h12 h20 h26
  linear_combination (1)*h0 + (π)*h12 + (π)*h20 + (π^2)*h26 + ((-1)*(f.M 0 1))*h6
include h6 ann in
theorem constraint_44_20_0_0 (f : HomData π 44 20) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h9 h24
  norm_num at h8 h9 h24
  linear_combination (π)*h8 + ((-1)*π^2)*h9 + (π^3)*h24 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_44_20_1_0 (f : HomData π 44 20) : ρ ((f.M 3 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h12 := f.ambient_descent 3 0
  have h13 := f.ambient_descent 3 1
  have h20 := f.commutes 0 0
  have h26 := f.commutes 3 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h12 h13 h20 h26
  norm_num at h0 h1 h12 h13 h20 h26
  linear_combination (1)*h0 + ((-1)*π)*h1 + (π)*h12 + ((-1)*π^2)*h13 + (π^2)*h20 + (π^3)*h26 + ((-1)*(f.M 0 2))*h6
include h6 ann in
theorem constraint_44_22_0_0 (f : HomData π 44 22) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (1)*h8 + (π^2)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_44_23_0_0 (f : HomData π 44 23) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (1)*h8 + (π^3)*h24 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_44_23_1_0 (f : HomData π 44 23) : ρ ((f.M 3 1))=0 := by
  apply (ann _).mp
  have h12 := f.ambient_descent 3 0
  have h22 := f.commutes 1 0
  have h26 := f.commutes 3 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h12 h22 h26
  norm_num at h12 h22 h26
  linear_combination (1)*h12 + ((-1)*π)*h22 + (π^3)*h26 + ((-1)*(f.M 1 0) + π*(f.M 1 1) + (f.U 0 0))*h6
include h6 ann in
theorem constraint_44_24_0_1 (f : HomData π 44 24) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π^2)*h8 + (π^4)*h25 + (π^2*(f.U 0 1))*h6
include h6 ann in
theorem constraint_44_24_1_1 (f : HomData π 44 24) : ρ ((f.M 3 2))=0 := by
  apply (ann _).mp
  have h12 := f.ambient_descent 3 0
  have h27 := f.commutes 3 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h12 h27
  norm_num at h12 h27
  linear_combination (π^2)*h12 + (π^4)*h27 + ((f.U 1 1))*h6
include h6 ann in
theorem constraint_44_25_0_0 (f : HomData π 44 25) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h18 := f.source_descent 1 0
  have h22 := f.commutes 1 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h18 h22 h24
  norm_num at h8 h18 h22 h24
  linear_combination (1)*h8 + (1)*h18 + (1)*h22 + (π)*h24 + ((f.M 1 0) + (-1)*π^2*(f.M 1 1))*h6
include h6 ann in
theorem constraint_44_26_0_0 (f : HomData π 44 26) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (1)*h8 + (π^2)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_44_26_0_1 (f : HomData π 44 26) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π)*h8 + (π^4)*h25 + (π^2*(f.U 0 1))*h6
include h6 ann in
theorem constraint_44_26_1_1 (f : HomData π 44 26) : ρ ((f.M 3 2))=0 := by
  apply (ann _).mp
  have h12 := f.ambient_descent 3 0
  have h27 := f.commutes 3 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h12 h27
  norm_num at h12 h27
  linear_combination (π)*h12 + (π^4)*h27 + ((f.U 1 1))*h6
include h6 ann in
theorem constraint_44_27_0_0 (f : HomData π 44 27) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h9 h24
  norm_num at h8 h9 h24
  linear_combination (1)*h8 + ((-1)*π)*h9 + (π^2)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_44_28_0_0 (f : HomData π 44 28) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (1)*h8 + (π^2)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_44_29_0_0 (f : HomData π 44 29) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h9 h24
  norm_num at h8 h9 h24
  linear_combination (1)*h8 + ((-1)*π^2)*h9 + (π^3)*h24 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_44_29_1_0 (f : HomData π 44 29) : ρ ((f.M 3 2))=0 := by
  apply (ann _).mp
  have h5 := f.ambient_descent 1 1
  have h12 := f.ambient_descent 3 0
  have h13 := f.ambient_descent 3 1
  have h22 := f.commutes 1 0
  have h26 := f.commutes 3 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h5 h12 h13 h22 h26
  norm_num at h5 h12 h13 h22 h26
  linear_combination (1)*h5 + (1)*h12 + ((-1)*π^2)*h13 + ((-1)*π)*h22 + (π^3)*h26 + ((-1)*(f.M 1 0) + π*(f.M 1 2) + (f.U 0 0))*h6
include h6 ann in
theorem constraint_44_30_0_0 (f : HomData π 44 30) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h8 := f.ambient_descent 2 0
  have h18 := f.source_descent 1 0
  have h21 := f.commutes 0 1
  have h22 := f.commutes 1 0
  have h23 := f.commutes 1 1
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h8 h18 h21 h22 h23 h24
  norm_num at h0 h8 h18 h21 h22 h23 h24
  linear_combination ((-1))*h0 + (1)*h8 + (1)*h18 + ((-1)*π^2)*h21 + (1)*h22 + ((-1)*π)*h23 + (π)*h24 + ((f.M 0 2) + (-1)*π^2*(f.M 1 1) + π*(f.M 1 2) + (f.U 0 1))*h6
include h6 ann in
theorem constraint_44_30_0_1 (f : HomData π 44 30) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π)*h8 + (π^3)*h25 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_44_30_1_1 (f : HomData π 44 30) : ρ ((f.M 3 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h12 := f.ambient_descent 3 0
  have h21 := f.commutes 0 1
  have h27 := f.commutes 3 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h12 h21 h27
  norm_num at h0 h12 h21 h27
  linear_combination (1)*h0 + (π)*h12 + (π^2)*h21 + (π^3)*h27 + ((-1)*(f.M 0 2))*h6
include h6 ann in
theorem constraint_44_31_0_0 (f : HomData π 44 31) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h18 := f.source_descent 1 0
  have h22 := f.commutes 1 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h18 h22 h24
  norm_num at h8 h18 h22 h24
  linear_combination (1)*h8 + (1)*h18 + (1)*h22 + (π)*h24 + ((f.M 1 0) + (-1)*π^2*(f.M 1 1))*h6
include h6 ann in
theorem constraint_44_31_0_1 (f : HomData π 44 31) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π)*h8 + (π^4)*h25 + (π^2*(f.U 0 1))*h6
include h6 ann in
theorem constraint_44_31_1_1 (f : HomData π 44 31) : ρ ((f.M 3 2))=0 := by
  apply (ann _).mp
  have h12 := f.ambient_descent 3 0
  have h27 := f.commutes 3 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h12 h27
  norm_num at h12 h27
  linear_combination (π)*h12 + (π^4)*h27 + ((f.U 1 1))*h6
include h6 ann in
theorem constraint_44_32_0_0 (f : HomData π 44 32) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h9 h24
  norm_num at h8 h9 h24
  linear_combination (1)*h8 + ((-1)*π)*h9 + (π^2)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_44_32_0_1 (f : HomData π 44 32) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π)*h8 + (π^4)*h25 + (π^2*(f.U 0 1))*h6
include h6 ann in
theorem constraint_44_32_1_1 (f : HomData π 44 32) : ρ ((f.M 3 3))=0 := by
  apply (ann _).mp
  have h12 := f.ambient_descent 3 0
  have h27 := f.commutes 3 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h12 h27
  norm_num at h12 h27
  linear_combination (π)*h12 + (π^4)*h27 + ((f.U 1 1))*h6
include h6 ann in
theorem constraint_44_33_0_0 (f : HomData π 44 33) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h18 := f.source_descent 1 0
  have h22 := f.commutes 1 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h18 h22 h24
  norm_num at h8 h18 h22 h24
  linear_combination (1)*h8 + (1)*h18 + (1)*h22 + (π)*h24 + (π*(f.M 1 0) + (-1)*π^2*(f.M 1 1))*h6
include h6 ann in
theorem constraint_44_34_0_0 (f : HomData π 44 34) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h9 h24
  norm_num at h8 h9 h24
  linear_combination (1)*h8 + ((-1)*π)*h9 + (π^2)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_44_35_0_0 (f : HomData π 44 35) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h9 h24
  norm_num at h8 h9 h24
  linear_combination (1)*h8 + ((-1)*π)*h9 + (π^3)*h24 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_44_36_0_0 (f : HomData π 44 36) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h9 h24
  norm_num at h8 h9 h24
  linear_combination (1)*h8 + ((-1)*π)*h9 + (π^2)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_44_37_0_0 (f : HomData π 44 37) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h18 := f.source_descent 1 0
  have h22 := f.commutes 1 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h18 h22 h24
  norm_num at h8 h18 h22 h24
  linear_combination (1)*h8 + (1)*h18 + (1)*h22 + (π)*h24 + ((f.M 1 0) + (-1)*π^2*(f.M 1 1))*h6
include h6 ann in
theorem constraint_44_37_0_1 (f : HomData π 44 37) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π)*h8 + (π^3)*h25 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_44_37_1_1 (f : HomData π 44 37) : ρ ((f.M 3 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h12 := f.ambient_descent 3 0
  have h21 := f.commutes 0 1
  have h27 := f.commutes 3 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h12 h21 h27
  norm_num at h0 h12 h21 h27
  linear_combination (1)*h0 + (π)*h12 + (π^2)*h21 + (π^3)*h27 + ((-1)*(f.M 0 2))*h6
include h6 ann in
theorem constraint_44_38_0_0 (f : HomData π 44 38) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h9 h24
  norm_num at h8 h9 h24
  linear_combination (1)*h8 + ((-1)*π)*h9 + (π^2)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_44_38_0_1 (f : HomData π 44 38) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π)*h8 + (π^3)*h25 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_44_38_1_1 (f : HomData π 44 38) : ρ ((f.M 3 3))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h12 := f.ambient_descent 3 0
  have h21 := f.commutes 0 1
  have h27 := f.commutes 3 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h12 h21 h27
  norm_num at h0 h12 h21 h27
  linear_combination (1)*h0 + (π)*h12 + (π^2)*h21 + (π^3)*h27 + ((-1)*(f.M 0 3))*h6
include h6 ann in
theorem constraint_44_39_0_0 (f : HomData π 44 39) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h9 h24
  norm_num at h8 h9 h24
  linear_combination (1)*h8 + ((-1)*π)*h9 + (π^2)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_44_39_0_1 (f : HomData π 44 39) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π)*h8 + (π^4)*h25 + (π^2*(f.U 0 1))*h6
include h6 ann in
theorem constraint_44_39_1_1 (f : HomData π 44 39) : ρ ((f.M 3 3))=0 := by
  apply (ann _).mp
  have h12 := f.ambient_descent 3 0
  have h27 := f.commutes 3 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h12 h27
  norm_num at h12 h27
  linear_combination (π)*h12 + (π^4)*h27 + ((f.U 1 1))*h6
include h6 ann in
theorem constraint_44_40_0_0 (f : HomData π 44 40) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h18 := f.source_descent 1 0
  have h22 := f.commutes 1 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h18 h22 h24
  norm_num at h8 h18 h22 h24
  linear_combination (1)*h8 + (1)*h18 + (1)*h22 + (π)*h24 + ((f.M 1 0) + (-1)*π^2*(f.M 1 2))*h6
include h6 ann in
theorem constraint_44_40_0_1 (f : HomData π 44 40) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h9 h25
  norm_num at h8 h9 h25
  linear_combination (π)*h8 + ((-1)*π^2)*h9 + (π^3)*h25 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_44_40_1_1 (f : HomData π 44 40) : ρ ((f.M 3 3))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h12 := f.ambient_descent 3 0
  have h13 := f.ambient_descent 3 1
  have h21 := f.commutes 0 1
  have h27 := f.commutes 3 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h12 h13 h21 h27
  norm_num at h0 h1 h12 h13 h21 h27
  linear_combination (1)*h0 + ((-1)*π)*h1 + (π)*h12 + ((-1)*π^2)*h13 + (π^2)*h21 + (π^3)*h27 + ((-1)*(f.M 0 3))*h6
include h6 ann in
theorem constraint_44_41_0_0 (f : HomData π 44 41) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h9 h24
  norm_num at h8 h9 h24
  linear_combination (1)*h8 + ((-1)*π)*h9 + (π^2)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_44_41_0_1 (f : HomData π 44 41) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h9 h25
  norm_num at h8 h9 h25
  linear_combination (π)*h8 + ((-1)*π^2)*h9 + (π^4)*h25 + (π^2*(f.U 0 1))*h6
include h6 ann in
theorem constraint_44_41_1_1 (f : HomData π 44 41) : ρ ((f.M 3 3))=0 := by
  apply (ann _).mp
  have h12 := f.ambient_descent 3 0
  have h13 := f.ambient_descent 3 1
  have h27 := f.commutes 3 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h12 h13 h27
  norm_num at h12 h13 h27
  linear_combination (π)*h12 + ((-1)*π^2)*h13 + (π^4)*h27 + ((f.U 1 1))*h6
include h6 ann in
theorem constraint_44_42_0_0 (f : HomData π 44 42) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h9 := f.ambient_descent 2 1
  have h18 := f.source_descent 1 0
  have h21 := f.commutes 0 1
  have h22 := f.commutes 1 0
  have h23 := f.commutes 1 1
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h9 h18 h21 h22 h23 h24
  norm_num at h0 h1 h9 h18 h21 h22 h23 h24
  linear_combination (1)*h0 + ((-1))*h1 + (1)*h9 + (1)*h18 + (π^2)*h21 + (1)*h22 + (π)*h23 + (π)*h24 + ((-1)*(f.M 0 3) + (f.M 1 0) + (-1)*π^2*(f.M 1 2) + (-1)*π*(f.M 1 3) + (-1)*(f.U 0 1))*h6
include h6 ann in
theorem constraint_44_42_0_1 (f : HomData π 44 42) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h9 h25
  norm_num at h8 h9 h25
  linear_combination (π)*h8 + ((-1)*π)*h9 + (π^3)*h25 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_44_42_1_1 (f : HomData π 44 42) : ρ ((f.M 3 3))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h12 := f.ambient_descent 3 0
  have h13 := f.ambient_descent 3 1
  have h21 := f.commutes 0 1
  have h27 := f.commutes 3 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h12 h13 h21 h27
  norm_num at h0 h1 h12 h13 h21 h27
  linear_combination (1)*h0 + ((-1))*h1 + (π)*h12 + ((-1)*π)*h13 + (π^2)*h21 + (π^3)*h27 + ((-1)*(f.M 0 3))*h6
include h6 ann in
theorem constraint_44_43_0_0 (f : HomData π 44 43) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (1)*h8 + (π^2)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_44_43_0_1 (f : HomData π 44 43) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h9 h25
  norm_num at h8 h9 h25
  linear_combination (1)*h8 + ((-1)*π)*h9 + (π^3)*h25 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_44_43_1_1 (f : HomData π 44 43) : ρ ((f.M 3 3) + (-1)*(f.M 3 2))=0 := by
  apply (ann _).mp
  have h1 := f.ambient_descent 0 1
  have h13 := f.ambient_descent 3 1
  have h20 := f.commutes 0 0
  have h21 := f.commutes 0 1
  have h26 := f.commutes 3 0
  have h27 := f.commutes 3 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h1 h13 h20 h21 h26 h27
  norm_num at h1 h13 h20 h21 h26 h27
  linear_combination ((-1))*h1 + ((-1)*π)*h13 + ((-1)*π)*h20 + (π^2)*h21 + ((-1)*π^2)*h26 + (π^3)*h27 + ((f.M 0 2) + (-1)*(f.M 0 3))*h6
include h6 ann in
theorem constraint_44_44_0_1 (f : HomData π 44 44) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h9 h25
  norm_num at h8 h9 h25
  linear_combination (1)*h8 + ((-1)*π)*h9 + (π^3)*h25 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_44_44_1_1 (f : HomData π 44 44) : ρ ((f.M 3 3) + (-1)*(f.M 2 2))=0 := by
  apply (ann _).mp
  have h9 := f.ambient_descent 2 1
  have h12 := f.ambient_descent 3 0
  have h13 := f.ambient_descent 3 1
  have h18 := f.source_descent 1 0
  have h22 := f.commutes 1 0
  have h23 := f.commutes 1 1
  have h24 := f.commutes 2 0
  have h27 := f.commutes 3 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h9 h12 h13 h18 h22 h23 h24 h27
  norm_num at h9 h12 h13 h18 h22 h23 h24 h27
  linear_combination ((-1))*h9 + (1)*h12 + ((-1)*π)*h13 + ((-1))*h18 + ((-1))*h22 + ((-1)*π)*h23 + ((-1)*π)*h24 + (π^3)*h27 + ((-1)*(f.M 1 0) + π^2*(f.M 1 2) + π*(f.M 1 3) + (f.U 0 1))*h6
include h6 ann in
theorem constraint_44_46_0_0 (f : HomData π 44 46) : ρ ((f.M 2 0))=0 := by
  apply (ann _).mp
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h24
  norm_num at h24
  linear_combination (π^5)*h24 + (π^3*(f.U 0 0))*h6
include h6 ann in
theorem constraint_44_46_1_0 (f : HomData π 44 46) : ρ ((f.M 3 0))=0 := by
  apply (ann _).mp
  have h26 := f.commutes 3 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h26
  norm_num at h26
  linear_combination (π^5)*h26 + (π*(f.U 1 0))*h6
end UniserialComputations.N6
