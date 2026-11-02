import N6Matrix
noncomputable section
namespace UniserialComputations.N6
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
variable {R k : Type*} [CommRing R] [Field k] (π : R) (ρ : R →+* k)
variable (h6 : π^6=0) (ann : ∀ r, π^5*r=0 ↔ ρ r=0)
include h6 ann in
theorem constraint_36_0_0_0 (f : HomData π 36 0) : ρ ((f.M 2 0))=0 := by
  apply (ann _).mp
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h24
  norm_num at h24
  linear_combination (π^4)*h24 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_36_1_0_0 (f : HomData π 36 1) : ρ ((f.M 2 0))=0 := by
  apply (ann _).mp
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h24
  norm_num at h24
  linear_combination (π^3)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_36_2_0_0 (f : HomData π 36 2) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (π^3)*h8 + (π^4)*h24 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_36_3_0_0 (f : HomData π 36 3) : ρ ((f.M 2 0))=0 := by
  apply (ann _).mp
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h20 h24
  norm_num at h20 h24
  linear_combination (π)*h20 + (π^2)*h24 + ((-1)*(f.M 0 0))*h6
include h6 ann in
theorem constraint_36_4_0_0 (f : HomData π 36 4) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (π^2)*h8 + (π^3)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_36_5_0_0 (f : HomData π 36 5) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (π^2)*h8 + (π^4)*h24 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_36_6_0_0 (f : HomData π 36 6) : ρ ((f.M 2 0))=0 := by
  apply (ann _).mp
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h20 h24
  norm_num at h20 h24
  linear_combination (1)*h20 + (π)*h24 + ((-1)*(f.M 0 0))*h6
include h6 ann in
theorem constraint_36_7_0_0 (f : HomData π 36 7) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h8 := f.ambient_descent 2 0
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h8 h20 h24
  norm_num at h0 h8 h20 h24
  linear_combination (1)*h0 + (π)*h8 + (π)*h20 + (π^2)*h24 + ((-1)*(f.M 0 1))*h6
include h6 ann in
theorem constraint_36_8_0_0 (f : HomData π 36 8) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (π)*h8 + (π^3)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_36_9_0_0 (f : HomData π 36 9) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (π)*h8 + (π^4)*h24 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_36_13_0_0 (f : HomData π 36 13) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (1)*h8 + (π^3)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_36_14_0_0 (f : HomData π 36 14) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (1)*h8 + (π^4)*h24 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_36_15_0_0 (f : HomData π 36 15) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (π^2)*h8 + (π^3)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_36_16_0_0 (f : HomData π 36 16) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h8 := f.ambient_descent 2 0
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h8 h20 h24
  norm_num at h0 h8 h20 h24
  linear_combination (1)*h0 + (π)*h8 + (π)*h20 + (π^2)*h24 + ((-1)*(f.M 0 1))*h6
include h6 ann in
theorem constraint_36_17_0_0 (f : HomData π 36 17) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (π)*h8 + (π^3)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_36_18_0_0 (f : HomData π 36 18) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h8 := f.ambient_descent 2 0
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h8 h20 h24
  norm_num at h0 h8 h20 h24
  linear_combination (1)*h0 + (π)*h8 + (π)*h20 + (π^2)*h24 + ((-1)*(f.M 0 1))*h6
include h6 ann in
theorem constraint_36_18_0_1 (f : HomData π 36 18) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π^2)*h8 + (π^4)*h25 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_36_19_0_0 (f : HomData π 36 19) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h8 := f.ambient_descent 2 0
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h8 h20 h24
  norm_num at h0 h8 h20 h24
  linear_combination (1)*h0 + (π)*h8 + (π)*h20 + (π^2)*h24 + ((-1)*(f.M 0 1))*h6
include h6 ann in
theorem constraint_36_20_0_0 (f : HomData π 36 20) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h9 h24
  norm_num at h8 h9 h24
  linear_combination (π)*h8 + ((-1)*π^2)*h9 + (π^3)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_36_23_0_0 (f : HomData π 36 23) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (1)*h8 + (π^3)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_36_24_0_1 (f : HomData π 36 24) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π^2)*h8 + (π^4)*h25 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_36_26_0_0 (f : HomData π 36 26) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h22 := f.commutes 1 0
  have h23 := f.commutes 1 1
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h22 h23 h24
  norm_num at h8 h22 h23 h24
  linear_combination (1)*h8 + ((-1))*h22 + (π)*h23 + (π^2)*h24 + (π*(f.M 1 1) + (-1)*(f.M 1 2) + (f.U 0 1))*h6
include h6 ann in
theorem constraint_36_26_0_1 (f : HomData π 36 26) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π)*h8 + (π^4)*h25 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_36_28_0_0 (f : HomData π 36 28) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h22 := f.commutes 1 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h22 h24
  norm_num at h8 h22 h24
  linear_combination (1)*h8 + ((-1))*h22 + (π^2)*h24 + ((-1)*(f.M 1 0) + π*(f.M 1 1))*h6
include h6 ann in
theorem constraint_36_29_0_0 (f : HomData π 36 29) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h9 h24
  norm_num at h8 h9 h24
  linear_combination (1)*h8 + ((-1)*π^2)*h9 + (π^3)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_36_30_0_1 (f : HomData π 36 30) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π)*h8 + (π^3)*h25 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_36_31_0_1 (f : HomData π 36 31) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π)*h8 + (π^4)*h25 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_36_32_0_1 (f : HomData π 36 32) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π)*h8 + (π^4)*h25 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_36_35_0_0 (f : HomData π 36 35) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h9 h24
  norm_num at h8 h9 h24
  linear_combination (1)*h8 + ((-1)*π)*h9 + (π^3)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_36_37_0_1 (f : HomData π 36 37) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π)*h8 + (π^3)*h25 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_36_38_0_1 (f : HomData π 36 38) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π)*h8 + (π^3)*h25 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_36_39_0_1 (f : HomData π 36 39) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π)*h8 + (π^4)*h25 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_36_40_0_1 (f : HomData π 36 40) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h9 h25
  norm_num at h8 h9 h25
  linear_combination (π)*h8 + ((-1)*π^2)*h9 + (π^3)*h25 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_36_41_0_0 (f : HomData π 36 41) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h22 := f.commutes 1 0
  have h23 := f.commutes 1 1
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h9 h22 h23 h24
  norm_num at h8 h9 h22 h23 h24
  linear_combination (1)*h8 + ((-1)*π)*h9 + ((-1))*h22 + (π)*h23 + (π^2)*h24 + (π*(f.M 1 2) + (-1)*(f.M 1 3) + (f.U 0 1))*h6
include h6 ann in
theorem constraint_36_41_0_1 (f : HomData π 36 41) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h9 h25
  norm_num at h8 h9 h25
  linear_combination (π)*h8 + ((-1)*π^2)*h9 + (π^4)*h25 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_36_42_0_1 (f : HomData π 36 42) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h9 h25
  norm_num at h8 h9 h25
  linear_combination (π)*h8 + ((-1)*π)*h9 + (π^3)*h25 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_36_43_0_0 (f : HomData π 36 43) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h1 := f.ambient_descent 0 1
  have h8 := f.ambient_descent 2 0
  have h20 := f.commutes 0 0
  have h21 := f.commutes 0 1
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h1 h8 h20 h21 h24
  norm_num at h1 h8 h20 h21 h24
  linear_combination (1)*h1 + (1)*h8 + (π)*h20 + ((-1)*π^2)*h21 + (π^2)*h24 + ((-1)*(f.M 0 2) + (f.M 0 3) + (f.U 0 1))*h6
include h6 ann in
theorem constraint_36_43_0_1 (f : HomData π 36 43) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h9 h25
  norm_num at h8 h9 h25
  linear_combination (1)*h8 + ((-1)*π)*h9 + (π^3)*h25 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_36_44_0_1 (f : HomData π 36 44) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h9 h25
  norm_num at h8 h9 h25
  linear_combination (1)*h8 + ((-1)*π)*h9 + (π^3)*h25 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_36_46_0_0 (f : HomData π 36 46) : ρ ((f.M 2 0))=0 := by
  apply (ann _).mp
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h24
  norm_num at h24
  linear_combination (π^5)*h24 + (π^2*(f.U 0 0))*h6
end UniserialComputations.N6
