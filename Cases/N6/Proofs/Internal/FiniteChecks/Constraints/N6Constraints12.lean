import N6Matrix
noncomputable section
namespace UniserialComputations.N6
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
variable {R k : Type*} [CommRing R] [Field k] (π : R) (ρ : R →+* k)
variable (h6 : π^6=0) (ann : ∀ r, π^5*r=0 ↔ ρ r=0)
include h6 ann in
theorem constraint_12_0_0_0 (f : HomData π 12 0) : ρ ((f.M 1 0))=0 := by
  apply (ann _).mp
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h22
  norm_num at h22
  linear_combination (π^4)*h22 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_12_1_0_0 (f : HomData π 12 1) : ρ ((f.M 1 0))=0 := by
  apply (ann _).mp
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h22
  norm_num at h22
  linear_combination (π^3)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_12_2_0_0 (f : HomData π 12 2) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (π^3)*h4 + (π^4)*h22 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_12_3_0_0 (f : HomData π 12 3) : ρ ((f.M 1 0))=0 := by
  apply (ann _).mp
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h20 h22
  norm_num at h20 h22
  linear_combination (π)*h20 + (π^2)*h22 + ((-1)*π^2*(f.M 0 0))*h6
include h6 ann in
theorem constraint_12_4_0_0 (f : HomData π 12 4) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (π^2)*h4 + (π^3)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_12_5_0_0 (f : HomData π 12 5) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (π^2)*h4 + (π^4)*h22 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_12_6_0_0 (f : HomData π 12 6) : ρ ((f.M 1 0))=0 := by
  apply (ann _).mp
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h20 h22
  norm_num at h20 h22
  linear_combination (1)*h20 + (π)*h22 + ((-1)*π^2*(f.M 0 0))*h6
include h6 ann in
theorem constraint_12_7_0_0 (f : HomData π 12 7) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h4 := f.ambient_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h4 h20 h22
  norm_num at h0 h4 h20 h22
  linear_combination (1)*h0 + (π)*h4 + (π)*h20 + (π^2)*h22 + ((-1)*π^2*(f.M 0 1))*h6
include h6 ann in
theorem constraint_12_8_0_0 (f : HomData π 12 8) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (π)*h4 + (π^3)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_12_9_0_0 (f : HomData π 12 9) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (π)*h4 + (π^4)*h22 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_12_13_0_0 (f : HomData π 12 13) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (1)*h4 + (π^3)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_12_14_0_0 (f : HomData π 12 14) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (1)*h4 + (π^4)*h22 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_12_15_0_0 (f : HomData π 12 15) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (π^2)*h4 + (π^3)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_12_16_0_0 (f : HomData π 12 16) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h20 h22
  norm_num at h4 h20 h22
  linear_combination (π)*h4 + (π)*h20 + (π^2)*h22 + ((f.M 0 0) + (-1)*π^2*(f.M 0 1))*h6
include h6 ann in
theorem constraint_12_17_0_0 (f : HomData π 12 17) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (π)*h4 + (π^3)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_12_18_0_0 (f : HomData π 12 18) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h20 h22
  norm_num at h4 h20 h22
  linear_combination (π)*h4 + (π)*h20 + (π^2)*h22 + ((f.M 0 0) + (-1)*π^2*(f.M 0 1))*h6
include h6 ann in
theorem constraint_12_18_0_1 (f : HomData π 12 18) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π^2)*h4 + (π^4)*h23 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_12_19_0_0 (f : HomData π 12 19) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h20 h22
  norm_num at h4 h20 h22
  linear_combination (π)*h4 + (π)*h20 + (π^2)*h22 + (π*(f.M 0 0) + (-1)*π^2*(f.M 0 1))*h6
include h6 ann in
theorem constraint_12_20_0_0 (f : HomData π 12 20) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h22
  norm_num at h4 h5 h22
  linear_combination (π)*h4 + ((-1)*π^2)*h5 + (π^3)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_12_22_0_0 (f : HomData π 12 22) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h20 h22
  norm_num at h4 h20 h22
  linear_combination (1)*h4 + (π)*h20 + (π^2)*h22 + ((f.M 0 0) + (-1)*π^2*(f.M 0 1))*h6
include h6 ann in
theorem constraint_12_23_0_0 (f : HomData π 12 23) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (1)*h4 + (π^3)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_12_24_0_1 (f : HomData π 12 24) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π^2)*h4 + (π^4)*h23 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_12_25_0_0 (f : HomData π 12 25) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h20 h22
  norm_num at h4 h20 h22
  linear_combination (1)*h4 + (1)*h20 + (π)*h22 + ((f.M 0 0) + (-1)*π^2*(f.M 0 1))*h6
include h6 ann in
theorem constraint_12_26_0_0 (f : HomData π 12 26) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h20 h22
  norm_num at h4 h20 h22
  linear_combination (1)*h4 + (π)*h20 + (π^2)*h22 + ((f.M 0 0) + (-1)*π^2*(f.M 0 1))*h6
include h6 ann in
theorem constraint_12_26_0_1 (f : HomData π 12 26) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π)*h4 + (π^4)*h23 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_12_27_0_0 (f : HomData π 12 27) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h1 := f.ambient_descent 0 1
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h1 h4 h5 h20 h22
  norm_num at h1 h4 h5 h20 h22
  linear_combination ((-1))*h1 + (1)*h4 + ((-1)*π)*h5 + (π)*h20 + (π^2)*h22 + ((f.M 0 0) + (-1)*π^2*(f.M 0 2))*h6
include h6 ann in
theorem constraint_12_28_0_0 (f : HomData π 12 28) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h20 h22
  norm_num at h4 h20 h22
  linear_combination (1)*h4 + (π)*h20 + (π^2)*h22 + (π*(f.M 0 0) + (-1)*π^2*(f.M 0 1))*h6
include h6 ann in
theorem constraint_12_29_0_0 (f : HomData π 12 29) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h22
  norm_num at h4 h5 h22
  linear_combination (1)*h4 + ((-1)*π^2)*h5 + (π^3)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_12_30_0_1 (f : HomData π 12 30) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π)*h4 + (π^3)*h23 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_12_31_0_0 (f : HomData π 12 31) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h20 h22
  norm_num at h4 h20 h22
  linear_combination (1)*h4 + (1)*h20 + (π)*h22 + ((f.M 0 0) + (-1)*π^2*(f.M 0 1))*h6
include h6 ann in
theorem constraint_12_31_0_1 (f : HomData π 12 31) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π)*h4 + (π^4)*h23 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_12_32_0_0 (f : HomData π 12 32) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h1 := f.ambient_descent 0 1
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h1 h4 h5 h20 h22
  norm_num at h1 h4 h5 h20 h22
  linear_combination ((-1))*h1 + (1)*h4 + ((-1)*π)*h5 + (π)*h20 + (π^2)*h22 + ((f.M 0 0) + (-1)*π^2*(f.M 0 2))*h6
include h6 ann in
theorem constraint_12_32_0_1 (f : HomData π 12 32) : ρ ((f.M 1 3))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π)*h4 + (π^4)*h23 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_12_33_0_0 (f : HomData π 12 33) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h20 h22
  norm_num at h4 h20 h22
  linear_combination (1)*h4 + (1)*h20 + (π)*h22 + (π*(f.M 0 0) + (-1)*π^2*(f.M 0 1))*h6
include h6 ann in
theorem constraint_12_34_0_0 (f : HomData π 12 34) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h1 := f.ambient_descent 0 1
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h1 h4 h5 h20 h22
  norm_num at h1 h4 h5 h20 h22
  linear_combination ((-1))*h1 + (1)*h4 + ((-1)*π)*h5 + (π)*h20 + (π^2)*h22 + (π*(f.M 0 0) + (-1)*π^2*(f.M 0 2))*h6
include h6 ann in
theorem constraint_12_35_0_0 (f : HomData π 12 35) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h22
  norm_num at h4 h5 h22
  linear_combination (1)*h4 + ((-1)*π)*h5 + (π^3)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_12_36_0_0 (f : HomData π 12 36) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h20 h22
  norm_num at h4 h5 h20 h22
  linear_combination (1)*h4 + ((-1)*π)*h5 + (π)*h20 + (π^2)*h22 + (π*(f.M 0 0) + (-1)*(f.M 0 1) + (-1)*π^2*(f.M 0 2))*h6
include h6 ann in
theorem constraint_12_37_0_0 (f : HomData π 12 37) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h20 h22
  norm_num at h4 h20 h22
  linear_combination (1)*h4 + (1)*h20 + (π)*h22 + ((f.M 0 0) + (-1)*π^2*(f.M 0 1))*h6
include h6 ann in
theorem constraint_12_37_0_1 (f : HomData π 12 37) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π)*h4 + (π^3)*h23 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_12_38_0_0 (f : HomData π 12 38) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h1 := f.ambient_descent 0 1
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h1 h4 h5 h20 h22
  norm_num at h1 h4 h5 h20 h22
  linear_combination ((-1))*h1 + (1)*h4 + ((-1)*π)*h5 + (π)*h20 + (π^2)*h22 + ((f.M 0 0) + (-1)*π^2*(f.M 0 2))*h6
include h6 ann in
theorem constraint_12_38_0_1 (f : HomData π 12 38) : ρ ((f.M 1 3))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π)*h4 + (π^3)*h23 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_12_39_0_0 (f : HomData π 12 39) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h20 h22
  norm_num at h4 h5 h20 h22
  linear_combination (1)*h4 + ((-1)*π)*h5 + (π)*h20 + (π^2)*h22 + ((f.M 0 0) + (-1)*(f.M 0 1) + (-1)*π^2*(f.M 0 2))*h6
include h6 ann in
theorem constraint_12_39_0_1 (f : HomData π 12 39) : ρ ((f.M 1 3))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π)*h4 + (π^4)*h23 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_12_40_0_0 (f : HomData π 12 40) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h20 h22
  norm_num at h4 h20 h22
  linear_combination (1)*h4 + (1)*h20 + (π)*h22 + ((f.M 0 0) + (-1)*π^2*(f.M 0 2))*h6
include h6 ann in
theorem constraint_12_40_0_1 (f : HomData π 12 40) : ρ ((f.M 1 3))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h23
  norm_num at h4 h5 h23
  linear_combination (π)*h4 + ((-1)*π^2)*h5 + (π^3)*h23 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_12_41_0_0 (f : HomData π 12 41) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h20 h22
  norm_num at h4 h5 h20 h22
  linear_combination (1)*h4 + ((-1)*π)*h5 + (π)*h20 + (π^2)*h22 + (π*(f.M 0 0) + (-1)*(f.M 0 1) + (-1)*π^2*(f.M 0 2))*h6
include h6 ann in
theorem constraint_12_41_0_1 (f : HomData π 12 41) : ρ ((f.M 1 3))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h23
  norm_num at h4 h5 h23
  linear_combination (π)*h4 + ((-1)*π^2)*h5 + (π^4)*h23 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_12_42_0_1 (f : HomData π 12 42) : ρ ((f.M 1 3))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h23
  norm_num at h4 h5 h23
  linear_combination (π)*h4 + ((-1)*π)*h5 + (π^3)*h23 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_12_43_0_0 (f : HomData π 12 43) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h20 h22
  norm_num at h4 h20 h22
  linear_combination (1)*h4 + (π)*h20 + (π^2)*h22 + (π*(f.M 0 0) + (-1)*π^2*(f.M 0 2))*h6
include h6 ann in
theorem constraint_12_43_0_1 (f : HomData π 12 43) : ρ ((f.M 1 3))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h23
  norm_num at h4 h5 h23
  linear_combination (1)*h4 + ((-1)*π)*h5 + (π^3)*h23 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_12_44_0_1 (f : HomData π 12 44) : ρ ((f.M 1 3))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h23
  norm_num at h4 h5 h23
  linear_combination (1)*h4 + ((-1)*π)*h5 + (π^3)*h23 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_12_46_0_0 (f : HomData π 12 46) : ρ ((f.M 1 0))=0 := by
  apply (ann _).mp
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h22
  norm_num at h22
  linear_combination (π^5)*h22 + (π^2*(f.U 0 0))*h6
end UniserialComputations.N6
