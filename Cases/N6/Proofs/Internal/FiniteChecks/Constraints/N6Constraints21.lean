import N6Matrix
noncomputable section
namespace UniserialComputations.N6
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
variable {R k : Type*} [CommRing R] [Field k] (π : R) (ρ : R →+* k)
variable (h6 : π^6=0) (ann : ∀ r, π^5*r=0 ↔ ρ r=0)
include h6 ann in
theorem constraint_21_0_0_0 (f : HomData π 21 0) : ρ ((f.M 1 0))=0 := by
  apply (ann _).mp
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h22
  norm_num at h22
  linear_combination (π^4)*h22 + (π^2*(f.U 0 0))*h6
include h6 ann in
theorem constraint_21_1_0_0 (f : HomData π 21 1) : ρ ((f.M 1 0))=0 := by
  apply (ann _).mp
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h22
  norm_num at h22
  linear_combination (π^3)*h22 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_21_2_0_0 (f : HomData π 21 2) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (π^3)*h4 + (π^4)*h22 + (π^2*(f.U 0 0))*h6
include h6 ann in
theorem constraint_21_3_0_0 (f : HomData π 21 3) : ρ ((f.M 1 0))=0 := by
  apply (ann _).mp
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h22
  norm_num at h22
  linear_combination (π^2)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_21_4_0_0 (f : HomData π 21 4) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (π^2)*h4 + (π^3)*h22 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_21_5_0_0 (f : HomData π 21 5) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (π^2)*h4 + (π^4)*h22 + (π^2*(f.U 0 0))*h6
include h6 ann in
theorem constraint_21_6_0_0 (f : HomData π 21 6) : ρ ((f.M 1 0))=0 := by
  apply (ann _).mp
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h20 h22
  norm_num at h20 h22
  linear_combination (1)*h20 + (π)*h22 + ((-1)*π^2*(f.M 0 0))*h6
include h6 ann in
theorem constraint_21_7_0_0 (f : HomData π 21 7) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (π)*h4 + (π^2)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_21_8_0_0 (f : HomData π 21 8) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (π)*h4 + (π^3)*h22 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_21_9_0_0 (f : HomData π 21 9) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (π)*h4 + (π^4)*h22 + (π^2*(f.U 0 0))*h6
include h6 ann in
theorem constraint_21_12_0_0 (f : HomData π 21 12) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (1)*h4 + (π^2)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_21_13_0_0 (f : HomData π 21 13) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (1)*h4 + (π^3)*h22 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_21_14_0_0 (f : HomData π 21 14) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (1)*h4 + (π^4)*h22 + (π^2*(f.U 0 0))*h6
include h6 ann in
theorem constraint_21_15_0_0 (f : HomData π 21 15) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (π^2)*h4 + (π^3)*h22 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_21_16_0_0 (f : HomData π 21 16) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (π)*h4 + (π^2)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_21_17_0_0 (f : HomData π 21 17) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (π)*h4 + (π^3)*h22 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_21_18_0_0 (f : HomData π 21 18) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (π)*h4 + (π^2)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_21_18_0_1 (f : HomData π 21 18) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π^2)*h4 + (π^4)*h23 + (π^2*(f.U 0 1))*h6
include h6 ann in
theorem constraint_21_19_0_0 (f : HomData π 21 19) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (π)*h4 + (π^2)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_21_20_0_0 (f : HomData π 21 20) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h22
  norm_num at h4 h5 h22
  linear_combination (π)*h4 + ((-1)*π^2)*h5 + (π^3)*h22 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_21_22_0_0 (f : HomData π 21 22) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (1)*h4 + (π^2)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_21_23_0_0 (f : HomData π 21 23) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (1)*h4 + (π^3)*h22 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_21_24_0_0 (f : HomData π 21 24) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h20 := f.commutes 0 0
  have h21 := f.commutes 0 1
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h20 h21 h22
  norm_num at h4 h20 h21 h22
  linear_combination (1)*h4 + (1)*h20 + ((-1)*π)*h21 + (π)*h22 + ((-1)*π^2*(f.M 0 1) + (f.M 0 2) + (f.U 0 1))*h6
include h6 ann in
theorem constraint_21_24_0_1 (f : HomData π 21 24) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π^2)*h4 + (π^4)*h23 + (π^2*(f.U 0 1))*h6
include h6 ann in
theorem constraint_21_25_0_0 (f : HomData π 21 25) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h20 h22
  norm_num at h4 h20 h22
  linear_combination (1)*h4 + (1)*h20 + (π)*h22 + ((f.M 0 0) + (-1)*π^2*(f.M 0 1))*h6
include h6 ann in
theorem constraint_21_26_0_0 (f : HomData π 21 26) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (1)*h4 + (π^2)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_21_26_0_1 (f : HomData π 21 26) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π)*h4 + (π^4)*h23 + (π^2*(f.U 0 1))*h6
include h6 ann in
theorem constraint_21_27_0_0 (f : HomData π 21 27) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h22
  norm_num at h4 h5 h22
  linear_combination (1)*h4 + ((-1)*π)*h5 + (π^2)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_21_28_0_0 (f : HomData π 21 28) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (1)*h4 + (π^2)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_21_29_0_0 (f : HomData π 21 29) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h22
  norm_num at h4 h5 h22
  linear_combination (1)*h4 + ((-1)*π^2)*h5 + (π^3)*h22 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_21_30_0_0 (f : HomData π 21 30) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h20 := f.commutes 0 0
  have h21 := f.commutes 0 1
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h20 h21 h22
  norm_num at h4 h20 h21 h22
  linear_combination (1)*h4 + (1)*h20 + ((-1)*π)*h21 + (π)*h22 + ((-1)*π^2*(f.M 0 1) + π*(f.M 0 2) + (f.U 0 1))*h6
include h6 ann in
theorem constraint_21_30_0_1 (f : HomData π 21 30) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π)*h4 + (π^3)*h23 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_21_31_0_0 (f : HomData π 21 31) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h20 h22
  norm_num at h4 h20 h22
  linear_combination (1)*h4 + (1)*h20 + (π)*h22 + ((f.M 0 0) + (-1)*π^2*(f.M 0 1))*h6
include h6 ann in
theorem constraint_21_31_0_1 (f : HomData π 21 31) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π)*h4 + (π^4)*h23 + (π^2*(f.U 0 1))*h6
include h6 ann in
theorem constraint_21_32_0_0 (f : HomData π 21 32) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h22
  norm_num at h4 h5 h22
  linear_combination (1)*h4 + ((-1)*π)*h5 + (π^2)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_21_32_0_1 (f : HomData π 21 32) : ρ ((f.M 1 3))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π)*h4 + (π^4)*h23 + (π^2*(f.U 0 1))*h6
include h6 ann in
theorem constraint_21_33_0_0 (f : HomData π 21 33) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h20 h22
  norm_num at h4 h20 h22
  linear_combination (1)*h4 + (1)*h20 + (π)*h22 + (π*(f.M 0 0) + (-1)*π^2*(f.M 0 1))*h6
include h6 ann in
theorem constraint_21_34_0_0 (f : HomData π 21 34) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h22
  norm_num at h4 h5 h22
  linear_combination (1)*h4 + ((-1)*π)*h5 + (π^2)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_21_35_0_0 (f : HomData π 21 35) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h22
  norm_num at h4 h5 h22
  linear_combination (1)*h4 + ((-1)*π)*h5 + (π^3)*h22 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_21_36_0_0 (f : HomData π 21 36) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h22
  norm_num at h4 h5 h22
  linear_combination (1)*h4 + ((-1)*π)*h5 + (π^2)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_21_37_0_0 (f : HomData π 21 37) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h20 h22
  norm_num at h4 h20 h22
  linear_combination (1)*h4 + (1)*h20 + (π)*h22 + ((f.M 0 0) + (-1)*π^2*(f.M 0 1))*h6
include h6 ann in
theorem constraint_21_37_0_1 (f : HomData π 21 37) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π)*h4 + (π^3)*h23 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_21_38_0_0 (f : HomData π 21 38) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h22
  norm_num at h4 h5 h22
  linear_combination (1)*h4 + ((-1)*π)*h5 + (π^2)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_21_38_0_1 (f : HomData π 21 38) : ρ ((f.M 1 3))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π)*h4 + (π^3)*h23 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_21_39_0_0 (f : HomData π 21 39) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h22
  norm_num at h4 h5 h22
  linear_combination (1)*h4 + ((-1)*π)*h5 + (π^2)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_21_39_0_1 (f : HomData π 21 39) : ρ ((f.M 1 3))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π)*h4 + (π^4)*h23 + (π^2*(f.U 0 1))*h6
include h6 ann in
theorem constraint_21_40_0_0 (f : HomData π 21 40) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h20 h22
  norm_num at h4 h20 h22
  linear_combination (1)*h4 + (1)*h20 + (π)*h22 + ((f.M 0 0) + (-1)*π^2*(f.M 0 2))*h6
include h6 ann in
theorem constraint_21_40_0_1 (f : HomData π 21 40) : ρ ((f.M 1 3))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h23
  norm_num at h4 h5 h23
  linear_combination (π)*h4 + ((-1)*π^2)*h5 + (π^3)*h23 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_21_41_0_0 (f : HomData π 21 41) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h22
  norm_num at h4 h5 h22
  linear_combination (1)*h4 + ((-1)*π)*h5 + (π^2)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_21_41_0_1 (f : HomData π 21 41) : ρ ((f.M 1 3))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h23
  norm_num at h4 h5 h23
  linear_combination (π)*h4 + ((-1)*π^2)*h5 + (π^4)*h23 + (π^2*(f.U 0 1))*h6
include h6 ann in
theorem constraint_21_42_0_0 (f : HomData π 21 42) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h5 := f.ambient_descent 1 1
  have h20 := f.commutes 0 0
  have h21 := f.commutes 0 1
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h5 h20 h21 h22
  norm_num at h5 h20 h21 h22
  linear_combination (1)*h5 + (1)*h20 + (π)*h21 + (π)*h22 + ((f.M 0 0) + (-1)*π^2*(f.M 0 2) + (-1)*π*(f.M 0 3) + (-1)*(f.U 0 1))*h6
include h6 ann in
theorem constraint_21_42_0_1 (f : HomData π 21 42) : ρ ((f.M 1 3))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h23
  norm_num at h4 h5 h23
  linear_combination (π)*h4 + ((-1)*π)*h5 + (π^3)*h23 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_21_43_0_0 (f : HomData π 21 43) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (1)*h4 + (π^2)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_21_43_0_1 (f : HomData π 21 43) : ρ ((f.M 1 3))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h23
  norm_num at h4 h5 h23
  linear_combination (1)*h4 + ((-1)*π)*h5 + (π^3)*h23 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_21_44_0_0 (f : HomData π 21 44) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h5 := f.ambient_descent 1 1
  have h20 := f.commutes 0 0
  have h21 := f.commutes 0 1
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h5 h20 h21 h22
  norm_num at h5 h20 h21 h22
  linear_combination (1)*h5 + (1)*h20 + (π)*h21 + (π)*h22 + ((f.M 0 0) + (-1)*π^2*(f.M 0 2) + (-1)*π*(f.M 0 3) + (-1)*(f.U 0 1))*h6
include h6 ann in
theorem constraint_21_44_0_1 (f : HomData π 21 44) : ρ ((f.M 1 3))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h23
  norm_num at h4 h5 h23
  linear_combination (1)*h4 + ((-1)*π)*h5 + (π^3)*h23 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_21_46_0_0 (f : HomData π 21 46) : ρ ((f.M 1 0))=0 := by
  apply (ann _).mp
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h22
  norm_num at h22
  linear_combination (π^5)*h22 + (π^3*(f.U 0 0))*h6
end UniserialComputations.N6
