import N6Matrix
noncomputable section
namespace UniserialComputations.N6
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
variable {R k : Type*} [CommRing R] [Field k] (π : R) (ρ : R →+* k)
variable (h6 : π^6=0) (ann : ∀ r, π^5*r=0 ↔ ρ r=0)
include h6 ann in
theorem constraint_13_0_0_0 (f : HomData π 13 0) : ρ ((f.M 1 0))=0 := by
  apply (ann _).mp
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h22
  norm_num at h22
  linear_combination (π^4)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_13_1_0_0 (f : HomData π 13 1) : ρ ((f.M 1 0))=0 := by
  apply (ann _).mp
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h20 h22
  norm_num at h20 h22
  linear_combination (π^2)*h20 + (π^3)*h22 + ((-1)*π*(f.M 0 0))*h6
include h6 ann in
theorem constraint_13_2_0_0 (f : HomData π 13 2) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (π^3)*h4 + (π^4)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_13_3_0_0 (f : HomData π 13 3) : ρ ((f.M 1 0))=0 := by
  apply (ann _).mp
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h20 h22
  norm_num at h20 h22
  linear_combination (π)*h20 + (π^2)*h22 + ((-1)*π*(f.M 0 0))*h6
include h6 ann in
theorem constraint_13_4_0_0 (f : HomData π 13 4) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h4 := f.ambient_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h4 h20 h22
  norm_num at h0 h4 h20 h22
  linear_combination (π)*h0 + (π^2)*h4 + (π^2)*h20 + (π^3)*h22 + ((-1)*π*(f.M 0 1))*h6
include h6 ann in
theorem constraint_13_5_0_0 (f : HomData π 13 5) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (π^2)*h4 + (π^4)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_13_6_0_0 (f : HomData π 13 6) : ρ ((f.M 1 0))=0 := by
  apply (ann _).mp
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h20 h22
  norm_num at h20 h22
  linear_combination (1)*h20 + (π)*h22 + ((-1)*π*(f.M 0 0))*h6
include h6 ann in
theorem constraint_13_7_0_0 (f : HomData π 13 7) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h4 := f.ambient_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h4 h20 h22
  norm_num at h0 h4 h20 h22
  linear_combination (1)*h0 + (π)*h4 + (π)*h20 + (π^2)*h22 + ((-1)*π*(f.M 0 1))*h6
include h6 ann in
theorem constraint_13_8_0_0 (f : HomData π 13 8) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h4 := f.ambient_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h4 h20 h22
  norm_num at h0 h4 h20 h22
  linear_combination (1)*h0 + (π)*h4 + (π^2)*h20 + (π^3)*h22 + ((-1)*π*(f.M 0 1))*h6
include h6 ann in
theorem constraint_13_9_0_0 (f : HomData π 13 9) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (π)*h4 + (π^4)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_13_14_0_0 (f : HomData π 13 14) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (1)*h4 + (π^4)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_13_15_0_0 (f : HomData π 13 15) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h20 h22
  norm_num at h4 h20 h22
  linear_combination (π^2)*h4 + (π^2)*h20 + (π^3)*h22 + ((f.M 0 0) + (-1)*π*(f.M 0 1))*h6
include h6 ann in
theorem constraint_13_16_0_0 (f : HomData π 13 16) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h4 := f.ambient_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h4 h20 h22
  norm_num at h0 h4 h20 h22
  linear_combination (1)*h0 + (π)*h4 + (π)*h20 + (π^2)*h22 + ((-1)*π*(f.M 0 1))*h6
include h6 ann in
theorem constraint_13_17_0_0 (f : HomData π 13 17) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h20 h22
  norm_num at h4 h20 h22
  linear_combination (π)*h4 + (π^2)*h20 + (π^3)*h22 + ((f.M 0 0) + (-1)*π*(f.M 0 1))*h6
include h6 ann in
theorem constraint_13_18_0_0 (f : HomData π 13 18) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h4 := f.ambient_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h4 h20 h22
  norm_num at h0 h4 h20 h22
  linear_combination (1)*h0 + (π)*h4 + (π)*h20 + (π^2)*h22 + ((-1)*π*(f.M 0 1))*h6
include h6 ann in
theorem constraint_13_18_0_1 (f : HomData π 13 18) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π^2)*h4 + (π^4)*h23 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_13_19_0_0 (f : HomData π 13 19) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h20 h22
  norm_num at h4 h20 h22
  linear_combination (π)*h4 + (π)*h20 + (π^2)*h22 + ((f.M 0 0) + (-1)*π*(f.M 0 1))*h6
include h6 ann in
theorem constraint_13_20_0_0 (f : HomData π 13 20) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h1 := f.ambient_descent 0 1
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h1 h4 h5 h20 h22
  norm_num at h1 h4 h5 h20 h22
  linear_combination ((-1)*π)*h1 + (π)*h4 + ((-1)*π^2)*h5 + (π^2)*h20 + (π^3)*h22 + ((f.M 0 0) + (-1)*π*(f.M 0 2))*h6
include h6 ann in
theorem constraint_13_23_0_0 (f : HomData π 13 23) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h20 h22
  norm_num at h4 h20 h22
  linear_combination (1)*h4 + (π^2)*h20 + (π^3)*h22 + ((f.M 0 0) + (-1)*π*(f.M 0 1))*h6
include h6 ann in
theorem constraint_13_24_0_1 (f : HomData π 13 24) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π^2)*h4 + (π^4)*h23 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_13_26_0_1 (f : HomData π 13 26) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π)*h4 + (π^4)*h23 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_13_28_0_0 (f : HomData π 13 28) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h20 h22
  norm_num at h4 h20 h22
  linear_combination (1)*h4 + (π)*h20 + (π^2)*h22 + ((f.M 0 0) + (-1)*π*(f.M 0 1))*h6
include h6 ann in
theorem constraint_13_29_0_0 (f : HomData π 13 29) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h1 := f.ambient_descent 0 1
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h1 h4 h5 h20 h22
  norm_num at h1 h4 h5 h20 h22
  linear_combination ((-1)*π)*h1 + (1)*h4 + ((-1)*π^2)*h5 + (π^2)*h20 + (π^3)*h22 + ((f.M 0 0) + (-1)*π*(f.M 0 2))*h6
include h6 ann in
theorem constraint_13_30_0_1 (f : HomData π 13 30) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h4 := f.ambient_descent 1 0
  have h21 := f.commutes 0 1
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h4 h21 h23
  norm_num at h0 h4 h21 h23
  linear_combination (1)*h0 + (π)*h4 + (π^2)*h21 + (π^3)*h23 + ((-1)*π*(f.M 0 2))*h6
include h6 ann in
theorem constraint_13_31_0_1 (f : HomData π 13 31) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π)*h4 + (π^4)*h23 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_13_32_0_1 (f : HomData π 13 32) : ρ ((f.M 1 3))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π)*h4 + (π^4)*h23 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_13_33_0_0 (f : HomData π 13 33) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h20 h22
  norm_num at h4 h20 h22
  linear_combination (1)*h4 + (1)*h20 + (π)*h22 + ((f.M 0 0) + (-1)*π*(f.M 0 1))*h6
include h6 ann in
theorem constraint_13_34_0_0 (f : HomData π 13 34) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h1 := f.ambient_descent 0 1
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h1 h4 h5 h20 h22
  norm_num at h1 h4 h5 h20 h22
  linear_combination ((-1))*h1 + (1)*h4 + ((-1)*π)*h5 + (π)*h20 + (π^2)*h22 + ((f.M 0 0) + (-1)*π*(f.M 0 2))*h6
include h6 ann in
theorem constraint_13_35_0_0 (f : HomData π 13 35) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h1 := f.ambient_descent 0 1
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h1 h4 h5 h20 h22
  norm_num at h1 h4 h5 h20 h22
  linear_combination ((-1))*h1 + (1)*h4 + ((-1)*π)*h5 + (π^2)*h20 + (π^3)*h22 + ((f.M 0 0) + (-1)*π*(f.M 0 2))*h6
include h6 ann in
theorem constraint_13_36_0_0 (f : HomData π 13 36) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h1 := f.ambient_descent 0 1
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h1 h4 h5 h20 h22
  norm_num at h1 h4 h5 h20 h22
  linear_combination ((-1))*h1 + (1)*h4 + ((-1)*π)*h5 + (π)*h20 + (π^2)*h22 + ((f.M 0 0) + (-1)*π*(f.M 0 2))*h6
include h6 ann in
theorem constraint_13_37_0_1 (f : HomData π 13 37) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h21 := f.commutes 0 1
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h21 h23
  norm_num at h4 h21 h23
  linear_combination (π)*h4 + (π^2)*h21 + (π^3)*h23 + ((f.M 0 0) + (-1)*π*(f.M 0 2))*h6
include h6 ann in
theorem constraint_13_38_0_1 (f : HomData π 13 38) : ρ ((f.M 1 3))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h21 := f.commutes 0 1
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h21 h23
  norm_num at h4 h21 h23
  linear_combination (π)*h4 + (π^2)*h21 + (π^3)*h23 + ((f.M 0 0) + (-1)*π*(f.M 0 3))*h6
include h6 ann in
theorem constraint_13_39_0_1 (f : HomData π 13 39) : ρ ((f.M 1 3))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π)*h4 + (π^4)*h23 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_13_40_0_1 (f : HomData π 13 40) : ρ ((f.M 1 3))=0 := by
  apply (ann _).mp
  have h1 := f.ambient_descent 0 1
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h21 := f.commutes 0 1
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h1 h4 h5 h21 h23
  norm_num at h1 h4 h5 h21 h23
  linear_combination ((-1)*π)*h1 + (π)*h4 + ((-1)*π^2)*h5 + (π^2)*h21 + (π^3)*h23 + ((f.M 0 0) + (-1)*π*(f.M 0 3))*h6
include h6 ann in
theorem constraint_13_41_0_0 (f : HomData π 13 41) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h1 := f.ambient_descent 0 1
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h1 h4 h5 h20 h22
  norm_num at h1 h4 h5 h20 h22
  linear_combination ((-1))*h1 + (1)*h4 + ((-1)*π)*h5 + (π)*h20 + (π^2)*h22 + ((f.M 0 0) + (-1)*π*(f.M 0 2))*h6
include h6 ann in
theorem constraint_13_41_0_1 (f : HomData π 13 41) : ρ ((f.M 1 3))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h23
  norm_num at h4 h5 h23
  linear_combination (π)*h4 + ((-1)*π^2)*h5 + (π^4)*h23 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_13_42_0_1 (f : HomData π 13 42) : ρ ((f.M 1 3))=0 := by
  apply (ann _).mp
  have h1 := f.ambient_descent 0 1
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h21 := f.commutes 0 1
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h1 h4 h5 h21 h23
  norm_num at h1 h4 h5 h21 h23
  linear_combination ((-1))*h1 + (π)*h4 + ((-1)*π)*h5 + (π^2)*h21 + (π^3)*h23 + ((f.M 0 0) + (-1)*π*(f.M 0 3))*h6
include h6 ann in
theorem constraint_13_43_0_0 (f : HomData π 13 43) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h20 h22
  norm_num at h4 h20 h22
  linear_combination (1)*h4 + (π)*h20 + (π^2)*h22 + ((f.M 0 0) + (-1)*π*(f.M 0 2))*h6
include h6 ann in
theorem constraint_13_43_0_1 (f : HomData π 13 43) : ρ ((f.M 1 3))=0 := by
  apply (ann _).mp
  have h1 := f.ambient_descent 0 1
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h21 := f.commutes 0 1
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h1 h4 h5 h21 h23
  norm_num at h1 h4 h5 h21 h23
  linear_combination ((-1))*h1 + (1)*h4 + ((-1)*π)*h5 + (π^2)*h21 + (π^3)*h23 + ((f.M 0 0) + (-1)*π*(f.M 0 3))*h6
include h6 ann in
theorem constraint_13_44_0_1 (f : HomData π 13 44) : ρ ((f.M 1 3))=0 := by
  apply (ann _).mp
  have h1 := f.ambient_descent 0 1
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h21 := f.commutes 0 1
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h1 h4 h5 h21 h23
  norm_num at h1 h4 h5 h21 h23
  linear_combination ((-1))*h1 + (1)*h4 + ((-1)*π)*h5 + (π^2)*h21 + (π^3)*h23 + ((f.M 0 0) + (-1)*π*(f.M 0 3))*h6
include h6 ann in
theorem constraint_13_46_0_0 (f : HomData π 13 46) : ρ ((f.M 1 0))=0 := by
  apply (ann _).mp
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h22
  norm_num at h22
  linear_combination (π^5)*h22 + (π*(f.U 0 0))*h6
end UniserialComputations.N6
