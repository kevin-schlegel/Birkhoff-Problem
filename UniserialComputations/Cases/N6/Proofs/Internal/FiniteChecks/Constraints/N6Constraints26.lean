import N6Matrix
noncomputable section
namespace UniserialComputations.N6
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
variable {R k : Type*} [CommRing R] [Field k] (π : R) (ρ : R →+* k)
variable (h6 : π^6=0) (ann : ∀ r, π^5*r=0 ↔ ρ r=0)
include h6 ann in
theorem constraint_26_0_0_0 (f : HomData π 26 0) : ρ ((f.M 1 0))=0 := by
  apply (ann _).mp
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h22
  norm_num at h22
  linear_combination (π^4)*h22 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_26_0_1_0 (f : HomData π 26 0) : ρ ((f.M 2 0))=0 := by
  apply (ann _).mp
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h20 h24
  norm_num at h20 h24
  linear_combination (π^2)*h20 + (π^4)*h24 + ((-1)*(f.M 0 0) + (-1)*(f.U 0 0))*h6
include h6 ann in
theorem constraint_26_1_0_0 (f : HomData π 26 1) : ρ ((f.M 1 0))=0 := by
  apply (ann _).mp
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h22
  norm_num at h22
  linear_combination (π^3)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_26_2_0_0 (f : HomData π 26 2) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (π^3)*h4 + (π^4)*h22 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_26_2_1_0 (f : HomData π 26 2) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h8 := f.ambient_descent 2 0
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h8 h20 h24
  norm_num at h0 h8 h20 h24
  linear_combination (π)*h0 + (π^3)*h8 + (π^2)*h20 + (π^4)*h24 + ((-1)*(f.M 0 1) + (-1)*(f.U 0 0))*h6
include h6 ann in
theorem constraint_26_3_0_0 (f : HomData π 26 3) : ρ ((f.M 1 0))=0 := by
  apply (ann _).mp
  have h18 := f.source_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h18 h20 h22
  norm_num at h18 h20 h22
  linear_combination ((-1))*h18 + (π)*h20 + (π^2)*h22 + ((-1)*π*(f.M 0 0))*h6
include h6 ann in
theorem constraint_26_4_0_0 (f : HomData π 26 4) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (π^2)*h4 + (π^3)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_26_5_0_0 (f : HomData π 26 5) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (π^2)*h4 + (π^4)*h22 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_26_5_1_0 (f : HomData π 26 5) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h8 := f.ambient_descent 2 0
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h8 h20 h24
  norm_num at h0 h8 h20 h24
  linear_combination (1)*h0 + (π^2)*h8 + (π^2)*h20 + (π^4)*h24 + ((-1)*(f.M 0 1) + (-1)*(f.U 0 0))*h6
include h6 ann in
theorem constraint_26_6_0_0 (f : HomData π 26 6) : ρ ((f.M 1 0))=0 := by
  apply (ann _).mp
  have h18 := f.source_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h18 h20 h22
  norm_num at h18 h20 h22
  linear_combination ((-1))*h18 + (1)*h20 + (π)*h22 + ((-1)*π*(f.M 0 0))*h6
include h6 ann in
theorem constraint_26_7_0_0 (f : HomData π 26 7) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h4 := f.ambient_descent 1 0
  have h18 := f.source_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h4 h18 h20 h22
  norm_num at h0 h4 h18 h20 h22
  linear_combination (1)*h0 + (π)*h4 + ((-1))*h18 + (π)*h20 + (π^2)*h22 + ((-1)*π*(f.M 0 1))*h6
include h6 ann in
theorem constraint_26_8_0_0 (f : HomData π 26 8) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (π)*h4 + (π^3)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_26_9_0_0 (f : HomData π 26 9) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (π)*h4 + (π^4)*h22 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_26_13_0_0 (f : HomData π 26 13) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (1)*h4 + (π^3)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_26_14_0_0 (f : HomData π 26 14) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (1)*h4 + (π^4)*h22 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_26_15_0_0 (f : HomData π 26 15) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (π^2)*h4 + (π^3)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_26_16_0_0 (f : HomData π 26 16) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h4 := f.ambient_descent 1 0
  have h18 := f.source_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h4 h18 h20 h22
  norm_num at h0 h4 h18 h20 h22
  linear_combination (1)*h0 + (π)*h4 + ((-1))*h18 + (π)*h20 + (π^2)*h22 + ((-1)*π*(f.M 0 1))*h6
include h6 ann in
theorem constraint_26_17_0_0 (f : HomData π 26 17) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (π)*h4 + (π^3)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_26_18_0_0 (f : HomData π 26 18) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h4 := f.ambient_descent 1 0
  have h18 := f.source_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h4 h18 h20 h22
  norm_num at h0 h4 h18 h20 h22
  linear_combination (1)*h0 + (π)*h4 + ((-1))*h18 + (π)*h20 + (π^2)*h22 + ((-1)*π*(f.M 0 1))*h6
include h6 ann in
theorem constraint_26_18_0_1 (f : HomData π 26 18) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π^2)*h4 + (π^4)*h23 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_26_18_1_1 (f : HomData π 26 18) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h8 := f.ambient_descent 2 0
  have h21 := f.commutes 0 1
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h8 h21 h25
  norm_num at h0 h8 h21 h25
  linear_combination (1)*h0 + (π^2)*h8 + (π^2)*h21 + (π^4)*h25 + ((-1)*(f.M 0 2) + (-1)*(f.U 0 1))*h6
include h6 ann in
theorem constraint_26_19_0_0 (f : HomData π 26 19) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h18 := f.source_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h18 h20 h22
  norm_num at h4 h18 h20 h22
  linear_combination (π)*h4 + ((-1))*h18 + (π)*h20 + (π^2)*h22 + ((f.M 0 0) + (-1)*π*(f.M 0 1))*h6
include h6 ann in
theorem constraint_26_20_0_0 (f : HomData π 26 20) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h22
  norm_num at h4 h5 h22
  linear_combination (π)*h4 + ((-1)*π^2)*h5 + (π^3)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_26_23_0_0 (f : HomData π 26 23) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (1)*h4 + (π^3)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_26_24_0_1 (f : HomData π 26 24) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π^2)*h4 + (π^4)*h23 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_26_24_1_1 (f : HomData π 26 24) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h8 := f.ambient_descent 2 0
  have h21 := f.commutes 0 1
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h8 h21 h25
  norm_num at h0 h8 h21 h25
  linear_combination (1)*h0 + (π^2)*h8 + (π^2)*h21 + (π^4)*h25 + ((-1)*(f.M 0 2) + (-1)*(f.U 0 1))*h6
include h6 ann in
theorem constraint_26_26_0_1 (f : HomData π 26 26) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π)*h4 + (π^4)*h23 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_26_26_1_1 (f : HomData π 26 26) : ρ ((f.M 2 2) + (-1)*(f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h8 := f.ambient_descent 2 0
  have h18 := f.source_descent 1 0
  have h20 := f.commutes 0 0
  have h21 := f.commutes 0 1
  have h22 := f.commutes 1 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h8 h18 h20 h21 h22 h25
  norm_num at h4 h8 h18 h20 h21 h22 h25
  linear_combination ((-1))*h4 + (π)*h8 + (1)*h18 + ((-1)*π)*h20 + (π^2)*h21 + ((-1)*π^2)*h22 + (π^4)*h25 + (π*(f.M 0 1) + (-1)*(f.M 0 2) + (-1)*(f.U 0 1))*h6
include h6 ann in
theorem constraint_26_28_0_0 (f : HomData π 26 28) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h18 := f.source_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h18 h20 h22
  norm_num at h4 h18 h20 h22
  linear_combination (1)*h4 + ((-1))*h18 + (π)*h20 + (π^2)*h22 + ((f.M 0 0) + (-1)*π*(f.M 0 1))*h6
include h6 ann in
theorem constraint_26_29_0_0 (f : HomData π 26 29) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h22
  norm_num at h4 h5 h22
  linear_combination (1)*h4 + ((-1)*π^2)*h5 + (π^3)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_26_30_0_1 (f : HomData π 26 30) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π)*h4 + (π^3)*h23 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_26_31_0_1 (f : HomData π 26 31) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π)*h4 + (π^4)*h23 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_26_31_1_1 (f : HomData π 26 31) : ρ ((f.M 2 2) + (-1)*(f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h8 := f.ambient_descent 2 0
  have h18 := f.source_descent 1 0
  have h20 := f.commutes 0 0
  have h21 := f.commutes 0 1
  have h22 := f.commutes 1 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h8 h18 h20 h21 h22 h25
  norm_num at h4 h8 h18 h20 h21 h22 h25
  linear_combination ((-1))*h4 + (π)*h8 + (1)*h18 + ((-1))*h20 + (π^2)*h21 + ((-1)*π)*h22 + (π^4)*h25 + (π*(f.M 0 1) + (-1)*(f.M 0 2) + (-1)*(f.U 0 1))*h6
include h6 ann in
theorem constraint_26_32_0_1 (f : HomData π 26 32) : ρ ((f.M 1 3))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π)*h4 + (π^4)*h23 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_26_32_1_1 (f : HomData π 26 32) : ρ ((f.M 2 3) + (-1)*(f.M 1 2))=0 := by
  apply (ann _).mp
  have h1 := f.ambient_descent 0 1
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h8 := f.ambient_descent 2 0
  have h18 := f.source_descent 1 0
  have h20 := f.commutes 0 0
  have h21 := f.commutes 0 1
  have h22 := f.commutes 1 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h1 h4 h5 h8 h18 h20 h21 h22 h25
  norm_num at h1 h4 h5 h8 h18 h20 h21 h22 h25
  linear_combination (1)*h1 + ((-1))*h4 + (π)*h5 + (π)*h8 + (1)*h18 + ((-1)*π)*h20 + (π^2)*h21 + ((-1)*π^2)*h22 + (π^4)*h25 + (π*(f.M 0 2) + (-1)*(f.M 0 3) + (-1)*(f.U 0 1))*h6
include h6 ann in
theorem constraint_26_33_0_0 (f : HomData π 26 33) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h18 := f.source_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h18 h20 h22
  norm_num at h4 h18 h20 h22
  linear_combination (1)*h4 + ((-1))*h18 + (1)*h20 + (π)*h22 + ((f.M 0 0) + (-1)*π*(f.M 0 1))*h6
include h6 ann in
theorem constraint_26_34_0_0 (f : HomData π 26 34) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h1 := f.ambient_descent 0 1
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h18 := f.source_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h1 h4 h5 h18 h20 h22
  norm_num at h1 h4 h5 h18 h20 h22
  linear_combination ((-1))*h1 + (1)*h4 + ((-1)*π)*h5 + ((-1))*h18 + (π)*h20 + (π^2)*h22 + ((f.M 0 0) + (-1)*π*(f.M 0 2))*h6
include h6 ann in
theorem constraint_26_35_0_0 (f : HomData π 26 35) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h22
  norm_num at h4 h5 h22
  linear_combination (1)*h4 + ((-1)*π)*h5 + (π^3)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_26_36_0_0 (f : HomData π 26 36) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h1 := f.ambient_descent 0 1
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h18 := f.source_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h1 h4 h5 h18 h20 h22
  norm_num at h1 h4 h5 h18 h20 h22
  linear_combination ((-1))*h1 + (1)*h4 + ((-1)*π)*h5 + ((-1))*h18 + (π)*h20 + (π^2)*h22 + ((f.M 0 0) + (-1)*π*(f.M 0 2))*h6
include h6 ann in
theorem constraint_26_37_0_1 (f : HomData π 26 37) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π)*h4 + (π^3)*h23 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_26_38_0_1 (f : HomData π 26 38) : ρ ((f.M 1 3))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π)*h4 + (π^3)*h23 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_26_39_0_1 (f : HomData π 26 39) : ρ ((f.M 1 3))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π)*h4 + (π^4)*h23 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_26_39_1_1 (f : HomData π 26 39) : ρ ((f.M 2 3) + (-1)*(f.M 1 2))=0 := by
  apply (ann _).mp
  have h1 := f.ambient_descent 0 1
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h8 := f.ambient_descent 2 0
  have h18 := f.source_descent 1 0
  have h20 := f.commutes 0 0
  have h21 := f.commutes 0 1
  have h22 := f.commutes 1 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h1 h4 h5 h8 h18 h20 h21 h22 h25
  norm_num at h1 h4 h5 h8 h18 h20 h21 h22 h25
  linear_combination (1)*h1 + ((-1))*h4 + (π)*h5 + (π)*h8 + (1)*h18 + ((-1)*π)*h20 + (π^2)*h21 + ((-1)*π^2)*h22 + (π^4)*h25 + (π*(f.M 0 2) + (-1)*(f.M 0 3) + (-1)*(f.U 0 1))*h6
include h6 ann in
theorem constraint_26_40_0_1 (f : HomData π 26 40) : ρ ((f.M 1 3))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h23
  norm_num at h4 h5 h23
  linear_combination (π)*h4 + ((-1)*π^2)*h5 + (π^3)*h23 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_26_41_0_0 (f : HomData π 26 41) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h1 := f.ambient_descent 0 1
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h18 := f.source_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h1 h4 h5 h18 h20 h22
  norm_num at h1 h4 h5 h18 h20 h22
  linear_combination ((-1))*h1 + (1)*h4 + ((-1)*π)*h5 + ((-1))*h18 + (π)*h20 + (π^2)*h22 + ((f.M 0 0) + (-1)*π*(f.M 0 2))*h6
include h6 ann in
theorem constraint_26_41_0_1 (f : HomData π 26 41) : ρ ((f.M 1 3))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h23
  norm_num at h4 h5 h23
  linear_combination (π)*h4 + ((-1)*π^2)*h5 + (π^4)*h23 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_26_41_1_1 (f : HomData π 26 41) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h1 := f.ambient_descent 0 1
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h21 := f.commutes 0 1
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h1 h8 h9 h21 h25
  norm_num at h1 h8 h9 h21 h25
  linear_combination ((-1))*h1 + (π)*h8 + ((-1)*π^2)*h9 + (π^2)*h21 + (π^4)*h25 + ((f.M 0 0) + (-1)*(f.M 0 3) + (-1)*(f.U 0 1))*h6
include h6 ann in
theorem constraint_26_42_0_1 (f : HomData π 26 42) : ρ ((f.M 1 3))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h23
  norm_num at h4 h5 h23
  linear_combination (π)*h4 + ((-1)*π)*h5 + (π^3)*h23 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_26_43_0_0 (f : HomData π 26 43) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h18 := f.source_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h18 h20 h22
  norm_num at h4 h18 h20 h22
  linear_combination (1)*h4 + ((-1))*h18 + (π)*h20 + (π^2)*h22 + ((f.M 0 0) + (-1)*π*(f.M 0 2))*h6
include h6 ann in
theorem constraint_26_43_0_1 (f : HomData π 26 43) : ρ ((f.M 1 3))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h23
  norm_num at h4 h5 h23
  linear_combination (1)*h4 + ((-1)*π)*h5 + (π^3)*h23 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_26_44_0_1 (f : HomData π 26 44) : ρ ((f.M 1 3))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h23
  norm_num at h4 h5 h23
  linear_combination (1)*h4 + ((-1)*π)*h5 + (π^3)*h23 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_26_46_0_0 (f : HomData π 26 46) : ρ ((f.M 1 0))=0 := by
  apply (ann _).mp
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h22
  norm_num at h22
  linear_combination (π^5)*h22 + (π^2*(f.U 0 0))*h6
include h6 ann in
theorem constraint_26_46_1_0 (f : HomData π 26 46) : ρ ((f.M 2 0))=0 := by
  apply (ann _).mp
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h24
  norm_num at h24
  linear_combination (π^5)*h24 + ((f.U 1 0))*h6
end UniserialComputations.N6
