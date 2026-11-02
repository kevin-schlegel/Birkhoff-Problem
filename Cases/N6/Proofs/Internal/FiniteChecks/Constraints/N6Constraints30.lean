import N6Matrix
noncomputable section
namespace UniserialComputations.N6
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
variable {R k : Type*} [CommRing R] [Field k] (π : R) (ρ : R →+* k)
variable (h6 : π^6=0) (ann : ∀ r, π^5*r=0 ↔ ρ r=0)
include h6 ann in
theorem constraint_30_0_0_0 (f : HomData π 30 0) : ρ ((f.M 1 0))=0 := by
  apply (ann _).mp
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h22
  norm_num at h22
  linear_combination (π^4)*h22 + (π^2*(f.U 0 0))*h6
include h6 ann in
theorem constraint_30_0_1_0 (f : HomData π 30 0) : ρ ((f.M 2 0))=0 := by
  apply (ann _).mp
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h24
  norm_num at h24
  linear_combination (π^4)*h24 + ((f.U 1 0))*h6
include h6 ann in
theorem constraint_30_1_0_0 (f : HomData π 30 1) : ρ ((f.M 1 0))=0 := by
  apply (ann _).mp
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h22
  norm_num at h22
  linear_combination (π^3)*h22 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_30_1_1_0 (f : HomData π 30 1) : ρ ((f.M 2 0))=0 := by
  apply (ann _).mp
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h20 h24
  norm_num at h20 h24
  linear_combination (π)*h20 + (π^3)*h24 + ((-1)*π*(f.M 0 0) + (-1)*(f.U 0 0))*h6
include h6 ann in
theorem constraint_30_2_0_0 (f : HomData π 30 2) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (π^3)*h4 + (π^4)*h22 + (π^2*(f.U 0 0))*h6
include h6 ann in
theorem constraint_30_2_1_0 (f : HomData π 30 2) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (π^3)*h8 + (π^4)*h24 + ((f.U 1 0))*h6
include h6 ann in
theorem constraint_30_3_0_0 (f : HomData π 30 3) : ρ ((f.M 1 0))=0 := by
  apply (ann _).mp
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h22
  norm_num at h22
  linear_combination (π^2)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_30_4_0_0 (f : HomData π 30 4) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (π^2)*h4 + (π^3)*h22 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_30_4_1_0 (f : HomData π 30 4) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h8 := f.ambient_descent 2 0
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h8 h20 h24
  norm_num at h0 h8 h20 h24
  linear_combination (1)*h0 + (π^2)*h8 + (π)*h20 + (π^3)*h24 + ((-1)*π*(f.M 0 1) + (-1)*(f.U 0 0))*h6
include h6 ann in
theorem constraint_30_5_0_0 (f : HomData π 30 5) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (π^2)*h4 + (π^4)*h22 + (π^2*(f.U 0 0))*h6
include h6 ann in
theorem constraint_30_5_1_0 (f : HomData π 30 5) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (π^2)*h8 + (π^4)*h24 + ((f.U 1 0))*h6
include h6 ann in
theorem constraint_30_6_0_0 (f : HomData π 30 6) : ρ ((f.M 1 0))=0 := by
  apply (ann _).mp
  have h18 := f.source_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h18 h20 h22
  norm_num at h18 h20 h22
  linear_combination ((-1))*h18 + (1)*h20 + (π)*h22 + ((-1)*π^2*(f.M 0 0))*h6
include h6 ann in
theorem constraint_30_7_0_0 (f : HomData π 30 7) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (π)*h4 + (π^2)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_30_8_0_0 (f : HomData π 30 8) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (π)*h4 + (π^3)*h22 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_30_9_0_0 (f : HomData π 30 9) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (π)*h4 + (π^4)*h22 + (π^2*(f.U 0 0))*h6
include h6 ann in
theorem constraint_30_9_1_0 (f : HomData π 30 9) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (π)*h8 + (π^4)*h24 + ((f.U 1 0))*h6
include h6 ann in
theorem constraint_30_12_0_0 (f : HomData π 30 12) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (1)*h4 + (π^2)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_30_13_0_0 (f : HomData π 30 13) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (1)*h4 + (π^3)*h22 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_30_14_0_0 (f : HomData π 30 14) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (1)*h4 + (π^4)*h22 + (π^2*(f.U 0 0))*h6
include h6 ann in
theorem constraint_30_14_1_0 (f : HomData π 30 14) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (1)*h8 + (π^4)*h24 + ((f.U 1 0))*h6
include h6 ann in
theorem constraint_30_15_0_0 (f : HomData π 30 15) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (π^2)*h4 + (π^3)*h22 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_30_15_1_0 (f : HomData π 30 15) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h20 h24
  norm_num at h8 h20 h24
  linear_combination (π^2)*h8 + (π)*h20 + (π^3)*h24 + ((f.M 0 0) + (-1)*π*(f.M 0 1) + (-1)*(f.U 0 0))*h6
include h6 ann in
theorem constraint_30_16_0_0 (f : HomData π 30 16) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (π)*h4 + (π^2)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_30_17_0_0 (f : HomData π 30 17) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (π)*h4 + (π^3)*h22 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_30_17_1_0 (f : HomData π 30 17) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h20 h24
  norm_num at h8 h20 h24
  linear_combination (π)*h8 + (π)*h20 + (π^3)*h24 + ((f.M 0 0) + (-1)*π*(f.M 0 1) + (-1)*(f.U 0 0))*h6
include h6 ann in
theorem constraint_30_18_0_0 (f : HomData π 30 18) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (π)*h4 + (π^2)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_30_18_0_1 (f : HomData π 30 18) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π^2)*h4 + (π^4)*h23 + (π^2*(f.U 0 1))*h6
include h6 ann in
theorem constraint_30_18_1_1 (f : HomData π 30 18) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π^2)*h8 + (π^4)*h25 + ((f.U 1 1))*h6
include h6 ann in
theorem constraint_30_19_0_0 (f : HomData π 30 19) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (π)*h4 + (π^2)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_30_20_0_0 (f : HomData π 30 20) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h22
  norm_num at h4 h5 h22
  linear_combination (π)*h4 + ((-1)*π^2)*h5 + (π^3)*h22 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_30_20_1_0 (f : HomData π 30 20) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h1 := f.ambient_descent 0 1
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h1 h8 h9 h20 h24
  norm_num at h1 h8 h9 h20 h24
  linear_combination ((-1))*h1 + (π)*h8 + ((-1)*π^2)*h9 + (π)*h20 + (π^3)*h24 + ((f.M 0 0) + (-1)*π*(f.M 0 2) + (-1)*(f.U 0 0))*h6
include h6 ann in
theorem constraint_30_22_0_0 (f : HomData π 30 22) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (1)*h4 + (π^2)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_30_23_0_0 (f : HomData π 30 23) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (1)*h4 + (π^3)*h22 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_30_23_1_0 (f : HomData π 30 23) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h20 h24
  norm_num at h8 h20 h24
  linear_combination (1)*h8 + (π)*h20 + (π^3)*h24 + ((f.M 0 0) + (-1)*π*(f.M 0 1) + (-1)*(f.U 0 0))*h6
include h6 ann in
theorem constraint_30_24_0_1 (f : HomData π 30 24) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π^2)*h4 + (π^4)*h23 + (π^2*(f.U 0 1))*h6
include h6 ann in
theorem constraint_30_24_1_1 (f : HomData π 30 24) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π^2)*h8 + (π^4)*h25 + ((f.U 1 1))*h6
include h6 ann in
theorem constraint_30_25_0_0 (f : HomData π 30 25) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h18 := f.source_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h18 h20 h22
  norm_num at h4 h18 h20 h22
  linear_combination (1)*h4 + ((-1))*h18 + (1)*h20 + (π)*h22 + ((f.M 0 0) + (-1)*π^2*(f.M 0 1))*h6
include h6 ann in
theorem constraint_30_26_0_0 (f : HomData π 30 26) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (1)*h4 + (π^2)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_30_26_0_1 (f : HomData π 30 26) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π)*h4 + (π^4)*h23 + (π^2*(f.U 0 1))*h6
include h6 ann in
theorem constraint_30_26_1_1 (f : HomData π 30 26) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π)*h8 + (π^4)*h25 + ((f.U 1 1))*h6
include h6 ann in
theorem constraint_30_27_0_0 (f : HomData π 30 27) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h22
  norm_num at h4 h5 h22
  linear_combination (1)*h4 + ((-1)*π)*h5 + (π^2)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_30_28_0_0 (f : HomData π 30 28) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (1)*h4 + (π^2)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_30_29_0_0 (f : HomData π 30 29) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h22
  norm_num at h4 h5 h22
  linear_combination (1)*h4 + ((-1)*π^2)*h5 + (π^3)*h22 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_30_29_1_0 (f : HomData π 30 29) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h1 := f.ambient_descent 0 1
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h1 h8 h9 h20 h24
  norm_num at h1 h8 h9 h20 h24
  linear_combination ((-1))*h1 + (1)*h8 + ((-1)*π^2)*h9 + (π)*h20 + (π^3)*h24 + ((f.M 0 0) + (-1)*π*(f.M 0 2) + (-1)*(f.U 0 0))*h6
include h6 ann in
theorem constraint_30_30_0_1 (f : HomData π 30 30) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π)*h4 + (π^3)*h23 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_30_30_1_1 (f : HomData π 30 30) : ρ ((f.M 2 2) + (-1)*(f.M 1 1))=0 := by
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
  linear_combination ((-1))*h4 + (π)*h8 + (1)*h18 + ((-1))*h20 + (π)*h21 + ((-1)*π)*h22 + (π^3)*h25 + (π^2*(f.M 0 1) + (-1)*π*(f.M 0 2) + (-1)*(f.U 0 1))*h6
include h6 ann in
theorem constraint_30_31_0_0 (f : HomData π 30 31) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h18 := f.source_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h18 h20 h22
  norm_num at h4 h18 h20 h22
  linear_combination (1)*h4 + ((-1))*h18 + (1)*h20 + (π)*h22 + ((f.M 0 0) + (-1)*π^2*(f.M 0 1))*h6
include h6 ann in
theorem constraint_30_31_0_1 (f : HomData π 30 31) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π)*h4 + (π^4)*h23 + (π^2*(f.U 0 1))*h6
include h6 ann in
theorem constraint_30_31_1_1 (f : HomData π 30 31) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π)*h8 + (π^4)*h25 + ((f.U 1 1))*h6
include h6 ann in
theorem constraint_30_32_0_0 (f : HomData π 30 32) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h22
  norm_num at h4 h5 h22
  linear_combination (1)*h4 + ((-1)*π)*h5 + (π^2)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_30_32_0_1 (f : HomData π 30 32) : ρ ((f.M 1 3))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π)*h4 + (π^4)*h23 + (π^2*(f.U 0 1))*h6
include h6 ann in
theorem constraint_30_32_1_1 (f : HomData π 30 32) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π)*h8 + (π^4)*h25 + ((f.U 1 1))*h6
include h6 ann in
theorem constraint_30_33_0_0 (f : HomData π 30 33) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h18 := f.source_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h18 h20 h22
  norm_num at h4 h18 h20 h22
  linear_combination (1)*h4 + ((-1))*h18 + (1)*h20 + (π)*h22 + (π*(f.M 0 0) + (-1)*π^2*(f.M 0 1))*h6
include h6 ann in
theorem constraint_30_34_0_0 (f : HomData π 30 34) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h22
  norm_num at h4 h5 h22
  linear_combination (1)*h4 + ((-1)*π)*h5 + (π^2)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_30_35_0_0 (f : HomData π 30 35) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h22
  norm_num at h4 h5 h22
  linear_combination (1)*h4 + ((-1)*π)*h5 + (π^3)*h22 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_30_36_0_0 (f : HomData π 30 36) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h22
  norm_num at h4 h5 h22
  linear_combination (1)*h4 + ((-1)*π)*h5 + (π^2)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_30_37_0_0 (f : HomData π 30 37) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h18 := f.source_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h18 h20 h22
  norm_num at h4 h18 h20 h22
  linear_combination (1)*h4 + ((-1))*h18 + (1)*h20 + (π)*h22 + ((f.M 0 0) + (-1)*π^2*(f.M 0 1))*h6
include h6 ann in
theorem constraint_30_37_0_1 (f : HomData π 30 37) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π)*h4 + (π^3)*h23 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_30_37_1_1 (f : HomData π 30 37) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h21 := f.commutes 0 1
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h21 h25
  norm_num at h8 h21 h25
  linear_combination (π)*h8 + (π)*h21 + (π^3)*h25 + ((f.M 0 0) + (-1)*π*(f.M 0 2) + (-1)*(f.U 0 1))*h6
include h6 ann in
theorem constraint_30_38_0_0 (f : HomData π 30 38) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h22
  norm_num at h4 h5 h22
  linear_combination (1)*h4 + ((-1)*π)*h5 + (π^2)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_30_38_0_1 (f : HomData π 30 38) : ρ ((f.M 1 3))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π)*h4 + (π^3)*h23 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_30_38_1_1 (f : HomData π 30 38) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h21 := f.commutes 0 1
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h21 h25
  norm_num at h8 h21 h25
  linear_combination (π)*h8 + (π)*h21 + (π^3)*h25 + ((f.M 0 0) + (-1)*π*(f.M 0 3) + (-1)*(f.U 0 1))*h6
include h6 ann in
theorem constraint_30_39_0_0 (f : HomData π 30 39) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h22
  norm_num at h4 h5 h22
  linear_combination (1)*h4 + ((-1)*π)*h5 + (π^2)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_30_39_0_1 (f : HomData π 30 39) : ρ ((f.M 1 3))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π)*h4 + (π^4)*h23 + (π^2*(f.U 0 1))*h6
include h6 ann in
theorem constraint_30_39_1_1 (f : HomData π 30 39) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π)*h8 + (π^4)*h25 + ((f.U 1 1))*h6
include h6 ann in
theorem constraint_30_40_0_0 (f : HomData π 30 40) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h18 := f.source_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h18 h20 h22
  norm_num at h4 h18 h20 h22
  linear_combination (1)*h4 + ((-1))*h18 + (1)*h20 + (π)*h22 + ((f.M 0 0) + (-1)*π^2*(f.M 0 2))*h6
include h6 ann in
theorem constraint_30_40_0_1 (f : HomData π 30 40) : ρ ((f.M 1 3))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h23
  norm_num at h4 h5 h23
  linear_combination (π)*h4 + ((-1)*π^2)*h5 + (π^3)*h23 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_30_40_1_1 (f : HomData π 30 40) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h1 := f.ambient_descent 0 1
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h21 := f.commutes 0 1
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h1 h8 h9 h21 h25
  norm_num at h1 h8 h9 h21 h25
  linear_combination ((-1))*h1 + (π)*h8 + ((-1)*π^2)*h9 + (π)*h21 + (π^3)*h25 + ((f.M 0 0) + (-1)*π*(f.M 0 3) + (-1)*(f.U 0 1))*h6
include h6 ann in
theorem constraint_30_41_0_0 (f : HomData π 30 41) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h22
  norm_num at h4 h5 h22
  linear_combination (1)*h4 + ((-1)*π)*h5 + (π^2)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_30_41_0_1 (f : HomData π 30 41) : ρ ((f.M 1 3))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h23
  norm_num at h4 h5 h23
  linear_combination (π)*h4 + ((-1)*π^2)*h5 + (π^4)*h23 + (π^2*(f.U 0 1))*h6
include h6 ann in
theorem constraint_30_41_1_1 (f : HomData π 30 41) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h9 h25
  norm_num at h8 h9 h25
  linear_combination (π)*h8 + ((-1)*π^2)*h9 + (π^4)*h25 + ((f.U 1 1))*h6
include h6 ann in
theorem constraint_30_42_0_1 (f : HomData π 30 42) : ρ ((f.M 1 3))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h23
  norm_num at h4 h5 h23
  linear_combination (π)*h4 + ((-1)*π)*h5 + (π^3)*h23 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_30_42_1_1 (f : HomData π 30 42) : ρ ((f.M 2 3) + (f.M 1 2))=0 := by
  apply (ann _).mp
  have h5 := f.ambient_descent 1 1
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h18 := f.source_descent 1 0
  have h20 := f.commutes 0 0
  have h21 := f.commutes 0 1
  have h22 := f.commutes 1 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h5 h8 h9 h18 h20 h21 h22 h25
  norm_num at h5 h8 h9 h18 h20 h21 h22 h25
  linear_combination (1)*h5 + (π)*h8 + ((-1)*π)*h9 + ((-1))*h18 + (1)*h20 + (π)*h21 + (π)*h22 + (π^3)*h25 + ((f.M 0 0) + (-1)*π^2*(f.M 0 2) + (-1)*π*(f.M 0 3) + (-1)*(f.U 0 1))*h6
include h6 ann in
theorem constraint_30_43_0_0 (f : HomData π 30 43) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (1)*h4 + (π^2)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_30_43_0_1 (f : HomData π 30 43) : ρ ((f.M 1 3))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h23
  norm_num at h4 h5 h23
  linear_combination (1)*h4 + ((-1)*π)*h5 + (π^3)*h23 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_30_44_0_1 (f : HomData π 30 44) : ρ ((f.M 1 3))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h23
  norm_num at h4 h5 h23
  linear_combination (1)*h4 + ((-1)*π)*h5 + (π^3)*h23 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_30_44_1_1 (f : HomData π 30 44) : ρ ((f.M 2 3) + (f.M 1 2))=0 := by
  apply (ann _).mp
  have h5 := f.ambient_descent 1 1
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h18 := f.source_descent 1 0
  have h20 := f.commutes 0 0
  have h21 := f.commutes 0 1
  have h22 := f.commutes 1 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h5 h8 h9 h18 h20 h21 h22 h25
  norm_num at h5 h8 h9 h18 h20 h21 h22 h25
  linear_combination (1)*h5 + (1)*h8 + ((-1)*π)*h9 + ((-1))*h18 + (1)*h20 + (π)*h21 + (π)*h22 + (π^3)*h25 + ((f.M 0 0) + (-1)*π^2*(f.M 0 2) + (-1)*π*(f.M 0 3) + (-1)*(f.U 0 1))*h6
include h6 ann in
theorem constraint_30_46_0_0 (f : HomData π 30 46) : ρ ((f.M 1 0))=0 := by
  apply (ann _).mp
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h22
  norm_num at h22
  linear_combination (π^5)*h22 + (π^3*(f.U 0 0))*h6
include h6 ann in
theorem constraint_30_46_1_0 (f : HomData π 30 46) : ρ ((f.M 2 0))=0 := by
  apply (ann _).mp
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h24
  norm_num at h24
  linear_combination (π^5)*h24 + (π*(f.U 1 0))*h6
end UniserialComputations.N6
