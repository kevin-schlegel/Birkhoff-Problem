import N6Matrix
noncomputable section
namespace UniserialComputations.N6
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
variable {R k : Type*} [CommRing R] [Field k] (π : R) (ρ : R →+* k)
variable (h6 : π^6=0) (ann : ∀ r, π^5*r=0 ↔ ρ r=0)
include h6 ann in
theorem constraint_32_0_0_0 (f : HomData π 32 0) : ρ ((f.M 2 0))=0 := by
  apply (ann _).mp
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h24
  norm_num at h24
  linear_combination (π^4)*h24 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_32_0_1_0 (f : HomData π 32 0) : ρ ((f.M 3 0))=0 := by
  apply (ann _).mp
  have h20 := f.commutes 0 0
  have h26 := f.commutes 3 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h20 h26
  norm_num at h20 h26
  linear_combination (π^2)*h20 + (π^4)*h26 + ((-1)*(f.M 0 0) + (-1)*(f.U 0 0))*h6
include h6 ann in
theorem constraint_32_1_0_0 (f : HomData π 32 1) : ρ ((f.M 2 0))=0 := by
  apply (ann _).mp
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h24
  norm_num at h24
  linear_combination (π^3)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_32_1_1_0 (f : HomData π 32 1) : ρ ((f.M 3 0))=0 := by
  apply (ann _).mp
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  have h26 := f.commutes 3 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h20 h22 h26
  norm_num at h20 h22 h26
  linear_combination (π)*h20 + (1)*h22 + (π^3)*h26 + ((-1)*(f.M 0 0) + (-1)*π*(f.M 1 0))*h6
include h6 ann in
theorem constraint_32_2_0_0 (f : HomData π 32 2) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (π^3)*h8 + (π^4)*h24 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_32_2_1_0 (f : HomData π 32 2) : ρ ((f.M 3 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h12 := f.ambient_descent 3 0
  have h20 := f.commutes 0 0
  have h26 := f.commutes 3 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h12 h20 h26
  norm_num at h0 h12 h20 h26
  linear_combination (π)*h0 + (π^3)*h12 + (π^2)*h20 + (π^4)*h26 + ((-1)*(f.M 0 1) + (-1)*(f.U 0 0))*h6
include h6 ann in
theorem constraint_32_3_0_0 (f : HomData π 32 3) : ρ ((f.M 2 0))=0 := by
  apply (ann _).mp
  have h18 := f.source_descent 1 0
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h18 h20 h24
  norm_num at h18 h20 h24
  linear_combination ((-1))*h18 + (π)*h20 + (π^2)*h24 + ((-1)*π*(f.M 0 0))*h6
include h6 ann in
theorem constraint_32_4_0_0 (f : HomData π 32 4) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (π^2)*h8 + (π^3)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_32_5_0_0 (f : HomData π 32 5) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (π^2)*h8 + (π^4)*h24 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_32_5_1_0 (f : HomData π 32 5) : ρ ((f.M 3 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h12 := f.ambient_descent 3 0
  have h20 := f.commutes 0 0
  have h26 := f.commutes 3 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h12 h20 h26
  norm_num at h0 h12 h20 h26
  linear_combination (1)*h0 + (π^2)*h12 + (π^2)*h20 + (π^4)*h26 + ((-1)*(f.M 0 1) + (-1)*(f.U 0 0))*h6
include h6 ann in
theorem constraint_32_6_0_0 (f : HomData π 32 6) : ρ ((f.M 2 0))=0 := by
  apply (ann _).mp
  have h18 := f.source_descent 1 0
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h18 h20 h24
  norm_num at h18 h20 h24
  linear_combination ((-1))*h18 + (1)*h20 + (π)*h24 + ((-1)*π*(f.M 0 0))*h6
include h6 ann in
theorem constraint_32_7_0_0 (f : HomData π 32 7) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h8 := f.ambient_descent 2 0
  have h18 := f.source_descent 1 0
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h8 h18 h20 h24
  norm_num at h0 h8 h18 h20 h24
  linear_combination (1)*h0 + (π)*h8 + ((-1))*h18 + (π)*h20 + (π^2)*h24 + ((-1)*π*(f.M 0 1))*h6
include h6 ann in
theorem constraint_32_8_0_0 (f : HomData π 32 8) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (π)*h8 + (π^3)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_32_9_0_0 (f : HomData π 32 9) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (π)*h8 + (π^4)*h24 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_32_13_0_0 (f : HomData π 32 13) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (1)*h8 + (π^3)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_32_14_0_0 (f : HomData π 32 14) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (1)*h8 + (π^4)*h24 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_32_15_0_0 (f : HomData π 32 15) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (π^2)*h8 + (π^3)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_32_15_1_0 (f : HomData π 32 15) : ρ ((f.M 3 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h12 := f.ambient_descent 3 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  have h26 := f.commutes 3 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h12 h20 h22 h26
  norm_num at h0 h12 h20 h22 h26
  linear_combination (1)*h0 + (π^2)*h12 + (π)*h20 + (1)*h22 + (π^3)*h26 + ((-1)*(f.M 0 1) + (f.M 1 0) + (-1)*π*(f.M 1 1))*h6
include h6 ann in
theorem constraint_32_16_0_0 (f : HomData π 32 16) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h8 := f.ambient_descent 2 0
  have h18 := f.source_descent 1 0
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h8 h18 h20 h24
  norm_num at h0 h8 h18 h20 h24
  linear_combination (1)*h0 + (π)*h8 + ((-1))*h18 + (π)*h20 + (π^2)*h24 + ((-1)*π*(f.M 0 1))*h6
include h6 ann in
theorem constraint_32_17_0_0 (f : HomData π 32 17) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (π)*h8 + (π^3)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_32_18_0_0 (f : HomData π 32 18) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h8 := f.ambient_descent 2 0
  have h18 := f.source_descent 1 0
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h8 h18 h20 h24
  norm_num at h0 h8 h18 h20 h24
  linear_combination (1)*h0 + (π)*h8 + ((-1))*h18 + (π)*h20 + (π^2)*h24 + ((-1)*π*(f.M 0 1))*h6
include h6 ann in
theorem constraint_32_18_0_1 (f : HomData π 32 18) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π^2)*h8 + (π^4)*h25 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_32_18_1_1 (f : HomData π 32 18) : ρ ((f.M 3 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h12 := f.ambient_descent 3 0
  have h21 := f.commutes 0 1
  have h27 := f.commutes 3 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h12 h21 h27
  norm_num at h0 h12 h21 h27
  linear_combination (1)*h0 + (π^2)*h12 + (π^2)*h21 + (π^4)*h27 + ((-1)*(f.M 0 2) + (-1)*(f.U 0 1))*h6
include h6 ann in
theorem constraint_32_19_0_0 (f : HomData π 32 19) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h18 := f.source_descent 1 0
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h18 h20 h24
  norm_num at h8 h18 h20 h24
  linear_combination (π)*h8 + ((-1))*h18 + (π)*h20 + (π^2)*h24 + ((f.M 0 0) + (-1)*π*(f.M 0 1))*h6
include h6 ann in
theorem constraint_32_20_0_0 (f : HomData π 32 20) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h9 h24
  norm_num at h8 h9 h24
  linear_combination (π)*h8 + ((-1)*π^2)*h9 + (π^3)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_32_22_0_0 (f : HomData π 32 22) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h22 := f.commutes 1 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h22 h24
  norm_num at h8 h22 h24
  linear_combination (1)*h8 + ((-1))*h22 + (π^2)*h24 + ((-1)*(f.M 1 0) + π^2*(f.M 1 1))*h6
include h6 ann in
theorem constraint_32_23_0_0 (f : HomData π 32 23) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (1)*h8 + (π^3)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_32_24_0_1 (f : HomData π 32 24) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π^2)*h8 + (π^4)*h25 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_32_24_1_1 (f : HomData π 32 24) : ρ ((f.M 3 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h12 := f.ambient_descent 3 0
  have h21 := f.commutes 0 1
  have h27 := f.commutes 3 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h12 h21 h27
  norm_num at h0 h12 h21 h27
  linear_combination (1)*h0 + (π^2)*h12 + (π^2)*h21 + (π^4)*h27 + ((-1)*(f.M 0 2) + (-1)*(f.U 0 1))*h6
include h6 ann in
theorem constraint_32_26_0_0 (f : HomData π 32 26) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h22 := f.commutes 1 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h22 h24
  norm_num at h8 h22 h24
  linear_combination (1)*h8 + ((-1))*h22 + (π^2)*h24 + ((-1)*(f.M 1 0) + π^2*(f.M 1 1))*h6
include h6 ann in
theorem constraint_32_26_0_1 (f : HomData π 32 26) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π)*h8 + (π^4)*h25 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_32_26_1_1 (f : HomData π 32 26) : ρ ((f.M 3 2))=0 := by
  apply (ann _).mp
  have h12 := f.ambient_descent 3 0
  have h18 := f.source_descent 1 0
  have h20 := f.commutes 0 0
  have h21 := f.commutes 0 1
  have h22 := f.commutes 1 0
  have h27 := f.commutes 3 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h12 h18 h20 h21 h22 h27
  norm_num at h12 h18 h20 h21 h22 h27
  linear_combination (π)*h12 + (1)*h18 + ((-1)*π)*h20 + (π^2)*h21 + ((-1))*h22 + (π^4)*h27 + (π*(f.M 0 1) + (-1)*(f.M 0 2) + (-1)*(f.M 1 0) + π^2*(f.M 1 1) + (-1)*(f.U 0 1))*h6
include h6 ann in
theorem constraint_32_28_0_0 (f : HomData π 32 28) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h18 := f.source_descent 1 0
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h18 h20 h24
  norm_num at h8 h18 h20 h24
  linear_combination (1)*h8 + ((-1))*h18 + (π)*h20 + (π^2)*h24 + ((f.M 0 0) + (-1)*π*(f.M 0 1))*h6
include h6 ann in
theorem constraint_32_29_0_0 (f : HomData π 32 29) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h9 h24
  norm_num at h8 h9 h24
  linear_combination (1)*h8 + ((-1)*π^2)*h9 + (π^3)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_32_30_0_1 (f : HomData π 32 30) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π)*h8 + (π^3)*h25 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_32_31_0_1 (f : HomData π 32 31) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π)*h8 + (π^4)*h25 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_32_31_1_1 (f : HomData π 32 31) : ρ ((f.M 3 2) + (-1)*(f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h12 := f.ambient_descent 3 0
  have h18 := f.source_descent 1 0
  have h20 := f.commutes 0 0
  have h21 := f.commutes 0 1
  have h24 := f.commutes 2 0
  have h27 := f.commutes 3 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h12 h18 h20 h21 h24 h27
  norm_num at h8 h12 h18 h20 h21 h24 h27
  linear_combination ((-1))*h8 + (π)*h12 + (1)*h18 + ((-1))*h20 + (π^2)*h21 + ((-1)*π)*h24 + (π^4)*h27 + (π*(f.M 0 1) + (-1)*(f.M 0 2) + (-1)*(f.U 0 1))*h6
include h6 ann in
theorem constraint_32_32_0_1 (f : HomData π 32 32) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π)*h8 + (π^4)*h25 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_32_32_1_1 (f : HomData π 32 32) : ρ ((f.M 3 3) + (-1)*(f.M 2 2))=0 := by
  apply (ann _).mp
  have h1 := f.ambient_descent 0 1
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h12 := f.ambient_descent 3 0
  have h18 := f.source_descent 1 0
  have h20 := f.commutes 0 0
  have h21 := f.commutes 0 1
  have h24 := f.commutes 2 0
  have h27 := f.commutes 3 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h1 h8 h9 h12 h18 h20 h21 h24 h27
  norm_num at h1 h8 h9 h12 h18 h20 h21 h24 h27
  linear_combination (1)*h1 + ((-1))*h8 + (π)*h9 + (π)*h12 + (1)*h18 + ((-1)*π)*h20 + (π^2)*h21 + ((-1)*π^2)*h24 + (π^4)*h27 + (π*(f.M 0 2) + (-1)*(f.M 0 3) + (-1)*(f.U 0 1))*h6
include h6 ann in
theorem constraint_32_33_0_0 (f : HomData π 32 33) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h18 := f.source_descent 1 0
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h18 h20 h24
  norm_num at h8 h18 h20 h24
  linear_combination (1)*h8 + ((-1))*h18 + (1)*h20 + (π)*h24 + ((f.M 0 0) + (-1)*π*(f.M 0 1))*h6
include h6 ann in
theorem constraint_32_34_0_0 (f : HomData π 32 34) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h1 := f.ambient_descent 0 1
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h18 := f.source_descent 1 0
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h1 h8 h9 h18 h20 h24
  norm_num at h1 h8 h9 h18 h20 h24
  linear_combination ((-1))*h1 + (1)*h8 + ((-1)*π)*h9 + ((-1))*h18 + (π)*h20 + (π^2)*h24 + ((f.M 0 0) + (-1)*π*(f.M 0 2))*h6
include h6 ann in
theorem constraint_32_35_0_0 (f : HomData π 32 35) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h9 h24
  norm_num at h8 h9 h24
  linear_combination (1)*h8 + ((-1)*π)*h9 + (π^3)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_32_36_0_0 (f : HomData π 32 36) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h1 := f.ambient_descent 0 1
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h18 := f.source_descent 1 0
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h1 h8 h9 h18 h20 h24
  norm_num at h1 h8 h9 h18 h20 h24
  linear_combination ((-1))*h1 + (1)*h8 + ((-1)*π)*h9 + ((-1))*h18 + (π)*h20 + (π^2)*h24 + ((f.M 0 0) + (-1)*π*(f.M 0 2))*h6
include h6 ann in
theorem constraint_32_37_0_1 (f : HomData π 32 37) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π)*h8 + (π^3)*h25 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_32_37_1_1 (f : HomData π 32 37) : ρ ((f.M 3 2) + (-1)*(f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h12 := f.ambient_descent 3 0
  have h18 := f.source_descent 1 0
  have h20 := f.commutes 0 0
  have h21 := f.commutes 0 1
  have h23 := f.commutes 1 1
  have h24 := f.commutes 2 0
  have h27 := f.commutes 3 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h12 h18 h20 h21 h23 h24 h27
  norm_num at h8 h12 h18 h20 h21 h23 h24 h27
  linear_combination ((-1))*h8 + (π)*h12 + (1)*h18 + ((-1))*h20 + (π)*h21 + (1)*h23 + ((-1)*π)*h24 + (π^3)*h27 + (π*(f.M 0 1) + (-1)*(f.M 0 2) + (f.M 1 0) + (-1)*π*(f.M 1 2))*h6
include h6 ann in
theorem constraint_32_38_0_1 (f : HomData π 32 38) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π)*h8 + (π^3)*h25 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_32_38_1_1 (f : HomData π 32 38) : ρ ((f.M 3 3) + (-1)*(f.M 2 2))=0 := by
  apply (ann _).mp
  have h1 := f.ambient_descent 0 1
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h12 := f.ambient_descent 3 0
  have h18 := f.source_descent 1 0
  have h20 := f.commutes 0 0
  have h21 := f.commutes 0 1
  have h23 := f.commutes 1 1
  have h24 := f.commutes 2 0
  have h27 := f.commutes 3 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h1 h8 h9 h12 h18 h20 h21 h23 h24 h27
  norm_num at h1 h8 h9 h12 h18 h20 h21 h23 h24 h27
  linear_combination (1)*h1 + ((-1))*h8 + (π)*h9 + (π)*h12 + (1)*h18 + ((-1)*π)*h20 + (π)*h21 + (1)*h23 + ((-1)*π^2)*h24 + (π^3)*h27 + (π*(f.M 0 2) + (-1)*(f.M 0 3) + (f.M 1 0) + (-1)*π*(f.M 1 3))*h6
include h6 ann in
theorem constraint_32_39_0_0 (f : HomData π 32 39) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h22 := f.commutes 1 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h9 h22 h24
  norm_num at h8 h9 h22 h24
  linear_combination (1)*h8 + ((-1)*π)*h9 + ((-1))*h22 + (π^2)*h24 + ((-1)*(f.M 1 0) + (f.M 1 1) + π^2*(f.M 1 2))*h6
include h6 ann in
theorem constraint_32_39_0_1 (f : HomData π 32 39) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π)*h8 + (π^4)*h25 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_32_39_1_1 (f : HomData π 32 39) : ρ ((f.M 3 3))=0 := by
  apply (ann _).mp
  have h1 := f.ambient_descent 0 1
  have h12 := f.ambient_descent 3 0
  have h18 := f.source_descent 1 0
  have h20 := f.commutes 0 0
  have h21 := f.commutes 0 1
  have h22 := f.commutes 1 0
  have h27 := f.commutes 3 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h1 h12 h18 h20 h21 h22 h27
  norm_num at h1 h12 h18 h20 h21 h22 h27
  linear_combination (1)*h1 + (π)*h12 + (1)*h18 + ((-1)*π)*h20 + (π^2)*h21 + ((-1))*h22 + (π^4)*h27 + (π*(f.M 0 2) + (-1)*(f.M 0 3) + (-1)*(f.M 1 0) + (f.M 1 1) + π^2*(f.M 1 2) + (-1)*(f.U 0 1))*h6
include h6 ann in
theorem constraint_32_40_0_1 (f : HomData π 32 40) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h9 h25
  norm_num at h8 h9 h25
  linear_combination (π)*h8 + ((-1)*π^2)*h9 + (π^3)*h25 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_32_41_0_0 (f : HomData π 32 41) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h1 := f.ambient_descent 0 1
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h18 := f.source_descent 1 0
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h1 h8 h9 h18 h20 h24
  norm_num at h1 h8 h9 h18 h20 h24
  linear_combination ((-1))*h1 + (1)*h8 + ((-1)*π)*h9 + ((-1))*h18 + (π)*h20 + (π^2)*h24 + ((f.M 0 0) + (-1)*π*(f.M 0 2))*h6
include h6 ann in
theorem constraint_32_41_0_1 (f : HomData π 32 41) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h9 h25
  norm_num at h8 h9 h25
  linear_combination (π)*h8 + ((-1)*π^2)*h9 + (π^4)*h25 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_32_41_1_1 (f : HomData π 32 41) : ρ ((f.M 3 3))=0 := by
  apply (ann _).mp
  have h1 := f.ambient_descent 0 1
  have h12 := f.ambient_descent 3 0
  have h13 := f.ambient_descent 3 1
  have h21 := f.commutes 0 1
  have h27 := f.commutes 3 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h1 h12 h13 h21 h27
  norm_num at h1 h12 h13 h21 h27
  linear_combination ((-1))*h1 + (π)*h12 + ((-1)*π^2)*h13 + (π^2)*h21 + (π^4)*h27 + ((f.M 0 0) + (-1)*(f.M 0 3) + (-1)*(f.U 0 1))*h6
include h6 ann in
theorem constraint_32_42_0_1 (f : HomData π 32 42) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h9 h25
  norm_num at h8 h9 h25
  linear_combination (π)*h8 + ((-1)*π)*h9 + (π^3)*h25 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_32_43_0_0 (f : HomData π 32 43) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h18 := f.source_descent 1 0
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h18 h20 h24
  norm_num at h8 h18 h20 h24
  linear_combination (1)*h8 + ((-1))*h18 + (π)*h20 + (π^2)*h24 + ((f.M 0 0) + (-1)*π*(f.M 0 2))*h6
include h6 ann in
theorem constraint_32_43_0_1 (f : HomData π 32 43) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h9 h25
  norm_num at h8 h9 h25
  linear_combination (1)*h8 + ((-1)*π)*h9 + (π^3)*h25 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_32_44_0_1 (f : HomData π 32 44) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h9 h25
  norm_num at h8 h9 h25
  linear_combination (1)*h8 + ((-1)*π)*h9 + (π^3)*h25 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_32_46_0_0 (f : HomData π 32 46) : ρ ((f.M 2 0))=0 := by
  apply (ann _).mp
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h24
  norm_num at h24
  linear_combination (π^5)*h24 + (π^2*(f.U 0 0))*h6
include h6 ann in
theorem constraint_32_46_1_0 (f : HomData π 32 46) : ρ ((f.M 3 0))=0 := by
  apply (ann _).mp
  have h26 := f.commutes 3 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h26
  norm_num at h26
  linear_combination (π^5)*h26 + ((f.U 1 0))*h6
end UniserialComputations.N6
