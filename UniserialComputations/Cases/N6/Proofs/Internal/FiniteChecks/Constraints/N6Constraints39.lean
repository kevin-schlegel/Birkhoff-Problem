import N6Matrix
noncomputable section
namespace UniserialComputations.N6
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
variable {R k : Type*} [CommRing R] [Field k] (π : R) (ρ : R →+* k)
variable (h6 : π^6=0) (ann : ∀ r, π^5*r=0 ↔ ρ r=0)
include h6 ann in
theorem constraint_39_0_0_0 (f : HomData π 39 0) : ρ ((f.M 2 0))=0 := by
  apply (ann _).mp
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h24
  norm_num at h24
  linear_combination (π^4)*h24 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_39_0_1_0 (f : HomData π 39 0) : ρ ((f.M 3 0))=0 := by
  apply (ann _).mp
  have h20 := f.commutes 0 0
  have h26 := f.commutes 3 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h20 h26
  norm_num at h20 h26
  linear_combination (π^2)*h20 + (π^4)*h26 + ((-1)*(f.M 0 0) + (-1)*(f.U 0 0))*h6
include h6 ann in
theorem constraint_39_1_0_0 (f : HomData π 39 1) : ρ ((f.M 2 0))=0 := by
  apply (ann _).mp
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h24
  norm_num at h24
  linear_combination (π^3)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_39_1_1_0 (f : HomData π 39 1) : ρ ((f.M 3 0))=0 := by
  apply (ann _).mp
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  have h26 := f.commutes 3 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h20 h22 h26
  norm_num at h20 h22 h26
  linear_combination (π)*h20 + (1)*h22 + (π^3)*h26 + ((-1)*(f.M 0 0) + (-1)*(f.M 1 0))*h6
include h6 ann in
theorem constraint_39_2_0_0 (f : HomData π 39 2) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (π^3)*h8 + (π^4)*h24 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_39_2_1_0 (f : HomData π 39 2) : ρ ((f.M 3 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h12 := f.ambient_descent 3 0
  have h20 := f.commutes 0 0
  have h26 := f.commutes 3 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h12 h20 h26
  norm_num at h0 h12 h20 h26
  linear_combination (π)*h0 + (π^3)*h12 + (π^2)*h20 + (π^4)*h26 + ((-1)*(f.M 0 1) + (-1)*(f.U 0 0))*h6
include h6 ann in
theorem constraint_39_3_0_0 (f : HomData π 39 3) : ρ ((f.M 2 0))=0 := by
  apply (ann _).mp
  have h18 := f.source_descent 1 0
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h18 h20 h24
  norm_num at h18 h20 h24
  linear_combination ((-1))*h18 + (π)*h20 + (π^2)*h24 + ((-1)*π*(f.M 0 0))*h6
include h6 ann in
theorem constraint_39_4_0_0 (f : HomData π 39 4) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (π^2)*h8 + (π^3)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_39_5_0_0 (f : HomData π 39 5) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (π^2)*h8 + (π^4)*h24 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_39_5_1_0 (f : HomData π 39 5) : ρ ((f.M 3 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h12 := f.ambient_descent 3 0
  have h20 := f.commutes 0 0
  have h26 := f.commutes 3 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h12 h20 h26
  norm_num at h0 h12 h20 h26
  linear_combination (1)*h0 + (π^2)*h12 + (π^2)*h20 + (π^4)*h26 + ((-1)*(f.M 0 1) + (-1)*(f.U 0 0))*h6
include h6 ann in
theorem constraint_39_6_0_0 (f : HomData π 39 6) : ρ ((f.M 2 0))=0 := by
  apply (ann _).mp
  have h18 := f.source_descent 1 0
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h18 h20 h24
  norm_num at h18 h20 h24
  linear_combination ((-1))*h18 + (1)*h20 + (π)*h24 + ((-1)*π*(f.M 0 0))*h6
include h6 ann in
theorem constraint_39_7_0_0 (f : HomData π 39 7) : ρ ((f.M 2 1))=0 := by
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
theorem constraint_39_8_0_0 (f : HomData π 39 8) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (π)*h8 + (π^3)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_39_9_0_0 (f : HomData π 39 9) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (π)*h8 + (π^4)*h24 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_39_13_0_0 (f : HomData π 39 13) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (1)*h8 + (π^3)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_39_14_0_0 (f : HomData π 39 14) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (1)*h8 + (π^4)*h24 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_39_15_0_0 (f : HomData π 39 15) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (π^2)*h8 + (π^3)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_39_16_0_0 (f : HomData π 39 16) : ρ ((f.M 2 1))=0 := by
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
theorem constraint_39_17_0_0 (f : HomData π 39 17) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (π)*h8 + (π^3)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_39_18_0_0 (f : HomData π 39 18) : ρ ((f.M 2 1))=0 := by
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
theorem constraint_39_18_0_1 (f : HomData π 39 18) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π^2)*h8 + (π^4)*h25 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_39_18_1_1 (f : HomData π 39 18) : ρ ((f.M 3 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h12 := f.ambient_descent 3 0
  have h21 := f.commutes 0 1
  have h27 := f.commutes 3 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h12 h21 h27
  norm_num at h0 h12 h21 h27
  linear_combination (1)*h0 + (π^2)*h12 + (π^2)*h21 + (π^4)*h27 + ((-1)*(f.M 0 2) + (-1)*(f.U 0 1))*h6
include h6 ann in
theorem constraint_39_19_0_0 (f : HomData π 39 19) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h18 := f.source_descent 1 0
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h18 h20 h24
  norm_num at h8 h18 h20 h24
  linear_combination (π)*h8 + ((-1))*h18 + (π)*h20 + (π^2)*h24 + ((f.M 0 0) + (-1)*π*(f.M 0 1))*h6
include h6 ann in
theorem constraint_39_20_0_0 (f : HomData π 39 20) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h9 h24
  norm_num at h8 h9 h24
  linear_combination (π)*h8 + ((-1)*π^2)*h9 + (π^3)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_39_23_0_0 (f : HomData π 39 23) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (1)*h8 + (π^3)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_39_24_0_1 (f : HomData π 39 24) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π^2)*h8 + (π^4)*h25 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_39_24_1_1 (f : HomData π 39 24) : ρ ((f.M 3 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h12 := f.ambient_descent 3 0
  have h21 := f.commutes 0 1
  have h27 := f.commutes 3 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h12 h21 h27
  norm_num at h0 h12 h21 h27
  linear_combination (1)*h0 + (π^2)*h12 + (π^2)*h21 + (π^4)*h27 + ((-1)*(f.M 0 2) + (-1)*(f.U 0 1))*h6
include h6 ann in
theorem constraint_39_26_0_0 (f : HomData π 39 26) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h22 := f.commutes 1 0
  have h23 := f.commutes 1 1
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h22 h23 h24
  norm_num at h8 h22 h23 h24
  linear_combination (1)*h8 + ((-1))*h22 + (π)*h23 + (π^2)*h24 + (π*(f.M 1 1) + (-1)*(f.M 1 2) + (f.U 0 1))*h6
include h6 ann in
theorem constraint_39_26_0_1 (f : HomData π 39 26) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π)*h8 + (π^4)*h25 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_39_26_1_1 (f : HomData π 39 26) : ρ ((f.M 3 2))=0 := by
  apply (ann _).mp
  have h12 := f.ambient_descent 3 0
  have h18 := f.source_descent 1 0
  have h20 := f.commutes 0 0
  have h21 := f.commutes 0 1
  have h22 := f.commutes 1 0
  have h23 := f.commutes 1 1
  have h27 := f.commutes 3 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h12 h18 h20 h21 h22 h23 h27
  norm_num at h12 h18 h20 h21 h22 h23 h27
  linear_combination (π)*h12 + (1)*h18 + ((-1)*π)*h20 + (π^2)*h21 + ((-1))*h22 + (π)*h23 + (π^4)*h27 + (π*(f.M 0 1) + (-1)*(f.M 0 2) + π*(f.M 1 1) + (-1)*(f.M 1 2))*h6
include h6 ann in
theorem constraint_39_28_0_0 (f : HomData π 39 28) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h18 := f.source_descent 1 0
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h18 h20 h24
  norm_num at h8 h18 h20 h24
  linear_combination (1)*h8 + ((-1))*h18 + (π)*h20 + (π^2)*h24 + ((f.M 0 0) + (-1)*π*(f.M 0 1))*h6
include h6 ann in
theorem constraint_39_29_0_0 (f : HomData π 39 29) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h9 h24
  norm_num at h8 h9 h24
  linear_combination (1)*h8 + ((-1)*π^2)*h9 + (π^3)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_39_30_0_1 (f : HomData π 39 30) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π)*h8 + (π^3)*h25 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_39_31_0_1 (f : HomData π 39 31) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π)*h8 + (π^4)*h25 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_39_31_1_1 (f : HomData π 39 31) : ρ ((f.M 3 2) + (-1)*(f.M 2 1))=0 := by
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
theorem constraint_39_32_0_1 (f : HomData π 39 32) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π)*h8 + (π^4)*h25 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_39_32_1_1 (f : HomData π 39 32) : ρ ((f.M 3 3) + (-1)*(f.M 2 2))=0 := by
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
theorem constraint_39_33_0_0 (f : HomData π 39 33) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h18 := f.source_descent 1 0
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h18 h20 h24
  norm_num at h8 h18 h20 h24
  linear_combination (1)*h8 + ((-1))*h18 + (1)*h20 + (π)*h24 + ((f.M 0 0) + (-1)*π*(f.M 0 1))*h6
include h6 ann in
theorem constraint_39_34_0_0 (f : HomData π 39 34) : ρ ((f.M 2 2))=0 := by
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
theorem constraint_39_35_0_0 (f : HomData π 39 35) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h9 h24
  norm_num at h8 h9 h24
  linear_combination (1)*h8 + ((-1)*π)*h9 + (π^3)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_39_36_0_0 (f : HomData π 39 36) : ρ ((f.M 2 2))=0 := by
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
theorem constraint_39_37_0_1 (f : HomData π 39 37) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π)*h8 + (π^3)*h25 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_39_38_0_1 (f : HomData π 39 38) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π)*h8 + (π^3)*h25 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_39_39_0_1 (f : HomData π 39 39) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π)*h8 + (π^4)*h25 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_39_39_1_1 (f : HomData π 39 39) : ρ ((f.M 3 3) + (-1)*(f.M 2 2))=0 := by
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
theorem constraint_39_40_0_1 (f : HomData π 39 40) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h9 h25
  norm_num at h8 h9 h25
  linear_combination (π)*h8 + ((-1)*π^2)*h9 + (π^3)*h25 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_39_41_0_0 (f : HomData π 39 41) : ρ ((f.M 2 2))=0 := by
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
theorem constraint_39_41_0_1 (f : HomData π 39 41) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h9 h25
  norm_num at h8 h9 h25
  linear_combination (π)*h8 + ((-1)*π^2)*h9 + (π^4)*h25 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_39_41_1_1 (f : HomData π 39 41) : ρ ((f.M 3 3))=0 := by
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
theorem constraint_39_42_0_1 (f : HomData π 39 42) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h9 h25
  norm_num at h8 h9 h25
  linear_combination (π)*h8 + ((-1)*π)*h9 + (π^3)*h25 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_39_43_0_0 (f : HomData π 39 43) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h18 := f.source_descent 1 0
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h18 h20 h24
  norm_num at h8 h18 h20 h24
  linear_combination (1)*h8 + ((-1))*h18 + (π)*h20 + (π^2)*h24 + ((f.M 0 0) + (-1)*π*(f.M 0 2))*h6
include h6 ann in
theorem constraint_39_43_0_1 (f : HomData π 39 43) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h9 h25
  norm_num at h8 h9 h25
  linear_combination (1)*h8 + ((-1)*π)*h9 + (π^3)*h25 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_39_44_0_1 (f : HomData π 39 44) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h9 h25
  norm_num at h8 h9 h25
  linear_combination (1)*h8 + ((-1)*π)*h9 + (π^3)*h25 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_39_46_0_0 (f : HomData π 39 46) : ρ ((f.M 2 0))=0 := by
  apply (ann _).mp
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h24
  norm_num at h24
  linear_combination (π^5)*h24 + (π^2*(f.U 0 0))*h6
include h6 ann in
theorem constraint_39_46_1_0 (f : HomData π 39 46) : ρ ((f.M 3 0))=0 := by
  apply (ann _).mp
  have h26 := f.commutes 3 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h26
  norm_num at h26
  linear_combination (π^5)*h26 + ((f.U 1 0))*h6
end UniserialComputations.N6
