import N6Matrix
noncomputable section
namespace UniserialComputations.N6
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
variable {R k : Type*} [CommRing R] [Field k] (π : R) (ρ : R →+* k)
variable (h6 : π^6=0) (ann : ∀ r, π^5*r=0 ↔ ρ r=0)
include h6 ann in
theorem constraint_29_0_0_0 (f : HomData π 29 0) : ρ ((f.M 2 0))=0 := by
  apply (ann _).mp
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h24
  norm_num at h24
  linear_combination (π^4)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_29_1_0_0 (f : HomData π 29 1) : ρ ((f.M 2 0))=0 := by
  apply (ann _).mp
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h20 h24
  norm_num at h20 h24
  linear_combination (π^2)*h20 + (π^3)*h24 + ((-1)*(f.M 0 0))*h6
include h6 ann in
theorem constraint_29_2_0_0 (f : HomData π 29 2) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (π^3)*h8 + (π^4)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_29_3_0_0 (f : HomData π 29 3) : ρ ((f.M 2 0))=0 := by
  apply (ann _).mp
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h20 h24
  norm_num at h20 h24
  linear_combination (π)*h20 + (π^2)*h24 + ((-1)*(f.M 0 0))*h6
include h6 ann in
theorem constraint_29_4_0_0 (f : HomData π 29 4) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h8 := f.ambient_descent 2 0
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h8 h20 h24
  norm_num at h0 h8 h20 h24
  linear_combination (π)*h0 + (π^2)*h8 + (π^2)*h20 + (π^3)*h24 + ((-1)*(f.M 0 1))*h6
include h6 ann in
theorem constraint_29_5_0_0 (f : HomData π 29 5) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (π^2)*h8 + (π^4)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_29_6_0_0 (f : HomData π 29 6) : ρ ((f.M 2 0))=0 := by
  apply (ann _).mp
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h20 h24
  norm_num at h20 h24
  linear_combination (1)*h20 + (π)*h24 + ((-1)*(f.M 0 0))*h6
include h6 ann in
theorem constraint_29_7_0_0 (f : HomData π 29 7) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h8 := f.ambient_descent 2 0
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h8 h20 h24
  norm_num at h0 h8 h20 h24
  linear_combination (1)*h0 + (π)*h8 + (π)*h20 + (π^2)*h24 + ((-1)*(f.M 0 1))*h6
include h6 ann in
theorem constraint_29_8_0_0 (f : HomData π 29 8) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h8 := f.ambient_descent 2 0
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h8 h20 h24
  norm_num at h0 h8 h20 h24
  linear_combination (1)*h0 + (π)*h8 + (π^2)*h20 + (π^3)*h24 + ((-1)*(f.M 0 1))*h6
include h6 ann in
theorem constraint_29_9_0_0 (f : HomData π 29 9) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (π)*h8 + (π^4)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_29_14_0_0 (f : HomData π 29 14) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (1)*h8 + (π^4)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_29_15_0_0 (f : HomData π 29 15) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h8 := f.ambient_descent 2 0
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h8 h20 h24
  norm_num at h0 h8 h20 h24
  linear_combination (π)*h0 + (π^2)*h8 + (π^2)*h20 + (π^3)*h24 + ((-1)*(f.M 0 1))*h6
include h6 ann in
theorem constraint_29_16_0_0 (f : HomData π 29 16) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h8 := f.ambient_descent 2 0
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h8 h20 h24
  norm_num at h0 h8 h20 h24
  linear_combination (1)*h0 + (π)*h8 + (π)*h20 + (π^2)*h24 + ((-1)*(f.M 0 1))*h6
include h6 ann in
theorem constraint_29_17_0_0 (f : HomData π 29 17) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h8 := f.ambient_descent 2 0
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h8 h20 h24
  norm_num at h0 h8 h20 h24
  linear_combination (1)*h0 + (π)*h8 + (π^2)*h20 + (π^3)*h24 + ((-1)*(f.M 0 1))*h6
include h6 ann in
theorem constraint_29_18_0_0 (f : HomData π 29 18) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h8 := f.ambient_descent 2 0
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h8 h20 h24
  norm_num at h0 h8 h20 h24
  linear_combination (1)*h0 + (π)*h8 + (π)*h20 + (π^2)*h24 + ((-1)*(f.M 0 1))*h6
include h6 ann in
theorem constraint_29_18_0_1 (f : HomData π 29 18) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π^2)*h8 + (π^4)*h25 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_29_19_0_0 (f : HomData π 29 19) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h8 := f.ambient_descent 2 0
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h8 h20 h24
  norm_num at h0 h8 h20 h24
  linear_combination (1)*h0 + (π)*h8 + (π)*h20 + (π^2)*h24 + ((-1)*(f.M 0 1))*h6
include h6 ann in
theorem constraint_29_20_0_0 (f : HomData π 29 20) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h8 h9 h20 h24
  norm_num at h0 h1 h8 h9 h20 h24
  linear_combination (1)*h0 + ((-1)*π)*h1 + (π)*h8 + ((-1)*π^2)*h9 + (π^2)*h20 + (π^3)*h24 + ((-1)*(f.M 0 2))*h6
include h6 ann in
theorem constraint_29_23_0_0 (f : HomData π 29 23) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h22 := f.commutes 1 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h22 h24
  norm_num at h8 h22 h24
  linear_combination (1)*h8 + ((-1))*h22 + (π^3)*h24 + ((-1)*(f.M 1 0) + π*(f.M 1 1))*h6
include h6 ann in
theorem constraint_29_24_0_1 (f : HomData π 29 24) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π^2)*h8 + (π^4)*h25 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_29_26_0_1 (f : HomData π 29 26) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π)*h8 + (π^4)*h25 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_29_30_0_1 (f : HomData π 29 30) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h8 := f.ambient_descent 2 0
  have h21 := f.commutes 0 1
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h8 h21 h25
  norm_num at h0 h8 h21 h25
  linear_combination (1)*h0 + (π)*h8 + (π^2)*h21 + (π^3)*h25 + ((-1)*(f.M 0 2))*h6
include h6 ann in
theorem constraint_29_31_0_1 (f : HomData π 29 31) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π)*h8 + (π^4)*h25 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_29_32_0_1 (f : HomData π 29 32) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π)*h8 + (π^4)*h25 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_29_37_0_1 (f : HomData π 29 37) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h8 := f.ambient_descent 2 0
  have h21 := f.commutes 0 1
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h8 h21 h25
  norm_num at h0 h8 h21 h25
  linear_combination (1)*h0 + (π)*h8 + (π^2)*h21 + (π^3)*h25 + ((-1)*(f.M 0 2))*h6
include h6 ann in
theorem constraint_29_38_0_1 (f : HomData π 29 38) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h8 := f.ambient_descent 2 0
  have h21 := f.commutes 0 1
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h8 h21 h25
  norm_num at h0 h8 h21 h25
  linear_combination (1)*h0 + (π)*h8 + (π^2)*h21 + (π^3)*h25 + ((-1)*(f.M 0 3))*h6
include h6 ann in
theorem constraint_29_39_0_1 (f : HomData π 29 39) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π)*h8 + (π^4)*h25 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_29_40_0_1 (f : HomData π 29 40) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h21 := f.commutes 0 1
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h8 h9 h21 h25
  norm_num at h0 h1 h8 h9 h21 h25
  linear_combination (1)*h0 + ((-1)*π)*h1 + (π)*h8 + ((-1)*π^2)*h9 + (π^2)*h21 + (π^3)*h25 + ((-1)*(f.M 0 3))*h6
include h6 ann in
theorem constraint_29_41_0_1 (f : HomData π 29 41) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h9 h25
  norm_num at h8 h9 h25
  linear_combination (π)*h8 + ((-1)*π^2)*h9 + (π^4)*h25 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_29_42_0_1 (f : HomData π 29 42) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h21 := f.commutes 0 1
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h8 h9 h21 h25
  norm_num at h0 h1 h8 h9 h21 h25
  linear_combination (1)*h0 + ((-1))*h1 + (π)*h8 + ((-1)*π)*h9 + (π^2)*h21 + (π^3)*h25 + ((-1)*(f.M 0 3))*h6
include h6 ann in
theorem constraint_29_43_0_1 (f : HomData π 29 43) : ρ ((f.M 2 3) + (-1)*(f.M 2 2))=0 := by
  apply (ann _).mp
  have h1 := f.ambient_descent 0 1
  have h9 := f.ambient_descent 2 1
  have h20 := f.commutes 0 0
  have h21 := f.commutes 0 1
  have h24 := f.commutes 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h1 h9 h20 h21 h24 h25
  norm_num at h1 h9 h20 h21 h24 h25
  linear_combination ((-1))*h1 + ((-1)*π)*h9 + ((-1)*π)*h20 + (π^2)*h21 + ((-1)*π^2)*h24 + (π^3)*h25 + ((f.M 0 2) + (-1)*(f.M 0 3))*h6
include h6 ann in
theorem constraint_29_46_0_0 (f : HomData π 29 46) : ρ ((f.M 2 0))=0 := by
  apply (ann _).mp
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h24
  norm_num at h24
  linear_combination (π^5)*h24 + (π*(f.U 0 0))*h6
end UniserialComputations.N6
