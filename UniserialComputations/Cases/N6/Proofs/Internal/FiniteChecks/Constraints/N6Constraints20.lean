import N6Matrix
noncomputable section
namespace UniserialComputations.N6
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
variable {R k : Type*} [CommRing R] [Field k] (π : R) (ρ : R →+* k)
variable (h6 : π^6=0) (ann : ∀ r, π^5*r=0 ↔ ρ r=0)
include h6 ann in
theorem constraint_20_0_0_0 (f : HomData π 20 0) : ρ ((f.M 2 0))=0 := by
  apply (ann _).mp
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h24
  norm_num at h24
  linear_combination (π^4)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_20_1_0_0 (f : HomData π 20 1) : ρ ((f.M 2 0))=0 := by
  apply (ann _).mp
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h20 h24
  norm_num at h20 h24
  linear_combination (π)*h20 + (π^3)*h24 + ((-1)*(f.M 0 0))*h6
include h6 ann in
theorem constraint_20_2_0_0 (f : HomData π 20 2) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (π^3)*h8 + (π^4)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_20_3_0_0 (f : HomData π 20 3) : ρ ((f.M 2 0))=0 := by
  apply (ann _).mp
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h20 h24
  norm_num at h20 h24
  linear_combination (1)*h20 + (π^2)*h24 + ((-1)*(f.M 0 0))*h6
include h6 ann in
theorem constraint_20_4_0_0 (f : HomData π 20 4) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h8 := f.ambient_descent 2 0
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h8 h20 h24
  norm_num at h0 h8 h20 h24
  linear_combination (1)*h0 + (π^2)*h8 + (π)*h20 + (π^3)*h24 + ((-1)*(f.M 0 1))*h6
include h6 ann in
theorem constraint_20_5_0_0 (f : HomData π 20 5) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (π^2)*h8 + (π^4)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_20_9_0_0 (f : HomData π 20 9) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (π)*h8 + (π^4)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_20_14_0_0 (f : HomData π 20 14) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (1)*h8 + (π^4)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_20_15_0_0 (f : HomData π 20 15) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h8 := f.ambient_descent 2 0
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h8 h20 h24
  norm_num at h0 h8 h20 h24
  linear_combination (1)*h0 + (π^2)*h8 + (π)*h20 + (π^3)*h24 + ((-1)*(f.M 0 1))*h6
include h6 ann in
theorem constraint_20_17_0_0 (f : HomData π 20 17) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h22 := f.commutes 1 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h22 h24
  norm_num at h8 h22 h24
  linear_combination (π)*h8 + ((-1))*h22 + (π^3)*h24 + ((-1)*(f.M 1 0) + π*(f.M 1 1))*h6
include h6 ann in
theorem constraint_20_18_0_1 (f : HomData π 20 18) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π^2)*h8 + (π^4)*h25 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_20_23_0_0 (f : HomData π 20 23) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h22 := f.commutes 1 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h22 h24
  norm_num at h8 h22 h24
  linear_combination (1)*h8 + ((-1))*h22 + (π^3)*h24 + ((-1)*(f.M 1 0) + π*(f.M 1 1))*h6
include h6 ann in
theorem constraint_20_24_0_1 (f : HomData π 20 24) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π^2)*h8 + (π^4)*h25 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_20_26_0_1 (f : HomData π 20 26) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π)*h8 + (π^4)*h25 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_20_30_0_1 (f : HomData π 20 30) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h16 := f.source_descent 0 0
  have h20 := f.commutes 0 0
  have h21 := f.commutes 0 1
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h16 h20 h21 h25
  norm_num at h8 h16 h20 h21 h25
  linear_combination (π)*h8 + (1)*h16 + ((-1))*h20 + (π)*h21 + (π^3)*h25 + (π*(f.M 0 1) + (-1)*(f.M 0 2))*h6
include h6 ann in
theorem constraint_20_31_0_1 (f : HomData π 20 31) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π)*h8 + (π^4)*h25 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_20_32_0_1 (f : HomData π 20 32) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π)*h8 + (π^4)*h25 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_20_37_0_1 (f : HomData π 20 37) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h16 := f.source_descent 0 0
  have h20 := f.commutes 0 0
  have h21 := f.commutes 0 1
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h16 h20 h21 h25
  norm_num at h8 h16 h20 h21 h25
  linear_combination (π)*h8 + (1)*h16 + ((-1))*h20 + (π)*h21 + (π^3)*h25 + (π*(f.M 0 1) + (-1)*(f.M 0 2))*h6
include h6 ann in
theorem constraint_20_38_0_1 (f : HomData π 20 38) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h1 := f.ambient_descent 0 1
  have h8 := f.ambient_descent 2 0
  have h16 := f.source_descent 0 0
  have h20 := f.commutes 0 0
  have h21 := f.commutes 0 1
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h1 h8 h16 h20 h21 h25
  norm_num at h1 h8 h16 h20 h21 h25
  linear_combination (1)*h1 + (π)*h8 + (1)*h16 + ((-1)*π)*h20 + (π)*h21 + (π^3)*h25 + (π*(f.M 0 2) + (-1)*(f.M 0 3))*h6
include h6 ann in
theorem constraint_20_39_0_1 (f : HomData π 20 39) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π)*h8 + (π^4)*h25 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_20_40_0_1 (f : HomData π 20 40) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h1 := f.ambient_descent 0 1
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h16 := f.source_descent 0 0
  have h20 := f.commutes 0 0
  have h21 := f.commutes 0 1
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h1 h8 h9 h16 h20 h21 h25
  norm_num at h1 h8 h9 h16 h20 h21 h25
  linear_combination ((-1))*h1 + (π)*h8 + ((-1)*π^2)*h9 + (1)*h16 + ((-1))*h20 + (π)*h21 + (π^3)*h25 + (π*(f.M 0 2) + (-1)*(f.M 0 3))*h6
include h6 ann in
theorem constraint_20_41_0_1 (f : HomData π 20 41) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h9 h25
  norm_num at h8 h9 h25
  linear_combination (π)*h8 + ((-1)*π^2)*h9 + (π^4)*h25 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_20_46_0_0 (f : HomData π 20 46) : ρ ((f.M 2 0))=0 := by
  apply (ann _).mp
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h24
  norm_num at h24
  linear_combination (π^5)*h24 + (π*(f.U 0 0))*h6
end UniserialComputations.N6
