import N6Matrix
noncomputable section
namespace UniserialComputations.N6
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
variable {R k : Type*} [CommRing R] [Field k] (π : R) (ρ : R →+* k)
variable (h6 : π^6=0) (ann : ∀ r, π^5*r=0 ↔ ρ r=0)
include h6 ann in
theorem constraint_5_0_0_0 (f : HomData π 5 0) : ρ ((f.M 1 0))=0 := by
  apply (ann _).mp
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h20 h22
  norm_num at h20 h22
  linear_combination (π)*h20 + (π^4)*h22 + ((-1)*(f.M 0 0))*h6
include h6 ann in
theorem constraint_5_1_0_0 (f : HomData π 5 1) : ρ ((f.M 1 0))=0 := by
  apply (ann _).mp
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h20 h22
  norm_num at h20 h22
  linear_combination (1)*h20 + (π^3)*h22 + ((-1)*(f.M 0 0))*h6
include h6 ann in
theorem constraint_5_2_0_0 (f : HomData π 5 2) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h4 := f.ambient_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h4 h20 h22
  norm_num at h0 h4 h20 h22
  linear_combination (1)*h0 + (π^3)*h4 + (π)*h20 + (π^4)*h22 + ((-1)*(f.M 0 1))*h6
include h6 ann in
theorem constraint_5_18_0_1 (f : HomData π 5 18) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h16 := f.source_descent 0 0
  have h20 := f.commutes 0 0
  have h21 := f.commutes 0 1
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h16 h20 h21 h23
  norm_num at h4 h16 h20 h21 h23
  linear_combination (π^2)*h4 + (1)*h16 + ((-1))*h20 + (π)*h21 + (π^4)*h23 + (π*(f.M 0 1) + (-1)*(f.M 0 2))*h6
include h6 ann in
theorem constraint_5_24_0_1 (f : HomData π 5 24) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h16 := f.source_descent 0 0
  have h20 := f.commutes 0 0
  have h21 := f.commutes 0 1
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h16 h20 h21 h23
  norm_num at h4 h16 h20 h21 h23
  linear_combination (π^2)*h4 + (π)*h16 + ((-1))*h20 + (π)*h21 + (π^4)*h23 + (π^2*(f.M 0 1) + (-1)*(f.M 0 2))*h6
include h6 ann in
theorem constraint_5_26_0_1 (f : HomData π 5 26) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h16 := f.source_descent 0 0
  have h20 := f.commutes 0 0
  have h21 := f.commutes 0 1
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h16 h20 h21 h23
  norm_num at h4 h16 h20 h21 h23
  linear_combination (π)*h4 + (1)*h16 + ((-1))*h20 + (π)*h21 + (π^4)*h23 + (π*(f.M 0 1) + (-1)*(f.M 0 2))*h6
include h6 ann in
theorem constraint_5_41_0_1 (f : HomData π 5 41) : ρ ((f.M 1 3))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h16 := f.source_descent 0 0
  have h20 := f.commutes 0 0
  have h21 := f.commutes 0 1
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h16 h20 h21 h23
  norm_num at h4 h5 h16 h20 h21 h23
  linear_combination (π)*h4 + ((-1)*π^2)*h5 + (1)*h16 + ((-1))*h20 + (π)*h21 + (π^4)*h23 + (π*(f.M 0 2) + (-1)*(f.M 0 3))*h6
include h6 ann in
theorem constraint_5_46_0_0 (f : HomData π 5 46) : ρ ((f.M 1 0))=0 := by
  apply (ann _).mp
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h22
  norm_num at h22
  linear_combination (π^5)*h22 + ((f.U 0 0))*h6
end UniserialComputations.N6
