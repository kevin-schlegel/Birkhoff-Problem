import N6Matrix
noncomputable section
namespace UniserialComputations.N6
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
variable {R k : Type*} [CommRing R] [Field k] (π : R) (ρ : R →+* k)
variable (h6 : π^6=0) (ann : ∀ r, π^5*r=0 ↔ ρ r=0)
include h6 ann in
theorem constraint_3_0_0_0 (f : HomData π 3 0) : ρ ((f.M 0 0))=0 := by
  apply (ann _).mp
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h20
  norm_num at h20
  linear_combination (π^4)*h20 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_3_1_0_0 (f : HomData π 3 1) : ρ ((f.M 0 0))=0 := by
  apply (ann _).mp
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h20
  norm_num at h20
  linear_combination (π^3)*h20 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_3_2_0_0 (f : HomData π 3 2) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (π^3)*h0 + (π^4)*h20 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_3_4_0_0 (f : HomData π 3 4) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (π^2)*h0 + (π^3)*h20 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_3_5_0_0 (f : HomData π 3 5) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (π^2)*h0 + (π^4)*h20 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_3_8_0_0 (f : HomData π 3 8) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (π)*h0 + (π^3)*h20 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_3_9_0_0 (f : HomData π 3 9) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (π)*h0 + (π^4)*h20 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_3_13_0_0 (f : HomData π 3 13) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (1)*h0 + (π^3)*h20 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_3_14_0_0 (f : HomData π 3 14) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (1)*h0 + (π^4)*h20 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_3_15_0_0 (f : HomData π 3 15) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (π^2)*h0 + (π^3)*h20 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_3_17_0_0 (f : HomData π 3 17) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (π)*h0 + (π^3)*h20 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_3_18_0_1 (f : HomData π 3 18) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h21
  norm_num at h0 h21
  linear_combination (π^2)*h0 + (π^4)*h21 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_3_20_0_0 (f : HomData π 3 20) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h20
  norm_num at h0 h1 h20
  linear_combination (π)*h0 + ((-1)*π^2)*h1 + (π^3)*h20 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_3_23_0_0 (f : HomData π 3 23) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (1)*h0 + (π^3)*h20 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_3_24_0_1 (f : HomData π 3 24) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h21
  norm_num at h0 h21
  linear_combination (π^2)*h0 + (π^4)*h21 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_3_26_0_1 (f : HomData π 3 26) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h21
  norm_num at h0 h21
  linear_combination (π)*h0 + (π^4)*h21 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_3_29_0_0 (f : HomData π 3 29) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h20
  norm_num at h0 h1 h20
  linear_combination (1)*h0 + ((-1)*π^2)*h1 + (π^3)*h20 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_3_30_0_1 (f : HomData π 3 30) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h21
  norm_num at h0 h21
  linear_combination (π)*h0 + (π^3)*h21 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_3_31_0_1 (f : HomData π 3 31) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h21
  norm_num at h0 h21
  linear_combination (π)*h0 + (π^4)*h21 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_3_32_0_1 (f : HomData π 3 32) : ρ ((f.M 0 3))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h21
  norm_num at h0 h21
  linear_combination (π)*h0 + (π^4)*h21 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_3_35_0_0 (f : HomData π 3 35) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h20
  norm_num at h0 h1 h20
  linear_combination (1)*h0 + ((-1)*π)*h1 + (π^3)*h20 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_3_37_0_1 (f : HomData π 3 37) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h21
  norm_num at h0 h21
  linear_combination (π)*h0 + (π^3)*h21 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_3_38_0_1 (f : HomData π 3 38) : ρ ((f.M 0 3))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h21
  norm_num at h0 h21
  linear_combination (π)*h0 + (π^3)*h21 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_3_39_0_1 (f : HomData π 3 39) : ρ ((f.M 0 3))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h21
  norm_num at h0 h21
  linear_combination (π)*h0 + (π^4)*h21 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_3_40_0_1 (f : HomData π 3 40) : ρ ((f.M 0 3))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h21
  norm_num at h0 h1 h21
  linear_combination (π)*h0 + ((-1)*π^2)*h1 + (π^3)*h21 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_3_41_0_1 (f : HomData π 3 41) : ρ ((f.M 0 3))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h21
  norm_num at h0 h1 h21
  linear_combination (π)*h0 + ((-1)*π^2)*h1 + (π^4)*h21 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_3_42_0_1 (f : HomData π 3 42) : ρ ((f.M 0 3))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h21
  norm_num at h0 h1 h21
  linear_combination (π)*h0 + ((-1)*π)*h1 + (π^3)*h21 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_3_43_0_1 (f : HomData π 3 43) : ρ ((f.M 0 3))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h21
  norm_num at h0 h1 h21
  linear_combination (1)*h0 + ((-1)*π)*h1 + (π^3)*h21 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_3_44_0_1 (f : HomData π 3 44) : ρ ((f.M 0 3))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h21
  norm_num at h0 h1 h21
  linear_combination (1)*h0 + ((-1)*π)*h1 + (π^3)*h21 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_3_46_0_0 (f : HomData π 3 46) : ρ ((f.M 0 0))=0 := by
  apply (ann _).mp
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h20
  norm_num at h20
  linear_combination (π^5)*h20 + (π^2*(f.U 0 0))*h6
end UniserialComputations.N6
