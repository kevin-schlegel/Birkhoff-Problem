import N6Matrix
noncomputable section
namespace UniserialComputations.N6
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
variable {R k : Type*} [CommRing R] [Field k] (π : R) (ρ : R →+* k)
variable (h6 : π^6=0) (ann : ∀ r, π^5*r=0 ↔ ρ r=0)
include h6 ann in
theorem constraint_28_0_0_0 (f : HomData π 28 0) : ρ ((f.M 1 0))=0 := by
  apply (ann _).mp
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h22
  norm_num at h22
  linear_combination (π^4)*h22 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_28_1_0_0 (f : HomData π 28 1) : ρ ((f.M 1 0))=0 := by
  apply (ann _).mp
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h22
  norm_num at h22
  linear_combination (π^3)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_28_2_0_0 (f : HomData π 28 2) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (π^3)*h4 + (π^4)*h22 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_28_3_0_0 (f : HomData π 28 3) : ρ ((f.M 1 0))=0 := by
  apply (ann _).mp
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h20 h22
  norm_num at h20 h22
  linear_combination (π)*h20 + (π^2)*h22 + ((-1)*(f.M 0 0))*h6
include h6 ann in
theorem constraint_28_4_0_0 (f : HomData π 28 4) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (π^2)*h4 + (π^3)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_28_5_0_0 (f : HomData π 28 5) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (π^2)*h4 + (π^4)*h22 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_28_6_0_0 (f : HomData π 28 6) : ρ ((f.M 1 0))=0 := by
  apply (ann _).mp
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h20 h22
  norm_num at h20 h22
  linear_combination (1)*h20 + (π)*h22 + ((-1)*(f.M 0 0))*h6
include h6 ann in
theorem constraint_28_7_0_0 (f : HomData π 28 7) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h4 := f.ambient_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h4 h20 h22
  norm_num at h0 h4 h20 h22
  linear_combination (1)*h0 + (π)*h4 + (π)*h20 + (π^2)*h22 + ((-1)*(f.M 0 1))*h6
include h6 ann in
theorem constraint_28_8_0_0 (f : HomData π 28 8) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (π)*h4 + (π^3)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_28_9_0_0 (f : HomData π 28 9) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (π)*h4 + (π^4)*h22 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_28_13_0_0 (f : HomData π 28 13) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (1)*h4 + (π^3)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_28_14_0_0 (f : HomData π 28 14) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (1)*h4 + (π^4)*h22 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_28_15_0_0 (f : HomData π 28 15) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (π^2)*h4 + (π^3)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_28_16_0_0 (f : HomData π 28 16) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h4 := f.ambient_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h4 h20 h22
  norm_num at h0 h4 h20 h22
  linear_combination (1)*h0 + (π)*h4 + (π)*h20 + (π^2)*h22 + ((-1)*(f.M 0 1))*h6
include h6 ann in
theorem constraint_28_17_0_0 (f : HomData π 28 17) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (π)*h4 + (π^3)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_28_18_0_0 (f : HomData π 28 18) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h4 := f.ambient_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h4 h20 h22
  norm_num at h0 h4 h20 h22
  linear_combination (1)*h0 + (π)*h4 + (π)*h20 + (π^2)*h22 + ((-1)*(f.M 0 1))*h6
include h6 ann in
theorem constraint_28_18_0_1 (f : HomData π 28 18) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π^2)*h4 + (π^4)*h23 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_28_19_0_0 (f : HomData π 28 19) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h4 := f.ambient_descent 1 0
  have h20 := f.commutes 0 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h4 h20 h22
  norm_num at h0 h4 h20 h22
  linear_combination (1)*h0 + (π)*h4 + (π)*h20 + (π^2)*h22 + ((-1)*(f.M 0 1))*h6
include h6 ann in
theorem constraint_28_20_0_0 (f : HomData π 28 20) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h22
  norm_num at h4 h5 h22
  linear_combination (π)*h4 + ((-1)*π^2)*h5 + (π^3)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_28_23_0_0 (f : HomData π 28 23) : ρ ((f.M 1 1))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h22
  norm_num at h4 h22
  linear_combination (1)*h4 + (π^3)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_28_24_0_1 (f : HomData π 28 24) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π^2)*h4 + (π^4)*h23 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_28_26_0_1 (f : HomData π 28 26) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π)*h4 + (π^4)*h23 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_28_29_0_0 (f : HomData π 28 29) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h22
  norm_num at h4 h5 h22
  linear_combination (1)*h4 + ((-1)*π^2)*h5 + (π^3)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_28_30_0_1 (f : HomData π 28 30) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π)*h4 + (π^3)*h23 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_28_31_0_1 (f : HomData π 28 31) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π)*h4 + (π^4)*h23 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_28_32_0_1 (f : HomData π 28 32) : ρ ((f.M 1 3))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π)*h4 + (π^4)*h23 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_28_35_0_0 (f : HomData π 28 35) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h22
  norm_num at h4 h5 h22
  linear_combination (1)*h4 + ((-1)*π)*h5 + (π^3)*h22 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_28_37_0_1 (f : HomData π 28 37) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π)*h4 + (π^3)*h23 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_28_38_0_1 (f : HomData π 28 38) : ρ ((f.M 1 3))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π)*h4 + (π^3)*h23 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_28_39_0_1 (f : HomData π 28 39) : ρ ((f.M 1 3))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h23
  norm_num at h4 h23
  linear_combination (π)*h4 + (π^4)*h23 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_28_40_0_1 (f : HomData π 28 40) : ρ ((f.M 1 3))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h23
  norm_num at h4 h5 h23
  linear_combination (π)*h4 + ((-1)*π^2)*h5 + (π^3)*h23 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_28_41_0_1 (f : HomData π 28 41) : ρ ((f.M 1 3))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h23
  norm_num at h4 h5 h23
  linear_combination (π)*h4 + ((-1)*π^2)*h5 + (π^4)*h23 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_28_42_0_1 (f : HomData π 28 42) : ρ ((f.M 1 3))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h23
  norm_num at h4 h5 h23
  linear_combination (π)*h4 + ((-1)*π)*h5 + (π^3)*h23 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_28_43_0_0 (f : HomData π 28 43) : ρ ((f.M 1 2))=0 := by
  apply (ann _).mp
  have h1 := f.ambient_descent 0 1
  have h4 := f.ambient_descent 1 0
  have h20 := f.commutes 0 0
  have h21 := f.commutes 0 1
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h1 h4 h20 h21 h22
  norm_num at h1 h4 h20 h21 h22
  linear_combination (1)*h1 + (1)*h4 + (π)*h20 + ((-1)*π^2)*h21 + (π^2)*h22 + ((-1)*(f.M 0 2) + (f.M 0 3) + (f.U 0 1))*h6
include h6 ann in
theorem constraint_28_43_0_1 (f : HomData π 28 43) : ρ ((f.M 1 3))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h23
  norm_num at h4 h5 h23
  linear_combination (1)*h4 + ((-1)*π)*h5 + (π^3)*h23 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_28_44_0_1 (f : HomData π 28 44) : ρ ((f.M 1 3))=0 := by
  apply (ann _).mp
  have h4 := f.ambient_descent 1 0
  have h5 := f.ambient_descent 1 1
  have h23 := f.commutes 1 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h4 h5 h23
  norm_num at h4 h5 h23
  linear_combination (1)*h4 + ((-1)*π)*h5 + (π^3)*h23 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_28_46_0_0 (f : HomData π 28 46) : ρ ((f.M 1 0))=0 := by
  apply (ann _).mp
  have h22 := f.commutes 1 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h22
  norm_num at h22
  linear_combination (π^5)*h22 + (π^2*(f.U 0 0))*h6
end UniserialComputations.N6
